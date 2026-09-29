-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_algHom_forall_equiv_comp_eq_comp_of_torsion_points_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/afa5088c-2a8a-570f-a802-e5397863a667

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_algHom_forall_equiv_comp_eq_comp_of_torsion_points_equiv

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem solution
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (n : ℕ)
    (H : Type u) [CommRing H] [HopfAlgebra K H]
    (e : ∀ (T : Type u) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) n)
    (he_mul : ∀ (T : Type u) [CommRing T] [Algebra K T] (φ ψ : WithConv (H →ₐ[K] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
        (g' : T →ₐ[K] T') (φ : WithConv (H →ₐ[K] T)),
      ((e T' (.toConv (g'.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1)
    (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (hφ_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ φ =
        (L.mul t ⟨P.1 ≫ φ, by rw [Category.assoc, hφ]; exact P.2⟩ ⟨Q.1 ≫ φ, by rw [Category.assoc, hφ]; exact Q.2⟩).1) :
    ∃ φH : H →ₐ[K] H,
      (∀ (T : Type u) [CommRing T] [Algebra K T] (q : WithConv (H →ₐ[K] T)),
        ((e T (.toConv (q.ofConv.comp φH))).val : SchemeHomOver _ f).1 = (e T q).val.1 ≫ φ) ∧
      (∀ x ∈ primitives K H, φH x ∈ primitives K H) := by
  classical

  let push : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}, SchemeHomOver t f → SchemeHomOver t f :=
    fun P => ⟨P.1 ≫ φ, by rw [Category.assoc, hφ]; exact P.2⟩
  have hpush_val : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (P : SchemeHomOver t f),
      (push P).1 = P.1 ≫ φ := fun P => rfl
  have hpush_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      push (L.mul t P Q) = L.mul t (push P) (push Q) := fun t P Q => Subtype.ext (hφ_hom t P Q)
  have hpush_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)), push (L.one t) = L.one t := by
    intro T t
    have h1 : push (L.one t) = L.mul t (push (L.one t)) (push (L.one t)) := by
      rw [← hpush_mul, L.one_mul]
    have h2 := congrArg (fun Q => L.mul t (L.inv t (push (L.one t))) Q) h1
    simp only [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at h2
    exact h2.symm
  have hpush_nsmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (m : ℕ) (P : SchemeHomOver t f),
      push (L.nsmul t m P) = L.nsmul t m (push P) := by
    intro T t m P
    induction m with
    | zero => exact hpush_one t
    | succ m ih => rw [L.nsmul_succ, L.nsmul_succ, hpush_mul, ih]
  have hpush_tors : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t f),
      P ∈ L.torsionSubset t n → push P ∈ L.torsionSubset t n := by
    intro T t P hP
    rw [RelativeGroupLaw.mem_torsionSubset, RelativeGroupLaw.isTorsionPoint_def] at hP ⊢
    rw [← hpush_nsmul, hP, hpush_one]

  let u := e H (.toConv (AlgHom.id K H))
  let q₀ : WithConv (H →ₐ[K] H) := (e H).symm ⟨push u.val, hpush_tors _ _ u.2⟩
  have hq₀ : (e H q₀).val = push u.val := by
    simp only [q₀, Equiv.apply_symm_apply]

  have hpin : ∀ (T : Type u) [CommRing T] [Algebra K T] (q : WithConv (H →ₐ[K] T)),
      ((e T (.toConv (q.ofConv.comp q₀.ofConv))).val : SchemeHomOver _ f).1 = (e T q).val.1 ≫ φ := by
    intro T _ _ q
    have h1 := he_nat H T q.ofConv q₀
    have h2 := he_nat H T q.ofConv (.toConv (AlgHom.id K H))
    rw [WithConv.toConv_ofConv] at h1
    have hq : WithConv.toConv (q.ofConv.comp (AlgHom.id K H)) = q := by
      rw [AlgHom.comp_id, WithConv.toConv_ofConv]
    rw [hq] at h2
    rw [h1, h2, Category.assoc]
    congr 1
    change (e H q₀).val.1 = u.val.1 ≫ φ
    rw [hq₀]
  have hpinPt : ∀ (T : Type u) [CommRing T] [Algebra K T] (q : WithConv (H →ₐ[K] T)),
      (e T (.toConv (q.ofConv.comp q₀.ofConv))).val = push (e T q).val :=
    fun T _ _ q => Subtype.ext (hpin T q)
  refine ⟨q₀.ofConv, hpin, ?_⟩

  have hconv : ∀ (T : Type u) [CommRing T] [Algebra K T] (q₁ q₂ : WithConv (H →ₐ[K] T)),
      WithConv.toConv ((q₁ * q₂).ofConv.comp q₀.ofConv) =
        WithConv.toConv (q₁.ofConv.comp q₀.ofConv) * WithConv.toConv (q₂.ofConv.comp q₀.ofConv) := by
    intro T _ _ q₁ q₂
    apply (e T).injective
    apply Subtype.ext
    rw [hpinPt, he_mul, he_mul, hpinPt, hpinPt, hpush_mul]

  have hlm : ∀ z : H ⊗[K] H,
      (Algebra.TensorProduct.lmul' (S := H ⊗[K] H) K)
        (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : H →ₐ[K] H ⊗[K] H)
          (Algebra.TensorProduct.includeRight : H →ₐ[K] H ⊗[K] H) z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
        rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
          Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  have hlm' : ∀ z : H ⊗[K] H,
      (Algebra.TensorProduct.lmul' (S := H ⊗[K] H) K)
        (Algebra.TensorProduct.map
          ((Algebra.TensorProduct.includeLeft : H →ₐ[K] H ⊗[K] H).comp q₀.ofConv)
          ((Algebra.TensorProduct.includeRight : H →ₐ[K] H ⊗[K] H).comp q₀.ofConv) z) =
        Algebra.TensorProduct.map q₀.ofConv q₀.ofConv z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
        rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, AlgHom.comp_apply,
          AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Algebra.TensorProduct.map_tmul]
    | add z w hz hw => rw [map_add, map_add, hz, hw, map_add]
  have hcomul : ∀ y : H, Coalgebra.comul (R := K) (q₀.ofConv y) =
      Algebra.TensorProduct.map q₀.ofConv q₀.ofConv (Coalgebra.comul (R := K) y) := by
    intro y
    have h := hconv (H ⊗[K] H) (.toConv Algebra.TensorProduct.includeLeft) (.toConv Algebra.TensorProduct.includeRight)
    have h' := congrArg (fun w : WithConv (H →ₐ[K] H ⊗[K] H) => w.ofConv y) h
    simp only [AlgHom.convMul_def, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply] at h'
    rw [hlm, hlm'] at h'
    exact h'
  intro x hx
  have hx' : Coalgebra.comul (R := K) x = x ⊗ₜ[K] 1 + 1 ⊗ₜ[K] x := by
    have h0 := hx
    simp only [primitives, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.flip_apply, TensorProduct.mk_apply] at h0
    rw [sub_sub, sub_eq_zero] at h0
    exact h0
  simp only [primitives, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
  rw [sub_sub, sub_eq_zero, hcomul, hx', map_add, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
  simp

end S_GoodReductionJacobian_RelativeGroupLaw_exists_algHom_forall_equiv_comp_eq_comp_of_torsion_points_equiv
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_algHom_forall_equiv_comp_eq_comp_of_torsion_points_equiv (solution)
