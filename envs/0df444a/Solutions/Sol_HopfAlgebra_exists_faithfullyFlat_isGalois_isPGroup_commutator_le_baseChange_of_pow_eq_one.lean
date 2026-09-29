-- Prove2me | solution 1 for HopfAlgebra.exists_faithfullyFlat_isGalois_isPGroup_commutator_le_baseChange_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/cb4495a8-b154-547c-91c5-82f679379cd2

import Mathlib
import Theorems.Thm_IsDiscreteValuationRing_exists_faithfullyFlat_isAdicComplete_irreducible
import Theorems.Thm_HopfAlgebra_forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one
import Theorems.Thm_HopfAlgebra_algebra_etale_of_module_finite_of_charZero
import Theorems.Thm_Algebra_Etale_finite_and_bijective_lift_pi_algHom_algebraicClosure
import Theorems.Thm_IsDiscreteValuationRing_exists_finite_etale_isGalois_isPGroup_commutator_le_of_etale
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_faithfullyFlat_isGalois_isPGroup_commutator_le_baseChange_of_pow_eq_one

set_option autoImplicit false

open scoped TensorProduct

universe u v

namespace F1Eng

open scoped TensorProduct

section BaseChangePoints

variable {R S K T : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing K] [Bialgebra R K]
  [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

noncomputable def resPt (f : WithConv (S ⊗[R] K →ₐ[S] T)) : WithConv (K →ₐ[R] T) :=
  WithConv.toConv ((f.ofConv.restrictScalars R).comp
    (Algebra.TensorProduct.includeRight : K →ₐ[R] S ⊗[R] K))

theorem resPt_apply (f : WithConv (S ⊗[R] K →ₐ[S] T)) (k : K) :
    (resPt f).ofConv k = f.ofConv ((1 : S) ⊗ₜ[R] k) := rfl

noncomputable def extPt (ψ : WithConv (K →ₐ[R] T)) : WithConv (S ⊗[R] K →ₐ[S] T) :=
  WithConv.toConv (Algebra.TensorProduct.lift (Algebra.ofId S T) ψ.ofConv (fun _ _ => Commute.all _ _))

theorem extPt_apply (ψ : WithConv (K →ₐ[R] T)) (s : S) (k : K) :
    (extPt (S := S) ψ).ofConv (s ⊗ₜ[R] k) = algebraMap S T s * ψ.ofConv k := by
  simp only [extPt, WithConv.ofConv_toConv, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]

theorem resPt_extPt (ψ : WithConv (K →ₐ[R] T)) : resPt (extPt (S := S) ψ) = ψ := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro k
  rw [resPt_apply, extPt_apply, map_one, one_mul]

theorem extPt_resPt (f : WithConv (S ⊗[R] K →ₐ[S] T)) : extPt (resPt f) = f := by
  apply WithConv.ofConv_injective
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · apply AlgHom.ext
    intro k
    change (extPt (S := S) (resPt f)).ofConv ((1 : S) ⊗ₜ[R] k) = f.ofConv ((1 : S) ⊗ₜ[R] k)
    rw [extPt_apply, map_one, one_mul, resPt_apply]

theorem resPt_injective : Function.Injective (resPt : WithConv (S ⊗[R] K →ₐ[S] T) → WithConv (K →ₐ[R] T)) :=
  fun f g h => by rw [← extPt_resPt f, ← extPt_resPt g, h]

noncomputable def resPtEquiv : WithConv (S ⊗[R] K →ₐ[S] T) ≃ WithConv (K →ₐ[R] T) :=
  ⟨resPt, extPt, extPt_resPt, resPt_extPt⟩

theorem resPt_one : resPt (1 : WithConv (S ⊗[R] K →ₐ[S] T)) = (1 : WithConv (K →ₐ[R] T)) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro k
  rw [resPt_apply, AlgHom.convOne_apply, AlgHom.convOne_apply, TensorProduct.counit_tmul,
    CommSemiring.counit_apply, ← Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_apply]

theorem resPt_mul (f g : WithConv (S ⊗[R] K →ₐ[S] T)) : resPt (f * g) = resPt f * resPt g := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro k
  rw [resPt_apply, AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply]

  let ρ := Coalgebra.Repr.arbitrary R k
  rw [← ρ.eq]
  simp only [TensorProduct.tmul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.lift_tmul]
  rfl

theorem resPt_pow (f : WithConv (S ⊗[R] K →ₐ[S] T)) (n : ℕ) : resPt (f ^ n) = resPt f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, resPt_one]
  | succ n ih => rw [pow_succ, pow_succ, resPt_mul, ih]

end BaseChangePoints

section GroupLikeDescent

variable {R S K : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing K] [Bialgebra R K]

theorem counit_eq_one_of_baseChange (hRS : Function.Injective (algebraMap R S)) (x : K)
    (hε : Coalgebra.counit (R := S) ((1 : S) ⊗ₜ[R] x) = 1) : Coalgebra.counit (R := R) x = 1 := by
  rw [TensorProduct.counit_tmul, CommSemiring.counit_apply, ← Algebra.algebraMap_eq_smul_one] at hε
  exact hRS (by rw [hε, map_one])

theorem comul_eq_tmul_self_of_forall_points (x : K)
    (h : ∀ (f g : WithConv (K →ₐ[R] K ⊗[R] K)), (f * g).ofConv x = f.ofConv x * g.ofConv x) :
    Coalgebra.comul (R := R) x = x ⊗ₜ[R] x := by
  have := h (WithConv.toConv Algebra.TensorProduct.includeLeft) (WithConv.toConv Algebra.TensorProduct.includeRight)
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv,
    Algebra.TensorProduct.lift_includeLeft_includeRight, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
  simpa using this

theorem convMul_apply_eq_of_baseChange (hRS : Function.Injective (algebraMap R S)) (x : K)
    (hΔ : Coalgebra.comul (R := S) ((1 : S) ⊗ₜ[R] x) = ((1 : S) ⊗ₜ[R] x) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x))
    (T : Type*) [CommRing T] [Algebra R T] [Module.Flat R T] (f g : WithConv (K →ₐ[R] T)) :
    (f * g).ofConv x = f.ofConv x * g.ofConv x := by
  let iT : T →ₐ[R] S ⊗[R] T := Algebra.TensorProduct.includeRight
  have hiT : Function.Injective iT := Algebra.TensorProduct.includeRight_injective hRS
  apply hiT
  rw [map_mul]

  let F := extPt (S := S) (T := S ⊗[R] T) (WithConv.toConv (iT.comp f.ofConv))
  let G := extPt (S := S) (T := S ⊗[R] T) (WithConv.toConv (iT.comp g.ofConv))
  have hF : resPt F = WithConv.toConv (iT.comp f.ofConv) := resPt_extPt _
  have hG : resPt G = WithConv.toConv (iT.comp g.ofConv) := resPt_extPt _
  have hFx := resPt_apply F x
  rw [hF, WithConv.ofConv_toConv, AlgHom.comp_apply] at hFx
  have hGx := resPt_apply G x
  rw [hG, WithConv.ofConv_toConv, AlgHom.comp_apply] at hGx

  have h1 : iT ((f * g).ofConv x) = (resPt (F * G)).ofConv x := by
    have e := resPt_apply (F * G) x
    rw [resPt_mul, hF, hG, ← AlgHom.comp_convMul_distrib, AlgHom.comp_apply] at e
    exact e
  have h2 : (resPt (F * G)).ofConv x = F.ofConv ((1 : S) ⊗ₜ[R] x) * G.ofConv ((1 : S) ⊗ₜ[R] x) := by
    rw [resPt_apply, AlgHom.convMul_apply, hΔ, Algebra.TensorProduct.lift_tmul]
  rw [h1, h2, hFx, hGx]

theorem comul_eq_tmul_self_of_baseChange [Module.Flat R K] (hRS : Function.Injective (algebraMap R S)) (x : K)
    (hΔ : Coalgebra.comul (R := S) ((1 : S) ⊗ₜ[R] x) = ((1 : S) ⊗ₜ[R] x) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x)) :
    Coalgebra.comul (R := R) x = x ⊗ₜ[R] x :=
  comul_eq_tmul_self_of_forall_points x (convMul_apply_eq_of_baseChange hRS x hΔ (K ⊗[R] K))

end GroupLikeDescent

end F1Eng

namespace F1Eng

theorem withConv_baseChange_pow_eq_one {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {H : Type*} [CommRing H] [HopfAlgebra R H] (m : ℕ)
    (hH : (WithConv.toConv (AlgHom.id R H)) ^ m = 1)
    (T : Type*) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (f : WithConv (S ⊗[R] H →ₐ[S] T)) : f ^ m = 1 := by
  apply resPt_injective (R := R) (S := S)
  rw [resPt_pow, resPt_one]

  set g := resPt f
  have key : ∀ k : ℕ, g ^ k = WithConv.toConv (g.ofConv.comp
      ((WithConv.toConv (AlgHom.id R H) ^ k : WithConv (H →ₐ[R] H))).ofConv) := by
    intro k
    induction k with
    | zero =>
        rw [pow_zero, pow_zero, AlgHom.convOne_def (R := R) (A := T) (C := H),
          AlgHom.convOne_def (R := R) (A := H) (C := H), WithConv.ofConv_toConv, ← AlgHom.comp_assoc]
        congr 1
        ext x
        simp
    | succ k ih =>
        rw [pow_succ, pow_succ, ih, AlgHom.comp_convMul_distrib, WithConv.ofConv_toConv, AlgHom.comp_id,
          WithConv.toConv_ofConv, WithConv.toConv_ofConv]
  rw [key, hH, AlgHom.convOne_def (R := R) (A := H) (C := H), WithConv.ofConv_toConv, ← AlgHom.comp_assoc,
    AlgHom.convOne_def (R := R) (A := T) (C := H)]
  congr 1
  ext x
  simp
end F1Eng

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (p : ℕ) [Fact p.Prime] (hunif : Irreducible (p : R))
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H] [Coalgebra.IsCocomm R H]
    (n : ℕ) (hH : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ p ^ n = 1) :
    ∃ (R₂ : Type u) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsDiscreteValuationRing R₂) (_ : Algebra R R₂)
      (_ : Module.FaithfullyFlat R R₂) (K₂ : Type u) (_ : Field K₂) (_ : Algebra R₂ K₂) (_ : IsFractionRing R₂ K₂),
      Irreducible (p : R₂) ∧
      ∃ N : ℕ,
        (∀ s : ℕ, 0 < s → s ≤ N → ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = p ^ s →
          IsUnit ((p ^ s : R₂) - 1) ∧
            ∃ (χ : Fˣ →* R₂ˣ) (ι : F →+* IsLocalRing.ResidueField R₂),
              ∀ l : Fˣ, IsLocalRing.residue R₂ (χ l : R₂) = ι l) ∧
        Finite (WithConv ((K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂)) ∧
        Function.Bijective
          (Algebra.TensorProduct.lift
            (Algebra.ofId (AlgebraicClosure K₂) (WithConv ((K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂) → AlgebraicClosure K₂))
            (Pi.algHom K₂ _
              fun ν : WithConv ((K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂) =>
                (WithConv.ofConv ν : (K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂))
            (fun _ _ => Commute.all _ _) :
            AlgebraicClosure K₂ ⊗[K₂] (K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[AlgebraicClosure K₂]
              (WithConv ((K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂) → AlgebraicClosure K₂)) ∧
        Nat.card (WithConv ((K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂)) ≤ p ^ N ∧
        (∀ ν : WithConv ((K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂), ν ^ p ^ n = 1) ∧
        ∃ (L : IntermediateField K₂ (AlgebraicClosure K₂)) (_ : FiniteDimensional K₂ L) (_ : IsGalois K₂ L),
          (∀ (ν : (K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂) (a : (K₂ ⊗[R₂] (R₂ ⊗[R] H))), ν a ∈ L) ∧
          ∃ P : Subgroup (L ≃ₐ[K₂] L), P.Normal ∧ IsPGroup p ↥P ∧
            ∀ a b : (L ≃ₐ[K₂] L), a⁻¹ * b⁻¹ * a * b ∈ P := by
  classical
  have hp : p.Prime := Fact.out

  have hHu : (WithConv.toConv (AlgHom.id R H)) ^ p ^ n = 1 :=
    (HopfAlgebra.forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one (p ^ n)).mp hH

  obtain ⟨R₁, _, _, _, _, _, _, hcompl, hunif₁⟩ :=
    IsDiscreteValuationRing.exists_faithfullyFlat_isAdicComplete_irreducible (R := R) p hunif
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal R₁) R₁ := hcompl
  let K₁ : Type u := FractionRing R₁
  haveI : CharZero K₁ := charZero_of_injective_algebraMap (IsFractionRing.injective R₁ K₁)

  let B₁ : Type (max u v) := K₁ ⊗[R₁] (R₁ ⊗[R] H)
  haveI : Algebra.Etale K₁ B₁ := HopfAlgebra.algebra_etale_of_module_finite_of_charZero K₁ B₁
  let N : ℕ := Module.finrank K₁ B₁

  obtain ⟨R₂, _, _, _, _, _, _, _, K₂, _, _, _, _, _, _, _, hunif₂, hloc, hT, L, _, _, hL, P, hPn, hPp, hPc⟩ :=
    IsDiscreteValuationRing.exists_finite_etale_isGalois_isPGroup_commutator_le_of_etale
      (R₁ := R₁) K₁ p hunif₁ N B₁

  letI algRR₂ : Algebra R R₂ := ((algebraMap R₁ R₂).comp (algebraMap R R₁)).toAlgebra
  haveI : IsScalarTower R R₁ R₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.FaithfullyFlat R R₂ := Module.FaithfullyFlat.trans R R₁ R₂
  letI algRK₂ : Algebra R K₂ := ((algebraMap R₂ K₂).comp (algebraMap R R₂)).toAlgebra
  haveI : IsScalarTower R R₂ K₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R R₁ K₂ := IsScalarTower.of_algebraMap_eq (fun r => by
    show (algebraMap R₂ K₂) ((algebraMap R₁ R₂) (algebraMap R R₁ r)) = algebraMap R₁ K₂ (algebraMap R R₁ r)
    rw [← IsScalarTower.algebraMap_apply R₁ R₂ K₂])
  haveI : IsScalarTower R K₁ K₂ := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply R R₁ K₂, IsScalarTower.algebraMap_apply R₁ K₁ K₂,
      ← IsScalarTower.algebraMap_apply R R₁ K₁])
  haveI : CharZero K₂ := charZero_of_injective_algebraMap (algebraMap K₁ K₂).injective

  let A₂ : Type (max u v) := K₂ ⊗[R₂] (R₂ ⊗[R] H)
  let φ : A₂ ≃ₐ[K₂] K₂ ⊗[K₁] B₁ :=
    (Algebra.TensorProduct.cancelBaseChange R R₂ K₂ K₂ H).trans
      ((Algebra.TensorProduct.cancelBaseChange R R₁ K₂ K₂ H).symm.trans
        (Algebra.TensorProduct.cancelBaseChange R₁ K₁ K₂ K₂ (R₁ ⊗[R] H)).symm)

  haveI : Algebra.Etale K₂ A₂ := HopfAlgebra.algebra_etale_of_module_finite_of_charZero K₂ A₂
  obtain ⟨hfin, hev⟩ := Algebra.Etale.finite_and_bijective_lift_pi_algHom_algebraicClosure K₂ A₂
  haveI := hfin

  have hcount : Nat.card (WithConv (A₂ →ₐ[K₂] AlgebraicClosure K₂)) = N := by
    haveI : Fintype (WithConv (A₂ →ₐ[K₂] AlgebraicClosure K₂)) := Fintype.ofFinite _
    let E := AlgEquiv.ofBijective _ hev
    have h1 : Module.finrank (AlgebraicClosure K₂) (AlgebraicClosure K₂ ⊗[K₂] A₂) = Module.finrank K₂ A₂ :=
      Module.finrank_baseChange
    have h2 : Module.finrank (AlgebraicClosure K₂) (WithConv (A₂ →ₐ[K₂] AlgebraicClosure K₂) → AlgebraicClosure K₂)
        = Fintype.card (WithConv (A₂ →ₐ[K₂] AlgebraicClosure K₂)) := Module.finrank_fintype_fun_eq_card _
    have h3 := E.toLinearEquiv.finrank_eq
    rw [h1, h2] at h3
    rw [Nat.card_eq_fintype_card, ← h3, φ.toLinearEquiv.finrank_eq]
    exact Module.finrank_baseChange
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, algRR₂, inferInstance, K₂, inferInstance,
    inferInstance, inferInstance, hunif₂, N, hT, hfin, hev, ?_, ?_, L, inferInstance, inferInstance, ?_,
    P, hPn, hPp, hPc⟩
  ·
    rw [hcount]
    exact (Nat.lt_pow_self hp.one_lt).le
  ·
    intro ν
    have h1 : (WithConv.toConv (AlgHom.id R₂ (R₂ ⊗[R] H))) ^ p ^ n = 1 :=
      F1Eng.withConv_baseChange_pow_eq_one (R := R) (S := R₂) (p ^ n) hHu (R₂ ⊗[R] H) _
    exact F1Eng.withConv_baseChange_pow_eq_one (R := R₂) (S := K₂) (p ^ n) h1 (AlgebraicClosure K₂) ν
  ·
    intro ν a
    have := hL (ν.comp φ.symm.toAlgHom) (φ a)
    simpa using this

end S_HopfAlgebra_exists_faithfullyFlat_isGalois_isPGroup_commutator_le_baseChange_of_pow_eq_one
end P2MW
export P2MW.S_HopfAlgebra_exists_faithfullyFlat_isGalois_isPGroup_commutator_le_baseChange_of_pow_eq_one (solution)
