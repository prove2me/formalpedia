-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_bialgHom_torsion_of_hom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ed4caca2-e64d-5729-91a1-2283985e32ae

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_bialgHom_torsion_of_hom

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

namespace S17HopfFun

section Hom
variable {R : Type u} [CommRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem eq_one_of_mul_self {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (a : SchemeHomOver t f) (haa : L.mul t a a = a) : a = L.one t := by
  calc a = L.mul t (L.one t) a := (L.one_mul t a).symm
    _ = L.mul t (L.mul t (L.inv t a) a) a := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t a) (L.mul t a a) := L.mul_assoc t _ _ _
    _ = L.mul t (L.inv t a) a := by rw [haa]
    _ = L.one t := L.inv_mul_cancel t a

variable (u : SchemeHomOver g f)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LB.mul t x y) u =
        L.mul t (NeronModelInfra.schemeHomOverComp x u) (NeronModelInfra.schemeHomOverComp y u))

include hu in
theorem hom_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    NeronModelInfra.schemeHomOverComp (LB.one t) u = L.one t := by
  apply eq_one_of_mul_self L t
  rw [← hu, LB.one_mul]

include hu in
theorem hom_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t g) :
    NeronModelInfra.schemeHomOverComp (LB.nsmul t n x) u =
      L.nsmul t n (NeronModelInfra.schemeHomOverComp x u) := by
  induction n with
  | zero => exact hom_one LB L u hu t
  | succ n ih =>
      rw [LB.nsmul_succ, L.nsmul_succ, hu, ih]

end Hom

theorem includeLeft_mul_includeRight {R : Type u} [CommRing R] (H : Type u) [CommRing H] [Bialgebra R H] :
    (WithConv.toConv (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H) *
        WithConv.toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H) :
        WithConv (H →ₐ[R] H ⊗[R] H)) =
      WithConv.toConv (Bialgebra.comulAlgHom R H) := by
  rw [AlgHom.convMul_def]
  congr 1
  rw [WithConv.ofConv_toConv, WithConv.ofConv_toConv, ← AlgHom.comp_assoc,
    Algebra.TensorProduct.lmul'_comp_map, Algebra.TensorProduct.lift_includeLeft_includeRight,
    AlgHom.id_comp]

end S17HopfFun

theorem solution
    {R : Type u} [CommRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (u : SchemeHomOver g f)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LB.mul t x y) u =
        L.mul t (NeronModelInfra.schemeHomOverComp x u) (NeronModelInfra.schemeHomOverComp y u))
    (n : ℕ)
    (HB : Type u) [CommRing HB] [HopfAlgebra R HB] (HJ : Type u) [CommRing HJ] [HopfAlgebra R HJ]
    (eB : ∀ (T : Type u) [CommRing T] [Algebra R T],
        WithConv (HB →ₐ[R] T) ≃
          LB.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n)
    (eB_mul : ∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (HB →ₐ[R] T)),
        ((eB T (φ * ψ)).val : SchemeHomOver _ g) =
          LB.mul _ (eB T φ).val (eB T ψ).val)
    (eB_nat : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
        (a : T →ₐ[R] T') (φ : WithConv (HB →ₐ[R] T)),
        ((eB T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ g).1 =
          Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (eB T φ).val.1)
    (eJ : ∀ (T : Type u) [CommRing T] [Algebra R T],
        WithConv (HJ →ₐ[R] T) ≃
          L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n)
    (eJ_mul : ∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (HJ →ₐ[R] T)),
        ((eJ T (φ * ψ)).val : SchemeHomOver _ f) =
          L.mul _ (eJ T φ).val (eJ T ψ).val)
    (eJ_nat : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
        (a : T →ₐ[R] T') (φ : WithConv (HJ →ₐ[R] T)),
        ((eJ T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
          Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (eJ T φ).val.1) :
    ∃ φ : HJ →ₐc[R] HB, ∀ (T : Type u) [CommRing T] [Algebra R T] (x : WithConv (HB →ₐ[R] T)),
      ((eJ T (.toConv (x.ofConv.comp (φ : HJ →ₐ[R] HB)))).val : SchemeHomOver _ f) =
        NeronModelInfra.schemeHomOverComp ((eB T x).val : SchemeHomOver _ g) u := by
  classical

  have htors : ∀ (T : Type u) [CommRing T] [Algebra R T] (x : WithConv (HB →ₐ[R] T)),
      NeronModelInfra.schemeHomOverComp ((eB T x).val : SchemeHomOver _ g) u ∈
        L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n := by
    intro T _ _ x
    have hx := (eB T x).property
    rw [RelativeGroupLaw.mem_torsionSubset, RelativeGroupLaw.isTorsionPoint_def] at hx ⊢
    rw [← S17HopfFun.hom_nsmul LB L u hu, hx, S17HopfFun.hom_one LB L u hu]

  let Ψ : ∀ (T : Type u) [CommRing T] [Algebra R T],
      WithConv (HB →ₐ[R] T) → WithConv (HJ →ₐ[R] T) :=
    fun T _ _ x => (eJ T).symm ⟨_, htors T x⟩
  have hΨ : ∀ (T : Type u) [CommRing T] [Algebra R T] (x : WithConv (HB →ₐ[R] T)),
      ((eJ T (Ψ T x)).val : SchemeHomOver _ f) =
        NeronModelInfra.schemeHomOverComp ((eB T x).val : SchemeHomOver _ g) u := by
    intro T _ _ x
    simp only [Ψ, Equiv.apply_symm_apply]
  have hinj : ∀ (T : Type u) [CommRing T] [Algebra R T] (y z : WithConv (HJ →ₐ[R] T)),
      ((eJ T y).val : SchemeHomOver _ f).1 = ((eJ T z).val : SchemeHomOver _ f).1 → y = z := by
    intro T _ _ y z h
    apply (eJ T).injective
    exact Subtype.ext (Subtype.ext h)

  have hnat : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
      (a : T →ₐ[R] T') (x : WithConv (HB →ₐ[R] T)),
      Ψ T' (.toConv (a.comp x.ofConv)) = .toConv (a.comp (Ψ T x).ofConv) := by
    intro T T' _ _ _ _ a x
    apply hinj T'
    rw [hΨ T', NeronModelInfra.schemeHomOverComp_coe, eB_nat T T' a x,
      eJ_nat T T' a (Ψ T x), hΨ T x, NeronModelInfra.schemeHomOverComp_coe, Category.assoc]

  let φ₀ : HJ →ₐ[R] HB := (Ψ HB (.toConv (AlgHom.id R HB))).ofConv
  have hYon : ∀ (T : Type u) [CommRing T] [Algebra R T] (x : WithConv (HB →ₐ[R] T)),
      Ψ T x = .toConv (x.ofConv.comp φ₀) := by
    intro T _ _ x
    have h := hnat HB T x.ofConv (.toConv (AlgHom.id R HB))
    rw [WithConv.ofConv_toConv, AlgHom.comp_id, WithConv.toConv_ofConv] at h
    exact h

  have hmul : ∀ (T : Type u) [CommRing T] [Algebra R T] (x y : WithConv (HB →ₐ[R] T)),
      Ψ T (x * y) = Ψ T x * Ψ T y := by
    intro T _ _ x y
    apply (eJ T).injective
    apply Subtype.ext
    rw [hΨ, eJ_mul, hΨ, hΨ, eB_mul, hu]
  have hone : ∀ (T : Type u) [CommRing T] [Algebra R T], Ψ T 1 = 1 := by
    intro T _ _
    have hB1 : ((eB T 1).val : SchemeHomOver _ g) = LB.one _ := by
      apply S17HopfFun.eq_one_of_mul_self LB
      rw [← eB_mul, mul_one]
    have hJ1 : ((eJ T 1).val : SchemeHomOver _ f) = L.one _ := by
      apply S17HopfFun.eq_one_of_mul_self L
      rw [← eJ_mul, mul_one]
    apply (eJ T).injective
    apply Subtype.ext
    rw [hΨ, hB1, S17HopfFun.hom_one LB L u hu, hJ1]

  have hcounit : (Bialgebra.counitAlgHom R HB).comp φ₀ = Bialgebra.counitAlgHom R HJ := by
    have h := hYon R 1
    rw [hone R] at h
    have h' := congrArg WithConv.ofConv h
    rw [WithConv.ofConv_toConv] at h'
    have e1 : (1 : WithConv (HJ →ₐ[R] R)).ofConv = Bialgebra.counitAlgHom R HJ := by
      rw [AlgHom.convOne_def, WithConv.ofConv_toConv, Algebra.ofId_self, AlgHom.id_comp]
    have e2 : (1 : WithConv (HB →ₐ[R] R)).ofConv = Bialgebra.counitAlgHom R HB := by
      rw [AlgHom.convOne_def, WithConv.ofConv_toConv, Algebra.ofId_self, AlgHom.id_comp]
    rw [e1, e2] at h'
    exact h'.symm

  have hcomul : (Algebra.TensorProduct.map φ₀ φ₀).comp (Bialgebra.comulAlgHom R HJ) =
      (Bialgebra.comulAlgHom R HB).comp φ₀ := by
    have hΔ := S17HopfFun.includeLeft_mul_includeRight (R := R) HB
    have h1 : Ψ (HB ⊗[R] HB)
        (WithConv.toConv (Algebra.TensorProduct.includeLeft : HB →ₐ[R] HB ⊗[R] HB) *
          WithConv.toConv (Algebra.TensorProduct.includeRight : HB →ₐ[R] HB ⊗[R] HB)) =
        .toConv ((Algebra.TensorProduct.map φ₀ φ₀).comp (Bialgebra.comulAlgHom R HJ)) := by
      rw [hmul, hYon, hYon, WithConv.ofConv_toConv, WithConv.ofConv_toConv, AlgHom.convMul_def,
        WithConv.ofConv_toConv, WithConv.ofConv_toConv, Algebra.TensorProduct.map_comp,
        AlgHom.comp_assoc, ← AlgHom.comp_assoc,
        Algebra.TensorProduct.lmul'_comp_map, Algebra.TensorProduct.lift_includeLeft_includeRight,
        AlgHom.id_comp]
    have h2 : Ψ (HB ⊗[R] HB) (WithConv.toConv (Bialgebra.comulAlgHom R HB)) =
        .toConv ((Bialgebra.comulAlgHom R HB).comp φ₀) := by
      rw [hYon, WithConv.ofConv_toConv]
    rw [hΔ] at h1
    exact WithConv.toConv_injective (h1.symm.trans h2)

  refine ⟨BialgHom.ofAlgHom φ₀ hcounit hcomul, ?_⟩
  intro T _ _ x
  have hcoe : ((BialgHom.ofAlgHom φ₀ hcounit hcomul : HJ →ₐc[R] HB) : HJ →ₐ[R] HB) = φ₀ := by
    ext a; rfl
  rw [hcoe, ← hYon T x]
  exact hΨ T x

end S_GoodReductionJacobian_RelativeGroupLaw_exists_bialgHom_torsion_of_hom
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_bialgHom_torsion_of_hom (solution)
