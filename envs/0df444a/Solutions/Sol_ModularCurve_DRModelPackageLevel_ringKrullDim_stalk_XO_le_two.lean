-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.ringKrullDim_stalk_XO_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/fef9c794-fd86-5d58-96b4-97f0310f7d44

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import Theorems.Thm_AlgebraicGeometry_IsOpenImmersion_ringKrullDim_stalk_eq
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_ringKrullDim_stalk_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_ringKrullDim_stalk_XO_le_two

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open Polynomial TensorProduct CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

namespace ECL_Dim2

private theorem ringKrullDim_le_of_isIntegral (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] : ringKrullDim B ≤ ringKrullDim A := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B)) ?_
  intro P Q hPQ
  have hPQ' : P.asIdeal < Q.asIdeal := hPQ
  obtain ⟨x, hxQ, hxP⟩ := Set.exists_of_ssubset hPQ'
  change Ideal.comap (algebraMap A B) P.asIdeal < Ideal.comap (algebraMap A B) Q.asIdeal
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hPQ'.le ⟨hxQ, hxP⟩ (Algebra.IsIntegral.isIntegral x)

private theorem ringKrullDim_polynomial_eq_two (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    ringKrullDim (Polynomial O) = 2 := by
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one]
  rfl

private theorem ringKrullDim_tensorProduct_le_two (R : Type) [CommRing R] (O : Type) [CommRing O] [Algebra R O] [IsDomain O]
    [IsDiscreteValuationRing O] (A : Type) [CommRing A] [Algebra R A] (ψA : Polynomial R →ₐ[R] A)
    (hA : ψA.toRingHom.IsIntegral) :
    ringKrullDim (O ⊗[R] A) ≤ 2 := by
  let φ : Polynomial O →ₐ[O] O ⊗[R] A := Polynomial.aeval ((1 : O) ⊗ₜ[R] ψA Polynomial.X)
  letI iA : Algebra (Polynomial R) A := ψA.toRingHom.toAlgebra
  letI iT : Algebra (Polynomial O) (O ⊗[R] A) := φ.toRingHom.toAlgebra
  letI iRT : Algebra (Polynomial R) (O ⊗[R] A) :=
    ((Algebra.TensorProduct.includeRight (R := R) (A := O) (B := A)).comp ψA).toRingHom.toAlgebra
  letI iRO : Algebra (Polynomial R) (Polynomial O) := (Polynomial.mapAlg R O).toRingHom.toAlgebra
  have hcompA : (φ.restrictScalars R).comp (Polynomial.mapAlg R O) =
      (Algebra.TensorProduct.includeRight (R := R) (A := O) (B := A)).comp ψA := by
    apply Polynomial.algHom_ext
    simp [φ, Polynomial.mapAlg_eq_map]
  have hcomp : ∀ x : Polynomial R, φ (Polynomial.mapAlg R O x) =
      (Algebra.TensorProduct.includeRight (R := R) (A := O) (B := A)) (ψA x) := fun x =>
    congrArg (fun h : Polynomial R →ₐ[R] O ⊗[R] A => h x) hcompA
  haveI : IsScalarTower (Polynomial R) (Polynomial O) (O ⊗[R] A) :=
    IsScalarTower.of_algebraMap_eq fun x => (hcomp x).symm
  let ι' : A →ₐ[Polynomial R] O ⊗[R] A :=
    { (Algebra.TensorProduct.includeRight (R := R) (A := O) (B := A)).toRingHom with commutes' := fun _ => rfl }
  haveI : Algebra.IsIntegral (Polynomial O) (O ⊗[R] A) := by
    refine ⟨fun t => ?_⟩
    induction t using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul o a =>
      have h1 : IsIntegral (Polynomial O) (o ⊗ₜ[R] (1 : A)) := by
        have : o ⊗ₜ[R] (1 : A) = algebraMap (Polynomial O) (O ⊗[R] A) (Polynomial.C o) := by
          change _ = φ (Polynomial.C o)
          rw [Polynomial.aeval_C]
          rfl
        rw [this]
        exact isIntegral_algebraMap
      have h2 : IsIntegral (Polynomial O) ((1 : O) ⊗ₜ[R] a) := by
        have ha : IsIntegral (Polynomial R) a := hA a
        have := ha.map ι'
        exact this.tower_top
      have : o ⊗ₜ[R] a = (o ⊗ₜ[R] (1 : A)) * ((1 : O) ⊗ₜ[R] a) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [this]
      exact h1.mul h2
    | add x y hx hy => exact hx.add hy
  calc ringKrullDim (O ⊗[R] A) ≤ ringKrullDim (Polynomial O) := ringKrullDim_le_of_isIntegral _ _
    _ = 2 := ringKrullDim_polynomial_eq_two O

private theorem exists_algHom_isIntegral (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (j : ↥(modularFunctionFieldFull N)) :
    ∃ ψ : Polynomial ↥(GaloisRep.ratLocalizedAt ℓ) →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ {j}), ψ.toRingHom.IsIntegral := by
  let T : Subalgebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) :=
    Algebra.adjoin ↥(GaloisRep.ratLocalizedAt ℓ) ({j} : Set ↥(modularFunctionFieldFull N))
  have hle : T ≤ chartAlg N ℓ {j} := adjoin_le_chartAlg N ℓ {j}
  have hT : (T : Subalgebra _ _) = (Polynomial.aeval j).range := Algebra.adjoin_singleton_eq_range_aeval _ j
  let f : Polynomial ↥(GaloisRep.ratLocalizedAt ℓ) →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥T :=
    (Polynomial.aeval j).codRestrict T (fun p => by rw [hT]; exact ⟨p, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ (Polynomial.aeval j).range := hT ▸ hx
    obtain ⟨p, rfl⟩ := hx'
    exact ⟨p, rfl⟩
  let g : ↥T →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ {j}) := Subalgebra.inclusion hle
  letI := g.toRingHom.toAlgebra
  have hg : g.toRingHom.IsIntegral := fun x => by
    let v : ↥(chartAlg N ℓ {j}) →ₐ[↥T] ↥(modularFunctionFieldFull N) :=
      { (chartAlg N ℓ {j}).val.toRingHom with commutes' := fun _ => rfl }
    exact (isIntegral_algHom_iff v Subtype.val_injective).mp ((mem_chartAlg_iff N ℓ).mp x.2)
  exact ⟨g.comp f, RingHom.IsIntegral.trans f.toRingHom g.toRingHom (RingHom.isIntegral_of_surjective _ hf) hg⟩

section Geo
variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] (O : Type) [CommRing O] (ρO : DRLevel.R q →+* O)

private theorem ringKrullDim_stalk_le_of_chart {A : Type} [CommRing A] [Algebra (DRLevel.R q) A]
    (u : Spec (CommRingCat.of A) ⟶ DRLevel.X N₀ q)
    [IsOpenImmersion u] (hu : u ≫ DRLevel.toBase N₀ q = Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) A)))
    (z : ↥(DRLevel.XO (N₀ := N₀) ρO))
    (hz : (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).base z ∈ Set.range ⇑u.base) :
    letI := ρO.toAlgebra
    ringKrullDim ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk z) ≤ ringKrullDim (A ⊗[DRLevel.R q] O) := by
  letI := ρO.toAlgebra
  let v := pullback.snd u (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))
  have hzv : z ∈ Set.range ⇑v.base := by
    show z ∈ Set.range ⇑(pullback.snd u (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))).base
    rw [Scheme.Pullback.range_snd]
    exact hz
  obtain ⟨w, rfl⟩ := hzv
  rw [← AlgebraicGeometry.IsOpenImmersion.ringKrullDim_stalk_eq v w]
  let e : pullback u (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ≅
      Spec (CommRingCat.of (A ⊗[DRLevel.R q] O)) :=
    pullbackRightPullbackFstIso (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) u ≪≫
      pullback.congrHom hu rfl ≪≫ pullbackSpecIso (DRLevel.R q) A O
  rw [AlgebraicGeometry.IsOpenImmersion.ringKrullDim_stalk_eq e.hom w]
  refine (AlgebraicGeometry.IsAffineOpen.ringKrullDim_stalk_le (isAffineOpen_top (Spec (CommRingCat.of (A ⊗[DRLevel.R q] O))))
    (e.hom.base w) trivial).trans (le_of_eq ?_)
  exact (ringKrullDim_eq_of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[DRLevel.R q] O))).commRingCatIsoToRingEquiv)

end Geo

end ECL_Dim2

open ECL_Dim2 in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    (z : ↥(DRLevel.XO (N₀ := N₀) ρO)) :
    ringKrullDim ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk z) ≤ 2 := by
  letI := ρO.toAlgebra
  have hdim : ∀ (j : ↥(modularFunctionFieldFull (N₀ * q))), ringKrullDim (↥(chartAlg (N₀ * q) q {j}) ⊗[DRLevel.R q] O) ≤ 2 := by
    intro j
    obtain ⟨ψ, hψ⟩ := exists_algHom_isIntegral (N₀ * q) q j
    exact (ringKrullDim_eq_of_ringEquiv (Algebra.TensorProduct.comm (DRLevel.R q) ↥(chartAlg (N₀ * q) q {j}) O).toRingEquiv).trans_le
      (ringKrullDim_tensorProduct_le_two (DRLevel.R q) O ↥(chartAlg (N₀ * q) q {j}) ψ hψ)
  rcases mem_range_ιFin_or_mem_range_ιInf (N₀ * q) q ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).base z) with h | h
  · exact (ringKrullDim_stalk_le_of_chart O ρO (ιFin (N₀ * q) q) (ιFin_igusaTo (N₀ * q) q) z h).trans (hdim _)
  · exact (ringKrullDim_stalk_le_of_chart O ρO (ιInf (N₀ * q) q) (ιInf_igusaTo (N₀ * q) q) z h).trans (hdim _)

end S_ModularCurve_DRModelPackageLevel_ringKrullDim_stalk_XO_le_two
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_ringKrullDim_stalk_XO_le_two (solution)
