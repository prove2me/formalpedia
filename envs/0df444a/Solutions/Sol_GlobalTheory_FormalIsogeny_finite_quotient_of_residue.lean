-- Prove2me | solution 1 for GlobalTheory.FormalIsogeny.finite_quotient_of_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:16:30.559022+00:00
-- url     : https://prove2.me/submissions/b740e580-4564-4d6e-89b1-bf23ce627e99

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Theorems.Thm_GlobalTheory_FormalIsogeny_finite_of_finite_quotient_map
import Theorems.Thm_GlobalTheory_FormalIsogeny_mem_maximalIdeal_iff_constantCoeff
import Theorems.Thm_GlobalTheory_FormalIsogeny_mem_map_C_of_coeff_mem
import Theorems.Thm_GlobalTheory_FormalIsogeny_map_surjective_of_surjective
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open GlobalTheory GlobalTheory.FormalIsogeny
variable {R : Type*} [CommRing R] {σ τ : Type*}
variable [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Finite σ]
namespace GlobalTheory.FormalIsogeny
theorem _root_.solution (J : Ideal (MvPowerSeries σ R))
    (h : Module.Finite (ResidueField R)
      (MvPowerSeries σ (ResidueField R) ⧸ J.map (MvPowerSeries.map (residue R)))) :
    Module.Finite R (MvPowerSeries σ R ⧸ J) := by
  have h1 : IsHausdorff (maximalIdeal R) (MvPowerSeries σ R ⧸ J) := by
    refine IsHausdorff.of_map (J := maximalIdeal (MvPowerSeries σ R)) ?_
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    exact mem_maximalIdeal_iff_constantCoeff.2 hr
  have h2 := (IsHausdorff.map_algebraMap_iff (S := MvPowerSeries σ R ⧸ J)).2 h1
  have h3 : Module.Finite R
      (MvPowerSeries σ (ResidueField R) ⧸ J.map (MvPowerSeries.map (residue R))) :=
    .trans (ResidueField R) _
  have hsurj := map_surjective_of_surjective (σ := σ) (residue_surjective (R := R))
  let p : MvPowerSeries σ R →ₐ[R]
      MvPowerSeries σ (ResidueField R) ⧸ J.map (MvPowerSeries.map (residue R)) :=
    (Ideal.Quotient.mkₐ R _).comp
      { MvPowerSeries.map (residue R) with
        commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }
  have hp : Function.Surjective p := Ideal.Quotient.mk_surjective.comp hsurj
  let q : MvPowerSeries σ R →ₐ[R] (MvPowerSeries σ R ⧸ J) ⧸
      (maximalIdeal R).map (algebraMap R (MvPowerSeries σ R ⧸ J)) :=
    (Ideal.Quotient.mkₐ R _).comp (Ideal.Quotient.mkₐ R _)
  have hq : Function.Surjective q :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hpq : ∀ g ∈ RingHom.ker p, q g = 0 := by
    intro g hg
    have h4 : MvPowerSeries.map (residue R) g ∈ J.map (MvPowerSeries.map (residue R)) :=
      Ideal.Quotient.eq_zero_iff_mem.1 hg
    obtain ⟨u, hu, hug⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 h4
    have h5 : g - u ∈ (maximalIdeal R).map (C : R →+* MvPowerSeries σ R) :=
      mem_map_C_of_coeff_mem (IsNoetherian.noetherian _) fun d => by
        rw [← residue_eq_zero_iff, ← coeff_map, map_sub, hug, sub_self, map_zero]
    have h6 := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) h5
    rw [Ideal.map_map, map_sub, Ideal.Quotient.eq_zero_iff_mem.2 hu, sub_zero] at h6
    exact Ideal.Quotient.eq_zero_iff_mem.2 h6
  have h7 : Module.Finite R (MvPowerSeries σ R ⧸ RingHom.ker p) :=
    .equiv (Ideal.quotientKerAlgEquivOfSurjective hp).symm.toLinearEquiv
  have h8 : Module.Finite R ((MvPowerSeries σ R ⧸ J) ⧸
      (maximalIdeal R).map (algebraMap R (MvPowerSeries σ R ⧸ J))) :=
    Module.Finite.of_surjective (Ideal.Quotient.liftₐ _ q hpq).toLinearMap
      (Ideal.Quotient.lift_surjective_of_surjective _ hpq hq)
  exact finite_of_finite_quotient_map (maximalIdeal R)
end GlobalTheory.FormalIsogeny
