-- Prove2me | solution 1 for GlobalTheory.ArcAvoid.exists_ringEquiv_powerSeries_of_complete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:49.682902+00:00
-- url     : https://prove2.me/submissions/d6e12910-b24e-4084-aa6a-b9e02d805ec1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_StalkGenericPointSpecializesOfSpecializes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRingEquivPowerSeriesOfComplete
import Theorems.Thm_GlobalTheory_exists_algHom_powerSeries_apply_X_of_isAdicComplete
import Theorems.Thm_GlobalTheory_powerSeriesPrimeX_asIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.powerSeriesPrimeX_asIdeal



set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.ArcAvoid
namespace GlobalTheory.ArcAvoid
theorem _root_.solution {k O : Type*} [Field k] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (ι : k →+* O)
    (hι : Function.Surjective ((residue O).comp ι)) :
    ∃ e : PowerSeries k ≃+* O, ∀ a, e (PowerSeries.C a) = ι a := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨ev, hev⟩ := exists_algHom_powerSeries_apply_X_of_isAdicComplete (maximalIdeal O)
    (π := π) (by rw [hπ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self π)
  let ψ : PowerSeries k →+* O := (ev : PowerSeries O →+* O).comp (PowerSeries.map ι)
  have hX : ψ PowerSeries.X = π := by simp [ψ, hev]
  have hC : ∀ a, ψ (PowerSeries.C a) = ι a := fun a => by
    simpa [ψ] using ev.commutes (ι a)
  have hmap : (Ideal.span {(PowerSeries.X : PowerSeries k)}).map ψ = maximalIdeal O := by
    rw [Ideal.map_span, Set.image_singleton, hX, hπ.maximalIdeal_eq]
  have hH : IsHausdorff ((Ideal.span {(PowerSeries.X : PowerSeries k)}).map ψ) O := by
    rw [hmap]; infer_instance
  have hs : Function.Surjective ψ := by
    refine surjective_of_mk_map_comp_surjective (I := Ideal.span {PowerSeries.X}) ψ ?_
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hι (residue O y)
    refine ⟨PowerSeries.C a, ?_⟩
    rw [RingHom.comp_apply, hC, Ideal.Quotient.eq, hmap]
    exact Ideal.Quotient.eq.mp ha
  have hi : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    obtain ⟨n, u, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 (PowerSeries.X_irreducible (R := k))
    rw [map_mul, map_pow, (u.isUnit.map _).mul_right_eq_zero, hX] at ha
    exact hπ.ne_zero (eq_zero_of_pow_eq_zero ha)
  exact ⟨RingEquiv.ofBijective ψ ⟨hi, hs⟩, hC⟩
end GlobalTheory.ArcAvoid
