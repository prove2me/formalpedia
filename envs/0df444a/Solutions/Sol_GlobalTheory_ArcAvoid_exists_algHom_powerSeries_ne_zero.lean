-- Prove2me | solution 1 for GlobalTheory.ArcAvoid.exists_algHom_powerSeries_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:39:40.040127+00:00
-- url     : https://prove2.me/submissions/8465a7a0-ee43-434b-bcce-ffe4b26c15e5

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
import Theorems.Thm_GlobalTheory_ArcAvoid_exists_injective_of_height_le_one
import Theorems.Thm_GlobalTheory_exists_mem_height_map_le_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.ArcAvoid
namespace GlobalTheory.ArcAvoid
theorem _root_.solution :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [IsDomain B] [Algebra k B]
      [Algebra.FiniteType k B] (m : Ideal B), m.IsMaximal → ∀ f : B, f ≠ 0 →
      ∃ φ : B →ₐ[k] PowerSeries k, φ f ≠ 0 ∧
        ∀ b, b ∈ m ↔ PowerSeries.constantCoeff (φ b) = 0 := by
  intro k _ _ B _ _ _ _ m hm f hf
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨q, hqf, hqm, hht⟩ := exists_mem_height_map_le_one m (PrimeSpectrum.basicOpen f).isOpen
    ⟨⊥, hf, bot_le⟩
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have hcomap : (m.map (Ideal.Quotient.mk q.asIdeal)).comap (Ideal.Quotient.mk q.asIdeal) = m := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hqm
  have : (m.map (Ideal.Quotient.mk q.asIdeal)).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm).resolve_left fun e => by
      rw [e, Ideal.comap_top] at hcomap
      exact hm.ne_top hcomap.symm
  obtain ⟨φ, hφi, hφm⟩ := exists_injective_of_height_le_one (k := k) _ hht
  refine ⟨φ.comp (Ideal.Quotient.mkₐ k q.asIdeal), fun h => hqf ?_, fun b => ?_⟩
  · exact Ideal.Quotient.eq_zero_iff_mem.mp (hφi (h.trans (map_zero φ).symm))
  · conv_lhs => rw [← hcomap]
    exact hφm _
end GlobalTheory.ArcAvoid
