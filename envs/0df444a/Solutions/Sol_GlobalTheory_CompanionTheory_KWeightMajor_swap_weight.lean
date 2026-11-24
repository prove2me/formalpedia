-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KWeightMajor.swap_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:21:54.678802+00:00
-- url     : https://prove2.me/submissions/3ce6c9bb-f16b-4d90-848a-5839423ab734

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsPowEqZero
import Theorems.Thm_GlobalTheory_CompanionTheory_KWeightMajor_swap_weight_of_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_inner_eq_zero_of_weight
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kcomm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kstab_orthogonal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Formalism.REAL (KHighest IsWeight CasK kSpan)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open GlobalTheory.CompanionTheory.KLowSpan (kcomm_apply inner_eq_zero_of_weight kstab_orthogonal)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KWeightMajor
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}
namespace GlobalTheory.CompanionTheory.KWeightMajor
theorem _root_.solution (hF : KRel ε E) (hU : KUnit ε E) {L : Submodule ℂ V} [FiniteDimensional ℂ L]
    (hL : KStab ε E L) {a b : Fin n} (hab : a ≠ b) (he : ε a = ε b)
    {μ : Fin n → ℝ} {z : V} (hzL : z ∈ L) (hz0 : z ≠ 0) (hz : IsWeight E μ z) :
    ∃ z' ∈ L, z' ≠ 0 ∧ IsWeight E (μ ∘ Equiv.swap a b) z' := by
  rcases le_total (μ a) (μ b) with h | h
  · exact swap_weight_of_le hF hU hL hab he hzL hz0 hz h
  · obtain ⟨z', hz'L, hz'0, hz'⟩ := swap_weight_of_le hF hU hL (Ne.symm hab) he.symm hzL hz0 hz h
    exact ⟨z', hz'L, hz'0, by rwa [Equiv.swap_comm] at hz'⟩
end GlobalTheory.CompanionTheory.KWeightMajor
