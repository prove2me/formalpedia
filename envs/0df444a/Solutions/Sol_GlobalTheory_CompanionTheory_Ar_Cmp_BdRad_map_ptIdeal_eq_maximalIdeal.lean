-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.map_ptIdeal_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:30:23.273616+00:00
-- url     : https://prove2.me/submissions/a59cc12f-8fb7-4fd0-be71-36b1f2c89405

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RegDom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_RegularSystemOfParametersLocalRing
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_isUnit_algebraMap_locRing_iff
import Theorems.Thm_ReciprocityTheory_AnForm_R_exists_mk_locRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.BdRad
open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
variable {m : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.Cmp.BdRad
theorem _root_.solution (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (hp : ∀ h ∈ I, eval t h = 0) [IsLocalRing (locRing I t)] :
    Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) = IsLocalRing.maximalIdeal (locRing I t) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_algebraMap_locRing_iff I t hp, not_not]
    exact RingHom.mem_ker.mp ha
  · intro x hx
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t x
    have hbu := (isUnit_algebraMap_locRing_iff I t hp b).mpr hb
    have hxn : ¬ IsUnit x := hx
    have ha : eval t a = 0 := by
      by_contra hne
      have hau := (isUnit_algebraMap_locRing_iff I t hp a).mpr hne
      rw [← hab] at hau
      exact hxn (isUnit_of_mul_isUnit_left hau)
    obtain ⟨u, hu⟩ := hbu
    have hx' : x = algebraMap _ (locRing I t) a * ↑u⁻¹ := by
      rw [← hab, ← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [hx']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr ha))
end GlobalTheory.CompanionTheory.Ar.Cmp.BdRad
