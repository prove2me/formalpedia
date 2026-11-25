-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.map_ptIdeal_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:26:17.568357+00:00
-- url     : https://prove2.me/submissions/d4a6a4a8-4535-4f29-b49c-b47ad9892f4b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_PrimesBelowParams
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages GlobalTheory.CompanionTheory.Ar.Cmp
variable {m : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
theorem _root_.solution {I : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ}
    (hI : ∀ h ∈ I, eval t h = 0) [IsLocalRing (locRing I t)] :
    Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) = IsLocalRing.maximalIdeal (locRing I t) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_algebraMap_locRing_iff I t hI]
    simpa using RingHom.mem_ker.mp hg
  · intro x hx
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t x
    have hbu := (isUnit_algebraMap_locRing_iff I t hI b).mpr hb
    have ha : a ∈ ptIdeal t := by
      refine RingHom.mem_ker.mpr ?_
      by_contra hne
      have hau := (isUnit_algebraMap_locRing_iff I t hI a).mpr hne
      rw [← hab] at hau
      exact ((IsLocalRing.mem_maximalIdeal _).mp hx) (isUnit_of_mul_isUnit_left hau)
    obtain ⟨v, hv⟩ := hbu.exists_right_inv
    have : x = algebraMap _ (locRing I t) a * v := by
      rw [← hab, mul_assoc, hv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
