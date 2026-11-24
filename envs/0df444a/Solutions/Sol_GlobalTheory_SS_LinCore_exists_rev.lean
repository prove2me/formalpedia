-- Prove2me | solution 1 for GlobalTheory.SS.LinCore.exists_rev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:34:13.376403+00:00
-- url     : https://prove2.me/submissions/1ddd2247-2f9f-497d-8ffe-7b558545e6b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankLeOfWeightsUnipotentSymplectic
import Theorems.Thm_GlobalTheory_SS_LinCore_aeval_rev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LinCore
open Polynomial
namespace GlobalTheory.SS.LinCore
theorem _root_.solution {A : Type} [Ring A] [Algebra ℚ A] (u v : A) (h : u * v = 1) (R : ℚ[X])
    (hR : ∀ β : ℂ, aeval β R = 0 → ‖β‖ ≤ 1) (hv : aeval v R = 0) :
    ∃ R' : ℚ[X], (∀ β : ℂ, aeval β R' = 0 → 1 ≤ ‖β‖) ∧ aeval u R' = 0 := by
  refine ⟨_, ?_, by rw [aeval_rev u v h R, hv, mul_zero]⟩
  intro β hβ
  have hR0 : R ≠ 0 := by
    rintro rfl
    have := hR 2 (by simp)
    norm_num at this
  by_cases hb : β = 0
  · exfalso
    subst hb
    rw [map_sum, Finset.sum_eq_single R.natDegree] at hβ
    · simp [hR0] at hβ
    · intro i hi hne
      have hi' : i ≤ R.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have : R.natDegree - i ≠ 0 := by omega
      simp [this]
    · simp
  · rw [aeval_rev β β⁻¹ (mul_inv_cancel₀ hb) R] at hβ
    have h1 := hR _ ((mul_eq_zero.mp hβ).resolve_left (pow_ne_zero _ hb))
    rw [norm_inv] at h1
    exact (inv_le_one₀ (norm_pos_iff.mpr hb)).mp h1
end GlobalTheory.SS.LinCore
