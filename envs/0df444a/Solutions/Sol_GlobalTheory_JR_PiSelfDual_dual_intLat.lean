-- Prove2me | solution 1 for GlobalTheory.JR.PiSelfDual.dual_intLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:02:57.791883+00:00
-- url     : https://prove2.me/submissions/97aa31ae-982d-435c-a1a6-1c9a3ea80de2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSelfDualPiHaarTraceStarDotProductUnramified
import Theorems.Thm_GlobalTheory_JR_PiSelfDual_trForm_apply
import Theorems.Thm_GlobalTheory_T_unramifiedStandardAddChar_conductor_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.PiSelfDual
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]
namespace GlobalTheory.JR.PiSelfDual
theorem _root_.solution (r : ℕ) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    {y : Fin r → E | ∀ x ∈ intLat (F := F) (E := E) r, ψ (trForm (F := F) r x y) = 1} =
      ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) := by
  classical
  haveI : IsUltrametricDist E := Unram.ultraE F
  have key := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.2
  ext y
  constructor
  · intro hy i
    refine (key (y i)).1 (fun e he => ?_)
    have hx : Pi.single i (star e) ∈ intLat (F := F) (E := E) r := by
      intro j
      by_cases hj : j = i
      · subst hj; simp [Unram.norm_star (F := F), he]
      · simp [Pi.single_apply, hj]
    have := hy _ hx
    rwa [trForm_apply, Pi.star_single, star_star, single_dotProduct] at this
  · intro hy x hx
    have hn : ‖star x ⬝ᵥ y‖ ≤ 1 := by
      unfold dotProduct
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => ?_)
      rw [norm_mul, Pi.star_apply, Unram.norm_star (F := F)]
      exact mul_le_one₀ (hx i) (norm_nonneg _) (hy i)
    have := (key 1).2 (by simp) (star x ⬝ᵥ y) hn
    rwa [mul_one] at this
end GlobalTheory.JR.PiSelfDual
