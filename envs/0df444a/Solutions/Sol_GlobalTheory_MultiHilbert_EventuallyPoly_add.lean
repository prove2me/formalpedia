-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.EventuallyPoly.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:44.184188+00:00
-- url     : https://prove2.me/submissions/672c6a27-da2d-4b75-b70b-126b630e0467

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
variable {r : ℕ}
namespace GlobalTheory.MultiHilbert
namespace EventuallyPoly
theorem _root_.solution {f g : (Fin r → ℕ) → ℚ} (hf : EventuallyPoly f)
    (hg : EventuallyPoly g) : EventuallyPoly (fun n => f n + g n) := by
  obtain ⟨Φ, a, h⟩ := hf
  obtain ⟨Ψ, b, h'⟩ := hg
  refine ⟨Φ + Ψ, max a b, fun n hn => ?_⟩
  rw [map_add, ← h n (fun k => (le_max_left _ _).trans (hn k)),
    ← h' n (fun k => (le_max_right _ _).trans (hn k))]
end EventuallyPoly
end GlobalTheory.MultiHilbert
