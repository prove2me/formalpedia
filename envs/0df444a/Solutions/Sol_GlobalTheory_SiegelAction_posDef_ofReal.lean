-- Prove2me | solution 1 for GlobalTheory.SiegelAction.posDef_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:48:12.670352+00:00
-- url     : https://prove2.me/submissions/d1c6790f-eb60-4e85-a410-4ce56e536c31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SiegelAction
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace GlobalTheory.SiegelAction
theorem _root_.solution {Y : Matrix ι ι ℝ} (h : Y.PosDef) :
    (Y.map (fun t => (t : ℂ))).PosDef := by
  have hs : ∀ i j, Y i j = Y j i := fun i j => by
    have := congrFun (congrFun h.isHermitian j) i
    simpa using this
  have hH : (Y.map (fun t => (t : ℂ))).IsHermitian := by
    ext i j
    simp [hs i j]
  refine PosDef.of_dotProduct_mulVec_pos hH fun v hv => ?_
  have hre : (star v ⬝ᵥ (Y.map (fun t => (t : ℂ))) *ᵥ v).re =
      star (fun i => (v i).re) ⬝ᵥ Y *ᵥ (fun i => (v i).re) +
      star (fun i => (v i).im) ⬝ᵥ Y *ᵥ (fun i => (v i).im) := by
    simp [dotProduct, mulVec, Finset.mul_sum, Finset.sum_add_distrib]
  have him : (star v ⬝ᵥ (Y.map (fun t => (t : ℂ))) *ᵥ v).im = 0 := by
    have := hH.im_star_dotProduct_mulVec_self v
    simpa using this
  rw [Complex.pos_iff, hre, him]
  refine ⟨?_, rfl⟩
  by_cases h1 : (fun i => (v i).re) = 0
  · have h2 : (fun i => (v i).im) ≠ 0 := fun h2 => hv (by
      ext i
      exact Complex.ext (congrFun h1 i) (congrFun h2 i))
    exact add_pos_of_nonneg_of_pos (h.posSemidef.dotProduct_mulVec_nonneg _)
      (h.dotProduct_mulVec_pos h2)
  · exact add_pos_of_pos_of_nonneg (h.dotProduct_mulVec_pos h1)
      (h.posSemidef.dotProduct_mulVec_nonneg _)
end GlobalTheory.SiegelAction
