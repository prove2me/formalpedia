-- Prove2me | solution 1 for GroundTheory.Arith.Toric.exists_add_smul_mem_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:52:53.637074+00:00
-- url     : https://prove2.me/submissions/7b83e194-5c6c-4e3c-96df-a3268fc3ce5c

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_IsFaceOfIffExistsEqExposedFace
import Theorems.Thm_GroundTheory_Arith_Toric_nonneg_of_mem_hull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
namespace GroundTheory.Arith.Toric
theorem _root_.solution (S : Finset V) {u w : Dual 𝕜 V}
    (hu : ∀ x ∈ hull 𝕜 (S : Set V), 0 ≤ u x)
    (hw : ∀ x ∈ exposedFace (hull 𝕜 (S : Set V)) u, 0 ≤ w x) :
    ∃ p : 𝕜, 0 ≤ p ∧ ∀ q : 𝕜, p ≤ q → ∀ x ∈ hull 𝕜 (S : Set V), 0 ≤ w x + q * u x := by
  classical
  refine ⟨∑ s ∈ S, |-w s / u s|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun q hq x hx => ?_⟩
  have key : ∀ s ∈ (S : Set V), 0 ≤ (w + q • u) s := by
    intro s hs
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    have hus := hu s (subset_hull hs)
    rcases hus.eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero, add_zero]
      exact hw s (mem_exposedFace.2 ⟨subset_hull hs, h0.symm⟩)
    · have h1 : -w s / u s ≤ q :=
        (le_abs_self _).trans ((Finset.single_le_sum (f := fun s => |-w s / u s|)
          (fun _ _ => abs_nonneg _) (Finset.mem_coe.1 hs)).trans hq)
      rw [div_le_iff₀ hpos] at h1
      linarith
  simpa using nonneg_of_mem_hull key hx
end GroundTheory.Arith.Toric
