-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.EventuallyPoly.of_shift_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:59:29.343879+00:00
-- url     : https://prove2.me/submissions/2000b11c-8be2-48f8-8132-46ae4b03de48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
import Theorems.Thm_GlobalTheory_MultiHilbert_eval_aeval_coord

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
theorem _root_.solution {f : (Fin r → ℕ) → ℚ} (e : Fin r → ℕ)
    (hf : EventuallyPoly (fun n => f (n + e))) : EventuallyPoly f := by
  obtain ⟨Φ, a, h⟩ := hf
  refine ⟨aeval (fun k => X k - C (e k : ℚ)) Φ, a + ∑ k, e k, fun n hn => ?_⟩
  have he : ∀ k, a + e k ≤ n k := fun k =>
    (Nat.add_le_add_left (Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)) a).trans (hn k)
  have h1 : n = (n - e) + e := by
    funext k
    have := he k
    simp only [Pi.add_apply, Pi.sub_apply]
    omega
  have h2 := h (n - e) (fun k => by have := he k; simp only [Pi.sub_apply]; omega)
  simp only [← h1] at h2
  rw [eval_aeval_coord, h2]
  congr 2
  funext k
  have := he k
  simp only [Pi.sub_apply, map_sub, eval_X, eval_C]
  rw [Nat.cast_sub (by omega)]
end EventuallyPoly
end GlobalTheory.MultiHilbert
