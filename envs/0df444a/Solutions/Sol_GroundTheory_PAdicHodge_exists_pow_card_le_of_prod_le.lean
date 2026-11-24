-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_pow_card_le_of_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:32:34.019793+00:00
-- url     : https://prove2.me/submissions/aadc8e8c-b010-4a9c-9368-df0c6a48d94e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
variable {E : Type*} [NormedField E] [IsUltrametricDist E]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ι : Type*} {s : Multiset ι} (hs : s ≠ 0) {f : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) {B : ℝ} (h : (s.map f).prod ≤ B) :
    ∃ i ∈ s, f i ^ Multiset.card s ≤ B := by
  obtain ⟨i, hi, hmin⟩ := Multiset.exists_min_image f hs
  refine ⟨i, hi, le_trans ?_ h⟩
  have key : ∀ t : Multiset ι, t ≤ s → f i ^ Multiset.card t ≤ (t.map f).prod := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simp
    | cons a t ih =>
      intro hts
      have ha : a ∈ s := Multiset.mem_of_le hts (Multiset.mem_cons_self a t)
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, mul_comm]
      refine mul_le_mul (hmin a ha) (ih ((Multiset.le_cons_self t a).trans hts))
        (pow_nonneg (hf i hi) _) (hf a ha)
  exact key s le_rfl
end GroundTheory.PAdicHodge
