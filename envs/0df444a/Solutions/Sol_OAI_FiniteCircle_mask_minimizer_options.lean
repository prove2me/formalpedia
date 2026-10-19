-- Prove2me | solution 1 for OAI.FiniteCircle.mask_minimizer_options
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:59:34.227986+00:00
-- url     : https://prove2.me/submissions/4f825fbe-dc03-4fc7-8fca-780183f5ffa3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/MaskSeparation.lean:L191-L213
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.mask_minimizer_options. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Theorems.Thm_OAI_FiniteCircle_mask_active_average_lower
import Theorems.Thm_OAI_FiniteCircle_mask_inactive_average_lower

-- ---- from OAI.Combinatorics.FiniteCircle.MaskSeparation ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

theorem mask_minimizer_options {h M l : ℕ} {p : ℕ → ℕ → ℕ}
    [∀ k : Fin h, NeZero (p l k)]
    (hh : 0 < h) (hd : ∀ k : Fin h, p l k ∣ M)
    (hp : ∀ k : Fin h, (p l k).Prime)
    (hlo : ∀ k : Fin h, h^3 ≤ p l k) (hhi : ∀ k : Fin h, p l k ≤ 2*h^3)
    (f : PhaseCost (ZMod M)) (x : ZMod M) :
    ∃ z : MaskResidues h p l,
      (let S := Finset.univ.filter (fun k : Fin h => z k ≠ 0)
       (∀ Q : ℝ, 0 ≤ Q → (∀ k ∈ S, Q ≤ f (subcircle (hd k) 1)) →
        (S.card : ℝ)/(4*h)*Q ≤ f.infAverage (maskPhaseHom h p M l hd) x) ∧
       (2*S.card ≤ h → (1/4:ℝ)*f (x+∑ k,subcircle (hd k) (z k)) ≤
         f.infAverage (maskPhaseHom h p M l hd) x)) := by
  classical
  let : ∀ k : Fin h, NeZero (p l k) := fun k => ⟨(hp k).ne_zero⟩
  obtain ⟨z,hz⟩ := f.exists_average_eq (maskPhaseHom h p M l hd) x
  refine ⟨z, ?_⟩
  dsimp only
  rw [hz]
  constructor
  · intro Q hQ hq
    exact mask_active_average_lower hh hd hp hlo hhi f x z Q hQ
      (fun k hk => hq k (by simp [hk]))
  · exact mask_inactive_average_lower hh hd hp hlo hhi f x z

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.mask_minimizer_options := @_root_.OAI.FiniteCircle.mask_minimizer_options
