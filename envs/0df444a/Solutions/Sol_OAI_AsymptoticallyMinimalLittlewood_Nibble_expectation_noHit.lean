-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Nibble.expectation_noHit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:38:40.392696+00:00
-- url     : https://prove2.me/submissions/bc5e2ddf-bd1e-4ab4-beb6-5ffa036c8612

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/ProductProbability.lean:L119-L133
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Nibble.expectation_noHit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability

-- ---- from OAI.Analysis.Littlewood.ProductProbability ----
namespace OAI

universe uE uI

namespace AsymptoticallyMinimalLittlewood
namespace Nibble
open scoped BigOperators
open Finset

section ProductSpace
variable {E : Type uE} [Fintype E] [DecidableEq E]

lemma expectation_prod (p : ℝ) (g : E → Bool → ℝ) :
    expectation p (fun s ↦ ∏ e, g e (s e)) =
      ∏ e, (p * g e true + (1 - p) * g e false) := by
  dsimp [expectation, coinWeight]
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun e b ↦ (if b then p else 1 - p) * g e b)]
  simp

lemma expectation_noHit (p : ℝ) (A : Finset E) :
    expectation p (noHit A) = (1 - p) ^ A.card := by
  have heq (s : E → Bool) : noHit A s =
      ∏ e : E, if e ∈ A then (if s e then (0 : ℝ) else 1) else 1 := by
    rw [Finset.prod_ite_mem]
    simp [noHit]
  change expectation p (fun s ↦ noHit A s) = _
  simp_rw [heq]
  rw [expectation_prod p (fun e b ↦ if e ∈ A then (if b then (0 : ℝ) else 1) else 1)]
  calc
    _ = ∏ e : E, if e ∈ A then 1 - p else 1 := by
      apply Finset.prod_congr rfl
      intro e he
      by_cases h : e ∈ A <;> simp [h]
    _ = _ := by rw [Finset.prod_ite_mem]; simp

end ProductSpace

end Nibble
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Nibble
open scoped BigOperators
open Finset


theorem solution.{uE} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.expectation_noHit.{uE} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.expectation_noHit.{uE}
