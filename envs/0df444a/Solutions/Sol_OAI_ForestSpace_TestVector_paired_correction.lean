-- Prove2me | solution 1 for OAI.ForestSpace.TestVector.paired_correction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:44:14.047272+00:00
-- url     : https://prove2.me/submissions/e944c558-611a-4588-be0c-0c32ecb0e0bf

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Completion.lean:L361-L380
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.TestVector.paired_correction. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Theorems.Thm_OAI_ForestSpace_finsupp_paired_correction

-- ---- from OAI.Analysis.ForestSpace.Completion ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

namespace TestVector
variable {V : Type}
variable [PartialOrder V]
 theorem paired_correction (hF : ForestOrder V) (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (H : Set V) (hH : IsLowerSet H) (f k : TestVector V)
    (hf : SupportedOn f H) (hk : SupportedOn k Hᶜ)
    (hf₁ : ‖f‖ ≤ 1) (hk₁ : ‖k‖ ≤ 1) (s : ℝ) (hs : 0 < s) :
    ∃ c : TestVector V, SupportedOn c Hᶜ ∧ ‖c‖ ≤ 1 ∧
      ‖f + s • (c + k)‖ ≤ Real.sqrt (1 + 12 * s ^ 2) ∧
      ‖f + s • (c - k)‖ ≤ Real.sqrt (1 + 12 * s ^ 2) := by
  have hf' : TestBound f 1 := by simpa using (norm_le_iff_testBound f zero_le_one).mp hf₁
  have hk' : TestBound k 1 := by simpa using (norm_le_iff_testBound k zero_le_one).mp hk₁
  obtain ⟨c,hcH,hc,hcp,hcm⟩ := finsupp_paired_correction hF hAnc H hH
    f.toFinsupp k.toFinsupp hf hk hf' hk' s hs
  refine ⟨c,hcH, ?_, ?_, ?_⟩
  · exact (norm_le_iff_testBound _ zero_le_one).mpr (by
      change TestBound c (1 ^ 2); simpa only [one_pow] using hc)
  · apply (norm_le_iff_testBound _ (Real.sqrt_nonneg _)).mpr
    rw [Real.sq_sqrt (by positivity)]
    exact hcp
  · apply (norm_le_iff_testBound _ (Real.sqrt_nonneg _)).mpr
    rw [Real.sq_sqrt (by positivity)]
    exact hcm

end TestVector

end

end ForestSpace

end OAI

-- ---- platform node ----
open OAI OAI.ForestSpace OAI.ForestSpace.TestVector
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ForestSpace.TestVector.paired_correction := @_root_.OAI.ForestSpace.TestVector.paired_correction
