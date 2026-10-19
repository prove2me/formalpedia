-- Prove2me | solution 1 for OAI.AffinePSD.psd_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:28:53.553565+00:00
-- url     : https://prove2.me/submissions/22f3d2b4-d5fc-4eb1-8c7b-c7d6a3178836

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/PSDTopology.lean:L11-L27
-- (upload_full_project.md Phase 4): solution for node OAI.AffinePSD.psd_isClosed. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation

-- ---- from OAI.Combinatorics.MatchingPSD.PSDTopology ----
namespace OAI

namespace AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

omit [Fintype I] [DecidableEq R] in
lemma psd_isClosed : IsClosed {A : Matrix R R ℝ | A.PosSemidef} := by
  have he : {A : Matrix R R ℝ | A.PosSemidef} =
      {A : Matrix R R ℝ | Aᵀ = A} ∩
        ⋂ x : R → ℝ, {A : Matrix R R ℝ | 0 ≤ x ⬝ᵥ (A *ᵥ x)} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec, star_trivial]
    rfl
  rw [he]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_id
  · apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    simp only [dotProduct, Matrix.mulVec]
    fun_prop

end AffinePSD

end OAI

-- ---- platform node ----
open OAI OAI.AffinePSD
open Matrix Finset
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.AffinePSD.psd_isClosed := @_root_.OAI.AffinePSD.psd_isClosed
