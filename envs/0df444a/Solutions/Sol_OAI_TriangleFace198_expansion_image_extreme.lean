-- Prove2me | solution 1 for OAI.TriangleFace198.expansion_image_extreme
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T15:56:55.88598+00:00
-- url     : https://prove2.me/submissions/4504bb2a-b767-4da1-86a6-ab0bb5a2f7e1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TriangleFace/MatchingImage.lean:L68-L84
-- (upload_full_project.md Phase 4): solution for node OAI.TriangleFace198.expansion_image_extreme. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Model
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Simplex
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Coupling
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Basic
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_OddCuts
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Contraction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Polytope
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Face
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Entropy
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Duality
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_EdgeReduction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_MinimalFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_FractionalReduction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Components
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_TriangleExpansion
import Theorems.Thm_OAI_TriangleFace198_expansion_image_eq

-- ---- from OAI.Combinatorics.MatchingEntropy.TriangleExpansion ----
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

section TriangleExpansion
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

end TriangleExpansion

section ExpansionSupport
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem triangleVertices_odd (v : V) : Odd (triangleVertices v).card := by
  have hcard : (triangleVertices v).card = 3 := by
    rw [triangleVertices,Finset.card_image_of_injective _ (triangleTip_injective v)]
    simp
  rw [hcard]
  norm_num

end ExpansionSupport
end MatchingEntropyBounds.Refined

end

end OAI

-- ---- from OAI.Combinatorics.TriangleFace.MatchingImage ----
namespace OAI

noncomputable section
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined
namespace TriangleFace198
universe uV uE
variable {V : Type uV} {E : Type uE} [instFintypeV : Fintype V] [Fintype E] [DecidableEq V] [instDecidableEqE : DecidableEq E]

theorem expansion_image_extreme (G : LooplessGraph V E) (c : E → Fin 3)
    (v : V) (hc : LocalLabels G v c) :
    IsExtreme ℝ (triangleExpansion G c v).polytope (localExtension G c v hc '' G.polytope) := by
  rw [expansion_image_eq]
  refine ⟨fun _ h => h.1, ?_⟩
  intro y hy z hz w hw hseg
  obtain ⟨a,b,ha,hb,hab,rfl⟩ := hseg
  refine ⟨hy,?_⟩
  have heq := hw.2
  rw [LooplessGraph.cutMass_linear] at heq
  have hyl := ((triangleExpansion G c v).polytope_subset_constraintPolytope hy).2.2 _ (triangleVertices_odd v)
  have hzl := ((triangleExpansion G c v).polytope_subset_constraintPolytope hz).2.2 _ (triangleVertices_odd v)
  apply le_antisymm _ hyl
  by_contra! hn
  have hpos := mul_pos ha (sub_pos.mpr hn)
  have hnonneg := mul_nonneg hb.le (sub_nonneg.mpr hzl)
  nlinarith

end TriangleFace198
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangleFace198
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined


theorem solution.{uV,uE} : type_of% @_root_.OAI.TriangleFace198.expansion_image_extreme.{uV,uE} := @_root_.OAI.TriangleFace198.expansion_image_extreme.{uV,uE}
