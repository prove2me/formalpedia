-- Prove2me | solution 1 for OAI.MatchingSmoothing.Pairing.lowDegree_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:15:30.748834+00:00
-- url     : https://prove2.me/submissions/933d96c8-89a9-4c5b-91b0-79c40fb45d47

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/EquivariantCompression.lean:L24-L44
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.Pairing.lowDegree_invariant. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression

-- ---- from OAI.Combinatorics.MatchingPSD.EquivariantCompression ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
namespace Pairing
variable {V : Type u_1}

lemma act_pointwise_mul (p : Equiv.Perm V) (f g : Pairing V → ℝ) :
    act p (f * g) = act p f * act p g := rfl

lemma act_pointwise_one (p : Equiv.Perm V) : act p (1 : Pairing V → ℝ) = 1 := rfl

lemma act_edgeCoord (p : Equiv.Perm V) (e : V × V) :
    act p (edgeCoord e) = edgeCoord (p e.1, p e.2) := by
  classical
  ext M
  simp only [act_apply, edgeCoord, relabel_apply, inv_inv]
  congr 1
  exact propext p.symm_apply_eq

lemma lowDegree_invariant (p : Equiv.Perm V) (d : ℕ)
    (f : Pairing V → ℝ) (hf : f ∈ lowDegree edgeCoord d) :
    act p f ∈ lowDegree edgeCoord d := by
  apply Submodule.span_induction (p := fun f _ => act p f ∈ lowDegree edgeCoord d)
    _ _ _ _ hf
  · rintro f ⟨l, hl, rfl⟩
    have hprod : act p ((l.map edgeCoord).prod) =
        ((l.map (fun e => (p e.1, p e.2))).map edgeCoord).prod := by
      clear hl
      induction l with
      | nil => exact act_pointwise_one p
      | cons e l ih =>
        simp only [List.map_cons, List.prod_cons, act_pointwise_mul,
          act_edgeCoord, ih]
    rw [hprod]
    exact Submodule.subset_span ⟨_, by simpa, rfl⟩
  · simp
  · intro f g _ _ hf hg
    simpa only [map_add] using (lowDegree edgeCoord d).add_mem hf hg
  · intro c f _ hf
    simpa only [map_smul] using (lowDegree edgeCoord d).smul_mem c hf

end Pairing

open scoped RealInnerProductSpace
section EuclideanPermutations
variable {X : Type u_2} [Fintype X]

end EuclideanPermutations

section CompressionEquivariance
variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end CompressionEquivariance
end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing OAI.MatchingSmoothing.Pairing


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.Pairing.lowDegree_invariant := @_root_.OAI.MatchingSmoothing.Pairing.lowDegree_invariant
