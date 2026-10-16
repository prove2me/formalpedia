-- Prove2me | solution 1 for OAI.Erdos3.RankPreparationFamily.PreparedHeights.euclideanJetLayers_compact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-15T21:56:48.410731+00:00
-- url     : https://prove2.me/submissions/94acf37c-0b40-42f3-9c3c-9053484ea447

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B129

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativePositivePassage
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.euclideanJetLayers_compact
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (O : Fin m → Type*) :
    CompactSpace (EuclideanJetLayers (fun j => (L j).space) O) := by
  let : ∀ j, CompactSpace (euclideanSubspace (L j).space ⧸
      (latticeSection (standardEuclideanLattice (L j).Coord)
        (euclideanSubspace (L j).space)).toAddSubgroup) :=
    hL.euclideanLayerTorus_compact L hp hR
  dsimp only [EuclideanJetLayers]
  infer_instance

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open VectorPolynomial Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal TensorProduct
attribute [local irreducible] integerBox

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.RankPreparationFamily.PreparedHeights.euclideanJetLayers_compact.{u_1} := @OAI.Erdos3.RankPreparationFamily.PreparedHeights.euclideanJetLayers_compact.{u_1}
