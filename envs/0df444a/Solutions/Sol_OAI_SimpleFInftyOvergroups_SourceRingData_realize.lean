-- Prove2me | solution 1 for OAI.SimpleFInftyOvergroups.SourceRingData.realize
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:03:45.019317+00:00
-- url     : https://prove2.me/submissions/42b0e0cd-c4b3-442d-a277-12fb0bd6dbb4

import Mathlib
import Definitions.Def_SimpleOvergroups
import Definitions.Def_OAIQ66So033
import Theorems.Thm_OAI_StageGeometry_simple_geometric_overgroup_of_corner_ring_data

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EnlargementCore
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SourceEnlargement

variable {D V Z : Type*} [Ring D] [Group V] [MulAction V Z]

lemma unitMap_identity_injective [Nontrivial D] :
    Function.Injective (unitMap (V := V) (1 : D) (one_mul 1)) := by
  intro g h hgh
  have he := congrArg Units.val hgh
  simp only [unitMap_val, value_identity] at he
  exact MonoidAlgebra.single_left_injective one_ne_zero he

variable (P : Set D) (hP : ∀ E ∈ P, E * E = E)

lemma map_identity_injective [Nontrivial D] (h1 : 1 ∈ P) :
    Function.Injective (map (V := V) P hP ⟨1, h1⟩) := by
  intro g h he
  apply unitMap_identity_injective (D := D)
  exact congrArg Subtype.val he

lemma basis_injective [Nontrivial D] :
    Function.Injective (fun z : Z => Finsupp.single z (1 : D)) :=
  Finsupp.single_left_injective one_ne_zero

end SourceEnlargement
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_TwoEnlargements
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SimpleFInftyOvergroups.SemanticEncoding.IdempotentNames.instFintypeElemSubtypeEndSpaceMemSubalgebraAlgebraIndexOfFinite _root_.OAI.SimpleFInftyOvergroups.SemanticEncoding.IdempotentNames.instPrimcodableElemSubtypeEndSpaceMemSubalgebraAlgebraIndexOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SourceEnlargement

section OneLayer
variable (K : Type) [CommRing K]
variable (V Z : Type) [Group V] [MulAction V Z]

variable {V Z}

lemma groupEmbedding_injective [Nontrivial K] :
    Function.Injective (groupEmbedding (V := V) K) :=
  map_identity_injective (BinaryPrefixOperators.idempotents K)
    (fun _ h => BinaryPrefixOperators.idempotents_are_idempotent K h)
    (BinaryPrefixOperators.identity_mem K)

lemma pointEmbedding_injective [Nontrivial K] :
    Function.Injective (pointEmbedding (Z := Z) K) := basis_injective

end OneLayer

namespace Saturation
variable {W X Y : Type} [Group W] [MulAction W Y] (t : X → Y)

lemma point_injective (ht : Function.Injective t) :
    Function.Injective (point (W := W) t) := fun _ _ e => ht (congrArg Subtype.val e)

lemma equivariant {Q : Type} [Group Q] [MulAction Q X] (i : Q →* W)
    (h : ∀ q x, i q • t x = t (q • x)) (q : Q) (x : X) :
    i q • point (W := W) t x = point t (q • x) := Subtype.ext (h q x)

end Saturation

namespace Double
variable (Q X : Type) [Group Q] [MulAction Q X]

variable {Q X}

lemma iota_injective : Function.Injective (iota (Q := Q)) :=
  (groupEmbedding_injective (ZMod 3)).comp (groupEmbedding_injective (ZMod 2))

lemma ambientPoint_injective : Function.Injective (ambientPoint (X := X)) :=
  (pointEmbedding_injective (ZMod 3)).comp (pointEmbedding_injective (ZMod 2))

lemma iota_ambientPoint (q : Q) (x : X) :
    (iota q • ambientPoint x : AmbientY X) = ambientPoint (q • x) := by
  change (groupEmbedding (ZMod 3) (groupEmbedding (ZMod 2) q) •
    pointEmbedding (ZMod 3) (pointEmbedding (ZMod 2) x) : AmbientY X) = _
  rw [groupEmbedding_pointEmbedding, groupEmbedding_pointEmbedding]
  rfl

lemma point_injective : Function.Injective (point (Q := Q) (X := X)) :=
  Saturation.point_injective _ ambientPoint_injective

lemma iota_point (q : Q) (x : X) :
    iota q • point (Q := Q) x = point (Q := Q) (q • x) :=
  Saturation.equivariant _ _ iota_ambientPoint q x

end Double
end SourceEnlargement
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SourceRingReduction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.SimpleFInftyOvergroups.SemanticEncoding.IdempotentNames.instFintypeElemSubtypeEndSpaceMemSubalgebraAlgebraIndexOfFinite _root_.OAI.SimpleFInftyOvergroups.SemanticEncoding.IdempotentNames.instPrimcodableElemSubtypeEndSpaceMemSubalgebraAlgebraIndexOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SimpleFInftyOvergroups
open StageConstruction SourceEnlargement
open scoped Classical

namespace SourceRingData
variable {G : Type} [Group G]

theorem realize_oai (d : SourceRingData G) :
    ∃ (H : Type) (_ : Group H), Nontrivial H ∧ IsSimpleGroup H ∧
      HasTypeFInfty H ∧ ∃ f : G →* H, Function.Injective f := by
  let _ := d.ringR
  let _ := d.nontrivialR
  let _ := d.algebraR
  let _ := d.finiteA
  exact StageGeometry.simple_geometric_overgroup_of_corner_ring_data
    d.φ d.binary d.e d.e_idempotent d.e_nonzero d.S d.T
    (by
      intro y z
      by_cases h : y = z
      · simpa only [ite_eq_left h] using d.TS y z
      · simpa only [ite_eq_right h] using d.TS y z) d.ρ
    (Double.iota (Q := Q d.R)) (Double.point (Q := Q d.R) (X := X d.R))
    d.ρS d.Tρ Double.iota_point d.φ_injective d.ρ_injective
    Double.iota_injective Double.point_injective Double.diagrams₂ Double.diagrams₃
    d.A d.π.toRingHom d.π_surjective d.rel d.rel_finite d.ker_π d.g d.g_injective

end SourceRingData

universe u

end SimpleFInftyOvergroups
end

end OAI
end

theorem solution : type_of% @OAI.SimpleFInftyOvergroups.SourceRingData.realize_oai := @OAI.SimpleFInftyOvergroups.SourceRingData.realize_oai
