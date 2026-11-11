-- Prove2me | solution 1 for OAI.HarmonicArtin.IsolatedIterationData.separation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:46:48.768028+00:00
-- url     : https://prove2.me/submissions/1f2daf46-1739-4991-bb79-302e03816c1d

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag013

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_BlockClosed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

omit [Fintype V] [DecidableEq A] in
lemma block_inclusion_projection (E:BasedComplex Q (K:=K) I) (T:Set I) :
    blockInclusion Q E T*blockProjection Q E T=projectiveIdentity Q (fun i:T=>E.placement i) := by
  rw [blockInclusion_mul Q E T _ _ (blockProjection_entries Q E T)]
  apply Matrix.ext
  intro i j
  change (if (i:I)=(j:I) then vertexId Q (K:=K) (E.placement i).color else 0)=
    (if i=j then vertexId Q (K:=K) (E.placement i).color else 0)
  simp only [Subtype.val_inj]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomSpace
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

namespace BasedComplex

variable [Fintype I] [Fintype J]

lemma homDifferential_square_zero (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n : ℤ)
    (f : Matrix I J (Q.Zigzag K)) :
    homDifferential Q E F (n + 1) (homDifferential Q E F n f) = 0 := by
  change E.differential * (E.differential * f - cochainSign n • (f * F.differential)) -
    cochainSign (n + 1) • ((E.differential * f - cochainSign n • (f * F.differential)) *
      F.differential) = 0
  have h₁ : E.differential * (E.differential * f) = 0 := by
    rw [← Matrix.mul_assoc, E.square_zero, Matrix.zero_mul]
  have h₂ : (f * F.differential) * F.differential = 0 := by
    rw [Matrix.mul_assoc, F.square_zero, Matrix.mul_zero]
  rw [cochainSign_add_one]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    h₁, h₂, neg_smul, smul_zero, sub_zero, zero_sub, Matrix.mul_assoc]
  abel

lemma homSpace_pure_total_degree_upper (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l)
    (hF : ∀ j, (F.placement j).level = k)
    (h : k - l + 2 < n + v) : homSpace Q E F n v = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply Matrix.ext
  intro i j
  by_contra he
  have hc : (F.placement j).cochain = (E.placement i).cochain + n := by
    by_contra hc
    exact he ((hf.2 i j).1 hc)
  have ha := homogeneous_nonzero_degree Q (hf.2 i j).2 he
  have he' := hE i
  have hf' := hF j
  dsimp only [GeneratorPlacement.level] at he' hf'
  omega

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_TraceLinear
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V]

namespace BasedComplex
variable [Fintype I] [Fintype J]

omit [Fintype V] in
lemma homBoundaries_le_homCycles (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homBoundaries Q E F n v ≤ homCycles Q E F n v := by
  rintro _ ⟨f, hf, rfl⟩
  constructor
  · change homDifferential Q E F (n - 1) f ∈ homSpace Q E F n v
    have hd := homDifferential_mem Q E F (n - 1) v hf
    rw [sub_add_cancel] at hd
    exact hd
  · change homDifferential Q E F n (homDifferential Q E F (n - 1) f) = 0
    simpa only [sub_add_cancel] using homDifferential_square_zero Q E F (n - 1) f

lemma supertrace_boundary (E : BasedComplex Q (K := K) I)
    (h : Matrix I I (Q.Zigzag K)) :
    supertrace Q E (homDifferential Q E E (-1) h) = 0 := by
  have hs : cochainSign (K := K) (-1) = -1 := by norm_num [cochainSign]
  have hp : cochainSign (K := K) 1 = -1 := by norm_num [cochainSign]
  change supertrace Q E (E.differential * h - cochainSign (K := K) (-1) • (h * E.differential)) = 0
  have hcyc := supertrace_mul Q E E E.degree h
  rw [hp] at hcyc
  calc
    _ = supertrace Q E (E.differential * h) -
        cochainSign (K := K) (-1) * supertrace Q E (h * E.differential) := by
      exact (supertrace Q E).map_sub _ _ |>.trans
        (congrArg (fun z => supertrace Q E (E.differential * h) - z)
          ((supertrace Q E).map_smul_of_tower (cochainSign (K := K) (-1)) (h * E.differential)))
    _ = 0 := by rw [hs, hcyc]; ring

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomSpaceDuality
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

attribute [local instance] OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.zigzagFiniteDimensional
lemma homSpace_finrank_dual (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    Module.finrank K (homSpace Q F E (-n) (2-v)) = Module.finrank K (homSpace Q E F n v) :=
  (homSpaceDuality Q E F n v).finrank_eq.trans Subspace.dual_finrank_eq

omit [DecidableEq A] in

lemma homDifferential_adjoint (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n : ℤ)
    (f : Matrix I J (Q.Zigzag K)) (g : Matrix J I (Q.Zigzag K)) :
    supertrace Q E (homDifferential Q E F (n-1) f * g) =
      cochainSign (K := K) n * supertrace Q E (f * homDifferential Q F E (-n) g) := by
  have hcyc := supertrace_mul Q E E E.degree (f*g)
  have hs := cochainSign_mul_self (K := K) n
  have hn : cochainSign (K := K) (n-1) = -cochainSign n := by
    have hh := cochainSign_add_one (K := K) (n-1)
    rw [sub_add_cancel] at hh
    linear_combination hh
  change supertrace Q E ((E.differential*f - cochainSign (K := K) (n-1) • (f*F.differential))*g) =
    cochainSign (K := K) n * supertrace Q E (f*(F.differential*g - cochainSign (K := K) (-n) • (g*E.differential)))
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    map_sub, map_sub, map_smul, map_smul]
  change supertrace Q E (E.differential*f*g) - cochainSign (K := K) (n-1) *
    supertrace Q E (f*F.differential*g) = cochainSign (K := K) n *
    (supertrace Q E (f*(F.differential*g)) - cochainSign (K := K) (-n) *
    supertrace Q E (f*(g*E.differential)))
  rw [cochainSign_neg, hn, Matrix.mul_assoc f F.differential g,
    Matrix.mul_assoc E.differential f g]
  have h1 : cochainSign (K := K) 1 = -1 := by
    simpa only [zero_add, cochainSign_zero] using cochainSign_add_one (K := K) 0
  rw [h1, neg_one_mul, Matrix.mul_assoc] at hcyc
  have hh : supertrace Q E (E.differential*(f*g)) = -supertrace Q E (f*(g*E.differential)) := by
    linear_combination hcyc
  rw [hh]
  linear_combination (supertrace Q E (f*(g*E.differential))) * hs

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_DiagonalVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V]

omit [Fintype A] in
lemma trace_tokenBasis (α : V) : trace Q (tokenBasis Q (K := K) α) = 1 := by
  change (∑ j, (Pi.single α (1 : K)) j) = 1
  simp

namespace BasedComplex
variable {I J : Type*} [Fintype I] [Fintype J]

variable [DecidableEq I]

lemma diagonalToken_entries (E : BasedComplex Q (K := K) I) (i : I) :
    ProjectiveEntries Q E.placement E.placement (diagonalToken Q E i) := by
  classical
  have hl : vertexId Q (K := K) (E.placement i).color * tokenBasis Q (E.placement i).color =
      tokenBasis Q (E.placement i).color := by
    simpa only [Path.source, pathBasis_token] using
      (pathBasis_left Q (K := K) (.inr (.inr (E.placement i).color)))
  have hr : tokenBasis Q (K := K) (E.placement i).color * vertexId Q (E.placement i).color =
      tokenBasis Q (E.placement i).color := by
    simpa only [Path.target, pathBasis_token] using
      (pathBasis_right Q (K := K) (.inr (.inr (E.placement i).color)))
  constructor <;> intro j k
  · by_cases hjk : j = k
    · subst k
      by_cases hji : j = i
      · subst j; simp only [diagonalToken, Matrix.diagonal_apply_eq, ite_true, if_true, hl]
      · simp only [diagonalToken, Matrix.diagonal_apply_eq, ite_eq_right hji, MulZeroClass.mul_zero]
    · simp only [diagonalToken, Matrix.diagonal_apply_ne _ hjk, MulZeroClass.mul_zero]
  · by_cases hjk : j = k
    · subst k
      by_cases hji : j = i
      · subst j; simp only [diagonalToken, Matrix.diagonal_apply_eq, ite_true, if_true, hr]
      · simp only [diagonalToken, Matrix.diagonal_apply_eq, ite_eq_right hji, MulZeroClass.zero_mul]
    · simp only [diagonalToken, Matrix.diagonal_apply_ne _ hjk, MulZeroClass.zero_mul]

omit [Fintype V] in
lemma diagonalToken_degree (E : BasedComplex Q (K := K) I) (i : I) :
    MapDegree Q E.placement E.placement 0 2 (diagonalToken Q E i) := by
  intro j k
  by_cases hjk : j = k
  · subst k
    constructor
    · intro h; exact (h (by omega)).elim
    · by_cases hji : j = i
      · subst j
        simp only [diagonalToken, Matrix.diagonal_apply_eq, ite_true, if_true]
        rw [add_sub_cancel_right]
        exact ⟨fun _ => rfl, fun _ => rfl, fun h => (h rfl).elim⟩
      · simp only [diagonalToken, Matrix.diagonal_apply_eq, ite_eq_right hji]
        exact homogeneous_zero Q _
  · have hz : diagonalToken Q E i j k = 0 := Matrix.diagonal_apply_ne _ hjk
    rw [hz]
    exact ⟨fun _ => rfl, homogeneous_zero Q _⟩

lemma diagonalToken_mem_homCycles (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (i : I) : diagonalToken Q E i ∈ homCycles Q E E 0 2 := by
  refine ⟨⟨diagonalToken_entries Q E i, diagonalToken_degree Q E i⟩, ?_⟩
  have hl : E.differential * diagonalToken Q E i = 0 := by
    apply Matrix.ext
    intro j k
    rw [diagonalToken, Matrix.mul_diagonal]
    by_cases hki : k = i
    · simp only [ite_eq_left hki, Matrix.zero_apply]
      exact positive_mul_tokenBasis Q _ _ (hE j k)
    · simp only [ite_eq_right hki, MulZeroClass.mul_zero, Matrix.zero_apply]
  have hr : diagonalToken Q E i * E.differential = 0 := by
    apply Matrix.ext
    intro j k
    rw [diagonalToken, Matrix.diagonal_mul]
    by_cases hji : j = i
    · simp only [ite_eq_left hji, Matrix.zero_apply]
      exact tokenBasis_mul_positive Q _ _ (hE j k)
    · simp only [ite_eq_right hji, MulZeroClass.zero_mul, Matrix.zero_apply]
  change E.differential * diagonalToken Q E i -
    cochainSign (K := K) 0 • (diagonalToken Q E i * E.differential) = 0
  rw [hl, hr, smul_zero, sub_zero]

lemma supertrace_diagonalToken (E : BasedComplex Q (K := K) I) (i : I) :
    supertrace Q E (diagonalToken Q E i) = cochainSign (K := K) (E.placement i).cochain := by
  change (∑ j, cochainSign (K := K) (E.placement j).cochain *
    trace Q (diagonalToken Q E i j j)) = _
  rw [Finset.sum_eq_single i]
  · simp only [diagonalToken, Matrix.diagonal_apply_eq, ite_true, if_true, trace_tokenBasis, _root_.mul_one]
  · intro j _ hji
    simp only [diagonalToken, Matrix.diagonal_apply_eq, ite_eq_right hji, trace_zero, MulZeroClass.mul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_LinearMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

namespace BasedComplex
lemma supertrace_linear (E : BasedComplex Q (K := K) I)
    {f : Matrix I I (Q.Zigzag K)} (hf : LinearMatrix Q f) : supertrace Q E f = 0 := by
  change (∑ i, cochainSign (K := K) (E.placement i).cochain * trace Q (f i i)) = 0
  apply Finset.sum_eq_zero
  intro i _
  have ht : trace Q (f i i) = 0 := by
    change (∑ α, (f i i).token α) = 0
    rw [(hf i i).2]
    simp only [Pi.zero_apply, Finset.sum_const_zero]
  rw [ht, MulZeroClass.mul_zero]

lemma cochainSign_ne_zero (n : ℤ) : cochainSign (K := K) n ≠ 0 := by
  intro h
  have hh := cochainSign_mul_self (K := K) n
  rw [h, MulZeroClass.zero_mul] at hh
  exact zero_ne_one hh

variable [DecidableEq I]

lemma linear_selfCycle_boundary_zero (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (i : I) (hd : homDimension Q E E 0 0 ≤ 1)
    {f : Matrix I I (Q.Zigzag K)} (hf : f ∈ homCycles Q E E 0 0)
    (hlin : LinearMatrix Q f) : f ∈ homBoundaries Q E E 0 0 := by
  apply boundary_of_homDimension_le_one Q E E 0 0 hd (diagonalVertex Q E i)
    (fun _ h => diagonalVertex_boundary Q E hE i 0 0 h) (identity_mem_homCycles Q E)
  · rw [diagonalVertex_identity]
    exact one_ne_zero
  · exact hf
  · exact congrFun (hlin i i).1 (E.placement i).color

lemma linear_selfCycle_boundary_two (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (i : I) (hd : homDimension Q E E 0 2 ≤ 1)
    {f : Matrix I I (Q.Zigzag K)} (hf : f ∈ homCycles Q E E 0 2)
    (hlin : LinearMatrix Q f) : f ∈ homBoundaries Q E E 0 2 := by
  apply boundary_of_homDimension_le_one Q E E 0 2 hd (supertrace Q E)
    (by rintro _ ⟨g, _, rfl⟩; exact supertrace_boundary Q E g)
    (diagonalToken_mem_homCycles Q E hE i)
  · rw [supertrace_diagonalToken]
    exact cochainSign_ne_zero _
  · exact hf
  · exact supertrace_linear Q E hlin

lemma linear_selfCycle_boundary (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q)
    (hcap : ∀ n v, homDimension Q E E n v ≤ 1)
    (hsupp : ∀ n v, n ≠ 0 ∨ (v ≠ 0 ∧ v ≠ 2) → homDimension Q E E n v = 0)
    (n v : ℤ) {f : Matrix I I (Q.Zigzag K)} (hf : f ∈ homCycles Q E E n v)
    (hlin : LinearMatrix Q f) : f ∈ homBoundaries Q E E n v := by
  by_cases hI : Nonempty I
  · let i : I := Classical.choice hI
    by_cases hn : n = 0
    · subst n
      by_cases hv₀ : v = 0
      · subst v
        exact linear_selfCycle_boundary_zero Q E hE i (hcap 0 0) hf hlin
      · by_cases hv₂ : v = 2
        · subst v
          exact linear_selfCycle_boundary_two Q E hE i (hcap 0 2) hf hlin
        · exact boundary_of_homDimension_zero Q E E 0 v
            (hsupp 0 v (Or.inr ⟨hv₀, hv₂⟩)) hf
    · exact boundary_of_homDimension_zero Q E E n v (hsupp n v (Or.inl hn)) hf
  · have hz : f = 0 := by
      apply Matrix.ext
      intro i _
      exact (hI ⟨i⟩).elim
    rw [hz]
    exact Submodule.zero_mem _

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomStep
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype V] [DecidableEq A] in
lemma homStep_range (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n m v : ℤ) (hm : m = n+1) :
    (LinearMap.range (homStep Q E F n m v hm)).map (homSpace Q E F m v).subtype =
      homBoundaries Q E F m v := by
  subst m
  ext f
  change (∃ g, (∃ h, homStep Q E F n (n+1) v rfl h = g) ∧ g.val = f) ↔ _
  constructor
  · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
    change ∃ g, g ∈ homSpace Q E F (n+1-1) v ∧
      homDifferential Q E F (n+1-1) g = homDifferential Q E F n h.val
    simpa only [add_sub_cancel_right] using
      (show ∃ g, g ∈ homSpace Q E F n v ∧ homDifferential Q E F n g =
        homDifferential Q E F n h.val from ⟨h.val, h.property, rfl⟩)
  · rintro ⟨g, hg, rfl⟩
    have hg' : g ∈ homSpace Q E F n v := by
      change g ∈ homSpace Q E F (n+1-1) v at hg
      rwa [add_sub_cancel_right] at hg
    refine ⟨homStep Q E F n (n+1) v rfl ⟨g, hg'⟩, ⟨⟨g, hg'⟩, rfl⟩, ?_⟩
    dsimp only [homStep, LinearMap.restrict_apply]
    simp only [add_sub_cancel_right]

omit [Fintype V] [DecidableEq A] in
lemma homStep_range_finrank (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n m v : ℤ) (hm : m = n+1) :
    Module.finrank K (LinearMap.range (homStep Q E F n m v hm)) =
      Module.finrank K (homBoundaries Q E F m v) := by
  rw [← homStep_range Q E F n m v hm, Submodule.finrank_map_subtype_eq]

omit [DecidableEq A] in

lemma hom_exact_dimension (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homDimension Q E F n v + Module.finrank K (homBoundaries Q E F n v) +
      Module.finrank K (homBoundaries Q E F (n+1) v) =
      Module.finrank K (homSpace Q E F n v) := by
  have hq := ((homBoundaries Q E F n v).comap (homCycles Q E F n v).subtype).finrank_quotient_add_finrank
  have hc := (Submodule.comapSubtypeEquivOfLe (homBoundaries_le_homCycles Q E F n v)).finrank_eq
  have hk := (homCycleKernelEquiv Q E F n (n+1) v rfl).finrank_eq
  have hr := homStep_range_finrank Q E F n (n+1) v rfl
  have he := (homStep Q E F n (n+1) v rfl).finrank_range_add_finrank_ker
  change homDimension Q E F n v + _ = _ at hq
  omega

lemma homStep_rank_dual (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n m v : ℤ) (hm : m = n+1) :
    Module.finrank K (homBoundaries Q E F m v) =
      Module.finrank K (homBoundaries Q F E (-n) (2-v)) := by
  have hneg : -n = -m+1 := by omega
  let d := homStep Q E F n m v hm
  let d' := homStep Q F E (-m) (-n) (2-v) hneg
  let e₀ := homSpaceDuality Q E F m v
  let e₁ := (homSpaceDuality Q E F n v).trans
    (LinearEquiv.smulOfNeZero K (Module.Dual K (homSpace Q E F n v))
      (cochainSign (K := K) m) (cochainSign_ne_zero m))
  have ha : e₁.toLinearMap.comp d' = d.dualMap.comp e₀.toLinearMap := by
    ext g f
    change cochainSign (K := K) m *
      supertrace Q E (f.val * homDifferential Q F E (-m) g.val) =
      supertrace Q E (homDifferential Q E F n f.val * g.val)
    have hh := homDifferential_adjoint Q E F m f.val g.val
    have he : m-1=n := by omega
    rw [he] at hh
    exact hh.symm
  have hr := congrArg (fun l : homSpace Q F E (-m) (2-v) →ₗ[K] Module.Dual K (homSpace Q E F n v) =>
    Module.finrank K (LinearMap.range l)) ha
  rw [LinearMap.range_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top] at hr
  rw [e₁.finrank_map_eq, LinearMap.finrank_range_dualMap_eq_finrank_range] at hr
  rw [homStep_range_finrank Q F E (-m) (-n) (2-v) hneg,
    homStep_range_finrank Q E F n m v hm] at hr
  exact hr.symm

lemma homDimension_dual (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homDimension Q E F n v = homDimension Q F E (-n) (2-v) := by
  have he := hom_exact_dimension Q E F n v
  have hf := hom_exact_dimension Q F E (-n) (2-v)
  have hs := homSpace_finrank_dual Q E F n v
  have h₁ := homStep_rank_dual Q E F (n-1) n v (by omega)
  have h₂ := homStep_rank_dual Q E F n (n+1) v rfl
  have hh : -(n-1) = -n+1 := by omega
  rw [hh] at h₁
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomInternalSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype V] [DecidableEq A] in
lemma homInternalSupport_dual (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (v : ℤ) :
    v ∈ homInternalSupport Q E F ↔ 2-v ∈ homInternalSupport Q F E := by
  rw [mem_homInternalSupport, mem_homInternalSupport]
  constructor
  · rintro ⟨i,j,r,h⟩
    refine ⟨j,i,r.rev, ?_⟩
    have hr := r.isLt
    simp only [Fin.val_rev]
    omega
  · rintro ⟨j,i,r,h⟩
    refine ⟨i,j,r.rev, ?_⟩
    have hr := r.isLt
    simp only [Fin.val_rev]
    omega

omit [Fintype V] [DecidableEq A] in
lemma homSpace_off_internal_support (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) (hv : v ∉ homInternalSupport Q E F) :
    homSpace Q E F n v = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply Matrix.ext
  intro i j
  by_contra hh
  have ha := homogeneous_nonzero_degree Q (hf.2 i j).2 hh
  rw [mem_homInternalSupport] at hv
  apply hv
  refine ⟨i,j,⟨(v + (E.placement i).internal - (F.placement j).internal).toNat, ?_⟩, ?_⟩
  · omega
  · simp only
    omega

omit [Fintype V] [DecidableEq A] in
lemma homDimension_off_internal_support (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) (hv : v ∉ homInternalSupport Q E F) :
    homDimension Q E F n v = 0 := by
  have hs := homSpace_off_internal_support Q E F n v hv
  have hz : homCycles Q E F n v = ⊥ := by
    change homSpace Q E F n v ⊓ _ = _
    rw [hs, bot_inf_eq]
  unfold homDimension
  have : Subsingleton (homCycles Q E F n v) := by rw [hz]; infer_instance
  have : Subsingleton (homCohomology Q E F n v) := inferInstance
  exact Module.finrank_zero_of_subsingleton

lemma totalHomDimension_dual (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (t : ℤ) :
    totalHomDimension Q E F t = totalHomDimension Q F E (2-t) := by
  classical
  unfold totalHomDimension
  refine Finset.sum_bij (fun v _ => 2-v) ?_ ?_ ?_ ?_
  · intro v hv
    exact (homInternalSupport_dual Q E F v).mp hv
  · intro a _ b _ h
    omega
  · intro b hb
    have hh := (homInternalSupport_dual Q F E b).mp hb
    exact ⟨2-b, hh, by omega⟩
  · intro v _
    rw [homDimension_dual Q E F (t-v) v]
    congr 1
    omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_PathZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

variable {I J L : Type*}

lemma matrixOne_eq_self {f : Matrix I J (Q.Zigzag K)} (hf : LinearMatrix Q f) :
    matrixOne Q f = f := by
  apply Matrix.ext
  intro i j
  exact pathOne_eq_self Q (hf i j).1 (hf i j).2

lemma matrixOne_mul [Fintype J] (f : Matrix I J (Q.Zigzag K))
    (g : Matrix J L (Q.Zigzag K)) :
    matrixOne Q (f * g) = matrixZero Q f * matrixOne Q g + matrixOne Q f * matrixZero Q g := by
  apply Matrix.ext
  intro i k
  change pathOne Q (∑ j, f i j * g j k) =
    (∑ j, pathZero Q (f i j) * pathOne Q (g j k)) +
    ∑ j, pathOne Q (f i j) * pathZero Q (g j k)
  rw [map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => pathOne_mul Q _ _

lemma matrixZero_entries {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q p q f) :
    ProjectiveEntries Q p q (matrixZero Q f) := by
  constructor
  · intro i j
    have h := congrArg (pathZero Q) (hf.1 i j)
    rw [pathZero_mul, pathZero_vertexId] at h
    exact h
  · intro i j
    have h := congrArg (pathZero Q) (hf.2 i j)
    rw [pathZero_mul, pathZero_vertexId] at h
    exact h

lemma matrixZero_degree {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {n v : ℤ} {f : Matrix I J (Q.Zigzag K)} (hf : MapDegree Q p q n v f) :
    MapDegree Q p q n v (matrixZero Q f) := by
  intro i j
  constructor
  · intro h
    change pathZero Q (f i j) = 0
    rw [(hf i j).1 h, map_zero]
  · exact ⟨(hf i j).2.1, fun _ => rfl, fun _ => rfl⟩

namespace BasedComplex
variable [Fintype I] [Fintype J]

lemma matrixOne_homDifferential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n : ℤ) (g : Matrix I J (Q.Zigzag K)) :
    matrixOne Q (homDifferential Q E F n g) =
      matrixOne Q E.differential * matrixZero Q g -
        cochainSign (K := K) n • (matrixZero Q g * matrixOne Q F.differential) := by
  change matrixOne Q (E.differential * g - cochainSign (K := K) n • (g * F.differential)) = _
  rw [map_sub, map_smul, matrixOne_mul, matrixOne_mul,
    matrixZero_eq_zero Q hE, matrixZero_eq_zero Q hF, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero]

lemma linear_boundary_primitive (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n v : ℤ) {f : Matrix I J (Q.Zigzag K)} (hlin : LinearMatrix Q f)
    (hf : f ∈ homBoundaries Q E F n v) :
    ∃ g ∈ homSpace Q E F (n - 1) v,
      (∀ i j, (g i j).arrow = 0 ∧ (g i j).token = 0) ∧
      matrixOne Q E.differential * g - cochainSign (K := K) (n - 1) •
        (g * matrixOne Q F.differential) = f := by
  obtain ⟨g, hg, rfl⟩ := hf
  refine ⟨matrixZero Q g, ⟨matrixZero_entries Q hg.1, matrixZero_degree Q hg.2⟩,
    fun _ _ => ⟨rfl, rfl⟩, ?_⟩
  rw [← matrixOne_homDifferential Q E F hE hF]
  exact matrixOne_eq_self Q hlin

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CoefficientSocle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype V] [DecidableEq A] in

lemma coefficient_cocycle_zero_of_socle_zero
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (n v : ℤ) (active : Set V)
    (hE : ∀ i, (E.placement i).color ∈ active)
    (hF : ∀ α ∈ active, ∀ c, coefficientSocle Q F α c = ⊥)
    {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homCycles Q E F n v)
    (hc : CoefficientMatrix Q f) : f = 0 := by
  classical
  by_contra hne
  let support : Finset I := Finset.univ.filter fun i => ∃ j, f i j ≠ 0
  have hs : support.Nonempty := by
    by_contra hh
    apply hne
    apply Matrix.ext
    intro i j
    by_contra hz
    exact hh ⟨i, by simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨j,hz⟩⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image support (fun i => (E.placement i).cochain) hs
  have hrow : ∀ j, (E.differential * f) i j = 0 := by
    intro j
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro t _
    by_cases ht : t ∈ support
    · have htdeg := hmax t ht
      have hz := (E.degree i t).1 (by omega)
      rw [hz, MulZeroClass.zero_mul]
    · have hz : f t j = 0 := by
        by_contra hh
        exact ht (by simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨j,hh⟩)
      rw [hz, MulZeroClass.mul_zero]
  have hout : ∀ j, (f * F.differential) i j = 0 := by
    intro j
    have hh := congrArg (fun m : Matrix I J (Q.Zigzag K) => m i j) hf.2
    change (E.differential*f) i j - cochainSign (K := K) n • (f*F.differential) i j = 0 at hh
    rw [hrow j, zero_sub, neg_eq_zero] at hh
    exact (smul_eq_zero.mp hh).resolve_left (cochainSign_ne_zero (K := K) n)
  let x : J → K := fun j => (f i j).vertex (E.placement i).color
  have hx : x ∈ coefficientSocle Q F (E.placement i).color ((E.placement i).cochain+n) := by
    constructor
    · intro j hj
      rcases hj with hj | hj
      · exact entry_vertex_right_support Q hf.1.1 i j _ (Ne.symm hj)
      · change (f i j).vertex _ = 0
        rw [(hf.1.2 i j).1 hj]
        rfl
    · intro j a ha
      have hh := congrArg (fun z : Q.Zigzag K => z.arrow a) (hout j)
      rw [Matrix.mul_apply, arrow_sum] at hh
      simp only [Finset.sum_apply, arrow_mul, Pi.add_apply, leftScale, rightScale,
        (hc i _).1, Pi.zero_apply, MulZeroClass.zero_mul, add_zero, ha] at hh
      exact hh
  have hxzero : x = 0 := by
    simpa only [hF _ (hE i) _, Submodule.mem_bot] using hx
  obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hi).2
  apply hj
  exact coefficient_row_zero Q hf.1.1 hc i (fun j => congrFun hxzero j) j

omit [Fintype V] [DecidableEq A] in
lemma pure_coefficient_homDimension_zero_of_socle_zero
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    {l k n v : ℤ} (hE : ∀ i, (E.placement i).level = l)
    (hF : ∀ j, (F.placement j).level = k) (h : n+v=k-l)
    (active : Set V) (hsE : ∀ i, (E.placement i).color ∈ active)
    (hsF : ∀ α ∈ active, ∀ c, coefficientSocle Q F α c = ⊥) :
    homDimension Q E F n v = 0 := by
  have hz : homCycles Q E F n v = ⊥ := by
    apply le_antisymm _ bot_le
    intro f hf
    exact coefficient_cocycle_zero_of_socle_zero Q E F n v active hsE hsF hf
      (pure_homSpace_coefficient Q E F hE hF h hf.1)
  unfold homDimension
  have : Subsingleton (homCycles Q E F n v) := by rw [hz]; infer_instance
  have : Subsingleton (homCohomology Q E F n v) := inferInstance
  exact Module.finrank_zero_of_subsingleton

omit [Fintype V] [DecidableEq A] in
lemma pure_total_coefficient_homDimension_zero_of_socle_zero
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    {l k : ℤ} (hE : ∀ i, (E.placement i).level = l)
    (hF : ∀ j, (F.placement j).level = k)
    (active : Set V) (hsE : ∀ i, (E.placement i).color ∈ active)
    (hsF : ∀ α ∈ active, ∀ c, coefficientSocle Q F α c = ⊥) :
    totalHomDimension Q E F (k-l) = 0 := by
  unfold totalHomDimension
  apply Finset.sum_eq_zero
  intro v _
  exact pure_coefficient_homDimension_zero_of_socle_zero Q E F hE hF (by omega)
    active hsE hsF

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_RestrictLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

namespace BasedComplex
variable {I J : Type*} [Fintype I] [Fintype J]

lemma restrictLayer_matrixOne_mul (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (l k : ℤ)
    (g : Matrix I J (Q.Zigzag K)) :
    restrictLayer Q E F l k (matrixOne Q E.differential * g) =
      (show Matrix {i // (E.placement i).level = l} {i // (E.placement i).level = l} (Q.Zigzag K) from (E.pureLayer Q hE l).differential) * restrictLayer Q E F l k g := by
  classical
  apply Matrix.ext
  intro i j
  change (∑ t, pathOne Q (E.differential i.val t) * g t j.val) =
    ∑ t : {i // (E.placement i).level = l}, E.differential i.val t.val * g t.val j.val
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro t ht
    have hh : (E.placement t).level ≠ (E.placement i.val).level := by
      intro he
      exact ht ⟨⟨t, he.trans i.property⟩, rfl⟩
    rw [pathOne_eq_zero Q (E.differential_arrow_level Q hh), MulZeroClass.zero_mul]
  · intro t
    exact congrArg (fun z : Q.Zigzag K => z * g t.val j.val)
      (pathOne_eq_self Q (E.pureLayer_linear Q hE l i t).1
        (E.pureLayer_linear Q hE l i t).2).symm

lemma restrictLayer_mul_matrixOne (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hF : F.IsMinimal Q) (l k : ℤ)
    (g : Matrix I J (Q.Zigzag K)) :
    restrictLayer Q E F l k (g * matrixOne Q F.differential) =
      restrictLayer Q E F l k g * (show Matrix {j // (F.placement j).level = k} {j // (F.placement j).level = k} (Q.Zigzag K) from (F.pureLayer Q hF k).differential) := by
  classical
  apply Matrix.ext
  intro i j
  change (∑ t, g i.val t * pathOne Q (F.differential t j.val)) =
    ∑ t : {j // (F.placement j).level = k}, g i.val t.val * F.differential t.val j.val
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro t ht
    have hh : (F.placement j.val).level ≠ (F.placement t).level := by
      intro he
      exact ht ⟨⟨t, he.symm.trans j.property⟩, rfl⟩
    rw [pathOne_eq_zero Q (F.differential_arrow_level Q hh), MulZeroClass.mul_zero]
  · intro t
    exact congrArg (fun z : Q.Zigzag K => g i.val t.val * z)
      (pathOne_eq_self Q (F.pureLayer_linear Q hF k t j).1
        (F.pureLayer_linear Q hF k t j).2).symm

lemma layer_boundary_of_extended_boundary (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (l k n v : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hlin : LinearMatrix Q f)
    (hf : extendLayer Q E F l k f ∈ homBoundaries Q E F n v) :
    f ∈ homBoundaries Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v := by
  obtain ⟨g, hg, _, he⟩ := linear_boundary_primitive Q E F hE hF n v
    (extendLayer_linear Q E F l k hlin) hf
  refine ⟨restrictLayer Q E F l k g, restrictLayer_homSpace Q E F hE hF l k (n-1) v hg, ?_⟩
  have h := congrArg (restrictLayer Q E F l k) he
  rw [map_sub, map_smul, restrictLayer_matrixOne_mul Q E F hE,
    restrictLayer_mul_matrixOne Q E F hF, restrictLayer_extend] at h
  exact h

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_DifferentialMulExtendLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma extendLayer_cycle (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (l k n v : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hf : f ∈ homCycles Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v)
    (hlin : LinearMatrix Q f) :
    extendLayer Q E F l k f ∈ homCycles Q E F n v := by
  refine ⟨extendLayer_homSpace Q E F hE hF l k n v hf.1, ?_⟩
  change homDifferential Q E F n (extendLayer Q E F l k f) = 0
  rw [homDifferential_extendLayer Q E F hE hF l k n hlin, hf.2, map_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_UnfoldedPresentation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

universe u

variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma unfoldedArtinAction_generator (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (α : V) :
    unfoldedArtinAction Q (K := K) hn M hM (generator M α) =
      classTwistPerm Q hn α := by
  exact PresentedGroup.toGroup.of _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomDimension2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma unfoldedArtinAction_homDimension (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M)
    (x : Artin M) (n v : ℤ) (E F : FiniteHomotopyClass Q (K := K)) :
    classHomDimension Q n v (unfoldedArtinAction Q hn M hM x E)
      (unfoldedArtinAction Q hn M hM x F) = classHomDimension Q n v E F := by
  let H : Subgroup (Artin M) := {
    carrier := {x | ∀ E F : FiniteHomotopyClass Q (K := K),
      classHomDimension Q n v (unfoldedArtinAction Q hn M hM x E)
        (unfoldedArtinAction Q hn M hM x F) = classHomDimension Q n v E F}
    one_mem' := by intro E F; simp only [map_one, Equiv.Perm.one_apply]
    mul_mem' := by
      intro x y hx hy E F
      rw [map_mul]
      change classHomDimension Q n v
        (unfoldedArtinAction Q hn M hM x (unfoldedArtinAction Q hn M hM y E))
        (unfoldedArtinAction Q hn M hM x (unfoldedArtinAction Q hn M hM y F)) = _
      rw [hx, hy]
    inv_mem' := by
      intro x hx E F
      have h := hx (unfoldedArtinAction Q hn M hM x⁻¹ E)
        (unfoldedArtinAction Q hn M hM x⁻¹ F)
      rw [map_inv] at h ⊢
      simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h.symm }
  have h := PresentedGroup.generated_by (braidRelators M) H (by
    intro α E F
    change classHomDimension Q n v
      (unfoldedArtinAction Q hn M hM (generator M α) E)
      (unfoldedArtinAction Q hn M hM (generator M α) F) = _
    rw [unfoldedArtinAction_generator]
    exact classPositiveTwist_homDimension Q hn α n v E F) x
  exact h E F

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InitialProjective
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma initial_homSpace_nonzero_cochain (α β : V) (n v : ℤ) (hn : n ≠ 0) :
    homSpace Q (initialProjective Q (K := K) α) (initialProjective Q β) n v = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply Matrix.ext
  intro i j
  apply (hf.2 i j).1
  change (0 : ℤ) ≠ 0 + n
  omega

omit [DecidableEq A] in
lemma initial_homSpace_orthogonal {α β : V} (h : OrthogonalVertices Q α β) (n v : ℤ) :
    homSpace Q (initialProjective Q (K := K) α) (initialProjective Q β) n v = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply Matrix.ext
  intro i j
  have he := sum_cornerPath Q (f i j) (hf.1.1 i j) (hf.1.2 i j)
  have hz : ∑ p : _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.CornerPath Q α β, pathCoordinates Q (f i j) p.val • pathBasis Q (K := K) p.val = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    exact (no_corner_of_orthogonal Q h p).elim
  exact he.symm.trans hz

lemma initial_homSpace_other_internal (hn : ∀ a, Q.source a ≠ Q.target a)
    (α : V) (n v : ℤ) (hv₀ : v ≠ 0) (hv₂ : v ≠ 2) :
    homSpace Q (initialProjective Q (K := K) α) (initialProjective Q α) n v = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply Matrix.ext
  intro i j
  rw [initial_self_entry_decomposition Q hn α n v hf i j]
  have hh := initial_self_entry_homogeneous Q α n v hf i j
  rw [hh.1 hv₀, hh.2.2 hv₂]
  simp only [Pi.zero_apply, zero_smul, add_zero, Matrix.zero_apply]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomDimensionZeroHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [DecidableEq A] in
lemma initial_homDimension_nonzero_cochain (α β : V) (n v : ℤ) (hn : n ≠ 0) :
    homDimension Q (initialProjective Q (K := K) α) (initialProjective Q β) n v = 0 :=
  homDimension_zero_of_homSpace_zero Q _ _ n v
    (initial_homSpace_nonzero_cochain Q α β n v hn)

omit [DecidableEq A] in
lemma initial_homDimension_orthogonal {α β : V} (h : OrthogonalVertices Q α β) (n v : ℤ) :
    homDimension Q (initialProjective Q (K := K) α) (initialProjective Q β) n v = 0 :=
  homDimension_zero_of_homSpace_zero Q _ _ n v (initial_homSpace_orthogonal Q h n v)

lemma initial_homDimension_other_internal (hn : ∀ a, Q.source a ≠ Q.target a)
    (α : V) (n v : ℤ) (hv₀ : v ≠ 0) (hv₂ : v ≠ 2) :
    homDimension Q (initialProjective Q (K := K) α) (initialProjective Q α) n v = 0 :=
  homDimension_zero_of_homSpace_zero Q _ _ n v
    (initial_homSpace_other_internal Q hn α n v hv₀ hv₂)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_Initial
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma unfoldedFrame_homDimension (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M)
    (α β : V) (n v : ℤ) :
    classHomDimension Q n v (unfoldedFrame Q (K := K) hn M hM x α)
      (unfoldedFrame Q hn M hM x β) =
    homDimension Q (initialProjective Q α : BasedComplex Q (K := K) PUnit.{u+1})
      (initialProjective Q β : BasedComplex Q (K := K) PUnit.{u+1}) n v :=
  unfoldedArtinAction_homDimension Q hn M hM x n v (initialClass Q α) (initialClass Q β)

lemma unfoldedFrame_self_bound (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M)
    (α : V) (n v : ℤ) :
    classHomDimension Q n v (unfoldedFrame Q (K := K) hn M hM x α)
      (unfoldedFrame Q hn M hM x α) ≤ 1 := by
  rw [unfoldedFrame_homDimension]
  exact initial_homDimension_le_one Q hn α n v

lemma unfoldedFrame_self_support (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M)
    (α : V) (n v : ℤ) (h : n ≠ 0 ∨ (v ≠ 0 ∧ v ≠ 2)) :
    classHomDimension Q n v (unfoldedFrame Q (K := K) hn M hM x α)
      (unfoldedFrame Q hn M hM x α) = 0 := by
  rw [unfoldedFrame_homDimension]
  rcases h with hn' | ⟨h₀, h₂⟩
  · exact initial_homDimension_nonzero_cochain Q α α n v hn'
  · exact initial_homDimension_other_internal Q hn α n v h₀ h₂

lemma unfoldedFrame_orthogonal (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M)
    {α β : V} (h : OrthogonalVertices Q α β) (n v : ℤ) :
    classHomDimension Q n v (unfoldedFrame Q (K := K) hn M hM x α)
      (unfoldedFrame Q hn M hM x β) = 0 := by
  rw [unfoldedFrame_homDimension]
  exact initial_homDimension_orthogonal Q h n v

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_MinimalModel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma frameModel_linear_cycle_boundary (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M) (α : V)
    (n v : ℤ) {f : Matrix (frameModel Q (K := K) hn M hM x α).Index
      (frameModel Q (K := K) hn M hM x α).Index (Q.Zigzag K)}
    (hf : f ∈ homCycles Q (frameModel Q hn M hM x α).complex
      (frameModel Q hn M hM x α).complex n v) (hlin : LinearMatrix Q f) :
    f ∈ homBoundaries Q (frameModel Q hn M hM x α).complex
      (frameModel Q hn M hM x α).complex n v := by
  apply linear_selfCycle_boundary Q _ (frameModel_minimal Q hn M hM x α) _ _ n v hf hlin
  · intro n v
    rw [frameModel, minimalClassModel_homDimension]
    exact unfoldedFrame_self_bound Q hn M hM x α n v
  · intro n v h
    rw [frameModel, minimalClassModel_homDimension]
    exact unfoldedFrame_self_support Q hn M hM x α n v h

lemma frameModel_orthogonal_cycle_boundary (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M)
    {α β : V} (h : OrthogonalVertices Q α β)
    (n v : ℤ) {f : Matrix (frameModel Q (K := K) hn M hM x α).Index
      (frameModel Q (K := K) hn M hM x β).Index (Q.Zigzag K)}
    (hf : f ∈ homCycles Q (frameModel Q hn M hM x α).complex
      (frameModel Q hn M hM x β).complex n v) :
    f ∈ homBoundaries Q (frameModel Q hn M hM x α).complex
      (frameModel Q hn M hM x β).complex n v := by
  apply boundary_of_homDimension_zero Q _ _ n v _ hf
  exact (minimalClassModel_homDimension Q (unfoldedFrame Q (K := K) hn M hM x α)
    (unfoldedFrame Q hn M hM x β) n v).trans
    (unfoldedFrame_orthogonal Q (K := K) hn M hM x h n v)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomPath
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma homSpace_finrank (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    Module.finrank K (homSpace Q E F n v) = Nat.card (HomPath Q E F n v) := by
  classical
  rw [(homCoordinatesEquiv Q E F n v).finrank_eq, Module.finrank_pi, Nat.card_eq_fintype_card]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CornerPath
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma totalChainDimension_eq_card (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) (r : ℤ) :
    totalChainDimension Q E F (k-l+r) = Nat.card (CornerPath Q E F r) := by
  classical
  unfold totalChainDimension
  simp_rw [homSpace_finrank, Nat.card_eq_fintype_card]
  rw [← Finset.sum_coe_sort, ← Fintype.card_sigma]
  exact Fintype.card_congr (purePathEquiv Q E F hE hF r)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InverseWordAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma inverse_positiveWord (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :
    inverseWordAction Q w (positiveWordAction Q w x)=x := by
  induction w generalizing x with
  | nil => rfl
  | cons α w ih =>
    change inverseWordAction Q w ((classTwistPerm Q hn α).symm
      ((classTwistPerm Q hn α) (positiveWordAction Q w x)))=x
    rw [Equiv.symm_apply_apply,ih]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_FrameModelLayerMiddle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma frameModel_layer_middle_vanishing (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M) (α : V)
    (l k n v : ℤ)
    {f : Matrix {i // ((frameModel Q (K := K) hn M hM x α).complex.placement i).level = l}
      {j // ((frameModel Q (K := K) hn M hM x α).complex.placement j).level = k} (Q.Zigzag K)}
    (hf : f ∈ homCycles Q
      ((frameModel Q hn M hM x α).complex.pureLayer Q (frameModel_minimal Q hn M hM x α) l)
      ((frameModel Q hn M hM x α).complex.pureLayer Q (frameModel_minimal Q hn M hM x α) k) n v)
    (hlin : LinearMatrix Q f) :
    f ∈ homBoundaries Q
      ((frameModel Q hn M hM x α).complex.pureLayer Q (frameModel_minimal Q hn M hM x α) l)
      ((frameModel Q hn M hM x α).complex.pureLayer Q (frameModel_minimal Q hn M hM x α) k) n v := by
  apply layer_boundary_of_extended_boundary Q _ _
    (frameModel_minimal Q hn M hM x α) (frameModel_minimal Q hn M hM x α) l k n v hlin
  apply frameModel_linear_cycle_boundary Q hn M hM x α n v
  · exact extendLayer_cycle Q _ _ (frameModel_minimal Q hn M hM x α)
      (frameModel_minimal Q hn M hM x α) l k n v hf hlin
  · exact extendLayer_linear Q _ _ l k hlin

lemma frameModel_orthogonal_layer_middle_vanishing (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M)
    {α β : V} (h : OrthogonalVertices Q α β) (l k n v : ℤ)
    {f : Matrix {i // ((frameModel Q (K := K) hn M hM x α).complex.placement i).level = l}
      {j // ((frameModel Q (K := K) hn M hM x β).complex.placement j).level = k} (Q.Zigzag K)}
    (hf : f ∈ homCycles Q
      ((frameModel Q hn M hM x α).complex.pureLayer Q (frameModel_minimal Q hn M hM x α) l)
      ((frameModel Q hn M hM x β).complex.pureLayer Q (frameModel_minimal Q hn M hM x β) k) n v)
    (hlin : LinearMatrix Q f) :
    f ∈ homBoundaries Q
      ((frameModel Q hn M hM x α).complex.pureLayer Q (frameModel_minimal Q hn M hM x α) l)
      ((frameModel Q hn M hM x β).complex.pureLayer Q (frameModel_minimal Q hn M hM x β) k) n v := by
  apply layer_boundary_of_extended_boundary Q _ _
    (frameModel_minimal Q hn M hM x α) (frameModel_minimal Q hn M hM x β) l k n v hlin
  apply frameModel_orthogonal_cycle_boundary Q hn M hM x h n v
  exact extendLayer_cycle Q _ _ (frameModel_minimal Q hn M hM x α)
    (frameModel_minimal Q hn M hM x β) l k n v hf hlin

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PureUpperBoundariesZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype V] [DecidableEq A] in
lemma pure_upper_boundaries_zero (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (h : k-l+2 < n+v) : homBoundaries Q E F n v = ⊥ := by
  have hb : homBoundaries Q E F n v ≤ homSpace Q E F n v :=
    (homBoundaries_le_homCycles Q E F n v).trans inf_le_left
  rw [homSpace_pure_total_degree_upper Q E F hE hF h] at hb
  exact le_antisymm hb bot_le

lemma pure_hom_euler (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (h : n+v=k-l) :
    Module.finrank K (homSpace Q E F n v) + Module.finrank K (homSpace Q E F (n+2) v) +
      homDimension Q E F (n+1) v =
    Module.finrank K (homSpace Q E F (n+1) v) + homDimension Q E F n v +
      homDimension Q F E (-(n+2)) (2-v) := by
  have h₀ := hom_exact_dimension Q E F n v
  have h₁ := hom_exact_dimension Q E F (n+1) v
  have h₂ := hom_exact_dimension Q E F (n+2) v
  rw [pure_coefficient_boundaries_zero Q E F hE hF h, finrank_bot] at h₀
  rw [pure_upper_boundaries_zero Q E F hE hF (n := n+2+1) (v := v) (by omega),
    finrank_bot] at h₂
  rw [homDimension_dual Q E F (n+2) v] at h₂
  have hn : n+1+1=n+2 := by omega
  rw [hn] at h₁
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PureTotalHomEuler
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma pure_total_hom_euler (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) :
    totalChainDimension Q E F (k-l) + totalChainDimension Q E F (k-l+2) +
      totalHomDimension Q E F (k-l+1) =
    totalChainDimension Q E F (k-l+1) + totalHomDimension Q E F (k-l) +
      totalHomDimension Q F E (l-k) := by
  have hp (v : ℤ) := pure_hom_euler Q E F hE hF (n := k-l-v) (v := v) (by omega)
  have he (v : ℤ) :
      Module.finrank K (homSpace Q E F (k-l-v) v) +
        Module.finrank K (homSpace Q E F (k-l+2-v) v) + homDimension Q E F (k-l+1-v) v =
      Module.finrank K (homSpace Q E F (k-l+1-v) v) +
        homDimension Q E F (k-l-v) v + homDimension Q E F (k-l+2-v) v := by
    have hh := hp v
    rw [← homDimension_dual Q E F (k-l-v+2) v] at hh
    have h₁ : k-l-v+1=k-l+1-v := by omega
    have h₂ : k-l-v+2=k-l+2-v := by omega
    rw [h₁,h₂] at hh
    exact hh
  have hs := Finset.sum_congr (s₁ := homInternalSupport Q E F) (s₂ := homInternalSupport Q E F)
    rfl (fun v _ => he v)
  simp only [Finset.sum_add_distrib] at hs
  change totalChainDimension Q E F (k-l) + totalChainDimension Q E F (k-l+2) +
    totalHomDimension Q E F (k-l+1) = totalChainDimension Q E F (k-l+1) +
    totalHomDimension Q E F (k-l) + totalHomDimension Q E F (k-l+2) at hs
  rw [totalHomDimension_dual Q E F (k-l+2)] at hs
  have h : 2-(k-l+2)=l-k := by omega
  rw [h] at hs
  exact hs

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_EqualColorPair
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma pure_generator_euler (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) :
    2 * Nat.card (EqualColorPair Q E F) + totalHomDimension Q E F (k-l+1) =
      Nat.card (ArrowPair Q E F) + totalHomDimension Q E F (k-l) +
        totalHomDimension Q F E (l-k) := by
  have hh := pure_total_hom_euler Q E F hE hF
  have h₀ := totalChainDimension_eq_card Q E F hE hF 0
  have h₁ := totalChainDimension_eq_card Q E F hE hF 1
  have h₂ := totalChainDimension_eq_card Q E F hE hF 2
  rw [Nat.card_congr (zeroCornerEquiv Q E F)] at h₀
  rw [Nat.card_congr (arrowCornerEquiv Q E F)] at h₁
  rw [Nat.card_congr (tokenCornerEquiv Q E F)] at h₂
  simp only [add_zero] at h₀
  rw [h₀,h₁,h₂] at hh
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_GeneratorVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

omit [DecidableEq A] in
lemma sum_generatorVector (E : BasedComplex Q (K := K) I) (f : V → ℝ) :
    ∑ α, generatorVector Q E α * f α = ∑ i, f (E.placement i).color := by
  classical
  simp only [generatorVector_sum, Finset.sum_mul, ite_mul, _root_.one_mul, MulZeroClass.zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]

omit [Fintype V] [DecidableEq A] in
lemma equalColorPair_card (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) :
    (Nat.card (EqualColorPair Q E F) : ℝ) =
      ∑ i, ∑ j, if (E.placement i).color = (F.placement j).color then (1 : ℝ) else 0 := by
  classical
  simp only [EqualColorPair, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← Finset.sum_boole,
    Fintype.sum_prod_type]

omit [Fintype V] [DecidableEq A] in
lemma arrowPair_card (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) :
    (Nat.card (ArrowPair Q E F) : ℝ) =
      ∑ i, ∑ j, (Nat.card {a : A // Q.source a = (E.placement i).color ∧
        Q.target a = (F.placement j).color} : ℝ) := by
  classical
  simp only [ArrowPair, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← Finset.sum_boole,
    Fintype.sum_prod_type]

omit [DecidableEq A] in
lemma generator_cartan_pairing (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) :
    (generatorVector Q E) ⬝ᵥ ((unfoldedCartan Q).mulVec (generatorVector Q F)) =
      2 * (Nat.card (EqualColorPair Q E F) : ℝ) - Nat.card (ArrowPair Q E F) := by
  classical
  rw [dotProduct, sum_generatorVector]
  simp only [Matrix.mulVec, dotProduct]
  have hs (i : I) :
      ∑ α, unfoldedCartan Q (E.placement i).color α * generatorVector Q F α =
        ∑ j, unfoldedCartan Q (E.placement i).color (F.placement j).color := by
    simpa only [_root_.mul_comm] using
      sum_generatorVector Q F (fun α => unfoldedCartan Q (E.placement i).color α)
  simp_rw [hs, unfoldedCartan]
  rw [equalColorPair_card, arrowPair_card]
  simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> norm_num

lemma pure_cartan_euler (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) :
    (generatorVector Q E) ⬝ᵥ ((unfoldedCartan Q).mulVec (generatorVector Q F)) =
      (totalHomDimension Q E F (k-l) : ℝ) - totalHomDimension Q E F (k-l+1) +
        totalHomDimension Q F E (l-k) := by
  rw [generator_cartan_pairing]
  have hh := pure_generator_euler Q E F hE hF
  have hh' : (2 : ℝ) * Nat.card (EqualColorPair Q E F) + totalHomDimension Q E F (k-l+1) =
      Nat.card (ArrowPair Q E F) + totalHomDimension Q E F (k-l) +
        totalHomDimension Q F E (l-k) := by exact_mod_cast hh
  linarith

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomDimensionZeroCycles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma frameModel_pure_middle_dimension (hn : ∀ a, Q.source a ≠ Q.target a)
    (C : CoxeterMatrix V) (hC : UnfoldedPresentation Q C) (x : Artin C) (α : V)
    (l k : ℤ) :
    totalHomDimension Q
      ((frameModel Q (K := K) hn C hC x α).complex.pureLayer Q (frameModel_minimal Q hn C hC x α) l)
      ((frameModel Q (K := K) hn C hC x α).complex.pureLayer Q (frameModel_minimal Q hn C hC x α) k)
      (k-l+1) = 0 := by
  unfold totalHomDimension
  apply Finset.sum_eq_zero
  intro v _
  apply homDimension_zero_of_cycles_boundary Q
  intro f hf
  apply frameModel_layer_middle_vanishing Q hn C hC x α l k _ v hf
  exact pure_homSpace_linear Q _ _ (fun i => i.property) (fun j => j.property) (by omega) hf.1

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_DownClosed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma lowerTruncation_minimal (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (d:ℤ) :
    (lowerTruncation Q E hE d).IsMinimal Q := fun i j=>hE i j

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionFold
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix
open scoped _root_.Matrix BigOperators

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ)

lemma fusion_pairing (hm : ∀ e, 2 ≤ m e) (d : V → V → FusionEdge E) (p q : V → ℝ) :
    fusionFold m p ⬝ᵥ (fusionUnfoldedCartan m d *ᵥ fusionFold m q) =
      fusionD0 m * (p ⬝ᵥ (fusionFoldedCartan m d *ᵥ q)) := by
  rw [fusion_intertwining m hm]
  simp only [dotProduct, Fintype.sum_prod_type, fusionFold, fusionD0, Finset.mul_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro L _
  ring

omit [Fintype V] [DecidableEq V] in
lemma fusionD0_pos (hm : ∀ e, 2 ≤ m e) : 0 < fusionD0 m := by
  let L : FusionLabel m := fun e => ⟨0, by have := hm e; omega⟩
  apply Finset.sum_pos'
  · intro L _; exact sq_nonneg _
  · exact ⟨L, Finset.mem_univ L, sq_pos_of_pos (fusionWeight_pos m hm L)⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CochainSignSubOne
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open _root_.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma cochainSign_sub_one (n : ℤ) : cochainSign (K:=ℝ) (n-1)= -cochainSign n := by
  have h:=cochainSign_add_one (K:=ℝ) (n-1)
  rw [sub_add_cancel] at h
  linarith

lemma cochainSign_sub_two (n : ℤ) : cochainSign (K:=ℝ) (n-2)=cochainSign n := by
  rw [show n-2=(n-1)-1 by omega,cochainSign_sub_one,cochainSign_sub_one,neg_neg]

omit [DecidableEq A] in
lemma signedCorner_sum (α β : V) :
    (∑ p : Zigzag.CornerPath Q α β, cochainSign (K:=ℝ) (Path.length p.val))=
      unfoldedCartan Q α β := by
  have hs := Finset.sum_subtype (p:=fun p : Path V A => Path.source Q p=α ∧ Path.target Q p=β) (F:=inferInstance)
    ((Finset.univ : Finset (Path V A)).filter (fun p => Path.source Q p=α ∧ Path.target Q p=β))
    (by intro p; simp) (fun p => cochainSign (K:=ℝ) (Path.length p))
  rw [← hs,Finset.sum_filter]
  simp only [Fintype.sum_sum_type,Path.source,Path.target,Path.length]
  simp [cochainSign,unfoldedCartan,Nat.card_eq_fintype_card,Fintype.card_subtype,
    ← Finset.sum_boole,eq_comm]
  have hv : (∑ x : V, if α=x ∧ β=x then (1:ℝ) else 0)=if α=β then 1 else 0 := by
    simp [ite_and, eq_comm]
  have ha : (∑ x : A, if α=Q.source x ∧ β=Q.target x then (-1:ℝ) else 0)=
      -(∑ x : A, if α=Q.source x ∧ β=Q.target x then (1:ℝ) else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> ring
  rw [hv,ha]
  split_ifs <;> ring

omit [DecidableEq A] in
lemma signedGeneratorVector_mulVec {I : Type u} [Fintype I]
    (E : BasedComplex Q (K:=K) I) (α : V) :
    (unfoldedCartan Q *ᵥ signedGeneratorVector Q E) α=
      ∑ i, cochainSign (K:=ℝ) (E.placement i).level * unfoldedCartan Q α (E.placement i).color := by
  simp only [Matrix.mulVec,dotProduct,signedGeneratorVector,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [placementSignedWeight,mul_comm]

lemma signedGeneratorVector_test {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K:=K) I) (α β : V) :
    signedGeneratorVector Q (E.testComplex Q α) β=
      if α=β then (unfoldedCartan Q *ᵥ signedGeneratorVector Q E) α else 0 := by
  by_cases h : α=β
  · subst β
    rw [ite_eq_left rfl,signedGeneratorVector_mulVec]
    change (∑ t : TestIndex Q E.placement α,
      if α=α then cochainSign (K:=ℝ) ((E.placement t.1).cochain+
        ((E.placement t.1).internal+Path.length t.2.val)) else 0)=_
    simp only [ite_true, if_true,Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    have hlev (p : Zigzag.CornerPath Q α (E.placement i).color) :
        (E.placement i).cochain+((E.placement i).internal+Path.length p.val)=
          (E.placement i).level+Path.length p.val := by
      simp only [GeneratorPlacement.level] <;> ring
    simp_rw [hlev,cochainSign_add]
    rw [← Finset.mul_sum,signedCorner_sum]

  · simp [signedGeneratorVector,placementSignedWeight,testComplex,testPlacement,h]

omit [Fintype V] in
lemma placementSignedWeight_raise (a : GeneratorPlacement V) (v : V) :
    placementSignedWeight ⟨a.color,a.cochain+1,a.internal⟩ v= -placementSignedWeight a v := by
  have hh : a.cochain+1+a.internal=a.level+1 := by dsimp [GeneratorPlacement.level]; omega
  simp only [placementSignedWeight,GeneratorPlacement.level,hh,cochainSign_add_one]
  split_ifs <;> simp

omit [DecidableEq A] [Fintype V] in
lemma Map.signedGeneratorVector_cocone {I J : Type u} [Fintype I] [Fintype J]
    {E : BasedComplex Q (K:=K) I} {F : BasedComplex Q (K:=K) J} (f : Map Q E F) :
    signedGeneratorVector Q (f.cocone Q)=signedGeneratorVector Q E-signedGeneratorVector Q F := by
  funext v
  simp only [signedGeneratorVector,Map.cocone,Map.coconePlacement,Fintype.sum_sum_type,
    placementSignedWeight_raise,Finset.sum_neg_distrib,Pi.sub_apply]
  ring

lemma signedGeneratorVector_cotest {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K:=K) I) (α : V) :
    signedGeneratorVector Q (E.cotestComplex Q α)=signedGeneratorVector Q (E.testComplex Q α) := by
  funext β
  apply Finset.sum_congr rfl
  intro t _
  change (if α=β then cochainSign (K:=ℝ) ((E.placement t.1).cochain+
    ((E.placement t.1).internal+Path.length t.2.val-2)) else 0)=
    (if α=β then cochainSign (K:=ℝ) ((E.placement t.1).cochain+
    ((E.placement t.1).internal+Path.length t.2.val)) else 0)
  rw [← add_sub_assoc,cochainSign_sub_two]

theorem signedGeneratorVector_negativeTwist {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K:=K) I) (α : V) :
    signedGeneratorVector Q (E.negativeTwist Q α)=rowReflect (unfoldedCartan Q) α
      (signedGeneratorVector Q E) := by
  unfold negativeTwist
  rw [Map.signedGeneratorVector_cocone,signedGeneratorVector_cotest]
  funext β
  simp only [Pi.sub_apply,signedGeneratorVector_test,rowReflect,Pi.smul_apply,smul_eq_mul,
    Pi.single_apply]
  by_cases h : α=β
  · subst β; simp
  · simp [h,Ne.symm h]

lemma classSignedVector_negativeTwist (x : FiniteHomotopyClass Q (K:=K)) (α : V) :
    classSignedVector Q (classNegativeTwist Q α x)=
      rowReflect (unfoldedCartan Q) α (classSignedVector Q x) := by
  induction x using Quotient.inductionOn with | _ E =>
    exact signedGeneratorVector_negativeTwist Q E.complex α

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TotalVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open _root_.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma signedGeneratorVector_upper_partition {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K:=K) I) (hE : E.IsMinimal Q)
    (q : ℤ) (hhi : ∀ i,(E.placement i).level≤q) :
    signedGeneratorVector Q E=signedGeneratorVector Q (lowerTruncation Q E hE (q-1))+
      signedGeneratorVector Q (E.pureLayer Q hE q) := by
  funext v
  simp only [signedGeneratorVector, lowerTruncation, lowRestriction, pureLayer, restrict, Pi.add_apply]
  have hlo : (∑ i : ↑(lowerLevelSet Q E (q-1)),placementSignedWeight (E.placement i) v)=
      ∑ i ∈ Finset.univ.filter (fun i : I=>(E.placement i).level≤q-1),
        placementSignedWeight (E.placement i) v := by
    symm
    apply Finset.sum_subtype
    intro i
    simp [lowerLevelSet]
  have hh : (∑ i : ↑{i : I | (E.placement i).level=q},placementSignedWeight (E.placement i) v)=
      ∑ i ∈ Finset.univ.filter (fun i : I=>(E.placement i).level=q),
        placementSignedWeight (E.placement i) v := by
    symm
    apply Finset.sum_subtype
    intro i
    simp
  rw [hlo,hh]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi:=hhi i
  by_cases he:(E.placement i).level≤q-1
  · have hn:(E.placement i).level≠q := by omega
    simp [he,hn]
  · have hn:(E.placement i).level=q := by omega
    simp [hn]

omit [Fintype V] [DecidableEq A] in
lemma classSignedVector_upper_partition (x : FiniteHomotopyClass Q (K:=K)) (q : ℤ)
    (hhi : ClassUpperBound Q q x) :
    classSignedVector Q x=classSignedVector Q (classLowerTruncation Q (q-1) x)+
      classSignedVector Q (classLayer Q q x) := by
  rw [classSignedVector_minimal Q x]
  exact signedGeneratorVector_upper_partition Q _ (minimalClassModel_minimal Q x) q hhi

lemma rowReflect_sub (C : Matrix V V ℝ) (α : V) (x y : V → ℝ) :
    rowReflect C α (x-y)=rowReflect C α x-rowReflect C α y := by
  simp only [rowReflect,Matrix.mulVec_sub,Pi.sub_apply,sub_smul]
  module

lemma rowReflect_smul (C : Matrix V V ℝ) (α : V) (a : ℝ) (x : V → ℝ) :
    rowReflect C α (a • x)=a • rowReflect C α x := by
  simp only [rowReflect,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul,smul_sub,smul_smul]

lemma rowReflectWord_sub (C : Matrix V V ℝ) (w : List V) (x y : V → ℝ) :
    rowReflectWord C w (x-y)=rowReflectWord C w x-rowReflectWord C w y := by
  induction w with
  | nil => rfl
  | cons α w ih =>
    change rowReflect C α (rowReflectWord C w (x-y))=_
    rw [ih,rowReflect_sub]
    rfl

lemma rowReflectWord_smul (C : Matrix V V ℝ) (w : List V) (a : ℝ) (x : V → ℝ) :
    rowReflectWord C w (a • x)=a • rowReflectWord C w x := by
  induction w with
  | nil => rfl
  | cons α w ih =>
    change rowReflect C α (rowReflectWord C w (a • x))=_
    rw [ih,rowReflect_smul]
    rfl

lemma classSignedVector_inverseWord (w : List V) (x : FiniteHomotopyClass Q (K:=K)) :
    classSignedVector Q (inverseWordAction Q w x)=
      rowReflectWord (unfoldedCartan Q) w.reverse (classSignedVector Q x) := by
  induction w generalizing x with
  | nil => rfl
  | cons α w ih =>
    change classSignedVector Q (inverseWordAction Q w (classNegativeTwist Q α x))=_
    rw [ih,classSignedVector_negativeTwist,List.reverse_cons,rowReflectWord_append]
    rfl

theorem canonicalLow_reflected_high_signed (hn : ∀ a,Q.source a≠Q.target a)
    (w : List V) (q : ℤ) (x : FiniteHomotopyClass Q (K:=K))
    (hhi : ClassUpperBound Q q x) :
    classSignedVector Q (classLayer Q q (inverseWordAction Q w x))=
      rowReflectWord (unfoldedCartan Q) w.reverse
        (classSignedVector Q x-classSignedVector Q (canonicalWordLow Q w q x)) := by
  have h:=classSignedVector_upper_partition Q (inverseWordAction Q w x) q
    (inverseWord_upper_bound Q w x hhi)
  have hl : classLowerTruncation Q (q-1) (inverseWordAction Q w x)=
      inverseWordAction Q w (canonicalWordLow Q w q x) :=
    (inverse_positiveWord Q hn w _).symm
  rw [hl,classSignedVector_inverseWord,classSignedVector_inverseWord] at h
  rw [rowReflectWord_sub]
  exact (eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact h.symm))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CanonicalLowReflectedHigh
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

theorem canonicalLow_reflected_high (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K))
    (hlo:ClassLowerBound Q q x) (hhi:ClassUpperBound Q q x)
    (hl:ClassLowerBound Q q (canonicalWordLow Q w q x))
    (hh:ClassUpperBound Q q (canonicalWordLow Q w q x)) :
    classTotalVector Q (classLayer Q q (inverseWordAction Q w x))=
      rowReflectWord (unfoldedCartan Q) w.reverse
        (classTotalVector Q x-classTotalVector Q (canonicalWordLow Q w q x)) := by
  have h:=canonicalLow_reflected_high_signed Q hn w q x hhi
  have lower : ClassLowerBound Q q (classLayer Q q (inverseWordAction Q w x)) :=
    classLowerBound_of_representative Q _ (fun index => le_of_eq index.property.symm)
  have upper : ClassUpperBound Q q (classLayer Q q (inverseWordAction Q w x)) :=
    classUpperBound_of_representative Q _ (fun index => le_of_eq index.property)
  rw [classSignedVector_pure Q _ q lower upper,
    classSignedVector_pure Q x q hlo hhi,classSignedVector_pure Q _ q hl hh,
    ← smul_sub,rowReflectWord_smul] at h
  have h':=congrArg (fun z:V→ℝ=>cochainSign (K:=ℝ) q • z) h
  simpa only [smul_smul,cochainSign_mul_self,one_smul] using h'

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ColorBoundary
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma colorRestriction_generatorVector (E:BasedComplex Q (K:=K) I) {q:ℤ} (U:Set V)
    (hp:∀ i,(E.placement i).level=q)
    (hb:∀ i,(E.placement i).color∉colorBoundary Q U) (v:V) :
    generatorVector Q (colorRestriction Q E U hp hb) v=
      if v∈U then generatorVector Q E v else 0 := by
  rw [generatorVector_sum]
  change (∑ i:{i // (E.placement i).color∈U},
    if (E.placement i).color=v then (1:ℝ) else 0)=_
  rw [← Finset.sum_subtype (Finset.univ.filter fun i:I=>(E.placement i).color∈U)
    (by simp) (fun i:I=>if (E.placement i).color=v then (1:ℝ) else 0),
    Finset.sum_filter]
  split_ifs with hv
  · rw [generatorVector_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases he:(E.placement i).color=v
    · simp only [he,hv,ite_true, if_true]
    · simp only [he,ite_false, if_false,ite_self]
  · apply Finset.sum_eq_zero
    intro i _
    by_cases he:(E.placement i).color=v
    · simp only [he,hv,ite_false, if_false]
    · simp only [he,ite_false, if_false,ite_self]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HighConeIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] in
lemma highRestriction_top_eq_layer (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (hhi:∀ i,(E.placement i).level≤q) :
    classOfComplex Q (upperTruncation Q E hE (q-1))=
      classLayer Q q (classOfComplex Q E) := by
  have he:(upperTruncation Q E hE (q-1)).reindex Q (highPureIndex Q E q hhi)=
      E.pureLayer Q hE q := by
    apply ext_placement_differential Q <;> rfl
  rw [classLayer_minimal]
  exact (classOfComplex_reindex Q _ (highPureIndex Q E q hhi)).trans
    (by rw [he])

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TermwiseSplitInjection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J T : Type*} [Fintype I] [Fintype J] [Fintype T] [DecidableEq I]

omit [Fintype V] [DecidableEq A] in
lemma postcomposeOnCycles_injective (E : BasedComplex Q (K := K) T)
    (F : BasedComplex Q (K := K) I) (G : BasedComplex Q (K := K) J)
    (ι : TermwiseSplitInjection Q F G) (n v : ℤ) :
    Function.Injective (postcomposeOnCycles Q E F G ι.inclusion n v) := by
  intro f g h
  apply Subtype.ext
  have hh := congrArg (fun f : homCycles Q E G n v => f.val * ι.retraction) h
  change (f.val * ι.inclusion.matrix) * ι.retraction =
    (g.val * ι.inclusion.matrix) * ι.retraction at hh
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ι.split] at hh
  apply Matrix.ext
  intro i j
  have hij := congrArg (fun m : Matrix T I (Q.Zigzag K) => m i j) hh
  simpa only [projectiveIdentity, Matrix.mul_diagonal,
    f.property.1.1.2, g.property.1.1.2] using hij

omit [DecidableEq A] in
lemma pure_coefficient_homDimension_mono (E : BasedComplex Q (K := K) T)
    (F : BasedComplex Q (K := K) I) (G : BasedComplex Q (K := K) J)
    {l k n v : ℤ} (hE : ∀ i, (E.placement i).level = l)
    (hF : ∀ i, (F.placement i).level = k) (hG : ∀ i, (G.placement i).level = k)
    (h : n+v=k-l) (ι : TermwiseSplitInjection Q F G) :
    homDimension Q E F n v ≤ homDimension Q E G n v := by
  unfold homDimension
  rw [(pureCoefficientCohomology Q E F hE hF h).finrank_eq,
    (pureCoefficientCohomology Q E G hE hG h).finrank_eq]
  exact LinearMap.finrank_le_finrank_of_injective
    (postcomposeOnCycles_injective Q E F G ι n v)

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma totalHomDimension_eq_sum_of_subset (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (t : ℤ) (D : Finset ℤ)
    (hD : homInternalSupport Q E F ⊆ D) :
    totalHomDimension Q E F t = ∑ v ∈ D, homDimension Q E F (t-v) v := by
  unfold totalHomDimension
  apply Finset.sum_subset hD
  intro v _ hv
  exact homDimension_off_internal_support Q E F (t-v) v hv

omit [DecidableEq A] in
lemma pure_total_coefficient_homDimension_mono (E : BasedComplex Q (K := K) T)
    (F : BasedComplex Q (K := K) I) (G : BasedComplex Q (K := K) J)
    {l k : ℤ} (hE : ∀ i, (E.placement i).level = l)
    (hF : ∀ i, (F.placement i).level = k) (hG : ∀ i, (G.placement i).level = k)
    (ι : TermwiseSplitInjection Q F G) :
    totalHomDimension Q E F (k-l) ≤ totalHomDimension Q E G (k-l) := by
  classical
  let D := homInternalSupport Q E F ∪ homInternalSupport Q E G
  rw [totalHomDimension_eq_sum_of_subset Q E F (k-l) D Finset.subset_union_left,
    totalHomDimension_eq_sum_of_subset Q E G (k-l) D Finset.subset_union_right]
  apply Finset.sum_le_sum
  intro v _
  exact pure_coefficient_homDimension_mono Q E F G hE hF hG (by omega) ι

lemma subobject_cartan_inequality (M : BasedComplex Q (K := K) J)
    (S : BasedComplex Q (K := K) I) (Y : BasedComplex Q (K := K) T)
    {q d : ℤ} (hM : ∀ i, (M.placement i).level = q)
    (hS : ∀ i, (S.placement i).level = q) (hY : ∀ i, (Y.placement i).level = d)
    (ι : TermwiseSplitInjection Q S M) (active : Set V)
    (hsS : ∀ i, (S.placement i).color ∈ active)
    (hsY : ∀ α ∈ active, ∀ c, coefficientSocle Q Y α c = ⊥)
    (hmid : totalHomDimension Q M Y (d-q+1) = 0) :
    (totalHomDimension Q M Y (d-q) : ℝ) ≤
      (generatorVector Q M - generatorVector Q S) ⬝ᵥ
        ((unfoldedCartan Q).mulVec (generatorVector Q Y)) := by
  rw [sub_dotProduct, pure_cartan_euler Q M Y hM hY, pure_cartan_euler Q S Y hS hY]
  have hz := pure_total_coefficient_homDimension_zero_of_socle_zero Q S Y hS hY active hsS hsY
  have hm := pure_total_coefficient_homDimension_mono Q Y S M hY hS hM ι
  have hm' : (totalHomDimension Q Y S (q-d) : ℝ) ≤ totalHomDimension Q Y M (q-d) := by
    exact_mod_cast hm
  have hn : (0 : ℝ) ≤ totalHomDimension Q S Y (d-q+1) := Nat.cast_nonneg _
  rw [hmid, hz, Nat.cast_zero]
  linarith

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomDimensionRetract
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J T:Type*} [Fintype I] [Fintype J] [Fintype T]
  [DecidableEq I] [DecidableEq J] [DecidableEq T]

omit [DecidableEq A] [DecidableEq I] in
lemma homDimension_retract_source (M:BasedComplex Q (K:=K) T)
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (ι:Map Q M E) (π:Map Q E M)
    (hret:ι.matrix*π.matrix=projectiveIdentity Q M.placement) (n v:ℤ) :
    homDimension Q M F n v ≤ homDimension Q E F n v := by
  let U:=sandwichHomOperator Q π (Map.identity Q F)
  let W:=sandwichHomOperator Q ι (Map.identity Q F)
  apply LinearMap.finrank_le_finrank_of_injective (f:=U.onCohomology n v)
  apply U.onCohomology_injective
  intro f hf hUf
  have h:=W.map_boundaries n v hUf
  have hcancel:W.component n (U.component n f)=f := by
    change ι.matrix*(π.matrix*f*projectiveIdentity Q (K:=K) F.placement)*
      projectiveIdentity Q (K:=K) F.placement=f
    erw [mul_projectiveIdentity Q (projectiveEntries_mul Q π.entries hf.1.1),
      ← Matrix.mul_assoc,hret,projectiveIdentity_mul Q hf.1.1,
      mul_projectiveIdentity Q hf.1.1]
  rwa [hcancel] at h

omit [DecidableEq A] [DecidableEq I] in
lemma totalHomDimension_retract_source (M:BasedComplex Q (K:=K) T)
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (ι:Map Q M E) (π:Map Q E M)
    (hret:ι.matrix*π.matrix=projectiveIdentity Q M.placement) (t:ℤ) :
    totalHomDimension Q M F t ≤ totalHomDimension Q E F t := by
  classical
  let D:=homInternalSupport Q M F ∪ homInternalSupport Q E F
  rw [totalHomDimension_eq_sum_of_subset Q M F t D Finset.subset_union_left,
    totalHomDimension_eq_sum_of_subset Q E F t D Finset.subset_union_right]
  exact Finset.sum_le_sum (fun v _=>homDimension_retract_source Q M E F ι π hret _ _)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InverseMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open _root_.Matrix

attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L:Type u} [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]
  {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}

omit [Fintype V] [DecidableEq A] in
theorem classLayer_eq_of_cone_gap (f:Map Q E F) (hE:E.IsMinimal Q) (hF:F.IsMinimal Q)
    (D:BasedComplex Q (K:=K) L) (e:HomotopyEquivalence Q (f.cone Q) D)
    (q:ℤ) (hD:∀ j,(D.placement j).level≠q-1 ∧ (D.placement j).level≠q) :
    classLayer Q q (classOfComplex Q E)=classLayer Q q (classOfComplex Q F) := by
  rw [classLayer_minimal Q E hE,classLayer_minimal Q F hF]
  exact Quotient.sound ⟨(coneLayerIsomorphism Q f hE hF D e q hD).toHomotopyEquivalence Q⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LayerConeEquivalence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L:Type u} [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]
  {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}

omit [Fintype V] [DecidableEq A] in
theorem classLayer_eq_of_cone_equivalence (f:Map Q E F)
    (D:BasedComplex Q (K:=K) L) (e:HomotopyEquivalence Q (f.cone Q) D)
    (q:ℤ) (hD:∀ j,(D.placement j).level≠q-1 ∧ (D.placement j).level≠q) :
    classLayer Q q (classOfComplex Q E)=classLayer Q q (classOfComplex Q F) := by
  let E₀:=minimalClassModel Q (classOfComplex Q E)
  let F₀:=minimalClassModel Q (classOfComplex Q F)
  let a:HomotopyEquivalence Q E₀.complex E:=minimalClassModelEquivalence Q E
  let b:HomotopyEquivalence Q F F₀.complex:=(minimalClassModelEquivalence Q F).symm Q
  let h:=a.forward.comp Q f
  let g:=h.comp Q b.forward
  let c:HomotopyEquivalence Q (g.cone Q) D:=
    (((b.coneTarget Q h).symm Q).trans Q (a.coneSource Q f)).trans Q e
  have hh:=classLayer_eq_of_cone_gap Q g
    (minimalClassModel_minimal Q (classOfComplex Q E))
    (minimalClassModel_minimal Q (classOfComplex Q F)) D c q hD
  have he:classOfComplex Q E₀.complex=classOfComplex Q E:=minimalClassModel_class Q _
  have hf:classOfComplex Q F₀.complex=classOfComplex Q F:=minimalClassModel_class Q _
  exact (congrArg (classLayer Q q) he).symm.trans
    (hh.trans (congrArg (classLayer Q q) hf))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LayerTotalHomDimension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} [Field K] (Q:ReversibleQuiver V A)
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma frameModel_pure_orthogonal_middle_dimension (hn:∀ a,Q.source a≠Q.target a)
    (C:CoxeterMatrix V) (hC:UnfoldedPresentation Q C) (x:Artin C)
    {α β:V} (hab:OrthogonalVertices Q α β) (l k:ℤ) :
    totalHomDimension Q
      ((frameModel Q (K:=K) hn C hC x α).complex.pureLayer Q (frameModel_minimal Q hn C hC x α) l)
      ((frameModel Q (K:=K) hn C hC x β).complex.pureLayer Q (frameModel_minimal Q hn C hC x β) k)
      (k-l+1)=0 := by
  unfold totalHomDimension
  apply Finset.sum_eq_zero
  intro v _
  apply homDimension_zero_of_cycles_boundary Q
  intro f hf
  apply frameModel_orthogonal_layer_middle_vanishing Q hn C hC x hab l k _ v hf
  exact pure_homSpace_linear Q _ _ (fun i=>i.property) (fun i=>i.property) (by omega) hf.1

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_ClosedNeighborhood
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
universe u
variable {V A : Type u} (Q : ReversibleQuiver V A)

namespace Zigzag.BasedComplex
open _root_.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {K : Type*} [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma ClassCapOn.mono {x : FiniteHomotopyClass Q (K:=K)} {U T : Set V} {q : ℤ}
    (h : ClassCapOn Q x U q) (hT : T⊆U) : ClassCapOn Q x T q := fun i hi=>h i (hT hi)

omit [Fintype V] [DecidableEq A] in
lemma classCapOn_of_upper (x : FiniteHomotopyClass Q (K:=K)) (U : Set V) (q : ℤ)
    (h : ClassUpperBound Q q x) : ClassCapOn Q x U q := fun i _=>h i

lemma reducedNegativeAmplitudeTwist_cap {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K:=K) I) (U : Set V) (q : ℤ)
    (hcap : ∀ i,(E.placement i).color∈Q.closedNeighborhood U → (E.placement i).level≤q)
    (α : V) (hα : α∈U) :
    ∀ k,((reducedNegativeAmplitudeTwist Q E α).placement k).color∈Q.closedNeighborhood U →
      ((reducedNegativeAmplitudeTwist Q E α).placement k).level≤q := by
  intro k hk
  rw [reducedNegativeAmplitudeTwist_placement] at hk ⊢
  rcases k with p|i
  · have hi:=hcap p.val.1 (Q.corner_target_mem_neighborhood hα p.val.2)
    have hp:=Path.length_cases p.val.2.val
    have hn:=p.property
    dsimp only [GeneratorPlacement.level] at hi ⊢
    rcases hp with hp|hp|hp <;> omega
  · exact hcap i.val hk

theorem classNegativeTwist_capOn (x : FiniteHomotopyClass Q (K:=K))
    (U : Set V) (q : ℤ) (hcap : ClassCapOn Q x (Q.closedNeighborhood U) q)
    (α : V) (hα : α∈U) :
    ClassCapOn Q (classNegativeTwist Q α x) (Q.closedNeighborhood U) q := by
  let E:=minimalClassModel Q x
  let y:=classNegativeTwist Q α x
  let F:=minimalClassModel Q y
  have he : classOfComplex Q (E.complex.negativeTwist Q α)=classOfComplex Q F.complex := by
    change classNegativeTwist Q α (classOfComplex Q E.complex)=classOfComplex Q F.complex
    have hx : classOfComplex Q E.complex=x := minimalClassModel_class Q x
    have hy : classOfComplex Q F.complex=y := minimalClassModel_class Q y
    rw [hx,hy]
  obtain ⟨e⟩:=Quotient.exact he
  have reduction : HomotopyEquivalence Q (E.complex.negativeTwist Q α)
      (reducedNegativeAmplitudeTwist Q E.complex α) := by
    convert negativeAmplitudeTwistReduction Q E.complex α using 1
    all_goals try with_reducible_and_instances rfl
  exact minimal_bound_transport Q (reducedNegativeAmplitudeTwist Q E.complex α) F.complex
    (minimalClassModel_minimal Q y)
    ((reduction.symm Q).trans Q e)
    (fun p=>p.color∈Q.closedNeighborhood U → p.level≤q)
    (reducedNegativeAmplitudeTwist_cap Q E.complex U q hcap α hα)

lemma inverseWord_capOn (w : List V) (x : FiniteHomotopyClass Q (K:=K))
    (U : Set V) (q : ℤ) (hcap : ClassCapOn Q x (Q.closedNeighborhood U) q)
    (hw : ∀ α∈w,α∈U) :
    ClassCapOn Q (inverseWordAction Q w x) (Q.closedNeighborhood U) q := by
  induction w generalizing x with
  | nil => exact hcap
  | cons α w ih =>
    exact ih _ (classNegativeTwist_capOn Q x U q hcap α (hw α (by simp)))
      (fun β hβ=>hw β (by simp [hβ]))

end Zigzag.BasedComplex
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_NegativeTwistModern
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] in
lemma classLayer_eq_self_of_pure (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (h:∀ i,(E.placement i).level=q) :
    classLayer Q q (classOfComplex Q E)=classOfComplex Q E := by
  rw [classLayer_minimal Q E hE]
  have he:(E.pureLayer Q hE q).reindex Q (allPureIndex Q E q h)=E := by
    apply ext_placement_differential Q <;> rfl
  exact (classOfComplex_reindex Q _ (allPureIndex Q E q h)).trans (by rw [he])

omit [Fintype V] [DecidableEq A] in
lemma classLayer_idempotent (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) :
    classLayer Q q (classLayer Q q x)=classLayer Q q x := by
  let y:=classLayer Q q x
  let E:=minimalClassModel Q y
  have hp:∀ i,(E.complex.placement i).level=q := fun i=>
    le_antisymm (classLayer_upperBound Q x q i) (classLayer_lowerBound Q x q i)
  have he:classOfComplex Q E.complex=y:=minimalClassModel_class Q y
  simpa only [he] using classLayer_eq_self_of_pure Q E.complex
    (minimalClassModel_minimal Q y) q hp

omit [Fintype V] [DecidableEq A] in
lemma classLayer_lowerTruncation (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (q:ℤ) :
    classLayer Q q (classOfComplex Q (lowerTruncation Q E hE q))=
      classLayer Q q (classOfComplex Q E) := by
  apply classLayer_eq_of_cone_equivalence Q (lowInclusion Q E _ (levelDownClosed Q E hE q))
    (upperTruncation Q E hE q) (lowConeReduction Q E _ _) q
  intro j
  have hj:=j.property
  change ¬(E.placement j).level≤q at hj
  change (E.placement j).level≠q-1 ∧ (E.placement j).level≠q
  omega

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma capped_upperTruncation_far (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (U:Set V) (q:ℤ)
    (hcap:∀ i,(E.placement i).color∈Q.closedNeighborhood U → (E.placement i).level≤q) :
    ∀ i,((upperTruncation Q E hE q).placement i).color∉Q.closedNeighborhood U := by
  intro i hi
  exact i.property (hcap i hi)

lemma negativeLayer_lowerTruncation (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (U:Set V) (q:ℤ)
    (hcap:∀ i,(E.placement i).color∈Q.closedNeighborhood U → (E.placement i).level≤q)
    (α:V) (hα:α∈U) :
    classLayer Q q (classOfComplex Q ((lowerTruncation Q E hE q).negativeTwist Q α))=
      classLayer Q q (classOfComplex Q (E.negativeTwist Q α)) := by
  let f:=lowInclusion Q E _ (levelDownClosed Q E hE q)
  let R:=upperTruncation Q E hE q
  have coneIso : ChainIsomorphism Q ((f.cone Q).negativeTwist Q α)
      ((f.negativeTwist Q α).cone Q) := by
    convert negativeTwistCone Q f α using 1
    all_goals try with_reducible_and_instances rfl
  let e:HomotopyEquivalence Q ((f.negativeTwist Q α).cone Q) R:=
    ((coneIso.toHomotopyEquivalence Q).symm Q).trans Q
      (((lowConeReduction Q E (lowerLevelSet Q E q) (levelDownClosed Q E hE q)).negativeTwistModern Q α).trans Q
        (negativeTwistFar Q R U (capped_upperTruncation_far Q E hE U q hcap) α hα))
  apply classLayer_eq_of_cone_equivalence Q (f.negativeTwist Q α) R e q
  intro j
  have hj:=j.property
  change ¬(E.placement j).level≤q at hj
  change (E.placement j).level≠q-1 ∧ (E.placement j).level≠q
  omega

lemma negativeLayer_top (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (hhi:∀ i,(E.placement i).level≤q) (α:V) :
    classLayer Q q (classNegativeTwist Q α (classOfComplex Q E))=
      classLayer Q q (classNegativeTwist Q α (classLayer Q q (classOfComplex Q E))) := by
  let f:=highProjection Q E _ (levelDownClosed Q E hE (q-1))
  let D:=(highConePivot Q E _ (levelDownClosed Q E hE (q-1))).reduced Q
  let G:=minimalClassModel Q (classOfComplex Q (D.negativeTwist Q α))
  let e₀:HomotopyEquivalence Q (D.negativeTwist Q α) G.complex:=
    (minimalClassModelEquivalence Q (D.negativeTwist Q α)).symm Q
  have hd:∀ i,(D.placement i).level≤q-2 := by
    intro i
    rw [highConeRetained_level]
    have hi:=i.property
    change (E.placement i).level≤q-1 at hi
    omega
  have hg:∀ i,(G.complex.placement i).level≤q-2 :=
    negativeTwist_upper_bound Q D G.complex hd α (minimalClassModel_minimal Q _) e₀
  have coneIso : ChainIsomorphism Q ((f.cone Q).negativeTwist Q α)
      ((f.negativeTwist Q α).cone Q) := by
    convert negativeTwistCone Q f α using 1
    all_goals try with_reducible_and_instances rfl
  let e:HomotopyEquivalence Q ((f.negativeTwist Q α).cone Q) G.complex:=
    ((coneIso.toHomotopyEquivalence Q).symm Q).trans Q
      ((((highConeReduction Q E (lowerLevelSet Q E (q-1)) (levelDownClosed Q E hE (q-1))).negativeTwistModern Q α)).trans Q e₀)
  have hh:=classLayer_eq_of_cone_equivalence Q (f.negativeTwist Q α) G.complex e q
    (fun i=>by have hi:=hg i; constructor <;> omega)
  change classLayer Q q (classNegativeTwist Q α (classOfComplex Q E))=
    classLayer Q q (classNegativeTwist Q α (classOfComplex Q (upperTruncation Q E hE (q-1)))) at hh
  rwa [highRestriction_top_eq_layer Q E hE q hhi] at hh

lemma classNegativeTwist_capped_layer (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (hcap:ClassCapOn Q x (Q.closedNeighborhood U) q)
    (α:V) (hα:α∈U) :
    classLayer Q q (classNegativeTwist Q α x)=
      classLayer Q q (classNegativeTwist Q α (classLayer Q q x)) := by
  let E:=minimalClassModel Q x
  have hE:=minimalClassModel_minimal Q x
  let L:=lowerTruncation Q E.complex hE q
  have hx:classOfComplex Q E.complex=x:=minimalClassModel_class Q x
  have hl:=negativeLayer_lowerTruncation Q E.complex hE U q hcap α hα
  have ht:=negativeLayer_top Q L (lowerTruncation_minimal Q E.complex hE q) q
    (fun i=>i.property) α
  have he:=classLayer_lowerTruncation Q E.complex hE q
  change classLayer Q q (classNegativeTwist Q α (classOfComplex Q L))=
    classLayer Q q (classNegativeTwist Q α (classOfComplex Q E.complex)) at hl
  rw [hx] at hl he
  exact hl.symm.trans (ht.trans (congrArg (fun y=>classLayer Q q (classNegativeTwist Q α y)) he))

theorem inverseWord_capped_layer (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (hcap:ClassCapOn Q x (Q.closedNeighborhood U) q)
    (hw:∀ α∈w,α∈U) :
    classLayer Q q (inverseWordAction Q w x)=
      classLayer Q q (inverseWordAction Q w (classLayer Q q x)) := by
  induction w generalizing x with
  | nil=>exact (classLayer_idempotent Q x q).symm
  | cons α w ih=>
    have hα:=hw α (by simp)
    have hw':∀ β∈w,β∈U:=fun β hβ=>hw β (by simp [hβ])
    have hc:=classNegativeTwist_capped_layer Q x U q hcap α hα
    have hy:=classCapOn_of_upper Q (classLayer Q q x) (Q.closedNeighborhood U) q
      (classLayer_upperBound Q x q)
    exact (ih _ (classNegativeTwist_capOn Q x U q hcap α hα) hw').trans
      ((congrArg (fun y=>classLayer Q q (inverseWordAction Q w y)) hc).trans
        (ih _ (classNegativeTwist_capOn Q _ U q hy α hα) hw').symm)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PacketPermAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  (hn : ∀ a, Q.source a ≠ Q.target a)
  (M:CoxeterMatrix V) (hM:UnfoldedPresentation Q M)
local notation "Act" => unfoldedArtinAction Q (K:=K) hn M hM

lemma classPacketPerm_in_action {J:Type u} [Fintype J] (v:J → V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)) :
    ∃ x:Artin M,Act x=classPacketPerm Q hn v hv := by
  suffices hh : ∀ (J:Type u) [Fintype J] (v:J → V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)),
    ∃ x:Artin M,Act x=classPacketPerm Q hn v hv from hh J v hv
  intro J inst
  apply Fintype.induction_empty_option (P:=fun J _=>∀ (v:J → V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)),
    ∃ x:Artin M,Act x=classPacketPerm Q hn v hv) _ _ _ J
  · intro J L instL e ih
    let := Fintype.ofEquiv L e.symm
    intro v hv
    rw [classPacketPerm_reindex Q hn v hv e]
    exact ih _ _
  · intro v hv
    refine ⟨1,?_⟩
    rw [map_one,classPacketPerm_empty]
    rfl
  · intro J inst ih v hv
    obtain ⟨x,hx⟩:=ih (v ∘ some) (fun a b hab=>hv (fun he=>hab (Option.some.inj he)))
    refine ⟨generator M (v none)*x,?_⟩
    rw [map_mul,unfoldedArtinAction_generator,hx,classPacketPerm_cons]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TotalVectorLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma classLayer_eq_self_of_bounds (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hl:ClassLowerBound Q q x) (hh:ClassUpperBound Q q x) : classLayer Q q x=x := by
  have h:=classLayer_eq_self_of_pure Q (minimalClassModel Q x).complex
    (minimalClassModel_minimal Q x) q (fun i=>le_antisymm (hh i) (hl i))
  have hx:classOfComplex Q (minimalClassModel Q x).complex=x:=minimalClassModel_class Q x
  rw [hx] at h
  exact h

omit [Fintype V] [DecidableEq A] in
lemma classTotalVector_pure_apply (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hl:ClassLowerBound Q q x) (hh:ClassUpperBound Q q x) (α:V) :
    classTotalVector Q x α=(classLevelArray Q x (α,q):ℝ) := by
  exact (congrArg (fun y=>classTotalVector Q y α) (classLayer_eq_self_of_bounds Q x q hl hh)).symm.trans
    (classTotalVector_layer_apply Q x q α)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Extend
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
namespace NullBoundary

open scoped _root_.Matrix Classical
open Set Filter

lemma continuousLinearMap_eq_zero_of_interior_max
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E →L[ℝ] ℝ) (s : Set E) {x : E}
    (hx : x ∈ interior s) (hmax : ∀ y ∈ s, f y ≤ f x) : f = 0 := by
  have hlocal : IsLocalMax f x := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hx] with y hy
    exact hmax y hy
  simpa only [f.fderiv] using hlocal.fderiv_eq_zero

variable {V : Type*}

lemma extend_restrict (J : Set V) (v : V → ℝ) (hv : ∀ i ∉ J, v i = 0) :
    extend J (fun i => v i) = v := by
  classical
  funext i
  by_cases hi : i ∈ J
  · simp [extend, hi]
  · simp [extend, hi, hv i hi]

variable [Fintype V]

lemma extend_dot (J : Set V) (s : J → ℝ) (v : V → ℝ) :
    extend J s ⬝ᵥ v = ∑ j : J, s j * v j := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ J)
    (fun i => extend J s i * v i)
  have hc : (∑ i : {x // x ∉ J}, extend J s i * v i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [extend, i.property]
  simpa only [dotProduct, extend_apply_mem, hc, add_zero] using h.symm

lemma coordFunctional_apply (J : Set V) (v : V → ℝ) (s : J → ℝ) :
    coordFunctional J v s = extend J s ⬝ᵥ v := by
  classical
  simp [coordFunctional, extend_dot, mul_comm]

lemma null_mulVec_nonpos (C : Matrix V V ℝ) (I : Set V) (c : V → ℝ)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (hc : ∀ i, 0 ≤ c i) (hsupp : ∀ i ∉ I, c i = 0)
    (hnull : ∀ i ∈ I, (C *ᵥ c) i = 0) : ∀ i, (C *ᵥ c) i ≤ 0 := by
  intro i
  by_cases hi : i ∈ I
  · exact le_of_eq (hnull i hi)
  · apply Finset.sum_nonpos
    intro j _
    by_cases hij : i = j
    · subst j; simp [hsupp i hi]
    · exact mul_nonpos_of_nonpos_of_nonneg (hOff i j hij) (hc j)

lemma null_pairing_nonpos (C : Matrix V V ℝ) (I : Set V) (c y : V → ℝ)
    (hSym : ∀ i j, C i j = C j i) (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (hc : ∀ i, 0 ≤ c i) (hsupp : ∀ i ∉ I, c i = 0)
    (hnull : ∀ i ∈ I, (C *ᵥ c) i = 0) (hy : ∀ i, 0 ≤ y i) :
    c ⬝ᵥ (C *ᵥ y) ≤ 0 := by
  have hCt : C.transpose = C := by ext i j; exact hSym j i
  rw [← hCt, Matrix.dotProduct_transpose_mulVec]
  exact Finset.sum_nonpos fun i _ =>
    mul_nonpos_of_nonneg_of_nonpos (hy i) (null_mulVec_nonpos C I c hOff hc hsupp hnull i)

lemma null_pairing_eq_zero_boundary (C : Matrix V V ℝ) (I : Set V) (c y : V → ℝ)
    (hSym : ∀ i j, C i j = C j i) (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (hc : ∀ i, 0 ≤ c i) (hsupp : ∀ i ∉ I, c i = 0)
    (hpos : ∀ i ∈ I, 0 < c i)
    (hnull : ∀ i ∈ I, (C *ᵥ c) i = 0) (hy : ∀ i, 0 ≤ y i)
    (heq : c ⬝ᵥ (C *ᵥ y) = 0) :
    ∀ a ∉ I, (∃ i ∈ I, C a i < 0) → y a = 0 := by
  intro a ha ⟨i, hi, hai⟩
  have hn := null_mulVec_nonpos C I c hOff hc hsupp hnull
  have haz : (C *ᵥ c) a < 0 := by
    apply Finset.sum_neg'
    · intro j _
      by_cases haj : a = j
      · subst j; simp [hsupp a ha]
      · exact mul_nonpos_of_nonpos_of_nonneg (hOff a j haj) (hc j)
    · exact ⟨i, Finset.mem_univ _, mul_neg_of_neg_of_pos hai (hpos i hi)⟩
  have hs : y ⬝ᵥ (C *ᵥ c) = 0 := by
    have hCt : C.transpose = C := by ext i j; exact hSym j i
    simpa only [hCt] using (Matrix.dotProduct_transpose_mulVec C y c).trans heq
  have hz : y a * (C *ᵥ c) a = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos (fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos (hy j) (hn j))).mp hs a (Finset.mem_univ _)
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_lt haz)

lemma convexHull_bound (J : Set V) (m r : V → ℝ) (B : Set (J → ℝ)) (a : ℝ)
    (hb : ∀ s ∈ B, a ≤ (m - extend J s) ⬝ᵥ r) :
    ∀ s ∈ convexHull ℝ B, a ≤ (m - extend J s) ⬝ᵥ r := by
  let f := coordFunctional J r
  have hs : B ⊆ f ⁻¹' Iic (m ⬝ᵥ r - a) := by
    intro s hs
    have h := hb s hs
    change f s ≤ m ⬝ᵥ r - a
    dsimp [f]
    rw [coordFunctional_apply]
    rw [sub_dotProduct] at h
    linarith
  have hc := convexHull_min hs ((convex_Iic (m ⬝ᵥ r - a)).linear_preimage f.toLinearMap)
  intro s hs
  have h := hc hs
  change f s ≤ m ⬝ᵥ r - a at h
  dsimp [f] at h
  rw [coordFunctional_apply] at h
  rw [sub_dotProduct]
  linarith

theorem convex_null_boundary_separation
    (C : Matrix V V ℝ) (I J : Set V) (c m y : V → ℝ) (B : Set (J → ℝ)) (a : ℝ)
    (hSym : ∀ i j, C i j = C j i) (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (hc : ∀ i, 0 ≤ c i) (hsupp : ∀ i ∉ I, c i = 0)
    (hpos : ∀ i ∈ I, 0 < c i)
    (hnull : ∀ i ∈ I, (C *ᵥ c) i = 0) (hy : ∀ i, 0 ≤ y i)
    (hext : ∀ i ∉ J, m i = c i)
    (he : (fun j : J => m j - c j) ∈ interior (convexHull ℝ B))
    (ha : 0 ≤ a) (hb : ∀ s ∈ B, a ≤ (m - extend J s) ⬝ᵥ (C *ᵥ y)) :
    (∀ b ∉ I, (∃ i ∈ I, C b i < 0) → y b = 0) ∧
    (∀ j ∈ J, (C *ᵥ y) j = 0) ∧ a = 0 ∧ m ⬝ᵥ (C *ᵥ y) = 0 := by
  let e : J → ℝ := fun j => m j - c j
  have hex : extend J e = m - c :=
    extend_restrict J (m-c) (fun i hi => by simp [hext i hi])
  have hbound := convexHull_bound J m (C *ᵥ y) B a hb
  have havg : a ≤ c ⬝ᵥ (C *ᵥ y) := by
    have h := hbound e (interior_subset he)
    simpa only [hex, sub_sub_cancel] using h
  have hsign := null_pairing_nonpos C I c y hSym hOff hc hsupp hnull hy
  have hzero : c ⬝ᵥ (C *ᵥ y) = 0 := le_antisymm hsign (ha.trans havg)
  have haz : a = 0 := le_antisymm (by linarith) ha
  have hmax : ∀ s ∈ convexHull ℝ B,
      coordFunctional J (C *ᵥ y) s ≤ coordFunctional J (C *ᵥ y) e := by
    intro s hs
    have h := hbound s hs
    rw [haz, sub_dotProduct] at h
    rw [coordFunctional_apply, coordFunctional_apply, hex, sub_dotProduct, hzero, sub_zero]
    linarith
  have hfzero := continuousLinearMap_eq_zero_of_interior_max
    (coordFunctional J (C *ᵥ y)) (convexHull ℝ B) he hmax
  refine ⟨null_pairing_eq_zero_boundary C I c y hSym hOff hc hsupp hpos hnull hy hzero,
    ?_, haz, ?_⟩
  · intro j hj
    have h := congrArg (fun f : (J → ℝ) →L[ℝ] ℝ => f (Pi.single ⟨j, hj⟩ 1)) hfzero
    simpa [coordFunctional, Pi.single_apply] using h
  · have h := congrArg (fun f : (J → ℝ) →L[ℝ] ℝ => f e) hfzero
    rw [coordFunctional_apply, hex, sub_dotProduct, hzero] at h
    simpa using h

end NullBoundary
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_UnfoldedCartanSymm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
open scoped _root_.Matrix

variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

variable {I : Type*} [Fintype I]

omit [Fintype V] [DecidableEq A] in
lemma generatorVector_eq_zero_off (E : BasedComplex Q (K := K) I) (active : Set V)
    (hs : ∀ i, (E.placement i).color ∈ active) (α : V) (hα : α ∉ active) :
    generatorVector Q E α = 0 := by
  rw [generatorVector_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hne : (E.placement i).color ≠ α := fun h => hα (h ▸ hs i)
  simp only [ite_eq_right hne]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_StrictChamber
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W:Type*} [Fintype S] [DecidableEq S] [Group W] [Fintype W]
  {M:CoxeterMatrix S} (cs:CoxeterSystem M W)

theorem dual_chamber_cover (f:(S → ℝ) →ₗ[ℝ] ℝ) :
    ∃ w:W,∃ a:S → ℝ,(∀ i,0 ≤ a i) ∧
      ∀ v:S → ℝ,f v=∑ i,a i*(representation cs w v) i := by
  obtain ⟨p,hp⟩:=exists_strict_chamber cs
  obtain ⟨w,_,hw⟩:=Finset.exists_max_image (Finset.univ:Finset W)
    (fun w=>f (representation cs w p)) Finset.univ_nonempty
  let a:S → ℝ := fun i=>f (representation cs w (Pi.single i 1))
  have ha : ∀ i,0 ≤ a i := by
    intro i
    have h:=hw (w*cs.simple i) (Finset.mem_univ _)
    simp only [map_mul,LinearEquiv.mul_apply,representation_simple,simpleReflection_apply,
      hp,one_smul,map_sub] at h
    dsimp [a]
    linarith
  refine ⟨w⁻¹,a,ha,?_⟩
  intro v
  have hv : representation cs w (representation cs w⁻¹ v)=v := by
    rw [← LinearEquiv.mul_apply,← map_mul,mul_inv_cancel,map_one]
    rfl
  have hv' : representation cs w⁻¹ v=∑ i,(representation cs w⁻¹ v) i • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply]
  calc
    f v=f (representation cs w (representation cs w⁻¹ v)) := congrArg f hv.symm
    _ = _ := by
      conv_lhs => rw [hv']
      simp only [map_sum,map_smul,smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [a]
      rw [mul_comm]

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_ChamberInequalitiesConvexHull
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W:Type*} [Fintype S] [DecidableEq S] [Group W] [Fintype W]
  {M:CoxeterMatrix S} (cs:CoxeterSystem M W)

theorem chamber_inequalities_convexHull (σ:W → S → ℝ) (e:S → ℝ)
    (h : ∀ w i,0 ≤ (representation cs w (e-σ w)) i) :
    e ∈ convexHull ℝ (Set.range σ) := by
  by_contra he
  obtain ⟨f,u,heu,hu⟩:=geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (Set.range σ)) ((Set.finite_range σ).isClosed_convexHull ℝ) he
  obtain ⟨w,a,ha,hf⟩:=dual_chamber_cover cs f.toLinearMap
  have hdiff : 0 ≤ f (e-σ w) := by
    rw [show f (e-σ w)=∑ i,a i*(representation cs w (e-σ w)) i from hf _]
    exact Finset.sum_nonneg (fun i _=>mul_nonneg (ha i) (h w i))
  have hs:=hu (σ w) (subset_convexHull ℝ (Set.range σ) (Set.mem_range_self w))
  rw [map_sub] at hdiff
  linarith

theorem chamber_inequalities_interior (σ:W → S → ℝ) (e:S → ℝ)
    (h : ∀ w i,0 < (representation cs w (e-σ w)) i) :
    e ∈ interior (convexHull ℝ (Set.range σ)) := by
  let U : Set (S → ℝ) := {x | ∀ w i,0 < (representation cs w (x-σ w)) i}
  have ho : IsOpen U := by
    have hU : U=(⋂ w:W,⋂ i:S,{x:S → ℝ | 0 < (representation cs w (x-σ w)) i}) := by
      ext x
      simp [U]
    rw [hU]
    apply isOpen_iInter_of_finite
    intro w
    apply isOpen_iInter_of_finite
    intro i
    have hc : Continuous (fun x:S → ℝ=>representation cs w (x-σ w)) :=
      ((representation cs w).toLinearMap.continuous_of_finiteDimensional).comp
      (continuous_id.sub continuous_const)
    exact isOpen_lt continuous_const ((continuous_apply i).comp hc)
  have hsub : U ⊆ convexHull ℝ (Set.range σ) := by
    intro x hx
    exact chamber_inequalities_convexHull cs σ x (fun w i=>(hx w i).le)
  exact interior_maximal hsub ho h

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E)

omit [Fintype V] [DecidableEq V] in
lemma fusionQuiver_arrow_count (hd : ∀ s t, d s t = d t s)
    (α β : FusionVertex (V := V) m) :
    Nat.card {a : FusionQuiverArrow m d // (fusionQuiver m d hd).source a = α ∧
      (fusionQuiver m d hd).target a = β} = (d α.1 β.1).multiplicity m α.2 β.2 := by
  rw [Nat.card_congr (fusionArrowAtEquiv m d hd α β), Nat.card_fin]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionPacketAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator _root_.OAI.HarmonicArtin.unfoldedHom_simple _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "C" => fusionOrdinaryMatrix m d hd
local notation "Act" => fusionOrdinaryAction m d hd (K:=K) hdiag

lemma fusionPacket_in_action (s:V) : ∃ x:Artin C,
    Act x=fusionPacketPerm m d hd hdiag s :=
  classPacketPerm_in_action Q (fusionQuiver_no_loops m d hd hdiag) C
    (fusionOrdinaryPresentation m d hd) (fun L=>(s,L)) (fusionColor_orthogonal m d hd hdiag s)

lemma fusionSignedPacket_in_action (a:V × Bool) : ∃ x:Artin C,
    Act x=fusionSignedPacketPerm m d hd hdiag a := by
  obtain ⟨x,hx⟩ := fusionPacket_in_action m d hd hdiag (K:=K) a.1
  cases h:a.2
  · refine ⟨x⁻¹,?_⟩
    rw [map_inv,hx]
    simp [fusionSignedPacketPerm,h]
  · exact ⟨x,by simpa only [fusionSignedPacketPerm,h,↓reduceIte] using hx⟩

lemma fusionWord_in_action (w:List (V × Bool)) : ∃ x:Artin C,
    Act x=fusionWordPacketPerm m d hd hdiag w := by
  induction w with
  | nil => exact ⟨1,map_one Act⟩
  | cons a w ih =>
    obtain ⟨x,hx⟩ := fusionSignedPacket_in_action m d hd hdiag (K:=K) a
    obtain ⟨y,hy⟩ := ih
    exact ⟨x*y,by rw [map_mul,hx,hy]; rfl⟩

lemma fusionOrbit_in_action (w:List (V × Bool)) : ∃ x:Artin C, ∀ s L,
    fusionPacketOrbit m d hd hdiag w s L = unfoldedFrame Q
      (fusionQuiver_no_loops m d hd hdiag) C (fusionOrdinaryPresentation m d hd) x (s,L) := by
  obtain ⟨x,hx⟩ := fusionWord_in_action m d hd hdiag (K:=ℂ) w
  refine ⟨x,fun s L=>?_⟩
  exact congrArg (fun f=> f (initialClass Q (s,L))) hx.symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionOrbitModel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "C" => fusionOrdinaryMatrix m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "hn" => fusionQuiver_no_loops m d hd hdiag

lemma fusionOrbitLayer_middle (w:List (V × Bool)) (s:V) (L H:FusionLabel m) (l k:ℤ) :
    totalHomDimension Q (fusionOrbitLayer m d hd hdiag w s L l)
      (fusionOrbitLayer m d hd hdiag w s H k) (k-l+1)=0 := by
  obtain ⟨x,hx⟩:=fusionOrbit_in_action m d hd hdiag w
  change classLayerTotalHomDimension Q (O w s L) (O w s H) l k (k-l+1)=0
  rw [hx,hx]
  by_cases he:L=H
  · subst H
    exact
      frameModel_pure_middle_dimension Q hn C (fusionOrdinaryPresentation m d hd) (K:=ℂ) x (s,L) l k
  · have hab:=fusionQuiver_same_color m d hd hdiag s L H he
    exact
      frameModel_pure_orthogonal_middle_dimension Q hn C (fusionOrdinaryPresentation m d hd)
        (K:=ℂ) x hab l k

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionQuiverCartan
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E)
omit [Fintype V] in

lemma fusionQuiver_cartan (hd : ∀ s t, d s t = d t s) :
    ReversibleQuiver.Zigzag.BasedComplex.unfoldedCartan (fusionQuiver m d hd) =
      fusionUnfoldedCartan m d := by
  ext α β
  simp only [ReversibleQuiver.Zigzag.BasedComplex.unfoldedCartan,
    fusionQuiver_arrow_count, fusionUnfoldedCartan, Matrix.sub_apply, Matrix.diagonal_apply,
    Matrix.of_apply]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionOrbitMultiplicity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

lemma finite_weighted_cartan {I J A:Type*} [Fintype I] [Fintype J] [Fintype A]
    (C:Matrix A A ℝ) (a:I → ℝ) (b:J → ℝ) (x:I → A → ℝ) (y:J → A → ℝ) :
    (∑ i,a i • x i) ⬝ᵥ (C *ᵥ (∑ j,b j • y j)) =
      ∑ i,∑ j,a i*b j*(x i ⬝ᵥ (C *ᵥ y j)) := by
  simp only [Matrix.mulVec_sum,Matrix.mulVec_smul,sum_dotProduct,dotProduct_sum,
    smul_dotProduct,dotProduct_smul,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)

lemma fusionOrbitMultiplicity_nonneg (w:List (V × Bool)) (s:V) (q:ℤ) (v:V) :
    0 ≤ fusionOrbitMultiplicity m d hd hdiag hm w s q v :=
  (Classical.choose_spec (fusionPacketOrbit_count_proportional m d hd hdiag hm w s v q)).1

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CanonicalFusionMultiplicity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "C" => canonicalFusionLow m d hd hdiag (K:=ℂ)

lemma canonicalFusionMultiplicity_fold (w:List V) (z:List (V×Bool)) (s:V) (q:ℤ)
    (hp:∀ L,ClassLowerBound Q q (C w q (classLayer Q q (O z s L))) ∧
      ClassUpperBound Q q (C w q (classLayer Q q (O z s L)))) :
    (∑ L,fusionWeight m L • classTotalVector Q (C w q (classLayer Q q (O z s L))))=
      fusionFold m (canonicalFusionMultiplicity m d hd hdiag hm w z s q) := by
  ext ⟨v,L⟩
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp_rw [classTotalVector_pure_apply Q _ q (hp _).1 (hp _).2]
  have hc:=(Classical.choose_spec
    (canonicalFusionLow_count_proportional m d hd hdiag hm w z s v q q)).2 L
  simpa only [fusionFold,canonicalFusionMultiplicity,mul_comm] using hc

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ArtinActionWordArtin
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] {K : Type*} [Field K]
  (M : CoxeterMatrix S)
local notation "Q" => fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "aw" => sourceArtinAction M (K:=K)

lemma sourceArtinAction_wordArtin (u:List S) :
    aw (wordArtin M u)=((fusionExpandedWord (fusionLabelSize M)
      (u.map (Sum.inl : S→S⊕Unit))).map (classTwistPerm Q (K:=K) hn)).prod := by
  have hh:=fusionExpandedWord_perm (fusionLabelSize M) (coxeterFusionEdge M)
    (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (K:=K)
    (u.map (Sum.inl : S→S⊕Unit))
  rw [fusionWordPacketPerm_positive] at hh
  have ha: aw (wordArtin M u)=
      ((u.map (Sum.inl : S→S⊕Unit)).map
        (fusionPacketPerm (fusionLabelSize M) (coxeterFusionEdge M)
          (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M))).prod := by
    simp only [wordArtin,map_list_prod,List.map_map,sourceArtinAction_generator,Function.comp_def]
  refine ha.trans (hh.symm.trans ?_)
  exact congrArg (fun h : DecidableEq (FusionQuiverArrow (fusionLabelSize M) (coxeterFusionEdge M)) =>
    ((fusionExpandedWord (fusionLabelSize M) (u.map (Sum.inl : S→S⊕Unit))).map
      (@classTwistPerm _ _ K Q _ _ _ _ h hn)).prod) (Subsingleton.elim _ _)

lemma sourceArtinAction_positiveWord (u:List S) (x:FiniteHomotopyClass Q (K:=K)) :
    aw (wordArtin M u) x=positiveWordAction Q
      (fusionExpandedWord (fusionLabelSize M) (u.map (Sum.inl : S→S⊕Unit))) x := by
  rw [sourceArtinAction_wordArtin,positiveWordAction_eq_prod Q hn]

lemma sourceArtinAction_negativeWord (u:List S) (x:FiniteHomotopyClass Q (K:=K)) :
    aw (wordArtin M u)⁻¹ x=inverseWordAction Q
      (fusionExpandedWord (fusionLabelSize M) (u.map (Sum.inl : S→S⊕Unit))) x := by
  apply (aw (wordArtin M u)).injective
  rw [map_inv]
  change (aw (wordArtin M u)) ((aw (wordArtin M u)).symm x)=_
  rw [Equiv.apply_symm_apply,sourceArtinAction_positiveWord,positive_inverseWord Q hn]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CanonicalLowSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "C" => canonicalFusionLow m d hd hdiag (K:=ℂ)
local notation "σ" => canonicalFusionMultiplicity m d hd hdiag hm

lemma sourceCanonicalMultiplicity_support (J:Set S) (hJ:IsSpherical M J)
    (u:List J) (hu:(restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) :
    ∀ v,v∉Sum.inl '' J→σ (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)) z s q v=0 := by
  let w:=u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)
  have hp:∀ L,ClassLowerBound Q q (C w q (classLayer Q q (O z s L))) ∧
      ClassUpperBound Q q (C w q (classLayer Q q (O z s L))) := fun L=>
    sourceCanonicalLow_pure M J hJ u hu q _ (classLayer_lowerBound Q _ q) (classLayer_upperBound Q _ q)
  have hv:=canonicalFusionMultiplicity_fold m d hd hdiag hm w z s q hp
  intro v hnot
  let H:FusionLabel m:=fun e=>⟨0,by have h:2 ≤ m e:=le_trans (by norm_num) (fusionLabelSize_ge_four M e);omega⟩
  have hz:∀ L,classTotalVector Q (C w q (classLayer Q q (O z s L))) (v,H)=0 := by
    intro L
    apply generatorVector_eq_zero_off Q _ (Set.range (unfoldedInclusion M J))
      (sourceCanonicalLow_support M J u z s q L)
    rintro ⟨⟨j,H'⟩,hh⟩
    have he:Sum.inl (j:S)=v:=congrArg Prod.fst hh
    exact hnot ⟨j,j.property,he⟩
  have hval:=congrFun hv (v,H)
  simp only [Finset.sum_apply,Pi.smul_apply,hz,smul_zero,Finset.sum_const_zero,fusionFold] at hval
  exact (mul_eq_zero.mp hval.symm).resolve_left (ne_of_gt (fusionWeight_pos m hm H))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_RootExtension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix Geometric CoxeterExchange
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I:Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

omit [Fintype V] in
lemma rootExtension_apply (f:I→V) (hf:Function.Injective f) (x:I→ℝ) (i:I) :
    rootExtension f x (f i)=x i := by
  simp only [rootExtension,Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
  simp_rw [hf.eq_iff]
  simp

omit [Fintype V] [DecidableEq I] in
lemma rootExtension_outside (f:I→V) (x:I→ℝ) (v:V) (hv:v∉Set.range f) :
    rootExtension f x v=0 := by
  simp only [rootExtension,Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  have hi:v≠f i:=fun h=>hv ⟨i,h.symm⟩
  simp only [ite_eq_right hi,mul_zero]

omit [Fintype V] in
lemma rootExtension_restrict (f:I→V) (hf:Function.Injective f) (x:V→ℝ)
    (hx:∀ v,v∉Set.range f→x v=0) : rootExtension f (x∘f)=x := by
  ext v
  by_cases hv:v∈Set.range f
  · obtain ⟨i,rfl⟩:=hv
    exact rootExtension_apply f hf _ i
  · rw [rootExtension_outside f _ v hv,hx v hv]

omit [Fintype V] [DecidableEq I] in
lemma rootExtension_sub (f:I→V) (x y:I→ℝ) :
    rootExtension f (x-y)=rootExtension f x-rootExtension f y := by
  simp only [rootExtension,Pi.sub_apply,sub_smul,Finset.sum_sub_distrib]

omit [Fintype V] [DecidableEq I] in
lemma rootExtension_smul (f:I→V) (r:ℝ) (x:I→ℝ) :
    rootExtension f (r • x)=r • rootExtension f x := by
  simp only [rootExtension,Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]

omit [Fintype V] in
lemma rootExtension_single (f:I→V) (i:I) :
    rootExtension f (Pi.single i 1)=Pi.single (f i) 1 := by
  simp [rootExtension,Pi.single_apply]

omit [DecidableEq I] in
lemma rootExtension_mulVec (C:Matrix V V ℝ) (f:I→V) (x:I→ℝ) (i:I) :
    (C *ᵥ rootExtension f x) (f i)=(C.submatrix f f *ᵥ x) i := by
  unfold rootExtension
  rw [Matrix.mulVec_sum]
  simp only [Finset.sum_apply,Matrix.mulVec_smul,Pi.smul_apply,Matrix.mulVec_single,
    Matrix.col,Matrix.transpose_apply,Matrix.mulVec,dotProduct,
    Matrix.submatrix_apply,smul_eq_mul]
  simp [MulOpposite.op_one,one_smul,mul_comm]

lemma rowReflect_rootExtension (C:Matrix V V ℝ) (f:I→V) (i:I) (x:I→ℝ) :
    rowReflect C (f i) (rootExtension f x)=rootExtension f (rowReflect (C.submatrix f f) i x) := by
  simp only [rowReflect,rootExtension_mulVec,rootExtension_sub,rootExtension_smul,rootExtension_single]

lemma rowReflectWord_rootExtension (C:Matrix V V ℝ) (f:I→V) (w:List I) (x:I→ℝ) :
    rowReflectWord C (w.map f) (rootExtension f x)=
      rootExtension f (rowReflectWord (C.submatrix f f) w x) := by
  induction w with
  | nil=>rfl
  | cons i w ih=>
    change rowReflect C (f i) (rowReflectWord C (w.map f) (rootExtension f x))=_
    rw [ih,rowReflect_rootExtension]
    rfl

lemma rowReflectWord_harmonic (C:Matrix V V ℝ) (w:List V) (p:V→ℝ)
    (hp:∀ i∈w,(C *ᵥ p) i=0) : rowReflectWord C w p=p := by
  induction w with
  | nil=>rfl
  | cons i w ih=>
    change rowReflect C i (rowReflectWord C w p)=p
    rw [ih (fun j hj=>hp j (by simp [hj]))]
    simp only [rowReflect,hp i (by simp),zero_smul,sub_zero]

variable {S:Type*} [Fintype S] [LinearOrder S]

omit [Fintype S] [LinearOrder S] in
lemma sourceRootInclusion_injective (J:Set S) : Function.Injective (sourceRootInclusion J) :=
  fun _ _ h=>Subtype.ext (Sum.inl.inj h)

omit [Fintype S] in
lemma source_folded_submatrix (M:CoxeterMatrix S) (J:Set S) :
    (fusionFoldedCartan (fusionLabelSize M) (coxeterFusionEdge M)).submatrix
      (sourceRootInclusion J) (sourceRootInclusion J)=cartan (restrictedMatrix M J) := by
  have hC : fusionFoldedCartan (fusionLabelSize M) (coxeterFusionEdge M)=framedCartan M := by
    convert fusionFoldedCartan_eq_framedCartan M using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    exact Subsingleton.elim _ _
  rw [hC]
  ext i j
  simp only [Matrix.submatrix_apply,sourceRootInclusion,framedCartan,cartan,restrictedMatrix_apply,
    Subtype.ext_iff]
  congr 1

lemma sourceRoot_word_representation (M:CoxeterMatrix S) (J:Set S) (w:List J) (x:J→ℝ) :
    rowReflectWord (fusionFoldedCartan (fusionLabelSize M) (coxeterFusionEdge M))
      (w.map (sourceRootInclusion J)) (rootExtension (sourceRootInclusion J) x)=
    rootExtension (sourceRootInclusion J)
      (representation (restrictedMatrix M J).toCoxeterSystem
        ((restrictedMatrix M J).toCoxeterSystem.wordProd w) x) := by
  rw [rowReflectWord_rootExtension,source_folded_submatrix,
    rowReflectWord_representation (restrictedMatrix M J).toCoxeterSystem]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CappedReflectedHigh
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "Q" => fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "C" => canonicalFusionLow (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (K:=K)

theorem source_capped_reflected_high (J:Set S) (hJ:IsSpherical M J)
    (u:List J) (hu:(restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (q:ℤ) (x:FiniteHomotopyClass Q (K:=K))
    (hcap:ClassCapOn Q x (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) :
    classTotalVector Q (classLayer Q q (inverseWordAction Q
      (fusionExpandedWord (fusionLabelSize M) (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit))) x))=
    rowReflectWord (unfoldedCartan Q)
      (fusionExpandedWord (fusionLabelSize M) (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit))).reverse
      (classTotalVector Q (classLayer Q q x)-classTotalVector Q
        (C (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)) q (classLayer Q q x))) := by
  let w:=fusionExpandedWord (fusionLabelSize M) (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit))
  rw [inverseWord_capped_layer Q w x (Set.range (unfoldedInclusion M J)) q hcap
    (unfolded_full_word_mem M J u)]
  have lower : ClassLowerBound Q q (classLayer Q q x) :=
    classLowerBound_of_representative Q _ (fun index => le_of_eq index.property.symm)
  have upper : ClassUpperBound Q q (classLayer Q q x) :=
    classUpperBound_of_representative Q _ (fun index => le_of_eq index.property)
  have hp:=sourceCanonicalLow_pure M J hJ u hu q (classLayer Q q x)
    lower upper
  rw [sourceCanonicalLow_eq] at hp ⊢
  exact canonicalLow_reflected_high Q hn w q (classLayer Q q x)
    lower upper hp.1 hp.2

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_NegativePrepend
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "hn" => fusionQuiver_no_loops m d hd hdiag
local notation "P" => fusionWordPacketPerm m d hd hdiag (K:=K)

lemma fusionExpandedInverse_action (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :
    inverseWordAction Q (fusionExpandedWord m w) x=(P (w.map fun s=>(s,true))).symm x := by
  apply (P (w.map fun s=>(s,true))).injective
  rw [Equiv.apply_symm_apply,← fusionExpandedWord_action,positive_inverseWord Q hn]

lemma fusionPacketOrbit_negativePrepend (w:List V) (z:List (V×Bool)) (s:V) (L:FusionLabel m) :
    fusionPacketOrbit m d hd hdiag (negativePrepend w z) s L=
      inverseWordAction Q (fusionExpandedWord m w) (fusionPacketOrbit m d hd hdiag z s L) := by
  simp only [fusionPacketOrbit,negativePrepend,fusionWordPacketPerm_append,fusionWordPacketPerm_inverse]
  rw [fusionExpandedInverse_action]
  rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_RowReflectWordReverse
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest _root_.OAI.HarmonicArtin.unfoldedHom_simple _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V:Type*} [Fintype V] [DecidableEq V]

lemma rowReflectWord_reverse_orthogonal (C:Matrix V V ℝ) (l:List V)
    (hn:l.Nodup) (ho:∀ α∈l,∀ β∈l,α≠β→C α β=0) (x:V→ℝ) :
    rowReflectWord C l.reverse x=rowReflectWord C l x := by
  rw [rowReflectWord_orthogonal C l hn ho,
    rowReflectWord_orthogonal C l.reverse (List.nodup_reverse.mpr hn)
      (by simpa only [List.mem_reverse] using ho)]
  simp only [List.toFinset_reverse]

lemma rowReflect_add (C:Matrix V V ℝ) (α:V) (x y:V→ℝ) :
    rowReflect C α (x+y)=rowReflect C α x+rowReflect C α y := by
  simp only [rowReflect,Matrix.mulVec_add,Pi.add_apply,add_smul]
  module

lemma rowReflectWord_add (C:Matrix V V ℝ) (w:List V) (x y:V→ℝ) :
    rowReflectWord C w (x+y)=rowReflectWord C w x+rowReflectWord C w y := by
  induction w with
  | nil=>rfl
  | cons α w ih=>
    change rowReflect C α (rowReflectWord C w (x+y))=_
    rw [ih,rowReflect_add]
    rfl

lemma rowReflectWord_zero (C:Matrix V V ℝ) (w:List V) : rowReflectWord C w 0=0 := by
  have h:=rowReflectWord_smul C w 0 (0:V→ℝ)
  simpa only [zero_smul] using h

lemma rowReflectWord_sum {F:Type*} (C:Matrix V V ℝ) (w:List V) (t:Finset F) (f:F→V→ℝ) :
    rowReflectWord C w (∑ i∈t,f i)=∑ i∈t,rowReflectWord C w (f i) := by
  induction t using Finset.induction_on with
  | empty=>simp only [Finset.sum_empty,rowReflectWord_zero]
  | @insert i t hi ih=>rw [Finset.sum_insert hi,Finset.sum_insert hi,rowReflectWord_add,ih]

variable {E:Type*} [Fintype E] [DecidableEq E] (m:E→ℕ)

lemma fusion_reverse_reflection_intertwining (hm:∀ e,2 ≤ m e)
    (d:V→V→FusionEdge E) (hdiag:∀ i,d i i=.units 0) (i:V) (p:V→ℝ) :
    rowReflectWord (fusionUnfoldedCartan m d)
      (((Finset.univ:Finset (FusionLabel m)).toList.map (fun L=>(i,L))).reverse)
      (fusionFold m p)=fusionFold m (rowReflect (fusionFoldedCartan m d) i p) := by
  let l:=((Finset.univ:Finset (FusionLabel m)).toList.map (fun L=>(i,L)))
  have hn:l.Nodup:=List.Nodup.map (fun _ _ h=>Prod.mk.inj h |>.2) (Finset.nodup_toList _)
  have ho:∀ α∈l,∀ β∈l,α≠β→fusionUnfoldedCartan m d α β=0 := by
    rintro α hα β hβ hne
    obtain ⟨L,_,rfl⟩:=List.mem_map.mp hα
    obtain ⟨L',_,rfl⟩:=List.mem_map.mp hβ
    simp [fusionUnfoldedCartan,hne,hdiag,FusionEdge.multiplicity]
  rw [rowReflectWord_reverse_orthogonal _ l hn ho]
  exact fusion_reflection_intertwining m hm d hdiag i p

theorem fusion_reverse_word_intertwining (hm:∀ e,2 ≤ m e)
    (d:V→V→FusionEdge E) (hdiag:∀ i,d i i=.units 0) (w:List V) (p:V→ℝ) :
    rowReflectWord (fusionUnfoldedCartan m d) (fusionExpandedWord m w).reverse (fusionFold m p)=
      fusionFold m (rowReflectWord (fusionFoldedCartan m d) w.reverse p) := by
  induction w generalizing p with
  | nil=>rfl
  | cons i w ih=>
    change rowReflectWord (fusionUnfoldedCartan m d)
      ((((Finset.univ:Finset (FusionLabel m)).toList.map (fun L=>(i,L))) ++
        fusionExpandedWord m w).reverse) (fusionFold m p)=_
    rw [List.reverse_append,rowReflectWord_append,fusion_reverse_reflection_intertwining m hm d hdiag,ih,
      List.reverse_cons,rowReflectWord_append]
    rfl

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma fusionFold_sub (x y:V→ℝ) : fusionFold m (x-y)=fusionFold m x-fusionFold m y := by
  ext α
  simp only [fusionFold,Pi.sub_apply,mul_sub]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma fusionFold_injective (hm:∀ e,2 ≤ m e) : Function.Injective (fusionFold (V:=V) m) := by
  intro x y h
  let L:FusionLabel m:=fun e=>⟨0,by have := hm e; omega⟩
  funext v
  have hh:=congrFun h (v,L)
  exact mul_left_cancel₀ (ne_of_gt (fusionWeight_pos m hm L)) hh

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightedReflectedHigh
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "C" => canonicalFusionLow m d hd hdiag (K:=ℂ)
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "σ" => canonicalFusionMultiplicity m d hd hdiag hm

theorem source_weighted_reflected_high (J:Set S) (hJ:IsSpherical M J)
    (u:List J) (hu:(restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ)
    (hcap:∀ L,ClassCapOn Q (O z s L)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) :
    μ (negativePrepend (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)) z) s q=
      rowReflectWord (fusionFoldedCartan m d) (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)).reverse
        (μ z s q-σ (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)) z s q) := by
  let w:=u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)
  let A:=fun L=>classTotalVector Q (classLayer Q q (O z s L))
  let B:=fun L=>classTotalVector Q (C w q (classLayer Q q (O z s L)))
  have hp:∀ L,ClassLowerBound Q q (C w q (classLayer Q q (O z s L))) ∧
      ClassUpperBound Q q (C w q (classLayer Q q (O z s L))) := by
    intro label
    exact sourceCanonicalLow_pure M J hJ u hu q _
      (classLowerBound_of_representative Q _ (fun index => le_of_eq index.property.symm))
      (classUpperBound_of_representative Q _ (fun index => le_of_eq index.property))
  have hA:(∑ L,fusionWeight m L • A L)=fusionFold m (μ z s q) := by
    rw [← fusionOrbitWeightedVector_class,fusionOrbitWeightedVector_eq m d hd hdiag hm]
  have hB:(∑ L,fusionWeight m L • B L)=fusionFold m (σ w z s q) :=
    canonicalFusionMultiplicity_fold m d hd hdiag hm w z s q hp
  apply fusionFold_injective m hm
  calc
    fusionFold m (μ (negativePrepend w z) s q)=
        ∑ L,fusionWeight m L • classTotalVector Q
          (classLayer Q q (inverseWordAction Q (fusionExpandedWord m w) (O z s L))) := by
      rw [← fusionOrbitWeightedVector_eq m d hd hdiag hm,fusionOrbitWeightedVector_class]
      simp only [fusionPacketOrbit_negativePrepend]
      congr 3
      funext L
      congr 9
      exact Subsingleton.elim _ _
    _ = ∑ L,fusionWeight m L • rowReflectWord (unfoldedCartan Q)
        (fusionExpandedWord m w).reverse (A L-B L) := by
      apply Finset.sum_congr rfl
      intro L _
      congr 1
      exact source_capped_reflected_high M J hJ u hu q (O z s L) (hcap L)
    _ = rowReflectWord (unfoldedCartan Q) (fusionExpandedWord m w).reverse
        ((∑ L,fusionWeight m L • A L)-(∑ L,fusionWeight m L • B L)) := by
      rw [← Finset.sum_sub_distrib,rowReflectWord_sum]
      apply Finset.sum_congr rfl
      intro L _
      rw [← smul_sub,rowReflectWord_smul]
    _ = fusionFold m (rowReflectWord (fusionFoldedCartan m d) w.reverse (μ z s q-σ w z s q)) := by
      rw [hA,hB,← fusionFold_sub,fusionQuiver_cartan]
      exact fusion_reverse_word_intertwining m hm d hdiag w _

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_RootInclusionRange
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "σ" => canonicalFusionMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d

omit [Fintype S] [LinearOrder S] in
lemma sourceRootInclusion_range (J:Set S) : Set.range (sourceRootInclusion J)=Sum.inl '' J := by
  ext v
  constructor
  · rintro ⟨j,rfl⟩; exact ⟨j,j.property,rfl⟩
  · rintro ⟨j,hj,rfl⟩; exact ⟨⟨j,hj⟩,rfl⟩

theorem source_chamber_identity (J:Set S) (hJ:IsSpherical M J)
    (u:List J) (hu:(restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) (p:S⊕Unit→ℝ)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (hp:∀ j:J,(C *ᵥ p) (.inl (j:S))=0)
    (hext:∀ v,v∉Sum.inl '' J→μ z s q v=p v) (j:J) :
    μ (negativePrepend (u.map (sourceRootInclusion J)) z) s q (.inl (j:S))-p (.inl (j:S))=
      representation (restrictedMatrix M J).toCoxeterSystem
        ((restrictedMatrix M J).toCoxeterSystem.wordProd u.reverse)
        ((μ z s q-p)∘sourceRootInclusion J-
          (σ (u.map (sourceRootInclusion J)) z s q)∘sourceRootInclusion J) j := by
  let f:=sourceRootInclusion J
  let a:=μ z s q
  let b:=σ (u.map f) z s q
  have hs:∀ v,v∉Sum.inl '' J→b v=0:=sourceCanonicalMultiplicity_support M J hJ u hu z s q
  have hv:∀ v,v∉Set.range f→((a-b)-p) v=0 := by
    intro v hv
    have hn:v∉Sum.inl '' J:=by simpa only [f,sourceRootInclusion_range] using hv
    simp only [Pi.sub_apply,a,hext v hn,hs v hn,sub_zero,sub_self]
  have hfix:rowReflectWord C (u.map f).reverse p=p := by
    apply rowReflectWord_harmonic
    intro v hv
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp (List.mem_reverse.mp hv)
    exact hp i
  have href:μ (negativePrepend (u.map f) z) s q=rowReflectWord C (u.map f).reverse (a-b) := by
    convert source_weighted_reflected_high M J hJ u hu z s q hcap using 1 <;>
      congr 9
  have hvec:μ (negativePrepend (u.map f) z) s q-p=
      rootExtension f (representation (restrictedMatrix M J).toCoxeterSystem
        ((restrictedMatrix M J).toCoxeterSystem.wordProd u.reverse)
        ((a-p)∘f-b∘f)) := by
    conv_lhs => rw [href,← hfix,← rowReflectWord_sub]
    rw [← rootExtension_restrict f (sourceRootInclusion_injective J) ((a-b)-p) hv]
    have he:(((a-b)-p)∘f)=((a-p)∘f-b∘f) := by ext i; simp only [Function.comp_apply,Pi.sub_apply] <;> ring
    rw [he,← List.map_reverse]
    exact sourceRoot_word_representation M J u.reverse _
  have hval:=congrFun hvec (f j)
  rw [rootExtension_apply f (sourceRootInclusion_injective J)] at hval
  exact hval

lemma source_negative_representative (J:Set S) (u:List J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) :
    ∃ g∈artinParabolic M J,
      (∀ L,O (negativePrepend (u.map (sourceRootInclusion J)) z) s L=
        sourceArtinAction M g (O z s L)) ∧
      (∀ L,ClassCapOn Q (O (negativePrepend (u.map (sourceRootInclusion J)) z) s L)
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) := by
  let a:=wordArtin M (u.map Subtype.val)
  have ha:a∈artinParabolic M J:=wordArtin_mem_parabolic M J _
    (by intro i hi;obtain ⟨j,_,rfl⟩:=List.mem_map.mp hi;exact j.property)
  refine ⟨a⁻¹,(artinParabolic M J).inv_mem ha,?_,?_⟩
  · intro L
    rw [fusionPacketOrbit_negativePrepend,sourceArtinAction_negativeWord]
    simp only [List.map_map,Function.comp_def]
    congr 9
    exact Subsingleton.elim _ _
  · intro L
    rw [fusionPacketOrbit_negativePrepend]
    convert inverseWord_capOn Q _ _ _ q (hcap L) (unfolded_full_word_mem M J u) using 1
    all_goals try with_reducible_and_instances rfl
    congr 9
    exact Subsingleton.elim _ _

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_ConvexWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d

omit [Fintype S] [LinearOrder S] in
lemma sourceConvexWord_reverse (J:Set S) (w:(restrictedMatrix M J).Group) :
    (restrictedMatrix M J).toCoxeterSystem.wordProd (sourceConvexWord M J w).reverse=w := by
  rw [CoxeterSystem.wordProd_reverse]
  have h:(restrictedMatrix M J).toCoxeterSystem.wordProd (sourceConvexWord M J w)=w⁻¹:=
    wordCoxeter_reducedExpression _ _
  rw [h,inv_inv]

lemma sourceConvexModel_counts (J:Set S) (hJ:IsSpherical M J) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (w:(restrictedMatrix M J).Group) :
    (∑ L,fusionWeight m L • generatorVector Q (sourceConvexModel M J z s q w L).complex)=
      fusionFold m (sourceConvexVector M J z s q w) := by
  apply canonicalFusionMultiplicity_fold
  intro L
  exact sourceCanonicalLow_pure M J hJ (sourceConvexWord M J w)
    (sourceConvexWord_reduced M J w) q _ (classLayer_lowerBound Q _ q) (classLayer_upperBound Q _ q)

lemma sourceConvexVector_support (J:Set S) (hJ:IsSpherical M J) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (w:(restrictedMatrix M J).Group) :
    ∀ v,v∉Sum.inl '' J→sourceConvexVector M J z s q w v=0 :=
  sourceCanonicalMultiplicity_support M J hJ (sourceConvexWord M J w)
    (sourceConvexWord_reduced M J w) z s q

lemma sourceConvex_representative (J:Set S) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) (p:S⊕Unit→ℝ)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (hp:∀ j:J,(C *ᵥ p) (.inl (j:S))=0)
    (hext:∀ v,v∉Sum.inl '' J→μ z s q v=p v) (w:(restrictedMatrix M J).Group) :
    ∃ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (sourceArtinAction M g (O z s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) ∧
      (∀ j:J,fusionFamilyMultiplicity m d hd hm (fun L=>sourceArtinAction M g (O z s L)) q (.inl (j:S))-
        p (.inl (j:S))=representation (restrictedMatrix M J).toCoxeterSystem w
          ((μ z s q-p)∘sourceRootInclusion J-(sourceConvexVector M J z s q w)∘sourceRootInclusion J) j) := by
  obtain ⟨g,hg,he,hc⟩:=source_negative_representative M J (sourceConvexWord M J w) z s q hcap
  have he':(fun L=>sourceArtinAction M g (O z s L))=
      O (negativePrepend ((sourceConvexWord M J w).map (sourceRootInclusion J)) z) s :=
    funext (fun L=>(he L).symm)
  refine ⟨g,hg,fun L=>he L ▸ hc L,?_⟩
  intro j
  rw [he',fusionFamilyMultiplicity_orbit]
  have h:=source_chamber_identity M J hJ (sourceConvexWord M J w)
    (sourceConvexWord_reduced M J w) z s q p hcap hp hext j
  rw [sourceConvexWord_reverse] at h
  exact h

theorem source_convex_subobjects_interior (J:Set S) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) (p:S⊕Unit→ℝ)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (hp:∀ j:J,(C *ᵥ p) (.inl (j:S))=0)
    (hext:∀ v,v∉Sum.inl '' J→μ z s q v=p v)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (sourceArtinAction M g (O z s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,p (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>sourceArtinAction M g (O z s L)) q (.inl (j:S))) :
    ((μ z s q-p)∘sourceRootInclusion J)∈interior (convexHull ℝ
      (Set.range fun w=>(sourceConvexVector M J z s q w)∘sourceRootInclusion J)) := by
  let : Finite (restrictedMatrix M J).Group := restricted_finite M J hJ
  let := Fintype.ofFinite (restrictedMatrix M J).Group
  apply chamber_inequalities_interior (restrictedMatrix M J).toCoxeterSystem
  intro w j
  obtain ⟨g,hg,hc,he⟩:=sourceConvex_representative M J hJ z s q p hcap hp hext w
  rw [← he j]
  exact sub_pos.mpr (huniv g hg hc j)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_InteriorConvexHullReindex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

lemma interior_convexHull_reindex {I J B:Type*} (e:I≃J) (v:J→ℝ) (f:B→J→ℝ)
    (h:(v∘e)∈interior (convexHull ℝ (Set.range fun b=>(f b)∘e))) :
    v∈interior (convexHull ℝ (Set.range f)) := by
  let E:=ContinuousLinearEquiv.piCongrLeft ℝ (fun _:J=>ℝ) e
  have hmap (g:J→ℝ):E (g∘e)=g := by
    exact E.apply_symm_apply g
  have hr:E '' (Set.range fun b=>(f b)∘e)=Set.range f := by
    ext x
    constructor
    · rintro ⟨_,⟨b,rfl⟩,rfl⟩
      exact ⟨b,(hmap (f b)).symm⟩
    · rintro ⟨b,rfl⟩
      exact ⟨(f b)∘e,⟨b,rfl⟩,hmap (f b)⟩
  have hh:E (v∘e)∈E '' interior (convexHull ℝ (Set.range fun b=>(f b)∘e)) := by
    exact ⟨v∘e,h,rfl⟩
  have hi:=E.toHomeomorph.image_interior (convexHull ℝ (Set.range fun b=>(f b)∘e))
  change E '' interior (convexHull ℝ (Set.range fun b=>(f b)∘e))=
    interior (E '' convexHull ℝ (Set.range fun b=>(f b)∘e)) at hi
  have hc:=E.toLinearMap.image_convexHull (Set.range fun b=>(f b)∘e)
  change E '' convexHull ℝ (Set.range fun b=>(f b)∘e)=
    convexHull ℝ (E '' (Set.range fun b=>(f b)∘e)) at hc
  rw [hi,hc,hr,hmap] at hh
  exact hh

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_FusionWeightedHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag

theorem fusionOrbit_summand_middle (w:List (V × Bool)) (s:V)
    (L H:FusionLabel m) {T:Type*} [Fintype T] (M:BasedComplex Q (K:=ℂ) T)
    (q k:ℤ) (ι:Map Q M (Y w s L q)) (π:Map Q (Y w s L q) M)
    (hret:ι.matrix*π.matrix=projectiveIdentity Q M.placement) :
    totalHomDimension Q M (Y w s H k) (k-q+1)=0 := by
  apply Nat.eq_zero_of_le_zero
  have h:=totalHomDimension_retract_source Q M (Y w s L q) (Y w s H k) ι π hret (k-q+1)
  rwa [fusionOrbitLayer_middle] at h

lemma fusionWeightedHom_nonneg (hm:∀ e,2 ≤ m e) {T R:FusionLabel m → Type*}
    [∀ L,Fintype (T L)] [∀ H,Fintype (R H)]
    (P:∀ L,BasedComplex Q (K:=ℂ) (T L)) (F:∀ H,BasedComplex Q (K:=ℂ) (R H)) (t:ℤ) :
    0≤fusionWeightedHom m d hd P F t := by
  apply Finset.sum_nonneg
  intro L _
  apply Finset.sum_nonneg
  intro H _
  exact mul_nonneg (mul_pos (fusionWeight_pos m hm L) (fusionWeight_pos m hm H)).le (Nat.cast_nonneg _)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionColorRegion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag

lemma fusionOrbitColor_generator (w:List (V × Bool)) (s:V) (q:ℤ) (U:Set V)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U))
    (L:FusionLabel m) (a:FusionVertex (V:=V) m) :
    generatorVector Q (fusionOrbitColorLayer m d hd hdiag w s q U hb L) a=
      if a.1∈U then generatorVector Q (Y w s L q) a else 0 := by
  exact colorRestriction_generatorVector Q (Y w s L q) (fusionColorRegion m U)
    (fun i=>i.property) (hb L) a

lemma fusionOrbitColor_weightedVector (hm:∀ e,2 ≤ m e)
    (w:List (V × Bool)) (s:V) (q:ℤ) (U:Set V)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U)) :
    (∑ L,fusionWeight m L • generatorVector Q (fusionOrbitColorLayer m d hd hdiag w s q U hb L))=
      fusionFold m (fusionOrbitColorMultiplicity m d hd hdiag hm w s q U) := by
  funext a
  have h:=congrFun (fusionOrbitWeightedVector_eq m d hd hdiag hm w s q) a
  simp only [fusionOrbitWeightedVector,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at h ⊢
  simp_rw [fusionOrbitColor_generator]
  by_cases ha:a.1∈U
  · simp only [ha,ite_true, if_true]
    simpa only [fusionFold,fusionOrbitColorMultiplicity,ha,ite_true, if_true] using h
  · simp only [ha,ite_false, if_false,MulZeroClass.mul_zero,
      Finset.sum_const_zero,fusionFold,fusionOrbitColorMultiplicity]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_DimensionNonneg
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "C" => fusionFoldedCartan m d

include hm in
lemma FusionEdge.dimension_nonneg (b:FusionEdge E) : 0≤b.dimension m := by
  let L:FusionLabel m:=fun e=>⟨0,by have:=hm e; omega⟩
  have hs:0≤∑ H,(b.multiplicity m L H:ℝ)*fusionWeight m H :=
    Finset.sum_nonneg (fun H _=>mul_nonneg (Nat.cast_nonneg _) (fusionWeight_pos m hm H).le)
  rw [FusionEdge.dimension_identity m hm] at hs
  exact nonneg_of_mul_nonneg_left hs (fusionWeight_pos m hm L)

include hm in
omit [Fintype V] in
lemma fusionFoldedCartan_off_nonpos (s t:V) (hst:s≠t) : C s t≤0 := by
  simp only [fusionFoldedCartan,Matrix.sub_apply,Matrix.diagonal_apply,Matrix.of_apply,
    ite_eq_right hst,zero_sub]
  exact neg_nonpos.mpr (FusionEdge.dimension_nonneg m hm (d s t))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionSubobjectCartanInequality
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "C" => fusionFoldedCartan m d

include hm in

lemma fusion_subobject_cartan_inequality
    {T R U:FusionLabel m → Type} [∀ L,Fintype (T L)] [∀ L,Fintype (R L)] [∀ L,Fintype (U L)]
    (M:∀ L,BasedComplex Q (K:=ℂ) (T L)) (S:∀ L,BasedComplex Q (K:=ℂ) (R L))
    (F:∀ L,BasedComplex Q (K:=ℂ) (U L)) (q k:ℤ)
    (hM:∀ L i,((M L).placement i).level=q) (hS:∀ L i,((S L).placement i).level=q)
    (hF:∀ L i,((F L).placement i).level=k)
    (incl:∀ L,TermwiseSplitInjection Q (S L) (M L)) (J:Set V)
    (hsupp:∀ L i,((S L).placement i).color.1∈J)
    (hsoc:∀ H α,α.1∈J → ∀ r,coefficientSocle Q (F H) α r=⊥)
    (hmid:∀ L H,totalHomDimension Q (M L) (F H) (k-q+1)=0) :
    fusionWeightedHom m d hd M F (k-q) ≤
      ((∑ L,fusionWeight m L • generatorVector Q (M L))-
       (∑ L,fusionWeight m L • generatorVector Q (S L))) ⬝ᵥ
        (unfoldedCartan Q *ᵥ (∑ H,fusionWeight m H • generatorVector Q (F H))) := by
  have he : ((∑ L,fusionWeight m L • generatorVector Q (M L))-
       (∑ L,fusionWeight m L • generatorVector Q (S L))) =
      ∑ L,fusionWeight m L • (generatorVector Q (M L)-generatorVector Q (S L)) := by
    simp only [smul_sub,Finset.sum_sub_distrib]
  rw [he,finite_weighted_cartan]
  unfold fusionWeightedHom
  apply Finset.sum_le_sum
  intro L _
  apply Finset.sum_le_sum
  intro H _
  apply mul_le_mul_of_nonneg_left _ (mul_pos (fusionWeight_pos m hm L) (fusionWeight_pos m hm H)).le
  exact subobject_cartan_inequality Q (M L) (S L) (F H) (hM L) (hS L) (hF H)
    (incl L) {α|α.1∈J} (hsupp L) (hsoc H) (hmid L H)

lemma fusion_weighted_euler_of_middle_zero
    {T R:FusionLabel m → Type} [∀ L,Fintype (T L)] [∀ L,Fintype (R L)]
    (M:∀ L,BasedComplex Q (K:=ℂ) (T L)) (F:∀ L,BasedComplex Q (K:=ℂ) (R L)) (q k:ℤ)
    (hM:∀ L i,((M L).placement i).level=q) (hF:∀ L i,((F L).placement i).level=k)
    (hmid:∀ L H,totalHomDimension Q (M L) (F H) (k-q+1)=0) :
    (∑ L,fusionWeight m L • generatorVector Q (M L)) ⬝ᵥ
      (unfoldedCartan Q *ᵥ (∑ H,fusionWeight m H • generatorVector Q (F H))) =
      fusionWeightedHom m d hd M F (k-q)+fusionWeightedHom m d hd F M (q-k) := by
  rw [finite_weighted_cartan]
  have he (L H:FusionLabel m) := pure_cartan_euler Q (M L) (F H) (hM L) (hF H)
  simp only [hmid,Nat.cast_zero,sub_zero] at he
  simp_rw [he]
  simp only [_root_.mul_add,Finset.sum_add_distrib,fusionWeightedHom]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro L _
  apply Finset.sum_congr rfl
  intro H _
  rw [mul_comm (fusionWeight m H) (fusionWeight m L)]

theorem fusionOrbit_subobject_null_separation
    (w:List (V × Bool)) (s:V) {T:FusionLabel m → Type} [∀ L,Fintype (T L)]
    (M:∀ L,BasedComplex Q (K:=ℂ) (T L)) (q k:ℤ)
    (hM:∀ L i,((M L).placement i).level=q)
    (ι:∀ L,Map Q (M L) (Y w s L q)) (π:∀ L,Map Q (Y w s L q) (M L))
    (hret:∀ L,(ι L).matrix*(π L).matrix=projectiveIdentity Q (M L).placement)
    {B:Type} {R:B → FusionLabel m → Type} [∀ b L,Fintype (R b L)]
    (S:∀ b L,BasedComplex Q (K:=ℂ) (R b L))
    (hS:∀ b L i,((S b L).placement i).level=q)
    (incl:∀ b L,TermwiseSplitInjection Q (S b L) (M L))
    (I J:Set V) (c a:V → ℝ) (σ:B → V → ℝ)
    (hmvec:(∑ L,fusionWeight m L • generatorVector Q (M L))=fusionFold m a)
    (hsvec:∀ b,(∑ L,fusionWeight m L • generatorVector Q (S b L))=fusionFold m (σ b))
    (hsupp:∀ b L i,((S b L).placement i).color.1∈J)
    (hσ:∀ b v,v∉J → σ b v=0)
    (hc:∀ v,0 ≤ c v) (hcSupp:∀ v,v∉I → c v=0) (hcPos:∀ v,v∈I → 0 < c v)
    (hcNull:∀ v,v∈I → (C *ᵥ c) v=0) (hext:∀ v,v∉J → a v=c v)
    (hint:(fun j:J=>a j-c j)∈interior (convexHull ℝ (Set.range fun b:B=>(fun j:J=>σ b j))))
    (hsoc:∀ H α,α.1∈J → ∀ r,coefficientSocle Q (Y w s H k) α r=⊥) :
    (∀ v∉I,(∃ u∈I,C v u<0) → fusionOrbitMultiplicity m d hd hdiag hm w s k v=0) ∧
    (∀ j∈J,(C *ᵥ fusionOrbitMultiplicity m d hd hdiag hm w s k) j=0) ∧
    fusionWeightedHom m d hd M (fun H=>Y w s H k) (k-q)=0 ∧
    fusionWeightedHom m d hd (fun H=>Y w s H k) M (q-k)=0 := by
  let y := fusionOrbitMultiplicity m d hd hdiag hm w s k
  let F := fun H=>Y w s H k
  let H₀ := fusionWeightedHom m d hd M F (k-q)
  have hF : ∀ H i,((F H).placement i).level=k := by
    intro H i
    exact i.property
  have hmid : ∀ L H,totalHomDimension Q (M L) (F H) (k-q+1)=0 := by
    intro L H
    exact fusionOrbit_summand_middle m d hd hdiag w s L H (M L) q k (ι L) (π L) (hret L)
  have hyvec : (∑ H,fusionWeight m H • generatorVector Q (F H))=fusionFold m y :=
    fusionOrbitWeightedVector_eq m d hd hdiag hm w s k
  have hD := fusionD0_pos m hm
  have hbound : ∀ b,H₀ ≤ fusionD0 m*((a-σ b) ⬝ᵥ (C *ᵥ y)) := by
    intro b
    have h := fusion_subobject_cartan_inequality m d hd hm M (S b) F q k hM (hS b) hF
      (incl b) J (hsupp b) hsoc hmid
    rw [hmvec,hsvec b,hyvec] at h
    have he : fusionFold m a-fusionFold m (σ b)=fusionFold m (a-σ b) := by
      ext α
      simp only [fusionFold,Pi.sub_apply,mul_sub]
    rw [he,fusionQuiver_cartan,fusion_pairing m hm] at h
    exact h
  have hb : ∀ z∈(Set.range fun b:B=>(fun j:J=>σ b j)),
      H₀/fusionD0 m ≤ (a-NullBoundary.extend J z) ⬝ᵥ (C *ᵥ y) := by
    rintro _ ⟨b,rfl⟩
    rw [NullBoundary.extend_restrict J (σ b) (hσ b)]
    exact (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using hbound b)
  have hsep := NullBoundary.convex_null_boundary_separation C I J c a y
    (Set.range fun b:B=>(fun j:J=>σ b j)) (H₀/fusionD0 m)
    (fusionFoldedCartan_symm m d hd) (fusionFoldedCartan_off_nonpos m d hm)
    hc hcSupp hcPos hcNull (fusionOrbitMultiplicity_nonneg m d hd hdiag hm w s k)
    hext hint (div_nonneg (fusionWeightedHom_nonneg m d hd hm M F (k-q)) hD.le) hb
  have hzero : H₀=0 := (div_eq_zero_iff.mp hsep.2.2.1).resolve_right (ne_of_gt hD)
  refine ⟨hsep.1,hsep.2.1,hzero,?_⟩
  have he := fusion_weighted_euler_of_middle_zero m d hd M F q k hM hF hmid
  rw [hmvec,hyvec,fusionQuiver_cartan,fusion_pairing m hm,hsep.2.2.2,MulZeroClass.mul_zero] at he
  change 0=H₀+_ at he
  simpa only [hzero,zero_add] using he.symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionOrbitColorSubobject
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "C" => fusionFoldedCartan m d
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "a" => fusionOrbitColorMultiplicity m d hd hdiag hm

theorem fusionOrbitColor_subobject_separation
    (w:List (V×Bool)) (s:V) (q k:ℤ) (I J:Set V)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m I))
    {B:Type} {R:B→FusionLabel m→Type} [∀ b L,Fintype (R b L)]
    (T:∀ b L,BasedComplex Q (K:=ℂ) (R b L))
    (hT:∀ b L i,((T b L).placement i).level=q)
    (incl:∀ b L,TermwiseSplitInjection Q (T b L)
      (fusionOrbitColorLayer m d hd hdiag w s q I hb L))
    (c:V→ℝ) (σ:B→V→ℝ)
    (hsvec:∀ b,(∑ L,fusionWeight m L • generatorVector Q (T b L))=fusionFold m (σ b))
    (hsupp:∀ b L i,((T b L).placement i).color.1∈J)
    (hσ:∀ b v,v∉J→σ b v=0)
    (hc:∀ v,0 ≤ c v) (hcSupp:∀ v,v∉I→c v=0) (hcPos:∀ v,v∈I→0 < c v)
    (hcNull:∀ v,v∈I→(C *ᵥ c) v=0) (hext:∀ v,v∉J→a w s q I v=c v)
    (hint:(fun j:J=>a w s q I j-c j)∈interior (convexHull ℝ (Set.range fun b:B=>(fun j:J=>σ b j))))
    (hsoc:∀ H α,α.1∈J→∀ r,coefficientSocle Q (Y w s H k) α r=⊥) :
    (∀ v∉I,(∃ u∈I,C v u<0)→μ w s k v=0) ∧
    (∀ j∈J,(C *ᵥ μ w s k) j=0) ∧
    fusionWeightedHom m d hd (fun L=>fusionOrbitColorLayer m d hd hdiag w s q I hb L)
      (fun H=>Y w s H k) (k-q)=0 ∧
    fusionWeightedHom m d hd (fun H=>Y w s H k)
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q I hb L) (q-k)=0 := by
  let T₀:=fun L=>fusionOrbitColorLayer m d hd hdiag w s q I hb L
  let incl₀ L:=blockInclusionMap Q (Y w s L q) _
    (pure_color_block Q _ _ (fun i=>i.property) (hb L))
  let proj₀ L:=blockProjectionMap Q (Y w s L q) _
    (pure_color_block Q _ _ (fun i=>i.property) (hb L))
  have hret:∀ L,(incl₀ L).matrix*(proj₀ L).matrix=projectiveIdentity Q (T₀ L).placement := by
    intro L
    convert block_inclusion_projection Q (Y w s L q)
      {i | ((Y w s L q).placement i).color∈fusionColorRegion m I} using 1
    · rfl
    · apply Matrix.ext
      intro i j
      simp only [projectiveIdentity,Matrix.diagonal_apply]
      by_cases h:i=j <;> simp only [h,ite_true, if_true,ite_false, if_false]
      rfl
  exact fusionOrbit_subobject_null_separation m d hd hdiag hm w s T₀ q k
    (fun L i=>i.val.property) incl₀ proj₀
    (fun L=>by
      convert hret L using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1)
      exact Subsingleton.elim _ _)
    T hT incl I J c (a w s q I) σ
    (fusionOrbitColor_weightedVector m d hd hdiag hm w s q I hb)
    hsvec hsupp hσ hc hcSupp hcPos hcNull hext hint hsoc

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_NullPatch
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix

attribute [local instance] Classical.propDecidable
variable {V:Type*}

lemma null_patch [Fintype V] {C:Matrix V V ℝ} (hsym:∀ i j,C i j=C j i)
    (hoff:∀ i j,i≠j→C i j≤0) (I J:Set V) (hJI:J⊆I) (c μ:V→ℝ)
    (hc:∀ i∈I,(C *ᵥ c) i=0)
    (hext:∀ v,(v∈I ∧ v∉J) ∨ (v∉I ∧ ∃ u∈I,C v u<0)→μ v=c v) :
    ∀ j∈J,(C *ᵥ (fun v=>if v∈J then c v else μ v)) j=0 := by
  intro j hj
  rw [← hc j (hJI hj)]
  apply Finset.sum_congr rfl
  intro v _
  change C j v*(if v∈J then c v else μ v)=C j v*c v
  by_cases hv:v∈J
  · rw [ite_eq_left hv]
  · rw [ite_eq_right hv]
    by_cases hi:v∈I
    · rw [hext v (Or.inl ⟨hi,hv⟩)]
    · by_cases hn:C v j<0
      · rw [hext v (Or.inr ⟨hi,j,hJI hj,hn⟩)]
      · have hn':C v j=0:=le_antisymm (hoff v j (fun he=>hi (he ▸ hJI hj))) (le_of_not_gt hn)
        rw [hsym j v,hn',zero_mul,zero_mul]

lemma color_region_exterior (I J:Set V) (c μ:V→ℝ)
    (hc:∀ v,v∉I→c v=0) (hext:∀ v,v∈I→v∉J→μ v=c v) :
    ∀ v,v∉J→(if v∈I then μ v else 0)=c v := by
  intro v hv
  by_cases hi:v∈I
  · rw [ite_eq_left hi,hext v hi hv]
  · rw [ite_eq_right hi,hc v hi]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_IsolatedBoundaryAbsent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "a" => fusionOrbitColorMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d

theorem source_isolated_interior (I J:Set S) (hJI:J⊆I) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) (c:S⊕Unit→ℝ)
    (hcNull:∀ v,v∈Sum.inl '' I→(C *ᵥ c) v=0)
    (hdata:∀ v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' J) ∨
      (v∉Sum.inl '' I ∧ ∃ u∈Sum.inl '' I,C v u<0)→μ z s q v=c v)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (sourceArtinAction M g (O z s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,c (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>sourceArtinAction M g (O z s L)) q (.inl (j:S))) :
    (fun j:(Sum.inl '' J:Set (S⊕Unit))=>a z s q (Sum.inl '' I) j-c j)∈
      interior (convexHull ℝ (Set.range fun w:(restrictedMatrix M J).Group=>
        (fun j:(Sum.inl '' J:Set (S⊕Unit))=>sourceConvexVector M J z s q w j))) := by
  let p:S⊕Unit→ℝ:=fun v=>if v∈Sum.inl '' J then c v else μ z s q v
  have hi:(Sum.inl '' J:Set (S⊕Unit))⊆Sum.inl '' I := Set.image_mono hJI
  have hp:∀ j:J,(C *ᵥ p) (.inl (j:S))=0 := by
    intro j
    apply null_patch (fusionFoldedCartan_symm m d hd) (fusionFoldedCartan_off_nonpos m d hm)
      (Sum.inl '' I) (Sum.inl '' J) hi c (μ z s q) hcNull hdata
    exact ⟨j,j.property,rfl⟩
  have hext:∀ v,v∉Sum.inl '' J→μ z s q v=p v := by
    intro v hv
    exact (ite_eq_right hv).symm
  have hpj (j:J):p (.inl (j:S))=c (.inl (j:S)):=ite_eq_left ⟨j,j.property,rfl⟩
  have hh:=source_convex_subobjects_interior M J hJ z s q p hcap hp hext
    (fun g hg hgc j=>by rw [hpj]; exact huniv g hg hgc j)
  let e:J≃(Sum.inl '' J:Set (S⊕Unit)):=Equiv.Set.image Sum.inl J Sum.inl_injective
  have hv : (fun j:(Sum.inl '' J:Set (S⊕Unit))=>a z s q (Sum.inl '' I) j-c j)∘e =
      (μ z s q-p)∘sourceRootInclusion J := by
    funext j
    change (if Sum.inl (j:S)∈Sum.inl '' I then μ z s q (.inl (j:S)) else 0)-c (.inl (j:S))=
      μ z s q (.inl (j:S))-p (.inl (j:S))
    rw [ite_eq_left ⟨j,hJI j.property,rfl⟩,hpj]
  apply interior_convexHull_reindex e
  rw [hv]
  exact hh

theorem source_isolated_separation (I J:Set S) (hJI:J⊆I) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q k:ℤ) (c:S⊕Unit→ℝ)
    (hc:∀ v,0 ≤ c v) (hcSupp:∀ v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀ v,v∈Sum.inl '' I→0 < c v)
    (hcNull:∀ v,v∈Sum.inl '' I→(C *ᵥ c) v=0)
    (hdata:∀ v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' J) ∨
      (v∉Sum.inl '' I ∧ ∃ u∈Sum.inl '' I,C v u<0)→μ z s q v=c v)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (sourceArtinAction M g (O z s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,c (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>sourceArtinAction M g (O z s L)) q (.inl (j:S)))
    (hsoc:∀ H α,α.1∈Sum.inl '' J→∀ r,coefficientSocle Q (Y z s H k) α r=⊥) :
    let hb:=source_isolated_boundary_absent M I J z s q c hcSupp hdata
    (∀ v∉Sum.inl '' I,(∃ u∈Sum.inl '' I,C v u<0)→μ z s k v=0) ∧
    (∀ j∈Sum.inl '' J,(C *ᵥ μ z s k) j=0) ∧
    fusionWeightedHom m d hd (fun L=>fusionOrbitColorLayer m d hd hdiag z s q (Sum.inl '' I) hb L)
      (fun H=>Y z s H k) (k-q)=0 ∧
    fusionWeightedHom m d hd (fun H=>Y z s H k)
      (fun L=>fusionOrbitColorLayer m d hd hdiag z s q (Sum.inl '' I) hb L) (q-k)=0 := by
  dsimp only
  apply fusionOrbitColor_subobject_separation m d hd hdiag hm z s q k
    (Sum.inl '' I) (Sum.inl '' J) (source_isolated_boundary_absent M I J z s q c hcSupp hdata)
    (fun w L=>(sourceConvexModel M J z s q w L).complex)
    (sourceConvexModel_pure M J hJ z s q)
    (fun w L=>by
      convert sourceConvexRegionInclusion M I J hJI hJ z s q
        (source_isolated_boundary_absent M I J z s q c hcSupp hdata) w L using 1)
    c (sourceConvexVector M J z s q)
    (sourceConvexModel_counts M J hJ z s q)
  · intro w L i
    obtain ⟨v,hv⟩:=sourceConvexModel_support M J z s q w L i
    rw [← hv]
    exact ⟨v.1,v.1.property,rfl⟩
  · exact sourceConvexVector_support M J hJ z s q
  · exact hc
  · exact hcSupp
  · exact hcPos
  · exact hcNull
  · exact color_region_exterior (Sum.inl '' I) (Sum.inl '' J) c (μ z s q)
      hcSupp (fun v hv hj=>hdata v (Or.inl ⟨hv,hj⟩))
  · exact source_isolated_interior M I J hJI hJ z s q c hcNull hdata hcap huniv
  · exact hsoc

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnfoldedInclusionRange
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M

omit [Fintype S] in
lemma unfoldedInclusion_range (J:Set S) :
    Set.range (unfoldedInclusion M J)=fusionColorRegion m (Sum.inl '' J) := by
  ext α
  rcases α with ⟨v,L⟩
  constructor
  · rintro ⟨⟨j,H⟩,he⟩
    change (Sum.inl (j:S),H)=(v,L) at he
    obtain ⟨rfl,rfl⟩:=Prod.mk.inj he
    exact ⟨j,j.property,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    exact ⟨(⟨j,hj⟩,L),rfl⟩

lemma closedNeighborhood_mono {V A:Type} (R:ReversibleQuiver V A)
    {U T:Set V} (h:U⊆T) : R.closedNeighborhood U⊆R.closedNeighborhood T := by
  rintro α (hα|⟨β,hβ,a,hs,ht⟩)
  · exact Or.inl (h hα)
  · exact Or.inr ⟨β,h hβ,a,hs,ht⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_IsolatedIterationData
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d

namespace IsolatedIterationData
variable {M} (D:IsolatedIterationData M)

lemma capJ (z:List ((S⊕Unit)×Bool)) (hc:D.capped z) :
    ∀ L,ClassCapOn Q (O z D.s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M D.J))) D.q := by
  intro L
  apply (hc L).mono
  apply closedNeighborhood_mono
  rw [unfoldedInclusion_range]
  exact fun α hα=>Set.image_mono D.hJI hα

lemma separation_oai (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
    (k:ℤ) (hs:D.openSocle z k) :
    (∀ v∉Sum.inl '' D.I,(∃ u∈Sum.inl '' D.I,C v u<0)→μ z D.s k v=0) ∧
    (∀ j∈Sum.inl '' D.J,(C *ᵥ μ z D.s k) j=0) ∧
    fusionWeightedHom m d hd (D.fullRegion z hz) (fun H=>Y z D.s H k) (k-D.q)=0 ∧
    fusionWeightedHom m d hd (fun H=>Y z D.s H k) (D.fullRegion z hz) (D.q-k)=0 := by
  apply source_isolated_separation M D.I D.J D.hJI D.hJ z D.s D.q k D.c
    D.hc D.hcSupp D.hcPos D.hcNull (D.data z hz) (D.capJ z hc) (D.strict z hz)
  intro H α hα r
  exact Submodule.finrank_eq_zero.mp (hs H α hα r)

end IsolatedIterationData
end HarmonicArtin

end OAI
end

theorem solution : type_of% @OAI.HarmonicArtin.IsolatedIterationData.separation_oai := @OAI.HarmonicArtin.IsolatedIterationData.separation_oai
