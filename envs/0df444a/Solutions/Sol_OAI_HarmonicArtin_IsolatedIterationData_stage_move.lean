-- Prove2me | solution 1 for OAI.HarmonicArtin.IsolatedIterationData.stage_move
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:57:37.221084+00:00
-- url     : https://prove2.me/submissions/79ab2750-da3e-4591-8b42-94e313dfd971

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag013
import Theorems.Thm_OAI_HarmonicArtin_IsolatedIterationData_separation

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_BottomScalarCycleInjective
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem bottom_scalar_cycle_injective
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (e:HomotopyEquivalence Q E F) (α:V) {l:ℤ}
    (hcolor:∀ i,(E.placement i).color=α)
    (hE:∀ i,l≤(E.placement i).level)
    (x:I→K) (hs:∀ i,(E.placement i).level≠l → x i=0)
    (hx:Matrix.vecMul x (E.differential.map (vertexHom Q α))=0)
    (hxf:Matrix.vecMul x (e.forward.matrix.map (vertexHom Q α))=0) : x=0 := by
  have hxh:Matrix.vecMul x (e.sourceHomotopy.map (vertexHom Q α))=0 := by
    funext j
    apply Finset.sum_eq_zero
    intro i hi
    change x i * (e.sourceHomotopy i j).vertex α = 0
    by_cases hxi:x i=0
    · rw [hxi,MulZeroClass.zero_mul]
    by_cases hm:(e.sourceHomotopy i j).vertex α=0
    · exact mul_eq_zero.mpr (Or.inr hm)
    have hp: (E.placement i).level=l := Classical.not_not.mp (fun h=>hxi (hs i h))
    obtain ⟨_,_,hc,hu⟩:=degree_vertex_support Q e.sourceEntries e.sourceDegree i j α hm
    have hh:=hE j
    dsimp only [GeneratorPlacement.level] at hp hh
    omega
  have hid:(projectiveIdentity Q (K:=K) E.placement).map (vertexHom Q α)=1 := by
    apply Matrix.ext
    intro i j
    by_cases he:i=j
    · subst j
      simp only [Matrix.one_apply,Matrix.map_apply,projectiveIdentity,Matrix.diagonal_apply]
      change (vertexId Q (K:=K) (E.placement i).color).vertex α = 1
      simp [hcolor i,vertexId_eval]
    · simp [projectiveIdentity,Matrix.map_apply,he,vertexHom]
  have he:=congrArg (fun M:Matrix I I (Q.Zigzag K)=>M.map (vertexHom Q α)) e.sourceEquation
  simp only [Matrix.map_mul,Matrix.map_add _ (map_add _),hid] at he
  have he':=congrArg (Matrix.vecMul x) he
  simp only [Matrix.vecMul_add,← Matrix.vecMul_vecMul,hxf,hx,hxh,
    Matrix.zero_vecMul,Matrix.vecMul_one,add_zero] at he'
  exact he'.symm

theorem bottom_scalar_cycle_transport
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (e:HomotopyEquivalence Q E F) (α:V) {l c:ℤ}
    (hcolor:∀ i,(E.placement i).color=α)
    (hE:∀ i,l≤(E.placement i).level)
    (hF:∀ y:J→K,
      (∀ j,¬ ((F.placement j).level=l ∧ (F.placement j).cochain=c)→y j=0)→
      Matrix.vecMul y (F.differential.map (vertexHom Q α))=0→y=0)
    (x:I→K) (hs:∀ i,¬ ((E.placement i).level=l ∧ (E.placement i).cochain=c)→x i=0)
    (hx:Matrix.vecMul x (E.differential.map (vertexHom Q α))=0) : x=0 := by
  apply bottom_scalar_cycle_injective Q E F e α hcolor hE x
    (fun i hi=>hs i (fun h=>hi h.1)) hx
  apply hF
  · intro j hj
    apply Finset.sum_eq_zero
    intro i hi
    change x i * (e.forward.matrix i j).vertex α=0
    by_cases hx0:x i=0
    · rw [hx0,MulZeroClass.zero_mul]
    by_cases hm:(e.forward.matrix i j).vertex α=0
    · rw [hm,MulZeroClass.mul_zero]
    have hp:= (reduction_support Q e.forward.entries e.forward.degree i j α hm).1
    have hi':(E.placement i).level=l ∧ (E.placement i).cochain=c :=
      Classical.not_not.mp (fun h=>hx0 (hs i h))
    exact (hj (by simpa only [← hp] using hi')).elim
  · have hc:=congrArg (fun M:Matrix I J (Q.Zigzag K)=>M.map (vertexHom Q α)) e.forward.commute
    simp only [Matrix.map_mul] at hc
    rw [Matrix.vecMul_vecMul,← hc,← Matrix.vecMul_vecMul,hx,Matrix.zero_vecMul]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_BottomScalarCycleZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem bottom_scalar_cycle_zero
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (e:HomotopyEquivalence Q E F) (α:V) {l:ℤ}
    (hcolor:∀ i,(E.placement i).color=α)
    (hE:∀ i,l≤(E.placement i).level) (hF:∀ j,l<(F.placement j).level)
    (x:I→K) (hs:∀ i,(E.placement i).level≠l → x i=0)
    (hx:Matrix.vecMul x (E.differential.map (vertexHom Q α))=0) : x=0 := by
  have hxf:Matrix.vecMul x (e.forward.matrix.map (vertexHom Q α))=0 := by
    funext j
    apply Finset.sum_eq_zero
    intro i hi
    change x i * (e.forward.matrix i j).vertex α = 0
    by_cases hxi:x i=0
    · rw [hxi,MulZeroClass.zero_mul]
    by_cases hm:(e.forward.matrix i j).vertex α=0
    · exact mul_eq_zero.mpr (Or.inr hm)
    have hp: (E.placement i).level=l := Classical.not_not.mp (fun h=>hxi (hs i h))
    have he:=congrArg GeneratorPlacement.level (reduction_support Q e.forward.entries e.forward.degree i j α hm).1
    have hh:=hF j
    omega
  have hxh:Matrix.vecMul x (e.sourceHomotopy.map (vertexHom Q α))=0 := by
    funext j
    apply Finset.sum_eq_zero
    intro i hi
    change x i * (e.sourceHomotopy i j).vertex α = 0
    by_cases hxi:x i=0
    · rw [hxi,MulZeroClass.zero_mul]
    by_cases hm:(e.sourceHomotopy i j).vertex α=0
    · exact mul_eq_zero.mpr (Or.inr hm)
    have hp: (E.placement i).level=l := Classical.not_not.mp (fun h=>hxi (hs i h))
    obtain ⟨_,_,hc,hu⟩:=degree_vertex_support Q e.sourceEntries e.sourceDegree i j α hm
    have hh:=hE j
    dsimp only [GeneratorPlacement.level] at hp hh
    omega
  have hid:(projectiveIdentity Q (K:=K) E.placement).map (vertexHom Q α)=1 := by
    apply Matrix.ext
    intro i j
    by_cases he:i=j
    · subst j
      simp only [Matrix.one_apply,Matrix.map_apply,projectiveIdentity,Matrix.diagonal_apply]
      change (vertexId Q (K:=K) (E.placement i).color).vertex α = 1
      simp [hcolor i,vertexId_eval]
    · simp [projectiveIdentity,Matrix.map_apply,he,vertexHom]
  have he:=congrArg (fun M:Matrix I I (Q.Zigzag K)=>M.map (vertexHom Q α)) e.sourceEquation
  simp only [Matrix.map_mul,Matrix.map_add _ (map_add _),hid] at he
  have he':=congrArg (Matrix.vecMul x) he
  simp only [Matrix.vecMul_add,← Matrix.vecMul_vecMul,hxf,hx,hxh,
    Matrix.zero_vecMul,Matrix.vecMul_one,add_zero] at he'
  exact he'.symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomSpace
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_TraceLinear
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_LinearMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

lemma cochainSign_ne_zero (n : ℤ) : cochainSign (K := K) n ≠ 0 := by
  intro h
  have hh := cochainSign_mul_self (K := K) n
  rw [h, MulZeroClass.zero_mul] at hh
  exact zero_ne_one hh

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CoefficientTopDual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPreorderLiftedCell
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
lemma pure_top_socle_homDimension_pos (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (α : V) (c d : ℤ) (ht : coefficientTopDual Q E α c ≠ ⊥)
    (hs : coefficientSocle Q F α d ≠ ⊥) :
    0 < homDimension Q E F (d-c) (k-l-(d-c)) := by
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ht
  obtain ⟨y,hy,hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs
  let f : homCycles Q E F (d-c) (k-l-(d-c)) :=
    ⟨topSocleMatrix Q α x y, topSocleMatrix_mem_homCycles Q E F hE hF α c d hx hy⟩
  have hf : f ≠ 0 := fun h => topSocleMatrix_ne_zero Q α hx0 hy0 (congrArg Subtype.val h)
  unfold homDimension
  rw [(pureCoefficientCohomology Q E F hE hF (by omega)).finrank_eq]
  exact Module.finrank_pos_iff.mpr ⟨⟨f,0,hf⟩⟩

omit [Fintype V] [DecidableEq A] in
lemma homDimension_le_totalHomDimension (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homDimension Q E F n v ≤ totalHomDimension Q E F (n+v) := by
  classical
  by_cases hv : v ∈ homInternalSupport Q E F
  · unfold totalHomDimension
    have h' := Finset.single_le_sum (f := fun w => homDimension Q E F (n+v-w) w)
      (fun _ _ => Nat.zero_le _) hv
    simpa only [add_sub_cancel_right] using h'
  · rw [homDimension_off_internal_support Q E F n v hv]
    exact Nat.zero_le _

omit [DecidableEq A] in
lemma pure_top_socle_totalHomDimension_pos (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (α : V) (c d : ℤ) (ht : coefficientTopDual Q E α c ≠ ⊥)
    (hs : coefficientSocle Q F α d ≠ ⊥) :
    0 < totalHomDimension Q E F (k-l) := by
  have h := lt_of_lt_of_le (pure_top_socle_homDimension_pos Q E F hE hF α c d ht hs)
    (homDimension_le_totalHomDimension Q E F (d-c) (k-l-(d-c)))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LayerVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma layerVector_support (E:BasedComplex Q (K:=K) I) (d:ℤ)
    (x:{i // (E.placement i).level=d}→K) (i:I)
    (h:(E.placement i).level≠d) : layerVector Q E d x i=0 := by
  classical
  simp [layerVector,h]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma layerVector_socle (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (d:ℤ) (α:V) (c:ℤ) {x:{i // (E.placement i).level=d}→K}
    (hx:x∈coefficientSocle Q (E.pureLayer Q hE d) α c) :
    layerVector Q E d x∈coefficientSocle Q E α c := by
  classical
  constructor
  · intro i hi
    by_cases hid:(E.placement i).level=d
    · simpa [layerVector,hid] using hx.1 ⟨i,hid⟩ hi
    · exact layerVector_support Q E d x i hid
  · intro j a ha
    by_cases hj:(E.placement j).level=d
    · rw [← hx.2 ⟨j,hj⟩ a ha]
      symm
      apply Fintype.sum_of_injective
        (Subtype.val : {i // (E.placement i).level=d}→I) Subtype.val_injective
      · intro i hi
        rw [layerVector_support Q E d x i (fun h=>hi ⟨⟨i,h⟩,rfl⟩),MulZeroClass.zero_mul]
      · intro i
        change x i * (E.differential i.val j).arrow a =
          layerVector Q E d x i.val * (E.differential i.val j).arrow a
        simp only [layerVector,dite_eq_left i.property]
    · apply Finset.sum_eq_zero
      intro i hi
      by_cases hid:(E.placement i).level=d
      · have hd:(E.differential i j).arrow a=0 := by
          exact congrFun (differential_arrow_level Q E (fun h=>hj (h.trans hid))) a
        rw [hd,MulZeroClass.mul_zero]
      · rw [layerVector_support Q E d x i hid,MulZeroClass.zero_mul]

omit [DecidableEq I] in
lemma unitTestVector_bottom_cycle (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (d:ℤ) (hfloor:∀ i,d≤(E.placement i).level) (α:V) (c:ℤ)
    {x:I→K} (hx:x∈coefficientSocle Q E α c)
    (hs:∀ i,(E.placement i).level≠d→x i=0) :
    Matrix.vecMul (unitTestVector Q E.placement α x)
      ((E.testComplex Q α).differential.map (vertexHom Q α))=0 := by
  have hd:((E.testComplex Q α).differential.map (vertexHom Q α))=
      testMatrix Q E.placement E.placement α E.differential := by
    apply Matrix.ext
    intro i j
    change ((testMatrix Q E.placement E.placement α E.differential i j) • vertexId Q α).vertex α = _
    simp
  rw [hd]
  funext j
  rw [unitTestVector_differential Q E α x (fun i h=>hx.1 i (Or.inl h))]
  rcases j with ⟨j,⟨p,hp,hq⟩⟩
  rcases p with v|a|v
  · apply Finset.sum_eq_zero
    intro i hi
    change x i * (E.differential i j).vertex v=0
    simp only [hE i j,Pi.zero_apply,MulZeroClass.mul_zero]
  · exact hx.2 j a hp
  · apply Finset.sum_eq_zero
    intro i hi
    change x i * (E.differential i j).token v=0
    by_cases hxi:x i=0
    · rw [hxi,MulZeroClass.zero_mul]
    have hi:(E.placement i).level=d := Classical.not_not.mp (fun h=>hxi (hs i h))
    have hz:(E.differential i j).token v=0 := by
      by_contra hn
      obtain ⟨_,_,hc,hu⟩:=degree_token_support Q E.entries E.degree i j v hn
      have hj:=hfloor j
      dsimp only [GeneratorPlacement.level] at hi hj
      omega
    rw [hz,MulZeroClass.mul_zero]

omit [DecidableEq I] in
theorem bottomSocle_zero_of_test_equiv_above
    (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) {d:ℤ}
    (hfloor:∀ i,d≤(E.placement i).level) (α:V)
    (F:BasedComplex Q (K:=K) J) (e:HomotopyEquivalence Q (E.testComplex Q α) F)
    (hF:∀ j,d<(F.placement j).level) (c:ℤ) :
    coefficientSocle Q (E.pureLayer Q hE d) α c=⊥ := by
  classical
  apply le_antisymm _ bot_le
  intro x hx
  change x=0
  let y:=layerVector Q E d x
  have hy:y∈coefficientSocle Q E α c:=layerVector_socle Q E hE d α c hx
  have hs:∀ i,(E.placement i).level≠d→y i=0:=layerVector_support Q E d x
  have htf:∀ i,d≤((E.testComplex Q α).placement i).level := by
    intro i
    have hi:=hfloor i.1
    have hl:0≤Path.length i.2.val := by
      rcases i.2.val with v|a|v <;> norm_num [Path.length]
    dsimp only [testComplex,testPlacement,GeneratorPlacement.level] at *
    omega
  have hts:∀ i,((E.testComplex Q α).placement i).level≠d→
      unitTestVector Q E.placement α y i=0 := by
    intro i hi
    change y i.1 * pathCoordinates Q (vertexId Q α) i.2.val=0
    by_cases hp:Sum.inl α=i.2.val
    · rw [vertex_coordinates,ite_eq_left hp,_root_.mul_one]
      apply hs
      intro hc
      apply hi
      change (E.placement i.1).cochain+((E.placement i.1).internal+Path.length i.2.val)=d
      rw [← hp]
      simpa [Path.length,GeneratorPlacement.level] using hc
    · rw [vertex_coordinates,ite_eq_right hp,MulZeroClass.mul_zero]
  have hz:=bottom_scalar_cycle_zero Q (E.testComplex Q α) F e α (fun _=>rfl) htf hF
    (unitTestVector Q E.placement α y) hts (unitTestVector_bottom_cycle Q E hE d hfloor α c hy hs)
  have hy0:y=0 := by
    have hh:=congrArg (sumUnitTest Q E.placement α) hz
    rw [sumUnitTest_unit Q E.placement α y (fun i h=>hy.1 i (Or.inl h)),map_zero] at hh
    exact hh
  funext i
  have hh:=congrFun hy0 i.val
  change (if h:(E.placement i.val).level=d then x ⟨i.val,h⟩ else 0)=0 at hh
  split_ifs at hh with hi
  · exact hh
  · exact (hi i.property).elim

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_BottomSocleZeroTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem bottomSocle_zero_of_test_cycle_zero
    (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) {d c:ℤ}
    (hfloor:∀ i,d≤(E.placement i).level) (α:V)
    (hzero:∀ y:TestIndex Q E.placement α→K,
      (∀ i,¬ (((E.testComplex Q α).placement i).level=d ∧
        ((E.testComplex Q α).placement i).cochain=c)→y i=0)→
      Matrix.vecMul y ((E.testComplex Q α).differential.map (vertexHom Q α))=0→y=0) :
    coefficientSocle Q (E.pureLayer Q hE d) α c=⊥ := by
  classical
  apply le_antisymm _ bot_le
  intro x hx
  change x=0
  let y:=layerVector Q E d x
  have hy:y∈coefficientSocle Q E α c:=layerVector_socle Q E hE d α c hx
  have hs:∀ i,(E.placement i).level≠d→y i=0:=layerVector_support Q E d x
  have hts:∀ i,¬ (((E.testComplex Q α).placement i).level=d ∧
      ((E.testComplex Q α).placement i).cochain=c)→
      unitTestVector Q E.placement α y i=0 := by
    intro i hi
    change y i.1 * pathCoordinates Q (vertexId Q α) i.2.val=0
    by_cases hp:Sum.inl α=i.2.val
    · rw [vertex_coordinates,ite_eq_left hp,_root_.mul_one]
      by_cases hl:(E.placement i.1).level=d
      · apply hy.1
        right
        intro hc
        apply hi
        constructor
        · change (E.placement i.1).cochain+((E.placement i.1).internal+Path.length i.2.val)=d
          rw [← hp]
          simpa [Path.length,GeneratorPlacement.level] using hl
        · exact hc
      · exact hs i.1 hl
    · rw [vertex_coordinates,ite_eq_right hp,MulZeroClass.mul_zero]
  have hz:=hzero (unitTestVector Q E.placement α y) hts
    (unitTestVector_bottom_cycle Q E hE d hfloor α c hy hs)
  have hy0:y=0 := by
    have hh:=congrArg (sumUnitTest Q E.placement α) hz
    rw [sumUnitTest_unit Q E.placement α y (fun i h=>hy.1 i (Or.inl h)),map_zero] at hh
    exact hh
  funext i
  have hh:=congrFun hy0 i.val
  change (if h:(E.placement i.val).level=d then x ⟨i.val,h⟩ else 0)=0 at hh
  split_ifs at hh with hi
  · exact hh
  · exact (hi i.property).elim

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_MinimalEmbedding
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteModel

universe u

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

theorem exists_minimal_embedding (E : FiniteModel.{u} Q (K := K)) :
    ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
      Nonempty (HomotopyEquivalence Q E.complex F.complex) ∧
        ∃ e : F.Index ↪ E.Index, ∀ i, F.complex.placement i = E.complex.placement (e i) := by
  have h : ∀ n (B : FiniteModel.{u} Q (K := K)), Fintype.card B.Index = n →
      ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
        Nonempty (HomotopyEquivalence Q B.complex F.complex) ∧
          ∃ e : F.Index ↪ B.Index,
            ∀ i, F.complex.placement i = B.complex.placement (e i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro B hn
      by_cases hm : B.complex.IsMinimal Q
      · exact ⟨B, hm, ⟨HomotopyEquivalence.refl Q B.complex⟩,
          Function.Embedding.refl _, fun _ => rfl⟩
      · obtain ⟨p⟩ := scalarPivot_of_not_minimal Q B.complex hm
        let C := ofComplex Q (p.reduced Q)
        have hc : Fintype.card C.Index < n := by
          dsimp only [C, ofComplex]
          rw [← hn]
          exact p.retained_card_lt Q
        obtain ⟨F, hF, ⟨e⟩, j, hj⟩ := ih (Fintype.card C.Index) hc C rfl
        exact ⟨F, hF, ⟨(p.reductionEquivalence Q).trans Q e⟩,
          j.trans ⟨Subtype.val, Subtype.val_injective⟩, hj⟩
  exact h (Fintype.card E.Index) E rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteModel

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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_MinimalModelEquivalence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type u} [Fintype I] [DecidableEq I]

lemma classLayerSocleDimension_minimal (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (d : ℤ) (α : V) (c : ℤ) :
    classLayerSocleDimension Q d α c (classOfComplex Q E) =
      Module.finrank K (coefficientSocle Q (E.pureLayer Q hE d) α c) :=
  (((minimalClassModelEquivalence Q E).pureLayer Q
    (minimalClassModel_minimal Q _) hE d).coefficientSocle Q
    (fun i => i.property) (fun j => j.property) α c).finrank_eq

lemma classLayerTopDimension_minimal (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (d : ℤ) (α : V) (c : ℤ) :
    classLayerTopDimension Q d α c (classOfComplex Q E) =
      Module.finrank K (coefficientTopDual Q (E.pureLayer Q hE d) α c) :=
  (((minimalClassModelEquivalence Q E).pureLayer Q
    (minimalClassModel_minimal Q _) hE d).coefficientTopDual Q
    (fun i => i.property) (fun j => j.property) α c).finrank_eq

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CoefficientSocleRestrictLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma coefficientSocle_restrict_layer
    (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q) (d:ℤ) (α:V) (c:ℤ)
    {x : I → K} (hx : x ∈ coefficientSocle Q E α c)
    (hs : ∀ i, (E.placement i).level≠d → x i=0) :
    (fun i : {i // (E.placement i).level=d} => x i.val) ∈
      coefficientSocle Q (E.pureLayer Q hE d) α c := by
  constructor
  · intro i hi; exact hx.1 i.val hi
  · intro j a ha
    change (∑ i : {i // (E.placement i).level=d}, x i.val * (E.differential i.val j.val).arrow a)=0
    rw [← hx.2 j.val a ha]
    apply Fintype.sum_of_injective (Subtype.val : {i // (E.placement i).level=d} → I)
      Subtype.val_injective
    · intro i hi
      rw [hs i (fun h => hi ⟨⟨i,h⟩,rfl⟩),MulZeroClass.zero_mul]
    · intro i; rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CoefficientTopDualRestrict
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I]

lemma coefficientTopDual_restrict_layer
    (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q) (d:ℤ) (α:V) (c:ℤ)
    {x : I → K} (hx : x ∈ coefficientTopDual Q E α c)
    (hs : ∀ i, (E.placement i).level≠d → x i=0) :
    (fun i : {i // (E.placement i).level=d} => x i.val) ∈
      coefficientTopDual Q (E.pureLayer Q hE d) α c := by
  constructor
  · intro i hi; exact hx.1 i.val hi
  · intro i a
    change (∑ j : {i // (E.placement i).level=d}, (E.differential i.val j.val).arrow a * x j.val)=0
    rw [← hx.2 i.val a]
    apply Fintype.sum_of_injective (Subtype.val : {i // (E.placement i).level=d} → I)
      Subtype.val_injective
    · intro j hj
      rw [hs j (fun h => hj ⟨⟨j,h⟩,rfl⟩),MulZeroClass.mul_zero]
    · intro j; rfl

lemma coefficientTopDual_restrict_layer_ne_zero
    (E : BasedComplex Q (K := K) I) (d:ℤ) {x : I → K}
    (hx : x≠0) (hs : ∀ i, (E.placement i).level≠d → x i=0) :
    (fun i : {i // (E.placement i).level=d} => x i.val) ≠ 0 := by
  intro hz
  apply hx
  funext i
  by_cases hi : (E.placement i).level=d
  · exact congrFun hz ⟨i,hi⟩
  · exact hs i hi

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PacketTwistRaisedGenerator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J P : Type u} [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq I] [DecidableEq J] [DecidableEq P]

theorem packetTwist_raised_generator_top_at_cap
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    {l : ℤ} (hE : ∀ i, (E.placement i).level≤l) (v:P → V)
    (hF : F.IsMinimal Q) (e : HomotopyEquivalence Q (E.packetTwist Q v) F)
    (j:J) (hj : (F.placement j).level=l+1) :
    ∃ a:P, ∃ x:I → K,
      x ∈ coefficientTopDual Q E (v a) ((F.placement j).cochain+1) ∧ x≠0 ∧
      ∀ i, (E.placement i).level≠l → x i=0 := by
  obtain ⟨x,hx,hxs,hxd⟩ := minimal_generator_dual_cycle Q (E.packetTwist Q v) F hF e j
  have hxold i : x (Sum.inr i)=0 := by
    apply hxs
    intro he
    have hl := congrArg GeneratorPlacement.level he
    change (E.placement i).level = (F.placement j).level at hl
    have hb := hE i
    rw [hj] at hl
    omega
  have hex : ∃ z, x z≠0 := not_forall.mp (fun h => hx (funext h))
  obtain ⟨⟨a,u⟩|i,hz⟩ := hex
  swap
  · exact (hz (hxold i)).elim
  have hp : (E.packetTwist Q v).placement (Sum.inl ⟨a,u⟩)=F.placement j :=
    Classical.not_not.mp (fun h => hz (hxs _ h))
  have hα : (F.placement j).color=v a := (congrArg GeneratorPlacement.color hp).symm
  let y : TestIndex Q E.placement (v a) → K := fun i => x (Sum.inl ⟨a,i⟩)
  have hplace (i : TestIndex Q E.placement (v a))
      (he : (E.packetTwist Q v).placement (Sum.inl ⟨a,i⟩)=F.placement j) :
      (E.placement i.1).cochain=(F.placement j).cochain+1 ∧
        Path.length i.2.val=2 ∧ (E.placement i.1).level=l := by
    have hc := congrArg GeneratorPlacement.cochain he
    have hu := congrArg GeneratorPlacement.internal he
    change (E.placement i.1).cochain-1=(F.placement j).cochain at hc
    change (E.placement i.1).internal+Path.length i.2.val=(F.placement j).internal at hu
    have hl := hE i.1
    have hr : Path.length i.2.val≤2 := by
      rcases Path.length_cases i.2.val with h|h|h <;> omega
    dsimp only [GeneratorPlacement.level] at hl hj ⊢
    exact ⟨by omega,by omega,by omega⟩
  have hys i : ¬ ((E.placement i.1).cochain=(F.placement j).cochain+1 ∧
      Path.length i.2.val=2) → y i=0 := by
    intro hi
    apply hxs
    intro he
    exact hi ⟨(hplace i he).1,(hplace i he).2.1⟩
  have hyd : Matrix.vecMul y
      (testMatrix Q E.placement E.placement (v a) E.differential).transpose=0 := by
    funext i
    have hh := hxd (Sum.inl ⟨a,i⟩)
    rw [hα,Fintype.sum_sum_type,Fintype.sum_sigma] at hh
    have ht k : ((E.packetTwist Q v).differential (Sum.inl ⟨a,i⟩) (Sum.inl ⟨a,k⟩)).vertex (v a) =
        -testMatrix Q E.placement E.placement (v a) E.differential i k := by
      change (-(packetDifferential Q E.placement v E.differential) ⟨a,i⟩ ⟨a,k⟩).vertex (v a) = _
      rw [packetDifferential,Matrix.blockDiagonal'_apply_eq]
      change -(testMatrix Q E.placement E.placement (v a) E.differential i k *
        (vertexId Q (K := K) (v a)).vertex (v a)) = _
      simp [vertexId_eval]
    have htne b (hb:b≠a) (k:TestIndex Q E.placement (v b)) :
        ((E.packetTwist Q v).differential (Sum.inl ⟨a,i⟩) (Sum.inl ⟨b,k⟩)).vertex (v a)=0 := by
      change (-(packetDifferential Q E.placement v E.differential) ⟨a,i⟩ ⟨b,k⟩).vertex (v a) = _
      rw [packetDifferential,Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hb),neg_zero]
      rfl
    rw [Finset.sum_eq_single a] at hh
    · simp only [ht,hxold,MulZeroClass.mul_zero,Finset.sum_const_zero,add_zero,
        neg_mul,Finset.sum_neg_distrib,neg_eq_zero] at hh
      simpa only [Matrix.vecMul,Matrix.transpose_apply,dotProduct,mul_comm,Pi.zero_apply] using hh
    · intro b hb hba
      simp only [htne b hba,MulZeroClass.zero_mul,Finset.sum_const_zero]
    · simp
  have hy : y ∈ topTestCycles Q E (v a) ((F.placement j).cochain+1) := ⟨hys,hyd⟩
  refine ⟨a,sumTokenTest Q E.placement (v a) y, sumTokenTest_top Q E (v a) _ hy, ?_, ?_⟩
  · intro hzero
    have hyz : y=0 := by
      rw [← tokenTestVector_sum Q E.placement (v a) _ y hys,hzero,map_zero]
    exact hz (congrFun hyz u)
  · intro i hi
    apply Finset.sum_eq_zero
    intro z hz
    apply hxs
    intro he
    exact hi (hplace ⟨i,z⟩ he).2.2

theorem packetTwist_cap_of_top_zero
    (E : BasedComplex Q (K := K) I) (hmin : E.IsMinimal Q) {l : ℤ}
    (hE : ∀ i, (E.placement i).level≤l) (v:P → V)
    (htop : ∀ a c, coefficientTopDual Q (E.pureLayer Q hmin l) (v a) c=⊥) :
    ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
      Nonempty (HomotopyEquivalence Q (E.packetTwist Q v) F.complex) ∧
      ∀ j, (F.complex.placement j).level≤l := by
  let B := FiniteModel.ofComplex Q (E.packetTwist Q v)
  obtain ⟨F,hF,⟨e⟩,f,hf⟩ := B.exists_minimal_embedding Q
  refine ⟨F,hF,⟨e⟩,?_⟩
  intro j
  by_contra hb
  have hj : (F.complex.placement j).level=l+1 := by
    have hmax : (F.complex.placement j).level≤l+1 := by
      rw [hf j]
      change ((E.packetTwist Q v).placement (f j)).level≤l+1
      rcases f j with ⟨a,i,p⟩|i
      · change ((E.placement i).cochain-1)+((E.placement i).internal+Path.length p.val)≤l+1
        have hh := hE i
        have hr : Path.length p.val≤2 := by
          rcases Path.length_cases p.val with h|h|h <;> omega
        dsimp only [GeneratorPlacement.level] at hh
        omega
      · have hh := hE i
        change (E.placement i).level≤l+1
        omega
    omega
  obtain ⟨a,x,hx,hxz,hs⟩ := packetTwist_raised_generator_top_at_cap Q E F.complex hE v hF e j hj
  have hm := coefficientTopDual_restrict_layer Q E hmin l (v a) _ hx hs
  have hn := coefficientTopDual_restrict_layer_ne_zero Q E l hxz hs
  rw [htop] at hm
  exact hn ((Submodule.mem_bot K).mp hm)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_UpperBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem classPacketPerm_cap_of_top_zero
    (hn:∀ a,Q.source a≠Q.target a) (v:J→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K:=K)) {l:ℤ} (hcap:ClassUpperBound Q l x)
    (htop:∀ a c,classLayerTopDimension Q l (v a) c x=0) :
    ClassUpperBound Q l (classPacketPerm Q hn v hv x) := by
  let E:=minimalClassModel Q x
  have hE:E.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  have ht:∀ a c,coefficientTopDual Q (E.complex.pureLayer Q hE l) (v a) c=⊥ := by
    intro a c
    exact Submodule.finrank_eq_zero.mp (htop a c)
  obtain ⟨F,hF,⟨e⟩,hb⟩:=packetTwist_cap_of_top_zero Q E.complex hE hcap v ht
  have hh:=classUpperBound_of_representative Q F.complex hb
  have hx:classPacketPerm Q hn v hv x=classOfComplex Q F.complex := by
    rw [← minimalClassModel_class Q x,classPacketPerm_apply]
    exact classOfComplex_eq Q e
  rw [hx]
  exact hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveTwistLowerBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
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

theorem positiveTwist_bottom_socle_zero
    (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    {d:ℤ} (hE:∀ i,d≤(E.placement i).level) (α:V) (hF:F.IsMinimal Q)
    (e:HomotopyEquivalence Q (E.positiveTwist Q α) F) (c:ℤ) :
    coefficientSocle Q (F.pureLayer Q hF d) α c=⊥ := by
  let g:=((e.symm Q).test Q α).trans Q (positiveTwist_testShift Q hn E α)
  apply bottomSocle_zero_of_test_equiv_above Q F hF
    (positiveTwist_lower_bound Q E F hE α hF e) α ((E.testComplex Q α).tokenShift Q) g _ c
  intro j
  have hh:=hE j.1
  have hl:0≤Path.length j.2.val := by
    rcases j.2.val with v|a|v <;> norm_num [Path.length]
  dsimp only [GeneratorPlacement.level,tokenShift,testComplex,testPlacement] at *
  omega

theorem classPositiveTwist_bottom_socle_zero
    (hn:∀ a,Q.source a≠Q.target a) (α:V)
    (x:FiniteHomotopyClass Q (K:=K)) {d:ℤ} (hx:ClassLowerBound Q d x) (c:ℤ) :
    classLayerSocleDimension Q d α c (classPositiveTwist Q α x)=0 := by
  let E:=minimalClassModel Q x
  let y:=classPositiveTwist Q α x
  let F:=minimalClassModel Q y
  have he:classOfComplex Q (E.complex.positiveTwist Q α)=classOfComplex Q F.complex := by
    change classPositiveTwist Q α (classOfComplex Q E.complex)=classOfComplex Q F.complex
    have hE:classOfComplex Q E.complex=x:=minimalClassModel_class Q x
    have hF:classOfComplex Q F.complex=y:=minimalClassModel_class Q y
    rw [hE,hF]
  obtain ⟨e⟩:=Quotient.exact he
  change Module.finrank K (coefficientSocle Q (F.complex.pureLayer Q
    (minimalClassModel_minimal Q y) d) α c)=0
  rw [positiveTwist_bottom_socle_zero Q hn E.complex F.complex hx α
    (minimalClassModel_minimal Q y) e c]
  simp

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TestComplexVertexDifferential
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I]

lemma test_bottom_length_zero (E:BasedComplex Q (K:=K) I) {d:ℤ}
    (hfloor:∀ i,d≤(E.placement i).level) (α:V)
    (i:TestIndex Q E.placement α) (hi:((E.testComplex Q α).placement i).level=d) :
    Path.length i.2.val=0 ∧ (E.placement i.1).level=d := by
  have hh:=hfloor i.1
  have hl:0≤Path.length i.2.val := by
    rcases i.2.val with v|a|v <;> norm_num [Path.length]
  dsimp only [testComplex,testPlacement,GeneratorPlacement.level] at *
  omega

theorem bottom_test_cycle_zero_of_socle
    (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) {d:ℤ}
    (hfloor:∀ i,d≤(E.placement i).level) (α:V) (c:ℤ)
    (hS:coefficientSocle Q (E.pureLayer Q hE d) α c=⊥)
    (y:TestIndex Q E.placement α→K)
    (hs:∀ i,¬ (((E.testComplex Q α).placement i).level=d ∧
      ((E.testComplex Q α).placement i).cochain=c)→y i=0)
    (hd:Matrix.vecMul y ((E.testComplex Q α).differential.map (vertexHom Q α))=0) : y=0 := by
  have hy: y∈socleTestCycles Q E α c := by
    constructor
    · intro i hi
      apply hs
      rintro ⟨hl,hc⟩
      exact hi ⟨hc,(test_bottom_length_zero Q E hfloor α i hl).1⟩
    · rwa [testComplex_vertex_differential Q E α] at hd
  let x:=sumUnitTest Q E.placement α y
  have hx:x∈coefficientSocle Q E α c:=sumUnitTest_socle Q E α c hy
  have hxs:∀ i,(E.placement i).level≠d→x i=0 := by
    intro i hi
    apply Finset.sum_eq_zero
    intro z hz
    apply hs
    intro hh
    exact hi (test_bottom_length_zero Q E hfloor α ⟨i,z⟩ hh.1).2
  have hxr:=coefficientSocle_restrict_layer Q E hE d α c hx hxs
  rw [hS] at hxr
  have hzr:(fun i:{i // (E.placement i).level=d}=>x i.val)=0:=hxr
  have hx0:x=0 := by
    funext i
    by_cases hi:(E.placement i).level=d
    · exact congrFun hzr ⟨i,hi⟩
    · exact hxs i hi
  rw [← unitTestVector_sum Q E.placement α c y hy.1]
  change unitTestVector Q E.placement α x=0
  rw [hx0,map_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveTwistOtherTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq I] in
theorem positiveTwist_other_test_cycle_zero
    (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) {d c:ℤ}
    (hfloor:∀ i,d≤(E.placement i).level) (α β:V) (hne:β≠α)
    (hα:coefficientSocle Q (E.pureLayer Q hE d) α (c+1)=⊥)
    (hβ:coefficientSocle Q (E.pureLayer Q hE d) β c=⊥)
    (y:TestIndex Q (E.positiveTwist Q α).placement β→K)
    (hs:∀ i,¬ ((((E.positiveTwist Q α).testComplex Q β).placement i).level=d ∧
      (((E.positiveTwist Q α).testComplex Q β).placement i).cochain=c)→y i=0)
    (hd:Matrix.vecMul y (((E.positiveTwist Q α).testComplex Q β).differential.map
      (vertexHom Q β))=0) : y=0 := by
  have hn:∀ p:Zigzag.CornerPath Q β α,∀ u:TestIndex Q E.placement α,
      y (twistNewTestIndex Q E α β p u)=0 := by
    intro p
    have hl:=corner_other_length Q hne p
    have hx:(fun u=>y (twistNewTestIndex Q E α β p u))=0 := by
      apply bottom_test_cycle_zero_of_socle Q E hE hfloor α (c+1) hα
      · intro i hi
        apply hs
        intro hh
        apply hi
        change (E.placement i.1).cochain+((E.placement i.1).internal+Path.length i.2.val)=d ∧
          (E.placement i.1).cochain=c+1
        change (E.placement i.1).cochain-1+
          ((E.placement i.1).internal+Path.length i.2.val+Path.length p.val)=d ∧
          (E.placement i.1).cochain-1=c at hh
        omega
      · rw [testComplex_vertex_differential Q E α]
        funext v
        have hh:=congrFun hd (twistNewTestIndex Q E α β p v)
        rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
          twistTest_new_differential Q E α β y p v] at hh
        exact neg_eq_zero.mp hh
    exact fun u=>congrFun hx u
  have ho:(fun u=>y (twistOldTestIndex Q E α β u))=0 := by
    apply bottom_test_cycle_zero_of_socle Q E hE hfloor β c hβ
    · intro i hi
      exact hs _ hi
    · rw [testComplex_vertex_differential Q E β]
      funext v
      have hh:=congrFun hd (twistOldTestIndex Q E α β v)
      rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_old_differential Q E α β y hn v] at hh
      exact hh
  funext i
  obtain ⟨i,p⟩:=i
  rcases i with i|i
  · exact hn p i
  · exact congrFun ho ⟨i,p⟩

theorem positiveTwist_other_bottom_socle_zero
    (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (F:BasedComplex Q (K:=K) J) (hF:F.IsMinimal Q) {d c:ℤ}
    (hfloor:∀ i,d≤(E.placement i).level) (α β:V) (hne:β≠α)
    (hα:coefficientSocle Q (E.pureLayer Q hE d) α (c+1)=⊥)
    (hβ:coefficientSocle Q (E.pureLayer Q hE d) β c=⊥)
    (e:HomotopyEquivalence Q (E.positiveTwist Q α) F) :
    coefficientSocle Q (F.pureLayer Q hF d) β c=⊥ := by
  have hFl:=positiveTwist_lower_bound Q E F hfloor α hF e
  apply bottomSocle_zero_of_test_cycle_zero Q F hF hFl β
  intro y hs hd
  apply bottom_scalar_cycle_transport Q (F.testComplex Q β)
    ((E.positiveTwist Q α).testComplex Q β) ((e.symm Q).test Q β) β
    (fun _=>rfl) _ (positiveTwist_other_test_cycle_zero Q E hE hfloor α β hne hα hβ) y hs hd
  intro i
  have hi:=hFl i.1
  have hl:0≤Path.length i.2.val := by
    rcases i.2.val with v|a|v <;> norm_num [Path.length]
  dsimp only [testComplex,testPlacement,GeneratorPlacement.level] at *
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_BottomSocleZero
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

theorem classPositiveTwist_other_bottom_socle_zero
    (α β:V) (hne:β≠α) (x:FiniteHomotopyClass Q (K:=K)) {d c:ℤ}
    (hx:ClassLowerBound Q d x)
    (hα:classLayerSocleDimension Q d α (c+1) x=0)
    (hβ:classLayerSocleDimension Q d β c x=0) :
    classLayerSocleDimension Q d β c (classPositiveTwist Q α x)=0 := by
  let E:=minimalClassModel Q x
  let y:=classPositiveTwist Q α x
  let F:=minimalClassModel Q y
  have he:classOfComplex Q (E.complex.positiveTwist Q α)=classOfComplex Q F.complex := by
    change classPositiveTwist Q α (classOfComplex Q E.complex)=classOfComplex Q F.complex
    have hE:classOfComplex Q E.complex=x:=minimalClassModel_class Q x
    have hF:classOfComplex Q F.complex=y:=minimalClassModel_class Q y
    rw [hE,hF]
  obtain ⟨e⟩:=Quotient.exact he
  apply Submodule.finrank_eq_zero.mpr
  exact positiveTwist_other_bottom_socle_zero Q E.complex (minimalClassModel_minimal Q x)
    F.complex (minimalClassModel_minimal Q y) hx α β hne
    (Submodule.finrank_eq_zero.mp hα) (Submodule.finrank_eq_zero.mp hβ) e

theorem classPositiveTwist_preserves_open_socle
    (hn:∀ a,Q.source a≠Q.target a) (α:V) (J:Set V) (hα:α∈J)
    (x:FiniteHomotopyClass Q (K:=K)) {d:ℤ} (hx:ClassLowerBound Q d x)
    (hJ:ClassBottomSocleZero Q d J x) :
    ClassBottomSocleZero Q d J (classPositiveTwist Q α x) := by
  intro β hβ c
  by_cases he:β=α
  · subst β
    exact classPositiveTwist_bottom_socle_zero Q hn α x hx c
  · exact classPositiveTwist_other_bottom_socle_zero Q α β he x hx (hJ α hα (c+1)) (hJ β hβ c)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

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
lemma placementSignedWeight_lower (a : GeneratorPlacement V) (v : V) :
    placementSignedWeight ⟨a.color,a.cochain-1,a.internal⟩ v= -placementSignedWeight a v := by
  have hh : a.cochain-1+a.internal=a.level-1 := by dsimp [GeneratorPlacement.level]; omega
  simp only [placementSignedWeight,GeneratorPlacement.level,hh,cochainSign_sub_one]
  split_ifs <;> simp

omit [DecidableEq A] [Fintype V] in
lemma Map.signedGeneratorVector_cone {I J : Type u} [Fintype I] [Fintype J]
    {E : BasedComplex Q (K:=K) I} {F : BasedComplex Q (K:=K) J} (f : Map Q E F) :
    signedGeneratorVector Q (f.cone Q)=signedGeneratorVector Q F-signedGeneratorVector Q E := by
  funext v
  simp only [signedGeneratorVector,Map.cone,Map.conePlacement,Fintype.sum_sum_type,
    placementSignedWeight_lower,Finset.sum_neg_distrib,Pi.sub_apply]
  ring

theorem signedGeneratorVector_positiveTwist {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K:=K) I) (α : V) :
    signedGeneratorVector Q (E.positiveTwist Q α)=rowReflect (unfoldedCartan Q) α
      (signedGeneratorVector Q E) := by
  unfold positiveTwist
  rw [Map.signedGeneratorVector_cone]
  funext β
  simp only [Pi.sub_apply,signedGeneratorVector_test,rowReflect,Pi.smul_apply,smul_eq_mul,
    Pi.single_apply]
  by_cases h : α=β
  · subst β; simp
  · simp [h,Ne.symm h]

lemma classSignedVector_positiveTwist (x : FiniteHomotopyClass Q (K:=K)) (α : V) :
    classSignedVector Q (classPositiveTwist Q α x)=
      rowReflect (unfoldedCartan Q) α (classSignedVector Q x) := by
  induction x using Quotient.inductionOn with | _ E =>
    exact signedGeneratorVector_positiveTwist Q E.complex α

lemma classSignedVector_positiveWord (w : List V) (x : FiniteHomotopyClass Q (K:=K)) :
    classSignedVector Q (positiveWordAction Q w x)=
      rowReflectWord (unfoldedCartan Q) w (classSignedVector Q x) := by
  induction w with
  | nil => rfl
  | cons α w ih =>
    change classSignedVector Q (classPositiveTwist Q α (positiveWordAction Q w x))=_
    rw [classSignedVector_positiveTwist,ih]
    rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ColorRestrictionTopZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype I] [DecidableEq I]
attribute [local instance] Classical.decEq Classical.propDecidable

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma colorRestriction_top_zero (E:BasedComplex Q (K:=K) I) (q:ℤ) (U:Set V)
    (hp:∀ i,(E.placement i).level=q)
    (hb:∀ i,(E.placement i).color∉colorBoundary Q U)
    (α:V) (hα:α∈U) (c:ℤ)
    (hz:coefficientTopDual Q (colorRestriction Q E U hp hb) α c=⊥) :
    coefficientTopDual Q E α c=⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  change x=0
  let y:{i:I // (E.placement i).color∈U}→K:=fun i=>x i
  have hxo (i:I) (hi:(E.placement i).color∉U):x i=0 := by
    apply hx.1 i
    left
    intro h
    exact hi (h ▸ hα)
  have hy:y∈coefficientTopDual Q (colorRestriction Q E U hp hb) α c := by
    constructor
    · intro i hi
      exact hx.1 i hi
    · intro i a
      change (∑ j:{i:I //(E.placement i).color∈U},(E.differential i.val j.val).arrow a*x j.val)=0
      rw [← Finset.sum_subtype (Finset.univ.filter fun j:I=>(E.placement j).color∈U)
        (by simp) (fun j:I=>(E.differential i.val j).arrow a*x j),Finset.sum_filter]
      convert hx.2 i.val a using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj:(E.placement j).color∈U
      · rw [ite_eq_left hj]
      · rw [ite_eq_right hj,hxo j hj,MulZeroClass.mul_zero]
  rw [hz] at hy
  have hy0:y=0:=(Submodule.mem_bot K).mp hy
  funext i
  by_cases hi:(E.placement i).color∈U
  · exact congrFun hy0 ⟨i,hi⟩
  · exact hxo i hi

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ComplexPacketLowerBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I]

theorem classOfComplex_packet_lower_bound
    (E:BasedComplex Q (K:=K) I) {d:ℤ} (hE:∀ i,d≤(E.placement i).level)
    (v:J→V) (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)) :
    ClassLowerBound Q d (classOfComplex Q (E.packetTwist Q v)) := by
  suffices hh:∀ (J:Type u) [Fintype J] (v:J→V),
      Pairwise (fun a b=>OrthogonalVertices Q (v a) (v b)) →
      ClassLowerBound Q d (classOfComplex Q (E.packetTwist Q v)) from hh J v hv
  intro J inst
  apply Fintype.induction_empty_option (P:=fun J _=>∀ v:J→V,
    Pairwise (fun a b=>OrthogonalVertices Q (v a) (v b)) →
    ClassLowerBound Q d (classOfComplex Q (E.packetTwist Q v))) _ _ _ J
  · intro J L instL e ih
    let:=Fintype.ofEquiv L e.symm
    intro v hv
    rw [classOfComplex_packet_reindex Q E v e]
    exact ih (v ∘ e) (fun a b hab=>hv (fun h=>hab (e.injective h)))
  · let : DecidableEq PEmpty := Classical.decEq _
    intro v hv
    apply classLowerBound_of_representative Q
    intro j
    rcases j with u|i
    · exact isEmptyElim u.1
    · exact hE i
  · intro J instJ ih
    let : DecidableEq J := Classical.decEq _
    let : DecidableEq (Option J) := Classical.decEq _
    intro v hv
    have hv':v=fun z:Option J=>z.elim (v none) (v ∘ some) := by
      funext z; cases z <;> rfl
    have he:classOfComplex Q (E.packetTwist Q v)=
        classPositiveTwist Q (v none) (classOfComplex Q (E.packetTwist Q (v ∘ some))) := by
      conv_lhs => rw [hv']
      convert classOfComplex_packet_cons Q E (v none) (v ∘ some) (fun a=>hv (by simp)) using 1
      all_goals try with_reducible_and_instances rfl
      congr 2
      exact Subsingleton.elim _ _
    rw [he]
    exact classPositiveTwist_lower_bound Q (v none) _
      (ih (v ∘ some) (fun a b hab=>hv (fun h=>hab (Option.some.inj h))))

theorem classPacketPerm_lower_bound
    (hn:∀ a,Q.source a≠Q.target a) (v:J→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K:=K)) {d:ℤ} (hx:ClassLowerBound Q d x) :
    ClassLowerBound Q d (classPacketPerm Q hn v hv x) := by
  have he:classPacketPerm Q hn v hv x=
      classOfComplex Q ((minimalClassModel Q x).complex.packetTwist Q v) := by
    conv_lhs => rw [← minimalClassModel_class Q x,classPacketPerm_apply]
  rw [he]
  exact classOfComplex_packet_lower_bound Q _ hx v hv

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ComplexPacketPreserves
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

theorem classOfComplex_packet_preserves
    {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I]
    (E:BasedComplex Q (K:=K) I) (P:FiniteHomotopyClass Q (K:=K)→Prop)
    (hE:P (classOfComplex Q E)) (v:J→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (hstep:∀ a x,P x→P (classPositiveTwist Q (v a) x)) :
    P (classOfComplex Q (E.packetTwist Q v)) := by
  have hs:=hstep
  suffices hh:∀ (J:Type u) [Fintype J] (v:J→V),
      Pairwise (fun a b=>OrthogonalVertices Q (v a) (v b))→
      (∀ a x,P x→P (classPositiveTwist Q (v a) x))→
      P (classOfComplex Q (E.packetTwist Q v)) from hh J v hv hs
  intro J inst
  apply Fintype.induction_empty_option (P:=fun J _=>∀ v:J→V,
    Pairwise (fun a b=>OrthogonalVertices Q (v a) (v b))→
    (∀ a x,P x→P (classPositiveTwist Q (v a) x))→
    P (classOfComplex Q (E.packetTwist Q v))) _ _ _ J
  · intro J L instL e ih
    let:=Fintype.ofEquiv L e.symm
    intro v hv hs
    rw [classOfComplex_packet_reindex Q E v e]
    exact ih (v ∘ e) (fun a b hab=>hv (fun h=>hab (e.injective h))) (fun a=>hs (e a))
  · let : DecidableEq PEmpty := Classical.decEq _
    intro v hv hs
    have he:classOfComplex Q (E.packetTwist Q v)=classOfComplex Q E := by
      convert (classOfComplex_reindex Q _ (packetEmptyEquiv Q E v)).trans
        (congrArg (classOfComplex Q) (packetEmpty_eq Q E v)) using 1
      all_goals try with_reducible_and_instances rfl
    rw [he]
    exact hE
  · intro J instJ ih
    let : DecidableEq J := Classical.decEq _
    let : DecidableEq (Option J) := Classical.decEq _
    intro v hv hs
    have hv':v=fun z:Option J=>z.elim (v none) (v ∘ some) := by
      funext z; cases z <;> rfl
    have he:classOfComplex Q (E.packetTwist Q v)=
        classPositiveTwist Q (v none) (classOfComplex Q (E.packetTwist Q (v ∘ some))) := by
      conv_lhs => rw [hv']
      convert classOfComplex_packet_cons Q E (v none) (v ∘ some) (fun a=>hv (by simp)) using 1
      all_goals try with_reducible_and_instances rfl
      congr 2
      exact Subsingleton.elim _ _
    rw [he]
    exact hs none _ (ih (v ∘ some) (fun a b hab=>hv (fun h=>hab (Option.some.inj h)))
      (fun a=>hs (some a)))

theorem classPacketPerm_preserves
    (hn:∀ a,Q.source a≠Q.target a) {J:Type u} [Fintype J]
    (v:J→V) (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (P:FiniteHomotopyClass Q (K:=K)→Prop)
    (hstep:∀ a x,P x→P (classPositiveTwist Q (v a) x))
    (x:FiniteHomotopyClass Q (K:=K)) (hx:P x) : P (classPacketPerm Q hn v hv x) := by
  have he:classPacketPerm Q hn v hv x=
      classOfComplex Q ((minimalClassModel Q x).complex.packetTwist Q v) := by
    conv_lhs => rw [← minimalClassModel_class Q x,classPacketPerm_apply]
  rw [he]
  have hxx:classOfComplex Q (minimalClassModel Q x).complex=x:=minimalClassModel_class Q x
  exact classOfComplex_packet_preserves Q _ P (by rwa [hxx]) v hv hstep

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveWordActionAppend
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  (hn:∀ a,Q.source a≠Q.target a)

lemma classPacketPerm_positiveWord {J:Type u} [Fintype J] (v:J→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)) :
    ∃ w:List V,(∀ a∈w,∃ j,v j=a) ∧ ∀ x:FiniteHomotopyClass Q (K:=K),
      positiveWordAction Q w x=classPacketPerm Q hn v hv x := by
  suffices hh:∀ (J:Type u) [Fintype J] (v:J→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)),
    ∃ w:List V,(∀ a∈w,∃ j,v j=a) ∧ ∀ x:FiniteHomotopyClass Q (K:=K),
      positiveWordAction Q w x=classPacketPerm Q hn v hv x from hh J v hv
  intro J inst
  apply Fintype.induction_empty_option (P:=fun J _=>∀ (v:J→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)),
    ∃ w:List V,(∀ a∈w,∃ j,v j=a) ∧ ∀ x:FiniteHomotopyClass Q (K:=K),
      positiveWordAction Q w x=classPacketPerm Q hn v hv x) _ _ _ J
  · intro J L instL e ih
    let := Fintype.ofEquiv L e.symm
    intro v hv
    obtain ⟨w,hw,h⟩:=ih (v∘e) (fun a b hab=>hv (fun he=>hab (e.injective he)))
    refine ⟨w,fun a ha=>?_,?_⟩
    · obtain ⟨j,hj⟩:=hw a ha
      exact ⟨e j,hj⟩
    · intro x
      rw [classPacketPerm_reindex Q hn v hv e]
      exact h x
  · intro v hv
    refine ⟨[],by simp,?_⟩
    intro x
    rw [classPacketPerm_empty]
    rfl
  · intro J inst ih v hv
    obtain ⟨w,hw,h⟩:=ih (v∘some) (fun a b hab=>hv (fun he=>hab (Option.some.inj he)))
    refine ⟨v none::w,?_,?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with he|ha
      · exact ⟨none,he.symm⟩
      · obtain ⟨j,hj⟩:=hw a ha
        exact ⟨some j,hj⟩
    · intro x
      rw [classPacketPerm_cons]
      change classPositiveTwist Q (v none) (positiveWordAction Q w x)=_
      rw [h]
      rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_Cone2
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

omit [Fintype V] [DecidableEq A] in
lemma ClassCone.ofMap {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J} (f:Map Q E F) :
    ClassCone Q (classOfComplex Q E) (classOfComplex Q F) (classOfComplex Q (f.cone Q)) :=
  ⟨FiniteModel.ofComplex Q E,FiniteModel.ofComplex Q F,f,rfl,rfl,rfl⟩

lemma ClassCone.positive {x y z:FiniteHomotopyClass Q (K:=K)} (h:ClassCone Q x y z) (α:V) :
    ClassCone Q (classPositiveTwist Q α x) (classPositiveTwist Q α y) (classPositiveTwist Q α z) := by
  obtain ⟨E,F,f,rfl,rfl,rfl⟩:=h
  refine ⟨FiniteModel.ofComplex Q (E.complex.positiveTwist Q α),
    FiniteModel.ofComplex Q (F.complex.positiveTwist Q α),f.positiveTwist Q α,rfl,rfl,?_⟩
  have coneIso : ChainIsomorphism Q ((f.cone Q).positiveTwist Q α)
      ((f.positiveTwist Q α).cone Q) := by
    convert positiveTwistCone Q f α using 1
    all_goals try with_reducible_and_instances rfl
  exact (classOfComplex_eq Q (coneIso.toHomotopyEquivalence Q)).symm

lemma ClassCone.positiveWord {x y z:FiniteHomotopyClass Q (K:=K)}
    (h:ClassCone Q x y z) (w:List V) :
    ClassCone Q (positiveWordAction Q w x) (positiveWordAction Q w y) (positiveWordAction Q w z) := by
  induction w with
  | nil=>exact h
  | cons α w ih=>exact ih.positive Q α

lemma ClassCone.packet {x y z:FiniteHomotopyClass Q (K:=K)}
    (h:ClassCone Q x y z) (hn:∀ a,Q.source a≠Q.target a)
    {P:Type u} [Fintype P] (v:P→V) (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)) :
    ClassCone Q (classPacketPerm Q hn v hv x) (classPacketPerm Q hn v hv y)
      (classPacketPerm Q hn v hv z) := by
  obtain ⟨w,_,hw⟩:=classPacketPerm_positiveWord Q (K:=K) hn v hv
  simpa only [hw] using h.positiveWord Q w

omit [Fintype V] [DecidableEq A] in
lemma ClassCone.layer_eq {x y z:FiniteHomotopyClass Q (K:=K)}
    (h:ClassCone Q x y z) (q:ℤ)
    (hz:∀ i,((minimalClassModel Q z).complex.placement i).level≠q-1 ∧
      ((minimalClassModel Q z).complex.placement i).level≠q) :
    classLayer Q q x=classLayer Q q y := by
  obtain ⟨E,F,f,hE,hF,hz'⟩:=h
  have he:classOfComplex Q (f.cone Q)=classOfComplex Q (minimalClassModel Q z).complex:=
    hz'.trans (minimalClassModel_class Q z).symm
  obtain ⟨e⟩:=Quotient.exact he
  rw [← hE,← hF]
  exact classLayer_eq_of_cone_equivalence Q f _ e q hz

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HighConeRetainedPure
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma top_zero_regraded (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (e:I≃J) (n:ℤ) (r:K) (hr:r≠0)
    (hc:∀ i,(F.placement (e i)).color=(E.placement i).color)
    (hd:∀ i,(F.placement (e i)).cochain=(E.placement i).cochain+n)
    (hf:∀ i j a,(F.differential (e i) (e j)).arrow a=r*(E.differential i j).arrow a)
    (α:V) (hz:∀ c,coefficientTopDual Q E α c=⊥) :
    ∀ c,coefficientTopDual Q F α c=⊥ := by
  intro c
  apply le_antisymm _ bot_le
  intro x hx
  have hy:(fun i=>x (e i))∈coefficientTopDual Q E α (c-n) := by
    constructor
    · intro i hi
      apply hx.1 (e i)
      rcases hi with hi|hi
      · exact Or.inl (by rwa [hc])
      · exact Or.inr (by rw [hd]; omega)
    · intro i a
      apply (mul_eq_zero.mp (show r*(∑ j:I,(E.differential i j).arrow a*x (e j))=0 from ?_)).resolve_left hr
      calc
        r*(∑ j:I,(E.differential i j).arrow a*x (e j))=
            ∑ j:I,(F.differential (e i) (e j)).arrow a*x (e j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [hf i j a]
          ring
        _ = ∑ j:J,(F.differential (e i) j).arrow a*x j := e.sum_comp (fun j:J=>(F.differential (e i) j).arrow a*x j)
        _ = 0 := hx.2 (e i) a
  rw [hz] at hy
  have hy':(fun i=>x (e i))=0:=(Submodule.mem_bot K).mp hy
  apply (Submodule.mem_bot K).mpr
  funext j
  obtain ⟨i,rfl⟩:=e.surjective j
  exact congrFun hy' i

omit [Fintype V] [DecidableEq A] in
lemma highConeRetained_top_zero (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (α:V)
    (ht:∀ c,coefficientTopDual Q (E.pureLayer Q hE (q-1)) α c=⊥) :
    ∀ c,coefficientTopDual Q
      (((highConePivot Q E _ (levelDownClosed Q E hE (q-1))).reduced Q).pureLayer Q
        (highConeRetained_minimal Q E hE _ _) (q-2)) α c=⊥ := by
  apply top_zero_regraded Q (E.pureLayer Q hE (q-1)) _
    (highConeRetainedPureIndex Q E hE q) (-1) (-1) (neg_ne_zero.mpr one_ne_zero)
    (fun _=>rfl) (fun i=>by
      change (E.placement i).cochain-1=(E.placement i).cochain+ -1
      omega) _ α ht
  intro i j a
  change (((highConePivot Q E _ (levelDownClosed Q E hE (q-1))).reduced Q).differential
    (highConeRetainedPureIndex Q E hE q i).val
    (highConeRetainedPureIndex Q E hE q j).val).arrow a= -1*(E.differential i j).arrow a
  rw [highConeRetained_differential]
  change -(E.differential i j).arrow a= -1*(E.differential i j).arrow a
  ring

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HighDualCycleZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
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

omit [Fintype V] [DecidableEq A] in
lemma high_dual_cycle_zero (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (e:HomotopyEquivalence Q E F) (α:V) (l:ℤ)
    (hE:∀ i,(E.placement i).level≤l) (hF:∀ j,(F.placement j).level<l)
    (x:I→K) (hx:∀ i,(E.placement i).level≠l ∨ (E.placement i).color≠α → x i=0)
    (hd:(E.differential.map (vertexHom Q α)).mulVec x=0) : x=0 := by
  let f:=e.forward.matrix.map (vertexHom Q α)
  let b:=e.backward.matrix.map (vertexHom Q α)
  let h:=e.sourceHomotopy.map (vertexHom Q α)
  let dE:=E.differential.map (vertexHom Q α)
  have hb:b.mulVec x=0 := by
    funext j
    apply Finset.sum_eq_zero
    intro i _
    change (e.backward.matrix j i).vertex α*x i=0
    by_cases hm:(e.backward.matrix j i).vertex α=0
    · rw [hm,MulZeroClass.zero_mul]
    obtain ⟨_,_,hc,hu⟩:=degree_vertex_support Q e.backward.entries e.backward.degree j i α hm
    have hi:(E.placement i).level≠l := by
      have hj:=hF j
      dsimp only [GeneratorPlacement.level] at *
      omega
    rw [hx i (Or.inl hi),MulZeroClass.mul_zero]
  have hh:h.mulVec x=0 := by
    funext j
    apply Finset.sum_eq_zero
    intro i _
    change (e.sourceHomotopy j i).vertex α*x i=0
    by_cases hm:(e.sourceHomotopy j i).vertex α=0
    · rw [hm,MulZeroClass.zero_mul]
    obtain ⟨_,_,hc,hu⟩:=degree_vertex_support Q e.sourceEntries e.sourceDegree j i α hm
    have hi:(E.placement i).level≠l := by
      have hj:=hE j
      dsimp only [GeneratorPlacement.level] at *
      omega
    rw [hx i (Or.inl hi),MulZeroClass.mul_zero]
  have hid:((projectiveIdentity Q E.placement).map (vertexHom Q α)).mulVec x=x := by
    funext i
    simp only [Matrix.mulVec,Matrix.map_apply,dotProduct,projectiveIdentity,Matrix.diagonal_apply]
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left rfl]
      change (vertexId Q (E.placement i).color).vertex α*x i=x i
      by_cases hi:(E.placement i).color=α
      · simp [hi,vertexId_eval]
      · rw [hx i (Or.inr hi),MulZeroClass.mul_zero]
    · intro j _ hj
      simp [Ne.symm hj,vertexHom]
    · simp
  have he:f*b=(projectiveIdentity Q E.placement).map (vertexHom Q α)+dE*h+h*dE := by
    simpa only [Matrix.map_mul,Matrix.map_add _ (map_add _),← add_assoc] using congrArg
      (fun M:Matrix I I (Q.Zigzag K)=>M.map (vertexHom Q α)) e.sourceEquation
  have hz:=congrArg (fun M:Matrix I I K=>M.mulVec x) he
  rw [← Matrix.mulVec_mulVec, hb,Matrix.mulVec_zero,Matrix.add_mulVec,Matrix.add_mulVec,
    hid,← Matrix.mulVec_mulVec,hh,Matrix.mulVec_zero,← Matrix.mulVec_mulVec,hd,
    Matrix.mulVec_zero,_root_.add_zero,_root_.add_zero] at hz
  exact hz.symm

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

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma totalHomDimension_eq_sum_of_subset (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (t : ℤ) (D : Finset ℤ)
    (hD : homInternalSupport Q E F ⊆ D) :
    totalHomDimension Q E F t = ∑ v ∈ D, homDimension Q E F (t-v) v := by
  unfold totalHomDimension
  apply Finset.sum_subset hD
  intro v _ hv
  exact homDimension_off_internal_support Q E F (t-v) v hv

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

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] [DecidableEq T] in
lemma totalHomDimension_le_of_pointwise (M:BasedComplex Q (K:=K) T)
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J) (a b:ℤ)
    (h:∀ v,homDimension Q M E (a-v) v ≤ homDimension Q M F (b-v) v) :
    totalHomDimension Q M E a ≤ totalHomDimension Q M F b := by
  classical
  let D:=homInternalSupport Q M E ∪ homInternalSupport Q M F
  rw [totalHomDimension_eq_sum_of_subset Q M E a D Finset.subset_union_left,
    totalHomDimension_eq_sum_of_subset Q M F b D Finset.subset_union_right]
  exact Finset.sum_le_sum (fun v _=>h v)

omit [DecidableEq I] [DecidableEq J] in
lemma cappedSummand_total_bound (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (hE:E.IsMinimal Q) (hF:F.IsMinimal Q)
    (M:BasedComplex Q (K:=K) T) (U:Set V) (q d:ℤ)
    (hM:∀ i,(M.placement i).level=q) (hU:∀ i,(M.placement i).color∈U)
    (ι:Map Q M (E.pureLayer Q hE q)) (π:Map Q (E.pureLayer Q hE q) M)
    (hret:ι.matrix*π.matrix=projectiveIdentity Q M.placement)
    (hcap:E.CappedOn Q U q)
    (hzero:∀ n v,n+v=d-q → homDimension Q E F n v=0) :
    totalHomDimension Q M (F.pureLayer Q hF d) (d-q) ≤
      totalHomDimension Q (F.pureLayer Q hF (d-1)) M (q-d+1) := by
  have hb:totalHomDimension Q M (F.pureLayer Q hF d) (d-q) ≤
      totalHomDimension Q M (F.pureLayer Q hF (d-1)) (d-q+1) := by
    apply totalHomDimension_le_of_pointwise Q
    intro v
    have f:=cappedSummandInjection Q E F hE hF M U q d (d-q-v) v hM hU ι π
      hret hcap (hzero _ _ (by omega)) (by omega)
    have h:=LinearMap.finrank_le_finrank_of_injective f.property
    change homDimension Q M (F.pureLayer Q hF d) (d-q-v) v ≤
      homDimension Q M (F.pureLayer Q hF (d-1)) (d-q-v+1) v at h
    simpa only [show d-q-v+1=d-q+1-v by omega] using h
  rw [totalHomDimension_dual Q M (F.pureLayer Q hF (d-1)) (d-q+1)] at hb
  simpa only [show 2-(d-q+1)=q-d+1 by omega] using hb

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InitialHomSpaceNegative
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma initial_homSpace_negative (α β : V) (n v : ℤ) (h : n + v < 0) :
    homSpace Q (initialProjective Q (K := K) α) (initialProjective Q β) n v = ⊥ := by
  by_cases hn : n = 0
  · apply le_antisymm _ bot_le
    intro f hf
    change f = 0
    apply Matrix.ext
    intro i j
    have hh : Homogeneous Q v (f i j) := by
      simpa only [initialProjective, add_zero, sub_zero] using (hf.2 i j).2
    have hv : v < 0 := by omega
    apply Zigzag.ext
    · exact hh.1 (by omega)
    · exact hh.2.1 (by omega)
    · exact hh.2.2 (by omega)
  · exact initial_homSpace_nonzero_cochain Q α β n v hn

lemma frameModel_negative_pair_homDimension (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M) (α β : V)
    (n v : ℤ) (h : n + v < 0) :
    homDimension Q (frameModel Q (K := K) hn M hM x α).complex
      (frameModel Q hn M hM x β).complex n v = 0 := by
  rw [frameModel, frameModel, minimalClassModel_homDimension, unfoldedFrame_homDimension]
  exact homDimension_zero_of_homSpace_zero Q _ _ n v (initial_homSpace_negative Q α β n v h)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_ClosedNeighborhood
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

end Zigzag.BasedComplex
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_NegativeTwistModern
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LayerSocleDimensionLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

lemma classLayerSocleDimension_layer (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) (α:V) (c:ℤ) :
    classLayerSocleDimension Q q α c (classLayer Q q x)=classLayerSocleDimension Q q α c x := by
  let E:=((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) q)
  have hE:∀ i,(E.placement i).level=q:=fun i=>i.property
  change classLayerSocleDimension Q q α c (classOfComplex Q E)=Module.finrank K (coefficientSocle Q E α c)
  rw [classLayerSocleDimension_minimal Q E (pure_minimal Q E hE)]
  exact ((pureLayerSelf Q E hE).coefficientSocle Q hE (fun i=>i.property) α c).finrank_eq.symm

lemma classLayerTopDimension_layer (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) (α:V) (c:ℤ) :
    classLayerTopDimension Q q α c (classLayer Q q x)=classLayerTopDimension Q q α c x := by
  let E:=((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) q)
  have hE:∀ i,(E.placement i).level=q:=fun i=>i.property
  change classLayerTopDimension Q q α c (classOfComplex Q E)=Module.finrank K (coefficientTopDual Q E α c)
  rw [classLayerTopDimension_minimal Q E (pure_minimal Q E hE)]
  exact ((pureLayerSelf Q E hE).coefficientTopDual Q hE (fun i=>i.property) α c).finrank_eq.symm

omit [Fintype V] [DecidableEq A] in
lemma classLayer_lowerTruncation_le (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (d q:ℤ) (hd:d≤q) :
    classLayer Q d (classOfComplex Q (lowerTruncation Q E hE q))=
      classLayer Q d (classOfComplex Q E) := by
  apply classLayer_eq_of_cone_equivalence Q (lowInclusion Q E _ (levelDownClosed Q E hE q))
    (upperTruncation Q E hE q) (lowConeReduction Q E _ _) d
  intro j
  have hj:=j.property
  change ¬(E.placement j).level≤q at hj
  change (E.placement j).level≠d-1 ∧ (E.placement j).level≠d
  omega

lemma classLayerTopDimension_congr_layer {x y:FiniteHomotopyClass Q (K:=K)} (q:ℤ)
    (h:classLayer Q q x=classLayer Q q y) (α:V) (c:ℤ) :
    classLayerTopDimension Q q α c x=classLayerTopDimension Q q α c y := by
  rw [← classLayerTopDimension_layer Q x q α c,h,classLayerTopDimension_layer]

lemma classLayerSocleDimension_congr_layer {x y:FiniteHomotopyClass Q (K:=K)} (q:ℤ)
    (h:classLayer Q q x=classLayer Q q y) (α:V) (c:ℤ) :
    classLayerSocleDimension Q q α c x=classLayerSocleDimension Q q α c y := by
  rw [← classLayerSocleDimension_layer Q x q α c,h,classLayerSocleDimension_layer]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LayerSocleDimensionSum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type u} [Fintype I] [DecidableEq I]

lemma classLayerTopDimension_sum (x : I → FiniteHomotopyClass Q (K := K))
    (d : ℤ) (α : V) (c : ℤ) :
    classLayerTopDimension Q d α c (classSum Q x) =
      ∑ i, classLayerTopDimension Q d α c (x i) := by
  classical
  let E (i:I) := (minimalClassModel Q (x i)).complex
  have hE (i:I) : (E i).IsMinimal Q := minimalClassModel_minimal Q (x i)
  have hx : x = fun i => classOfComplex Q (E i) := by
    funext i
    exact (minimalClassModel_class Q (x i)).symm
  conv_lhs => rw [hx,classSum_complex]
  rw [classLayerTopDimension_minimal Q _ (finiteSum_minimal Q E hE)]
  rw [((sumLayerComparison Q E hE d).coefficientTopDual Q
    (fun i => i.property) (fun i => i.2.property) α c).finrank_eq]
  rw [(coefficientTopSumEquiv Q (fun i => (E i).pureLayer Q (hE i) d)
    (fun _ x => x.property) α c).finrank_eq,Module.finrank_pi_fintype]
  rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LevelArrayMinimalApply
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

lemma classLayerTopDimension_below (x:FiniteHomotopyClass Q (K:=K)) (b k:ℤ)
    (hb:ClassLowerBound Q b x) (hk:k<b) (α:V) (c:ℤ) :
    classLayerTopDimension Q k α c x=0 := by
  change Module.finrank K (coefficientTopDual Q
    ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) k) α c)=0
  have hz:coefficientTopDual Q
      ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) k) α c=⊥ := by
    apply eq_bot_iff.mpr
    intro functional _
    change functional=0
    funext i
    have hi:=hb i
    have he:=i.property
    change ((minimalClassModel Q x).complex.placement i.val).level=k at he
    omega
  rw [hz,finrank_bot]

lemma classLayerSocleDimension_below (x:FiniteHomotopyClass Q (K:=K)) (b k:ℤ)
    (hb:ClassLowerBound Q b x) (hk:k<b) (α:V) (c:ℤ) :
    classLayerSocleDimension Q k α c x=0 := by
  change Module.finrank K (coefficientSocle Q
    ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) k) α c)=0
  have hz:coefficientSocle Q
      ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) k) α c=⊥ := by
    apply eq_bot_iff.mpr
    intro functional _
    change functional=0
    funext i
    have hi:=hb i
    have he:=i.property
    change ((minimalClassModel Q x).complex.placement i.val).level=k at he
    omega
  rw [hz,finrank_bot]

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

lemma rowReflect_smul (C : Matrix V V ℝ) (α : V) (a : ℝ) (x : V → ℝ) :
    rowReflect C α (a • x)=a • rowReflect C α x := by
  simp only [rowReflect,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul,smul_sub,smul_smul]

lemma rowReflectWord_smul (C : Matrix V V ℝ) (w : List V) (a : ℝ) (x : V → ℝ) :
    rowReflectWord C w (a • x)=a • rowReflectWord C w x := by
  induction w with
  | nil => rfl
  | cons α w ih =>
    change rowReflect C α (rowReflectWord C w (a • x))=_
    rw [ih,rowReflect_smul]
    rfl

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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LowerTruncationLayerFloor
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma classLowerTruncation_eq_layer_of_floor (x:FiniteHomotopyClass Q (K:=K))
    (q:ℤ) (hx:ClassLowerBound Q q x) :
    classLowerTruncation Q q x=classLayer Q q x := by
  have hp:=classLayer_eq_self_of_bounds Q (classLowerTruncation Q q x) q
    (classLowerTruncation_floor Q q q x hx) (classLowerTruncation_cap Q q x)
  have hl:=classLayer_lowerTruncation Q (minimalClassModel Q x).complex
    (minimalClassModel_minimal Q x) q
  have hxx:classOfComplex Q (minimalClassModel Q x).complex=x:=minimalClassModel_class Q x
  rw [hxx] at hl
  exact hp.symm.trans hl

omit [Fintype V] [DecidableEq A] in
theorem classSignedVector_two_levels (x:FiniteHomotopyClass Q (K:=K))
    (q:ℤ) (hl:ClassLowerBound Q q x) (hh:ClassUpperBound Q (q+1) x) :
    classSignedVector Q x=cochainSign (K:=ℝ) q •
      (classTotalVector Q (classLayer Q q x)-classTotalVector Q (classLayer Q (q+1) x)) := by
  rw [classSignedVector_upper_partition Q x (q+1) hh]
  rw [show q+1-1=q by omega,classLowerTruncation_eq_layer_of_floor Q x q hl]
  rw [classSignedVector_pure Q _ q (classLayer_lowerBound Q x q) (classLayer_upperBound Q x q),
    classSignedVector_pure Q _ (q+1) (classLayer_lowerBound Q x (q+1)) (classLayer_upperBound Q x (q+1)),
    cochainSign_add_one,neg_smul,smul_sub,sub_eq_add_neg]

lemma classPacketPerm_upper_add_one {P:Type u} [Fintype P] [DecidableEq P]
    (hn:∀ a,Q.source a≠Q.target a) (v:P→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K:=K)) {q:ℤ} (hx:ClassUpperBound Q q x) :
    ClassUpperBound Q (q+1) (classPacketPerm Q hn v hv x) := by
  rw [← minimalClassModel_class Q x,classPacketPerm_apply]
  apply classUpperBound_of_representative Q
  intro i
  rcases i with ⟨b,i⟩|i
  · change ((minimalClassModel Q x).complex.placement i.1).cochain-1+
      (((minimalClassModel Q x).complex.placement i.1).internal+Path.length i.2.val)≤q+1
    have hi:=hx i.1
    have hl:Path.length i.2.val≤2:=by rcases Path.length_cases i.2.val with h|h|h <;> omega
    dsimp only [GeneratorPlacement.level] at hi
    omega
  · change ((minimalClassModel Q x).complex.placement i).level≤q+1
    have hi:=hx i
    omega

omit [Fintype V] [DecidableEq A] in
lemma classTotalVector_layer_nonneg (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) (α:V) :
    0 ≤ classTotalVector Q (classLayer Q q x) α := by
  rw [classTotalVector_layer_apply]
  exact Nat.cast_nonneg _

omit [Fintype V] [DecidableEq A] in
lemma classUpperBound_of_upper_layer_zero (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hh:ClassUpperBound Q (q+1) x)
    (hz:classTotalVector Q (classLayer Q (q+1) x)=0) : ClassUpperBound Q q x := by
  intro i
  have hi:=hh i
  by_contra hn
  have he:((minimalClassModel Q x).complex.placement i).level=q+1 := by omega
  have hc:=congrFun hz ((minimalClassModel Q x).complex.placement i).color
  rw [classTotalVector_layer_apply] at hc
  have hc0:classLevelArray Q x (((minimalClassModel Q x).complex.placement i).color,q+1)=0 :=
    by simpa only [Nat.cast_eq_zero,Pi.zero_apply] using hc
  have harr:classLevelArray Q x=(minimalClassModel Q x).complex.levelArray Q := by
    have hmodel : classOfComplex Q (minimalClassModel Q x).complex=x := minimalClassModel_class Q x
    exact (congrArg (classLevelArray Q) hmodel).symm.trans
      (classLevelArray_complex_minimal Q (minimalClassModel Q x).complex (minimalClassModel_minimal Q x))
  rw [harr] at hc0
  rw [levelArray_apply,Nat.card_eq_fintype_card] at hc0
  have hp:0<Fintype.card {j : (minimalClassModel Q x).Index //
      ((minimalClassModel Q x).complex.placement j).color=((minimalClassModel Q x).complex.placement i).color ∧
      ((minimalClassModel Q x).complex.placement j).level=q+1} :=
    Fintype.card_pos_iff.mpr ⟨⟨i,rfl,he⟩⟩
  rw [hc0] at hp
  exact Nat.lt_irrefl _ hp

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PacketLayerLowerTruncation
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
  {I P:Type u} [Fintype I] [Fintype P] [DecidableEq I] [DecidableEq P]
  (hn:∀ a,Q.source a≠Q.target a) (v:P→V)
  (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
local notation "T" => classPacketPerm Q hn v hv

omit [DecidableEq P] in
lemma packetLayer_lowerTruncation (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (q:ℤ) :
    classLayer Q q (T (classOfComplex Q (lowerTruncation Q E hE q)))=
      classLayer Q q (T (classOfComplex Q E)) := by
  let f:=lowInclusion Q E _ (levelDownClosed Q E hE q)
  let R:=upperTruncation Q E hE q
  have hc:=ClassCone.ofMap Q f
  have he:classOfComplex Q (f.cone Q)=classOfComplex Q R:=
    classOfComplex_eq Q (lowConeReduction Q E _ (levelDownClosed Q E hE q))
  rw [he] at hc
  have hr:ClassLowerBound Q (q+1) (classOfComplex Q R):=by
    apply classLowerBound_of_representative Q
    intro i
    have hi:=i.property
    change ¬(E.placement i).level≤q at hi
    change q+1≤(E.placement i).level
    omega
  have hb:=classPacketPerm_lower_bound Q hn v hv (classOfComplex Q R) hr
  exact (hc.packet Q hn v hv).layer_eq Q q (fun i=>by have hi:=hb i; constructor <;> omega)

lemma packetLayer_top (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (hhi:∀ i,(E.placement i).level≤q)
    (ht:∀ a c,coefficientTopDual Q (E.pureLayer Q hE (q-1)) (v a) c=⊥) :
    classLayer Q q (T (classOfComplex Q E))=
      classLayer Q q (T (classLayer Q q (classOfComplex Q E))) := by
  let f:=highProjection Q E _ (levelDownClosed Q E hE (q-1))
  let D:=(highConePivot Q E _ (levelDownClosed Q E hE (q-1))).reduced Q
  have hD:D.IsMinimal Q:=highConeRetained_minimal Q E hE _ _
  have hd:ClassUpperBound Q (q-2) (classOfComplex Q D) := by
    apply classUpperBound_of_representative Q
    intro i
    rw [highConeRetained_level]
    have hi:=i.property
    change (E.placement i).level≤q-1 at hi
    omega
  have htop:∀ a c,classLayerTopDimension Q (q-2) (v a) c (classOfComplex Q D)=0 := by
    intro a c
    rw [classLayerTopDimension_minimal Q D hD]
    rw [highConeRetained_top_zero Q E hE q (v a) (ht a),finrank_bot]
  have hb:=classPacketPerm_cap_of_top_zero Q hn v hv (classOfComplex Q D) hd htop
  have hc:=ClassCone.ofMap Q f
  have he:classOfComplex Q (f.cone Q)=classOfComplex Q D:=
    classOfComplex_eq Q (highConeReduction Q E _ (levelDownClosed Q E hE (q-1)))
  rw [he] at hc
  have hh:classLayer Q q (T (classOfComplex Q E))=
      classLayer Q q (T (classOfComplex Q (upperTruncation Q E hE (q-1)))):=
    (hc.packet Q hn v hv).layer_eq Q q (fun i=>by have hi:=hb i; constructor <;> omega)
  rwa [highRestriction_top_eq_layer Q E hE q hhi] at hh

theorem classPacketPerm_unshifted_layer (x:FiniteHomotopyClass Q (K:=K))
    (q:ℤ) (ht:∀ a c,classLayerTopDimension Q (q-1) (v a) c x=0) :
    classLayer Q q (T x)=classLayer Q q (T (classLayer Q q x)) := by
  let E:=(minimalClassModel Q x).complex
  have hE:E.IsMinimal Q:=minimalClassModel_minimal Q x
  have hx:classOfComplex Q E=x:=minimalClassModel_class Q x
  let L:=lowerTruncation Q E hE q
  have hL:L.IsMinimal Q:=lowerTruncation_minimal Q E hE q
  have hl:classLayer Q (q-1) (classOfComplex Q L)=classLayer Q (q-1) x := by
    exact (classLayer_lowerTruncation_le Q E hE (q-1) q (by omega)).trans
      (congrArg (classLayer Q (q-1)) hx)
  have htL:∀ a c,coefficientTopDual Q (L.pureLayer Q hL (q-1)) (v a) c=⊥ := by
    intro a c
    apply Submodule.finrank_eq_zero.mp
    rw [← classLayerTopDimension_minimal Q L hL]
    rw [classLayerTopDimension_congr_layer Q (q-1) hl (v a) c,ht a c]
  have hh:=packetLayer_top Q hn v hv L hL q (fun i=>i.property) htL
  have hp:=packetLayer_lowerTruncation Q hn v hv E hE q
  rw [classLayer_lowerTruncation_le Q E hE q q le_rfl,hx] at hh
  rw [hx] at hp
  exact hp.symm.trans hh

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PacketPermPreservesOpen
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

theorem classPacketPerm_preserves_open_socle
    (hn:∀ a,Q.source a≠Q.target a) {P:Type u} [Fintype P]
    (v:P→V) (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (J:Set V) (hJ:∀ a,v a∈J) (x:FiniteHomotopyClass Q (K:=K)) {d:ℤ}
    (hx:ClassLowerBound Q d x) (hs:ClassBottomSocleZero Q d J x) :
    ClassBottomSocleZero Q d J (classPacketPerm Q hn v hv x) := by
  have hh:=classPacketPerm_preserves Q hn v hv
    (fun y=>ClassLowerBound Q d y ∧ ClassBottomSocleZero Q d J y)
    (fun a y hy=>⟨classPositiveTwist_lower_bound Q (v a) y hy.1,
      classPositiveTwist_preserves_open_socle Q hn (v a) J (hJ a) y hy.1 hy.2⟩)
    x ⟨hx,hs⟩
  exact hh.2

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PacketTwistRaisedGenerator2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J P : Type u} [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq I] [DecidableEq J] [DecidableEq P]

theorem packetTwist_raised_generator_top_at_local_cap
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    {l : ℤ} (U:Set V)
    (hE : ∀ i, (E.placement i).color∈Q.closedNeighborhood U → (E.placement i).level≤l)
    (v:P → V) (hv:∀ a,v a∈U)
    (hF : F.IsMinimal Q) (e : HomotopyEquivalence Q (E.packetTwist Q v) F)
    (j:J) (hj : (F.placement j).level=l+1)
    (hcol:(F.placement j).color∈Q.closedNeighborhood U) :
    ∃ a:P, ∃ x:I → K,
      x ∈ coefficientTopDual Q E (v a) ((F.placement j).cochain+1) ∧ x≠0 ∧
      ∀ i, (E.placement i).level≠l → x i=0 := by
  obtain ⟨x,hx,hxs,hxd⟩ := minimal_generator_dual_cycle Q (E.packetTwist Q v) F hF e j
  have hxold i : x (Sum.inr i)=0 := by
    apply hxs
    intro he
    have hl := congrArg GeneratorPlacement.level he
    change (E.placement i).level = (F.placement j).level at hl
    have hc: (E.placement i).color=(F.placement j).color := congrArg GeneratorPlacement.color he
    have hb := hE i (hc.symm ▸ hcol)
    rw [hj] at hl
    omega
  have hex : ∃ z, x z≠0 := not_forall.mp (fun h => hx (funext h))
  obtain ⟨⟨a,u⟩|i,hz⟩ := hex
  swap
  · exact (hz (hxold i)).elim
  have hp : (E.packetTwist Q v).placement (Sum.inl ⟨a,u⟩)=F.placement j :=
    Classical.not_not.mp (fun h => hz (hxs _ h))
  have hα : (F.placement j).color=v a := (congrArg GeneratorPlacement.color hp).symm
  let y : TestIndex Q E.placement (v a) → K := fun i => x (Sum.inl ⟨a,i⟩)
  have hplace (i : TestIndex Q E.placement (v a))
      (he : (E.packetTwist Q v).placement (Sum.inl ⟨a,i⟩)=F.placement j) :
      (E.placement i.1).cochain=(F.placement j).cochain+1 ∧
        Path.length i.2.val=2 ∧ (E.placement i.1).level=l := by
    have hc := congrArg GeneratorPlacement.cochain he
    have hu := congrArg GeneratorPlacement.internal he
    change (E.placement i.1).cochain-1=(F.placement j).cochain at hc
    change (E.placement i.1).internal+Path.length i.2.val=(F.placement j).internal at hu
    have hl := hE i.1 (Q.corner_target_mem_neighborhood (hv a) i.2)
    have hr : Path.length i.2.val≤2 := by
      rcases Path.length_cases i.2.val with h|h|h <;> omega
    dsimp only [GeneratorPlacement.level] at hl hj ⊢
    exact ⟨by omega,by omega,by omega⟩
  have hys i : ¬ ((E.placement i.1).cochain=(F.placement j).cochain+1 ∧
      Path.length i.2.val=2) → y i=0 := by
    intro hi
    apply hxs
    intro he
    exact hi ⟨(hplace i he).1,(hplace i he).2.1⟩
  have hyd : Matrix.vecMul y
      (testMatrix Q E.placement E.placement (v a) E.differential).transpose=0 := by
    funext i
    have hh := hxd (Sum.inl ⟨a,i⟩)
    rw [hα,Fintype.sum_sum_type,Fintype.sum_sigma] at hh
    have ht k : ((E.packetTwist Q v).differential (Sum.inl ⟨a,i⟩) (Sum.inl ⟨a,k⟩)).vertex (v a) =
        -testMatrix Q E.placement E.placement (v a) E.differential i k := by
      change (-(packetDifferential Q E.placement v E.differential) ⟨a,i⟩ ⟨a,k⟩).vertex (v a) = _
      rw [packetDifferential,Matrix.blockDiagonal'_apply_eq]
      change -(testMatrix Q E.placement E.placement (v a) E.differential i k *
        (vertexId Q (K := K) (v a)).vertex (v a)) = _
      simp [vertexId_eval]
    have htne b (hb:b≠a) (k:TestIndex Q E.placement (v b)) :
        ((E.packetTwist Q v).differential (Sum.inl ⟨a,i⟩) (Sum.inl ⟨b,k⟩)).vertex (v a)=0 := by
      change (-(packetDifferential Q E.placement v E.differential) ⟨a,i⟩ ⟨b,k⟩).vertex (v a) = _
      rw [packetDifferential,Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hb),neg_zero]
      rfl
    rw [Finset.sum_eq_single a] at hh
    · simp only [ht,hxold,MulZeroClass.mul_zero,Finset.sum_const_zero,add_zero,
        neg_mul,Finset.sum_neg_distrib,neg_eq_zero] at hh
      simpa only [Matrix.vecMul,Matrix.transpose_apply,dotProduct,mul_comm,Pi.zero_apply] using hh
    · intro b hb hba
      simp only [htne b hba,MulZeroClass.zero_mul,Finset.sum_const_zero]
    · simp
  have hy : y ∈ topTestCycles Q E (v a) ((F.placement j).cochain+1) := ⟨hys,hyd⟩
  refine ⟨a,sumTokenTest Q E.placement (v a) y, sumTokenTest_top Q E (v a) _ hy, ?_, ?_⟩
  · intro hzero
    have hyz : y=0 := by
      rw [← tokenTestVector_sum Q E.placement (v a) _ y hys,hzero,map_zero]
    exact hz (congrFun hyz u)
  · intro i hi
    apply Finset.sum_eq_zero
    intro z hz
    apply hxs
    intro he
    exact hi (hplace ⟨i,z⟩ he).2.2

theorem packetTwist_local_cap_of_top_zero
    (E : BasedComplex Q (K := K) I) (hmin : E.IsMinimal Q) {l : ℤ}
    (U:Set V)
    (hE : ∀ i, (E.placement i).color∈Q.closedNeighborhood U → (E.placement i).level≤l)
    (v:P → V) (hv:∀ a,v a∈U)
    (htop : ∀ a c, coefficientTopDual Q (E.pureLayer Q hmin l) (v a) c=⊥) :
    ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
      Nonempty (HomotopyEquivalence Q (E.packetTwist Q v) F.complex) ∧
      ∀ j, (F.complex.placement j).color∈Q.closedNeighborhood U →
        (F.complex.placement j).level≤l := by
  let B := FiniteModel.ofComplex Q (E.packetTwist Q v)
  obtain ⟨F,hF,⟨e⟩,f,hf⟩ := B.exists_minimal_embedding Q
  refine ⟨F,hF,⟨e⟩,?_⟩
  intro j hcol
  by_contra hb
  have hj : (F.complex.placement j).level=l+1 := by
    have hmax : (F.complex.placement j).level≤l+1 := by
      rw [hf j] at hcol ⊢
      change ((E.packetTwist Q v).placement (f j)).color∈Q.closedNeighborhood U at hcol
      change ((E.packetTwist Q v).placement (f j)).level≤l+1
      generalize he:f j=k at hcol ⊢
      rcases k with ⟨a,i,p⟩|i
      · change ((E.placement i).cochain-1)+((E.placement i).internal+Path.length p.val)≤l+1
        have hh := hE i (Q.corner_target_mem_neighborhood (hv a) p)
        have hr : Path.length p.val≤2 := by
          rcases Path.length_cases p.val with h|h|h <;> omega
        dsimp only [GeneratorPlacement.level] at hh
        omega
      · have hh := hE i hcol
        change (E.placement i).level≤l+1
        omega
    omega
  obtain ⟨a,x,hx,hxz,hs⟩ := packetTwist_raised_generator_top_at_local_cap Q E F.complex U hE v hv hF e j hj hcol
  have hm := coefficientTopDual_restrict_layer Q E hmin l (v a) _ hx hs
  have hn := coefficientTopDual_restrict_layer_ne_zero Q E l hxz hs
  rw [htop] at hm
  exact hn ((Submodule.mem_bot K).mp hm)

theorem classPacketPerm_local_cap_of_top_zero
    (hn:∀ a,Q.source a≠Q.target a) (v:P→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) {l:ℤ}
    (hcap:ClassCapOn Q x (Q.closedNeighborhood U) l) (hU:∀ a,v a∈U)
    (htop:∀ a c,classLayerTopDimension Q l (v a) c x=0) :
    ClassCapOn Q (classPacketPerm Q hn v hv x) (Q.closedNeighborhood U) l := by
  let E:=minimalClassModel Q x
  have hE:E.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  have ht:∀ a c,coefficientTopDual Q (E.complex.pureLayer Q hE l) (v a) c=⊥ := by
    intro a c
    exact Submodule.finrank_eq_zero.mp (htop a c)
  obtain ⟨F,hF,⟨e⟩,hb⟩:=packetTwist_local_cap_of_top_zero Q E.complex hE U hcap v hU ht
  have hh:ClassCapOn Q (classOfComplex Q F.complex) (Q.closedNeighborhood U) l :=
    minimal_bound_transport Q F.complex _ (minimalClassModel_minimal Q _)
      (minimalClassModelEquivalence Q F.complex).symm (fun p=>p.color∈Q.closedNeighborhood U→p.level≤l) hb
  have hx:classPacketPerm Q hn v hv x=classOfComplex Q F.complex := by
    rw [← minimalClassModel_class Q x,classPacketPerm_apply]
    exact classOfComplex_eq Q e
  rw [hx]
  exact hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PacketTwistTopZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J P:Type u} [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq I] [DecidableEq J] [DecidableEq P]

theorem packetTwist_top_zero_of_cap
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (q:ℤ) (hE:∀ i,(E.placement i).level=q) (v:P→V)
    (e:HomotopyEquivalence Q (E.packetTwist Q v) F)
    (hF:∀ j,(F.placement j).level≤q) :
    ∀ a c,coefficientTopDual Q E (v a) c=⊥ := by
  intro a c
  apply eq_bot_iff.mpr
  intro x hx
  change x=0
  let t:=tokenTestVector Q E.placement (v a) x
  have ht:t∈topTestCycles Q E (v a) c:=tokenTestVector_top Q E hE (v a) c hx
  let z':∀ b:P,TestIndex Q E.placement (v b)→K:=Pi.single a t
  let z:PacketIndex Q E.placement v→K:=fun b=>z' b.1 b.2
  let y:PacketIndex Q E.placement v⊕I→K:=Sum.elim z (fun _=>0)
  have hz:∀ (b:P) (i:TestIndex Q E.placement (v b)),b≠a→z ⟨b,i⟩=0 := by
    intro b i h
    simp [z,z',Pi.single_eq_of_ne h]
  have hza:∀ i,z ⟨a,i⟩=t i := by intro i; simp [z,z']
  have hy:y=0 := by
    apply high_dual_cycle_zero Q (E.packetTwist Q v) F e (v a) (q+1)
    · intro i
      rcases i with ⟨b,i⟩|i
      · change (E.placement i.1).cochain-1+((E.placement i.1).internal+Path.length i.2.val)≤q+1
        have hi:=hE i.1
        have hl:Path.length i.2.val≤2:=by rcases Path.length_cases i.2.val with h|h|h <;> omega
        dsimp only [GeneratorPlacement.level] at hi
        omega
      · change (E.placement i).level≤q+1
        rw [hE]; omega
    · intro j
      have hj:=hF j
      omega
    · intro i hi
      rcases i with ⟨b,i⟩|i
      · change z ⟨b,i⟩=0
        by_cases hb:b=a
        · subst b
          rw [hza]
          apply ht.1
          intro hh
          apply hi.elim
          · intro h
            apply h
            change (E.placement i.1).cochain-1+((E.placement i.1).internal+Path.length i.2.val)=q+1
            have hq:=hE i.1
            dsimp only [GeneratorPlacement.level] at hq
            omega
          · intro h
            exact h rfl
        · exact hz b i hb
      · rfl
    · funext i
      rcases i with ⟨b,i⟩|i
      · change (∑ j:PacketIndex Q E.placement v⊕I,
          ((E.packetTwist Q v).differential (.inl ⟨b,i⟩) j).vertex (v a)*y j)=0
        rw [Fintype.sum_sum_type]
        simp only [y,Sum.elim_inl,Sum.elim_inr,MulZeroClass.mul_zero,Finset.sum_const_zero,_root_.add_zero]
        rw [Fintype.sum_sigma,Finset.sum_eq_single a]
        · simp only [hza]
          by_cases hb:b=a
          · subst b
            have hh:=congrFun ht.2 i
            change (∑ j,t j * testMatrix Q E.placement E.placement (v a) E.differential i j)=0 at hh
            have hm j:((E.packetTwist Q v).differential (.inl ⟨a,i⟩) (.inl ⟨a,j⟩)).vertex (v a) =
                -testMatrix Q E.placement E.placement (v a) E.differential i j := by
              change (-packetDifferential Q E.placement v E.differential ⟨a,i⟩ ⟨a,j⟩).vertex (v a)=_
              rw [packetDifferential,Matrix.blockDiagonal'_apply_eq]
              change -(testMatrix Q E.placement E.placement (v a) E.differential i j *
                (vertexId Q (K:=K) (v a)).vertex (v a)) = _
              rw [vertexId_eval,ite_eq_left rfl,_root_.mul_one]
            simp only [hm,_root_.neg_mul,Finset.sum_neg_distrib]
            rw [show (∑ j,testMatrix Q E.placement E.placement (v a) E.differential i j*t j)=0 from by
              simpa only [_root_.mul_comm] using hh,_root_.neg_zero]
          · apply Finset.sum_eq_zero
            intro j _
            change (-packetDifferential Q E.placement v E.differential ⟨b,i⟩ ⟨a,j⟩).vertex (v a)*t j=0
            rw [packetDifferential,Matrix.blockDiagonal'_apply_ne _ _ _ hb]
            simp
        · intro b hb hba
          apply Finset.sum_eq_zero
          intro j _
          rw [hz b j hba,MulZeroClass.mul_zero]
        · simp
      · change (∑ j:PacketIndex Q E.placement v⊕I,
          ((E.packetTwist Q v).differential (.inr i) j).vertex (v a)*y j)=0
        rw [Fintype.sum_sum_type]
        simp [y,BasedComplex.packetTwist,Map.cone,Map.coneDifferential,Matrix.fromBlocks]
  have ht0:t=0:=funext fun i=>by simpa only [y,Sum.elim_inl,hza,Pi.zero_apply] using congrFun hy (.inl ⟨a,i⟩)
  have hr:=sumTokenTest_unit Q E.placement (v a) x (fun i hi=>hx.1 i (Or.inl hi))
  change sumTokenTest Q E.placement (v a) t=x at hr
  rw [ht0,map_zero] at hr
  exact hr.symm

theorem classPacketPerm_top_zero_of_layer_cap
    (hn:∀ a,Q.source a≠Q.target a) (v:P→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hh:ClassUpperBound Q q (classPacketPerm Q hn v hv (classLayer Q q x))) :
    ∀ a c,classLayerTopDimension Q q (v a) c x=0 := by
  let E:=(minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) q
  let y:=classPacketPerm Q hn v hv (classLayer Q q x)
  let F:=(minimalClassModel Q y).complex
  have he:classOfComplex Q (E.packetTwist Q v)=classOfComplex Q F := by
    have hp:=classPacketPerm_apply Q hn v hv (FiniteModel.ofComplex Q E)
    change classPacketPerm Q hn v hv (classOfComplex Q E)=
      classOfComplex Q (E.packetTwist Q v) at hp
    rw [← hp]
    exact (minimalClassModel_class Q y).symm
  obtain ⟨e⟩:=Quotient.exact he
  have ht:=packetTwist_top_zero_of_cap Q E F q (fun i=>i.property) v e hh
  intro a c
  change Module.finrank K (coefficientTopDual Q E (v a) c)=0
  rw [ht,finrank_bot]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_ComplexPureLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag Zigzag.BasedComplex

universe u
attribute [local instance] Classical.propDecidable
variable {V A W B : Type u} {K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R) [Field K] [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B]
  {I : Type u} [Fintype I] [DecidableEq I]

lemma classMap_topDimension (x:FiniteHomotopyClass Q (K := K)) (d:ℤ) (α:V) (c:ℤ) :
    classLayerTopDimension R d (e.vertex α) c (e.classMap x) =
      classLayerTopDimension Q d α c x := by
  let E := (minimalClassModel Q x).complex
  have hE := minimalClassModel_minimal Q x
  have hx : classOfComplex Q E = x := minimalClassModel_class Q x
  rw [← hx,classMap_complex,classLayerTopDimension_minimal Q E hE,
    classLayerTopDimension_minimal R (e.complex E) (e.complex_minimal hE),← e.complex_pureLayer]
  exact (e.coefficientTopDual (E.pureLayer Q hE d) (fun i => i.property) α c).finrank_eq.symm

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_HomDualSupportedCycles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
attribute [local instance] Classical.propDecidable
variable {V B J K T : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN
variable [Fintype T] [DecidableEq T]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)

local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

lemma coefficientTop_label_dimension
    (E : Zigzag.BasedComplex U (K := K) T) {l:ℤ}
    (hE : ∀ i, (E.placement i).level=l) (u:V) (c:J) (b:ℤ) :
    Module.finrank K (Zigzag.BasedComplex.coefficientTopDual U (C E) (u,c) b) =
      ∑ a : {a:J // N a c}, Module.finrank K (Zigzag.BasedComplex.coefficientTopDual U E (u,a) b) := by
  rw [(coefficientTopLabelEquiv Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE u c b).finrank_eq]
  exact Module.finrank_pi_fintype K

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_LayerIndexEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
universe u
attribute [local instance] Classical.propDecidable
variable {V B J : Type u} {K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN
open Zigzag.BasedComplex

variable (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

variable {T : Type u} [Fintype T] [DecidableEq T]

lemma classLayerTopDimension_label (d : ℤ) (x : FiniteHomotopyClass U (K := K))
    (v:V) (c:J) (b:ℤ) :
    classLayerTopDimension U d (v,c) b (F x) =
      ∑ a : {a:J // N a c}, classLayerTopDimension U d (v,a) b x := by
  let E := (minimalClassModel U x).complex
  have hE := minimalClassModel_minimal U x
  have hx : classOfComplex U E = x := minimalClassModel_class U x
  conv_lhs => rw [← hx,classLabel_complex]
  rw [classLayerTopDimension_minimal U (C E)
    (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE)]
  rw [((layerComparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE d).coefficientTopDual U
    (fun i => i.property) (fun i => i.1.property) (v,c) b).finrank_eq,
    coefficientTop_label_dimension Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
      (E.pureLayer U hE d) (fun i => i.property)]
  rfl

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_WordOrbitSocleAdjacency
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
universe u
attribute [local instance] Classical.propDecidable
variable {V B J : Type u} {K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
local notation "U" => Q.stringQuiver step hstep N hN
open Zigzag.BasedComplex

variable (hn : ∀ b, Q.source b ≠ Q.target b)
  (orient : B → Bool) (μ : J → K) (A : K)
  (ho : ∀ b, orient (Q.reverse b) = !(orient b))
  (hμ : ∀ a, μ a ≠ 0) (δ : K)
  (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
  (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "O" => (fun (w : List (V × Bool)) (s : V) (a : J) =>
  wordPacketPerm Q step hstep N hN hn w (initialClass U (K := K) (s,a)))

include ho hμ hA hroot hPF

lemma wordOrbit_top_adjacency (w : List (V × Bool)) (s v : V) (d b : ℤ) (i j : J) :
    (∑ a : {a // N a j}, classLayerTopDimension U d (v,a) b (O w s i)) =
      ∑ a : {a // N i a}, classLayerTopDimension U d (v,j) b (O w s a) := by
  rw [← classLayerTopDimension_label Q step hstep N hN orient μ A ho hμ δ hA hroot hPF]
  rw [classLabel_wordOrbit Q step hstep N hN hn orient μ A ho hμ δ hA hroot hPF,
    classLayerTopDimension_sum]

variable [Nonempty J]
  (hconn : ∀ a b, Relation.ReflTransGen N a b)
  (ρ : J → ℝ) (hρ : ∀ a, 0 < ρ a) (θ : ℝ)
  (hρPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, ρ b = θ * ρ a)

include hconn hρ hρPF

theorem wordOrbit_top_proportional (w : List (V × Bool)) (s v : V) (d b : ℤ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ j,
      (∑ i, ρ i * (classLayerTopDimension U d (v,j) b (O w s i) : ℝ)) = r * ρ j := by
  apply GraphConnection.nonnegative_eigenvector_proportional N hconn ρ hρ θ hρPF
  · exact GraphConnection.weighted_intertwiner N hN ρ θ hρPF _
      (wordOrbit_top_adjacency Q step hstep N hN hn orient μ A ho hμ δ hA hroot hPF w s v d b)
  · intro j
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (le_of_lt (hρ i)) (Nat.cast_nonneg _)

end HarmonicArtin.ReversibleQuiver.StringFunctor

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_StringAdjacent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

namespace ReversibleQuiver
variable {V B : Type} (Q : ReversibleQuiver V B)
  [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]

namespace StringFunctor
open Zigzag.BasedComplex

variable (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (hn : ∀ b, Q.source b ≠ Q.target b) (m : ℕ) (hm : 2 ≤ m)
local notation "N" => stringAdjacent m
local notation "hN" => stringAdjacent_symm m
local notation "U" => Q.stringQuiver step hstep N hN
local notation "O" => (fun (w : List (V × Bool)) (s : V) (a : StringLabel m) =>
  wordPacketPerm Q step hstep N hN hn w (initialClass U (K := ℂ) (s,a)))

include hm

include hn hm

theorem string_wordOrbit_top_proportional (w : List (V × Bool)) (s v : V) (d b : ℤ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ j,
      (∑ i, stringWeight m i * (classLayerTopDimension U d (v,j) b (O w s i) : ℝ)) =
        r * stringWeight m j := by
  have : NeZero (m-1) := ⟨by omega⟩
  obtain ⟨A,hA,hr,hμ,hPF⟩ := string_connection_exists m hm
  exact wordOrbit_top_proportional Q step hstep N hN hn Q.fixedOrientation
    (fun a => (stringWeight m a : ℂ)) A (Q.fixedOrientation_reverse hn) hμ
    (2 * Real.cos (Real.pi/m) : ℝ) hA hr hPF (stringAdjacent_connected m)
    (stringWeight m) (stringWeight_pos hm) _ (stringAdjacent_weight m hm) w s v d b

end StringFunctor
end ReversibleQuiver
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_RowReflectWordReverse
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionColorWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
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
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd
local notation "T" => fusionPacketPerm m d hd hdiag (K:=K)
local notation "hn" => fusionQuiver_no_loops m d hd hdiag
local notation "C" => fusionFoldedCartan m d

lemma fusionColorWord_action (j:V) (x:FiniteHomotopyClass Q (K:=K)) :
    positiveWordAction Q (fusionColorWord m j) x=T j x := by
  have h:=fusionExpandedWord_action m d hd hdiag [j] x
  simpa only [fusionExpandedWord,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.map_cons,List.map_nil,fusionWordPacketPerm,fusionSignedPacketPerm,ite_true, if_true,
    fusionColorWord,_root_.mul_one] using h

theorem fusionPacket_pure_two_layer (j:V) (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hl:ClassLowerBound Q q x) (hh:ClassUpperBound Q q x) :
    classTotalVector Q (classLayer Q q (T j x))-
      classTotalVector Q (classLayer Q (q+1) (T j x))=
      rowReflectWord (unfoldedCartan Q) (fusionColorWord m j) (classTotalVector Q x) := by
  have h:=classSignedVector_positiveWord Q (fusionColorWord m j) x
  rw [fusionColorWord_action m d hd hdiag j x] at h
  rw [classSignedVector_two_levels Q (T j x) q
    (classPacketPerm_lower_bound Q hn _ (fusionColor_orthogonal m d hd hdiag j) x hl)
    (classPacketPerm_upper_add_one Q hn _ (fusionColor_orthogonal m d hd hdiag j) x hh),
    classSignedVector_pure Q x q hl hh,rowReflectWord_smul] at h
  have h':=congrArg (fun z:FusionVertex (V:=V) m→ℝ=>cochainSign (K:=ℝ) q • z) h
  simpa only [smul_smul,cochainSign_mul_self,one_smul] using h'

include hm in
lemma fusionPacket_weighted_two_layer (j:V)
    (x:FusionLabel m→FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hl:∀ L,ClassLowerBound Q q (x L)) (hh:∀ L,ClassUpperBound Q q (x L))
    (a:V→ℝ) (ha:(∑ L,fusionWeight m L • classTotalVector Q (x L))=fusionFold m a) :
    (∑ L,fusionWeight m L • classTotalVector Q (classLayer Q q (T j (x L))))-
      (∑ L,fusionWeight m L • classTotalVector Q (classLayer Q (q+1) (T j (x L))))=
      fusionFold m (rowReflect C j a) := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← smul_sub,fusionPacket_pure_two_layer m d hd hdiag j _ q (hl _) (hh _),
    ← rowReflectWord_smul]
  rw [← rowReflectWord_sum,ha,fusionQuiver_cartan]
  exact fusion_reflection_intertwining m hm d hdiag j a

include hdiag in

omit [Fintype E] [DecidableEq E] in
lemma color_counts_eq_of_rows (j:V) (a b:V→ℝ)
    (hext:∀ v,v≠j→a v=b v) (ha:(C *ᵥ a) j=0) (hb:(C *ᵥ b) j=0) : a=b := by
  have hdif:(C *ᵥ (a-b)) j=0 := by rw [Matrix.mulVec_sub,Pi.sub_apply,ha,hb,sub_self]
  have hsum:(C *ᵥ (a-b)) j=2*(a j-b j) := by
    change (∑ v,C j v*(a v-b v))=_
    rw [Finset.sum_eq_single j]
    · simp [fusionFoldedCartan,hdiag,FusionEdge.dimension]
    · intro v hv hvj
      rw [hext v hvj,sub_self,MulZeroClass.mul_zero]
    · simp
  funext v
  by_cases hv:v=j
  · subst v
    rw [hsum] at hdif
    linarith
  · exact hext v hv

include hm in

theorem fusionPacket_cap_of_bottom_counts (j:V)
    (x:FusionLabel m→FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hl:∀ L,ClassLowerBound Q q (x L)) (hh:∀ L,ClassUpperBound Q q (x L))
    (a:V→ℝ) (ha:(∑ L,fusionWeight m L • classTotalVector Q (x L))=fusionFold m a)
    (hb:(∑ L,fusionWeight m L • classTotalVector Q (classLayer Q q (T j (x L))))=fusionFold m a)
    (hr:(C *ᵥ a) j=0) : ∀ L,ClassUpperBound Q q (T j (x L)) := by
  have he:=fusionPacket_weighted_two_layer m d hd hdiag hm j x q hl hh a ha
  have hr':rowReflect C j a=a := by simp only [rowReflect,hr,zero_smul,sub_zero]
  rw [hr',hb] at he
  have hz:(∑ L,fusionWeight m L • classTotalVector Q (classLayer Q (q+1) (T j (x L))))=0 := by
    exact sub_eq_self.mp he
  intro L
  apply classUpperBound_of_upper_layer_zero Q _ q
    (classPacketPerm_upper_add_one Q hn _ (fusionColor_orthogonal m d hd hdiag j) _ (hh L))
  funext α
  have hs:=congrFun hz α
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hs ⊢
  have hnz:∀ H∈(Finset.univ:Finset (FusionLabel m)),0≤fusionWeight m H*
      classTotalVector Q (classLayer Q (q+1) (T j (x H))) α :=
    fun H _=>mul_nonneg (fusionWeight_pos m hm H).le (classTotalVector_layer_nonneg Q _ _ _)
  have hlz: fusionWeight m L*classTotalVector Q (classLayer Q (q+1) (T j (x L))) α=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnz).mp hs L (Finset.mem_univ _)
  exact (mul_eq_zero.mp hlz).resolve_left (ne_of_gt (fusionWeight_pos m hm L))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionPacketOrbit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V : Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd

variable (e:E)
local notation "mr" => (fun f:FusionRest e => m f)
local notation "dr" => (fun s t=>FusionEdge.removeFactor e (d s t))
local notation "Qr" => fusionQuiver mr dr (restFusion_symmetric d hd e)
local notation "hnr" => fusionQuiver_no_loops mr dr (restFusion_symmetric d hd e) (restFusion_diagonal d hdiag e)
local notation "step" => fusionFactorStep m e d
local notation "hstep" => fusionFactorStep_reverse m e d hd
local notation "N" => stringAdjacent (m e)
local notation "hN" => stringAdjacent_symm (m e)
local notation "U" => ReversibleQuiver.stringQuiver Qr step hstep N hN
local notation "W" => StringFunctor.wordPacketPerm Qr step hstep N hN (K:=ℂ) hnr
local notation "O" => fusionPacketOrbit m d hd hdiag

variable (hm:∀ e,2 ≤ m e)

include hm in
lemma fusionOrbit_top_slice (w:List (V × Bool)) (s v:V) (q b:ℤ)
    (r t:FusionLabel mr) : ∃ c:ℝ, ∀ j,
    (∑ i,stringWeight (m e) i *
      (classLayerTopDimension Q q (v,(labelSplit m e).symm (r,j)) b
        (O w s ((labelSplit m e).symm (t,i))):ℝ)) = c*stringWeight (m e) j := by
  obtain ⟨z,hz⟩ := fusionOrbit_split m d hd hdiag e w
  obtain ⟨c,hc,h⟩ := StringFunctor.string_wordOrbit_top_proportional Qr step hstep hnr (m e) (hm e)
    z (s,t) (v,r) q b
  refine ⟨c,fun j=>?_⟩
  calc
    _ = ∑ i,stringWeight (m e) i * (classLayerTopDimension U q ((v,r),j) b
        (W z (initialClass U ((s,t),i))):ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← (fusionQuiverSplit m e d hd).classMap_topDimension,hz]
      simp only [fusionQuiverSplit,fusionVertexSplit,Equiv.coe_fn_mk,
        labelSplit_symm_at,labelSplit_symm_rest]
    _ = _ := h j

include hm

theorem fusionPacketOrbit_top_proportional (w:List (V × Bool)) (s v:V) (q b:ℤ) :
    ∃ c:ℝ,0 ≤ c ∧ ∀ L,
      (∑ H,fusionWeight m H*(classLayerTopDimension Q q (v,L) b (O w s H):ℝ)) =
        c*fusionWeight m L :=
  fusion_weighted_matrix_proportional m hm _
    (fun e=>fusionOrbit_top_slice m d hd hdiag e hm w s v q b)

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

lemma fusionOrbitModel_negative_homDimension (w:List (V × Bool)) (s t:V)
    (L H:FusionLabel m) (n v:ℤ) (h:n+v<0) :
    homDimension Q (fusionOrbitModel m d hd hdiag w s L).complex
      (fusionOrbitModel m d hd hdiag w t H).complex n v=0 := by
  obtain ⟨x,hx⟩:=fusionOrbit_in_action m d hd hdiag w
  let f (a b:FiniteHomotopyClass Q (K:=ℂ)) :=
    homDimension Q (minimalClassModel Q a).complex (minimalClassModel Q b).complex n v
  change f (O w s L) (O w t H)=0
  rw [hx,hx]
  exact
    frameModel_negative_pair_homDimension Q hn C (fusionOrdinaryPresentation m d hd)
      (K:=ℂ) x (s,L) (t,H) n v h

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
local notation "O" => fusionOrbitModel m d hd hdiag

theorem fusionOrbit_summand_secondary_bound (w:List (V × Bool)) (s:V)
    (L H:FusionLabel m) {T:Type*} [Fintype T] (M:BasedComplex Q (K:=ℂ) T)
    (U:Set (FusionVertex (V:=V) m)) (q k:ℤ)
    (hM:∀ i,(M.placement i).level=q) (hU:∀ i,(M.placement i).color∈U)
    (ι:Map Q M (Y w s L q)) (π:Map Q (Y w s L q) M)
    (hret:ι.matrix*π.matrix=projectiveIdentity Q M.placement)
    (hcap:(O w s L).complex.CappedOn Q U q) (hk:k<q) :
    totalHomDimension Q M (Y w s H k) (k-q) ≤
      totalHomDimension Q (Y w s H (k-1)) M (q-k+1) := by
  exact cappedSummand_total_bound Q (O w s L).complex (O w s H).complex
    (fusionOrbitModel_minimal m d hd hdiag w s L)
    (fusionOrbitModel_minimal m d hd hdiag w s H) M U q k hM hU ι π hret hcap
    (fun n v h=>fusionOrbitModel_negative_homDimension m d hd hdiag w s s L H n v (by omega))

lemma fusionWeightedHom_nonneg (hm:∀ e,2 ≤ m e) {T R:FusionLabel m → Type*}
    [∀ L,Fintype (T L)] [∀ H,Fintype (R H)]
    (P:∀ L,BasedComplex Q (K:=ℂ) (T L)) (F:∀ H,BasedComplex Q (K:=ℂ) (R H)) (t:ℤ) :
    0≤fusionWeightedHom m d hd P F t := by
  apply Finset.sum_nonneg
  intro L _
  apply Finset.sum_nonneg
  intro H _
  exact mul_nonneg (mul_pos (fusionWeight_pos m hm L) (fusionWeight_pos m hm H)).le (Nat.cast_nonneg _)

theorem fusionOrbit_weighted_secondary_bound (hm:∀ e,2 ≤ m e)
    (w:List (V × Bool)) (s:V) {T:FusionLabel m → Type*} [∀ L,Fintype (T L)]
    (M:∀ L,BasedComplex Q (K:=ℂ) (T L)) (U:Set (FusionVertex (V:=V) m)) (q k:ℤ)
    (hM:∀ L i,((M L).placement i).level=q) (hU:∀ L i,((M L).placement i).color∈U)
    (ι:∀ L,Map Q (M L) (Y w s L q)) (π:∀ L,Map Q (Y w s L q) (M L))
    (hret:∀ L,(ι L).matrix*(π L).matrix=projectiveIdentity Q (M L).placement)
    (hcap:∀ L,(O w s L).complex.CappedOn Q U q) (hk:k<q) :
    fusionWeightedHom m d hd M (fun H=>Y w s H k) (k-q) ≤
      fusionWeightedHom m d hd (fun H=>Y w s H (k-1)) M (q-k+1) := by
  unfold fusionWeightedHom
  rw [Finset.sum_comm (f:=fun H L=>fusionWeight m H*fusionWeight m L*
    (totalHomDimension Q (Y w s H (k-1)) (M L) (q-k+1):ℝ))]
  apply Finset.sum_le_sum
  intro L _
  apply Finset.sum_le_sum
  intro H _
  rw [mul_comm (fusionWeight m H) (fusionWeight m L)]
  apply mul_le_mul_of_nonneg_left _ (mul_pos (fusionWeight_pos m hm L) (fusionWeight_pos m hm H)).le
  exact_mod_cast fusionOrbit_summand_secondary_bound m d hd hdiag w s L H (M L) U q k
    (hM L) (hU L) (ι L) (π L) (hret L) (hcap L) hk

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionOrbitColorSecondary
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
include hm
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "O" => fusionPacketOrbit m d hd hdiag

theorem fusionOrbitColor_secondary_bound (w:List (V×Bool)) (s:V) (q k:ℤ) (U:Set V)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U))
    (hcap:∀ L,ClassCapOn Q (O w s L) (fusionColorRegion m U) q) (hk:k<q) :
    fusionWeightedHom m d hd
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L) (fun H=>Y w s H k) (k-q) ≤
    fusionWeightedHom m d hd (fun H=>Y w s H (k-1))
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L) (q-k+1) := by
  let T:=fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L
  let incl L:=blockInclusionMap Q (Y w s L q) _
    (pure_color_block Q _ _ (fun i=>i.property) (hb L))
  let proj L:=blockProjectionMap Q (Y w s L q) _
    (pure_color_block Q _ _ (fun i=>i.property) (hb L))
  have hret:∀ L,(incl L).matrix*(proj L).matrix=projectiveIdentity Q (T L).placement := by
    intro L
    convert block_inclusion_projection Q (Y w s L q)
      {i | ((Y w s L q).placement i).color∈fusionColorRegion m U} using 1
    · rfl
    · apply Matrix.ext
      intro i j
      simp only [projectiveIdentity,Matrix.diagonal_apply]
      by_cases h:i=j <;> simp only [h,ite_true, if_true,ite_false, if_false]
      rfl
  exact fusionOrbit_weighted_secondary_bound m d hd hdiag hm w s T (fusionColorRegion m U)
    q k (fun L i=>i.val.property) (fun L i=>i.property) incl proj
    (fun L=>by
      convert hret L using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1)
      exact Subsingleton.elim _ _) hcap hk

lemma fusionOrbitColor_Hom_zero_of_previous (w:List (V×Bool)) (s:V) (q k:ℤ) (U:Set V)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U))
    (hcap:∀ L,ClassCapOn Q (O w s L) (fusionColorRegion m U) q) (hk:k<q)
    (hz:fusionWeightedHom m d hd (fun H=>Y w s H (k-1))
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L) (q-k+1)=0) :
    fusionWeightedHom m d hd
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L) (fun H=>Y w s H k) (k-q)=0 := by
  apply le_antisymm
  · exact (fusionOrbitColor_secondary_bound m d hd hdiag hm w s q k U hb hcap hk).trans_eq hz
  · exact fusionWeightedHom_nonneg m d hd hm _ _ _

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionProfilePositiveEvery
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
  (m:E → ℕ) (hm:∀ e,2 ≤ m e)
include hm

lemma fusion_profile_positive_every_label (a:FusionLabel m → FusionLabel m → ℕ)
    (ha:∃ c:ℝ,0 ≤ c ∧ ∀ L,(∑ H,fusionWeight m H*(a H L:ℝ))=c*fusionWeight m L)
    {H₀ L₀:FusionLabel m} (h₀:0<a H₀ L₀) (L:FusionLabel m) : ∃ H,0<a H L := by
  obtain ⟨c,_,h⟩:=ha
  have hsum:0 < ∑ H,fusionWeight m H*(a H L₀:ℝ) := by
    apply lt_of_lt_of_le (mul_pos (fusionWeight_pos m hm H₀) (show (0:ℝ)<(a H₀ L₀:ℝ) by exact_mod_cast h₀))
    exact Finset.single_le_sum (fun H _=>mul_nonneg (fusionWeight_pos m hm H).le (Nat.cast_nonneg (a H L₀)))
      (Finset.mem_univ H₀)
  rw [h] at hsum
  have hcpos:0 < c := (mul_pos_iff_of_pos_right (fusionWeight_pos m hm L₀)).mp hsum
  have htarget:0 < ∑ H,fusionWeight m H*(a H L:ℝ) := by
    rw [h]
    exact mul_pos hcpos (fusionWeight_pos m hm L)
  by_contra hn
  push Not at hn
  have hz:∀ H,a H L=0:=fun H=>Nat.eq_zero_of_le_zero (hn H)
  simp only [hz,Nat.cast_zero,MulZeroClass.mul_zero,Finset.sum_const_zero,lt_self_iff_false] at htarget

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionOrbitColorTop
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
include hm
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "O" => fusionPacketOrbit m d hd hdiag

theorem fusionOrbitColor_top_socle_Hom_pos (w:List (V×Bool)) (s v:V) (q k b c:ℤ)
    (U:Set V) (hv:v∈U)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U))
    {L₀ H₀ L₁ H₁:FusionLabel m}
    (ht:0 < classLayerTopDimension Q q (v,L₀) b (O w s H₀))
    (hs:0 < classLayerSocleDimension Q k (v,L₁) c (O w s H₁)) :
    0<fusionWeightedHom m d hd
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L)
      (fun H=>Y w s H k) (k-q) := by
  obtain ⟨H,htH⟩:=fusion_profile_positive_every_label m hm
    (fun H L=>classLayerTopDimension Q q (v,L) b (O w s H))
    (fusionPacketOrbit_top_proportional m d hd hdiag hm w s v q b) ht L₁
  have hn {I:Type} [Fintype I] (P:Submodule ℂ (I→ℂ))
      (hp:0<Module.finrank ℂ P):P≠⊥ := by
    intro hz
    rw [hz,finrank_bot] at hp
    exact (lt_irrefl 0 hp)
  have htne:coefficientTopDual Q
      (fusionOrbitColorLayer m d hd hdiag w s q U hb H) (v,L₁) b≠⊥ := by
    intro hz
    have hfull:=colorRestriction_top_zero Q (Y w s H q) q (fusionColorRegion m U)
      (fun i=>i.property) (hb H) (v,L₁) hv b hz
    exact hn _ htH hfull
  have hsne:coefficientSocle Q (Y w s H₁ k) (v,L₁) c≠⊥:=hn _ hs
  have hh:=pure_top_socle_totalHomDimension_pos Q
    (fusionOrbitColorLayer m d hd hdiag w s q U hb H) (Y w s H₁ k)
    (fun i=>i.val.property) (fun i=>i.property) (v,L₁) b c htne hsne
  have hnon (L T:FusionLabel m):0≤fusionWeight m L*fusionWeight m T*
      (totalHomDimension Q (fusionOrbitColorLayer m d hd hdiag w s q U hb L)
        (Y w s T k) (k-q):ℝ):=
    mul_nonneg (mul_pos (fusionWeight_pos m hm L) (fusionWeight_pos m hm T)).le (Nat.cast_nonneg _)
  apply Finset.sum_pos'
  · intro L _
    exact Finset.sum_nonneg (fun T _=>hnon L T)
  · refine ⟨H,Finset.mem_univ H,Finset.sum_pos' (fun T _=>hnon H T) ?_⟩
    refine ⟨H₁,Finset.mem_univ H₁,?_⟩
    exact mul_pos (mul_pos (fusionWeight_pos m hm H) (fusionWeight_pos m hm H₁)) (by exact_mod_cast hh)

theorem fusionOrbitColor_top_zero_of_Hom_zero (w:List (V×Bool)) (s v:V) (q k c:ℤ)
    (U:Set V) (hv:v∈U)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U))
    {L H:FusionLabel m} (hs:0 < classLayerSocleDimension Q k (v,L) c (O w s H))
    (hh:fusionWeightedHom m d hd
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L)
      (fun H=>Y w s H k) (k-q)=0) :
    ∀ L' H' b,classLayerTopDimension Q q (v,L') b (O w s H')=0 := by
  intro L' H' b
  by_contra ht
  have hp:=fusionOrbitColor_top_socle_Hom_pos m d hd hdiag hm w s v q k b c U hv hb
    (Nat.pos_of_ne_zero ht) hs
  rw [hh] at hp
  exact lt_irrefl 0 hp

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionPacketLayerExterior
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
local notation "T" => fusionPacketPerm m d hd hdiag (K:=ℂ)
local notation "hn" => fusionQuiver_no_loops m d hd hdiag
local notation "C" => fusionFoldedCartan m d

lemma fusionPacket_layer_exterior (j v:V) (hv:v≠j)
    (x:FiniteHomotopyClass Q (K:=ℂ)) (L:FusionLabel m) (q:ℤ) :
    classTotalVector Q (classLayer Q q (T j x)) (v,L)=
      classTotalVector Q (classLayer Q q x) (v,L) := by
  simp only [classTotalVector_layer_apply]
  congr 1
  have h:=fusionWord_level_exterior m d hd hdiag [(j,true)] x v L q
    (by simpa only [List.mem_singleton,forall_eq,ne_eq] using hv.symm)
  simpa only [fusionWordPacketPerm,fusionSignedPacketPerm,ite_true, if_true,_root_.mul_one] using h

include hm in

theorem fusionPacket_zero_rows_force_top (j:V) (q:ℤ)
    (x:FusionLabel m→FiniteHomotopyClass Q (K:=ℂ))
    (ht:∀ H L c,classLayerTopDimension Q (q-1) (j,L) c (x H)=0)
    (a b:V→ℝ)
    (ha:(∑ H,fusionWeight m H • classTotalVector Q (classLayer Q q (x H)))=fusionFold m a)
    (hb:(∑ H,fusionWeight m H • classTotalVector Q (classLayer Q q (T j (x H))))=fusionFold m b)
    (hra:(C *ᵥ a) j=0) (hrb:(C *ᵥ b) j=0) :
    a=b ∧ ∀ H L c,classLayerTopDimension Q q (j,L) c (x H)=0 := by
  have hext:∀ v,v≠j→a v=b v := by
    intro v hv
    let L:FusionLabel m:=fun e=>⟨0,by have :=hm e; omega⟩
    have he:(fusionFold m a) (v,L)=(fusionFold m b) (v,L) := by
      rw [← ha,← hb]
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
        fusionPacket_layer_exterior m d hd hdiag j v hv]
    exact mul_left_cancel₀ (ne_of_gt (fusionWeight_pos m hm L)) he
  have hab:a=b:=color_counts_eq_of_rows m d hdiag j a b hext hra hrb
  have hu (H:FusionLabel m):classLayer Q q (T j (x H))=
      classLayer Q q (T j (classLayer Q q (x H))) :=
    classPacketPerm_unshifted_layer Q hn (fun L=>(j,L))
      (fusionColor_orthogonal m d hd hdiag j) (x H) q (ht H)
  have hc:∀ H,ClassUpperBound Q q (T j (classLayer Q q (x H))) := by
    apply fusionPacket_cap_of_bottom_counts m d hd hdiag hm j
      (fun H=>classLayer Q q (x H)) q
      (fun H=>classLayer_lowerBound Q (x H) q)
      (fun H=>classLayer_upperBound Q (x H) q) a ha
    · simp only [← hu]
      exact hb.trans (congrArg (fusionFold m) hab.symm)
    · exact hra
  refine ⟨hab,fun H=>?_⟩
  exact classPacketPerm_top_zero_of_layer_cap Q hn (fun L=>(j,L))
    (fusionColor_orthogonal m d hd hdiag j) (x H) q (hc H)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_IntegerUpward
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

lemma integer_upward {P:ℤ→Prop} (b d:ℤ)
    (low:∀ k,k<b→P k)
    (step:∀ k,b≤k→k<d→P (k-1)→P k) : ∀ k,k<d→P k := by
  intro k hk
  by_cases hb:k<b
  · exact low k hb
  · have go:∀ n,b-1≤n→ n<d→P n := by
      intro n hn
      refine Int.leInduction (m:=b-1) (motive:=fun n _=>n<d→P n) ?_ ?_ n hn
      · intro hn
        exact low (b-1) (by omega)
      · intro n hn ih hnd
        apply step (n+1) (by omega) hnd
        have h:=ih (by omega)
        simpa only [add_sub_cancel_right] using h
    exact go k (by omega) hk
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
local notation "hn" => fusionQuiver_no_loops m d hd hdiag

namespace IsolatedIterationData
variable {M} (D:IsolatedIterationData M)

lemma lower_bound_move (z:List ((S⊕Unit)×Bool)) (j:D.J) (b:ℤ)
    (hb:∀ L,ClassLowerBound Q b (O z D.s L)) :
    ∀ L,ClassLowerBound Q b (O ((.inl j,true)::z) D.s L) := by
  intro L
  exact classPacketPerm_lower_bound Q hn (fun H=>(Sum.inl (j:S),H))
    (fusionColor_orthogonal m d hd hdiag (.inl j)) (O z D.s L) (hb L)

lemma socle_below (z:List ((S⊕Unit)×Bool)) (b k:ℤ)
    (hb:∀ L,ClassLowerBound Q b (O z D.s L)) (hk:k<b) : D.openSocle z k := by
  intro H α hα c
  exact classLayerSocleDimension_below Q (O z D.s H) b k (hb H) hk α c

lemma cap_move (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
    (k:ℤ) (hk:k<D.q) (hp:D.openSocle z (k-1)) (j:D.J)
    (hs:∃ H L c,0 < classLayerSocleDimension Q k (.inl j,L) c (O z D.s H)) :
    D.capped ((.inl j,true)::z) := by
  have hrev: fusionWeightedHom m d hd (fun H=>Y z D.s H (k-1))
      (D.fullRegion z hz) (D.q-k+1)=0 := by
    convert (D.separation z hz hc (k-1) hp).2.2.2 using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    omega
  have hf:=fusionOrbitColor_Hom_zero_of_previous m d hd hdiag hm z D.s D.q k
    (Sum.inl '' D.I) (D.boundary z hz)
    (fun L=>ClassCapOn.mono Q (hc L) (fun α hα=>Or.inl hα)) hk hrev
  obtain ⟨H,L,c,hs⟩:=hs
  have ht:=fusionOrbitColor_top_zero_of_Hom_zero m d hd hdiag hm z D.s (.inl j) D.q k c
    (Sum.inl '' D.I) ⟨j,D.hJI j.property,rfl⟩ (D.boundary z hz) hs hf
  intro Hout
  exact classPacketPerm_local_cap_of_top_zero Q hn (fun L=>(Sum.inl (j:S),L))
    (fusionColor_orthogonal m d hd hdiag (.inl j)) (O z D.s Hout) D.region (hc Hout)
    (fun L=>⟨j,D.hJI j.property,rfl⟩) (fun L c=>ht L Hout c)

end IsolatedIterationData
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightedCounts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {M:CoxeterMatrix S}
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "T" => fusionPacketPerm m d hd hdiag (K:=ℂ)
local notation "hn" => fusionQuiver_no_loops m d hd hdiag

namespace IsolatedIterationData
variable (D:IsolatedIterationData M)

lemma weighted_counts (z:List ((S⊕Unit)×Bool)) (k:ℤ) :
    (∑ H,fusionWeight m H • classTotalVector Q (classLayer Q k (O z D.s H)))=
      fusionFold m (μ z D.s k) := by
  rw [← fusionOrbitWeightedVector_class]
  exact fusionOrbitWeightedVector_eq m d hd hdiag hm z D.s k

lemma unshifted (z:List ((S⊕Unit)×Bool)) (j:D.J) (k:ℤ)
    (ht:∀ H L c,classLayerTopDimension Q (k-1) (.inl j,L) c (O z D.s H)=0) :
    ∀ H,classLayer Q k (O ((.inl j,true)::z) D.s H)=
      classLayer Q k (T (.inl j) (classLayer Q k (O z D.s H))) := by
  intro H
  exact classPacketPerm_unshifted_layer Q hn (fun L=>(Sum.inl (j:S),L))
    (fusionColor_orthogonal m d hd hdiag (.inl j)) (O z D.s H) k (ht H)

lemma openSocle_unshifted (z:List ((S⊕Unit)×Bool)) (j:D.J) (k:ℤ)
    (ht:∀ H L c,classLayerTopDimension Q (k-1) (.inl j,L) c (O z D.s H)=0)
    (hs:D.openSocle z k) : D.openSocle ((.inl j,true)::z) k := by
  intro H α hα c
  rw [classLayerSocleDimension_congr_layer Q k (D.unshifted z j k ht H) α c]
  apply classPacketPerm_preserves_open_socle Q hn (fun L=>(Sum.inl (j:S),L))
    (fusionColor_orthogonal m d hd hdiag (.inl j)) D.operated
    (fun L=>⟨j,j.property,rfl⟩) (classLayer Q k (O z D.s H))
    (classLayer_lowerBound Q (O z D.s H) k) _ α hα c
  intro β hβ r
  rw [classLayerSocleDimension_layer]
  exact hs H β hβ r

theorem upward (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
    (j:D.J) (b t:ℤ) (hb:∀ H,ClassLowerBound Q b (O z D.s H))
    (hp:∀ k,k<t→D.openSocle z k) (hc':D.capped ((.inl j,true)::z)) :
    (∀ k,k<t→D.openSocle ((.inl j,true)::z) k) ∧
    (∀ k,k<t→∀ H L c,classLayerTopDimension Q k (.inl j,L) c (O z D.s H)=0) ∧
    (∀ H,classLayer Q t (O ((.inl j,true)::z) D.s H)=
      classLayer Q t (T (.inl j) (classLayer Q t (O z D.s H)))) := by
  let z':=((Sum.inl (j:S),true)::z)
  have hz':D.valid z':=D.move z hz j
  have hb':∀ H,ClassLowerBound Q b (O z' D.s H):=D.lower_bound_move z j b hb
  let P:ℤ→Prop:=fun k=>
    (∀ H L c,classLayerTopDimension Q k (.inl j,L) c (O z D.s H)=0) ∧ D.openSocle z' k
  have hP:∀ k,k<t→P k := by
    refine integer_upward (P:=P) b t ?_ ?_
    · intro k hk
      exact ⟨fun H L c=>classLayerTopDimension_below Q (O z D.s H) b k (hb H) hk _ c,
        D.socle_below z' b k hb' hk⟩
    · intro k _ hkt hprev
      have hs':D.openSocle z' k:=D.openSocle_unshifted z j k hprev.1 (hp k hkt)
      have hr:=(D.separation z hz hc k (hp k hkt)).2.1
      have hr':=(D.separation z' hz' hc' k hs').2.1
      have htop:=fusionPacket_zero_rows_force_top m d hd hdiag hm (.inl j) k
        (O z D.s) hprev.1 (μ z D.s k) (μ z' D.s k)
        (D.weighted_counts z k) (D.weighted_counts z' k)
        (hr (.inl j) ⟨j,j.property,rfl⟩) (hr' (.inl j) ⟨j,j.property,rfl⟩)
      exact ⟨htop.2,hs'⟩
  exact ⟨fun k hk=>(hP k hk).2,fun k hk=>(hP k hk).1,
    D.unshifted z j t (hP (t-1) (by omega)).1⟩

theorem stage_move_oai (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
    (j:D.J) (b t:ℤ) (ht:t<D.q) (hb:∀ H,ClassLowerBound Q b (O z D.s H))
    (hp:∀ k,k<t→D.openSocle z k)
    (hs:∃ H L c,0 < classLayerSocleDimension Q t (.inl j,L) c (O z D.s H)) :
    D.capped ((.inl j,true)::z) ∧
    (∀ H,ClassLowerBound Q b (O ((.inl j,true)::z) D.s H)) ∧
    (∀ k,k<t→D.openSocle ((.inl j,true)::z) k) ∧
    (∀ H,classLayer Q t (O ((.inl j,true)::z) D.s H)=
      classLayer Q t (T (.inl j) (classLayer Q t (O z D.s H)))) := by
  have hc':=D.cap_move z hz hc t ht (hp (t-1) (by omega)) j hs
  have hup:=D.upward z hz hc j b t hb hp hc'
  exact ⟨hc',D.lower_bound_move z j b hb,hup.1,hup.2.2⟩

end IsolatedIterationData
end HarmonicArtin

end OAI
end

theorem solution : type_of% @OAI.HarmonicArtin.IsolatedIterationData.stage_move_oai := @OAI.HarmonicArtin.IsolatedIterationData.stage_move_oai
