-- Prove2me | solution 1 for OAI.HarmonicArtin.sourceClosedResidue_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:46:51.878202+00:00
-- url     : https://prove2.me/submissions/c8980101-e40a-4fdb-bf5c-85b966d3546b

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag013
import Theorems.Thm_OAI_HarmonicArtin_IsolatedIterationData_separation
import Theorems.Thm_OAI_HarmonicArtin_IsolatedIterationData_stage_move

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

theorem classPacketPerm_bottom_socle_zero
    (hn:∀ a,Q.source a≠Q.target a) (v:J→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K:=K)) {d:ℤ} (hx:ClassLowerBound Q d x) (a:J) (c:ℤ) :
    classLayerSocleDimension Q d (v a) c (classPacketPerm Q hn v hv x)=0 := by
  let : DecidableEq {b:J // b≠a} := Classical.decEq _
  let E:=minimalClassModel Q x
  let vr:{b:J // b≠a}→V:=fun b=>v b.val
  have hvr:Pairwise fun b b'=>OrthogonalVertices Q (vr b) (vr b') := by
    intro b b' h
    apply hv
    intro he
    exact h (Subtype.ext he)
  have he:classPacketPerm Q hn v hv x=
      classPositiveTwist Q (v a) (classOfComplex Q (E.complex.packetTwist Q vr)) := by
    rw [← minimalClassModel_class Q x,classPacketPerm_apply,
      classOfComplex_packet_reindex Q E.complex v (Equiv.optionSubtypeNe a)]
    have hf:v ∘ Equiv.optionSubtypeNe a=fun z:Option {b:J // b≠a}=>z.elim (v a) vr := by
      funext z; cases z <;> rfl
    rw [hf,classOfComplex_packet_cons Q E.complex (v a) vr (fun b=>hv (Ne.symm b.property))]
  rw [he]
  exact classPositiveTwist_bottom_socle_zero Q hn (v a) _
    (classOfComplex_packet_lower_bound Q E.complex hx vr hvr) c

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TestExact
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma classTestUpper_model (E:FiniteModel Q (K:=K)) (U:Set V) (t:ℤ) :
    ClassTestUpper Q ⟦E⟧ U t ↔ TestUpperBound Q E.complex U t := Iff.rfl

lemma classTestExact_positive_self (hn:∀ a,Q.source a≠Q.target a)
    (x:FiniteHomotopyClass Q (K:=K)) (α:V) (l c:ℤ) :
    ClassTestExact Q α l c (classPositiveTwist Q α x) ↔
      ClassTestExact Q α (l-1) (c+1) x := by
  induction x using Quotient.inductionOn with | _ E =>
    exact positiveTwist_test_exact_iff Q hn E.complex α l c

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

lemma mem_closedNeighborhood {U : Set V} {α : V} (hα : α∈U) :
    α∈Q.closedNeighborhood U := Or.inl hα

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HighestLocalGeneratorTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type u} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem highest_local_generator_test_not_exact
    (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (U:Set V) (i:I)
    (hiU:(E.placement i).color∈U)
    (hcap:∀ j,(E.placement j).color∈Q.closedNeighborhood U → (E.placement j).level≤(E.placement i).level)
    (hfirst:∀ j,(E.placement j).color∈Q.closedNeighborhood U → (E.placement j).level=(E.placement i).level→
      (E.placement i).cochain≤(E.placement j).cochain) :
    ¬ ScalarExactAt Q (E.testComplex Q (E.placement i).color) (E.placement i).color
      ((E.placement i).level+2) (E.placement i).cochain := by
  classical
  let α:=(E.placement i).color
  let T:=E.testComplex Q α
  let t:TestIndex Q E.placement α:=generatorTokenTest Q E i
  let D:=testMatrix Q E.placement E.placement α E.differential
  have ht:Path.length t.2.val=2:=rfl
  have hcol:∀ u,D u t=0 := by
    intro u
    by_contra hm
    have hm':(T.differential u t).vertex α≠0 := by
      change ((D u t) • vertexId Q (K:=K) α).vertex α≠0
      simpa [vertexId_eval] using hm
    obtain ⟨_,_,hc,hu⟩:=degree_vertex_support Q T.entries T.degree u t α hm'
    change (E.placement i).cochain=(E.placement u.1).cochain+1 at hc
    change (E.placement i).internal+2=
      (E.placement u.1).internal+Path.length u.2.val+0 at hu
    have hmem := Q.corner_target_mem_neighborhood hiU u.2
    have hh:=hcap u.1 hmem
    rcases hp:u.2.val with v|a|v
    · have hl:Path.length u.2.val=0:=by rw [hp]; rfl
      dsimp only [GeneratorPlacement.level] at hh
      omega
    · have hl:Path.length u.2.val=1:=by rw [hp]; rfl
      have he:(E.placement u.1).level=(E.placement i).level := by
        dsimp only [GeneratorPlacement.level]; omega
      have hm:=hfirst u.1 hmem he
      omega
    · exact hm (test_token_row_zero Q E hE α u t (by rw [hp]; rfl))
  intro he
  change ScalarExactAt Q T α ((E.placement i).level+2) (E.placement i).cochain at he
  let x:TestIndex Q E.placement α→K:=Pi.single t 1
  have hxs:ScalarSupported Q T ((E.placement i).level+2) (E.placement i).cochain x := by
    intro u hu
    have hut:u≠t := by
      intro hh
      subst u
      apply hu
      constructor
      · change (E.placement i).cochain+((E.placement i).internal+2)=
          (E.placement i).cochain+(E.placement i).internal+2
        omega
      · rfl
    exact Pi.single_eq_of_ne hut _
  have hxd:Matrix.vecMul x (T.differential.map (vertexHom Q α))=0 := by
    rw [testComplex_vertex_differential Q E α]
    funext u
    change (∑ v,x v * D v u)=0
    rw [Finset.sum_eq_single t]
    · exact mul_eq_zero.mpr (Or.inr (test_token_row_zero Q E hE α t u ht))
    · intro v hv hvt
      rw [show x v=0 from Pi.single_eq_of_ne hvt _,MulZeroClass.zero_mul]
    · simp
  obtain ⟨z,hzs,hzd⟩:=he x hxs hxd
  have hh:=congrFun hzd t
  rw [testComplex_vertex_differential Q E α] at hh
  have hz:Matrix.vecMul z D t=0 := by
    apply Finset.sum_eq_zero
    intro u hu
    exact mul_eq_zero.mpr (Or.inr (hcol u))
  change Matrix.vecMul z D t=x t at hh
  rw [hz] at hh
  have hx:x t=1:=Pi.single_eq_same _ _
  rw [hx] at hh
  exact zero_ne_one hh

omit [DecidableEq I] in
theorem local_generatorBound_of_test_and_boundary
    (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (U:Set V) (d:ℤ)
    (h:TestUpperBound Q E U (d+2))
    (hout:∀ i,(E.placement i).color∈Q.closedNeighborhood U →
      (E.placement i).color∉U → (E.placement i).level≤d) :
    ∀ i,(E.placement i).color∈U → (E.placement i).level≤d := by
  classical
  intro i hiU
  by_contra hi
  let G:Finset I:=Finset.univ.filter (fun k=>(E.placement k).color∈U)
  have hiG:i∈G := by simp [G,hiU]
  obtain ⟨j,hj,hmax⟩:=Finset.exists_max_image G
    (fun j:I=>(E.placement j).level) ⟨i,hiG⟩
  have hm:∀ k,(E.placement k).color∈U → (E.placement k).level≤(E.placement j).level:=
    fun k hk=>hmax k (by simp [G,hk])
  let F:=G.filter (fun k:I=>(E.placement k).level=(E.placement j).level)
  have hjF:j∈F:=by simp [F,hj]
  obtain ⟨k,hk,hmin⟩:=Finset.exists_min_image F (fun k:I=>(E.placement k).cochain) ⟨j,hjF⟩
  have hlev:(E.placement k).level=(E.placement j).level:= (Finset.mem_filter.mp hk).2
  have hkd:d<(E.placement k).level := by have hh:=hm i hiU; omega
  have hku:(E.placement k).color∈U :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
  apply highest_local_generator_test_not_exact Q E hE U k hku
  · intro z hz
    by_cases hzU:(E.placement z).color∈U
    · rw [hlev]; exact hm z hzU
    · have hh:=hout z hz hzU; omega
  · intro z hz hzlev
    have hzU:(E.placement z).color∈U := by
      by_contra hzU
      have hh:=hout z hz hzU
      omega
    exact hmin z (by simp [F,G,hzU,hzlev,hlev])
  · exact h (E.placement k).color hku ((E.placement k).level+2) (by omega)
      (E.placement k).cochain

lemma classCapOn_of_test_and_boundary (x : FiniteHomotopyClass Q (K:=K))
    (U:Set V) (d:ℤ) (h:ClassTestUpper Q x U (d+2))
    (hb:ClassCapOn Q x (Q.closedNeighborhood U \ U) d) : ClassCapOn Q x U d := by
  let E:=minimalClassModel Q x
  have hx : (⟦E⟧:FiniteHomotopyClass Q (K:=K))=x := minimalClassModel_class Q x
  have ht : TestUpperBound Q E.complex U (d+2) := by
    rw [← classTestUpper_model,hx]; exact h
  exact local_generatorBound_of_test_and_boundary Q E.complex
    (minimalClassModel_minimal Q x) U d ht (fun i hi hni=>hb i ⟨hi,hni⟩)

lemma classPositiveNegative_cancel (hn:∀ a,Q.source a≠Q.target a)
    (x:FiniteHomotopyClass Q (K:=K)) (α:V) :
    classPositiveTwist Q α (classNegativeTwist Q α x)=x :=
  (classTwistPerm Q hn α).apply_symm_apply x

lemma classTestExact_negative_self (hn:∀ a,Q.source a≠Q.target a)
    (x:FiniteHomotopyClass Q (K:=K)) (α:V) (l c:ℤ) :
    ClassTestExact Q α l c (classNegativeTwist Q α x) ↔
      ClassTestExact Q α (l+1) (c-1) x := by
  have h:=classTestExact_positive_self Q hn (classNegativeTwist Q α x) α (l+1) (c-1)
  rw [classPositiveNegative_cancel Q hn] at h
  simpa only [add_sub_cancel_right,sub_add_cancel] using h.symm

lemma classNegativeTwist_testUpper (hn:∀ a,Q.source a≠Q.target a)
    (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (α:V) (hα:α∈U) {t:ℤ}
    (h:ClassTestUpper Q x U t) : ClassTestUpper Q (classNegativeTwist Q α x) U t := by
  apply classPositiveTwist_testUpper_reflect Q hn _ U α hα
  simpa only [classPositiveNegative_cancel Q hn] using h

lemma inverseWord_testUpper (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) {t:ℤ}
    (h:ClassTestUpper Q x U t) (hw:∀ α∈w,α∈U) :
    ClassTestUpper Q (inverseWordAction Q w x) U t := by
  induction w generalizing x with
  | nil => exact h
  | cons α w ih =>
    exact ih _ (classNegativeTwist_testUpper Q hn x U α (hw α (by simp)) h)
      (fun β hβ=>hw β (by simp [hβ]))

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InverseWordActionAppend
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u v
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  (hn : ∀ a,Q.source a≠Q.target a)

lemma inverseWordAction_append (w v : List V) (x : FiniteHomotopyClass Q (K:=K)) :
    inverseWordAction Q (w++v) x=inverseWordAction Q v (inverseWordAction Q w x) := by
  induction w generalizing x with
  | nil => rfl
  | cons α w ih => exact ih (classNegativeTwist Q α x)

include hn in
lemma inverseWordAction_eq_of_positive (w v : List V)
    (h : ∀ x : FiniteHomotopyClass Q (K:=K),positiveWordAction Q w x=positiveWordAction Q v x)
    (x : FiniteHomotopyClass Q (K:=K)) :
    inverseWordAction Q w x=inverseWordAction Q v x := by
  calc
    inverseWordAction Q w x=
        inverseWordAction Q w (positiveWordAction Q v (inverseWordAction Q v x)) := by
      rw [positive_inverseWord Q hn]
    _=inverseWordAction Q w (positiveWordAction Q w (inverseWordAction Q v x)) := by rw [h]
    _=inverseWordAction Q v x := inverse_positiveWord Q hn w _

variable {T : Type v} [Fintype T] [DecidableEq T] (C : CoxeterMatrix T) (ι : T → V)
  (hmat : ∀ α β,ordinaryCoxeterMatrix Q (ι α) (ι β)=C α β)

include hn hmat

lemma mapped_inverseWord_property (w v : List T)
    (hw : C.toCoxeterSystem.IsReduced w) (hv : C.toCoxeterSystem.IsReduced v)
    (he : C.toCoxeterSystem.wordProd w=C.toCoxeterSystem.wordProd v)
    (x : FiniteHomotopyClass Q (K:=K)) :
    inverseWordAction Q (w.map ι) x=inverseWordAction Q (v.map ι) x := by
  apply inverseWordAction_eq_of_positive Q hn
  intro y
  have hb : ∀ α β,((altList α β (C α β)).map (fun α=>classTwistPerm Q (K:=K) hn (ι α))).prod=
      ((altList β α (C α β)).map (fun α=>classTwistPerm Q (K:=K) hn (ι α))).prod := by
    intro α β
    have hh:=ordinaryTwist_braid Q (K:=K) hn (ι α) (ι β)
    rw [hmat] at hh
    simpa only [← altList_map,List.map_map,Function.comp_def] using hh
  have hh:=reduced_word_property C.toCoxeterSystem (fun α=>classTwistPerm Q (K:=K) hn (ι α))
    hb w v hw hv he
  rw [positiveWordAction_eq_prod Q hn,positiveWordAction_eq_prod Q hn]
  simpa only [List.map_map,Function.comp_def] using
    congrArg (fun f : Equiv.Perm (FiniteHomotopyClass Q (K:=K))=>f y) hh

theorem longest_inverseWord_testUpper (w : List T)
    (hw : C.toCoxeterSystem.IsReduced w)
    (hd : ∀ α,C.toCoxeterSystem.length (C.toCoxeterSystem.wordProd w*C.toCoxeterSystem.simple α)+1=
      C.toCoxeterSystem.length (C.toCoxeterSystem.wordProd w))
    (x : FiniteHomotopyClass Q (K:=K)) (t : ℤ)
    (hx : ClassTestUpper Q x (Set.range ι) t) :
    ClassTestUpper Q (inverseWordAction Q (w.map ι) x) (Set.range ι) (t-1) := by
  rintro _ ⟨α,rfl⟩ l hl c
  let cs:=C.toCoxeterSystem
  obtain ⟨v,hv,he⟩:=cs.exists_isReduced (cs.wordProd w*cs.simple α)
  have hprod : cs.wordProd (v++[α])=cs.wordProd w := by
    rw [cs.wordProd_append,cs.wordProd_singleton,← he,_root_.mul_assoc,cs.simple_mul_simple_self,_root_.mul_one]
  have hvr : cs.IsReduced (v++[α]) := by
    change cs.length (cs.wordProd (v++[α]))=(v++[α]).length
    rw [hprod,List.length_append,List.length_singleton,← hv.eq,← he]
    exact (hd α).symm
  rw [mapped_inverseWord_property Q hn C ι hmat w (v++[α]) hw hvr hprod.symm,
    List.map_append,inverseWordAction_append]
  change ClassTestExact Q (ι α) l c
    (classNegativeTwist Q (ι α) (inverseWordAction Q (v.map ι) x))
  apply (classTestExact_negative_self Q hn _ (ι α) l c).mpr
  apply inverseWord_testUpper Q hn (v.map ι) x (Set.range ι) hx
    (fun β hβ=>by obtain ⟨γ,_,rfl⟩:=List.mem_map.mp hβ; exact ⟨γ,rfl⟩)
    (ι α) ⟨α,rfl⟩ (l+1) (by omega) (c-1)

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_NegativeTwistModern
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

lemma classCapOn_iff_level_zero (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (q:ℤ) :
    ClassCapOn Q x U q ↔ ∀ α∈U,∀ k,q<k→classLevelArray Q x (α,k)=0 := by
  constructor
  · intro h α hα k hk
    rw [classLevelArray_minimal_apply]
    let :IsEmpty {i:(minimalClassModel Q x).Index //
      ((minimalClassModel Q x).complex.placement i).color=α ∧
      ((minimalClassModel Q x).complex.placement i).level=k}:=⟨by
        rintro ⟨i,hi,he⟩
        have hh:=h i (hi ▸ hα)
        omega⟩
    exact Nat.card_of_isEmpty
  · intro h i hi
    by_contra hn
    have hh:=h _ hi _ (lt_of_not_ge hn)
    rw [classLevelArray_minimal_apply] at hh
    have hp:0<Nat.card {j:(minimalClassModel Q x).Index //
      ((minimalClassModel Q x).complex.placement j).color=
        ((minimalClassModel Q x).complex.placement i).color ∧
      ((minimalClassModel Q x).complex.placement j).level=
        ((minimalClassModel Q x).complex.placement i).level} := by
      let :Nonempty {j:(minimalClassModel Q x).Index //
        ((minimalClassModel Q x).complex.placement j).color=
          ((minimalClassModel Q x).complex.placement i).color ∧
        ((minimalClassModel Q x).complex.placement j).level=
          ((minimalClassModel Q x).complex.placement i).level}:=⟨⟨i,rfl,rfl⟩⟩
      exact Nat.card_pos
    omega

lemma classCapOn_of_level_eq {x y:FiniteHomotopyClass Q (K:=K)} (U:Set V) (q:ℤ)
    (he:∀ α∈U,∀ k,classLevelArray Q y (α,k)=classLevelArray Q x (α,k))
    (hx:ClassCapOn Q x U q) : ClassCapOn Q y U q := by
  rw [classCapOn_iff_level_zero] at hx ⊢
  intro α hα k hk
  rw [he α hα k]
  exact hx α hα k hk

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

lemma finiteFamily_lowerBound {R:Type*} [Finite R]
    (x:R→FiniteHomotopyClass Q (K:=K)) : ∃ b:ℤ,∀ r,ClassLowerBound Q b (x r) := by
  obtain ⟨b,hb⟩:=Finite.exists_ge
    (fun z:Σ r:R,(minimalClassModel Q (x r)).Index=>
      ((minimalClassModel Q (x z.1)).complex.placement z.2).level)
  exact ⟨b,fun r i=>hb ⟨r,i⟩⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_NegativeTwistCapDisjoint
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u v
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma classNegativeTwist_capOn_disjoint (x : FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (hcap:ClassCapOn Q x U q) (α:V) (hα:α∉U) :
    ClassCapOn Q (classNegativeTwist Q α x) U q := by
  let E:=minimalClassModel Q x
  let F:=E.complex.negativeTwist Q α
  have hx:classOfComplex Q F=classNegativeTwist Q α x := by
    change classNegativeTwist Q α (classOfComplex Q E.complex)=_
    exact congrArg (classNegativeTwist Q α) (minimalClassModel_class Q x)
  rw [← hx]
  apply minimal_bound_transport Q F _ (minimalClassModel_minimal Q _)
    ((minimalClassModelEquivalence Q F).symm Q) (fun p=>p.color∈U→p.level≤q)
  intro i hi
  rcases i with j|j
  · exact hcap j hi
  · exact (hα hi).elim

lemma inverseWord_capOn_disjoint (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (hcap:ClassCapOn Q x U q) (hw:∀ α∈w,α∉U) :
    ClassCapOn Q (inverseWordAction Q w x) U q := by
  induction w generalizing x with
  | nil => exact hcap
  | cons α w ih =>
    exact ih _ (classNegativeTwist_capOn_disjoint Q x U q hcap α (hw α (by simp)))
      (fun β hβ=>hw β (by simp [hβ]))

omit [Fintype V] [DecidableEq A] in
lemma finiteFamily_upperBound {F:Type*} [Finite F]
    (x:F→FiniteHomotopyClass Q (K:=K)) : ∃ d:ℤ,∀ f,ClassUpperBound Q d (x f) := by
  obtain ⟨d,hd⟩:=Finite.exists_le
    (fun z : Σ f:F,(minimalClassModel Q (x f)).Index =>
      ((minimalClassModel Q (x z.1)).complex.placement z.2).level)
  exact ⟨d,fun f i=>hd ⟨f,i⟩⟩

lemma ClassTestUpper.mono {x:FiniteHomotopyClass Q (K:=K)} {U:Set V} {s t:ℤ}
    (h:ClassTestUpper Q x U s) (hst:s≤t) : ClassTestUpper Q x U t :=
  fun α hα l hl c=>h α hα l (lt_of_le_of_lt hst hl) c

variable (hn:∀ a,Q.source a≠Q.target a)

lemma inverseWord_iterate_testUpper (w:List V) (U:Set V)
    (hw:∀ (x:FiniteHomotopyClass Q (K:=K)) (t:ℤ),ClassTestUpper Q x U t →
      ClassTestUpper Q (inverseWordAction Q w x) U (t-1))
    (x:FiniteHomotopyClass Q (K:=K)) (t:ℤ) (hx:ClassTestUpper Q x U t) (n:ℕ) :
    ClassTestUpper Q ((inverseWordAction Q w)^[n] x) U (t-(n:ℤ)) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    convert hw _ _ ih using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring

lemma inverseWord_iterate_boundary (w:List V) (U:Set V) (hw:∀ α∈w,α∈U)
    (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hb:ClassCapOn Q x (Q.closedNeighborhood U \ U) q) (n:ℕ) :
    ClassCapOn Q ((inverseWordAction Q w)^[n] x) (Q.closedNeighborhood U \ U) q := by
  induction n with
  | zero => exact hb
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact inverseWord_capOn_disjoint Q w _ _ q ih (fun α hα h=>h.2 (hw α hα))

theorem finiteFamily_cap_accessible_of_test_decrement {F:Type*} [Finite F]
    (w:List V) (U:Set V) (hw:∀ α∈w,α∈U)
    (hdec:∀ (x:FiniteHomotopyClass Q (K:=K)) (t:ℤ),ClassTestUpper Q x U t →
      ClassTestUpper Q (inverseWordAction Q w x) U (t-1))
    (x:F→FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hb:∀ f,ClassCapOn Q (x f) (Q.closedNeighborhood U \ U) q) :
    ∃ n:ℕ,∀ f,ClassCapOn Q ((inverseWordAction Q w)^[n] (x f)) (Q.closedNeighborhood U) q := by
  obtain ⟨d,hd⟩:=finiteFamily_upperBound Q x
  let n:ℕ:=(d-q).toNat
  have hn:(d:ℤ)-q≤(n:ℤ) := by dsimp [n]; omega
  refine ⟨n,fun f=>?_⟩
  have hbd:=inverseWord_iterate_boundary Q w U hw (x f) q (hb f) n
  have ht:=inverseWord_iterate_testUpper Q w U hdec (x f) (d+2)
    (classTestUpper_of_generator_cap Q (x f) d (hd f) U) n
  have hcu:=classCapOn_of_test_and_boundary Q _ U q (ht.mono Q (by omega)) hbd
  intro i hi
  by_cases hui:((minimalClassModel Q ((inverseWordAction Q w)^[n] (x f))).complex.placement i).color∈U
  · exact hcu i hui
  · exact hbd i ⟨hi,hui⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveTwistModern
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

lemma positiveLayer_lowerTruncation (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (α:V) :
    classLayer Q q (classOfComplex Q ((lowerTruncation Q E hE q).positiveTwist Q α))=
      classLayer Q q (classOfComplex Q (E.positiveTwist Q α)) := by
  let f:=lowInclusion Q E _ (levelDownClosed Q E hE q)
  let R:=upperTruncation Q E hE q
  let G:=minimalClassModel Q (classOfComplex Q (R.positiveTwist Q α))
  let e₀:HomotopyEquivalence Q (R.positiveTwist Q α) G.complex:=
    (minimalClassModelEquivalence Q (R.positiveTwist Q α)).symm Q
  have hr:∀ i,q+1≤(R.placement i).level := by
    intro i
    have hi:=i.property
    change ¬(E.placement i).level≤q at hi
    change q+1≤(E.placement i).level
    omega
  have hg:∀ i,q+1≤(G.complex.placement i).level :=
    positiveTwist_lower_bound Q R G.complex hr α (minimalClassModel_minimal Q _) e₀
  have coneIso : ChainIsomorphism Q ((f.cone Q).positiveTwist Q α)
      ((f.positiveTwist Q α).cone Q) := by
    convert positiveTwistCone Q f α using 1
    all_goals try with_reducible_and_instances rfl
  let e:HomotopyEquivalence Q ((f.positiveTwist Q α).cone Q) G.complex:=
    ((coneIso.toHomotopyEquivalence Q).symm Q).trans Q
      (((lowConeReduction Q E (lowerLevelSet Q E q) (levelDownClosed Q E hE q)).positiveTwistModern Q α).trans Q e₀)
  apply classLayer_eq_of_cone_equivalence Q (f.positiveTwist Q α) G.complex e q
  intro i
  have hi:=hg i
  constructor <;> omega

omit [Fintype V] [DecidableEq A] in
lemma lowRestriction_bottom_eq_layer (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (hlo:∀ i,q≤(E.placement i).level) :
    classOfComplex Q (lowerTruncation Q E hE q)=
      classLayer Q q (classOfComplex Q E) := by
  have he:(lowerTruncation Q E hE q).reindex Q (lowPureIndex Q E q hlo)=
      E.pureLayer Q hE q := by
    apply ext_placement_differential Q <;> rfl
  rw [classLayer_minimal]
  exact (classOfComplex_reindex Q _ (lowPureIndex Q E q hlo)).trans (by rw [he])

lemma classPositiveTwist_bottom_layer (x:FiniteHomotopyClass Q (K:=K))
    (q:ℤ) (hfloor:ClassLowerBound Q q x) (α:V) :
    classLayer Q q (classPositiveTwist Q α x)=
      classLayer Q q (classPositiveTwist Q α (classLayer Q q x)) := by
  let E:=minimalClassModel Q x
  have hE:=minimalClassModel_minimal Q x
  have hx:classOfComplex Q E.complex=x:=minimalClassModel_class Q x
  have hl:=positiveLayer_lowerTruncation Q E.complex hE q α
  have he:=lowRestriction_bottom_eq_layer Q E.complex hE q hfloor
  change classLayer Q q (classPositiveTwist Q α (classOfComplex Q (lowerTruncation Q E.complex hE q)))=
    classLayer Q q (classPositiveTwist Q α (classOfComplex Q E.complex)) at hl
  rw [he,hx] at hl
  exact hl.symm

theorem positiveWord_bottom_layer (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    (q:ℤ) (hfloor:ClassLowerBound Q q x) :
    classLayer Q q (positiveWordAction Q w x)=
      classLayer Q q (positiveWordAction Q w (classLayer Q q x)) := by
  induction w generalizing x with
  | nil=>exact (classLayer_idempotent Q x q).symm
  | cons α w ih=>
    have hc:=classPositiveTwist_bottom_layer Q (positiveWordAction Q w x) q
      (positiveWord_lower_bound Q w x hfloor) α
    have hc':=classPositiveTwist_bottom_layer Q (positiveWordAction Q w (classLayer Q q x)) q
      (positiveWord_lower_bound Q w _ (classLayer_lowerBound Q x q)) α
    exact hc.trans ((congrArg (fun y=>classLayer Q q (classPositiveTwist Q α y))
      (ih x hfloor)).trans hc'.symm)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnfoldedHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Geometric CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable

variable {S : Type*} [Fintype S] [LinearOrder S]

theorem unfoldedHom_right_ascent (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (w : (restrictedMatrix M J).Group) (α : J × FusionLabel (fusionLabelSize M)) :
    let c := (restrictedMatrix M J).toCoxeterSystem
    let d := (unfoldedMatrix M J).toCoxeterSystem
    d.length (unfoldedHom M J hJ w*d.simple α)=d.length (unfoldedHom M J hJ w)+1 ↔
      c.length (w*c.simple α.1)=c.length w+1 := by
  dsimp only
  have h := unfoldedHom_left_ascent M J hJ w⁻¹ α
  dsimp only at h
  rw [map_inv,← inverse_right_length,← inverse_right_length,inv_inv,inv_inv,
    CoxeterSystem.length_inv,CoxeterSystem.length_inv] at h
  exact h

theorem unfoldedHom_right_descent (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (w : (restrictedMatrix M J).Group) (α : J × FusionLabel (fusionLabelSize M)) :
    let c := (restrictedMatrix M J).toCoxeterSystem
    let d := (unfoldedMatrix M J).toCoxeterSystem
    d.length (unfoldedHom M J hJ w*d.simple α)+1=d.length (unfoldedHom M J hJ w) ↔
      c.length (w*c.simple α.1)+1=c.length w := by
  dsimp only
  have h := unfoldedHom_right_ascent M J hJ w α
  have h₁ := (unfoldedMatrix M J).toCoxeterSystem.length_mul_simple (unfoldedHom M J hJ w) α
  have h₂ := (restrictedMatrix M J).toCoxeterSystem.length_mul_simple w α.1
  dsimp only at h
  omega

theorem unfolded_longest (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (z : (restrictedMatrix M J).Group)
    (hz : ∀ w,(restrictedMatrix M J).toCoxeterSystem.length w≤
      (restrictedMatrix M J).toCoxeterSystem.length z) (v : (unfoldedMatrix M J).Group) :
    (unfoldedMatrix M J).toCoxeterSystem.length v≤
      (unfoldedMatrix M J).toCoxeterSystem.length (unfoldedHom M J hJ z) := by
  apply length_le_of_all_descents (unfoldedMatrix M J).toCoxeterSystem (unfoldedHom M J hJ z)
  intro α
  exact (unfoldedHom_right_descent M J hJ z α).mpr
    (all_descents_of_longest (restrictedMatrix M J).toCoxeterSystem z hz α.1)

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

theorem source_finiteFamily_cap_accessible {F:Type*} [Finite F]
    (J:Set S) (hJ:IsSpherical M J)
    (x:F→FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hb:∀ f,ClassCapOn Q (x f)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M J)) \
        Set.range (unfoldedInclusion M J)) q) :
    ∃ g∈artinParabolic M J,∀ f,ClassCapOn Q (aw g (x f))
      (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q := by
  have : Finite (restrictedMatrix M J).Group:=restricted_finite M J hJ
  obtain ⟨z,hz⟩:=exists_longest (restrictedMatrix M J).toCoxeterSystem
  obtain ⟨u,hu,he⟩:=(restrictedMatrix M J).toCoxeterSystem.exists_isReduced z
  let w:=fusionExpandedWord (fusionLabelSize M) u
  have hw:(unfoldedMatrix M J).toCoxeterSystem.IsReduced w:=unfolded_reducedWord M J hJ u hu
  have hp:(unfoldedMatrix M J).toCoxeterSystem.wordProd w=unfoldedHom M J hJ z := by
    rw [he,unfoldedHom_wordProd]
  have hlong:∀ β,(unfoldedMatrix M J).toCoxeterSystem.length
      ((unfoldedMatrix M J).toCoxeterSystem.wordProd w*(unfoldedMatrix M J).toCoxeterSystem.simple β)+1=
      (unfoldedMatrix M J).toCoxeterSystem.length ((unfoldedMatrix M J).toCoxeterSystem.wordProd w) := by
    rw [hp]
    exact all_descents_of_longest (unfoldedMatrix M J).toCoxeterSystem _
      (unfolded_longest M J hJ z hz)
  have hdec:=longest_inverseWord_testUpper Q (K:=K) hn (unfoldedMatrix M J) (unfoldedInclusion M J)
    (unfolded_ordinaryMatrix M J hJ) w hw hlong
  obtain ⟨n,hcap⟩:=finiteFamily_cap_accessible_of_test_decrement Q
    (w.map (unfoldedInclusion M J)) (Set.range (unfoldedInclusion M J))
    (fun β hβ=>by obtain ⟨α,_,rfl⟩:=List.mem_map.mp hβ; exact ⟨α,rfl⟩) hdec x q hb
  let a:=wordArtin M (u.map Subtype.val)
  have ha:a∈artinParabolic M J := wordArtin_mem_parabolic M J _
    (by intro s hs; obtain ⟨i,_,rfl⟩:=List.mem_map.mp hs; exact i.property)
  refine ⟨a⁻¹^n,(artinParabolic M J).pow_mem ((artinParabolic M J).inv_mem ha) n,fun f=>?_⟩
  have hact: (fun y : FiniteHomotopyClass Q (K:=K)=>aw a⁻¹ y)=
      inverseWordAction Q (w.map (unfoldedInclusion M J)) := by
    funext y
    rw [sourceArtinAction_negativeWord]
    congr 2
    simpa only [List.map_map,Function.comp_def,w,unfoldedInclusion] using
      fusionExpandedWord_map (fusionLabelSize M) (fun i : J=>(Sum.inl (i:S) : S⊕Unit)) u
  have hpow:aw (a⁻¹^n) (x f)= (inverseWordAction Q (w.map (unfoldedInclusion M J)))^[n] (x f) := by
    rw [map_pow]
    change ((aw a⁻¹)^n) (x f)=_
    rw [Equiv.Perm.coe_pow]
    exact congrArg (fun t : FiniteHomotopyClass Q (K:=K)→FiniteHomotopyClass Q (K:=K) => t^[n] (x f)) hact
  rw [hpow]
  exact hcap f

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionColorWord
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
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd
local notation "T" => fusionPacketPerm m d hd hdiag (K:=K)

lemma fusionColorWord_action (j:V) (x:FiniteHomotopyClass Q (K:=K)) :
    positiveWordAction Q (fusionColorWord m j) x=T j x := by
  have h:=fusionExpandedWord_action m d hd hdiag [j] x
  simpa only [fusionExpandedWord,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.map_cons,List.map_nil,fusionWordPacketPerm,fusionSignedPacketPerm,ite_true, if_true,
    fusionColorWord,_root_.mul_one] using h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "aw" => sourceArtinAction M (K:=K)
local notation "T" => fusionPacketPerm m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (K:=K)

lemma sourcePositiveWord_cons (J:Set S) (j:J) (w:List J) (x:FiniteHomotopyClass Q (K:=K)) :
    sourcePositiveWord M J (j::w) x=T (.inl j) (sourcePositiveWord M J w x) := by
  simp only [sourcePositiveWord,List.map_cons,wordArtin,List.map_cons,List.prod_cons,map_mul,
    sourceArtinAction_generator,Equiv.Perm.mul_apply]

lemma sourcePositiveWord_lowerBound (J:Set S) (w:List J) (x:FiniteHomotopyClass Q (K:=K))
    (q:ℤ) (hx:ClassLowerBound Q q x) :
    ClassLowerBound Q q (sourcePositiveWord M J w x) := by
  unfold sourcePositiveWord
  rw [sourceArtinAction_positiveWord]
  exact positiveWord_lower_bound Q _ x hx

lemma sourcePositiveWord_reduced_eq (J:Set S) (u v:List J)
    (hu:(restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (hv:(restrictedMatrix M J).toCoxeterSystem.IsReduced v)
    (he:(restrictedMatrix M J).toCoxeterSystem.wordProd u=
      (restrictedMatrix M J).toCoxeterSystem.wordProd v)
    (x:FiniteHomotopyClass Q (K:=K)) : sourcePositiveWord M J u x=sourcePositiveWord M J v x := by
  let f:J→Equiv.Perm (FiniteHomotopyClass Q (K:=K)):=fun j=>T (.inl j)
  have hb:∀ i j:J,((altList i j (restrictedMatrix M J i j)).map f).prod=
      ((altList j i (restrictedMatrix M J i j)).map f).prod := by
    intro i j
    have hh:=sourcePacket_braid M (K:=K) i j
    simpa only [← altList_map,List.map_map,Function.comp_def,restrictedMatrix_apply,f] using hh
  have hh:=reduced_word_property (restrictedMatrix M J).toCoxeterSystem f hb u v hu hv he
  have hperm:aw (wordArtin M (u.map Subtype.val))=aw (wordArtin M (v.map Subtype.val)) := by
    simpa only [wordArtin,map_list_prod,List.map_map,sourceArtinAction_generator,Function.comp_def,f] using hh
  exact congrArg (fun p=>p x) hperm

lemma sourceBottomWord_cons_socle_zero (J:Set S) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K))
    (hx:ClassLowerBound Q q x) (j:J) (w:List J) (L:FusionLabel m) (c:ℤ) :
    classLayerSocleDimension Q q (.inl j,L) c (sourceBottomWord M J q (j::w) x)=0 := by
  rw [sourceBottomWord,classLayerSocleDimension_layer,sourcePositiveWord_cons]
  convert classPacketPerm_bottom_socle_zero Q hn (fun L:FusionLabel m=>(Sum.inl (j:S),L))
    (fusionColor_orthogonal m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (.inl j))
    (sourcePositiveWord M J w x) (sourcePositiveWord_lowerBound M J w x q hx) L c using 1
  all_goals try with_reducible_and_instances rfl
  congr 9

theorem sourceBottomWord_socle_ascent (J:Set S) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K))
    (hx:ClassLowerBound Q q x) (w:List J)
    (hw:(restrictedMatrix M J).toCoxeterSystem.IsReduced w) (j:J)
    (hs:∃ L c,0 < classLayerSocleDimension Q q (.inl j,L) c (sourceBottomWord M J q w x)) :
    (restrictedMatrix M J).toCoxeterSystem.IsReduced (j::w) := by
  let cs:=(restrictedMatrix M J).toCoxeterSystem
  have ha:¬cs.IsLeftDescent (cs.wordProd w) j := by
    intro hj
    obtain ⟨v,hv,hev⟩:=cs.exists_isReduced (cs.simple j*cs.wordProd w)
    have hprod:cs.wordProd (j::v)=cs.wordProd w := by
      rw [CoxeterSystem.wordProd_cons,← hev,cs.simple_mul_simple_cancel_left]
    have hred:cs.IsReduced (j::v) := by
      change cs.length (cs.wordProd (j::v))=v.length+1
      rw [hprod,← hv.eq,← hev]
      exact (cs.isLeftDescent_iff.mp hj).symm
    have he:=sourcePositiveWord_reduced_eq M J w (j::v) hw hred hprod.symm x
    obtain ⟨L,c,hsc⟩:=hs
    have hval:sourceBottomWord M J q w x=sourceBottomWord M J q (j::v) x := congrArg (classLayer Q q) he
    rw [hval,sourceBottomWord_cons_socle_zero M J q x hx j v L c] at hsc
    exact (Nat.lt_irrefl 0) hsc
  change cs.length (cs.simple j*cs.wordProd w)=w.length+1
  rw [cs.not_isLeftDescent_iff.mp ha,hw.eq]

lemma bounded_word_saturation {R:Type*} (B:ℕ) (good inv:List R→Prop)
    (move:List R→R→Prop) (hgood:good []) (hinv:inv [])
    (bound:∀ w,good w→w.length≤B)
    (extend:∀ w,good w→∀ j,move w j→ good (j::w))
    (preserve:∀ w,good w→inv w→∀ j,move w j→inv (j::w)) :
    ∃ w,good w ∧ inv w ∧ ∀ j,¬move w j := by
  classical
  have go:∀ n:ℕ,∀ w:List R,B-w.length=n→ good w→inv w→
      ∃ v,good v ∧ inv v ∧ ∀ j,¬move v j := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih=>
      intro w hm hw hv
      by_cases hz:∀ j,¬move w j
      · exact ⟨w,hw,hv,hz⟩
      · push Not at hz
        obtain ⟨j,hj⟩:=hz
        have hw':=extend w hw j hj
        have hb:=bound (j::w) hw'
        have hlt:B-(j::w).length<n := by simp only [List.length_cons] at hb ⊢; omega
        exact ih _ hlt (j::w) rfl hw' (preserve w hw hv j hj)
  exact go B [] (by simp) hgood hinv

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_BottomWordNil
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "Q" => fusionQuiver m d hd
local notation "T" => fusionPacketPerm m d hd hdiag (K:=K)

lemma sourceBottomWord_nil (J:Set S) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :
    sourceBottomWord M J q [] x=classLayer Q q x := by
  simp only [sourceBottomWord,sourcePositiveWord,List.map_nil,wordArtin,
    List.prod_nil,map_one,Equiv.Perm.one_apply]

lemma sourceBottomWord_cons (J:Set S) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K))
    (hx:ClassLowerBound Q q x) (j:J) (w:List J) :
    sourceBottomWord M J q (j::w) x=
      classLayer Q q (T (.inl j) (sourceBottomWord M J q w x)) := by
  unfold sourceBottomWord
  rw [sourcePositiveWord_cons]
  have h:=positiveWord_bottom_layer Q (fusionColorWord m (.inl (j:S)))
    (sourcePositiveWord M J w x) q (sourcePositiveWord_lowerBound M J w x q hx)
  have hc (y:FiniteHomotopyClass Q (K:=K)) :
      positiveWordAction Q (fusionColorWord m (.inl (j:S))) y=T (.inl j) y := by
    convert fusionColorWord_action m d hd hdiag (.inl (j:S)) y using 1
    all_goals try with_reducible_and_instances rfl
    congr 9
    exact Subsingleton.elim _ _
  rw [hc,hc] at h
  exact h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionSignedPacketExterior
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
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)

lemma fusionOrbitMultiplicity_frame (hm:∀ e,2 ≤ m e)
    (w:List (V × Bool)) (s:V) (hs:∀ b∈w,b.1≠s) :
    fusionOrbitMultiplicity m d hd hdiag hm w s 0 s=1 := by
  let L:FusionLabel m:=fun e=>⟨0,by have:=hm e; omega⟩
  have hc:=congrFun (fusionOrbitWeightedVector_eq m d hd hdiag hm w s 0) (s,L)
  simp only [fusionOrbitWeightedVector,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    fusionOrbitLayer_generator,fusionFold] at hc
  simp_rw [fusionOrbit_frame_level m d hd hdiag w s _ _ _ hs] at hc
  simp only [and_true,↓reduceIte,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    mul_ite,_root_.mul_one,MulZeroClass.mul_zero,Finset.sum_ite_eq',Finset.mem_univ] at hc
  apply mul_right_cancel₀ (fusionWeight_pos m hm L).ne'
  rw [_root_.one_mul]
  simpa only [mul_comm] using hc.symm

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

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PacketWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourcePacket_frame (w:List (S × Bool)) :
    sourcePacketMultiplicity M w 0 (.inr ())=1 := by
  apply fusionOrbitMultiplicity_frame
  intro b hb
  obtain ⟨a,_,rfl⟩:=List.mem_map.mp hb
  exact Sum.inl_ne_inr

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_SignedLetter
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M

lemma sourcePacketOrbit_signedPrepend (w:List (S×Bool))
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (L:FusionLabel m) :
    fusionPacketOrbit m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
      (sourcePacketWord w++z) s L=
    sourceArtinAction M (sourceSignedWord M w)
      (fusionPacketOrbit m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) z s L) := by
  rw [sourceArtinAction_signedWord]
  induction w with
  | nil=>rfl
  | cons a w ih=>
    change fusionSignedPacketPerm m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
      (.inl a.1,a.2) (_)=_
    exact congrArg (fusionSignedPacketPerm m d (coxeterFusionEdge_symm M)
      (coxeterFusionEdge_diag M) (.inl a.1,a.2)) ih

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnfoldedInclusionRange
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "Q" => fusionQuiver m d hd
local notation "aw" => sourceArtinAction M (K:=ℂ)

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

lemma sourceArtinAction_cap_exterior (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (x:FiniteHomotopyClass Q (K:=ℂ)) (U:Set (FusionVertex (V:=S⊕Unit) m))
    (hU:∀ α∈U,α.1∉Sum.inl '' J) (q:ℤ) (hx:ClassCapOn Q x U q) :
    ClassCapOn Q (aw g x) U q := by
  apply classCapOn_of_level_eq Q U q _ hx
  intro α hα k
  exact sourceArtinAction_level_exterior M J g hg x α.1 (hU α hα) α.2 k

lemma source_cap_closed_of_cap_parts (I J:Set S) (_ : J⊆I)
    (x:FiniteHomotopyClass Q (K:=ℂ)) (q:ℤ)
    (hJ:ClassCapOn Q x (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (hE:ClassCapOn Q x (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
      fusionColorRegion m (Sum.inl '' J)) q) :
    ClassCapOn Q x (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I))) q := by
  intro i hi
  by_contra hout
  apply hout
  apply hE i
  refine ⟨hi,?_⟩
  intro hj
  apply hout
  apply hJ i
  apply Or.inl
  rwa [unfoldedInclusion_range]

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
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag

namespace IsolatedIterationData
variable {M} (D:IsolatedIterationData M)

lemma socle_below (z:List ((S⊕Unit)×Bool)) (b k:ℤ)
    (hb:∀ L,ClassLowerBound Q b (O z D.s L)) (hk:k<b) : D.openSocle z k := by
  intro H α hα c
  exact classLayerSocleDimension_below Q (O z D.s H) b k (hb H) hk α c

end IsolatedIterationData
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FamilySocleFiniteTermination
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)

theorem source_family_socle_finite_termination {R:Type*}
    (J:Set S) (hJ:IsSpherical M J) (q:ℤ)
    (x:R→FiniteHomotopyClass Q (K:=K)) (hx:∀ r,ClassLowerBound Q q (x r))
    (P:List J→Prop) (hP:P [])
    (step:∀ w,(restrictedMatrix M J).toCoxeterSystem.IsReduced w→P w→
      ∀ j:J,(∃ r L c,0 < classLayerSocleDimension Q q (.inl j,L) c
        (sourceBottomWord M J q w (x r)))→P (j::w)) :
    ∃ w:List J,(restrictedMatrix M J).toCoxeterSystem.IsReduced w ∧ P w ∧
      ∀ r (j:J) L c,classLayerSocleDimension Q q (.inl j,L) c
        (sourceBottomWord M J q w (x r))=0 := by
  have : Finite (restrictedMatrix M J).Group:=restricted_finite M J hJ
  let:=Fintype.ofFinite (restrictedMatrix M J).Group
  let cs:=(restrictedMatrix M J).toCoxeterSystem
  let B:=Finset.univ.sup cs.length
  let move:List J→J→Prop:=fun w j=>∃ r L c,
    0 < classLayerSocleDimension Q q (.inl j,L) c (sourceBottomWord M J q w (x r))
  have bound (w:List J) (hw:cs.IsReduced w) : w.length≤B := by
    rw [← hw.eq]
    exact Finset.le_sup (f:=cs.length) (Finset.mem_univ _)
  have extend (w:List J) (hw:cs.IsReduced w) (j:J) (hj:move w j) : cs.IsReduced (j::w) := by
    obtain ⟨r,L,c,h⟩:=hj
    exact sourceBottomWord_socle_ascent M J q (x r) (hx r) w hw j ⟨L,c,h⟩
  obtain ⟨w,hw,hp,hz⟩:=bounded_word_saturation B cs.IsReduced P move
    (by simp [cs,CoxeterSystem.IsReduced]) hP bound extend step
  refine ⟨w,hw,hp,?_⟩
  intro r j L c
  apply Nat.eq_zero_of_not_pos
  intro hc
  exact hz j ⟨r,L,c,hc⟩

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Stage
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {M:CoxeterMatrix S}
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag

namespace IsolatedIterationData
variable (D:IsolatedIterationData M)

theorem stage (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
    (b t:ℤ) (ht:t<D.q) (hb:∀ H,ClassLowerBound Q b (O z D.s H))
    (hp:∀ k,k<t→D.openSocle z k) :
    ∃ z',D.valid z' ∧ D.capped z' ∧
      (∀ H,ClassLowerBound Q b (O z' D.s H)) ∧
      (∀ k,k<t+1→D.openSocle z' k) := by
  let x:=fun H=>classLayer Q t (O z D.s H)
  have hx:∀ H,ClassLowerBound Q t (x H):=fun _=>
    classLowerBound_of_representative Q _ (fun index=>le_of_eq index.property.symm)
  let P:List D.J→Prop:=fun w=>∃ z',D.valid z' ∧ D.capped z' ∧
    (∀ H,ClassLowerBound Q b (O z' D.s H)) ∧
    (∀ k,k<t→D.openSocle z' k) ∧
    ∀ H,classLayer Q t (O z' D.s H)=sourceBottomWord M D.J t w (x H)
  have hP:P [] := by
    refine ⟨z,hz,hc,hb,hp,fun H=>?_⟩
    rw [sourceBottomWord_nil,classLayer_idempotent]
  have step:∀ w,(restrictedMatrix M D.J).toCoxeterSystem.IsReduced w→P w→
      ∀ j:D.J,(∃ H L c,0 < classLayerSocleDimension Q t (.inl j,L) c
        (sourceBottomWord M D.J t w (x H)))→P (j::w) := by
    intro w _ hPw j hs
    obtain ⟨z',hz',hc',hb',hp',he⟩:=hPw
    have hs':∃ H L c,0 < classLayerSocleDimension Q t (.inl j,L) c (O z' D.s H) := by
      obtain ⟨H,L,c,hs⟩:=hs
      rw [← he H,classLayerSocleDimension_layer] at hs
      exact ⟨H,L,c,hs⟩
    have hm:=D.stage_move z' hz' hc' j b t ht hb' hp' hs'
    refine ⟨((.inl j,true)::z'),D.move z' hz' j,hm.1,hm.2.1,hm.2.2.1,fun H=>?_⟩
    rw [hm.2.2.2 H,he H,sourceBottomWord_cons M D.J t (x H) (hx H)]
  obtain ⟨w,_,hPw,hs⟩:=source_family_socle_finite_termination M D.J D.hJ t x hx P hP step
  obtain ⟨z',hz',hc',hb',hp',he⟩:=hPw
  refine ⟨z',hz',hc',hb',fun k hk=>?_⟩
  by_cases hkt:k<t
  · exact hp' k hkt
  · have hkt:k=t:=by omega
    subst k
    intro H α hα c
    obtain ⟨j,hj,heα⟩:=hα
    have hf:α.1=.inl j:=heα.symm
    have hsc:=hs H ⟨j,hj⟩ α.2 c
    rw [← he H,classLayerSocleDimension_layer] at hsc
    have hαeq:(Sum.inl j,α.2)=α:=Prod.ext hf.symm rfl
    rwa [hαeq] at hsc

theorem saturate (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
    (b t:ℤ) (ht:t<D.q) (hb:∀ H,ClassLowerBound Q b (O z D.s H)) :
    ∃ z',D.valid z' ∧ D.capped z' ∧
      (∀ H,ClassLowerBound Q b (O z' D.s H)) ∧ D.openSocle z' t := by
  let P:ℤ→Prop:=fun k=>∃ z',D.valid z' ∧ D.capped z' ∧
    (∀ H,ClassLowerBound Q b (O z' D.s H)) ∧ (∀ l,l<k+1→D.openSocle z' l)
  have hP:∀ k,k<t+1→P k := by
    refine integer_upward (P:=P) b (t+1) ?_ ?_
    · intro k hk
      exact ⟨z,hz,hc,hb,fun l hl=>D.socle_below z b l hb (by omega)⟩
    · intro k _ hkt hp
      obtain ⟨z',hz',hc',hb',hp'⟩:=hp
      apply D.stage z' hz' hc' b k (by omega) hb'
      intro l hl
      exact hp' l (by omega)
  obtain ⟨z',hz',hc',hb',hp'⟩:=hP t (by omega)
  exact ⟨z',hz',hc',hb',hp' t (by omega)⟩

end IsolatedIterationData
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Contradiction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix

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
local notation "C" => fusionFoldedCartan m d

namespace IsolatedIterationData
variable (D:IsolatedIterationData M)

theorem contradiction (hI:D.I.Nonempty) (hq:0<D.q)
    (hframe:∀ z,D.valid z→μ z D.s 0 (.inr ())=1)
    (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z) : False := by
  obtain ⟨b,hb⟩:=finiteFamily_lowerBound Q (O z D.s)
  obtain ⟨z',hz',hc',hb',hs⟩:=D.saturate z hz hc b 0 hq hb
  have hf:(Sum.inr () : S⊕Unit)∉Sum.inl '' D.I := by
    rintro ⟨i,hi,he⟩
    exact Sum.inl_ne_inr he
  obtain ⟨i,hi⟩:=hI
  have ha:∃ u∈Sum.inl '' D.I,C (.inr ()) u<0 := by
    refine ⟨.inl i,⟨i,hi,rfl⟩,?_⟩
    have hC : C = framedCartan M := by
      convert fusionFoldedCartan_eq_framedCartan M using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      exact Subsingleton.elim _ _
    rw [hC]
    change (-1:ℝ)<0
    norm_num
  have hh:=(D.separation z' hz' hc' 0 hs).1 (.inr ()) hf ha
  rw [hframe z' hz'] at hh
  exact one_ne_zero hh

end IsolatedIterationData
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CosetOrbit
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
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag

lemma sourceCosetOrbit_cap_exterior (J:Set S) (z₀:List ((S⊕Unit)×Bool)) (s:S⊕Unit)
    (z:List ((S⊕Unit)×Bool)) (hz:SourceCosetOrbit M J z₀ s z)
    (U:Set (FusionVertex (V:=S⊕Unit) m)) (hU:∀ α∈U,α.1∉Sum.inl '' J) (q:ℤ)
    (hc:∀ L,ClassCapOn Q (O z₀ s L) U q) : ∀ L,ClassCapOn Q (O z s L) U q := by
  obtain ⟨g,hg,he⟩:=hz
  intro L
  rw [he]
  exact sourceArtinAction_cap_exterior M J g hg (O z₀ s L) U hU q (hc L)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CosetOrbitCap
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
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "aw" => sourceArtinAction M (K:=ℂ)

theorem sourceCosetOrbit_exists_cap (I J:Set S) (hJI:J⊆I) (hJ:IsSpherical M J)
    (z₀:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ)
    (hE:∀ L,ClassCapOn Q (O z₀ s L)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
        fusionColorRegion m (Sum.inl '' J)) q) :
    ∃ z,SourceCosetOrbit M J z₀ s z ∧
      ∀ L,ClassCapOn Q (O z s L)
        (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I))) q := by
  have hsub:fusionColorRegion (V:=S⊕Unit) m (Sum.inl '' J)⊆fusionColorRegion m (Sum.inl '' I) :=
    fun _ hα=>Set.image_mono hJI hα
  have hb:∀ L,ClassCapOn Q (O z₀ s L)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M J)) \
        Set.range (unfoldedInclusion M J)) q := by
    intro L
    apply ClassCapOn.mono Q (hE L)
    rw [unfoldedInclusion_range]
    intro α hα
    exact ⟨closedNeighborhood_mono Q hsub hα.1,hα.2⟩
  obtain ⟨g,hg,hcap⟩:=source_finiteFamily_cap_accessible M J hJ (O z₀ s) q hb
  obtain ⟨w,_,he⟩:=artinParabolic_signed_word M J g hg
  let z:=sourcePacketWord w++z₀
  have hz:SourceCosetOrbit M J z₀ s z := by
    refine ⟨g,hg,fun L=>?_⟩
    rw [← he]
    exact sourcePacketOrbit_signedPrepend M w z₀ s L
  refine ⟨z,hz,fun L=>?_⟩
  apply source_cap_closed_of_cap_parts M I J hJI (O z s L) q
  · have hact:O z s L=aw g (O z₀ s L) := by
      rw [← he]
      exact sourcePacketOrbit_signedPrepend M w z₀ s L
    rw [hact]
    exact hcap L
  · apply sourceCosetOrbit_cap_exterior M J z₀ s z hz _ _ q hE L
    intro α hα
    exact hα.2

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FrameFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceMultiplicity_word (w:List (S×Bool)) (k:ℤ) :
    sourceMultiplicity M (sourceSignedWord M w) k=sourcePacketMultiplicity M w k := by
  unfold sourceMultiplicity
  rw [sourceFrameFamily_word,fusionFamilyMultiplicity_orbit]
  rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_IsolatedHarmonicLayer
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
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d
local notation "aw" => sourceArtinAction M (K:=ℂ)

theorem source_isolated_harmonic_layer (I J:Set S) (hI:I.Nonempty)
    (hJI:J⊆I) (hJ:IsSpherical M J) (w:List (S×Bool)) (q:ℤ) (hq:0<q)
    (c:S⊕Unit→ℝ) (hc:∀ v,0 ≤ c v) (hcSupp:∀ v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀ v,v∈Sum.inl '' I→0 < c v)
    (hcNull:∀ v,v∈Sum.inl '' I→(C *ᵥ c) v=0)
    (hE:∀ L,ClassCapOn Q (O (sourcePacketWord w) (.inr ()) L)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
        fusionColorRegion m (Sum.inl '' J)) q)
    (hdata:∀ v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' J) ∨
      (v∉Sum.inl '' I ∧ ∃ u∈Sum.inl '' I,C v u<0)→
      μ (sourcePacketWord w) (.inr ()) q v=c v)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (aw g (O (sourcePacketWord w) (.inr ()) L))
        (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I))) q)→
      ∀ j:J,c (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>aw g (O (sourcePacketWord w) (.inr ()) L)) q (.inl (j:S))) : False := by
  let z₀:=sourcePacketWord w
  have hstrict:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (aw g (O z₀ (.inr ()) L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,c (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>aw g (O z₀ (.inr ()) L)) q (.inl (j:S)) := by
    intro g hg hcap
    apply huniv g hg
    intro L
    apply source_cap_closed_of_cap_parts M I J hJI _ q (hcap L)
    exact sourceArtinAction_cap_exterior M J g hg (O z₀ (.inr ()) L) _
      (fun α hα=>hα.2) q (hE L)
  let D:=isolatedDataOfCoset M I J hJI hJ z₀ (.inr ()) q c hc hcSupp hcPos hcNull hdata hstrict
  obtain ⟨z,hz,hcap⟩:=sourceCosetOrbit_exists_cap M I J hJI hJ z₀ (.inr ()) q hE
  apply D.contradiction hI hq _ z hz hcap
  intro z' hz'
  have he:=sourceCosetOrbit_multiplicity_exterior M J z₀ (.inr ()) z' hz'
    (.inr ()) (by rintro ⟨_,_,he⟩; exact Sum.inl_ne_inr he) 0
  exact he.trans (sourcePacket_frame M w)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FoldedCartan
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
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

omit [Fintype S] in
lemma sourceFoldedCartan_eq :
    fusionFoldedCartan m (coxeterFusionEdge M)=framedCartan M := by
  convert fusionFoldedCartan_eq_framedCartan M using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  exact Subsingleton.elim _ _

theorem sourceGroup_isolated_harmonic_layer (I J:Set S) (hI:I.Nonempty)
    (hJI:J⊆I) (hJ:IsSpherical M J) (x:Artin M) (q:ℤ) (hq:0<q)
    (c:S⊕Unit→ℝ) (hc:∀v,0 ≤ c v) (hcSupp:∀v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀v,v∈Sum.inl '' I→0 < c v)
    (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hE:∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
        fusionColorRegion m (Sum.inl '' J)) q)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' J) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→
      sourceMultiplicity M x q v=c v)
    (huniv:∀g∈artinParabolic M J,
      (∀H,ClassCapOn Q (sourceFrameFamily M (g*x) H)
        (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I))) q)→
      ∀j:J,c (.inl (j:S)) < sourceMultiplicity M (g*x) q (.inl (j:S))) : False := by
  obtain ⟨w,rfl⟩:=sourceSignedWord_surjective M x
  apply source_isolated_harmonic_layer M I J hI hJI hJ w q hq c hc hcSupp hcPos
  · simpa only [sourceFoldedCartan_eq] using hcNull
  · simpa only [sourceFrameFamily_word] using hE
  · simpa only [sourceFoldedCartan_eq,sourceMultiplicity_word,sourcePacketMultiplicity] using hdata
  · intro g hg hcap j
    have he:sourceFrameFamily M (g*sourceSignedWord M w)=
        (fun H=>sourceArtinAction M g (fusionPacketOrbit m (coxeterFusionEdge M)
          (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (sourcePacketWord w) (.inr ()) H)) := by
      funext H
      rw [sourceFrameFamily_mul,sourceFrameFamily_word]
    have hh:=huniv g hg (by simpa only [he] using hcap) j
    simpa only [sourceMultiplicity,he] using hh

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_FrameFamilyWeightedLevel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => fusionLabelSize_ge_two M
local notation "Q" => fusionQuiver m d hd

lemma sourceFrameFamily_weighted_level (z:Artin M) (q:ℤ)
    (α:FusionVertex (V:=S⊕Unit) m) :
    (∑H,fusionWeight m H*(classLevelArray Q (sourceFrameFamily M z H) (α,q):ℝ))=
      fusionWeight m α.2*sourceMultiplicity M z q α.1 := by
  obtain ⟨w,rfl⟩:=sourceSignedWord_surjective M z
  rw [sourceMultiplicity_word,sourceFrameFamily_word]
  have h:=congrFun (fusionOrbitWeightedVector_eq m d hd hdiag hm (sourcePacketWord w) (.inr ()) q) α
  simpa only [fusionOrbitWeightedVector,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    fusionOrbitLayer_generator,fusionFold,sourcePacketMultiplicity] using h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_MultiplicityZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma sourceMultiplicity_zero_iff (z:Artin M) (q:ℤ) (v:S⊕Unit) :
    sourceMultiplicity M z q v=0 ↔
      ∀ H L,classLevelArray Q (sourceFrameFamily M z H) ((v,L),q)=0 := by
  constructor
  · intro hz H L
    have he:=sourceFrameFamily_weighted_level M z q (v,L)
    rw [hz,MulZeroClass.mul_zero] at he
    have hnn:∀ H:FusionLabel m,0≤fusionWeight m H *
        (classLevelArray Q (sourceFrameFamily M z H) ((v,L),q):ℝ) := by
      intro H
      exact mul_nonneg (fusionWeight_pos m (fusionLabelSize_ge_two M) H).le (Nat.cast_nonneg _)
    have hh:= (Finset.sum_eq_zero_iff_of_nonneg (fun H _=>hnn H)).mp he H (Finset.mem_univ H)
    have hz':(classLevelArray Q (sourceFrameFamily M z H) ((v,L),q):ℝ)=0 :=
      (mul_eq_zero.mp hh).resolve_left (ne_of_gt (fusionWeight_pos m (fusionLabelSize_ge_two M) H))
    exact_mod_cast hz'
  · intro hz
    let L:=fusionZeroLabel m (fusionLabelSize_ge_two M)
    have he:=sourceFrameFamily_weighted_level M z q (v,L)
    simp only [hz,Nat.cast_zero,MulZeroClass.mul_zero,Finset.sum_const_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left
      (ne_of_gt (fusionWeight_pos m (fusionLabelSize_ge_two M) L))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CosetVectorNullPatch
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
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma sourceCosetVector_of_null_patch (P:Deligne M) (x:Artin M) (hx:x∈P.val.2)
    (I:Set S) (hPI:P.val.1⊆I) (q:ℤ) (c:S⊕Unit→ℝ)
    (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→
      sourceMultiplicity M x q v=c v) (i:S) (hi:i∈P.val.1) :
    sourceCosetVector M P q (.inl i)=c (.inl i) := by
  let p:S⊕Unit→ℝ:=fun v=>if v∈Sum.inl '' P.val.1 then c v else sourceMultiplicity M x q v
  have hp:p=sourceHarmonicAt M P.val.1 x q := by
    apply harmonicExtension_unique _ _ (framed_spherical_posDef M _ P.property.1)
    · intro v hv
      exact ite_eq_right hv
    · intro j
      exact null_patch (framedCartan_symm M) (framedCartan_off M)
        (Sum.inl '' I) (Sum.inl '' P.val.1) (Set.image_mono hPI) c
        (sourceMultiplicity M x q) hcNull hdata j j.property
  rw [sourceCosetVector_eq M P x hx q,←hp]
  exact ite_eq_left ⟨i,hi,rfl⟩

theorem sourceClosedResidue_nonempty_oai (P:Deligne M) (x:Artin M) (hx:x∈P.val.2)
    (I:Set S) (hI:I.Nonempty) (hPI:P.val.1⊆I) (q:ℤ) (hq:0<q)
    (c:S⊕Unit→ℝ) (hc:∀v,0 ≤ c v) (hcSupp:∀v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀v,v∈Sum.inl '' I→0 < c v)
    (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hE:∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
        fusionColorRegion m (Sum.inl '' P.val.1)) q)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→
      sourceMultiplicity M x q v=c v) : Nonempty (SourceResidue M false P q) := by
  by_contra hempty
  apply sourceGroup_isolated_harmonic_layer M I P.val.1 hI hPI P.property.1 x q hq
    c hc hcSupp hcPos hcNull hE hdata
  intro g hg hcap j
  by_contra hn
  have hj:sourceMultiplicity M (g*x) q (.inl (j:S)) ≤ c (.inl (j:S)):=le_of_not_gt hn
  let z:=g*x
  have hz:z∈P.val.2 := by
    rw [sourceCosetRepresentative_spec] at hx ⊢
    change (g*x)*(sourceCosetRepresentative M P)⁻¹∈artinParabolic M P.val.1
    rw [_root_.mul_assoc]
    exact Subgroup.mul_mem _ hg hx
  let T:=P.val.1\{(j:S)}
  have ht:T⊆P.val.1:=Set.sdiff_subset
  let R:=sourceCoset M T (source_spherical_mono M ht P.property.1) z
  have hr:R≤P := by
    rw [←sourceCoset_eq M P z hz]
    exact sourceCoset_le M ht z
  have hrlt:R<P := by
    apply lt_of_le_of_ne hr
    intro he
    have he':T=P.val.1:=congrArg (fun A:Deligne M=>A.val.1) he
    have hmem:(j:S)∈T:=by rw [he'];exact j.property
    exact hmem.2 rfl
  have hrz:z∈R.val.2:=rightCoset_self M T z
  have hvec(k:ℤ)(i:S)(hi:i∉T):sourceCosetVector M R k (.inl i)=sourceMultiplicity M z k (.inl i) := by
    rw [sourceCosetVector_eq M R z hrz k]
    exact sourceHarmonicAt_outside M T z k _ (by
      rintro ⟨a,ha,he⟩;exact hi ((Sum.inl_injective he) ▸ ha))
  apply hempty
  refine ⟨R,hrlt,?_⟩
  intro i hi hnT
  have hei:i=(j:S) := by
    by_contra hne
    exact hnT ⟨hi,hne⟩
  subst i
  refine ⟨?_,?_⟩
  · intro k hk
    rw [hvec k j hnT,sourceMultiplicity_zero_iff]
    intro H L
    exact (classCapOn_iff_level_zero Q _ _ _).mp (hcap H) ((.inl (j:S)),L)
      (mem_closedNeighborhood Q ⟨j,hPI j.property,rfl⟩) k hk
  · change sourceCosetVector M R q (.inl (j:S))≤ sourceCosetVector M P q (.inl (j:S))
    rw [hvec q j hnT,sourceCosetVector_of_null_patch M P x hx I hPI q c hcNull hdata j j.property]
    exact hj

end HarmonicArtin

end OAI
end

theorem solution : type_of% @OAI.HarmonicArtin.sourceClosedResidue_nonempty_oai := @OAI.HarmonicArtin.sourceClosedResidue_nonempty_oai
