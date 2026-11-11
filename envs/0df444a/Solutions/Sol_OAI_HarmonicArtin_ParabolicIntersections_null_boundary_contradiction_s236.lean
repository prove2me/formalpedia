-- Prove2me | solution 1 for OAI.HarmonicArtin.ParabolicIntersections.null_boundary_contradiction_s236
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T20:14:43.089215+00:00
-- url     : https://prove2.me/submissions/e33208f0-8ea7-4387-b220-c1729ec47440

import Mathlib
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap013
import Theorems.Thm_OAI_HarmonicArtin_IsolatedIterationData_stage_move_s236
import Theorems.Thm_OAI_HarmonicArtin_fusionOrbitColor_subobject_separation_s236

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_BottomScalarCycleZero
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_MinimalModelEquivalence
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LayerVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PositiveTwistLowerBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_InverseWordAction
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_DownClosed
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_CochainSignSubOne
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TotalVector
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_CanonicalLowReflectedHigh
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ComplexPacketLowerBound
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HighConeIndex
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_InverseMatrix
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LayerConeEquivalence
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_ClosedNeighborhood
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_NegativeTwistModern
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LayerSocleDimensionLayer
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LevelArrayMinimalApply
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PositiveTwistModern
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TotalVectorLayer
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_UnfoldedCartanSymm
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_StrictChamber
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_ChamberInequalitiesConvexHull
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionVertex
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionQuiverCartan
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CanonicalFusionMultiplicity
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ArtinActionWordArtin
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CanonicalLowSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_RootExtension
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CappedReflectedHigh
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_NegativePrepend
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_RowReflectWordReverse
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest _root_.OAI.HarmonicArtin.unfoldedHom_simple _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightedReflectedHigh
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_RootInclusionRange
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_ConvexWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_InteriorConvexHullReindex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionColorWord
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_BottomWordNil
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_DimensionNonneg
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FamilySocleFiniteTermination
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_IntegerUpward
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_NullPatch
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_IsolatedBoundaryAbsent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
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
  apply fusionOrbitColor_subobject_separation_s236 m d hd hdiag hm z s q k
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnfoldedInclusionRange
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

lemma closedNeighborhood_mono {V A:Type} (R:ReversibleQuiver V A)
    {U T:Set V} (h:U⊆T) : R.closedNeighborhood U⊆R.closedNeighborhood T := by
  rintro α (hα|⟨β,hβ,a,hs,ht⟩)
  · exact Or.inl (h hα)
  · exact Or.inr ⟨β,h hβ,a,hs,ht⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_IsolatedIterationData
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

lemma separation (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
    (k:ℤ) (hs:D.openSocle z k) :
    (∀ v∉Sum.inl '' D.I,(∃ u∈Sum.inl '' D.I,C v u<0)→μ z D.s k v=0) ∧
    (∀ j∈Sum.inl '' D.J,(C *ᵥ μ z D.s k) j=0) ∧
    fusionWeightedHom m d hd (D.fullRegion z hz) (fun H=>Y z D.s H k) (k-D.q)=0 ∧
    fusionWeightedHom m d hd (fun H=>Y z D.s H k) (D.fullRegion z hz) (D.q-k)=0 := by
  apply source_isolated_separation M D.I D.J D.hJI D.hJ z D.s D.q k D.c
    D.hc D.hcSupp D.hcPos D.hcNull (D.data z hz) (D.capJ z hc) (D.strict z hz)
  intro H α hα r
  exact Submodule.finrank_eq_zero.mp (hs H α hα r)

lemma socle_below (z:List ((S⊕Unit)×Bool)) (b k:ℤ)
    (hb:∀ L,ClassLowerBound Q b (O z D.s L)) (hk:k<b) : D.openSocle z k := by
  intro H α hα c
  exact classLayerSocleDimension_below Q (O z D.s H) b k (hb H) hk α c

end IsolatedIterationData
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_Stage
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
    have hm:=D.stage_move_s236 z' hz' hc' j b t ht hb' hp' hs'
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
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_NullBoundary
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The boundary form of the relative null-layer obstruction

The old universal-frame argument used a boundary generator in degree zero
and therefore applied only above zero. In §5 of paper 082-03 the relative
frame can instead be joined to the isolated layer through a boundary
color at any lower integer degree. This is the saturation contradiction
at that degree. Establishing the occupied boundary for a relative family
is a separate support argument, not a published hypothesis.
-/

namespace HarmonicArtin.ParabolicIntersections

open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable

variable {S : Type} [Fintype S] [LinearOrder S] {M : CoxeterMatrix S}

/-- Saturation kills every exterior boundary count below the isolated
layer. Thus a boundary count preserved throughout the permitted orbit
prevents the isolated null-layer configuration, at any integer height. -/
theorem null_boundary_contradiction_s236_oai (D : IsolatedIterationData M)
    (k : ℤ) (hk : k < D.q) (v : S ⊕ Unit)
    (hv : v ∉ Sum.inl '' D.I)
    (hinc : ∃ u ∈ Sum.inl '' D.I,
      fusionFoldedCartan (fusionLabelSize M) (coxeterFusionEdge M) v u < 0)
    (hoccupied : ∀ z, D.valid z →
      0 < fusionOrbitMultiplicity (fusionLabelSize M) (coxeterFusionEdge M)
        (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
        (fun e => le_trans (by norm_num) (fusionLabelSize_ge_four M e)) z D.s k v)
    (z : List ((S ⊕ Unit) × Bool)) (hz : D.valid z) (hc : D.capped z) : False := by
  obtain ⟨b, hb⟩ := finiteFamily_lowerBound
    (fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M))
    (fusionPacketOrbit (fusionLabelSize M) (coxeterFusionEdge M)
      (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) z D.s)
  obtain ⟨z', hz', hc', _, hs⟩ := D.saturate z hz hc b k hk hb
  have hzero := (D.separation z' hz' hc' k hs).1 v hv hinc
  have hpositive := hoccupied z' hz'
  rw [hzero] at hpositive
  exact lt_irrefl 0 hpositive

end HarmonicArtin.ParabolicIntersections

end OAI
end

theorem solution : type_of% @OAI.HarmonicArtin.ParabolicIntersections.null_boundary_contradiction_s236_oai := @OAI.HarmonicArtin.ParabolicIntersections.null_boundary_contradiction_s236_oai
