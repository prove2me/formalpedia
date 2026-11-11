-- Prove2me | solution 1 for OAI.HarmonicArtin.ParabolicIntersections.pointedCandidate_comparison_parabolic_s236
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T20:19:11.904209+00:00
-- url     : https://prove2.me/submissions/63ab97de-1304-42d6-b96f-14ff460fb324

import Mathlib
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap013
import Theorems.Thm_OAI_HarmonicArtin_ParabolicIntersections_PointedCappedCandidate_probe_euler_s236
import Theorems.Thm_OAI_HarmonicArtin_ParabolicIntersections_pointedProbe_raise_lower_s236

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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_TraceLinear
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomSpaceDuality
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_LinearMatrix
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomStep
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_PathTwo
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

namespace BasedComplex
variable [Fintype I] [Fintype J]

lemma tokenHomDifferential_positive (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n : ℤ) {f : Matrix I J (Q.Zigzag K)} (hf : PositiveMatrix Q f) :
    tokenHomDifferential Q E F n f = 0 := by
  rw [tokenHomDifferential_apply Q E F hE hF,
    matrixTwo_mul_positive Q _ hf, positive_mul_matrixTwo Q hf, smul_zero, sub_zero]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PureHomSpaceHomogeneous
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma pure_homSpace_token (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (h : n + v = k-l+2) {f : Matrix I J (Q.Zigzag K)}
    (hf : f ∈ homSpace Q E F n v) : TokenMatrix Q f := by
  intro i j
  have hh := pure_homSpace_homogeneous Q E F hE hF h hf i j
  exact ⟨hh.1 (by norm_num), hh.2.1 (by norm_num)⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_RestrictLayer
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

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_CoefficientTopDual
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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_CoefficientTopDualRestrict
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomPath
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_MinimalEmbedding
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_ClosedNeighborhood
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_QuotientFinrankKer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

lemma quotient_finrank_le_of_ker_le {K U W:Type*} [Field K]
    [AddCommGroup U] [Module K U] [Module.Finite K U]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (B:Submodule K U) (f:U→ₗ[K]W) (h:LinearMap.ker f≤B) :
    Module.finrank K (U ⧸ B)≤Module.finrank K W := by
  have hq:=B.finrank_quotient_add_finrank
  have hr:=f.finrank_range_add_finrank_ker
  have hk:=Submodule.finrank_mono h
  have hi:=Submodule.finrank_le (LinearMap.range f)
  omega

namespace ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J I' J':Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [Fintype I'] [Fintype J']

omit [DecidableEq A] in
lemma homDimension_le_of_cycle_map
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (E':BasedComplex Q (K:=K) I') (F':BasedComplex Q (K:=K) J') (n v:ℤ)
    (T:homCycles Q E F n v→ₗ[K]homCycles Q E' F' n v)
    (hr:∀ f:homCycles Q E F n v,
      (T f).val∈homBoundaries Q E' F' n v→f.val∈homBoundaries Q E F n v) :
    homDimension Q E F n v≤homDimension Q E' F' n v := by
  let B:Submodule K (homCycles Q E F n v):=
    (homBoundaries Q E F n v).comap (homCycles Q E F n v).subtype
  let B':Submodule K (homCycles Q E' F' n v):=
    (homBoundaries Q E' F' n v).comap (homCycles Q E' F' n v).subtype
  apply quotient_finrank_le_of_ker_le B (B'.mkQ.comp T)
  intro f hf
  exact hr f ((Submodule.Quotient.mk_eq_zero B').mp hf)

omit [Fintype V] [DecidableEq A] in
lemma homSpace_positive_of_vertexLevelBound
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J) (r n v:ℤ)
    (hb:∀i j,(E.placement i).color=(F.placement j).color→
      (F.placement j).level-(E.placement i).level ≤ r) (h:r<n+v)
    {f:Matrix I J (Q.Zigzag K)} (hf:f∈homSpace Q E F n v) : PositiveMatrix Q f := by
  intro i j
  funext α
  by_contra hz
  have hh:=degree_vertex_support Q hf.1 hf.2 i j α hz
  have hb':=hb i j (hh.1.trans hh.2.1.symm)
  dsimp only [GeneratorPlacement.level] at hb'
  omega

omit [Fintype V] [DecidableEq A] in
lemma TokenMatrix.extendLayer
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J) (l k:ℤ)
    {f:Matrix {i // (E.placement i).level=l} {j // (F.placement j).level=k} (Q.Zigzag K)}
    (hf:TokenMatrix Q f) : TokenMatrix Q (extendLayer Q E F l k f) := by
  intro i j
  rw [extendLayer_entry]
  split_ifs
  · exact hf _ _
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩

omit [Fintype V] [DecidableEq A] in
lemma homDifferential_token_zero
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (hE:E.IsMinimal Q) (hF:F.IsMinimal Q) (n:ℤ)
    {f:Matrix I J (Q.Zigzag K)} (hf:TokenMatrix Q f) : homDifferential Q E F n f=0 := by
  change E.differential*f-cochainSign (K:=K) n • (f*F.differential)=0
  rw [← matrixTwo_eq_self Q hf,positive_mul_matrixTwo Q hE,
    matrixTwo_mul_positive Q _ hF,smul_zero,sub_zero]

omit [Fintype V] [DecidableEq A] in
lemma tokenLayer_boundary_of_extended_boundary
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (hE:E.IsMinimal Q) (hF:F.IsMinimal Q) (l k n v:ℤ) (h:n+v=k-l+2)
    (hb:∀i j,(E.placement i).color=(F.placement j).color→
      (F.placement j).level-(E.placement i).level≤k-l)
    {f:Matrix {i // (E.placement i).level=l} {j // (F.placement j).level=k} (Q.Zigzag K)}
    (hf:extendLayer Q E F l k f∈homBoundaries Q E F n v) :
    f∈homBoundaries Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v := by
  obtain ⟨g,hg,he⟩:=hf
  have hp:PositiveMatrix Q g:=homSpace_positive_of_vertexLevelBound Q E F (k-l) (n-1) v
    hb (by omega) hg
  have hd:homDifferential Q E F (n-1) g=linearHomDifferential Q E F (n-1) g := by
    rw [homDifferential_eq_linear_add_token,
      tokenHomDifferential_positive Q E F hE hF _ hp,add_zero]
  rw [hd] at he
  refine ⟨restrictLayer Q E F l k g,restrictLayer_homSpace Q E F hE hF l k (n-1) v hg,?_⟩
  have hh:=congrArg (restrictLayer Q E F l k) he
  change restrictLayer Q E F l k (matrixOne Q E.differential*g-
    cochainSign (K:=K) (n-1) • (g*matrixOne Q F.differential))=_ at hh
  rw [map_sub,map_smul,restrictLayer_matrixOne_mul Q E F hE,
    restrictLayer_mul_matrixOne Q E F hF,restrictLayer_extend] at hh
  exact hh

omit [DecidableEq A] in
theorem tokenLayer_homDimension_le
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (hE:E.IsMinimal Q) (hF:F.IsMinimal Q) (l k n v:ℤ) (h:n+v=k-l+2)
    (hb:∀i j,(E.placement i).color=(F.placement j).color→
      (F.placement j).level-(E.placement i).level≤k-l) :
    homDimension Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v≤homDimension Q E F n v := by
  let T:homCycles Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v→ₗ[K]
      homCycles Q E F n v :=
    (extendLayer Q E F l k).restrict (fun f hf=>
      ⟨extendLayer_homSpace Q E F hE hF l k n v hf.1,
        homDifferential_token_zero Q E F hE hF n
          (TokenMatrix.extendLayer Q E F l k
            (pure_homSpace_token Q _ _ (fun i=>i.property) (fun j=>j.property) h hf.1))⟩)
  apply homDimension_le_of_cycle_map Q _ _ E F n v T
  intro f hf
  exact tokenLayer_boundary_of_extended_boundary Q E F hE hF l k n v h hb hf

end ReversibleQuiver.Zigzag.BasedComplex
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_GeneratorArrayZeroCap
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

omit [Fintype V] [DecidableEq A] in
lemma classGeneratorArray_zero_of_cap (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (hx:ClassCapOn Q x U q) (p:GeneratorPlacement V)
    (hp:p.color∈U) (hd:q<p.level) : classGeneratorArray Q x p=0 := by
  let E:=minimalClassModel Q x
  have hm:E.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  have hzero:IsEmpty {i:E.Index // E.complex.placement i=p}:=⟨by
    rintro ⟨i,hi⟩
    have hc:(E.complex.placement i).color∈U:=by rw [hi]; exact hp
    have h:=hx i hc
    change (E.complex.placement i).level≤q at h
    rw [hi] at h
    omega⟩
  rw [← minimalClassModel_class Q x,classGeneratorArray_of_minimal Q _ hm,generatorArray_apply]
  exact Nat.card_eq_zero.mpr (Or.inl hzero)

variable {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
lemma extremal_socle_forces_top_zero (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (hE:E.IsMinimal Q) (hF:F.IsMinimal Q)
    (l q:ℤ) (hb:∀i j,(E.placement i).color=(F.placement j).color→
      (F.placement j).level-(E.placement i).level≤q-l)
    (hz:∀n v,n+v=q-l+2→homDimension Q E F n v=0)
    (α:V) (c d:ℤ)
    (hs:coefficientSocle Q (E.pureLayer Q hE l) α d≠⊥) :
    coefficientTopDual Q (F.pureLayer Q hF q) α c=⊥ := by
  by_contra ht
  have hp:=pure_top_socle_homDimension_pos Q (F.pureLayer Q hF q) (E.pureLayer Q hE l)
    (fun i=>i.property) (fun i=>i.property) α c d ht hs
  have hd:=homDimension_dual Q (E.pureLayer Q hE l) (F.pureLayer Q hF q)
    (c-d) (q-l-(c-d)+2)
  have hp':0<homDimension Q (E.pureLayer Q hE l) (F.pureLayer Q hF q)
      (c-d) (q-l-(c-d)+2) := by
    rw [hd]
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    congr 1 <;> omega
  have hl:=tokenLayer_homDimension_le Q E F hE hF l q
    (c-d) (q-l-(c-d)+2) (by omega) hb
  rw [hz _ _ (by omega)] at hl
  omega

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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_GeneratorArrayZeroLevel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type} {K:Type*} [Field K] [Fintype V] [Fintype A]
  (Q:ReversibleQuiver V A) [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma classGeneratorArray_zero_of_level (x:FiniteHomotopyClass Q (K:=K))
    (p:GeneratorPlacement V) (h:classLevelArray Q x (p.color,p.level)=0) :
    classGeneratorArray Q x p=0 := by
  rw [classLevelArray_minimal_apply] at h
  rw [← minimalClassModel_class Q x,
    classGeneratorArray_of_minimal Q _ (minimalClassModel_minimal Q x),generatorArray_apply]
  let E:=minimalClassModel Q x
  change Nat.card {i:E.Index // E.complex.placement i=p}=0
  have : IsEmpty {i:E.Index // E.complex.placement i=p}:=⟨by
    rintro ⟨i,hi⟩
    have : Nonempty {j:E.Index // (E.complex.placement j).color=p.color ∧
      (E.complex.placement j).level=p.level}:=⟨⟨i,by rw [hi]; exact ⟨rfl,rfl⟩⟩⟩
    have hp:0<Nat.card {j:E.Index // (E.complex.placement j).color=p.color ∧
      (E.complex.placement j).level=p.level}:=Nat.card_pos
    exact Nat.ne_of_gt hp h⟩
  exact Nat.card_of_isEmpty

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_ComplexPureLayer
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_OffDiagonalVertexZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

lemma offDiagonal_vertex_zero {s t:V} {x:Q.Zigzag K}
    (hl:vertexId Q s*x=x) (hr:x*vertexId Q t=x) (hst:s≠t) : x.vertex=0 := by
  funext v
  by_contra hv
  have h:=coordinates_corner Q hl hr (p:=.inl v) hv
  exact hst (h.1.symm.trans h.2)

lemma offDiagonal_token_zero {s t:V} {x:Q.Zigzag K}
    (hl:vertexId Q s*x=x) (hr:x*vertexId Q t=x) (hst:s≠t) : x.token=0 := by
  funext v
  by_contra hv
  have h:=coordinates_corner Q hl hr (p:=.inr (.inr v)) hv
  exact hst (h.1.symm.trans h.2)

lemma offDiagonal_radical_mul_zero {s t u:V} {x y:Q.Zigzag K}
    (hl:vertexId Q s*x=x) (hr:x*vertexId Q t=x) (hst:s≠t)
    (hy:y.vertex=0) (hyr:y*vertexId Q u=y) (hsu:s≠u) : x*y=0 := by
  have hv:=offDiagonal_vertex_zero Q hl hr hst
  have ht: (x*y).token=0 := offDiagonal_token_zero Q
    (by rw [← mul_assoc,hl]) (by rw [mul_assoc,hyr]) hsu
  apply Zigzag.ext
  · simp only [vertex_mul,hv,MulZeroClass.zero_mul,vertex_zero]
  · ext a
    simp only [arrow_mul,hv,hy,leftScale,rightScale,Pi.add_apply,Pi.zero_apply,
      MulZeroClass.zero_mul,MulZeroClass.mul_zero,add_zero,arrow_zero]
  · exact ht

namespace BasedComplex
variable {I:Type*} [Fintype I]

lemma absentProjective_homDifferential_zero (E:BasedComplex Q (K:=K) I)
    (hE:E.IsMinimal Q) (α:V) (ha:∀i,(E.placement i).color≠α)
    (n v:ℤ) {f:Matrix PUnit.{1} I (Q.Zigzag K)}
    (hf:f∈homSpace Q ((initialProjective Q α : BasedComplex Q (K:=K) PUnit.{1})) E n v) :
    homDifferential Q ((initialProjective Q α : BasedComplex Q (K:=K) PUnit.{1})) E n f=0 := by
  have hm:f*E.differential=0 := by
    apply Matrix.ext
    intro i k
    change (∑j,f i j*E.differential j k)=0
    apply Finset.sum_eq_zero
    intro j _
    exact offDiagonal_radical_mul_zero Q (hf.1.1 i j) (hf.1.2 i j)
      (Ne.symm (ha j)) (hE j k) (E.entries.2 j k) (Ne.symm (ha k))
  change (0:Matrix PUnit.{1} PUnit.{1} (Q.Zigzag K))*f-cochainSign (K:=K) n • (f*E.differential)=0
  rw [hm,Matrix.zero_mul,smul_zero,sub_zero]

lemma absentProjective_homBoundaries_bot (E:BasedComplex Q (K:=K) I)
    (hE:E.IsMinimal Q) (α:V) (ha:∀i,(E.placement i).color≠α) (n v:ℤ) :
    homBoundaries Q ((initialProjective Q α : BasedComplex Q (K:=K) PUnit.{1})) E n v=⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨f,hf,rfl⟩
  exact absentProjective_homDifferential_zero Q E hE α ha (n-1) v hf

variable [Fintype V] [DecidableEq A]

lemma absentProjective_homDimension (E:BasedComplex Q (K:=K) I)
    (hE:E.IsMinimal Q) (α:V) (ha:∀i,(E.placement i).color≠α) (n v:ℤ) :
    homDimension Q ((initialProjective Q α : BasedComplex Q (K:=K) PUnit.{1})) E n v=
      Nat.card (HomPath Q ((initialProjective Q α : BasedComplex Q (K:=K) PUnit.{1})) E n v) := by
  have h:=hom_exact_dimension Q ((initialProjective Q α : BasedComplex Q (K:=K) PUnit.{1})) E n v
  rw [absentProjective_homBoundaries_bot Q E hE α ha,
    absentProjective_homBoundaries_bot Q E hE α ha,finrank_bot,
    add_zero,add_zero,homSpace_finrank] at h
  exact h

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_ProbeVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
variable {V A:Type*} (Q:ReversibleQuiver V A)
attribute [local instance] Classical.decEq Classical.propDecidable

namespace Zigzag.BasedComplex
variable {K I:Type*} [Field K] [Fintype V] [Fintype A] [Fintype I]
local notation "R" => probeQuiver Q

lemma probeHomDimension (E:BasedComplex R (K:=K) I) (hE:E.IsMinimal R)
    (α:V) (b:Bool) (ha:∀i,(E.placement i).color≠.inr (α,b)) (n v:ℤ) :
    homDimension R ((initialProjective R (.inr (α,b)) : BasedComplex R (K:=K) PUnit.{1})) E n v=
      Nat.card (probeCoefficient Q E α n v) := by
  rw [absentProjective_homDimension R E hE _ ha]
  exact Nat.card_congr (probeHomPathEquiv Q E α b ha n v)

end Zigzag.BasedComplex
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomDimensionDual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A:Type} {K:Type*} [Field K] [Fintype V] [Fintype A]
  (Q:ReversibleQuiver V A)
attribute [local instance] Classical.decEq Classical.propDecidable

lemma classHomDimension_dual [DecidableEq V] (x y:FiniteHomotopyClass Q (K:=K)) (n v:ℤ) :
    classHomDimension Q n v x y=classHomDimension Q (-n) (2-v) y x := by
  induction x using Quotient.inductionOn with | _ E =>
    induction y using Quotient.inductionOn with | _ F =>
      exact homDimension_dual Q E.complex F.complex n v

local notation "R" => probeQuiver Q

lemma probeHomDimension_generatorArray {I:Type} [Fintype I]
    (E:BasedComplex R (K:=K) I) (hE:E.IsMinimal R)
    (α:V) (b:Bool) (ha:∀i,(E.placement i).color≠.inr (α,b)) (n v:ℤ) :
    homDimension R ((initialProjective R (.inr (α,b)) : BasedComplex R (K:=K) PUnit.{1})) E n v=
      E.generatorArray R ⟨.inl α,n,v-1⟩ := by
  rw [probeHomDimension Q E hE α b ha,generatorArray_apply]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun i => by
    cases E.placement i
    simp only [GeneratorPlacement.mk.injEq]

lemma probeClassHomDimension_generatorArray (x:FiniteHomotopyClass R (K:=K))
    (α:V) (b:Bool)
    (ha:∀i,((minimalClassModel R x).complex.placement i).color≠.inr (α,b)) (n v:ℤ) :
    classHomDimension R n v (initialClass R (.inr (α,b))) x=
      classGeneratorArray R x ⟨.inl α,n,v-1⟩ := by
  rw [← minimalClassModel_class R x, classGeneratorArray_of_minimal R _
    (minimalClassModel_minimal R x)]
  exact probeHomDimension_generatorArray Q _ (minimalClassModel_minimal R x) α b ha n v

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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LayerSocleDimensionSum
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LevelArrayBelow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type} {K:Type*} [Field K] [Fintype V] [Fintype A]
  (Q:ReversibleQuiver V A) [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma classLevelArray_below (x:FiniteHomotopyClass Q (K:=K)) (k l:ℤ)
    (hx:ClassLowerBound Q k x) (hl:l<k) (α:V) : classLevelArray Q x (α,l)=0 := by
  rw [classLevelArray_minimal_apply]
  let :IsEmpty {i:(minimalClassModel Q x).Index //
      ((minimalClassModel Q x).complex.placement i).color=α ∧
      ((minimalClassModel Q x).complex.placement i).level=l}:=⟨by
    rintro ⟨i,hi,he⟩
    have hh:=hx i
    omega⟩
  exact Nat.card_of_isEmpty

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PacketTwistRaisedGenerator2
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ProbeHomDimensionGenerator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type} {K:Type*} [Field K] [Fintype V] [Fintype A]
  (Q:ReversibleQuiver V A) [DecidableEq (ProbeVertex V)]

lemma probeClassHomDimension_generatorArray_flexible
    (x:FiniteHomotopyClass (probeQuiver Q) (K:=K)) (α:V) (b:Bool)
    (ha:∀i,((minimalClassModel (probeQuiver Q) x).complex.placement i).color≠.inr (α,b)) (n v:ℤ) :
    classHomDimension (probeQuiver Q) n v (initialClass (probeQuiver Q) (.inr (α,b))) x=
      classGeneratorArray (probeQuiver Q) x ⟨.inl α,n,v-1⟩ := by
  cases Subsingleton.elim (inferInstance : DecidableEq (ProbeVertex V))
    (@instDecidableEqSum V (V×Bool) (Classical.decEq V)
      (@instDecidableEqProd V Bool (Classical.decEq V) inferInstance))
  exact probeClassHomDimension_generatorArray Q x α b ha n v

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_Path2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A K:Type*} (Q:ReversibleQuiver V A)
local notation "R" => probeQuiver Q

variable [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma path_coordinates (x:Q.Zigzag K) (p:Path V A) :
    pathCoordinates R (zigzagLinear Q x) (path p)=pathCoordinates Q x p := by
  rcases p with v|a|v <;> rfl

lemma path_basis (p:Path V A) : zigzagLinear Q (pathBasis Q (K:=K) p)=pathBasis R (path p) := by
  apply (pathCoordinates R).injective
  funext q
  rcases q with (v|v)|(a|a)|(v|v)
  · change pathCoordinates Q (pathBasis Q p) (.inl v)=_
    rw [pathBasis_coordinates,pathBasis_coordinates]
    exact if_congr (path_injective.eq_iff.symm) rfl rfl
  · rw [pathCoordinates_vertex,zigzag_vertex_leaf,pathBasis_coordinates]
    rcases p with p|p|p <;> simp [path]
  · change pathCoordinates Q (pathBasis Q p) (.inr (.inl a))=_
    rw [pathBasis_coordinates,pathBasis_coordinates]
    exact if_congr (path_injective.eq_iff.symm) rfl rfl
  · rw [pathCoordinates_arrow,zigzag_arrow_leaf,pathBasis_coordinates]
    rcases p with p|p|p <;> simp [path]
  · change pathCoordinates Q (pathBasis Q p) (.inr (.inr v))=_
    rw [pathBasis_coordinates,pathBasis_coordinates]
    exact if_congr (path_injective.eq_iff.symm) rfl rfl
  · rw [pathCoordinates_token,zigzag_token_leaf,pathBasis_coordinates]
    rcases p with p|p|p <;> simp [path]

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_TestIndex2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
  {I J:Type*}
local notation "R" => probeQuiver Q

lemma test_matrix (p:I → GeneratorPlacement V) (q:J → GeneratorPlacement V) (α:V)
    (M:Matrix I J (Q.Zigzag K)) (i:TestIndex Q p α) (j:TestIndex Q q α) :
    testMatrix R (placement ∘ p) (placement ∘ q) (Sum.inl α) (matrix Q M)
      (testIndex Q p α i) (testIndex Q q α j) = testMatrix Q p q α M i j := by
  change pathCoordinates R (pathBasis R (path i.2.val) * zigzagLinear Q (M i.1 j.1))
    (path j.2.val) = _
  rw [← path_basis Q,← zigzagLinear_mul Q,path_coordinates Q]
  rfl

lemma test_transform (p:I → GeneratorPlacement V) (q:J → GeneratorPlacement V) (α:V)
    (M:Matrix I J (Q.Zigzag K)) (i:TestIndex Q p α) (j:TestIndex Q q α) :
    testTransform R (placement ∘ p) (placement ∘ q) (Sum.inl α) (matrix Q M)
      (testIndex Q p α i) (testIndex Q q α j) =
      zigzagLinear Q (testTransform Q p q α M i j) := by
  unfold testTransform scalarCornerMatrix
  rw [test_matrix Q,← zigzag_vertexId Q,map_smul]

lemma evaluation_matrix (p:I → GeneratorPlacement V) (α:V)
    (i:TestIndex Q p α) (j:I) :
    evaluationMatrix R (placement ∘ p) (Sum.inl α) (K := K) (testIndex Q p α i) j =
      zigzagLinear Q (evaluationMatrix Q p α i j) := by
  classical
  change (if i.1=j then pathBasis R (path i.2.val) else 0) = _
  unfold evaluationMatrix
  split_ifs
  · exact (path_basis Q i.2.val).symm
  · exact (map_zero (zigzagLinear Q)).symm

variable [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma positiveTwist_transport (E:BasedComplex Q (K := K) I) (α:V) :
    ((complex Q E).positiveTwist R (Sum.inl α)).reindex R
      ((testIndex Q E.placement α).sumCongr (Equiv.refl I)) =
      complex Q (E.positiveTwist Q α) := by
  apply ext_placement_differential R
  · funext i
    rcases i with i|i
    · change GeneratorPlacement.mk _ _ (_ + Path.length (path i.2.val)) = _
      rw [path_length]
      rfl
    · rfl
  · apply Matrix.ext
    intro i j
    rcases i with i|i <;> rcases j with j|j
    · change -(testTransform R (placement ∘ E.placement) (placement ∘ E.placement)
          (Sum.inl α) (matrix Q E.differential) (testIndex Q E.placement α i)
          (testIndex Q E.placement α j)) = zigzagLinear Q (-testTransform Q _ _ _ _ i j)
      rw [test_transform Q,map_neg]
    · exact evaluation_matrix Q E.placement α i j
    · exact (map_zero (zigzagLinear Q)).symm
    · rfl

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_ProbeEmbeddingMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
local notation "R" => probeQuiver Q

lemma classMap_positiveTwist (α:V) (x:FiniteHomotopyClass Q (K:=K)) :
    classMap Q (classPositiveTwist Q α x)=classPositiveTwist R (.inl α) (classMap Q x) := by
  induction x using Quotient.inductionOn with | _ E =>
    change classOfComplex R (complex Q (E.complex.positiveTwist Q α))=
      classOfComplex R ((complex Q E.complex).positiveTwist R (.inl α))
    rw [← positiveTwist_transport]
    exact (classOfComplex_reindex R _ _).symm

omit [Fintype V] [DecidableEq V] [DecidableEq (ProbeVertex V)] in
lemma placement_injective : Function.Injective (placement (V:=V)) := by
  intro p q h
  cases p with | mk v n t => cases q with | mk w m u =>
    simpa only [placement,GeneratorPlacement.mk.injEq,Sum.inl.injEq] using h

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma generatorArray_core {I:Type u} [Fintype I] (E:BasedComplex Q (K:=K) I)
    (p:GeneratorPlacement V) :
    (complex Q E).generatorArray R (placement p)=E.generatorArray Q p := by
  classical
  simp only [generatorArray,Finsupp.finsetSum_apply,Finsupp.single_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (if placement (E.placement i)=placement p then 1 else 0)=_
  simp only [placement_injective.eq_iff]

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma levelArray_leaf {I:Type u} [Fintype I] (E:BasedComplex Q (K:=K) I) (v:V) (b:Bool) (d:ℤ) :
    (complex Q E).levelArray R (.inr (v,b),d)=0 := by
  classical
  simp only [levelArray_eq_sum,Finsupp.finsetSum_apply,Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro i _
  change (if ((.inl (E.placement i).color:ProbeVertex V),(E.placement i).level)=(.inr (v,b),d) then 1 else 0)=0
  simp

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma classGeneratorArray_core (x:FiniteHomotopyClass Q (K:=K)) (p:GeneratorPlacement V) :
    classGeneratorArray R (classMap Q x) (placement p)=classGeneratorArray Q x p := by
  let E:=minimalClassModel Q x
  have hE:E.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  rw [← minimalClassModel_class Q x]
  change classGeneratorArray R (classOfComplex R (complex Q E.complex)) _=_
  erw [classGeneratorArray_of_minimal R (FiniteModel.ofComplex R _) (complex_minimal Q hE),
    classGeneratorArray_of_minimal Q E hE]
  exact generatorArray_core Q E.complex p

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma classLevelArray_leaf (x:FiniteHomotopyClass Q (K:=K)) (v:V) (b:Bool) (d:ℤ) :
    classLevelArray R (classMap Q x) (.inr (v,b),d)=0 := by
  let E:=minimalClassModel Q x
  have hE:E.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  rw [← minimalClassModel_class Q x]
  change classLevelArray R (classOfComplex R (complex Q E.complex)) _=0
  erw [classLevelArray_of_minimal R (FiniteModel.ofComplex R _) (complex_minimal Q hE)]
  exact levelArray_leaf Q E.complex v b d

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_SignedPerm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A]
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q

lemma classMap_absent (x:FiniteHomotopyClass Q (K:=K)) (α:V) (b:Bool) :
    ∀i,((minimalClassModel R (classMap Q x)).complex.placement i).color≠.inr (α,b) := by
  intro i hi
  let E:=minimalClassModel R (classMap Q x)
  let d:ℤ:=(E.complex.placement i).level
  have hz:=classLevelArray_leaf Q x α b d
  rw [← minimalClassModel_class R (classMap Q x),
    classLevelArray_of_minimal R _ (minimalClassModel_minimal R _),levelArray_apply] at hz
  have hh:Nonempty {j:E.Index // (E.complex.placement j).color=.inr (α,b) ∧
      (E.complex.placement j).level=d}:=⟨⟨i,hi,rfl⟩⟩
  have hp:0<Nat.card {j:E.Index // (E.complex.placement j).color=.inr (α,b) ∧
      (E.complex.placement j).level=d}:=Nat.card_pos
  change Nat.card {j:E.Index // (E.complex.placement j).color=.inr (α,b) ∧
      (E.complex.placement j).level=d}=0 at hz
  omega

lemma classHom_dimension (x:FiniteHomotopyClass Q (K:=K)) (α:V) (b:Bool) (n v:ℤ) :
    classHomDimension R n v (initialClass R (.inr (α,b))) (classMap Q x)=
      classGeneratorArray Q x ⟨α,n,v-1⟩ := by
  rw [probeClassHomDimension_generatorArray Q _ α b (classMap_absent Q x α b)]
  exact classGeneratorArray_core Q x ⟨α,n,v-1⟩

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_HomDimensionFlexible
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A]
  [DecidableEq V] [DecidableEq A] [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q
variable (hn:∀a,Q.source a≠Q.target a)

lemma classHom_dimension_flexible (x:FiniteHomotopyClass Q (K:=K))
    (α:V) (b:Bool) (n v:ℤ) :
    classHomDimension R n v (initialClass R (.inr (α,b))) (classMap Q x)=
      classGeneratorArray Q x ⟨α,n,v-1⟩ := by
  cases Subsingleton.elim (inferInstance : DecidableEq V) (Classical.decEq V)
  cases Subsingleton.elim (inferInstance : DecidableEq A) (Classical.decEq A)
  cases Subsingleton.elim (inferInstance : DecidableEq (ProbeVertex V))
    (@instDecidableEqSum V (V×Bool) (Classical.decEq V)
      (@instDecidableEqProd V Bool (Classical.decEq V) inferInstance))
  cases Subsingleton.elim (inferInstance : DecidableEq (ProbeArrow V A))
    (@instDecidableEqSum A (V×Bool×Bool) (Classical.decEq A)
      (@instDecidableEqProd V (Bool×Bool) (Classical.decEq V) inferInstance))
  exact classHom_dimension Q x α b n v

lemma classMap_twistProd (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :
    classMap Q (((w.map (classTwistPerm Q hn)).prod) x)=
      ((w.map (fun v=>classTwistPerm R (probeQuiver_no_loops Q hn) (.inl v))).prod)
        (classMap Q x) := by
  induction w generalizing x with
  | nil=>rfl
  | cons a w ih=>
    simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
    change classMap Q (classPositiveTwist Q a _) = _
    rw [classMap_positiveTwist,ih]
    rfl

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_HomDualSupportedCycles
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_LayerIndexEquiv
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_TermwiseSplitInjection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
local notation "R" => probeQuiver Q

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] [DecidableEq I] in
lemma coefficientTopDual_complex (E:BasedComplex Q (K:=K) I) (α:V) (c:ℤ) :
    coefficientTopDual R (complex Q E) (.inl α) c=coefficientTopDual Q E α c := by
  ext x
  constructor
  · rintro ⟨hs,hz⟩
    refine ⟨?_,?_⟩
    · intro i hi
      apply hs i
      simpa [complex,placement] using hi
    · intro i a
      exact hz i (.inl a)
  · rintro ⟨hs,hz⟩
    refine ⟨?_,?_⟩
    · intro i hi
      apply hs i
      simpa [complex,placement] using hi
    · intro i a
      cases a with
      | inl a=>exact hz i a
      | inr a=>simp only [complex,matrix,Matrix.map_apply,zigzag_arrow_leaf,MulZeroClass.zero_mul,Finset.sum_const_zero]

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] [DecidableEq I] in
lemma pureLayer_complex (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (q:ℤ) :
    (complex Q E).pureLayer R (complex_minimal Q hE) q=complex Q (E.pureLayer Q hE q) := by
  apply ext_placement_differential R <;> rfl

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_TopZeroProbeSocle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
local notation "R" => probeQuiver Q

omit [DecidableEq A] in
lemma top_zero_of_probe_socle (y:FiniteHomotopyClass R (K:=K))
    (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (l q:ℤ)
    (hy:ClassLowerBound R l y) (hx:ClassCapOn Q x U q)
    (hsupport:∀i α,((minimalClassModel R y).complex.placement i).color=.inl α→α∈U)
    (hz:∀n v,n+v=q-l+2→classHomDimension R n v y (classMap Q x)=0)
    (α:V) (d:ℤ) (hs:0 < classLayerSocleDimension R l (.inl α) d y) :
    ∀c,classLayerTopDimension Q q α c x=0 := by
  let E:=minimalClassModel R y
  let F:=minimalClassModel Q x
  have hE:E.complex.IsMinimal R:=minimalClassModel_minimal R y
  have hF:F.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  have hs':coefficientSocle R (E.complex.pureLayer R hE l) (.inl α) d≠⊥ := by
    intro h
    change 0<Module.finrank K (coefficientSocle R (E.complex.pureLayer R hE l) (.inl α) d) at hs
    rw [h,finrank_bot] at hs
    omega
  have hb:∀i j,(E.complex.placement i).color=((complex Q F.complex).placement j).color→
      ((complex Q F.complex).placement j).level-(E.complex.placement i).level≤q-l := by
    intro i j he
    have hc:=hsupport i (F.complex.placement j).color he
    have hi:=hy i
    have hj:=hx j hc
    change l≤(E.complex.placement i).level at hi
    change (F.complex.placement j).level≤q at hj
    change (F.complex.placement j).level-(E.complex.placement i).level≤q-l
    omega
  have hhom:∀n v,n+v=q-l+2→homDimension R E.complex (complex Q F.complex) n v=0 := by
    intro n v hnv
    have he:classOfComplex R E.complex=y:=minimalClassModel_class R y
    have hf:classOfComplex R (complex Q F.complex)=classMap Q x:=by
      rw [← classMap_complex]
      exact congrArg (classMap Q) (minimalClassModel_class Q x)
    change classHomDimension R n v (classOfComplex R _) (classOfComplex R _)=0
    erw [he,hf]
    exact hz n v hnv
  intro c
  have ht:=extremal_socle_forces_top_zero R E.complex (complex Q F.complex)
    hE (complex_minimal Q hF) l q hb hhom (.inl α) c d hs'
  erw [pureLayer_complex Q F.complex hF q,coefficientTopDual_complex] at ht
  change Module.finrank K (coefficientTopDual Q (F.complex.pureLayer Q hF q) α c)=0
  erw [ht,finrank_bot]

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_WordOrbitSocleAdjacency
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CosetVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
variable {S : Type u}

open _root_.Matrix

theorem harmonic_two_point_equality {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hC : C.PosDef)
    (p p' a a' : ι → ℝ)
    (hrow : a' - a = -(C *ᵥ (p' - p)))
    (hforward : 0 ≤ a' ⬝ᵥ (p' - p))
    (hreverse : 0 ≤ a ⬝ᵥ (p - p')) : p = p' ∧ a = a' := by
  have hneg : p - p' = -(p' - p) := by abel
  have hbound : 0 ≤ (a' - a) ⬝ᵥ (p' - p) := by
    rw [hneg, dotProduct_neg] at hreverse
    rw [sub_dotProduct]
    linarith
  rw [hrow, neg_dotProduct, dotProduct_comm] at hbound
  have hdelta : p' - p = 0 := by
    by_contra h
    have hp := hC.dotProduct_mulVec_pos h
    simp only [star_trivial] at hp
    linarith
  have heq : p = p' := (sub_eq_zero.mp hdelta).symm
  refine ⟨heq, ?_⟩
  rw [hdelta, Matrix.mulVec_zero, neg_zero] at hrow
  exact (sub_eq_zero.mp hrow).symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_StringAdjacent
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionPacketOrbit
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_RootExtension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
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

omit [DecidableEq I] in
lemma rootExtension_mulVec (C:Matrix V V ℝ) (f:I→V) (x:I→ℝ) (i:I) :
    (C *ᵥ rootExtension f x) (f i)=(C.submatrix f f *ᵥ x) i := by
  unfold rootExtension
  rw [Matrix.mulVec_sum]
  simp only [Finset.sum_apply,Matrix.mulVec_smul,Pi.smul_apply,Matrix.mulVec_single,
    Matrix.col,Matrix.transpose_apply,Matrix.mulVec,dotProduct,
    Matrix.submatrix_apply,smul_eq_mul]
  simp [MulOpposite.op_one,one_smul,mul_comm]

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

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PlacementLevelFiberSum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable

lemma placementLevel_fiber_sum {V:Type*} (f:GeneratorPlacement V→₀ℕ) (α:V) (d:ℤ) :
    f.mapDomain (fun p=>(p.color,p.level)) (α,d)=
      ∑ p ∈ f.support.filter (fun p=>p.color=α ∧ p.level=d), f p := by
  have h:=Finsupp.mapDomain_apply_eq_sum (fun p:GeneratorPlacement V=>(p.color,p.level)) f
    (a:=⟨α,d,0⟩)
  simp only [GeneratorPlacement.level,add_zero] at h
  apply h.trans
  apply Finset.sum_congr
  · ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hs,he⟩
      exact Finset.mem_filter.mpr ⟨hs,congrArg Prod.fst he,congrArg Prod.snd he⟩
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hs,hc,hd⟩
      exact Finset.mem_filter.mpr ⟨hs,Prod.ext hc hd⟩
  · intro p hp
    rfl

lemma placementLevel_dual {V:Type*} (f g:GeneratorPlacement V→₀ℕ) (α β:V)
    (he:∀ n u,f ⟨α,n,u⟩=g ⟨β,-n,-u⟩) (d:ℤ) :
    f.mapDomain (fun p=>(p.color,p.level)) (α,d)=
      g.mapDomain (fun p=>(p.color,p.level)) (β,-d) := by
  rw [placementLevel_fiber_sum,placementLevel_fiber_sum]
  refine Finset.sum_bij (fun p _ => ⟨β,-p.cochain,-p.internal⟩) ?_ ?_ ?_ ?_
  · rintro ⟨v,n,u⟩ hp
    rcases Finset.mem_filter.mp hp with ⟨hs,hc,hd⟩
    dsimp only at hc
    subst v
    refine Finset.mem_filter.mpr ⟨?_,rfl,?_⟩
    · rw [Finsupp.mem_support_iff,← he]
      exact Finsupp.mem_support_iff.mp hs
    · change -n + -u = -d
      change n+u=d at hd
      omega
  · rintro ⟨v,n,u⟩ hp ⟨w,m,t⟩ hq hh
    rcases (Finset.mem_filter.mp hp).2 with ⟨hc,hd⟩
    rcases (Finset.mem_filter.mp hq).2 with ⟨kc,kd⟩
    dsimp only at hc kc
    have hn:=congrArg GeneratorPlacement.cochain hh
    have hu:=congrArg GeneratorPlacement.internal hh
    dsimp only at hn hu
    have hm:n=m:=by omega
    have ht:u=t:=by omega
    subst v; subst w; subst m; subst t
    rfl
  · rintro ⟨v,n,u⟩ hp
    rcases Finset.mem_filter.mp hp with ⟨hs,hc,hd⟩
    dsimp only at hc
    subst v
    refine ⟨⟨α,-n,-u⟩,Finset.mem_filter.mpr ⟨?_,rfl,?_⟩,?_⟩
    · rw [Finsupp.mem_support_iff,he,neg_neg,neg_neg]
      exact Finsupp.mem_support_iff.mp hs
    · change -n + -u=d
      change n+u= -d at hd
      omega
    · simp only [neg_neg]
  · rintro ⟨v,n,u⟩ hp
    have hc: v=α := (Finset.mem_filter.mp hp).2.1
    subst v
    exact he n u

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_MapPacket
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open ReversibleQuiver.ProbeEmbedding

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "aw" => sourceArtinAction M (K:=K)
local notation "bw" => sourceProbeAction M (K:=K)

lemma classMap_sourcePacket (s:S) (x:FiniteHomotopyClass Q (K:=K)) :
    classMap Q (aw (generator M s) x)=sourceProbePacket M s (classMap Q x) := by
  have h:=classMap_twistProd Q hn (K:=K) (fusionExpandedWord m [Sum.inl s]) x
  erw [fusionExpandedWord_perm m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)] at h
  simpa only [sourceArtinAction_generator,List.map_cons,List.map_nil,
    fusionWordPacketPerm,fusionSignedPacketPerm,ite_true, if_true,sourceProbePacket,_root_.mul_one] using h

lemma classMap_sourceArtinAction (g:Artin M) (x:FiniteHomotopyClass Q (K:=K)) :
    classMap Q (aw g x)=bw g (classMap Q x) := by
  let H:Subgroup (Artin M):=
    { carrier:={g|∀x,classMap Q (aw g x)=bw g (classMap Q x)}
      one_mem':=by intro x; simp
      mul_mem':=by
        intro a b ha hb x
        simp only [map_mul,Equiv.Perm.mul_apply]
        exact (ha (aw b x)).trans (congrArg (bw a) (hb x))
      inv_mem':=by
        intro a ha x
        apply (bw a).injective
        have h:=ha (aw a⁻¹ x)
        simpa only [map_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using h.symm }
  have hg:g∈H:=PresentedGroup.generated_by (braidRelators M) H (by
    intro s
    change ∀x,classMap Q (aw (generator M s) x)=bw (generator M s) (classMap Q x)
    intro x
    rw [sourceProbeAction_generator]
    exact classMap_sourcePacket M s x) g
  exact hg x

lemma sourceProbeAction_hom_reading (g:Artin M) (x:FiniteHomotopyClass Q (K:=K))
    (α:(S⊕Unit)×FusionLabel m) (b:Bool) (n v:ℤ) :
    classHomDimension R n v (bw g⁻¹ (initialClass R (.inr (α,b)))) (classMap Q x)=
      classGeneratorArray Q (aw g x) ⟨α,n,v-1⟩ := by
  have hd : classHomDimension R n v (initialClass R (.inr (α,b)))
      (classMap Q (aw g x))=classGeneratorArray Q (aw g x) ⟨α,n,v-1⟩ :=
    classHom_dimension_flexible Q (aw g x) α b n v
  rw [← hd,classMap_sourceArtinAction]
  simpa only [map_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using
    (sourceProbeAction_homDimension M g
      (bw g⁻¹ (initialClass R (.inr (α,b)))) (classMap Q x) n v).symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ProbePacketExterior
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open ReversibleQuiver.ProbeEmbedding

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=K)

lemma sourceProbeOrbit_support (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (α:FusionVertex (V:=S⊕Unit) m) (b:Bool) :
    ∀i β,((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.placement i).color=.inl β→
      β∈Set.range (unfoldedInclusion M J) := by
  let y:=bw g (initialClass R (.inr (α,b)))
  let E:=minimalClassModel R y
  intro i β hi
  by_contra hout
  have hp:0 < classGeneratorArray R y (E.complex.placement i) := by
    rw [← minimalClassModel_class R y,classGeneratorArray_of_minimal R _ (minimalClassModel_minimal R y),
      generatorArray_apply]
    change 0<Nat.card {j:E.Index // E.complex.placement j=E.complex.placement i}
    have :Nonempty {j:E.Index // E.complex.placement j=E.complex.placement i}:=⟨⟨i,rfl⟩⟩
    exact Nat.card_pos
  have hz:=sourceProbeAction_exterior M (K:=K) J g hg (initialClass R (.inr (α,b))) (E.complex.placement i)
    (by
      intro s hs L he
      apply hout
      exact ⟨(⟨s,hs⟩,L),Sum.inl.inj (he.trans hi)⟩)
  rw [sourceProbeInitial_array] at hz
  have hne:E.complex.placement i≠⟨.inr (α,b),0,0⟩:=by
    intro he
    have hh:=congrArg GeneratorPlacement.color he
    rw [hi] at hh
    exact Sum.inl_ne_inr hh
  rw [ite_eq_right hne] at hz
  change 0 < classGeneratorArray R (bw g (initialClass R (.inr (α,b)))) _ at hp
  omega

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ProbeActionLevelExterior
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open ReversibleQuiver.ProbeEmbedding _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=K)

lemma sourceProbeAction_level_exterior (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (x:FiniteHomotopyClass R (K:=K)) (α:ProbeVertex (FusionVertex (V:=S⊕Unit) m))
    (hp:∀s∈J,∀L,Sum.inl (Sum.inl s,L)≠α) (l:ℤ) :
    classLevelArray R (bw g x) (α,l)=classLevelArray R x (α,l) := by
  apply finsupp_mapDomain_fiber
  intro p he
  apply sourceProbeAction_exterior M J g hg
  intro s hs L hh
  apply hp s hs L
  exact hh.trans (congrArg Prod.fst he)

lemma sourceProbeOrbit_core_vector_off (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (α β:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ)
    (hb:β∉Set.range (unfoldedInclusion M J)) :
    generatorVector R
      ((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.pureLayer R
        (minimalClassModel_minimal R _) l) (.inl β)=0 := by
  rw [generatorVector_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply ite_eq_right
  intro he
  exact hb (sourceProbeOrbit_support M J g hg α b i.val β he)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FrameFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma artinParabolic_univ : artinParabolic M Set.univ=⊤ := by
  change Subgroup.closure ((generator M) '' Set.univ)=⊤
  rw [Set.image_univ]
  exact PresentedGroup.closure_range_of (braidRelators M)

omit [Fintype S] [LinearOrder S] in
lemma sourceSignedWord_surjective : Function.Surjective (sourceSignedWord M) := by
  intro x
  have hx:x∈artinParabolic M Set.univ := by rw [artinParabolic_univ]; trivial
  obtain ⟨w,_,hw⟩:=artinParabolic_signed_word M Set.univ x hx
  exact ⟨w,hw⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ProbeCoreTermNonpos
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=K)
local notation "C" => fusionFoldedCartan m d

lemma sourceProbe_core_term_nonpos (T:Set S) (g:Artin M) (hg:g∈artinParabolic M T)
    (α β:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ) (p:S⊕Unit→ℝ)
    (hp:∀s∈T,(C *ᵥ p) (.inl s)≤0) :
    let N:=((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.pureLayer R
      (minimalClassModel_minimal R _) l);
    generatorVector R N (.inl β)*fusionFold m (C *ᵥ p) β≤0 := by
  dsimp only
  by_cases hb:β∈Set.range (unfoldedInclusion M T)
  · obtain ⟨⟨s,L⟩,rfl⟩:=hb
    apply mul_nonpos_of_nonneg_of_nonpos (generatorVector_nonneg R _ _)
    exact mul_nonpos_of_nonneg_of_nonpos (fusionWeight_pos m (fusionLabelSize_ge_two M) L).le
      (hp s s.property)
  · rw [sourceProbeOrbit_core_vector_off M T g hg α β b l hb,MulZeroClass.zero_mul]

lemma sourceProbe_core_dot_nonpos (T:Set S) (g:Artin M) (hg:g∈artinParabolic M T)
    (α:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ) (p:S⊕Unit→ℝ)
    (hp:∀s∈T,(C *ᵥ p) (.inl s)≤0) :
    let N:=((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.pureLayer R
      (minimalClassModel_minimal R _) l);
    (fun β=>generatorVector R N (.inl β)) ⬝ᵥ fusionFold m (C *ᵥ p)≤0 := by
  apply Finset.sum_nonpos
  intro β _
  exact sourceProbe_core_term_nonpos M T g hg α β b l p hp

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionProfilePositiveEvery
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ProbePositiveWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "hnR" => probeQuiver_no_loops Q hn

lemma probePositiveWord_lowerBound (J:Set S) (w:List J) (x:FiniteHomotopyClass R (K:=K))
    (q:ℤ) (hx:ClassLowerBound R q x) :
    ClassLowerBound R q (probePositiveWord M J w x) := by
  rw [probePositiveWord_expanded]
  exact positiveWord_lower_bound R _ x hx

lemma probePositiveWord_reduced_eq (J:Set S) (u v:List J)
    (hu:(restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (hv:(restrictedMatrix M J).toCoxeterSystem.IsReduced v)
    (he:(restrictedMatrix M J).toCoxeterSystem.wordProd u=
      (restrictedMatrix M J).toCoxeterSystem.wordProd v)
    (x:FiniteHomotopyClass R (K:=K)) : probePositiveWord M J u x=probePositiveWord M J v x := by
  let f:J→Equiv.Perm (FiniteHomotopyClass R (K:=K)):=fun j=>sourceProbePacket M j
  have hb:∀ i j:J,((altList i j (restrictedMatrix M J i j)).map f).prod=
      ((altList j i (restrictedMatrix M J i j)).map f).prod := by
    intro i j
    have hh:=sourceProbePacket_braid M (K:=K) i j
    simpa only [← altList_map,List.map_map,Function.comp_def,restrictedMatrix_apply,f] using hh
  have hh:=reduced_word_property (restrictedMatrix M J).toCoxeterSystem f hb u v hu hv he
  have hperm:sourceProbeAction M (K:=K) (wordArtin M (u.map Subtype.val))=
      sourceProbeAction M (K:=K) (wordArtin M (v.map Subtype.val)) := by
    simpa only [wordArtin,map_list_prod,List.map_map,sourceProbeAction_generator,Function.comp_def,f] using hh
  exact congrArg (fun p=>p x) hperm

lemma probeBottomWord_cons_socle_zero (J:Set S) (q:ℤ) (x:FiniteHomotopyClass R (K:=K))
    (hx:ClassLowerBound R q x) (j:J) (w:List J) (L:FusionLabel m) (c:ℤ) :
    classLayerSocleDimension R q (.inl (.inl j,L)) c (probeBottomWord M J q (j::w) x)=0 := by
  rw [probeBottomWord,classLayerSocleDimension_layer,probePositiveWord_cons,sourceProbePacket_as_packet]
  exact classPacketPerm_bottom_socle_zero R hnR
    (fun L:FusionLabel m=>Sum.inl (Sum.inl (j:S),L))
    (fun a b hab=>probe_orthogonal Q
      (fusionColor_orthogonal m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (.inl j) hab))
    (probePositiveWord M J w x) (probePositiveWord_lowerBound M J w x q hx) L c

theorem probeBottomWord_socle_ascent (J:Set S) (q:ℤ) (x:FiniteHomotopyClass R (K:=K))
    (hx:ClassLowerBound R q x) (w:List J)
    (hw:(restrictedMatrix M J).toCoxeterSystem.IsReduced w) (j:J)
    (hs:∃ L c,0 < classLayerSocleDimension R q (.inl (.inl j,L)) c (probeBottomWord M J q w x)) :
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
    have he:=probePositiveWord_reduced_eq M J w (j::v) hw hred hprod.symm x
    obtain ⟨L,c,hsc⟩:=hs
    have hval:probeBottomWord M J q w x=probeBottomWord M J q (j::v) x := congrArg (classLayer R q) he
    rw [hval,probeBottomWord_cons_socle_zero M J q x hx j v L c] at hsc
    exact (Nat.lt_irrefl 0) hsc
  change cs.length (cs.simple j*cs.wordProd w)=w.length+1
  rw [cs.not_isLeftDescent_iff.mp ha,hw.eq]

theorem probe_family_socle_finite_termination {B:Type*}
    (J:Set S) (hJ:IsSpherical M J) (q:ℤ)
    (x:B→FiniteHomotopyClass R (K:=K)) (hx:∀ r,ClassLowerBound R q (x r))
    (P:List J→Prop) (hP:P [])
    (step:∀ w,(restrictedMatrix M J).toCoxeterSystem.IsReduced w→P w→
      ∀ j:J,(∃ r L c,0 < classLayerSocleDimension R q (.inl (.inl j,L)) c
        (probeBottomWord M J q w (x r)))→P (j::w)) :
    ∃ w:List J,(restrictedMatrix M J).toCoxeterSystem.IsReduced w ∧ P w ∧
      ∀ r (j:J) L c,classLayerSocleDimension R q (.inl (.inl j,L)) c
        (probeBottomWord M J q w (x r))=0 := by
  let:Finite (restrictedMatrix M J).Group:=restricted_finite M J hJ
  let:=Fintype.ofFinite (restrictedMatrix M J).Group
  let cs:=(restrictedMatrix M J).toCoxeterSystem
  let B:=Finset.univ.sup cs.length
  let move:List J→J→Prop:=fun w j=>∃ r L c,
    0 < classLayerSocleDimension R q (.inl (.inl j,L)) c (probeBottomWord M J q w (x r))
  have bound (w:List J) (hw:cs.IsReduced w) : w.length≤B := by
    rw [← hw.eq]
    exact Finset.le_sup (f:=cs.length) (Finset.mem_univ _)
  have extend (w:List J) (hw:cs.IsReduced w) (j:J) (hj:move w j) : cs.IsReduced (j::w) := by
    obtain ⟨r,L,c,h⟩:=hj
    exact probeBottomWord_socle_ascent M J q (x r) (hx r) w hw j ⟨L,c,h⟩
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_WordArtinSubtypeMem
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma wordArtin_subtype_mem (J:Set S) (w:List J) :
    wordArtin M (w.map Subtype.val)∈artinParabolic M J :=
  wordArtin_mem_parabolic M J _ (by
    intro s hs
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp hs
    exact j.property)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FoldedSphericalPos
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "C" => fusionFoldedCartan m d

lemma source_folded_spherical_posDef (T:Set S) (hT:IsSpherical M T) :
    ((C).submatrix (sourceRootInclusion T) (sourceRootInclusion T)).PosDef := by
  rw [source_folded_submatrix]
  convert Geometric.spherical_cartan_posDef M T hT using 1
  all_goals try with_reducible_and_instances rfl
  exact Geometric.cartan_restricted M T

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ProbeOrbitAbsent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=K)

lemma sourceProbeOrbit_absent (T:Set S) (g:Artin M) (hg:g∈artinParabolic M T)
    (α β:FusionVertex (V:=S⊕Unit) m) (b c:Bool) (hbc:b≠c) :
    ∀i,((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.placement i).color≠.inr (β,c) := by
  intro i hi
  let x:=bw g (initialClass R (.inr (α,b)))
  let E:=minimalClassModel R x
  have hp:0 < classGeneratorArray R x (E.complex.placement i) := by
    rw [← minimalClassModel_class R x,classGeneratorArray_of_minimal R _ (minimalClassModel_minimal R x)]
    rw [generatorArray_apply]
    change 0<Nat.card {j:E.Index // E.complex.placement j=E.complex.placement i}
    let : Nonempty {j:E.Index // E.complex.placement j=E.complex.placement i}:=⟨⟨i,rfl⟩⟩
    exact Nat.card_pos
  have hz:=sourceProbeAction_exterior M (K:=K) T g hg (initialClass R (.inr (α,b))) (E.complex.placement i)
    (by intro s hs L he; exact Sum.inl_ne_inr (he.trans hi))
  rw [sourceProbeInitial_array] at hz
  have hne:E.complex.placement i≠⟨.inr (α,b),0,0⟩:=by
    intro he
    have hh:=congrArg GeneratorPlacement.color he
    rw [hi] at hh
    exact hbc (congrArg Prod.snd (Sum.inr.inj hh)).symm
  rw [ite_eq_right hne] at hz
  change 0 < classGeneratorArray R (bw g (initialClass R (.inr (α,b)))) _ at hp
  omega

lemma sourceProbe_generator_dual (T:Set S) (g:Artin M) (hg:g∈artinParabolic M T)
    (α β:FusionVertex (V:=S⊕Unit) m) (b:Bool) (n u:ℤ) :
    classGeneratorArray R (bw g (initialClass R (.inr (α,b)))) ⟨.inl β,n,u⟩=
      classGeneratorArray R (bw g⁻¹ (initialClass R (.inr (β,!b)))) ⟨.inl α,-n,-u⟩ := by
  have h₁:=probeClassHomDimension_generatorArray_flexible Q
    (bw g (initialClass R (.inr (α,b)))) β (!b)
    (sourceProbeOrbit_absent M T g hg α β b (!b) (by cases b <;> decide)) n (u+1)
  have h₂:=probeClassHomDimension_generatorArray_flexible Q
    (bw g⁻¹ (initialClass R (.inr (β,!b)))) α b
    (sourceProbeOrbit_absent M T g⁻¹ ((artinParabolic M T).inv_mem hg) β α (!b) b (by cases b <;> decide))
    (-n) (1-u)
  have hu:(u+1)-1=u:=by omega
  have hv:(1-u)-1= -u:=by omega
  rw [hu] at h₁
  rw [hv] at h₂
  rw [←h₁,←h₂,classHomDimension_dual]
  have he:=sourceProbeAction_homDimension M g (initialClass R (.inr (α,b)))
    (bw g⁻¹ (initialClass R (.inr (β,!b)))) (-n) (1-u)
  rw [map_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply] at he
  have ht:2-(u+1)=1-u:=by omega
  simpa only [ht,map_inv,Equiv.Perm.inv_def] using he

lemma sourceProbe_level_dual (T:Set S) (g:Artin M) (hg:g∈artinParabolic M T)
    (α β:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ) :
    classLevelArray R (bw g (initialClass R (.inr (α,b)))) (.inl β,l)=
      classLevelArray R (bw g⁻¹ (initialClass R (.inr (β,!b)))) (.inl α,-l) := by
  exact placementLevel_dual
    (classGeneratorArray R (bw g (initialClass R (.inr (α,b)))))
    (classGeneratorArray R (bw g⁻¹ (initialClass R (.inr (β,!b)))))
    (.inl β) (.inl α) (sourceProbe_generator_dual M T g hg α β b) l

lemma sourceProbe_block_left (J:Set S) (a g:Artin M) (ha:a∈artinParabolic M J)
    (α β:FusionVertex (V:=S⊕Unit) m) (hβ:β∉Set.range (unfoldedInclusion M J)) (b:Bool) (l:ℤ) :
    classLevelArray R (bw (a*g) (initialClass R (.inr (α,b)))) (.inl β,l)=
      classLevelArray R (bw g (initialClass R (.inr (α,b)))) (.inl β,l) := by
  rw [map_mul,Equiv.Perm.mul_apply]
  apply sourceProbeAction_level_exterior M J a ha
  intro s hs L he
  exact hβ ⟨(⟨s,hs⟩,L),Sum.inl.inj he⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ProbeFixedDiagonal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=K)

theorem sourceProbe_fixed_of_diagonal (T:Set S) (g:Artin M) (hg:g∈artinParabolic M T)
    (α:FusionVertex (V:=S⊕Unit) m) (b:Bool)
    (hz:∀l,classLevelArray R (bw g (initialClass R (.inr (α,b)))) (.inl α,l)=0) :
    bw g (initialClass R (.inr (α,b)))=initialClass R (.inr (α,b)) := by
  apply probeClass_fixed_of_no_diagonal Q
  · intro n u
    exact classGeneratorArray_zero_of_level R _ ⟨.inl α,n,u⟩ (hz (n+u))
  · intro n u
    rw [sourceProbeAction_exterior M T g hg _ _ (by intros; exact Sum.inl_ne_inr),
      sourceProbeInitial_array M]
    simp only [GeneratorPlacement.mk.injEq,true_and]
  · rw [sourceProbeAction_homDimension]
    exact initial_homDimension_le_one R
      (probeQuiver_no_loops Q (fusionQuiver_no_loops m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)))
      (.inr (α,b)) 0 0

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedMultiplicity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Layer counts of the pointed categorical family, at every integer level. -/

namespace HarmonicArtin.ParabolicIntersections

open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "diag" => coxeterFusionEdge_diag M

lemma pointedFamily_word (f : S) (w : List (S × Bool)) :
    pointedFamily M f (sourceSignedWord M w) =
      fusionPacketOrbit m d hd diag (sourcePacketWord w) (.inl f) := by
  funext L
  unfold pointedFamily pointedAction
  rw [sourceArtinAction_signedWord]
  rfl

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedWeighted
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted multiplicities for the family based at any original color. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M

lemma pointedFamily_mul (g x : Artin M) (L : FusionLabel m) :
    pointedFamily M f (g*x) L = sourceArtinAction M g (pointedFamily M f x L) := by
  simp only [pointedFamily, pointedAction, map_mul, Equiv.Perm.mul_apply]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedTop
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)

lemma pointedFamily_top_proportional (x:Artin M) (s:S⊕Unit) (q c:ℤ) :
    ∃ a:ℝ,0≤a ∧ ∀ L,(∑ H,fusionWeight m H*
      (classLayerTopDimension Q q (s,L) c (pointedFamily M f x H):ℝ))=a*fusionWeight m L := by
  obtain ⟨w,rfl⟩:=sourceSignedWord_surjective M x
  rw [pointedFamily_word]
  exact fusionPacketOrbit_top_proportional m d (coxeterFusionEdge_symm M)
    (coxeterFusionEdge_diag M) (fusionLabelSize_ge_two M) (sourcePacketWord w) (.inl f) s q c

lemma pointedFamily_top_zero_of_label (x:Artin M) (s:S⊕Unit) (q:ℤ)
    (L₀:FusionLabel m)
    (hz:∀ H c,classLayerTopDimension Q q (s,L₀) c (pointedFamily M f x H)=0) :
    ∀ H L c,classLayerTopDimension Q q (s,L) c (pointedFamily M f x H)=0 := by
  intro H L c
  apply Nat.eq_zero_of_not_pos
  intro hp
  obtain ⟨H',hp'⟩:=fusion_profile_positive_every_label m (fusionLabelSize_ge_two M)
    (fun H L=>classLayerTopDimension Q q (s,L) c (pointedFamily M f x H))
    (pointedFamily_top_proportional M f x s q c) hp L₀
  exact hp'.ne' (hz H' c)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedProbeCap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open ReversibleQuiver.ProbeEmbedding

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=ℂ)

lemma pointedFamily_cap_of_top_zero (T:Set S) (z:Artin M) (q:ℤ)
    (hz:∀H,ClassCapOn Q (pointedFamily M f z H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q)
    (j:S) (hj:j∈T)
    (ht:∀H L c,classLayerTopDimension Q q (.inl j,L) c (pointedFamily M f z H)=0) :
    ∀H,ClassCapOn Q (pointedFamily M f (generator M j*z) H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q := by
  intro H
  rw [pointedFamily_mul,sourceArtinAction_generator]
  exact classPacketPerm_local_cap_of_top_zero Q hn (fun L:FusionLabel m=>(.inl j,L))
    (fusionColor_orthogonal m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (.inl j))
    _ _ (hz H) (fun L=>⟨(⟨j,hj⟩,L),rfl⟩) (ht H)

theorem pointedProbe_socle_cap_move (T J:Set S) (hJT:J⊆T)
    (z h:Artin M) (hh:h∈artinParabolic M T) (q l:ℤ) (hl:l≤0)
    (hz:∀H,ClassCapOn Q (pointedFamily M f z H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q)
    (hzh:∀H,ClassCapOn Q (pointedFamily M f (h*z) H)
      (Set.range (unfoldedInclusion M T)) q)
    (α:FusionVertex (V:=S⊕Unit) m) (ha:α∈Set.range (unfoldedInclusion M T)) (b:Bool)
    (hy:ClassLowerBound R l (bw h⁻¹ (initialClass R (.inr (α,b)))))
    (j:S) (hj:j∈J) (L:FusionLabel m) (c:ℤ)
    (hs:0 < classLayerSocleDimension R l (.inl (.inl j,L)) c
      (bw h⁻¹ (initialClass R (.inr (α,b))))) :
    ∀H,ClassCapOn Q (pointedFamily M f (generator M j*z) H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q := by
  apply pointedFamily_cap_of_top_zero M f T z q hz j (hJT hj)
  apply pointedFamily_top_zero_of_label M f z (.inl j) q L
  intro H
  refine top_zero_of_probe_socle Q _ _ (Set.range (unfoldedInclusion M T)) l q hy
    ?_ ?_ ?_ (.inl j,L) c hs
  · exact ClassCapOn.mono Q (hz H) (fun _ ha=>Or.inl ha)
  · exact sourceProbeOrbit_support M T h⁻¹ ((artinParabolic M T).inv_mem hh) α b
  · intro n v hnv
    rw [sourceProbeAction_hom_reading,← pointedFamily_mul]
    apply classGeneratorArray_zero_of_cap Q _ _ q (hzh H) _ ha
    change q<n+(v-1)
    omega

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedCapSaturation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=ℂ)

theorem pointedProbe_cap_saturation {B:Type*}
    (T J:Set S) (hJT:J⊆T) (hJ:IsSpherical M J)
    (z h:Artin M) (hh:h∈artinParabolic M T) (q l:ℤ) (hl:l≤0)
    (hz:∀H,ClassCapOn Q (pointedFamily M f z H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q)
    (hzh:∀H,ClassCapOn Q (pointedFamily M f (h*z) H)
      (Set.range (unfoldedInclusion M T)) q)
    (α:B→FusionVertex (V:=S⊕Unit) m) (ha:∀r,α r∈Set.range (unfoldedInclusion M T))
    (b:B→Bool)
    (hy:∀r,ClassLowerBound R l (bw h⁻¹ (initialClass R (.inr (α r,b r))))) :
    ∃ a∈artinParabolic M J,
      (∀H,ClassCapOn Q (pointedFamily M f (a*z) H)
        (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q) ∧
      (∀r,ClassLowerBound R l (bw (a*h⁻¹) (initialClass R (.inr (α r,b r))))) ∧
      ∀r (j:J) L c,classLayerSocleDimension R l (.inl (.inl j,L)) c
        (bw (a*h⁻¹) (initialClass R (.inr (α r,b r))))=0 := by
  let x:=fun r=>bw h⁻¹ (initialClass R (.inr (α r,b r)))
  let P:List J→Prop:=fun w=>∀H,ClassCapOn Q
    (pointedFamily M f (wordArtin M (w.map Subtype.val)*z) H)
    (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q
  have hP:P []:=by simpa only [P,List.map_nil,wordArtin,List.prod_nil,_root_.one_mul] using hz
  have he (w:List J) (r:B) : probePositiveWord M J w (x r)=
      bw (h*(wordArtin M (w.map Subtype.val))⁻¹)⁻¹ (initialClass R (.inr (α r,b r))) := by
    simp only [probePositiveWord,x,mul_inv_rev,inv_inv,map_mul,Equiv.Perm.mul_apply]
  have step:∀w,(restrictedMatrix M J).toCoxeterSystem.IsReduced w→P w→
      ∀j:J,(∃r L c,0 < classLayerSocleDimension R l (.inl (.inl j,L)) c
        (probeBottomWord M J l w (x r)))→P (j::w) := by
    intro w _ hp j hs
    obtain ⟨r,L,c,hs⟩:=hs
    rw [probeBottomWord,classLayerSocleDimension_layer,he] at hs
    have hb:=probePositiveWord_lowerBound M J w (x r) l (hy r)
    rw [he] at hb
    have hwT:wordArtin M (w.map Subtype.val)∈artinParabolic M T:=
      artinParabolic_mono M hJT (wordArtin_subtype_mem M J w)
    have hprod:(h*(wordArtin M (w.map Subtype.val))⁻¹)*(wordArtin M (w.map Subtype.val)*z)=h*z:=by
      simp only [_root_.mul_assoc,inv_mul_cancel_left]
    have hm:=pointedProbe_socle_cap_move M f T J hJT
      (wordArtin M (w.map Subtype.val)*z) (h*(wordArtin M (w.map Subtype.val))⁻¹)
      ((artinParabolic M T).mul_mem hh ((artinParabolic M T).inv_mem hwT)) q l hl hp
      (by rw [hprod]; exact hzh) (α r) (ha r) (b r) hb j j.property L c hs
    simpa only [P,List.map_cons,wordArtin,List.prod_cons,_root_.mul_assoc] using hm
  obtain ⟨w,_,hp,hs⟩:=probe_family_socle_finite_termination M J hJ l x hy P hP step
  refine ⟨wordArtin M (w.map Subtype.val),wordArtin_subtype_mem M J w,hp,?_,?_⟩
  · intro r
    have hb:=probePositiveWord_lowerBound M J w (x r) l (hy r)
    simpa only [probePositiveWord,x,map_mul,Equiv.Perm.mul_apply] using hb
  · intro r j L c
    have hh:=hs r j L c
    simpa only [probeBottomWord,classLayerSocleDimension_layer,probePositiveWord,x,map_mul,
      Equiv.Perm.mul_apply] using hh

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedCappedCandidate
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "C" => fusionFoldedCartan m d

namespace PointedCappedCandidate
variable {M} {f:S} {T J:Set S} {z:Artin M} {q:ℤ} {p:S⊕Unit→ℝ}

lemma cartan_nonpos (X:PointedCappedCandidate M f T J z q p) (s:S) (hs:s∈T) :
    (C *ᵥ p) (.inl s)≤0 := by
  by_cases hj:s∈J
  · exact (X.harmonic ⟨s,hj⟩).le
  · exact (X.negative s hs hj).le

lemma move (X:PointedCappedCandidate M f T J z q p) (a:Artin M) (ha:a∈artinParabolic M J)
    (hc:∀H,ClassCapOn Q (pointedFamily M f (a*z) H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q) :
    PointedCappedCandidate M f T J (a*z) q p := by
  refine ⟨X.subset,X.spherical,hc,X.harmonic,?_,X.negative,?_⟩
  · intro v hv
    rw [pointedMultiplicity_exterior_ordered M f J a ha z v hv q]
    exact X.exterior v hv
  · intro b hb hcap j
    have hh:=X.representatives (b*a) ((artinParabolic M J).mul_mem hb ha)
      (by simpa only [_root_.mul_assoc] using hcap) j
    simpa only [_root_.mul_assoc] using hh

end PointedCappedCandidate
end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedProbeRaiseLower
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=ℂ)

theorem pointedProbe_zero_saturation {B:Type*} [Finite B]
    (T J:Set S) (z h:Artin M) (q:ℤ) (p:S⊕Unit→ℝ)
    (X:PointedCappedCandidate M f T J z q p) (hh:h∈artinParabolic M T)
    (hzh:∀H,ClassCapOn Q (pointedFamily M f (h*z) H)
      (Set.range (unfoldedInclusion M T)) q)
    (α:B→FusionVertex (V:=S⊕Unit) m) (ha:∀r,α r∈Set.range (unfoldedInclusion M T))
    (b:B→Bool) :
    ∃ a∈artinParabolic M J,
      (∀H,ClassCapOn Q (pointedFamily M f (a*z) H)
        (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q) ∧
      (∀r,ClassLowerBound R 0 (bw (a*h⁻¹) (initialClass R (.inr (α r,b r))))) ∧
      ∀r (j:J) L c,classLayerSocleDimension R 0 (.inl (.inl j,L)) c
        (bw (a*h⁻¹) (initialClass R (.inr (α r,b r))))=0 := by
  have aux:∀n:ℕ,∀z h:Artin M,PointedCappedCandidate M f T J z q p→
      h∈artinParabolic M T→
      (∀H,ClassCapOn Q (pointedFamily M f (h*z) H) (Set.range (unfoldedInclusion M T)) q)→
      (∀r,ClassLowerBound R (-(n:ℤ)) (bw h⁻¹ (initialClass R (.inr (α r,b r)))))→
      ∃ a∈artinParabolic M J,
        (∀H,ClassCapOn Q (pointedFamily M f (a*z) H)
          (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q) ∧
        (∀r,ClassLowerBound R 0 (bw (a*h⁻¹) (initialClass R (.inr (α r,b r))))) ∧
        ∀r (j:J) L c,classLayerSocleDimension R 0 (.inl (.inl j,L)) c
          (bw (a*h⁻¹) (initialClass R (.inr (α r,b r))))=0 := by
    intro n
    induction n with
    | zero =>
      intro z h X hh hc hy
      apply pointedProbe_cap_saturation M f T J X.subset X.spherical z h hh q 0 (by omega)
        X.cap hc α ha b
      simpa only [Nat.cast_zero,neg_zero] using hy
    | succ n ih =>
      intro z h X hh hc hy
      obtain ⟨a,haJ,hcap,hlower,hsoc⟩:=pointedProbe_cap_saturation M f T J X.subset X.spherical z h hh q
        (-((n+1:ℕ):ℤ)) (by omega) X.cap hc α ha b hy
      have haT:=artinParabolic_mono M X.subset haJ
      have hhT:(h*a⁻¹)∈artinParabolic M T:=
        (artinParabolic M T).mul_mem hh ((artinParabolic M T).inv_mem haT)
      have he:(h*a⁻¹)*(a*z)=h*z:=by simp only [_root_.mul_assoc,inv_mul_cancel_left]
      have hei:(h*a⁻¹)⁻¹=a*h⁻¹:=by simp only [_root_.mul_inv_rev,inv_inv]
      have hraise:∀r,ClassLowerBound R (-(n:ℤ))
          (bw (h*a⁻¹)⁻¹ (initialClass R (.inr (α r,b r)))) := by
        intro r
        have hr:=pointedProbe_raise_lower_s236 M f T J (a*z) (h*a⁻¹) q (-((n+1:ℕ):ℤ)) p (X.move a haJ hcap)
          hhT (by omega) (by rw [he]; exact hc) (α r) (ha r) (b r)
          (by rw [hei]; exact hlower r) (by rw [hei]; exact hsoc r)
        convert hr using 1
        all_goals try with_reducible_and_instances rfl
        omega
      obtain ⟨a',ha',hcap',hlower',hsoc'⟩:=ih (a*z) (h*a⁻¹) (X.move a haJ hcap) hhT
        (by rw [he];exact hc) hraise
      refine ⟨a'*a,(artinParabolic M J).mul_mem ha' haJ,?_,?_,?_⟩
      · simpa only [_root_.mul_assoc] using hcap'
      · simpa only [hei,_root_.mul_assoc] using hlower'
      · simpa only [hei,_root_.mul_assoc] using hsoc'
  obtain ⟨l,hl⟩:=finiteFamily_lowerBound R (fun r=>bw h⁻¹ (initialClass R (.inr (α r,b r))))
  apply aux (-l).toNat z h X hh hzh
  intro r i
  have hh:=hl r i
  have hn:Int.ofNat (-l).toNat≥-l:=Int.self_le_toNat (-l)
  omega

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedCandidateCapped
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)

theorem pointedCandidate_le_capped (T J:Set S) (z h:Artin M) (q:ℤ) (p:S⊕Unit→ℝ)
    (X:PointedCappedCandidate M f T J z q p) (hh:h∈artinParabolic M T)
    (hzh:∀H,ClassCapOn Q (pointedFamily M f (h*z) H)
      (Set.range (unfoldedInclusion M T)) q) (s:S) (hs:s∈T) :
    p (.inl s)≤ pointedMultiplicity M f (h*z) q (.inl s) := by
  let L:=fusionZeroLabel m (fusionLabelSize_ge_two M)
  let α:FusionVertex (V:=S⊕Unit) m:=(.inl s,L)
  obtain ⟨a,ha,hcap,_,hsoc⟩:=pointedProbe_zero_saturation M f T J z h q p X hh hzh
    (fun _:Unit=>α) (fun _=>⟨(⟨s,hs⟩,L),rfl⟩) (fun _=>false)
  have haT:=artinParabolic_mono M X.subset ha
  have hg:(h*a⁻¹)∈artinParabolic M T:=
    (artinParabolic M T).mul_mem hh ((artinParabolic M T).inv_mem haT)
  have hei:(h*a⁻¹)⁻¹=a*h⁻¹:=by simp only [_root_.mul_inv_rev,inv_inv]
  have he:(h*a⁻¹)*(a*z)=h*z:=by simp only [_root_.mul_assoc,inv_mul_cancel_left]
  have hu:=(X.move a ha hcap).probe_euler_s236 (h*a⁻¹) hg α false 0 (by rw [hei];exact hsoc ())
  have hn:=sourceProbe_core_dot_nonpos M (K:=ℂ) T (h*a⁻¹)⁻¹
    ((artinParabolic M T).inv_mem hg) α false 0 p X.cartan_nonpos
  dsimp only at hu hn
  rw [ite_eq_left rfl,sub_zero,he] at hu
  have hw:fusionWeight m α.2*p α.1≤fusionWeight m α.2*pointedMultiplicity M f (h*z) q α.1:=by linarith
  exact (mul_le_mul_iff_right₀ (fusionWeight_pos m (fusionLabelSize_ge_two M) L)).mp hw

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedCandidateNumerical
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "C" => fusionFoldedCartan m d

theorem pointedCandidate_numerical_unique (T J J':Set S) (hT:IsSpherical M T)
    (z h:Artin M) (hh:h∈artinParabolic M T) (q:ℤ) (p p':S⊕Unit→ℝ)
    (X:PointedCappedCandidate M f T J z q p) (Y:PointedCappedCandidate M f T J' (h*z) q p') :
    p=p' ∧ J=J' := by
  have hforward:∀s∈T,s∉J'→p (.inl s)≤p' (.inl s):=by
    intro s hs hj
    have hv:(Sum.inl s:S⊕Unit)∉Sum.inl '' J':=by
      rintro ⟨t,ht,he⟩
      exact hj (Sum.inl.inj he ▸ ht)
    rw [←Y.exterior (.inl s) hv]
    exact pointedCandidate_le_capped M f T J z h q p X hh
      (fun H i hi=>Y.cap H i (Or.inl hi)) s hs
  have hreverse:∀s∈T,s∉J→p' (.inl s)≤p (.inl s):=by
    intro s hs hj
    have hv:(Sum.inl s:S⊕Unit)∉Sum.inl '' J:=by
      rintro ⟨t,ht,he⟩
      exact hj (Sum.inl.inj he ▸ ht)
    have hm:=pointedCandidate_le_capped M f T J' (h*z) h⁻¹ q p' Y ((artinParabolic M T).inv_mem hh)
      (by rw [inv_mul_cancel_left]; exact fun H i hi=>X.cap H i (Or.inl hi)) s hs
    simpa only [inv_mul_cancel_left,X.exterior (.inl s) hv] using hm
  have hext:∀v,v∉Sum.inl '' T→p v=p' v := by
    intro v hv
    have hvJ:v∉Sum.inl '' J:=fun ⟨s,hs,he⟩=>hv ⟨s,X.subset hs,he⟩
    have hvJ':v∉Sum.inl '' J':=fun ⟨s,hs,he⟩=>hv ⟨s,Y.subset hs,he⟩
    rw [←X.exterior v hvJ,←Y.exterior v hvJ',pointedMultiplicity_exterior_ordered M f T h hh z v hv q]
  let f:=sourceRootInclusion T
  let a:T→ℝ:=fun i=>-(C *ᵥ p) (f i)
  let a':T→ℝ:=fun i=>-(C *ᵥ p') (f i)
  have hf:Function.Injective f:=sourceRootInclusion_injective T
  have he:rootExtension f ((p'-p)∘f)=p'-p:=rootExtension_restrict f hf (p'-p) (by
    intro v hv
    apply sub_eq_zero.mpr
    apply (hext v ?_).symm
    rintro ⟨s,hs,rfl⟩
    exact hv ⟨⟨s,hs⟩,rfl⟩)
  have hrow:a'-a=-((C).submatrix f f *ᵥ ((p'∘f)-(p∘f))) := by
    funext i
    have hc:=rootExtension_mulVec C f ((p'-p)∘f) i
    rw [he,mulVec_sub] at hc
    change -(C *ᵥ p') (f i) - -(C *ᵥ p) (f i)= -(_)
    change (C *ᵥ p') (f i)-(C *ᵥ p) (f i)=_ at hc
    have hd:(p'∘f)-(p∘f)=(p'-p)∘f:=rfl
    rw [hd,←hc]
    ring
  have hfor:0≤a' ⬝ᵥ ((p'∘f)-(p∘f)) := by
    apply Finset.sum_nonneg
    intro i hi
    by_cases hj:(i:S)∈J'
    · have hz:=Y.harmonic ⟨i,hj⟩
      change -(C *ᵥ p') (.inl (i:S)) * (p' (.inl (i:S))-p (.inl (i:S)))≥0
      rw [hz,neg_zero,MulZeroClass.zero_mul]
    · exact mul_nonneg (neg_nonneg.mpr (Y.cartan_nonpos i i.property))
        (sub_nonneg.mpr (hforward i i.property hj))
  have hrev:0≤a ⬝ᵥ ((p∘f)-(p'∘f)) := by
    apply Finset.sum_nonneg
    intro i hi
    by_cases hj:(i:S)∈J
    · have hz:=X.harmonic ⟨i,hj⟩
      change -(C *ᵥ p) (.inl (i:S)) * (p (.inl (i:S))-p' (.inl (i:S)))≥0
      rw [hz,neg_zero,MulZeroClass.zero_mul]
    · exact mul_nonneg (neg_nonneg.mpr (X.cartan_nonpos i i.property))
        (sub_nonneg.mpr (hreverse i i.property hj))
  have hp:=harmonic_two_point_equality ((C).submatrix f f) (source_folded_spherical_posDef M T hT)
    (p∘f) (p'∘f) a a' hrow hfor hrev
  have hep:p=p':=by
    funext v
    by_cases hv:v∈Sum.inl '' T
    · obtain ⟨s,hs,rfl⟩:=hv
      exact congrFun hp.1 ⟨s,hs⟩
    · exact hext v hv
  refine ⟨hep,?_⟩
  apply Set.Subset.antisymm
  · intro s hs
    by_contra hj
    have hn:=Y.negative s (X.subset hs) hj
    rw [←hep,X.harmonic ⟨s,hs⟩] at hn
    exact lt_irrefl _ hn
  · intro s hs
    by_contra hj
    have hn:=X.negative s (Y.subset hs) hj
    rw [hep,Y.harmonic ⟨s,hs⟩] at hn
    exact lt_irrefl _ hn

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedCandidateBlock
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=ℂ)
local notation "C" => fusionFoldedCartan m d

lemma pointedCandidate_block_nonpos (T J:Set S) (z h:Artin M)
    (hh:h∈artinParabolic M T) (q:ℤ) (p:S⊕Unit→ℝ)
    (X:PointedCappedCandidate M f T J z q p) (Y:PointedCappedCandidate M f T J (h*z) q p)
    (s t:S) (hs:s∈T) (hsJ:s∉J) (ht:t∈T) (htJ:t∉J)
    (L H:FusionLabel m) (b:Bool) (l:ℤ) (hl:l≤0) :
    classLevelArray R (bw h⁻¹ (initialClass R (.inr ((.inl s,L),b)))) (.inl (.inl t,H),l)=0 := by
  let α:FusionVertex (V:=S⊕Unit) m:=(.inl s,L)
  let β:FusionVertex (V:=S⊕Unit) m:=(.inl t,H)
  obtain ⟨a,ha,hcap,hlower,hsoc⟩:=pointedProbe_zero_saturation M f T J z h q p X hh
    (fun H i hi=>Y.cap H i (Or.inl hi))
    (fun _:Unit=>α) (fun _=>⟨(⟨s,hs⟩,L),rfl⟩) (fun _=>b)
  have haT:=artinParabolic_mono M X.subset ha
  have hg:(h*a⁻¹)∈artinParabolic M T:=
    (artinParabolic M T).mul_mem hh ((artinParabolic M T).inv_mem haT)
  have hei:(h*a⁻¹)⁻¹=a*h⁻¹:=by simp only [_root_.mul_inv_rev,inv_inv]
  have he:(h*a⁻¹)*(a*z)=h*z:=by simp only [_root_.mul_assoc,inv_mul_cancel_left]
  have hβ:β∉Set.range (unfoldedInclusion M J):=by
    rintro ⟨⟨j,_⟩,he⟩
    have hj:(j:S)=t:=Sum.inl.inj (congrArg Prod.fst he)
    exact htJ (hj ▸ j.property)
  rw [←sourceProbe_block_left M J a h⁻¹ ha α β hβ b l]
  rcases lt_or_eq_of_le hl with hl|rfl
  · exact classLevelArray_below R _ 0 l (hlower ()) hl (.inl β)
  · have hu:=(X.move a ha hcap).probe_euler_s236 (h*a⁻¹) hg α b 0 (by rw [hei]; exact hsoc ())
    have hα:(Sum.inl s:S⊕Unit)∉Sum.inl '' J:=by
      rintro ⟨j,hj,he⟩
      exact hsJ (Sum.inl.inj he ▸ hj)
    dsimp only at hu
    rw [ite_eq_left rfl,sub_zero,he,Y.exterior (.inl s) hα,hei] at hu
    by_contra hz
    have hn:0 < classLevelArray R (bw (a*h⁻¹) (initialClass R (.inr (α,b)))) (.inl β,0):=Nat.pos_of_ne_zero hz
    let N:=((minimalClassModel R (bw (a*h⁻¹) (initialClass R (.inr (α,b))))).complex.pureLayer R
      (minimalClassModel_minimal R _) 0)
    have hp:0<generatorVector R N (.inl β):=by
      rw [generatorVector_minimalLayer]
      exact_mod_cast hn
    have hg':a*h⁻¹∈artinParabolic M T:=by rw [←hei];exact (artinParabolic M T).inv_mem hg
    have hterm:generatorVector R N (.inl β)*fusionFold m (C *ᵥ p) β<0:=
      mul_neg_of_pos_of_neg hp (mul_neg_of_pos_of_neg (fusionWeight_pos m (fusionLabelSize_ge_two M) H)
        (X.negative t ht htJ))
    have hdot:(fun γ=>generatorVector R N (.inl γ)) ⬝ᵥ fusionFold m (C *ᵥ p)<0:=by
      apply Finset.sum_neg' (fun γ _=>sourceProbe_core_term_nonpos M (K:=ℂ) T (a*h⁻¹) hg' α γ b 0 p X.cartan_nonpos)
      exact ⟨β,Finset.mem_univ _,hterm⟩
    change _-(fun γ=>generatorVector R N (.inl γ)) ⬝ᵥ fusionFold m (C *ᵥ p)≤_ at hu
    linarith

theorem pointedCandidate_zero_block (T J J':Set S) (hT:IsSpherical M T) (z h:Artin M)
    (hh:h∈artinParabolic M T) (q:ℤ) (p p':S⊕Unit→ℝ)
    (X:PointedCappedCandidate M f T J z q p) (Y:PointedCappedCandidate M f T J' (h*z) q p') :
    p=p' ∧ J=J' ∧ ∀s∈T,s∉J→∀t∈T,t∉J→∀L H b l,
      classLevelArray R (bw h (initialClass R (.inr ((.inl s,L),b)))) (.inl (.inl t,H),l)=0 := by
  obtain ⟨rfl,rfl⟩:=pointedCandidate_numerical_unique M f T J J' hT z h hh q p p' X Y
  refine ⟨rfl,rfl,?_⟩
  intro s hs hsJ t ht htJ L H b l
  by_cases hl:l≤0
  · have hz:=pointedCandidate_block_nonpos M f T J (h*z) h⁻¹ ((artinParabolic M T).inv_mem hh)
      q p Y (by simpa only [inv_mul_cancel_left] using X) s t hs hsJ ht htJ L H b l hl
    simpa only [inv_inv] using hz
  · rw [sourceProbe_level_dual M T h hh (.inl s,L) (.inl t,H) b l]
    exact pointedCandidate_block_nonpos M f T J z h hh q p X Y t s ht htJ hs hsJ H L (!b) (-l) (by omega)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedCandidateFixed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q

theorem pointedCandidate_fixed_probes (T J J':Set S) (hT:IsSpherical M T) (z h:Artin M)
    (hh:h∈artinParabolic M T) (q:ℤ) (p p':S⊕Unit→ℝ)
    (X:PointedCappedCandidate M f T J z q p) (Y:PointedCappedCandidate M f T J' (h*z) q p') :
    p=p' ∧ J=J' ∧ ∀s∈T,s∉J→∀L b,
      sourceProbeAction M (K:=ℂ) h (initialClass R (.inr ((.inl s,L),b)))=
        initialClass R (.inr ((.inl s,L),b)) := by
  obtain ⟨he,hj,hz⟩:=pointedCandidate_zero_block M f T J J' hT z h hh q p p' X Y
  refine ⟨he,hj,?_⟩
  intro s hs hsJ L b
  exact sourceProbe_fixed_of_diagonal M T h hh (.inl s,L) b (hz s hs hsJ s hs hsJ L L b)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedCandidateComparison
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

theorem pointedCandidate_comparison_parabolic_s236_oai (T J J':Set S) (hT:IsSpherical M T)
    (z h:Artin M) (hh:h∈artinParabolic M T) (q:ℤ) (p p':S⊕Unit→ℝ)
    (X:PointedCappedCandidate M f T J z q p) (Y:PointedCappedCandidate M f T J' (h*z) q p') :
    p=p' ∧ J=J' ∧ h∈artinParabolic M J := by
  obtain ⟨hp,hj,hfix⟩:=pointedCandidate_fixed_probes M f T J J' hT z h hh q p p' X Y
  exact ⟨hp,hj,sourceProbe_parabolic_detector M T J hT h hh hfix⟩

end HarmonicArtin.ParabolicIntersections

end OAI
end

theorem solution : type_of% @OAI.HarmonicArtin.ParabolicIntersections.pointedCandidate_comparison_parabolic_s236_oai := @OAI.HarmonicArtin.ParabolicIntersections.pointedCandidate_comparison_parabolic_s236_oai
