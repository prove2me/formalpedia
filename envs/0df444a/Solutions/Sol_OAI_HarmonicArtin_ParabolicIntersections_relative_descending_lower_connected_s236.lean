-- Prove2me | solution 1 for OAI.HarmonicArtin.ParabolicIntersections.relative_descending_lower_connected_s236
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T20:14:44.484068+00:00
-- url     : https://prove2.me/submissions/56709ec5-565d-4f05-9a31-d3dcc968a190

import Mathlib
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap010
import Definitions.Def_OAIQ236Ap013
import Theorems.Thm_OAI_HarmonicArtin_ParabolicIntersections_null_boundary_contradiction_s236
import Theorems.Thm_OAI_HarmonicArtin_ParabolicIntersections_pointedCandidate_comparison_parabolic_s236

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_UnfoldedPresentation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomDimension2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_Initial
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TestExact
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HighestLocalGeneratorTest
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_InverseWordActionAppend
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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_NegativeTwistCapDisjoint
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PacketPermAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PacketPermExterior
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
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
  (hn:∀ a,Q.source a≠Q.target a)

omit [Fintype V] [DecidableEq A] in
lemma classLevelArray_initial (α β:V) (q:ℤ) :
    classLevelArray Q (initialClass Q (K:=K) α) (β,q)=if α=β ∧ q=0 then 1 else 0 := by
  classical
  rw [initialClass,classLevelArray_of_minimal Q _ (show (initialProjective Q α).IsMinimal Q from
    fun i j=>rfl)]
  change (initialProjective Q α).levelArray Q (β,q)=_
  rw [levelArray_eq_sum]
  simp only [initialProjective,GeneratorPlacement.level,Finset.univ_unique,
    Finset.sum_singleton,Finsupp.single_apply,Prod.mk.injEq]
  simp [eq_comm]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_RootNonposDescent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

lemma length_le_of_all_descents (z : W)
    (hz : ∀ i,cs.length (z*cs.simple i)+1=cs.length z) (w : W) :
    cs.length w ≤ cs.length z := by
  have := length_mul_of_all_descents cs z hz w
  omega

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnfoldedHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_NerveOrderMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
open scoped unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

lemma simplex_zero_unique (z:Convexity.StdSimplex ℝ (Fin 1)) :
    z=Convexity.StdSimplex.single 0 :=
  Subsingleton.elim _ _

lemma realizeSimplex_const {P Q:Type u} [Preorder P] [Preorder Q] (c:Q)
    {n:SimplexCategory} (x:(nerve P).obj (op n))
    (z:Convexity.StdSimplex ℝ (Fin (n.len+1))) :
    realizeSimplex (nerve Q) ((nerveMap (OrderHom.const P c).toFunctor).app (op n) x) z=nerveVertex Q c := by
  let a:n⟶⦋0⦌:=SimplexCategory.mkHom (OrderHom.const _ 0)
  have he:(nerve Q).map a.op (ComposableArrows.mk₀ c)=
      (nerveMap (OrderHom.const P c).toFunctor).app (op n) x:=by
    apply nerve.ext_of_isThin
    rfl
  have hh:=realizeSimplex_natural (nerve Q) a (ComposableArrows.mk₀ c) z
  rw [he] at hh
  exact hh.trans (congrArg (realizeSimplex (nerve Q) (ComposableArrows.mk₀ c))
    (simplex_zero_unique (Convexity.StdSimplex.map a.toOrderHom z)))

lemma nerveOrderMap_const {P Q:Type u} [Preorder P] [Preorder Q] (c:Q) :
    nerveOrderMap (OrderHom.const P c)=ContinuousMap.const _ (nerveVertex Q c) := by
  have he:SSet.toTop.map (nerveMap (OrderHom.const P c).toFunctor)=TopCat.const (X:=|nerve P|) (nerveVertex Q c):=by
    apply (sSetTopAdj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit,Adjunction.homEquiv_unit]
    ext n x
    apply (toSimp _ n).injective
    ext z
    change SSet.toTop.map (nerveMap (OrderHom.const P c).toFunctor) (realizeSimplex (nerve P) x z)=nerveVertex Q c
    rw [realizeSimplex_map,realizeSimplex_const]
  exact congrArg TopCat.Hom.hom he

theorem nerve_contractible_of_order_clip {P:Type u} [Preorder P]
    (e:P→o P) (c:P) (he:∀p,e p≤p) (hc:∀p,e p ≤ c) : ContractibleSpace |nerve P| := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨nerveVertex P c,?_⟩
  have hh:ContinuousMap.Homotopic (nerveOrderMap (OrderHom.id (α:=P)))
      (nerveOrderMap (OrderHom.const P c)):=
    ⟨(nerveOrderComparisonHomotopy e (OrderHom.id (α:=P)) he).symm.trans
      (nerveOrderComparisonHomotopy e (OrderHom.const P c) hc)⟩
  simpa only [nerveOrderMap_id,nerveOrderMap_const] using hh

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightHomeomorph
attribute [-instance] _root_.OAI.HarmonicArtin.WeightContractionPiece.instReflExtends
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

universe u v
variable {P:Type u} {Q:Type v} [PartialOrder P] [PartialOrder Q]

variable (r:P→P→Prop) (c:P)

namespace WeightContractionPiece
variable {r c}

lemma extends_trans {a b d:WeightContractionPiece r c} (h:a.Extends b) (k:b.Extends d) : a.Extends d := by
  obtain ⟨h,hh⟩:=h
  obtain ⟨k,hk⟩:=k
  refine ⟨h.trans k,?_⟩
  intro t w
  rw [hh,hk,weightMap_comp]
  rfl

end WeightContractionPiece
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_LateDelay
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval
open Topology

attribute [local instance] Classical.propDecidable
universe u v
variable {A:Type u} {X:Type v} [TopologicalSpace A] [TopologicalSpace X] [T2Space X]

variable (i:C(A,X)) (r:C(X,A)) (hr:∀a,r (i a)=a)
  (D:ContinuousMap.HomotopyRel (ContinuousMap.id X) (i.comp r) (Set.range i))
  (δ:C(X,I)) (hd:∀x,δ x<1) (hz:∀x,δ x=0↔x∈Set.range i)
  (c:A) (H:ContinuousMap.Homotopy (ContinuousMap.id A) (ContinuousMap.const A c))

include hr in
lemma extendContraction_old (t:I) (a:A) :
    extendContraction i r D δ hd hz c H (t,i a)=i (H (t,a)) := by
  have he:δ (i a)=0:=(hz _).mpr ⟨a,rfl⟩
  have hlate:δ (i a)≤t:=he ▸ t.property.1
  change extensionValue i r D δ hd hz c H (t,i a)=_
  rw [show (t,i a)=(⟨(t,i a),hlate⟩:LateDelay δ).val from rfl,extensionValue_late]
  change i (H (lateDelayTime δ hd ⟨(t,i a),hlate⟩,r (i a)))=_
  have ht:lateDelayTime δ hd ⟨(t,i a),hlate⟩=t:=by
    apply Subtype.ext
    simp [lateDelayTime,he]
  rw [ht,hr]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightVertexRetract
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

universe u
variable {P:Type u} [PartialOrder P] (v:P)
  (c:OrderWeights (WeightLink v))
  (H:ContinuousMap.Homotopy (ContinuousMap.id _) (ContinuousMap.const _ c))

lemma weightVertexRetract_old (w:OrderWeights (WeightOld v)) :
    weightVertexRetract v c H (weightOldMap v w)=w := by
  change coneAttachmentRetract _ c H ((weightAttachEquiv v c).symm (weightOldMap v w))=w
  rw [weightAttachEquiv_symm_old]
  rfl

variable (a:OrderWeights (WeightOld v))
  (K:ContinuousMap.Homotopy (ContinuousMap.id _) (ContinuousMap.const _ a))

lemma weightExtendContraction_old (t:I) (w:OrderWeights (WeightOld v)) :
    weightExtendContraction v c H a K (t,weightOldMap v w)=weightOldMap v (K (t,w)) :=
  extendContraction_old (weightOldMap v) (weightVertexRetract v c H)
    (weightVertexRetract_old v c H) (weightVertexDeformation v c H)
    (weightVertexDelay v) (weightVertexDelay_lt v) (weightVertexDelay_zero v) a K t w

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_InsertOldIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

variable (A:Set P) (v:P) (hv:v∉A)
  (l:OrderWeights (WeightLink (⟨v,Set.mem_insert v A⟩:↥(insert v A))))
  (L:ContinuousMap.Homotopy (ContinuousMap.id _) (ContinuousMap.const _ l))
  (a:OrderWeights A) (H:ContinuousMap.Homotopy (ContinuousMap.id _) (ContinuousMap.const _ a))

lemma weightInsertContraction_old (t:I) (w:OrderWeights A) :
    weightInsertContraction A v hv l L a H (t,weightMap (weightSubset A (insert v A) (Set.subset_insert v A)) w)=
      weightMap (weightSubset A (insert v A) (Set.subset_insert v A)) (H (t,w)) := by
  let e:=weightHomeomorph (insertOldIso A v hv)
  have he:weightMap (weightSubset A (insert v A) (Set.subset_insert v A)) w=
      weightOldMap (⟨v,Set.mem_insert v A⟩:↥(insert v A)) (e w):=by
    change _=weightMap (weightOldIncl _) (weightMap (OrderHomClass.toOrderHom (insertOldIso A v hv)) w)
    rw [weightMap_comp,insertOldIso_incl]
  rw [he]
  change weightExtendContraction _ l L (e a) (transportContraction e a H) (t,weightOldMap _ (e w))=_
  rw [weightExtendContraction_old]
  change weightMap (weightOldIncl _) (e (H (t,e.symm (e w))))=_
  rw [e.symm_apply_apply]
  change weightMap (weightOldIncl _) (weightMap (OrderHomClass.toOrderHom (insertOldIso A v hv)) (H (t,w)))=_
  rw [weightMap_comp,insertOldIso_incl]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnionCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P] {r:P→P→Prop} {c:P}
namespace WeightContractionPiece

variable (C:Set (WeightContractionPiece r c)) (hc:IsChain Extends C) (hne:C.Nonempty)

lemma extends_union {a:WeightContractionPiece r c} (ha:a∈C) : a.Extends (union C hc hne) := by
  refine ⟨subset_union C ha,?_⟩
  intro t w
  change weightMap a.inclusion (a.hom (t,w))=
    weightMap (weightInclusion (unionCarrier C)) (unionMap C hc hne (t,weightMap (unionIncl C ⟨a,ha⟩) w))
  rw [unionMap_on,weightMap_comp]
  rfl

end WeightContractionPiece
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_Initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

variable {r:P→P→Prop} {c:P}
namespace WeightContractionPiece

variable (wf:WellFounded r) (htotal:∀x y,x≠y → r x y ∨ r y x)

include wf htotal in
lemma missing_minimal (a:WeightContractionPiece r c) (ha:∃x,x∉a.carrier) :
    ∃v,v∉a.carrier ∧ ∀x,x∈a.carrier↔r x v := by
  obtain ⟨v,hv,hm⟩:=wf.has_min a.carrierᶜ ha
  refine ⟨v,hv,?_⟩
  intro x
  constructor
  · intro hx
    have hne:x≠v:=by intro he;exact hv (he ▸ hx)
    rcases htotal x v hne with h|h
    · exact h
    · exact (hv (a.down hx h)).elim
  · intro h
    by_contra hn
    exact hm x hn h

variable (a:WeightContractionPiece r c) (v:P) (hv:v∉a.carrier)
  (heA:∀x,x∈a.carrier↔r x v)
  (hlink:ContractibleSpace (OrderWeights (WeightEarlierLink r v)))

lemma extends_successor : a.Extends (successor wf a v hv heA hlink) := by
  refine ⟨Set.subset_insert v a.carrier,?_⟩
  intro t w
  change weightMap a.inclusion (a.hom (t,w))=
    weightMap (weightInclusion (insert v a.carrier))
      (weightInsertContraction a.carrier v hv (insertLinkContractionPoint wf a v heA hlink)
        (insertLinkContraction wf a v heA hlink) (weightVertex ⟨c,a.root_mem⟩) a.hom
        (t,weightMap (weightSubset a.carrier (insert v a.carrier) (Set.subset_insert v a.carrier)) w))
  rw [weightInsertContraction_old,weightMap_comp]
  rfl

end WeightContractionPiece

theorem orderWeights_contractible_of_earlier_links (r:P→P→Prop) (wf:WellFounded r)
    (htotal:∀x y,x≠y → r x y ∨ r y x) (c:P) (hc:∀x,¬r x c)
    (hl:∀v,v≠c → ContractibleSpace (OrderWeights (WeightEarlierLink r v))) :
    ContractibleSpace (OrderWeights P) := by
  let : Nonempty (WeightContractionPiece r c) := ⟨WeightContractionPiece.initial hc⟩
  obtain ⟨a,ha⟩:=exists_maximal_of_nonempty_chains_bounded
    (r:=@WeightContractionPiece.Extends P _ r c)
    (fun C hc hn=>⟨WeightContractionPiece.union C hc hn,
      fun a ha=>WeightContractionPiece.extends_union C hc hn ha⟩)
    WeightContractionPiece.extends_trans
  have hfull:∀x,x∈a.carrier:=by
    by_contra hn
    have he:∃x,x∉a.carrier:=not_forall.mp hn
    obtain ⟨v,hv,heA⟩:=WeightContractionPiece.missing_minimal wf htotal a he
    have hvc:v≠c:=by intro he;exact hv (he ▸ a.root_mem)
    have hnext:=WeightContractionPiece.extends_successor wf a v hv heA (hl v hvc)
    have hback:=ha _ hnext
    exact hv (hback.choose (Set.mem_insert v a.carrier))
  let e:a.carrier≃oP:={
    toFun:=Subtype.val
    invFun:=fun x=>⟨x,hfull x⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl
    map_rel_iff':=by intros;rfl }
  exact (contractible_iff_id_nullhomotopic _).mpr
    ⟨weightHomeomorph e (weightVertex ⟨c,a.root_mem⟩),
      ⟨transportContraction (weightHomeomorph e) _ a.hom⟩⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_ContractionPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

theorem orderWeights_contractible_of_piece (r:P→P→Prop) (wf:WellFounded r)
    (htotal:∀x y,x≠y → r x y ∨ r y x) (c:P) (a0:WeightContractionPiece r c)
    (hl:∀v,v∉a0.carrier → ContractibleSpace (OrderWeights (WeightEarlierLink r v))) :
    ContractibleSpace (OrderWeights P) := by
  let X:Type u:={a:WeightContractionPiece r c // a0.Extends a}
  let R:X→X→Prop:=fun a b=>a.val.Extends b.val
  let : Nonempty X := ⟨a0,WeightContractionPiece.extends_refl a0⟩
  have hbound:∀C:Set X,IsChain R C→C.Nonempty→∃ub:X,∀a∈C,R a ub:=by
    intro C hc hn
    let D:Set (WeightContractionPiece r c):=Subtype.val '' C
    have hd:IsChain WeightContractionPiece.Extends D:=by
      rintro a ⟨a,ha,rfl⟩ b ⟨b,hb,rfl⟩ hne
      exact hc ha hb (fun he=>hne (congrArg Subtype.val he))
    have hdn:D.Nonempty:=hn.image Subtype.val
    let u:=WeightContractionPiece.union D hd hdn
    have h0:a0.Extends u:=by
      obtain ⟨a,ha⟩:=hn
      exact WeightContractionPiece.extends_trans a.property
        (WeightContractionPiece.extends_union D hd hdn ⟨a,ha,rfl⟩)
    refine ⟨⟨u,h0⟩,?_⟩
    intro a ha
    exact WeightContractionPiece.extends_union D hd hdn ⟨a,ha,rfl⟩
  obtain ⟨a,ha⟩:=exists_maximal_of_nonempty_chains_bounded (r:=R) hbound
    (fun hab hbd=>WeightContractionPiece.extends_trans hab hbd)
  have hfull:∀x,x∈a.val.carrier:=by
    by_contra hn
    obtain ⟨v,hv,heA⟩:=WeightContractionPiece.missing_minimal wf htotal a.val (not_forall.mp hn)
    have hv0:v∉a0.carrier:=fun he=>hv (a.property.choose he)
    let b:=WeightContractionPiece.successor wf a.val v hv heA (hl v hv0)
    have hab:a.val.Extends b:=WeightContractionPiece.extends_successor wf a.val v hv heA (hl v hv0)
    let z:X:=⟨b,WeightContractionPiece.extends_trans a.property hab⟩
    have hback:=ha z hab
    exact hv (hback.choose (Set.mem_insert v a.val.carrier))
  let e:a.val.carrier≃oP:={
    toFun:=Subtype.val
    invFun:=fun x=>⟨x,hfull x⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl
    map_rel_iff':=by intros;rfl }
  exact (contractible_iff_id_nullhomotopic _).mpr
    ⟨weightHomeomorph e (weightVertex ⟨c,a.val.root_mem⟩),
      ⟨transportContraction (weightHomeomorph e) _ a.val.hom⟩⟩

theorem orderWeights_contractible_of_initial (r:P→P→Prop) (wf:WellFounded r)
    (htotal:∀x y,x≠y → r x y ∨ r y x) (A:Set P)
    (hdown:∀{x y},x∈A → r y x → y∈A)
    (hA:ContractibleSpace (OrderWeights A))
    (hl:∀v,v∉A → ContractibleSpace (OrderWeights (WeightEarlierLink r v))) :
    ContractibleSpace (OrderWeights P) := by
  obtain ⟨a,⟨H⟩⟩:=@id_nullhomotopic _ _ hA
  obtain ⟨v,hv⟩:=a.support_nonempty
  let c:P:=v.val

  let H':ContinuousMap.Homotopy (ContinuousMap.id (OrderWeights A))
      (ContinuousMap.const _ (weightVertex v)):=
    contractionToPoint a H (weightVertex v)
  let a0:WeightContractionPiece r c:={
    carrier:=A
    root_mem:=v.property
    down:=hdown
    hom:=H' }
  exact orderWeights_contractible_of_piece r wf htotal c a0 hl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightJoinKey
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

omit [PartialOrder P] in
lemma weightJoinEarlier_wf (A:Set P) (d:P→ℕ) : WellFounded (WeightJoinEarlier A d) :=
  InvImage.wf (fun x=>(weightJoinKey A d x,x))
    (wellFounded_lt.prod_lex WellOrderingRel.isWellOrder.wf)

omit [PartialOrder P] in
lemma weightJoinEarlier_iff (A:Set P) (d:P→ℕ) (x y:P) :
    WeightJoinEarlier A d x y ↔ weightJoinKey A d x<weightJoinKey A d y ∨
      weightJoinKey A d x=weightJoinKey A d y ∧ WellOrderingRel x y := Prod.lex_iff

omit [PartialOrder P] in
lemma weightJoinEarlier_total (A:Set P) (d:P→ℕ) (x y:P) (h:x≠y) :
    WeightJoinEarlier A d x y ∨ WeightJoinEarlier A d y x := by
  rw [weightJoinEarlier_iff,weightJoinEarlier_iff]
  rcases lt_trichotomy (weightJoinKey A d x) (weightJoinKey A d y) with h'|he|h'
  · exact Or.inl (Or.inl h')
  · rcases trichotomous_of WellOrderingRel x y with hl|he'|hr
    · exact Or.inl (Or.inr ⟨he,hl⟩)
    · exact (h he').elim
    · exact Or.inr (Or.inr ⟨he.symm,hr⟩)
  · exact Or.inr (Or.inl h')

omit [PartialOrder P] in
lemma weightJoinEarlier_initial (A:Set P) (d:P→ℕ) {x y:P} (hx:x∈A)
    (hy:WeightJoinEarlier A d y x) : y∈A := by
  by_contra hn
  rw [weightJoinEarlier_iff] at hy
  simp [weightJoinKey,hx,hn] at hy

omit [PartialOrder P] in
lemma weightJoinEarlier_old (A:Set P) (d:P→ℕ) {x y:P} (hx:x∈A) (hy:y∉A) :
    WeightJoinEarlier A d x y := by
  rw [weightJoinEarlier_iff]
  left
  simp [weightJoinKey,hx,hy]

theorem weightJoin_contractible (N:ℕ) : ∀{P:Type u} [PartialOrder P]
    (A:Set P) (d:P→ℕ),
    (∀x,x∉A → d x<N) →
    (∀{x y},x∉A → y∉A → x<y → d y<d x) →
    (∀{a b},a∈A → b∉A → a≤b) →
    ContractibleSpace (OrderWeights A) → ContractibleSpace (OrderWeights P) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro P inst A d hb hd hcross hA
    let r:=WeightJoinEarlier A d
    apply orderWeights_contractible_of_initial r (weightJoinEarlier_wf A d)
      (weightJoinEarlier_total A d) A (weightJoinEarlier_initial A d) hA
    intro v hv
    let L:=WeightEarlierLink r v
    let A':Set L:={x | x.val∈A}
    have hne (x:L) : x.val≠v := by
      intro he
      have hr:=x.property.1
      rw [he] at hr
      exact (weightJoinEarlier_wf A d).irrefl.irrefl v hr
    have hupper (x:L) (hx:x∉A') : v<x.val := by
      have hr:WeightJoinEarlier A d x.val v:=x.property.1
      rw [weightJoinEarlier_iff] at hr
      have hx':x.val∉A:=hx
      simp [weightJoinKey,hx',hv] at hr
      rcases x.property.2 with hl|hu
      · have lt:x.val<v:=lt_of_le_of_ne hl (hne x)
        have :=hd hx' hv lt
        omega
      · exact lt_of_le_of_ne hu (hne x).symm
    let e:A≃oA':={
      toFun:=fun a=>⟨⟨a.val,weightJoinEarlier_old A d a.property hv,
        Or.inl (hcross a.property hv)⟩,a.property⟩
      invFun:=fun a=>⟨a.val.val,a.property⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl
      map_rel_iff':=by intros;rfl }
    have hA':ContractibleSpace (OrderWeights A'):=
      (weightHomeomorph e).contractibleSpace_iff.mp hA
    exact ih (d v) (hb v hv) A' (fun x:L=>d x.val)
      (fun x hx=>hd hv hx (hupper x hx))
      (by intro x y hx hy hxy;exact hd hx hy hxy)
      (by intro a b ha hb;exact hcross ha hb) hA'

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightEarlierLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

lemma weightLink_lower_cross (r:P→P→Prop) (hirr:∀x,¬r x x) (v:P)
    {a b:WeightEarlierLink r v} (ha:a.val<v) (hb:¬b.val<v) : a≤b := by
  rcases b.property.2 with h|h
  · rcases lt_or_eq_of_le h with hl|he
    · exact (hb hl).elim
    · have hr:=b.property.1
      rw [he] at hr
      exact (hirr v hr).elim
  · exact ha.le.trans h

theorem weightLink_contractible_of_lower (r:P→P→Prop) (hirr:∀x,¬r x x) (v:P)
    (k:P→ℕ) (N:ℕ) (hk:∀x,k x≤N) (hmono:StrictMono k)
    (h:ContractibleSpace (OrderWeights (WeightEarlierLower r v))) :
    ContractibleSpace (OrderWeights (WeightEarlierLink r v)) := by
  let A:Set (WeightEarlierLink r v):={x | x.val<v}
  have hA:ContractibleSpace (OrderWeights A):=(weightHomeomorph (earlierLowerIso r v)).contractibleSpace_iff.mp h
  apply weightJoin_contractible (N+1) A (fun x=>N-k x.val)
    (fun x _=>by omega) ?_ (weightLink_lower_cross r hirr v) hA
  intro x y hx hy hxy
  have hlt:k x.val<k y.val:=hmono hxy
  have hb:=hk y.val
  omega

theorem weightJoin_contractible_upper (N:ℕ) (A:Set P) (k:P→ℕ)
    (hk:∀x,x∈A → k x<N)
    (hmono:∀{x y},x∈A → y∈A → x<y → k x<k y)
    (hcross:∀{a b},a∈A → b∉A → a≤b)
    (hB:ContractibleSpace (OrderWeights (Aᶜ:Set P))) : ContractibleSpace (OrderWeights P) := by
  have hdual:ContractibleSpace (OrderWeights Pᵒᵈ):=by
    apply weightJoin_contractible N (Aᶜ:Set Pᵒᵈ) k
    · intro x hx
      exact hk x (not_not.mp hx)
    · intro x y hx hy hxy
      exact hmono (not_not.mp hy) (not_not.mp hx) hxy
    · intro a b ha hb
      exact hcross (not_not.mp hb) ha
    · exact (weightDualHomeomorph (P:=(Aᶜ:Set P))).contractibleSpace_iff.mp hB
  exact (weightDualHomeomorph (P:=P)).contractibleSpace_iff.mpr hdual

theorem weightLink_contractible_of_upper (r:P→P→Prop) (hirr:∀x,¬r x x) (v:P)
    (k:P→ℕ) (N:ℕ) (hk:∀x,k x≤N) (hmono:StrictMono k)
    (h:ContractibleSpace (OrderWeights (WeightEarlierUpper r v))) :
    ContractibleSpace (OrderWeights (WeightEarlierLink r v)) := by
  let A:Set (WeightEarlierLink r v):={x | x.val<v}
  have hB:ContractibleSpace (OrderWeights (Aᶜ:Set (WeightEarlierLink r v))):=
    (weightHomeomorph (earlierUpperIso r hirr v)).contractibleSpace_iff.mp h
  apply weightJoin_contractible_upper (N+1) A (fun x=>k x.val)
    (fun x _=>Nat.lt_succ_of_le (hk x.val))
    (by intro x y _ _ hxy;exact hmono hxy) (weightLink_lower_cross r hirr v) hB

lemma weightLink_nonempty_parts (r:P→P→Prop) (hirr:∀x,¬r x x) (v:P)
    (h:Nonempty (WeightEarlierLink r v)) :
    Nonempty (WeightEarlierLower r v) ∨ Nonempty (WeightEarlierUpper r v) := by
  obtain ⟨x,hx,hcmp⟩:=h
  have hne:x≠v:=by intro he;exact hirr v (he ▸ hx)
  exact hcmp.elim (fun h=>Or.inl ⟨x,hx,lt_of_le_of_ne h hne⟩)
    (fun h=>Or.inr ⟨x,hx,lt_of_le_of_ne h hne.symm⟩)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_OrderWeightsContractibleLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

theorem orderWeights_contractible_of_lower_fibers (A:Set P) (k:P→ℕ) (N:ℕ)
    (hk:∀x,k x≤N) (hm:StrictMono k) (hA:ContractibleSpace (OrderWeights A))
    (hf:∀v,v∉A → ContractibleSpace (OrderWeights {x:P // x∈A ∧ x<v})) :
    ContractibleSpace (OrderWeights P) := by
  let d:P→ℕ:=fun x=>N-k x
  let r:=WeightJoinEarlier A d
  have hw:=weightJoinEarlier_wf A d
  apply orderWeights_contractible_of_initial r hw (weightJoinEarlier_total A d) A
    (weightJoinEarlier_initial A d) hA
  intro v hv
  have he:∀x,x<v → (r x v ↔ x∈A):=by
    intro x hx
    constructor
    · intro hr
      by_contra hn
      change WeightJoinEarlier A d x v at hr
      rw [weightJoinEarlier_iff] at hr
      have hlt:=hm hx
      have hb:=hk v
      simp [weightJoinKey,hn,hv,d] at hr
      omega
    · intro ha
      exact weightJoinEarlier_old A d ha hv
  let e:WeightEarlierLower r v ≃o {x:P // x∈A ∧ x<v}:={
    toFun:=fun x=>⟨x.val,(he x.val x.property.2).mp x.property.1,x.property.2⟩
    invFun:=fun x=>⟨x.val,(he x.val x.property.2).mpr x.property.1,x.property.2⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl
    map_rel_iff':=by intros;rfl }
  exact weightLink_contractible_of_lower r (fun x=>hw.irrefl.irrefl x) v k N hk hm
    ((weightHomeomorph e).contractibleSpace_iff.mpr (hf v hv))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ProductBoxSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
universe u

lemma weight_contractible_of_order_retraction {P Q:Type u} [PartialOrder P] [PartialOrder Q]
    (r:P→oQ) (i:Q→oP) (hr:r.comp i=OrderHom.id) (hi:∀p,p ≤ i (r p))
    (h:ContractibleSpace (OrderWeights Q)) : ContractibleSpace (OrderWeights P) := by
  have hQ:ContractibleSpace |nerve Q|:=nerveWeightsHomeomorph.contractibleSpace_iff.mpr h
  have hP:ContractibleSpace |nerve P|:=(nerveOrderRetractionEquiv r i hr hi).contractibleSpace_iff.mpr hQ
  exact nerveWeightsHomeomorph.contractibleSpace_iff.mp hP

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_BinaryProductBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {A B:Type u} [PartialOrder A] [PartialOrder B] [OrderTop A] [OrderTop B]

omit [OrderTop B] in
lemma binaryProductBox_contractible (b:A×B) (hb:b.1=⊤)
    (h:ContractibleSpace (OrderWeights {a:A //a≠⊤})) :
    ContractibleSpace (OrderWeights (BinaryProductBox b)) := by
  let r : BinaryProductBox b →o {a:A //a≠⊤} :=
    { toFun := fun x=>⟨x.val.1,x.property.2⟩
      monotone' := fun _ _ h=>h.1 }
  let i : {a:A //a≠⊤} →o BinaryProductBox b :=
    { toFun := fun a=>⟨(a.val,b.2),⟨by simpa only [hb] using (le_top:a.val≤⊤),le_rfl⟩,a.property⟩
      monotone' := fun _ _ h=>⟨h,le_rfl⟩ }
  apply weight_contractible_of_order_retraction r i rfl ?_ h
  intro x
  exact ⟨le_rfl,x.property.1.2⟩

theorem binaryProductBoundary_contractible (k:BinaryProductBoundary A B→ℕ) (N:ℕ)
    (hk:∀x,k x≤N) (hm:StrictMono k)
    (h:ContractibleSpace (OrderWeights {a:A //a≠⊤})) :
    ContractibleSpace (OrderWeights (BinaryProductBoundary A B)) := by
  apply orderWeights_contractible_of_lower_fibers {x |x.val.1≠⊤} k N hk hm
  · exact (weightHomeomorph binaryBoundarySliceIso).contractibleSpace_iff.mpr
      (binaryProductBox_contractible (⊤:A×B) rfl h)
  · intro v hv
    have he:v.val.1=⊤:=not_not.mp hv
    exact (weightHomeomorph (binaryBoundaryFiberIso v he)).contractibleSpace_iff.mpr
      (binaryProductBox_contractible v.val he h)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionPacketAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator _root_.OAI.HarmonicArtin.unfoldedHom_simple _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
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

lemma fusionOrbit_homDimension (w:List (V × Bool)) (s t:V) (L H:FusionLabel m) (n v:ℤ) :
    classHomDimension Q n v (fusionPacketOrbit m d hd hdiag w s L)
      (fusionPacketOrbit m d hd hdiag w t H) =
    homDimension Q (initialProjective Q (s,L) : BasedComplex Q (K:=ℂ) PUnit.{1})
      (initialProjective Q (t,H) : BasedComplex Q (K:=ℂ) PUnit.{1}) n v := by
  obtain ⟨x,hx⟩ := fusionOrbit_in_action m d hd hdiag w
  rw [hx,hx,unfoldedFrame_homDimension]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionSignedPacketExterior
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
local notation "Q" => fusionQuiver m d hd

lemma fusionOrbit_frame_level (w:List (V × Bool)) (s:V) (H L:FusionLabel m) (q:ℤ)
    (hs:∀ b∈w,b.1≠s) :
    classLevelArray Q (fusionPacketOrbit m d hd hdiag w s H) ((s,L),q)=
      if H=L ∧ q=0 then 1 else 0 := by
  rw [fusionPacketOrbit,fusionWord_level_exterior m d hd hdiag w _ s L q hs,
    classLevelArray_initial]
  simp only [Prod.mk.injEq,true_and]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_SignedLetter
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnfoldedInclusionRange
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
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "Q" => fusionQuiver m d hd
local notation "aw" => sourceArtinAction M (K:=ℂ)

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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnfoldedInclusionRangeMono
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

omit [Fintype S] in
lemma unfoldedInclusion_range_mono {J T:Set S} (h:J⊆T) :
    Set.range (unfoldedInclusion M J)⊆Set.range (unfoldedInclusion M T) := by
  rintro α ⟨⟨j,L⟩,rfl⟩
  exact ⟨(⟨j,h j.property⟩,L),rfl⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CartanCommutingZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma sourceCartan_commuting_zero (s t:S) (h:M s t=2) :
    framedCartan M (.inl s) (.inl t)=0 := by
  have hn:s≠t:=by rintro rfl;have hh:=M.diagonal s;omega
  simp [framedCartan,hn,h,Real.cos_pi_div_two]

lemma harmonic_block_eq {ι:Type*} [Fintype ι] (C:Matrix ι ι ℝ) (U V:Set ι)
    (hU:(C.submatrix Subtype.val Subtype.val:Matrix U U ℝ).PosDef)
    (p q:ι→ℝ) (hp:∀i:U,(C *ᵥ p) i=0) (hq:∀i:U,(C *ᵥ q) i=0)
    (hzero:∀i∈U,∀j∈V,C i j=0) (hext:∀j,j∉U→j∉V→p j=q j) :
    ∀i∈U,p i=q i := by
  have he:(C.submatrix Subtype.val Subtype.val:Matrix U U ℝ) *ᵥ
      (fun i:U=>p i-q i)=0:=by
    funext i
    have hr:(C *ᵥ (p-q)) i=0:=by rw [Matrix.mulVec_sub,Pi.sub_apply,hp i,hq i,sub_self]
    rw [harmonic_row_split C U] at hr
    have hz:(∑j:↥(Uᶜ),C i j*(p-q) j)=0:=by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hv:j.val∈V
      · rw [hzero i i.property j hv,zero_mul]
      · simp only [Pi.sub_apply,hext j j.property hv,sub_self,mul_zero]
    rw [hz,add_zero] at hr
    exact hr
  have hh:=harmonic_solve_left (C.submatrix Subtype.val Subtype.val:Matrix U U ℝ) hU
    (fun i:U=>p i-q i)
  rw [he,Matrix.mulVec_zero] at hh
  intro i hi
  exact sub_eq_zero.mp (congrFun hh.symm ⟨i,hi⟩)

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
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag

namespace IsolatedIterationData
variable {M} (D:IsolatedIterationData M)

lemma capJ (z:List ((S⊕Unit)×Bool)) (hc:D.capped z) :
    ∀ L,ClassCapOn Q (O z D.s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M D.J))) D.q := by
  intro L
  apply (hc L).mono
  apply closedNeighborhood_mono
  rw [unfoldedInclusion_range]
  exact fun α hα=>Set.image_mono D.hJI hα

end IsolatedIterationData
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CosetOrbit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CosetOrbitCap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveComponentPositive
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma sourcePositiveComponent_positive (p:S⊕Unit→ℝ) (i:S⊕Unit) (hi:0<p i)
    (j:S⊕Unit) (hj:j∈sourcePositiveComponent M p i) : 0<p j := by
  change Relation.ReflTransGen _ i j at hj
  induction hj with
  | refl => exact hi
  | tail _ hbc _ => exact hbc.2.2

omit [Fintype S] [LinearOrder S] in
lemma sourcePositiveComponent_connected (p:S⊕Unit→ℝ) (i:S⊕Unit) :
    ∀j l:sourcePositiveComponent M p i,
      Relation.ReflTransGen (fun a b:sourcePositiveComponent M p i=>framedCartan M a b<0) j l := by
  let I:=sourcePositiveComponent M p i
  have hi:i∈I:=Relation.ReflTransGen.refl
  have hroot:∀j:I,Relation.ReflTransGen (fun a b:I=>framedCartan M a b<0) ⟨i,hi⟩ j := by
    rintro ⟨j,hj⟩
    change Relation.ReflTransGen _ i j at hj
    induction hj with
    | refl => exact .refl
    | tail _ hbc ih => exact ih.tail hbc.2.1
  intro j l
  have hrev:=Relation.ReflTransGen.swap _ _ (hroot j)
  have hj:Relation.ReflTransGen (fun a b:I=>framedCartan M a b<0) j ⟨i,hi⟩:=
    Relation.ReflTransGen.mono (by intro a b h; dsimp [Function.swap] at h; rwa [framedCartan_symm] at h) _ _ hrev
  exact hj.trans (hroot l)

omit [Fintype S] [LinearOrder S] in
lemma sourcePositiveComponent_spec (p:S⊕Unit→ℝ) (i:S⊕Unit) (hi:0<p i) :
    PositiveSupportComponent (framedCartan M) p (sourcePositiveComponent M p i) := by
  refine ⟨⟨i,Relation.ReflTransGen.refl⟩,sourcePositiveComponent_positive M p i hi,
    sourcePositiveComponent_connected M p i,?_⟩
  intro j hj l hjl hl
  exact hj.tail ⟨sourcePositiveComponent_positive M p i hi j hj,hjl,hl⟩

omit [Fintype S] [LinearOrder S] in
lemma sourcePositiveComponent_eq (p:S⊕Unit→ℝ) (i:S⊕Unit) (I:Set (S⊕Unit))
    (hI:PositiveSupportComponent (framedCartan M) p I) (hi:i∈I) :
    sourcePositiveComponent M p i=I := by
  ext j
  constructor
  · intro hj
    change Relation.ReflTransGen _ i j at hj
    induction hj with
    | refl => exact hi
    | tail _ hbc ih => exact hI.2.2.2 _ ih _ hbc.2.1 hbc.2.2
  · intro hj
    exact Relation.ReflTransGen.lift ((↑):I→S⊕Unit)
      (fun a b hab=>⟨hI.2.1 a a.property,hab,hI.2.1 b b.property⟩)
      ⟨i,hi⟩ ⟨j,hj⟩ (hI.2.2.1 ⟨i,hi⟩ ⟨j,hj⟩)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_TypeComponent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma framedCartan_neg_of_label_ne_two (s t:S) (hst:s≠t) (hm:M s t≠2) :
    framedCartan M (.inl s) (.inl t)<0 := by
  simp only [framedCartan,hst,↓reduceIte]
  split_ifs with hz
  · norm_num
  · have hn:2<M s t:=by have h:=M.off_diagonal s t hst;omega
    have hr:(2:ℝ)<M s t:=by exact_mod_cast hn
    have hp:0<(M s t:ℝ):=by linarith
    have hc:0<Real.cos (Real.pi/(M s t:ℝ)):=by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · have h:=div_pos Real.pi_pos hp
        linarith [Real.pi_pos]
      · apply (div_lt_iff₀ hp).mpr
        nlinarith [Real.pi_pos]
    nlinarith

omit [Fintype S] [LinearOrder S] in
lemma sourceTypeComponent_self (P:Deligne M) (i:S) (hi:i∈P.val.1) :
    i∈sourceTypeComponent M P i hi := ⟨hi,.refl⟩

omit [Fintype S] [LinearOrder S] in
lemma sourceTypeComponent_subset (P:Deligne M) (i:S) (hi:i∈P.val.1) :
    sourceTypeComponent M P i hi⊆P.val.1 := fun _ h=>h.choose

omit [Fintype S] [LinearOrder S] in
lemma sourceTypeComponent_closed (P:Deligne M) (i:S) (hi:i∈P.val.1)
    (j:S) (hj:j∈sourceTypeComponent M P i hi) (k:S) (hk:k∈P.val.1)
    (hjk:framedCartan M (.inl j) (.inl k)<0) : k∈sourceTypeComponent M P i hi := by
  obtain ⟨hj,h⟩:=hj
  exact ⟨hk,h.tail hjk⟩

omit [Fintype S] [LinearOrder S] in
lemma sourceTypeComponent_commutes (P:Deligne M) (i:S) (hi:i∈P.val.1)
    (j:S) (hj:j∈sourceTypeComponent M P i hi) (k:S)
    (hk:k∈P.val.1\sourceTypeComponent M P i hi) : M j k=2 := by
  by_contra hn
  exact hk.2 (sourceTypeComponent_closed M P i hi j hj k hk.1
    (framedCartan_neg_of_label_ne_two M j k (by rintro rfl;exact hk.2 hj) hn))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_NeighborhoodProject
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
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma sourceNeighborhood_project (I:Set (S⊕Unit)) :
    closedNeighborhood Q (fusionColorRegion m I) ⊆ fusionColorRegion m (sourceClosedRegion M I) := by
  rintro α (ha|⟨β,hβ,a,hs,ht⟩)
  · exact Or.inl ha
  · by_cases hα:α.1∈I
    · exact Or.inl hα
    · have hn:β.1≠α.1:=by intro he;exact hα (he ▸ hβ)
      have hC:fusionFoldedCartan m (coxeterFusionEdge M)=framedCartan M:=by
        convert fusionFoldedCartan_eq_framedCartan M using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        exact Subsingleton.elim _ _
      have hh:=fusion_arrow_color_cartan_neg m (coxeterFusionEdge M) (fusionLabelSize_ge_two M) a
        (fun he=>hn ((congrArg Prod.fst hs).symm.trans
          (he.trans (congrArg Prod.fst ht))))
      rw [hC] at hh
      have hh':framedCartan M β.1 α.1<0:=by
        simpa only [show a.1.1=β from hs,show a.1.2=α from ht] using hh
      exact Or.inr ⟨β.1,hβ,by rwa [framedCartan_symm]⟩

omit [Fintype S] [LinearOrder S] in
lemma sourceBlock_boundary_outside (P:Deligne M) (B:Set S) (_hB:B⊆P.val.1)
    (hc:∀i∈B,∀j∈P.val.1\B,M i j=2) (v:S⊕Unit)
    (hv:v∈sourceClosedRegion M (Sum.inl '' B)) (ho:v∉Sum.inl '' B) :
    v∉Sum.inl '' P.val.1 := by
  rcases hv with hv|⟨u,hu,huv⟩
  · exact (ho hv).elim
  · obtain ⟨i,hi,rfl⟩:=hu
    rintro ⟨j,hj,rfl⟩
    have hjB:j∉B:=fun h=>ho ⟨j,h,rfl⟩
    have hz:=sourceCartan_commuting_zero M i j (hc i hi j ⟨hj,hjB⟩)
    rw [framedCartan_symm,hz] at huv
    exact (lt_irrefl 0 huv)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_NullPatch2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma sourcePositiveComponent_boundary_zero (p:S⊕Unit→ℝ) (hp:∀v,0≤p v)
    (i:S⊕Unit) (hi:0<p i) (v:S⊕Unit) (ho:v∉sourcePositiveComponent M p i)
    (hn:∃u∈sourcePositiveComponent M p i,framedCartan M v u<0) : p v=0 := by
  by_contra hz
  have hv:0<p v:=lt_of_le_of_ne (hp v) (Ne.symm hz)
  obtain ⟨u,hu,huv⟩:=hn
  exact ho (hu.tail ⟨sourcePositiveComponent_positive M p i hi u hu,
    by rwa [framedCartan_symm],hv⟩)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_TieCode
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceTieCode_injective : Function.Injective (sourceTieCode M) := by
  let :=sourceDeligne_countable M
  let :=Encodable.ofCountable (Deligne M)
  exact Encodable.encode_injective

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ConnectedSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Connected support of transported indecomposable projectives

This proves the support-cut form of the connectedness assertion in
Proposition 2.7 of paper 082-03. The input is the dimension of the actual
endomorphism cohomology, rather than an assumed connectedness property.
-/

namespace HarmonicArtin.ParabolicIntersections

open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable

variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] in
private theorem blockProjector_diagonal (E : BasedComplex Q (K := K) I)
    (T : Set I) (hT : BlockClosed Q E T) (i : I) :
    diagonalVertex Q E i (blockProjector Q E T hT).matrix = if i ∈ T then 1 else 0 := by
  change ((blockProjection Q E T * blockInclusion Q E T) i i).vertex _ = _
  by_cases hi : i ∈ T
  · rw [Matrix.mul_apply, Finset.sum_eq_single (⟨i, hi⟩ : T)]
    · simp [blockProjection, blockInclusion, projectiveIdentity, hi, vertexId_mul_self]
    · intro j _ hji
      have hne : i ≠ (j : I) := fun he => hji (Subtype.ext he.symm)
      simp [blockProjection, projectiveIdentity, hne]
    · simp
  · have hz : (blockProjection Q E T * blockInclusion Q E T) i i = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hne : i ≠ (j : I) := fun he => hi (he.symm ▸ j.property)
      simp [blockProjection, projectiveIdentity, hne]
    simp [hz, hi]

omit [DecidableEq A] in
/-- A minimal complex with at most one-dimensional degree-zero
endomorphism cohomology cannot have two nonempty differential blocks. -/
theorem no_proper_block (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q)
    (hd : homDimension Q E E 0 0 ≤ 1) (T : Set I) (hT : BlockClosed Q E T)
    (i j : I) (hi : i ∈ T) (hj : j ∉ T) : False := by
  have hf := map_mem_homCycles Q (blockProjector Q E T hT)
  have hb := boundary_of_homDimension_le_one Q E E 0 0 hd
    (diagonalVertex Q E j) (fun _ h => diagonalVertex_boundary Q E hE j 0 0 h)
    (identity_mem_homCycles Q E) (by rw [diagonalVertex_identity]; exact one_ne_zero)
    hf (by rw [blockProjector_diagonal]; simp [hj])
  have hz := diagonalVertex_boundary Q E hE i 0 0 hb
  have he : diagonalVertex Q E i (blockProjector Q E T hT).matrix = 1 := by
    rw [blockProjector_diagonal]
    simp only [hi, ↓reduceIte]
  rw [he] at hz
  exact one_ne_zero hz

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
/-- Nonzero minimal differential entries either stay at one color or
follow an arrow of the quiver. This includes the token entries between
successive layers. -/
theorem differential_same_or_arrow (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (i j : I) (hn : E.differential i j ≠ 0) :
    (E.placement i).color = (E.placement j).color ∨
      ∃ a : A, Q.source a = (E.placement i).color ∧
        Q.target a = (E.placement j).color := by
  by_cases hc : (E.placement i).color = (E.placement j).color
  · exact Or.inl hc
  right
  by_contra ha
  push Not at ha
  apply hn
  apply ReversibleQuiver.Zigzag.ext
  · exact hE i j
  · funext a
    by_contra hnz
    have hh := coordinates_corner Q (E.entries.1 i j) (E.entries.2 i j)
      (p := .inr (.inl a)) hnz
    exact ha a hh.1 hh.2
  · funext v
    by_contra hnz
    have hh := coordinates_corner Q (E.entries.1 i j) (E.entries.2 i j)
      (p := .inr (.inr v)) hnz
    exact hc (hh.1.symm.trans hh.2)

omit [DecidableEq A] in
/-- If the support meets both a color set and its complement, it must
meet the exterior boundary of that set. This is the exact support fact
needed to find a boundary level below an isolated null layer. -/
theorem support_meets_boundary (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q)
    (hd : homDimension Q E E 0 0 ≤ 1) (U : Set V)
    (i j : I) (hi : (E.placement i).color ∈ U) (hj : (E.placement j).color ∉ U) :
    ∃ k : I, (E.placement k).color ∈ colorBoundary Q U := by
  by_contra hb
  push Not at hb
  apply no_proper_block Q E hE hd {k | (E.placement k).color ∈ U} _ i j hi hj
  intro a b hn
  rcases differential_same_or_arrow Q E hE a b hn with he | ⟨c, hs, ht⟩
  · change (E.placement a).color ∈ U ↔ (E.placement b).color ∈ U
    rw [he]
  · constructor
    · intro ha
      by_contra hnb
      exact hb b ⟨hnb, c, hs ▸ ha, ht⟩
    · intro hbb
      change (E.placement b).color ∈ U at hbb
      by_contra hna
      exact hb a ⟨hna, Q.reverse c,
        by simpa only [Q.source_reverse, ht] using hbb,
        by simpa only [Q.target_reverse] using hs⟩

section Fusion

variable {E W : Type} [Fintype E] [DecidableEq E] [Fintype W] [DecidableEq W]
  (m : E → ℕ) (d : W → W → FusionEdge E) (hd : ∀ s t, d s t = d t s)
  (hdiag : ∀ s, d s s = .units 0)

/-- The preceding support statement applies unconditionally to the
minimal representative of every transported projective in the fusion
packet action. -/
theorem fusionOrbit_support_meets_boundary (w : List (W × Bool)) (s : W)
    (L : FusionLabel m) (U : Set (FusionVertex (V := W) m))
    (i j : (fusionOrbitModel m d hd hdiag w s L).Index)
    (hi : ((fusionOrbitModel m d hd hdiag w s L).complex.placement i).color ∈ U)
    (hj : ((fusionOrbitModel m d hd hdiag w s L).complex.placement j).color ∉ U) :
    ∃ k : (fusionOrbitModel m d hd hdiag w s L).Index,
      ((fusionOrbitModel m d hd hdiag w s L).complex.placement k).color ∈
        colorBoundary (fusionQuiver m d hd) U := by
  apply support_meets_boundary (fusionQuiver m d hd) _
    (fusionOrbitModel_minimal m d hd hdiag w s L) _ U i j hi hj
  change homDimension (fusionQuiver m d hd)
    (minimalClassModel (fusionQuiver m d hd) (fusionPacketOrbit m d hd hdiag w s L)).complex
    (minimalClassModel (fusionQuiver m d hd) (fusionPacketOrbit m d hd hdiag w s L)).complex
    0 0 ≤ 1
  rw [minimalClassModel_homDimension, fusionOrbit_homDimension]
  exact initial_homDimension_le_one (fusionQuiver m d hd)
    (fusionQuiver_no_loops m d hd hdiag) (s, L) 0 0

end Fusion

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_BoundaryWitness
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A boundary witness below a capped isolated layer

The relative frame need not be adjacent to the isolated set. Connected
support finds an occupied exterior boundary color. A zero boundary cap
then puts that occupation strictly below the isolated layer. This is the
additional boundary argument of §5 of paper 082-03.
-/

namespace HarmonicArtin.ParabolicIntersections

open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable

variable {E V : Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E) (hd : ∀ s t, d s t = d t s)
  (hdiag : ∀ s, d s s = .units 0) (hm : ∀ e, 2 ≤ m e)

local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d

/-- The unchanged initial frame occurs in every minimal representative,
with its original label and level. -/
theorem orbit_frame_generator (w : List (V × Bool)) (s : V)
    (hw : ∀ a ∈ w, a.1 ≠ s) (L : FusionLabel m) :
    ∃ j : (fusionOrbitModel m d hd hdiag w s L).Index,
      ((fusionOrbitModel m d hd hdiag w s L).complex.placement j).color = (s, L) ∧
      ((fusionOrbitModel m d hd hdiag w s L).complex.placement j).level = 0 := by
  have hc := fusionOrbit_frame_level m d hd hdiag w s L L 0 hw
  rw [classLevelArray_minimal_apply] at hc
  simp only [and_self, ite_true, if_true] at hc
  have hp : 0 < Nat.card {i : (minimalClassModel Q (O w s L)).Index //
      ((minimalClassModel Q (O w s L)).complex.placement i).color = (s, L) ∧
      ((minimalClassModel Q (O w s L)).complex.placement i).level = 0} := by
    rw [hc]
    exact Nat.zero_lt_one
  rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff] at hp
  obtain ⟨j⟩ := hp
  exact ⟨j.val, j.property⟩

/-- A positive folded count is witnessed by an actual generator in one
member of the family, at the specified color and level. -/
theorem orbit_generator_of_positive (w : List (V × Bool)) (s v : V) (q : ℤ)
    (hp : 0 < μ w s q v) :
    ∃ L : FusionLabel m, ∃ i : (fusionOrbitModel m d hd hdiag w s L).Index,
      ((fusionOrbitModel m d hd hdiag w s L).complex.placement i).color.1 = v ∧
      ((fusionOrbitModel m d hd hdiag w s L).complex.placement i).level = q := by
  let H : FusionLabel m := fun e => ⟨0, by have := hm e; omega⟩
  have hweighted : 0 < fusionOrbitWeightedVector m d hd hdiag w s q (v, H) := by
    rw [fusionOrbitWeightedVector_eq m d hd hdiag hm]
    exact mul_pos (fusionWeight_pos m hm H) hp
  have hsum : 0 < ∑ L, fusionWeight m L * generatorVector Q (Y w s L q) (v, H) := by
    simpa only [fusionOrbitWeightedVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      using hweighted
  have hex : ∃ L, 0 < fusionWeight m L * generatorVector Q (Y w s L q) (v, H) := by
    by_contra hn
    push Not at hn
    exact (not_lt_of_ge (Finset.sum_nonpos (fun L _ => hn L))) hsum
  obtain ⟨L, hL⟩ := hex
  have hg : 0 < generatorVector Q (Y w s L q) (v, H) :=
    (mul_pos_iff_of_pos_left (fusionWeight_pos m hm L)).mp hL
  change 0 < (Nat.card {i : FusionOrbitLayerIndex m d hd hdiag w s L q //
    ((Y w s L q).placement i).color = (v, H)} : ℝ) at hg
  have hcard : 0 < Nat.card {i : FusionOrbitLayerIndex m d hd hdiag w s L q //
      ((Y w s L q).placement i).color = (v, H)} := by exact_mod_cast hg
  rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff] at hcard
  obtain ⟨i⟩ := hcard
  exact ⟨L, i.val.val, congrArg Prod.fst i.property, i.val.property⟩

/-- An occupied generator in `U` and an unoperated frame outside `U`
force an occupied boundary below `q`, if every boundary count at `q`
and above is zero. No condition `0 < q` is used. -/
theorem orbit_boundary_below (w : List (V × Bool)) (s : V)
    (hw : ∀ a ∈ w, a.1 ≠ s) (U : Set V) (hs : s ∉ U) (q : ℤ)
    (L : FusionLabel m) (i : (fusionOrbitModel m d hd hdiag w s L).Index)
    (hi : ((fusionOrbitModel m d hd hdiag w s L).complex.placement i).color.1 ∈ U)
    (hcap : ∀ H, ClassCapOn Q (O w s H)
      (colorBoundary Q (fusionColorRegion m U)) q)
    (hzero : ∀ v, v ∉ U → (∃ u ∈ U, C v u < 0) → μ w s q v = 0) :
    ∃ k v, k < q ∧ v ∉ U ∧ (∃ u ∈ U, C v u < 0) ∧ 0 < μ w s k v := by
  obtain ⟨j, hj, _⟩ := orbit_frame_generator m d hd hdiag w s hw L
  have hjs : ((fusionOrbitModel m d hd hdiag w s L).complex.placement j).color.1 = s :=
    congrArg Prod.fst hj
  obtain ⟨b, hb⟩ := fusionOrbit_support_meets_boundary m d hd hdiag w s L
    (fusionColorRegion m U) i j hi (by change _ ∉ U; rwa [hjs])
  have hbound := hcap L b hb
  obtain ⟨hbout, a, ha, he⟩ := hb
  let k := ((fusionOrbitModel m d hd hdiag w s L).complex.placement b).level
  let v := ((fusionOrbitModel m d hd hdiag w s L).complex.placement b).color.1
  have hv : v ∉ U := hbout
  have hau : a.1.1.1 ∈ U := ha
  have hev : a.1.2.1 = v := congrArg Prod.fst he
  have hne : a.1.1.1 ≠ a.1.2.1 := by
    intro h
    exact hv (hev ▸ h ▸ hau)
  have hneg := fusion_arrow_color_cartan_neg m d hm a hne
  rw [fusionFoldedCartan_symm m d hd, hev] at hneg
  have hinc : ∃ u ∈ U, C v u < 0 := ⟨a.1.1.1, hau, hneg⟩
  have hpos : 0 < μ w s k v :=
    fusionOrbitMultiplicity_pos_at_generator m d hd hdiag hm w s k L ⟨b, rfl⟩
  refine ⟨k, v, ?_, hv, hinc, hpos⟩
  by_contra hlt
  have hk : k = q := le_antisymm hbound (le_of_not_gt hlt)
  rw [hk, hzero v hv hinc] at hpos
  exact lt_irrefl 0 hpos

end HarmonicArtin.ParabolicIntersections

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
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "diag" => coxeterFusionEdge_diag M
local notation "hm" => fusionLabelSize_ge_two M
local notation "Q" => fusionQuiver m d hd

lemma pointedFamily_mul (g x : Artin M) (L : FusionLabel m) :
    pointedFamily M f (g*x) L = sourceArtinAction M g (pointedFamily M f x L) := by
  simp only [pointedFamily, pointedAction, map_mul, Equiv.Perm.mul_apply]

lemma pointedMultiplicity_word (w : List (S × Bool)) (k : ℤ) :
    pointedMultiplicity M f (sourceSignedWord M w) k =
      fusionOrbitMultiplicity m d hd diag hm (sourcePacketWord w) (.inl f) k := by
  unfold pointedMultiplicity
  rw [pointedFamily_word, fusionFamilyMultiplicity_orbit]

lemma pointedFamily_weighted_level (z : Artin M) (q : ℤ)
    (α : FusionVertex (V := S ⊕ Unit) m) :
    (∑ H, fusionWeight m H * (classLevelArray Q (pointedFamily M f z H) (α,q) : ℝ)) =
      fusionWeight m α.2 * pointedMultiplicity M f z q α.1 := by
  obtain ⟨w,rfl⟩ := sourceSignedWord_surjective M z
  rw [pointedMultiplicity_word, pointedFamily_word]
  have h := congrFun (fusionOrbitWeightedVector_eq m d hd diag hm (sourcePacketWord w) (.inl f) q) α
  simpa only [fusionOrbitWeightedVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    fusionOrbitLayer_generator, fusionFold] using h

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedCap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
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

lemma pointedMultiplicity_cap_zero (T:Set S) (z:Artin M) (q k:ℤ) (hq:q<k)
    (hz:∀H,ClassCapOn Q (pointedFamily M f z H)
      (Set.range (unfoldedInclusion M T)) q) (s:S) (hs:s∈T) :
    pointedMultiplicity M f z k (.inl s)=0 := by
  let L:=fusionZeroLabel m (fusionLabelSize_ge_two M)
  have hw:=pointedFamily_weighted_level M f z k (.inl s,L)
  have he: (∑H,fusionWeight m H*
      (classLevelArray Q (pointedFamily M f z H) ((.inl s,L),k):ℝ))=0 := by
    apply Finset.sum_eq_zero
    intro H _
    rw [(classCapOn_iff_level_zero Q _ _ _).mp (hz H) _ ⟨(⟨s,hs⟩,L),rfl⟩ k hq]
    simp
  rw [he] at hw
  exact (mul_eq_zero.mp hw.symm).resolve_left (ne_of_gt (fusionWeight_pos m (fusionLabelSize_ge_two M) L))

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedMultiplicityZero
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
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma pointedMultiplicity_zero_iff (z:Artin M) (q:ℤ) (v:S⊕Unit) :
    pointedMultiplicity M f z q v=0 ↔
      ∀ H L,classLevelArray Q (pointedFamily M f z H) ((v,L),q)=0 := by
  constructor
  · intro hz H L
    have he:=pointedFamily_weighted_level M f z q (v,L)
    rw [hz,MulZeroClass.mul_zero] at he
    have hnn:∀ H:FusionLabel m,0≤fusionWeight m H *
        (classLevelArray Q (pointedFamily M f z H) ((v,L),q):ℝ) := by
      intro H
      exact mul_nonneg (fusionWeight_pos m (fusionLabelSize_ge_two M) H).le (Nat.cast_nonneg _)
    have hh:= (Finset.sum_eq_zero_iff_of_nonneg (fun H _=>hnn H)).mp he H (Finset.mem_univ H)
    have hz':(classLevelArray Q (pointedFamily M f z H) ((v,L),q):ℝ)=0 :=
      (mul_eq_zero.mp hh).resolve_left (ne_of_gt (fusionWeight_pos m (fusionLabelSize_ge_two M) H))
    exact_mod_cast hz'
  · intro hz
    let L:=fusionZeroLabel m (fusionLabelSize_ge_two M)
    have he:=pointedFamily_weighted_level M f z q (v,L)
    simp only [hz,Nat.cast_zero,MulZeroClass.mul_zero,Finset.sum_const_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left
      (ne_of_gt (fusionWeight_pos m (fusionLabelSize_ge_two M) L))

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedCosetGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedCosetVector_upper_harmonize {P R:Deligne M} (h:P≤R) (k:ℤ) :
    pointedCosetVector M f R k=harmonicExtension (framedCartan M)
      ((Sum.inl:S→S⊕Unit) '' R.val.1) (pointedCosetVector M f P k) :=
  harmonicExtension_unique _ _ (framed_spherical_posDef M R.val.1 R.property.1) _ _
    (pointedCosetVector_upper_outside M f h k) (pointedCosetVector_harmonic M f R k)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedResidueAllowed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedResidueHeight_strict {P Q:Deligne M} {q:ℤ}
    (h:PointedResidueAllowed M f true P Q q) : pointedResidueHeight M f P Q q<0 := by
  have ht:=deligne_lt_type M h.1
  obtain ⟨i,hi,hn⟩:=Set.exists_of_ssubset ht
  apply Finset.sum_neg' (fun i _=>sub_nonpos.mpr (pointedResidueAllowed_le M f h (.inl i)))
  exact ⟨i,Set.mem_toFinset.mpr hi,sub_neg.mpr (by simpa only [↓reduceIte] using (h.2 i hi hn).2)⟩

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedCosetExteriorCap
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
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma pointedCoset_exterior_cap (P:Deligne M) (x z:Artin M) (hx:x∈P.val.2) (hz:z∈P.val.2)
    (U:Set (FusionVertex (V:=S⊕Unit) m)) (hU:∀α∈U,α.1∉Sum.inl '' P.val.1) (q:ℤ)
    (h:∀H,ClassCapOn Q (pointedFamily M f x H) U q) :
    ∀H,ClassCapOn Q (pointedFamily M f z H) U q := by
  have hg:z*x⁻¹∈artinParabolic M P.val.1 := by
    rw [←sourceCoset_eq M P x hx] at hz
    exact hz
  have he:z=(z*x⁻¹)*x:=by group
  intro H
  rw [he,pointedFamily_mul]
  exact sourceArtinAction_cap_exterior M P.val.1 _ hg _ U hU q (h H)

lemma pointedCoset_exterior_multiplicity (P:Deligne M) (x z:Artin M) (hx:x∈P.val.2) (hz:z∈P.val.2)
    (v:S⊕Unit) (hv:v∉Sum.inl '' P.val.1) (q:ℤ) :
    pointedMultiplicity M f z q v=pointedMultiplicity M f x q v := by
  have hg:z*x⁻¹∈artinParabolic M P.val.1 := by
    rw [←sourceCoset_eq M P x hx] at hz
    exact hz
  have he:z=(z*x⁻¹)*x:=by group
  rw [he]
  exact pointedMultiplicity_exterior_ordered M f P.val.1 _ hg x v hv q

lemma pointedResidue_exterior_cap {strict:Bool} {P X:Deligne M} {q:ℤ}
    (h:PointedResidueAllowed M f strict P X q) (x z:Artin M) (hx:x∈P.val.2) (hz:z∈X.val.2)
    (U:Set (FusionVertex (V:=S⊕Unit) m))
    (hE:∀H,ClassCapOn Q (pointedFamily M f x H) (U\fusionColorRegion m (Sum.inl '' P.val.1)) q) :
    ∀H,ClassCapOn Q (pointedFamily M f z H) (U\fusionColorRegion m (Sum.inl '' X.val.1)) q := by
  have hout:=pointedCoset_exterior_cap M f P x z hx (h.1.le.2 hz)
    (U\fusionColorRegion m (Sum.inl '' P.val.1)) (fun α hα=>hα.2) q hE
  intro H
  rw [classCapOn_iff_level_zero]
  intro α hα k hk
  by_cases hp:α.1∈Sum.inl '' P.val.1
  · obtain ⟨i,hi,hei⟩:=hp
    have hxi:i∉X.val.1:=fun hh=>hα.2 ⟨i,hh,hei⟩
    have hzero:= (h.2 i hi hxi).1 k hk
    rw [pointedCosetVector_open_at M f X z hz _ (by
      rintro ⟨j,hj,hh⟩;exact hxi ((Sum.inl_injective hh) ▸ hj))] at hzero
    change classLevelArray Q (pointedFamily M f z H) ((α.1,α.2),k)=0
    rw [←hei]
    exact (pointedMultiplicity_zero_iff M f z k _).mp hzero H α.2
  · exact (classCapOn_iff_level_zero Q _ _ _).mp (hout H) α ⟨hα.1,hp⟩ k hk

omit [Fintype S] [LinearOrder S] in
/-- Frame avoidance persists throughout a coset whose type avoids the frame. -/
lemma pointedCoset_avoids_frame (P : Deligne M) (x z : Artin M)
    (hx : x ∈ P.val.2) (hz : z ∈ P.val.2) (I : Set S)
    (hPI : P.val.1 ⊆ I) (hf : f ∉ I) (hxA : x ∈ artinParabolic M {f}ᶜ) :
    z ∈ artinParabolic M {f}ᶜ := by
  have hg : z*x⁻¹ ∈ artinParabolic M P.val.1 := by
    rw [←sourceCoset_eq M P x hx] at hz
    exact hz
  have hsub : P.val.1 ⊆ {f}ᶜ := by
    intro i hi he
    exact hf (he ▸ hPI hi)
  have hm := (artinParabolic M {f}ᶜ).mul_mem (artinParabolic_mono M hsub hg) hxA
  simpa only [_root_.mul_assoc, inv_mul_cancel, _root_.mul_one] using hm

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedResidueActive
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedResidueActive_misses {P X:Deligne M} {q:ℤ} (hx:X≤P)
    (hh:pointedResidueHeight M f P X q<0) :
    ∃i∈P.val.1,i∉X.val.1 ∧ i∉pointedResidueActive M f P X q := by
  by_contra hn
  have hv:pointedCosetVector M f P q≤ pointedCosetVector M f X q:=by
    apply pointedCosetVector_upper_antitone_int M f hx q
    intro i hi hxi
    by_contra hr
    exact hn ⟨i,hi,hxi,fun hd=>hr hd.2.2⟩
  have hnon:0≤ pointedResidueHeight M f P X q:=
    Finset.sum_nonneg (fun i _=>sub_nonneg.mpr (hv (.inl i)))
  exact (not_lt_of_ge hnon) hh

lemma pointedResidueUpperTop_mem {P X:Deligne M} {q:ℤ} (hx:X≤P)
    (hh:pointedResidueHeight M f P X q<0) (hd:(pointedResidueActive M f P X q).Nonempty) :
    X<pointedResidueUpperTop M f P X q hx ∧ pointedResidueUpperTop M f P X q hx<P ∧
      pointedResidueHeight M f P (pointedResidueUpperTop M f P X q hx) q≤ pointedResidueHeight M f P X q := by
  have hl:X≤ pointedResidueUpperTop M f P X q hx:=by
    calc
      X=sourceCoset M X.val.1 X.property.1 (sourceCosetRepresentative M X):=
        (sourceCoset_eq M X _ (sourceCosetRepresentative_mem M X)).symm
      _≤ pointedResidueUpperTop M f P X q hx:=sourceCoset_le M Set.subset_union_left _
  have hp:pointedResidueUpperTop M f P X q hx≤P:=by
    calc
      pointedResidueUpperTop M f P X q hx≤ sourceCoset M P.val.1 P.property.1 (sourceCosetRepresentative M X):=
        sourceCoset_le M (fun _ hi=>hi.elim (fun h=>hx.1 h) (fun h=>h.1)) _
      _=P:=sourceCoset_eq M P _ (hx.2 (sourceCosetRepresentative_mem M X))
  refine ⟨lt_of_le_of_ne hl ?_,lt_of_le_of_ne hp ?_,pointedResidueUpper_active M f hl (fun _ hi hn=>hi.resolve_left hn)⟩
  · intro he
    obtain ⟨i,hi⟩:=hd
    have ht:=congrArg (fun K:Deligne M=>K.val.1) he
    have hiTop:i∈(pointedResidueUpperTop M f P X q hx).val.1:=Or.inr hi
    rw [←ht] at hiTop
    exact hi.2.1 hiTop
  · intro he
    obtain ⟨i,hi,hxOut,hdOut⟩:=pointedResidueActive_misses M f hx hh
    have ht:=congrArg (fun K:Deligne M=>K.val.1) he
    have hiTop:i∈(pointedResidueUpperTop M f P X q hx).val.1:=by rw [ht];exact hi
    exact hiTop.elim hxOut hdOut

theorem pointedResidueEarlierUpper_contractible {P X:Deligne M} {q:ℤ} (hx:X≤P)
    (hh:pointedResidueHeight M f P X q<0) (h:Nonempty (PointedResidueEarlierUpper M f P X q)) :
    ContractibleSpace |CategoryTheory.nerve (PointedResidueEarlierUpper M f P X q)| := by
  let R:=Classical.choice h
  obtain ⟨i,_,hi⟩:=pointedResidueUpper_meets M f R.property.1 R.property.2.1.le R.property.2.2
  let c:PointedResidueEarlierUpper M f P X q:=⟨pointedResidueUpperTop M f P X q hx,
    pointedResidueUpperTop_mem M f hx hh ⟨i,hi⟩⟩
  exact nerve_contractible_of_order_clip (pointedResidueUpperRetraction M f P X q) c
    (by intro R; change pointedResidueUpperClip M f P X R q≤R.val
        exact pointedResidueUpperClip_le M f R.property.1.le)
    (fun R=>show pointedResidueUpperClip M f P X R q≤ pointedResidueUpperTop M f P X q hx from
      sourceCoset_le M Set.inter_subset_right _)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedRows
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedCosetVector_eq_of_upper_rows {P R:Deligne M} (h:P≤R) (k:ℤ)
    (hr:∀i∈R.val.1,i∉P.val.1→(framedCartan M *ᵥ pointedCosetVector M f P k) (.inl i)=0) :
    pointedCosetVector M f R k=pointedCosetVector M f P k := by
  rw [pointedCosetVector_upper_harmonize M f h k]
  symm
  apply harmonicExtension_unique (framedCartan M)
    ((Sum.inl:S→S⊕Unit) '' R.val.1) (framed_spherical_posDef M R.val.1 R.property.1)
    (pointedCosetVector M f P k) (pointedCosetVector M f P k)
  · intro _ _; rfl
  · rintro ⟨_,⟨i,hi,rfl⟩⟩
    by_cases ht:i∈P.val.1
    · exact pointedCosetVector_harmonic M f P k ⟨.inl i,⟨i,ht,rfl⟩⟩
    · exact hr i hi ht

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativePeaks
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Last occupied levels and lower-edge harmonic comparisons for the pointed family. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S) (cutoff:ℤ)

lemma relativePeak_positive (P:Deligne M) (i:S)
    (hi : ∃ k, 0 < pointedProfile M f P cutoff k (.inl i)) :
    0 < pointedProfile M f P cutoff (relativePeak M f cutoff P i) (.inl i) := by
  obtain ⟨k,hk⟩ := hi
  have hn := relativePeak_nonzero M f cutoff P i
    ⟨k,(relativePeakSupport_mem M f cutoff P i k).mpr (ne_of_gt hk)⟩
  exact lt_of_le_of_ne (pointedCosetVector_nonneg M f P _ _) (Ne.symm hn)


end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedTypeComponent
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Peaks and signs on connected components of a spherical closed type. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

lemma pointedProfile_positive_neighbor (P:Deligne M) (k:ℕ) (i:S) (hi:i∈P.val.1)
    (j:S ⊕ Unit) (hij:framedCartan M (.inl i) j<0)
    (hj:0<pointedProfile M f P cutoff k j) : 0<pointedProfile M f P cutoff k (.inl i) := by
  apply harmonic_positive_neighbor_at (framedCartan M) (framedCartan_off M)
    _ (pointedCosetVector_nonneg M f P (cutoff+k)) _ hij hj
  exact (pointedCosetVector_harmonic M f P (cutoff+k) ⟨.inl i,⟨i,hi,rfl⟩⟩).ge

lemma relativePeak_neighbor (P:Deligne M) (i j:S) (hi:i∈P.val.1) (hj:j∈P.val.1)
    (hij:framedCartan M (.inl i) (.inl j)<0) :
    relativePeak M f cutoff P i = relativePeak M f cutoff P j := by
  have he : relativePeakSupport M f cutoff P i = relativePeakSupport M f cutoff P j := by
    ext k
    rw [relativePeakSupport_mem,relativePeakSupport_mem]
    constructor
    · intro hn
      exact ne_of_gt (pointedProfile_positive_neighbor M f cutoff P k j hj (.inl i)
        (by rwa [framedCartan_symm])
        (lt_of_le_of_ne (pointedCosetVector_nonneg M f P _ _) (Ne.symm hn)))
    · intro hn
      exact ne_of_gt (pointedProfile_positive_neighbor M f cutoff P k i hi (.inl j) hij
        (lt_of_le_of_ne (pointedCosetVector_nonneg M f P _ _) (Ne.symm hn)))
  exact congrArg (fun F:Finset ℕ => F.sup id) he

lemma pointedTypeComponent_peak (P:Deligne M) (i:S) (hi:i∈P.val.1)
    (j:S) (hj:j∈sourceTypeComponent M P i hi) :
    relativePeak M f cutoff P j = relativePeak M f cutoff P i := by
  obtain ⟨hj,h⟩ := hj
  have hgen : ∀ a:P.val.1, Relation.ReflTransGen
      (fun a b:P.val.1 => framedCartan M (.inl a.val) (.inl b.val)<0) ⟨i,hi⟩ a →
      relativePeak M f cutoff P a = relativePeak M f cutoff P i := by
    intro a ha
    induction ha with
    | refl => rfl
    | @tail b c _ hbc ih =>
      exact (relativePeak_neighbor M f cutoff P c b c.property b.property
        (by rwa [framedCartan_symm])).trans ih
  exact hgen ⟨j,hj⟩ h

lemma pointedTypeComponent_positive (P:Deligne M) (i:S) (hi:i∈P.val.1) (k:ℕ)
    (hp:0<pointedProfile M f P cutoff k (.inl i))
    (j:S) (hj:j∈sourceTypeComponent M P i hi) :
    0<pointedProfile M f P cutoff k (.inl j) := by
  obtain ⟨hj,h⟩ := hj
  have hgen : ∀ a:P.val.1, Relation.ReflTransGen
      (fun a b:P.val.1 => framedCartan M (.inl a.val) (.inl b.val)<0) ⟨i,hi⟩ a →
      0<pointedProfile M f P cutoff k (.inl a.val) := by
    intro a ha
    induction ha with
    | refl => exact hp
    | @tail b c _ hbc ih =>
      exact pointedProfile_positive_neighbor M f cutoff P k c c.property (.inl b)
        (by rwa [framedCartan_symm]) ih
  exact hgen ⟨j,hj⟩ h

lemma pointedTypeComponent_positiveComponent (P:Deligne M) (i:S) (hi:i∈P.val.1) (k:ℕ)
    (hp:0<pointedProfile M f P cutoff k (.inl i))
    (j:S) (hj:j∈sourceTypeComponent M P i hi) :
    sourcePositiveComponent M (pointedProfile M f P cutoff k) (.inl j) =
      sourcePositiveComponent M (pointedProfile M f P cutoff k) (.inl i) := by
  apply sourcePositiveComponent_eq M _ _ _ (sourcePositiveComponent_spec M _ _ hp)
  obtain ⟨hj,h⟩ := hj
  have hgen : ∀ a:P.val.1, Relation.ReflTransGen
      (fun a b:P.val.1 => framedCartan M (.inl a.val) (.inl b.val)<0) ⟨i,hi⟩ a →
      (.inl a.val:S ⊕ Unit) ∈ sourcePositiveComponent M (pointedProfile M f P cutoff k) (.inl i) := by
    intro a ha
    induction ha with
    | refl => exact .refl
    | @tail b c hb hbc ih =>
      exact ih.tail ⟨pointedTypeComponent_positive M f cutoff P i hi k hp b ⟨b.property,hb⟩,
        hbc,pointedTypeComponent_positive M f cutoff P i hi k hp c ⟨c.property,hb.tail hbc⟩⟩
  exact hgen ⟨j,hj⟩ h

omit [LinearOrder S] in
lemma relativePositiveSign_component_iff (p:ℕ →₀ (S ⊕ Unit → ℝ)) (k:ℕ) (i:S ⊕ Unit)
    (hp:0<p k i) :
    relativePositiveSign (framedCartan M) U p k i ↔
      sourcePositiveComponent M (p k) i ⊆ U ∧
      (∀ j ∈ sourcePositiveComponent M (p k) i, (framedCartan M *ᵥ p k) j = 0) ∧
      ∀ d, k<d → ∀ j, (j ∈ sourcePositiveComponent M (p k) i ∨
        ∃ a ∈ sourcePositiveComponent M (p k) i, framedCartan M a j<0) → p d j=0 := by
  constructor
  · rintro ⟨I,hi,hU,hI,hr,hh⟩
    have he := sourcePositiveComponent_eq M (p k) i I hI hi
    simpa only [he] using And.intro hU (And.intro hr hh)
  · rintro ⟨hU,hr,hh⟩
    exact ⟨_,.refl,hU,sourcePositiveComponent_spec M _ _ hp,hr,hh⟩

lemma pointedTypeComponent_sign (P:Deligne M) (i:S) (hi:i∈P.val.1) (k:ℕ)
    (hp:0<pointedProfile M f P cutoff k (.inl i))
    (j:S) (hj:j∈sourceTypeComponent M P i hi) :
    relativeSign M U (pointedProfile M f P cutoff) k (.inl j) =
      relativeSign M U (pointedProfile M f P cutoff) k (.inl i) := by
  have hjp := pointedTypeComponent_positive M f cutoff P i hi k hp j hj
  have he := pointedTypeComponent_positiveComponent M f cutoff P i hi k hp j hj
  have hs : relativePositiveSign (framedCartan M) U (pointedProfile M f P cutoff) k (.inl j) ↔
      relativePositiveSign (framedCartan M) U (pointedProfile M f P cutoff) k (.inl i) := by
    rw [relativePositiveSign_component_iff M U _ _ _ hjp,
      relativePositiveSign_component_iff M U _ _ _ hp,he]
  simp only [relativeSign,ne_of_gt hp,ne_of_gt hjp,↓reduceIte,hs]

lemma pointedBlock_above_boundary (P:Deligne M) (B:Set S) (hB:B⊆P.val.1) (q:ℕ)
    (hq:∀i∈B,relativePeak M f cutoff P i=q) (v:S ⊕ Unit)
    (hv:∃i∈B,framedCartan M (.inl i) v<0) (d:ℕ) (hd:q<d) :
    pointedProfile M f P cutoff d v=0 := by
  obtain ⟨i,hi,hiv⟩ := hv
  by_contra hn
  have hp := pointedProfile_positive_neighbor M f cutoff P d i (hB hi) v hiv
    (lt_of_le_of_ne (pointedCosetVector_nonneg M f P _ _) (Ne.symm hn))
  exact (ne_of_gt hp) (relativePeak_above M f cutoff P i (by rwa [hq i hi]))

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedBlockBoundary
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary caps for commuting closed components at any integer cutoff. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S) (cutoff:ℤ)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma pointedBlock_boundary_cap (P:Deligne M) (B:Set S) (hB:B⊆P.val.1)
    (hc:∀i∈B,∀j∈P.val.1\B,M i j=2) (q:ℕ) (hq:∀i∈B,relativePeak M f cutoff P i=q)
    (x:Artin M) (hx:x∈P.val.2) :
    ∀H,ClassCapOn Q (pointedFamily M f x H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M B))\Set.range (unfoldedInclusion M B)) (cutoff+q) := by
  intro H
  rw [classCapOn_iff_level_zero]
  intro α hα k hk
  have ha:α∈closedNeighborhood Q (fusionColorRegion m (Sum.inl '' B)):=by
    simpa only [unfoldedInclusion_range] using hα.1
  have ho':α∉fusionColorRegion m (Sum.inl '' B):=by simpa only [unfoldedInclusion_range] using hα.2
  have ho:α.1∉Sum.inl '' B:=ho'
  have hv:=sourceNeighborhood_project M (Sum.inl '' B) ha
  have hout:=sourceBlock_boundary_outside M P B hB hc α.1 hv ho
  have hnb:∃i∈B,framedCartan M (.inl i) α.1<0:=by
    rcases hv with hv|⟨u,hu,huv⟩
    · exact (ho hv).elim
    · obtain ⟨i,hi,rfl⟩:=hu
      exact ⟨i,hi,by rwa [framedCartan_symm]⟩
  have hn : 0 ≤ k-cutoff := by omega
  have he : cutoff+((k-cutoff).toNat:ℤ)=k := by rw [Int.toNat_of_nonneg hn];omega
  have hz:=pointedBlock_above_boundary M f cutoff P B hB q hq α.1 hnb (k-cutoff).toNat (by omega)
  change pointedCosetVector M f P (cutoff+(k-cutoff).toNat) α.1=0 at hz
  rw [he,pointedCosetVector_open_at M f P x hx α.1 hout k] at hz
  exact (pointedMultiplicity_zero_iff M f x k α.1).mp hz H α.2

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedCandidate
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

lemma pointedCandidate_capped (T J:Set S) (hT:IsSpherical M T) (z:Artin M) (q:ℤ)
    (X:PointedCandidate M f T J z q) :
    ∃a∈artinParabolic M J,
      PointedCappedCandidate M f T J (a*z) q (pointedHarmonicAt M f J z q) := by
  have hJ:=source_spherical_mono M X.proper.subset hT
  obtain ⟨a,ha,hcap⟩:=source_finiteFamily_cap_accessible M J hJ (pointedFamily M f z) q
    (by intro H i hi; exact X.cap H i ⟨closedNeighborhood_mono Q
      (unfoldedInclusion_range_mono M X.proper.subset) hi.1,hi.2⟩)
  have hc:∀H,ClassCapOn Q (pointedFamily M f (a*z) H) (closedNeighborhood Q (U T)) q := by
    intro H
    dsimp only
    rw [unfoldedInclusion_range M T]
    apply source_cap_closed_of_cap_parts M T J X.proper.subset _ q
    · rw [pointedFamily_mul]; exact hcap H
    · rw [pointedFamily_mul]
      apply sourceArtinAction_cap_exterior M J a ha _ _ (fun _ membership=>membership.2) q
      simpa only [unfoldedInclusion_range M T,unfoldedInclusion_range M J] using X.cap H
  have hC : fusionFoldedCartan m (coxeterFusionEdge M) = framedCartan M := by
    convert fusionFoldedCartan_eq_framedCartan M using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    exact Subsingleton.elim _ _
  refine ⟨a,ha,X.proper.subset,hJ,hc,?_,?_,?_,?_⟩
  · intro j
    rw [hC]
    exact pointedHarmonicAt_harmonic M f J hJ z q ⟨.inl (j:S),⟨j,j.property,rfl⟩⟩
  · intro v hv
    rw [pointedMultiplicity_exterior_ordered M f J a ha z v hv q,pointedHarmonicAt_outside M f J z q v hv]
  · rw [hC]
    exact X.negative
  · intro b hb hbc j
    apply X.representatives (b*(a*z)) _ hbc j
    change b*(a*z)*z⁻¹∈artinParabolic M J
    simpa only [mul_assoc,mul_inv_cancel,mul_one] using (artinParabolic M J).mul_mem hb ha

theorem pointedCandidate_unique (T J J':Set S) (hT:IsSpherical M T)
    (z h:Artin M) (hh:h∈artinParabolic M T) (q:ℤ)
    (X:PointedCandidate M f T J z q) (Y:PointedCandidate M f T J' (h*z) q) :
    J=J' ∧ rightCoset M J z=rightCoset M J' (h*z) := by
  obtain ⟨a,ha,hX⟩:=pointedCandidate_capped M f T J hT z q X
  obtain ⟨b,hb,hY⟩:=pointedCandidate_capped M f T J' hT (h*z) q Y
  let k:=b*h*a⁻¹
  have hk:k∈artinParabolic M T := (artinParabolic M T).mul_mem
    ((artinParabolic M T).mul_mem (artinParabolic_mono M Y.proper.subset hb) hh)
    ((artinParabolic M T).inv_mem (artinParabolic_mono M X.proper.subset ha))
  have he:k*(a*z)=b*(h*z) := by dsimp [k]; group
  have hY':PointedCappedCandidate M f T J' (k*(a*z)) q (pointedHarmonicAt M f J' (h*z) q) := by
    rw [he]; exact hY
  obtain ⟨_,hj,hkJ⟩:=pointedCandidate_comparison_parabolic_s236 M f T J J' hT (a*z) k hk q _ _ hX hY'
  subst J'
  have heh:h=b⁻¹*k*a := by dsimp [k]; group
  have hhJ:h∈artinParabolic M J := by
    rw [heh]
    exact (artinParabolic M J).mul_mem ((artinParabolic M J).mul_mem
      ((artinParabolic M J).inv_mem hb) hkJ) ha
  exact ⟨rfl,(rightCoset_mul_eq M J h z hhJ).symm⟩

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedCosetProduct
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointed multiplicities on products of commuting standard cosets. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedCosetVector_block (B C:Set S) (hT:IsSpherical M (B∪C))
    (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) (k:ℤ) (i:S) (hi:i∈B) :
    pointedCosetVector M f (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) k (.inl i)=
      pointedCosetVector M f (sourceCoset M (B∪C) hT x) k (.inl i) := by
  let P:=sourceCoset M (B∪C) hT x
  let R:=sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x
  apply harmonic_block_eq (framedCartan M) (Sum.inl '' B) (Sum.inl '' C)
    (framed_spherical_posDef M B (source_spherical_mono M Set.subset_union_left hT))
    (pointedCosetVector M f R k) (pointedCosetVector M f P k)
    (pointedCosetVector_harmonic M f R k)
    (fun j=>pointedCosetVector_harmonic M f P k ⟨j,Set.image_mono Set.subset_union_left j.property⟩)
    ?_ ?_ (.inl i) ⟨i,hi,rfl⟩
  · rintro _ ⟨s,hs,rfl⟩ _ ⟨t,ht,rfl⟩
    exact sourceCartan_commuting_zero M s t (hc s hs t ht)
  · intro j hjB hjC
    rw [pointedCosetVector_open_at M f R x (rightCoset_self M B x) j hjB k,
      pointedCosetVector_open_at M f P x (rightCoset_self M (B∪C) x) j (by
        rintro ⟨s,hs,rfl⟩
        rcases hs with hs|hs
        · exact hjB ⟨s,hs,rfl⟩
        · exact hjC ⟨s,hs,rfl⟩) k]


end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeNullLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The relative null-layer obstruction at every integer level

This is the version of Proposition 5.1 of paper 082-03 needed for a
relative frame. It uses connected support, cap accessibility and finite
spherical socle saturation. It does not require the frame to be adjacent
to every operated color, or the isolated level to be positive.
-/

namespace HarmonicArtin.ParabolicIntersections

open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open scoped _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "diag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e => le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd diag
local notation "μ" => fusionOrbitMultiplicity m d hd diag hm
local notation "C" => fusionFoldedCartan m d
local notation "aw" => sourceArtinAction M (K := ℂ)

/-- Relative null-layer obstruction, with no restriction on the sign of
`q`. All the inputs concern concrete layer counts and spherical caps. -/
theorem relative_null_layer (I J : Set S) (hI : I.Nonempty)
    (hJI : J ⊆ I) (hJ : IsSpherical M J)
    (z₀ : List ((S ⊕ Unit) × Bool)) (s : S ⊕ Unit)
    (hs : s ∉ Sum.inl '' I) (hw : ∀ a ∈ z₀, a.1 ≠ s) (q : ℤ)
    (c : S ⊕ Unit → ℝ) (hc : ∀ v, 0 ≤ c v)
    (hcSupp : ∀ v, v ∉ Sum.inl '' I → c v = 0)
    (hcPos : ∀ v, v ∈ Sum.inl '' I → 0 < c v)
    (hcNull : ∀ v, v ∈ Sum.inl '' I → (C *ᵥ c) v = 0)
    (hE : ∀ L, ClassCapOn Q (O z₀ s L)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
        fusionColorRegion m (Sum.inl '' J)) q)
    (hdata : ∀ v, (v ∈ Sum.inl '' I ∧ v ∉ Sum.inl '' J) ∨
      (v ∉ Sum.inl '' I ∧ ∃ u ∈ Sum.inl '' I, C v u < 0) → μ z₀ s q v = c v)
    (huniv : ∀ g ∈ artinParabolic M J,
      (∀ L, ClassCapOn Q (aw g (O z₀ s L))
        (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I))) q) →
      ∀ j : J, c (.inl (j : S)) < fusionFamilyMultiplicity m d hd hm
        (fun L => aw g (O z₀ s L)) q (.inl (j : S))) : False := by
  have hstrict : ∀ g ∈ artinParabolic M J,
      (∀ L, ClassCapOn Q (aw g (O z₀ s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) →
      ∀ j : J, c (.inl (j : S)) < fusionFamilyMultiplicity m d hd hm
        (fun L => aw g (O z₀ s L)) q (.inl (j : S)) := by
    intro g hg hcap
    apply huniv g hg
    intro L
    apply source_cap_closed_of_cap_parts M I J hJI _ q (hcap L)
    exact sourceArtinAction_cap_exterior M J g hg (O z₀ s L) _
      (fun _ h => h.2) q (hE L)
  let D := isolatedDataOfCoset M I J hJI hJ z₀ s q c hc hcSupp hcPos hcNull hdata hstrict
  obtain ⟨zcap, hzcap, hcap⟩ := sourceCosetOrbit_exists_cap M I J hJI hJ z₀ s q hE
  obtain ⟨g, hg, hge⟩ := hzcap
  obtain ⟨w, hwt, hwe⟩ := artinParabolic_signed_word M J g hg
  let z := sourcePacketWord w ++ z₀
  have he (L : FusionLabel m) : O z s L = O zcap s L := by
    rw [hge L, ← hwe]
    exact sourcePacketOrbit_signedPrepend M w z₀ s L
  have hz : D.valid z := by
    refine ⟨g, hg, fun L => ?_⟩
    exact (he L).trans (hge L)
  have hcz' (L : FusionLabel m) : ClassCapOn Q (O z s L)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I))) q := by
    rw [he L]
    exact hcap L
  have hcz : D.capped z := hcz' 
  have hwz : ∀ a ∈ z, a.1 ≠ s := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      intro heq
      exact hs ⟨b.1, hJI (hwt b hb), heq⟩
    · exact hw a ha
  obtain ⟨i, hi⟩ := hI
  have hipos : 0 < μ z s q (.inl i) := by
    have hci := hcPos (.inl i) ⟨i, hi, rfl⟩
    by_cases hij : i ∈ J
    · have h := D.strict z hz 1 (artinParabolic M J).one_mem
        (by intro L; simpa only [map_one, Equiv.Perm.one_apply] using D.capJ z hcz L) ⟨i, hij⟩
      simp only [map_one, Equiv.Perm.one_apply, fusionFamilyMultiplicity_orbit] at h
      exact lt_trans hci h
    · have hiq := D.data z hz (.inl i) (Or.inl ⟨⟨i, hi, rfl⟩, by
        rintro ⟨j, hj, hej⟩; exact hij (Sum.inl.inj hej ▸ hj)⟩)
      change μ z s q (.inl i) = c (.inl i) at hiq
      rw [hiq]
      exact hci
  obtain ⟨L, b, hb, _⟩ := orbit_generator_of_positive m d hd diag hm z s (.inl i) q hipos
  have hbin : ((fusionOrbitModel m d hd diag z s L).complex.placement b).color.1 ∈
      Sum.inl '' I := hb.symm ▸ ⟨i, hi, rfl⟩
  obtain ⟨k, v, hk, hv, hinc, hp⟩ := orbit_boundary_below m d hd diag hm z s hwz
    (Sum.inl '' I) hs q L b hbin
    (fun H => ClassCapOn.mono Q (hcz' H) (by
      rintro α ⟨_, a, ha, ht⟩
      exact Or.inr ⟨(Q).source a, ha, a, rfl, ht⟩))
    (by
      intro v hv hinc
      have hh := D.data z hz v (Or.inr ⟨hv, hinc⟩)
      change μ z s q v = c v at hh
      exact hh.trans (hcSupp v hv))
  have hvJ : v ∉ Sum.inl '' J := fun h => hv (Set.image_mono hJI h)
  apply null_boundary_contradiction_s236 D k hk v hv hinc _ z hz hcz
  intro z' hz'
  have heq : μ z' s k v = μ z s k v := by
    rw [sourceCosetOrbit_multiplicity_exterior M J z₀ s z' hz' v hvJ k,
      sourceCosetOrbit_multiplicity_exterior M J z₀ s z hz v hvJ k]
  change 0 < μ z' s k v
  rw [heq]
  exact hp

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedNullObstruction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The relative null obstruction for actual group elements avoiding the frame. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "diag" => coxeterFusionEdge_diag M
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd diag

/-- Proposition 5.1 of 082-03, expressed using the pointed group orbit.
The avoidance hypothesis is automatic in the relative enlarged diagram. -/
theorem pointed_null_obstruction (I J : Set S) (hI : I.Nonempty) (hf : f ∉ I)
    (hJI : J ⊆ I) (hJ : IsSpherical M J) (x : Artin M)
    (hx : x ∈ artinParabolic M {f}ᶜ) (q : ℤ)
    (c : S ⊕ Unit → ℝ) (hc : ∀ v, 0 ≤ c v)
    (hcSupp : ∀ v, v ∉ Sum.inl '' I → c v = 0)
    (hcPos : ∀ v, v ∈ Sum.inl '' I → 0 < c v)
    (hcNull : ∀ v, v ∈ Sum.inl '' I → (framedCartan M *ᵥ c) v = 0)
    (hE : ∀ L, ClassCapOn Q (pointedFamily M f x L)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
        fusionColorRegion m (Sum.inl '' J)) q)
    (hdata : ∀ v, (v ∈ Sum.inl '' I ∧ v ∉ Sum.inl '' J) ∨
      (v ∉ Sum.inl '' I ∧ ∃ u ∈ Sum.inl '' I, framedCartan M v u < 0) →
        pointedMultiplicity M f x q v = c v)
    (huniv : ∀ g ∈ artinParabolic M J,
      (∀ L, ClassCapOn Q (pointedFamily M f (g*x) L)
        (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I))) q) →
      ∀ j : J, c (.inl (j:S)) < pointedMultiplicity M f (g*x) q (.inl (j:S))) : False := by
  obtain ⟨w, hw, rfl⟩ := artinParabolic_signed_word M {f}ᶜ x hx
  have hC : fusionFoldedCartan m d = framedCartan M := by
    convert fusionFoldedCartan_eq_framedCartan M using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    exact Subsingleton.elim _ _
  apply relative_null_layer M I J hI hJI hJ (sourcePacketWord w) (.inl f)
    (by rintro ⟨i, hi, he⟩; exact hf (Sum.inl.inj he ▸ hi))
    (by
      intro a ha he
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact hw b hb (Sum.inl.inj he)) q c hc hcSupp hcPos
    (by simpa only [hC] using hcNull)
    (by simpa only [pointedFamily_word] using hE)
    (by simpa only [pointedMultiplicity_word, hC] using hdata)
  intro g hg hcap j
  have he : pointedFamily M f (g * sourceSignedWord M w) =
      fun L => sourceArtinAction M g (O (sourcePacketWord w) (.inl f) L) := by
    funext L
    rw [pointedFamily_mul, pointedFamily_word]
  have h := huniv g hg (by simpa only [he] using hcap) j
  simpa only [pointedMultiplicity, he] using h

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedNullPatch
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma pointedCosetVector_of_null_patch (P:Deligne M) (x:Artin M) (hx:x∈P.val.2)
    (I:Set S) (hPI:P.val.1⊆I) (q:ℤ) (c:S⊕Unit→ℝ)
    (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→
      pointedMultiplicity M f x q v=c v) (i:S) (hi:i∈P.val.1) :
    pointedCosetVector M f P q (.inl i)=c (.inl i) := by
  let p:S⊕Unit→ℝ:=fun v=>if v∈Sum.inl '' P.val.1 then c v else pointedMultiplicity M f x q v
  have hp:p=pointedHarmonicAt M f P.val.1 x q := by
    apply harmonicExtension_unique _ _ (framed_spherical_posDef M _ P.property.1)
    · intro v hv
      exact ite_eq_right hv
    · intro j
      exact null_patch (framedCartan_symm M) (framedCartan_off M)
        (Sum.inl '' I) (Sum.inl '' P.val.1) (Set.image_mono hPI) c
        (pointedMultiplicity M f x q) hcNull hdata j j.property
  rw [pointedCosetVector_eq M f P x hx q,←hp]
  exact ite_eq_left ⟨i,hi,rfl⟩

theorem pointedClosedResidue_nonempty (P:Deligne M) (x:Artin M) (hx:x∈P.val.2) (hxA:x∈artinParabolic M {f}ᶜ)
    (I:Set S) (hI:I.Nonempty) (hf:f∉I) (hPI:P.val.1⊆I) (q:ℤ)
    (c:S⊕Unit→ℝ) (hc:∀v,0 ≤ c v) (hcSupp:∀v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀v,v∈Sum.inl '' I→0 < c v)
    (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hE:∀H,ClassCapOn Q (pointedFamily M f x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
        fusionColorRegion m (Sum.inl '' P.val.1)) q)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→
      pointedMultiplicity M f x q v=c v) : Nonempty (PointedResidue M f false P q) := by
  by_contra hempty
  apply pointed_null_obstruction M f I P.val.1 hI hf hPI P.property.1 x hxA q
    c hc hcSupp hcPos hcNull hE hdata
  intro g hg hcap j
  by_contra hn
  have hj:pointedMultiplicity M f (g*x) q (.inl (j:S)) ≤ c (.inl (j:S)):=le_of_not_gt hn
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
  have hvec(k:ℤ)(i:S)(hi:i∉T):pointedCosetVector M f R k (.inl i)=pointedMultiplicity M f z k (.inl i) := by
    rw [pointedCosetVector_eq M f R z hrz k]
    exact pointedHarmonicAt_outside M f T z k _ (by
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
    rw [hvec k j hnT,pointedMultiplicity_zero_iff]
    intro H L
    exact (classCapOn_iff_level_zero Q _ _ _).mp (hcap H) ((.inl (j:S)),L)
      (mem_closedNeighborhood Q ⟨j,hPI j.property,rfl⟩) k hk
  · change pointedCosetVector M f R q (.inl (j:S))≤ pointedCosetVector M f P q (.inl (j:S))
    rw [hvec q j hnT,pointedCosetVector_of_null_patch M f P x hx I hPI q c hcNull hdata j j.property]
    exact hj

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedResidueSingleOpen
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedResidue_single_open {strict:Bool} (P:Deligne M) (z:Artin M) (hz:z∈P.val.2)
    (q:ℤ) (j:S) (hj:j∈P.val.1)
    (hcap:∀k:ℤ,q<k→pointedMultiplicity M f z k (.inl j)=0)
    (hbound:if strict then pointedMultiplicity M f z q (.inl j)<pointedCosetVector M f P q (.inl j)
      else pointedMultiplicity M f z q (.inl j)≤ pointedCosetVector M f P q (.inl j)) :
    Nonempty (PointedResidue M f strict P q) := by
  let T:=P.val.1\{j}
  have ht:T⊆P.val.1:=Set.sdiff_subset
  let R:=sourceCoset M T (source_spherical_mono M ht P.property.1) z
  have hr:R≤P := by
    rw [←sourceCoset_eq M P z hz]
    exact sourceCoset_le M ht z
  have hrlt:R<P := by
    apply lt_of_le_of_ne hr
    intro he
    have he':T=P.val.1:=congrArg (fun A:Deligne M=>A.val.1) he
    have hm:j∈T:=by rw [he'];exact hj
    exact hm.2 rfl
  have hrz:z∈R.val.2:=rightCoset_self M T z
  refine ⟨R,hrlt,?_⟩
  intro i hi hn
  have hei:i=j := by
    by_contra hne
    exact hn ⟨hi,hne⟩
  subst i
  have hvec(k:ℤ):pointedCosetVector M f R k (.inl j)=pointedMultiplicity M f z k (.inl j):=
    pointedCosetVector_open_at M f R z hrz _ (by
      rintro ⟨i,hi,he⟩;exact hn ((Sum.inl_injective he) ▸ hi)) k
  simpa only [hvec] using And.intro hcap hbound

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedResidueActiveEmpty
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.sourceCosetProfile_apply
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
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

lemma pointedResidue_pointed_active_empty {P X:Deligne M} {q:ℤ} (hx:X≤P)
    (hh:pointedResidueHeight M f P X q<0)
    (hu:¬Nonempty (PointedResidueEarlierUpper M f P X q)) :
    pointedResidueActive M f P X q=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro i hi
  apply hu
  exact ⟨pointedResidueUpperTop M f P X q hx,pointedResidueUpperTop_mem M f hx hh ⟨i,hi⟩⟩

lemma pointedResidue_pointed_candidate {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:PointedResidueAllowed M f strict P X q) (x:Artin M) (hx:x∈P.val.2)
    (hboundary:∀H,ClassCapOn Q (pointedFamily M f x H)
      (closedNeighborhood Q (U P.val.1)\U P.val.1) q)
    (hh:pointedResidueHeight M f P X q<0)
    (hu:¬Nonempty (PointedResidueEarlierUpper M f P X q))
    (hl:¬Nonempty (PointedResidue M f true X q)) :
    PointedCandidate M f P.val.1 X.val.1 (sourceCosetRepresentative M X) q := by
  have ha:=pointedResidue_pointed_active_empty M f hX.1.le hh hu
  let z:=sourceCosetRepresentative M X
  have hz:=sourceCosetRepresentative_mem M X
  refine ⟨deligne_lt_type M hX.1,?_,?_,?_⟩
  · have he:=pointedResidue_exterior_cap M f hX x z hx hz (closedNeighborhood Q (U P.val.1))
      (by simpa only [←unfoldedInclusion_range] using hboundary)
    simpa only [←unfoldedInclusion_range] using he
  · intro i hi hn
    change (framedCartan M *ᵥ pointedCosetVector M f X q) (.inl i)<0
    by_contra hr
    have hm:i∈pointedResidueActive M f P X q:=⟨hi,hn,le_of_not_gt hr⟩
    rw [ha] at hm
    exact hm
  · intro y hy hcap j
    have hy':y∈X.val.2:=by rw [sourceCosetRepresentative_spec];exact hy
    change pointedCosetVector M f X q (.inl (j:S))≤ pointedMultiplicity M f y q (.inl (j:S))
    by_contra hn
    apply hl
    apply pointedResidue_single_open M f X y hy' q j j.property
    · intro k hk
      exact pointedMultiplicity_cap_zero M f P.val.1 y q k hk hcap j (hX.1.le.1 j.property)
    · exact lt_of_not_ge hn

theorem pointedResidue_negative_pointeds_unique {strict:Bool} {P X Y:Deligne M} {q:ℤ}
    (hX:PointedResidueAllowed M f strict P X q) (hY:PointedResidueAllowed M f strict P Y q)
    (x:Artin M) (hx:x∈P.val.2)
    (hboundary:∀H,ClassCapOn Q (pointedFamily M f x H)
      (closedNeighborhood Q (U P.val.1)\U P.val.1) q)
    (hhX:pointedResidueHeight M f P X q<0) (hhY:pointedResidueHeight M f P Y q<0)
    (huX:¬Nonempty (PointedResidueEarlierUpper M f P X q))
    (huY:¬Nonempty (PointedResidueEarlierUpper M f P Y q))
    (hlX:¬Nonempty (PointedResidue M f true X q))
    (hlY:¬Nonempty (PointedResidue M f true Y q)) : X=Y := by
  let z:=sourceCosetRepresentative M X
  let w:=sourceCosetRepresentative M Y
  let g:=w*z⁻¹
  have hz:z∈P.val.2:=hX.1.le.2 (sourceCosetRepresentative_mem M X)
  have hw:w∈P.val.2:=hY.1.le.2 (sourceCosetRepresentative_mem M Y)
  have hg:g∈artinParabolic M P.val.1:=by
    rw [←sourceCoset_eq M P z hz] at hw
    exact hw
  have he:g*z=w:=by dsimp [g];group
  have hcX:=pointedResidue_pointed_candidate M f hX x hx hboundary hhX huX hlX
  have hcY:=pointedResidue_pointed_candidate M f hY x hx hboundary hhY huY hlY
  obtain ⟨ht,hc⟩:=pointedCandidate_unique M f P.val.1 X.val.1 Y.val.1 P.property.1 z g hg q hcX
    (by simpa only [he] using hcY)
  apply Subtype.ext
  apply Prod.ext ht
  rw [sourceCosetRepresentative_spec,sourceCosetRepresentative_spec]
  simpa only [he] using hc

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedResidueHeightZero
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
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma pointedResidue_zero_exterior {P X:Deligne M} {q:ℤ}
    (h:PointedResidueAllowed M f false P X q) (hh:pointedResidueHeight M f P X q=0)
    (x z:Artin M) (hx:x∈P.val.2) (hz:z∈X.val.2) (I:Set S) (hPI:P.val.1⊆I)
    (c:S⊕Unit→ℝ) (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→pointedMultiplicity M f x q v=c v) :
    ∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' X.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→pointedMultiplicity M f z q v=c v := by
  intro v hv
  by_cases hp:v∈Sum.inl '' P.val.1
  · obtain ⟨i,hi,rfl⟩:=hp
    have hn:(Sum.inl i:S⊕Unit)∉Sum.inl '' X.val.1:=by
      rcases hv with hv|hv
      · exact hv.2
      · exact False.elim (hv.1 ⟨i,hPI hi,rfl⟩)
    rw [←pointedCosetVector_open_at M f X z hz _ hn q,pointedResidueHeight_zero_vector M f h hh]
    exact pointedCosetVector_of_null_patch M f P x hx I hPI q c hcNull hdata i hi
  · rw [pointedCoset_exterior_multiplicity M f P x z hx (h.1.le.2 hz) v hp q]
    apply hdata v
    rcases hv with hv|hv
    · exact Or.inl ⟨hv.1,hp⟩
    · exact Or.inr hv

theorem pointedResidue_zero_ne_lower (P X:Deligne M) (x:Artin M) (hx:x∈P.val.2) (hxA:x∈artinParabolic M {f}ᶜ)
    (I:Set S) (hI:I.Nonempty) (hf:f∉I) (hPI:P.val.1⊆I) (q:ℤ)
    (c:S⊕Unit→ℝ) (hc:∀v,0 ≤ c v) (hcSupp:∀v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀v,v∈Sum.inl '' I→0 < c v)
    (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hE:∀H,ClassCapOn Q (pointedFamily M f x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \fusionColorRegion m (Sum.inl '' P.val.1)) q)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→pointedMultiplicity M f x q v=c v)
    (hX:PointedResidueAllowed M f false P X q) (hh:pointedResidueHeight M f P X q=0) :
    ∃Y:Deligne M,Y<X ∧ PointedResidueAllowed M f false P Y q := by
  let z:=sourceCosetRepresentative M X
  have hz:=sourceCosetRepresentative_mem M X
  have hE':=pointedResidue_exterior_cap M f hX x z hx hz _ hE
  have hdata':=pointedResidue_zero_exterior M f hX hh x z hx hz I hPI c hcNull hdata
  obtain ⟨residue⟩:=pointedClosedResidue_nonempty M f X z hz
    (pointedCoset_avoids_frame M f P x z hx (hX.1.le.2 hz) I hPI hf hxA) I hI hf (hX.1.le.1.trans hPI)
    q c hc hcSupp hcPos hcNull hE' hdata'
  exact ⟨residue.val,residue.property.1,pointedResidueAllowed_closed_trans M f hX residue.property⟩

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedResidueRank
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedResidueKey_injective (strict:Bool) (P:Deligne M) (q:ℤ) :
    Function.Injective (pointedResidueKey M f strict P q) := by
  intro X Y h
  apply Subtype.ext
  apply sourceTieCode_injective M
  exact congrArg (fun z:Lex (ℕ × Lex (ℕ×ℕ))=>(ofLex (ofLex z).2).2) h

theorem pointedResidueEarlier_wellFounded (strict:Bool) (P:Deligne M) (q:ℤ) :
    WellFounded (PointedResidueEarlier M f strict P q) :=
  InvImage.wf (pointedResidueKey M f strict P q) wellFounded_lt

lemma pointedResidueEarlier_upper_zero {P:Deligne M} {q:ℤ}
    (X Y:PointedResidue M f false P q) (h:X.val<Y.val) (hh:pointedResidueHeight M f P X q=0) :
    ¬PointedResidueEarlier M f false P q Y X := by
  have hv:pointedCosetVector M f X q=pointedCosetVector M f P q:=pointedResidueHeight_zero_vector M f X.property hh
  have heV:pointedCosetVector M f Y q=pointedCosetVector M f X q:=by
    apply pointedCosetVector_eq_of_upper_rows M f h.le q
    intro i hi _
    rw [hv]
    exact pointedCosetVector_harmonic M f P q ⟨.inl i,⟨i,Y.property.1.le.1 hi,rfl⟩⟩
  have he:pointedResidueHeight M f P Y q=0:=by
    unfold pointedResidueHeight at hh ⊢
    rw [heV]
    exact hh
  rw [pointedResidueEarlier_iff,he,hh]
  have hn:X.val.val.1.ncard<Y.val.val.1.ncard:=Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)
  simp only [pointedResidueSecondary,he,hh,lt_self_iff_false,ite_false, if_false,false_or,true_and]
  omega

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedResidueEarlierLowerIso
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
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
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

lemma pointedResidueEarlier_total (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:PointedResidue M f strict P q) (h:X≠Y) :
    PointedResidueEarlier M f strict P q X Y ∨ PointedResidueEarlier M f strict P q Y X := by
  exact lt_or_gt_of_ne (fun he=>h (pointedResidueKey_injective M f strict P q he))

lemma pointedResidue_lower_boundary {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:PointedResidueAllowed M f strict P X q) (x:Artin M) (hx:x∈P.val.2)
    (hb:∀H,ClassCapOn Q (pointedFamily M f x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q) :
    ∀H,ClassCapOn Q (pointedFamily M f (sourceCosetRepresentative M X) H)
      (closedNeighborhood Q (U X.val.1)\U X.val.1) q := by
  have h':=pointedResidue_exterior_cap M f hX x (sourceCosetRepresentative M X) hx
    (sourceCosetRepresentative_mem M X) (closedNeighborhood Q (U P.val.1))
    (by simpa only [←unfoldedInclusion_range] using hb)
  intro H
  apply ClassCapOn.mono Q (h' H)
  intro α hα
  refine ⟨closedNeighborhood_mono Q (unfoldedInclusion_range_mono M hX.1.le.1) hα.1,?_⟩
  simpa only [←unfoldedInclusion_range] using hα.2

lemma pointedResidue_upper_weights_contractible {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:PointedResidue M f strict P q) (hh:pointedResidueHeight M f P X q<0)
    (hn:Nonempty (WeightEarlierUpper (PointedResidueEarlier M f strict P q) X)) :
    ContractibleSpace (OrderWeights (WeightEarlierUpper (PointedResidueEarlier M f strict P q) X)) := by
  let e:=pointedResidueEarlierUpperIso M f X hh
  have hc:=pointedResidueEarlierUpper_contractible M f X.property.1.le hh (hn.map e)
  have hw:ContractibleSpace (OrderWeights (PointedResidueEarlierUpper M f P X q)):=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp hc
  exact (weightHomeomorph e).contractibleSpace_iff.mpr hw

lemma pointedResidue_emptyLink_upper {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:PointedResidue M f strict P q) (hh:pointedResidueHeight M f P X q<0)
    (hn:¬Nonempty (WeightEarlierLink (PointedResidueEarlier M f strict P q) X)) :
    ¬Nonempty (PointedResidueEarlierUpper M f P X q) := by
  intro h
  obtain ⟨Y⟩:=h.map (pointedResidueEarlierUpperIso M f X hh).symm
  exact hn ⟨Y.val,Y.property.1,Or.inr Y.property.2.le⟩

lemma pointedResidue_emptyLink_lower {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:PointedResidue M f strict P q) (hh:pointedResidueHeight M f P X q<0)
    (hn:¬Nonempty (WeightEarlierLink (PointedResidueEarlier M f strict P q) X)) :
    ¬Nonempty (PointedResidue M f true X q) := by
  intro h
  obtain ⟨Y⟩:=h.map (pointedResidueLowerInclusion M f X.property)
  let Z:=(pointedResidueEarlierLowerIso M f X hh).symm Y
  exact hn ⟨Z.val,Z.property.1,Or.inl Z.property.2.le⟩

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_OrderWeightsContractibleUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

theorem orderWeights_contractible_unique_source (r:P→P→Prop) (wf:WellFounded r)
    (htotal:∀x y,x≠y → r x y ∨ r y x)
    (k:P→ℕ) (N:ℕ) (hk:∀x,k x≤N) (hmono:StrictMono k)
    (hl:∀v,Nonempty (WeightEarlierLower r v) →
      ContractibleSpace (OrderWeights (WeightEarlierLower r v)))
    (hu:∀v,Nonempty (WeightEarlierUpper r v) →
      ContractibleSpace (OrderWeights (WeightEarlierUpper r v)))
    (hs:∀x y,¬Nonempty (WeightEarlierLink r x) →
      ¬Nonempty (WeightEarlierLink r y) → x=y)
    (hne:Nonempty P) : ContractibleSpace (OrderWeights P) := by
  obtain ⟨c,_,hc⟩:=wf.has_min Set.univ (by obtain ⟨x⟩:=hne;exact ⟨x,Set.mem_univ _⟩)
  have hc':∀x,¬r x c:=fun x=>hc x (Set.mem_univ x)
  have hcL:¬Nonempty (WeightEarlierLink r c):=by
    rintro ⟨x,hx,_⟩
    exact hc' x hx
  apply orderWeights_contractible_of_earlier_links r wf htotal c hc'
  intro v hv
  have hn:Nonempty (WeightEarlierLink r v):=by
    by_contra hn
    exact hv (hs v c hn hcL)
  rcases weightLink_nonempty_parts r (fun x=>wf.irrefl.irrefl x) v hn with h|h
  · exact weightLink_contractible_of_lower r (fun x=>wf.irrefl.irrefl x) v k N hk hmono (hl v h)
  · exact weightLink_contractible_of_upper r (fun x=>wf.irrefl.irrefl x) v k N hk hmono (hu v h)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_DeligneRankBound
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [LinearOrder S] in
lemma sourceDeligne_rank_bound (X:Deligne M) : X.val.1.ncard≤Fintype.card S := by
  simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card X.val.1
omit [LinearOrder S] in
lemma sourceDeligne_rank_strictMono : StrictMono (fun X:Deligne M=>X.val.1.ncard) := by
  intro X Y h
  exact Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedStrictResidue
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open Simplicial CategoryTheory
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

private theorem pointedStrictResidue_rank (n:ℕ) : ∀(P:Deligne M),P.val.1.ncard=n →
    ∀(q:ℤ) (x:Artin M),x∈P.val.2 →
    (∀H,ClassCapOn Q (pointedFamily M f x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q) →
    Nonempty (PointedResidue M f true P q) →
    ContractibleSpace (OrderWeights (PointedResidue M f true P q)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hn q x hx hb hne
    let r:=PointedResidueEarlier M f true P q
    have hl:∀X:PointedResidue M f true P q,Nonempty (WeightEarlierLower r X) →
        ContractibleSpace (OrderWeights (WeightEarlierLower r X)):=by
      intro X hX
      have hh:=pointedResidueHeight_strict M f X.property
      let e:=pointedResidueEarlierLowerIso M f X hh
      have hsmall:Nonempty (PointedResidue M f true X q):=
        (hX.map e).map (pointedResidueLowerProjection M f X.property)
      have hrank:X.val.val.1.ncard<n:=by
        rw [←hn]
        exact sourceDeligne_rank_strictMono M X.property.1
      have hcont:=ih X.val.val.1.ncard hrank X.val rfl q (sourceCosetRepresentative M X)
        (sourceCosetRepresentative_mem M X) (pointedResidue_lower_boundary M f X.property x hx hb) hsmall
      have hnerve:ContractibleSpace |CategoryTheory.nerve (PointedResidue M f true X q)|:=
        nerveWeightsHomeomorph.contractibleSpace_iff.mpr hcont
      have hlarge:ContractibleSpace |CategoryTheory.nerve (PointedResidueEarlierLower M f true P X q)|:=by
        let :=hnerve
        exact (pointedResidueLowerEquiv M f X.property).contractibleSpace
      have hw:ContractibleSpace (OrderWeights (PointedResidueEarlierLower M f true P X q)):=
        nerveWeightsHomeomorph.contractibleSpace_iff.mp hlarge
      exact (weightHomeomorph e).contractibleSpace_iff.mpr hw
    apply orderWeights_contractible_unique_source r (pointedResidueEarlier_wellFounded M f true P q)
      (pointedResidueEarlier_total M f true P q) (fun X=>X.val.val.1.ncard) (Fintype.card S)
      (fun X=>sourceDeligne_rank_bound M X) (by intro X Y h;exact sourceDeligne_rank_strictMono M h)
      hl (fun X hX=>pointedResidue_upper_weights_contractible M f X (pointedResidueHeight_strict M f X.property) hX)
      ?_ hne
    intro X Y hX hY
    apply Subtype.ext
    have hhX:=pointedResidueHeight_strict M f X.property
    have hhY:=pointedResidueHeight_strict M f Y.property
    exact pointedResidue_negative_pointeds_unique M f X.property Y.property x hx hb hhX hhY
      (pointedResidue_emptyLink_upper M f X hhX hX) (pointedResidue_emptyLink_upper M f Y hhY hY)
      (pointedResidue_emptyLink_lower M f X hhX hX) (pointedResidue_emptyLink_lower M f Y hhY hY)

theorem pointedStrictResidue_contractible (P:Deligne M) (q:ℤ) (x:Artin M) (hx:x∈P.val.2)
    (hb:∀H,ClassCapOn Q (pointedFamily M f x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q)
    (hne:Nonempty (PointedResidue M f true P q)) :
    ContractibleSpace |CategoryTheory.nerve (PointedResidue M f true P q)| :=
  nerveWeightsHomeomorph.contractibleSpace_iff.mpr
    (pointedStrictResidue_rank M f P.val.1.ncard P rfl q x hx hb hne)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedResidueZeroLower
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open Simplicial CategoryTheory
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

lemma pointedResidue_lower_weights_contractible {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:PointedResidue M f strict P q) (hh:pointedResidueHeight M f P X q<0)
    (x:Artin M) (hx:x∈P.val.2)
    (hb:∀H,ClassCapOn Q (pointedFamily M f x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q)
    (hX:Nonempty (WeightEarlierLower (PointedResidueEarlier M f strict P q) X)) :
    ContractibleSpace (OrderWeights (WeightEarlierLower (PointedResidueEarlier M f strict P q) X)) := by
  let e:=pointedResidueEarlierLowerIso M f X hh
  have hsmall:Nonempty (PointedResidue M f true X q):=
    (hX.map e).map (pointedResidueLowerProjection M f X.property)
  have :=pointedStrictResidue_contractible M f X q (sourceCosetRepresentative M X)
    (sourceCosetRepresentative_mem M X) (pointedResidue_lower_boundary M f X.property x hx hb) hsmall
  have hc:= (pointedResidueLowerEquiv M f X.property).contractibleSpace
  exact (weightHomeomorph e).contractibleSpace_iff.mpr
    (nerveWeightsHomeomorph.contractibleSpace_iff.mp hc)

lemma pointedResidueZeroUpper_empty {P:Deligne M} {q:ℤ}
    (X:PointedResidue M f false P q) (hh:pointedResidueHeight M f P X q=0) :
    ¬Nonempty (WeightEarlierUpper (PointedResidueEarlier M f false P q) X) := by
  rintro ⟨Y⟩
  exact pointedResidueEarlier_upper_zero M f X Y.val Y.property.2 hh Y.property.1

lemma pointedResidue_special_boundary {P:Deligne M} {q:ℤ}
    (I:Set S) (hPI:P.val.1⊆I) (x:Artin M)
    (hE:∀H,ClassCapOn Q (pointedFamily M f x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \fusionColorRegion m (Sum.inl '' P.val.1)) q) :
    ∀H,ClassCapOn Q (pointedFamily M f x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q := by
  intro H
  apply ClassCapOn.mono Q (hE H)
  intro α hα
  refine ⟨closedNeighborhood_mono Q ?_ hα.1,?_⟩
  · change Set.range (unfoldedInclusion M P.val.1) ⊆ _
    rw [unfoldedInclusion_range]
    exact fun _ h=>(Set.image_mono hPI) h
  · simpa only [←unfoldedInclusion_range] using hα.2

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedSpecialResidue
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open Simplicial CategoryTheory _root_.Matrix _root_.OAI.Matrix
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

private theorem pointedSpecialResidue_rank (n:ℕ) : ∀(P:Deligne M),P.val.1.ncard=n →
    ∀(x:Artin M),x∈P.val.2 → x∈artinParabolic M {f}ᶜ →
    ∀(I:Set S),I.Nonempty → f∉I → P.val.1⊆I → ∀(q:ℤ),
    ∀(c:S⊕Unit→ℝ),(∀v,0 ≤ c v) → (∀v,v∉Sum.inl '' I→c v=0) →
    (∀v,v∈Sum.inl '' I→0 < c v) → (∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0) →
    (∀H,ClassCapOn Q (pointedFamily M f x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \fusionColorRegion m (Sum.inl '' P.val.1)) q) →
    (∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→pointedMultiplicity M f x q v=c v) →
    ContractibleSpace (OrderWeights (PointedResidue M f false P q)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hn x hx hxA I hI hf hPI q c hc hcSupp hcPos hcNull hE hdata
    let r:=PointedResidueEarlier M f false P q
    have hb:=pointedResidue_special_boundary M f I hPI x hE
    have hzcont:∀(X:PointedResidue M f false P q),pointedResidueHeight M f P X q=0 →
        ContractibleSpace (OrderWeights (PointedResidue M f false X q)):=by
      intro X hh
      have hrank:X.val.val.1.ncard<n:=by
        rw [←hn]
        exact sourceDeligne_rank_strictMono M X.property.1
      exact ih X.val.val.1.ncard hrank X.val rfl (sourceCosetRepresentative M X)
        (sourceCosetRepresentative_mem M X)
        (pointedCoset_avoids_frame M f P x (sourceCosetRepresentative M X) hx
          (X.property.1.le.2 (sourceCosetRepresentative_mem M X)) I hPI hf hxA)
        I hI hf (X.property.1.le.1.trans hPI) q c hc hcSupp hcPos hcNull
        (pointedResidue_exterior_cap M f X.property x (sourceCosetRepresentative M X) hx
          (sourceCosetRepresentative_mem M X) _ hE)
        (pointedResidue_zero_exterior M f X.property hh x (sourceCosetRepresentative M X) hx
          (sourceCosetRepresentative_mem M X) I hPI c hcNull hdata)
    have hneg:∀(X:PointedResidue M f false P q),¬Nonempty (WeightEarlierLink r X) →
        pointedResidueHeight M f P X q<0:=by
      intro X hX
      rcases lt_or_eq_of_le (pointedResidueHeight_nonpos M f X.property) with hh|hh
      · exact hh
      · exfalso
        obtain ⟨Y,hy,hYa⟩:=pointedResidue_zero_ne_lower M f P X x hx hxA I hI hf hPI q c hc hcSupp hcPos hcNull hE hdata X.property hh
        exact hX ⟨⟨Y,hYa⟩,pointedResidueEarlier_lower_zero M f X _ hy hh,Or.inl hy.le⟩
    apply orderWeights_contractible_unique_source r (pointedResidueEarlier_wellFounded M f false P q)
      (pointedResidueEarlier_total M f false P q) (fun X=>X.val.val.1.ncard) (Fintype.card S)
      (fun X=>sourceDeligne_rank_bound M X) (by intro X Y h;exact sourceDeligne_rank_strictMono M h)
      ?_ ?_ ?_ (pointedClosedResidue_nonempty M f P x hx hxA I hI hf hPI q c hc hcSupp hcPos hcNull hE hdata)
    · intro X hX
      rcases lt_or_eq_of_le (pointedResidueHeight_nonpos M f X.property) with hh|hh
      · exact pointedResidue_lower_weights_contractible M f X hh x hx hb hX
      · exact (weightHomeomorph (pointedResidueZeroLowerIso M f X hh)).contractibleSpace_iff.mpr (hzcont X hh)
    · intro X hX
      rcases lt_or_eq_of_le (pointedResidueHeight_nonpos M f X.property) with hh|hh
      · exact pointedResidue_upper_weights_contractible M f X hh hX
      · exact False.elim (pointedResidueZeroUpper_empty M f X hh hX)
    · intro X Y hX hY
      have hhX:=hneg X hX
      have hhY:=hneg Y hY
      apply Subtype.ext
      exact pointedResidue_negative_pointeds_unique M f X.property Y.property x hx hb hhX hhY
        (pointedResidue_emptyLink_upper M f X hhX hX) (pointedResidue_emptyLink_upper M f Y hhY hY)
        (pointedResidue_emptyLink_lower M f X hhX hX) (pointedResidue_emptyLink_lower M f Y hhY hY)

theorem pointedSpecialResidue_contractible (P:Deligne M) (x:Artin M) (hx:x∈P.val.2) (hxA:x∈artinParabolic M {f}ᶜ)
    (I:Set S) (hI:I.Nonempty) (hf:f∉I) (hPI:P.val.1⊆I) (q:ℤ)
    (c:S⊕Unit→ℝ) (hc:∀v,0 ≤ c v) (hcSupp:∀v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀v,v∈Sum.inl '' I→0 < c v)
    (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hE:∀H,ClassCapOn Q (pointedFamily M f x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \fusionColorRegion m (Sum.inl '' P.val.1)) q)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→pointedMultiplicity M f x q v=c v) :
    ContractibleSpace |nerve (PointedResidue M f false P q)| :=
  nerveWeightsHomeomorph.contractibleSpace_iff.mpr
    (pointedSpecialResidue_rank M f P.val.1.ncard P rfl x hx hxA I hI hf hPI q c hc hcSupp hcPos hcNull hE hdata)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeEligibleFactor
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

theorem relativeEligibleProduct_contractible (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (h:ContractibleSpace (OrderWeights
      {V:RelativeEligibleWithin M f U cutoff Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) //V≠⊤})) :
    ContractibleSpace (OrderWeights {V:RelativeEligibleWithin M f U cutoff Ref (sourceCoset M (B∪C) hT x) //V≠⊤}) := by
  let e:=relativeEligibleProductPuncture M f U cutoff Ref B C hT hd hc x
  apply (weightHomeomorph e).contractibleSpace_iff.mp
  apply binaryProductBoundary_contractible (fun V=>(e V).val.val.val.1.ncard) (Fintype.card S)
    (fun V=>sourceDeligne_rank_bound M (e V).val.val) ?_ h
  intro V W hVW
  exact sourceDeligne_rank_strictMono M (e.strictMono hVW)


end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeEligibleBlocks
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

lemma relativeEligible_left_nonempty (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (V:RelativeEligibleWithin M f U cutoff Ref (sourceCoset M (B∪C) hT x)) (i:S) (hi:i∈B) (ho:i∉V.val.val.1) :
    Nonempty {A:RelativeEligibleWithin M f U cutoff Ref
      (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) //A≠⊤} := by
  obtain ⟨⟨a,_⟩,he⟩:=relativeEligibleProductFun_surjective M f U cutoff Ref B C hT hd hc x V
  refine ⟨a,?_⟩
  intro ha
  have ht:i∈a.val.val.1:=by rw [ha];exact hi
  apply ho
  rw [←he]
  exact Or.inl ht

lemma relativeBlock_allEligible_contractible (P:Deligne M) (B:Set S) (hB:B⊆P.val.1)
    (hc:∀s∈B,∀t∈P.val.1\B,M s t=2) (x:Artin M) (hx:x∈P.val.2)
    (h:ContractibleSpace (OrderWeights
      {V:RelativeEligibleWithin M f U cutoff P (sourceCoset M B (source_spherical_mono M hB P.property.1) x) //V≠⊤})) :
    ContractibleSpace (OrderWeights (RelativeAllEligibleLower M f U cutoff P)) := by
  let C:=P.val.1\B
  have hBC:B∪C=P.val.1:=Set.union_sdiff_cancel hB
  have hT:IsSpherical M (B∪C):=by rw [hBC];exact P.property.1
  have hd:Disjoint B C:=Set.disjoint_left.mpr (fun _ h h'=>h'.2 h)
  have he:sourceCoset M (B∪C) hT x=P:=by
    simpa only [hBC] using sourceCoset_eq M P x hx
  have hh:=relativeEligibleProduct_contractible M f U cutoff P B C hT hd hc x h
  rw [he] at hh
  exact (weightHomeomorph (relativeEligiblePuncture M f U cutoff P)).contractibleSpace_iff.mp hh

lemma relativeBlock_eligible_nonempty (P:Deligne M) (B:Set S) (hB:B⊆P.val.1)
    (hc:∀s∈B,∀t∈P.val.1\B,M s t=2) (x:Artin M) (hx:x∈P.val.2)
    (V:RelativeAllEligibleLower M f U cutoff P) (i:S) (hi:i∈B) (ho:i∉V.val.val.1) :
    Nonempty {A:RelativeEligibleWithin M f U cutoff P
      (sourceCoset M B (source_spherical_mono M hB P.property.1) x) //A≠⊤} := by
  let C:=P.val.1\B
  have hBC:B∪C=P.val.1:=Set.union_sdiff_cancel hB
  have hT:IsSpherical M (B∪C):=by rw [hBC];exact P.property.1
  have hd:Disjoint B C:=Set.disjoint_left.mpr (fun _ h h'=>h'.2 h)
  have he:sourceCoset M (B∪C) hT x=P:=by simpa only [hBC] using sourceCoset_eq M P x hx
  let W:RelativeEligibleWithin M f U cutoff P (sourceCoset M (B∪C) hT x):=
    ⟨V.val,by rw [he];exact ⟨V.property.1.le,V.property.2⟩⟩
  exact relativeEligible_left_nonempty M f U cutoff P B C hT hd hc x W i hi ho

lemma pointedBlock_vector (P:Deligne M) (B:Set S) (hB:B⊆P.val.1)
    (hc:∀s∈B,∀t∈P.val.1\B,M s t=2) (x:Artin M) (hx:x∈P.val.2) (q:ℤ) :
    ∀i∈B,pointedCosetVector M f (sourceCoset M B (source_spherical_mono M hB P.property.1) x) q (.inl i)=
      pointedCosetVector M f P q (.inl i) := by
  have hBC:B∪(P.val.1\B)=P.val.1:=Set.union_sdiff_cancel hB
  have hT:IsSpherical M (B∪(P.val.1\B)):=by rw [hBC];exact P.property.1
  have he:sourceCoset M (B∪(P.val.1\B)) hT x=P:=by simpa only [hBC] using sourceCoset_eq M P x hx
  intro i hi
  simpa only [he] using pointedCosetVector_block M f B (P.val.1\B) hT hc x q i hi


end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeNullBlockData
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

omit [LinearOrder S] in
lemma relativeNullData_of_positive (p:ℕ →₀ (S ⊕ Unit → ℝ)) (q:ℕ) (i:S ⊕ Unit)
    (hp:0<p q i) (h:relativePositiveSign (framedCartan M) U p q i) : RelativeNullData M U p q i := by
  obtain ⟨hU,hr,hh⟩ := (relativePositiveSign_component_iff M U p q i hp).mp h
  refine ⟨hU,hr,?_⟩
  intro j hj d hd
  apply hh d hd j
  rcases hj with hj|⟨a,ha,hja⟩
  · exact Or.inl hj
  · exact Or.inr ⟨a,ha,by rwa [framedCartan_symm]⟩

omit [LinearOrder S] in
lemma relativePositive_of_nullData (p:ℕ →₀ (S ⊕ Unit → ℝ)) (q:ℕ) (i:S ⊕ Unit)
    (hp:0<p q i) (h:RelativeNullData M U p q i) : relativePositiveSign (framedCartan M) U p q i := by
  apply (relativePositiveSign_component_iff M U p q i hp).mpr
  refine ⟨h.1,h.2.1,?_⟩
  intro d hd j hj
  apply h.2.2 j _ d hd
  rcases hj with hj|⟨a,ha,haj⟩
  · exact Or.inl hj
  · exact Or.inr ⟨a,ha,by rwa [framedCartan_symm]⟩

lemma pointedPositiveComponent_type_neighbor (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<pointedProfile M f P cutoff q i) (j:S⊕Unit)
    (hj:j∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i) (k:S) (hk:k∈P.val.1)
    (hjk:framedCartan M j (.inl k)<0) :
    (.inl k:S⊕Unit)∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i := by
  have hp:=sourcePositiveComponent_positive M _ i hi j hj
  have hkp:=pointedProfile_positive_neighbor M f cutoff P q k hk j (by rwa [framedCartan_symm]) hp
  exact hj.tail ⟨hp,hjk,hkp⟩

lemma pointedPositiveBlock_commutes (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<pointedProfile M f P cutoff q i) (j k:S) (_hj:j∈P.val.1)
    (hjI:(.inl j:S⊕Unit)∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i)
    (hk:k∈P.val.1) (hkI:(.inl k:S⊕Unit)∉sourcePositiveComponent M (pointedProfile M f P cutoff q) i) :
    M j k=2 := by
  by_contra hn
  exact hkI (pointedPositiveComponent_type_neighbor M f cutoff P q i hi (.inl j) hjI k hk
    (framedCartan_neg_of_label_ne_two M j k (by rintro rfl;exact hkI hjI) hn))

lemma relativeNullSign_image (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hn:RelativeNullData M U (pointedProfile M f P cutoff) q i)
    (hU : U ⊆ Set.range (Sum.inl:S→S⊕Unit)) :
    Sum.inl '' {j:S | (.inl j:S⊕Unit)∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i}=
      sourcePositiveComponent M (pointedProfile M f P cutoff q) i := by
  ext v
  constructor
  · rintro ⟨j,hj,rfl⟩;exact hj
  · intro hv
    rcases v with j|u
    · exact ⟨j,hv,rfl⟩
    · obtain ⟨a,ha⟩ := hU (hn.1 hv)
      cases ha

lemma relativeNullSign_peak (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<pointedProfile M f P cutoff q i)
    (hn:RelativeNullData M U (pointedProfile M f P cutoff) q i)
    (j:S) (_hj:j∈P.val.1)
    (hjI:(.inl j:S⊕Unit)∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i) :
    relativePeak M f cutoff P j=q := by
  apply le_antisymm
  · by_contra h
    have hh:q < relativePeak M f cutoff P j:=lt_of_not_ge h
    have hz:=hn.2.2 (.inl j) (Or.inl hjI) (relativePeak M f cutoff P j) hh
    exact (ne_of_gt (relativePeak_positive M f cutoff P j ⟨q, sourcePositiveComponent_positive M _ i hi _ hjI⟩)) hz
  · exact relativePeak_bound M f cutoff P j q (ne_of_gt (sourcePositiveComponent_positive M _ i hi _ hjI))

lemma relativeNullSign_sign (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<pointedProfile M f P cutoff q i)
    (hn:RelativeNullData M U (pointedProfile M f P cutoff) q i)
    (v:S⊕Unit) (hv:v∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i) :
    relativeSign M U (pointedProfile M f P cutoff) q v=1 := by
  have he:=sourcePositiveComponent_eq M (pointedProfile M f P cutoff q) v
    (sourcePositiveComponent M (pointedProfile M f P cutoff q) i)
    (sourcePositiveComponent_spec M _ i hi) hv
  have hnv:RelativeNullData M U (pointedProfile M f P cutoff) q v := by
    unfold RelativeNullData
    rw [he]
    exact hn
  have hsign := relativePositive_of_nullData M U _ q v
    (sourcePositiveComponent_positive M _ i hi v hv) hnv
  simp only [relativeSign, ne_of_gt (sourcePositiveComponent_positive M _ i hi v hv),
    hsign, ↓reduceIte]

lemma relativeNullPatch_nonneg (P:Deligne M) (q:ℕ) (i v:S⊕Unit) : 0 ≤ relativeNullPatch M f cutoff P q i v := by
  unfold relativeNullPatch
  split_ifs
  · exact pointedCosetVector_nonneg M f P (cutoff+q) v
  · rfl

lemma relativeNullPatch_row (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<pointedProfile M f P cutoff q i)
    (hn:RelativeNullData M U (pointedProfile M f P cutoff) q i)
    (v:S⊕Unit) (hv:v∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i) :
    (framedCartan M *ᵥ relativeNullPatch M f cutoff P q i) v=0 := by
  trans (framedCartan M *ᵥ pointedProfile M f P cutoff q) v
  · apply Finset.sum_congr rfl
    intro u _
    by_cases hu:u∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i
    · simp only [relativeNullPatch,ite_eq_left hu]
    · simp only [relativeNullPatch,ite_eq_right hu,MulZeroClass.mul_zero]
      by_cases hh:framedCartan M v u<0
      · rw [sourcePositiveComponent_boundary_zero M (pointedProfile M f P cutoff q)
          (fun v => pointedCosetVector_nonneg M f P (cutoff+q) v) i hi u hu
          ⟨v,hv,by rwa [framedCartan_symm]⟩,MulZeroClass.mul_zero]
      · have he:framedCartan M v u=0:=le_antisymm (framedCartan_off M v u
          (by rintro rfl;exact hu hv)) (le_of_not_gt hh)
        rw [he,MulZeroClass.zero_mul]
  · exact hn.2.1 v hv

lemma relativePositive_exterior (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<pointedProfile M f P cutoff q i) (v:S⊕Unit)
    (hv:v∈sourceClosedRegion M (sourcePositiveComponent M (pointedProfile M f P cutoff q) i))
    (ho:v∉Sum.inl '' (P.val.1∩{j:S | (.inl j:S⊕Unit)∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i})) :
    v∉Sum.inl '' P.val.1 := by
  rintro ⟨j,hj,rfl⟩
  apply ho
  refine ⟨j,⟨hj,?_⟩,rfl⟩
  rcases hv with hv|⟨u,hu,huj⟩
  · exact hv
  · exact pointedPositiveComponent_type_neighbor M f cutoff P q i hi u hu j hj (by rwa [framedCartan_symm])

lemma relativePositive_block_cap (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<pointedProfile M f P cutoff q i)
    (hn:RelativeNullData M U (pointedProfile M f P cutoff) q i)
    (hU : U ⊆ Set.range (Sum.inl:S→S⊕Unit)) (x:Artin M) (hx:x∈P.val.2) :
    let I:Set S:={j | (.inl j:S⊕Unit)∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i}
    ∀H,ClassCapOn Q (pointedFamily M f x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
        fusionColorRegion m (Sum.inl '' (P.val.1∩I))) (cutoff+q) := by
  intro I H
  rw [classCapOn_iff_level_zero]
  intro α hα k hk
  have hv:=sourceNeighborhood_project M (Sum.inl '' I) hα.1
  rw [relativeNullSign_image M f U cutoff P q i hn hU] at hv
  have hout:=relativePositive_exterior M f cutoff P q i hi α.1 hv hα.2
  have hk0:0≤k-cutoff:=by omega
  have he:cutoff+((k-cutoff).toNat:ℤ)=k:=by rw [Int.toNat_of_nonneg hk0];omega
  have hz:=hn.2.2 α.1 hv (k-cutoff).toNat (by omega)
  change pointedCosetVector M f P (cutoff+(k-cutoff).toNat) α.1=0 at hz
  rw [he,pointedCosetVector_open_at M f P x hx α.1 hout k] at hz
  exact (pointedMultiplicity_zero_iff M f x k α.1).mp hz H α.2

lemma relativePositive_block_values (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<pointedProfile M f P cutoff q i)
    (hn:RelativeNullData M U (pointedProfile M f P cutoff) q i)
    (hU : U ⊆ Set.range (Sum.inl:S→S⊕Unit)) (x:Artin M) (hx:x∈P.val.2) :
    let I:Set S:={j | (.inl j:S⊕Unit)∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i}
    ∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' (P.val.1∩I)) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→
      pointedMultiplicity M f x (cutoff+q) v=relativeNullPatch M f cutoff P q i v := by
  intro I v hv
  have hI:Sum.inl '' I=sourcePositiveComponent M (pointedProfile M f P cutoff q) i:=relativeNullSign_image M f U cutoff P q i hn hU
  rw [hI] at hv
  rcases hv with ⟨hv,ho⟩|⟨ho,hv⟩
  · rw [←pointedCosetVector_open_at M f P x hx v (relativePositive_exterior M f cutoff P q i hi v (Or.inl hv) ho) (cutoff+q)]
    simp only [relativeNullPatch,ite_eq_left hv]
    rfl
  · have hoB:v∉Sum.inl '' (P.val.1∩I):=by
      intro h
      exact ho (hI ▸ Set.image_mono Set.inter_subset_right h)
    rw [←pointedCosetVector_open_at M f P x hx v (relativePositive_exterior M f cutoff P q i hi v (Or.inr hv) hoB) (cutoff+q)]
    rw [relativeNullPatch,ite_eq_right ho]
    exact sourcePositiveComponent_boundary_zero M _ (pointedCosetVector_nonneg M f P (cutoff+q)) i hi v ho hv


end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeLowerContractible
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contractibility of nonempty descending lower neighborhoods of the relative height. -/
namespace HarmonicArtin.ParabolicIntersections
open scoped _root_.Matrix _root_.OAI.Matrix
open CategoryTheory Simplicial ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

lemma relativeNegativeBlock_contractible (P:Deligne M) (i:S) (hi:i∈P.val.1)
    (hp:0<pointedProfile M f P cutoff (relativePeak M f cutoff P i) (.inl i))
    (hs:relativeSign M U (pointedProfile M f P cutoff) (relativePeak M f cutoff P i) (.inl i)= -1)
    (V:RelativeAllEligibleLower M f U cutoff P) (ho:i∉V.val.val.1) :
    ContractibleSpace (OrderWeights (RelativeAllEligibleLower M f U cutoff P)) := by
  let B:=sourceTypeComponent M P i hi
  have hB:B⊆P.val.1:=sourceTypeComponent_subset M P i hi
  have hc:∀s∈B,∀t∈P.val.1\B,M s t=2:=sourceTypeComponent_commutes M P i hi
  let q:=relativePeak M f cutoff P i
  have hpeak:∀j∈B,relativePeak M f cutoff P j=q:=pointedTypeComponent_peak M f cutoff P i hi
  let x:=sourceCosetRepresentative M P
  have hx:=sourceCosetRepresentative_mem M P
  let R:=sourceCoset M B (source_spherical_mono M hB P.property.1) x
  have hsg:∀j∈B,relativeSign M U (pointedProfile M f P cutoff) q (.inl j)=if true then -1 else 1:=by
    intro j hj
    exact (pointedTypeComponent_sign M f U cutoff P i hi q hp j hj).trans hs
  let e:=relativeEligibleFactor M f U cutoff P R hB q true hpeak hsg
    (pointedBlock_vector M f P B hB hc x hx (cutoff+q))
  have hn:=relativeBlock_eligible_nonempty M f U cutoff P B hB hc x hx V i
    (sourceTypeComponent_self M P i hi) ho
  have hr:ContractibleSpace (OrderWeights (PointedResidue M f true R (cutoff+q))):=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp
      (pointedStrictResidue_contractible M f R (cutoff+q) x (rightCoset_self M B x)
        (pointedBlock_boundary_cap M f cutoff P B hB hc q hpeak x hx) (Nonempty.map e hn))
  exact relativeBlock_allEligible_contractible M f U cutoff P B hB hc x hx
    ((weightHomeomorph e).contractibleSpace_iff.mpr hr)

lemma relativePositiveBlock_contractible (P:Deligne M) (q:ℕ) (i:S)
    (hp:0<pointedProfile M f P cutoff q (.inl i))
    (hn:RelativeNullData M U (pointedProfile M f P cutoff) q (.inl i))
    (hU:U⊆Set.range (Sum.inl:S→S⊕Unit)) (hf:(.inl f:S⊕Unit)∉U)
    (hxA:sourceCosetRepresentative M P∈artinParabolic M {f}ᶜ) :
    ContractibleSpace (OrderWeights (RelativeAllEligibleLower M f U cutoff P)) := by
  let I:Set S:={j | (.inl j:S⊕Unit)∈sourcePositiveComponent M (pointedProfile M f P cutoff q) (.inl i)}
  let B:=P.val.1∩I
  have hB:B⊆P.val.1:=Set.inter_subset_left
  have hiI:i∈I:=Relation.ReflTransGen.refl
  have hfI:f∉I:=fun h => hf (hn.1 h)
  have hc:∀s∈B,∀t∈P.val.1\B,M s t=2:=by
    intro s hs t ht
    exact pointedPositiveBlock_commutes M f cutoff P q (.inl i) hp s t hs.1 hs.2 ht.1
      (fun h=>ht.2 ⟨ht.1,h⟩)
  have hpeak:∀j∈B,relativePeak M f cutoff P j=q:=fun j hj=>
    relativeNullSign_peak M f U cutoff P q (.inl i) hp hn j hj.1 hj.2
  have hsg:∀j∈B,relativeSign M U (pointedProfile M f P cutoff) q (.inl j)=if false then -1 else 1:=
    fun j hj=>relativeNullSign_sign M f U cutoff P q (.inl i) hp hn (.inl j) hj.2
  let x:=sourceCosetRepresentative M P
  have hx:=sourceCosetRepresentative_mem M P
  let R:=sourceCoset M B (source_spherical_mono M hB P.property.1) x
  let c:=relativeNullPatch M f cutoff P q (.inl i)
  have hI:Sum.inl '' I=sourcePositiveComponent M (pointedProfile M f P cutoff q) (.inl i):=
    relativeNullSign_image M f U cutoff P q (.inl i) hn hU
  have hcSupp:∀v,v∉Sum.inl '' I→c v=0:=by
    intro v hv
    rw [hI] at hv
    exact ite_eq_right hv
  have hcPos:∀v,v∈Sum.inl '' I→0 < c v:=by
    intro v hv
    rw [hI] at hv
    change 0 < relativeNullPatch M f cutoff P q (.inl i) v
    rw [relativeNullPatch,ite_eq_left hv]
    exact sourcePositiveComponent_positive M _ (.inl i) hp v hv
  have hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0:=by
    intro v hv
    rw [hI] at hv
    exact relativeNullPatch_row M f U cutoff P q (.inl i) hp hn v hv
  have hr:ContractibleSpace (OrderWeights (PointedResidue M f false R (cutoff+q))):=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp
      (pointedSpecialResidue_contractible M f R x (rightCoset_self M B x) hxA I ⟨i,hiI⟩ hfI
        Set.inter_subset_right (cutoff+q) c (relativeNullPatch_nonneg M f cutoff P q (.inl i))
        hcSupp hcPos hcNull (relativePositive_block_cap M f U cutoff P q (.inl i) hp hn hU x hx)
        (relativePositive_block_values M f U cutoff P q (.inl i) hp hn hU x hx))
  let e:=relativeEligibleFactor M f U cutoff P R hB q false hpeak hsg
    (pointedBlock_vector M f P B hB hc x hx (cutoff+q))
  exact relativeBlock_allEligible_contractible M f U cutoff P B hB hc x hx
    ((weightHomeomorph e).contractibleSpace_iff.mpr hr)

/-- The lower-link argument uses no positivity assumption on invisible colors. -/
theorem relativeAllEligibleLower_contractible (P:Deligne M)
    (hU:U⊆Set.range (Sum.inl:S→S⊕Unit)) (hf:(.inl f:S⊕Unit)∉U)
    (hxA:sourceCosetRepresentative M P∈artinParabolic M {f}ᶜ)
    (hne:Nonempty (RelativeAllEligibleLower M f U cutoff P)) :
    ContractibleSpace (OrderWeights (RelativeAllEligibleLower M f U cutoff P)) := by
  obtain ⟨V⟩:=hne
  have hnot:¬P.val.1⊆V.val.val.1:=by
    intro h
    exact V.property.1.ne (deligne_eq_of_le_type_eq M V.property.1.le
      (Set.Subset.antisymm V.property.1.le.1 h))
  obtain ⟨i,hi,ho⟩:=Set.not_subset.mp hnot
  let q:=relativePeak M f cutoff P i
  have hp : 0 < pointedProfile M f P cutoff q (.inl i) :=
    relativeEligible_positive M f U cutoff (V.property.2 i hi ho)
  by_cases hn:relativePositiveSign (framedCartan M) U (pointedProfile M f P cutoff) q (.inl i)
  · exact relativePositiveBlock_contractible M f U cutoff P q i hp
      (relativeNullData_of_positive M U _ q (.inl i) hp hn) hU hf hxA
  · have hs:relativeSign M U (pointedProfile M f P cutoff) q (.inl i)= -1:=by
      simp only [relativeSign,ne_of_gt hp,hn,↓reduceIte]
    exact relativeNegativeBlock_contractible M f U cutoff P i hi hp hs V ho

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightColor
attribute [-instance] _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {P:Type u} [PartialOrder P]

lemma weightColor_eq {A:Type v} (f:P→A) (hf:∀x y,x≤y → f x=f y)
    (w:OrderWeights P) (p:P) (hp:p∈w.weights.support) : weightColor f w=f p := by
  rcases w.chain (Classical.choose w.support_nonempty) (Classical.choose_spec w.support_nonempty) p hp with h|h
  · exact hf _ _ h
  · exact (hf _ _ h).symm

lemma weightColor_continuous {A:Type v} [TopologicalSpace A] (f:P→A)
    (hf:∀x y,x≤y → f x=f y) : Continuous (weightColor f) := by
  rw [orderWeights_continuous_iff]
  intro n x
  have he: (fun z=>weightColor f (orderWeightsOfChain (nerveChain x) z))=
      (fun _ : Convexity.StdSimplex ℝ (Fin (n.len+1))=>f (nerveChain x 0)) := by
    funext z
    let w:=orderWeightsOfChain (nerveChain x) z
    have hp:Classical.choose w.support_nonempty∈(chainWeights (nerveChain x) z).support:=Classical.choose_spec w.support_nonempty
    obtain ⟨j,_,hj⟩:=Finset.mem_image.mp (chainWeights_support (nerveChain x) z hp)
    change f (Classical.choose w.support_nonempty)=_
    rw [←hj]
    exact (hf _ _ ((nerveChain x).monotone (Fin.zero_le j))).symm
  rw [he]
  exact continuous_const

lemma weightColor_vertex {A:Type v} (f:P→A) (hf:∀x y,x≤y → f x=f y) (p:P) :
    weightColor f (weightVertex p)=f p := by
  apply weightColor_eq f hf
  simp [weightVertex]

lemma orderWeights_colors_eq {A:Type v} (h:ContractibleSpace (OrderWeights P))
    (f:P→A) (hf:∀x y,x≤y → f x=f y) (x y:P) : f x=f y := by
  let _ := h
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have he:=PreconnectedSpace.constant (inferInstance:PreconnectedSpace (OrderWeights P))
    (weightColor_continuous f hf) (x:=weightVertex x) (y:=weightVertex y)
  simpa only [weightColor_vertex f hf] using he

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeLowerConnected
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparability paths in the descending lower neighborhood. -/
namespace HarmonicArtin.ParabolicIntersections
open CategoryTheory Simplicial
attribute [local instance] Classical.decEq Classical.propDecidable

lemma orderWeights_comparability_connected {V:Type} [PartialOrder V]
    (h:ContractibleSpace (OrderWeights V)) (a b:V) :
    Relation.ReflTransGen (fun x y:V => x≤y ∨ y≤x) a b := by
  let s : Setoid V :=
    { r := Relation.ReflTransGen (fun x y:V => x≤y ∨ y≤x)
      iseqv :=
        { refl := fun _ => .refl
          symm := by
            intro x y hp
            induction hp with
            | refl => exact .refl
            | @tail z w hp edge ih =>
              exact (Relation.ReflTransGen.single (r:=fun x y:V => x≤y ∨ y≤x)
                (edge.elim Or.inr Or.inl)).trans ih
          trans := fun h₁ h₂ => h₁.trans h₂ } }
  have he : Quotient.mk s a = Quotient.mk s b :=
    orderWeights_colors_eq h (Quotient.mk s)
      (fun x y hxy => Quotient.sound (Relation.ReflTransGen.single (r:=fun x y:V => x≤y ∨ y≤x)
        (Or.inl hxy))) a b
  exact Quotient.exact he

variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

theorem relativeDescendingLower_contractible (P:Deligne M)
    (hU:U⊆Set.range (Sum.inl:S→S⊕Unit)) (hf:(.inl f:S⊕Unit)∉U)
    (hxA:sourceCosetRepresentative M P∈artinParabolic M {f}ᶜ)
    (hne:Nonempty (RelativeDescendingLower M f U cutoff P)) :
    ContractibleSpace (OrderWeights (RelativeDescendingLower M f U cutoff P)) := by
  have he:=relativeEarlierLower_equiv_allEligible M f U cutoff P
  have hc:ContractibleSpace |nerve (RelativeAllEligibleLower M f U cutoff P)|:=
    nerveWeightsHomeomorph.contractibleSpace_iff.mpr
      (relativeAllEligibleLower_contractible M f U cutoff P hU hf hxA
        (Nonempty.map (relativeAllEligibleProjection M f U cutoff P) hne))
  exact nerveWeightsHomeomorph.contractibleSpace_iff.mp (he.contractibleSpace_iff.mpr hc)

/-- Any two descending lower neighbors are joined within that same neighborhood. -/
theorem relative_descending_lower_connected_s236_oai {Y:Set S} {x:Artin M} (P:RelativeVertex M Y x)
    (hU:U⊆Set.range (Sum.inl:S→S⊕Unit)) (hf:(.inl f:S⊕Unit)∉U)
    (hxA:sourceCosetRepresentative M P.val∈artinParabolic M {f}ᶜ)
    (R Q:RelativeVertex M Y x)
    (hR:RelativeStrictLower M f U cutoff P R) (hQ:RelativeStrictLower M f U cutoff P Q) :
    PathWithin (relativeAdjacent M) (RelativeStrictLower M f U cutoff P) R Q := by
  let A:RelativeDescendingLower M f U cutoff P.val:=⟨R.val,hR⟩
  let B:RelativeDescendingLower M f U cutoff P.val:=⟨Q.val,hQ⟩
  let e (V:RelativeDescendingLower M f U cutoff P.val) : RelativeVertex M Y x :=
    ⟨V.val, V.property.1.le.1.trans P.property.1, V.property.1.le.2.trans P.property.2⟩
  have hc:=relativeDescendingLower_contractible M f U cutoff P.val hU hf hxA ⟨A⟩
  have hp:=orderWeights_comparability_connected hc A B
  exact Relation.ReflTransGen.lift e (fun a b hab =>
    ⟨a.property,b.property,hab.elim Or.inl Or.inr⟩) A B hp

end HarmonicArtin.ParabolicIntersections

end OAI
end

theorem solution : type_of% @OAI.HarmonicArtin.ParabolicIntersections.relative_descending_lower_connected_s236_oai := @OAI.HarmonicArtin.ParabolicIntersections.relative_descending_lower_connected_s236_oai
