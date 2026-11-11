-- Prove2me | solution 1 for OAI.HarmonicArtin.sourcePositiveBlock_contractible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T18:03:34.890609+00:00
-- url     : https://prove2.me/submissions/81fa9992-7cb5-4550-b26b-e6c43565f8de

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag015
import Theorems.Thm_OAI_HarmonicArtin_sourceCandidate_zero_block
import Theorems.Thm_OAI_HarmonicArtin_sourceClosedResidue_nonempty
import Theorems.Thm_OAI_HarmonicArtin_sourceResidue_lower_weights_contractible
import Theorems.Thm_OAI_HarmonicArtin_sourceResidue_zero_ne_lower

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LevelArrayMinimalApply
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_GeneratorArrayZeroLevel
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnfoldedHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
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
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_NerveOrderMap
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightHomeomorph
attribute [-instance] _root_.OAI.HarmonicArtin.WeightContractionPiece.instReflExtends _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_LateDelay
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightVertexRetract
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_InsertOldIso
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnionCarrier
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Initial
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_ContractionPoint
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightJoinKey
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightEarlierLower
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_OrderWeightsContractibleLower
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProductBoxSlice
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPreorderLiftedCell
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_BinaryProductBoundary
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnfoldedInclusionRange
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_FrameFamilyWeightedLevel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnfoldedInclusionRangeMono
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
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
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)

omit [Fintype S] in
lemma unfoldedInclusion_range_mono {J T:Set S} (h:J⊆T) :
    Set.range (unfoldedInclusion M J)⊆Set.range (unfoldedInclusion M T) := by
  rintro α ⟨⟨j,L⟩,rfl⟩
  exact ⟨(⟨j,h j.property⟩,L),rfl⟩

lemma sourceMultiplicity_cap_zero (T:Set S) (z:Artin M) (q k:ℤ) (hq:q<k)
    (hz:∀H,ClassCapOn Q (sourceFrameFamily M z H)
      (Set.range (unfoldedInclusion M T)) q) (s:S) (hs:s∈T) :
    sourceMultiplicity M z k (.inl s)=0 := by
  let L:=fusionZeroLabel m (fusionLabelSize_ge_two M)
  have hw:=sourceFrameFamily_weighted_level M z k (.inl s,L)
  have he: (∑H,fusionWeight m H*
      (classLevelArray Q (sourceFrameFamily M z H) ((.inl s,L),k):ℝ))=0 := by
    apply Finset.sum_eq_zero
    intro H _
    rw [(classCapOn_iff_level_zero Q _ _ _).mp (hz H) _ ⟨(⟨s,hs⟩,L),rfl⟩ k hq]
    simp
  rw [he] at hw
  exact (mul_eq_zero.mp hw.symm).resolve_left (ne_of_gt (fusionWeight_pos m (fusionLabelSize_ge_two M) L))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbeFixedDiagonal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
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

theorem sourceCandidate_fixed_probes (T J J':Set S) (hT:IsSpherical M T) (z h:Artin M)
    (hh:h∈artinParabolic M T) (q:ℤ) (p p':S⊕Unit→ℝ)
    (X:SourceCappedCandidate M T J z q p) (Y:SourceCappedCandidate M T J' (h*z) q p') :
    p=p' ∧ J=J' ∧ ∀s∈T,s∉J→∀L b,
      sourceProbeAction M (K:=ℂ) h (initialClass R (.inr ((.inl s,L),b)))=
        initialClass R (.inr ((.inl s,L),b)) := by
  obtain ⟨he,hj,hz⟩:=sourceCandidate_zero_block M T J J' hT z h hh q p p' X Y
  refine ⟨he,hj,?_⟩
  intro s hs hsJ L b
  exact sourceProbe_fixed_of_diagonal M T h hh (.inl s,L) b (hz s hs hsJ s hs hsJ L L b)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ProbePositiveWordLeft
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)

theorem sourceCandidate_comparison_parabolic (T J J':Set S) (hT:IsSpherical M T)
    (z h:Artin M) (hh:h∈artinParabolic M T) (q:ℤ) (p p':S⊕Unit→ℝ)
    (X:SourceCappedCandidate M T J z q p) (Y:SourceCappedCandidate M T J' (h*z) q p') :
    p=p' ∧ J=J' ∧ h∈artinParabolic M J := by
  obtain ⟨hp,hj,hfix⟩:=sourceCandidate_fixed_probes M T J J' hT z h hh q p p' X Y
  exact ⟨hp,hj,sourceProbe_parabolic_detector M T J hT h hh hfix⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Candidate
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

lemma sourceCandidate_capped (T J:Set S) (hT:IsSpherical M T) (z:Artin M) (q:ℤ)
    (X:SourceCandidate M T J z q) :
    ∃a∈artinParabolic M J,
      SourceCappedCandidate M T J (a*z) q (sourceHarmonicAt M J z q) := by
  have hJ:=source_spherical_mono M X.proper.subset hT
  obtain ⟨a,ha,hcap⟩:=source_finiteFamily_cap_accessible M J hJ (sourceFrameFamily M z) q
    (by intro H i hi; exact X.cap H i ⟨closedNeighborhood_mono Q
      (unfoldedInclusion_range_mono M X.proper.subset) hi.1,hi.2⟩)
  have hc:∀H,ClassCapOn Q (sourceFrameFamily M (a*z) H) (closedNeighborhood Q (U T)) q := by
    intro H
    dsimp only
    rw [unfoldedInclusion_range M T]
    apply source_cap_closed_of_cap_parts M T J X.proper.subset _ q
    · rw [sourceFrameFamily_mul]; exact hcap H
    · rw [sourceFrameFamily_mul]
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
    exact sourceHarmonicAt_harmonic M J hJ z q ⟨.inl (j:S),⟨j,j.property,rfl⟩⟩
  · intro v hv
    rw [sourceMultiplicity_exterior M J a ha z v hv q,sourceHarmonicAt_outside M J z q v hv]
  · rw [hC]
    exact X.negative
  · intro b hb hbc j
    apply X.representatives (b*(a*z)) _ hbc j
    change b*(a*z)*z⁻¹∈artinParabolic M J
    simpa only [mul_assoc,mul_inv_cancel,mul_one] using (artinParabolic M J).mul_mem hb ha

theorem sourceCandidate_unique (T J J':Set S) (hT:IsSpherical M T)
    (z h:Artin M) (hh:h∈artinParabolic M T) (q:ℤ)
    (X:SourceCandidate M T J z q) (Y:SourceCandidate M T J' (h*z) q) :
    J=J' ∧ rightCoset M J z=rightCoset M J' (h*z) := by
  obtain ⟨a,ha,hX⟩:=sourceCandidate_capped M T J hT z q X
  obtain ⟨b,hb,hY⟩:=sourceCandidate_capped M T J' hT (h*z) q Y
  let k:=b*h*a⁻¹
  have hk:k∈artinParabolic M T := (artinParabolic M T).mul_mem
    ((artinParabolic M T).mul_mem (artinParabolic_mono M Y.proper.subset hb) hh)
    ((artinParabolic M T).inv_mem (artinParabolic_mono M X.proper.subset ha))
  have he:k*(a*z)=b*(h*z) := by dsimp [k]; group
  have hY':SourceCappedCandidate M T J' (k*(a*z)) q (sourceHarmonicAt M J' (h*z) q) := by
    rw [he]; exact hY
  obtain ⟨_,hj,hkJ⟩:=sourceCandidate_comparison_parabolic M T J J' hT (a*z) k hk q _ _ hX hY'
  subst J'
  have heh:h=b⁻¹*k*a := by dsimp [k]; group
  have hhJ:h∈artinParabolic M J := by
    rw [heh]
    exact (artinParabolic M J).mul_mem ((artinParabolic M J).mul_mem
      ((artinParabolic M J).inv_mem hb) hkJ) ha
  exact ⟨rfl,(rightCoset_mul_eq M J h z hhJ).symm⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_MultiplicityZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CosetExteriorCap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
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

lemma sourceCoset_exterior_cap (P:Deligne M) (x z:Artin M) (hx:x∈P.val.2) (hz:z∈P.val.2)
    (U:Set (FusionVertex (V:=S⊕Unit) m)) (hU:∀α∈U,α.1∉Sum.inl '' P.val.1) (q:ℤ)
    (h:∀H,ClassCapOn Q (sourceFrameFamily M x H) U q) :
    ∀H,ClassCapOn Q (sourceFrameFamily M z H) U q := by
  have hg:z*x⁻¹∈artinParabolic M P.val.1 := by
    rw [←sourceCoset_eq M P x hx] at hz
    exact hz
  have he:z=(z*x⁻¹)*x:=by group
  intro H
  rw [he,sourceFrameFamily_mul]
  exact sourceArtinAction_cap_exterior M P.val.1 _ hg _ U hU q (h H)

lemma sourceCoset_exterior_multiplicity (P:Deligne M) (x z:Artin M) (hx:x∈P.val.2) (hz:z∈P.val.2)
    (v:S⊕Unit) (hv:v∉Sum.inl '' P.val.1) (q:ℤ) :
    sourceMultiplicity M z q v=sourceMultiplicity M x q v := by
  have hg:z*x⁻¹∈artinParabolic M P.val.1 := by
    rw [←sourceCoset_eq M P x hx] at hz
    exact hz
  have he:z=(z*x⁻¹)*x:=by group
  rw [he]
  exact sourceMultiplicity_exterior M P.val.1 _ hg x v hv q

lemma sourceCosetVector_open_at (P:Deligne M) (z:Artin M) (hz:z∈P.val.2)
    (v:S⊕Unit) (hv:v∉Sum.inl '' P.val.1) (q:ℤ) :
    sourceCosetVector M P q v=sourceMultiplicity M z q v := by
  rw [sourceCosetVector_eq M P z hz q]
  exact sourceHarmonicAt_outside M P.val.1 z q v hv

lemma sourceResidue_exterior_cap {strict:Bool} {P X:Deligne M} {q:ℤ}
    (h:SourceResidueAllowed M strict P X q) (x z:Artin M) (hx:x∈P.val.2) (hz:z∈X.val.2)
    (U:Set (FusionVertex (V:=S⊕Unit) m))
    (hE:∀H,ClassCapOn Q (sourceFrameFamily M x H) (U\fusionColorRegion m (Sum.inl '' P.val.1)) q) :
    ∀H,ClassCapOn Q (sourceFrameFamily M z H) (U\fusionColorRegion m (Sum.inl '' X.val.1)) q := by
  have hout:=sourceCoset_exterior_cap M P x z hx (h.1.le.2 hz)
    (U\fusionColorRegion m (Sum.inl '' P.val.1)) (fun α hα=>hα.2) q hE
  intro H
  rw [classCapOn_iff_level_zero]
  intro α hα k hk
  by_cases hp:α.1∈Sum.inl '' P.val.1
  · obtain ⟨i,hi,hei⟩:=hp
    have hxi:i∉X.val.1:=fun hh=>hα.2 ⟨i,hh,hei⟩
    have hzero:= (h.2 i hi hxi).1 k hk
    rw [sourceCosetVector_open_at M X z hz _ (by
      rintro ⟨j,hj,hh⟩;exact hxi ((Sum.inl_injective hh) ▸ hj))] at hzero
    change classLevelArray Q (sourceFrameFamily M z H) ((α.1,α.2),k)=0
    rw [←hei]
    exact (sourceMultiplicity_zero_iff M z k _).mp hzero H α.2
  · exact (classCapOn_iff_level_zero Q _ _ _).mp (hout H) α ⟨hα.1,hp⟩ k hk

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CartanCommutingZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
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

lemma sourceCosetVector_block (B C:Set S) (hT:IsSpherical M (B∪C))
    (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) (k:ℤ) (i:S) (hi:i∈B) :
    sourceCosetVector M (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) k (.inl i)=
      sourceCosetVector M (sourceCoset M (B∪C) hT x) k (.inl i) := by
  let P:=sourceCoset M (B∪C) hT x
  let R:=sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x
  apply harmonic_block_eq (framedCartan M) (Sum.inl '' B) (Sum.inl '' C)
    (framed_spherical_posDef M B (source_spherical_mono M Set.subset_union_left hT))
    (sourceCosetVector M R k) (sourceCosetVector M P k)
    (sourceCosetVector_harmonic M R k)
    (fun j=>sourceCosetVector_harmonic M P k ⟨j,Set.image_mono Set.subset_union_left j.property⟩)
    ?_ ?_ (.inl i) ⟨i,hi,rfl⟩
  · rintro _ ⟨s,hs,rfl⟩ _ ⟨t,ht,rfl⟩
    exact sourceCartan_commuting_zero M s t (hc s hs t ht)
  · intro j hjB hjC
    rw [sourceCosetVector_open_at M R x (rightCoset_self M B x) j hjB,
      sourceCosetVector_open_at M P x (rightCoset_self M (B∪C) x) j (by
        rintro ⟨s,hs,rfl⟩
        rcases hs with hs|hs
        · exact hjB ⟨s,hs,rfl⟩
        · exact hjC ⟨s,hs,rfl⟩)]

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CosetVectorNullPatch
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
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

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_TieCode
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueActive
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceResidueActive_misses {P X:Deligne M} {q:ℤ} (hx:X≤P)
    (hh:sourceResidueHeight M P X q<0) :
    ∃i∈P.val.1,i∉X.val.1 ∧ i∉sourceResidueActive M P X q := by
  by_contra hn
  have hv:sourceCosetVector M P q≤ sourceCosetVector M X q:=by
    apply sourceCosetVector_upper_antitone_int M hx q
    intro i hi hxi
    by_contra hr
    exact hn ⟨i,hi,hxi,fun hd=>hr hd.2.2⟩
  have hnon:0≤ sourceResidueHeight M P X q:=
    Finset.sum_nonneg (fun i _=>sub_nonneg.mpr (hv (.inl i)))
  exact (not_lt_of_ge hnon) hh

lemma sourceResidueUpperTop_mem {P X:Deligne M} {q:ℤ} (hx:X≤P)
    (hh:sourceResidueHeight M P X q<0) (hd:(sourceResidueActive M P X q).Nonempty) :
    X < sourceResidueUpperTop M P X q hx ∧ sourceResidueUpperTop M P X q hx<P ∧
      sourceResidueHeight M P (sourceResidueUpperTop M P X q hx) q≤ sourceResidueHeight M P X q := by
  have hl:X≤ sourceResidueUpperTop M P X q hx:=by
    calc
      X=sourceCoset M X.val.1 X.property.1 (sourceCosetRepresentative M X):=
        (sourceCoset_eq M X _ (sourceCosetRepresentative_mem M X)).symm
      _≤ sourceResidueUpperTop M P X q hx:=sourceCoset_le M Set.subset_union_left _
  have hp:sourceResidueUpperTop M P X q hx≤P:=by
    calc
      sourceResidueUpperTop M P X q hx≤ sourceCoset M P.val.1 P.property.1 (sourceCosetRepresentative M X):=
        sourceCoset_le M (fun _ hi=>hi.elim (fun h=>hx.1 h) (fun h=>h.1)) _
      _=P:=sourceCoset_eq M P _ (hx.2 (sourceCosetRepresentative_mem M X))
  refine ⟨lt_of_le_of_ne hl ?_,lt_of_le_of_ne hp ?_,sourceResidueUpper_active M hl (fun _ hi hn=>hi.resolve_left hn)⟩
  · intro he
    obtain ⟨i,hi⟩:=hd
    have ht:=congrArg (fun K:Deligne M=>K.val.1) he
    have hiTop:i∈(sourceResidueUpperTop M P X q hx).val.1:=Or.inr hi
    rw [←ht] at hiTop
    exact hi.2.1 hiTop
  · intro he
    obtain ⟨i,hi,hxOut,hdOut⟩:=sourceResidueActive_misses M hx hh
    have ht:=congrArg (fun K:Deligne M=>K.val.1) he
    have hiTop:i∈(sourceResidueUpperTop M P X q hx).val.1:=by rw [ht];exact hi
    exact hiTop.elim hxOut hdOut

theorem sourceResidueEarlierUpper_contractible {P X:Deligne M} {q:ℤ} (hx:X≤P)
    (hh:sourceResidueHeight M P X q<0) (h:Nonempty (SourceResidueEarlierUpper M P X q)) :
    ContractibleSpace |CategoryTheory.nerve (SourceResidueEarlierUpper M P X q)| := by
  let R:=Classical.choice h
  obtain ⟨i,_,hi⟩:=sourceResidueUpper_meets M R.property.1 R.property.2.1.le R.property.2.2
  let c:SourceResidueEarlierUpper M P X q:=⟨sourceResidueUpperTop M P X q hx,
    sourceResidueUpperTop_mem M hx hh ⟨i,hi⟩⟩
  exact nerve_contractible_of_order_clip (sourceResidueUpperRetraction M P X q) c
    (by intro R; change sourceResidueUpperClip M P X R q≤R.val
        exact sourceResidueUpperClip_le M R.property.1.le)
    (fun R=>show sourceResidueUpperClip M P X R q≤ sourceResidueUpperTop M P X q hx from
      sourceCoset_le M Set.inter_subset_right _)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueSingleOpen
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceResidue_single_open {strict:Bool} (P:Deligne M) (z:Artin M) (hz:z∈P.val.2)
    (q:ℤ) (j:S) (hj:j∈P.val.1)
    (hcap:∀k:ℤ,q<k→sourceMultiplicity M z k (.inl j)=0)
    (hbound:if strict then sourceMultiplicity M z q (.inl j) < sourceCosetVector M P q (.inl j)
      else sourceMultiplicity M z q (.inl j)≤ sourceCosetVector M P q (.inl j)) :
    Nonempty (SourceResidue M strict P q) := by
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
  have hvec(k:ℤ):sourceCosetVector M R k (.inl j)=sourceMultiplicity M z k (.inl j):=
    sourceCosetVector_open_at M R z hrz _ (by
      rintro ⟨i,hi,he⟩;exact hn ((Sum.inl_injective he) ▸ hi)) k
  simpa only [hvec] using And.intro hcap hbound

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueActiveEmpty
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
attribute [-simp] _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.sourceCosetProfile_apply
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
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

lemma sourceResidue_source_active_empty {P X:Deligne M} {q:ℤ} (hx:X≤P)
    (hh:sourceResidueHeight M P X q<0)
    (hu:¬Nonempty (SourceResidueEarlierUpper M P X q)) :
    sourceResidueActive M P X q=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro i hi
  apply hu
  exact ⟨sourceResidueUpperTop M P X q hx,sourceResidueUpperTop_mem M hx hh ⟨i,hi⟩⟩

lemma sourceResidue_source_candidate {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:SourceResidueAllowed M strict P X q) (x:Artin M) (hx:x∈P.val.2)
    (hboundary:∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (U P.val.1)\U P.val.1) q)
    (hh:sourceResidueHeight M P X q<0)
    (hu:¬Nonempty (SourceResidueEarlierUpper M P X q))
    (hl:¬Nonempty (SourceResidue M true X q)) :
    SourceCandidate M P.val.1 X.val.1 (sourceCosetRepresentative M X) q := by
  have ha:=sourceResidue_source_active_empty M hX.1.le hh hu
  let z:=sourceCosetRepresentative M X
  have hz:=sourceCosetRepresentative_mem M X
  refine ⟨deligne_lt_type M hX.1,?_,?_,?_⟩
  · have he:=sourceResidue_exterior_cap M hX x z hx hz (closedNeighborhood Q (U P.val.1))
      (by simpa only [←unfoldedInclusion_range] using hboundary)
    simpa only [←unfoldedInclusion_range] using he
  · intro i hi hn
    change (framedCartan M *ᵥ sourceCosetVector M X q) (.inl i)<0
    by_contra hr
    have hm:i∈sourceResidueActive M P X q:=⟨hi,hn,le_of_not_gt hr⟩
    rw [ha] at hm
    exact hm
  · intro y hy hcap j
    have hy':y∈X.val.2:=by rw [sourceCosetRepresentative_spec];exact hy
    change sourceCosetVector M X q (.inl (j:S))≤ sourceMultiplicity M y q (.inl (j:S))
    by_contra hn
    apply hl
    apply sourceResidue_single_open M X y hy' q j j.property
    · intro k hk
      exact sourceMultiplicity_cap_zero M P.val.1 y q k hk hcap j (hX.1.le.1 j.property)
    · exact lt_of_not_ge hn

theorem sourceResidue_negative_sources_unique {strict:Bool} {P X Y:Deligne M} {q:ℤ}
    (hX:SourceResidueAllowed M strict P X q) (hY:SourceResidueAllowed M strict P Y q)
    (x:Artin M) (hx:x∈P.val.2)
    (hboundary:∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (U P.val.1)\U P.val.1) q)
    (hhX:sourceResidueHeight M P X q<0) (hhY:sourceResidueHeight M P Y q<0)
    (huX:¬Nonempty (SourceResidueEarlierUpper M P X q))
    (huY:¬Nonempty (SourceResidueEarlierUpper M P Y q))
    (hlX:¬Nonempty (SourceResidue M true X q))
    (hlY:¬Nonempty (SourceResidue M true Y q)) : X=Y := by
  let z:=sourceCosetRepresentative M X
  let w:=sourceCosetRepresentative M Y
  let g:=w*z⁻¹
  have hz:z∈P.val.2:=hX.1.le.2 (sourceCosetRepresentative_mem M X)
  have hw:w∈P.val.2:=hY.1.le.2 (sourceCosetRepresentative_mem M Y)
  have hg:g∈artinParabolic M P.val.1:=by
    rw [←sourceCoset_eq M P z hz] at hw
    exact hw
  have he:g*z=w:=by dsimp [g];group
  have hcX:=sourceResidue_source_candidate M hX x hx hboundary hhX huX hlX
  have hcY:=sourceResidue_source_candidate M hY x hx hboundary hhY huY hlY
  obtain ⟨ht,hc⟩:=sourceCandidate_unique M P.val.1 X.val.1 Y.val.1 P.property.1 z g hg q hcX
    (by simpa only [he] using hcY)
  apply Subtype.ext
  apply Prod.ext ht
  rw [sourceCosetRepresentative_spec,sourceCosetRepresentative_spec]
  simpa only [he] using hc

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueHeightZeroVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceResidue_zero_exterior {P X:Deligne M} {q:ℤ}
    (h:SourceResidueAllowed M false P X q) (hh:sourceResidueHeight M P X q=0)
    (x z:Artin M) (hx:x∈P.val.2) (hz:z∈X.val.2) (I:Set S) (hPI:P.val.1⊆I)
    (c:S⊕Unit→ℝ) (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→sourceMultiplicity M x q v=c v) :
    ∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' X.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→sourceMultiplicity M z q v=c v := by
  intro v hv
  by_cases hp:v∈Sum.inl '' P.val.1
  · obtain ⟨i,hi,rfl⟩:=hp
    have hn:(Sum.inl i:S⊕Unit)∉Sum.inl '' X.val.1:=by
      rcases hv with hv|hv
      · exact hv.2
      · exact False.elim (hv.1 ⟨i,hPI hi,rfl⟩)
    rw [←sourceCosetVector_open_at M X z hz _ hn q,sourceResidueHeight_zero_vector M h hh]
    exact sourceCosetVector_of_null_patch M P x hx I hPI q c hcNull hdata i hi
  · rw [sourceCoset_exterior_multiplicity M P x z hx (h.1.le.2 hz) v hp q]
    apply hdata v
    rcases hv with hv|hv
    · exact Or.inl ⟨hv.1,hp⟩
    · exact Or.inr hv

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueRank
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceResidueKey_injective (strict:Bool) (P:Deligne M) (q:ℤ) :
    Function.Injective (sourceResidueKey M strict P q) := by
  intro X Y h
  apply Subtype.ext
  apply sourceTieCode_injective M
  exact congrArg (fun z:Lex (ℕ × Lex (ℕ×ℕ))=>(ofLex (ofLex z).2).2) h

theorem sourceResidueEarlier_wellFounded (strict:Bool) (P:Deligne M) (q:ℤ) :
    WellFounded (SourceResidueEarlier M strict P q) :=
  InvImage.wf (sourceResidueKey M strict P q) wellFounded_lt

lemma sourceResidueEarlier_upper_zero {P:Deligne M} {q:ℤ}
    (X Y:SourceResidue M false P q) (h:X.val<Y.val) (hh:sourceResidueHeight M P X q=0) :
    ¬SourceResidueEarlier M false P q Y X := by
  have hv:sourceCosetVector M X q=sourceCosetVector M P q:=sourceResidueHeight_zero_vector M X.property hh
  have heV:sourceCosetVector M Y q=sourceCosetVector M X q:=by
    apply sourceCosetVector_eq_of_upper_rows M h.le q
    intro i hi _
    rw [hv]
    exact sourceCosetVector_harmonic M P q ⟨.inl i,⟨i,Y.property.1.le.1 hi,rfl⟩⟩
  have he:sourceResidueHeight M P Y q=0:=by
    unfold sourceResidueHeight at hh ⊢
    rw [heV]
    exact hh
  rw [sourceResidueEarlier_iff,he,hh]
  have hn:X.val.val.1.ncard<Y.val.val.1.ncard:=Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)
  simp only [sourceResidueSecondary,he,hh,lt_self_iff_false,ite_false, if_false,false_or,true_and]
  omega

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueEarlierLowerIso
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceResidueEarlier_total (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:SourceResidue M strict P q) (h:X≠Y) :
    SourceResidueEarlier M strict P q X Y ∨ SourceResidueEarlier M strict P q Y X := by
  exact lt_or_gt_of_ne (fun he=>h (sourceResidueKey_injective M strict P q he))

lemma sourceResidue_upper_weights_contractible {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:SourceResidue M strict P q) (hh:sourceResidueHeight M P X q<0)
    (hn:Nonempty (WeightEarlierUpper (SourceResidueEarlier M strict P q) X)) :
    ContractibleSpace (OrderWeights (WeightEarlierUpper (SourceResidueEarlier M strict P q) X)) := by
  let e:=sourceResidueEarlierUpperIso M X hh
  have hc:=sourceResidueEarlierUpper_contractible M X.property.1.le hh (hn.map e)
  have hw:ContractibleSpace (OrderWeights (SourceResidueEarlierUpper M P X q)):=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp hc
  exact (weightHomeomorph e).contractibleSpace_iff.mpr hw

lemma sourceResidue_emptyLink_upper {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:SourceResidue M strict P q) (hh:sourceResidueHeight M P X q<0)
    (hn:¬Nonempty (WeightEarlierLink (SourceResidueEarlier M strict P q) X)) :
    ¬Nonempty (SourceResidueEarlierUpper M P X q) := by
  intro h
  obtain ⟨Y⟩:=h.map (sourceResidueEarlierUpperIso M X hh).symm
  exact hn ⟨Y.val,Y.property.1,Or.inr Y.property.2.le⟩

lemma sourceResidue_emptyLink_lower {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:SourceResidue M strict P q) (hh:sourceResidueHeight M P X q<0)
    (hn:¬Nonempty (WeightEarlierLink (SourceResidueEarlier M strict P q) X)) :
    ¬Nonempty (SourceResidue M true X q) := by
  intro h
  obtain ⟨Y⟩:=h.map (sourceResidueLowerInclusion M X.property)
  let Z:=(sourceResidueEarlierLowerIso M X hh).symm Y
  exact hn ⟨Z.val,Z.property.1,Or.inl Z.property.2.le⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_OrderWeightsContractibleUnique
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_DeligneRankBound
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_EligibleFactor
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

theorem sourceEligibleProduct_contractible (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (h:ContractibleSpace (OrderWeights
      {V:SourceEligibleWithin M Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) //V≠⊤})) :
    ContractibleSpace (OrderWeights {V:SourceEligibleWithin M Ref (sourceCoset M (B∪C) hT x) //V≠⊤}) := by
  let e:=sourceEligibleProductPuncture M Ref B C hT hd hc x
  apply (weightHomeomorph e).contractibleSpace_iff.mp
  apply binaryProductBoundary_contractible (fun V=>(e V).val.val.val.1.ncard) (Fintype.card S)
    (fun V=>sourceDeligne_rank_bound M (e V).val.val) ?_ h
  intro V W hVW
  exact sourceDeligne_rank_strictMono M (e.strictMono hVW)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_EligibleLeftNonempty
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CategoryTheory Simplicial ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceBlock_allEligible_contractible (P:Deligne M) (B:Set S) (hB:B⊆P.val.1)
    (hc:∀s∈B,∀t∈P.val.1\B,M s t=2) (x:Artin M) (hx:x∈P.val.2)
    (h:ContractibleSpace (OrderWeights
      {V:SourceEligibleWithin M P (sourceCoset M B (source_spherical_mono M hB P.property.1) x) //V≠⊤})) :
    ContractibleSpace (OrderWeights (SourceAllEligibleLower M P)) := by
  let C:=P.val.1\B
  have hBC:B∪C=P.val.1:=Set.union_sdiff_cancel hB
  have hT:IsSpherical M (B∪C):=by rw [hBC];exact P.property.1
  have hd:Disjoint B C:=Set.disjoint_left.mpr (fun _ h h'=>h'.2 h)
  have he:sourceCoset M (B∪C) hT x=P:=by
    simpa only [hBC] using sourceCoset_eq M P x hx
  have hh:=sourceEligibleProduct_contractible M P B C hT hd hc x h
  rw [he] at hh
  exact (weightHomeomorph (sourceEligiblePuncture M P)).contractibleSpace_iff.mp hh

lemma sourceBlock_vector (P:Deligne M) (B:Set S) (hB:B⊆P.val.1)
    (hc:∀s∈B,∀t∈P.val.1\B,M s t=2) (x:Artin M) (hx:x∈P.val.2) (q:ℤ) :
    ∀i∈B,sourceCosetVector M (sourceCoset M B (source_spherical_mono M hB P.property.1) x) q (.inl i)=
      sourceCosetVector M P q (.inl i) := by
  have hBC:B∪(P.val.1\B)=P.val.1:=Set.union_sdiff_cancel hB
  have hT:IsSpherical M (B∪(P.val.1\B)):=by rw [hBC];exact P.property.1
  have he:sourceCoset M (B∪(P.val.1\B)) hT x=P:=by simpa only [hBC] using sourceCoset_eq M P x hx
  intro i hi
  simpa only [he] using sourceCosetVector_block M B (P.val.1\B) hT hc x q i hi

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_TypeComponent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
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

lemma sourceCosetVector_positive_neighbor (P:Deligne M) (k:ℤ) (i:S) (hi:i∈P.val.1)
    (j:S⊕Unit) (hij:framedCartan M (.inl i) j<0)
    (hj:0 < sourceCosetVector M P k j) : 0 < sourceCosetVector M P k (.inl i) := by
  apply harmonic_positive_neighbor_at (framedCartan M) (framedCartan_off M)
    (sourceCosetVector M P k) (sourceCosetVector_nonneg M P k) _ hij hj
  exact (sourceCosetVector_harmonic M P k ⟨.inl i,⟨i,hi,rfl⟩⟩).ge

lemma sourcePositiveComponent_type_neighbor (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0 < sourceCosetVector M P q i) (j:S⊕Unit)
    (hj:j∈sourcePositiveComponent M (sourceCosetVector M P q) i) (k:S) (hk:k∈P.val.1)
    (hjk:framedCartan M j (.inl k)<0) :
    (.inl k:S⊕Unit)∈sourcePositiveComponent M (sourceCosetVector M P q) i := by
  have hp:=sourcePositiveComponent_positive M _ i hi j hj
  have hkp:=sourceCosetVector_positive_neighbor M P q k hk j (by rwa [framedCartan_symm]) hp
  exact hj.tail ⟨hp,hjk,hkp⟩

lemma sourcePositiveBlock_commutes (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0 < sourceCosetVector M P q i) (j k:S) (_hj:j∈P.val.1)
    (hjI:(.inl j:S⊕Unit)∈sourcePositiveComponent M (sourceCosetVector M P q) i)
    (hk:k∈P.val.1) (hkI:(.inl k:S⊕Unit)∉sourcePositiveComponent M (sourceCosetVector M P q) i) :
    M j k=2 := by
  by_contra hn
  exact hkI (sourcePositiveComponent_type_neighbor M P q i hi (.inl j) hjI k hk
    (framedCartan_neg_of_label_ne_two M j k (by rintro rfl;exact hkI hjI) hn))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_NeighborhoodProject
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

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_NullPatch2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

omit [Fintype S] [LinearOrder S] in
lemma sourcePositiveComponent_boundary_zero (p:S⊕Unit→ℝ) (hp:∀v,0≤p v)
    (i:S⊕Unit) (hi:0<p i) (v:S⊕Unit) (ho:v∉sourcePositiveComponent M p i)
    (hn:∃u∈sourcePositiveComponent M p i,framedCartan M v u<0) : p v=0 := by
  by_contra hz
  have hv:0<p v:=lt_of_le_of_ne (hp v) (Ne.symm hz)
  obtain ⟨u,hu,huv⟩:=hn
  exact ho (hu.tail ⟨sourcePositiveComponent_positive M p i hi u hu,
    by rwa [framedCartan_symm],hv⟩)

lemma sourceNullSign_image (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hn:SourceNullSign M (fun d=>sourceCosetVector M P d) q i) :
    Sum.inl '' {j:S | (.inl j:S⊕Unit)∈sourcePositiveComponent M (sourceCosetVector M P q) i}=
      sourcePositiveComponent M (sourceCosetVector M P q) i := by
  ext v
  constructor
  · rintro ⟨j,hj,rfl⟩;exact hj
  · intro hv
    rcases v with j|u
    · exact ⟨j,hv,rfl⟩
    · cases u;exact (hn.2.1 hv).elim

lemma sourceNullSign_peak (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0 < sourceCosetVector M P q i)
    (hn:SourceNullSign M (fun d=>sourceCosetVector M P d) q i)
    (j:S) (hj:j∈P.val.1)
    (hjI:(.inl j:S⊕Unit)∈sourcePositiveComponent M (sourceCosetVector M P q) i) :
    sourcePeak M P j=q := by
  apply le_antisymm
  · by_contra h
    have hh:q < sourcePeak M P j:=lt_of_not_ge h
    have hz:=hn.2.2.2 (.inl j) (Or.inl hjI) (sourcePeak M P j) hh
    exact (ne_of_gt (sourcePeak_positive M P j hj)) hz
  · exact sourcePeak_bound M P j q (ne_of_gt (sourcePositiveComponent_positive M _ i hi _ hjI))

lemma sourceNullSign_sign (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0 < sourceCosetVector M P q i)
    (hn:SourceNullSign M (fun d=>sourceCosetVector M P d) q i)
    (v:S⊕Unit) (hv:v∈sourcePositiveComponent M (sourceCosetVector M P q) i) :
    sourceCosetSign M P q v=1 := by
  have he:=sourcePositiveComponent_eq M (sourceCosetVector M P q) v
    (sourcePositiveComponent M (sourceCosetVector M P q) i)
    (sourcePositiveComponent_spec M _ i hi) hv
  have hnv:SourceNullSign M (fun d=>sourceCosetVector M P d) q v:=by
    unfold SourceNullSign
    rw [he]
    exact hn
  change sourceSignAt M _ q v=1
  rw [sourceSignAt,ite_eq_right (ne_of_gt (sourcePositiveComponent_positive M _ i hi v hv)),ite_eq_left hnv]

lemma sourceNullPatch_nonneg (P:Deligne M) (q:ℕ) (i v:S⊕Unit) : 0 ≤ sourceNullPatch M P q i v := by
  unfold sourceNullPatch
  split_ifs
  · exact sourceCosetVector_nonneg M P q v
  · rfl

lemma sourceNullPatch_row (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0 < sourceCosetVector M P q i)
    (hn:SourceNullSign M (fun d=>sourceCosetVector M P d) q i)
    (v:S⊕Unit) (hv:v∈sourcePositiveComponent M (sourceCosetVector M P q) i) :
    (framedCartan M *ᵥ sourceNullPatch M P q i) v=0 := by
  trans (framedCartan M *ᵥ sourceCosetVector M P q) v
  · apply Finset.sum_congr rfl
    intro u _
    by_cases hu:u∈sourcePositiveComponent M (sourceCosetVector M P q) i
    · simp only [sourceNullPatch,ite_eq_left hu]
    · simp only [sourceNullPatch,ite_eq_right hu,MulZeroClass.mul_zero]
      by_cases hh:framedCartan M v u<0
      · rw [sourcePositiveComponent_boundary_zero M _ (sourceCosetVector_nonneg M P q) i hi u hu
          ⟨v,hv,by rwa [framedCartan_symm]⟩,MulZeroClass.mul_zero]
      · have he:framedCartan M v u=0:=le_antisymm (framedCartan_off M v u
          (by rintro rfl;exact hu hv)) (le_of_not_gt hh)
        rw [he,MulZeroClass.zero_mul]
  · exact hn.2.2.1 v hv

lemma sourcePositive_exterior (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0 < sourceCosetVector M P q i) (v:S⊕Unit)
    (hv:v∈sourceClosedRegion M (sourcePositiveComponent M (sourceCosetVector M P q) i))
    (ho:v∉Sum.inl '' (P.val.1∩{j:S | (.inl j:S⊕Unit)∈sourcePositiveComponent M (sourceCosetVector M P q) i})) :
    v∉Sum.inl '' P.val.1 := by
  rintro ⟨j,hj,rfl⟩
  apply ho
  refine ⟨j,⟨hj,?_⟩,rfl⟩
  rcases hv with hv|⟨u,hu,huj⟩
  · exact hv
  · exact sourcePositiveComponent_type_neighbor M P q i hi u hu j hj (by rwa [framedCartan_symm])

lemma sourcePositive_block_cap (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0 < sourceCosetVector M P q i)
    (hn:SourceNullSign M (fun d=>sourceCosetVector M P d) q i) (x:Artin M) (hx:x∈P.val.2) :
    let I:Set S:={j | (.inl j:S⊕Unit)∈sourcePositiveComponent M (sourceCosetVector M P q) i}
    ∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
        fusionColorRegion m (Sum.inl '' (P.val.1∩I))) q := by
  intro I H
  rw [classCapOn_iff_level_zero]
  intro α hα k hk
  have hv:=sourceNeighborhood_project M (Sum.inl '' I) hα.1
  rw [sourceNullSign_image M P q i hn] at hv
  have hout:=sourcePositive_exterior M P q i hi α.1 hv hα.2
  have he:(k.toNat:ℤ)=k:=Int.toNat_of_nonneg (by omega)
  have hz:=hn.2.2.2 α.1 hv k.toNat (by omega)
  dsimp only at hz
  rw [he,sourceCosetVector_open_at M P x hx α.1 hout] at hz
  exact (sourceMultiplicity_zero_iff M x k α.1).mp hz H α.2

lemma sourcePositive_block_values (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0 < sourceCosetVector M P q i)
    (hn:SourceNullSign M (fun d=>sourceCosetVector M P d) q i) (x:Artin M) (hx:x∈P.val.2) :
    let I:Set S:={j | (.inl j:S⊕Unit)∈sourcePositiveComponent M (sourceCosetVector M P q) i}
    ∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' (P.val.1∩I)) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→
      sourceMultiplicity M x q v=sourceNullPatch M P q i v := by
  intro I v hv
  have hI:Sum.inl '' I=sourcePositiveComponent M (sourceCosetVector M P q) i:=sourceNullSign_image M P q i hn
  rw [hI] at hv
  rcases hv with ⟨hv,ho⟩|⟨ho,hv⟩
  · rw [←sourceCosetVector_open_at M P x hx v (sourcePositive_exterior M P q i hi v (Or.inl hv) ho)]
    simp only [sourceNullPatch,ite_eq_left hv]
  · have hoB:v∉Sum.inl '' (P.val.1∩I):=by
      intro h
      exact ho (hI ▸ Set.image_mono Set.inter_subset_right h)
    rw [←sourceCosetVector_open_at M P x hx v (sourcePositive_exterior M P q i hi v (Or.inr hv) hoB)]
    rw [sourceNullPatch,ite_eq_right ho]
    exact sourcePositiveComponent_boundary_zero M _ (sourceCosetVector_nonneg M P q) i hi v ho hv

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ResidueZeroLowerIso
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
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
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

lemma sourceResidueZeroUpper_empty {P:Deligne M} {q:ℤ}
    (X:SourceResidue M false P q) (hh:sourceResidueHeight M P X q=0) :
    ¬Nonempty (WeightEarlierUpper (SourceResidueEarlier M false P q) X) := by
  rintro ⟨Y⟩
  exact sourceResidueEarlier_upper_zero M X Y.val Y.property.2 hh Y.property.1

lemma sourceResidue_special_boundary {P:Deligne M} {q:ℤ}
    (I:Set S) (hPI:P.val.1⊆I) (x:Artin M)
    (hE:∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \fusionColorRegion m (Sum.inl '' P.val.1)) q) :
    ∀H,ClassCapOn Q (sourceFrameFamily M x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q := by
  intro H
  apply ClassCapOn.mono Q (hE H)
  intro α hα
  refine ⟨closedNeighborhood_mono Q ?_ hα.1,?_⟩
  · change Set.range (unfoldedInclusion M P.val.1) ⊆ _
    rw [unfoldedInclusion_range]
    exact fun _ h=>(Set.image_mono hPI) h
  · simpa only [←unfoldedInclusion_range] using hα.2

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_SpecialResidueRank
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder _root_.OAI.HarmonicArtin.sourceEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory _root_.Matrix _root_.OAI.Matrix
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

private theorem specialResidue_rank (n:ℕ) : ∀(P:Deligne M),P.val.1.ncard=n →
    ∀(x:Artin M),x∈P.val.2 → ∀(I:Set S),I.Nonempty → P.val.1⊆I → ∀(q:ℤ),0<q →
    ∀(c:S⊕Unit→ℝ),(∀v,0 ≤ c v) → (∀v,v∉Sum.inl '' I→c v=0) →
    (∀v,v∈Sum.inl '' I→0 < c v) → (∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0) →
    (∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \fusionColorRegion m (Sum.inl '' P.val.1)) q) →
    (∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→sourceMultiplicity M x q v=c v) →
    ContractibleSpace (OrderWeights (SourceResidue M false P q)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hn x hx I hI hPI q hq c hc hcSupp hcPos hcNull hE hdata
    let r:=SourceResidueEarlier M false P q
    have hb:=sourceResidue_special_boundary M I hPI x hE
    have hzcont:∀(X:SourceResidue M false P q),sourceResidueHeight M P X q=0 →
        ContractibleSpace (OrderWeights (SourceResidue M false X q)):=by
      intro X hh
      have hrank:X.val.val.1.ncard<n:=by
        rw [←hn]
        exact sourceDeligne_rank_strictMono M X.property.1
      exact ih X.val.val.1.ncard hrank X.val rfl (sourceCosetRepresentative M X)
        (sourceCosetRepresentative_mem M X) I hI (X.property.1.le.1.trans hPI) q hq c hc hcSupp hcPos hcNull
        (sourceResidue_exterior_cap M X.property x (sourceCosetRepresentative M X) hx
          (sourceCosetRepresentative_mem M X) _ hE)
        (sourceResidue_zero_exterior M X.property hh x (sourceCosetRepresentative M X) hx
          (sourceCosetRepresentative_mem M X) I hPI c hcNull hdata)
    have hneg:∀(X:SourceResidue M false P q),¬Nonempty (WeightEarlierLink r X) →
        sourceResidueHeight M P X q<0:=by
      intro X hX
      rcases lt_or_eq_of_le (sourceResidueHeight_nonpos M X.property) with hh|hh
      · exact hh
      · exfalso
        obtain ⟨Y,hy,hYa⟩:=sourceResidue_zero_ne_lower M P X x hx I hI hPI q hq c hc hcSupp hcPos hcNull hE hdata X.property hh
        exact hX ⟨⟨Y,hYa⟩,sourceResidueEarlier_lower_zero M X _ hy hh,Or.inl hy.le⟩
    apply orderWeights_contractible_unique_source r (sourceResidueEarlier_wellFounded M false P q)
      (sourceResidueEarlier_total M false P q) (fun X=>X.val.val.1.ncard) (Fintype.card S)
      (fun X=>sourceDeligne_rank_bound M X) (by intro X Y h;exact sourceDeligne_rank_strictMono M h)
      ?_ ?_ ?_ (sourceClosedResidue_nonempty M P x hx I hI hPI q hq c hc hcSupp hcPos hcNull hE hdata)
    · intro X hX
      rcases lt_or_eq_of_le (sourceResidueHeight_nonpos M X.property) with hh|hh
      · exact sourceResidue_lower_weights_contractible M X hh x hx hb hX
      · exact (weightHomeomorph (sourceResidueZeroLowerIso M X hh)).contractibleSpace_iff.mpr (hzcont X hh)
    · intro X hX
      rcases lt_or_eq_of_le (sourceResidueHeight_nonpos M X.property) with hh|hh
      · exact sourceResidue_upper_weights_contractible M X hh hX
      · exact False.elim (sourceResidueZeroUpper_empty M X hh hX)
    · intro X Y hX hY
      have hhX:=hneg X hX
      have hhY:=hneg Y hY
      apply Subtype.ext
      exact sourceResidue_negative_sources_unique M X.property Y.property x hx hb hhX hhY
        (sourceResidue_emptyLink_upper M X hhX hX) (sourceResidue_emptyLink_upper M Y hhY hY)
        (sourceResidue_emptyLink_lower M X hhX hX) (sourceResidue_emptyLink_lower M Y hhY hY)

theorem sourceSpecialResidue_contractible (P:Deligne M) (x:Artin M) (hx:x∈P.val.2)
    (I:Set S) (hI:I.Nonempty) (hPI:P.val.1⊆I) (q:ℤ) (hq:0<q)
    (c:S⊕Unit→ℝ) (hc:∀v,0 ≤ c v) (hcSupp:∀v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀v,v∈Sum.inl '' I→0 < c v)
    (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hE:∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \fusionColorRegion m (Sum.inl '' P.val.1)) q)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→sourceMultiplicity M x q v=c v) :
    ContractibleSpace |nerve (SourceResidue M false P q)| :=
  nerveWeightsHomeomorph.contractibleSpace_iff.mpr
    (specialResidue_rank M P.val.1.ncard P rfl x hx I hI hPI q hq c hc hcSupp hcPos hcNull hE hdata)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_NegativeBlockContractible
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped _root_.Matrix _root_.OAI.Matrix
open CategoryTheory Simplicial ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourcePositiveBlock_contractible_oai (P:Deligne M) (q:ℕ) (i:S) (_hi:i∈P.val.1)
    (hp:0 < sourceCosetVector M P q (.inl i))
    (hn:SourceNullSign M (fun d=>sourceCosetVector M P d) q (.inl i)) :
    ContractibleSpace (OrderWeights (SourceAllEligibleLower M P)) := by
  let I:Set S:={j | (.inl j:S⊕Unit)∈sourcePositiveComponent M (sourceCosetVector M P q) (.inl i)}
  let B:=P.val.1∩I
  have hB:B⊆P.val.1:=Set.inter_subset_left
  have hiI:i∈I:=Relation.ReflTransGen.refl
  have hc:∀s∈B,∀t∈P.val.1\B,M s t=2:=by
    intro s hs t ht
    exact sourcePositiveBlock_commutes M P q (.inl i) hp s t hs.1 hs.2 ht.1
      (fun h=>ht.2 ⟨ht.1,h⟩)
  have hpeak:∀j∈B,sourcePeak M P j=q:=fun j hj=>sourceNullSign_peak M P q (.inl i) hp hn j hj.1 hj.2
  have hsg:∀j∈B,sourceCosetSign M P q (.inl j)=if false then -1 else 1:=fun j hj=>
    sourceNullSign_sign M P q (.inl i) hp hn (.inl j) hj.2
  let x:=sourceCosetRepresentative M P
  have hx:=sourceCosetRepresentative_mem M P
  let R:=sourceCoset M B (source_spherical_mono M hB P.property.1) x
  let c:=sourceNullPatch M P q (.inl i)
  have hI:Sum.inl '' I=sourcePositiveComponent M (sourceCosetVector M P q) (.inl i):=
    sourceNullSign_image M P q (.inl i) hn
  have hcSupp:∀v,v∉Sum.inl '' I→c v=0:=by
    intro v hv
    rw [hI] at hv
    exact ite_eq_right hv
  have hcPos:∀v,v∈Sum.inl '' I→0 < c v:=by
    intro v hv
    rw [hI] at hv
    change 0 < sourceNullPatch M P q (.inl i) v
    rw [sourceNullPatch,ite_eq_left hv]
    exact sourcePositiveComponent_positive M _ (.inl i) hp v hv
  have hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0:=by
    intro v hv
    rw [hI] at hv
    exact sourceNullPatch_row M P q (.inl i) hp hn v hv
  have hr:ContractibleSpace (OrderWeights (SourceResidue M false R q)):=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp
      (sourceSpecialResidue_contractible M R x (rightCoset_self M B x) I ⟨i,hiI⟩ Set.inter_subset_right
        q (by exact_mod_cast hn.1) c (sourceNullPatch_nonneg M P q (.inl i)) hcSupp hcPos hcNull
        (sourcePositive_block_cap M P q (.inl i) hp hn x hx)
        (sourcePositive_block_values M P q (.inl i) hp hn x hx))
  let e:=sourceEligibleFactor M P R hB q false hpeak hsg (sourceBlock_vector M P B hB hc x hx q)
  exact sourceBlock_allEligible_contractible M P B hB hc x hx
    ((weightHomeomorph e).contractibleSpace_iff.mpr hr)

end HarmonicArtin

end OAI
end

theorem solution : type_of% @OAI.HarmonicArtin.sourcePositiveBlock_contractible_oai := @OAI.HarmonicArtin.sourcePositiveBlock_contractible_oai
