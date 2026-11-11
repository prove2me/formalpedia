-- Prove2me | solution 1 for OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T20:23:32.581087+00:00
-- url     : https://prove2.me/submissions/4d461264-bb0c-4b46-9296-bbb79c956e68

import Mathlib
import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Topology.MetricSpace.Isometry
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap010
import Definitions.Def_OAIQ236Ap013
import Theorems.Thm_OAI_HarmonicArtin_ParabolicIntersections_relative_descending_lower_connected_s236
import Theorems.Thm_OAI_HarmonicArtin_ParabolicIntersections_spherical_mesh_input_s236
import Theorems.Thm_OAI_HarmonicArtin_ParabolicIntersections_spherical_reduction_s236

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_Cartan
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric

open scoped Classical

variable {S W : Type*} [DecidableEq S] [Group W]

variable [Fintype S]

lemma simple_injective {M : CoxeterMatrix S} (cs : CoxeterSystem M W) :
    Function.Injective cs.simple := by
  intro i j h
  by_contra hij
  have hh := congrArg (fun w => representation cs w (Pi.single i 1) i) h
  simp only [representation_simple,simpleReflection_apply,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,Pi.single_eq_same] at hh
  have hji : (Pi.single j (1:ℝ) : S → ℝ) i = 0 := Pi.single_eq_of_ne hij 1
  have hrow : (Matrix.mulVec (cartan M) (Pi.single i (1:ℝ))) i=2 := by simp [Matrix.mulVec_single]
  rw [hji,hrow] at hh
  norm_num at hh

end HarmonicArtin.Geometric

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

theorem finite_of_all_descents (z : W)
    (hz : ∀ i,cs.length (z*cs.simple i)+1=cs.length z) : Finite W := by
  apply Set.finite_univ_iff.mp
  apply ((List.finite_length_le S (cs.length z)).image cs.wordProd).subset
  intro w _
  obtain ⟨u,hu,he⟩ := cs.exists_isReduced w
  refine ⟨u,?_,he.symm⟩
  change u.length ≤ cs.length z
  rw [← hu.eq,← he]
  exact length_le_of_all_descents cs z hz w

end HarmonicArtin.Geometric

end OAI
end

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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_EmptyTestIndex
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

lemma classNegativeTwist_far (E:BasedComplex Q (K:=K) I) (U:Set V)
    (hE:∀ i,(E.placement i).color∉Q.closedNeighborhood U)
    (α:V) (hα:α∈U) :
    classNegativeTwist Q α (classOfComplex Q E)=classOfComplex Q E :=
  classOfComplex_eq Q (negativeTwistFar Q E U hE α hα)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CosetVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
variable {S : Type u}

 theorem spherical_singleton (M : CoxeterMatrix S) (s : S) : IsSpherical M {s} := by
  have horder : IsOfFinOrder (M.simple s) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, M.toCoxeterSystem.simple_sq s⟩
  unfold IsSpherical coxeterParabolic
  rw [Set.image_singleton, ← Subgroup.zpowers_eq_closure]
  exact horder.finite_zpowers

 theorem rightCoset_empty (M : CoxeterMatrix S) (x : Artin M) :
    rightCoset M ∅ x = {x} := by
  ext g
  simp [rightCoset, artinParabolic, mul_inv_eq_one]

open _root_.Matrix

end HarmonicArtin

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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionOrbitMultiplicity
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
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)

lemma fusionOrbitMultiplicity_nonneg (w:List (V × Bool)) (s:V) (q:ℤ) (v:V) :
    0 ≤ fusionOrbitMultiplicity m d hd hdiag hm w s q v :=
  (Classical.choose_spec (fusionPacketOrbit_count_proportional m d hd hdiag hm w s v q)).1

end HarmonicArtin

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

theorem unfolded_finite (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) :
    Finite (unfoldedMatrix M J).Group := by
  let : Finite (restrictedMatrix M J).Group := restricted_finite M J hJ
  obtain ⟨z,hz⟩ := exists_longest (restrictedMatrix M J).toCoxeterSystem
  apply finite_of_all_descents (unfoldedMatrix M J).toCoxeterSystem (unfoldedHom M J hJ z)
  intro α
  exact (unfoldedHom_right_descent M J hJ z α).mpr
    (all_descents_of_longest (restrictedMatrix M J).toCoxeterSystem z hz α.1)

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
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_WeakPrefix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {B W:Type*} [Group W] {M:CoxeterMatrix B} (cs:CoxeterSystem M W)

lemma weakPrefix_one (a:W) : WeakPrefix cs 1 a := by simp [WeakPrefix]
lemma weakPrefix_length {a b:W} (h:WeakPrefix cs a b) : cs.length a ≤ cs.length b := by
  unfold WeakPrefix at h;omega

lemma weakPrefix_trans {a b c:W} (hab:WeakPrefix cs a b) (hbc:WeakPrefix cs b c) : WeakPrefix cs a c := by
  have hl:=cs.length_mul_le (a⁻¹*b) (b⁻¹*c)
  have he:(a⁻¹*b)*(b⁻¹*c)=a⁻¹*c:=by group
  rw [he] at hl
  have hr:=cs.length_mul_le a (a⁻¹*c)
  rw [mul_inv_cancel_left] at hr
  unfold WeakPrefix at *
  omega

lemma weakPrefix_left_remove {a b:W} (s:B) (ha:WeakPrefix cs (cs.simple s) a)
    (hb:WeakPrefix cs (cs.simple s) b) :
    WeakPrefix cs (cs.simple s*a) (cs.simple s*b) ↔ WeakPrefix cs a b := by
  have hla:=(weakPrefix_simple_iff cs s a).mp ha
  have hlb:=(weakPrefix_simple_iff cs s b).mp hb
  have he:(cs.simple s*a)⁻¹*(cs.simple s*b)=a⁻¹*b:=by group
  unfold WeakPrefix
  rw [he]
  omega

lemma weakPrefix_left_add {g a:W} (s:B) (ha:WeakPrefix cs (cs.simple s) a)
    (hg:WeakPrefix cs g (cs.simple s*a)) :
    WeakPrefix cs (cs.simple s*g) a ∧ cs.length (cs.simple s*g)=cs.length g+1 := by
  have hla:=(weakPrefix_simple_iff cs s a).mp ha
  have hmul:=cs.length_mul_le (cs.simple s*g) (g⁻¹*(cs.simple s*a))
  have he:(cs.simple s*g)*(g⁻¹*(cs.simple s*a))=a:=by
    rw [mul_assoc,mul_inv_cancel_left,cs.simple_mul_simple_cancel_left]
  rw [he] at hmul
  have hstep:=cs.length_simple_mul g s
  have hlen:cs.length (cs.simple s*g)=cs.length g+1:=by unfold WeakPrefix at hg;omega
  refine ⟨?_,hlen⟩
  have hsuf:(cs.simple s*g)⁻¹*a=g⁻¹*(cs.simple s*a):=by rw [mul_inv_rev,cs.inv_simple,mul_assoc]
  unfold WeakPrefix at *
  rw [hsuf,hlen]
  omega

lemma exists_simple_prefix {a:W} (ha:a≠1) : ∃s:B,WeakPrefix cs (cs.simple s) a := by
  obtain ⟨w,hw,he⟩:=cs.exists_isReduced a
  cases w with
  | nil=>simp only [cs.wordProd_nil] at he;exact (ha he).elim
  | cons s w=>
    refine ⟨s,(weakPrefix_simple_iff cs s a).mpr ?_⟩
    have hl:=hw.drop 1
    simp only [List.drop_succ_cons,List.drop_zero] at hl
    rw [he,hw.eq,cs.wordProd_cons,cs.simple_mul_simple_cancel_left,hl.eq]
    rfl

lemma weakPrefix_first_of_reduced (s:B) (w:List B) (h:cs.IsReduced (s::w)) :
    WeakPrefix cs (cs.simple s) (cs.wordProd (s::w)) := by
  apply (weakPrefix_simple_iff cs s _).mpr
  have hr:=h.drop 1
  simp only [List.drop_succ_cons,List.drop_zero] at hr
  rw [h.eq,cs.wordProd_cons,cs.simple_mul_simple_cancel_left,hr.eq]
  rfl

variable [Fintype B]

lemma simple_pair_prefix (s t:B) (hne:s≠t) {a:W}
    (hs:WeakPrefix cs (cs.simple s) a) (ht:WeakPrefix cs (cs.simple t) a) :
    WeakPrefix cs (cs.wordProd (altList s t (M s t))) a ∧
      WeakPrefix cs (cs.simple s) (cs.wordProd (altList s t (M s t))) ∧
      WeakPrefix cs (cs.simple t) (cs.wordProd (altList s t (M s t))) := by
  have hsl:=(weakPrefix_simple_iff cs s a).mp hs
  have htl:=(weakPrefix_simple_iff cs t a).mp ht
  obtain ⟨v,hm,hl,he,he'⟩:=double_descent_prefix cs s t hne a (by omega) (by omega)
  let d:=cs.wordProd (altList s t (M s t))
  have hred:cs.IsReduced (altList s t (M s t)):=by
    have hd:=cs.length_wordProd_le (altList s t (M s t))
    have hh:=cs.length_mul_le d v
    change cs.length (cs.wordProd (altList s t (M s t))*v) ≤ cs.length (cs.wordProd (altList s t (M s t)))+cs.length v at hh
    rw [←he] at hh
    simp only [length_altList] at hd
    change cs.length d=(altList s t (M s t)).length
    rw [length_altList]
    dsimp [d]
    omega
  have hda:WeakPrefix cs d a:=by
    unfold WeakPrefix
    rw [he,inv_mul_cancel_left,hred.eq,length_altList]
    simpa only [he] using hl
  have hsD:WeakPrefix cs (cs.simple s) d:=by
    obtain ⟨n,hn⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : M s t≠0)
    change WeakPrefix cs (cs.simple s) (cs.wordProd (altList s t (M s t)))
    rw [hn,altList_succ] at hred ⊢
    exact weakPrefix_first_of_reduced cs s _ hred
  have htD:WeakPrefix cs (cs.simple t) d:=by
    have hdEq:cs.wordProd (altList s t (M s t))=cs.wordProd (altList t s (M s t)):=altList_braid cs s t
    have htred:cs.IsReduced (altList t s (M s t)):=by
      change cs.length (cs.wordProd (altList t s (M s t)))=(altList t s (M s t)).length
      rw [←hdEq,hred.eq,length_altList,length_altList]
    change WeakPrefix cs (cs.simple t) (cs.wordProd (altList s t (M s t)))
    rw [hdEq]
    obtain ⟨n,hn⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : M s t≠0)
    rw [hn,altList_succ] at htred ⊢
    exact weakPrefix_first_of_reduced cs t _ htred
  exact ⟨hda,hsD,htD⟩

end HarmonicArtin.CoxeterExchange

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_CommonWeakPrefixMaximal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {B W:Type*} [Group W] [Fintype B] {M:CoxeterMatrix B} (cs:CoxeterSystem M W)

omit [Fintype B] in
lemma common_weakPrefix_maximal_remove (a b g:W)
    (hmax:∀x:W,WeakPrefix cs x a→WeakPrefix cs x b→cs.length x ≤ cs.length g)
    (s:B) (hsa:WeakPrefix cs (cs.simple s) a) (hsb:WeakPrefix cs (cs.simple s) b)
    (hsg:WeakPrefix cs (cs.simple s) g) :
    ∀x:W,WeakPrefix cs x (cs.simple s*a)→WeakPrefix cs x (cs.simple s*b)→
      cs.length x ≤ cs.length (cs.simple s*g) := by
  intro x hxa hxb
  obtain ⟨hxa',hl⟩:=weakPrefix_left_add cs s hsa hxa
  have hxb':=(weakPrefix_left_add cs s hsb hxb).1
  have hh:=hmax _ hxa' hxb'
  have hg:=(weakPrefix_simple_iff cs s g).mp hsg
  omega

theorem maximal_common_weakPrefix_greatest (a b g:W)
    (hga:WeakPrefix cs g a) (hgb:WeakPrefix cs g b)
    (hmax:∀x:W,WeakPrefix cs x a→WeakPrefix cs x b→cs.length x ≤ cs.length g) :
    ∀e:W,WeakPrefix cs e a→WeakPrefix cs e b→WeakPrefix cs e g := by
  induction a using (measure cs.length).wf.induction generalizing b g with
  | h a ih=>
    intro e hea heb
    by_cases he:e=1
    · rw [he];exact weakPrefix_one cs g
    obtain ⟨s,hse⟩:=exists_simple_prefix cs he
    have hsa:=weakPrefix_trans cs hse hea
    have hsb:=weakPrefix_trans cs hse heb
    have hsg:WeakPrefix cs (cs.simple s) g:=by
      have hg:g≠1:=by
        intro hg
        have hh:=hmax _ hsa hsb
        rw [hg,cs.length_simple,cs.length_one] at hh
        omega
      obtain ⟨t,htg⟩:=exists_simple_prefix cs hg
      by_cases hts:t=s
      · simpa only [hts] using htg
      have hta:=weakPrefix_trans cs htg hga
      have htb:=weakPrefix_trans cs htg hgb
      let d:=cs.wordProd (altList t s (M t s))
      obtain ⟨hda,htd,hsd⟩:=simple_pair_prefix cs t s hts hta hsa
      have hdb:WeakPrefix cs d b:=(simple_pair_prefix cs t s hts htb hsb).1
      have hga':WeakPrefix cs (cs.simple t*g) (cs.simple t*a):=
        (weakPrefix_left_remove cs t htg hta).mpr hga
      have hgb':WeakPrefix cs (cs.simple t*g) (cs.simple t*b):=
        (weakPrefix_left_remove cs t htg htb).mpr hgb
      have hmax':=common_weakPrefix_maximal_remove cs a b g hmax t hta htb htg
      have hlt:cs.length (cs.simple t*a) < cs.length a:=by
        have hh:=(weakPrefix_simple_iff cs t a).mp hta;omega
      have hda':WeakPrefix cs (cs.simple t*d) (cs.simple t*a):=
        (weakPrefix_left_remove cs t htd hta).mpr hda
      have hdb':WeakPrefix cs (cs.simple t*d) (cs.simple t*b):=
        (weakPrefix_left_remove cs t htd htb).mpr hdb
      have hdg':=ih (cs.simple t*a) hlt (cs.simple t*b) (cs.simple t*g) hga' hgb' hmax' (cs.simple t*d) hda' hdb'
      have hdg:WeakPrefix cs d g:=(weakPrefix_left_remove cs t htd htg).mp hdg'
      exact weakPrefix_trans cs hsd hdg
    have hea':WeakPrefix cs (cs.simple s*e) (cs.simple s*a):=
      (weakPrefix_left_remove cs s hse hsa).mpr hea
    have heb':WeakPrefix cs (cs.simple s*e) (cs.simple s*b):=
      (weakPrefix_left_remove cs s hse hsb).mpr heb
    have hga':WeakPrefix cs (cs.simple s*g) (cs.simple s*a):=
      (weakPrefix_left_remove cs s hsg hsa).mpr hga
    have hgb':WeakPrefix cs (cs.simple s*g) (cs.simple s*b):=
      (weakPrefix_left_remove cs s hsg hsb).mpr hgb
    have hmax':=common_weakPrefix_maximal_remove cs a b g hmax s hsa hsb hsg
    have hlt:cs.length (cs.simple s*a) < cs.length a:=by
      have hh:=(weakPrefix_simple_iff cs s a).mp hsa;omega
    have heg':=ih (cs.simple s*a) hlt (cs.simple s*b) (cs.simple s*g) hga' hgb' hmax' (cs.simple s*e) hea' heb'
    exact (weakPrefix_left_remove cs s hse hsg).mp heg'

theorem exists_greatest_common_weakPrefix (a b:W) :
    ∃g:W,WeakPrefix cs g a ∧ WeakPrefix cs g b ∧
      ∀e:W,WeakPrefix cs e a→WeakPrefix cs e b→WeakPrefix cs e g := by
  let P:ℕ→Prop:=fun n=>∃g:W,WeakPrefix cs g a ∧ WeakPrefix cs g b ∧ cs.length g=n
  have hP:P 0:=⟨1,weakPrefix_one cs a,weakPrefix_one cs b,cs.length_one⟩
  obtain ⟨g,hga,hgb,hlen⟩:=Nat.findGreatest_spec (Nat.zero_le (cs.length a)) hP
  refine ⟨g,hga,hgb,maximal_common_weakPrefix_greatest cs a b g hga hgb ?_⟩
  intro x hxa hxb
  rw [hlen]
  exact Nat.le_findGreatest (weakPrefix_length cs hxa) ⟨x,hxa,hxb,rfl⟩

end HarmonicArtin.CoxeterExchange

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveDegreeHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

universe u
variable {S:Type u} (M:CoxeterMatrix S)

lemma positiveDegree_zero_iff (a:PositiveArtin M) : positiveDegree M a=0 ↔ a=1 := by
  obtain ⟨w,rfl⟩:=positive_word_surjective M a
  rw [positiveDegree_word]
  constructor
  · intro h;rw [List.eq_nil_of_length_eq_zero h];rfl
  · intro h;simpa only [positiveDegree_word,positiveDegree_one] using congrArg (positiveDegree M) h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositivePrefix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} (M:CoxeterMatrix S)

lemma positivePrefix_refl (a:PositiveArtin M) : PositivePrefix M a a :=⟨1,(mul_one a).symm⟩
lemma positivePrefix_one (a:PositiveArtin M) : PositivePrefix M 1 a :=⟨a,(one_mul a).symm⟩
lemma positivePrefix_trans {a b c:PositiveArtin M} (hab:PositivePrefix M a b) (hbc:PositivePrefix M b c) : PositivePrefix M a c := by
  obtain ⟨u,hu⟩:=hab;obtain ⟨v,hv⟩:=hbc
  exact ⟨u*v,by rw [hv,hu,mul_assoc]⟩

lemma positivePrefix_degree {a b:PositiveArtin M} (h:PositivePrefix M a b) : positiveDegree M a≤positiveDegree M b := by
  obtain ⟨c,rfl⟩:=h
  rw [positiveDegree_mul];omega

lemma positivePrefix_eq_of_degree {a b:PositiveArtin M} (h:PositivePrefix M a b)
    (he:positiveDegree M a=positiveDegree M b) : a=b := by
  obtain ⟨c,rfl⟩:=h
  rw [positiveDegree_mul] at he
  have hc:c=1:=(positiveDegree_zero_iff M c).mp (by omega)
  rw [hc,mul_one]

variable [Fintype S]

lemma positivePrefix_of_simple_eq {a b:PositiveArtin M} {w:M.Group}
    (h:PositivePrefix M a b) (hb:b=positiveSimpleLift M w) :
    a=positiveSimpleLift M (positiveToCoxeter M a) := by
  obtain ⟨c,hc⟩:=h
  exact (positive_simple_factors M a c w (hc.symm.trans hb)).1

theorem exists_greatest_common_simplePrefix (u v:M.Group) :
    ∃g:M.Group,PositivePrefix M (positiveSimpleLift M g) (positiveSimpleLift M u) ∧
      PositivePrefix M (positiveSimpleLift M g) (positiveSimpleLift M v) ∧
      ∀a:PositiveArtin M,PositivePrefix M a (positiveSimpleLift M u)→
        PositivePrefix M a (positiveSimpleLift M v)→PositivePrefix M a (positiveSimpleLift M g) := by
  obtain ⟨g,hgu,hgv,hgreat⟩:=exists_greatest_common_weakPrefix M.toCoxeterSystem u v
  refine ⟨g,(positivePrefix_simple_iff M g u).mpr hgu,(positivePrefix_simple_iff M g v).mpr hgv,?_⟩
  intro a hau hav
  have he:=positivePrefix_of_simple_eq M hau rfl
  rw [he] at hau hav ⊢
  exact (positivePrefix_simple_iff M _ _).mpr (hgreat _
    ((positivePrefix_simple_iff M _ _).mp hau) ((positivePrefix_simple_iff M _ _).mp hav))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_SimpleFrontLink
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

omit [Fintype S] in
lemma simpleFrontLink_mono {a b:PositiveArtin M} (hab:PositivePrefix M a b) {s t:S}
    (h:SimpleFrontLink M a s t) : SimpleFrontLink M b s t := by
  obtain ⟨w,hwa,hs,ht⟩:=h
  exact ⟨w,positivePrefix_trans M hwa hab,hs,ht⟩

omit [Fintype S] in
lemma frontLinked_mono {a b:PositiveArtin M} (hab:PositivePrefix M a b) {s t:S}
    (h:FrontLinked M a s t) : FrontLinked M b s t := by
  induction h with
  | refl=>exact .refl
  | tail h hst ih=>exact ih.tail (simpleFrontLink_mono M hab hst)

omit [Fintype S] in
lemma frontLinked_symm {a:PositiveArtin M} {s t:S} (h:FrontLinked M a s t) : FrontLinked M a t s := by
  induction h with
  | refl=>exact .refl
  | @tail u v h huv ih=>
    obtain ⟨w,hwa,hu,hv⟩:=huv
    exact (Relation.ReflTransGen.single ⟨w,hwa,hv,hu⟩).trans ih

lemma wordPositive_simple_of_reduced (w:List S) (hw:M.toCoxeterSystem.IsReduced w) :
    wordPositive M w=positiveSimpleLift M (wordCoxeter M w) :=
  (positiveSimpleLift_word M w hw).symm

omit [Fintype S] in
lemma positivePrefix_first (s:S) (w:List S) : PositivePrefix M (positiveGenerator M s) (wordPositive M (s::w)) :=⟨wordPositive M w,rfl⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_WordFrontData
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_mul _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_one _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_word _root_.OAI.HarmonicArtin.positiveReverse_generator _root_.OAI.HarmonicArtin.positiveReverse_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

omit [Fintype S] in
private lemma wordFront_refl (u:List S) : WordFrontData M u u := by
  refine ⟨rfl,rfl,?_⟩
  intro s us t vs hu hv
  have h:s=t:=by simpa only [hu,List.cons.injEq] using (List.cons.inj (hu.symm.trans hv)).1
  subst t
  exact .refl

omit [Fintype S] in
private lemma wordFront_symm {u v:List S} (h:WordFrontData M u v) : WordFrontData M v u := by
  refine ⟨h.1.symm,h.2.1.symm,?_⟩
  intro s us t vs hu hv
  rw [←h.1]
  exact frontLinked_symm M (h.2.2 t vs s us hv hu)

omit [Fintype S] in
private lemma wordFront_trans {u v w:List S} (h:WordFrontData M u v) (k:WordFrontData M v w) : WordFrontData M u w := by
  refine ⟨h.1.trans k.1,h.2.1.trans k.2.1,?_⟩
  intro s us t ts hu hw
  cases v with
  | nil=>have hh:=h.2.1;rw [hu] at hh;simp at hh
  | cons r rs=>
    have hl:=h.2.2 s us r rs hu rfl
    have hr:=k.2.2 r rs t ts rfl hw
    rw [←h.1] at hr
    exact hl.trans hr

omit [Fintype S] in
private lemma wordFront_mul {u v w x:List S} (h:WordFrontData M u v) (k:WordFrontData M w x) : WordFrontData M (u++w) (v++x) := by
  refine ⟨by rw [wordPositive_append,wordPositive_append,h.1,k.1],by simp only [List.length_append,h.2.1,k.2.1],?_⟩
  intro s us t ts hu hv
  cases u with
  | nil=>
    have he:v=[]:=List.length_eq_zero_iff.mp h.2.1.symm
    subst v
    exact k.2.2 s us t ts hu hv
  | cons r rs=>
    cases v with
    | nil=>have hh:=h.2.1;simp at hh
    | cons q qs=>
      have hs:r=s:=(List.cons.inj hu).1
      have ht:q=t:=(List.cons.inj hv).1
      subst s;subst t
      exact frontLinked_mono M ⟨wordPositive M w,wordPositive_append M _ _⟩
        (h.2.2 r rs q qs rfl rfl)

private lemma wordFront_relation (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (s t:S) :
    WordFrontData M (altList s t (M s t)) (altList t s (M s t)) := by
  refine ⟨wordPositive_braid M s t,by simp only [length_altList],?_⟩
  intro r rs q qs hr hq
  by_cases hm:M s t=0
  · rw [hm,altList_zero] at hr
    contradiction
  obtain ⟨n,hn⟩:=Nat.exists_eq_succ_of_ne_zero hm
  have hs:s=r:=by rw [hn,altList_succ] at hr;exact (List.cons.inj hr).1
  have ht:t=q:=by rw [hn,altList_succ] at hq;exact (List.cons.inj hq).1
  subst r;subst q
  have hred:=alternating_isReduced_of_longest M z hz s t
  have he:=wordPositive_simple_of_reduced M _ hred
  apply Relation.ReflTransGen.single
  refine ⟨wordCoxeter M (altList s t (M s t)),he ▸ positivePrefix_refl M _,?_,?_⟩
  · rw [←he,hr]
    exact positivePrefix_first M s rs
  · rw [←he,wordPositive_braid,hq]
    exact positivePrefix_first M t qs

private lemma wordFront_conGen (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    {u v:FreeMonoid S} (h:ConGen.Rel (positiveBraidRelations M) u v) :
    WordFrontData M u.toList v.toList := by
  induction h with
  | of a b h=>
    obtain ⟨s,t,rfl,rfl⟩:=h
    exact wordFront_relation M z hz s t
  | refl a=>exact wordFront_refl M a.toList
  | symm h ih=>exact wordFront_symm M ih
  | trans h k ih ik=>exact wordFront_trans M ih ik
  | mul h k ih ik=>exact wordFront_mul M ih ik

theorem positive_first_letters_connected (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (a:PositiveArtin M) (s t:S)
    (hs:PositivePrefix M (positiveGenerator M s) a)
    (ht:PositivePrefix M (positiveGenerator M t) a) : FrontLinked M a s t := by
  obtain ⟨b,hb⟩:=hs
  obtain ⟨c,hc⟩:=ht
  obtain ⟨u,hu⟩:=PresentedMonoid.surjective_mk (rels:=positiveBraidRelations M) b
  obtain ⟨v,hv⟩:=PresentedMonoid.surjective_mk (rels:=positiveBraidRelations M) c
  have hu':wordPositive M u.toList=b:=by rw [wordPositive_mk,FreeMonoid.ofList_toList,hu]
  have hv':wordPositive M v.toList=c:=by rw [wordPositive_mk,FreeMonoid.ofList_toList,hv]
  have he₁:wordPositive M (s::u.toList)=a:=by change positiveGenerator M s*wordPositive M u.toList=a;rw [hu',←hb]
  have he₂:wordPositive M (t::v.toList)=a:=by change positiveGenerator M t*wordPositive M v.toList=a;rw [hv',←hc]
  have he:=he₁.trans he₂.symm
  rw [wordPositive_mk,wordPositive_mk] at he
  have h:ConGen.Rel (positiveBraidRelations M) (FreeMonoid.ofList (s::u.toList)) (FreeMonoid.ofList (t::v.toList)):=PresentedMonoid.mk_eq_mk_iff.mp he
  have hf:=(wordFront_conGen M z hz h).2.2 s u.toList t v.toList rfl rfl
  rw [FreeMonoid.toList_ofList,he₁] at hf
  exact hf

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveHead
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_mul _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_one _root_.OAI.HarmonicArtin.positiveReverse_generator _root_.OAI.HarmonicArtin.positiveReverse_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

private lemma exists_front_head
    (cancel:∀a b c:PositiveArtin M,a*b=a*c→b=c)
    (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (a:PositiveArtin M)
    (ih:∀b:PositiveArtin M,positiveDegree M b<positiveDegree M a→HasPositiveHead M b)
    (s:S) (hs:PositivePrefix M (positiveGenerator M s) a) :
    ∃h:M.Group,IsFrontHead M a s h := by
  obtain ⟨b,hb⟩:=hs
  have hdeg:positiveDegree M b<positiveDegree M a:=by rw [hb,positiveDegree_mul,positiveDegree_generator];omega
  obtain ⟨g,hgb,hgreat⟩:=ih b hdeg
  let c: M.Group:=(M.toCoxeterSystem.simple s)⁻¹*z
  have hsc:positiveGenerator M s*positiveSimpleLift M c=positiveSimpleLift M z:=by
    simpa only [positiveSimpleLift_simple] using positiveSimpleLift_left_complement M z hz (M.toCoxeterSystem.simple s)
  obtain ⟨k,hkg,hkc,hmeet⟩:=exists_greatest_common_simplePrefix M g c
  let x:PositiveArtin M:=positiveGenerator M s*positiveSimpleLift M k
  have hxb:PositivePrefix M x a:=by
    obtain ⟨r,hr⟩:=positivePrefix_trans M hkg hgb
    refine ⟨r,?_⟩
    rw [hb,hr,mul_assoc]
  have hxΔ:PositivePrefix M x (positiveSimpleLift M z):=by
    obtain ⟨r,hr⟩:=hkc
    refine ⟨r,?_⟩
    rw [←hsc,hr,mul_assoc]
  have hx:x=positiveSimpleLift M (positiveToCoxeter M x):=positivePrefix_of_simple_eq M hxΔ rfl
  refine ⟨positiveToCoxeter M x,?_,?_,?_⟩
  · exact hx ▸ hxb
  · rw [←hx]
    exact ⟨positiveSimpleLift M k,rfl⟩
  · intro w hwa hsw
    obtain ⟨e,he⟩:=hsw
    have hes:e=positiveSimpleLift M (positiveToCoxeter M e):=
      (positive_simple_factors M (positiveGenerator M s) e w he.symm).2
    have heb:PositivePrefix M e b:=by
      obtain ⟨f,hf⟩:=hwa
      refine ⟨f,cancel (positiveGenerator M s) b (e*f) ?_⟩
      rw [←hb,hf,he,mul_assoc]
    have hec:PositivePrefix M e (positiveSimpleLift M c):=by
      have hwΔ:PositivePrefix M (positiveSimpleLift M w) (positiveSimpleLift M z):=
        ⟨positiveSimpleLift M (w⁻¹*z),(positiveSimpleLift_left_complement M z hz w).symm⟩
      obtain ⟨f,hf⟩:=hwΔ
      refine ⟨f,cancel (positiveGenerator M s) (positiveSimpleLift M c) (e*f) ?_⟩
      rw [hsc,hf,he,mul_assoc]
    have heg:PositivePrefix M e (positiveSimpleLift M g):=by
      rw [hes] at heb ⊢
      exact hgreat _ heb
    obtain ⟨r,hr⟩:=hmeet e heg hec
    rw [←hx]
    refine ⟨r,?_⟩
    dsimp [x]
    rw [he,hr,mul_assoc]

theorem positive_greedy_head
    (cancel:∀a b c:PositiveArtin M,a*b=a*c→b=c)
    (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (a:PositiveArtin M) : HasPositiveHead M a := by
  induction a using (measure (positiveDegree M)).wf.induction with
  | h a ih=>
    by_cases ha:a=1
    · subst a
      refine ⟨1,by rw [positiveSimpleLift_one];exact positivePrefix_refl M 1,?_⟩
      intro w hw
      rw [positiveSimpleLift_one]
      exact hw
    obtain ⟨l,hl⟩:=positive_word_surjective M a
    cases l with
    | nil=>exact (ha hl.symm).elim
    | cons s ls=>
      have hs:PositivePrefix M (positiveGenerator M s) a:=by rw [←hl];exact positivePrefix_first M s ls
      obtain ⟨h,hh⟩:=exists_front_head M cancel z hz a (fun b hb=>ih b hb) s hs
      refine ⟨h,hh.1,?_⟩
      intro w hwa
      by_cases hw:w=1
      · subst w
        rw [positiveSimpleLift_one]
        exact positivePrefix_one M _
      obtain ⟨t,ht⟩:=exists_simple_prefix M.toCoxeterSystem hw
      have htw:PositivePrefix M (positiveGenerator M t) (positiveSimpleLift M w):=by
        simpa only [positiveSimpleLift_simple] using (positivePrefix_simple_iff M _ _).mpr ht
      have hta:=positivePrefix_trans M htw hwa
      have hlink:=positive_first_letters_connected M z hz a s t hs hta
      have hfront:IsFrontHead M a t h:=by
        clear ht htw hta
        induction hlink with
        | refl=>exact hh
        | @tail t u chain link hi=>
          obtain ⟨d,hda,htd,hud⟩:=link
          obtain ⟨k,hk⟩:=exists_front_head M cancel z hz a (fun b hb=>ih b hb) u
            (positivePrefix_trans M hud hda)
          have hdk:=hk.2.2 d hda hud
          have htk:=positivePrefix_trans M htd hdk
          have hkh:=hi.2.2 k hk.1 htk
          refine ⟨hi.1,positivePrefix_trans M hk.2.1 hkh,?_⟩
          intro v hva huv
          exact positivePrefix_trans M (hk.2.2 v hva huv) hkh
      exact hfront.2.2 w hwa htw

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositivePrefixMulLeft
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

omit [Fintype S] in
lemma positivePrefix_mul_left (c:PositiveArtin M) {a b:PositiveArtin M} (h:PositivePrefix M a b) :
    PositivePrefix M (c*a) (c*b) := by
  obtain ⟨r,hr⟩:=h
  exact ⟨r,by rw [hr,mul_assoc]⟩

omit [Fintype S] in
lemma positivePrefix_mul_left_iff (cancel:∀a b c:PositiveArtin M,a*b=a*c→b=c)
    (c a b:PositiveArtin M) : PositivePrefix M (c*a) (c*b) ↔ PositivePrefix M a b := by
  constructor
  · rintro ⟨r,hr⟩
    exact ⟨r,cancel c b (a*r) (by simpa only [mul_assoc] using hr)⟩
  · exact positivePrefix_mul_left M c

omit [Fintype S] in
lemma exists_positive_first {a:PositiveArtin M} (ha:a≠1) :
    ∃s:S,PositivePrefix M (positiveGenerator M s) a := by
  obtain ⟨w,hw⟩:=positive_word_surjective M a
  cases w with
  | nil=>exact (ha hw.symm).elim
  | cons s w=>exact ⟨s,hw ▸ positivePrefix_first M s w⟩

lemma positive_common_atoms_prefix
    (heads:∀a:PositiveArtin M,HasPositiveHead M a)
    (a b:PositiveArtin M) (s t:S)
    (hsa:PositivePrefix M (positiveGenerator M s) a)
    (hsb:PositivePrefix M (positiveGenerator M s) b)
    (hta:PositivePrefix M (positiveGenerator M t) a)
    (htb:PositivePrefix M (positiveGenerator M t) b) :
    ∃d:PositiveArtin M,PositivePrefix M d a ∧ PositivePrefix M d b ∧
      PositivePrefix M (positiveGenerator M s) d ∧ PositivePrefix M (positiveGenerator M t) d := by
  obtain ⟨u,hua,hU⟩:=heads a
  obtain ⟨v,hvb,hV⟩:=heads b
  obtain ⟨d,hdu,hdv,hd⟩:=exists_greatest_common_simplePrefix M u v
  refine ⟨positiveSimpleLift M d,positivePrefix_trans M hdu hua,positivePrefix_trans M hdv hvb,?_,?_⟩
  · simpa only [positiveSimpleLift_simple] using hd (positiveSimpleLift M (M.toCoxeterSystem.simple s)) (hU (M.toCoxeterSystem.simple s) (by simpa only [positiveSimpleLift_simple] using hsa))
      (hV (M.toCoxeterSystem.simple s) (by simpa only [positiveSimpleLift_simple] using hsb))
  · simpa only [positiveSimpleLift_simple] using hd (positiveSimpleLift M (M.toCoxeterSystem.simple t)) (hU (M.toCoxeterSystem.simple t) (by simpa only [positiveSimpleLift_simple] using hta))
      (hV (M.toCoxeterSystem.simple t) (by simpa only [positiveSimpleLift_simple] using htb))

omit [Fintype S] in
lemma positive_common_maximal_remove (c a b g:PositiveArtin M)
    (hmax:∀x:PositiveArtin M,PositivePrefix M x (c*a)→PositivePrefix M x (c*b)→positiveDegree M x≤positiveDegree M (c*g)) :
    ∀x:PositiveArtin M,PositivePrefix M x a→PositivePrefix M x b→positiveDegree M x≤positiveDegree M g := by
  intro x hxa hxb
  have hh:=hmax (c*x) (positivePrefix_mul_left M c hxa) (positivePrefix_mul_left M c hxb)
  simp only [positiveDegree_mul] at hh
  omega

theorem maximal_common_positivePrefix_greatest
    (cancel:∀a b c:PositiveArtin M,a*b=a*c→b=c)
    (heads:∀a:PositiveArtin M,HasPositiveHead M a)
    (a b g:PositiveArtin M)
    (hga:PositivePrefix M g a) (hgb:PositivePrefix M g b)
    (hmax:∀x:PositiveArtin M,PositivePrefix M x a→PositivePrefix M x b→positiveDegree M x≤positiveDegree M g) :
    ∀e:PositiveArtin M,PositivePrefix M e a→PositivePrefix M e b→PositivePrefix M e g := by
  induction a using (measure (positiveDegree M)).wf.induction generalizing b g with
  | h a ih=>
    intro e hea heb
    by_cases he:e=1
    · rw [he];exact positivePrefix_one M g
    obtain ⟨s,hse⟩:=exists_positive_first M he
    have hsa:=positivePrefix_trans M hse hea
    have hsb:=positivePrefix_trans M hse heb
    have hsg:PositivePrefix M (positiveGenerator M s) g:=by
      have hg:g≠1:=by
        intro hg
        have hh:=hmax _ hsa hsb
        rw [hg,positiveDegree_one,positiveDegree_generator] at hh
        omega
      obtain ⟨t,htg⟩:=exists_positive_first M hg
      have hta:=positivePrefix_trans M htg hga
      have htb:=positivePrefix_trans M htg hgb
      obtain ⟨d,hda,hdb,hsd,htd⟩:=positive_common_atoms_prefix M heads a b s t hsa hsb hta htb
      obtain ⟨a',ha'⟩:=hta
      obtain ⟨b',hb'⟩:=htb
      obtain ⟨g',hg'⟩:=htg
      obtain ⟨d',hd'⟩:=htd
      have Hga:PositivePrefix M g' a':=(positivePrefix_mul_left_iff M cancel _ _ _).mp (by rw [←ha',←hg'];exact hga)
      have Hgb:PositivePrefix M g' b':=(positivePrefix_mul_left_iff M cancel _ _ _).mp (by rw [←hb',←hg'];exact hgb)
      have Hda:PositivePrefix M d' a':=(positivePrefix_mul_left_iff M cancel _ _ _).mp (by rw [←ha',←hd'];exact hda)
      have Hdb:PositivePrefix M d' b':=(positivePrefix_mul_left_iff M cancel _ _ _).mp (by rw [←hb',←hd'];exact hdb)
      have Hmax:=positive_common_maximal_remove M (positiveGenerator M t) a' b' g' (by rw [←ha',←hb',←hg'];exact hmax)
      have hlt:positiveDegree M a'<positiveDegree M a:=by rw [ha',positiveDegree_mul,positiveDegree_generator];omega
      have hdg:=positivePrefix_mul_left M (positiveGenerator M t) (ih a' hlt b' g' Hga Hgb Hmax d' Hda Hdb)
      rw [←hd',←hg'] at hdg
      exact positivePrefix_trans M hsd hdg
    obtain ⟨a',ha'⟩:=hsa
    obtain ⟨b',hb'⟩:=hsb
    obtain ⟨g',hg'⟩:=hsg
    obtain ⟨e',he'⟩:=hse
    have Hga:PositivePrefix M g' a':=(positivePrefix_mul_left_iff M cancel _ _ _).mp (by rw [←ha',←hg'];exact hga)
    have Hgb:PositivePrefix M g' b':=(positivePrefix_mul_left_iff M cancel _ _ _).mp (by rw [←hb',←hg'];exact hgb)
    have Hea:PositivePrefix M e' a':=(positivePrefix_mul_left_iff M cancel _ _ _).mp (by rw [←ha',←he'];exact hea)
    have Heb:PositivePrefix M e' b':=(positivePrefix_mul_left_iff M cancel _ _ _).mp (by rw [←hb',←he'];exact heb)
    have Hmax:=positive_common_maximal_remove M (positiveGenerator M s) a' b' g' (by rw [←ha',←hb',←hg'];exact hmax)
    have hlt:positiveDegree M a'<positiveDegree M a:=by rw [ha',positiveDegree_mul,positiveDegree_generator];omega
    have heg:=positivePrefix_mul_left M (positiveGenerator M s) (ih a' hlt b' g' Hga Hgb Hmax e' Hea Heb)
    rwa [←he',←hg'] at heg

theorem positive_greatest_common_left_divisor
    (cancel:∀a b c:PositiveArtin M,a*b=a*c→b=c)
    (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (a b:PositiveArtin M) :
    ∃g:PositiveArtin M,PositivePrefix M g a ∧ PositivePrefix M g b ∧
      ∀e:PositiveArtin M,PositivePrefix M e a→PositivePrefix M e b→PositivePrefix M e g := by
  let P:ℕ→Prop:=fun n=>∃g:PositiveArtin M,PositivePrefix M g a ∧ PositivePrefix M g b ∧ positiveDegree M g=n
  have hP:P 0:=⟨1,positivePrefix_one M a,positivePrefix_one M b,positiveDegree_one M⟩
  obtain ⟨g,hga,hgb,hlen⟩:=Nat.findGreatest_spec (Nat.zero_le (positiveDegree M a)) hP
  refine ⟨g,hga,hgb,maximal_common_positivePrefix_greatest M cancel (positive_greedy_head M cancel z hz) a b g hga hgb ?_⟩
  intro x hxa hxb
  rw [hlen]
  exact Nat.le_findGreatest (positivePrefix_degree M hxa) ⟨x,hxa,hxb,rfl⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Cancellation_SphericalPositiveCancelLeft
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma spherical_positive_cancel_left (T:Set S) (hT:IsSpherical M T)
    (a b c:PositiveArtin (restrictedMatrix M T)) (h:a*b=a*c) : b=c := by
  let := sphericalPositiveCancelMonoid M T hT
  exact mul_left_cancel h

end HarmonicArtin

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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveDegreeSublevelFinite
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

omit [Fintype S] in
theorem positive_lcm_of_common_multiple
    (gcd:∀a b:PositiveArtin M,∃g:PositiveArtin M,
      PositivePrefix M g a ∧ PositivePrefix M g b ∧
      ∀e:PositiveArtin M,PositivePrefix M e a→PositivePrefix M e b→PositivePrefix M e g)
    (a b:PositiveArtin M)
    (hex:∃c:PositiveArtin M,PositivePrefix M a c ∧ PositivePrefix M b c) :
    ∃c:PositiveArtin M,PositivePrefix M a c ∧ PositivePrefix M b c ∧
      ∀d:PositiveArtin M,PositivePrefix M a d→PositivePrefix M b d→PositivePrefix M c d := by
  let P:ℕ→Prop:=fun n=>∃c:PositiveArtin M,PositivePrefix M a c ∧ PositivePrefix M b c ∧ positiveDegree M c=n
  have hP:∃n,P n:=by obtain ⟨c,hac,hbc⟩:=hex;exact ⟨positiveDegree M c,c,hac,hbc,rfl⟩
  obtain ⟨c,hac,hbc,hc⟩:=Nat.find_spec hP
  refine ⟨c,hac,hbc,?_⟩
  intro d had hbd
  obtain ⟨e,hec,hed,he⟩:=gcd c d
  have hae:=he a hac had
  have hbe:=he b hbc hbd
  have hmin:positiveDegree M c≤positiveDegree M e:=by
    rw [hc]
    exact Nat.find_min' hP ⟨e,hae,hbe,rfl⟩
  have heq:e=c:=positivePrefix_eq_of_degree M hec (Nat.le_antisymm (positivePrefix_degree M hec) hmin)
  rwa [heq] at hed

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_TypeComponent
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

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The existing categorical action with an arbitrary original color as frame. -/

namespace HarmonicArtin.ParabolicIntersections

open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "diag" => coxeterFusionEdge_diag M
local notation "Q" => fusionQuiver m d hd

private theorem pointed_orthogonal (s f : S) (hsf : M s f = 2)
    (L H : PointedLabel M) : OrthogonalVertices Q (.inl s, L) (.inl f, H) := by
  have hne : s ≠ f := by
    intro he
    subst f
    rw [M.diagonal] at hsf
    norm_num at hsf
  apply fusionQuiver_orthogonal
  · intro he
    exact hne (Sum.inl.inj (congrArg Prod.fst he))
  · simp only [coxeterFusionEdge, hne, ↓reduceDIte, hsf,
      OfNat.ofNat_ne_zero, FusionEdge.multiplicity]
    split <;> rfl

/-- A color nonadjacent to the frame fixes each initial projective. -/
theorem pointed_generator_fixes_initial (s f : S) (hsf : M s f = 2)
    (L : PointedLabel M) :
    pointedAction M (generator M s) (pointedInitial M f L) = pointedInitial M f L := by
  rw [pointedAction_generator, fusionPacketPerm, ← classPacketPerm_toList]
  have hlist (l : List (PointedLabel M)) :
      (l.map (fun H => classTwistPerm Q (fusionQuiver_no_loops m d hd diag)
        (.inl s, H))).prod (pointedInitial M f L) = pointedInitial M f L := by
    induction l with
    | nil => rfl
    | cons H l ih =>
      change classPositiveTwist Q (.inl s, H)
        ((l.map (fun J => classTwistPerm Q (fusionQuiver_no_loops m d hd diag)
          (.inl s, J))).prod (pointedInitial M f L)) = _
      rw [ih]
      exact classPositiveTwist_initial_orthogonal Q (pointed_orthogonal M s f hsf H L)
  exact hlist _

/-- The whole standard subgroup of nonadjacent colors fixes the frame. -/
theorem pointed_standard_fixes_initial (X : Set S) (f : S)
    (hX : ∀ s ∈ X, M s f = 2) (g : Artin M) (hg : g ∈ artinParabolic M X)
    (L : PointedLabel M) :
    pointedAction M g (pointedInitial M f L) = pointedInitial M f L := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨s, hs, rfl⟩ := hg
    exact pointed_generator_fixes_initial M s f (hX s hs) L
  | one => simp only [map_one, Equiv.Perm.one_apply]
  | mul g h hg hh ihg ihh =>
    simp only [map_mul, Equiv.Perm.mul_apply, ihh, ihg]
  | inv g hg ih =>
    rw [map_inv]
    apply (pointedAction M g).injective
    change (pointedAction M g) ((pointedAction M g).symm (pointedInitial M f L)) = _
    rw [Equiv.apply_symm_apply, ih]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_AcyclicTwist
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharging the acyclic-evaluation input by finite minimal reduction. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) [Fintype V] [Fintype A]
  [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma minimal_scalar_exact_empty {I : Type} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K := ℂ) I) (hE : E.IsMinimal Q) (α : V)
    (h : ∀ l c, ScalarExactAt Q E α l c) : IsEmpty I := by
  have hdm : E.differential.map (vertexHom Q α)=0 := by
    ext i j
    exact congrFun (hE i j) α
  refine ⟨fun i => ?_⟩
  let x : I → ℂ := Pi.single i 1
  have hx : ScalarSupported Q E (E.placement i).level (E.placement i).cochain x := by
    intro j hj
    have hji : j ≠ i := by rintro rfl; exact hj ⟨rfl,rfl⟩
    exact Pi.single_eq_of_ne hji _
  obtain ⟨y,_,hy⟩ := h _ _ x hx (by rw [hdm,Matrix.vecMul_zero])
  rw [hdm,Matrix.vecMul_zero] at hy
  have hi := congrFun hy i
  simp [x] at hi

omit [Fintype V] [DecidableEq A] in
/-- An everywhere exact, one-color complex has an empty minimal model. -/
lemma scalar_exact_empty_model {I : Type} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K := ℂ) I) (α : V)
    (hcolor : ∀ i, (E.placement i).color=α)
    (h : ∀ l c, ScalarExactAt Q E α l c) :
    ∃ F : FiniteModel.{0} Q (K := ℂ), IsEmpty F.Index ∧
      Nonempty (HomotopyEquivalence Q F.complex E) := by
  obtain ⟨F,hF,⟨e⟩,j,hj⟩ := FiniteModel.exists_minimal_embedding Q (FiniteModel.ofComplex Q E)
  have hc : ∀ i, (F.complex.placement i).color=α := by
    intro i
    rw [hj i]
    exact hcolor (j i)
  have he : ∀ l c, ScalarExactAt Q F.complex α l c := fun l c =>
    scalarExact_transport Q F.complex E (e.symm Q) α hc (h l c)
  exact ⟨F,minimal_scalar_exact_empty Q F.complex hF α he,⟨e.symm Q⟩⟩

omit [Fintype V] [DecidableEq A] in
lemma cone_empty_source_class {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [IsEmpty I]
    {E : BasedComplex Q (K := ℂ) I} {F : BasedComplex Q (K := ℂ) J}
    (f : Map Q E F) : classOfComplex Q (f.cone Q)=classOfComplex Q F := by
  rw [classOfComplex_reindex Q _ (Equiv.emptySum I J).symm]
  congr 1

/-- The evaluation cone of an acyclic vertex test is homotopy equivalent
 to its target. This proves the Seidel--Thomas input in the actual model. -/
theorem acyclic_twist_input : PublishedAcyclicTwist Q := by
  constructor
  intro x α hx
  induction x using Quotient.inductionOn with | _ E =>
    change classOfComplex Q (E.complex.positiveTwist Q α)=classOfComplex Q E.complex
    obtain ⟨F,hF,⟨e⟩⟩ := scalar_exact_empty_model Q (E.complex.testComplex Q α) α
      (fun _ => rfl) hx
    let := hF
    let c := e.coneSource Q (E.complex.evaluation Q α)
    exact (classOfComplex_eq Q c).symm.trans (cone_empty_source_class Q _)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ArtinRelabel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Maps of Artin presentations induced by label-preserving maps. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
variable {S T : Type} (M : CoxeterMatrix S) (N : CoxeterMatrix T)
    (f : S → T) (hf : ∀ i j, N (f i) (f j)=M i j)

lemma artinMap_leftInverse (g : T → S) (hg : ∀ i j, M (g i) (g j)=N i j)
    (hgf : Function.LeftInverse g f) :
    Function.LeftInverse (artinMap N M g hg) (artinMap M N f hf) := by
  have he : (artinMap N M g hg).comp (artinMap M N f hf)=MonoidHom.id (Artin M) := by
    apply PresentedGroup.ext
    intro s
    change artinMap N M g hg (artinMap M N f hf (generator M s))=generator M s
    rw [artinMap_generator,artinMap_generator,hgf s]
  intro a
  exact DFunLike.congr_fun he a

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_Basic
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parabolic subgroups for result 082-03

We use the Artin presentation and standard parabolics already used by
`Topology.ArtinGroups`. In Mathlib's Coxeter matrix convention, a zero
off-diagonal entry means an infinite label.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {G : Type*} [Group G]

theorem conjugate_inf (g : G) (P Q : Subgroup G) :
    conjugate g (P ⊓ Q) = conjugate g P ⊓ conjugate g Q := rfl

theorem conjugate_sup (g : G) (P Q : Subgroup G) :
    conjugate g (P ⊔ Q) = conjugate g P ⊔ conjugate g Q :=
  (conjugateOrderIso g).map_sup P Q

theorem conjugate_eq_self {g : G} {P : Subgroup G} (hg : g ∈ P) :
    conjugate g P = P := by
  ext a
  rw [mem_conjugate]
  constructor
  · intro ha
    have hb := P.mul_mem (P.mul_mem hg ha) (P.inv_mem hg)
    simpa [mul_assoc] using hb
  · intro ha
    exact P.mul_mem (P.mul_mem (P.inv_mem hg) ha) hg

variable {S : Type*} (M : CoxeterMatrix S)

theorem standard_univ : artinParabolic M Set.univ = ⊤ := by
  rw [artinParabolic, Set.image_univ]
  exact PresentedGroup.closure_range_of (braidRelators M)

theorem standard_union (X Y : Set S) :
    artinParabolic M (X ∪ Y) = artinParabolic M X ⊔ artinParabolic M Y := by
  simp only [artinParabolic, Set.image_union, Subgroup.closure_union]

end HarmonicArtin.ParabolicIntersections

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

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_BraidRestriction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_mul _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_one _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_word _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.positiveDegree_generator _root_.OAI.HarmonicArtin.positiveDegree_mul _root_.OAI.HarmonicArtin.positiveDegree_one _root_.OAI.HarmonicArtin.positiveDegree_word _root_.OAI.HarmonicArtin.positiveReverse_generator _root_.OAI.HarmonicArtin.positiveReverse_one _root_.OAI.HarmonicArtin.positiveSimpleLift_one _root_.OAI.HarmonicArtin.positiveSimpleLift_simple _root_.OAI.HarmonicArtin.positiveToCoxeter_generator _root_.OAI.HarmonicArtin.positiveToCoxeter_simpleLift _root_.OAI.HarmonicArtin.positiveToCoxeter_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive braid derivations restrict to a full subdiagram. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S V A : Type} (Q : ReversibleQuiver V A) (N : CoxeterMatrix S)
    (f : S → V) (hinj : Function.Injective f)
    (hN : ∀ i j, ordinaryCoxeterMatrix Q (f i) (f j)=N i j)

private lemma positive_cons_p0 (i : S) (w : List S) :
    wordPositive N (i::w)=positiveGenerator N i*wordPositive N w := rfl

include hinj hN in
/-- No braid move can introduce a vertex outside the original support.
Inside a full subdiagram every move is a defining positive Artin relation. -/
theorem positiveBraidRel_restrict [Nonempty S] {v w : List V}
    (h : PositiveBraidRel Q v w) (hv : ∀ x ∈ v, x ∈ Set.range f) :
    wordPositive N (v.map (Function.invFun f)) =
      wordPositive N (w.map (Function.invFun f)) := by
  have hinv : ∀ x, Function.invFun f (f x)=x := Function.leftInverse_invFun hinj
  induction h with
  | refl => rfl
  | symm h ih => exact (ih (h.symm.mem_set Q _ hv)).symm
  | trans h k ih ik => exact (ih hv).trans (ik (h.mem_set Q _ hv))
  | cons α h ih =>
    simp only [List.map_cons,positive_cons_p0]
    rw [ih (fun x hx => hv x (List.mem_cons_of_mem α hx))]
  | @orthogonal α β ho w =>
    obtain ⟨i,rfl⟩ := hv α (by simp)
    obtain ⟨j,rfl⟩ := hv β (by simp)
    have hij : N i j=2 := (hN i j).symm.trans (ordinaryCoxeterMatrix_orthogonal Q ho)
    have hb := wordPositive_braid N i j
    rw [hij] at hb
    have hc : positiveGenerator N i*positiveGenerator N j =
        positiveGenerator N j*positiveGenerator N i := by
      simpa only [altList_succ,altList_zero,positive_cons_p0,wordPositive,
        List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,_root_.mul_one] using hb
    simpa only [List.map_cons,hinv,positive_cons_p0,
      _root_.mul_assoc] using congrArg (·*wordPositive N (w.map (Function.invFun f))) hc
  | @adjacent α β edge w =>
    obtain ⟨i,rfl⟩ := hv α (by simp)
    obtain ⟨j,rfl⟩ := hv β (by simp)
    have hij : N i j=3 := (hN i j).symm.trans (ordinaryCoxeterMatrix_adjacent Q edge)
    have hb := wordPositive_braid N i j
    rw [hij] at hb
    have hc : positiveGenerator N i*(positiveGenerator N j*positiveGenerator N i) =
        positiveGenerator N j*(positiveGenerator N i*positiveGenerator N j) := by
      simpa only [altList_succ,altList_zero,positive_cons_p0,wordPositive,
        List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,_root_.mul_one] using hb
    simpa only [List.map_cons,hinv,positive_cons_p0,
      _root_.mul_assoc] using congrArg (·*wordPositive N (w.map (Function.invFun f))) hc

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_Consequences
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Consequences of the inside-parabolic intersection theorem

These are the deductions in the introduction of paper 082-03. The premise
`InsideIntersectionProperty` is a **new result of that paper**, not a
published input and not an established instance. These deductions alone
do not constitute a formalization of its main intersection theorem.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {S : Type*} (M : CoxeterMatrix S)

theorem inside_conjugate (h : InsideIntersectionProperty M)
    (Y : Set S) (g : Artin M) {P : Subgroup (Artin M)} (hP : IsParabolic M P) :
    ∃ (Z : Set S) (c : Artin M), Z ⊆ Y ∧ c ∈ artinParabolic M Y ∧
      conjugate g (artinParabolic M Y) ⊓ P =
        conjugate (g * c) (artinParabolic M Z) := by
  obtain ⟨X, a, rfl⟩ := hP
  obtain ⟨Z, c, hZ, hc, he⟩ := h X Y (g⁻¹ * a)
  refine ⟨Z, c, hZ, hc, ?_⟩
  have hh := congrArg (conjugate g) he
  rw [conjugate_inf, ← conjugate_mul, ← conjugate_mul] at hh
  simpa only [mul_inv_cancel_left] using hh

private theorem insert_intersection {G : Type*} [Group G]
    [DecidableEq (Subgroup G)]
    (P : Subgroup G) (F : Finset (Subgroup G)) :
    sInf (↑(insert P F) : Set (Subgroup G)) = P ⊓ sInf (↑F : Set (Subgroup G)) := by
  classical
  rw [Finset.coe_insert, sInf_insert]

variable [Finite S]

/-- The descent uses the displayed type, so no separate theorem asserting
that parabolic rank is invariant under conjugation is required. -/
private theorem finite_subfamily_aux (h : InsideIntersectionProperty M)
    (F : Set (Subgroup (Artin M))) (hF : ∀ P ∈ F, IsParabolic M P) :
    ∀ n : ℕ, ∀ (X : Set S), X.ncard = n → ∀ g : Artin M,
      ∃ F₀ : Finset (Subgroup (Artin M)),
        (↑F₀ : Set (Subgroup (Artin M))) ⊆ F ∧ F₀.card ≤ n ∧
        conjugate g (artinParabolic M X) ⊓ sInf F =
          conjugate g (artinParabolic M X) ⊓ sInf (↑F₀ : Set (Subgroup (Artin M))) ∧
        IsParabolic M (conjugate g (artinParabolic M X) ⊓ sInf F) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro X hX g
    let Q := conjugate g (artinParabolic M X)
    by_cases hQ : Q ≤ sInf F
    · refine ⟨∅, by simp, by simp, ?_, ?_⟩
      · simp only [Finset.coe_empty, sInf_empty, inf_top_eq]
        exact inf_eq_left.mpr hQ
      · change IsParabolic M (Q ⊓ sInf F)
        rw [inf_eq_left.mpr hQ]
        exact ⟨X, g, rfl⟩
    · obtain ⟨P, hPF, hQP⟩ : ∃ P ∈ F, ¬ Q ≤ P := by
        by_contra hn
        push Not at hn
        exact hQ (le_sInf hn)
      obtain ⟨Z, c, hZX, hc, he⟩ := inside_conjugate M h X g (hF P hPF)
      have hne : Z ≠ X := by
        intro hz
        rw [hz, conjugate_mul, conjugate_eq_self hc] at he
        exact hQP (inf_eq_left.mp he)
      have hlt : Z.ncard < n := by
        rw [← hX]
        exact Set.ncard_lt_ncard (ssubset_of_subset_of_ne hZX hne)
      obtain ⟨F₀, hF₀, hcard, hEq, hPar⟩ := ih Z.ncard hlt Z rfl (g * c)
      refine ⟨insert P F₀, ?_, ?_, ?_, ?_⟩
      · intro A hA
        rcases Finset.mem_insert.mp hA with rfl | hA
        · exact hPF
        · exact hF₀ hA
      · have hi := Finset.card_insert_le P F₀
        omega
      · rw [insert_intersection]
        calc
          Q ⊓ sInf F = (Q ⊓ P) ⊓ sInf F := by
            rw [inf_assoc, inf_eq_right.mpr (sInf_le hPF)]
          _ = conjugate (g * c) (artinParabolic M Z) ⊓ sInf F := by rw [he]
          _ = conjugate (g * c) (artinParabolic M Z) ⊓ sInf (↑F₀ : Set _) := hEq
          _ = Q ⊓ (P ⊓ sInf (↑F₀ : Set _)) := by rw [← he, inf_assoc]
      · have heF : Q ⊓ sInf F =
            conjugate (g * c) (artinParabolic M Z) ⊓ sInf F := by
          rw [← he, inf_assoc, inf_eq_right.mpr (sInf_le hPF)]
        rw [heF]
        exact hPar

/-- The full subfamily bound in Corollary 1.2, including the empty family.
This is conditional on the new inside-intersection theorem, explicitly. -/
theorem arbitrary_intersections_of_inside (h : InsideIntersectionProperty M)
    (F : Set (Subgroup (Artin M))) (hF : ∀ P ∈ F, IsParabolic M P) :
    (∃ F₀ : Finset (Subgroup (Artin M)),
      (↑F₀ : Set (Subgroup (Artin M))) ⊆ F ∧ F₀.card ≤ Nat.card S ∧
        sInf F = sInf (↑F₀ : Set (Subgroup (Artin M)))) ∧
    IsParabolic M (sInf F) := by
  obtain ⟨F₀, hF₀, hcard, he, hp⟩ :=
    finite_subfamily_aux M h F hF (Set.univ : Set S).ncard Set.univ rfl 1
  simp only [standard_univ, conjugate_top, top_inf_eq, Set.ncard_univ] at he hp hcard
  exact ⟨⟨F₀, hF₀, hcard, he⟩, hp⟩

/-- The unique smallest parabolic containing an arbitrary subset, rather
than merely a smallest parabolic containing a finite set. -/
theorem parabolic_closure_of_inside (h : InsideIntersectionProperty M)
    (E : Set (Artin M)) :
    ∃! P : Subgroup (Artin M), IsParabolic M P ∧ E ⊆ P ∧
      ∀ Q : Subgroup (Artin M), IsParabolic M Q → E ⊆ Q → P ≤ Q := by
  let F := {P : Subgroup (Artin M) | IsParabolic M P ∧ E ⊆ P}
  have hp := (arbitrary_intersections_of_inside M h F (fun _ hP => hP.1)).2
  have he : E ⊆ (sInf F : Subgroup (Artin M)) := by
    intro a ha
    exact Subgroup.mem_sInf.mpr (fun P hP => hP.2 ha)
  refine ⟨sInf F, ⟨hp, he, ?_⟩, ?_⟩
  · intro Q hQ hEQ
    exact sInf_le ⟨hQ, hEQ⟩
  · intro Q hQ
    exact le_antisymm (hQ.2.2 _ hp he) (sInf_le ⟨hQ.1, hQ.2.1⟩)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_StabilizerDescent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The rank induction in §8 of paper 082-03

The finite-rank induction is proved here for an actual group action.
`ReductionAt` records the three alternatives that the paper obtains from
its new relative-height arguments. It is deliberately not called a
published input: constructing these alternatives for the categorical
action is still required before this module implies the main theorem.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {S : Type*} (M : CoxeterMatrix S)
variable {V : Type*} [MulAction (Artin M) V] (v : V)

theorem conjugate_stabilizer (b x : Artin M) :
    conjugate b (MulAction.stabilizer (Artin M) (x • v)) =
      MulAction.stabilizer (Artin M) ((b * x) • v) := by
  ext a
  rw [mem_conjugate, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  rw [← smul_left_cancel_iff b]
  simp only [← mul_smul, mul_assoc, mul_inv_cancel_left]

/-- Lemma 8.1: a containing smaller parabolic removes the ambient
intersection after conjugation. -/
theorem relativeStabilizer_conjugation (Y D : Set S) (b x : Artin M)
    (hD : D ⊆ Y) (hb : b ∈ artinParabolic M Y)
    (hcontain : relativeStabilizer M v Y x ≤ conjugate b⁻¹ (artinParabolic M D)) :
    conjugate b (relativeStabilizer M v Y x) = relativeStabilizer M v D (b * x) := by
  have hsmall : conjugate b (relativeStabilizer M v Y x) ≤ artinParabolic M D := by
    have h := conjugate_mono b hcontain
    simpa [← conjugate_mul] using h
  have hlarge : artinParabolic M D ≤ artinParabolic M Y := standard_mono M hD
  have he : conjugate b (relativeStabilizer M v Y x) =
      artinParabolic M Y ⊓ MulAction.stabilizer (Artin M) ((b * x) • v) := by
    rw [relativeStabilizer, conjugate_inf, conjugate_eq_self hb, conjugate_stabilizer]
  apply le_antisymm
  · exact le_inf hsmall (he.le.trans inf_le_right)
  · rw [he]
    exact inf_le_inf hlarge le_rfl

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RankReduction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rank descent restricted to the subgroup of colors avoiding the frame. -/
namespace HarmonicArtin.ParabolicIntersections
variable {S : Type*} [Finite S] (M : CoxeterMatrix S)
variable {V : Type*} [MulAction (Artin M) V] (v : V)

/-- The induction keeps the transported point inside the prescribed orbit.
This permits the extra frame color in the relative diagram to remain fixed. -/
theorem relativeStabilizers_of_reductions_on (U : Set S)
    (hred : ∀ Y : Set S, Y ⊆ U → ∀ x : Artin M, x ∈ artinParabolic M U →
      ReductionAt M v Y x)
    (Y : Set S) (hYU : Y ⊆ U) (x : Artin M) (hx : x ∈ artinParabolic M U) :
    ∃ (R : Set S) (c : Artin M), R ⊆ Y ∧ c ∈ artinParabolic M Y ∧
      relativeStabilizer M v Y x = conjugate c⁻¹ (artinParabolic M R) := by
  suffices h : ∀ n : ℕ, ∀ Y : Set S, Y.ncard = n → Y ⊆ U →
      ∀ x : Artin M, x ∈ artinParabolic M U →
      ∃ (R : Set S) (c : Artin M), R ⊆ Y ∧ c ∈ artinParabolic M Y ∧
        relativeStabilizer M v Y x = conjugate c⁻¹ (artinParabolic M R) from h _ Y rfl hYU x hx
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Y hY hYU x hx
    rcases hred Y hYU x hx with hfixed | ⟨D,b,hD,hb,hcontain⟩ | ⟨T,K,hT,hK,hnorm,hsplit⟩
    · refine ⟨Y,1,Set.Subset.rfl,(artinParabolic M Y).one_mem,?_⟩
      simpa using hfixed
    · have hlt : D.ncard < n := hY ▸ Set.ncard_lt_ncard hD
      obtain ⟨R,c,hRD,hc,he⟩ := ih _ hlt D rfl (hD.subset.trans hYU) (b*x)
        ((artinParabolic M U).mul_mem (standard_mono M hYU hb) hx)
      have hconj := relativeStabilizer_conjugation M v Y D b x hD.subset hb hcontain
      have heq := congrArg (conjugate b⁻¹) (hconj.trans he)
      refine ⟨R,c*b,hRD.trans hD.subset,
        (artinParabolic M Y).mul_mem (standard_mono M hD.subset hc) hb,?_⟩
      simpa only [← conjugate_mul,inv_mul_cancel,conjugate_one,mul_inv_rev] using heq
    · have hlt : T.ncard < n := hY ▸ Set.ncard_lt_ncard hT
      obtain ⟨R,c,hRT,hc,he⟩ := ih _ hlt T rfl (hT.subset.trans hYU) x hx
      have hn := hnorm c⁻¹ ((artinParabolic M T).inv_mem hc)
      refine ⟨K ∪ R,c,Set.union_subset hK (hRT.trans hT.subset),
        standard_mono M hT.subset hc,?_⟩
      rw [hsplit,he,standard_union,conjugate_sup,hn]

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
local notation "hm" => fusionLabelSize_ge_two M

lemma pointedFamily_word (f : S) (w : List (S × Bool)) :
    pointedFamily M f (sourceSignedWord M w) =
      fusionPacketOrbit m d hd diag (sourcePacketWord w) (.inl f) := by
  funext L
  unfold pointedFamily pointedAction
  rw [sourceArtinAction_signedWord]
  rfl

/-- A frame color outside the operated type retains its unique level-zero count. -/
lemma pointedMultiplicity_frame (J : Set S) (f : S) (hf : f ∉ J)
    (x : Artin M) (hx : x ∈ artinParabolic M J) (k : ℤ) :
    pointedMultiplicity M f x k (.inl f) = if k = 0 then 1 else 0 := by
  obtain ⟨w, hw, rfl⟩ := artinParabolic_signed_word M J x hx
  have hav : ∀ a ∈ sourcePacketWord w, a.1 ≠ (.inl f : S ⊕ Unit) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    intro he
    exact hf (Sum.inl.inj he ▸ hw b hb)
  unfold pointedMultiplicity
  rw [pointedFamily_word]
  unfold fusionFamilyMultiplicity
  simp_rw [classTotalVector_layer_apply,
    fusionOrbit_frame_level m d hd diag _ _ _ _ _ hav]
  by_cases hk : k = 0
  · subst k
    simp only [and_true, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, _root_.mul_one,
      MulZeroClass.mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
    exact div_self (ne_of_gt (fusionWeight_pos m hm _))
  · simp only [hk, and_false, ite_false, if_false, Nat.cast_zero, MulZeroClass.mul_zero, Finset.sum_const_zero,
      zero_div]

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
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedInitialCounts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact counts and harmonic vectors at the initial pointed family. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M

lemma pointedMultiplicity_one (k : ℤ) (v : S ⊕ Unit) :
    pointedMultiplicity M f 1 k v = if v = .inl f ∧ k = 0 then 1 else 0 := by
  rw [pointedMultiplicity_sum]
  simp only [pointedFamily_one, classLevelArray_initial, Prod.mk.injEq]
  by_cases hv : v = .inl f
  · subst v
    by_cases hk : k = 0
    · subst k
      simp only [true_and, and_true, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite,
        _root_.mul_one, MulZeroClass.mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
      exact div_self (ne_of_gt (fusionWeight_pos m (fusionLabelSize_ge_two M) _))
    · simp only [hk, and_false, ite_false, if_false, Nat.cast_zero, MulZeroClass.mul_zero,
        Finset.sum_const_zero, zero_div]
  · have hv' : (.inl f : S ⊕ Unit) ≠ v := Ne.symm hv
    simp only [hv, hv', false_and, ite_false, if_false, Nat.cast_zero, MulZeroClass.mul_zero,
      Finset.sum_const_zero, zero_div]

lemma pointedHarmonicAt_empty (x : Artin M) (k : ℤ) :
    pointedHarmonicAt M f ∅ x k = pointedMultiplicity M f x k := by
  funext i
  exact pointedHarmonicAt_outside M f ∅ x k i (by simp)

lemma pointedCosetVector_empty (x : Artin M) (k : ℤ) :
    pointedCosetVector M f (sourceCoset M ∅ (spherical_empty M) x) k =
      pointedMultiplicity M f x k := by
  rw [pointedCosetVector_eq M f _ x (rightCoset_self M ∅ x) k]
  exact pointedHarmonicAt_empty M f x k

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_CosetContainment
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedProfile_apply _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.sourceCosetProfile_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Confining paths of parabolic cosets

This is the coset argument in Proposition 6.9 of paper 082-03. A path
whose types stay in one set cannot escape its standard coset. The proof
uses actual subgroup cosets, including upward as well as downward edges.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {S : Type*} (M : CoxeterMatrix S)

/-- A represented parabolic coset can be recentered at each of its points. -/
theorem deligne_coset_eq_at_point (P : Deligne M) (w : Artin M) (hw : w ∈ P.val.2) :
    P.val.2 = rightCoset M P.val.1 w := by
  obtain ⟨z, hz⟩ := P.property.2
  rw [hz] at hw ⊢
  ext a
  change a * z⁻¹ ∈ artinParabolic M P.val.1 ↔ a * w⁻¹ ∈ artinParabolic M P.val.1
  have he : a * z⁻¹ = (a * w⁻¹) * (w * z⁻¹) := by group
  rw [he]
  exact (artinParabolic M P.val.1).mul_mem_cancel_right hw

/-- Upward comparability preserves containment when the larger type is
still contained in the specified standard type. -/
theorem deligne_upper_contained {P R : Deligne M} (hPR : P ≤ R)
    (D : Set S) (z : Artin M) (hR : R.val.1 ⊆ D)
    (hP : P.val.2 ⊆ rightCoset M D z) : R.val.2 ⊆ rightCoset M D z := by
  obtain ⟨w, hw⟩ : P.val.2.Nonempty := by
    obtain ⟨w, hw⟩ := P.property.2
    refine ⟨w, ?_⟩
    rw [hw]
    change w * w⁻¹ ∈ artinParabolic M P.val.1
    simp
  rw [deligne_coset_eq_at_point M R w (hPR.2 hw)]
  exact rightCoset_subset_of_point M hR (hP hw)

/-- Every coset on a finite comparability path with types in `D` stays
inside the starting `D`-coset. This is the path confinement used at a
minimum of the relative height. -/
theorem deligne_path_contained (D : Set S) (z : Artin M) {P R : Deligne M}
    (hP : P.val.2 ⊆ rightCoset M D z)
    (path : Relation.ReflTransGen
      (fun A B : Deligne M => A.val.1 ⊆ D ∧ B.val.1 ⊆ D ∧ (A ≤ B ∨ B ≤ A)) P R) :
    R.val.2 ⊆ rightCoset M D z := by
  induction path with
  | refl => exact hP
  | @tail A B path edge ih =>
    rcases edge.2.2 with hAB | hBA
    · exact deligne_upper_contained M hAB D z edge.2.1 ih
    · exact hBA.2.trans ih

/-- If a confined path reaches the translate of its starting coset by
`r`, then `r` belongs to the corresponding conjugate standard subgroup. -/
theorem conjugate_membership_of_coset_path (D : Set S) (z r : Artin M)
    {P R : Deligne M} (hP : z ∈ P.val.2) (hPT : P.val.1 ⊆ D)
    (hR : z * r ∈ R.val.2)
    (path : Relation.ReflTransGen
      (fun A B : Deligne M => A.val.1 ⊆ D ∧ B.val.1 ⊆ D ∧ (A ≤ B ∨ B ≤ A)) P R) :
    r ∈ conjugate z⁻¹ (artinParabolic M D) := by
  have hstart : P.val.2 ⊆ rightCoset M D z := by
    rw [deligne_coset_eq_at_point M P z hP]
    exact rightCoset_subset_of_point M hPT (by
      change z * z⁻¹ ∈ artinParabolic M D
      simp)
  have hend := deligne_path_contained M D z hstart path hR
  change (z * r) * z⁻¹ ∈ artinParabolic M D at hend
  simpa only [mem_conjugate, inv_inv] using hend

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativePoset
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The connected poset of actual spherical cosets inside a fixed standard coset. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} (M : CoxeterMatrix S)

lemma relativeElement_le (Y : Set S) (x : Artin M) (P : RelativeVertex M Y x)
    (z : Artin M) (hz : z ∈ P.val.val.2) :
    relativeElement M Y x z (P.property.2 hz) ≤ P := by
  refine ⟨Set.empty_subset _, ?_⟩
  change rightCoset M ∅ z ⊆ P.val.val.2
  rw [rightCoset_empty]
  exact Set.singleton_subset_iff.mpr hz

lemma relativePath_symm {Y : Set S} {x : Artin M} {P R : RelativeVertex M Y x}
    (h : RelativePath M P R) : RelativePath M R P := by
  induction h with
  | refl => exact .refl
  | @tail A B h edge ih =>
    exact (Relation.ReflTransGen.single (r := relativeAdjacent M) (edge.elim Or.inr Or.inl)).trans ih

lemma relative_generator_step (Y : Set S) (x z : Artin M)
    (hz : z ∈ rightCoset M Y x) (s : S) (hs : s ∈ Y) :
    RelativePath M (relativeElement M Y x z hz)
      (relativeElement M Y x (generator M s*z) (by
        change (generator M s*z)*x⁻¹ ∈ artinParabolic M Y
        rw [_root_.mul_assoc]
        exact (artinParabolic M Y).mul_mem (Subgroup.subset_closure ⟨s,hs,rfl⟩) hz)) := by
  have hg : generator M s*z ∈ rightCoset M Y x := by
    change (generator M s*z)*x⁻¹ ∈ artinParabolic M Y
    rw [_root_.mul_assoc]
    exact (artinParabolic M Y).mul_mem (Subgroup.subset_closure ⟨s,hs,rfl⟩) hz
  let R := relativeVertex M Y {s} (spherical_singleton M s)
    (Set.singleton_subset_iff.mpr hs) x z hz
  have hzr : z ∈ R.val.val.2 := rightCoset_self M {s} z
  have hgr : generator M s*z ∈ R.val.val.2 := by
    change (generator M s*z)*z⁻¹ ∈ artinParabolic M {s}
    simp only [_root_.mul_assoc, mul_inv_cancel, _root_.mul_one]
    exact Subgroup.subset_closure ⟨s,rfl,rfl⟩
  exact (Relation.ReflTransGen.single (r := relativeAdjacent M) (Or.inl (relativeElement_le M Y x R z hzr))).tail
    (Or.inr (relativeElement_le M Y x R _ hgr))

/-- Left multiplication by a word in the ambient standard subgroup gives
an explicit comparability path through rank-one cosets. -/
lemma relative_element_connected (Y : Set S) (x g : Artin M)
    (hg : g ∈ artinParabolic M Y) :
    RelativePath M (relativeElement M Y x x (rightCoset_self M Y x))
      (relativeElement M Y x (g*x) (by
        change (g*x)*x⁻¹ ∈ artinParabolic M Y
        simpa only [_root_.mul_assoc, mul_inv_cancel, _root_.mul_one] using hg)) := by
  induction hg using Subgroup.closure_induction_left with
  | one => simpa only [_root_.one_mul] using (Relation.ReflTransGen.refl
      (a := relativeElement M Y x x (rightCoset_self M Y x)))
  | mul_left a ha g hg ih =>
    obtain ⟨s, hs, rfl⟩ := ha
    have h := relative_generator_step M Y x (g*x) (by
      change (g*x)*x⁻¹ ∈ artinParabolic M Y
      simpa only [_root_.mul_assoc, mul_inv_cancel, _root_.mul_one] using (show g ∈ artinParabolic M Y from hg)) s hs
    simpa only [_root_.mul_assoc] using ih.trans h
  | inv_mul_cancel a ha g hg ih =>
    obtain ⟨s, hs, rfl⟩ := ha
    have hg' : (generator M s)⁻¹*g ∈ artinParabolic M Y :=
      (artinParabolic M Y).mul_mem
        ((artinParabolic M Y).inv_mem (Subgroup.subset_closure ⟨s,hs,rfl⟩)) hg
    have h := relative_generator_step M Y x (((generator M s)⁻¹*g)*x) (by
      change (((generator M s)⁻¹*g)*x)*x⁻¹ ∈ artinParabolic M Y
      simpa only [_root_.mul_assoc, mul_inv_cancel, _root_.mul_one] using hg') s hs
    have he : generator M s * (((generator M s)⁻¹*g)*x) = g*x := by group
    simp only [he] at h
    exact ih.trans (relativePath_symm M h)

/-- The relative spherical-coset poset is connected, without assuming that
its ambient type is spherical. -/
theorem relative_poset_connected (Y : Set S) (x : Artin M)
    (P R : RelativeVertex M Y x) : RelativePath M P R := by
  have base (P : RelativeVertex M Y x) :
      RelativePath M (relativeElement M Y x x (rightCoset_self M Y x)) P := by
    let z := sourceCosetRepresentative M P.val
    have hz : z ∈ P.val.val.2 := sourceCosetRepresentative_mem M P.val
    have hzx : z ∈ rightCoset M Y x := P.property.2 hz
    have h := relative_element_connected M Y x (z*x⁻¹) hzx
    have he : (z*x⁻¹)*x = z := by group
    simp only [he] at h
    exact h.tail (Or.inl (relativeElement_le M Y x P z hz))
  exact (relativePath_symm M (base P)).trans (base R)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeHeight
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The relative harmonic height

The finite-support, highest-level-first height of §6.2 of paper 082-03.
The last coordinate is the full closed-type sign mask. The cutoff is an
arbitrary integer; null signs can occur at the cutoff itself.
-/

namespace HarmonicArtin.ParabolicIntersections

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

lemma relativeHeight_eq_blocks {P R : Deligne M}
    (he : relativeHeight M f U cutoff P = relativeHeight M f U cutoff R) (k : ℕ) :
    relativeBlock M f U cutoff P k = relativeBlock M f U cutoff R k := by
  apply (relativeBlockRank_eq_iff M f U cutoff (Or.inr ⟨P, k, rfl⟩) (Or.inr ⟨R, k, rfl⟩)).mp
  exact congrArg (fun h : Colex (ℕ →₀ ℕ) => ofColex h k) he

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeTies
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Visible and invisible sets along tied comparable vertices, §6.5 of paper 082-03. -/

namespace HarmonicArtin.ParabolicIntersections

open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

omit [LinearOrder S] in
lemma relativeSign_eq_zero_iff (p : ℕ →₀ (S ⊕ Unit → ℝ)) (k : ℕ) (i : S ⊕ Unit) :
    relativeSign M U p k i = 0 ↔ p k i = 0 := by
  unfold relativeSign
  split_ifs <;> simp_all

lemma relativeHeight_eq_profiles {P R : Deligne M}
    (he : relativeHeight M f U cutoff P = relativeHeight M f U cutoff R) (k : ℕ) :
    pointedProfile M f P cutoff k = pointedProfile M f R cutoff k := by
  have hb := relativeHeight_eq_blocks M f U cutoff he k
  have hv := congrArg (fun b : RelativeBlock S => (ofLex (ofLex b).2).1) hb
  exact congrArg ofLex hv

lemma relativeHeight_eq_masks {P R : Deligne M}
    (he : relativeHeight M f U cutoff P = relativeHeight M f U cutoff R) (k : ℕ) :
    relativeSignMask M f U cutoff P k = relativeSignMask M f U cutoff R k := by
  have hb := relativeHeight_eq_blocks M f U cutoff he k
  have hv := congrArg (fun b : RelativeBlock S => (ofLex (ofLex b).2).2) hb
  exact congrArg ofLex hv

lemma relativeInvisible_eq_of_height_eq (Y : Set S) {P R : Deligne M}
    (he : relativeHeight M f U cutoff P = relativeHeight M f U cutoff R) :
    relativeInvisible M f cutoff Y P = relativeInvisible M f cutoff Y R := by
  ext i
  constructor
  · rintro ⟨hi, hh⟩
    refine ⟨hi, fun k => ?_⟩
    unfold levelIncident at *
    rw [← relativeHeight_eq_profiles M f U cutoff he k]
    exact hh k
  · rintro ⟨hi, hh⟩
    refine ⟨hi, fun k => ?_⟩
    unfold levelIncident at *
    rw [relativeHeight_eq_profiles M f U cutoff he k]
    exact hh k

/-- Each new closed color at a tied upper vertex has no recorded incidence. -/
lemma tied_new_color_invisible (Y : Set S) {P R : Deligne M}
    (hR : R.val.1 ⊆ Y)
    (he : relativeHeight M f U cutoff P = relativeHeight M f U cutoff R)
    (i : S) (hi : i ∈ R.val.1) (hn : i ∉ P.val.1) :
    i ∈ relativeInvisible M f cutoff Y R := by
  refine ⟨hR hi, ?_⟩
  intro k hinc
  have hm := congrFun (relativeHeight_eq_masks M f U cutoff he k) (toLex (.inl i))
  have hp : (.inl i : S ⊕ Unit) ∉ Sum.inl '' P.val.1 := by
    rintro ⟨j, hj, heq⟩
    exact hn (Sum.inl.inj heq ▸ hj)
  have hr : (.inl i : S ⊕ Unit) ∈ Sum.inl '' R.val.1 := ⟨i, hi, rfl⟩
  simp only [relativeSignMask, ofLex_toLex, hp, hr, ↓reduceIte] at hm
  have hz : pointedProfile M f R cutoff k (.inl i) = 0 :=
    (relativeSign_eq_zero_iff M U _ k _).mp hm.symm
  rcases hinc with hpos | ⟨j, hij, hj⟩
  · exact (ne_of_gt hpos) hz
  · have hrow : (framedCartan M *ᵥ pointedProfile M f R cutoff k) (.inl i) = 0 :=
      pointedCosetVector_harmonic M f R (cutoff + k) ⟨.inl i, hr⟩
    have hpos := harmonic_positive_neighbor_at (framedCartan M) (framedCartan_off M)
      _ (pointedCosetVector_nonneg M f R (cutoff + k)) (le_of_eq hrow.symm) hij hj
    exact (ne_of_gt hpos) hz

/-- The visible closed set is constant across a tied comparability edge. -/
lemma relativeVisible_eq_of_tie (Y : Set S) {P R : Deligne M} (hPR : P ≤ R)
    (hR : R.val.1 ⊆ Y)
    (he : relativeHeight M f U cutoff P = relativeHeight M f U cutoff R) :
    relativeVisible M f cutoff Y P = relativeVisible M f cutoff Y R := by
  have hK := relativeInvisible_eq_of_height_eq M f U cutoff Y he
  ext i
  constructor
  · rintro ⟨hi, hn⟩
    exact ⟨hPR.1 hi, by rwa [← hK]⟩
  · rintro ⟨hi, hn⟩
    have hp : i ∈ P.val.1 := by
      by_contra hp
      exact hn (tied_new_color_invisible M f U cutoff Y hR he i hi hp)
    exact ⟨hp, by rwa [hK]⟩

/-- A visible closed color is positive at some recorded level. -/
lemma relativeVisible_positive (Y : Set S) (P : Deligne M) (hP : P.val.1 ⊆ Y)
    (i : S) (hi : i ∈ relativeVisible M f cutoff Y P) :
    ∃ k, 0 < pointedProfile M f P cutoff k (.inl i) := by
  have hex : ∃ k, levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i) := by
    by_contra hh
    exact hi.2 ⟨hP hi.1, fun k hk => hh ⟨k, hk⟩⟩
  obtain ⟨k, hk⟩ := hex
  refine ⟨k, ?_⟩
  rcases hk with hp | ⟨j, hij, hj⟩
  · exact hp
  · have hrow : (framedCartan M *ᵥ pointedProfile M f P cutoff k) (.inl i) = 0 :=
      pointedCosetVector_harmonic M f P (cutoff + k) ⟨.inl i, ⟨i, hi.1, rfl⟩⟩
    exact harmonic_positive_neighbor_at (framedCartan M) (framedCartan_off M) _
      (pointedCosetVector_nonneg M f P (cutoff + k)) (le_of_eq hrow.symm) hij hj

/-- Visible closed colors cannot be adjacent to any invisible color. -/
lemma relativeVisible_nonadjacent (Y : Set S) (P : Deligne M) (hP : P.val.1 ⊆ Y)
    (i j : S) (hi : i ∈ relativeInvisible M f cutoff Y P)
    (hj : j ∈ relativeVisible M f cutoff Y P) :
    ¬framedCartan M (.inl i) (.inl j) < 0 := by
  intro hij
  obtain ⟨k, hk⟩ := relativeVisible_positive M f cutoff Y P hP j hj
  exact hi.2 k (Or.inr ⟨.inl j, hij, hk⟩)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeTranslation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Right translation of the relative coset poset by a transported stabilizer. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma mem_deligneRightTranslate (P : Deligne M) (r z : Artin M) :
    z ∈ (deligneRightTranslate M P r).val.2 ↔ z*r⁻¹ ∈ P.val.2 := by
  rw [sourceCosetRepresentative_spec M P]
  change z*(sourceCosetRepresentative M P*r)⁻¹ ∈ artinParabolic M P.val.1 ↔
    (z*r⁻¹)*(sourceCosetRepresentative M P)⁻¹ ∈ artinParabolic M P.val.1
  simp only [mul_inv_rev, _root_.mul_assoc]

lemma pointedFamily_transport_fixed (f : S) (x a : Artin M)
    (ha : pointedFamily M f (a*x) = pointedFamily M f x) (z : Artin M) :
    pointedFamily M f (z*(x⁻¹*a*x)) = pointedFamily M f z := by
  have h1 : z*(x⁻¹*a*x) = (z*x⁻¹)*(a*x) := by group
  have h2 : (z*x⁻¹)*x = z := by group
  funext L
  rw [h1, pointedFamily_mul, congrFun ha L, ←pointedFamily_mul, h2]

lemma pointedCosetVector_translate_fixed (f : S) (x a : Artin M)
    (ha : pointedFamily M f (a*x) = pointedFamily M f x) (P : Deligne M) (k : ℤ) :
    pointedCosetVector M f (deligneRightTranslate M P (x⁻¹*a*x)) k =
      pointedCosetVector M f P k := by
  let z := sourceCosetRepresentative M P
  have hz : z*(x⁻¹*a*x) ∈ (deligneRightTranslate M P (x⁻¹*a*x)).val.2 :=
    rightCoset_self M _ _
  rw [pointedCosetVector_eq M f _ _ hz k]
  change pointedHarmonicAt M f P.val.1 (z*(x⁻¹*a*x)) k = pointedHarmonicAt M f P.val.1 z k
  unfold pointedHarmonicAt
  congr 1
  unfold pointedMultiplicity
  rw [pointedFamily_transport_fixed M f x a ha z]

lemma relativeHeight_congr (f : S) (U : Set (S ⊕ Unit)) (cutoff : ℤ)
    (P R : Deligne M) (ht : P.val.1 = R.val.1)
    (hv : ∀ k, pointedCosetVector M f P k = pointedCosetVector M f R k) :
    relativeHeight M f U cutoff P = relativeHeight M f U cutoff R := by
  have hp : pointedProfile M f P cutoff = pointedProfile M f R cutoff := by
    ext k i
    exact congrFun (hv (cutoff+k)) i
  have hm (k : ℕ) : relativeSignMask M f U cutoff P k = relativeSignMask M f U cutoff R k := by
    unfold relativeSignMask
    rw [ht, hp]
  have hb (k : ℕ) : relativeBlock M f U cutoff P k = relativeBlock M f U cutoff R k := by
    unfold relativeBlock pointedCosetSum
    rw [hv, hp, hm]
  apply congrArg toColex
  ext k
  change relativeBlockRank M f U cutoff (relativeBlock M f U cutoff P k) =
    relativeBlockRank M f U cutoff (relativeBlock M f U cutoff R k)
  rw [hb]

/-- A transported stabilizer preserves the complete relative height,
including every sign-mask coordinate. -/
lemma relativeHeight_translate_fixed (f : S) (U : Set (S ⊕ Unit)) (cutoff : ℤ)
    (x a : Artin M) (ha : pointedFamily M f (a*x) = pointedFamily M f x) (P : Deligne M) :
    relativeHeight M f U cutoff (deligneRightTranslate M P (x⁻¹*a*x)) =
      relativeHeight M f U cutoff P :=
  relativeHeight_congr M f U cutoff _ _ rfl (pointedCosetVector_translate_fixed M f x a ha P)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_InitialMinimum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.sourceCosetProfile_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial singleton is a minimum of the full relative harmonic height. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)

private lemma vector_eq_single_of_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (o : ι) (hn : ∀ i, 0 ≤ v i) (ho : v o = 1)
    (hs : ∑ i, v i = 1) : v = (Pi.single o (1:ℝ) : ι → ℝ) := by
  have hnon (i : ι) : 0 ≤ v i - (Pi.single o (1:ℝ) : ι → ℝ) i := by
    by_cases hi : i = o
    · subst i
      simp only [Pi.single_eq_same, ho, sub_self, le_refl]
    · simpa only [Pi.single_eq_of_ne hi, sub_zero] using hn i
  have hsum : ∑ i, (v i - (Pi.single o (1:ℝ) : ι → ℝ) i) = 0 := by
    rw [Finset.sum_sub_distrib, hs]
    simp
  funext i
  exact sub_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnon i)).mp hsum i
    (Finset.mem_univ i))

lemma initial_profile (cutoff : ℤ) (k : ℕ) :
    pointedProfile M f (sourceCoset M ∅ (spherical_empty M) 1) cutoff k =
      if cutoff+k = 0 then Pi.single (.inl f) 1 else 0 := by
  ext i
  change pointedCosetVector M f (sourceCoset M ∅ (spherical_empty M) 1) (cutoff+k) i = _
  rw [pointedCosetVector_empty, pointedMultiplicity_one]
  by_cases hk : cutoff+k = 0 <;> simp [hk, Pi.single_apply]

lemma pointedCosetVector_frame_of_relative (Y : Set S) (hf : f ∉ Y)
    (P : RelativeVertex M Y 1) (k : ℤ) :
    pointedCosetVector M f P.val k (.inl f) = if k = 0 then 1 else 0 := by
  have hfP : (.inl f : S ⊕ Unit) ∉ Sum.inl '' P.val.val.1 := by
    rintro ⟨i, hi, he⟩
    exact hf (Sum.inl.inj he ▸ P.property.1 hi)
  have hz : sourceCosetRepresentative M P.val ∈ artinParabolic M Y := by
    have h := P.property.2 (sourceCosetRepresentative_mem M P.val)
    simpa only [rightCoset, Set.mem_ofPred_eq, inv_one, _root_.mul_one] using h
  change pointedHarmonicAt M f P.val.val.1 _ k (.inl f) = _
  rw [pointedHarmonicAt_outside M f _ _ k _ hfP]
  exact pointedMultiplicity_frame M Y f hf _ hz k

lemma initial_block_le (U : Set (S ⊕ Unit)) (cutoff : ℤ) (Y : Set S) (hf : f ∉ Y)
    (P : RelativeVertex M Y 1) (k : ℕ) :
    relativeBlock M f U cutoff (sourceCoset M ∅ (spherical_empty M) 1) k ≤
      relativeBlock M f U cutoff P.val k := by
  let P₀ := sourceCoset M ∅ (spherical_empty M) 1
  change relativeBlock M f U cutoff P₀ k ≤ relativeBlock M f U cutoff P.val k
  have hmask₀ : relativeSignMask M f U cutoff P₀ k = 0 := by
    funext i
    simp only [relativeSignMask, P₀, sourceCoset, Set.image_empty, Set.notMem_empty,
      ↓reduceIte, Pi.zero_apply]
  by_cases hk : cutoff+k = 0
  · have hv₀ : pointedProfile M f P₀ cutoff k = Pi.single (.inl f) 1 := by
      simpa only [hk, ite_true, if_true] using initial_profile M f cutoff k
    have hs₀ : pointedCosetSum M f P₀ (cutoff+k) = 1 := by
      change (∑ i, pointedProfile M f P₀ cutoff k i) = 1
      rw [hv₀]
      simp
    have hframe : pointedProfile M f P.val cutoff k (.inl f) = 1 := by
      change pointedCosetVector M f P.val (cutoff+k) (.inl f) = 1
      rw [pointedCosetVector_frame_of_relative M f Y hf P, hk, ite_eq_left rfl]
    have hs : 1 ≤ pointedCosetSum M f P.val (cutoff+k) := by
      rw [←hframe]
      exact pointedCosetVector_le_sum M f P.val (cutoff+k) (.inl f)
    rcases lt_or_eq_of_le hs with hlt | heq
    · have hh : pointedCosetSum M f P₀ (cutoff+k) < pointedCosetSum M f P.val (cutoff+k) := by
        rw [hs₀]
        exact hlt
      exact (Prod.Lex.lt_iff.mpr (Or.inl hh)).le
    · have hv : pointedProfile M f P.val cutoff k = Pi.single (.inl f) 1 :=
        vector_eq_single_of_sum _ _ (pointedCosetVector_nonneg M f P.val (cutoff+k)) hframe heq.symm
      have hm : relativeSignMask M f U cutoff P.val k = 0 := by
        funext i
        unfold relativeSignMask
        by_cases hi : ofLex i ∈ Sum.inl '' P.val.val.1
        · have hne : ofLex i ≠ (.inl f : S ⊕ Unit) := by
            intro h
            obtain ⟨j, hj, hjf⟩ := hi
            exact hf (Sum.inl.inj (hjf.trans h) ▸ P.property.1 hj)
          simp only [hi, ↓reduceIte, relativeSign, hv, Pi.single_eq_of_ne hne,
            ↓reduceIte, Pi.zero_apply]
        · simp only [hi, ↓reduceIte, Pi.zero_apply]
      unfold relativeBlock
      rw [hs₀, ←heq, hv₀, hv, hmask₀, hm]
  · have hz : pointedProfile M f P₀ cutoff k = 0 := by
      simpa only [hk, ite_false, if_false] using initial_profile M f cutoff k
    rw [relativeBlock_of_vector_zero M f U cutoff P₀ k hz]
    exact relativeZeroBlock_le M f U cutoff _ (Or.inr ⟨P.val,k,rfl⟩)

/-- The minimum-height assertion in the proof of the initial stabilizer,
including the full vector and full sign mask. -/
theorem initial_height_minimum (U : Set (S ⊕ Unit)) (cutoff : ℤ) (Y : Set S) (hf : f ∉ Y)
    (P : RelativeVertex M Y 1) :
    relativeHeight M f U cutoff (sourceCoset M ∅ (spherical_empty M) 1) ≤
      relativeHeight M f U cutoff P.val := by
  apply Finsupp.toColex_monotone
  intro k
  have hb := initial_block_le M f U cutoff Y hf P k
  change relativeBlockRank M f U cutoff _ ≤ relativeBlockRank M f U cutoff _
  rcases lt_or_eq_of_le hb with hb | hb
  · exact (relativeBlockRank_strictMono M f U cutoff (Or.inr ⟨_,k,rfl⟩) hb).le
  · rw [hb]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ConnectedMinima
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Lowering paths across tied heights

This is the finite-path argument of §6.5 of paper 082-03. The local
hypotheses are precisely the connected descending neighborhoods and the
compatibility across tied adjacent vertices. They are not installed as
published assumptions; their verification for the relative harmonic
height is a separate part of that paper's proof.
-/

namespace HarmonicArtin.ParabolicIntersections

section Paths

variable {V H : Type*} [LinearOrder H]
variable (adj : V → V → Prop) (height : V → H)

private theorem path_mono {p q : V → Prop} (hpq : ∀ v, p v → q v)
    {a b : V} (h : PathWithin adj p a b) : PathWithin adj q a b :=
  by
    induction h with
    | refl => exact .refl
    | tail _ he ih => exact ih.tail ⟨hpq _ he.1, hpq _ he.2.1, he.2.2⟩

/-- Remove all occurrences of one maximal height in a finite path.
The invariant also covers a whole segment of tied vertices. -/
theorem lower_path (D : LocalDescent adj height) (h : H)
    {a b : V} (ha : height a < h) (hb : height b < h)
    (p : PathWithin adj (fun v => height v ≤ h) a b) :
    PathWithin adj (fun v => height v < h) a b := by
  have step : ∀ {v}, PathWithin adj (fun z => height z ≤ h) a v →
      (height v < h ∧ PathWithin adj (fun z => height z < h) a v) ∨
      (height v = h ∧ ∃ c, adj v c ∧ height c < h ∧
        PathWithin adj (fun z => height z < h) a c) := by
    intro v hv
    induction hv with
    | refl => exact Or.inl ⟨ha, .refl⟩
    | @tail v w p edge ih =>
      obtain ⟨_, hw, hvw⟩ := edge
      by_cases hwl : height w < h
      · left
        refine ⟨hwl, ?_⟩
        rcases ih with ⟨hvl, pav⟩ | ⟨hve, c, hvc, hcl, pac⟩
        · exact pav.tail ⟨hvl, hwl, hvw⟩
        · have pcw := D.descending v c w hvc (hve ▸ hcl) hvw (hve ▸ hwl)
          rw [hve] at pcw
          exact pac.trans pcw
      · right
        have hwe : height w = h := le_antisymm hw (le_of_not_gt hwl)
        refine ⟨hwe, ?_⟩
        rcases ih with ⟨hvl, pav⟩ | ⟨hve, c, hvc, hcl, pac⟩
        · exact ⟨v, D.symmetric hvw, hvl, pav⟩
        · obtain ⟨d, hwd, hdl, pcd⟩ := D.tied v w hvw (hve.trans hwe.symm)
            c hvc (hve ▸ hcl)
          rw [hve] at pcd
          exact ⟨d, hwd, hwe ▸ hdl, pac.trans pcd⟩
  rcases step p with ⟨_, hp⟩ | ⟨he, _⟩
  · exact hp
  · exact (ne_of_lt hb he).elim

private theorem bounded_path {a b : V} (p : Relation.ReflTransGen adj a b) :
    ∃ h, height a ≤ h ∧ PathWithin adj (fun v => height v ≤ h) a b := by
  induction p with
  | refl => exact ⟨height a, le_rfl, .refl⟩
  | @tail v w p edge ih =>
    obtain ⟨h, ha, hp⟩ := ih
    refine ⟨max h (height w), ha.trans (le_max_left _ _), ?_⟩
    have hv : height v ≤ max h (height w) := by
      rcases hp.cases_tail with rfl | ⟨u, _, _, hv, _⟩
      · exact ha.trans (le_max_left _ _)
      · exact hv.trans (le_max_left _ _)
    exact (path_mono adj (fun _ hv => hv.trans (le_max_left _ _)) hp).tail
      ⟨hv, le_max_right _ _, edge⟩

private theorem strictly_bounded_path (h : H) {a b : V} (ha : height a < h)
    (p : PathWithin adj (fun v => height v < h) a b) :
    ∃ k, k < h ∧ height a ≤ k ∧ PathWithin adj (fun v => height v ≤ k) a b := by
  induction p with
  | refl => exact ⟨height a, ha, le_rfl, .refl⟩
  | @tail v w p edge ih =>
    obtain ⟨k, hk, hak, pk⟩ := ih
    obtain ⟨_, hw, hvw⟩ := edge
    refine ⟨max k (height w), max_lt hk hw, hak.trans (le_max_left _ _), ?_⟩
    have hvk : height v ≤ k := by
      rcases pk.cases_tail with rfl | ⟨u, _, _, hvk, _⟩
      · exact hak
      · exact hvk
    exact (path_mono adj (fun _ hz => hz.trans (le_max_left _ _)) pk).tail
      ⟨hvk.trans (le_max_left _ _), le_max_right _ _, hvw⟩

/-- Every sublevel of a well-founded height with the two local descent
properties contains a path between any of its vertices that were connected
in the original graph. -/
theorem sublevel_path (D : LocalDescent adj height)
    (wf : WellFounded ((· < ·) : H → H → Prop)) (c : H)
    {a b : V} (ha : height a ≤ c) (hb : height b ≤ c)
    (p : Relation.ReflTransGen adj a b) :
    PathWithin adj (fun v => height v ≤ c) a b := by
  obtain ⟨h, hbound, hp⟩ := bounded_path adj height p
  clear hbound
  induction h using wf.induction with
  | h h ih =>
    by_cases hc : h ≤ c
    · exact path_mono adj (fun _ hv => hv.trans hc) hp
    · have hch : c < h := lt_of_not_ge hc
      have pl := lower_path adj height D h (ha.trans_lt hch) (hb.trans_lt hch) hp
      obtain ⟨k, hk, _, pk⟩ := strictly_bounded_path adj height h (ha.trans_lt hch) pl
      exact ih k hk pk

/-- The minimum-height vertices in a connected graph form a connected
subgraph. This is the path-lowering conclusion used in §6.5. -/
theorem minimum_path (D : LocalDescent adj height)
    (wf : WellFounded ((· < ·) : H → H → Prop))
    {a b : V} (ha : ∀ v, height a ≤ height v) (hb : ∀ v, height b ≤ height v)
    (p : Relation.ReflTransGen adj a b) :
    PathWithin adj (fun v => ∀ w, height v ≤ height w) a b := by
  have hp := sublevel_path adj height D wf (height a) le_rfl (hb a) p
  exact path_mono adj (fun v hv w => hv.trans (ha w)) hp

end Paths

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
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeUpperBasics
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Highest-incidence comparisons for upper edges of the relative filtration. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

lemma relative_no_incidence {P : Deligne M} {k : ℕ} {i : S}
    (hn : ¬levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i)) :
    pointedProfile M f P cutoff k (.inl i) = 0 ∧
    (framedCartan M *ᵥ pointedProfile M f P cutoff k) (.inl i) = 0 ∧
    relativeSign M U (pointedProfile M f P cutoff) k (.inl i) = 0 := by
  have hz : pointedProfile M f P cutoff k (.inl i) = 0 := le_antisymm
    (le_of_not_gt (fun h => hn (Or.inl h))) (pointedCosetVector_nonneg M f P _ _)
  refine ⟨hz, no_incidence_row_zero (framedCartan M) (framedCartan_off M) _
    (fun k i => pointedCosetVector_nonneg M f P (cutoff+k) i) hn, ?_⟩
  simp only [relativeSign, hz, ↓reduceIte]

lemma relative_above_incidence {P : Deligne M} {k : ℕ} {i : S}
    (h : relativeIncidence M f cutoff P i < k) :
    ¬levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i) :=
  fun hi => (not_le_of_gt h) (levelIncident_le _ _ hi)

lemma relativeIncidence_le_upperLevel (P R : Deligne M) (i : S)
    (hi : i ∈ R.val.1) (ht : i ∉ P.val.1) :
    relativeIncidence M f cutoff P i ≤ relativeUpperLevel M f cutoff P R :=
  Finset.le_sup (f := relativeIncidence M f cutoff P) (by simp [hi, ht])

lemma relativeProfile_eq_above_upper {P R : Deligne M} (h : P ≤ R) {k : ℕ}
    (hk : relativeUpperLevel M f cutoff P R < k) :
    pointedProfile M f R cutoff k = pointedProfile M f P cutoff k := by
  apply pointedCosetVector_eq_of_upper_rows M f h (cutoff+k)
  intro i hi ht
  exact (relative_no_incidence M f ∅ cutoff (relative_above_incidence M f cutoff
    ((relativeIncidence_le_upperLevel M f cutoff P R i hi ht).trans_lt hk))).2.1

lemma relativeBlock_eq_above_upper {P R : Deligne M} (h : P ≤ R) {k : ℕ}
    (hk : relativeUpperLevel M f cutoff P R < k) :
    relativeBlock M f U cutoff R k = relativeBlock M f U cutoff P k := by
  have hv := relativeProfile_eq_above_upper M f cutoff h hk
  have hs (i : S ⊕ Unit) :
      relativeSign M U (pointedProfile M f R cutoff) k i =
        relativeSign M U (pointedProfile M f P cutoff) k i :=
    relativeSign_congr_above M U _ _ k
      (fun d hd => relativeProfile_eq_above_upper M f cutoff h (hk.trans_le hd)) i
  have hm : relativeSignMask M f U cutoff R k = relativeSignMask M f U cutoff P k := by
    funext i
    unfold relativeSignMask
    by_cases hp : ofLex i ∈ Sum.inl '' P.val.1
    · have hr := Set.image_mono h.1 hp
      simp only [hp, hr, ↓reduceIte, hs]
    · by_cases hr : ofLex i ∈ Sum.inl '' R.val.1
      · obtain ⟨j, hj, he⟩ := hr
        have hjp : j ∉ P.val.1 := fun h => hp ⟨j,h,he⟩
        have hz := (relative_no_incidence M f U cutoff (relative_above_incidence M f cutoff
          ((relativeIncidence_le_upperLevel M f cutoff P R j hj hjp).trans_lt hk))).2.2
        simp only [hs, ←he, hz, ite_self]
      · simp only [hp, hr, ↓reduceIte]
  unfold relativeBlock
  have hsum : pointedCosetSum M f R (cutoff+k) = pointedCosetSum M f P (cutoff+k) :=
    congrArg (fun v : S ⊕ Unit → ℝ => ∑ i, v i) hv
  rw [hsum, hv, hm]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeUpperSigns
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Active-color rows and full sign masks at an upper comparison level. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

lemma relative_active_incident (P : Deligne M) (i : S)
    (ha : relativeColorActive M f U cutoff P i) :
    levelIncident (framedCartan M) (pointedProfile M f P cutoff)
      (relativeIncidence M f cutoff P i) (.inl i) := by
  by_contra hn
  have hz := relative_no_incidence M f U cutoff hn
  rcases ha with hp | ⟨_,hp,_⟩
  · exact (ne_of_gt hp) hz.2.1
  · exact (ne_of_gt hp) hz.1

lemma relative_active_sign (P : Deligne M) (i : S)
    (ha : relativeColorActive M f U cutoff P i)
    (hr : (framedCartan M *ᵥ pointedProfile M f P cutoff
      (relativeIncidence M f cutoff P i)) (.inl i) = 0) :
    relativeSign M U (pointedProfile M f P cutoff) (relativeIncidence M f cutoff P i) (.inl i) = -1 := by
  change 0 < (framedCartan M *ᵥ pointedProfile M f P cutoff (relativeIncidence M f cutoff P i)) (.inl i) ∨
    (framedCartan M *ᵥ pointedProfile M f P cutoff (relativeIncidence M f cutoff P i)) (.inl i) = 0 ∧
    0 < pointedProfile M f P cutoff (relativeIncidence M f cutoff P i) (.inl i) ∧
    ¬relativePositiveSign (framedCartan M) U (pointedProfile M f P cutoff)
      (relativeIncidence M f cutoff P i) (.inl i) at ha
  rcases ha with hp | ⟨_,hp,hn⟩
  · exact ((ne_of_gt hp) hr).elim
  · change 0 < pointedProfile M f P cutoff (relativeIncidence M f cutoff P i) (.inl i) at hp
    change ¬relativePositiveSign (framedCartan M) U (pointedProfile M f P cutoff)
      (relativeIncidence M f cutoff P i) (.inl i) at hn
    simp only [relativeSign, ne_of_gt hp, hn, ↓reduceIte]

lemma relative_inactive_sign (P : Deligne M) (i : S) (k : ℕ)
    (ha : ¬relativeColorActive M f U cutoff P i)
    (hk : k = relativeIncidence M f cutoff P i)
    (hi : levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i))
    (hr : (framedCartan M *ᵥ pointedProfile M f P cutoff k) (.inl i) = 0) :
    relativeSign M U (pointedProfile M f P cutoff) k (.inl i) = 1 := by
  have hp : 0 < pointedProfile M f P cutoff k (.inl i) := by
    rcases hi with hp | ⟨j,hij,hj⟩
    · exact hp
    · exact harmonic_positive_neighbor_at (framedCartan M) (framedCartan_off M) _
        (pointedCosetVector_nonneg M f P (cutoff+k)) (le_of_eq hr.symm) hij hj
  have hs : relativePositiveSign (framedCartan M) U (pointedProfile M f P cutoff) k (.inl i) := by
    by_contra hn
    apply ha
    change relativeActive (framedCartan M) U (pointedProfile M f P cutoff) (.inl i)
    change 0 < (framedCartan M *ᵥ pointedProfile M f P cutoff (relativeIncidence M f cutoff P i)) (.inl i) ∨
      (framedCartan M *ᵥ pointedProfile M f P cutoff (relativeIncidence M f cutoff P i)) (.inl i) = 0 ∧
      0 < pointedProfile M f P cutoff (relativeIncidence M f cutoff P i) (.inl i) ∧
      ¬relativePositiveSign (framedCartan M) U (pointedProfile M f P cutoff)
        (relativeIncidence M f cutoff P i) (.inl i)
    rw [←hk]
    exact Or.inr ⟨hr,hp,hn⟩
  simp only [relativeSign, ne_of_gt hp, hs, ↓reduceIte]

lemma relative_upper_inactive_rows (P R : Deligne M)
    (ha : ∀ i ∈ R.val.1, i ∉ P.val.1 → ¬relativeColorActive M f U cutoff P i)
    (i : S) (hi : i ∈ R.val.1) (ht : i ∉ P.val.1) :
    (framedCartan M *ᵥ pointedProfile M f P cutoff (relativeUpperLevel M f cutoff P R)) (.inl i) ≤ 0 := by
  rcases eq_or_lt_of_le (relativeIncidence_le_upperLevel M f cutoff P R i hi ht) with he | he
  · have hn : ¬0 < (framedCartan M *ᵥ pointedProfile M f P cutoff
        (relativeIncidence M f cutoff P i)) (.inl i) := fun hp => ha i hi ht (Or.inl hp)
    rw [←he]
    exact le_of_not_gt hn
  · rw [(relative_no_incidence M f U cutoff (relative_above_incidence M f cutoff he)).2.1]

lemma relative_upper_active_rows (P R : Deligne M)
    (ha : ∀ i ∈ R.val.1, i ∉ P.val.1 → relativeColorActive M f U cutoff P i)
    (i : S) (hi : i ∈ R.val.1) (ht : i ∉ P.val.1) :
    0 ≤ (framedCartan M *ᵥ pointedProfile M f P cutoff (relativeUpperLevel M f cutoff P R)) (.inl i) := by
  rcases eq_or_lt_of_le (relativeIncidence_le_upperLevel M f cutoff P R i hi ht) with he | he
  · have hh := ha i hi ht
    have hrow : 0 ≤ (framedCartan M *ᵥ pointedProfile M f P cutoff
        (relativeIncidence M f cutoff P i)) (.inl i) := by
      rcases hh with hp | ⟨hz, _⟩
      · exact hp.le
      · exact hz.ge
    simpa only [he] using hrow
  · rw [(relative_no_incidence M f U cutoff (relative_above_incidence M f cutoff he)).2.1]

lemma relativeUpperLevel_incident (P R : Deligne M)
    (hsome : ∃ i ∈ R.val.1, i ∉ P.val.1 ∧ ∃ k,
      levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i)) :
    ∃ i ∈ R.val.1, i ∉ P.val.1 ∧
      levelIncident (framedCartan M) (pointedProfile M f P cutoff)
        (relativeUpperLevel M f cutoff P R) (.inl i) := by
  by_cases hk : relativeUpperLevel M f cutoff P R = 0
  · obtain ⟨i,hi,ht,k,hki⟩ := hsome
    have hle := (levelIncident_le _ _ hki).trans (relativeIncidence_le_upperLevel M f cutoff P R i hi ht)
    have he : k = relativeUpperLevel M f cutoff P R := by omega
    exact ⟨i,hi,ht,he ▸ hki⟩
  · obtain ⟨i,hi,ht,k,hki⟩ := hsome
    obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup
      (R.val.1.toFinset \ P.val.1.toFinset) ⟨i,by simp [hi,ht]⟩ (relativeIncidence M f cutoff P)
    have hjR : j ∈ R.val.1 := Set.mem_toFinset.mp (Finset.mem_sdiff.mp hj).1
    have hjP : j ∉ P.val.1 := fun h => (Finset.mem_sdiff.mp hj).2 (Set.mem_toFinset.mpr h)
    refine ⟨j,hjR,hjP,?_⟩
    have hex : ∃ k, levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl j) := by
      by_contra hn
      have hempty : incidenceIndices (framedCartan M) (pointedProfile M f P cutoff) (.inl j) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro d hd
        exact hn ⟨d,(Finset.mem_filter.mp hd).2⟩
      have hz : relativeIncidence M f cutoff P j = 0 := by
        simp only [relativeIncidence, incidenceLevel, hempty, Finset.sup_empty, bot_eq_zero]
      exact hk (he.trans hz)
    rw [show relativeUpperLevel M f cutoff P R = relativeIncidence M f cutoff P j from he]
    exact incidenceLevel_incident _ _ _ hex

lemma relative_sign_upper_tie {P R : Deligne M} (h : P ≤ R)
    (hv : pointedProfile M f R cutoff (relativeUpperLevel M f cutoff P R) =
      pointedProfile M f P cutoff (relativeUpperLevel M f cutoff P R)) (i : S ⊕ Unit) :
    relativeSign M U (pointedProfile M f R cutoff) (relativeUpperLevel M f cutoff P R) i =
      relativeSign M U (pointedProfile M f P cutoff) (relativeUpperLevel M f cutoff P R) i := by
  apply relativeSign_congr_above M U
  intro d hd
  rcases eq_or_lt_of_le hd with rfl | hd
  · exact hv
  · exact relativeProfile_eq_above_upper M f cutoff h hd

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeUpperComparison
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict upper-neighbor comparisons for the relative height. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

lemma relativeHeight_eq_of_new_invisible {P R : Deligne M} (h : P ≤ R)
    (hn : ∀ i ∈ R.val.1, i ∉ P.val.1 → ∀ k,
      ¬levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i)) :
    relativeHeight M f U cutoff R = relativeHeight M f U cutoff P := by
  have hv (k : ℕ) : pointedProfile M f R cutoff k = pointedProfile M f P cutoff k := by
    apply pointedCosetVector_eq_of_upper_rows M f h (cutoff+k)
    intro i hi ht
    exact (relative_no_incidence M f U cutoff (hn i hi ht k)).2.1
  have hs (k : ℕ) (i : S ⊕ Unit) := relativeSign_congr_above M U
    (pointedProfile M f R cutoff) (pointedProfile M f P cutoff) k (fun d _ => hv d) i
  apply relativeHeight_eq_of_blocks M f U cutoff
  intro k
  have hm : relativeSignMask M f U cutoff R k = relativeSignMask M f U cutoff P k := by
    funext i
    unfold relativeSignMask
    rw [hs]
    by_cases hp : ofLex i ∈ Sum.inl '' P.val.1
    · simp only [hp, Set.image_mono h.1 hp, ↓reduceIte]
    · by_cases hr : ofLex i ∈ Sum.inl '' R.val.1
      · obtain ⟨j,hj,he⟩ := hr
        have hjp : j ∉ P.val.1 := fun hh => hp ⟨j,hh,he⟩
        have hz := (relative_no_incidence M f U cutoff (hn j hj hjp k)).2.2
        simp only [←he, hz, ite_self]
      · simp only [hp, hr, ↓reduceIte]
  unfold relativeBlock
  have hsum : pointedCosetSum M f R (cutoff+k) = pointedCosetSum M f P (cutoff+k) :=
    congrArg (fun v : S ⊕ Unit → ℝ => ∑ i, v i) (hv k)
  rw [hsum, hv, hm]

lemma relativeUpper_inactive_le {P R : Deligne M} (h : P < R)
    (ha : ∀ i ∈ R.val.1, i ∉ P.val.1 → ¬relativeColorActive M f U cutoff P i) :
    relativeHeight M f U cutoff P ≤ relativeHeight M f U cutoff R := by
  by_cases hsome : ∃ i ∈ R.val.1, i ∉ P.val.1 ∧ ∃ k,
      levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i)
  · apply le_of_lt
    apply (relativeHeight_lt_iff M f U cutoff P R).mpr
    refine ⟨relativeUpperLevel M f cutoff P R,
      fun d hd => (relativeBlock_eq_above_upper M f U cutoff h.le hd).symm, ?_⟩
    let H := relativeUpperLevel M f cutoff P R
    by_cases hv : pointedProfile M f R cutoff H = pointedProfile M f P cutoff H
    · have hr (i : S) (hi : i ∈ R.val.1) :
          (framedCartan M *ᵥ pointedProfile M f P cutoff H) (.inl i) = 0 := by
        rw [←hv]
        exact pointedCosetVector_harmonic M f R (cutoff+H) ⟨.inl i,⟨i,hi,rfl⟩⟩
      have hs (i : S) (hi : i ∈ R.val.1) (ht : i ∉ P.val.1) :
          0 ≤ relativeSign M U (pointedProfile M f P cutoff) H (.inl i) := by
        by_cases hn : levelIncident (framedCartan M) (pointedProfile M f P cutoff) H (.inl i)
        · have he : H = relativeIncidence M f cutoff P i := le_antisymm
            (levelIncident_le _ _ hn) (relativeIncidence_le_upperLevel M f cutoff P R i hi ht)
          rw [relative_inactive_sign M f U cutoff P i H (ha i hi ht) he hn (hr i hi)]
          norm_num
        · rw [(relative_no_incidence M f U cutoff hn).2.2]
      have hsEq := relative_sign_upper_tie M f U cutoff h.le hv
      have hm := relative_mask_upper_nonneg M f U cutoff h.le H hsEq hs
      have hne : relativeSignMask M f U cutoff P H ≠ relativeSignMask M f U cutoff R H := by
        intro heq
        obtain ⟨i,hi,ht,hin⟩ := relativeUpperLevel_incident M f cutoff P R hsome
        have hiP : (.inl i : S ⊕ Unit) ∉ Sum.inl '' P.val.1 := by
          rintro ⟨j,hj,he⟩
          exact ht (Sum.inl.inj he ▸ hj)
        have hiR : (.inl i : S ⊕ Unit) ∈ Sum.inl '' R.val.1 := ⟨i,hi,rfl⟩
        have he : H = relativeIncidence M f cutoff P i := le_antisymm
          (levelIncident_le _ _ hin) (relativeIncidence_le_upperLevel M f cutoff P R i hi ht)
        have hz := congrFun heq (toLex (.inl i))
        simp only [relativeSignMask, ofLex_toLex, hiP, hiR, ↓reduceIte] at hz
        have hsi : relativeSign M U (pointedProfile M f R cutoff) H (.inl i) =
            relativeSign M U (pointedProfile M f P cutoff) H (.inl i) := hsEq _
        rw [hsi, relative_inactive_sign M f U cutoff P i H (ha i hi ht) he hin (hr i hi)] at hz
        norm_num at hz
      exact relativeBlock_lt_of_mask M f U cutoff hv.symm (lt_of_le_of_ne hm hne)
    · have hle := pointedCosetVector_upper_monotone_int M f h.le (cutoff+H)
        (relative_upper_inactive_rows M f U cutoff P R ha)
      exact Prod.Lex.lt_iff.mpr (Or.inl (harmonic_sum_lt_of_lt _ _ hle (Ne.symm hv)))
  · have hn : ∀ i ∈ R.val.1, i ∉ P.val.1 → ∀ k,
        ¬levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i) := by
      intro i hi ht k hin
      exact hsome ⟨i,hi,ht,k,hin⟩
    exact (relativeHeight_eq_of_new_invisible M f U cutoff h.le hn).symm.le

/-- Every descending upper neighbor adds an active color. -/
theorem relativeUpper_descending_has_active {P R : Deligne M} (h : P < R)
    (he : relativeHeight M f U cutoff R < relativeHeight M f U cutoff P) :
    ∃ i ∈ R.val.1, i ∉ P.val.1 ∧ relativeColorActive M f U cutoff P i := by
  by_contra hn
  have hle := relativeUpper_inactive_le M f U cutoff h
    (fun i hi ht ha => hn ⟨i,hi,ht,ha⟩)
  exact (not_lt_of_ge hle) he

/-- Closing a nonempty set of active colors strictly decreases the height. -/
theorem relativeUpper_active_descending {P R : Deligne M} (h : P < R)
    (ha : ∀ i ∈ R.val.1, i ∉ P.val.1 → relativeColorActive M f U cutoff P i) :
    relativeHeight M f U cutoff R < relativeHeight M f U cutoff P := by
  apply (relativeHeight_lt_iff M f U cutoff R P).mpr
  refine ⟨relativeUpperLevel M f cutoff P R,
    fun d hd => relativeBlock_eq_above_upper M f U cutoff h.le hd, ?_⟩
  let H := relativeUpperLevel M f cutoff P R
  by_cases hv : pointedProfile M f R cutoff H = pointedProfile M f P cutoff H
  · have hr (i : S) (hi : i ∈ R.val.1) :
        (framedCartan M *ᵥ pointedProfile M f P cutoff H) (.inl i) = 0 := by
      rw [←hv]
      exact pointedCosetVector_harmonic M f R (cutoff+H) ⟨.inl i,⟨i,hi,rfl⟩⟩
    have hs (i : S) (hi : i ∈ R.val.1) (ht : i ∉ P.val.1) :
        relativeSign M U (pointedProfile M f P cutoff) H (.inl i) ≤ 0 := by
      rcases eq_or_lt_of_le (relativeIncidence_le_upperLevel M f cutoff P R i hi ht) with he | he
      · have hh := relative_active_sign M f U cutoff P i (ha i hi ht) (by rw [he]; exact hr i hi)
        rw [he] at hh
        rw [hh]
        norm_num
      · rw [(relative_no_incidence M f U cutoff (relative_above_incidence M f cutoff he)).2.2]
    have hsEq := relative_sign_upper_tie M f U cutoff h.le hv
    have hm := relative_mask_upper_nonpos M f U cutoff h.le H hsEq hs
    have hsome : ∃ i ∈ R.val.1, i ∉ P.val.1 ∧ ∃ k,
        levelIncident (framedCartan M) (pointedProfile M f P cutoff) k (.inl i) := by
      obtain ⟨i,hi,ht⟩ := Set.exists_of_ssubset (deligne_lt_type M h)
      exact ⟨i,hi,ht,relativeIncidence M f cutoff P i,relative_active_incident M f U cutoff P i (ha i hi ht)⟩
    have hne : relativeSignMask M f U cutoff R H ≠ relativeSignMask M f U cutoff P H := by
      intro heq
      obtain ⟨i,hi,ht,hin⟩ := relativeUpperLevel_incident M f cutoff P R hsome
      have hiP : (.inl i : S ⊕ Unit) ∉ Sum.inl '' P.val.1 := by
        rintro ⟨j,hj,he⟩
        exact ht (Sum.inl.inj he ▸ hj)
      have hiR : (.inl i : S ⊕ Unit) ∈ Sum.inl '' R.val.1 := ⟨i,hi,rfl⟩
      have he : relativeIncidence M f cutoff P i = H := le_antisymm
        (relativeIncidence_le_upperLevel M f cutoff P R i hi ht) (levelIncident_le _ _ hin)
      have hsign := relative_active_sign M f U cutoff P i (ha i hi ht) (by rw [he]; exact hr i hi)
      rw [he] at hsign
      have hz := congrFun heq (toLex (.inl i))
      simp only [relativeSignMask, ofLex_toLex, hiP, hiR, ↓reduceIte] at hz
      have hsi : relativeSign M U (pointedProfile M f R cutoff) H (.inl i) =
          relativeSign M U (pointedProfile M f P cutoff) H (.inl i) := hsEq _
      rw [hsi, hsign] at hz
      norm_num at hz
    exact relativeBlock_lt_of_mask M f U cutoff hv (lt_of_le_of_ne hm hne)
  · have hle := pointedCosetVector_upper_antitone_int M f h.le (cutoff+H)
      (relative_upper_active_rows M f U cutoff P R ha)
    exact Prod.Lex.lt_iff.mpr (Or.inl (harmonic_sum_lt_of_lt _ _ hle hv))

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeUpperConnected
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Connected descending upper neighborhoods, using their common active-color extension. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ) (Y : Set S) (x : Artin M)

lemma relative_le_upperClip {P R : RelativeVertex M Y x} (h : P ≤ R) :
    P ≤ relativeUpperClip M f U cutoff Y x P R := by
  change P.val ≤ (relativeUpperClip M f U cutoff Y x P R).val
  change P.val ≤ sourceCoset M _ (source_spherical_mono M Set.inter_subset_left R.val.property.1) _
  nth_rw 1 [←sourceCoset_eq M P.val _ (sourceCosetRepresentative_mem M P.val)]
  exact sourceCoset_le M (show P.val.val.1 ⊆ R.val.val.1 ∩
    (P.val.val.1 ∪ relativeActiveSet M f U cutoff Y P.val) from
      fun _ hi => ⟨h.1 hi, Or.inl hi⟩) _

lemma relative_upperClip_le {P R : RelativeVertex M Y x} (h : P ≤ R) :
    relativeUpperClip M f U cutoff Y x P R ≤ R := by
  change sourceCoset M _ (source_spherical_mono M Set.inter_subset_left R.val.property.1) _ ≤ R.val
  rw [←sourceCoset_eq M R.val _ (h.2 (sourceCosetRepresentative_mem M P.val))]
  exact sourceCoset_le M Set.inter_subset_left _

lemma relative_upperClip_le_top (P R : RelativeVertex M Y x)
    (hYU : ∀ i ∈ Y, (.inl i : S ⊕ Unit) ∈ U) :
    relativeUpperClip M f U cutoff Y x P R ≤ relativeUpperTop M f U cutoff Y x P hYU := by
  exact sourceCoset_le M (hT := source_spherical_mono M Set.inter_subset_left R.val.property.1)
    (hU := relativeActiveSet_spherical M f U cutoff Y P.val P.property.1 hYU) Set.inter_subset_right _

lemma relative_upperClip_descending {P R : RelativeVertex M Y x}
    (h : RelativeDescendingUpper M f U cutoff Y x P R) :
    RelativeDescendingUpper M f U cutoff Y x P (relativeUpperClip M f U cutoff Y x P R) := by
  obtain ⟨i,hi,ht,ha⟩ := relativeUpper_descending_has_active M f U cutoff h.1 h.2
  have hl : P < relativeUpperClip M f U cutoff Y x P R := by
    apply lt_of_le_of_ne (relative_le_upperClip M f U cutoff Y x h.1.le)
    intro he
    have hiC : i ∈ (relativeUpperClip M f U cutoff Y x P R).val.val.1 :=
      ⟨hi, Or.inr ⟨R.property.1 hi,ht,ha⟩⟩
    rw [←he] at hiC
    exact ht hiC
  refine ⟨hl, relativeUpper_active_descending M f U cutoff hl ?_⟩
  intro j hj hn
  exact (hj.2.resolve_left hn).2.2

lemma relative_upperTop_descending (P : RelativeVertex M Y x)
    (hYU : ∀ i ∈ Y, (.inl i : S ⊕ Unit) ∈ U)
    (ha : (relativeActiveSet M f U cutoff Y P.val).Nonempty) :
    RelativeDescendingUpper M f U cutoff Y x P (relativeUpperTop M f U cutoff Y x P hYU) := by
  have hp : P ≤ relativeUpperTop M f U cutoff Y x P hYU := by
    change P.val ≤ sourceCoset M _
      (relativeActiveSet_spherical M f U cutoff Y P.val P.property.1 hYU) _
    nth_rw 1 [←sourceCoset_eq M P.val _ (sourceCosetRepresentative_mem M P.val)]
    exact sourceCoset_le M Set.subset_union_left _
  have hl : P < relativeUpperTop M f U cutoff Y x P hYU := by
    apply lt_of_le_of_ne hp
    intro he
    obtain ⟨i,hi⟩ := ha
    have hm : i ∈ (relativeUpperTop M f U cutoff Y x P hYU).val.val.1 := Or.inr hi
    rw [←he] at hm
    exact hi.2.1 hm
  exact ⟨hl,relativeUpper_active_descending M f U cutoff hl (fun _ hi hn => (hi.resolve_left hn).2.2)⟩

private lemma within_symm {V : Type*} {adj : V → V → Prop} {p : V → Prop}
    (hs : ∀ a b, adj a b → adj b a) {a b : V} (h : PathWithin adj p a b) :
    PathWithin adj p b a := by
  induction h with
  | refl => exact .refl
  | @tail c d h he ih =>
    exact (Relation.ReflTransGen.single (r := fun u v => p u ∧ p v ∧ adj u v)
      ⟨he.2.1, he.1, hs c d he.2.2⟩).trans ih

/-- Descending upper neighbors are connected through descending upper neighbors. -/
theorem relative_descending_upper_connected (P : RelativeVertex M Y x)
    (hYU : ∀ i ∈ Y, (.inl i : S ⊕ Unit) ∈ U)
    (R Q : RelativeVertex M Y x)
    (hR : RelativeDescendingUpper M f U cutoff Y x P R)
    (hQ : RelativeDescendingUpper M f U cutoff Y x P Q) :
    PathWithin (relativeAdjacent M) (RelativeDescendingUpper M f U cutoff Y x P) R Q := by
  obtain ⟨i,hi,ht,ha⟩ := relativeUpper_descending_has_active M f U cutoff hR.1 hR.2
  have hTop := relative_upperTop_descending M f U cutoff Y x P hYU
    ⟨i,R.property.1 hi,ht,ha⟩
  have pathToTop (V : RelativeVertex M Y x) (hV : RelativeDescendingUpper M f U cutoff Y x P V) :
      PathWithin (relativeAdjacent M) (RelativeDescendingUpper M f U cutoff Y x P)
        V (relativeUpperTop M f U cutoff Y x P hYU) := by
    have hC := relative_upperClip_descending M f U cutoff Y x hV
    exact (Relation.ReflTransGen.single (r := fun a b =>
      RelativeDescendingUpper M f U cutoff Y x P a ∧
      RelativeDescendingUpper M f U cutoff Y x P b ∧ relativeAdjacent M a b)
      ⟨hV,hC,Or.inr (relative_upperClip_le M f U cutoff Y x hV.1.le)⟩).tail
      ⟨hC,hTop,Or.inl (relative_upperClip_le_top M f U cutoff Y x P V hYU)⟩
  exact (pathToTop R hR).trans (within_symm (fun _ _ h => h.elim Or.inr Or.inl) (pathToTop Q hQ))

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeDescending
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combining upper and lower descending neighborhoods. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

lemma relativePathWithin_mono {V:Type} {adj:V→V→Prop} {p q:V→Prop}
    (hpq:∀v,p v→q v) {a b:V} (h:PathWithin adj p a b) : PathWithin adj q a b := by
  induction h with
  | refl => exact .refl
  | tail _ he ih => exact ih.tail ⟨hpq _ he.1,hpq _ he.2.1,he.2.2⟩

lemma relativePathWithin_single {V:Type} {adj:V→V→Prop} {p:V→Prop}
    {a b:V} (ha:p a) (hb:p b) (h:adj a b) : PathWithin adj p a b :=
  Relation.ReflTransGen.single ⟨ha,hb,h⟩

omit [Fintype S] [LinearOrder S] in
lemma relative_vertex_avoids_frame {Y:Set S} {x:Artin M}
    (hf:f∉Y) (hx:x∈artinParabolic M {f}ᶜ) (P:RelativeVertex M Y x) :
    sourceCosetRepresentative M P.val∈artinParabolic M {f}ᶜ := by
  have hg:=P.property.2 (sourceCosetRepresentative_mem M P.val)
  have hY:Y⊆({f}ᶜ:Set S):=fun i hi he=>hf (he ▸ hi)
  have hm:=(artinParabolic M {f}ᶜ).mul_mem (artinParabolic_mono M hY hg) hx
  simpa only [_root_.mul_assoc,inv_mul_cancel,_root_.mul_one] using hm

theorem relative_descending_connected {Y:Set S} {x:Artin M} (P:RelativeVertex M Y x)
    (hYU:∀i∈Y,(.inl i:S⊕Unit)∈U)
    (hU:U⊆Set.range (Sum.inl:S→S⊕Unit)) (hf:(.inl f:S⊕Unit)∉U)
    (hxA:sourceCosetRepresentative M P.val∈artinParabolic M {f}ᶜ)
    (A B:RelativeVertex M Y x)
    (hA:relativeAdjacent M P A) (ha:relativeHeight M f U cutoff A.val < relativeHeight M f U cutoff P.val)
    (hB:relativeAdjacent M P B) (hb:relativeHeight M f U cutoff B.val < relativeHeight M f U cutoff P.val) :
    PathWithin (relativeAdjacent M) (fun V=>relativeHeight M f U cutoff V.val < relativeHeight M f U cutoff P.val) A B := by
  have hneA:P≠A:=by intro he;subst A;exact lt_irrefl _ ha
  have hneB:P≠B:=by intro he;subst B;exact lt_irrefl _ hb
  rcases hA with hA|hA <;> rcases hB with hB|hB
  · exact relativePathWithin_mono (fun _ h=>h.2)
      (relative_descending_upper_connected M f U cutoff Y x P hYU A B
        ⟨lt_of_le_of_ne hA hneA,ha⟩ ⟨lt_of_le_of_ne hB hneB,hb⟩)
  · exact relativePathWithin_single ha hb (Or.inr (hB.trans hA))
  · exact relativePathWithin_single ha hb (Or.inl (hA.trans hB))
  · exact relativePathWithin_mono (fun _ h=>h.2)
      (relative_descending_lower_connected_s236 M f U cutoff P hU hf hxA A B
        ⟨lt_of_le_of_ne hA (Ne.symm hneA),ha⟩ ⟨lt_of_le_of_ne hB (Ne.symm hneB),hb⟩)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeTieLower
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transferring an eligible opening across a tied inclusion. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

lemma relativeProfiles_eq_of_tie {P Q:Deligne M}
    (he:relativeHeight M f U cutoff P=relativeHeight M f U cutoff Q) :
    pointedProfile M f P cutoff=pointedProfile M f Q cutoff :=
  Finsupp.ext (relativeHeight_eq_profiles M f U cutoff he)

lemma relativePeak_eq_of_tie {P Q:Deligne M}
    (he:relativeHeight M f U cutoff P=relativeHeight M f U cutoff Q) (i:S) :
    relativePeak M f cutoff P i=relativePeak M f cutoff Q i := by
  unfold relativePeak relativePeakSupport
  rw [relativeProfiles_eq_of_tie M f U cutoff he]

lemma relativeEligible_visible {P R:Deligne M} (Y:Set S) (_hP:P.val.1⊆Y)
    {i:S} (hi:RelativeEligible M f U cutoff P R i) :
    i∈relativeVisible M f cutoff Y P := by
  refine ⟨hi.1,?_⟩
  intro hn
  exact hn.2 (relativePeak M f cutoff P i) (Or.inl (relativeEligible_positive M f U cutoff hi))

lemma relativeVisible_commutes (Y:Set S) (P:Deligne M) (hP:P.val.1⊆Y)
    (i:S) (hi:i∈relativeVisible M f cutoff Y P) (j:S)
    (hj:j∈relativeInvisible M f cutoff Y P) : M i j=2 := by
  by_contra hn
  have hij:i≠j:=by rintro rfl;exact hi.2 hj
  have hc:=framedCartan_neg_of_label_ne_two M i j hij hn
  rw [framedCartan_symm] at hc
  exact relativeVisible_nonadjacent M f cutoff Y P hP j i hj hi hc

lemma relativeEligible_single_open (P R:Deligne M) (i:S)
    (hi:RelativeEligible M f U cutoff P R i) (z:Artin M) (hz:z∈P.val.2)
    (he:∀k:ℕ,pointedMultiplicity M f z (cutoff+k) (.inl i)=pointedProfile M f R cutoff k (.inl i)) :
    ∃ Q:Deligne M,Q<P ∧ relativeHeight M f U cutoff Q < relativeHeight M f U cutoff P := by
  let T:=P.val.1\{i}
  let Q:=sourceCoset M T (source_spherical_mono M Set.sdiff_subset P.property.1) z
  have hle:Q≤P := by
    rw [←sourceCoset_eq M P z hz]
    exact sourceCoset_le M Set.sdiff_subset z
  have hin:i∉Q.val.1:=fun hh=>hh.2 rfl
  have hlt:Q<P:=lt_of_le_of_ne hle (by
    intro h
    apply hin
    rw [h]
    exact hi.1)
  have hv (k:ℕ) : pointedProfile M f Q cutoff k (.inl i)=pointedProfile M f R cutoff k (.inl i) := by
    change pointedCosetVector M f Q (cutoff+k) (.inl i)=_
    rw [pointedCosetVector_open M f Q i hin z (rightCoset_self M T z),he]
  have hnew:RelativeEligible M f U cutoff P Q i := by
    refine ⟨hi.1,hin,?_,?_⟩
    · intro d hd
      rw [hv]
      exact hi.2.2.1 d hd
    · simpa only [hv] using hi.2.2.2
  exact ⟨Q,hlt,relativeLower_eligible_descending M f U cutoff hlt (by
    intro j hj hn
    have hji:j=i:=by
      by_contra hji
      exact hn ⟨hj,hji⟩
    subst j
    exact hnew)⟩

/-- A descending lower neighbor at the larger end of a tie yields one at
its smaller end. The invisible group factor is omitted from the representative. -/
theorem relativeTie_lower_nonempty (Y:Set S) {P Q:Deligne M} (hPQ:P≤Q) (hQ:Q.val.1⊆Y)
    (htie:relativeHeight M f U cutoff P=relativeHeight M f U cutoff Q)
    (R:Deligne M) (hR:R<Q) (hdesc:relativeHeight M f U cutoff R < relativeHeight M f U cutoff Q) :
    ∃ V:Deligne M,V<P ∧ relativeHeight M f U cutoff V < relativeHeight M f U cutoff P := by
  obtain ⟨i,hi⟩:=relativeLower_descending_has_eligible M f U cutoff hR hdesc
  let B:=relativeVisible M f cutoff Y Q
  let C:=Q.val.1∩relativeInvisible M f cutoff Y Q
  have hBC:B∪C=Q.val.1:=by
    ext j
    simp only [B,C,relativeVisible,Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff]
    tauto
  have hc:∀s∈B,∀t∈C,M s t=2:=fun s hs t ht=>
    relativeVisible_commutes M f cutoff Y Q hQ s hs t ht.2
  have hiB:i∈B:=relativeEligible_visible M f U cutoff Y hQ hi
  have hiP:i∈P.val.1:=by
    have he:=relativeVisible_eq_of_tie M f U cutoff Y hPQ hQ htie
    have hm:i∈relativeVisible M f cutoff Y P:=he ▸ hiB
    exact hm.1
  let z:=sourceCosetRepresentative M P
  let w:=sourceCosetRepresentative M R
  have hz:z∈Q.val.2:=hPQ.2 (sourceCosetRepresentative_mem M P)
  have hw:w∈Q.val.2:=hR.le.2 (sourceCosetRepresentative_mem M R)
  have hg:w*z⁻¹∈artinParabolic M (B∪C):=by
    rw [hBC]
    rw [←sourceCoset_eq M Q z hz] at hw
    exact hw
  rw [←sourceParabolicProductMap_range M B C hc] at hg
  obtain ⟨⟨b,c⟩,hbc⟩:=hg
  have hmul:(b:Artin M)*c=w*z⁻¹:=hbc
  have hew:w=(c:Artin M)*((b:Artin M)*z):=by
    rw [←_root_.mul_assoc,←(sourceParabolics_commute M B C hc b c b.property c.property).eq,hmul]
    group
  have hbP:(b:Artin M)∈artinParabolic M P.val.1:=by
    apply artinParabolic_mono M _ b.property
    intro j hj
    have he:=relativeVisible_eq_of_tie M f U cutoff Y hPQ hQ htie
    exact (show j∈relativeVisible M f cutoff Y P from he ▸ hj).1
  have hbz:(b:Artin M)*z∈P.val.2:=by
    rw [←sourceCoset_eq M P z (sourceCosetRepresentative_mem M P)]
    change ((b:Artin M)*z)*z⁻¹∈artinParabolic M P.val.1
    simpa only [_root_.mul_assoc,mul_inv_cancel,_root_.mul_one] using hbP
  have hiC:(.inl i:S⊕Unit)∉Sum.inl '' C:=by
    rintro ⟨j,hj,hji⟩
    cases Sum.inl.inj hji
    exact hiB.2 hj.2
  have heprof:=relativeProfiles_eq_of_tie M f U cutoff htie
  have hielig:RelativeEligible M f U cutoff P R i:=by
    refine ⟨hiP,hi.2.1,?_,?_⟩
    · simpa only [relativePeak_eq_of_tie M f U cutoff htie] using hi.2.2.1
    · simpa only [relativePeak_eq_of_tie M f U cutoff htie,heprof] using hi.2.2.2
  apply relativeEligible_single_open M f U cutoff P R i hielig ((b:Artin M)*z) hbz
  intro k
  have hv:=pointedCosetVector_open M f R i hi.2.1 w (sourceCosetRepresentative_mem M R) (cutoff+k)
  change _=pointedCosetVector M f R (cutoff+k) (.inl i)
  rw [hv,hew,pointedMultiplicity_exterior_ordered M f C c c.property _ _ hiC]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeTiedDescent
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compatibility of descending neighborhoods across equal-height inclusions. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ) {Y:Set S} {x:Artin M}

lemma relativeTie_active_common {P Q:RelativeVertex M Y x} (hPQ:P≤Q)
    (he:relativeHeight M f U cutoff P.val=relativeHeight M f U cutoff Q.val)
    (hYU:∀i∈Y,(.inl i:S⊕Unit)∈U)
    (i:S) (hi:i∈Y) (hn:i∉P.val.val.1) (ha:relativeColorActive M f U cutoff P.val i) :
    ∃ V:RelativeVertex M Y x, relativeAdjacent M P V ∧ relativeAdjacent M Q V ∧
      relativeHeight M f U cutoff V.val < relativeHeight M f U cutoff P.val := by
  have hp:=relativeProfiles_eq_of_tie M f U cutoff he
  have hni:i∉Q.val.val.1:=by
    intro hiQ
    have hz:=tied_new_color_invisible M f U cutoff Y Q.property.1 he i hiQ hn
    have hinc:=relative_active_incident M f U cutoff P.val i ha
    unfold levelIncident at hinc
    rw [hp] at hinc
    exact hz.2 _ hinc
  have haQ:relativeColorActive M f U cutoff Q.val i:=by
    unfold relativeColorActive at *
    rwa [←hp]
  have htop:=relative_upperTop_descending M f U cutoff Y x Q hYU ⟨i,hi,hni,haQ⟩
  exact ⟨relativeUpperTop M f U cutoff Y x Q hYU,
    Or.inl (hPQ.trans htop.1.le),Or.inl htop.1.le,htop.2.trans_eq he.symm⟩

lemma relativeTie_common_from_larger {P Q:RelativeVertex M Y x} (hPQ:P≤Q)
    (he:relativeHeight M f U cutoff P.val=relativeHeight M f U cutoff Q.val)
    (hYU:∀i∈Y,(.inl i:S⊕Unit)∈U)
    (A:RelativeVertex M Y x) (hA:relativeAdjacent M Q A)
    (ha:relativeHeight M f U cutoff A.val < relativeHeight M f U cutoff Q.val) :
    ∃ V:RelativeVertex M Y x, relativeAdjacent M P V ∧ relativeAdjacent M Q V ∧
      relativeHeight M f U cutoff V.val < relativeHeight M f U cutoff P.val := by
  have hne:Q.val≠A.val:=by intro h;rw [h] at ha;exact lt_irrefl _ ha
  rcases hA with hQA|hAQ
  · obtain ⟨i,hi,hn,hact⟩:=relativeUpper_descending_has_active M f U cutoff
      (lt_of_le_of_ne hQA hne) ha
    have hp:=relativeProfiles_eq_of_tie M f U cutoff he
    have hactP:relativeColorActive M f U cutoff P.val i:=by
      unfold relativeColorActive at *
      rwa [hp]
    exact relativeTie_active_common M f U cutoff hPQ he hYU i (A.property.1 hi)
      (fun hiP=>hn (hPQ.1 hiP)) hactP
  · obtain ⟨V,hVP,hVh⟩:=relativeTie_lower_nonempty M f U cutoff Y hPQ Q.property.1 he A.val
      (lt_of_le_of_ne hAQ (Ne.symm hne)) ha
    let W:RelativeVertex M Y x:=⟨V,hVP.le.1.trans P.property.1,hVP.le.2.trans P.property.2⟩
    exact ⟨W,Or.inr hVP.le,Or.inr (hVP.le.trans hPQ),hVh⟩

lemma relativeTie_common_from_smaller {P Q:RelativeVertex M Y x} (hPQ:P≤Q)
    (he:relativeHeight M f U cutoff P.val=relativeHeight M f U cutoff Q.val)
    (hYU:∀i∈Y,(.inl i:S⊕Unit)∈U)
    (A:RelativeVertex M Y x) (hA:relativeAdjacent M P A)
    (ha:relativeHeight M f U cutoff A.val < relativeHeight M f U cutoff P.val) :
    ∃ V:RelativeVertex M Y x, relativeAdjacent M P V ∧ relativeAdjacent M Q V ∧
      relativeHeight M f U cutoff V.val < relativeHeight M f U cutoff P.val := by
  have hne:P.val≠A.val:=by intro h;rw [h] at ha;exact lt_irrefl _ ha
  rcases hA with hPA|hAP
  · obtain ⟨i,hi,hn,hact⟩:=relativeUpper_descending_has_active M f U cutoff
      (lt_of_le_of_ne hPA hne) ha
    exact relativeTie_active_common M f U cutoff hPQ he hYU i (A.property.1 hi) hn hact
  · exact ⟨A,Or.inr hAP,Or.inr (hAP.trans hPQ),ha⟩

/-- The local hypotheses used by path lowering are verified for the actual
relative coset poset and the actual pointed-family height. -/
theorem relative_localDescent
    (hYU:∀i∈Y,(.inl i:S⊕Unit)∈U)
    (hU:U⊆Set.range (Sum.inl:S→S⊕Unit)) (hf:(.inl f:S⊕Unit)∉U)
    (hx:x∈artinParabolic M {f}ᶜ) :
    LocalDescent (relativeAdjacent M (Y:=Y) (x:=x))
      (fun P=>relativeHeight M f U cutoff P.val) where
  symmetric := fun h=>h.elim Or.inr Or.inl
  descending := fun P A B hA ha hB hb=>
    relative_descending_connected M f U cutoff P hYU hU hf
      (relative_vertex_avoids_frame M f (fun hi=>hf (hYU f hi)) hx P) A B hA ha hB hb
  tied := by
    intro P Q hPQ he A hA ha
    rcases hPQ with hPQ|hQP
    · obtain ⟨V,hPV,hQV,hV⟩:=relativeTie_common_from_smaller M f U cutoff hPQ he hYU A hA ha
      exact ⟨V,hQV,hV.trans_eq he,
        relative_descending_connected M f U cutoff P hYU hU hf
          (relative_vertex_avoids_frame M f (fun hi=>hf (hYU f hi)) hx P) A V hA ha hPV hV⟩
    · obtain ⟨V,hQV,hPV,hV⟩:=relativeTie_common_from_larger M f U cutoff hQP he.symm hYU A hA ha
      have hVP:relativeHeight M f U cutoff V.val < relativeHeight M f U cutoff P.val:=hV.trans_eq he.symm
      exact ⟨V,hQV,hV,
        relative_descending_connected M f U cutoff P hYU hU hf
          (relative_vertex_avoids_frame M f (fun hi=>hf (hYU f hi)) hx P) A V hA ha hPV hVP⟩

theorem relative_minimum_path
    (hYU:∀i∈Y,(.inl i:S⊕Unit)∈U)
    (hU:U⊆Set.range (Sum.inl:S→S⊕Unit)) (hf:(.inl f:S⊕Unit)∉U)
    (hx:x∈artinParabolic M {f}ᶜ)
    (P Q:RelativeVertex M Y x)
    (hP:∀V:RelativeVertex M Y x,relativeHeight M f U cutoff P.val ≤ relativeHeight M f U cutoff V.val)
    (hQ:∀V:RelativeVertex M Y x,relativeHeight M f U cutoff Q.val ≤ relativeHeight M f U cutoff V.val) :
    PathWithin (relativeAdjacent M)
      (fun P=>∀V:RelativeVertex M Y x,relativeHeight M f U cutoff P.val ≤ relativeHeight M f U cutoff V.val) P Q :=
  minimum_path _ _ (relative_localDescent M f U cutoff hYU hU hf hx) wellFounded_lt hP hQ
    (relative_poset_connected M Y x P Q)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeMinimumContainment
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Confinement of the actual categorical stabilizer from a harmonic minimum. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ) {Y:Set S} {x:Artin M}

lemma relative_type_subset_containing (Y:Set S) (P:Deligne M) :
    P.val.1⊆relativeContainingType M f cutoff Y P := by
  intro i hi
  by_cases hn:i∈relativeInvisible M f cutoff Y P
  · exact Or.inr hn
  · exact Or.inl ⟨hi,hn⟩

lemma relative_containing_subset (P:RelativeVertex M Y x) :
    relativeContainingType M f cutoff Y P.val⊆Y :=
  fun _ hi=>hi.elim (fun h=>P.property.1 h.1) (fun h=>h.1)

theorem relative_minimum_exists : ∃ P:RelativeVertex M Y x,RelativeMinimum M f U cutoff P := by
  let P₀:=relativeElement M Y x x (rightCoset_self M Y x)
  obtain ⟨h,⟨P,rfl⟩,hmin⟩:=wellFounded_lt.has_min
    (Set.range (fun V:RelativeVertex M Y x=>relativeHeight M f U cutoff V.val))
    ⟨relativeHeight M f U cutoff P₀.val,P₀,rfl⟩
  exact ⟨P,fun V=>le_of_not_gt (hmin _ ⟨V,rfl⟩)⟩

lemma relative_minimum_path_confined {P Q:RelativeVertex M Y x}
    (path:PathWithin (relativeAdjacent M) (RelativeMinimum M f U cutoff) P Q) :
    relativeVisible M f cutoff Y Q.val=relativeVisible M f cutoff Y P.val ∧
    relativeInvisible M f cutoff Y Q.val=relativeInvisible M f cutoff Y P.val ∧
    Relation.ReflTransGen (fun A B:Deligne M=>
      A.val.1⊆relativeContainingType M f cutoff Y P.val ∧
      B.val.1⊆relativeContainingType M f cutoff Y P.val ∧ (A≤B ∨ B≤A)) P.val Q.val := by
  induction path with
  | refl => exact ⟨rfl,rfl,.refl⟩
  | @tail A B path he ih =>
    have ht:relativeHeight M f U cutoff A.val=relativeHeight M f U cutoff B.val:=
      le_antisymm (he.1 B) (he.2.1 A)
    have hI:=relativeInvisible_eq_of_height_eq M f U cutoff Y ht
    have hV:relativeVisible M f cutoff Y A.val=relativeVisible M f cutoff Y B.val:=by
      rcases he.2.2 with hAB|hBA
      · exact relativeVisible_eq_of_tie M f U cutoff Y hAB B.property.1 ht
      · exact (relativeVisible_eq_of_tie M f U cutoff Y hBA A.property.1 ht.symm).symm
    have hBV:=hV.symm.trans ih.1
    have hBI:=hI.symm.trans ih.2.1
    have hA:A.val.val.1⊆relativeContainingType M f cutoff Y P.val:=by
      have h:=relative_type_subset_containing M f cutoff Y A.val
      simpa only [relativeContainingType,ih.1,ih.2.1] using h
    have hB:B.val.val.1⊆relativeContainingType M f cutoff Y P.val:=by
      have h:=relative_type_subset_containing M f cutoff Y B.val
      simpa only [relativeContainingType,hBV,hBI] using h
    exact ⟨hBV,hBI,ih.2.2.tail ⟨hA,hB,he.2.2⟩⟩

/-- Proposition 6.9: the stabilizer lies in the conjugate standard subgroup
specified by the visible and invisible colors at a minimum. -/
theorem relative_minimum_stabilizer_containment
    (hYU:∀i∈Y,(.inl i:S⊕Unit)∈U)
    (hU:U⊆Set.range (Sum.inl:S→S⊕Unit)) (hf:(.inl f:S⊕Unit)∉U)
    (hx:x∈artinParabolic M {f}ᶜ) (P:RelativeVertex M Y x)
    (hP:RelativeMinimum M f U cutoff P)
    (a:Artin M) (ha:a∈artinParabolic M Y)
    (hfix:pointedFamily M f (a*x)=pointedFamily M f x) :
    a∈conjugate (sourceCosetRepresentative M P.val*x⁻¹)⁻¹
      (artinParabolic M (relativeContainingType M f cutoff Y P.val)) := by
  let R:=relativeTranslate M Y x a ha P
  have he:relativeHeight M f U cutoff R.val=relativeHeight M f U cutoff P.val:=
    relativeHeight_translate_fixed M f U cutoff x a hfix P.val
  have hR:RelativeMinimum M f U cutoff R:=fun V=>he.trans_le (hP V)
  have hp:=relative_minimum_path M f U cutoff hYU hU hf hx P R hP hR
  have hconf:=(relative_minimum_path_confined M f U cutoff hp).2.2
  let z:=sourceCosetRepresentative M P.val
  let r:=x⁻¹*a*x
  have hz:z*r∈R.val.val.2:=by
    change z*r∈(deligneRightTranslate M P.val r).val.2
    apply (mem_deligneRightTranslate M P.val r (z*r)).mpr
    simpa only [_root_.mul_assoc,mul_inv_cancel,_root_.mul_one] using sourceCosetRepresentative_mem M P.val
  have hm:=conjugate_membership_of_coset_path M (relativeContainingType M f cutoff Y P.val)
    z r (sourceCosetRepresentative_mem M P.val)
    (relative_type_subset_containing M f cutoff Y P.val) hz hconf
  rw [mem_conjugate,inv_inv] at hm ⊢
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [z,r]
  group

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedInitialStabilizer
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial pointed-family stabilizer inside a frame-avoiding standard subgroup. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma initial_containing_subset (Y:Set S) (hf:f∉Y) :
    relativeContainingType M f 0 Y (sourceCoset M ∅ (spherical_empty M) 1) ⊆
      {i | i∈Y ∧ M i f=2} := by
  intro i hi
  rcases hi with hi|hi
  · exact (Set.notMem_empty i hi.1).elim
  · refine ⟨hi.1,?_⟩
    by_contra hm
    have hif:i≠f:=by rintro rfl;exact hf hi.1
    have hneg:=framedCartan_neg_of_label_ne_two M i f hif hm
    apply hi.2 0
    right
    refine ⟨.inl f,hneg,?_⟩
    rw [initial_profile]
    norm_num

/-- The only frame-avoiding words fixing the initial family are generated
by the colors that commute with the frame. -/
theorem pointed_initial_stabilizer_le (Y:Set S) (hf:f∉Y)
    (a:Artin M) (ha:a∈artinParabolic M Y)
    (hfix:pointedFamily M f a=pointedFamily M f 1) :
    a∈artinParabolic M {i | i∈Y ∧ M i f=2} := by
  let U:Set (S⊕Unit):=Sum.inl '' Y
  let P:RelativeVertex M Y 1:=relativeElement M Y 1 1 (rightCoset_self M Y 1)
  have hmin:RelativeMinimum M f U 0 P:=initial_height_minimum M f U 0 Y hf
  have hU:U⊆Set.range (Sum.inl:S→S⊕Unit):=by
    rintro _ ⟨i,_,rfl⟩
    exact ⟨i,rfl⟩
  have hfU:(.inl f:S⊕Unit)∉U:=by
    rintro ⟨i,hi,he⟩
    exact hf (Sum.inl.inj he ▸ hi)
  have hm:=relative_minimum_stabilizer_containment M f U 0
    (fun i hi=>⟨i,hi,rfl⟩) hU hfU (artinParabolic M {f}ᶜ).one_mem P hmin a ha
    (by simpa only [_root_.mul_one] using hfix)
  have hz:sourceCosetRepresentative M P.val=1:=by
    have h:=sourceCosetRepresentative_mem M P.val
    change sourceCosetRepresentative M P.val∈rightCoset M ∅ 1 at h
    rw [rightCoset_empty] at h
    exact h
  rw [hz,inv_one,_root_.mul_one,inv_one,conjugate_one] at hm
  exact artinParabolic_mono M (initial_containing_subset M f Y hf) hm

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeDiagram
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The relative diagram in §2.1 of paper 082-03

Adjoin the color `f`, with label 2 to the chosen standard type `X` and
label 3 to its complement. The existing fusion construction subsequently
adjoins the universal auxiliary color `o`. The map on Artin presentations
is constructed directly; no parabolic embedding theorem is assumed here.
-/

namespace HarmonicArtin.ParabolicIntersections

attribute [local instance] Classical.propDecidable

variable {S : Type*} (M : CoxeterMatrix S) (X : Set S)

/-- Standard parabolics map onto the corresponding standard parabolics
of the extended diagram. Injectivity is not needed for this identity. -/
theorem relativeArtinHom_parabolic (Y : Set S) :
    (artinParabolic M Y).map (relativeArtinHom M X) =
      artinParabolic (relativeMatrix M X) (Sum.inl '' Y) := by
  simp only [artinParabolic, MonoidHom.map_closure, Set.image_image,
    relativeArtinHom_generator]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveLift_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The relative categorical family of paper 082-03

The family consists of actual bounded-projective homotopy classes in the
extended diagram. Its initial color is the new relative color `f`; the
auxiliary universal color is the one already adjoined by the fusion model.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (X : Set S)
local notation "N" => relativeMatrix M X

attribute [local instance] OAI.HarmonicArtin.ParabolicIntersections.instLinearOrderSumUnit_solutions
/-- Verified containment of the standard subgroup in the actual initial stabilizer. -/
theorem standard_fixes_relativeInitial (g : Artin M) (hg : g ∈ artinParabolic M X)
    (L : RelativeLabel M X) :
    relativeAction M X g (relativeInitial M X L) = relativeInitial M X L := by
  apply pointed_standard_fixes_initial N (Sum.inl '' X) (.inr ())
  · rintro _ ⟨s, hs, rfl⟩
    simp [hs]
  · rw [← relativeArtinHom_parabolic]
    exact ⟨g, hg, rfl⟩

theorem standard_le_relative_stabilizer :
    artinParabolic M X ≤ MulAction.stabilizer (Artin M) (relativeInitial M X) := by
  intro g hg
  apply funext
  exact standard_fixes_relativeInitial M X g hg

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeInitialStabilizer
attribute [-simp] _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The initial stabilizer in the relative diagram

The sole input below is the unrestricted standard-parabolic embedding theorem:
van der Lek, *The Homotopy Type of Complex Hyperplane Complements* (1983),
Chapter II, §4, Theorem 4.13(i). See also Charney–Paris, *Convexity of parabolic
subgroups in Artin groups* (2014), §1, p. 2, https://arxiv.org/abs/1401.7634.
The exact case needed is injectivity of the canonical inclusion from the
original Artin presentation into the presentation with one additional color.
The categorical stabilizer identity is proved below, not assumed.
-/
namespace HarmonicArtin.ParabolicIntersections
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (X:Set S)
local notation "N" => relativeMatrix M X
attribute [local instance] Classical.decEq Classical.propDecidable

omit [Fintype S] [LinearOrder S] in
lemma relativeFrame_commuting_type :
    {i:S⊕Unit | i∈Set.range (Sum.inl:S→S⊕Unit) ∧ N i (.inr ())=2} = Sum.inl '' X := by
  ext i
  cases i with
  | inl s =>
    by_cases hs:s∈X <;> simp [relativeMatrix_frame,hs]
  | inr u => simp

attribute [local instance] OAI.HarmonicArtin.ParabolicIntersections.instLinearOrderSumUnit_solutions_1
/-- Proposition 8.3, conditional only on the published embedding input. -/
theorem relative_initial_stabilizer (hEmb:VanDerLekRelativeEmbedding M X) :
    MulAction.stabilizer (Artin M) (relativeInitial M X) = artinParabolic M X := by
  apply le_antisymm
  · intro a ha
    have hfix:pointedFamily N (.inr ()) (relativeArtinHom M X a)=pointedFamily N (.inr ()) 1 := by
      change a • relativeInitial M X=relativeInitial M X at ha
      funext L
      have h:=congrFun ha L
      change pointedAction N (relativeArtinHom M X a) (pointedInitial N (.inr ()) L)=_ at h
      simpa only [pointedFamily,map_one,Equiv.Perm.one_apply,relativeInitial] using h
    have hmap:relativeArtinHom M X a∈artinParabolic N (Set.range (Sum.inl:S→S⊕Unit)):=by
      have he:=relativeArtinHom_parabolic M X Set.univ
      simp only [Set.image_univ] at he
      rw [←he]
      exact ⟨a,by rw [standard_univ];trivial,rfl⟩
    have hm:=pointed_initial_stabilizer_le N (.inr ()) (Set.range (Sum.inl:S→S⊕Unit))
      (by simp) (relativeArtinHom M X a) hmap hfix
    rw [relativeFrame_commuting_type M X,←relativeArtinHom_parabolic M X X] at hm
    obtain ⟨b,hb,he⟩:=hm
    exact hEmb.injective he ▸ hb
  · exact standard_le_relative_stabilizer M X

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_FixedFactor
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing an invisible factor

The nonspherical branch of §8 of paper 082-03 splits off a standard
factor fixing the entire family. This module proves that step for the
actual subgroup lattice and group action. Pairwise label 2 is the precise
commutation hypothesis; no product decomposition is assumed.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {G V : Type*} [Group G] [MulAction G V]

/-- A subgroup centralized pointwise by an element is invariant under its
conjugation. -/
theorem conjugate_eq_of_commute (P : Subgroup G) (g : G)
    (hc : ∀ a ∈ P, Commute a g) : conjugate g P = P := by
  apply le_antisymm
  · intro a ha
    rw [mem_conjugate] at ha
    have hh := (hc (g⁻¹ * a * g) ha).eq
    have he : g⁻¹ * a * g = a := by
      calc
        g⁻¹ * a * g = (g⁻¹ * a * g) * g * g⁻¹ := by group
        _ = g * (g⁻¹ * a * g) * g⁻¹ := by rw [hh]
        _ = a := by group
    rwa [he] at ha
  · intro a ha
    rw [mem_conjugate]
    have he : g⁻¹ * a * g = a := by
      calc
        g⁻¹ * a * g = g⁻¹ * (a * g) := by group
        _ = g⁻¹ * (g * a) := by rw [(hc a ha).eq]
        _ = a := by group
    rwa [he]

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
  {W : Type*} [MulAction (Artin M) W] (v : W)

omit [Fintype S] [LinearOrder S] in
/-- A fixed commuting standard factor splits off from the simultaneous
stabilizer. Surjectivity of the multiplication map suffices. -/
theorem relativeStabilizer_fixed_factor (K T : Set S) (x : Artin M)
    (hc : ∀ k ∈ K, ∀ t ∈ T, M k t = 2)
    (hfix : ∀ k ∈ artinParabolic M K, k • (x • v) = x • v) :
    relativeStabilizer M v (K ∪ T) x =
      artinParabolic M K ⊔ relativeStabilizer M v T x := by
  apply le_antisymm
  · intro a ha
    have hr : a ∈ (sourceParabolicProductMap M K T hc).range := by
      rw [sourceParabolicProductMap_range]
      exact ha.1
    obtain ⟨⟨k, t⟩, he⟩ := hr
    change (k : Artin M) * t = a at he
    have ht : (t : Artin M) • (x • v) = x • v := by
      apply (smul_left_cancel_iff (k : Artin M)).mp
      rw [hfix k k.property, ← mul_smul, he]
      exact ha.2
    rw [← he]
    exact Subgroup.mul_mem _
      ((show artinParabolic M K ≤ _ from le_sup_left) k.property)
      ((show relativeStabilizer M v T x ≤ _ from le_sup_right) ⟨t.property, ht⟩)
  · apply sup_le
    · intro k hk
      exact ⟨standard_mono M Set.subset_union_left hk, hfix k hk⟩
    · exact inf_le_inf (standard_mono M Set.subset_union_right) le_rfl

omit [Fintype S] [LinearOrder S] in
/-- The fixed factor is normalized by the complementary standard factor,
as required by the rank induction. -/
theorem standard_factor_normalized (K T : Set S)
    (hc : ∀ k ∈ K, ∀ t ∈ T, M k t = 2)
    (t : Artin M) (ht : t ∈ artinParabolic M T) :
    conjugate t (artinParabolic M K) = artinParabolic M K :=
  conjugate_eq_of_commute _ t (fun k hk => sourceParabolics_commute M K T hc k t hk ht)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedBoundaryZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The all-level connected-support argument in the nonspherical case of §8. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable

section Fusion
variable {E V : Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E) (hd : ∀ s t, d s t = d t s)
  (hdiag : ∀ s, d s s = .units 0) (hm : ∀ e, 2 ≤ m e)

/-- An unoperated exterior frame and an empty boundary exclude every
interior generator, including generators below the harmonic cutoff. -/
theorem orbit_boundary_zero_interior_zero (w : List (V × Bool)) (s : V)
    (hw : ∀ a ∈ w, a.1 ≠ s) (U : Set V) (hs : s ∉ U)
    (hz : ∀ k v, v ∉ U → (∃ u ∈ U, fusionFoldedCartan m d v u < 0) →
      fusionOrbitMultiplicity m d hd hdiag hm w s k v = 0) :
    ∀ k v, v ∈ U → fusionOrbitMultiplicity m d hd hdiag hm w s k v = 0 := by
  intro k v hv
  apply le_antisymm _ (fusionOrbitMultiplicity_nonneg m d hd hdiag hm w s k v)
  by_contra hn
  have hp : 0 < fusionOrbitMultiplicity m d hd hdiag hm w s k v := lt_of_not_ge hn
  obtain ⟨L, i, hi, _⟩ := orbit_generator_of_positive m d hd hdiag hm w s v k hp
  obtain ⟨j, hj, _⟩ := orbit_frame_generator m d hd hdiag w s hw L
  obtain ⟨b, hb⟩ := fusionOrbit_support_meets_boundary m d hd hdiag w s L
    (fusionColorRegion m U) i j (by change _ ∈ U; rwa [hi])
    (by change _ ∉ U; rw [congrArg Prod.fst hj]; exact hs)
  let q := ((fusionOrbitModel m d hd hdiag w s L).complex.placement b).level
  have he := fusionOrbit_boundary_absent m d hd hdiag hm w s q U (hz q) L ⟨b, rfl⟩
  exact he hb
end Fusion

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "diag" => coxeterFusionEdge_diag M
local notation "Q" => fusionQuiver m d hd

/-- Connectedness of the actual pointed family converts an all-level
exterior boundary vanishing statement to interior vanishing. -/
theorem pointed_boundary_zero_interior_zero (x : Artin M)
    (hx : x ∈ artinParabolic M {f}ᶜ) (K : Set S) (hf : f ∉ K)
    (hz : ∀ k v, v ∉ Sum.inl '' K →
      (∃ u ∈ Sum.inl '' K, framedCartan M v u < 0) →
      pointedMultiplicity M f x k v = 0) :
    ∀ k i, i ∈ K → pointedMultiplicity M f x k (.inl i) = 0 := by
  obtain ⟨w, hw, rfl⟩ := artinParabolic_signed_word M {f}ᶜ x hx
  have hC : fusionFoldedCartan m d = framedCartan M := by
    convert fusionFoldedCartan_eq_framedCartan M using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    exact Subsingleton.elim _ _
  have hh := orbit_boundary_zero_interior_zero m d hd diag (fusionLabelSize_ge_two M)
    (sourcePacketWord w) (.inl f)
    (by
      intro a ha he
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact hw b hb (Sum.inl.inj he)) (Sum.inl '' K)
    (by rintro ⟨i, hi, he⟩; exact hf (Sum.inl.inj he ▸ hi))
    (by simpa only [hC, pointedMultiplicity_word] using hz)
  intro k i hi
  simpa only [pointedMultiplicity_word] using hh k (.inl i) ⟨i, hi, rfl⟩

/-- Termwise absence in a closed neighborhood makes its negative twists
identity maps on each member of the pointed family. -/
theorem pointed_negativeTwist_of_zero (x : Artin M) (K : Set S)
    (hz : ∀ k v, v ∈ Sum.inl '' K ∨
      (∃ u ∈ Sum.inl '' K, framedCartan M v u < 0) →
      pointedMultiplicity M f x k v = 0)
    (i : S) (hi : i ∈ K) (L H : FusionLabel m) :
    classNegativeTwist Q (.inl i, L) (pointedFamily M f x H) = pointedFamily M f x H := by
  let E := minimalClassModel Q (pointedFamily M f x H)
  have hC : fusionFoldedCartan m d = framedCartan M := by
    convert fusionFoldedCartan_eq_framedCartan M using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    exact Subsingleton.elim _ _
  have hE : ∀ a : E.Index, (E.complex.placement a).color ∉
      closedNeighborhood Q (fusionColorRegion m (Sum.inl '' K)) := by
    intro a ha
    let v := (E.complex.placement a).color.1
    let k := (E.complex.placement a).level
    have hv : pointedMultiplicity M f x k v = 0 := by
      rcases ha with ha | ⟨β, hβ, r, hr, he⟩
      · obtain ⟨j, hj, he⟩ := ha
        have hv : v = .inl j := he.symm
        rw [hv]
        exact hz k (.inl j) (Or.inl ⟨j, hj, rfl⟩)
      · obtain ⟨j, hj, hej⟩ := hβ
        have hc := fusion_arrow_color_cartan_neg m d (fusionLabelSize_ge_two M) r
        have ht : r.1.2.1 = v := congrArg Prod.fst he
        have hs : r.1.1.1 = .inl j := (congrArg Prod.fst hr).trans hej.symm
        by_cases hne : r.1.1.1 = r.1.2.1
        · have hv : v = .inl j := ht ▸ hne ▸ hs
          rw [hv]
          exact hz k (.inl j) (Or.inl ⟨j, hj, rfl⟩)
        · have hneg := hc hne
          rw [hs, ht, hC, framedCartan_symm] at hneg
          exact hz k v (Or.inr ⟨.inl j, ⟨j, hj, rfl⟩, hneg⟩)
    have hn := (pointedMultiplicity_zero_iff M f x k v).mp hv H
      (E.complex.placement a).color.2
    rw [classLevelArray_minimal_apply] at hn
    have hp : 0 < Nat.card {b : E.Index // (E.complex.placement b).color =
        (E.complex.placement a).color ∧ (E.complex.placement b).level = k} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff]
      exact ⟨⟨a, rfl, rfl⟩⟩
    exact (ne_of_gt hp) hn
  have h := classNegativeTwist_far Q E.complex (fusionColorRegion m (Sum.inl '' K))
    hE (.inl i, L) ⟨i, hi, rfl⟩
  have hm : classOfComplex Q E.complex = pointedFamily M f x H :=
    minimalClassModel_class Q _
  rw [hm] at h
  exact h

/-- Vanishing on a full closed neighborhood makes the standard subgroup
fix the actual family, with no restriction on the levels. -/
theorem pointed_standard_fixes_of_closed_zero (x : Artin M) (K : Set S)
    (hz : ∀ k v, v ∈ Sum.inl '' K ∨
      (∃ u ∈ Sum.inl '' K, framedCartan M v u < 0) →
      pointedMultiplicity M f x k v = 0)
    (g : Artin M) (hg : g ∈ artinParabolic M K) :
    pointedFamily M f (g * x) = pointedFamily M f x := by
  have hpos (i : S) (hi : i ∈ K) (L H : FusionLabel m) :
      classPositiveTwist Q (.inl i, L) (pointedFamily M f x H) =
        pointedFamily M f x H := by
    let e := classTwistPerm Q (K := ℂ) (fusionQuiver_no_loops m d hd diag) (.inl i, L)
    have hn := pointed_negativeTwist_of_zero M f x K hz i hi L H
    calc
      _ = e (e.symm (pointedFamily M f x H)) := congrArg e hn.symm
      _ = _ := e.apply_symm_apply _
  have hgen (i : S) (hi : i ∈ K) (H : FusionLabel m) :
      pointedAction M (generator M i) (pointedFamily M f x H) =
        pointedFamily M f x H := by
    rw [pointedAction_generator, fusionPacketPerm, ← classPacketPerm_toList]
    have hlist (l : List (FusionLabel m)) :
        (l.map (fun L => classTwistPerm Q (fusionQuiver_no_loops m d hd diag)
          (.inl i, L))).prod (pointedFamily M f x H) = pointedFamily M f x H := by
      induction l with
      | nil => rfl
      | cons L l ih =>
        change classPositiveTwist Q (.inl i, L)
          ((l.map (fun J => classTwistPerm Q (fusionQuiver_no_loops m d hd diag)
            (.inl i, J))).prod (pointedFamily M f x H)) = _
        rw [ih]
        exact hpos i hi L H
    exact hlist _
  have hall (H : FusionLabel m) :
      pointedAction M g (pointedFamily M f x H) = pointedFamily M f x H := by
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨i, hi, rfl⟩ := hg
      exact hgen i hi H
    | one => simp only [map_one, Equiv.Perm.one_apply]
    | mul g h hg hh ihg ihh =>
      simp only [map_mul, Equiv.Perm.mul_apply, ihh, ihg]
    | inv g hg ih =>
      rw [map_inv]
      apply (pointedAction M g).injective
      change (pointedAction M g) ((pointedAction M g).symm _) = _
      rw [Equiv.apply_symm_apply, ih]
  funext H
  change pointedAction M (g * x) (pointedInitial M f H) = _
  rw [map_mul, Equiv.Perm.mul_apply]
  exact hall H

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeInvisibleFactor
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the all-level invisible factor in the nonspherical case of §8. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)

lemma exteriorCutoff_exists (Y : Set S) (x : Artin M) :
    ∃ cutoff : ℤ, cutoff ≤ 0 ∧ ExteriorCutoff M f Y x cutoff := by
  obtain ⟨b, hb⟩ := (pointedMultiplicity_support_finite M f x).bddBelow
  refine ⟨min b 0, min_le_right _ _, ?_⟩
  intro k hk v _
  have hz : pointedMultiplicity M f x k = 0 := by
    by_contra hn
    have := hb hn
    have := min_le_left b (0 : ℤ)
    omega
  exact congrFun hz v

lemma relative_profile_exterior {Y : Set S} {x : Artin M}
    (P : RelativeVertex M Y x) (cutoff : ℤ) (k : ℕ) (v : S ⊕ Unit)
    (hv : v ∉ Sum.inl '' Y) :
    pointedProfile M f P.val cutoff k v = pointedMultiplicity M f x (cutoff + k) v := by
  let z := sourceCosetRepresentative M P.val
  have hz : z ∈ rightCoset M Y x := P.property.2 (sourceCosetRepresentative_mem M P.val)
  have hvP : v ∉ Sum.inl '' P.val.val.1 := fun h => hv (Set.image_mono P.property.1 h)
  change pointedCosetVector M f P.val (cutoff+k) v = _
  rw [pointedCosetVector_eq M f P.val z (sourceCosetRepresentative_mem M P.val),
    pointedHarmonicAt_outside M f _ _ _ _ hvP]
  have he := pointedMultiplicity_exterior M Y (z*x⁻¹) hz f x v hv (cutoff+k)
  simpa only [_root_.mul_assoc, inv_mul_cancel, _root_.mul_one] using he

/-- If the containing type is the whole acting type, every exterior
neighbor of the invisible set is absent at every level. -/
lemma relative_invisible_boundary_zero {Y : Set S} {x : Artin M}
    (P : RelativeVertex M Y x) (cutoff : ℤ) (hcut : ExteriorCutoff M f Y x cutoff)
    (hfull : relativeContainingType M f cutoff Y P.val = Y) :
    ∀ k v, v ∉ Sum.inl '' relativeInvisible M f cutoff Y P.val →
      (∃ u ∈ Sum.inl '' relativeInvisible M f cutoff Y P.val, framedCartan M v u < 0) →
      pointedMultiplicity M f x k v = 0 := by
  intro k v hv hn
  obtain ⟨u, hu, hvi⟩ := hn
  obtain ⟨i, hi, hei⟩ := hu
  rw [← hei] at hvi
  have hvY : v ∉ Sum.inl '' Y := by
    rintro ⟨j, hj, rfl⟩
    have hjD : j ∈ relativeContainingType M f cutoff Y P.val := hfull.symm ▸ hj
    rcases hjD with hjV | hjK
    · rw [framedCartan_symm] at hvi
      exact relativeVisible_nonadjacent M f cutoff Y P.val P.property.1 i j hi hjV hvi
    · exact hv ⟨j, hjK, rfl⟩
  by_cases hk : k < cutoff
  · exact hcut k hk v hvY
  · let n := (k-cutoff).toNat
    have he : cutoff + (n : ℤ) = k := by
      dsimp only [n]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    have hz : pointedProfile M f P.val cutoff n v = 0 := by
      apply le_antisymm _ (pointedCosetVector_nonneg M f P.val (cutoff+n) v)
      by_contra hn
      have hp : 0 < pointedProfile M f P.val cutoff n v := lt_of_not_ge hn
      apply hi.2 n
      exact Or.inr ⟨v, by rwa [framedCartan_symm], hp⟩
    rwa [relative_profile_exterior M f P cutoff n v hvY, he] at hz

/-- The entire invisible factor fixes the family, even below the cutoff.
This is the additional step after Proposition 6.9 in the proof of Theorem 8.2. -/
theorem relative_invisible_factor_fixes {Y : Set S} {x : Artin M}
    (hf : f ∉ Y) (hx : x ∈ artinParabolic M {f}ᶜ)
    (P : RelativeVertex M Y x) (cutoff : ℤ) (hcut : ExteriorCutoff M f Y x cutoff)
    (hfull : relativeContainingType M f cutoff Y P.val = Y)
    (g : Artin M) (hg : g ∈ artinParabolic M (relativeInvisible M f cutoff Y P.val)) :
    pointedFamily M f (g*x) = pointedFamily M f x := by
  let K := relativeInvisible M f cutoff Y P.val
  have hKf : f ∉ K := fun h => hf h.1
  have hbound := relative_invisible_boundary_zero M f P cutoff hcut hfull
  have hint := pointed_boundary_zero_interior_zero M f x hx K hKf hbound
  apply pointed_standard_fixes_of_closed_zero M f x K _ g hg
  intro k v hv
  rcases hv with hv | hn
  · obtain ⟨i, hi, rfl⟩ := hv
    exact hint k i hi
  · by_cases hvK : v ∈ Sum.inl '' K
    · obtain ⟨i, hi, rfl⟩ := hvK
      exact hint k i hi
    · exact hbound k v hvK hn

/-- The nonspherical case is reduced to a proper containing type or to a
proper spherical visible factor; no new containment is assumed. -/
theorem relative_nonspherical_reduction {Y : Set S} {x : Artin M}
    (hf : f ∉ Y) (hx : x ∈ artinParabolic M {f}ᶜ) (hY : ¬IsSpherical M Y) :
    ReductionAt M (pointedInitial M f) Y x := by
  obtain ⟨cutoff, _, hcut⟩ := exteriorCutoff_exists M f Y x
  let U := (Sum.inl : S → S ⊕ Unit) '' Y
  obtain ⟨P, hP⟩ := relative_minimum_exists M f U cutoff (Y := Y) (x := x)
  let D := relativeContainingType M f cutoff Y P.val
  have hDY : D ⊆ Y := relative_containing_subset M f cutoff P
  by_cases hD : D = Y
  · let T := relativeVisible M f cutoff Y P.val
    let K := relativeInvisible M f cutoff Y P.val
    have hT : T ⊆ Y := fun _ hi => P.property.1 hi.1
    have hTs : IsSpherical M T := source_spherical_mono M Set.sdiff_subset P.val.property.1
    have hTproper : T ⊂ Y := lt_of_le_of_ne hT (by intro he; exact hY (he ▸ hTs))
    have hK : K ⊆ Y := fun _ hi => hi.1
    have hc : ∀ k ∈ K, ∀ t ∈ T, M k t = 2 := by
      intro k hk t ht
      rw [M.symmetric]
      exact relativeVisible_commutes M f cutoff Y P.val P.property.1 t ht k hk
    apply ReductionAt.split T K hTproper hK
    · exact standard_factor_normalized M K T hc
    · have he := relativeStabilizer_fixed_factor M (pointedInitial M f) K T x hc
        (fun g hg => by
          have h := relative_invisible_factor_fixes M f hf hx P cutoff hcut hD g hg
          rw [← mul_smul]
          exact h)
      have hKT : K ∪ T = Y := (Set.union_comm K T).trans hD
      rwa [hKT] at he
  · apply ReductionAt.smaller D (sourceCosetRepresentative M P.val*x⁻¹)
      (lt_of_le_of_ne hDY hD)
      (P.property.2 (sourceCosetRepresentative_mem M P.val))
    intro a ha
    exact relative_minimum_stabilizer_containment M f U cutoff
      (fun i hi => ⟨i, hi, rfl⟩) (fun _ ⟨i, _, he⟩ => ⟨i, he⟩)
      (by rintro ⟨i, hi, he⟩; exact hf (Sum.inl.inj he ▸ hi)) hx P hP a ha.1 (by
        have h := ha.2
        change a • (x • pointedInitial M f) = x • pointedInitial M f at h
        rw [← mul_smul] at h
        exact h)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MainIntersection
attribute [-simp] _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The main intersection theorems of paper 082-03

The hypotheses are exactly the published inputs documented in
`MeshNilpotence`, `FoldingGcdInput`, `AcyclicTwistInput`, and
`RelativeInitialStabilizer`. All relative-height, positive-height,
stabilizer-containment and rank-induction arguments are proved in this
local development; none of those new assertions is a hypothesis here.
-/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

/-- Theorem 8.2 on the actual pointed family with an unoperated frame. -/
theorem pointed_relative_stabilizers (hPub : PublishedSphericalInputs M)
    (f : S) (Y : Set S) (hf : f ∉ Y) (x : Artin M)
    (hx : x ∈ artinParabolic M {f}ᶜ) :
    ∃ (R : Set S) (c : Artin M), R ⊆ Y ∧ c ∈ artinParabolic M Y ∧
      relativeStabilizer M (pointedInitial M f) Y x = conjugate c⁻¹ (artinParabolic M R) := by
  apply relativeStabilizers_of_reductions_on M (pointedInitial M f) {f}ᶜ _ Y
    (by intro s hs hsf; exact hf (hsf ▸ hs)) x hx
  intro D hD z hz
  have hfD : f ∉ D := fun h => hD h rfl
  by_cases hDs : IsSpherical M D
  · exact spherical_reduction_s236 M f D hDs hfD (hPub.folding D hDs)
      (hPub.mesh D hDs) hPub.acyclic z hz
  · exact relative_nonspherical_reduction M f hfD hz hDs

section Relative
variable (X : Set S)
local notation "N" => relativeMatrix M X

omit [Fintype S] [LinearOrder S] in
private lemma relative_comap_standard (hEmb : VanDerLekRelativeEmbedding M X) (Y : Set S) :
    (artinParabolic N (Sum.inl '' Y)).comap (relativeArtinHom M X) = artinParabolic M Y := by
  rw [← relativeArtinHom_parabolic]
  exact Subgroup.comap_map_eq_self_of_injective hEmb.injective _

omit [Fintype S] [LinearOrder S] in
private lemma relative_comap_conjugate (c : Artin M) (P : Subgroup (Artin N)) :
    (conjugate (relativeArtinHom M X c) P).comap (relativeArtinHom M X) =
      conjugate c (P.comap (relativeArtinHom M X)) := by
  ext a
  simp only [Subgroup.mem_comap,mem_conjugate,map_mul,map_inv]

attribute [local instance] OAI.HarmonicArtin.ParabolicIntersections.instLinearOrderSumUnit_solutions_2
/-- The stronger inside-parabolic form, with its conjugator inside the
acting parabolic. This is the result used by the arbitrary-family theorem. -/
theorem inside_intersection_at
    (hEmb : VanDerLekRelativeEmbedding M X) (hPub : PublishedSphericalInputs N)
    (Y : Set S) (g : Artin M) :
    ∃ (R : Set S) (c : Artin M), R ⊆ Y ∧ c ∈ artinParabolic M Y ∧
      artinParabolic M Y ⊓ conjugate g (artinParabolic M X) =
        conjugate c (artinParabolic M R) := by
  let F := relativeArtinHom M X
  have hg : F g ∈ artinParabolic N {(.inr () : S⊕Unit)}ᶜ := by
    apply standard_mono N (X := Set.range (Sum.inl : S → S⊕Unit))
      (by rintro a ⟨s,rfl⟩; simp)
    rw [← Set.image_univ, ← relativeArtinHom_parabolic]
    exact ⟨g,by rw [standard_univ]; trivial,rfl⟩
  obtain ⟨R,c,hR,hc,he⟩ := pointed_relative_stabilizers N hPub (.inr ()) (Sum.inl '' Y)
    (by simp) (F g) hg
  rw [← relativeArtinHom_parabolic M X Y] at hc
  obtain ⟨b,hb,hbc⟩ := hc
  let D : Set S := Sum.inl ⁻¹' R
  have hD : D ⊆ Y := by
    intro s hs
    obtain ⟨t,ht,hte⟩ := hR hs
    exact Sum.inl.inj hte ▸ ht
  have hRD : R = Sum.inl '' D := by
    ext a
    constructor
    · intro ha
      obtain ⟨s,hs,rfl⟩ := hR ha
      exact ⟨s,ha,rfl⟩
    · rintro ⟨s,hs,rfl⟩
      exact hs
  have hleft : (relativeStabilizer N (pointedInitial N (.inr ())) (Sum.inl '' Y) (F g)).comap F =
      relativeStabilizer M (relativeInitial M X) Y g := by
    unfold relativeStabilizer
    rw [Subgroup.comap_inf,relative_comap_standard M X hEmb Y]
    rfl
  have he' := congrArg (Subgroup.comap F) he
  rw [hleft,hRD,←hbc,←map_inv,relative_comap_conjugate,
    relative_comap_standard M X hEmb D] at he'
  refine ⟨D,b⁻¹,hD,(artinParabolic M Y).inv_mem hb,?_⟩
  have hinit := relative_initial_stabilizer M X hEmb
  have hconj := conjugate_stabilizer M (relativeInitial M X) g 1
  simp only [one_smul,_root_.mul_one,hinit] at hconj
  simpa only [relativeStabilizer,←hconj] using he'
end Relative

attribute [local instance] OAI.HarmonicArtin.ParabolicIntersections.instLinearOrderSumUnit_solutions_3
/-- The entire inside-parabolic statement, conditional solely on published inputs. -/
theorem inside_intersection
    (hEmb : ∀ X : Set S, VanDerLekRelativeEmbedding M X)
    (hPub : ∀ X : Set S, PublishedSphericalInputs (relativeMatrix M X)) :
    InsideIntersectionProperty M := fun X Y g => inside_intersection_at M X (hEmb X) (hPub X) Y g

/-- Corollary 1.2: every subset has a unique smallest parabolic closure. -/
theorem parabolic_closure
    (hEmb : ∀ X : Set S, VanDerLekRelativeEmbedding M X)
    (hPub : ∀ X : Set S, PublishedSphericalInputs (relativeMatrix M X))
    (E : Set (Artin M)) :
    ∃! P : Subgroup (Artin M), IsParabolic M P ∧ E ⊆ P ∧
      ∀ Q : Subgroup (Artin M), IsParabolic M Q → E ⊆ Q → P ≤ Q :=
  parabolic_closure_of_inside M (inside_intersection M hEmb hPub) E

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ConditionalMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Main statements with the acyclic-evaluation input already discharged. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [fS : Fintype S] [oS : LinearOrder S] (M : CoxeterMatrix S)

theorem PublishedSphericalAlgebraInputs.withAcyclic (h : PublishedSphericalAlgebraInputs M) :
    PublishedSphericalInputs M where
  mesh := h.mesh
  folding := h.folding
  acyclic := acyclic_twist_input _

attribute [local instance] OAI.HarmonicArtin.ParabolicIntersections.conditionalSumOrder
/-- Paper 082-03, Corollary 1.2, the closure assertion for every subset. -/
theorem main_parabolic_closure
    (hEmb : ∀ X : Set S, VanDerLekRelativeEmbedding M X)
    (hAlg : ∀ X : Set S, PublishedSphericalAlgebraInputs (relativeMatrix M X))
    (E : Set (Artin M)) :
    ∃! P : Subgroup (Artin M), IsParabolic M P ∧ E ⊆ P ∧
      ∀ Q : Subgroup (Artin M), IsParabolic M Q → E ⊆ Q → P ≤ Q :=
  parabolic_closure M hEmb (fun X => (hAlg X).withAcyclic _) E

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_FoldingPositive
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive-monoid folding and its action on simple elements. These are
proved from the Coxeter word theorem and the established folding geometry. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
    (Y : Set S) (hY : IsSpherical M Y)
local notation "R" => restrictedMatrix M Y
local notation "N" => unfoldedMatrix M Y
local notation "m" => fusionLabelSize M

lemma foldedPositiveHom_word (w : List Y) :
    foldedPositiveHom M Y hY (wordPositive R w)=wordPositive N (fusionExpandedWord m w) := by
  unfold wordPositive
  rw [map_list_prod]
  simp only [List.map_map,Function.comp_def,foldedPositiveHom_generator]
  exact folded_word_product M Y w

lemma foldedPositiveHom_simpleLift (w : (R).Group) :
    foldedPositiveHom M Y hY (positiveSimpleLift R w)=
      positiveSimpleLift N (unfoldedHom M Y hY w) := by
  change foldedPositiveHom M Y hY (wordPositive R (reducedExpression R w))=_
  rw [foldedPositiveHom_word]
  have hu := unfolded_reducedWord M Y hY _ (reducedExpression_reduced R w)
  have hw : (N).toCoxeterSystem.wordProd (fusionExpandedWord m (reducedExpression R w)) =
      unfoldedHom M Y hY w := by
    rw [← unfoldedHom_wordProd]
    exact congrArg (unfoldedHom M Y hY) (wordCoxeter_reducedExpression R w)
  rw [←hw]
  exact (positiveSimpleLift_word N _ hu).symm

/-- A left atom divides the folded simple element precisely when its
original color divides the original simple element. -/
theorem folded_simple_atom_iff (w : (R).Group) (α : Y × FusionLabel m) :
    PositivePrefix N (positiveGenerator N α)
      (foldedPositiveHom M Y hY (positiveSimpleLift R w)) ↔
    PositivePrefix R (positiveGenerator R α.1) (positiveSimpleLift R w) := by
  rw [foldedPositiveHom_simpleLift,←positiveSimpleLift_simple N α,
    ←positiveSimpleLift_simple R α.1,positivePrefix_simple_iff,positivePrefix_simple_iff,
    weakPrefix_simple_iff,weakPrefix_simple_iff]
  have h := unfoldedHom_left_ascent M Y hY w α
  have hn := (N).toCoxeterSystem.length_simple_mul (unfoldedHom M Y hY w) α
  have hr := (R).toCoxeterSystem.length_simple_mul w α.1
  dsimp only at h
  omega

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PositiveTransport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relabeling positive Artin monoids and finite-type cancellation. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable

variable {S T : Type} (M : CoxeterMatrix S) (N : CoxeterMatrix T)
    (f : S → T) (hf : ∀ i j, N (f i) (f j)=M i j)

lemma positiveMap_word (w : List S) :
    positiveMap M N f hf (wordPositive M w)=wordPositive N (w.map f) := by
  simp only [wordPositive,map_list_prod,List.map_map,Function.comp_def,positiveMap_generator]

/-- Cancellation in a finite Coxeter type, without an artificial subtype
of generators in the statement. -/
theorem finite_positive_cancel_left [Fintype S] [LinearOrder S] [Finite M.Group]
    (a b c : PositiveArtin M) (h : a*b=a*c) : b=c := by
  let R := restrictedMatrix M Set.univ
  let f : S → (Set.univ : Set S) := fun s => ⟨s,Set.mem_univ s⟩
  let up := positiveMap M R f (fun _ _ => rfl)
  let down := positiveMap R M Subtype.val (fun _ _ => rfl)
  have inverse : ∀ x, down (up x)=x := by
    intro x
    obtain ⟨w,rfl⟩ := positive_word_surjective M x
    calc
      down (up (wordPositive M w)) = down (wordPositive R (w.map f)) :=
        congrArg down (positiveMap_word M R f (fun _ _ => rfl) w)
      _ = wordPositive M ((w.map f).map Subtype.val) :=
        positiveMap_word R M Subtype.val (fun _ _ => rfl) (w.map f)
      _ = wordPositive M w := by
        rw [List.map_map]
        change wordPositive M (w.map id)=wordPositive M w
        rw [List.map_id]
  have hs : IsSpherical M Set.univ := by
    change Finite (coxeterParabolic M Set.univ)
    infer_instance
  have he : up b=up c := spherical_positive_cancel_left M Set.univ hs (up a) (up b) (up c)
    (by simpa only [←map_mul] using congrArg up h)
  simpa only [inverse] using congrArg down he

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_FoldingSimpleGcd
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Folding preserves greatest common prefixes of simple elements. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
    (Y : Set S) (hY : IsSpherical M Y)
local notation "R" => restrictedMatrix M Y
local notation "N" => unfoldedMatrix M Y
local notation "Φ" => foldedPositiveHom M Y hY
local notation "P" => positiveSimpleLift R

private lemma folded_prefix {a b : PositiveArtin R} (h : PositivePrefix R a b) :
    PositivePrefix N (Φ a) (Φ b) := by
  obtain ⟨c,rfl⟩ := h
  exact ⟨_,map_mul _ _ _⟩

/-- Greatest common prefixes of simples are preserved by the color folding.
The induction removes one complete color at a time. -/
theorem folded_simple_gcd (u v g : (R).Group)
    (hgu : PositivePrefix R (P g) (P u)) (hgv : PositivePrefix R (P g) (P v))
    (hg : ∀ e, PositivePrefix R e (P u) → PositivePrefix R e (P v) → PositivePrefix R e (P g)) :
    ∀ e, PositivePrefix N e (Φ (P u)) → PositivePrefix N e (Φ (P v)) →
      PositivePrefix N e (Φ (P g)) := by
  let : Finite (N).Group := unfolded_finite M Y hY
  let : LinearOrder (Y × FusionLabel (fusionLabelSize M)) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  have cancelR := spherical_positive_cancel_left M Y hY
  have cancelN := finite_positive_cancel_left N
  induction u using (measure (fun u => (R).toCoxeterSystem.length u)).wf.induction
      generalizing v g with
  | h u ih =>
    intro e heu hev
    obtain ⟨d,hdu,hdv,hd⟩ := exists_greatest_common_simplePrefix N
      (unfoldedHom M Y hY u) (unfoldedHom M Y hY v)
    simp only [←foldedPositiveHom_simpleLift] at hdu hdv hd
    apply positivePrefix_trans N (hd e heu hev)
    by_cases hd1 : positiveSimpleLift N d=1
    · rw [hd1]
      exact positivePrefix_one N _
    obtain ⟨α,hα⟩ := exists_positive_first N hd1
    have hau := positivePrefix_trans N hα hdu
    have hav := positivePrefix_trans N hα hdv
    have hiu := (folded_simple_atom_iff M Y hY u α).mp hau
    have hiv := (folded_simple_atom_iff M Y hY v α).mp hav
    have hig := hg _ hiu hiv
    obtain ⟨ur,hur⟩ := hiu
    obtain ⟨vr,hvr⟩ := hiv
    obtain ⟨gr,hgr⟩ := hig
    have su := (positive_simple_factors R _ _ _ hur.symm).2
    have sv := (positive_simple_factors R _ _ _ hvr.symm).2
    have sg := (positive_simple_factors R _ _ _ hgr.symm).2
    have pgu : PositivePrefix R gr ur :=
      (positivePrefix_mul_left_iff R cancelR _ _ _).mp (by rwa [←hur,←hgr])
    have pgv : PositivePrefix R gr vr :=
      (positivePrefix_mul_left_iff R cancelR _ _ _).mp (by rwa [←hvr,←hgr])
    have pg : ∀ x, PositivePrefix R x ur → PositivePrefix R x vr → PositivePrefix R x gr := by
      intro x hxu hxv
      apply (positivePrefix_mul_left_iff R cancelR (positiveGenerator R α.1) x gr).mp
      rw [←hgr]
      apply hg
      · rw [hur]; exact positivePrefix_mul_left R _ hxu
      · rw [hvr]; exact positivePrefix_mul_left R _ hxv
    have hcolor : PositivePrefix N (Φ (positiveGenerator R α.1)) (positiveSimpleLift N d) :=
      hd _ (folded_prefix M Y hY ⟨ur,hur⟩) (folded_prefix M Y hY ⟨vr,hvr⟩)
    obtain ⟨dr,hdr⟩ := hcolor
    have dru : PositivePrefix N dr (Φ ur) :=
      (positivePrefix_mul_left_iff N cancelN _ _ _).mp (by
        simpa only [hur,map_mul,hdr] using hdu)
    have drv : PositivePrefix N dr (Φ vr) :=
      (positivePrefix_mul_left_iff N cancelN _ _ _).mp (by
        simpa only [hvr,map_mul,hdr] using hdv)
    have hlt : (R).toCoxeterSystem.length (positiveToCoxeter R ur) <
        (R).toCoxeterSystem.length u := by
      have hdg := congrArg (positiveDegree R) hur
      simp only [positiveDegree_simpleLift,positiveDegree_mul,positiveDegree_generator] at hdg
      rw [su,positiveDegree_simpleLift] at hdg
      omega
    have hr := ih (positiveToCoxeter R ur) hlt (positiveToCoxeter R vr)
      (positiveToCoxeter R gr) (by rwa [←sg,←su]) (by rwa [←sg,←sv])
      (by simpa only [←su,←sv,←sg] using pg) dr
      (by rwa [←su]) (by rwa [←sv])
    rw [←sg] at hr
    rw [hdr,hgr,map_mul]
    exact positivePrefix_mul_left N _ hr

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PositiveHeadProduct
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The greedy head of a product with a simple left factor. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S)

/-- If `h` is the greatest simple prefix of `b`, the greatest simple prefix
of `a*b` is `a*g`, where `g` is the gcd of the complement of `a` and `h`.
This is the local normal-form step used in folding. -/
theorem positive_head_product
    (cancel : ∀ a b c : PositiveArtin M, a*b=a*c → b=c)
    (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
    (a h g : M.Group) (b : PositiveArtin M)
    (hh : PositivePrefix M (positiveSimpleLift M h) b)
    (hhead : ∀ w, PositivePrefix M (positiveSimpleLift M w) b →
      PositivePrefix M (positiveSimpleLift M w) (positiveSimpleLift M h))
    (hgc : PositivePrefix M (positiveSimpleLift M g) (positiveSimpleLift M (a⁻¹*z)))
    (hgh : PositivePrefix M (positiveSimpleLift M g) (positiveSimpleLift M h))
    (hgreat : ∀ e, PositivePrefix M e (positiveSimpleLift M (a⁻¹*z)) →
      PositivePrefix M e (positiveSimpleLift M h) → PositivePrefix M e (positiveSimpleLift M g)) :
    ∃ k : M.Group, positiveSimpleLift M k=positiveSimpleLift M a*positiveSimpleLift M g ∧
      PositivePrefix M (positiveSimpleLift M k) (positiveSimpleLift M a*b) ∧
      ∀ w, PositivePrefix M (positiveSimpleLift M w) (positiveSimpleLift M a*b) →
        PositivePrefix M (positiveSimpleLift M w) (positiveSimpleLift M k) := by
  have complement := positiveSimpleLift_left_complement M z hz a
  have hag : PositivePrefix M (positiveSimpleLift M a*positiveSimpleLift M g)
      (positiveSimpleLift M z) := by
    rw [←complement]
    exact positivePrefix_mul_left M _ hgc
  have hsimple := positivePrefix_of_simple_eq M hag rfl
  refine ⟨positiveToCoxeter M (positiveSimpleLift M a*positiveSimpleLift M g),
    hsimple.symm, ?_, ?_⟩
  · rw [←hsimple]
    exact positivePrefix_mul_left M _ (positivePrefix_trans M hgh hh)
  · intro w hw
    rw [←hsimple]
    have haZ : PositivePrefix M (positiveSimpleLift M a) (positiveSimpleLift M z) :=
      ⟨_, complement.symm⟩
    have hwZ : PositivePrefix M (positiveSimpleLift M w) (positiveSimpleLift M z) :=
      ⟨_, (positiveSimpleLift_left_complement M z hz w).symm⟩
    obtain ⟨c,hac,hwc,hc⟩ := positive_lcm_of_common_multiple M
      (positive_greatest_common_left_divisor M cancel z hz) _ _ ⟨_,haZ,hwZ⟩
    have hcZ := hc _ haZ hwZ
    have hcab := hc _ ⟨b,rfl⟩ hw
    obtain ⟨e,he⟩ := hac
    have hcSimple := positivePrefix_of_simple_eq M hcZ rfl
    have heSimple := (positive_simple_factors M _ _ _ (he.symm.trans hcSimple)).2
    have heB : PositivePrefix M e b :=
      (positivePrefix_mul_left_iff M cancel _ _ _).mp (by rwa [←he])
    have heC : PositivePrefix M e (positiveSimpleLift M (a⁻¹*z)) :=
      (positivePrefix_mul_left_iff M cancel _ _ _).mp (by simpa only [←complement,he] using hcZ)
    have heH : PositivePrefix M e (positiveSimpleLift M h) := by
      rw [heSimple] at heB ⊢
      exact hhead _ heB
    have heg := hgreat e heC heH
    apply positivePrefix_trans M hwc
    rw [he]
    exact positivePrefix_mul_left M _ heg

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_FoldingHead
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Greedy heads, and hence left atoms, are preserved by folding. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
    (Y : Set S) (hY : IsSpherical M Y)
local notation "R" => restrictedMatrix M Y
local notation "N" => unfoldedMatrix M Y
local notation "Φ" => foldedPositiveHom M Y hY
local notation "P" => positiveSimpleLift R

omit [Fintype S] [LinearOrder S] in
private lemma positive_nil : wordPositive R [] = 1 := rfl

omit [Fintype S] [LinearOrder S] in
private lemma positive_cons_p1 (i : Y) (w : List Y) :
    wordPositive R (i::w)=positiveGenerator R i*wordPositive R w := rfl

/-- The original and folded positive elements have corresponding greedy heads. -/
theorem folded_positive_head (b : PositiveArtin R) :
    ∃ h : (R).Group,
      PositivePrefix R (P h) b ∧
      (∀ w, PositivePrefix R (P w) b → PositivePrefix R (P w) (P h)) ∧
      PositivePrefix N (Φ (P h)) (Φ b) ∧
      (∀ w, PositivePrefix N (positiveSimpleLift N w) (Φ b) →
        PositivePrefix N (positiveSimpleLift N w) (Φ (P h))) := by
  let : Finite (R).Group := restricted_finite M Y hY
  let : Finite (N).Group := unfolded_finite M Y hY
  let : LinearOrder (Y × FusionLabel (fusionLabelSize M)) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  obtain ⟨z,hz⟩ := exists_longest (R).toCoxeterSystem
  have hzN := unfolded_longest M Y hY z hz
  have cancelR := spherical_positive_cancel_left M Y hY
  have cancelN := finite_positive_cancel_left N
  obtain ⟨word,rfl⟩ := positive_word_surjective R b
  induction word with
  | nil =>
    refine ⟨1,?_,?_,?_,?_⟩
    · simpa only [positiveSimpleLift_one,positive_nil] using positivePrefix_refl R 1
    · intro w hw
      simpa only [positiveSimpleLift_one,positive_nil] using hw
    · simp only [positiveSimpleLift_one,positive_nil,map_one]
      exact positivePrefix_refl N 1
    · intro w hw
      simpa only [positiveSimpleLift_one,positive_nil,map_one] using hw
  | cons i word ih =>
    obtain ⟨h,hh,hhead,hhN,hheadN⟩ := ih
    obtain ⟨g,hgc,hgh,hgreat⟩ := exists_greatest_common_simplePrefix R
      (((R).toCoxeterSystem.simple i)⁻¹*z) h
    obtain ⟨k,hk,hkb,hkhead⟩ := positive_head_product R cancelR z hz
      ((R).toCoxeterSystem.simple i) h g (wordPositive R word) hh hhead hgc hgh hgreat
    have hcN : PositivePrefix N
        (positiveSimpleLift N (unfoldedHom M Y hY g))
        (positiveSimpleLift N ((unfoldedHom M Y hY ((R).toCoxeterSystem.simple i))⁻¹*
          unfoldedHom M Y hY z)) := by
      rw [←map_inv,←map_mul,←foldedPositiveHom_simpleLift,←foldedPositiveHom_simpleLift]
      obtain ⟨r,hr⟩ := hgc
      exact ⟨Φ r,by rw [hr,map_mul]⟩
    have hgN : PositivePrefix N (positiveSimpleLift N (unfoldedHom M Y hY g))
        (positiveSimpleLift N (unfoldedHom M Y hY h)) := by
      rw [←foldedPositiveHom_simpleLift,←foldedPositiveHom_simpleLift]
      obtain ⟨r,hr⟩ := hgh
      exact ⟨Φ r,by rw [hr,map_mul]⟩
    have hgreatN := folded_simple_gcd M Y hY _ _ _ hgc hgh hgreat
    simp only [foldedPositiveHom_simpleLift,map_mul,map_inv] at hgreatN
    obtain ⟨kN,hkN,hkbN,hkheadN⟩ := positive_head_product N cancelN
      (unfoldedHom M Y hY z) hzN
      (unfoldedHom M Y hY ((R).toCoxeterSystem.simple i))
      (unfoldedHom M Y hY h) (unfoldedHom M Y hY g) (Φ (wordPositive R word))
      (by simpa only [foldedPositiveHom_simpleLift] using hhN)
      (by simpa only [foldedPositiveHom_simpleLift] using hheadN) hcN hgN hgreatN
    have heN : positiveSimpleLift N kN=Φ (P k) := by
      rw [hkN,←foldedPositiveHom_simpleLift,←foldedPositiveHom_simpleLift,←map_mul,←hk]
    refine ⟨k,?_,?_,?_,?_⟩
    · simpa only [positiveSimpleLift_simple,positive_cons_p1] using hkb
    · simpa only [positiveSimpleLift_simple,positive_cons_p1] using hkhead
    · rw [←heN]
      simpa only [←foldedPositiveHom_simpleLift,positiveSimpleLift_simple,positive_cons_p1,←map_mul] using hkbN
    · intro w hw
      rw [←heN]
      apply hkheadN
      simpa only [←foldedPositiveHom_simpleLift,positiveSimpleLift_simple,positive_cons_p1,←map_mul] using hw

/-- Every atom dividing an expanded positive word has its entire color as
a left divisor. This is the exact divisibility consequence needed downstream. -/
theorem folded_atom_reflect (b : PositiveArtin R)
    (α : Y × FusionLabel (fusionLabelSize M))
    (hα : PositivePrefix N (positiveGenerator N α) (Φ b)) :
    PositivePrefix R (positiveGenerator R α.1) b := by
  obtain ⟨h,hh,_,_,hhead⟩ := folded_positive_head M Y hY b
  have hp : PositivePrefix N (positiveGenerator N α) (Φ (P h)) := by
    simpa only [positiveSimpleLift_simple,positive_cons_p1] using
      hhead ((N).toCoxeterSystem.simple α) (by simpa only [positiveSimpleLift_simple,positive_cons_p1] using hα)
  exact positivePrefix_trans R ((folded_simple_atom_iff M Y hY h α).mp hp) hh

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_FoldingGcd
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge of the published common-left-atom folding input. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
    (Y : Set S) (hY : IsSpherical M Y)
local notation "R" => restrictedMatrix M Y
local notation "N" => unfoldedMatrix M Y
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "f" => unfoldedInclusion M Y

private lemma expanded_braid_prefix (u : List Y) (a : Y × FusionLabel m)
    (r : List (FusionVertex (V:=S⊕Unit) m))
    (hu : PositiveBraidRel Q
      (fusionExpandedWord m (u.map fun j : Y => (Sum.inl (j:S) : S⊕Unit))) (f a::r)) :
    PositivePrefix N (positiveGenerator N a) (foldedPositiveHom M Y hY (wordPositive R u)) := by
  let : Nonempty (Y × FusionLabel m) := ⟨a⟩
  rw [fusionExpandedWord_map] at hu
  have hs : ∀ x ∈ (fusionExpandedWord m u).map f, x ∈ Set.range f := by
    intro x hx
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
    exact ⟨b,rfl⟩
  have he := positiveBraidRel_restrict Q N f (unfoldedInclusion_injective M Y)
    (unfolded_ordinaryMatrix M Y hY) hu hs
  have hinv : ∀ x, Function.invFun f (f x)=x :=
    Function.leftInverse_invFun (unfoldedInclusion_injective M Y)
  have hw : ((fusionExpandedWord m u).map f).map (Function.invFun f)=fusionExpandedWord m u := by
    rw [List.map_map]
    have hi : (Function.invFun f ∘ f)=id := funext hinv
    rw [hi,List.map_id]
  rw [hw,List.map_cons,hinv] at he
  rw [foldedPositiveHom_word]
  exact ⟨wordPositive N (r.map (Function.invFun f)),he⟩

/-- Castella's common-atom consequence, now proved for the particular
color folding rather than supplied as a hypothesis. -/
theorem folding_gcd_input : PublishedFoldingGcd M Y hY where
  common_atom := by
    intro u v α r s hu hv
    have hmem := (hu.mem_iff Q α).mpr (by simp)
    rw [fusionExpandedWord_map] at hmem
    obtain ⟨a,_,ha⟩ := List.mem_map.mp hmem
    change f a=α at ha
    subst α
    exact ⟨a.1,
      folded_atom_reflect M Y hY _ a (expanded_braid_prefix M Y hY u a r hu),
      folded_atom_reflect M Y hY _ a (expanded_braid_prefix M Y hY v a s hv)⟩

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ReducedInputsMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Main results after discharging the acyclic-twist and folding inputs. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

theorem PublishedMeshInput.withAlgebra (h : PublishedMeshInput M) :
    PublishedSphericalAlgebraInputs M where
  mesh := h
  folding := folding_gcd_input M

attribute [local instance] OAI.HarmonicArtin.ParabolicIntersections.instLinearOrderSumUnit_solutions_5
/-- Corollary 1.2: every subset has a unique smallest containing parabolic. -/
theorem mesh_parabolic_closure
    (hEmb : ∀ X : Set S, VanDerLekRelativeEmbedding M X)
    (hMesh : ∀ X : Set S, PublishedMeshInput (relativeMatrix M X))
    (E : Set (Artin M)) :
    ∃! P : Subgroup (Artin M), IsParabolic M P ∧ E ⊆ P ∧
      ∀ Q : Subgroup (Artin M), IsParabolic M Q → E ⊆ Q → P ≤ Q :=
  main_parabolic_closure M hEmb (fun X => (hMesh X).withAlgebra _) E

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ParabolicRetractionAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The parabolic gallery retraction as an action of the Artin presentation. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (J : Set S)

lemma parabolicRetractionAction_generator (s : S) :
    parabolicRetractionAction M J (generator M s)=MulOpposite.op (parabolicStepPerm M J s) :=
  PresentedGroup.toGroup.of _

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_StandardEmbedding
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Injectivity of every finite-rank standard Artin parabolic. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (J : Set S)
local notation "cs" => M.toCoxeterSystem
local notation "R" => restrictedMatrix M J

omit [Fintype S] in
private lemma component_of_parabolic (w : M.Group) (hw : w ∈ parabolic cs J) :
    parabolicComponent cs J w=w := by
  have hmin : IsParabolicMinimum cs J (1 : M.Group) := by
    intro a _
    simp only [(cs).length_one,mul_one]
    exact Nat.zero_le _
  have hr : parabolicRep cs J w=1 :=
    parabolicRep_eq_of_decomposition cs J w w 1 hw hmin (mul_one w).symm
  simp only [parabolicComponent,hr,inv_one,mul_one]

lemma parabolicStepLetter_standard (w : M.Group) (hw : w ∈ parabolic cs J) (s : J) :
    parabolicStepLetter cs J w s=some s := by
  have hws : w*(cs).simple s ∈ parabolic cs J :=
    (parabolic cs J).mul_mem hw (simple_mem_parabolic cs J s.property)
  have hv := parabolicStepLetter_value cs J w s
  unfold parabolicStepRatio at hv
  rw [component_of_parabolic M J w hw,component_of_parabolic M J _ hws,inv_mul_cancel_left] at hv
  cases hl : parabolicStepLetter cs J w s with
  | none =>
    rw [hl] at hv
    change 1=(cs).simple s at hv
    have hh := congrArg (cs).length hv
    rw [(cs).length_one,(cs).length_simple] at hh
    omega
  | some t =>
    rw [hl] at hv
    have he : t=s := Subtype.ext (simple_injective cs hv)
    exact congrArg some he

/-- On the standard parabolic, the gallery action is its right regular action. -/
theorem parabolicRetractionAction_standard (g a : Artin R) :
    MulOpposite.unop (parabolicRetractionAction M J (restrictedArtinHom M J g))
      (parabolicState M J a)=parabolicState M J (a*g) := by
  let f := (parabolicRetractionAction M J).comp (restrictedArtinHom M J)
  have hg : g ∈ Subgroup.closure (Set.range (generator R)) := by
    rw [show Subgroup.closure (Set.range (generator R))=⊤ from
      PresentedGroup.closure_range_of (braidRelators R)]
    trivial
  change MulOpposite.unop (f g) (parabolicState M J a)=_
  induction hg using Subgroup.closure_induction generalizing a with
  | mem x hx =>
    obtain ⟨s,rfl⟩ := hx
    have hw : restrictionHom M J (artinCoxeter R a) ∈ parabolic cs J :=
      restrictionHom_mem_parabolic M J _
    simp only [f,MonoidHom.comp_apply,restrictedArtinHom_generator,
      parabolicRetractionAction_generator]
    change (restrictionHom M J (artinCoxeter R a)*(cs).simple s,
      a*parabolicStepArtin M J (restrictionHom M J (artinCoxeter R a)) s)=_
    rw [parabolicStepArtin,parabolicStepLetter_standard M J _ hw]
    simp only [Option.toList_some,wordArtin,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
      parabolicState,map_mul,artinCoxeter_generator,restrictionHom_simple]
  | one => simp only [map_one,MulOpposite.unop_one,Equiv.Perm.one_apply,mul_one]
  | mul x y hx hy ihx ihy =>
    rw [map_mul,MulOpposite.unop_mul]
    change MulOpposite.unop (f y) (MulOpposite.unop (f x) (parabolicState M J a))=_
    rw [ihx,ihy,mul_assoc]
  | inv x hx ih =>
    rw [map_inv,MulOpposite.unop_inv]
    change (MulOpposite.unop (f x)).symm (parabolicState M J a)=_
    apply (MulOpposite.unop (f x)).injective
    simp only [Equiv.apply_symm_apply,ih,inv_mul_cancel_right]

/-- Van der Lek's standard-parabolic injectivity theorem in finite rank,
proved from the Coxeter retraction and the Artin braid presentation. -/
theorem standardArtinEmbedding : Function.Injective (restrictedArtinHom M J) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have ha := parabolicRetractionAction_standard M J g 1
  rw [hg,map_one,MulOpposite.unop_one,Equiv.Perm.one_apply,one_mul] at ha
  exact (congrArg Prod.snd ha).symm

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge of the one-color standard embedding input. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (X : Set S)

omit [LinearOrder S] in
/-- The relative extension includes the original Artin presentation injectively. -/
theorem relative_embedding_input : VanDerLekRelativeEmbedding M X := by
  let N := relativeMatrix M X
  let T : Set (S⊕Unit) := Set.range Sum.inl
  let e : S ≃ T := Equiv.ofInjective (Sum.inl : S → S⊕Unit) Sum.inl_injective
  let R := restrictedMatrix N T
  have hu : ∀ i j : S, R (e i) (e j)=M i j := fun _ _ => rfl
  have hd : ∀ i j : T, M (e.symm i) (e.symm j)=R i j := by
    intro i j
    have hi : Sum.inl (e.symm i)=i.val := congrArg Subtype.val (e.apply_symm_apply i)
    have hj : Sum.inl (e.symm j)=j.val := congrArg Subtype.val (e.apply_symm_apply j)
    change M (e.symm i) (e.symm j)=N i.val j.val
    rw [←hi,←hj]
    rfl
  let up := artinMap M R e hu
  have hup : Function.Injective up := (artinMap_leftInverse M R e hu e.symm hd e.left_inv).injective
  have hfactor : (restrictedArtinHom N T).comp up=relativeArtinHom M X := by
    apply PresentedGroup.ext
    intro s
    change restrictedArtinHom N T (artinMap M R e hu (generator M s)) =
      relativeArtinHom M X (generator M s)
    rw [artinMap_generator,restrictedArtinHom_generator,relativeArtinHom_generator]
    rfl
  refine ⟨?_⟩
  rw [←hfactor]
  exact (standardArtinEmbedding N T).comp hup

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Main results after discharging standard embeddings, acyclic twists,
and folding. Only mesh nilpotence and the dynamical criteria remain. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

attribute [local instance] OAI.HarmonicArtin.ParabolicIntersections.instLinearOrderSumUnit_solutions_6
/-- Paper 082-03, Corollary 1.2, parabolic closure. -/
theorem parabolic_closure_of_mesh
    (hMesh : ∀ X : Set S, PublishedMeshInput (relativeMatrix M X))
    (E : Set (Artin M)) :
    ∃! P : Subgroup (Artin M), IsParabolic M P ∧ E ⊆ P ∧
      ∀ Q : Subgroup (Artin M), IsParabolic M Q → E ⊆ Q → P ≤ Q :=
  mesh_parabolic_closure M (relative_embedding_input M) hMesh E

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_UnconditionalMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unconditional parabolic intersections and closure

The spherical mesh input is proved by weighted path contractions and finite
Jones--Wenzl projections. Together with the proved standard embeddings,
folding, and acyclic evaluation, this discharges every input to Theorem 1.1
and Corollary 1.2 of paper 082-03. The dynamical corollary below still names
its separate published geometric input explicitly.
-/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

attribute [local instance] OAI.HarmonicArtin.ParabolicIntersections.instLinearOrderSumUnit_solutions_7
/-- Paper 082-03, Corollary 1.2: the unique smallest containing parabolic. -/
theorem unconditional_parabolic_closure_oai (E : Set (Artin M)) :
    ∃! P : Subgroup (Artin M), IsParabolic M P ∧ E ⊆ P ∧
      ∀ Q : Subgroup (Artin M), IsParabolic M Q → E ⊆ Q → P ≤ Q :=
  parabolic_closure_of_mesh M (fun X => spherical_mesh_input_s236 (relativeMatrix M X)) E

end HarmonicArtin.ParabolicIntersections

end OAI
end

theorem solution : type_of% @OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure_oai := @OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure_oai
