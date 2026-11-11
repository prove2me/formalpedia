-- Prove2me | solution 1 for OAI.HarmonicArtin.ParabolicIntersections.spherical_reduction_s236
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T20:26:04.626438+00:00
-- url     : https://prove2.me/submissions/1be51596-9a88-4bf7-a206-32e448d68f1e

import Mathlib
import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap010
import Definitions.Def_OAIQ236Ap013

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveLiftSimple
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

theorem finiteArtin_positive_fraction [Finite M.Group] (g:Artin M) :
    ∃ u v:List S,g=wordArtin M u*(wordArtin M v)⁻¹ := by
  obtain ⟨z,hz⟩:=exists_longest M.toCoxeterSystem
  obtain ⟨n,u,hu⟩:=positive_fraction_longest M z hz g
  obtain ⟨v,hv⟩:=positiveLift_longest_square_positive M z
  obtain ⟨v',hv'⟩:=wordArtin_positive_power M v n
  refine ⟨u,v',?_⟩
  rw [hu,hv',hv,zpow_neg,zpow_natCast]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_Level
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

namespace ReversibleQuiver.Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

namespace BasedComplex

variable {I : Type*} [Fintype I]

lemma restrict_minimal (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q)
    (T : Set I) [Fintype T] (hT : ∀ i ∈ T, ∀ j ∈ T, ∀ k ∉ T,
      E.differential i k * E.differential k j = 0) :
    (E.restrict Q T hT).IsMinimal Q := by
  intro i j
  exact hE i j

end BasedComplex
end ReversibleQuiver.Zigzag
end HarmonicArtin

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

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Cancellation_SphericalPositiveCancelMonoid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

theorem spherical_positiveToArtin_injective (T:Set S) (hT:IsSpherical M T) :
    Function.Injective (positiveToArtin (restrictedMatrix M T)) := by
  intro a b h
  apply spherical_positiveToAmbient_injective M T hT
  exact congrArg (restrictedArtinHom M T) h

omit [LinearOrder S] in
theorem spherical_positive_monoid_fractions (T:Set S) (hT:IsSpherical M T)
    (g:Artin (restrictedMatrix M T)) :
    (∃a b:PositiveArtin (restrictedMatrix M T),g=positiveToArtin _ a*(positiveToArtin _ b)⁻¹) ∧
    (∃c d:PositiveArtin (restrictedMatrix M T),g=(positiveToArtin _ c)⁻¹*positiveToArtin _ d) := by
  have : Finite (restrictedMatrix M T).Group := restricted_finite M T hT
  constructor
  · obtain ⟨a,b,h⟩:=finiteArtin_positive_fraction (restrictedMatrix M T) g
    exact ⟨wordPositive _ a,wordPositive _ b,by simpa only [positiveToArtin_word] using h⟩
  · obtain ⟨a,b,h⟩:=finiteArtin_positive_left_fraction (restrictedMatrix M T) g
    exact ⟨wordPositive _ a,wordPositive _ b,by simpa only [positiveToArtin_word] using h⟩

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
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_AcyclicTwistInput
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published acyclic-evaluation input

Seidel--Thomas, *Braid group actions on derived categories of coherent
sheaves*, Duke Math. J. 108 (2001), Definition 2.5 (equation (2.2)),
and the first sentence of the proof of Proposition 2.12:
https://arxiv.org/pdf/math/0001043, pp. 13 and 17.
A twist is the cone of evaluation. If the entire evaluated Hom complex
is acyclic, this cone is isomorphic to the original object. For bounded
projective complexes the resulting isomorphism is a homotopy equivalence.
Below is precisely this standard consequence in the existing vertex-test
notation. It is independent of the Artin stabilizer argument.
-/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "diag" => coxeterFusionEdge_diag M
local notation "Q" => fusionQuiver m d hd

/-- Acyclic tests make every generator, and hence the entire standard
parabolic, fix the actual pointed family. -/
theorem pointed_standard_fixes_of_acyclic_tests (hAcyclic : PublishedAcyclicTwist Q)
    (Y : Set S) (x : Artin M)
    (h : ∀ H, ∀ α ∈ Set.range (unfoldedInclusion M Y), ∀ l c,
      ClassTestExact Q α l c (pointedFamily M f x H))
    (g : Artin M) (hg : g ∈ artinParabolic M Y) :
    pointedFamily M f (g*x)=pointedFamily M f x := by
  have hgen (i : S) (hi : i ∈ Y) (H : PointedLabel M) :
      pointedAction M (generator M i) (pointedFamily M f x H)=pointedFamily M f x H := by
    rw [pointedAction_generator, fusionPacketPerm, ← classPacketPerm_toList]
    have hl (w : List (FusionLabel m)) :
        (w.map (fun L => classTwistPerm Q (fusionQuiver_no_loops m d hd diag)
          (.inl i,L))).prod (pointedFamily M f x H)=pointedFamily M f x H := by
      induction w with
      | nil => rfl
      | cons L w ih =>
        change classPositiveTwist Q (.inl i,L)
          ((w.map (fun L => classTwistPerm Q (fusionQuiver_no_loops m d hd diag)
            (.inl i,L))).prod (pointedFamily M f x H))=_
        rw [ih]
        exact hAcyclic.fix_of_exact _ _ (h H _ ⟨(⟨i,hi⟩,L),rfl⟩)
    exact hl _
  funext H
  change pointedAction M (g*x) (pointedInitial M f H)=_
  rw [map_mul, Equiv.Perm.mul_apply]
  change pointedAction M g (pointedFamily M f x H)=_
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i,hi,rfl⟩ := hg
    exact hgen i hi H
  | one => rw [map_one]; rfl
  | mul a b _ _ ha hb => simp only [map_mul, Equiv.Perm.mul_apply, hb,ha]
  | inv a _ ha =>
    rw [map_inv]
    apply (pointedAction M a).injective
    change (pointedAction M a) ((pointedAction M a).symm _) = _
    rw [Equiv.apply_symm_apply,ha]

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

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshNilpotence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published finite-Dynkin path input

`MeshNilpotent` is the positive-degree nilpotence assertion for the
preprojective (mesh) algebra of an induced finite Dynkin graph. Its
relations are displayed explicitly, rather than asserted for a complex.
The standard finite-dimensionality input is Amiot, *On the structure of
triangulated categories with finitely many indecomposables*, Bull. Soc.
Math. France 135 (2007), Proposition 9.1; the essential-path formulation
is Coquereaux (2002), §§3.1–3.2, and Cooper (2007), Theorem 5.4.3 and
Proposition 5.6.10. On a bipartite Dynkin graph the usual signed mesh
relations have the same zero sets as the displayed all-plus relations.

This module proves evaluation of the abstract relations. It does not
assume their vanishing for coefficient maps of the target paper's
complexes, nor assume any stabilizer or bounded-height conclusion.
-/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) [Fintype A]

/-- Evaluation of one abstract path identity into an arbitrary complex algebra. -/
theorem mesh_word_evaluate {U : Set V}
    {R : Type*} [Ring R] [Algebra ℂ R] (B : A → R)
    (houtside : ∀ a, Q.source a ∉ U ∨ Q.target a ∉ U → B a = 0)
    (hpath : ∀ a b, Q.target a ≠ Q.source b → B a * B b = 0)
    (hmesh : ∀ v ∈ U, (∑ a, if Q.source a = v then B a * B (Q.reverse a) else 0) = 0)
    (w : List A) (hw : (w.map (FreeAlgebra.ι ℂ)).prod ∈
      TwoSidedIdeal.span (meshRelations Q U)) : (w.map B).prod = 0 := by
  let φ : FreeAlgebra ℂ A →ₐ[ℂ] R := FreeAlgebra.lift ℂ B
  have hk : TwoSidedIdeal.span (meshRelations Q U) ≤ TwoSidedIdeal.ker φ.toRingHom := by
    apply TwoSidedIdeal.span_le.mpr
    intro z hz
    change φ z = φ 0
    rw [map_zero]
    rcases hz with (⟨a, ha, rfl⟩ | ⟨a, b, hab, rfl⟩) | ⟨v, hv, rfl⟩
    · simpa only [φ, FreeAlgebra.lift_ι_apply] using houtside a ha
    · simpa only [map_mul, φ, FreeAlgebra.lift_ι_apply] using hpath a b hab
    · simp only [meshRelation, map_sum]
      convert hmesh v hv using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro a _
      split_ifs
      · simp only [map_mul, φ, FreeAlgebra.lift_ι_apply]
      · exact map_zero φ
  have he : φ (w.map (FreeAlgebra.ι ℂ)).prod = φ 0 := hk hw
  rw [map_zero] at he
  simpa only [map_list_prod, List.map_map, Function.comp_def, φ, FreeAlgebra.lift_ι_apply] using he

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_CoefficientPaths
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The path-algebra relations satisfied by actual minimal differentials. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A)
  [Fintype V] [Fintype A]
  {I : Type} [Fintype I]

omit [Fintype V] in
lemma differential_arrow_left_support (E : BasedComplex Q (K := ℂ) I) (i j : I) (a : A)
    (h : (E.placement i).color ≠ Q.source a) : (E.differential i j).arrow a = 0 := by
  have hh := congrArg (fun z : Q.Zigzag ℂ => z.arrow a) (E.entries.1 i j)
  simpa only [arrow_mul, Pi.add_apply, leftScale, rightScale, arrow_vertexId, Pi.zero_apply,
    MulZeroClass.zero_mul, add_zero, vertexId_eval, ite_eq_right h.symm,
    MulZeroClass.zero_mul] using hh.symm

omit [Fintype V] in
lemma arrowMatrix_noncomposable (E : BasedComplex Q (K := ℂ) I) (a b : A)
    (hab : Q.target a ≠ Q.source b) : arrowMatrix Q E a * arrowMatrix Q E b = 0 := by
  ext i j
  apply Finset.sum_eq_zero
  intro k _
  change (E.differential i k).arrow a * (E.differential k j).arrow b = 0
  by_cases hk : (E.placement k).color = Q.target a
  · rw [differential_arrow_left_support Q E k j b (by rwa [hk]), MulZeroClass.mul_zero]
  · rw [differential_arrow_right_support Q E i k a hk, MulZeroClass.zero_mul]

omit [Fintype V] in
lemma arrowMatrix_outside (E : BasedComplex Q (K := ℂ) I) (U : Set V)
    (hU : ∀ i, (E.placement i).color ∈ U) (a : A)
    (ha : Q.source a ∉ U ∨ Q.target a ∉ U) : arrowMatrix Q E a = 0 := by
  ext i j
  rcases ha with ha | ha
  · exact differential_arrow_left_support Q E i j a (fun he => ha (he ▸ hU i))
  · exact differential_arrow_right_support Q E i j a (fun he => ha (he ▸ hU j))

omit [Fintype V] in
/-- The mesh relation is precisely the token coefficient of `d²=0`;
minimality eliminates the other two terms in that coefficient. -/
lemma arrowMatrix_mesh (E : BasedComplex Q (K := ℂ) I) (hE : E.IsMinimal Q) (v : V) :
    (∑ a, if Q.source a = v then arrowMatrix Q E a * arrowMatrix Q E (Q.reverse a) else 0) = 0 := by
  ext i j
  have hs := congrArg (fun D : Matrix I I (Q.Zigzag ℂ) => (D i j).token v) E.square_zero
  have hv (i j : I) : (E.differential i j).vertex v = 0 := congrFun (hE i j) v
  simp only [Matrix.mul_apply, token_sum, Finset.sum_apply, token_mul, Pi.add_apply,
    Pi.mul_apply, hv, MulZeroClass.zero_mul, MulZeroClass.mul_zero, zero_add, backtrack,
    Matrix.zero_apply, token_zero, Pi.zero_apply] at hs
  have hentry (a : A) :
      (if Q.source a = v then arrowMatrix Q E a * arrowMatrix Q E (Q.reverse a) else 0) i j =
      if Q.source a = v then
        (∑ k, (E.differential i k).arrow a * (E.differential k j).arrow (Q.reverse a)) else 0 := by
    by_cases ha : Q.source a = v
    · simp only [ha, ite_true, if_true, Matrix.mul_apply, arrowMatrix]
    · simp only [ha, ite_false, if_false, Matrix.zero_apply]
  rw [Matrix.sum_apply]
  simp only [hentry, Matrix.zero_apply]
  calc
    _ = ∑ a, ∑ k, if Q.source a = v then
        (E.differential i k).arrow a * (E.differential k j).arrow (Q.reverse a) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp only [Finset.sum_const_zero]
    _ = ∑ k, ∑ a, if Q.source a = v then
        (E.differential i k).arrow a * (E.differential k j).arrow (Q.reverse a) else 0 :=
      Finset.sum_comm
    _ = 0 := hs

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PathImages
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iterated images of the arrow coefficient maps. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {A I : Type} [Fintype I] [DecidableEq I] (B : A → Matrix I I ℂ)

lemma mem_pathImages_zero (x : I → ℂ) : x ∈ pathImages B 0 := by
  apply Submodule.subset_span
  exact ⟨[], rfl, x, Matrix.vecMul_one x⟩

lemma pathImages_step {n : ℕ} {x : I → ℂ} (hx : x ∈ pathImages B n) (a : A) :
    Matrix.vecMul x (B a) ∈ pathImages B (n+1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, y, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨w ++ [a], by simp only [List.length_append, List.length_singleton, hw], y, ?_⟩
    simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
      Matrix.vecMul_vecMul]
  | zero =>
    rw [Matrix.zero_vecMul]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [Matrix.add_vecMul]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [Matrix.smul_vecMul]
    exact Submodule.smul_mem _ c hx

lemma pathImages_eq_bot (n : ℕ)
    (hz : ∀ w : List A, w.length = n → (w.map B).prod = 0) : pathImages B n = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨w, hw, y, rfl⟩
  rw [hz w hw, Matrix.vecMul_zero]
  exact Submodule.zero_mem _

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TokenBoundary
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact vertex tests express a generator through incoming coefficients. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) [Fintype V] [Fintype A]
  {I : Type} [Fintype I]

/-- A boundary for the token of a generator, retaining the precise source
level and cochain support. This is the first step of Lemma 7.3. -/
theorem generator_token_boundary (E : BasedComplex Q (K := ℂ) I) (hE : E.IsMinimal Q)
    (i : I) (hex : ScalarExactAt Q (E.testComplex Q (E.placement i).color)
      (E.placement i).color ((E.placement i).level + 2) (E.placement i).cochain) :
    ∃ y : TestIndex Q E.placement (E.placement i).color → ℂ,
      (∀ u, y u ≠ 0 → (E.placement u.1).cochain = (E.placement i).cochain - 1 ∧
        (E.placement u.1).level + Path.length u.2.val = (E.placement i).level + 1) ∧
      ∀ j : I, (Pi.single i (1 : ℂ) : I → ℂ) j =
        ∑ u, y u * pathCoordinates Q (E.differential u.1 j) (Path.dual Q u.2.val) := by
  let α := (E.placement i).color
  let T := E.testComplex Q α
  let t := generatorTokenTest Q E i
  let x : TestIndex Q E.placement α → ℂ := Pi.single t 1
  have hxs : ScalarSupported Q T ((E.placement i).level+2) (E.placement i).cochain x := by
    intro u hu
    apply Pi.single_eq_of_ne
    intro he
    subst u
    apply hu
    constructor
    · change (E.placement i).cochain + ((E.placement i).internal + 2) =
        (E.placement i).cochain + (E.placement i).internal + 2
      omega
    · rfl
  have hxd : Matrix.vecMul x (T.differential.map (vertexHom Q α)) = 0 := by
    rw [testComplex_vertex_differential Q E α]
    funext u
    change (∑ v, x v * testMatrix Q E.placement E.placement α E.differential v u) = 0
    rw [Finset.sum_eq_single t]
    · exact mul_eq_zero.mpr (Or.inr (test_token_row_zero Q E hE α t u rfl))
    · intro v _ hv
      rw [show x v = 0 from Pi.single_eq_of_ne hv _, MulZeroClass.zero_mul]
    · simp
  obtain ⟨y, hy, hd⟩ := hex x hxs hxd
  refine ⟨y, ?_, ?_⟩
  · intro u hu
    have hh := not_not.mp (fun h => hu (hy u h))
    change (E.placement u.1).cochain + ((E.placement u.1).internal + Path.length u.2.val) =
        (E.placement i).level+2-1 ∧
      (E.placement u.1).cochain = (E.placement i).cochain-1 at hh
    exact ⟨hh.2, by dsimp only [GeneratorPlacement.level] at *; omega⟩
  · intro j
    by_cases hj : (E.placement j).color = α
    · let s : TestIndex Q E.placement α := ⟨j, .inr (.inr α), rfl, hj.symm⟩
      have hh := congrFun hd s
      rw [testComplex_vertex_differential Q E α] at hh
      have he : x s = (Pi.single i (1 : ℂ) : I → ℂ) j := by
        dsimp only [x]
        by_cases hji : j = i
        · subst j
          have hs : s = t := by rfl
          rw [hs]
          simp only [Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hji]
          apply Pi.single_eq_of_ne
          intro he
          exact hji (congrArg (fun z : TestIndex Q E.placement α => z.1) he)
      rw [he] at hh
      rw [← hh]
      apply Finset.sum_congr rfl
      intro u _
      congr 1
      change (pathBasis Q u.2.val * E.differential u.1 j).token α = _
      exact token_path_mul Q u.2 _
    · have hji : j ≠ i := fun he => hj (by subst j; rfl)
      rw [Pi.single_eq_of_ne hji]
      symm
      apply Finset.sum_eq_zero
      intro u _
      have hz : pathCoordinates Q (E.differential u.1 j) (Path.dual Q u.2.val) = 0 := by
        by_contra hn
        have hc := coordinates_corner Q (E.entries.1 u.1 j) (E.entries.2 u.1 j) hn
        have ht : ReversibleQuiver.Path.target Q (Path.dual Q u.2.val) = α := by
          rw [Path.target_dual]
          exact u.2.property.1
        exact hj (hc.2.symm.trans ht)
      rw [hz, MulZeroClass.mul_zero]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_IncomingSpanning
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incoming spanning inside a cochain interval, used to force an empty placement. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) [Fintype V] [Fintype A]
  {I : Type} [Fintype I]

/-- If the next higher layer is absent, exactness expresses every basis
vector through incoming arrows in the same layer. Iterated path images
record this statement without losing possible linear cancellations. -/
theorem incoming_spanning_step (E : BasedComplex Q (K := ℂ) I) (hE : E.IsMinimal Q)
    (l r : ℤ) (i : {i | l ≤ (E.placement i).cochain ∧ (E.placement i).cochain ≤ r})
    (hil : l < (E.placement i).cochain)
    (hex : ScalarExactAt Q (E.testComplex Q (E.placement i).color)
      (E.placement i).color ((E.placement i).level+2) (E.placement i).cochain)
    (hhigher : ∀ j, (E.placement j).cochain = (E.placement i).cochain-1 →
      (E.placement i).level < (E.placement j).level → False)
    (n : ℕ)
    (hprev : ∀ j : {j | l ≤ (E.placement j).cochain ∧ (E.placement j).cochain ≤ r},
      (E.placement j).level = (E.placement i).level →
      (E.placement j).cochain = (E.placement i).cochain-1 →
      Pi.single j (1 : ℂ) ∈ pathImages (arrowMatrix Q (cochainInterval Q E l r)) n) :
    Pi.single i (1 : ℂ) ∈ pathImages (arrowMatrix Q (cochainInterval Q E l r)) (n+1) := by
  let J := {j | l ≤ (E.placement j).cochain ∧ (E.placement j).cochain ≤ r}
  let B := arrowMatrix Q (cochainInterval Q E l r)
  obtain ⟨y, hy, he⟩ := generator_token_boundary Q E hE i.val hex
  let z (u : TestIndex Q E.placement (E.placement i).color) : J → ℂ :=
    fun j => y u * pathCoordinates Q (E.differential u.1 j.val) (Path.dual Q u.2.val)
  have heq : (Pi.single i (1 : ℂ) : J → ℂ) = ∑ u, z u := by
    funext j
    rw [Finset.sum_apply]
    change (Pi.single i (1 : ℂ) : J → ℂ) j = ∑ u, y u * _
    have h := he j.val
    simpa only [Pi.single_apply, Subtype.val_inj] using h
  rw [heq]
  apply Submodule.sum_mem
  intro u _
  by_cases hzero : y u = 0
  · have hz : z u = 0 := by
      ext j
      change y u * _ = 0
      rw [hzero, MulZeroClass.zero_mul]
    rw [hz]
    exact Submodule.zero_mem _
  obtain ⟨hdeg, hlev⟩ := hy u hzero
  rcases hp : u.2.val with v | a | v
  · have hlen : Path.length u.2.val = 0 := by rw [hp]; rfl
    have hh : (E.placement i).level < (E.placement u.1).level := by omega
    exact (hhigher u.1 hdeg hh).elim
  · have hlen : Path.length u.2.val = 1 := by rw [hp]; rfl
    have hu : l ≤ (E.placement u.1).cochain ∧ (E.placement u.1).cochain ≤ r := by
      have hir := i.property.2
      constructor <;> omega
    let j₀ : J := ⟨u.1, hu⟩
    have hj₀ : Pi.single j₀ (1 : ℂ) ∈ pathImages B n := hprev j₀ (by
      change (E.placement u.1).level = (E.placement i).level
      omega) hdeg
    have hz : z u = y u • Matrix.vecMul (Pi.single j₀ (1 : ℂ)) (B (Q.reverse a)) := by
      funext j
      change y u * pathCoordinates Q (E.differential u.1 j.val) (Path.dual Q u.2.val) = _
      rw [hp]
      change y u * (E.differential u.1 j.val).arrow (Q.reverse a) = _
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct, Pi.single_apply,
        ite_mul, _root_.one_mul, MulZeroClass.zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
      rfl
    rw [hz]
    exact Submodule.smul_mem _ _ (pathImages_step B hj₀ (Q.reverse a))
  · have hz : z u = 0 := by
      funext j
      change y u * pathCoordinates Q (E.differential u.1 j.val) (Path.dual Q u.2.val) = 0
      rw [hp]
      change y u * (E.differential u.1 j.val).vertex v = 0
      rw [hE u.1 j.val]
      exact MulZeroClass.mul_zero _
    rw [hz]
    exact Submodule.zero_mem _

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_LayerErasure
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nilpotent coefficient paths remove one layer on a shorter interval. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) [Fintype V] [Fintype A]
  {I : Type} [Fintype I]

theorem one_layer_erasure (U : Set V) (N : ℕ)
    (hwords : ∀ w : List A, w.length = N →
      (w.map (FreeAlgebra.ι ℂ)).prod ∈ TwoSidedIdeal.span (meshRelations Q U))
    (E : BasedComplex Q (K := ℂ) I) (hE : E.IsMinimal Q)
    (l r q : ℤ)
    (hcolors : ∀ i, l ≤ (E.placement i).cochain → (E.placement i).cochain ≤ r →
      (E.placement i).color ∈ U)
    (hex : ∀ α ∈ U, ∀ c, l ≤ c → c ≤ r → ∀ d,
      ScalarExactAt Q (E.testComplex Q α) α d c)
    (hhigher : ∀ i, l ≤ (E.placement i).cochain → (E.placement i).cochain ≤ r →
      q < (E.placement i).level → False) :
    ∀ i, (E.placement i).level = q → l+N ≤ (E.placement i).cochain →
      (E.placement i).cochain ≤ r → False := by
  let J := {i | l ≤ (E.placement i).cochain ∧ (E.placement i).cochain ≤ r}
  let F := cochainInterval Q E l r
  let B := arrowMatrix Q F
  have hF : F.IsMinimal Q := restrict_minimal Q E hE _ _
  have hU : ∀ i, (F.placement i).color ∈ U := fun i => hcolors i i.property.1 i.property.2
  have hnil : ∀ w : List A, w.length = N → (w.map B).prod = 0 := by
    intro w hw
    exact mesh_word_evaluate Q B (arrowMatrix_outside Q F U hU)
      (arrowMatrix_noncomposable Q F) (fun v _ => arrowMatrix_mesh Q F hF v) w (hwords w hw)
  have hbound : ∀ n : ℕ, ∀ i : J, (E.placement i).level = q →
      l+n ≤ (E.placement i).cochain → Pi.single i (1 : ℂ) ∈ pathImages B n := by
    intro n
    induction n with
    | zero => exact fun i _ _ => mem_pathImages_zero B _
    | succ n ih =>
      intro i hi hp
      apply incoming_spanning_step Q E hE l r i (by omega)
      · exact hex _ (hU i) _ i.property.1 i.property.2 _
      · intro j hj hlev
        apply hhigher j
        · omega
        · have := i.property.2; omega
        · rwa [← hi]
      · intro j hj hpj
        apply ih j (hj.trans hi)
        omega
  intro i hi hp hr
  let j : J := ⟨i, by constructor <;> omega⟩
  have hj := hbound N j hi hp
  rw [pathImages_eq_bot B N hnil] at hj
  have hz : (Pi.single j (1 : ℂ) : J → ℂ) = 0 := hj
  have hc := congrFun hz j
  exact one_ne_zero (by simpa only [Pi.single_eq_same, Pi.zero_apply] using hc)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_EmptyPlacement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The empty-placement lemma (Lemma 7.3 of paper 082-03). -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) [Fintype V] [Fintype A]

/-- Exact vertex tests on a spherical interval force a gap after at most
`N` placements per occupied layer. Only the abstract published path
identity is assumed; the layer-removal argument is proved here. -/
theorem empty_placement_of_mesh (U : Set V) (hmesh : MeshNilpotent Q U) :
    ∃ N : ℕ, 0 < N ∧ ∀ (I : Type) [Fintype I] (E : BasedComplex Q (K := ℂ) I),
      E.IsMinimal Q → ∀ l r d₁ d₂ : ℤ, d₁ ≤ d₂ →
      (∀ i, d₁ ≤ (E.placement i).level ∧ (E.placement i).level ≤ d₂) →
      (∀ i, l ≤ (E.placement i).cochain → (E.placement i).cochain ≤ r →
        (E.placement i).color ∈ U) →
      (∀ α ∈ U, ∀ c, l ≤ c → c ≤ r → ∀ d,
        ScalarExactAt Q (E.testComplex Q α) α d c) →
      ∀ i, l+N*(d₂-d₁+1) ≤ (E.placement i).cochain →
        (E.placement i).cochain ≤ r → False := by
  obtain ⟨N, hN, hwords⟩ := hmesh
  refine ⟨N, hN, ?_⟩
  intro I _ E hE l r d₁ d₂ hdd hlevels hcolors hex
  have herase : ∀ n : ℕ, ∀ i, l+(n:ℤ)*N ≤ (E.placement i).cochain →
      (E.placement i).cochain ≤ r → d₂-(n:ℤ) < (E.placement i).level → False := by
    intro n
    induction n with
    | zero =>
      intro i _ _ hi
      have := (hlevels i).2
      simp only [Int.natCast_zero, sub_zero] at hi
      omega
    | succ n ih =>
      intro i hi hir hlev
      by_cases htop : d₂-(n:ℤ) < (E.placement i).level
      · apply ih i _ hir htop
        have : (0 : ℤ) ≤ N := Int.natCast_nonneg N
        push_cast at hi
        nlinarith
      · have heq : (E.placement i).level = d₂-(n:ℤ) := by
          push_cast at hlev
          omega
        apply one_layer_erasure Q U N hwords E hE (l+(n:ℤ)*N) r (d₂-(n:ℤ))
          (fun j hj hjr => hcolors j (by have := Int.natCast_nonneg n; have := Int.natCast_nonneg N; nlinarith) hjr)
          (fun α hα c hc hcr d => hex α hα c
            (by have := Int.natCast_nonneg n; have := Int.natCast_nonneg N; nlinarith) hcr d)
          (fun j hj hjr hhigh => ih j hj hjr hhigh) i heq _ hir
        push_cast at hi
        nlinarith
  let n := (d₂-d₁+1).toNat
  have hn : (n : ℤ) = d₂-d₁+1 := Int.toNat_of_nonneg (by omega)
  intro i hi hir
  apply herase n i _ hir _
  · rw [hn]
    nlinarith
  · rw [hn]
    have := (hlevels i).1
    omega

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
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_SphericalCochain
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary cochain bound in Lemma 7.2 of paper 082-03. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma classTestCochainUpper_positive (hn : ∀ a, Q.source a ≠ Q.target a)
    (x : FiniteHomotopyClass Q (K := K)) (U : Set V) (α : V) (hα : α ∈ U)
    (m : ℤ) (h : ClassTestCochainUpper Q x U m) :
    ClassTestCochainUpper Q (classPositiveTwist Q α x) U m := by
  intro β hβ l c hc
  by_cases he : β = α
  · subst β
    apply (classTestExact_positive_self Q hn x α l c).mpr
    exact h α hα (l-1) (c+1) (by omega)
  · exact classTestExact_positive_other Q x α β he l c
      (h α hα l (c+1) (by omega)) (h β hβ l c hc)

lemma positiveWord_cochain_bounds (hn : ∀ a, Q.source a ≠ Q.target a)
    (w : List V) (x : FiniteHomotopyClass Q (K := K)) (U : Set V)
    (hw : ∀ α ∈ w, α ∈ U) (m : ℤ) (h : ClassTestCochainUpper Q x U m) :
    ClassTestCochainUpper Q (positiveWordAction Q w x) U m ∧
      ∀ α ∈ w, ∀ l c : ℤ, m-1 < c →
        ClassTestExact Q α l c (positiveWordAction Q w x) := by
  induction w with
  | nil => exact ⟨h, fun _ hα => (List.not_mem_nil hα).elim⟩
  | cons α w ih =>
    obtain ⟨hbound, himproved⟩ := ih (fun β hβ => hw β (List.mem_cons_of_mem α hβ))
    refine ⟨classTestCochainUpper_positive Q hn _ U α (hw α (by simp)) m hbound, ?_⟩
    intro β hβ l c hc
    change ClassTestExact Q β l c (classPositiveTwist Q α (positiveWordAction Q w x))
    by_cases he : β = α
    · subst β
      apply (classTestExact_positive_self Q hn _ α l c).mpr
      exact hbound α (hw α (by simp)) (l-1) (c+1) (by omega)
    · apply classTestExact_positive_other Q _ α β he l c
      · exact hbound α (hw α (by simp)) l (c+1) (by omega)
      · exact himproved β ((List.mem_cons.mp hβ).resolve_left he) l c hc

/-- A pass containing every operated vertex lowers the ordinary cochain
bound by one. This is proved from the actual twist test formulas. -/
theorem positiveWord_complete_cochain_drop (hn : ∀ a, Q.source a ≠ Q.target a)
    (w : List V) (x : FiniteHomotopyClass Q (K := K)) (U : Set V)
    (hw : ∀ α, α ∈ w ↔ α ∈ U) (m : ℤ) (h : ClassTestCochainUpper Q x U m) :
    ClassTestCochainUpper Q (positiveWordAction Q w x) U (m-1) := by
  have hh := (positiveWord_cochain_bounds Q hn w x U (fun α hα => (hw α).mp hα) m h).2
  exact fun α hα => hh α ((hw α).mpr hα)

omit [Fintype V] [DecidableEq A] in
lemma scalarExact_of_absent_cochain {I : Type} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K := K) I) (α : V) (l c : ℤ)
    (h : ∀ i, (E.placement i).cochain ≠ c) : ScalarExactAt Q E α l c := by
  intro x hx _
  have hz : x = 0 := by
    funext i
    exact hx i (fun hi => h i hi.2)
  refine ⟨0, fun _ _ => rfl, ?_⟩
  rw [Matrix.zero_vecMul, hz]

/-- Every bounded family admits an ordinary cochain upper bound. -/
theorem classTestCochainUpper_exists (x : FiniteHomotopyClass Q (K := K)) (U : Set V) :
    ∃ m : ℤ, ClassTestCochainUpper Q x U m := by
  induction x using Quotient.inductionOn with
  | _ E =>
    obtain ⟨m, hm⟩ := Finite.bddAbove_range (fun i : E.Index => (E.complex.placement i).cochain)
    refine ⟨m, ?_⟩
    intro α _ l c hc
    change ScalarExactAt Q (E.complex.testComplex Q α) α l c
    apply scalarExact_of_absent_cochain Q
    intro i hi
    have hle := hm (Set.mem_range_self i.1)
    change (E.complex.placement i.1).cochain = c at hi
    omega

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_SphericalGap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The gap contradiction in Proposition 7.4 of paper 082-03. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) [Fintype V] [Fintype A]
  {I : Type} [Fintype I]

/-- A missing cochain placement separates every generator below it from
all generators above it. The actual endomorphism dimension rules out
such a separation for a transported indecomposable projective. -/
lemma no_cochain_gap (E : BasedComplex Q (K := ℂ) I) (hE : E.IsMinimal Q)
    (hd : homDimension Q E E 0 0 ≤ 1) (r : ℤ)
    (hgap : ∀ i, (E.placement i).cochain ≠ r)
    (i j : I) (hi : (E.placement i).cochain < r)
    (hj : r < (E.placement j).cochain) : False := by
  apply no_proper_block Q E hE hd {k | (E.placement k).cochain < r} _ i j hi (not_lt.mpr hj.le)
  intro a b hab
  have hc : (E.placement b).cochain = (E.placement a).cochain+1 := by
    by_contra hn
    exact hab ((E.degree a b).1 hn)
  change (E.placement a).cochain < r ↔ (E.placement b).cochain < r
  have ha := hgap a
  have hb := hgap b
  omega

/-- Once the cochain tests have moved below the fixed exterior and the
path bound forces a gap, all tests vanish. This is the contradiction
used in the bounded-positive-height argument. -/
theorem tests_exact_of_empty_gap (U : Set V) (E : BasedComplex Q (K := ℂ) I)
    (hE : E.IsMinimal Q) (hd : homDimension Q E E 0 0 ≤ 1)
    (l r : ℤ) (hlr : l ≤ r)
    (hgap : ∀ i, (E.placement i).cochain ≠ r)
    (j : I) (hj : r < (E.placement j).cochain)
    (hex : ∀ α ∈ U, ∀ d c, l ≤ c → ScalarExactAt Q (E.testComplex Q α) α d c) :
    ∀ α ∈ U, ∀ d c, ScalarExactAt Q (E.testComplex Q α) α d c := by
  intro α hα d c
  by_cases hc : l ≤ c
  · exact hex α hα d c hc
  · apply scalarExact_of_absent_cochain Q
    intro i hi
    change (E.placement i.1).cochain = c at hi
    exact (no_cochain_gap Q E hE hd r hgap i.1 j (by omega) hj).elim

/-- The quantitative form of Proposition 7.4: with fixed generator-level
bounds and a fixed exterior lower placement, nonzero tests cannot all
move arbitrarily far down in cochain degree. -/
theorem cochain_lower_obstruction_of_mesh (U : Set V) (hmesh : MeshNilpotent Q U) :
    ∃ N : ℕ, 0 < N ∧ ∀ (I : Type) [Fintype I] (E : BasedComplex Q (K := ℂ) I),
      E.IsMinimal Q → homDimension Q E E 0 0 ≤ 1 →
      ∀ d₁ d₂ p : ℤ, d₁ ≤ d₂ →
      (∀ i, d₁ ≤ (E.placement i).level ∧ (E.placement i).level ≤ d₂) →
      (∀ i, (E.placement i).color ∉ U → p ≤ (E.placement i).cochain) →
      (∃ j, p ≤ (E.placement j).cochain) →
      (∀ α ∈ U, ∀ d c, p-1-N*(d₂-d₁+1) ≤ c →
        ScalarExactAt Q (E.testComplex Q α) α d c) →
      ∀ α ∈ U, ∀ d c, ScalarExactAt Q (E.testComplex Q α) α d c := by
  obtain ⟨N, hN, hgap⟩ := empty_placement_of_mesh Q U hmesh
  refine ⟨N, hN, ?_⟩
  intro J _ E hE hd d₁ d₂ p hdd hlevels hout hj hex
  let r := p-1
  let l := r-N*(d₂-d₁+1)
  have hNl : (0 : ℤ) ≤ N*(d₂-d₁+1) := mul_nonneg (Int.natCast_nonneg N) (by omega)
  have hlr : l ≤ r := by dsimp only [l]; omega
  have hempty : ∀ i, (E.placement i).cochain ≠ r := by
    intro i hi
    apply hgap J E hE l r d₁ d₂ hdd hlevels
      (fun k hk hkr => by
        by_contra hn
        have := hout k hn
        dsimp only [r] at hkr
        omega)
      (fun α hα c hc _ d => hex α hα d c hc) i
    · dsimp only [l] at *
      omega
    · omega
  obtain ⟨j, hj⟩ := hj
  apply tests_exact_of_empty_gap Q U E hE hd l r hlr hempty j (by dsimp only [r]; omega)
  exact hex

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_SphericalNoChain
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded total height forbids infinitely many complete positive passes. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) [Fintype V] [Fintype A]
  [DecidableEq V] [DecidableEq A]

lemma positiveWord_generator_exterior (w : List V) (x : FiniteHomotopyClass Q (K := ℂ))
    (U : Set V) (hw : ∀ v ∈ w, v ∈ U) (p : GeneratorPlacement V) (hp : p.color ∉ U) :
    classGeneratorArray Q (positiveWordAction Q w x) p = classGeneratorArray Q x p := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    change classGeneratorArray Q (classPositiveTwist Q v (positiveWordAction Q w x)) p = _
    rw [classPositiveTwist_exterior Q _ v p (fun he => hp (he ▸ hw v (by simp)))]
    exact ih (fun a ha => hw a (List.mem_cons_of_mem v ha))

lemma classPositiveTwist_outside_placement (x : FiniteHomotopyClass Q (K := ℂ))
    (U : Set V) (v : V) (hv : v ∈ U) (P : GeneratorPlacement V → Prop)
    (h : ∀ i, ((minimalClassModel Q x).complex.placement i).color ∉ U →
      P ((minimalClassModel Q x).complex.placement i)) :
    ∀ i, ((minimalClassModel Q (classPositiveTwist Q v x)).complex.placement i).color ∉ U →
      P ((minimalClassModel Q (classPositiveTwist Q v x)).complex.placement i) := by
  let E := minimalClassModel Q x
  let F := E.complex.positiveTwist Q v
  have hx : classOfComplex Q F = classPositiveTwist Q v x := by
    change classPositiveTwist Q v (classOfComplex Q E.complex) = _
    exact congrArg (classPositiveTwist Q v) (minimalClassModel_class Q x)
  rw [← hx]
  apply minimal_bound_transport Q F _ (minimalClassModel_minimal Q _)
    (minimalClassModelEquivalence Q F).symm (fun p => p.color ∉ U → P p)
  intro i hi
  rcases i with i | i
  · exact (hi hv).elim
  · exact h i hi

lemma positiveWord_outside_placement (w : List V) (x : FiniteHomotopyClass Q (K := ℂ))
    (U : Set V) (hw : ∀ v ∈ w, v ∈ U) (P : GeneratorPlacement V → Prop)
    (h : ∀ i, ((minimalClassModel Q x).complex.placement i).color ∉ U →
      P ((minimalClassModel Q x).complex.placement i)) :
    ∀ i, ((minimalClassModel Q (positiveWordAction Q w x)).complex.placement i).color ∉ U →
      P ((minimalClassModel Q (positiveWordAction Q w x)).complex.placement i) := by
  induction w with
  | nil => exact h
  | cons v w ih =>
    exact classPositiveTwist_outside_placement Q _ U v (hw v (by simp)) P
      (ih (fun a ha => hw a (List.mem_cons_of_mem v ha)))

lemma positiveWord_allTests_reflect (hn : ∀ a, Q.source a ≠ Q.target a)
    (w : List V) (x : FiniteHomotopyClass Q (K := ℂ)) (U : Set V)
    (hw : ∀ v ∈ w, v ∈ U)
    (h : ∀ α ∈ U, ∀ l c, ClassTestExact Q α l c (positiveWordAction Q w x)) :
    ∀ α ∈ U, ∀ l c, ClassTestExact Q α l c x := by
  have href : ∀ t, ClassTestUpper Q (positiveWordAction Q w x) U t →
      ClassTestUpper Q x U t := by
    clear h
    intro t
    induction w with
    | nil => exact id
    | cons v w ih =>
      intro ht
      exact ih (fun a ha => hw a (List.mem_cons_of_mem v ha))
        (classPositiveTwist_testUpper_reflect Q hn _ U v (hw v (by simp)) ht)
  intro α hα l c
  exact href (l-1) (fun β hβ k _ d => h β hβ k d) α hα l (by omega) c

omit [Fintype V] [DecidableEq A] in
lemma generatorArray_positive_iff (x : FiniteHomotopyClass Q (K := ℂ))
    (p : GeneratorPlacement V) :
    0 < classGeneratorArray Q x p ↔ ∃ i : (minimalClassModel Q x).Index,
      (minimalClassModel Q x).complex.placement i = p := by
  have he := congrArg (fun a => a p)
    (classGeneratorArray_of_minimal Q (minimalClassModel Q x) (minimalClassModel_minimal Q x))
  rw [minimalClassModel_class Q x] at he
  rw [he, generatorArray_apply]
  change 0 < Nat.card {i : (minimalClassModel Q x).Index //
      (minimalClassModel Q x).complex.placement i = p} ↔ _
  rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff]
  exact nonempty_subtype

/-- Proposition 7.4 for actual positive vertex operations. The only
published input is the abstract mesh-algebra path identity. -/
theorem no_bounded_complete_positive_chain (hn : ∀ a, Q.source a ≠ Q.target a)
    (U : Set V) (hmesh : MeshNilpotent Q U)
    (x : ℕ → FiniteHomotopyClass Q (K := ℂ)) (w : ℕ → List V)
    (hstep : ∀ n, x (n+1) = positiveWordAction Q (w n) (x n))
    (hw : ∀ n v, v ∈ w n ↔ v ∈ U)
    (hdim : classHomDimension Q 0 0 (x 0) (x 0) ≤ 1)
    (hframe : ∃ p : GeneratorPlacement V, p.color ∉ U ∧ 0 < classGeneratorArray Q (x 0) p)
    (hnonzero : ¬ ∀ α ∈ U, ∀ l c, ClassTestExact Q α l c (x 0))
    (t : ℤ) (ht : ∀ n, ClassTestUpper Q (x n) U t) : False := by
  cases Subsingleton.elim (inferInstance : DecidableEq V) (Classical.decEq V)
  cases Subsingleton.elim (inferInstance : DecidableEq A) (Classical.decEq A)
  obtain ⟨frame, hframeU, hframe⟩ := hframe
  obtain ⟨d₁, hd₁⟩ := Finite.bddBelow_range
    (fun i : (minimalClassModel Q (x 0)).Index =>
      ((minimalClassModel Q (x 0)).complex.placement i).level)
  obtain ⟨b, hb⟩ := Finite.bddAbove_range
    (fun i : (minimalClassModel Q (x 0)).Index =>
      ((minimalClassModel Q (x 0)).complex.placement i).level)
  obtain ⟨p, hp⟩ := Finite.bddBelow_range
    (fun i : (minimalClassModel Q (x 0)).Index =>
      ((minimalClassModel Q (x 0)).complex.placement i).cochain)
  obtain ⟨m, hm⟩ := classTestCochainUpper_exists Q (x 0) U
  let d₂ := max b (t-2)
  have hstate : ∀ n,
      ClassLowerBound Q d₁ (x n) ∧ ClassOutsideCap Q (x n) U d₂ ∧
      (∀ i, ((minimalClassModel Q (x n)).complex.placement i).color ∉ U →
        p ≤ ((minimalClassModel Q (x n)).complex.placement i).cochain) ∧
      classGeneratorArray Q (x n) frame = classGeneratorArray Q (x 0) frame ∧
      classHomDimension Q 0 0 (x n) (x n) ≤ 1 ∧
      ClassTestCochainUpper Q (x n) U (m-n) ∧
      ¬ (∀ α ∈ U, ∀ l c, ClassTestExact Q α l c (x n)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun i => hd₁ (Set.mem_range_self i),
        fun i _ => (hb (Set.mem_range_self i)).trans (le_max_left _ _),
        fun i _ => hp (Set.mem_range_self i), rfl, hdim, ?_, hnonzero⟩
      simpa only [Int.natCast_zero, sub_zero] using hm
    | succ n ih =>
      rw [hstep n]
      refine ⟨positiveWord_lower_bound Q _ _ ih.1,
        positiveWord_outside_cap Q _ _ U d₂ (fun a ha => (hw n a).mp ha) ih.2.1,
        positiveWord_outside_placement Q _ _ U (fun a ha => (hw n a).mp ha)
          (fun q => p ≤ q.cochain) ih.2.2.1,
        (positiveWord_generator_exterior Q _ _ U (fun a ha => (hw n a).mp ha)
          frame hframeU).trans ih.2.2.2.1, ?_, ?_, ?_⟩
      · rw [positiveWord_homDimension Q hn]
        exact ih.2.2.2.2.1
      · have hh := positiveWord_complete_cochain_drop Q hn (w n) (x n) U (hw n)
          (m-n) ih.2.2.2.2.2.1
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        push_cast
        ring
      · intro h
        exact ih.2.2.2.2.2.2 (positiveWord_allTests_reflect Q hn _ _ U
          (fun a ha => (hw n a).mp ha) h)
  have hupper (n : ℕ) : ClassUpperBound Q d₂ (x n) := by
    apply classUpperBound_of_test_and_outside Q _ U d₂ _ (hstate n).2.1
    intro α hα l hl c
    exact ht n α hα l (by have := le_max_right b (t-2); dsimp only [d₂] at hl; omega) c
  obtain ⟨j₀, hj₀⟩ := (generatorArray_positive_iff Q (x 0) frame).mp hframe
  have hdd : d₁ ≤ d₂ := (hstate 0).1 j₀ |>.trans (hupper 0 j₀)
  obtain ⟨N, _, hbound⟩ := cochain_lower_obstruction_of_mesh Q U hmesh
  let l := p-1-N*(d₂-d₁+1)
  let n := (m-l+1).toNat
  have hn : m-(n:ℤ) < l := by
    dsimp only [n]
    have : m-l+1 ≤ ((m-l+1).toNat : ℤ) := by omega
    omega
  have hs := hstate n
  apply hs.2.2.2.2.2.2
  rw [← minimalClassModel_class Q (x n)]
  apply hbound _ (minimalClassModel Q (x n)).complex (minimalClassModel_minimal Q (x n))
    (by rw [minimalClassModel_homDimension]; exact hs.2.2.2.2.1) d₁ d₂ p hdd
    (fun i => ⟨hs.1 i, hupper n i⟩) hs.2.2.1
  · obtain ⟨j, hj⟩ := (generatorArray_positive_iff Q (x n) frame).mp
      (by rw [hs.2.2.2.1]; exact hframe)
    refine ⟨j, ?_⟩
    have hext : p ≤ frame.cochain := by
      rw [← hj₀]
      exact hp (Set.mem_range_self j₀)
    rwa [hj]
  · intro α hα d c hc
    have hh := hs.2.2.2.2.2.1 α hα d c (by change l ≤ c at hc; omega)
    rwa [← minimalClassModel_class Q (x n)] at hh

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PointedSphericalNoChain
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded-positive-height obstruction for the actual pointed family. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "diag" => coxeterFusionEdge_diag M
local notation "Q" => fusionQuiver m d hd

/-- Every member is the transport of one indecomposable projective. -/
lemma pointed_endomorphism_dimension_le_one (z : Artin M)
    (hz : z ∈ artinParabolic M {f}ᶜ) (L : PointedLabel M) :
    classHomDimension Q 0 0 (pointedFamily M f z L) (pointedFamily M f z L) ≤ 1 := by
  obtain ⟨u, _, rfl⟩ := artinParabolic_signed_word M {f}ᶜ z hz
  rw [pointedFamily_word]
  rw [fusionOrbit_homDimension m d hd diag]
  exact initial_homDimension_le_one Q (fusionQuiver_no_loops m d hd diag) (.inl f,L) 0 0

/-- An unoperated frame supplies a nonzero exterior generator in each
member, including when its cochain position is not explicitly chosen. -/
lemma pointed_exterior_generator (Y : Set S) (hf : f ∉ Y) (z : Artin M)
    (hz : z ∈ artinParabolic M {f}ᶜ) (L : PointedLabel M) :
    ∃ p : GeneratorPlacement (FusionVertex (V := S⊕Unit) m),
      p.color ∉ fusionColorRegion m (Sum.inl '' Y) ∧
        0 < classGeneratorArray Q (pointedFamily M f z L) p := by
  obtain ⟨u, hu, rfl⟩ := artinParabolic_signed_word M {f}ᶜ z hz
  rw [pointedFamily_word]
  obtain ⟨j, hj, _⟩ := orbit_frame_generator m d hd diag (sourcePacketWord u) (.inl f)
    (by
      intro a ha he
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact hu b hb (Sum.inl.inj he)) L
  refine ⟨(fusionOrbitModel m d hd diag (sourcePacketWord u) (.inl f) L).complex.placement j,
    ?_, (generatorArray_positive_iff Q _ _).mpr ⟨j, rfl⟩⟩
  change ((fusionOrbitModel m d hd diag (sourcePacketWord u) (.inl f) L).complex.placement j).color.1
    ∉ Sum.inl '' Y
  rw [congrArg Prod.fst hj]
  rintro ⟨s, hs, he⟩
  exact hf (Sum.inl.inj he ▸ hs)

/-- Proposition 7.4, with the actual Artin action and complete passes
through the original colors. The mesh hypothesis is the abstract
published finite-Dynkin path input; no categorical obstruction is assumed. -/
theorem pointed_no_bounded_complete_positive_chain (Y : Set S) (hf : f ∉ Y)
    (hmesh : MeshNilpotent Q (fusionColorRegion m (Sum.inl '' Y)))
    (z : ℕ → Artin M) (u : ℕ → List S)
    (hz : z 0 ∈ artinParabolic M {f}ᶜ)
    (hstep : ∀ n, z (n+1) = wordArtin M (u n) * z n)
    (hu : ∀ n s, s ∈ u n ↔ s ∈ Y)
    (L : PointedLabel M)
    (hnonzero : ¬ ∀ α ∈ fusionColorRegion m (Sum.inl '' Y), ∀ l c,
      ClassTestExact Q α l c (pointedFamily M f (z 0) L))
    (t : ℤ) (ht : ∀ n, ClassTestUpper Q (pointedFamily M f (z n) L)
      (fusionColorRegion m (Sum.inl '' Y)) t) : False := by
  apply no_bounded_complete_positive_chain Q (fusionQuiver_no_loops m d hd diag)
    (fusionColorRegion m (Sum.inl '' Y)) hmesh
    (fun n => pointedFamily M f (z n) L)
    (fun n => fusionExpandedWord m ((u n).map (Sum.inl : S → S⊕Unit)))
  · intro n
    rw [hstep n]
    change pointedAction M (wordArtin M (u n)*z n) (pointedInitial M f L) = _
    rw [map_mul, Equiv.Perm.mul_apply]
    exact sourceArtinAction_positiveWord M (u n) _
  · intro n α
    simp only [fusionExpandedWord, List.mem_flatMap, List.mem_map,
      Finset.mem_toList, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, ⟨s, hs, rfl⟩, H, rfl⟩
      exact ⟨s, (hu n s).mp hs, rfl⟩
    · rintro ⟨s, hs, he⟩
      refine ⟨.inl s, ⟨s, (hu n s).mpr hs, rfl⟩, α.2, ?_⟩
      exact Prod.ext he rfl
  · exact pointed_endomorphism_dimension_le_one M f (z 0) hz L
  · exact pointed_exterior_generator M f Y hf (z 0) hz L
  · exact hnonzero
  · exact ht

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PositiveSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support of an element of the actual positive Artin monoid. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable

variable {S : Type} (M : CoxeterMatrix S)

/-- Support inclusion gives a word using only the specified colors. -/
theorem positiveSupport_word_exists (a : PositiveArtin M) (J : Set S)
    (ha : positiveSupport M a ⊆ J) :
    ∃ w : List S, wordPositive M w=a ∧ ∀ s ∈ w, s ∈ J := by
  obtain ⟨w, rfl⟩ := positive_word_surjective M a
  exact ⟨w, rfl, fun s hs => ha ((positiveSupport_word M w).symm ▸ hs)⟩

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ProperPositiveSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-family argument in Lemma 7.6 of paper 082-03. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S)

/-- Common positive extensions preserving a bound, together with the
absence of infinitely many complete passes, give one common proper
support for all permitted continuations of a suitable endpoint. -/
theorem proper_positive_support
    (cancel : ∀ a b c : PositiveArtin M, a*c=b*c → a=b)
    (P : PositiveArtin M → Prop) (hOne : P 1)
    (hcommon : ∀ F : Finset (PositiveArtin M), (∀ a ∈ F, P a) →
      ∃ c, P c ∧ ∀ a ∈ F, ∃ q, c=q*a)
    (hchain : ∀ a b : ℕ → PositiveArtin M, a 0=1 → (∀ n, P (a n)) →
      (∀ n, a (n+1)=b n*a n) → (∀ n, positiveSupport M (b n)=Set.univ) → False) :
    ∃ p, P p ∧ ∃ J : Set S, J ⊂ Set.univ ∧
      ∀ b, P (b*p) → positiveSupport M b ⊆ J := by
  let U (p : PositiveArtin M) : Set S := {s | ∃ b, P (b*p) ∧ s ∈ positiveSupport M b}
  by_contra hgoal
  have hall (p : PositiveArtin M) (hp : P p) : U p=Set.univ := by
    by_contra he
    apply hgoal
    refine ⟨p, hp, U p, lt_of_le_of_ne (Set.subset_univ _) he, ?_⟩
    exact fun b hb s hs => ⟨b, hb, hs⟩
  have hstep (p : PositiveArtin M) (hp : P p) :
      ∃ c b, P c ∧ c=b*p ∧ positiveSupport M b=Set.univ := by
    have hcover (s : S) : ∃ b, P (b*p) ∧ s ∈ positiveSupport M b := by
      have hs : s ∈ U p := by rw [hall p hp]; trivial
      exact hs
    let b : S → PositiveArtin M := fun s => (hcover s).choose
    have hb (s : S) : P (b s*p) ∧ s ∈ positiveSupport M (b s) := (hcover s).choose_spec
    let F : Finset (PositiveArtin M) := insert p (Finset.univ.image (fun s => b s*p))
    obtain ⟨c, hc, hF⟩ := hcommon F (by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hp
      · obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp ha
        exact (hb s).1)
    obtain ⟨q, hq⟩ := hF p (Finset.mem_insert_self _ _)
    refine ⟨c, q, hc, hq, Set.eq_univ_of_forall ?_⟩
    intro s
    obtain ⟨d, hd⟩ := hF (b s*p) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩))
    have he : q=d*b s := cancel q (d*b s) p (hq.symm.trans (hd.trans (mul_assoc _ _ _).symm))
    rw [he, positiveSupport_mul]
    exact Or.inr (hb s).2
  let next (p : {p : PositiveArtin M // P p}) : PositiveArtin M × PositiveArtin M :=
    ((hstep p.val p.property).choose, (hstep p.val p.property).choose_spec.choose)
  have hnext (p : {p : PositiveArtin M // P p}) : P (next p).1 ∧
      (next p).1=(next p).2*p.val ∧ positiveSupport M (next p).2=Set.univ :=
    (hstep p.val p.property).choose_spec.choose_spec
  let a : ℕ → {p : PositiveArtin M // P p} :=
    fun n => Nat.rec ⟨1,hOne⟩ (fun _ p => ⟨(next p).1, (hnext p).1⟩) n
  apply hchain (fun n => (a n).val) (fun n => (next (a n)).2) rfl
    (fun n => (a n).property)
  · intro n
    exact (hnext (a n)).2.1
  · intro n
    exact (hnext (a n)).2.2

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ReducedPositiveExtension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cancelling common atoms in a spherical common left extension. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

omit [LinearOrder S] in
/-- The finite-type fraction theorem gives a common positive extension
whose two positive factors have no common left atom. Choosing the least
sum of positive lengths proves termination of the cancellation process. -/
theorem spherical_reduced_positive_extension (Y : Set S) (hY : IsSpherical M Y)
    (a b : Artin (restrictedMatrix M Y)) :
    ∃ p q : PositiveArtin (restrictedMatrix M Y),
      positiveToArtin _ p*a=positiveToArtin _ q*b ∧
      ∀ s : Y, ¬ (PositivePrefix _ (positiveGenerator _ s) p ∧
        PositivePrefix _ (positiveGenerator _ s) q) := by
  let N := restrictedMatrix M Y
  let f := positiveToArtin N
  obtain ⟨p,q,hpq⟩ := (spherical_positive_monoid_fractions M Y hY (a*b⁻¹)).2
  have he : f p*a=f q*b := by
    have h := congrArg (fun g : Artin N => f p*g*b) hpq
    change f p*(a*b⁻¹)*b=f p*((f p)⁻¹*f q)*b at h
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel,
      mul_one, mul_inv_cancel_left] using h
  let P (n : ℕ) := ∃ p q : PositiveArtin N,
    f p*a=f q*b ∧ positiveDegree N p+positiveDegree N q=n
  have hex : ∃ n, P n := ⟨_,p,q,he,rfl⟩
  obtain ⟨p,q,hpq,hlen⟩ := Nat.find_spec hex
  refine ⟨p,q,hpq,?_⟩
  intro s hcommon
  obtain ⟨p',hp'⟩ := hcommon.1
  obtain ⟨q',hq'⟩ := hcommon.2
  have heq : f p'*a=f q'*b := by
    rw [hp',hq',map_mul,map_mul,mul_assoc,mul_assoc] at hpq
    exact mul_left_cancel hpq
  have hlt : positiveDegree N p'+positiveDegree N q'<Nat.find hex := by
    rw [hp',hq'] at hlen
    dsimp only [N] at hlen ⊢
    simp only [positiveDegree_mul,positiveDegree_generator] at hlen
    omega
  exact Nat.find_min hex hlt ⟨p',q',heq,rfl⟩

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_SphericalCommonExtension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common positive extensions with the actual total test-height bound. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops m (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)

lemma restrictedPointedFamily_word (Y : Set S) (x : Artin M)
    (u : List Y) (a : Artin (restrictedMatrix M Y)) (L : PointedLabel M) :
    restrictedPointedFamily M f Y x (positiveToArtin _ (wordPositive _ u)*a) L =
      positiveWordAction Q
        (fusionExpandedWord m (u.map fun j : Y => (Sum.inl (j:S) : S⊕Unit)))
        (restrictedPointedFamily M f Y x a L) := by
  unfold restrictedPointedFamily pointedFamily
  rw [positiveToArtin_word, map_mul (restrictedArtinHom M Y),
    restrictedArtinHom_word, _root_.mul_assoc]
  rw [map_mul, Equiv.Perm.mul_apply]
  simpa only [pointedAction, List.map_map, Function.comp_def] using
    sourceArtinAction_positiveWord M (u.map Subtype.val)
      (pointedAction M (restrictedArtinHom M Y a*x) (pointedInitial M f L))

private lemma testUpper_eventually (x : FiniteHomotopyClass Q (K := ℂ))
    (U : Set (FusionVertex (V := S⊕Unit) m)) (t : ℤ) :
    ∃ n : ℕ, ClassTestUpper Q x U (t+n) := by
  obtain ⟨b,hb⟩ := Finite.bddAbove_range (fun i : (minimalClassModel Q x).Index =>
    ((minimalClassModel Q x).complex.placement i).level)
  have h := classTestUpper_of_generator_cap Q x b (fun i => hb (Set.mem_range_self i)) U
  refine ⟨(b+2-t).toNat, ?_⟩
  intro α hα l hl c
  apply h α hα l _ c
  have : b+2-t ≤ ((b+2-t).toNat : ℤ) := by omega
  omega

/-- Lemma 7.5: a common positive left extension preserves a common bound
on the total test heights. Only published admissible-folding gcd
preservation is assumed; the top-test argument is proved here. -/
theorem spherical_common_extension (Y : Set S) (hY : IsSpherical M Y)
    (hGcd : PublishedFoldingGcd M Y hY) (x : Artin M)
    (a b : Artin (restrictedMatrix M Y)) (t : ℤ)
    (ha : ∀ L, ClassTestUpper Q (restrictedPointedFamily M f Y x a L)
      (Set.range (unfoldedInclusion M Y)) t)
    (hb : ∀ L, ClassTestUpper Q (restrictedPointedFamily M f Y x b L)
      (Set.range (unfoldedInclusion M Y)) t) :
    ∃ p q : PositiveArtin (restrictedMatrix M Y),
      positiveToArtin _ p*a=positiveToArtin _ q*b ∧
      ∀ L, ClassTestUpper Q
        (restrictedPointedFamily M f Y x (positiveToArtin _ p*a) L)
        (Set.range (unfoldedInclusion M Y)) t := by
  obtain ⟨p,q,he,hdisjoint⟩ := spherical_reduced_positive_extension M Y hY a b
  refine ⟨p,q,he,?_⟩
  intro L
  by_contra hbad
  obtain ⟨u,rfl⟩ := positive_word_surjective _ p
  obtain ⟨v,rfl⟩ := positive_word_surjective _ q
  let z := restrictedPointedFamily M f Y x (positiveToArtin _ (wordPositive _ u)*a) L
  let U := Set.range (unfoldedInclusion M Y)
  obtain ⟨l,hl,hcap,α,hα,c,hnot⟩ := exists_top_test Q z U t
    (testUpper_eventually M z U t) hbad
  have hletters (w : List Y) : ∀ β ∈ fusionExpandedWord m
      (w.map fun j : Y => (Sum.inl (j:S) : S⊕Unit)), β ∈ U := by
    intro β hβ
    have h : β.1 ∈ w.map (fun j : Y => (Sum.inl (j:S) : S⊕Unit)) :=
      fusionExpandedWord_mem m _ β hβ
    obtain ⟨i,_,hi⟩ := List.mem_map.mp h
    exact ⟨(i,β.2), Prod.ext hi rfl⟩
  have hzU : z=positiveWordAction Q
      (fusionExpandedWord m (u.map fun j : Y => (Sum.inl (j:S) : S⊕Unit)))
      (restrictedPointedFamily M f Y x a L) := restrictedPointedFamily_word M f Y x u a L
  have hzV : z=positiveWordAction Q
      (fusionExpandedWord m (v.map fun j : Y => (Sum.inl (j:S) : S⊕Unit)))
      (restrictedPointedFamily M f Y x b L) := by
    change restrictedPointedFamily M f Y x (positiveToArtin _ (wordPositive _ u)*a) L = _
    rw [he]
    exact restrictedPointedFamily_word M f Y x v b L
  obtain ⟨r,hr⟩ := positive_top_divisor Q hn U (unfolded_full_simply_laced M Y hY)
    (restrictedPointedFamily M f Y x a L) t (ha L) _ (hletters u) α hα l hl
    (hzU ▸ hcap) c (hzU ▸ hnot)
  obtain ⟨s,hs⟩ := positive_top_divisor Q hn U (unfolded_full_simply_laced M Y hY)
    (restrictedPointedFamily M f Y x b L) t (hb L) _ (hletters v) α hα l hl
    (hzV ▸ hcap) c (hzV ▸ hnot)
  obtain ⟨i,hi⟩ := hGcd.common_atom u v α r s hr hs
  exact hdisjoint i hi

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_SphericalProperSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveReverse_generator _root_.OAI.HarmonicArtin.positiveReverse_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One proper support controls every bounded-height positive continuation. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

/-- Lemma 7.6 for the actual pointed family. Both conditional inputs
concern published positive-monoid or mesh-algebra results. -/
theorem spherical_proper_positive_support (Y : Set S) (hY : IsSpherical M Y)
    (hf : f ∉ Y) (hGcd : PublishedFoldingGcd M Y hY)
    (hmesh : MeshNilpotent Q (fusionColorRegion m (Sum.inl '' Y)))
    (x : Artin M) (hx : x ∈ artinParabolic M {f}ᶜ) (t : ℤ)
    (ht : ∀ L, ClassTestUpper Q (pointedFamily M f x L)
      (Set.range (unfoldedInclusion M Y)) t)
    (hnonzero : ∃ L, ¬ ∀ α ∈ Set.range (unfoldedInclusion M Y), ∀ l c,
      ClassTestExact Q α l c (pointedFamily M f x L)) :
    ∃ p : PositiveArtin (restrictedMatrix M Y),
      (∀ L, ClassTestUpper Q (restrictedPointedFamily M f Y x (positiveToArtin _ p) L)
        (Set.range (unfoldedInclusion M Y)) t) ∧
      ∃ J : Set Y, J ⊂ Set.univ ∧ ∀ b : PositiveArtin (restrictedMatrix M Y),
        (∀ L, ClassTestUpper Q
          (restrictedPointedFamily M f Y x (positiveToArtin _ (b*p)) L)
          (Set.range (unfoldedInclusion M Y)) t) → positiveSupport _ b ⊆ J := by
  let N := restrictedMatrix M Y
  let fpos := positiveToArtin N
  let P : PositiveArtin N → Prop := fun p => ∀ L,
    ClassTestUpper Q (restrictedPointedFamily M f Y x (fpos p) L)
      (Set.range (unfoldedInclusion M Y)) t
  have hOne : P 1 := by
    simpa only [P, fpos, map_one, restrictedPointedFamily, _root_.one_mul] using ht
  have hpair (a b : PositiveArtin N) (ha : P a) (hb : P b) :
      ∃ c, P c ∧ (∃ p, c=p*a) ∧ ∃ q, c=q*b := by
    obtain ⟨p,q,he,hcap⟩ := spherical_common_extension M f Y hY hGcd x (fpos a) (fpos b) t ha hb
    refine ⟨p*a, ?_, ⟨p,rfl⟩, q, ?_⟩
    · simpa only [P, fpos, map_mul] using hcap
    · apply spherical_positiveToArtin_injective M Y hY
      simpa only [fpos,map_mul] using he
  have hcommon (F : Finset (PositiveArtin N)) (hF : ∀ a ∈ F, P a) :
      ∃ c, P c ∧ ∀ a ∈ F, ∃ q, c=q*a := by
    induction F using Finset.induction_on with
    | empty => exact ⟨1,hOne,by simp⟩
    | @insert a F ha ih =>
      obtain ⟨c,hc,hca⟩ := ih (fun b hb => hF b (Finset.mem_insert_of_mem hb))
      obtain ⟨d,hd,⟨r,hr⟩,s,hs⟩ := hpair c a hc (hF a (Finset.mem_insert_self _ _))
      refine ⟨d,hd,?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ⟨s,hs⟩
      · obtain ⟨q,hq⟩ := hca b hb
        exact ⟨r*q,by rw [hr,hq,_root_.mul_assoc]⟩
  apply proper_positive_support N
    (fun a b c h => spherical_positiveToArtin_injective M Y hY (by
      apply mul_right_cancel (b := fpos c)
      simpa only [map_mul] using congrArg fpos h)) P hOne hcommon
  intro a b ha hPa hab hsupp
  let u (n : ℕ) : List Y := (positive_word_surjective N (b n)).choose
  have hu (n : ℕ) : wordPositive N (u n)=b n := (positive_word_surjective N (b n)).choose_spec
  let z (n : ℕ) := restrictedArtinHom M Y (fpos (a n))*x
  have hz0 : z 0=x := by simp only [z,ha,map_one,_root_.one_mul]
  obtain ⟨L,hL⟩ := hnonzero
  apply pointed_no_bounded_complete_positive_chain M f Y hf hmesh z
    (fun n => (u n).map Subtype.val) (hz0.symm ▸ hx)
  · intro n
    dsimp only [z]
    rw [hab n,map_mul,map_mul,←hu n,positiveToArtin_word,restrictedArtinHom_word,_root_.mul_assoc]
  · intro n s
    constructor
    · intro hs
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hs
      exact i.property
    · intro hs
      refine List.mem_map.mpr ⟨⟨s,hs⟩,?_,rfl⟩
      have hi : (⟨s,hs⟩ : Y) ∈ positiveSupport N (b n) := by rw [hsupp n]; trivial
      rwa [←hu n,positiveSupport_word] at hi
  · simpa only [hz0,←unfoldedInclusion_range M Y] using hL
  · intro n
    simpa only [z,restrictedPointedFamily,unfoldedInclusion_range M Y] using hPa n L

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_SphericalReduction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spherical stabilizer containment, Proposition 7.7 of paper 082-03. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma pointed_testUpper_exists (Y : Set S) (x : Artin M) :
    ∃ t : ℤ, ∀ L, ClassTestUpper Q (pointedFamily M f x L)
      (Set.range (unfoldedInclusion M Y)) t := by
  have heach (L : PointedLabel M) : ∃ t : ℤ,
      ClassTestUpper Q (pointedFamily M f x L) (Set.range (unfoldedInclusion M Y)) t := by
    obtain ⟨b,hb⟩ := Finite.bddAbove_range (fun i : (minimalClassModel Q (pointedFamily M f x L)).Index =>
      ((minimalClassModel Q (pointedFamily M f x L)).complex.placement i).level)
    exact ⟨b+2, classTestUpper_of_generator_cap Q _ b
      (fun i => hb (Set.mem_range_self i)) _⟩
  choose b hb using heach
  obtain ⟨t,ht⟩ := Finite.bddAbove_range b
  refine ⟨t,?_⟩
  intro L α hα l hl c
  exact hb L α hα l (lt_of_le_of_lt (ht (Set.mem_range_self L)) hl) c

omit [Fintype S] [LinearOrder S] in
/-- Support in a subtype becomes the corresponding ambient standard subgroup. -/
lemma positiveSupport_ambient_mem (Y : Set S) (J : Set Y)
    (a : PositiveArtin (restrictedMatrix M Y))
    (ha : positiveSupport _ a ⊆ J) :
    restrictedArtinHom M Y (positiveToArtin _ a) ∈
      artinParabolic M (Subtype.val '' J) := by
  obtain ⟨w,rfl,hw⟩ := positiveSupport_word_exists _ a J ha
  rw [positiveToArtin_word, restrictedArtinHom_word]
  apply wordArtin_mem_parabolic
  intro s hs
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
  exact ⟨i,hw i hi,rfl⟩

/-- The spherical case of the local rank reduction. The positive-height
argument, including its proper-support and containment steps, is proved
here. Only the indicated published categorical and monoid inputs remain. -/
theorem spherical_reduction_s236_oai (Y : Set S) (hY : IsSpherical M Y)
    (hf : f ∉ Y) (hGcd : PublishedFoldingGcd M Y hY)
    (hmesh : MeshNilpotent Q (fusionColorRegion m (Sum.inl '' Y)))
    (hAcyclic : PublishedAcyclicTwist Q)
    (x : Artin M) (hx : x ∈ artinParabolic M {f}ᶜ) :
    ReductionAt M (pointedInitial M f) Y x := by
  rcases Classical.em (∀ L : PointedLabel M, ∀ α ∈ Set.range (unfoldedInclusion M Y),
      ∀ l c : ℤ, ClassTestExact Q α l c (pointedFamily M f x L)) with hExact | hExact
  · apply ReductionAt.fixed
    apply le_antisymm inf_le_left
    intro g hg
    have hfix := pointed_standard_fixes_of_acyclic_tests M f hAcyclic Y x hExact g hg
    change pointedFamily M f (g*x) = pointedFamily M f x at hfix
    refine ⟨hg,?_⟩
    change (fun L => pointedAction M g (pointedAction M x (pointedInitial M f L))) =
      (fun L => pointedAction M x (pointedInitial M f L))
    funext L
    simpa only [pointedFamily,map_mul,Equiv.Perm.mul_apply] using congrFun hfix L
  have hnonzero : ∃ L, ¬ ∀ α ∈ Set.range (unfoldedInclusion M Y), ∀ l c,
      ClassTestExact Q α l c (pointedFamily M f x L) := by
    exact not_forall.mp hExact
  obtain ⟨t,ht⟩ := pointed_testUpper_exists M f Y x
  obtain ⟨p,hp,J,hJ,hcont⟩ :=
    spherical_proper_positive_support M f Y hY hf hGcd hmesh x hx t ht hnonzero
  let N := restrictedMatrix M Y
  let fp := positiveToArtin N
  let F := restrictedArtinHom M Y
  let D : Set S := Subtype.val '' J
  let bp := F (fp p)
  have hDY : D ⊂ Y := by
    refine lt_of_le_of_ne (by rintro s ⟨i,_,rfl⟩; exact i.property) ?_
    intro he
    apply hJ.ne
    apply Set.eq_univ_of_forall
    intro i
    have hi : (i:S) ∈ D := he.symm ▸ i.property
    obtain ⟨j,hj,hji⟩ := hi
    exact Subtype.val_injective hji ▸ hj
  have hbp : bp ∈ artinParabolic M Y := by
    rw [← restrictedArtinHom_range M Y]
    exact ⟨fp p,rfl⟩
  apply ReductionAt.smaller D bp hDY hbp
  intro g hg
  have hfix : pointedFamily M f (g*x)=pointedFamily M f x := by
    have hh := hg.2
    change (fun L => pointedAction M g (pointedAction M x (pointedInitial M f L))) =
      (fun L => pointedAction M x (pointedInitial M f L)) at hh
    funext L
    simpa only [pointedFamily,map_mul,Equiv.Perm.mul_apply] using congrFun hh L
  have hgY := hg.1
  rw [← restrictedArtinHom_range M Y] at hgY
  obtain ⟨a,ha⟩ := hgY
  have hright (z : Artin N) :
      restrictedPointedFamily M f Y x (z*a)=restrictedPointedFamily M f Y x z := by
    funext L
    unfold restrictedPointedFamily pointedFamily
    rw [map_mul F,ha,_root_.mul_assoc,map_mul (pointedAction M),Equiv.Perm.mul_apply,
      map_mul (pointedAction M),Equiv.Perm.mul_apply]
    simpa only [pointedFamily,map_mul,Equiv.Perm.mul_apply] using
      congrArg (pointedAction M (F z)) (congrFun hfix L)
  obtain ⟨r,s,he,hcap⟩ := spherical_common_extension M f Y hY hGcd x (fp p) (fp p*a) t hp
    (by simpa only [hright] using hp)
  have hrJ : positiveSupport N r ⊆ J := hcont r (by simpa only [map_mul] using hcap)
  have hsJ : positiveSupport N s ⊆ J := by
    apply hcont s
    intro L
    have hh := hcap L
    rw [he, ← _root_.mul_assoc, hright] at hh
    simpa only [map_mul] using hh
  have hr := positiveSupport_ambient_mem M Y J r hrJ
  have hs := positiveSupport_ambient_mem M Y J s hsJ
  have heG := congrArg F he
  simp only [map_mul] at heG
  have ha' : F a=g := ha
  rw [ha'] at heG
  rw [mem_conjugate,inv_inv]
  have hrewrite : bp*g*bp⁻¹=(F (fp s))⁻¹*F (fp r) := by
    dsimp only [bp]
    apply (mul_left_cancel_iff (a := F (fp s))).mp
    calc
      F (fp s) * (F (fp p)*g*(F (fp p))⁻¹) =
          (F (fp s)*(F (fp p)*g))*(F (fp p))⁻¹ := by group
      _ = (F (fp r)*F (fp p))*(F (fp p))⁻¹ := by rw [← heG]
      _ = F (fp s)*((F (fp s))⁻¹*F (fp r)) := by group
  rw [hrewrite]
  exact (artinParabolic M D).mul_mem ((artinParabolic M D).inv_mem hs) hr

end HarmonicArtin.ParabolicIntersections

end OAI
end

theorem solution : type_of% @OAI.HarmonicArtin.ParabolicIntersections.spherical_reduction_s236_oai := @OAI.HarmonicArtin.ParabolicIntersections.spherical_reduction_s236_oai
