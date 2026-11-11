-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFreePrincipal_fredholm_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:54:52.502177+00:00
-- url     : https://prove2.me/submissions/e877c5ca-e247-4212-b489-32699af99f8e

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp020
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_completedPrincipal_add_compact_fredholm_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FiniteExtensions
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open Set Function
open scoped LinearMap.FiniteRangeSetoid
variable {E F G T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]

lemma fredholm_comp (A : E →L[ℝ] F) (B : F →L[ℝ] G) (hA : A.IsFredholm) (hB : B.IsFredholm) :
    (B.comp A).IsFredholm := by
  obtain ⟨S,hS⟩ := hA.exists_isQuasiInverse
  obtain ⟨U,hU⟩ := hB.exists_isQuasiInverse
  exact ContinuousLinearMap.IsFredholm.of_isQuasiInverse (v := S.comp U) (hS.comp hU)

lemma fredholm_snd_finite : (ContinuousLinearMap.snd ℝ T E).IsFredholm := by
  apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse (v := ContinuousLinearMap.inr ℝ T E)
  constructor
  · change (LinearMap.inr ℝ T E ∘ₗ LinearMap.snd ℝ T E) ≈ LinearMap.id
    apply LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mpr
    have he : (LinearMap.inr ℝ T E ∘ₗ LinearMap.snd ℝ T E)-LinearMap.id =
        -(LinearMap.inl ℝ T E ∘ₗ LinearMap.fst ℝ T E) := by ext x <;> simp
    rw [he]
    exact (LinearMap.HasFiniteRange.of_finite_dom (f := LinearMap.inl ℝ T E)).comp_right _ |>.neg
  · change (LinearMap.snd ℝ T E ∘ₗ LinearMap.inr ℝ T E) ≈ LinearMap.id
    simp


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_CompactFredholmAlternative
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open Set Function

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma fredholm_pre_equiv (L : F →L[ℝ] G) (hL : L.IsFredholm) (e : E ≃L[ℝ] F) :
    (L.comp e.toContinuousLinearMap).IsFredholm := by
  obtain ⟨v,hv⟩ := hL.exists_isQuasiInverse
  apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse
    (v := e.symm.toContinuousLinearMap.comp v)
  exact e.toLinearEquiv.isQuasiInverse.comp hv

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_PointwiseMarkedCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {K : Set ℂ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst11
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst12
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst14
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst16
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst18
variable (A C : HMap ℂ (E →L[ℝ] E))
  (hA : ∀ z ∉ K, valueCLM _ A z = complexI (E := E))
  (hC : ∀ z ∉ K, valueCLM _ C z = 0)

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst13
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst15
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst17
lemma freePrincipal_fredholm [FiniteDimensional ℝ E] (hP : (markedPrincipal A hA).IsFredholm) :
    (freePrincipal A hA).IsFredholm := by
  have hs : (ContinuousLinearMap.snd ℝ E (markedModel (E := E) K)).IsFredholm := fredholm_snd_finite
  have hn : (freeNormalize (E := E) (K := K)).IsFredholm := by
    exact fredholm_pre_equiv (ContinuousLinearMap.snd ℝ E (markedModel (E := E) K))
      hs (freeEquiv (E := E) (K := K))
  exact fredholm_comp (freeNormalize (E := E) (K := K)) (markedPrincipal A hA) hn hP


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FreeLinearization
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HolderCompletion
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst6
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (p q : Phase n) (u : COne ℂ (Phase n))
  {K : Set ℂ} (hK : IsCompact K) (he : ∀ z ∉ K, B < ‖markedCurve p q u z‖)

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst11
local instance afInst12_r316be9_1 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst13
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst15
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst16
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst17
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst18
include hc hK in
lemma completedFreePrincipal_fredholm_bp240_oai : (completedFreePrincipal hJ hstd p q u he).IsFredholm := by
  have hP := (completedPrincipal_add_compact_fredholm_bp240 hJ hc hstd p q u hK he 0 isCompactOperator_zero).1
  have hP' : (completedPrincipal hJ hstd p q u he).IsFredholm := by
    simpa only [add_zero] using hP
  exact freePrincipal_fredholm (E := Phase n) (K := K) (jetValueCLM _ (completedStructureJet hJ hstd p q u))
    (fun z hz => hstd _ (he z hz)) hP'

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFreePrincipal_fredholm_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFreePrincipal_fredholm_bp240_oai
