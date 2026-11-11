-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFreeLinearized_fredholm_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:54:51.634857+00:00
-- url     : https://prove2.me/submissions/650857a1-5c1a-41a4-a30b-20f28043fe84

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp020
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_completedPrincipal_add_compact_fredholm_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_completedZeroOrder_compact_bp240

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

lemma fredholm_add_finite (D : E →L[ℝ] F) (hD : D.IsFredholm) (Q : E →L[ℝ] F)
    (hQ : Q.toLinearMap.HasFiniteRange) : (D+Q).IsFredholm := by
  obtain ⟨S,hS⟩ := hD.exists_isQuasiInverse
  apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse (v := S)
  apply hS.congr (Setoid.refl _) ?_
  apply LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mpr
  simpa only [ContinuousLinearMap.toLinearMap_add,add_sub_cancel_left] using hQ

lemma fredholm_finite_extension (D : E →L[ℝ] F) (hD : D.IsFredholm) (Q : T →L[ℝ] F) :
    (D.comp (ContinuousLinearMap.snd ℝ T E)+Q.comp (ContinuousLinearMap.fst ℝ T E)).IsFredholm :=
  fredholm_add_finite _ (fredholm_comp _ D fredholm_snd_finite hD) _
    ((LinearMap.HasFiniteRange.of_finite_dom (f := Q.toLinearMap)).comp_right _)


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
section Transport
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
lemma fredholm_from_coordinates (D : X →L[ℝ] Z) (e : Y ≃L[ℝ] X)
    (L : Y →L[ℝ] Z) (he : D.comp e.toContinuousLinearMap=L) (hL : L.IsFredholm) : D.IsFredholm := by
  have hh := fredholm_pre_equiv L hL e.symm
  have h : L.comp e.symm.toContinuousLinearMap=D := by
    rw [←he]
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg D (e.apply_symm_apply x)
  exact h ▸ hh
end Transport

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
lemma freeLinearized_coords :
    (freeLinearized A C hA hC).comp (freeEquiv (E := E) (K := K)).symm.toContinuousLinearMap =
      (markedPrincipal A hA-markedZeroOrder C hC).comp
        (ContinuousLinearMap.snd ℝ E (markedModel (E := E) K)) +
      (-constantZeroOrder C hC).comp (ContinuousLinearMap.fst ℝ E (markedModel (E := E) K)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  apply value_ext
  intro z
  have hp := freePrincipal_value A hA (freeSum (E := E) (K := K) v) z
  have hq := freeZeroOrder_value C hC (freeSum (E := E) (K := K) v) z
  have hs := freeSum_value (E := E) (K := K) v z
  have hd := freeSum_deriv (E := E) (K := K) v z
  have hp' := hp.trans (congrArg (fun L : ℂ →L[ℝ] E => L Complex.I-valueCLM _ A z (L 1)) hd)
  have hq' := hq.trans (congrArg (valueCLM _ C z) hs)
  have hh := congrArg₂ (fun x y : E => x-y) hp' hq'
  apply hh.trans
  change (cDeriv v.2.val z Complex.I-valueCLM _ A z (cDeriv v.2.val z 1))-
    valueCLM _ C z (v.1+cValue v.2.val z) =
    ((cDeriv v.2.val z Complex.I-valueCLM _ A z (cDeriv v.2.val z 1))-
      valueCLM _ C z (cValue v.2.val z)) + -valueCLM _ C z v.1
  rw [map_add]
  abel

lemma freeLinearized_fredholm [FiniteDimensional ℝ E]
    (hP : (markedPrincipal A hA-markedZeroOrder C hC).IsFredholm) :
    (freeLinearized A C hA hC).IsFredholm := by
  let L := (markedPrincipal A hA-markedZeroOrder C hC).comp
    (ContinuousLinearMap.snd ℝ E (markedModel (E := E) K)) +
    (-constantZeroOrder C hC).comp (ContinuousLinearMap.fst ℝ E (markedModel (E := E) K))
  have hf : L.IsFredholm := fredholm_finite_extension _ hP (-constantZeroOrder C hC)
  exact fredholm_from_coordinates (freeLinearized (E := E) (K := K) A C hA hC)
    (freeEquiv (E := E) (K := K)).symm L (freeLinearized_coords (E := E) (K := K) A C hA hC) hf


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
local instance afInst12_r5e42f9_1 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst13
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst15
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst16
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst17
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst18
include hc hK in
lemma completedFreeLinearized_fredholm_bp240_oai : (completedFreeLinearized hJ hstd p q u he).IsFredholm := by
  have hP := (completedPrincipal_add_compact_fredholm_bp240 hJ hc hstd p q u hK he
    (-completedZeroOrder hJ hstd p q u he) (completedZeroOrder_compact_bp240 hJ hstd p q u hK he).neg).1
  have hP' : (completedPrincipal hJ hstd p q u he-completedZeroOrder hJ hstd p q u he).IsFredholm := by
    simpa only [sub_eq_add_neg] using hP
  exact freeLinearized_fredholm (E := Phase n) (K := K) (jetValueCLM _ (completedStructureJet hJ hstd p q u))
    (completedQ hJ hstd p q u) (fun z hz => hstd _ (he z hz))
    (completedQ_zero_outside hJ hstd p q u he) hP'

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFreeLinearized_fredholm_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFreeLinearized_fredholm_bp240_oai
