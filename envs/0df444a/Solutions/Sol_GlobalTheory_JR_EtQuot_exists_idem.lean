-- Prove2me | solution 1 for GlobalTheory.JR.EtQuot.exists_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:58:35.129549+00:00
-- url     : https://prove2.me/submissions/775424d5-0e87-4d47-8d0c-9053cdbf49fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleInvolutiveAlgebraSplittingSmaller

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtQuot
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable (A : Et F E) (e : A.K)
namespace GlobalTheory.JR.EtQuot
theorem _root_.solution (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] [Nontrivial K] (hf : ¬ IsField K) :
    ∃ e : K, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  classical
  obtain ⟨m₁, hm₁⟩ := Ideal.exists_maximal K
  have hex : ∃ m₂ : Ideal K, m₂.IsMaximal ∧ m₂ ≠ m₁ := by
    by_contra h
    push_neg at h
    haveI : IsLocalRing K := IsLocalRing.of_unique_max_ideal ⟨m₁, hm₁, fun y hy => h y hy⟩
    exact hf (IsArtinianRing.isField_of_isReduced_of_isLocalRing K)
  obtain ⟨m₂, hm₂, hne⟩ := hex
  let i : MaximalSpectrum K := ⟨m₁, hm₁⟩
  let j : MaximalSpectrum K := ⟨m₂, hm₂⟩
  have hij : j ≠ i := fun h => hne (congrArg MaximalSpectrum.asIdeal h)
  haveI : i.asIdeal.IsMaximal := hm₁
  haveI : j.asIdeal.IsMaximal := hm₂
  let φ := IsArtinianRing.equivPi K
  refine ⟨φ.symm (Pi.single i 1), ?_, ?_, ?_⟩
  · unfold IsIdempotentElem
    rw [← map_mul, ← Pi.single_mul, mul_one]
  · intro h
    have := congrArg φ h
    simp at this
  · intro h
    have := congrFun (congrArg φ h) j
    simp [Pi.single_apply, hij] at this
end GlobalTheory.JR.EtQuot
