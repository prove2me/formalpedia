-- Prove2me | solution 1 for GlobalTheory.PlancherelZero.fourB_indicator_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:27:10.404714+00:00
-- url     : https://prove2.me/submissions/0abe9c72-6ba6-4600-926f-d8b18433b7dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTruncatedFourierTendstoZeroEtale

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
open GlobalTheory GlobalTheory.PlancherelZero
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.PlancherelZero
theorem _root_.solution (A : Et F E) (ψ : AddChar F ℂ) (μ : Measure A.K) (u : A.K → ℂ) (c : F)
    (hM : MeasurableSet (box A c)) (y : A.K) :
    fourB μ (A.kerK ψ) ((box A c).indicator u) y = ∫ z in box A c, u z * A.psiK ψ (-((-y) * z)) ∂μ := by
  unfold fourB
  have h : ∀ x, (box A c).indicator u x * A.kerK ψ x y = (box A c).indicator (fun x => u x * A.kerK ψ x y) x :=
    fun x => by by_cases hx : x ∈ box A c <;> simp [hx]
  simp_rw [h]
  rw [integral_indicator hM]
  congr 1; funext z
  rw [Et.kerK, neg_mul, neg_neg, mul_comm z y]
end GlobalTheory.PlancherelZero
