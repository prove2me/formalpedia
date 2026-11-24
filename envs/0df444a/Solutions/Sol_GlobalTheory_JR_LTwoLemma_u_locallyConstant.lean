-- Prove2me | solution 1 for GlobalTheory.JR.LTwoLemma.u_locallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:01:14.146716+00:00
-- url     : https://prove2.me/submissions/7c30e2ee-4b02-4749-963a-7aca6eaf044c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerBoundBigCellStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHeightSqLintegralLtTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTruncatedFourierTendstoZeroEtaleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerFunctionalWeylVanishOfWeylUnipotentZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KirillovVanishingOfLimit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LTwoLemma
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.LTwoLemma
theorem _root_.solution (A : Et F E) (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ) (h : A.InI Ψ) :
    IsLocallyConstant (fun z => Ψ (wS A.K * nS z)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z
  obtain ⟨U, hU, hinv⟩ := h.1
  have h0 : (0 : A.K) ∈ U := mem_of_mem_nhds hU
  have ht : Tendsto (fun y : A.K => y - z) (𝓝 z) (𝓝 0) :=
    (continuous_sub_right z).tendsto' z 0 (sub_self z)
  filter_upwards [ht hU] with y hy
  simp only [Set.mem_preimage] at hy
  have he : wS A.K * nS y = (wS A.K * nS z) * nS (y - z) := by
    rw [mul_assoc]; congr 1; apply Subtype.ext
    show !![(1 : A.K), y; 0, 1] = !![1, z; 0, 1] * !![1, y - z; 0, 1]
    rw [Matrix.mul_fin_two]; simp
  rw [he]
  apply hinv
  intro i j
  fin_cases i <;> fin_cases j <;> simp [nS, h0, hy]
end GlobalTheory.JR.LTwoLemma
