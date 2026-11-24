-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelColumns.vecNorm_of_vecClose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:14:07.107612+00:00
-- url     : https://prove2.me/submissions/5d66f988-ec13-41e0-a149-eed3e08028bf

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VecNormOfVecClose
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelColumns_isVec_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelColumns_tst_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelColumns_exists_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelColumns
namespace GlobalTheory.CompanionTheory.KernelColumns
theorem _root_.solution : VecClose → VecNorm := by
  intro hV X ι _ Φ hΦ
  obtain ⟨ε, hε⟩ := exists_bound X Φ hΦ
  set Ω₀ : Set X.G := ⋃ i, ⋃ j, tsupport (Φ i j) with hΩ₀
  have hc : IsCompact Ω₀ := isCompact_iUnion fun i => isCompact_iUnion fun j => (hΦ i j).2
  have hci : IsCompact Ω₀⁻¹ := hc.inv
  refine ⟨(Fintype.card ι : ℝ≥0∞) * (ENNReal.ofReal ε ^ 2 * X.μ Ω₀⁻¹), Ω₀⁻¹ * Ω₀, ?_,
    hci.mul hc, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hci.measure_lt_top.ne)
  · intro y j k hk
    have h := hV X ι Φ 0 Ω₀ ε y j k 0 hc (fun l => ⟨hΦ l j, tst_zero X, ?_, ?_, ?_⟩) hk
      (isVec_zero X y j)
    · simpa [mul_assoc] using h
    · exact (subset_tsupport _).trans
        (Set.subset_iUnion_of_subset l (Set.subset_iUnion_of_subset j subset_rfl))
    · simp
    · intro z
      simpa using hε l j z
end GlobalTheory.CompanionTheory.KernelColumns
