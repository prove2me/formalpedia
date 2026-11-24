-- Prove2me | solution 1 for GlobalTheory.KSp.four_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:06:13.035865+00:00
-- url     : https://prove2.me/submissions/c4034098-95fa-43f0-b6a3-eb7ae64c23ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformTwiceEqPosSmulReflect
import Theorems.Thm_GlobalTheory_KSp_FourInv_exists_invariant
import Theorems.Thm_GlobalTheory_KSp_FourInv_indicator_invariant
import Theorems.Thm_GlobalTheory_KSp_FourInv_indicator_mem
import Theorems.Thm_GlobalTheory_KSp_FourInv_four_four_of_invariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.KSp
open FourInv
namespace GlobalTheory.KSp
theorem _root_.solution (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (hX : Good X)
    (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ) (he : IsPair e) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x) := by
  have := hX.grp
  have := hX.t2
  obtain ⟨M0, hM0c, hM0o, -⟩ := hX.large ∅ isCompact_empty
  obtain ⟨C, hC, hCφ⟩ := four_four_of_invariant μ hX he M0 hM0c hM0o
  refine ⟨C, hC, fun φ hφ x => ?_⟩
  obtain ⟨U, hU, hUinv⟩ := exists_invariant hφ
  obtain ⟨M1, hM1c, hM1o, hM1U⟩ := hX.small U hU
  have hMo : IsOpen ((M1 ⊓ M0 : AddSubgroup X) : Set X) := by
    rw [AddSubgroup.coe_inf]
    exact hM1o.inter hM0o
  have hMc : IsCompact ((M1 ⊓ M0 : AddSubgroup X) : Set X) := by
    rw [AddSubgroup.coe_inf]
    exact hM1c.inter_right (AddSubgroup.isClosed_of_isOpen M0 hM0o)
  obtain ⟨C', -, hC'φ⟩ := four_four_of_invariant μ hX he (M1 ⊓ M0) hMc hMo
  have h0 : (0 : X) ∈ (M0 : Set X) := M0.zero_mem
  have hCC : C' = C := by
    have h1 := hCφ _ (indicator_mem M0 hM0c hM0o) (indicator_invariant M0 1) 0
    have h2 := hC'φ _ (indicator_mem M0 hM0c hM0o)
      (fun t ht => indicator_invariant M0 1 t (AddSubgroup.mem_inf.mp ht).2) 0
    rw [neg_zero, Set.indicator_of_mem h0, mul_one] at h1 h2
    exact_mod_cast h2.symm.trans h1
  rw [← hCC]
  exact hC'φ φ hφ (fun t ht => hUinv M1 hM1U t (AddSubgroup.mem_inf.mp ht).1) x
end GlobalTheory.KSp
