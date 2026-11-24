-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.Window.ne_zero_of_isPre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:51:54.778487+00:00
-- url     : https://prove2.me/submissions/9264fcef-c2cd-4892-be0e-3fe0a8e41f03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology Classical
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc GlobalTheory.UnitLemma.Desc.Window
variable {K : UQ} (B : InvAlg K) {ι : Type}
namespace GlobalTheory.UnitLemma.Desc.Window
theorem _root_.solution [Fintype ι] {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) (i : ι) : e i ≠ 0 := by
  obtain ⟨f, hf, hf0, -, hS, hnS⟩ := h.2 i
  by_cases hi : i ∈ S
  · rw [(hS hi).1]; exact hf0
  · obtain ⟨h1, h2⟩ := hnS hi
    rw [h2]
    intro hz
    have hs : B.σ f = -f := eq_neg_of_add_eq_zero_right hz
    rw [hs, mul_neg, hf.eq, neg_eq_zero] at h1
    exact hf0 h1
end GlobalTheory.UnitLemma.Desc.Window
