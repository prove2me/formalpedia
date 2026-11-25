-- Prove2me | solution 1 for GlobalTheory.MinorGerm.jet_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:59:41.238245+00:00
-- url     : https://prove2.me/submissions/8539e433-6563-447c-97e6-127ac4d607aa

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_coeff_kill

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] {σ : Type}
variable {p : σ → Prop} [DecidablePred p]
namespace GlobalTheory.MinorGerm
theorem _root_.solution {α : σ →₀ ℕ} {P : MvPolynomial σ C} {g : MvPowerSeries σ C} (hP : Lead p α P)
    (hg : Low α g) : jetAt0 P g = (mfact α : C) := by
  classical
  obtain ⟨hk, hh, hs⟩ := hP
  obtain ⟨h1, h0⟩ := hg
  have hcoef : MvPolynomial.coeff α P = 1 := by
    rw [← coeff_kill p α hs P, hk, MvPolynomial.coeff_monomial, if_pos rfl]
  unfold jetAt0
  rw [Finset.sum_eq_single α]
  · rw [hcoef, h1]
    ring
  · intro m hm hne
    have hdeg : m.degree = α.degree := by
      by_contra hd
      exact (MvPolynomial.mem_support_iff.1 hm) (hh.coeff_eq_zero hd)
    rw [h0 m hdeg.le hne, mul_zero]
  · intro hα
    exact absurd (MvPolynomial.mem_support_iff.2 (by rw [hcoef]; exact one_ne_zero)) hα
end GlobalTheory.MinorGerm
