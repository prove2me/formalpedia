-- Prove2me | solution 1 for GlobalTheory.AnArc.exists_norm_theta_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:16.014802+00:00
-- url     : https://prove2.me/submissions/9621136a-0504-41f9-b31b-2c86931597d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_continuous_H
import Theorems.Thm_GlobalTheory_AnArc_H_add_self_re
import Theorems.Thm_GlobalTheory_AnArc_norm_ah

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) :
    ∃ M, 0 ≤ M ∧ ∀ z, ‖th z‖ ≤
      M * Real.exp (j * (Real.pi / 2 * (A.H z z).re) + Real.pi * (A.H (A.ct α) z).re) := by
  set g : (Fin A.gB → ℂ) → ℝ := fun z => j * (Real.pi / 2 * (A.H z z).re) + Real.pi * (A.H (A.ct α) z).re with hg
  have c1 : Continuous fun z => A.H z z := A.continuous_H.comp (continuous_id.prodMk continuous_id)
  have c2 : Continuous fun z => A.H (A.ct α) z := A.continuous_H.comp (continuous_const.prodMk continuous_id)
  have c3 := h.1.continuous
  have hK := IsZLattice.isCompact_range_of_periodic A.abelian₂ (fun z => ‖th z‖ * Real.exp (-g z))
    (by rw [hg]; fun_prop) fun z l hl => by
      have h2 := h.2 ⟨l, hl⟩ z
      simp only at h2
      rw [h2, norm_mul, norm_mul, norm_pow, norm_ah, Complex.norm_exp, ← Real.exp_nat_mul, ← Real.exp_add,
        mul_comm _ ‖th z‖, mul_assoc, ← Real.exp_add]
      congr 2
      simp only [hg, H_add_self_re, A.H_add_right (A.ct α), Complex.add_re, Complex.re_ofReal_mul]
      ring
  obtain ⟨M, hM⟩ := hK.bddAbove
  refine ⟨M, le_trans (by positivity) (hM ⟨0, rfl⟩), fun z => ?_⟩
  have : ‖th z‖ * Real.exp (-g z) ≤ M := hM ⟨z, rfl⟩
  rwa [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)] at this
end GlobalTheory.AnArc
