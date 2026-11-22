-- Prove2me | solution 2 for MasulloRH.single_resolvent_test
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T12:03:14.648714+00:00
-- url     : https://prove2.me/submissions/0020586d-afad-4ea1-ba1e-279fd897148b

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_compensated_resolvent_baseline_pos
import Theorems.Thm_MasulloRH_full_strip_resolvent_norm_summable_at_three
import Theorems.Thm_MasulloRH_high_height_zero_resolvent_re_nonneg
import Theorems.Thm_MasulloRH_low_height_trace_zero_set_empty

set_option autoImplicit false

open MasulloRH Set

private theorem height_ge (ρ : ZetaZerosInTraceStrip (1 / 2)) : 36 ≤ ρ.val.im ^ 2 := by
  by_contra! h
  have hmem : ρ ∈ {r : ZetaZerosInTraceStrip (1 / 2) | |r.val.im| ^ 2 < 36} := by
    change |ρ.val.im| ^ 2 < 36
    simpa only [sq_abs] using h
  rw [low_height_trace_zero_set_empty] at hmem
  exact hmem

-- The positive multiplicity argument and spectral partition are adapted from
-- the original single_resolvent_test solution eaa70854-8b74-41d4-aa64-7fee74546f60.
private theorem multiplicity_pos (ρ : ZetaZerosInTraceStrip (1 / 2)) :
    0 < analyticOrderNatAt riemannZeta ρ.val := by
  have h1 : ρ.val ≠ 1 := fun h => by
    have hr := congrArg Complex.re h
    simp only [Complex.one_re] at hr
    linarith [ρ.prop.2.2.1]
  have hA := analyticOn_riemannZeta
  have htwo : analyticOrderAt riemannZeta 2 = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
  have hfin := hA.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
    (show (2 : ℂ) ∈ ({1} : Set ℂ)ᶜ by norm_num) h1 (htwo ▸ ENat.zero_ne_top)
  apply Nat.pos_of_ne_zero
  unfold analyticOrderNatAt
  exact fun h => (ENat.toNat_eq_zero.mp h).elim
    ((hA _ h1).analyticOrderAt_ne_zero.mpr ρ.prop.1) hfin

private theorem term_re_pos (ρ : ZetaZerosInTraceStrip (1 / 2)) :
    0 < (zeroResolventTerm (1 / 2) 3 ρ).re := by
  let β := ρ.val.re
  let γ := ρ.val.im
  have hreal : (zeroResolventTerm (1 / 2) (3 : ℂ) ρ).re =
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
      ((3 - β) / ((3 - β) ^ 2 + γ ^ 2) -
       (5 / 2 - β) / ((5 / 2 - β) ^ 2 + γ ^ 2)) := by
    simp [zeroResolventTerm, β, γ, Complex.mul_re, Complex.sub_re,
      Complex.inv_re, Complex.normSq_apply, pow_two]
  rw [hreal]
  exact mul_pos (by exact_mod_cast multiplicity_pos ρ)
    (compensated_resolvent_baseline_pos β γ ρ.prop.2.1.le ρ.prop.2.2.1.le (height_ge ρ))

theorem solution (α : ℝ) :
    (regularizedTraceRHS (1 / 2) 3).re ≤ (regularizedTraceRHS α 3).re ↔
      ∀ ρ : ZetaZerosInTraceStrip (1 / 2), |ρ.val.re - 1 / 2| < α := by
  let Z := ZetaZerosInTraceStrip (1 / 2)
  let inside : Set Z := {r | |r.val.re - 1 / 2| < α}
  let f := zeroResolventTerm (1 / 2) 3
  have hf : Summable f := full_strip_resolvent_norm_summable_at_three.of_norm
  let e : ZetaZerosInTraceStrip α ≃ inside :=
    { toFun := fun r => ⟨⟨r.val, r.prop.1, r.prop.2.1, r.prop.2.2.1, abs_lt.mpr
        ⟨by linarith [r.prop.2.1], by linarith [r.prop.2.2.1]⟩⟩, r.prop.2.2.2⟩
      invFun := fun r => ⟨r.val.val, r.val.prop.1, r.val.prop.2.1, r.val.prop.2.2.1, r.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hin := e.tsum_eq (fun r => f r.val)
  have hsplit := hf.tsum_subtype_add_tsum_subtype_compl inside
  rw [← hin] at hsplit
  change regularizedSpectral α 3 + _ = regularizedSpectral (1 / 2) 3 at hsplit
  have hout : Summable (fun r : (insideᶜ : Set Z) => f r.val) := hf.subtype (· ∈ insideᶜ)
  have hh := congrArg Complex.re hsplit
  rw [Complex.add_re, Complex.re_tsum hout] at hh
  simp only [regularizedTraceRHS, Complex.add_re, add_le_add_iff_left]
  constructor
  · intro h r
    by_contra hr
    have hpos := (Complex.hasSum_re hout.hasSum).summable.tsum_pos
      (fun i => high_height_zero_resolvent_re_nonneg i.val (height_ge i.val))
      (⟨r, hr⟩ : (insideᶜ : Set Z)) (term_re_pos r)
    linarith
  · intro h
    have : IsEmpty (insideᶜ : Set Z) := ⟨fun r => r.prop (h r.val)⟩
    rw [tsum_empty, add_zero] at hh
    exact hh.ge
