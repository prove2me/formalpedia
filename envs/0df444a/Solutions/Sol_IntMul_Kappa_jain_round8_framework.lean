-- Prove2me | solution 1 for IntMul.Kappa.jain_round8_framework
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:08:25.885828+00:00
-- url     : https://prove2.me/submissions/60d22310-c0a3-400f-904e-d49eba36ebfd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_RG_Defs
import Definitions.Def_IntMul_KappaJainData
import Theorems.Thm_IntMul_Kappa_R6_rG_normalize
import Theorems.Thm_IntMul_Kappa_R6_rat_eps
import Theorems.Thm_IntMul_Kappa_R6_setupNeed6
import Theorems.Thm_IntMul_Kappa_R6_crtNeed6_all
import Theorems.Thm_IntMul_Kappa_R6_kappa_finalG_at
import Theorems.Thm_IntMul_Kappa_R6_Leaf_fineNeed6_all
import Theorems.Thm_IntMul_Kappa_R6_Leaf_lineNeed6_all
import Theorems.Thm_IntMul_Kappa_R6_Leaf_p18IL6_all
import Theorems.Thm_IntMul_Kappa_R8_histMoment_mono_tau
import Theorems.Thm_IntMul_Kappa_R8_bitNetR8_mom
import Theorems.Thm_IntMul_Kappa_R8_cxNetR8G
import Theorems.Thm_IntMul_Kappa_R8_bitNetR7plain_mom
import Theorems.Thm_IntMul_Kappa_R8_bitR8_widths
import Theorems.Thm_IntMul_Kappa_R8_bitR7plain_widths
import Theorems.Thm_IntMul_Kappa_R8_cxR8_p14NeedG
import Theorems.Thm_IntMul_Kappa_R8_cxR8_widths

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

open IntMul IntMul.Kappa IntMul.Kappa.R6 IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Cx
open IntMul.Kappa.R6.IL3H IntMul.Kappa.R6.Leaf IntMul.Kappa.R8 IntMul.Kappa.Jain

private theorem ab_nonneg {aOld aStar ab : ℝ} (hOld : 0 ≤ aOld) (hStar : 0 ≤ aStar)
    (hstop : ab = (1 - 1 / 1000) * aStar + 1 / 1000 * aOld) : 0 ≤ ab := by
  have : 0 ≤ (1 - 1 / 1000 : ℝ) := by norm_num
  have : 0 ≤ (1 / 1000 : ℝ) := by norm_num
  rw [hstop]; nlinarith

private theorem tau_pos {ab : ℝ} (hθ : ab < 1 / 1000) : 0 < 1 - ab := by linarith

private theorem aStar_lt_one {aOld aStar ab : ℝ} (hOld : 0 ≤ aOld) (hStar : 0 ≤ aStar)
    (hstop : ab = (1 - 1 / 1000) * aStar + 1 / 1000 * aOld) (hθ : ab < 1 / 1000) :
    aStar < 1 := by
  have : (1 - 1 / 1000 : ℝ) * aStar ≤ ab := by rw [hstop]; nlinarith
  nlinarith

private theorem aOld_lt_one {aOld aStar ab : ℝ} (hOld : 0 ≤ aOld) (hStar : 0 ≤ aStar)
    (hstop : ab = (1 - 1 / 1000) * aStar + 1 / 1000 * aOld) (hθ : ab < 1 / 1000) :
    aOld < 1 := by
  have : (1 / 1000 : ℝ) * aOld ≤ ab := by rw [hstop]; nlinarith
  nlinarith

/-- If `τ ≤ 0` and every width lies in `(0, m]`, the moment is at least the total bin count. -/
private theorem hist_ge_count {h : List (ℕ × ℕ)} {m : ℕ} {τ : ℝ}
    (hm : 0 < m) (hw : ∀ p ∈ h, 0 < p.1 ∧ p.1 ≤ m) (hτ : τ ≤ 0) :
    ((h.map Prod.snd).sum : ℝ) ≤ histMoment h m τ := by
  unfold histMoment
  induction h with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    have hp : p ∈ p :: ps := by simp
    have hp' := hw p hp
    have hps : ∀ q ∈ ps, 0 < q.1 ∧ q.1 ≤ m := fun q hq => hw q (List.mem_cons_of_mem p hq)
    have ih' := ih hps
    have hr : (1 : ℝ) ≤ ((p.1 : ℝ) / m) ^ τ := by
      have h0 : 0 < (p.1 : ℝ) := by exact_mod_cast hp'.1
      have hle : (p.1 : ℝ) / m ≤ 1 := by
        have : (p.1 : ℝ) ≤ m := by exact_mod_cast hp'.2
        exact (div_le_one (by exact_mod_cast hm)).2 this
      have hpos : 0 < (p.1 : ℝ) / m := div_pos h0 (by exact_mod_cast hm)
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos hle hτ
    have hterm : (p.2 : ℝ) ≤ (p.2 : ℝ) * ((p.1 : ℝ) / m) ^ τ := by
      have : 0 ≤ (p.2 : ℝ) := Nat.cast_nonneg _
      nlinarith
    linarith

/-- `σ = 1 - ac > 0` from the complex moment hyp (at `τ ≤ 0` the moment is ≥ total count ≫ W). -/
private theorem sigma_pos_of_hcx (ac : ℝ)
    (hcx : histMoment cxR8 576 (1 - ac) < 12869228) : 0 < 1 - ac := by
  by_contra hne
  push Not at hne
  have hw : ∀ p ∈ cxR8, 0 < p.1 ∧ p.1 ≤ 576 := by
    intro p hp
    have ⟨h0, h529⟩ := cxR8_widths p hp
    exact ⟨h0, (h529.trans_lt (by norm_num : (529 : ℕ) < 576)).le⟩
  have hge := hist_ge_count (m := 576) (by norm_num) hw hne
  have hsumN : 12869228 ≤ (cxR8.map Prod.snd).sum := by decide
  have hsum : (12869228 : ℝ) ≤ ((cxR8.map Prod.snd).sum : ℝ) := Nat.cast_le.mpr hsumN
  linarith

/-- Sketch reduction of `jain_round8_framework` onto the Proved R6 stack / R8 side lemmas
and the Open network leaves `bitNetR8_mom`, `bitNetR7plain_mom`, `cxNetR8G`, `cxR8_p14NeedG`. -/
theorem solution (aOld aStar ab ac ε x C₁ κ : ℝ)
    (hOld : 0 ≤ aOld) (hStar : 0 ≤ aStar) (hac : 0 ≤ ac)
    (hbitOld : histMoment bitR7plain 529 (1 - aOld) < 104719230)
    (hbit : histMoment bitR8 529 (1 - aStar) < 104719230)
    (hstop : ab = (1 - 1 / 1000) * aStar + 1 / 1000 * aOld)
    (hθ : ab < 1 / 1000)
    (hcx : histMoment cxR8 576 (1 - ac) < 12869228)
    (hasm : CrudeAssembly ab ac (1 / 1000) ε x C₁ κ 576 (histRankSum cxR8)) :
    IntMul.KappaBound κ := by
  have hab0 := ab_nonneg hOld hStar hstop
  have hτpos := tau_pos hθ
  have hσpos := sigma_pos_of_hcx ac hcx
  obtain ⟨P0, hP0, hκ0, hτ0, hσ0, hC10⟩ :=
    rG_normalize 576 (histRankSum cxR8) ab ac ε x C₁ κ hτpos hσpos hab0 hac hasm
  obtain ⟨q, hPq, hκq⟩ := rat_eps P0 hP0 κ hκ0
  set P : Prm := { P0 with ε := (q : ℝ) }
  have hP : P.Ok := hPq
  have hκ : κ < P.gap := hκq
  have hq : ∃ q : ℚ, P.ε = q := ⟨q, rfl⟩
  have hτP : P.τ = 1 - ab := hτ0
  have hσP : P.σ = 1 - ac := hσ0
  have hC1P : 2 + (576 : ℝ) * Real.log (histRankSum cxR8) ≤ P.C1 := hC10
  have hSet := setupNeed6 P hP
  have hCrt := crtNeed6_all P hP
  have hFine := fineNeed6_all P hP
  have hLine := lineNeed6_all P hP
  have hP18 := p18IL6_all P hP
  have hP14 := cxR8_p14NeedG P hP
  have hCx := cxNetR8G
  have hJc : histMoment cxR8 576 P.σ < 12869228 := by rw [hσP]; exact hcx
  cases le_total aOld aStar with
  | inl hAO =>
    have hab_le : ab ≤ aStar := by rw [hstop]; nlinarith
    have hA := aStar_lt_one hOld hStar hstop hθ
    have hτ1 : 0 ≤ (1 - aStar : ℝ) := by linarith
    have hle : (1 - aStar : ℝ) ≤ P.τ := by rw [hτP]; linarith
    have hJb : histMoment bitR8 529 P.τ < 104719230 := by
      have hm := histMoment_mono_tau bitR8 529 (1 - aStar) P.τ (by norm_num)
        bitR8_widths hτ1 hle
      exact lt_of_le_of_lt hm hbit
    exact kappa_finalG_at 104719230 529 12869228 576 bitR8 cxR8 (by norm_num)
      P hP hq κ hκ hSet hCrt hFine hLine hP14 hP18 hJb hJc hC1P bitNetR8_mom hCx
  | inr hSA =>
    have hab_le : ab ≤ aOld := by rw [hstop]; nlinarith
    have hA := aOld_lt_one hOld hStar hstop hθ
    have hτ1 : 0 ≤ (1 - aOld : ℝ) := by linarith
    have hle : (1 - aOld : ℝ) ≤ P.τ := by rw [hτP]; linarith
    have hJb : histMoment bitR7plain 529 P.τ < 104719230 := by
      have hm := histMoment_mono_tau bitR7plain 529 (1 - aOld) P.τ (by norm_num)
        bitR7plain_widths hτ1 hle
      exact lt_of_le_of_lt hm hbitOld
    exact kappa_finalG_at 104719230 529 12869228 576 bitR7plain cxR8 (by norm_num)
      P hP hq κ hκ hSet hCrt hFine hLine hP14 hP18 hJb hJc hC1P bitNetR7plain_mom hCx

end
