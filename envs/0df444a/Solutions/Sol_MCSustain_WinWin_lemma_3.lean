-- Prove2me | solution 1 for MCSustain.WinWin.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T19:57:12.649217+00:00
-- url     : https://prove2.me/submissions/57898def-6c38-4c0b-95c7-e6ea4170e15b

import Mathlib
import Definitions.Def_MCSustain_WinWin_Model

namespace MCSustain.WinWin
namespace SolAux

lemma mu_bounds (P : Params) (hP : P.Standing) : P.mL < P.μ ∧ P.μ < P.mH := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hP
  unfold Params.μ
  constructor <;> nlinarith

lemma beta_gt_one (P : Params) (hP : P.Standing) : 1 < P.β := by
  have := mu_bounds P hP
  have h3 := hP.2.2.1
  unfold Params.β; rw [lt_div_iff₀ h3]; linarith

lemma A_eq (P : Params) (hP : P.Standing) :
    P.c * (P.β - 1 + P.α) / (P.α * P.β) = P.c * (P.β - 1) * (1 - P.α) / (P.α * P.β) + P.c := by
  have hb := beta_gt_one P hP
  have ha := hP.1
  field_simp; ring

lemma t_lamH (P : Params) (hP : P.Standing) :
    P.t * lamH P = P.r - P.c - P.c * (P.β - 1) * (1 - P.α) / (P.α * P.β) := by
  unfold lamH; rw [A_eq P hP]; field_simp [hP.2.2.2.2.1.ne']; ring

lemma t_lamHp (P : Params) (hP : P.Standing) :
    P.t * lamHp P = P.w - P.c * (P.β - 1) * (1 - P.α) / (P.α * P.β) := by
  unfold lamHp; field_simp [hP.2.2.2.2.1.ne']

lemma lamHp_pos (P : Params) (hP : P.Standing) : 0 < lamHp P := by
  have h := t_lamHp P hP
  have ht := hP.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, h11, -⟩ := hP
  have : 0 < P.t * lamHp P := by linarith
  exact pos_of_mul_pos_right this ht.le

lemma lamHp_lt_lamH (P : Params) (hP : P.Standing) : lamHp P < lamH P := by
  have h := t_lamHp P hP
  have h' := t_lamH P hP
  have ht := hP.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, h11, -⟩ := hP
  have : P.t * lamHp P < P.t * lamH P := by linarith
  exact lt_of_mul_lt_mul_left this ht.le

lemma lamH_pos (P : Params) (hP : P.Standing) : 0 < lamH P :=
  (lamHp_pos P hP).trans (lamHp_lt_lamH P hP)


lemma sales_H (P : Params) (hP : P.Standing) (n lam : ℝ) (hlam : 0 ≤ lam) :
    sales P ⟨n, lam, lam * P.mH⟩ = n * lam * P.μ := by
  have h4 := hP.2.2.2.1
  unfold sales E Params.μ
  simp only
  rw [mul_comm P.mH lam, min_self, min_eq_right (by nlinarith)]
  ring

lemma leftover_H (P : Params) (hP : P.Standing) (n lam : ℝ) (hlam : 0 ≤ lam) :
    leftover P ⟨n, lam, lam * P.mH⟩ = n * lam * (P.mH - P.μ) := by
  have h4 := hP.2.2.2.1
  unfold leftover E Params.μ
  simp only
  rw [mul_comm P.mH lam, sub_self, max_self, max_eq_left (by nlinarith)]
  ring

lemma impact_H (P : Params) (hP : P.Standing) (n lam : ℝ) (hlam : 0 ≤ lam) :
    impactMP P ⟨n, lam, lam * P.mH⟩ = P.Es * (n * lam * P.μ) + P.El * (n * lam * (P.mH - P.μ)) := by
  unfold impactMP; rw [sales_H P hP n lam hlam, leftover_H P hP n lam hlam]

lemma impact_Hu (P : Params) (hP : P.Standing) :
    impactMP P (Hu P) = P.Es * (nH P * lamH P * P.μ) + P.El * (nH P * lamH P * (P.mH - P.μ)) :=
  impact_H P hP _ _ (lamH_pos P hP).le

lemma impact_Hup (P : Params) (hP : P.Standing) :
    impactHyb P (Hup P) = P.Es * (nHp P * lamHp P * P.μ) +
      P.El * (nHp P * lamHp P * (P.mH - P.μ)) + P.Es * (P.μ * (1 - nHp P * lamHp P)) := by
  unfold impactHyb
  have := impact_H P hP (nHp P) (lamHp P) (lamHp_pos P hP).le
  unfold Hup nHp at *
  simp only at *
  rw [this]

lemma impact_Hc (P : Params) (hP : P.Standing) :
    impactMP P (Hc P) = P.Es * P.μ + P.El * (P.mH - P.μ) := by
  have hn : 0 < (P.t * P.μ / (4 * P.f)) ^ ((1 : ℝ) / 3) := by
    apply Real.rpow_pos_of_pos
    have := (mu_bounds P hP).1
    have := hP.2.2.1; have := hP.2.2.2.2.1; have := hP.2.2.2.2.2.2.2.1
    have : 0 < P.μ := by linarith
    positivity
  have := impact_H P hP ((P.t * P.μ / (4 * P.f)) ^ ((1 : ℝ) / 3))
    (1 / (P.t * P.μ / (4 * P.f)) ^ ((1 : ℝ) / 3)) (div_nonneg zero_le_one hn.le)
  unfold Hc
  rw [show P.mH / (P.t * P.μ / (4 * P.f)) ^ ((1 : ℝ) / 3) =
    1 / (P.t * P.μ / (4 * P.f)) ^ ((1 : ℝ) / 3) * P.mH by ring, this]
  field_simp

theorem impact_Hup_vs_Hu (P : Params) (hP : P.Standing) :
    impactHyb P (Hup P) - impactMP P (Hu P) =
        P.Es * P.μ * (1 - nH P * lamH P) -
          P.El * (P.mH - P.μ) * (nH P * lamH P - nHp P * lamHp P) ∧
      (impactHyb P (Hup P) < impactMP P (Hu P) ↔ R P < P.El / P.Es) := by
  have hdiff : impactHyb P (Hup P) - impactMP P (Hu P) =
        P.Es * P.μ * (1 - nH P * lamH P) -
          P.El * (P.mH - P.μ) * (nH P * lamH P - nHp P * lamHp P) := by
    rw [impact_Hup P hP, impact_Hu P hP]; ring
  refine ⟨hdiff, ?_⟩
  have hEs : 0 < P.Es := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmu := mu_bounds P hP
  have hD : 0 < nH P * lamH P - nHp P * lamHp P := by
    have h1 := lamHp_pos P hP
    have h2 := lamHp_lt_lamH P hP
    have hf := hP.2.2.2.2.2.2.2.1
    have ht := hP.2.2.2.2.1
    have hmu0 : 0 < P.μ := by linarith [hP.2.2.1]
    unfold nH nHp
    rw [sub_pos, div_mul_eq_mul_div, div_mul_eq_mul_div]
    apply div_lt_div_of_pos_right _ (by positivity)
    have : lamHp P ^ 2 * lamHp P < lamH P ^ 2 * lamH P := by
      have := pow_lt_pow_left₀ h2 h1.le (by norm_num : (3:ℕ) ≠ 0)
      nlinarith
    have hmt : 0 < P.μ * P.t := by positivity
    nlinarith
  have hden : 0 < (P.mH - P.μ) * (nH P * lamH P - nHp P * lamHp P) :=
    mul_pos (by linarith) hD
  constructor
  · intro h
    have h0 : impactHyb P (Hup P) - impactMP P (Hu P) < 0 := by linarith
    rw [hdiff] at h0
    unfold R
    rw [div_lt_div_iff₀ hden hEs]
    nlinarith
  · intro h
    unfold R at h
    rw [div_lt_div_iff₀ hden hEs] at h
    have : impactHyb P (Hup P) - impactMP P (Hu P) < 0 := by rw [hdiff]; nlinarith
    linarith

theorem impact_Hup_lt_Hc (P : Params) (hP : P.Standing) (hf1 : fHp P < P.f)
    (_hf2 : P.f ≤ fH P) :
    impactHyb P (Hup P) < impactMP P (Hc P) := by
  rw [impact_Hup P hP, impact_Hc P hP]
  have hEl : 0 < P.El := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hmu := mu_bounds P hP
  have hf := hP.2.2.2.2.2.2.2.1
  have hlt : nHp P * lamHp P < 1 := by
    unfold nHp; unfold fHp at hf1
    rw [div_mul_eq_mul_div, div_lt_one (by positivity)]
    nlinarith
  have : 0 < P.El * ((P.mH - P.μ) * (1 - nHp P * lamHp P)) :=
    mul_pos hEl (mul_pos (by linarith) (by linarith))
  nlinarith


/-- Newsvendor inequality with the two-point demand. -/
lemma nv_ineq (α p c a b q : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hab : a ≤ b)
    (hc : 0 ≤ c) (hpc : c ≤ p) :
    p * (α * min q b + (1 - α) * min q a) - c * q ≤
      (if c < p * α then p * (α * b + (1 - α) * a) - c * b else p * a - c * a) := by
  rcases le_total q a with h1 | h1
  · rw [min_eq_left h1, min_eq_left (h1.trans hab)]
    split_ifs with h
    · nlinarith
    · nlinarith
  rcases le_total q b with h2 | h2
  · rw [min_eq_left h2, min_eq_right h1]
    split_ifs with h
    · nlinarith
    · nlinarith
  · rw [min_eq_right h2, min_eq_right h1]
    split_ifs with h
    · nlinarith
    · nlinarith

lemma lamT_iff (P : Params) (hP : P.Standing) (lam : ℝ) :
    lam < lamT P ↔ P.c < pMP P lam * P.α := by
  have hα := hP.1
  have ht := hP.2.2.2.2.1
  unfold lamT pMP
  rw [lt_div_iff₀ ht, ← div_lt_iff₀ hα]
  constructor <;> intro h <;> linarith

theorem lemma_1 (P : Params) (hP : P.Standing) (n lam : ℝ) (hn : 0 ≤ n) (hlam : 0 ≤ lam)
    (hlam_le : lam ≤ 1)
    (hprice : P.t * lam ≤ 2 * (P.r - P.c)) (q : ℝ) (hq : 0 ≤ q) :
    profitMP P ⟨n, lam, q⟩ ≤
      profitMP P ⟨n, lam, if lam < lamT P then lam * P.mH else lam * P.mL⟩ := by
  have hα0 := hP.1
  have hα1 := hP.2.1
  have hmL := hP.2.2.1
  have hmH := hP.2.2.2.1
  have hc := hP.2.2.2.2.2.1
  have hpc : P.c ≤ pMP P lam := by unfold pMP; linarith
  have key := nv_ineq P.α (pMP P lam) P.c (P.mL * lam) (P.mH * lam) q hα0 hα1
    (by nlinarith) hc.le hpc
  unfold profitMP sales E
  simp only
  have hiff := lamT_iff P hP lam
  split_ifs at key ⊢ with h1 h2 h2
  · have e2 : min (P.mH * lam) (P.mL * lam) = P.mL * lam := min_eq_right (by nlinarith)
    rw [mul_comm lam P.mH, min_self, e2]
    nlinarith [mul_le_mul_of_nonneg_left key hn]
  · exact absurd (hiff.1 h1) h2
  · exact absurd (hiff.2 h2) h1
  · have e2 : min (P.mL * lam) (P.mH * lam) = P.mL * lam := min_eq_left (by nlinarith)
    rw [mul_comm lam P.mL, min_self, e2]
    nlinarith [mul_le_mul_of_nonneg_left key hn]

theorem lemma_3 (P : Params) (hP : P.Standing) (n lam pMC lamMC : ℝ) (hn : 0 ≤ n)
    (hlam : 0 ≤ lam) (hlam_le : lam ≤ 1)
    (hprice : P.t * lam ≤ 2 * (P.r - P.c)) (q : ℝ) (hq : 0 ≤ q) :
    profitHyb P { n := n, lam := lam, q := q, pMC := pMC, lamMC := lamMC } ≤
      profitHyb P { n := n, lam := lam, q := if lam < lamT P then lam * P.mH else lam * P.mL,
                    pMC := pMC, lamMC := lamMC } := by
  unfold profitHyb
  have := lemma_1 P hP n lam hn hlam hlam_le hprice q hq
  simp only
  linarith

theorem lemma_2 (P : Params) (hP : P.Standing) (y : HybDec) (hy : y.Feasible P) :
    ({ y with pMC := P.r - P.w, lamMC := 1 - y.n * y.lam } : HybDec).Feasible P ∧
      profitHyb P y ≤ profitHyb P { y with pMC := P.r - P.w, lamMC := 1 - y.n * y.lam } := by
  obtain ⟨⟨hn, hl0, hl1, hnl, hq⟩, hmc, hsum, hp⟩ := hy
  have hmu := mu_bounds P hP
  have hmu0 : 0 < P.μ := by linarith [hP.2.2.1]
  have hw := hP.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨⟨⟨hn, hl0, hl1, hnl, hq⟩, by simp; linarith, by simp, fun _ => le_rfl⟩, ?_⟩
  unfold profitHyb
  simp only
  rcases hmc.lt_or_eq with h | h
  · have := hp h
    have h1 : (y.pMC - P.c) * y.lamMC ≤ (P.r - P.w - P.c) * y.lamMC :=
      mul_le_mul_of_nonneg_right (by linarith) hmc
    have h2 : (P.r - P.w - P.c) * y.lamMC ≤ (P.r - P.w - P.c) * (1 - y.n * y.lam) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  · rw [← h]
    have : 0 ≤ (P.r - P.w - P.c) * (1 - y.n * y.lam) := mul_nonneg (by linarith) (by linarith)
    nlinarith

end SolAux
end MCSustain.WinWin

open MCSustain.WinWin in
theorem solution (P : Params) (hP : P.Standing) (n lam pMC lamMC : ℝ) (hn : 0 ≤ n)
    (hlam : 0 ≤ lam) (hlam_le : lam ≤ 1)
    (hprice : P.t * lam ≤ 2 * (P.r - P.c)) (q : ℝ) (hq : 0 ≤ q) :
    profitHyb P { n := n, lam := lam, q := q, pMC := pMC, lamMC := lamMC } ≤
      profitHyb P { n := n, lam := lam, q := if lam < lamT P then lam * P.mH else lam * P.mL,
                    pMC := pMC, lamMC := lamMC } :=
  MCSustain.WinWin.SolAux.lemma_3 P hP n lam pMC lamMC hn hlam hlam_le hprice q hq
