-- Prove2me | solution 1 for HDXConc.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:38:09.0496+00:00
-- url     : https://prove2.me/submissions/638bd2f4-9565-456f-aece-20196dbc79b9

import Mathlib
import Definitions.Def_HDXConc_IsTopDensity
import Definitions.Def_HDXConc_IsTopLinkExpander
import Definitions.Def_SteurerHDX_IsPure

section
set_option autoImplicit false
namespace HDXConc.Dev.T23Spec
open Finset

variable {V : Type*} [Fintype V]

noncomputable def Dg (w : V → V → ℝ) (v : V) : ℝ := ∑ u, w v u
noncomputable def Tg (w : V → V → ℝ) (g : V → ℝ) (v : V) : ℝ := ∑ u, w v u * g u
noncomputable def Eb (w : V → V → ℝ) (g h : V → ℝ) : ℝ := ∑ u, ∑ v, w u v * g u * h v
noncomputable def Nb (w : V → V → ℝ) (g h : V → ℝ) : ℝ := ∑ v, Dg w v * g v * h v

lemma Dg_nonneg (w : V → V → ℝ) (hnn : ∀ u v, 0 ≤ w u v) (v : V) : 0 ≤ Dg w v :=
  Finset.sum_nonneg fun u _ => hnn v u

lemma w_zero_of_Dg (w : V → V → ℝ) (hnn : ∀ u v, 0 ≤ w u v) {v : V} (h : Dg w v = 0) (u : V) :
    w v u = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun u _ => hnn v u).1 h u (Finset.mem_univ u)

lemma Tg_zero_of_Dg (w : V → V → ℝ) (hnn : ∀ u v, 0 ≤ w u v) {v : V} (h : Dg w v = 0)
    (g : V → ℝ) : Tg w g v = 0 := by
  simp [Tg, w_zero_of_Dg w hnn h]

lemma Eb_eq_sum_T (w : V → V → ℝ) (hsym : ∀ u v, w u v = w v u) (g h : V → ℝ) :
    Eb w g h = ∑ v, Tg w g v * h v := by
  unfold Eb Tg
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [hsym u v]

lemma Eb_comm (w : V → V → ℝ) (hsym : ∀ u v, w u v = w v u) (g h : V → ℝ) :
    Eb w g h = Eb w h g := by
  unfold Eb
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
  rw [hsym u v]; ring

lemma sum_T (w : V → V → ℝ) (hsym : ∀ u v, w u v = w v u) (g : V → ℝ) :
    ∑ v, Tg w g v = ∑ v, Dg w v * g v := by
  unfold Tg Dg
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [hsym v u]

lemma Nb_eq (w : V → V → ℝ) (g : V → ℝ) : Nb w g g = ∑ u, ∑ v, w u v * g u ^ 2 := by
  unfold Nb Dg
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun v _ => by ring

lemma Nb_nonneg (w : V → V → ℝ) (hnn : ∀ u v, 0 ≤ w u v) (g : V → ℝ) : 0 ≤ Nb w g g :=
  Finset.sum_nonneg fun v _ => by
    have := Dg_nonneg w hnn v
    have h2 : 0 ≤ Dg w v * (g v * g v) := mul_nonneg this (mul_self_nonneg _)
    nlinarith

lemma gap_eq (w : V → V → ℝ) (hsym : ∀ u v, w u v = w v u) (g : V → ℝ) :
    ∑ u, ∑ v, w u v * (g u - g v) ^ 2 = 2 * (Nb w g g - Eb w g g) := by
  have h1 : Nb w g g = ∑ u, ∑ v, w u v * g v ^ 2 := by
    rw [Nb_eq, Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
    rw [hsym u v]
  have h3 : ∑ u, ∑ v, w u v * (g u - g v) ^ 2 =
      (∑ u, ∑ v, w u v * g u ^ 2) + (∑ u, ∑ v, w u v * g v ^ 2) - 2 * Eb w g g := by
    unfold Eb
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [← Nb_eq, ← h1] at h3
  linarith

lemma Eb_le_Nb (w : V → V → ℝ) (hsym : ∀ u v, w u v = w v u) (hnn : ∀ u v, 0 ≤ w u v)
    (g : V → ℝ) : Eb w g g ≤ Nb w g g := by
  have h2 : 0 ≤ ∑ u, ∑ v, w u v * (g u - g v) ^ 2 :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (hnn u v) (sq_nonneg _)
  rw [gap_eq w hsym] at h2
  linarith

/-- If `a ε + ε² b ≤ 0` for all `ε`, then `a = 0`. -/
lemma lin_zero (a b : ℝ) (h : ∀ ε : ℝ, 2 * ε * a + ε ^ 2 * b ≤ 0) : a = 0 := by
  by_contra hne
  have hb := abs_nonneg b
  have hp : 0 < |b| + 1 := by linarith
  have key := h (a / (|b| + 1))
  rcases lt_or_gt_of_ne hne with ha | ha
  · have hneg : a / (|b| + 1) < 0 := div_neg_of_neg_of_pos ha hp
    have h3 : a / (|b| + 1) * b ≤ |a / (|b| + 1)| * |b| :=
      (le_abs_self _).trans_eq (abs_mul _ _)
    have h4 : |a / (|b| + 1)| * |b| < |a| := by
      rw [abs_div, abs_of_pos hp]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hp]
      nlinarith [abs_nonneg a, abs_pos.2 hne]
    rw [abs_of_neg ha] at h4
    have h6 : 2 * a + a / (|b| + 1) * b < 0 := by linarith
    nlinarith
  · have hpos : 0 < a / (|b| + 1) := div_pos ha hp
    have h3 : -(|a / (|b| + 1)| * |b|) ≤ a / (|b| + 1) * b := by
      have := neg_abs_le (a / (|b| + 1) * b)
      rwa [abs_mul] at this
    have h4 : |a / (|b| + 1)| * |b| < |a| := by
      rw [abs_div, abs_of_pos hp]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hp]
      nlinarith [abs_nonneg a, abs_pos.2 hne]
    rw [abs_of_pos ha] at h4
    have : 0 < 2 * a + a / (|b| + 1) * b := by linarith
    nlinarith


lemma Nb_smul (w : V → V → ℝ) (c : ℝ) (g : V → ℝ) :
    Nb w (fun v => c * g v) (fun v => c * g v) = c ^ 2 * Nb w g g := by
  unfold Nb; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring

lemma Eb_smul (w : V → V → ℝ) (c : ℝ) (g : V → ℝ) :
    Eb w (fun v => c * g v) (fun v => c * g v) = c ^ 2 * Eb w g g := by
  unfold Eb; rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by ring

lemma Nb_add (w : V → V → ℝ) (ε : ℝ) (g h : V → ℝ) :
    Nb w (fun v => g v + ε * h v) (fun v => g v + ε * h v) =
      Nb w g g + 2 * ε * Nb w g h + ε ^ 2 * Nb w h h := by
  unfold Nb
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => by ring

lemma Eb_add (w : V → V → ℝ) (ε : ℝ) (g h : V → ℝ) :
    Eb w (fun v => g v + ε * h v) (fun v => g v + ε * h v) =
      Eb w g g + ε * (Eb w g h + Eb w h g) + ε ^ 2 * Eb w h h := by
  unfold Eb
  have key : ∀ u v, w u v * (g u + ε * h u) * (g v + ε * h v) =
      (w u v * g u * g v) + ε * (w u v * g u * h v + w u v * h u * g v) +
        ε ^ 2 * (w u v * h u * h v) := fun u v => by ring
  simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum]

noncomputable def rr (w : V → V → ℝ) (v : V) : ℝ := if Dg w v = 0 then 0 else 1 + 1 / Dg w v

def Kset (w : V → V → ℝ) : Set (V → ℝ) :=
  ((Set.pi Set.univ fun v => Set.Icc (-rr w v) (rr w v)) ∩ {g | ∑ v, Dg w v * g v = 0}) ∩
    {g | Nb w g g = 1}

lemma Kset_compact (w : V → V → ℝ) : IsCompact (Kset w) := by
  have h1 : IsCompact (Set.pi Set.univ fun v => Set.Icc (-rr w v) (rr w v)) :=
    isCompact_univ_pi fun v => isCompact_Icc
  have h2 : IsClosed {g : V → ℝ | ∑ v, Dg w v * g v = 0} :=
    isClosed_eq (continuous_finsetSum _ fun v _ => continuous_const.mul (continuous_apply v))
      continuous_const
  have h3 : IsClosed {g : V → ℝ | Nb w g g = 1} := by
    refine isClosed_eq ?_ continuous_const
    unfold Nb
    exact continuous_finsetSum _ fun v _ =>
      (continuous_const.mul (continuous_apply v)).mul (continuous_apply v)
  exact (h1.inter_right h2).inter_right h3

lemma normalize (w : V → V → ℝ) (hnn : ∀ u v, 0 ≤ w u v) (g : V → ℝ)
    (hg0 : ∀ v, Dg w v = 0 → g v = 0) (hH : ∑ v, Dg w v * g v = 0) (hN : 0 < Nb w g g) :
    ∃ g' ∈ Kset w, Eb w g' g' * Nb w g g = Eb w g g := by
  set c := (Real.sqrt (Nb w g g))⁻¹ with hc
  have hc2 : c ^ 2 * Nb w g g = 1 := by
    rw [hc, inv_pow, Real.sq_sqrt hN.le]; exact inv_mul_cancel₀ hN.ne'
  have hN1 : Nb w (fun v => c * g v) (fun v => c * g v) = 1 := by rw [Nb_smul, hc2]
  refine ⟨fun v => c * g v, ⟨⟨?_, ?_⟩, hN1⟩, ?_⟩
  · intro v _
    simp only [rr, Set.mem_Icc]
    by_cases hD : Dg w v = 0
    · simp [hD, hg0 v hD]
    · simp only [hD, if_false]
      have hpos : 0 < Dg w v := lt_of_le_of_ne (Dg_nonneg w hnn v) (Ne.symm hD)
      have h1 : Dg w v * (c * g v) * (c * g v) ≤ 1 := by
        rw [← hN1]; unfold Nb
        exact Finset.single_le_sum
          (f := fun v => Dg w v * (c * g v) * (c * g v))
          (fun i _ => by
            have h := Dg_nonneg w hnn i
            have := mul_self_nonneg (c * g i)
            nlinarith) (Finset.mem_univ v)
      have h2 : (c * g v) ^ 2 ≤ 1 / Dg w v := by
        rw [le_div_iff₀ hpos]; nlinarith
      have h3 : |c * g v| ≤ 1 + 1 / Dg w v := by
        have : |c * g v| ≤ 1 + (c * g v) ^ 2 := by
          nlinarith [sq_abs (c * g v), abs_nonneg (c * g v), sq_nonneg (|c * g v| - 1)]
        linarith
      have h4 := abs_le.1 h3
      exact ⟨by linarith [h4.1], h4.2⟩
  · show ∑ v, Dg w v * (c * g v) = 0
    have : ∑ v, Dg w v * (c * g v) = c * ∑ v, Dg w v * g v := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
    rw [this, hH, mul_zero]
  · rw [Eb_smul, mul_assoc, mul_comm (Eb w g g), ← mul_assoc, hc2, one_mul]


theorem spectral (w : V → V → ℝ) (hsym : ∀ u v, w u v = w v u) (hnn : ∀ u v, 0 ≤ w u v)
    {lam : ℝ} (hlam : lam < 1)
    (hconn : ∀ g : V → ℝ, ∑ v, Dg w v * g v = 0 → Nb w g g ≠ 0 → Eb w g g < Nb w g g)
    (hq : ∀ g : V → ℝ, ∑ v, Dg w v * g v = 0 →
      Eb w g g ≤ (1 - lam) * ∑ v, (Tg w g v) ^ 2 / Dg w v + lam * Nb w g g) :
    ∀ g : V → ℝ, ∑ v, Dg w v * g v = 0 → Eb w g g ≤ lam / (1 - lam) * Nb w g g := by
  intro g1 hg1
  by_contra hcon
  rw [not_le] at hcon
  have h1l : 0 < 1 - lam := by linarith
  set gt : V → ℝ := fun v => if Dg w v = 0 then 0 else g1 v with hgt
  have hgt0 : ∀ v, Dg w v = 0 → gt v = 0 := fun v hv => by simp [hgt, hv]
  have hsumt : ∑ v, Dg w v * gt v = 0 := by
    rw [← hg1]; refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : Dg w v = 0 <;> simp [hgt, hv]
  have hNt : Nb w gt gt = Nb w g1 g1 := by
    unfold Nb; refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : Dg w v = 0 <;> simp [hgt, hv]
  have hEt : Eb w gt gt = Eb w g1 g1 := by
    unfold Eb; refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    by_cases hu : Dg w u = 0
    · simp [w_zero_of_Dg w hnn hu]
    · by_cases hv : Dg w v = 0
      · have : w u v = 0 := by rw [hsym]; exact w_zero_of_Dg w hnn hv u
        simp [this]
      · simp [hgt, hu, hv]
  have hcon' : lam / (1 - lam) * Nb w gt gt < Eb w gt gt := by rw [hNt, hEt]; exact hcon
  have hNpos : 0 < Nb w gt gt := by
    rcases (Nb_nonneg w hnn gt).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : Nb w gt gt = 0 := h.symm
      have := Eb_le_Nb w hsym hnn gt
      rw [h0] at this hcon'
      linarith
  obtain ⟨g2, hg2K, hg2E⟩ := normalize w hnn gt hgt0 hsumt hNpos
  have hKne : (Kset w).Nonempty := ⟨g2, hg2K⟩
  have hcont : Continuous fun g : V → ℝ => Eb w g g := by
    unfold Eb
    exact continuous_finsetSum _ fun u _ => continuous_finsetSum _ fun v _ =>
      ((continuous_const.mul (continuous_apply u))).mul (continuous_apply v)
  obtain ⟨g0, hg0K, hmax⟩ := (Kset_compact w).exists_isMaxOn hKne hcont.continuousOn
  obtain ⟨⟨hbox, hsum0⟩, hN0⟩ := hg0K
  have hsum0' : ∑ v, Dg w v * g0 v = 0 := hsum0
  have hN0' : Nb w g0 g0 = 1 := hN0
  have hg0z : ∀ v, Dg w v = 0 → g0 v = 0 := by
    intro v hv
    have := hbox v (Set.mem_univ v)
    simp only [rr, hv, if_true, neg_zero, Set.mem_Icc] at this
    exact le_antisymm this.2 this.1
  set μ := Eb w g0 g0 with hμ
  have hμ1 : μ < 1 := by
    have := hconn g0 hsum0' (by rw [hN0']; norm_num)
    rw [hN0'] at this; exact this
  have hμgt : lam / (1 - lam) < μ := by
    have h2 : Eb w g2 g2 ≤ μ := hmax hg2K
    have h3 : lam / (1 - lam) * Nb w gt gt < Eb w g2 g2 * Nb w gt gt := by
      rw [hg2E]; exact hcon'
    have := lt_of_mul_lt_mul_right h3 hNpos.le
    linarith
  have hA : ∀ g : V → ℝ, (∀ v, Dg w v = 0 → g v = 0) → ∑ v, Dg w v * g v = 0 →
      Eb w g g ≤ μ * Nb w g g := by
    intro g hz hs
    rcases (Nb_nonneg w hnn g).lt_or_eq with hN | hN
    · obtain ⟨g', hg'K, hg'E⟩ := normalize w hnn g hz hs hN
      have := hmax hg'K
      rw [← hg'E]
      exact mul_le_mul_of_nonneg_right this hN.le
    · have h0 : Nb w g g = 0 := hN.symm
      have := Eb_le_Nb w hsym hnn g
      rw [h0] at this ⊢
      linarith
  have hTD : ∀ v, Dg w v * (Tg w g0 v / Dg w v) = Tg w g0 v := by
    intro v
    by_cases hD : Dg w v = 0
    · simp [hD, Tg_zero_of_Dg w hnn hD]
    · exact mul_div_cancel₀ _ hD
  set hh : V → ℝ := fun v => Tg w g0 v / Dg w v - μ * g0 v with hhh
  have hhz : ∀ v, Dg w v = 0 → hh v = 0 := by
    intro v hv; simp [hhh, hv, hg0z v hv]
  have hDh : ∀ v, Dg w v * hh v = Tg w g0 v - μ * (Dg w v * g0 v) := by
    intro v; simp only [hhh]; rw [mul_sub, hTD]; ring
  have hhsum : ∑ v, Dg w v * hh v = 0 := by
    rw [Finset.sum_congr rfl fun v _ => hDh v, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_T w hsym, hsum0']
    ring
  have ha : Eb w g0 hh - μ * Nb w g0 hh = Nb w hh hh := by
    rw [Eb_eq_sum_T w hsym]
    unfold Nb
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    have := hDh v
    have h5 : Tg w g0 v = Dg w v * (hh v + μ * g0 v) := by
      simp only [hhh]
      rw [sub_add_cancel, hTD]
    rw [h5]; ring
  have hzero : Eb w g0 hh - μ * Nb w g0 hh = 0 := by
    apply lin_zero _ (Eb w hh hh - μ * Nb w hh hh)
    intro ε
    have h1 := hA (fun v => g0 v + ε * hh v)
      (fun v hv => by simp [hg0z v hv, hhz v hv])
      (by
        have : ∑ v, Dg w v * (g0 v + ε * hh v) =
            ∑ v, Dg w v * g0 v + ε * ∑ v, Dg w v * hh v := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun v _ => by ring
        rw [this, hsum0', hhsum]; ring)
    rw [Eb_add, Nb_add, hN0', Eb_comm w hsym hh g0] at h1
    have h2 : Eb w g0 g0 = μ := rfl
    nlinarith [h1]
  have hNh : Nb w hh hh = 0 := by rw [← ha]; exact hzero
  have hh0 : ∀ v, hh v = 0 := by
    intro v
    by_cases hD : Dg w v = 0
    · exact hhz v hD
    · have := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => by
        have h := Dg_nonneg w hnn v
        have := mul_self_nonneg (hh v)
        nlinarith : ∀ i ∈ (Finset.univ : Finset V), 0 ≤ Dg w i * hh i * hh i)).1 hNh v
        (Finset.mem_univ v)
      have hpos : Dg w v ≠ 0 := hD
      have := mul_eq_zero.1 this
      rcases this with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h hpos
        · exact h
      · exact h
  have hT : ∀ v, Tg w g0 v = μ * Dg w v * g0 v := by
    intro v
    by_cases hD : Dg w v = 0
    · simp [hD, Tg_zero_of_Dg w hnn hD]
    · have h := hh0 v
      simp only [hhh] at h
      have : Tg w g0 v / Dg w v = μ * g0 v := by linarith
      rw [div_eq_iff hD] at this
      rw [this]; ring
  have hP2 : ∑ v, (Tg w g0 v) ^ 2 / Dg w v = μ ^ 2 := by
    have : ∑ v, (Tg w g0 v) ^ 2 / Dg w v = μ ^ 2 * Nb w g0 g0 := by
      unfold Nb
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hD : Dg w v = 0
      · simp [hD, Tg_zero_of_Dg w hnn hD]
      · rw [hT v]; field_simp
    rw [this, hN0']; ring
  have hqq := hq g0 hsum0'
  rw [hP2, hN0'] at hqq
  have h6 : lam < μ * (1 - lam) := (div_lt_iff₀ h1l).1 hμgt
  nlinarith [mul_pos (sub_pos.2 h6) (sub_pos.2 hμ1)]

end HDXConc.Dev.T23Spec
end

section
set_option autoImplicit false
namespace HDXConc.Dev.T23Spec
open Finset

variable {V : Type*} [Fintype V]

lemma Eb_shift (w : V → V → ℝ) (hsym : ∀ u v, w u v = w v u) (g : V → ℝ) (m : ℝ) :
    Eb w (fun u => g u - m) (fun u => g u - m) =
      Eb w g g - 2 * m * ∑ v, Dg w v * g v + m ^ 2 * ∑ v, Dg w v := by
  unfold Eb
  have key : ∀ u x, w u x * (g u - m) * (g x - m) =
      w u x * g u * g x - m * (w u x * g u) - m * (w u x * g x) + m ^ 2 * w u x :=
    fun u x => by ring
  simp only [key, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ u, ∑ x, w u x * g u = ∑ v, Dg w v * g v :=
    Finset.sum_congr rfl fun u _ => by rw [Dg, Finset.sum_mul]
  have h2 : ∑ u, ∑ x, w u x * g x = ∑ v, Dg w v * g v := sum_T w hsym g
  have h3 : ∑ u, ∑ x, w u x = ∑ v, Dg w v := rfl
  rw [h1, h2, h3]; ring

lemma Nb_shift (w : V → V → ℝ) (g : V → ℝ) (m : ℝ) :
    Nb w (fun u => g u - m) (fun u => g u - m) =
      Nb w g g - 2 * m * ∑ v, Dg w v * g v + m ^ 2 * ∑ v, Dg w v := by
  unfold Nb
  have key : ∀ u, Dg w u * (g u - m) * (g u - m) =
      Dg w u * g u * g u - 2 * m * (Dg w u * g u) + m ^ 2 * Dg w u := fun u => by ring
  simp only [key, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem step_abstract (w : V → V → ℝ) (hsym : ∀ u v, w u v = w v u) (hnn : ∀ u v, 0 ≤ w u v)
    (S : Finset V) (wv : V → V → V → ℝ) {c lam : ℝ} (hc : 0 < c)
    (hvsym : ∀ v ∈ S, ∀ u x, wv v u x = wv v x u)
    (hS0 : ∀ v, v ∉ S → ∀ u, w v u = 0)
    (hdeg : ∀ v ∈ S, ∀ u, Dg (wv v) u = c * w v u)
    (hsumv : ∀ u x, ∑ v ∈ S, wv v u x = c * w u x)
    (hSE : ∀ v ∈ S, ∀ h : V → ℝ, ∑ u, Dg (wv v) u * h u = 0 →
        Eb (wv v) h h ≤ lam * Nb (wv v) h h)
    (g : V → ℝ) :
    Eb w g g ≤ (1 - lam) * ∑ v, (Tg w g v) ^ 2 / Dg w v + lam * Nb w g g := by
  set m : V → ℝ := fun v => Tg w g v / Dg w v with hm
  have hTm : ∀ v, Tg w g v = m v * Dg w v := by
    intro v; by_cases hD : Dg w v = 0
    · simp [hD, Tg_zero_of_Dg w hnn hD]
    · simp only [hm]; field_simp
  have hm2 : ∀ v, m v ^ 2 * Dg w v = Tg w g v ^ 2 / Dg w v := by
    intro v; by_cases hD : Dg w v = 0
    · simp [hD]
    · simp only [hm]; field_simp
  have key : ∀ v ∈ S, Eb (wv v) g g ≤
      c * (m v ^ 2 * Dg w v) + lam * c * ((∑ u, w v u * g u ^ 2) - m v ^ 2 * Dg w v) := by
    intro v hv
    have f1 : ∑ u, Dg (wv v) u * g u = c * Tg w g v := by
      rw [Tg, Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by rw [hdeg v hv u]; ring
    have f2 : ∑ u, Dg (wv v) u = c * Dg w v := by
      rw [Dg, Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => hdeg v hv u
    have f3 : Nb (wv v) g g = c * ∑ u, w v u * g u ^ 2 := by
      rw [Finset.mul_sum]; unfold Nb
      exact Finset.sum_congr rfl fun u _ => by rw [hdeg v hv u]; ring
    have hz : ∑ u, Dg (wv v) u * (g u - m v) = 0 := by
      have : ∑ u, Dg (wv v) u * (g u - m v) =
          ∑ u, Dg (wv v) u * g u - m v * ∑ u, Dg (wv v) u := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun u _ => by ring
      rw [this, f1, f2, hTm v]; ring
    have h := hSE v hv (fun u => g u - m v) hz
    rw [Eb_shift _ (hvsym v hv), Nb_shift, f1, f2, f3, hTm v] at h
    nlinarith [h]
  have hsum1 : ∑ v ∈ S, Eb (wv v) g g = c * Eb w g g := by
    unfold Eb
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have := hsumv u x
    calc ∑ v ∈ S, wv v u x * g u * g x = (∑ v ∈ S, wv v u x) * g u * g x := by
          rw [Finset.sum_mul, Finset.sum_mul]
      _ = c * (w u x * g u * g x) := by rw [this]; ring
  have hR : ∑ v ∈ S, ∑ u, w v u * g u ^ 2 = Nb w g g := by
    have h0 : ∑ v ∈ S, ∑ u, w v u * g u ^ 2 = ∑ v, ∑ u, w v u * g u ^ 2 :=
      Finset.sum_subset (Finset.subset_univ S) (fun v _ hv => by simp [hS0 v hv])
    rw [h0, Nb_eq, Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hsym v u]
  have hP : ∑ v ∈ S, m v ^ 2 * Dg w v = ∑ v, Tg w g v ^ 2 / Dg w v := by
    calc ∑ v ∈ S, m v ^ 2 * Dg w v = ∑ v ∈ S, Tg w g v ^ 2 / Dg w v :=
          Finset.sum_congr rfl fun v _ => hm2 v
      _ = ∑ v, Tg w g v ^ 2 / Dg w v :=
          Finset.sum_subset (Finset.subset_univ S) (fun v _ hv => by simp [Tg, hS0 v hv])
  have hs := Finset.sum_le_sum key
  rw [hsum1] at hs
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hR, hP] at hs
  have h2 : c * Eb w g g ≤ c * ((1 - lam) * ∑ v, Tg w g v ^ 2 / Dg w v + lam * Nb w g g) := by
    nlinarith [hs]
  exact le_of_mul_le_mul_left h2 hc

end HDXConc.Dev.T23Spec
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace HDXConc.Dev.T23Link
open Finset HDXConc HDXConc.Dev.T23Spec

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def Mm (X : Finset (Finset V)) (d : ℕ) (π : Finset V → ℝ) (S : Finset V) : ℝ :=
  ∑ t ∈ (SteurerHDX.faces X d).filter (fun t => S ⊆ t), π t

lemma mem_faces {X : Finset (Finset V)} {d : ℕ} {t : Finset V} :
    t ∈ SteurerHDX.faces X d ↔ t ∈ X ∧ t.card = d := Finset.mem_filter

section
variable {X : Finset (Finset V)} {d : ℕ} {π : Finset V → ℝ}

lemma Mm_nonneg (hπ : IsTopDensity X d π) (S : Finset V) : 0 ≤ Mm X d π S :=
  Finset.sum_nonneg fun t ht => (hπ.pos t (Finset.mem_filter.1 ht).1).le

lemma Mm_mem (hX : SteurerHDX.IsPure X d) {S : Finset V} (h : Mm X d π S ≠ 0) : S ∈ X := by
  by_contra hS
  apply h
  refine Finset.sum_eq_zero fun t ht => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 ht
  exact absurd (hX.1 t (mem_faces.1 h1).1 S h2) hS

lemma Mm_pos (hX : SteurerHDX.IsPure X d) (hπ : IsTopDensity X d π) {S : Finset V}
    (hS : S ∈ X) : 0 < Mm X d π S := by
  have hne : (X.filter (fun t => S ⊆ t)).Nonempty :=
    ⟨S, Finset.mem_filter.2 ⟨hS, Finset.Subset.refl S⟩⟩
  obtain ⟨t, ht, hmax⟩ := Finset.exists_maximal hne
  obtain ⟨htX, hSt⟩ := Finset.mem_filter.1 ht
  have hcard : t.card = d := by
    refine hX.2 t htX fun ρ hρ hsub => ?_
    exact Finset.Subset.antisymm (hmax (Finset.mem_filter.2 ⟨hρ, hSt.trans hsub⟩) hsub) hsub
  have htF : t ∈ SteurerHDX.faces X d := mem_faces.2 ⟨htX, hcard⟩
  have h1 : π t ≤ Mm X d π S :=
    Finset.single_le_sum (f := π) (fun i hi => (hπ.pos i (Finset.mem_filter.1 hi).1).le)
      (Finset.mem_filter.2 ⟨htF, hSt⟩)
  exact lt_of_lt_of_le (hπ.pos t htF) h1

lemma sum_insert_Mm (hπ : IsTopDensity X d π) (S : Finset V) :
    ∑ x ∈ Finset.univ.filter (fun x => x ∉ S), Mm X d π (insert x S) =
      ((d : ℝ) - S.card) * Mm X d π S := by
  unfold Mm
  have per : ∀ t ∈ SteurerHDX.faces X d,
      ∑ x ∈ Finset.univ.filter (fun x => x ∉ S), (if insert x S ⊆ t then π t else 0) =
        ((d : ℝ) - S.card) * (if S ⊆ t then π t else 0) := by
    intro t ht
    have htd : t.card = d := (mem_faces.1 ht).2
    by_cases hS : S ⊆ t
    · have e : ∀ x, insert x S ⊆ t ↔ x ∈ t := fun x => by
        rw [Finset.insert_subset_iff]; simp [hS]
      simp only [e, if_pos hS]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have : (Finset.univ.filter (fun x => x ∉ S)).filter (fun x => x ∈ t) = t \ S := by
        ext x; simp [and_comm]
      have hle : S.card ≤ d := htd ▸ Finset.card_le_card hS
      rw [this, Finset.card_sdiff_of_subset hS, htd, Nat.cast_sub hle]
    · have e : ∀ x, ¬ insert x S ⊆ t := fun x h => hS ((Finset.subset_insert x S).trans h)
      simp [e, hS]
  calc ∑ x ∈ Finset.univ.filter (fun x => x ∉ S),
        ∑ t ∈ (SteurerHDX.faces X d).filter (fun t => insert x S ⊆ t), π t
      = ∑ x ∈ Finset.univ.filter (fun x => x ∉ S),
        ∑ t ∈ SteurerHDX.faces X d, (if insert x S ⊆ t then π t else 0) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_filter _ _
    _ = ∑ t ∈ SteurerHDX.faces X d, ∑ x ∈ Finset.univ.filter (fun x => x ∉ S),
        (if insert x S ⊆ t then π t else 0) := Finset.sum_comm
    _ = ∑ t ∈ SteurerHDX.faces X d, ((d : ℝ) - S.card) * (if S ⊆ t then π t else 0) :=
        Finset.sum_congr rfl per
    _ = ((d : ℝ) - S.card) * ∑ t ∈ SteurerHDX.faces X d, (if S ⊆ t then π t else 0) :=
        (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [Finset.sum_filter]


lemma lw_def (s : Finset V) (u v : V) :
    linkWeight X d π s u v =
      if u ≠ v ∧ u ∉ s ∧ v ∉ s then Mm X d π (s ∪ {u, v}) else 0 := rfl

lemma lw_symm (s : Finset V) (u v : V) :
    linkWeight X d π s u v = linkWeight X d π s v u := by
  simp only [lw_def]
  rw [Finset.pair_comm u v]
  by_cases h : u ≠ v ∧ u ∉ s ∧ v ∉ s
  · have h' : v ≠ u ∧ v ∉ s ∧ u ∉ s := ⟨h.1.symm, h.2.2, h.2.1⟩
    simp [h, h']
  · have h' : ¬ (v ≠ u ∧ v ∉ s ∧ u ∉ s) := fun h' => h ⟨h'.1.symm, h'.2.2, h'.2.1⟩
    simp [h, h']

lemma lw_nonneg (hπ : IsTopDensity X d π) (s : Finset V) (u v : V) :
    0 ≤ linkWeight X d π s u v := by
  rw [lw_def]; split_ifs
  · exact Mm_nonneg hπ _
  · exact le_refl _

lemma lw_ne_zero (hX : SteurerHDX.IsPure X d) {s : Finset V} {u v : V}
    (h : linkWeight X d π s u v ≠ 0) :
    (u ≠ v ∧ u ∉ s ∧ v ∉ s) ∧ s ∪ {u, v} ∈ X := by
  rw [lw_def] at h
  by_cases hc : u ≠ v ∧ u ∉ s ∧ v ∉ s
  · rw [if_pos hc] at h
    exact ⟨hc, Mm_mem hX h⟩
  · rw [if_neg hc] at h; exact absurd rfl h

lemma mem_linkVerts {s : Finset V} {u : V} :
    u ∈ linkVerts X s ↔ u ∉ s ∧ insert u s ∈ X := by
  simp [linkVerts]

lemma lw_support (hX : SteurerHDX.IsPure X d) {s : Finset V} {u v : V}
    (h : linkWeight X d π s u v ≠ 0) : u ∈ linkVerts X s ∧ v ∈ linkVerts X s := by
  obtain ⟨⟨hne, hu, hv⟩, hmem⟩ := lw_ne_zero hX h
  refine ⟨mem_linkVerts.2 ⟨hu, hX.1 _ hmem _ ?_⟩, mem_linkVerts.2 ⟨hv, hX.1 _ hmem _ ?_⟩⟩
  · intro y; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]; tauto
  · intro y; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]; tauto

lemma lw_zero_of_not_mem (hX : SteurerHDX.IsPure X d) {s : Finset V} (hs : s ∉ X) (u v : V) :
    linkWeight X d π s u v = 0 := by
  by_contra h
  have := (mem_linkVerts.1 (lw_support hX h).1).2
  exact hs (hX.1 _ this s (Finset.subset_insert _ _))

lemma lw_pos (hX : SteurerHDX.IsPure X d) (hπ : IsTopDensity X d π) {s : Finset V} {u v : V}
    (h1 : u ≠ v) (h2 : u ∉ s) (h3 : v ∉ s) (h4 : s ∪ {u, v} ∈ X) :
    0 < linkWeight X d π s u v := by
  rw [lw_def, if_pos ⟨h1, h2, h3⟩]
  exact Mm_pos hX hπ h4

lemma lw_deg (hπ : IsTopDensity X d π) {s : Finset V} {v : V} (hv : v ∉ s) (u : V) :
    Dg (linkWeight X d π (insert v s)) u = ((d : ℝ) - s.card - 2) * linkWeight X d π s v u := by
  unfold Dg
  by_cases hu : u ∈ insert v s
  · have h1 : ∀ x, linkWeight X d π (insert v s) u x = 0 := fun x => by
      rw [lw_def, if_neg (fun h => h.2.1 hu)]
    have h2 : linkWeight X d π s v u = 0 := by
      rw [lw_def, if_neg]
      intro h
      rcases Finset.mem_insert.1 hu with rfl | hus
      · exact h.1 rfl
      · exact h.2.2 hus
    simp [h1, h2]
  · have hus : u ∉ s := fun h => hu (Finset.mem_insert_of_mem h)
    have huv : u ≠ v := fun h => hu (h ▸ Finset.mem_insert_self _ _)
    have hS : (insert u (insert v s)).card = s.card + 2 := by
      rw [Finset.card_insert_of_notMem hu, Finset.card_insert_of_notMem hv]
    have key := sum_insert_Mm hπ (insert u (insert v s))
    rw [hS] at key
    have e : ∀ x, (insert v s) ∪ {u, x} = insert x (insert u (insert v s)) := fun x => by
      ext y; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]; tauto
    have hw : linkWeight X d π s v u = Mm X d π (insert u (insert v s)) := by
      rw [lw_def, if_pos ⟨huv.symm, hv, hus⟩]
      congr 1
      ext y; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]; tauto
    rw [hw]
    have : ∑ x, linkWeight X d π (insert v s) u x =
        ∑ x ∈ Finset.univ.filter (fun x => x ∉ insert u (insert v s)),
          Mm X d π (insert x (insert u (insert v s))) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [lw_def]
      have hc : (u ≠ x ∧ u ∉ insert v s ∧ x ∉ insert v s) ↔ x ∉ insert u (insert v s) := by
        constructor
        · rintro ⟨h1, h2, h3⟩ hx
          simp only [Finset.mem_insert] at h3 hx
          rcases hx with h | h | h
          · exact h1 h.symm
          · exact h3 (Or.inl h)
          · exact h3 (Or.inr h)
        · intro h
          simp only [Finset.mem_insert, not_or] at h
          refine ⟨fun h' => h.1 h'.symm, by simp [huv, hus], ?_⟩
          simp only [Finset.mem_insert, not_or]; exact h.2
      exact if_congr hc (by rw [e x]) rfl
    rw [this, key]
    push_cast; ring


lemma lw_sumv (hπ : IsTopDensity X d π) (s : Finset V) (u x : V) :
    ∑ v ∈ Finset.univ.filter (fun v => v ∉ s), linkWeight X d π (insert v s) u x =
      ((d : ℝ) - s.card - 2) * linkWeight X d π s u x := by
  by_cases h : u ≠ x ∧ u ∉ s ∧ x ∉ s
  · obtain ⟨hux, hus, hxs⟩ := h
    have hxu : x ∉ insert u s := by
      simp only [Finset.mem_insert, not_or]; exact ⟨fun h => hux h.symm, hxs⟩
    have hS : (insert x (insert u s)).card = s.card + 2 := by
      rw [Finset.card_insert_of_notMem hxu, Finset.card_insert_of_notMem hus]
    have key := sum_insert_Mm hπ (insert x (insert u s))
    rw [hS] at key
    have hw : linkWeight X d π s u x = Mm X d π (insert x (insert u s)) := by
      rw [lw_def, if_pos ⟨hux, hus, hxs⟩]
      congr 1
      ext y; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]; tauto
    rw [hw]
    have : ∑ v ∈ Finset.univ.filter (fun v => v ∉ s), linkWeight X d π (insert v s) u x =
        ∑ v ∈ Finset.univ.filter (fun v => v ∉ insert x (insert u s)),
          Mm X d π (insert v (insert x (insert u s))) := by
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hvs : v ∈ s
      · rw [if_neg (not_not.2 hvs), if_neg (not_not.2 (by simp [hvs]))]
      · rw [if_pos hvs, lw_def]
        by_cases hvS : v ∈ insert x (insert u s)
        · rw [if_neg (not_not.2 hvS), if_neg]
          rintro ⟨_, h2, h3⟩
          simp only [Finset.mem_insert, not_or] at hvS h2 h3
          rcases hvS with h | h | h
          · exact h3.1 h.symm
          · exact h2.1 h.symm
          · exact hvs h
        · rw [if_pos hvS, if_pos]
          · congr 1
            ext y; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]; tauto
          · simp only [Finset.mem_insert, not_or] at hvS ⊢
            exact ⟨hux, ⟨fun h => hvS.2.1 h.symm, hus⟩, ⟨fun h => hvS.1 h.symm, hxs⟩⟩
    rw [this, key]
    push_cast; ring
  · have hz : linkWeight X d π s u x = 0 := by rw [lw_def, if_neg h]
    rw [hz, mul_zero]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [lw_def, if_neg]
    rintro ⟨h1, h2, h3⟩
    apply h
    refine ⟨h1, fun h => h2 (Finset.mem_insert_of_mem h), fun h => h3 (Finset.mem_insert_of_mem h)⟩

lemma SE_iff (W : Finset V) (w : V → V → ℝ) (lam : ℝ)
    (hsupp : ∀ u v, w u v ≠ 0 → u ∈ W ∧ v ∈ W) :
    SecondEigLE W w lam ↔
      ∀ g : V → ℝ, ∑ v, Dg w v * g v = 0 → Eb w g g ≤ lam * Nb w g g := by
  have hD : ∀ v, weightedDeg W w v = Dg w v := fun v =>
    Finset.sum_subset (Finset.subset_univ W) (fun u _ hu => by
      by_contra h; exact hu (hsupp v u h).2)
  have hDz : ∀ v, v ∉ W → Dg w v = 0 := fun v hv =>
    Finset.sum_eq_zero fun u _ => by by_contra h; exact hv (hsupp v u h).1
  have hSum : ∀ g : V → ℝ, ∑ v ∈ W, weightedDeg W w v * g v = ∑ v, Dg w v * g v := fun g => by
    simp only [hD]
    exact Finset.sum_subset (Finset.subset_univ W) (fun v _ hv => by simp [hDz v hv])
  have hN : ∀ g : V → ℝ, ∑ v ∈ W, weightedDeg W w v * g v ^ 2 = Nb w g g := fun g => by
    simp only [hD]
    unfold Nb
    rw [Finset.sum_subset (Finset.subset_univ W) (fun v _ hv => by simp [hDz v hv])]
    exact Finset.sum_congr rfl fun v _ => by ring
  have hE : ∀ g : V → ℝ, ∑ u ∈ W, ∑ v ∈ W, w u v * g u * g v = Eb w g g := fun g => by
    unfold Eb
    have h1 : ∀ u, ∑ v ∈ W, w u v * g u * g v = ∑ v, w u v * g u * g v := fun u =>
      Finset.sum_subset (Finset.subset_univ W) (fun v _ hv => by
        have : w u v = 0 := by by_contra h; exact hv (hsupp u v h).2
        simp [this])
    simp only [h1]
    exact Finset.sum_subset (Finset.subset_univ W) (fun u _ hu => by
      refine Finset.sum_eq_zero fun v _ => ?_
      have : w u v = 0 := by by_contra h; exact hu (hsupp u v h).1
      simp [this])
  unfold SecondEigLE
  constructor
  · intro h g hg
    have := h g (by rw [hSum]; exact hg)
    rwa [hE, hN] at this
  · intro h g hg
    have := h g (by rw [← hSum]; exact hg)
    rwa [← hE, ← hN] at this


lemma conn_strict (hX : SteurerHDX.IsPure X d) (hπ : IsTopDensity X d π) {s : Finset V}
    (hconn : (linkGraph X s).Connected) (g : V → ℝ)
    (hg : ∑ v, Dg (linkWeight X d π s) v * g v = 0)
    (hN : Nb (linkWeight X d π s) g g ≠ 0) :
    Eb (linkWeight X d π s) g g < Nb (linkWeight X d π s) g g := by
  have hsym : ∀ u v, linkWeight X d π s u v = linkWeight X d π s v u := lw_symm s
  have hnn := lw_nonneg hπ s
  rcases (Eb_le_Nb _ hsym hnn g).lt_or_eq with h | h
  · exact h
  · exfalso
    have hgap := gap_eq _ hsym g
    rw [h, sub_self, mul_zero] at hgap
    have hterm : ∀ u v, linkWeight X d π s u v * (g u - g v) ^ 2 = 0 := by
      intro u v
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => Finset.sum_nonneg fun v _ =>
        mul_nonneg (hnn u v) (sq_nonneg _))).1 hgap u (Finset.mem_univ u)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun v _ =>
        mul_nonneg (hnn u v) (sq_nonneg _))).1 h1 v (Finset.mem_univ v)
    have hadj : ∀ a b : {v // v ∈ linkVerts X s}, (linkGraph X s).Adj a b → g a = g b := by
      intro a b hab
      obtain ⟨hne, hmem⟩ := hab
      have ha := (mem_linkVerts.1 a.2).1
      have hb := (mem_linkVerts.1 b.2).1
      have hpos := lw_pos hX hπ hne ha hb hmem
      rcases mul_eq_zero.1 (hterm a b) with h0 | h0
      · exact absurd h0 hpos.ne'
      · have := pow_eq_zero_iff (two_ne_zero) |>.1 h0
        linarith
    have hreach : ∀ a b : {v // v ∈ linkVerts X s}, g a = g b := by
      intro a b
      have := (SimpleGraph.reachable_iff_reflTransGen a b).1 (hconn.preconnected a b)
      induction this with
      | refl => rfl
      | tail _ hbc ih => exact ih.trans (hadj _ _ hbc)
    have hDpos : ∀ v, Dg (linkWeight X d π s) v ≠ 0 → v ∈ linkVerts X s := by
      intro v hD
      obtain ⟨u, _, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hD
      exact (lw_support hX hu).1
    by_cases hex : ∃ u0, u0 ∈ linkVerts X s
    · obtain ⟨u0, hu0⟩ := hex
      have hk : ∀ v, Dg (linkWeight X d π s) v * g v * g v =
          g u0 * (Dg (linkWeight X d π s) v * g v) := by
        intro v
        by_cases hD : Dg (linkWeight X d π s) v = 0
        · simp [hD]
        · have hv := hDpos v hD
          have := hreach ⟨v, hv⟩ ⟨u0, hu0⟩
          simp only at this
          rw [this]; ring
      apply hN
      unfold Nb
      rw [Finset.sum_congr rfl fun v _ => hk v, ← Finset.mul_sum, hg, mul_zero]
    · rw [not_exists] at hex
      apply hN; unfold Nb; refine Finset.sum_eq_zero fun v _ => ?_
      have : Dg (linkWeight X d π s) v = 0 := by
        by_contra hD; exact hex v (hDpos v hD)
      simp [this]

theorem link_step (hX : SteurerHDX.IsPure X d) (hπ : IsTopDensity X d π) {s : Finset V}
    (hcard : s.card + 3 ≤ d) (hconn : (linkGraph X s).Connected) {lam : ℝ} (hlam : lam < 1)
    (hIH : ∀ v ∈ linkVerts X s,
      SecondEigLE (linkVerts X (insert v s)) (linkWeight X d π (insert v s)) lam) :
    SecondEigLE (linkVerts X s) (linkWeight X d π s) (lam / (1 - lam)) := by
  have hsym : ∀ u v, linkWeight X d π s u v = linkWeight X d π s v u := lw_symm s
  have hnn := lw_nonneg hπ s
  rw [SE_iff _ _ _ (fun u v h => lw_support hX h)]
  have hcr : (0 : ℝ) < (d : ℝ) - s.card - 2 := by
    have : (s.card : ℝ) + 3 ≤ d := by exact_mod_cast hcard
    linarith
  have hq := spectral (linkWeight X d π s) hsym hnn hlam
    (fun g hg hN => conn_strict hX hπ hconn g hg hN)
    (fun g _ => step_abstract (linkWeight X d π s) hsym hnn
      (Finset.univ.filter (fun v => v ∉ s)) (fun v => linkWeight X d π (insert v s)) hcr
      (fun v _ u x => lw_symm _ u x)
      (fun v hv u => by
        have : v ∈ s := by simpa using hv
        rw [lw_def, if_neg]
        intro h; exact h.2.1 this)
      (fun v hv u => lw_deg hπ (Finset.mem_filter.1 hv).2 u)
      (lw_sumv hπ s)
      (fun v hv h hh => by
        by_cases hmem : insert v s ∈ X
        · have hvl : v ∈ linkVerts X s := mem_linkVerts.2 ⟨(Finset.mem_filter.1 hv).2, hmem⟩
          exact (SE_iff _ _ _ (fun u x hne => lw_support hX hne)).1 (hIH v hvl) h hh
        · have hz := fun u x => lw_zero_of_not_mem hX hmem (π := π) u x
          simp [Eb, Nb, Dg, hz]) g)
  exact hq

end
end HDXConc.Dev.T23Link
end

section
set_option autoImplicit false
namespace HDXConc.Dev.T23Main
open HDXConc HDXConc.Dev.T23Spec HDXConc.Dev.T23Link

lemma denom_pos {d : ℕ} (hd : 2 ≤ d) {lam : ℝ} (hlam : lam < 1 / ((d : ℝ) - 1)) {j : ℝ}
    (hj0 : 0 ≤ j) (hj : j ≤ (d : ℝ) - 2) : 0 < 1 - j * lam := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hl : lam * ((d : ℝ) - 1) < 1 := by
    have := (lt_div_iff₀ hpos).1 hlam
    exact this
  rcases le_or_gt lam 0 with h | h
  · nlinarith
  · have h1 : j * lam ≤ ((d : ℝ) - 2) * lam := mul_le_mul_of_nonneg_right hj h.le
    nlinarith

lemma SE_mono {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} {X : Finset (Finset V)}
    {π : Finset V → ℝ} (hX : SteurerHDX.IsPure X d) (hπ : IsTopDensity X d π) (s : Finset V)
    {a b : ℝ} (hab : a ≤ b)
    (h : SecondEigLE (linkVerts X s) (linkWeight X d π s) a) :
    SecondEigLE (linkVerts X s) (linkWeight X d π s) b := by
  rw [SE_iff _ _ _ (fun u v h => lw_support hX h)] at h ⊢
  intro g hg
  exact (h g hg).trans (mul_le_mul_of_nonneg_right hab
    (Nb_nonneg _ (lw_nonneg hπ s) g))

theorem main {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} (hd : 2 ≤ d)
    {X : Finset (Finset V)} {π : Finset V → ℝ} (hX : SteurerHDX.IsPure X d)
    (hπ : IsTopDensity X d π) (hconn : LinksConnected X d) {lam : ℝ}
    (hlam : lam < 1 / ((d : ℝ) - 1))
    (hlink : ∀ s ∈ X, s.card + 2 = d →
      SecondEigLE (linkVerts X s) (linkWeight X d π s) lam) :
    ∀ s ∈ X, s.card + 2 ≤ d →
      SecondEigLE (linkVerts X s) (linkWeight X d π s)
        (lam / (1 - ((d : ℝ) - 2) * lam)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have claim : ∀ j : ℕ, j + 2 ≤ d → ∀ s ∈ X, s.card + 2 + j = d →
      SecondEigLE (linkVerts X s) (linkWeight X d π s) (lam / (1 - (j : ℝ) * lam)) := by
    intro j
    induction j with
    | zero =>
      intro _ s hs hsc
      have := hlink s hs (by omega)
      simpa using this
    | succ j ih =>
      intro hj s hs hsc
      have hjr : ((j : ℝ) + 1) ≤ (d : ℝ) - 2 := by
        have : j + 1 + 2 ≤ d := hj
        have : ((j + 1 + 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast this
        push_cast at this; linarith
      have hp1 := denom_pos hd hlam (j := (j : ℝ) + 1) (by positivity) hjr
      have hp0 := denom_pos hd hlam (j := (j : ℝ)) (by positivity) (by linarith)
      have hlt : lam / (1 - (j : ℝ) * lam) < 1 := by
        rw [div_lt_one hp0]; nlinarith
      have hstep := link_step hX hπ (s := s) (by omega) (hconn s hs (by omega)) hlt
        (fun v hv => by
          obtain ⟨hvs, hvX⟩ := mem_linkVerts.1 hv
          have hc : (insert v s).card = s.card + 1 := Finset.card_insert_of_notMem hvs
          exact ih (by omega) (insert v s) hvX (by omega))
      have heq : lam / (1 - (j : ℝ) * lam) / (1 - lam / (1 - (j : ℝ) * lam)) =
          lam / (1 - ((j + 1 : ℕ) : ℝ) * lam) := by
        push_cast
        have h1 : (1 - ((j : ℝ) + 1) * lam) ≠ 0 := hp1.ne'
        have h2 : (1 - (j : ℝ) * lam) ≠ 0 := hp0.ne'
        have h3 : 1 - lam / (1 - (j : ℝ) * lam) = (1 - ((j : ℝ) + 1) * lam) /
            (1 - (j : ℝ) * lam) := by
          rw [eq_div_iff h2, sub_mul, div_mul_cancel₀ _ h2]; ring
        rw [h3, div_div_div_cancel_right₀ h2]
      rw [heq] at hstep
      exact hstep
  intro s hs hsc
  have hj : d - 2 - s.card + 2 ≤ d := by omega
  have h := claim (d - 2 - s.card) hj s hs (by omega)
  refine SE_mono hX hπ s ?_ h
  have hjr : ((d - 2 - s.card : ℕ) : ℝ) ≤ (d : ℝ) - 2 := by
    have : ((d - 2 - s.card : ℕ) : ℝ) ≤ ((d - 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le _ _
    rw [Nat.cast_sub hd] at this; push_cast at this; linarith
  have hpa := denom_pos hd hlam (j := ((d - 2 - s.card : ℕ) : ℝ)) (by positivity) hjr
  have hpb := denom_pos hd hlam (j := (d : ℝ) - 2) (by linarith) le_rfl
  rw [div_le_div_iff₀ hpa hpb]
  nlinarith [sq_nonneg lam]

end HDXConc.Dev.T23Main

namespace HDXConc

theorem chk_theorem_2_3 {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} (hd : 2 ≤ d)
    {X : Finset (Finset V)} {π : Finset V → ℝ} (hX : SteurerHDX.IsPure X d) (hπ : IsTopDensity X d π)
    (hconn : LinksConnected X d) {lam : ℝ} (hlam : lam < 1 / ((d : ℝ) - 1))
    (hlink : ∀ s ∈ X, s.card + 2 = d → SecondEigLE (linkVerts X s) (linkWeight X d π s) lam) :
    ∀ s ∈ X, s.card + 2 ≤ d →
      SecondEigLE (linkVerts X s) (linkWeight X d π s) (lam / (1 - ((d : ℝ) - 2) * lam)) :=
  HDXConc.Dev.T23Main.main hd hX hπ hconn hlam hlink

end HDXConc
end

theorem solution : type_of% @HDXConc.chk_theorem_2_3 := @HDXConc.chk_theorem_2_3
