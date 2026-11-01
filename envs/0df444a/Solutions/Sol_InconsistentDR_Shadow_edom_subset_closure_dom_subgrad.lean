-- Prove2me | solution 1 for InconsistentDR.Shadow.edom_subset_closure_dom_subgrad
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T23:33:35.737784+00:00
-- url     : https://prove2.me/submissions/58a16f6e-b4fb-419b-860e-59b72690646c

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization

open scoped InnerProductSpace Topology
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization

namespace DRShadowDensAux

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

lemma conv_le (f : X → EReal) (hc : EConvex f) {a b : X} {Fa Fb : ℝ} (ha : f a = Fa)
    (hb : f b = Fb) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    f (s • a + t • b) ≤ ((s * Fa + t * Fb : ℝ) : EReal) := by
  have hA : ((a, Fa) : X × ℝ) ∈ {p : X × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} := by
    simp [ha]
  have hB : ((b, Fb) : X × ℝ) ∈ {p : X × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} := by
    simp [hb]
  have := hc hA hB hs ht hst
  simpa using this

lemma toReal_eq {e : EReal} (h1 : e ≠ ⊤) (h2 : e ≠ ⊥) : ∃ r : ℝ, e = r :=
  ⟨e.toReal, (EReal.coe_toReal h1 h2).symm⟩

/-- Existence of a minimizer of `w ↦ f w - ⟪w, u⟫ + ‖w‖² / (2λ)` when `u ∈ dom f*`. -/
lemma exists_min [CompleteSpace X] (f : X → EReal) (hf : GammaZero f) (u : X) (M : ℝ)
    (lam : ℝ) (hlam : 0 < lam)
    (hM : ∀ w (r : ℝ), f w = r → -M ≤ r - ⟪w, u⟫_ℝ + ‖w‖ ^ 2 / (2 * lam)) :
    ∃ w : X, ∃ F : ℝ, f w = F ∧ ∀ w' (r : ℝ), f w' = r →
      F - ⟪w, u⟫_ℝ + ‖w‖ ^ 2 / (2 * lam) ≤ r - ⟪w', u⟫_ℝ + ‖w'‖ ^ 2 / (2 * lam) := by
  set Φ : X → ℝ := fun w => (f w).toReal - ⟪w, u⟫_ℝ + ‖w‖ ^ 2 / (2 * lam) with hΦ
  set S : Set X := {w | f w ≠ ⊤} with hS
  have hcoe : ∀ w ∈ S, f w = ((f w).toReal : EReal) := fun w hw =>
    (EReal.coe_toReal hw (hf.1 w)).symm
  have hlam2 : 0 < 2 * lam := by positivity
  have hlow : ∀ w ∈ S, -M ≤ Φ w := by
    intro w hw
    have := hM w _ (hcoe w hw)
    simp only [hΦ]; linarith
  obtain ⟨x0, hx0⟩ := hf.2.1
  have hVne : (Φ '' S).Nonempty := ⟨Φ x0, x0, hx0, rfl⟩
  have hVbdd : BddBelow (Φ '' S) := ⟨-M, by rintro _ ⟨w, hw, rfl⟩; exact hlow w hw⟩
  set m := sInf (Φ '' S) with hm
  have hmle : ∀ w ∈ S, m ≤ Φ w := fun w hw => csInf_le hVbdd ⟨w, hw, rfl⟩
  have hseq : ∀ k : ℕ, ∃ w ∈ S, Φ w < m + 1 / ((k : ℝ) + 1) := by
    intro k
    have hk : m < m + 1 / ((k : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hVne hk
    exact ⟨w, hw, hlt⟩
  choose w hwS hwlt using hseq
  -- strong convexity at midpoints
  have hmid : ∀ a ∈ S, ∀ b ∈ S, ‖a - b‖ ^ 2 / (8 * lam) ≤ (Φ a + Φ b) / 2 - m := by
    intro a ha b hb
    have hc := conv_le f hf.2.2.1 (hcoe a ha) (hcoe b hb) (s := 1 / 2) (t := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
    set c := (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b with hcdef
    have hcS : c ∈ S := by
      intro htop; rw [htop, top_le_iff] at hc; exact EReal.coe_ne_top _ hc
    have hcle : (f c).toReal ≤ 1 / 2 * (f a).toReal + 1 / 2 * (f b).toReal := by
      rw [hcoe c hcS] at hc; exact_mod_cast hc
    have h1 := hmle c hcS
    have hpar := parallelogram_law_with_norm ℝ a b
    have hcn : ‖c‖ = 1 / 2 * ‖a + b‖ := by
      rw [hcdef, ← smul_add, norm_smul]; norm_num
    have hcu : ⟪c, u⟫_ℝ = 1 / 2 * ⟪a, u⟫_ℝ + 1 / 2 * ⟪b, u⟫_ℝ := by
      rw [hcdef, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    simp only [hΦ] at h1 ⊢
    rw [hcn, hcu] at h1
    have key : ‖a - b‖ ^ 2 / (8 * lam) =
        ((‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 - (1 / 2 * ‖a + b‖) ^ 2) / (2 * lam) := by
      field_simp; nlinarith [hpar]
    rw [key]
    have e2 : ((‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 - (1 / 2 * ‖a + b‖) ^ 2) / (2 * lam) =
        (‖a‖ ^ 2 / (2 * lam) + ‖b‖ ^ 2 / (2 * lam)) / 2 - (1 / 2 * ‖a + b‖) ^ 2 / (2 * lam) := by
      field_simp
    rw [e2]
    linarith
  -- the minimizing sequence is Cauchy
  have hcauchy : CauchySeq w := by
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => Real.sqrt (8 * lam * (1 / ((N : ℝ) + 1))))
      (fun n k N hn hk => ?_) ?_
    · rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg (w n - w k))]
      apply Real.sqrt_le_sqrt
      have h := hmid (w n) (hwS n) (w k) (hwS k)
      have hn' := hwlt n
      have hk' := hwlt k
      have hN1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity); exact_mod_cast Nat.add_le_add_right hn 1
      have hN2 : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity); exact_mod_cast Nat.add_le_add_right hk 1
      have h8 : 0 < 8 * lam := by positivity
      have : ‖w n - w k‖ ^ 2 / (8 * lam) ≤ 1 / ((N : ℝ) + 1) := by linarith
      rw [div_le_iff₀ h8] at this
      linarith
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (8 * lam)).sqrt
      simpa using this
  obtain ⟨ws, hws⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- values converge
  have hΦlim : Tendsto (fun k => Φ (w k)) atTop (𝓝 m) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun k => hmle _ (hwS k)) (fun k => (hwlt k).le)
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_add m)
    simpa using this
  set L := m + ⟪ws, u⟫_ℝ - ‖ws‖ ^ 2 / (2 * lam) with hL
  have hFlim : Tendsto (fun k => (f (w k)).toReal) atTop (𝓝 L) := by
    have e : (fun k => (f (w k)).toReal) =
        fun k => Φ (w k) + ⟪w k, u⟫_ℝ - ‖w k‖ ^ 2 / (2 * lam) := by
      funext k; simp only [hΦ]; ring
    rw [e]
    exact (hΦlim.add (hws.inner tendsto_const_nhds)).sub ((hws.norm.pow 2).div_const _)
  -- lower semicontinuity
  have hlsc : f ws ≤ (L : EReal) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy1, hy2⟩ := exists_between hcon
    have hev := (hf.2.2.2 ws y hy2)
    have hev2 := hws.eventually hev
    have hyne : y ≠ ⊤ := ne_top_of_lt hy2
    have hynb : y ≠ ⊥ := ne_bot_of_gt hy1
    obtain ⟨y', rfl⟩ := toReal_eq hyne hynb
    have hLy : L < y' := by exact_mod_cast hy1
    have hev3 := hFlim.eventually (gt_mem_nhds hLy)
    obtain ⟨k, hk1, hk2⟩ := (hev2.and hev3).exists
    rw [hcoe _ (hwS k)] at hk1
    have : y' < (f (w k)).toReal := by exact_mod_cast hk1
    linarith
  have hwsS : ws ∈ S := by
    intro htop; rw [htop, top_le_iff] at hlsc; exact EReal.coe_ne_top _ hlsc
  refine ⟨ws, (f ws).toReal, hcoe ws hwsS, fun w' r hr => ?_⟩
  have hw'S : w' ∈ S := by intro htop; rw [hr] at htop; exact EReal.coe_ne_top _ htop
  have h1 := hmle w' hw'S
  have h2 : (f ws).toReal ≤ L := by rw [hcoe ws hwsS] at hlsc; exact_mod_cast hlsc
  simp only [hΦ, hr, EReal.toReal_coe] at h1
  rw [hL] at h2
  linarith

/-- First-order optimality: the minimizer `w` satisfies `u - λ⁻¹ w ∈ ∂f(w)`. -/
lemma opt_subgrad (f : X → EReal) (hf : GammaZero f) (u : X) (lam : ℝ) (hlam : 0 < lam)
    (w : X) (F : ℝ) (hF : f w = F)
    (hmin : ∀ w' (r : ℝ), f w' = r →
      F - ⟪w, u⟫_ℝ + ‖w‖ ^ 2 / (2 * lam) ≤ r - ⟪w', u⟫_ℝ + ‖w'‖ ^ 2 / (2 * lam)) :
    u - lam⁻¹ • w ∈ subgrad f w := by
  refine ⟨by rw [hF]; exact EReal.coe_ne_bot F, by rw [hF]; exact EReal.coe_ne_top F, ?_⟩
  intro z
  by_cases hz : f z = ⊤
  · rw [hz]; exact le_top
  obtain ⟨Fz, hFz⟩ := toReal_eq hz (hf.1 z)
  rw [hF, hFz, ← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  set d := z - w with hd
  set C := ‖d‖ ^ 2 / (2 * lam) with hC
  have hC0 : 0 ≤ C := by positivity
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      F + ⟪d, u⟫_ℝ - lam⁻¹ * ⟪d, w⟫_ℝ ≤ Fz + t * C := by
    intro t ht0 ht1
    have hc := conv_le f hf.2.2.1 hF hFz (s := 1 - t) (t := t) (by linarith) ht0.le (by ring)
    set wt := (1 - t) • w + t • z with hwt
    have hwtS : f wt ≠ ⊤ := by
      intro htop; rw [htop, top_le_iff] at hc; exact EReal.coe_ne_top _ hc
    obtain ⟨r, hr⟩ := toReal_eq hwtS (hf.1 wt)
    have hrle : r ≤ (1 - t) * F + t * Fz := by rw [hr] at hc; exact_mod_cast hc
    have h1 := hmin wt r hr
    have ewt : wt = w + t • d := by rw [hwt, hd]; module
    have h2 : ⟪wt, u⟫_ℝ = ⟪w, u⟫_ℝ + t * ⟪d, u⟫_ℝ := by
      rw [ewt, inner_add_left, real_inner_smul_left]
    have h3 : ‖wt‖ ^ 2 = ‖w‖ ^ 2 + 2 * t * ⟪w, d⟫_ℝ + t ^ 2 * ‖d‖ ^ 2 := by
      rw [ewt, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg ht0.le]
      ring
    rw [h2, h3] at h1
    have h4 : t * (F + ⟪d, u⟫_ℝ - lam⁻¹ * ⟪d, w⟫_ℝ) ≤ t * (Fz + t * C) := by
      have e : ⟪d, w⟫_ℝ = ⟪w, d⟫_ℝ := real_inner_comm _ _
      rw [hC, e]
      have hl : (0 : ℝ) < 2 * lam := by positivity
      have h5 : F - ⟪w, u⟫_ℝ + ‖w‖ ^ 2 / (2 * lam) ≤
          (1 - t) * F + t * Fz - (⟪w, u⟫_ℝ + t * ⟪d, u⟫_ℝ) +
            (‖w‖ ^ 2 + 2 * t * ⟪w, d⟫_ℝ + t ^ 2 * ‖d‖ ^ 2) / (2 * lam) := by linarith
      have e2 : (‖w‖ ^ 2 + 2 * t * ⟪w, d⟫_ℝ + t ^ 2 * ‖d‖ ^ 2) / (2 * lam) =
          ‖w‖ ^ 2 / (2 * lam) + t * (lam⁻¹ * ⟪w, d⟫_ℝ) + t * (t * (‖d‖ ^ 2 / (2 * lam))) := by
        field_simp
      rw [e2] at h5
      nlinarith
    exact le_of_mul_le_mul_left h4 ht0
  rw [inner_sub_right, real_inner_smul_right]
  apply le_of_forall_pos_le_add
  intro ε hε
  set t := min 1 (ε / (C + 1)) with ht
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htC : t * C ≤ ε := by
    have h1 : t ≤ ε / (C + 1) := min_le_right _ _
    have h2 : t * (C + 1) ≤ ε := by
      have := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ C + 1)
      rwa [div_mul_cancel₀ _ (by linarith)] at this
    nlinarith
  have := key t ht0 ht1
  linarith

end DRShadowDensAux

theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f : X → EReal) (hf : GammaZero f) (P : X → X) (hP : IsResolvent 1 (subgrad f) P) :
    InconsistentDR.Shadow.edom f ⊆ closure (dom (subgrad f)) := by
  intro a ha
  obtain ⟨Fa, hFa⟩ := DRShadowDensAux.toReal_eq ha (hf.1 a)
  -- an affine minorant from the proximal point of `0`
  have hs0 := hP 0
  rw [inv_one, one_smul] at hs0
  set p0 := P 0
  set s0 : X := 0 - p0
  obtain ⟨F0, hF0⟩ := DRShadowDensAux.toReal_eq hs0.2.1 hs0.1
  have hminor : ∀ w (r : ℝ), f w = r → F0 + ⟪w - p0, s0⟫_ℝ ≤ r := by
    intro w r hr
    have := hs0.2.2 w
    rw [hF0, hr, ← EReal.coe_add] at this
    exact_mod_cast this
  set K := Fa - F0 - ⟪a - p0, s0⟫_ℝ with hK
  have hK0 : 0 ≤ K := by have := hminor a Fa hFa; rw [hK]; linarith
  set S := ‖s0‖ ^ 2 with hS
  rw [Metric.mem_closure_iff]
  intro ε hε
  set lam := min 1 (ε ^ 2 / (8 * (K + S + 1))) with hlam
  have hlam0 : 0 < lam := lt_min one_pos (by positivity)
  have hlam1 : lam ≤ 1 := min_le_left _ _
  have hlamε : lam * (8 * (K + S + 1)) ≤ ε ^ 2 := by
    have h1 : lam ≤ ε ^ 2 / (8 * (K + S + 1)) := min_le_right _ _
    rwa [le_div_iff₀ (by positivity)] at h1
  set u : X := lam⁻¹ • a with hu
  have hl2 : (0 : ℝ) < 2 * lam := by positivity
  -- lower bound for the objective
  set c : X := s0 - u
  have hM : ∀ w (r : ℝ), f w = r →
      -(-(F0 - ⟪p0, s0⟫_ℝ - lam / 2 * ‖c‖ ^ 2)) ≤ r - ⟪w, u⟫_ℝ + ‖w‖ ^ 2 / (2 * lam) := by
    intro w r hr
    have h1 := hminor w r hr
    have hsq : 0 ≤ ‖w + lam • c‖ ^ 2 := sq_nonneg _
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg hlam0.le] at hsq
    have e1 : ⟪w - p0, s0⟫_ℝ = ⟪w, c⟫_ℝ + ⟪w, u⟫_ℝ - ⟪p0, s0⟫_ℝ := by
      simp only [c, inner_sub_left, inner_sub_right]; ring
    have e2 : ‖w‖ ^ 2 / (2 * lam) + ⟪w, c⟫_ℝ + lam / 2 * ‖c‖ ^ 2 =
        (‖w‖ ^ 2 + 2 * (lam * ⟪w, c⟫_ℝ) + (lam * ‖c‖) ^ 2) / (2 * lam) := by
      field_simp
    have e3 : 0 ≤ (‖w‖ ^ 2 + 2 * (lam * ⟪w, c⟫_ℝ) + (lam * ‖c‖) ^ 2) / (2 * lam) :=
      div_nonneg hsq hl2.le
    linarith
  obtain ⟨w, F, hF, hmin⟩ := DRShadowDensAux.exists_min f hf u _ lam hlam0 hM
  have hsub := DRShadowDensAux.opt_subgrad f hf u lam hlam0 w F hF hmin
  refine ⟨w, ⟨_, hsub⟩, ?_⟩
  rw [dist_eq_norm]
  -- `F + ‖w - a‖²/(2λ) ≤ Fa`
  have h1 := hmin a Fa hFa
  have hwa : ‖a - w‖ ^ 2 = ‖w‖ ^ 2 - 2 * ⟪w, a⟫_ℝ + ‖a‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm]; ring
  have hwu : ⟪w, u⟫_ℝ = lam⁻¹ * ⟪w, a⟫_ℝ := by rw [hu, real_inner_smul_right]
  have hau : ⟪a, u⟫_ℝ = lam⁻¹ * ‖a‖ ^ 2 := by
    rw [hu, real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [hwu, hau] at h1
  have hdist : F + ‖a - w‖ ^ 2 / (2 * lam) ≤ Fa := by
    rw [hwa]
    have e : (‖w‖ ^ 2 - 2 * ⟪w, a⟫_ℝ + ‖a‖ ^ 2) / (2 * lam) =
        ‖w‖ ^ 2 / (2 * lam) - lam⁻¹ * ⟪w, a⟫_ℝ - (‖a‖ ^ 2 / (2 * lam) - lam⁻¹ * ‖a‖ ^ 2) := by
      field_simp; ring
    rw [e]; linarith
  have h2 := hminor w F hF
  -- `⟪w - p0, s0⟫ = ⟪a - p0, s0⟫ - ⟪a - w, s0⟫`
  have e4 : ⟪w - p0, s0⟫_ℝ = ⟪a - p0, s0⟫_ℝ - ⟪a - w, s0⟫_ℝ := by
    rw [← inner_sub_left]; congr 1; abel
  have hcs : ⟪a - w, s0⟫_ℝ ≤ ‖a - w‖ ^ 2 / (4 * lam) + lam * S := by
    have hsq : 0 ≤ ‖a - w - (2 * lam) • s0‖ ^ 2 := sq_nonneg _
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg hl2.le] at hsq
    have e5 : ‖a - w‖ ^ 2 / (4 * lam) + lam * S - ⟪a - w, s0⟫_ℝ =
        (‖a - w‖ ^ 2 - 2 * (2 * lam * ⟪a - w, s0⟫_ℝ) + (2 * lam * ‖s0‖) ^ 2) / (4 * lam) := by
      rw [hS]; field_simp; ring
    have : 0 ≤ (‖a - w‖ ^ 2 - 2 * (2 * lam * ⟪a - w, s0⟫_ℝ) + (2 * lam * ‖s0‖) ^ 2) / (4 * lam) :=
      div_nonneg hsq (by positivity)
    linarith
  have hr2 : ‖a - w‖ ^ 2 ≤ 4 * lam * K + 4 * lam ^ 2 * S := by
    have h3 : ‖a - w‖ ^ 2 / (2 * lam) ≤ K + ‖a - w‖ ^ 2 / (4 * lam) + lam * S := by
      rw [hK]; linarith
    have e6 : ‖a - w‖ ^ 2 / (2 * lam) - ‖a - w‖ ^ 2 / (4 * lam) = ‖a - w‖ ^ 2 / (4 * lam) := by
      field_simp; ring
    have h4 : ‖a - w‖ ^ 2 / (4 * lam) ≤ K + lam * S := by linarith
    rw [div_le_iff₀ (by positivity)] at h4
    nlinarith
  have hS0 : 0 ≤ S := by positivity
  have hfin : ‖a - w‖ ^ 2 < ε ^ 2 := by
    have : 4 * lam ^ 2 * S ≤ 4 * lam * S := by
      have : lam ^ 2 ≤ lam := by nlinarith
      nlinarith
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hfin
