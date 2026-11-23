-- Prove2me | solution 1 for GrothendieckLB.majorant_barrier
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:56:13.151454+00:00
-- url     : https://prove2.me/submissions/ca3a9701-2db8-48b2-b1b6-81efd009b788

import Mathlib
import Definitions.Def_GrothendieckLB_IsAdmissible
import Definitions.Def_GrothendieckLB_taylorCoeff
open Topology

namespace GrothendieckLB

private lemma inv_coeff {H G : ℝ → ℝ}
    (hH : AnalyticAt ℝ H 0) (hG : AnalyticAt ℝ G 0) (hG0 : G 0 = 0)
    (hinv : ∀ᶠ z in 𝓝 (0 : ℝ), H (G z) = z)
    (hH2 : iteratedDeriv 2 H 0 = 0) :
    deriv H 0 * deriv G 0 = 1 ∧ iteratedDeriv 2 G 0 = 0 ∧
      iteratedDeriv 3 H 0 * (deriv G 0) ^ 3 + deriv H 0 * iteratedDeriv 3 G 0 = 0 := by
  have hd2 (F : ℝ → ℝ) : deriv (deriv F) = iteratedDeriv 2 F := by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ (n := 1) (f := F), iteratedDeriv_one]
  have hd3 (F : ℝ → ℝ) : deriv (iteratedDeriv 2 F) = iteratedDeriv 3 F := by
    rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ (n := 2) (f := F)]
  have hHiter : ∀ n : ℕ, AnalyticAt ℝ (iteratedDeriv n H) 0 := by
    intro n
    induction n with
    | zero => simpa [iteratedDeriv_zero] using hH
    | succ n ih => simpa [iteratedDeriv_succ] using ih.deriv
  have hGiter : ∀ n : ℕ, AnalyticAt ℝ (iteratedDeriv n G) 0 := by
    intro n
    induction n with
    | zero => simpa [iteratedDeriv_zero] using hG
    | succ n ih => simpa [iteratedDeriv_succ] using ih.deriv
  have hGtend : Filter.Tendsto G (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, hG0] using hG.continuousAt
  have hHloc (n : ℕ) : ∀ᶠ z in 𝓝 (0 : ℝ), AnalyticAt ℝ (iteratedDeriv n H) (G z) :=
    hGtend.eventually (hHiter n).eventually_analyticAt
  have hGloc (n : ℕ) : ∀ᶠ z in 𝓝 (0 : ℝ), AnalyticAt ℝ (iteratedDeriv n G) z :=
    (hGiter n).eventually_analyticAt
  have hinv' : H ∘ G =ᶠ[𝓝 (0 : ℝ)] id := hinv
  let D1 : ℝ → ℝ := fun z => deriv H (G z) * deriv G z
  let D2 : ℝ → ℝ := fun z =>
    iteratedDeriv 2 H (G z) * deriv G z ^ 2 + deriv H (G z) * iteratedDeriv 2 G z
  let D3 : ℝ → ℝ := fun z =>
    iteratedDeriv 3 H (G z) * deriv G z ^ 3 +
      3 * iteratedDeriv 2 H (G z) * deriv G z * iteratedDeriv 2 G z +
      deriv H (G z) * iteratedDeriv 3 G z
  have hD1 : D1 =ᶠ[𝓝 (0 : ℝ)] (fun _ => 1) := by
    have hloc : ∀ᶠ z in 𝓝 (0 : ℝ), H ∘ G =ᶠ[𝓝 z] id :=
      eventually_eventually_nhds.2 hinv'
    filter_upwards [hloc, hHloc 0, hGloc 0] with z hz hHz hGz
    have hHa : AnalyticAt ℝ H (G z) := by simpa [iteratedDeriv_zero] using hHz
    have hGa : AnalyticAt ℝ G z := by simpa [iteratedDeriv_zero] using hGz
    change deriv H (G z) * deriv G z = 1
    calc
      deriv H (G z) * deriv G z = deriv (H ∘ G) z :=
        (deriv_comp z hHa.differentiableAt hGa.differentiableAt).symm
      _ = deriv id z := hz.deriv_eq
      _ = 1 := deriv_id z
  have hD1der : (fun z => deriv D1 z) =ᶠ[𝓝 (0 : ℝ)] D2 := by
    filter_upwards [hHloc 0, hHloc 1, hGloc 0, hGloc 1] with z hH0z hH1z hG0z hG1z
    have hH0a : AnalyticAt ℝ H (G z) := by simpa [iteratedDeriv_zero] using hH0z
    have hG0a : AnalyticAt ℝ G z := by simpa [iteratedDeriv_zero] using hG0z
    have hH1a : AnalyticAt ℝ (deriv H) (G z) := by
      simpa [iteratedDeriv_succ, iteratedDeriv_one] using hH1z
    have hG1a : AnalyticAt ℝ (deriv G) z := by
      simpa [iteratedDeriv_succ, iteratedDeriv_one] using hG1z
    change deriv (((deriv H) ∘ G) * deriv G) z = _
    rw [deriv_mul ((hH1a.comp hG0a).differentiableAt) hG1a.differentiableAt]
    rw [deriv_comp z hH1a.differentiableAt hG0a.differentiableAt]
    simp only [hd2, Function.comp_apply]
    dsimp [D2]
    ring
  have hD2der : (fun z => deriv D2 z) =ᶠ[𝓝 (0 : ℝ)] D3 := by
    filter_upwards [hHloc 0, hHloc 1, hHloc 2, hGloc 0, hGloc 1, hGloc 2]
      with z hH0z hH1z hH2z hG0z hG1z hG2z
    have hG0a : AnalyticAt ℝ G z := by simpa [iteratedDeriv_zero] using hG0z
    have hH1a : AnalyticAt ℝ (deriv H) (G z) := by
      simpa [iteratedDeriv_succ, iteratedDeriv_one] using hH1z
    have hG1a : AnalyticAt ℝ (deriv G) z := by
      simpa [iteratedDeriv_succ, iteratedDeriv_one] using hG1z
    have hH2a : AnalyticAt ℝ (iteratedDeriv 2 H) (G z) := hH2z
    have hG2a : AnalyticAt ℝ (iteratedDeriv 2 G) z := hG2z
    change deriv (((iteratedDeriv 2 H) ∘ G) * (deriv G ^ 2) +
      ((deriv H) ∘ G) * iteratedDeriv 2 G) z = _
    rw [deriv_add
      (((hH2a.comp hG0a).differentiableAt).mul (hG1a.differentiableAt.pow 2))
      (((hH1a.comp hG0a).differentiableAt).mul hG2a.differentiableAt)]
    rw [deriv_mul (hH2a.comp hG0a).differentiableAt (hG1a.differentiableAt.pow 2)]
    rw [deriv_mul (hH1a.comp hG0a).differentiableAt hG2a.differentiableAt]
    rw [deriv_comp z hH2a.differentiableAt hG0a.differentiableAt]
    rw [deriv_comp z hH1a.differentiableAt hG0a.differentiableAt]
    rw [deriv_pow hG1a.differentiableAt 2]
    simp only [hd2, hd3, Function.comp_apply, Pi.pow_apply]
    dsimp [D3]
    ring
  have hEq1 : D1 0 = 1 := hD1.eq_of_nhds
  have hEq1' : deriv H 0 * deriv G 0 = 1 := by simpa [D1, hG0] using hEq1
  have hH1ne : deriv H 0 ≠ 0 := by
    intro hh
    rw [hh, zero_mul] at hEq1'
    exact zero_ne_one hEq1'
  have hEq2 : D2 0 = 0 := by
    rw [← hD1der.eq_of_nhds]
    rw [hD1.deriv_eq]
    exact deriv_const 0 1
  have hG2 : iteratedDeriv 2 G 0 = 0 := by
    have he := hEq2
    dsimp [D2] at he
    rw [hG0, hH2] at he
    simp only [zero_mul, zero_add] at he
    exact (mul_eq_zero.mp he).resolve_left hH1ne
  have hderivD1 : (fun z => deriv D1 z) =ᶠ[𝓝 (0 : ℝ)] (fun _ => 0) := by
    have hloc : ∀ᶠ z in 𝓝 (0 : ℝ), D1 =ᶠ[𝓝 z] (fun _ => 1) :=
      eventually_eventually_nhds.2 hD1
    filter_upwards [hloc] with z hz
    rw [hz.deriv_eq]
    exact deriv_const z 1
  have hEq3 : D3 0 = 0 := by
    rw [← hD2der.eq_of_nhds]
    rw [← hD1der.deriv_eq]
    rw [hderivD1.deriv_eq]
    exact deriv_const 0 0
  refine ⟨hEq1', hG2, ?_⟩
  have he := hEq3
  dsimp [D3] at he
  simpa [hG0, hH2, hG2] using he

private lemma odd_iteratedDeriv_two_zero {H : ℝ → ℝ} (hH : AnalyticAt ℝ H 0)
    (hodd : ∀ᶠ t in 𝓝 (0 : ℝ), H (-t) = -H t) : iteratedDeriv 2 H 0 = 0 := by
  have hHtend : Filter.Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, neg_zero] using (continuousAt_neg (x := (0 : ℝ)))
  have hHloc : ∀ᶠ x in 𝓝 (0 : ℝ), AnalyticAt ℝ H (-x) :=
    hHtend.eventually hH.eventually_analyticAt
  have hlocodd : ∀ᶠ x in 𝓝 (0 : ℝ),
      (fun t => H (-t)) =ᶠ[𝓝 x] (fun t => -H t) := eventually_eventually_nhds.2 hodd
  have heven : (fun x => deriv H (-x)) =ᶠ[𝓝 (0 : ℝ)] deriv H := by
    filter_upwards [hHloc, hlocodd] with x hx hxodd
    have hchain : deriv (H ∘ (fun t : ℝ => -t)) x = - deriv H (-x) := by
      rw [deriv_comp x hx.differentiableAt (differentiableAt_id.neg)]
      simp
    have hd := hxodd.deriv_eq
    change deriv (H ∘ (fun t : ℝ => -t)) x = deriv (-H) x at hd
    rw [hchain, deriv.neg] at hd
    simpa using neg_eq_iff_eq_neg.mp hd
  have hn := heven.deriv_eq (x := (0 : ℝ))
  have hleft : deriv (fun x => deriv H (-x)) 0 = - deriv (deriv H) 0 := by
    change deriv ((deriv H) ∘ (fun t : ℝ => -t)) 0 = _
    rw [deriv_comp 0 (by simpa using hH.deriv.differentiableAt) (differentiableAt_id.neg)]
    simp
  have hd2 : deriv (deriv H) = iteratedDeriv 2 H := by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ (n := 1) (f := H), iteratedDeriv_one]
  change deriv (fun x => deriv H (-x)) 0 = deriv (deriv H) 0 at hn
  rw [hleft] at hn
  rw [← hd2]
  linarith

private lemma inverse_taylor_coefficients {H G : ℝ → ℝ}
    (hH : AnalyticAt ℝ H 0) (hodd : ∀ᶠ t in 𝓝 (0 : ℝ), H (-t) = -H t)
    (hG : AnalyticAt ℝ G 0) (hG0 : G 0 = 0)
    (hinv : ∀ᶠ z in 𝓝 (0 : ℝ), H (G z) = z)
    (hc : 0 < taylorCoeff 1 H) :
    taylorCoeff 1 G = 1 / taylorCoeff 1 H ∧
      taylorCoeff 3 G = -taylorCoeff 3 H / (taylorCoeff 1 H) ^ 4 := by
  obtain ⟨hc1, _, hc3⟩ := inv_coeff hH hG hG0 hinv (odd_iteratedDeriv_two_zero hH hodd)
  have ht1 (F : ℝ → ℝ) : taylorCoeff 1 F = deriv F 0 := by
    simp [taylorCoeff, iteratedDeriv_one]
  have ht3 (F : ℝ → ℝ) : iteratedDeriv 3 F 0 = 6 * taylorCoeff 3 F := by
    norm_num [taylorCoeff]
    ring
  have hcne : taylorCoeff 1 H ≠ 0 := ne_of_gt hc
  have hc1' : taylorCoeff 1 G * taylorCoeff 1 H = 1 := by
    simpa [ht1, mul_comm] using hc1
  have ha1 : taylorCoeff 1 G = 1 / taylorCoeff 1 H := (eq_div_iff hcne).2 hc1'
  rw [ht3 H, ht3 G, ← ht1 H, ← ht1 G] at hc3
  rw [ha1] at hc3
  refine ⟨ha1, ?_⟩
  field_simp
  field_simp at hc3
  nlinarith

private lemma majorant_barrier_aux (lam : ℝ) (hlam : 1 / 2 ≤ lam) {H : ℝ → ℝ}
    {b₁ b₃ γ : ℝ} (hH : AnalyticAt ℝ H 0)
    (hodd : ∀ᶠ t in 𝓝 (0 : ℝ), H (-t) = -H t)
    (hb1 : taylorCoeff 1 H = b₁) (hb3 : taylorCoeff 3 H = b₃)
    (hb1pos : 0 < b₁) (hb1le : b₁ ≤ 1) (hadm : IsAdmissible H γ)
    (hb3ge : b₃ ≥ (1 + lam) * b₁ - (lam + 5 / 6)) :
    γ ≤ (lam + 5 / 6) / (1 + lam) := by
  let Γ : ℝ := (lam + 5 / 6) / (1 + lam)
  have hApos : 0 < 1 + lam := by linarith
  have hΓpos : 0 < Γ := by
    dsimp [Γ]
    exact div_pos (by linarith) hApos
  have hAΓ : (1 + lam) * Γ = lam + 5 / 6 := by
    dsimp [Γ]
    field_simp
  have hΓcube : 1 < (lam + 1) * Γ ^ 3 := by
    have hpoly : (lam + 1) ^ 2 < (lam + 5 / 6) ^ 3 := by
      let δ : ℝ := lam - 1 / 2
      have hδ : 0 ≤ δ := by dsimp [δ]; linarith
      have hexp : (lam + 5 / 6) ^ 3 - (lam + 1) ^ 2 =
          δ ^ 3 + 3 * δ ^ 2 + 7 / 3 * δ + 13 / 108 := by
        dsimp [δ]
        ring
      have hpos : 0 < (lam + 5 / 6) ^ 3 - (lam + 1) ^ 2 := by
        rw [hexp]
        positivity
      linarith
    have hid : (lam + 1) * Γ ^ 3 = (lam + 5 / 6) ^ 3 / (lam + 1) ^ 2 := by
      dsimp [Γ]
      field_simp
      ring
    rw [hid]
    exact (lt_div_iff₀ (sq_pos_of_pos (by linarith : 0 < lam + 1))).2 (by simpa using hpoly)
  change γ ≤ Γ
  have hγpos : 0 < γ := hadm.2.2.2.1
  rcases hadm.2.2.2.2 with ⟨G, ⟨hG, hG0, hGinv⟩, hsum, hAle⟩
  have hb1pos' : 0 < taylorCoeff 1 H := by simpa [hb1] using hb1pos
  obtain ⟨ha1, ha3⟩ := inverse_taylor_coefficients hH hodd hG hG0 hGinv hb1pos'
  rw [hb1] at ha1 ha3
  rw [hb3] at ha3
  let A : ℕ → ℝ := fun j => |taylorCoeff (2 * j + 1) G| * γ ^ (2 * j + 1)
  have hAnonneg : ∀ j, 0 ≤ A j := by
    intro j
    exact mul_nonneg (abs_nonneg _) (pow_nonneg hγpos.le _)
  have hfinite (s : Finset ℕ) : ∑ j ∈ s, A j ≤ 1 :=
    (hsum.sum_le_tsum s (fun i _ => hAnonneg i)).trans hAle
  by_cases hsmall : b₁ ≤ Γ
  · have h0 := hfinite {0}
    simp [A, ha1] at h0
    rw [abs_of_pos hb1pos] at h0
    have hgamma : γ ≤ b₁ := by
      have hd : γ / b₁ ≤ 1 := by
        calc
          γ / b₁ = (1 / b₁) * γ := by ring
          _ ≤ 1 := by simpa [one_div] using h0
      simpa using (div_le_iff₀ hb1pos).mp hd
    exact hgamma.trans hsmall
  · have hlarge : Γ < b₁ := lt_of_not_ge hsmall
    by_contra hn
    have hΓ : Γ < γ := lt_of_not_ge hn
    have hb3ge' : (1 + lam) * (b₁ - Γ) ≤ b₃ := by
      rw [mul_sub, hAΓ]
      exact hb3ge
    have hb3pos : 0 < b₃ := by
      have : 0 < (1 + lam) * (b₁ - Γ) :=
        mul_pos hApos (sub_pos.mpr hlarge)
      linarith
    have hb14pos : 0 < b₁ ^ 4 := pow_pos hb1pos 4
    have ha1pos : 0 < |1 / b₁| := abs_pos.mpr (ne_of_gt (one_div_pos.mpr hb1pos))
    have habsa3 : |(-b₃) / b₁ ^ 4| = b₃ / b₁ ^ 4 := by
      rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb3pos.le) hb14pos.le)]
      ring
    have ha3ge : (1 + lam) * (b₁ - Γ) / b₁ ^ 4 ≤ |(-b₃) / b₁ ^ 4| := by
      rw [habsa3]
      exact (div_le_div_iff_of_pos_right hb14pos).2 hb3ge'
    rw [← ha1] at ha1pos
    rw [← ha3] at ha3ge
    have htwo := hfinite ({0, 1} : Finset ℕ)
    norm_num [A] at htwo
    have hbase1 : |taylorCoeff 1 G| * Γ = Γ / b₁ := by
      rw [ha1, abs_of_pos (one_div_pos.mpr hb1pos)]
      ring
    have hbase : 1 < |taylorCoeff 1 G| * Γ + |taylorCoeff 3 G| * Γ ^ 3 := by
      rw [hbase1]
      have hb13le : b₁ ^ 3 ≤ 1 := pow_le_one₀ hb1pos.le hb1le
      have hfactor : 0 < (b₁ - Γ) * ((lam + 1) * Γ ^ 3 - b₁ ^ 3) := by
        apply mul_pos (sub_pos.mpr hlarge)
        linarith
      have hnum : 0 < (b₁ - Γ) * ((lam + 1) * Γ ^ 3 - b₁ ^ 3) / b₁ ^ 4 :=
        div_pos hfactor hb14pos
      have hid : Γ / b₁ + ((1 + lam) * (b₁ - Γ) / b₁ ^ 4) * Γ ^ 3 =
          1 + (b₁ - Γ) * ((lam + 1) * Γ ^ 3 - b₁ ^ 3) / b₁ ^ 4 := by
        field_simp
        ring
      have hcub := mul_le_mul_of_nonneg_right ha3ge (pow_nonneg hΓpos.le 3)
      linarith
    have hp₀ : |taylorCoeff 1 G| * Γ < |taylorCoeff 1 G| * γ :=
      mul_lt_mul_of_pos_left hΓ ha1pos
    have hp₃ : |taylorCoeff 3 G| * Γ ^ 3 ≤ |taylorCoeff 3 G| * γ ^ 3 := by
      have hpow : Γ ^ 3 ≤ γ ^ 3 := by
        exact (pow_lt_pow_left₀ hΓ hΓpos.le (by norm_num)).le
      exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    linarith

end GrothendieckLB

open GrothendieckLB

theorem solution (lam : ℝ) (hlam : 1 / 2 ≤ lam) {H : ℝ → ℝ}
    (hodd : ∀ᶠ t in 𝓝 (0 : ℝ), H (-t) = -H t)
    (han : AnalyticAt ℝ H 0) (hb₁ : 0 < taylorCoeff 1 H) (hb₁' : taylorCoeff 1 H ≤ 1)
    (hb₃ : (1 + lam) * taylorCoeff 1 H - (lam + 5 / 6) ≤ taylorCoeff 3 H)
    {γ : ℝ} (hγ : IsAdmissible H γ) :
    γ ≤ (lam + 5 / 6) / (1 + lam) := by
  exact majorant_barrier_aux lam hlam han hodd rfl rfl hb₁ hb₁' hγ hb₃
