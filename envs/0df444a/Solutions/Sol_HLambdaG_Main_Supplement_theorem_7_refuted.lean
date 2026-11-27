-- Prove2me | solution 1 for HLambdaG.Main.Supplement.theorem_7_refuted
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:26:12.840087+00:00
-- url     : https://prove2.me/submissions/7ebe6aa5-fea8-4889-ad0f-058a479248ef

import Mathlib
import Definitions.Def_HLambdaG_Main_Supplement_FCLTExamples

open scoped NNReal

open HLambdaG
open HLambdaG.Main
open HLambdaG.Main.Supplement

open Filter Topology

/-- Refutation of Theorem 7 as printed, including (27) with G,H as the averages (1).
Take λ = g = h = 1, F(s,t) = min(s,B(t))², T₁ = T₂ = s + √s, S₁ = S₂ = B.
The remainders vanish; G(s) = s. All paths are deterministic, so convergence uniformly
on compact intervals to continuous limits implies the required J₁ weak convergence.
The actual limits S = -√t, H = -2√t refute both the '=ᵈ' claim S =ᵈ T and the
transformation H = G - T in (30). No cumulative reinterpretation of G or H is used. -/
theorem solution :
    Continuous curvedT ∧ Monotone curvedT ∧ Tendsto curvedT atTop atTop ∧
    Continuous curvedS ∧ Monotone curvedS ∧
    (∀ t : ℝ≥0, curvedS t = sInf {s : ℝ | 0 ≤ s ∧ (t : ℝ) < s + Real.sqrt s}) ∧
    (∀ t : ℝ≥0, Monotone (fun s => curvedF s t) ∧
      Tendsto (fun s => curvedF s t) atTop (𝓝 ((curvedS t) ^ 2))) ∧
    (∀ s : ℝ≥0, Monotone (curvedF s) ∧
      Tendsto (curvedF s) atTop (𝓝 ((s : ℝ) ^ 2))) ∧
    (∀ s : ℝ≥0, curvedS (⟨curvedT s, by unfold curvedT; positivity⟩ : ℝ≥0) = s ∧
      curvedF s ⟨curvedT s, by unfold curvedT; positivity⟩ = (s : ℝ) ^ 2) ∧
    CompactConvergence (diffusion (fun s => (s : ℝ))) (fun _ => 0) ∧
    CompactConvergence (diffusion curvedT) (fun t => Real.sqrt t) ∧
    CompactConvergence (diffusion curvedS) (fun t => -Real.sqrt t) ∧
    CompactConvergence (diffusion curvedH) (fun t => -2 * Real.sqrt t) ∧
    (-Real.sqrt (1 : ℝ) ≠ Real.sqrt (1 : ℝ)) ∧
    (-2 * Real.sqrt (1 : ℝ) ≠ 0 - Real.sqrt (1 : ℝ)) := by
      have hsq1 : ∀ t : ℝ≥0, 1 ≤ Real.sqrt (1 + 4 * (t:ℝ)) := fun t => by
        rw [Real.le_sqrt (by norm_num) (by positivity)]
        have := t.2
        nlinarith
      have hu : ∀ t : ℝ≥0, 0 ≤ (Real.sqrt (1 + 4 * (t:ℝ)) - 1) / 2 ∧
          ((Real.sqrt (1 + 4 * (t:ℝ)) - 1) / 2) ^ 2 + (Real.sqrt (1 + 4 * (t:ℝ)) - 1) / 2 = t := by
        intro t
        have h := Real.sq_sqrt (show (0:ℝ) ≤ 1 + 4 * (t:ℝ) by positivity)
        refine ⟨by linarith [hsq1 t], ?_⟩
        linear_combination (1/4 : ℝ) * h
      have hS_eq : ∀ t : ℝ≥0, curvedS t = (t:ℝ) - (Real.sqrt (1 + 4 * (t:ℝ)) - 1) / 2 := by
        intro t; unfold curvedS; linarith [(hu t).2]
      have hSnn : ∀ t, 0 ≤ curvedS t := fun t => by unfold curvedS; positivity
      have hSmono : Monotone curvedS := by
        intro a b hab
        have hab' : (a:ℝ) ≤ b := hab
        unfold curvedS
        apply pow_le_pow_left₀ (hu a).1
        have : Real.sqrt (1 + 4 * (a:ℝ)) ≤ Real.sqrt (1 + 4 * (b:ℝ)) :=
          Real.sqrt_le_sqrt (by linarith)
        linarith
      have h9' : ∀ s : ℝ≥0, ((Real.sqrt (1 + 4 * ((s:ℝ) + Real.sqrt s)) - 1) / 2) ^ 2 = s := by
        intro s
        have hs := Real.sq_sqrt (NNReal.coe_nonneg s)
        have : 1 + 4 * ((s:ℝ) + Real.sqrt s) = (1 + 2 * Real.sqrt s) ^ 2 := by
          linear_combination (-4 : ℝ) * hs
        rw [this, Real.sqrt_sq (by positivity)]
        rw [show (1 + 2 * Real.sqrt s - 1) / 2 = Real.sqrt s by ring]
        exact hs
      have h9 : ∀ s : ℝ≥0, curvedS (⟨curvedT s, by unfold curvedT; positivity⟩ : ℝ≥0) = s :=
        fun s => h9' s
      have hcast : ∀ (n : ℕ) (t : ℝ≥0), (((n:ℝ≥0) * t : ℝ≥0) : ℝ) = (n:ℝ) * (t:ℝ) := by
        intro n t; push_cast; rfl
      have hbnd : ∀ x : ℝ, 0 ≤ x → Real.sqrt x - 1/2 ≤ (Real.sqrt (1 + 4 * x) - 1) / 2 ∧
          (Real.sqrt (1 + 4 * x) - 1) / 2 ≤ Real.sqrt x := by
        intro x hx
        have hs := Real.sq_sqrt hx
        have hs0 := Real.sqrt_nonneg x
        constructor
        · have : 2 * Real.sqrt x ≤ Real.sqrt (1 + 4 * x) := by
            rw [Real.le_sqrt (by positivity) (by positivity)]
            nlinarith
          linarith
        · have : Real.sqrt (1 + 4 * x) ≤ 1 + 2 * Real.sqrt x := by
            rw [Real.sqrt_le_left (by positivity)]
            nlinarith
          linarith
      have hev : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt (n:ℝ) ∧ 1 / Real.sqrt (n:ℝ) < ε := by
        intro ε hε
        have hlim : Tendsto (fun n : ℕ => 1 / Real.sqrt (n:ℝ)) atTop (𝓝 0) := by
          have := tendsto_inv_atTop_zero.comp
            (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
          simpa [one_div, Function.comp_def] using this
        filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with n h1 h2
        exact ⟨Real.sqrt_pos.2 (Nat.cast_pos.mpr (by omega)), h1⟩
      refine ⟨?_, ?_, ?_, ?_, hSmono, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · unfold curvedT; fun_prop
      · intro a b hab
        have hab' : (a:ℝ) ≤ b := hab
        unfold curvedT
        have := Real.sqrt_le_sqrt hab'
        linarith
      · refine tendsto_atTop_mono (fun s => ?_) (NNReal.tendsto_coe_atTop.2 tendsto_id)
        unfold curvedT
        simp only [id]
        linarith [Real.sqrt_nonneg (s:ℝ)]
      · unfold curvedS; fun_prop
      · intro t
        have hb := hS_eq t
        have hu0 := (hu t).1
        have hsqb : Real.sqrt (curvedS t) = (Real.sqrt (1 + 4 * (t:ℝ)) - 1) / 2 := by
          unfold curvedS; exact Real.sqrt_sq hu0
        have hset : {s : ℝ | 0 ≤ s ∧ (t : ℝ) < s + Real.sqrt s} = Set.Ioi (curvedS t) := by
          ext s
          simp only [Set.mem_ofPred_eq, Set.mem_Ioi]
          constructor
          · rintro ⟨hs0, hlt⟩
            by_contra h
            push Not at h
            have := Real.sqrt_le_sqrt h
            linarith
          · intro h
            have := Real.sqrt_lt_sqrt (hSnn t) h
            exact ⟨by linarith [hSnn t], by linarith⟩
        rw [hset, csInf_Ioi]
      · intro t
        refine ⟨fun a b hab => ?_, ?_⟩
        · have hab' : (a:ℝ) ≤ b := hab
          simp only [curvedF]
          exact pow_le_pow_left₀ (le_min a.2 (hSnn t)) (min_le_min_right _ hab') 2
        · apply tendsto_const_nhds.congr'
          filter_upwards [eventually_ge_atTop (curvedS t).toNNReal] with s hs
          have := Real.toNNReal_le_iff_le_coe.1 hs
          simp only [curvedF]
          rw [min_eq_right this]
      · intro s
        refine ⟨fun a b hab => ?_, ?_⟩
        · simp only [curvedF]
          exact pow_le_pow_left₀ (le_min s.2 (hSnn a)) (min_le_min_left _ (hSmono hab)) 2
        · apply tendsto_const_nhds.congr'
          filter_upwards [eventually_ge_atTop
            (⟨curvedT s, by unfold curvedT; positivity⟩ : ℝ≥0)] with t ht
          have := hSmono ht
          rw [h9] at this
          simp only [curvedF]
          rw [min_eq_left this]
      · intro s
        refine ⟨h9 s, ?_⟩
        simp only [curvedF]
        rw [h9, min_self]
      · intro a ε hε
        filter_upwards with n t _
        simp only [diffusion, hcast, sub_self, zero_div, abs_zero]
        exact hε
      · intro a ε hε
        filter_upwards [hev ε hε] with n hn t _
        obtain ⟨hc, _⟩ := hn
        simp only [diffusion, curvedT, hcast]
        rw [Real.sqrt_mul (Nat.cast_nonneg _),
          show (n:ℝ) * t + Real.sqrt n * Real.sqrt t - n * t = Real.sqrt n * Real.sqrt t by ring,
          mul_div_cancel_left₀ _ hc.ne']
        simpa using hε
      · intro a ε hε
        filter_upwards [hev ε hε] with n hn t _
        obtain ⟨hc, hlt⟩ := hn
        simp only [diffusion]
        rw [hS_eq, hcast]
        have hx : 0 ≤ (n:ℝ) * t := by positivity
        obtain ⟨hl, hr⟩ := hbnd _ hx
        rw [Real.sqrt_mul (Nat.cast_nonneg _)] at hl hr
        set c := Real.sqrt (n:ℝ)
        set q := Real.sqrt (t:ℝ)
        set u := (Real.sqrt (1 + 4 * ((n:ℝ) * t)) - 1) / 2
        have heq : ((n:ℝ) * t - u - n * t) / c - -q = (c * q - u) / c := by
          field_simp; ring
        rw [heq, abs_lt]
        constructor
        · have : 0 ≤ (c * q - u) / c := div_nonneg (by linarith) hc.le
          linarith
        · have : (c * q - u) / c ≤ 1 / c := div_le_div_of_nonneg_right (by linarith) hc.le
          linarith
      · intro a ε hε
        filter_upwards [hev (ε/2) (by linarith)] with n hn t _
        obtain ⟨hc, hlt⟩ := hn
        simp only [diffusion, curvedH]
        rw [hS_eq, hcast]
        have hx : 0 ≤ (n:ℝ) * t := by positivity
        obtain ⟨hl, hr⟩ := hbnd _ hx
        have hu0 : 0 ≤ (Real.sqrt (1 + 4 * ((n:ℝ) * t)) - 1) / 2 := (hu ((n:ℝ≥0) * t)).1.trans_eq
          (by rw [hcast])
        have hsx := Real.sq_sqrt hx
        set x := (n:ℝ) * t with hxdef
        set u := (Real.sqrt (1 + 4 * x) - 1) / 2
        have hw : 0 ≤ (x - u) ^ 2 / x - x + 2 * u ∧ (x - u) ^ 2 / x - x + 2 * u ≤ 1 := by
          by_cases hx0 : x = 0
          · have : u = 0 := by
              have : Real.sqrt x = 0 := by rw [hx0, Real.sqrt_zero]
              linarith
            rw [hx0, this]; norm_num
          · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
            have : (x - u) ^ 2 / x - x + 2 * u = u ^ 2 / x := by
              field_simp; ring
            rw [this]
            refine ⟨by positivity, div_le_one_of_le₀ ?_ hx⟩
            have : u ^ 2 ≤ (Real.sqrt x) ^ 2 := pow_le_pow_left₀ hu0 hr 2
            linarith
        have hsq : Real.sqrt x = Real.sqrt n * Real.sqrt t := Real.sqrt_mul (Nat.cast_nonneg _) _
        rw [hsq] at hl hr
        set c := Real.sqrt (n:ℝ)
        set q := Real.sqrt (t:ℝ)
        set w := (x - u) ^ 2 / x - x + 2 * u with hwdef
        have heq : ((x - u) ^ 2 / x - x) / c - -2 * q = (w + 2 * (c * q - u)) / c := by
          rw [hwdef]; field_simp; ring
        rw [heq, abs_lt]
        constructor
        · have : 0 ≤ (w + 2 * (c * q - u)) / c := div_nonneg (by linarith) hc.le
          linarith
        · have : (w + 2 * (c * q - u)) / c ≤ 2 / c := div_le_div_of_nonneg_right (by linarith) hc.le
          have h2 : 2 / c = 2 * (1 / c) := by ring
          linarith
      · rw [Real.sqrt_one]; norm_num
      · rw [Real.sqrt_one]; norm_num
