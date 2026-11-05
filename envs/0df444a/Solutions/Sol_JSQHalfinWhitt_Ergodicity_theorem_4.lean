-- Prove2me | solution 1 for JSQHalfinWhitt.Ergodicity.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T21:21:46.603181+00:00
-- url     : https://prove2.me/submissions/79f98d84-bd7d-4928-99f2-53b81a666ca3

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Ergodicity_Operators

open JSQHalfinWhitt.Ergodicity JSQHalfinWhitt.Tightness

lemma jsq4_hasV (θ γ κ0 : ℝ) (x : ℝ × ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ => Real.exp (θ * (x.1 + x.2) + γ / 2 * x.1 ^ 2 + κ0))
      (((θ + γ * x.1) * Real.exp (θ * (x.1 + x.2) + γ / 2 * x.1 ^ 2 + κ0)) •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        (θ * Real.exp (θ * (x.1 + x.2) + γ / 2 * x.1 ^ 2 + κ0)) •
          ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  have hf : HasFDerivAt (fun x : ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) x := hasFDerivAt_fst
  have hs : HasFDerivAt (fun x : ℝ × ℝ => x.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) x := hasFDerivAt_snd
  have h1 := ((((hf.add hs).const_mul θ).add ((hf.pow 2).const_mul (γ / 2))).add_const κ0).exp
  refine h1.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp
  ring

lemma jsq4_hasV1 (θ γ κ0 : ℝ) (x : ℝ × ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ => (θ + γ * x.1) * Real.exp (θ * (x.1 + x.2) + γ / 2 * x.1 ^ 2 + κ0))
      ((γ * Real.exp (θ * (x.1 + x.2) + γ / 2 * x.1 ^ 2 + κ0) + (θ + γ * x.1) *
          ((θ + γ * x.1) * Real.exp (θ * (x.1 + x.2) + γ / 2 * x.1 ^ 2 + κ0))) •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        ((θ + γ * x.1) * (θ * Real.exp (θ * (x.1 + x.2) + γ / 2 * x.1 ^ 2 + κ0))) •
          ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  have hf : HasFDerivAt (fun x : ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) x := hasFDerivAt_fst
  have h1 := ((hf.const_mul γ).const_add θ).mul (jsq4_hasV θ γ κ0 x)
  refine h1.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp
  ring

lemma jsq4_partials {f : ℝ × ℝ → ℝ} {a b : ℝ} {x : ℝ × ℝ} (hx : x ∈ Omega)
    (h : HasFDerivAt f (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) x) :
    d1 f x = a ∧ d2 f x = b := by
  have hU : UniqueDiffOn ℝ Omega := (uniqueDiffOn_Iic (0 : ℝ)).prod (uniqueDiffOn_Ici (0 : ℝ))
  have := h.hasFDerivWithinAt.fderivWithin (hU x hx)
  simp [d1, d2, this]

lemma jsq4_Q (γ A L C0 T X δ c x1 x2 : ℝ) (hγ : 0 < γ) (hA : 0 < A) (hL : 0 < L)
    (hc : c = -C0 / 2) (hcpos : 0 < c) (hδ : L * δ = c) (hδpos : 0 < δ) (hAT : A * T = L)
    (hX : γ * δ * X = L * T) (hx1 : x1 ≤ 0) (hx2 : 0 ≤ x2) (hout : x1 < -T ∨ X < x2) :
    -A * x1 ^ 2 + γ * x1 * x2 - L * x1 + C0 ≤ -c := by
  have hm : γ * x1 * x2 ≤ 0 := by
    have := mul_nonpos_of_nonpos_of_nonneg hx1 hx2
    have := mul_nonpos_of_nonneg_of_nonpos hγ.le this
    linarith [mul_assoc γ x1 x2]
  have hsq : 0 ≤ A * x1 ^ 2 := by positivity
  by_cases h1 : -δ ≤ x1
  · have : -L * x1 ≤ L * δ := by nlinarith
    linarith
  push Not at h1
  rcases hout with h2 | h2
  · have : A * x1 ^ 2 + L * x1 ≥ 0 := by
      have e : A * x1 ^ 2 + L * x1 = (-x1) * (A * (-x1) - A * T) := by rw [← hAT]; ring
      rw [e]
      apply mul_nonneg (by linarith)
      nlinarith
    linarith
  · by_cases h3 : x1 < -T
    · have : A * x1 ^ 2 + L * x1 ≥ 0 := by
        have e : A * x1 ^ 2 + L * x1 = (-x1) * (A * (-x1) - A * T) := by rw [← hAT]; ring
        rw [e]
        apply mul_nonneg (by linarith)
        nlinarith
      linarith
    push Not at h3
    have h4 : γ * x1 * x2 ≤ -(γ * δ * x2) := by
      have : 0 ≤ (-x1 - δ) * x2 := mul_nonneg (by linarith) hx2
      have := mul_nonneg hγ.le this
      nlinarith
    have h5 : γ * δ * X ≤ γ * δ * x2 := by
      have : 0 < γ * δ := mul_pos hγ hδpos
      exact mul_le_mul_of_nonneg_left h2.le this.le
    have h6 : -L * x1 ≤ L * T := by nlinarith
    linarith

theorem solution (β : ℝ) (hβ : 0 < β) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∃ K : Set (ℝ × ℝ), IsCompact K ∧
      ∃ V : ℝ × ℝ → ℝ, ContDiffOn ℝ 2 V JSQHalfinWhitt.Tightness.Omega ∧ (∀ x ∈ JSQHalfinWhitt.Tightness.Omega, 1 ≤ V x) ∧
        (∀ M : ℝ, ∃ R : ℝ, ∀ x ∈ JSQHalfinWhitt.Tightness.Omega, R ≤ ‖x‖ → M ≤ V x) ∧
        (∀ x2 : ℝ, 0 ≤ x2 → d1 V (0, x2) = d2 V (0, x2)) ∧
        ∀ x ∈ JSQHalfinWhitt.Tightness.Omega, genY β V x ≤ -c * V x + d * K.indicator (fun _ => (1 : ℝ)) x := by
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = β / 2 := ⟨_, rfl⟩
  obtain ⟨γ, hγpos, hγ1, hγ2⟩ : ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 / 2 ∧ γ ≤ β ^ 2 / 8 :=
    ⟨min (1 / 2) (β ^ 2 / 8), lt_min (by norm_num) (by positivity), min_le_left _ _,
      min_le_right _ _⟩
  have hθpos : 0 < θ := by rw [hθ]; positivity
  obtain ⟨κ0, hκ0⟩ : ∃ κ0 : ℝ, κ0 = θ ^ 2 / (2 * γ) := ⟨_, rfl⟩
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, C0 = θ ^ 2 - θ * β + γ := ⟨_, rfl⟩
  have hC0neg : C0 < 0 := by rw [hC0, hθ]; nlinarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = θ + γ * β - 2 * θ * γ := ⟨_, rfl⟩
  have hLpos : 0 < L := by
    rw [hL]
    have : 0 ≤ θ * (1 - 2 * γ) := mul_nonneg hθpos.le (by linarith)
    nlinarith [mul_pos hγpos hβ]
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = γ * (1 - γ) := ⟨_, rfl⟩
  have hApos : 0 < A := by rw [hA]; exact mul_pos hγpos (by linarith)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = -C0 / 2 := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = c / L := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; exact div_pos hcpos hLpos
  have hLδ : L * δ = c := by rw [hδ]; field_simp
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = L / A := ⟨_, rfl⟩
  have hAT : A * T = L := by rw [hT]; field_simp
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = L * T / (γ * δ) := ⟨_, rfl⟩
  have hγδX : γ * δ * X = L * T := by rw [hX]; field_simp
  -- the Lyapunov function
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ × ℝ → ℝ,
      V = fun x => Real.exp (θ * (x.1 + x.2) + γ / 2 * x.1 ^ 2 + κ0) := ⟨_, rfl⟩
  have hVpos : ∀ x, 0 < V x := fun x => by rw [hVdef]; exact Real.exp_pos _
  have hV : ∀ x : ℝ × ℝ, HasFDerivAt V
      (((θ + γ * x.1) * V x) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (θ * V x) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
    intro x; rw [hVdef]; exact jsq4_hasV θ γ κ0 x
  have hV1 : ∀ x : ℝ × ℝ, HasFDerivAt (fun y : ℝ × ℝ => (θ + γ * y.1) * V y)
      ((γ * V x + (θ + γ * x.1) * ((θ + γ * x.1) * V x)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        ((θ + γ * x.1) * (θ * V x)) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
    intro x; rw [hVdef]; exact jsq4_hasV1 θ γ κ0 x
  have hd1 : ∀ x ∈ Omega, d1 V x = (θ + γ * x.1) * V x := fun x hx => (jsq4_partials hx (hV x)).1
  have hd2 : ∀ x ∈ Omega, d2 V x = θ * V x := fun x hx => (jsq4_partials hx (hV x)).2
  have hd11 : ∀ x ∈ Omega, d11 V x = γ * V x + (θ + γ * x.1) * ((θ + γ * x.1) * V x) := by
    intro x hx
    have hcongr : fderivWithin ℝ (d1 V) Omega x =
        fderivWithin ℝ (fun y : ℝ × ℝ => (θ + γ * y.1) * V y) Omega x :=
      fderivWithin_congr (fun y hy => hd1 y hy) (hd1 x hx)
    have := (jsq4_partials hx (hV1 x)).1
    simp only [d11]
    rw [d1, hcongr]
    exact this
  have hgen : ∀ x ∈ Omega, genY β V x =
      (-A * x.1 ^ 2 + γ * x.1 * x.2 - L * x.1 + C0) * V x := by
    intro x hx
    simp only [genY]
    rw [hd1 x hx, hd2 x hx, hd11 x hx, hA, hL, hC0]
    ring
  -- the compact set
  obtain ⟨K, hK⟩ : ∃ K : Set (ℝ × ℝ), K = Set.Icc (-T) 0 ×ˢ Set.Icc 0 X := ⟨_, rfl⟩
  have hKc : IsCompact K := by rw [hK]; exact isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn
      (fun x : ℝ × ℝ => (-A * x.1 ^ 2 + γ * x.1 * x.2 - L * x.1 + C0 + c) * V x) K := by
    apply Continuous.continuousOn
    rw [hVdef]
    fun_prop
  obtain ⟨B, hB⟩ := hKc.bddAbove_image hcont
  refine ⟨c, max B 1, hcpos, lt_of_lt_of_le one_pos (le_max_right _ _), K, hKc, V, ?_, ?_, ?_, ?_, ?_⟩
  · apply ContDiff.contDiffOn
    rw [hVdef]
    fun_prop
  · intro x hx
    have hx2 : 0 ≤ x.2 := hx.2
    rw [hVdef]
    have e : θ * (x.1 + x.2) + γ / 2 * x.1 ^ 2 + κ0 =
        θ * x.2 + γ / 2 * (x.1 + θ / γ) ^ 2 := by
      rw [hκ0]; field_simp; ring
    have : 0 ≤ θ * (x.1 + x.2) + γ / 2 * x.1 ^ 2 + κ0 := by
      rw [e]; have := mul_nonneg hθpos.le hx2; positivity
    exact Real.one_le_exp this
  · intro M
    refine ⟨(|M| + 3 * θ ^ 2 / (2 * γ)) / θ, ?_⟩
    intro x hx hR
    have hx1 : x.1 ≤ 0 := hx.1
    have hx2 : 0 ≤ x.2 := hx.2
    have hnorm : ‖x‖ ≤ -x.1 + x.2 := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos hx1, abs_of_nonneg hx2]
      exact max_le (by linarith) (by linarith)
    have hR' : (|M| + 3 * θ ^ 2 / (2 * γ)) ≤ θ * (-x.1 + x.2) := by
      rw [div_le_iff₀ hθpos] at hR
      have := mul_le_mul_of_nonneg_right hnorm hθpos.le
      linarith
    have hsq : 0 ≤ γ / 2 * (x.1 + 2 * θ / γ) ^ 2 := by positivity
    have e : γ / 2 * (x.1 + 2 * θ / γ) ^ 2 = γ / 2 * x.1 ^ 2 + 2 * θ * x.1 + 2 * θ ^ 2 / γ := by
      field_simp; ring
    have e2 : 3 * θ ^ 2 / (2 * γ) = 2 * θ ^ 2 / γ - κ0 := by rw [hκ0]; field_simp; ring
    rw [e2] at hR'
    have hφ : |M| ≤ θ * (x.1 + x.2) + γ / 2 * x.1 ^ 2 + κ0 := by nlinarith
    have h1 := Real.add_one_le_exp (θ * (x.1 + x.2) + γ / 2 * x.1 ^ 2 + κ0)
    have h2 := le_abs_self M
    rw [hVdef]
    show M ≤ Real.exp _
    linarith
  · intro x2 hx2
    have hx : ((0 : ℝ), x2) ∈ Omega := ⟨Set.mem_Iic.2 le_rfl, Set.mem_Ici.2 hx2⟩
    rw [hd1 _ hx, hd2 _ hx]
    simp
  · intro x hx
    have hx1 : x.1 ≤ 0 := hx.1
    have hx2 : 0 ≤ x.2 := hx.2
    rw [hgen x hx]
    have hVx := hVpos x
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem hxK]
      have h1 : (-A * x.1 ^ 2 + γ * x.1 * x.2 - L * x.1 + C0 + c) * V x ≤ B := hB ⟨x, hxK, rfl⟩
      have h2 := le_max_left B 1
      have e : (-A * x.1 ^ 2 + γ * x.1 * x.2 - L * x.1 + C0 + c) * V x =
        (-A * x.1 ^ 2 + γ * x.1 * x.2 - L * x.1 + C0) * V x + c * V x := by ring
      linarith
    · rw [Set.indicator_of_notMem hxK]
      have hout : x.1 < -T ∨ X < x.2 := by
        by_contra hcon
        push Not at hcon
        apply hxK
        rw [hK]
        exact ⟨⟨hcon.1, hx1⟩, ⟨hx2, hcon.2⟩⟩
      have hQ := jsq4_Q γ A L C0 T X δ c x.1 x.2 hγpos hApos hLpos hc hcpos hLδ hδpos hAT hγδX
        hx1 hx2 hout
      have := mul_le_mul_of_nonneg_right hQ hVx.le
      linarith
