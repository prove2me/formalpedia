-- Prove2me | solution 2 for NAPPAL.Rate.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T23:52:35.757366+00:00
-- url     : https://prove2.me/submissions/15b2233a-aab0-428e-b1e0-b63c55b8ff69

import Mathlib
import Definitions.Def_NAPPAL_Rate_Setting
import Theorems.Thm_NAPPAL_Rate_proposition_3_1
import Theorems.Thm_NAPPAL_Rate_lemma_4_1
import Theorems.Thm_NAPPAL_Rate_lemma_4_3
open Filter Topology
open scoped InnerProductSpace
open NAPPAL.KL NAPPAL.Rate

namespace NAPPALP41

/-! Helper estimates (descent lemma, Rayleigh quotient); the first four follow the accepted
platform proof of Lemma 4.3. -/

theorem scalar_upper (g dg : ℝ → ℝ) (L : ℝ)
    (hd : ∀ t, HasDerivAt g (dg t) t)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, dg t - dg 0 ≤ L * t) :
    g 1 - g 0 ≤ dg 0 + L / 2 := by
  let f := fun t => g t - dg 0 * t - L / 2 * t ^ 2
  have hf (t : ℝ) : HasDerivAt f (dg t - dg 0 - L * t) t := by
    convert! ((hd t).sub ((hasDerivAt_id t).const_mul (dg 0))).sub
      (((hasDerivAt_id t).pow 2).const_mul (L / 2)) using 1
    dsimp [f]
    ring
  have ha : AntitoneOn f (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hf t).continuousAt.continuousWithinAt
    · exact fun t _ => (hf t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hf t).deriv]
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
      linarith only [hb t ht']
  have h := ha (by simp : (0 : ℝ) ∈ Set.Icc 0 1) (by simp : (1 : ℝ) ∈ Set.Icc 0 1) zero_le_one
  dsimp [f] at h
  norm_num at h
  linarith

theorem scalar_abs (g dg : ℝ → ℝ) (L : ℝ)
    (hd : ∀ t, HasDerivAt g (dg t) t)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, |dg t - dg 0| ≤ L * t) :
    |g 1 - g 0 - dg 0| ≤ L / 2 := by
  have hu := scalar_upper g dg L hd (fun t ht => (le_abs_self _).trans (hb t ht))
  have hl := scalar_upper (fun t => -g t) (fun t => -dg t) L (fun t => (hd t).neg)
    (fun t ht => by have hh := (abs_le.mp (hb t ht)).1; linarith only [hh])
  apply abs_le.mpr
  constructor <;> linarith

theorem gradient_taylor {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (f : X → ℝ) (L : ℝ) (hf : Differentiable ℝ f)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x y : X) :
    |f y - f x - ⟪gradient f x, y - x⟫_ℝ| ≤ L / 2 * ‖y - x‖ ^ 2 := by
  let d := y - x
  let g := fun t : ℝ => f (x + t • d)
  let dg := fun t : ℝ => ⟪gradient f (x + t • d), d⟫_ℝ
  have hd (t : ℝ) : HasDerivAt g (dg t) t := by
    have hh := (hf _).hasFDerivAt.comp_hasDerivAt t (((hasDerivAt_id t).smul_const d).const_add x)
    convert! hh using 1
    simp only [dg, inner_gradient_left, id_eq, one_smul]
  have hb (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : |dg t - dg 0| ≤ (L * ‖d‖ ^ 2) * t := by
    dsimp [dg]
    simp only [zero_smul, add_zero, ← inner_sub_left]
    calc
      _ ≤ ‖gradient f (x + t • d) - gradient f x‖ * ‖d‖ := abs_real_inner_le_norm _ _
      _ ≤ (L * ‖(x + t • d) - x‖) * ‖d‖ := mul_le_mul_of_nonneg_right (hLip _ _) (norm_nonneg _)
      _ = _ := by rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]; ring
  have hh := scalar_abs g dg (L * ‖d‖ ^ 2) hd hb
  dsimp [g, dg, d] at hh
  simp only [zero_smul, one_smul, add_zero, add_sub_cancel] at hh
  convert hh using 1 <;> ring

theorem rayleigh {n d m : ℕ} (P : Problem n d m) (v : E d) :
    lamMin P * ‖v‖ ^ 2 ≤ ‖P.B v‖ ^ 2 := by
  by_cases hv : v = 0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hnorm : ‖‖v‖⁻¹ • v‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn]
  have hmem : ‖P.B (‖v‖⁻¹ • v)‖ ^ 2 ∈ (fun x => ‖P.B x‖ ^ 2) '' Metric.sphere (0 : E d) 1 :=
    ⟨‖v‖⁻¹ • v, by simpa only [Metric.mem_sphere, dist_zero_right] using hnorm, rfl⟩
  have hbb : BddBelow ((fun x : E d => ‖P.B x‖ ^ 2) '' Metric.sphere (0 : E d) 1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    positivity
  have hh : lamMin P ≤ ‖P.B (‖v‖⁻¹ • v)‖ ^ 2 := csInf_le hbb hmem
  rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] at hh
  have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖v‖)
  field_simp [hn] at hm
  nlinarith only [hm]

theorem adjoint_range_bound {n d m : ℕ} (P : Problem n d m) (hlam : 0 ≤ lamMin P)
    (z : E m) (hz : z ∈ Set.range P.B) :
    lamMin P * ‖z‖ ^ 2 ≤ ‖ContinuousLinearMap.adjoint P.B z‖ ^ 2 := by
  obtain ⟨v, rfl⟩ := hz
  by_cases hb : P.B v = 0
  · simp [hb]
  have hbpos : 0 < ‖P.B v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hb)
  have hinner : ‖P.B v‖ ^ 2 ≤ ‖v‖ * ‖ContinuousLinearMap.adjoint P.B (P.B v)‖ := by
    rw [P.B.apply_norm_sq_eq_inner_adjoint_right]
    exact real_inner_le_norm v (ContinuousLinearMap.adjoint P.B (P.B v))
  have hs := mul_self_le_mul_self (sq_nonneg ‖P.B v‖) hinner
  have h1 := mul_le_mul_of_nonneg_left hs hlam
  have h2 := mul_le_mul_of_nonneg_right (rayleigh P v)
    (sq_nonneg ‖ContinuousLinearMap.adjoint P.B (P.B v)‖)
  apply (mul_le_mul_iff_right₀ hbpos).mp
  nlinarith only [h1, h2]

theorem gradV_bound {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (hA1 : Assumption1 P LG LH L0 LOmj) (u u' : E n) (v v' : E d) :
    ‖gradV P u v - gradV P u' v'‖ ≤ LG * (‖u - u'‖ + ‖v - v'‖) := by
  have h := hA1.1.2.2 u v u' v'
  have hnn := mul_nonneg (sq_nonneg LG) (mul_nonneg (norm_nonneg (u - u')) (norm_nonneg (v - v')))
  have hLG := hA1.1.2.1
  have hp : 0 ≤ LG * (‖u - u'‖ + ‖v - v'‖) :=
    mul_nonneg hLG (add_nonneg (norm_nonneg _) (norm_nonneg _))
  nlinarith only [h, hnn, hp, norm_nonneg (gradV P u v - gradV P u' v'),
    sq_nonneg ‖gradU P u v - gradU P u' v'‖]

theorem adjoint_theta_bound {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (hA1 : Assumption1 P LG LH L0 LOmj) (u u' : E n) :
    ‖ContinuousLinearMap.adjoint P.B (Theta P u - Theta P u')‖ ≤ ‖P.B‖ * L0 * ‖u - u'‖ := by
  calc
    _ ≤ ‖ContinuousLinearMap.adjoint P.B‖ * ‖Theta P u - Theta P u'‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖P.B‖ * ‖Theta P u - Theta P u'‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ ‖P.B‖ * (L0 * ‖u - u'‖) :=
      mul_le_mul_of_nonneg_left (hA1.2.2.2.1.2.2.2 u u') (norm_nonneg _)
    _ = _ := by ring

/-- `G(u, z) ≤ G(u, v) + ⟨∇_v G(u,v), z - v⟩ + L_G/2 ‖z - v‖²` (descent lemma in `v`). -/
theorem G_upper_v {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (hA1 : Assumption1 P LG LH L0 LOmj) (u : E n) (v z : E d) :
    P.G (u, z) - P.G (u, v) - ⟪gradV P u v, z - v⟫_ℝ ≤ LG / 2 * ‖z - v‖ ^ 2 := by
  let f : E d → ℝ := fun y => P.G (u, y)
  have hf : Differentiable ℝ f := fun y =>
    (hA1.1.1 (u, y)).comp y ((differentiableAt_const u).prodMk differentiableAt_id)
  have hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ LG * ‖x - y‖ := by
    intro x y
    have h := gradV_bound P LG LH L0 LOmj hA1 u u x y
    simpa [gradV, f] using h
  have h := gradient_taylor f LG hf hLip v z
  have h' := (le_abs_self _).trans h
  simpa [gradV, f] using h'

/-- Young-type inequality `A x y ≤ 7A²/t x² + t/28 y²`. -/
theorem young7 (A x y t : ℝ) (ht : 0 < t) : A * x * y ≤ 7 * A ^ 2 / t * x ^ 2 + t / 28 * y ^ 2 := by
  have h : 7 * A ^ 2 / t * x ^ 2 + t / 28 * y ^ 2 - A * x * y = (14 * A * x - t * y) ^ 2 / (28 * t) := by
    field_simp
    ring
  have : 0 ≤ (14 * A * x - t * y) ^ 2 / (28 * t) := by positivity
  linarith

theorem sq_sqrt_wdist {n d m : ℕ} (a a' : E n) (b b' : E d) (c c' : E m) :
    wdist (a, b, c) (a', b', c') ^ 2 = ‖a - a'‖ ^ 2 + ‖b - b'‖ ^ 2 + ‖c - c'‖ ^ 2 := by
  unfold wdist tnorm
  exact Real.sq_sqrt (by positivity)

theorem le_wdist {n d m : ℕ} (a a' : E n) (b b' : E d) (c c' : E m) :
    ‖a - a'‖ ≤ wdist (a, b, c) (a', b', c') ∧ ‖b - b'‖ ≤ wdist (a, b, c) (a', b', c') ∧
      ‖c - c'‖ ≤ wdist (a, b, c) (a', b', c') := by
  unfold wdist tnorm
  simp only [Prod.fst_sub, Prod.snd_sub]
  refine ⟨?_, ?_, ?_⟩
  · exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg ‖b - b'‖, sq_nonneg ‖c - c'‖]))
  · exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg ‖a - a'‖, sq_nonneg ‖c - c'‖]))
  · exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg ‖b - b'‖, sq_nonneg ‖a - a'‖]))


/-- Lower bound (from the proof of Theorem 4.1(i)): if `Θ(u^k) + B z = 0`, then
`F(u^k, z) + (3γλ/7 - (L_G+L_H)/2) ‖v^k - z‖² ≤ Λ^k` for `k ≥ 1`. -/
theorem lam_lower {n d m : ℕ} (P : Problem n d m) (LG LH L0 LK β γ σ : ℝ) (LOmj : Fin m → ℝ)
    (K : E n → ℝ) (δ ε : ℕ → ℝ) (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hrun : RunHyp P LG LH L0 LOmj K β LK γ σ δ ε u v p) (k : ℕ) (hk : 1 ≤ k)
    (z : E d) (hz : Theta P (u k) + P.B z = 0) :
    F P (u k) z + (3 * (γ * lamMin P) / 7 - (LG + LH) / 2) * ‖v k - z‖ ^ 2 ≤
      Lam P LG LH L0 γ u v p k := by
  have hA1 := hrun.1
  have hγ : 0 < γ := hrun.2.2.1.1
  have hlam : 0 < lamMin P := hA1.2.2.2.2.2.1.2
  have ht : 0 < γ * lamMin P := mul_pos hγ hlam
  set t := γ * lamMin P with ht_def
  set e := v k - z with he
  have hth : Theta P (u k) = -P.B z := eq_neg_of_add_eq_zero_left hz
  have hr : Theta P (u k) + P.B (v k) = P.B e := by
    rw [he, map_sub, hth]; abel
  -- dual identity, Lemma 4.1(ii)
  have hdual := (lemma_4_1 P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun.1 hrun.2.1 hrun.2.2.1).2.1 k hk
  have hpe : ⟪p k, P.B e⟫_ℝ = ⟪ContinuousLinearMap.adjoint P.B (p k), e⟫_ℝ :=
    (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
  set gv' := gradV P (u (k - 1)) (v (k - 1)) with hgv'
  set gh' := gradient P.H (v (k - 1)) with hgh'
  set gv := gradV P (u k) (v k) with hgv
  set gh := gradient P.H (v k) with hgh
  set dT := ContinuousLinearMap.adjoint P.B (Theta P (u k) - Theta P (u (k - 1))) with hdT
  have hsplit : ⟪p k, P.B e⟫_ℝ = ⟪gv - gv', e⟫_ℝ + ⟪gh - gh', e⟫_ℝ + γ * ⟪dT, e⟫_ℝ -
      ⟪gv, e⟫_ℝ - ⟪gh, e⟫_ℝ := by
    rw [hpe, hdual]
    simp only [inner_add_left, inner_sub_left, inner_neg_left, real_inner_smul_left]
    ring
  set du := ‖u (k - 1) - u k‖ with hdu
  set dv := ‖v (k - 1) - v k‖ with hdv
  set ne := ‖e‖ with hne
  have hne0 : 0 ≤ ne := norm_nonneg _
  have hdu0 : 0 ≤ du := norm_nonneg _
  have hdv0 : 0 ≤ dv := norm_nonneg _
  have b1 : -(LG * (du + dv) * ne) ≤ ⟪gv - gv', e⟫_ℝ := by
    have h1 := gradV_bound P LG LH L0 LOmj hA1 (u k) (u (k - 1)) (v k) (v (k - 1))
    rw [norm_sub_rev (u k), norm_sub_rev (v k)] at h1
    have h2 := (abs_le.mp (abs_real_inner_le_norm (gv - gv') e)).1
    nlinarith [mul_le_mul_of_nonneg_right h1 hne0]
  have b2 : -(LH * dv * ne) ≤ ⟪gh - gh', e⟫_ℝ := by
    have h1 := hA1.2.1.2.2 (v k) (v (k - 1))
    rw [norm_sub_rev (v k)] at h1
    have h2 := (abs_le.mp (abs_real_inner_le_norm (gh - gh') e)).1
    nlinarith [mul_le_mul_of_nonneg_right h1 hne0]
  have b3 : -(γ * (‖P.B‖ * L0 * du) * ne) ≤ γ * ⟪dT, e⟫_ℝ := by
    have h1 := adjoint_theta_bound P LG LH L0 LOmj hA1 (u k) (u (k - 1))
    rw [norm_sub_rev (u k)] at h1
    have h2 := (abs_le.mp (abs_real_inner_le_norm dT e)).1
    have h3 : -(‖P.B‖ * L0 * du * ne) ≤ ⟪dT, e⟫_ℝ := by
      nlinarith [mul_le_mul_of_nonneg_right h1 hne0]
    nlinarith [mul_le_mul_of_nonneg_left h3 hγ.le]
  have y1 := young7 (LG + γ * ‖P.B‖ * L0) du ne t ht
  have y2 := young7 (LG + LH) dv ne t ht
  have hray := rayleigh P e
  -- descent lemma in `v`
  have hGd := G_upper_v P LG LH L0 LOmj hA1 (u k) (v k) z
  have hHd := (le_abs_self _).trans (gradient_taylor P.H LH hA1.2.1.1 hA1.2.1.2.2 (v k) z)
  have hzv : z - v k = -e := by rw [he]; abel
  rw [hzv, norm_neg, inner_neg_right] at hGd hHd
  -- assemble
  have hLam : Lam P LG LH L0 γ u v p k = F P (u k) (v k) + ⟪p k, P.B e⟫_ℝ +
      γ / 2 * ‖P.B e‖ ^ 2 + c1 P LG L0 γ * du ^ 2 + c2 P LG LH γ * dv ^ 2 +
      1 / (2 * γ) * ‖p (k - 1) - p k‖ ^ 2 := by
    simp only [Lam, augLag, wseq, hr]
    rfl
  have hp0 : 0 ≤ 1 / (2 * γ) * ‖p (k - 1) - p k‖ ^ 2 := by positivity
  have hc1 : c1 P LG L0 γ * du ^ 2 = 7 * (LG + γ * ‖P.B‖ * L0) ^ 2 / t * du ^ 2 := rfl
  have hc2 : c2 P LG LH γ * dv ^ 2 = 7 * (LG + LH) ^ 2 / t * dv ^ 2 := rfl
  have hF : F P (u k) z = P.G (u k, z) + P.J (u k) + P.H z := rfl
  have hF' : F P (u k) (v k) = P.G (u k, v k) + P.J (u k) + P.H (v k) := rfl
  have hBe : γ / 2 * (lamMin P * ne ^ 2) ≤ γ / 2 * ‖P.B e‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hray (by positivity)
  have hte : γ / 2 * (lamMin P * ne ^ 2) = t / 2 * ne ^ 2 := by rw [ht_def]; ring
  rw [hLam, hsplit, hc1, hc2, hF]
  rw [hF']
  rw [← hne] at hGd hHd
  rw [← hne] at hray
  have hBe' : t / 2 * ne ^ 2 ≤ γ / 2 * ‖P.B e‖ ^ 2 := hte ▸ hBe
  linear_combination hGd + hHd + b1 + b2 + b3 + y1 + y2 + hBe' + hp0


theorem c3_pos {n d m : ℕ} (P : Problem n d m) (LG LH L0 LK β γ σ : ℝ) (LOmj : Fin m → ℝ)
    (K : E n → ℝ) (δ ε : ℕ → ℝ) (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hrun : RunHyp P LG LH L0 LOmj K β LK γ σ δ ε u v p) : 0 < c3 P LG LH γ := by
  have hc4 := (lemma_4_3 P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun).1
  have hγ : 0 < γ := hrun.2.2.1.1
  simp only [c3]
  refine lt_min (by norm_num) (lt_min hc4 ?_)
  positivity

theorem kappa_pos {n d m : ℕ} (P : Problem n d m) (LG LH L0 LK β γ σ : ℝ) (LOmj : Fin m → ℝ)
    (K : E n → ℝ) (δ ε : ℕ → ℝ) (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hrun : RunHyp P LG LH L0 LOmj K β LK γ σ δ ε u v p) :
    0 < 3 * (γ * lamMin P) / 7 - (LG + LH) / 2 := by
  have hγ : 0 < γ := hrun.2.2.1.1
  have hlam : 0 < lamMin P := hrun.1.2.2.2.2.2.1.2
  have hs : 0 ≤ LG + LH := add_nonneg hrun.1.1.2.1 hrun.1.2.1.2.1
  have hh := mul_lt_mul_of_pos_right hrun.2.1.2.2.2.2.2 hlam
  have ht : (Real.sqrt 57 + 1) / 2 * (LG + LH) < γ * lamMin P := by
    convert! hh using 1
    field_simp
  have h7 : (7 : ℝ) ≤ Real.sqrt 57 := by
    rw [show (7 : ℝ) = Real.sqrt 49 by rw [show (49 : ℝ) = 7 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h4 : 4 * (LG + LH) ≤ (Real.sqrt 57 + 1) / 2 * (LG + LH) := by nlinarith
  have htp : 0 < γ * lamMin P := mul_pos hγ hlam
  nlinarith

theorem lam_le_one {n d m : ℕ} (P : Problem n d m) (LG LH L0 LK β γ σ : ℝ) (LOmj : Fin m → ℝ)
    (K : E n → ℝ) (δ ε : ℕ → ℝ) (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hrun : RunHyp P LG LH L0 LOmj K β LK γ σ δ ε u v p) :
    ∀ k, 1 ≤ k → Lam P LG LH L0 γ u v p k ≤ Lam P LG LH L0 γ u v p 1 := by
  have hdec := (lemma_4_3 P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun).2
  have hc3 := c3_pos P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    have h := hdec k hk
    have : 0 ≤ c3 P LG LH γ * wdist (u k, v k, p k) (u (k + 1), v (k + 1), p (k + 1)) ^ 2 :=
      mul_nonneg hc3.le (sq_nonneg _)
    linarith

set_option maxHeartbeats 1000000 in
/-- The iterates are bounded (Theorem 4.1(ii), via the lower bound of Theorem 4.1(i),
coercivity (H7) and Lemma 4.1). -/
theorem bounded_run {n d m : ℕ} (P : Problem n d m) (LG LH L0 LK β γ σ : ℝ) (LOmj : Fin m → ℝ)
    (K : E n → ℝ) (δ ε : ℕ → ℝ) (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hrun : RunHyp P LG LH L0 LOmj K β LK γ σ δ ε u v p) :
    ∃ R, ∀ k, ‖u k‖ ≤ R ∧ ‖v k‖ ≤ R ∧ ‖p k‖ ≤ R := by
  have hA1 := hrun.1
  have hγ : 0 < γ := hrun.2.2.1.1
  have hlam : 0 < lamMin P := hA1.2.2.2.2.2.1.2
  have hκ := kappa_pos P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun
  set κ := 3 * (γ * lamMin P) / 7 - (LG + LH) / 2 with hκdef
  set M := Lam P LG LH L0 γ u v p 1 with hM
  obtain ⟨c, hc⟩ := hA1.2.2.2.2.2.2.1
  obtain ⟨C, hC⟩ := (hA1.2.2.2.2.2.2.2 M).exists_norm_le
  have hLG := hA1.1.2.1
  have hLH := hA1.2.1.2.1
  have hL0 := hA1.2.2.2.1.2.2.1
  -- bounds on `u^k, v^k` for `k ≥ 1`
  have huv1 : ∀ k, 1 ≤ k → ‖u k‖ ≤ C + 1 + (M - c) / κ ∧ ‖v k‖ ≤ C + 1 + (M - c) / κ := by
    intro k hk
    obtain ⟨y, hy⟩ := hA1.2.2.2.2.2.1.1 (Set.mem_range_self (u k))
    have hz : Theta P (u k) + P.B (-y) = 0 := by rw [map_neg, hy]; abel
    have hlow := lam_lower P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun k hk (-y) hz
    have hle := lam_le_one P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun k hk
    rw [← hκdef] at hlow
    rw [← hM] at hle
    have he0 : 0 ≤ κ * ‖v k - -y‖ ^ 2 := mul_nonneg hκ.le (sq_nonneg _)
    have hcF := hc (u k) (-y) hz
    have hmem : (u k, -y) ∈ {x : E n × E d | Theta P x.1 + P.B x.2 = 0 ∧ F P x.1 x.2 ≤ M} :=
      ⟨hz, by simp only; linarith⟩
    have hnorm := hC _ hmem
    have hu : ‖u k‖ ≤ C := (norm_fst_le _).trans hnorm
    have hy' : ‖-y‖ ≤ C := (norm_snd_le (u k, -y)).trans hnorm
    have hesq : ‖v k - -y‖ ^ 2 ≤ (M - c) / κ := by
      rw [le_div_iff₀ hκ]; nlinarith only [hlow, hle, hcF]
    have he : ‖v k - -y‖ ≤ 1 + (M - c) / κ := by
      nlinarith only [sq_nonneg (‖v k - -y‖ - 1), hesq]
    have hv : ‖v k‖ ≤ ‖-y‖ + ‖v k - -y‖ := by
      have := norm_add_le (-y) (v k - -y)
      simpa using this
    have hMc : 0 ≤ (M - c) / κ := (sq_nonneg _).trans hesq
    constructor <;> linarith
  set R1 := |C + 1 + (M - c) / κ| + ‖u 0‖ + ‖v 0‖ with hR1
  have huv : ∀ k, ‖u k‖ ≤ R1 ∧ ‖v k‖ ≤ R1 := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · constructor <;> linarith [abs_nonneg (C + 1 + (M - c) / κ), norm_nonneg (u 0), norm_nonneg (v 0)]
    · obtain ⟨h1, h2⟩ := huv1 k hk
      have := le_abs_self (C + 1 + (M - c) / κ)
      constructor <;> linarith [norm_nonneg (u 0), norm_nonneg (v 0)]
  have hR10 : 0 ≤ R1 := (norm_nonneg _).trans (huv 0).1
  -- bound on `B^⊤ p^k` for `k ≥ 1`
  set C0 := ‖gradV P 0 0‖ + LG * (2 * R1) + (‖gradient P.H 0‖ + LH * R1) +
    γ * (‖P.B‖ * L0 * (2 * R1)) with hC0
  have hdual := (lemma_4_1 P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun.1 hrun.2.1 hrun.2.2.1).2.1
  have hBp : ∀ k, 1 ≤ k → ‖ContinuousLinearMap.adjoint P.B (p k)‖ ≤ C0 := by
    intro k hk
    rw [hdual k hk]
    have h1 := gradV_bound P LG LH L0 LOmj hA1 (u (k - 1)) 0 (v (k - 1)) 0
    have h2 := hA1.2.1.2.2 (v (k - 1)) 0
    have h3 := adjoint_theta_bound P LG LH L0 LOmj hA1 (u k) (u (k - 1))
    simp only [sub_zero] at h1 h2
    have hu1 := (huv (k - 1)).1
    have hv1 := (huv (k - 1)).2
    have hu2 := (huv k).1
    have hgv : ‖gradV P (u (k - 1)) (v (k - 1))‖ ≤ ‖gradV P 0 0‖ + LG * (2 * R1) := by
      have := norm_le_insert' (gradV P (u (k - 1)) (v (k - 1))) (gradV P 0 0)
      have h4 := mul_le_mul_of_nonneg_left (add_le_add hu1 hv1) hLG
      linarith only [this, h1, h4]
    have hgh : ‖gradient P.H (v (k - 1))‖ ≤ ‖gradient P.H 0‖ + LH * R1 := by
      have := norm_le_insert' (gradient P.H (v (k - 1))) (gradient P.H 0)
      have h4 := mul_le_mul_of_nonneg_left hv1 hLH
      linarith only [this, h2, h4]
    have hdu : ‖u k - u (k - 1)‖ ≤ 2 * R1 := by
      have := norm_sub_le (u k) (u (k - 1)); linarith
    have hth : γ * ‖ContinuousLinearMap.adjoint P.B (Theta P (u k) - Theta P (u (k - 1)))‖ ≤
        γ * (‖P.B‖ * L0 * (2 * R1)) := by
      apply mul_le_mul_of_nonneg_left _ hγ.le
      exact h3.trans (mul_le_mul_of_nonneg_left hdu (mul_nonneg (norm_nonneg _) hL0))
    calc ‖-gradV P (u (k - 1)) (v (k - 1)) - gradient P.H (v (k - 1)) +
          γ • ContinuousLinearMap.adjoint P.B (Theta P (u k) - Theta P (u (k - 1)))‖
        ≤ ‖gradV P (u (k - 1)) (v (k - 1))‖ + ‖gradient P.H (v (k - 1))‖ +
          γ * ‖ContinuousLinearMap.adjoint P.B (Theta P (u k) - Theta P (u (k - 1)))‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_of_nonneg hγ.le]
          have := norm_sub_le (-gradV P (u (k - 1)) (v (k - 1))) (gradient P.H (v (k - 1)))
          rw [norm_neg] at this
          linarith
      _ ≤ C0 := by rw [hC0]; linarith
  -- `p^k - p^1 ∈ range B`
  have hrange : ∀ k, 1 ≤ k → p k - p 1 ∈ Set.range P.B := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact ⟨0, by simp⟩
    | succ k hk ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨z, hz⟩ := hA1.2.2.2.2.2.1.1 (Set.mem_range_self (u (k + 1)))
      refine ⟨y + γ • (z + v (k + 1)), ?_⟩
      rw [(hrun.2.2.1.2.2.2 k).2.2.2, map_add, map_smul, map_add, hy, hz]
      abel
  have hp1 : ∀ k, 1 ≤ k → ‖p k‖ ≤ ‖p 1‖ + (1 + 4 * C0 ^ 2 / lamMin P) := by
    intro k hk
    have hr := adjoint_range_bound P hlam.le _ (hrange k hk)
    have hb : ‖ContinuousLinearMap.adjoint P.B (p k - p 1)‖ ≤ 2 * C0 := by
      rw [map_sub]
      have := norm_sub_le (ContinuousLinearMap.adjoint P.B (p k)) (ContinuousLinearMap.adjoint P.B (p 1))
      linarith [hBp k hk, hBp 1 le_rfl]
    have hb2 : ‖ContinuousLinearMap.adjoint P.B (p k - p 1)‖ ^ 2 ≤ (2 * C0) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hrsq : ‖p k - p 1‖ ^ 2 ≤ 4 * C0 ^ 2 / lamMin P := by
      rw [le_div_iff₀ hlam]; nlinarith only [hr, hb2]
    have hr1 : ‖p k - p 1‖ ≤ 1 + 4 * C0 ^ 2 / lamMin P := by
      nlinarith only [sq_nonneg (‖p k - p 1‖ - 1), hrsq]
    have := norm_le_insert' (p k) (p 1)
    linarith
  refine ⟨R1 + ‖p 0‖ + (‖p 1‖ + (1 + 4 * C0 ^ 2 / lamMin P)), fun k => ?_⟩
  have hq : 0 ≤ 4 * C0 ^ 2 / lamMin P := by positivity
  have hp0 := norm_nonneg (p 0)
  have hp1' := norm_nonneg (p 1)
  refine ⟨by linarith [(huv k).1], by linarith [(huv k).2], ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · linarith
  · linarith [hp1 k hk]


/-- If `b ≥ 0` is summable, then `k * min_{k/2 ≤ i < k} b i ≤ 2 ∑_{j} b (j + k/2)`. -/
theorem min_le_tail (b : ℕ → ℝ) (hb0 : ∀ i, 0 ≤ b i) (hbs : Summable b) (k : ℕ)
    (hk : 1 ≤ k) :
    ∃ i, k / 2 ≤ i ∧ i < k ∧ (k : ℝ) * b i ≤ 2 * ∑' j, b (j + k / 2) := by
  have hne : (Finset.Ico (k / 2) k).Nonempty := ⟨k / 2, by simp; omega⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (Finset.Ico (k / 2) k) b hne
  refine ⟨i, (Finset.mem_Ico.1 hi).1, (Finset.mem_Ico.1 hi).2, ?_⟩
  have hcard : ((Finset.Ico (k / 2) k).card : ℝ) * b i ≤ ∑ x ∈ Finset.Ico (k / 2) k, b x := by
    have := Finset.card_nsmul_le_sum (Finset.Ico (k / 2) k) b (b i) hmin
    simpa [nsmul_eq_mul] using this
  have hsum : ∑ x ∈ Finset.Ico (k / 2) k, b x ≤ ∑' j, b (j + k / 2) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hs : Summable (fun j => b (j + k / 2)) := (summable_nat_add_iff (k / 2)).2 hbs
    calc ∑ j ∈ Finset.range (k - k / 2), b (k / 2 + j)
        = ∑ j ∈ Finset.range (k - k / 2), b (j + k / 2) := by
          refine Finset.sum_congr rfl fun j _ => by rw [Nat.add_comm]
      _ ≤ ∑' j, b (j + k / 2) := hs.sum_le_tsum _ (fun j _ => hb0 _)
  have hc : (Finset.Ico (k / 2) k).card = k - k / 2 := Nat.card_Ico _ _
  rw [hc] at hcard
  have hk2 : (k : ℝ) ≤ 2 * ((k - k / 2 : ℕ) : ℝ) := by
    have : k ≤ 2 * (k - k / 2) := by omega
    exact_mod_cast this
  have hbi := hb0 i
  nlinarith

/-- Uniform residual bound: `dist(0, ∂L_γ(w^{k+1})) ≤ C ‖w^k - w^{k+1}‖` (Theorem 4.1(iv),
from Proposition 3.1 and boundedness). -/
theorem residual_bound {n d m : ℕ} (P : Problem n d m) (LG LH L0 LK β γ σ : ℝ) (LOmj : Fin m → ℝ)
    (K : E n → ℝ) (δ ε : ℕ → ℝ) (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hrun : RunHyp P LG LH L0 LOmj K β LK γ σ δ ε u v p) :
    ∃ C : ℝ, ∀ k, distZero (dAugLag P γ (u (k + 1), v (k + 1), p (k + 1))) ≤
      ENNReal.ofReal (C * wdist (u k, v k, p k) (u (k + 1), v (k + 1), p (k + 1))) := by
  obtain ⟨R, hR⟩ := bounded_run P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun
  have hA1 := hrun.1
  have hγ : 0 < γ := hrun.2.2.1.1
  have hσ : 0 < σ := hrun.2.2.1.2.1
  have hβ : 0 < β := hrun.2.1.2.1
  have hLK : 0 ≤ LK := hrun.2.1.2.2.2.1
  have hlam : 0 < lamMin P := hA1.2.2.2.2.2.1.2
  have hLG := hA1.1.2.1
  have hL0 := hA1.2.2.2.1.2.2.1
  have hLOm : 0 ≤ LOm LOmj := Finset.sum_nonneg (fun j _ => (hA1.2.2.2.2.1 j).1)
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0).1
  set Q := R + γ * (‖Theta P 0‖ + L0 * R + ‖P.B‖ * R) with hQ
  have hq : ∀ k, ‖qseq P γ u v p k‖ ≤ Q := by
    intro k
    have h1 : ‖Theta P (u k)‖ ≤ ‖Theta P 0‖ + L0 * R := by
      have := norm_le_insert' (Theta P (u k)) (Theta P 0)
      have h2 := hA1.2.2.2.1.2.2.2 (u k) 0
      rw [sub_zero] at h2
      have h3 := mul_le_mul_of_nonneg_left (hR k).1 hL0
      linarith
    have h2 : ‖P.B (v k)‖ ≤ ‖P.B‖ * R :=
      (P.B.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hR k).2.1 (norm_nonneg _))
    have h3 : ‖Theta P (u k) + P.B (v k)‖ ≤ ‖Theta P 0‖ + L0 * R + ‖P.B‖ * R :=
      (norm_add_le _ _).trans (by linarith)
    simp only [qseq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hγ.le]
    have := mul_le_mul_of_nonneg_left h3 hγ.le
    linarith [(hR k).2.2]
  set T := γ * L0 ^ 2 + 14 * γ * ‖P.B‖ ^ 2 * L0 ^ 2 / lamMin P +
    14 * (LG + γ * ‖P.B‖ * L0) ^ 2 / (γ * lamMin P) + 1 with hT
  have hT0 : 1 ≤ T := by
    have : 0 ≤ γ * L0 ^ 2 + 14 * γ * ‖P.B‖ ^ 2 * L0 ^ 2 / lamMin P +
      14 * (LG + γ * ‖P.B‖ * L0) ^ 2 / (γ * lamMin P) := by positivity
    linarith
  set DQ := LG + Q * LOm LOmj + T with hDQ
  set Hb := max (max (2 * LG + Q * LOm LOmj + γ * ‖P.B‖ * L0 + γ * L0 ^ 2 + LK * DQ / (σ * β))
    (2 * LG + LH + γ * ‖P.B‖ * L0)) (L0 + ‖P.B‖ + 1 / γ) with hHb
  refine ⟨Real.sqrt 3 * Hb, fun k => ?_⟩
  have h31 := proposition_3_1 P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun k
  refine h31.trans (ENNReal.ofReal_le_ofReal ?_)
  have ha0 : 0 ≤ wdist (u k, v k, p k) (u (k + 1), v (k + 1), p (k + 1)) := Real.sqrt_nonneg _
  apply mul_le_mul_of_nonneg_right _ ha0
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  -- bound `h(u^k, p^k)`
  set qk := qseq P γ u v p k
  have hqk := hq k
  set Dk := LG + ‖qk‖ * LOm LOmj + T with hDk
  have hδ : δ k = β / Dk := by
    rw [hrun.2.2.2 k, delta8, hDk, hT]; ring
  have hDk0 : 0 < Dk := by
    have := mul_nonneg (norm_nonneg qk) hLOm
    linarith
  have hDle : Dk ≤ DQ := by
    have := mul_le_mul_of_nonneg_right hqk hLOm
    rw [hDk, hDQ]; linarith
  have hLKt : LK / (σ * δ k) ≤ LK * DQ / (σ * β) := by
    rw [hδ]
    have he : LK / (σ * (β / Dk)) = LK * Dk / (σ * β) := by
      field_simp
    rw [he]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hDle hLK) (mul_pos hσ hβ).le
  have hqL := mul_le_mul_of_nonneg_right hqk hLOm
  simp only [hfun, hHb]
  refine max_le_max (max_le_max ?_ le_rfl) le_rfl
  linarith

end NAPPALP41

open NAPPALP41 in
theorem solution {n d m : ℕ} (P : NAPPAL.KL.Problem n d m) (LG LH L0 LK β γ σ : ℝ) (LOmj : Fin m → ℝ)
    (K : NAPPAL.KL.E n → ℝ) (δ ε : ℕ → ℝ) (u : ℕ → NAPPAL.KL.E n) (v : ℕ → NAPPAL.KL.E d) (p : ℕ → NAPPAL.KL.E m)
    (hrun : NAPPAL.Rate.RunHyp P LG LH L0 LOmj K β LK γ σ δ ε u v p) :
    Tendsto
      (fun k : ℕ => ENNReal.ofReal (Real.sqrt k) *
        ⨅ j ∈ Finset.Icc 1 k, NAPPAL.KL.distZero (NAPPAL.KL.dAugLag P γ (u j, v j, p j)))
      atTop (𝓝 0) := by
  obtain ⟨c5, hc5⟩ := residual_bound P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun
  obtain ⟨-, hdec⟩ := NAPPAL.Rate.lemma_4_3 P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun
  have hc3 := c3_pos P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun
  set Lam := NAPPAL.KL.Lam P LG LH L0 γ u v p with hLam
  set c3 := NAPPAL.KL.c3 P LG LH γ with hc3def
  -- lower bound of the potential (Theorem 4.1(i))
  obtain ⟨cF, hcF⟩ := hrun.1.2.2.2.2.2.2.1
  have hκ := kappa_pos P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun
  have hLk : ∀ k, 1 ≤ k → cF ≤ Lam k := by
    intro k hk
    obtain ⟨y, hy⟩ := hrun.1.2.2.2.2.2.1.1 (Set.mem_range_self (u k))
    have hz : Theta P (u k) + P.B (-y) = 0 := by rw [map_neg, hy]; abel
    have hlow := lam_lower P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun k hk (-y) hz
    have h1 := hcF (u k) (-y) hz
    have h2 := mul_nonneg hκ.le (sq_nonneg ‖v k - -y‖)
    linarith
  -- step lengths
  set a : ℕ → ℝ := fun i =>
    NAPPAL.KL.wdist (u i, v i, p i) (u (i + 1), v (i + 1), p (i + 1)) with ha
  have ha0 : ∀ i, 0 ≤ a i := fun i => Real.sqrt_nonneg _
  set b : ℕ → ℝ := fun i => a i ^ 2 with hb
  have hb0 : ∀ i, 0 ≤ b i := fun i => sq_nonneg _
  have htel : ∀ N, c3 * ∑ i ∈ Finset.range N, b (i + 1) ≤ Lam 1 - Lam (N + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, mul_add]
      have := hdec (N + 1) (by omega)
      simp only [hb, ha]
      simp only [hb, ha] at ih
      linarith
  have hbs : Summable b := by
    refine summable_of_sum_range_le (c := b 0 + (Lam 1 - cF) / c3) hb0 fun N => ?_
    cases N with
    | zero => simp; exact add_nonneg (hb0 0) (div_nonneg (by linarith [hLk 1 le_rfl]) hc3.le)
    | succ N =>
      rw [Finset.sum_range_succ']
      have h1 := htel N
      have h2 := hLk (N + 1) (by omega)
      have : ∑ i ∈ Finset.range N, b (i + 1) ≤ (Lam 1 - cF) / c3 := by
        rw [le_div_iff₀ hc3]; linarith
      linarith
  -- tail sums
  set T : ℕ → ℝ := fun N => ∑' j, b (j + N) with hT
  have hT0 : Tendsto T atTop (𝓝 0) := tendsto_sum_nat_add b
  have hTk : Tendsto (fun k : ℕ => T (k / 2)) atTop (𝓝 0) :=
    hT0.comp (Nat.tendsto_div_const_atTop (by norm_num))
  have hg : Tendsto (fun k : ℕ => ENNReal.ofReal (c5 * Real.sqrt (2 * T (k / 2)))) atTop
      (𝓝 0) := by
    have : Tendsto (fun k : ℕ => c5 * Real.sqrt (2 * T (k / 2))) atTop
        (𝓝 (c5 * Real.sqrt (2 * 0))) :=
      (((hTk.const_mul 2).sqrt).const_mul c5)
    simpa using (ENNReal.tendsto_ofReal this)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  obtain ⟨i, -, hik, hki⟩ := min_le_tail b hb0 hbs k hk
  have hinf : (⨅ j ∈ Finset.Icc 1 k, NAPPAL.KL.distZero (NAPPAL.KL.dAugLag P γ (u j, v j, p j)))
      ≤ ENNReal.ofReal (c5 * a i) := by
    refine (iInf₂_le (i + 1) (by simp; omega)).trans ?_
    exact hc5 i
  calc ENNReal.ofReal (Real.sqrt k) *
        ⨅ j ∈ Finset.Icc 1 k, NAPPAL.KL.distZero (NAPPAL.KL.dAugLag P γ (u j, v j, p j))
      ≤ ENNReal.ofReal (Real.sqrt k) * ENNReal.ofReal (c5 * a i) := by gcongr
    _ = ENNReal.ofReal (c5 * Real.sqrt ((k : ℝ) * b i)) := by
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      congr 1
      rw [Real.sqrt_mul (Nat.cast_nonneg _), hb]
      simp only
      rw [Real.sqrt_sq (ha0 i)]
      ring
    _ ≤ ENNReal.ofReal (c5 * Real.sqrt (2 * T (k / 2))) := by
      by_cases hc : 0 ≤ c5
      · apply ENNReal.ofReal_le_ofReal
        gcongr
      · rw [ENNReal.ofReal_of_nonpos (by
          have := Real.sqrt_nonneg ((k : ℝ) * b i)
          nlinarith)]
        exact zero_le
