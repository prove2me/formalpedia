-- Prove2me | solution 1 for HilbertSixteenth.cubic_two_algebraic_limit_cycles
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T03:30:52.213967+00:00
-- url     : https://prove2.me/submissions/b9f07999-8fd2-49a5-b946-8fe6f79b0d30

import Definitions.Def_HilbertSixteenth_PolyFields


open Real

namespace HS16

/-- explicit field -/
def Fx (p : ℝ × ℝ) : ℝ × ℝ :=
  (2 * p.2 * (10 + p.1 * p.2), 20 * p.1 + p.2 - 20 * p.1 ^ 3 - 2 * p.1 ^ 2 * p.2 + 4 * p.2 ^ 3)

def fx (p : ℝ × ℝ) : ℝ := 2 * p.1 ^ 4 - 4 * p.1 ^ 2 + 4 * p.2 ^ 2 + 1

lemma Fx_neg (p : ℝ × ℝ) : Fx (-p) = -Fx p := by
  simp only [Fx, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk, Prod.mk.injEq]; constructor <;> ring

lemma fx_neg (p : ℝ × ℝ) : fx (-p) = fx p := by
  simp only [fx, Prod.fst_neg, Prod.snd_neg]; ring

noncomputable def X (θ : ℝ) : ℝ := √(1 + cos θ / √2)

lemma s2pos : (0:ℝ) < √2 := by positivity
lemma s2sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
lemma s2gt : (1.4 : ℝ) < √2 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

lemma inner_pos (θ : ℝ) : 0.25 < 1 + cos θ / √2 := by
  have h1 := neg_one_le_cos θ
  have h2 : -1 / √2 ≤ cos θ / √2 := div_le_div_of_nonneg_right h1 s2pos.le
  have h3 : -1 / √2 > -0.75 := by
    rw [gt_iff_lt, lt_div_iff₀ s2pos]; nlinarith [s2gt]
  linarith

lemma inner_le (θ : ℝ) : 1 + cos θ / √2 ≤ 2 := by
  have h1 := cos_le_one θ
  have h2 : cos θ / √2 ≤ 1 / √2 := div_le_div_of_nonneg_right h1 s2pos.le
  have h3 : 1 / √2 ≤ 1 := by rw [div_le_one s2pos]; nlinarith [s2gt]
  linarith

lemma X_sq (θ : ℝ) : X θ ^ 2 = 1 + cos θ / √2 := Real.sq_sqrt (by linarith [inner_pos θ])

lemma X_pos (θ : ℝ) : 0.5 < X θ := by
  unfold X; rw [Real.lt_sqrt (by norm_num)]; linarith [inner_pos θ]

lemma X_le (θ : ℝ) : X θ ≤ √2 := Real.sqrt_le_sqrt (inner_le θ)

lemma X_cont : Continuous X := by unfold X; fun_prop

lemma X_deriv (θ : ℝ) : HasDerivAt X (-sin θ / √2 / (2 * X θ)) θ := by
  have h : HasDerivAt (fun θ => 1 + cos θ / √2) (-sin θ / √2) θ := by
    have := ((hasDerivAt_cos θ).div_const √2).const_add 1
    simpa using this
  have := h.sqrt (by linarith [inner_pos θ])
  exact this

/-- speed -/
noncomputable def H (θ : ℝ) : ℝ := 2 * √2 * X θ * (10 - X θ * sin θ / 2)

lemma H_cont : Continuous H := by unfold H; have := X_cont; fun_prop

lemma H_pos (θ : ℝ) : 1 ≤ H θ := by
  have hx := X_pos θ; have hx2 := X_le θ
  have hs := sin_le_one θ; have hs' := neg_one_le_sin θ
  have h4 : (√2) ≤ 2 := by nlinarith [s2sq, s2pos]
  have : X θ * sin θ ≤ 2 := by nlinarith
  have h9 : 9 ≤ 10 - X θ * sin θ / 2 := by linarith
  have h1 : 1.4 ≤ 2 * √2 * X θ := by nlinarith [s2gt]
  unfold H; nlinarith

lemma H_le (θ : ℝ) : H θ ≤ 44 := by
  have hx := X_pos θ; have hx2 := X_le θ
  have hs := sin_le_one θ; have hs' := neg_one_le_sin θ
  have h4 : (√2) ≤ 2 := by nlinarith [s2sq, s2pos]
  have : -2 ≤ X θ * sin θ := by nlinarith
  have : 10 - X θ * sin θ / 2 ≤ 11 := by linarith
  have h5 : 0 ≤ 10 - X θ * sin θ / 2 := by nlinarith
  unfold H
  have : 2 * √2 * X θ ≤ 4 := by nlinarith [s2sq]
  nlinarith

lemma H_periodic : Function.Periodic H (2 * π) := by
  intro θ; simp [H, X, cos_add_two_pi, sin_add_two_pi]

end HS16

open Real

namespace HS16

noncomputable def G (θ : ℝ) : ℝ := ∫ u in (0:ℝ)..θ, 1 / H u

lemma iH_cont : Continuous (fun u => 1 / H u) :=
  continuous_const.div H_cont (fun u => by linarith [H_pos u])

lemma G_deriv (θ : ℝ) : HasDerivAt G (1 / H θ) θ :=
  (iH_cont.integral_hasStrictDerivAt 0 θ).hasDerivAt

lemma G_cont : Continuous G := continuous_iff_continuousAt.2 fun θ => (G_deriv θ).continuousAt

lemma G_mono : StrictMono G :=
  strictMono_of_hasDerivAt_pos G_deriv (fun θ => by have := H_pos θ; positivity)

lemma G_lower (θ : ℝ) (h : 0 ≤ θ) : θ / 44 ≤ G θ := by
  have : ∫ u in (0:ℝ)..θ, (1 / 44 : ℝ) ≤ G θ := by
    apply intervalIntegral.integral_mono_on h intervalIntegrable_const
      (iH_cont.intervalIntegrable _ _)
    intro u _
    exact one_div_le_one_div_of_le (by linarith [H_pos u]) (H_le u)
  simpa [div_eq_inv_mul, mul_comm] using this

lemma G_upper (θ : ℝ) (h : θ ≤ 0) : G θ ≤ θ / 44 := by
  have : ∫ u in θ..(0:ℝ), (1 / 44 : ℝ) ≤ ∫ u in θ..(0:ℝ), 1 / H u := by
    apply intervalIntegral.integral_mono_on h intervalIntegrable_const
      (iH_cont.intervalIntegrable _ _)
    intro u _
    exact one_div_le_one_div_of_le (by linarith [H_pos u]) (H_le u)
  rw [G, intervalIntegral.integral_symm]
  simp at this ⊢
  linarith

lemma G_zero : G 0 = 0 := by simp [G]

lemma G_surj : Function.Surjective G := by
  intro t
  rcases le_total 0 t with ht | ht
  · have h1 : G 0 ≤ t := by rw [G_zero]; exact ht
    have h2 : t ≤ G (44 * t) := by have := G_lower (44 * t) (by linarith); linarith
    obtain ⟨θ, _, hθ⟩ := intermediate_value_Icc (by linarith : (0:ℝ) ≤ 44 * t)
      G_cont.continuousOn ⟨h1, h2⟩
    exact ⟨θ, hθ⟩
  · have h1 : t ≤ G 0 := by rw [G_zero]; exact ht
    have h2 : G (44 * t) ≤ t := by have := G_upper (44 * t) (by linarith); linarith
    obtain ⟨θ, _, hθ⟩ := intermediate_value_Icc (by linarith : 44 * t ≤ 0)
      G_cont.continuousOn ⟨h2, h1⟩
    exact ⟨θ, hθ⟩

noncomputable def Gi : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective G G_mono G_surj

noncomputable def Θ (t : ℝ) : ℝ := Gi.symm t

lemma G_Θ (t : ℝ) : G (Θ t) = t := Gi.apply_symm_apply t

lemma Θ_G (θ : ℝ) : Θ (G θ) = θ := Gi.symm_apply_apply θ

lemma Θ_deriv (t : ℝ) : HasDerivAt Θ (H (Θ t)) t := by
  have h := HasDerivAt.of_local_left_inverse (Gi.symm.continuous.continuousAt (x := t))
    (G_deriv (Θ t)) (by have := H_pos (Θ t); positivity)
    (Filter.Eventually.of_forall G_Θ)
  have e : Θ = ⇑Gi.symm := rfl
  rw [e]; convert h using 1
  · rfl
  · simp [Θ]

noncomputable def T : ℝ := G (2 * π)

lemma T_pos : 0 < T := by
  have := G_mono (show (0:ℝ) < 2 * π by positivity); rw [G_zero] at this; exact this

lemma G_add (θ : ℝ) : G (θ + 2 * π) = G θ + T := by
  unfold G T
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := θ)
    (iH_cont.intervalIntegrable _ _) (iH_cont.intervalIntegrable _ _)]
  have hp : Function.Periodic (fun u => 1 / H u) (2 * π) := fun u => by simp [H_periodic u]
  rw [hp.intervalIntegral_add_eq θ 0]
  simp only [zero_add]
  rfl

end HS16

open Real

namespace HS16

lemma Θ_add (t : ℝ) : Θ (t + T) = Θ t + 2 * π := by
  apply G_mono.injective
  rw [G_Θ, G_add, G_Θ]

noncomputable def γ (t : ℝ) : ℝ × ℝ := (X (Θ t), -sin (Θ t) / 2)

lemma key_x (θ : ℝ) : -sin θ / √2 / (2 * X θ) * H θ =
    2 * (-sin θ / 2) * (10 + X θ * (-sin θ / 2)) := by
  have hx := X_pos θ
  have hr := s2pos
  unfold H
  field_simp
  ring

lemma key_y (θ : ℝ) : -(cos θ * H θ) / 2 =
    20 * X θ + (-sin θ / 2) - 20 * X θ ^ 3 - 2 * X θ ^ 2 * (-sin θ / 2) + 4 * (-sin θ / 2) ^ 3 := by
  have hX := X_sq θ
  have hr := s2sq
  have hr0 := s2pos.ne'
  have hcs := sin_sq_add_cos_sq θ
  set r := √2
  set c := cos θ
  set s := sin θ
  set x := X θ
  have hc : c = r * (x ^ 2 - 1) := by
    rw [hX]; field_simp; ring
  have hcr : c * r = 2 * x ^ 2 - 2 := by rw [hc]; linear_combination (x^2 - 1) * hr
  have hc2 : c ^ 2 = 2 * (x ^ 2 - 1) ^ 2 := by
    linear_combination (c + r * (x ^ 2 - 1)) * hc + (x ^ 2 - 1) ^ 2 * hr
  unfold H
  linear_combination (-10 * x + x ^ 2 * s / 2) * hcr + (s / 2) * hcs - (s / 2) * hc2

lemma γ_deriv (t : ℝ) : HasDerivAt γ (Fx (γ t)) t := by
  have h1 := (X_deriv (Θ t)).comp t (Θ_deriv t)
  have h2 := ((hasDerivAt_sin (Θ t)).comp t (Θ_deriv t)).neg.div_const 2
  have := h1.prodMk h2
  convert this using 1
  · funext x; simp [γ]
  · rw [key_x, key_y]; simp [Fx, γ]

lemma γ_periodic (t : ℝ) : γ (t + T) = γ t := by
  simp [γ, Θ_add, X, cos_add_two_pi, sin_add_two_pi]

lemma fx_γ (t : ℝ) : fx (γ t) = 0 := by
  have hX := X_sq (Θ t)
  have hr := s2sq
  have hr0 := s2pos.ne'
  have hcs := sin_sq_add_cos_sq (Θ t)
  simp only [fx, γ]
  have : X (Θ t) ^ 4 = (X (Θ t) ^ 2) ^ 2 := by ring
  rw [this, hX]
  field_simp
  linear_combination 8 * hcs + (4 * sin (Θ t) ^ 2 - 4) * hr

lemma exists_angle (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : ∃ θ, cos θ = c ∧ sin θ = s := by
  set z : ℂ := ⟨c, s⟩
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk]
    rw [show c * c + s * s = 1 by linear_combination h]; simp
  have hz : z ≠ 0 := by intro h0; rw [h0] at hn; simp at hn
  refine ⟨Complex.arg z, ?_, ?_⟩
  · rw [Complex.cos_arg hz, hn]; simp [z]
  · rw [Complex.sin_arg, hn]; simp [z]

lemma range_γ : Set.range γ = {p | fx p = 0 ∧ 0 < p.1} := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨fx_γ t, by have := X_pos (Θ t); simp [γ]; linarith⟩
  · rintro ⟨hf, hp⟩
    have hr := s2sq
    have hr0 := s2pos.ne'
    obtain ⟨θ, hc, hs⟩ := exists_angle (√2 * (p.1 ^ 2 - 1)) (-2 * p.2) (by
      simp only [fx] at hf
      linear_combination (p.1 ^ 2 - 1) ^ 2 * hr + hf)
    refine ⟨G θ, ?_⟩
    simp only [γ, Θ_G]
    ext
    · simp only [X]
      rw [hc]
      have : 1 + √2 * (p.1 ^ 2 - 1) / √2 = p.1 ^ 2 := by field_simp; ring
      rw [this, Real.sqrt_sq hp.le]
    · simp only; rw [hs]; ring

lemma γ_nonconst : ∃ t, γ t ≠ γ 0 := by
  by_contra h
  push Not at h
  have h1 := h (G 0)
  have h2 := h (G π)
  rw [← h2] at h1
  have := congrArg (fun p => p.1 ^ 2) h1
  simp only [γ, Θ_G, X_sq, cos_zero, cos_pi] at this
  have hr := s2pos
  have : (1:ℝ) / √2 = -1 / √2 := by linarith
  rw [div_eq_div_iff hr.ne' hr.ne'] at this
  linarith

end HS16

open Real

namespace HS16

lemma comp_fst {δ : ℝ → ℝ × ℝ} {v : ℝ × ℝ} {t : ℝ} (h : HasDerivAt δ v t) :
    HasDerivAt (fun s => (δ s).1) v.1 t := by
  have := hasFDerivAt_fst.comp_hasDerivAt t h
  exact this

lemma comp_snd {δ : ℝ → ℝ × ℝ} {v : ℝ × ℝ} {t : ℝ} (h : HasDerivAt δ v t) :
    HasDerivAt (fun s => (δ s).2) v.2 t := by
  have := hasFDerivAt_snd.comp_hasDerivAt t h
  exact this

lemma periodic_mono_const {u : ℝ → ℝ} (hu : Monotone u) {T' : ℝ} (hT : 0 < T')
    (hp : ∀ t, u (t + T') = u t) (t : ℝ) : u t = u 0 := by
  have hn : ∀ n : ℕ, ∀ s, u (s + n * T') = u s := by
    intro n; induction n with
    | zero => simp
    | succ n ih => intro s; rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, hp, ih]
  obtain ⟨n, hn'⟩ := exists_nat_gt (|t| / T')
  rw [div_lt_iff₀ hT] at hn'
  rcases le_total 0 t with ht | ht
  · apply le_antisymm
    · calc u t ≤ u (0 + n * T') := hu (by rw [abs_of_nonneg ht] at hn'; linarith)
        _ = u 0 := hn n 0
    · exact hu ht
  · apply le_antisymm (hu ht)
    calc u 0 ≤ u (t + n * T') := hu (by rw [abs_of_nonpos ht] at hn'; linarith)
      _ = u t := hn n t

theorem periodic_on_curve {δ : ℝ → ℝ × ℝ} (hδ : ∀ t, HasDerivAt δ (Fx (δ t)) t) {T' : ℝ}
    (hT : 0 < T') (hp : ∀ t, δ (t + T') = δ t) (hnc : ∃ t, δ t ≠ δ 0) (t : ℝ) :
    fx (δ t) = 0 := by
  set x := fun s => (δ s).1
  set y := fun s => (δ s).2
  have hx : ∀ s, HasDerivAt x (2 * y s * (10 + x s * y s)) s := fun s => by
    have := comp_fst (hδ s); simpa [Fx] using this
  have hy : ∀ s, HasDerivAt y (20 * x s + y s - 20 * x s ^ 3 - 2 * x s ^ 2 * y s + 4 * y s ^ 3) s :=
    fun s => by have := comp_snd (hδ s); simpa [Fx] using this
  set g := fun s => fx (δ s)
  have hg : ∀ s, HasDerivAt g (8 * y s ^ 2 * g s) s := fun s => by
    have := (((((hx s).pow 4).const_mul 2).sub (((hx s).pow 2).const_mul 4)).add
      (((hy s).pow 2).const_mul 4)).add_const 1
    refine HasDerivAt.congr_of_eventuallyEq (this.congr_deriv ?_)
      (Filter.Eventually.of_forall fun r => ?_)
    · simp only [g, fx, x, y]; push_cast; ring
    · simp [g, fx, x, y]
  set u := fun s => g s ^ 2
  have hu : ∀ s, HasDerivAt u (16 * y s ^ 2 * g s ^ 2) s := fun s => by
    have := (hg s).pow 2
    refine HasDerivAt.congr_of_eventuallyEq (this.congr_deriv ?_)
      (Filter.Eventually.of_forall fun r => ?_)
    · push_cast; ring
    · simp [u]
  have hmono : Monotone u := by
    apply monotone_of_deriv_nonneg (fun s => (hu s).differentiableAt)
    intro s; rw [(hu s).deriv]; positivity
  have hup : ∀ s, u (s + T') = u s := fun s => by simp only [u, g, hp]
  have hc : ∀ s, u s = u 0 := periodic_mono_const hmono hT hup
  have hu0 : ∀ s, 16 * y s ^ 2 * g s ^ 2 = 0 := fun s => by
    have h1 : HasDerivAt u 0 s := by
      have : u = fun _ => u 0 := funext hc
      rw [this]; exact hasDerivAt_const s _
    exact (hu s).unique h1
  by_contra hne
  have hg0 : ∀ s, g s ≠ 0 := by
    intro s hs
    have : u s = 0 := by simp [u, hs]
    rw [hc s, ← hc t] at this
    exact hne (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
  have hy0 : ∀ s, y s = 0 := fun s => by
    have := hu0 s
    have h2 := pow_ne_zero 2 (hg0 s)
    simp [h2] at this; exact this
  have hx' : ∀ s, HasDerivAt x 0 s := fun s => by
    have := hx s; rw [hy0 s] at this; simpa using this
  have hxc : ∀ s, x s = x 0 := fun s =>
    is_const_of_deriv_eq_zero (fun s => (hx' s).differentiableAt)
      (fun s => (hx' s).deriv) s 0
  obtain ⟨t1, ht1⟩ := hnc
  apply ht1
  ext
  · exact hxc t1
  · show y t1 = y 0; rw [hy0, hy0]

lemma Fx_contDiff : ContDiff ℝ 1 Fx := by unfold Fx; fun_prop

lemma mem_ball_of_fx {p : ℝ × ℝ} (h : fx p = 0) : p ∈ Metric.closedBall (0 : ℝ × ℝ) 2 := by
  simp only [fx] at h
  rw [mem_closedBall_zero_iff, norm_prod_le_iff]
  simp only [Real.norm_eq_abs]
  constructor
  · rw [abs_le]; constructor <;> nlinarith [sq_nonneg (p.1 ^ 2 - 1), sq_nonneg p.2, sq_nonneg (p.1 - 2), sq_nonneg (p.1 + 2)]
  · rw [abs_le]; constructor <;> nlinarith [sq_nonneg (p.1 ^ 2 - 1), sq_nonneg p.2]

theorem unique_sol {δ ε : ℝ → ℝ × ℝ} (hδ : ∀ t, HasDerivAt δ (Fx (δ t)) t)
    (hε : ∀ t, HasDerivAt ε (Fx (ε t)) t) (hδf : ∀ t, fx (δ t) = 0) (hεf : ∀ t, fx (ε t) = 0)
    (h0 : δ 0 = ε 0) : δ = ε := by
  obtain ⟨K, hK⟩ := Fx_contDiff.contDiffOn.exists_lipschitzOnWith (s := Metric.closedBall 0 2)
    (by norm_num) (convex_closedBall 0 2) (isCompact_closedBall 0 2)
  exact ODE_solution_unique_univ (v := fun _ => Fx) (s := fun _ => Metric.closedBall 0 2)
    (t₀ := 0) (fun _ => hK) (fun t => ⟨hδ t, mem_ball_of_fx (hδf t)⟩)
    (fun t => ⟨hε t, mem_ball_of_fx (hεf t)⟩) h0

end HS16

open Real HilbertSixteenth

namespace HS16

theorem cycle_of (γ0 : ℝ → ℝ × ℝ) (hγ0 : ∀ t, HasDerivAt γ0 (Fx (γ0 t)) t)
    (hper : ∀ t, γ0 (t + T) = γ0 t) (hnc : ∃ t, γ0 t ≠ γ0 0) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hrange : Set.range γ0 = {p | fx p = 0} ∩ U) : IsLimitCycle Fx (Set.range γ0) := by
  refine ⟨⟨γ0, T, ⟨hγ0, T_pos, hper, hnc⟩, rfl⟩, U, hU, ?_, ?_⟩
  · rw [hrange]; exact Set.inter_subset_right
  · rintro O' ⟨δ, T', ⟨hδ, hT', hp', hnc'⟩, rfl⟩ hsub
    have hδf := periodic_on_curve hδ hT' hp' hnc'
    have h0 : δ 0 ∈ Set.range γ0 := by
      rw [hrange]; exact ⟨hδf 0, hsub ⟨0, rfl⟩⟩
    obtain ⟨s0, hs0⟩ := h0
    have hγf : ∀ t, fx (γ0 t) = 0 := fun t => by
      have : γ0 t ∈ Set.range γ0 := ⟨t, rfl⟩
      rw [hrange] at this; exact this.1
    have hε : ∀ t, HasDerivAt (fun t => γ0 (t + s0)) (Fx (γ0 (t + s0))) t := fun t =>
      (hγ0 (t + s0)).comp_add_const t s0
    have heq := unique_sol hδ hε hδf (fun t => hγf _) (by simp [hs0])
    rw [heq]
    ext p; constructor
    · rintro ⟨t, rfl⟩; exact ⟨t + s0, rfl⟩
    · rintro ⟨t, rfl⟩; exact ⟨t - s0, by simp⟩

lemma γneg_deriv (t : ℝ) : HasDerivAt (fun t => -γ t) (Fx (-γ t)) t := by
  rw [Fx_neg]; exact (γ_deriv t).neg

lemma range_γneg : Set.range (fun t => -γ t) = {p | fx p = 0} ∩ {p | p.1 < 0} := by
  ext p; constructor
  · rintro ⟨t, rfl⟩
    have : γ t ∈ Set.range γ := ⟨t, rfl⟩
    rw [range_γ] at this
    exact ⟨by simp [fx_neg, this.1], by simp; exact this.2⟩
  · rintro ⟨h1, h2⟩
    have : -p ∈ Set.range γ := by
      rw [range_γ]; exact ⟨by rw [fx_neg]; exact h1, by simp; linarith [show p.1 < 0 from h2]⟩
    obtain ⟨t, ht⟩ := this
    exact ⟨t, by simp [ht]⟩

end HS16

open HS16 in
theorem solution :
    let x : Poly2 := MvPolynomial.X 0
    let y : Poly2 := MvPolynomial.X 1
    let V : PolyField :=
      ⟨2 * y * (10 + x * y), 20 * x + y - 20 * x ^ 3 - 2 * x ^ 2 * y + 4 * y ^ 3⟩
    let f : Poly2 := 2 * x ^ 4 - 4 * x ^ 2 + 4 * y ^ 2 + 1
    IsAlgebraicLimitCycle V {p | p ∈ zeroSet f ∧ 0 < p.1} ∧
      IsAlgebraicLimitCycle V {p | p ∈ zeroSet f ∧ p.1 < 0} := by
  intro x y V f
  have hF : V.toField = Fx := by
    funext p; simp [V, x, y, PolyField.toField, evalAt, Fx]
  have hf : ∀ p, evalAt f p = fx p := fun p => by simp [f, x, y, evalAt, fx]
  have hf0 : f ≠ 0 := by
    intro h; have := hf (0, 0); rw [h] at this; simp [evalAt, fx] at this
  have e1 : {p | p ∈ zeroSet f ∧ 0 < p.1} = Set.range γ := by
    rw [range_γ]; ext p; simp [zeroSet, hf]
  have e2 : {p | p ∈ zeroSet f ∧ p.1 < 0} = Set.range (fun t => -γ t) := by
    rw [range_γneg]; ext p; simp [zeroSet, hf]
  refine ⟨⟨?_, f, hf0, fun p hp => hp.1⟩, ⟨?_, f, hf0, fun p hp => hp.1⟩⟩
  · rw [hF, e1]
    refine cycle_of γ γ_deriv γ_periodic γ_nonconst {p | 0 < p.1}
      (isOpen_lt continuous_const continuous_fst) ?_
    rw [range_γ]; rfl
  · rw [hF, e2]
    refine cycle_of (fun t => -γ t) γneg_deriv (fun t => by simp [γ_periodic])
      ?_ {p | p.1 < 0} (isOpen_lt continuous_fst continuous_const) range_γneg
    obtain ⟨t, ht⟩ := γ_nonconst
    exact ⟨t, fun h => ht (neg_inj.1 h)⟩
