-- Prove2me | solution 1 for MetodosNumericos.lagrange_interpolation_error
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:45:00.47933+00:00
-- url     : https://prove2.me/submissions/d4f0aa21-1ce7-4caa-aa81-6a6ae95c55fc

import Mathlib
import Definitions.Def_MetodosNumericos_edoDefs
import Definitions.Def_MetodosNumericos_interpolacaoDefs
import Definitions.Def_MetodosNumericos_integracaoDefs

open MetodosNumericos

theorem W7b_MetodosNumericos_euler_global_error (f : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (x0 y0 X L : ℝ) (hX : x0 < X)
    (hphi0 : phi x0 = y0)
    (hsol : ∀ x ∈ Set.Icc x0 X, HasDerivAt phi (f x (phi x)) x)
    (hphi2 : ContDiffOn ℝ 2 phi (Set.Icc x0 X))
    (hlip : ∀ x ∈ Set.Icc x0 X, ∀ u v : ℝ, |f x u - f x v| ≤ L * |u - v|) :
    ∃ C > 0, ∀ h ∈ Set.Ioc (0 : ℝ) 1, ∀ i : ℕ, x0 + i * h ≤ X →
      |eulerSeq f x0 y0 h i - phi (x0 + i * h)| ≤ C * h := by
  set s := Set.Icc x0 X with hs
  have hx0 : x0 ∈ s := Set.left_mem_Icc.mpr hX.le
  have hL : 0 ≤ L := by
    have := hlip x0 hx0 1 0
    have h2 : 0 ≤ |f x0 1 - f x0 0| := abs_nonneg _
    norm_num at this; linarith
  have hu : UniqueDiffOn ℝ s := uniqueDiffOn_Icc hX
  have h1 : ContDiffOn ℝ 1 (derivWithin phi s) s := hphi2.derivWithin hu (by norm_num)
  have hd : DifferentiableOn ℝ (derivWithin phi s) s := h1.differentiableOn (by norm_num)
  have hc : ContinuousOn (derivWithin (derivWithin phi s) s) s :=
    h1.continuousOn_derivWithin hu le_rfl
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK x0 hx0)
  have hder : ∀ x ∈ s, derivWithin phi s x = f x (phi x) := fun x hx =>
    (hsol x hx).hasDerivWithinAt.derivWithin (hu x hx)
  have hLip : ∀ x ∈ s, ∀ y ∈ s, |f y (phi y) - f x (phi x)| ≤ K * |y - x| := by
    intro x hx y hy
    have := Convex.norm_image_sub_le_of_norm_derivWithin_le hd (fun z hz => hK z hz)
      (convex_Icc x0 X) hx hy
    rw [hder x hx, hder y hy] at this
    simpa [Real.norm_eq_abs] using this
  -- local truncation error
  have hloc : ∀ x h : ℝ, 0 < h → x0 ≤ x → x + h ≤ X →
      |phi (x + h) - phi x - h * f x (phi x)| ≤ K * h ^ 2 := by
    intro x h hh hx hxh
    have hxs : x ∈ s := ⟨hx, by linarith⟩
    have hcont : ContinuousOn phi (Set.Icc x (x + h)) := by
      intro z hz
      exact (hsol z ⟨by linarith [hz.1], by linarith [hz.2]⟩).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope phi (fun z => f z (phi z))
      (by linarith : x < x + h) hcont
      (fun z hz => hsol z ⟨by linarith [hz.1], by linarith [hz.2]⟩)
    have hcs : c ∈ s := ⟨by linarith [hc.1], by linarith [hc.2]⟩
    have e : phi (x + h) - phi x = h * f c (phi c) := by
      have hh0 : h ≠ 0 := hh.ne'
      rw [hceq, add_sub_cancel_left]; field_simp
    rw [e, ← mul_sub, abs_mul, abs_of_pos hh]
    have := hLip x hxs c hcs
    have hcx : |c - x| ≤ h := by
      rw [abs_of_pos (by linarith [hc.1])]; linarith [hc.2]
    calc h * |f c (phi c) - f x (phi x)| ≤ h * (K * h) :=
          mul_le_mul_of_nonneg_left (this.trans (mul_le_mul_of_nonneg_left hcx hK0)) hh.le
      _ = K * h ^ 2 := by ring
  -- discrete Gronwall by induction
  have hind : ∀ h : ℝ, 0 < h → ∀ i : ℕ, x0 + i * h ≤ X →
      |eulerSeq f x0 y0 h i - phi (x0 + i * h)| ≤ i * K * h ^ 2 * (1 + h * L) ^ i := by
    intro h hh i
    induction i with
    | zero => intro _; simp [eulerSeq, hphi0]
    | succ i ih =>
      intro hi
      push_cast at hi ⊢
      have hi' : x0 + i * h ≤ X := by linarith
      have ihb := ih hi'
      have hxi : x0 + i * h ∈ s := ⟨by nlinarith [Nat.cast_nonneg (α := ℝ) i], hi'⟩
      set y := eulerSeq f x0 y0 h i with hy
      set xi := x0 + i * h with hxi_def
      have hstep : eulerSeq f x0 y0 h (i + 1) = y + h * f xi y := rfl
      have hx1 : x0 + (i + 1) * h = xi + h := by rw [hxi_def]; ring
      rw [hstep, hx1]
      have hloc' := hloc xi h hh hxi.1 (by linarith)
      have hl := hlip xi hxi y (phi xi)
      have eq : y + h * f xi y - phi (xi + h) = (y - phi xi) + h * (f xi y - f xi (phi xi))
          - (phi (xi + h) - phi xi - h * f xi (phi xi)) := by ring
      rw [eq]
      have hpow : 1 ≤ (1 + h * L) ^ i := one_le_pow₀ (by nlinarith)
      have hA : |h * (f xi y - f xi (phi xi))| ≤ h * L * |y - phi xi| := by
        rw [abs_mul, abs_of_pos hh, mul_assoc]
        exact mul_le_mul_of_nonneg_left hl hh.le
      calc |(y - phi xi) + h * (f xi y - f xi (phi xi))
            - (phi (xi + h) - phi xi - h * f xi (phi xi))|
          ≤ |y - phi xi| + h * L * |y - phi xi| + K * h ^ 2 := by
            refine (abs_sub _ _).trans ?_
            refine add_le_add ((abs_add_le _ _).trans ?_) hloc'
            linarith
        _ = (1 + h * L) * |y - phi xi| + K * h ^ 2 := by ring
        _ ≤ (1 + h * L) * (i * K * h ^ 2 * (1 + h * L) ^ i) + K * h ^ 2 * (1 + h * L) ^ i := by
            have hKh : 0 ≤ K * h ^ 2 := by positivity
            have h1L : 0 ≤ 1 + h * L := by positivity
            nlinarith [mul_le_mul_of_nonneg_left ihb h1L, mul_le_mul_of_nonneg_left hpow hKh]
        _ ≤ ((i : ℝ) + 1) * K * h ^ 2 * (1 + h * L) ^ (i + 1) := by
            have : 0 ≤ K * h ^ 2 * (1 + h * L) ^ i * (h * L) := by positivity
            have e : ((i : ℝ) + 1) * K * h ^ 2 * (1 + h * L) ^ (i + 1) -
                ((1 + h * L) * (i * K * h ^ 2 * (1 + h * L) ^ i) + K * h ^ 2 * (1 + h * L) ^ i) =
                K * h ^ 2 * (1 + h * L) ^ i * (h * L) := by ring
            linarith
  have hXx : 0 < X - x0 := sub_pos.mpr hX
  refine ⟨K * (X - x0) * Real.exp (L * (X - x0)) + 1, by
    have := mul_nonneg (mul_nonneg hK0 hXx.le) (Real.exp_pos (L * (X - x0))).le
    linarith, ?_⟩
  intro h hh i hi
  have hb := hind h hh.1 i hi
  have hih : (i : ℝ) * h ≤ X - x0 := by linarith
  have hexp : (1 + h * L) ^ i ≤ Real.exp (L * (X - x0)) := by
    calc (1 + h * L) ^ i ≤ (Real.exp (h * L)) ^ i := by
          gcongr
          · nlinarith [hh.1]
          · linarith [Real.add_one_le_exp (h * L)]
      _ = Real.exp (L * (i * h)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (L * (X - x0)) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left hih hL
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  calc |eulerSeq f x0 y0 h i - phi (x0 + i * h)| ≤ i * K * h ^ 2 * (1 + h * L) ^ i := hb
    _ = K * h * ((i * h) * (1 + h * L) ^ i) := by ring
    _ ≤ K * h * ((X - x0) * Real.exp (L * (X - x0))) := by
        apply mul_le_mul_of_nonneg_left _ (by nlinarith [hh.1])
        have h1L : 0 ≤ 1 + h * L := by have := mul_nonneg hh.1.le hL; linarith
        apply mul_le_mul hih hexp (pow_nonneg h1L _) (by linarith)
    _ ≤ (K * (X - x0) * Real.exp (L * (X - x0)) + 1) * h := by nlinarith [hh.1]

theorem W7b_MetodosNumericos_lip (f : ℝ → ℝ → ℝ) (x0 y0 a b L : ℝ)
    (hlip : ∀ x ∈ Set.Icc (x0 - a) (x0 + a), ∀ u ∈ Set.Icc (y0 - b) (y0 + b),
      ∀ v ∈ Set.Icc (y0 - b) (y0 + b), |f x u - f x v| ≤ L * |u - v|)
    (t : ℝ) (ht : t ∈ Set.Icc (x0 - a) (x0 + a)) :
    LipschitzOnWith (Real.toNNReal L) (f t) (Set.Icc (y0 - b) (y0 + b)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
  exact (hlip t ht u hu v hv).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

theorem W7b_MetodosNumericos_pvi_existence_uniqueness (f : ℝ → ℝ → ℝ) (x0 y0 a b L : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Set.Icc (x0 - a) (x0 + a) ×ˢ Set.Icc (y0 - b) (y0 + b)))
    (hlip : ∀ x ∈ Set.Icc (x0 - a) (x0 + a), ∀ u ∈ Set.Icc (y0 - b) (y0 + b),
      ∀ v ∈ Set.Icc (y0 - b) (y0 + b), |f x u - f x v| ≤ L * |u - v|) :
    ∃ h > 0,
      (∃ phi : ℝ → ℝ, phi x0 = y0 ∧
        (∀ x ∈ Set.Icc (x0 - h) (x0 + h), HasDerivAt phi (f x (phi x)) x) ∧
        ∀ x ∈ Set.Icc (x0 - h) (x0 + h), phi x ∈ Set.Icc (y0 - b) (y0 + b)) ∧
      (∀ phi psi : ℝ → ℝ,
        (phi x0 = y0 ∧ ∀ x ∈ Set.Icc (x0 - h) (x0 + h), HasDerivAt phi (f x (phi x)) x) →
        (psi x0 = y0 ∧ ∀ x ∈ Set.Icc (x0 - h) (x0 + h), HasDerivAt psi (f x (psi x)) x) →
        (∀ x ∈ Set.Icc (x0 - h) (x0 + h), phi x ∈ Set.Icc (y0 - b) (y0 + b)) →
        (∀ x ∈ Set.Icc (x0 - h) (x0 + h), psi x ∈ Set.Icc (y0 - b) (y0 + b)) →
        Set.EqOn phi psi (Set.Icc (x0 - h) (x0 + h))) := by
  have hBc : IsCompact (Set.Icc (x0 - a) (x0 + a) ×ˢ Set.Icc (y0 - b) (y0 + b)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hBc.exists_bound_of_continuousOn hcont
  set M : ℝ := max C 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  set h1 : ℝ := min a (b / M) with hh1def
  have hh1 : 0 < h1 := lt_min ha (div_pos hb hM)
  have hh1a : h1 ≤ a := min_le_left _ _
  have hh1b : M * h1 ≤ b := by
    have := min_le_right a (b / M)
    rw [← hh1def] at this
    calc M * h1 ≤ M * (b / M) := mul_le_mul_of_nonneg_left this hM.le
      _ = b := by field_simp
  refine ⟨h1 / 2, by positivity, ?_, ?_⟩
  · -- existence via Picard-Lindelöf
    have ht0 : x0 ∈ Set.Icc (x0 - h1) (x0 + h1) := ⟨by linarith, by linarith⟩
    let t0 : Set.Icc (x0 - h1) (x0 + h1) := ⟨x0, ht0⟩
    have hball : Metric.closedBall y0 (b.toNNReal : ℝ) = Set.Icc (y0 - b) (y0 + b) := by
      rw [Real.coe_toNNReal _ hb.le, Real.closedBall_eq_Icc]
    have htime : ∀ t ∈ Set.Icc (x0 - h1) (x0 + h1), t ∈ Set.Icc (x0 - a) (x0 + a) :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hPL : IsPicardLindelof f t0 y0 b.toNNReal 0 M.toNNReal L.toNNReal :=
      { lipschitzOnWith := by
          intro t ht
          rw [hball]
          exact W7b_MetodosNumericos_lip f x0 y0 a b L hlip t (htime t ht)
        continuousOn := by
          intro y hy
          rw [hball] at hy
          have hmaps : Set.MapsTo (fun t : ℝ => (t, y)) (Set.Icc (x0 - h1) (x0 + h1))
              (Set.Icc (x0 - a) (x0 + a) ×ˢ Set.Icc (y0 - b) (y0 + b)) :=
            fun t ht => ⟨htime t ht, hy⟩
          exact hcont.comp (by fun_prop) hmaps
        norm_le := by
          intro t ht y hy
          rw [hball] at hy
          rw [Real.coe_toNNReal _ hM.le]
          exact (hC (t, y) ⟨htime t ht, hy⟩).trans (le_max_left _ _)
        mul_max_le := by
          simp only [Real.coe_toNNReal _ hM.le, Real.coe_toNNReal _ hb.le, NNReal.coe_zero,
            sub_zero, t0]
          have : max (x0 + h1 - x0) (x0 - (x0 - h1)) = h1 := by
            rw [show x0 + h1 - x0 = h1 by ring, show x0 - (x0 - h1) = h1 by ring, max_self]
          rw [this]; exact hh1b }
    have hx : y0 ∈ Metric.closedBall y0 ((0 : NNReal) : ℝ) := Metric.mem_closedBall_self le_rfl
    obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hPL hx
    refine ⟨α.compProj, ?_, ?_, ?_⟩
    · show α.compProj (t0 : ℝ) = y0
      rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
    · intro t ht
      have htI : t ∈ Set.Icc (x0 - h1) (x0 + h1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hderiv : HasDerivWithinAt α.compProj (f t (α.compProj t))
          (Set.Icc (x0 - h1) (x0 + h1)) t := by
        apply ODE.hasDerivWithinAt_picard_Icc t0.2 hPL.continuousOn_uncurry
          α.continuous_compProj.continuousOn
          (fun _ ht' ↦ α.compProj_mem_closedBall hPL.mul_max_le) y0 htI |>.congr_of_mem _ htI
        intro t' ht'
        nth_rw 1 [← hα]
        rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
      exact hderiv.hasDerivAt (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))
    · intro t _
      have := α.compProj_mem_closedBall hPL.mul_max_le (t := t)
      rwa [hball] at this
  · -- uniqueness via Gronwall
    rintro phi psi ⟨hphi0, hphi⟩ ⟨hpsi0, hpsi⟩ hphir hpsir
    have hx0 : x0 ∈ Set.Ioo (x0 - h1 / 2) (x0 + h1 / 2) := ⟨by linarith, by linarith⟩
    have hsub : ∀ t ∈ Set.Ioo (x0 - h1 / 2) (x0 + h1 / 2), t ∈ Set.Icc (x0 - h1 / 2) (x0 + h1 / 2) :=
      fun t ht => Set.Ioo_subset_Icc_self ht
    exact ODE_solution_unique_of_mem_Icc (v := f) (s := fun _ => Set.Icc (y0 - b) (y0 + b))
      (K := L.toNNReal)
      (fun t ht => W7b_MetodosNumericos_lip f x0 y0 a b L hlip t
        ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      hx0
      (fun t ht => (hphi t ht).continuousAt.continuousWithinAt)
      (fun t ht => hphi t (hsub t ht))
      (fun t ht => hphir t (hsub t ht))
      (fun t ht => (hpsi t ht).continuousAt.continuousWithinAt)
      (fun t ht => hpsi t (hsub t ht))
      (fun t ht => hpsir t (hsub t ht))
      (by rw [hphi0, hpsi0])

/-! ## Lagrange interpolation error -/

/-- One Rolle step: `k+2` zeros of `g` give `k+1` zeros of `deriv g`. -/
theorem W7b_MetodosNumericos_rolle_step (a b : ℝ) (g : ℝ → ℝ) (k : ℕ)
    (hg : ContinuousOn g (Set.Ioo a b)) (S : Finset ℝ) (hS : S.card = k + 2)
    (hSs : ∀ z ∈ S, z ∈ Set.Ioo a b) (hz : ∀ z ∈ S, g z = 0) :
    ∃ T : Finset ℝ, T.card = k + 1 ∧ (∀ z ∈ T, z ∈ Set.Ioo a b) ∧ ∀ z ∈ T, deriv g z = 0 := by
  set e := S.orderEmbOfFin hS with he
  have hmem : ∀ i, e i ∈ S := fun i => S.orderEmbOfFin_mem hS i
  have hstep : ∀ j : Fin (k + 1), ∃ t ∈ Set.Ioo (e j.castSucc) (e j.succ), deriv g t = 0 := by
    intro j
    have hlt : e j.castSucc < e j.succ := e.strictMono (Fin.castSucc_lt_succ)
    apply exists_deriv_eq_zero hlt
    · apply hg.mono
      intro z hz
      exact ⟨lt_of_lt_of_le (hSs _ (hmem _)).1 hz.1, lt_of_le_of_lt hz.2 (hSs _ (hmem _)).2⟩
    · rw [hz _ (hmem _), hz _ (hmem _)]
  choose t ht htz using hstep
  have hmono : StrictMono t := by
    intro i j hij
    have h1 := (ht i).2
    have h2 := (ht j).1
    have h3 : e i.succ ≤ e j.castSucc := by
      apply e.monotone
      rw [Fin.le_def]; simp; omega
    linarith
  refine ⟨Finset.univ.image t, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
  · intro z hz
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨lt_trans (hSs _ (hmem _)).1 (ht j).1, lt_trans (ht j).2 (hSs _ (hmem _)).2⟩
  · intro z hz
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
    exact htz j

/-- Generalized Rolle theorem on an open interval. -/
theorem W7b_MetodosNumericos_gen_rolle (a b : ℝ) (m : ℕ) : ∀ (g : ℝ → ℝ),
    ContDiffOn ℝ (m : ℕ) g (Set.Ioo a b) → ∀ S : Finset ℝ, S.card = m + 1 →
    (∀ z ∈ S, z ∈ Set.Ioo a b) → (∀ z ∈ S, g z = 0) →
    ∃ xi ∈ Set.Ioo a b, iteratedDerivWithin m g (Set.Ioo a b) xi = 0 := by
  induction m with
  | zero =>
    intro g _ S hS hSs hz
    obtain ⟨z, hzS⟩ : S.Nonempty := by rw [← Finset.card_pos, hS]; norm_num
    exact ⟨z, hSs z hzS, by simpa using hz z hzS⟩
  | succ m ih =>
    intro g hg S hS hSs hz
    obtain ⟨T, hT, hTs, hTz⟩ := W7b_MetodosNumericos_rolle_step a b g m hg.continuousOn S hS hSs hz
    have hg' : ContDiffOn ℝ (m : ℕ) (deriv g) (Set.Ioo a b) :=
      hg.deriv_of_isOpen isOpen_Ioo (by push_cast; exact le_rfl)
    obtain ⟨xi, hxi, hxi0⟩ := ih (deriv g) hg' T hT hTs hTz
    refine ⟨xi, hxi, ?_⟩
    rw [iteratedDerivWithin_of_isOpen_eq_iterate isOpen_Ioo hxi]
    rw [iteratedDerivWithin_of_isOpen_eq_iterate isOpen_Ioo hxi] at hxi0
    rw [Function.iterate_succ_apply]
    exact hxi0

theorem W7b_MetodosNumericos_iterate_derivative_add (p q : Polynomial ℝ) (k : ℕ) :
    Polynomial.derivative^[k] (p + q) =
      Polynomial.derivative^[k] p + Polynomial.derivative^[k] q := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, Polynomial.derivative_add]

theorem W7b_MetodosNumericos_iteratedDeriv_poly (p : Polynomial ℝ) (k : ℕ) :
    iteratedDeriv k (fun t => p.eval t) = fun t => (Polynomial.derivative^[k] p).eval t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [Polynomial.deriv, Function.iterate_succ_apply']

/-- The Lagrange interpolant as a polynomial. -/
noncomputable def W7b_MetodosNumericos_Ppoly {n : ℕ} (xs fs : Fin (n + 1) → ℝ) : Polynomial ℝ :=
  ∑ i : Fin (n + 1), Polynomial.C (fs i) *
    ∏ j ∈ Finset.univ.erase i,
      (Polynomial.C (xs i - xs j)⁻¹ * (Polynomial.X - Polynomial.C (xs j)))

theorem W7b_MetodosNumericos_polyCD (p : Polynomial ℝ) (m : WithTop ℕ∞) :
    ContDiff ℝ m (fun t => p.eval t) := by
  have := p.contDiff_aeval (𝕜 := ℝ) m
  simpa [Polynomial.coe_aeval_eq_eval] using this

theorem W7b_MetodosNumericos_Ppoly_eval {n : ℕ} (xs fs : Fin (n + 1) → ℝ) (t : ℝ) :
    (W7b_MetodosNumericos_Ppoly xs fs).eval t = lagrangeInterp xs fs t := by
  unfold W7b_MetodosNumericos_Ppoly lagrangeInterp lagrangeBasis
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  rw [div_eq_inv_mul]

theorem W7b_MetodosNumericos_Ppoly_natDegree {n : ℕ} (xs fs : Fin (n + 1) → ℝ) :
    (W7b_MetodosNumericos_Ppoly xs fs).natDegree ≤ n := by
  unfold W7b_MetodosNumericos_Ppoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  have : ∀ j ∈ Finset.univ.erase i,
      (Polynomial.C (xs i - xs j)⁻¹ * (Polynomial.X - Polynomial.C (xs j))).natDegree ≤ 1 :=
    fun j _ => (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_sub_C_le _)
  refine (Finset.sum_le_card_nsmul _ _ 1 this).trans ?_
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  simp

theorem W7b_MetodosNumericos_interp_node {n : ℕ} (xs fs : Fin (n + 1) → ℝ)
    (hxs : Function.Injective xs) (i : Fin (n + 1)) :
    lagrangeInterp xs fs (xs i) = fs i := by
  unfold lagrangeInterp lagrangeBasis
  rw [Finset.sum_eq_single i]
  · rw [Finset.prod_eq_one, mul_one]
    intro j hj
    have hne : xs i - xs j ≠ 0 := sub_ne_zero.mpr (hxs.ne (Finset.ne_of_mem_erase hj).symm)
    exact div_self hne
  · intro j _ hji
    rw [Finset.prod_eq_zero (i := i) (Finset.mem_erase.mpr ⟨hji.symm, Finset.mem_univ _⟩)]
    · ring
    · simp
  · intro h; exact absurd (Finset.mem_univ i) h

theorem solution {n : ℕ} (f : ℝ → ℝ) (a b : ℝ) (xs : Fin (n + 1) → ℝ)
    (hxs : StrictMono xs) (hmem : ∀ i, xs i ∈ Set.Ioo a b)
    (hf : ContDiffOn ℝ (n + 1 : ℕ) f (Set.Ioo a b))
    (x : ℝ) (hx : x ∈ Set.Ioo a b) (hne : ∀ i, x ≠ xs i) :
    ∃ xi ∈ Set.Ioo a b,
      f x = lagrangeInterp xs (fun i => f (xs i)) x +
        (∏ k : Fin (n + 1), (x - xs k)) *
          (iteratedDerivWithin (n + 1) f (Set.Ioo a b) xi / (Nat.factorial (n + 1) : ℝ)) := by
  set s := Set.Ioo a b with hs
  set P := W7b_MetodosNumericos_Ppoly xs (fun i => f (xs i)) with hP
  set w : Polynomial ℝ := ∏ k : Fin (n + 1), (Polynomial.X - Polynomial.C (xs k)) with hw
  have hweval : ∀ t, w.eval t = ∏ k : Fin (n + 1), (t - xs k) := by
    intro t; rw [hw, Polynomial.eval_prod]; simp
  have hwx : w.eval x ≠ 0 := by
    rw [hweval, Finset.prod_ne_zero_iff]
    intro k _; exact sub_ne_zero.mpr (hne k)
  set c := (f x - P.eval x) / w.eval x with hc
  set Q := P + Polynomial.C c * w with hQ
  set F := fun t => f t - Q.eval t with hF
  -- iterated derivatives of the polynomials
  have hwmonic : w.Monic := Polynomial.monic_prod_of_monic _ _ (fun k _ => Polynomial.monic_X_sub_C _)
  have hwdeg : w.natDegree = n + 1 := by
    rw [hw, Polynomial.natDegree_prod_of_monic _ _ (fun k _ => Polynomial.monic_X_sub_C _)]
    simp
  have hPd : Polynomial.derivative^[n + 1] P = 0 :=
    Polynomial.iterate_derivative_eq_zero
      (lt_of_le_of_lt (W7b_MetodosNumericos_Ppoly_natDegree _ _) (Nat.lt_succ_self n))
  have hwd : Polynomial.derivative^[n + 1] w = Polynomial.C ((Nat.factorial (n + 1) : ℝ)) := by
    have hdeg : (Polynomial.derivative^[n + 1] w).natDegree ≤ 0 := by
      have := Polynomial.natDegree_iterate_derivative w (n + 1)
      rw [hwdeg, Nat.sub_self] at this; exact this
    rw [Polynomial.eq_C_of_natDegree_le_zero hdeg, Polynomial.coeff_iterate_derivative, zero_add,
      Nat.descFactorial_self]
    congr 1
    have : w.coeff (n + 1) = 1 := by
      rw [← hwdeg]; exact hwmonic.coeff_natDegree
    rw [this, nsmul_eq_mul, mul_one]
  have hQd : Polynomial.derivative^[n + 1] Q =
      Polynomial.C (c * (Nat.factorial (n + 1) : ℝ)) := by
    rw [hQ, W7b_MetodosNumericos_iterate_derivative_add, hPd, Polynomial.iterate_derivative_C_mul,
      hwd, zero_add, ← Polynomial.C_mul]
  -- zeros of F
  have hFnode : ∀ i, F (xs i) = 0 := by
    intro i
    simp only [hF, hQ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hP,
      W7b_MetodosNumericos_Ppoly_eval, W7b_MetodosNumericos_interp_node xs _ hxs.injective]
    have : w.eval (xs i) = 0 := by
      rw [hweval, Finset.prod_eq_zero (Finset.mem_univ i)]; ring
    rw [this]; ring
  have hFx : F x = 0 := by
    simp only [hF, hQ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    rw [hc]; field_simp; ring
  set S : Finset ℝ := insert x (Finset.univ.image xs) with hSdef
  have hxS : x ∉ Finset.univ.image xs := by
    intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    exact hne i hi.symm
  have hScard : S.card = (n + 1) + 1 := by
    rw [hSdef, Finset.card_insert_of_notMem hxS, Finset.card_image_of_injective _ hxs.injective,
      Finset.card_univ, Fintype.card_fin]
  have hSs : ∀ z ∈ S, z ∈ s := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz; exact hmem i
  have hSz : ∀ z ∈ S, F z = 0 := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hFx
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz; exact hFnode i
  have hFcd : ContDiffOn ℝ ((n + 1 : ℕ)) F s := hf.sub (W7b_MetodosNumericos_polyCD Q _).contDiffOn
  obtain ⟨xi, hxi, hxi0⟩ :=
    W7b_MetodosNumericos_gen_rolle a b (n + 1) F hFcd S hScard hSs hSz
  refine ⟨xi, hxi, ?_⟩
  have hu : UniqueDiffOn ℝ s := uniqueDiffOn_Ioo a b
  have hsplit : iteratedDerivWithin (n + 1) F s xi =
      iteratedDerivWithin (n + 1) f s xi - c * (Nat.factorial (n + 1) : ℝ) := by
    have h1 := iteratedDerivWithin_sub hxi hu (hf.contDiffWithinAt hxi)
      ((W7b_MetodosNumericos_polyCD Q _).contDiffOn.contDiffWithinAt hxi)
    have h1' : iteratedDerivWithin (n + 1) F s xi =
        iteratedDerivWithin (n + 1) f s xi -
          iteratedDerivWithin (n + 1) (fun t => Q.eval t) s xi := h1
    have hq : iteratedDerivWithin (n + 1) (fun t => Q.eval t) s xi =
        c * (Nat.factorial (n + 1) : ℝ) := by
      rw [iteratedDerivWithin_of_isOpen (f := fun t => Q.eval t) isOpen_Ioo hxi,
        W7b_MetodosNumericos_iteratedDeriv_poly, hQd]
      simp
    rw [h1', hq]
  rw [hsplit, sub_eq_zero] at hxi0
  have hfac : (Nat.factorial (n + 1) : ℝ) ≠ 0 := by positivity
  rw [hxi0, ← hweval x, mul_div_assoc, div_self hfac, mul_one]
  have : c * w.eval x = f x - P.eval x := by
    rw [hc]; field_simp
  rw [hP, W7b_MetodosNumericos_Ppoly_eval] at this
  linarith [mul_comm c (w.eval x)]

theorem W7b_MetodosNumericos_lagrange_error_bound {n : ℕ} (f : ℝ → ℝ) (a b M : ℝ) (xs : Fin (n + 1) → ℝ)
    (hxs : StrictMono xs) (hmem : ∀ i, xs i ∈ Set.Ioo a b)
    (hf : ContDiffOn ℝ (n + 1 : ℕ) f (Set.Ioo a b))
    (hM : ∀ y ∈ Set.Ioo a b, |iteratedDerivWithin (n + 1) f (Set.Ioo a b) y| ≤ M)
    (x : ℝ) (hx : x ∈ Set.Ioo a b) (hne : ∀ i, x ≠ xs i) :
    |f x - lagrangeInterp xs (fun i => f (xs i)) x| ≤
      M / (Nat.factorial (n + 1) : ℝ) * ∏ k : Fin (n + 1), |x - xs k| := by
  obtain ⟨xi, hxi, heq⟩ :=
    solution f a b xs hxs hmem hf x hx hne
  rw [heq, add_sub_cancel_left, abs_mul, Finset.abs_prod, abs_div]
  have hfac : (0 : ℝ) < (Nat.factorial (n + 1) : ℝ) := by positivity
  rw [abs_of_pos hfac]
  have hp : 0 ≤ ∏ k : Fin (n + 1), |x - xs k| := Finset.prod_nonneg (fun k _ => abs_nonneg _)
  calc (∏ k : Fin (n + 1), |x - xs k|) * (|iteratedDerivWithin (n + 1) f (Set.Ioo a b) xi| /
        (Nat.factorial (n + 1) : ℝ))
      ≤ (∏ k : Fin (n + 1), |x - xs k|) * (M / (Nat.factorial (n + 1) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hp
        exact div_le_div_of_nonneg_right (hM xi hxi) hfac.le
    _ = M / (Nat.factorial (n + 1) : ℝ) * ∏ k : Fin (n + 1), |x - xs k| := by ring

/-! ## Convergence of Picard iterates -/

theorem W7b_MetodosNumericos_int_bound (F : ℝ → ℝ) (x0 x C : ℝ) (m : ℕ) (hC : 0 ≤ C)
    (hF : ContinuousOn F (Set.uIcc x0 x)) (hb : ∀ t ∈ Set.uIcc x0 x, |F t| ≤ C * |t - x0| ^ m) :
    |∫ t in x0..x, F t| ≤ C * |x - x0| ^ (m + 1) / (m + 1) := by
  rcases le_total x0 x with hle | hle
  · rw [Set.uIcc_of_le hle] at hF hb
    calc |∫ t in x0..x, F t| ≤ ∫ t in x0..x, |F t| :=
          intervalIntegral.abs_integral_le_integral_abs hle
      _ ≤ ∫ t in x0..x, C * (t - x0) ^ m := by
          apply intervalIntegral.integral_mono_on hle (hF.abs.intervalIntegrable_of_Icc hle)
            (by apply Continuous.intervalIntegrable; fun_prop)
          intro t ht
          have := hb t ht
          rwa [abs_of_nonneg (sub_nonneg.2 ht.1)] at this
      _ = C * (x - x0) ^ (m + 1) / (m + 1) := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_comp_sub_right (fun t => t ^ m), integral_pow]
          simp; ring
      _ = C * |x - x0| ^ (m + 1) / (m + 1) := by rw [abs_of_nonneg (sub_nonneg.2 hle)]
  · rw [Set.uIcc_comm, Set.uIcc_of_le hle] at hF hb
    rw [intervalIntegral.integral_symm, abs_neg]
    calc |∫ t in x..x0, F t| ≤ ∫ t in x..x0, |F t| :=
          intervalIntegral.abs_integral_le_integral_abs hle
      _ ≤ ∫ t in x..x0, C * (x0 - t) ^ m := by
          apply intervalIntegral.integral_mono_on hle (hF.abs.intervalIntegrable_of_Icc hle)
            (by apply Continuous.intervalIntegrable; fun_prop)
          intro t ht
          have := hb t ht
          rwa [abs_of_nonpos (sub_nonpos.2 ht.2), neg_sub] at this
      _ = C * (x0 - x) ^ (m + 1) / (m + 1) := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_comp_sub_left (fun t => t ^ m), integral_pow]
          simp; ring
      _ = C * |x - x0| ^ (m + 1) / (m + 1) := by
          rw [abs_of_nonpos (sub_nonpos.2 hle), neg_sub]

theorem W7b_MetodosNumericos_picard_converges (f : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (x0 y0 a b M N h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hM : 0 < M) (hN : 0 ≤ N) (hh : h = min a (b / M))
    (hbound : ∀ x ∈ Set.Icc (x0 - a) (x0 + a), ∀ y ∈ Set.Icc (y0 - b) (y0 + b), |f x y| ≤ M)
    (hlip : ∀ x ∈ Set.Icc (x0 - a) (x0 + a), ∀ u ∈ Set.Icc (y0 - b) (y0 + b),
      ∀ v ∈ Set.Icc (y0 - b) (y0 + b), |f x u - f x v| ≤ N * |u - v|)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Set.Icc (x0 - a) (x0 + a) ×ˢ Set.Icc (y0 - b) (y0 + b)))
    (hphi0 : phi x0 = y0)
    (hsol : ∀ x ∈ Set.Icc (x0 - h) (x0 + h), HasDerivAt phi (f x (phi x)) x)
    (hrange : ∀ x ∈ Set.Icc (x0 - h) (x0 + h), phi x ∈ Set.Icc (y0 - b) (y0 + b))
    (x : ℝ) (hx : x ∈ Set.Icc (x0 - h) (x0 + h)) :
    Filter.Tendsto (fun k => picardSeq f x0 y0 k x) Filter.atTop (nhds (phi x)) := by
  set I := Set.Icc (x0 - h) (x0 + h) with hI
  have hha : h ≤ a := by rw [hh]; exact min_le_left _ _
  have hhb : M * h ≤ b := by
    have := min_le_right a (b / M)
    rw [← hh] at this
    calc M * h ≤ M * (b / M) := mul_le_mul_of_nonneg_left this hM.le
      _ = b := by field_simp
  have hh0 : 0 < h := by rw [hh]; exact lt_min ha (div_pos hb hM)
  have hIa : ∀ t ∈ I, t ∈ Set.Icc (x0 - a) (x0 + a) :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hx0I : x0 ∈ I := ⟨by linarith, by linarith⟩
  have hsubI : ∀ t, t ∈ I → Set.uIcc x0 t ⊆ I := fun t ht =>
    Set.uIcc_subset_Icc hx0I ht
  -- composition continuity
  have hcomp : ∀ g : ℝ → ℝ, ContinuousOn g I → (∀ t ∈ I, g t ∈ Set.Icc (y0 - b) (y0 + b)) →
      ContinuousOn (fun t => f t (g t)) I := by
    intro g hg hgr
    have : ContinuousOn (fun t => ((t, g t) : ℝ × ℝ)) I :=
      continuousOn_id.prodMk hg
    exact hcont.comp this (fun t ht => ⟨hIa t ht, hgr t ht⟩)
  have hMt : ∀ t ∈ I, M * |t - x0| ≤ b := by
    intro t ht
    have : |t - x0| ≤ h := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    nlinarith
  -- iterates are continuous and stay in the box
  have hP : ∀ k, ContinuousOn (picardSeq f x0 y0 k) I ∧
      ∀ t ∈ I, |picardSeq f x0 y0 k t - y0| ≤ M * |t - x0| := by
    intro k
    induction k with
    | zero =>
      refine ⟨continuousOn_const, fun t _ => ?_⟩
      simp [picardSeq]; positivity
    | succ k ih =>
      obtain ⟨hc, hbd⟩ := ih
      have hr : ∀ t ∈ I, picardSeq f x0 y0 k t ∈ Set.Icc (y0 - b) (y0 + b) := by
        intro t ht
        have := (hbd t ht).trans (hMt t ht)
        rw [abs_le] at this
        exact ⟨by linarith [this.1], by linarith [this.2]⟩
      have hg := hcomp _ hc hr
      refine ⟨?_, ?_⟩
      · have hii : IntervalIntegrable (fun t => f t (picardSeq f x0 y0 k t)) MeasureTheory.volume
            (x0 - h) (x0 + h) := by
          apply ContinuousOn.intervalIntegrable
          rw [Set.uIcc_of_le (by linarith)]; exact hg
        have := intervalIntegral.continuousOn_primitive_interval' hii
          (by rw [Set.uIcc_of_le (by linarith)]; exact hx0I)
        rw [Set.uIcc_of_le (by linarith)] at this
        exact continuousOn_const.add this
      · intro t ht
        show |y0 + (∫ s in x0..t, f s (picardSeq f x0 y0 k s)) - y0| ≤ M * |t - x0|
        rw [add_sub_cancel_left]
        have := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := x0) (b := t) (f := fun s => f s (picardSeq f x0 y0 k s)) (C := M) (fun s hs => by
            have hsI : s ∈ I := hsubI t ht (Set.uIoc_subset_uIcc hs)
            exact hbound s (hIa s hsI) _ (hr s hsI))
        simpa [Real.norm_eq_abs] using this
  -- integral equation for `phi`
  have hphic : ContinuousOn phi I := fun t ht => (hsol t ht).continuousAt.continuousWithinAt
  have hgphi := hcomp phi hphic hrange
  have hphieq : ∀ t ∈ I, phi t = y0 + ∫ s in x0..t, f s (phi s) := by
    intro t ht
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hsol s (hsubI t ht hs))
      ((hgphi.mono (hsubI t ht)).intervalIntegrable), hphi0]
    ring
  -- error estimate
  have hE : ∀ k, ∀ t ∈ I, |phi t - picardSeq f x0 y0 k t| ≤
      M * N ^ k * |t - x0| ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by
    intro k
    induction k with
    | zero =>
      intro t ht
      simp only [picardSeq, pow_zero, mul_one, zero_add, pow_one, Nat.factorial_one, Nat.cast_one,
        div_one]
      rw [hphieq t ht, add_sub_cancel_left]
      have := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := x0) (b := t) (f := fun s => f s (phi s)) (C := M) (fun s hs => by
            have hsI : s ∈ I := hsubI t ht (Set.uIoc_subset_uIcc hs)
            exact hbound s (hIa s hsI) _ (hrange s hsI))
      simpa [Real.norm_eq_abs] using this
    | succ k ih =>
      intro t ht
      obtain ⟨hc, hbd⟩ := hP k
      have hr : ∀ s ∈ I, picardSeq f x0 y0 k s ∈ Set.Icc (y0 - b) (y0 + b) := by
        intro s hs
        have := (hbd s hs).trans (hMt s hs)
        rw [abs_le] at this
        exact ⟨by linarith [this.1], by linarith [this.2]⟩
      have hg := hcomp _ hc hr
      have hdiff : phi t - picardSeq f x0 y0 (k + 1) t =
          ∫ s in x0..t, (f s (phi s) - f s (picardSeq f x0 y0 k s)) := by
        rw [intervalIntegral.integral_sub ((hgphi.mono (hsubI t ht)).intervalIntegrable)
          ((hg.mono (hsubI t ht)).intervalIntegrable), hphieq t ht]
        show y0 + (∫ s in x0..t, f s (phi s)) - (y0 + ∫ s in x0..t, f s (picardSeq f x0 y0 k s)) = _
        ring
      rw [hdiff]
      have hC : 0 ≤ N * (M * N ^ k / (Nat.factorial (k + 1) : ℝ)) := by positivity
      have := W7b_MetodosNumericos_int_bound
        (fun s => f s (phi s) - f s (picardSeq f x0 y0 k s)) x0 t
        (N * (M * N ^ k / (Nat.factorial (k + 1) : ℝ))) (k + 1) hC
        ((hgphi.sub hg).mono (hsubI t ht)) (by
          intro s hs
          have hsI := hsubI t ht hs
          refine (hlip s (hIa s hsI) _ (hrange s hsI) _ (hr s hsI)).trans ?_
          have := ih s hsI
          calc N * |phi s - picardSeq f x0 y0 k s|
              ≤ N * (M * N ^ k * |s - x0| ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) :=
                mul_le_mul_of_nonneg_left this hN
            _ = N * (M * N ^ k / (Nat.factorial (k + 1) : ℝ)) * |s - x0| ^ (k + 1) := by ring)
      refine this.trans (le_of_eq ?_)
      rw [Nat.factorial_succ (k + 1)]
      push_cast
      field_simp
      ring
  -- conclude
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set c := N * |x - x0| with hc
  have hlim := (FloorSemiring.tendsto_pow_div_factorial_atTop c).const_mul (M * |x - x0|)
  rw [mul_zero] at hlim
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hlim
  rw [Real.norm_eq_abs, abs_sub_comm]
  refine (hE k x hx).trans ?_
  have hf1 : (Nat.factorial k : ℝ) ≤ Nat.factorial (k + 1) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ k)
  have hfk : (0 : ℝ) < Nat.factorial k := by exact_mod_cast Nat.factorial_pos k
  have hnum : 0 ≤ M * N ^ k * |x - x0| ^ (k + 1) := by positivity
  calc M * N ^ k * |x - x0| ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)
      ≤ M * N ^ k * |x - x0| ^ (k + 1) / (Nat.factorial k : ℝ) :=
        div_le_div_of_nonneg_left hnum hfk hf1
    _ = M * |x - x0| * (c ^ k / (Nat.factorial k : ℝ)) := by rw [hc, mul_pow]; ring

/-! ## Simpson's rule error -/

theorem W7b_MetodosNumericos_simpson_simple_error (f : ℝ → ℝ) (x0 h : ℝ) (hh : 0 < h)
    (hf : ContDiffOn ℝ 4 f (Set.Icc (x0 - h) (x0 + h))) :
    ∃ mu ∈ Set.Ioo (x0 - h) (x0 + h),
      ∫ t in (x0 - h)..(x0 + h), f t =
        h / 3 * (f (x0 - h) + 4 * f x0 + f (x0 + h))
          - h ^ 5 * iteratedDerivWithin 4 f (Set.Icc (x0 - h) (x0 + h)) mu / 90 := by
  have hh0 : h ≠ 0 := hh.ne'
  set I := Set.Icc (x0 - h) (x0 + h) with hI
  set J := Set.Ioo (x0 - h) (x0 + h) with hJdef
  have hJo : IsOpen J := isOpen_Ioo
  have hJ : ContDiffOn ℝ 4 f J := hf.mono Set.Ioo_subset_Icc_self
  set D1 := deriv f
  set D2 := deriv D1
  set D3 := deriv D2
  set D4 := deriv D3
  have c1 : ContDiffOn ℝ 3 D1 J := hJ.deriv_of_isOpen hJo (by norm_num)
  have c2 : ContDiffOn ℝ 2 D2 J := c1.deriv_of_isOpen hJo (by norm_num)
  have c3 : ContDiffOn ℝ 1 D3 J := c2.deriv_of_isOpen hJo (by norm_num)
  have hd0 : ∀ y ∈ J, HasDerivAt f (D1 y) y := fun y hy =>
    ((hJ.differentiableOn (by norm_num)) y hy).differentiableAt (hJo.mem_nhds hy) |>.hasDerivAt
  have hd1 : ∀ y ∈ J, HasDerivAt D1 (D2 y) y := fun y hy =>
    ((c1.differentiableOn (by norm_num)) y hy).differentiableAt (hJo.mem_nhds hy) |>.hasDerivAt
  have hd2 : ∀ y ∈ J, HasDerivAt D2 (D3 y) y := fun y hy =>
    ((c2.differentiableOn (by norm_num)) y hy).differentiableAt (hJo.mem_nhds hy) |>.hasDerivAt
  have hd3 : ∀ y ∈ J, HasDerivAt D3 (D4 y) y := fun y hy =>
    ((c3.differentiableOn (by norm_num)) y hy).differentiableAt (hJo.mem_nhds hy) |>.hasDerivAt
  have hfc : ContinuousOn f I := hf.continuousOn
  have hx0 : x0 ∈ I := ⟨by linarith, by linarith⟩
  have hmemJ : ∀ t, |t| < h → x0 + t ∈ J ∧ x0 - t ∈ J := by
    intro t ht
    rw [abs_lt] at ht
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  -- the primitive
  set P : ℝ → ℝ := fun u => ∫ x in x0..u, f x with hP
  have hPd : ∀ u ∈ J, HasDerivAt P (f u) u := by
    intro u hu
    apply intervalIntegral.integral_hasDerivAt_right
    · apply ContinuousOn.intervalIntegrable
      exact hfc.mono (Set.uIcc_subset_Icc hx0 (Set.Ioo_subset_Icc_self hu))
    · exact (hfc.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter hJo u hu
    · exact (hd0 u hu).continuousAt
  have hPc : ContinuousOn P I := by
    have := intervalIntegral.continuousOn_primitive_interval' (a := x0) (μ := MeasureTheory.volume)
      (hfc.intervalIntegrable_of_Icc (by linarith)) (by rw [Set.uIcc_of_le (by linarith)]; exact hx0)
    rwa [Set.uIcc_of_le (by linarith)] at this
  -- F and its derivatives
  set F : ℝ → ℝ := fun t => P (x0 + t) - P (x0 - t) - t / 3 * (f (x0 - t) + 4 * f x0 + f (x0 + t))
    with hF
  set F1 : ℝ → ℝ := fun t => 2 / 3 * (f (x0 + t) + f (x0 - t)) - 4 / 3 * f x0
    - t / 3 * (D1 (x0 + t) - D1 (x0 - t)) with hF1
  set F2 : ℝ → ℝ := fun t => 1 / 3 * (D1 (x0 + t) - D1 (x0 - t))
    - t / 3 * (D2 (x0 + t) + D2 (x0 - t)) with hF2
  set F3 : ℝ → ℝ := fun t => -(t / 3) * (D3 (x0 + t) - D3 (x0 - t)) with hF3
  have hplus : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x0 + t) 1 t := fun t =>
    (hasDerivAt_id' t).const_add x0
  have hminus : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x0 - t) (-1) t := fun t =>
    (hasDerivAt_id' t).const_sub x0
  have hFd : ∀ t, |t| < h → HasDerivAt F (F1 t) t := by
    intro t ht
    obtain ⟨hp, hm⟩ := hmemJ t ht
    have a1 := (hPd _ hp).comp t (hplus t)
    have a2 := (hPd _ hm).comp t (hminus t)
    have a3 := (hd0 _ hm).comp t (hminus t)
    have a4 := (hd0 _ hp).comp t (hplus t)
    have a5 := ((hasDerivAt_id' t).div_const 3).mul ((a3.add_const (4 * f x0)).add a4)
    have := (a1.sub a2).sub a5
    refine this.congr_deriv ?_
    simp only [hF1, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply,
      Function.comp_apply]
    ring
  have hF1d : ∀ t, |t| < h → HasDerivAt F1 (F2 t) t := by
    intro t ht
    obtain ⟨hp, hm⟩ := hmemJ t ht
    have a1 := (hd0 _ hp).comp t (hplus t)
    have a2 := (hd0 _ hm).comp t (hminus t)
    have a3 := (hd1 _ hp).comp t (hplus t)
    have a4 := (hd1 _ hm).comp t (hminus t)
    have := (((a1.add a2).const_mul (2 / 3)).sub_const (4 / 3 * f x0)).sub
      (((hasDerivAt_id' t).div_const 3).mul (a3.sub a4))
    refine this.congr_deriv ?_
    simp only [hF2, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply,
      Function.comp_apply]
    ring
  have hF2d : ∀ t, |t| < h → HasDerivAt F2 (F3 t) t := by
    intro t ht
    obtain ⟨hp, hm⟩ := hmemJ t ht
    have a1 := (hd1 _ hp).comp t (hplus t)
    have a2 := (hd1 _ hm).comp t (hminus t)
    have a3 := (hd2 _ hp).comp t (hplus t)
    have a4 := (hd2 _ hm).comp t (hminus t)
    have := ((a1.sub a2).const_mul (1 / 3)).sub
      (((hasDerivAt_id' t).div_const 3).mul (a3.add a4))
    refine this.congr_deriv ?_
    simp only [hF3, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply,
      Function.comp_apply]
    ring
  -- G and Rolle three times
  set C := F h with hC
  set G : ℝ → ℝ := fun t => F t - t ^ 5 * (C / h ^ 5) with hG
  set G1 : ℝ → ℝ := fun t => F1 t - 5 * t ^ 4 * (C / h ^ 5) with hG1
  set G2 : ℝ → ℝ := fun t => F2 t - 20 * t ^ 3 * (C / h ^ 5) with hG2
  set G3 : ℝ → ℝ := fun t => F3 t - 60 * t ^ 2 * (C / h ^ 5) with hG3
  have hGd : ∀ t, |t| < h → HasDerivAt G (G1 t) t := by
    intro t ht
    have := (hFd t ht).sub ((hasDerivAt_pow 5 t).mul_const (C / h ^ 5))
    refine this.congr_deriv ?_
    simp only [hG1, show (5 : ℕ) - 1 = 4 from rfl]; push_cast; ring
  have hG1d : ∀ t, |t| < h → HasDerivAt G1 (G2 t) t := by
    intro t ht
    have := (hF1d t ht).sub (((hasDerivAt_pow 4 t).const_mul 5).mul_const (C / h ^ 5))
    refine this.congr_deriv ?_
    simp only [hG2, show (4 : ℕ) - 1 = 3 from rfl]; push_cast; ring
  have hG2d : ∀ t, |t| < h → HasDerivAt G2 (G3 t) t := by
    intro t ht
    have := (hF2d t ht).sub (((hasDerivAt_pow 3 t).const_mul 20).mul_const (C / h ^ 5))
    refine this.congr_deriv ?_
    simp only [hG3, show (3 : ℕ) - 1 = 2 from rfl]; push_cast; ring
  have habs : ∀ t, 0 ≤ t → t < h → |t| < h := fun t h0 h1 => by rw [abs_of_nonneg h0]; exact h1
  -- continuity of G on [0, h]
  have hGc : ContinuousOn G (Set.Icc 0 h) := by
    have hmap1 : Set.MapsTo (fun t : ℝ => x0 + t) (Set.Icc 0 h) I :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hmap2 : Set.MapsTo (fun t : ℝ => x0 - t) (Set.Icc 0 h) I :=
      fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have k1 : ContinuousOn (fun t => P (x0 + t)) (Set.Icc 0 h) :=
      hPc.comp (by fun_prop) hmap1
    have k2 : ContinuousOn (fun t => P (x0 - t)) (Set.Icc 0 h) :=
      hPc.comp (by fun_prop) hmap2
    have k3 : ContinuousOn (fun t => f (x0 + t)) (Set.Icc 0 h) :=
      hfc.comp (by fun_prop) hmap1
    have k4 : ContinuousOn (fun t => f (x0 - t)) (Set.Icc 0 h) :=
      hfc.comp (by fun_prop) hmap2
    exact ((k1.sub k2).sub ((continuousOn_id.div_const 3).mul ((k4.add continuousOn_const).add k3))).sub
      ((continuousOn_id.pow 5).mul continuousOn_const)
  have hG0 : G 0 = 0 := by simp [hG, hF, hP]
  have hGh : G h = 0 := by simp only [hG, hC]; field_simp; ring
  obtain ⟨t1, ht1, hG1t1⟩ := exists_hasDerivAt_eq_zero hh hGc (by rw [hG0, hGh])
    (fun t ht => hGd t (habs t ht.1.le ht.2))
  have hG10 : G1 0 = 0 := by simp [hG1, hF1]; ring
  obtain ⟨t2, ht2, hG2t2⟩ := exists_hasDerivAt_eq_zero ht1.1
    (fun t ht => (hG1d t (habs t ht.1 (lt_of_le_of_lt ht.2 ht1.2))).continuousAt.continuousWithinAt)
    (by rw [hG10, hG1t1]) (fun t ht => hG1d t (habs t ht.1.le (lt_trans ht.2 ht1.2)))
  have hG20 : G2 0 = 0 := by simp [hG2, hF2]
  obtain ⟨t3, ht3, hG3t3⟩ := exists_hasDerivAt_eq_zero ht2.1
    (fun t ht => (hG2d t (habs t ht.1 (by linarith [ht.2, ht2.2, ht1.2]))).continuousAt.continuousWithinAt)
    (by rw [hG20, hG2t2]) (fun t ht => hG2d t (habs t ht.1.le (by linarith [ht.2, ht2.2, ht1.2])))
  have t3pos : 0 < t3 := ht3.1
  have t3h : t3 < h := by linarith [ht3.2, ht2.2, ht1.2]
  have hcont3 : ContinuousOn D3 (Set.Icc (x0 - t3) (x0 + t3)) := fun y hy =>
    (hd3 y ⟨by linarith [hy.1], by linarith [hy.2]⟩).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope D3 D4 (by linarith : x0 - t3 < x0 + t3) hcont3
    (fun y hy => hd3 y ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  have hξJ : ξ ∈ J := ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
  refine ⟨ξ, hξJ, ?_⟩
  have hiter : iteratedDerivWithin 4 f I ξ = D4 ξ := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith))
      (hJ.contDiffAt (hJo.mem_nhds hξJ)) (Set.Ioo_subset_Icc_self hξJ), iteratedDeriv_eq_iterate]
    rfl
  rw [hiter]
  have hG3' : F3 t3 = 60 * t3 ^ 2 * (C / h ^ 5) := by
    have := hG3t3; simp only [hG3] at this; linarith
  have hdiff : D3 (x0 + t3) - D3 (x0 - t3) = 2 * t3 * D4 ξ := by
    have ht3ne : t3 ≠ 0 := t3pos.ne'
    rw [hξeq, show x0 + t3 - (x0 - t3) = 2 * t3 by ring]; field_simp
  simp only [hF3] at hG3'
  rw [hdiff] at hG3'
  have hCval : C = -(h ^ 5 * D4 ξ / 90) := by
    have ht0 : t3 ^ 2 ≠ 0 := by positivity
    have key : t3 ^ 2 * (C / h ^ 5 + D4 ξ / 90) = 0 := by
      linear_combination (-1 / 60 : ℝ) * hG3'
    have h5 : C / h ^ 5 + D4 ξ / 90 = 0 := (mul_eq_zero.mp key).resolve_left ht0
    have h6 : C = h ^ 5 * (C / h ^ 5) := by field_simp
    rw [h6]
    have h7 : C / h ^ 5 = -(D4 ξ / 90) := by linarith
    rw [h7]; ring
  have hint : ∫ t in (x0 - h)..(x0 + h), f t = P (x0 + h) - P (x0 - h) := by
    rw [hP]
    simp only
    rw [intervalIntegral.integral_interval_sub_left
      (hfc.mono (Set.uIcc_subset_Icc hx0 (show x0 + h ∈ I from ⟨by linarith, by linarith⟩))).intervalIntegrable
      (hfc.mono (Set.uIcc_subset_Icc hx0 (show x0 - h ∈ I from ⟨by linarith, by linarith⟩))).intervalIntegrable]
  have hCdef : C = P (x0 + h) - P (x0 - h) - h / 3 * (f (x0 - h) + 4 * f x0 + f (x0 + h)) := rfl
  rw [hint]
  linarith [hCval, hCdef]

theorem W7b_MetodosNumericos_simpson_composite_error (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) (hab : a < b) (hk : 0 < k)
    (hf : ContDiffOn ℝ 4 f (Set.Icc a b)) :
    ∃ mu ∈ Set.Ioo a b,
      ∫ t in a..b, f t =
        simpsonRule f a b k
          - (b - a) ^ 5 * iteratedDerivWithin 4 f (Set.Icc a b) mu / (180 * (2 * k : ℝ) ^ 4) := by
  set H := (b - a) / (2 * k) with hH
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hH0 : 0 < H := div_pos (by linarith) (by positivity)
  set x : ℕ → ℝ := fun i => a + i * H with hx
  have hxk : x (2 * k) = b := by
    simp only [hx, hH]; push_cast; field_simp; ring
  have hx0 : x 0 = a := by simp [hx]
  set g := iteratedDerivWithin 4 f (Set.Icc a b) with hg
  -- the Simpson error on each panel
  have panel : ∀ j : Fin k, ∃ μ ∈ Set.Ioo (x (2 * j)) (x (2 * j + 2)),
      ∫ t in x (2 * j)..x (2 * j + 2), f t =
        H / 3 * (f (x (2 * j)) + 4 * f (x (2 * j + 1)) + f (x (2 * j + 2))) - H ^ 5 * g μ / 90 := by
    intro j
    have hj : (j : ℝ) + 1 ≤ k := by exact_mod_cast j.2
    set c := x (2 * j + 1) with hc
    have hc1 : c - H = x (2 * j) := by simp only [hc, hx]; push_cast; ring
    have hc2 : c + H = x (2 * j + 2) := by simp only [hc, hx]; push_cast; ring
    have hlo : a ≤ c - H := by
      rw [hc1]; simp only [hx]; have : (0 : ℝ) ≤ ((2 * (j : ℕ) : ℕ) : ℝ) * H := by positivity
      linarith
    have hhi : c + H ≤ b := by
      rw [hc2, ← hxk]; simp only [hx]; push_cast
      have : (2 * (j : ℝ) + 2) * H ≤ 2 * k * H := by nlinarith
      linarith
    have hsub : Set.Icc (c - H) (c + H) ⊆ Set.Icc a b := Set.Icc_subset_Icc hlo hhi
    obtain ⟨μ, hμ, heq⟩ := W7b_MetodosNumericos_simpson_simple_error f c H hH0 (hf.mono hsub)
    refine ⟨μ, by rw [← hc1, ← hc2]; exact hμ, ?_⟩
    rw [← hc1, ← hc2, heq]
    have hμab : μ ∈ Set.Ioo a b := ⟨by linarith [hμ.1], by linarith [hμ.2]⟩
    have hca : ContDiffAt ℝ 4 f μ := hf.contDiffAt (Icc_mem_nhds hμab.1 hμab.2)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith)) hca
        (Set.Ioo_subset_Icc_self hμ),
      hg, iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hca
        (Set.Ioo_subset_Icc_self hμab)]
  choose μ hμ hpanel using panel
  have hμab : ∀ j, μ j ∈ Set.Ioo a b := by
    intro j
    have hj : (j : ℝ) + 1 ≤ k := by exact_mod_cast j.2
    have h1 := (hμ j).1
    have h2 := (hμ j).2
    simp only [hx] at h1 h2
    push_cast at h1 h2
    constructor
    · have : (0 : ℝ) ≤ 2 * (j : ℝ) * H := by positivity
      linarith
    · have : (2 * (j : ℝ) + 2) * H ≤ 2 * k * H := by nlinarith
      have hb : a + 2 * k * H = b := by rw [hH]; field_simp; ring
      linarith
  -- sum of panel integrals
  have hcont : ContinuousOn f (Set.Icc a b) := hf.continuousOn
  have hsum_int : ∑ j ∈ Finset.range k, ∫ t in x (2 * j)..x (2 * j + 2), f t = ∫ t in a..b, f t := by
    have := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := MeasureTheory.volume)
      (a := fun j => x (2 * j)) (n := k) (fun j hj => by
        apply ContinuousOn.intervalIntegrable
        apply hcont.mono
        apply Set.uIcc_subset_Icc
        · simp only [hx]; constructor
          · have : (0 : ℝ) ≤ ((2 * j : ℕ) : ℝ) * H := by positivity
            linarith
          · rw [← hxk]; simp only [hx]; push_cast
            have : (2 * (j : ℝ)) * H ≤ 2 * k * H := by
              have : (j : ℝ) ≤ k := by exact_mod_cast hj.le
              nlinarith
            linarith
        · simp only [hx]; constructor
          · have : (0 : ℝ) ≤ ((2 * (j + 1) : ℕ) : ℝ) * H := by positivity
            linarith
          · rw [← hxk]; simp only [hx]; push_cast
            have : (2 * ((j : ℝ) + 1)) * H ≤ 2 * k * H := by
              have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
              nlinarith
            linarith)
    simp only [show ∀ j : ℕ, 2 * (j + 1) = 2 * j + 2 from fun j => by ring] at this
    rw [this, hx0, hxk]
  -- rewrite the sum over `range k` as a sum over `Fin k`
  have hsum_fin : ∑ j ∈ Finset.range k, ∫ t in x (2 * j)..x (2 * j + 2), f t =
      ∑ j : Fin k, (H / 3 * (f (x (2 * j)) + 4 * f (x (2 * j + 1)) + f (x (2 * j + 2)))
        - H ^ 5 * g (μ j) / 90) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun j _ => hpanel j)
  -- the quadrature part equals `simpsonRule`
  have hquad : ∑ j : Fin k, H / 3 * (f (x (2 * j)) + 4 * f (x (2 * j + 1)) + f (x (2 * j + 2))) =
      simpsonRule f a b k := by
    rw [Fin.sum_univ_eq_sum_range (fun j => H / 3 * (f (x (2 * j)) + 4 * f (x (2 * j + 1))
      + f (x (2 * j + 2))))]
    unfold simpsonRule
    simp only
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have e1 : ∑ j ∈ Finset.range k, f (x (2 * j)) = f a + ∑ i ∈ Finset.Ico 1 k, f (a + (2 * i) * H) := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk, ← hx0]
      simp only [hx]; push_cast; simp
    have e2 : ∑ j ∈ Finset.range k, f (x (2 * j + 2)) =
        ∑ i ∈ Finset.Ico 1 k, f (a + (2 * i) * H) + f b := by
      have : ∑ j ∈ Finset.range k, f (x (2 * j + 2)) = ∑ i ∈ Finset.Ico 1 (k + 1), f (x (2 * i)) := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel]
        apply Finset.sum_congr rfl; intro i _; congr 2; ring
      rw [this, Finset.sum_Ico_succ_top (by omega), hxk]
      congr 1
      apply Finset.sum_congr rfl; intro i _; simp only [hx]; push_cast; ring_nf
    have e3 : ∑ j ∈ Finset.range k, f (x (2 * j + 1)) = ∑ i ∈ Finset.range k, f (a + (2 * i + 1) * H) := by
      apply Finset.sum_congr rfl; intro i _; simp only [hx]; push_cast; ring_nf
    rw [e1, e2, e3]
    ring
  -- intermediate value for the fourth derivative
  have hgc : ContinuousOn g (Set.Icc a b) :=
    hf.continuousOn_iteratedDerivWithin (by norm_num) (uniqueDiffOn_Icc hab)
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩
  obtain ⟨jmin, -, hjmin⟩ := Finset.exists_min_image Finset.univ (fun j => g (μ j)) hne
  obtain ⟨jmax, -, hjmax⟩ := Finset.exists_max_image Finset.univ (fun j => g (μ j)) hne
  set S := ∑ j : Fin k, g (μ j) with hS
  have hlo : g (μ jmin) ≤ S / k := by
    rw [le_div_iff₀ hkR]
    have := Finset.card_nsmul_le_sum Finset.univ (fun j => g (μ j)) (g (μ jmin))
      (fun j _ => hjmin j (Finset.mem_univ _))
    simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using this
  have hhi : S / k ≤ g (μ jmax) := by
    rw [div_le_iff₀ hkR]
    have := Finset.sum_le_card_nsmul Finset.univ (fun j => g (μ j)) (g (μ jmax))
      (fun j _ => hjmax j (Finset.mem_univ _))
    simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using this
  have hsubI : Set.uIcc (μ jmin) (μ jmax) ⊆ Set.Ioo a b := by
    intro y hy
    rcases Set.mem_uIcc.mp hy with h | h
    · exact ⟨lt_of_lt_of_le (hμab jmin).1 h.1, lt_of_le_of_lt h.2 (hμab jmax).2⟩
    · exact ⟨lt_of_lt_of_le (hμab jmax).1 h.1, lt_of_le_of_lt h.2 (hμab jmin).2⟩
  obtain ⟨m, hm, hgm⟩ := intermediate_value_uIcc
    (hgc.mono (hsubI.trans Set.Ioo_subset_Icc_self)) (Set.mem_uIcc_of_le hlo hhi)
  refine ⟨m, hsubI hm, ?_⟩
  rw [← hsum_int, hsum_fin, Finset.sum_sub_distrib, hquad, ← Finset.sum_div, ← Finset.mul_sum, ← hS]
  have hSk : S = k * g m := by rw [hgm]; field_simp
  rw [hSk, hH]
  field_simp
  ring
