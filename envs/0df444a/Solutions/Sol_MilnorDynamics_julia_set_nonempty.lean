-- Prove2me | solution 1 for MilnorDynamics.julia_set_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-29T15:29:15.992578+00:00
-- url     : https://prove2.me/submissions/c7a558c8-8ec4-42bf-be06-728c0c5d14cb

import Mathlib
import Definitions.Def_MilnorDynamics_RationalMaps

open scoped OnePoint
open Filter Set

/-!
# Milnor, Lemma 4.8: the Julia set of a rational map of degree `≥ 2` is nonempty

Proof outline.  Suppose the Fatou set is the whole sphere.

* Using the chordal metric (realised as the Euclidean distance after inverse stereographic
  projection `stereo`), and compactness of the sphere, every sequence of iterates `f^[n k]` has a
  subsequence converging uniformly on the whole sphere to a continuous map (`global_normal`).
* Take `f^[φ k] → g` uniformly, and then `f^[m (ψ j)] → h` uniformly where
  `m k = φ (k+1) - φ k`.  Passing to the limit in `f^[φ (ψ j + 1)] = f^[m (ψ j)] ∘ f^[φ (ψ j)]`
  gives `h ∘ g = g`.  Since `f` is surjective, so is `g` (`limit_surjective`), hence `h = id`.
* Since `deg f ≥ 2`, `f` is not injective: `f a = f b` with `a ≠ b`.  Then
  `f^[m] a = f^[m] b` for all `m ≥ 1`, and passing to the limit gives `a = h a = h b = b`.
-/

open scoped Topology
open Polynomial

namespace MilnorDynamics

/-- Inverse stereographic projection of the Riemann sphere onto the unit sphere of `ℝ³`. -/
noncomputable def stereo : OnePoint ℂ → EuclideanSpace ℝ (Fin 3)
  | some z => !₂[2 * z.re / (1 + ‖z‖ ^ 2), 2 * z.im / (1 + ‖z‖ ^ 2),
      (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2)]
  | none => !₂[0, 0, 1]

theorem chordalDist_some_none (z : ℂ) :
    2 / Real.sqrt (1 + ‖z‖ ^ 2) = dist (stereo (some z)) (stereo none) := by
  rw [EuclideanSpace.dist_eq]
  simp only [stereo, Fin.sum_univ_three, Real.dist_eq, sq_abs]
  simp
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1 : (0:ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  rw [eq_comm, Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
  rw [show (2 / √(1 + ‖z‖ ^ 2)) ^ 2 = 4 / (1 + ‖z‖ ^ 2) by
    rw [div_pow, Real.sq_sqrt h1.le]; norm_num]
  field_simp
  rw [hz]
  ring

/-- The chordal distance is the Euclidean distance after inverse stereographic projection. -/
theorem chordalDist_eq_dist (x y : OnePoint ℂ) : chordalDist x y = dist (stereo x) (stereo y) := by
  rcases x with _ | z <;> rcases y with _ | w
  · simp [chordalDist]
  · rw [dist_comm]; exact chordalDist_some_none w
  · exact chordalDist_some_none z
  · show 2 * ‖z - w‖ / (Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2)) = _
    rw [EuclideanSpace.dist_eq]
    simp only [stereo, Fin.sum_univ_three, Real.dist_eq, sq_abs]
    simp
    have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hw : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hzw : ‖z - w‖ ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have h1 : (0:ℝ) < 1 + ‖z‖ ^ 2 := by positivity
    have h2 : (0:ℝ) < 1 + ‖w‖ ^ 2 := by positivity
    rw [eq_comm, Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt h1.le, Real.sq_sqrt h2.le]
    field_simp
    rw [hzw, hz, hw]
    ring

theorem stereo_injective : Function.Injective stereo := by
  intro x y h
  have h0 : chordalDist x y = 0 := by rw [chordalDist_eq_dist, h, dist_self]
  rcases x with _ | z <;> rcases y with _ | w
  · rfl
  · exfalso
    simp only [chordalDist] at h0
    have : (0:ℝ) < 2 / Real.sqrt (1 + ‖w‖ ^ 2) := by positivity
    linarith
  · exfalso
    simp only [chordalDist] at h0
    have : (0:ℝ) < 2 / Real.sqrt (1 + ‖z‖ ^ 2) := by positivity
    linarith
  · simp only [chordalDist] at h0
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · have : z = w := by simpa [sub_eq_zero] using h0
      rw [this]
    · exfalso
      have : 0 < Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2) := by positivity
      linarith

theorem chordalDist_coe_le (z w : ℂ) : chordalDist (z : OnePoint ℂ) w ≤ 2 * ‖z - w‖ := by
  show 2 * ‖z - w‖ / (Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2)) ≤ _
  apply div_le_self (by positivity)
  have h1 : 1 ≤ Real.sqrt (1 + ‖z‖ ^ 2) := Real.one_le_sqrt.mpr (by nlinarith [norm_nonneg z])
  have h2 : 1 ≤ Real.sqrt (1 + ‖w‖ ^ 2) := Real.one_le_sqrt.mpr (by nlinarith [norm_nonneg w])
  nlinarith

theorem continuous_stereo : Continuous stereo := by
  rw [continuous_iff_continuousAt]
  intro x
  induction x using OnePoint.rec with
  | infty =>
    rw [ContinuousAt, OnePoint.tendsto_nhds_infty']
    refine ⟨tendsto_pure_nhds _ _, ?_⟩
    rw [Filter.coclosedCompact_eq_cocompact, tendsto_iff_dist_tendsto_zero]
    have : (fun z : ℂ => dist ((stereo ∘ OnePoint.some) z) (stereo ∞)) =
        fun z => 2 / Real.sqrt (1 + ‖z‖ ^ 2) := by
      funext z; rw [Function.comp_apply, ← chordalDist_eq_dist]; rfl
    rw [this]
    refine Tendsto.div_atTop tendsto_const_nhds ?_
    refine Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_left _ _ ?_)
    exact (tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cocompact_atTop
  | coe z =>
    rw [OnePoint.continuousAt_coe, Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε / 2, by positivity, fun w hw => ?_⟩
    rw [Function.comp_apply, Function.comp_apply, ← chordalDist_eq_dist]
    calc _ ≤ 2 * ‖w - z‖ := chordalDist_coe_le w z
      _ < ε := by rw [← dist_eq_norm]; linarith

theorem isEmbedding_stereo : Topology.IsEmbedding stereo :=
  (continuous_stereo.isClosedEmbedding stereo_injective).isEmbedding

theorem RationalMap.den_eval_ne_zero (f : RationalMap) {r : ℂ} (h : f.num.eval r = 0) :
    f.den.eval r ≠ 0 := by
  intro h'
  obtain ⟨u, v, huv⟩ := f.coprime
  have := congrArg (eval r) huv
  simp [h, h'] at this

theorem RationalMap.toFun_coe_of_eval (f : RationalMap) {a c : ℂ}
    (h : f.num.eval a = c * f.den.eval a) : f.toFun a = c := by
  have hq : f.den.eval a ≠ 0 := by
    intro hq
    exact f.den_eval_ne_zero (by rw [h, hq, mul_zero]) hq
  show (if f.den.eval a = 0 then ∞ else ((f.num.eval a / f.den.eval a : ℂ) : OnePoint ℂ)) = c
  rw [if_neg hq, h, mul_div_cancel_right₀ _ hq]

/-- A rational map of degree `≥ 1` is surjective on the Riemann sphere. -/
theorem RationalMap.toFun_surjective (f : RationalMap) (hf : 1 ≤ f.degree) :
    Function.Surjective f.toFun := by
  intro w
  induction w using OnePoint.rec with
  | infty =>
    by_cases hq : 0 < f.den.degree
    · obtain ⟨a, ha⟩ := Complex.exists_root hq
      refine ⟨a, ?_⟩
      show (if f.den.eval a = 0 then ∞ else _) = ∞
      rw [if_pos (show f.den.eval a = 0 from ha)]
    · have hq0 : f.den.natDegree = 0 := by
        rw [not_lt] at hq; exact natDegree_eq_zero_iff_degree_le_zero.2 hq
      have hp : f.den.natDegree < f.num.natDegree := by
        unfold RationalMap.degree at hf; omega
      refine ⟨∞, ?_⟩
      show (if f.den.natDegree < f.num.natDegree then ∞ else _) = ∞
      rw [if_pos hp]
  | coe c =>
    set P := f.num - C c * f.den with hP
    by_cases hdeg : 0 < P.degree
    · obtain ⟨a, ha⟩ := Complex.exists_root hdeg
      refine ⟨a, f.toFun_coe_of_eval ?_⟩
      simp only [hP, IsRoot, eval_sub, eval_mul, eval_C] at ha
      linear_combination ha
    · rw [not_lt] at hdeg
      obtain ⟨k, hk⟩ : ∃ k, P = C k := ⟨P.coeff 0, eq_C_of_degree_le_zero hdeg⟩
      have hp : f.num = C c * f.den + C k := by rw [← hk, hP]; ring
      have hpdeg : f.num.natDegree ≤ f.den.natDegree := by
        rw [hp]; exact (natDegree_add_le _ _).trans (max_le (natDegree_C_mul_le _ _) (by simp))
      have hqpos : 0 < f.den.natDegree := by
        unfold RationalMap.degree at hf; omega
      refine ⟨∞, ?_⟩
      show (if f.den.natDegree < f.num.natDegree then ∞
        else ((f.num.coeff f.den.natDegree / f.den.leadingCoeff : ℂ) : OnePoint ℂ)) = c
      rw [if_neg (by omega)]
      congr 1
      rw [hp, coeff_add, coeff_C_mul, coeff_C, if_neg hqpos.ne', add_zero, leadingCoeff,
        mul_div_cancel_right₀ _ (by simpa using f.den_ne_zero)]

/-- The Wronskian `p' q - p q'` of a nonconstant rational map `p / q` is nonzero. -/
theorem RationalMap.wronskian_ne_zero (f : RationalMap) (hf : 1 ≤ f.degree) :
    derivative f.num * f.den - f.num * derivative f.den ≠ 0 := by
  intro hW
  have h1 : f.num * derivative f.den = derivative f.num * f.den := (sub_eq_zero.1 hW).symm
  have hdvd : f.den ∣ derivative f.den * f.num := ⟨derivative f.num, by rw [mul_comm, h1]; ring⟩
  have hdvd' := f.coprime.symm.dvd_of_dvd_mul_right hdvd
  have hq' : derivative f.den = 0 := by
    by_cases h0 : f.den.natDegree = 0
    · exact derivative_of_natDegree_zero h0
    · exact eq_zero_of_dvd_of_natDegree_lt hdvd' (natDegree_derivative_lt h0)
  have hp' : derivative f.num = 0 := by
    rw [hq', mul_zero] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_right f.den_ne_zero
  have := natDegree_eq_zero_of_derivative_eq_zero hp'
  have := natDegree_eq_zero_of_derivative_eq_zero hq'
  unfold RationalMap.degree at hf
  omega

/-- A rational map of degree `≥ 2` is not injective on the Riemann sphere: for all but finitely
many `c`, the equation `p - c q = 0` has `≥ 2` distinct (simple) roots. -/
theorem RationalMap.exists_ne_toFun_eq (f : RationalMap) (hf : 2 ≤ f.degree) :
    ∃ a b : OnePoint ℂ, a ≠ b ∧ f.toFun a = f.toFun b := by
  classical
  set p := f.num with hp_def
  set q := f.den with hq_def
  set d := f.degree with hd_def
  set W := derivative p * q - p * derivative q with hW_def
  have hW : W ≠ 0 := f.wronskian_ne_zero (by omega)
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset
    (insert (p.coeff d / q.coeff d) (W.roots.toFinset.image (fun r => p.eval r / q.eval r)))
  rw [Finset.mem_insert, not_or, Finset.mem_image, not_exists] at hc
  set P := p - C c * q with hP_def
  have hPd : P.coeff d ≠ 0 := by
    rw [hP_def, coeff_sub, coeff_C_mul]
    by_cases hq : q.coeff d = 0
    · rw [hq, mul_zero, sub_zero]
      have hdq : d ≠ q.natDegree := by
        intro h
        rw [h, ← leadingCoeff, leadingCoeff_eq_zero] at hq
        exact f.den_ne_zero hq
      have hdp : d = p.natDegree := by
        rcases max_choice p.natDegree q.natDegree with h | h
        · exact h
        · exact absurd h hdq
      have hp0 : p ≠ 0 := by
        rintro h
        rw [h, natDegree_zero] at hdp
        omega
      rw [hdp, ← leadingCoeff]
      exact leadingCoeff_ne_zero.2 hp0
    · intro h
      apply hc.1
      rw [eq_div_iff hq]
      linear_combination -h
  have hPdeg : 2 ≤ P.natDegree := le_trans hf (le_natDegree_of_ne_zero hPd)
  have hsimple : ∀ r, P.eval r = 0 → (derivative P).eval r ≠ 0 := by
    intro r hr hr'
    simp only [hP_def, eval_sub, eval_mul, eval_C, derivative_sub, derivative_mul,
      derivative_C, zero_mul, zero_add] at hr hr'
    have hqr : q.eval r ≠ 0 := by
      intro h0
      exact f.den_eval_ne_zero (show p.eval r = 0 by rw [h0] at hr; linear_combination hr) h0
    have hWr : W.eval r = 0 := by
      simp only [hW_def, eval_sub, eval_mul]
      linear_combination (eval r q) * hr' - (eval r (derivative q)) * hr
    apply hc.2 r
    refine ⟨Multiset.mem_toFinset.2 ((mem_roots hW).2 hWr), ?_⟩
    rw [div_eq_iff hqr]
    linear_combination hr
  have hPpos : 0 < P.degree := by
    rw [degree_eq_natDegree (by rintro h; rw [h] at hPd; simp at hPd)]
    exact_mod_cast (by omega : 0 < P.natDegree)
  obtain ⟨a, ha⟩ := Complex.exists_root hPpos
  set Q := P /ₘ (X - C a) with hQ_def
  have hPQ : (X - C a) * Q = P := (mul_divByMonic_eq_iff_isRoot).2 ha
  have hQa : Q.eval a ≠ 0 := by
    intro h
    apply hsimple a ha
    rw [← hPQ, derivative_mul]
    simp [h]
  have hQdeg : 0 < Q.degree := by
    have : Q.natDegree = P.natDegree - 1 := by
      rw [hQ_def, natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]
    rw [degree_eq_natDegree (by rintro h; rw [h] at hQa; simp at hQa)]
    exact_mod_cast (by omega : 0 < Q.natDegree)
  obtain ⟨b, hb⟩ := Complex.exists_root hQdeg
  have hab : a ≠ b := by
    rintro rfl
    exact hQa hb
  have hPb : P.eval b = 0 := by
    rw [← hPQ, eval_mul, hb.eq_zero, mul_zero]
  have hPa : P.eval a = 0 := ha
  refine ⟨a, b, fun h => hab (OnePoint.coe_injective h), ?_⟩
  rw [f.toFun_coe_of_eval (c := c), f.toFun_coe_of_eval (c := c)]
  · simp only [hP_def, eval_sub, eval_mul, eval_C] at hPb; linear_combination hPb
  · simp only [hP_def, eval_sub, eval_mul, eval_C] at hPa; linear_combination hPa

/-- Iterated extraction of subsequences, one for each element of a finite set. -/
theorem exists_subseq_finset {α : Type*} (P : α → (ℕ → ℕ) → Prop)
    (hmono : ∀ i n (ψ : ℕ → ℕ), StrictMono ψ → P i n → P i (n ∘ ψ))
    (hex : ∀ i n, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P i (n ∘ ψ)) (T : Finset α) (n : ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i ∈ T, P i (n ∘ φ) := by
  classical
  induction T using Finset.induction_on generalizing n with
  | empty => exact ⟨id, strictMono_id, by simp⟩
  | insert a T _ ih =>
    obtain ⟨φ, hφ, hP⟩ := ih n
    obtain ⟨ψ, hψ, hPa⟩ := hex a (n ∘ φ)
    refine ⟨φ ∘ ψ, hφ.comp hψ, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hPa
    · exact hmono i (n ∘ φ) ψ hψ (hP i hi)

/-- Local data attached to a point of the Fatou set: a chart `c` with inverse `ι` on an open
neighbourhood `N` of the point, which `ι` maps into a compact subset `K` of an open set `V` on
which the iterates (read in the chart `c`) form a normal family. -/
theorem fatou_local_data (F : OnePoint ℂ → OnePoint ℂ) (x : OnePoint ℂ) (hx : x ∈ fatouSet F) :
    ∃ (c : ℂ → OnePoint ℂ) (ι : OnePoint ℂ → ℂ) (V K : Set ℂ) (N : Set (OnePoint ℂ)),
      IsOpen V ∧ IsCompact K ∧ K ⊆ V ∧ IsOpen N ∧ x ∈ N ∧ (∀ y ∈ N, ι y ∈ K ∧ c (ι y) = y) ∧
      ContinuousOn ι N ∧
      IsNormalFamily V ((fun g : OnePoint ℂ → OnePoint ℂ => fun w => g (c w)) ''
        range (fun n => F^[n])) := by
  induction x using OnePoint.rec with
  | infty =>
    obtain ⟨V, hV, h0, hnorm⟩ := hx
    obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hV 0 h0
    refine ⟨invChart, chartInfinite, V, Metric.closedBall 0 (r / 2),
      (OnePoint.some '' Metric.closedBall 0 (2 / r))ᶜ, hV, isCompact_closedBall _ _,
      (Metric.closedBall_subset_ball (by linarith)).trans hrV,
      ((isCompact_closedBall _ _).image OnePoint.continuous_coe).isClosed.isOpen_compl,
      by simp, ?_, ?_, hnorm⟩
    · intro y hy
      induction y using OnePoint.rec with
      | infty => exact ⟨by simp [chartInfinite]; positivity, by simp [invChart, chartInfinite]⟩
      | coe w =>
        have hw : 2 / r < ‖w‖ := by
          by_contra h
          exact hy ⟨w, by simpa using h, rfl⟩
        have hw' : 0 < ‖w‖ := lt_trans (by positivity) hw
        have hw0 : w ≠ 0 := norm_pos_iff.1 hw'
        refine ⟨?_, ?_⟩
        · show w⁻¹ ∈ Metric.closedBall 0 (r / 2)
          rw [Metric.mem_closedBall, dist_zero_right, norm_inv, inv_le_comm₀ hw' (by positivity),
            inv_div]
          exact hw.le
        · show invChart w⁻¹ = w
          simp [invChart, hw0]
    · intro y hy
      apply ContinuousAt.continuousWithinAt
      induction y using OnePoint.rec with
      | infty =>
        rw [ContinuousAt, OnePoint.tendsto_nhds_infty']
        refine ⟨tendsto_pure_nhds _ _, ?_⟩
        rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
        exact tendsto_inv₀_cobounded
      | coe w =>
        have hw0 : w ≠ 0 := by
          rintro rfl; exact hy ⟨0, by simp; positivity, rfl⟩
        rw [OnePoint.continuousAt_coe]
        exact continuousAt_inv₀ hw0
  | coe z =>
    obtain ⟨V, hV, hz, hnorm⟩ := hx
    obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hV z hz
    refine ⟨OnePoint.some, chartFinite, V, Metric.closedBall z (r / 2),
      OnePoint.some '' Metric.ball z (r / 2), hV, isCompact_closedBall _ _,
      (Metric.closedBall_subset_ball (by linarith)).trans hrV,
      OnePoint.isOpenMap_coe _ Metric.isOpen_ball, ⟨z, Metric.mem_ball_self (by positivity), rfl⟩,
      ?_, ?_, hnorm⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact ⟨Metric.ball_subset_closedBall hw, rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      apply ContinuousAt.continuousWithinAt
      rw [OnePoint.continuousAt_coe]
      exact continuous_id.continuousAt

/-- If every point is in the Fatou set of `F`, every sequence of iterates of `F` has a
subsequence converging uniformly on the whole sphere (in the chordal metric) to a continuous
self-map of the sphere. -/
theorem global_normal (F : OnePoint ℂ → OnePoint ℂ) (hF : ∀ x, x ∈ fatouSet F) (n : ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : OnePoint ℂ → OnePoint ℂ, Continuous g ∧
      TendstoUniformly (fun k x => stereo (F^[n (φ k)] x)) (fun x => stereo (g x)) atTop := by
  classical
  choose c ι V K N hV hK hKV hN hxN hι hιc hnorm using fun x => fatou_local_data F x (hF x)
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover N hN
    (fun x _ => mem_iUnion.2 ⟨x, hxN x⟩)
  have hcover : ∀ y, ∃ x ∈ T, y ∈ N x := fun y => by
    simpa using hT (mem_univ y)
  let P : OnePoint ℂ → (ℕ → ℕ) → Prop := fun x n => ∃ g : ℂ → OnePoint ℂ,
    ContinuousOn g (V x) ∧ TendstoLocallyUniformlyOnSphere (fun k w => F^[n k] (c x w)) g (V x)
  have hmono : ∀ x n (ψ : ℕ → ℕ), StrictMono ψ → P x n → P x (n ∘ ψ) := by
    rintro x n ψ hψ ⟨g, hg, hconv⟩
    exact ⟨g, hg, fun K' hK' hK'c ε hε => hψ.tendsto_atTop.eventually (hconv K' hK' hK'c ε hε)⟩
  have hex : ∀ x n, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P x (n ∘ ψ) := by
    intro x n
    obtain ⟨ψ, hψ, g, hg, hconv⟩ := hnorm x (fun k w => F^[n k] (c x w))
      (fun k => ⟨F^[n k], ⟨n k, rfl⟩, rfl⟩)
    exact ⟨ψ, hψ, g, hg, hconv⟩
  obtain ⟨φ, hφ, hP⟩ := exists_subseq_finset P hmono hex T n
  choose! g hg hconv using hP
  -- uniform convergence on each `N x`, `x ∈ T`
  have hunifN : ∀ x ∈ T, ∀ ε > 0, ∀ᶠ k in atTop, ∀ y ∈ N x,
      dist (stereo (F^[n (φ k)] y)) (stereo (g x (ι x y))) < ε := by
    intro x hx ε hε
    filter_upwards [hconv x hx (K x) (hKV x) (hK x) ε hε] with k hk y hy
    have := hk (ι x y) (hι x y hy).1
    rw [(hι x y hy).2, chordalDist_eq_dist] at this
    exact this
  have hlim : ∀ x ∈ T, ∀ y ∈ N x,
      Tendsto (fun k => stereo (F^[n (φ k)] y)) atTop (𝓝 (stereo (g x (ι x y)))) := by
    intro x hx y hy
    exact Metric.tendsto_nhds.2 fun ε hε => (hunifN x hx ε hε).mono fun k hk => hk y hy
  let G : OnePoint ℂ → EuclideanSpace ℝ (Fin 3) := fun y =>
    limUnder atTop (fun k => stereo (F^[n (φ k)] y))
  have hG : ∀ x ∈ T, ∀ y ∈ N x, G y = stereo (g x (ι x y)) := fun x hx y hy =>
    (hlim x hx y hy).limUnder_eq
  have hGr : ∀ y, ∃ z, stereo z = G y := fun y => by
    obtain ⟨x, hx, hy⟩ := hcover y
    exact ⟨_, (hG x hx y hy).symm⟩
  let gg : OnePoint ℂ → OnePoint ℂ := fun y => Function.invFun stereo (G y)
  have hgg : ∀ y, stereo (gg y) = G y := fun y => Function.invFun_eq (hGr y)
  refine ⟨φ, hφ, gg, ?_, ?_⟩
  · rw [isEmbedding_stereo.continuous_iff, continuous_iff_continuousAt]
    intro y
    obtain ⟨x, hx, hy⟩ := hcover y
    have heq : (fun y' => stereo (g x (ι x y'))) =ᶠ[𝓝 y] (stereo ∘ gg) :=
      Filter.eventually_of_mem ((hN x).mem_nhds hy) fun y' hy' => by
        simp only [Function.comp_apply, hgg, hG x hx y' hy']
    refine ContinuousAt.congr ?_ heq
    exact continuous_stereo.continuousAt.comp
      (((hg x hx).continuousAt ((hV x).mem_nhds ((hKV x) (hι x y hy).1))).comp
        ((hιc x).continuousAt ((hN x).mem_nhds hy)))
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(Filter.eventually_all_finset T).2 (fun x hx => hunifN x hx ε hε)] with k hk y
    obtain ⟨x, hx, hy⟩ := hcover y
    rw [hgg, hG x hx y hy, dist_comm]
    exact hk x hx y hy

/-- A uniform limit of surjective self-maps of the sphere is surjective. -/
theorem limit_surjective (F : ℕ → OnePoint ℂ → OnePoint ℂ) (hF : ∀ k, Function.Surjective (F k))
    (g : OnePoint ℂ → OnePoint ℂ) (hg : Continuous g)
    (hU : TendstoUniformly (fun k x => stereo (F k x)) (fun x => stereo (g x)) atTop) :
    Function.Surjective g := by
  intro w
  choose z hz using fun k => hF k w
  obtain ⟨a, ha_mem, φ, hφ, ha⟩ := (isCompact_range continuous_stereo).tendsto_subseq
    (x := fun k => stereo (z k)) (fun k => mem_range_self _)
  obtain ⟨z₀, rfl⟩ := ha_mem
  have hz₀ : Tendsto (fun k => z (φ k)) atTop (𝓝 z₀) := by
    rw [isEmbedding_stereo.tendsto_nhds_iff]
    exact ha
  have hU' : TendstoUniformly (fun k x => stereo (F (φ k) x)) (fun x => stereo (g x)) atTop :=
    fun u hu => hφ.tendsto_atTop.eventually (hU u hu)
  have h1 := hU'.tendsto_comp (continuous_stereo.comp hg).continuousAt hz₀
  simp only [hz, tendsto_const_nhds_iff] at h1
  exact ⟨z₀, stereo_injective h1.symm⟩

theorem julia_set_nonempty (f : RationalMap) (hf : 2 ≤ f.degree) :
    (juliaSet f.toFun).Nonempty := by
  by_contra hJ
  have hF : ∀ x, x ∈ fatouSet f.toFun := fun x => by
    by_contra hx
    exact hJ ⟨x, hx⟩
  obtain ⟨φ, hφ, g, hg, hgU⟩ := global_normal _ hF id
  obtain ⟨ψ, hψ, h, hh, hhU⟩ := global_normal _ hF (fun k => φ (k + 1) - φ k)
  have hsurj : ∀ k, Function.Surjective (f.toFun^[id (φ k)]) := fun k =>
    (f.toFun_surjective (by omega)).iterate _
  have gsurj := limit_surjective _ hsurj g hg hgU
  -- `h ∘ g = g`
  have hfix : ∀ x, h (g x) = g x := by
    intro x
    have hψ' : Tendsto ψ atTop atTop := hψ.tendsto_atTop
    have h1 : Tendsto (fun j => stereo (f.toFun^[φ (ψ j + 1)] x)) atTop (𝓝 (stereo (g x))) :=
      (hgU.tendsto_at x).comp (tendsto_atTop_mono (fun j => Nat.le_succ _) hψ')
    have hy : Tendsto (fun j => f.toFun^[φ (ψ j)] x) atTop (𝓝 (g x)) := by
      rw [isEmbedding_stereo.tendsto_nhds_iff]
      exact (hgU.tendsto_at x).comp hψ'
    have h2 : Tendsto (fun j => stereo (f.toFun^[φ (ψ j + 1) - φ (ψ j)]
        (f.toFun^[φ (ψ j)] x))) atTop (𝓝 (stereo (h (g x)))) :=
      hhU.tendsto_comp (continuous_stereo.comp hh).continuousAt hy
    have h3 : (fun j => stereo (f.toFun^[φ (ψ j + 1) - φ (ψ j)] (f.toFun^[φ (ψ j)] x))) =
        fun j => stereo (f.toFun^[φ (ψ j + 1)] x) := by
      funext j
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel (hφ (Nat.lt_succ_self _)).le]
    rw [h3] at h2
    exact stereo_injective (tendsto_nhds_unique h2 h1)
  obtain ⟨a, b, hab, hfab⟩ := f.exists_ne_toFun_eq hf
  have key : ∀ j, f.toFun^[φ (ψ j + 1) - φ (ψ j)] a = f.toFun^[φ (ψ j + 1) - φ (ψ j)] b := by
    intro j
    obtain ⟨k, hk⟩ : ∃ k, φ (ψ j + 1) - φ (ψ j) = k + 1 :=
      ⟨φ (ψ j + 1) - φ (ψ j) - 1, by have := hφ (lt_add_one (ψ j)); omega⟩
    rw [hk, Function.iterate_succ_apply, Function.iterate_succ_apply, hfab]
  have ha := hhU.tendsto_at a
  have hb := hhU.tendsto_at b
  simp only [key] at ha
  have hab' : h a = h b := stereo_injective (tendsto_nhds_unique ha hb)
  obtain ⟨xa, rfl⟩ := gsurj a
  obtain ⟨xb, rfl⟩ := gsurj b
  rw [hfix, hfix] at hab'
  exact hab hab'

end MilnorDynamics

theorem solution (f : MilnorDynamics.RationalMap) (hf : 2 ≤ f.degree) :
    (MilnorDynamics.juliaSet f.toFun).Nonempty :=
  MilnorDynamics.julia_set_nonempty f hf
