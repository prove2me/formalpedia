-- Prove2me | solution 1 for NonsmoothLojasiewicz.Convex.moreauEnv_properties
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T00:31:58.011371+00:00
-- url     : https://prove2.me/submissions/abcdbb29-16ae-4192-9f4e-b9c9ec153cfa

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_MoreauProx_Characterization_Prox
import Definitions.Def_NonsmoothLojasiewicz_Convex_crit
import Definitions.Def_NonsmoothLojasiewicz_Convex_moreauEnv

set_option autoImplicit false

open Filter Topology
open NonconvexSplitting.Shared MoreauProx.Characterization
open scoped InnerProductSpace

/-- If `0 ≤ K + t * M` for all `t ∈ (0, 1]` with `M ≥ 0`, then `0 ≤ K`. -/
theorem mpc_nonneg_of_forall {K M : ℝ} (hM : 0 ≤ M)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ K + t * M) : 0 ≤ K := by
  by_contra hK'
  have hK : K < 0 := not_le.mp hK'
  set s : ℝ := -K / (2 * (M + 1)) with hs
  have hM1 : 0 < 2 * (M + 1) := by linarith
  have hs0 : 0 < s := div_pos (neg_pos.mpr hK) hM1
  have hsM : s * (2 * (M + 1)) = -K := by
    rw [hs]; field_simp
  set t : ℝ := min 1 s with ht
  have ht0 : 0 < t := lt_min one_pos hs0
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ s := min_le_right _ _
  have h1 := h t ht0 ht1
  have h2 : t * M ≤ s * M := mul_le_mul_of_nonneg_right ht2 hM
  nlinarith

/-- A proximal point of a `Γ₀` function has a finite value. -/
theorem mpc_prox_finite {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H → EReal) (hg : GammaZero g) (z x : H) (hp : IsProx g z x) :
    ∃ a : ℝ, g x = (a : EReal) := by
  obtain ⟨x0, hx0⟩ := hg.2.1
  have h := hp x0
  have hne : g x ≠ ⊤ := by
    intro htop
    rw [htop, EReal.coe_add_top] at h
    have hc := (EReal.coe_toReal hx0 (hg.1 x0)).symm
    rw [hc, ← EReal.coe_add, top_le_iff] at h
    exact EReal.coe_ne_top _ h
  exact ⟨(g x).toReal, (EReal.coe_toReal hne (hg.1 x)).symm⟩

/-- Variational inequality from minimality of the proximal objective and convexity. -/
theorem mpc_varineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H → EReal) (hg : GammaZero g) (z x : H) (a : ℝ) (hgx : g x = (a : EReal))
    (hp : IsProx g z x) (u : H) (c : ℝ) (hgu : g u = (c : EReal)) :
    ⟪u - x, z - x⟫_ℝ ≤ c - a := by
  have hconvx : Convex ℝ {q : H × ℝ | g q.1 ≤ ((q.2 : ℝ) : EReal)} := hg.2.2.1
  have key : 0 ≤ (c - a - ⟪u - x, z - x⟫_ℝ) := by
    refine mpc_nonneg_of_forall (M := ‖u - x‖ ^ 2 / 2) (by positivity) ?_
    intro t ht0 ht1
    have hxe : (x, a) ∈ {q : H × ℝ | g q.1 ≤ ((q.2 : ℝ) : EReal)} := by
      simp only [Set.mem_ofPred_eq, hgx, le_refl]
    have hue : (u, c) ∈ {q : H × ℝ | g q.1 ≤ ((q.2 : ℝ) : EReal)} := by
      simp only [Set.mem_ofPred_eq, hgu, le_refl]
    have hconv := hconvx hxe hue (a := 1 - t) (b := t) (by linarith) ht0.le (by ring)
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hconv
    have hpr := hp ((1 - t) • x + t • u)
    rw [hgx] at hpr
    have h2 := hpr.trans (add_le_add le_rfl hconv)
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
    have heq : (1 - t) • x + t • u - z = t • (u - x) - (z - x) := by
      simp only [sub_smul, one_smul, smul_sub]; abel
    rw [heq, norm_sub_rev x z, norm_sub_sq_real (t • (u - x)) (z - x), norm_smul,
      real_inner_smul_left] at h2
    have hn : (‖t‖ * ‖u - x‖) ^ 2 = t ^ 2 * ‖u - x‖ ^ 2 := by
      rw [mul_pow, Real.norm_eq_abs, sq_abs]
    rw [hn] at h2
    by_contra hneg'
    have hneg := not_le.mp hneg'
    have : t * (c - a - ⟪u - x, z - x⟫_ℝ + t * (‖u - x‖ ^ 2 / 2)) < 0 :=
      mul_neg_of_pos_of_neg ht0 hneg
    nlinarith
  linarith

/-- A prox map of a `Γ₀` function contracts distances. -/
theorem mpc_nonexp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : H → H) (g : H → EReal) (hg : GammaZero g) (hp : ∀ z, IsProx g z (p z)) (z z' : H) :
    ‖p z - p z'‖ ≤ ‖z - z'‖ := by
  obtain ⟨a, ha⟩ := mpc_prox_finite g hg z (p z) (hp z)
  obtain ⟨a', ha'⟩ := mpc_prox_finite g hg z' (p z') (hp z')
  have h1 := mpc_varineq g hg z (p z) a ha (hp z) (p z') a' ha'
  have h2 := mpc_varineq g hg z' (p z') a' ha' (hp z') (p z) a ha
  have hsq : ‖p z - p z'‖ ^ 2 ≤ ⟪p z - p z', z - z'⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢
    have c1 := real_inner_comm (p z) (p z')
    have c2 := real_inner_comm (p z) z'
    have c3 := real_inner_comm (p z') z
    have c4 := real_inner_comm (p z) z
    have c5 := real_inner_comm (p z') z'
    linarith
  have hcs := real_inner_le_norm (p z - p z') (z - z')
  by_contra hc
  have hc' := not_le.mp hc
  nlinarith [norm_nonneg (z - z'), norm_nonneg (p z - p z')]

theorem me_real_of {x : EReal} (h1 : x ≠ ⊥) (h2 : x ≠ ⊤) : x = ((x.toReal : ℝ) : EReal) :=
  (EReal.coe_toReal h2 h1).symm

/-- Convexity inequality at finite values. -/
theorem me_conv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : GammaZero f) (a b : H) (α β t : ℝ) (ha : f a = (α : EReal))
    (hb : f b = (β : EReal)) (t0 : 0 ≤ t) (t1 : t ≤ 1) :
    f ((1 - t) • a + t • b) ≤ (((1 - t) * α + t * β : ℝ) : EReal) := by
  have hconvx : Convex ℝ {q : H × ℝ | f q.1 ≤ ((q.2 : ℝ) : EReal)} := hf.2.2.1
  have hxe : (a, α) ∈ {q : H × ℝ | f q.1 ≤ ((q.2 : ℝ) : EReal)} := by
    simp only [Set.mem_ofPred_eq, ha, le_refl]
  have hue : (b, β) ∈ {q : H × ℝ | f q.1 ≤ ((q.2 : ℝ) : EReal)} := by
    simp only [Set.mem_ofPred_eq, hb, le_refl]
  have hconv := hconvx hxe hue (a := 1 - t) (b := t) (by linarith) t0 (by ring)
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hconv
  exact hconv

/-- A `Γ₀` function on a proper space has a linear-growth lower bound. -/
theorem me_growth {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [ProperSpace H]
    (f : H → EReal) (hf : GammaZero f) :
    ∃ x0 : H, ∃ r0 K : ℝ, f x0 = (r0 : EReal) ∧ 0 ≤ K ∧
      ∀ u, ((r0 - K - K * ‖u - x0‖ : ℝ) : EReal) ≤ f u := by
  obtain ⟨x0, hx0⟩ := hf.2.1
  set r0 := (f x0).toReal
  have hr0 : f x0 = (r0 : EReal) := me_real_of (hf.1 x0) hx0
  have hne : (Metric.closedBall x0 1).Nonempty := ⟨x0, Metric.mem_closedBall_self zero_le_one⟩
  obtain ⟨a, -, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne (isCompact_closedBall x0 1)
    (hf.2.2.2.lowerSemicontinuousOn _)
  have hfa_le : f a ≤ f x0 := hmin (Metric.mem_closedBall_self zero_le_one)
  have hfa_top : f a ≠ ⊤ := ne_top_of_le_ne_top hx0 hfa_le
  set m0 := (f a).toReal
  have hm0 : f a = (m0 : EReal) := me_real_of (hf.1 a) hfa_top
  have hm0r : m0 ≤ r0 := by
    rw [hm0, hr0] at hfa_le; exact_mod_cast hfa_le
  refine ⟨x0, r0, r0 - m0, hr0, by linarith, ?_⟩
  intro u
  by_cases hu : ‖u - x0‖ ≤ 1
  · have h1 : f a ≤ f u := hmin (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hu)
    rw [hm0] at h1
    refine le_trans ?_ h1
    have : 0 ≤ (r0 - m0) * ‖u - x0‖ := mul_nonneg (by linarith) (norm_nonneg _)
    exact_mod_cast (by linarith : r0 - (r0 - m0) - (r0 - m0) * ‖u - x0‖ ≤ m0)
  · push Not at hu
    by_cases hut : f u = ⊤
    · rw [hut]; exact le_top
    set β := (f u).toReal
    have hβ : f u = (β : EReal) := me_real_of (hf.1 u) hut
    set d := ‖u - x0‖ with hd_def
    have hd : 0 < d := by linarith
    set t := 1 / d with ht_def
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 1 := by rw [ht_def, div_le_one hd]; linarith
    have htd : t * d = 1 := one_div_mul_cancel hd.ne'
    have hc := me_conv f hf x0 u r0 β t hr0 hβ ht0 ht1
    have hmem : (1 - t) • x0 + t • u ∈ Metric.closedBall x0 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have : (1 - t) • x0 + t • u - x0 = t • (u - x0) := by
        simp only [sub_smul, one_smul, smul_sub]; abel
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, ← hd_def, htd]
    have h2 := (hmin hmem).trans hc
    rw [hm0] at h2
    have h3 : m0 ≤ (1 - t) * r0 + t * β := by exact_mod_cast h2
    rw [hβ]
    have e : ((1 - t) * r0 + t * β) * d = r0 * d - r0 + β := by
      linear_combination (β - r0) * htd
    have h4 : m0 * d ≤ r0 * d - r0 + β := by
      have := mul_le_mul_of_nonneg_right h3 hd.le
      linarith
    have h5 : r0 - (r0 - m0) - (r0 - m0) * d ≤ β := by nlinarith
    exact_mod_cast h5

/-- Existence of a proximal point. -/
theorem me_prox_exists {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [ProperSpace H] (f : H → EReal) (hf : GammaZero f) (x : H) : ∃ q, IsProx f x q := by
  obtain ⟨x0, r0, K, hr0, hK, hgr⟩ := me_growth f hf
  set φ : H → EReal := fun u => (((‖u - x‖ ^ 2 / 2 : ℝ)) : EReal) + f u with hφ
  have hφlsc : LowerSemicontinuous φ := by
    refine LowerSemicontinuous.add' ?_ hf.2.2.2 ?_
    · exact (continuous_coe_real_ereal.comp (by fun_prop)).lowerSemicontinuous
    · intro u
      exact EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))
  set c := ‖x - x0‖ with hc_def
  set R := 2 * (c + K) + 2 with hR
  have hc0 : 0 ≤ c := norm_nonneg _
  have hR0 : 0 ≤ R := by positivity
  have hne : (Metric.closedBall x0 R).Nonempty := ⟨x0, Metric.mem_closedBall_self hR0⟩
  obtain ⟨q, -, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne (isCompact_closedBall x0 R)
    (hφlsc.lowerSemicontinuousOn _)
  refine ⟨q, fun u => ?_⟩
  show φ q ≤ φ u
  by_cases hu : u ∈ Metric.closedBall x0 R
  · exact hmin hu
  · refine (hmin (Metric.mem_closedBall_self hR0)).trans ?_
    rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hu
    have hg := hgr u
    show (((‖x0 - x‖ ^ 2 / 2 : ℝ)) : EReal) + f x0 ≤ (((‖u - x‖ ^ 2 / 2 : ℝ)) : EReal) + f u
    rw [hr0]
    refine le_trans ?_ (add_le_add le_rfl hg)
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    set d := ‖u - x0‖ with hd_def
    have hux : d - c ≤ ‖u - x‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub u x x0
      linarith
    have hx0x : ‖x0 - x‖ = c := norm_sub_rev _ _
    rw [hx0x]
    have hdc : 0 ≤ d - c := by linarith
    have hsq : (d - c) ^ 2 ≤ ‖u - x‖ ^ 2 := pow_le_pow_left₀ hdc hux 2
    have hdpos : 0 < d := lt_of_le_of_lt hR0 hu
    have hm := mul_pos (sub_pos.mpr hu) hdpos
    nlinarith

open NonsmoothLojasiewicz.Convex in
/-- The envelope equals the value at the proximal point. -/
theorem me_env_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : GammaZero f) (p : H → H) (hp : ∀ x, IsProx f x (p x)) (x : H) :
    moreauEnv f x = (((f (p x)).toReal + ‖x - p x‖ ^ 2 / 2 : ℝ) : EReal) := by
  obtain ⟨a, ha⟩ := mpc_prox_finite f hf x (p x) (hp x)
  have hat : (f (p x)).toReal = a := by rw [ha, EReal.toReal_coe]
  rw [hat]
  unfold moreauEnv
  apply le_antisymm
  · refine (iInf_le _ (p x)).trans (le_of_eq ?_)
    rw [ha, EReal.coe_add]
  · refine le_iInf fun u => ?_
    have h1 := hp x u
    rw [ha, norm_sub_rev (p x) x, norm_sub_rev u x] at h1
    rw [EReal.coe_add, add_comm (f u), add_comm ((a : ℝ) : EReal)]
    exact h1

/-- Quadratic upper bound for the envelope. -/
theorem me_upper {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : GammaZero f) (p : H → H) (hp : ∀ x, IsProx f x (p x)) (x y : H) :
    (f (p y)).toReal + ‖y - p y‖ ^ 2 / 2 ≤
      ((f (p x)).toReal + ‖x - p x‖ ^ 2 / 2) + ⟪x - p x, y - x⟫_ℝ + ‖y - x‖ ^ 2 / 2 := by
  obtain ⟨a, ha⟩ := mpc_prox_finite f hf x (p x) (hp x)
  obtain ⟨b, hb⟩ := mpc_prox_finite f hf y (p y) (hp y)
  have h1 := hp y (p x)
  rw [ha, hb, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
  rw [ha, hb, EReal.toReal_coe, EReal.toReal_coe]
  have e1 : ‖p x - y‖ ^ 2 = ‖y - x‖ ^ 2 + 2 * ⟪y - x, x - p x⟫_ℝ + ‖x - p x‖ ^ 2 := by
    rw [norm_sub_rev (p x) y, show y - p x = (y - x) + (x - p x) by abel, norm_add_sq_real]
  have e2 : ‖p y - y‖ = ‖y - p y‖ := norm_sub_rev _ _
  have e3 := real_inner_comm (y - x) (x - p x)
  rw [e1, e2] at h1
  linarith

/-- Quadratic lower bound for the envelope. -/
theorem me_lower {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : GammaZero f) (p : H → H) (hp : ∀ x, IsProx f x (p x)) (x y : H) :
    ((f (p x)).toReal + ‖x - p x‖ ^ 2 / 2) + ⟪x - p x, y - x⟫_ℝ - ‖y - x‖ ^ 2 / 2 ≤
      (f (p y)).toReal + ‖y - p y‖ ^ 2 / 2 := by
  have h1 := me_upper f hf p hp y x
  have hne := mpc_nonexp p f hf hp y x
  have key : ⟪y - p y, x - y⟫_ℝ =
      -(⟪y - x, y - x⟫_ℝ) - ⟪x - p x, y - x⟫_ℝ + ⟪p y - p x, y - x⟫_ℝ := by
    have : y - p y = (y - x) + (x - p x) - (p y - p x) := by abel
    rw [this, show x - y = -(y - x) by abel, inner_neg_right, inner_sub_left, inner_add_left]
    ring
  rw [real_inner_self_eq_norm_sq] at key
  have hcs := real_inner_le_norm (p y - p x) (y - x)
  have hm := mul_le_mul_of_nonneg_right hne (norm_nonneg (y - x))
  have e4 : ‖x - y‖ = ‖y - x‖ := norm_sub_rev _ _
  rw [key, e4] at h1
  nlinarith

/-- The proximal map is continuous. -/
theorem me_p_cont {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : GammaZero f) (p : H → H) (hp : ∀ x, IsProx f x (p x)) :
    Continuous p := by
  refine (LipschitzWith.of_dist_le_mul fun x y => ?_).continuous (K := 1)
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  exact mpc_nonexp p f hf hp x y

/-- Derivative from the two-sided quadratic bounds. -/
theorem me_hasFDeriv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (h : H → ℝ) (G : H → H)
    (hu : ∀ x y, h y ≤ h x + ⟪G x, y - x⟫_ℝ + ‖y - x‖ ^ 2 / 2)
    (hl : ∀ x y, h x + ⟪G x, y - x⟫_ℝ - ‖y - x‖ ^ 2 / 2 ≤ h y) (x : H) :
    HasFDerivAt h (innerSL ℝ (G x)) x := by
  rw [hasFDerivAt_iff_isLittleO]
  refine Asymptotics.isLittleO_iff.mpr fun c hc => ?_
  filter_upwards [Metric.closedBall_mem_nhds x (by linarith : (0:ℝ) < 2 * c)] with y hy
  rw [Metric.mem_closedBall, dist_eq_norm] at hy
  rw [innerSL_apply_apply, Real.norm_eq_abs, abs_le]
  have h1 := hu x y
  have h2 := hl x y
  have : ‖y - x‖ ^ 2 / 2 ≤ c * ‖y - x‖ := by nlinarith [norm_nonneg (y - x)]
  constructor <;> linarith

/-- The gradient is a regular subgradient. -/
theorem me_reg_grad {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (h : H → ℝ) (G : H → H)
    (hl : ∀ x y, h x + ⟪G x, y - x⟫_ℝ - ‖y - x‖ ^ 2 / 2 ≤ h y) (x : H) :
    IsRegularSubgrad (fun z => ((h z : ℝ) : EReal)) x (G x) := by
  refine ⟨EReal.coe_ne_top _, fun ε hε => ?_⟩
  filter_upwards [Metric.closedBall_mem_nhds x (by linarith : (0:ℝ) < 2 * ε)] with z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  show ((h x : ℝ) : EReal) + ((⟪G x, z - x⟫_ℝ - ε * ‖z - x‖ : ℝ) : EReal) ≤ ((h z : ℝ) : EReal)
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  have h1 := hl x z
  have : ‖z - x‖ ^ 2 / 2 ≤ ε * ‖z - x‖ := by nlinarith [norm_nonneg (z - x)]
  linarith

/-- A regular subgradient of a function with the quadratic upper bound is the gradient. -/
theorem me_reg_unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (h : H → ℝ) (G : H → H)
    (hu : ∀ x y, h y ≤ h x + ⟪G x, y - x⟫_ℝ + ‖y - x‖ ^ 2 / 2) (x v : H)
    (hv : IsRegularSubgrad (fun z => ((h z : ℝ) : EReal)) x v) : v = G x := by
  by_contra hne
  set w := v - G x with hw
  have hd : 0 < ‖w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  set d := ‖w‖ with hd_def
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hv.2 (d / 4) (by positivity))
  set s := min 1 (δ / (2 * d)) with hs_def
  have hs0 : 0 < s := lt_min one_pos (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hs2 : s ≤ δ / (2 * d) := min_le_right _ _
  have hsd : s * d < δ := by
    have h1 := mul_le_mul_of_nonneg_right hs2 hd.le
    have h2 : δ / (2 * d) * d = δ / 2 := by field_simp
    linarith
  set z := x + s • w with hz
  have hzx : z - x = s • w := by rw [hz]; abel
  have hnz : ‖s • w‖ = s * d := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
  have h1 := hball (show dist z x < δ by rw [dist_eq_norm, hzx, hnz]; exact hsd)
  have h1' : h x + (⟪v, z - x⟫_ℝ - d / 4 * ‖z - x‖) ≤ h z := by
    have := h1
    simp only at this
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at this
    exact this
  have h2 := hu x z
  rw [hzx, hnz, real_inner_smul_right] at h1' h2
  have hvw : ⟪v, w⟫_ℝ - ⟪G x, w⟫_ℝ = d ^ 2 := by
    rw [← inner_sub_left, ← hw, real_inner_self_eq_norm_sq]
  have hss : s ^ 2 * d ^ 2 ≤ s * d ^ 2 := by
    have : s ^ 2 ≤ s := by nlinarith
    nlinarith [sq_nonneg d]
  have e3 : (s * d) ^ 2 = s ^ 2 * d ^ 2 := by ring
  have e4 : s * ⟪v, w⟫_ℝ - s * ⟪G x, w⟫_ℝ = s * d ^ 2 := by rw [← mul_sub, hvw]
  have hpos : 0 < s * d ^ 2 := mul_pos hs0 (pow_pos hd 2)
  nlinarith

open NonsmoothLojasiewicz.Convex in
/-- Critical points of a function with gradient `G` and two-sided quadratic bounds. -/
theorem me_crit_smooth {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (h : H → ℝ) (G : H → H) (hGc : Continuous G)
    (hu : ∀ x y, h y ≤ h x + ⟪G x, y - x⟫_ℝ + ‖y - x‖ ^ 2 / 2)
    (hl : ∀ x y, h x + ⟪G x, y - x⟫_ℝ - ‖y - x‖ ^ 2 / 2 ≤ h y) (x : H) :
    x ∈ crit (fun z => ((h z : ℝ) : EReal)) ↔ G x = 0 := by
  simp only [crit, LimitingSubdiff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨-, xs, vs, hxs, -, hvs, hreg⟩
    have heq : vs = fun t => G (xs t) := funext fun t => me_reg_unique h G hu (xs t) (vs t) (hreg t)
    rw [heq] at hvs
    exact tendsto_nhds_unique ((hGc.tendsto x).comp hxs) hvs
  · intro hG
    refine ⟨EReal.coe_ne_top _, fun _ => x, fun _ => 0, tendsto_const_nhds, tendsto_const_nhds,
      tendsto_const_nhds, fun _ => ?_⟩
    have := me_reg_grad h G hl x
    rw [hG] at this
    exact this

/-- A regular subgradient of a convex function is a global subgradient. -/
theorem me_reg_global {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : GammaZero f) (y v : H) (hv : IsRegularSubgrad f y v)
    (a : ℝ) (ha : f y = (a : EReal)) (z : H) (c : ℝ) (hc : f z = (c : EReal)) :
    a + ⟪v, z - y⟫_ℝ ≤ c := by
  by_contra hlt
  push Not at hlt
  set η := a + ⟪v, z - y⟫_ℝ - c with hη_def
  have hη : 0 < η := by linarith
  set ε := η / (2 * (‖z - y‖ + 1)) with hε_def
  have hε : 0 < ε := by positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hv.2 ε hε)
  set t := min 1 (δ / (2 * (‖z - y‖ + 1))) with ht_def
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ δ / (2 * (‖z - y‖ + 1)) := min_le_right _ _
  set w := (1 - t) • y + t • z with hw
  have hwy : w - y = t • (z - y) := by rw [hw]; simp only [sub_smul, one_smul, smul_sub]; abel
  have hnw : ‖w - y‖ = t * ‖z - y‖ := by rw [hwy, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
  have hdist : dist w y < δ := by
    rw [dist_eq_norm, hnw]
    have h1 : t * ‖z - y‖ ≤ δ / (2 * (‖z - y‖ + 1)) * (‖z - y‖ + 1) := by
      have := mul_le_mul_of_nonneg_right ht2 (by positivity : (0:ℝ) ≤ ‖z - y‖ + 1)
      nlinarith [norm_nonneg (z - y)]
    have h2 : δ / (2 * (‖z - y‖ + 1)) * (‖z - y‖ + 1) = δ / 2 := by field_simp
    linarith
  have h1 := hball hdist
  have h2 := me_conv f hf y z a c t ha hc ht0.le ht1
  rw [ha] at h1
  have h3 := h1.trans h2
  rw [← EReal.coe_add, EReal.coe_le_coe_iff, hwy, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos ht0] at h3
  have hεn : ε * ‖z - y‖ ≤ η / 2 := by
    rw [hε_def, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (z - y)]
  have h4 : t * (a + ⟪v, z - y⟫_ℝ - c - ε * ‖z - y‖) ≤ 0 := by nlinarith
  have h5 : a + ⟪v, z - y⟫_ℝ - c - ε * ‖z - y‖ ≤ 0 := by
    by_contra hc'
    push Not at hc'
    have := mul_pos ht0 hc'
    linarith
  linarith

open NonsmoothLojasiewicz.Convex in
/-- Critical points of a `Γ₀` function are the fixed points of its proximal map. -/
theorem me_crit_f {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : GammaZero f) (p : H → H) (hp : ∀ x, IsProx f x (p x)) (x : H) :
    x ∈ crit f ↔ x - p x = 0 := by
  obtain ⟨a1, ha1⟩ := mpc_prox_finite f hf x (p x) (hp x)
  constructor
  · intro hx
    simp only [crit, LimitingSubdiff, Set.mem_ofPred_eq] at hx
    obtain ⟨hxt, xs, vs, hxs, hfx, hvs, hreg⟩ := hx
    set a := (f x).toReal
    have ha : f x = (a : EReal) := me_real_of (hf.1 x) hxt
    have hmin : ∀ z (c : ℝ), f z = (c : EReal) → a ≤ c := by
      intro z c hc
      have hfin : ∀ t, f (xs t) = (((f (xs t)).toReal : ℝ) : EReal) :=
        fun t => me_real_of (hf.1 _) (hreg t).1
      have hlim : Tendsto (fun t => (f (xs t)).toReal) atTop (𝓝 a) := by
        rw [← EReal.tendsto_coe]
        rw [ha] at hfx
        exact hfx.congr hfin
      have hlim2 : Tendsto (fun t => (f (xs t)).toReal + ⟪vs t, z - xs t⟫_ℝ) atTop
          (𝓝 (a + ⟪(0 : H), z - x⟫_ℝ)) :=
        hlim.add (hvs.inner (tendsto_const_nhds.sub hxs))
      rw [inner_zero_left, add_zero] at hlim2
      exact le_of_tendsto' hlim2
        (fun t => me_reg_global f hf (xs t) (vs t) (hreg t) _ (hfin t) z c hc)
    have h1 := mpc_varineq f hf x (p x) a1 ha1 (hp x) x a ha
    have h2 := hmin (p x) a1 ha1
    have h3 : ⟪x - p x, x - p x⟫_ℝ ≤ 0 := by linarith
    rw [real_inner_self_nonpos] at h3
    exact h3
  · intro hx0
    have hpx : p x = x := (sub_eq_zero.mp hx0).symm
    have hprox := hp x
    rw [hpx] at hprox ha1
    simp only [crit, LimitingSubdiff, Set.mem_ofPred_eq]
    refine ⟨by rw [ha1]; exact EReal.coe_ne_top _, fun _ => x, fun _ => 0, tendsto_const_nhds,
      tendsto_const_nhds, tendsto_const_nhds,
      fun _ => ⟨by rw [ha1]; exact EReal.coe_ne_top _, fun ε hε => ?_⟩⟩
    filter_upwards [Metric.closedBall_mem_nhds x (by linarith : (0:ℝ) < 2 * ε)] with z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hq := hprox z
    rw [sub_self, norm_zero, ha1] at hq
    rw [ha1, inner_zero_left]
    by_cases hzt : f z = ⊤
    · rw [hzt]; exact le_top
    have hc := me_real_of (hf.1 z) hzt
    rw [hc] at hq ⊢
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hq
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    have : ‖z - x‖ ^ 2 / 2 ≤ ε * ‖z - x‖ := by nlinarith [norm_nonneg (z - x)]
    norm_num at hq
    linarith

open Filter Topology NonconvexSplitting.Shared MoreauProx.Characterization NonsmoothLojasiewicz.Convex in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : GammaZero f) :
    (∃ h : EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ x, moreauEnv f x = (h x : EReal)) ∧ ContDiff ℝ 1 h) ∧
      (∀ x, moreauEnv f x ≤ f x) ∧
      crit (moreauEnv f) = crit f ∧
      (⨅ x, f x) = (⨅ x, moreauEnv f x) := by
  choose p hp using me_prox_exists f hf
  have henv := me_env_eq f hf p hp
  have hu := me_upper f hf p hp
  have hl := me_lower f hf p hp
  have hGc : Continuous (fun x => x - p x) := continuous_id.sub (me_p_cont f hf p hp)
  have hle : ∀ x, moreauEnv f x ≤ f x := by
    intro x
    unfold moreauEnv
    refine (iInf_le _ x).trans (le_of_eq ?_)
    simp
  refine ⟨⟨fun x => (f (p x)).toReal + ‖x - p x‖ ^ 2 / 2, henv, ?_⟩, hle, ?_, ?_⟩
  · rw [contDiff_one_iff_hasFDerivAt]
    exact ⟨fun x => innerSL ℝ (x - p x), (innerSL ℝ).continuous.comp hGc,
      fun x => me_hasFDeriv (fun x => (f (p x)).toReal + ‖x - p x‖ ^ 2 / 2)
        (fun x => x - p x) hu hl x⟩
  · have hfun : moreauEnv f = fun x => ((((f (p x)).toReal + ‖x - p x‖ ^ 2 / 2 : ℝ)) : EReal) :=
      funext henv
    ext x
    rw [hfun, me_crit_smooth (fun x => (f (p x)).toReal + ‖x - p x‖ ^ 2 / 2)
      (fun x => x - p x) hGc hu hl x, me_crit_f f hf p hp x]
  · apply le_antisymm
    · refine le_iInf fun x => ?_
      unfold moreauEnv
      refine le_iInf fun u => (iInf_le _ u).trans ?_
      exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr (by positivity))
    · exact iInf_mono hle
