-- Prove2me | solution 1 for InfluencerAuth.Switch.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T18:34:41.299484+00:00
-- url     : https://prove2.me/submissions/83a787dd-5dd9-4b5f-bf82-716501049f35

import Mathlib
import Definitions.Def_InfluencerAuth_Switch_Model
import Definitions.Def_InfluencerAuth_Switch_ClosedForms

open MeasureTheory Set Filter Topology InfluencerAuth.Switch



namespace IASol

noncomputable def sig (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

lemma sig_pos (x : ℝ) : 0 < sig x := by
  unfold sig; positivity

lemma sig_lt_one (x : ℝ) : sig x < 1 := by
  unfold sig
  rw [div_lt_one (by positivity)]
  linarith [Real.exp_pos (-x)]

lemma one_sub_sig (x : ℝ) : 1 - sig x = Real.exp (-x) / (1 + Real.exp (-x)) := by
  unfold sig
  have : (0:ℝ) < 1 + Real.exp (-x) := by positivity
  field_simp
  ring

lemma hasDerivAt_sig (x : ℝ) : HasDerivAt sig (sig x * (1 - sig x)) x := by
  have h1 : HasDerivAt (fun x => 1 + Real.exp (-x)) (-Real.exp (-x)) x := by
    have := ((hasDerivAt_neg x).exp).const_add 1
    simpa using this
  have hne : (1 + Real.exp (-x)) ≠ 0 := by positivity
  have hs : sig = fun y => (1 + Real.exp (-y))⁻¹ := by
    funext y; simp [sig, one_div]
  have := h1.inv hne
  have key : sig x * (1 - sig x) = - -Real.exp (-x) / (1 + Real.exp (-x)) ^ 2 := by
    rw [one_sub_sig]; unfold sig; field_simp
  rw [key, hs]; exact this

lemma continuous_sig : Continuous sig := by
  unfold sig
  exact continuous_const.div (continuous_const.add (Real.continuous_exp.comp continuous_neg))
    (fun x => by positivity)

lemma sig_strictMono : StrictMono sig := by
  intro x y hxy
  unfold sig
  apply one_div_lt_one_div_of_lt (by positivity)
  have := Real.exp_lt_exp.mpr (neg_lt_neg hxy)
  linarith

lemma sig_logit {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : sig (Real.log (a / (1 - a))) = a := by
  unfold sig
  have h1 : 0 < 1 - a := by linarith
  rw [← Real.log_inv, Real.exp_log (by positivity)]
  field_simp
  ring

lemma exp_neg_logit {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Real.exp (-Real.log (a / (1 - a))) = (1 - a) / a := by
  have h1 : 0 < 1 - a := by linarith
  rw [← Real.log_inv, Real.exp_log (by positivity), inv_div]

/-- sig (x + a) ≤ exp a * sig x for a ≥ 0. -/
lemma sig_add_le (x : ℝ) {a : ℝ} (ha : 0 ≤ a) : sig (x + a) ≤ Real.exp a * sig x := by
  unfold sig
  have e1 := Real.exp_pos a
  have e2 := Real.exp_pos (-x)
  have e3 : Real.exp (-(x + a)) * Real.exp a = Real.exp (-x) := by
    rw [← Real.exp_add]; ring_nf
  rw [div_le_iff₀ (by positivity)]
  have : Real.exp a * (1 / (1 + Real.exp (-x))) * (1 + Real.exp (-(x + a)))
      = (Real.exp a + Real.exp (-x)) / (1 + Real.exp (-x)) := by
    field_simp; nlinarith [e3]
  rw [this, le_div_iff₀ (by positivity)]
  have : 1 ≤ Real.exp a := Real.one_le_exp ha
  linarith

/-- the ratio sig (x + a) / sig x is antitone in x (a ≥ 0). -/
lemma sig_ratio_anti {x y a : ℝ} (ha : 0 ≤ a) (hxy : x ≤ y) :
    sig (y + a) * sig x ≤ sig (x + a) * sig y := by
  unfold sig
  have p1 := Real.exp_pos (-x)
  have p2 := Real.exp_pos (-y)
  have p3 := Real.exp_pos (-(x + a))
  have p4 := Real.exp_pos (-(y + a))
  rw [div_mul_div_comm, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have hx : Real.exp (-(x + a)) = Real.exp (-x) * Real.exp (-a) := by
    rw [← Real.exp_add]; ring_nf
  have hy : Real.exp (-(y + a)) = Real.exp (-y) * Real.exp (-a) := by
    rw [← Real.exp_add]; ring_nf
  have hea : Real.exp (-a) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have hyx : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
  rw [hx, hy]
  nlinarith [mul_le_mul_of_nonneg_right hyx (sub_nonneg.mpr hea)]

end IASol



namespace IASol

lemma integrableOn_exp_mul_bdd {r : ℝ} (hr : 0 < r) {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0:ℝ)))) {M : ℝ}
    (hM : ∀ t ∈ Ioi (0:ℝ), |g t| ≤ M) :
    IntegrableOn (fun t => Real.exp (-r * t) * g t) (Ioi (0:ℝ)) := by
  have hi : IntegrableOn (fun t => M * Real.exp (-r * t)) (Ioi (0:ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 hr).const_mul M
  refine Integrable.mono' hi ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable.mul hg
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hM t ht) (Real.exp_pos _).le

lemma integral_exp_neg_Ioi_zero' {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0:ℝ), Real.exp (-r * t) = 1 / r := by
  rw [integral_exp_mul_Ioi (by linarith) 0]
  simp

noncomputable def cval (r c k L : ℝ) : ℝ :=
  ∫ t in Ioi (0:ℝ), Real.exp (-r * t) * (c * sig (L + k * t))

noncomputable def cder (r c k L : ℝ) : ℝ :=
  ∫ t in Ioi (0:ℝ), Real.exp (-r * t) * (c * (sig (L + k * t) * (1 - sig (L + k * t))))

lemma sig_mul_one_sub_nonneg (x : ℝ) : 0 ≤ sig x * (1 - sig x) :=
  mul_nonneg (sig_pos x).le (by linarith [sig_lt_one x])

lemma sig_mul_one_sub_le (x : ℝ) : sig x * (1 - sig x) ≤ 1 := by
  have := sig_pos x; have := sig_lt_one x; nlinarith

lemma cval_integrable {r : ℝ} (hr : 0 < r) (c k L : ℝ) :
    IntegrableOn (fun t => Real.exp (-r * t) * (c * sig (L + k * t))) (Ioi (0:ℝ)) := by
  refine integrableOn_exp_mul_bdd hr ?_ (M := |c|) ?_
  · exact (continuous_const.mul (continuous_sig.comp
      (continuous_const.add (continuous_const.mul continuous_id)))).aestronglyMeasurable
  · intro t _
    rw [abs_mul, abs_of_pos (sig_pos _)]
    exact mul_le_of_le_one_right (abs_nonneg c) (sig_lt_one _).le

lemma cder_integrable {r : ℝ} (hr : 0 < r) (c k L : ℝ) :
    IntegrableOn (fun t => Real.exp (-r * t) * (c * (sig (L + k * t) * (1 - sig (L + k * t)))))
      (Ioi (0:ℝ)) := by
  refine integrableOn_exp_mul_bdd hr ?_ (M := |c|) ?_
  · have hc : Continuous (fun t : ℝ => sig (L + k * t)) := continuous_sig.comp
      (continuous_const.add (continuous_const.mul continuous_id))
    exact (continuous_const.mul (hc.mul (continuous_const.sub hc))).aestronglyMeasurable
  · intro t _
    rw [abs_mul, abs_of_nonneg (sig_mul_one_sub_nonneg _)]
    exact mul_le_of_le_one_right (abs_nonneg c) (sig_mul_one_sub_le _)

lemma cval_hasDerivAt {r : ℝ} (hr : 0 < r) (c k L : ℝ) :
    HasDerivAt (cval r c k) (cder r c k L) L := by
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun L t => Real.exp (-r * t) * (c * sig (L + k * t)))
    (F' := fun L t => Real.exp (-r * t) * (c * (sig (L + k * t) * (1 - sig (L + k * t)))))
    (x₀ := L) (s := univ) (bound := fun t => Real.exp (-r * t) * |c|) univ_mem
    (Eventually.of_forall fun L' => ?_) (cval_integrable hr c k L) ?_ ?_ ?_ ?_
  · exact this.2
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable.mul
      (continuous_const.mul (continuous_sig.comp
      (continuous_const.add (continuous_const.mul continuous_id)))).aestronglyMeasurable
  · exact (cder_integrable hr c k L).aestronglyMeasurable
  · refine Eventually.of_forall fun t L' _ => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul,
      abs_of_nonneg (sig_mul_one_sub_nonneg _)]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (abs_nonneg c)
      (sig_mul_one_sub_le _)) (Real.exp_pos _).le
  · exact ((exp_neg_integrableOn_Ioi 0 hr).mul_const |c|)
  · refine Eventually.of_forall fun t L' _ => ?_
    have h1 : HasDerivAt (fun x => x + k * t) 1 L' := (hasDerivAt_id L').add_const _
    have h2 := (hasDerivAt_sig (L' + k * t)).comp L' h1
    have h3 := (h2.const_mul c).const_mul (Real.exp (-r * t))
    simpa using h3

lemma cval_ibp {r : ℝ} (hr : 0 < r) (c k L : ℝ) :
    k * cder r c k L = r * cval r c k L - c * sig L := by
  have hderiv : ∀ t ∈ Ici (0:ℝ), HasDerivAt (fun t => Real.exp (-r * t) * (c * sig (L + k * t)))
      (-r * (Real.exp (-r * t) * (c * sig (L + k * t))) +
        k * (Real.exp (-r * t) * (c * (sig (L + k * t) * (1 - sig (L + k * t)))))) t := by
    intro t _
    have e1 : HasDerivAt (fun t => Real.exp (-r * t)) (Real.exp (-r * t) * -r) t := by
      have := ((hasDerivAt_id t).const_mul (-r)).exp
      simpa using this
    have h1 : HasDerivAt (fun t => L + k * t) k t := by
      simpa using ((hasDerivAt_id t).const_mul k).const_add L
    have h2 := ((hasDerivAt_sig (L + k * t)).comp t h1).const_mul c
    have := e1.mul h2
    exact this.congr_deriv (by simp only [Function.comp_apply]; ring)
  have hint : IntegrableOn (fun t => -r * (Real.exp (-r * t) * (c * sig (L + k * t))) +
        k * (Real.exp (-r * t) * (c * (sig (L + k * t) * (1 - sig (L + k * t)))))) (Ioi 0) :=
    ((cval_integrable hr c k L).const_mul (-r)).add ((cder_integrable hr c k L).const_mul k)
  have htend : Tendsto (fun t => Real.exp (-r * t) * (c * sig (L + k * t))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun t => Real.exp (-r * t) * |c|) atTop (𝓝 0) := by
      have : Tendsto (fun t : ℝ => Real.exp (-r * t)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
      simpa using this.mul_const |c|
    refine squeeze_zero_norm (fun t => ?_) h0
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_of_pos (sig_pos _)]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (abs_nonneg c) (sig_lt_one _).le)
      (Real.exp_pos _).le
  have key := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rw [integral_add ((cval_integrable hr c k L).const_mul (-r))
    ((cder_integrable hr c k L).const_mul k), integral_const_mul, integral_const_mul] at key
  simp only [mul_zero, Real.exp_zero, one_mul, add_zero] at key
  unfold cval cder
  linarith

lemma cval_nonneg {r c : ℝ} (hc : 0 ≤ c) (k L : ℝ) : 0 ≤ cval r c k L := by
  unfold cval
  exact setIntegral_nonneg measurableSet_Ioi fun t _ =>
    mul_nonneg (Real.exp_pos _).le (mul_nonneg hc (sig_pos _).le)

lemma cder_nonneg {r c : ℝ} (hc : 0 ≤ c) (k L : ℝ) : 0 ≤ cder r c k L := by
  unfold cder
  exact setIntegral_nonneg measurableSet_Ioi fun t _ =>
    mul_nonneg (Real.exp_pos _).le (mul_nonneg hc (sig_mul_one_sub_nonneg _))

lemma cval_le {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) (k L : ℝ) : cval r c k L ≤ c / r := by
  unfold cval
  have : ∫ t in Ioi (0:ℝ), Real.exp (-r * t) * c = c / r := by
    rw [integral_mul_const, integral_exp_neg_Ioi_zero' hr]; ring
  rw [← this]
  refine setIntegral_mono_on (cval_integrable hr c k L)
    ((exp_neg_integrableOn_Ioi 0 hr).mul_const c) measurableSet_Ioi fun t _ => ?_
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hc (sig_lt_one _).le) (Real.exp_pos _).le

lemma cval_ge {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) {k : ℝ} (hk : 0 ≤ k) (L : ℝ) :
    c * sig L / r ≤ cval r c k L := by
  unfold cval
  have : ∫ t in Ioi (0:ℝ), Real.exp (-r * t) * (c * sig L) = c * sig L / r := by
    rw [integral_mul_const, integral_exp_neg_Ioi_zero' hr]; ring
  rw [← this]
  refine setIntegral_mono_on ((exp_neg_integrableOn_Ioi 0 hr).mul_const _)
    (cval_integrable hr c k L) measurableSet_Ioi fun t ht => ?_
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hc) (Real.exp_pos _).le
  exact sig_strictMono.monotone (by nlinarith [ht.out])

lemma cval_le_of_lt {r c k : ℝ} (hc : 0 ≤ c) (hk : 0 ≤ k) (hkr : k < r) (L : ℝ) :
    cval r c k L ≤ c * sig L / (r - k) := by
  have hr : 0 < r := by linarith
  unfold cval
  have : ∫ t in Ioi (0:ℝ), Real.exp (-(r - k) * t) * (c * sig L) = c * sig L / (r - k) := by
    rw [integral_mul_const, integral_exp_neg_Ioi_zero' (by linarith)]; ring
  rw [← this]
  refine setIntegral_mono_on (cval_integrable hr c k L)
    ((exp_neg_integrableOn_Ioi 0 (by linarith)).mul_const _) measurableSet_Ioi fun t ht => ?_
  have ht' : 0 ≤ k * t := mul_nonneg hk (le_of_lt ht)
  have h1 := sig_add_le L ht'
  have h2 : Real.exp (-(r - k) * t) = Real.exp (-r * t) * Real.exp (k * t) := by
    rw [← Real.exp_add]; ring_nf
  rw [h2, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  calc c * sig (L + k * t) ≤ c * (Real.exp (k * t) * sig L) := mul_le_mul_of_nonneg_left h1 hc
    _ = _ := by ring

lemma cder_le {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) {k : ℝ} (hk : 0 ≤ k) (L : ℝ) :
    cder r c k L ≤ (1 - sig L) * cval r c k L := by
  unfold cder cval
  rw [← integral_const_mul]
  refine setIntegral_mono_on (cder_integrable hr c k L)
    ((cval_integrable hr c k L).const_mul _) measurableSet_Ioi fun t ht => ?_
  have hm : sig L ≤ sig (L + k * t) := sig_strictMono.monotone (by nlinarith [ht.out])
  have := sig_pos (L + k * t)
  have := Real.exp_pos (-r * t)
  have : c * (sig (L + k * t) * (1 - sig (L + k * t))) ≤ (1 - sig L) * (c * sig (L + k * t)) := by
    nlinarith [mul_nonneg hc (sig_pos (L + k * t)).le]
  nlinarith

/-- ratio monotonicity: cval L' * sig L ≤ cval L * sig L' for L ≤ L'. -/
lemma cval_ratio_anti {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) {k : ℝ} (hk : 0 ≤ k) {L L' : ℝ}
    (hLL : L ≤ L') : cval r c k L' * sig L ≤ cval r c k L * sig L' := by
  unfold cval
  rw [← integral_mul_const, ← integral_mul_const]
  refine setIntegral_mono_on ((cval_integrable hr c k L').mul_const _)
    ((cval_integrable hr c k L).mul_const _) measurableSet_Ioi fun t ht => ?_
  have h := sig_ratio_anti (a := k * t) (mul_nonneg hk (le_of_lt ht)) hLL
  have := Real.exp_pos (-r * t)
  have h2 : Real.exp (-r * t) * (c * sig (L' + k * t)) * sig L
      = (Real.exp (-r * t) * c) * (sig (L' + k * t) * sig L) := by ring
  have h3 : Real.exp (-r * t) * (c * sig (L + k * t)) * sig L'
      = (Real.exp (-r * t) * c) * (sig (L + k * t) * sig L') := by ring
  rw [h2, h3]
  exact mul_le_mul_of_nonneg_left h (mul_nonneg this.le hc)

end IASol



namespace IASol

lemma intOn_of_bdd {f : ℝ → ℝ} {s : Set ℝ} (hsm : MeasurableSet s) (hs : volume s < ⊤)
    (hm : AEStronglyMeasurable f (volume.restrict s)) {M : ℝ} (hM : ∀ t ∈ s, |f t| ≤ M) :
    IntegrableOn f s := by
  refine Integrable.mono' (g := fun _ => M) ?_ hm ?_
  · exact integrableOn_const hs.ne
  · exact (ae_restrict_iff' hsm).mpr (Eventually.of_forall fun t ht => by
      rw [Real.norm_eq_abs]; exact hM t ht)

lemma ae_ne_pt (T : ℝ) : ∀ᵐ t : ℝ, t ≠ T := by
  simp [ae_iff, measure_singleton]

lemma measurable_ff {γ : ℝ} {S : Set ℝ} (hS : MeasurableSet S) :
    Measurable (followerFactor γ S) := by
  unfold followerFactor
  classical
  exact Measurable.ite hS measurable_const measurable_const

lemma measurable_pf {γ φ : ℝ} {S : Set ℝ} (hS : MeasurableSet S) :
    Measurable (profitFactor γ φ S) := by
  unfold profitFactor
  classical
  exact Measurable.ite hS measurable_const measurable_const

lemma ff_pos {γ : ℝ} (hγ0 : 0 < γ) (S : Set ℝ) (t : ℝ) : 0 < followerFactor γ S t := by
  unfold followerFactor; split_ifs <;> linarith

lemma ff_le_one {γ : ℝ} (hγ1 : γ < 1) (S : Set ℝ) (t : ℝ) : followerFactor γ S t ≤ 1 := by
  unfold followerFactor; split_ifs <;> linarith

lemma pf_nonneg {γ φ : ℝ} (hγ0 : 0 < γ) (hφ : 1 < φ) (S : Set ℝ) (t : ℝ) :
    0 ≤ profitFactor γ φ S t := by
  unfold profitFactor; split_ifs <;> nlinarith

lemma pf_le {γ φ : ℝ} (hγ0 : 0 < γ) (hφ : 1 < φ) (S : Set ℝ) (t : ℝ) :
    profitFactor γ φ S t ≤ γ * φ + 1 := by
  unfold profitFactor; split_ifs <;> nlinarith

section Path

variable {β γ A₀ : ℝ} {S : Set ℝ} {A : ℝ → ℝ}

/-- the drift -/
noncomputable def drift (β γ : ℝ) (S : Set ℝ) (A : ℝ → ℝ) (s : ℝ) : ℝ :=
  β * followerFactor γ S s * A s * (1 - A s)

lemma drift_nonneg (hβ : 0 < β) (hγ0 : 0 < γ) (hp : IsPath β γ A₀ S A) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ drift β γ S A s := by
  have h := hp.2.2.2.1 s hs
  unfold drift
  have := ff_pos hγ0 S s
  have : 0 ≤ 1 - A s := by linarith [h.2]
  have := h.1
  positivity

lemma drift_le (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : IsPath β γ A₀ S A) {s : ℝ}
    (hs : 0 ≤ s) : drift β γ S A s ≤ β * (1 - A s) := by
  have h := hp.2.2.2.1 s hs
  unfold drift
  have h1 := ff_pos hγ0 S s
  have h2 := ff_le_one hγ1 S s
  have h3 : 0 ≤ 1 - A s := by linarith [h.2]
  have h4 : followerFactor γ S s * A s ≤ 1 := by nlinarith [h.1, h.2]
  have : β * followerFactor γ S s * A s * (1 - A s) = β * (1 - A s) * (followerFactor γ S s * A s) := by ring
  rw [this]
  exact mul_le_of_le_one_right (by positivity) h4

lemma drift_abs_le (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : IsPath β γ A₀ S A) {s : ℝ}
    (hs : 0 ≤ s) : |drift β γ S A s| ≤ β := by
  rw [abs_of_nonneg (drift_nonneg hβ hγ0 hp hs)]
  have := drift_le hβ hγ0 hγ1 hp hs
  have := (hp.2.2.2.1 s hs).1
  nlinarith

lemma drift_aesm (hp : IsPath β γ A₀ S A) {a b : ℝ} (ha : 0 ≤ a) :
    AEStronglyMeasurable (drift β γ S A) (volume.restrict (Ioc a b)) := by
  have hc : ContinuousOn A (Ioc a b) :=
    hp.2.1.mono (fun t ht => le_trans ha (le_of_lt ht.1))
  have hA : AEStronglyMeasurable A (volume.restrict (Ioc a b)) :=
    hc.aestronglyMeasurable measurableSet_Ioc
  have hf : AEStronglyMeasurable (followerFactor γ S) (volume.restrict (Ioc a b)) :=
    (measurable_ff hp.1).aestronglyMeasurable
  unfold drift
  exact ((aestronglyMeasurable_const.mul hf).mul hA).mul (aestronglyMeasurable_const.sub hA)

lemma drift_intervalIntegrable (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : IsPath β γ A₀ S A)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable (drift β γ S A) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact intOn_of_bdd measurableSet_Ioc measure_Ioc_lt_top (drift_aesm hp ha)
    (fun t ht => drift_abs_le hβ hγ0 hγ1 hp (le_trans ha (le_of_lt ht.1)))

lemma path_eq (hp : IsPath β γ A₀ S A) {t : ℝ} (ht : 0 ≤ t) :
    A t = A₀ + ∫ s in (0:ℝ)..t, drift β γ S A s := hp.2.2.2.2 t ht

lemma path_sub (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : IsPath β γ A₀ S A) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) : A t - A s = ∫ u in s..t, drift β γ S A u := by
  rw [path_eq hp hs, path_eq hp (le_trans hs hst)]
  have h1 := drift_intervalIntegrable hβ hγ0 hγ1 hp le_rfl hs
  have h2 := drift_intervalIntegrable hβ hγ0 hγ1 hp hs hst
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  ring

lemma path_mono (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : IsPath β γ A₀ S A) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) : A s ≤ A t := by
  have := path_sub hβ hγ0 hγ1 hp hs hst
  have h2 : 0 ≤ ∫ u in s..t, drift β γ S A u :=
    intervalIntegral.integral_nonneg hst (fun u hu => drift_nonneg hβ hγ0 hp (le_trans hs hu.1))
  linarith

lemma path_ge (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : IsPath β γ A₀ S A) {t : ℝ}
    (ht : 0 ≤ t) : A₀ ≤ A t := by
  have := path_mono hβ hγ0 hγ1 hp le_rfl ht
  rwa [hp.2.2.1] at this

lemma path_lip (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : IsPath β γ A₀ S A) (T : ℝ) :
    LipschitzOnWith (Real.toNNReal β) A (Icc 0 T) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [Real.coe_toNNReal _ hβ.le, Real.dist_eq, Real.dist_eq]
  have key : ∀ s t : ℝ, 0 ≤ s → s ≤ t → |A t - A s| ≤ β * |t - s| := by
    intro s t hs hst
    rw [path_sub hβ hγ0 hγ1 hp hs hst]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t) (C := β)
      (f := drift β γ S A) (fun u hu => by
        rw [Real.norm_eq_abs]
        rw [uIoc_of_le hst] at hu
        exact drift_abs_le hβ hγ0 hγ1 hp (le_trans hs (le_of_lt hu.1)))
    simpa [Real.norm_eq_abs] using this
  rcases le_total x y with h | h
  · rw [abs_sub_comm, abs_sub_comm x y]; exact key x y hx.1 h
  · exact key y x hy.1 h

lemma path_ae_deriv (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : IsPath β γ A₀ S A) {T : ℝ}
    (hT : 0 ≤ T) : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt A (drift β γ S A t) t := by
  have hi := drift_intervalIntegrable hβ hγ0 hγ1 hp le_rfl hT
  filter_upwards [hi.ae_hasDerivAt_integral] with t ht htI
  have hmem : t ∈ uIcc 0 T := by rw [uIcc_of_le hT]; exact ⟨le_of_lt htI.1, le_of_lt htI.2⟩
  have h0 : (0:ℝ) ∈ uIcc 0 T := by rw [uIcc_of_le hT]; exact ⟨le_rfl, hT⟩
  have hd := (ht hmem 0 h0).const_add A₀
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds htI.1] with s hs
  exact path_eq hp (le_of_lt hs)

lemma path_ac (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : IsPath β γ A₀ S A) {T : ℝ}
    (hT : 0 ≤ T) : AbsolutelyContinuousOnInterval A 0 T := by
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := Real.toNNReal β)
  rw [uIcc_of_le hT]; exact path_lip hβ hγ0 hγ1 hp T

lemma exp_ac (c a b : ℝ) : AbsolutelyContinuousOnInterval (fun t => Real.exp (c * t)) a b := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  exact (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffOn

lemma path_lt_one (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : IsPath β γ A₀ S A)
    (hA1 : A₀ < 1) {T : ℝ} (hT : 0 ≤ T) : A T < 1 := by
  set h : ℝ → ℝ := fun t => Real.exp (β * t) * (1 - A t) with hh
  have h1A : AbsolutelyContinuousOnInterval (fun t => 1 - A t) 0 T := by
    have := (exp_ac 0 0 T).sub (path_ac hβ hγ0 hγ1 hp hT)
    have e : (fun t => 1 - A t) = (fun t => Real.exp (0 * t)) - A := by funext t; simp
    rw [e]; exact this
  have hac : AbsolutelyContinuousOnInterval h 0 T := (exp_ac β 0 T).mul h1A
  have hftc := hac.integral_deriv_eq_sub
  have hnn : 0 ≤ ∫ t in (0:ℝ)..T, deriv h t := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hT
    have h1 := path_ae_deriv hβ hγ0 hγ1 hp hT
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [h1, ae_ne_pt 0, ae_ne_pt T] with t ht h0 hTT htI
    have htI' : t ∈ Ioo 0 T := ⟨lt_of_le_of_ne htI.1 (Ne.symm h0), lt_of_le_of_ne htI.2 hTT⟩
    have hd : HasDerivAt h (Real.exp (β * t) * β * (1 - A t) +
        Real.exp (β * t) * (-drift β γ S A t)) t := by
      have e1 : HasDerivAt (fun t => Real.exp (β * t)) (Real.exp (β * t) * β) t := by
        simpa using ((hasDerivAt_id t).const_mul β).exp
      exact e1.mul ((ht htI').const_sub 1)
    rw [hd.deriv]
    have := drift_le hβ hγ0 hγ1 hp (le_of_lt htI'.1)
    have := Real.exp_pos (β * t)
    simp only [Pi.zero_apply]
    nlinarith
  rw [hftc] at hnn
  simp only [hh, mul_zero, Real.exp_zero, one_mul, hp.2.2.1] at hnn
  have : 0 < Real.exp (β * T) * (1 - A T) := by linarith
  have := (pos_iff_pos_of_mul_pos this).mp (Real.exp_pos _)
  linarith

end Path

end IASol



namespace IASol

noncomputable def logit (a : ℝ) : ℝ := Real.log (a / (1 - a))

lemma sig_logit' {a : ℝ} (h0 : 0 < a) (h1 : a < 1) : sig (logit a) = a := sig_logit h0 h1

lemma hasDerivAt_logit {a : ℝ} (h0 : 0 < a) (h1 : a < 1) :
    HasDerivAt logit (1 / (a * (1 - a))) a := by
  have h1' : 0 < 1 - a := by linarith
  have d1 := Real.hasDerivAt_log h0.ne'
  have d2 : HasDerivAt (fun x => Real.log (1 - x)) ((1 - a)⁻¹ * (-1)) a := by
    exact (Real.hasDerivAt_log h1'.ne').comp a ((hasDerivAt_id' (x := a)).const_sub 1)
  have d := d1.sub d2
  have heq : (fun x => Real.log x - Real.log (1 - x)) =ᶠ[𝓝 a] logit := by
    filter_upwards [Ioo_mem_nhds h0 h1] with x hx
    unfold logit
    rw [Real.log_div hx.1.ne' (by linarith [hx.2])]
  refine (d.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  field_simp
  ring

lemma logit_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) : logit a ≤ logit b := by
  unfold logit
  apply Real.log_le_log (by apply div_pos ha; linarith)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

section Verif

variable {β γ φ r A₀ : ℝ} {S : Set ℝ} {A : ℝ → ℝ}

lemma verif_core (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hp : IsPath β γ A₀ S A) (hA0 : 0 < A₀) (hA1 : A₀ < 1)
    {G G' : ℝ → ℝ} (hG : ∀ x, HasDerivAt G (G' x) x)
    (hG'b : ∀ a b, ∃ K, ∀ x ∈ Icc a b, |G' x| ≤ K) {T : ℝ} (hT : 0 ≤ T) :
    ∃ D : ℝ → ℝ, IntervalIntegrable D volume 0 T ∧
      (∫ t in (0:ℝ)..T, D t) = G (logit A₀) - Real.exp (-r * T) * G (logit (A T)) ∧
      ∀ᵐ t, t ∈ Ioo 0 T → D t = Real.exp (-r * t) *
        (r * G (logit (A t)) - β * followerFactor γ S t * G' (logit (A t))) := by
  set a1 := A T with ha1def
  have ha1 : a1 < 1 := path_lt_one hβ hγ0 hγ1 hp hA1 hT
  have hA0a1 : A₀ ≤ a1 := path_ge hβ hγ0 hγ1 hp hT
  set Φ : ℝ → ℝ := fun a => G (logit a) with hΦ
  obtain ⟨K, hK⟩ := hG'b (logit A₀) (logit a1)
  have hKnn : 0 ≤ max K 0 := le_max_right _ _
  set C : ℝ := max K 0 * (1 / (A₀ * (1 - a1))) with hC
  have hΦd : ∀ a ∈ Icc A₀ a1, HasDerivAt Φ (G' (logit a) * (1 / (a * (1 - a)))) a := by
    intro a ha
    have h0 : 0 < a := lt_of_lt_of_le hA0 ha.1
    have h1 : a < 1 := lt_of_le_of_lt ha.2 ha1
    exact (hG (logit a)).comp a (hasDerivAt_logit h0 h1)
  have hΦlip : LipschitzOnWith (Real.toNNReal C) Φ (Icc A₀ a1) := by
    refine Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Icc _ _)
      (fun a ha => (hΦd a ha).hasDerivWithinAt) (fun a ha => ?_)
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity), Real.norm_eq_abs]
    have h0 : 0 < a := lt_of_lt_of_le hA0 ha.1
    have h1 : a < 1 := lt_of_le_of_lt ha.2 ha1
    have hlo : logit A₀ ≤ logit a := logit_mono hA0 ha.1 h1
    have hhi : logit a ≤ logit a1 := logit_mono h0 ha.2 ha1
    have hk := hK (logit a) ⟨hlo, hhi⟩
    have hpa : (0:ℝ) < 1 / (a * (1 - a)) := by apply div_pos one_pos; nlinarith
    rw [abs_mul, abs_of_pos hpa]
    have hden : A₀ * (1 - a1) ≤ a * (1 - a) := by
      apply mul_le_mul ha.1 (by linarith [ha.2]) (by linarith) h0.le
    have hpos : 0 < A₀ * (1 - a1) := by apply mul_pos hA0; linarith
    have : 1 / (a * (1 - a)) ≤ 1 / (A₀ * (1 - a1)) := one_div_le_one_div_of_le hpos hden
    exact mul_le_mul (le_trans hk (le_max_left _ _)) this (by positivity) hKnn
  have hAmaps : MapsTo A (Icc 0 T) (Icc A₀ a1) := fun t ht =>
    ⟨path_ge hβ hγ0 hγ1 hp ht.1, path_mono hβ hγ0 hγ1 hp ht.1 ht.2⟩
  have hcomp : LipschitzOnWith _ (Φ ∘ A) (Icc 0 T) :=
    hΦlip.comp (path_lip hβ hγ0 hγ1 hp T) hAmaps
  have hacΦ : AbsolutelyContinuousOnInterval (Φ ∘ A) 0 T := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    rw [uIcc_of_le hT]; exact hcomp
  set h : ℝ → ℝ := fun t => Real.exp (-r * t) * Φ (A t) with hh
  have hac : AbsolutelyContinuousOnInterval h 0 T := (exp_ac (-r) 0 T).mul hacΦ
  refine ⟨fun t => -deriv h t, hac.intervalIntegrable_deriv.neg, ?_, ?_⟩
  · rw [intervalIntegral.integral_neg, hac.integral_deriv_eq_sub]
    simp only [hh, hΦ, mul_zero, Real.exp_zero, one_mul, hp.2.2.1]
    ring
  · filter_upwards [path_ae_deriv hβ hγ0 hγ1 hp hT] with t ht htI
    have hAt := ht htI
    have hm : A t ∈ Icc A₀ a1 := hAmaps ⟨le_of_lt htI.1, le_of_lt htI.2⟩
    have h0 : 0 < A t := lt_of_lt_of_le hA0 hm.1
    have h1 : A t < 1 := lt_of_le_of_lt hm.2 ha1
    have hd1 := (hΦd (A t) hm).comp t hAt
    have e1 : HasDerivAt (fun t => Real.exp (-r * t)) (Real.exp (-r * t) * -r) t := by
      simpa using ((hasDerivAt_id t).const_mul (-r)).exp
    have hd := e1.mul hd1
    have : deriv h t = _ := hd.deriv
    rw [this]
    simp only [Function.comp_apply, hΦ]
    unfold drift
    have hne : (1 - A t) ≠ 0 := by linarith
    field_simp
    ring

lemma dp_integrable (hr : 0 < r) (hγ0 : 0 < γ) (hφ : 1 < φ) (hp : IsPath β γ A₀ S A) :
    IntegrableOn (fun t => Real.exp (-r * t) * profitFactor γ φ S t * A t) (Ioi 0) := by
  have : (fun t => Real.exp (-r * t) * profitFactor γ φ S t * A t) =
      (fun t => Real.exp (-r * t) * (profitFactor γ φ S t * A t)) := by
    funext t; ring
  rw [this]
  refine integrableOn_exp_mul_bdd hr ?_ (M := γ * φ + 1) ?_
  · have hA : AEStronglyMeasurable A (volume.restrict (Ioi 0)) :=
      (hp.2.1.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
    exact (measurable_pf hp.1).aestronglyMeasurable.mul hA
  · intro t ht
    have hA := hp.2.2.2.1 t (le_of_lt ht)
    rw [abs_mul, abs_of_nonneg (pf_nonneg hγ0 hφ S t), abs_of_nonneg hA.1]
    have := pf_le hγ0 hφ S t
    have := pf_nonneg hγ0 hφ S t
    nlinarith [hA.2]

lemma dp_intervalIntegrable (hr : 0 < r) (hγ0 : 0 < γ) (hφ : 1 < φ) (hp : IsPath β γ A₀ S A)
    {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => Real.exp (-r * t) * profitFactor γ φ S t * A t) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  exact (dp_integrable hr hγ0 hφ hp).mono_set Ioc_subset_Ioi_self

lemma dp_tendsto (hr : 0 < r) (hγ0 : 0 < γ) (hφ : 1 < φ) (hp : IsPath β γ A₀ S A) :
    Tendsto (fun T => ∫ t in (0:ℝ)..T, Real.exp (-r * t) * profitFactor γ φ S t * A t) atTop
      (𝓝 (discountedProfit γ φ r S A)) :=
  intervalIntegral_tendsto_integral_Ioi 0 (dp_integrable hr hγ0 hφ hp) tendsto_id

lemma exp_tendsto_zero (hr : 0 < r) (M : ℝ) :
    Tendsto (fun T : ℝ => Real.exp (-r * T) * M) atTop (𝓝 0) := by
  have : Tendsto (fun t : ℝ => Real.exp (-r * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  simpa using this.mul_const M

theorem verif_le (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hφ : 1 < φ) (hr : 0 < r)
    (hp : IsPath β γ A₀ S A) (hA0 : 0 < A₀) (hA1 : A₀ < 1)
    {G G' : ℝ → ℝ} (hG : ∀ x, HasDerivAt G (G' x) x)
    (hG'b : ∀ a b, ∃ K, ∀ x ∈ Icc a b, |G' x| ≤ K)
    (hGb : ∃ M, ∀ x, logit A₀ ≤ x → |G x| ≤ M)
    (hHJB : ∀ x, sig x + β * G' x ≤ r * G x ∧ γ * φ * sig x + γ * β * G' x ≤ r * G x) :
    discountedProfit γ φ r S A ≤ G (logit A₀) := by
  obtain ⟨M, hM⟩ := hGb
  have hlim : Tendsto (fun T : ℝ => G (logit A₀) + Real.exp (-r * T) * M) atTop
      (𝓝 (G (logit A₀))) := by
    simpa using (exp_tendsto_zero hr M).const_add (G (logit A₀))
  refine le_of_tendsto_of_tendsto (dp_tendsto hr hγ0 hφ hp) hlim ?_
  filter_upwards [eventually_ge_atTop 0] with T hT
  obtain ⟨D, hDi, hDint, hDae⟩ := verif_core (r := r) hβ hγ0 hγ1 hp hA0 hA1 hG hG'b hT
  have h1 : (∫ t in (0:ℝ)..T, Real.exp (-r * t) * profitFactor γ φ S t * A t) ≤
      ∫ t in (0:ℝ)..T, D t := by
    apply intervalIntegral.integral_mono_ae_restrict hT (dp_intervalIntegrable hr hγ0 hφ hp hT) hDi
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hDae, ae_ne_pt 0, ae_ne_pt T] with t ht h0 hTT htI
    have htI' : t ∈ Ioo 0 T := ⟨lt_of_le_of_ne htI.1 (Ne.symm h0), lt_of_le_of_ne htI.2 hTT⟩
    rw [ht htI']
    have hm0 : A₀ ≤ A t := path_ge hβ hγ0 hγ1 hp htI.1
    have hm1 : A t < 1 := path_lt_one hβ hγ0 hγ1 hp hA1 htI.1
    have hs : sig (logit (A t)) = A t := sig_logit' (by linarith) hm1
    obtain ⟨H1, H2⟩ := hHJB (logit (A t))
    rw [hs] at H1 H2
    have he := Real.exp_pos (-r * t)
    unfold profitFactor followerFactor
    split_ifs
    · rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ he.le; linarith
    · rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ he.le; linarith
  have hm0 : A₀ ≤ A T := path_ge hβ hγ0 hγ1 hp hT
  have hb := hM (logit (A T)) (logit_mono hA0 hm0 (path_lt_one hβ hγ0 hγ1 hp hA1 hT))
  have he := Real.exp_pos (-r * T)
  have : -(Real.exp (-r * T) * G (logit (A T))) ≤ Real.exp (-r * T) * M := by
    rw [← mul_neg]; apply mul_le_mul_of_nonneg_left _ he.le
    linarith [neg_abs_le (G (logit (A T)))]
  linarith

theorem verif_eq (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hφ : 1 < φ) (hr : 0 < r)
    (hp : IsPath β γ A₀ S A) (hA0 : 0 < A₀) (hA1 : A₀ < 1)
    {G G' : ℝ → ℝ} (hG : ∀ x, HasDerivAt G (G' x) x)
    (hG'b : ∀ a b, ∃ K, ∀ x ∈ Icc a b, |G' x| ≤ K)
    (hGb : ∃ M, ∀ x, logit A₀ ≤ x → |G x| ≤ M) (τ : ℝ)
    (hEq : ∀ t, 0 < t → t ≠ τ → profitFactor γ φ S t * A t =
      r * G (logit (A t)) - β * followerFactor γ S t * G' (logit (A t))) :
    discountedProfit γ φ r S A = G (logit A₀) := by
  obtain ⟨M, hM⟩ := hGb
  refine tendsto_nhds_unique (dp_tendsto hr hγ0 hφ hp) ?_
  have hlim : Tendsto (fun T : ℝ => G (logit A₀) - Real.exp (-r * T) * G (logit (A T))) atTop
      (𝓝 (G (logit A₀))) := by
    have h0 : Tendsto (fun T : ℝ => Real.exp (-r * T) * G (logit (A T))) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (exp_tendsto_zero hr M)
      filter_upwards [eventually_ge_atTop 0] with T hT
      have hm0 : A₀ ≤ A T := path_ge hβ hγ0 hγ1 hp hT
      have hb := hM (logit (A T)) (logit_mono hA0 hm0 (path_lt_one hβ hγ0 hγ1 hp hA1 hT))
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    simpa using h0.const_sub (G (logit A₀))
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with T hT
  obtain ⟨D, hDi, hDint, hDae⟩ := verif_core (r := r) hβ hγ0 hγ1 hp hA0 hA1 hG hG'b hT
  rw [← hDint]
  apply intervalIntegral.integral_congr_ae
  rw [uIoc_of_le hT]
  filter_upwards [hDae, ae_ne_pt T, ae_ne_pt τ] with t ht hTT hτ htI
  have htI' : t ∈ Ioo 0 T := ⟨htI.1, lt_of_le_of_ne htI.2 hTT⟩
  have := hEq t htI.1 hτ
  rw [ht htI', mul_assoc (Real.exp (-r * t)), this]

end Verif

end IASol



namespace IASol

lemma logit_sig (x : ℝ) : logit (sig x) = x := by
  unfold logit
  rw [one_sub_sig]
  unfold sig
  have : (1 / (1 + Real.exp (-x))) / (Real.exp (-x) / (1 + Real.exp (-x))) = Real.exp x := by
    have h1 : (0:ℝ) < 1 + Real.exp (-x) := by positivity
    rw [Real.exp_neg]
    field_simp
  rw [this, Real.log_exp]

section SigPath

variable {β γ A₀ : ℝ} {S : Set ℝ}

lemma sig_drift_ii (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hS : MeasurableSet S) {ℓ : ℝ → ℝ}
    (hℓc : Continuous ℓ) (a b : ℝ) :
    IntervalIntegrable (drift β γ S (fun t => sig (ℓ t))) volume a b := by
  have hA : Continuous (fun t => sig (ℓ t)) := continuous_sig.comp hℓc
  refine IntervalIntegrable.mono_fun' (g := fun _ => β) intervalIntegrable_const ?_ ?_
  · unfold drift
    exact (((aestronglyMeasurable_const.mul (measurable_ff hS).aestronglyMeasurable).mul
      hA.aestronglyMeasurable).mul (aestronglyMeasurable_const.sub hA.aestronglyMeasurable))
  · refine Eventually.of_forall fun t => ?_
    unfold drift
    simp only [Real.norm_eq_abs]
    have h1 := ff_pos hγ0 S t
    have h2 := ff_le_one hγ1 S t
    have h3 := sig_pos (ℓ t)
    have h4 := sig_lt_one (ℓ t)
    have hnn : 0 ≤ β * followerFactor γ S t * sig (ℓ t) * (1 - sig (ℓ t)) := by
      have : 0 ≤ 1 - sig (ℓ t) := by linarith
      positivity
    rw [abs_of_nonneg hnn]
    have : followerFactor γ S t * (sig (ℓ t) * (1 - sig (ℓ t))) ≤ 1 := by
      have := sig_mul_one_sub_le (ℓ t)
      have := sig_mul_one_sub_nonneg (ℓ t)
      nlinarith
    nlinarith

lemma sig_path_piece (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hS : MeasurableSet S)
    {ℓ : ℝ → ℝ} (hℓc : Continuous ℓ) (τ : ℝ)
    (hd : ∀ t, 0 < t → t ≠ τ → HasDerivAt ℓ (β * followerFactor γ S t) t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hτ : τ ∉ Ioo a b) :
    sig (ℓ b) - sig (ℓ a) = ∫ s in a..b, drift β γ S (fun t => sig (ℓ t)) s := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (continuous_sig.comp hℓc).continuousOn
  · intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt ha hx.1
    have hxτ : x ≠ τ := fun h => hτ (h ▸ hx)
    have := (hasDerivAt_sig (ℓ x)).comp x (hd x hx0 hxτ)
    exact this.congr_deriv (by unfold drift; ring)
  · exact sig_drift_ii hβ hγ0 hγ1 hS hℓc a b

lemma sig_path (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hS : MeasurableSet S)
    (hA0 : 0 < A₀) (hA1 : A₀ < 1)
    {ℓ : ℝ → ℝ} (hℓc : Continuous ℓ) (hℓ0 : ℓ 0 = logit A₀) (τ : ℝ)
    (hd : ∀ t, 0 < t → t ≠ τ → HasDerivAt ℓ (β * followerFactor γ S t) t) :
    IsPath β γ A₀ S (fun t => sig (ℓ t)) := by
  refine ⟨hS, (continuous_sig.comp hℓc).continuousOn, ?_, ?_, ?_⟩
  · simp only [hℓ0]; exact sig_logit' hA0 hA1
  · intro t _; exact ⟨(sig_pos _).le, (sig_lt_one _).le⟩
  · intro t ht
    show sig (ℓ t) = A₀ + ∫ s in (0:ℝ)..t, drift β γ S (fun t => sig (ℓ t)) s
    have h0 : sig (ℓ 0) = A₀ := by rw [hℓ0]; exact sig_logit' hA0 hA1
    by_cases hτ : τ ∈ Ioo 0 t
    · have e1 := sig_path_piece hβ hγ0 hγ1 hS hℓc τ hd le_rfl hτ.1.le
        (fun h => lt_irrefl τ h.2)
      have e2 := sig_path_piece hβ hγ0 hγ1 hS hℓc τ hd hτ.1.le hτ.2.le
        (fun h => lt_irrefl τ h.1)
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (sig_drift_ii hβ hγ0 hγ1 hS hℓc 0 τ) (sig_drift_ii hβ hγ0 hγ1 hS hℓc τ t)]
      linarith
    · have := sig_path_piece hβ hγ0 hγ1 hS hℓc τ hd le_rfl ht hτ
      linarith

end SigPath

section Parts

variable {β γ φ r : ℝ}

lemma ff_empty (γ t : ℝ) : followerFactor γ ∅ t = 1 := by simp [followerFactor]
lemma pf_empty (γ φ t : ℝ) : profitFactor γ φ ∅ t = 1 := by simp [profitFactor]
lemma ff_univ (γ t : ℝ) : followerFactor γ univ t = γ := by simp [followerFactor]
lemma pf_univ (γ φ t : ℝ) : profitFactor γ φ univ t = γ * φ := by simp [profitFactor]

/-- linear logit path -/
lemma lin_hasDerivAt (L k t : ℝ) : HasDerivAt (fun t => L + k * t) k t := by
  simpa using ((hasDerivAt_id t).const_mul k).const_add L

theorem part1 (hγ0 : 0 < γ) (hγ1 : γ < 1) (hφ : 1 < φ) (hβ : 0 < β) (hr : 0 < r)
    (hγφ : γ * φ ≤ 1) (A₀ : ℝ) (hA0 : 0 < A₀) (hA1 : A₀ < 1) :
    ∃ A : ℝ → ℝ, IsOptimalFrom β γ φ r A₀ ∅ A := by
  set G := cval r 1 β
  set G' := cder r 1 β
  have hG : ∀ x, HasDerivAt G (G' x) x := fun x => cval_hasDerivAt hr 1 β x
  have hibp : ∀ x, β * G' x = r * G x - sig x := fun x => by
    have := cval_ibp hr 1 β x; simpa using this
  have hG'b : ∀ a b, ∃ K, ∀ x ∈ Icc a b, |G' x| ≤ K := by
    intro a b; refine ⟨1 / β, fun x _ => ?_⟩
    have h1 := cder_nonneg (r := r) zero_le_one β x
    have h2 := cval_le hr zero_le_one β x
    have h3 := hibp x
    have h4 := sig_pos x
    rw [abs_of_nonneg h1, le_div_iff₀ hβ]
    have : r * G x ≤ 1 := by
      have : r * G x ≤ r * (1 / r) := mul_le_mul_of_nonneg_left h2 hr.le
      rwa [mul_one_div_cancel hr.ne'] at this
    nlinarith
  have hGb : ∃ M, ∀ x, logit A₀ ≤ x → |G x| ≤ M := ⟨1 / r, fun x _ => by
    rw [abs_of_nonneg (cval_nonneg zero_le_one β x)]; exact cval_le hr zero_le_one β x⟩
  have hHJB : ∀ x, sig x + β * G' x ≤ r * G x ∧ γ * φ * sig x + γ * β * G' x ≤ r * G x := by
    intro x
    have h1 := hibp x
    have h2 := cval_ge hr zero_le_one hβ.le x
    have h3 := sig_pos x
    refine ⟨by linarith, ?_⟩
    have h4 : sig x ≤ r * G x := by
      have := mul_le_mul_of_nonneg_left h2 hr.le
      rwa [mul_div_cancel₀ _ hr.ne', one_mul] at this
    have : γ * β * G' x = γ * (r * G x - sig x) := by rw [mul_assoc, h1]
    rw [this]
    nlinarith
  set ℓ : ℝ → ℝ := fun t => logit A₀ + β * 1 * t
  have hpath : IsPath β γ A₀ ∅ (fun t => sig (ℓ t)) := by
    refine sig_path hβ hγ0 hγ1 MeasurableSet.empty hA0 hA1 (by fun_prop) (by simp [ℓ]) 0 ?_
    intro t _ _
    rw [ff_empty]; exact lin_hasDerivAt _ _ t
  refine ⟨_, hpath, fun S' A' hp' => ?_⟩
  rw [verif_eq hβ hγ0 hγ1 hφ hr hpath hA0 hA1 hG hG'b hGb 0 (fun t _ _ => ?_)]
  · exact verif_le hβ hγ0 hγ1 hφ hr hp' hA0 hA1 hG hG'b hGb hHJB
  · simp only [ff_empty, pf_empty, logit_sig]
    have := hibp (ℓ t)
    linarith

theorem part2 (hγ0 : 0 < γ) (hγ1 : γ < 1) (hφ : 1 < φ) (hβ : 0 < β) (hr : 0 < r)
    (hγφ : 1 < γ * φ) (hC : ¬ Condition1 γ φ β r) (A₀ : ℝ) (hA0 : 0 < A₀) (hA1 : A₀ < 1) :
    ∃ A : ℝ → ℝ, IsOptimalFrom β γ φ r A₀ univ A := by
  unfold Condition1 at hC
  push Not at hC
  obtain ⟨hlt, hle⟩ := hC
  have hd : 0 < r - γ * β := by linarith
  have hc : 0 ≤ γ * φ := by positivity
  have hk : 0 ≤ γ * β := by positivity
  have hkey : (β - γ * β) * (γ * φ) ≤ (γ * φ - 1) * (r - γ * β) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hd] at hle; linarith
  set G := cval r (γ * φ) (γ * β)
  set G' := cder r (γ * φ) (γ * β)
  have hG : ∀ x, HasDerivAt G (G' x) x := fun x => cval_hasDerivAt hr _ _ x
  have hibp : ∀ x, γ * β * G' x = r * G x - γ * φ * sig x := fun x => cval_ibp hr _ _ x
  have hG'b : ∀ a b, ∃ K, ∀ x ∈ Icc a b, |G' x| ≤ K := by
    intro a b; refine ⟨φ / β, fun x _ => ?_⟩
    have h1 := cder_nonneg (r := r) hc (γ * β) x
    have h2 := cval_le hr hc (γ * β) x
    have h3 := hibp x
    have h4 := sig_pos x
    rw [abs_of_nonneg h1, le_div_iff₀ hβ]
    have : r * G x ≤ γ * φ := by
      have : r * G x ≤ r * (γ * φ / r) := mul_le_mul_of_nonneg_left h2 hr.le
      rwa [mul_div_cancel₀ _ hr.ne'] at this
    have : γ * (G' x * β) ≤ γ * φ := by nlinarith
    nlinarith
  have hGb : ∃ M, ∀ x, logit A₀ ≤ x → |G x| ≤ M := ⟨γ * φ / r, fun x _ => by
    rw [abs_of_nonneg (cval_nonneg hc _ x)]; exact cval_le hr hc _ x⟩
  have hHJB : ∀ x, sig x + β * G' x ≤ r * G x ∧ γ * φ * sig x + γ * β * G' x ≤ r * G x := by
    intro x
    have h1 := hibp x
    have h2 := cval_le_of_lt hc hk hlt x
    have h3 := sig_pos x
    refine ⟨?_, by linarith⟩
    -- need (1-γ) r G ≤ γ (φ-1) sig
    have hG2 : (r - γ * β) * G x ≤ γ * φ * sig x := by
      rw [le_div_iff₀ hd] at h2; linarith
    have hGn := cval_nonneg (r := r) hc (γ * β) x
    have e : γ * (sig x + β * G' x) = γ * sig x + (r * G x - γ * φ * sig x) := by
      rw [← h1]; ring
    have : (1 - γ) * r * G x ≤ γ * (φ - 1) * sig x := by
      -- (1-γ) r γφ ≤ γ(φ-1)(r - γβ)
      have hh : (1 - γ) * r * (γ * φ) ≤ γ * (φ - 1) * (r - γ * β) := by nlinarith
      have : (1 - γ) * r * G x * (r - γ * β) ≤ γ * (φ - 1) * sig x * (r - γ * β) := by
        calc (1 - γ) * r * G x * (r - γ * β) = (1 - γ) * r * ((r - γ * β) * G x) := by ring
          _ ≤ (1 - γ) * r * (γ * φ * sig x) := by
            apply mul_le_mul_of_nonneg_left hG2; nlinarith
          _ = (1 - γ) * r * (γ * φ) * sig x := by ring
          _ ≤ γ * (φ - 1) * (r - γ * β) * sig x := mul_le_mul_of_nonneg_right hh h3.le
          _ = _ := by ring
      exact le_of_mul_le_mul_right this hd
    nlinarith
  set ℓ : ℝ → ℝ := fun t => logit A₀ + β * γ * t
  have hpath : IsPath β γ A₀ univ (fun t => sig (ℓ t)) := by
    refine sig_path hβ hγ0 hγ1 MeasurableSet.univ hA0 hA1 (by fun_prop) (by simp [ℓ]) 0 ?_
    intro t _ _
    rw [ff_univ]; exact lin_hasDerivAt _ _ t
  refine ⟨_, hpath, fun S' A' hp' => ?_⟩
  rw [verif_eq hβ hγ0 hγ1 hφ hr hpath hA0 hA1 hG hG'b hGb 0 (fun t _ _ => ?_)]
  · exact verif_le hβ hγ0 hγ1 hφ hr hp' hA0 hA1 hG hG'b hGb hHJB
  · simp only [ff_univ, pf_univ, logit_sig]
    have := hibp (ℓ t)
    linarith

end Parts

end IASol



namespace IASol

noncomputable def kap (γ φ r : ℝ) : ℝ := γ * (φ - 1) / ((1 - γ) * r)

lemma kap_spec {γ φ r : ℝ} (hγ1 : γ < 1) (hr : 0 < r) : (1 - γ) * r * kap γ φ r = γ * (φ - 1) := by
  unfold kap
  have h1 : 1 - γ ≠ 0 := by linarith
  have h2 : r ≠ 0 := by linarith
  field_simp

lemma kap_pos {γ φ r : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hφ : 1 < φ) (hr : 0 < r) :
    0 < kap γ φ r := by
  unfold kap
  apply div_pos (mul_pos hγ0 (by linarith)) (mul_pos (by linarith) hr)

lemma exp_integral {δ : ℝ} (hδ : δ ≠ 0) (T : ℝ) :
    ∫ t in (0:ℝ)..T, Real.exp (-δ * t) = (1 - Real.exp (-δ * T)) / δ := by
  have hd : ∀ x ∈ uIcc (0:ℝ) T, HasDerivAt (fun t => -Real.exp (-δ * t) / δ)
      (Real.exp (-δ * x)) x := by
    intro x _
    have := (((hasDerivAt_id x).const_mul (-δ)).exp.neg).div_const δ
    refine this.congr_deriv ?_
    field_simp
    simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp
  ring

lemma lower_trunc {r c k : ℝ} (hr : 0 < r) (hc : 0 ≤ c) (hk : 0 ≤ k) {θ T L : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hT : 0 ≤ T)
    (hL : Real.exp (k * T) ≤ (1 - θ) * Real.exp (-L)) :
    θ * c * sig L * (∫ t in (0:ℝ)..T, Real.exp (-(r - k) * t)) ≤ cval r c k L := by
  have hf : IntegrableOn (fun t => Real.exp (-r * t) * (c * sig (L + k * t))) (Ioi 0) :=
    cval_integrable hr c k L
  have h1 : (∫ t in (0:ℝ)..T, Real.exp (-r * t) * (c * sig (L + k * t))) ≤ cval r c k L := by
    rw [intervalIntegral.integral_of_le hT]
    unfold cval
    refine setIntegral_mono_set hf ?_ Ioc_subset_Ioi_self.eventuallyLE
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t _ =>
      mul_nonneg (Real.exp_pos _).le (mul_nonneg hc (sig_pos _).le))
  refine le_trans ?_ h1
  rw [← intervalIntegral.integral_const_mul]
  have hcont1 : Continuous (fun t => θ * c * sig L * Real.exp (-(r - k) * t)) := by fun_prop
  have hcont2 : Continuous (fun t => Real.exp (-r * t) * (c * sig (L + k * t))) := by
    have := continuous_sig
    fun_prop
  refine intervalIntegral.integral_mono_on hT (hcont1.intervalIntegrable _ _)
    (hcont2.intervalIntegrable _ _) fun t ht => ?_
  have hkey : θ * Real.exp (k * t) * sig L ≤ sig (L + k * t) := by
    unfold sig
    have hu := Real.exp_pos (-L)
    have hE := Real.exp_pos (k * t)
    have e1 : Real.exp (-(L + k * t)) * Real.exp (k * t) = Real.exp (-L) := by
      rw [← Real.exp_add]; ring_nf
    have hp := Real.exp_pos (-(L + k * t))
    have hkt : Real.exp (k * t) ≤ Real.exp (k * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hk)
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hkt hθ0]
  have e2 : Real.exp (-(r - k) * t) = Real.exp (-r * t) * Real.exp (k * t) := by
    rw [← Real.exp_add]; ring_nf
  rw [e2]
  have := Real.exp_pos (-r * t)
  calc θ * c * sig L * (Real.exp (-r * t) * Real.exp (k * t))
      = Real.exp (-r * t) * (c * (θ * Real.exp (k * t) * sig L)) := by ring
    _ ≤ Real.exp (-r * t) * (c * sig (L + k * t)) := by
      apply mul_le_mul_of_nonneg_left _ this.le
      exact mul_le_mul_of_nonneg_left hkey hc

section Exist

variable {β γ φ r : ℝ}

lemma exists_L1 (hγ0 : 0 < γ) (hγ1 : γ < 1) (hφ : 1 < φ) (hβ : 0 < β) (hr : 0 < r)
    (hγφ : 1 < γ * φ) (hC1 : Condition1 γ φ β r) :
    ∃ L, kap γ φ r * sig L < cval r (γ * φ) (γ * β) L := by
  have hκ := kap_pos hγ0 hγ1 hφ hr
  have hκs := kap_spec (φ := φ) hγ1 hr
  have hc : 0 < γ * φ := by positivity
  have hk : 0 ≤ γ * β := by positivity
  rcases hC1 with h | h
  · -- r ≤ γβ
    set θ : ℝ := 1 / 2
    set T : ℝ := 2 * kap γ φ r / (γ * φ) + 1
    have hT : 0 ≤ T := by positivity
    set L : ℝ := Real.log (1 - θ) - γ * β * T
    have hL : Real.exp (γ * β * T) ≤ (1 - θ) * Real.exp (-L) := by
      have : Real.exp (-L) = Real.exp (γ * β * T) / (1 - θ) := by
        simp only [L, neg_sub]
        rw [Real.exp_sub, Real.exp_log (by norm_num [θ])]
      rw [this, mul_div_cancel₀ _ (by norm_num [θ])]
    have hlow := lower_trunc hr hc.le hk (by norm_num [θ]) (by norm_num [θ]) hT hL
    have hJ : T ≤ ∫ t in (0:ℝ)..T, Real.exp (-(r - γ * β) * t) := by
      have : ∫ t in (0:ℝ)..T, (1:ℝ) = T := by simp
      conv_lhs => rw [← this]
      refine intervalIntegral.integral_mono_on hT intervalIntegrable_const
        (by apply Continuous.intervalIntegrable; fun_prop)
        fun t ht => ?_
      exact Real.one_le_exp (by nlinarith [ht.1])
    refine ⟨L, lt_of_lt_of_le ?_ hlow⟩
    have hs := sig_pos L
    have : kap γ φ r < θ * (γ * φ) * T := by
      simp only [θ, T]
      field_simp
      nlinarith
    calc kap γ φ r * sig L < θ * (γ * φ) * T * sig L := mul_lt_mul_of_pos_right this hs
      _ ≤ θ * (γ * φ) * sig L * (∫ t in (0:ℝ)..T, Real.exp (-(r - γ * β) * t)) := by
        have := mul_le_mul_of_nonneg_left hJ (show 0 ≤ θ * (γ * φ) * sig L by positivity)
        linarith
  · -- γβ < r case (or r ≤ γβ also fine): use the strict inequality
    by_cases hrk : r ≤ γ * β
    · -- reuse first case argument
      set θ : ℝ := 1 / 2
      set T : ℝ := 2 * kap γ φ r / (γ * φ) + 1
      have hT : 0 ≤ T := by positivity
      set L : ℝ := Real.log (1 - θ) - γ * β * T
      have hL : Real.exp (γ * β * T) ≤ (1 - θ) * Real.exp (-L) := by
        have : Real.exp (-L) = Real.exp (γ * β * T) / (1 - θ) := by
          simp only [L, neg_sub]
          rw [Real.exp_sub, Real.exp_log (by norm_num [θ])]
        rw [this, mul_div_cancel₀ _ (by norm_num [θ])]
      have hlow := lower_trunc hr hc.le hk (by norm_num [θ]) (by norm_num [θ]) hT hL
      have hJ : T ≤ ∫ t in (0:ℝ)..T, Real.exp (-(r - γ * β) * t) := by
        have : ∫ t in (0:ℝ)..T, (1:ℝ) = T := by simp
        conv_lhs => rw [← this]
        refine intervalIntegral.integral_mono_on hT intervalIntegrable_const
          (by apply Continuous.intervalIntegrable; fun_prop)
          fun t ht => ?_
        exact Real.one_le_exp (by nlinarith [ht.1])
      refine ⟨L, lt_of_lt_of_le ?_ hlow⟩
      have hs := sig_pos L
      have : kap γ φ r < θ * (γ * φ) * T := by
        simp only [θ, T]
        field_simp
        nlinarith
      calc kap γ φ r * sig L < θ * (γ * φ) * T * sig L := mul_lt_mul_of_pos_right this hs
        _ ≤ θ * (γ * φ) * sig L * (∫ t in (0:ℝ)..T, Real.exp (-(r - γ * β) * t)) := by
          have := mul_le_mul_of_nonneg_left hJ (show 0 ≤ θ * (γ * φ) * sig L by positivity)
          linarith
    push Not at hrk
    set δ := r - γ * β with hδdef
    have hδ : 0 < δ := by linarith
    have hC : (γ * φ - 1) * δ < (β - γ * β) * (γ * φ) := by
      rw [gt_iff_lt, div_mul_eq_mul_div, lt_div_iff₀ hδ] at h; linarith
    -- ρ := κ δ / c < 1
    set ρ := kap γ φ r * δ / (γ * φ) with hρ
    have hρ0 : 0 < ρ := by positivity
    have hρ1 : ρ < 1 := by
      rw [hρ, div_lt_one hc]
      -- κ δ < γφ  ⟸  (1-γ) r κ δ < (1-γ) r γ φ
      have h1 : (1 - γ) * r * (kap γ φ r * δ) < (1 - γ) * r * (γ * φ) := by
        rw [← mul_assoc, hκs]
        simp only [hδdef]
        nlinarith
      exact lt_of_mul_lt_mul_left h1 (by nlinarith)
    set ε := (1 - ρ) / 4 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hε1 : ε < 1 := by rw [hε]; linarith
    set θ := 1 - ε
    set T := -Real.log ε / δ
    have hT : 0 ≤ T := div_nonneg (by linarith [Real.log_neg hε0 hε1]) hδ.le
    have heT : Real.exp (-δ * T) = ε := by
      have : -δ * T = Real.log ε := by simp only [T]; field_simp
      rw [this, Real.exp_log hε0]
    set L : ℝ := Real.log (1 - θ) - γ * β * T
    have hθ1 : 0 < 1 - θ := by simp only [θ]; linarith
    have hL : Real.exp (γ * β * T) ≤ (1 - θ) * Real.exp (-L) := by
      have : Real.exp (-L) = Real.exp (γ * β * T) / (1 - θ) := by
        simp only [L, neg_sub]
        rw [Real.exp_sub, Real.exp_log hθ1]
      rw [this, mul_div_cancel₀ _ hθ1.ne']
    have hlow := lower_trunc hr hc.le hk (by simp only [θ]; linarith) (by simp only [θ]; linarith)
      hT hL
    rw [exp_integral hδ.ne', heT] at hlow
    refine ⟨L, lt_of_lt_of_le ?_ hlow⟩
    have hs := sig_pos L
    -- κ < θ c (1-ε)/δ
    have : kap γ φ r < θ * (γ * φ) * ((1 - ε) / δ) := by
      have hκρ : kap γ φ r = ρ * (γ * φ) / δ := by rw [hρ]; field_simp
      rw [hκρ, div_lt_iff₀ hδ]
      have : θ * (γ * φ) * ((1 - ε) / δ) * δ = (1 - ε) * (1 - ε) * (γ * φ) := by
        simp only [θ]; field_simp
      rw [this]
      have : ρ < (1 - ε) * (1 - ε) := by rw [hε]; nlinarith
      nlinarith
    have := mul_lt_mul_of_pos_right this hs
    linarith

lemma exists_Lstar (hγ0 : 0 < γ) (hγ1 : γ < 1) (hφ : 1 < φ) (hβ : 0 < β) (hr : 0 < r)
    (hγφ : 1 < γ * φ) (hC1 : Condition1 γ φ β r) :
    ∃ L, cval r (γ * φ) (γ * β) L = kap γ φ r * sig L := by
  obtain ⟨L1, h1⟩ := exists_L1 hγ0 hγ1 hφ hβ hr hγφ hC1
  have hκ := kap_pos hγ0 hγ1 hφ hr
  have hκs := kap_spec (φ := φ) hγ1 hr
  have hc : 0 < γ * φ := by positivity
  have hlt : γ * φ / r < kap γ φ r := by
    rw [div_lt_iff₀ hr]
    have : (1 - γ) * (γ * φ) < (1 - γ) * (kap γ φ r * r) := by
      have : (1 - γ) * (kap γ φ r * r) = γ * (φ - 1) := by rw [← hκs]; ring
      rw [this]; nlinarith
    exact lt_of_mul_lt_mul_left this (by linarith)
  set q := (γ * φ / (r * kap γ φ r) + 1) / 2 with hq
  have hq1' : γ * φ / (r * kap γ φ r) < 1 := by
    rw [div_lt_one (by positivity)]
    rw [div_lt_iff₀ hr] at hlt; linarith
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by rw [hq]; linarith
  set L2 := logit q
  have h2 : cval r (γ * φ) (γ * β) L2 < kap γ φ r * sig L2 := by
    rw [sig_logit' hq0 hq1]
    have hv := cval_le hr hc.le (γ * β) L2
    have : γ * φ / r < kap γ φ r * q := by
      have e : γ * φ / r = kap γ φ r * (γ * φ / (r * kap γ φ r)) := by field_simp
      rw [e]
      apply mul_lt_mul_of_pos_left _ hκ
      rw [hq]; linarith
    linarith
  have hcont : Continuous (fun L => cval r (γ * φ) (γ * β) L - kap γ φ r * sig L) := by
    have : Continuous (cval r (γ * φ) (γ * β)) :=
      continuous_iff_continuousAt.mpr fun L => (cval_hasDerivAt hr _ _ L).continuousAt
    exact this.sub (continuous_const.mul continuous_sig)
  have hiv := intermediate_value_uIcc (a := L1) (b := L2) hcont.continuousOn
  have h0 : (0:ℝ) ∈ uIcc ((fun L => cval r (γ * φ) (γ * β) L - kap γ φ r * sig L) L1)
      ((fun L => cval r (γ * φ) (γ * β) L - kap γ φ r * sig L) L2) := by
    rw [mem_uIcc]; right; constructor <;> simp only <;> linarith
  obtain ⟨L, _, hL⟩ := hiv h0
  exact ⟨L, by simp only at hL; linarith⟩

lemma cder_eq_marg (γ φ β r L : ℝ) :
    cder r (γ * φ) (γ * β) L = sig L * (1 - sig L) * margValue γ φ β r (sig L) := by
  unfold cder margValue
  rw [← integral_const_mul]
  congr 1
  funext t
  have hu := Real.exp_pos (-L)
  have hE := Real.exp_pos (-(γ * β) * t)
  have e1 : Real.exp (-(L + γ * β * t)) = Real.exp (-L) * Real.exp (-(γ * β) * t) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(γ * β + r) * t) = Real.exp (-r * t) * Real.exp (-(γ * β) * t) := by
    rw [← Real.exp_add]; ring_nf
  rw [one_sub_sig, one_sub_sig, e2]
  unfold sig
  rw [e1]
  set u := Real.exp (-L)
  set E := Real.exp (-(γ * β) * t)
  field_simp

lemma marg_at (hγ0 : 0 < γ) (hγ1 : γ < 1) (hβ : 0 < β) (hr : 0 < r) {L : ℝ}
    (hV : cval r (γ * φ) (γ * β) L = kap γ φ r * sig L) :
    margValue γ φ β r (sig L) = (γ * φ - 1) / ((1 - γ) * β * (1 - sig L)) := by
  have hibp := cval_ibp hr (γ * φ) (γ * β) L
  rw [cder_eq_marg, hV] at hibp
  have hκs := kap_spec (φ := φ) hγ1 hr
  have hs0 := sig_pos L
  have hs1 : 0 < 1 - sig L := by linarith [sig_lt_one L]
  rw [eq_div_iff (by positivity)]
  -- hibp : γβ * (s (1-s) m) = r κ s - γφ s
  have h1 : γ * β * ((1 - sig L) * margValue γ φ β r (sig L)) = r * kap γ φ r - γ * φ := by
    have := hibp
    have h2 : sig L * (γ * β * ((1 - sig L) * margValue γ φ β r (sig L))) =
        sig L * (r * kap γ φ r - γ * φ) := by linarith
    exact mul_left_cancel₀ hs0.ne' h2
  have h3 : (1 - γ) * (γ * β * ((1 - sig L) * margValue γ φ β r (sig L))) =
      γ * (γ * φ - 1) := by
    rw [h1]; nlinarith
  have h4 : γ * (margValue γ φ β r (sig L) * ((1 - γ) * β * (1 - sig L))) = γ * (γ * φ - 1) := by
    rw [← h3]; ring
  exact mul_left_cancel₀ hγ0.ne' h4

end Exist

end IASol



namespace IASol

noncomputable def Pf (β r κ Ls L : ℝ) : ℝ :=
  Real.exp (-r * Ls / β) * (κ * sig Ls) - (1 / β) * ∫ x in Ls..L, Real.exp (-r * x / β) * sig x

noncomputable def Phi (β r κ Ls L : ℝ) : ℝ := Real.exp (r * L / β) * Pf β r κ Ls L

lemma cont_aux (β r : ℝ) : Continuous (fun x => Real.exp (-r * x / β) * sig x) := by
  have := continuous_sig; fun_prop

lemma Pf_hasDerivAt (β r κ Ls L : ℝ) :
    HasDerivAt (Pf β r κ Ls) (-(1 / β) * (Real.exp (-r * L / β) * sig L)) L := by
  have h := ((cont_aux β r).integral_hasStrictDerivAt Ls L).hasDerivAt
  have := (h.const_mul (1 / β)).const_sub (Real.exp (-r * Ls / β) * (κ * sig Ls))
  unfold Pf
  exact this.congr_deriv (by ring)

lemma Phi_hasDerivAt {β : ℝ} (hβ : β ≠ 0) (r κ Ls L : ℝ) :
    HasDerivAt (Phi β r κ Ls) ((r * Phi β r κ Ls L - sig L) / β) L := by
  have e1 : HasDerivAt (fun L => Real.exp (r * L / β)) (Real.exp (r * L / β) * (r / β)) L := by
    have := (((hasDerivAt_id L).const_mul r).div_const β).exp
    simpa using this
  have := e1.mul (Pf_hasDerivAt β r κ Ls L)
  unfold Phi
  refine this.congr_deriv ?_
  have h1 : Real.exp (r * L / β) * Real.exp (-r * L / β) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  rw [show Real.exp (r * L / β) * (r / β) * Pf β r κ Ls L + Real.exp (r * L / β) *
      (-(1 / β) * (Real.exp (-r * L / β) * sig L)) = (r * (Real.exp (r * L / β) * Pf β r κ Ls L)
      - sig L * (Real.exp (r * L / β) * Real.exp (-r * L / β))) / β by field_simp; ring, h1, mul_one]

lemma Phi_at (β r κ Ls : ℝ) : Phi β r κ Ls Ls = κ * sig Ls := by
  unfold Phi Pf
  rw [intervalIntegral.integral_same, mul_zero, sub_zero, ← mul_assoc, ← Real.exp_add]
  ring_nf; simp

lemma Phi_continuous {β : ℝ} (hβ : β ≠ 0) (r κ Ls : ℝ) : Continuous (Phi β r κ Ls) :=
  continuous_iff_continuousAt.mpr fun L => (Phi_hasDerivAt hβ r κ Ls L).continuousAt

lemma Phi_ge {β r κ Ls : ℝ} (hβ : 0 < β) (hκ : 0 < κ)
    (hk : (r * κ - 1) / β ≤ κ * (1 - sig Ls)) {L : ℝ} (hL : L ≤ Ls) :
    κ * sig L ≤ Phi β r κ Ls L := by
  set E : ℝ → ℝ := fun L => Pf β r κ Ls L - κ * (Real.exp (-r * L / β) * sig L) with hE
  have hEd : ∀ x, HasDerivAt E (Real.exp (-r * x / β) * sig x *
      (-(1 / β) + κ * r / β - κ * (1 - sig x))) x := by
    intro x
    have e1 : HasDerivAt (fun L => Real.exp (-r * L / β)) (Real.exp (-r * x / β) * (-r / β)) x := by
      have := (((hasDerivAt_id x).const_mul (-r)).div_const β).exp
      simpa using this
    have := (Pf_hasDerivAt β r κ Ls x).sub ((e1.mul (hasDerivAt_sig x)).const_mul κ)
    refine this.congr_deriv ?_
    ring
  have hanti : AntitoneOn E (Iic Ls) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic Ls)
    · exact (continuous_iff_continuousAt.mpr fun x => (hEd x).continuousAt).continuousOn
    · exact fun x _ => (hEd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Iic] at hx
      rw [(hEd x).deriv]
      have hs : sig x ≤ sig Ls := sig_strictMono.monotone (le_of_lt hx)
      have h1 : (r * κ - 1) / β ≤ κ * (1 - sig x) := le_trans hk (by nlinarith)
      have h2 : -(1 / β) + κ * r / β - κ * (1 - sig x) ≤ 0 := by
        have : -(1 / β) + κ * r / β = (r * κ - 1) / β := by ring
        linarith
      have := mul_pos (Real.exp_pos (-r * x / β)) (sig_pos x)
      nlinarith
  have hEs : E Ls = 0 := by
    simp only [hE, Pf, intervalIntegral.integral_same, mul_zero, sub_zero]; ring
  have := hanti hL (show Ls ∈ Iic Ls from le_refl Ls) hL
  rw [hEs] at this
  simp only [hE] at this
  have hP : κ * (Real.exp (-r * L / β) * sig L) ≤ Pf β r κ Ls L := by linarith
  unfold Phi
  have h2 : Real.exp (r * L / β) * Real.exp (-r * L / β) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have := mul_le_mul_of_nonneg_left hP (Real.exp_pos (r * L / β)).le
  calc κ * sig L = Real.exp (r * L / β) * (κ * (Real.exp (-r * L / β) * sig L)) := by
        linear_combination (-(κ * sig L)) * h2
    _ ≤ _ := this

section Part3

variable {β γ φ r : ℝ}

set_option maxHeartbeats 4000000 in
theorem part3 (hγ0 : 0 < γ) (hγ1 : γ < 1) (hφ : 1 < φ) (hβ : 0 < β) (hr : 0 < r)
    (hγφ : 1 < γ * φ) (hC1 : Condition1 γ φ β r) :
    ∃ Astar ∈ Set.Ioo (0 : ℝ) 1,
        margValue γ φ β r Astar = (γ * φ - 1) / ((1 - γ) * β * (1 - Astar)) ∧
        ∃ Abar : ℝ, 0 < Abar ∧ ∀ A₀ ∈ Set.Ioo (0 : ℝ) 1, A₀ < Abar →
          ∃ A : ℝ → ℝ, IsOptimalFrom β γ φ r A₀ {t : ℝ | 0 ≤ t ∧ Astar ≤ A t} A := by
  obtain ⟨Ls, hLs⟩ := exists_Lstar hγ0 hγ1 hφ hβ hr hγφ hC1
  set κ := kap γ φ r with hκdef
  have hκ : 0 < κ := kap_pos hγ0 hγ1 hφ hr
  have hκs : (1 - γ) * r * κ = γ * (φ - 1) := kap_spec hγ1 hr
  have hc : 0 ≤ γ * φ := by positivity
  have hkk : 0 ≤ γ * β := by positivity
  set V := cval r (γ * φ) (γ * β) with hVdef
  set V' := cder r (γ * φ) (γ * β) with hV'def
  have hV : ∀ x, HasDerivAt V (V' x) x := fun x => cval_hasDerivAt hr _ _ x
  have hibp : ∀ x, γ * β * V' x = r * V x - γ * φ * sig x := fun x => cval_ibp hr _ _ x
  have hσs0 := sig_pos Ls
  have hσs1 := sig_lt_one Ls
  -- key inequality at Ls
  have h5 : r * κ - γ * φ = γ * (r * κ - 1) := by linear_combination hκs
  have hk : (r * κ - 1) / β ≤ κ * (1 - sig Ls) := by
    have h1 := cder_le hr hc hkk Ls
    rw [← hVdef, ← hV'def, hLs] at h1
    have h2 := hibp Ls
    rw [hLs] at h2
    have h3 : (r * κ - γ * φ) * sig Ls ≤ (γ * β * ((1 - sig Ls) * κ)) * sig Ls := by
      have := mul_le_mul_of_nonneg_left h1 hkk
      linear_combination this - h2
    have h4 : r * κ - γ * φ ≤ γ * β * ((1 - sig Ls) * κ) := le_of_mul_le_mul_right h3 hσs0
    rw [h5] at h4
    have h6 : r * κ - 1 ≤ β * ((1 - sig Ls) * κ) := by
      have : γ * (r * κ - 1) ≤ γ * (β * ((1 - sig Ls) * κ)) := by linear_combination h4
      exact le_of_mul_le_mul_left this hγ0
    rw [div_le_iff₀ hβ]
    linear_combination h6
  refine ⟨sig Ls, ⟨hσs0, hσs1⟩, marg_at hγ0 hγ1 hβ hr hLs, sig Ls, hσs0, ?_⟩
  rintro A₀ ⟨hA0, hA1⟩ hA0s
  -- the threshold value function
  set G : ℝ → ℝ := fun L => if L ≤ Ls then Phi β r κ Ls L else V L with hGdef
  set G' : ℝ → ℝ := fun L => if L ≤ Ls then (r * Phi β r κ Ls L - sig L) / β else V' L
    with hG'def
  have hPhiLs : Phi β r κ Ls Ls = V Ls := by rw [Phi_at, hLs]
  have hderLs : (r * Phi β r κ Ls Ls - sig Ls) / β = V' Ls := by
    rw [Phi_at]
    have h2 := hibp Ls
    rw [hLs] at h2
    have : γ * (β * V' Ls) = γ * ((r * κ - 1) * sig Ls) := by
      linear_combination h2 + sig Ls * h5
    have := mul_left_cancel₀ hγ0.ne' this
    field_simp
    linarith
  have hG : ∀ x, HasDerivAt G (G' x) x := by
    intro x
    rcases lt_trichotomy x Ls with h | h | h
    · have hd := Phi_hasDerivAt hβ.ne' r κ Ls x
      have : G' x = (r * Phi β r κ Ls x - sig x) / β := by simp [hG'def, h.le]
      rw [this]
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds h] with y hy
      show (if y ≤ Ls then Phi β r κ Ls y else V y) = Phi β r κ Ls y
      rw [if_pos (le_of_lt (show y < Ls from hy))]
    · subst h
      have : G' x = (r * Phi β r κ x x - sig x) / β := by simp [hG'def]
      rw [this]
      have h1 : HasDerivWithinAt G ((r * Phi β r κ x x - sig x) / β) (Iic x) x := by
        refine (Phi_hasDerivAt hβ.ne' r κ x x).hasDerivWithinAt.congr (fun y hy => ?_) ?_
        · simp [hGdef, hy.out]
        · simp [hGdef]
      have h2 : HasDerivWithinAt G ((r * Phi β r κ x x - sig x) / β) (Ici x) x := by
        rw [hderLs]
        refine (hV x).hasDerivWithinAt.congr (fun y hy => ?_) ?_
        · by_cases hyx : y ≤ x
          · have : y = x := le_antisymm hyx hy.out
            subst this; simp [hGdef, hPhiLs]
          · simp [hGdef, hyx]
        · simp [hGdef, hPhiLs]
      have := h1.union h2
      rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
      exact this
    · have hd := hV x
      have : G' x = V' x := by simp [hG'def, not_le.mpr h]
      rw [this]
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds h] with y hy
      show (if y ≤ Ls then Phi β r κ Ls y else V y) = V y
      rw [if_neg (not_le.mpr (show Ls < y from hy))]
  have hV'b : ∀ x, |V' x| ≤ φ / β := by
    intro x
    have h1 := cder_nonneg (r := r) hc (γ * β) x
    have h2 := cval_le hr hc (γ * β) x
    have h3 := hibp x
    have h4 := sig_pos x
    rw [abs_of_nonneg h1, le_div_iff₀ hβ]
    have : r * V x ≤ γ * φ := by
      have : r * V x ≤ r * (γ * φ / r) := mul_le_mul_of_nonneg_left h2 hr.le
      rwa [mul_div_cancel₀ _ hr.ne'] at this
    have : γ * (V' x * β) ≤ γ * φ := by nlinarith
    nlinarith
  have hG'b : ∀ a b, ∃ K, ∀ x ∈ Icc a b, |G' x| ≤ K := by
    intro a b
    obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (Phi_continuous hβ.ne' r κ Ls).continuousOn (s := Icc a b)
    refine ⟨(r * |M1| + 1) / β + φ / β, fun x hx => ?_⟩
    have hφβ : 0 ≤ φ / β := by positivity
    by_cases hxs : x ≤ Ls
    · have : G' x = (r * Phi β r κ Ls x - sig x) / β := by simp [hG'def, hxs]
      rw [this, abs_div, abs_of_pos hβ]
      have hb := hM1 x hx
      rw [Real.norm_eq_abs] at hb
      have : |r * Phi β r κ Ls x - sig x| ≤ r * |M1| + 1 := by
        have h1 : |r * Phi β r κ Ls x| ≤ r * |M1| := by
          rw [abs_mul, abs_of_pos hr]
          exact mul_le_mul_of_nonneg_left (le_trans hb (le_abs_self _)) hr.le
        have h2 : |sig x| ≤ 1 := by
          rw [abs_of_pos (sig_pos x)]; exact (sig_lt_one x).le
        calc _ ≤ |r * Phi β r κ Ls x| + |sig x| := abs_sub _ _
          _ ≤ _ := by linarith
      have := div_le_div_of_nonneg_right this hβ.le
      linarith
    · have : G' x = V' x := by simp [hG'def, hxs]
      rw [this]
      have := hV'b x
      have : 0 ≤ (r * |M1| + 1) / β := by positivity
      linarith
  have hGb : ∃ M, ∀ x, logit A₀ ≤ x → |G x| ≤ M := by
    obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (Phi_continuous hβ.ne' r κ Ls).continuousOn (s := Icc (logit A₀) Ls)
    refine ⟨|M1| + γ * φ / r, fun x hx => ?_⟩
    have h0 : 0 ≤ γ * φ / r := by positivity
    by_cases hxs : x ≤ Ls
    · have : G x = Phi β r κ Ls x := by simp [hGdef, hxs]
      rw [this]
      have := hM1 x ⟨hx, hxs⟩
      rw [Real.norm_eq_abs] at this
      linarith [le_abs_self M1]
    · have : G x = V x := by simp [hGdef, hxs]
      rw [this, abs_of_nonneg (cval_nonneg hc _ x)]
      have := cval_le hr hc (γ * β) x
      linarith [abs_nonneg M1]
  have hHJB : ∀ x, sig x + β * G' x ≤ r * G x ∧ γ * φ * sig x + γ * β * G' x ≤ r * G x := by
    intro x
    by_cases hxs : x ≤ Ls
    · have e1 : G x = Phi β r κ Ls x := by simp [hGdef, hxs]
      have e2 : G' x = (r * Phi β r κ Ls x - sig x) / β := by simp [hG'def, hxs]
      rw [e1, e2]
      have hge := Phi_ge hβ hκ hk hxs
      have e3 : β * ((r * Phi β r κ Ls x - sig x) / β) = r * Phi β r κ Ls x - sig x := by
        field_simp
      constructor
      · rw [e3]; linarith
      · have : γ * β * ((r * Phi β r κ Ls x - sig x) / β) =
            γ * (r * Phi β r κ Ls x - sig x) := by rw [mul_assoc, e3]
        rw [this]
        -- γ(φ-1)σ ≤ (1-γ) r Φ
        have h1 : γ * (φ - 1) * sig x ≤ (1 - γ) * r * Phi β r κ Ls x := by
          rw [← hκs]
          have : (1 - γ) * r * (κ * sig x) ≤ (1 - γ) * r * Phi β r κ Ls x :=
            mul_le_mul_of_nonneg_left hge (by nlinarith)
          linarith
        nlinarith
    · have e1 : G x = V x := by simp [hGdef, hxs]
      have e2 : G' x = V' x := by simp [hG'def, hxs]
      rw [e1, e2]
      have h1 := hibp x
      refine ⟨?_, by linarith⟩
      have hrat := cval_ratio_anti hr hc hkk (le_of_lt (not_le.mp hxs))
      rw [← hVdef, hLs] at hrat
      have hVle : V x ≤ κ * sig x := by
        have : V x * sig Ls ≤ (κ * sig x) * sig Ls := by linarith
        exact le_of_mul_le_mul_right this hσs0
      have h2 : (1 - γ) * r * V x ≤ γ * (φ - 1) * sig x := by
        rw [← hκs]
        have := mul_le_mul_of_nonneg_left hVle (show 0 ≤ (1 - γ) * r by nlinarith)
        linarith
      have h3 : γ * (sig x + β * V' x) ≤ γ * (r * V x) := by nlinarith
      exact le_of_mul_le_mul_left h3 hγ0
  -- the candidate path
  set L0 := logit A₀ with hL0
  have hL0s : L0 < Ls := by
    have : sig L0 < sig Ls := by rw [hL0, sig_logit' hA0 hA1]; exact hA0s
    exact sig_strictMono.lt_iff_lt.mp this
  set τ := (Ls - L0) / β with hτdef
  have hτ : 0 < τ := div_pos (by linarith) hβ
  have hβτ : β * τ = Ls - L0 := by rw [hτdef]; field_simp
  set ℓ : ℝ → ℝ := fun t => L0 + β * min t τ + β * γ * max (t - τ) 0 with hℓdef
  have hℓc : Continuous ℓ := by
    simp only [hℓdef]
    exact (continuous_const.add (continuous_const.mul (continuous_id.min continuous_const))).add
      (continuous_const.mul ((continuous_id.sub continuous_const).max continuous_const))
  have hℓlt : ∀ t, t < τ → ℓ t = L0 + β * t := by
    intro t ht
    simp only [hℓdef, min_eq_left ht.le, max_eq_right (by linarith : t - τ ≤ 0)]; ring
  have hℓge : ∀ t, τ ≤ t → ℓ t = Ls + β * γ * (t - τ) := by
    intro t ht
    simp only [hℓdef, min_eq_right ht, max_eq_left (by linarith : 0 ≤ t - τ)]
    linarith
  set A : ℝ → ℝ := fun t => sig (ℓ t) with hAdef
  set S : Set ℝ := {t : ℝ | 0 ≤ t ∧ sig Ls ≤ A t} with hSdef
  have hSeq : S = Ici τ := by
    ext t
    simp only [hSdef, hAdef, mem_setOf_eq, mem_Ici]
    constructor
    · rintro ⟨_, h⟩
      by_contra hlt
      push Not at hlt
      have := sig_strictMono.le_iff_le.mp h
      rw [hℓlt t hlt] at this
      have := mul_lt_mul_of_pos_left hlt hβ
      linarith
    · intro h
      refine ⟨le_trans hτ.le h, ?_⟩
      apply sig_strictMono.monotone
      rw [hℓge t h]
      have : 0 ≤ β * γ * (t - τ) := by
        apply mul_nonneg (by positivity); linarith
      linarith
  have hSm : MeasurableSet S := by rw [hSeq]; exact measurableSet_Ici
  have hffS : ∀ t, followerFactor γ S t = if τ ≤ t then γ else 1 := by
    intro t; simp [followerFactor, hSeq]
  have hpfS : ∀ t, profitFactor γ φ S t = if τ ≤ t then γ * φ else 1 := by
    intro t; simp [profitFactor, hSeq]
  have hℓ0 : ℓ 0 = L0 := by rw [hℓlt 0 hτ]; ring
  have hderℓ : ∀ t, 0 < t → t ≠ τ → HasDerivAt ℓ (β * followerFactor γ S t) t := by
    intro t _ htτ
    rcases lt_or_gt_of_ne htτ with h | h
    · rw [hffS, if_neg (not_le.mpr h), mul_one]
      refine (lin_hasDerivAt L0 β t).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds h] with y hy
      exact hℓlt y hy
    · rw [hffS, if_pos h.le]
      have : HasDerivAt (fun t => Ls + β * γ * (t - τ)) (β * γ) t := by
        have := ((hasDerivAt_id t).sub_const τ).const_mul (β * γ)
        simpa using this.const_add Ls
      refine this.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds h] with y hy
      exact hℓge y hy.out.le
  have hpath : IsPath β γ A₀ S A :=
    sig_path hβ hγ0 hγ1 hSm hA0 hA1 hℓc hℓ0 τ hderℓ
  refine ⟨A, hpath, fun S' A' hp' => ?_⟩
  rw [verif_eq hβ hγ0 hγ1 hφ hr hpath hA0 hA1 hG hG'b hGb τ (fun t ht htτ => ?_)]
  · exact verif_le hβ hγ0 hγ1 hφ hr hp' hA0 hA1 hG hG'b hGb hHJB
  · simp only [hAdef, logit_sig]
    rcases lt_or_gt_of_ne htτ with h | h
    · rw [hffS, hpfS, if_neg (not_le.mpr h), if_neg (not_le.mpr h)]
      have hlt : ℓ t ≤ Ls := by rw [hℓlt t h]; nlinarith
      have e1 : G (ℓ t) = Phi β r κ Ls (ℓ t) := by simp [hGdef, hlt]
      have e2 : G' (ℓ t) = (r * Phi β r κ Ls (ℓ t) - sig (ℓ t)) / β := by simp [hG'def, hlt]
      rw [e1, e2]
      field_simp
      ring
    · rw [hffS, hpfS, if_pos h.le, if_pos h.le]
      have hgt : ¬ ℓ t ≤ Ls := by
        rw [hℓge t h.le]
        have : 0 < β * γ * (t - τ) := by
          apply mul_pos (by positivity); linarith
        linarith
      have e1 : G (ℓ t) = V (ℓ t) := by simp [hGdef, hgt]
      have e2 : G' (ℓ t) = V' (ℓ t) := by simp [hG'def, hgt]
      rw [e1, e2]
      have := hibp (ℓ t)
      linarith

end Part3

end IASol


theorem solution (γ φ β r : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hφ : 1 < φ)
    (hβ : 0 < β) (hr : 0 < r) :
    (γ * φ ≤ 1 →
      ∀ A₀ ∈ Set.Ioo (0 : ℝ) 1, ∃ A : ℝ → ℝ, IsOptimalFrom β γ φ r A₀ ∅ A) ∧
    (1 < γ * φ → ¬ Condition1 γ φ β r →
      ∀ A₀ ∈ Set.Ioo (0 : ℝ) 1, ∃ A : ℝ → ℝ, IsOptimalFrom β γ φ r A₀ Set.univ A) ∧
    (1 < γ * φ → Condition1 γ φ β r →
      ∃ Astar ∈ Set.Ioo (0 : ℝ) 1,
        margValue γ φ β r Astar = (γ * φ - 1) / ((1 - γ) * β * (1 - Astar)) ∧
        ∃ Abar : ℝ, 0 < Abar ∧ ∀ A₀ ∈ Set.Ioo (0 : ℝ) 1, A₀ < Abar →
          ∃ A : ℝ → ℝ, IsOptimalFrom β γ φ r A₀ {t : ℝ | 0 ≤ t ∧ Astar ≤ A t} A) :=
  ⟨fun h A₀ hA => IASol.part1 hγ0 hγ1 hφ hβ hr h A₀ hA.1 hA.2,
   fun h hC A₀ hA => IASol.part2 hγ0 hγ1 hφ hβ hr h hC A₀ hA.1 hA.2,
   fun h hC => IASol.part3 hγ0 hγ1 hφ hβ hr h hC⟩
