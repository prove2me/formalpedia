-- Prove2me | solution 1 for MDPFinance.Contracting.lemma_7_3_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:45:26.241295+00:00
-- url     : https://prove2.me/submissions/4adc7160-fc73-42e3-a138-e6c527e8c741

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding

open MeasureTheory ProbabilityTheory Filter Topology
open MDPFinance.Contracting

namespace L733Aux

lemma toENNReal_coe_sup (t : ℝ) : ((t : EReal) ⊔ 0).toENNReal = ENNReal.ofReal t := by
  rcases le_total t 0 with h | h
  · rw [sup_of_le_right (by exact_mod_cast h)]; simp [ENNReal.ofReal_of_nonpos h]
  · rw [sup_of_le_left (by exact_mod_cast h), EReal.toENNReal_of_ne_top (EReal.coe_ne_top t)]
    simp

lemma erealIntegral_mono {E : Type*} [MeasurableSpace E] (μ : Measure E) {f g : E → EReal}
    (h : ∀ x, f x ≤ g x) : erealIntegral μ f ≤ erealIntegral μ g := by
  unfold erealIntegral
  apply add_le_add
  · apply EReal.coe_ennreal_le_coe_ennreal_iff.2
    apply lintegral_mono
    intro x
    exact EReal.toENNReal_le_toENNReal (sup_le_sup_right (h x) _)
  · apply EReal.neg_le_neg_iff.2
    apply EReal.coe_ennreal_le_coe_ennreal_iff.2
    apply lintegral_mono
    intro x
    exact EReal.toENNReal_le_toENNReal (sup_le_sup_right (EReal.neg_le_neg_iff.2 (h x)) _)

lemma erealIntegral_coe {E : Type*} [MeasurableSpace E] (μ : Measure E) {g : E → ℝ}
    (hg : Integrable g μ) :
    erealIntegral μ (fun y => (g y : EReal)) = ((∫ y, g y ∂μ : ℝ) : EReal) := by
  unfold erealIntegral
  have h1 : ∀ y, ((g y : EReal) ⊔ 0).toENNReal = ENNReal.ofReal (g y) :=
    fun y => toENNReal_coe_sup _
  have h2 : ∀ y, ((-(g y : EReal)) ⊔ 0).toENNReal = ENNReal.ofReal (-g y) := by
    intro y; rw [← EReal.coe_neg]; exact toENNReal_coe_sup _
  simp only [h1, h2]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
  have f1 : ∫⁻ a, ENNReal.ofReal (g a) ∂μ ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_mono fun a => ENNReal.ofReal_le_ofReal (le_abs_self (g a)))
      (by simpa [Real.norm_eq_abs] using (hasFiniteIntegral_iff_norm g).1 hg.2)).ne
  have f2 : ∫⁻ a, ENNReal.ofReal (-g a) ∂μ ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_mono fun a => ENNReal.ofReal_le_ofReal (neg_le_abs (g a)))
      (by simpa [Real.norm_eq_abs] using (hasFiniteIntegral_iff_norm g).1 hg.2)).ne
  rw [← EReal.coe_ennreal_toReal f1, ← EReal.coe_ennreal_toReal f2, ← EReal.coe_neg,
    ← EReal.coe_add, sub_eq_add_neg]

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

lemma b_integrable (M : MarkovDecisionModel E A) {b : E → ℝ} {cr αb : ℝ}
    (hb : IsBoundingFunction M b cr αb) {xa : E × A} (hxa : xa ∈ M.D) :
    Integrable b (M.Q xa) := by
  refine ⟨hb.hb_meas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hb.hb_nonneg)]
  exact lt_of_le_of_lt (hb.hQ xa hxa) ENNReal.ofReal_lt_top

lemma b_int_le (M : MarkovDecisionModel E A) {b : E → ℝ} {cr αb : ℝ}
    (hb : IsBoundingFunction M b cr αb) {xa : E × A} (hxa : xa ∈ M.D) :
    ∫ y, b y ∂(M.Q xa) ≤ αb * b xa.1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hb.hb_nonneg)
    hb.hb_meas.aestronglyMeasurable]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb.hQ xa hxa)
  rwa [ENNReal.toReal_ofReal (mul_nonneg hb.hαb (hb.hb_nonneg _))] at this

lemma v_integrable (M : MarkovDecisionModel E A) {b : E → ℝ} {cr αb : ℝ}
    (hb : IsBoundingFunction M b cr αb) {xa : E × A} (hxa : xa ∈ M.D)
    {v : E → ℝ} (hv : Measurable v) {c : ℝ} (hc : ∀ x, |v x| ≤ c * b x) :
    Integrable v (M.Q xa) :=
  Integrable.mono' ((b_integrable M hb hxa).const_mul c) hv.aestronglyMeasurable
    (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hc y)

lemma int_diff_le (M : MarkovDecisionModel E A) {b : E → ℝ} {cr αb : ℝ}
    (hb : IsBoundingFunction M b cr αb) {xa : E × A} (hxa : xa ∈ M.D)
    {v w : E → ℝ} (hv : Measurable v) {cv : ℝ} (hcv : ∀ x, |v x| ≤ cv * b x)
    (hw : Measurable w) {cw : ℝ} (hcw : ∀ x, |w x| ≤ cw * b x)
    {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ y, |v y - w y| ≤ K * b y) :
    |∫ y, v y ∂(M.Q xa) - ∫ y, w y ∂(M.Q xa)| ≤ K * (αb * b xa.1) := by
  rw [← integral_sub (v_integrable M hb hxa hv hcv) (v_integrable M hb hxa hw hcw)]
  calc |∫ y, (v y - w y) ∂(M.Q xa)| ≤ ∫ y, K * b y ∂(M.Q xa) := by
        have := norm_integral_le_of_norm_le (f := fun y => v y - w y)
          ((b_integrable M hb hxa).const_mul K)
          (ae_of_all _ (fun y => by simpa [Real.norm_eq_abs] using hK y))
        simpa [Real.norm_eq_abs] using this
    _ = K * ∫ y, b y ∂(M.Q xa) := integral_const_mul _ _
    _ ≤ K * (αb * b xa.1) := mul_le_mul_of_nonneg_left (b_int_le M hb hxa) hK0

lemma L_bound (M : MarkovDecisionModel E A) {b : E → ℝ} {cr αb : ℝ}
    (hb : IsBoundingFunction M b cr αb) {xa : E × A} (hxa : xa ∈ M.D)
    {v : E → ℝ} (hv : Measurable v) {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ x, |v x| ≤ c * b x) :
    |M.r xa + M.β * ∫ y, v y ∂(M.Q xa)| ≤ (cr + M.β * c * αb) * b xa.1 := by
  have h1 := int_diff_le M hb hxa hv hc (measurable_const (a := (0:ℝ)))
    (cw := 0) (fun _ => by simp) hc0 (fun y => by simpa using hc y)
  simp only [integral_zero, sub_zero] at h1
  have h2 := hb.hr xa hxa
  have hβ := M.hβ0
  calc |M.r xa + M.β * ∫ y, v y ∂(M.Q xa)|
      ≤ |M.r xa| + M.β * |∫ y, v y ∂(M.Q xa)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos hβ]
    _ ≤ cr * b xa.1 + M.β * (c * (αb * b xa.1)) := by gcongr
    _ = (cr + M.β * c * αb) * b xa.1 := by ring

lemma normb_nonneg {b : E → ℝ} (hb0 : ∀ x, 0 ≤ b x) (u : E → ℝ) : 0 ≤ normb b u :=
  Real.iSup_nonneg fun x => div_nonneg (abs_nonneg _) (hb0 x)

lemma le_normb {b : E → ℝ} (hb0 : ∀ x, 0 ≤ b x) {u : E → ℝ} {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ x, |u x| ≤ c * b x) (x : E) : |u x| ≤ normb b u * b x := by
  rcases (hb0 x).lt_or_eq with hpos | hzero
  · have hbdd : BddAbove (Set.range fun y => |u y| / b y) := by
      refine ⟨c, ?_⟩
      rintro _ ⟨y, rfl⟩
      rcases (hb0 y).lt_or_eq with hy | hy
      · exact (div_le_iff₀ hy).2 (hc y)
      · simp [← hy, hc0]
    have := le_ciSup hbdd x
    exact (div_le_iff₀ hpos).1 this
  · have := hc x
    rw [← hzero, mul_zero] at this ⊢
    exact this

lemma normb_le {b : E → ℝ} {u : E → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (h : ∀ x, |u x| ≤ K * b x) : normb b u ≤ K := by
  unfold normb
  rcases isEmpty_or_nonempty E with hE | hE
  · rw [Real.iSup_of_isEmpty]; exact hK0
  · refine ciSup_le fun x => ?_
    rcases lt_or_ge 0 (b x) with hpos | hle
    · exact (div_le_iff₀ hpos).2 (h x)
    · rcases hle.lt_or_eq with hneg | hz
      · exact (div_nonpos_of_nonneg_of_nonpos (abs_nonneg _) hneg.le).trans hK0
      · simp [hz, hK0]

lemma Tf'_IBb (M : MarkovDecisionModel E A) {b : E → ℝ} {cr αb : ℝ}
    (hb : IsBoundingFunction M b cr αb) {f : E → A} (hf : IsDecisionRuleOf M f)
    {v : E → ℝ} (hv : v ∈ IBb b) : Tf' M f v ∈ IBb b := by
  obtain ⟨hvm, c, hc0, hc⟩ := hv
  have hg : Measurable fun x => (x, f x) := measurable_id.prodMk hf.1
  refine ⟨?_, cr + M.β * c * αb, ?_, fun x => L_bound M hb (hf.2 x) hvm hc0 hc⟩
  · have h1 : Measurable fun x => ∫ y, v y ∂((M.Q.comap (fun x => (x, f x)) hg) x) :=
      (hvm.stronglyMeasurable.integral_kernel).measurable
    simp only [Kernel.comap_apply] at h1
    exact (M.hr_meas.comp hg).add (h1.const_mul _)
  · have := M.hβ0; have := hb.hcr; have := hb.hαb; positivity

lemma iter_IBb (M : MarkovDecisionModel E A) {b : E → ℝ} {cr αb : ℝ}
    (hb : IsBoundingFunction M b cr αb) {f : E → A} (hf : IsDecisionRuleOf M f)
    {v : E → ℝ} (hv : v ∈ IBb b) (n : ℕ) : (Tf' M f)^[n] v ∈ IBb b := by
  induction n with
  | zero => exact hv
  | succ n ih => rw [Function.iterate_succ_apply']; exact Tf'_IBb M hb hf ih

lemma Tf'_contr (M : MarkovDecisionModel E A) {b : E → ℝ} {cr αb : ℝ}
    (hb : IsBoundingFunction M b cr αb) {f : E → A} (hf : IsDecisionRuleOf M f)
    {v w : E → ℝ} (hv : v ∈ IBb b) (hw : w ∈ IBb b) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ y, |v y - w y| ≤ K * b y) (x : E) :
    |Tf' M f v x - Tf' M f w x| ≤ M.β * αb * K * b x := by
  obtain ⟨hvm, cv, -, hcv⟩ := hv
  obtain ⟨hwm, cw, -, hcw⟩ := hw
  have h := int_diff_le M hb (hf.2 x) hvm hcv hwm hcw hK0 hK
  unfold Tf'
  have hβ := M.hβ0
  calc |M.r (x, f x) + M.β * ∫ y, v y ∂(M.Q (x, f x)) -
        (M.r (x, f x) + M.β * ∫ y, w y ∂(M.Q (x, f x)))|
      = M.β * |∫ y, v y ∂(M.Q (x, f x)) - ∫ y, w y ∂(M.Q (x, f x))| := by
        rw [← abs_of_pos hβ, ← abs_mul, abs_of_pos hβ]; congr 1; ring
    _ ≤ M.β * (K * (αb * b x)) := mul_le_mul_of_nonneg_left h hβ.le
    _ = M.β * αb * K * b x := by ring

lemma iter_contr (M : MarkovDecisionModel E A) {b : E → ℝ} {cr αb : ℝ}
    (hb : IsBoundingFunction M b cr αb) {f : E → A} (hf : IsDecisionRuleOf M f)
    {v w : E → ℝ} (hv : v ∈ IBb b) (hw : w ∈ IBb b) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ y, |v y - w y| ≤ K * b y) (n : ℕ) (x : E) :
    |(Tf' M f)^[n] v x - (Tf' M f)^[n] w x| ≤ (M.β * αb) ^ n * K * b x := by
  have hq : 0 ≤ M.β * αb := mul_nonneg M.hβ0.le hb.hαb
  induction n generalizing x with
  | zero => simpa using hK x
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have := Tf'_contr M hb hf (iter_IBb M hb hf hv n) (iter_IBb M hb hf hw n)
      (mul_nonneg (pow_nonneg hq n) hK0) ih x
    calc _ ≤ _ := this
      _ = (M.β * αb) ^ (n + 1) * K * b x := by ring

lemma sup_le_sup_add {ι : Type*} {F G : ι → ℝ} (hG : BddAbove (Set.range G)) {d : ℝ}
    (hd : 0 ≤ d) (h : ∀ i, F i ≤ G i + d) : iSup F ≤ iSup G + d := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Real.iSup_of_isEmpty, hd]
  · exact ciSup_le fun i => by linarith [h i, le_ciSup hG i]

open Classical in
lemma T'_contr (M : MarkovDecisionModel E A) {b : E → ℝ} {cr αb : ℝ}
    (hb : IsBoundingFunction M b cr αb)
    {v w : E → ℝ} (hv : v ∈ IBb b) (hw : w ∈ IBb b) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ y, |v y - w y| ≤ K * b y) (x : E) :
    |T' M v x - T' M w x| ≤ M.β * αb * K * b x := by
  obtain ⟨hvm, cv, hcv0, hcv⟩ := hv
  obtain ⟨hwm, cw, hcw0, hcw⟩ := hw
  have hβ := M.hβ0
  have hd : 0 ≤ M.β * αb * K * b x :=
    mul_nonneg (mul_nonneg (mul_nonneg hβ.le hb.hαb) hK0) (hb.hb_nonneg x)
  have hite : ∀ (u : E → ℝ) (a : A), (⨆ (_ : a ∈ M.Dx x), M.r (x, a) + M.β * ∫ y, u y ∂(M.Q (x, a)))
      = if a ∈ M.Dx x then M.r (x, a) + M.β * ∫ y, u y ∂(M.Q (x, a)) else 0 := by
    intro u a
    split_ifs with h
    · exact ciSup_pos h
    · have : IsEmpty (a ∈ M.Dx x) := ⟨h⟩
      exact Real.iSup_of_isEmpty _
  have hbdd : ∀ (u : E → ℝ) (c : ℝ), Measurable u → 0 ≤ c → (∀ y, |u y| ≤ c * b y) →
      BddAbove (Set.range fun a => if a ∈ M.Dx x then
        M.r (x, a) + M.β * ∫ y, u y ∂(M.Q (x, a)) else 0) := by
    intro u c hum hc0 hc
    refine ⟨max ((cr + M.β * c * αb) * b x) 0, ?_⟩
    rintro _ ⟨a, rfl⟩
    dsimp only
    split_ifs with h
    · exact le_max_of_le_left ((le_abs_self _).trans (L_bound M hb h hum hc0 hc))
    · exact le_max_right _ _
  have hstep : ∀ (u u' : E → ℝ), Measurable u → Measurable u' → (∃ c, ∀ y, |u y| ≤ c * b y) →
      (∃ c, ∀ y, |u' y| ≤ c * b y) → (∀ y, |u y - u' y| ≤ K * b y) → ∀ a,
      (if a ∈ M.Dx x then M.r (x, a) + M.β * ∫ y, u y ∂(M.Q (x, a)) else 0) ≤
      (if a ∈ M.Dx x then M.r (x, a) + M.β * ∫ y, u' y ∂(M.Q (x, a)) else 0)
        + M.β * αb * K * b x := by
    rintro u u' hu hu' ⟨c, hc⟩ ⟨c', hc'⟩ huu a
    split_ifs with h
    · have h1 := int_diff_le M hb h hu hc hu' hc' hK0 huu
      have h2 := (le_abs_self _).trans h1
      have h3 := mul_le_mul_of_nonneg_left h2 hβ.le
      simp only at h3
      nlinarith
    · simpa using hd
  unfold T'
  simp only [hite]
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    exact (sup_le_sup_add (hbdd w cw hwm hcw0 hcw) hd
      (hstep v w hvm hwm ⟨cv, hcv⟩ ⟨cw, hcw⟩ hK)).trans_eq (add_comm _ _)
  · rw [sub_le_iff_le_add]
    exact (sup_le_sup_add (hbdd v cv hvm hcv0 hcv) hd
      (hstep w v hwm hvm ⟨cw, hcw⟩ ⟨cv, hcv⟩ (fun y => by rw [abs_sub_comm]; exact hK y))).trans_eq
      (add_comm _ _)

lemma Jnpi_eq (M : MarkovDecisionModel E A) {b : E → ℝ} {cr αb : ℝ}
    (hb : IsBoundingFunction M b cr αb) {f : E → A} (hf : IsDecisionRuleOf M f) (n : ℕ) :
    ∀ x, Jnpi M M.r (fun _ => f) n x = (((Tf' M f)^[n] 0 x : ℝ) : EReal) := by
  have h0 : (0 : E → ℝ) ∈ IBb b := ⟨measurable_const, 0, le_rfl, fun x => by simp⟩
  induction n with
  | zero => intro x; simp [Jnpi]
  | succ n ih =>
    intro x
    have hfun : Jnpi M M.r (fun _ => f) n = fun y => (((Tf' M f)^[n] 0 y : ℝ) : EReal) :=
      funext ih
    obtain ⟨hum, c, -, hc⟩ := iter_IBb M hb hf h0 n
    simp only [Jnpi]
    rw [hfun, erealIntegral_coe _ (v_integrable M hb (hf.2 x) hum hc),
      Function.iterate_succ_apply']
    simp only [Tf', EReal.coe_add, EReal.coe_mul]

end L733Aux

open L733Aux in
theorem solution {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (f : E → A)
    (hf : IsDecisionRuleOf M f) :
    (∀ v ∈ IBb b, ∀ w ∈ IBb b,
        normb b (fun x => Tf' M f v x - Tf' M f w x) ≤ M.β * αb * normb b (fun x => v x - w x)) ∧
      (∀ v ∈ IBb b, ∀ w ∈ IBb b,
        normb b (fun x => T' M v x - T' M w x) ≤ M.β * αb * normb b (fun x => v x - w x)) ∧
      (M.β * αb < 1 →
        (∀ g ∈ IBb b, Tendsto (fun n => normb b fun x =>
            (Tf' M f)^[n] g x - (Jinfpi M M.r (fun _ => f) x).toReal) atTop (𝓝 0)) ∧
          ∀ v ∈ IBb b, Tf' M f v = v → v = fun x => (Jinfpi M M.r (fun _ => f) x).toReal) := by
  have hb0 := hb.hb_nonneg
  have hq : 0 ≤ M.β * αb := mul_nonneg M.hβ0.le hb.hαb
  -- pointwise bound of a difference by its norm
  have hdiff : ∀ v ∈ IBb b, ∀ w ∈ IBb b, ∀ y,
      |v y - w y| ≤ normb b (fun x => v x - w x) * b y := by
    rintro v ⟨-, cv, hcv0, hcv⟩ w ⟨-, cw, hcw0, hcw⟩ y
    refine le_normb (u := fun x => v x - w x) hb0 (add_nonneg hcv0 hcw0) (fun x => ?_) y
    calc |v x - w x| ≤ |v x| + |w x| := abs_sub _ _
      _ ≤ cv * b x + cw * b x := add_le_add (hcv x) (hcw x)
      _ = (cv + cw) * b x := by ring
  refine ⟨?_, ?_, ?_⟩
  · intro v hv w hw
    have hN := normb_nonneg hb0 (fun x => v x - w x)
    exact normb_le (mul_nonneg hq hN) (Tf'_contr M hb hf hv hw hN (hdiff v hv w hw))
  · intro v hv w hw
    have hN := normb_nonneg hb0 (fun x => v x - w x)
    exact normb_le (mul_nonneg hq hN) (T'_contr M hb hv hw hN (hdiff v hv w hw))
  intro hk
  set k := M.β * αb with hkdef
  have h0 : (0 : E → ℝ) ∈ IBb b := ⟨measurable_const, 0, le_rfl, fun x => by simp⟩
  set u : ℕ → E → ℝ := fun n => (Tf' M f)^[n] 0 with hu
  obtain ⟨-, c1, hc10, hc1⟩ := Tf'_IBb M hb hf h0
  have hstep : ∀ x n, dist (u n x) (u (n + 1) x) ≤ c1 * b x * k ^ n := by
    intro x n
    have := iter_contr M hb hf (Tf'_IBb M hb hf h0) h0 hc10
      (fun y => by simpa using hc1 y) n x
    rw [Real.dist_eq, abs_sub_comm]
    simp only [hu]
    rw [Function.iterate_succ_apply]
    calc _ ≤ _ := this
      _ = c1 * b x * k ^ n := by ring
  have hlim : ∀ x, ∃ L, Tendsto (fun n => u n x) atTop (𝓝 L) := fun x =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric k (c1 * b x) hk (hstep x))
  choose L hL using hlim
  have hJ : ∀ x, (Jinfpi M M.r (fun _ => f) x).toReal = L x := by
    intro x
    have h1 : Tendsto (fun n => Jnpi M M.r (fun _ => f) n x) atTop (𝓝 ((L x : ℝ) : EReal)) := by
      simp only [Jnpi_eq M hb hf]
      exact (continuous_coe_real_ereal.tendsto _).comp (hL x)
    unfold Jinfpi
    rw [h1.limsup_eq, EReal.toReal_coe]
  have hLb : ∀ x n, |u n x - L x| ≤ k ^ n * (c1 / (1 - k)) * b x := by
    intro x n
    have := dist_le_of_le_geometric_of_tendsto k (c1 * b x) hk (hstep x) (hL x) n
    rw [Real.dist_eq] at this
    calc _ ≤ _ := this
      _ = k ^ n * (c1 / (1 - k)) * b x := by ring
  have hk1 : 0 < 1 - k := by linarith
  have hgen : ∀ g ∈ IBb b, ∃ D, 0 ≤ D ∧ ∀ n x,
      |(Tf' M f)^[n] g x - (Jinfpi M M.r (fun _ => f) x).toReal| ≤ k ^ n * D * b x := by
    intro g hg
    obtain ⟨-, cg, hcg0, hcg⟩ := id hg
    refine ⟨cg + c1 / (1 - k), add_nonneg hcg0 (div_nonneg hc10 hk1.le), fun n x => ?_⟩
    have h1 := iter_contr M hb hf hg h0 hcg0 (fun y => by simpa using hcg y) n x
    rw [hJ]
    calc |(Tf' M f)^[n] g x - L x|
        ≤ |(Tf' M f)^[n] g x - u n x| + |u n x - L x| := abs_sub_le _ _ _
      _ ≤ k ^ n * cg * b x + k ^ n * (c1 / (1 - k)) * b x := add_le_add h1 (hLb x n)
      _ = k ^ n * (cg + c1 / (1 - k)) * b x := by ring
  have hpow : Tendsto (fun n => k ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq hk
  refine ⟨fun g hg => ?_, fun v hv hfix => ?_⟩
  · obtain ⟨D, hD0, hD⟩ := hgen g hg
    refine squeeze_zero (fun n => normb_nonneg hb0 _) (fun n => normb_le
      (mul_nonneg (pow_nonneg hq n) hD0) (hD n)) ?_
    simpa using hpow.mul_const D
  · obtain ⟨D, hD0, hD⟩ := hgen v hv
    funext x
    have hfixn : ∀ n, (Tf' M f)^[n] v = v := fun n => Function.iterate_fixed hfix n
    have h1 : ∀ n, |v x - (Jinfpi M M.r (fun _ => f) x).toReal| ≤ k ^ n * D * b x := by
      intro n; have := hD n x; rwa [hfixn] at this
    have h2 : Tendsto (fun n => k ^ n * D * b x) atTop (𝓝 0) := by
      simpa using (hpow.mul_const D).mul_const (b x)
    have h3 := ge_of_tendsto' h2 h1
    have : |v x - (Jinfpi M M.r (fun _ => f) x).toReal| = 0 := le_antisymm h3 (abs_nonneg _)
    linarith [abs_eq_zero.1 this]
