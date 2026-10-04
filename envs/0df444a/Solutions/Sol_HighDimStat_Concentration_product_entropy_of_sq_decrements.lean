-- Prove2me | solution 1 for HighDimStat.Concentration.product_entropy_of_sq_decrements
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T21:43:05.343343+00:00
-- url     : https://prove2.me/submissions/558663c6-1d58-454d-ad10-4a0fd7caeca7

import Mathlib
import Definitions.Def_HighDimStat_Concentration_phiEntropy
import Theorems.Thm_bousquet_massart_modified_lsi_summand_psi
import Theorems.Thm_entropy_n_coordinate_han_subadditivity_measure_pi_pos


open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

set_option maxHeartbeats 800000

lemma exp_neg_le_quadratic (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  let F := fun y : ℝ => 1 - y + y ^ 2 / 2 - Real.exp (-y)
  let D := fun y : ℝ => -1 + y + Real.exp (-y)
  have hd : ∀ y ∈ Set.Icc 0 x, HasDerivAt F (D y) y := by
    intro y hy
    convert (((hasDerivAt_const y 1).sub (hasDerivAt_id y)).add
      ((hasDerivAt_pow 2 y).div_const 2)).sub ((hasDerivAt_id y).neg.exp) using 1 <;>
      first | rfl | (dsimp [F, D]; ring)
  have hm : MonotoneOn F (Set.Icc 0 x) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    dsimp [D]
    linarith [Real.add_one_le_exp (-y)]
  have hh := hm ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  simpa [F] using hh

/-- A constant lower reference gives an entropy estimate in terms of the
squared decrement. This is the one-coordinate input to tensorization. -/
lemma entropy_exp_le_sq_gap {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} {lam c : ℝ}
    (hlam : 0 ≤ lam)
    (hexp : Integrable (fun ω => Real.exp (lam * Z ω)) μ)
    (hzexp : Integrable (fun ω => lam * Z ω * Real.exp (lam * Z ω)) μ)
    (hgap : ∀ᵐ ω ∂μ, c ≤ Z ω)
    (hsq : Integrable (fun ω => Real.exp (lam * Z ω) * (Z ω - c) ^ 2) μ) :
    phiEntropy (fun ω => Real.exp (lam * Z ω)) μ ≤
      lam ^ 2 / 2 * ∫ ω, Real.exp (lam * Z ω) * (Z ω - c) ^ 2 ∂μ := by
  have hid (ω : Ω) :
      Real.exp (lam * Z ω) *
        (Real.exp (-(lam * (Z ω - c))) - 1 + lam * (Z ω - c)) =
      Real.exp (lam * c) - Real.exp (lam * Z ω) +
        lam * Z ω * Real.exp (lam * Z ω) -
        (lam * c) * Real.exp (lam * Z ω) := by
    have he : Real.exp (lam * Z ω) * Real.exp (-(lam * (Z ω - c))) =
        Real.exp (lam * c) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_add, mul_sub, mul_one, he]
    ring
  have hpsi : Integrable (fun ω => Real.exp (lam * Z ω) *
      (Real.exp (-(lam * (Z ω - c))) - 1 + lam * (Z ω - c))) μ := by
    have hi := ((integrable_const (Real.exp (lam * c))).sub hexp).add hzexp
    have hi' := hi.sub (hexp.const_mul (lam * c))
    exact hi'.congr (ae_of_all _ (fun ω => (hid ω).symm))
  have hrhs : Integrable (fun ω => lam ^ 2 / 2 *
      (Real.exp (lam * Z ω) * (Z ω - c) ^ 2)) μ := hsq.const_mul _
  calc
    _ = lam * (∫ ω, Z ω * Real.exp (lam * Z ω) ∂μ) -
        (∫ ω, Real.exp (lam * Z ω) ∂μ) * Real.log (∫ ω, Real.exp (lam * Z ω) ∂μ) := by
      unfold phiEntropy
      congr 1
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ω
      rw [Real.log_exp]
      ring
    _ ≤ ∫ ω, Real.exp (lam * Z ω) *
        (Real.exp (-(lam * (Z ω - c))) - 1 + lam * (Z ω - c)) ∂μ :=
      bousquet_massart_modified_lsi_summand_psi hexp hzexp
    _ ≤ ∫ ω, lam ^ 2 / 2 * (Real.exp (lam * Z ω) * (Z ω - c) ^ 2) ∂μ := by
      apply integral_mono_ae hpsi hrhs
      filter_upwards [hgap] with ω hω
      have h := exp_neg_le_quadratic (lam * (Z ω - c)) (mul_nonneg hlam (sub_nonneg.mpr hω))
      have h' : Real.exp (-(lam * (Z ω - c))) - 1 + lam * (Z ω - c) ≤
          (lam * (Z ω - c)) ^ 2 / 2 := by linarith
      calc
        _ ≤ Real.exp (lam * Z ω) * ((lam * (Z ω - c)) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left h' (Real.exp_pos _).le
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

end HighDimStat.Concentration



open MeasureTheory

namespace HighDimStat.Concentration

theorem talagrand_upd_insertNth {m : ℕ} {α : Fin (m+1) → Type}
    (k : Fin (m+1)) (x0 t : α k) (rest : ∀ j, α (k.succAbove j)) :
    Function.update (Fin.insertNth k x0 rest) k t = Fin.insertNth k t rest := by
  ext i
  rcases eq_or_ne i k with h | h
  · subst h; simp
  · rw [Function.update_of_ne h]
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq h
    simp [Fin.insertNth_apply_succAbove]

-- Single integral transport at coordinate k.
theorem talagrand_transport_at_k {m : ℕ} {α : Fin (m+1) → Type} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (k : Fin (m+1)) (F : (∀ i, α i) → ℝ) :
    ∫ x, F x ∂(Measure.pi μ)
      = ∫ p : α k × (∀ j, α (k.succAbove j)),
          F (Fin.insertNth k p.1 p.2)
          ∂((μ k).prod (Measure.pi (fun j => μ (k.succAbove j)))) := by
  have hmp := measurePreserving_piFinSuccAbove μ k
  rw [← hmp.integral_comp (MeasurableEquiv.piFinSuccAbove α k).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with x
  have : Fin.insertNth k ((MeasurableEquiv.piFinSuccAbove α k) x).1
      ((MeasurableEquiv.piFinSuccAbove α k) x).2
      = (MeasurableEquiv.piFinSuccAbove α k).symm ((MeasurableEquiv.piFinSuccAbove α k) x) := rfl
  rw [this, MeasurableEquiv.symm_apply_apply]



end HighDimStat.Concentration



open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

set_option maxHeartbeats 1200000

lemma bounded_measurable_integrable {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ] {F : A → ℝ}
    (hF : Measurable F) {C : ℝ} (hbound : ∀ x, ‖F x‖ ≤ C) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ hbound)

/-- Averaging one coordinate with its own marginal leaves a product
expectation unchanged. -/
lemma integral_pi_coordinate_average {n : ℕ} {α : Fin n → Type}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (k : Fin n) (F : (∀ i, α i) → ℝ)
    (hF : Measurable F) {C : ℝ} (hbound : ∀ x, ‖F x‖ ≤ C) :
    (∫ x, (∫ t, F (Function.update x k t) ∂(μ k)) ∂(Measure.pi μ)) =
      ∫ x, F x ∂(Measure.pi μ) := by
  classical
  cases n with
  | zero => exact k.elim0
  | succ m =>
    let ν := Measure.pi (fun j : Fin m => μ (k.succAbove j))
    let G := fun p : α k × (∀ j : Fin m, α (k.succAbove j)) =>
      F (Fin.insertNth k p.1 p.2)
    have hG : Measurable G := hF.comp (MeasurableEquiv.piFinSuccAbove α k).symm.measurable
    have hGi : Integrable G ((μ k).prod ν) :=
      bounded_measurable_integrable hG (fun p => hbound _)
    let H := fun rest : (∀ j : Fin m, α (k.succAbove j)) => ∫ t, G (t, rest) ∂(μ k)
    have hH : Measurable H := by
      have hswap : Measurable (fun p : (∀ j : Fin m, α (k.succAbove j)) × α k => G (p.2, p.1)) :=
        hG.comp (measurable_snd.prodMk measurable_fst)
      exact hswap.stronglyMeasurable.integral_prod_right'.measurable
    have hHb (rest : ∀ j : Fin m, α (k.succAbove j)) : ‖H rest‖ ≤ C := by
      have h := norm_integral_le_of_norm_le_const (μ := μ k)
        (f := fun t => G (t, rest)) (C := C) (ae_of_all _ (fun t => hbound _))
      simpa [H, probReal_univ] using h
    have hHi : Integrable (fun p : α k × (∀ j : Fin m, α (k.succAbove j)) => H p.2)
        ((μ k).prod ν) := bounded_measurable_integrable (hH.comp measurable_snd) (fun p => hHb _)
    rw [talagrand_transport_at_k μ k (fun x => ∫ t, F (Function.update x k t) ∂(μ k)),
      talagrand_transport_at_k μ k F]
    simp_rw [talagrand_upd_insertNth]
    change (∫ p, H p.2 ∂((μ k).prod ν)) = ∫ p, G p ∂((μ k).prod ν)
    rw [integral_prod _ hHi, integral_prod_symm _ hGi]
    simp [H]

end HighDimStat.Concentration



open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

set_option maxHeartbeats 1200000

lemma log_abs_le_of_mem_positive_interval {cc CC v : ℝ} (hcc : 0 < cc)
    (hlo : cc ≤ v) (hhi : v ≤ CC) :
    |Real.log v| ≤ |Real.log cc| + |Real.log CC| := by
  have h1 := Real.log_le_log hcc hlo
  have h2 := Real.log_le_log (lt_of_lt_of_le hcc hlo) hhi
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log cc), abs_nonneg (Real.log CC)]
  · linarith [le_abs_self (Real.log CC), abs_nonneg (Real.log cc)]

lemma mul_log_norm_le_of_mem_positive_interval {cc CC v : ℝ} (hcc : 0 < cc)
    (hlo : cc ≤ v) (hhi : v ≤ CC) :
    ‖v * Real.log v‖ ≤ |CC| * (|Real.log cc| + |Real.log CC|) := by
  rw [Real.norm_eq_abs, abs_mul]
  apply mul_le_mul _ (log_abs_le_of_mem_positive_interval hcc hlo hhi) (abs_nonneg _) (abs_nonneg _)
  rw [abs_of_pos (lt_of_lt_of_le hcc hlo)]
  exact hhi.trans (le_abs_self CC)

lemma coordinate_average_measurable {n : ℕ} {α : Fin n → Type}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (k : Fin n) {F : (∀ i, α i) → ℝ} (hF : Measurable F) :
    Measurable (fun x => ∫ t, F (Function.update x k t) ∂(μ k)) := by
  have h : Measurable (fun p : (∀ i, α i) × α k => F (Function.update p.1 k p.2)) :=
    hF.comp (measurable_update'.comp (measurable_fst.prodMk measurable_snd))
  exact h.stronglyMeasurable.integral_prod_right'.measurable

lemma bounded_positive_fiber_entropy_integrable {E A : Type*}
    [MeasurableSpace E] [MeasurableSpace A] (ν : Measure E) (ρ : Measure A)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    {F : E × A → ℝ} (hF : Measurable F) {cc CC : ℝ} (hcc : 0 < cc)
    (hlo : ∀ p, cc ≤ F p) (hhi : ∀ p, F p ≤ CC) :
    Integrable (fun x => phiEntropy (fun t => F (x, t)) ρ) ν := by
  let B := |CC| * (|Real.log cc| + |Real.log CC|)
  let M := fun x => ∫ t, F (x, t) ∂ρ
  let A := fun x => ∫ t, F (x, t) * Real.log (F (x, t)) ∂ρ
  have hMb (x : E) : cc ≤ M x ∧ M x ≤ CC := by
    have hi : Integrable (fun t => F (x, t)) ρ :=
      bounded_measurable_integrable (hF.comp measurable_prodMk_left) (fun t => by
        rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hcc (hlo _))]
        exact (hhi _).trans (le_abs_self CC))
    constructor
    · calc cc = ∫ _t, cc ∂ρ := by simp
           _ ≤ _ := integral_mono (integrable_const _) hi (fun t => hlo _)
    · calc _ ≤ ∫ _t, CC ∂ρ := integral_mono hi (integrable_const _) (fun t => hhi _)
           _ = CC := by simp
  have hMmeas : Measurable M := hF.stronglyMeasurable.integral_prod_right'.measurable
  have hAmeas : Measurable A :=
    (hF.mul hF.log).stronglyMeasurable.integral_prod_right'.measurable
  have hAi : Integrable A ν := by
    apply bounded_measurable_integrable hAmeas
    intro x
    have h := norm_integral_le_of_norm_le_const (μ := ρ)
      (f := fun t => F (x, t) * Real.log (F (x, t))) (C := B)
      (ae_of_all _ (fun t => mul_log_norm_le_of_mem_positive_interval hcc (hlo _) (hhi _)))
    simpa [A, probReal_univ] using h
  have hMi : Integrable (fun x => M x * Real.log (M x)) ν :=
    bounded_measurable_integrable (hMmeas.mul hMmeas.log)
      (fun x => mul_log_norm_le_of_mem_positive_interval hcc (hMb x).1 (hMb x).2)
  exact hAi.sub hMi

/-- The accepted positive bounded product entropy theorem, expressed as a
sum of expected fiber entropies so that one-coordinate estimates can apply. -/
lemma phiEntropy_pi_le_sum_fiber {n : ℕ} {α : Fin n → Type}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (F : (∀ i, α i) → ℝ) (cc CC : ℝ) (hcc : 0 < cc) (hF : Measurable F)
    (hlo : ∀ x, cc ≤ F x) (hhi : ∀ x, F x ≤ CC) :
    phiEntropy F (Measure.pi μ) ≤
      ∑ k : Fin n, ∫ x, phiEntropy (fun t => F (Function.update x k t)) (μ k) ∂(Measure.pi μ) := by
  classical
  let B := |CC| * (|Real.log cc| + |Real.log CC|)
  have hFlog : Measurable (fun x => F x * Real.log (F x)) := hF.mul hF.log
  have hFlogb (x) : ‖F x * Real.log (F x)‖ ≤ B :=
    mul_log_norm_le_of_mem_positive_interval hcc (hlo x) (hhi x)
  have hnormF (x) : ‖F x‖ ≤ |CC| := by
    rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hcc (hlo x))]
    exact (hhi x).trans (le_abs_self CC)
  let M := fun (k : Fin n) (x : ∀ i, α i) => ∫ t, F (Function.update x k t) ∂(μ k)
  have hMlo (k : Fin n) (x : ∀ i, α i) : cc ≤ M k x := by
    have hi : Integrable (fun t => F (Function.update x k t)) (μ k) :=
      bounded_measurable_integrable (hF.comp (measurable_update x)) (fun t => hnormF _)
    calc
      cc = ∫ _t, cc ∂(μ k) := by simp
      _ ≤ _ := integral_mono (integrable_const _) hi (fun t => hlo _)
  have hMhi (k : Fin n) (x : ∀ i, α i) : M k x ≤ CC := by
    have hi : Integrable (fun t => F (Function.update x k t)) (μ k) :=
      bounded_measurable_integrable (hF.comp (measurable_update x)) (fun t => hnormF _)
    calc
      _ ≤ ∫ _t, CC ∂(μ k) := integral_mono hi (integrable_const _) (fun t => hhi _)
      _ = CC := by simp
  have hMlogi (k : Fin n) : Integrable (fun x => M k x * Real.log (M k x)) (Measure.pi μ) := by
    have hm := coordinate_average_measurable μ k hF
    apply bounded_measurable_integrable (hm.mul hm.log)
    exact fun x => mul_log_norm_le_of_mem_positive_interval hcc (hMlo k x) (hMhi k x)
  have hFlogavgi (k : Fin n) : Integrable
      (fun x => ∫ t, F (Function.update x k t) * Real.log (F (Function.update x k t)) ∂(μ k))
      (Measure.pi μ) := by
    apply bounded_measurable_integrable (coordinate_average_measurable μ k hFlog)
    intro x
    have h := norm_integral_le_of_norm_le_const (μ := μ k)
      (f := fun t => F (Function.update x k t) * Real.log (F (Function.update x k t)))
      (C := B) (ae_of_all _ (fun t => hFlogb _))
    simpa [probReal_univ] using h
  have h := entropy_n_coordinate_han_subadditivity_measure_pi_pos μ F cc CC hcc hF hlo hhi
  change phiEntropy F (Measure.pi μ) ≤ _ at h
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro k hk
  unfold phiEntropy
  rw [integral_sub (hFlogavgi k) (hMlogi k),
    integral_pi_coordinate_average μ k (fun x => F x * Real.log (F x)) hFlog hFlogb]

end HighDimStat.Concentration


namespace HighDimStat.Concentration

lemma bounded_observable_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : Integrable Z μ) {C : ℝ} (hbound : ∀ᵐ ω ∂μ, |Z ω| ≤ C) (lam : ℝ) :
    Integrable (fun ω => Real.exp (lam * Z ω)) μ := by
  refine Integrable.of_bound ((hZ.aemeasurable.const_mul lam).exp).aestronglyMeasurable
    (Real.exp (|lam| * C)) ?_
  filter_upwards [hbound] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |lam * Z ω| := le_abs_self _
    _ = |lam| * |Z ω| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hω (abs_nonneg _)

lemma bounded_observable_exp_log_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : Integrable Z μ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ ω ∂μ, |Z ω| ≤ C) (lam : ℝ) :
    Integrable (fun ω => Real.exp (lam * Z ω) * Real.log (Real.exp (lam * Z ω))) μ := by
  have he := bounded_observable_exp_integrable hZ hbound lam
  refine Integrable.of_bound
    (he.aestronglyMeasurable.mul ((hZ.aestronglyMeasurable.const_mul lam)))
    (Real.exp (|lam| * C) * (|lam| * C)) ?_ |>.congr ?_
  · filter_upwards [hbound] with ω hω
    change ‖Real.exp (lam * Z ω) * (lam * Z ω)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
    have he' : Real.exp (lam * Z ω) ≤ Real.exp (|lam| * C) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ |lam * Z ω| := le_abs_self _
        _ = |lam| * |Z ω| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hω (abs_nonneg _)
    exact mul_le_mul he' (mul_le_mul_of_nonneg_left hω (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.exp_pos _).le
  · exact ae_of_all _ (fun ω => by
      change Real.exp (lam * Z ω) * (lam * Z ω) =
        Real.exp (lam * Z ω) * Real.log (Real.exp (lam * Z ω))
      rw [Real.log_exp])


end HighDimStat.Concentration


open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

set_option maxHeartbeats 1600000

/-- A bounded observable on a product probability space has dimension-free
exponential entropy whenever its coordinate decrements have a uniform
squared-sum bound. Each reference must be independent of its own coordinate. -/
lemma product_entropy_of_sq_decrements {n : ℕ} {α : Fin n → Type}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : (∀ i, α i) → ℝ) (c : Fin n → (∀ i, α i) → ℝ)
    (hZ : Measurable Z) (hc : ∀ k, Measurable (c k))
    {C V : ℝ} (hC : 0 ≤ C) (hV : 0 ≤ V) (hZb : ∀ x, |Z x| ≤ C)
    (hclo : ∀ k x, c k x ≤ Z x)
    (hcfiber : ∀ k x t, c k (Function.update x k t) = c k x)
    (hsum : ∀ x, (∑ k, (Z x - c k x) ^ 2) ≤ V)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    phiEntropy (fun x => Real.exp (lam * Z x)) (Measure.pi μ) ≤
      lam ^ 2 / 2 * V * ∫ x, Real.exp (lam * Z x) ∂(Measure.pi μ) := by
  classical
  let F := fun x => Real.exp (lam * Z x)
  let D := fun (k : Fin n) x => (Z x - c k x) ^ 2
  let E := Real.exp (|lam| * C)
  have hF : Measurable F := (hZ.const_mul lam).exp
  have hFb (x) : ‖F x‖ ≤ E := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self (lam * Z x)).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hZb x) (abs_nonneg _))
  have hFlo (x) : Real.exp (-|lam| * C) ≤ F x := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (hZb x) (abs_nonneg lam)
    have h' := neg_abs_le (lam * Z x)
    rw [abs_mul] at h'
    nlinarith
  have hFhi (x) : F x ≤ E := by
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), F] using hFb x
  have hDb (k : Fin n) (x) : ‖D k x‖ ≤ V := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (Finset.single_le_sum (fun j _ => sq_nonneg (Z x - c j x)) (Finset.mem_univ k)).trans (hsum x)
  have hD (k : Fin n) : Measurable (D k) := (hZ.sub (hc k)).pow_const 2
  have hFDb (k : Fin n) (x) : ‖F x * D k x‖ ≤ E * V := by
    rw [norm_mul]
    exact mul_le_mul (hFb x) (hDb k x) (norm_nonneg _) (Real.exp_pos _).le
  have hFDi (k : Fin n) : Integrable (fun x => F x * D k x) (Measure.pi μ) :=
    bounded_measurable_integrable (hF.mul (hD k)) (hFDb k)
  have hcoord (k : Fin n) (x) :
      phiEntropy (fun t => F (Function.update x k t)) (μ k) ≤
        lam ^ 2 / 2 * ∫ t, F (Function.update x k t) * D k (Function.update x k t) ∂(μ k) := by
    let W := fun t => Z (Function.update x k t)
    have hWi : Integrable W (μ k) :=
      bounded_measurable_integrable (hZ.comp (measurable_update x)) (fun t => by
        simpa [Real.norm_eq_abs] using hZb (Function.update x k t))
    have hwExp := bounded_observable_exp_integrable hWi
      (ae_of_all _ (fun t => hZb (Function.update x k t))) lam
    have hwLog := bounded_observable_exp_log_integrable hWi hC
      (ae_of_all _ (fun t => hZb (Function.update x k t))) lam
    have hwZExp : Integrable (fun t => lam * W t * Real.exp (lam * W t)) (μ k) :=
      hwLog.congr (ae_of_all _ (fun t => by
        change Real.exp (lam * W t) * Real.log (Real.exp (lam * W t)) =
          lam * W t * Real.exp (lam * W t)
        rw [Real.log_exp]
        ring))
    have hwSq : Integrable (fun t => Real.exp (lam * W t) * (W t - c k x) ^ 2) (μ k) := by
      have hi : Integrable (fun t => F (Function.update x k t) * D k (Function.update x k t)) (μ k) :=
        bounded_measurable_integrable ((hF.mul (hD k)).comp (measurable_update x))
          (fun t => hFDb k (Function.update x k t))
      simpa only [F, D, hcfiber, W] using hi
    have h := entropy_exp_le_sq_gap hlam hwExp hwZExp
      (ae_of_all _ (fun t => by simpa only [W, ← hcfiber k x t] using hclo k (Function.update x k t))) hwSq
    simpa only [F, D, hcfiber, W] using h
  have hEnti (k : Fin n) : Integrable
      (fun x => phiEntropy (fun t => F (Function.update x k t)) (μ k)) (Measure.pi μ) := by
    apply bounded_positive_fiber_entropy_integrable (Measure.pi μ) (μ k)
      (hF.comp (measurable_update'.comp (measurable_fst.prodMk measurable_snd)))
      (Real.exp_pos (-|lam| * C))
    · exact fun p => hFlo _
    · exact fun p => hFhi _
  have hAvgi (k : Fin n) : Integrable
      (fun x => ∫ t, F (Function.update x k t) * D k (Function.update x k t) ∂(μ k))
      (Measure.pi μ) := by
    apply bounded_measurable_integrable (coordinate_average_measurable μ k (hF.mul (hD k)))
    intro x
    have h := norm_integral_le_of_norm_le_const (μ := μ k)
      (f := fun t => F (Function.update x k t) * D k (Function.update x k t)) (C := E * V)
      (ae_of_all _ (fun t => hFDb k _))
    simpa [probReal_univ] using h
  calc
    _ ≤ ∑ k : Fin n, ∫ x, phiEntropy (fun t => F (Function.update x k t)) (μ k) ∂(Measure.pi μ) :=
      phiEntropy_pi_le_sum_fiber μ F _ E (Real.exp_pos _) hF hFlo hFhi
    _ ≤ ∑ k : Fin n, ∫ x, lam ^ 2 / 2 *
        (∫ t, F (Function.update x k t) * D k (Function.update x k t) ∂(μ k)) ∂(Measure.pi μ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact integral_mono (hEnti k) ((hAvgi k).const_mul _) (hcoord k)
    _ = lam ^ 2 / 2 * ∑ k : Fin n, ∫ x, F x * D k x ∂(Measure.pi μ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_const_mul,
        integral_pi_coordinate_average μ k (fun x => F x * D k x) (hF.mul (hD k)) (hFDb k)]
    _ = lam ^ 2 / 2 * ∫ x, F x * (∑ k : Fin n, D k x) ∂(Measure.pi μ) := by
      rw [← integral_finsetSum _ (fun k _ => hFDi k)]
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        change (∑ k, F x * D k x) = F x * ∑ k, D k x
        rw [Finset.mul_sum])
    _ ≤ lam ^ 2 / 2 * ∫ x, F x * V ∂(Measure.pi μ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply integral_mono
      · simpa only [Finset.mul_sum] using integrable_finsetSum _ (fun k _ => hFDi k)
      · exact (bounded_measurable_integrable hF hFb).mul_const V
      · intro x
        exact mul_le_mul_of_nonneg_left (hsum x) (Real.exp_pos _).le
    _ = _ := by rw [integral_mul_const]; ring

end HighDimStat.Concentration


open MeasureTheory ProbabilityTheory HighDimStat.Concentration

theorem solution {n : ℕ} {α : Fin n → Type}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : (∀ i, α i) → ℝ) (c : Fin n → (∀ i, α i) → ℝ)
    (hZ : Measurable Z) (hc : ∀ k, Measurable (c k))
    {C V : ℝ} (hC : 0 ≤ C) (hV : 0 ≤ V) (hZb : ∀ x, |Z x| ≤ C)
    (hclo : ∀ k x, c k x ≤ Z x)
    (hcfiber : ∀ k x t, c k (Function.update x k t) = c k x)
    (hsum : ∀ x, (∑ k, (Z x - c k x) ^ 2) ≤ V)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    phiEntropy (fun x => Real.exp (lam * Z x)) (Measure.pi μ) ≤
      lam ^ 2 / 2 * V * ∫ x, Real.exp (lam * Z x) ∂(Measure.pi μ) := by
  exact product_entropy_of_sq_decrements μ Z c hZ hc hC hV hZb hclo hcfiber hsum lam hlam

#print axioms solution
