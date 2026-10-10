-- Prove2me | solution 1 for HighDimStat.TailBounds.martingale_bernstein_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-10T00:26:00.101777+00:00
-- url     : https://prove2.me/submissions/b5cad246-12d9-4456-9f8f-76c1823a1659

/-
SPDX-License-Identifier: Apache-2.0
Complete proof of the canonical corrected martingale Bernstein theorem.
All custom proof bodies are included; only canonical definitions and Mathlib
are imported. Conditional integrability, moment induction and tail optimization are reconstructed.
-/
import Mathlib
import Definitions.Def_HighDimStat_TailBounds_IsSubExponential

/- Complete module: KernelProduct -/
section

open MeasureTheory ProbabilityTheory

namespace HighDimStat.TailBounds

theorem kernel_product_integrable
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} [SFinite μ] {κ : Kernel X Y} [IsSFiniteKernel κ]
    {f : X → ℝ} {g : Y → ℝ} {C : ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y)
    (hfi : Integrable f μ)
    (hgi : ∀ᵐ x ∂μ, Integrable g (κ x))
    (hbound : ∀ᵐ x ∂μ, ∫ y, g y ∂κ x ≤ C) :
    Integrable (fun p : X × Y => f p.1 * g p.2) (μ ⊗ₘ κ) := by
  apply (Measure.integrable_compProd_iff (by fun_prop)).2
  constructor
  · filter_upwards [hgi] with x hx
    exact hx.const_mul (f x)
  · have heq : (fun x => ∫ y, ‖f x * g y‖ ∂κ x) =
        fun x => f x * ∫ y, g y ∂κ x := by
      funext x
      simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 x) (hg0 _))]
      exact integral_const_mul _ _
    rw [heq]
    apply (hfi.mul_const C).mono'
      (hf.stronglyMeasurable.mul hg.stronglyMeasurable.integral_kernel).aestronglyMeasurable
    filter_upwards [hbound] with x hx
    change ‖f x * ∫ y, g y ∂κ x‖ ≤ f x * C
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (hf0 x) (integral_nonneg hg0))]
    exact mul_le_mul_of_nonneg_left hx (hf0 x)

end HighDimStat.TailBounds

end

/- Complete module: ConditionalProduct -/
section

open MeasureTheory ProbabilityTheory

namespace HighDimStat.TailBounds

theorem conditional_product_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {f g : Ω → ℝ} {C : ℝ}
    (hf : Measurable[m] f) (hg : Measurable[mΩ] g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hbound : μ[g | m] ≤ᵐ[μ] fun _ => C) :
    Integrable (fun x => f x * g x) μ ∧
      ∫ x, f x * g x ∂μ ≤ C * ∫ x, f x ∂μ := by
  have hbtrim : μ[g | m] ≤ᵐ[μ.trim hm] fun _ => C :=
    StronglyMeasurable.ae_le_trim_of_stronglyMeasurable hm
      stronglyMeasurable_condExp stronglyMeasurable_const hbound
  have hbk : ∀ᵐ x ∂μ.trim hm, ∫ y, g y ∂condExpKernel (mΩ := mΩ) μ m x ≤ C := by
    filter_upwards [hbtrim, condExp_ae_eq_trim_integral_condExpKernel (mΩ := mΩ) hm hgi] with x hx he
    rwa [← he]
  have hcomp : Integrable g (condExpKernel (mΩ := mΩ) μ m ∘ₘ μ.trim hm) := by
    rwa [condExpKernel_comp_trim (mΩ := mΩ) hm]
  have hp := @kernel_product_integrable Ω Ω m mΩ (μ.trim hm) _
    (condExpKernel (mΩ := mΩ) μ m) _ f g C hf hg hf0 hg0
    (hfi.trim hm hf.stronglyMeasurable)
    (Measure.ae_integrable_of_integrable_comp hcomp) hbk
  rw [compProd_trim_condExpKernel (mΩ := mΩ) hm] at hp
  have hdiag : @Measurable Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag :=
    (measurable_id'' hm).prodMk measurable_id
  have hprod : Integrable (fun x => f x * g x) μ := by
    let : MeasurableSpace Ω := mΩ
    let : MeasurableSpace (Ω × Ω) := m.prod mΩ
    exact hp.comp_measurable hdiag
  refine ⟨hprod, ?_⟩
  have hce := condExp_mul_of_stronglyMeasurable_left hf.stronglyMeasurable hprod hgi
  calc
    ∫ x, f x * g x ∂μ = ∫ x, μ[fun x => f x * g x | m] x ∂μ :=
      (integral_condExp hm).symm
    _ ≤ ∫ x, C * f x ∂μ := by
      apply integral_mono_ae integrable_condExp (hfi.const_mul C)
      filter_upwards [hce, hbound] with x he hb
      change μ[f * g | m] x ≤ C * f x
      rw [he]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hb (hf0 x)
    _ = C * ∫ x, f x ∂μ := integral_const_mul _ _

end HighDimStat.TailBounds

end

/- Complete module: FiltrationMGF -/
section

open MeasureTheory ProbabilityTheory

namespace HighDimStat.TailBounds

theorem filtration_mgf_induction
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {D : ℕ → Ω → ℝ} {v : ℕ → ℝ} {ℱ : Filtration ℕ mΩ}
    (n : ℕ) (lam : ℝ)
    (h_meas : ∀ k ∈ Finset.Icc 1 n, Measurable[ℱ k] (D k))
    (h_int : ∀ k ∈ Finset.Icc 1 n,
      Integrable (fun ω => Real.exp (lam * D k ω)) μ)
    (h_bound : ∀ k ∈ Finset.Icc 1 n,
      μ[fun ω => Real.exp (lam * D k ω) | ℱ (k-1)] ≤ᵐ[μ]
        fun _ => Real.exp (v k)) :
    Integrable (fun ω => Real.exp (lam * ∑ k ∈ Finset.Icc 1 n, D k ω)) μ ∧
      ∫ ω, Real.exp (lam * ∑ k ∈ Finset.Icc 1 n, D k ω) ∂μ ≤
        Real.exp (∑ k ∈ Finset.Icc 1 n, v k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsub : Finset.Icc 1 n ⊆ Finset.Icc 1 (n+1) := by
      intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    have hn : n+1 ∈ Finset.Icc 1 (n+1) := by simp
    obtain ⟨hi, hb⟩ := ih (fun k hk => h_meas k (hsub hk))
      (fun k hk => h_int k (hsub hk)) (fun k hk => h_bound k (hsub hk))
    have hsum : Measurable[ℱ n] (fun ω => ∑ k ∈ Finset.Icc 1 n, D k ω) := by
      apply Finset.measurable_sum
      intro k hk
      exact (h_meas k (hsub hk)).mono (ℱ.mono (Finset.mem_Icc.mp hk).2) le_rfl
    have hg : Measurable (fun ω => Real.exp (lam * D (n+1) ω)) :=
      ((h_meas (n+1) hn).mono (ℱ.le (n+1)) le_rfl).const_mul lam |>.exp
    have hstep := conditional_product_bound (ℱ.le n)
      ((hsum.const_mul lam).exp) hg
      (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
      hi (h_int (n+1) hn) (by simpa using h_bound (n+1) hn)
    have heq : (fun ω => Real.exp (lam * ∑ k ∈ Finset.Icc 1 (n+1), D k ω)) =
        fun ω => Real.exp (lam * ∑ k ∈ Finset.Icc 1 n, D k ω) *
          Real.exp (lam * D (n+1) ω) := by
      funext ω
      rw [Finset.sum_Icc_succ_top (by omega), mul_add, Real.exp_add]
    rw [heq]
    refine ⟨hstep.1, hstep.2.trans ?_⟩
    calc
      Real.exp (v (n+1)) * (∫ ω, Real.exp (lam * ∑ k ∈ Finset.Icc 1 n, D k ω) ∂μ)
          ≤ Real.exp (v (n+1)) * Real.exp (∑ k ∈ Finset.Icc 1 n, v k) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = Real.exp (∑ k ∈ Finset.Icc 1 (n+1), v k) := by
        rw [Finset.sum_Icc_succ_top (by omega), Real.exp_add, mul_comm]

end HighDimStat.TailBounds

end

/- Complete module: MartingaleMGF -/
section

open MeasureTheory ProbabilityTheory

namespace HighDimStat.TailBounds

theorem admissible_of_le_scale {a A lam : ℝ} (ha : 0 ≤ a) (haA : a ≤ A)
    (hdom : A = 0 ∨ |lam| < 1 / A) : a = 0 ∨ |lam| < 1 / a := by
  by_cases ha0 : a = 0
  · exact Or.inl ha0
  right
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  rcases hdom with hA | hdom
  · exact False.elim (ha0 (le_antisymm (hA ▸ haA) ha))
  · exact hdom.trans_le (one_div_le_one_div_of_le hap haA)

theorem martingale_mgf_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {D : ℕ → Ω → ℝ} {ν α : ℕ → ℝ} {ℱ : Filtration ℕ mΩ}
    (n : ℕ) (hn : 1 ≤ n)
    (h_alpha : ∀ k ∈ Finset.Icc 1 n, 0 ≤ α k)
    (h_meas : ∀ k ∈ Finset.Icc 1 n, Measurable[ℱ k] (D k))
    (h_subexp_int : ∀ k ∈ Finset.Icc 1 n, ∀ lam : ℝ,
      (α k = 0 ∨ |lam| < 1 / α k) → Integrable (fun ω => Real.exp (lam * D k ω)) μ)
    (h_subexp : ∀ k ∈ Finset.Icc 1 n, ∀ lam : ℝ,
      (α k = 0 ∨ |lam| < 1 / α k) →
      μ[fun ω => Real.exp (lam * D k ω) | ℱ (k-1)] ≤ᵐ[μ]
        fun _ => Real.exp (lam ^ 2 * (ν k) ^ 2 / 2))
    (lam : ℝ)
    (hdom : Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α = 0 ∨
      |lam| < 1 / Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α) :
    Integrable (fun ω => Real.exp (lam * ∑ k ∈ Finset.Icc 1 n, D k ω)) μ ∧
      ∫ ω, Real.exp (lam * ∑ k ∈ Finset.Icc 1 n, D k ω) ∂μ ≤
        Real.exp (lam ^ 2 * (∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2) / 2) := by
  have hd : ∀ k ∈ Finset.Icc 1 n, α k = 0 ∨ |lam| < 1 / α k := by
    intro k hk
    exact admissible_of_le_scale (h_alpha k hk) (Finset.le_sup' α hk) hdom
  have h := filtration_mgf_induction n lam h_meas
    (fun k hk => h_subexp_int k hk lam (hd k hk))
    (fun k hk => h_subexp k hk lam (hd k hk))
  simpa only [Finset.sum_div, Finset.mul_sum] using h

end HighDimStat.TailBounds

end

/- Complete module: MartingaleSubExponential -/
section

open MeasureTheory ProbabilityTheory

namespace HighDimStat.TailBounds

theorem martingale_sum_integral_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {D : ℕ → Ω → ℝ} {ℱ : Filtration ℕ mΩ} (n : ℕ)
    (h_int : ∀ k ∈ Finset.Icc 1 n, Integrable (D k) μ)
    (h_cent : ∀ k ∈ Finset.Icc 1 n, μ[D k | ℱ (k-1)] =ᵐ[μ] 0) :
    Integrable (fun ω => ∑ k ∈ Finset.Icc 1 n, D k ω) μ ∧
      ∫ ω, ∑ k ∈ Finset.Icc 1 n, D k ω ∂μ = 0 := by
  refine ⟨integrable_finsetSum _ h_int, ?_⟩
  rw [integral_finsetSum _ h_int]
  apply Finset.sum_eq_zero
  intro k hk
  calc
    ∫ ω, D k ω ∂μ = ∫ ω, μ[D k | ℱ (k-1)] ω ∂μ :=
      (integral_condExp (ℱ.le (k-1))).symm
    _ = 0 := by rw [integral_congr_ae (h_cent k hk)]; simp

theorem martingale_isSubExponential
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {D : ℕ → Ω → ℝ} {ν α : ℕ → ℝ} {ℱ : Filtration ℕ mΩ}
    (n : ℕ) (hn : 1 ≤ n)
    (h_alpha : ∀ k ∈ Finset.Icc 1 n, 0 ≤ α k)
    (h_meas : ∀ k ∈ Finset.Icc 1 n, Measurable[ℱ k] (D k))
    (h_int : ∀ k ∈ Finset.Icc 1 n, Integrable (D k) μ)
    (h_cent : ∀ k ∈ Finset.Icc 1 n, μ[D k | ℱ (k-1)] =ᵐ[μ] 0)
    (h_subexp_int : ∀ k ∈ Finset.Icc 1 n, ∀ lam : ℝ,
      (α k = 0 ∨ |lam| < 1 / α k) → Integrable (fun ω => Real.exp (lam * D k ω)) μ)
    (h_subexp : ∀ k ∈ Finset.Icc 1 n, ∀ lam : ℝ,
      (α k = 0 ∨ |lam| < 1 / α k) →
      μ[fun ω => Real.exp (lam * D k ω) | ℱ (k-1)] ≤ᵐ[μ]
        fun _ => Real.exp (lam ^ 2 * (ν k) ^ 2 / 2)) :
    IsSubExponential (fun ω => ∑ k ∈ Finset.Icc 1 n, D k ω) μ
      (Real.sqrt (∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2))
      (Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α) := by
  obtain ⟨hi, hz⟩ := martingale_sum_integral_zero n h_int h_cent
  have hv : 0 ≤ ∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  refine ⟨hi, ?_, ?_⟩
  · intro lam hdom
    simpa only [hz, sub_zero] using
      (martingale_mgf_bound n hn h_alpha h_meas h_subexp_int h_subexp lam hdom).1
  · intro lam hdom
    simpa only [hz, sub_zero, Real.sq_sqrt hv, mul_comm (∑ k ∈ Finset.Icc 1 n, (ν k)^2)] using
      (martingale_mgf_bound n hn h_alpha h_meas h_subexp_int h_subexp lam hdom).2

end HighDimStat.TailBounds

end

/- Complete module: BernsteinChernoff -/
section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace HighDimStat.TailBounds.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma absolute_chernoff {X : Ω → ℝ} {V A lam t : ℝ}
    (hlam : 0 ≤ lam) (hdom : A = 0 ∨ |lam| < 1 / A)
    (hi : ∀ z : ℝ, (A = 0 ∨ |z| < 1 / A) →
      Integrable (fun ω => Real.exp (z * X ω)) μ)
    (hb : ∀ z : ℝ, (A = 0 ∨ |z| < 1 / A) →
      (∫ ω, Real.exp (z * X ω) ∂μ) ≤ Real.exp (z ^ 2 * V / 2)) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * Real.exp (-lam * t + lam ^ 2 * V / 2) := by
  have hdneg : A = 0 ∨ |-lam| < 1 / A := by simpa only [abs_neg] using hdom
  have hp := measure_ge_le_exp_mul_mgf (μ := μ) (X := X) t hlam (hi lam hdom)
  have hn := measure_le_le_exp_mul_mgf (μ := μ) (X := X) (-t) (neg_nonpos.mpr hlam)
    (hi (-lam) hdneg)
  have hp' : μ.real {ω | t ≤ X ω} ≤ Real.exp (-lam * t + lam ^ 2 * V / 2) := by
    calc
      _ ≤ Real.exp (-lam * t) * (∫ ω, Real.exp (lam * X ω) ∂μ) := hp
      _ ≤ Real.exp (-lam * t) * Real.exp (lam ^ 2 * V / 2) :=
        mul_le_mul_of_nonneg_left (hb lam hdom) (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have hn' : μ.real {ω | X ω ≤ -t} ≤ Real.exp (-lam * t + lam ^ 2 * V / 2) := by
    calc
      _ ≤ Real.exp (-(-lam) * (-t)) * (∫ ω, Real.exp ((-lam) * X ω) ∂μ) := hn
      _ ≤ Real.exp (-(-lam) * (-t)) * Real.exp ((-lam) ^ 2 * V / 2) :=
        mul_le_mul_of_nonneg_left (hb (-lam) hdneg) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have he : {ω | t ≤ |X ω|} = {ω | t ≤ X ω} ∪ {ω | X ω ≤ -t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
    constructor <;> intro h
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
  rw [he]
  exact (measureReal_union_le _ _).trans (by linarith)

lemma scalar_endpoint {p V u t : ℝ} (hu : 0 < u)
    (h : ∀ lam : ℝ, 0 < lam → lam < u → p ≤ 2 * Real.exp (-lam * t + lam ^ 2 * V / 2)) :
    p ≤ 2 * Real.exp (-u * t + u ^ 2 * V / 2) := by
  have hc : Continuous (fun lam : ℝ => 2 * Real.exp (-lam * t + lam ^ 2 * V / 2)) := by
    fun_prop
  apply ge_of_tendsto (hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[Set.Iio u] u ≤ 𝓝 u))
  filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds hu).filter_mono nhdsWithin_le_nhds] with lam hlt hpos
  exact h lam hpos hlt

end HighDimStat.TailBounds.Proof

end

/- Complete module: BernsteinScalar -/
section

namespace HighDimStat.TailBounds.Proof

lemma scalar_bernstein {p V A t : ℝ} (hp : p ≤ 1) (hV : 0 ≤ V) (hA : 0 ≤ A)
    (ht : 0 ≤ t)
    (h : ∀ lam : ℝ, 0 ≤ lam → (A = 0 ∨ |lam| < 1 / A) →
      p ≤ 2 * Real.exp (-lam * t + lam ^ 2 * V / 2)) :
    p ≤ if A = 0 ∨ t ≤ V / A then 2 * Real.exp (-(t ^ 2) / (2 * V))
      else 2 * Real.exp (-t / (2 * A)) := by
  by_cases ht0 : t = 0
  · subst t
    simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_div, neg_zero,
      Real.exp_zero, mul_one, ite_self]
    exact hp.trans (by norm_num)
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  by_cases hreg : A = 0 ∨ t ≤ V / A
  · rw [if_pos hreg]
    by_cases hV0 : V = 0
    · simp only [hV0, mul_zero, div_zero, Real.exp_zero, mul_one]
      exact hp.trans (by norm_num)
    have hVp : 0 < V := lt_of_le_of_ne hV (Ne.symm hV0)
    have hu : 0 < t / V := div_pos htpos hVp
    have hb : p ≤ 2 * Real.exp (-(t / V) * t + (t / V) ^ 2 * V / 2) := by
      apply scalar_endpoint hu
      intro lam hlam hlamu
      apply h lam hlam.le
      rcases hreg with hAz | hta
      · exact Or.inl hAz
      · by_cases hAz : A = 0
        · exact Or.inl hAz
        have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
        right
        rw [abs_of_pos hlam]
        apply hlamu.trans_le
        apply (div_le_div_iff₀ hVp hAp).mpr
        have hh := (le_div_iff₀ hAp).mp hta
        simpa only [one_mul] using hh
    have he : -(t / V) * t + (t / V) ^ 2 * V / 2 = -(t ^ 2) / (2 * V) := by
      field_simp
      ring
    rwa [he] at hb
  · rw [if_neg hreg]
    have hAz : A ≠ 0 := fun hz => hreg (Or.inl hz)
    have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    have hta : V / A < t := lt_of_not_ge (fun ht' => hreg (Or.inr ht'))
    have hb : p ≤ 2 * Real.exp (-(1 / A) * t + (1 / A) ^ 2 * V / 2) := by
      apply scalar_endpoint (one_div_pos.mpr hAp)
      intro lam hlam hlamu
      exact h lam hlam.le (Or.inr (by simpa only [abs_of_pos hlam] using hlamu))
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have hvta : V < t * A := (div_lt_iff₀ hAp).mp hta
    have he : -(1 / A) * t + (1 / A) ^ 2 * V / 2 = (V - 2 * t * A) / (2 * A ^ 2) := by
      field_simp
      ring
    rw [he]
    apply (div_le_iff₀ (show 0 < 2 * A ^ 2 by positivity)).mpr
    have hh : -t / (2 * A) * (2 * A ^ 2) = -t * A := by
      field_simp
    rw [hh]
    linarith

end HighDimStat.TailBounds.Proof

end

/- Complete module: BernsteinTail -/
section

open MeasureTheory

namespace HighDimStat.TailBounds.Proof

lemma bernstein_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {V A : ℝ} (hV : 0 ≤ V) (hA : 0 ≤ A)
    (hi : ∀ z : ℝ, (A = 0 ∨ |z| < 1 / A) →
      Integrable (fun ω => Real.exp (z * X ω)) μ)
    (hb : ∀ z : ℝ, (A = 0 ∨ |z| < 1 / A) →
      (∫ ω, Real.exp (z * X ω) ∂μ) ≤ Real.exp (z ^ 2 * V / 2))
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤
      if A = 0 ∨ t ≤ V / A then 2 * Real.exp (-(t ^ 2) / (2 * V))
      else 2 * Real.exp (-t / (2 * A)) := by
  apply scalar_bernstein measureReal_le_one hV hA ht
  intro lam hlam hdom
  exact absolute_chernoff hlam hdom hi hb

end HighDimStat.TailBounds.Proof

end

/- Complete module: BernsteinRoot -/
section

open MeasureTheory

namespace HighDimStat.TailBounds

/-- **Theorem 2.19** (Martingale Bernstein bound), Wainwright, *High-Dimensional Statistics*
(2019), p. 35, Eq. (2.28). Let `{(Dk,Fk)}` be a martingale difference sequence (realized as:
`D k` is `ℱ k`-measurable and `E[D k | ℱ (k-1)] = 0`, for `k = 1,...,n`), and suppose
`E[e^{λDk} | ℱ(k-1)] ≤ e^{λ²νk²/2}` a.s. for `|λ| < 1/αk`, where the scale parameters `αk`
are **nonnegative** (Definition 2.7: sub-exponential parameters `(ν, α)` are nonnegative, with
`1/0 = +∞`). Then (a) `∑Dk` is sub-exponential with parameters `(√(∑νk²), α* := max αk)`, and
(b) `∑Dk` satisfies the two-regime concentration inequality (2.28), where the Gaussian regime
`t ≤ ∑νk²/α*` is read with the book's convention `1/0 = +∞` (so it covers every `t ≥ 0` when
`α* = 0`). Explicit `Integrable` hypotheses on each `D k` and on each conditional-MGF
exponential block Mathlib's `condExp`/Bochner-integral junk value `0`.

Corrections relative to the retired version: `h_alpha : 0 ≤ α k` was missing (with `α k < 0`
the guard `α k = 0 ∨ |λ| < 1/α k` is unsatisfiable, so the MGF hypothesis was vacuous), and the
regime split `t ≤ ∑νk²/α*` silently became `t ≤ 0` when `α* = 0` (Lean's `x/0 = 0`), which
collapsed part (b) to the trivial bound `2` in the sub-Gaussian case `α* = 0`. -/
theorem martingale_bernstein_bound_v2 {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {D : ℕ → Ω → ℝ} {ν α : ℕ → ℝ} {ℱ : Filtration ℕ mΩ}
    (n : ℕ) (hn : 1 ≤ n)
    (h_alpha : ∀ k ∈ Finset.Icc 1 n, 0 ≤ α k)
    (h_meas : ∀ k ∈ Finset.Icc 1 n, Measurable[ℱ k] (D k))
    (h_int : ∀ k ∈ Finset.Icc 1 n, Integrable (D k) μ)
    (h_cent : ∀ k ∈ Finset.Icc 1 n, μ[D k | ℱ (k - 1)] =ᵐ[μ] 0)
    (h_subexp_int : ∀ k ∈ Finset.Icc 1 n, ∀ lam : ℝ, (α k = 0 ∨ |lam| < 1 / α k) →
      Integrable (fun ω => Real.exp (lam * D k ω)) μ)
    (h_subexp : ∀ k ∈ Finset.Icc 1 n, ∀ lam : ℝ, (α k = 0 ∨ |lam| < 1 / α k) →
      (μ[fun ω => Real.exp (lam * D k ω) | ℱ (k - 1)]) ≤ᵐ[μ]
        fun _ => Real.exp (lam ^ 2 * (ν k) ^ 2 / 2)) :
    IsSubExponential (fun ω => ∑ k ∈ Finset.Icc 1 n, D k ω) μ
        (Real.sqrt (∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2))
        (Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α)
    ∧
    ∀ t : ℝ, 0 ≤ t →
      μ.real {ω | t ≤ |∑ k ∈ Finset.Icc 1 n, D k ω|} ≤
        if (Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α = 0 ∨
            t ≤ (∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2) /
              (Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α))
        then 2 * Real.exp (-(t ^ 2) / (2 * ∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2))
        else 2 * Real.exp (-t / (2 * Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α))  := by
  constructor
  · exact martingale_isSubExponential n hn h_alpha h_meas h_int h_cent h_subexp_int h_subexp
  · intro t ht
    apply Proof.bernstein_tail (Finset.sum_nonneg (fun k _ => sq_nonneg (ν k)))
      (le_trans (h_alpha 1 (by simp [hn]))
        (Finset.le_sup' α (by simp [hn])))
    · intro lam hlam
      exact (martingale_mgf_bound n hn h_alpha h_meas h_subexp_int h_subexp lam hlam).1
    · intro lam hlam
      exact (martingale_mgf_bound n hn h_alpha h_meas h_subexp_int h_subexp lam hlam).2
    · exact ht

end HighDimStat.TailBounds

open HighDimStat.TailBounds

theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {D : ℕ → Ω → ℝ} {ν α : ℕ → ℝ} {ℱ : Filtration ℕ mΩ}
    (n : ℕ) (hn : 1 ≤ n)
    (h_alpha : ∀ k ∈ Finset.Icc 1 n, 0 ≤ α k)
    (h_meas : ∀ k ∈ Finset.Icc 1 n, Measurable[ℱ k] (D k))
    (h_int : ∀ k ∈ Finset.Icc 1 n, Integrable (D k) μ)
    (h_cent : ∀ k ∈ Finset.Icc 1 n, μ[D k | ℱ (k - 1)] =ᵐ[μ] 0)
    (h_subexp_int : ∀ k ∈ Finset.Icc 1 n, ∀ lam : ℝ, (α k = 0 ∨ |lam| < 1 / α k) →
      Integrable (fun ω => Real.exp (lam * D k ω)) μ)
    (h_subexp : ∀ k ∈ Finset.Icc 1 n, ∀ lam : ℝ, (α k = 0 ∨ |lam| < 1 / α k) →
      (μ[fun ω => Real.exp (lam * D k ω) | ℱ (k - 1)]) ≤ᵐ[μ]
        fun _ => Real.exp (lam ^ 2 * (ν k) ^ 2 / 2)) :
    IsSubExponential (fun ω => ∑ k ∈ Finset.Icc 1 n, D k ω) μ
        (Real.sqrt (∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2))
        (Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α)
    ∧
    ∀ t : ℝ, 0 ≤ t →
      μ.real {ω | t ≤ |∑ k ∈ Finset.Icc 1 n, D k ω|} ≤
        if (Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α = 0 ∨
            t ≤ (∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2) /
              (Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α))
        then 2 * Real.exp (-(t ^ 2) / (2 * ∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2))
        else 2 * Real.exp (-t / (2 * Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α))  := by
  exact martingale_bernstein_bound_v2 n hn h_alpha h_meas h_int h_cent h_subexp_int h_subexp

end
