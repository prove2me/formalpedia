-- Prove2me | solution 1 for OAI.Rokhlin.polynomial_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:01:50.000782+00:00
-- url     : https://prove2.me/submissions/07088010-dd28-4d00-a61b-7a65cfd32543

import Mathlib
import Definitions.Def_OAIQ3Ro001

section
-- module Solutions.OAIQ3_Rok.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Foundations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Rokhlin

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

section

namespace ProjectiveCharacters
variable {Y L : Type*} [MeasurableSpace Y] [AddCommGroup L]
  {η : Measure Y} [IsProbabilityMeasure η] {χ : L → Y → ℂ}
  (hχ : ProjectiveCharacters η χ)
include hχ

omit [IsProbabilityMeasure η] in

theorem conjugate (l : L) : ∃ c : ℂ, ‖c‖ = 1 ∧
    (fun y => conj (χ l y)) =ᵐ[η] (fun y => c * χ (-l) y) := by
  obtain ⟨c, hc, hm⟩ := hχ.mul (-l) l
  refine ⟨c⁻¹, by simp [hc], ?_⟩
  filter_upwards [hm, hχ.zero, hχ.modulus l] with y hy h0 hn
  simp only [neg_add_cancel, h0, mul_one] at hy
  have hcn : c ≠ 0 := by intro hz; simp [hz] at hc
  have hln : χ l y ≠ 0 := by intro hz; simp [hz] at hn
  rw [← Complex.inv_eq_conj hn]
  apply (mul_right_cancel₀ hln)
  rw [inv_mul_cancel₀ hln, mul_assoc, hy, inv_mul_cancel₀ hcn]

end ProjectiveCharacters

end

open MeasureTheory Filter
open scoped BigOperators Topology

section
open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate

theorem exists_aligning_phase (z : ℂ) : ∃ ω : ℂ, ‖ω‖ = 1 ∧ (ω * z).re = ‖z‖ := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  · refine ⟨conj z / (‖z‖ : ℂ), ?_, ?_⟩
    · simp [hz]
    · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      rw [div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self, Complex.div_ofReal_re,
        Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      field_simp

end

open MeasureTheory Filter
open scoped Topology InnerProductSpace ComplexConjugate


section Hilbert
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : ι → H →ₗᵢ[ℂ] H) (l : Filter ι) (e : H)

theorem isClosed_mixing_right (f : H) :
    IsClosed {g : H | Tendsto (fun i => inner ℂ f (U i g)) l
      (𝓝 (inner ℂ f e * inner ℂ e g))} := by
  apply Equicontinuous.isClosed_setOfPred_tendsto
  · apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ ‖f‖₊
    intro i
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← inner_sub_right]
    calc
      ‖inner ℂ f (U i x - U i y)‖ ≤ ‖f‖ * ‖U i x - U i y‖ := norm_inner_le_norm _ _
      _ = ‖f‖₊ * dist x y := by rw [← map_sub, LinearIsometry.norm_map, dist_eq_norm]; rfl
  · exact continuous_const.mul (continuous_const.inner continuous_id)

theorem isClosed_mixing_left (g : H) :
    IsClosed {f : H | Tendsto (fun i => inner ℂ f (U i g)) l
      (𝓝 (inner ℂ f e * inner ℂ e g))} := by
  apply Equicontinuous.isClosed_setOfPred_tendsto
  · apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ ‖g‖₊
    intro i
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← inner_sub_left]
    calc
      ‖inner ℂ (x - y) (U i g)‖ ≤ ‖x - y‖ * ‖U i g‖ := norm_inner_le_norm _ _
      _ = ‖g‖₊ * dist x y := by rw [LinearIsometry.norm_map, dist_eq_norm]; exact mul_comm _ _
  · exact (continuous_id.inner continuous_const).mul continuous_const
end Hilbert
section

variable {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (t : ι → Ω → Ω) (ht : ∀ i, MeasurePreserving (t i) μ μ) (l : Filter ι)

theorem mixing_L2
    (hmix : ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
      Tendsto (fun i => μ (A ∩ t i ⁻¹' B)) l (𝓝 (μ A * μ B)))
    (f g : Lp ℂ 2 μ) :
    Tendsto (fun i => inner ℂ f ((Lp.compMeasurePreservingₗᵢ ℂ (t i) (ht i)) g)) l
      (𝓝 (inner ℂ f (probabilityOne (μ := μ)) *
        inner ℂ (probabilityOne (μ := μ)) g)) := by
  let U := fun i => Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ (t i) (ht i)
  let e : Lp ℂ 2 μ := probabilityOne
  change Tendsto (fun i => inner ℂ f (U i g)) l (𝓝 (inner ℂ f e * inner ℂ e g))
  have hbase (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B)
      (a b : ℂ) : Tendsto (fun i => inner ℂ
        (indicatorConstLp 2 hA (measure_ne_top _ _) a)
        (U i (indicatorConstLp 2 hB (measure_ne_top _ _) b))) l
      (𝓝 (inner ℂ (indicatorConstLp 2 hA (measure_ne_top _ _) a) e *
        inner ℂ e (indicatorConstLp 2 hB (measure_ne_top _ _) b))) := by
    have hreal := (ENNReal.tendsto_toReal (by finiteness : μ A * μ B ≠ ⊤)).comp
      (hmix A B hA hB)
    have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    have hc := hcomplex.mul_const (conj a * b)
    convert hc using 1
    · funext i
      change inner ℂ (indicatorConstLp 2 hA _ a)
        (Lp.compMeasurePreserving (t i) (ht i) (indicatorConstLp 2 hB _ b)) = _
      rw [Lp.indicatorConstLp_compMeasurePreserving,
        L2.inner_indicatorConstLp_indicatorConstLp]
      simp [RCLike.inner_apply, measureReal_def, mul_comm]
    · dsimp [e, probabilityOne]
      rw [L2.inner_indicatorConstLp_indicatorConstLp,
        L2.inner_indicatorConstLp_indicatorConstLp]
      congr 1
      simp [RCLike.inner_apply, ENNReal.toReal_mul, measureReal_def, Algebra.smul_def]
      ring
  have hfirst (A : Set Ω) (hA : MeasurableSet A) (a : ℂ) :
      ∀ g : Lp ℂ 2 μ, Tendsto (fun i => inner ℂ
        (indicatorConstLp 2 hA (measure_ne_top _ _) a) (U i g)) l
        (𝓝 (inner ℂ (indicatorConstLp 2 hA (measure_ne_top _ _) a) e * inner ℂ e g)) := by
    refine Lp.induction (by norm_num : (2 : ENNReal) ≠ ⊤) _ ?_ ?_ ?_
    · intro b B hB _
      exact hbase A B hA hB a b
    · intro f g hf hg _ h₁ h₂
      simpa only [map_add, inner_add_right, mul_add] using h₁.add h₂
    · exact isClosed_mixing_right U l e _
  have hall : ∀ f : Lp ℂ 2 μ, ∀ g : Lp ℂ 2 μ,
      Tendsto (fun i => inner ℂ f (U i g)) l (𝓝 (inner ℂ f e * inner ℂ e g)) := by
    refine Lp.induction (by norm_num : (2 : ENNReal) ≠ ⊤) _ ?_ ?_ ?_
    · intro a A hA _
      exact hfirst A hA a
    · intro f g hf hg _ h₁ h₂ w
      simpa only [inner_add_left, add_mul] using (h₁ w).add (h₂ w)
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter (fun g => isClosed_mixing_left U l e g)
  exact hall f g

theorem inner_probabilityOne (f : Lp ℂ 2 μ) :
    inner ℂ (probabilityOne (μ := μ)) f = ∫ y, f y ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
    (hμs := measure_ne_top μ Set.univ) (c := (1 : ℂ))] with y hy
  change inner ℂ ((indicatorConstLp 2 MeasurableSet.univ
    (measure_ne_top μ Set.univ) (1 : ℂ)) y) (f y) = f y
  rw [hy]
  simp

include ht in

theorem mixing_integral_coupling {Y : Type*} [MeasurableSpace Y]
    {η : Measure Y} [IsProbabilityMeasure η] (x : Y → Ω)
    (hx : MeasurePreserving x η μ)
    (hmix : ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
      Tendsto (fun i => μ (A ∩ t i ⁻¹' B)) l (𝓝 (μ A * μ B)))
    {F : Ω → ℂ} (hF : MemLp F 2 μ) (hF0 : ∫ z, F z ∂μ = 0)
    {q : Y → ℂ} (hq : MemLp q 2 η) :
    Tendsto (fun i => ∫ y, F (t i (x y)) * conj (q y) ∂η) l (𝓝 0) := by
  let V := (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ x hx).toContinuousLinearMap
  have hm := mixing_L2 t ht l hmix (V.adjoint (hq.toLp q)) (hF.toLp F)
  have hmean : inner ℂ (probabilityOne (μ := μ)) (hF.toLp F) = 0 := by
    rw [inner_probabilityOne]
    exact (integral_congr_ae hF.coeFn_toLp).trans hF0
  rw [hmean, mul_zero] at hm
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def]
  apply integral_congr_ae
  have h₁ := Lp.coeFn_compMeasurePreserving
    (Lp.compMeasurePreserving (t i) (ht i) (hF.toLp F)) hx
  have h₂ := hx.quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving (hF.toLp F) (ht i))
  have h₃ := (ht i).quasiMeasurePreserving.ae_eq_comp hF.coeFn_toLp
  have h₄ := hx.quasiMeasurePreserving.ae_eq_comp h₃
  filter_upwards [hq.coeFn_toLp, h₁, h₂, h₄] with y hy h1 h2 h4
  change F (t i (x y)) * conj (q y) =
    inner ℂ ((hq.toLp q) y)
      ((Lp.compMeasurePreserving x hx
        (Lp.compMeasurePreserving (t i) (ht i) (hF.toLp F))) y)
  rw [hy, h1, h2, h4]
  rfl

end

open Filter
open scoped BigOperators Topology InnerProductSpace

section

section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_cesaro_le (v : ℕ → E) (N : ℕ) :
    ‖cesaro v N‖ ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖v n‖ := by
  rw [cesaro, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (N : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

theorem norm_cesaro_shift_sub_le (v : ℕ → E) {C : ℝ}
    (hv : ∀ n, ‖v n‖ ≤ C) (s N : ℕ) :
    ‖cesaro (fun n => v (n + s)) N - cesaro v N‖ ≤
      (N : ℝ)⁻¹ * (2 * s * C) := by
  have heq : (∑ n ∈ Finset.range N, v (n + s)) - ∑ n ∈ Finset.range N, v n =
      (∑ n ∈ Finset.range s, v (n + N)) - ∑ n ∈ Finset.range s, v n := by
    have h₁ := Finset.sum_range_add v N s
    have h₂ := Finset.sum_range_add v s N
    rw [Nat.add_comm s N] at h₂
    simp only [Nat.add_comm] at h₁ h₂
    rw [h₁] at h₂
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using h₂.symm
  calc
    ‖cesaro (fun n => v (n + s)) N - cesaro v N‖ =
        (N : ℝ)⁻¹ * ‖(∑ n ∈ Finset.range s, v (n + N)) -
          ∑ n ∈ Finset.range s, v n‖ := by
      rw [cesaro, cesaro, ← smul_sub, heq, norm_smul,
        Real.norm_of_nonneg (by positivity : 0 ≤ (N : ℝ)⁻¹)]
    _ ≤ (N : ℝ)⁻¹ * ((∑ n ∈ Finset.range s, ‖v (n + N)‖) +
          ∑ n ∈ Finset.range s, ‖v n‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sub_le _ _).trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _))
    _ ≤ (N : ℝ)⁻¹ * ((∑ _ ∈ Finset.range s, C) + ∑ _ ∈ Finset.range s, C) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (Finset.sum_le_sum (fun n _ => hv (n + N)))
        (Finset.sum_le_sum (fun n _ => hv n))
    _ = (N : ℝ)⁻¹ * (2 * s * C) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

theorem cesaro_shift_sub_tendsto_zero (v : ℕ → E) {C : ℝ}
    (hv : ∀ n, ‖v n‖ ≤ C) (s : ℕ) :
    Tendsto (fun N => cesaro (fun n => v (n + s)) N - cesaro v N) atTop (𝓝 0) := by
  apply squeeze_zero_norm (norm_cesaro_shift_sub_le v hv s)
  simpa using (tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).mul_const (2 * s * C)

theorem cesaro_finset_sum {ι : Type*} (s : Finset ι) (v : ι → ℕ → E) (N : ℕ) :
    cesaro (fun n => ∑ i ∈ s, v i n) N = ∑ i ∈ s, cesaro (v i) N := by
  simp only [cesaro, Finset.smul_sum]
  rw [Finset.sum_comm]

theorem cesaro_smul (c : ℝ) (v : ℕ → E) (N : ℕ) :
    cesaro (fun n => c • v n) N = c • cesaro v N := by
  unfold cesaro
  rw [← Finset.smul_sum]
  exact smul_comm _ _ _

theorem cesaro_smoothing_sub_tendsto_zero (v : ℕ → E) {C : ℝ}
    (hv : ∀ n, ‖v n‖ ≤ C) (H : ℕ) (hH : H ≠ 0) (r : Fin H → ℕ) :
    Tendsto (fun N => cesaro (fun n => (H : ℝ)⁻¹ • ∑ a : Fin H, v (n + r a)) N -
      cesaro v N) atTop (𝓝 0) := by
  have h := (tendsto_finsetSum Finset.univ (fun (a : Fin H) _ =>
    cesaro_shift_sub_tendsto_zero v hv (r a))).const_smul (H : ℝ)⁻¹
  simp only [Finset.sum_const_zero, smul_zero] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext N
  rw [cesaro_smul, cesaro_finset_sum]
  rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hH), one_smul]

end Normed

theorem cesaro_mono {f g : ℕ → ℝ} (h : ∀ n, f n ≤ g n) (N : ℕ) :
    cesaro f N ≤ cesaro g N := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n _ => h n)) (by positivity)

theorem cesaro_le_bound {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n, f n ≤ C) (N : ℕ) : cesaro f N ≤ C := by
  by_cases hN : N = 0
  · simpa [cesaro, hN] using hC
  · exact (cesaro_mono h N).trans_eq (by simp [cesaro, hN])

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_cesaro_sq_le (v : ℕ → E) (N : ℕ) :
    ‖cesaro v N‖ ^ 2 ≤ cesaro (fun n => ‖v n‖ ^ 2) N := by
  by_cases hN : N = 0
  · simp [cesaro, hN]
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
    (fun n => ‖v n‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one] at hs
  have hnorm := norm_cesaro_le v N
  have hsquare : ‖cesaro v N‖ ^ 2 ≤
      (N : ℝ)⁻¹ ^ 2 * (∑ n ∈ Finset.range N, ‖v n‖)^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc
    ‖cesaro v N‖ ^ 2 ≤ (N : ℝ)⁻¹ ^ 2 * (∑ n ∈ Finset.range N, ‖v n‖)^2 := hsquare
    _ ≤ (N : ℝ)⁻¹ ^ 2 * ((∑ n ∈ Finset.range N, ‖v n‖^2) * N) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = cesaro (fun n => ‖v n‖ ^ 2) N := by
      simp only [cesaro, smul_eq_mul]
      field_simp

theorem norm_finite_mean_sq (v : ℕ → E) (H : ℕ) (r : Fin H → ℕ) (n : ℕ) :
    ‖(H : ℝ)⁻¹ • ∑ a : Fin H, v (n + r a)‖ ^ 2 =
      (H : ℝ)⁻¹ ^ 2 * ∑ a : Fin H, ∑ b : Fin H,
        inner ℝ (v (n + r a)) (v (n + r b)) := by
  rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (H : ℝ)⁻¹), mul_pow,
    ← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum]
  rw [Finset.sum_comm]

theorem norm_smoothed_cesaro_sq_le (v : ℕ → E) (H N : ℕ) (r : Fin H → ℕ) :
    ‖cesaro (fun n => (H : ℝ)⁻¹ • ∑ a : Fin H, v (n + r a)) N‖ ^ 2 ≤
      (H : ℝ)⁻¹ ^ 2 * ∑ a : Fin H, ∑ b : Fin H,
        cesaro (fun n => inner ℝ (v (n + r a)) (v (n + r b))) N := by
  convert norm_cesaro_sq_le (fun n => (H : ℝ)⁻¹ • ∑ a : Fin H, v (n + r a)) N using 1
  all_goals try with_reducible_and_instances rfl
  simp_rw [norm_finite_mean_sq]
  change _ = cesaro (fun n => ((H : ℝ)⁻¹ ^ 2) • ∑ a : Fin H, ∑ b : Fin H,
    inner ℝ (v (n + r a)) (v (n + r b))) N
  rw [cesaro_smul, cesaro_finset_sum]
  simp_rw [cesaro_finset_sum, smul_eq_mul]

theorem shifted_lag_cesaro_bound (v : ℕ → E) {C : ℝ} (hv : ∀ n, ‖v n‖ ≤ C)
    {c : ℕ → ℝ} (hc : LagCesaroBound v c) (s h : ℕ) (hh : 0 < h)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N in atTop,
    cesaro (fun n => |inner ℝ (v (n + s)) (v (n + s + h))|) N ≤ c h + ε := by
  have hC : 0 ≤ C := (norm_nonneg (v 0)).trans (hv 0)
  have hb : ∀ n, ‖|inner ℝ (v n) (v (n + h))|‖ ≤ C ^ 2 := by
    intro n
    rw [Real.norm_eq_abs, abs_abs, ← Real.norm_eq_abs]
    exact (norm_inner_le_norm _ _).trans
      (by simpa only [pow_two] using mul_le_mul (hv n) (hv (n + h)) (norm_nonneg _) hC)
  have hs := cesaro_shift_sub_tendsto_zero _ hb s
  have he := hs.eventually_lt_const (half_pos hε)
  filter_upwards [he, hc h hh (ε / 2) (half_pos hε)] with N hshift hbase
  change cesaro (fun n => |inner ℝ (v (n + s)) (v (n + s + h))|) N -
    cesaro (fun n => |inner ℝ (v n) (v (n + h))|) N < ε / 2 at hshift
  linarith

theorem pair_cesaro_bound (v : ℕ → E) {C : ℝ} (hv : ∀ n, ‖v n‖ ≤ C)
    {c : ℕ → ℝ} (hc : LagCesaroBound v c) (a b : ℕ) (hab : a ≠ b)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N in atTop,
    cesaro (fun n => inner ℝ (v (n + a)) (v (n + b))) N ≤ c (Nat.dist a b) + ε := by
  rcases le_total a b with hle | hle
  · have he := shifted_lag_cesaro_bound v hv hc a (b - a) (by omega) ε hε
    filter_upwards [he] with N hN
    have hsub : ∀ n, n + a + (b - a) = n + b := by omega
    simp_rw [hsub, ← Nat.dist_eq_sub_of_le hle] at hN
    exact (cesaro_mono (fun n => le_abs_self _) N).trans hN
  · have he := shifted_lag_cesaro_bound v hv hc b (a - b) (by omega) ε hε
    filter_upwards [he] with N hN
    have hsub : ∀ n, n + b + (a - b) = n + a := by omega
    simp_rw [hsub, ← Nat.dist_eq_sub_of_le_right hle] at hN
    exact (cesaro_mono (fun n => (real_inner_comm _ _).le.trans (le_abs_self _)) N).trans hN

theorem van_der_corput (v : ℕ → E) {C : ℝ} (hv : ∀ n, ‖v n‖ ≤ C)
    {c : ℕ → ℝ} (hc : LagCesaroBound v c) (hclim : Tendsto c atTop (𝓝 0)) :
    Tendsto (cesaro v) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0 < ε ^ 2 / 16 := by positivity
  have hinv : Tendsto (fun H : ℕ => (H : ℝ)⁻¹ * C ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).mul_const (C ^ 2)
  obtain ⟨H, hHpos, hHsmall⟩ :=
    ((eventually_ge_atTop 1).and (hinv.eventually_lt_const hδ)).exists
  have hH : H ≠ 0 := by omega
  have hHR : (H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hH
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (hclim.eventually_lt_const (half_pos hδ))
  let L := L₀ + 1
  let r (a : Fin H) := a.val * L
  have hpairs : ∀ a b : Fin H, ∀ᶠ N in atTop,
      cesaro (fun n => inner ℝ (v (n + r a)) (v (n + r b))) N ≤
        (if a = b then C ^ 2 else 0) + ε ^ 2 / 16 := by
    intro a b
    by_cases hab : a = b
    · subst b
      apply Eventually.of_forall
      intro N
      simp only [ite_true]
      have hdiag : cesaro (fun n => inner ℝ (v (n + r a)) (v (n + r a))) N ≤ C ^ 2 := by
        apply cesaro_le_bound (sq_nonneg C)
        intro n
        rw [real_inner_self_eq_norm_sq]
        exact pow_le_pow_left₀ (norm_nonneg _) (hv _) 2
      linarith
    · have hval : a.val ≠ b.val := fun h => hab (Fin.ext h)
      have hdist : L₀ ≤ Nat.dist (r a) (r b) := by
        dsimp [r]
        rw [Nat.dist_mul_right]
        have hh : 1 ≤ Nat.dist a.val b.val := Nat.dist_pos_of_ne hval
        have hh' := Nat.mul_le_mul_right L hh
        simp only [one_mul] at hh'
        exact (by dsimp [L]; omega : L₀ ≤ L).trans hh'
      have hr : r a ≠ r b := by
        intro hh
        have hh' := Nat.eq_of_mul_eq_mul_right (by dsimp [L]; omega : 0 < L) hh
        exact hval hh'
      filter_upwards [pair_cesaro_bound v hv hc (r a) (r b) hr
        (ε ^ 2 / 16 / 2) (half_pos hδ)] with N hN
      simp only [ite_eq_right hab]
      have hh := hL₀ _ hdist
      linarith
  have hpairs' : ∀ᶠ N in atTop, ∀ a b : Fin H,
      cesaro (fun n => inner ℝ (v (n + r a)) (v (n + r b))) N ≤
        (if a = b then C ^ 2 else 0) + ε ^ 2 / 16 :=
    eventually_all.mpr (fun a => eventually_all.mpr (hpairs a))
  let w (n : ℕ) := (H : ℝ)⁻¹ • ∑ a : Fin H, v (n + r a)
  have hdiff := cesaro_smoothing_sub_tendsto_zero v hv H hH r
  have hdiff' := (Metric.tendsto_nhds.mp hdiff) (ε / 2) (half_pos hε)
  filter_upwards [hpairs', hdiff'] with N hN hdiffN
  have hbound : ‖cesaro w N‖ ^ 2 ≤ (H : ℝ)⁻¹ * C ^ 2 + ε ^ 2 / 16 := by
    calc
      ‖cesaro w N‖ ^ 2 ≤ (H : ℝ)⁻¹ ^ 2 * ∑ a : Fin H, ∑ b : Fin H,
          cesaro (fun n => inner ℝ (v (n + r a)) (v (n + r b))) N :=
        norm_smoothed_cesaro_sq_le v H N r
      _ ≤ (H : ℝ)⁻¹ ^ 2 * ∑ a : Fin H, ∑ b : Fin H,
          ((if a = b then C ^ 2 else 0) + ε ^ 2 / 16) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hN a b))
      _ = (H : ℝ)⁻¹ * C ^ 2 + ε ^ 2 / 16 := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  have hw : ‖cesaro w N‖ < ε / 2 := by
    nlinarith [norm_nonneg (cesaro w N)]
  have he : ‖cesaro w N - cesaro v N‖ < ε / 2 := by
    simpa only [dist_zero_right] using hdiffN
  simp only [dist_zero_right]
  calc
    ‖cesaro v N‖ = ‖cesaro w N - (cesaro w N - cesaro v N)‖ := by
      congr 1; abel
    _ ≤ ‖cesaro w N‖ + ‖cesaro w N - cesaro v N‖ := norm_sub_le _ _
    _ < ε := by linarith

end

section

open MeasureTheory Filter
open scoped BigOperators Topology InnerProductSpace ComplexConjugate

section Bounded
variable {Y : Type*} [MeasurableSpace Y] {η : Measure Y} [IsProbabilityMeasure η]

theorem norm_toLp_le_bound {f : Y → ℂ} (hf : MemLp f 2 η) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ᵐ y ∂η, ‖f y‖ ≤ C) : ‖hf.toLp f‖ ≤ C := by
  have hb' : ∀ᵐ y ∂η, ‖hf.toLp f y‖ ≤ C := by
    filter_upwards [hf.coeFn_toLp, hb] with y hy hb
    simpa only [hy] using hb
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hC hb'
end Bounded

namespace ProjectiveCharacters
variable {Y L : Type*} [MeasurableSpace Y] [AddCommGroup L]
    {η : Measure Y} [IsProbabilityMeasure η] {χ : L → Y → ℂ}
    (hχ : ProjectiveCharacters η χ)
include hχ

omit [IsProbabilityMeasure η] in

theorem mul_conj (l m : L) : ∃ c : ℂ, ‖c‖ = 1 ∧
    (fun y => χ l y * conj (χ m y)) =ᵐ[η] (fun y => c * χ (l - m) y) := by
  obtain ⟨c, hc, hcon⟩ := hχ.conjugate m
  obtain ⟨d, hd, hmul⟩ := hχ.mul l (-m)
  refine ⟨c * d, by simp [hc, hd], ?_⟩
  filter_upwards [hcon, hmul] with y hy hz
  rw [hy]
  calc
    χ l y * (c * χ (-m) y) = c * (χ l y * χ (-m) y) := by ring
    _ = c * (d * χ (l + -m) y) := by rw [hz]
    _ = (c * d) * χ (l - m) y := by simp only [sub_eq_add_neg]; ring

theorem norm_integral_conj_le_one (l : L) : ‖∫ y, conj (χ l y) ∂η‖ ≤ 1 := by
  have hb : ∀ᵐ y ∂η, ‖conj (χ l y)‖ ≤ 1 := by
    filter_upwards [hχ.modulus l] with y hy
    simpa using hy.le
  simpa using norm_integral_le_of_norm_le_const hb
end ProjectiveCharacters

theorem l2_real_inner_eq_re_inner {Y : Type*} [MeasurableSpace Y] {η : Measure Y}
    (f g : Lp ℂ 2 η) : inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def, L2.inner_def]
  simp_rw [real_inner_eq_re_inner ℂ]
  exact integral_re (L2.integrable_inner (𝕜 := ℂ) f g)

variable {X Y L : Type*} [MeasurableSpace X] [MeasurableSpace Y] [AddCommGroup L]
    {μ : Measure X} [IsProbabilityMeasure μ]
    {η : Measure Y} [IsProbabilityMeasure η]
    (x : Y → X) (hx : MeasurePreserving x η μ)
    (t : ℕ → X → X) (ht : ∀ m, MeasurePreserving (t m) μ μ)
    {χ : L → Y → ℂ} (hχ : ProjectiveCharacters η χ)

omit [IsProbabilityMeasure μ] in
include hx ht hχ in

theorem phased_memLp {F : X → ℂ} (hFm : AEStronglyMeasurable F μ)
    {C : ℝ} (hFb : ∀ᵐ z ∂μ, ‖F z‖ ≤ C) (P : ℕ → L)
    (ω : ℕ → ℂ) (hω : ∀ m, ‖ω m‖ = 1) (m : ℕ) :
    MemLp (fun y => ω m * F (t m (x y)) * conj (χ (P m) y)) 2 η := by
  apply MemLp.of_bound
    (((hFm.comp_measurePreserving ((ht m).comp hx)).const_mul _).mul
      (hχ.measurable _).star) C
  filter_upwards [((ht m).comp hx).quasiMeasurePreserving.ae hFb,
    hχ.modulus (P m)] with y hy hz
  change ‖ω m * F (t m (x y)) * conj (χ (P m) y)‖ ≤ C
  simpa only [norm_mul, Complex.norm_conj, hω, hz, one_mul, mul_one, Function.comp_def] using hy

omit [MeasurableSpace X] [IsProbabilityMeasure η] in
include hχ in

theorem phased_lag_norm {F : X → ℂ} (P : ℕ → L) (ω : ℕ → ℂ)
    (hω : ∀ m, ‖ω m‖ = 1) (m h : ℕ)
    (htadd : ∀ a b z, t (a + b) z = t b (t a z))
    (hf : ∀ m, MemLp (fun y => ω m * F (t m (x y)) * conj (χ (P m) y)) 2 η) :
    ‖inner ℂ ((hf m).toLp _) ((hf (m + h)).toLp _)‖ =
      ‖∫ y, (F (t h (t m (x y))) * conj (F (t m (x y)))) *
        conj (χ (P (m + h) - P m) y) ∂η‖ := by
  obtain ⟨c, hc, hm⟩ := hχ.mul_conj (P (m + h)) (P m)
  rw [L2.inner_def]
  have heq : (fun y => inner ℂ (((hf m).toLp _) y) (((hf (m + h)).toLp _) y)) =ᵐ[η]
      (fun y => (ω (m + h) * conj (ω m) * conj c) *
        ((F (t h (t m (x y))) * conj (F (t m (x y)))) *
          conj (χ (P (m + h) - P m) y))) := by
    filter_upwards [(hf m).coeFn_toLp, (hf (m + h)).coeFn_toLp, hm] with y hy hz hm
    rw [hy, hz, RCLike.inner_apply, map_mul, map_mul, starRingEnd_self_apply,
      htadd m h]
    have hm' := congrArg conj hm
    simp only [map_mul, starRingEnd_self_apply] at hm'
    calc
      _ = (ω (m + h) * conj (ω m)) *
        (F (t h (t m (x y))) * conj (F (t m (x y)))) *
        (conj (χ (P (m + h)) y) * χ (P m) y) := by ring
      _ = _ := by rw [hm']; ring
  rw [integral_congr_ae heq, integral_const_mul, norm_mul]
  simp [hω, hc]

include hx ht hχ in

theorem polynomial_cancellation_oai
    (htadd : ∀ a b z, t (a + b) z = t b (t a z))
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun m => μ (A ∩ t m ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
    (d : ℕ) (P : ℕ → L) (hP : DifferencePolynomial d P)
    {F : X → ℂ} (hFm : AEStronglyMeasurable F μ)
    {C : ℝ} (hC : 0 ≤ C) (hFb : ∀ᵐ z ∂μ, ‖F z‖ ≤ C)
    (hF0 : ∫ z, F z ∂μ = 0) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N,
      ‖∫ y, F (t m (x y)) * conj (χ (P m) y) ∂η‖) atTop (𝓝 0) := by
  induction d generalizing P F C with
  | zero =>
    obtain ⟨l, hl⟩ := hP
    have hF := MemLp.of_bound (p := 2) hFm C hFb
    have hq := MemLp.of_bound (p := 2) (hχ.measurable l) 1
      ((hχ.modulus l).mono (fun _ h => h.le))
    have hm := mixing_integral_coupling t ht atTop x hx hmix hF hF0 hq
    simpa only [hl, norm_zero] using hm.norm.cesaro
  | succ d ih =>
    choose ω hω hw using fun m =>
      exists_aligning_phase (∫ y, F (t m (x y)) * conj (χ (P m) y) ∂η)
    let q (m : ℕ) (y : Y) := ω m * F (t m (x y)) * conj (χ (P m) y)
    have hq (m : ℕ) : MemLp (q m) 2 η := phased_memLp x hx t ht hχ hFm hFb P ω hω m
    let v (m : ℕ) : Lp ℂ 2 η := (hq m).toLp (q m)
    have hv (m : ℕ) : ‖v m‖ ≤ C := by
      apply norm_toLp_le_bound (hq m) hC
      filter_upwards [((ht m).comp hx).quasiMeasurePreserving.ae hFb,
        hχ.modulus (P m)] with y hy hz
      simpa only [q, norm_mul, Complex.norm_conj, hω, hz, one_mul, mul_one, Function.comp_def] using hy
    let c (h : ℕ) := ‖∫ z, F (t h z) * conj (F z) ∂μ‖
    have hclim : Tendsto c atTop (𝓝 0) := by
      have hF := MemLp.of_bound (p := 2) hFm C hFb
      have hm := mixing_integral_coupling t ht atTop id (MeasurePreserving.id μ)
        hmix hF hF0 hF
      simpa only [c, id_eq, norm_zero] using hm.norm
    have hlag : LagCesaroBound v c := by
      intro h hh ε hε
      let H (z : X) := F (t h z) * conj (F z)
      have hHm : AEStronglyMeasurable H μ :=
        (hFm.comp_measurePreserving (ht h)).mul hFm.star
      have hHb : ∀ᵐ z ∂μ, ‖H z‖ ≤ C ^ 2 := by
        filter_upwards [(ht h).quasiMeasurePreserving.ae hFb, hFb] with z hz hf
        dsimp [H]
        rw [norm_mul, Complex.norm_conj, pow_two]
        exact mul_le_mul hz hf (norm_nonneg _) hC
      have hHi : Integrable H μ := (MemLp.of_bound (p := 1) hHm (C ^ 2) hHb).integrable le_rfl
      let a : ℂ := ∫ z, H z ∂μ
      let G (z : X) := H z - a
      have hGm : AEStronglyMeasurable G μ := hHm.sub aestronglyMeasurable_const
      have hGb : ∀ᵐ z ∂μ, ‖G z‖ ≤ C ^ 2 + ‖a‖ := by
        filter_upwards [hHb] with z hz
        exact (norm_sub_le _ _).trans (add_le_add hz le_rfl)
      have hG0 : ∫ z, G z ∂μ = 0 := by
        dsimp [G]
        rw [integral_sub hHi (integrable_const a)]
        simp [a]
      let D (m : ℕ) := P (m + h) - P m
      have hGc := ih D (hP h hh) hGm (by positivity : 0 ≤ C ^ 2 + ‖a‖) hGb hG0
      let b (m : ℕ) := ‖∫ y, G (t m (x y)) * conj (χ (D m) y) ∂η‖
      have hbound (m : ℕ) : |inner ℝ (v m) (v (m + h))| ≤ b m + c h := by
        have hreal : |inner ℝ (v m) (v (m + h))| ≤
            ‖inner ℂ (v m) (v (m + h))‖ := by
          rw [l2_real_inner_eq_re_inner]
          exact Complex.abs_re_le_norm _
        have heq := phased_lag_norm x t hχ P ω hω m h htadd hq
        change ‖inner ℂ (v m) (v (m + h))‖ = _ at heq
        rw [heq] at hreal
        refine hreal.trans ?_
        have hGi : Integrable (fun y => G (t m (x y)) * conj (χ (D m) y)) η := by
          have hhq := phased_memLp x hx t ht hχ hGm hGb D (fun _ => 1)
            (fun _ => norm_one) m
          simpa only [one_mul] using hhq.integrable (by norm_num : (1 : ENNReal) ≤ 2)
        have hei : Integrable (fun y => a * conj (χ (D m) y)) η :=
          ((MemLp.of_bound (p := 1) (hχ.measurable _).star 1
            ((hχ.modulus (D m)).mono (fun y hy => by simpa only [Pi.star_apply, norm_star] using hy.le))).integrable le_rfl).const_mul a
        have hi : (∫ y, H (t m (x y)) * conj (χ (D m) y) ∂η) =
            (∫ y, G (t m (x y)) * conj (χ (D m) y) ∂η) +
              a * (∫ y, conj (χ (D m) y) ∂η) := by
          rw [← integral_const_mul, ← integral_add hGi hei]
          apply integral_congr_ae
          exact Eventually.of_forall (fun y => by dsimp [G]; ring)
        change ‖∫ y, H (t m (x y)) * conj (χ (D m) y) ∂η‖ ≤ _
        rw [hi]
        calc
          _ ≤ b m + ‖a * ∫ y, conj (χ (D m) y) ∂η‖ := norm_add_le _ _
          _ ≤ b m + ‖a‖ := by
            gcongr
            rw [norm_mul]
            exact (mul_le_mul_of_nonneg_left (hχ.norm_integral_conj_le_one _) (norm_nonneg a)).trans_eq
              (mul_one _)
          _ = b m + c h := rfl
      filter_upwards [hGc.eventually_lt_const hε, eventually_gt_atTop 0] with N hN hN0
      have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN0)
      change cesaro (fun m => |inner ℝ (v m) (v (m + h))|) N ≤ c h + ε
      calc
        _ ≤ cesaro (fun m => b m + c h) N := cesaro_mono hbound N
        _ = cesaro b N + c h := by
          simp [cesaro, Finset.sum_add_distrib, mul_add, hNne]
        _ ≤ c h + ε := by change (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N, b m < ε at hN
                          change (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N, b m + c h ≤ c h + ε
                          linarith
    have hc := van_der_corput v hv hlag hclim
    have hcont : Continuous (fun w : Lp ℂ 2 η =>
        inner ℝ (probabilityOne (μ := η)) w) := by fun_prop
    have he (m : ℕ) : inner ℝ (probabilityOne (μ := η)) (v m) =
        ‖∫ y, F (t m (x y)) * conj (χ (P m) y) ∂η‖ := by
      rw [l2_real_inner_eq_re_inner, inner_probabilityOne]
      have hqi : (∫ y, v m y ∂η) = ∫ y, q m y ∂η := integral_congr_ae (hq m).coeFn_toLp
      rw [hqi]
      change (∫ y, ω m * F (t m (x y)) * conj (χ (P m) y) ∂η).re = _
      simp_rw [mul_assoc]
      rw [integral_const_mul]
      exact hw m
    have hi' : Tendsto (fun N => inner ℝ (probabilityOne (μ := η)) (cesaro v N)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, inner_zero_right] using (hcont.tendsto 0).comp hc
    convert hi' using 1
    all_goals try with_reducible_and_instances rfl
    funext N
    simp only [cesaro, inner_smul_right, inner_sum, he]

end

open scoped BigOperators
open Polynomial

open scoped BigOperators

open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate


end Rokhlin

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Rokhlin.polynomial_cancellation_oai.{u_1, u_2, u_3} := @OAI.Rokhlin.polynomial_cancellation_oai.{u_1, u_2, u_3}
