-- Prove2me | solution 1 for MasulloGRH.partial_euler_products_converge_on_one_line
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T17:27:04.019332+00:00
-- url     : https://prove2.me/submissions/f26a5fe6-a130-41f0-bb64-2a62e86c73f0

import Definitions.Def_MasulloGRH_IdeleNorm
import Theorems.Thm_MasulloGRH_heckeLFunction_exists_meromorphic_continuation
import Theorems.Thm_MasulloGRH_prime_sums_converge_on_one_line

set_option autoImplicit false

/-!
# Corollary B.7.2.5: partial Euler products converge on the 1-line

We reduce Corollary B.7.2.5 to Corollary B.7.2.3 (convergence of the prime sums
`∑_{N𝔭 < x} χ(𝔭) N𝔭^{-s}` on the line `Re s = 1`), following Theorem B.7.2.4 of the source.

* On `Re s ≥ 1` each Euler factor is `(1 - z_v)⁻¹ = exp(z_v + r_v)` with `|r_v| ≤ N𝔭_v^{-2}`, so the
  partial Euler product is `exp(Σ_x(s) + R_x(s))`, where `Σ_x` is the prime sum and `R_x` converges
  uniformly on `Re s ≥ 1`.
* If `Σ_x → g` locally uniformly on a set `S` of the line, then the partial products converge
  locally uniformly on `S` to `exp(g + R)`.
* Abel's theorem for Dirichlet series shows `∑_v z_v(s₀ + ε) → g(s₀)` as `ε → 0⁺`, so
  `L_f(s₀ + ε) → exp(g(s₀) + R(s₀))`.  This limit is finite, so `L_f` has no pole at `s₀`; being in
  meromorphic normal form it is continuous there, and `L_f(s₀) = exp(g(s₀) + R(s₀))`.
-/

namespace MasulloGRH.PEP

open Filter Topology NumberField IsDedekindDomain Complex

/-! ### Abel's theorem for weighted partial sums -/

section abelSection

/-- Summation by parts. -/
lemma sum_by_parts (P : ℕ → ℂ) (A : ℂ) (w : ℕ → ℝ) (hP0 : P 0 = 0) (N : ℕ) :
    ∑ k ∈ Finset.range N, (w k : ℂ) * (P (k + 1) - P k) =
      (P N - A) * (w N : ℂ) + A * (w 0 : ℂ) +
        ∑ k ∈ Finset.range N, (P (k + 1) - A) * ((w k : ℂ) - (w (k + 1) : ℂ)) := by
  induction N with
  | zero => rw [Finset.sum_range_zero, Finset.sum_range_zero, hP0]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- **Abel's theorem.** If the partial sums `P N` converge to `A`, and `B ε` is the sum of the
series weighted by a family of antitone weights `w ε` with `w ε 0 = 1` that tend pointwise to `1`
as `ε → 0⁺`, then `B ε → A`. -/
theorem abel_weighted {P : ℕ → ℂ} {A : ℂ} (hP0 : P 0 = 0) (hP : Tendsto P atTop (𝓝 A))
    (w : ℝ → ℕ → ℝ) (B : ℝ → ℂ)
    (hw0 : ∀ ε > 0, w ε 0 = 1) (hwanti : ∀ ε > 0, Antitone (w ε))
    (hwnn : ∀ ε > 0, ∀ k, 0 ≤ w ε k)
    (hw1 : ∀ k, Tendsto (fun ε => w ε k) (𝓝[>] 0) (𝓝 1))
    (hB : ∀ ε > 0, Tendsto (fun N => ∑ k ∈ Finset.range N, (w ε k : ℂ) * (P (k + 1) - P k))
      atTop (𝓝 (B ε))) :
    Tendsto B (𝓝[>] 0) (𝓝 A) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨C, hC⟩ : ∃ C, ∀ k, ‖P k - A‖ ≤ C := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
      (Metric.isBounded_range_of_tendsto _ (hP.sub_const A))
    exact ⟨C, fun k => hC _ ⟨k, rfl⟩⟩
  obtain ⟨M, hM⟩ : ∃ M, ∀ k ≥ M, ‖P k - A‖ ≤ δ / 4 := by
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hP (δ / 4) (by linarith)
    exact ⟨M, fun k hk => by rw [← dist_eq_norm]; exact (hM k hk).le⟩
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioi (0 : ℝ) ∧ |C| * (1 - w ε M) < δ / 4 := by
    have h1 : Tendsto (fun ε => |C| * (1 - w ε M)) (𝓝[>] 0) (𝓝 (|C| * (1 - 1))) :=
      ((hw1 M).const_sub 1).const_mul |C|
    rw [sub_self, mul_zero] at h1
    exact (eventually_mem_nhdsWithin).and (h1.eventually (gt_mem_nhds (by linarith)))
  filter_upwards [hev] with ε hεC
  obtain ⟨hε, hεC⟩ := hεC
  have hε' : 0 < ε := hε
  rw [dist_eq_norm]
  have hm : ∀ k, 0 ≤ w ε k - w ε (k + 1) := fun k =>
    sub_nonneg.2 (hwanti ε hε' (Nat.le_succ k))
  have hD : ∀ N, M ≤ N → ∑ k ∈ Finset.range N, ‖P (k + 1) - A‖ * (w ε k - w ε (k + 1)) ≤
      |C| * (1 - w ε M) + δ / 4 * (w ε M - w ε N) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      have h : ∑ k ∈ Finset.range M, ‖P (k + 1) - A‖ * (w ε k - w ε (k + 1)) ≤
          ∑ k ∈ Finset.range M, |C| * (w ε k - w ε (k + 1)) :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right ((hC _).trans (le_abs_self C)) (hm k)
      rw [← Finset.mul_sum, Finset.sum_range_sub' (w ε), hw0 ε hε'] at h
      linarith
    | succ n hn ih =>
      rw [Finset.sum_range_succ]
      have h1 : ‖P (n + 1) - A‖ * (w ε n - w ε (n + 1)) ≤ δ / 4 * (w ε n - w ε (n + 1)) :=
        mul_le_mul_of_nonneg_right (hM _ (by omega)) (hm n)
      linarith
  have hlim : Tendsto (fun N => ‖(∑ k ∈ Finset.range N, (w ε k : ℂ) * (P (k + 1) - P k)) - A‖ -
      ‖P N - A‖) atTop (𝓝 (‖B ε - A‖ - ‖A - A‖)) :=
    (((hB ε hε').sub_const A).norm).sub ((hP.sub_const A).norm)
  rw [sub_self, norm_zero, sub_zero] at hlim
  refine lt_of_le_of_lt (le_of_tendsto hlim ?_) (by linarith : |C| * (1 - w ε M) + δ / 4 < δ)
  filter_upwards [eventually_ge_atTop M] with N hN
  have hid := sum_by_parts P A (w ε) hP0 N
  rw [hw0 ε hε'] at hid
  have e : (∑ k ∈ Finset.range N, (w ε k : ℂ) * (P (k + 1) - P k)) - A =
      (P N - A) * (w ε N : ℂ) +
        ∑ k ∈ Finset.range N, (P (k + 1) - A) * ((w ε k : ℂ) - (w ε (k + 1) : ℂ)) := by
    rw [hid]; push_cast; ring
  rw [e]
  have h1 : ‖(P N - A) * (w ε N : ℂ)‖ ≤ ‖P N - A‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hwnn ε hε' N)]
    have : w ε N ≤ 1 := (hwanti ε hε' (Nat.zero_le N)).trans_eq (hw0 ε hε')
    exact mul_le_of_le_one_right (norm_nonneg _) this
  have h2 : ‖∑ k ∈ Finset.range N, (P (k + 1) - A) * ((w ε k : ℂ) - (w ε (k + 1) : ℂ))‖ ≤
      ∑ k ∈ Finset.range N, ‖P (k + 1) - A‖ * (w ε k - w ε (k + 1)) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (hm k)]
  have h3 := hD N hN
  have h4 : δ / 4 * (w ε M - w ε N) ≤ δ / 4 := by
    have h5 : w ε M - w ε N ≤ 1 := by
      have := hwnn ε hε' N
      have := (hwanti ε hε' (Nat.zero_le M)).trans_eq (hw0 ε hε')
      linarith
    have : 0 ≤ δ / 4 := by linarith
    nlinarith
  have h6 := norm_add_le ((P N - A) * (w ε N : ℂ))
    (∑ k ∈ Finset.range N, (P (k + 1) - A) * ((w ε k : ℂ) - (w ε (k + 1) : ℂ)))
  linarith

end abelSection

/-! ### Locally uniform convergence and `exp` -/

lemma tlu_exp {ι α : Type*} [TopologicalSpace α] {p : Filter ι} {S : Set α} {F : ι → α → ℂ}
    {f : α → ℂ} (hF : TendstoLocallyUniformlyOn F f p S) (hf : ContinuousOn f S) :
    TendstoLocallyUniformlyOn (fun n y => Complex.exp (F n y)) (fun y => Complex.exp (f y)) p S := by
  rw [Metric.tendstoLocallyUniformlyOn_iff] at hF ⊢
  intro ε hε x hx
  set M : ℝ := ‖f x‖ + 1 with hM
  have hEpos : 0 < Real.exp M := Real.exp_pos M
  have hδpos : 0 < min 1 (ε / (2 * Real.exp M)) := lt_min one_pos (div_pos hε (by positivity))
  obtain ⟨t, ht, hFt⟩ := hF _ hδpos x hx
  have ht1 : ∀ᶠ y in 𝓝[S] x, f y ∈ Metric.ball (f x) 1 :=
    (hf x hx).eventually (Metric.ball_mem_nhds (f x) one_pos)
  refine ⟨t ∩ {y | f y ∈ Metric.ball (f x) 1}, Filter.inter_mem ht ht1, ?_⟩
  filter_upwards [hFt] with n hn y hy
  have h1 : dist (f y) (F n y) < min 1 (ε / (2 * Real.exp M)) := hn y hy.1
  have h2 : dist (f y) (f x) < 1 := hy.2
  have hfy : ‖f y‖ ≤ M := by
    rw [dist_eq_norm] at h2
    have := norm_sub_norm_le (f y) (f x)
    rw [hM]; linarith
  have hdiff : ‖F n y - f y‖ < min 1 (ε / (2 * Real.exp M)) := by
    rw [← dist_eq_norm, dist_comm]; exact h1
  rw [dist_eq_norm]
  have e : Complex.exp (F n y) = Complex.exp (f y) * Complex.exp (F n y - f y) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : Complex.exp (f y) - Complex.exp (f y) * Complex.exp (F n y - f y) =
      -(Complex.exp (f y) * (Complex.exp (F n y - f y) - 1)) := by ring
  rw [e, e2, norm_neg, norm_mul]
  have hA : ‖Complex.exp (f y)‖ ≤ Real.exp M :=
    (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 hfy)
  have hB : ‖Complex.exp (F n y - f y) - 1‖ ≤ 2 * ‖F n y - f y‖ :=
    Complex.norm_exp_sub_one_le (hdiff.le.trans (min_le_left _ _))
  have hlt : ‖F n y - f y‖ < ε / (2 * Real.exp M) := hdiff.trans_le (min_le_right _ _)
  calc ‖Complex.exp (f y)‖ * ‖Complex.exp (F n y - f y) - 1‖
      ≤ Real.exp M * (2 * ‖F n y - f y‖) := mul_le_mul hA hB (norm_nonneg _) hEpos.le
    _ < Real.exp M * (2 * (ε / (2 * Real.exp M))) :=
        mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hlt two_pos) hEpos
    _ = ε := by field_simp

/-! ### Euler factors -/

section hecke

open Ideal

variable {F : Type*} [Field F] [NumberField F]

theorem lseriesSummable_card (σ : ℝ) (hσ : 1 < σ) :
    LSeriesSummable (fun n => ((Nat.card {I : Ideal (𝓞 F) // absNorm I = n} : ℝ) : ℂ)) σ := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n => (Nat.card {I : Ideal (𝓞 F) // absNorm I = n} : ℝ)) ?_
    (fun _ => Nat.cast_nonneg _) zero_le_one (by simpa using hσ)
  refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (a := ?_) ?_
  · exact (2 ^ InfinitePlace.nrRealPlaces F * (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces F *
      Units.regulator F * classNumber F) / (Units.torsionOrder F * Real.sqrt |discr F|)
  have h := ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop)
  simp only [Real.rpow_one]
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 F) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem summable_idealNorm (σ : ℝ) (hσ : 1 < σ) :
    Summable fun I : Ideal (𝓞 F) => ((absNorm I : ℕ) : ℝ) ^ (-σ) := by
  have hL := lseriesSummable_card (F := F) σ hσ
  rw [LSeriesSummable, ← summable_norm_iff] at hL
  let g : Ideal (𝓞 F) → ℕ := fun I => absNorm I
  rw [← (Equiv.sigmaFiberEquiv g).summable_iff]
  have hnn : ∀ x : (Σ n : ℕ, {I : Ideal (𝓞 F) // g I = n}),
      0 ≤ ((fun I : Ideal (𝓞 F) => ((absNorm I : ℕ) : ℝ) ^ (-σ)) ∘ (Equiv.sigmaFiberEquiv g)) x :=
    fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [summable_sigma_of_nonneg hnn]
  refine ⟨fun n => ?_, ?_⟩
  · have : Finite {I : Ideal (𝓞 F) // g I = n} := Ideal.finite_setOfPred_absNorm_eq n
    exact Summable.of_finite
  · refine hL.congr fun n => ?_
    have : Finite {I : Ideal (𝓞 F) // g I = n} := Ideal.finite_setOfPred_absNorm_eq n
    have h1 : ∀ y : {I : Ideal (𝓞 F) // g I = n},
        ((fun I : Ideal (𝓞 F) => ((absNorm I : ℕ) : ℝ) ^ (-σ)) ∘ (Equiv.sigmaFiberEquiv g)) ⟨n, y⟩
          = (n : ℝ) ^ (-σ) := by
      intro y
      simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply]
      rw [show (absNorm y.1 : ℕ) = n from y.2]
    simp_rw [h1]
    rw [tsum_const, nsmul_eq_mul, LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow (show -σ ≠ 0 by linarith)]
    · rw [if_neg hn, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg _),
        Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

theorem summable_placeNorm (σ : ℝ) (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ((absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) :=
  (summable_idealNorm (F := F) σ hσ).comp_injective
    (fun _ _ h => HeightOneSpectrum.ext h)

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 F)) : 2 ≤ absNorm v.asIdeal := by
  have h0 : absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

lemma one_le_natNorm (v : HeightOneSpectrum (𝓞 F)) :
    (1 : ℝ) ≤ ((absNorm v.asIdeal : ℕ) : ℝ) := by
  have := two_le_absNorm v
  exact_mod_cast (by omega : 1 ≤ absNorm v.asIdeal)

lemma natNorm_pos (v : HeightOneSpectrum (𝓞 F)) : (0 : ℝ) < ((absNorm v.asIdeal : ℕ) : ℝ) :=
  lt_of_lt_of_le one_pos (one_le_natNorm v)

lemma primeNorm_ne_zero (v : HeightOneSpectrum (𝓞 F)) : primeNorm v ≠ 0 := by
  unfold primeNorm
  have := two_le_absNorm v
  exact_mod_cast (by omega : absNorm v.asIdeal ≠ 0)

theorem norm_primeValue_le (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    ‖χ.primeValue v‖ ≤ 1 := by
  unfold HeckeCharacter.primeValue
  split_ifs
  · unfold HeckeCharacter.localComponent
    rw [Circle.norm_coe]
  · simp

/-- The Euler variable `z_v(s) = χ(𝔭_v) N(𝔭_v)^{-s}`. -/
noncomputable def eulerVar (χ : HeckeCharacter F) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  χ.primeValue v * primeNorm v ^ (-s)

lemma norm_eulerVar_le (χ : HeckeCharacter F) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    ‖eulerVar χ s v‖ ≤ ((absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) := by
  unfold eulerVar primeNorm
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by have := two_le_absNorm v; omega)]
  simp only [Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (norm_primeValue_le χ v)

lemma norm_eulerVar_le_inv (χ : HeckeCharacter F) {s : ℂ} (hs : 1 ≤ s.re)
    (v : HeightOneSpectrum (𝓞 F)) :
    ‖eulerVar χ s v‖ ≤ ((absNorm v.asIdeal : ℕ) : ℝ) ^ (-1 : ℝ) :=
  (norm_eulerVar_le χ s v).trans
    (Real.rpow_le_rpow_of_exponent_le (one_le_natNorm v) (by linarith))

lemma norm_eulerVar_le_half (χ : HeckeCharacter F) {s : ℂ} (hs : 1 ≤ s.re)
    (v : HeightOneSpectrum (𝓞 F)) : ‖eulerVar χ s v‖ ≤ 1 / 2 := by
  refine (norm_eulerVar_le_inv χ hs v).trans ?_
  have h2 : (2 : ℝ) ≤ ((absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm v
  rw [Real.rpow_neg_one, one_div]
  exact inv_anti₀ (by norm_num) h2

lemma summable_eulerVar (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re) :
    Summable (eulerVar χ s) :=
  Summable.of_norm_bounded (summable_placeNorm (F := F) s.re hs) (norm_eulerVar_le χ s)

lemma continuous_eulerVar (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun s => eulerVar χ s v := by
  unfold eulerVar
  exact continuous_const.mul (continuous_neg.const_cpow (Or.inl (primeNorm_ne_zero v)))

lemma eulerVar_shift (χ : HeckeCharacter F) (s₀ : ℂ) (ε : ℝ) (v : HeightOneSpectrum (𝓞 F)) :
    eulerVar χ (s₀ + ε) v =
      eulerVar χ s₀ v * ((((absNorm v.asIdeal : ℕ) : ℝ) ^ (-ε) : ℝ) : ℂ) := by
  have hN : ((absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := primeNorm_ne_zero v
  unfold eulerVar primeNorm
  rw [show -(s₀ + (ε : ℂ)) = -s₀ + ((-ε : ℝ) : ℂ) by push_cast; ring, Complex.cpow_add _ _ hN,
    Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast]
  ring

lemma one_sub_mem_slitPlane {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) : 1 - w ∈ slitPlane := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  have := Complex.re_le_norm w
  simp only [Complex.sub_re, Complex.one_re]
  linarith

lemma norm_logRem_le' {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) : ‖-Complex.log (1 - w) - w‖ ≤ ‖w‖ ^ 2 := by
  have h := Complex.norm_log_one_add_sub_self_le (z := -w) (by rw [norm_neg]; linarith)
  rw [norm_neg] at h
  have e : -Complex.log (1 - w) - w = -(Complex.log (1 + -w) - -w) := by
    rw [← sub_eq_add_neg]; ring
  rw [e, norm_neg]
  refine h.trans ?_
  have h1 : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h3 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖w‖)
  linarith

lemma inv_one_sub_eq_exp {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    (1 - w)⁻¹ = Complex.exp (-Complex.log (1 - w)) := by
  rw [Complex.exp_neg, Complex.exp_log (Complex.slitPlane_ne_zero (one_sub_mem_slitPlane hw))]

/-- The logarithm `-log(1 - z_v(s))` of the Euler factor at `v`. -/
noncomputable def logFactor (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ :=
  -Complex.log (1 - eulerVar χ s v)

/-- Its nonlinear part `-log(1 - z_v(s)) - z_v(s)`. -/
noncomputable def logRem (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ :=
  logFactor χ v s - eulerVar χ s v

lemma norm_logRem_le (χ : HeckeCharacter F) {s : ℂ} (hs : 1 ≤ s.re)
    (v : HeightOneSpectrum (𝓞 F)) :
    ‖logRem χ v s‖ ≤ ((absNorm v.asIdeal : ℕ) : ℝ) ^ (-2 : ℝ) := by
  have h1 := norm_logRem_le' (norm_eulerVar_le_half χ hs v)
  have h2 := norm_eulerVar_le_inv χ hs v
  have hp := natNorm_pos v
  unfold logRem logFactor
  refine h1.trans ?_
  have e : ((absNorm v.asIdeal : ℕ) : ℝ) ^ (-2 : ℝ) =
      (((absNorm v.asIdeal : ℕ) : ℝ) ^ (-1 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]; norm_num
  rw [e]
  exact pow_le_pow_left₀ (norm_nonneg _) h2 2

lemma summable_two : Summable fun v : HeightOneSpectrum (𝓞 F) =>
    ((absNorm v.asIdeal : ℕ) : ℝ) ^ (-2 : ℝ) :=
  summable_placeNorm (F := F) 2 (by norm_num)

lemma summable_logRem (χ : HeckeCharacter F) {s : ℂ} (hs : 1 ≤ s.re) :
    Summable fun v => logRem χ v s :=
  Summable.of_norm_bounded summable_two (fun v => norm_logRem_le χ hs v)

lemma continuousOn_logRem (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    ContinuousOn (fun s => logRem χ v s) {s : ℂ | 1 ≤ s.re} := by
  unfold logRem logFactor
  refine (((continuous_const.sub (continuous_eulerVar χ v)).continuousOn.clog ?_).neg).sub
    (continuous_eulerVar χ v).continuousOn
  intro s hs
  exact one_sub_mem_slitPlane (norm_eulerVar_le_half χ hs v)

lemma continuousOn_tsum_logRem (χ : HeckeCharacter F) :
    ContinuousOn (fun s => ∑' v, logRem χ v s) {s : ℂ | 1 ≤ s.re} :=
  continuousOn_tsum (continuousOn_logRem χ) summable_two (fun v _ hs => norm_logRem_le χ hs v)

/-- On `Re s > 1` the Euler product is `exp` of the sum of the logarithms of its factors. -/
lemma euler_eq_exp (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re) :
    heckeEulerProduct χ s = Complex.exp (∑' v, logFactor χ v s) := by
  have hne : ∀ v : HeightOneSpectrum (𝓞 F), (1 - eulerVar χ s v)⁻¹ ≠ 0 := fun v =>
    inv_ne_zero (Complex.slitPlane_ne_zero (one_sub_mem_slitPlane (norm_eulerVar_le_half χ hs.le v)))
  have hlog : ∀ v : HeightOneSpectrum (𝓞 F),
      Complex.log ((1 - eulerVar χ s v)⁻¹) = logFactor χ v s := fun v =>
    Complex.log_inv _
      (Complex.slitPlane_arg_ne_pi (one_sub_mem_slitPlane (norm_eulerVar_le_half χ hs.le v)))
  have hsum : Summable fun v : HeightOneSpectrum (𝓞 F) =>
      Complex.log ((1 - eulerVar χ s v)⁻¹) := by
    simp_rw [hlog]
    refine ((summable_eulerVar χ hs).add (summable_logRem χ hs.le)).congr fun v => ?_
    unfold logRem; ring
  have := Complex.cexp_tsum_eq_tprod hne hsum
  simp_rw [hlog] at this
  rw [this]
  rfl

lemma L_spec (χ : HeckeCharacter F) :
    MeromorphicNFOn (heckeLFunction χ) Set.univ ∧
      ∀ s : ℂ, 1 < s.re → heckeLFunction χ s = heckeEulerProduct χ s := by
  have hex := MasulloGRH.heckeLFunction_exists_meromorphic_continuation F χ
  unfold heckeLFunction
  rw [dif_pos hex]
  exact hex.choose_spec

/-! ### Finite sets of places of bounded norm -/

lemma finite_lt (x : ℝ) :
    {v : HeightOneSpectrum (𝓞 F) | ((absNorm v.asIdeal : ℕ) : ℝ) < x}.Finite := by
  have hI := Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌈x⌉₊
  refine (hI.preimage (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun _ _ _ _ h => HeightOneSpectrum.ext h)).subset ?_
  intro v hv
  simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hv ⊢
  have : ((absNorm v.asIdeal : ℕ) : ℝ) ≤ (⌈x⌉₊ : ℝ) := hv.le.trans (Nat.le_ceil x)
  exact_mod_cast this

/-- The finite set of places `v` with `N(𝔭_v) < x`. -/
noncomputable def normLT (x : ℝ) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (finite_lt (F := F) x).toFinset

lemma mem_normLT {x : ℝ} {v : HeightOneSpectrum (𝓞 F)} :
    v ∈ normLT x ↔ ((absNorm v.asIdeal : ℕ) : ℝ) < x := by
  unfold normLT
  rw [Set.Finite.mem_toFinset]
  rfl

lemma normLT_mono : Monotone (normLT (F := F)) := fun _ _ hxy _ hv =>
  mem_normLT.2 ((mem_normLT.1 hv).trans_le hxy)

lemma tendsto_normLT : Tendsto (normLT (F := F)) atTop atTop :=
  tendsto_atTop_finset_of_monotone normLT_mono fun v =>
    ⟨((absNorm v.asIdeal : ℕ) : ℝ) + 1, mem_normLT.2 (lt_add_one _)⟩

lemma finsum_eq (x : ℝ) (f : HeightOneSpectrum (𝓞 F) → ℂ) :
    ∑ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x), f v =
      ∑ v ∈ normLT x, f v :=
  finsum_cond_eq_sum_of_cond_iff f fun {_} _ => mem_normLT.symm

lemma finprod_eq (x : ℝ) (f : HeightOneSpectrum (𝓞 F) → ℂ) :
    ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x), f v =
      ∏ v ∈ normLT x, f v :=
  finprod_cond_eq_prod_of_cond_iff f fun {_} _ => mem_normLT.symm

lemma partial_eq (χ : HeckeCharacter F) {s : ℂ} (hs : 1 ≤ s.re) (x : ℝ) :
    ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x),
        (eulerFactorInv χ v s)⁻¹ =
      Complex.exp (∑ v ∈ normLT x, logFactor χ v s) := by
  rw [finprod_eq, Complex.exp_sum]
  refine Finset.prod_congr rfl fun v _ => ?_
  unfold eulerFactorInv logFactor
  exact inv_one_sub_eq_exp (norm_eulerVar_le_half χ hs v)

lemma tendstoUniformlyOn_logRem (χ : HeckeCharacter F) :
    TendstoUniformlyOn (fun (x : ℝ) (s : ℂ) => ∑ v ∈ normLT x, logRem χ v s)
      (fun s => ∑' v, logRem χ v s) atTop {s : ℂ | 1 ≤ s.re} := by
  have h := tendstoUniformlyOn_tsum (f := fun v s => logRem χ v s) summable_two
    (s := {s : ℂ | 1 ≤ s.re}) (fun v s hs => norm_logRem_le χ hs v)
  exact fun u hu => tendsto_normLT.eventually (h u hu)

/-! ### Abel's theorem for the prime sums -/

/-- The prime sum over the places of norm `< N`. -/
noncomputable def Psum (χ : HeckeCharacter F) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ v ∈ normLT (N : ℝ), eulerVar χ s v

lemma Psum_zero (χ : HeckeCharacter F) (s : ℂ) : Psum χ s 0 = 0 := by
  unfold Psum
  refine Finset.sum_eq_zero fun v hv => ?_
  have h := mem_normLT.1 hv
  rw [Nat.cast_zero] at h
  exact absurd h (not_lt.2 (Nat.cast_nonneg _))

/-- The weights `max(k, 1)^{-ε}`. -/
noncomputable def wt (ε : ℝ) (k : ℕ) : ℝ := (max (k : ℝ) 1) ^ (-ε)

lemma wt_zero (ε : ℝ) : wt ε 0 = 1 := by
  unfold wt
  rw [Nat.cast_zero, max_eq_right zero_le_one, Real.one_rpow]

lemma wt_anti {ε : ℝ} (hε : 0 < ε) : Antitone (wt ε) := fun k l hkl => by
  unfold wt
  exact Real.rpow_le_rpow_of_nonpos (lt_max_of_lt_right one_pos)
    (max_le_max (by exact_mod_cast hkl) le_rfl) (by linarith)

lemma wt_nonneg (ε : ℝ) (k : ℕ) : 0 ≤ wt ε k :=
  Real.rpow_nonneg (le_max_of_le_right zero_le_one) _

lemma wt_tendsto (k : ℕ) : Tendsto (fun ε => wt ε k) (𝓝[>] 0) (𝓝 1) := by
  have hne : max (k : ℝ) 1 ≠ 0 := ne_of_gt (lt_max_of_lt_right one_pos)
  have h : Tendsto (fun ε : ℝ => (max (k : ℝ) 1) ^ (-ε)) (𝓝 0)
      (𝓝 ((max (k : ℝ) 1) ^ (-(0 : ℝ)))) :=
    ((Real.continuousAt_const_rpow hne).comp continuous_neg.continuousAt).tendsto
  rw [neg_zero, Real.rpow_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

lemma normLT_succ_sdiff [DecidableEq (HeightOneSpectrum (𝓞 F))] {k : ℕ}
    {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∈ normLT ((k + 1 : ℕ) : ℝ) \ normLT (k : ℝ)) : absNorm v.asIdeal = k := by
  rw [Finset.mem_sdiff, mem_normLT, mem_normLT] at hv
  obtain ⟨h1, h2⟩ := hv
  have h1' : absNorm v.asIdeal < k + 1 := by exact_mod_cast h1
  have h2' : ¬ absNorm v.asIdeal < k := by exact_mod_cast h2
  omega

lemma Psum_succ_sub (χ : HeckeCharacter F) (s₀ : ℂ) (ε : ℝ) (k : ℕ) :
    Psum χ (s₀ + ε) (k + 1) - Psum χ (s₀ + ε) k =
      (wt ε k : ℂ) * (Psum χ s₀ (k + 1) - Psum χ s₀ k) := by
  classical
  have hsub : normLT (F := F) (k : ℝ) ⊆ normLT ((k + 1 : ℕ) : ℝ) :=
    normLT_mono (by push_cast; linarith)
  unfold Psum
  rw [← Finset.sum_sdiff_eq_sub hsub, ← Finset.sum_sdiff_eq_sub hsub, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hk := normLT_succ_sdiff hv
  have hk1 : (1 : ℝ) ≤ k := by
    have := two_le_absNorm v
    rw [hk] at this
    exact_mod_cast (by omega : 1 ≤ k)
  rw [eulerVar_shift, hk, wt, max_eq_left hk1]
  ring

lemma sum_wt_eq (χ : HeckeCharacter F) (s₀ : ℂ) (ε : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, (wt ε k : ℂ) * (Psum χ s₀ (k + 1) - Psum χ s₀ k) =
      Psum χ (s₀ + ε) N := by
  induction N with
  | zero => rw [Finset.sum_range_zero, Psum_zero]
  | succ n ih => rw [Finset.sum_range_succ, ih, ← Psum_succ_sub]; ring

lemma tendsto_Psum (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (Psum χ s) atTop (𝓝 (∑' v, eulerVar χ s v)) := by
  have h : Tendsto (fun t : Finset (HeightOneSpectrum (𝓞 F)) => ∑ v ∈ t, eulerVar χ s v) atTop
      (𝓝 (∑' v, eulerVar χ s v)) := (summable_eulerVar χ hs).hasSum
  exact h.comp (tendsto_normLT.comp tendsto_natCast_atTop_atTop)

lemma re_shift {s₀ : ℂ} (hs₀ : s₀.re = 1) (ε : ℝ) : (s₀ + (ε : ℂ)).re = 1 + ε := by
  rw [Complex.add_re, Complex.ofReal_re, hs₀]

/-- The path `ε ↦ s₀ + ε` approaches `s₀` from the right. -/
lemma tendsto_path (s₀ : ℂ) :
    Tendsto (fun ε : ℝ => s₀ + (ε : ℂ)) (𝓝[>] 0) (𝓝 s₀) := by
  have h : Tendsto (fun ε : ℝ => s₀ + (ε : ℂ)) (𝓝 0) (𝓝 (s₀ + ((0 : ℝ) : ℂ))) :=
    (continuous_const.add Complex.continuous_ofReal).tendsto 0
  rw [Complex.ofReal_zero, add_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **Identification of the limit on the line.** If the prime sums at a point `s₀` of the line
converge to `A`, then `L_f(s₀, χ) = exp(A + ∑_v r_v(s₀))`. -/
theorem L_eq_on_line (χ : HeckeCharacter F) (s₀ : ℂ) (hs₀ : s₀.re = 1) (A : ℂ)
    (hP : Tendsto (fun x : ℝ => ∑ v ∈ normLT x, eulerVar χ s₀ v) atTop (𝓝 A)) :
    heckeLFunction χ s₀ = Complex.exp (A + ∑' v, logRem χ v s₀) := by
  have hre : ∀ ε : ℝ, 0 < ε → 1 < (s₀ + (ε : ℂ)).re := fun ε hε => by
    rw [re_shift hs₀]; linarith
  -- Abel's theorem
  have hAbel : Tendsto (fun ε : ℝ => ∑' v, eulerVar χ (s₀ + ε) v) (𝓝[>] 0) (𝓝 A) :=
    abel_weighted (P := Psum χ s₀) (Psum_zero χ s₀)
      (hP.comp tendsto_natCast_atTop_atTop) wt (fun ε => ∑' v, eulerVar χ (s₀ + ε) v)
      (fun ε _ => wt_zero ε) (fun ε hε => wt_anti hε) (fun ε _ k => wt_nonneg ε k) wt_tendsto
      (fun ε hε => (tendsto_Psum χ (hre ε hε)).congr fun N => (sum_wt_eq χ s₀ ε N).symm)
  -- continuity of the remainder
  have hpath : Tendsto (fun ε : ℝ => s₀ + (ε : ℂ)) (𝓝[>] 0) (𝓝[{s : ℂ | 1 ≤ s.re}] s₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_path s₀) ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have := Set.mem_Ioi.1 hε
    show 1 ≤ (s₀ + (ε : ℂ)).re
    rw [re_shift hs₀]; linarith
  have hmem : s₀ ∈ {s : ℂ | 1 ≤ s.re} := by show 1 ≤ s₀.re; rw [hs₀]
  have hR : Tendsto (fun ε : ℝ => ∑' v, logRem χ v (s₀ + ε)) (𝓝[>] 0)
      (𝓝 (∑' v, logRem χ v s₀)) :=
    ((continuousOn_tsum_logRem χ) s₀ hmem).tendsto.comp hpath
  -- the values of `L_f` to the right of `s₀`
  have hLeq : ∀ ε : ℝ, 0 < ε → heckeLFunction χ (s₀ + ε) =
      Complex.exp ((∑' v, eulerVar χ (s₀ + ε) v) + ∑' v, logRem χ v (s₀ + ε)) := by
    intro ε hε
    rw [(L_spec χ).2 _ (hre ε hε), euler_eq_exp χ (hre ε hε),
      ← (summable_eulerVar χ (hre ε hε)).tsum_add (summable_logRem χ (hre ε hε).le)]
    congr 1
    refine tsum_congr fun v => ?_
    unfold logRem; ring
  have hlimL : Tendsto (fun ε : ℝ => heckeLFunction χ (s₀ + ε)) (𝓝[>] 0)
      (𝓝 (Complex.exp (A + ∑' v, logRem χ v s₀))) := by
    refine ((hAbel.add hR).cexp).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hLeq ε hε).symm
  -- `L_f` has no pole at `s₀`, hence is continuous there
  have hNF : MeromorphicNFAt (heckeLFunction χ) s₀ := (L_spec χ).1 (Set.mem_univ s₀)
  have hpath' : Tendsto (fun ε : ℝ => s₀ + (ε : ℂ)) (𝓝[>] 0) (𝓝[≠] s₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_path s₀) ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have := Set.mem_Ioi.1 hε
    show s₀ + (ε : ℂ) ≠ s₀
    intro h
    have h' := congrArg Complex.re h
    rw [re_shift hs₀, hs₀] at h'
    linarith
  have hord : 0 ≤ meromorphicOrderAt (heckeLFunction χ) s₀ := by
    by_contra hneg
    rw [not_le] at hneg
    have h1 := (tendsto_cobounded_of_meromorphicOrderAt_neg hneg).comp hpath'
    rw [← tendsto_norm_atTop_iff_cobounded] at h1
    exact not_tendsto_atTop_of_tendsto_nhds hlimL.norm h1
  have hcont : ContinuousAt (heckeLFunction χ) s₀ :=
    (hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 hord).continuousAt
  have hlim2 : Tendsto (fun ε : ℝ => heckeLFunction χ (s₀ + ε)) (𝓝[>] 0)
      (𝓝 (heckeLFunction χ s₀)) :=
    hcont.tendsto.comp (tendsto_path s₀)
  exact tendsto_nhds_unique hlim2 hlimL

/-- **Reduction.** If the prime sums converge locally uniformly on a subset `S` of the line
`Re s = 1`, then the partial Euler products converge locally uniformly on `S` to `L_f(s, χ)`. -/
theorem reduction (χ : HeckeCharacter F) (S : Set ℂ) (hS : ∀ s ∈ S, s.re = 1) (g : ℂ → ℂ)
    (hg : TendstoLocallyUniformlyOn (fun (x : ℝ) (s : ℂ) =>
      ∑ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x),
        χ.primeValue v * primeNorm v ^ (-s)) g atTop S) :
    TendstoLocallyUniformlyOn (fun (x : ℝ) (s : ℂ) =>
      ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x),
        (eulerFactorInv χ v s)⁻¹) (heckeLFunction χ) atTop S := by
  have hS1 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun s hs => by show 1 ≤ s.re; rw [hS s hs]
  have hg' : TendstoLocallyUniformlyOn (fun (x : ℝ) (s : ℂ) => ∑ v ∈ normLT x, eulerVar χ s v)
      g atTop S :=
    hg.congr fun x s _ => finsum_eq x _
  have hgc : ContinuousOn g S := hg'.continuousOn (Frequently.of_forall fun x =>
    continuousOn_finsetSum _ fun v _ => (continuous_eulerVar χ v).continuousOn)
  have hR := ((tendstoUniformlyOn_logRem χ).tendstoLocallyUniformlyOn).mono hS1
  have hsum := hg'.add hR
  have hH : ContinuousOn (g + fun s => ∑' v, logRem χ v s) S :=
    hgc.add ((continuousOn_tsum_logRem χ).mono hS1)
  have hexp := tlu_exp hsum hH
  refine (hexp.congr fun x s hs => ?_).congr_right fun s hs => ?_
  · show Complex.exp (∑ v ∈ normLT x, eulerVar χ s v + ∑ v ∈ normLT x, logRem χ v s) =
      ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x),
        (eulerFactorInv χ v s)⁻¹
    rw [partial_eq χ (hS1 hs) x, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    unfold logRem; ring
  · show Complex.exp (g s + ∑' v, logRem χ v s) = heckeLFunction χ s
    exact (L_eq_on_line χ s (hS s hs) (g s) (hg'.tendsto_at hs)).symm

end hecke

end MasulloGRH.PEP

open MasulloGRH NumberField IsDedekindDomain in
theorem solution
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    (¬ χ.IsTrivialOnNormOne → TendstoLocallyUniformlyOn
      (fun (x : ℝ) (s : ℂ) => ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x),
        (eulerFactorInv χ v s)⁻¹)
      (heckeLFunction χ) Filter.atTop {s : ℂ | s.re = 1}) ∧
    (∀ t₀ : ℝ, χ.IsNormPower t₀ → TendstoLocallyUniformlyOn
      (fun (x : ℝ) (s : ℂ) => ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x),
        (eulerFactorInv χ v s)⁻¹)
      (heckeLFunction χ) Filter.atTop {s : ℂ | s.re = 1 ∧ s.im ≠ t₀}) := by
  obtain ⟨h1, h2⟩ := MasulloGRH.prime_sums_converge_on_one_line F χ
  refine ⟨fun h => ?_, fun t₀ ht => ?_⟩
  · obtain ⟨g, hg⟩ := h1 h
    exact MasulloGRH.PEP.reduction χ _ (fun s hs => hs) g hg
  · obtain ⟨g, hg⟩ := h2 t₀ ht
    exact MasulloGRH.PEP.reduction χ _ (fun s hs => hs.1) g hg
