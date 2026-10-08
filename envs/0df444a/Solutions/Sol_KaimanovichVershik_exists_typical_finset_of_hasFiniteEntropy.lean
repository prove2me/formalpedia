-- Prove2me | solution 1 for KaimanovichVershik.exists_typical_finset_of_hasFiniteEntropy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-05T23:00:48.154888+00:00
-- url     : https://prove2.me/submissions/5accf075-37ed-4714-a80c-5aa71d9187ec

import Mathlib
import Definitions.Def_ErschlerZheng_Walks
import Theorems.Thm_ErschlerZheng_hasFiniteEntropy_convPow_and_tendsto_entropy_convPow_div

section
/-!
# C1: Avez's asymptotic entropy exists (Erschler–Zheng p. 10)

`H(μ^{(n)})/n → h_μ`: entropy is subadditive under convolution, `H(μ ⋆ ν) ≤ H(μ) + H(ν)`,
so `n ↦ H(μ^{(n)})` is subadditive and Fekete's lemma applies.

All bookkeeping is done in `ℝ≥0∞`, where the series need no summability side conditions.
-/

namespace ErschlerZheng

namespace EntropyDev

open scoped ENNReal

set_option linter.unusedSectionVars false

variable {Γ : Type*} [Group Γ]

/-- The entropy series in `[0, ∞]`. -/
noncomputable def entE (μ : Γ → ℝ) : ℝ≥0∞ := ∑' g, ENNReal.ofReal (Real.negMulLog (μ g))

/-- Convolution of `[0, ∞]`-valued functions. -/
noncomputable def convE (a b : Γ → ℝ≥0∞) : Γ → ℝ≥0∞ := fun g => ∑' h, a h * b (h⁻¹ * g)

lemma le_one_of_isProb {μ : Γ → ℝ} (hμ : IsProbability μ) (g : Γ) : μ g ≤ 1 :=
  le_hasSum hμ.2 g (fun j _ => hμ.1 j)

lemma tsum_ofReal_of_isProb {μ : Γ → ℝ} (hμ : IsProbability μ) :
    ∑' g, ENNReal.ofReal (μ g) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg hμ.1 hμ.2.summable, hμ.2.tsum_eq, ENNReal.ofReal_one]

lemma isProb_of_tsum_ofReal {f : Γ → ℝ} (h0 : ∀ g, 0 ≤ f g)
    (h : ∑' g, ENNReal.ofReal (f g) = 1) : IsProbability f := by
  have hs : Summable f := by
    have := ENNReal.summable_toReal (f := fun g => ENNReal.ofReal (f g))
      (by rw [h]; exact ENNReal.one_ne_top)
    simpa [ENNReal.toReal_ofReal (h0 _)] using this
  refine ⟨h0, hs.hasSum_iff.mpr ?_⟩
  have := ENNReal.ofReal_tsum_of_nonneg h0 hs
  rw [h] at this
  exact ENNReal.ofReal_eq_one.mp this

lemma tsum_mulLeft_eq (F : Γ → ℝ≥0∞) (k : Γ) : ∑' m, F (k * m) = ∑' h, F h :=
  (Equiv.mulLeft k).tsum_eq F

lemma conv_summand_summable {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) (g : Γ) :
    Summable fun h => μ h * ν (h⁻¹ * g) := by
  refine Summable.of_nonneg_of_le (fun h => mul_nonneg (hμ.1 h) (hν.1 _)) (fun h => ?_)
    hμ.2.summable
  calc μ h * ν (h⁻¹ * g) ≤ μ h * 1 :=
        mul_le_mul_of_nonneg_left (le_one_of_isProb hν _) (hμ.1 h)
    _ = μ h := mul_one _

lemma conv_nonneg {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) (g : Γ) :
    0 ≤ conv μ ν g :=
  tsum_nonneg fun h => mul_nonneg (hμ.1 h) (hν.1 _)

lemma ofReal_conv {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) (g : Γ) :
    ENNReal.ofReal (conv μ ν g) =
      convE (fun x => ENNReal.ofReal (μ x)) (fun x => ENNReal.ofReal (ν x)) g := by
  unfold conv convE
  rw [ENNReal.ofReal_tsum_of_nonneg (fun h => mul_nonneg (hμ.1 h) (hν.1 _))
    (conv_summand_summable hμ hν g)]
  congr 1
  ext h
  rw [ENNReal.ofReal_mul (hμ.1 h)]

lemma isProb_conv {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) :
    IsProbability (conv μ ν) := by
  refine isProb_of_tsum_ofReal (conv_nonneg hμ hν) ?_
  simp_rw [ofReal_conv hμ hν]
  unfold convE
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  have : ∀ h : Γ, ∑' g, ENNReal.ofReal (ν (h⁻¹ * g)) = 1 := fun h => by
    rw [tsum_mulLeft_eq (fun x => ENNReal.ofReal (ν x)) h⁻¹]
    exact tsum_ofReal_of_isProb hν
  simp_rw [this, mul_one]
  exact tsum_ofReal_of_isProb hμ

lemma convE_assoc (a b c : Γ → ℝ≥0∞) : convE (convE a b) c = convE a (convE b c) := by
  ext g
  unfold convE
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  congr 1
  ext k
  rw [← ENNReal.tsum_mul_left]
  rw [← tsum_mulLeft_eq _ k]
  congr 1
  ext m
  simp only [mul_inv_rev, inv_mul_cancel_left, mul_assoc]

lemma conv_assoc {a b c : Γ → ℝ} (ha : IsProbability a) (hb : IsProbability b)
    (hc : IsProbability c) : conv (conv a b) c = conv a (conv b c) := by
  ext g
  have h1 := ofReal_conv (isProb_conv ha hb) hc g
  have h2 := ofReal_conv ha (isProb_conv hb hc) g
  have e1 : (fun x => ENNReal.ofReal (conv a b x)) =
      convE (fun x => ENNReal.ofReal (a x)) (fun x => ENNReal.ofReal (b x)) :=
    funext (ofReal_conv ha hb)
  have e2 : (fun x => ENNReal.ofReal (conv b c x)) =
      convE (fun x => ENNReal.ofReal (b x)) (fun x => ENNReal.ofReal (c x)) :=
    funext (ofReal_conv hb hc)
  rw [e1] at h1
  rw [e2, ← convE_assoc, ← h1] at h2
  exact (ENNReal.ofReal_eq_ofReal_iff (conv_nonneg (isProb_conv ha hb) hc g)
    (conv_nonneg ha (isProb_conv hb hc) g)).mp h2.symm

open scoped Classical in
lemma conv_delta (a : Γ → ℝ) : conv a (fun g => if g = 1 then 1 else 0) = a := by
  ext g
  unfold conv
  rw [tsum_eq_single g]
  · simp
  · intro h hh
    have : h⁻¹ * g ≠ 1 := by
      intro e
      apply hh
      rw [inv_mul_eq_one] at e
      exact e
    simp [this]

lemma isProb_convPow {μ : Γ → ℝ} (hμ : IsProbability μ) (n : ℕ) :
    IsProbability (convPow μ n) := by
  induction n with
  | zero =>
    classical
    refine ⟨fun g => ?_, ?_⟩
    · simp only [convPow]; split_ifs <;> norm_num
    · have : convPow μ 0 = fun g => if g = 1 then (1 : ℝ) else 0 := by
        ext g; simp only [convPow]
      rw [this]
      convert hasSum_ite_eq (1 : Γ) (1 : ℝ) using 1
  | succ n ih => exact isProb_conv ih hμ

lemma convPow_add {μ : Γ → ℝ} (hμ : IsProbability μ) (m n : ℕ) :
    convPow μ (m + n) = conv (convPow μ m) (convPow μ n) := by
  induction n with
  | zero =>
    classical
    have : convPow μ 0 = fun g => if g = 1 then (1 : ℝ) else 0 := by
      ext g; simp only [convPow]
    rw [this, conv_delta]
    rfl
  | succ n ih =>
    rw [← add_assoc]
    show conv (convPow μ (m + n)) μ = conv (convPow μ m) (conv (convPow μ n) μ)
    rw [ih, conv_assoc (isProb_convPow hμ m) (isProb_convPow hμ n) hμ]

/-- The pointwise step: `-q log q ≤ Σ_h -t_h log t_h` where `q = Σ_h t_h`. -/
lemma ofReal_negMulLog_conv_le {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν)
    (g : Γ) :
    ENNReal.ofReal (Real.negMulLog (conv μ ν g)) ≤
      ∑' h, ENNReal.ofReal (Real.negMulLog (μ h * ν (h⁻¹ * g))) := by
  set q := conv μ ν g with hq
  have hq0 : 0 ≤ q := conv_nonneg hμ hν g
  have hq1 : q ≤ 1 := le_one_of_isProb (isProb_conv hμ hν) g
  have hlog : 0 ≤ -Real.log q := by
    have := Real.log_nonpos hq0 hq1
    linarith
  have hs := conv_summand_summable hμ hν g
  have ht0 : ∀ h, 0 ≤ μ h * ν (h⁻¹ * g) := fun h => mul_nonneg (hμ.1 h) (hν.1 _)
  have key : Real.negMulLog q = ∑' h, μ h * ν (h⁻¹ * g) * (-Real.log q) := by
    rw [tsum_mul_right, Real.negMulLog]
    rw [hq]
    unfold conv
    ring
  rw [key, ENNReal.ofReal_tsum_of_nonneg (fun h => mul_nonneg (ht0 h) hlog)
    (hs.mul_right _)]
  refine ENNReal.tsum_le_tsum fun h => ENNReal.ofReal_le_ofReal ?_
  set t := μ h * ν (h⁻¹ * g) with ht
  rcases (ht0 h).lt_or_eq with htp | htz
  · have htq : t ≤ q := hs.le_tsum h (fun j _ => ht0 j)
    have : Real.log t ≤ Real.log q := Real.log_le_log htp htq
    rw [Real.negMulLog]
    nlinarith
  · rw [ht, ← htz]
    simp

lemma entE_conv_le {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) :
    entE (conv μ ν) ≤ entE μ + entE ν := by
  unfold entE
  calc ∑' g, ENNReal.ofReal (Real.negMulLog (conv μ ν g))
      ≤ ∑' g, ∑' h, ENNReal.ofReal (Real.negMulLog (μ h * ν (h⁻¹ * g))) :=
        ENNReal.tsum_le_tsum fun g => ofReal_negMulLog_conv_le hμ hν g
    _ = ∑' h, ∑' k, ENNReal.ofReal (Real.negMulLog (μ h * ν k)) := by
        rw [ENNReal.tsum_comm]
        congr 1
        ext h
        rw [← tsum_mulLeft_eq _ h]
        simp only [inv_mul_cancel_left]
    _ = ∑' h, ∑' k, (ENNReal.ofReal (ν k) * ENNReal.ofReal (Real.negMulLog (μ h)) +
          ENNReal.ofReal (μ h) * ENNReal.ofReal (Real.negMulLog (ν k))) := by
        congr 1; ext h; congr 1; ext k
        have a0 := Real.negMulLog_nonneg (hμ.1 h) (le_one_of_isProb hμ h)
        have b0 := Real.negMulLog_nonneg (hν.1 k) (le_one_of_isProb hν k)
        rw [Real.negMulLog_mul, ENNReal.ofReal_add (mul_nonneg (hν.1 k) a0)
          (mul_nonneg (hμ.1 h) b0), ENNReal.ofReal_mul (hν.1 k), ENNReal.ofReal_mul (hμ.1 h)]
    _ = ∑' g, ENNReal.ofReal (Real.negMulLog (μ g)) +
          ∑' g, ENNReal.ofReal (Real.negMulLog (ν g)) := by
        simp_rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left,
          tsum_ofReal_of_isProb hν, one_mul]
        rw [ENNReal.tsum_mul_right, tsum_ofReal_of_isProb hμ, one_mul]

lemma entropy_eq_toReal {μ : Γ → ℝ} (hμ : IsProbability μ) : entropy μ = (entE μ).toReal := by
  unfold entropy entE
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  congr 1
  ext g
  rw [ENNReal.toReal_ofReal (Real.negMulLog_nonneg (hμ.1 g) (le_one_of_isProb hμ g))]

end EntropyDev

end ErschlerZheng
end

section
/-!
# Path space of a random walk (helpers for B7, B8)

Originally for B7: a shift-invariant event of intermediate probability gives a non-trivial Poisson boundary
(Kaimanovich–Vershik, pp. 9–10)

`F(y) = ℙ_y(A)` is `μ`-harmonic by the Markov property at the first step: under the product
measure, a path is its first increment followed by an independent path (`head_tail`), and
shift-invariance turns `W ∈ A` into `(path from y ξ_0) ∈ A`. If `F` were constant `= c` on the
points reachable from `x`, induction on the rank of a cylinder gives
`ℙ(S ∩ W_x⁻¹A) = c ℙ(S)` for every cylinder `S`; the cylinders generate the product σ-algebra,
so `ℙ(W_x⁻¹A) = c²` and `c ∈ {0, 1}`.
-/

open MeasureTheory

namespace ErschlerZheng

namespace B7Dev

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {Γ : Type*} [Group Γ] [Countable Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]

theorem stepMeasure_apply (μ : Γ → ℝ) (s : Set Γ) :
    stepMeasure μ s = ∑' g, ENNReal.ofReal (μ g) * s.indicator 1 g := by
  unfold stepMeasure
  rw [Measure.sum_apply _ (DiscreteMeasurableSpace.forall_measurableSet s)]
  congr 1; funext g
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _
    (DiscreteMeasurableSpace.forall_measurableSet s)]

theorem isProbabilityMeasure_stepMeasure {μ : Γ → ℝ} (hμ : IsProbability μ) :
    IsProbabilityMeasure (stepMeasure μ) := by
  constructor
  rw [stepMeasure_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg hμ.1 hμ.2.summable, hμ.2.tsum_eq, ENNReal.ofReal_one]

theorem lintegral_stepMeasure (μ : Γ → ℝ) (f : Γ → ENNReal) :
    ∫⁻ z, f z ∂stepMeasure μ = ∑' z, ENNReal.ofReal (μ z) * f z := by
  unfold stepMeasure
  rw [lintegral_sum_measure]
  congr 1; funext z
  rw [lintegral_smul_measure, lintegral_dirac]
  rfl


end B7Dev

end ErschlerZheng
end

section
/-!
# C2, the easy direction: zero asymptotic entropy forces a trivial Poisson boundary

For a probability `μ` of finite entropy with `h_μ = 0`, every bounded `μ`-harmonic function is
constant on the submonoid generated by the support of `μ`.

Write `ν = μ^{(n)}`, `p_g = δ_g ⋆ ν` (so `p_g(z) = ν(g⁻¹z)`) and `q = μ^{(n+1)} = μ ⋆ ν = Σ_g μ(g) p_g`.

* Jensen gap: for each `z`, `J_z := φ(q_z) − Σ_g μ(g) φ(p_g(z)) = Σ_g μ(g) ψ(p_g(z), q_z)` with
  `φ = negMulLog` and `ψ(p, q) = p log p − p log q − p + q ⩾ 0` (a Kullback–Leibler summand), and
  `Σ_z J_z = H(μ^{(n+1)}) − H(μ^{(n)}) =: Δ_n`.
* Pinsker-type bound: `|p − q| ⩽ ψ(p, q)/(2ε) + ε(p + q)` (from `ψ ⩾ (√p − √q)²`), so
  `‖p_g − q‖₁ ⩽ Δ_n/(2εμ(g)) + 2ε`.
* `Σ_{k<N} Δ_k = H(μ^{(N)})` and `H(μ^{(N)})/N → h_μ = 0`, so `inf_n Δ_n = 0`.
* A bounded harmonic `f` satisfies `f(x) = Σ_z f(xz) μ^{(n)}(z)` for every `n`, hence
  `|f(xg) − f(x)| ⩽ sup|f| · ‖p_g − q‖₁`; so `f(xg) = f(x)` for `g ∈ supp μ`.
-/

namespace ErschlerZheng

namespace P5Dev

open EntropyDev

set_option linter.unusedSectionVars false

variable {Γ : Type*} [Group Γ]

lemma entropy_convPow_zero (μ : Γ → ℝ) : entropy (convPow μ 0) = 0 := by
  classical
  have : convPow μ 0 = fun g => if g = 1 then (1 : ℝ) else 0 := by
    ext g; simp only [convPow]
  rw [this]
  unfold entropy
  rw [tsum_eq_single 1]
  · simp
  · intro b hb
    simp [hb]


/-! ### The Kullback–Leibler summand and a Pinsker-type bound -/

/-! ### The Jensen gap of the entropy at one step -/


/-! ### From the entropy increment to the total variation distance -/

/-! ### The theorem: `h_μ = 0` forces the Poisson boundary to be trivial -/

end P5Dev

end ErschlerZheng
end

section
/-!
# C2, the converse direction: tools for "trivial Poisson boundary ⇒ `h_μ = 0`"

Two steps that need no aperiodicity:

* (duality) if `‖μ^{(n+1)} − μ^{(n)}‖₁ → 0` and every bounded harmonic function is constant on the
  submonoid generated by `supp μ`, then `‖δ_g ⋆ μ^{(n)} − μ^{(n)}‖₁ → 0` for `g` in that submonoid:
  otherwise an ultrafilter limit of `x ↦ Σ_w s_n(xw) μ^{(n)}(w)`, `s_n` the sign of
  `δ_g ⋆ μ^{(n)} − μ^{(n)}`, is a bounded harmonic function separating `g` from `1`;
* (entropy) the likelihood ratio `p_g / q ⩽ 1/μ(g)` is bounded, so each Kullback–Leibler summand
  is at most `(1 − log μ(g)) |p − q|`, and `Δ_n ⩽ Σ_g (μ(g) + φ(μ(g))) ‖δ_g ⋆ μ^{(n)} − μ^{(n+1)}‖₁`;
  if every `‖δ_g ⋆ μ^{(n)} − μ^{(n+1)}‖₁ → 0` (`g ∈ supp μ`) then `Δ_n → 0` by dominated
  convergence, and `h_μ = 0` (Cesàro).
-/

namespace ErschlerZheng

namespace P5Dev

open EntropyDev Filter Topology

set_option linter.unusedSectionVars false

variable {Γ : Type*} [Group Γ]

/-! ### Duality: a trivial boundary forces `‖δ_g ⋆ μ^{(n)} − μ^{(n)}‖₁ → 0` -/

/-! ### Entropy: bounded likelihood ratios -/

end P5Dev

end ErschlerZheng
end

section
/-!
# C2, the converse direction via the lazy walk

`μ' = (δ_1 + μ)/2` has the same bounded harmonic functions as `μ`, and its support generates no
more than that of `μ`. Its convolution powers are binomial mixtures,
`μ'^{(n)} = Σ_k C(n,k) 2^{-n} μ^{(k)}`, so

* (aperiodicity) `‖μ'^{(n+1)} − μ'^{(n)}‖₁ ⩽ Σ_k |C(n+1,k)/2^{n+1} − C(n,k)/2^n| ⩽ 1/√(n+1)`
  (the difference is `C(n+1,k)(2k − n − 1)/((n+1)2^{n+1})`, and the binomial variance is `(n+1)/4`);
* (entropy) `H(μ'^{(n)}) ⩾ Σ_k C(n,k)2^{-n} H(μ^{(k)}) ⩾ Σ_k C(n,k)2^{-n} k h_μ = n h_μ / 2`
  (concavity of `−t log t`, and Fekete: `H(μ^{(k)}) ⩾ k h_μ`), so `h_μ ⩽ 2 h_{μ'}`.

With `P5Converse`: a trivial boundary for `μ` is trivial for `μ'`, so
`‖δ_g ⋆ μ'^{(n)} − μ'^{(n+1)}‖₁ → 0` for `g ∈ supp μ'`, so `h_{μ'} = 0`, so `h_μ = 0`.
-/

namespace ErschlerZheng

namespace P5Dev

open EntropyDev Filter Topology

set_option linter.unusedSectionVars false

variable {Γ : Type*} [Group Γ]

/-! ### The binomial expansion -/

/-! ### Aperiodicity of the lazy walk -/

/-! ### Entropy of the lazy walk: `h_μ ⩽ 2 h_{μ'}` -/

lemma asymptoticEntropy_nonneg [Countable Γ] {μ : Γ → ℝ} (hμ : IsProbability μ)
    (hH : HasFiniteEntropy μ) : 0 ≤ asymptoticEntropy μ := by
  obtain ⟨_, hT⟩ := hasFiniteEntropy_convPow_and_tendsto_entropy_convPow_div μ hμ hH
  refine ge_of_tendsto hT (Eventually.of_forall fun n => ?_)
  rw [entropy_eq_toReal (isProb_convPow hμ n)]
  positivity

/-! ### The converse: a trivial boundary forces `h_μ = 0` -/

end P5Dev

end ErschlerZheng
end

section
/-!
# C3: typical sets for `μ^{(n)}` (Kaimanovich–Vershik, Erschler–Zheng p. 10)

The Shannon–McMillan–Breiman theorem in probability: `−(1/n) log μ^{(n)}(W_n) → h_μ` in
probability. Fix a block length `k`, write `n = r + qk` (`r < k`) and realise `W_n` as
`ω_0 ω_1 ⋯ ω_q` with independent `ω_0 ∼ μ^{(r)}`, `ω_i ∼ μ^{(k)}` (`i ⩾ 1`). Since
`μ^{(n)}(ω_0 ⋯ ω_q) ⩾ μ^{(r)}(ω_0) Π μ^{(k)}(ω_i)`,
`I_n(W) := −log μ^{(n)}(W) = A − D` with `A = −log μ^{(r)}(ω_0) + Σ_{i ⩽ q} −log μ^{(k)}(ω_i)` and
`D ⩾ 0`, `𝔼 D = H_r + q H_k − H_n ⩽ H_r + qk(H_k/k − h)` (Fekete: `H_n ⩾ n h`). The law of large
numbers (Mathlib's `strong_law_ae`) concentrates `A/n` near `H_k/k`, Markov's inequality makes
`D/n` small with high probability once `H_k/k − h` is small, so `I_n(W)/n ∈ [h − ε, h + ε]` with
probability `⩾ 1 − ε`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ErschlerZheng

namespace P5SMB

open EntropyDev B7Dev P5Dev

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {Γ : Type*} [Group Γ] [Countable Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]

open scoped Classical in
/-- Coordinate `0` has law `a`, the others law `b`. -/
noncomputable def blockLaw (a b : Γ → ℝ) (i : ℕ) : Measure Γ :=
  if i = 0 then stepMeasure a else stepMeasure b

lemma isProbabilityMeasure_blockLaw {a b : Γ → ℝ} (ha : IsProbability a) (hb : IsProbability b)
    (i : ℕ) : IsProbabilityMeasure (blockLaw a b i) := by
  unfold blockLaw
  split_ifs
  · exact isProbabilityMeasure_stepMeasure ha
  · exact isProbabilityMeasure_stepMeasure hb

/-- `ω_0 ω_1 ⋯ ω_q`. -/
def prodUpTo (ω : ℕ → Γ) : ℕ → Γ
  | 0 => ω 0
  | q + 1 => prodUpTo ω q * ω (q + 1)

lemma prodUpTo_congr {ω ω' : ℕ → Γ} (q : ℕ) (h : ∀ i ≤ q, ω i = ω' i) :
    prodUpTo ω q = prodUpTo ω' q := by
  induction q with
  | zero => exact h 0 le_rfl
  | succ q ih =>
    simp only [prodUpTo]
    rw [ih fun i hi => h i (by omega), h (q + 1) le_rfl]

lemma measurable_prodUpTo (q : ℕ) : Measurable fun ω : ℕ → Γ => prodUpTo ω q := by
  induction q with
  | zero => exact measurable_pi_apply 0
  | succ q ih =>
    have hm : Measurable fun p : Γ × Γ => p.1 * p.2 := measurable_of_countable _
    exact hm.comp (ih.prodMk (measurable_pi_apply (q + 1)))

/-- `a ⋆ b ⋆ ⋯ ⋆ b` (`q` copies of `b`). -/
noncomputable def iterConv (a b : Γ → ℝ) : ℕ → Γ → ℝ
  | 0 => a
  | q + 1 => conv (iterConv a b q) b

lemma isProb_iterConv {a b : Γ → ℝ} (ha : IsProbability a) (hb : IsProbability b) (q : ℕ) :
    IsProbability (iterConv a b q) := by
  induction q with
  | zero => exact ha
  | succ q ih => exact isProb_conv ih hb

lemma stepMeasure_singleton (ν : Γ → ℝ) (z : Γ) : stepMeasure ν {z} = ENNReal.ofReal (ν z) := by
  rw [stepMeasure_apply, tsum_eq_single z]
  · simp
  · intro b hb
    simp [Set.indicator, hb]

lemma indep_prodUpTo {a b : Γ → ℝ} [∀ i, IsProbabilityMeasure (blockLaw a b i)] (q : ℕ) :
    IndepFun (fun ω : ℕ → Γ => prodUpTo ω q) (fun ω => ω (q + 1))
      (Measure.infinitePi (blockLaw a b)) := by
  have hall : iIndepFun (fun i (ω : ℕ → Γ) => ω i) (Measure.infinitePi (blockLaw a b)) :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hS := hall.indepFun_finset (Finset.range (q + 1)) {q + 1}
    (by simp) (fun i => measurable_pi_apply i)
  let φ : (Finset.range (q + 1) → Γ) → Γ := fun v =>
    prodUpTo (fun i => if h : i ∈ Finset.range (q + 1) then v ⟨i, h⟩ else 1) q
  let ψ : (({q + 1} : Finset ℕ) → Γ) → Γ := fun v => v ⟨q + 1, Finset.mem_singleton_self _⟩
  have h := hS.comp (measurable_of_countable φ) (measurable_of_countable ψ)
  convert h using 1
  · funext ω
    simp only [Function.comp_apply, φ]
    apply prodUpTo_congr
    intro i hi
    have : i ∈ Finset.range (q + 1) := Finset.mem_range.mpr (by omega)
    simp [this]
  · rfl

/-- The law of `ω_0 ⋯ ω_q` is `a ⋆ b^{⋆q}`. -/
lemma map_prodUpTo {a b : Γ → ℝ} (ha : IsProbability a) (hb : IsProbability b)
    [∀ i, IsProbabilityMeasure (blockLaw a b i)] (q : ℕ) :
    (Measure.infinitePi (blockLaw a b)).map (fun ω => prodUpTo ω q) =
      stepMeasure (iterConv a b q) := by
  induction q with
  | zero =>
    show (Measure.infinitePi (blockLaw a b)).map (fun ω => ω 0) = _
    rw [Measure.infinitePi_map_eval]
    simp [blockLaw, iterConv]
  | succ q ih =>
    rw [Measure.ext_iff_singleton]
    intro z
    rw [Measure.map_apply (measurable_prodUpTo (q + 1)) (measurableSet_singleton z),
      stepMeasure_singleton]
    have hset : (fun ω : ℕ → Γ => prodUpTo ω (q + 1)) ⁻¹' {z} =
        ⋃ x : Γ, ((fun ω : ℕ → Γ => prodUpTo ω q) ⁻¹' {x} ∩
          (fun ω : ℕ → Γ => ω (q + 1)) ⁻¹' {x⁻¹ * z}) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
        prodUpTo]
      constructor
      · intro h
        refine ⟨prodUpTo ω q, rfl, ?_⟩
        rw [← h]; group
      · rintro ⟨x, rfl, h⟩
        rw [h]; group
    rw [hset, measure_iUnion]
    · have hind := indep_prodUpTo (a := a) (b := b) q
      simp_rw [hind.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton _)
        (measurableSet_singleton _)]
      have h1 : ∀ x, Measure.infinitePi (blockLaw a b) ((fun ω => prodUpTo ω q) ⁻¹' {x}) =
          ENNReal.ofReal (iterConv a b q x) := by
        intro x
        rw [← Measure.map_apply (measurable_prodUpTo q) (measurableSet_singleton x), ih,
          stepMeasure_singleton]
      have h2 : ∀ y, Measure.infinitePi (blockLaw a b) ((fun ω : ℕ → Γ => ω (q + 1)) ⁻¹' {y}) =
          ENNReal.ofReal (b y) := by
        intro y
        rw [← Measure.map_apply (measurable_pi_apply (q + 1)) (measurableSet_singleton y),
          Measure.infinitePi_map_eval]
        simp [blockLaw, stepMeasure_singleton]
      simp_rw [h1, h2]
      rw [show iterConv a b (q + 1) = conv (iterConv a b q) b from rfl,
        ofReal_conv (isProb_iterConv ha hb q) hb z]
      rfl
    · intro x y hxy
      refine Set.disjoint_left.mpr fun ω h1 h2 => hxy ?_
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
      rw [← h1.1, ← h2.1]
    · intro x
      exact ((measurable_prodUpTo q) (measurableSet_singleton x)).inter
        ((measurable_pi_apply (q + 1)) (measurableSet_singleton _))

/-! ### Integrals over discrete laws -/

lemma integral_stepMeasure_nonneg {ν : Γ → ℝ} (hν : IsProbability ν) {f : Γ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hs : Summable fun x => ν x * f x) :
    Integrable f (stepMeasure ν) ∧ ∫ x, f x ∂(stepMeasure ν) = ∑' x, ν x * f x := by
  have hl : ∫⁻ x, ENNReal.ofReal (f x) ∂(stepMeasure ν) = ENNReal.ofReal (∑' x, ν x * f x) := by
    rw [lintegral_stepMeasure, ENNReal.ofReal_tsum_of_nonneg
      (fun x => mul_nonneg (hν.1 x) (hf x)) hs]
    congr 1; ext x
    rw [ENNReal.ofReal_mul (hν.1 x)]
  have hm : AEStronglyMeasurable f (stepMeasure ν) := (Measurable.of_discrete).aestronglyMeasurable
  refine ⟨⟨hm, ?_⟩, ?_⟩
  · unfold HasFiniteIntegral
    simp_rw [Real.enorm_of_nonneg (hf _)]
    rw [hl]; exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf) hm, hl,
      ENNReal.toReal_ofReal (tsum_nonneg fun x => mul_nonneg (hν.1 x) (hf x))]

/-- `−log ν`, the information function. -/
noncomputable def info (ν : Γ → ℝ) (x : Γ) : ℝ := -Real.log (ν x)

lemma info_nonneg {ν : Γ → ℝ} (hν : IsProbability ν) (x : Γ) : 0 ≤ info ν x := by
  unfold info
  have := Real.log_nonpos (hν.1 x) (le_one_of_isProb hν x)
  linarith

lemma integral_info {ν : Γ → ℝ} (hν : IsProbability ν) (hH : HasFiniteEntropy ν) :
    Integrable (info ν) (stepMeasure ν) ∧ ∫ x, info ν x ∂(stepMeasure ν) = entropy ν := by
  have e : ∀ x, ν x * info ν x = Real.negMulLog (ν x) := fun x => by
    unfold info Real.negMulLog; ring
  have hs : Summable fun x => ν x * info ν x := by simp_rw [e]; exact hH
  obtain ⟨h1, h2⟩ := integral_stepMeasure_nonneg hν (info_nonneg hν) hs
  refine ⟨h1, ?_⟩
  rw [h2]; simp_rw [e]; rfl

/-! ### The probability space of blocks -/

section Blocks

variable {a b : Γ → ℝ} [hP : ∀ i, IsProbabilityMeasure (blockLaw a b i)]


lemma map_eval_zero : (Measure.infinitePi (blockLaw a b)).map (fun ω : ℕ → Γ => ω 0) = stepMeasure a := by
  rw [Measure.infinitePi_map_eval]; simp [blockLaw]

lemma map_eval_succ (i : ℕ) : (Measure.infinitePi (blockLaw a b)).map (fun ω : ℕ → Γ => ω (i + 1)) = stepMeasure b := by
  rw [Measure.infinitePi_map_eval]; simp [blockLaw]

lemma ae_pos_zero : ∀ᵐ ω ∂(Measure.infinitePi (blockLaw a b)), 0 < a (ω 0) := by
  have h : (Measure.infinitePi (blockLaw a b)) {ω | ¬ 0 < a (ω 0)} = 0 := by
    have hm : MeasurableSet {x : Γ | ¬ 0 < a x} := DiscreteMeasurableSpace.forall_measurableSet _
    rw [show {ω : ℕ → Γ | ¬ 0 < a (ω 0)} = (fun ω : ℕ → Γ => ω 0) ⁻¹' {x | ¬ 0 < a x} from rfl,
      ← Measure.map_apply (measurable_pi_apply 0) hm, map_eval_zero, stepMeasure_apply]
    refine ENNReal.tsum_eq_zero.mpr fun x => ?_
    by_cases hx : 0 < a x
    · simp [Set.indicator, hx]
    · rw [ENNReal.ofReal_eq_zero.mpr (not_lt.mp hx), zero_mul]
  exact measure_eq_zero_iff_ae_notMem.mp h |>.mono fun ω hω => by simpa using hω

lemma ae_pos_succ : ∀ᵐ ω ∂(Measure.infinitePi (blockLaw a b)), ∀ i, 0 < b (ω (i + 1)) := by
  rw [ae_all_iff]
  intro i
  have h : (Measure.infinitePi (blockLaw a b)) {ω | ¬ 0 < b (ω (i + 1))} = 0 := by
    have hm : MeasurableSet {x : Γ | ¬ 0 < b x} := DiscreteMeasurableSpace.forall_measurableSet _
    rw [show {ω : ℕ → Γ | ¬ 0 < b (ω (i + 1))} =
        (fun ω : ℕ → Γ => ω (i + 1)) ⁻¹' {x | ¬ 0 < b x} from rfl,
      ← Measure.map_apply (measurable_pi_apply (i + 1)) hm, map_eval_succ, stepMeasure_apply]
    refine ENNReal.tsum_eq_zero.mpr fun x => ?_
    by_cases hx : 0 < b x
    · simp [Set.indicator, hx]
    · rw [ENNReal.ofReal_eq_zero.mpr (not_lt.mp hx), zero_mul]
  exact measure_eq_zero_iff_ae_notMem.mp h |>.mono fun ω hω => by simpa using hω

/-- `A_q(ω) = −log a(ω_0) + Σ_{i<q} −log b(ω_{i+1})`. -/
noncomputable def Asum (a b : Γ → ℝ) (ω : ℕ → Γ) (q : ℕ) : ℝ :=
  info a (ω 0) + ∑ i ∈ Finset.range q, info b (ω (i + 1))

lemma info_iterConv_le (ha : IsProbability a) (hb : IsProbability b) (ω : ℕ → Γ)
    (h0 : 0 < a (ω 0)) (hpos : ∀ i, 0 < b (ω (i + 1))) (q : ℕ) :
    info (iterConv a b q) (prodUpTo ω q) ≤ Asum a b ω q := by
  -- the product of the laws along `ω`
  have key : ∀ q, ∃ L, 0 < L ∧ L ≤ iterConv a b q (prodUpTo ω q) ∧
      -Real.log L = Asum a b ω q := by
    intro q
    induction q with
    | zero => exact ⟨a (ω 0), h0, le_rfl, by simp [Asum, info]⟩
    | succ q ih =>
      obtain ⟨L, hL0, hLle, hLlog⟩ := ih
      refine ⟨L * b (ω (q + 1)), mul_pos hL0 (hpos q), ?_, ?_⟩
      · show L * b (ω (q + 1)) ≤ conv (iterConv a b q) b (prodUpTo ω q * ω (q + 1))
        have hc := isProb_iterConv ha hb q
        have hle : iterConv a b q (prodUpTo ω q) *
            b ((prodUpTo ω q)⁻¹ * (prodUpTo ω q * ω (q + 1))) ≤
            conv (iterConv a b q) b (prodUpTo ω q * ω (q + 1)) :=
          (conv_summand_summable hc hb _).le_tsum (prodUpTo ω q)
            (fun j _ => mul_nonneg (hc.1 j) (hb.1 _))
        rw [inv_mul_cancel_left] at hle
        exact (mul_le_mul_of_nonneg_right hLle (hb.1 _)).trans hle
      · rw [Real.log_mul hL0.ne' (hpos q).ne']
        simp only [Asum, info, Finset.sum_range_succ] at hLlog ⊢
        linarith
  obtain ⟨L, hL0, hLle, hLlog⟩ := key q
  unfold info
  rw [← hLlog]
  have := Real.log_le_log hL0 hLle
  linarith


lemma iterConv_pos (ha : IsProbability a) (hb : IsProbability b) (ω : ℕ → Γ)
    (h0 : 0 < a (ω 0)) (hpos : ∀ i, 0 < b (ω (i + 1))) (q : ℕ) :
    0 < iterConv a b q (prodUpTo ω q) := by
  induction q with
  | zero => exact h0
  | succ q ih =>
    show 0 < conv (iterConv a b q) b (prodUpTo ω q * ω (q + 1))
    have hc := isProb_iterConv ha hb q
    have hle : iterConv a b q (prodUpTo ω q) *
        b ((prodUpTo ω q)⁻¹ * (prodUpTo ω q * ω (q + 1))) ≤
        conv (iterConv a b q) b (prodUpTo ω q * ω (q + 1)) :=
      (conv_summand_summable hc hb _).le_tsum (prodUpTo ω q)
        (fun j _ => mul_nonneg (hc.1 j) (hb.1 _))
    rw [inv_mul_cancel_left] at hle
    exact lt_of_lt_of_le (mul_pos ih (hpos q)) hle

end Blocks

/-! ### The law of large numbers for the blocks, and the main estimate -/

section Main

variable {a b : Γ → ℝ} [hP : ∀ i, IsProbabilityMeasure (blockLaw a b i)]

lemma integrable_info_zero (ha : IsProbability a) (hHa : HasFiniteEntropy a) :
    Integrable (fun ω : ℕ → Γ => info a (ω 0)) (Measure.infinitePi (blockLaw a b)) ∧
      ∫ ω, info a (ω 0) ∂(Measure.infinitePi (blockLaw a b)) = entropy a := by
  have hmeas : Measurable (info a) := Measurable.of_discrete
  have h := integral_info ha hHa
  rw [← map_eval_zero (a := a) (b := b)] at h
  refine ⟨(integrable_map_measure h.1.1 (measurable_pi_apply 0).aemeasurable).mp h.1, ?_⟩
  rw [← h.2, integral_map (measurable_pi_apply 0).aemeasurable hmeas.aestronglyMeasurable]

lemma integrable_info_succ (hb : IsProbability b) (hHb : HasFiniteEntropy b) (i : ℕ) :
    Integrable (fun ω : ℕ → Γ => info b (ω (i + 1))) (Measure.infinitePi (blockLaw a b)) ∧
      ∫ ω, info b (ω (i + 1)) ∂(Measure.infinitePi (blockLaw a b)) = entropy b := by
  have hmeas : Measurable (info b) := Measurable.of_discrete
  have h := integral_info hb hHb
  rw [← map_eval_succ (a := a) (b := b) i] at h
  refine ⟨(integrable_map_measure h.1.1 (measurable_pi_apply (i + 1)).aemeasurable).mp h.1, ?_⟩
  rw [← h.2, integral_map (measurable_pi_apply (i + 1)).aemeasurable hmeas.aestronglyMeasurable]

lemma slln_blocks (hb : IsProbability b) (hHb : HasFiniteEntropy b) :
    ∀ᵐ ω ∂(Measure.infinitePi (blockLaw a b)),
      Tendsto (fun q : ℕ => (q : ℝ)⁻¹ * ∑ i ∈ Finset.range q, info b (ω (i + 1))) atTop
        (𝓝 (entropy b)) := by
  have hall : iIndepFun (fun i (ω : ℕ → Γ) => ω i) (Measure.infinitePi (blockLaw a b)) :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hmeas : Measurable (info b) := Measurable.of_discrete
  have hindep : Pairwise fun i j => IndepFun (fun ω : ℕ → Γ => info b (ω (i + 1)))
      (fun ω : ℕ → Γ => info b (ω (j + 1))) (Measure.infinitePi (blockLaw a b)) := by
    intro i j hij
    exact (hall.indepFun (by omega : i + 1 ≠ j + 1)).comp hmeas hmeas
  have hident : ∀ i, IdentDistrib (fun ω : ℕ → Γ => info b (ω (i + 1)))
      (fun ω => info b (ω (0 + 1))) (Measure.infinitePi (blockLaw a b))
        (Measure.infinitePi (blockLaw a b)) := by
    intro i
    have h : IdentDistrib (fun ω : ℕ → Γ => ω (i + 1)) (fun ω => ω (0 + 1))
        (Measure.infinitePi (blockLaw a b)) (Measure.infinitePi (blockLaw a b)) :=
      ⟨(measurable_pi_apply _).aemeasurable, (measurable_pi_apply _).aemeasurable, by
        rw [map_eval_succ, map_eval_succ]⟩
    exact h.comp hmeas
  have hs := strong_law_ae (fun i (ω : ℕ → Γ) => info b (ω (i + 1)))
    (integrable_info_succ hb hHb 0).1 hindep hident
  rw [(integrable_info_succ hb hHb 0).2] at hs
  filter_upwards [hs] with ω hω
  simpa [smul_eq_mul] using hω

lemma slln_meas (hb : IsProbability b) (hHb : HasFiniteEntropy b) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun q : ℕ => Measure.infinitePi (blockLaw a b)
      {ω | δ ≤ |(q : ℝ)⁻¹ * ∑ i ∈ Finset.range q, info b (ω (i + 1)) - entropy b|}) atTop
      (𝓝 0) := by
  have hmq : ∀ q : ℕ, Measurable (fun ω : ℕ → Γ =>
      (q : ℝ)⁻¹ * ∑ i ∈ Finset.range q, info b (ω (i + 1))) := by
    intro q
    refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
    exact (Measurable.of_discrete (f := info b)).comp (measurable_pi_apply (i + 1))
  have h := tendstoInMeasure_of_tendsto_ae (μ := Measure.infinitePi (blockLaw a b))
    (f := fun (q : ℕ) (ω : ℕ → Γ) => (q : ℝ)⁻¹ * ∑ i ∈ Finset.range q, info b (ω (i + 1)))
    (g := fun _ => entropy b) (fun q => (hmq q).aestronglyMeasurable) (slln_blocks hb hHb)
  have := h (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)
  convert this using 3 with q
  ext ω
  simp only [Set.mem_ofPred_eq, edist_dist, Real.dist_eq]
  exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).symm

lemma meas_ge_le_of_integral {f : (ℕ → Γ) → ℝ} (hf0 : 0 ≤ᵐ[Measure.infinitePi (blockLaw a b)] f)
    (hfi : Integrable f (Measure.infinitePi (blockLaw a b))) {t : ℝ} (ht : 0 < t) :
    Measure.infinitePi (blockLaw a b) {ω | t ≤ f ω} ≤
      ENNReal.ofReal ((∫ ω, f ω ∂(Measure.infinitePi (blockLaw a b))) / t) := by
  have h := mul_meas_ge_le_integral_of_nonneg hf0 hfi t
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  rw [le_div_iff₀ ht]
  linarith

/-- The main estimate: with probability close to one, `−log (a ⋆ b^{⋆q})(ω_0 ⋯ ω_q)` lies within
`O(q θ)` of `q H(b)`; the defect `Δ_q = H(a) + q H(b) − H(a ⋆ b^{⋆q})` enters through Markov. -/
lemma main_estimate (ha : IsProbability a) (hb : IsProbability b) (hHa : HasFiniteEntropy a)
    (hHb : HasFiniteEntropy b) (hHc : ∀ q, HasFiniteEntropy (iterConv a b q))
    {θ θ' ε' : ℝ} (hθ : 0 < θ) (hθ' : 0 < θ') (hε' : 0 < ε') :
    ∃ Q : ℕ, ∀ q ≥ Q, Measure.infinitePi (blockLaw a b)
      {ω | ¬ ((q : ℝ) * (entropy b - θ - θ') ≤ info (iterConv a b q) (prodUpTo ω q) ∧
        info (iterConv a b q) (prodUpTo ω q) ≤ q * (entropy b + 2 * θ))} ≤
      ENNReal.ofReal (ε' + (entropy a + q * entropy b - entropy (iterConv a b q)) /
        (q * θ')) := by
  set P := Measure.infinitePi (blockLaw a b) with hPdef
  -- the law-of-large-numbers event
  have h1 := slln_meas (a := a) hb hHb hθ
  have h1' : ∀ᶠ q : ℕ in atTop, P {ω | θ ≤ |(q : ℝ)⁻¹ *
      ∑ i ∈ Finset.range q, info b (ω (i + 1)) - entropy b|} < ENNReal.ofReal (ε' / 2) :=
    (tendsto_order.1 h1).2 _ (ENNReal.ofReal_pos.mpr (by positivity))
  obtain ⟨Q1, hQ1⟩ := eventually_atTop.mp h1'
  have hHa0 : 0 ≤ entropy a := by rw [entropy_eq_toReal ha]; positivity
  obtain ⟨Q2, hQ2⟩ : ∃ Q2 : ℕ, 2 * entropy a / (θ * ε') + 1 ≤ Q2 := exists_nat_ge _
  refine ⟨max (max Q1 Q2) 1, fun q hq => ?_⟩
  have hq1 : q ≥ Q1 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq2 : (Q2 : ℝ) ≤ q := by
    exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hqpos : (0 : ℝ) < q := by
    have : 1 ≤ q := le_trans (le_max_right _ _) hq
    exact_mod_cast this
  set W := fun ω : ℕ → Γ => prodUpTo ω q
  set c := iterConv a b q
  have hc := isProb_iterConv ha hb q
  -- the defect `D = A − I`
  set D := fun ω : ℕ → Γ => Asum a b ω q - info c (W ω) with hD
  have hIW : Integrable (fun ω => info c (W ω)) P ∧ ∫ ω, info c (W ω) ∂P = entropy c := by
    have h := integral_info hc (hHc q)
    rw [← map_prodUpTo ha hb q] at h
    refine ⟨(integrable_map_measure h.1.1 (measurable_prodUpTo q).aemeasurable).mp h.1, ?_⟩
    rw [← h.2, integral_map (measurable_prodUpTo q).aemeasurable
      (Measurable.of_discrete (f := info c)).aestronglyMeasurable]
  have hA : Integrable (fun ω => Asum a b ω q) P ∧
      ∫ ω, Asum a b ω q ∂P = entropy a + q * entropy b := by
    have hi : ∀ i ∈ Finset.range q, Integrable (fun ω : ℕ → Γ => info b (ω (i + 1))) P :=
      fun i _ => (integrable_info_succ hb hHb i).1
    refine ⟨((integrable_info_zero (b := b) ha hHa).1.add (integrable_finsetSum _ hi)), ?_⟩
    simp only [Asum]
    rw [integral_add (integrable_info_zero (b := b) ha hHa).1 (integrable_finsetSum _ hi),
      integral_finsetSum _ hi, (integrable_info_zero (b := b) ha hHa).2,
      Finset.sum_congr rfl (fun i _ => (integrable_info_succ (a := a) hb hHb i).2)]
    simp
  have hDi : Integrable D P := hA.1.sub hIW.1
  have hD0 : 0 ≤ᵐ[P] D := by
    filter_upwards [ae_pos_zero (a := a) (b := b), ae_pos_succ (a := a) (b := b)] with ω h0 hs
    have := info_iterConv_le ha hb ω h0 hs q
    simp only [hD, Pi.zero_apply]
    linarith
  have hDint : ∫ ω, D ω ∂P = entropy a + q * entropy b - entropy c := by
    rw [integral_sub hA.1 hIW.1, hA.2, hIW.2]
  -- the three bad events
  set E1 := {ω : ℕ → Γ | θ ≤ |(q : ℝ)⁻¹ * ∑ i ∈ Finset.range q, info b (ω (i + 1)) -
    entropy b|}
  set E2 := {ω : ℕ → Γ | q * θ ≤ info a (ω 0)}
  set E3 := {ω : ℕ → Γ | q * θ' ≤ D ω}
  set G := {ω : ℕ → Γ | 0 < a (ω 0) ∧ ∀ i, 0 < b (ω (i + 1))}
  have hG : P Gᶜ = 0 := by
    have := (ae_pos_zero (a := a) (b := b)).and (ae_pos_succ (a := a) (b := b))
    exact measure_eq_zero_iff_ae_notMem.mpr (this.mono fun ω hω => by simpa [G] using hω)
  have hsub : {ω | ¬ ((q : ℝ) * (entropy b - θ - θ') ≤ info c (W ω) ∧
      info c (W ω) ≤ q * (entropy b + 2 * θ))} ⊆ Gᶜ ∪ E1 ∪ E2 ∪ E3 := by
    intro ω hω
    by_contra hc'
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hc'
    obtain ⟨⟨⟨hGω, hE1⟩, hE2⟩, hE3⟩ := hc'
    apply hω
    simp only [E1, E2, E3, G, Set.mem_ofPred_eq, not_le] at hE1 hE2 hE3 hGω
    have hdom := info_iterConv_le ha hb ω hGω.1 hGω.2 q
    have hsum : ∑ i ∈ Finset.range q, info b (ω (i + 1)) =
        q * ((q : ℝ)⁻¹ * ∑ i ∈ Finset.range q, info b (ω (i + 1))) := by
      field_simp
    have hav := abs_lt.mp hE1
    have hia := info_nonneg ha (ω 0)
    simp only [Asum, hD] at hdom hE3
    rw [hsum] at hdom hE3
    constructor
    · nlinarith [mul_lt_mul_of_pos_left hav.1 hqpos]
    · nlinarith [mul_lt_mul_of_pos_left hav.2 hqpos]
  calc P {ω | ¬ ((q : ℝ) * (entropy b - θ - θ') ≤ info c (W ω) ∧
        info c (W ω) ≤ q * (entropy b + 2 * θ))}
      ≤ P (Gᶜ ∪ E1 ∪ E2 ∪ E3) := measure_mono hsub
    _ ≤ P Gᶜ + P E1 + P E2 + P E3 := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ 0 + ENNReal.ofReal (ε' / 2) + ENNReal.ofReal (ε' / 2) +
          ENNReal.ofReal ((entropy a + q * entropy b - entropy c) / (q * θ')) := by
        gcongr
        · exact hG.le
        · exact (hQ1 q hq1).le
        · refine (meas_ge_le_of_integral (Eventually.of_forall fun ω => info_nonneg ha (ω 0))
            (integrable_info_zero (b := b) ha hHa).1 (by positivity)).trans ?_
          rw [(integrable_info_zero (b := b) ha hHa).2]
          apply ENNReal.ofReal_le_ofReal
          rw [div_le_iff₀ (by positivity)]
          have : 2 * entropy a / (θ * ε') ≤ q := by linarith
          rw [div_le_iff₀ (by positivity)] at this
          nlinarith
        · refine (meas_ge_le_of_integral hD0 hDi (by positivity)).trans ?_
          rw [hDint]
    _ ≤ ENNReal.ofReal (ε' + (entropy a + q * entropy b - entropy c) / (q * θ')) := by
        have hΔ0 : 0 ≤ (entropy a + q * entropy b - entropy c) / (q * θ') := by
          rw [← hDint]
          exact div_nonneg (integral_nonneg_of_ae hD0) (by positivity)
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) hΔ0]
        ring_nf
        rfl

end Main

/-! ### Assembly -/

lemma iterConv_convPow {μ : Γ → ℝ} (hμ : IsProbability μ) (r k q : ℕ) :
    iterConv (convPow μ r) (convPow μ k) q = convPow μ (r + q * k) := by
  induction q with
  | zero => simp [iterConv]
  | succ q ih =>
    show conv (iterConv (convPow μ r) (convPow μ k) q) (convPow μ k) = _
    rw [ih, ← convPow_add hμ]
    congr 1; ring

lemma entropy_convPow_ge {μ : Γ → ℝ} (hμ : IsProbability μ)
    (hH : HasFiniteEntropy μ) (k : ℕ) :
    (k : ℝ) * asymptoticEntropy μ ≤ entropy (convPow μ k) := by
  obtain ⟨hfin, hT⟩ := hasFiniteEntropy_convPow_and_tendsto_entropy_convPow_div μ hμ hH
  have hsk : ∀ k, IsProbability (convPow μ k) := isProb_convPow hμ
  have hent : ∀ k, entE (convPow μ k) ≠ ⊤ := fun k => by
    have h := (hfin k)
    unfold entE
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun g => Real.negMulLog_nonneg ((hsk k).1 g) (le_one_of_isProb (hsk k) g)) h]
    exact ENNReal.ofReal_ne_top
  have hsub : Subadditive fun n => entropy (convPow μ n) := by
    intro a b
    simp only
    rw [entropy_eq_toReal (hsk _), entropy_eq_toReal (hsk _),
      entropy_eq_toReal (hsk _), convPow_add hμ,
      ← ENNReal.toReal_add (hent a) (hent b)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hent a, hent b⟩)
      (entE_conv_le (hsk a) (hsk b))
  have hbdd : BddBelow (Set.range fun n : ℕ => entropy (convPow μ n) / n) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    simp only
    rw [entropy_eq_toReal (hsk _)]
    positivity
  have hlim : asymptoticEntropy μ = hsub.lim := tendsto_nhds_unique hT (hsub.tendsto_lim hbdd)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [entropy_convPow_zero]
  · have h := hsub.lim_le_div hbdd (Nat.pos_iff_ne_zero.mp hk)
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    rw [le_div_iff₀ hk'] at h
    rw [hlim]; linarith

end P5SMB

open P5SMB EntropyDev B7Dev P5Dev in
/-- C3: typical sets for `μ^{(n)}`. -/
theorem P5SMB.exists_typical {Γ : Type*} [Group Γ] [Countable Γ]
    (μ : Γ → ℝ) (hμ : IsProbability μ) (hH : HasFiniteEntropy μ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n > N, ∃ V : Finset Γ, 1 - ε ≤ mass (convPow μ n) (V : Set Γ) ∧
      ∀ x ∈ V, Real.exp (-(n * (asymptoticEntropy μ + ε))) ≤ convPow μ n x ∧
        convPow μ n x ≤ Real.exp (-(n * (asymptoticEntropy μ - ε))) := by
  intro ε hε
  letI : MeasurableSpace Γ := ⊤
  have : DiscreteMeasurableSpace Γ := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  obtain ⟨hfin, hT⟩ := hasFiniteEntropy_convPow_and_tendsto_entropy_convPow_div μ hμ hH
  set h := asymptoticEntropy μ with hhdef
  have h0 : 0 ≤ h := asymptoticEntropy_nonneg hμ hH
  have hsk := isProb_convPow hμ
  set η₀ := min (ε ^ 2 / 12) (ε / 2) with hη₀
  have hη₀pos : 0 < η₀ := lt_min (by positivity) (by positivity)
  have hη₁ : η₀ ≤ ε ^ 2 / 12 := min_le_left _ _
  have hη₂ : η₀ ≤ ε / 2 := min_le_right _ _
  -- the block length
  obtain ⟨k, hk1, hkη⟩ : ∃ k : ℕ, 1 ≤ k ∧ entropy (convPow μ k) / k < h + η₀ := by
    have := (hT.eventually (gt_mem_nhds (by linarith : h < h + η₀))).and (eventually_ge_atTop 1)
    obtain ⟨k, hk, hk1⟩ := this.exists
    exact ⟨k, hk1, hk⟩
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hHk : entropy (convPow μ k) ≤ k * (h + η₀) := by
    rw [div_lt_iff₀ hkpos] at hkη; linarith
  have hHk' : k * h ≤ entropy (convPow μ k) := entropy_convPow_ge hμ hH k
  set θ : ℝ := k * ε / 8 with hθ
  set θ' : ℝ := k * ε / 4 with hθ'
  have hblk : ∀ r i, IsProbabilityMeasure (blockLaw (convPow μ r) (convPow μ k) i) :=
    fun r => isProbabilityMeasure_blockLaw (hsk r) (hsk k)
  -- the estimate for each remainder `r`
  have hQ : ∀ r : ℕ, ∃ Q : ℕ, ∀ q ≥ Q,
      (Measure.infinitePi (blockLaw (convPow μ r) (convPow μ k)))
        {ω | ¬ ((q : ℝ) * (entropy (convPow μ k) - θ - θ') ≤
          info (convPow μ (r + q * k)) (prodUpTo ω q) ∧
          info (convPow μ (r + q * k)) (prodUpTo ω q) ≤ q * (entropy (convPow μ k) + 2 * θ))} ≤
      ENNReal.ofReal (ε / 3 + (entropy (convPow μ r) + q * entropy (convPow μ k) -
        entropy (convPow μ (r + q * k))) / (q * θ')) := by
    intro r
    haveI := hblk r
    obtain ⟨Q, hQ⟩ := main_estimate (hsk r) (hsk k) (hfin r) (hfin k)
      (fun q => by rw [iterConv_convPow hμ]; exact hfin _) (θ := θ) (θ' := θ') (ε' := ε / 3)
      (by positivity) (by positivity) (by positivity)
    refine ⟨Q, fun q hq => ?_⟩
    have := hQ q hq
    simp only [iterConv_convPow hμ] at this
    exact this
  choose Q hQ using hQ
  set Hmax := ∑ r ∈ Finset.range k, entropy (convPow μ r) with hHmax
  have hHr : ∀ r < k, entropy (convPow μ r) ≤ Hmax := fun r hr =>
    Finset.single_le_sum (f := fun r => entropy (convPow μ r))
      (fun i _ => by rw [entropy_eq_toReal (hsk i)]; positivity) (Finset.mem_range.mpr hr)
  have hHr0 : ∀ r, 0 ≤ entropy (convPow μ r) := fun r => by
    rw [entropy_eq_toReal (hsk r)]; positivity
  set S0 : ℕ := (Finset.range k).sup Q with hS0
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (S0 : ℝ) + 2 * h / ε + 3 * Hmax / (θ' * ε) + 1
      ≤ M := exists_nat_ge _
  refine ⟨k * M + k, fun n hn => ?_⟩
  set r := n % k with hrdef
  set q := n / k with hqdef
  have hnrq : n = r + q * k := (Nat.mod_add_div' n k).symm
  have hr : r < k := Nat.mod_lt n (by omega)
  have hqM : M + 1 ≤ q := by
    rw [hqdef, Nat.le_div_iff_mul_le (by omega)]
    have : (M + 1) * k = k * M + k := by ring
    omega
  have hqR : (M : ℝ) + 1 ≤ q := by exact_mod_cast hqM
  have hqpos : (0 : ℝ) < q := by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hQr : Q r ≤ q := by
    have h1 : Q r ≤ S0 := Finset.le_sup (Finset.mem_range.mpr hr)
    have h2 : (S0 : ℝ) ≤ M := by
      have : 0 ≤ 2 * h / ε + 3 * Hmax / (θ' * ε) := by
        have : 0 ≤ Hmax := Finset.sum_nonneg fun i _ => hHr0 i
        positivity
      linarith
    have h3 : S0 ≤ M := by exact_mod_cast h2
    omega
  have hq2h : 2 * h / ε ≤ q := by
    have : 0 ≤ (S0 : ℝ) + 3 * Hmax / (θ' * ε) := by
      have : 0 ≤ Hmax := Finset.sum_nonneg fun i _ => hHr0 i
      positivity
    linarith
  have hqH : 3 * Hmax / (θ' * ε) ≤ q := by
    have : 0 ≤ (S0 : ℝ) + 2 * h / ε := by positivity
    linarith
  haveI := hblk r
  set P := Measure.infinitePi (blockLaw (convPow μ r) (convPow μ k)) with hPdef
  set ν := convPow μ n with hνdef
  have hν := hsk n
  set W := fun ω : ℕ → Γ => prodUpTo ω q with hWdef
  have hlaw : P.map W = stepMeasure ν := by
    rw [hνdef, hnrq, ← iterConv_convPow hμ]
    exact map_prodUpTo (hsk r) (hsk k) q
  -- the typical set
  set c := Real.exp (-(n * (h + ε))) with hc
  have hcpos : 0 < c := Real.exp_pos _
  set Vs := {x : Γ | c ≤ ν x ∧ ν x ≤ Real.exp (-(n * (h - ε)))} with hVs
  have hVfin : Vs.Finite := by
    have h1 := hν.2.summable.tendsto_cofinite_zero.eventually (gt_mem_nhds hcpos)
    rw [Filter.eventually_cofinite] at h1
    exact h1.subset fun x hx => by simp only [Set.mem_ofPred_eq, not_lt]; exact hx.1
  refine ⟨hVfin.toFinset, ?_, fun x hx => by
    rw [Set.Finite.mem_toFinset] at hx; exact hx⟩
  rw [Set.Finite.coe_toFinset]
  -- the bad event has probability at most ε
  have hbad : P (W ⁻¹' Vsᶜ) ≤ ENNReal.ofReal ε := by
    set B := {ω : ℕ → Γ | ¬ ((q : ℝ) * (entropy (convPow μ k) - θ - θ') ≤
          info (convPow μ (r + q * k)) (prodUpTo ω q) ∧
          info (convPow μ (r + q * k)) (prodUpTo ω q) ≤ q * (entropy (convPow μ k) + 2 * θ))}
    set G := {ω : ℕ → Γ | 0 < convPow μ r (ω 0) ∧ ∀ i, 0 < convPow μ k (ω (i + 1))}
    have hG : P Gᶜ = 0 := by
      have := (ae_pos_zero (a := convPow μ r) (b := convPow μ k)).and
        (ae_pos_succ (a := convPow μ r) (b := convPow μ k))
      exact measure_eq_zero_iff_ae_notMem.mpr (this.mono fun ω hω => by simpa [G] using hω)
    have hsub : W ⁻¹' Vsᶜ ⊆ B ∪ Gᶜ := by
      intro ω hω
      by_contra hc'
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hc'
      obtain ⟨hB, hGω⟩ := hc'
      simp only [B, Set.mem_ofPred_eq, not_not] at hB
      simp only [G, Set.mem_ofPred_eq] at hGω
      apply hω
      have hpos : 0 < ν (W ω) := by
        have := iterConv_pos (hsk r) (hsk k) ω hGω.1 hGω.2 q
        rw [iterConv_convPow hμ, ← hnrq] at this
        exact this
      rw [← hnrq] at hB
      have hexp : ν (W ω) = Real.exp (-info ν (W ω)) := by
        unfold info; rw [neg_neg, Real.exp_log hpos]
      have hnR : (n : ℝ) = r + q * k := by exact_mod_cast hnrq
      have hrR : (r : ℝ) < k := by exact_mod_cast hr
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not, hVs]
      rw [hexp]
      constructor
      · apply Real.exp_le_exp.mpr
        -- info ≤ q (H_k + 2θ) ≤ n (h + ε)
        have h1 := hB.2
        have h2 : (q : ℝ) * (entropy (convPow μ k) + 2 * θ) ≤ q * k * (h + η₀ + ε / 4) := by
          have := mul_le_mul_of_nonneg_left hHk hqpos.le
          have e1 : (q : ℝ) * (entropy (convPow μ k) + 2 * θ) =
              q * entropy (convPow μ k) + q * k * ε / 4 := by rw [hθ]; ring
          have e2 : (q : ℝ) * k * (h + η₀ + ε / 4) = q * (k * (h + η₀)) + q * k * ε / 4 := by ring
          rw [e1, e2]; linarith
        have h3 : (q : ℝ) * k * (h + η₀ + ε / 4) ≤ n * (h + ε) := by
          rw [hnR]
          have m1 : (0 : ℝ) ≤ r * (h + ε) := mul_nonneg hr0 (by linarith)
          have m2 : (0 : ℝ) ≤ q * k * (3 * ε / 4 - η₀) :=
            mul_nonneg (by positivity) (by linarith)
          have e : ((r : ℝ) + q * k) * (h + ε) - q * k * (h + η₀ + ε / 4) =
              r * (h + ε) + q * k * (3 * ε / 4 - η₀) := by ring
          linarith
        linarith
      · apply Real.exp_le_exp.mpr
        -- info ≥ q (H_k − θ − θ') ≥ n (h − ε)
        have h1 := hB.1
        have h2 : (q : ℝ) * k * (h - 3 * ε / 8) ≤ (q : ℝ) * (entropy (convPow μ k) - θ - θ') := by
          have := mul_le_mul_of_nonneg_left hHk' hqpos.le
          have e1 : (q : ℝ) * (entropy (convPow μ k) - θ - θ') =
              q * entropy (convPow μ k) - q * k * (3 * ε / 8) := by rw [hθ, hθ']; ring
          have e2 : (q : ℝ) * k * (h - 3 * ε / 8) = q * (k * h) - q * k * (3 * ε / 8) := by ring
          rw [e1, e2]; linarith
        have h3 : (n : ℝ) * (h - ε) ≤ q * k * (h - 3 * ε / 8) := by
          rw [hnR]
          have hq' : 2 * h ≤ q * ε := by rwa [div_le_iff₀ hε] at hq2h
          have m0 : (r : ℝ) * h ≤ k * h := mul_le_mul_of_nonneg_right hrR.le h0
          have m1 : (k : ℝ) * (2 * h) ≤ k * (q * ε) := mul_le_mul_of_nonneg_left hq' hkpos.le
          have m2 : (0 : ℝ) ≤ r * ε := mul_nonneg hr0 hε.le
          have m3 : (0 : ℝ) ≤ k * h := mul_nonneg hkpos.le h0
          have e : ((r : ℝ) + q * k) * (h - ε) - q * k * (h - 3 * ε / 8) =
              r * h - r * ε - 5 / 8 * (k * (q * ε)) := by ring
          linarith
        linarith
    calc P (W ⁻¹' Vsᶜ) ≤ P (B ∪ Gᶜ) := measure_mono hsub
      _ ≤ P B + P Gᶜ := measure_union_le _ _
      _ = P B := by rw [hG, add_zero]
      _ ≤ ENNReal.ofReal (ε / 3 + (entropy (convPow μ r) + q * entropy (convPow μ k) -
            entropy (convPow μ (r + q * k))) / (q * θ')) := hQ r q hQr
      _ ≤ ENNReal.ofReal ε := by
          apply ENNReal.ofReal_le_ofReal
          rw [← hnrq]
          have hnh : (q : ℝ) * k * h ≤ entropy ν := by
            have := entropy_convPow_ge hμ hH n
            have hnR : (n : ℝ) = r + q * k := by exact_mod_cast hnrq
            have : (q : ℝ) * k * h ≤ n * h := by
              rw [hnR]
              have m : (0 : ℝ) ≤ r * h := mul_nonneg (Nat.cast_nonneg r) h0
              have e : ((r : ℝ) + q * k) * h = r * h + q * k * h := by ring
              linarith
            linarith
          have hΔ : entropy (convPow μ r) + q * entropy (convPow μ k) - entropy ν ≤
              Hmax + q * k * η₀ := by
            have := mul_le_mul_of_nonneg_left hHk hqpos.le
            have e : (q : ℝ) * (k * (h + η₀)) = q * k * h + q * k * η₀ := by ring
            have := hHr r hr
            linarith
          have hqθ : 0 < (q : ℝ) * θ' := by positivity
          have h4 : (entropy (convPow μ r) + q * entropy (convPow μ k) - entropy ν) / (q * θ') ≤
              (Hmax + q * k * η₀) / (q * θ') := div_le_div_of_nonneg_right hΔ hqθ.le
          have h5 : (Hmax + q * k * η₀) / (q * θ') = Hmax / (q * θ') + 4 * η₀ / ε := by
            simp only [hθ']; field_simp
          have h6 : Hmax / (q * θ') ≤ ε / 3 := by
            rw [div_le_iff₀ hqθ]
            have : 3 * Hmax / (θ' * ε) ≤ q := hqH
            rw [div_le_iff₀ (by positivity)] at this
            have e : ε / 3 * (q * θ') = q * (θ' * ε) / 3 := by ring
            rw [e]; linarith
          have h7 : 4 * η₀ / ε ≤ ε / 3 := by
            rw [div_le_iff₀ hε]
            have e : ε / 3 * ε = ε ^ 2 / 3 := by ring
            rw [e]; linarith
          linarith
  -- convert to the mass
  have hmeasV : MeasurableSet Vs := DiscreteMeasurableSpace.forall_measurableSet _
  have hWm : Measurable W := measurable_prodUpTo q
  have hPV : P (W ⁻¹' Vs) = ENNReal.ofReal (mass ν Vs) := by
    rw [← Measure.map_apply hWm hmeasV, hlaw, stepMeasure_apply]
    unfold mass
    rw [ENNReal.ofReal_tsum_of_nonneg (fun x => Set.indicator_nonneg (fun y _ => hν.1 y) x)
      (hν.2.summable.indicator _)]
    congr 1; ext x
    by_cases hx : x ∈ Vs <;> simp [Set.indicator, hx] <;> rfl
  have hsum : P (W ⁻¹' Vs) + P (W ⁻¹' Vsᶜ) = 1 := by
    rw [Set.preimage_compl, measure_add_measure_compl (hWm hmeasV), measure_univ]
  have hmass0 : 0 ≤ mass ν Vs := tsum_nonneg fun x => Set.indicator_nonneg (fun y _ => hν.1 y) x
  have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (mass ν Vs + ε) := by
    rw [ENNReal.ofReal_add hmass0 hε.le, ← hPV, ← hsum]
    gcongr
  rw [ENNReal.one_le_ofReal] at this
  linarith

end ErschlerZheng

namespace KaimanovichVershik

end KaimanovichVershik
end

section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open KaimanovichVershik
open ErschlerZheng in
theorem solution {Γ : Type*} [Group Γ] [Countable Γ]
    (μ : Γ → ℝ) (hμ : IsProbability μ) (hH : HasFiniteEntropy μ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n > N, ∃ V : Finset Γ, 1 - ε ≤ mass (convPow μ n) (V : Set Γ) ∧
      ∀ x ∈ V, Real.exp (-(n * (asymptoticEntropy μ + ε))) ≤ convPow μ n x ∧
        convPow μ n x ≤ Real.exp (-(n * (asymptoticEntropy μ - ε))) :=
  P5SMB.exists_typical μ hμ hH
end
