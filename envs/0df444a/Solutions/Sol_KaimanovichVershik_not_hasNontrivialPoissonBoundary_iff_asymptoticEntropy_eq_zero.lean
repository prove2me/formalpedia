-- Prove2me | solution 1 for KaimanovichVershik.not_hasNontrivialPoissonBoundary_iff_asymptoticEntropy_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-05T22:33:27.163991+00:00
-- url     : https://prove2.me/submissions/334c6ed5-310e-4c46-9b87-0633adfeb1b4

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

lemma entE_ne_top {μ : Γ → ℝ} (hμ : IsProbability μ) (hH : HasFiniteEntropy μ) : entE μ ≠ ⊤ := by
  unfold entE
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun g => Real.negMulLog_nonneg (hμ.1 g) (le_one_of_isProb hμ g)) hH]
  exact ENNReal.ofReal_ne_top

end EntropyDev

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

open scoped Classical in
lemma delta_conv (a : Γ → ℝ) : conv (fun g => if g = 1 then 1 else 0) a = a := by
  ext g
  unfold conv
  rw [tsum_eq_single 1]
  · simp
  · intro h hh
    simp [hh]

lemma convPow_one (μ : Γ → ℝ) : convPow μ 1 = μ := by
  classical
  show conv (convPow μ 0) μ = μ
  have : convPow μ 0 = fun g => if g = 1 then (1 : ℝ) else 0 := by
    ext g; simp only [convPow]
  rw [this, delta_conv]

lemma convPow_succ' {μ : Γ → ℝ} (hμ : IsProbability μ) (n : ℕ) :
    convPow μ (n + 1) = conv μ (convPow μ n) := by
  rw [add_comm, convPow_add hμ 1 n, convPow_one]

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

/-- Summability of `(z, h) ↦ a(h) b(h⁻¹ z)` on `Γ × Γ`. -/
lemma summable_conv_kernel {a b : Γ → ℝ} (ha : IsProbability a) (hb : IsProbability b) :
    Summable fun p : Γ × Γ => a p.2 * b (p.2⁻¹ * p.1) := by
  have hs : Summable fun p : Γ × Γ => a p.1 * b p.2 :=
    Summable.mul_of_nonneg ha.2.summable hb.2.summable ha.1 hb.1
  let e : Γ × Γ ≃ Γ × Γ :=
    { toFun := fun p => (p.2, p.2⁻¹ * p.1)
      invFun := fun p => (p.1 * p.2, p.1)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  exact (e.summable_iff (f := fun p : Γ × Γ => a p.1 * b p.2)).mpr hs

/-- A bounded harmonic function is harmonic for every convolution power. -/
lemma harmonic_convPow {μ : Γ → ℝ} (hμ : IsProbability μ) {f : Γ → ℝ} {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (hf : IsHarmonic μ f) (n : ℕ) (x : Γ) :
    f x = ∑' z, f (x * z) * convPow μ n z := by
  induction n generalizing x with
  | zero =>
    classical
    have : convPow μ 0 = fun g => if g = 1 then (1 : ℝ) else 0 := by
      ext g; simp only [convPow]
    rw [this, tsum_eq_single 1]
    · simp
    · intro b hb
      simp [hb]
  | succ n ih =>
    have hν := isProb_convPow hμ n
    set ν := convPow μ n with hνdef
    show f x = ∑' z, f (x * z) * conv ν μ z
    set F : Γ → Γ → ℝ := fun z h => f (x * z) * (ν h * μ (h⁻¹ * z)) with hF
    have hsum : Summable (Function.uncurry F) := by
      refine Summable.of_norm_bounded ((summable_conv_kernel hν hμ).mul_left C) ?_
      rintro ⟨z, h⟩
      simp only [Function.uncurry_apply_pair, hF, Real.norm_eq_abs, abs_mul]
      have h0 : 0 ≤ ν h * μ (h⁻¹ * z) := mul_nonneg (hν.1 h) (hμ.1 _)
      rw [abs_of_nonneg (hν.1 h), abs_of_nonneg (hμ.1 _)]
      exact mul_le_mul_of_nonneg_right (hC _) h0
    have e1 : ∀ z, f (x * z) * conv ν μ z = ∑' h, F z h := by
      intro z
      simp only [hF, conv]
      rw [tsum_mul_left]
    simp_rw [e1]
    rw [← hsum.tsum_comm]
    have e2 : ∀ h, ∑' z, F z h = f (x * h) * ν h := by
      intro h
      rw [← (Equiv.mulLeft h).tsum_eq]
      simp only [hF, Equiv.coe_mulLeft, inv_mul_cancel_left]
      have : ∀ w, f (x * (h * w)) * (ν h * μ w) = ν h * (f (x * h * w) * μ w) := by
        intro w; rw [mul_assoc x h w]; ring
      simp_rw [this]
      rw [tsum_mul_left, ← hf (x * h)]
      ring
    simp_rw [e2]
    exact ih x


/-! ### The Kullback–Leibler summand and a Pinsker-type bound -/

/-- The Kullback–Leibler summand `ψ(p, q) = p log p − p log q − p + q`. -/
noncomputable def psi (p q : ℝ) : ℝ := p * Real.log p - p * Real.log q - p + q

lemma sq_sqrt_sub_le_psi {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    (Real.sqrt p - Real.sqrt q) ^ 2 ≤ psi p q := by
  rcases hp.lt_or_eq with hp | hp
  · have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
    have ht : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
    have hs2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp.le
    have ht2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
    have hlp : Real.log p = 2 * Real.log (Real.sqrt p) := by
      conv_lhs => rw [← hs2]
      rw [Real.log_pow]; push_cast; ring
    have hlq : Real.log q = 2 * Real.log (Real.sqrt q) := by
      conv_lhs => rw [← ht2]
      rw [Real.log_pow]; push_cast; ring
    set s := Real.sqrt p
    set t := Real.sqrt q
    have key : Real.log (t / s) ≤ t / s - 1 := Real.log_le_sub_one_of_pos (div_pos ht hs)
    rw [Real.log_div ht.ne' hs.ne'] at key
    have key2 : s * (Real.log t - Real.log s) ≤ t - s := by
      have := mul_le_mul_of_nonneg_left key hs.le
      have e : s * (t / s - 1) = t - s := by field_simp
      linarith
    have key3 : s ^ 2 * (Real.log t - Real.log s) ≤ s * t - s ^ 2 := by
      have := mul_le_mul_of_nonneg_left key2 hs.le
      nlinarith [this]
    unfold psi
    rw [hlp, hlq]
    nlinarith [key3, hs2, ht2]
  · subst hp
    unfold psi
    simp [Real.sq_sqrt hq.le]

lemma psi_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : q = 0 → p = 0) : 0 ≤ psi p q := by
  rcases hq.lt_or_eq with hq | hq
  · exact (sq_nonneg _).trans (sq_sqrt_sub_le_psi hp hq)
  · rw [← hq, hpq hq.symm]; simp [psi]

/-- Pinsker-type bound, pointwise: `|p − q| ⩽ ψ(p, q)/(2ε) + ε(p + q)`. -/
lemma abs_sub_le_psi {p q ε : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : q = 0 → p = 0)
    (hε : 0 < ε) : |p - q| ≤ psi p q / (2 * ε) + ε * (p + q) := by
  rcases hq.lt_or_eq with hq | hq
  · have h1 := sq_sqrt_sub_le_psi hp hq
    have hs2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp
    have ht2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
    have hs0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
    have ht0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
    set s := Real.sqrt p
    set t := Real.sqrt q
    have e : |p - q| = |s - t| * (s + t) := by
      rw [← hs2, ← ht2, show s ^ 2 - t ^ 2 = (s - t) * (s + t) by ring, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ s + t)]
    rw [e]
    have ha2 : |s - t| ^ 2 = (s - t) ^ 2 := sq_abs _
    have ha0 : 0 ≤ |s - t| := abs_nonneg _
    have h2 : (s + t) ^ 2 ≤ 2 * (p + q) := by nlinarith [sq_nonneg (s - t)]
    have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg ε)
    rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|s - t| - ε * (s + t))]
  · rw [← hq, hpq hq.symm]; simp [psi]

/-! ### The Jensen gap of the entropy at one step -/

lemma summable_mul_negMulLog {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν)
    (z : Γ) : Summable fun g => μ g * Real.negMulLog (ν (g⁻¹ * z)) := by
  refine Summable.of_nonneg_of_le (fun g => mul_nonneg (hμ.1 g)
    (Real.negMulLog_nonneg (hν.1 _) (le_one_of_isProb hν _))) (fun g => ?_) hμ.2.summable
  have h1 := Real.negMulLog_le_one_sub_self (hν.1 (g⁻¹ * z))
  have h2 := hν.1 (g⁻¹ * z)
  have h3 := Real.negMulLog_nonneg (hν.1 (g⁻¹ * z)) (le_one_of_isProb hν _)
  nlinarith [hμ.1 g]

/-- For each `z`: `Σ_g μ(g) ψ(p_g(z), q_z) = φ(q_z) − Σ_g μ(g) φ(p_g(z))`. -/
lemma hasSum_gap {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) (z : Γ) :
    HasSum (fun g => μ g * psi (ν (g⁻¹ * z)) (conv μ ν z))
      (Real.negMulLog (conv μ ν z) - ∑' g, μ g * Real.negMulLog (ν (g⁻¹ * z))) := by
  have hs1 := summable_mul_negMulLog hμ hν z
  have hs2 : HasSum (fun g => μ g * ν (g⁻¹ * z)) (conv μ ν z) :=
    (conv_summand_summable hμ hν z).hasSum
  have h := ((hs1.hasSum.neg.sub (hs2.mul_right (Real.log (conv μ ν z)))).sub hs2).add
    (hμ.2.mul_left (conv μ ν z))
  convert h using 1
  all_goals first
    | rfl
    | (ext g; unfold psi Real.negMulLog; ring)
    | (unfold Real.negMulLog; ring)

lemma eq_zero_of_conv_eq_zero {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν)
    {z g : Γ} (hg : 0 < μ g) (h0 : conv μ ν z = 0) : ν (g⁻¹ * z) = 0 := by
    have hle : μ g * ν (g⁻¹ * z) ≤ conv μ ν z :=
      (conv_summand_summable hμ hν z).le_tsum g (fun j _ => mul_nonneg (hμ.1 j) (hν.1 _))
    rw [h0] at hle
    have := hν.1 (g⁻¹ * z)
    have h3 : μ g * ν (g⁻¹ * z) = 0 := le_antisymm hle (mul_nonneg hg.le this)
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hg.ne'
    · exact h

lemma gap_term_nonneg {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) (z g : Γ) :
    0 ≤ μ g * psi (ν (g⁻¹ * z)) (conv μ ν z) := by
  rcases (hμ.1 g).lt_or_eq with hg | hg
  · exact mul_nonneg hg.le (psi_nonneg (hν.1 _) (conv_nonneg hμ hν z)
      (eq_zero_of_conv_eq_zero hμ hν hg))
  · rw [← hg, zero_mul]

lemma hasSum_inner_entropy {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν)
    (hHν : HasFiniteEntropy ν) :
    HasSum (fun z => ∑' g, μ g * Real.negMulLog (ν (g⁻¹ * z))) (entropy ν) := by
  have ha0 : ∀ z, 0 ≤ ∑' g, μ g * Real.negMulLog (ν (g⁻¹ * z)) := fun z =>
    tsum_nonneg fun g => mul_nonneg (hμ.1 g)
      (Real.negMulLog_nonneg (hν.1 _) (le_one_of_isProb hν _))
  have key : ∑' z, ENNReal.ofReal (∑' g, μ g * Real.negMulLog (ν (g⁻¹ * z))) = entE ν := by
    have e1 : ∀ z, ENNReal.ofReal (∑' g, μ g * Real.negMulLog (ν (g⁻¹ * z))) =
        ∑' g, ENNReal.ofReal (μ g) * ENNReal.ofReal (Real.negMulLog (ν (g⁻¹ * z))) := by
      intro z
      rw [ENNReal.ofReal_tsum_of_nonneg (fun g => mul_nonneg (hμ.1 g)
        (Real.negMulLog_nonneg (hν.1 _) (le_one_of_isProb hν _)))
        (summable_mul_negMulLog hμ hν z)]
      congr 1; ext g
      rw [ENNReal.ofReal_mul (hμ.1 g)]
    simp_rw [e1]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    have e2 : ∀ g : Γ, ∑' z, ENNReal.ofReal (Real.negMulLog (ν (g⁻¹ * z))) = entE ν := by
      intro g
      rw [tsum_mulLeft_eq (fun x => ENNReal.ofReal (Real.negMulLog (ν x))) g⁻¹]
      rfl
    simp_rw [e2]
    rw [ENNReal.tsum_mul_right, tsum_ofReal_of_isProb hμ, one_mul]
  have hne : ∑' z, ENNReal.ofReal (∑' g, μ g * Real.negMulLog (ν (g⁻¹ * z))) ≠ ⊤ := by
    rw [key]; exact entE_ne_top hν hHν
  have h := ENNReal.hasSum_toReal hne
  simp only [ENNReal.toReal_ofReal (ha0 _)] at h
  convert h using 1
  rw [entropy_eq_toReal hν, ← key, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (ha0 _)]

/-- `Σ_z J_z = H(μ^{(n+1)}) − H(μ^{(n)})`. -/
lemma hasSum_gap_total {μ : Γ → ℝ} (hμ : IsProbability μ)
    (hfin : ∀ n, HasFiniteEntropy (convPow μ n)) (n : ℕ) :
    HasSum (fun z => Real.negMulLog (conv μ (convPow μ n) z) -
        ∑' g, μ g * Real.negMulLog (convPow μ n (g⁻¹ * z)))
      (entropy (convPow μ (n + 1)) - entropy (convPow μ n)) := by
  have h1 : HasSum (fun z => Real.negMulLog (conv μ (convPow μ n) z))
      (entropy (convPow μ (n + 1))) := by
    have := (hfin (n + 1)).hasSum
    rw [convPow_succ' hμ n] at this ⊢
    exact this
  exact h1.sub (hasSum_inner_entropy hμ (isProb_convPow hμ n) (hfin n))


/-! ### From the entropy increment to the total variation distance -/

/-- `‖δ_g ⋆ μ^{(n)} − μ^{(n+1)}‖₁ ⩽ Δ_n/(2εμ(g)) + 2ε`, `Δ_n = H(μ^{(n+1)}) − H(μ^{(n)})`. -/
lemma l1_le {μ : Γ → ℝ} (hμ : IsProbability μ) (hfin : ∀ n, HasFiniteEntropy (convPow μ n))
    (n : ℕ) {g₀ : Γ} (hg₀ : 0 < μ g₀) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun z => |convPow μ n (g₀⁻¹ * z) - conv μ (convPow μ n) z|) ∧
    ∑' z, |convPow μ n (g₀⁻¹ * z) - conv μ (convPow μ n) z| ≤
      (entropy (convPow μ (n + 1)) - entropy (convPow μ n)) / (2 * ε * μ g₀) + 2 * ε := by
  have hν := isProb_convPow hμ n
  have hJ := hasSum_gap_total hμ hfin n
  set ν := convPow μ n
  have hq := isProb_conv hμ hν
  have hp : HasSum (fun z => ν (g₀⁻¹ * z)) 1 := (Equiv.mulLeft g₀⁻¹).hasSum_iff.mpr hν.2
  have hpt : ∀ z, |ν (g₀⁻¹ * z) - conv μ ν z| ≤
      (Real.negMulLog (conv μ ν z) - ∑' g, μ g * Real.negMulLog (ν (g⁻¹ * z))) /
        (2 * ε * μ g₀) + ε * (ν (g₀⁻¹ * z) + conv μ ν z) := by
    intro z
    have h1 : μ g₀ * psi (ν (g₀⁻¹ * z)) (conv μ ν z) ≤
        Real.negMulLog (conv μ ν z) - ∑' g, μ g * Real.negMulLog (ν (g⁻¹ * z)) :=
      le_hasSum (hasSum_gap hμ hν z) g₀ (fun g _ => gap_term_nonneg hμ hν z g)
    have h2 := abs_sub_le_psi (hν.1 (g₀⁻¹ * z)) (conv_nonneg hμ hν z)
      (eq_zero_of_conv_eq_zero hμ hν hg₀) hε
    have h3 : psi (ν (g₀⁻¹ * z)) (conv μ ν z) / (2 * ε) ≤
        (Real.negMulLog (conv μ ν z) - ∑' g, μ g * Real.negMulLog (ν (g⁻¹ * z))) /
          (2 * ε * μ g₀) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hs : Summable fun z => |ν (g₀⁻¹ * z) - conv μ ν z| := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun z => ?_)
      (hp.summable.add hq.2.summable)
    have a := hν.1 (g₀⁻¹ * z)
    have b := conv_nonneg hμ hν z
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hR := (hJ.div_const (2 * ε * μ g₀)).add ((hp.add hq.2).mul_left ε)
  refine ⟨hs, ?_⟩
  have := hasSum_le hpt hs.hasSum hR
  linarith

lemma summable_bdd_mul {f : Γ → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) {a : Γ → ℝ}
    (ha0 : ∀ z, 0 ≤ a z) (ha : Summable a) (x : Γ) : Summable fun z => f (x * z) * a z := by
  refine Summable.of_norm_bounded (ha.mul_left C) fun z => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 z)]
  exact mul_le_mul_of_nonneg_right (hC _) (ha0 z)

/-- `|f(xg) − f(x)| ⩽ sup|f| · ‖δ_g ⋆ μ^{(n)} − μ^{(n+1)}‖₁` for bounded harmonic `f`. -/
lemma abs_harmonic_sub_le {μ : Γ → ℝ} (hμ : IsProbability μ) {f : Γ → ℝ} {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (hf : IsHarmonic μ f) (n : ℕ) (x g₀ : Γ)
    (hs : Summable fun z => |convPow μ n (g₀⁻¹ * z) - conv μ (convPow μ n) z|) :
    |f (x * g₀) - f x| ≤ C * ∑' z, |convPow μ n (g₀⁻¹ * z) - conv μ (convPow μ n) z| := by
  have hν := isProb_convPow hμ n
  have e1 : f (x * g₀) = ∑' z, f (x * z) * convPow μ n (g₀⁻¹ * z) := by
    rw [harmonic_convPow hμ hC hf n (x * g₀),
      ← (Equiv.mulLeft g₀).tsum_eq (fun z => f (x * z) * convPow μ n (g₀⁻¹ * z))]
    congr 1; ext w
    simp [mul_assoc]
  have e2 : f x = ∑' z, f (x * z) * conv μ (convPow μ n) z := by
    rw [harmonic_convPow hμ hC hf (n + 1) x, convPow_succ' hμ n]
  set ν := convPow μ n
  have hq := isProb_conv hμ hν
  have hp : HasSum (fun z => ν (g₀⁻¹ * z)) 1 := (Equiv.mulLeft g₀⁻¹).hasSum_iff.mpr hν.2
  have sp := summable_bdd_mul hC (fun z => hν.1 (g₀⁻¹ * z)) hp.summable x
  have sq := summable_bdd_mul hC (conv_nonneg hμ hν) hq.2.summable x
  rw [e1, e2, ← sp.tsum_sub sq]
  have hpt : ∀ z, |f (x * z) * ν (g₀⁻¹ * z) - f (x * z) * conv μ ν z| ≤
      C * |ν (g₀⁻¹ * z) - conv μ ν z| := by
    intro z
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_right (hC _) (abs_nonneg _)
  have sa : Summable fun z => |f (x * z) * ν (g₀⁻¹ * z) - f (x * z) * conv μ ν z| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hpt (hs.mul_left C)
  calc |∑' z, (f (x * z) * ν (g₀⁻¹ * z) - f (x * z) * conv μ ν z)|
      ≤ ∑' z, |f (x * z) * ν (g₀⁻¹ * z) - f (x * z) * conv μ ν z| := by
        have := norm_tsum_le_tsum_norm (f := fun z =>
          f (x * z) * ν (g₀⁻¹ * z) - f (x * z) * conv μ ν z) (by simpa [Real.norm_eq_abs] using sa)
        simpa [Real.norm_eq_abs] using this
    _ ≤ ∑' z, C * |ν (g₀⁻¹ * z) - conv μ ν z| := sa.tsum_le_tsum hpt (hs.mul_left C)
    _ = C * ∑' z, |ν (g₀⁻¹ * z) - conv μ ν z| := tsum_mul_left

/-! ### The theorem: `h_μ = 0` forces the Poisson boundary to be trivial -/

theorem not_hasNontrivialPoissonBoundary_of_asymptoticEntropy_eq_zero [Countable Γ]
    (μ : Γ → ℝ) (hμ : IsProbability μ) (hH : HasFiniteEntropy μ)
    (h0 : asymptoticEntropy μ = 0) : ¬ HasNontrivialPoissonBoundary μ := by
  obtain ⟨hfin, hT⟩ := hasFiniteEntropy_convPow_and_tendsto_entropy_convPow_div μ hμ hH
  rw [h0] at hT
  set Δ : ℕ → ℝ := fun k => entropy (convPow μ (k + 1)) - entropy (convPow μ k) with hΔ
  have hsumΔ : ∀ N, entropy (convPow μ N) = ∑ k ∈ Finset.range N, Δ k := by
    intro N
    rw [Finset.sum_range_sub (fun k => entropy (convPow μ k)), entropy_convPow_zero, sub_zero]
  have hinf : ∀ δ > 0, ∃ n, Δ n < δ := by
    intro δ hδ
    by_contra hc
    push Not at hc
    obtain ⟨N, hN, hN1⟩ :=
      ((hT.eventually (gt_mem_nhds hδ)).and (Filter.eventually_ge_atTop 1)).exists
    have hge : (N : ℝ) * δ ≤ entropy (convPow μ N) := by
      rw [hsumΔ N]
      calc (N : ℝ) * δ = ∑ k ∈ Finset.range N, δ := by simp
        _ ≤ ∑ k ∈ Finset.range N, Δ k := Finset.sum_le_sum fun k _ => hc k
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [div_lt_iff₀ hNpos] at hN
    linarith
  rintro ⟨f, ⟨C, hC⟩, hf, x, hx, y, hy, hxy⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 1)
  have hstep : ∀ x g, μ g ≠ 0 → f (x * g) = f x := by
    intro x g hg
    have hg0 : 0 < μ g := lt_of_le_of_ne (hμ.1 g) (Ne.symm hg)
    have key : ∀ ε > 0, |f (x * g) - f x| ≤ 3 * C * ε := by
      intro ε hε
      obtain ⟨n, hn⟩ := hinf (2 * ε ^ 2 * μ g) (by positivity)
      obtain ⟨hs, hle⟩ := l1_le hμ hfin n hg0 hε
      have h1 := abs_harmonic_sub_le hμ hC hf n x g hs
      have hΔ0 : Δ n / (2 * ε * μ g) ≤ ε := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      calc |f (x * g) - f x|
          ≤ C * ∑' z, |convPow μ n (g⁻¹ * z) - conv μ (convPow μ n) z| := h1
        _ ≤ C * (Δ n / (2 * ε * μ g) + 2 * ε) := mul_le_mul_of_nonneg_left hle hC0
        _ ≤ C * (ε + 2 * ε) := by gcongr
        _ = 3 * C * ε := by ring
    set d := |f (x * g) - f x| with hd
    have hd0 : d ≤ 0 := by
      by_contra hc
      push Not at hc
      have := key (d / (6 * C + 1)) (by positivity)
      rw [show 3 * C * (d / (6 * C + 1)) = 3 * C * d / (6 * C + 1) by ring,
        le_div_iff₀ (by positivity)] at this
      nlinarith
    have : f (x * g) - f x = 0 := abs_nonpos_iff.mp hd0
    linarith
  have hcl : ∀ m ∈ Submonoid.closure (Function.support μ), ∀ x, f (x * m) = f x := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem g hg => exact fun x => hstep x g hg
    | one => exact fun x => by rw [mul_one]
    | mul a b _ _ ha hb => exact fun x => by rw [← mul_assoc, hb, ha]
  apply hxy
  have e1 := hcl x hx 1
  have e2 := hcl y hy 1
  rw [one_mul] at e1 e2
  rw [e1, e2]

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

lemma isProb_transl {ν : Γ → ℝ} (hν : IsProbability ν) (g : Γ) :
    IsProbability fun z => ν (g⁻¹ * z) :=
  ⟨fun _ => hν.1 _, (Equiv.mulLeft g⁻¹).hasSum_iff.mpr hν.2⟩

lemma summable_abs_sub {a b : Γ → ℝ} (ha : IsProbability a) (hb : IsProbability b) :
    Summable (fun z => |a z - b z|) ∧ ∑' z, |a z - b z| ≤ 2 := by
  have hle : ∀ z, |a z - b z| ≤ a z + b z := fun z => by
    have := ha.1 z; have := hb.1 z
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hs := ha.2.summable.add hb.2.summable
  have hS : Summable (fun z => |a z - b z|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hle hs
  refine ⟨hS, ?_⟩
  calc ∑' z, |a z - b z| ≤ ∑' z, (a z + b z) := hS.tsum_le_tsum hle hs
    _ = 2 := by rw [ha.2.summable.tsum_add hb.2.summable, ha.2.tsum_eq, hb.2.tsum_eq]; norm_num

lemma abs_tsum_mul_le_one {φ : Γ → ℝ} (hφ : ∀ x, |φ x| ≤ 1) {ν : Γ → ℝ} (hν : IsProbability ν) :
    |∑' w, φ w * ν w| ≤ 1 := by
  have hpt : ∀ w, |φ w * ν w| ≤ ν w := fun w => by
    rw [abs_mul, abs_of_nonneg (hν.1 w)]
    simpa using mul_le_mul_of_nonneg_right (hφ w) (hν.1 w)
  have sa : Summable fun w => |φ w * ν w| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hpt hν.2.summable
  calc |∑' w, φ w * ν w| ≤ ∑' w, |φ w * ν w| := by
        have := norm_tsum_le_tsum_norm (f := fun w => φ w * ν w)
          (by simpa [Real.norm_eq_abs] using sa)
        simpa [Real.norm_eq_abs] using this
    _ ≤ ∑' w, ν w := sa.tsum_le_tsum hpt hν.2.summable
    _ = 1 := hν.2.tsum_eq

/-- Fubini for a bounded function against a convolution. -/
lemma tsum_mul_conv {a b : Γ → ℝ} (ha : IsProbability a) (hb : IsProbability b) {φ : Γ → ℝ}
    {C : ℝ} (hφ : ∀ x, |φ x| ≤ C) :
    ∑' v, φ v * conv a b v = ∑' h, a h * ∑' w, φ (h * w) * b w := by
  set F : Γ → Γ → ℝ := fun v h => φ v * (a h * b (h⁻¹ * v)) with hF
  have hsum : Summable (Function.uncurry F) := by
    refine Summable.of_norm_bounded ((summable_conv_kernel ha hb).mul_left C) ?_
    rintro ⟨v, h⟩
    simp only [Function.uncurry_apply_pair, hF, Real.norm_eq_abs, abs_mul]
    have h0 : 0 ≤ a h * b (h⁻¹ * v) := mul_nonneg (ha.1 h) (hb.1 _)
    rw [abs_of_nonneg (ha.1 h), abs_of_nonneg (hb.1 _)]
    exact mul_le_mul_of_nonneg_right (hφ _) h0
  have e1 : ∀ v, φ v * conv a b v = ∑' h, F v h := by
    intro v; simp only [hF, conv]; rw [tsum_mul_left]
  simp_rw [e1]
  rw [← hsum.tsum_comm]
  congr 1; ext h
  rw [← (Equiv.mulLeft h).tsum_eq]
  simp only [hF, Equiv.coe_mulLeft, inv_mul_cancel_left]
  rw [← tsum_mul_left]
  congr 1; ext w; ring

/-! ### Duality: a trivial boundary forces `‖δ_g ⋆ μ^{(n)} − μ^{(n)}‖₁ → 0` -/

theorem tendsto_tv_of_liouville {μ : Γ → ℝ} (hμ : IsProbability μ)
    (hL : ¬ HasNontrivialPoissonBoundary μ)
    (hap : Tendsto (fun n => ∑' z, |convPow μ (n + 1) z - convPow μ n z|) atTop (𝓝 0))
    {g : Γ} (hg : g ∈ Submonoid.closure (Function.support μ)) :
    Tendsto (fun n => ∑' z, |convPow μ n (g⁻¹ * z) - convPow μ n z|) atTop (𝓝 0) := by
  set a : ℕ → ℝ := fun n => ∑' z, |convPow μ n (g⁻¹ * z) - convPow μ n z| with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => tsum_nonneg fun _ => abs_nonneg _
  by_contra hne
  rw [Metric.tendsto_atTop] at hne
  push Not at hne
  obtain ⟨ε, hε, hfreq⟩ := hne
  have hfr : ∃ᶠ n in atTop, ε ≤ a n := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hn, h⟩ := hfreq N
    refine ⟨n, hn, ?_⟩
    simpa [Real.dist_eq, abs_of_nonneg (ha0 n)] using h
  have := Filter.frequently_iff_neBot.mp hfr
  set U : Ultrafilter ℕ := Ultrafilter.of (atTop ⊓ 𝓟 {n | ε ≤ a n})
  have hU : (U : Filter ℕ) ≤ atTop ⊓ 𝓟 {n | ε ≤ a n} := Ultrafilter.of_le _
  have hUat : (U : Filter ℕ) ≤ atTop := hU.trans inf_le_left
  have hUS : {n | ε ≤ a n} ∈ (U : Filter ℕ) := hU (mem_inf_of_right (mem_principal_self _))
  -- the sign functions and the test functions
  set s : ℕ → Γ → ℝ := fun n z =>
    if 0 ≤ convPow μ n (g⁻¹ * z) - convPow μ n z then 1 else -1 with hsdef
  have hs1 : ∀ n z, |s n z| ≤ 1 := by
    intro n z; simp only [hsdef]; split_ifs <;> simp
  have hsd : ∀ n z, s n z * (convPow μ n (g⁻¹ * z) - convPow μ n z) =
      |convPow μ n (g⁻¹ * z) - convPow μ n z| := by
    intro n z; simp only [hsdef]; split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · push Not at h; rw [abs_of_neg h]; ring
  set F : ℕ → Γ → ℝ := fun n x => ∑' w, s n (x * w) * convPow μ n w with hFdef
  have hF1 : ∀ n x, |F n x| ≤ 1 := fun n x =>
    abs_tsum_mul_le_one (fun w => hs1 n (x * w)) (isProb_convPow hμ n)
  have hlim : ∀ x, ∃ c ∈ Set.Icc (-1 : ℝ) 1, Tendsto (fun n => F n x) U (𝓝 c) := by
    intro x
    obtain ⟨c, hc, hle⟩ := isCompact_Icc.ultrafilter_le_nhds (U.map (fun n => F n x)) (by
      rw [Ultrafilter.coe_map, le_principal_iff, mem_map]
      exact univ_mem' fun n => abs_le.mp (hF1 n x))
    exact ⟨c, hc, by rw [Ultrafilter.coe_map] at hle; exact hle⟩
  choose G hGI hGt using hlim
  -- G is harmonic
  have hharm : IsHarmonic μ G := by
    intro x
    have hdiff : ∀ n, |F n x - ∑' y, F n (x * y) * μ y| ≤
        ∑' v, |convPow μ (n + 1) v - convPow μ n v| := by
      intro n
      have hν := isProb_convPow hμ n
      have hν1 := isProb_convPow hμ (n + 1)
      have e : ∑' y, F n (x * y) * μ y = ∑' v, s n (x * v) * convPow μ (n + 1) v := by
        rw [convPow_succ' hμ n, tsum_mul_conv hμ hν (fun v => hs1 n (x * v))]
        congr 1; ext h
        simp only [hFdef, mul_assoc]
        ring
      rw [e]
      have sp := summable_bdd_mul (hs1 n) hν.1 hν.2.summable x
      have sq := summable_bdd_mul (hs1 n) hν1.1 hν1.2.summable x
      rw [← sp.tsum_sub sq]
      have hpt : ∀ v, |s n (x * v) * convPow μ n v - s n (x * v) * convPow μ (n + 1) v| ≤
          |convPow μ (n + 1) v - convPow μ n v| := by
        intro v
        rw [← mul_sub, abs_mul, abs_sub_comm (convPow μ (n + 1) v)]
        simpa using mul_le_mul_of_nonneg_right (hs1 n (x * v)) (abs_nonneg _)
      have hS := (summable_abs_sub hν1 hν).1
      have sa : Summable fun v =>
          |s n (x * v) * convPow μ n v - s n (x * v) * convPow μ (n + 1) v| :=
        Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hpt hS
      calc |∑' v, (s n (x * v) * convPow μ n v - s n (x * v) * convPow μ (n + 1) v)|
          ≤ ∑' v, |s n (x * v) * convPow μ n v - s n (x * v) * convPow μ (n + 1) v| := by
            have := norm_tsum_le_tsum_norm (f := fun v =>
              s n (x * v) * convPow μ n v - s n (x * v) * convPow μ (n + 1) v)
              (by simpa [Real.norm_eq_abs] using sa)
            simpa [Real.norm_eq_abs] using this
        _ ≤ ∑' v, |convPow μ (n + 1) v - convPow μ n v| := sa.tsum_le_tsum hpt hS
    have h0 : Tendsto (fun n => F n x - ∑' y, F n (x * y) * μ y) U (𝓝 0) := by
      refine Tendsto.mono_left ?_ hUat
      exact squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hdiff n) hap
    have h1 : Tendsto (fun n => ∑' y, F n (x * y) * μ y) U (𝓝 (∑' y, G (x * y) * μ y)) := by
      refine tendsto_tsum_of_dominated_convergence (bound := μ) hμ.2.summable
        (fun y => (hGt (x * y)).mul_const (μ y)) (Eventually.of_forall fun n y => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hμ.1 y)]
      simpa using mul_le_mul_of_nonneg_right (hF1 n (x * y)) (hμ.1 y)
    have h2 := (hGt x).sub h1
    have := tendsto_nhds_unique h2 h0
    linarith
  -- G separates g from 1
  have hsep : ε ≤ G g - G 1 := by
    have e : ∀ n, F n g - F n 1 = a n := by
      intro n
      have hν := isProb_convPow hμ n
      have e1 : F n g = ∑' z, s n z * convPow μ n (g⁻¹ * z) := by
        simp only [hFdef]
        rw [← (Equiv.mulLeft g).tsum_eq (fun z => s n z * convPow μ n (g⁻¹ * z))]
        simp
      have e2 : F n 1 = ∑' z, s n z * convPow μ n z := by simp [hFdef]
      have sp : Summable fun z => s n z * convPow μ n (g⁻¹ * z) := by
        simpa using summable_bdd_mul (hs1 n) (isProb_transl hν g).1
          (isProb_transl hν g).2.summable 1
      have sq : Summable fun z => s n z * convPow μ n z := by
        simpa using summable_bdd_mul (hs1 n) hν.1 hν.2.summable 1
      rw [e1, e2, ← sp.tsum_sub sq]
      simp only [ha]
      congr 1; ext z
      rw [← hsd n z]; ring
    have ht : Tendsto (fun n => F n g - F n 1) U (𝓝 (G g - G 1)) := (hGt g).sub (hGt 1)
    simp_rw [e] at ht
    exact ge_of_tendsto ht (Filter.mem_of_superset hUS fun n hn => hn)
  apply hL
  refine ⟨G, ⟨1, fun x => abs_le.mpr ⟨(hGI x).1, (hGI x).2⟩⟩, hharm, g, hg, 1,
    Submonoid.one_mem _, ?_⟩
  intro h
  rw [h] at hsep
  linarith

/-! ### Entropy: bounded likelihood ratios -/

lemma psi_le {p q m : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hm : 0 < m) (hm1 : m ≤ 1)
    (hmpq : m * p ≤ q) : psi p q ≤ (1 - Real.log m) * |p - q| := by
  have hlm : Real.log m ≤ 0 := Real.log_nonpos hm.le hm1
  rcases hp.lt_or_eq with hp | hp
  · have hq' : 0 < q := lt_of_lt_of_le (mul_pos hm hp) hmpq
    unfold psi
    rcases le_or_gt p q with hpq | hpq
    · have hl : Real.log p ≤ Real.log q := Real.log_le_log hp hpq
      rw [abs_of_nonpos (by linarith : p - q ≤ 0)]
      nlinarith [mul_le_mul_of_nonneg_left hl hp.le,
        mul_nonneg (neg_nonneg.mpr hlm) (sub_nonneg.mpr hpq)]
    · rw [abs_of_pos (by linarith : 0 < p - q)]
      have h1 : Real.log (p / q) ≤ p / q - 1 := Real.log_le_sub_one_of_pos (div_pos hp hq')
      rw [Real.log_div hp.ne' hq'.ne'] at h1
      have h1' : q * (Real.log p - Real.log q) ≤ p - q := by
        have := mul_le_mul_of_nonneg_left h1 hq'.le
        have e : q * (p / q - 1) = p - q := by field_simp
        linarith
      have h2 : Real.log p - Real.log q ≤ -Real.log m := by
        have := Real.log_le_log (mul_pos hm hp) hmpq
        rw [Real.log_mul hm.ne' hp.ne'] at this
        linarith
      nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ p - q)]
  · rw [← hp]
    simp only [psi, zero_mul, sub_zero, zero_sub, abs_neg, abs_of_nonneg hq, zero_add]
    nlinarith [mul_nonneg (neg_nonneg.mpr hlm) hq]

lemma summable_weight {μ : Γ → ℝ} (hμ : IsProbability μ) (hH : HasFiniteEntropy μ) :
    Summable fun g => μ g + Real.negMulLog (μ g) := hμ.2.summable.add hH

lemma weight_nonneg {μ : Γ → ℝ} (hμ : IsProbability μ) (g : Γ) :
    0 ≤ μ g + Real.negMulLog (μ g) :=
  add_nonneg (hμ.1 g) (Real.negMulLog_nonneg (hμ.1 g) (le_one_of_isProb hμ g))

lemma gap_le {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hH : HasFiniteEntropy μ)
    (hν : IsProbability ν) (z : Γ) :
    Real.negMulLog (conv μ ν z) - ∑' g, μ g * Real.negMulLog (ν (g⁻¹ * z)) ≤
      ∑' g, (μ g + Real.negMulLog (μ g)) * |ν (g⁻¹ * z) - conv μ ν z| := by
  have hq := isProb_conv hμ hν
  have hb : ∀ g, |ν (g⁻¹ * z) - conv μ ν z| ≤ 1 := fun g => by
    have := hν.1 (g⁻¹ * z); have := le_one_of_isProb hν (g⁻¹ * z)
    have := hq.1 z; have := le_one_of_isProb hq z
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hs : Summable fun g => (μ g + Real.negMulLog (μ g)) * |ν (g⁻¹ * z) - conv μ ν z| :=
    Summable.of_nonneg_of_le (fun g => mul_nonneg (weight_nonneg hμ g) (abs_nonneg _))
      (fun g => by simpa using mul_le_mul_of_nonneg_left (hb g) (weight_nonneg hμ g))
      (summable_weight hμ hH)
  refine hasSum_le (fun g => ?_) (hasSum_gap hμ hν z) hs.hasSum
  rcases (hμ.1 g).lt_or_eq with hg | hg
  · have hle : μ g * ν (g⁻¹ * z) ≤ conv μ ν z :=
      (conv_summand_summable hμ hν z).le_tsum g (fun j _ => mul_nonneg (hμ.1 j) (hν.1 _))
    have h := psi_le (hν.1 _) (conv_nonneg hμ hν z) hg (le_one_of_isProb hμ g) hle
    have e : μ g + Real.negMulLog (μ g) = μ g * (1 - Real.log (μ g)) := by
      unfold Real.negMulLog; ring
    rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_left h hg.le
  · rw [← hg]; simp

lemma delta_le {μ : Γ → ℝ} (hμ : IsProbability μ) (hH : HasFiniteEntropy μ)
    (hfin : ∀ n, HasFiniteEntropy (convPow μ n)) (n : ℕ) :
    entropy (convPow μ (n + 1)) - entropy (convPow μ n) ≤
      ∑' g, (μ g + Real.negMulLog (μ g)) *
        ∑' z, |convPow μ n (g⁻¹ * z) - conv μ (convPow μ n) z| := by
  have hν := isProb_convPow hμ n
  have hJ := hasSum_gap_total hμ hfin n
  set ν := convPow μ n
  have hq := isProb_conv hμ hν
  set K : Γ → Γ → ℝ := fun g z => (μ g + Real.negMulLog (μ g)) * |ν (g⁻¹ * z) - conv μ ν z|
    with hK
  have hK0 : 0 ≤ Function.uncurry K := fun p =>
    mul_nonneg (weight_nonneg hμ p.1) (abs_nonneg _)
  have hrow : ∀ g, Summable (K g) ∧ ∑' z, K g z ≤ 2 * (μ g + Real.negMulLog (μ g)) := by
    intro g
    obtain ⟨h1, h2⟩ := summable_abs_sub (isProb_transl hν g) hq
    refine ⟨h1.mul_left _, ?_⟩
    simp only [hK]
    rw [tsum_mul_left, mul_comm 2]
    exact mul_le_mul_of_nonneg_left h2 (weight_nonneg hμ g)
  have hKs : Summable (Function.uncurry K) := by
    refine (summable_prod_of_nonneg hK0).mpr ⟨fun g => (hrow g).1, ?_⟩
    refine Summable.of_nonneg_of_le (fun g => tsum_nonneg fun z => hK0 (g, z))
      (fun g => (hrow g).2) ((summable_weight hμ hH).mul_left 2)
  have hcol : Summable fun z => ∑' g, K g z := hKs.prod_symm.prod
  calc entropy (convPow μ (n + 1)) - entropy ν
      = ∑' z, (Real.negMulLog (conv μ ν z) - ∑' g, μ g * Real.negMulLog (ν (g⁻¹ * z))) :=
        hJ.tsum_eq.symm
    _ ≤ ∑' z, ∑' g, K g z := hJ.summable.tsum_le_tsum (fun z => gap_le hμ hH hν z) hcol
    _ = ∑' g, ∑' z, K g z := hKs.tsum_comm
    _ = ∑' g, (μ g + Real.negMulLog (μ g)) * ∑' z, |ν (g⁻¹ * z) - conv μ ν z| := by
        congr 1; ext g; simp only [hK]; rw [tsum_mul_left]

lemma delta_nonneg {μ : Γ → ℝ} (hμ : IsProbability μ)
    (hfin : ∀ n, HasFiniteEntropy (convPow μ n)) (n : ℕ) :
    0 ≤ entropy (convPow μ (n + 1)) - entropy (convPow μ n) := by
  have hν := isProb_convPow hμ n
  refine (hasSum_gap_total hμ hfin n).nonneg (fun z => ?_)
  exact (hasSum_gap hμ hν z).nonneg (fun g => gap_term_nonneg hμ hν z g)

/-- If `‖δ_g ⋆ μ^{(n)} − μ^{(n+1)}‖₁ → 0` for every `g ∈ supp μ`, then `h_μ = 0`. -/
theorem asymptoticEntropy_eq_zero_of_tendsto [Countable Γ] {μ : Γ → ℝ} (hμ : IsProbability μ)
    (hH : HasFiniteEntropy μ)
    (h : ∀ g, μ g ≠ 0 → Tendsto (fun n => ∑' z, |convPow μ n (g⁻¹ * z) -
      conv μ (convPow μ n) z|) atTop (𝓝 0)) :
    asymptoticEntropy μ = 0 := by
  obtain ⟨hfin, hT⟩ := hasFiniteEntropy_convPow_and_tendsto_entropy_convPow_div μ hμ hH
  set Δ : ℕ → ℝ := fun k => entropy (convPow μ (k + 1)) - entropy (convPow μ k) with hΔ
  set D : ℕ → Γ → ℝ := fun n g => ∑' z, |convPow μ n (g⁻¹ * z) - conv μ (convPow μ n) z|
    with hD
  have hD2 : ∀ n g, 0 ≤ D n g ∧ D n g ≤ 2 := fun n g =>
    ⟨tsum_nonneg fun _ => abs_nonneg _,
      (summable_abs_sub (isProb_transl (isProb_convPow hμ n) g)
        (isProb_conv hμ (isProb_convPow hμ n))).2⟩
  have hup : Tendsto (fun n => ∑' g, (μ g + Real.negMulLog (μ g)) * D n g) atTop (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun n g => (μ g + Real.negMulLog (μ g)) * D n g) (g := fun _ => (0 : ℝ))
      (bound := fun g => 2 * (μ g + Real.negMulLog (μ g)))
      ((summable_weight hμ hH).mul_left 2) (fun g => ?_)
      (Eventually.of_forall fun n g => ?_)
    · simpa using this
    · by_cases hg : μ g = 0
      · simp [hg]
      · simpa using (h g hg).const_mul (μ g + Real.negMulLog (μ g))
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weight_nonneg hμ g) (hD2 n g).1)]
      nlinarith [(hD2 n g).2, weight_nonneg hμ g]
  have hΔt : Tendsto Δ atTop (𝓝 0) :=
    squeeze_zero (fun n => delta_nonneg hμ hfin n) (fun n => delta_le hμ hH hfin n) hup
  have hc := hΔt.cesaro
  have e : ∀ n : ℕ, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Δ i = entropy (convPow μ n) / n := by
    intro n
    rw [Finset.sum_range_sub (fun k => entropy (convPow μ k)), entropy_convPow_zero, sub_zero,
      div_eq_inv_mul]
  simp_rw [e] at hc
  exact tendsto_nhds_unique hT hc

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

open scoped Classical in
/-- The lazy measure `(δ_1 + μ)/2`. -/
noncomputable def lazy (μ : Γ → ℝ) : Γ → ℝ := fun g => ((if g = 1 then 1 else 0) + μ g) / 2

open scoped Classical in
lemma isProb_delta : IsProbability (fun g : Γ => if g = 1 then (1 : ℝ) else 0) := by
  refine ⟨fun g => by dsimp only; split_ifs <;> norm_num, ?_⟩
  convert hasSum_ite_eq (1 : Γ) (1 : ℝ) using 1

lemma isProb_lazy {μ : Γ → ℝ} (hμ : IsProbability μ) : IsProbability (lazy μ) := by
  classical
  refine ⟨fun g => div_nonneg (add_nonneg (isProb_delta.1 g) (hμ.1 g)) two_pos.le, ?_⟩
  have := (isProb_delta.2.add hμ.2).div_const 2
  norm_num at this
  exact this

lemma hasFiniteEntropy_lazy {μ : Γ → ℝ} (hμ : IsProbability μ) (hH : HasFiniteEntropy μ) :
    HasFiniteEntropy (lazy μ) := by
  have h1 : Summable fun g => Real.negMulLog (μ g / 2) := by
    have : ∀ g, Real.negMulLog (μ g / 2) =
        (1 / 2) * Real.negMulLog (μ g) + μ g * Real.negMulLog (1 / 2) := by
      intro g; rw [div_eq_mul_one_div, Real.negMulLog_mul]
    simp_rw [this]
    exact (hH.mul_left _).add (hμ.2.summable.mul_right _)
  refine h1.congr_cofinite ?_
  filter_upwards [(Set.finite_singleton (1 : Γ)).compl_mem_cofinite] with g hg
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hg
  simp [lazy, hg]

lemma harmonic_of_lazy {μ : Γ → ℝ} (hμ : IsProbability μ) {f : Γ → ℝ} {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (hf : IsHarmonic (lazy μ) f) : IsHarmonic μ f := by
  classical
  intro x
  have h := hf x
  have hs1 := summable_bdd_mul hC isProb_delta.1 isProb_delta.2.summable x
  have hs2 := summable_bdd_mul hC hμ.1 hμ.2.summable x
  have e : ∑' y, f (x * y) * lazy μ y = (∑' y, f (x * y) * (if y = 1 then (1 : ℝ) else 0) +
      ∑' y, f (x * y) * μ y) / 2 := by
    rw [← hs1.tsum_add hs2, ← tsum_div_const]
    congr 1; ext y; simp only [lazy]; ring
  have e1 : ∑' y, f (x * y) * (if y = 1 then (1 : ℝ) else 0) = f x := by
    rw [tsum_eq_single 1]
    · simp
    · intro b hb; simp [hb]
  rw [e, e1] at h
  linarith

lemma closure_lazy_le (μ : Γ → ℝ) :
    Submonoid.closure (Function.support (lazy μ)) ≤ Submonoid.closure (Function.support μ) := by
  rw [Submonoid.closure_le]
  intro g hg
  by_cases h1 : g = 1
  · rw [h1]; exact Submonoid.one_mem _
  · apply Submonoid.subset_closure
    simp only [Function.mem_support, lazy, h1, if_false, zero_add] at hg ⊢
    intro h; apply hg; rw [h]; simp

lemma hasNontrivial_of_lazy {μ : Γ → ℝ} (hμ : IsProbability μ)
    (h : HasNontrivialPoissonBoundary (lazy μ)) : HasNontrivialPoissonBoundary μ := by
  obtain ⟨f, ⟨C, hC⟩, hf, x, hx, y, hy, hxy⟩ := h
  exact ⟨f, ⟨C, hC⟩, harmonic_of_lazy hμ hC hf, x, closure_lazy_le μ hx, y,
    closure_lazy_le μ hy, hxy⟩

/-! ### The binomial expansion -/

/-- `C(n,k)/2^n`. -/
noncomputable def bin (n k : ℕ) : ℝ := (n.choose k : ℝ) / 2 ^ n

lemma bin_nonneg (n k : ℕ) : 0 ≤ bin n k := by unfold bin; positivity

lemma sum_bin (n : ℕ) : ∑ k ∈ Finset.range (n + 1), bin n k = 1 := by
  unfold bin
  rw [← Finset.sum_div]
  have := congrArg (Nat.cast (R := ℝ)) (Nat.sum_range_choose n)
  push_cast at this
  rw [this, div_self (by positivity)]

lemma conv_lazy {a μ : Γ → ℝ} (ha : IsProbability a) (hμ : IsProbability μ) (z : Γ) :
    conv a (lazy μ) z = (a z + conv a μ z) / 2 := by
  classical
  have hs1 := conv_summand_summable ha isProb_delta z
  have hs2 := conv_summand_summable ha hμ z
  have e : ∀ h, a h * lazy μ (h⁻¹ * z) =
      (a h * (if h⁻¹ * z = 1 then (1 : ℝ) else 0) + a h * μ (h⁻¹ * z)) / 2 := by
    intro h; simp only [lazy]; ring
  show ∑' h, a h * lazy μ (h⁻¹ * z) = (a z + conv a μ z) / 2
  simp_rw [e]
  rw [tsum_div_const, hs1.tsum_add hs2]
  congr 2
  exact congrFun (conv_delta a) z

lemma convPow_lazy {μ : Γ → ℝ} (hμ : IsProbability μ) (n : ℕ) (z : Γ) :
    convPow (lazy μ) n z = ∑ k ∈ Finset.range (n + 1), bin n k * convPow μ k z := by
  induction n generalizing z with
  | zero => simp [bin, convPow]
  | succ n ih =>
    have hsk : ∀ k, IsProbability (convPow μ k) := isProb_convPow hμ
    show conv (convPow (lazy μ) n) (lazy μ) z = _
    rw [conv_lazy (isProb_convPow (isProb_lazy hμ) n) hμ z]
    have hc : conv (convPow (lazy μ) n) μ z =
        ∑ k ∈ Finset.range (n + 1), bin n k * convPow μ (k + 1) z := by
      unfold conv
      simp_rw [ih, Finset.sum_mul]
      rw [Summable.tsum_finsetSum (fun k _ => ?_)]
      · congr 1; ext k
        simp_rw [mul_assoc]
        rw [tsum_mul_left]
        rfl
      · exact (conv_summand_summable (hsk k) hμ z).mul_left _ |>.congr fun h => by ring
    rw [ih z, hc]
    have hb : ∀ k, bin (n + 1) (k + 1) = (bin n k + bin n (k + 1)) / 2 := by
      intro k; simp only [bin, Nat.choose_succ_succ', pow_succ]; push_cast; ring
    have hb0 : bin (n + 1) 0 = bin n 0 / 2 := by simp [bin, pow_succ]; ring
    have hbn : bin n (n + 1) = 0 := by simp [bin, Nat.choose_succ_self]
    have L1 : ∑ k ∈ Finset.range (n + 1), bin n k * convPow μ k z =
        ∑ k ∈ Finset.range n, bin n (k + 1) * convPow μ (k + 1) z + bin n 0 * convPow μ 0 z :=
      Finset.sum_range_succ' _ _
    have L2 : ∑ k ∈ Finset.range (n + 1), bin n (k + 1) * convPow μ (k + 1) z =
        ∑ k ∈ Finset.range n, bin n (k + 1) * convPow μ (k + 1) z := by
      rw [Finset.sum_range_succ, hbn, zero_mul, add_zero]
    have R : ∑ k ∈ Finset.range (n + 1 + 1), bin (n + 1) k * convPow μ k z =
        (∑ k ∈ Finset.range (n + 1), bin n k * convPow μ (k + 1) z +
          ∑ k ∈ Finset.range (n + 1), bin n (k + 1) * convPow μ (k + 1) z) / 2 +
          bin n 0 / 2 * convPow μ 0 z := by
      rw [Finset.sum_range_succ', hb0]
      congr 1
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      congr 1; ext k
      rw [hb]; ring
    rw [R, L1, L2]
    ring

/-! ### Aperiodicity of the lazy walk -/

lemma sum_choose_sq (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * (2 * (k : ℝ) - (m : ℝ)) ^ 2 =
      (m : ℝ) * 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_succ_succ']
    push_cast
    have hsplit : ∀ k ∈ Finset.range (m + 1),
        ((m.choose k : ℝ) + (m.choose (k + 1) : ℝ)) * (2 * ((k : ℝ) + 1) - ((m : ℝ) + 1)) ^ 2 =
        (m.choose k : ℝ) * (2 * (k : ℝ) - m + 1) ^ 2 +
          (m.choose (k + 1) : ℝ) * (2 * ((k + 1 : ℕ) : ℝ) - m - 1) ^ 2 := by
      intro k _; push_cast; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    have hshift : ∑ k ∈ Finset.range (m + 1),
        (m.choose (k + 1) : ℝ) * (2 * ((k + 1 : ℕ) : ℝ) - m - 1) ^ 2 +
          (m.choose 0 : ℝ) * (2 * ((0 : ℕ) : ℝ) - m - 1) ^ 2 =
        ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * (2 * (k : ℝ) - m - 1) ^ 2 := by
      rw [← Finset.sum_range_succ' (fun k => (m.choose k : ℝ) * (2 * (k : ℝ) - m - 1) ^ 2),
        Finset.sum_range_succ, Nat.choose_succ_self]
      simp
    have hc0 : ((m + 1).choose 0 : ℝ) = (m.choose 0 : ℝ) := by simp
    have hfin : ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * (2 * (k : ℝ) - m + 1) ^ 2 +
        ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * (2 * (k : ℝ) - m - 1) ^ 2 =
        2 * ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * (2 * (k : ℝ) - (m : ℝ)) ^ 2 +
          2 * ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      congr 1; ext k; ring
    have h2 := congrArg (Nat.cast (R := ℝ)) (Nat.sum_range_choose m)
    push_cast at h2
    simp only [Nat.choose_zero_right, Nat.cast_one] at hshift ⊢
    linear_combination hshift + hfin + 2 * ih + 2 * h2

lemma bin_diff (n k : ℕ) (hk : k ≤ n + 1) :
    bin (n + 1) k - bin n k = bin (n + 1) k * (2 * (k : ℝ) - ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
  have h := congrArg (Nat.cast (R := ℝ)) (Nat.choose_mul_succ_eq n k)
  push_cast [Nat.cast_sub hk] at h
  unfold bin
  rw [pow_succ]
  field_simp
  linear_combination (-2 : ℝ) * h

lemma sum_abs_bin_diff (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1 + 1), |bin (n + 1) k - bin n k| ≤ 1 / Real.sqrt ((n : ℝ) + 1) := by
  set M : ℝ := (n : ℝ) + 1 with hMdef
  have hM : 0 < M := by positivity
  set r := Real.sqrt M with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hM
  have hr2 : r ^ 2 = M := Real.sq_sqrt hM.le
  have e1 : ∀ k ∈ Finset.range (n + 1 + 1), |bin (n + 1) k - bin n k| =
      bin (n + 1) k * |2 * (k : ℝ) - M| / M := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [bin_diff n k (by omega), abs_div, abs_mul, abs_of_nonneg (bin_nonneg _ _),
      abs_of_pos hM]
  rw [Finset.sum_congr rfl e1]
  have hpt : ∀ k ∈ Finset.range (n + 1 + 1), bin (n + 1) k * |2 * (k : ℝ) - M| / M ≤
      bin (n + 1) k * ((2 * (k : ℝ) - M) ^ 2 + M) / (2 * r * M) := by
    intro k _
    rw [div_le_div_iff₀ hM (by positivity)]
    have hb := bin_nonneg (n + 1) k
    have hx : |2 * (k : ℝ) - M| * (2 * r) ≤ (2 * (k : ℝ) - M) ^ 2 + M := by
      nlinarith [sq_nonneg (|2 * (k : ℝ) - M| - r), sq_abs (2 * (k : ℝ) - M)]
    have := mul_le_mul_of_nonneg_left hx hb
    nlinarith
  refine (Finset.sum_le_sum hpt).trans (le_of_eq ?_)
  have hV := sum_choose_sq (n + 1)
  push_cast at hV
  have hS := sum_bin (n + 1)
  rw [← Finset.sum_div]
  have e2 : ∑ k ∈ Finset.range (n + 1 + 1), bin (n + 1) k * ((2 * (k : ℝ) - M) ^ 2 + M) =
      M + M := by
    have e3 : ∑ k ∈ Finset.range (n + 1 + 1), bin (n + 1) k * (2 * (k : ℝ) - M) ^ 2 = M := by
      unfold bin
      rw [show (∑ k ∈ Finset.range (n + 1 + 1),
          ((n + 1).choose k : ℝ) / 2 ^ (n + 1) * (2 * (k : ℝ) - M) ^ 2) =
          (∑ k ∈ Finset.range (n + 1 + 1), ((n + 1).choose k : ℝ) * (2 * (k : ℝ) - M) ^ 2) /
            2 ^ (n + 1) by rw [Finset.sum_div]; congr 1; ext k; ring]
      rw [hMdef, hV]
      field_simp
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, e3, ← Finset.sum_mul, hS, one_mul]
  rw [e2]
  field_simp
  nlinarith [hr2]

lemma tv_lazy_le {μ : Γ → ℝ} (hμ : IsProbability μ) (n : ℕ) :
    ∑' z, |convPow (lazy μ) (n + 1) z - convPow (lazy μ) n z| ≤
      ∑ k ∈ Finset.range (n + 1 + 1), |bin (n + 1) k - bin n k| := by
  have hsk : ∀ k, IsProbability (convPow μ k) := isProb_convPow hμ
  have hext : ∀ z, convPow (lazy μ) n z =
      ∑ k ∈ Finset.range (n + 1 + 1), bin n k * convPow μ k z := by
    intro z
    rw [convPow_lazy hμ n z, Finset.sum_range_succ _ (n + 1)]
    simp [bin, Nat.choose_succ_self]
  have hpt : ∀ z, |convPow (lazy μ) (n + 1) z - convPow (lazy μ) n z| ≤
      ∑ k ∈ Finset.range (n + 1 + 1), |bin (n + 1) k - bin n k| * convPow μ k z := by
    intro z
    rw [convPow_lazy hμ (n + 1) z, hext z, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    congr 1; ext k
    rw [← sub_mul, abs_mul, abs_of_nonneg ((hsk k).1 z)]
  have hs1 := (summable_abs_sub (isProb_convPow (isProb_lazy hμ) (n + 1))
    (isProb_convPow (isProb_lazy hμ) n)).1
  have hs2 : Summable fun z => ∑ k ∈ Finset.range (n + 1 + 1),
      |bin (n + 1) k - bin n k| * convPow μ k z :=
    summable_sum fun k _ => (hsk k).2.summable.mul_left _
  refine (hs1.tsum_le_tsum hpt hs2).trans (le_of_eq ?_)
  rw [Summable.tsum_finsetSum fun k _ => (hsk k).2.summable.mul_left _]
  congr 1; ext k
  rw [tsum_mul_left, (hsk k).2.tsum_eq, mul_one]

lemma tendsto_tv_lazy {μ : Γ → ℝ} (hμ : IsProbability μ) :
    Tendsto (fun n => ∑' z, |convPow (lazy μ) (n + 1) z - convPow (lazy μ) n z|) atTop
      (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 1 / Real.sqrt ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simp_rw [one_div]
    exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
  exact squeeze_zero (fun n => tsum_nonneg fun _ => abs_nonneg _)
    (fun n => (tv_lazy_le hμ n).trans (sum_abs_bin_diff n)) h

/-! ### Entropy of the lazy walk: `h_μ ⩽ 2 h_{μ'}` -/

lemma sum_bin_mul (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1 + 1), bin (m + 1) k * (k : ℝ) = ((m : ℝ) + 1) / 2 := by
  have h := congrArg (Nat.cast (R := ℝ)) (Nat.sum_range_mul_choose (m + 1))
  push_cast at h
  try simp only [add_tsub_cancel_right] at h
  unfold bin
  rw [show (∑ k ∈ Finset.range (m + 1 + 1), ((m + 1).choose k : ℝ) / 2 ^ (m + 1) * (k : ℝ)) =
      (∑ k ∈ Finset.range (m + 1 + 1), (k : ℝ) * ((m + 1).choose k : ℝ)) / 2 ^ (m + 1) by
    rw [Finset.sum_div]; congr 1; ext k; ring]
  rw [h, pow_succ]
  field_simp

lemma entropy_lazy_ge [Countable Γ] {μ : Γ → ℝ} (hμ : IsProbability μ) (hH : HasFiniteEntropy μ)
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) / 2 * asymptoticEntropy μ ≤ entropy (convPow (lazy μ) n) := by
  obtain ⟨hfin, hT⟩ := hasFiniteEntropy_convPow_and_tendsto_entropy_convPow_div μ hμ hH
  have hfin' := (hasFiniteEntropy_convPow_and_tendsto_entropy_convPow_div (lazy μ)
    (isProb_lazy hμ) (hasFiniteEntropy_lazy hμ hH)).1 n
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
  have hk : ∀ k : ℕ, (k : ℝ) * asymptoticEntropy μ ≤ entropy (convPow μ k) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [entropy_convPow_zero]
    · have h := hsub.lim_le_div hbdd (Nat.pos_iff_ne_zero.mp hk)
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      rw [le_div_iff₀ hk'] at h
      rw [hlim]; linarith
  have hJ : ∀ z, ∑ k ∈ Finset.range (n + 1), bin n k * Real.negMulLog (convPow μ k z) ≤
      Real.negMulLog (convPow (lazy μ) n z) := by
    intro z
    rw [convPow_lazy hμ n z]
    have := Real.concaveOn_negMulLog.le_map_sum (t := Finset.range (n + 1)) (w := bin n)
      (p := fun k => convPow μ k z) (fun k _ => bin_nonneg n k) (sum_bin n)
      (fun k _ => Set.mem_Ici.mpr ((hsk k).1 z))
    simpa [smul_eq_mul] using this
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  calc ((m + 1 : ℕ) : ℝ) / 2 * asymptoticEntropy μ
      = ∑ k ∈ Finset.range (m + 1 + 1), bin (m + 1) k * ((k : ℝ) * asymptoticEntropy μ) := by
        simp_rw [← mul_assoc]
        rw [← Finset.sum_mul, sum_bin_mul]
        push_cast; ring
    _ ≤ ∑ k ∈ Finset.range (m + 1 + 1), bin (m + 1) k * entropy (convPow μ k) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hk k) (bin_nonneg _ _)
    _ = ∑' z, ∑ k ∈ Finset.range (m + 1 + 1), bin (m + 1) k * Real.negMulLog (convPow μ k z) := by
        rw [Summable.tsum_finsetSum fun k _ => (hfin k).mul_left _]
        congr 1; ext k
        rw [tsum_mul_left]; rfl
    _ ≤ ∑' z, Real.negMulLog (convPow (lazy μ) (m + 1) z) :=
        (summable_sum fun k _ => (hfin k).mul_left _).tsum_le_tsum hJ hfin'
    _ = entropy (convPow (lazy μ) (m + 1)) := rfl

lemma asymptoticEntropy_nonneg [Countable Γ] {μ : Γ → ℝ} (hμ : IsProbability μ)
    (hH : HasFiniteEntropy μ) : 0 ≤ asymptoticEntropy μ := by
  obtain ⟨_, hT⟩ := hasFiniteEntropy_convPow_and_tendsto_entropy_convPow_div μ hμ hH
  refine ge_of_tendsto hT (Eventually.of_forall fun n => ?_)
  rw [entropy_eq_toReal (isProb_convPow hμ n)]
  positivity

lemma asymptoticEntropy_le_two_mul_lazy [Countable Γ] {μ : Γ → ℝ} (hμ : IsProbability μ)
    (hH : HasFiniteEntropy μ) : asymptoticEntropy μ ≤ 2 * asymptoticEntropy (lazy μ) := by
  obtain ⟨_, hT'⟩ := hasFiniteEntropy_convPow_and_tendsto_entropy_convPow_div (lazy μ)
    (isProb_lazy hμ) (hasFiniteEntropy_lazy hμ hH)
  have : asymptoticEntropy μ / 2 ≤ asymptoticEntropy (lazy μ) := by
    refine ge_of_tendsto hT' ((eventually_ge_atTop 1).mono fun n hn => ?_)
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn']
    have := entropy_lazy_ge hμ hH n hn
    linarith
  linarith

/-! ### The converse: a trivial boundary forces `h_μ = 0` -/

theorem asymptoticEntropy_eq_zero_of_not_hasNontrivialPoissonBoundary [Countable Γ]
    (μ : Γ → ℝ) (hμ : IsProbability μ) (hH : HasFiniteEntropy μ)
    (hL : ¬ HasNontrivialPoissonBoundary μ) : asymptoticEntropy μ = 0 := by
  have hμ' := isProb_lazy hμ
  have hH' := hasFiniteEntropy_lazy hμ hH
  have hL' : ¬ HasNontrivialPoissonBoundary (lazy μ) := fun h => hL (hasNontrivial_of_lazy hμ h)
  have hap := tendsto_tv_lazy hμ
  have h0' : asymptoticEntropy (lazy μ) = 0 := by
    refine asymptoticEntropy_eq_zero_of_tendsto hμ' hH' (fun g hg => ?_)
    have hgc : g ∈ Submonoid.closure (Function.support (lazy μ)) := Submonoid.subset_closure hg
    have h1 := tendsto_tv_of_liouville hμ' hL' hap hgc
    refine squeeze_zero (fun n => tsum_nonneg fun _ => abs_nonneg _) (fun n => ?_)
      (by simpa using h1.add hap)
    rw [← convPow_succ' hμ' n]
    have ha := isProb_transl (isProb_convPow hμ' n) g
    have hb := isProb_convPow hμ' n
    have hc := isProb_convPow hμ' (n + 1)
    have s1 := (summable_abs_sub ha hc).1
    have s2 := (summable_abs_sub ha hb).1
    have s3 := (summable_abs_sub hc hb).1
    calc ∑' z, |convPow (lazy μ) n (g⁻¹ * z) - convPow (lazy μ) (n + 1) z|
        ≤ ∑' z, (|convPow (lazy μ) n (g⁻¹ * z) - convPow (lazy μ) n z| +
            |convPow (lazy μ) (n + 1) z - convPow (lazy μ) n z|) :=
          s1.tsum_le_tsum (fun z => by
            rw [abs_sub_comm (convPow (lazy μ) (n + 1) z)]
            exact abs_sub_le _ _ _) (s2.add s3)
      _ = _ := s2.tsum_add s3
  have hle := asymptoticEntropy_le_two_mul_lazy hμ hH
  have hge := asymptoticEntropy_nonneg hμ hH
  linarith

end P5Dev

end ErschlerZheng
end

section
/-!
# C2 (Kaimanovich–Vershik's entropy criterion, Erschler–Zheng p. 10)

For a probability `μ` of finite entropy on a countable group, the Poisson boundary is trivial iff
`h_μ = 0`.

* `h_μ = 0 ⇒` trivial (`P5Liouville`): the entropy increments `Δ_n = H(μ^{(n+1)}) − H(μ^{(n)})`
  are Jensen gaps `Σ_g μ(g) D(δ_g ⋆ μ^{(n)} ‖ μ^{(n+1)})`, `inf_n Δ_n = 0`, and a Pinsker-type
  bound makes every bounded harmonic function right-invariant under `supp μ`.
* trivial `⇒ h_μ = 0` (`P5Converse`, `P5Lazy`): pass to the lazy walk `(δ_1 + μ)/2` (same bounded
  harmonic functions, `‖μ'^{(n+1)} − μ'^{(n)}‖₁ ⩽ 1/√(n+1)`, `h_μ ⩽ 2h_{μ'}`); an ultrafilter limit
  of `x ↦ Σ_w s_n(xw) μ'^{(n)}(w)` shows `‖δ_g ⋆ μ'^{(n)} − μ'^{(n)}‖₁ → 0`; bounded likelihood
  ratios (`≤ 1/μ'(g)`) turn this into `Δ'_n → 0` by dominated convergence (finite entropy).
-/

namespace KaimanovichVershik

end KaimanovichVershik
end

section
open KaimanovichVershik
open ErschlerZheng in
theorem solution {Γ : Type*} [Group Γ]
    [Countable Γ] (μ : Γ → ℝ) (hμ : IsProbability μ) (hH : HasFiniteEntropy μ) :
    ¬ HasNontrivialPoissonBoundary μ ↔ asymptoticEntropy μ = 0 :=
  ⟨P5Dev.asymptoticEntropy_eq_zero_of_not_hasNontrivialPoissonBoundary μ hμ hH,
    P5Dev.not_hasNontrivialPoissonBoundary_of_asymptoticEntropy_eq_zero μ hμ hH⟩
end
