-- Prove2me | solution 1 for Kesten.isAmenableAction_iff_limsup_stepProb_rpow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T13:36:40.351975+00:00
-- url     : https://prove2.me/submissions/2beabfbb-7265-4d5c-97b8-2517650eca49

import Mathlib
import Definitions.Def_IntervalExchange

section

/-!
# Kesten's criterion for transitive actions

For a transitive action of `H` on `Y` and a symmetric, non-degenerate, finitely supported
probability `ν` on `H`, the action is amenable iff `limsup p_n(y₀,y₀)^{1/n} = 1`.

Route: the Markov operator `Q f = ∑_g ν g • (g · f)` acts on finitely supported functions,
which we embed into `ℓ²(Y)`. It is self-adjoint and a contraction, and `p_n(x,y) = (Q^n δ_x)(y)`.

* `limsup < 1` ⇒ `‖Q f‖ ≤ r ‖f‖` for some `r < 1` (log-convexity of `‖Q^k f‖` and transfer of
  return probabilities between points) ⇒ the Schreier graph of `Q^k` expands by a factor `2`
  ⇒ (Hall's marriage theorem) a 2-to-1 matching ⇒ a paradoxical decomposition, so no invariant
  mean.
* `limsup = 1` ⇒ `‖Q f‖ ≥ L ‖f‖` for some `f = Q^n δ_{y₀}` and `L` close to `1` ⇒ almost
  invariant unit vectors `w` in `ℓ²` ⇒ the finitely additive probabilities `A ↦ ∑_{y∈A} w(y)²`
  are almost invariant, and an ultrafilter limit is an invariant mean.
-/

open IntervalExchange
open scoped ENNReal RealInnerProductSpace Pointwise

namespace Kesten.IETK

noncomputable section

open Classical

variable {H Y : Type*} [Group H] [MulAction H Y]

/-! ## ℓ² embedding of finitely supported functions -/

abbrev E (Y : Type*) := lp (fun _ : Y => ℝ) 2

def toE : (Y →₀ ℝ) →ₗ[ℝ] E Y :=
  Finsupp.linearCombination ℝ (fun y => (lp.single 2 y (1 : ℝ) : E Y))

theorem toE_single (y : Y) (a : ℝ) : toE (Finsupp.single y a) = lp.single 2 y a := by
  simp only [toE, Finsupp.linearCombination_single]
  rw [← lp.single_smul]
  simp

theorem toE_apply (f : Y →₀ ℝ) (y : Y) : toE f y = f y := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | single x a =>
    rw [toE_single, lp.single_apply, Pi.single_apply, Finsupp.single_apply]
    by_cases h : y = x
    · subst h; simp
    · simp [h, Ne.symm h]

theorem inner_toE (f : Y →₀ ℝ) (w : E Y) : ⟪toE f, w⟫ = ∑ y ∈ f.support, f y * w y := by
  conv_lhs => rw [← Finsupp.sum_single f]
  simp only [Finsupp.sum, map_sum, sum_inner, toE_single]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [lp.inner_single_left]
  simp [mul_comm]

theorem inner_toE' (f : Y →₀ ℝ) (w : E Y) (T : Finset Y) (hT : f.support ⊆ T) :
    ⟪toE f, w⟫ = ∑ y ∈ T, f y * w y := by
  rw [inner_toE]
  refine Finset.sum_subset hT fun y _ hy => ?_
  rw [Finsupp.notMem_support_iff.mp hy, zero_mul]

theorem norm_sq_toE (f : Y →₀ ℝ) (T : Finset Y) (hT : f.support ⊆ T) :
    ‖toE f‖ ^ 2 = ∑ y ∈ T, f y ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_toE' f _ T hT]
  simp [toE_apply, sq]

theorem norm_toE_single (y : Y) : ‖toE (Finsupp.single y (1 : ℝ))‖ = 1 := by
  rw [toE_single, lp.norm_single (by norm_num)]
  simp

theorem inner_toE_single (f : Y →₀ ℝ) (y : Y) :
    ⟪toE f, toE (Finsupp.single y (1 : ℝ))⟫ = f y := by
  rw [toE_single, lp.inner_single_right, toE_apply]
  simp

/-! ## Translations -/

def tr (h : H) : (Y →₀ ℝ) →ₗ[ℝ] (Y →₀ ℝ) := Finsupp.lmapDomain ℝ ℝ (fun y : Y => h • y)

theorem tr_apply (h : H) (f : Y →₀ ℝ) (y : Y) : tr h f y = f (h⁻¹ • y) := by
  have := Finsupp.mapDomain_apply (MulAction.injective h) f (h⁻¹ • y)
  simpa [tr] using this

theorem tr_mul (g h : H) (f : Y →₀ ℝ) : tr (g * h) f = tr g (tr h f) := by
  ext y; simp [tr_apply, mul_smul]

theorem tr_one (f : Y →₀ ℝ) : tr (1 : H) f = f := by
  ext y; simp [tr_apply]

theorem tr_inv_tr (h : H) (f : Y →₀ ℝ) : tr h⁻¹ (tr h f) = f := by
  rw [← tr_mul, inv_mul_cancel, tr_one]

theorem tr_tr_inv (h : H) (f : Y →₀ ℝ) : tr h (tr h⁻¹ f) = f := by
  rw [← tr_mul, mul_inv_cancel, tr_one]

theorem support_tr_subset (h : H) (f : Y →₀ ℝ) :
    (tr h f).support ⊆ f.support.image (fun y => h • y) := by
  intro y hy
  rw [Finsupp.mem_support_iff, tr_apply] at hy
  exact Finset.mem_image.mpr ⟨h⁻¹ • y, Finsupp.mem_support_iff.mpr hy, by simp⟩

theorem inner_tr (h : H) (f g : Y →₀ ℝ) :
    ⟪toE (tr h f), toE g⟫ = ⟪toE f, toE (tr h⁻¹ g)⟫ := by
  rw [inner_toE' _ _ _ (support_tr_subset h f), inner_toE]
  rw [Finset.sum_image (fun a _ b _ hab => (MulAction.injective h) hab)]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [tr_apply, toE_apply]

theorem inner_tr_tr (h : H) (f g : Y →₀ ℝ) :
    ⟪toE (tr h f), toE (tr h g)⟫ = ⟪toE f, toE g⟫ := by
  rw [inner_tr, tr_inv_tr]

theorem norm_tr (h : H) (f : Y →₀ ℝ) : ‖toE (tr h f)‖ = ‖toE f‖ := by
  have h2 : ‖toE (tr h f)‖ ^ 2 = ‖toE f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_tr_tr]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

theorem tr_nonneg (h : H) {f : Y →₀ ℝ} (hf : ∀ y, 0 ≤ f y) (y : Y) : 0 ≤ tr h f y := by
  rw [tr_apply]; exact hf _

/-! ## The Markov operator -/

def Q (ν : H →₀ ℝ) : Module.End ℝ (Y →₀ ℝ) := ∑ g ∈ ν.support, ν g • tr g

theorem Q_eq (ν : H →₀ ℝ) (f : Y →₀ ℝ) : Q ν f = ∑ g ∈ ν.support, ν g • tr g f := by
  simp [Q, Finset.sum_apply]

theorem Q_apply (ν : H →₀ ℝ) (f : Y →₀ ℝ) (y : Y) :
    Q ν f y = ∑ g ∈ ν.support, ν g * f (g⁻¹ • y) := by
  rw [Q_eq, Finsupp.finsetSum_apply]
  simp [tr_apply]

theorem toE_Q (ν : H →₀ ℝ) (f : Y →₀ ℝ) :
    toE (Q ν f) = ∑ g ∈ ν.support, ν g • toE (tr g f) := by
  rw [Q_eq, map_sum]; simp

variable {ν : H →₀ ℝ}

omit [Group H] in
theorem sum_nu (hν : ThompsonAmenability.IsProbability ν) : ∑ g ∈ ν.support, ν g = 1 := hν.2

theorem Q_nonneg (hν : ThompsonAmenability.IsProbability ν) {f : Y →₀ ℝ} (hf : ∀ y, 0 ≤ f y)
    (y : Y) : 0 ≤ Q ν f y := by
  rw [Q_apply]
  exact Finset.sum_nonneg fun g _ => mul_nonneg (hν.1 g) (hf _)

theorem Qpow_nonneg (hν : ThompsonAmenability.IsProbability ν) {f : Y →₀ ℝ}
    (hf : ∀ y, 0 ≤ f y) (n : ℕ) (y : Y) : 0 ≤ (Q ν ^ n) f y := by
  induction n generalizing y with
  | zero => simpa using hf y
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact Q_nonneg hν ih y

theorem norm_Q_le (hν : ThompsonAmenability.IsProbability ν) (f : Y →₀ ℝ) :
    ‖toE (Q ν f)‖ ≤ ‖toE f‖ := by
  rw [toE_Q]
  calc ‖∑ g ∈ ν.support, ν g • toE (tr g f)‖
      ≤ ∑ g ∈ ν.support, ‖ν g • toE (tr g f)‖ := norm_sum_le _ _
    _ = ∑ g ∈ ν.support, ν g * ‖toE f‖ := by
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [norm_smul, norm_tr, Real.norm_of_nonneg (hν.1 g)]
    _ = ‖toE f‖ := by rw [← Finset.sum_mul, sum_nu hν, one_mul]

theorem norm_Qpow_le (hν : ThompsonAmenability.IsProbability ν) (f : Y →₀ ℝ) (n : ℕ) :
    ‖toE ((Q ν ^ n) f)‖ ≤ ‖toE f‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (norm_Q_le hν _).trans ih

theorem inner_Q (hsymm : IsSymmetric ν) (f g : Y →₀ ℝ) :
    ⟪toE (Q ν f), toE g⟫ = ⟪toE f, toE (Q ν g)⟫ := by
  rw [toE_Q, toE_Q, sum_inner, inner_sum]
  simp only [real_inner_smul_left, real_inner_smul_right]
  simp_rw [inner_tr]
  refine Finset.sum_equiv (Equiv.inv H) (fun g => ?_) fun g _ => ?_
  · simp only [Equiv.inv_apply, Finsupp.mem_support_iff]
    rw [hsymm g]
  · simp [hsymm g]

theorem inner_Qpow (hsymm : IsSymmetric ν) (n : ℕ) (f g : Y →₀ ℝ) :
    ⟪toE ((Q ν ^ n) f), toE g⟫ = ⟪toE f, toE ((Q ν ^ n) g)⟫ := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, inner_Q hsymm, ← Module.End.mul_apply, ← pow_succ', pow_succ]

/-! ## Transition probabilities -/

/-- `p_n(x, y) = (Q^n δ_x)(y)`. -/
def pp (ν : H →₀ ℝ) (n : ℕ) (x y : Y) : ℝ := (Q ν ^ n) (Finsupp.single x 1) y

theorem walkKernel_eq' (z y : Y) :
    walkKernel (ν : H → ℝ) z y = ∑ g ∈ ν.support, if g • z = y then ν g else 0 := by
  unfold walkKernel
  rw [tsum_eq_sum (s := ν.support)]
  intro g hg
  rw [Finsupp.notMem_support_iff.mp hg]; simp

theorem tsum_mul_walkKernel (f : Y →₀ ℝ) (y : Y) :
    ∑' z, f z * walkKernel (ν : H → ℝ) z y = Q ν f y := by
  simp only [walkKernel_eq', Finset.mul_sum]
  rw [Summable.tsum_finsetSum]
  · rw [Q_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    have : ∀ z, f z * (if g • z = y then ν g else 0) =
        if z = g⁻¹ • y then ν g * f z else 0 := by
      intro z
      rw [eq_inv_smul_iff]
      split_ifs <;> ring
    simp only [this]
    rw [tsum_ite_eq]
  · intro g _
    refine summable_of_ne_finset_zero (s := {g⁻¹ • y}) fun z hz => ?_
    rw [Finset.mem_singleton, eq_inv_smul_iff] at hz
    simp [hz]

theorem stepProb_eq (n : ℕ) (x y : Y) :
    stepProb (walkKernel (ν : H → ℝ)) n x y = pp ν n x y := by
  induction n generalizing y with
  | zero =>
    simp [stepProb, pp, Finsupp.single_apply, eq_comm]
  | succ n ih =>
    simp only [stepProb]
    simp_rw [ih]
    rw [pp, pow_succ', Module.End.mul_apply, ← tsum_mul_walkKernel]
    rfl

abbrev dl (x : Y) : Y →₀ ℝ := Finsupp.single x 1

theorem dl_nonneg (x y : Y) : 0 ≤ dl x y := by
  simp only [dl, Finsupp.single_apply]; split_ifs <;> norm_num

theorem pp_add (hsymm : IsSymmetric ν) (a b : ℕ) (x y : Y) :
    pp ν (a + b) x y = ⟪toE ((Q ν ^ a) (dl x)), toE ((Q ν ^ b) (dl y))⟫ := by
  rw [← inner_Qpow hsymm, ← Module.End.mul_apply, ← pow_add, add_comm, pp,
    inner_toE_single]

theorem pp_nonneg (hν : ThompsonAmenability.IsProbability ν) (n : ℕ) (x y : Y) :
    0 ≤ pp ν n x y := Qpow_nonneg hν (dl_nonneg x) n y

theorem pp_symm (hsymm : IsSymmetric ν) (n : ℕ) (x y : Y) : pp ν n x y = pp ν n y x := by
  have h1 := pp_add hsymm 0 n x y
  have h2 := pp_add hsymm n 0 y x
  rw [zero_add] at h1; rw [add_zero] at h2
  rw [h1, h2, real_inner_comm]

theorem pp_le_one (hν : ThompsonAmenability.IsProbability ν) (hsymm : IsSymmetric ν)
    (n : ℕ) (x y : Y) : pp ν n x y ≤ 1 := by
  have h := pp_add hsymm n 0 x y
  rw [add_zero] at h
  rw [h]
  refine (real_inner_le_norm _ _).trans ?_
  simp only [pow_zero, Module.End.one_apply, dl, norm_toE_single, mul_one]
  exact (norm_Qpow_le hν _ n).trans (norm_toE_single x).le

theorem pp_two_mul (hsymm : IsSymmetric ν) (n : ℕ) (x : Y) :
    pp ν (2 * n) x x = ‖toE ((Q ν ^ n) (dl x))‖ ^ 2 := by
  rw [two_mul, pp_add hsymm, real_inner_self_eq_norm_sq]

theorem pp_ck (hν : ThompsonAmenability.IsProbability ν) (hsymm : IsSymmetric ν)
    (a b : ℕ) (x z y : Y) : pp ν a x z * pp ν b z y ≤ pp ν (a + b) x y := by
  rw [pp_add hsymm, inner_toE' _ _ (((Q ν ^ a) (dl x)).support ∪ {z}) Finset.subset_union_left]
  have hz : z ∈ ((Q ν ^ a) (dl x)).support ∪ {z} := Finset.mem_union_right _ (by simp)
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun w =>
    (Q ν ^ a) (dl x) w * toE ((Q ν ^ b) (dl y)) w) (fun w _ => mul_nonneg
      (Qpow_nonneg hν (dl_nonneg x) a w) (by rw [toE_apply]; exact Qpow_nonneg hν (dl_nonneg y) b w))
    hz)
  simp only [toE_apply]
  rw [pp_symm hsymm b z y]
  rfl

theorem pp_one_ge (hν : ThompsonAmenability.IsProbability ν) (s : H) (x : Y) :
    ν s ≤ pp ν 1 x (s • x) := by
  rw [pp, pow_one, Q_apply]
  by_cases hs : s ∈ ν.support
  · refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun g =>
      ν g * dl x (g⁻¹ • s • x)) (fun g _ => mul_nonneg (hν.1 g) (dl_nonneg _ _)) hs)
    simp [dl]
  · rw [Finsupp.notMem_support_iff.mp hs]
    exact Finset.sum_nonneg fun g _ => mul_nonneg (hν.1 g) (dl_nonneg _ _)

theorem pp_zero_self (x : Y) : pp ν 0 x x = 1 := by simp [pp]

theorem exists_pp_pos (hν : ThompsonAmenability.IsProbability ν) (hsymm : IsSymmetric ν)
    (hnd : IsNondegenerate ν) (h : H) : ∀ y : Y, ∃ k, 0 < pp ν k y (h • y) := by
  have hmem : h ∈ Subgroup.closure (ν.support : Set H) := hnd ▸ Subgroup.mem_top h
  induction hmem using Subgroup.closure_induction with
  | mem s hs =>
    intro y
    refine ⟨1, lt_of_lt_of_le ?_ (pp_one_ge hν s y)⟩
    exact lt_of_le_of_ne (hν.1 s) (Ne.symm (Finsupp.mem_support_iff.mp hs))
  | one => intro y; exact ⟨0, by rw [one_smul, pp_zero_self]; norm_num⟩
  | mul g k _ _ hg hk =>
    intro y
    obtain ⟨a, ha⟩ := hk y
    obtain ⟨b, hb⟩ := hg (k • y)
    refine ⟨a + b, lt_of_lt_of_le (mul_pos ha hb) ?_⟩
    rw [mul_smul]
    exact pp_ck hν hsymm a b y (k • y) (g • k • y)
  | inv g _ hg =>
    intro y
    obtain ⟨a, ha⟩ := hg (g⁻¹ • y)
    rw [smul_inv_smul, pp_symm hsymm] at ha
    exact ⟨a, ha⟩

/-- Transfer of return probabilities from `x` to `y₀`. -/
theorem exists_transfer (hν : ThompsonAmenability.IsProbability ν) (hsymm : IsSymmetric ν)
    (hnd : IsNondegenerate ν) [MulAction.IsPretransitive H Y] (y₀ x : Y) :
    ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ n, c * pp ν (2 * n) x x ≤ pp ν (2 * n + 2 * k) y₀ y₀ := by
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq H y₀ x
  obtain ⟨k, hk⟩ := exists_pp_pos hν hsymm hnd h y₀
  refine ⟨k, pp ν k y₀ (h • y₀) * pp ν k (h • y₀) y₀, mul_pos hk (by rwa [pp_symm hsymm]),
    fun n => ?_⟩
  have h1 := pp_ck hν hsymm k (2 * n) y₀ (h • y₀) (h • y₀)
  have h2 := pp_ck hν hsymm (k + 2 * n) k y₀ (h • y₀) y₀
  have e : k + 2 * n + k = 2 * n + 2 * k := by ring
  rw [e] at h2
  have hk' : 0 ≤ pp ν k (h • y₀) y₀ := pp_nonneg hν _ _ _
  calc pp ν k y₀ (h • y₀) * pp ν k (h • y₀) y₀ * pp ν (2 * n) (h • y₀) (h • y₀)
      = pp ν k y₀ (h • y₀) * pp ν (2 * n) (h • y₀) (h • y₀) * pp ν k (h • y₀) y₀ := by ring
    _ ≤ pp ν (k + 2 * n) y₀ (h • y₀) * pp ν k (h • y₀) y₀ :=
        mul_le_mul_of_nonneg_right h1 hk'
    _ ≤ _ := h2

/-! ## Log-convexity -/

theorem logconv_step (hsymm : IsSymmetric ν) (g : Y →₀ ℝ) (k : ℕ) :
    ‖toE ((Q ν ^ (k + 1)) g)‖ ^ 2 ≤ ‖toE ((Q ν ^ k) g)‖ * ‖toE ((Q ν ^ (k + 2)) g)‖ := by
  rw [← real_inner_self_eq_norm_sq]
  have : ⟪toE ((Q ν ^ (k + 1)) g), toE ((Q ν ^ (k + 1)) g)⟫ =
      ⟪toE ((Q ν ^ k) g), toE ((Q ν ^ (k + 2)) g)⟫ := by
    have e1 : (Q ν ^ (k + 1)) g = Q ν ((Q ν ^ k) g) := by rw [pow_succ']; rfl
    have e2 : (Q ν ^ (k + 2)) g = Q ν ((Q ν ^ (k + 1)) g) := by rw [pow_succ' _ (k + 1)]; rfl
    rw [e2, e1, inner_Q hsymm]
  rw [this]
  exact real_inner_le_norm _ _

theorem logconv (hsymm : IsSymmetric ν) (g : Y →₀ ℝ) (n : ℕ) :
    ‖toE ((Q ν ^ 1) g)‖ ^ n * ‖toE ((Q ν ^ 0) g)‖ ≤
      ‖toE ((Q ν ^ 0) g)‖ ^ n * ‖toE ((Q ν ^ n) g)‖ := by
  set b : ℕ → ℝ := fun k => ‖toE ((Q ν ^ k) g)‖ with hb
  have hb0 : ∀ k, 0 ≤ b k := fun k => norm_nonneg _
  have step : ∀ k, b 1 * b k ≤ b 0 * b (k + 1) := by
    intro k
    induction k with
    | zero => rw [mul_comm]
    | succ k ih =>
      have hlc : b (k + 1) ^ 2 ≤ b k * b (k + 2) := logconv_step hsymm g k
      rcases (hb0 (k + 1)).eq_or_lt with h0 | hpos
      · rw [← h0, mul_zero]; exact mul_nonneg (hb0 0) (hb0 _)
      · refine le_of_mul_le_mul_right ?_ hpos
        calc b 1 * b (k + 1) * b (k + 1) = b 1 * b (k + 1) ^ 2 := by ring
          _ ≤ b 1 * (b k * b (k + 2)) := mul_le_mul_of_nonneg_left hlc (hb0 1)
          _ = (b 1 * b k) * b (k + 2) := by ring
          _ ≤ (b 0 * b (k + 1)) * b (k + 2) := mul_le_mul_of_nonneg_right ih (hb0 _)
          _ = b 0 * b (k + 1 + 1) * b (k + 1) := by ring
  show b 1 ^ n * b 0 ≤ b 0 ^ n * b n
  induction n with
  | zero => simp
  | succ n ih =>
    calc b 1 ^ (n + 1) * b 0 = b 1 * (b 1 ^ n * b 0) := by ring
      _ ≤ b 1 * (b 0 ^ n * b n) := mul_le_mul_of_nonneg_left ih (hb0 1)
      _ = b 0 ^ n * (b 1 * b n) := by ring
      _ ≤ b 0 ^ n * (b 0 * b (n + 1)) := mul_le_mul_of_nonneg_left (step n) (pow_nonneg (hb0 0) n)
      _ = b 0 ^ (n + 1) * b (n + 1) := by ring


/-! ## `limsup < 1` gives a contraction -/

theorem real_aux {b0 b1 r C : ℝ} {B : ℕ → ℝ} (hr : 0 < r) (hb0 : 0 ≤ b0) (hb10 : b1 ≤ b0)
    (hlc : ∀ n : ℕ, b1 ^ n * b0 ≤ b0 ^ n * B n) (hB : ∀ᶠ n in Filter.atTop, B n ≤ C * r ^ n) :
    b1 ≤ r * b0 := by
  by_contra hcon
  replace hcon := not_le.mp hcon
  have hb0' : 0 < b0 := by
    rcases hb0.eq_or_lt with h | h
    · rw [← h] at hcon hb10; linarith
    · exact h
  have hrb : 0 < r * b0 := mul_pos hr hb0'
  set t := b1 / (r * b0) with ht
  have ht1 : 1 < t := by rw [ht, one_lt_div hrb]; exact hcon
  obtain ⟨n, hn1, hn2⟩ := (hB.and ((tendsto_pow_atTop_atTop_of_one_lt ht1).eventually_gt_atTop
    (C / b0))).exists
  have e : b1 ^ n = t ^ n * (r * b0) ^ n := by
    rw [← mul_pow, ht, div_mul_cancel₀ _ (ne_of_gt hrb)]
  have hpos : 0 < r ^ n * b0 ^ n := mul_pos (pow_pos hr n) (pow_pos hb0' n)
  have key : t ^ n * b0 * (r ^ n * b0 ^ n) ≤ C * (r ^ n * b0 ^ n) := by
    calc t ^ n * b0 * (r ^ n * b0 ^ n) = b1 ^ n * b0 := by rw [e, mul_pow]; ring
      _ ≤ b0 ^ n * B n := hlc n
      _ ≤ b0 ^ n * (C * r ^ n) := mul_le_mul_of_nonneg_left hn1 (pow_nonneg hb0 n)
      _ = C * (r ^ n * b0 ^ n) := by ring
  have k2 := le_of_mul_le_mul_right key hpos
  have k3 := (div_lt_iff₀ hb0').1 hn2
  linarith

theorem contraction (hν : ThompsonAmenability.IsProbability ν) (hsymm : IsSymmetric ν)
    (hnd : IsNondegenerate ν) [MulAction.IsPretransitive H Y] (y₀ : Y) {r : ℝ} (hr : 0 < r)
    (hρ : ∀ᶠ m in Filter.atTop, pp ν m y₀ y₀ ≤ r ^ m) (f : Y →₀ ℝ) :
    ‖toE (Q ν f)‖ ≤ r * ‖toE f‖ := by
  have ha : ∀ x : Y, ∃ C : ℝ, ∀ᶠ n in Filter.atTop, ‖toE ((Q ν ^ n) (dl x))‖ ≤ C * r ^ n := by
    intro x
    obtain ⟨k, c, hc, htr⟩ := exists_transfer hν hsymm hnd y₀ x
    have ht : Filter.Tendsto (fun n : ℕ => 2 * n + 2 * k) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by omega⟩
    refine ⟨Real.sqrt (r ^ (2 * k) / c), (ht.eventually hρ).mono fun n hn => ?_⟩
    have h1 : ‖toE ((Q ν ^ n) (dl x))‖ ^ 2 ≤ (r ^ (2 * k) / c) * (r ^ n) ^ 2 := by
      rw [← pp_two_mul hsymm, div_mul_eq_mul_div, le_div_iff₀ hc]
      calc pp ν (2 * n) x x * c = c * pp ν (2 * n) x x := by ring
        _ ≤ pp ν (2 * n + 2 * k) y₀ y₀ := htr n
        _ ≤ r ^ (2 * n + 2 * k) := hn
        _ = r ^ (2 * k) * (r ^ n) ^ 2 := by ring
    calc ‖toE ((Q ν ^ n) (dl x))‖ = Real.sqrt (‖toE ((Q ν ^ n) (dl x))‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((r ^ (2 * k) / c) * (r ^ n) ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt (r ^ (2 * k) / c) * r ^ n := by
          rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (pow_nonneg hr.le n)]
  choose C hC using ha
  have hb : ∀ᶠ n in Filter.atTop,
      ‖toE ((Q ν ^ n) f)‖ ≤ (∑ x ∈ f.support, |f x| * C x) * r ^ n := by
    filter_upwards [(Filter.eventually_all_finset f.support).2 fun x _ => hC x] with n hn
    have hf : f = ∑ x ∈ f.support, f x • dl x := by
      conv_lhs => rw [← Finsupp.sum_single f]
      simp [Finsupp.sum, dl]
    conv_lhs => rw [hf]
    rw [map_sum, map_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
    rw [map_smul, map_smul, norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hn x hx) (abs_nonneg _)
  have hlc := logconv hsymm f
  simp only [pow_one, pow_zero, Module.End.one_apply] at hlc
  exact real_aux hr (norm_nonneg _) (norm_Q_le hν f) hlc hb


/-! ## A contraction forbids an invariant mean (expansion, Hall, paradox) -/

variable (ν) in
def Bk : ℕ → Finset H
  | 0 => {1}
  | k + 1 => ν.support * Bk k

theorem support_Qpow_dl (k : ℕ) (x : Y) :
    ∀ z, (Q ν ^ k) (dl x) z ≠ 0 → ∃ b ∈ Bk ν k, b • x = z := by
  induction k with
  | zero =>
    intro z hz
    refine ⟨1, by simp [Bk], ?_⟩
    simp only [pow_zero, Module.End.one_apply, dl, Finsupp.single_apply] at hz
    split_ifs at hz with h
    · simp [h]
    · exact absurd rfl hz
  | succ k ih =>
    intro z hz
    rw [pow_succ', Module.End.mul_apply, Q_apply] at hz
    obtain ⟨g, hg, hgz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨b, hb, hbx⟩ := ih _ (right_ne_zero_of_mul hgz)
    refine ⟨g * b, Finset.mul_mem_mul hg hb, ?_⟩
    rw [mul_smul, hbx, smul_inv_smul]

variable (Y) in
def mass : (Y →₀ ℝ) →ₗ[ℝ] ℝ := Finsupp.linearCombination ℝ (fun _ : Y => (1 : ℝ))

omit [Group H] [MulAction H Y] in
theorem mass_apply (f : Y →₀ ℝ) : mass Y f = ∑ y ∈ f.support, f y := by
  simp [mass, Finsupp.linearCombination_apply, Finsupp.sum]

theorem mass_tr (h : H) (f : Y →₀ ℝ) : mass Y (tr h f) = mass Y f := by
  simp only [mass, tr, Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain]
  rfl

theorem mass_Q (hν : ThompsonAmenability.IsProbability ν) (f : Y →₀ ℝ) :
    mass Y (Q ν f) = mass Y f := by
  rw [Q_eq, map_sum]
  simp only [map_smul, mass_tr, smul_eq_mul]
  rw [← Finset.sum_mul, sum_nu hν, one_mul]

theorem mass_Qpow_dl (hν : ThompsonAmenability.IsProbability ν) (k : ℕ) (x : Y) :
    mass Y ((Q ν ^ k) (dl x)) = 1 := by
  induction k with
  | zero => simp [mass, dl]
  | succ k ih => rw [pow_succ', Module.End.mul_apply, mass_Q hν, ih]

omit [Group H] [MulAction H Y] in
def ind (G : Finset Y) : Y →₀ ℝ := ∑ y ∈ G, dl y

omit [Group H] [MulAction H Y] in
theorem ind_apply (G : Finset Y) (z : Y) : ind G z = if z ∈ G then 1 else 0 := by
  simp [ind, Finsupp.finsetSum_apply, dl, Finsupp.single_apply]

omit [Group H] [MulAction H Y] in
theorem support_ind (G : Finset Y) : (ind G).support ⊆ G := by
  intro z hz
  rw [Finsupp.mem_support_iff, ind_apply] at hz
  by_contra h; simp [h] at hz

omit [Group H] [MulAction H Y] in
theorem norm_toE_ind (G : Finset Y) : ‖toE (ind G)‖ = Real.sqrt G.card := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_toE _ G (support_ind G)]
  congr 1
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  simp [ind_apply, hz]

omit [Group H] [MulAction H Y] in
theorem mass_eq_inner (g : Y →₀ ℝ) (G : Finset Y) (hg : g.support ⊆ G) :
    mass Y g = ⟪toE g, toE (ind G)⟫ := by
  rw [mass_apply, inner_toE]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [toE_apply, ind_apply, if_pos (hg hz), mul_one]

theorem norm_Qpow_contr {r : ℝ} (hr : 0 ≤ r) (hcon : ∀ f : Y →₀ ℝ, ‖toE (Q ν f)‖ ≤ r * ‖toE f‖)
    (k : ℕ) (f : Y →₀ ℝ) : ‖toE ((Q ν ^ k) f)‖ ≤ r ^ k * ‖toE f‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', mul_assoc]
    exact (hcon _).trans (mul_le_mul_of_nonneg_left ih hr)

theorem expansion (hν : ThompsonAmenability.IsProbability ν) {r : ℝ} (hr : 0 ≤ r)
    (hcon : ∀ f : Y →₀ ℝ, ‖toE (Q ν f)‖ ≤ r * ‖toE f‖) (k : ℕ) (hk : r ^ k ≤ 1 / 2)
    (F : Finset Y) : 2 * F.card ≤ (F.biUnion fun x => (Bk ν k).image (· • x)).card := by
  set G := F.biUnion fun x => (Bk ν k).image (· • x) with hG
  have hsupp : ((Q ν ^ k) (ind F)).support ⊆ G := by
    intro z hz
    rw [Finsupp.mem_support_iff, ind, map_sum, Finsupp.finsetSum_apply] at hz
    obtain ⟨x, hx, hxz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨b, hb, hbz⟩ := support_Qpow_dl k x z hxz
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨b, hb, hbz⟩⟩
  have hmass : (F.card : ℝ) = mass Y ((Q ν ^ k) (ind F)) := by
    rw [ind, map_sum, map_sum]
    simp [mass_Qpow_dl hν]
  have h1 : (F.card : ℝ) ≤ r ^ k * Real.sqrt F.card * Real.sqrt G.card := by
    conv_lhs => rw [hmass, mass_eq_inner _ G hsupp]
    refine (real_inner_le_norm _ _).trans ?_
    rw [norm_toE_ind, ← norm_toE_ind F]
    exact mul_le_mul_of_nonneg_right (norm_Qpow_contr hr hcon k _) (Real.sqrt_nonneg _)
  rcases Nat.eq_zero_or_pos F.card with h0 | hpos
  · rw [h0]; simp
  · have ha : 0 < Real.sqrt F.card := Real.sqrt_pos.mpr (by exact_mod_cast hpos)
    have hFa : (F.card : ℝ) = Real.sqrt F.card * Real.sqrt F.card :=
      (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
    have hGa : (G.card : ℝ) = Real.sqrt G.card * Real.sqrt G.card :=
      (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
    have h2 : Real.sqrt F.card ≤ r ^ k * Real.sqrt G.card := by
      refine le_of_mul_le_mul_left ?_ ha
      calc Real.sqrt F.card * Real.sqrt F.card = F.card := hFa.symm
        _ ≤ _ := h1
        _ = Real.sqrt F.card * (r ^ k * Real.sqrt G.card) := by ring
    have h3 : Real.sqrt F.card ≤ 1 / 2 * Real.sqrt G.card :=
      h2.trans (mul_le_mul_of_nonneg_right hk (Real.sqrt_nonneg _))
    have h4 : (F.card : ℝ) ≤ 1 / 4 * G.card := by
      rw [hFa, hGa]
      nlinarith [Real.sqrt_nonneg (F.card : ℝ)]
    have h5 : (2 * F.card : ℝ) ≤ G.card := by
      nlinarith [(Nat.cast_nonneg G.card : (0 : ℝ) ≤ G.card)]
    exact_mod_cast h5

theorem fa_biUnion {ι : Type*} {m : Set Y → ℝ≥0∞} (hm : Garrido.IsFinitelyAdditiveMeasure m)
    (A : ι → Set Y) (s : Finset ι) (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j)) :
    m (⋃ i ∈ s, A i) = ∑ i ∈ s, m (A i) := by
  induction s using Finset.induction_on with
  | empty => simp [hm.1]
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    rw [hm.2 _ _ ?_, ih fun i hi j hj hij =>
      hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij]
    rw [Set.disjoint_iUnion₂_right]
    intro i hi
    exact hd a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
      (fun h => ha (h ▸ hi))

omit [Group H] [MulAction H Y] in
theorem fa_le_univ {m : Set Y → ℝ≥0∞} (hm : Garrido.IsFinitelyAdditiveMeasure m) (A : Set Y) :
    m A ≤ m Set.univ := by
  have := hm.2 A Aᶜ disjoint_compl_right
  rw [Set.union_compl_self] at this
  rw [this]; exact le_self_add

theorem not_amenable_of_contraction (hν : ThompsonAmenability.IsProbability ν) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hcon : ∀ f : Y →₀ ℝ, ‖toE (Q ν f)‖ ≤ r * ‖toE f‖) :
    ¬ IsAmenableAction H Y := by
  rintro ⟨m, hm, hm1, hinv⟩
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) hr1
  set B := Bk ν k
  let t : Y × Bool → Finset Y := fun i => B.image (· • i.1)
  have hhall : ∀ s : Finset (Y × Bool), s.card ≤ (s.biUnion t).card := by
    intro s
    set F := s.image Prod.fst
    have hexp := expansion hν hr hcon k hk.le F
    have hsub : s ⊆ F ×ˢ (Finset.univ : Finset Bool) := by
      intro i hi
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hi, Finset.mem_univ _⟩
    have hc1 : s.card ≤ 2 * F.card := by
      have := Finset.card_le_card hsub
      rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm] at this
      exact this
    have hc2 : (F.biUnion fun x => B.image (· • x)) ⊆ s.biUnion t := by
      intro z hz
      obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_biUnion.mpr ⟨i, hi, hzx⟩
    exact hc1.trans (hexp.trans (Finset.card_le_card hc2))
  obtain ⟨φ, hφinj, hφ⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hhall
  have hβ : ∀ i : Y × Bool, ∃ b ∈ B, b • i.1 = φ i := fun i => Finset.mem_image.mp (hφ i)
  choose β hβB hβ using hβ
  let Ev : H → Bool → Set Y := fun b i => {y | β (y, i) = b}
  have hrow : ∀ i : Bool, ∑ b ∈ B, m (Ev b i) = 1 := by
    intro i
    rw [← fa_biUnion hm (fun b => Ev b i) B ?_, ← hm1]
    · congr 1
      ext y
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact ⟨β (y, i), hβB _, rfl⟩
    · intro b _ b' _ hbb'
      rw [Set.disjoint_left]
      intro y hy hy'
      exact hbb' (hy.symm.trans hy')
  have hdisj : ∀ p ∈ B ×ˢ (Finset.univ : Finset Bool), ∀ q ∈ B ×ˢ (Finset.univ : Finset Bool),
      p ≠ q → Disjoint (p.1 • Ev p.1 p.2) (q.1 • Ev q.1 q.2) := by
    rintro ⟨b, i⟩ _ ⟨b', i'⟩ _ hne
    rw [Set.disjoint_left]
    rintro z ⟨y, hy, rfl⟩ ⟨y', hy', hyy⟩
    have e1 : φ (y, i) = b • y := by rw [← hβ]; simp only at hy; rw [hy]
    have e2 : φ (y', i') = b' • y' := by rw [← hβ]; simp only at hy'; rw [hy']
    have := hφinj (e1.trans (hyy.symm.trans e2.symm) |>.symm)
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    apply hne
    simp only at hy hy'
    rw [← hy, ← hy']
  have htot := fa_biUnion hm (fun p : H × Bool => p.1 • Ev p.1 p.2) _ hdisj
  have hle := fa_le_univ hm (⋃ p ∈ B ×ˢ (Finset.univ : Finset Bool), p.1 • Ev p.1 p.2)
  rw [htot, hm1, Finset.sum_product_right] at hle
  have hinv' : ∀ (g : H) (A : Set Y), m (g • A) = m A := hinv
  simp only [hinv', hrow] at hle
  norm_num at hle


/-! ## `limsup = 1` gives almost invariant vectors -/

theorem sum_sum_eq (hν : ThompsonAmenability.IsProbability ν) (f : Y →₀ ℝ) :
    ∑ s ∈ ν.support, ∑ t ∈ ν.support, ν s * ν t * ‖toE (tr s f) - toE (tr t f)‖ ^ 2 =
      2 * ‖toE f‖ ^ 2 - 2 * ‖toE (Q ν f)‖ ^ 2 := by
  have hI : ‖toE (Q ν f)‖ ^ 2 = ∑ s ∈ ν.support, ∑ t ∈ ν.support,
      ν s * ν t * ⟪toE (tr s f), toE (tr t f)⟫ := by
    rw [← real_inner_self_eq_norm_sq, toE_Q, sum_inner]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]; ring
  have hD : ∀ s t, ν s * ν t * ‖toE (tr s f) - toE (tr t f)‖ ^ 2 =
      2 * ‖toE f‖ ^ 2 * (ν s * ν t) - 2 * (ν s * ν t * ⟪toE (tr s f), toE (tr t f)⟫) := by
    intro s t
    rw [norm_sub_sq_real, norm_tr, norm_tr]; ring
  simp_rw [hD, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hI, sum_nu hν]
  simp only [mul_one, sum_nu hν]

theorem pair_bound (hν : ThompsonAmenability.IsProbability ν) (f : Y →₀ ℝ) {s t : H}
    (hs : s ∈ ν.support) (ht : t ∈ ν.support) :
    ν s * ν t * ‖toE (tr s f) - toE (tr t f)‖ ^ 2 ≤
      2 * ‖toE f‖ ^ 2 - 2 * ‖toE (Q ν f)‖ ^ 2 := by
  rw [← sum_sum_eq hν]
  have hnn : ∀ s' t', 0 ≤ ν s' * ν t' * ‖toE (tr s' f) - toE (tr t' f)‖ ^ 2 :=
    fun s' t' => mul_nonneg (mul_nonneg (hν.1 _) (hν.1 _)) (sq_nonneg _)
  refine le_trans ?_ (Finset.single_le_sum (f := fun s' => ∑ t' ∈ ν.support,
    ν s' * ν t' * ‖toE (tr s' f) - toE (tr t' f)‖ ^ 2)
    (fun s' _ => Finset.sum_nonneg fun t' _ => hnn s' t') hs)
  exact Finset.single_le_sum (f := fun t' =>
    ν s * ν t' * ‖toE (tr s f) - toE (tr t' f)‖ ^ 2) (fun t' _ => hnn s t') ht

theorem exists_almost_inv (hν : ThompsonAmenability.IsProbability ν) (hsymm : IsSymmetric ν)
    (hratio : ∀ L : ℝ, 0 ≤ L → L < 1 →
      ∃ f : Y →₀ ℝ, (∀ y, 0 ≤ f y) ∧ L * ‖toE f‖ < ‖toE (Q ν f)‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : Y →₀ ℝ, ‖toE w‖ = 1 ∧ ∀ s ∈ ν.support, ‖toE (tr s w) - toE w‖ ≤ ε := by
  have hne : ν.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := sum_nu hν
    rw [h, Finset.sum_empty] at this
    norm_num at this
  obtain ⟨s₀, hs₀⟩ := hne
  obtain ⟨s₁, hs₁, hmin⟩ := ν.support.exists_min_image ν ⟨s₀, hs₀⟩
  set c := ν s₁
  have hc : 0 < c := lt_of_le_of_ne (hν.1 s₁) (Ne.symm (Finsupp.mem_support_iff.mp hs₁))
  set ε' := ε / 2 with hε'
  have hε'0 : 0 < ε' := by positivity
  set η := min (1 / 2 : ℝ) (c ^ 2 * ε' ^ 2 / 4) with hη
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 / 2 := min_le_left _ _
  have hη2 : η ≤ c ^ 2 * ε' ^ 2 / 4 := min_le_right _ _
  obtain ⟨f, hf0, hfL⟩ := hratio (1 - η) (by linarith) (by linarith)
  set b := ‖toE f‖ with hb
  have hQb : ‖toE (Q ν f)‖ ≤ b := norm_Q_le hν f
  have hbpos : 0 < b := by
    rcases (norm_nonneg (toE f)).eq_or_lt with h | h
    · have hb0 : b = 0 := by rw [hb, ← h]
      rw [hb0] at hfL hQb; linarith [norm_nonneg (toE (Q ν f))]
    · exact h
  have hL0 : 0 ≤ (1 - η) * b := mul_nonneg (by linarith) hbpos.le
  have hQsq : ((1 - η) * b) ^ 2 ≤ ‖toE (Q ν f)‖ ^ 2 := pow_le_pow_left₀ hL0 hfL.le 2
  have hpair : ∀ s ∈ ν.support, ∀ t ∈ ν.support, ‖toE (tr s f) - toE (tr t f)‖ ≤ ε' * b := by
    intro s hs t ht
    have h1 := pair_bound hν f hs ht
    have hcs : c ≤ ν s := hmin s hs
    have hct : c ≤ ν t := hmin t ht
    have hcc : c ^ 2 ≤ ν s * ν t := by
      rw [sq]; exact mul_le_mul hcs hct hc.le (hν.1 s)
    have h2 : c ^ 2 * ‖toE (tr s f) - toE (tr t f)‖ ^ 2 ≤ c ^ 2 * (ε' * b) ^ 2 := by
      calc c ^ 2 * ‖toE (tr s f) - toE (tr t f)‖ ^ 2
          ≤ ν s * ν t * ‖toE (tr s f) - toE (tr t f)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hcc (sq_nonneg _)
        _ ≤ 2 * b ^ 2 - 2 * ‖toE (Q ν f)‖ ^ 2 := h1
        _ ≤ 2 * b ^ 2 - 2 * ((1 - η) * b) ^ 2 := by linarith
        _ = (4 * η - 2 * η ^ 2) * b ^ 2 := by ring
        _ ≤ (c ^ 2 * ε' ^ 2) * b ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            nlinarith [sq_nonneg η]
        _ = c ^ 2 * (ε' * b) ^ 2 := by ring
    have h3 := le_of_mul_le_mul_left h2 (by positivity)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 h3
  set w₀ := f + tr s₀ f with hw₀
  have hw₀b : b ≤ ‖toE w₀‖ := by
    have hin : 0 ≤ ⟪toE f, toE (tr s₀ f)⟫ := by
      rw [inner_toE]
      exact Finset.sum_nonneg fun y _ => mul_nonneg (hf0 y) (by
        rw [toE_apply]; exact tr_nonneg s₀ hf0 y)
    have hsq : b ^ 2 ≤ ‖toE w₀‖ ^ 2 := by
      rw [hw₀, map_add, norm_add_sq_real, norm_tr]
      nlinarith [sq_nonneg b]
    exact (pow_le_pow_iff_left₀ hbpos.le (norm_nonneg _) (by norm_num)).1 hsq
  have hw₀pos : 0 < ‖toE w₀‖ := lt_of_lt_of_le hbpos hw₀b
  have hw₀inv : ∀ s ∈ ν.support, ‖toE (tr s w₀) - toE w₀‖ ≤ 2 * ε' * b := by
    intro s hs
    have hsinv : s⁻¹ ∈ ν.support := by
      rw [Finsupp.mem_support_iff, hsymm s]; exact Finsupp.mem_support_iff.mp hs
    have e : toE (tr s w₀) - toE w₀ = (toE (tr s f) - toE (tr s₀ f)) +
        toE (tr s (tr s₀ f - tr s⁻¹ f)) := by
      rw [hw₀, map_sub, tr_tr_inv]
      simp only [map_add, map_sub]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_tr, map_sub]
    linarith [hpair s hs s₀ hs₀, hpair s₀ hs₀ s⁻¹ hsinv]
  refine ⟨‖toE w₀‖⁻¹ • w₀, ?_, fun s hs => ?_⟩
  · rw [map_smul, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw₀pos.ne']
  · rw [map_smul, map_smul, map_smul, ← smul_sub, norm_smul, norm_inv, norm_norm]
    rw [inv_mul_le_iff₀ hw₀pos]
    calc ‖toE (tr s w₀) - toE w₀‖ ≤ 2 * ε' * b := hw₀inv s hs
      _ ≤ 2 * ε' * ‖toE w₀‖ := mul_le_mul_of_nonneg_left hw₀b (by positivity)
      _ = ‖toE w₀‖ * ε := by rw [hε']; ring

/-! ## Almost invariant vectors give an invariant mean -/

omit [Group H] [MulAction H Y] in
def sqm (u : Y →₀ ℝ) (A : Set Y) : ℝ := ∑' y, A.indicator (fun y => u y ^ 2) y

omit [Group H] [MulAction H Y] in
theorem sqm_eq_sum (u : Y →₀ ℝ) (A : Set Y) (T : Finset Y) (hT : u.support ⊆ T) :
    sqm u A = ∑ y ∈ T, A.indicator (fun y => u y ^ 2) y := by
  unfold sqm
  refine tsum_eq_sum fun y hy => ?_
  have : u y = 0 := Finsupp.notMem_support_iff.mp fun h => hy (hT h)
  simp [Set.indicator_apply, this]

omit [Group H] [MulAction H Y] in
theorem sqm_nonneg (u : Y →₀ ℝ) (A : Set Y) : 0 ≤ sqm u A :=
  tsum_nonneg fun y => Set.indicator_nonneg (fun y _ => sq_nonneg (u y)) y

omit [Group H] [MulAction H Y] in
theorem sqm_univ (u : Y →₀ ℝ) : sqm u Set.univ = ‖toE u‖ ^ 2 := by
  rw [sqm_eq_sum u _ u.support subset_rfl, norm_sq_toE u u.support subset_rfl]
  simp

omit [Group H] [MulAction H Y] in
theorem sqm_le (u : Y →₀ ℝ) (A : Set Y) : sqm u A ≤ ‖toE u‖ ^ 2 := by
  rw [← sqm_univ, sqm_eq_sum u _ u.support subset_rfl, sqm_eq_sum u _ u.support subset_rfl]
  exact Finset.sum_le_sum fun y _ => Set.indicator_le_indicator_of_subset (Set.subset_univ _)
    (fun y => sq_nonneg (u y)) y

omit [Group H] [MulAction H Y] in
theorem sqm_empty (u : Y →₀ ℝ) : sqm u ∅ = 0 := by simp [sqm]

omit [Group H] [MulAction H Y] in
theorem sqm_union (u : Y →₀ ℝ) {A B : Set Y} (hd : Disjoint A B) :
    sqm u (A ∪ B) = sqm u A + sqm u B := by
  rw [sqm_eq_sum u _ u.support subset_rfl, sqm_eq_sum u _ u.support subset_rfl,
    sqm_eq_sum u _ u.support subset_rfl, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Set.indicator_union_of_disjoint hd]

theorem sqm_smul (u : Y →₀ ℝ) (h : H) (A : Set Y) : sqm u (h • A) = sqm (tr h⁻¹ u) A := by
  unfold sqm
  rw [← (MulAction.toPerm h : Equiv.Perm Y).tsum_eq]
  refine tsum_congr fun z => ?_
  simp only [MulAction.toPerm_apply, tr_apply, inv_inv]
  by_cases hz : z ∈ A
  · rw [Set.indicator_of_mem (Set.smul_mem_smul_set hz), Set.indicator_of_mem hz]
  · rw [Set.indicator_of_notMem (fun h' => hz (Set.smul_mem_smul_set_iff.mp h')),
      Set.indicator_of_notMem hz]

omit [Group H] [MulAction H Y] in
theorem sqm_diff (u v : Y →₀ ℝ) (A : Set Y) :
    |sqm u A - sqm v A| ≤ ‖toE u - toE v‖ * ‖toE u + toE v‖ := by
  set T := u.support ∪ v.support
  rw [sqm_eq_sum u A T Finset.subset_union_left, sqm_eq_sum v A T Finset.subset_union_right,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ y ∈ T, |A.indicator (fun y => u y ^ 2) y - A.indicator (fun y => v y ^ 2) y| ≤
      |u y - v y| * |u y + v y| := by
    intro y _
    rw [← abs_mul]
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      exact le_of_eq (by ring_nf)
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, sub_self, abs_zero]
      exact abs_nonneg _
  refine (Finset.sum_le_sum h1).trans ?_
  refine (Real.sum_mul_le_sqrt_mul_sqrt T _ _).trans (le_of_eq ?_)
  have hsub : (u - v).support ⊆ T := Finsupp.support_sub
  have hadd : (u + v).support ⊆ T := Finsupp.support_add
  rw [← map_sub, ← map_add, ← Real.sqrt_sq (norm_nonneg (toE (u - v))),
    ← Real.sqrt_sq (norm_nonneg (toE (u + v))), norm_sq_toE _ T hsub, norm_sq_toE _ T hadd]
  simp [sq_abs]

theorem tendsto_tr (hnd : IsNondegenerate ν) (w : ℕ → Y →₀ ℝ)
    (hw : ∀ n, ∀ s ∈ ν.support, ‖toE (tr s (w n)) - toE (w n)‖ ≤ 1 / ((n : ℝ) + 1)) (h : H) :
    Filter.Tendsto (fun n => ‖toE (tr h (w n)) - toE (w n)‖) Filter.atTop (nhds 0) := by
  have hmem : h ∈ Subgroup.closure (ν.support : Set H) := hnd ▸ Subgroup.mem_top h
  induction hmem using Subgroup.closure_induction with
  | mem s hs =>
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => hw n s hs)
      tendsto_one_div_add_atTop_nhds_zero_nat
  | one => simp [tr_one]
  | mul g k _ _ hg hk =>
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hk.add hg)
    have e : toE (tr (g * k) (w n)) - toE (w n) =
        toE (tr g (tr k (w n) - w n)) + (toE (tr g (w n)) - toE (w n)) := by
      rw [tr_mul, map_sub, map_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_tr, map_sub]
  | inv g _ hg =>
    refine hg.congr fun n => ?_
    symm
    rw [← map_sub, ← norm_tr g, map_sub, tr_tr_inv, map_sub, norm_sub_rev]

theorem amenable_of_almost_inv (hnd : IsNondegenerate ν) (w : ℕ → Y →₀ ℝ)
    (hw1 : ∀ n, ‖toE (w n)‖ = 1)
    (hw : ∀ n, ∀ s ∈ ν.support, ‖toE (tr s (w n)) - toE (w n)‖ ≤ 1 / ((n : ℝ) + 1)) :
    IsAmenableAction H Y := by
  let p : ℕ → Set Y → ℝ := fun n A => sqm (w n) A
  have hp01 : ∀ n A, p n A ∈ Set.Icc (0 : ℝ) 1 := fun n A =>
    ⟨sqm_nonneg _ _, (sqm_le _ _).trans (by rw [hw1]; norm_num)⟩
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hU : (U : Filter ℕ) ≤ Filter.atTop := Ultrafilter.of_le _
  have hex : ∀ A, ∃ L ∈ Set.Icc (0 : ℝ) 1, Filter.Tendsto (fun n => p n A) U (nhds L) := by
    intro A
    obtain ⟨L, hL, hle⟩ := isCompact_Icc.ultrafilter_le_nhds (U.map fun n => p n A) (by
      rw [Ultrafilter.coe_map, Filter.le_principal_iff]
      exact Filter.mem_map.mpr (Filter.univ_mem' fun n => hp01 n A))
    exact ⟨L, hL, by rw [Ultrafilter.coe_map] at hle; exact hle⟩
  choose L hL01 hL using hex
  have huniq : ∀ A (v : ℝ), (∀ n, p n A = v) → L A = v := fun A v hv =>
    tendsto_nhds_unique (hL A) (tendsto_const_nhds.congr fun n => (hv n).symm)
  have hinv : ∀ (h : H) A, L (h • A) = L A := by
    intro h A
    have h1 : Filter.Tendsto (fun n => p n (h • A) - p n A) U (nhds (L (h • A) - L A)) :=
      (hL _).sub (hL A)
    have h2 : Filter.Tendsto (fun n => p n (h • A) - p n A) Filter.atTop (nhds 0) := by
      have ht := tendsto_tr hnd w hw h⁻¹
      rw [tendsto_zero_iff_abs_tendsto_zero]
      refine squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) (by simpa using ht.mul_const 2)
      show |sqm (w n) (h • A) - sqm (w n) A| ≤ _
      rw [sqm_smul]
      refine (sqm_diff _ _ A).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      refine (norm_add_le _ _).trans ?_
      rw [norm_tr, hw1]; norm_num
    have := tendsto_nhds_unique h1 (h2.mono_left hU)
    linarith
  refine ⟨fun A => ENNReal.ofReal (L A), ⟨?_, fun A B hd => ?_⟩, ?_, fun h A => ?_⟩
  · simp only [huniq ∅ 0 fun n => sqm_empty _, ENNReal.ofReal_zero]
  · show ENNReal.ofReal (L (A ∪ B)) = ENNReal.ofReal (L A) + ENNReal.ofReal (L B)
    rw [tendsto_nhds_unique (hL (A ∪ B)) (((hL A).add (hL B)).congr
        fun n => (sqm_union (w n) hd).symm), ENNReal.ofReal_add (hL01 A).1 (hL01 B).1]
  · simp only [huniq Set.univ 1 fun n => by simp [p, sqm_univ, hw1], ENNReal.ofReal_one]
  · simp only [hinv h A]


/-! ## Assembly -/

theorem rpow_le_of_le_pow {a L : ℝ} {n : ℕ} (hn : 1 ≤ n) (ha : 0 ≤ a) (hL : 0 ≤ L)
    (h : a ≤ L ^ n) : a ^ (1 / (n : ℝ)) ≤ L := by
  have hn0 : n ≠ 0 := by omega
  calc a ^ (1 / (n : ℝ)) ≤ (L ^ n) ^ (1 / (n : ℝ)) :=
        Real.rpow_le_rpow ha h (by positivity)
    _ = L := by rw [one_div, Real.pow_rpow_inv_natCast hL hn0]

theorem pow_le_of_rpow_le {a r : ℝ} {n : ℕ} (hn : 1 ≤ n) (ha : 0 ≤ a)
    (h : a ^ (1 / (n : ℝ)) ≤ r) : a ≤ r ^ n := by
  have hn0 : n ≠ 0 := by omega
  calc a = (a ^ (1 / (n : ℝ))) ^ n := by rw [one_div, Real.rpow_inv_natCast_pow ha hn0]
    _ ≤ r ^ n := pow_le_pow_left₀ (Real.rpow_nonneg ha _) h n

end

end Kesten.IETK

namespace Kesten

open IETK in
theorem chk_isAmenableAction_iff_limsup_stepProb_rpow_eq_one {H Y : Type*} [Group H] [MulAction H Y]
    [Group.FG H] [MulAction.IsPretransitive H Y] (ν : H →₀ ℝ)
    (hν : ThompsonAmenability.IsProbability ν) (hsymm : IsSymmetric ν) (hnd : IsNondegenerate ν)
    (y₀ : Y) :
    IsAmenableAction H Y ↔
      Filter.limsup (fun n : ℕ => stepProb (walkKernel (ν : H → ℝ)) n y₀ y₀ ^ (1 / (n : ℝ)))
        Filter.atTop = 1 := by
  simp_rw [stepProb_eq]
  set u : ℕ → ℝ := fun n => pp ν n y₀ y₀ ^ (1 / (n : ℝ)) with hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => Real.rpow_nonneg (pp_nonneg hν n y₀ y₀) _
  have hu1 : ∀ n, u n ≤ 1 := fun n =>
    Real.rpow_le_one (pp_nonneg hν n y₀ y₀) (pp_le_one hν hsymm n y₀ y₀) (by positivity)
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u :=
    Filter.isBoundedUnder_of ⟨1, hu1⟩
  have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop u :=
    Filter.isCoboundedUnder_le_of_le Filter.atTop hu0
  have hle1 : Filter.limsup u Filter.atTop ≤ 1 :=
    Filter.limsup_le_of_le hcobdd (Filter.Eventually.of_forall hu1)
  constructor
  · intro hA
    by_contra hne
    have hlt := lt_of_le_of_ne hle1 hne
    set ρ := Filter.limsup u Filter.atTop
    set r := (max ρ 0 + 1) / 2 with hr
    have hr0 : 0 < r := by rw [hr]; have := le_max_right ρ 0; linarith
    have hr1 : r < 1 := by
      rw [hr]; have : max ρ 0 < 1 := max_lt hlt (by norm_num); linarith
    have hρr : ρ < r := by rw [hr]; have := le_max_left ρ 0; linarith
    have hev := Filter.eventually_lt_of_limsup_lt hρr hbdd
    have hpow : ∀ᶠ m in Filter.atTop, pp ν m y₀ y₀ ≤ r ^ m := by
      filter_upwards [hev, Filter.eventually_ge_atTop 1] with m hm hm1
      exact pow_le_of_rpow_le hm1 (pp_nonneg hν m y₀ y₀) hm.le
    exact not_amenable_of_contraction hν hr0.le hr1
      (contraction hν hsymm hnd y₀ hr0 hpow) hA
  · intro h1
    have hratio : ∀ L : ℝ, 0 ≤ L → L < 1 →
        ∃ f : Y →₀ ℝ, (∀ y, 0 ≤ f y) ∧ L * ‖toE f‖ < ‖toE (Q ν f)‖ := by
      intro L hL0 hL1
      by_contra hno
      have hno' : ∀ n, ‖toE (Q ν ((Q ν ^ n) (dl y₀)))‖ ≤ L * ‖toE ((Q ν ^ n) (dl y₀))‖ :=
        fun n => not_lt.mp fun hlt => hno ⟨_, Qpow_nonneg hν (dl_nonneg y₀) n, hlt⟩
      have hb : ∀ n, ‖toE ((Q ν ^ n) (dl y₀))‖ ≤ L ^ n := by
        intro n
        induction n with
        | zero => simp [dl, norm_toE_single]
        | succ n ih =>
          rw [pow_succ', Module.End.mul_apply, pow_succ']
          exact (hno' n).trans (mul_le_mul_of_nonneg_left ih hL0)
      have hpp : ∀ n, pp ν n y₀ y₀ ≤ L ^ n := by
        intro n
        have h := pp_add hsymm n 0 y₀ y₀
        rw [add_zero] at h
        rw [h]
        refine (real_inner_le_norm _ _).trans ?_
        simp only [pow_zero, Module.End.one_apply, dl, norm_toE_single, mul_one]
        exact hb n
      have hlim : Filter.limsup u Filter.atTop ≤ L := by
        refine Filter.limsup_le_of_le hcobdd ?_
        filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        exact rpow_le_of_le_pow hn (pp_nonneg hν n y₀ y₀) hL0 (hpp n)
      linarith
    have hw := fun n : ℕ => exists_almost_inv hν hsymm hratio
      (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
    choose w hw1 hwinv using hw
    exact amenable_of_almost_inv hnd w hw1 hwinv

end Kesten
end

open IntervalExchange
open Kesten in
theorem solution {H Y : Type*} [Group H] [MulAction H Y]
    [Group.FG H] [MulAction.IsPretransitive H Y] (ν : H →₀ ℝ)
    (hν : ThompsonAmenability.IsProbability ν) (hsymm : IsSymmetric ν) (hnd : IsNondegenerate ν)
    (y₀ : Y) :
    IsAmenableAction H Y ↔
      Filter.limsup (fun n : ℕ => stepProb (walkKernel (ν : H → ℝ)) n y₀ y₀ ^ (1 / (n : ℝ)))
        Filter.atTop = 1 :=
  Kesten.chk_isAmenableAction_iff_limsup_stepProb_rpow_eq_one ν hν hsymm hnd y₀
