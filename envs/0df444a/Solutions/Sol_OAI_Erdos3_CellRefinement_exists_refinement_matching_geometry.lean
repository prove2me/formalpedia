-- Prove2me | solution 1 for OAI.Erdos3.CellRefinement.exists_refinement_matching_geometry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T18:21:46.682599+00:00
-- url     : https://prove2.me/submissions/1047371a-9f3e-4da7-8576-5ce86cab5698

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalizedAverageScaleOrder
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem localizedAverageScale_spec (rank : ℕ) {R epsilon : ℝ}
    (hR : 0 ≤ R) (hepsilon : 0 < epsilon) :
    0 < localizedAverageScale rank R epsilon ∧
      localizedAverageScale rank R epsilon ≤ 1 / (100 * (2 * max rank 1 : ℕ) : ℝ≥0) ∧
      R * (400 * (max rank 1 : ℕ) * (localizedAverageScale rank R epsilon : ℝ)) ≤ epsilon := by
  let d : ℝ := (max rank 1 : ℕ)
  let r : ℝ := min (1 / (200 * d)) (epsilon / (400 * d * (R + 1)))
  have hd : 0 < d := by dsimp [d]; positivity
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hcast : (localizedAverageScale rank R epsilon : ℝ) = r := Real.coe_toNNReal r hr.le
  refine ⟨Real.toNNReal_pos.mpr hr, ?_, ?_⟩
  · apply NNReal.coe_le_coe.mp
    push_cast
    rw [hcast]
    have hdcast : max (rank : ℝ) 1 = d := by simp [d]
    rw [hdcast]
    have h : r ≤ 1 / (200 * d) := min_le_left _ _
    convert h using 1
    ring
  · rw [hcast]
    change R * (400 * d * r) ≤ epsilon
    have h : r * (400 * d * (R + 1)) ≤ epsilon :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith [mul_nonneg hr.le hd.le]

end Erdos3

end

section

namespace Erdos3

theorem localizedAverageScale_le_one (rank : ℕ) {R epsilon : ℝ}
    (hR : 0 ≤ R) (hepsilon : 0 < epsilon) :
    localizedAverageScale rank R epsilon ≤ 1 := by
  apply (localizedAverageScale_spec rank hR hepsilon).2.1.trans
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast (show 1 ≤ 100 * (2 * max rank 1) by omega)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.LocalizedAverageScaleBudget
namespace OAI

section

namespace Erdos3

theorem localizedAverageScale_exp_lower (rank : ℕ) {W A E : ℝ}
    (hW : 0 ≤ W) (hWA : W ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    Real.exp (-((rank : ℝ) + A + E + 1600)) ≤
      (localizedAverageScale rank W (Real.exp (-E) / 2) : ℝ) := by
  let m : ℝ := (max rank 1 : ℕ)
  have hm : 0 < m := by dsimp [m]; positivity
  have hmexp : m ≤ Real.exp (rank : ℝ) := by
    apply le_trans _ (Real.add_one_le_exp (rank : ℝ))
    dsimp [m]
    exact_mod_cast (show max rank 1 ≤ rank + 1 by omega)
  have hWexp : W + 1 ≤ 2 * Real.exp A := by
    linarith [Real.one_le_exp hA]
  have hden : 800 * m * (W + 1) ≤ Real.exp ((rank : ℝ) + A + 1600) := by
    calc
      _ ≤ 800 * Real.exp (rank : ℝ) * (2 * Real.exp A) := by gcongr
      _ = 1600 * Real.exp ((rank : ℝ) + A) := by rw [Real.exp_add]; ring
      _ ≤ Real.exp 1600 * Real.exp ((rank : ℝ) + A) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        linarith [Real.add_one_le_exp 1600]
      _ = Real.exp ((rank : ℝ) + A + 1600) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hscaled : Real.exp (-((rank : ℝ) + A + E + 1600)) *
      (800 * m * (W + 1)) ≤ Real.exp (-E) := by
    calc
      _ ≤ Real.exp (-((rank : ℝ) + A + E + 1600)) *
          Real.exp ((rank : ℝ) + A + 1600) :=
        mul_le_mul_of_nonneg_left hden (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmin : 0 ≤ min (1 / (200 * m)) ((Real.exp (-E) / 2) / (400 * m * (W + 1))) := by
    exact le_of_lt (lt_min (by positivity) (by positivity))
  change Real.exp (-((rank : ℝ) + A + E + 1600)) ≤
    ((min (1 / (200 * m)) ((Real.exp (-E) / 2) / (400 * m * (W + 1)))).toNNReal : ℝ)
  rw [Real.coe_toNNReal _ hmin]
  apply le_min
  · apply (le_div_iff₀ (by positivity : 0 < 200 * m)).mpr
    have hsmall : 200 * m ≤ 800 * m * (W + 1) := by nlinarith
    exact (mul_le_mul_of_nonneg_left hsmall (Real.exp_nonneg _)).trans
      (hscaled.trans (Real.exp_le_one_iff.mpr (by linarith)))
  · rw [div_div, show 2 * (400 * m * (W + 1)) = 800 * m * (W + 1) by ring]
    exact (le_div_iff₀ (by positivity)).mpr hscaled

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FlatWeightedComparison
namespace OAI

namespace Erdos3

open scoped BigOperators

variable {ι : Type*}

end Erdos3

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.LocalConvolution

namespace Erdos3

open scoped BigOperators

variable {ι : Type*}

end Erdos3

namespace Erdos3.LocalConvolution

open scoped BigOperators

theorem momentAmplificationFactor_pos (delta : ℝ) : 0 < momentAmplificationFactor delta := by
  unfold momentAmplificationFactor
  omega

theorem momentAmplificationGain_pos (delta : ℝ) : 0 < momentAmplificationGain delta := by
  have hR : (0 : ℝ) < momentAmplificationFactor delta := by
    exact_mod_cast momentAmplificationFactor_pos delta
  have h := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity : 0 < 1 / (momentAmplificationFactor delta : ℝ))
  unfold momentAmplificationGain
  linarith

theorem momentAmplificationGain_le_one (delta : ℝ) : momentAmplificationGain delta ≤ 1 := by
  have hR : (1 : ℝ) ≤ momentAmplificationFactor delta := by
    exact_mod_cast momentAmplificationFactor_pos delta
  have hinv : 1 / (momentAmplificationFactor delta : ℝ) ≤ 1 :=
    (div_le_one (by linarith)).mpr hR
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hinv
  rw [Real.rpow_one] at h
  unfold momentAmplificationGain
  linarith

end Erdos3.LocalConvolution

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

end Erdos3.LocalConvolution

namespace Erdos3

open scoped BigOperators

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingDecomposition
namespace OAI

namespace Erdos3

open scoped BigOperators

theorem abs_expect_le_of_bound {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f : ι → ℝ) {epsilon : ℝ} (hf : ∀ x ∈ S, |f x| ≤ epsilon) :
    |𝔼 x ∈ S, f x| ≤ epsilon := by
  have h := RCLike.norm_expect_le (K := ℝ) (s := S) (f := f)
  calc
    _ ≤ 𝔼 x ∈ S, |f x| := by simpa only [Real.norm_eq_abs] using h
    _ ≤ 𝔼 _x ∈ S, epsilon := Finset.expect_le_expect hf
    _ = epsilon := Finset.expect_const hS epsilon

theorem abs_expect_sub_expect_le {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f g : ι → ℝ) {epsilon : ℝ} (hfg : ∀ x ∈ S, |f x - g x| ≤ epsilon) :
    |(𝔼 x ∈ S, f x) - 𝔼 x ∈ S, g x| ≤ epsilon := by
  rw [← Finset.expect_sub_distrib]
  exact abs_expect_le_of_bound S hS _ hfg

end Erdos3

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

end Erdos3.Peeling

namespace Erdos3

open scoped BigOperators

namespace Peeling

end Peeling

namespace CellRefinement

variable {G : Type*} [AddCommGroup G]

variable [Fintype G] [DecidableEq G]

end CellRefinement
end Erdos3

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.LocalConvolution

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

namespace Chain

variable {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
  {f g : G → ℝ} {cs : List (Finset G)}

end Chain
end Erdos3.Peeling

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

end Erdos3.Peeling

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

end Erdos3.Peeling

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalMomentScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem abs_sum_mul_sub_le {ι : Type*} [Fintype ι] (u v f : ι → ℝ) {M : ℝ}
    (hf : ∀ x, |f x| ≤ M) :
    |(∑ x, u x * f x) - ∑ x, v x * f x| ≤ M * ∑ x, |u x - v x| := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x, |u x * f x - v x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |u x - v x| * |f x| := by simp only [← sub_mul, abs_mul]
    _ ≤ ∑ x, |u x - v x| * M :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _))
    _ = M * ∑ x, |u x - v x| := by rw [← Finset.sum_mul]; ring

namespace LocalConvolution

variable {G : Type*} [AddCommGroup G] [Fintype G]

variable [DecidableEq G]

end LocalConvolution
end Erdos3

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

variable [DecidableEq G]

end Erdos3.LocalConvolution

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem sum_uniformMass_mul_eq_expect (S : Finset G) (f : G → ℝ) :
    (∑ x, realUniformMass S x * f x) = 𝔼 x ∈ S, f x := by
  rw [Finset.expect_eq_sum_div_card]
  simp only [realUniformMass, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  rw [← Finset.mul_sum]
  ring

variable [AddCommGroup G]

theorem expect_add_eq_shift_mass (S : Finset G) (f : G → ℝ) (t : G) :
    (𝔼 x ∈ S, f (x + t)) = ∑ x, realUniformMass S (x - t) * f x := by
  rw [← sum_uniformMass_mul_eq_expect]
  apply Fintype.sum_equiv (Equiv.addRight t)
  intro x
  simp

theorem abs_expect_add_sub_le (S : Finset G) (f : G → ℝ) (t : G)
    {M : ℝ} (hf : ∀ x, |f x| ≤ M) :
    |(𝔼 x ∈ S, f (x + t)) - 𝔼 x ∈ S, f x| ≤
      M * ∑ x, |realUniformMass S (x - t) - realUniformMass S x| := by
  rw [expect_add_eq_shift_mass, ← sum_uniformMass_mul_eq_expect]
  exact abs_sum_mul_sub_le _ _ f hf

end Erdos3

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

theorem localMomentGain_pos (delta : ℝ) : 0 < localMomentGain delta :=
  div_pos (momentAmplificationGain_pos _) (by norm_num)

theorem localMomentGain_le_half (delta : ℝ) : localMomentGain delta ≤ 1 / 2 :=
  div_le_div_of_nonneg_right (momentAmplificationGain_le_one _) (by norm_num)

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.LocalConvolution

end

section

namespace Erdos3

open scoped BigOperators

theorem abs_unit_weighted_mul_le {u v b M : ℝ}
    (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) (hb : |b| ≤ M) :
    |u * v * b| ≤ M := by
  have hM : 0 ≤ M := (abs_nonneg b).trans hb
  rw [abs_mul, abs_of_nonneg (mul_nonneg hu.1 hv.1)]
  exact (mul_le_mul_of_nonneg_left hb (mul_nonneg hu.1 hv.1)).trans
    ((mul_le_mul_of_nonneg_right
      ((mul_le_mul hu.2 hv.2 hv.1 (by norm_num)).trans_eq (one_mul 1)) hM).trans_eq (one_mul M))

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem abs_expect_pair_add_sub_le (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty)
    (F : G → G → ℝ) (r s : G) {M etaA etaB : ℝ} (hM : 0 ≤ M)
    (hF : ∀ x y, |F x y| ≤ M)
    (hAshift : (∑ x, |realUniformMass A (x - r) - realUniformMass A x|) ≤ etaA)
    (hBshift : (∑ y, |realUniformMass B (y - s) - realUniformMass B y|) ≤ etaB) :
    |(𝔼 x ∈ A, 𝔼 y ∈ B, F (x + r) (y + s)) -
      𝔼 x ∈ A, 𝔼 y ∈ B, F x y| ≤ M * (etaA + etaB) := by
  have hfirst : |(𝔼 x ∈ A, 𝔼 y ∈ B, F (x + r) (y + s)) -
      𝔼 x ∈ A, 𝔼 y ∈ B, F x (y + s)| ≤ M * etaA := by
    exact (abs_expect_add_sub_le A (fun x => 𝔼 y ∈ B, F x (y + s)) r
      (fun x => abs_expect_le_of_bound B hB _ (fun y _ => hF x (y + s)))).trans
        (mul_le_mul_of_nonneg_left hAshift hM)
  have hsecond : |(𝔼 x ∈ A, 𝔼 y ∈ B, F x (y + s)) -
      𝔼 x ∈ A, 𝔼 y ∈ B, F x y| ≤ M * etaB := by
    apply abs_expect_sub_expect_le A hA
    intro x _
    exact (abs_expect_add_sub_le B (F x) s (hF x)).trans
      (mul_le_mul_of_nonneg_left hBshift hM)
  calc
    _ ≤ |(𝔼 x ∈ A, 𝔼 y ∈ B, F (x + r) (y + s)) -
          𝔼 x ∈ A, 𝔼 y ∈ B, F x (y + s)| +
        |(𝔼 x ∈ A, 𝔼 y ∈ B, F x (y + s)) -
          𝔼 x ∈ A, 𝔼 y ∈ B, F x y| := abs_sub_le _ _ _
    _ ≤ M * etaA + M * etaB := add_le_add hfirst hsecond
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] in
theorem expect_neg_add_eq (L : Finset G) (hL : -L = L) (f : G → ℝ) (t : G) :
    (𝔼 x ∈ L, f (-x + t)) = 𝔼 x ∈ L, f (x + t) := by
  have h := Finset.expect_neg_index L (fun x => f (x + t))
  rw [hL] at h
  exact h.symm

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

variable [DecidableEq G]

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped NNReal

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteCellRefinement
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem expect_outside_reflected_le (L : Finset G) (hsymm : -L = L) (q : G)
    {eta : ℝ} (hTV : (∑ x, |realUniformMass L (x - q) - realUniformMass L x|) ≤ eta) :
    (𝔼 r ∈ L, if -r + q ∈ L then (0 : ℝ) else 1) ≤ eta := by
  let out : G → ℝ := fun x => if x ∈ L then 0 else 1
  have hbound (x : G) : |out x| ≤ 1 := by
    dsimp [out]
    split_ifs <;> norm_num
  have hzero : (𝔼 x ∈ L, out x) = 0 := by
    calc
      _ = 𝔼 _x ∈ L, (0 : ℝ) := Finset.expect_congr rfl (fun x hx => by simp [out, hx])
      _ = 0 := by simp
  have h := abs_expect_add_sub_le L out q hbound
  rw [hzero, sub_zero, one_mul] at h
  change (𝔼 r ∈ L, out (-r + q)) ≤ eta
  rw [expect_neg_add_eq L hsymm out q]
  exact (le_abs_self _).trans (h.trans hTV)

theorem abs_reflected_restriction_le (L : Finset G) (hsymm : -L = L)
    (F : G → G → ℝ) (q : G) {M eta : ℝ} (hM : 0 ≤ M) (hF : ∀ x y, |F x y| ≤ M)
    (hTV : (∑ x, |realUniformMass L (x - q) - realUniformMass L x|) ≤ eta) :
    |(𝔼 r ∈ L, F r (-r + q)) -
      𝔼 r ∈ L, if -r + q ∈ L then F r (-r + q) else 0| ≤ M * eta := by
  rw [← Finset.expect_sub_distrib]
  have hnorm := RCLike.norm_expect_le (K := ℝ) (s := L)
    (f := fun r => F r (-r + q) - if -r + q ∈ L then F r (-r + q) else 0)
  calc
    _ ≤ 𝔼 r ∈ L, |F r (-r + q) - if -r + q ∈ L then F r (-r + q) else 0| := by
      simpa only [Real.norm_eq_abs] using hnorm
    _ ≤ 𝔼 r ∈ L, M * (if -r + q ∈ L then (0 : ℝ) else 1) := by
      apply Finset.expect_le_expect
      intro r _
      by_cases hr : -r + q ∈ L
      · simp only [hr, ite_true, sub_self, abs_zero, mul_zero, le_refl]
      · simpa only [hr, ite_false, sub_zero, mul_one] using hF r (-r + q)
    _ = M * (𝔼 r ∈ L, if -r + q ∈ L then (0 : ℝ) else 1) := (Finset.mul_expect _ _ _).symm
    _ ≤ M * eta := mul_le_mul_of_nonneg_left (expect_outside_reflected_le L hsymm q hTV) hM

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

theorem expect_matchedPairAverage {ι : Type*} (I : Finset ι) (L S : Finset G)
    (F : ι → G → G → ℝ) :
    (𝔼 i ∈ I, matchedPairAverage L S (F i)) =
      matchedPairAverage L S (fun x y => 𝔼 i ∈ I, F i x y) := by
  unfold matchedPairAverage
  rw [Finset.expect_comm I L]
  apply Finset.expect_congr rfl
  intro r _
  rw [Finset.expect_comm I S]
  apply Finset.expect_congr rfl
  intro s _
  exact Finset.expect_comm I S _

theorem matchedPairAverage_const (L S : Finset G) (hL : L.Nonempty) (hS : S.Nonempty) (b : ℝ) :
    matchedPairAverage L S (fun _ _ => b) = b := by
  simp only [matchedPairAverage, Finset.expect_const hL, Finset.expect_const hS]

variable [Fintype G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

variable [DecidableEq G]

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G]

theorem matchedIntegral_sum_order (L S : Finset G) (a f g : G → ℝ) :
    matchedIntegral L S a f g =
      𝔼 s ∈ S, 𝔼 t ∈ S, 𝔼 r ∈ L, f r * g (-r + (s + t)) * a (s + t) := by
  unfold matchedIntegral matchedPairAverage
  rw [Finset.expect_comm L S]
  apply Finset.expect_congr rfl
  intro s _
  rw [Finset.expect_comm L S]
  apply Finset.expect_congr rfl
  intro t _
  apply Finset.expect_congr rfl
  intro r _
  dsimp only
  have heq : r + (-r + s + t) = s + t := by abel
  rw [heq, add_assoc (-r) s t]

variable [Fintype G] [DecidableEq G]

theorem abs_matchedIntegral_restrict_sub_le
    (L S : Finset G) (hsymm : -L = L) (hS : S.Nonempty) (a f g : G → ℝ)
    {M eta : ℝ} (hM : 0 ≤ M) (ha : ∀ x, |a x| ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hTV : ∀ s ∈ S, ∀ t ∈ S,
      (∑ x, |realUniformMass L (x - (s + t)) - realUniformMass L x|) ≤ eta) :
    |matchedIntegral L S a f g - matchedIntegral L S a (Peeling.slice L f) (Peeling.slice L g)| ≤
      M * eta := by
  simp only [matchedIntegral_sum_order]
  apply abs_expect_sub_expect_le S hS
  intro s hs
  apply abs_expect_sub_expect_le S hS
  intro t ht
  have htrunc :
      (𝔼 r ∈ L, Peeling.slice L f r * Peeling.slice L g (-r + (s + t)) * a (s + t)) =
        𝔼 r ∈ L, if -r + (s + t) ∈ L then f r * g (-r + (s + t)) * a (s + t) else 0 := by
    apply Finset.expect_congr rfl
    intro r hr
    by_cases hy : -r + (s + t) ∈ L <;> simp [Peeling.slice, hr, hy]
  rw [htrunc]
  exact abs_reflected_restriction_le L hsymm (fun r y => f r * g y * a (s + t)) (s + t)
    hM (fun r y => abs_unit_weighted_mul_le (hf r) (hg y) (ha (s + t))) (hTV s hs t ht)

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G]

theorem parentMatchedAverage_eq_average (A B L S : Finset G) (F : G → G → ℝ) :
    parentMatchedAverage A B L S F =
      matchedPairAverage L S (fun r q => 𝔼 x ∈ A, 𝔼 y ∈ B, F (x + r) (y + q)) := by
  unfold parentMatchedAverage
  simp_rw [expect_matchedPairAverage]

theorem parentMatchedAverage_eq_integrals (A B L S : Finset G) (a f g : G → ℝ) :
    parentMatchedAverage A B L S (fun x y => f x * g y * a (x + y)) =
      𝔼 x ∈ A, 𝔼 y ∈ B, matchedIntegral L S (fun z => a (x + y + z))
        (fun r => f (x + r)) (fun q => g (y + q)) := by
  unfold parentMatchedAverage
  apply Finset.expect_congr rfl
  intro x _
  apply Finset.expect_congr rfl
  intro y _
  unfold matchedIntegral
  apply congrArg (matchedPairAverage L S)
  funext r q
  dsimp only
  rw [show (x + r) + (y + q) = x + y + (r + q) by abel]

variable [DecidableEq G]

variable [Fintype G]

theorem abs_parentMatchedAverage_sub_le
    (A B L S : Finset G) (hA : A.Nonempty) (hB : B.Nonempty) (hL : L.Nonempty) (hS : S.Nonempty)
    (F : G → G → ℝ) {M etaA etaB : ℝ} (hM : 0 ≤ M) (hF : ∀ x y, |F x y| ≤ M)
    (hAshift : ∀ r ∈ L, (∑ x, |realUniformMass A (x - r) - realUniformMass A x|) ≤ etaA)
    (hBshift : ∀ r ∈ L, ∀ s ∈ S, ∀ t ∈ S,
      (∑ y, |realUniformMass B (y - (-r + s + t)) - realUniformMass B y|) ≤ etaB) :
    |parentMatchedAverage A B L S F - 𝔼 x ∈ A, 𝔼 y ∈ B, F x y| ≤ M * (etaA + etaB) := by
  rw [parentMatchedAverage_eq_average]
  calc
    _ = |matchedPairAverage L S (fun r q => 𝔼 x ∈ A, 𝔼 y ∈ B, F (x + r) (y + q)) -
        matchedPairAverage L S (fun _ _ => 𝔼 x ∈ A, 𝔼 y ∈ B, F x y)| := by
      rw [matchedPairAverage_const L S hL hS]
    _ ≤ M * (etaA + etaB) := by
      unfold matchedPairAverage
      apply abs_expect_sub_expect_le L hL
      intro r hr
      apply abs_expect_sub_expect_le S hS
      intro s hs
      apply abs_expect_sub_expect_le S hS
      intro t ht
      exact abs_expect_pair_add_sub_le A B hA hB F r (-r + s + t) hM hF
        (hAshift r hr) (hBshift r hr s hs t ht)

theorem abs_parentMatchedAverage_sub_truncated_le
    (A B L S : Finset G) (hA : A.Nonempty) (hB : B.Nonempty) (hsymm : -L = L) (hS : S.Nonempty)
    (a f g : G → ℝ) {M etaL : ℝ} (hM : 0 ≤ M) (ha : ∀ x, |a x| ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hTV : ∀ s ∈ S, ∀ t ∈ S,
      (∑ x, |realUniformMass L (x - (s + t)) - realUniformMass L x|) ≤ etaL) :
    |parentMatchedAverage A B L S (fun x y => f x * g y * a (x + y)) -
      parentTruncatedIntegral A B L S a f g| ≤ M * etaL := by
  rw [parentMatchedAverage_eq_integrals]
  unfold parentTruncatedIntegral
  apply abs_expect_sub_expect_le A hA
  intro x _
  apply abs_expect_sub_expect_le B hB
  intro y _
  exact abs_matchedIntegral_restrict_sub_le L S hsymm hS _ _ _ hM
    (fun z => ha (x + y + z)) (fun r => hf (x + r)) (fun q => hg (y + q)) hTV

theorem parent_integral_truncated_comparison
    (A B L S : Finset G) (hA : A.Nonempty) (hB : B.Nonempty) (hL : L.Nonempty) (hS : S.Nonempty)
    (hsymm : -L = L) (a f g : G → ℝ) {M etaA etaB etaL : ℝ} (hM : 0 ≤ M)
    (ha : ∀ x, |a x| ≤ M) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hAshift : ∀ r ∈ L, (∑ x, |realUniformMass A (x - r) - realUniformMass A x|) ≤ etaA)
    (hBshift : ∀ r ∈ L, ∀ s ∈ S, ∀ t ∈ S,
      (∑ y, |realUniformMass B (y - (-r + s + t)) - realUniformMass B y|) ≤ etaB)
    (hLshift : ∀ s ∈ S, ∀ t ∈ S,
      (∑ x, |realUniformMass L (x - (s + t)) - realUniformMass L x|) ≤ etaL) :
    |bilinearIntegral A B a f g - parentTruncatedIntegral A B L S a f g| ≤
      M * (etaA + etaB + etaL) := by
  have hfirst := abs_parentMatchedAverage_sub_le A B L S hA hB hL hS
    (fun x y => f x * g y * a (x + y)) hM
    (fun x y => abs_unit_weighted_mul_le (hf x) (hg y) (ha (x + y))) hAshift hBshift
  have hsecond := abs_parentMatchedAverage_sub_truncated_le A B L S hA hB hsymm hS a f g
    hM ha hf hg hLshift
  calc
    _ ≤ |bilinearIntegral A B a f g -
          parentMatchedAverage A B L S (fun x y => f x * g y * a (x + y))| +
        |parentMatchedAverage A B L S (fun x y => f x * g y * a (x + y)) -
          parentTruncatedIntegral A B L S a f g| := abs_sub_le _ _ _
    _ ≤ M * (etaA + etaB) + M * etaL :=
      add_le_add (by simpa only [bilinearIntegral, abs_sub_comm] using hfirst) hsecond
    _ = _ := by ring

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

variable [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] {I : Type*}

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrMatchingScales
namespace OAI

section

namespace Erdos3.CellRefinement

open scoped BigOperators Pointwise NNReal

variable {N : ℕ} [NeZero N]

theorem bohr_parent_truncated_comparison
    (B L S : CyclicBohr.Set N) (hB : B.IsRankRegular) (hL : L.IsRankRegular)
    {ell sigma delta : ℝ≥0}
    (hLB : L.carrier ⊆ (B.ndilate ell).carrier)
    (hSB : S.carrier ⊆ (B.ndilate sigma).carrier)
    (hSL : S.carrier ⊆ (L.ndilate delta).carrier)
    (hparent : ell + sigma + sigma ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (hlocal : delta + delta ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (a f g : ZMod N → ℝ) {M : ℝ} (hM : 0 ≤ M) (ha : ∀ x, |a x| ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    |bilinearIntegral B.carrier B.carrier a f g -
      parentTruncatedIntegral B.carrier B.carrier L.carrier S.carrier a f g| ≤
      M * (2 * (400 * (max B.rank 1 : ℕ) * ((ell + sigma + sigma : ℝ≥0) : ℝ)) +
        400 * (max L.rank 1 : ℕ) * ((delta + delta : ℝ≥0) : ℝ)) := by
  have hsymm : -L.carrier = L.carrier := by
    ext x
    constructor
    · intro h
      obtain ⟨y, hy, rfl⟩ := Finset.mem_neg.mp h
      exact (L.neg_mem_iff y).2 hy
    · intro h
      exact Finset.mem_neg.mpr ⟨-x, (L.neg_mem_iff x).2 h, neg_neg x⟩
  have hfirst : ∀ r ∈ L.carrier,
      (∑ x, |realUniformMass B.carrier (x - r) - realUniformMass B.carrier x|) ≤
        400 * (max B.rank 1 : ℕ) * ((ell + sigma + sigma : ℝ≥0) : ℝ) := by
    intro r hr
    apply CyclicBohr.Set.uniformMass_translation_le_of_rankRegular hB hparent
    exact CyclicBohr.Set.carrier_ndilate_mono
      (show ell ≤ ell + sigma + sigma from (le_self_add).trans le_self_add) (hLB hr)
  have hsecond : ∀ r ∈ L.carrier, ∀ s ∈ S.carrier, ∀ t ∈ S.carrier,
      (∑ x, |realUniformMass B.carrier (x - (-r + s + t)) - realUniformMass B.carrier x|) ≤
        400 * (max B.rank 1 : ℕ) * ((ell + sigma + sigma : ℝ≥0) : ℝ) := by
    intro r hr s hs t ht
    apply CyclicBohr.Set.uniformMass_translation_le_of_rankRegular hB hparent
    have hmem := CyclicBohr.Set.sub_mem_ndilate
      (CyclicBohr.Set.add_mem_ndilate (hSB hs) (hSB ht)) (hLB hr)
    have hscale : sigma + sigma + ell = ell + sigma + sigma := by ac_rfl
    have hpoint : (s + t) - r = -r + s + t := by abel
    rwa [hscale, hpoint] at hmem
  have hboundary : ∀ s ∈ S.carrier, ∀ t ∈ S.carrier,
      (∑ x, |realUniformMass L.carrier (x - (s + t)) - realUniformMass L.carrier x|) ≤
        400 * (max L.rank 1 : ℕ) * ((delta + delta : ℝ≥0) : ℝ) := by
    intro s hs t ht
    exact CyclicBohr.Set.uniformMass_translation_le_of_rankRegular hL hlocal
      (CyclicBohr.Set.add_mem_ndilate (hSL hs) (hSL ht))
  have h := parent_integral_truncated_comparison B.carrier B.carrier L.carrier S.carrier
    B.carrier_nonempty B.carrier_nonempty L.carrier_nonempty S.carrier_nonempty hsymm
    a f g hM ha hf hg hfirst hsecond hboundary
  simpa only [two_mul] using h

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_bohr_matching_scales_with_scales
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular)
    {M epsilon : ℝ} (hM : 0 ≤ M) (hepsilon : 0 < epsilon)
    (kappa tau : ℝ≥0) (hkappa0 : 0 < kappa)
    (hkappaScale : kappa ≤ localizedAverageScale B.rank M (epsilon / 4))
    (htau0 : 0 < tau) (htau : tau ≤ kappa / 2) :
    ∃ L S : CyclicBohr.Set N,
      L.frequencies = B.frequencies ∧ S.frequencies = B.frequencies ∧
      L.IsRankRegular ∧ S.IsRankRegular ∧ 0 < L.radius ∧ 0 < S.radius ∧
      (kappa : ℝ) * B.radius / 6 ≤ L.radius ∧ L.radius ≤ (kappa : ℝ) * B.radius / 3 ∧
      (kappa : ℝ) * (tau : ℝ) * B.radius / 12 ≤ S.radius ∧ S.radius ≤ (tau : ℝ) * L.radius ∧
      L.carrier ⊆ (B.ndilate (kappa / 3)).carrier ∧
      S.carrier ⊆ (L.ndilate tau).carrier ∧
      ∀ a f g : ZMod N → ℝ, (∀ x, |a x| ≤ M) →
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
        |bilinearIntegral B.carrier B.carrier a f g -
          parentTruncatedIntegral B.carrier B.carrier L.carrier S.carrier a f g| ≤ epsilon := by
  obtain ⟨_, hlimit, hbound⟩ := localizedAverageScale_spec B.rank hM
    (show 0 < epsilon / 4 by positivity)
  have hkappa := hkappaScale.trans hlimit
  have hscaleR : (kappa : ℝ) ≤ localizedAverageScale B.rank M (epsilon / 4) := by
    exact_mod_cast hkappaScale
  have herror : M * (400 * (max B.rank 1 : ℕ) * (kappa : ℝ)) ≤ epsilon / 4 := by
    apply le_trans _ hbound
    gcongr
  have hkappaR : (0 : ℝ) < kappa := by exact_mod_cast hkappa0
  have hkappa1 : kappa ≤ 1 := by
    apply hkappa.trans
    rw [div_le_one (by positivity)]
    exact_mod_cast (show 1 ≤ 100 * (2 * max B.rank 1) by omega)
  have hell0 : 0 < kappa / 3 := div_pos hkappa0 (by norm_num)
  have hell1 : kappa / 3 ≤ 1 :=
    (div_le_self (by positivity) (by norm_num)).trans hkappa1
  obtain ⟨L, hLfreq, hLreg, hLlo, hLhi, hLB, _⟩ :=
    B.exists_controlled_regular_subdilate hBpos (kappa / 3) hell0 hell1
  change (kappa : ℝ) / 3 * B.radius / 2 ≤ L.radius at hLlo
  change L.radius ≤ (kappa : ℝ) / 3 * B.radius at hLhi
  have hLlower : (kappa : ℝ) * B.radius / 6 ≤ L.radius := by nlinarith [hLlo]
  have hLupper : L.radius ≤ (kappa : ℝ) * B.radius / 3 := by nlinarith [hLhi]
  have hLpos : 0 < L.radius := (show 0 < (kappa : ℝ) * B.radius / 6 by positivity).trans_le hLlower
  have hLrank : L.rank = B.rank := by simp only [CyclicBohr.Set.rank, hLfreq]
  have htau1 : tau ≤ 1 := htau.trans
    ((div_le_self (by positivity) (by norm_num)).trans hkappa1)
  have htauR : (0 : ℝ) < tau := by exact_mod_cast htau0
  obtain ⟨S, hSfreq, hSreg, hSlo, hShi, hSL, _⟩ :=
    L.exists_controlled_regular_subdilate hLpos tau htau0 htau1
  have hSpos : 0 < S.radius :=
    (show 0 < (tau : ℝ) * L.radius / 2 by positivity).trans_le hSlo
  have hSlower : (kappa : ℝ) * (tau : ℝ) * B.radius / 12 ≤ S.radius := by
    have h := mul_le_mul_of_nonneg_left hLlower (show (0 : ℝ) ≤ tau / 2 by positivity)
    nlinarith [hSlo]
  have hSLbase : S.carrier ⊆ L.carrier := by
    have h := hSL.trans (CyclicBohr.Set.carrier_ndilate_mono (B := L) htau1)
    simpa only [CyclicBohr.Set.ndilate_one] using h
  refine ⟨L, S, hLfreq, hSfreq.trans hLfreq, hLreg, hSreg, hLpos, hSpos,
    hLlower, hLupper, hSlower, hShi, hLB, hSL, ?_⟩
  intro a f g ha hf hg
  have hthirds : kappa / 3 + kappa / 3 + kappa / 3 = kappa := by ring
  have htaus : tau + tau ≤ kappa := by
    have h := add_le_add htau htau
    simpa only [add_halves] using h
  have hparent : kappa / 3 + kappa / 3 + kappa / 3 ≤
      1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0) := by rwa [hthirds]
  have hlocal : tau + tau ≤
      1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0) := by
    rw [hLrank]
    exact htaus.trans hkappa
  have h := bohr_parent_truncated_comparison B L S hB hLreg hLB (hSLbase.trans hLB) hSL
    hparent hlocal a f g hM ha hf hg
  rw [hthirds, hLrank] at h
  have htausR : ((tau + tau : ℝ≥0) : ℝ) ≤ kappa := by exact_mod_cast htaus
  have hlocalError : M * (400 * (max B.rank 1 : ℕ) * ((tau + tau : ℝ≥0) : ℝ)) ≤ epsilon / 4 := by
    apply le_trans _ herror
    gcongr
  exact h.trans (by nlinarith [herror, hlocalError])

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentReturnScale
namespace OAI

section

namespace Erdos3

theorem localizedAverageScale_mono_error (rank : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    Monotone (fun epsilon : ℝ => localizedAverageScale rank R epsilon) := by
  intro a b hab
  unfold localizedAverageScale
  apply Real.toNNReal_mono
  exact min_le_min le_rfl (div_le_div_of_nonneg_right hab (by positivity))

theorem localizedAverageScale_exp_lower_of_error (rank : ℕ) {W A E epsilon : ℝ}
    (hW : 0 ≤ W) (hWA : W ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hepsilon : Real.exp (-E) / 2 ≤ epsilon) :
    Real.exp (-((rank : ℝ) + A + E + 1600)) ≤ (localizedAverageScale rank W epsilon : ℝ) := by
  apply (localizedAverageScale_exp_lower rank hW hWA hA hE).trans
  exact_mod_cast localizedAverageScale_mono_error rank hW hepsilon

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped NNReal

theorem outerMatchingScale_spec (rank : ℕ) {W epsilon : ℝ} {scale : ℝ≥0}
    (hW : 0 ≤ W) (hepsilon : 0 < epsilon) (hscale : 0 < scale) :
    0 < outerMatchingScale rank W epsilon scale ∧
      outerMatchingScale rank W epsilon scale ≤ scale ∧
      outerMatchingScale rank W epsilon scale ≤ localizedAverageScale rank W (epsilon / 4) := by
  exact ⟨lt_min hscale (localizedAverageScale_spec rank hW (show 0 < epsilon / 4 by positivity)).1,
    min_le_left _ _, min_le_right _ _⟩

theorem outerMatchingScaleLoss_nonneg (rank : ℕ) {A E T : ℝ}
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hT : 0 ≤ T) :
    0 ≤ outerMatchingScaleLoss rank A E T := by
  unfold outerMatchingScaleLoss
  positivity

theorem outerMatchingScale_exp_lower (rank : ℕ) {W A E T : ℝ} {scale : ℝ≥0}
    (hW : 0 ≤ W) (hcap : W ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hscale : Real.exp (-T) ≤ (scale : ℝ)) :
    Real.exp (-outerMatchingScaleLoss rank A E T) ≤
      (outerMatchingScale rank W (Real.exp (-E)) scale : ℝ) := by
  have htwo : Real.exp (-2 : ℝ) ≤ 1 / 2 := by
    have h : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
    simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num) h
  have herror : Real.exp (-(E + 2)) / 2 ≤ Real.exp (-E) / 4 := by
    have h := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg (-E))
    rw [← Real.exp_add] at h
    have heq : -E + -2 = -(E + 2) := by ring
    rw [heq] at h
    linarith
  have hlocal := localizedAverageScale_exp_lower_of_error rank hW hcap hA
    (show 0 ≤ E + 2 by positivity) herror
  change _ ≤ min (scale : ℝ) (localizedAverageScale rank W (Real.exp (-E) / 4) : ℝ)
  apply le_min
  · apply le_trans _ hscale
    apply Real.exp_le_exp.mpr
    unfold outerMatchingScaleLoss
    have hrank : (0 : ℝ) ≤ rank := Nat.cast_nonneg rank
    linarith
  · apply le_trans _ hlocal
    apply Real.exp_le_exp.mpr
    unfold outerMatchingScaleLoss
    linarith

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped NNReal

theorem controlledLocalMomentScale_spec (rank : ℕ) {M delta : ℝ}
    (hM : 0 ≤ M) (hdelta : 0 < delta) :
    0 < controlledLocalMomentScale rank M delta ∧
      controlledLocalMomentScale rank M delta + controlledLocalMomentScale rank M delta ≤
        1 / (100 * (2 * max rank 1 : ℕ) : ℝ≥0) ∧
      1200 * (max rank 1 : ℕ) *
          ((controlledLocalMomentScale rank M delta + controlledLocalMomentScale rank M delta : ℝ≥0) : ℝ) * M ≤
        min (delta / 2) (localMomentGain delta) := by
  have hc : 0 < min (delta / 2) (localMomentGain delta) :=
    lt_min (by positivity) (localMomentGain_pos delta)
  obtain ⟨hr, hsmall, herror⟩ := localizedAverageScale_spec rank hM
    (show 0 < min (delta / 2) (localMomentGain delta) / 3 by positivity)
  have heq : controlledLocalMomentScale rank M delta + controlledLocalMomentScale rank M delta =
      localizedAverageScale rank M (min (delta / 2) (localMomentGain delta) / 3) := by
    unfold controlledLocalMomentScale
    ring
  refine ⟨div_pos hr (by norm_num), ?_, ?_⟩
  · rwa [heq]
  · rw [heq]
    nlinarith

theorem localMomentErrorBudget_spec {delta : ℝ} (hdelta : 0 < delta) :
    0 ≤ localMomentErrorBudget delta ∧
      Real.exp (-localMomentErrorBudget delta) / 2 = min (delta / 2) (localMomentGain delta) / 3 := by
  have hc : 0 < min (delta / 2) (localMomentGain delta) :=
    lt_min (by positivity) (localMomentGain_pos delta)
  have hc1 : min (delta / 2) (localMomentGain delta) ≤ 1 / 2 :=
    (min_le_right _ _).trans (localMomentGain_le_half delta)
  unfold localMomentErrorBudget
  constructor
  · exact neg_nonneg.mpr (Real.log_nonpos (by positivity) (by linarith))
  · rw [neg_neg, Real.exp_log (by positivity)]
    ring

theorem controlledLocalMomentScale_exp_lower (rank : ℕ) {M delta A : ℝ}
    (hM : 0 ≤ M) (hcap : M ≤ Real.exp A) (hA : 0 ≤ A) (hdelta : 0 < delta) :
    Real.exp (-((rank : ℝ) + A + localMomentErrorBudget delta + 1602)) ≤
      (controlledLocalMomentScale rank M delta : ℝ) := by
  obtain ⟨hE, hEeq⟩ := localMomentErrorBudget_spec hdelta
  have hbase := localizedAverageScale_exp_lower rank hM hcap hA hE
  rw [hEeq] at hbase
  have htwo : Real.exp (-2 : ℝ) ≤ 1 / 2 := by
    have h : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
    simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num) h
  calc
    _ = Real.exp (-((rank : ℝ) + A + localMomentErrorBudget delta + 1600)) * Real.exp (-2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ (localizedAverageScale rank M (min (delta / 2) (localMomentGain delta) / 3) : ℝ) * (1 / 2) :=
      mul_le_mul hbase htwo (Real.exp_nonneg _) (by positivity)
    _ = _ := by
      change _ = (localizedAverageScale rank M (min (delta / 2) (localMomentGain delta) / 3) : ℝ) / 2
      ring

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.UnbalancedWidthBudget
namespace OAI

section

namespace Erdos3.LocalConvolution

open CyclicCrootSisask

theorem unbalancedErrorBudget_spec {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    0 ≤ unbalancedErrorBudget c ∧ Real.exp (-unbalancedErrorBudget c) / 2 = c / 64 := by
  constructor
  · unfold unbalancedErrorBudget
    apply neg_nonneg.mpr
    exact Real.log_nonpos (by positivity) (by linarith)
  · unfold unbalancedErrorBudget
    rw [neg_neg, Real.exp_log (by positivity)]
    ring

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinatedMatchingScale
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped NNReal

theorem coordinatedMatchingScale_spec (rank : ℕ) {M delta c : ℝ} {kappa : ℝ≥0}
    (hM : 0 ≤ M) (hdelta : 0 < delta) (hc : 0 < c) (hkappa : 0 < kappa) :
    0 < coordinatedMatchingScale rank M delta c kappa ∧
      coordinatedMatchingScale rank M delta c kappa ≤ kappa / 2 ∧
      coordinatedMatchingScale rank M delta c kappa ≤ controlledLocalMomentScale rank M delta ∧
      coordinatedMatchingScale rank M delta c kappa + coordinatedMatchingScale rank M delta c kappa ≤
        1 / (100 * (2 * max rank 1 : ℕ) : ℝ≥0) ∧
      M ^ 2 * (400 * (max rank 1 : ℕ) *
        ((coordinatedMatchingScale rank M delta c kappa + coordinatedMatchingScale rank M delta c kappa : ℝ≥0) : ℝ)) ≤
          c / 32 := by
  obtain ⟨hmoment, _, _⟩ := controlledLocalMomentScale_spec rank hM hdelta
  obtain ⟨hboundary, hsmall, herror⟩ := localizedAverageScale_spec rank (sq_nonneg M)
    (show 0 < c / 32 by positivity)
  have hleft : coordinatedMatchingScale rank M delta c kappa ≤ kappa / 2 := min_le_left _ _
  have hmomentBound : coordinatedMatchingScale rank M delta c kappa ≤
      controlledLocalMomentScale rank M delta := (min_le_right _ _).trans (min_le_left _ _)
  have hboundaryBound : coordinatedMatchingScale rank M delta c kappa ≤
      localizedAverageScale rank (M ^ 2) (c / 32) / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hsum : coordinatedMatchingScale rank M delta c kappa + coordinatedMatchingScale rank M delta c kappa ≤
      localizedAverageScale rank (M ^ 2) (c / 32) := by
    simpa only [add_halves] using add_le_add hboundaryBound hboundaryBound
  refine ⟨lt_min (div_pos hkappa (by norm_num)) (lt_min hmoment (div_pos hboundary (by norm_num))),
    hleft, hmomentBound, hsum.trans hsmall, ?_⟩
  have hsumR : ((coordinatedMatchingScale rank M delta c kappa + coordinatedMatchingScale rank M delta c kappa : ℝ≥0) : ℝ) ≤
      localizedAverageScale rank (M ^ 2) (c / 32) := by exact_mod_cast hsum
  apply le_trans _ herror
  gcongr

theorem coordinatedMatchingScale_exp_lower (rank : ℕ)
    {M P K delta c : ℝ} {kappa : ℝ≥0}
    (hM : 0 ≤ M) (hcap : M ≤ Real.exp P) (hP : 0 ≤ P) (hK : 0 ≤ K)
    (hdelta : 0 < delta) (hc : 0 < c) (hc1 : c ≤ 1)
    (hkappa : Real.exp (-K) ≤ (kappa : ℝ)) :
    Real.exp (-coordinatedMatchingScaleLoss rank P K delta c) ≤
      (coordinatedMatchingScale rank M delta c kappa : ℝ) := by
  have hEd := (localMomentErrorBudget_spec hdelta).1
  obtain ⟨hEc, hEceq⟩ := unbalancedErrorBudget_spec hc hc1
  have hmoment := controlledLocalMomentScale_exp_lower rank hM hcap hP hdelta
  have hMtwo : M ^ 2 ≤ Real.exp (2 * P) := by
    calc
      _ ≤ (Real.exp P) ^ 2 := pow_le_pow_left₀ hM hcap 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hboundary := localizedAverageScale_exp_lower_of_error rank (sq_nonneg M) hMtwo
    (show 0 ≤ 2 * P by positivity) hEc
    (show Real.exp (-unbalancedErrorBudget c) / 2 ≤ c / 32 by rw [hEceq]; linarith)
  have htwo : Real.exp (-2 : ℝ) ≤ 1 / 2 := by
    have h : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
    simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num) h
  have hhalf {a : ℝ} {r : ℝ≥0} (ha : Real.exp (-a) ≤ (r : ℝ)) :
      Real.exp (-(a + 2)) ≤ ((r / 2 : ℝ≥0) : ℝ) := by
    calc
      _ = Real.exp (-a) * Real.exp (-2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ (r : ℝ) * (1 / 2) := mul_le_mul ha htwo (Real.exp_nonneg _) r.coe_nonneg
      _ = _ := by change _ = (r : ℝ) / 2; ring
  have hrank : (0 : ℝ) ≤ rank := Nat.cast_nonneg rank
  have houter : Real.exp (-coordinatedMatchingScaleLoss rank P K delta c) ≤
      ((kappa / 2 : ℝ≥0) : ℝ) := by
    apply le_trans _ (hhalf hkappa)
    apply Real.exp_le_exp.mpr
    unfold coordinatedMatchingScaleLoss
    linarith
  have hmom : Real.exp (-coordinatedMatchingScaleLoss rank P K delta c) ≤
      (controlledLocalMomentScale rank M delta : ℝ) := by
    apply le_trans _ hmoment
    apply Real.exp_le_exp.mpr
    unfold coordinatedMatchingScaleLoss
    linarith
  have hbound : Real.exp (-coordinatedMatchingScaleLoss rank P K delta c) ≤
      ((localizedAverageScale rank (M ^ 2) (c / 32) / 2 : ℝ≥0) : ℝ) := by
    apply le_trans _ (hhalf hboundary)
    apply Real.exp_le_exp.mpr
    unfold coordinatedMatchingScaleLoss
    linarith
  change _ ≤ min ((kappa / 2 : ℝ≥0) : ℝ)
    (min (controlledLocalMomentScale rank M delta : ℝ)
      ((localizedAverageScale rank (M ^ 2) (c / 32) / 2 : ℝ≥0) : ℝ))
  exact le_min houter (le_min hmom hbound)

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CoordinatedBohrMatching
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

theorem matchingWidthLoss_nonneg (rank : ℕ) {P K delta c : ℝ}
    (hP : 0 ≤ P) (hK : 0 ≤ K) (hdelta : 0 < delta) (hc : 0 < c) (hc1 : c ≤ 1) :
    0 ≤ matchingWidthLoss rank P K delta c := by
  have hEd := (localMomentErrorBudget_spec hdelta).1
  have hEc := (unbalancedErrorBudget_spec hc hc1).1
  unfold matchingWidthLoss coordinatedMatchingScaleLoss
  positivity

variable {N : ℕ} [NeZero N]

theorem exists_coordinated_bohr_matching
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular)
    {W epsilon M P K delta c : ℝ} (hW : 0 ≤ W) (hepsilon : 0 < epsilon)
    (hM : 0 ≤ M) (hcap : M ≤ Real.exp P) (hP : 0 ≤ P) (hK : 0 ≤ K)
    (hdelta : 0 < delta) (hc : 0 < c) (hc1 : c ≤ 1)
    (kappa : ℝ≥0) (hkappa : kappa ≤ localizedAverageScale B.rank W (epsilon / 4))
    (hkappaLog : Real.exp (-K) ≤ (kappa : ℝ)) :
    let tau := coordinatedMatchingScale B.rank M delta c kappa
    ∃ L S : CyclicBohr.Set N,
      L.frequencies = B.frequencies ∧ S.frequencies = L.frequencies ∧
      L.IsRankRegular ∧ S.IsRankRegular ∧ 0 < L.radius ∧ 0 < S.radius ∧
      L.radius ≤ B.radius / 3 ∧ S.radius ≤ L.radius ∧
      B.radius * Real.exp (-(K + 6)) ≤ L.radius ∧
      B.radius * Real.exp (-matchingWidthLoss B.rank P K delta c) ≤ S.radius ∧
      L.carrier ⊆ (B.ndilate (kappa / 3)).carrier ∧
      S.carrier ⊆ (L.ndilate tau).carrier ∧
      S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M delta)).carrier ∧
      tau + tau ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0) ∧
      M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((tau + tau : ℝ≥0) : ℝ)) ≤ c / 32 ∧
      ∀ a f g : ZMod N → ℝ, (∀ x, |a x| ≤ W) →
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
        |bilinearIntegral B.carrier B.carrier a f g -
          parentTruncatedIntegral B.carrier B.carrier L.carrier S.carrier a f g| ≤ epsilon := by
  intro tau
  have hkappa0 : 0 < kappa := by
    exact_mod_cast (Real.exp_pos (-K)).trans_le hkappaLog
  obtain ⟨htau0, htau, hmoment, hsmall, herror⟩ :=
    coordinatedMatchingScale_spec B.rank hM hdelta hc hkappa0
  obtain ⟨L, S, hLfreq, hSfreq, hLreg, hSreg, hLpos, hSpos,
      hLlo, hLhi, hSlo, hShi, hLB, hSL, hcompare⟩ :=
    exists_bohr_matching_scales_with_scales B hBpos hB hW hepsilon kappa tau
      hkappa0 hkappa htau0 htau
  have hLrank : L.rank = B.rank := congrArg Finset.card hLfreq
  have hkappa1 : kappa ≤ 1 := hkappa.trans
    (localizedAverageScale_le_one B.rank hW (show 0 < epsilon / 4 by positivity))
  have htau1 : tau ≤ 1 := htau.trans
    ((div_le_self (by positivity) (by norm_num)).trans hkappa1)
  have hkappa1R : (kappa : ℝ) ≤ 1 := by exact_mod_cast hkappa1
  have htau1R : (tau : ℝ) ≤ 1 := by exact_mod_cast htau1
  have hLwidth : L.radius ≤ B.radius / 3 := by
    have h := mul_le_mul_of_nonneg_right hkappa1R B.radius_nonneg
    linarith
  have hSwidth : S.radius ≤ L.radius :=
    hShi.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right htau1R L.radius_nonneg)
  have h6 : Real.exp (-6 : ℝ) ≤ 1 / 6 := by
    have h : (6 : ℝ) ≤ Real.exp 6 := by linarith [Real.add_one_le_exp 6]
    simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num) h
  have h12 : Real.exp (-12 : ℝ) ≤ 1 / 12 := by
    have h : (12 : ℝ) ≤ Real.exp 12 := by linarith [Real.add_one_le_exp 12]
    simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num) h
  have htauLog := coordinatedMatchingScale_exp_lower B.rank hM hcap hP hK hdelta hc hc1 hkappaLog
  have hBnonneg := B.radius_nonneg
  have hLlower : B.radius * Real.exp (-(K + 6)) ≤ L.radius := by
    calc
      _ = Real.exp (-K) * B.radius * Real.exp (-6) := by
        rw [neg_add, Real.exp_add]
        ring
      _ ≤ (kappa : ℝ) * B.radius * (1 / 6) := by gcongr
      _ = (kappa : ℝ) * B.radius / 6 := by ring
      _ ≤ _ := hLlo
  have hSlower : B.radius * Real.exp (-matchingWidthLoss B.rank P K delta c) ≤ S.radius := by
    calc
      _ = Real.exp (-K) * Real.exp (-coordinatedMatchingScaleLoss B.rank P K delta c) *
          B.radius * Real.exp (-12) := by
        unfold matchingWidthLoss
        rw [neg_add, Real.exp_add, neg_add, Real.exp_add]
        ring
      _ ≤ (kappa : ℝ) * (tau : ℝ) * B.radius * (1 / 12) := by gcongr
      _ = (kappa : ℝ) * (tau : ℝ) * B.radius / 12 := by ring
      _ ≤ _ := hSlo
  refine ⟨L, S, hLfreq, hSfreq.trans hLfreq.symm, hLreg, hSreg, hLpos, hSpos,
    hLwidth, hSwidth, hLlower, hSlower, hLB, hSL, ?_, ?_, ?_, hcompare⟩
  · apply hSL.trans
    apply CyclicBohr.Set.carrier_ndilate_mono
    simpa only [hLrank] using hmoment
  · simpa only [hLrank] using hsmall
  · simpa only [hLrank] using herror

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ParentControlledMatching
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_parent_controlled_matching
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular)
    {W A E M P T delta c : ℝ} {scale : ℝ≥0}
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hM : 0 ≤ M) (hMcap : M ≤ Real.exp P) (hP : 0 ≤ P) (hT : 0 ≤ T)
    (hdelta : 0 < delta) (hc : 0 < c) (hc1 : c ≤ 1)
    (hscale : Real.exp (-T) ≤ (scale : ℝ)) :
    let kappa := outerMatchingScale B.rank W (Real.exp (-E)) scale
    let tau := coordinatedMatchingScale B.rank M delta c kappa
    let K := outerMatchingScaleLoss B.rank A E T
    ∃ L S : CyclicBohr.Set N,
      L.frequencies = B.frequencies ∧ S.frequencies = L.frequencies ∧
      L.IsRankRegular ∧ S.IsRankRegular ∧ 0 < L.radius ∧ 0 < S.radius ∧
      L.radius ≤ B.radius / 3 ∧ S.radius ≤ L.radius ∧
      B.radius * Real.exp (-(K + 6)) ≤ L.radius ∧
      B.radius * Real.exp (-matchingWidthLoss B.rank P K delta c) ≤ S.radius ∧
      L.carrier ⊆ (B.ndilate scale).carrier ∧
      S.carrier ⊆ (L.ndilate tau).carrier ∧
      S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M delta)).carrier ∧
      tau + tau ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0) ∧
      M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((tau + tau : ℝ≥0) : ℝ)) ≤ c / 32 ∧
      ∀ a f g : ZMod N → ℝ, (∀ x, |a x| ≤ W) →
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
        |bilinearIntegral B.carrier B.carrier a f g -
          parentTruncatedIntegral B.carrier B.carrier L.carrier S.carrier a f g| ≤ Real.exp (-E) := by
  intro kappa tau K
  have hscale0 : 0 < scale := by exact_mod_cast (Real.exp_pos (-T)).trans_le hscale
  obtain ⟨_, hkappaScale, hkappa⟩ := outerMatchingScale_spec B.rank hW (Real.exp_pos (-E)) hscale0
  have hkappaLog := outerMatchingScale_exp_lower B.rank hW hWcap hA hE hT hscale
  have hK : 0 ≤ K := outerMatchingScaleLoss_nonneg B.rank hA hE hT
  obtain ⟨L, S, hLfreq, hSfreq, hLreg, hSreg, hLpos, hSpos, hLwidth, hSwidth,
      hLlower, hSlower, hLB, hSL, hmoment, hsmall, herror, hcompare⟩ :=
    exists_coordinated_bohr_matching B hBpos hB hW (Real.exp_pos (-E)) hM hMcap hP hK
      hdelta hc hc1 kappa hkappa hkappaLog
  refine ⟨L, S, hLfreq, hSfreq, hLreg, hSreg, hLpos, hSpos, hLwidth, hSwidth,
    hLlower, hSlower, ?_, hSL, hmoment, hsmall, herror, hcompare⟩
  apply hLB.trans
  apply CyclicBohr.Set.carrier_ndilate_mono
  exact (div_le_self (show 0 ≤ kappa by positivity) (by norm_num : (1 : ℝ≥0) ≤ 3)).trans hkappaScale

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.UnbalancedPolynomialBudget
namespace OAI

section

namespace Erdos3.LocalConvolution

open CyclicCrootSisask

theorem unbalancedWidthLoss_nonneg (rank : ℕ) {c p H : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hp : 0 ≤ p) (hH : 0 ≤ H) :
    0 ≤ unbalancedWidthLoss rank c p H := by
  have hK := (almostPeriodicityWidthConstant_pos (show 0 < c / 64 by positivity)).le
  have hE := (unbalancedErrorBudget_spec hc hc1).1
  have hlog : 0 ≤ Real.log (2 + (rank : ℝ)) :=
    Real.log_nonneg (by have hr : (0 : ℝ) ≤ (rank : ℝ) := Nat.cast_nonneg rank; linarith)
  unfold unbalancedWidthLoss
  positivity

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefinementMatchingGeometry
namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.Peeling

open scoped NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.Peeling

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_refinement_matching_geometry
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular)
    (hBwidth : B.radius ≤ 2) (hBrank : 1 ≤ B.rank)
    {W Q E M p H J T R delta : ℝ} {scale : ℝ≥0}
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (hM : 0 ≤ M) (hMcap : M ≤ Real.exp p) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hJ : 0 ≤ J) (hT : 0 ≤ T) (hR : 0 ≤ R) (hdelta : 0 < delta)
    (hBwide : Real.exp (-R) ≤ B.radius) (hscale : Real.exp (-T) ≤ (scale : ℝ)) :
    let c := localMomentGain delta
    let kappa := outerMatchingScale B.rank W (Real.exp (-E)) scale
    let tau := coordinatedMatchingScale B.rank M delta c kappa
    let D := matchingWidthLoss B.rank p (outerMatchingScaleLoss B.rank Q E T) delta c
    let w := B.radius * Real.exp (-refinementMatchingWidthLoss B.rank p H Q E J T delta)
    0 ≤ R + D ∧ ∃ L S : CyclicBohr.Set N,
      L.frequencies = B.frequencies ∧ S.frequencies = L.frequencies ∧
      L.IsRankRegular ∧ S.IsRankRegular ∧ 0 < L.radius ∧ 0 < S.radius ∧
      S.radius ≤ L.radius ∧ S.radius ≤ 1 ∧ 1 ≤ S.rank ∧
      Peeling.admissibleBohrShape B scale (unbalancedRankExtra c p H) w L ∧
      S.carrier ⊆ (B.ndilate scale).carrier ∧
      S.rank + unbalancedRankExtra c p H ≤ B.rank + unbalancedRankExtra c p H ∧
      w ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H Q J) ∧
      Real.exp (-(R + D)) ≤ S.radius ∧
      S.carrier ⊆ (L.ndilate tau).carrier ∧
      S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M delta)).carrier ∧
      tau + tau ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0) ∧
      M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((tau + tau : ℝ≥0) : ℝ)) ≤ c / 32 ∧
      ∀ a f g : ZMod N → ℝ, (∀ x, |a x| ≤ W) →
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
        |bilinearIntegral B.carrier B.carrier a f g -
          parentTruncatedIntegral B.carrier B.carrier L.carrier S.carrier a f g| ≤ Real.exp (-E) := by
  intro c kappa tau D w
  have hc : 0 < c := localMomentGain_pos delta
  have hc1 : c ≤ 1 := (localMomentGain_le_half delta).trans (by norm_num)
  have hp0 : 0 ≤ p := by linarith
  have hK := outerMatchingScaleLoss_nonneg B.rank hQ hE hT
  have hD : 0 ≤ D := matchingWidthLoss_nonneg B.rank hp0 hK hdelta hc hc1
  refine ⟨add_nonneg hR hD, ?_⟩
  obtain ⟨L, S, hLfreq, hSfreq, hLreg, hSreg, hLpos, hSpos,
      hLwidth, hSwidth, hLlower, hSlower, hLB, hSL, hmoment, hsmall, herror, hcompare⟩ :=
    exists_parent_controlled_matching B hBpos hB hW hWcap hQ hE hM hMcap hp0 hT
      hdelta hc hc1 hscale
  have hLrank : L.rank = B.rank := congrArg Finset.card hLfreq
  have hSrank : S.rank = B.rank := congrArg Finset.card (hSfreq.trans hLfreq)
  have hSLbase : S.carrier ⊆ L.carrier := by
    apply CyclicBohr.Set.carrier_mono
    · rw [hSfreq]
    · exact hSwidth
  have hU : 0 ≤ unbalancedReturnWidthLoss B.rank c p H Q J := by
    have h := unbalancedWidthLoss_nonneg B.rank hc hc1 hp0 hH
    unfold unbalancedReturnWidthLoss
    positivity
  have hDlarge : outerMatchingScaleLoss B.rank Q E T + 6 ≤ D := by
    have hEd := (localMomentErrorBudget_spec hdelta).1
    have hEc := (unbalancedErrorBudget_spec hc hc1).1
    have hrank : (0 : ℝ) ≤ B.rank := Nat.cast_nonneg B.rank
    change _ ≤ matchingWidthLoss B.rank p (outerMatchingScaleLoss B.rank Q E T) delta c
    unfold matchingWidthLoss coordinatedMatchingScaleLoss
    linarith
  have hLminimum : w ≤ L.radius := by
    apply le_trans _ hLlower
    apply mul_le_mul_of_nonneg_left _ B.radius_nonneg
    apply Real.exp_le_exp.mpr
    change -(D + unbalancedReturnWidthLoss B.rank c p H Q J) ≤
      -(outerMatchingScaleLoss B.rank Q E T + 6)
    linarith
  have hsuccessorWidth : w ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H Q J) := by
    rw [hSrank]
    calc
      _ = (B.radius * Real.exp (-D)) * Real.exp (-unbalancedReturnWidthLoss B.rank c p H Q J) := by
        change B.radius * Real.exp (-(D + unbalancedReturnWidthLoss B.rank c p H Q J)) = _
        rw [neg_add, Real.exp_add, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right hSlower (Real.exp_nonneg _)
  have hSwide : Real.exp (-(R + D)) ≤ S.radius := by
    calc
      _ = Real.exp (-R) * Real.exp (-D) := by rw [neg_add, Real.exp_add]
      _ ≤ B.radius * Real.exp (-D) := mul_le_mul_of_nonneg_right hBwide (Real.exp_nonneg _)
      _ ≤ _ := hSlower
  refine ⟨L, S, hLfreq, hSfreq, hLreg, hSreg, hLpos, hSpos, hSwidth,
    hSwidth.trans (by linarith), ?_, ⟨hLreg, hLB, ?_, hLminimum⟩,
    hSLbase.trans hLB, ?_, hsuccessorWidth, hSwide, hSL, hmoment, hsmall, herror, hcompare⟩
  · simpa only [hSrank] using hBrank
  · rw [hLrank]
    omega
  · rw [hSrank]

end Erdos3.CellRefinement

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.CellRefinement.exists_refinement_matching_geometry := @OAI.Erdos3.CellRefinement.exists_refinement_matching_geometry
