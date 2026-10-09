-- Prove2me | solution 1 for OAI.Erdos3.LocalConvolution.exists_parent_unbalanced_independent_refinement
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T17:48:56.392972+00:00
-- url     : https://prove2.me/submissions/454fcd5c-b935-405b-afc8-f0adc4bcf1e5

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090
import Theorems.Thm_OAI_Erdos3_LocalConvolution_exists_unbalanced_bohr_second_moment_at_scale

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
namespace OAI

section

open scoped BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*}

theorem cellAverage_nonneg [Add G] (C : Finset G) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (x : G) : 0 ≤ cellAverage C f x :=
  Finset.expect_nonneg (fun c _ => hf (x + c))

theorem cellAverage_le [Add G] {C : Finset G} (hC : C.Nonempty) (f : G → ℝ)
    {M : ℝ} (hf : ∀ x, f x ≤ M) (x : G) : cellAverage C f x ≤ M :=
  (Finset.expect_le_expect (fun c (_ : c ∈ C) => hf (x + c))).trans_eq (Finset.expect_const hC M)

variable [Fintype G] [DecidableEq G]

theorem expect_comp_le_expect_of_support (L : Finset G) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ L → f x = 0)
    (phi : G → G) (hphi : Function.Injective phi) :
    (𝔼 x ∈ L, f (phi x)) ≤ 𝔼 x ∈ L, f x := by
  have hsum : (∑ x ∈ L, f (phi x)) ≤ ∑ x, f x := by
    rw [← Finset.sum_image hphi.injOn]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hf x)
  have htotal : (∑ x ∈ L, f x) = ∑ x, f x :=
    Finset.sum_subset (Finset.subset_univ L) (fun x _ hx => hsupport x hx)
  simp only [Finset.expect_eq_sum_div_card]
  rw [htotal]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg L.card)

variable [AddCommGroup G]

theorem expect_cellAverage_comp_le (L C : Finset G) (hC : C.Nonempty) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ L → f x = 0)
    (phi : G → G) (hphi : Function.Injective phi) :
    (𝔼 x ∈ L, cellAverage C f (phi x)) ≤ 𝔼 x ∈ L, f x := by
  unfold cellAverage
  rw [Finset.expect_comm]
  have h := Finset.expect_le_expect (fun c (_ : c ∈ C) =>
    expect_comp_le_expect_of_support L f hf hsupport (fun x => phi x + c)
      (fun _ _ h => hphi (add_right_cancel h)))
  simpa only [Finset.expect_const hC] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

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

theorem localizedAverageScale_antitone_rank {R epsilon : ℝ}
    (hR : 0 ≤ R) (hepsilon : 0 ≤ epsilon) :
    Antitone (fun rank : ℕ => localizedAverageScale rank R epsilon) := by
  intro a b hab
  have hd : (max a 1 : ℕ) ≤ max b 1 := max_le_max hab le_rfl
  have hdR : ((max a 1 : ℕ) : ℝ) ≤ (max b 1 : ℕ) := by exact_mod_cast hd
  unfold localizedAverageScale
  apply Real.toNNReal_mono
  apply min_le_min
  · apply one_div_le_one_div_of_le (by positivity)
    gcongr
  · apply div_le_div_of_nonneg_left hepsilon (by positivity)
    gcongr

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

theorem reflected_average_sub_le (L : Finset G) (hL : -L = L) (f : G → ℝ) (t : G)
    {M eta : ℝ} (hM : 0 ≤ M) (hf : ∀ x, |f x| ≤ M)
    (hTV : (∑ x, |realUniformMass L (x - t) - realUniformMass L x|) ≤ eta) :
    (𝔼 x ∈ L, f x) - M * eta ≤ 𝔼 x ∈ L, f (-x + t) := by
  rw [expect_neg_add_eq L hL f t]
  have h := (abs_expect_add_sub_le L f t hf).trans (mul_le_mul_of_nonneg_left hTV hM)
  have hlower := (abs_le.mp h).1
  linarith

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ReplacementCellPotential
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem sq_deviation_le_sqrt_gap {x M : ℝ} (hx : 0 ≤ x) (hxM : x ≤ M) :
    (x - 1) ^ 2 ≤ 2 * (1 + Real.sqrt M) ^ 2 * ((1 + x) / 2 - Real.sqrt x) := by
  have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hsq : Real.sqrt x ≤ Real.sqrt M := Real.sqrt_le_sqrt hxM
  have hgap : 0 ≤ (1 + x) / 2 - Real.sqrt x := by
    nlinarith [sq_nonneg (Real.sqrt x - 1)]
  have hfac : 2 * (1 + Real.sqrt x) ^ 2 ≤ 2 * (1 + Real.sqrt M) ^ 2 := by
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg M]
  calc
    (x - 1) ^ 2 = 2 * (1 + Real.sqrt x) ^ 2 * ((1 + x) / 2 - Real.sqrt x) := by
      have hid : ((Real.sqrt x) ^ 2 - 1) ^ 2 =
          2 * (1 + Real.sqrt x) ^ 2 * ((1 + (Real.sqrt x) ^ 2) / 2 - Real.sqrt x) := by
        ring
      simpa only [hsx] using hid
    _ ≤ _ := mul_le_mul_of_nonneg_right hfac hgap

theorem sqrt_average_le_of_second_moment {ι : Type*} [Fintype ι]
    (w X : ι → ℝ) {M c : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hwSum : ∑ i, w i = 1)
    (hX : ∀ i, 0 ≤ X i) (hXM : ∀ i, X i ≤ M)
    (hmean : ∑ i, w i * X i ≤ 1)
    (hsecond : 1 + c ≤ ∑ i, w i * (X i) ^ 2) :
    (∑ i, w i * Real.sqrt (X i)) ≤
      1 - c / (2 * (1 + Real.sqrt M) ^ 2) := by
  have hden : 0 < 2 * (1 + Real.sqrt M) ^ 2 := by
    positivity
  have hvariance : c ≤ ∑ i, w i * (X i - 1) ^ 2 := by
    have heq : (∑ i, w i * (X i - 1) ^ 2) =
        (∑ i, w i * (X i) ^ 2) - 2 * (∑ i, w i * X i) + 1 := by
      calc
        _ = ∑ i, (w i * (X i) ^ 2 - 2 * (w i * X i) + w i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, hwSum]
    rw [heq]
    linarith
  have hbound : (∑ i, w i * (X i - 1) ^ 2) ≤
      2 * (1 + Real.sqrt M) ^ 2 *
        ((1 + ∑ i, w i * X i) / 2 - ∑ i, w i * Real.sqrt (X i)) := by
    calc
      _ ≤ ∑ i, w i * (2 * (1 + Real.sqrt M) ^ 2 *
          ((1 + X i) / 2 - Real.sqrt (X i))) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (sq_deviation_le_sqrt_gap (hX i) (hXM i)) (hw i)
      _ = _ := by
        have hid : ∀ i, w i * (2 * (1 + Real.sqrt M) ^ 2 *
            ((1 + X i) / 2 - Real.sqrt (X i))) =
            2 * (1 + Real.sqrt M) ^ 2 *
              ((w i + w i * X i) / 2 - w i * Real.sqrt (X i)) := by
          intro i
          ring
        simp_rw [hid]
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div,
          Finset.sum_add_distrib, hwSum]
  have hfinal : c ≤ 2 * (1 + Real.sqrt M) ^ 2 *
      (1 - ∑ i, w i * Real.sqrt (X i)) := by
    have hm : (1 + ∑ i, w i * X i) / 2 - ∑ i, w i * Real.sqrt (X i) ≤
        1 - ∑ i, w i * Real.sqrt (X i) := by linarith
    exact hvariance.trans (hbound.trans (mul_le_mul_of_nonneg_left hm hden.le))
  have hdiv : c / (2 * (1 + Real.sqrt M) ^ 2) ≤
      1 - ∑ i, w i * Real.sqrt (X i) := (div_le_iff₀ hden).mpr (by nlinarith)
  linarith

theorem sqrt_average_sq_le {ι : Type*} [Fintype ι] (w X : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwSum : ∑ i, w i = 1) (hX : ∀ i, 0 ≤ X i) :
    (∑ i, w i * Real.sqrt (X i)) ^ 2 ≤ ∑ i, w i * X i := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i ↦ w i * Real.sqrt (X i)) (f := w) (g := fun i ↦ w i * X i)
    (fun i _ ↦ hw i) (fun i _ ↦ mul_nonneg (hw i) (hX i))
    (fun i _ ↦ by rw [mul_pow, Real.sq_sqrt (hX i)]; nlinarith)
  simpa only [hwSum, one_mul] using h

theorem fourth_root_product_average_le {ι : Type*} [Fintype ι]
    (w X Y : ι → ℝ) {M c : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hwSum : ∑ i, w i = 1)
    (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i) (hXM : ∀ i, X i ≤ M)
    (hmeanX : ∑ i, w i * X i ≤ 1) (hmeanY : ∑ i, w i * Y i ≤ 1)
    (hsecond : 1 + c ≤ ∑ i, w i * (X i) ^ 2) :
    (∑ i, w i * (X i * Y i) ^ (1 / 4 : ℝ)) ≤
      1 - c / (4 * (1 + Real.sqrt M) ^ 2) := by
  have hroot (i : ι) : (X i * Y i) ^ (1 / 4 : ℝ) =
      Real.sqrt (Real.sqrt (X i * Y i)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (mul_nonneg (hX i) (hY i))]
    norm_num
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i ↦ w i * (X i * Y i) ^ (1 / 4 : ℝ))
    (f := fun i ↦ w i * Real.sqrt (X i)) (g := fun i ↦ w i * Real.sqrt (Y i))
    (fun i _ ↦ mul_nonneg (hw i) (Real.sqrt_nonneg _))
    (fun i _ ↦ mul_nonneg (hw i) (Real.sqrt_nonneg _)) (fun i _ ↦ by
      rw [hroot, mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sqrt_mul (hX i)]
      exact le_of_eq (by ring))
  have hYsq := sqrt_average_sq_le w Y hw hwSum hY
  have hYmean : (∑ i, w i * Real.sqrt (Y i)) ≤ 1 := by nlinarith
  have hXnonneg : 0 ≤ ∑ i, w i * Real.sqrt (X i) :=
    Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hw i) (Real.sqrt_nonneg _))
  have hprod := mul_le_mul_of_nonneg_left hYmean hXnonneg
  simp only [mul_one] at hprod
  have hXmean := sqrt_average_le_of_second_moment w X hw hwSum hX hXM hmeanX hsecond
  have hsq : (∑ i, w i * (X i * Y i) ^ (1 / 4 : ℝ)) ^ 2 ≤
      1 - c / (2 * (1 + Real.sqrt M) ^ 2) := by
    exact hcs.trans (hprod.trans hXmean)
  have hhalf : c / (4 * (1 + Real.sqrt M) ^ 2) =
      (c / (2 * (1 + Real.sqrt M) ^ 2)) / 2 := by
    rw [div_div]
    congr 1
    ring
  rw [hhalf]
  nlinarith [sq_nonneg ((∑ i, w i * (X i * Y i) ^ (1 / 4 : ℝ)) - 1)]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

end Erdos3.Peeling

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem expect_quarter_product_contraction (S : Finset ι) (hS : S.Nonempty) (X Y : ι → ℝ)
    {M c : ℝ} (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i) (hXM : ∀ i, X i ≤ M)
    (hmeanX : (𝔼 i ∈ S, X i) ≤ 1) (hmeanY : (𝔼 i ∈ S, Y i) ≤ 1)
    (hsecond : 1 + c ≤ 𝔼 i ∈ S, X i ^ 2) :
    (𝔼 i ∈ S, (X i * Y i) ^ (1 / 4 : ℝ)) ≤ 1 - c / (4 * (1 + Real.sqrt M) ^ 2) := by
  have h := fourth_root_product_average_le (realUniformMass S) X Y
    (realUniformMass_nonneg S) (sum_realUniformMass hS) hX hY hXM
    (by simpa only [sum_uniformMass_mul_eq_expect] using hmeanX)
    (by simpa only [sum_uniformMass_mul_eq_expect] using hmeanY)
    (by simpa only [sum_uniformMass_mul_eq_expect] using hsecond)
  simpa only [sum_uniformMass_mul_eq_expect] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem normalized_quarter_potential_contraction
    (S : Finset ι) (hS : S.Nonempty) (U V : ι → ℝ) {u v M c : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hU : ∀ i, 0 ≤ U i) (hV : ∀ i, 0 ≤ V i)
    (hmeanU : (𝔼 i ∈ S, U i) ≤ u) (hmeanV : (𝔼 i ∈ S, V i) ≤ v)
    (hcap : ∀ i, U i / u ≤ M)
    (hsecond : 1 + c ≤ 𝔼 i ∈ S, (U i / u) ^ 2) :
    (𝔼 i ∈ S, (U i * V i) ^ (1 / 4 : ℝ)) ≤
      (1 - c / (4 * (1 + Real.sqrt M) ^ 2)) * (u * v) ^ (1 / 4 : ℝ) := by
  have hX : ∀ i, 0 ≤ U i / u := fun i => div_nonneg (hU i) hu.le
  have hY : ∀ i, 0 ≤ V i / v := fun i => div_nonneg (hV i) hv.le
  have hxmean : (𝔼 i ∈ S, U i / u) ≤ 1 := by
    rw [← Finset.expect_div]
    exact (div_le_one hu).mpr hmeanU
  have hymean : (𝔼 i ∈ S, V i / v) ≤ 1 := by
    rw [← Finset.expect_div]
    exact (div_le_one hv).mpr hmeanV
  have h := expect_quarter_product_contraction S hS (fun i => U i / u) (fun i => V i / v)
    hX hY hcap hxmean hymean hsecond
  have hpoint (i : ι) : (U i * V i) ^ (1 / 4 : ℝ) =
      (u * v) ^ (1 / 4 : ℝ) * ((U i / u) * (V i / v)) ^ (1 / 4 : ℝ) := by
    rw [← Real.mul_rpow (mul_nonneg hu.le hv.le) (mul_nonneg (hX i) (hY i))]
    congr 1
    field_simp
  calc
    _ = (u * v) ^ (1 / 4 : ℝ) *
        (𝔼 i ∈ S, ((U i / u) * (V i / v)) ^ (1 / 4 : ℝ)) := by
      simp_rw [hpoint]
      rw [← Finset.mul_expect]
    _ ≤ (u * v) ^ (1 / 4 : ℝ) * (1 - c / (4 * (1 + Real.sqrt M) ^ 2)) :=
      mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (mul_nonneg hu.le hv.le) _)
    _ = _ := mul_comm _ _

theorem normalized_quarter_potential_contraction_either
    (S : Finset ι) (hS : S.Nonempty) (U V : ι → ℝ) {u v M c : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hU : ∀ i, 0 ≤ U i) (hV : ∀ i, 0 ≤ V i)
    (hmeanU : (𝔼 i ∈ S, U i) ≤ u) (hmeanV : (𝔼 i ∈ S, V i) ≤ v)
    (hcapU : ∀ i, U i / u ≤ M) (hcapV : ∀ i, V i / v ≤ M)
    (hsecond : (1 + c ≤ 𝔼 i ∈ S, (U i / u) ^ 2) ∨
      (1 + c ≤ 𝔼 i ∈ S, (V i / v) ^ 2)) :
    (𝔼 i ∈ S, (U i * V i) ^ (1 / 4 : ℝ)) ≤
      (1 - c / (4 * (1 + Real.sqrt M) ^ 2)) * (u * v) ^ (1 / 4 : ℝ) := by
  rcases hsecond with hsecond | hsecond
  · exact normalized_quarter_potential_contraction S hS U V hu hv hU hV hmeanU hmeanV hcapU hsecond
  · simpa only [mul_comm] using
      normalized_quarter_potential_contraction S hS V U hv hu hV hU hmeanV hmeanU hcapV hsecond

theorem quarter_contraction_factor_bounds {M c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    3 / 4 ≤ 1 - c / (4 * (1 + Real.sqrt M) ^ 2) ∧
      1 - c / (4 * (1 + Real.sqrt M) ^ 2) < 1 := by
  have hden : 0 < 4 * (1 + Real.sqrt M) ^ 2 := by positivity
  have hratio : c / (4 * (1 + Real.sqrt M) ^ 2) ≤ 1 / 4 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [Real.sqrt_nonneg M, sq_nonneg (Real.sqrt M)]
  have hpos := div_pos hc hden
  constructor <;> linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem normalized_cell_cap {a u u₀ c₀ K : ℝ}
    (hu : 0 < u) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hlower : c₀ * u ≤ u₀) (hcell : a ≤ K * u) : a / u₀ ≤ K / c₀ := by
  have hu₀ : 0 < u₀ := (mul_pos hc₀ hu).trans_le hlower
  apply (div_le_div_iff₀ hu₀ hc₀).mpr
  nlinarith [mul_le_mul_of_nonneg_left hlower hK,
    mul_le_mul_of_nonneg_right hcell hc₀.le]

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

variable [Fintype G] [DecidableEq G]

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalWeightCaps
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
theorem cellAverage_le_shifted (C : Finset G) (f F : G → ℝ) (x : G)
    (hF : ∀ r, F r ≤ f (x + r)) (z : G) :
    cellAverage C F z ≤ cellAverage C f (x + z) := by
  unfold cellAverage
  apply Finset.expect_le_expect
  intro c _
  simpa only [add_assoc] using hF (z + c)

omit [Fintype G] [DecidableEq G] in
theorem normalized_local_cell_cap (C : Finset G) (f F : G → ℝ) (x : G)
    (hF : ∀ r, F r ≤ f (x + r)) {u u₀ c₀ K : ℝ}
    (hu : 0 < u) (hc₀ : 0 < c₀) (hK : 0 ≤ K) (hlower : c₀ * u ≤ u₀)
    (hparent : ∀ z, cellAverage C f z ≤ K * u) (z : G) :
    cellAverage C F z / u₀ ≤ K / c₀ :=
  normalized_cell_cap hu hc₀ hK hlower ((cellAverage_le_shifted C f F x hF z).trans
    (hparent (x + z)))

end Erdos3

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

omit [AddCommGroup G] [Fintype G] [DecidableEq G] in
theorem matchedCellSpace_nonempty {L S : Finset G} (hL : L.Nonempty) (hS : S.Nonempty) :
    (matchedCellSpace L S).Nonempty := hL.product (hS.product hS)

omit [Fintype G] [DecidableEq G] in
theorem expect_matchedFirstCell (L S C : Finset G) (hS : S.Nonempty) (f : G → ℝ) :
    (𝔼 z ∈ matchedCellSpace L S, matchedFirstCell C f z) = 𝔼 r ∈ L, cellAverage C f r := by
  simp only [matchedCellSpace, Finset.expect_product, matchedFirstCell, Finset.expect_const hS]

theorem mean_matchedFirstCell_le (L S C : Finset G) (hS : S.Nonempty) (hC : C.Nonempty)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ L → f x = 0) :
    (𝔼 z ∈ matchedCellSpace L S, matchedFirstCell C f z) ≤ 𝔼 r ∈ L, f r := by
  rw [expect_matchedFirstCell L S C hS]
  exact expect_cellAverage_comp_le L C hC f hf hsupport id Function.injective_id

theorem mean_matchedSecondCell_le (L S C : Finset G) (hS : S.Nonempty) (hC : C.Nonempty)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ L → f x = 0) :
    (𝔼 z ∈ matchedCellSpace L S, matchedSecondCell C f z) ≤ 𝔼 r ∈ L, f r := by
  have hpoint (s t : G) : (𝔼 r ∈ L, cellAverage C f (-r + s + t)) ≤ 𝔼 r ∈ L, f r :=
    expect_cellAverage_comp_le L C hC f hf hsupport (fun r => -r + s + t)
      (fun _ _ h => neg_injective (add_right_cancel (add_right_cancel h)))
  have h := Finset.expect_le_expect (fun s (_ : s ∈ S) =>
    Finset.expect_le_expect (fun t (_ : t ∈ S) => hpoint s t))
  simp only [Finset.expect_const hS] at h
  simp only [matchedCellSpace, Finset.expect_product, matchedSecondCell]
  have horder : (𝔼 r ∈ L, 𝔼 s ∈ S, 𝔼 t ∈ S, cellAverage C f (-r + s + t)) =
      𝔼 s ∈ S, 𝔼 t ∈ S, 𝔼 r ∈ L, cellAverage C f (-r + s + t) := by
    rw [Finset.expect_comm L S]
    apply Finset.expect_congr rfl
    intro s _
    exact Finset.expect_comm L S _
  rwa [horder]

end Erdos3

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

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

theorem matchedPairAverage_eq_space (L S : Finset G) (F : G → G → ℝ) :
    matchedPairAverage L S F =
      𝔼 z ∈ matchedCellSpace L S, F z.1 (-z.1 + z.2.1 + z.2.2) := by
  simp only [matchedPairAverage, matchedCellSpace, Finset.expect_product]

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

variable [Fintype G] [DecidableEq G]

theorem abs_matchedPairAverage_shift_sub_le
    (L S : Finset G) (hL : L.Nonempty) (hS : S.Nonempty) (F : G → G → ℝ)
    (u v : G) {M etaL etaS : ℝ} (hM : 0 ≤ M) (hF : ∀ x y, |F x y| ≤ M)
    (hLshift : (∑ x, |realUniformMass L (x - u) - realUniformMass L x|) ≤ etaL)
    (hSshift : (∑ x, |realUniformMass S (x - (u + v)) - realUniformMass S x|) ≤ etaS) :
    |matchedPairAverage L S (fun x y => F (x + u) (y + v)) -
      matchedPairAverage L S F| ≤ M * (etaL + etaS) := by
  have horder (H : G → G → ℝ) : matchedPairAverage L S H =
      𝔼 t ∈ S, 𝔼 r ∈ L, 𝔼 s ∈ S, H r (-r + s + t) := by
    unfold matchedPairAverage
    have hin (r : G) : (𝔼 s ∈ S, 𝔼 t ∈ S, H r (-r + s + t)) =
        𝔼 t ∈ S, 𝔼 s ∈ S, H r (-r + s + t) := Finset.expect_comm S S _
    simp_rw [hin]
    exact Finset.expect_comm L S _
  rw [horder, horder]
  apply abs_expect_sub_expect_le S hS
  intro t _
  have h := abs_expect_pair_add_sub_le L S hL hS (fun r s => F r (-r + s + t))
    u (u + v) hM (fun r s => hF r (-r + s + t)) hLshift hSshift
  have heq (r s : G) : -(r + u) + (s + (u + v)) + t = (-r + s + t) + v := by abel
  simpa only [heq] using h

end Erdos3.CellRefinement

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
theorem cellAverage_div (C : Finset G) (f : G → ℝ) (u : ℝ) (x : G) :
    cellAverage C (fun y => f y / u) x = cellAverage C f x / u :=
  (Finset.expect_div C (fun c => f (x + c)) u).symm

theorem matchedSecondCell_second_moment_ge
    (L S C : Finset G) (hL : -L = L) (hS : S.Nonempty) (hC : C.Nonempty)
    (f : G → ℝ) {M eta : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hTV : ∀ s ∈ S, ∀ t ∈ S,
      (∑ x, |realUniformMass L (x - (s + t)) - realUniformMass L x|) ≤ eta) :
    (𝔼 x ∈ L, cellAverage C f x ^ 2) - M ^ 2 * eta ≤
      𝔼 z ∈ matchedCellSpace L S, matchedSecondCell C f z ^ 2 := by
  have hbound (x : G) : |cellAverage C f x ^ 2| ≤ M ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (cellAverage_nonneg C f (fun y => (hf y).1) x)
      (cellAverage_le hC f (fun y => (hf y).2) x) 2
  have hshift (s : G) (hs : s ∈ S) (t : G) (ht : t ∈ S) :
      (𝔼 x ∈ L, cellAverage C f x ^ 2) - M ^ 2 * eta ≤
        𝔼 x ∈ L, cellAverage C f (-x + s + t) ^ 2 := by
    simpa only [add_assoc] using reflected_average_sub_le L hL
      (fun x => cellAverage C f x ^ 2) (s + t) (sq_nonneg M) hbound (hTV s hs t ht)
  have h := Finset.expect_le_expect (fun s (hs : s ∈ S) =>
    Finset.expect_le_expect (fun t (ht : t ∈ S) => hshift s hs t ht))
  simp only [Finset.expect_const hS] at h
  simp only [matchedCellSpace, Finset.expect_product, matchedSecondCell]
  have horder : (𝔼 x ∈ L, 𝔼 s ∈ S, 𝔼 t ∈ S, cellAverage C f (-x + s + t) ^ 2) =
      𝔼 s ∈ S, 𝔼 t ∈ S, 𝔼 x ∈ L, cellAverage C f (-x + s + t) ^ 2 := by
    rw [Finset.expect_comm L S]
    apply Finset.expect_congr rfl
    intro s _
    exact Finset.expect_comm L S _
  rwa [horder]

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

theorem matchedIndependentAverage_eq_average (L S C : Finset G) (F : G → G → ℝ) :
    matchedIndependentAverage L S C F =
      matchedPairAverage L S (fun x y => 𝔼 u ∈ C, 𝔼 v ∈ C, F (x + u) (y + v)) := by
  unfold matchedIndependentAverage
  simp_rw [expect_matchedPairAverage]

variable [DecidableEq G]

theorem matchedIndependentAverage_eq_cells (L S C : Finset G) (a f g : G → ℝ) :
    matchedIndependentAverage L S C (fun x y => f x * g y * a (x + y)) =
      𝔼 z ∈ matchedCellSpace L S,
        bilinearIntegral (C.image (fun t => z.1 + t))
          (C.image (fun t => (-z.1 + z.2.1 + z.2.2) + t)) a f g := by
  rw [matchedIndependentAverage_eq_average, matchedPairAverage_eq_space]
  apply Finset.expect_congr rfl
  intro z _
  unfold bilinearIntegral
  rw [Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)]
  apply Finset.expect_congr rfl
  intro u _
  rw [Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)]

variable [Fintype G]

theorem abs_matchedIndependentAverage_sub_le
    (L S C : Finset G) (hL : L.Nonempty) (hS : S.Nonempty) (hC : C.Nonempty)
    (F : G → G → ℝ) {M etaL etaS : ℝ} (hM : 0 ≤ M) (hF : ∀ x y, |F x y| ≤ M)
    (hLshift : ∀ u ∈ C, (∑ x, |realUniformMass L (x - u) - realUniformMass L x|) ≤ etaL)
    (hSshift : ∀ u ∈ C, ∀ v ∈ C,
      (∑ x, |realUniformMass S (x - (u + v)) - realUniformMass S x|) ≤ etaS) :
    |matchedIndependentAverage L S C F - matchedPairAverage L S F| ≤ M * (etaL + etaS) := by
  calc
    _ = |(𝔼 u ∈ C, 𝔼 v ∈ C, matchedPairAverage L S (fun x y => F (x + u) (y + v))) -
        𝔼 _u ∈ C, 𝔼 _v ∈ C, matchedPairAverage L S F| := by
      rw [Finset.expect_const hC, Finset.expect_const hC]
      rfl
    _ ≤ M * (etaL + etaS) := by
      apply abs_expect_sub_expect_le C hC
      intro u hu
      apply abs_expect_sub_expect_le C hC
      intro v hv
      exact abs_matchedPairAverage_shift_sub_le L S hL hS F u v hM hF
        (hLshift u hu) (hSshift u hu v hv)

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G]

variable [Fintype G] [DecidableEq G]

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

variable [DecidableEq G]

variable [Fintype G]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MatchedPotentialContraction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem matched_potential_contraction
    (L S C : Finset G) (hL : L.Nonempty) (hLsymm : -L = L)
    (hS : S.Nonempty) (hC : C.Nonempty) (f g : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ L → f x = 0) (hgsupport : ∀ x, x ∉ L → g x = 0)
    {u v M K c eta : ℝ} (hu : 0 < u) (hv : 0 < v) (heta : 0 ≤ eta)
    (hmeanf : (𝔼 x ∈ L, f x) ≤ u) (hmeang : (𝔼 x ∈ L, g x) ≤ v)
    (hcapg : ∀ x, g x / v ≤ M)
    (hcellf : ∀ x, cellAverage C f x / u ≤ K)
    (hcellg : ∀ x, cellAverage C g x / v ≤ K)
    (hTV : ∀ s ∈ S, ∀ t ∈ S,
      (∑ x, |realUniformMass L (x - (s + t)) - realUniformMass L x|) ≤ eta)
    (hsecond :
      (1 + c + M ^ 2 * eta ≤ 𝔼 x ∈ L, cellAverage C (fun y => f y / u) x ^ 2) ∨
      (1 + c + M ^ 2 * eta ≤ 𝔼 x ∈ L, cellAverage C (fun y => g y / v) x ^ 2)) :
    (𝔼 z ∈ matchedCellSpace L S,
      (matchedFirstCell C f z * matchedSecondCell C g z) ^ (1 / 4 : ℝ)) ≤
      (1 - c / (4 * (1 + Real.sqrt K) ^ 2)) * (u * v) ^ (1 / 4 : ℝ) := by
  apply normalized_quarter_potential_contraction_either (matchedCellSpace L S)
    (matchedCellSpace_nonempty hL hS) (matchedFirstCell C f) (matchedSecondCell C g) hu hv
    (fun z => cellAverage_nonneg C f hf z.1)
    (fun z => cellAverage_nonneg C g hg (-z.1 + z.2.1 + z.2.2))
    ((mean_matchedFirstCell_le L S C hS hC f hf hfsupport).trans hmeanf)
    ((mean_matchedSecondCell_le L S C hS hC g hg hgsupport).trans hmeang)
    (fun z => hcellf z.1) (fun z => hcellg (-z.1 + z.2.1 + z.2.2))
  rcases hsecond with hsecond | hsecond
  · left
    have heq :
        (𝔼 z ∈ matchedCellSpace L S, (matchedFirstCell C f z / u) ^ 2) =
          𝔼 x ∈ L, cellAverage C (fun y => f y / u) x ^ 2 := by
      simp only [matchedCellSpace, Finset.expect_product, matchedFirstCell,
        cellAverage_div, Finset.expect_const hS]
    rw [heq]
    linarith [mul_nonneg (sq_nonneg M) heta]
  · right
    have hnormg : ∀ x, 0 ≤ g x / v ∧ g x / v ≤ M :=
      fun x => ⟨div_nonneg (hg x) hv.le, hcapg x⟩
    have hshift := matchedSecondCell_second_moment_ge L S C hLsymm hS hC
      (fun y => g y / v) hnormg hTV
    have heq :
        (𝔼 z ∈ matchedCellSpace L S, matchedSecondCell C (fun y => g y / v) z ^ 2) =
          𝔼 z ∈ matchedCellSpace L S, (matchedSecondCell C g z / v) ^ 2 := by
      simp only [matchedSecondCell, cellAverage_div]
    rw [heq] at hshift
    linarith

end Erdos3

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

theorem bohr_matched_independent_integral_error
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular) (hS : S.IsRankRegular)
    (C : Finset (ZMod N)) (hC : C.Nonempty) {ell sigma : ℝ≥0}
    (hCL : C ⊆ (L.ndilate ell).carrier) (hCS : C ⊆ (S.ndilate sigma).carrier)
    (hell : ell ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hsigma : sigma + sigma ≤ 1 / (100 * (2 * max S.rank 1 : ℕ) : ℝ≥0))
    (a f g : ZMod N → ℝ) {M : ℝ} (hM : 0 ≤ M) (ha : ∀ x, |a x| ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    |(𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
        bilinearIntegral (C.image (fun t => z.1 + t))
          (C.image (fun t => (-z.1 + z.2.1 + z.2.2) + t)) a f g) -
      matchedIntegral L.carrier S.carrier a f g| ≤
      M * (400 * (max L.rank 1 : ℕ) * (ell : ℝ) +
        400 * (max S.rank 1 : ℕ) * ((sigma + sigma : ℝ≥0) : ℝ)) := by
  have hfirst : ∀ u ∈ C,
      (∑ x, |realUniformMass L.carrier (x - u) - realUniformMass L.carrier x|) ≤
        400 * (max L.rank 1 : ℕ) * (ell : ℝ) := by
    intro u hu
    exact CyclicBohr.Set.uniformMass_translation_le_of_rankRegular hL hell (hCL hu)
  have hsecond : ∀ u ∈ C, ∀ v ∈ C,
      (∑ x, |realUniformMass S.carrier (x - (u + v)) - realUniformMass S.carrier x|) ≤
        400 * (max S.rank 1 : ℕ) * ((sigma + sigma : ℝ≥0) : ℝ) := by
    intro u hu v hv
    exact CyclicBohr.Set.uniformMass_translation_le_of_rankRegular hS hsigma
      (CyclicBohr.Set.add_mem_ndilate (hCS hu) (hCS hv))
  have h := abs_matchedIndependentAverage_sub_le L.carrier S.carrier C L.carrier_nonempty
    S.carrier_nonempty hC (fun x y => f x * g y * a (x + y)) hM
    (fun x y => abs_unit_weighted_mul_le (hf x) (hg y) (ha (x + y))) hfirst hsecond
  rw [matchedIndependentAverage_eq_cells] at h
  exact h

end Erdos3.CellRefinement

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

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped NNReal

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

theorem independentReturnScale_spec (rank : ℕ) {M epsilon : ℝ}
    (hM : 0 ≤ M) (hepsilon : 0 < epsilon) :
    0 < independentReturnScale rank M epsilon ∧
      independentReturnScale rank M epsilon ≤ 1 ∧
      independentReturnScale rank M epsilon + independentReturnScale rank M epsilon ≤
        1 / (100 * (2 * max rank 1 : ℕ) : ℝ≥0) ∧
      M * (400 * (max rank 1 : ℕ) * (independentReturnScale rank M epsilon : ℝ) +
        400 * (max rank 1 : ℕ) *
          ((independentReturnScale rank M epsilon + independentReturnScale rank M epsilon : ℝ≥0) : ℝ)) ≤
        epsilon := by
  obtain ⟨hr, hsmall, herror⟩ := localizedAverageScale_spec rank hM
    (show 0 < epsilon / 2 by positivity)
  have heq : independentReturnScale rank M epsilon + independentReturnScale rank M epsilon =
      localizedAverageScale rank M (epsilon / 2) := by
    unfold independentReturnScale
    ring
  have hone : independentReturnScale rank M epsilon ≤ 1 := by
    change localizedAverageScale rank M (epsilon / 2) / 2 ≤ 1
    exact (div_le_self (by positivity) (by norm_num : (1 : ℝ≥0) ≤ 2)).trans
      (localizedAverageScale_le_one rank hM (show 0 < epsilon / 2 by positivity))
  refine ⟨div_pos hr (by norm_num), hone, ?_, ?_⟩
  · rwa [heq]
  · rw [heq]
    change M * (400 * (max rank 1 : ℕ) *
      ((localizedAverageScale rank M (epsilon / 2) : ℝ) / 2) +
      400 * (max rank 1 : ℕ) * (localizedAverageScale rank M (epsilon / 2) : ℝ)) ≤ epsilon
    nlinarith

theorem independentReturnScale_exp_lower (rank : ℕ) {M A E : ℝ}
    (hM : 0 ≤ M) (hcap : M ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    Real.exp (-((rank : ℝ) + A + E + 1602)) ≤
      (independentReturnScale rank M (Real.exp (-E)) : ℝ) := by
  have hbase := localizedAverageScale_exp_lower rank hM hcap hA hE
  have htwo : Real.exp (-2 : ℝ) ≤ 1 / 2 := by
    have h : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
    simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num) h
  calc
    _ = Real.exp (-((rank : ℝ) + A + E + 1600)) * Real.exp (-2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ (localizedAverageScale rank M (Real.exp (-E) / 2) : ℝ) * (1 / 2) :=
      mul_le_mul hbase htwo (Real.exp_nonneg _) (by positivity)
    _ = _ := by
      change _ = (localizedAverageScale rank M (Real.exp (-E) / 2) : ℝ) / 2
      ring

variable {N : ℕ} [NeZero N]

theorem bohr_matched_independent_at_return_scale
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular) (hS : S.IsRankRegular)
    (hfreq : S.frequencies = L.frequencies) (hwidth : S.radius ≤ L.radius)
    (C : Finset (ZMod N)) (hC : C.Nonempty)
    (a f g : ZMod N → ℝ) {M epsilon : ℝ} (hM : 0 ≤ M) (hepsilon : 0 < epsilon)
    (hCS : C ⊆ (S.ndilate (independentReturnScale S.rank M epsilon)).carrier)
    (ha : ∀ x, |a x| ≤ M) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    |(𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
        bilinearIntegral (C.image (fun t => z.1 + t))
          (C.image (fun t => (-z.1 + z.2.1 + z.2.2) + t)) a f g) -
      matchedIntegral L.carrier S.carrier a f g| ≤ epsilon := by
  let zeta := independentReturnScale S.rank M epsilon
  have hrank : L.rank = S.rank := (congrArg Finset.card hfreq).symm
  have hSL : (S.ndilate zeta).carrier ⊆ (L.ndilate zeta).carrier := by
    apply CyclicBohr.Set.carrier_mono
    · change L.frequencies ⊆ S.frequencies
      rw [hfreq]
    · simp only [CyclicBohr.Set.radius_ndilate]
      exact mul_le_mul_of_nonneg_left hwidth zeta.coe_nonneg
  obtain ⟨_, _, hsmall, herror⟩ := independentReturnScale_spec S.rank hM hepsilon
  have hell : zeta ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0) := by
    rw [hrank]
    exact le_trans le_self_add hsmall
  have h := bohr_matched_independent_integral_error L S hL hS C hC (hCS.trans hSL) hCS
    hell hsmall a f g hM ha hf hg
  rw [hrank] at h
  exact h.trans herror

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

theorem unbalanced_power_gap {c : ℝ} (hc : 0 < c) {q : ℕ} (hq : 0 < q) :
    c / 2 ≤ (1 + c) ^ q - (1 + c / 2) ^ q := by
  have h : ∀ n : ℕ, c / 2 ≤ (1 + c) ^ (n + 1) - (1 + c / 2) ^ (n + 1) := by
    intro n
    induction n with
    | zero => norm_num; linarith
    | succ n ih =>
      have hd : 0 ≤ (1 + c) ^ (n + 1) - (1 + c / 2) ^ (n + 1) := by linarith
      have hb : 0 ≤ (1 + c / 2) ^ (n + 1) := pow_nonneg (by linarith) _
      have hmul := mul_nonneg hc.le hd
      have hmul' := mul_nonneg hc.le hb
      change c / 2 ≤ (1 + c) ^ ((n + 1) + 1) - (1 + c / 2) ^ ((n + 1) + 1)
      rw [pow_succ (1 + c) (n + 1), pow_succ (1 + c / 2) (n + 1)]
      nlinarith
  cases q with
  | zero => omega
  | succ n => exact h n

theorem unbalancedErrorBudget_spec {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    0 ≤ unbalancedErrorBudget c ∧ Real.exp (-unbalancedErrorBudget c) / 2 = c / 64 := by
  constructor
  · unfold unbalancedErrorBudget
    apply neg_nonneg.mpr
    exact Real.log_nonpos (by positivity) (by linarith)
  · unfold unbalancedErrorBudget
    rw [neg_neg, Real.exp_log (by positivity)]
    ring

theorem unbalancedMinimumWidth_exp_lower {N : ℕ} [NeZero N]
    (S : CyclicBohr.Set N) {M c p H : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hc1 : c ≤ 1) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hcap : M ≤ Real.exp p) {q : ℕ} (hq : 0 < q) (hqp : (q : ℝ) ≤ H * p) :
    S.radius * Real.exp (-unbalancedWidthLoss S.rank c p H) ≤
      unbalancedMinimumWidth S M c p H q := by
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨hE, hEeq⟩ := unbalancedErrorBudget_spec hc hc1
  have hMpow : M ^ (2 * q) ≤ Real.exp (2 * H * p ^ 2) := by
    calc
      _ ≤ (Real.exp p) ^ (2 * q) := pow_le_pow_left₀ hM hcap _
      _ = Real.exp (((2 * q : ℕ) : ℝ) * p) := by rw [Real.exp_nat_mul]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith [mul_le_mul_of_nonneg_right hqp hp0]
  have hMtwo : M ^ 2 ≤ Real.exp (2 * p) := by
    calc
      _ ≤ (Real.exp p) ^ 2 := pow_le_pow_left₀ hM hcap _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have heps : Real.exp (-unbalancedErrorBudget c) / 2 ≤
      (1 + c) ^ q - (1 + c / 2) ^ q := by
    rw [hEeq]
    exact (show c / 64 ≤ c / 2 by linarith).trans (unbalanced_power_gap hc hq)
  have hκ := localizedAverageScale_exp_lower_of_error S.rank (pow_nonneg hM (2 * q))
    hMpow (by positivity : 0 ≤ 2 * H * p ^ 2) hE heps
  have hσ := localizedAverageScale_exp_lower_of_error (S.rank + unbalancedRankExtra c p H)
    (sq_nonneg M) hMtwo (by positivity : 0 ≤ 2 * p) hE hEeq.le
  have h8 : Real.exp (-8 : ℝ) ≤ 1 / 8 := by
    have h : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp 8]
    simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num) h
  let a := (S.rank : ℝ) + 2 * H * p ^ 2 + unbalancedErrorBudget c + 1600
  let b := ((S.rank + unbalancedRankExtra c p H : ℕ) : ℝ) + 2 * p + unbalancedErrorBudget c + 1600
  let t := almostPeriodicityWidthConstant (c / 64) *
    (1 + (3 * H + 1) * p ^ 2 + Real.log (2 + S.rank))
  have hSnonneg := S.radius_nonneg
  have hexp : Real.exp (-(a + b + 8 + t)) =
      Real.exp (-a) * Real.exp (-b) * Real.exp (-8) * Real.exp (-t) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  change S.radius * Real.exp (-(a + b + 8 + t)) ≤ _
  calc
    _ = Real.exp (-a) * Real.exp (-b) * S.radius * Real.exp (-8) * Real.exp (-t) := by
      rw [hexp]
      ring
    _ ≤ (localizedAverageScale S.rank (M ^ (2 * q)) ((1 + c) ^ q - (1 + c / 2) ^ q) : ℝ) *
        (localizedAverageScale (S.rank + unbalancedRankExtra c p H) (M ^ 2) (c / 64) : ℝ) *
        S.radius * (1 / 8) * Real.exp (-t) := by gcongr
    _ = _ := by unfold unbalancedMinimumWidth; dsimp only [t]; ring

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrMatchedContraction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Pointwise NNReal

variable {N : ℕ} [NeZero N]

theorem bohr_matched_potential_contraction
    (L : CyclicBohr.Set N) (hL : L.IsRankRegular) (S C : Finset (ZMod N))
    (hS : S.Nonempty) (hC : C.Nonempty) {kappa : ℝ≥0}
    (hSL : S ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f g : ZMod N → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ L.carrier → f x = 0)
    (hgsupport : ∀ x, x ∉ L.carrier → g x = 0)
    {u v M K c : ℝ} (hu : 0 < u) (hv : 0 < v) (hc : 0 < c) (hc1 : c ≤ 1)
    (hmeanf : (𝔼 x ∈ L.carrier, f x) ≤ u) (hmeang : (𝔼 x ∈ L.carrier, g x) ≤ v)
    (hcapg : ∀ x, g x / v ≤ M)
    (hcellf : ∀ x, cellAverage C f x / u ≤ K)
    (hcellg : ∀ x, cellAverage C g x / v ≤ K)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ c / 2)
    (hsecond : (1 + c ≤ 𝔼 x ∈ L.carrier, cellAverage C (fun y => f y / u) x ^ 2) ∨
      (1 + c ≤ 𝔼 x ∈ L.carrier, cellAverage C (fun y => g y / v) x ^ 2)) :
    let rho := 1 - c / (8 * (1 + Real.sqrt K) ^ 2)
    3 / 4 ≤ rho ∧ rho < 1 ∧
      (𝔼 z ∈ matchedCellSpace L.carrier S,
        (matchedFirstCell C f z * matchedSecondCell C g z) ^ (1 / 4 : ℝ)) ≤
        rho * (u * v) ^ (1 / 4 : ℝ) := by
  intro rho
  let eta : ℝ := 400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)
  have heta : 0 ≤ eta := by dsimp [eta]; positivity
  have hsymm : -L.carrier = L.carrier := by
    ext x
    constructor
    · intro h
      obtain ⟨y, hy, rfl⟩ := Finset.mem_neg.mp h
      exact (L.neg_mem_iff y).2 hy
    · intro h
      exact Finset.mem_neg.mpr ⟨-x, (L.neg_mem_iff x).2 h, neg_neg x⟩
  have hTV : ∀ s ∈ S, ∀ t ∈ S,
      (∑ x, |realUniformMass L.carrier (x - (s + t)) - realUniformMass L.carrier x|) ≤ eta := by
    intro s hs t ht
    exact CyclicBohr.Set.uniformMass_translation_le_of_rankRegular hL hkappa
      (CyclicBohr.Set.add_mem_ndilate (hSL hs) (hSL ht))
  have hsecond' :
      (1 + c / 2 + M ^ 2 * eta ≤ 𝔼 x ∈ L.carrier, cellAverage C (fun y => f y / u) x ^ 2) ∨
      (1 + c / 2 + M ^ 2 * eta ≤ 𝔼 x ∈ L.carrier, cellAverage C (fun y => g y / v) x ^ 2) := by
    change M ^ 2 * eta ≤ c / 2 at herror
    rcases hsecond with hsecond | hsecond
    · left; linarith
    · right; linarith
  have h := matched_potential_contraction L.carrier S C L.carrier_nonempty hsymm hS hC f g hf hg
    hfsupport hgsupport hu hv heta hmeanf hmeang hcapg hcellf hcellg hTV hsecond'
  have heq : c / 2 / (4 * (1 + Real.sqrt K) ^ 2) = c / (8 * (1 + Real.sqrt K) ^ 2) := by
    rw [div_div]
    congr 1
    ring
  rw [heq] at h
  have hbounds := quarter_contraction_factor_bounds (M := K) (c := c / 2)
    (by linarith) (by linarith)
  rw [heq] at hbounds
  exact ⟨hbounds.1, hbounds.2, h⟩

end Erdos3

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

theorem exists_small_scale_unbalanced_shape
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    {kappa₀ : ℝ≥0} (hSL : S.carrier ⊆ (L.ndilate kappa₀).carrier)
    (hkappa₀ : kappa₀ ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f : ZMod N → ℝ) (hsupport : ∀ x, x ∉ L.carrier → f x = 0)
    {M c p H : ℝ} (hM : 0 < M) (hc : 0 < c) (hc1 : c ≤ 1)
    (hp : 1 ≤ p) (hH : 0 ≤ H) (hcap : M ≤ Real.exp p)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hboundary : 200 * (max L.rank 1 : ℕ) * (kappa₀ : ℝ) * M ^ 2 ≤ c / 64)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier f f) q)
    (hseparation : (1 + c / 4) ^ q ≤ (c / 64) / 2 * (1 + c / 2) ^ q)
    (zeta : ℝ≥0) (hzeta : 0 < zeta) (hzeta1 : zeta ≤ 1) :
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape S zeta (unbalancedRankExtra c p H)
        ((zeta : ℝ) * S.radius * Real.exp (-unbalancedWidthLoss S.rank c p H)) C ∧
      0 < C.radius ∧ C.radius ≤ 1 ∧
      1 + c / 16 ≤ 𝔼 x ∈ L.carrier, cellAverage C.carrier f x ^ 2 := by
  let kappa := localizedAverageScale S.rank (M ^ (2 * q))
    ((1 + c) ^ q - (1 + c / 2) ^ q)
  have hgap : 0 < (1 + c) ^ q - (1 + c / 2) ^ q :=
    lt_of_lt_of_le (by positivity : 0 < c / 2) (unbalanced_power_gap hc hq)
  have hkappa : 0 < kappa := (localizedAverageScale_spec S.rank
    (pow_nonneg hM.le _) hgap).1
  have hkappa1 : kappa ≤ 1 := localizedAverageScale_le_one S.rank
    (pow_nonneg hM.le _) hgap
  have hscale : zeta * kappa ≤ kappa := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hzeta1 (show 0 ≤ kappa by positivity)
  have hsmall : zeta * kappa ≤ zeta := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hkappa1 (show 0 ≤ zeta by positivity)
  obtain ⟨C, hCreg, hCpos, hCwidth, _, hCS, hrank, hwidth, hsecond⟩ :=
    exists_unbalanced_bohr_second_moment_at_scale L S hL hSpos hSwidth hSreg hSrank
      hSL hkappa₀ f hsupport hM hc hc1 hp hH hcap hf hboundary q hq heven hqp
      hlarge hseparation (zeta * kappa) (mul_pos hzeta hkappa) hscale
  have hbound : C.rank ≤ S.rank + unbalancedRankExtra c p H := by
    have hceil := Nat.le_ceil
      (almostPeriodicityWidthConstant (c / 64) * (1 + (3 * H + 1) * p ^ 2) ^ 4)
    have hreal : (C.rank : ℝ) ≤ (S.rank : ℝ) + (unbalancedRankExtra c p H : ℝ) :=
      hrank.trans (add_le_add le_rfl hceil)
    exact_mod_cast hreal
  have hσ := localizedAverageScale_antitone_rank (sq_nonneg M)
    (show 0 ≤ c / 64 by positivity) hbound
  have hσR : (localizedAverageScale (S.rank + unbalancedRankExtra c p H) (M ^ 2) (c / 64) : ℝ) ≤
      (localizedAverageScale C.rank (M ^ 2) (c / 64) : ℝ) := by exact_mod_cast hσ
  have hminimum : (zeta : ℝ) * unbalancedMinimumWidth S M c p H q ≤ C.radius := by
    apply le_trans _ hwidth
    rw [NNReal.coe_mul]
    unfold unbalancedMinimumWidth
    dsimp only [kappa]
    calc
      _ = ((zeta : ℝ) * (localizedAverageScale S.rank (M ^ (2 * q))
          ((1 + c) ^ q - (1 + c / 2) ^ q) : ℝ)) *
          (localizedAverageScale (S.rank + unbalancedRankExtra c p H) (M ^ 2) (c / 64) : ℝ) *
          S.radius / 8 * Real.exp (-(almostPeriodicityWidthConstant (c / 64) *
            (1 + (3 * H + 1) * p ^ 2 + Real.log (2 + S.rank)))) := by ring
      _ ≤ _ := by gcongr
  refine ⟨C, ⟨hCreg, hCS.trans (CyclicBohr.Set.carrier_ndilate_mono hsmall),
    hbound, ?_⟩, hCpos, hCwidth, hsecond⟩
  have h := mul_le_mul_of_nonneg_left
    (unbalancedMinimumWidth_exp_lower S hM.le hc hc1 hp hH hcap hq hqp) zeta.coe_nonneg
  simpa only [← mul_assoc] using h.trans hminimum

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_small_scale_unbalanced_contraction
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    {kappa : ℝ≥0} (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f g : ZMod N → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ L.carrier → f x = 0)
    (hgsupport : ∀ x, x ∉ L.carrier → g x = 0)
    {u v M K c p H : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hmeanf : (𝔼 x ∈ L.carrier, f x) ≤ u) (hmeang : (𝔼 x ∈ L.carrier, g x) ≤ v)
    (hM : 0 < M) (hc : 0 < c) (hc1 : c ≤ 1) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hMcap : M ≤ Real.exp p) (hcapf : ∀ x, f x / u ≤ M) (hcapg : ∀ x, g x / v ≤ M)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ c / 32)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (h : ZMod N → ℝ) (hchoice : h = (fun x => f x / u) ∨ h = (fun x => g x / v))
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier h h) q)
    (hseparation : (1 + c / 4) ^ q ≤ (c / 64) / 2 * (1 + c / 2) ^ q)
    (zeta : ℝ≥0) (hzeta : 0 < zeta) (hzeta1 : zeta ≤ 1)
    (hcells : ∀ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape S zeta (unbalancedRankExtra c p H)
        ((zeta : ℝ) * S.radius * Real.exp (-unbalancedWidthLoss S.rank c p H)) C →
      (∀ x, cellAverage C.carrier f x / u ≤ K) ∧
        (∀ x, cellAverage C.carrier g x / v ≤ K)) :
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape S zeta (unbalancedRankExtra c p H)
        ((zeta : ℝ) * S.radius * Real.exp (-unbalancedWidthLoss S.rank c p H)) C ∧
      0 < C.radius ∧ C.radius ≤ 1 ∧
      let rho := 1 - c / (128 * (1 + Real.sqrt K) ^ 2)
      3 / 4 ≤ rho ∧ rho < 1 ∧
        (𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
          (matchedFirstCell C.carrier f z * matchedSecondCell C.carrier g z) ^ (1 / 4 : ℝ)) ≤
          rho * (u * v) ^ (1 / 4 : ℝ) := by
  have hkappa₀ : kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0) :=
    le_trans le_self_add hkappa
  have hboundary : 200 * (max L.rank 1 : ℕ) * (kappa : ℝ) * M ^ 2 ≤ c / 64 := by
    have heq : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) =
        4 * (200 * (max L.rank 1 : ℕ) * (kappa : ℝ) * M ^ 2) := by
      rw [NNReal.coe_add]
      ring
    rw [heq] at herror
    linarith
  have hdata : (∀ x, x ∉ L.carrier → h x = 0) ∧ (∀ x, 0 ≤ h x ∧ h x ≤ M) := by
    rcases hchoice with rfl | rfl
    · exact ⟨fun x hx => by dsimp only; rw [hfsupport x hx, zero_div],
        fun x => ⟨div_nonneg (hf x) hu.le, hcapf x⟩⟩
    · exact ⟨fun x hx => by dsimp only; rw [hgsupport x hx, zero_div],
        fun x => ⟨div_nonneg (hg x) hv.le, hcapg x⟩⟩
  obtain ⟨C, hshape, hCpos, hCwidth, hsecond⟩ :=
    exists_small_scale_unbalanced_shape L S hL hSpos hSwidth hSreg hSrank hSL hkappa₀
      h hdata.1 hM hc hc1 hp hH hMcap hdata.2 hboundary q hq heven hqp hlarge hseparation
      zeta hzeta hzeta1
  have hsecond' :
      (1 + c / 16 ≤ 𝔼 x ∈ L.carrier, cellAverage C.carrier (fun y => f y / u) x ^ 2) ∨
      (1 + c / 16 ≤ 𝔼 x ∈ L.carrier, cellAverage C.carrier (fun y => g y / v) x ^ 2) := by
    rcases hchoice with hchoice | hchoice
    · exact Or.inl (by simpa only [hchoice] using hsecond)
    · exact Or.inr (by simpa only [hchoice] using hsecond)
  have hcontraction := bohr_matched_potential_contraction L hL S.carrier C.carrier
    S.carrier_nonempty C.carrier_nonempty hSL hkappa f g hf hg hfsupport hgsupport
    hu hv (show 0 < c / 16 by positivity) (show c / 16 ≤ 1 by linarith)
    hmeanf hmeang hcapg (hcells C hshape).1 (hcells C hshape).2
    (by convert herror using 1; ring) hsecond'
  refine ⟨C, hshape, hCpos, hCwidth, ?_⟩
  have heq : c / 16 / (8 * (1 + Real.sqrt K) ^ 2) =
      c / (128 * (1 + Real.sqrt K) ^ 2) := by
    rw [div_div]
    congr 1
    ring
  simpa only [heq] using hcontraction

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

theorem unbalanced_return_width_lower {N : ℕ} [NeZero N]
    (S : CyclicBohr.Set N) (c p H : ℝ) {W A E : ℝ}
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H A E) ≤
      (CellRefinement.independentReturnScale S.rank W (Real.exp (-E)) : ℝ) * S.radius *
        Real.exp (-unbalancedWidthLoss S.rank c p H) := by
  have h := CellRefinement.independentReturnScale_exp_lower S.rank hW hWcap hA hE
  calc
    _ = Real.exp (-((S.rank : ℝ) + A + E + 1602)) * S.radius *
        Real.exp (-unbalancedWidthLoss S.rank c p H) := by
      unfold unbalancedReturnWidthLoss
      rw [neg_add, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h S.radius_nonneg) (Real.exp_nonneg _)

variable {N : ℕ} [NeZero N]

theorem exists_unbalanced_independent_refinement
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    (hfreq : S.frequencies = L.frequencies) (hwidth : S.radius ≤ L.radius)
    {kappa : ℝ≥0} (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f g : ZMod N → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hfsupport : ∀ x, x ∉ L.carrier → f x = 0)
    (hgsupport : ∀ x, x ∉ L.carrier → g x = 0)
    {u v M K c p H : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hmeanf : (𝔼 x ∈ L.carrier, f x) ≤ u) (hmeang : (𝔼 x ∈ L.carrier, g x) ≤ v)
    (hM : 0 < M) (hc : 0 < c) (hc1 : c ≤ 1) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hMcap : M ≤ Real.exp p) (hcapf : ∀ x, f x / u ≤ M) (hcapg : ∀ x, g x / v ≤ M)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ c / 32)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (h : ZMod N → ℝ) (hchoice : h = (fun x => f x / u) ∨ h = (fun x => g x / v))
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier h h) q)
    (hseparation : (1 + c / 4) ^ q ≤ (c / 64) / 2 * (1 + c / 2) ^ q)
    {W A E : ℝ} (hW : 0 ≤ W) (hWcap : W ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hcells : ∀ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape S (CellRefinement.independentReturnScale S.rank W (Real.exp (-E))) (unbalancedRankExtra c p H)
        (S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H A E)) C →
      (∀ x, cellAverage C.carrier f x / u ≤ K) ∧
        (∀ x, cellAverage C.carrier g x / v ≤ K)) :
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape S (CellRefinement.independentReturnScale S.rank W (Real.exp (-E))) (unbalancedRankExtra c p H)
        (S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H A E)) C ∧
      0 < C.radius ∧ C.radius ≤ 1 ∧
      (let rho := 1 - c / (128 * (1 + Real.sqrt K) ^ 2)
      3 / 4 ≤ rho ∧ rho < 1 ∧
        (𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
          (matchedFirstCell C.carrier f z * matchedSecondCell C.carrier g z) ^ (1 / 4 : ℝ)) ≤
          rho * (u * v) ^ (1 / 4 : ℝ)) ∧
      ∀ a : ZMod N → ℝ, (∀ x, |a x| ≤ W) →
        |(𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
            CellRefinement.bilinearIntegral (C.carrier.image (fun t => z.1 + t))
              (C.carrier.image (fun t => (-z.1 + z.2.1 + z.2.2) + t)) a f g) -
          CellRefinement.matchedIntegral L.carrier S.carrier a f g| ≤ Real.exp (-E) := by
  let zeta := CellRefinement.independentReturnScale S.rank W (Real.exp (-E))
  obtain ⟨hzeta, hzeta1, _, _⟩ := CellRefinement.independentReturnScale_spec S.rank hW
    (Real.exp_pos (-E))
  have hconvert (C : CyclicBohr.Set N)
      (hshape : Peeling.admissibleBohrShape S zeta (unbalancedRankExtra c p H)
        ((zeta : ℝ) * S.radius * Real.exp (-unbalancedWidthLoss S.rank c p H)) C) :
      Peeling.admissibleBohrShape S zeta (unbalancedRankExtra c p H)
        (S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H A E)) C :=
    ⟨hshape.1, hshape.2.1, hshape.2.2.1,
      (unbalanced_return_width_lower S c p H hW hWcap hA hE).trans hshape.2.2.2⟩
  obtain ⟨C, hshape, hCpos, hCwidth, hcontraction⟩ :=
    exists_small_scale_unbalanced_contraction L S hL hSpos hSwidth hSreg hSrank hSL hkappa
      f g (fun x => (hf x).1) (fun x => (hg x).1) hfsupport hgsupport hu hv hmeanf hmeang
      hM hc hc1 hp hH hMcap hcapf hcapg herror q hq heven hqp h hchoice hlarge hseparation
      zeta hzeta hzeta1 (fun C hC => hcells C (hconvert C hC))
  refine ⟨C, hconvert C hshape, hCpos, hCwidth, hcontraction, ?_⟩
  intro a ha
  exact CellRefinement.bohr_matched_independent_at_return_scale L S hL hSreg hfreq hwidth
    C.carrier C.carrier_nonempty a f g hW (Real.exp_pos (-E)) hshape.2.1 ha hf hg

end Erdos3.LocalConvolution

end

section

namespace Erdos3.Peeling

open scoped NNReal

variable {N : ℕ} [NeZero N]

theorem admissibleBohrShape_transfer
    {B S C : CyclicBohr.Set N} {scaleB scaleS : ℝ≥0}
    {extraB extraS : ℕ} {widthB widthS : ℝ}
    (hsub : (S.ndilate scaleS).carrier ⊆ (B.ndilate scaleB).carrier)
    (hrank : S.rank + extraS ≤ B.rank + extraB) (hwidth : widthB ≤ widthS)
    (hC : admissibleBohrShape S scaleS extraS widthS C) :
    admissibleBohrShape B scaleB extraB widthB C :=
  ⟨hC.1, hC.2.1.trans hsub, hC.2.2.1.trans hrank, hwidth.trans hC.2.2.2⟩

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

theorem exists_parent_unbalanced_independent_refinement
    (B L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    (hfreq : S.frequencies = L.frequencies) (hlocalWidth : S.radius ≤ L.radius)
    {kappa scale : ℝ≥0} {extra : ℕ} {minimumWidth c p H W A E : ℝ}
    (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hSB : S.carrier ⊆ (B.ndilate scale).carrier)
    (hrank : S.rank + unbalancedRankExtra c p H ≤ B.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H A E))
    (F G f g : ZMod N → ℝ) (x y : ZMod N)
    (hdomf : ∀ r, f r ≤ F (x + r)) (hdomg : ∀ r, g r ≤ G (y + r))
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1)
    (hfsupport : ∀ r, r ∉ L.carrier → f r = 0)
    (hgsupport : ∀ r, r ∉ L.carrier → g r = 0)
    {U V u v M K c₀ : ℝ} (hU : 0 < U) (hV : 0 < V) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hlowerf : c₀ * U ≤ u) (hlowerg : c₀ * V ≤ v)
    (hmeanf : (𝔼 r ∈ L.carrier, f r) ≤ u) (hmeang : (𝔼 r ∈ L.carrier, g r) ≤ v)
    (hparentF : ∀ C, Peeling.admissibleBohrShape B scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier F z ≤ K * U)
    (hparentG : ∀ C, Peeling.admissibleBohrShape B scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier G z ≤ K * V)
    (hM : 0 < M) (hc : 0 < c) (hc1 : c ≤ 1) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hMcap : M ≤ Real.exp p) (hcapf : ∀ r, f r / u ≤ M) (hcapg : ∀ r, g r / v ≤ M)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ c / 32)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (h : ZMod N → ℝ) (hchoice : h = (fun r => f r / u) ∨ h = (fun r => g r / v))
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier h h) q)
    (hseparation : (1 + c / 4) ^ q ≤ (c / 64) / 2 * (1 + c / 2) ^ q)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape B scale extra minimumWidth C ∧
      Peeling.admissibleBohrShape S
        (CellRefinement.independentReturnScale S.rank W (Real.exp (-E))) (unbalancedRankExtra c p H)
        (S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H A E)) C ∧
      0 < C.radius ∧ C.radius ≤ 1 ∧
      (let rho := 1 - c / (128 * (1 + Real.sqrt (K / c₀)) ^ 2)
      3 / 4 ≤ rho ∧ rho < 1 ∧
        (𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
          (matchedFirstCell C.carrier f z * matchedSecondCell C.carrier g z) ^ (1 / 4 : ℝ)) ≤
          rho * (u * v) ^ (1 / 4 : ℝ)) ∧
      ∀ a : ZMod N → ℝ, (∀ r, |a r| ≤ W) →
        |(𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
            CellRefinement.bilinearIntegral (C.carrier.image (fun t => z.1 + t))
              (C.carrier.image (fun t => (-z.1 + z.2.1 + z.2.2) + t)) a f g) -
          CellRefinement.matchedIntegral L.carrier S.carrier a f g| ≤ Real.exp (-E) := by
  have hu : 0 < u := (mul_pos hc₀ hU).trans_le hlowerf
  have hv : 0 < v := (mul_pos hc₀ hV).trans_le hlowerg
  let zeta := CellRefinement.independentReturnScale S.rank W (Real.exp (-E))
  have hzeta1 : zeta ≤ 1 :=
    (CellRefinement.independentReturnScale_spec S.rank hW (Real.exp_pos (-E))).2.1
  have hsub : (S.ndilate zeta).carrier ⊆ (B.ndilate scale).carrier := by
    have h := CyclicBohr.Set.carrier_ndilate_mono (B := S) hzeta1
    rw [CyclicBohr.Set.ndilate_one] at h
    exact h.trans hSB
  have hconvert (C : CyclicBohr.Set N)
      (hC : Peeling.admissibleBohrShape S zeta (unbalancedRankExtra c p H)
        (S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H A E)) C) :
      Peeling.admissibleBohrShape B scale extra minimumWidth C :=
    Peeling.admissibleBohrShape_transfer hsub hrank hwidth hC
  have hcells (C : CyclicBohr.Set N)
      (hC : Peeling.admissibleBohrShape S zeta (unbalancedRankExtra c p H)
        (S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H A E)) C) :
      (∀ r, cellAverage C.carrier f r / u ≤ K / c₀) ∧
        (∀ r, cellAverage C.carrier g r / v ≤ K / c₀) := by
    exact ⟨fun r => normalized_local_cell_cap C.carrier F f x hdomf hU hc₀ hK hlowerf
        (hparentF C (hconvert C hC)) r,
      fun r => normalized_local_cell_cap C.carrier G g y hdomg hV hc₀ hK hlowerg
        (hparentG C (hconvert C hC)) r⟩
  obtain ⟨C, hshape, hCpos, hCwidth, hcontraction, hintegral⟩ :=
    exists_unbalanced_independent_refinement L S hL hSpos hSwidth hSreg hSrank hfreq hlocalWidth
      hSL hkappa f g hf hg hfsupport hgsupport hu hv hmeanf hmeang hM hc hc1 hp hH
      hMcap hcapf hcapg herror q hq heven hqp h hchoice hlarge hseparation hW hWcap hA hE hcells
  exact ⟨C, hconvert C hshape, hshape, hCpos, hCwidth, hcontraction, hintegral⟩

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CellRefinement

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.LocalConvolution.exists_parent_unbalanced_independent_refinement := @OAI.Erdos3.LocalConvolution.exists_parent_unbalanced_independent_refinement
