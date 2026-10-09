-- Prove2me | solution 1 for OAI.Erdos3.CellRefinement.capped_parent_bound_of_children
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T01:01:32.955599+00:00
-- url     : https://prove2.me/submissions/81378cee-8da1-404b-ae89-9b62a3bf3245

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B034
import Theorems.Thm_OAI_Erdos3_CellRefinement_capped_center_alternatives

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

theorem sqrt_average_sq_le {ι : Type*} [Fintype ι] (w X : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwSum : ∑ i, w i = 1) (hX : ∀ i, 0 ≤ X i) :
    (∑ i, w i * Real.sqrt (X i)) ^ 2 ≤ ∑ i, w i * X i := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i ↦ w i * Real.sqrt (X i)) (f := w) (g := fun i ↦ w i * X i)
    (fun i _ ↦ hw i) (fun i _ ↦ mul_nonneg (hw i) (hX i))
    (fun i _ ↦ by rw [mul_pow, Real.sq_sqrt (hX i)]; nlinarith)
  simpa only [hwSum, one_mul] using h

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

theorem fourth_root_product_average_le_means {ι : Type*} [Fintype ι]
    (w X Y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwSum : ∑ i, w i = 1)
    (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i) :
    (∑ i, w i * (X i * Y i) ^ (1 / 4 : ℝ)) ≤
      ((∑ i, w i * X i) * ∑ i, w i * Y i) ^ (1 / 4 : ℝ) := by
  have hroot (i : ι) : (X i * Y i) ^ (1 / 4 : ℝ) =
      Real.sqrt (Real.sqrt (X i * Y i)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (mul_nonneg (hX i) (hY i))]
    norm_num
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i => w i * (X i * Y i) ^ (1 / 4 : ℝ))
    (f := fun i => w i * Real.sqrt (X i)) (g := fun i => w i * Real.sqrt (Y i))
    (fun i _ => mul_nonneg (hw i) (Real.sqrt_nonneg _))
    (fun i _ => mul_nonneg (hw i) (Real.sqrt_nonneg _)) (fun i _ => by
      rw [hroot, mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sqrt_mul (hX i)]
      exact le_of_eq (by ring))
  have hXs := sqrt_average_sq_le w X hw hwSum hX
  have hYs := sqrt_average_sq_le w Y hw hwSum hY
  have hXm : 0 ≤ ∑ i, w i * X i := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hX i))
  have hYm : 0 ≤ ∑ i, w i * Y i := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hY i))
  have hprod := mul_le_mul hXs hYs (sq_nonneg _) hXm
  have hfour := pow_le_pow_left₀ (sq_nonneg _) hcs 2
  have hfour' : (∑ i, w i * (X i * Y i) ^ (1 / 4 : ℝ)) ^ 4 ≤
      (∑ i, w i * X i) * ∑ i, w i * Y i := by
    nlinarith
  have hrootPow : (((∑ i, w i * X i) * ∑ i, w i * Y i) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) =
      (∑ i, w i * X i) * ∑ i, w i * Y i := by
    simpa only [Nat.cast_ofNat, one_div] using
      Real.rpow_inv_natCast_pow (mul_nonneg hXm hYm) (by norm_num : (4 : ℕ) ≠ 0)
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
    (Real.rpow_nonneg (mul_nonneg hXm hYm) (1 / 4 : ℝ))
  rwa [hrootPow]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem expect_quarter_product_le (S : Finset ι) (hS : S.Nonempty) (X Y : ι → ℝ)
    (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i) {u v : ℝ}
    (hu : (𝔼 i ∈ S, X i) ≤ u) (hv : (𝔼 i ∈ S, Y i) ≤ v) :
    (𝔼 i ∈ S, (X i * Y i) ^ (1 / 4 : ℝ)) ≤ (u * v) ^ (1 / 4 : ℝ) := by
  have h := fourth_root_product_average_le_means (realUniformMass S) X Y
    (realUniformMass_nonneg S) (sum_realUniformMass hS) hX hY
  simp only [sum_uniformMass_mul_eq_expect] at h
  apply h.trans
  apply Real.rpow_le_rpow
  · exact mul_nonneg (Finset.expect_nonneg (fun i _ => hX i)) (Finset.expect_nonneg (fun i _ => hY i))
  · exact mul_le_mul hu hv (Finset.expect_nonneg (fun i _ => hY i))
      ((Finset.expect_nonneg (fun i _ => hX i)).trans hu)
  · norm_num

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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

theorem parent_cell_potential_le {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (B L : Finset G) (hB : B.Nonempty) (hL : L.Nonempty)
    (f g : G → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0) :
    (𝔼 x ∈ B, 𝔼 y ∈ B, (cellAverage L f x * cellAverage L g y) ^ (1 / 4 : ℝ)) ≤
      ((𝔼 x ∈ B, f x) * (𝔼 y ∈ B, g y)) ^ (1 / 4 : ℝ) := by
  have hfmean := expect_cellAverage_comp_le B L hL f hf hfsupport id Function.injective_id
  have hgmean := expect_cellAverage_comp_le B L hL g hg hgsupport id Function.injective_id
  have h := expect_quarter_product_le (B ×ˢ B) (hB.product hB)
    (fun z => cellAverage L f z.1) (fun z => cellAverage L g z.2)
    (fun z => cellAverage_nonneg L f hf z.1) (fun z => cellAverage_nonneg L g hg z.2)
    (u := 𝔼 x ∈ B, f x) (v := 𝔼 y ∈ B, g y)
    (by simpa only [id_eq, Finset.expect_product, Finset.expect_const hB] using hfmean)
    (by simpa only [id_eq, Finset.expect_product, Finset.expect_const hB] using hgmean)
  simpa only [Finset.expect_product] using h

theorem small_ratio_quarter_potential_le {a b u v c₀ K : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hc₀ : 0 ≤ c₀) (hK : 0 ≤ K) (hau : a ≤ c₀ * u) (hbv : b ≤ K * v)
    (hsmall : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2) :
    (a * b) ^ (1 / 4 : ℝ) ≤ (u * v) ^ (1 / 4 : ℝ) / 2 := by
  have hab : a * b ≤ (c₀ * K) * (u * v) := by
    nlinarith [mul_le_mul hau hbv hb (mul_nonneg hc₀ hu)]
  calc
    _ ≤ ((c₀ * K) * (u * v)) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (mul_nonneg ha hb) hab (by norm_num)
    _ = (c₀ * K) ^ (1 / 4 : ℝ) * (u * v) ^ (1 / 4 : ℝ) :=
      Real.mul_rpow (mul_nonneg hc₀ hK) (mul_nonneg hu hv)
    _ ≤ (1 / 2) * (u * v) ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg (mul_nonneg hu hv) _)
    _ = _ := by ring

theorem combine_matched_potential_contractions {A B Phi rho : ℝ}
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (hsmall : A ≤ Phi / 2) (htotal : A + B ≤ Phi) :
    A + rho * B ≤ ((1 + rho) / 2) * Phi := by
  nlinarith [mul_le_mul_of_nonneg_left htotal hrho,
    mul_le_mul_of_nonneg_left hsmall (sub_nonneg.mpr hrho1)]

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

omit [Fintype G] in
theorem translated_slice_le (L : Finset G) (f : G → ℝ) (hf : ∀ r, 0 ≤ f r)
    (x r : G) : Peeling.slice L (fun t => f (x + t)) r ≤ f (x + r) := by
  by_cases hr : r ∈ L <;> simp [Peeling.slice, hr, hf]

omit [Fintype G] in
theorem translated_slice_nonneg (L : Finset G) (f : G → ℝ) (hf : ∀ r, 0 ≤ f r)
    (x r : G) : 0 ≤ Peeling.slice L (fun t => f (x + t)) r := by
  by_cases hr : r ∈ L <;> simp [Peeling.slice, hr, hf]

omit [Fintype G] in
theorem expect_translated_slice (L : Finset G) (f : G → ℝ) (x : G) :
    (𝔼 r ∈ L, Peeling.slice L (fun t => f (x + t)) r) = cellAverage L f x := by
  apply Finset.expect_congr rfl
  intro r hr
  simp only [Peeling.slice, hr, ite_true]

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

theorem matched_cell_potential_le (L S C : Finset G)
    (hL : L.Nonempty) (hS : S.Nonempty) (hC : C.Nonempty)
    (f g : G → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ L → f x = 0) (hgsupport : ∀ x, x ∉ L → g x = 0) :
    (𝔼 z ∈ matchedCellSpace L S,
      (matchedFirstCell C f z * matchedSecondCell C g z) ^ (1 / 4 : ℝ)) ≤
      ((𝔼 r ∈ L, f r) * (𝔼 r ∈ L, g r)) ^ (1 / 4 : ℝ) := by
  exact expect_quarter_product_le (matchedCellSpace L S) (matchedCellSpace_nonempty hL hS)
    (matchedFirstCell C f) (matchedSecondCell C g)
    (fun z => cellAverage_nonneg C f hf z.1)
    (fun z => cellAverage_nonneg C g hg (-z.1 + z.2.1 + z.2.2))
    (mean_matchedFirstCell_le L S C hS hC f hf hfsupport)
    (mean_matchedSecondCell_le L S C hS hC g hg hgsupport)

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

theorem bilinearIntegral_restrict (A B : Finset G) (a f g : G → ℝ) :
    bilinearIntegral A B a (Peeling.slice A f) (Peeling.slice B g) =
      bilinearIntegral A B a f g := by
  apply Finset.expect_congr rfl
  intro x hx
  apply Finset.expect_congr rfl
  intro y hy
  simp only [Peeling.slice, hx, hy, ite_true]

theorem bilinearIntegral_translate (A B : Finset G) (a f g : G → ℝ) (x₀ y₀ : G) :
    bilinearIntegral (A.image (fun x => x₀ + x)) (B.image (fun y => y₀ + y)) a f g =
      bilinearIntegral A B (fun z => a (x₀ + y₀ + z)) (fun x => f (x₀ + x))
        (fun y => g (y₀ + y)) := by
  unfold bilinearIntegral
  rw [Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)]
  apply Finset.expect_congr rfl
  intro x _
  rw [Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)]
  apply Finset.expect_congr rfl
  intro y _
  have heq : x₀ + x + (y₀ + y) = x₀ + y₀ + (x + y) := by abel
  rw [heq]

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

theorem centerSlice_bounds (L : Finset G) (f : G → ℝ)
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (x r : G) :
    0 ≤ centerSlice L f x r ∧ centerSlice L f x r ≤ 1 := by
  exact ⟨translated_slice_nonneg L f (fun t => (hf t).1) x r,
    (translated_slice_le L f (fun t => (hf t).1) x r).trans (hf (x + r)).2⟩

theorem centerSlice_supported (L : Finset G) (f : G → ℝ) (x : G) :
    ∀ r, r ∉ L → centerSlice L f x r = 0 := by
  intro r hr
  simp only [centerSlice, Peeling.slice, hr, ite_false]

theorem centerSlice_mean (L : Finset G) (f : G → ℝ) (x : G) :
    (𝔼 r ∈ L, centerSlice L f x r) = cellAverage L f x :=
  expect_translated_slice L f x

theorem centerMatchedIntegral_mean (B L S : Finset G) (a f g : G → ℝ) :
    (𝔼 z ∈ B ×ˢ B, centerMatchedIntegral L S a f g z) =
      parentTruncatedIntegral B B L S a f g := by
  rw [Finset.expect_product]
  rfl

omit [DecidableEq G] in
theorem centerPotential_nonneg (L : Finset G) (f g : G → ℝ)
    (hf : ∀ r, 0 ≤ f r) (hg : ∀ r, 0 ≤ g r) (z : G × G) :
    0 ≤ centerPotential L f g z :=
  Real.rpow_nonneg (mul_nonneg (cellAverage_nonneg L f hf z.1) (cellAverage_nonneg L g hg z.2)) _

variable [Fintype G]

theorem centerPotential_mean_le (B L : Finset G) (hB : B.Nonempty) (hL : L.Nonempty)
    (f g : G → ℝ) (hf : ∀ r, 0 ≤ f r) (hg : ∀ r, 0 ≤ g r)
    (hfsupport : ∀ r, r ∉ B → f r = 0) (hgsupport : ∀ r, r ∉ B → g r = 0) :
    (𝔼 z ∈ B ×ˢ B, centerPotential L f g z) ≤
      ((𝔼 r ∈ B, f r) * (𝔼 r ∈ B, g r)) ^ (1 / 4 : ℝ) := by
  simpa only [Finset.expect_product, centerPotential] using
    parent_cell_potential_le B L hB hL f g hf hg hfsupport hgsupport

theorem centerChildPotential_le (L S C : Finset G)
    (hL : L.Nonempty) (hS : S.Nonempty) (hC : C.Nonempty)
    (f g : G → ℝ) (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1)
    (z : G × G) : centerChildPotential L S f g z C ≤ centerPotential L f g z := by
  have h := matched_cell_potential_le L S C hL hS hC (centerSlice L f z.1) (centerSlice L g z.2)
    (fun r => (centerSlice_bounds L f hf z.1 r).1) (fun r => (centerSlice_bounds L g hg z.2 r).1)
    (centerSlice_supported L f z.1) (centerSlice_supported L g z.2)
  simpa only [centerChildPotential, centerPotential, centerSlice_mean] using h

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem bilinearIntegral_translated_centerSlices (C : Finset G) (a f g : G → ℝ) (x y : G) :
    bilinearIntegral (C.image (fun r => x + r)) (C.image (fun r => y + r)) a f g =
      bilinearIntegral C C (fun r => a (x + y + r)) (centerSlice C f x) (centerSlice C g y) := by
  rw [bilinearIntegral_translate]
  exact (bilinearIntegral_restrict C C (fun r => a (x + y + r))
    (fun r => f (x + r)) (fun r => g (y + r))).symm

theorem centerChildIntegral_eq_rebased (L S C : Finset G) (a f g : G → ℝ) (z : G × G) :
    centerChildIntegral L S a f g z C =
      𝔼 t ∈ matchedCellSpace L S,
        bilinearIntegral C C (fun r => a (z.1 + z.2 + (t.2.1 + t.2.2) + r))
          (centerSlice C (centerSlice L f z.1) t.1)
          (centerSlice C (centerSlice L g z.2) (-t.1 + t.2.1 + t.2.2)) := by
  unfold centerChildIntegral
  apply Finset.expect_congr rfl
  intro t _
  rw [bilinearIntegral_translated_centerSlices]
  congr 1
  funext r
  congr 1
  abel

theorem centerChildPotential_eq_rebased (L S C : Finset G) (f g : G → ℝ) (z : G × G) :
    centerChildPotential L S f g z C =
      𝔼 t ∈ matchedCellSpace L S,
        ((𝔼 r ∈ C, centerSlice C (centerSlice L f z.1) t.1 r) *
          (𝔼 r ∈ C, centerSlice C (centerSlice L g z.2) (-t.1 + t.2.1 + t.2.2) r)) ^ (1 / 4 : ℝ) := by
  simp only [centerSlice_mean, centerChildPotential, matchedFirstCell, matchedSecondCell]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

variable [DecidableEq G]

theorem centerChildIntegral_le_of_cellBilinearBound
    (L S C : Finset G) (a f g : G → ℝ) (origin : G) (z : G × G) {T : ℝ}
    (hbound : CellBilinearBound C a T)
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1) :
    centerChildIntegral L S (fun r => a (origin + r)) f g z C ≤
      T * centerChildPotential L S f g z C := by
  rw [centerChildIntegral_eq_rebased, centerChildPotential_eq_rebased]
  calc
    _ ≤ 𝔼 t ∈ matchedCellSpace L S,
        T * ((𝔼 r ∈ C, centerSlice C (centerSlice L f z.1) t.1 r) *
          (𝔼 r ∈ C, centerSlice C (centerSlice L g z.2) (-t.1 + t.2.1 + t.2.2) r)) ^ (1 / 4 : ℝ) := by
      apply Finset.expect_le_expect
      intro t _
      have h := hbound (origin + (z.1 + z.2 + (t.2.1 + t.2.2)))
        (centerSlice C (centerSlice L f z.1) t.1)
        (centerSlice C (centerSlice L g z.2) (-t.1 + t.2.1 + t.2.2))
        (centerSlice_bounds C _ (centerSlice_bounds L f hf z.1) t.1)
        (centerSlice_bounds C _ (centerSlice_bounds L g hg z.2) (-t.1 + t.2.1 + t.2.2))
        (centerSlice_supported C _ t.1)
        (centerSlice_supported C _ (-t.1 + t.2.1 + t.2.2))
      simpa only [add_assoc] using h
    _ = _ := (Finset.mul_expect _ _ T).symm

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ReturnShapeWidthBudget
namespace OAI

section

namespace Erdos3.LocalConvolution

open CyclicCrootSisask

theorem two_le_unbalancedWidthLoss (rank : ℕ) {c p H : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hp : 0 ≤ p) (hH : 0 ≤ H) :
    2 ≤ unbalancedWidthLoss rank c p H := by
  have hE := (unbalancedErrorBudget_spec hc hc1).1
  have hK := (almostPeriodicityWidthConstant_pos (show 0 < c / 64 by positivity)).le
  have hlog : 0 ≤ Real.log (2 + (rank : ℝ)) :=
    Real.log_nonneg (by have hrank : (0 : ℝ) ≤ rank := Nat.cast_nonneg rank; linarith)
  have hrest : 0 ≤ (rank : ℝ) + 2 * H * p ^ 2 + unbalancedErrorBudget c +
      (((rank + unbalancedRankExtra c p H : ℕ) : ℝ) + 2 * p + unbalancedErrorBudget c) +
      almostPeriodicityWidthConstant (c / 64) *
        (1 + (3 * H + 1) * p ^ 2 + Real.log (2 + rank)) := by positivity
  unfold unbalancedWidthLoss
  linarith

theorem unbalanced_return_width_le_regular_return {N : ℕ} [NeZero N]
    (S : CyclicBohr.Set N) {c p H W Q E : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hp : 0 ≤ p) (hH : 0 ≤ H)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E) :
    S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H Q E) ≤
      (CellRefinement.independentReturnScale S.rank W (Real.exp (-E)) : ℝ) * S.radius / 2 := by
  have hscale := CellRefinement.independentReturnScale_exp_lower S.rank hW hWcap hQ hE
  have htwo : Real.exp (-2 : ℝ) ≤ 1 / 2 := by
    have h : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
    simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num) h
  have hloss : Real.exp (-unbalancedWidthLoss S.rank c p H) ≤ 1 / 2 :=
    (Real.exp_le_exp.mpr (neg_le_neg (two_le_unbalancedWidthLoss S.rank hc hc1 hp hH))).trans htwo
  have hS := S.radius_nonneg
  calc
    _ = Real.exp (-((S.rank : ℝ) + Q + E + 1602)) * S.radius *
        Real.exp (-unbalancedWidthLoss S.rank c p H) := by
      unfold unbalancedReturnWidthLoss
      rw [neg_add, Real.exp_add]
      ring
    _ ≤ (CellRefinement.independentReturnScale S.rank W (Real.exp (-E)) : ℝ) * S.radius * (1 / 2) := by
      gcongr
    _ = _ := by ring

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SmallRatioPotential
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem small_ratio_quarter_potential_le_either {a b u v c₀ K : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hc₀ : 0 ≤ c₀) (hK : 0 ≤ K) (hau : a ≤ K * u) (hbv : b ≤ K * v)
    (hsmall : a ≤ c₀ * u ∨ b ≤ c₀ * v)
    (hfactor : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2) :
    (a * b) ^ (1 / 4 : ℝ) ≤ (u * v) ^ (1 / 4 : ℝ) / 2 := by
  rcases hsmall with hsmall | hsmall
  · exact small_ratio_quarter_potential_le ha hb hu hv hc₀ hK hsmall hbv hfactor
  · simpa only [mul_comm] using
      small_ratio_quarter_potential_le hb ha hv hu hc₀ hK hsmall hau hfactor

variable {G : Type*} [AddCommGroup G]

theorem smallRatioCenterPotential_le (L : Finset G) (f g : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    {u v c₀ K : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hc₀ : 0 ≤ c₀) (hK : 0 ≤ K)
    (hcapf : ∀ x, cellAverage L f x ≤ K * u)
    (hcapg : ∀ y, cellAverage L g y ≤ K * v)
    (hfactor : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2) (x y : G) :
    smallRatioCenterPotential L f g u v c₀ x y ≤ (u * v) ^ (1 / 4 : ℝ) / 2 := by
  classical
  unfold smallRatioCenterPotential
  split_ifs with hsmall
  · apply small_ratio_quarter_potential_le_either
      (cellAverage_nonneg L f hf x) (cellAverage_nonneg L g hg y)
      hu hv hc₀ hK (hcapf x) (hcapg y) _ hfactor
    exact hsmall.imp le_of_lt le_of_lt
  · positivity

theorem expect_smallRatioCenterPotential_le (B L : Finset G) (hB : B.Nonempty)
    (f g : G → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    {u v c₀ K : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hc₀ : 0 ≤ c₀) (hK : 0 ≤ K)
    (hcapf : ∀ x, cellAverage L f x ≤ K * u)
    (hcapg : ∀ y, cellAverage L g y ≤ K * v)
    (hfactor : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2) :
    (𝔼 x ∈ B, 𝔼 y ∈ B, smallRatioCenterPotential L f g u v c₀ x y) ≤
      (u * v) ^ (1 / 4 : ℝ) / 2 := by
  calc
    _ ≤ 𝔼 _x ∈ B, 𝔼 _y ∈ B, (u * v) ^ (1 / 4 : ℝ) / 2 := by
      apply Finset.expect_le_expect
      intro x _
      apply Finset.expect_le_expect
      intro y _
      exact smallRatioCenterPotential_le L f g hf hg hu hv hc₀ hK hcapf hcapg hfactor x y
    _ = _ := by rw [Finset.expect_const hB, Finset.expect_const hB]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedChildBound
namespace OAI

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem active_center_integral_le
    (Z : Finset (G × G)) (L S : Finset G) (a f g : G → ℝ) (origin : G)
    (shape : G × G → Finset G) (active : G × G → Bool) {T : ℝ}
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1)
    (hchild : ∀ z ∈ Z, active z = true → CellBilinearBound (shape z) a T) :
    (𝔼 z ∈ Z, if active z = true then
      centerChildIntegral L S (fun r => a (origin + r)) f g z (shape z) else 0) ≤
      T * (𝔼 z ∈ Z, if active z = true then centerChildPotential L S f g z (shape z) else 0) := by
  calc
    _ ≤ 𝔼 z ∈ Z, T * (if active z = true then centerChildPotential L S f g z (shape z) else 0) := by
      apply Finset.expect_le_expect
      intro z hz
      by_cases ha : active z = true
      · simpa only [if_pos ha] using
          centerChildIntegral_le_of_cellBilinearBound L S (shape z) a f g origin z (hchild z hz ha) hf hg
      · simp only [if_neg ha, mul_zero, le_refl]
    _ = _ := (Finset.mul_expect _ _ T).symm

theorem parent_bound_of_selected_children
    (Z : Finset (G × G)) (L S : Finset G) (a f g : G → ℝ) (origin : G)
    (shape : G × G → Finset G) (active : G × G → Bool)
    {parent T rho Phi error : ℝ} (hT : 0 ≤ T)
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1)
    (hchild : ∀ z ∈ Z, active z = true → CellBilinearBound (shape z) a T)
    (hpotential : (𝔼 z ∈ Z, if active z = true then centerChildPotential L S f g z (shape z) else 0) ≤
      rho * Phi)
    (hparent : parent ≤ (𝔼 z ∈ Z, if active z = true then
      centerChildIntegral L S (fun r => a (origin + r)) f g z (shape z) else 0) + error) :
    parent ≤ T * rho * Phi + error := by
  have hsum := active_center_integral_le Z L S a f g origin shape active hf hg hchild
  calc
    _ ≤ T * (𝔼 z ∈ Z, if active z = true then centerChildPotential L S f g z (shape z) else 0) + error :=
      hparent.trans (add_le_add hsum le_rfl)
    _ ≤ T * (rho * Phi) + error := add_le_add (mul_le_mul_of_nonneg_left hpotential hT) le_rfl
    _ = _ := by rw [mul_assoc]

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefinementEnlargement
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mixed_center_contraction {ι : Type*} (Z : Finset ι)
    (small : ι → Prop) [DecidablePred small] (P C : ι → ℝ) {Phi rho : ℝ}
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hsmall : (𝔼 z ∈ Z, if small z then P z else 0) ≤ Phi / 2)
    (htotal : (𝔼 z ∈ Z, P z) ≤ Phi)
    (hCsmall : ∀ z ∈ Z, small z → C z ≤ P z)
    (hClarge : ∀ z ∈ Z, ¬ small z → C z ≤ rho * P z) :
    (𝔼 z ∈ Z, C z) ≤ ((1 + rho) / 2) * Phi := by
  let A := 𝔼 z ∈ Z, if small z then P z else 0
  let B := 𝔼 z ∈ Z, if small z then 0 else P z
  have hsplit : A + B = 𝔼 z ∈ Z, P z := by
    rw [← Finset.expect_add_distrib]
    apply Finset.expect_congr rfl
    intro z _
    split_ifs <;> simp
  have hbound : (𝔼 z ∈ Z, C z) ≤ A + rho * B := by
    calc
      _ ≤ 𝔼 z ∈ Z, ((if small z then P z else 0) + rho * (if small z then 0 else P z)) := by
        apply Finset.expect_le_expect
        intro z hz
        by_cases hs : small z
        · simpa only [if_pos hs, mul_zero, add_zero] using hCsmall z hz hs
        · simpa only [if_neg hs, zero_add] using hClarge z hz hs
      _ = _ := by rw [Finset.expect_add_distrib, ← Finset.mul_expect]
  exact hbound.trans (combine_matched_potential_contractions hrho hrho1 hsmall
    (by simpa only [hsplit] using htotal))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem center_refinement_integral_bound {ι : Type*} (Z : Finset ι) (hZ : Z.Nonempty)
    (active : ι → Prop) [DecidablePred active] (I J P : ι → ℝ)
    {epsilon eta Phi : ℝ} (hepsilon : 0 ≤ epsilon) (heta : 0 ≤ eta)
    (hP : ∀ z ∈ Z, 0 ≤ P z) (hmean : (𝔼 z ∈ Z, P z) ≤ Phi)
    (hterminal : ∀ z ∈ Z, ¬ active z → I z ≤ epsilon * P z)
    (hsurviving : ∀ z ∈ Z, active z → |J z - I z| ≤ eta) :
    (𝔼 z ∈ Z, I z) ≤ (𝔼 z ∈ Z, if active z then J z else 0) + epsilon * Phi + eta := by
  have hpoint : ∀ z ∈ Z, I z ≤ (if active z then J z else 0) + epsilon * P z + eta := by
    intro z hz
    by_cases ha : active z
    · rw [if_pos ha]
      have h := (abs_le.mp (hsurviving z hz ha)).1
      have hn := mul_nonneg hepsilon (hP z hz)
      linarith
    · rw [if_neg ha, zero_add]
      exact (hterminal z hz ha).trans (le_add_of_nonneg_right heta)
  calc
    _ ≤ 𝔼 z ∈ Z, ((if active z then J z else 0) + epsilon * P z + eta) :=
      Finset.expect_le_expect hpoint
    _ = (𝔼 z ∈ Z, if active z then J z else 0) + epsilon * (𝔼 z ∈ Z, P z) + eta := by
      rw [Finset.expect_add_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
        Finset.expect_const hZ]
    _ ≤ _ := by gcongr

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_center_refinement {ι κ : Type*}
    (Z : Finset ι) (hZ : Z.Nonempty) (small : ι → Prop) [DecidablePred small]
    (Allowed : κ → Prop) (defaultShape : κ) (hdefault : Allowed defaultShape)
    (I P : ι → ℝ) (childIntegral childPotential : ι → κ → ℝ)
    {epsilon eta Phi rho : ℝ} (hepsilon : 0 ≤ epsilon) (heta : 0 ≤ eta)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hP : ∀ z ∈ Z, 0 ≤ P z) (hmean : (𝔼 z ∈ Z, P z) ≤ Phi)
    (hsmallMean : (𝔼 z ∈ Z, if small z then P z else 0) ≤ Phi / 2)
    (hsmall : ∀ z ∈ Z, small z →
      |childIntegral z defaultShape - I z| ≤ eta ∧ childPotential z defaultShape ≤ P z)
    (hlarge : ∀ z ∈ Z, ¬ small z →
      I z ≤ epsilon * P z ∨ ∃ c, Allowed c ∧
        |childIntegral z c - I z| ≤ eta ∧ childPotential z c ≤ rho * P z) :
    ∃ shape : ι → κ, ∃ active : ι → Bool,
      (∀ z ∈ Z, Allowed (shape z)) ∧
      (∀ z ∈ Z, ¬ active z = true → I z ≤ epsilon * P z) ∧
      (∀ z ∈ Z, active z = true → |childIntegral z (shape z) - I z| ≤ eta) ∧
      (𝔼 z ∈ Z, if active z = true then childPotential z (shape z) else 0) ≤
        ((1 + rho) / 2) * Phi ∧
      (𝔼 z ∈ Z, I z) ≤
        (𝔼 z ∈ Z, if active z = true then childIntegral z (shape z) else 0) + epsilon * Phi + eta := by
  classical
  let Good (z : ι) (d : Bool × κ) : Prop :=
    Allowed d.2 ∧
      (d.1 = true → |childIntegral z d.2 - I z| ≤ eta) ∧
      (¬ d.1 = true → I z ≤ epsilon * P z) ∧
      (small z → (if d.1 = true then childPotential z d.2 else 0) ≤ P z) ∧
      (¬ small z → (if d.1 = true then childPotential z d.2 else 0) ≤ rho * P z)
  have hexists : ∀ z ∈ Z, ∃ d : Bool × κ, Good z d := by
    intro z hz
    by_cases hs : small z
    · obtain ⟨herr, hpot⟩ := hsmall z hz hs
      refine ⟨(true, defaultShape), hdefault, ?_, ?_, ?_, ?_⟩
      · intro _; exact herr
      · simp
      · intro _; simpa only [ite_true] using hpot
      · intro hn; exact False.elim (hn hs)
    · rcases hlarge z hz hs with hflat | ⟨c, hc, herr, hpot⟩
      · refine ⟨(false, defaultShape), hdefault, ?_, ?_, ?_, ?_⟩
        · simp
        · intro _; exact hflat
        · intro ht; exact False.elim (hs ht)
        · intro _
          simpa only [Bool.false_eq_true, ite_false] using mul_nonneg hrho (hP z hz)
      · refine ⟨(true, c), hc, ?_, ?_, ?_, ?_⟩
        · intro _; exact herr
        · simp
        · intro ht; exact False.elim (hs ht)
        · intro _; simpa only [ite_true] using hpot
  let selected (z : ι) : Bool × κ :=
    if hz : z ∈ Z then Classical.choose (hexists z hz) else (false, defaultShape)
  have hselected (z : ι) (hz : z ∈ Z) : Good z (selected z) := by
    dsimp only [selected]
    rw [dif_pos hz]
    exact Classical.choose_spec (hexists z hz)
  let shape := fun z => (selected z).2
  let active := fun z => (selected z).1
  refine ⟨shape, active, (fun z hz => (hselected z hz).1),
    (fun z hz => (hselected z hz).2.2.1), (fun z hz => (hselected z hz).2.1), ?_, ?_⟩
  · exact mixed_center_contraction Z small P
      (fun z => if active z = true then childPotential z (shape z) else 0)
      hrho hrho1 hsmallMean hmean
      (fun z hz => (hselected z hz).2.2.2.1)
      (fun z hz => (hselected z hz).2.2.2.2)
  · exact center_refinement_integral_bound Z hZ (fun z => active z = true) I
      (fun z => childIntegral z (shape z)) P hepsilon heta hP hmean
      (fun z hz => (hselected z hz).2.2.1)
      (fun z hz => (hselected z hz).2.1)

end Erdos3

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_admissible_independent_return_shape
    (B L S : CyclicBohr.Set N) (hL : L.IsRankRegular) (hS : S.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hfreq : S.frequencies = L.frequencies) (hwidth : S.radius ≤ L.radius)
    {scale : ℝ≥0} {extra : ℕ} {minimumWidth c p H W Q E : ℝ}
    (hSB : S.carrier ⊆ (B.ndilate scale).carrier) (hrank : S.rank ≤ B.rank + extra)
    (hminimum : minimumWidth ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H Q E))
    (hc : 0 < c) (hc1 : c ≤ 1) (hp : 0 ≤ p) (hH : 0 ≤ H)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E) :
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape B scale extra minimumWidth C ∧
      C.frequencies = S.frequencies ∧ 0 < C.radius ∧ C.radius ≤ 1 ∧
      C.carrier ⊆ (S.ndilate (independentReturnScale S.rank W (Real.exp (-E)))).carrier ∧
      ∀ a f g : ZMod N → ℝ, (∀ x, |a x| ≤ W) →
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
        |(𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
            bilinearIntegral (C.carrier.image (fun t => z.1 + t))
              (C.carrier.image (fun t => (-z.1 + z.2.1 + z.2.2) + t)) a f g) -
          matchedIntegral L.carrier S.carrier a f g| ≤ Real.exp (-E) := by
  let zeta := independentReturnScale S.rank W (Real.exp (-E))
  obtain ⟨hzeta, hzeta1, _, _⟩ := independentReturnScale_spec S.rank hW (Real.exp_pos (-E))
  obtain ⟨C, hCfreq, hCreg, hClo, hChi, hCS, _⟩ :=
    S.exists_controlled_regular_subdilate hSpos zeta hzeta hzeta1
  have hzetaR : (0 : ℝ) < zeta := by exact_mod_cast hzeta
  have hzeta1R : (zeta : ℝ) ≤ 1 := by exact_mod_cast hzeta1
  have hCpos : 0 < C.radius := (show 0 < (zeta : ℝ) * S.radius / 2 by positivity).trans_le hClo
  have hCwidth : C.radius ≤ 1 := hChi.trans (by nlinarith [S.radius_nonneg])
  have hCSbase : C.carrier ⊆ S.carrier := by
    have h := hCS.trans (CyclicBohr.Set.carrier_ndilate_mono (B := S) hzeta1)
    simpa only [CyclicBohr.Set.ndilate_one] using h
  have hCrank : C.rank = S.rank := congrArg Finset.card hCfreq
  have hCminimum : minimumWidth ≤ C.radius :=
    hminimum.trans ((unbalanced_return_width_le_regular_return S hc hc1 hp hH hW hWcap hQ hE).trans hClo)
  refine ⟨C, ⟨hCreg, hCSbase.trans hSB, by simpa only [hCrank] using hrank, hCminimum⟩,
    hCfreq, hCpos, hCwidth, hCS, ?_⟩
  intro a f g ha hf hg
  exact bohr_matched_independent_at_return_scale L S hL hS hfreq hwidth C.carrier
    C.carrier_nonempty a f g hW (Real.exp_pos (-E)) hCS ha hf hg

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

theorem unbalanced_factor_bounds {c M : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    3 / 4 ≤ 1 - c / (128 * (1 + Real.sqrt M) ^ 2) ∧
      1 - c / (128 * (1 + Real.sqrt M) ^ 2) < 1 := by
  have h := quarter_contraction_factor_bounds (M := M)
    (show 0 < c / 32 by positivity) (show c / 32 ≤ 1 by linarith)
  have heq : c / 32 / (4 * (1 + Real.sqrt M) ^ 2) = c / (128 * (1 + Real.sqrt M) ^ 2) := by
    rw [div_div]
    congr 1
    ring
  simpa only [heq] using h

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem exists_capped_parent_refinement
    (B₀ L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    (hfreq : S.frequencies = L.frequencies) (hlocalWidth : S.radius ≤ L.radius)
    {kappa scale : ℝ≥0} {extra : ℕ} {minimumWidth p D R P H W Q E : ℝ}
    (hepsilon : 0 < epsilon) (hp : 1 ≤ p) (hD : 0 ≤ D) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hSB : S.carrier ⊆ (B₀.ndilate scale).carrier)
    (hrank : S.rank + unbalancedRankExtra γ p H ≤ B₀.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank γ p H Q E))
    (hLshape : Peeling.admissibleBohrShape B₀ scale extra minimumWidth L)
    (A B F G : ZMod N → ℝ) (origin : ZMod N)
    (hA : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p)
    (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p)
    (hF : ∀ r, 0 ≤ F r ∧ F r ≤ 1) (hG : ∀ r, 0 ≤ G r ∧ G r ≤ 1)
    (hFsupport : ∀ r, r ∉ B₀.carrier → F r = 0)
    (hGsupport : ∀ r, r ∉ B₀.carrier → G r = 0)
    {U V M K c₀ : ℝ} (hU : 0 < U) (hV : 0 < V) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hmeanF : (𝔼 r ∈ B₀.carrier, F r) = U) (hmeanG : (𝔼 r ∈ B₀.carrier, G r) = V)
    (hfactor : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2)
    (hparentF : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier F z ≤ K * U)
    (hparentG : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier G z ≤ K * V)
    (hM : 0 < M) (hMcap : M ≤ Real.exp p)
    (hMU : 1 ≤ M * (c₀ * U)) (hMV : 1 ≤ M * (c₀ * V))
    (hSLmoment : S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M δ)).carrier)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ γ / 32)
    (hSlog : Real.exp (-R) ≤ S.radius)
    (hcomplexity : 2 * (S.rank : ℝ) + p + (D + 2) * p + R + 1612 ≤ P)
    (hprecision : (D + 2) * p + 2 + (S.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ W)
    {matchingError : ℝ}
    (hmatching : |bilinearIntegral B₀.carrier B₀.carrier (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) F G -
      parentTruncatedIntegral B₀.carrier B₀.carrier L.carrier S.carrier
        (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) F G| ≤ matchingError)
    (m : ℕ) (hm : 0 < m)
    (horder : (1 + 1 + (D + 1) + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2)
    (horders : ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
      ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
      (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m')) :
    let a := fun r => A (origin + r) - (1 + epsilon) * B (origin + r)
    let rho := 1 - γ / (128 * (1 + Real.sqrt (K / c₀)) ^ 2)
    ∃ shape : ZMod N × ZMod N → CyclicBohr.Set N,
      ∃ active : ZMod N × ZMod N → Bool,
      (∀ z ∈ B₀.carrier ×ˢ B₀.carrier,
        Peeling.admissibleBohrShape B₀ scale extra minimumWidth (shape z) ∧
          0 < (shape z).radius ∧ (shape z).radius ≤ 1) ∧
      (∀ z ∈ B₀.carrier ×ˢ B₀.carrier, ¬ active z = true →
        centerMatchedIntegral L.carrier S.carrier a F G z ≤
          Real.exp (-(D * p)) * centerPotential L.carrier F G z) ∧
      (∀ z ∈ B₀.carrier ×ˢ B₀.carrier, active z = true →
        |centerChildIntegral L.carrier S.carrier a F G z (shape z).carrier -
          centerMatchedIntegral L.carrier S.carrier a F G z| ≤ Real.exp (-E)) ∧
      (𝔼 z ∈ B₀.carrier ×ˢ B₀.carrier,
        if active z = true then centerChildPotential L.carrier S.carrier F G z (shape z).carrier else 0) ≤
          ((1 + rho) / 2) * (U * V) ^ (1 / 4 : ℝ) ∧
      bilinearIntegral B₀.carrier B₀.carrier a F G ≤
        (𝔼 z ∈ B₀.carrier ×ˢ B₀.carrier,
          if active z = true then centerChildIntegral L.carrier S.carrier a F G z (shape z).carrier else 0) +
          Real.exp (-(D * p)) * (U * V) ^ (1 / 4 : ℝ) + Real.exp (-E) + matchingError := by
  classical
  intro a rho
  let small := fun z : ZMod N × ZMod N =>
    cellAverage L.carrier F z.1 < c₀ * U ∨ cellAverage L.carrier G z.2 < c₀ * V
  let Allowed := fun C : CyclicBohr.Set N =>
    Peeling.admissibleBohrShape B₀ scale extra minimumWidth C ∧ 0 < C.radius ∧ C.radius ≤ 1
  have hF0 : ∀ r, 0 ≤ F r := fun r => (hF r).1
  have hG0 : ∀ r, 0 ≤ G r := fun r => (hG r).1
  have hgamma : 0 < γ := localMomentGain_pos δ
  have hgamma1 : γ ≤ 1 := (localMomentGain_le_half δ).trans (by norm_num)
  obtain ⟨hrho, hrho1⟩ := unbalanced_factor_bounds (M := K / c₀) hgamma hgamma1
  have hmean : (𝔼 z ∈ B₀.carrier ×ˢ B₀.carrier, centerPotential L.carrier F G z) ≤
      (U * V) ^ (1 / 4 : ℝ) := by
    have h := centerPotential_mean_le B₀.carrier L.carrier B₀.carrier_nonempty L.carrier_nonempty
      F G hF0 hG0 hFsupport hGsupport
    simpa only [hmeanF, hmeanG] using h
  have hsmallMean :
      (𝔼 z ∈ B₀.carrier ×ˢ B₀.carrier, if small z then centerPotential L.carrier F G z else 0) ≤
        (U * V) ^ (1 / 4 : ℝ) / 2 := by
    have h := expect_smallRatioCenterPotential_le B₀.carrier L.carrier B₀.carrier_nonempty
      F G hF0 hG0 hU.le hV.le hc₀.le hK (hparentF L hLshape) (hparentG L hLshape) hfactor
    simpa only [Finset.expect_product, small, centerPotential, smallRatioCenterPotential] using h
  obtain ⟨C₀, hC₀shape, _, hC₀pos, hC₀width, _, hC₀error⟩ :=
    exists_admissible_independent_return_shape (extra := extra) B₀ L S hL hSreg hSpos hSwidth hfreq hlocalWidth
      hSB (by omega) hwidth hgamma hgamma1 (by linarith) hH hW hWcap hQ hE
  have hdefault : Allowed C₀ := ⟨hC₀shape, hC₀pos, hC₀width⟩
  have hsmallCase : ∀ z ∈ B₀.carrier ×ˢ B₀.carrier, small z →
      |centerChildIntegral L.carrier S.carrier a F G z C₀.carrier -
        centerMatchedIntegral L.carrier S.carrier a F G z| ≤ Real.exp (-E) ∧
      centerChildPotential L.carrier S.carrier F G z C₀.carrier ≤ centerPotential L.carrier F G z := by
    intro z _ _
    refine ⟨?_, centerChildPotential_le L.carrier S.carrier C₀.carrier
      L.carrier_nonempty S.carrier_nonempty C₀.carrier_nonempty F G hF hG z⟩
    exact hC₀error (fun r => a (z.1 + z.2 + r))
      (centerSlice L.carrier F z.1) (centerSlice L.carrier G z.2)
      (fun r => ha (origin + (z.1 + z.2 + r))) (centerSlice_bounds L.carrier F hF z.1)
      (centerSlice_bounds L.carrier G hG z.2)
  have hlargeCase : ∀ z ∈ B₀.carrier ×ˢ B₀.carrier, ¬ small z →
      centerMatchedIntegral L.carrier S.carrier a F G z ≤
        Real.exp (-(D * p)) * centerPotential L.carrier F G z ∨
      ∃ C, Allowed C ∧
        |centerChildIntegral L.carrier S.carrier a F G z C.carrier -
          centerMatchedIntegral L.carrier S.carrier a F G z| ≤ Real.exp (-E) ∧
        centerChildPotential L.carrier S.carrier F G z C.carrier ≤ rho * centerPotential L.carrier F G z := by
    intro z _ hz
    have hlowerF : c₀ * U ≤ cellAverage L.carrier F z.1 := le_of_not_gt (not_or.mp hz).1
    have hlowerG : c₀ * V ≤ cellAverage L.carrier G z.2 := le_of_not_gt (not_or.mp hz).2
    have h := capped_center_alternatives B₀ L S hL hSpos hSwidth hSreg hSrank hfreq hlocalWidth
      hepsilon hp hD hR hH hSL hkappa hSB hrank hwidth A B F G origin z.1 z.2 hA hB hF hG
      hU hV hc₀ hK hlowerF hlowerG hparentF hparentG hM hMcap hMU hMV hSLmoment herror
      hSlog hcomplexity hprecision hcompare hW hWcap hQ hE ha m hm horder horders
    rcases h with hflat | ⟨C, hC, hCpos, hCwidth, herr, hpot⟩
    · exact Or.inl hflat
    · exact Or.inr ⟨C, ⟨hC, hCpos, hCwidth⟩, herr, hpot⟩
  obtain ⟨shape, active, hallowed, hterminal, hactive, hpotential, hintegral⟩ :=
    exists_center_refinement (B₀.carrier ×ˢ B₀.carrier) (B₀.carrier_nonempty.product B₀.carrier_nonempty)
      small Allowed C₀ hdefault (centerMatchedIntegral L.carrier S.carrier a F G)
      (centerPotential L.carrier F G)
      (fun z C => centerChildIntegral L.carrier S.carrier a F G z C.carrier)
      (fun z C => centerChildPotential L.carrier S.carrier F G z C.carrier)
      (Real.exp_nonneg _) (Real.exp_nonneg _) (by linarith) hrho1.le
      (fun z _ => centerPotential_nonneg L.carrier F G hF0 hG0 z) hmean hsmallMean hsmallCase hlargeCase
  refine ⟨shape, active, hallowed, hterminal, hactive, hpotential, ?_⟩
  rw [centerMatchedIntegral_mean] at hintegral
  have hmatch := (abs_le.mp hmatching).2
  linarith only [hmatch, hintegral]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem capped_parent_bound_of_children
    (B₀ L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    (hfreq : S.frequencies = L.frequencies) (hlocalWidth : S.radius ≤ L.radius)
    {kappa scale : ℝ≥0} {extra : ℕ} {minimumWidth p D R P H W Q E : ℝ}
    (hepsilon : 0 < epsilon) (hp : 1 ≤ p) (hD : 0 ≤ D) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hSB : S.carrier ⊆ (B₀.ndilate scale).carrier)
    (hrank : S.rank + unbalancedRankExtra γ p H ≤ B₀.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank γ p H Q E))
    (hLshape : Peeling.admissibleBohrShape B₀ scale extra minimumWidth L)
    (A B F G : ZMod N → ℝ) (origin : ZMod N)
    (hA : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p)
    (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p)
    (hF : ∀ r, 0 ≤ F r ∧ F r ≤ 1) (hG : ∀ r, 0 ≤ G r ∧ G r ≤ 1)
    (hFsupport : ∀ r, r ∉ B₀.carrier → F r = 0)
    (hGsupport : ∀ r, r ∉ B₀.carrier → G r = 0)
    {U V M K c₀ : ℝ} (hU : 0 < U) (hV : 0 < V) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hmeanF : (𝔼 r ∈ B₀.carrier, F r) = U) (hmeanG : (𝔼 r ∈ B₀.carrier, G r) = V)
    (hfactor : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2)
    (hparentF : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier F z ≤ K * U)
    (hparentG : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier G z ≤ K * V)
    (hM : 0 < M) (hMcap : M ≤ Real.exp p)
    (hMU : 1 ≤ M * (c₀ * U)) (hMV : 1 ≤ M * (c₀ * V))
    (hSLmoment : S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M δ)).carrier)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ γ / 32)
    (hSlog : Real.exp (-R) ≤ S.radius)
    (hcomplexity : 2 * (S.rank : ℝ) + p + (D + 2) * p + R + 1612 ≤ P)
    (hprecision : (D + 2) * p + 2 + (S.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ W)
    {matchingError : ℝ}
    (hmatching : |bilinearIntegral B₀.carrier B₀.carrier (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) F G -
      parentTruncatedIntegral B₀.carrier B₀.carrier L.carrier S.carrier
        (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) F G| ≤ matchingError)
    (m : ℕ) (hm : 0 < m)
    (horder : (1 + 1 + (D + 1) + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2)
    (horders : ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
      ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
      (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m'))
    {T : ℝ} (hT : 0 ≤ T)
    (hchildren : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      CellBilinearBound C.carrier (fun r => A r - (1 + epsilon) * B r) T) :
    let rho := 1 - γ / (128 * (1 + Real.sqrt (K / c₀)) ^ 2)
    bilinearIntegral B₀.carrier B₀.carrier
        (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) F G ≤
      (T * ((1 + rho) / 2) + Real.exp (-(D * p))) * (U * V) ^ (1 / 4 : ℝ) +
        Real.exp (-E) + matchingError := by
  intro rho
  obtain ⟨shape, active, hallowed, _, _, hpotential, hintegral⟩ :=
    exists_capped_parent_refinement B₀ L S hL hSpos hSwidth hSreg hSrank hfreq hlocalWidth
      hepsilon hp hD hR hH hSL hkappa hSB hrank hwidth hLshape A B F G origin hA hB hF hG
      hFsupport hGsupport hU hV hc₀ hK hmeanF hmeanG hfactor hparentF hparentG hM hMcap hMU hMV
      hSLmoment herror hSlog hcomplexity hprecision hcompare hW hWcap hQ hE ha hmatching
      m hm horder horders
  have h := parent_bound_of_selected_children (B₀.carrier ×ˢ B₀.carrier) L.carrier S.carrier
    (fun r => A r - (1 + epsilon) * B r) F G origin (fun z => (shape z).carrier) active hT hF hG
    (fun z hz _ => hchildren (shape z) (hallowed z hz).1) hpotential
    (by simpa only [add_assoc] using hintegral)
  nlinarith only [h]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

end Erdos3.CellRefinement

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.CellRefinement.capped_parent_bound_of_children := @OAI.Erdos3.CellRefinement.capped_parent_bound_of_children
