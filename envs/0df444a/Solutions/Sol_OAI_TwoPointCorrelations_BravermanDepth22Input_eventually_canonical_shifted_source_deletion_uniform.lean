-- Prove2me | solution 1 for OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_canonical_shifted_source_deletion_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:51:22.33257+00:00
-- url     : https://prove2.me/submissions/6ad84bbe-dc4e-499b-86ed-2bbad1260587

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_BravermanDepth22Input_eventually_shifted_actual_prohibited_deletion_uniform
import Theorems.Thm_OAI_TwoPointCorrelations_BravermanDepth22Input_eventually_shifted_padding_deletion_uniform
import Theorems.Thm_OAI_TwoPointCorrelations_BravermanDepth22Input_eventually_shifted_tuple_degree_deletion
import Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_actual_pool_masses
import Theorems.Thm_OAI_TwoPointCorrelations_eventually_prohibited_density

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DeletionErrorScale
namespace OAI

/-! The finite-catalog error in the three deletion estimates is
negligible even when every bin uses a different interval. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma deletion_comparison_error_bound (L C b d q S V : ℝ)
    (hL : 4800 ≤ L) (hC : 0 ≤ C) (hCL : C + 104 ≤ L)
    (hb0 : 0 ≤ b) (hd0 : 0 ≤ d) (hq0 : 0 ≤ q)
    (hb : b ≤ Real.exp (C * Real.log L)) (hd : d ≤ Real.exp (2 * L))
    (hq : q ≤ Real.exp (100 * L ^ 2)) (hS : 1 ≤ S) (hV : 1 ≤ V) :
    ((3 * b * d * q + b * Real.exp (101 * L)) * Real.exp (-(L ^ 9))) /
      (S * V) ≤ Real.exp (-L ^ (9 / 10 : ℝ)) := by
  have hL0 : 0 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hcLog := mul_le_mul_of_nonneg_left hlog hC
  have hcL := mul_le_mul_of_nonneg_right hCL hL0
  have h101 := mul_le_mul_of_nonneg_right (show (101 : ℝ) ≤ L by linarith) (sq_nonneg L)
  have hp1 : C * Real.log L + 2 * L + 100 * L ^ 2 ≤ L ^ 3 := by nlinarith
  have hp2 : C * Real.log L + 101 * L ≤ L ^ 3 := by nlinarith
  have hprod : b * d * q ≤ Real.exp (L ^ 3) := by
    calc
      _ ≤ Real.exp (C * Real.log L) * Real.exp (2 * L) * Real.exp (100 * L ^ 2) :=
        mul_le_mul (mul_le_mul hb hd hd0 (Real.exp_pos _).le) hq hq0
          (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      _ = Real.exp (C * Real.log L + 2 * L + 100 * L ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr hp1
  have hother : b * Real.exp (101 * L) ≤ Real.exp (L ^ 3) := by
    calc
      _ ≤ Real.exp (C * Real.log L) * Real.exp (101 * L) :=
        mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
      _ = Real.exp (C * Real.log L + 101 * L) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hp2
  have h34 : L ^ 3 + 3 ≤ L ^ 4 := by
    have hh := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ L by linarith) (pow_nonneg hL0 3)
    have hp : 3 ≤ L ^ 3 := (show (3 : ℝ) ≤ L by linarith).trans (by
      simpa only [pow_one] using pow_le_pow_right₀ hL1 (show 1 ≤ 3 by norm_num))
    nlinarith
  have hcoefficient : 3 * b * d * q + b * Real.exp (101 * L) ≤ Real.exp (L ^ 4) := by
    calc
      _ ≤ 4 * Real.exp (L ^ 3) := by nlinarith
      _ ≤ Real.exp 3 * Real.exp (L ^ 3) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (3 : ℝ)]) (Real.exp_pos _).le
      _ = Real.exp (L ^ 3 + 3) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr h34
  have hpower : L ^ 4 + L ≤ L ^ 9 := by
    have h45 : 2 * L ^ 4 ≤ L ^ 5 := by
      have hh := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ L by linarith) (pow_nonneg hL0 4)
      nlinarith
    have h59 : L ^ 5 ≤ L ^ 9 := pow_le_pow_right₀ hL1 (by norm_num)
    have h14 : L ≤ L ^ 4 := by
      have hh : L ^ 1 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
      simpa only [pow_one] using hh
    linarith
  have hsmall : L ^ (9 / 10 : ℝ) ≤ L := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL1
      (show (9 / 10 : ℝ) ≤ 1 by norm_num)
  have hSV : 1 ≤ S * V := by nlinarith
  have hnonneg : 0 ≤ (3 * b * d * q + b * Real.exp (101 * L)) * Real.exp (-(L ^ 9)) := by
    positivity
  calc
    _ ≤ (3 * b * d * q + b * Real.exp (101 * L)) * Real.exp (-(L ^ 9)) :=
      div_le_self hnonneg hSV
    _ ≤ Real.exp (L ^ 4) * Real.exp (-(L ^ 9)) :=
      mul_le_mul_of_nonneg_right hcoefficient (Real.exp_pos _).le
    _ = Real.exp (L ^ 4 - L ^ 9) := by rw [← Real.exp_add]; congr 1
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem eventually_deletion_comparison_error (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ b d q S V : ℝ,
      0 ≤ b → 0 ≤ d → 0 ≤ q →
      b ≤ Real.exp (C * Real.log L) → d ≤ Real.exp (2 * L) →
      q ≤ Real.exp (100 * L ^ 2) → 1 ≤ S → 1 ≤ V →
      ((3 * b * d * q + b * Real.exp (101 * L)) * Real.exp (-(L ^ 9))) /
        (S * V) ≤ Real.exp (-L ^ (9 / 10 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (max 4800 (C + 104))] with L hL
  intro b d q S V hb0 hd0 hq0 hb hd hq hS hV
  exact deletion_comparison_error_bound L C b d q S V
    ((le_max_left _ _).trans hL) hC ((le_max_right _ _).trans hL)
    hb0 hd0 hq0 hb hd hq hS hV

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DeletionNormalization
namespace OAI

/-! Normalize the three deletion costs by the exact padding and tuple
masses. The rare-site term uses only S*V ≥ 1. -/

namespace TwoPointCorrelations

lemma normalize_three_deletion_costs
    (F pad deg rare S V T α β δ ep ed er : ℝ)
    (hS : 1 ≤ S) (hV : 1 ≤ V) (hδ : 0 ≤ δ)
    (hF : F ≤ pad + deg + rare)
    (hpad : pad ≤ S * V * T * α + ep)
    (hdeg : deg ≤ S * V * T * β + ed)
    (hrare : rare ≤ δ + er) :
    F / (S * V) ≤ T * (α + β) + δ + (ep + ed + er) / (S * V) := by
  have hSV : 1 ≤ S * V := by nlinarith
  have hSVpos : 0 < S * V := by linarith
  have hrare' : δ ≤ S * V * δ := by nlinarith
  have hb : F ≤ S * V * (T * (α + β) + δ) + (ep + ed + er) := by nlinarith
  calc
    _ ≤ (S * V * (T * (α + β) + δ) + (ep + ed + er)) / (S * V) :=
      div_le_div_of_nonneg_right hb hSVpos.le
    _ = _ := by rw [add_div, mul_div_cancel_left₀ _ hSVpos.ne']


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LabeledForest
namespace OAI

/-!
# Labeled ordered forests

Binary trees use the first-child / next-sibling convention. The labels
are auxiliary: erasing them keeps the finite shape used by the code.
-/

namespace TwoPointCorrelations

open _root_.BinaryTree

variable {V : Type*}











@[simp] lemma attachForestLeaf_roots [DecidableEq V] (parent leaf : V) (t : BinaryTree V) :
    forestRoots (attachForestLeaf parent leaf t) = forestRoots t := by
  induction t with
  | nil => rfl
  | node v l r hl hr =>
      by_cases hv : v = parent <;> simp [attachForestLeaf, hv, forestRoots, hr]










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling
namespace OAI

/-! Product sampling and the atom bound for independent linear equations. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]


omit [Fintype ι] in
@[simp] lemma joinCoordinates_mem (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A)
    (i : S) : joinCoordinates S x y i = x i := by simp [joinCoordinates, i.property]

omit [Fintype ι] in
@[simp] lemma joinCoordinates_notMem (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A)
    (i : {i // i ∉ S}) : joinCoordinates S x y i = y i := by simp [joinCoordinates, i.property]

namespace FiniteLaw

variable [Fintype A]






end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MatrixAction
namespace OAI

/-! Concrete continuous operators associated with finite matrices. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


@[simp] lemma matrixOperator_apply (A : ι → ι → ℂ) (v : EuclideanSpace ℂ ι) (i : ι) :
    matrixOperator A v i = ∑ j, A i j * v j := rfl


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MixedDifference
namespace OAI

/-!
# Exact singleton centering

The product sampling law is kept fixed. Forcing a coordinate overwrites
that coordinate of the same sample, rather than drawing fresh coordinates
at different sites. This is the algebraic part of `q:mixed-difference`.
-/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]


omit [Fintype ι] [Fintype A] [DecidableEq A] in
@[simp] lemma forceCoordinates_apply (S : Finset ι) (a x : ι → A) (i : ι) :
    forceCoordinates S a x i = if i ∈ S then a i else x i := rfl


namespace FiniteLaw











end FiniteLaw



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddedListCode
namespace OAI

/-! Fixed-length code slots for finite lists with a bounded length. -/

namespace TwoPointCorrelations

variable {α : Type*} {N : ℕ}


@[simp] theorem paddedListCode_ofFn (l : List α) (h : l.length ≤ N) (default : α) :
    List.ofFn (paddedListCode l h default) = l ++ List.replicate (N - l.length) default := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · intro i hi hj
    simp only [List.getElem_ofFn, paddedListCode]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages
namespace OAI

/-! Elementary finite averaging identities used to assemble encoded marginals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformAverage (fun _ : α => c) = c := by simp [uniformAverage]








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingTilt
namespace OAI

/-! The literal `5^omega` tilt of independent divisibility indicators gives
exactly the prime availability law used in the padding anti-concentration. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical






lemma paddingTiltNormalizer_pos (Q : Finset ℕ) : 0 < paddingTiltNormalizer Q := by
  apply prod_pos
  intro p _
  positivity










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TriangularElimination
namespace OAI

/-! Successive elimination for finite product laws and triangular events. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]


omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_same (i : ι) (a : A) (y : {j : ι // j ≠ i} → A) :
    restoreCoordinate i a y i = a := by simp [restoreCoordinate]

omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_other (i : ι) (a : A) (y : {j : ι // j ≠ i} → A)
    (j : {j : ι // j ≠ i}) : restoreCoordinate i a y j = y j := by
  simp [restoreCoordinate, j.property]


namespace FiniteLaw





end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.UniformResidues
namespace OAI

/-! Uniform residue coordinates realized on one common finite carrier. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma uniformResidueLaw_weight (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (x : Fin B) (hx : x.val < p) :
    (uniformResidueLaw B p hp hpB).weight x = (p : ℝ)⁻¹ := by
  simp [uniformResidueLaw, hx]


@[simp] lemma uniformResidueLaw_castLE (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (x : Fin p) :
    (uniformResidueLaw B p hp hpB).weight (Fin.castLE hpB x) = (p : ℝ)⁻¹ := by
  exact uniformResidueLaw_weight B p hp hpB _ x.isLt


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.FourierCorrection
namespace OAI

/-!
# Correcting an almost independent Boolean density

This is the finite Fourier correction used in the proof of the manuscript's
finite-residue comparison (`q:finite-law`, `q:fourier-correction-tv`). The
construction removes the chosen nonconstant Walsh coefficients and adds the
constant `a` before normalization, retaining pointwise nonnegativity.
-/

namespace TwoPointCorrelations

open _root_.Finset










@[simp] lemma booleanSign_not (b : Bool) : booleanSign (!b) = -booleanSign b := by
  cases b <;> norm_num [booleanSign]

@[simp] lemma booleanSign_sq (b : Bool) : booleanSign b * booleanSign b = 1 := by
  cases b <;> norm_num [booleanSign]

@[simp] lemma abs_booleanSign (b : Bool) : |booleanSign b| = 1 := by
  cases b <;> norm_num [booleanSign]



@[simp] lemma abs_walsh {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    |walsh S x| = 1 := by
  simp [walsh, Finset.abs_prod]

@[simp] lemma walsh_mul_self {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    walsh S x * walsh S x = 1 := by
  unfold walsh
  rw [← Finset.prod_mul_distrib]
  simp
























end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.BitEncoding
namespace OAI

/-!
# Exact finite jitter encoding

For `Q = 2^B`, the integer code `⌊(r Q + j)/s⌋`, with `j` uniform in
`{0,…,Q-1}`, has exactly the distribution of the first `B` binary digits
of `(r + U)/s` for uniform `U` in `[0,1)`. This finite construction avoids
continuous auxiliary probability spaces. Jointly uniform residue and
jitter give a uniform code. Decoding can fail for at most `s` jitter values
at each fixed residue, giving the stronger bound `s/Q`.
-/

open _root_.Finset

namespace TwoPointCorrelations












@[simp] lemma decode_jitterBits {s B : ℕ} (hs : 0 < s) (r : Fin s) (j : Fin (2 ^ B)) :
    decodeBits hs (jitterBits r j) = jitterDecode hs (by positivity) (jitterCode r j) := by
  simp [decodeBits, jitterBits]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.EncodedCoefficients
namespace OAI

/-!
# Low-order coefficients of the actual encoded interval law

A Walsh coefficient only uses the residue coordinates touched by its bits.
All other independent jitters integrate out. The remaining observable is
bounded by one, so CRT gives the product of its selected moduli divided by
the interval length as an explicit coefficient bound.
-/

namespace TwoPointCorrelations

open _root_.Finset





@[simp] lemma flattenBitBlocks_apply {m B : ℕ} (z : Fin m → BooleanCube B)
    (k : Fin (m * B)) : flattenBitBlocks m B z k = z k.divNat k.modNat := rfl






















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DecoderComparison
namespace OAI

/-! Uniform decoding-error estimates for the finite jitter construction. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma uniformAverage_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ x, f x ≤ g x) : uniformAverage f ≤ uniformAverage g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (Nat.cast_nonneg _)











end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimes
namespace OAI

/-! The fixed modulus-five prime-number input used by the manuscript.

Published source: D. Koukoulopoulos, *The Distribution of Prime Numbers*,
AMS, 2019, Theorem 12.1 (Siegel--Walfisz), with modulus 5 fixed. That theorem
is stated for the prime-counting function. `ModFiveThetaInput` is its standard
partial-summation consequence for the logarithmically weighted prime count,
specialized to the two selections needed here. The complementary selection
includes the single prime 5, which changes the error by a bounded amount.
Source: https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf

The estimate includes every prime in the selected classes. Removing a finite
exceptional prime set contributes an explicit finite-deletion correction.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology











lemma modFivePrimesUpTo_le {one : Bool} {x : ℝ} (hx : 0 ≤ x) {p : ℕ}
    (hp : p ∈ modFivePrimesUpTo one x) : (p : ℝ) ≤ x :=
  (Nat.le_floor_iff hx).mp (mem_Icc.mp (mem_filter.mp hp).1).2






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeSupplyGeometry
namespace OAI

/-! Actual disjoint prime supplies at geometric logarithmic scales. Their
mass follows from the published fixed-modulus input through the proved
partial-summation chain, and all support assertions are finite identities. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma primeSupplyEndpoint_zero (A W : ℝ) : primeSupplyEndpoint A W 0 = A := by
  simp [primeSupplyEndpoint]

lemma primeSupplyEndpoint_succ (A W : ℝ) (i : ℕ) :
    primeSupplyEndpoint A W (i + 1) = primeSupplyEndpoint A W i * Real.exp (6 * W) := by
  unfold primeSupplyEndpoint
  rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add]
  ring





lemma centeredPrimeSupply_global_bounds {E : Finset ℕ} {A W L : ℝ}
    (hA : 0 ≤ A) (hW : 0 ≤ W) {J i p : ℕ} (hi : i < J)
    (hL : primeSupplyEndpoint A W J ≤ L) (hp : p ∈ centeredPrimeSupply E A W i) :
    Real.exp A < (p : ℝ) ∧ (p : ℝ) ≤ Real.exp L := by
  have hh := centeredPrimeSupply_mem hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hh.1.pos
  have hlo : A < Real.log p := by
    have hmono := primeSupplyEndpoint_mono A W hA hW (Nat.zero_le i)
    rw [primeSupplyEndpoint_zero] at hmono
    exact hmono.trans_lt hh.2.2.2.1
  have hhi : Real.log p ≤ L := hh.2.2.2.2.trans
    ((primeSupplyEndpoint_mono A W hA hW (Nat.succ_le_of_lt hi)).trans hL)
  constructor
  · simpa only [Real.exp_log hp0] using Real.exp_lt_exp.mpr hlo
  · simpa only [Real.exp_log hp0] using Real.exp_le_exp.mpr hhi

lemma primeSupplyEndpoint_sum_lt (A W : ℝ) (hA : 0 < A) (hW : 1 ≤ W) (J : ℕ) :
    (∑ i ∈ range J, primeSupplyEndpoint A W (i + 1)) < 2 * primeSupplyEndpoint A W J := by
  have hratio : 2 ≤ Real.exp (6 * W) := by
    linarith [Real.add_one_le_exp (6 * W)]
  induction J with
  | zero => simp [primeSupplyEndpoint, hA]
  | succ J ih =>
    have he : 0 ≤ primeSupplyEndpoint A W J := by unfold primeSupplyEndpoint; positivity
    have hstep : 2 * primeSupplyEndpoint A W J ≤ primeSupplyEndpoint A W (J + 1) := by
      rw [primeSupplyEndpoint_succ]
      nlinarith [mul_le_mul_of_nonneg_right hratio he]
    rw [sum_range_succ]
    linarith

lemma centeredPrimeSupply_tuple_log_bound {E : Finset ℕ} {A W L : ℝ}
    (hA : 0 < A) (hW : 1 ≤ W) {J : ℕ} (hL : primeSupplyEndpoint A W J ≤ L)
    (p : Fin J → ℕ) (hp : ∀ i : Fin J, p i ∈ centeredPrimeSupply E A W i.val) :
    Real.log ((∏ i, p i : ℕ) : ℝ) < 2 * L := by
  have hlog : Real.log ((∏ i, p i : ℕ) : ℝ) = ∑ i, Real.log (p i : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro i _
    exact_mod_cast (centeredPrimeSupply_mem (hp i)).1.ne_zero
  rw [hlog]
  calc
    _ ≤ ∑ i : Fin J, primeSupplyEndpoint A W (i.val + 1) :=
      sum_le_sum (fun i _ => (centeredPrimeSupply_mem (hp i)).2.2.2.2)
    _ = ∑ i ∈ range J, primeSupplyEndpoint A W (i + 1) :=
      Fin.sum_univ_eq_sum_range (fun i : ℕ => primeSupplyEndpoint A W (i + 1)) J
    _ < 2 * primeSupplyEndpoint A W J := primeSupplyEndpoint_sum_lt A W hA hW J
    _ ≤ 2 * L := by linarith


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeSupplyScale
namespace OAI

/-! The literal scale choice of the manuscript satisfies all prime-supply
mass and support hypotheses; no prime-family existence premise remains. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma primeSupplyScale_endpoint (W L : ℝ) (hW : 0 < W) (hL : 1 ≤ L) :
    primeSupplyEndpoint (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) ≤ L := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hl : 0 ≤ Real.log L := Real.log_nonneg hL
  have hj : (primeSupplyCount W L : ℝ) ≤ ((1 / 200 : ℝ) * Real.log L) / (6 * W) :=
    Nat.floor_le (by positivity)
  have hj' := (le_div_iff₀ (by positivity : 0 < 6 * W)).mp hj
  unfold primeSupplyEndpoint
  calc
    _ = Real.exp (Real.log L * (199 / 200 : ℝ) + 6 * W * primeSupplyCount W L) := by
      rw [Real.rpow_def_of_pos hLp, Real.exp_add]
    _ ≤ Real.exp (Real.log L) := Real.exp_le_exp.mpr (by nlinarith)
    _ = L := Real.exp_log hLp



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalForest
namespace OAI

/-! Equal ordered-forest shapes identify their graphs by preorder indices. -/

namespace TwoPointCorrelations

open _root_.SimpleGraph _root_.BinaryTree

variable {V W : Type*}


@[simp] lemma forestIndexEquiv_val [DecidableEq V] (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t) (v : V) :
    (forestIndexEquiv t ht hc v).val = (forestNodes t).idxOf v := rfl






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnDecoder
namespace OAI

/-!
# Decoding complete column patterns

Three binary streams merge regular segments with omitted runs, mark new
runs, and mark imperfect positions. Representative indices supply omitted
labels and imperfect attachments. All decoding is independent of numerical
primes, quotient coordinates, and padding coefficients.
-/

namespace TwoPointCorrelations











@[simp] theorem expandColumnRuns_length (flags : List (Bool × Bool))
    (runs : List CanonicalColumnLabel) (previous : Option CanonicalColumnLabel) :
    (expandColumnRuns flags runs previous).length = flags.length := by
  induction flags generalizing runs previous with
  | nil => rfl
  | cons flag flags ih => cases flag with
    | mk imperfect newRun =>
      cases imperfect <;> cases newRun <;> simp [expandColumnRuns, ih]


@[simp] theorem attachImperfectLabels_length (full rest : List (Option CanonicalColumnLabel))
    (refs : List ℕ) : (attachImperfectLabels full rest refs).length = rest.length := by
  induction rest generalizing refs with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [attachImperfectLabels, ih]







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnRunEncoding
namespace OAI

/-! Reconstructing perfect runs and imperfect attachments from their bits. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]




@[simp] theorem columnFlags_length (entries : List (Option α)) (previous : Option α) :
    (columnFlags entries previous).length = entries.length := by
  induction entries generalizing previous with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [columnFlags, ih]










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnBoundaryEncoding
namespace OAI

/-! Run bits may force a split at a perfect-block boundary without changing its label. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]



@[simp] theorem columnFlagsWithCuts_length (entries : List (Option α × Bool)) (previous : Option α) :
    (columnFlagsWithCuts entries previous).length = entries.length := by
  induction entries generalizing previous with
  | nil => rfl
  | cons entry rest ih => rcases entry with ⟨a, cut⟩; cases a <;> simp [columnFlagsWithCuts, ih]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedWords
namespace OAI

/-!
# Positive words, reversal, and descent to a minimal prohibited word

A step keeps its whole tuple and padding divisor. Positivity is the exact
integer divisibility `q*d ∣ x` at its departure. Since the displacement is
`±h*q*d`, this divisibility also holds at its arrival. Restriction and
reversal therefore preserve positivity, as required in the witness descent.
-/

namespace TwoPointCorrelations


namespace SignedStep


@[simp] lemma flip_flip (a : SignedStep) : a.flip.flip = a := by
  cases a
  simp [flip]



@[simp] lemma displacement_flip (h : ℕ) (a : SignedStep) :
    a.flip.displacement h = -a.displacement h := by
  rcases a with ⟨b, d, q⟩
  cases b <;> simp [flip, displacement]


@[simp] lemma divisor_flip (a : SignedStep) : a.flip.divisor = a.divisor := rfl



end SignedStep


@[simp] lemma wordDisplacement_nil (h : ℕ) : wordDisplacement h [] = 0 := rfl

@[simp] lemma wordDisplacement_cons (h : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordDisplacement h (a :: w) = a.displacement h + wordDisplacement h w := rfl

@[simp] lemma wordDisplacement_append (h : ℕ) (u v : List SignedStep) :
    wordDisplacement h (u ++ v) = wordDisplacement h u + wordDisplacement h v := by
  simp [wordDisplacement]


@[simp] lemma reverseWord_nil : reverseWord [] = [] := rfl

@[simp] lemma reverseWord_cons (a : SignedStep) (w : List SignedStep) :
    reverseWord (a :: w) = reverseWord w ++ [a.flip] := by simp [reverseWord]

@[simp] lemma reverseWord_append (u v : List SignedStep) :
    reverseWord (u ++ v) = reverseWord v ++ reverseWord u := by simp [reverseWord]

@[simp] lemma reverseWord_length (w : List SignedStep) : (reverseWord w).length = w.length := by
  simp [reverseWord]

@[simp] lemma reverseWord_reverseWord (w : List SignedStep) : reverseWord (reverseWord w) = w := by
  simp [reverseWord, List.map_map, Function.comp_def]

@[simp] lemma wordDisplacement_reverseWord (h : ℕ) (w : List SignedStep) :
    wordDisplacement h (reverseWord w) = -wordDisplacement h w := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]


@[simp] lemma positiveWord_nil (h : ℕ) (x : ℤ) : PositiveWord h x [] := trivial

@[simp] lemma positiveWord_cons (h : ℕ) (x : ℤ) (a : SignedStep) (w : List SignedStep) :
    PositiveWord h x (a :: w) ↔ a.divisor ∣ x ∧ PositiveWord h (x + a.displacement h) w := Iff.rfl






















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.BlockGeometry
namespace OAI

/-!
# The shortest-gap argument for perfect blocks

The finite combinatorial lemma isolates a shortest gap across all prime
coordinates. Every label has interval-shaped uses inside the intervening
substring. The arithmetic lemmas below use exact integer displacement sums.
-/

namespace TwoPointCorrelations

open _root_.Finset








@[simp] lemma intervalDisplacement_singleton (D : ℕ → ℤ) (a : ℕ) :
    intervalDisplacement D a (a + 1) = D a := by simp [intervalDisplacement]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnChunkBudgets
namespace OAI

/-! Exact decoder budgets for lists of actual perfect blocks. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
@[simp] theorem regularPieceCount_append (a b : List (List α ⊕ α)) :
    regularPieceCount (a ++ b) = regularPieceCount a + regularPieceCount b := by
  simp [regularPieceCount, List.filterMap_append]

omit [DecidableEq α] in
@[simp] theorem omittedPieceCount_append (a b : List (List α ⊕ α)) :
    omittedPieceCount (a ++ b) = omittedPieceCount a + omittedPieceCount b := by
  simp [omittedPieceCount, List.filterMap_append]






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShortBlockPartition
namespace OAI

/-! The actual subdivision of perfect intervals into short blocks. -/

namespace TwoPointCorrelations

variable {α : Type*}





@[simp] theorem shortBlocks_length (s : ℕ) (l : List α) :
    (shortBlocks s l).length = l.length / s + 1 := by
  simp [shortBlocks, shortBlockLengths]











end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedDivisorMass
namespace OAI

/-! The literal finite retained-divisor set and its Euler-product mass.
Distinct prime subsets produce distinct integers, so the divisor sum does
not contain hidden multiplicities. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma retainedPrimeDivisor_pos (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    {u : ℕ} (hu : u ∈ retainedPrimeDivisors S) : 0 < u := by
  obtain ⟨U, hU, rfl⟩ := mem_image.mp hu
  exact prod_pos (fun p hp => (hS p ((mem_powerset.mp hU) hp)).pos)




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingIntegerBins
namespace OAI

/-! The squarefree divisor formula uses literal divisibility by the site,
including the site zero. Bin membership is exactly the half-open interval
condition in the manuscript. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma paddingBin_eq_iff (η c x : ℝ) (j : ℤ) (hη : 0 < η) :
    paddingBin η c x = j ↔ (j : ℝ) * η ≤ x + c ∧ x + c < ((j : ℝ) + 1) * η := by
  rw [paddingBin, Int.floor_eq_iff, le_div_iff₀ hη, div_lt_iff₀ hη]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WordSegments
namespace OAI

/-! Exact identification of list segments with integer displacement intervals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma wordStepDisplacement_nil (h i : ℕ) : wordStepDisplacement h [] i = 0 := by
  simp [wordStepDisplacement]

@[simp] lemma wordStepDisplacement_cons_zero (h : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordStepDisplacement h (a :: w) 0 = a.displacement h := rfl

@[simp] lemma wordStepDisplacement_cons_succ (h i : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordStepDisplacement h (a :: w) (i + 1) = wordStepDisplacement h w i := rfl












end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FixedColumnWords
namespace OAI

/-! The actual resampling model after every other column and padding are fixed. -/

namespace TwoPointCorrelations


namespace ColumnWordPattern

variable {α : Type*}




@[simp] lemma word_length (w : ColumnWordPattern α) (value : α → ℕ) :
    (w.word value).length = w.length := by simp [word]





end ColumnWordPattern

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingBinCoverage
namespace OAI

/-! The literal finite bin family covers every padding divisor surviving
the degree and logarithmic-size cuts. This includes the last bin whose
left endpoint, rather than its right endpoint, is at most `100 L`. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma mem_paddingBinIndices_iff (L η : ℝ) (j : ℤ) (hη : 0 < η) :
    j ∈ paddingBinIndices L η ↔ 0 ≤ j ∧ (j : ℝ) * η ≤ 100 * L := by
  rw [paddingBinIndices, mem_Icc, Int.le_floor, le_div_iff₀ hη]








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessSystemDecoding
namespace OAI

/-! Decode bounded witness metadata into the actual interval or comparison relations. -/

namespace TwoPointCorrelations


attribute [instance] PackedPrimeRelation.termFintype

namespace WitnessSystemData

variable {n N : ℕ} {ι : Type*} [DecidableEq ι]







@[simp] lemma toSystem_size (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) :
    (d.toSystem main word h ht).size = d.chosen.card := by
  exact Fintype.card_coe d.chosen

@[simp] lemma toSystem_holds (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) (x : ι → ℤ) :
    (d.toSystem main word h ht).Holds x ↔ d.Holds main word h x := Iff.rfl

end WitnessSystemData

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LabeledWordSegments
namespace OAI

/-! Splitting a coded word into the main path and its attached witness paths. -/

namespace TwoPointCorrelations
namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]


omit [DecidableEq ι] in
@[simp] lemma segment_length (w : LabeledPrimeWord ι) (a n : ℕ) :
    (w.segment a n).word.length = min n (w.word.length - a) := by
  simp only [segment, List.length_take, List.length_drop]



end LabeledPrimeWord
end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueLawUniform
namespace OAI

/-! The common padded carrier law pushes forward to the genuine uniform
product of prime residue fields. Padding points contribute zero mass. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


local instance residuePrime_neZero {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (p : ↥(data.P ∪ data.Q)) : NeZero p.val := ⟨(data.prime p).ne_zero⟩


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TuplePrimeArithmetic
namespace OAI

/-! Disjoint prime pools give the actual tuple factorization and unique tuple labels. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





/-- The numerical whole tuple determines its column choices, as used by
the nonbacktracking matrix's actual copy labels. -/
theorem primeTuple_injective {J : ℕ} {P : Fin J → Finset ℕ}
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Function.Injective (fun x : (j : Fin J) → P j => ∏ j, (x j).val) := by
  intro x y he
  change (∏ j, (x j).val) = (∏ j, (y j).val) at he
  funext j
  apply Subtype.ext
  have hp := hprime j _ (x j).property
  have hd : (x j).val ∣ ∏ l, (y l).val := by
    rw [← he]
    exact dvd_prod_of_mem (fun l => (x l).val) (mem_univ j)
  obtain ⟨l, _, hdiv⟩ := (hp.prime.dvd_finsetProd_iff (fun l => (y l).val)).mp hd
  have hv : (x j).val = (y l).val :=
    (Nat.prime_dvd_prime_iff_eq hp (hprime l _ (y l).property)).mp hdiv
  have hjl : j = l := by
    by_contra hne
    exact (disjoint_left.mp (hdisjoint j l (Ne.symm hne)))
      (x j).property (hv.symm ▸ (y l).property)
  subst l
  exact hv

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeTupleMass
namespace OAI

/-! The centered divisor family is the actual image of one prime choice
from each disjoint band. Its harmonic mass has no representation
multiplicity and is exactly the product of the band masses. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma centeredPrimeTuple_log_bound {E : Finset ℕ} {A W L : ℝ}
    (hA : 0 < A) (hW : 1 ≤ W) {J : ℕ} (hL : primeSupplyEndpoint A W J ≤ L)
    {d : ℕ} (hd : d ∈ primeTupleDivisors (fun j : Fin J => centeredPrimeSupply E A W j)) :
    0 < d ∧ Real.log d ≤ 2 * L := by
  obtain ⟨x, _, rfl⟩ := mem_image.mp hd
  constructor
  · exact prod_pos fun j _ => (centeredPrimeSupply_mem (x j).property).1.pos
  · exact (centeredPrimeSupply_tuple_log_bound hA hW hL
      (fun j => (x j).val) (fun j => (x j).property)).le




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeFamily
namespace OAI

/-! The prohibited-word data are constructed from the actual prime bands,
not assumed. Padding divisors have the requested degree cap, and the
finite pair catalog can impose any numerical eligibility condition. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical







lemma actualProhibitedPrimeFamily_pairs (h J M : ℕ) (E : Finset ℕ)
    (A W L : ℝ) (eligible : ℕ → ℕ → Prop) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (d q : ℕ) :
    (d, q) ∈ (actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE).pairs ↔
      d ∈ primeTupleDivisors (centeredPrimeBands E A W J) ∧
        q ∈ retainedPrimeDivisors (paddingPrimeSupply E L) ∧
          q.primeFactors.card ≤ M ∧ eligible d q := mem_primeFamilyPairs


lemma centeredPrimePool_bounds (E : Finset ℕ) (A W L : ℝ) (J : ℕ)
    (hA : 0 ≤ A) (hW : 0 ≤ W) (hL : primeSupplyEndpoint A W J ≤ L)
    {p : ℕ} (hp : p ∈ centeredPrimePool E A W J) :
    Real.exp A < (p : ℝ) ∧ (p : ℝ) ≤ Real.exp L := by
  obtain ⟨j, hj⟩ := mem_primeTuplePool.mp hp
  exact centeredPrimeSupply_global_bounds hA hW j.isLt hL hj

lemma paddingPrimeSupply_bounds (E : Finset ℕ) (L : ℝ) {p : ℕ}
    (hp : p ∈ paddingPrimeSupply E L) : (p : ℝ) ≤ Real.exp L :=
  modFivePrimesUpTo_le (Real.exp_pos _).le (Finset.mem_sdiff.mp hp).1

lemma actualProhibitedPrimeFamily_residue_bound (h J M : ℕ) (E : Finset ℕ)
    (A W L : ℝ) (eligible : ℕ → ℕ → Prop) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (hL : primeSupplyEndpoint A W J ≤ L)
    {p : ℕ}
    (hp : p ∈ (actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE).P ∪
      (actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE).Q) :
    p ≤ ⌊Real.exp L⌋₊ := by
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  rcases mem_union.mp hp with hp | hp
  · exact (centeredPrimePool_bounds E A W L J hA hW hL hp).2
  · exact paddingPrimeSupply_bounds E L hp

lemma centeredPrimePool_lower_nat (E : Finset ℕ) (A W L : ℝ) (J : ℕ)
    (hA : 0 ≤ A) (hW : 0 ≤ W) (hL : primeSupplyEndpoint A W J ≤ L)
    {p : ℕ} (hp : p ∈ centeredPrimePool E A W J) : ⌈Real.exp A⌉₊ ≤ p :=
  Nat.ceil_le.mpr (centeredPrimePool_bounds E A W L J hA hW hL hp).1.le


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeScale
namespace OAI

/-! Harmonic masses and integer endpoints for the literal prime family.
These derive the trace theorem's prime-pool hypotheses from the single
fixed-modulus published input. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma primeSupplyCount_mul_bound (W L : ℝ) (hW : 0 < W) (hL : 1 ≤ L) :
    (primeSupplyCount W L : ℝ) * (6 * W) ≤ (1 / 200 : ℝ) * Real.log L := by
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hj : (primeSupplyCount W L : ℝ) ≤
      ((1 / 200 : ℝ) * Real.log L) / (6 * W) := Nat.floor_le (by positivity)
  exact (le_div_iff₀ (by positivity : 0 < 6 * W)).mp hj



lemma centeredPrimeTuple_upper (E : Finset ℕ) (A W L : ℝ) (J : ℕ)
    (hA : 0 < A) (hW : 1 ≤ W) (hL : primeSupplyEndpoint A W J ≤ L)
    {d : ℕ} (hd : d ∈ primeTupleDivisors (centeredPrimeBands E A W J)) :
    d ≤ ⌊Real.exp (2 * L)⌋₊ := by
  have hb := centeredPrimeTuple_log_bound hA hW hL hd
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hb.1
  simpa only [Real.exp_log hdpos] using Real.exp_le_exp.mpr hb.2




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeBlockDimension
namespace OAI

/-! The actual tuple copies and the length-exp(103L) block fit the
exp(106L) starting-vertex allowance in the matrix trace. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma primeTuple_card_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (Dmax : ℕ)
    (hmax : ∀ d : (j : Fin J) → P j, (∏ j, (d j).val) ≤ Dmax) :
    Fintype.card ((j : Fin J) → P j) ≤ Dmax := by
  have hp (d : (j : Fin J) → P j) : 0 < ∏ j, (d j).val :=
    prod_pos (fun j _ => (hprime j _ (d j).property).pos)
  let f : ((j : Fin J) → P j) → Fin Dmax := fun d =>
    ⟨(∏ j, (d j).val) - 1, by have := hmax d; have := hp d; omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply primeTuple_injective hprime hdisjoint
    have he := congrArg Fin.val hab
    have ha := hp a
    have hb := hp b
    change (∏ j, (a j).val) - 1 = (∏ j, (b j).val) - 1 at he
    change (∏ j, (a j).val) = (∏ j, (b j).val)
    omega
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeAlphabetSize
namespace OAI

/-! The full forced-step alphabet includes all bounded padding divisors.
Its size still fits the polynomial exponential budget of finite-law
comparison; no eligibility restriction is needed for this count. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma boundedPaddingDivisor_real_upper (E : Finset ℕ) (L : ℝ) (hL : 1 ≤ L)
    (q : ℕ) (hq : q ∈ boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊) :
    (q : ℝ) ≤ Real.exp (100 * L ^ 2) := by
  have hr := (mem_filter.mp hq).1
  have hsq := retainedPrimeDivisor_squarefree (paddingPrimeSupply E L)
    (fun _ hp => paddingPrimeSupply_prime hp) hr
  have hpool := retainedPrimeDivisor_factors (paddingPrimeSupply E L)
    (fun _ hp => paddingPrimeSupply_prime hp) hr
  have hdeg : (q.primeFactors.card : ℝ) ≤ 100 * Real.log L :=
    (show (q.primeFactors.card : ℝ) ≤ (⌊100 * Real.log L⌋₊ : ℝ) by
      exact_mod_cast (mem_filter.mp hq).2).trans
        (Nat.floor_le (mul_nonneg (by norm_num) (Real.log_nonneg hL)))
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  calc
    _ = ∏ p ∈ q.primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
    _ ≤ ∏ _p ∈ q.primeFactors, Real.exp L :=
      Finset.prod_le_prod (fun p _ => Nat.cast_nonneg p)
        (fun p hp => paddingPrimeSupply_bounds E L (hpool hp))
    _ = Real.exp ((q.primeFactors.card : ℝ) * L) := by
      rw [prod_const, Real.exp_nat_mul]
    _ ≤ _ := by apply Real.exp_le_exp.mpr; nlinarith

lemma boundedPaddingDivisors_card (E : Finset ℕ) (L : ℝ) (hL : 1 ≤ L) :
    ((boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊).card : ℝ) ≤
      Real.exp (100 * L ^ 2) := by
  let Q := boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊
  let N := ⌊Real.exp (100 * L ^ 2)⌋₊
  have hp (q : Q) : 0 < q.val := retainedPrimeDivisor_pos (paddingPrimeSupply E L)
    (fun _ hp => paddingPrimeSupply_prime hp) (mem_filter.mp q.property).1
  have hq (q : Q) : q.val ≤ N :=
    (Nat.le_floor_iff (Real.exp_pos _).le).mpr (boundedPaddingDivisor_real_upper E L hL _ q.property)
  let f : Q → Fin N := fun q => ⟨q.val - 1, by have := hp q; have := hq q; omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have he : a.val - 1 = b.val - 1 := congrArg Fin.val hab
    have ha := hp a
    have hb := hp b
    omega
  have hc : Q.card ≤ N := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf
  exact (show (Q.card : ℝ) ≤ N by exact_mod_cast hc).trans (Nat.floor_le (Real.exp_pos _).le)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimePairCatalog
namespace OAI

/-! The tuple/padding pair catalog injects into its integer product:
the two factors have disjoint prime supports. Thus the numerical bin
endpoint bounds the whole catalog, without an extra tuple factor. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma ProhibitedPrimeFamily.pair_cross_coprime {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (a b : data.pairs) : a.val.1.Coprime b.val.2 := by
  apply (Nat.disjoint_primeFactors (data.tuple_squarefree _ a.property).ne_zero
    (data.padding_squarefree _ b.property).ne_zero).mp
  exact data.disjoint.mono (data.tuple_pool _ a.property) (data.padding_pool _ b.property)

lemma ProhibitedPrimeFamily.pair_product_injective {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) :
    Function.Injective (fun a : data.pairs => a.val.1 * a.val.2) := by
  intro a b hab
  change a.val.1 * a.val.2 = b.val.1 * b.val.2 at hab
  have hdab : a.val.1 ∣ b.val.1 := (data.pair_cross_coprime a b).dvd_of_dvd_mul_right
    (hab ▸ dvd_mul_right a.val.1 a.val.2)
  have hdba : b.val.1 ∣ a.val.1 := (data.pair_cross_coprime b a).dvd_of_dvd_mul_right
    (hab.symm ▸ dvd_mul_right b.val.1 b.val.2)
  have hd : a.val.1 = b.val.1 := Nat.dvd_antisymm hdab hdba
  have hq : a.val.2 = b.val.2 := by
    rw [← hd] at hab
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero (data.tuple_squarefree _ a.property).ne_zero) hab
  exact Subtype.ext (Prod.ext hd hq)

lemma ProhibitedPrimeFamily.pairs_card_le {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (B : ℕ)
    (hB : ∀ dq ∈ data.pairs, dq.1 * dq.2 ≤ B) : data.pairs.card ≤ B := by
  have hp (a : data.pairs) : 0 < a.val.1 * a.val.2 :=
    Nat.mul_pos (Nat.pos_of_ne_zero (data.tuple_squarefree _ a.property).ne_zero)
      (Nat.pos_of_ne_zero (data.padding_squarefree _ a.property).ne_zero)
  let f : data.pairs → Fin B := fun a =>
    ⟨a.val.1 * a.val.2 - 1, by have := hp a; have := hB _ a.property; omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply data.pair_product_injective
    change a.val.1 * a.val.2 = b.val.1 * b.val.2
    have he : a.val.1 * a.val.2 - 1 = b.val.1 * b.val.2 - 1 := congrArg Fin.val hab
    have ha := hp a
    have hb := hp b
    omega
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf

lemma paddingPairEligible_product_upper {L η : ℝ} {d q : ℕ}
    (hη : 0 < η) (hηone : η ≤ 1) (he : PaddingPairEligible L η d q) :
    d * q ≤ ⌊Real.exp (100 * L + 1)⌋₊ := by
  by_cases hz : d * q = 0
  · simp [hz]
  let j := paddingBin η 0 (Real.log (d * q : ℕ))
  have hj := (mem_paddingBinIndices_iff L η j hη).mp he.2
  have hx := (paddingBin_eq_iff η 0 (Real.log (d * q : ℕ)) j hη).mp rfl
  simp only [add_zero] at hx
  have hu : Real.log (d * q : ℕ) ≤ 100 * L + 1 := by
    nlinarith [hj.2, hx.2]
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  have hp : (0 : ℝ) < (d * q : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hz
  simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr hu

lemma actualProhibitedPrimeFamily_pairs_card (h J M : ℕ) (E : Finset ℕ)
    (A W L η : ℝ) (eligible : ℕ → ℕ → Prop) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (hL : 1 ≤ L)
    (hη : 0 < η) (hηone : η ≤ 1)
    (he : ∀ d q, eligible d q → PaddingPairEligible L η d q) :
    ((actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE).pairs.card : ℝ) ≤
      Real.exp (101 * L) := by
  let data := actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE
  have hb : data.pairs.card ≤ ⌊Real.exp (100 * L + 1)⌋₊ := by
    apply data.pairs_card_le
    intro dq hdq
    have hm := (actualProhibitedPrimeFamily_pairs h J M E A W L eligible hA hW hE
      dq.1 dq.2).mp hdq
    exact paddingPairEligible_product_upper hη hηone (he _ _ hm.2.2.2)
  have hbr : (data.pairs.card : ℝ) ≤ (⌊Real.exp (100 * L + 1)⌋₊ : ℝ) := by exact_mod_cast hb
  exact (hbr.trans (Nat.floor_le (Real.exp_pos _).le)).trans
    (Real.exp_le_exp.mpr (by linarith))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeTraceParameters
namespace OAI

/-! The canonical prime count and padding degree cap satisfy the numerical
budgets of the trace theorem with an absolute coefficient. -/

namespace TwoPointCorrelations

lemma prime_trace_degree_budget (W L : ℝ) (hW : 1 ≤ W) (hL : 1 ≤ L) :
    ((primeSupplyCount W L + ⌊100 * Real.log L⌋₊ : ℕ) : ℝ) ≤ 101 * Real.log L ∧
      (⌊100 * Real.log L⌋₊ : ℝ) ≤ 100 * Real.log L := by
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hcount := primeSupplyCount_mul_bound W L (by linarith) hL
  have hprod : (primeSupplyCount W L : ℝ) ≤ primeSupplyCount W L * (6 * W) := by
    have hb := mul_le_mul_of_nonneg_left hW (show (0 : ℝ) ≤ primeSupplyCount W L by positivity)
    nlinarith
  have hj : (primeSupplyCount W L : ℝ) ≤ Real.log L := by
    nlinarith
  have hm : (⌊100 * Real.log L⌋₊ : ℝ) ≤ 100 * Real.log L := Nat.floor_le (by positivity)
  refine ⟨?_, hm⟩
  push_cast
  linarith

lemma prime_trace_endpoints (L : ℝ) (hL : 1 ≤ L) :
    1 ≤ ⌊Real.exp L⌋₊ ∧
      (⌊Real.exp L⌋₊ : ℝ) ≤ Real.exp L ∧
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ ⌈Real.exp (L ^ (199 / 200 : ℝ))⌉₊ ∧
      (⌊Real.exp (100 * L + 1)⌋₊ : ℝ) ≤ Real.exp (100 * L + 1) ∧
      (⌊Real.exp (2 * L)⌋₊ : ℝ) ≤ Real.exp (2 * L) := by
  refine ⟨?_, Nat.floor_le (Real.exp_pos _).le, Nat.le_ceil _,
    Nat.floor_le (Real.exp_pos _).le, Nat.floor_le (Real.exp_pos _).le⟩
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  simpa only [Nat.cast_one] using Real.one_le_exp (by linarith : 0 ≤ L)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingWeights
namespace OAI

/-! The graph's literal padding weight and vertex normalization.
The normalization is the square root of `5^omega_Q(n)` and depends
only on the padding-prime residues, including at the integer zero. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





lemma actualPaddingCoefficient_nonneg (q : ℕ) : 0 ≤ actualPaddingCoefficient q := by
  unfold actualPaddingCoefficient
  positivity





















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingIntegerBounds
namespace OAI

/-! Truncated padding weights on actual integer intervals.  The finite
active-state comparison is used only after the degree restriction. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical










lemma paddingTiltNormalizer_one_le (Q : Finset ℕ) : 1 ≤ paddingTiltNormalizer Q := by
  calc
    1 = ∏ _p : Q, (1 : ℝ) := by simp
    _ ≤ paddingTiltNormalizer Q := by
      apply Finset.prod_le_prod
      · intro p _
        exact zero_le_one
      · intro p _
        exact le_add_of_nonneg_right (by positivity)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeDegreeTail
namespace OAI

/-! The prime-degree deletion under the literal full residue law.  The
positive tuple majorant has mean `2^omega(d)/d`, and its tilted degree
tail is exponentially small in `W * omega(d)`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





lemma positivePrimeWeight_nonneg (S : Finset ℕ) (n : ℤ) :
    0 ≤ positivePrimeWeight S n := by
  apply prod_nonneg
  intro p _
  split_ifs <;> positivity






namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)





end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DeletionRowSplit
namespace OAI

/-! Deterministic union bound for the three actual source deletions.
The disjoint logarithmic bins prevent an extra bin-count loss in the
tuple-degree term. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma weighted_three_deletions (w : ℝ) (hw : 0 ≤ w) (divisor A B C : Prop) :
    w * (if divisor ∧ (A ∨ B ∨ C) then 1 else 0) ≤
      w * (if divisor ∧ A then 1 else 0) +
      w * (if divisor ∧ B then 1 else 0) +
      w * (if divisor ∧ C then 1 else 0) := by
  by_cases hd : divisor <;> by_cases ha : A <;> by_cases hb : B <;> by_cases hc : C <;>
    simp [hd, ha, hb, hc] <;> linarith



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeMatrix
namespace OAI

/-! The residue-model trace bound for the actual prime supplies and padding
normalization. Its only analytic input is the cited fixed-modulus prime theorem. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma canonicalTraceFamily_residue_bound (h : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) :
    ∀ p ∈ (canonicalTraceFamily h E W L eligible hL hW hE).P ∪
      (canonicalTraceFamily h E W L eligible hL hW hE).Q, p ≤ ⌊Real.exp L⌋₊ :=
  fun _ hp => actualProhibitedPrimeFamily_residue_bound h _ _ E _ W L eligible _ _ hE
    (primeSupplyScale_endpoint W L (zero_lt_one.trans_le hW) hL) hp


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualProhibitedDensity
namespace OAI

/-! Apply the finite prohibited-word density estimate to the actual
prime bands and padding degree cap. No rare-event density hypothesis
is retained in this specialization. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma ProhibitedPrimeFamily.whole_factor_card_le {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (dq : ℕ × ℕ) (hdq : dq ∈ data.pairs) :
    (dq.2 * dq.1).primeFactors.card ≤ J + M := by
  rw [Nat.primeFactors_mul (data.padding_squarefree dq hdq).ne_zero
    (data.tuple_squarefree dq hdq).ne_zero]
  have hc := card_union_le dq.2.primeFactors dq.1.primeFactors
  rw [data.tuple_card dq hdq] at hc
  have hm := data.padding_card dq hdq
  omega

theorem ModFiveThetaInput.eventually_actual_prohibited_density
    (hP : ModFiveThetaInput) (h : ℕ) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (hL : 1 ≤ L) (eligible : ℕ → ℕ → Prop),
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let B := ⌊Real.exp L⌋₊
      let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hW hE
      (data.residueLaw B hB).probability (data.deletedEvent ⌊L ^ (1 / 10 : ℝ)⌋₊ B) ≤
        Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) := by
  have hs := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).eventually
    (eventually_ge_atTop 1)
  filter_upwards [eventually_prohibited_density 101 (by norm_num),
    hP.eventually_actual_pool_masses E W hW, hs] with L hd hm hs
  intro hL eligible
  let J := primeSupplyCount W L
  let M := ⌊100 * Real.log L⌋₊
  let s := ⌊L ^ (1 / 10 : ℝ)⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let B := ⌊Real.exp L⌋₊
  let H := ⌈Real.exp (L ^ (199 / 200 : ℝ))⌉₊
  let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hW hE
  have hspos : 1 ≤ s := by
    apply (Nat.le_floor_iff (Real.rpow_nonneg (zero_le_one.trans hL) _)).mpr
    simpa only [Nat.cast_one] using hs
  have hsupper : (s : ℝ) ≤ L ^ (1 / 10 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hL) _)
  have hslots : ((s * (J + M) : ℕ) : ℝ) ≤ 101 * s * Real.log L := by
    have hb := mul_le_mul_of_nonneg_left (prime_trace_degree_budget W L hW hL).1
      (show (0 : ℝ) ≤ s by positivity)
    push_cast at hb ⊢
    nlinarith
  have hlo (p : ℕ) (hp : p ∈ data.P) : H ≤ p := by
    apply centeredPrimePool_lower_nat E (L ^ (199 / 200 : ℝ)) W L J
      (Real.rpow_nonneg (zero_le_one.trans hL) _) (zero_le_one.trans hW)
      (primeSupplyScale_endpoint W L (zero_lt_one.trans_le hW) hL)
    exact hp
  exact hd h s J M B H data hB hspos hsupper hslots hm.2.2.1 hm.2.2.2.2.1
    hm.2.2.2.2.2 (Nat.le_ceil _) (prime_trace_endpoints L hL).1
    (prime_trace_endpoints L hL).2.1 hlo

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SourceDeletionTerms
namespace OAI

/-! The three source deletions at the actual, possibly bin-dependent,
integer sampling sites. Extra pair eligibility is retained in the rare
term and may be discarded in the two nonnegative numerical terms. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma uniformAverage_finset_sum {α ι : Type*} [Fintype α]
    (S : Finset ι) (f : ι → α → ℝ) :
    uniformAverage (fun x => ∑ i ∈ S, f i x) = ∑ i ∈ S, uniformAverage (f i) := by
  unfold uniformAverage
  rw [sum_comm, sum_div]



lemma positiveDeletionAtom_le (P Q R : Finset ℕ) (η : ℝ) (c : ℕ → ℝ)
    (L K W : ℝ) (eligible : ℤ → ℕ → ℕ → Prop) (bad : ℤ → ℤ → Prop)
    (j : ℤ) (d q : ℕ) (n : ℤ)
    (he : eligible j d q → actualPaddingBin η (c d) j q) :
    positiveDeletionAtom P Q R η c L K W eligible bad j d q n ≤
      paddingRejectionAtom Q d.primeFactors R (actualPaddingBin η (c d) j) L K q n +
      (if actualPaddingBin η (c d) j q then positiveDegreeCost P d.primeFactors W q n else 0) +
      (if eligible j d q then actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n *
        (if (q : ℤ) ∣ n ∧ bad j n then 1 else 0) else 0) := by
  have hw := mul_nonneg (actualPaddingCoefficient_nonneg q) (positivePrimeWeight_nonneg d.primeFactors n)
  by_cases h : eligible j d q
  · have hb := he h
    simp only [positiveDeletionAtom, h, hb, paddingRejectionAtom, positiveDegreeCost, ite_true]
    simpa using weighted_three_deletions _ hw ((q : ℤ) ∣ n)
      (¬integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
        (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n)
      (6 * W * d.primeFactors.card < (actualPaddingDegree P n : ℝ)) (bad j n)
  · simp only [positiveDeletionAtom, h, ite_false, add_zero]
    unfold paddingRejectionAtom positiveDegreeCost
    split_ifs <;> positivity


lemma shifted_source_deletion_split (P Q D R : Finset ℕ) (bins : Finset ℤ)
    (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ)
    (eligible : ℤ → ℕ → ℕ → Prop) (bad : ℤ → ℤ → Prop)
    (he : ∀ j ∈ bins, ∀ d ∈ D, ∀ q ∈ R,
      eligible j d q → actualPaddingBin η (c d) j q)
    (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ) :
    (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R, uniformAverage (fun x : Fin (N j) =>
      positiveDeletionAtom P Q R η c L K W eligible bad j d q ((a j + x.val : ℤ) + site j d q))) ≤
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R, uniformAverage (fun x : Fin (N j) =>
        paddingRejectionAtom Q d.primeFactors R (actualPaddingBin η (c d) j) L K q
          ((a j + x.val : ℤ) + site j d q))) +
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R.filter (actualPaddingBin η (c d) j),
        uniformAverage (fun x : Fin (N j) =>
          positiveDegreeCost P d.primeFactors W q ((a j + x.val : ℤ) + site j d q))) +
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R.filter (eligible j d),
        uniformAverage (fun x : Fin (N j) =>
          actualPaddingCoefficient q * positivePrimeWeight d.primeFactors ((a j + x.val : ℤ) + site j d q) *
            if (q : ℤ) ∣ ((a j + x.val : ℤ) + site j d q) ∧ bad j ((a j + x.val : ℤ) + site j d q)
              then 1 else 0)) := by
  have hi (j : ℤ) (pred : Prop) (f : Fin (N j) → ℝ) :
      uniformAverage (fun x => if pred then f x else 0) =
        if pred then uniformAverage f else 0 := by
    by_cases hp : pred <;> simp only [hp, ite_true, ite_false]
    simp only [uniformAverage, sum_const_zero, zero_div]
  have hs (j : ℤ) (hj : j ∈ bins) (d : ℕ) (hd : d ∈ D) (q : ℕ) (hq : q ∈ R) :=
    uniformAverage_mono (fun x : Fin (N j) =>
      positiveDeletionAtom_le P Q R η c L K W eligible bad j d q
        ((a j + x.val : ℤ) + site j d q) (he j hj d hd q hq))
  have hadd (j : ℤ) (f g k : Fin (N j) → ℝ) :
      uniformAverage (fun x => f x + g x + k x) =
        uniformAverage f + uniformAverage g + uniformAverage k := by
    simp only [uniformAverage, sum_add_distrib, add_div]
  simp only [hadd, hi] at hs
  have hs' := sum_le_sum (fun j hj => sum_le_sum (fun d hd =>
    sum_le_sum (fun q hq => hs j hj d hd q hq)))
  simp only [sum_add_distrib] at hs'
  simpa only [sum_filter] using hs'

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShiftedRareDeletion
namespace OAI

/-! The actual rare-event deletion bound is unchanged by separate endpoint
shifts for each pair. All arithmetic and circuit budgets are supplied here. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical




theorem ModFiveThetaInput.eventually_shifted_canonical_rare_deletion_uniform
    (hP : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ (h : ℕ) (E : Finset ℕ)
      (hE : ∀ p, p.Prime → p ∣ h → p ∈ E),
      ∀ (W C : ℝ) (hW : 10 ≤ W) (_hC : 0 ≤ C), ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ (eligible : ℕ → ℕ → Prop),
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      let M := ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL (by linarith) hE
      let padding := canonicalPairPadding Q M eligible
      ∀ T : ℝ, 0 ≤ T → T ≤ Real.exp (C * Real.log L) →
      ∀ (site : ℕ → ℕ → ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      T * uniformAverage (fun x : Fin N =>
        shiftedProhibitedRow data ⌊L ^ (1 / 10 : ℝ)⌋₊ (primeTupleDivisors P) padding
          site (a + x.val)) ≤
        Real.exp (-L ^ (9 / 10 : ℝ)) + T * Real.exp (101 * L) * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_shifted_actual_prohibited_deletion_uniform hP
  refine ⟨A, hA, ?_⟩
  intro h E hE W C hW hC
  have hWone : 1 ≤ W := by linarith
  have hb := hb E W C hW hC
  filter_upwards [hb, hP.eventually_actual_prohibited_density h E hE W hWone,
    hP.eventually_actual_pool_masses E W hWone, eventually_ge_atTop (4800 : ℝ)]
      with L hb hd hm hlarge
  intro hL η hη hηone eligible he
  dsimp only
  let J := primeSupplyCount W L
  let M := ⌊100 * Real.log L⌋₊
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let data := canonicalTraceFamily h E W L eligible hL hWone hE
  let padding := canonicalPairPadding Q M eligible
  let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hWone hE
  have hpool : (data.P ∪ data.Q).Nonempty := by
    by_contra hn
    have hempty : data.P = ∅ := not_nonempty_iff_eq_empty.mp
      (fun hp => hn (hp.mono subset_union_left))
    have hp := hm.2.2.1
    change 1 ≤ primeHarmonicMass data.P at hp
    rw [hempty] at hp
    norm_num [primeHarmonicMass] at hp
  have hJM : ((J + M : ℕ) : ℝ) ≤ L ^ 2 :=
    (prime_trace_degree_budget W L hWone hL).1.trans (by
      have hlog : Real.log L ≤ L :=
        (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      nlinarith)
  have hJ : (J : ℝ) ≤ L ^ 2 := by
    have hjle : (J : ℝ) ≤ ((J + M : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right J M
    exact hjle.trans hJM
  have hs : (⌊L ^ (1 / 10 : ℝ)⌋₊ : ℝ) ≤ L := by
    apply (Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hL) _)).trans
    simpa using Real.rpow_le_rpow_of_exponent_le hL (show (1 / 10 : ℝ) ≤ 1 by norm_num)
  have hpair : (data.pairs.card : ℝ) ≤ Real.exp (101 * L) :=
    actualProhibitedPrimeFamily_pairs_card h J M E (L ^ (199 / 200 : ℝ)) W L η eligible
      (Real.rpow_nonneg (zero_le_one.trans hL) _) (zero_le_one.trans hWone) hE hL hη hηone he
  have hpadding (d : ℕ) (_hd : d ∈ primeTupleDivisors P) :
      padding d ⊆ retainedPrimeDivisors data.Q := by
    intro q hq
    exact (mem_filter.mp (mem_filter.mp hq).1).1
  have hqdegree (d : ℕ) (_hd : d ∈ primeTupleDivisors P) (q : ℕ) (hq : q ∈ padding d) :
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L := by
    have hM : q.primeFactors.card ≤ M := (mem_filter.mp (mem_filter.mp hq).1).2
    have hMr : (q.primeFactors.card : ℝ) ≤ M := by exact_mod_cast hM
    exact hMr.trans (prime_trace_degree_budget W L hWone hL).2
  have hpairs (d : ℕ) (hd : d ∈ primeTupleDivisors P) (q : ℕ) (hq : q ∈ padding d) :
      (d, q) ∈ data.pairs := by
    have hm := mem_filter.mp hq
    have hq' := mem_filter.mp hm.1
    exact (actualProhibitedPrimeFamily_pairs h J M E (L ^ (199 / 200 : ℝ)) W L eligible
      (Real.rpow_nonneg (zero_le_one.trans hL) _) (zero_le_one.trans hWone) hE d q).mpr
      ⟨hd, hq'.1, hq'.2, hm.2⟩
  intro T hT hTcap site a N hN
  have ht := hb h M ⌊Real.exp L⌋₊ ⌊L ^ (1 / 10 : ℝ)⌋₊ (J + M) data rfl rfl hB
    hpool (Nat.floor_le (Real.exp_pos _).le) hs hJM hpair data.whole_factor_card_le
    (hd hL eligible) hJ (primeTupleDivisors P) subset_rfl padding hpadding hqdegree hpairs
    T hT hTcap site a N hN
  apply ht.trans
  have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpair hT)
    (Real.exp_pos (-(L ^ 9))).le
  linarith



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShiftedVariableRare
namespace OAI

/-! Sum the canonical rare-site deletion over bins with separately
chosen integer intervals. The polynomial bin count is absorbed by
the proved second-moment rare-event estimate. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem ModFiveThetaInput.eventually_shifted_variable_rare_deletion_uniform
    (hP : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ (h : ℕ) (E : Finset ℕ)
      (hE : ∀ p, p.Prime → p ∣ h → p ∈ E),
      ∀ (W C : ℝ) (hW : 10 ≤ W) (_hC : 0 ≤ C), ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ (bins : Finset ℤ) (eligible : ℤ → ℕ → ℕ → Prop),
      (∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q) →
      (bins.card : ℝ) ≤ Real.exp (C * Real.log L) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      let M := ⌊100 * Real.log L⌋₊
      ∀ (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ), (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
      (∑ j ∈ bins, uniformAverage (fun x : Fin (N j) =>
        shiftedProhibitedRow (canonicalTraceFamily h E W L (eligible j) hL (by linarith) hE)
          ⌊L ^ (1 / 10 : ℝ)⌋₊ (primeTupleDivisors P) (canonicalPairPadding Q M (eligible j))
            (site j) (a j + x.val))) ≤
        Real.exp (-L ^ (9 / 10 : ℝ)) + bins.card * Real.exp (101 * L) * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hP.eventually_shifted_canonical_rare_deletion_uniform hBr
  refine ⟨A, hA, ?_⟩
  intro h E hE W C hW hC
  have hb := hb h E hE W C hW hC
  filter_upwards [hb] with L hb
  intro hL η hη hηone bins eligible he hbins
  dsimp only
  intro site a N hN
  by_cases hempty : bins = ∅
  · subst bins
    simp only [sum_empty, card_empty, Nat.cast_zero, zero_mul, add_zero]
    positivity
  let T : ℝ := bins.card
  let cost := fun j : ℤ => uniformAverage (fun x : Fin (N j) =>
    shiftedProhibitedRow (canonicalTraceFamily h E W L (eligible j) hL (by linarith) hE)
      ⌊L ^ (1 / 10 : ℝ)⌋₊
      (primeTupleDivisors (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)))
      (canonicalPairPadding (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊ (eligible j))
      (site j) (a j + x.val))
  have hT : 0 < T := by
    dsimp only [T]
    exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr hempty)
  have heach (j : ℤ) (hj : j ∈ bins) : T * cost j ≤
      Real.exp (-L ^ (9 / 10 : ℝ)) + T * Real.exp (101 * L) * Real.exp (-(L ^ 9)) :=
    hb hL η hη hηone (eligible j) (he j hj) T hT.le hbins (site j) (a j) (N j) (hN j hj)
  have hsum : T * (∑ j ∈ bins, cost j) ≤
      T * (Real.exp (-L ^ (9 / 10 : ℝ)) + T * Real.exp (101 * L) * Real.exp (-(L ^ 9))) := by
    rw [mul_sum]
    calc
      _ ≤ ∑ _j ∈ bins, (Real.exp (-L ^ (9 / 10 : ℝ)) +
          T * Real.exp (101 * L) * Real.exp (-(L ^ 9))) := sum_le_sum heach
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; rfl
  exact le_of_mul_le_mul_left hsum hT


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalShiftedDeletion
namespace OAI

/-! The one-endpoint deletion bound for the literal prime supplies.
Every bin may have its own integer interval. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


theorem BravermanDepth22Input.eventually_canonical_shifted_source_deletion_uniform_oai
    (hBr : BravermanDepth22Input) (hP : ModFiveThetaInput) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ (h : ℕ) (E : Finset ℕ)
      (hE : ∀ p, p.Prime → p ∣ h → p ∈ E),
      ∀ (W Cbins : ℝ) (hW : 10 ≤ W) (_hC : 0 ≤ Cbins),
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η K : ℝ), 0 < η → η ≤ 1 → 0 < K →
      ∀ (bins : Finset ℤ) (c : ℕ → ℝ) (eligible : ℤ → ℕ → ℕ → Prop),
      (bins.card : ℝ) ≤ Real.exp (Cbins * Real.log L) →
      (∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q) →
      (∀ j ∈ bins, ∀ d q, eligible j d q → actualPaddingBin η (c d) j q) →
      ∀ (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ),
      (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      canonicalShiftedSourceDeletion h E W L η K hL (by linarith) hE bins c eligible site a N /
        (paddingTiltNormalizer (paddingPrimeSupply E L) * ∏ j, primeHarmonicMass (P j)) ≤
        (2 : ℝ) ^ J * (C / K + L ^ (-100 : ℝ) + Real.exp (-2 * W * J)) +
          2 * Real.exp (-L ^ (9 / 10 : ℝ)) := by
  obtain ⟨Ap, hAp, hp⟩ := hBr.eventually_shifted_padding_deletion_uniform hP
  obtain ⟨Ad, hAd, hd⟩ := hBr.eventually_shifted_tuple_degree_deletion
  obtain ⟨Ar, hAr, hr⟩ := hP.eventually_shifted_variable_rare_deletion_uniform hBr
  let A := Ap + Ad + Ar
  refine ⟨A, by dsimp [A]; omega, ?_⟩
  intro h E hE W Cbins hW hC
  obtain ⟨Cp, hCp, hp⟩ := hp E
  have hr := hr h E hE W Cbins hW hC
  refine ⟨Cp, hCp, ?_⟩
  filter_upwards [hp, hd, hr, hP.eventually_actual_pool_masses E W (by linarith),
    eventually_deletion_comparison_error Cbins hC, eventually_ge_atTop (4800 : ℝ)]
      with L hp hd hr hm herr hlarge
  intro hL η K hη hηone hK bins c eligible hbins helig hbin site a N hN
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
  let D := primeTupleDivisors P
  let data := canonicalTraceFamily h E W L (fun _ _ => False) hL (by linarith) hE
  let hB := canonicalTraceFamily_residue_bound h E W L (fun _ _ => False) hL (by linarith) hE
  let bad := fun j n => ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
    (fun d q => (d, q) ∈ (canonicalTraceFamily h E W L (eligible j) hL (by linarith) hE).pairs) n
  let S := paddingTiltNormalizer Q
  let V := ∏ j, primeHarmonicMass (P j)
  let pad := ∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R, uniformAverage (fun x : Fin (N j) =>
    paddingRejectionAtom Q d.primeFactors R (actualPaddingBin η (c d) j) L K q
      ((a j + x.val : ℤ) + site j d q))
  let deg := ∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R.filter (actualPaddingBin η (c d) j),
    uniformAverage (fun x : Fin (N j) =>
      positiveDegreeCost (primeTuplePool P) d.primeFactors W q ((a j + x.val : ℤ) + site j d q))
  let rare := ∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R.filter (eligible j d),
    uniformAverage (fun x : Fin (N j) => actualPaddingCoefficient q *
      positivePrimeWeight d.primeFactors ((a j + x.val : ℤ) + site j d q) *
        if (q : ℤ) ∣ ((a j + x.val : ℤ) + site j d q) ∧ bad j ((a j + x.val : ℤ) + site j d q)
          then 1 else 0)
  have hN' (A' : ℕ) (hA' : A' ≤ A) (j : ℤ) (hj : j ∈ bins) :
      Real.exp (L ^ A' / 2) ≤ (N j : ℝ) :=
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ hL hA') (by norm_num))).trans (hN j hj)
  have hprime : ∀ j, ∀ p ∈ P j, p.Prime := centeredPrimeBands_prime _ _ _ _
  have hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l) :=
    centeredPrimeBands_disjoint _ _ _ _ (Real.rpow_nonneg (zero_le_one.trans hL) _) (by linarith)
  have hpool : (data.P ∪ data.Q).Nonempty := by
    by_contra hn
    have hempty : data.P = ∅ := not_nonempty_iff_eq_empty.mp
      (fun hp => hn (hp.mono subset_union_left))
    have hx := hm.2.2.1
    change 1 ≤ primeHarmonicMass data.P at hx
    rw [hempty] at hx
    norm_num [primeHarmonicMass] at hx
  have hJ : (J : ℝ) ≤ L ^ 2 := by
    have ht := (prime_trace_degree_budget W L (by linarith) hL).1
    have hj : (J : ℝ) ≤ ((J + ⌊100 * Real.log L⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right J ⌊100 * Real.log L⌋₊
    have hl : Real.log L ≤ L :=
      (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    exact hj.trans (ht.trans (by nlinarith))
  have hR : R ⊆ retainedPrimeDivisors data.Q := filter_subset _ _
  have hdegree : ∀ q ∈ R, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L := by
    intro q hq
    have hx : (q.primeFactors.card : ℝ) ≤ (⌊100 * Real.log L⌋₊ : ℝ) := by
      exact_mod_cast (mem_filter.mp hq).2
    exact hx.trans (prime_trace_degree_budget W L (by linarith) hL).2
  have hpad := hp h J ⌊100 * Real.log L⌋₊ ⌊Real.exp L⌋₊ data rfl hB hpool
    (Nat.floor_le (Real.exp_pos _).le) P rfl hprime hdisjoint hJ D subset_rfl R hR hdegree
      bins η K c hη hηone hK site a N (hN' Ap (by dsimp [A]; omega))
  have hdeg := hd h J ⌊100 * Real.log L⌋₊ ⌊Real.exp L⌋₊ data hB hpool
    (Nat.floor_le (Real.exp_pos _).le) P rfl hprime hdisjoint W hW
      (fun j => (hm.2.1 j).2.1) hJ
      (by have ht := primeSupplyCount_mul_bound W L (by linarith) hL; nlinarith [Real.log_nonneg hL])
      D subset_rfl R hR hdegree bins η c hη site a N (hN' Ad (by dsimp [A]; omega))
  have hrare := hr hL η hη hηone bins eligible helig hbins site a N
    (hN' Ar (by dsimp [A]; omega))
  have hrare' : rare ≤ Real.exp (-L ^ (9 / 10 : ℝ)) +
      bins.card * Real.exp (101 * L) * Real.exp (-(L ^ 9)) := by
    simpa only [shiftedProhibitedRow, uniformAverage_finset_sum, canonicalPairPadding] using hrare
  have hS : 1 ≤ S := paddingTiltNormalizer_one_le Q
  have hV : 1 ≤ V := by
    apply Finset.one_le_prod
    intro j _
    exact (hm.2.1 j).1
  have hDcard : (D.card : ℝ) ≤ Real.exp (2 * L) := by
    have hc : D.card ≤ Fintype.card ((j : Fin J) → P j) := by
      exact (card_image_le).trans_eq card_univ
    have ht := primeTuple_card_le P hprime hdisjoint ⌊Real.exp (2 * L)⌋₊ (fun d =>
      centeredPrimeTuple_upper E _ W L J
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le hL) _) (by linarith)
        (primeSupplyScale_endpoint W L (by linarith) hL) (mem_image.mpr ⟨d, mem_univ _, rfl⟩))
    exact (show (D.card : ℝ) ≤ (⌊Real.exp (2 * L)⌋₊ : ℝ) by exact_mod_cast hc.trans ht).trans
      (Nat.floor_le (Real.exp_pos _).le)
  have herror := herr bins.card D.card R.card S V (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hbins hDcard (boundedPaddingDivisors_card E L hL) hS hV
  have hsplit := shifted_source_deletion_split (primeTuplePool P) Q D R bins η c L K W
    eligible bad (fun j hj d _ q _ => hbin j hj d q) site a N
  have hpad' : pad ≤ S * V * (2 : ℝ) ^ J * (Cp / K + L ^ (-100 : ℝ)) +
      2 * bins.card * D.card * R.card * Real.exp (-(L ^ 9)) := by
    change pad / S ≤ (2 : ℝ) ^ J * V * (Cp / K + L ^ (-100 : ℝ)) +
      (2 * bins.card * D.card * R.card * Real.exp (-(L ^ 9))) / S at hpad
    have hx := (div_le_iff₀ (show 0 < S from paddingTiltNormalizer_pos Q)).mp hpad
    rw [add_mul, div_mul_cancel₀ _ (show 0 < S from paddingTiltNormalizer_pos Q).ne'] at hx
    nlinarith
  have hdeg' : deg ≤ S * V * (2 : ℝ) ^ J * Real.exp (-2 * W * J) +
      bins.card * D.card * R.card * Real.exp (-(L ^ 9)) := by
    change deg ≤ ((2 : ℝ) ^ J * V) * S * Real.exp (-2 * W * J) +
      bins.card * D.card * R.card * Real.exp (-(L ^ 9)) at hdeg
    convert (preTransparency := .instances) hdeg using 1; ring
  have hn := normalize_three_deletion_costs
    (canonicalShiftedSourceDeletion h E W L η K hL (by linarith) hE bins c eligible site a N)
    pad deg rare S V ((2 : ℝ) ^ J) (Cp / K + L ^ (-100 : ℝ))
      (Real.exp (-2 * W * J)) (Real.exp (-L ^ (9 / 10 : ℝ)))
      (2 * bins.card * D.card * R.card * Real.exp (-(L ^ 9)))
      (bins.card * D.card * R.card * Real.exp (-(L ^ 9)))
      (bins.card * Real.exp (101 * L) * Real.exp (-(L ^ 9)))
    hS hV (Real.exp_pos _).le hsplit hpad' hdeg' hrare'
  have heq :
      (2 * bins.card * D.card * R.card * Real.exp (-(L ^ 9)) +
        bins.card * D.card * R.card * Real.exp (-(L ^ 9)) +
        bins.card * Real.exp (101 * L) * Real.exp (-(L ^ 9))) /
        (S * V) ≤ Real.exp (-L ^ (9 / 10 : ℝ)) := by
    convert (preTransparency := .instances) herror using 1; ring
  change _ / (S * V) ≤ _
  linarith


end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_canonical_shifted_source_deletion_uniform_oai := @OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_canonical_shifted_source_deletion_uniform_oai
