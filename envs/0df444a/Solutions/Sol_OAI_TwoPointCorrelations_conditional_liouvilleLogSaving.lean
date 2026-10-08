-- Prove2me | solution 1 for OAI.TwoPointCorrelations.conditional_liouvilleLogSaving
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:43:08.347982+00:00
-- url     : https://prove2.me/submissions/5ddeb564-1596-4658-a8f4-7d7c6105b01f

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_BravermanDepth22Input_eventually_canonical_shifted_source_deletion_uniform
import Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_actual_retained_bin_uniform
import Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_canonical_retained_mass
import Theorems.Thm_OAI_TwoPointCorrelations_quantitative_centering_assembly

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h

/-- Multiplying the two affine arguments by the opposite slopes gives an exact
identity. There is no coprimality restriction on any coefficient. -/
theorem liouville_affine_dilation (a₁ a₂ b₁ b₂ n : ℕ)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    liouville (a₁ * n + b₁) * liouville (a₂ * n + b₂) =
      liouville (a₁ * a₂) * liouville (a₂ * (a₁ * n + b₁)) *
        liouville (a₁ * (a₂ * n + b₂)) := by
  have hs := liouville_sq (Nat.mul_ne_zero ha₁ ha₂)
  calc
    _ = liouville (a₁ * a₂) ^ 2 *
        (liouville (a₁ * n + b₁) * liouville (a₂ * n + b₂)) := by rw [hs, one_mul]
    _ = _ := by simp only [liouville_mul]; ring

/-- The orientation with `a₂ b₁ ≤ a₁ b₂`; the opposite orientation is obtained
by swapping the two factors. This is manuscript equation (q:quant-affine-identity). -/
theorem liouville_affine_ordered (a₁ a₂ b₁ b₂ n : ℕ)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (horder : a₂ * b₁ ≤ a₁ * b₂) :
    liouville (a₁ * n + b₁) * liouville (a₂ * n + b₂) =
      liouville (a₁ * a₂) * liouville (a₁ * a₂ * n + a₂ * b₁) *
        liouville (a₁ * a₂ * n + a₂ * b₁ + (a₁ * b₂ - a₂ * b₁)) := by
  rw [liouville_affine_dilation a₁ a₂ b₁ b₂ n ha₁ ha₂]
  congr 2
  · congr 1; ring
  · calc
      a₁ * (a₂ * n + b₂) = a₁ * a₂ * n + a₁ * b₂ := by ring
      _ = a₁ * a₂ * n + a₂ * b₁ + (a₁ * b₂ - a₂ * b₁) := by omega


theorem liouville_oneBounded : OneBounded liouville := by
  intro n hn
  have hs : ‖liouville n‖ ^ 2 = 1 := by
    rw [← norm_pow, liouville_sq hn.ne', norm_one]
  nlinarith [norm_nonneg (liouville n)]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.AffineTransfer
namespace OAI

/-!
# Exact progression and affine endpoint identities

These finite identities implement the endpoint step of §8 of the manuscript.
They include nonunit residue classes and do not assume any cancellation theorem.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations


lemma progression_interval_image (l b N : ℕ) (hl : 0 < l) :
    (Finset.Icc 1 N).image (fun n => l * n + b) =
      (Finset.Ioc b (l * N + b)).filter (fun m => m % l = b % l) := by
  ext m
  simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨n, ⟨hn, hnN⟩, rfl⟩
    constructor
    · constructor
      · have : 0 < l * n := Nat.mul_pos hl hn
        omega
      · exact Nat.add_le_add_right (Nat.mul_le_mul_left l hnN) b
    · simp
  · rintro ⟨⟨hbm, hmN⟩, hmod⟩
    have hdvd : l ∣ m - b := Nat.ModEq.dvd' hmod.symm
    obtain ⟨n, hn⟩ := hdvd
    have heq : l * n + b = m := by omega
    refine ⟨n, ⟨?_, ?_⟩, heq⟩
    · by_contra h
      have hn0 : n = 0 := by omega
      subst n
      simp only [Nat.mul_zero, zero_add] at heq
      omega
    · exact Nat.le_of_mul_le_mul_left (by omega : l * n ≤ l * N) hl

/-- Exact extraction of an affine subsequence from two progression prefixes. -/
theorem affine_sum_eq_residue_prefix (u : ℕ → ℂ) (l b N : ℕ) (hl : 0 < l) :
    (∑ n ∈ Finset.Icc 1 N, u (l * n + b)) =
      residuePrefix u l b (l * N + b) - residuePrefix u l b b := by
  have hinj : Set.InjOn (fun n : ℕ => l * n + b) (Finset.Icc 1 N) := by
    intro n hn m hm hnm
    exact Nat.eq_of_mul_eq_mul_left hl (Nat.add_right_cancel hnm)
  have hsum : (∑ n ∈ Finset.Icc 1 N, u (l * n + b)) =
      ∑ m ∈ (Finset.Ioc b (l * N + b)).filter (fun m => m % l = b % l), u m := by
    rw [← progression_interval_image l b N hl, Finset.sum_image hinj]
  have hsplit := Finset.sum_Ioc_consecutive
    (fun m => if m % l = b % l then u m else 0)
    (Nat.zero_le b) (Nat.le_add_left b (l * N))
  unfold residuePrefix
  rw [hsum, Finset.sum_filter]
  exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hsplit)

/-- The ordered Liouville affine sum has exactly the progression endpoints
specified in the manuscript, with no condition on the residue class. -/
theorem liouville_affine_sum_endpoints (a₁ a₂ b₁ b₂ N : ℕ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (horder : a₂ * b₁ ≤ a₁ * b₂) :
    affineSum liouville liouville a₁ a₂ b₁ b₂ N =
      liouville (a₁ * a₂) *
        (residuePrefix (fun m => liouville m * liouville (m + (a₁ * b₂ - a₂ * b₁)))
            (a₁ * a₂) (a₂ * b₁) (a₁ * a₂ * N + a₂ * b₁) -
          residuePrefix (fun m => liouville m * liouville (m + (a₁ * b₂ - a₂ * b₁)))
            (a₁ * a₂) (a₂ * b₁) (a₂ * b₁)) := by
  unfold affineSum
  simp_rw [liouville_affine_ordered a₁ a₂ b₁ b₂ _ ha₁.ne' ha₂.ne' horder]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [mul_assoc] using affine_sum_eq_residue_prefix
    (fun m => liouville m * liouville (m + (a₁ * b₂ - a₂ * b₁)))
    (a₁ * a₂) (a₂ * b₁) N (Nat.mul_pos ha₁ ha₂)

/-- Swapping the two factors does not alter an affine correlation. -/
theorem affineSum_swap (f g : ℕ → ℂ) (a₁ a₂ b₁ b₂ N : ℕ) :
    affineSum f g a₁ a₂ b₁ b₂ N = affineSum g f a₂ a₁ b₂ b₁ N := by
  unfold affineSum
  apply Finset.sum_congr rfl
  intro n hn
  exact mul_comm _ _

/-- The exact endpoint formula with either determinant sign. -/
theorem liouville_affine_sum_endpoints_all (a₁ a₂ b₁ b₂ N : ℕ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) :
    let l := a₁ * a₂
    let b := min (a₂ * b₁) (a₁ * b₂)
    let h := Nat.dist (a₁ * b₂) (a₂ * b₁)
    affineSum liouville liouville a₁ a₂ b₁ b₂ N =
      liouville l *
        (residuePrefix (fun m => liouville m * liouville (m + h)) l b (l * N + b) -
          residuePrefix (fun m => liouville m * liouville (m + h)) l b b) := by
  dsimp
  rcases le_total (a₂ * b₁) (a₁ * b₂) with hle | hle
  · rw [min_eq_left hle, Nat.dist_eq_sub_of_le_right hle]
    exact liouville_affine_sum_endpoints a₁ a₂ b₁ b₂ N ha₁ ha₂ hle
  · rw [affineSum_swap, min_eq_right hle, Nat.dist_eq_sub_of_le hle]
    simpa only [Nat.mul_comm a₁ a₂] using
      liouville_affine_sum_endpoints a₂ a₁ b₂ b₁ N ha₂ ha₁ hle


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SelfAdjointPath
namespace OAI

/-!
# Positivity along an invertible self-adjoint path

The resolvent path in manuscript Lemma `q:noncommuting` starts at the
identity and is self-adjoint and invertible throughout a real interval.
Its positivity follows from continuity of the least Rayleigh quotient.
The argument is carried out in finite dimension.
-/

open _root_.Filter

namespace TwoPointCorrelations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Nontrivial E]






@[simp] lemma leastRayleigh_id : leastRayleigh (ContinuousLinearMap.id ℂ E) = 1 := by
  let : Nonempty {x : E // x ≠ 0} := ⟨⟨Classical.choose (exists_ne (0 : E)),
    Classical.choose_spec (exists_ne (0 : E))⟩⟩
  have hpoint (x : {x : E // x ≠ 0}) :
      (ContinuousLinearMap.id ℂ E).rayleighQuotient x = 1 := by
    have hn : ‖(x : E)‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr x.property)
    simp only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.id_apply,
      inner_self_eq_norm_sq_to_K]
    norm_cast
    exact div_self hn
  simp [leastRayleigh, hpoint]



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IntegerLiouville
namespace OAI

/-! The real Liouville test function on ambient integer vertices and
the exact cancellation of the square-root weights on each directed edge. -/

namespace TwoPointCorrelations

open scoped _root_.Classical


lemma liouville_norm_le_one (n : ℕ) : ‖liouville n‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [liouville]
  · exact liouville_oneBounded n (Nat.pos_of_ne_zero hn)

lemma integerLiouville_norm_le_one (n : ℤ) : ‖integerLiouville n‖ ≤ 1 :=
  liouville_norm_le_one _




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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeSupplyScale
namespace OAI

/-! The literal scale choice of the manuscript satisfies all prime-supply
mass and support hypotheses; no prime-family existence premise remains. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma eventually_primeSupplyCount_pos (W : ℝ) (hW : 0 < W) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ primeSupplyCount W L := by
  filter_upwards [eventually_ge_atTop (Real.exp (1200 * W))] with L hL
  have hLp : 0 < L := (Real.exp_pos _).trans_le hL
  have hl : 1200 * W ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hL
  have hl0 : 0 ≤ Real.log L := le_trans (by positivity : (0 : ℝ) ≤ 1200 * W) hl
  unfold primeSupplyCount
  apply (Nat.le_floor_iff (by positivity : 0 ≤ ((1 / 200 : ℝ) * Real.log L) / (6 * W))).mpr
  norm_num
  apply (le_div_iff₀ (by positivity : 0 < 6 * W)).mpr
  linarith


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShortSumSampling
namespace OAI

/-!
# Sampling the published short-interval estimate

For integral short lengths, a moving short sum is constant on each unit
cell of its origin. Thus its published integral controls the actual finite
sum of integer origins, with outer cutoff `Y+1`. The progression restriction
is an average of fixed frequencies and has total coefficient mass one.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical






lemma sum_Icc_shift (f : ℕ → ℂ) (v D : ℕ) :
    (∑ n ∈ Icc (v + 1) (v + D), f n) = ∑ m ∈ range D, f (v + m + 1) := by
  symm
  apply sum_bij (fun m _ => v + m + 1)
  · intro m hm
    simp only [mem_range] at hm
    simp only [mem_Icc]
    omega
  · intro m hm n hn he
    omega
  · intro n hn
    simp only [mem_Icc] at hn
    refine ⟨n - (v + 1), ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro m _
    rfl









end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.QuantitativeAffineTransfer
namespace OAI

/-! Quantitative passage from all progression classes to the main
affine Liouville statement. The logarithmic exponent is preserved. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology

lemma progressionSum_eq_residuePrefix (f g : ℕ → ℂ) (h l b N : ℕ) :
    progressionSum f g h l b N =
      residuePrefix (fun n => f n * g (n + h)) l b N := by
  have hs : Icc 1 N = Ioc 0 N := by
    ext n
    simp only [mem_Icc, mem_Ioc]
    omega
  simp only [progressionSum, residuePrefix, sum_filter, hs]

lemma liouville_affine_norm_le (a₁ a₂ b₁ b₂ N : ℕ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) :
    ‖affineSum liouville liouville a₁ a₂ b₁ b₂ N‖ ≤ N := by
  unfold affineSum
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖liouville (a₁ * n + b₁) * liouville (a₂ * n + b₂)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Icc 1 N, (1 : ℝ) := by
      apply sum_le_sum
      intro n hn
      have hnpos := (mem_Icc.mp hn).1
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (liouville_oneBounded _ (by nlinarith))).trans
          (liouville_oneBounded _ (by nlinarith))
    _ = _ := by simp

lemma eventually_log_power_le_self (c : ℝ) :
    ∀ᶠ X : ℝ in atTop, (Real.log X) ^ c ≤ X := by
  have hb := (isLittleO_log_rpow_rpow_atTop c (show (0 : ℝ) < 1 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with X hb hX
  simpa only [Real.rpow_one, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hX) _),
    abs_of_nonneg (zero_le_one.trans hX), one_mul] using hb

lemma affine_cutoff_log_bound (c X : ℝ) (l b : ℕ)
    (hc : 0 ≤ c) (hX : 4 ≤ X) (hl : 0 < l) :
    ((l * ⌊X⌋₊ + b : ℕ) : ℝ) /
        (Real.log ((l * ⌊X⌋₊ + b : ℕ) : ℝ)) ^ c ≤
      ((l + b : ℕ) : ℝ) * (2 : ℝ) ^ c * X / (Real.log X) ^ c := by
  let Y : ℝ := (l * ⌊X⌋₊ + b : ℕ)
  have hXp : 0 < X := by linarith
  have hYlower : X / 2 ≤ Y := by
    have hf := Nat.lt_floor_add_one X
    have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have hn : (0 : ℝ) ≤ ⌊X⌋₊ := Nat.cast_nonneg _
    have hh : (⌊X⌋₊ : ℝ) ≤ Y := by
      dsimp only [Y]
      push_cast
      nlinarith [show (0 : ℝ) ≤ b from Nat.cast_nonneg b]
    linarith
  have hYupper : Y ≤ ((l + b : ℕ) : ℝ) * X := by
    have hf := Nat.floor_le hXp.le
    have hXone : 1 ≤ X := by linarith
    dsimp only [Y]
    push_cast
    nlinarith [show (0 : ℝ) ≤ l from Nat.cast_nonneg l,
      show (0 : ℝ) ≤ b from Nat.cast_nonneg b]
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlog4 : 2 * Real.log 2 ≤ Real.log X := by
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [← he]
    exact Real.log_le_log (by norm_num) hX
  have hlogY : Real.log X / 2 ≤ Real.log Y := by
    have hh := Real.log_le_log (by positivity : 0 < X / 2) hYlower
    rw [Real.log_div hXp.ne' (by norm_num)] at hh
    linarith
  have hden : (Real.log X / 2) ^ c ≤ (Real.log Y) ^ c :=
    Real.rpow_le_rpow (by positivity) hlogY hc
  change Y / (Real.log Y) ^ c ≤ _
  calc
    _ ≤ (((l + b : ℕ) : ℝ) * X) / (Real.log X / 2) ^ c :=
      div_le_div₀ (by positivity) hYupper (Real.rpow_pos_of_pos (by positivity) _) hden
    _ = _ := by
      rw [Real.div_rpow hlogX.le (by norm_num)]
      rw [div_div_eq_mul_div]
      ring

lemma real_log_saving_extend (F : ℝ → ℂ) (c : ℝ) (hc : 0 < c)
    (htrivial : ∀ X : ℝ, 3 ≤ X → ‖F X‖ ≤ X)
    (hlarge : ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ‖F X‖ ≤ C * X / (Real.log X) ^ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      ‖F X‖ ≤ C * X / (Real.log X) ^ c := by
  obtain ⟨C, hC, hb⟩ := hlarge
  obtain ⟨B, hB⟩ := eventually_atTop.1 hb
  let Z : ℝ := max B 3
  let K : ℝ := C + (Real.log Z) ^ c + 1
  have hZ : 3 ≤ Z := le_max_right _ _
  have hlogZ : 0 < Real.log Z := Real.log_pos (by linarith)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro X hX
  have hXp : 0 < X := by linarith
  have hlogX : 0 < (Real.log X) ^ c := Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
  by_cases hx : Z ≤ X
  · apply (hB X ((le_max_left _ _).trans hx)).trans
    apply div_le_div_of_nonneg_right _ hlogX.le
    have hCK : C ≤ K := by
      dsimp only [K]
      have hp := Real.rpow_nonneg hlogZ.le c
      linarith
    exact mul_le_mul_of_nonneg_right hCK hXp.le
  · have hxl : (Real.log X) ^ c ≤ (Real.log Z) ^ c :=
      Real.rpow_le_rpow (Real.log_pos (by linarith)).le
        (Real.log_le_log hXp (le_of_not_ge hx)) hc.le
    apply (htrivial X hX).trans
    apply (le_div_iff₀ hlogX).mpr
    have hk : (Real.log X) ^ c ≤ K := by
      dsimp only [K]
      linarith
    nlinarith

theorem liouvilleLogSaving_of_progression
    (hprog : ∃ c : ℝ, 0 < c ∧ ∀ h l b : ℕ, 0 < h → 0 < l →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
        ‖progressionSum liouville liouville h l b ⌊X⌋₊‖ ≤
          C * X / (Real.log X) ^ c) : LiouvilleLogSaving := by
  obtain ⟨c, hc, hprog⟩ := hprog
  refine ⟨c, hc, ?_⟩
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hneq
  let l := a₁ * a₂
  let b := min (a₂ * b₁) (a₁ * b₂)
  let h := Nat.dist (a₁ * b₂) (a₂ * b₁)
  have hl : 0 < l := Nat.mul_pos ha₁ ha₂
  have hh : 0 < h := Nat.dist_pos_of_ne hneq
  obtain ⟨C, hC, hp⟩ := hprog h l b hh hl
  let u : ℕ → ℂ := fun m => liouville m * liouville (m + h)
  let d : ℝ := ‖residuePrefix u l b b‖
  have hd : 0 ≤ d := norm_nonneg _
  have hsample : Tendsto (fun X : ℝ => ((l * ⌊X⌋₊ + b : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    filter_upwards [(tendsto_nat_floor_atTop (α := ℝ)).eventually
      (eventually_ge_atTop ⌈max B 0⌉₊)] with X hX
    have hn : ⌊X⌋₊ ≤ l * ⌊X⌋₊ + b := by nlinarith
    have hb : B ≤ (⌈max B 0⌉₊ : ℝ) :=
      (le_max_left _ _).trans (Nat.le_ceil _)
    exact hb.trans (by exact_mod_cast hX.trans hn)
  apply real_log_saving_extend _ c hc
    (fun X hX => (liouville_affine_norm_le a₁ a₂ b₁ b₂ ⌊X⌋₊ ha₁ ha₂).trans
      (Nat.floor_le (by linarith)))
  refine ⟨C * ((l + b : ℕ) : ℝ) * (2 : ℝ) ^ c + d, by
    have hlb : (0 : ℝ) < (l + b : ℕ) := by exact_mod_cast (by omega : 0 < l + b)
    positivity, ?_⟩
  filter_upwards [hsample.eventually hp, eventually_log_power_le_self c,
    eventually_ge_atTop (4 : ℝ)] with X hp hlog hX
  have hY := affine_cutoff_log_bound c X l b hc.le hX hl
  have hXp : 0 < X := by linarith
  have hden : 0 < (Real.log X) ^ c := Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
  have hboundary : d ≤ d * (X / (Real.log X) ^ c) := by
    have hr : 1 ≤ X / (Real.log X) ^ c := (one_le_div hden).mpr hlog
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hr hd
  have hprefix : ‖residuePrefix u l b (l * ⌊X⌋₊ + b)‖ ≤
      C * ((l * ⌊X⌋₊ + b : ℕ) : ℝ) /
        (Real.log ((l * ⌊X⌋₊ + b : ℕ) : ℝ)) ^ c := by
    simpa only [Nat.floor_natCast, progressionSum_eq_residuePrefix, u] using hp
  rw [liouville_affine_sum_endpoints_all a₁ a₂ b₁ b₂ ⌊X⌋₊ ha₁ ha₂]
  change ‖liouville l * (residuePrefix u l b (l * ⌊X⌋₊ + b) -
    residuePrefix u l b b)‖ ≤ _
  calc
    _ ≤ ‖residuePrefix u l b (l * ⌊X⌋₊ + b) - residuePrefix u l b b‖ :=
      (norm_mul_le _ _).trans (by
        exact mul_le_of_le_one_left (norm_nonneg _) (liouville_oneBounded l hl))
    _ ≤ ‖residuePrefix u l b (l * ⌊X⌋₊ + b)‖ + d := norm_sub_le _ _
    _ ≤ C * (((l + b : ℕ) : ℝ) * (2 : ℝ) ^ c * X / (Real.log X) ^ c) +
        d * (X / (Real.log X) ^ c) :=
      add_le_add (hprefix.trans (by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hY hC.le)) hboundary
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ForestCodeAsymptotics
namespace OAI

/-! Absorbing the sublinear endpoint and exceptional-position costs. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma eventually_sublinear_log_cost (d C : ℝ) (hd : d < 1) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, C * L ^ d * Real.log L ≤ L := by
  by_cases hzero : C = 0
  · filter_upwards [eventually_ge_atTop 0] with L hL
    simpa only [hzero, zero_mul] using hL
  have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
  have hb := (isLittleO_log_rpow_atTop (show 0 < 1 - d by linarith)).bound
    (show 0 < 1 / C by positivity)
  filter_upwards [eventually_ge_atTop 1, hb] with L hL hb
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL), Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hb
  calc
    C * L ^ d * Real.log L ≤ C * L ^ d * ((1 / C) * L ^ (1 - d)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (C * (1 / C)) * (L ^ d * L ^ (1 - d)) := by ring
    _ = L := by
      rw [mul_one_div_cancel hzero, one_mul, ← Real.rpow_add hLp,
        show d + (1 - d) = 1 by ring, Real.rpow_one]



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DivisibilityPrefix
namespace OAI

/-! Exact change of variables `x=u*z` for a divisibility indicator,
including the floor endpoint `floor(X/u)`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma positivePrefix_eq_Icc (F : ℕ → ℂ) (X : ℕ) :
    positivePrefix F X = ∑ n ∈ Icc 1 X, F n := by
  simpa only [Nat.zero_add, positivePrefix] using (sum_Icc_shift F 0 X).symm


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


lemma paddingBinIndices_card (L η : ℝ) (hL : 0 ≤ L) (hη : 0 < η) :
    ((paddingBinIndices L η).card : ℝ) ≤ 100 * L / η + 1 := by
  have hf : 0 ≤ ⌊100 * L / η⌋ := Int.floor_nonneg.mpr (by positivity)
  have hc : ((paddingBinIndices L η).card : ℝ) = (⌊100 * L / η⌋ : ℝ) + 1 := by
    have hh := Int.card_Icc_of_le 0 ⌊100 * L / η⌋
      (show (0 : ℤ) ≤ ⌊100 * L / η⌋ + 1 by omega)
    simp only [sub_zero] at hh
    change ((Icc (0 : ℤ) ⌊100 * L / η⌋).card : ℝ) = _
    exact_mod_cast hh
  rw [hc]
  linarith [Int.floor_le (100 * L / η)]






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







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedRowScale
namespace OAI

/-! At a fixed W the retained row majorant grows polynomially in L;
it can therefore be absorbed into a small exponential boundary budget. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma primeSupplyCount_le_log (W L : ℝ) (hW : 1 ≤ W) (hL : 1 ≤ L) :
    (primeSupplyCount W L : ℝ) ≤ Real.log L := by
  have hb := primeSupplyCount_mul_bound W L (by linarith) hL
  have hJ : 0 ≤ (primeSupplyCount W L : ℝ) := Nat.cast_nonneg _
  nlinarith [Real.log_nonneg hL]




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingBinCount
namespace OAI

/-! Bounds for the actual finite bin set at eta = exp(-J). -/

namespace TwoPointCorrelations

open _root_.Filter

lemma paddingBinIndices_card_linear (L η : ℝ) (hL : 1 ≤ L)
    (hη : 0 < η) (hηone : η ≤ 1) :
    ((paddingBinIndices L η).card : ℝ) ≤ 101 * L / η := by
  have hb := paddingBinIndices_card L η (by linarith) hη
  have hratio : 1 ≤ L / η := (one_le_div hη).mpr (by linarith)
  have he : 101 * L / η = 100 * L / η + L / η := by ring
  rw [he]
  linarith

lemma paddingBinIndices_card_polynomial (L W : ℝ) (hL : 101 ≤ L) (hW : 1 ≤ W) :
    ((paddingBinIndices L (Real.exp (-(primeSupplyCount W L : ℝ)))).card : ℝ) ≤
      Real.exp (3 * Real.log L) := by
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hJ := primeSupplyCount_le_log W L hW hLone
  have he : Real.exp (primeSupplyCount W L) ≤ L := by
    simpa only [Real.exp_log hLp] using Real.exp_le_exp.mpr hJ
  have hη : Real.exp (-(primeSupplyCount W L : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hb := paddingBinIndices_card_linear L (Real.exp (-(primeSupplyCount W L : ℝ)))
    hLone (Real.exp_pos _) hη
  calc
    _ ≤ 101 * L / Real.exp (-(primeSupplyCount W L : ℝ)) := hb
    _ = 101 * L * Real.exp (primeSupplyCount W L) := by rw [Real.exp_neg]; field_simp
    _ ≤ 101 * L * L := mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ L ^ 3 := by
      have hx := mul_le_mul_of_nonneg_right hL (sq_nonneg L)
      nlinarith
    _ = _ := by
      rw [show 3 * Real.log L = (3 : ℕ) * Real.log L by norm_num,
        Real.exp_nat_mul, Real.exp_log hLp]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QuantitativeParameterChoice
namespace OAI

/-! The manuscript's final exponential savings at eta = exp(-J),
K = exp(4J), and a fixed sufficiently large W. -/

namespace TwoPointCorrelations

lemma two_pow_eq_exp (J : ℕ) : (2 : ℝ) ^ J = Real.exp ((J : ℝ) * Real.log 2) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  congr 1
  ring

lemma quantitative_small_terms (L W : ℝ) (J : ℕ) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hJ : 60 * (J : ℝ) ≤ Real.log L) :
    Real.exp J * (2 : ℝ) ^ J * L ^ (-1 / 20 : ℝ) ≤ Real.exp (-(J : ℝ)) ∧
    (2 : ℝ) ^ J * Real.exp (-4 * (J : ℝ)) ≤ Real.exp (-(J : ℝ)) ∧
    (2 : ℝ) ^ J * L ^ (-100 : ℝ) ≤ Real.exp (-(J : ℝ)) ∧
    (2 : ℝ) ^ J * Real.exp (-2 * W * J) ≤ Real.exp (-(J : ℝ)) := by
  have hLp : 0 < L := by linarith
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogtwo : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have htwo : (J : ℝ) * Real.log 2 ≤ J := by nlinarith
  have hWJ : (J : ℝ) ≤ W * J := by nlinarith
  rw [two_pow_eq_exp]
  simp only [Real.rpow_def_of_pos hLp]
  repeat rw [← Real.exp_add]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Real.exp_le_exp.mpr <;> nlinarith

lemma quantitative_spectral_term (C W : ℝ) (J : ℕ) (hC : 0 ≤ C) (hW : 0 < W)
    (hchoice : Real.exp 5 * (C / Real.sqrt W) ≤ Real.exp (-1)) :
    Real.exp (5 * (J : ℝ)) * (C / Real.sqrt W) ^ J ≤ Real.exp (-(J : ℝ)) := by
  have he : Real.exp (5 * (J : ℝ)) = (Real.exp 5) ^ J := by
    rw [mul_comm, Real.exp_nat_mul]
  rw [he, ← mul_pow]
  have hp := pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le (by positivity)) hchoice J
  calc
    _ ≤ (Real.exp (-1)) ^ J := hp
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma primeSupplyCount_final_budget (L W : ℝ) (hL : 1 ≤ L) (hW : 1 ≤ W) :
    60 * (primeSupplyCount W L : ℝ) ≤ Real.log L := by
  have hj := primeSupplyCount_mul_bound W L (by linarith) hL
  have hJ0 : (0 : ℝ) ≤ primeSupplyCount W L := Nat.cast_nonneg _
  nlinarith

lemma primeSupplyCount_saving (L W : ℝ) (hL : 1 ≤ L) (_hW : 0 < W) :
    Real.exp (-(primeSupplyCount W L : ℝ)) ≤
      Real.exp 1 * L ^ (-(1 / (1200 * W)) : ℝ) := by
  have hLp : 0 < L := by linarith
  have hf := Nat.lt_floor_add_one (((1 / 200 : ℝ) * Real.log L) / (6 * W))
  have he : ((1 / 200 : ℝ) * Real.log L) / (6 * W) = Real.log L / (1200 * W) := by ring
  change ((1 / 200 : ℝ) * Real.log L) / (6 * W) < (primeSupplyCount W L : ℝ) + 1 at hf
  rw [he] at hf
  rw [Real.rpow_def_of_pos hLp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hz : Real.log L * (-(1 / (1200 * W))) = -(Real.log L / (1200 * W)) := by ring
  rw [hz]
  linarith

lemma exists_fixed_spectral_parameter (C : ℝ) (hC : 0 ≤ C) :
    ∃ W : ℝ, 10 ≤ W ∧ Real.exp 5 * (C / Real.sqrt W) ≤ Real.exp (-1) := by
  let a := Real.exp 6 * C + 4
  have ha : 4 ≤ a := by
    have hp := mul_nonneg (Real.exp_pos (6 : ℝ)).le hC
    dsimp only [a]
    linarith
  have hap : 0 < a := by linarith
  refine ⟨a ^ 2, by nlinarith, ?_⟩
  rw [Real.sqrt_sq hap.le, ← mul_div_assoc]
  apply (div_le_iff₀ hap).mpr
  have he : Real.exp (-1) * Real.exp 6 = Real.exp 5 := by
    rw [← Real.exp_add]
    norm_num
  dsimp [a]
  rw [mul_add, ← mul_assoc, he]
  linarith [Real.exp_pos (-1)]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FinalErrorScale
namespace OAI

/-! The residual rare-site and summed block-boundary errors are below
the same exp(-J) saving as the principal terms. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma eventually_rare_error_saving (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, Real.exp (-L ^ (9 / 10 : ℝ)) ≤
      Real.exp (-(primeSupplyCount W L : ℝ)) := by
  have hs := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 9 / 10 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hs] with L hL hs
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL), Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by linarith : 0 < L) _), one_mul] at hs
  apply Real.exp_le_exp.mpr
  have hj := primeSupplyCount_le_log W L hW hL
  linarith

lemma eventually_bin_error_saving (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      (L / Real.exp (-(primeSupplyCount W L : ℝ))) * Real.exp (-L) ≤
        Real.exp (-(primeSupplyCount W L : ℝ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_sublinear_log_cost 0 3 (by norm_num) (by norm_num)] with L hL hs
  simp only [Real.rpow_zero, mul_one] at hs
  have hLp : 0 < L := by linarith
  have hj := primeSupplyCount_le_log W L hW hL
  have he : L / Real.exp (-(primeSupplyCount W L : ℝ)) =
      Real.exp (Real.log L + (primeSupplyCount W L : ℝ)) := by
    rw [Real.exp_add, Real.exp_log hLp, Real.exp_neg, div_inv_eq_mul]
  rw [he, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LogSavingScale
namespace OAI

/-! Convert the fixed prime-count saving into the final logarithmic
power, retaining a single exponent for all affine coefficients. -/

namespace TwoPointCorrelations

lemma primeSupplyCount_log_saving (X W : ℝ) (A : ℕ) (hX : Real.exp 1 ≤ X)
    (hW : 0 < W) (hA : 0 < A) :
    Real.exp (-(primeSupplyCount W ((Real.log X) ^ (1 / (A : ℝ))) : ℝ)) ≤
      Real.exp 1 / (Real.log X) ^ (1 / (1200 * W * A) : ℝ) := by
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hX
  have hlogp : 0 < Real.log X := by linarith
  have hL : 1 ≤ (Real.log X) ^ (1 / (A : ℝ)) :=
    Real.one_le_rpow hlog (by positivity)
  have hp := primeSupplyCount_saving ((Real.log X) ^ (1 / (A : ℝ))) W hL hW
  apply hp.trans_eq
  rw [← Real.rpow_mul hlogp.le]
  have he : (1 / (A : ℝ)) * (-(1 / (1200 * W))) = -(1 / (1200 * W * A)) := by ring
  rw [he, Real.rpow_neg hlogp.le]
  rfl

lemma log_saving_exponent_pos (W : ℝ) (A : ℕ) (hW : 0 < W) (hA : 0 < A) :
    0 < (1 / (1200 * W * A) : ℝ) := by positivity

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.BinCutoffGeometry
namespace OAI

/-! The literal logarithmic bin places T/(dq) between X exp(-eta)
and X. Floor normalization introduces a scalar of norm at most one. -/

namespace TwoPointCorrelations


lemma floor_cutoff_weight_norm_le (T : ℝ) (hT : 0 < T) :
    ‖(⌊T⌋₊ : ℂ) / (T : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  exact (div_le_one hT).mpr (Nat.floor_le hT.le)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.NumericalBins
namespace OAI

/-! One common eligibility predicate for the literal manuscript bins.
Positivity makes the log-product identity valid even outside the prime pools. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma numericalBinEligible_bin (L η : ℝ) (j : ℤ) (d q : ℕ)
    (he : numericalBinEligible L η j d q) : actualPaddingBin η (Real.log d) j q := he.2.2.2

lemma numericalBinEligible_pair (L η : ℝ) (hη : 0 < η) (j : ℤ)
    (hj : j ∈ paddingBinIndices L η) (d q : ℕ) (he : numericalBinEligible L η j d q) :
    PaddingPairEligible L η d q := by
  refine ⟨he.2.2.1, ?_⟩
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast he.1.ne'
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast he.2.1.ne'
  have hlog : Real.log (d * q : ℕ) = Real.log q + Real.log d := by
    rw [Nat.cast_mul, Real.log_mul hd hq]
    ring
  have hb : paddingBin η 0 (Real.log (d * q : ℕ)) = j := by
    apply (paddingBin_eq_iff η 0 (Real.log (d * q : ℕ)) j hη).mpr
    simpa only [actualPaddingBin, hlog, add_zero] using he.2.2.2
  rw [hb]
  exact hj


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

lemma abs_centeredTuple_le_positivePrimeWeight (S : Finset ℕ) (n : ℤ) :
    |centeredTuple S n| ≤ positivePrimeWeight S n := by
  rw [centeredTuple, abs_prod]
  apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
  intro p _
  have hi : 0 ≤ (if (p : ℤ) ∣ n then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have hp : 0 ≤ (p : ℝ)⁻¹ := by positivity
  simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hi, abs_of_nonneg hp, one_div] using
    abs_sub_le (if (p : ℤ) ∣ n then (1 : ℝ) else 0) 0 (p : ℝ)⁻¹





namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)





end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DivisorEndpointSymmetry
namespace OAI

/-! Positive tuple/padding edge weights are unchanged when the origin
is moved to the other endpoint. Both signs of the shift are included. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma positivePrimeWeight_add_multiple (d : ℕ) (n c : ℤ) :
    positivePrimeWeight d.primeFactors (n + (d : ℤ) * c) =
      positivePrimeWeight d.primeFactors n := by
  unfold positivePrimeWeight
  apply prod_congr rfl
  intro p hp
  have hpd : (p : ℤ) ∣ (d : ℤ) := by exact_mod_cast Nat.dvd_of_mem_primeFactors hp
  have hc : (p : ℤ) ∣ (d : ℤ) * c := dvd_mul_of_dvd_left hpd c
  have he : (p : ℤ) ∣ n + (d : ℤ) * c ↔ (p : ℤ) ∣ n := by
    constructor
    · intro hn
      simpa only [add_sub_cancel_right] using dvd_sub hn hc
    · intro hn
      exact dvd_add hn hc
  simp only [he]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalCenteringBins
namespace OAI

/-! Sum the actual partial-centering errors over the logarithmic bins.
The interval exponent remains the absolute value 1000. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma bin_cutoff_ge (L η X : ℝ) (hη : 0 < η) (hX : 0 ≤ X)
    (j : ℤ) (hj : j ∈ paddingBinIndices L η) :
    X ≤ X * Real.exp ((j : ℝ) * η) := by
  have hj0 : (0 : ℝ) ≤ j := by
    exact_mod_cast ((mem_paddingBinIndices_iff L η j hη).mp hj).1
  have he : 1 ≤ Real.exp ((j : ℝ) * η) := Real.one_le_exp (mul_nonneg hj0 hη.le)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he hX



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QuantitativeFinalWindows
namespace OAI

/-! The final logarithmic bins meet both the analytic and spectral
long-window hypotheses, uniformly in the absolute exponent A. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma exp_neg_nat_lt_log_two (J : ℕ) (hJ : 1 ≤ J) :
    Real.exp (-(J : ℝ)) < Real.log 2 := by
  have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have he : 2 < Real.exp 1 := by
    linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
  have hi : (Real.exp 1)⁻¹ < (1 / 2 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ (Real.exp_pos 1)).mpr
    linarith
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    linarith
  calc
    _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    _ < (1 / 2 : ℝ) := by simpa only [Real.exp_neg] using hi
    _ ≤ _ := hl

lemma floor_exp_half_bound (Y T : ℝ) (hY : 2 ≤ Y) (hT : Real.exp Y ≤ T) :
    Real.exp (Y / 2) ≤ (⌊T⌋₊ : ℝ) := by
  let E := Real.exp (Y / 2)
  have hE : 2 ≤ E := by
    have he := Real.add_one_le_exp (Y / 2)
    dsimp only [E]
    linarith
  have hsq : E * E ≤ T := by
    calc
      _ = Real.exp Y := by
        dsimp only [E]
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ T := hT
  have hf := Nat.lt_floor_add_one T
  change E ≤ _
  nlinarith

lemma final_bin_windows (L X η : ℝ) (A : ℕ) (hL : 2 ≤ L)
    (hA : 1000 ≤ A) (hX : Real.exp (L ^ A) ≤ X) (hη : 0 < η)
    (j : ℤ) (hj : j ∈ paddingBinIndices L η) :
    Real.exp (L ^ (1000 : ℝ)) ≤ X ∧
      Real.exp (L ^ A / 2) ≤ (⌊X * Real.exp ((j : ℝ) * η)⌋₊ : ℝ) := by
  have hLone : 1 ≤ L := by linarith
  have hAp : A ≠ 0 := by omega
  have hpow : L ^ (1000 : ℝ) ≤ L ^ A := by
    rw [Real.rpow_ofNat]
    exact pow_le_pow_right₀ hLone hA
  have hY : 2 ≤ L ^ A := hL.trans (le_self_pow₀ hLone hAp)
  have hXp : 0 < X := (Real.exp_pos _).trans_le hX
  exact ⟨(Real.exp_le_exp.mpr hpow).trans hX,
    floor_exp_half_bound _ _ hY
      (hX.trans (bin_cutoff_ge L η X hη hXp.le j hj))⟩

theorem eventually_quantitative_final_windows (W : ℝ) (hW : 0 < W) :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧ 1 ≤ primeSupplyCount W L ∧
      0 < Real.exp (-(primeSupplyCount W L : ℝ)) ∧
      Real.exp (-(primeSupplyCount W L : ℝ)) < Real.log 2 ∧
      ∀ (A : ℕ), 1000 ≤ A → ∀ (X : ℝ), Real.exp (L ^ A) ≤ X →
        Real.exp (L ^ (1000 : ℝ)) ≤ X ∧
        ∀ j ∈ paddingBinIndices L (Real.exp (-(primeSupplyCount W L : ℝ))),
          Real.exp (L ^ A / 2) ≤
            (⌊X * Real.exp ((j : ℝ) * Real.exp (-(primeSupplyCount W L : ℝ)))⌋₊ : ℝ) := by
  filter_upwards [eventually_primeSupplyCount_pos W hW, eventually_ge_atTop (2 : ℝ)]
    with L hJ hL
  refine ⟨hL, hJ, Real.exp_pos _, exp_neg_nat_lt_log_two _ hJ, ?_⟩
  intro A hA X hX
  have hLone : 1 ≤ L := by linarith
  have hpow : L ^ (1000 : ℝ) ≤ L ^ A := by
    rw [Real.rpow_ofNat]
    exact pow_le_pow_right₀ hLone hA
  refine ⟨(Real.exp_le_exp.mpr hpow).trans hX, ?_⟩
  intro j hj
  exact (final_bin_windows L X _ A hL hA hX (Real.exp_pos _) j hj).2

lemma final_log_scale_exact (X : ℝ) (A : ℕ) (hX : 1 ≤ X) (hA : A ≠ 0) :
    Real.exp (((Real.log X) ^ (1 / (A : ℝ))) ^ A) = X := by
  have hp : ((Real.log X) ^ (1 / (A : ℝ))) ^ A = Real.log X := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow (Real.log_nonneg hX) hA
  rw [hp, Real.exp_log (zero_lt_one.trans_le hX)]

lemma final_log_scale_tendsto (A : ℕ) (hA : 0 < A) :
    Tendsto (fun X : ℝ => (Real.log X) ^ (1 / (A : ℝ))) atTop atTop := by
  have hAp : (0 : ℝ) < A := by exact_mod_cast hA
  exact (tendsto_rpow_atTop (one_div_pos.mpr hAp)).comp Real.tendsto_log_atTop

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






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedBinSummation
namespace OAI

/-! Sum the retained bin estimates and divide by the retained harmonic
mass. No extra factor is hidden in the mass normalization. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma retained_bin_sum_normalize (bins : Finset ℤ) (C : ℤ → ℂ)
    (S V S₀ L l R ε : ℝ) (hS : 0 < S) (hV : 0 < V) (hL : 0 < L)
    (hS₀ : S * V / 2 ≤ S₀)
    (hC : ∀ j ∈ bins, ‖C j‖ ≤ 3 * l ^ 2 * S * R / L + 3 * ε) :
    ‖∑ j ∈ bins, C j‖ / S₀ ≤
      (6 * bins.card * l ^ 2 * R) / (L * V) + (6 * bins.card * ε) / (S * V) := by
  have hp : 0 < S * V / 2 := by positivity
  have hs : ‖∑ j ∈ bins, C j‖ ≤ bins.card * (3 * l ^ 2 * S * R / L + 3 * ε) := by
    calc
      _ ≤ ∑ j ∈ bins, ‖C j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ bins, (3 * l ^ 2 * S * R / L + 3 * ε) := sum_le_sum hC
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  calc
    _ ≤ ‖∑ j ∈ bins, C j‖ / (S * V / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hp hS₀
    _ ≤ (bins.card * (3 * l ^ 2 * S * R / L + 3 * ε)) / (S * V / 2) :=
      div_le_div_of_nonneg_right hs hp.le
    _ = _ := by field_simp; ring

lemma retained_bin_sum_mass_lower (bins : Finset ℤ) (C : ℤ → ℂ)
    (S V S₀ L l R ε W : ℝ) (J : ℕ)
    (hS : 1 ≤ S) (hW : 1 ≤ W) (hV : W ^ J ≤ V) (hL : 0 < L)
    (hS₀ : S * V / 2 ≤ S₀) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hC : ∀ j ∈ bins, ‖C j‖ ≤ 3 * l ^ 2 * S * R / L + 3 * ε) :
    ‖∑ j ∈ bins, C j‖ / S₀ ≤
      (6 * bins.card * l ^ 2 / L) * (R / W ^ J) + 6 * bins.card * ε := by
  have hWp : 0 < W := by linarith
  have hVone : 1 ≤ V := (one_le_pow₀ hW).trans hV
  have hSV : 1 ≤ S * V := by nlinarith
  have hb := retained_bin_sum_normalize bins C S V S₀ L l R ε
    (by linarith) (by linarith) hL hS₀ hC
  apply hb.trans
  have hfirst : (6 * bins.card * l ^ 2 * R) / (L * V) ≤
      (6 * bins.card * l ^ 2 / L) * (R / W ^ J) := by
    calc
      _ ≤ (6 * bins.card * l ^ 2 * R) / (L * W ^ J) := by
        gcongr
      _ = _ := by ring
  have hsecond : (6 * bins.card * ε) / (S * V) ≤ 6 * bins.card * ε :=
    div_le_self (by positivity) hSV
  exact add_le_add hfirst hsecond

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.WeightedRetainedBins
namespace OAI

/-! Real bin endpoints introduce factors floor(T)/T of norm at most one.
The per-bin spectral bounds remain valid with these factors. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem ModFiveThetaInput.eventually_canonical_weighted_bin_sum_uniform
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h l : ℕ) (_hh : 0 < h) (_hl : 0 < l) (E : Finset ℕ)
        (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
        (_hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W),
      ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ (bins : Finset ℤ) (eligible : ℤ → ℕ → ℕ → Prop),
        (∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q) →
      ∀ (b : ℕ) (N : ℤ → ℕ) (v : ℤ → ℂ),
        (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
        (∀ j ∈ bins, ‖v j‖ ≤ 1) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let R := Real.exp 1 * (2 * (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      ‖∑ j ∈ bins, v j * canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE (N j)‖ /
        totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η ≤
        (6 * bins.card * (l : ℝ) ^ 2 / L) * (R / W ^ J) +
          6 * bins.card * Real.exp (-L) := by
  obtain ⟨A, hA, hb⟩ := hprime.eventually_actual_retained_bin_uniform hBr
  refine ⟨A, hA, ?_⟩
  intro h l hh hl E hE hEl W hW
  filter_upwards [hb h l hh hl E hE hEl W hW,
    hprime.eventually_canonical_retained_mass E W hW] with L hb hm
  intro hL η hη hηone bins eligible he b N v hN hv
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let S := paddingTiltNormalizer (paddingPrimeSupply E L)
  let V := ∏ j, primeHarmonicMass (P j)
  let R := Real.exp 1 * (2 * (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J))
  have hmass := hm hL η hη
  have hbound (j : ℤ) (hj : j ∈ bins) :
      ‖v j * canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE (N j)‖ ≤
        3 * (l : ℝ) ^ 2 * S * R / L + 3 * Real.exp (-L) := by
    rw [norm_mul]
    calc
      _ ≤ 1 * ‖canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE (N j)‖ :=
        mul_le_mul_of_nonneg_right (hv j hj) (norm_nonneg _)
      _ = ‖canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE (N j)‖ := one_mul _
      _ ≤ _ := hb hL η hη hηone (eligible j) (he j hj) b (N j) (hN j hj)
  exact retained_bin_sum_mass_lower bins
    (fun j => v j * canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE (N j))
    S V (totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η)
    L l R (Real.exp (-L)) W J (paddingTiltNormalizer_one_le _) hW hmass.1
    (by linarith) hmass.2 (by positivity) (Real.exp_pos _).le hbound

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedFinalScale
namespace OAI

/-! The retained graph contribution at the final fixed parameter choice.
The interval exponent is chosen before all affine coefficients. -/

namespace TwoPointCorrelations

open _root_.Filter
open scoped _root_.Classical

lemma retained_spectral_scale (L W : ℝ) (J : ℕ) (l : ℕ) (B : ℝ)
    (hL : 0 < L) (hW : 0 < W) (_hB : 0 ≤ B)
    (hbins : B ≤ 101 * L / Real.exp (-(J : ℝ)))
    (hchoice : Real.exp 5 * ((2 * Real.exp 150) / Real.sqrt W) ≤ Real.exp (-1))
    (herr : L / Real.exp (-(J : ℝ)) * Real.exp (-L) ≤ Real.exp (-(J : ℝ))) :
    (6 * B * (l : ℝ) ^ 2 / L) *
      ((Real.exp 1 * (2 * (Real.exp (4 * J) *
        (2 * Real.exp 150 * Real.sqrt W) ^ J))) / W ^ J) +
      6 * B * Real.exp (-L) ≤
        (1212 * Real.exp 1 * (l : ℝ) ^ 2 + 606) * Real.exp (-(J : ℝ)) := by
  have hs : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  have hratio : (2 * Real.exp 150 * Real.sqrt W) / W =
      (2 * Real.exp 150) / Real.sqrt W := by
    apply (div_eq_div_iff hW.ne' hs.ne').mpr
    rw [mul_assoc, ← pow_two, Real.sq_sqrt hW.le]
  have hspec := quantitative_spectral_term (2 * Real.exp 150) W J (by positivity) hW hchoice
  have hmain : (6 * B * (l : ℝ) ^ 2 / L) *
      ((Real.exp 1 * (2 * (Real.exp (4 * J) *
        (2 * Real.exp 150 * Real.sqrt W) ^ J))) / W ^ J) ≤
      1212 * Real.exp 1 * (l : ℝ) ^ 2 * Real.exp (-(J : ℝ)) := by
    calc
      _ ≤ (6 * (101 * L / Real.exp (-(J : ℝ))) * (l : ℝ) ^ 2 / L) *
          ((Real.exp 1 * (2 * (Real.exp (4 * J) *
            (2 * Real.exp 150 * Real.sqrt W) ^ J))) / W ^ J) := by
        gcongr
      _ = (1212 * Real.exp 1 * (l : ℝ) ^ 2) *
          (Real.exp (5 * J) * ((2 * Real.exp 150) / Real.sqrt W) ^ J) := by
        have he : Real.exp (5 * (J : ℝ)) =
            Real.exp (4 * J) * Real.exp (J : ℝ) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hr : (Real.exp 1 * (2 * (Real.exp (4 * J) *
            (2 * Real.exp 150 * Real.sqrt W) ^ J))) / W ^ J =
            2 * Real.exp 1 * Real.exp (4 * J) *
              ((2 * Real.exp 150) / Real.sqrt W) ^ J := by
          calc
            _ = (2 * Real.exp 1 * Real.exp (4 * J)) *
                ((2 * Real.exp 150 * Real.sqrt W) ^ J / W ^ J) := by ring
            _ = _ := by rw [← div_pow, hratio]
        rw [hr, he, Real.exp_neg]
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hspec (by positivity)
  have herror : 6 * B * Real.exp (-L) ≤ 606 * Real.exp (-(J : ℝ)) := by
    calc
      _ ≤ 6 * (101 * L / Real.exp (-(J : ℝ))) * Real.exp (-L) := by gcongr
      _ = 606 * (L / Real.exp (-(J : ℝ)) * Real.exp (-L)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left herr (by norm_num)
  nlinarith


theorem ModFiveThetaInput.eventually_canonical_retained_weighted_saving
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ (A : ℕ) (W : ℝ), 1000 ≤ A ∧ ∃ hW : 10 ≤ W,
      ∀ (h l : ℕ) (_hh : 0 < h) (_hl : 0 < l) (E : Finset ℕ)
        (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
        (_hEl : ∀ p, p.Prime → p ∣ l → p ∈ E),
      ∀ᶠ L : ℝ in atTop, ∀ hL : 1 ≤ L,
      let J := primeSupplyCount W L
      let η := Real.exp (-(J : ℝ))
      let bins := paddingBinIndices L η
      ∀ eligible : ℤ → ℕ → ℕ → Prop,
        (∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q) →
      ∀ (b : ℕ) (N : ℤ → ℕ) (v : ℤ → ℂ),
        (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
      (∀ j ∈ bins, ‖v j‖ ≤ 1) →
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      ‖∑ j ∈ bins, v j * canonicalRetainedPrefix h l b E W L (eligible j) hL
        (by linarith) hE (N j)‖ /
          totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η ≤
        (1212 * Real.exp 1 * (l : ℝ) ^ 2 + 606) * Real.exp (-(J : ℝ)) := by
  obtain ⟨A, hA, hb⟩ := hprime.eventually_canonical_weighted_bin_sum_uniform hBr
  obtain ⟨W, hW, hchoice⟩ := exists_fixed_spectral_parameter (2 * Real.exp 150) (by positivity)
  refine ⟨A, W, hA, hW, ?_⟩
  intro h l hh hl E hE hEl
  have hWone : 1 ≤ W := by linarith
  filter_upwards [hb h l hh hl E hE hEl W hWone, eventually_bin_error_saving W hWone,
    eventually_ge_atTop (1 : ℝ)] with L hb herr hL
  intro hL'
  dsimp only
  intro eligible he b N v hN hv
  let J := primeSupplyCount W L
  let η := Real.exp (-(J : ℝ))
  have hη : 0 < η := Real.exp_pos _
  have hηone : η ≤ 1 := Real.exp_le_one_iff.mpr (by
    dsimp only [J]
    exact neg_nonpos.mpr (Nat.cast_nonneg _))
  have hbound := hb hL' η hη hηone (paddingBinIndices L η) eligible he b N v hN hv
  apply hbound.trans
  exact retained_spectral_scale L W J l (paddingBinIndices L η).card (by linarith)
    (by linarith) (Nat.cast_nonneg _) (paddingBinIndices_card_linear L η hL hη hηone)
    hchoice herr

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedNumericalPrefix
namespace OAI

/-! Reindex the retained prefix by the original numerical divisors,
with no tuple-representation multiplicity. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma retainedPrimeEdge_eq_numerical {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    (e : ((j : Fin J) → P j) × Q) (n m : ℤ) :
    retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n m =
      retainedNumericalEdge P Q Qp u eligible L K W extra h gate keep
        (∏ j, (e.1 j).val) e.2.val n m := rfl

lemma retained_tuple_sum_eq_numerical {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (n : ℤ) :
    (∑ e : ((j : Fin J) → P j) × Q,
      retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n
        (n + (h * e.2.val * ∏ j, (e.1 j).val : ℕ))) =
      ∑ d ∈ primeTupleDivisors P, ∑ q ∈ Q,
        retainedNumericalEdge P Q Qp u eligible L K W extra h gate keep d q n
          (n + (h * q * d : ℕ)) := by
  rw [Fintype.sum_prod_type, primeTupleDivisors, sum_image]
  · apply sum_congr rfl
    intro d _
    simp only [retainedPrimeEdge_eq_numerical]
    exact sum_coe_sort Q (fun q => retainedNumericalEdge P Q Qp u eligible
      L K W extra h gate keep (∏ j, (d j).val) q n
      (n + (h * q * ∏ j, (d j).val : ℕ)))
  · intro d _ e _ hde
    exact primeTuple_injective hprime hdisjoint hde

theorem retainedPrimePrefix_eq_numerical {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (N : ℕ) :
    retainedPrimePrefix P Q Qp u eligible L K W extra h gate keep N =
      positivePrefix (fun n => ∑ d ∈ primeTupleDivisors P, ∑ q ∈ Q,
        retainedNumericalEdge P Q Qp u eligible L K W extra h gate keep d q n
          ((n : ℤ) + (h * q * d : ℕ))) N / (N : ℂ) := by
  unfold retainedPrimePrefix
  simp_rw [retained_tuple_sum_eq_numerical P hprime hdisjoint]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedDeletionBridge
namespace OAI

/-! The actual complex correlation lost at either endpoint is dominated
by the positive deletion costs already estimated on integer intervals. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma integerEdgeKeep_of_larger_eligibility (R : Finset ℕ) (u : ℕ → ℝ)
    (small large : ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop)
    (hu : ∀ q ∈ R, 0 ≤ u q) (hsub : ∀ q ∈ R, small q → large q) (n : ℤ)
    (hk : integerEdgeKeep R u large g L K extra n) :
    integerEdgeKeep R u small g L K extra n := by
  refine ⟨?_, hk.2⟩
  apply le_trans _ hk.1
  unfold paddingDensity
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply sum_le_sum
  intro q hq
  by_cases hs : small q ∧ (q : ℤ) ∣ n
  · have hl : large q ∧ (q : ℤ) ∣ n := ⟨hsub q hq hs.1, hs.2⟩
    rw [if_pos hs, if_pos hl]
  · simp only [hs, ite_false]
    split_ifs <;> first | exact hu q hq | exact le_rfl

lemma liouville_edge_norm_le_positive (d q : ℕ) (n m : ℤ) :
    ‖(actualPaddingCoefficient q * centeredTuple d.primeFactors n : ℝ) *
      integerLiouville n * integerLiouville m‖ ≤
      actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n := by
  calc
    _ = |actualPaddingCoefficient q * centeredTuple d.primeFactors n| *
        ‖integerLiouville n‖ * ‖integerLiouville m‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |actualPaddingCoefficient q * centeredTuple d.primeFactors n| * 1 * 1 := by
      gcongr <;> exact integerLiouville_norm_le_one _
    _ ≤ _ := by
      rw [mul_one, mul_one, abs_mul, abs_of_nonneg (actualPaddingCoefficient_nonneg q)]
      exact mul_le_mul_of_nonneg_left (abs_centeredTuple_le_positivePrimeWeight _ _)
        (actualPaddingCoefficient_nonneg q)


lemma norm_sub_optional_le_two_costs (z retained : ℂ) (B : ℝ) (gn gm : Prop)
    (hB : ‖z‖ ≤ B) (hret : retained = z ∨ retained = 0)
    (hgood : gn → gm → retained = z) :
    ‖z - retained‖ ≤ (if gn then 0 else B) + (if gm then 0 else B) := by
  have hB0 := (norm_nonneg z).trans hB
  by_cases hn : gn <;> by_cases hm : gm
  · simp only [hn, hm, ite_true, hgood hn hm, sub_self, norm_zero, add_zero, le_refl]
  all_goals
    rcases hret with rfl | rfl <;> simp only [hn, hm, ite_true, ite_false,
      sub_self, sub_zero, norm_zero, zero_add, add_zero] <;> linarith

lemma retainedNumericalEdge_optional {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (eligible : ℕ → ℕ → Prop) (L K W : ℝ) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (bad : ℤ → Prop) (d q : ℕ) (n m : ℤ) :
    retainedNumericalEdge P R Q actualPaddingCoefficient eligible L K W
      (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad z) d q n m =
        uncutNumericalEdge R eligible h gate d q n m ∨
    retainedNumericalEdge P R Q actualPaddingCoefficient eligible L K W
      (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad z) d q n m = 0 := by
  unfold retainedNumericalEdge retainedLiouvilleEdge uncutNumericalEdge
  split_ifs <;> simp_all

lemma retainedNumericalEdge_eq_uncut_of_good {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ)
    (eligible : ℕ → ℕ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (bad : ℤ → Prop) (j : ℤ) (d q : ℕ) (n m : ℤ)
    (hsub : ∀ r ∈ R, eligible d r → actualPaddingBin η (c d) j r)
    (hn : integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
        (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n ∧
      (actualPaddingDegree (primeTuplePool P) n : ℝ) ≤ 6 * W * J ∧ ¬bad n)
    (hm : integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
        (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) m ∧
      (actualPaddingDegree (primeTuplePool P) m : ℝ) ≤ 6 * W * J ∧ ¬bad m) :
    retainedNumericalEdge P R Q actualPaddingCoefficient eligible L K W
      (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad z) d q n m =
        uncutNumericalEdge R eligible h gate d q n m := by
  have hkn := integerEdgeKeep_of_larger_eligibility R actualPaddingCoefficient
    (eligible d) (actualPaddingBin η (c d) j) (actualPaddingVertex Q) L K
    (actualPaddingDegreeCut Q L) (fun r _ => actualPaddingCoefficient_nonneg r) hsub n hn.1
  have hkm := integerEdgeKeep_of_larger_eligibility R actualPaddingCoefficient
    (eligible d) (actualPaddingBin η (c d) j) (actualPaddingVertex Q) L K
    (actualPaddingDegreeCut Q L) (fun r _ => actualPaddingCoefficient_nonneg r) hsub m hm.1
  have hdn : (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J := hn.2.1
  have hdm : (actualPaddingDegree (univ.biUnion P) m : ℝ) ≤ 6 * W * J := hm.2.1
  by_cases hg : gate d n m
  · simp only [retainedNumericalEdge, retainedLiouvilleEdge, uncutNumericalEdge,
      hn.2.2, hm.2.2, hkn, hkm, hdn, hdm, hn.1.2, hm.1.2, hg,
      and_true, true_and, not_false_eq_true, ite_true]
    congr 1
    apply propext
    tauto
  · simp only [retainedNumericalEdge, uncutNumericalEdge, hg, false_and, ite_false]

lemma positiveDeletionAtom_eq_good_cost {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ)
    (eligible : ℤ → ℕ → ℕ → Prop) (bad : ℤ → ℤ → Prop)
    (j : ℤ) (d q : ℕ) (n : ℤ) (he : eligible j d q) (hq : (q : ℤ) ∣ n)
    (hd : d.primeFactors.card = J) :
    positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q n =
      if integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
          (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n ∧
        (actualPaddingDegree (primeTuplePool P) n : ℝ) ≤ 6 * W * J ∧ ¬bad j n
      then 0 else actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n := by
  have hf : (¬integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
      (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n ∨
      6 * W * J < (actualPaddingDegree (primeTuplePool P) n : ℝ) ∨ bad j n) ↔
      ¬(integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
        (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n ∧
        (actualPaddingDegree (primeTuplePool P) n : ℝ) ≤ 6 * W * J ∧ ¬bad j n) := by
    simp only [not_and_or, not_le, not_not]
  simp only [positiveDeletionAtom, he, hq, hd, ite_true, true_and, hf]
  split_ifs <;> simp_all

lemma positiveDeletionAtom_nonneg (P Q R : Finset ℕ) (η : ℝ) (c : ℕ → ℝ)
    (L K W : ℝ) (eligible : ℤ → ℕ → ℕ → Prop) (bad : ℤ → ℤ → Prop)
    (j : ℤ) (d q : ℕ) (n : ℤ) :
    0 ≤ positiveDeletionAtom P Q R η c L K W eligible bad j d q n := by
  unfold positiveDeletionAtom
  split_ifs <;> first
    | exact le_rfl
    | exact mul_nonneg (mul_nonneg (actualPaddingCoefficient_nonneg q)
        (positivePrimeWeight_nonneg _ _)) (by norm_num)

/-- On a numerical edge, each discarded correlation is paid by one of
its two actual endpoint costs. No averaging or periodicity premise is added. -/
theorem uncut_sub_retained_edge_le {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ)
    (eligible : ℤ → ℕ → ℕ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (bad : ℤ → ℤ → Prop) (j : ℤ) (d q : ℕ) (n : ℤ)
    (hsub : ∀ r ∈ R, eligible j d r → actualPaddingBin η (c d) j r)
    (hd : d.primeFactors.card = J) :
    ‖uncutNumericalEdge R (eligible j) h gate d q n (n + (h * q * d : ℕ)) -
      retainedNumericalEdge P R Q actualPaddingCoefficient (eligible j) L K W
        (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad j z)
        d q n (n + (h * q * d : ℕ))‖ ≤
      positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q n +
      positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q
        (n + (h * q * d : ℕ)) := by
  let m := n + (h * q * d : ℕ)
  let z := uncutNumericalEdge R (eligible j) h gate d q n m
  let r := retainedNumericalEdge P R Q actualPaddingCoefficient (eligible j) L K W
    (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad j z) d q n m
  have hop : r = z ∨ r = 0 := retainedNumericalEdge_optional P R Q (eligible j)
    L K W h gate (bad j) d q n m
  by_cases ha : gate d n m ∧ q ∈ R ∧ eligible j d q ∧ (q : ℤ) ∣ n
  · have hmdiv : (q : ℤ) ∣ m := by
      dsimp [m]
      apply dvd_add ha.2.2.2
      exact_mod_cast (show q ∣ h * q * d from dvd_mul_of_dvd_left (dvd_mul_left q h) d)
    have hw : positivePrimeWeight d.primeFactors m = positivePrimeWeight d.primeFactors n := by
      have he : (h * q * d : ℕ) = (d : ℤ) * ((h * q : ℕ) : ℤ) := by push_cast; ring
      change positivePrimeWeight d.primeFactors (n + (h * q * d : ℕ)) = _
      rw [he, positivePrimeWeight_add_multiple]
    let good := fun t : ℤ =>
      integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
        (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) t ∧
      (actualPaddingDegree (primeTuplePool P) t : ℝ) ≤ 6 * W * J ∧ ¬bad j t
    have hz : ‖z‖ ≤ actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n := by
      dsimp [z, uncutNumericalEdge]
      rw [if_pos ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, rfl⟩]
      exact liouville_edge_norm_le_positive d q n m
    have hg : good n → good m → r = z :=
      fun hn hm => retainedNumericalEdge_eq_uncut_of_good P R Q η c L K W
        (eligible j) h gate (bad j) j d q n m hsub hn hm
    have hb := norm_sub_optional_le_two_costs z r
      (actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n)
      (good n) (good m) hz hop hg
    have hcn := positiveDeletionAtom_eq_good_cost P R Q η c L K W eligible bad j d q n
      ha.2.2.1 ha.2.2.2 hd
    have hcm := positiveDeletionAtom_eq_good_cost P R Q η c L K W eligible bad j d q m
      ha.2.2.1 hmdiv hd
    change ‖z - r‖ ≤ _
    rw [hcn, hcm, hw]
    by_cases hn : good n <;> by_cases hm : good m
    all_goals
      dsimp only [good] at hn hm hb
      simpa only [hn, hm, ite_true, ite_false] using hb
  · have hz : z = 0 := by
      dsimp [z, uncutNumericalEdge]
      exact if_neg (fun hcond => ha ⟨hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2.1⟩)
    have hr : r = 0 := hop.elim (fun he => he.trans hz) id
    change ‖z - r‖ ≤ _
    rw [hz, hr, sub_self, norm_zero]
    exact add_nonneg
      (positiveDeletionAtom_nonneg (primeTuplePool P) Q R η c L K W eligible bad j d q n)
      (positiveDeletionAtom_nonneg (primeTuplePool P) Q R η c L K W eligible bad j d q m)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrefixDeletionBridge
namespace OAI

/-! Sum the pointwise endpoint loss over the same positive prefixes as
the spectral test, retaining every tuple and padding weight. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma normalized_prefix_difference_le (F G : ℕ → ℂ) (cost : ℕ → ℝ) (N : ℕ)
    (hb : ∀ n, ‖F n - G n‖ ≤ cost n) :
    ‖positivePrefix F N / (N : ℂ) - positivePrefix G N / (N : ℂ)‖ ≤
      uniformAverage (fun x : Fin N => cost (x.val + 1)) := by
  rw [← sub_div]
  have he : positivePrefix F N - positivePrefix G N = positivePrefix (fun n => F n - G n) N := by
    simp only [positivePrefix, sum_sub_distrib]
  rw [he, norm_div, Complex.norm_natCast]
  unfold positivePrefix uniformAverage
  rw [Fintype.card_fin, Fin.sum_univ_eq_sum_range (fun x => cost (x + 1)) N]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (norm_sum_le _ _).trans (sum_le_sum (fun n _ => hb (n + 1)))


theorem uncut_sub_retained_prefix_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i k, k ≠ i → Disjoint (P i) (P k))
    (R Q : Finset ℕ) (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ)
    (eligible : ℤ → ℕ → ℕ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (bad : ℤ → ℤ → Prop) (j : ℤ) (N : ℕ)
    (hsub : ∀ d ∈ primeTupleDivisors P, ∀ q ∈ R,
      eligible j d q → actualPaddingBin η (c d) j q) :
    ‖uncutPrimePrefix P R (eligible j) h gate N -
      retainedPrimePrefix P R Q actualPaddingCoefficient (eligible j) L K W
        (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad j z) N‖ ≤
      (∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        uniformAverage (fun x : Fin N => positiveDeletionAtom (primeTuplePool P) Q R
          η c L K W eligible bad j d q ((x.val + 1 : ℕ) : ℤ))) +
      (∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        uniformAverage (fun x : Fin N => positiveDeletionAtom (primeTuplePool P) Q R
          η c L K W eligible bad j d q (((x.val + 1 : ℕ) : ℤ) + (h * q * d : ℕ)))) := by
  rw [retainedPrimePrefix_eq_numerical P hprime hdisjoint]
  unfold uncutPrimePrefix
  have hb (n : ℕ) :
      ‖(∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        uncutNumericalEdge R (eligible j) h gate d q n ((n : ℤ) + (h * q * d : ℕ))) -
        (∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        retainedNumericalEdge P R Q actualPaddingCoefficient (eligible j) L K W
          (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad j z)
          d q n ((n : ℤ) + (h * q * d : ℕ)))‖ ≤
      ∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        (positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q n +
        positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q
          ((n : ℤ) + (h * q * d : ℕ))) := by
    simp only [← sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro d hd
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro q _
    exact uncut_sub_retained_edge_le P R Q η c L K W eligible h gate bad j d q n
      (hsub d hd) (primeTupleDivisors_arithmetic P hprime hdisjoint hd).2.1
  have hp := normalized_prefix_difference_le _ _ _ N hb
  apply hp.trans_eq
  have hadd (f g : Fin N → ℝ) : uniformAverage (fun x => f x + g x) =
      uniformAverage f + uniformAverage g := by
    simp only [uniformAverage, sum_add_distrib, add_div]
  simp only [uniformAverage_finset_sum, hadd, sum_add_distrib]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedEligibility
namespace OAI

/-! On the actual tuple and padding pools, canonical pair membership
agrees with the original bin eligibility, including inside the density cut. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma canonicalTraceFamily_pair_on_pool (h : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (d q : ℕ)
    (hd : d ∈ primeTupleDivisors
      (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)))
    (hq : q ∈ boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊) :
    (d, q) ∈ (canonicalTraceFamily h E W L eligible hL hW hE).pairs ↔ eligible d q := by
  rw [canonicalTraceFamily, actualProhibitedPrimeFamily_pairs]
  simp only [hd, (mem_filter.mp hq).1, (mem_filter.mp hq).2, true_and]

lemma integerEdgeKeep_congr_eligible (R : Finset ℕ) (u : ℕ → ℝ)
    (e f : ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop)
    (hef : ∀ q ∈ R, e q ↔ f q) (n : ℤ) :
    integerEdgeKeep R u e g L K extra n ↔ integerEdgeKeep R u f g L K extra n := by
  have he : paddingDensity R u e g n = paddingDensity R u f g n := by
    unfold paddingDensity
    congr 1
    apply sum_congr rfl
    intro q hq
    simp only [hef q hq]
  simp only [integerEdgeKeep, he]

lemma retainedNumericalEdge_congr_eligible {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (u : ℕ → ℝ) (e f : ℕ → ℕ → Prop) (L K W : ℝ)
    (extra : ℕ → ℤ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (keep : ℤ → Prop) (d q : ℕ) (n m : ℤ) (hq : q ∈ R)
    (hef : ∀ r ∈ R, e d r ↔ f d r) :
    retainedNumericalEdge P R Q u e L K W extra h gate keep d q n m =
      retainedNumericalEdge P R Q u f L K W extra h gate keep d q n m := by
  have hk := integerEdgeKeep_congr_eligible R u (e d) (f d)
    (actualPaddingVertex Q) L K (extra d) hef
  simp only [retainedNumericalEdge, retainedLiouvilleEdge, hef q hq, hk]
  split_ifs <;> rfl

lemma retainedPrimePrefix_congr_eligible {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i k, k ≠ i → Disjoint (P i) (P k))
    (R Q : Finset ℕ) (u : ℕ → ℝ) (e f : ℕ → ℕ → Prop) (L K W : ℝ)
    (extra : ℕ → ℤ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (keep : ℤ → Prop) (N : ℕ)
    (hef : ∀ d ∈ primeTupleDivisors P, ∀ q ∈ R, e d q ↔ f d q) :
    retainedPrimePrefix P R Q u e L K W extra h gate keep N =
      retainedPrimePrefix P R Q u f L K W extra h gate keep N := by
  rw [retainedPrimePrefix_eq_numerical P hprime hdisjoint,
    retainedPrimePrefix_eq_numerical P hprime hdisjoint]
  congr 2
  funext n
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro q hq
  exact retainedNumericalEdge_congr_eligible P R Q u e f L K W extra h gate keep
    d q n ((n : ℤ) + (h * q * d : ℕ)) hq (hef d hd)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalCorrelationDeletion
namespace OAI

/-! The literal uncut bin correlation differs from the spectral test
by the two canonical endpoint deletion costs. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma canonical_uncut_sub_retained_prefix (h l b : ℕ) (E : Finset ℕ)
    (W L η : ℝ) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (c : ℕ → ℝ) (eligible : ℤ → ℕ → ℕ → Prop) (j : ℤ) (N : ℕ)
    (hbin : ∀ d q, eligible j d q → actualPaddingBin η (c d) j q) :
    let J := primeSupplyCount W L
    let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
    let Q := paddingPrimeSupply E L
    let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
    let bad := fun k n => ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
      (fun d q => (d, q) ∈ (canonicalTraceFamily h E W L (eligible k) hL hW hE).pairs) n
    ‖canonicalUncutPrefix h l b E W L (eligible j) N -
      canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE N‖ ≤
      (∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        uniformAverage (fun x : Fin N => positiveDeletionAtom (primeTuplePool P) Q R
          η c L (Real.exp (4 * J)) W eligible bad j d q ((x.val + 1 : ℕ) : ℤ))) +
      (∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        uniformAverage (fun x : Fin N => positiveDeletionAtom (primeTuplePool P) Q R
          η c L (Real.exp (4 * J)) W eligible bad j d q
            (((x.val + 1 : ℕ) : ℤ) + (h * q * d : ℕ)))) := by
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
  let bad := fun k n => ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
    (fun d q => (d, q) ∈ (canonicalTraceFamily h E W L (eligible k) hL hW hE).pairs) n
  let active := fun d q => (d, q) ∈ (canonicalTraceFamily h E W L (eligible j) hL hW hE).pairs
  have hp : ∀ i, ∀ p ∈ P i, p.Prime := centeredPrimeBands_prime _ _ _ _
  have hd : ∀ i k, k ≠ i → Disjoint (P i) (P k) := centeredPrimeBands_disjoint _ _ _ _
    (Real.rpow_nonneg (zero_le_one.trans hL) _) (zero_le_one.trans hW)
  have hcongr := retainedPrimePrefix_congr_eligible P hp hd R Q actualPaddingCoefficient
    active (eligible j) L (Real.exp (4 * J)) W (fun _ => actualPaddingDegreeCut Q L)
    h (progressionEdgeGate h l b) (fun z => ¬bad j z) N
    (fun d hd q hq => canonicalTraceFamily_pair_on_pool h E W L (eligible j) hL hW hE d q hd hq)
  change ‖uncutPrimePrefix P R (eligible j) h (progressionEdgeGate h l b) N -
    retainedPrimePrefix P R Q actualPaddingCoefficient active L (Real.exp (4 * J)) W
      (fun _ => actualPaddingDegreeCut Q L) h (progressionEdgeGate h l b)
      (fun z => ¬bad j z) N‖ ≤ _
  rw [hcongr]
  exact uncut_sub_retained_prefix_le P hp hd R Q η c L (Real.exp (4 * J)) W
    eligible h (progressionEdgeGate h l b) bad j N (fun d _ q _ => hbin d q)

lemma prefix_start_one_add (n : ℕ) : (1 : ℤ) + n = ((n + 1 : ℕ) : ℤ) := by
  push_cast
  ring

lemma canonical_weighted_correlation_deletion (h l b : ℕ) (E : Finset ℕ)
    (W L η : ℝ) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (bins : Finset ℤ)
    (c : ℕ → ℝ) (eligible : ℤ → ℕ → ℕ → Prop) (N : ℤ → ℕ) (v : ℤ → ℂ)
    (hbin : ∀ j ∈ bins, ∀ d q, eligible j d q → actualPaddingBin η (c d) j q)
    (hv : ∀ j ∈ bins, ‖v j‖ ≤ 1) :
    ‖(∑ j ∈ bins, v j * canonicalUncutPrefix h l b E W L (eligible j) (N j)) -
      (∑ j ∈ bins, v j * canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE (N j))‖ ≤
      canonicalShiftedSourceDeletion h E W L η (Real.exp (4 * primeSupplyCount W L))
        hL hW hE bins c eligible (fun _ _ _ => 0) (fun _ => 1) N +
      canonicalShiftedSourceDeletion h E W L η (Real.exp (4 * primeSupplyCount W L))
        hL hW hE bins c eligible (fun _ d q => (h * q * d : ℕ)) (fun _ => 1) N := by
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ bins, ‖canonicalUncutPrefix h l b E W L (eligible j) (N j) -
        canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE (N j)‖ := by
      apply sum_le_sum
      intro j hj
      rw [norm_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hv j hj) (norm_nonneg _)
    _ ≤ ∑ j ∈ bins, _ := sum_le_sum (fun j hj =>
      canonical_uncut_sub_retained_prefix h l b E W L η hL hW hE c eligible j (N j) (hbin j hj))
    _ = _ := by
      simp only [canonicalShiftedSourceDeletion, Nat.cast_one, prefix_start_one_add,
        sum_add_distrib, add_zero]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FinalCorrelationBound
namespace OAI

/-! Arithmetic assembly of the centering, endpoint deletion, and retained
spectral estimates at the manuscript's final parameter choice. -/

namespace TwoPointCorrelations

lemma quantitative_deletion_small (L W C : ℝ) (J : ℕ)
    (hL : 1 ≤ L) (hW : 1 ≤ W) (hC : 0 ≤ C)
    (hJ : 60 * (J : ℝ) ≤ Real.log L)
    (hr : Real.exp (-L ^ (9 / 10 : ℝ)) ≤ Real.exp (-(J : ℝ))) :
    (2 : ℝ) ^ J * (C / Real.exp (4 * J) + L ^ (-100 : ℝ) +
      Real.exp (-2 * W * J)) + 2 * Real.exp (-L ^ (9 / 10 : ℝ)) ≤
        (C + 4) * Real.exp (-(J : ℝ)) := by
  obtain ⟨_, hk, hl, hw⟩ := quantitative_small_terms L W J hL hW hJ
  have hc := mul_le_mul_of_nonneg_left hk hC
  have he : (2 : ℝ) ^ J * (C / Real.exp (4 * J)) =
      C * ((2 : ℝ) ^ J * Real.exp (-4 * (J : ℝ))) := by
    rw [show (4 : ℝ) * J = -(-4 * (J : ℝ)) by ring, Real.exp_neg]
    simp only [div_eq_mul_inv, inv_inv]
    ring
  rw [← he] at hc
  nlinarith

lemma reciprocal_cutoff_saving (L W X : ℝ) (A : ℕ)
    (hL : 1 ≤ L) (hW : 1 ≤ W) (hA : A ≠ 0)
    (hX : Real.exp (L ^ A) ≤ X) :
    1 / X ≤ Real.exp (-(primeSupplyCount W L : ℝ)) := by
  have hXp : 0 < X := (Real.exp_pos _).trans_le hX
  have hJ := primeSupplyCount_le_log W L hW hL
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hpow : L ≤ L ^ A := le_self_pow₀ hL hA
  calc
    1 / X ≤ 1 / Real.exp (L ^ A) := one_div_le_one_div_of_le (Real.exp_pos _) hX
    _ = Real.exp (-(L ^ A)) := by rw [Real.exp_neg, one_div]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

lemma correlation_normalized_bound (raw retained F : ℂ)
    (S₀ M η Cret Cdel Ccenter Xinv : ℝ)
    (hS : 0 < S₀) (_hM : 0 ≤ M) (hη : 0 ≤ η)
    (_hretC : 0 ≤ Cret) (hdelC : 0 ≤ Cdel) (hcenterC : 0 ≤ Ccenter)
    (hmass : M / 2 ≤ S₀) (hX : Xinv ≤ η)
    (hret : ‖retained‖ / S₀ ≤ Cret * η)
    (hdel : ‖raw - retained‖ ≤ 2 * M * ((Cdel + 4) * η))
    (hcenter : ‖raw - (S₀ : ℂ) * F‖ ≤
      Ccenter * η * M + S₀ * (2 * η + Xinv)) :
    ‖F‖ ≤ (Cret + 4 * Cdel + 2 * Ccenter + 19) * η := by
  have hr := (div_le_iff₀ hS).mp hret
  have hmc : Ccenter * η * M ≤ 2 * Ccenter * η * S₀ := by
    have hx := mul_le_mul_of_nonneg_left (show M ≤ 2 * S₀ by linarith)
      (mul_nonneg hcenterC hη)
    nlinarith
  have hmd : 2 * M * ((Cdel + 4) * η) ≤
      4 * (Cdel + 4) * η * S₀ := by
    have hx := mul_le_mul_of_nonneg_left (show M ≤ 2 * S₀ by linarith)
      (show 0 ≤ 2 * ((Cdel + 4) * η) by positivity)
    nlinarith
  have ht : ‖(S₀ : ℂ) * F‖ ≤
      ‖raw - (S₀ : ℂ) * F‖ + ‖raw - retained‖ + ‖retained‖ := by
    calc
      _ = ‖raw - (raw - (S₀ : ℂ) * F)‖ := by congr 1; ring
      _ ≤ ‖raw‖ + ‖raw - (S₀ : ℂ) * F‖ := norm_sub_le _ _
      _ ≤ (‖raw - retained‖ + ‖retained‖) + ‖raw - (S₀ : ℂ) * F‖ := by
        gcongr
        calc
          ‖raw‖ = ‖(raw - retained) + retained‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      _ = _ := by ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS] at ht
  have hxe := mul_le_mul_of_nonneg_left hX hS.le
  have hf : S₀ * ‖F‖ ≤ S₀ * ((Cret + 4 * Cdel + 2 * Ccenter + 19) * η) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ hS).mp hf

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ProgressionMeanIdentity
namespace OAI

/-! Match the analytic real-cutoff mean with the manuscript's ordinary
progression sum, for every residue class. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma progressionLiouvilleMean_eq (h l b : ℕ) [NeZero l] (X : ℝ) :
    progressionLiouvilleMean h l b X =
      progressionSum liouville liouville h l b ⌊X⌋₊ / (X : ℂ) := by
  unfold progressionLiouvilleMean
  rw [positivePrefix_eq_Icc]
  congr 1
  simp only [progressionSum, sum_filter]
  apply sum_congr rfl
  intro n _
  simp only [progressionSequence, ZMod.natCast_eq_natCast_iff']
  split_ifs <;> simp only [zero_mul]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QuantitativeFixedScale
namespace OAI

/-! Assembly of the actual graph, deletion and centering estimates.
The interval exponent and prime-band width are absolute: they are chosen
before the shift, modulus, or residue class. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem quantitative_fixed_scale (hP : ModFiveThetaInput)
    (hBr : BravermanDepth22Input) (hM : PrimeReciprocalInput)
    (hMRT : MRTLiouvilleShortInput) :
    ∃ (A : ℕ) (W : ℝ), 1000 ≤ A ∧ 10 ≤ W ∧
      ∀ (h l : ℕ) [NeZero l], 0 < h →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
        ∀ X : ℝ, Real.exp (L ^ A) ≤ X → ∀ b : ℕ,
          ‖progressionLiouvilleMean h l b X‖ ≤
            C * Real.exp (-(primeSupplyCount W L : ℝ)) := by
  obtain ⟨As, W, hAs, hW, hs⟩ :=
    hP.eventually_canonical_retained_weighted_saving hBr
  obtain ⟨Ad, hAd, hd⟩ := hBr.eventually_canonical_shifted_source_deletion_uniform hP
  let A := As + Ad
  have hA : 1000 ≤ A := by dsimp only [A]; omega
  have hWone : 1 ≤ W := by linarith
  refine ⟨A, W, hA, hW, ?_⟩
  intro h l _ hh
  have hl : 0 < l := NeZero.pos l
  let E := (h * l).primeFactors
  have hE : ∀ p, p.Prime → p ∣ h → p ∈ E := by
    intro p hp hph
    exact Nat.mem_primeFactors.mpr
      ⟨hp, dvd_mul_of_dvd_left hph l, (Nat.mul_pos hh hl).ne'⟩
  have hEl : ∀ p, p.Prime → p ∣ l → p ∈ E := by
    intro p hp hpl
    exact Nat.mem_primeFactors.mpr
      ⟨hp, dvd_mul_of_dvd_right hpl h, (Nat.mul_pos hh hl).ne'⟩
  obtain ⟨Cd, hCd, hd⟩ := hd h E hE W 3 hW (by norm_num)
  obtain ⟨Cc, hCc, hc⟩ := quantitative_centering_assembly hP hM hMRT h hh l E hEl W hWone
  let Cs : ℝ := 1212 * Real.exp 1 * (l : ℝ) ^ 2 + 606
  refine ⟨Cs + 4 * Cd + 2 * Cc + 19, by dsimp only [Cs]; positivity, ?_⟩
  filter_upwards [hs h l hh hl E hE hEl, hd, hc,
    hP.eventually_canonical_retained_mass E W hWone,
    eventually_quantitative_final_windows W (by linarith),
    eventually_rare_error_saving W hWone,
    eventually_ge_atTop (101 : ℝ)] with L hs hd hc hm hw hr hlarge
  intro X hX b
  have hL : 1 ≤ L := by linarith
  let J := primeSupplyCount W L
  let η := Real.exp (-(J : ℝ))
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let S := paddingTiltNormalizer Q
  let V := ∏ i, primeHarmonicMass (P i)
  let M := S * V
  let S₀ := totalPaddingBinMass (primeTupleDivisors P) Q L η
  let bins := paddingBinIndices L η
  let eligible := numericalBinEligible L η
  let T := fun j : ℤ => X * Real.exp ((j : ℝ) * η)
  let N := fun j : ℤ => ⌊T j⌋₊
  let v := fun j : ℤ => (N j : ℂ) / (T j : ℂ)
  let raw := ∑ j ∈ bins, v j * canonicalUncutPrefix h l b E W L (eligible j) (N j)
  let retained := ∑ j ∈ bins,
    v j * canonicalRetainedPrefix h l b E W L (eligible j) hL hWone hE (N j)
  let cost := fun site => canonicalShiftedSourceDeletion h E W L η (Real.exp (4 * J))
    hL hWone hE bins (fun d => Real.log d) eligible site (fun _ => 1) N
  have hη : 0 < η := Real.exp_pos _
  have hηone : η ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg J))
  have hXpos : 0 < X := (Real.exp_pos _).trans_le hX
  have hwindow := hw.2.2.2.2 A hA X hX
  have hN (A' : ℕ) (hA' : A' ≤ A) (j : ℤ) (hj : j ∈ bins) :
      Real.exp (L ^ A' / 2) ≤ (N j : ℝ) :=
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ hL hA') (by norm_num))).trans (hwindow.2 j hj)
  have hv : ∀ j ∈ bins, ‖v j‖ ≤ 1 := by
    intro j _
    exact floor_cutoff_weight_norm_le (T j) (mul_pos hXpos (Real.exp_pos _))
  have he : ∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q := by
    intro j hj d q hdq
    exact numericalBinEligible_pair L η hη j hj d q hdq
  have hb : ∀ j ∈ bins, ∀ d q, eligible j d q →
      actualPaddingBin η (Real.log d) j q := by
    intro j _ d q hdq
    exact numericalBinEligible_bin L η j d q hdq
  have hbins : (bins.card : ℝ) ≤ Real.exp (3 * Real.log L) :=
    paddingBinIndices_card_polynomial L W hlarge hWone
  have hm' := hm hL η hη
  have hV : 1 ≤ V := (one_le_pow₀ hWone).trans hm'.1
  have hM : 0 < M := mul_pos (paddingTiltNormalizer_pos Q) (by linarith)
  have hmass : M / 2 ≤ S₀ := hm'.2
  have hS₀ : 0 < S₀ := (half_pos hM).trans_le hmass
  have hret : ‖retained‖ / S₀ ≤ Cs * η :=
    hs hL eligible he b N v (hN As (by dsimp only [A]; omega)) hv
  have hdelete : ‖raw - retained‖ ≤ cost (fun _ _ _ => 0) +
      cost (fun _ d q => (h * q * d : ℕ)) :=
    canonical_weighted_correlation_deletion h l b E W L η hL hWone hE bins
      (fun d => Real.log d) eligible N v hb hv
  have hd' (site : ℤ → ℕ → ℕ → ℤ) : cost site / M ≤ (Cd + 4) * η := by
    have hx := hd hL η (Real.exp (4 * J)) hη hηone (Real.exp_pos _) bins
      (fun d => Real.log d) eligible hbins he hb site (fun _ => 1) N
      (hN Ad (by dsimp only [A]; omega))
    exact hx.trans (quantitative_deletion_small L W Cd J hL hWone hCd.le
      (primeSupplyCount_final_budget L W hL hWone) hr)
  have hdel : ‖raw - retained‖ ≤ 2 * M * ((Cd + 4) * η) := by
    have h₁ := (div_le_iff₀ hM).mp (hd' (fun _ _ _ => 0))
    have h₂ := (div_le_iff₀ hM).mp (hd' (fun _ d q => (h * q * d : ℕ)))
    nlinarith
  have hcenter : ‖raw - (S₀ : ℂ) * progressionLiouvilleMean h l b X‖ ≤
      Cc * η * M + S₀ * (2 * η + 1 / X) := by
    have hx := hc hL X hwindow.1 η hη hw.2.2.2.1 b
    change ‖raw - (S₀ : ℂ) * progressionLiouvilleMean h l b X‖ ≤ _ at hx
    have hsmall := (quantitative_small_terms L W J hL hWone
      (primeSupplyCount_final_budget L W hL hWone)).1
    have hinv : η⁻¹ = Real.exp (J : ℝ) := by
      dsimp only [η]
      rw [Real.exp_neg, inv_inv]
    rw [← hinv] at hsmall
    have hcsmall := mul_le_mul_of_nonneg_left hsmall hCc.le
    have hcsmall' := mul_le_mul_of_nonneg_right hcsmall hM.le
    dsimp only [M] at hcsmall'
    nlinarith
  exact correlation_normalized_bound raw retained (progressionLiouvilleMean h l b X)
    S₀ M η Cs Cd Cc (1 / X) hS₀ hM.le hη.le (by dsimp only [Cs]; positivity)
    hCd.le hCc.le hmass (reciprocal_cutoff_saving L W X A hL hWone (by omega) hX)
    hret hdel hcenter

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ConditionalLiouville
namespace OAI

/-! The manuscript's quantitative main theorem, conditional only on the
named published prime, circuit, and Liouville short-sum inputs. -/

namespace TwoPointCorrelations

open _root_.Filter

theorem conditional_liouville_progression (hP : ModFiveThetaInput)
    (hBr : BravermanDepth22Input) (hM : PrimeReciprocalInput)
    (hMRT : MRTLiouvilleShortInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ h l b : ℕ, 0 < h → 0 < l →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
        ‖progressionSum liouville liouville h l b ⌊X⌋₊‖ ≤
          C * X / (Real.log X) ^ c := by
  obtain ⟨A, W, hA, hW, hb⟩ := quantitative_fixed_scale hP hBr hM hMRT
  have hAp : 0 < A := by omega
  have hWp : 0 < W := by linarith
  let c : ℝ := 1 / (1200 * W * A)
  refine ⟨c, log_saving_exponent_pos W A hWp hAp, ?_⟩
  intro h l b hh hl
  let : NeZero l := ⟨by omega⟩
  obtain ⟨C, hC, hb⟩ := hb h l hh
  refine ⟨C * Real.exp 1, by positivity, ?_⟩
  filter_upwards [(final_log_scale_tendsto A hAp).eventually hb,
    eventually_ge_atTop (Real.exp 1)] with X hb hX
  have hXone : 1 ≤ X := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hX
  have hXp : 0 < X := (Real.exp_pos _).trans_le hX
  have hm := hb X (by rw [final_log_scale_exact X A hXone (by omega)]) b
  rw [progressionLiouvilleMean_eq, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hXp] at hm
  have hs := mul_le_mul_of_nonneg_left (primeSupplyCount_log_saving X W A hX hWp hAp) hC.le
  have hm' := (div_le_iff₀ hXp).mp (hm.trans hs)
  change ‖progressionSum liouville liouville h l b ⌊X⌋₊‖ ≤ _
  convert (preTransparency := .instances) hm' using 1; ring

theorem conditional_liouvilleLogSaving_oai (hP : ModFiveThetaInput)
    (hBr : BravermanDepth22Input) (hM : PrimeReciprocalInput)
    (hMRT : MRTLiouvilleShortInput) : LiouvilleLogSaving :=
  liouvilleLogSaving_of_progression (conditional_liouville_progression hP hBr hM hMRT)

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.conditional_liouvilleLogSaving_oai := @OAI.TwoPointCorrelations.conditional_liouvilleLogSaving_oai
