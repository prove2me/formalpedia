-- Prove2me | solution 1 for OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_actual_affine_word_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:31:52.693621+00:00
-- url     : https://prove2.me/submissions/9e23c6aa-54f3-4489-ac75-d1b4c9a8d130

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_BravermanDepth22Input_eventually_affine_weighted_word_comparison

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability
namespace OAI

/-!
# Finite weighted sampling for the random-prime rank argument

The prime labels in the rank argument have a nonuniform reciprocal law.
The corresponding finite-sum probability identities account for that law.
-/

namespace TwoPointCorrelations

open _root_.Finset


namespace FiniteLaw

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]






lemma average_sum (μ : FiniteLaw α) (f : ι → α → ℝ) :
    μ.average (fun x => ∑ i, f i x) = ∑ i, μ.average (f i) := by
  simp only [average, mul_sum]
  rw [sum_comm]









lemma independent_average_product [DecidableEq ι] (μ : ι → FiniteLaw α) (f : ι → α → ℝ) :
    (independent μ).average (fun x => ∏ i, f i (x i)) = ∏ i, (μ i).average (f i) := by
  simp only [average, independent, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (μ i).weight x * f i x)).symm




end FiniteLaw

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

lemma independent_probability_all (μ : ι → FiniteLaw A) (E : ι → A → Prop) :
    (independent μ).probability (fun x => ∀ i, E i (x i)) =
      ∏ i, (μ i).probability (E i) := by
  classical
  unfold probability
  calc
    _ = (independent μ).average (fun x => ∏ i, if E i (x i) then (1 : ℝ) else 0) := by
      apply congrArg (independent μ).average
      funext x
      by_cases hx : ∀ i, E i (x i) <;> simp [Fintype.prod_boole, hx]
    _ = _ := independent_average_product μ (fun i x => if E i x then 1 else 0)





end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteLawMapping
namespace OAI

/-! Finite pushforward identities, used to identify the actual two-selection
padding experiment with its three-point difference law. -/

namespace TwoPointCorrelations.FiniteLaw

open _root_.Finset
open scoped _root_.Classical

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

lemma average_fibers (μ : FiniteLaw α) (g : α → β) (F : β → ℝ) :
    μ.average (fun x => F (g x)) = ∑ y, μ.probability (fun x => g x = y) * F y := by
  calc
    _ = μ.average (fun x => ∑ y, if g x = y then F y else 0) := by
      congr 1
      funext x
      simp
    _ = _ := by
      rw [average_sum]
      apply sum_congr rfl
      intro y _
      simp [average, probability, sum_mul, mul_ite, ite_mul]




end TwoPointCorrelations.FiniteLaw

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CommonResidueLift
namespace OAI

/-! One integer realizes all coordinates of a common residue configuration. -/

namespace TwoPointCorrelations

open _root_.Finset


/-- Prime divisibility at any offset is read from that same lifted origin. -/
lemma residue_offset_divisibility {p : ℕ} (r : ZMod p) (n offset : ℤ)
    (hn : (n : ZMod p) = r) :
    (p : ℤ) ∣ n + offset ↔ r = -(offset : ZMod p) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_add, hn, add_eq_zero_iff_eq_neg]


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IntegerEdges
namespace OAI

/-! Concrete centered integer edges and the padding-density cutoff. -/

namespace TwoPointCorrelations

open _root_.Finset


lemma centeredTuple_add (P : Finset ℕ) (n t : ℤ)
    (ht : ∀ p ∈ P, (p : ℤ) ∣ t) : centeredTuple P (n + t) = centeredTuple P n := by
  unfold centeredTuple
  apply prod_congr rfl
  intro p hp
  simp only [dvd_add_left (ht p hp)]












lemma centeredTuple_padding_periodic (P : Finset ℕ) (h d : ℕ)
    (hd : ∀ p ∈ P, p ∣ d) (q : ℕ) (n : ℤ) :
    centeredTuple P (n + (h * q * d : ℕ)) = centeredTuple P n := by
  apply centeredTuple_add
  intro p hp
  exact_mod_cast dvd_mul_of_dvd_right (hd p hp) (h * q)


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitEncoding
namespace OAI

/-!
# Truth-table encoding and substitution for residue circuits

Any decoded residue equality is a Boolean function of its block of bits.
Its explicit disjunctive normal form has depth at most two and size at most
`1 + 2^B (1+B)`. Substituting such forms into the actual circuit syntax
increases depth by at most two and multiplies size by this bound.
-/

namespace TwoPointCorrelations.AC0Circuit

open _root_.Finset


lemma substitute_eval {n m : ℕ} (σ : Fin n → Bool → AC0Circuit m)
    (F : BooleanCube m → BooleanCube n)
    (hσ : ∀ i positive x, (σ i positive).eval x = if positive then F x i else !(F x i))
    (c : AC0Circuit n) (x : BooleanCube m) : (substitute σ c).eval x = c.eval (F x) := by
  induction c with
  | literal i positive => exact hσ i positive x
  | andGate children ih => simp only [substitute, eval, ih]
  | orGate children ih => simp only [substitute, eval, ih]

lemma substitute_depth {n m d : ℕ} (σ : Fin n → Bool → AC0Circuit m)
    (hσ : ∀ i positive, (σ i positive).depth ≤ d) (c : AC0Circuit n) :
    (substitute σ c).depth ≤ c.depth + d := by
  induction c with
  | literal i positive => simpa [substitute, depth] using hσ i positive
  | andGate children ih =>
      simp only [substitute, depth]
      have hs : (Finset.univ.sup fun i => (substitute σ (children i)).depth) ≤
          (Finset.univ.sup fun i => (children i).depth) + d := by
        apply Finset.sup_le
        intro i hi
        exact (ih i).trans (Nat.add_le_add_right (Finset.le_sup (f := fun i => (children i).depth) hi) d)
      omega
  | orGate children ih =>
      simp only [substitute, depth]
      have hs : (Finset.univ.sup fun i => (substitute σ (children i)).depth) ≤
          (Finset.univ.sup fun i => (children i).depth) + d := by
        apply Finset.sup_le
        intro i hi
        exact (ih i).trans (Nat.add_le_add_right (Finset.le_sup (f := fun i => (children i).depth) hi) d)
      omega

lemma substitute_size {n m K : ℕ} (σ : Fin n → Bool → AC0Circuit m)
    (hK : 1 ≤ K) (hσ : ∀ i positive, (σ i positive).size ≤ K) (c : AC0Circuit n) :
    (substitute σ c).size ≤ K * c.size := by
  induction c with
  | literal i positive => simpa [substitute, size] using hσ i positive
  | andGate children ih =>
      simp only [substitute, size]
      calc
        1 + ∑ i, (substitute σ (children i)).size ≤ K + ∑ i, K * (children i).size :=
          Nat.add_le_add hK (Finset.sum_le_sum (fun i _ => ih i))
        _ = K * (1 + ∑ i, (children i).size) := by rw [← Finset.mul_sum]; ring
  | orGate children ih =>
      simp only [substitute, size]
      calc
        1 + ∑ i, (substitute σ (children i)).size ≤ K + ∑ i, K * (children i).size :=
          Nat.add_le_add hK (Finset.sum_le_sum (fun i _ => ih i))
        _ = K * (1 + ∑ i, (children i).size) := by rw [← Finset.mul_sum]; ring
















end TwoPointCorrelations.AC0Circuit

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeLiteralEncoding
namespace OAI

/-! Canonical residue coordinates for the prime-and-offset literals
occurring in a weighted matrix word. Repeated tests share one prime
coordinate, and may have different offsets. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma primeResidueModuli_coordinate (P : Finset ℕ) {n : ℕ}
    (literal : Fin n → P × ℤ) (i : Fin n) :
    primeResidueModuli P (primeLiteralCoordinate P literal i) = (literal i).1.val := by
  simp [primeResidueModuli, primeLiteralCoordinate]

lemma primeLiteral_integer_input (P : Finset ℕ) {n : ℕ}
    (literal : Fin n → P × ℤ) (a : ℤ) (i : Fin n) :
    residueCircuitInputs (primeResidueModuli P) (primeLiteralCoordinate P literal)
      (primeLiteralTest P literal) (fun j => (a : ZMod (primeResidueModuli P j))) i =
      decide (((literal i).1.val : ℤ) ∣ a + (literal i).2) := by
  change decide ((a : ZMod (primeResidueModuli P (primeLiteralCoordinate P literal i))) =
    -((literal i).2 : ZMod (primeResidueModuli P (primeLiteralCoordinate P literal i)))) = _
  apply Bool.decide_congr
  exact (residue_offset_divisibility
    (a : ZMod (primeResidueModuli P (primeLiteralCoordinate P literal i)))
    a (literal i).2 rfl).symm.trans (by rw [primeResidueModuli_coordinate])

lemma primeResidueModuli_prime (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (i : Fin (Fintype.card P)) : (primeResidueModuli P i).Prime :=
  hP _ ((Fintype.equivFin P).symm i).property

lemma primeResidueModuli_coprime (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Pairwise (fun i j => (primeResidueModuli P i).Coprime (primeResidueModuli P j)) := by
  intro i j hij
  apply (Nat.coprime_primes (primeResidueModuli_prime P hP i)
    (primeResidueModuli_prime P hP j)).mpr
  intro he
  apply hij
  apply (Fintype.equivFin P).symm.injective
  exact Subtype.ext he

lemma primeResidueModuli_bound (P : Finset ℕ) (B : ℝ)
    (hP : ∀ p ∈ P, (p : ℝ) ≤ B) (i : Fin (Fintype.card P)) :
    (primeResidueModuli P i : ℝ) ≤ B := hP _ ((Fintype.equivFin P).symm i).property

lemma primePool_card_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (B : ℕ) (hB : ∀ p ∈ P, p ≤ B) : P.card ≤ B := by
  let f : P → Fin B := fun p => ⟨p.val - 1, by have := (hP _ p.property).pos; have := hB _ p.property; omega⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    have he : p.val - 1 = q.val - 1 := congrArg Fin.val hpq
    have hp := (hP _ p.property).pos
    have hq := (hP _ q.property).pos
    omega
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitBooleanOps
namespace OAI

/-! Relabel, complement and conjoin the residue circuits used in a
closed-word expansion without increasing their internal depth. -/

namespace TwoPointCorrelations.AC0Circuit

open _root_.Finset


lemma negate_eval {n : ℕ} (c : AC0Circuit n) (x : BooleanCube n) :
    c.negate.eval x = true ↔ c.eval x ≠ true := by
  induction c with
  | literal i b => cases b <;> cases hx : x i <;> simp [negate, eval, hx]
  | andGate c ih => simp only [negate, eval, ne_eq, decide_eq_true_eq, ih, not_forall]
  | orGate c ih => simp only [negate, eval, ne_eq, decide_eq_true_eq, ih, not_exists]

lemma negate_depth {n : ℕ} (c : AC0Circuit n) : c.negate.depth = c.depth := by
  induction c with
  | literal i b => rfl
  | andGate c ih => simp only [negate, depth, ih]
  | orGate c ih => simp only [negate, depth, ih]

lemma negate_size {n : ℕ} (c : AC0Circuit n) : c.negate.size = c.size := by
  induction c with
  | literal i b => rfl
  | andGate c ih => simp only [negate, size, ih]
  | orGate c ih => simp only [negate, size, ih]


lemma relabel_eval {n m : ℕ} (f : Fin n → Fin m) (c : AC0Circuit n) (x : BooleanCube m) :
    (relabel f c).eval x = c.eval (fun i => x (f i)) :=
  substitute_eval _ (fun x i => x (f i)) (fun _ _ _ => rfl) c x

lemma relabel_depth {n m : ℕ} (f : Fin n → Fin m) (c : AC0Circuit n) :
    (relabel f c).depth ≤ c.depth := by
  simpa only [relabel, Nat.add_zero] using substitute_depth (fun i b => literal (f i) b)
    (d := 0) (fun _ _ => Nat.le_refl 0) c

lemma relabel_size {n m : ℕ} (f : Fin n → Fin m) (c : AC0Circuit n) :
    (relabel f c).size ≤ c.size := by
  simpa only [relabel, Nat.one_mul] using substitute_size (fun i b => literal (f i) b)
    (K := 1) (by omega) (fun _ _ => Nat.le_refl 1) c


lemma conjunction_eval {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) (x : BooleanCube n) :
    (conjunction c).eval x = true ↔ ∀ i, (c i).eval x = true := by
  simp only [conjunction, eval, decide_eq_true_eq]
  constructor
  · intro h i
    simpa only [Equiv.symm_apply_apply] using h ((Fintype.equivFin ι) i)
  · intro h i
    exact h _

lemma conjunction_depth {ι : Type*} [Fintype ι] {n d : ℕ}
    (c : ι → AC0Circuit n) (hc : ∀ i, (c i).depth ≤ d) :
    (conjunction c).depth ≤ d + 1 := by
  simp only [conjunction, depth]
  have hh : (univ.sup fun i : Fin (Fintype.card ι) =>
      (c ((Fintype.equivFin ι).symm i)).depth) ≤ d :=
    Finset.sup_le (fun i _ => hc _)
  omega

lemma conjunction_size {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) : (conjunction c).size = 1 + ∑ i, (c i).size := by
  simp only [conjunction, size]
  congr 1
  exact (Fintype.equivFin ι).symm.sum_comp (fun i => (c i).size)

end TwoPointCorrelations.AC0Circuit

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IntegerShiftGeometry
namespace OAI

/-! Numerical words attached to the forced paths in the actual trace expansion. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

variable {D V : Type*}





/-- Periodicity permits using the departure center in both orientations.
All surviving cutoffs remain literal indicator conditions. -/
lemma signedIntegerWeight_departure (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h : ℕ) (a : SignedStep) (n : ℤ)
    (hperiod : ∀ q ∈ Q, ∀ z, center (z + (h * q * a.tuple : ℕ)) = center z) :
    signedIntegerWeight Q u eligible g center L K extra h a n =
      if a.padding ∈ Q ∧ eligible a.padding ∧ (a.padding : ℤ) ∣ n ∧
        integerEdgeKeep Q u eligible g L K extra n ∧
        integerEdgeKeep Q u eligible g L K extra (n + a.displacement h) then
        L * u a.padding * center n / (g n * g (n + a.displacement h)) else 0 := by
  classical
  rcases a with ⟨b, d, q⟩
  by_cases hq : q ∈ Q
  · cases b
    · have hd : (SignedStep.mk false d q).displacement h = -(h * q * d : ℕ) := by
        simp [SignedStep.displacement, Nat.cast_mul]
      have hn : n + -(h * q * d : ℕ) + (h * q * d : ℕ) = n := by ring
      have hc : center (n + -(h * q * d : ℕ)) = center n := by
        have hh := hperiod q hq (n + -(h * q * d : ℕ))
        rw [hn] at hh
        exact hh.symm
      have hqd : (q : ℤ) ∣ n + -(h * q * d : ℕ) ↔ (q : ℤ) ∣ n := by
        apply dvd_add_left
        apply dvd_neg.mpr
        exact_mod_cast dvd_mul_of_dvd_left (dvd_mul_left q h) d
      simp only [signedIntegerWeight, Bool.false_eq_true, ↓reduceIte, hd, directedIntegerEdge,
        hq, hn, true_and, hqd, hc]
      rw [mul_comm (g (n + -(h * q * d : ℕ))) (g n)]
      congr 1
      apply propext
      tauto
    · have hd : (SignedStep.mk true d q).displacement h = (h * q * d : ℕ) := by
        simp [SignedStep.displacement, Nat.cast_mul]
      simp [signedIntegerWeight, directedIntegerEdge, hd]
  · cases b <;> simp [signedIntegerWeight, directedIntegerEdge, hq]

variable [DecidableEq D]


variable [Fintype V]


variable [Fintype D] [DecidableEq V]



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ClosedWalkNormalization
namespace OAI

/-! Exact normalization of a closed numerical word, counting repeated visits. -/

namespace TwoPointCorrelations

open scoped _root_.Classical


lemma scalarWalkProduct_mul (h : ℕ) (a b : SignedStep → ℤ → ℝ)
    (n : ℤ) (w : List SignedStep) :
    scalarWalkProduct h (fun t x => a t x * b t x) n w =
      scalarWalkProduct h a n w * scalarWalkProduct h b n w := by
  induction w generalizing n with
  | nil => simp [scalarWalkProduct]
  | cons t w ih => simp only [scalarWalkProduct, ih]; ring

lemma scalarWalkProduct_congr (h : ℕ) {a b : SignedStep → ℤ → ℝ}
    (hab : ∀ t x, a t x = b t x) (n : ℤ) (w : List SignedStep) :
    scalarWalkProduct h a n w = scalarWalkProduct h b n w := by
  have he : a = b := funext (fun t => funext (hab t))
  rw [he]

/-- Each visit contributes its denominator once at departure and once
at arrival; the only uncancelled factors lie at the two endpoints. -/
theorem scalarWalkProduct_normalize (h : ℕ) (a : SignedStep → ℤ → ℝ)
    (g : ℤ → ℝ) (hg : ∀ n, g n ≠ 0) (n : ℤ) (w : List SignedStep) :
    scalarWalkProduct h (fun t x => a t x / (g x * g (x + t.displacement h))) n w =
      scalarWalkProduct h (fun t x => a t x / (g x) ^ 2) n w *
        g n / g (n + wordDisplacement h w) := by
  induction w generalizing n with
  | nil => simp [scalarWalkProduct, hg]
  | cons t w ih =>
      rw [scalarWalkProduct, ih, scalarWalkProduct, wordDisplacement_cons]
      rw [← add_assoc]
      field_simp [hg n, hg (n + t.displacement h),
        hg (n + t.displacement h + wordDisplacement h w)]

/-- On a closed word, the exact original edge denominators become the
product of departure weights. Repeated sites remain repeated factors. -/
theorem scalarWalkProduct_closed_normalize (h : ℕ) (a : SignedStep → ℤ → ℝ)
    (g : ℤ → ℝ) (hg : ∀ n, g n ≠ 0) (n : ℤ) (w : List SignedStep)
    (hclosed : wordDisplacement h w = 0) :
    scalarWalkProduct h (fun t x => a t x / (g x * g (x + t.displacement h))) n w =
      scalarWalkProduct h (fun t x => a t x / (g x) ^ 2) n w := by
  rw [scalarWalkProduct_normalize h a g hg, hclosed, add_zero, mul_div_cancel_right₀ _ (hg n)]

/-- Keep every arithmetic, vertex, and orientation condition while moving
the exact matrix denominator to the departure site. -/
theorem signedIntegerWeight_closed_normalize (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (center : SignedStep → ℤ → ℝ) (L K : ℝ)
    (extra : SignedStep → ℤ → Prop) (h : ℕ) (n : ℤ) (w : List SignedStep)
    (hg : ∀ n, g n ≠ 0)
    (hperiod : ∀ t, ∀ q ∈ Q, ∀ z, center t (z + (h * q * t.tuple : ℕ)) = center t z)
    (hclosed : wordDisplacement h w = 0) :
    scalarWalkProduct h (fun t x =>
      signedIntegerWeight Q u (eligible t) g (center t) L K (extra t) h t x) n w =
      scalarWalkProduct h (fun t x =>
        if t.padding ∈ Q ∧ eligible t t.padding ∧ (t.padding : ℤ) ∣ x ∧
          integerEdgeKeep Q u (eligible t) g L K (extra t) x ∧
          integerEdgeKeep Q u (eligible t) g L K (extra t) (x + t.displacement h)
        then L * u t.padding * center t x / (g x) ^ 2 else 0) n w := by
  let a : SignedStep → ℤ → ℝ := fun t x =>
    if t.padding ∈ Q ∧ eligible t t.padding ∧ (t.padding : ℤ) ∣ x ∧
      integerEdgeKeep Q u (eligible t) g L K (extra t) x ∧
      integerEdgeKeep Q u (eligible t) g L K (extra t) (x + t.displacement h)
    then L * u t.padding * center t x else 0
  calc
    _ = scalarWalkProduct h (fun t x => a t x / (g x * g (x + t.displacement h))) n w := by
      apply scalarWalkProduct_congr
      intro t x
      rw [signedIntegerWeight_departure Q u (eligible t) g (center t) L K (extra t) h t x
        (hperiod t)]
      dsimp only [a]
      split_ifs <;> simp
    _ = scalarWalkProduct h (fun t x => a t x / (g x) ^ 2) n w :=
      scalarWalkProduct_closed_normalize h a g hg n w hclosed
    _ = _ := by
      apply scalarWalkProduct_congr
      intro t x
      dsimp only [a]
      split_ifs <;> simp

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingDivisorEncoding
namespace OAI

/-! Squarefree padding divisors encode prime selections without multiplicity.
This identifies the bin law with the paper's numerical divisor sum. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical







lemma padding_supported_iff_primeFactors_subset (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (a b : Q → Bool) :
    PaddingSelectionSupported Q a b ↔
      (paddingSelectedDivisor Q b).primeFactors ⊆ paddingAvailablePrimes Q a := by
  rw [paddingSelectedDivisor_primeFactors Q hQ b]
  constructor
  · intro h p hp
    have hpQ := paddingAvailablePrimes_subset Q b hp
    exact (mem_paddingAvailablePrimes Q a ⟨p, hpQ⟩).mpr
      (h ⟨p, hpQ⟩ ((mem_paddingAvailablePrimes Q b ⟨p, hpQ⟩).mp hp))
  · intro h p hp
    exact (mem_paddingAvailablePrimes Q a p).mp
      (h ((mem_paddingAvailablePrimes Q b p).mpr hp))









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

lemma paddingSelectedDivisor_dvd_iff (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (b : Q → Bool) (n : ℤ) :
    (paddingSelectedDivisor Q b : ℤ) ∣ n ↔
      ∀ p : Q, b p = true → (p.val : ℤ) ∣ n := by
  rw [paddingSelectedDivisor, Nat.cast_prod]
  constructor
  · intro h p hp
    exact (dvd_prod_of_mem (fun q : Q => (q.val : ℤ))
      (mem_filter.mpr ⟨mem_univ p, hp⟩)).trans h
  · intro h
    apply prod_dvd_of_coprime
    · intro p _ q _ hpq
      apply Nat.Coprime.cast
      apply (Nat.coprime_primes (hQ p p.property) (hQ q q.property)).mpr
      exact fun he => hpq (Subtype.ext he)
    · intro p hp
      exact h p (mem_filter.mp hp).2

lemma padding_literal_support_iff_dvd (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (n : ℤ) (q : ℕ) (hq : q ∈ retainedPrimeDivisors Q) :
    q.primeFactors ⊆ paddingAvailablePrimes Q (fun p => decide ((p.val : ℤ) ∣ n)) ↔
      (q : ℤ) ∣ n := by
  obtain ⟨b, rfl⟩ := exists_paddingSelection Q q hq
  rw [← padding_supported_iff_primeFactors_subset Q hQ,
    paddingSelectedDivisor_dvd_iff Q hQ b n]
  simp only [PaddingSelectionSupported, decide_eq_true_eq]


lemma paddingAvailablePrimes_integer (Q : Finset ℕ) (n : ℤ) :
    paddingAvailablePrimes Q (fun p => decide ((p.val : ℤ) ∣ n)) =
      Q.filter (fun (p : ℕ) => (p : ℤ) ∣ n) := by
  ext p
  constructor
  · intro hp
    have hpQ := paddingAvailablePrimes_subset Q _ hp
    exact mem_filter.mpr ⟨hpQ, by
      simpa using (mem_paddingAvailablePrimes Q _ ⟨p, hpQ⟩).mp hp⟩
  · intro hp
    exact (mem_paddingAvailablePrimes Q _ ⟨p, (mem_filter.mp hp).1⟩).mpr
      (by simpa using (mem_filter.mp hp).2)




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

lemma wordDisplacement_take (h : ℕ) (w : List SignedStep) (n : ℕ) :
    wordDisplacement h (w.take n) = ∑ i ∈ range n, wordStepDisplacement h w i := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
      cases w with
      | nil => simp
      | cons a w =>
          rw [List.take_succ_cons, wordDisplacement_cons, Finset.sum_range_succ']
          simp only [wordStepDisplacement_cons_zero, wordStepDisplacement_cons_succ, ih]
          ring











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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LitBlockGeometry
namespace OAI

/-! Perfect blocks use only the lit divisibilities at their actual positions. -/

namespace TwoPointCorrelations

open _root_.Finset

theorem positiveWord_iff_departures (h : ℕ) (x : ℤ) (w : List SignedStep) :
    PositiveWord h x w ↔ ∀ i : Fin w.length,
      (w.get i).divisor ∣ x + wordDisplacement h (w.take i.val) := by
  induction w generalizing x with
  | nil => simp
  | cons a w ih =>
      rw [positiveWord_cons, ih]
      constructor
      · rintro ⟨ha, hw⟩ i
        rcases i with ⟨i, hi⟩
        cases i with
        | zero => simpa using ha
        | succ i =>
            simpa only [List.get_eq_getElem, List.getElem_cons_succ, List.take_succ_cons,
              wordDisplacement_cons, add_assoc] using hw ⟨i, by simpa using hi⟩
      · intro hw
        refine ⟨?_, ?_⟩
        · simpa using hw ⟨0, by simp⟩
        · intro i
          simpa only [List.get_eq_getElem, List.getElem_cons_succ, List.take_succ_cons,
            wordDisplacement_cons, add_assoc] using hw ⟨i.val + 1, by simp⟩



namespace ColumnWordPattern

variable {α : Type*} [Fintype α] [DecidableEq α]


end ColumnWordPattern

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedCircuit
namespace OAI

/-! The actual deleted event is a finite depth-two DNF of prime tests. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace AC0Circuit


lemma finiteDNF_eval {W : Type*} [Fintype W] (T : W → Type*) [∀ w, Fintype (T w)]
    {n : ℕ} (input : ∀ w, T w → Fin n) (x : BooleanCube n) :
    (finiteDNF T input).eval x = true ↔ ∃ w, ∀ t, x (input w t) = true := by
  simp only [finiteDNF, eval, ite_true, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨(Fintype.equivFin W).symm j, ?_⟩
    intro t
    simpa only [Equiv.symm_apply_apply] using hj ((Fintype.equivFin _ ) t)
  · rintro ⟨w, hw⟩
    obtain ⟨j, rfl⟩ := (Fintype.equivFin W).symm.surjective w
    exact ⟨j, fun k => hw ((Fintype.equivFin _).symm k)⟩

lemma finiteDNF_depth {W : Type*} [Fintype W] (T : W → Type*) [∀ w, Fintype (T w)]
    {n : ℕ} (input : ∀ w, T w → Fin n) : (finiteDNF T input).depth ≤ 2 := by
  simp only [finiteDNF, depth]
  have h : (univ.sup fun j : Fin (Fintype.card W) =>
      1 + univ.sup (fun _ : Fin (Fintype.card (T ((Fintype.equivFin W).symm j))) => (0 : ℕ))) ≤ 1 := by
    apply Finset.sup_le
    intro j _
    simp
  omega

lemma finiteDNF_size {W : Type*} [Fintype W] (T : W → Type*) [∀ w, Fintype (T w)]
    {n : ℕ} (input : ∀ w, T w → Fin n) :
    (finiteDNF T input).size = 1 + ∑ w, (1 + Fintype.card (T w)) := by
  simp only [finiteDNF, size, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  congr 1
  simpa only [Nat.cast_id] using
    (Fintype.equivFin W).symm.sum_comp (fun w => 1 + Fintype.card (T w))

end AC0Circuit





lemma decodeStepWord_length {pairs : Finset (ℕ × ℕ)} {s : ℕ}
    (c : BoundedStepWords pairs s) : (decodeStepWord c).length = c.1.val := by
  simp [decodeStepWord]

lemma stepWord_covered (pairs : Finset (ℕ × ℕ)) (s : ℕ) (w : List SignedStep)
    (hlen : w.length ≤ s) (hpairs : ∀ a ∈ w, (a.tuple, a.padding) ∈ pairs) :
    ∃ c : BoundedStepWords pairs s, decodeStepWord c = w := by
  let f : Fin w.length → StepAlphabet pairs := fun i =>
    ⟨(w.get i).forward, ⟨((w.get i).tuple, (w.get i).padding), hpairs _ (List.get_mem _ _)⟩⟩
  refine ⟨⟨⟨w.length, by omega⟩, f⟩, ?_⟩
  change List.ofFn (fun i : Fin w.length => decodeStep (f i)) = w
  have he : (fun i : Fin w.length => decodeStep (f i)) = w.get := by
    funext i
    cases hw : w.get i
    simp only [f, decodeStep, hw]
  rw [he, List.ofFn_get]







lemma prohibitedInputAt_index (pairs : Finset (ℕ × ℕ)) (h s : ℕ) (n : ℤ)
    (c : ProhibitedCatalog pairs h s) (t : ProhibitedWordTests c) :
    prohibitedInputAt pairs h s n (prohibitedInputIndex pairs h s ⟨c, t⟩) =
      decide ((t.2.val : ℤ) ∣ n + wordDisplacement h ((decodeStepWord c.val).take t.1.val)) := by
  exact congrArg (fun u : ProhibitedInputs pairs h s =>
    decide ((u.2.2.val : ℤ) ∣ n + wordDisplacement h ((decodeStepWord u.1.val).take u.2.1.val)))
      ((prohibitedInputIndex pairs h s).symm_apply_apply ⟨c, t⟩)

lemma squarefree_divisor_iff (d : ℕ) (hd : Squarefree d) (n : ℤ) :
    (d : ℤ) ∣ n ↔ ∀ p ∈ d.primeFactors, (p : ℤ) ∣ n := by
  constructor
  · intro hn p hp
    have hp' : (p : ℤ) ∣ (d : ℤ) := by exact_mod_cast Nat.dvd_of_mem_primeFactors hp
    exact hp'.trans hn
  · intro hn
    rw [← Nat.prod_primeFactors_of_squarefree hd, Nat.cast_prod]
    apply prod_dvd_of_coprime
    · intro p hp q hq hpq
      exact ((Nat.coprime_primes (Nat.mem_primeFactors.mp hp).1
        (Nat.mem_primeFactors.mp hq).1).mpr hpq).cast (R := ℤ)
    · exact hn

lemma positiveWord_iff_prime_tests (h : ℕ) (n : ℤ) (w : List SignedStep)
    (hsq : ∀ a ∈ w, Squarefree (a.padding * a.tuple)) :
    PositiveWord h n w ↔ ∀ i : Fin w.length,
      ∀ p ∈ ((w.get i).padding * (w.get i).tuple).primeFactors,
        (p : ℤ) ∣ n + wordDisplacement h (w.take i.val) := by
  rw [positiveWord_iff_departures]
  apply forall_congr'
  intro i
  simpa only [SignedStep.divisor, Nat.cast_mul] using
    squarefree_divisor_iff _ (hsq _ (List.get_mem _ _)) (n + wordDisplacement h (w.take i.val))

/-- The circuit accepts precisely the manuscript's deleted event, not a
larger class of arbitrary positive paths. Minimal words are preselected. -/
theorem prohibitedCircuit_correct (pairs : Finset (ℕ × ℕ)) (h s : ℕ) (n : ℤ)
    (hsq : ∀ dq ∈ pairs, Squarefree (dq.2 * dq.1)) :
    (prohibitedCircuit pairs h s).eval (prohibitedInputAt pairs h s n) = true ↔
      ProhibitedSite h s (fun d q => (d, q) ∈ pairs) n := by
  rw [prohibitedCircuit, AC0Circuit.finiteDNF_eval]
  have hprime (c : ProhibitedCatalog pairs h s) :
      (∀ t : ProhibitedWordTests c,
        prohibitedInputAt pairs h s n (prohibitedInputIndex pairs h s ⟨c, t⟩) = true) ↔
        PositiveWord h n (decodeStepWord c.val) := by
    have hc : ∀ a ∈ decodeStepWord c.val, Squarefree (a.padding * a.tuple) := by
      intro a ha
      exact hsq _ (c.property.1.2.2.1 a ha)
    rw [positiveWord_iff_prime_tests h n _ hc]
    simp only [prohibitedInputAt_index, decide_eq_true_eq]
    constructor
    · intro ht i p hp
      exact ht ⟨i, ⟨p, hp⟩⟩
    · intro ht t
      exact ht t.1 t.2.val t.2.property
  simp_rw [hprime]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨decodeStepWord c.val, hc, c.property⟩
  · rintro ⟨w, hw, hmin⟩
    obtain ⟨c, hc⟩ := stepWord_covered pairs s w hmin.1.2.1 hmin.1.2.2.1
    refine ⟨⟨c, ?_⟩, ?_⟩
    · simpa only [hc] using hmin
    · simpa only [hc] using hw

theorem prohibitedCircuit_depth (pairs : Finset (ℕ × ℕ)) (h s : ℕ) :
    (prohibitedCircuit pairs h s).depth ≤ 2 := AC0Circuit.finiteDNF_depth _ _

theorem prohibitedCircuit_size (pairs : Finset (ℕ × ℕ)) (h s : ℕ) :
    (prohibitedCircuit pairs h s).size =
      1 + ∑ c : ProhibitedCatalog pairs h s, (1 + Fintype.card (ProhibitedWordTests c)) :=
  AC0Circuit.finiteDNF_size _ _

theorem card_boundedStepWords_le (pairs : Finset (ℕ × ℕ)) (s : ℕ) :
    Fintype.card (BoundedStepWords pairs s) ≤
      (s + 1) * (max 1 (2 * pairs.card)) ^ s := by
  rw [show Fintype.card (BoundedStepWords pairs s) =
    ∑ m : Fin (s + 1), (2 * pairs.card) ^ m.val by
      simp only [BoundedStepWords, Fintype.card_sigma, Fintype.card_fun,
        StepAlphabet, Fintype.card_prod, Fintype.card_bool, Fintype.card_coe, Fintype.card_fin]]
  calc
    _ ≤ ∑ _m : Fin (s + 1), (max 1 (2 * pairs.card)) ^ s := by
      apply sum_le_sum
      intro m _
      exact (Nat.pow_le_pow_left (le_max_right _ _) _).trans
        (Nat.pow_le_pow_right (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) (by omega))
    _ = _ := by simp [Nat.mul_comm]

theorem card_prohibitedWordTests_le {pairs : Finset (ℕ × ℕ)} {h s M : ℕ}
    (c : ProhibitedCatalog pairs h s)
    (hM : ∀ a ∈ decodeStepWord c.val, (a.padding * a.tuple).primeFactors.card ≤ M) :
    Fintype.card (ProhibitedWordTests c) ≤ s * M := by
  change Fintype.card ((i : Fin (decodeStepWord c.val).length) ×
    {p : ℕ // p ∈ (((decodeStepWord c.val).get i).padding *
      ((decodeStepWord c.val).get i).tuple).primeFactors}) ≤ _
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _i : Fin (decodeStepWord c.val).length, M := by
      apply sum_le_sum
      intro i _
      simpa only [Fintype.card_coe] using hM _ (List.get_mem _ _)
    _ = (decodeStepWord c.val).length * M := by simp
    _ ≤ s * M := Nat.mul_le_mul_right M (by
      rw [decodeStepWord_length]
      exact Nat.le_of_lt_succ c.val.1.isLt)

/-- An explicit size bound, including every input occurrence. The only
numerical data are the finite step alphabet and its prime-factor cap. -/
theorem prohibitedCircuit_size_le (pairs : Finset (ℕ × ℕ)) (h s M : ℕ)
    (hM : ∀ dq ∈ pairs, (dq.2 * dq.1).primeFactors.card ≤ M) :
    (prohibitedCircuit pairs h s).size ≤
      1 + ((s + 1) * (max 1 (2 * pairs.card)) ^ s) * (1 + s * M) := by
  have htests (c : ProhibitedCatalog pairs h s) : Fintype.card (ProhibitedWordTests c) ≤ s * M :=
    card_prohibitedWordTests_le c (fun a ha => hM _ (c.property.1.2.2.1 a ha))
  have hcatalog : Fintype.card (ProhibitedCatalog pairs h s) ≤
      (s + 1) * (max 1 (2 * pairs.card)) ^ s :=
    (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans
      (card_boundedStepWords_le pairs s)
  rw [prohibitedCircuit_size]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _c : ProhibitedCatalog pairs h s, (1 + s * M) :=
      sum_le_sum (fun c _ => Nat.add_le_add_left (htests c) 1)
    _ = Fintype.card (ProhibitedCatalog pairs h s) * (1 + s * M) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hcatalog

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PositiveWordProbability
namespace OAI

/-!
# Probability of one positive numerical word

The same residue coordinate is reused at every occurrence of a prime.
Selecting one occurrence per distinct prime therefore bounds the probability
by one reciprocal per distinct prime, including all padding factors. There
is no independence assumption between different sites of the word.
-/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


/-- Every residue modulo the true modulus has precisely its uniform mass,
even though the common carrier `Fin B` also contains zero-weight points. -/
theorem uniformResidueLaw_mod_eq (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B) (r : ZMod p) :
    (uniformResidueLaw B p hp hpB).probability
      (fun x => (x.val : ZMod p) = r) = (p : ℝ)⁻¹ := by
  classical
  let : NeZero p := ⟨hp.ne'⟩
  let : DecidableEq (ZMod p) := fun _ _ => Classical.propDecidable _
  let a : Fin B := ⟨r.val, r.val_lt.trans_le hpB⟩
  have ha : a.val < p := r.val_lt
  have har : (a.val : ZMod p) = r := ZMod.natCast_zmod_val r
  have hterm (x : Fin B) :
      (uniformResidueLaw B p hp hpB).weight x *
        (if (x.val : ZMod p) = r then (1 : ℝ) else 0) =
      if x = a then (p : ℝ)⁻¹ else 0 := by
    by_cases hx : x = a
    · subst x
      simp only [uniformResidueLaw_weight B p hp hpB a ha, har, ite_true, mul_one]
    · by_cases hxp : x.val < p
      · have hxr : (x.val : ZMod p) ≠ r := by
          intro he
          have hv := congrArg ZMod.val he
          rw [ZMod.val_natCast_of_lt hxp] at hv
          exact hx (Fin.ext hv)
        simp only [uniformResidueLaw_weight B p hp hpB x hxp, if_neg hxr,
          mul_zero, if_neg hx]
      · simp only [uniformResidueLaw, if_neg hxp, zero_mul, if_neg hx]
  unfold FiniteLaw.probability FiniteLaw.average
  dsimp only
  calc
    _ = ∑ x : Fin B, if x = a then (p : ℝ)⁻¹ else 0 :=
      Finset.sum_congr rfl (fun x _ => hterm x)
    _ = _ := by simp









end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedCircuitBounds
namespace OAI

/-! The numerical DNF size is below the manuscript's exp(L^3) budget. -/

namespace TwoPointCorrelations

theorem prohibitedCircuit_size_quadratic (pairs : Finset (ℕ × ℕ)) (h s M : ℕ) (L : ℝ)
    (hL : 110 ≤ L) (hs : (s : ℝ) ≤ L) (hM : (M : ℝ) ≤ L ^ (2 : ℕ))
    (hpairs : (pairs.card : ℝ) ≤ Real.exp (101 * L))
    (hcap : ∀ dq ∈ pairs, (dq.2 * dq.1).primeFactors.card ≤ M) :
    ((prohibitedCircuit pairs h s).size : ℝ) ≤ Real.exp (104 * L ^ (2 : ℕ)) := by
  have hL0 : 0 ≤ L := by linarith
  have hEL : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hLexp : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hmax : ((max 1 (2 * pairs.card) : ℕ) : ℝ) ≤ Real.exp (102 * L) := by
    push_cast
    apply max_le
    · have he : 1 ≤ Real.exp (102 * L) := by linarith [Real.add_one_le_exp (102 * L)]
      exact he
    · calc
        2 * (pairs.card : ℝ) ≤ Real.exp L * Real.exp (101 * L) :=
          mul_le_mul hEL hpairs (Nat.cast_nonneg _) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmain : ((max 1 (2 * pairs.card) : ℕ) : ℝ) ^ s ≤ Real.exp (102 * L ^ (2 : ℕ)) := by
    calc
      _ ≤ (Real.exp (102 * L)) ^ s := pow_le_pow_left₀ (Nat.cast_nonneg _) hmax _
      _ = Real.exp (102 * L * s) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ 102 * L by positivity)]
  have hfirst : (s : ℝ) + 1 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hlast : 1 + (s : ℝ) * M ≤ Real.exp (4 * L) := by
    have hcube : L ^ (3 : ℕ) ≤ Real.exp (3 * L) := by
      have hp := pow_le_pow_left₀ hL0 hLexp 3
      simpa only [← Real.exp_nat_mul, Nat.cast_ofNat] using hp
    have hEL3 : 1 ≤ Real.exp (3 * L) := by linarith [Real.add_one_le_exp (3 * L)]
    calc
      _ ≤ 1 + L ^ (3 : ℕ) := by
        have hm := mul_le_mul hs hM (Nat.cast_nonneg _) hL0
        nlinarith
      _ ≤ 1 + Real.exp (3 * L) := by linarith
      _ ≤ Real.exp L * Real.exp (3 * L) := by nlinarith
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hraw := prohibitedCircuit_size_le pairs h s M hcap
  have hraw' : ((prohibitedCircuit pairs h s).size : ℝ) ≤
      1 + ((s : ℝ) + 1) * ((max 1 (2 * pairs.card) : ℕ) : ℝ) ^ s * (1 + (s : ℝ) * M) := by
    exact_mod_cast hraw
  have h103 : 102 * L ^ (2 : ℕ) + 5 * L ≤ 103 * L ^ (2 : ℕ) := by nlinarith
  have hEL2 : 2 ≤ Real.exp (L ^ (2 : ℕ)) := by
    linarith [Real.add_one_le_exp (L ^ (2 : ℕ)), sq_nonneg (L - 1)]
  have hE103 : 1 ≤ Real.exp (103 * L ^ (2 : ℕ)) := by
    linarith [Real.add_one_le_exp (103 * L ^ (2 : ℕ)), sq_nonneg L]
  calc
    _ ≤ 1 + Real.exp L * Real.exp (102 * L ^ (2 : ℕ)) * Real.exp (4 * L) := by
      apply hraw'.trans
      gcongr
    _ = 1 + Real.exp (102 * L ^ (2 : ℕ) + 5 * L) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 1 + Real.exp (103 * L ^ (2 : ℕ)) :=
      add_le_add_right (Real.exp_le_exp.mpr h103) 1
    _ ≤ Real.exp (L ^ (2 : ℕ)) * Real.exp (103 * L ^ (2 : ℕ)) := by nlinarith
    _ = Real.exp (104 * L ^ (2 : ℕ)) := by rw [← Real.exp_add]; congr 1; ring



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedDensity
namespace OAI

/-! Density of the actual deleted event, with all finite catalog costs included. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


namespace ProhibitedPrimeFamily

variable {h J M : ℕ} (F : ProhibitedPrimeFamily h J M)


lemma whole_squarefree (dq : ℕ × ℕ) (hdq : dq ∈ F.pairs) : Squarefree (dq.2 * dq.1) := by
  apply (Nat.squarefree_mul ?_).mpr
  · exact ⟨F.padding_squarefree _ hdq, F.tuple_squarefree _ hdq⟩
  · apply (Nat.disjoint_primeFactors (F.padding_squarefree _ hdq).ne_zero
      (F.tuple_squarefree _ hdq).ne_zero).mp
    exact F.disjoint.symm.mono (F.padding_pool _ hdq) (F.tuple_pool _ hdq)






end ProhibitedPrimeFamily

open _root_.Filter


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeResidueLift
namespace OAI

/-! Evaluate the actual padding-periodic weights at one common integer lift of the product-law sample. -/

namespace TwoPointCorrelations.ProhibitedPrimeFamily

open _root_.Finset
open scoped _root_.Classical



lemma residueOrigin_spec {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)
    (x : ↥(data.P ∪ data.Q) → Fin B) (p : ↥(data.P ∪ data.Q)) :
    (data.residueOrigin x : ZMod p.val) = ((x p).val : ZMod p.val) :=
  (data.exists_residue_origin x).choose_spec p





end TwoPointCorrelations.ProhibitedPrimeFamily

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

theorem uniformResidue_product_average {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℕ) (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (F : (∀ i, ZMod (p i)) → ℝ) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun x => F (fun i => (x i).val)) = uniformAverage F := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  rw [μ.average_fibers (fun x i => ((x i).val : ZMod (p i))) F]
  have hprob (y : ∀ i, ZMod (p i)) :
      μ.probability (fun x => (fun i => ((x i).val : ZMod (p i))) = y) =
        ∏ i, (p i : ℝ)⁻¹ := by
    have he : (fun x : ι → Fin B => (fun i => ((x i).val : ZMod (p i))) = y) =
        (fun x => ∀ i, ((x i).val : ZMod (p i)) = y i) := by
      funext x
      exact propext funext_iff
    rw [he]
    dsimp only [μ]
    rw [FiniteLaw.independent_probability_all
      (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
      (fun i (x : Fin B) => (x.val : ZMod (p i)) = y i)]
    apply prod_congr rfl
    intro i _
    exact uniformResidueLaw_mod_eq B (p i) (hp i) (hpB i) (y i)
  simp only [hprob, uniformAverage, Fintype.card_pi, ZMod.card, Nat.cast_prod,
    div_eq_mul_inv, ← prod_inv_distrib, ← mul_sum]
  ring

local instance residuePrime_neZero {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (p : ↥(data.P ∪ data.Q)) : NeZero p.val := ⟨(data.prime p).ne_zero⟩


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueRestriction
namespace OAI

/-! Restriction of a product law to selected prime coordinates.  The
coordinate laws may depend on the prime; no common-modulus uniformity is
assumed. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw

lemma independent_average_reindex {ι κ A : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Fintype A]
    (e : ι ≃ κ) (μ : κ → FiniteLaw A) (f : (κ → A) → ℝ) :
    (independent μ).average f =
      (independent (fun i => μ (e i))).average (fun x => f (fun k => x (e.symm k))) := by
  let E : (ι → A) ≃ (κ → A) := Equiv.arrowCongr e (Equiv.refl A)
  calc
    _ = ∑ x : ι → A, (independent μ).weight (E x) * f (E x) :=
      (E.sum_comp (fun x => (independent μ).weight x * f x)).symm
    _ = _ := by
      apply sum_congr rfl
      intro x _
      change (∏ k, (μ k).weight (x (e.symm k))) * f (fun k => x (e.symm k)) =
        (∏ i, (μ (e i)).weight (x i)) * f (fun k => x (e.symm k))
      congr 1
      simpa only [e.apply_symm_apply] using
        e.symm.prod_comp (fun i => (μ (e i)).weight (x i))



end FiniteLaw

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)









end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeCoordinates
namespace OAI

/-! The common padded prime law in the canonical finite coordinate order. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

local instance canonicalPrime_neZero {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (i : Fin (Fintype.card ↥(data.P ∪ data.Q))) :
    NeZero (primeResidueModuli (data.P ∪ data.Q) i) :=
  ⟨(primeResidueModuli_prime _ (fun p hp => data.prime ⟨p, hp⟩) i).ne_zero⟩

lemma ProhibitedPrimeFamily.residue_average_canonical {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (F : (∀ i, ZMod (primeResidueModuli (data.P ∪ data.Q) i)) → ℝ) :
    (data.residueLaw B hB).average
      (fun x => F (fun i => (x ((Fintype.equivFin ↥(data.P ∪ data.Q)).symm i)).val)) =
      uniformAverage F := by
  unfold ProhibitedPrimeFamily.residueLaw
  rw [FiniteLaw.independent_average_reindex (Fintype.equivFin ↥(data.P ∪ data.Q)).symm]
  simp only [Equiv.symm_symm, Equiv.apply_symm_apply]
  exact uniformResidue_product_average B (primeResidueModuli (data.P ∪ data.Q))
    (fun i => (data.prime _).pos) (fun i => hB _ ((Fintype.equivFin ↥(data.P ∪ data.Q)).symm i).property) F

lemma ProhibitedPrimeFamily.canonical_origin {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (x : ↥(data.P ∪ data.Q) → Fin B) :
    (fun i => (data.residueOrigin x : ZMod (primeResidueModuli (data.P ∪ data.Q) i))) =
      (fun i => ((x ((Fintype.equivFin ↥(data.P ∪ data.Q)).symm i)).val :
        ZMod (primeResidueModuli (data.P ∪ data.Q) i))) := by
  funext i
  exact data.residueOrigin_spec x ((Fintype.equivFin ↥(data.P ∪ data.Q)).symm i)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedWordCircuit
namespace OAI

/-! The surviving-site mask for every departure of one closed word is
an actual small circuit. Each complemented prohibited DNF keeps its
original prime input occurrences. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma prohibitedWordKeepCircuit_eval (pairs : Finset (ℕ × ℕ)) (h s : ℕ)
    (hsq : ∀ dq ∈ pairs, Squarefree (dq.2 * dq.1))
    {R n : ℕ} (index : Fin R → Fin (Fintype.card (ProhibitedInputs pairs h s)) → Fin n)
    (site : Fin R → ℤ) (x : BooleanCube n)
    (hx : ∀ r i, x (index r i) = prohibitedInputAt pairs h s (site r) i) :
    (prohibitedWordKeepCircuit pairs h s index).eval x = true ↔
      ∀ r, ¬ProhibitedSite h s (fun d q => (d, q) ∈ pairs) (site r) := by
  rw [prohibitedWordKeepCircuit, AC0Circuit.conjunction_eval]
  apply forall_congr'
  intro r
  rw [AC0Circuit.relabel_eval, AC0Circuit.negate_eval]
  have hb : (fun i => x (index r i)) = prohibitedInputAt pairs h s (site r) := funext (hx r)
  rw [hb, ne_eq, prohibitedCircuit_correct pairs h s (site r) hsq]

lemma prohibitedWordKeepCircuit_depth (pairs : Finset (ℕ × ℕ)) (h s : ℕ)
    {R n : ℕ} (index : Fin R → Fin (Fintype.card (ProhibitedInputs pairs h s)) → Fin n) :
    (prohibitedWordKeepCircuit pairs h s index).depth ≤ 3 := by
  apply AC0Circuit.conjunction_depth (d := 2)
  intro r
  exact (AC0Circuit.relabel_depth _ _).trans
    ((AC0Circuit.negate_depth _).le.trans (prohibitedCircuit_depth pairs h s))

lemma prohibitedWordKeepCircuit_size (pairs : Finset (ℕ × ℕ)) (h s : ℕ)
    {R n : ℕ} (index : Fin R → Fin (Fintype.card (ProhibitedInputs pairs h s)) → Fin n) :
    (prohibitedWordKeepCircuit pairs h s index).size ≤
      1 + R * (prohibitedCircuit pairs h s).size := by
  rw [prohibitedWordKeepCircuit, AC0Circuit.conjunction_size]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _r : Fin R, (prohibitedCircuit pairs h s).size := by
      apply sum_le_sum
      intro r _
      exact (AC0Circuit.relabel_size _ _).trans (AC0Circuit.negate_size _).le
    _ = _ := by simp

lemma prohibitedWordKeepCircuit_size_budget (pairs : Finset (ℕ × ℕ)) (h s M : ℕ)
    {R n : ℕ} (index : Fin R → Fin (Fintype.card (ProhibitedInputs pairs h s)) → Fin n)
    (L : ℝ) (hL : 110 ≤ L) (hR : (R : ℝ) ≤ 4 * L) (hs : (s : ℝ) ≤ L)
    (hM : (M : ℝ) ≤ L ^ 2) (hpairs : (pairs.card : ℝ) ≤ Real.exp (101 * L))
    (hcap : ∀ dq ∈ pairs, (dq.2 * dq.1).primeFactors.card ≤ M) :
    ((prohibitedWordKeepCircuit pairs h s index).size : ℝ) ≤ Real.exp (L ^ 3) := by
  have hb := prohibitedCircuit_size_quadratic pairs h s M L hL hs hM hpairs hcap
  have hn : (0 : ℝ) ≤ (prohibitedCircuit pairs h s).size := Nat.cast_nonneg _
  have hraw : ((prohibitedWordKeepCircuit pairs h s index).size : ℝ) ≤
      1 + R * (prohibitedCircuit pairs h s).size := by
    exact_mod_cast prohibitedWordKeepCircuit_size pairs h s index
  have hE : (1 : ℝ) ≤ Real.exp (104 * L ^ 2) := Real.one_le_exp_iff.mpr (by positivity)
  have hLexp : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have h5 : (5 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hLp : 0 ≤ L := by linarith
  calc
    _ ≤ 1 + 4 * L * Real.exp (104 * L ^ 2) := by
      apply hraw.trans
      gcongr
    _ ≤ 5 * Real.exp L * Real.exp (104 * L ^ 2) := by nlinarith [Real.exp_pos L]
    _ ≤ Real.exp L * Real.exp L * Real.exp (104 * L ^ 2) := by gcongr
    _ = Real.exp (104 * L ^ 2 + 2 * L) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (105 * L ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (show 0 ≤ L - 105 by linarith) (sq_nonneg L)]




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingProduct
namespace OAI

/-! Identify recursive padding weights with the literal product at the numerical departures. -/

namespace TwoPointCorrelations

open _root_.Finset


lemma wordDisplacement_take_succ (h : ℕ) (word : List SignedStep) (t : ℕ) :
    wordDisplacement h (word.take (t + 1)) =
      wordDisplacement h (word.take t) + wordStepDisplacement h word t := by
  simp only [wordDisplacement_take, sum_range_succ]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ClosedWordPadding
namespace OAI

/-! Separate the actual closed matrix word into centered factors and its retained padding weight. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




theorem closed_signed_word_factorization (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (center : SignedStep → ℤ → ℝ)
    (L K : ℝ) (extra : SignedStep → ℤ → Prop) (h : ℕ) (n : ℤ) (word : List SignedStep)
    (hg : ∀ n, g n ≠ 0)
    (hperiod : ∀ t, ∀ q ∈ Q, ∀ z, center t (z + (h * q * t.tuple : ℕ)) = center t z)
    (hclosed : wordDisplacement h word = 0) :
    scalarWalkProduct h (fun t x =>
      signedIntegerWeight Q u (eligible t) g (center t) L K (extra t) h t x) n word =
      scalarWalkProduct h (retainedEdgeDeparture Q u eligible g L K extra h) n word *
        scalarWalkProduct h center n word := by
  rw [signedIntegerWeight_closed_normalize Q u eligible g center L K extra h n word
    hg hperiod hclosed]
  rw [← scalarWalkProduct_mul]
  apply scalarWalkProduct_congr
  intro t x
  unfold retainedEdgeDeparture
  split_ifs <;> ring




theorem scalarWalkProduct_ofFn {m : ℕ} (h : ℕ) (weight : SignedStep → ℤ → ℝ)
    (step : Fin m → SignedStep) (n : ℤ) :
    scalarWalkProduct h weight n (List.ofFn step) =
      ∏ i : Fin m, weight (step i) (n + wordDisplacement h ((List.ofFn step).take i.val)) := by
  induction m generalizing n with
  | zero => simp [scalarWalkProduct]
  | succ m ih =>
      rw [List.ofFn_succ, scalarWalkProduct, ih, Fin.prod_univ_succ]
      simp only [Fin.val_zero, List.take_zero, wordDisplacement_nil, add_zero]
      congr 1
      apply prod_congr rfl
      intro i _
      simp only [Fin.val_succ, List.take_succ_cons, wordDisplacement_cons,
        add_assoc]

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


lemma columnTuple_primeFactors {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : Fin R)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    (columnTuple w i).primeFactors = univ.image (fun j => (w j i).val) := by
  exact familyTuple_primeFactors (fun _ p => p.val)
    (fun j p => hprime j _ p.property) (fun j => w j i)
    (selectedPrimeValues_injective (fun j => w j i) hdisjoint)




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ClosedVertexMask
namespace OAI

/-! A closed nonempty word counts a binary vertex mask once per departure, despite the two edge endpoints. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma closed_binary_mask_product {m : ℕ} (hm : 0 < m)
    (site : Fin (m + 1) → ℤ) (hclosed : site (Fin.last m) = site 0)
    (mask : ℤ → ℝ) (hmask : ∀ z, mask z = 0 ∨ mask z = 1) :
    (∏ i : Fin m, mask (site i.castSucc) * mask (site i.succ)) =
      ∏ i : Fin m, mask (site i.castSucc) := by
  by_cases hz : ∃ i : Fin m, mask (site i.castSucc) = 0
  · obtain ⟨i, hi⟩ := hz
    rw [prod_mul_distrib, prod_eq_zero (mem_univ i) hi, zero_mul]
  · have hd (i : Fin m) : mask (site i.castSucc) = 1 :=
      (hmask _).resolve_left (fun hi => hz ⟨i, hi⟩)
    have ha (i : Fin m) : mask (site i.succ) = 1 := by
      by_cases hi : i.val + 1 < m
      · have he : i.succ = (⟨i.val + 1, hi⟩ : Fin m).castSucc := Fin.ext rfl
        rw [he, hd]
      · have he : i.succ = Fin.last m := Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
        have he0 : (⟨0, hm⟩ : Fin m).castSucc = (0 : Fin (m + 1)) := Fin.ext rfl
        rw [he, hclosed, ← he0, hd]
    simp only [hd, ha, mul_one, prod_const_one]

theorem closed_masked_scalar_word {m : ℕ} (hm : 0 < m)
    (h : ℕ) (step : Fin m → SignedStep) (n : ℤ)
    (hclosed : wordDisplacement h (List.ofFn step) = 0)
    (weight : SignedStep → ℤ → ℝ) (mask : ℤ → ℝ)
    (hmask : ∀ z, mask z = 0 ∨ mask z = 1) :
    scalarWalkProduct h (fun t z => mask z * weight t z * mask (z + t.displacement h))
      n (List.ofFn step) =
      scalarWalkProduct h weight n (List.ofFn step) *
        scalarWalkProduct h (fun _ z => mask z) n (List.ofFn step) := by
  let site (i : Fin (m + 1)) := n + wordDisplacement h ((List.ofFn step).take i.val)
  have hsite : site (Fin.last m) = site 0 := by
    have ht : (List.ofFn step).take m = List.ofFn step :=
      List.take_of_length_le (by simp)
    simp only [site, Fin.val_last, ht, hclosed, add_zero, Fin.val_zero,
      List.take_zero, wordDisplacement_nil]
  have hs (i : Fin m) : site i.castSucc + (step i).displacement h = site i.succ := by
    have ht : wordStepDisplacement h (List.ofFn step) i.val = (step i).displacement h := by
      simp only [wordStepDisplacement, List.getElem?_ofFn, i.isLt, dite_true, Fin.eta,
        Option.map_some, Option.getD_some]
    simp only [site, Fin.val_castSucc, Fin.val_succ, wordDisplacement_take_succ, ht, add_assoc]
  simp only [scalarWalkProduct_ofFn]
  change (∏ i : Fin m, mask (site i.castSucc) * weight (step i) (site i.castSucc) *
      mask (site i.castSucc + (step i).displacement h)) =
    (∏ i : Fin m, weight (step i) (site i.castSucc)) * ∏ i : Fin m, mask (site i.castSucc)
  calc
    _ = (∏ i : Fin m, weight (step i) (site i.castSucc)) *
        ∏ i : Fin m, mask (site i.castSucc) * mask (site i.succ) := by
      rw [← prod_mul_distrib]
      apply prod_congr rfl
      intro i _
      rw [hs]
      ring
    _ = _ := by rw [closed_binary_mask_product hm site hsite mask hmask]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedWordIdentity
namespace OAI

/-! Exact identification of a masked closed matrix word with the literal
centered word average.  No arithmetic or probabilistic estimate is assumed. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma centeredTuple_column {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : Fin R)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) :
    centeredTuple (columnTuple w i).primeFactors n =
      ∏ j, ((if ((w j i).val : ℤ) ∣ n then (1 : ℝ) else 0) - ((w j i).val : ℝ)⁻¹) := by
  unfold centeredTuple
  rw [columnTuple_primeFactors w i hprime hdisjoint, prod_image]
  exact fun _ _ _ _ he => selectedPrimeValues_injective (fun j => w j i) hdisjoint he





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

lemma actualPaddingWeight_one_le (Q : Finset ℕ) (n : ℤ) : 1 ≤ actualPaddingWeight Q n :=
  one_le_pow₀ (by norm_num)

lemma actualPaddingVertex_one_le (Q : Finset ℕ) (n : ℤ) : 1 ≤ actualPaddingVertex Q n := by
  simpa only [actualPaddingVertex, Real.sqrt_one] using
    Real.sqrt_le_sqrt (actualPaddingWeight_one_le Q n)

lemma actualPaddingVertex_pos (Q : Finset ℕ) (n : ℤ) : 0 < actualPaddingVertex Q n :=
  zero_lt_one.trans_le (actualPaddingVertex_one_le Q n)

lemma actualPaddingVertex_ne_zero (Q : Finset ℕ) (n : ℤ) : actualPaddingVertex Q n ≠ 0 :=
  (actualPaddingVertex_pos Q n).ne'

lemma actualPaddingVertex_sq (Q : Finset ℕ) (n : ℤ) :
    actualPaddingVertex Q n ^ 2 = actualPaddingWeight Q n :=
  Real.sq_sqrt (zero_le_one.trans (actualPaddingWeight_one_le Q n))
















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingActiveState
namespace OAI

/-! Exact finite-index active states for the literal padding primes.
The same state determines the vertex normalization and every retained
squarefree padding-divisor test. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma paddingActiveState_image {m : ℕ} (Q : Finset ℕ) (e : Fin m ≃ Q) (n : ℤ) :
    (paddingActiveState Q e n).image (fun i => (e i).val) =
      Q.filter (fun p : ℕ => (p : ℤ) ∣ n) := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    exact mem_filter.mpr ⟨(e i).property, by simpa [paddingActiveState, activeState] using hi⟩
  · intro hp
    obtain ⟨hpQ, hd⟩ := mem_filter.mp hp
    obtain ⟨i, hi⟩ := e.surjective ⟨p, hpQ⟩
    apply mem_image.mpr
    refine ⟨i, ?_, congrArg Subtype.val hi⟩
    simp only [paddingActiveState, activeState, mem_filter, mem_univ, true_and,
      decide_eq_true_eq]
    simpa only [hi] using hd

lemma paddingActiveState_card {m : ℕ} (Q : Finset ℕ) (e : Fin m ≃ Q) (n : ℤ) :
    (paddingActiveState Q e n).card = actualPaddingDegree Q n := by
  have hi : Function.Injective (fun i => (e i).val) :=
    Subtype.val_injective.comp e.injective
  have hh := congrArg Finset.card (paddingActiveState_image Q e n)
  rw [card_image_of_injective _ hi] at hh
  exact hh

lemma actualPaddingVertex_sq_activeState {m : ℕ} (Q : Finset ℕ) (e : Fin m ≃ Q) (n : ℤ) :
    (actualPaddingVertex Q n) ^ 2 = (5 : ℝ) ^ (paddingActiveState Q e n).card := by
  rw [actualPaddingVertex_sq, actualPaddingWeight, paddingActiveState_card]

lemma retainedPadding_dvd_iff_activeState {m : ℕ} (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (e : Fin m ≃ Q) (q : ℕ)
    (hq : q ∈ retainedPrimeDivisors Q) (n : ℤ) :
    (q : ℤ) ∣ n ↔ q.primeFactors ⊆
      (paddingActiveState Q e n).image (fun i => (e i).val) := by
  rw [paddingActiveState_image, ← paddingAvailablePrimes_integer]
  exact (padding_literal_support_iff_dvd Q hQ n q hq).symm




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingStateWeights
namespace OAI

/-! The actual retained departure coefficient is an explicit function
of the finite padding states at its two endpoints. This is the scalar
coefficient used in the signed finite-law expansion. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma paddingDensity_eq_state {m : ℕ} (Qp Q : Finset ℕ)
    (hQp : ∀ p ∈ Qp, p.Prime) (hQ : Q ⊆ retainedPrimeDivisors Qp)
    (e : Fin m ≃ Qp) (eligible : ℕ → Prop) (n : ℤ) :
    paddingDensity Q actualPaddingCoefficient eligible (actualPaddingVertex Qp) n =
      paddingStateDensity Qp Q e eligible (paddingActiveState Qp e n) := by
  unfold paddingDensity paddingStateDensity
  rw [actualPaddingVertex_sq_activeState Qp e n]
  congr 1
  apply sum_congr rfl
  intro q hq
  simp only [retainedPadding_dvd_iff_activeState Qp hQp e q (hQ hq) n]

lemma integerEdgeKeep_eq_state {m : ℕ} (Qp Q : Finset ℕ)
    (hQp : ∀ p ∈ Qp, p.Prime) (hQ : Q ⊆ retainedPrimeDivisors Qp)
    (e : Fin m ≃ Qp) (eligible : ℕ → Prop) (L K : ℝ) (n : ℤ) :
    integerEdgeKeep Q actualPaddingCoefficient eligible (actualPaddingVertex Qp) L K
      (actualPaddingDegreeCut Qp L) n ↔
      paddingStateKeep Qp Q e eligible L K (paddingActiveState Qp e n) := by
  simp only [integerEdgeKeep, paddingStateKeep, paddingDensity_eq_state Qp Q hQp hQ e,
    actualPaddingDegreeCut, paddingActiveState_card]

lemma retainedEdgeDeparture_eq_state {m : ℕ} (Qp Q : Finset ℕ)
    (hQp : ∀ p ∈ Qp, p.Prime) (hQ : Q ⊆ retainedPrimeDivisors Qp)
    (e : Fin m ≃ Qp) (eligible : SignedStep → ℕ → Prop) (L K : ℝ)
    (h : ℕ) (t : SignedStep) (n : ℤ) :
    retainedEdgeDeparture Q actualPaddingCoefficient eligible (actualPaddingVertex Qp) L K
      (fun _ => actualPaddingDegreeCut Qp L) h t n =
      paddingStateDeparture Qp Q e eligible L K t
        (paddingActiveState Qp e n) (paddingActiveState Qp e (n + t.displacement h)) := by
  unfold retainedEdgeDeparture paddingStateDeparture
  by_cases hq : t.padding ∈ Q
  · simp only [retainedPadding_dvd_iff_activeState Qp hQp e t.padding (hQ hq) n,
      integerEdgeKeep_eq_state Qp Q hQp hQ e,
      actualPaddingVertex_sq_activeState Qp e n]
  · simp only [hq, false_and, ite_false]

lemma paddingStateDeparture_nonneg {m : ℕ} (Qp Q : Finset ℕ) (e : Fin m ≃ Qp)
    (eligible : SignedStep → ℕ → Prop) (L K : ℝ) (t : SignedStep)
    (S T : Finset (Fin m)) (hL : 0 ≤ L) :
    0 ≤ paddingStateDeparture Qp Q e eligible L K t S T := by
  unfold paddingStateDeparture
  split_ifs
  · exact div_nonneg (mul_nonneg hL (actualPaddingCoefficient_nonneg _)) (by positivity)
  · exact le_rfl

lemma paddingStateDeparture_le {m : ℕ} (Qp Q : Finset ℕ) (e : Fin m ≃ Qp)
    (eligible : SignedStep → ℕ → Prop) (L K : ℝ) (t : SignedStep)
    (S T : Finset (Fin m)) (hL : 0 ≤ L) :
    paddingStateDeparture Qp Q e eligible L K t S T ≤ L * actualPaddingCoefficient t.padding := by
  unfold paddingStateDeparture
  split_ifs
  · exact div_le_self (mul_nonneg hL (actualPaddingCoefficient_nonneg _))
      (one_le_pow₀ (by norm_num))
  · exact mul_nonneg hL (actualPaddingCoefficient_nonneg _)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WeightedWordCoefficient
namespace OAI

/-! The coefficient table in the finite-state expansion is the literal
retained padding product times the signed centered-prime product. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma centeredWordBits_abs_le {R J : ℕ} (p : Fin R → Fin J → ℕ)
    (hp : ∀ i j, (p i j).Prime) (bits : BooleanCube (R * J)) :
    |centeredWordBits p bits| ≤ 1 := by
  unfold centeredWordBits
  simp only [abs_prod]
  apply Finset.prod_le_one
  · intro i _
    positivity
  · intro i _
    apply Finset.prod_le_one
    · intro j _
      exact abs_nonneg _
    · intro j _
      have hpos : (0 : ℝ) < p i j := by exact_mod_cast (hp i j).pos
      have hone : (1 : ℝ) ≤ p i j := by exact_mod_cast (hp i j).one_lt.le
      have hinv : (p i j : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hpos).mpr hone
      cases bits (finProdFinEquiv (i, j)) <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · simpa only [zero_sub, abs_neg, abs_of_nonneg (inv_nonneg.mpr hpos.le)] using hinv
      · rw [abs_of_nonneg (by linarith : 0 ≤ 1 - (p i j : ℝ)⁻¹)]
        linarith [inv_nonneg.mpr hpos.le]


lemma actualWordCoefficient_abs_le {R J m : ℕ}
    (Qp Q : Finset ℕ) (e : Fin m ≃ Qp) (eligible : SignedStep → ℕ → Prop)
    (L K : ℝ) (step : Fin R → SignedStep) (p : Fin R → Fin J → ℕ)
    (hp : ∀ i j, (p i j).Prime) (hL : 0 ≤ L)
    (S : Fin (R + 1) → Finset (Fin m)) (bits : BooleanCube (R * J)) :
    |actualWordCoefficient Qp Q e eligible L K step p S bits| ≤
      ∏ i : Fin R, L * actualPaddingCoefficient (step i).padding := by
  rw [actualWordCoefficient, abs_mul, abs_prod]
  calc
    _ ≤ (∏ i : Fin R, L * actualPaddingCoefficient (step i).padding) * 1 := by
      apply mul_le_mul _ (centeredWordBits_abs_le p hp bits) (abs_nonneg _)
        (prod_nonneg (fun i _ => mul_nonneg hL (actualPaddingCoefficient_nonneg _)))
      apply Finset.prod_le_prod
      · intro i _
        exact abs_nonneg _
      · intro i _
        rw [abs_of_nonneg (paddingStateDeparture_nonneg Qp Q e eligible L K _ _ _ hL)]
        exact paddingStateDeparture_le Qp Q e eligible L K _ _ _ hL
    _ = _ := mul_one _

lemma actualWordCoefficient_budget {R J m : ℕ}
    (Qp Q : Finset ℕ) (e : Fin m ≃ Qp) (eligible : SignedStep → ℕ → Prop)
    (L K : ℝ) (step : Fin R → SignedStep) (p : Fin R → Fin J → ℕ)
    (hp : ∀ i j, (p i j).Prime) (hL : 4800 ≤ L) (hR : (R : ℝ) ≤ 4 * L)
    (hdeg : ∀ i, ((step i).padding.primeFactors.card : ℝ) ≤ 100 * Real.log L)
    (S : Fin (R + 1) → Finset (Fin m)) (bits : BooleanCube (R * J)) :
    |actualWordCoefficient Qp Q e eligible L K step p S bits| ≤ Real.exp (L ^ 4) := by
  have hLp : 0 ≤ L := by linarith
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hLexp : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hu (i : Fin R) : L * actualPaddingCoefficient (step i).padding ≤ Real.exp (401 * L) := by
    have hd : actualPaddingCoefficient (step i).padding ≤ Real.exp (400 * L) := by
      unfold actualPaddingCoefficient
      calc
        _ ≤ (Real.exp 4) ^ (step i).padding.primeFactors.card :=
          pow_le_pow_left₀ (by norm_num) hfour _
        _ = Real.exp ((step i).padding.primeFactors.card * 4) := by rw [Real.exp_nat_mul]
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [hdeg i])
    calc
      _ ≤ Real.exp L * Real.exp (400 * L) :=
        mul_le_mul hLexp hd (actualPaddingCoefficient_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (actualWordCoefficient_abs_le Qp Q e eligible L K step p hp hLp S bits).trans
  calc
    _ ≤ ∏ _i : Fin R, Real.exp (401 * L) :=
      Finset.prod_le_prod (fun i _ => mul_nonneg hLp (actualPaddingCoefficient_nonneg _)) (fun i _ => hu i)
    _ = Real.exp ((R : ℝ) * (401 * L)) := by simp only [prod_const, card_univ,
      Fintype.card_fin, Real.exp_nat_mul]
    _ ≤ Real.exp (1604 * L ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hR (show 0 ≤ 401 * L by positivity)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh : 1604 ≤ L ^ 2 := by nlinarith
      nlinarith [mul_nonneg (show 0 ≤ L ^ 2 - 1604 by linarith) (sq_nonneg L)]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualWordStateIdentity
namespace OAI

/-! Exact evaluation of the coefficient table on the integer sites of a
word, including both endpoints of every retained departure. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma wordVertexSite_step {R : ℕ} (h : ℕ) (step : Fin R → SignedStep) (n : ℤ)
    (i : Fin R) :
    wordVertexSite h step n i.succ =
      wordVertexSite h step n i.castSucc + (step i).displacement h := by
  unfold wordVertexSite
  rw [wordDisplacement_take, wordDisplacement_take]
  simp only [Fin.val_succ, Fin.val_castSucc, sum_range_succ]
  have he : wordStepDisplacement h (List.ofFn step) i.val = (step i).displacement h := by
    simp [wordStepDisplacement]
  rw [he]
  ring

lemma retainedWord_eq_state_product {R m : ℕ} (Qp Q : Finset ℕ)
    (hQp : ∀ p ∈ Qp, p.Prime) (hQ : Q ⊆ retainedPrimeDivisors Qp)
    (e : Fin m ≃ Qp) (eligible : SignedStep → ℕ → Prop) (L K : ℝ)
    (h : ℕ) (step : Fin R → SignedStep) (n : ℤ) :
    scalarWalkProduct h
      (retainedEdgeDeparture Q actualPaddingCoefficient eligible (actualPaddingVertex Qp) L K
        (fun _ => actualPaddingDegreeCut Qp L) h) n (List.ofFn step) =
      ∏ i : Fin R, paddingStateDeparture Qp Q e eligible L K (step i)
        (paddingActiveState Qp e (wordVertexSite h step n i.castSucc))
        (paddingActiveState Qp e (wordVertexSite h step n i.succ)) := by
  rw [scalarWalkProduct_ofFn]
  apply prod_congr rfl
  intro i _
  rw [retainedEdgeDeparture_eq_state Qp Q hQp hQ e]
  change paddingStateDeparture Qp Q e eligible L K (step i)
      (paddingActiveState Qp e (wordVertexSite h step n i.castSucc))
      (paddingActiveState Qp e (wordVertexSite h step n i.castSucc + (step i).displacement h)) = _
  rw [← wordVertexSite_step]


lemma wordCenteredBits_apply {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (h : ℕ) (step : Fin R → SignedStep) (n : ℤ)
    (i : Fin R) (j : Fin J) :
    wordCenteredBits w h step n (finProdFinEquiv (i, j)) =
      decide (((w j i).val : ℤ) ∣ wordVertexSite h step n i.castSucc) :=
  congrArg (fun ij : Fin R × Fin J =>
    decide (((w ij.2 ij.1).val : ℤ) ∣ wordVertexSite h step n ij.1.castSucc))
    ((finProdFinEquiv : Fin R × Fin J ≃ Fin (R * J)).symm_apply_apply (i, j))

lemma centeredWord_eq_state_bits {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (h : ℕ) (n : ℤ) :
    let step := fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i)
    scalarWalkProduct h (fun t n => centeredTuple t.tuple.primeFactors n) n (List.ofFn step) =
      centeredWordBits (fun i j => (w j i).val) (wordCenteredBits w h step n) := by
  dsimp only
  rw [scalarWalkProduct_ofFn]
  unfold centeredWordBits
  apply prod_congr rfl
  intro i _
  rw [centeredTuple_column w i hprime hdisjoint]
  apply prod_congr rfl
  intro j _
  simp only [wordCenteredBits_apply, decide_eq_true_eq]
  rfl

lemma actualWordCoefficient_integer_identity {J R m : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (Qp Q : Finset ℕ) (hQp : ∀ p ∈ Qp, p.Prime) (hQ : Q ⊆ retainedPrimeDivisors Qp)
    (e : Fin m ≃ Qp) (eligible : SignedStep → ℕ → Prop) (L K : ℝ) (h : ℕ) (n : ℤ) :
    let step := fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i)
    actualWordCoefficient Qp Q e eligible L K step (fun i j => (w j i).val)
      (fun i => paddingActiveState Qp e (wordVertexSite h step n i))
      (wordCenteredBits w h step n) =
    scalarWalkProduct h
      (retainedEdgeDeparture Q actualPaddingCoefficient eligible (actualPaddingVertex Qp) L K
        (fun _ => actualPaddingDegreeCut Qp L) h) n (List.ofFn step) *
      scalarWalkProduct h (fun t n => centeredTuple t.tuple.primeFactors n) n (List.ofFn step) := by
  dsimp only
  rw [actualWordCoefficient, retainedWord_eq_state_product Qp Q hQp hQ e,
    centeredWord_eq_state_bits w forward padding hprime hdisjoint]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualWordInputs
namespace OAI

/-! A finite list of every literal in a weighted word: the padding
state at each endpoint, its centered-prime tests, and every occurrence
in the prohibited-site DNFs. Equal primes share one residue coordinate. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical








lemma actualWordQIndex_eval {h J M R m : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s : ℕ) (e : Fin m ≃ data.Q) (step : Fin R → SignedStep)
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q)) (n : ℤ) (r : Fin (R + 1)) (j : Fin m) :
    actualWordIntegerBits data s e step label n (actualWordQIndex data s R m r j) =
      decide (((e j).val : ℤ) ∣ wordVertexSite h step n r) := by
  rw [actualWordIntegerBits, primeLiteral_integer_input]
  simp only [actualWordLiterals, actualWordQIndex, Equiv.symm_apply_apply, wordVertexSite,
    zero_add]
  rfl

lemma actualWordBadIndex_eval {h J M R m : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s : ℕ) (e : Fin m ≃ data.Q) (step : Fin R → SignedStep)
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q)) (n : ℤ) (r : Fin (R + 1))
    (j : Fin (Fintype.card (ProhibitedInputs data.pairs h s))) :
    actualWordIntegerBits data s e step label n (actualWordBadIndex data s R m r j) =
      prohibitedInputAt data.pairs h s (wordVertexSite h step n r) j := by
  rw [actualWordIntegerBits, primeLiteral_integer_input]
  simp only [actualWordLiterals, actualWordBadIndex, Equiv.symm_apply_apply,
    ProhibitedPrimeFamily.prohibitedLiteral, prohibitedInputAt, wordVertexSite, zero_add,
    add_assoc]

lemma actualWordPIndex_eval {h J M R m : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (s : ℕ) (e : Fin m ≃ data.Q)
    (w : ColumnPrimeAssignment J R P) (step : Fin R → SignedStep)
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val) (n : ℤ) (k : Fin (R * J)) :
    actualWordIntegerBits data s e step label n (actualWordPIndex data s R m k) =
      wordCenteredBits w h step n k := by
  rw [actualWordIntegerBits, primeLiteral_integer_input]
  simp only [actualWordLiterals, actualWordPIndex, Equiv.symm_apply_apply]
  simp only [hlabel, wordCenteredBits, wordVertexSite, zero_add]
  rfl

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ClosedWordStateMask
namespace OAI

/-! The actual closed masked word is its finite-state coefficient times
one indicator for survival of all its vertices. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma wordVertexSite_closed {R : ℕ} (h : ℕ) (step : Fin R → SignedStep) (n : ℤ)
    (hclosed : wordDisplacement h (List.ofFn step) = 0) :
    wordVertexSite h step n (Fin.last R) = wordVertexSite h step n 0 := by
  simp [wordVertexSite, List.take_of_length_le (by simp : (List.ofFn step).length ≤ R), hclosed]

lemma closed_word_vertex_iff {R : ℕ} (hR : 0 < R) (h : ℕ)
    (step : Fin R → SignedStep) (n : ℤ)
    (hclosed : wordDisplacement h (List.ofFn step) = 0) (keep : ℤ → Prop) :
    (∀ i : Fin R, keep (wordVertexSite h step n i.castSucc)) ↔
      ∀ i : Fin (R + 1), keep (wordVertexSite h step n i) := by
  constructor
  · intro hi i
    by_cases hb : i.val < R
    · have he : (⟨i.val, hb⟩ : Fin R).castSucc = i := Fin.ext rfl
      simpa only [he] using hi ⟨i.val, hb⟩
    · have he : i = Fin.last R := Fin.ext (by simp only [Fin.val_last]; omega)
      rw [he, wordVertexSite_closed h step n hclosed]
      exact hi ⟨0, hR⟩
  · intro hi i
    exact hi i.castSucc

lemma closed_word_mask {R : ℕ} (hR : 0 < R) (h : ℕ)
    (step : Fin R → SignedStep) (n : ℤ)
    (hclosed : wordDisplacement h (List.ofFn step) = 0) (keep : ℤ → Prop) :
    scalarWalkProduct h (fun _ z => vertexIndicator keep z) n (List.ofFn step) =
      if ∀ i : Fin (R + 1), keep (wordVertexSite h step n i) then 1 else 0 := by
  rw [scalarWalkProduct_ofFn]
  change (∏ i : Fin R, vertexIndicator keep (wordVertexSite h step n i.castSucc)) = _
  by_cases hv : ∀ i : Fin R, keep (wordVertexSite h step n i.castSucc)
  · have hv' := (closed_word_vertex_iff hR h step n hclosed keep).mp hv
    simp [vertexIndicator, hv, hv']
  · have hv' : ¬∀ i : Fin (R + 1), keep (wordVertexSite h step n i) :=
      fun hh => hv ((closed_word_vertex_iff hR h step n hclosed keep).mpr hh)
    rw [if_neg hv']
    obtain ⟨i, hi⟩ := not_forall.mp hv
    exact prod_eq_zero (mem_univ i) (by simp [vertexIndicator, hi])

lemma closed_actual_word_state {J R m : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (Qp Q : Finset ℕ) (hQp : ∀ p ∈ Qp, p.Prime) (hQ : Q ⊆ retainedPrimeDivisors Qp)
    (e : Fin m ≃ Qp) (eligible : ℕ → ℕ → Prop) (L K : ℝ) (h : ℕ) (n : ℤ)
    (hR : 0 < R) (hclosed : wordDisplacement h (columnTupleWord w forward padding) = 0)
    (keep : ℤ → Prop) :
    let step := fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i)
    scalarWalkProduct h
      (maskedSignedIntegerWeight Q actualPaddingCoefficient eligible (actualPaddingVertex Qp)
        (fun d => centeredTuple d.primeFactors) L K (fun _ => actualPaddingDegreeCut Qp L) h keep)
      n (List.ofFn step) =
      if ∀ i : Fin (R + 1), keep (wordVertexSite h step n i) then
        actualWordCoefficient Qp Q e (fun t => eligible t.tuple) L K step (fun i j => (w j i).val)
          (fun i => paddingActiveState Qp e (wordVertexSite h step n i)) (wordCenteredBits w h step n)
      else 0 := by
  dsimp only
  rw [show maskedSignedIntegerWeight Q actualPaddingCoefficient eligible (actualPaddingVertex Qp)
      (fun d => centeredTuple d.primeFactors) L K (fun _ => actualPaddingDegreeCut Qp L) h keep =
      fun t z => vertexIndicator keep z *
        signedIntegerWeight Q actualPaddingCoefficient (eligible t.tuple) (actualPaddingVertex Qp)
          (centeredTuple t.tuple.primeFactors) L K (actualPaddingDegreeCut Qp L) h t z *
        vertexIndicator keep (z + t.displacement h) from rfl]
  rw [closed_masked_scalar_word hR h _ n hclosed _ _
    (fun z => by unfold vertexIndicator; split_ifs <;> simp)]
  rw [closed_signed_word_factorization Q actualPaddingCoefficient (fun t => eligible t.tuple)
    (actualPaddingVertex Qp) (fun t => centeredTuple t.tuple.primeFactors) L K
    (fun _ => actualPaddingDegreeCut Qp L) h n
    (List.ofFn (fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i)))
    (actualPaddingVertex_ne_zero Qp)
    (fun t q _ z => centeredTuple_padding_periodic t.tuple.primeFactors h t.tuple
      (fun p hp => (Nat.mem_primeFactors.mp hp).2.1) q z) hclosed]
  rw [← actualWordCoefficient_integer_identity w forward padding hprime hdisjoint Qp Q hQp hQ e]
  rw [closed_word_mask hR h _ n hclosed keep]
  split_ifs <;> simp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WordDegreeSupport
namespace OAI

/-! Endpoint degree cutoffs are already present in the exact coefficient
table. Restricting its state expansion introduces no extra deletion. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma paddingStateDeparture_degree_of_ne_zero {m : ℕ} (Qp Q : Finset ℕ)
    (e : Fin m ≃ Qp) (eligible : SignedStep → ℕ → Prop) (L K : ℝ) (t : SignedStep)
    (S T : Finset (Fin m)) (hn : paddingStateDeparture Qp Q e eligible L K t S T ≠ 0) :
    (S.card : ℝ) ≤ 400 * Real.log L ∧ (T.card : ℝ) ≤ 400 * Real.log L := by
  unfold paddingStateDeparture at hn
  split_ifs at hn with hh
  · exact ⟨hh.2.2.2.1.2, hh.2.2.2.2.2⟩
  · contradiction

lemma all_vertices_of_endpoint_pairs {R : ℕ} (hR : 0 < R)
    (P : Fin (R + 1) → Prop) (hP : ∀ i : Fin R, P i.castSucc ∧ P i.succ) :
    ∀ i, P i := by
  cases R with
  | zero => omega
  | succ R =>
    intro i
    by_cases hi : i.val < R + 1
    · have he : (⟨i.val, hi⟩ : Fin (R + 1)).castSucc = i := Fin.ext rfl
      simpa only [he] using (hP ⟨i.val, hi⟩).1
    · have he : (Fin.last R).succ = i := Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
      simpa only [he] using (hP (Fin.last R)).2

lemma actualWordCoefficient_degree_of_ne_zero {R J m : ℕ}
    (Qp Q : Finset ℕ) (e : Fin m ≃ Qp) (eligible : SignedStep → ℕ → Prop)
    (L K : ℝ) (step : Fin R → SignedStep) (p : Fin R → Fin J → ℕ)
    (S : Fin (R + 1) → Finset (Fin m)) (bits : BooleanCube (R * J))
    (hR : 0 < R) (hn : actualWordCoefficient Qp Q e eligible L K step p S bits ≠ 0) :
    ∀ i, ((S i).card : ℝ) ≤ 400 * Real.log L := by
  have hprod : (∏ i : Fin R, paddingStateDeparture Qp Q e eligible L K (step i)
      (S i.castSucc) (S i.succ)) ≠ 0 := (mul_ne_zero_iff.mp hn).1
  apply all_vertices_of_endpoint_pairs hR
  intro i
  apply paddingStateDeparture_degree_of_ne_zero Qp Q e eligible L K (step i)
  exact (prod_ne_zero_iff.mp hprod) i (mem_univ i)

lemma actualWordCoefficient_truncation {R J m : ℕ}
    (Qp Q : Finset ℕ) (e : Fin m ≃ Qp) (eligible : SignedStep → ℕ → Prop)
    (L K : ℝ) (step : Fin R → SignedStep) (p : Fin R → Fin J → ℕ)
    (S : Fin (R + 1) → Finset (Fin m)) (bits : BooleanCube (R * J))
    (hR : 0 < R) (hL : 1 ≤ L) :
    (if ∀ i, (S i).card ≤ ⌊400 * Real.log L⌋₊
      then actualWordCoefficient Qp Q e eligible L K step p S bits else 0) =
      actualWordCoefficient Qp Q e eligible L K step p S bits := by
  by_cases hn : actualWordCoefficient Qp Q e eligible L K step p S bits = 0
  · simp [hn]
  · have hcard := actualWordCoefficient_degree_of_ne_zero Qp Q e eligible L K step p S bits hR hn
    have hm : ∀ i, (S i).card ≤ ⌊400 * Real.log L⌋₊ := fun i =>
      (Nat.le_floor_iff (mul_nonneg (by norm_num) (Real.log_nonneg hL))).mpr (hcard i)
    exact if_pos hm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualWordBoolean
namespace OAI

/-! The actual closed scalar word is precisely the bounded-state Boolean
function to which weighted finite-interval comparison applies. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma actualWordBoolean_integer {h J M R m : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (s : ℕ) (Q : Finset ℕ)
    (hQ : Q ⊆ retainedPrimeDivisors data.Q) (e : Fin m ≃ data.Q)
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val)
    (eligible : ℕ → ℕ → Prop) (L K : ℝ) (hL : 1 ≤ L) (n : ℤ)
    (hR : 0 < R) (hclosed : wordDisplacement h (columnTupleWord w forward padding) = 0) :
    let step := fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i)
    actualWordBoolean data s Q e step (fun i j => (w j i).val) eligible L K
      (actualWordIntegerBits data s e step label n) =
    scalarWalkProduct h
      (maskedSignedIntegerWeight Q actualPaddingCoefficient eligible (actualPaddingVertex data.Q)
        (fun d => centeredTuple d.primeFactors) L K (fun _ => actualPaddingDegreeCut data.Q L)
        h (fun z => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) z))
      n (List.ofFn step) := by
  dsimp only
  let step := fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i)
  let x := actualWordIntegerBits data s e step label n
  have hS (r : Fin (R + 1)) :
      activeState (fun i => x (actualWordQIndex data s R m r i)) =
        paddingActiveState data.Q e (wordVertexSite h step n r) := by
    unfold paddingActiveState
    congr 1
    funext i
    exact actualWordQIndex_eval data s e step label n r i
  have hbits : (fun k => x (actualWordPIndex data s R m k)) = wordCenteredBits w h step n :=
    funext (actualWordPIndex_eval data s e w step label hlabel n)
  have hmask : (prohibitedWordKeepCircuit data.pairs h s
      (actualWordBadIndex data s R m)).eval x = true ↔
      ∀ r, ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (wordVertexSite h step n r) :=
    prohibitedWordKeepCircuit_eval data.pairs h s data.whole_squarefree _ _ x
      (actualWordBadIndex_eval data s e step label n)
  rw [closed_actual_word_state w forward padding hprime hdisjoint data.Q Q
    data.primeQ hQ e eligible L K h n hR hclosed]
  change actualWordBoolean data s Q e step (fun i j => (w j i).val) eligible L K x = _
  simp only [actualWordBoolean, hS, hbits, hmask]
  let S := fun r => paddingActiveState data.Q e (wordVertexSite h step n r)
  let coeff := actualWordCoefficient data.Q Q e (fun t => eligible t.tuple) L K step
    (fun i j => (w j i).val) S (wordCenteredBits w h step n)
  have ht : (if ∀ r, (S r).card ≤ ⌊400 * Real.log L⌋₊ then coeff else 0) = coeff :=
    actualWordCoefficient_truncation data.Q Q e (fun t => eligible t.tuple) L K step
      (fun i j => (w j i).val) S _ hR hL
  dsimp only [S, coeff, step] at ht ⊢
  by_cases hm : ∀ r, ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs)
      (wordVertexSite h (fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i)) n r)
  · simpa [hm] using ht
  · simp [hm]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualWordComparison
namespace OAI

/-! The actual signed closed word has the finite-origin error required
by the matrix trace argument. Only the published Braverman input is
used for this transfer; the residue expectation is unchanged. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

local instance wordPrime_neZero {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (i : Fin (Fintype.card ↥(data.P ∪ data.Q))) :
    NeZero (primeResidueModuli (data.P ∪ data.Q) i) :=
  ⟨(primeResidueModuli_prime _ (fun p hp => data.prime ⟨p, hp⟩) i).ne_zero⟩

lemma ProhibitedPrimeFamily.pair_primeFactors_card {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (dq : ℕ × ℕ) (hdq : dq ∈ data.pairs) :
    (dq.2 * dq.1).primeFactors.card ≤ J + M := by
  rw [Nat.primeFactors_mul (data.padding_squarefree _ hdq).ne_zero
    (data.tuple_squarefree _ hdq).ne_zero]
  have hh := card_union_le dq.2.primeFactors dq.1.primeFactors
  rw [data.tuple_card _ hdq] at hh
  have hq := data.padding_card _ hdq
  omega


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualAffineWordComparison
namespace OAI

/-! The concrete signed masked word on a fixed arithmetic progression
of origins, preserving the original residue-model expectation. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

local instance affineWordPrime_neZero {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (i : Fin (Fintype.card ↥(data.P ∪ data.Q))) :
    NeZero (primeResidueModuli (data.P ∪ data.Q) i) :=
  ⟨(primeResidueModuli_prime _ (fun p hp => data.prime ⟨p, hp⟩) i).ne_zero⟩

theorem BravermanDepth22Input.eventually_actual_affine_word_comparison (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M R s B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      (s : ℝ) ≤ L → ((J + M : ℕ) : ℝ) ≤ L ^ 2 →
      (data.pairs.card : ℝ) ≤ Real.exp (101 * L) →
      0 < R → ((R + 1 : ℕ) : ℝ) ≤ 4 * L → ((R * J : ℕ) : ℝ) ≤ L ^ 2 →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      ∀ (P : Fin J → Finset ℕ)
        (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (padding : Fin R → ℕ),
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      (∀ i, ((padding i).primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (label : Fin R × Fin J → ↥(data.P ∪ data.Q)),
      (∀ i j, (label (i, j)).val = (w j i).val) →
      wordDisplacement h (columnTupleWord w forward padding) = 0 →
      ∀ (eligible : ℕ → ℕ → Prop) (K : ℝ) (a l N : ℕ),
      (∀ p ∈ data.P ∪ data.Q, l.Coprime p) → Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient eligible
        (actualPaddingVertex data.Q) (fun d => centeredTuple d.primeFactors) L K
        (fun _ => actualPaddingDegreeCut data.Q L) h
        (fun z => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) z)
      |uniformAverage (fun x : Fin N => scalarWalkProduct h weight (a + l * x.val)
          (columnTupleWord w forward padding)) -
        (data.residueLaw B hB).average (fun r => scalarWalkProduct h weight (data.residueOrigin r)
          (columnTupleWord w forward padding))| ≤ Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hcomp⟩ := hBr.eventually_affine_weighted_word_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hcomp, eventually_ge_atTop (4800 : ℝ)] with L hcomp hL
  intro h J M R s B data hB hpool hBL hs hJM hpairs hR hRL hRJ Q hQ P w forward padding
    hprime hdisjoint hdeg label hlabel hclosed eligible K a l N hl hN
  let m := Fintype.card ↥data.Q
  let e : Fin m ≃ data.Q := (Fintype.equivFin ↥data.Q).symm
  let primes := data.P ∪ data.Q
  let modulus := primeResidueModuli primes
  let (i : Fin (Fintype.card primes)) : NeZero (modulus i) :=
    ⟨(primeResidueModuli_prime primes (fun p hp => data.prime ⟨p, hp⟩) i).ne_zero⟩
  let step := fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i)
  let literal := actualWordLiterals data s e step label
  let F := fun z : ∀ i, ZMod (modulus i) => actualWordBoolean data s Q e step
    (fun i j => (w j i).val) eligible L K
    (residueCircuitInputs modulus (primeLiteralCoordinate primes literal) (primeLiteralTest primes literal) z)
  have hp : ∀ p ∈ primes, p.Prime := fun p hp => data.prime ⟨p, hp⟩
  have hcard : (Fintype.card primes : ℝ) ≤ Real.exp L := by
    have hb := primePool_card_bound primes hp B hB
    have hb' : (primes.card : ℝ) ≤ B := by exact_mod_cast hb
    simpa only [Fintype.card_coe] using hb'.trans hBL
  have hm : (m : ℝ) ≤ Real.exp L := by
    have he : m = data.Q.card := by simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_congr e
    rw [he]
    have hq : (data.Q.card : ℝ) ≤ primes.card := by
      exact_mod_cast card_le_card (subset_union_right : data.Q ⊆ primes)
    exact hq.trans (by simpa only [Fintype.card_coe] using hcard)
  have hpzero : 0 < Fintype.card primes := by
    simpa only [Fintype.card_coe] using card_pos.mpr hpool
  have hmod : ∀ i, (modulus i : ℝ) ≤ Real.exp L := by
    intro i
    exact primeResidueModuli_bound primes (Real.exp L)
      (fun p hp => (show (p : ℝ) ≤ B by exact_mod_cast hB p hp).trans hBL) i
  have hR' : (R : ℝ) ≤ 4 * L := by push_cast at hRL; linarith
  have hsize := prohibitedWordKeepCircuit_size_budget data.pairs h s (J + M)
    (actualWordBadIndex data s R m) L (by linarith) hRL hs hJM hpairs
    (data.pair_primeFactors_card)
  have hc := hcomp (Fintype.card primes) modulus hpzero (by linarith)
    (primeResidueModuli_coprime primes hp) hmod (R + 1) m (R * J) _ ⌊400 * Real.log L⌋₊
    hm (Nat.floor_le (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))) hRL hRJ
    (primeLiteralCoordinate primes literal) (primeLiteralTest primes literal)
    (actualWordQIndex data s R m) (actualWordPIndex data s R m)
    (actualWordCoefficient data.Q Q e (fun t => eligible t.tuple) L K step (fun i j => (w j i).val))
    (prohibitedWordKeepCircuit data.pairs h s (actualWordBadIndex data s R m))
    (fun b => actualWordCoefficient_budget data.Q Q e (fun t => eligible t.tuple) L K step _
      (fun i j => hprime j _ (w j i).property) hL hR' hdeg _ _)
    ((prohibitedWordKeepCircuit_depth data.pairs h s _).trans (by norm_num)) hsize a l N (fun i => hl _ ((Fintype.equivFin primes).symm i).property) hN
  change |uniformAverage (fun x : Fin N => F (fun i => (a + l * x.val : ZMod (modulus i)))) -
    uniformAverage F| ≤ Real.exp (-(L ^ 9)) at hc
  let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient eligible
    (actualPaddingVertex data.Q) (fun d => centeredTuple d.primeFactors) L K
    (fun _ => actualPaddingDegreeCut data.Q L) h
    (fun z => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) z)
  have hF (n : ℤ) : F (fun i => (n : ZMod (modulus i))) =
      scalarWalkProduct h weight n (columnTupleWord w forward padding) :=
    actualWordBoolean_integer data s Q hQ e w forward padding hprime hdisjoint label hlabel
      eligible L K (by linarith) n hR hclosed
  have hmodel : (data.residueLaw B hB).average (fun r =>
      scalarWalkProduct h weight (data.residueOrigin r) (columnTupleWord w forward padding)) =
      uniformAverage F := by
    rw [← data.residue_average_canonical hB F]
    apply congrArg (data.residueLaw B hB).average
    funext r
    rw [← hF, data.canonical_origin]
  dsimp only
  rw [hmodel]
  have hsample : (fun x : Fin N => scalarWalkProduct h weight (a + l * x.val)
      (columnTupleWord w forward padding)) =
      (fun x : Fin N => F (fun i => (a + l * x.val : ZMod (modulus i)))) := by
    funext x
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_add, Nat.cast_mul] using
      (hF (a + l * x.val)).symm
  rw [hsample]
  exact hc

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_actual_affine_word_comparison := @OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_actual_affine_word_comparison
