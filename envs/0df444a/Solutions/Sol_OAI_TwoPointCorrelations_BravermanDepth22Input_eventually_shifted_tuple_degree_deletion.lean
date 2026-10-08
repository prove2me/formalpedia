-- Prove2me | solution 1 for OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_shifted_tuple_degree_deletion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:48:25.294979+00:00
-- url     : https://prove2.me/submissions/b251099b-1c5f-434a-ad0c-8a79a5178d9f

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_BravermanDepth22Input_eventually_positive_weight_comparison
import Theorems.Thm_OAI_TwoPointCorrelations_ProhibitedPrimeFamily_positive_divisor_degree_cost

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DegreeThresholdCircuit
namespace OAI

/-! The literal degree cutoffs are depth-two monotone circuits: a large
active set contains a subset of the prescribed size. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace AC0Circuit


lemma disjunction_eval {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) (x : BooleanCube n) :
    (disjunction c).eval x = true ↔ ∃ i, (c i).eval x = true := by
  simp only [disjunction, eval, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨_, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨(Fintype.equivFin ι) i, by simpa only [Equiv.symm_apply_apply] using hi⟩

lemma disjunction_depth {ι : Type*} [Fintype ι] {n d : ℕ}
    (c : ι → AC0Circuit n) (hc : ∀ i, (c i).depth ≤ d) :
    (disjunction c).depth ≤ d + 1 := by
  simp only [disjunction, depth]
  have hh : (univ.sup fun i : Fin (Fintype.card ι) =>
      (c ((Fintype.equivFin ι).symm i)).depth) ≤ d :=
    Finset.sup_le (fun i _ => hc _)
  omega

lemma disjunction_size {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) : (disjunction c).size = 1 + ∑ i, (c i).size := by
  simp only [disjunction, size]
  congr 1
  exact (Fintype.equivFin ι).symm.sum_comp (fun i => (c i).size)

end AC0Circuit


lemma degreeSubsetCircuit_eval {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    (degreeSubsetCircuit S).eval x = true ↔ S ⊆ activeState x := by
  rw [degreeSubsetCircuit, AC0Circuit.conjunction_eval]
  simp only [AC0Circuit.eval, ite_true]
  constructor
  · intro h i hi
    exact mem_filter.mpr ⟨mem_univ i, h ⟨i, hi⟩⟩
  · intro h i
    exact (mem_filter.mp (h i.property)).2

lemma degreeSubsetCircuit_depth {n : ℕ} (S : Finset (Fin n)) :
    (degreeSubsetCircuit S).depth ≤ 1 :=
  AC0Circuit.conjunction_depth _ (fun _ => Nat.le_refl 0)

lemma degreeSubsetCircuit_size {n : ℕ} (S : Finset (Fin n)) :
    (degreeSubsetCircuit S).size = 1 + S.card := by
  simp [degreeSubsetCircuit, AC0Circuit.conjunction_size, AC0Circuit.size]


lemma degreeThresholdCircuit_eval (n r : ℕ) (x : BooleanCube n) :
    (degreeThresholdCircuit n r).eval x = true ↔ r ≤ (activeState x).card := by
  rw [degreeThresholdCircuit, AC0Circuit.disjunction_eval]
  constructor
  · rintro ⟨S, hS⟩
    have hsub := (degreeSubsetCircuit_eval S.val x).mp hS
    have hcard := (mem_powersetCard.mp S.property).2
    exact hcard ▸ card_le_card hsub
  · intro hr
    obtain ⟨S, hsub, hcard⟩ := exists_subset_card_eq hr
    refine ⟨⟨S, mem_powersetCard.mpr ⟨subset_univ S, hcard⟩⟩, ?_⟩
    exact (degreeSubsetCircuit_eval S x).mpr hsub

lemma degreeThresholdCircuit_depth (n r : ℕ) :
    (degreeThresholdCircuit n r).depth ≤ 2 :=
  AC0Circuit.disjunction_depth _ (fun S => degreeSubsetCircuit_depth S.val)

lemma degreeThresholdCircuit_size (n r : ℕ) :
    (degreeThresholdCircuit n r).size = 1 + n.choose r * (r + 1) := by
  rw [degreeThresholdCircuit, AC0Circuit.disjunction_size]
  have hs (S : (univ : Finset (Fin n)).powersetCard r) :
      (degreeSubsetCircuit S.val).size = r + 1 := by
    rw [degreeSubsetCircuit_size, (mem_powersetCard.mp S.property).2]
    omega
  simp only [hs, sum_const, card_univ, Fintype.card_coe, card_powersetCard,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]

lemma degreeThresholdCircuit_size_le (n r : ℕ) :
    (degreeThresholdCircuit n r).size ≤ 1 + (r + 1) * (n + 1) ^ r := by
  rw [degreeThresholdCircuit_size]
  have hb : n.choose r ≤ (n + 1) ^ r :=
    (Nat.choose_le_pow n r).trans (Nat.pow_le_pow_left (Nat.le_succ n) r)
  simpa only [Nat.mul_comm] using Nat.add_le_add_left
    (Nat.mul_le_mul_right (r + 1) hb) 1



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


lemma primeSubset_product_injective (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    Set.InjOn (fun U : Finset ℕ => ∏ p ∈ U, p) S.powerset := by
  intro U hU V hV heq
  have hU' : U ⊆ S := mem_powerset.mp hU
  have hV' : V ⊆ S := mem_powerset.mp hV
  have hprimeU : ∀ p ∈ U, Nat.Prime p := fun p hp => hS p (hU' hp)
  have hprimeV : ∀ p ∈ V, Nat.Prime p := fun p hp => hS p (hV' hp)
  have hfactors := congrArg Nat.primeFactors heq
  simpa only [Nat.primeFactors_prod hprimeU, Nat.primeFactors_prod hprimeV] using hfactors




theorem retainedPrimeDivisors_weighted_mass (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (w : ℕ → ℝ) :
    (∑ u ∈ retainedPrimeDivisors S, (∏ p ∈ u.primeFactors, w p) / (u : ℝ)) =
      ∏ p ∈ S, (1 + w p / (p : ℝ)) := by
  unfold retainedPrimeDivisors
  rw [sum_image (primeSubset_product_injective S hS)]
  calc
    _ = ∑ U ∈ S.powerset, ∏ p ∈ U, (w p / (p : ℝ)) := by
      apply sum_congr rfl
      intro U hU
      have hUS : U ⊆ S := mem_powerset.mp hU
      rw [Nat.primeFactors_prod (fun p hp => hS p (hUS hp)), Nat.cast_prod,
        prod_div_distrib]
    _ = _ := (prod_one_add S).symm

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







lemma paddingTiltNormalizer_eq_divisor_sum (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) :
    paddingTiltNormalizer Q =
      ∑ q ∈ retainedPrimeDivisors Q, (4 : ℝ) ^ q.primeFactors.card / (q : ℝ) := by
  unfold paddingTiltNormalizer
  rw [prod_coe_sort Q (fun p : ℕ => 1 + 4 / (p : ℝ))]
  simpa only [prod_const] using
    (retainedPrimeDivisors_weighted_mass Q hQ (fun _ => (4 : ℝ))).symm


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

lemma paddingBin_eq_iff (η c x : ℝ) (j : ℤ) (hη : 0 < η) :
    paddingBin η c x = j ↔ (j : ℝ) * η ≤ x + c ∧ x + c < ((j : ℝ) + 1) * η := by
  rw [paddingBin, Int.floor_eq_iff, le_div_iff₀ hη, div_lt_iff₀ hη]

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


lemma primeTupleDivisors_mass {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    (∑ d ∈ primeTupleDivisors P, 1 / (d : ℝ)) =
      ∏ j, ∑ p ∈ P j, 1 / (p : ℝ) := by
  rw [primeTupleDivisors, sum_image]
  · calc
      _ = ∑ x : (j : Fin J) → P j, ∏ j, 1 / ((x j).val : ℝ) := by
        apply sum_congr rfl
        intro x _
        simp only [Nat.cast_prod, one_div, prod_inv_distrib]
      _ = ∏ j, ∑ p : P j, 1 / (p.val : ℝ) :=
        (Fintype.prod_sum (fun j (p : P j) => 1 / (p.val : ℝ))).symm
      _ = _ := by
        apply prod_congr rfl
        intro j _
        exact sum_coe_sort (P j) (fun p : ℕ => 1 / (p : ℝ))
  · intro x _ y _ hxy
    exact primeTuple_injective hprime hdisjoint hxy





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeTuplePool
namespace OAI

/-! Arithmetic support of the actual one-prime-per-band tuple family. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma primeHarmonicMass_eq_sum (S : Finset ℕ) :
    primeHarmonicMass S = ∑ p ∈ S, 1 / (p : ℝ) := by
  unfold primeHarmonicMass
  simpa only [one_div] using sum_coe_sort S (fun p : ℕ => 1 / (p : ℝ))


lemma primeTuplePool_mass {J : ℕ} (P : Fin J → Finset ℕ)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    primeHarmonicMass (primeTuplePool P) = ∑ j, primeHarmonicMass (P j) := by
  simp only [primeHarmonicMass_eq_sum, primeTuplePool]
  apply sum_biUnion
  intro j _ l _ hne
  exact hdisjoint j l (Ne.symm hne)






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






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeDegreeCircuit
namespace OAI

/-! Literal degree deletion together with divisibility by a fixed
padding divisor. All tests use the common prime coordinates. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma primeSubsetIndex_value (U S : Finset ℕ) (hS : S ⊆ U)
    (i : Fin (Fintype.card S)) :
    ((Fintype.equivFin U).symm (primeSubsetIndex U S hS i)).val =
      ((Fintype.equivFin S).symm i).val := by
  simp only [primeSubsetIndex, Equiv.symm_apply_apply]


lemma primeSubsetIndex_bits (U S : Finset ℕ) (hS : S ⊆ U) (n : ℤ) :
    (fun i => primeSiteBits U n (primeSubsetIndex U S hS i)) = primeSiteBits S n := by
  funext i
  simp only [primeSiteBits, primeSubsetIndex_value]

lemma primeSiteBits_card (U : Finset ℕ) (n : ℤ) :
    (activeState (primeSiteBits U n)).card = actualPaddingDegree U n :=
  paddingActiveState_card U (Fintype.equivFin U).symm n


lemma degreeDivisorCircuit_eval {m n t : ℕ}
    (pindex : Fin n → Fin m) (qindex : Fin t → Fin m) (r : ℕ)
    (x : BooleanCube m) :
    (degreeDivisorCircuit pindex qindex r).eval x = true ↔
      (∀ i, x (qindex i) = true) ∧ r ≤ (activeState (fun i => x (pindex i))).card := by
  rw [degreeDivisorCircuit, AC0Circuit.conjunction_eval]
  simp only [Bool.forall_bool, Bool.false_eq_true, ite_false, ite_true,
    AC0Circuit.relabel_eval, degreeThresholdCircuit_eval, degreeSubsetCircuit_eval]
  have he : (univ : Finset (Fin t)) ⊆ activeState (fun i => x (qindex i)) ↔
      ∀ i, x (qindex i) = true := by
    simp only [subset_iff, mem_univ, activeState, mem_filter, true_and, forall_const]
  rw [he]

lemma degreeDivisorCircuit_depth {m n t : ℕ}
    (pindex : Fin n → Fin m) (qindex : Fin t → Fin m) (r : ℕ) :
    (degreeDivisorCircuit pindex qindex r).depth ≤ 3 := by
  apply AC0Circuit.conjunction_depth
  intro b
  cases b
  · exact (AC0Circuit.relabel_depth _ _).trans ((degreeSubsetCircuit_depth _).trans (by omega))
  · exact (AC0Circuit.relabel_depth _ _).trans (degreeThresholdCircuit_depth _ _)

lemma degreeDivisorCircuit_size {m n t : ℕ}
    (pindex : Fin n → Fin m) (qindex : Fin t → Fin m) (r : ℕ) :
    (degreeDivisorCircuit pindex qindex r).size ≤
      3 + t + (r + 1) * (n + 1) ^ r := by
  rw [degreeDivisorCircuit, AC0Circuit.conjunction_size]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
  have hq := AC0Circuit.relabel_size qindex (degreeSubsetCircuit (univ : Finset (Fin t)))
  have hp := AC0Circuit.relabel_size pindex (degreeThresholdCircuit n r)
  have hd := degreeThresholdCircuit_size_le n r
  simp only [degreeSubsetCircuit_size, card_univ, Fintype.card_fin] at hq
  omega

lemma degreeDivisorCircuit_size_exp {m n t : ℕ}
    (pindex : Fin n → Fin m) (qindex : Fin t → Fin m) (r : ℕ) (L : ℝ)
    (hL : 4800 ≤ L) (hn : (n : ℝ) ≤ Real.exp L)
    (ht : (t : ℝ) ≤ 100 * Real.log L) (hr : (r : ℝ) ≤ 400 * Real.log L + 1) :
    ((degreeDivisorCircuit pindex qindex r).size : ℝ) ≤ Real.exp (L ^ 3) := by
  have hL0 : 0 ≤ L := by linarith
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hrL : (r : ℝ) ≤ 401 * L := by nlinarith
  have htwo : (2 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hn' : (n : ℝ) + 1 ≤ Real.exp (2 * L) := by
    rw [show 2 * L = L + L by ring, Real.exp_add]
    nlinarith
  have hprod : ((r : ℝ) + 1) * ((n : ℝ) + 1) ^ r ≤
      Real.exp (1203 * L ^ 2) := by
    calc
      _ ≤ Real.exp (r : ℝ) * (Real.exp (2 * L)) ^ r :=
        mul_le_mul (Real.add_one_le_exp (r : ℝ))
          (pow_le_pow_left₀ (by positivity) hn' r) (by positivity) (by positivity)
      _ = Real.exp ((r : ℝ) * (1 + 2 * L)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hm := mul_le_mul_of_nonneg_right hrL (show 0 ≤ 1 + 2 * L by positivity)
        have hs := mul_nonneg hL0 (show 0 ≤ L - 1 by linarith)
        nlinarith)
  have hsmall : 3 + (t : ℝ) ≤ Real.exp (1203 * L ^ 2) := by
    have he := Real.add_one_le_exp (1203 * L ^ 2)
    nlinarith [sq_nonneg (L - 1)]
  have hc : ((degreeDivisorCircuit pindex qindex r).size : ℝ) ≤
      3 + t + ((r : ℝ) + 1) * ((n : ℝ) + 1) ^ r := by
    exact_mod_cast degreeDivisorCircuit_size pindex qindex r
  calc
    _ ≤ 2 * Real.exp (1203 * L ^ 2) := by linarith
    _ ≤ Real.exp (1 + 1203 * L ^ 2) := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hsq : (1 : ℝ) ≤ L ^ 2 := by nlinarith
      have hh := mul_nonneg (sq_nonneg L) (show 0 ≤ L - 1204 by linarith)
      nlinarith)

lemma prime_divisor_all_bits (U Q : Finset ℕ) (hQU : Q ⊆ U)
    (hQ : ∀ p ∈ Q, p.Prime) (q : ℕ) (hq : q ∈ retainedPrimeDivisors Q) (n : ℤ) :
    (∀ i : Fin (Fintype.card q.primeFactors),
      primeSiteBits U n (primeSubsetIndex U q.primeFactors
        ((retainedPrimeDivisor_factors Q hQ hq).trans hQU) i) = true) ↔
      (q : ℤ) ∣ n := by
  rw [← padding_literal_support_iff_dvd Q hQ n q hq, paddingAvailablePrimes_integer]
  constructor
  · intro hb p hp
    let i := (Fintype.equivFin q.primeFactors) ⟨p, hp⟩
    have hi := hb i
    simp only [primeSiteBits, primeSubsetIndex_value, i, Equiv.symm_apply_apply,
      decide_eq_true_eq] at hi
    exact mem_filter.mpr ⟨retainedPrimeDivisor_factors Q hQ hq hp, hi⟩
  · intro hb i
    have hh := hb ((Fintype.equivFin q.primeFactors).symm i).property
    simpa only [primeSiteBits, primeSubsetIndex_value, decide_eq_true_eq] using (mem_filter.mp hh).2

lemma degreeDivisorCircuit_integer (U P Q : Finset ℕ) (hPU : P ⊆ U)
    (hQU : Q ⊆ U) (hQ : ∀ p ∈ Q, p.Prime) (q : ℕ)
    (hq : q ∈ retainedPrimeDivisors Q) (T : ℝ) (hT : 0 ≤ T) (n : ℤ) :
    (degreeDivisorCircuit (primeSubsetIndex U P hPU)
      (primeSubsetIndex U q.primeFactors ((retainedPrimeDivisor_factors Q hQ hq).trans hQU))
      (⌊T⌋₊ + 1)).eval (primeSiteBits U n) = true ↔
        (q : ℤ) ∣ n ∧ T < (actualPaddingDegree P n : ℝ) := by
  rw [degreeDivisorCircuit_eval, prime_divisor_all_bits U Q hQU hQ q hq n,
    primeSubsetIndex_bits, primeSiteBits_card, ← Nat.lt_iff_add_one_le, Nat.floor_lt hT]

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









lemma positivePrimeNormalizer_squarefree (d : ℕ) (hd : Squarefree d) :
    positivePrimeNormalizer d.primeFactors = (2 : ℝ) ^ d.primeFactors.card / d := by
  unfold positivePrimeNormalizer
  rw [prod_div_distrib, prod_const]
  congr 1
  rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]


namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)





end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PositiveWeightComparison
namespace OAI

/-! Finite-interval comparison for the positive tuple majorant used in
deletion costs. The selected-prime values are kept in one bounded
coefficient table; no subset expansion is needed. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical





lemma positivePrimeTable_actual {t : ℕ} (S : Finset ℕ) (e : Fin t ≃ S)
    (r : ℕ) (n : ℤ) :
    positivePrimeTable (fun i => (e i).val) r (fun i => decide (((e i).val : ℤ) ∣ n)) =
      (4 : ℝ) ^ r * positivePrimeWeight S n := by
  unfold positivePrimeTable positivePrimeWeight
  simp only [decide_eq_true_eq]
  congr 1
  rw [← prod_coe_sort S (fun p : ℕ => (if (p : ℤ) ∣ n then (1 : ℝ) else 0) + 1 / (p : ℝ))]
  exact e.prod_comp (fun p : S =>
    (if (p.val : ℤ) ∣ n then (1 : ℝ) else 0) + 1 / (p.val : ℝ))


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PositivePrimeCostComparison
namespace OAI

/-! Actual integer-origin transfer of one positive deletion cost. The
event is represented by its literal prime-residue circuit, and the
comparison uses the same CRT law as the graph estimates. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem BravermanDepth22Input.eventually_positive_prime_cost_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (S : Finset ℕ), S ⊆ data.P ∪ data.Q → (S.card : ℝ) ≤ L ^ 2 →
      ∀ (r ninput : ℕ), (r : ℝ) ≤ 100 * Real.log L →
      ∀ (literal : Fin ninput → ↥(data.P ∪ data.Q) × ℤ)
        (index : Fin (Fintype.card S) → Fin ninput) (site : ℤ),
      (∀ i, (literal (index i)).1.val = ((Fintype.equivFin S).symm i).val ∧
        (literal (index i)).2 = site) →
      ∀ (c : AC0Circuit ninput), c.depth ≤ 19 → (c.size : ℝ) ≤ Real.exp (L ^ 3) →
      ∀ (bad : ℤ → Prop),
      (∀ n, c.eval (fun i => decide (((literal i).1.val : ℤ) ∣ n + (literal i).2)) = true ↔
        bad n) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let F := fun n : ℤ => (4 : ℝ) ^ r * positivePrimeWeight S (n + site) *
        if bad n then 1 else 0
      |uniformAverage (fun x : Fin N => F (a + x.val)) -
        (data.residueLaw B hB).average (fun x => F (data.residueOrigin x))| ≤
          Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_positive_weight_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hb
  intro h J M B data hB hpool hBL S hS hSL r ninput hr literal index site hindex
    c hc hsize bad hbad a N hN
  let primes := data.P ∪ data.Q
  let modulus := primeResidueModuli primes
  let (i : Fin (Fintype.card primes)) : NeZero (modulus i) :=
    ⟨(primeResidueModuli_prime primes (fun p hp => data.prime ⟨p, hp⟩) i).ne_zero⟩
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let p : Fin (Fintype.card S) → ℕ := fun i => (e i).val
  let F := fun z : ∀ i, ZMod (modulus i) =>
    let bits := residueCircuitInputs modulus (primeLiteralCoordinate primes literal)
      (primeLiteralTest primes literal) z
    positivePrimeTable p r (fun i => bits (index i)) * c.indicator bits
  let cost := fun n : ℤ => (4 : ℝ) ^ r * positivePrimeWeight S (n + site) *
    if bad n then 1 else 0
  have hp (i : Fin (Fintype.card S)) : 1 ≤ p i :=
    (data.prime ⟨p i, hS (e i).property⟩).one_lt.le
  have hcard : (Fintype.card primes : ℝ) ≤ Real.exp L := by
    have hh := primePool_card_bound primes (fun p hp => data.prime ⟨p, hp⟩) B hB
    have hh' : (primes.card : ℝ) ≤ B := by exact_mod_cast hh
    simpa only [Fintype.card_coe] using hh'.trans hBL
  have hm : 0 < Fintype.card primes := by
    simpa only [Fintype.card_coe] using card_pos.mpr hpool
  have hmod (i : Fin (Fintype.card primes)) : (modulus i : ℝ) ≤ Real.exp L :=
    primeResidueModuli_bound primes (Real.exp L)
      (fun p hp => (show (p : ℝ) ≤ B by exact_mod_cast hB p hp).trans hBL) i
  have hh := hb (Fintype.card primes) modulus hm (by linarith)
    (primeResidueModuli_coprime primes (fun p hp => data.prime ⟨p, hp⟩)) hmod
    (Fintype.card S) r ninput p hp (by simpa only [Fintype.card_coe] using hSL) hr
    (primeLiteralCoordinate primes literal) (primeLiteralTest primes literal) index c
    hc hsize a N hN
  change |uniformAverage (fun x : Fin N => F (fun i => (a + x.val : ZMod (modulus i)))) -
    uniformAverage F| ≤ Real.exp (-(L ^ 9)) at hh
  have hF (n : ℤ) : F (fun i => (n : ZMod (modulus i))) = cost n := by
    let bits := residueCircuitInputs modulus (primeLiteralCoordinate primes literal)
      (primeLiteralTest primes literal) (fun i => (n : ZMod (modulus i)))
    have hall : bits = fun i => decide (((literal i).1.val : ℤ) ∣ n + (literal i).2) := by
      funext i
      exact primeLiteral_integer_input primes literal n i
    have hbits (i : Fin (Fintype.card S)) : bits (index i) =
        decide ((p i : ℤ) ∣ n + site) := by
      rw [hall]
      simp only [(hindex i).1, (hindex i).2, p, e]
    have hgate : c.indicator bits = if bad n then 1 else 0 := by
      have heval : c.eval bits = true ↔ bad n := by
        simpa only [hall] using hbad n
      simp only [AC0Circuit.indicator, heval]
    change positivePrimeTable p r (fun i => bits (index i)) * c.indicator bits = cost n
    simp only [hbits, hgate]
    rw [positivePrimeTable_actual S e r (n + site)]
  have hmodel : (data.residueLaw B hB).average (fun x => cost (data.residueOrigin x)) =
      uniformAverage F := by
    rw [← data.residue_average_canonical hB F]
    apply congrArg (data.residueLaw B hB).average
    funext x
    rw [← hF, data.canonical_origin]
  dsimp only
  rw [hmodel]
  have hsample : (fun x : Fin N => cost (a + x.val)) =
      (fun x : Fin N => F (fun i => (a + x.val : ZMod (modulus i)))) := by
    funext x
    simpa only [Int.cast_add, Int.cast_natCast, Nat.cast_add] using (hF (a + x.val)).symm
  rw [hsample]
  exact hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DegreeCostComparison
namespace OAI

/-! Finite-interval transfer of the literal prime-degree deletion.
The padding-divisor indicator is kept, so its reciprocal saving is
available in the residue-model bound. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem BravermanDepth22Input.eventually_degree_cost_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (S V : Finset ℕ), S ⊆ data.P ∪ data.Q → V ⊆ data.P ∪ data.Q →
      (S.card : ℝ) ≤ L ^ 2 →
      ∀ (q : ℕ), q ∈ retainedPrimeDivisors data.Q →
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L →
      ∀ (T : ℝ), 0 ≤ T → T ≤ 400 * Real.log L →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let F := fun n : ℤ => actualPaddingCoefficient q * positivePrimeWeight S (n + site) *
        if (q : ℤ) ∣ n + site ∧ T < (actualPaddingDegree V (n + site) : ℝ) then 1 else 0
      |uniformAverage (fun x : Fin N => F (a + x.val)) -
        (data.residueLaw B hB).average (fun x => F (data.residueOrigin x))| ≤
          Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_positive_prime_cost_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (4800 : ℝ)] with L hb hL
  intro h J M B data hB hpool hBL S V hS hV hSL q hq hqdegree T hT hTL site a N hN
  let U := data.P ∪ data.Q
  let hQU : data.Q ⊆ U := subset_union_right
  let literal : Fin (Fintype.card U) → U × ℤ :=
    fun i => ((Fintype.equivFin U).symm i, site)
  let index := primeSubsetIndex U S hS
  let pindex := primeSubsetIndex U V hV
  let qindex := primeSubsetIndex U q.primeFactors
    ((retainedPrimeDivisor_factors data.Q data.primeQ hq).trans hQU)
  let c := degreeDivisorCircuit pindex qindex (⌊T⌋₊ + 1)
  let bad := fun n : ℤ => (q : ℤ) ∣ n + site ∧
    T < (actualPaddingDegree V (n + site) : ℝ)
  have hindex (i : Fin (Fintype.card S)) :
      (literal (index i)).1.val = ((Fintype.equivFin S).symm i).val ∧
        (literal (index i)).2 = site :=
    ⟨primeSubsetIndex_value U S hS i, rfl⟩
  have hVcard : (Fintype.card V : ℝ) ≤ Real.exp L := by
    have hbound : V.card ≤ B := (card_le_card hV).trans
      (primePool_card_bound U (fun p hp => data.prime ⟨p, hp⟩) B hB)
    have hbound' : (V.card : ℝ) ≤ B := by exact_mod_cast hbound
    simpa only [Fintype.card_coe] using hbound'.trans hBL
  have hqcard : (Fintype.card q.primeFactors : ℝ) ≤ 100 * Real.log L := by
    simpa only [Fintype.card_coe] using hqdegree
  have hfloor : ((⌊T⌋₊ + 1 : ℕ) : ℝ) ≤ 400 * Real.log L + 1 := by
    push_cast
    linarith [Nat.floor_le hT]
  have hsize : (c.size : ℝ) ≤ Real.exp (L ^ 3) :=
    degreeDivisorCircuit_size_exp pindex qindex (⌊T⌋₊ + 1) L hL hVcard hqcard hfloor
  have hc : c.depth ≤ 19 := (degreeDivisorCircuit_depth pindex qindex _).trans (by norm_num)
  have hbad (n : ℤ) : c.eval
      (fun i => decide (((literal i).1.val : ℤ) ∣ n + (literal i).2)) = true ↔ bad n :=
    degreeDivisorCircuit_integer U V data.Q hV hQU data.primeQ q hq T hT (n + site)
  have hh := hb h J M B data hB hpool hBL S hS hSL q.primeFactors.card
    (Fintype.card U) hqdegree literal index site hindex c hc hsize bad hbad a N hN
  simpa [actualPaddingCoefficient, bad] using hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DegreeCostResidue
namespace OAI

/-! The model degree cost preserves one reciprocal for the fixed
padding divisor. This is the estimate transferred to integer intervals. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)



end ProhibitedPrimeFamily

theorem BravermanDepth22Input.eventually_integer_degree_cost
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (_hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (S : Finset ℕ), S ⊆ data.P → (S.card : ℝ) ≤ L ^ 2 →
      ∀ (W : ℝ), 10 ≤ W → 6 * W * S.card ≤ 400 * Real.log L →
      (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * S.card →
      ∀ (q : ℕ), q ∈ retainedPrimeDivisors data.Q →
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      uniformAverage (fun x : Fin N =>
        actualPaddingCoefficient q * positivePrimeWeight S ((a + x.val : ℤ) + site) *
          if (q : ℤ) ∣ (a + x.val : ℤ) + site ∧
            6 * W * S.card < (actualPaddingDegree data.P ((a + x.val : ℤ) + site) : ℝ)
            then 1 else 0) ≤
        actualPaddingCoefficient q / q * positivePrimeNormalizer S *
          Real.exp (-2 * W * S.card) + Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_degree_cost_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hb
  intro h J M B data hB hpool hBL S hSP hSL W hW hTL hmass q hq hqdegree site a N hN
  have hc := hb h J M B data hB hpool hBL S data.P
    (hSP.trans subset_union_left) subset_union_left hSL q hq hqdegree
    (6 * W * S.card) (by positivity) hTL site a N hN
  have hm := data.positive_divisor_degree_cost hB S hSP q hq W hW hmass site
  dsimp only at hc
  have hu := le_trans (le_abs_self _) hc
  linarith

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

lemma actualPaddingBin_sum_le (bins : Finset ℤ) (η c : ℝ) (hη : 0 < η)
    (q : ℕ) (w : ℝ) (hw : 0 ≤ w) :
    (∑ j ∈ bins, if actualPaddingBin η c j q then w else 0) ≤ w := by
  have he (j : ℤ) : actualPaddingBin η c j q ↔ paddingBin η c (Real.log q) = j :=
    (paddingBin_eq_iff η c (Real.log q) j hη).symm
  simp only [he]
  by_cases hm : paddingBin η c (Real.log q) ∈ bins
  · simp [hm]
  · simpa [hm] using hw




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleDeletionNormalizer
namespace OAI

/-! Exact normalizers for summing the deletion estimates over the
one-prime-per-band tuple family and retained padding divisors. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma tuple_normalizer_sum {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    (∑ d ∈ primeTupleDivisors P, positivePrimeNormalizer d.primeFactors) =
      (2 : ℝ) ^ J * ∏ j, primeHarmonicMass (P j) := by
  calc
    _ = ∑ d ∈ primeTupleDivisors P, (2 : ℝ) ^ J / d := by
      apply sum_congr rfl
      intro d hd
      have ha := primeTupleDivisors_arithmetic P hprime hdisjoint hd
      rw [positivePrimeNormalizer_squarefree d ha.1, ha.2.1]
    _ = (2 : ℝ) ^ J * ∑ d ∈ primeTupleDivisors P, 1 / (d : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ = _ := by rw [primeTupleDivisors_mass P hprime hdisjoint]; simp only [primeHarmonicMass_eq_sum]

lemma retained_padding_mass_le (Q D : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (hD : D ⊆ retainedPrimeDivisors Q) :
    (∑ q ∈ D, actualPaddingCoefficient q / (q : ℝ)) ≤ paddingTiltNormalizer Q := by
  rw [paddingTiltNormalizer_eq_divisor_sum Q hQ]
  apply sum_le_sum_of_subset_of_nonneg hD
  intro q _ _
  unfold actualPaddingCoefficient
  positivity

lemma tuple_normalizer_sum_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (D : Finset ℕ) (hD : D ⊆ primeTupleDivisors P) :
    (∑ d ∈ D, positivePrimeNormalizer d.primeFactors) ≤
      (2 : ℝ) ^ J * ∏ j, primeHarmonicMass (P j) := by
  rw [← tuple_normalizer_sum P hprime hdisjoint]
  exact sum_le_sum_of_subset_of_nonneg hD (fun d _ _ => by
    unfold positivePrimeNormalizer
    positivity)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.VariableDegreeDeletion
namespace OAI

/-! The tuple-degree deletion summed over disjoint logarithmic bins,
each sampled on its own integer interval. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma padding_bin_reciprocal_sum_le (Q R : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (hR : R ⊆ retainedPrimeDivisors Q) (bins : Finset ℤ) (η c : ℝ) (hη : 0 < η) :
    (∑ j ∈ bins, ∑ q ∈ R.filter (actualPaddingBin η c j),
      actualPaddingCoefficient q / (q : ℝ)) ≤ paddingTiltNormalizer Q := by
  simp only [sum_filter]
  rw [sum_comm]
  calc
    _ ≤ ∑ q ∈ R, actualPaddingCoefficient q / (q : ℝ) := by
      apply sum_le_sum
      intro q _
      exact actualPaddingBin_sum_le bins η c hη q _
        (div_nonneg (actualPaddingCoefficient_nonneg q) (Nat.cast_nonneg q))
    _ ≤ _ := retained_padding_mass_le Q R hQ hR


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShiftedDegreeDeletion
namespace OAI

/-! Pair-dependent endpoint shifts do not change the degree cost. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem BravermanDepth22Input.eventually_shifted_tuple_degree_deletion_oai
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (_hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (P : Fin J → Finset ℕ), primeTuplePool P = data.P →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      ∀ W : ℝ, 10 ≤ W → (∀ j, primeHarmonicMass (P j) ≤ 2 * W) →
      (J : ℝ) ≤ L ^ 2 → 6 * W * J ≤ 400 * Real.log L →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors P →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      (∀ q ∈ Q, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (bins : Finset ℤ) (η : ℝ) (c : ℕ → ℝ), 0 < η →
      ∀ (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ), (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ Q.filter (actualPaddingBin η (c d) j),
        uniformAverage (fun x : Fin (N j) =>
          positiveDegreeCost data.P d.primeFactors W q ((a j + x.val : ℤ) + site j d q))) ≤
      (2 : ℝ) ^ J * (∏ j, primeHarmonicMass (P j)) * paddingTiltNormalizer data.Q *
        Real.exp (-2 * W * J) +
          bins.card * D.card * Q.card * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_integer_degree_cost
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hb
  intro h J M B data hB hpool hBL P hP hprime hdisjoint W hW hV hJ hTL D hD Q hQ
    hqdegree bins η c hη site a N hN
  have hmass : (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * J := by
    rw [← primeHarmonicMass_eq_sum, ← hP, primeTuplePool_mass P hdisjoint]
    calc
      _ ≤ ∑ _j : Fin J, 2 * W := sum_le_sum (fun j _ => hV j)
      _ = _ := by simp; ring
  have ht (d : ℕ) (hd : d ∈ D) :
      (∑ j ∈ bins, ∑ q ∈ Q.filter (actualPaddingBin η (c d) j),
        uniformAverage (fun x : Fin (N j) =>
          positiveDegreeCost data.P d.primeFactors W q ((a j + x.val : ℤ) + site j d q))) ≤
      positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) * paddingTiltNormalizer data.Q +
        bins.card * Q.card * Real.exp (-(L ^ 9)) := by
    have ha := primeTupleDivisors_arithmetic P hprime hdisjoint (hD hd)
    have heach (j : ℤ) (hj : j ∈ bins) :
        (∑ q ∈ Q.filter (actualPaddingBin η (c d) j),
          uniformAverage (fun x : Fin (N j) =>
            positiveDegreeCost data.P d.primeFactors W q ((a j + x.val : ℤ) + site j d q))) ≤
        positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) *
          (∑ q ∈ Q.filter (actualPaddingBin η (c d) j), actualPaddingCoefficient q / q) +
            Q.card * Real.exp (-(L ^ 9)) := by
      have hpoint (q : ℕ) (hq : q ∈ Q.filter (actualPaddingBin η (c d) j)) :
          uniformAverage (fun x : Fin (N j) =>
            positiveDegreeCost data.P d.primeFactors W q
              ((a j + x.val : ℤ) + site j d q)) ≤
            actualPaddingCoefficient q / q * positivePrimeNormalizer d.primeFactors *
              Real.exp (-2 * W * J) + Real.exp (-(L ^ 9)) := by
        have hx := hb h J M B data hB hpool hBL d.primeFactors (ha.2.2.trans_eq hP)
          (by simpa only [ha.2.1] using hJ) W hW (by simpa only [ha.2.1] using hTL)
          (by simpa only [ha.2.1] using hmass) q (hQ (mem_filter.mp hq).1)
          (hqdegree q (mem_filter.mp hq).1) (site j d q) (a j) (N j) (hN j hj)
        simpa only [positiveDegreeCost, ha.2.1] using hx
      have hcard : ((Q.filter (actualPaddingBin η (c d) j)).card : ℝ) ≤ Q.card := by
        exact_mod_cast card_filter_le Q (actualPaddingBin η (c d) j)
      calc
        _ ≤ ∑ q ∈ Q.filter (actualPaddingBin η (c d) j),
            (actualPaddingCoefficient q / q * positivePrimeNormalizer d.primeFactors *
              Real.exp (-2 * W * J) + Real.exp (-(L ^ 9))) := sum_le_sum hpoint
        _ = positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) *
              (∑ q ∈ Q.filter (actualPaddingBin η (c d) j), actualPaddingCoefficient q / q) +
              (Q.filter (actualPaddingBin η (c d) j)).card * Real.exp (-(L ^ 9)) := by
          simp only [sum_add_distrib, ← sum_mul, sum_const, nsmul_eq_mul]
          ring
        _ ≤ _ := by
          have he := mul_le_mul_of_nonneg_right hcard (Real.exp_pos (-(L ^ 9))).le
          linarith
    calc
      _ ≤ ∑ j ∈ bins, (positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) *
            (∑ q ∈ Q.filter (actualPaddingBin η (c d) j), actualPaddingCoefficient q / q) +
              Q.card * Real.exp (-(L ^ 9))) := sum_le_sum heach
      _ = positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) *
            (∑ j ∈ bins, ∑ q ∈ Q.filter (actualPaddingBin η (c d) j), actualPaddingCoefficient q / q) +
              bins.card * Q.card * Real.exp (-(L ^ 9)) := by
        simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
        ring
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left
          (padding_bin_reciprocal_sum_le data.Q Q data.primeQ hQ bins η (c d) hη)
          (show 0 ≤ positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) by
            unfold positivePrimeNormalizer; positivity)
        linarith
  rw [sum_comm]
  calc
    _ ≤ ∑ d ∈ D, (positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) *
          paddingTiltNormalizer data.Q + bins.card * Q.card * Real.exp (-(L ^ 9))) := sum_le_sum ht
    _ = (∑ d ∈ D, positivePrimeNormalizer d.primeFactors) * Real.exp (-2 * W * J) *
          paddingTiltNormalizer data.Q + bins.card * D.card * Q.card * Real.exp (-(L ^ 9)) := by
      simp only [sum_add_distrib, ← sum_mul, sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (tuple_normalizer_sum_le P hprime hdisjoint D hD)
          (Real.exp_pos (-2 * W * J)).le) (paddingTiltNormalizer_pos data.Q).le
      nlinarith

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_shifted_tuple_degree_deletion_oai := @OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_shifted_tuple_degree_deletion_oai
