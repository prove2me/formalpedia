-- Prove2me | solution 1 for OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_shifted_actual_prohibited_deletion_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:51:15.025134+00:00
-- url     : https://prove2.me/submissions/5ec4f198-779e-4984-a77b-ea1e6761f1f6

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_BravermanDepth22Input_eventually_positive_weight_comparison
import Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_prohibited_model_row

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

lemma independent_average_map [DecidableEq ι] (μ : ι → FiniteLaw α)
    (ν : ι → FiniteLaw β) (g : ι → α → β)
    (hg : ∀ i y, (μ i).probability (fun x => g i x = y) = (ν i).weight y)
    (F : (ι → β) → ℝ) :
    (independent μ).average (fun x => F (fun i => g i (x i))) =
      (independent ν).average F := by
  rw [average_fibers]
  unfold average
  apply sum_congr rfl
  intro y _
  congr 1
  have he : (fun x : ι → α => (fun i => g i (x i)) = y) =
      (fun x => ∀ i, g i (x i) = y i) := by
    funext x
    exact propext funext_iff
  rw [he, independent_probability_all μ (fun i x => g i x = y i)]
  simp only [hg, independent]



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








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingBinSquare
namespace OAI

/-! The actual bin-square padding average is bounded by the exact difference
small-ball probability, uniformly in a common translation of all bins. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw

variable {α β : Type*} [Fintype α]

lemma average_finset_sum (μ : FiniteLaw α) (s : Finset β) (F : β → α → ℝ) :
    μ.average (fun x => ∑ b ∈ s, F b x) = ∑ b ∈ s, μ.average (F b) := by
  simp only [average, mul_sum]
  exact sum_comm


end FiniteLaw






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


lemma mem_wordDivisorPrimeSupport (w : List SignedStep) (p : ℕ) :
    p ∈ wordDivisorPrimeSupport w ↔
      ∃ k : Fin w.length, p ∈ ((w.get k).padding * (w.get k).tuple).primeFactors := by
  simp only [wordDivisorPrimeSupport, mem_biUnion, List.mem_toFinset]
  exact List.exists_mem_iff_get


/-- A residue test is exact arithmetic positivity at any common integer lift. -/
theorem residuePositiveWord_iff {ι : Type*} (p : ι → ℕ) (h : ℕ)
    (w : List SignedStep) (r : ∀ i, ZMod (p i)) (n : ℤ)
    (hn : ∀ i, (n : ZMod (p i)) = r i)
    (hsq : ∀ a ∈ w, Squarefree (a.padding * a.tuple))
    (hcover : ∀ q ∈ wordDivisorPrimeSupport w, ∃ i, p i = q) :
    ResiduePositiveWord p h w r ↔ PositiveWord h n w := by
  rw [positiveWord_iff_prime_tests h n w hsq]
  constructor
  · intro hr k q hq
    have hmem : q ∈ wordDivisorPrimeSupport w :=
      (mem_wordDivisorPrimeSupport w q).mpr ⟨k, hq⟩
    obtain ⟨i, rfl⟩ := hcover q hmem
    exact (residue_offset_divisibility (r i) n _ (hn i)).mpr (hr k i hq)
  · intro hn' k i hi
    exact (residue_offset_divisibility (r i) n _ (hn i)).mp (hn' k (p i) hi)



/-- The finite catalog's modular event is exactly the deleted event at any
common integer lift. Minimality remains in the catalog, not in the random law. -/
theorem prohibited_residue_catalog_iff {ι : Type*} (p : ι → ℕ)
    (pairs : Finset (ℕ × ℕ)) (h s : ℕ) (r : ∀ i, ZMod (p i)) (n : ℤ)
    (hn : ∀ i, (n : ZMod (p i)) = r i)
    (hsq : ∀ dq ∈ pairs, Squarefree (dq.2 * dq.1))
    (hcover : ∀ c : ProhibitedCatalog pairs h s,
      ∀ q ∈ wordDivisorPrimeSupport (decodeStepWord c.val), ∃ i, p i = q) :
    (∃ c : ProhibitedCatalog pairs h s, ResiduePositiveWord p h (decodeStepWord c.val) r) ↔
      ProhibitedSite h s (fun d q => (d, q) ∈ pairs) n := by
  have he (c : ProhibitedCatalog pairs h s) :
      ResiduePositiveWord p h (decodeStepWord c.val) r ↔
        PositiveWord h n (decodeStepWord c.val) :=
    residuePositiveWord_iff p h _ r n hn
      (fun a ha => hsq _ (c.property.1.2.2.1 a ha)) (hcover c)
  simp_rw [he]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨decodeStepWord c.val, hc, c.property⟩
  · rintro ⟨w, hw, hmin⟩
    obtain ⟨c, hc⟩ := stepWord_covered pairs s w hmin.1.2.1 hmin.1.2.2.1
    refine ⟨⟨c, ?_⟩, ?_⟩
    · simpa only [hc] using hmin
    · simpa only [hc] using hw


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




/-- The finite-residue event is precisely the manuscript's prohibited-site
predicate at any common integer lift of those same coordinates. -/
lemma deletedEvent_iff (s B : ℕ) (x : ↥(F.P ∪ F.Q) → Fin B) (n : ℤ)
    (hn : ∀ p : ↥(F.P ∪ F.Q), (n : ZMod p.val) = ((x p).val : ZMod p.val)) :
    F.deletedEvent s B x ↔ ProhibitedSite h s (fun d q => (d, q) ∈ F.pairs) n := by
  apply prohibited_residue_catalog_iff (fun p : ↥(F.P ∪ F.Q) => p.val) F.pairs h s _ n hn
    F.whole_squarefree
  intro c q hq
  exact ⟨⟨q, F.support_subset s c hq⟩, rfl⟩


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.UniformResidueTranslation
namespace OAI

/-! Translation invariance of the actual product law on the padded carrier. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma translateResidue_cast (B p : ℕ) [NeZero p] (hpB : p ≤ B)
    (c : ℤ) (x : Fin B) :
    ((translateResidue B p hpB c x).val : ZMod p) = (x.val : ZMod p) + (c : ZMod p) := by
  exact ZMod.natCast_zmod_val _

theorem uniformResidueLaw_translate (B p : ℕ) [NeZero p] (hp : 0 < p) (hpB : p ≤ B)
    (c : ℤ) (y : Fin B) :
    (uniformResidueLaw B p hp hpB).probability
      (fun x => translateResidue B p hpB c x = y) =
      (uniformResidueLaw B p hp hpB).weight y := by
  by_cases hy : y.val < p
  · have he (x : Fin B) : translateResidue B p hpB c x = y ↔
        (x.val : ZMod p) = (y.val : ZMod p) - (c : ZMod p) := by
      rw [eq_sub_iff_add_eq]
      constructor
      · intro hxy
        rw [← translateResidue_cast B p hpB c x, hxy]
      · intro hxy
        apply Fin.ext
        have hv := congrArg ZMod.val hxy
        simpa only [translateResidue, ZMod.val_natCast_of_lt hy] using hv
    have heq : (fun x => translateResidue B p hpB c x = y) =
        (fun x : Fin B => (x.val : ZMod p) = (y.val : ZMod p) - (c : ZMod p)) :=
      funext (fun x => propext (he x))
    rw [heq, uniformResidueLaw_mod_eq, uniformResidueLaw_weight B p hp hpB y hy]
  · have hn (x : Fin B) : translateResidue B p hpB c x ≠ y := by
      intro hxy
      have hx : (translateResidue B p hpB c x).val < p := ZMod.val_lt _
      exact hy (hxy ▸ hx)
    simp [FiniteLaw.probability, FiniteLaw.average, hn, uniformResidueLaw, hy]

theorem independent_residue_translate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℕ) (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B) (c : ℤ)
    (f : (ι → Fin B) → ℝ) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun x => f (fun i => translateResidue B (p i) (hpB i) c (x i))) =
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average f := by
  exact FiniteLaw.independent_average_map _ _ _
    (fun i y => uniformResidueLaw_translate B (p i) (hp i) (hpB i) c y) f

theorem ProhibitedPrimeFamily.residue_average_translate {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (f : ℤ → ℝ)
    (hf : ∀ n m, (∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) →
      f n = f m) (c : ℤ) :
    (data.residueLaw B hB).average (fun x => f (data.residueOrigin x + c)) =
      (data.residueLaw B hB).average (fun x => f (data.residueOrigin x)) := by
  let (p : ↥(data.P ∪ data.Q)) : NeZero p.val := ⟨(data.prime p).ne_zero⟩
  let translate (x : ↥(data.P ∪ data.Q) → Fin B) (p : ↥(data.P ∪ data.Q)) :=
    translateResidue B p.val (hB _ p.property) c (x p)
  calc
    _ = (data.residueLaw B hB).average (fun x => f (data.residueOrigin (translate x))) := by
      apply congrArg (data.residueLaw B hB).average
      funext x
      apply hf
      intro p
      rw [Int.cast_add, data.residueOrigin_spec, data.residueOrigin_spec]
      exact (translateResidue_cast B p.val (hB _ p.property) c (x p)).symm
    _ = _ := independent_residue_translate B (fun p : ↥(data.P ∪ data.Q) => p.val)
      (fun p => (data.prime p).pos) (fun p => hB _ p.property) c
      (fun x => f (data.residueOrigin x))

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








lemma ProhibitedPrimeFamily.prohibitedLiteral_integer_input {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (s : ℕ) (a : ℤ)
    (i : Fin (Fintype.card (ProhibitedInputs data.pairs h s))) :
    residueCircuitInputs (primeResidueModuli (data.P ∪ data.Q))
      (primeLiteralCoordinate (data.P ∪ data.Q) (data.prohibitedLiteral s))
      (primeLiteralTest (data.P ∪ data.Q) (data.prohibitedLiteral s))
      (fun j => (a : ZMod (primeResidueModuli (data.P ∪ data.Q) j))) i =
      prohibitedInputAt data.pairs h s a i := by
  rw [primeLiteral_integer_input]
  rfl

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedWeightIndependence
namespace OAI

/-! The retained departure weight is independent of tuple-prime residue draws.
Only the padding-prime residues enter its divisibility, density and cutoff data. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma squarefree_divisor_congr (Qp : Finset ℕ) (q : ℕ) (hq : Squarefree q)
    (hpool : q.primeFactors ⊆ Qp) (n m : ℤ)
    (hnm : ∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) :
    (q : ℤ) ∣ n ↔ (q : ℤ) ∣ m := by
  rw [squarefree_divisor_iff q hq n, squarefree_divisor_iff q hq m]
  apply forall_congr'
  intro p
  apply imp_congr_right
  intro hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    hnm p (hpool hp)]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MaskedWeightPeriodicity
namespace OAI

/-! The literal masked arithmetic weights depend only on the finite prime residues. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma ProhibitedPrimeFamily.prohibitedSite_congr {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s : ℕ) (n m : ℤ)
    (hnm : ∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) :
    ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n ↔
      ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) m := by
  let (p : ↥(data.P ∪ data.Q)) : NeZero p.val := ⟨(data.prime p).ne_zero⟩
  let x (p : ↥(data.P ∪ data.Q)) : Fin B :=
    ⟨(n : ZMod p.val).val, (ZMod.val_lt _).trans_le (hB _ p.property)⟩
  have hn (p : ↥(data.P ∪ data.Q)) : (n : ZMod p.val) = ((x p).val : ZMod p.val) :=
    (ZMod.natCast_zmod_val _).symm
  exact (data.deletedEvent_iff s B x n hn).symm.trans
    (data.deletedEvent_iff s B x m (fun p => (hnm p).symm.trans (hn p)))



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.VariableWindowComparison
namespace OAI

/-! Finite families of interval comparisons may use a different integer
length in every bin. No common probability space for the sampled
integer intervals is needed. -/

namespace TwoPointCorrelations

open _root_.Finset


lemma finset_sum_error {ι : Type*} (I : Finset ι) (f g ε : ι → ℝ)
    (h : ∀ i ∈ I, |f i - g i| ≤ ε i) :
    |(∑ i ∈ I, f i) - ∑ i ∈ I, g i| ≤ ∑ i ∈ I, ε i := by
  rw [← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum h)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedCostComparison
namespace OAI

/-! Positive costs at actual prohibited sites. The forbidden-word DNF
is conjoined with the padding divisor test on a shared list of prime
literals; all circuit bounds are derived here. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma prohibitedCostCircuit_eval {n m t : ℕ} (c : AC0Circuit n)
    (index : Fin n → Fin m) (qindex : Fin t → Fin m) (x : BooleanCube m) :
    (prohibitedCostCircuit c index qindex).eval x = true ↔
      (∀ i, x (qindex i) = true) ∧ c.eval (fun i => x (index i)) = true := by
  rw [prohibitedCostCircuit, AC0Circuit.conjunction_eval]
  simp only [Bool.forall_bool, Bool.false_eq_true, ite_false, ite_true,
    AC0Circuit.relabel_eval, degreeSubsetCircuit_eval]
  have he : (univ : Finset (Fin t)) ⊆ activeState (fun i => x (qindex i)) ↔
      ∀ i, x (qindex i) = true := by
    simp only [subset_iff, mem_univ, activeState, mem_filter, true_and, forall_const]
  rw [he]

lemma prohibitedCostCircuit_depth {n m t : ℕ} (c : AC0Circuit n)
    (index : Fin n → Fin m) (qindex : Fin t → Fin m) (hc : c.depth ≤ 2) :
    (prohibitedCostCircuit c index qindex).depth ≤ 3 := by
  apply AC0Circuit.conjunction_depth
  intro b
  cases b
  · exact (AC0Circuit.relabel_depth _ _).trans ((degreeSubsetCircuit_depth _).trans (by omega))
  · exact (AC0Circuit.relabel_depth _ _).trans hc

lemma prohibitedCostCircuit_size {n m t : ℕ} (c : AC0Circuit n)
    (index : Fin n → Fin m) (qindex : Fin t → Fin m) :
    (prohibitedCostCircuit c index qindex).size ≤ 2 + t + c.size := by
  rw [prohibitedCostCircuit, AC0Circuit.conjunction_size]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
  have hq := AC0Circuit.relabel_size qindex (degreeSubsetCircuit (univ : Finset (Fin t)))
  have hp := AC0Circuit.relabel_size index c
  simp only [degreeSubsetCircuit_size, card_univ, Fintype.card_fin] at hq
  omega

lemma prohibitedCostCircuit_size_exp {n m t : ℕ} (c : AC0Circuit n)
    (index : Fin n → Fin m) (qindex : Fin t → Fin m) (L : ℝ)
    (hL : 4800 ≤ L) (ht : (t : ℝ) ≤ 100 * Real.log L)
    (hc : (c.size : ℝ) ≤ Real.exp (104 * L ^ 2)) :
    ((prohibitedCostCircuit c index qindex).size : ℝ) ≤ Real.exp (L ^ 3) := by
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hraw : ((prohibitedCostCircuit c index qindex).size : ℝ) ≤ 2 + t + c.size := by
    exact_mod_cast prohibitedCostCircuit_size c index qindex
  have hsmall : 2 + (t : ℝ) ≤ Real.exp (104 * L ^ 2) := by
    have he := Real.add_one_le_exp (104 * L ^ 2)
    nlinarith [sq_nonneg (L - 1)]
  calc
    _ ≤ 2 * Real.exp (104 * L ^ 2) := by linarith
    _ ≤ Real.exp (1 + 104 * L ^ 2) := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hsq : (1 : ℝ) ≤ L ^ 2 := by nlinarith
      have hh := mul_nonneg (sq_nonneg L) (show 0 ≤ L - 105 by linarith)
      nlinarith)

/-- One actual positive tuple/padding cost at a prohibited origin is
compared with its value under the same residue law as the graph. -/
theorem BravermanDepth22Input.eventually_prohibited_cost_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B s cap : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      (s : ℝ) ≤ L → (cap : ℝ) ≤ L ^ 2 →
      (data.pairs.card : ℝ) ≤ Real.exp (101 * L) →
      (∀ dq ∈ data.pairs, (dq.2 * dq.1).primeFactors.card ≤ cap) →
      ∀ (S : Finset ℕ), S ⊆ data.P ∪ data.Q → (S.card : ℝ) ≤ L ^ 2 →
      ∀ (q : ℕ), q ∈ retainedPrimeDivisors data.Q →
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let F := fun n : ℤ => actualPaddingCoefficient q * positivePrimeWeight S (n + site) *
        if (q : ℤ) ∣ n + site ∧
          ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (n + site) then 1 else 0
      |uniformAverage (fun x : Fin N => F (a + x.val)) -
        (data.residueLaw B hB).average (fun x => F (data.residueOrigin x))| ≤
          Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_positive_prime_cost_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (4800 : ℝ)] with L hb hL
  intro h J M B s cap data hB hpool hBL hs hcap hpair hdegree S hS hSL q hq hqdegree site a N hN
  let U := data.P ∪ data.Q
  let n := Fintype.card (ProhibitedInputs data.pairs h s)
  let I := Fin n ⊕ Fin (Fintype.card U)
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let cindex : Fin n → Fin (Fintype.card I) := fun i => e (Sum.inl i)
  let uindex : Fin (Fintype.card U) → Fin (Fintype.card I) := fun i => e (Sum.inr i)
  let literal : Fin (Fintype.card I) → U × ℤ := fun i =>
    Sum.elim (fun j => ((data.prohibitedLiteral s j).1, site + (data.prohibitedLiteral s j).2))
      (fun j => ((Fintype.equivFin U).symm j, site)) (e.symm i)
  let index : Fin (Fintype.card S) → Fin (Fintype.card I) :=
    fun i => uindex (primeSubsetIndex U S hS i)
  let qindex : Fin (Fintype.card q.primeFactors) → Fin (Fintype.card I) :=
    fun i => uindex (primeSubsetIndex U q.primeFactors
      ((retainedPrimeDivisor_factors data.Q data.primeQ hq).trans subset_union_right) i)
  let c := prohibitedCostCircuit (prohibitedCircuit data.pairs h s) cindex qindex
  let bad := fun n : ℤ => (q : ℤ) ∣ n + site ∧
    ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (n + site)
  have hindex (i : Fin (Fintype.card S)) :
      (literal (index i)).1.val = ((Fintype.equivFin S).symm i).val ∧
        (literal (index i)).2 = site := by
    simp only [literal, index, uindex, Equiv.symm_apply_apply, Sum.elim_inr]
    exact ⟨primeSubsetIndex_value U S hS i, trivial⟩
  have hbad (n0 : ℤ) : c.eval
      (fun i => decide (((literal i).1.val : ℤ) ∣ n0 + (literal i).2)) = true ↔ bad n0 := by
    rw [prohibitedCostCircuit_eval]
    have hqbits : (∀ i, decide (((literal (qindex i)).1.val : ℤ) ∣
        n0 + (literal (qindex i)).2) = true) ↔ (q : ℤ) ∣ n0 + site := by
      simpa only [literal, qindex, uindex, Equiv.symm_apply_apply, Sum.elim_inr,
        primeSiteBits] using
        prime_divisor_all_bits U data.Q subset_union_right data.primeQ q hq (n0 + site)
    have hcbits : (fun i => decide (((literal (cindex i)).1.val : ℤ) ∣
        n0 + (literal (cindex i)).2)) = prohibitedInputAt data.pairs h s (n0 + site) := by
      funext i
      have hi := data.prohibitedLiteral_integer_input s (n0 + site) i
      rw [primeLiteral_integer_input] at hi
      simpa only [literal, cindex, Equiv.symm_apply_apply, Sum.elim_inl, add_assoc] using hi
    rw [hqbits, hcbits, prohibitedCircuit_correct data.pairs h s (n0 + site) data.whole_squarefree]
  have hsize : (c.size : ℝ) ≤ Real.exp (L ^ 3) := by
    apply prohibitedCostCircuit_size_exp _ _ _ L hL
    · simpa only [Fintype.card_coe] using hqdegree
    · exact prohibitedCircuit_size_quadratic data.pairs h s cap L (by linarith)
        hs hcap hpair hdegree
  have hc : c.depth ≤ 19 :=
    (prohibitedCostCircuit_depth _ _ _ (prohibitedCircuit_depth data.pairs h s)).trans (by omega)
  have hh := hb h J M B data hB hpool hBL S hS hSL q.primeFactors.card
    (Fintype.card I) hqdegree literal index site hindex c hc hsize bad hbad a N hN
  simpa [actualPaddingCoefficient, bad] using hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualRareDeletion
namespace OAI

/-! The prohibited-site part of the deletion estimate. The rare-event
cost is controlled after summing the actual positive tuple/padding row;
only the finite-interval comparison error pays for individual pairs. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma padding_pair_count_le (D : Finset ℕ) (padding : ℕ → Finset ℕ)
    (pairs : Finset (ℕ × ℕ))
    (hp : ∀ d ∈ D, ∀ q ∈ padding d, (d, q) ∈ pairs) :
    (∑ d ∈ D, (padding d).card) ≤ pairs.card := by
  rw [← card_sigma]
  apply card_le_card_of_injOn (fun z : (d : ℕ) × ℕ => (z.1, z.2))
  · intro z hz
    obtain ⟨hd, hq⟩ := mem_sigma.mp hz
    exact hp z.1 hd z.2 hq
  · intro x _ y _ hxy
    exact Sigma.ext (congrArg Prod.fst hxy) (by simpa using congrArg Prod.snd hxy)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.EndpointResidueAverage
namespace OAI

/-! Exact equality of the two endpoint deletion costs in the actual
product law. The whole padding weight need not be periodic across an
edge: only the fixed q and tuple divisor tests are transported. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma positivePrimeWeight_residue_congr (S : Finset ℕ) (n m : ℤ)
    (hnm : ∀ p ∈ S, (n : ZMod p) = (m : ZMod p)) :
    positivePrimeWeight S n = positivePrimeWeight S m := by
  unfold positivePrimeWeight
  apply prod_congr rfl
  intro p hp
  have he : (p : ℤ) ∣ n ↔ (p : ℤ) ∣ m := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hnm p hp]
  simp only [he]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PositiveCostPeriodicity
namespace OAI

/-! Periodicity needed to shift each numerical pair separately before
averaging its nonnegative deletion cost. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma ProhibitedPrimeFamily.prohibited_cost_average_translate {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (S : Finset ℕ) (hS : S ⊆ data.P ∪ data.Q) (s q : ℕ)
    (hq : q ∈ retainedPrimeDivisors data.Q) (site : ℤ) :
    (data.residueLaw B hB).average (fun x => actualPaddingCoefficient q *
      positivePrimeWeight S (data.residueOrigin x + site) *
        if (q : ℤ) ∣ data.residueOrigin x + site ∧
          ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (data.residueOrigin x + site)
          then 1 else 0) =
    (data.residueLaw B hB).average (fun x => actualPaddingCoefficient q *
      positivePrimeWeight S (data.residueOrigin x) *
        if (q : ℤ) ∣ data.residueOrigin x ∧
          ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (data.residueOrigin x)
          then 1 else 0) := by
  let F := fun n : ℤ => actualPaddingCoefficient q * positivePrimeWeight S n *
    if (q : ℤ) ∣ n ∧ ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n then 1 else 0
  have hF (n m : ℤ)
      (hnm : ∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) : F n = F m := by
    have hw := positivePrimeWeight_residue_congr S n m (fun p hp => hnm ⟨p, hS hp⟩)
    have hd := squarefree_divisor_congr data.Q q
      (retainedPrimeDivisor_squarefree data.Q data.primeQ hq)
      (retainedPrimeDivisor_factors data.Q data.primeQ hq) n m
      (fun p hp => hnm ⟨p, mem_union_right _ hp⟩)
    have hp := data.prohibitedSite_congr hB s n m hnm
    simp only [F, hw, hd, hp]
  exact data.residue_average_translate hB F hF site

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShiftedRareComparison
namespace OAI

/-! Rare-site row comparison with a distinct additive shift at every
numerical pair, in particular the opposite endpoint of that edge. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


theorem BravermanDepth22Input.eventually_shifted_prohibited_row_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B s cap : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      (s : ℝ) ≤ L → (cap : ℝ) ≤ L ^ 2 →
      (data.pairs.card : ℝ) ≤ Real.exp (101 * L) →
      (∀ dq ∈ data.pairs, (dq.2 * dq.1).primeFactors.card ≤ cap) →
      ∀ (D : Finset ℕ),
      (∀ d ∈ D, d.primeFactors ⊆ data.P ∪ data.Q) →
      (∀ d ∈ D, (d.primeFactors.card : ℝ) ≤ L ^ 2) →
      ∀ (padding : ℕ → Finset ℕ),
      (∀ d ∈ D, padding d ⊆ retainedPrimeDivisors data.Q) →
      (∀ d ∈ D, ∀ q ∈ padding d, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (site : ℕ → ℕ → ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      |(∑ d ∈ D, ∑ q ∈ padding d, uniformAverage (fun x : Fin N =>
          actualPaddingCoefficient q * positivePrimeWeight d.primeFactors ((a + x.val : ℤ) + site d q) *
            if (q : ℤ) ∣ (a + x.val : ℤ) + site d q ∧
              ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) ((a + x.val : ℤ) + site d q)
              then 1 else 0)) -
        (data.residueLaw B hB).average (fun x =>
          prohibitedPositiveRow data s D padding (data.residueOrigin x))| ≤
            (∑ d ∈ D, (padding d).card : ℕ) * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_prohibited_cost_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hb
  intro h J M B s cap data hB hpool hBL hs hcap hpair hdegree D hD hcard
    padding hpadding hqdegree site a N hN
  let μ := data.residueLaw B hB
  let atom := fun d q n => actualPaddingCoefficient q * positivePrimeWeight (Nat.primeFactors d) n *
    if (q : ℤ) ∣ n ∧ ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n then 1 else 0
  have hpoint (d : ℕ) (hd : d ∈ D) (q : ℕ) (hq : q ∈ padding d) :
      |uniformAverage (fun x : Fin N => atom d q ((a + x.val : ℤ) + site d q)) -
        μ.average (fun x => atom d q (data.residueOrigin x))| ≤ Real.exp (-(L ^ 9)) := by
    have hx := hb h J M B s cap data hB hpool hBL hs hcap hpair hdegree
      d.primeFactors (hD d hd) (hcard d hd) q (hpadding d hd hq) (hqdegree d hd q hq)
      (site d q) a N hN
    dsimp only at hx
    rw [data.prohibited_cost_average_translate hB d.primeFactors (hD d hd) s q
      (hpadding d hd hq) (site d q)] at hx
    exact hx
  have hinner (d : ℕ) (hd : d ∈ D) :
      |(∑ q ∈ padding d, uniformAverage (fun x : Fin N =>
          atom d q ((a + x.val : ℤ) + site d q))) -
        μ.average (fun x => ∑ q ∈ padding d, atom d q (data.residueOrigin x))| ≤
          (padding d).card * Real.exp (-(L ^ 9)) := by
    rw [μ.average_finset_sum]
    simpa only [sum_const, nsmul_eq_mul] using finset_sum_error (padding d)
      (fun q => uniformAverage (fun x : Fin N => atom d q ((a + x.val : ℤ) + site d q)))
      (fun q => μ.average (fun x => atom d q (data.residueOrigin x)))
      (fun _ => Real.exp (-(L ^ 9))) (hpoint d hd)
  have hout := finset_sum_error D
    (fun d => ∑ q ∈ padding d, uniformAverage (fun x : Fin N =>
      atom d q ((a + x.val : ℤ) + site d q)))
    (fun d => μ.average (fun x => ∑ q ∈ padding d, atom d q (data.residueOrigin x)))
    (fun d => (padding d).card * Real.exp (-(L ^ 9))) hinner
  rw [← μ.average_finset_sum, ← sum_mul, ← Nat.cast_sum] at hout
  exact hout

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

theorem BravermanDepth22Input.eventually_shifted_actual_prohibited_deletion_uniform
    (hBr : BravermanDepth22Input) (hP : ModFiveThetaInput) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ (E : Finset ℕ) (W C : ℝ),
      10 ≤ W → 0 ≤ C → ∀ᶠ L : ℝ in atTop,
      ∀ (h M B s cap : ℕ) (data : ProhibitedPrimeFamily h (primeSupplyCount W L) M),
      data.P = centeredPrimePool E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) →
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      (s : ℝ) ≤ L → (cap : ℝ) ≤ L ^ 2 →
      (data.pairs.card : ℝ) ≤ Real.exp (101 * L) →
      (∀ dq ∈ data.pairs, (dq.2 * dq.1).primeFactors.card ≤ cap) →
      (data.residueLaw B hB).probability (data.deletedEvent s B) ≤
        Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) →
      (primeSupplyCount W L : ℝ) ≤ L ^ 2 →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors
        (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)) →
      ∀ (padding : ℕ → Finset ℕ),
      (∀ d ∈ D, padding d ⊆ retainedPrimeDivisors data.Q) →
      (∀ d ∈ D, ∀ q ∈ padding d, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      (∀ d ∈ D, ∀ q ∈ padding d, (d, q) ∈ data.pairs) →
      ∀ (T : ℝ), 0 ≤ T → T ≤ Real.exp (C * Real.log L) →
      ∀ (site : ℕ → ℕ → ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      T * uniformAverage (fun x : Fin N =>
        shiftedProhibitedRow data s D padding site (a + x.val)) ≤
          Real.exp (-L ^ (9 / 10 : ℝ)) +
            T * data.pairs.card * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hc⟩ := hBr.eventually_shifted_prohibited_row_comparison
  refine ⟨A, hA, ?_⟩
  intro E W C hW hC
  filter_upwards [hc, hP.eventually_prohibited_model_row E W C hW hC,
    eventually_ge_atTop (1 : ℝ)] with L hc hm hL
  intro h M B s cap data hp hq hB hpool hBL hs hcap hpair hdegree hprob hJ D hD
    padding hpadding hqdegree hpairs T hT hTcap site a N hN
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)
  have hprime := centeredPrimeBands_prime E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)
  have hdisj := centeredPrimeBands_disjoint E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)
    (Real.rpow_nonneg (by linarith) _) (by linarith : 0 ≤ W)
  have hd (d : ℕ) (hd : d ∈ D) := primeTupleDivisors_arithmetic P hprime hdisj (hD hd)
  have hsupport (d : ℕ) (hmem : d ∈ D) : d.primeFactors ⊆ data.P ∪ data.Q := by
    apply (hd d hmem).2.2.trans
    rw [hp]
    exact subset_union_left
  have hcard (d : ℕ) (hmem : d ∈ D) : (d.primeFactors.card : ℝ) ≤ L ^ 2 := by
    rw [(hd d hmem).2.1]
    exact hJ
  have hcompare := hc h (primeSupplyCount W L) M B s cap data hB hpool hBL hs hcap
    hpair hdegree D hsupport hcard padding hpadding hqdegree site a N hN
  have hcompare' : |uniformAverage (fun x : Fin N =>
      shiftedProhibitedRow data s D padding site (a + x.val)) -
        (data.residueLaw B hB).average (fun x =>
          prohibitedPositiveRow data s D padding (data.residueOrigin x))| ≤
      (∑ d ∈ D, (padding d).card : ℕ) * Real.exp (-(L ^ 9)) := by
    simpa only [shiftedProhibitedRow, uniformAverage_finset_sum] using hcompare
  have hmodel := hm h M B s data hp hq hB hprob D hD padding hpadding T hT hTcap 0
  simp only [add_zero] at hmodel
  have hcount : ((∑ d ∈ D, (padding d).card : ℕ) : ℝ) ≤ data.pairs.card := by
    exact_mod_cast padding_pair_count_le D padding data.pairs hpairs
  have hdiff := (le_abs_self _).trans hcompare'
  have hdiffT := mul_le_mul_of_nonneg_left hdiff hT
  have hcountT := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hcount (Real.exp_pos (-(L ^ 9))).le) hT
  nlinarith






end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_shifted_actual_prohibited_deletion_uniform := @OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_shifted_actual_prohibited_deletion_uniform
