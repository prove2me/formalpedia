-- Prove2me | solution 1 for OAI.KaplanskyCounterexample.finitelyPresented_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:42:55.354183+00:00
-- url     : https://prove2.me/submissions/fdbf0498-0d7a-4c21-9520-12acc1783f9b

import Mathlib
import Definitions.Def_OAIQWKAP002
import Theorems.Thm_OAI_KaplanskyCounterexample_CurrentMain_multipleHNN_finitelyPresented
import Theorems.Thm_OAI_KaplanskyCounterexample_MultipleHNN_of_injective

section
-- module Solutions.OAIQW_Kaplansky.MultiHNN
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical
open Monoid Function
namespace KaplanskyCounterexample.MultipleHNN

universe u v
variable {H : Type u} [Group H] {I : Type v}
variable (A B : I → Subgroup H) (φ : ∀ i, A i ≃* B i)

lemma letter_mul_of (i : I) (a : A i) :
    letter A B φ i * of A B φ a = of A B φ (φ i a) * letter A B φ i :=
  (Con.eq _).mpr <| ConGen.Rel.of _ _ ⟨i, a, rfl, rfl⟩

/-- A central base element fixed in every associated subgroup stays central. -/
theorem of_central (z : H) (hz : ∀ h : H, Commute h z)
    (ha : ∀ i, z ∈ A i) (hφ : ∀ i, (φ i ⟨z, ha i⟩ : H) = z) :
    ∀ x : Extension A B φ, Commute x (of A B φ z) := by
  intro x
  induction x using induction_on A B φ with
  | hof h => exact (hz h).map (of A B φ)
  | ht i =>
    have h := letter_mul_of A B φ i ⟨z, ha i⟩
    rw [hφ i] at h
    exact h
  | hmul x y hx hy => exact hx.mul_left hy
  | hinv x hx => exact hx.inv_left

end KaplanskyCounterexample.MultipleHNN
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

attribute [local instance] OAI.KaplanskyCounterexample.Prescription.instDecidablePredNatAndPrimeDvdHPowQcardOfNatHAdd
lemma dimension_pos (h : ℕ) : 0 < dimension h := by
  unfold dimension blockdim
  omega

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.LexicographicOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

lemma first_le {α : Type u_3} [Fintype α] [LinearOrder α] (P : α → Prop) (h : ∃ x, P x)
    (y : α) (hy : P y) : first P h ≤ y :=
  Finset.min'_le _ y (by simp [hy])

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.FiniteAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} [Field Q] [AddCommGroup A] [Module Q A] [Fintype A]

namespace AffineCoset
variable (U : Submodule Q A)

lemma of_surjective : Function.Surjective (of U) := by
  rintro ⟨C,x,rfl⟩
  exact ⟨x,rfl⟩

end AffineCoset

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.Pairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped BigOperators Classical
open MvPolynomial

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.PolynomialPairing

variable {Q : Type u_2} {σ : Type u_3} [Field Q]

lemma lineRestriction_eval (u v : σ → Q) (P : MvPolynomial σ Q) (t : Q) :
    (lineRestriction u v P).eval t = MvPolynomial.eval (fun i => u i + t * v i) P := by
  unfold lineRestriction
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P R hP hR => simp [hP, hR]
  | mul_X P i hP => simp [hP, mul_comm t]

lemma lineRestriction_degree (u v : σ → Q) (P : MvPolynomial σ Q) :
    (lineRestriction u v P).natDegree ≤ P.totalDegree := by
  rw [lineRestriction, MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  apply (Polynomial.natDegree_mul_le).trans
  simp only [Polynomial.natDegree_C, zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply le_trans _ (MvPolynomial.le_totalDegree hd)
  change (∑ i ∈ d.support, _) ≤ ∑ i ∈ d.support, d i
  apply Finset.sum_le_sum
  intro i _
  apply (Polynomial.natDegree_pow_le).trans
  have hc : (Polynomial.C (u i) + Polynomial.C (v i) * Polynomial.X).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    simp only [Polynomial.natDegree_C, max_le_iff, zero_le, true_and]
    simpa using Polynomial.natDegree_C_mul_X_pow_le (v i) 1
  simpa using Nat.mul_le_mul_left (d i) hc

/-- The exact finite-field power-sum consequence used on every line. -/
lemma sum_polynomial_eval [Fintype Q] (P : Polynomial Q)
    (hP : P.natDegree < Fintype.card Q - 1) : ∑ t : Q, P.eval t = 0 := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  rw [← Finset.mul_sum]
  have hk' : k < Fintype.card Q - 1 := lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp k hk) hP
  rw [FiniteField.sum_pow_lt_card_sub_one Q k hk', mul_zero]

theorem line_sum_zero [Fintype Q] (u v : σ → Q) (P : MvPolynomial σ Q)
    (hP : P.totalDegree < Fintype.card Q - 1) :
    ∑ t : Q, MvPolynomial.eval (fun i => u i + t * v i) P = 0 := by
  simpa only [lineRestriction_eval] using sum_polynomial_eval (lineRestriction u v P)
    (lt_of_le_of_lt (lineRestriction_degree u v P) hP)

/-- Partitioning the entire affine space into coordinate-parallel lines. -/
theorem affine_space_sum_zero [Fintype Q] [Fintype σ] (i : σ) (P : MvPolynomial σ Q)
    (hP : P.totalDegree < Fintype.card Q - 1) :
    ∑ x : σ → Q, MvPolynomial.eval x P = 0 := by
  rw [← (Equiv.funSplitAt i Q).symm.sum_comp (fun x => MvPolynomial.eval x P)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro x _
  let u : σ → Q := fun j => if h : j = i then 0 else x ⟨j, h⟩
  let v : σ → Q := fun j => if j = i then 1 else 0
  have hparam (t : Q) : (Equiv.funSplitAt i Q).symm (t, x) = fun j => u j + t * v j := by
    funext j
    by_cases h : j = i <;> simp [Equiv.funSplitAt, u, v, h]
  simpa only [hparam] using line_sum_zero u v P hP

end KaplanskyCounterexample.PolynomialPairing

namespace KaplanskyCounterexample.PolynomialPairing

variable {Q : Type u_4} [Field Q] [Fintype Q] {n q : ℕ}

omit [Fintype Q] in
lemma holePolynomial_degree (a : Fin q ≃ Q) (d : ℕ) (o : Fin n → Q) :
    (holePolynomial a d o).totalDegree ≤ d :=
  (exists_interpolation a (fun k : Simplex n q d => if point a k.val = o then 1 else 0)).choose_spec.1

omit [Fintype Q] in
lemma holePolynomial_eval (a : Fin q ≃ Q) (d : ℕ) (o x : Fin n → Q)
    (hx : x ∈ simplexPoints a n d) :
    MvPolynomial.eval x (holePolynomial a d o) = if x = o then 1 else 0 := by
  obtain ⟨k, rfl⟩ := (mem_simplexPoints a).mp hx
  exact (exists_interpolation a (fun k : Simplex n q d => if point a k.val = o then 1 else 0)).choose_spec.2 k

omit [Fintype Q] in
lemma sum_holes_gram (a : Fin q ≃ Q) {d : ℕ} (O : Finset (Fin n → Q))
    (hO : O ⊆ simplexPoints a n d) :
    ∑ v ∈ O, gramColumn a d O v = 1 := by
  ext o o'
  simp only [Matrix.sum_apply, gramColumn, column]
  calc
    _ = ∑ v ∈ O, (if v = o.val then (1 : Q) else 0) *
        (if v = o'.val then (1 : Q) else 0) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [holePolynomial_eval a d _ _ (hO hv), holePolynomial_eval a d _ _ (hO hv)]
    _ = _ := by
      rw [Finset.sum_eq_single_of_mem o.val o.property]
      · simp only [ite_true, one_mul, Matrix.one_apply]
        congr 1
        exact propext Subtype.val_inj
      · intro v _ hv
        rw [ite_eq_right hv, zero_mul]

omit [Fintype Q] in
lemma gram_degree (a : Fin q ≃ Q) (d : ℕ) (o o' : Fin n → Q) :
    (holePolynomial a d o * holePolynomial a d o').totalDegree ≤ 2 * d := by
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (by simpa [two_mul] using (Nat.add_le_add (holePolynomial_degree a d o)
      (holePolynomial_degree a d o')))

lemma cutoff_degree (q : ℕ) (hq : 2 ≤ q) : 2 * ((q - 2) / 2) < q - 1 := by
  have h := Nat.mul_div_le (q - 2) 2
  omega

/-- All entries of the Gram column sum vanish on the full affine space. -/
lemma sum_all_gram (a : Fin q ≃ Q) (hq : q = Fintype.card Q) (hn : 0 < n)
    (O : Finset (Fin n → Q)) :
    ∑ v : Fin n → Q, gramColumn a ((q - 2) / 2) O v = 0 := by
  ext o o'
  simp only [Matrix.sum_apply, Matrix.zero_apply, gramColumn, column]
  have hq2 : 2 ≤ q := hq ▸ Nat.succ_le_iff.mpr (Fintype.one_lt_card (α := Q))
  convert! (affine_space_sum_zero (⟨0, hn⟩ : Fin n)
    (holePolynomial a ((q - 2) / 2) o.val * holePolynomial a ((q - 2) / 2) o'.val)
    ((gram_degree a _ _ _).trans_lt (hq ▸ cutoff_degree q hq2))) using 1
  simp only [map_mul]
  exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)

/-- The precise global identity on V, with no characteristic simplification. -/
theorem sum_complement_gram (a : Fin q ≃ Q) (hq : q = Fintype.card Q) (hn : 0 < n)
    (O : Finset (Fin n → Q)) (hO : O ⊆ simplexPoints a n ((q - 2) / 2)) :
    ∑ v ∈ Finset.univ \ O, gramColumn a ((q - 2) / 2) O v = -1 := by
  have h := Finset.sum_sdiff (f := gramColumn a ((q - 2) / 2) O) (Finset.subset_univ O)
  rw [sum_holes_gram a O hO, sum_all_gram a hq hn O] at h
  exact eq_neg_of_add_eq_zero_left h

omit [Fintype Q] in
lemma AffineLine.param_injective (L : AffineLine Q n) : Function.Injective L.param := by
  intro t u h
  have hi : ∃ i, L.direction i ≠ 0 := by
    by_contra! h
    exact L.direction_ne_zero (funext h)
  obtain ⟨i, hi⟩ := hi
  have he := congrFun h i
  exact mul_right_cancel₀ hi (add_left_cancel he)

theorem sum_line_gram (a : Fin q ≃ Q) (hq : q = Fintype.card Q)
    (O : Finset (Fin n → Q)) (L : AffineLine Q n) :
    ∑ v ∈ L.points, gramColumn a ((q - 2) / 2) O v = 0 := by
  rw [AffineLine.points, Finset.sum_image (L.param_injective.injOn)]
  ext o o'
  simp only [Matrix.sum_apply, Matrix.zero_apply, gramColumn, column]
  have hq2 : 2 ≤ q := hq ▸ Nat.succ_le_iff.mpr (Fintype.one_lt_card (α := Q))
  convert! (line_sum_zero L.base L.direction
    (holePolynomial a ((q - 2) / 2) o.val * holePolynomial a ((q - 2) / 2) o'.val)
    ((gram_degree a _ _ _).trans_lt (hq ▸ cutoff_degree q hq2))) using 1
  simp only [map_mul]
  apply Finset.sum_congr rfl
  intro t _
  rfl

end KaplanskyCounterexample.PolynomialPairing
end
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

attribute [local instance] OAI.KaplanskyCounterexample.Prescription.instDecidablePredNatSucceeds
lemma selectedH_le (h : ℕ) (hh : Succeeds h) : selectedH ≤ h := Nat.find_min' _ hh
lemma selectedH_le217 : selectedH ≤ 217 := selectedH_le 217 succeeds217

lemma selectedPair_minimal (p : Pair selectedInput) (hp : Test selectedInput p) :
    @LE.le _ (pairOrder selectedInput).toLE selectedPair p := by
  let _ := pairOrder selectedInput
  exact first_le (Test selectedInput) selectedInput_success p hp

/-- Formal termination certificate for both the outer loop and its finite inner loop. -/
theorem finite_search_terminates :
    2 ≤ selectedH ∧ selectedH ≤ 217 ∧ Test selectedInput selectedPair ∧
      (∀ h, Succeeds h → selectedH ≤ h) ∧
      (∀ p, Test selectedInput p → @LE.le _ (pairOrder selectedInput).toLE selectedPair p) :=
  ⟨selectedH_ge,selectedH_le217,selectedPair_spec,selectedH_le,selectedPair_minimal⟩

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.IncidenceDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.IncidenceDirections
variable {K : Type u_1} [Field K]

/-- The local subgroup decomposition, before applying a group-ring map. -/
lemma sum_directions [Fintype K] {M : Type u_2} [AddCommGroup M]
    (f : (Fin 2 → K) → M) :
    ∑ a : Fin 2 → K, f a = f 0 + ∑ d : Option K, (∑ c : K, f (directionMap d c) - f 0) := by
  rw [Fintype.sum_eq_add_sum_subtype_ne f 0]
  congr 1
  rw [← Equiv.sum_comp nonzeroEquiv (fun a => f a.val), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro d _
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun c : K => f (directionMap d c)) 0]
  simp

end KaplanskyCounterexample.IncidenceDirections
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.AssignedDevelopment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical BigOperators

namespace KaplanskyCounterexample.AssignedDevelopment
open GluedGroup AssignedDirections IncidenceDirections
variable {V F : Type} (Inc : F → Finset V) (ℓ : ℕ) [Fact ℓ.Prime]
variable (assign : ∀ v, {f : F // v ∈ Inc f} ≃ Option (ZMod ℓ))
variable (hInc : ∀ f, (Inc f).Nonempty)

lemma point_direction (v : V) (f : F) (hf : v ∈ Inc f) (c : ZMod ℓ) :
    point Inc ℓ assign v (Multiplicative.ofAdd (maps Inc ℓ assign v ⟨f, hf⟩ c)) =
      line Inc ℓ assign hInc f (Multiplicative.ofAdd c) := by
  by_cases hc : c = 0
  · subst c
    simp
  · exact (theta_generator Inc ℓ (maps Inc ℓ assign) (covers Inc ℓ assign) v f hf c hc).trans
      (theta_generator Inc ℓ (maps Inc ℓ assign) (covers Inc ℓ assign) (hInc f).choose f (hInc f).choose_spec c hc).symm

variable [Fintype F]

lemma subgroup_decomposition {K : Type u_3} [CommRing K] (v : V) :
    ∑ a : PointGroup ℓ, MonoidAlgebra.single (point Inc ℓ assign v a) (1 : K) =
      1 + ∑ f : {f : F // v ∈ Inc f},
        ((∑ c : Multiplicative (ZMod ℓ), MonoidAlgebra.single (line Inc ℓ assign hInc f.val c) (1 : K)) - 1) := by
  have h := sum_directions (K := ZMod ℓ) (fun a =>
    MonoidAlgebra.single (point Inc ℓ assign v (Multiplicative.ofAdd a)) (1 : K))
  rw [← Equiv.sum_comp Multiplicative.ofAdd
    (fun a : PointGroup ℓ => MonoidAlgebra.single (point Inc ℓ assign v a) (1 : K))]
  rw [h]
  simp only [ofAdd_zero, map_one, ← MonoidAlgebra.one_def]
  congr 1
  rw [← Equiv.sum_comp (assign v)
    (fun d : Option (ZMod ℓ) =>
      (∑ c : ZMod ℓ, MonoidAlgebra.single
        (point Inc ℓ assign v (Multiplicative.ofAdd (directionMap d c))) (1 : K)) - 1)]
  apply Finset.sum_congr rfl
  intro f _
  congr 1
  rw [← Equiv.sum_comp Multiplicative.ofAdd
    (fun c : Multiplicative (ZMod ℓ) => MonoidAlgebra.single (line Inc ℓ assign hInc f.val c) (1 : K))]
  apply Finset.sum_congr rfl
  intro c _
  exact congrArg (fun g => MonoidAlgebra.single g (1 : K))
    (point_direction Inc ℓ assign hInc v f.val f.property c)

end KaplanskyCounterexample.AssignedDevelopment
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.CoordinateCharacters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.CoordinateCharacters
variable (ℓ : ℕ) [Fact ℓ.Prime]

attribute [local instance] OAI.KaplanskyCounterexample.CoordinateCharacters.modulusNeZero
lemma form_injective : Function.Injective (form ℓ) := by
  intro a b hab
  funext i
  have hi := congrArg (fun φ : Plane ℓ →* Cyclic ℓ =>
    Multiplicative.toAdd (φ (Multiplicative.ofAdd (Pi.single i 1)))) hab
  fin_cases i <;> simpa [form, Pi.single_apply] using hi

variable {K : Type u_3} [Field K]

lemma cyclicCharacter_injective {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) :
    Function.Injective (cyclicCharacter ℓ hζ) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  apply ZMod.val_injective ℓ
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  exact congrArg (fun u : Kˣ => (u : K)) hab

lemma cyclicCharacter_ne_one {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) :
    cyclicCharacter ℓ hζ ≠ 1 := by
  intro h
  have he : Multiplicative.ofAdd (1 : ZMod ℓ) = 1 :=
    (cyclicCharacter_injective ℓ hζ) (by simp [h])
  exact (one_ne_zero : (1 : ZMod ℓ) ≠ 0) (congrArg Multiplicative.toAdd he)

end KaplanskyCounterexample.CoordinateCharacters
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription
variable (ℓ : ℕ) [Fact ℓ.Prime]
variable {V m : Type} [Fintype V] [Fintype m] [LinearOrder V] [LinearOrder m]

attribute [local instance] OAI.KaplanskyCounterexample.Prescription.slotModulusNeZero
attribute [local instance] OAI.KaplanskyCounterexample.Prescription.slotIndexWellFounded
lemma assignedForm_distinct (hsize : Fintype.card V ≤ Fintype.card m * ℓ^2)
    (v w : V) (hvw : v ≠ w) (hs : assignedSlot ℓ hsize v=assignedSlot ℓ hsize w) :
    assignedForm ℓ hsize v ≠ assignedForm ℓ hsize w := by
  intro he
  exact hvw ((slotAssignment ℓ hsize).injective
    (Prod.ext hs (CoordinateCharacters.form_injective ℓ he)))

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample
open PolynomialPairing FiniteGeometry

namespace PolynomialPairing
variable {Q K : Type} [Field Q] [Fintype Q] [Field K] [Algebra Q K]
  {q n : ℕ}

lemma complementMatrix_global (a : Fin q ≃ Q) (hq : q = Fintype.card Q)
    (hn : 0 < n) (O : Finset (Fin n → Q))
    (hO : O ⊆ simplexPoints a n ((q-2)/2)) :
    complementMatrix (K := K) a O * (complementMatrix (K := K) a O).transpose = -1 := by
  ext i j
  have hh := congrFun (congrFun (sum_complement_gram a hq hn O hO) i) j
  simp only [Matrix.sum_apply,gramColumn,Matrix.neg_apply,Matrix.one_apply] at hh
  have hs : ∑ v : {v : Fin n → Q // v ∉ O},
      column a ((q-2)/2) O v.val i * column a ((q-2)/2) O v.val j =
      ∑ v ∈ Finset.univ \ O, column a ((q-2)/2) O v i * column a ((q-2)/2) O v j := by
    symm
    exact Finset.sum_subtype _ (by simp) _
  change (∑ v : {v : Fin n → Q // v ∉ O},
    algebraMap Q K (column a ((q-2)/2) O v.val i) *
    algebraMap Q K (column a ((q-2)/2) O v.val j)) = -(if i = j then 1 else 0)
  simp_rw [← map_mul]
  rw [← map_sum,hs,hh]
  simp

lemma sum_fullLine_gram (a : Fin q ≃ Q) (hq : q = Fintype.card Q)
    (O : Finset (Fin n → Q)) {s : Finset (Fin n → Q)} (hs : FullLine (Q := Q) s) :
    ∑ v ∈ s, gramColumn a ((q-2)/2) O v = 0 := by
  obtain ⟨x,w,hw,rfl⟩ := hs
  let l : PolynomialPairing.AffineLine Q n := ⟨x,w,hw⟩
  have hl : l.points = linePoints (Q := Q) x w := by
    ext z
    simp only [PolynomialPairing.AffineLine.points,linePoints,Finset.mem_image,
      Finset.mem_univ,true_and]
    rfl
  rw [← hl]
  exact sum_line_gram a hq O l

lemma complementMatrix_local (a : Fin q ≃ Q) (hq : q = Fintype.card Q)
    (O : Finset (Fin n → Q)) {s : Finset (Fin n → Q)}
    (hs : FullLine (Q := Q) s) (ha : ∀ v ∈ s, v ∉ O) (i j : O) :
    ∑ v ∈ s.subtype (fun v => v ∉ O),
      complementMatrix (K := K) a O i v * complementMatrix a O j v = 0 := by
  have hh := congrFun (congrFun (sum_fullLine_gram a hq O hs) i) j
  simp only [Matrix.sum_apply,gramColumn,Matrix.zero_apply] at hh
  change ∑ v ∈ s.subtype (fun v => v ∉ O),
    algebraMap Q K (column a ((q-2)/2) O v.val i) *
    algebraMap Q K (column a ((q-2)/2) O v.val j) = 0
  simp_rw [← map_mul]
  rw [← map_sum]
  have he : (∑ v ∈ s.subtype (fun v => v ∉ O),
      column a ((q-2)/2) O v.val i * column a ((q-2)/2) O v.val j) =
      ∑ v ∈ s, column a ((q-2)/2) O v i * column a ((q-2)/2) O v j := by
    exact Finset.sum_subtype_of_mem (fun v => column a ((q-2)/2) O v i * column a ((q-2)/2) O v j) ha
  rw [he,hh,map_zero]

end PolynomialPairing

end KaplanskyCounterexample
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.Prescription.Output
open PolynomialPairing

attribute [local instance] OAI.KaplanskyCounterexample.Prescription.Output.instDecidableEqSubtypeKHMemSubfieldSubfield
attribute [local instance] OAI.KaplanskyCounterexample.Prescription.Output.instDecidableEqV
lemma forms_distinct (v w : V) (hne : v ≠ w) (hs : slot v=slot w) : form v ≠ form w :=
  assignedForm_distinct ell sizes.2.2 v w hne hs

lemma X_global : X * X.transpose = -1 :=
  complementMatrix_global _ (Q_card h).symm (dimension_pos h.val) _ success.holes_subset
lemma X_local (f : F) (i j : Slots) : ∑ v ∈ Inc f, X i v * X j v=0 :=
  complementMatrix_local _ (Q_card h).symm holes (success.full f.val f.property)
    (success.avoid f.val f.property) i j

end KaplanskyCounterexample.Prescription.Output
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.CharacterIdempotents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.CharacterIdempotents
variable {K : Type u_1} {A : Type u_2} {G : Type u_3} [Field K] [Group A] [Fintype A] [Group G]

lemma sum_character_eq_zero (χ : A →* Kˣ) (hχ : χ ≠ 1) :
    ∑ a : A, (χ a : K) = 0 := by
  have hn : ∃ b : A, (χ b : K) ≠ 1 := by
    by_contra! h
    apply hχ
    ext b
    exact h b
  obtain ⟨b, hb⟩ := hn
  have hh : (χ b : K) * ∑ a : A, (χ a : K) = ∑ a : A, (χ a : K) := by
    rw [Finset.mul_sum]
    simp only [← Units.val_mul, ← map_mul]
    exact Equiv.sum_comp (Equiv.mulLeft b) (fun a => (χ a : K))
  by_contra hs
  exact hb ((mul_eq_right₀ hs).mp hh)

lemma projector_mul_single (χ : A →* Kˣ) (b : A) :
    projector χ * MonoidAlgebra.single b 1 = (χ b : K) • projector χ := by
  unfold projector
  rw [smul_mul_assoc, Finset.sum_mul, smul_smul]
  rw [mul_comm (χ b : K), ← smul_smul]
  congr 1
  rw [Finset.smul_sum]
  calc
    (∑ a : A, MonoidAlgebra.single a ((χ a : K)⁻¹) * MonoidAlgebra.single b 1) =
        ∑ a : A, (χ b : K) • MonoidAlgebra.single (a * b) ((χ (a * b) : K)⁻¹) := by
      apply Finset.sum_congr rfl
      intro a _
      simp [MonoidAlgebra.single_mul_single, mul_comm]
    _ = _ := Equiv.sum_comp (Equiv.mulRight b)
      (fun a : A => (χ b : K) • MonoidAlgebra.single a ((χ a : K)⁻¹))

lemma projector_mul (χ ψ : A →* Kˣ) :
    projector χ * projector ψ =
      ((Fintype.card A : K)⁻¹ * ∑ b : A, ((χ b : K) * (ψ b : K)⁻¹)) •
        projector χ := by
  conv_lhs => rhs; unfold projector
  rw [mul_smul_comm, Finset.mul_sum]
  have hh (b : A) : projector χ * MonoidAlgebra.single b ((ψ b : K)⁻¹) =
      ((χ b : K) * (ψ b : K)⁻¹) • projector χ := by
    rw [show MonoidAlgebra.single b ((ψ b : K)⁻¹) =
      (ψ b : K)⁻¹ • MonoidAlgebra.single b 1 by simp]
    rw [mul_smul_comm, projector_mul_single, smul_smul, mul_comm]
  simp_rw [hh]
  rw [← Finset.sum_smul, smul_smul]

lemma projector_idempotent (χ : A →* Kˣ) (hcard : (Fintype.card A : K) ≠ 0) :
    IsIdempotentElem (projector χ) := by
  change projector χ * projector χ = projector χ
  rw [projector_mul]
  simp [hcard]

lemma projector_orthogonal (χ ψ : A →* Kˣ) (hne : χ ≠ ψ) :
    projector χ * projector ψ = 0 := by
  rw [projector_mul]
  have hn : χ * ψ⁻¹ ≠ 1 := by
    intro h
    apply hne
    apply MonoidHom.ext
    intro a
    have hh := congrArg (fun f : A →* Kˣ => f a) h
    exact mul_inv_eq_one.mp hh
  have h := sum_character_eq_zero (χ * ψ⁻¹) hn
  simpa using congrArg (fun c : K => ((Fintype.card A : K)⁻¹ * c) • projector χ) h

lemma projector_one_coeff (χ : A →* Kˣ) :
    (projector χ).coeff 1 = (Fintype.card A : K)⁻¹ := by
  simp [projector, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul, Finsupp.single_apply]

lemma projector_ne_zero (χ : A →* Kˣ) (hcard : (Fintype.card A : K) ≠ 0) :
    projector χ ≠ 0 := by
  intro h
  have := congrArg (fun p : MonoidAlgebra K A => p.coeff 1) h
  rw [projector_one_coeff] at this
  exact (inv_ne_zero hcard) this

lemma pushed_eq_sum (f : A →* G) (χ : A →* Kˣ) :
    pushed f χ = (Fintype.card A : K)⁻¹ •
      ∑ a : A, MonoidAlgebra.single (f a) ((χ a : K)⁻¹) := by
  simp [pushed, projector, map_sum]

lemma pushed_idempotent (f : A →* G) (χ : A →* Kˣ)
    (hc : (Fintype.card A : K) ≠ 0) :
    pushed f χ * pushed f χ = pushed f χ := by
  unfold pushed
  rw [← map_mul, projector_idempotent χ hc]

lemma pushed_orthogonal (f : A →* G) (χ ψ : A →* Kˣ) (hne : χ ≠ ψ) :
    pushed f χ * pushed f ψ = 0 := by
  unfold pushed
  rw [← map_mul, projector_orthogonal χ ψ hne, map_zero]

lemma pushed_ne_zero (f : A →* G) (hf : Function.Injective f) (χ : A →* Kˣ)
    (hc : (Fintype.card A : K) ≠ 0) : pushed f χ ≠ 0 := by
  intro h
  exact projector_ne_zero χ hc ((MonoidAlgebra.mapDomain_injective hf) (h.trans (MonoidAlgebra.mapDomain_zero f).symm))

lemma pushed_mul_single (f : A →* G) (χ : A →* Kˣ) (b : A) :
    pushed f χ * MonoidAlgebra.single (f b) 1 = (χ b : K) • pushed f χ := by
  have h := congrArg (MonoidAlgebra.mapDomainAlgHom K K f) (projector_mul_single χ b)
  rw [map_mul, map_smul] at h
  simpa only [pushed, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single] using h

lemma pushed_central (f : A →* G) (χ : A →* Kˣ)
    (hf : ∀ a g, Commute (f a) g) (x : MonoidAlgebra K G) :
    Commute (pushed f χ) x := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    change pushed f χ * MonoidAlgebra.single g 1 = _
    rw [pushed_eq_sum, smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one, one_mul,
      (hf a g).eq]
  | add x y hx hy => exact hx.add_right hy
  | smul r x hx => exact hx.smul_right r

lemma lift_pushed (f : A →* G) (χ : A →* Kˣ) (ρ : G →* K)
    (hρ : ∀ a, ρ (f a) = (χ a : K)) (hc : (Fintype.card A : K) ≠ 0) :
    MonoidAlgebra.lift K K G ρ (pushed f χ) = 1 := by
  rw [pushed_eq_sum]
  simp [map_sum, MonoidAlgebra.lift_single, hρ, hc]

end KaplanskyCounterexample.CharacterIdempotents

end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.CharacterTwist
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.CharacterTwist
open MultipleHNN CharacterIdempotents
variable {A : Type u_1} {N : Type u_2} {C : Type u_3} {V : Type u_4} [CommGroup A] [Group N] [CommGroup C]
variable (ι : V → A →* N) (hi : ∀ v, Function.Injective (ι v)) (v₀ : V)
variable (α : V → A →* C)

lemma emb_injective [Fintype V] : Function.Injective (emb ι hi v₀ α) :=
  of_injective _ _ _

lemma conjugacy (v : V) (a : A) (c : C) :
    τ ι hi v₀ α v * emb ι hi v₀ α (ι v a, c) =
      emb ι hi v₀ α (ι v₀ a, c * α v a) * τ ι hi v₀ α v := by
  have h := letter_mul_of (source (C := C) ι) (target ι v₀ α) (edgeIso ι hi v₀ α)
    v (MonoidHom.ofInjective (src_injective ι hi v) (a,c))
  have he : edgeIso ι hi v₀ α v (MonoidHom.ofInjective (src_injective ι hi v) (a,c)) =
      MonoidHom.ofInjective (dst_injective ι hi v₀ α v) (a,c) := by
    exact congrArg (MonoidHom.ofInjective (dst_injective ι hi v₀ α v))
      ((MonoidHom.ofInjective (src_injective ι hi v)).symm_apply_apply (a,c))
  rw [he] at h
  exact h

lemma central_cyclic (c : C) (x : L ι hi v₀ α) :
    Commute (emb ι hi v₀ α (1,c)) x := by
  apply Commute.symm
  exact of_central (source (C := C) ι) (target ι v₀ α) (edgeIso ι hi v₀ α) (1,c)
    (by
      rintro ⟨n,d⟩
      change (n,d) * (1,c) = (1,c) * (n,d)
      ext <;> simp [mul_comm]) (by
      intro v
      exact ⟨(1,c), by simp [src]⟩) (by
      intro v
      change (dst ι v₀ α v) ((MonoidHom.ofInjective (src_injective ι hi v)).symm _) = _
      have he : (⟨(1,c), ⟨(1,c), by simp [src]⟩⟩ : source (C := C) ι v) =
          MonoidHom.ofInjective (src_injective ι hi v) (1,c) := by
        apply Subtype.ext
        change (1,c) = (src (C := C) ι v) (1,c)
        simp [src]
      rw [he, MulEquiv.symm_apply_apply]
      simp [dst]) x

variable {K : Type u_5} [Field K] [Fintype A] [Fintype C]
variable (ξ : C →* Kˣ)

omit [Fintype A] [Fintype C] in
lemma uInv_mul_u (v : V) : uInv (K := K) ι hi v₀ α v * u ι hi v₀ α v = 1 := by
  simp [uInv, u, ← MonoidAlgebra.one_def]

omit [Fintype A] in
lemma e_central (x : MonoidAlgebra K (L ι hi v₀ α)) : Commute (e ι hi v₀ α ξ) x :=
  pushed_central _ _ (central_cyclic ι hi v₀ α) x

omit [Fintype A] in
lemma cyclic_weight (n : N) (c : C) :
    e ι hi v₀ α ξ * MonoidAlgebra.of K _ (emb ι hi v₀ α (n,c)) =
      (ξ c : K) • (e ι hi v₀ α ξ * MonoidAlgebra.of K _ (emb ι hi v₀ α (n,1))) := by
  have hfac : emb ι hi v₀ α (n,c) =
      zHom ι hi v₀ α c * emb ι hi v₀ α (n,1) := by
    change _ = emb ι hi v₀ α (1,c) * _
    rw [← map_mul]
    congr 1
    ext <;> simp
  rw [hfac, map_mul, ← mul_assoc]
  rw [show e ι hi v₀ α ξ * MonoidAlgebra.of K _ (zHom ι hi v₀ α c) =
    (ξ c : K) • e ι hi v₀ α ξ from pushed_mul_single _ _ c]
  rw [smul_mul_assoc]

omit [Fintype A] [Fintype C] in
lemma twisted_single (v : V) (a : A) :
    u (K := K) ι hi v₀ α v * MonoidAlgebra.of K _ (localHom ι hi v₀ α v a) *
        uInv ι hi v₀ α v =
      MonoidAlgebra.of K _ (emb ι hi v₀ α (ι v₀ a, α v a)) := by
  simp only [u, uInv, localHom, MonoidHom.comp_apply, MonoidHom.inl_apply, ← map_mul]
  congr 1
  rw [conjugacy, mul_assoc, mul_inv_cancel, mul_one, one_mul]

lemma twisted_average (v : V) :
    e ι hi v₀ α ξ * (u ι hi v₀ α v * P (K := K) ι hi v₀ α v * uInv ι hi v₀ α v) =
      e ι hi v₀ α ξ * Q ι hi v₀ α ξ v := by
  unfold P Q
  rw [pushed_eq_sum, pushed_eq_sum]
  simp only [MonoidHom.one_apply, Units.val_one, inv_one, MonoidHom.inv_apply,
    MonoidHom.comp_apply, Units.val_inv_eq_inv_val, inv_inv]
  simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change e ι hi v₀ α ξ * (u ι hi v₀ α v * MonoidAlgebra.of K _ (localHom ι hi v₀ α v a) *
      uInv ι hi v₀ α v) = _
  rw [twisted_single, cyclic_weight]
  simp [localHom, MonoidAlgebra.of_apply, ← mul_smul_comm]

lemma conjugate_projection (v : V) :
    u ι hi v₀ α v * (e ι hi v₀ α ξ * P (K := K) ι hi v₀ α v) * uInv ι hi v₀ α v =
      e ι hi v₀ α ξ * Q ι hi v₀ α ξ v := by
  rw [← mul_assoc, (e_central ι hi v₀ α ξ (u ι hi v₀ α v)).eq.symm,
    mul_assoc, mul_assoc, ← mul_assoc (u ι hi v₀ α v)]
  exact twisted_average ι hi v₀ α ξ v

end KaplanskyCounterexample.CharacterTwist

end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.AlgebraicPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.AlgebraicPacking

variable {R : Type u_1} {m : Type u_2} {t : Type u_3} [Ring R] [Fintype m] [Fintype t]

theorem packing_identities
    (U C : Matrix m t R) (T J : Matrix t m R) (P F : Matrix t t R)
    (E : Matrix m m R)
    (hUP : U * P = U) (hPT : P * T = T) (hUT : U * T = 1)
    (hJC : J * C = F * P) (hEE : E * E = E) (hFF : F * F = F)
    (hEU : E * U = U * F) (hFT : F * T = T * E)
    (hJE : J * E = J) (hEC : E * C = C)
    (hCF : C * F = C) (hFJ : F * J = J) :
    aMat U J E * bMat C T E = 1 ∧
      J * (bMat C T E * aMat U J E - 1) * C = F * (T * U - P) := by
  have hUJCT : U * J * (C * T) = E := by
    calc
      U * J * (C * T) = U * (J * C) * T := by simp only [Matrix.mul_assoc]
      _ = U * (F * P) * T := by rw [hJC]
      _ = E * (U * (P * T)) := by rw [← Matrix.mul_assoc U, ← hEU]; simp only [Matrix.mul_assoc]
      _ = E := by rw [hPT, hUT, Matrix.mul_one]
  have hUJE : (U * J) * E = U * J := by rw [Matrix.mul_assoc, hJE]
  have hECT : E * (C * T) = C * T := by rw [← Matrix.mul_assoc, hEC]
  have hproj : (1 - E) * (1 - E) = 1 - E := by
    noncomm_ring [hEE]
  constructor
  · unfold aMat bMat
    rw [mul_add, add_mul, add_mul, hUJCT, mul_sub, Matrix.mul_one,
      hUJE, sub_self, sub_mul, Matrix.one_mul, hECT, sub_self, hproj]
    abel
  · have hCTE : C * T * E = C * T := by
      rw [Matrix.mul_assoc, ← hFT, ← Matrix.mul_assoc, hCF]
    have hEUJ : E * (U * J) = U * J := by
      rw [← Matrix.mul_assoc, hEU, Matrix.mul_assoc, hFJ]
    have hdelta : bMat C T E * aMat U J E - 1 = C * T * (U * J) - E := by
      unfold aMat bMat
      rw [mul_add, add_mul, add_mul, mul_sub, Matrix.mul_one, hCTE,
        sub_self, sub_mul, Matrix.one_mul, hEUJ, sub_self, hproj]
      abel
    have hsandwich : J * (C * T * (U * J)) * C = F * (T * U) := by
      calc
        J * (C * T * (U * J)) * C = (J * C) * T * U * (J * C) := by
          simp only [Matrix.mul_assoc]
        _ = (F * P) * T * U * (F * P) := by rw [hJC]
        _ = F * T * (U * F) * P := by
          rw [Matrix.mul_assoc F P T, hPT]
          simp only [Matrix.mul_assoc]
        _ = F * (T * E) * (U * P) := by
          rw [← hEU]
          simp only [Matrix.mul_assoc]
        _ = F * (F * T) * U := by rw [hUP, ← hFT]
        _ = F * (T * U) := by
          rw [← Matrix.mul_assoc F F T, hFF, Matrix.mul_assoc]
    rw [hdelta, Matrix.mul_sub, Matrix.sub_mul, hsandwich, hJE, hJC, Matrix.mul_sub]

/-- The rank defect used after specialization to the subgroup algebra. -/
theorem transpose_mul_ne_one {K : Type u_4} {m : Type u_5} {t : Type u_6} [Field K] [Fintype m] [Fintype t]
    (X : Matrix m t K) (hlt : Fintype.card m < Fintype.card t) :
    X.transpose * X ≠ 1 := by
  intro heq
  have h := (Matrix.rank_mul_le_right X.transpose X).trans (Matrix.rank_le_card_height X)
  rw [heq, Matrix.rank_one] at h
  omega

omit [Fintype t] in
lemma Jpack_mul_Cpack (slot : t → m) (u uInv D Q : t → R)
    (hlu : ∀ v, uInv v * u v = 1)
    (hD : ∀ v, D v * D v = D v)
    (hconj : ∀ v, u v * D v * uInv v = Q v)
    (horth : ∀ v w, v ≠ w → slot v = slot w → Q v * Q w = 0) :
    Jpack slot uInv D * Cpack slot u D = Matrix.diagonal D := by
  have hleft (v : t) : D v * uInv v = uInv v * Q v := by
    rw [← hconj, ← mul_assoc, ← mul_assoc, hlu, one_mul]
  have hright (v : t) : u v * D v = Q v * u v := by
    rw [← hconj, mul_assoc (u v * D v), hlu, mul_one]
  ext v w
  rw [Matrix.mul_apply]
  by_cases hvw : v = w
  · subst w
    rw [Matrix.diagonal_apply_eq]
    rw [Finset.sum_eq_single (slot v)]
    · simp only [Jpack, Cpack, ite_true]
      rw [mul_assoc, ← mul_assoc (uInv v), hlu, one_mul, hD]
    · intro i _ hi
      simp [Jpack, Cpack, Ne.symm hi]
    · simp
  · rw [Matrix.diagonal_apply_ne _ hvw]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hvi : slot v = i <;> by_cases hwi : slot w = i <;>
      simp only [Jpack, Cpack, hvi, hwi, ite_true, ite_false, mul_zero, zero_mul]
    rw [hleft, hright, mul_assoc, ← mul_assoc (Q v), horth v w hvw (hvi.trans hwi.symm),
      zero_mul, mul_zero]

end KaplanskyCounterexample.AlgebraicPacking

end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.Rectangular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped BigOperators Classical
namespace KaplanskyCounterexample.Rectangular
variable {K : Type u_1} {R : Type u_2} {V : Type u_3} {F : Type u_4} {m : Type u_5} [CommRing K] [Ring R] [Algebra K R]
variable [Fintype V] [Fintype F] [Fintype m]

omit [Fintype m] in
theorem identities (X : Matrix m V K) (P : V → R) (L : F → R)
    (Inc : F → Finset V)
    (hP : ∀ v, P v * P v = P v)
    (hdec : ∀ v, P v = 1 + ∑ f : {f : F // v ∈ Inc f}, (L f - 1))
    (hglobal : X * X.transpose = 1)
    (hlocal : ∀ f i j, ∑ v ∈ Inc f, X i v * X j v = 0) :
    U X P * Matrix.diagonal P = U X P ∧
      Matrix.diagonal P * T X P = T X P ∧ U X P * T X P = 1 := by
  constructor
  · ext i v
    simp [U, Matrix.mul_diagonal, hP]
  constructor
  · ext v i
    simp [T, Matrix.diagonal_mul, hP]
  · ext i j
    change (∑ v, (X i v • P v) * (X j v • P v)) = (1 : Matrix m m R) i j
    simp_rw [smul_mul_smul_comm, hP, hdec, smul_add, Finset.smul_sum]
    rw [Finset.sum_add_distrib, ← Finset.sum_smul]
    have hh := congrFun (congrFun hglobal i) j
    change ∑ v, X i v * X j v = (1 : Matrix m m K) i j at hh
    rw [hh]
    have hzero : ∑ v : V, ∑ f : {f : F // v ∈ Inc f},
        (X i v * X j v) • (L f.val - 1) = 0 := by
      have hv (v : V) : (∑ f : {f : F // v ∈ Inc f},
          (X i v * X j v) • (L f.val - 1)) =
          ∑ f : F, if v ∈ Inc f then (X i v * X j v) • (L f - 1) else 0 := by
        rw [← Finset.sum_filter]
        exact (Finset.sum_subtype (p := fun f : F => v ∈ Inc f)
          (Finset.univ.filter (fun f : F => v ∈ Inc f)) (by simp)
          (fun f : F => (X i v * X j v) • (L f - 1))).symm
      simp_rw [hv]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro f _
      rw [← Finset.sum_filter]
      have hf : Finset.univ.filter (fun v => v ∈ Inc f) = Inc f := by ext; simp
      rw [hf, ← Finset.sum_smul, hlocal, zero_smul]
    rw [hzero, add_zero]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

end KaplanskyCounterexample.Rectangular
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.AlgebraicCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.CharacterTwist
open CharacterIdempotents AlgebraicPacking
variable {A : Type u_1} {N : Type u_2} {C : Type u_3} {V : Type u_4} {m : Type u_5} {K : Type u_6} [CommGroup A] [Group N] [CommGroup C]
variable [Field K] [Fintype A] [Fintype C] [Fintype V] [Fintype m]
variable (ι : V → A →* N) (hi : ∀ v, Function.Injective (ι v)) (v₀ : V)
variable (α : V → A →* C) (ξ : C →* Kˣ)

lemma map_pushed {G : Type u_7} {H : Type u_8} [Group G] [Group H]
    (f : G →* H) (g : A →* G) (χ : A →* Kˣ) :
    MonoidAlgebra.mapDomainAlgHom K K f (pushed g χ) = pushed (f.comp g) χ := by
  unfold pushed
  rw [MonoidAlgebra.mapDomainAlgHom_comp]
  rfl

lemma defect_ne_zero (X : Matrix m V K) (hlt : Fintype.card m < Fintype.card V)
    (hA : (Fintype.card A : K) ≠ 0) (hC : (Fintype.card C : K) ≠ 0) :
    Matrix.diagonal (fun _ : V => e ι hi v₀ α ξ) *
      (Rectangular.T X (P ι hi v₀ α) * Rectangular.U X (P ι hi v₀ α) -
        Matrix.diagonal (P ι hi v₀ α)) ≠ 0 := by
  let pH (v : V) : MonoidAlgebra K (N × C) :=
    pushed ((MonoidHom.inl N C).comp (ι v)) 1
  let eH : MonoidAlgebra K (N × C) := pushed (MonoidHom.inr N C) ξ
  let f := MonoidAlgebra.mapDomainAlgHom K K (emb ι hi v₀ α)
  have hf : Function.Injective f := MonoidAlgebra.mapDomain_injective (emb_injective ι hi v₀ α)
  have hp (v : V) : f (pH v) = P ι hi v₀ α v := map_pushed _ _ _
  have he : f eH = e ι hi v₀ α ξ := map_pushed _ _ _
  let ρ : (N × C) →* K := (Units.coeHom K).comp (ξ.comp (MonoidHom.snd N C))
  let ε := MonoidAlgebra.lift K K (N × C) ρ
  have hεp (v : V) : ε (pH v) = 1 := by
    apply lift_pushed _ _ ρ _ hA
    intro a
    simp [ρ]
  have hεe : ε eH = 1 := by
    apply lift_pushed _ _ ρ _ hC
    intro c
    rfl
  intro hz
  apply transpose_mul_ne_one X hlt
  ext v w
  have hzvw := congrFun (congrFun hz v) w
  rw [Matrix.diagonal_mul] at hzvw
  change e ι hi v₀ α ξ * ((∑ i : m, (X i v • P ι hi v₀ α v) *
    (X i w • P ι hi v₀ α w)) - (if v = w then P ι hi v₀ α v else 0)) = 0 at hzvw
  have hpre : eH * ((∑ i : m, (X i v • pH v) * (X i w • pH w)) -
      (if v = w then pH v else 0)) = 0 := by
    apply hf
    simp only [map_mul, map_sub, map_sum, map_smul, hp, he, map_zero]
    simpa only [apply_ite, map_zero, hp] using hzvw
  have hs := congrArg ε hpre
  simp only [map_mul, map_sub, map_sum, map_smul, hεp, hεe, one_mul,
    smul_eq_mul, mul_one, map_zero, apply_ite] at hs
  apply sub_eq_zero.mp
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, apply_ite] using hs

end KaplanskyCounterexample.CharacterTwist
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PackingFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.AlgebraicPacking
variable {R : Type u_1} {m : Type u_2} {t : Type u_3} [Ring R] [Fintype m] [Fintype t]

theorem prescribed_packing_products (U : Matrix m t R) (T : Matrix t m R)
    (p q u uInv : t → R) (slot : t → m) (e : R)
    (he : e * e = e) (hc : ∀ x : R, Commute e x)
    (hp : ∀ v, p v * p v = p v)
    (hUP : U * Matrix.diagonal p = U) (hPT : Matrix.diagonal p * T = T)
    (hUT : U * T = 1)
    (hlu : ∀ v, uInv v * u v = 1)
    (hconj : ∀ v, u v * (e * p v) * uInv v = e * q v)
    (horth : ∀ v w, v ≠ w → slot v = slot w → q v * q w = 0)
    (hdefect : Matrix.diagonal (fun _ : t => e) * (T * U - Matrix.diagonal p) ≠ 0) :
    let a := aMat U (Jpack slot uInv (fun v => e*p v)) (Matrix.diagonal (fun _ => e))
    let b := bMat (Cpack slot u (fun v => e*p v)) T (Matrix.diagonal (fun _ => e))
    a*b=1 ∧ b*a≠1 := by
  let D : t → R := fun v => e * p v
  let C := Cpack slot u D
  let J := Jpack slot uInv D
  let E : Matrix m m R := Matrix.diagonal (fun _ => e)
  let F : Matrix t t R := Matrix.diagonal (fun _ => e)
  have hD (v : t) : D v * D v = D v := by
    dsimp [D]
    calc
      e * p v * (e * p v) = e * (e * p v) * p v := by
        rw [mul_assoc, ← mul_assoc (p v), (hc (p v)).eq.symm]; simp only [mul_assoc]
      _ = e * p v := by rw [← mul_assoc e e, he, mul_assoc, hp]
  have horth' (v w : t) (hne : v ≠ w) (hs : slot v = slot w) :
      (e * q v) * (e * q w) = 0 := by
    calc
      e * q v * (e * q w) = (e * e) * (q v * q w) := by
        rw [mul_assoc, ← mul_assoc (q v), (hc (q v)).eq.symm]; simp only [mul_assoc]
      _ = 0 := by rw [horth v w hne hs, mul_zero]
  have hJC : J * C = F * Matrix.diagonal p := by
    rw [show F * Matrix.diagonal p = Matrix.diagonal D by
      simp [F, D, Matrix.diagonal_mul_diagonal]]
    exact Jpack_mul_Cpack slot u uInv D (fun v => e * q v) hlu hD hconj horth'
  have hEE : E * E = E := by simp [E, Matrix.diagonal_mul_diagonal, he]
  have hFF : F * F = F := by simp [F, Matrix.diagonal_mul_diagonal, he]
  have hEU : E * U = U * F := by
    ext i v
    simpa [E, F, Matrix.diagonal_mul, Matrix.mul_diagonal] using (hc (U i v)).eq
  have hFT : F * T = T * E := by
    ext v i
    simpa [E, F, Matrix.diagonal_mul, Matrix.mul_diagonal] using (hc (T v i)).eq
  have hC (i : m) (v : t) : e * C i v = C i v := by
    dsimp [C, Cpack, D]
    split_ifs
    · rw [← mul_assoc, (hc (u v)).eq, mul_assoc, ← mul_assoc e e, he]
    · exact mul_zero e
  have hJ (v : t) (i : m) : e * J v i = J v i := by
    dsimp [J, Jpack, D]
    split_ifs
    · rw [← mul_assoc, ← mul_assoc e e, he]
    · exact mul_zero e
  have hJE : J * E = J := by
    ext v i
    simp only [E, Matrix.mul_diagonal]
    rw [← (hc (J v i)).eq, hJ]
  have hEC : E * C = C := by ext i v; simpa [E, Matrix.diagonal_mul] using hC i v
  have hCF : C * F = C := by
    ext i v
    simp only [F, Matrix.mul_diagonal]
    rw [← (hc (C i v)).eq, hC]
  have hFJ : F * J = J := by ext v i; simpa [F, Matrix.diagonal_mul] using hJ v i
  obtain ⟨hab, hdelta⟩ := packing_identities U C T J (Matrix.diagonal p) F E
    hUP hPT hUT hJC hEE hFF hEU hFT hJE hEC hCF hFJ
  refine ⟨hab, ?_⟩
  intro hba
  apply hdefect
  rw [hba, sub_self, Matrix.mul_zero, Matrix.zero_mul] at hdelta
  exact hdelta.symm

end KaplanskyCounterexample.AlgebraicPacking
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.CharacterFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.CharacterTwist
open CharacterIdempotents AlgebraicPacking
variable {A : Type u_1} {N : Type u_2} {C : Type u_3} {V : Type u_4} {m : Type u_5} {K : Type u_6} [CommGroup A] [Group N] [CommGroup C]
variable [Field K] [Fintype A] [Fintype C] [Fintype V] [Fintype m]
variable (ι : V → A →* N) (hi : ∀ v, Function.Injective (ι v)) (v₀ : V)
variable (α : V → A →* C) (ξ : C →* Kˣ)

theorem matrix_products {F : Type u_7} [Fintype F]
    (X : Matrix m V K) (Inc : F → Finset V)
    (lineSum : F → MonoidAlgebra K (L ι hi v₀ α))
    (hdec : ∀ v, P (K := K) ι hi v₀ α v =
      1 + ∑ f : {f : F // v ∈ Inc f}, (lineSum f.val - 1))
    (hglobal : X * X.transpose = 1)
    (hlocal : ∀ f i j, ∑ v ∈ Inc f, X i v * X j v = 0)
    (hlt : Fintype.card m < Fintype.card V)
    (hA : (Fintype.card A : K) ≠ 0) (hC : (Fintype.card C : K) ≠ 0)
    (slot : V → m) (hξ : Function.Injective ξ)
    (hα : ∀ v w, v ≠ w → slot v = slot w → α v ≠ α w) :
    aMatrix ι hi v₀ α ξ X slot * bMatrix ι hi v₀ α ξ X slot=1 ∧
    bMatrix ι hi v₀ α ξ X slot * aMatrix ι hi v₀ α ξ X slot≠1 := by
  have hp (v : V) : P (K := K) ι hi v₀ α v * P ι hi v₀ α v = P ι hi v₀ α v :=
    pushed_idempotent _ _ hA
  obtain ⟨hUP,hPT,hUT⟩ := Rectangular.identities X (P ι hi v₀ α) lineSum Inc hp hdec hglobal hlocal
  apply prescribed_packing_products (Rectangular.U X (P ι hi v₀ α))
    (Rectangular.T X (P ι hi v₀ α)) (P ι hi v₀ α) (Q ι hi v₀ α ξ)
    (u ι hi v₀ α) (uInv ι hi v₀ α) slot (e ι hi v₀ α ξ)
    (pushed_idempotent _ _ hC) (e_central ι hi v₀ α ξ) hp hUP hPT hUT
    (uInv_mul_u ι hi v₀ α) (conjugate_projection ι hi v₀ α ξ)
    _ (defect_ne_zero ι hi v₀ α ξ X hlt hA hC)
  intro v w hvw hslot
  apply pushed_orthogonal
  intro heq
  apply hα v w hvw hslot
  apply MonoidHom.ext
  intro a
  apply hξ
  have heq' := congrArg (fun χ : A →* Kˣ => χ a) heq
  exact inv_injective heq'

end KaplanskyCounterexample.CharacterTwist
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.FiniteBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteBlock
variable {m : Type u_1} {C : Type u_2} [CommGroup C]

variable {K : Type u_5} [Field K] [Fintype m] [Fintype C]
variable (ξ : C →* Kˣ)

omit [Fintype m] in
lemma coordinate_ne (hξ : ξ ≠ 1) {i j : m} (hij : i ≠ j) :
    coordinate ξ i ≠ coordinate ξ j := by
  obtain ⟨c,hc⟩ : ∃ c, ξ c ≠ 1 := by
    by_contra! h
    exact hξ (MonoidHom.ext h)
  intro h
  have hh := congrArg (fun χ : (m → C) →* Kˣ => χ (Function.update 1 i c)) h
  simp [coordinate, Function.update_of_ne hij.symm] at hh
  exact hc hh

open CharacterIdempotents

omit [Fintype m] [Fintype C] in
lemma permElt_inv_mul (σ : Equiv.Perm m) :
    permElt (K := K) (C := C) σ⁻¹ * permElt σ = 1 := by
  simp [permElt, ← MonoidAlgebra.one_def]

lemma p_ne_zero (hc : (Fintype.card (m → C) : K) ≠ 0) (i : m) : p ξ i ≠ 0 :=
  pushed_ne_zero _ SemidirectProduct.inl_injective _ hc
lemma p_idem (hc : (Fintype.card (m → C) : K) ≠ 0) (i : m) : p ξ i * p ξ i = p ξ i :=
  pushed_idempotent _ _ hc
lemma p_orth (hξ : ξ ≠ 1) {i j : m} (hij : i ≠ j) : p ξ i * p ξ j = 0 :=
  pushed_orthogonal _ _ _ (coordinate_ne ξ hξ hij)

lemma translated (σ : Equiv.Perm m) (i : m) :
    permElt σ * p ξ i * permElt σ⁻¹ = p ξ (σ i) := by
  unfold p
  rw [pushed_eq_sum, pushed_eq_sum]
  simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  calc
    _ = ∑ w : m → C, MonoidAlgebra.single (SemidirectProduct.inl (permAction σ w))
        ((coordinate ξ (σ i) (permAction σ w) : K)⁻¹) := by
      apply Finset.sum_congr rfl
      intro w _
      simp only [permElt, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
        one_mul, mul_one]
      rw [← SemidirectProduct.inl_aut]
      congr 1
      simp [coordinate, permAction]
    _ = _ := Equiv.sum_comp (permAction σ).toEquiv (fun w : m → C =>
      (MonoidAlgebra.single (SemidirectProduct.inl w : Auxiliary m C)
        ((coordinate ξ (σ i) w : K)⁻¹)))

end KaplanskyCounterexample.FiniteBlock
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.TranslatedUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.TranslatedUnits
variable {R : Type u_1} {m : Type u_2} [Ring R]
variable (s t : m → R) (p : R)

variable (hts : ∀ i, t i * s i = 1) (hpp : p * p = p)
include hts hpp

lemma unit_middle (i j k : m) : unit s t p i j * unit s t p j k = unit s t p i k := by
  simp only [unit, mul_assoc]
  rw [← mul_assoc (t j), hts, one_mul, ← mul_assoc p p, hpp]

lemma products (horth : ∀ j k, j ≠ k → unit s t p j j * unit s t p k k = 0)
    (i j k r : m) :
    unit s t p i j * unit s t p k r = if j = k then unit s t p i r else 0 := by
  by_cases hjk : j = k
  · subst k
    simpa using unit_middle s t p hts hpp i j r
  · rw [ite_eq_right hjk]
    calc
      _ = (unit s t p i j * unit s t p j j) *
          (unit s t p k k * unit s t p k r) := by
        rw [unit_middle s t p hts hpp, unit_middle s t p hts hpp]
      _ = unit s t p i j * (unit s t p j j * unit s t p k k) * unit s t p k r := by
        simp only [mul_assoc]
      _ = 0 := by rw [horth j k hjk, mul_zero, zero_mul]

omit hpp in
lemma unit_ne_zero (hp : p ≠ 0) (i j : m) : unit s t p i j ≠ 0 := by
  intro h
  apply hp
  have hh : t i * unit s t p i j * s j = p := by
    simp only [unit, ← mul_assoc]
    rw [hts, one_mul, mul_assoc p, hts, mul_one]
  rw [h, mul_zero, zero_mul] at hh
  exact hh.symm

end KaplanskyCounterexample.TranslatedUnits
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.MatrixBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.MatrixBlock
variable {S : Type u_1} {R : Type u_2} {m : Type u_3} [Ring S] [Ring R] [Fintype m]
variable (f : S →+* R) (q : m → m → R)

lemma block_sub (X Y : Matrix m m S) : block f q (X - Y) = block f q X - block f q Y := by
  simp [block, sub_mul, Finset.sum_sub_distrib]

variable (hqq : ∀ i j k r, q i j * q k r = if j = k then q i r else 0)
variable (hcomm : ∀ x i j, Commute (f x) (q i j))
include hqq hcomm

lemma block_mul (X Y : Matrix m m S) : block f q (X * Y) = block f q X * block f q Y := by
  have hterm (i j k r : m) :
      (f (X i j) * q i j) * (f (Y k r) * q k r) =
        if j = k then f (X i j * Y k r) * q i r else 0 := by
    calc
      _ = f (X i j * Y k r) * (q i j * q k r) := by
        rw [map_mul, ← mul_assoc, mul_assoc (f (X i j)),
          (hcomm (Y k r) i j).eq.symm]
        simp only [mul_assoc]
      _ = _ := by rw [hqq]; split_ifs <;> simp
  have hmulij (i j : m) : (f (X i j) * q i j) * block f q Y =
      ∑ r, f (X i j * Y j r) * q i r := by
    simp only [block, Finset.mul_sum, hterm]
    rw [Finset.sum_comm]
    simp
  symm
  calc
    block f q X * block f q Y = ∑ i, ∑ j, (f (X i j) * q i j) * block f q Y := by
      change (∑ i, ∑ j, f (X i j) * q i j) * block f q Y = _
      simp only [Finset.sum_mul]
    _ = ∑ i, ∑ j, ∑ r, f (X i j * Y j r) * q i r := by simp_rw [hmulij]
    _ = block f q (X * Y) := by
      simp only [block, Matrix.mul_apply, map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm

lemma block_sandwich (X : Matrix m m S) (i j : m) :
    q i i * block f q X * q j j = f (X i j) * q i j := by
  have hterm (k r : m) : q i i * (f (X k r) * q k r) * q j j =
      if i = k then if r = j then f (X k r) * q i j else 0 else 0 := by
    calc
      _ = f (X k r) * (q i i * q k r * q j j) := by
        rw [← mul_assoc, (hcomm (X k r) i i).eq.symm]
        simp only [mul_assoc]
      _ = _ := by
        by_cases hik : i = k <;> by_cases hrj : r = j <;>
          simp [hqq, hik, hrj]

  simp only [block, Finset.mul_sum, Finset.sum_mul, hterm]
  simp

lemma block_injective (hpure : ∀ x i j, f x * q i j = 0 → x = 0) :
    Function.Injective (block f q) := by
  intro X Y h
  have hz : block f q (X - Y) = 0 := by rw [block_sub, h, sub_self]
  have hXY : X - Y = 0 := by
    ext i j
    apply hpure _ i j
    rw [← block_sandwich f q hqq hcomm, hz, mul_zero, zero_mul]
  exact sub_eq_zero.mp hXY

end KaplanskyCounterexample.MatrixBlock
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.ProductAlgebras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.ProductAlgebras
variable {K : Type u_1} {G : Type u_2} {H : Type u_3} [Field K] [Group G] [Group H]

lemma left_right_commute (x : MonoidAlgebra K G) (y : MonoidAlgebra K H) :
    Commute (leftMap x) (rightMap y) := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    induction y using MonoidAlgebra.induction_on with
    | of h =>
      change _ * _ = _ * _
      simp [leftMap, rightMap, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single]
    | add y z hy hz => simpa only [map_add] using hy.add_right hz
    | smul c y hy => simpa only [map_smul] using hy.smul_right c
  | add x z hx hz => simpa only [map_add] using hx.add_left hz
  | smul c x hx => simpa only [map_smul] using hx.smul_left c

lemma product_coeff (x : MonoidAlgebra K G) (y : MonoidAlgebra K H) (g : G) (h : H) :
    (leftMap x * rightMap y).coeff (g,h) = x.coeff g * y.coeff h := by
  induction x using MonoidAlgebra.induction_on with
  | of a =>
    induction y using MonoidAlgebra.induction_on with
    | of b =>
      by_cases hag : a = g <;> by_cases hbh : b = h <;>
        simp [leftMap, rightMap, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
          hag, hbh, Prod.ext_iff]
    | add y z hy hz =>
      simp only [map_add, mul_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, hy, hz]
    | smul c y hy =>
      simp only [map_smul, mul_smul_comm, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
        smul_eq_mul, hy]
      ring
  | add x z hx hz =>
    simp only [map_add, add_mul, MonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hz]
  | smul c x hx =>
    simp only [map_smul, smul_mul_assoc, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
      smul_eq_mul, hx]
    ring

lemma product_ne_zero {x : MonoidAlgebra K G} {y : MonoidAlgebra K H}
    (hx : x ≠ 0) (hy : y ≠ 0) : leftMap x * rightMap y ≠ 0 := by
  obtain ⟨g,hg⟩ : ∃ g, x.coeff g ≠ 0 := by
    by_contra! h
    apply hx
    ext g
    exact h g
  obtain ⟨h,hh⟩ : ∃ h, y.coeff h ≠ 0 := by
    by_contra! h
    apply hy
    ext a
    exact h a
  intro he
  have he' := congrArg (fun z : MonoidAlgebra K (G × H) => z.coeff (g,h)) he
  rw [product_coeff] at he'
  exact mul_ne_zero hg hh he'

end KaplanskyCounterexample.ProductAlgebras
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.ScalarWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteBlock
variable {K : Type u_1} {C : Type u_2} {m : Type u_3} {L : Type u_4} [Field K] [CommGroup C] [Group L]
variable [Fintype m] [Fintype C]
variable (ξ : C →* Kˣ) (i₀ : m)

lemma matrixUnit_diag (i : m) : matrixUnit ξ i₀ i i = p ξ i := by
  simpa only [matrixUnit, TranslatedUnits.unit, Equiv.swap_apply_left] using
    translated ξ (Equiv.swap i₀ i) i₀

lemma matrixUnit_mul (hc : (Fintype.card (m → C) : K) ≠ 0) (hξ : ξ ≠ 1)
    (i j k r : m) :
    matrixUnit ξ i₀ i j * matrixUnit ξ i₀ k r =
      if j = k then matrixUnit ξ i₀ i r else 0 := by
  apply TranslatedUnits.products _ _ _
    (fun i => permElt_inv_mul (Equiv.swap i₀ i)) (p_idem ξ hc i₀)
  intro j k hjk
  change matrixUnit ξ i₀ j j * matrixUnit ξ i₀ k k = 0
  rw [matrixUnit_diag, matrixUnit_diag]
  exact p_orth ξ hξ hjk

lemma matrixUnit_ne_zero (hc : (Fintype.card (m → C) : K) ≠ 0) (i j : m) :
    matrixUnit ξ i₀ i j ≠ 0 :=
  TranslatedUnits.unit_ne_zero _ _ _ (fun i => permElt_inv_mul (Equiv.swap i₀ i))
    (p_ne_zero ξ hc i₀) i j

end KaplanskyCounterexample.FiniteBlock
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.ScalarFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.MatrixBlock
variable {S : Type u_1} {R : Type u_2} {m : Type u_3} [Ring S] [Ring R] [Fintype m]
variable (f : S →+* R) (q : m → m → R)

variable (hqq : ∀ i j k r, q i j * q k r = if j = k then q i r else 0)
variable (hcomm : ∀ x i j, Commute (f x) (q i j))

include hqq hcomm in
theorem prescribed_scalar_products
    (hpure : ∀ x i j, f x * q i j = 0 → x = 0)
    (a b : Matrix m m S) (hab : a * b = 1) (hba : b * a ≠ 1) :
    output f q a * output f q b = 1 ∧ output f q b * output f q a ≠ 1 := by
  let e := block f q 1
  let a' := 1 - e + block f q a
  let b' := 1 - e + block f q b
  have he : e * e = e := by rw [← block_mul f q hqq hcomm, mul_one]
  have hea : e * block f q a = block f q a := by rw [← block_mul f q hqq hcomm, one_mul]
  have hae : block f q a * e = block f q a := by rw [← block_mul f q hqq hcomm, mul_one]
  have heb : e * block f q b = block f q b := by rw [← block_mul f q hqq hcomm, one_mul]
  have hbe : block f q b * e = block f q b := by rw [← block_mul f q hqq hcomm, mul_one]
  have hab' : block f q a * block f q b = e := by rw [← block_mul f q hqq hcomm, hab]
  change a' * b' = 1 ∧ b' * a' ≠ 1
  refine ⟨?_,?_⟩
  · dsimp [a',b']
    noncomm_ring [he, hea, hae, heb, hbe, hab']
  · intro h
    have h' : block f q b * block f q a = e := by
      apply add_left_cancel (a := 1 - e)
      calc
        1 - e + block f q b * block f q a =
            (1 - e + block f q b) * (1 - e + block f q a) := by
          noncomm_ring [he, hea, hae, heb, hbe]
        _ = 1 := h
        _ = 1 - e + e := by abel
    apply hba
    apply block_injective f q hqq hcomm hpure
    rw [block_mul f q hqq hcomm]
    exact h'

end KaplanskyCounterexample.MatrixBlock

namespace KaplanskyCounterexample.FiniteBlock
variable {K : Type u_4} {C : Type u_5} {m : Type u_6} {L : Type u_7} [Field K] [CommGroup C] [Group L]
variable [Fintype m] [Fintype C]
variable (ξ : C →* Kˣ) (i₀ : m)

theorem output_products (hc : (Fintype.card (m → C) : K) ≠ 0) (hξ : ξ ≠ 1)
    (a b : Matrix m m (MonoidAlgebra K L)) (hab : a * b = 1) (hba : b * a ≠ 1) :
    output ξ i₀ a * output ξ i₀ b=1 ∧ output ξ i₀ b*output ξ i₀ a≠1 := by
  let f := (ProductAlgebras.leftMap (K := K) (G := L) (H := Auxiliary m C)).toRingHom
  let q (i j : m) := ProductAlgebras.rightMap (G := L) (matrixUnit ξ i₀ i j)
  have hqq (i j k r : m) : q i j * q k r = if j = k then q i r else 0 := by
    dsimp [q]
    rw [← map_mul, matrixUnit_mul ξ i₀ hc hξ]
    split_ifs <;> simp
  have hcomm (x : MonoidAlgebra K L) (i j : m) : Commute (f x) (q i j) :=
    ProductAlgebras.left_right_commute x _
  have hpure (x : MonoidAlgebra K L) (i j : m) : f x * q i j = 0 → x = 0 := by
    intro he
    by_contra hx
    exact ProductAlgebras.product_ne_zero hx (matrixUnit_ne_zero ξ i₀ hc i j) he
  exact MatrixBlock.prescribed_scalar_products f q hqq hcomm hpure a b hab hba

end KaplanskyCounterexample.FiniteBlock
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.ChosenCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.ChosenCriterion
open AssignedDevelopment CharacterIdempotents
variable {K V F m : Type} [Field K] [CharP K 2]
variable [Fintype V] [Fintype F] [Fintype m]
variable (ℓ : ℕ) [Fact ℓ.Prime]

attribute [local instance] OAI.KaplanskyCounterexample.ChosenCriterion.modulusNeZero
variable (Inc : F → Finset V)
variable (assign : ∀ v, {f : F // v ∈ Inc f} ≃ Option (ZMod ℓ))
variable (hInc : ∀ f, (Inc f).Nonempty)
variable (hg : 12 ≤ (Planar.incidenceGraph (fun v f => v ∈ Inc f)).egirth)
variable (v₀ : V) (α : V → GluedGroup.PointGroup ℓ →* Multiplicative (ZMod ℓ))

variable {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (X : Matrix m V K)
variable (i₀ : m) (slot : V → m)

include hζ in
lemma products (hodd : Odd ℓ)
    (hlt : Fintype.card m < Fintype.card V)
    (hglobal : X * X.transpose = -1)
    (hlocal : ∀ f i j, ∑ v ∈ Inc f, X i v * X j v = 0)
    (hα : ∀ v w, v ≠ w → slot v = slot w → α v ≠ α w) :
    aOut ℓ Inc assign hInc hg v₀ α hζ X i₀ slot *
      bOut ℓ Inc assign hInc hg v₀ α hζ X i₀ slot=1 ∧
    bOut ℓ Inc assign hInc hg v₀ α hζ X i₀ slot *
      aOut ℓ Inc assign hInc hg v₀ α hζ X i₀ slot≠1 := by
  let A := GluedGroup.PointGroup ℓ
  let C := Multiplicative (ZMod ℓ)
  let N := Base Inc ℓ assign
  let ι := point Inc ℓ assign
  let hi := point_injective Inc ℓ assign hInc hg
  let ξ := CoordinateCharacters.cyclicCharacter ℓ hζ
  have hξ : Function.Injective ξ := CoordinateCharacters.cyclicCharacter_injective ℓ hζ
  have hξ1 : ξ ≠ 1 := CoordinateCharacters.cyclicCharacter_ne_one ℓ hζ
  have hell : (ℓ : K) = 1 := natCast_eq_one_of_odd_of_two_eq_zero hodd CharTwo.two_eq_zero
  have hAc : (Fintype.card A : K) = 1 := by simp [A, GluedGroup.PointGroup, hell]
  have hCc : (Fintype.card C : K) = 1 := by simp [C, hell]
  let L := CharacterTwist.L ι hi v₀ α
  let f : MonoidAlgebra K N →ₐ[K] MonoidAlgebra K L :=
    MonoidAlgebra.mapDomainAlgHom K K ((CharacterTwist.emb ι hi v₀ α).comp (MonoidHom.inl N C))
  let lineSum (l : F) : MonoidAlgebra K L :=
    f (∑ c : C, MonoidAlgebra.single (line Inc ℓ assign hInc l c) 1)
  have hdec (v : V) : CharacterTwist.P (K := K) ι hi v₀ α v =
      1 + ∑ l : {l : F // v ∈ Inc l}, (lineSum l.val - 1) := by
    have hd := congrArg f (subgroup_decomposition (K := K) Inc ℓ assign hInc v)
    have hp : CharacterTwist.P (K := K) ι hi v₀ α v =
        f (∑ a : A, MonoidAlgebra.single (ι v a) 1) := by
      simp [CharacterTwist.P, pushed_eq_sum, f, CharacterTwist.localHom, hell]
      apply Fintype.sum_equiv (Equiv.refl A)
      intro a
      rfl
    rw [hp]
    simpa only [map_add, map_one, map_sum, map_sub, lineSum] using hd
  have hglobal' : X * X.transpose = 1 := by
    rw [hglobal]
    ext i j
    exact CharTwo.neg_eq _
  obtain ⟨ha,hb⟩ := CharacterTwist.matrix_products ι hi v₀ α ξ X Inc lineSum
    hdec hglobal' hlocal hlt (hAc ▸ one_ne_zero) (hCc ▸ one_ne_zero) slot hξ hα
  have hc : (Fintype.card (m → C) : K) ≠ 0 := by simp [hCc]
  exact FiniteBlock.output_products ξ i₀ hc hξ1 _ _ ha hb

end KaplanskyCounterexample.ChosenCriterion
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.FinitePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite presentations of finite-relation quotients and products. -/

noncomputable section

open scoped Classical

namespace KaplanskyCounterexample.CurrentMain

lemma finitelyPresented_fg (G : Type*) [Group G] [Group.IsFinitelyPresented G] :
    Group.FG G := by
  obtain ⟨n, f, hf, _⟩ := Group.IsFinitelyPresented.out (G := G)
  exact Group.fg_of_surjective hf

lemma conGen_ker_finite {G J : Type*} [Group G] [Finite J] (u v : J → G) :
    (conGen (fun x y => ∃ j, x=u j ∧ y=v j)).mk'.ker.IsFinitelyNormallyGenerated := by
  let c := conGen (fun x y => ∃ j, x=u j ∧ y=v j)
  let R := Set.range (fun j => u j * (v j)⁻¹)
  refine ⟨R, Set.finite_range _, ?_⟩
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j, rfl⟩
    have he : c.mk' (u j) = c.mk' (v j) :=
      (Con.eq c).mpr (ConGen.Rel.of _ _ ⟨j, rfl, rfl⟩)
    change c.mk' (u j * (v j)⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  · let q := QuotientGroup.mk' (Subgroup.normalClosure R)
    have hc : c ≤ Con.ker q := by
      apply Con.conGen_le.mpr
      rintro _ _ ⟨j, rfl, rfl⟩
      apply (Con.ker_rel q).mpr
      apply mul_inv_eq_one.mp
      rw [← map_inv, ← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨j, rfl⟩)
    intro w hw
    apply (QuotientGroup.eq_one_iff w).mp
    change q w = 1
    rw [← map_one q]
    apply hc
    exact (Con.eq c).mp (MonoidHom.mem_ker.mp hw |>.trans (map_one c.mk').symm)

lemma commuting_of_generators {G H T : Type*} [Group G] [Group H] [Group T]
    (S : Set G) (U : Set H) (hS : Subgroup.closure S = ⊤) (hU : Subgroup.closure U = ⊤)
    (f : G →* T) (g : H →* T) (h : ∀ a ∈ S, ∀ b ∈ U, Commute (f a) (g b)) :
    ∀ a b, Commute (f a) (g b) := by
  intro a b
  have ha : a ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top a
  have hb : b ∈ Subgroup.closure U := hU ▸ Subgroup.mem_top b
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    induction hb using Subgroup.closure_induction with
    | mem b hb => exact h a ha b hb
    | one => simp
    | mul b c hb hc hB hC => simpa only [map_mul] using hB.mul_right hC
    | inv b hb hB => simpa only [map_inv] using hB.inv_right
  | one => simp
  | mul a c ha hc hA hC => simpa only [map_mul] using hA.mul_left hC
  | inv a ha hA => simpa only [map_inv] using hA.inv_left

lemma finitelyPresented_prod (G H : Type*) [Group G] [Group H]
    [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented H] :
    Group.IsFinitelyPresented (G × H) := by
  obtain ⟨S, hS, hSf⟩ := Group.fg_iff.mp (finitelyPresented_fg G)
  obtain ⟨U, hU, hUf⟩ := Group.fg_iff.mp (finitelyPresented_fg H)
  let J := S × U
  let : Finite S := hSf
  let : Finite U := hUf
  let u : J → Monoid.Coprod G H := fun j =>
    Monoid.Coprod.inl j.1.val * Monoid.Coprod.inr j.2.val
  let v : J → Monoid.Coprod G H := fun j =>
    Monoid.Coprod.inr j.2.val * Monoid.Coprod.inl j.1.val
  let c := conGen (fun x y => ∃ j, x=u j ∧ y=v j)
  let q := c.mk'
  let f : G →* c.Quotient := q.comp Monoid.Coprod.inl
  let g : H →* c.Quotient := q.comp Monoid.Coprod.inr
  have hgen : ∀ a ∈ S, ∀ b ∈ U, Commute (f a) (g b) := by
    intro a ha b hb
    change q (Monoid.Coprod.inl a) * q (Monoid.Coprod.inr b) =
      q (Monoid.Coprod.inr b) * q (Monoid.Coprod.inl a)
    rw [← map_mul, ← map_mul]
    exact (Con.eq c).mpr (ConGen.Rel.of _ _ ⟨(⟨a,ha⟩,⟨b,hb⟩),rfl,rfl⟩)
  let p : G × H →* c.Quotient :=
    MonoidHom.noncommCoprod f g (commuting_of_generators S U hS hU f g hgen)
  have hp : p.comp Monoid.Coprod.toProd = q := by
    apply Monoid.Coprod.hom_ext
    · ext a
      simp [p, f, g, MonoidHom.noncommCoprod]
    · ext b
      simp [p, f, g, MonoidHom.noncommCoprod]
  have hc : c ≤ Con.ker (Monoid.Coprod.toProd : Monoid.Coprod G H →* G × H) := by
    apply Con.conGen_le.mpr
    rintro _ _ ⟨j, rfl, rfl⟩
    simp [u, v]
  have hk : (Monoid.Coprod.toProd : Monoid.Coprod G H →* G × H).ker = q.ker := by
    ext w
    constructor
    · intro hw
      apply MonoidHom.mem_ker.mpr
      rw [← hp, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hw, map_one]
    · intro hw
      have he : c w 1 := (Con.eq c).mp
        (MonoidHom.mem_ker.mp hw |>.trans (map_one q).symm)
      have he' := hc he
      apply MonoidHom.mem_ker.mpr
      simpa only [Con.ker_rel, map_one] using he'
  apply Group.IsFinitelyPresented.of_surjective _ Monoid.Coprod.toProd_surjective
  rw [hk]
  exact conGen_ker_finite u v

end KaplanskyCounterexample.CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.ShortRelators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical

namespace KaplanskyCounterexample.GluedGroup
variable {V : Type u_4} {F : Type u_5} (Inc : F → Finset V) (ℓ : ℕ)
variable (incMap : ∀ v : V, {f : F // v ∈ Inc f} → (ZMod ℓ →+ (Fin 2 → ZMod ℓ)))

/-- Only finitely many of the length-at-most-three relations occur. -/
lemma shortRelators_finite [Finite V] [Finite F] [NeZero ℓ] :
    (shortRelators Inc ℓ incMap).Finite := by
  let I := Σ (v : V), Σ k : Fin 4, Fin k.val → LocalGenerator Inc ℓ v × Bool
  let W (i : I) := includeLocal Inc ℓ i.1 (FreeGroup.mk (List.ofFn i.2.2))
  apply (Set.finite_range W).subset
  rintro w ⟨v,r,hr,_,rfl⟩
  refine ⟨⟨v,⟨r.length,by omega⟩,r.get⟩,?_⟩
  change includeLocal Inc ℓ v (FreeGroup.mk (List.ofFn r.get)) = _
  rw [List.ofFn_get]

end KaplanskyCounterexample.GluedGroup
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedOutputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription.Output

attribute [local instance] OAI.KaplanskyCounterexample.Prescription.Output.instDecidableEqSubtypeKHMemSubfieldSubfield_1
local instance (priority := 3000) instDecidableEqV_1_raff6f0_1 : DecidableEq V := Classical.decEq _
/-- The two product assertions are for the specified first successful data and
specified sums, not merely for some field, some group or some pair of inverses. -/
theorem prescribed_products : a*b=1 ∧ b*a≠1 :=
  ChosenCriterion.products ell Inc assignment nonempty_Inc girth_Inc v0 form
    (zeta_primitive h) X i0 slot (prime_odd h.val h.property) sizes.2.1
    (by convert X_global using 1; congr 1; ext i j; simp only [Matrix.one_apply]; split_ifs <;> rfl) X_local forms_distinct

lemma N_shortRelators_finite :
    (GluedGroup.shortRelators Inc ell (AssignedDirections.incidenceMap Inc ell assignment)).Finite :=
  GluedGroup.shortRelators_finite _ _ _

end KaplanskyCounterexample.Prescription.Output
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.OddTorsion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An embedded cyclic subgroup of odd prime order in the prescribed group. -/

noncomputable section

open scoped Classical

namespace KaplanskyCounterexample.Prescription.Output

lemma diagonalPoint_injective : Function.Injective diagonalPoint := by
  intro c d he
  exact congrArg (fun a : GluedGroup.PointGroup ell => a.toAdd (0 : Fin 2)) he

lemma retainedPoint_injective : Function.Injective retainedPoint := by
  dsimp only [retainedPoint, MonoidHom.coe_comp]
  apply Function.Injective.comp (fun x y h => congrArg Prod.fst h)
  apply Function.Injective.comp (CharacterTwist.emb_injective _ _ _ _)
  apply Function.Injective.comp (fun x y h => congrArg Prod.fst h)
  exact AssignedDevelopment.point_injective Inc ell assignment nonempty_Inc girth_Inc v0

theorem prescribed_odd_prime_order :
    ∃ (ℓ : ℕ) (_ : ℓ.Prime) (_ : Odd ℓ) (g : G), orderOf g = ℓ := by
  refine ⟨ell, Fact.out, prime_odd h.val h.property,
    retainedPoint (diagonalPoint (Multiplicative.ofAdd (1 : ZMod ell))), ?_⟩
  rw [orderOf_injective retainedPoint retainedPoint_injective,
    orderOf_injective diagonalPoint diagonalPoint_injective,
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

end KaplanskyCounterexample.Prescription.Output

end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.HNNPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite presentation of multiple HNN extensions and character twists. -/

noncomputable section

open scoped Classical

namespace KaplanskyCounterexample.CurrentMain

lemma characterTwist_finitelyPresented {A N C V : Type*}
    [CommGroup A] [Group N] [CommGroup C] [Finite A] [Finite C] [Finite V]
    [Group.IsFinitelyPresented N]
    (ι : V → A →* N) (hi : ∀ v, Function.Injective (ι v))
    (v₀ : V) (α : V → A →* C) :
    Group.IsFinitelyPresented (CharacterTwist.L ι hi v₀ α) := by
  let : Group.IsFinitelyPresented (N × C) := finitelyPresented_prod N C
  let (v : V) : Finite (CharacterTwist.source (C := C) ι v) :=
    Finite.of_surjective _ (CharacterTwist.src (C := C) ι v).rangeRestrict_surjective
  exact multipleHNN_finitelyPresented _ _ _

end KaplanskyCounterexample.CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite presentation of the prescribed group. -/

noncomputable section

open scoped Classical

namespace KaplanskyCounterexample.Prescription.Output

lemma prescribed_base_finitelyPresented :
    Group.IsFinitelyPresented (AssignedDevelopment.Base Inc ell assignment) := by
  let : Finite (GluedGroup.shortRelators Inc ell
    (AssignedDirections.incidenceMap Inc ell assignment)) := N_shortRelators_finite
  exact Group.IsFinitelyPresented.equiv N_shortEquiv

theorem prescribed_finitelyPresented : Group.IsFinitelyPresented G := by
  let := prescribed_base_finitelyPresented
  let : Group.IsFinitelyPresented
      (ChosenCriterion.Extension ell Inc assignment nonempty_Inc girth_Inc v0 form) :=
    CurrentMain.characterTwist_finitelyPresented _ _ _ _
  exact CurrentMain.finitelyPresented_prod _ _

end KaplanskyCounterexample.Prescription.Output

end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.FinitelyPresented
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prescribed finitely presented counterexample in characteristic two. -/

namespace KaplanskyCounterexample

open Prescription

theorem thm_main :
    (∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2),
      ∃ (G : Type) (_ : Group G) (_ : Group.IsFinitelyPresented G),
        (∃ (ℓ : ℕ) (_ : ℓ.Prime) (_ : Odd ℓ) (g : G), orderOf g = ℓ) ∧
        ∃ a_out b_out : MonoidAlgebra K G, a_out * b_out = 1 ∧ b_out * a_out ≠ 1) ∧
    (2 ≤ selectedH ∧ selectedH ≤ 217 ∧ Test selectedInput selectedPair ∧
      (∀ h, Succeeds h → selectedH ≤ h) ∧
      (∀ p, Test selectedInput p →
        @LE.le _ (pairOrder selectedInput).toLE selectedPair p)) ∧
    Group.IsFinitelyPresented Output.G ∧
    (∃ (ℓ : ℕ) (_ : ℓ.Prime) (_ : Odd ℓ) (g : Output.G), orderOf g = ℓ) ∧
    Output.a * Output.b = 1 ∧ Output.b * Output.a ≠ 1 := by
  refine ⟨?_, finite_search_terminates, Output.prescribed_finitelyPresented,
    Output.prescribed_odd_prime_order, Output.prescribed_products⟩
  exact ⟨Output.Coeff, inferInstance, inferInstance, inferInstance,
    Output.G, inferInstance, Output.prescribed_finitelyPresented,
    Output.prescribed_odd_prime_order, Output.a, Output.b, Output.prescribed_products⟩


/-- The existential main result of the characteristic-two paper, separated from
the certificates for its prescribed construction. -/
theorem finitelyPresented_counterexample_oai :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2),
      ∃ (G : Type) (_ : Group G) (_ : Group.IsFinitelyPresented G),
        (∃ (ℓ : ℕ) (_ : ℓ.Prime) (_ : Odd ℓ) (g : G), orderOf g = ℓ) ∧
        ∃ a_out b_out : MonoidAlgebra K G, a_out * b_out = 1 ∧ b_out * a_out ≠ 1 :=
  thm_main.1

end KaplanskyCounterexample

end OAI
end

theorem solution : type_of% @OAI.KaplanskyCounterexample.finitelyPresented_counterexample_oai := @OAI.KaplanskyCounterexample.finitelyPresented_counterexample_oai
