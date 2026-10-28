-- Prove2me | solution 1 for OAI.QuantitativeVanDerWaerden.uniform_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-24T23:37:35.236074+00:00
-- url     : https://prove2.me/submissions/9d783c4f-d516-4fdd-ab2c-a7359ab37146

import Mathlib
import Definitions.Def_QuantitativeVanDerWaerden

namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
end OAICompat434

end OAI

universe uOmega uI uKey uAlpha uBeta uIndex uA uX uBox uAmbient uU uV uWord uLabel uk uOtherLabel uG uL uK uB u

section
section
namespace OAI

/-!
# Finite weighted probability and independent Bernoulli coordinates

Events are finite sets and their weights are finite sums. Normalization and
nonnegativity are explicit hypotheses for the generic probability inequalities.
The product identities are algebraic, so their statements also hold at the
boundary parameters zero and one without dividing by any point weight.
-/


namespace QuantitativeVanDerWaerden.FiniteProbability

open scoped BigOperators

noncomputable section

variable {Ω : Type uOmega} {I : Type uI}

/-- The weight of a finite event. -/
def prob (w : Ω → ℝ) (A : Finset Ω) : ℝ := ∑ ω ∈ A, w ω

@[simp] theorem prob_empty (w : Ω → ℝ) : prob w ∅ = 0 := by
  simp [prob]

@[simp] theorem prob_univ [Fintype Ω] (w : Ω → ℝ) :
    prob w Finset.univ = ∑ ω, w ω := rfl

theorem prob_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (A : Finset Ω) :
    0 ≤ prob w A :=
  Finset.sum_nonneg (fun ω _ => hw ω)

theorem prob_mono {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    {A B : Finset Ω} (hAB : A ⊆ B) : prob w A ≤ prob w B :=
  Finset.sum_le_sum_of_subset_of_nonneg hAB (fun ω _ _ => hw ω)

section DecidableEvents
variable [DecidableEq Ω]

theorem prob_union_le {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (A B : Finset Ω) : prob w (A ∪ B) ≤ prob w A + prob w B := by
  have hid : prob w (A ∪ B) + prob w (A ∩ B) = prob w A + prob w B :=
    Finset.sum_union_inter
  have hn := prob_nonneg hw (A ∩ B)
  linarith

/-- Finite union bound; events need not be independent. -/
theorem prob_biUnion_le {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (J : Finset I) (A : I → Finset Ω) :
    prob w (J.biUnion A) ≤ ∑ i ∈ J, prob w (A i) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [prob]
  | @insert i J hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      exact (prob_union_le hw (A i) (J.biUnion A)).trans (add_le_add le_rfl ih)

/-- A normalized event of weight strictly below one misses a point. -/
theorem exists_not_mem_of_prob_lt_one [Fintype Ω] {w : Ω → ℝ}
    (hw : ∑ ω, w ω = 1) (A : Finset Ω) (hA : prob w A < 1) :
    ∃ ω, ω ∉ A := by
  classical
  by_contra h
  have hfull : A = Finset.univ := by
    apply Finset.ext
    intro ω
    simp only [Finset.mem_univ, iff_true]
    by_contra hω
    exact h ⟨ω, hω⟩
  have heq : prob w A = 1 := by simpa [hfull] using hw
  linarith

/-- If the sum of bad-event probabilities is below one, avoid all of them. -/
theorem exists_avoiding_of_sum_probs_lt_one [Fintype Ω] {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (htotal : ∑ ω, w ω = 1)
    (J : Finset I) (A : I → Finset Ω)
    (hbudget : (∑ i ∈ J, prob w (A i)) < 1) :
    ∃ ω, ∀ i ∈ J, ω ∉ A i := by
  obtain ⟨ω, hω⟩ := exists_not_mem_of_prob_lt_one htotal (J.biUnion A)
    ((prob_biUnion_le hw J A).trans_lt hbudget)
  refine ⟨ω, ?_⟩
  intro i hi hmem
  exact hω (Finset.mem_biUnion.mpr ⟨i, hi, hmem⟩)

end DecidableEvents

/-- A single Bernoulli coordinate gives weight `p` to `true`. -/
def bitWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

variable {Key : Type uKey} [Fintype Key]

/-- Product weight on the actual finite space of all bit assignments. -/
def bernoulliWeight (p : ℝ) (ω : Key → Bool) : ℝ :=
  ∏ i, bitWeight p (ω i)

theorem bernoulliWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (ω : Key → Bool) : 0 ≤ bernoulliWeight p ω := by
  apply Finset.prod_nonneg
  intro i _
  cases ω i <;> simp only [bitWeight, Bool.false_eq_true, ↓reduceIte]
  · exact sub_nonneg.mpr hp'
  · exact hp

variable [DecidableEq Key]

/-- The product Bernoulli weights sum to one, including `p = 0` and `p = 1`. -/
theorem sum_bernoulliWeight (p : ℝ) :
    ∑ ω : Key → Bool, bernoulliWeight p ω = 1 := by
  classical
  have hbit : (∑ b : Bool, bitWeight p b) = 1 := by
    simp [bitWeight]
  unfold bernoulliWeight
  rw [← Fintype.prod_sum]
  simp only [hbit, Finset.prod_const_one]

/-- Product expectation for independent bits, expressed entirely by finite sums. -/
theorem expectation_prod (p : ℝ) (f : Key → Bool → ℝ) :
    (∑ ω : Key → Bool, bernoulliWeight p ω * ∏ i, f i (ω i)) =
      ∏ i, ((1 - p) * f i false + p * f i true) := by
  classical
  calc
    (∑ ω : Key → Bool, bernoulliWeight p ω * ∏ i, f i (ω i)) =
        ∑ ω : Key → Bool, ∏ i, bitWeight p (ω i) * f i (ω i) := by
      simp only [bernoulliWeight, Finset.prod_mul_distrib]
    _ = ∏ i, ∑ b : Bool, bitWeight p b * f i b :=
      (Fintype.prod_sum (fun i b => bitWeight p b * f i b)).symm
    _ = ∏ i, ((1 - p) * f i false + p * f i true) := by
      apply Finset.prod_congr rfl
      intro i _
      simp [bitWeight, add_comm]

/-- Each coordinate may restrict its bit independently. -/
def coordinateEvent (P : Key → Bool → Prop) : Finset (Key → Bool) := by
  classical
  exact Finset.univ.filter (fun ω => ∀ i, P i (ω i))

/-- Exact weight of arbitrary coordinatewise restrictions. -/
theorem prob_coordinateEvent (p : ℝ) (P : Key → Bool → Prop)
    [∀ i, DecidablePred (P i)] :
    prob (bernoulliWeight p) (coordinateEvent P) =
      ∏ i, ∑ b : Bool, if P i b then bitWeight p b else 0 := by
  classical
  unfold prob coordinateEvent
  rw [Finset.sum_filter]
  calc
    _ = ∑ ω : Key → Bool, ∏ i, if P i (ω i) then bitWeight p (ω i) else 0 := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [Fintype.prod_ite_zero]
      by_cases h : ∀ i, P i (ω i)
      · simp only [ite_eq_left h, bernoulliWeight]
      · simp only [ite_eq_right h]
    _ = ∏ i, ∑ b : Bool, if P i b then bitWeight p b else 0 :=
      (Fintype.prod_sum (fun i b => if P i b then bitWeight p b else 0)).symm

/-- Assign prescribed bits on a named finite set of distinct keys. -/
def cylinder (S : Finset Key) (a : Key → Bool) : Finset (Key → Bool) := by
  classical
  exact Finset.univ.filter (fun ω => ∀ i ∈ S, ω i = a i)

@[simp] theorem mem_cylinder (S : Finset Key) (a ω : Key → Bool) :
    ω ∈ cylinder S a ↔ ∀ i ∈ S, ω i = a i := by
  classical
  simp [cylinder]

/-- Exact cylinder probability; coordinates outside `S` are summed out. -/
theorem prob_bernoulli_cylinder (p : ℝ) (S : Finset Key) (a : Key → Bool) :
    prob (bernoulliWeight p) (cylinder S a) =
      ∏ i ∈ S, if a i then p else 1 - p := by
  classical
  have hc : cylinder S a = coordinateEvent (fun i b => i ∈ S → b = a i) := by
    ext ω
    simp [cylinder, coordinateEvent]
  rw [hc, prob_coordinateEvent]
  calc
    (∏ i, ∑ b : Bool, if i ∈ S → b = a i then bitWeight p b else 0) =
        ∏ i, if i ∈ S then bitWeight p (a i) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ S <;> cases a i <;>
        simp [bitWeight, hi]
    _ = ∏ i ∈ S, if a i then p else 1 - p := by
      simpa only [bitWeight] using
        (Fintype.prod_ite_mem S (fun i => bitWeight p (a i)))

/-- A finite event is determined by the coordinates in its declared support. -/
def DependsOn (S : Finset Key) (E : Finset (Key → Bool)) : Prop :=
  ∀ ω η, (∀ i ∈ S, ω i = η i) → (ω ∈ E ↔ η ∈ E)

private def splice (S : Finset Key) (ω η : Key → Bool) : Key → Bool :=
  fun i => if i ∈ S then ω i else η i

/-- Exchange the complementary coordinates between two complete assignments. -/
private def coordinateSwap (S : Finset Key) :
    ((Key → Bool) × (Key → Bool)) ≃ ((Key → Bool) × (Key → Bool)) where
  toFun z := (splice S z.1 z.2, splice S z.2 z.1)
  invFun z := (splice S z.1 z.2, splice S z.2 z.1)
  left_inv z := by
    apply Prod.ext <;> funext i <;> by_cases hi : i ∈ S <;> simp [splice, hi]
  right_inv z := by
    apply Prod.ext <;> funext i <;> by_cases hi : i ∈ S <;> simp [splice, hi]

private theorem bernoulliWeight_splice (p : ℝ) (S : Finset Key)
    (ω η : Key → Bool) :
    bernoulliWeight p (splice S ω η) * bernoulliWeight p (splice S η ω) =
      bernoulliWeight p ω * bernoulliWeight p η := by
  unfold bernoulliWeight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [splice, hi, mul_comm]

private theorem sum_pair_product {α : Type uAlpha} {β : Type uBeta} [Fintype α] [Fintype β]
    (f : α → ℝ) (g : β → ℝ) :
    (∑ z : α × β, f z.1 * g z.2) = (∑ x, f x) * (∑ y, g y) := by
  simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- Arbitrary functions of disjoint sets of coordinates factor under the
actual finite Bernoulli weights. The proof swaps two complete assignments. -/
theorem expectation_mul_of_disjoint_supports (p : ℝ) (S T : Finset Key)
    (hST : Disjoint S T) (f g : (Key → Bool) → ℝ)
    (hf : ∀ ω η, (∀ i ∈ S, ω i = η i) → f ω = f η)
    (hg : ∀ ω η, (∀ i ∈ T, ω i = η i) → g ω = g η) :
    (∑ ω : Key → Bool, bernoulliWeight p ω * f ω * g ω) =
      (∑ ω : Key → Bool, bernoulliWeight p ω * f ω) *
      (∑ ω : Key → Bool, bernoulliWeight p ω * g ω) := by
  classical
  have hsum :
      (∑ z : (Key → Bool) × (Key → Bool),
        (bernoulliWeight p z.1 * f z.1 * g z.1) * bernoulliWeight p z.2) =
      ∑ z : (Key → Bool) × (Key → Bool),
        (bernoulliWeight p z.1 * f z.1) * (bernoulliWeight p z.2 * g z.2) := by
    apply Fintype.sum_equiv (coordinateSwap S)
    intro z
    change (bernoulliWeight p z.1 * f z.1 * g z.1) * bernoulliWeight p z.2 =
      (bernoulliWeight p (splice S z.1 z.2) * f (splice S z.1 z.2)) *
      (bernoulliWeight p (splice S z.2 z.1) * g (splice S z.2 z.1))
    have hf' : f (splice S z.1 z.2) = f z.1 := by
      apply hf
      intro i hi
      simp [splice, hi]
    have hg' : g (splice S z.2 z.1) = g z.1 := by
      apply hg
      intro i hi
      have hin : i ∉ S := fun his => Finset.disjoint_left.mp hST his hi
      simp [splice, hin]
    rw [hf', hg']
    calc
      (bernoulliWeight p z.1 * f z.1 * g z.1) * bernoulliWeight p z.2 =
          (bernoulliWeight p z.1 * bernoulliWeight p z.2) * (f z.1 * g z.1) := by ring
      _ = (bernoulliWeight p (splice S z.1 z.2) *
          bernoulliWeight p (splice S z.2 z.1)) * (f z.1 * g z.1) := by
        rw [bernoulliWeight_splice]
      _ = (bernoulliWeight p (splice S z.1 z.2) * f z.1) *
          (bernoulliWeight p (splice S z.2 z.1) * g z.1) := by ring
  have hleft := sum_pair_product
    (fun ω : Key → Bool => bernoulliWeight p ω * f ω * g ω)
    (fun η : Key → Bool => bernoulliWeight p η)
  have hright := sum_pair_product
    (fun ω : Key → Bool => bernoulliWeight p ω * f ω)
    (fun η : Key → Bool => bernoulliWeight p η * g η)
  rw [hleft, hright, sum_bernoulliWeight, mul_one] at hsum
  exact hsum

/-- Finite-event mass as the expectation of its zero-one indicator. -/
theorem prob_eq_sum_indicator [Fintype Ω] [DecidableEq Ω]
    (w : Ω → ℝ) (E : Finset Ω) :
    prob w E = ∑ ω, w ω * (if ω ∈ E then (1 : ℝ) else 0) := by
  classical
  have hfilter : Finset.univ.filter (fun ω => ω ∈ E) = E := by
    ext ω
    simp
  calc
    prob w E = ∑ ω ∈ Finset.univ.filter (fun ω => ω ∈ E), w ω := by
      rw [hfilter]
      rfl
    _ = ∑ ω, w ω * (if ω ∈ E then (1 : ℝ) else 0) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hω : ω ∈ E <;> simp [hω]

/-- Actual events depending on disjoint key sets are independent. No cylinder
restriction or probability-factorization hypothesis is imposed on the events. -/
theorem prob_inter_of_disjoint_supports (p : ℝ)
    (E F : Finset (Key → Bool)) (S T : Finset Key)
    (hE : DependsOn S E) (hF : DependsOn T F) (hST : Disjoint S T) :
    prob (bernoulliWeight p) (E ∩ F) =
      prob (bernoulliWeight p) E * prob (bernoulliWeight p) F := by
  classical
  simp only [prob_eq_sum_indicator]
  calc
    (∑ ω : Key → Bool, bernoulliWeight p ω *
        (if ω ∈ E ∩ F then (1 : ℝ) else 0)) =
      ∑ ω : Key → Bool, bernoulliWeight p ω *
        (if ω ∈ E then (1 : ℝ) else 0) * (if ω ∈ F then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases he : ω ∈ E <;> by_cases hf : ω ∈ F <;> simp [he, hf]
    _ = (∑ ω : Key → Bool, bernoulliWeight p ω * (if ω ∈ E then (1 : ℝ) else 0)) *
        (∑ ω : Key → Bool, bernoulliWeight p ω * (if ω ∈ F then (1 : ℝ) else 0)) := by
      apply expectation_mul_of_disjoint_supports p S T hST
      · intro ω η h
        simp only [hE ω η h]
      · intro ω η h
        simp only [hF ω η h]

end

end QuantitativeVanDerWaerden.FiniteProbability

end OAI
end
end

section
section
namespace OAI

/-! The common nonzero-step cyclic avoidance predicate. Colors are generic so
the constructed Boolean coloring and finite-cardinality transfers use the same
definition without a color conversion. -/


namespace QuantitativeVanDerWaerden

def CyclicAvoids {N : ℕ} {α : Type uAlpha} (C : ZMod N → α) (k : ℕ) : Prop :=
  ∀ a d, d ≠ 0 → ¬ (∀ j < k, C (a + (j : ZMod N) * d) = C a)

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Sparse perturbations indexed by literal keys

A signature records the original bit and the actual key at every position.
The key is never renamed. All positions with the same key use the same sampled
bit. The finite events below therefore include the correlations caused by
repeated keys, including inconsistent prescriptions.
-/


namespace QuantitativeVanDerWaerden
namespace SparsePerturbation

open scoped BigOperators

abbrev Signature (Key : Type uKey) (k : ℕ) := Fin k → Bool × Key

variable {Key : Type uKey} [Fintype Key] {k : ℕ}
variable [DecidableEq Key]

/-- The actual key image of a literal signature. -/
noncomputable def usedKeys (σ : Signature Key k) : Finset Key := by
  classical
  exact Finset.univ.image (fun j => (σ j).2)

/-- Positions whose original bit differs from the target bit. -/
def oppositePositions (σ : Signature Key k) (b : Bool) : Finset (Fin k) :=
  Finset.univ.filter (fun j => (σ j).1 ≠ b)

/-- The fixed keys that must flip for the target event. -/
noncomputable def oppositeKeys (σ : Signature Key k) (b : Bool) : Finset Key := by
  classical
  exact (oppositePositions σ b).image (fun j => (σ j).2)

/-- The finite event that this signature becomes monochromatic in bit `b`. -/
noncomputable def targetEvent (σ : Signature Key k) (b : Bool) :
    Finset (Key → Bool) := by
  classical
  exact Finset.univ.filter (fun ω => ∀ j, Bool.xor (σ j).1 (ω (σ j).2) = b)

@[simp] theorem mem_targetEvent (σ : Signature Key k) (b : Bool) (ω : Key → Bool) :
    ω ∈ targetEvent σ b ↔ ∀ j, Bool.xor (σ j).1 (ω (σ j).2) = b := by
  classical
  simp [targetEvent]

theorem xor_right_eq_of_same_target {c x y b : Bool}
    (hx : Bool.xor c x = b) (hy : Bool.xor c y = b) : x = y := by
  cases c <;> cases x <;> cases y <;> cases b <;> simp_all

theorem xor_target_of_opposite {c x b : Bool}
    (hc : c ≠ b) (hx : Bool.xor c x = b) : x = true := by
  cases c <;> cases x <;> cases b <;> simp_all

/-- A key shared by opposite original colors makes each target event empty. -/
theorem targetEvent_eq_empty_of_conflict (σ : Signature Key k) (b : Bool)
    {i j : Fin k} (hkey : (σ i).2 = (σ j).2) (hcolor : (σ i).1 ≠ (σ j).1) :
    targetEvent σ b = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ω hω
  have hi := (mem_targetEvent σ b ω).mp hω i
  have hj := (mem_targetEvent σ b ω).mp hω j
  rw [hkey] at hi
  generalize hc : (σ i).1 = ci at hi hcolor
  generalize hd : (σ j).1 = cj at hj hcolor
  generalize he : ω (σ j).2 = e at hi hj
  cases ci <;> cases cj <;> cases e <;> cases b <;> simp_all

/-- A nonempty target event is exactly the cylinder prescribed by any one of
its members, on the actual used-key set. -/
theorem targetEvent_eq_prescriptions (σ : Signature Key k) (b : Bool)
    {ω₀ : Key → Bool} (hω₀ : ω₀ ∈ targetEvent σ b) :
    targetEvent σ b = Finset.univ.filter (fun ω =>
      ∀ a ∈ usedKeys σ, ω a = ω₀ a) := by
  classical
  ext ω
  simp only [mem_targetEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hω a ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    exact xor_right_eq_of_same_target (hω j) ((mem_targetEvent σ b ω₀).mp hω₀ j)
  · intro hω j
    have hj : (σ j).2 ∈ usedKeys σ := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rw [hω _ hj]
    exact (mem_targetEvent σ b ω₀).mp hω₀ j

/-- Every target event forces the already determined opposite-key set to flip.
There is no additional choice of a subset of keys. -/
theorem targetEvent_subset_opposite_cylinder (σ : Signature Key k) (b : Bool) :
    targetEvent σ b ⊆ Finset.univ.filter (fun ω =>
      ∀ a ∈ oppositeKeys σ b, ω a = true) := by
  classical
  intro ω hω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro a ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
  have hc : (σ j).1 ≠ b := (Finset.mem_filter.mp hj).2
  exact xor_target_of_opposite hc ((mem_targetEvent σ b ω).mp hω j)

/-- The same literal signature gives the same event on the same key variables. -/
theorem targetEvent_eq_of_signature_eq {σ τ : Signature Key k} (h : σ = τ)
    (b : Bool) : targetEvent σ b = targetEvent τ b := by rw [h]

/-- A multiplicity cap applies to every subset of positions. -/
theorem card_le_four_mul_card_image {Key : Type uKey} [Fintype Key] {k : ℕ}
    [DecidableEq Key]
    (σ : Signature Key k)
    (hmult : ∀ a, (Finset.univ.filter (fun j => (σ j).2 = a)).card ≤ 4)
    (J : Finset (Fin k)) :
    J.card ≤ 4 * (J.image (fun j => (σ j).2)).card := by
  classical
  calc
    J.card = ∑ a ∈ J.image (fun j => (σ j).2),
        (J.filter (fun j => (σ j).2 = a)).card :=
      Finset.card_eq_sum_card_image _ J
    _ ≤ ∑ _a ∈ J.image (fun j => (σ j).2), 4 := by
      apply Finset.sum_le_sum
      intro a ha
      apply le_trans (Finset.card_le_card ?_) (hmult a)
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
    _ = 4 * (J.image (fun j => (σ j).2)).card := by simp [Nat.mul_comm]

/-- Exact integer lower bound on the number of keys in a whole signature. -/
theorem ceil_quarter_le_usedKeys_card (σ : Signature Key k)
    (hmult : ∀ a, (Finset.univ.filter (fun j => (σ j).2 = a)).card ≤ 4) :
    (k + 3) / 4 ≤ (usedKeys σ).card := by
  have h := card_le_four_mul_card_image σ hmult Finset.univ
  simp only [Finset.card_univ, Fintype.card_fin] at h
  change k ≤ 4 * (usedKeys σ).card at h
  omega

/-- Exact integer lower bound on the predetermined flips in a rich signature.
The richness premise is the integral form of at least `k/100` opposite bits. -/
theorem ceil_four_hundredth_le_oppositeKeys_card (σ : Signature Key k) (b : Bool)
    (hmult : ∀ a, (Finset.univ.filter (fun j => (σ j).2 = a)).card ≤ 4)
    (hrich : k ≤ 100 * (oppositePositions σ b).card) :
    (k + 399) / 400 ≤ (oppositeKeys σ b).card := by
  have h := card_le_four_mul_card_image σ hmult (oppositePositions σ b)
  change (oppositePositions σ b).card ≤ 4 * (oppositeKeys σ b).card at h
  omega

open FiniteProbability

/-- Exact target probability, whenever the prescriptions are consistent. -/
theorem target_probability_eq (p : ℝ) (σ : Signature Key k) (b : Bool)
    {ω₀ : Key → Bool} (hω₀ : ω₀ ∈ targetEvent σ b) :
    prob (bernoulliWeight p) (targetEvent σ b) =
      ∏ a ∈ usedKeys σ, if ω₀ a then p else 1 - p := by
  have heq : targetEvent σ b = cylinder (usedKeys σ) ω₀ :=
    targetEvent_eq_prescriptions σ b hω₀
  rw [heq, prob_bernoulli_cylinder]

/-- Sparse flips preserve a fixed rich signature with high probability. -/
theorem target_probability_le_flip_pow {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Signature Key k) (b : Bool) :
    prob (bernoulliWeight p) (targetEvent σ b) ≤ p ^ (oppositeKeys σ b).card := by
  classical
  have hsub : targetEvent σ b ⊆ cylinder (oppositeKeys σ b) (fun _ => true) :=
    targetEvent_subset_opposite_cylinder σ b
  calc
    _ ≤ prob (bernoulliWeight p) (cylinder (oppositeKeys σ b) (fun _ => true)) :=
      prob_mono (bernoulliWeight_nonneg hp hp1) hsub
    _ = p ^ (oppositeKeys σ b).card := by
      rw [prob_bernoulli_cylinder]
      simp

/-- For `p ≤ 1/2`, every prescribed key has probability at most `1-p`. -/
theorem target_probability_le_stay_pow {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (σ : Signature Key k) (b : Bool) :
    prob (bernoulliWeight p) (targetEvent σ b) ≤ (1 - p) ^ (usedKeys σ).card := by
  classical
  by_cases h : (targetEvent σ b).Nonempty
  · obtain ⟨ω₀, hω₀⟩ := h
    rw [target_probability_eq p σ b hω₀]
    calc
      _ ≤ ∏ _a ∈ usedKeys σ, (1 - p) := by
        apply Finset.prod_le_prod
        · intro a ha
          split_ifs <;> linarith
        · intro a ha
          split_ifs <;> linarith
      _ = (1 - p) ^ (usedKeys σ).card := by simp
  · rw [Finset.not_nonempty_iff_eq_empty.mp h, prob_empty]
    exact pow_nonneg (by linarith) _

theorem rich_target_probability_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Signature Key k) (b : Bool)
    (hmult : ∀ a, (Finset.univ.filter (fun j => (σ j).2 = a)).card ≤ 4)
    (hrich : k ≤ 100 * (oppositePositions σ b).card) :
    prob (bernoulliWeight p) (targetEvent σ b) ≤ p ^ ((k + 399) / 400) :=
  (target_probability_le_flip_pow hp hp1 σ b).trans
    (pow_le_pow_of_le_one hp hp1 (ceil_four_hundredth_le_oppositeKeys_card σ b hmult hrich))

theorem target_probability_le {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (σ : Signature Key k)
    (hmult : ∀ a, (Finset.univ.filter (fun j => (σ j).2 = a)).card ≤ 4)
    (b : Bool) :
    prob (bernoulliWeight p) (targetEvent σ b) ≤ (1 - p) ^ ((k + 3) / 4) :=
  (target_probability_le_stay_pow hp hp2 σ b).trans
    (pow_le_pow_of_le_one (by linarith) (by linarith) (ceil_quarter_le_usedKeys_card σ hmult))

/-- Either target bit is bad. -/
noncomputable def monochromaticEvent (σ : Signature Key k) : Finset (Key → Bool) := by
  classical
  exact targetEvent σ false ∪ targetEvent σ true

@[simp] theorem mem_monochromaticEvent (σ : Signature Key k) (ω : Key → Bool) :
    ω ∈ monochromaticEvent σ ↔ ∃ b, ∀ j, Bool.xor (σ j).1 (ω (σ j).2) = b := by
  classical
  simp only [monochromaticEvent, Finset.mem_union, mem_targetEvent]
  constructor
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · rintro ⟨b, h⟩
    cases b
    · exact Or.inl h
    · exact Or.inr h

theorem monochromatic_probability_le {p r : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Signature Key k)
    (h : ∀ b, prob (bernoulliWeight p) (targetEvent σ b) ≤ r) :
    prob (bernoulliWeight p) (monochromaticEvent σ) ≤ 2 * r := by
  classical
  calc
    _ ≤ prob (bernoulliWeight p) (targetEvent σ false) +
        prob (bernoulliWeight p) (targetEvent σ true) :=
      prob_union_le (bernoulliWeight_nonneg hp hp1) _ _
    _ ≤ r + r := add_le_add (h false) (h true)
    _ = 2 * r := by ring

/-- Finite sparse-perturbation theorem. The affine family is counted through
its actual literal-signature image; repeated descriptions are not new events.
No independence between different progression events is assumed. -/
theorem exists_avoiding_of_rich_or_signature {ι : Type uIndex} [DecidableEq ι]
    (P A : Finset ι) (σ : ι → Signature Key k) (hA : A ⊆ P)
    {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hmult : ∀ i ∈ P, ∀ a, (Finset.univ.filter (fun j => (σ i j).2 = a)).card ≤ 4)
    (hcases : ∀ i ∈ P, i ∈ A ∨ ∀ b, k ≤ 100 * (oppositePositions (σ i) b).card)
    (hbudget : 2 * (P.card : ℝ) * p ^ ((k + 399) / 400) +
      2 * ((A.image σ).card : ℝ) * (1 - p) ^ ((k + 3) / 4) < 1) :
    ∃ ω : Key → Bool, ∀ i ∈ P, ∀ b, ∃ j,
      Bool.xor (σ i j).1 (ω (σ i j).2) ≠ b := by
  classical
  let R := P \ A
  let F := A.image σ
  let ER := R.biUnion (fun i => monochromaticEvent (σ i))
  let EF := F.biUnion monochromaticEvent
  have hp1 : p ≤ 1 := by linarith
  have hnonneg := bernoulliWeight_nonneg (Key := Key) hp hp1
  have hR : prob (bernoulliWeight p) ER ≤ 2 * (P.card : ℝ) * p ^ ((k + 399) / 400) := by
    calc
      _ ≤ ∑ i ∈ R, prob (bernoulliWeight p) (monochromaticEvent (σ i)) :=
        prob_biUnion_le hnonneg R _
      _ ≤ ∑ _i ∈ R, 2 * p ^ ((k + 399) / 400) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiP : i ∈ P := (Finset.mem_sdiff.mp hi).1
        have hiA : i ∉ A := (Finset.mem_sdiff.mp hi).2
        have hrich := (hcases i hiP).resolve_left hiA
        exact monochromatic_probability_le hp hp1 (σ i)
          (fun b => rich_target_probability_le hp hp1 (σ i) b (hmult i hiP) (hrich b))
      _ = 2 * (R.card : ℝ) * p ^ ((k + 399) / 400) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ 2 * (P.card : ℝ) * p ^ ((k + 399) / 400) := by
        have hcard : (R.card : ℝ) ≤ P.card := by
          exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : R ⊆ P)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num))
          (pow_nonneg hp _)
  have hF : prob (bernoulliWeight p) EF ≤
      2 * (F.card : ℝ) * (1 - p) ^ ((k + 3) / 4) := by
    calc
      _ ≤ ∑ τ ∈ F, prob (bernoulliWeight p) (monochromaticEvent τ) :=
        prob_biUnion_le hnonneg F _
      _ ≤ ∑ _τ ∈ F, 2 * (1 - p) ^ ((k + 3) / 4) := by
        apply Finset.sum_le_sum
        intro τ hτ
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hτ
        exact monochromatic_probability_le hp hp1 (σ i)
          (target_probability_le hp hp2 (σ i) (hmult i (hA hi)))
      _ = 2 * (F.card : ℝ) * (1 - p) ^ ((k + 3) / 4) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  have hbad : prob (bernoulliWeight p) (ER ∪ EF) < 1 :=
    (prob_union_le hnonneg ER EF).trans_lt ((add_le_add hR hF).trans_lt hbudget)
  obtain ⟨ω, hω⟩ := exists_not_mem_of_prob_lt_one (sum_bernoulliWeight p) (ER ∪ EF) hbad
  refine ⟨ω, ?_⟩
  intro i hi b
  by_contra h
  have hmono : ω ∈ monochromaticEvent (σ i) := by
    apply (mem_monochromaticEvent (σ i) ω).mpr
    exact ⟨b, fun j => not_ne_iff.mp (fun hn => h ⟨j, hn⟩)⟩
  apply hω
  by_cases hiA : i ∈ A
  · apply Finset.mem_union.mpr (Or.inr ?_)
    exact Finset.mem_biUnion.mpr ⟨σ i, Finset.mem_image.mpr ⟨i, hiA, rfl⟩, hmono⟩
  · apply Finset.mem_union.mpr (Or.inl ?_)
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hi, hiA⟩, hmono⟩

/-- Actual ordered nonzero-step progressions in a finite cyclic group. -/
def nonzeroProgressions (N : ℕ) [NeZero N] : Finset (ZMod N × ZMod N) :=
  Finset.univ.filter (fun ad => ad.2 ≠ 0)

@[simp] theorem mem_nonzeroProgressions {N : ℕ} [NeZero N] (ad : ZMod N × ZMod N) :
    ad ∈ nonzeroProgressions N ↔ ad.2 ≠ 0 := by
  simp [nonzeroProgressions]

theorem nonzeroProgressions_card_le (N : ℕ) [NeZero N] :
    (nonzeroProgressions N).card ≤ N ^ 2 := by
  calc
    _ ≤ (Finset.univ : Finset (ZMod N × ZMod N)).card := Finset.card_filter_le _ _
    _ = N ^ 2 := by simp [ZMod.card, pow_two]

/-- Literal signatures of the actual cyclic samples. -/
def cyclicSignature {N : ℕ} (c₀ : ZMod N → Bool) (key : ZMod N → Key)
    (ad : ZMod N × ZMod N) : Signature Key k :=
  fun j => let x := ad.1 + (j.val : ZMod N) * ad.2; (c₀ x, key x)

/-- Apply the finite product construction to the actual cyclic group. This
wrapper constructs the coloring itself from the sampled key bits. -/
theorem exists_cyclicAvoids_of_sparse_data {N : ℕ} [NeZero N]
    (c₀ : ZMod N → Bool) (key : ZMod N → Key)
    (A : Finset (ZMod N × ZMod N)) (hA : A ⊆ nonzeroProgressions N)
    {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hmult : ∀ ad ∈ nonzeroProgressions N, ∀ a,
      (Finset.univ.filter (fun j : Fin k => (cyclicSignature (k := k) c₀ key ad j).2 = a)).card ≤ 4)
    (hcases : ∀ ad ∈ nonzeroProgressions N, ad ∈ A ∨ ∀ b,
      k ≤ 100 * (oppositePositions (cyclicSignature (k := k) c₀ key ad) b).card)
    (hbudget : 2 * (N : ℝ) ^ 2 * p ^ ((k + 399) / 400) +
      2 * ((A.image (cyclicSignature (k := k) c₀ key)).card : ℝ) *
        (1 - p) ^ ((k + 3) / 4) < 1) :
    ∃ C : ZMod N → Bool, CyclicAvoids C k := by
  classical
  have hbudget' : 2 * ((nonzeroProgressions N).card : ℝ) * p ^ ((k + 399) / 400) +
      2 * ((A.image (cyclicSignature (k := k) c₀ key)).card : ℝ) *
        (1 - p) ^ ((k + 3) / 4) < 1 := by
    have hc : ((nonzeroProgressions N).card : ℝ) ≤ (N : ℝ) ^ 2 := by
      exact_mod_cast nonzeroProgressions_card_le N
    apply lt_of_le_of_lt _ hbudget
    exact add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num))
        (pow_nonneg hp _)) le_rfl
  obtain ⟨ω, hω⟩ := exists_avoiding_of_rich_or_signature
    (nonzeroProgressions N) A (cyclicSignature (k := k) c₀ key) hA hp hp2 hmult hcases hbudget'
  refine ⟨fun x => Bool.xor (c₀ x) (ω (key x)), ?_⟩
  intro a d hd hmono
  obtain ⟨j, hj⟩ := hω (a, d) ((mem_nonzeroProgressions (a, d)).mpr hd)
    (Bool.xor (c₀ a) (ω (key a)))
  exact hj (hmono j.val j.isLt)

end SparsePerturbation
end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

noncomputable section


namespace QuantitativeVanDerWaerden

open scoped BigOperators

abbrev Vec (D : ℕ) := Fin D → ℝ

def normSq {D : ℕ} (x : Vec D) : ℝ := ∑ i, (x i) ^ 2

def distSq {D : ℕ} (x y : Vec D) : ℝ := ∑ i, (x i - y i) ^ 2

theorem normSq_nonneg {D : ℕ} (x : Vec D) : 0 ≤ normSq x :=
  Finset.sum_nonneg fun i _ => sq_nonneg (x i)

/-- On either nonnegative ray, squared separation is strictly less than
the width of a common half-open quadratic band. -/
theorem weighted_nonneg_band_sq_dist_lt_one (a C m x y : ℝ)
    (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxb : m ≤ a * x ^ 2 + C ∧ a * x ^ 2 + C < m + 1)
    (hyb : m ≤ a * y ^ 2 + C ∧ a * y ^ 2 + C < m + 1) :
    a * (x - y) ^ 2 < 1 := by
  by_cases hxy : x ≤ y
  · have hprod : 0 ≤ a * x * (y - x) :=
      mul_nonneg (mul_nonneg ha hx) (sub_nonneg.mpr hxy)
    nlinarith [hxb.1, hyb.2]
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hprod : 0 ≤ a * y * (x - y) :=
      mul_nonneg (mul_nonneg ha hy) (sub_nonneg.mpr hyx)
    nlinarith [hyb.1, hxb.2]

/-- Weighted scalar packing, including the zero quadratic coefficient.
The parameters may have either sign, and the finite index type is arbitrary. -/
theorem weighted_scalar_band_card_le_two {ι : Type uIndex} (s : Finset ι)
    (t : ι → ℝ) (a C m : ℝ) (ha : 0 ≤ a)
    (hsep : (s : Set ι).Pairwise fun i j => 1 ≤ a * (t i - t j) ^ 2)
    (hband : ∀ i ∈ s, m ≤ a * (t i) ^ 2 + C ∧
      a * (t i) ^ 2 + C < m + 1) :
    s.card ≤ 2 := by
  classical
  have hpos : (s.filter fun i => 0 ≤ t i).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    rcases Finset.mem_filter.mp hi with ⟨his, hit⟩
    rcases Finset.mem_filter.mp hj with ⟨hjs, hjt⟩
    by_contra hij
    exact (not_lt_of_ge (hsep his hjs hij))
      (weighted_nonneg_band_sq_dist_lt_one a C m (t i) (t j)
        ha hit hjt (hband i his) (hband j hjs))
  have hneg : (s.filter fun i => t i < 0).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    rcases Finset.mem_filter.mp hi with ⟨his, hit⟩
    rcases Finset.mem_filter.mp hj with ⟨hjs, hjt⟩
    by_contra hij
    have hd := weighted_nonneg_band_sq_dist_lt_one a C m (-t i) (-t j)
      ha (neg_nonneg.mpr hit.le) (neg_nonneg.mpr hjt.le)
      (by simpa only [neg_sq] using hband i his)
      (by simpa only [neg_sq] using hband j hjs)
    have heq : ((-t i) - (-t j)) ^ 2 = (t i - t j) ^ 2 := by ring
    rw [heq] at hd
    exact (not_lt_of_ge (hsep his hjs hij)) hd
  have hsub : s ⊆ (s.filter fun i => 0 ≤ t i) ∪ (s.filter fun i => t i < 0) := by
    intro i hi
    by_cases ht : 0 ≤ t i
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hi, ht⟩))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hi, lt_of_not_ge ht⟩))
  calc
    s.card ≤ ((s.filter fun i => 0 ≤ t i) ∪ (s.filter fun i => t i < 0)).card :=
      Finset.card_le_card hsub
    _ ≤ (s.filter fun i => 0 ≤ t i).card + (s.filter fun i => t i < 0).card :=
      Finset.card_union_le _ _
    _ ≤ 2 := Nat.add_le_add hpos hneg

/-- Unit-separated real parameters in a common scalar squared-norm band. -/
theorem scalar_band_card_le_two {ι : Type uIndex} (s : Finset ι)
    (t : ι → ℝ) (C m : ℝ)
    (hsep : (s : Set ι).Pairwise fun i j => 1 ≤ |t i - t j|)
    (hband : ∀ i ∈ s, m ≤ (t i) ^ 2 + C ∧ (t i) ^ 2 + C < m + 1) :
    s.card ≤ 2 := by
  apply weighted_scalar_band_card_le_two s t 1 C m zero_le_one
  · intro i hi j hj hij
    have hab := hsep hi hj hij
    have hs : (1 : ℝ) ≤ (t i - t j) ^ 2 := by
      nlinarith [sq_nonneg (|t i - t j| - 1), sq_abs (t i - t j)]
    simpa only [one_mul] using hs
  · intro i hi
    simpa only [one_mul] using hband i hi

theorem scalar_band_card_le_four {ι : Type uIndex} (s : Finset ι)
    (t : ι → ℝ) (C m : ℝ)
    (hsep : (s : Set ι).Pairwise fun i j => 1 ≤ |t i - t j|)
    (hband : ∀ i ∈ s, m ≤ (t i) ^ 2 + C ∧ (t i) ^ 2 + C < m + 1) :
    s.card ≤ 4 :=
  (scalar_band_card_le_two s t C m hsep hband).trans (by decide)

/-- Squared distance on an affine line, without Euclidean projection. -/
theorem distSq_affine {D : ℕ} (A B : Vec D) (u v : ℝ) :
    distSq (fun i => A i + u * B i) (fun i => A i + v * B i) =
      normSq B * (u - v) ^ 2 := by
  unfold distSq normSq
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normSq_affine {D : ℕ} (A B : Vec D) (t : ℝ) :
    normSq (fun i => A i + t * B i) =
      normSq A + 2 * t * (∑ i, A i * B i) + t ^ 2 * normSq B := by
  unfold normSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Completing the scalar quadratic gives the weighted band directly.
The constant term need not be assumed positive for the packing lemma. -/
theorem normSq_affine_complete_square {D : ℕ} (A B : Vec D) (t : ℝ)
    (hB : normSq B ≠ 0) :
    normSq (fun i => A i + t * B i) =
      normSq B * (t + (∑ i, A i * B i) / normSq B) ^ 2 +
        (normSq A - (∑ i, A i * B i) ^ 2 / normSq B) := by
  rw [normSq_affine]
  field_simp [hB]
  ring

end QuantitativeVanDerWaerden

end

end OAI
end
end

section
section
namespace OAI


namespace QuantitativeVanDerWaerden

open scoped BigOperators

abbrev CyclicGroup (q D : ℕ) := ZMod (q ^ D)

noncomputable def centered (x : ℝ) : ℝ := x - (⌊x + 1 / 2⌋ : ℤ)

theorem centered_mem (x : ℝ) : -(1 / 2 : ℝ) ≤ centered x ∧ centered x < 1 / 2 := by
  have h₁ := Int.floor_le (x + 1 / 2)
  have h₂ := Int.lt_floor_add_one (x + 1 / 2)
  constructor <;> dsimp [centered] <;> linarith

theorem centered_add_int (x : ℝ) (z : ℤ) : centered (x + z) = centered x := by
  unfold centered
  rw [show x + (z : ℝ) + 1 / 2 = (x + 1 / 2) + z by ring,
    Int.floor_add_intCast, Int.cast_add]
  ring

theorem centered_int (z : ℤ) : centered (z : ℝ) = 0 := by
  have hz := centered_add_int 0 z
  norm_num [centered] at hz ⊢

noncomputable def xRep (q D : ℕ) (n : CyclicGroup q D) (i : Fin D) : ℝ :=
  Int.fract ((n.val : ℝ) / (q : ℝ) ^ (i.val + 1))

noncomputable def yRep (q D dilation : ℕ) (n : CyclicGroup q D) (i : Fin D) : ℝ :=
  centered (((((dilation : CyclicGroup q D) * n).val : ℕ) : ℝ) /
    (q : ℝ) ^ (i.val + 1))

theorem xRep_mem (q D : ℕ) (n : CyclicGroup q D) (i : Fin D) :
    0 ≤ xRep q D n i ∧ xRep q D n i < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem yRep_mem (q D dilation : ℕ) (n : CyclicGroup q D) (i : Fin D) :
    -(1 / 2 : ℝ) ≤ yRep q D dilation n i ∧ yRep q D dilation n i < 1 / 2 :=
  centered_mem _

/-- Dividing congruent integers by any divisor of the modulus gives real
representatives differing by an integer. -/
theorem quotient_integer_difference {N m : ℕ} (hm : 0 < m) (hdiv : m ∣ N)
    {a b : ℤ} (hab : (a : ZMod N) = (b : ZMod N)) :
    ∃ z : ℤ, (a : ℝ) / m - (b : ℝ) / m = z := by
  have hz : ((a - b : ℤ) : ZMod N) = 0 := by
    push_cast
    exact sub_eq_zero.mpr hab
  have hdN : (N : ℤ) ∣ a - b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have hdm : (m : ℤ) ∣ a - b := (Int.natCast_dvd_natCast.mpr hdiv).trans hdN
  obtain ⟨z, hz⟩ := hdm
  refine ⟨z, ?_⟩
  have hr : (a : ℝ) - b = (m : ℝ) * z := by exact_mod_cast hz
  have hmR : (m : ℝ) ≠ 0 := by positivity
  rw [← sub_div, hr, mul_div_cancel_left₀ _ hmR]

theorem xRep_integer_offset (q D : ℕ) (n : CyclicGroup q D) (i : Fin D) :
    ∃ z : ℤ, xRep q D n i - (n.val : ℝ) / (q : ℝ) ^ (i.val + 1) = z := by
  refine ⟨-⌊(n.val : ℝ) / (q : ℝ) ^ (i.val + 1)⌋, ?_⟩
  simp only [xRep, Int.fract, Int.cast_neg]
  ring

theorem yRep_integer_offset (q D dilation : ℕ) (n : CyclicGroup q D) (i : Fin D) :
    ∃ z : ℤ, yRep q D dilation n i -
      (((dilation : CyclicGroup q D) * n).val : ℝ) / (q : ℝ) ^ (i.val + 1) = z := by
  refine ⟨-⌊(((dilation : CyclicGroup q D) * n).val : ℝ) /
    (q : ℝ) ^ (i.val + 1) + 1 / 2⌋, ?_⟩
  simp only [yRep, centered, Int.cast_neg]
  ring

theorem val_add_integer_difference {q D : ℕ} (hq : 0 < q)
    (a b : CyclicGroup q D) (i : Fin D) :
    ∃ z : ℤ, ((a + b).val : ℝ) / (q : ℝ) ^ (i.val + 1) -
      ((a.val : ℝ) / (q : ℝ) ^ (i.val + 1) +
        (b.val : ℝ) / (q : ℝ) ^ (i.val + 1)) = z := by
  let : NeZero (q ^ D) := ⟨(pow_pos hq D).ne'⟩
  have hi : i.val + 1 ≤ D := i.isLt
  have hab : (((a + b).val : ℤ) : ZMod (q ^ D)) =
      (((a.val : ℤ) + b.val : ℤ) : ZMod (q ^ D)) := by
    simp
  obtain ⟨z, hz⟩ := quotient_integer_difference (pow_pos hq (i.val + 1))
    (pow_dvd_pow q hi) hab
  refine ⟨z, ?_⟩
  simpa only [Int.cast_natCast, Int.cast_add, Nat.cast_pow, add_div] using hz

theorem xRep_add_congr {q D : ℕ} (hq : 0 < q)
    (a b : CyclicGroup q D) (i : Fin D) :
    ∃ z : ℤ, xRep q D (a + b) i - (xRep q D a i + xRep q D b i) = z := by
  obtain ⟨z₁, h₁⟩ := xRep_integer_offset q D (a + b) i
  obtain ⟨z₂, h₂⟩ := xRep_integer_offset q D a i
  obtain ⟨z₃, h₃⟩ := xRep_integer_offset q D b i
  obtain ⟨z₄, h₄⟩ := val_add_integer_difference hq a b i
  refine ⟨z₁ - z₂ - z₃ + z₄, ?_⟩
  push_cast
  linarith

theorem yRep_add_congr {q D : ℕ} (hq : 0 < q) (dilation : ℕ)
    (a b : CyclicGroup q D) (i : Fin D) :
    ∃ z : ℤ, yRep q D dilation (a + b) i -
      (yRep q D dilation a i + yRep q D dilation b i) = z := by
  obtain ⟨z₁, h₁⟩ := yRep_integer_offset q D dilation (a + b) i
  obtain ⟨z₂, h₂⟩ := yRep_integer_offset q D dilation a i
  obtain ⟨z₃, h₃⟩ := yRep_integer_offset q D dilation b i
  obtain ⟨z₄, h₄⟩ := val_add_integer_difference hq
    ((dilation : CyclicGroup q D) * a) ((dilation : CyclicGroup q D) * b) i
  rw [mul_add] at h₁
  refine ⟨z₁ - z₂ - z₃ + z₄, ?_⟩
  push_cast
  linarith

theorem representative_ap_congr {A : Type uA} [AddMonoid A] (f : A → ℝ)
    (_hzero : f 0 = 0)
    (hadd : ∀ a b, ∃ z : ℤ, f (a + b) - (f a + f b) = z)
    (a d : A) (j : ℕ) :
    ∃ z : ℤ, f (a + j • d) - f a - (j : ℝ) * f d = z := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨z₁, h₁⟩ := ih
    obtain ⟨z₂, h₂⟩ := hadd (a + j • d) d
    refine ⟨z₁ + z₂, ?_⟩
    rw [succ_nsmul, ← add_assoc]
    push_cast
    linarith

theorem xRep_ap_congr {q D : ℕ} (hq : 0 < q)
    (a d : CyclicGroup q D) (j : ℕ) (i : Fin D) :
    ∃ z : ℤ, xRep q D (a + j • d) i - xRep q D a i -
      (j : ℝ) * xRep q D d i = z := by
  apply representative_ap_congr (fun n => xRep q D n i)
  · simp [xRep]
  · exact fun a b => xRep_add_congr hq a b i

theorem yRep_ap_congr {q D : ℕ} (hq : 0 < q) (dilation : ℕ)
    (a d : CyclicGroup q D) (j : ℕ) (i : Fin D) :
    ∃ z : ℤ, yRep q D dilation (a + j • d) i - yRep q D dilation a i -
      (j : ℝ) * yRep q D dilation d i = z := by
  apply representative_ap_congr (fun n => yRep q D dilation n i)
  · simpa [yRep] using centered_int 0
  · exact fun a b => yRep_add_congr hq dilation a b i

theorem yRep_dilation_congr {q D : ℕ} (hq : 0 < q) (dilation : ℕ)
    (n : CyclicGroup q D) (i : Fin D) :
    ∃ z : ℤ, yRep q D dilation n i - (dilation : ℝ) * xRep q D n i = z := by
  let : NeZero (q ^ D) := ⟨(pow_pos hq D).ne'⟩
  have hab : (((((dilation : CyclicGroup q D) * n).val : ℕ) : ℤ) :
      ZMod (q ^ D)) = (((dilation : ℤ) * n.val : ℤ) : ZMod (q ^ D)) := by simp
  obtain ⟨z₁, h₁⟩ := quotient_integer_difference (pow_pos hq (i.val + 1))
    (pow_dvd_pow q (show i.val + 1 ≤ D from i.isLt)) hab
  obtain ⟨z₂, h₂⟩ := yRep_integer_offset q D dilation n i
  obtain ⟨z₃, h₃⟩ := xRep_integer_offset q D n i
  refine ⟨z₁ + z₂ - dilation * z₃, ?_⟩
  simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_pow] at h₁
  rw [mul_div_assoc] at h₁
  push_cast
  nlinarith [h₁, h₂, h₃, congrArg (fun t : ℝ => (dilation : ℝ) * t) h₃]

/-- Every centered coordinate lies in the claimed discrete lattice. -/
theorem yRep_lattice (q D dilation : ℕ) (n : CyclicGroup q D) (i : Fin D)
    (hq : 0 < q) :
    ∃ z : ℤ, (q : ℝ) ^ (i.val + 1) * yRep q D dilation n i = z := by
  let a := ((dilation : CyclicGroup q D) * n).val
  let b : ℤ := ⌊(a : ℝ) / (q : ℝ) ^ (i.val + 1) + 1 / 2⌋
  refine ⟨(a : ℤ) - (q : ℤ) ^ (i.val + 1) * b, ?_⟩
  change (q : ℝ) ^ (i.val + 1) *
    ((a : ℝ) / (q : ℝ) ^ (i.val + 1) - (b : ℝ)) = _
  push_cast
  have hqR : (q : ℝ) ^ (i.val + 1) ≠ 0 := by positivity
  field_simp

theorem integer_eq_zero_of_abs_lt_one {z : ℤ} (h : |(z : ℝ)| < 1) : z = 0 := by
  have hh : -(1 : ℤ) < z ∧ z < 1 := by exact_mod_cast (abs_lt.mp h)
  omega

theorem lattice_separation {m : ℕ} (hm : 0 < m) {w : ℝ}
    (hw : ∃ z : ℤ, (m : ℝ) * w = z) (hne : w ≠ 0) : 1 / (m : ℝ) ≤ |w| := by
  obtain ⟨z, hz⟩ := hw
  have hzne : z ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at hz
    exact hne ((mul_eq_zero.mp hz).resolve_left (by positivity))
  have hzabs : 1 ≤ |(z : ℝ)| := by
    by_contra h
    exact hzne (integer_eq_zero_of_abs_lt_one (lt_of_not_ge h))
  have hmR : 0 < (m : ℝ) := by positivity
  rw [← hz, abs_mul, abs_of_pos hmR] at hzabs
  exact (div_le_iff₀ hmR).mpr (by simpa [mul_comm] using hzabs)

/-- The representative at exponent zero is included as an auxiliary coordinate. -/
noncomputable def centeredDigit (q a j : ℕ) : ℝ := centered ((a : ℝ) / (q : ℝ) ^ j)

theorem centeredDigit_zero (q a : ℕ) : centeredDigit q a 0 = 0 := by
  simpa [centeredDigit] using centered_int (a : ℤ)

theorem centeredDigit_recurrence {q : ℕ} (hq : 0 < q) (a j : ℕ) :
    ∃ z : ℤ, (q : ℝ) * centeredDigit q a (j + 1) - centeredDigit q a j = z := by
  refine ⟨⌊(a : ℝ) / (q : ℝ) ^ j + 1 / 2⌋ -
    (q : ℤ) * ⌊(a : ℝ) / (q : ℝ) ^ (j + 1) + 1 / 2⌋, ?_⟩
  unfold centeredDigit centered
  push_cast
  have hqR : (q : ℝ) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp
  ring

theorem centered_injective_on_unit_interval {x y : ℝ}
    (hx : 0 ≤ x ∧ x < 1) (hy : 0 ≤ y ∧ y < 1)
    (h : centered x = centered y) : x = y := by
  let z : ℤ := ⌊x + 1 / 2⌋ - ⌊y + 1 / 2⌋
  have hz : x - y = (z : ℝ) := by
    dsimp [centered] at h
    dsimp [z]
    push_cast
    linarith
  have hzabs : |(z : ℝ)| < 1 := by rw [← hz, abs_lt]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hz0 := integer_eq_zero_of_abs_lt_one hzabs
  rw [hz0, Int.cast_zero] at hz
  exact sub_eq_zero.mp hz

/-- The cyclic digit embedding separates distinct residues after multiplication
by `q`. This proof works for every positive base, not just primes. -/
theorem centeredDigit_separation {q D a b : ℕ} (hq : 0 < q)
    (ha : a < q ^ D) (hb : b < q ^ D) (hab : a ≠ b) :
    ∃ i : Fin D, 1 ≤ |(q : ℝ) *
      (centeredDigit q a (i.val + 1) - centeredDigit q b (i.val + 1))| := by
  by_contra! h
  have hdiff : ∀ j, j ≤ D → centeredDigit q a j - centeredDigit q b j = 0 := by
    intro j hj
    induction j with
    | zero => simp [centeredDigit_zero]
    | succ j ih =>
      have hp := ih (by omega)
      obtain ⟨za, hza⟩ := centeredDigit_recurrence hq a j
      obtain ⟨zb, hzb⟩ := centeredDigit_recurrence hq b j
      have hh : (q : ℝ) * (centeredDigit q a (j + 1) - centeredDigit q b (j + 1)) =
          ((za - zb : ℤ) : ℝ) := by push_cast; linarith
      have hz := integer_eq_zero_of_abs_lt_one
        (show |((za - zb : ℤ) : ℝ)| < 1 by rw [← hh]; exact h ⟨j, by omega⟩)
      rw [hz, Int.cast_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_left (by positivity)
  have hN : 0 < (q : ℝ) ^ D := by positivity
  have habR : (a : ℝ) / (q : ℝ) ^ D = (b : ℝ) / (q : ℝ) ^ D := by
    apply centered_injective_on_unit_interval
    · constructor
      · positivity
      · apply (div_lt_one hN).mpr
        exact_mod_cast ha
    · constructor
      · positivity
      · apply (div_lt_one hN).mpr
        exact_mod_cast hb
    · exact sub_eq_zero.mp (hdiff D le_rfl)
  apply hab
  exact_mod_cast (div_left_inj' hN.ne').mp habR

theorem yRep_coordinate_separation {q D dilation : ℕ} (hq : 0 < q)
    (hunit : Nat.Coprime dilation (q ^ D))
    {a b : CyclicGroup q D} (hab : a ≠ b) :
    ∃ i : Fin D, 1 ≤ |(q : ℝ) * (yRep q D dilation a i - yRep q D dilation b i)| := by
  let : NeZero (q ^ D) := ⟨(pow_pos hq D).ne'⟩
  have hu : IsUnit (dilation : CyclicGroup q D) := (ZMod.isUnit_iff_coprime _ _).mpr hunit
  have hne : ((dilation : CyclicGroup q D) * a).val ≠
      ((dilation : CyclicGroup q D) * b).val := by
    intro h
    exact hab (hu.mul_left_cancel (ZMod.val_injective (q ^ D) h))
  exact centeredDigit_separation hq (ZMod.val_lt _) (ZMod.val_lt _) hne

theorem yRep_squared_separation {q D dilation : ℕ} (hq : 0 < q)
    (hunit : Nat.Coprime dilation (q ^ D))
    {a b : CyclicGroup q D} (hab : a ≠ b) :
    1 ≤ ∑ i : Fin D, ((q : ℝ) * yRep q D dilation a i -
      (q : ℝ) * yRep q D dilation b i) ^ 2 := by
  obtain ⟨i, hi⟩ := yRep_coordinate_separation hq hunit hab
  have hsq : 1 ≤ ((q : ℝ) * yRep q D dilation a i -
      (q : ℝ) * yRep q D dilation b i) ^ 2 := by
    rw [mul_sub] at hi
    nlinarith [sq_nonneg (|(q : ℝ) * yRep q D dilation a i -
      (q : ℝ) * yRep q D dilation b i| - 1),
      sq_abs ((q : ℝ) * yRep q D dilation a i - (q : ℝ) * yRep q D dilation b i)]
  exact hsq.trans (Finset.single_le_sum
    (fun j _ => sq_nonneg ((q : ℝ) * yRep q D dilation a j -
      (q : ℝ) * yRep q D dilation b j)) (Finset.mem_univ i))

theorem prime_power_step_ne {P e i j : ℕ} (hP : P.Prime)
    (hij : i < j) (hj : j < P) {d : ZMod (P ^ e)} (hd : d ≠ 0) :
    (i : ZMod (P ^ e)) * d ≠ (j : ZMod (P ^ e)) * d := by
  intro h
  have hpos : 0 < j - i := Nat.sub_pos_of_lt hij
  have hlt : j - i < P := lt_of_le_of_lt (Nat.sub_le _ _) hj
  have hcop : Nat.Coprime (j - i) (P ^ e) :=
    (Nat.coprime_of_lt_prime (Nat.ne_of_gt hpos) hlt hP).symm.pow_right e
  have hu := (ZMod.isUnit_iff_coprime (j - i) (P ^ e)).mpr hcop
  have hz : ((j - i : ℕ) : ZMod (P ^ e)) * d = 0 := by
    rw [Nat.cast_sub hij.le, sub_mul, h, sub_self]
  exact hd (hu.mul_left_cancel (by simpa using hz))

theorem prime_power_ap_injective {P e k : ℕ} (hP : P.Prime) (hk : k ≤ P)
    (a d : ZMod (P ^ e)) (hd : d ≠ 0) :
    Function.Injective (fun j : Fin k => a + (j.val : ZMod (P ^ e)) * d) := by
  intro i j hij
  have hm := add_left_cancel hij
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact prime_power_step_ne hP hlt (lt_of_lt_of_le j.isLt hk) hd hm
  · exact prime_power_step_ne hP hlt (lt_of_lt_of_le i.isLt hk) hd hm.symm

theorem prime_power_ap_injective_pow {P e D k : ℕ} (hP : P.Prime) (hk : k ≤ P)
    (a d : CyclicGroup (P ^ e) D) (hd : d ≠ 0) :
    Function.Injective (fun j : Fin k => a + (j.val : CyclicGroup (P ^ e) D) * d) := by
  have hstep : ∀ i j : ℕ, i < j → j < P →
      (i : CyclicGroup (P ^ e) D) * d ≠ (j : CyclicGroup (P ^ e) D) * d := by
    intro i j hij hj heq
    have hpos : 0 < j - i := Nat.sub_pos_of_lt hij
    have hlt : j - i < P := lt_of_le_of_lt (Nat.sub_le _ _) hj
    have hcop : Nat.Coprime (j - i) ((P ^ e) ^ D) :=
      ((Nat.coprime_of_lt_prime (Nat.ne_of_gt hpos) hlt hP).symm.pow_right e).pow_right D
    have hu := (ZMod.isUnit_iff_coprime (j - i) ((P ^ e) ^ D)).mpr hcop
    have hz : ((j - i : ℕ) : CyclicGroup (P ^ e) D) * d = 0 := by
      rw [Nat.cast_sub hij.le, sub_mul, heq, sub_self]
    exact hd (hu.mul_left_cancel (by simpa using hz))
  intro i j hij
  have hm := add_left_cancel hij
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hstep i.val j.val hlt (lt_of_lt_of_le j.isLt hk) hm
  · exact hstep j.val i.val hlt (lt_of_lt_of_le i.isLt hk) hm.symm

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Affinity of representatives inside a small box

The input is the integer-valued cross difference of three representatives of
an arithmetic progression modulo one. A box of width `2 * H` makes this integer
strictly smaller than one in absolute value, so it vanishes. Interpolation then
produces one real affine lift on all selected indices.
-/


namespace QuantitativeVanDerWaerden

/-- An integer whose real absolute value is less than one vanishes. -/
theorem integer_zero_of_abs_lt_one {m : ℤ} (h : |(m : ℝ)| < 1) : m = 0 := by
  have hm : |m| < 1 := by exact_mod_cast h
  exact Int.abs_lt_one_iff.mp hm

/-- Integer errors in affine representatives imply an integer cross difference.
No ordering assumption on the three indices is needed here. -/
theorem triple_integral_of_integer_errors {z : ℕ → ℝ} {A B : ℝ}
    (h : ∀ j, ∃ m : ℤ, z j - A - (j : ℝ) * B = (m : ℝ))
    (a b c : ℕ) :
    ∃ m : ℤ, ((c : ℝ) - b) * (z b - z a) -
      ((b : ℝ) - a) * (z c - z b) = (m : ℝ) := by
  obtain ⟨ma, ha⟩ := h a
  obtain ⟨mb, hb⟩ := h b
  obtain ⟨mc, hc⟩ := h c
  have hza : z a = A + (a : ℝ) * B + (ma : ℝ) := by linarith
  have hzb : z b = A + (b : ℝ) * B + (mb : ℝ) := by linarith
  have hzc : z c = A + (c : ℝ) * B + (mc : ℝ) := by linarith
  refine ⟨((c : ℤ) - b) * (mb - ma) - ((b : ℤ) - a) * (mc - mb), ?_⟩
  rw [hza, hzb, hzc]
  push_cast
  ring

/-- The cross difference of three points in a short real interval is small. -/
theorem abs_cross_difference_lt_one {k a b c : ℕ} {H : ℝ} {z : ℕ → ℝ}
    (hab : a < b) (hbc : b < c) (hck : c < k)
    (hH : 0 ≤ H) (hsmall : 2 * (k : ℝ) * H < 1)
    (habox : |z b - z a| ≤ 2 * H) (hbbox : |z c - z b| ≤ 2 * H) :
    |((c : ℝ) - b) * (z b - z a) -
      ((b : ℝ) - a) * (z c - z b)| < 1 := by
  have hbc' : (b : ℝ) ≤ c := by exact_mod_cast hbc.le
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab.le
  have hp : 0 ≤ (c : ℝ) - b := sub_nonneg.mpr hbc'
  have hq : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr hab'
  have hck' : (c : ℝ) ≤ k := by exact_mod_cast hck.le
  have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  calc
    _ ≤ |((c : ℝ) - b) * (z b - z a)| +
        |((b : ℝ) - a) * (z c - z b)| := abs_sub _ _
    _ = ((c : ℝ) - b) * |z b - z a| +
        ((b : ℝ) - a) * |z c - z b| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]
    _ ≤ ((c : ℝ) - b) * (2 * H) + ((b : ℝ) - a) * (2 * H) :=
      add_le_add (mul_le_mul_of_nonneg_left habox hp)
        (mul_le_mul_of_nonneg_left hbbox hq)
    _ = 2 * ((c : ℝ) - a) * H := by ring
    _ ≤ 2 * (k : ℝ) * H := mul_le_mul_of_nonneg_right (by linarith) hH
    _ < 1 := hsmall

/-- In a small box, the integral cross difference is exactly zero. -/
theorem cross_difference_eq_zero_of_small_box {k a b c : ℕ} {H : ℝ}
    {z : ℕ → ℝ} (hab : a < b) (hbc : b < c) (hck : c < k)
    (hH : 0 ≤ H) (hsmall : 2 * (k : ℝ) * H < 1)
    (habox : |z b - z a| ≤ 2 * H) (hbbox : |z c - z b| ≤ 2 * H)
    (hint : ∃ m : ℤ, ((c : ℝ) - b) * (z b - z a) -
      ((b : ℝ) - a) * (z c - z b) = (m : ℝ)) :
    ((c : ℝ) - b) * (z b - z a) -
      ((b : ℝ) - a) * (z c - z b) = 0 := by
  obtain ⟨m, hm⟩ := hint
  have h := abs_cross_difference_lt_one hab hbc hck hH hsmall habox hbbox
  rw [hm] at h
  have hmzero := integer_zero_of_abs_lt_one h
  simpa [hmzero] using hm

/-- Vanishing cross differences on ordered triples give one affine interpolation
on a finite set, including the empty and singleton cases. -/
theorem exists_affine_of_cross_difference_eq_zero (J : Finset ℕ) (z : ℕ → ℝ)
    (hcross : ∀ a ∈ J, ∀ b ∈ J, ∀ c ∈ J, a < b → b < c →
      ((c : ℝ) - b) * (z b - z a) -
        ((b : ℝ) - a) * (z c - z b) = 0) :
    ∃ A B : ℝ, ∀ j ∈ J, z j = A + (j : ℝ) * B := by
  by_cases hJ : J.Nonempty
  · let a := J.min' hJ
    let b := J.max' hJ
    have ha : a ∈ J := Finset.min'_mem J hJ
    have hb : b ∈ J := Finset.max'_mem J hJ
    have hmin (j : ℕ) (hj : j ∈ J) : a ≤ j := Finset.min'_le J j hj
    have hmax (j : ℕ) (hj : j ∈ J) : j ≤ b := Finset.le_max' J j hj
    by_cases hab : a = b
    · refine ⟨z a, 0, ?_⟩
      intro j hj
      have hja : j = a :=
        le_antisymm ((hmax j hj).trans (le_of_eq hab.symm)) (hmin j hj)
      simp [hja]
    · have hablt : a < b := lt_of_le_of_ne (hmin b hb) hab
      have hablt' : (a : ℝ) < b := by exact_mod_cast hablt
      have hd : (b : ℝ) - a ≠ 0 := ne_of_gt (sub_pos.mpr hablt')
      let B : ℝ := (z b - z a) / ((b : ℝ) - a)
      refine ⟨z a - (a : ℝ) * B, B, ?_⟩
      intro j hj
      have hscale : (z j - z a) * ((b : ℝ) - a) =
          ((j : ℝ) - a) * (z b - z a) := by
        by_cases hja : j = a
        · rw [hja]
          ring
        by_cases hjb : j = b
        · rw [hjb]
          ring
        have haj : a < j := lt_of_le_of_ne (hmin j hj) (Ne.symm hja)
        have hjb' : j < b := lt_of_le_of_ne (hmax j hj) hjb
        have hc := hcross a ha j hj b hb haj hjb'
        nlinarith only [hc]
      have hquot : z j - z a =
          ((j : ℝ) - a) * (z b - z a) / ((b : ℝ) - a) :=
        (eq_div_iff hd).2 hscale
      calc
        z j = z a + (z j - z a) := by ring
        _ = z a + ((j : ℝ) - a) * (z b - z a) / ((b : ℝ) - a) := by
          rw [hquot]
        _ = z a - (a : ℝ) * B + (j : ℝ) * B := by
          dsimp only [B]
          ring
  · refine ⟨0, 0, ?_⟩
    intro j hj
    exact (hJ ⟨j, hj⟩).elim

/-- Scalar affinity inside a box of width `2 * H`. The integer premise is the
explicit consequence of arithmetic progression modulo one. -/
theorem exists_affine_of_small_box {k : ℕ} {H : ℝ}
    (J : Finset ℕ) (z : ℕ → ℝ) (hJ : ∀ j ∈ J, j < k)
    (hH : 0 ≤ H) (hsmall : 2 * (k : ℝ) * H < 1)
    (hbox : ∀ i ∈ J, ∀ j ∈ J, |z j - z i| ≤ 2 * H)
    (hint : ∀ a ∈ J, ∀ b ∈ J, ∀ c ∈ J, a < b → b < c →
      ∃ m : ℤ, ((c : ℝ) - b) * (z b - z a) -
        ((b : ℝ) - a) * (z c - z b) = (m : ℝ)) :
    ∃ A B : ℝ, ∀ j ∈ J, z j = A + (j : ℝ) * B := by
  apply exists_affine_of_cross_difference_eq_zero J z
  intro a ha b hb c hc hab hbc
  exact cross_difference_eq_zero_of_small_box hab hbc (hJ c hc) hH hsmall
    (hbox a ha b hb) (hbox b hb c hc) (hint a ha b hb c hc hab hbc)

/-- The coordinatewise form gives a single real affine vector lift. In the
application the coordinate type is `Fin D` (or two copies of `Fin D`). -/
theorem exists_affine_of_small_box_vector {ι : Type uIndex} {k : ℕ} {H : ℝ}
    (J : Finset ℕ) (z : ℕ → ι → ℝ) (hJ : ∀ j ∈ J, j < k)
    (hH : 0 ≤ H) (hsmall : 2 * (k : ℝ) * H < 1)
    (hbox : ∀ i ∈ J, ∀ j ∈ J, ∀ d, |z j d - z i d| ≤ 2 * H)
    (hint : ∀ a ∈ J, ∀ b ∈ J, ∀ c ∈ J, a < b → b < c → ∀ d,
      ∃ m : ℤ, ((c : ℝ) - b) * (z b d - z a d) -
        ((b : ℝ) - a) * (z c d - z b d) = (m : ℝ)) :
    ∃ A B : ι → ℝ, ∀ j ∈ J, ∀ d, z j d = A d + (j : ℝ) * B d := by
  classical
  have hcoord : ∀ d : ι, ∃ A B : ℝ, ∀ j ∈ J,
      z j d = A + (j : ℝ) * B := by
    intro d
    exact exists_affine_of_small_box J (fun j => z j d) hJ hH hsmall
      (fun i hi j hj => hbox i hi j hj d)
      (fun a ha b hb c hc hab hbc => hint a ha b hb c hc hab hbc d)
  choose A B hAB using hcoord
  exact ⟨A, B, fun j hj d => hAB d j hj⟩

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

namespace QuantitativeVanDerWaerden

/-- Distance to the cut, expressed using the centered representative. -/
noncomputable def rho (x : ℝ) : ℝ := 1 / 2 - |centered x|

theorem rho_nonneg (x : ℝ) : 0 ≤ rho x := by
  have hx := centered_mem x
  have ha : |centered x| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨hx.1, hx.2.le⟩
  unfold rho
  linarith

theorem rho_le_half (x : ℝ) : rho x ≤ 1 / 2 := by
  unfold rho
  linarith [abs_nonneg (centered x)]

theorem rho_add_int (x : ℝ) (z : ℤ) : rho (x + z) = rho x := by
  simp only [rho, centered_add_int]

structure AdaptiveMesh where
  H : ℝ
  alpha : ℝ
  H_pos : 0 < H
  H_le : H ≤ 1 / 8
  alpha_pos : 0 < alpha
  alpha_le : alpha ≤ 1 / 4

namespace AdaptiveMesh

variable (A : AdaptiveMesh)

noncomputable def R : ℝ := Real.log (1 + 1 / (2 * A.alpha))
noncomputable def m : ℕ := ⌈A.R / A.H⌉₊
noncomputable def theta : ℝ := A.R / A.m
noncomputable def endpoint (j : ℕ) : ℝ :=
  A.alpha * (Real.exp ((j : ℝ) * A.theta) - 1)
noncomputable def radialWidth (j : ℕ) : ℝ := A.endpoint (j + 1) - A.endpoint j

theorem argument_ge_three : (3 : ℝ) ≤ 1 + 1 / (2 * A.alpha) := by
  have hp : 0 < 2 * A.alpha := by nlinarith [A.alpha_pos]
  have h : (2 : ℝ) ≤ 1 / (2 * A.alpha) :=
    (le_div_iff₀ hp).mpr (by nlinarith [A.alpha_le])
  linarith

theorem one_le_R : (1 : ℝ) ≤ A.R := by
  have hp : 0 < 1 + 1 / (2 * A.alpha) := by
    linarith [A.argument_ge_three]
  apply (Real.le_log_iff_exp_le hp).mpr
  have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  exact he.le.trans A.argument_ge_three

theorem R_pos : 0 < A.R := lt_of_lt_of_le (by norm_num) A.one_le_R

theorem m_pos : 0 < A.m := by
  exact Nat.ceil_pos.mpr (div_pos A.R_pos A.H_pos)

theorem m_cast_pos : (0 : ℝ) < A.m := by exact_mod_cast A.m_pos

theorem theta_pos : 0 < A.theta := div_pos A.R_pos A.m_cast_pos

theorem theta_le_H : A.theta ≤ A.H := by
  have hc : A.R / A.H ≤ (A.m : ℝ) := Nat.le_ceil _
  have hc' : A.R ≤ (A.m : ℝ) * A.H := (div_le_iff₀ A.H_pos).mp hc
  exact (div_le_iff₀ A.m_cast_pos).mpr (by simpa [mul_comm] using hc')

theorem half_H_le_theta : A.H / 2 ≤ A.theta := by
  have hHR : A.H ≤ A.R := by linarith [A.H_le, A.one_le_R]
  have hone : (1 : ℝ) ≤ A.R / A.H := (le_div_iff₀ A.H_pos).mpr (by simpa using hHR)
  have hc : (A.m : ℝ) < A.R / A.H + 1 :=
    Nat.ceil_lt_add_one (le_of_lt (div_pos A.R_pos A.H_pos))
  have hmul : (A.m : ℝ) * A.H ≤ 2 * A.R := by
    have hm : (A.m : ℝ) ≤ (2 * A.R) / A.H := by
      rw [mul_div_assoc]
      linarith
    exact (le_div_iff₀ A.H_pos).mp hm
  exact (le_div_iff₀ A.m_cast_pos).mpr (by nlinarith)

theorem theta_le_eighth : A.theta ≤ 1 / 8 := A.theta_le_H.trans A.H_le

theorem exp_theta_le_two : Real.exp A.theta ≤ 2 := by
  have ht : A.theta < 1 := by linarith [A.theta_le_eighth]
  have he := Real.exp_bound_div_one_sub_of_interval A.theta_pos.le ht
  have hm : Real.exp A.theta * (1 - A.theta) ≤ 1 :=
    (le_div_iff₀ (by linarith : 0 < 1 - A.theta)).mp he
  nlinarith [Real.exp_pos A.theta, A.theta_le_eighth]

theorem exp_theta_sub_one_le : Real.exp A.theta - 1 ≤ 2 * A.theta := by
  have ht : A.theta < 1 := by linarith [A.theta_le_eighth]
  have he := Real.exp_bound_div_one_sub_of_interval A.theta_pos.le ht
  have hm : Real.exp A.theta * (1 - A.theta) ≤ 1 :=
    (le_div_iff₀ (by linarith : 0 < 1 - A.theta)).mp he
  have hp := mul_nonneg A.theta_pos.le (sub_nonneg.mpr A.exp_theta_le_two)
  nlinarith

theorem theta_le_exp_theta_sub_one : A.theta ≤ Real.exp A.theta - 1 := by
  linarith [Real.add_one_le_exp A.theta]

@[simp] theorem endpoint_zero : A.endpoint 0 = 0 := by simp [endpoint]

theorem endpoint_strictMono : StrictMono A.endpoint := by
  intro i j hij
  unfold endpoint
  apply mul_lt_mul_of_pos_left _ A.alpha_pos
  apply sub_lt_sub_right
  apply Real.exp_lt_exp.mpr
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) A.theta_pos

theorem endpoint_m : A.endpoint A.m = 1 / 2 := by
  have hm : (A.m : ℝ) ≠ 0 := ne_of_gt A.m_cast_pos
  have hmt : (A.m : ℝ) * A.theta = A.R := by
    dsimp [theta]
    field_simp [hm]
  have hp : 0 < 1 + 1 / (2 * A.alpha) := by
    linarith [A.argument_ge_three]
  rw [endpoint, hmt, R, Real.exp_log hp]
  have ha : A.alpha ≠ 0 := ne_of_gt A.alpha_pos
  field_simp [ha]
  ring

theorem radialWidth_pos (j : ℕ) : 0 < A.radialWidth j := by
  exact sub_pos.mpr (A.endpoint_strictMono (Nat.lt_succ_self j))

theorem radialWidth_eq (j : ℕ) :
    A.radialWidth j = A.alpha * Real.exp ((j : ℝ) * A.theta) *
      (Real.exp A.theta - 1) := by
  simp only [radialWidth, endpoint, Nat.cast_add, Nat.cast_one, add_mul,
    one_mul, Real.exp_add]
  ring

/-- The width estimate holds on the closed radial interval; this includes
the circle cut and zero once the two halves are realized as intervals. -/
theorem radial_width_bounds (j : ℕ) (r : ℝ)
    (hl : A.endpoint j ≤ r) (hu : r ≤ A.endpoint (j + 1)) :
    A.H / 4 * (r + A.alpha) ≤ A.radialWidth j ∧
      A.radialWidth j ≤ 2 * A.H * (r + A.alpha) := by
  let b := A.alpha * Real.exp ((j : ℝ) * A.theta)
  have hH : 0 < A.H := A.H_pos
  have hb : 0 < b := mul_pos A.alpha_pos (Real.exp_pos _)
  have hl' : b ≤ r + A.alpha := by dsimp [endpoint] at hl; dsimp [b]; nlinarith
  have hu' : r + A.alpha ≤ b * Real.exp A.theta := by
    simp only [endpoint, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      Real.exp_add] at hu
    dsimp [b]
    nlinarith
  have hr : r + A.alpha ≤ 2 * b := by
    calc
      r + A.alpha ≤ b * Real.exp A.theta := hu'
      _ ≤ b * 2 := mul_le_mul_of_nonneg_left A.exp_theta_le_two hb.le
      _ = 2 * b := by ring
  rw [A.radialWidth_eq]
  change A.H / 4 * (r + A.alpha) ≤ b * (Real.exp A.theta - 1) ∧
    b * (Real.exp A.theta - 1) ≤ 2 * A.H * (r + A.alpha)
  constructor
  · calc
      A.H / 4 * (r + A.alpha) ≤ A.H / 4 * (2 * b) := by gcongr
      _ = b * (A.H / 2) := by ring
      _ ≤ b * A.theta := mul_le_mul_of_nonneg_left A.half_H_le_theta hb.le
      _ ≤ b * (Real.exp A.theta - 1) :=
        mul_le_mul_of_nonneg_left A.theta_le_exp_theta_sub_one hb.le
  · calc
      b * (Real.exp A.theta - 1) ≤ b * (2 * A.theta) :=
        mul_le_mul_of_nonneg_left A.exp_theta_sub_one_le hb.le
      _ ≤ b * (2 * A.H) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left A.theta_le_H (by norm_num)) hb.le
      _ ≤ (r + A.alpha) * (2 * A.H) :=
        mul_le_mul_of_nonneg_right hl' (by positivity)
      _ = 2 * A.H * (r + A.alpha) := by ring

/-- `false` denotes the negative half and `true` the positive half. -/
abbrev Label := Bool × Fin A.m

noncomputable def left (i : A.Label) : ℝ :=
  if i.1 then 1 / 2 - A.endpoint (i.2.val + 1) else -1 / 2 + A.endpoint i.2.val

noncomputable def right (i : A.Label) : ℝ :=
  if i.1 then 1 / 2 - A.endpoint i.2.val else -1 / 2 + A.endpoint (i.2.val + 1)

def Contains (i : A.Label) (x : ℝ) : Prop := A.left i ≤ x ∧ x < A.right i

noncomputable def width (i : A.Label) : ℝ := A.right i - A.left i

theorem width_eq_radialWidth (i : A.Label) : A.width i = A.radialWidth i.2.val := by
  rcases i with ⟨side, i⟩
  cases side <;> dsimp [width, left, right, radialWidth] <;> ring

theorem width_pos (i : A.Label) : 0 < A.width i := by
  rw [A.width_eq_radialWidth]
  exact A.radialWidth_pos _

end AdaptiveMesh
end QuantitativeVanDerWaerden

/- Actual half-open labels and their periodic geometry. -/

namespace QuantitativeVanDerWaerden

theorem centered_eq_of_mem {x : ℝ}
    (hl : -(1 / 2 : ℝ) ≤ x) (hu : x < 1 / 2) : centered x = x := by
  have hf : ⌊x + 1 / 2⌋ = (0 : ℤ) :=
    Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
  simp only [centered, hf, Int.cast_zero, sub_zero]

theorem rho_eq_of_closed_mem {x : ℝ}
    (hl : -(1 / 2 : ℝ) ≤ x) (hu : x ≤ 1 / 2) : rho x = 1 / 2 - |x| := by
  rcases hu.eq_or_lt with hx | hx
  · subst x
    norm_num [rho, centered]
  · rw [rho, centered_eq_of_mem hl hx]

private theorem abs_le_abs_add_int {x : ℝ}
    (hl : -(1 / 2 : ℝ) ≤ x) (hu : x ≤ 1 / 2) (z : ℤ) : |x| ≤ |x + z| := by
  have ha : |x| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨hl, hu⟩
  rcases lt_trichotomy z 0 with hz | hz | hz
  · have hz' : (z : ℝ) ≤ -1 := by exact_mod_cast (show z ≤ -1 by omega)
    rw [abs_of_nonpos (by linarith : x + (z : ℝ) ≤ 0)]
    linarith
  · subst z
    simp
  · have hz' : (1 : ℝ) ≤ z := by exact_mod_cast (show 1 ≤ z by omega)
    rw [abs_of_nonneg (by linarith : 0 ≤ x + (z : ℝ))]
    linarith

theorem centered_abs_minimal (x : ℝ) (z : ℤ) : |centered x| ≤ |x - z| := by
  have hc := centered_mem x
  have h := abs_le_abs_add_int hc.1 hc.2.le (⌊x + 1 / 2⌋ - z)
  convert h using 1
  congr 1
  simp only [centered, Int.cast_sub]
  ring

theorem centered_abs_sub_le (x y : ℝ) : |centered x| - |centered y| ≤ |x - y| := by
  have hm := centered_abs_minimal x ⌊y + 1 / 2⌋
  have he : x - (⌊y + 1 / 2⌋ : ℤ) = (x - y) + centered y := by
    dsimp [centered]
    ring
  rw [he] at hm
  have ht := abs_add_le (x - y) (centered y)
  linarith

theorem rho_lipschitz (x y : ℝ) : |rho x - rho y| ≤ |x - y| := by
  have hxy := centered_abs_sub_le x y
  have hyx := centered_abs_sub_le y x
  rw [abs_sub_comm y x] at hyx
  apply abs_le.mpr
  unfold rho
  constructor <;> linarith

theorem rho_lipschitz_integer (x y : ℝ) (z : ℤ) :
    |rho x - rho y| ≤ |x - y - z| := by
  have h := rho_lipschitz x (y + z)
  rw [rho_add_int] at h
  simpa only [sub_add_eq_sub_sub] using h

namespace AdaptiveMesh

variable (A : AdaptiveMesh)

private theorem increasing_cover_Ico (f : ℕ → ℝ) (_hf : StrictMono f)
    (n : ℕ) (r : ℝ) (hl : f 0 ≤ r) (hu : r < f n) :
    ∃ i : Fin n, f i.val ≤ r ∧ r < f (i.val + 1) := by
  classical
  have he : ∃ j : ℕ, r < f j := ⟨n, hu⟩
  let j := Nat.find he
  have hj : r < f j := Nat.find_spec he
  have hjn : j ≤ n := Nat.find_min' he hu
  have hj0 : 0 < j := by
    by_contra h
    have hz : j = 0 := by omega
    rw [hz] at hj
    linarith
  refine ⟨⟨j - 1, by omega⟩, ?_, ?_⟩
  · have hm : ¬ r < f (j - 1) := Nat.find_min he (by omega)
    exact le_of_not_gt hm
  · simpa only [show j - 1 + 1 = j by omega] using hj

private theorem increasing_cover_Ioc (f : ℕ → ℝ) (_hf : StrictMono f)
    (n : ℕ) (r : ℝ) (hl : f 0 < r) (hu : r ≤ f n) :
    ∃ i : Fin n, f i.val < r ∧ r ≤ f (i.val + 1) := by
  classical
  have he : ∃ j : ℕ, r ≤ f j := ⟨n, hu⟩
  let j := Nat.find he
  have hj : r ≤ f j := Nat.find_spec he
  have hjn : j ≤ n := Nat.find_min' he hu
  have hj0 : 0 < j := by
    by_contra h
    have hz : j = 0 := by omega
    rw [hz] at hj
    linarith
  refine ⟨⟨j - 1, by omega⟩, ?_, ?_⟩
  · have hm : ¬ r ≤ f (j - 1) := Nat.find_min he (by omega)
    exact lt_of_not_ge hm
  · simpa only [show j - 1 + 1 = j by omega] using hj

theorem endpoint_nonneg (j : ℕ) : 0 ≤ A.endpoint j := by
  have h := A.endpoint_strictMono.monotone (Nat.zero_le j)
  simpa using h

theorem endpoint_le_half {j : ℕ} (hj : j ≤ A.m) : A.endpoint j ≤ 1 / 2 := by
  have h := A.endpoint_strictMono.monotone hj
  simpa only [A.endpoint_m] using h

theorem left_ge_neg_half (i : A.Label) : -(1 / 2 : ℝ) ≤ A.left i := by
  rcases i with ⟨side, i⟩
  have h0 := A.endpoint_nonneg i.val
  have h1 := A.endpoint_le_half (show i.val + 1 ≤ A.m from i.isLt)
  cases side <;> dsimp [left] <;> linarith

theorem right_le_half (i : A.Label) : A.right i ≤ 1 / 2 := by
  rcases i with ⟨side, i⟩
  have h0 := A.endpoint_nonneg i.val
  have h1 := A.endpoint_le_half (show i.val + 1 ≤ A.m from i.isLt)
  cases side <;> dsimp [right] <;> linarith

theorem contains_iff_negative (i : Fin A.m) (x : ℝ) :
    A.Contains (false, i) x ↔
      A.endpoint i.val ≤ x + 1 / 2 ∧ x + 1 / 2 < A.endpoint (i.val + 1) := by
  dsimp [Contains, left, right]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem contains_iff_positive (i : Fin A.m) (x : ℝ) :
    A.Contains (true, i) x ↔
      A.endpoint i.val < 1 / 2 - x ∧ 1 / 2 - x ≤ A.endpoint (i.val + 1) := by
  dsimp [Contains, left, right]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem exists_label {x : ℝ} (hl : -(1 / 2 : ℝ) ≤ x) (hu : x < 1 / 2) :
    ∃ i : A.Label, A.Contains i x := by
  by_cases hx : x < 0
  · obtain ⟨i, hi⟩ := increasing_cover_Ico A.endpoint A.endpoint_strictMono A.m
      (x + 1 / 2) (by rw [A.endpoint_zero]; linarith)
      (by rw [A.endpoint_m]; linarith)
    exact ⟨(false, i), (A.contains_iff_negative i x).mpr hi⟩
  · obtain ⟨i, hi⟩ := increasing_cover_Ioc A.endpoint A.endpoint_strictMono A.m
      (1 / 2 - x) (by rw [A.endpoint_zero]; linarith)
      (by rw [A.endpoint_m]; linarith)
    exact ⟨(true, i), (A.contains_iff_positive i x).mpr hi⟩

private theorem increasing_Ico_unique (f : ℕ → ℝ) (hf : StrictMono f)
    {i j : ℕ} {x : ℝ} (hi : f i ≤ x ∧ x < f (i + 1))
    (hj : f j ≤ x ∧ x < f (j + 1)) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hle := hf.monotone (show i + 1 ≤ j by omega)
    linarith [hi.2, hj.1]
  · exact h
  · have hle := hf.monotone (show j + 1 ≤ i by omega)
    linarith [hj.2, hi.1]

private theorem increasing_Ioc_unique (f : ℕ → ℝ) (hf : StrictMono f)
    {i j : ℕ} {x : ℝ} (hi : f i < x ∧ x ≤ f (i + 1))
    (hj : f j < x ∧ x ≤ f (j + 1)) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hle := hf.monotone (show i + 1 ≤ j by omega)
    linarith [hi.2, hj.1]
  · exact h
  · have hle := hf.monotone (show j + 1 ≤ i by omega)
    linarith [hj.2, hi.1]

theorem contains_negative_lt_zero (i : Fin A.m) {x : ℝ}
    (hx : A.Contains (false, i) x) : x < 0 := by
  have h := (A.contains_iff_negative i x).mp hx
  have hb := A.endpoint_le_half (show i.val + 1 ≤ A.m from i.isLt)
  linarith [h.2]

theorem contains_positive_nonneg (i : Fin A.m) {x : ℝ}
    (hx : A.Contains (true, i) x) : 0 ≤ x := by
  have h := (A.contains_iff_positive i x).mp hx
  have hb := A.endpoint_le_half (show i.val + 1 ≤ A.m from i.isLt)
  linarith [h.2]

theorem label_unique (i j : A.Label) {x : ℝ}
    (hi : A.Contains i x) (hj : A.Contains j x) : i = j := by
  rcases i with ⟨side, i⟩
  rcases j with ⟨side', j⟩
  cases side <;> cases side'
  · have hij := increasing_Ico_unique A.endpoint A.endpoint_strictMono
      ((A.contains_iff_negative i x).mp hi) ((A.contains_iff_negative j x).mp hj)
    have hf : i = j := Fin.ext hij
    subst j
    rfl
  · linarith [A.contains_negative_lt_zero i hi, A.contains_positive_nonneg j hj]
  · linarith [A.contains_positive_nonneg i hi, A.contains_negative_lt_zero j hj]
  · have hij := increasing_Ioc_unique A.endpoint A.endpoint_strictMono
      ((A.contains_iff_positive i x).mp hi) ((A.contains_iff_positive j x).mp hj)
    have hf : i = j := Fin.ext hij
    subst j
    rfl

noncomputable def meshLabel (x : ℝ) : A.Label :=
  Classical.choose (A.exists_label (centered_mem x).1 (centered_mem x).2)

theorem meshLabel_contains (x : ℝ) : A.Contains (A.meshLabel x) (centered x) :=
  Classical.choose_spec (A.exists_label (centered_mem x).1 (centered_mem x).2)

theorem meshLabel_eq_iff (x : ℝ) (i : A.Label) :
    A.meshLabel x = i ↔ A.Contains i (centered x) := by
  constructor
  · intro h
    rw [← h]
    exact A.meshLabel_contains x
  · intro h
    exact A.label_unique _ _ (A.meshLabel_contains x) h

theorem meshLabel_add_int (x : ℝ) (z : ℤ) : A.meshLabel (x + z) = A.meshLabel x := by
  apply (A.meshLabel_eq_iff _ _).mpr
  rw [centered_add_int]
  exact A.meshLabel_contains x

theorem same_label_distance {x y : ℝ} (h : A.meshLabel x = A.meshLabel y) :
    |centered x - centered y| ≤ A.width (A.meshLabel x) := by
  have hx := A.meshLabel_contains x
  have hy := A.meshLabel_contains y
  rw [← h] at hy
  unfold Contains at hx hy
  unfold width
  apply abs_le.mpr
  constructor <;> linarith

theorem closed_radial_mem (i : A.Label) {x : ℝ}
    (hl : A.left i ≤ x) (hu : x ≤ A.right i) :
    A.endpoint i.2.val ≤ rho x ∧ rho x ≤ A.endpoint (i.2.val + 1) := by
  have hxmin : -(1 / 2 : ℝ) ≤ x := (A.left_ge_neg_half i).trans hl
  have hxmax : x ≤ 1 / 2 := hu.trans (A.right_le_half i)
  rw [rho_eq_of_closed_mem hxmin hxmax]
  rcases i with ⟨side, i⟩
  have hb := A.endpoint_le_half (show i.val + 1 ≤ A.m from i.isLt)
  cases side
  · dsimp [left, right] at hl hu
    have hx : x ≤ 0 := by linarith
    rw [abs_of_nonpos hx]
    constructor <;> linarith
  · dsimp [left, right] at hl hu
    have hx : 0 ≤ x := by linarith
    rw [abs_of_nonneg hx]
    constructor <;> linarith

theorem width_bounds_of_closed_mem (i : A.Label) {x : ℝ}
    (hl : A.left i ≤ x) (hu : x ≤ A.right i) :
    A.H / 4 * (rho x + A.alpha) ≤ A.width i ∧
      A.width i ≤ 2 * A.H * (rho x + A.alpha) := by
  have hx := A.closed_radial_mem i hl hu
  rw [A.width_eq_radialWidth]
  exact A.radial_width_bounds i.2.val (rho x) hx.1 hx.2

theorem width_le_two_H (i : A.Label) : A.width i ≤ 2 * A.H := by
  have hw := A.width_bounds_of_closed_mem i (le_refl _)
    (le_of_lt (sub_pos.mp (A.width_pos i)))
  have hr := rho_le_half (A.left i)
  have hH := A.H_pos
  have ha := A.alpha_le
  have hp := mul_nonneg (by positivity : 0 ≤ 2 * A.H)
    (by linarith : 0 ≤ 1 - (rho (A.left i) + A.alpha))
  nlinarith [hw.2]

/-- Integer congruence is kept explicit. A displacement of at most twice
the anchor width covers every point in its closed circle neighborhood. -/
theorem neighbor_width (i j : A.Label) {x y : ℝ}
    (hxl : A.left i ≤ x) (hxu : x ≤ A.right i)
    (hyl : A.left j ≤ y) (hyu : y ≤ A.right j)
    (hnear : ∃ z : ℤ, |y - x - z| ≤ 2 * A.width i) :
    A.width i / 16 ≤ A.width j := by
  obtain ⟨z, hz⟩ := hnear
  have hr := (rho_lipschitz_integer y x z).trans hz
  have hr' := (abs_le.mp hr).1
  have hi := A.width_bounds_of_closed_mem i hxl hxu
  have hj := A.width_bounds_of_closed_mem j hyl hyu
  have hH := A.H_pos
  have hHa := A.H_le
  have hrad : 0 ≤ rho x + A.alpha := by linarith [rho_nonneg x, A.alpha_pos]
  have hmult := mul_nonneg (by linarith : 0 ≤ 1 / 8 - A.H) hrad
  have hrhalf : (rho x + A.alpha) / 2 ≤ rho y + A.alpha := by
    nlinarith [hi.2]
  have hscaled := mul_le_mul_of_nonneg_left hrhalf (by positivity : 0 ≤ A.H / 4)
  nlinarith [hj.1, hi.2]

end AdaptiveMesh
end QuantitativeVanDerWaerden

namespace QuantitativeVanDerWaerden.AdaptiveMesh

variable (A : AdaptiveMesh)

@[simp] theorem card_label : Fintype.card A.Label = 2 * A.m := by
  simp [Label, Fintype.card_prod]

theorem twice_m_le : (2 : ℝ) * A.m ≤ 2 * (A.R / A.H) + 2 := by
  have h := Nat.ceil_lt_add_one (le_of_lt (div_pos A.R_pos A.H_pos))
  change (A.m : ℝ) < A.R / A.H + 1 at h
  linarith

theorem twice_m_le_of_H {k : ℕ} (_hk : 0 < k) (hH : A.H = 1 / (k : ℝ)^2) :
    (2 : ℝ) * A.m ≤ 2 * (k : ℝ)^2 * A.R + 2 := by
  have h := A.twice_m_le
  rw [hH] at h
  simpa only [div_div_eq_mul_div, div_one, mul_comm A.R ((k : ℝ)^2),
    ← mul_assoc] using h

end QuantitativeVanDerWaerden.AdaptiveMesh

end OAI
end
end

section
section
namespace OAI

noncomputable section


namespace QuantitativeVanDerWaerden

open scoped BigOperators

/-- Squared-separated points on an affine line in one half-open norm band. -/
theorem affine_norm_band_card_le_two {ι : Type uIndex} {D : ℕ} (s : Finset ι)
    (t : ι → ℝ) (A B : Vec D) (m : ℝ)
    (hsep : (s : Set ι).Pairwise fun i j =>
      1 ≤ distSq (fun d => A d + t i * B d) (fun d => A d + t j * B d))
    (hband : ∀ i ∈ s,
      m ≤ normSq (fun d => A d + t i * B d) ∧
      normSq (fun d => A d + t i * B d) < m + 1) :
    s.card ≤ 2 := by
  classical
  by_cases hB : normSq B = 0
  · have hcard : s.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      by_contra hij
      have h : 1 ≤ distSq (fun d => A d + t i * B d)
          (fun d => A d + t j * B d) := hsep hi hj hij
      rw [distSq_affine A B (t i) (t j), hB, zero_mul] at h
      norm_num at h
    exact hcard.trans (by decide)
  · apply weighted_scalar_band_card_le_two s
      (fun i => t i + (∑ d, A d * B d) / normSq B) (normSq B)
      (normSq A - (∑ d, A d * B d) ^ 2 / normSq B) m (normSq_nonneg B)
    · intro i hi j hj hij
      simpa only [distSq_affine, add_sub_add_right_eq_sub] using hsep hi hj hij
    · intro i hi
      simpa only [normSq_affine_complete_square A B (t i) hB] using hband i hi

theorem affine_norm_band_card_le_four {ι : Type uIndex} {D : ℕ} (s : Finset ι)
    (t : ι → ℝ) (A B : Vec D) (m : ℝ)
    (hsep : (s : Set ι).Pairwise fun i j =>
      1 ≤ distSq (fun d => A d + t i * B d) (fun d => A d + t j * B d))
    (hband : ∀ i ∈ s,
      m ≤ normSq (fun d => A d + t i * B d) ∧
      normSq (fun d => A d + t i * B d) < m + 1) :
    s.card ≤ 4 :=
  (affine_norm_band_card_le_two s t A B m hsep hband).trans (by decide)

/-- The literal box label and integer squared-norm band. -/
def geometricKey {X : Type uX} {Box : Type uBox} {D : ℕ}
    (box : X → Box) (point : X → Vec D) (x : X) : Box × ℤ :=
  (box x, ⌊normSq (point x)⌋)

theorem geometricKey_band {X : Type uX} {Box : Type uBox} {D : ℕ}
    (box : X → Box) (point : X → Vec D) {x : X} {key : Box × ℤ}
    (hkey : geometricKey box point x = key) :
    (key.2 : ℝ) ≤ normSq (point x) ∧ normSq (point x) < (key.2 : ℝ) + 1 := by
  have hf : ⌊normSq (point x)⌋ = key.2 := congrArg Prod.snd hkey
  constructor
  · simpa only [hf] using Int.floor_le (normSq (point x))
  · simpa only [hf] using Int.lt_floor_add_one (normSq (point x))

/-- No consecutive-index assumption is made on the selected key occurrences. -/
theorem same_geometricKey_card_le_four {ι : Type uIndex} {Box : Type uBox} {D : ℕ}
    (s : Finset ι) (t : ι → ℝ) (box : ι → Box) (point : ι → Vec D)
    (key : Box × ℤ) (hkey : ∀ i ∈ s, geometricKey box point i = key)
    (hsep : (s : Set ι).Pairwise fun i j => 1 ≤ distSq (point i) (point j))
    (A B : Vec D) (haffine : ∀ i ∈ s, point i = fun d => A d + t i * B d) :
    s.card ≤ 4 := by
  apply affine_norm_band_card_le_four s t A B (key.2 : ℝ)
  · intro i hi j hj hij
    rw [← haffine i hi, ← haffine j hj]
    exact hsep hi hj hij
  · intro i hi
    have hb := geometricKey_band box point (hkey i hi)
    rwa [haffine i hi] at hb

/-- The actual scale used by the second representative system. -/
def scaledYRep (q D dilation : ℕ) (n : CyclicGroup q D) : Vec D :=
  fun i => (q : ℝ) * yRep q D dilation n i

def yGeometricKey {Box : Type uBox} (q D dilation : ℕ)
    (box : CyclicGroup q D → Box) (n : CyclicGroup q D) : Box × ℤ :=
  geometricKey box (scaledYRep q D dilation) n

theorem yGeometricKey_fiber_card_le_four {Box : Type uBox} [DecidableEq Box]
    {q D dilation k : ℕ} {H : ℝ} (hq : 0 < q)
    (hunit : Nat.Coprime dilation (q ^ D))
    (box : CyclicGroup q D → Box)
    (hbox : ∀ n n', box n = box n' → ∀ i,
      |yRep q D dilation n i - yRep q D dilation n' i| ≤ 2 * H)
    (hH : 0 ≤ H) (hsmall : 2 * (k : ℝ) * H < 1)
    (a d : CyclicGroup q D)
    (hinj : Function.Injective (fun j : Fin k => a + (j.val : CyclicGroup q D) * d))
    (key : Box × ℤ) :
    ((Finset.range k).filter fun j : ℕ =>
      yGeometricKey q D dilation box (a + (j : CyclicGroup q D) * d) = key).card ≤ 4 := by
  classical
  let J := (Finset.range k).filter fun j : ℕ =>
    yGeometricKey q D dilation box (a + (j : CyclicGroup q D) * d) = key
  let z : ℕ → Vec D := fun j => yRep q D dilation (a + (j : CyclicGroup q D) * d)
  have hJ : ∀ j ∈ J, j < k := fun j hj =>
    Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hkey : ∀ j ∈ J,
      yGeometricKey q D dilation box (a + (j : CyclicGroup q D) * d) = key :=
    fun j hj => (Finset.mem_filter.mp hj).2
  have hb : ∀ i ∈ J, ∀ j ∈ J, ∀ c, |z j c - z i c| ≤ 2 * H := by
    intro i hi j hj c
    have hi' : box (a + (i : CyclicGroup q D) * d) = key.1 :=
      congrArg Prod.fst (hkey i hi)
    have hj' : box (a + (j : CyclicGroup q D) * d) = key.1 :=
      congrArg Prod.fst (hkey j hj)
    exact hbox _ _ (hj'.trans hi'.symm) c
  have hint : ∀ i ∈ J, ∀ j ∈ J, ∀ l ∈ J, i < j → j < l → ∀ c,
      ∃ m : ℤ, ((l : ℝ) - j) * (z j c - z i c) -
        ((j : ℝ) - i) * (z l c - z j c) = (m : ℝ) := by
    intro i hi j hj l hl hij hjl c
    apply triple_integral_of_integer_errors
      (A := yRep q D dilation a c) (B := yRep q D dilation d c)
    intro n
    simpa only [z, nsmul_eq_mul] using yRep_ap_congr hq dilation a d n c
  obtain ⟨A, B, hAB⟩ := exists_affine_of_small_box_vector J z hJ hH hsmall hb hint
  have hsep : (J : Set ℕ).Pairwise fun i j =>
      1 ≤ distSq (scaledYRep q D dilation (a + (i : CyclicGroup q D) * d))
        (scaledYRep q D dilation (a + (j : CyclicGroup q D) * d)) := by
    intro i hi j hj hij
    have hne : a + (i : CyclicGroup q D) * d ≠ a + (j : CyclicGroup q D) * d := by
      intro heq
      have hfin : (⟨i, hJ i hi⟩ : Fin k) = ⟨j, hJ j hj⟩ := hinj heq
      exact hij (congrArg Fin.val hfin)
    exact yRep_squared_separation hq hunit hne
  change J.card ≤ 4
  apply same_geometricKey_card_le_four J (fun j => (j : ℝ))
    (fun j => box (a + (j : CyclicGroup q D) * d))
    (fun j => scaledYRep q D dilation (a + (j : CyclicGroup q D) * d)) key
    hkey hsep (fun c => (q : ℝ) * A c) (fun c => (q : ℝ) * B c)
  intro j hj
  funext c
  change (q : ℝ) * z j c = (q : ℝ) * A c + (j : ℝ) * ((q : ℝ) * B c)
  rw [hAB j hj c]
  ring

/-- The actual coordinatewise second-system box label. -/
def secondBox (mesh : AdaptiveMesh) (q D dilation : ℕ)
    (n : CyclicGroup q D) : Fin D → mesh.Label :=
  fun i => mesh.meshLabel (yRep q D dilation n i)

def perturbationKey (mesh : AdaptiveMesh) (q D dilation : ℕ)
    (n : CyclicGroup q D) : (Fin D → mesh.Label) × ℤ :=
  yGeometricKey q D dilation (secondBox mesh q D dilation) n

theorem secondBox_same_distance (mesh : AdaptiveMesh) (q D dilation : ℕ)
    {a b : CyclicGroup q D} (h : secondBox mesh q D dilation a =
      secondBox mesh q D dilation b) (i : Fin D) :
    |yRep q D dilation a i - yRep q D dilation b i| ≤ 2 * mesh.H := by
  have hi : mesh.meshLabel (yRep q D dilation a i) =
      mesh.meshLabel (yRep q D dilation b i) := congrFun h i
  have ha := yRep_mem q D dilation a i
  have hb := yRep_mem q D dilation b i
  have hd := (mesh.same_label_distance hi).trans (mesh.width_le_two_H _)
  simpa only [centered_eq_of_mem ha.1 ha.2, centered_eq_of_mem hb.1 hb.2] using hd

/-- Every literal geometric key occurs at most four times on an actual
nonconstant cyclic progression. The prime-power hypothesis supplies distinct
terms, the mesh supplies the width bound, and coprime dilation supplies
squared separation; no affinity or key-multiplicity conclusion is assumed. -/
theorem perturbationKey_fiber_card_le_four (mesh : AdaptiveMesh)
    {P e D dilation k : ℕ} (hP : P.Prime) (hk : k ≤ P)
    (hunit : Nat.Coprime dilation ((P ^ e) ^ D))
    (hsmall : 2 * (k : ℝ) * mesh.H < 1)
    (a d : CyclicGroup (P ^ e) D) (hd : d ≠ 0)
    (key : (Fin D → mesh.Label) × ℤ) :
    ((Finset.range k).filter fun j : ℕ =>
      perturbationKey mesh (P ^ e) D dilation
        (a + (j : CyclicGroup (P ^ e) D) * d) = key).card ≤ 4 := by
  apply yGeometricKey_fiber_card_le_four (pow_pos hP.pos e) hunit
    (secondBox mesh (P ^ e) D dilation) ?_ mesh.H_pos.le hsmall a d
    (prime_power_ap_injective_pow hP hk a d hd) key
  intro n n' h i
  exact secondBox_same_distance mesh (P ^ e) D dilation h i

/-- The same literal-key bound on the finite index type used by the
Bernoulli perturbation. This is only the bijection between `Fin k` and
`range k`; the geometric argument is reused unchanged. -/
theorem perturbationKey_fin_fiber_card_le_four (mesh : AdaptiveMesh)
    {P e D dilation k : ℕ} (hP : P.Prime) (hk : k ≤ P)
    (hunit : Nat.Coprime dilation ((P ^ e) ^ D))
    (hsmall : 2 * (k : ℝ) * mesh.H < 1)
    (a d : CyclicGroup (P ^ e) D) (hd : d ≠ 0)
    (key : (Fin D → mesh.Label) × ℤ) :
    (Finset.univ.filter fun j : Fin k =>
      perturbationKey mesh (P ^ e) D dilation
        (a + (j.val : CyclicGroup (P ^ e) D) * d) = key).card ≤ 4 := by
  classical
  have hcard :
      (Finset.univ.filter fun j : Fin k =>
        perturbationKey mesh (P ^ e) D dilation
          (a + (j.val : CyclicGroup (P ^ e) D) * d) = key).card =
      ((Finset.range k).filter fun j : ℕ =>
        perturbationKey mesh (P ^ e) D dilation
          (a + (j : CyclicGroup (P ^ e) D) * d) = key).card := by
    refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr j.isLt, (Finset.mem_filter.mp hj).2⟩
    · intro i hi j hj hij
      exact Fin.ext hij
    · intro j hj
      refine ⟨⟨j, Finset.mem_range.mp (Finset.mem_filter.mp hj).1⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  rw [hcard]
  exact perturbationKey_fiber_card_le_four mesh hP hk hunit hsmall a d hd key

end QuantitativeVanDerWaerden

end

end OAI
end
end

section
section
namespace OAI

noncomputable section


namespace QuantitativeVanDerWaerden
namespace CyclicColoring

open SparsePerturbation

variable {X : Type uX} {Ambient : Type uAmbient}

def finiteImageKey (key : X → Ambient) (x : X) : Set.range key :=
  ⟨key x, x, rfl⟩

@[simp] theorem finiteImageKey_val (key : X → Ambient) (x : X) :
    (finiteImageKey key x).val = key x := rfl

@[simp] theorem finiteImageKey_eq_iff (key : X → Ambient) (x : X)
    (a : Set.range key) : finiteImageKey key x = a ↔ key x = a.val :=
  Subtype.ext_iff

/-- Coercion keeps literal key identities and is injective on signature words. -/
def ambientSignature {k : ℕ} (key : X → Ambient)
    (σ : Signature (Set.range key) k) : Signature Ambient k :=
  fun j => ((σ j).1, (σ j).2.val)

theorem ambientSignature_injective {k : ℕ} (key : X → Ambient) :
    Function.Injective (ambientSignature (k := k) key) := by
  intro σ τ h
  funext j
  have hj := congrFun h j
  apply Prod.ext
  · exact congrArg (fun z : Bool × Ambient => z.1) hj
  · apply Subtype.ext
    exact congrArg (fun z : Bool × Ambient => z.2) hj

/-- Passing to the finite image does not rename or merge geometric signatures. -/
theorem cyclic_signature_image_card {N k : ℕ} [NeZero N] [DecidableEq Ambient]
    (c₀ : ZMod N → Bool) (key : ZMod N → Ambient)
    (A : Finset (ZMod N × ZMod N)) :
    (A.image (cyclicSignature (k := k) c₀ (finiteImageKey key))).card =
      (A.image (cyclicSignature (k := k) c₀ key)).card := by
  classical
  calc
    _ = ((A.image (cyclicSignature (k := k) c₀ (finiteImageKey key))).image
        (ambientSignature key)).card :=
      (Finset.card_image_of_injective _ (ambientSignature_injective key)).symm
    _ = (A.image (cyclicSignature (k := k) c₀ key)).card := by
      rw [Finset.image_image]
      rfl

/-- The finite Bernoulli construction also applies to an infinite ambient key
type: only the actual image is used as the probability-space coordinate type. -/
theorem exists_cyclicAvoids_of_ambient_keys {N k : ℕ} [NeZero N]
    [DecidableEq Ambient] (c₀ : ZMod N → Bool) (key : ZMod N → Ambient)
    (A : Finset (ZMod N × ZMod N)) (hA : A ⊆ nonzeroProgressions N)
    {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hmult : ∀ ad ∈ nonzeroProgressions N, ∀ a,
      (Finset.univ.filter (fun j : Fin k => (cyclicSignature (k := k) c₀ key ad j).2 = a)).card ≤ 4)
    (hcases : ∀ ad ∈ nonzeroProgressions N, ad ∈ A ∨ ∀ b,
      k ≤ 100 * (oppositePositions (cyclicSignature (k := k) c₀ key ad) b).card)
    (hbudget : 2 * (N : ℝ) ^ 2 * p ^ ((k + 399) / 400) +
      2 * ((A.image (cyclicSignature (k := k) c₀ key)).card : ℝ) *
        (1 - p) ^ ((k + 3) / 4) < 1) :
    ∃ C : ZMod N → Bool, CyclicAvoids C k := by
  classical
  apply exists_cyclicAvoids_of_sparse_data c₀ (finiteImageKey key) A hA hp hp2
  · intro ad had a
    refine (Nat.le_of_eq (congrArg (Finset.card : Finset (Fin k) → ℕ) ?_)).trans
      (hmult ad had a.val)
    apply Finset.ext
    intro j
    constructor
    · intro hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact (finiteImageKey_eq_iff key _ a).mp (Finset.mem_filter.mp hj).2
    · intro hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact (finiteImageKey_eq_iff key _ a).mpr (Finset.mem_filter.mp hj).2
  · intro ad had
    rcases hcases ad had with hmem | hbound
    · exact Or.inl hmem
    · refine Or.inr ?_
      intro b
      refine (hbound b).trans (Nat.mul_le_mul_left 100
        (Nat.le_of_eq (congrArg (Finset.card : Finset (Fin k) → ℕ) ?_)))
      apply Finset.ext
      intro j
      constructor
      · intro hj
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
      · intro hj
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  · simpa only [cyclic_signature_image_card] using hbudget

theorem exists_cyclicAvoids_of_geometric_data (mesh : AdaptiveMesh)
    {P e D dilation k : ℕ} [NeZero ((P ^ e) ^ D)] (hP : P.Prime) (hk : k ≤ P)
    (hunit : Nat.Coprime dilation ((P ^ e) ^ D))
    (hsmall : 2 * (k : ℝ) * mesh.H < 1)
    (c₀ : CyclicGroup (P ^ e) D → Bool)
    (A : Finset (CyclicGroup (P ^ e) D × CyclicGroup (P ^ e) D))
    (hA : A ⊆ nonzeroProgressions ((P ^ e) ^ D))
    {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hcases : ∀ ad ∈ nonzeroProgressions ((P ^ e) ^ D), ad ∈ A ∨ ∀ b,
      k ≤ 100 * (oppositePositions
        (cyclicSignature (k := k) c₀ (perturbationKey mesh (P ^ e) D dilation) ad) b).card)
    (hbudget : 2 * (((P ^ e) ^ D : ℕ) : ℝ) ^ 2 * p ^ ((k + 399) / 400) +
      2 * ((A.image (cyclicSignature (k := k) c₀
        (perturbationKey mesh (P ^ e) D dilation))).card : ℝ) *
        (1 - p) ^ ((k + 3) / 4) < 1) :
    ∃ C : CyclicGroup (P ^ e) D → Bool, CyclicAvoids C k := by
  classical
  apply exists_cyclicAvoids_of_ambient_keys c₀
    (perturbationKey mesh (P ^ e) D dilation) A hA hp hp2 ?_ hcases hbudget
  intro ad had a
  exact perturbationKey_fin_fiber_card_le_four mesh hP hk hunit hsmall ad.1 ad.2
    ((mem_nonzeroProgressions ad).mp had) a

end CyclicColoring
end QuantitativeVanDerWaerden

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace QuantitativeVanDerWaerden.Parameters

def c : ℝ := 1 / 100000
def dimension (k : ℕ) : ℕ := ⌈(k : ℝ) ^ (1 / 10 : ℝ)⌉₊
def cutoff (k : ℕ) : ℕ := ⌈(k : ℝ) ^ (1 / 2 : ℝ)⌉₊
def flipProbability (k : ℕ) : ℝ := (k : ℝ) ^ (-1 / 20 : ℝ)
def meshScale (k : ℕ) : ℝ := 1 / (k : ℝ) ^ 2
def cutScale (k : ℕ) : ℝ := 1 / (1000 * (dimension k : ℝ))

theorem c_pos : 0 < c := by norm_num [c]

theorem rich_coefficient :
    2 * c - (1 / 100 : ℝ) / 80 = -(21 / 200000 : ℝ) := by
  norm_num [c]

theorem dimension_lower (k : ℕ) :
    (k : ℝ) ^ (1 / 10 : ℝ) ≤ (dimension k : ℝ) := Nat.le_ceil _

theorem cutoff_lower (k : ℕ) :
    (k : ℝ) ^ (1 / 2 : ℝ) ≤ (cutoff k : ℝ) := Nat.le_ceil _

theorem dimension_upper {k : ℕ} (hk : 1 ≤ k) :
    (dimension k : ℝ) ≤ 2 * (k : ℝ) ^ (1 / 10 : ℝ) := by
  have hceil : (dimension k : ℝ) < (k : ℝ) ^ (1 / 10 : ℝ) + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have : 1 ≤ (k : ℝ) ^ (1 / 10 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hk) (by norm_num)
  linarith

theorem cutoff_upper {k : ℕ} (hk : 1 ≤ k) :
    (cutoff k : ℝ) ≤ 2 * (k : ℝ) ^ (1 / 2 : ℝ) := by
  have hceil : (cutoff k : ℝ) < (k : ℝ) ^ (1 / 2 : ℝ) + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have : 1 ≤ (k : ℝ) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hk) (by norm_num)
  linarith

theorem dimension_pos {k : ℕ} (hk : 1 ≤ k) : 0 < dimension k := by
  have h : 1 ≤ (k : ℝ) ^ (1 / 10 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hk) (by norm_num)
  have := dimension_lower k
  exact_mod_cast (show (0 : ℝ) < dimension k by linarith)

theorem cutoff_pos {k : ℕ} (hk : 1 ≤ k) : 0 < cutoff k := by
  have h : 1 ≤ (k : ℝ) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hk) (by norm_num)
  have := cutoff_lower k
  exact_mod_cast (show (0 : ℝ) < cutoff k by linarith)

theorem dimension_sq_lower (k : ℕ) :
    (k : ℝ) ^ (1 / 5 : ℝ) ≤ (dimension k : ℝ) ^ 2 := by
  have hp := Real.rpow_nonneg (Nat.cast_nonneg k) (1 / 10 : ℝ)
  have hh := dimension_lower k
  have he : ((k : ℝ) ^ (1 / 10 : ℝ)) ^ 2 = (k : ℝ) ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg k)]
    norm_num
  nlinarith

theorem dimension_sq_upper {k : ℕ} (hk : 1 ≤ k) :
    (dimension k : ℝ) ^ 2 ≤ 4 * (k : ℝ) ^ (1 / 5 : ℝ) := by
  have hp := Real.rpow_nonneg (Nat.cast_nonneg k) (1 / 10 : ℝ)
  have hh := dimension_upper hk
  have he : ((k : ℝ) ^ (1 / 10 : ℝ)) ^ 2 = (k : ℝ) ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg k)]
    norm_num
  have hd : (0 : ℝ) ≤ dimension k := Nat.cast_nonneg _
  nlinarith

theorem dimension_cutoff_upper {k : ℕ} (hk : 1 ≤ k) :
    (dimension k : ℝ) * cutoff k ≤ 4 * (k : ℝ) ^ (3 / 5 : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    (dimension k : ℝ) * cutoff k ≤
        (2 * (k : ℝ) ^ (1 / 10 : ℝ)) * (2 * (k : ℝ) ^ (1 / 2 : ℝ)) :=
      mul_le_mul (dimension_upper hk) (cutoff_upper hk)
        (Nat.cast_nonneg _) (by positivity)
    _ = 4 * ((k : ℝ) ^ (1 / 10 : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ)) := by ring
    _ = 4 * (k : ℝ) ^ (3 / 5 : ℝ) := by
      rw [← Real.rpow_add hk0]
      norm_num

theorem flipProbability_pos {k : ℕ} (hk : 0 < k) : 0 < flipProbability k :=
  Real.rpow_pos_of_pos (by exact_mod_cast hk) _

theorem flip_mass {k : ℕ} (hk : 0 < k) :
    flipProbability k * k = (k : ℝ) ^ (19 / 20 : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  change (k : ℝ) ^ (-1 / 20 : ℝ) * k = _
  nth_rw 2 [← Real.rpow_one (k : ℝ)]
  rw [← Real.rpow_add hk0]
  norm_num

theorem meshScale_pos {k : ℕ} (hk : 0 < k) : 0 < meshScale k := by
  unfold meshScale
  positivity

theorem cutScale_pos {k : ℕ} (hk : 1 ≤ k) : 0 < cutScale k := by
  have := dimension_pos hk
  unfold cutScale
  positivity

end QuantitativeVanDerWaerden.Parameters

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace QuantitativeVanDerWaerden.Parameters

/-- A positive power of an integer base lies within one base factor of any
real target at least one. -/
theorem exists_power_near {P : ℕ} (hP : 2 ≤ P) {x : ℝ} (hx : 1 ≤ x) :
    ∃ n : ℕ, 0 < n ∧ x ≤ ((P ^ n : ℕ) : ℝ) ∧
      ((P ^ n : ℕ) : ℝ) ≤ (P : ℝ) * x := by
  have hP1 : (1 : ℝ) < P := by exact_mod_cast hP
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hx hP1
  refine ⟨n + 1, Nat.succ_pos _, ?_, ?_⟩
  · simpa only [Nat.cast_pow] using hn'.le
  · calc
      ((P ^ (n + 1) : ℕ) : ℝ) = (P : ℝ) ^ n * P := by
        rw [Nat.cast_pow, pow_succ]
      _ ≤ x * (P : ℝ) := mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg P)
      _ = (P : ℝ) * x := mul_comm _ _

/-- The elementary prime bound used in the cyclic construction. -/
theorem exists_prime_above {k : ℕ} (hk : 2 ≤ k) :
    ∃ P : ℕ, P.Prime ∧ k < P ∧ P ≤ 2 * k ^ 2 := by
  obtain ⟨P, hP, hkP, hPk⟩ :=
    Nat.exists_prime_lt_and_le_two_mul k (by omega)
  refine ⟨P, hP, hkP, hPk.trans ?_⟩
  nlinarith

/-- The complete arithmetic choice of prime and prime-power base. -/
structure PrimeScale (k D : ℕ) where
  P : ℕ
  exponent : ℕ
  q : ℕ
  prime : P.Prime
  prime_lower : k < P
  prime_upper : P ≤ 2 * k ^ 2
  exponent_pos : 0 < exponent
  q_eq_pow : q = P ^ exponent
  q_lower : (k : ℝ) ^ (c * k / D) ≤ (q : ℝ)
  q_upper : (q : ℝ) ≤ 2 * (k : ℝ) ^ 2 * (k : ℝ) ^ (c * k / D)

theorem exists_primeScale {k D : ℕ} (hk : 2 ≤ k) (hD : 1 ≤ D) :
    Nonempty (PrimeScale k D) := by
  obtain ⟨P, hP, hkP, hPk⟩ := exists_prime_above hk
  have hc := c_pos
  have hx : 1 ≤ (k : ℝ) ^ (c * k / D) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ k by omega)) (by positivity)
  obtain ⟨n, hn, hlow, hupp⟩ := exists_power_near hP.two_le hx
  refine ⟨{
    P := P
    exponent := n
    q := P ^ n
    prime := hP
    prime_lower := hkP
    prime_upper := hPk
    exponent_pos := hn
    q_eq_pow := rfl
    q_lower := hlow
    q_upper := hupp.trans ?_
  }⟩
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast hPk
  · exact Real.rpow_nonneg (Nat.cast_nonneg k) _

namespace PrimeScale

variable {k D : ℕ} (s : PrimeScale k D)

theorem isPrimePow : IsPrimePow s.q := by
  rw [s.q_eq_pow]
  exact s.prime.isPrimePow.pow (Nat.ne_of_gt s.exponent_pos)

theorem two_le : 2 ≤ s.q := s.isPrimePow.two_le

theorem pos : 0 < s.q := s.isPrimePow.pos

theorem log_lower (hk : 2 ≤ k) (hD : 1 ≤ D) :
    c * k * Real.log k ≤ (D : ℝ) * Real.log s.q := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hk0 _) s.q_lower
  rw [Real.log_rpow hk0] at hl
  have h := mul_le_mul_of_nonneg_left hl hD0.le
  calc
    c * k * Real.log k = (D : ℝ) * ((c * k / D) * Real.log k) := by
      field_simp [hD0.ne']
    _ ≤ (D : ℝ) * Real.log s.q := h

theorem log_upper (hk : 2 ≤ k) (hD : 1 ≤ D) :
    (D : ℝ) * Real.log s.q ≤
      c * k * Real.log k + (D : ℝ) * Real.log (2 * (k : ℝ) ^ 2) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hq0 : (0 : ℝ) < s.q := by exact_mod_cast s.pos
  have ht0 := Real.rpow_pos_of_pos hk0 (c * k / D)
  have hf0 : (0 : ℝ) < 2 * (k : ℝ) ^ 2 := by positivity
  have hl := Real.log_le_log hq0 s.q_upper
  rw [Real.log_mul hf0.ne' ht0.ne', Real.log_rpow hk0] at hl
  calc
    (D : ℝ) * Real.log s.q ≤
        (D : ℝ) * (Real.log (2 * (k : ℝ) ^ 2) + (c * k / D) * Real.log k) :=
      mul_le_mul_of_nonneg_left hl hD0.le
    _ = c * k * Real.log k + (D : ℝ) * Real.log (2 * (k : ℝ) ^ 2) := by
      field_simp [hD0.ne']
      ring

/-- The cardinality of the cyclic group has the required superexponential scale. -/
theorem cardinal_lower (hk : 2 ≤ k) (hD : 1 ≤ D) :
    (k : ℝ) ^ (c * k) ≤ ((s.q ^ D : ℕ) : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have he : (c * (k : ℝ) / D) * D = c * k :=
    div_mul_cancel₀ _ hD0.ne'
  calc
    (k : ℝ) ^ (c * k) = ((k : ℝ) ^ (c * k / D)) ^ D := by
      rw [← Real.rpow_mul_natCast hk0.le, he]
    _ ≤ (s.q : ℝ) ^ D :=
      pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg k) _) s.q_lower D
    _ = ((s.q ^ D : ℕ) : ℝ) := by rw [Nat.cast_pow]

end PrimeScale

end QuantitativeVanDerWaerden.Parameters

end

end OAI
end
end

section
section
namespace OAI

namespace QuantitativeVanDerWaerden

open scoped BigOperators

/-- The primes up to the short-period cutoff. -/
def dilationPrimes (h₀ : ℕ) : Finset ℕ :=
  (Finset.Icc 1 h₀).filter Nat.Prime

@[simp] theorem mem_dilationPrimes {p h₀ : ℕ} :
    p ∈ dilationPrimes h₀ ↔ Nat.Prime p ∧ p ≤ h₀ := by
  simp only [dilationPrimes, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.one_lt.le, h.2⟩, h.1⟩⟩

def dilation (h₀ M : ℕ) : ℕ :=
  ∏ p ∈ dilationPrimes h₀, p ^ Nat.log p (2 * M)

theorem dilation_pos (h₀ M : ℕ) : 0 < dilation h₀ M := by
  apply Nat.pos_of_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (mem_dilationPrimes.mp hp).1.ne_zero

theorem dilation_ne_zero (h₀ M : ℕ) : dilation h₀ M ≠ 0 :=
  (dilation_pos h₀ M).ne'

theorem prime_pow_dvd_dilation {h₀ M p a h : ℕ}
    (hp : p.Prime) (hp₀ : p ≤ h₀) (hh : 0 < h)
    (hmax : h ≤ 2 * M) (hpow : p ^ a ∣ h) :
    p ^ a ∣ dilation h₀ M := by
  have ha : a ≤ Nat.log p (2 * M) :=
    Nat.le_log_of_pow_le hp.one_lt ((Nat.le_of_dvd hh hpow).trans hmax)
  exact (pow_dvd_pow p ha).trans
    (Finset.dvd_prod_of_mem (fun p => p ^ Nat.log p (2 * M))
      (mem_dilationPrimes.mpr ⟨hp, hp₀⟩))

theorem primary_part_dvd_dilation {h₀ M p h : ℕ}
    (hp : p.Prime) (hp₀ : p ≤ h₀) (hh : 0 < h)
    (hmax : h ≤ 2 * M) :
    p ^ h.factorization p ∣ dilation h₀ M :=
  prime_pow_dvd_dilation hp hp₀ hh hmax (Nat.ordProj_dvd h p)

/-- Every positive period up to the cutoff is killed by the dilation. -/
theorem short_period_dvd_dilation {h₀ M h : ℕ}
    (hh : 0 < h) (hshort : h ≤ h₀) (hmax : h ≤ 2 * M) :
    h ∣ dilation h₀ M := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd (dilation h₀ M) h).mpr
  intro p a hp hpow
  by_cases ha : a = 0
  · simp [ha]
  have hph : p ∣ h := (dvd_pow_self p ha).trans hpow
  exact prime_pow_dvd_dilation hp ((Nat.le_of_dvd hh hph).trans hshort) hh hmax hpow

/-- The natural-number bound that yields `log λ ≤ h₀ * log (2M)`. -/
theorem dilation_le_pow {h₀ M : ℕ} (hM : 0 < M) :
    dilation h₀ M ≤ (2 * M) ^ h₀ := by
  have hcard : (dilationPrimes h₀).card ≤ h₀ := by
    simpa [dilationPrimes] using
      (Finset.card_filter_le (s := Finset.Icc 1 h₀) (p := Nat.Prime))
  have hfactor : ∀ p ∈ dilationPrimes h₀, p ^ Nat.log p (2 * M) ≤ 2 * M := by
    intro p _
    exact Nat.pow_log_le_self p (by omega)
  exact (Finset.prod_le_pow_card _ _ _ hfactor).trans
    (Nat.pow_le_pow_right (by omega) hcard)

/-- The explicit logarithmic size bound from the dilation lemma. -/
theorem log_dilation_le {h₀ M : ℕ} (hM : 0 < M) :
    Real.log (dilation h₀ M) ≤ (h₀ : ℝ) * Real.log (2 * M) := by
  have hpos : (0 : ℝ) < dilation h₀ M := by
    exact_mod_cast dilation_pos h₀ M
  have hle : (dilation h₀ M : ℝ) ≤ (2 * (M : ℝ)) ^ h₀ := by
    exact_mod_cast dilation_le_pow (h₀ := h₀) hM
  simpa only [Real.log_pow] using Real.log_le_log hpos hle

/-- Large prime powers are relatively prime to the dilation. -/
theorem dilation_coprime_prime_pow {h₀ M P a : ℕ}
    (hP : P.Prime) (hlarge : h₀ < P) :
    Nat.Coprime (dilation h₀ M) (P ^ a) := by
  unfold dilation
  refine Finset.prod_induction _ (fun n => Nat.Coprime n (P ^ a))
    (fun _ _ hm hn => Nat.coprime_mul_iff_left.mpr ⟨hm, hn⟩)
    (Nat.coprime_one_left _) ?_
  intro p hp
  obtain ⟨hpprime, hple⟩ := mem_dilationPrimes.mp hp
  exact Nat.coprime_pow_primes _ _ hpprime hP (by omega)

/-- If a multiplier contains every small primary part of the period, reducing
the resulting fraction removes every small prime from its denominator. -/
theorem prime_dvd_reducedDenominator_gt_of_primary_parts
    {h h₀ L t : ℕ} (hh : 0 < h)
    (hL : ∀ p : ℕ, p.Prime → p ≤ h₀ → p ^ h.factorization p ∣ L)
    {p : ℕ} (hp : p.Prime) (hpd : p ∣ h / Nat.gcd h (L * t)) : h₀ < p := by
  have hgpos : 0 < Nat.gcd h (L * t) := Nat.gcd_pos_of_pos_left _ hh
  have hqpos : 0 < h / Nat.gcd h (L * t) :=
    Nat.div_pos (Nat.le_of_dvd hh (Nat.gcd_dvd_left h (L * t))) hgpos
  by_contra hnot
  have hple : p ≤ h₀ := Nat.le_of_not_gt hnot
  have hpowg : p ^ h.factorization p ∣ Nat.gcd h (L * t) :=
    Nat.dvd_gcd (Nat.ordProj_dvd h p)
      ((hL p hp hple).trans (dvd_mul_right L t))
  have hval : h.factorization p ≤ (Nat.gcd h (L * t)).factorization p :=
    (hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hgpos)).mp hpowg
  have hz : (h / Nat.gcd h (L * t)).factorization p = 0 := by
    rw [Nat.factorization_div (Nat.gcd_dvd_left h (L * t)),
      Finsupp.tsub_apply, Nat.sub_eq_zero_of_le hval]
  have hone : 1 ≤ (h / Nat.gcd h (L * t)).factorization p :=
    (hp.dvd_iff_one_le_factorization (Nat.ne_of_gt hqpos)).mp hpd
  rw [hz] at hone
  exact Nat.not_succ_le_zero 0 hone

theorem reducedDenominator_eq_one_or_gt_of_primary_parts
    {h h₀ L t : ℕ} (hh : 0 < h)
    (hL : ∀ p : ℕ, p.Prime → p ≤ h₀ → p ^ h.factorization p ∣ L) :
    h / Nat.gcd h (L * t) = 1 ∨ h₀ < h / Nat.gcd h (L * t) := by
  by_cases hq1 : h / Nat.gcd h (L * t) = 1
  · exact Or.inl hq1
  · apply Or.inr
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hq1
    have hgpos : 0 < Nat.gcd h (L * t) := Nat.gcd_pos_of_pos_left _ hh
    have hqpos : 0 < h / Nat.gcd h (L * t) :=
      Nat.div_pos (Nat.le_of_dvd hh (Nat.gcd_dvd_left h (L * t))) hgpos
    exact (prime_dvd_reducedDenominator_gt_of_primary_parts hh hL hp hpd).trans_le
      (Nat.le_of_dvd hqpos hpd)

/-- Dilation removes every small prime from a reduced denominator. -/
theorem prime_dvd_dilatedDenominator_gt {h₀ M h p : ℕ} (t : ℤ)
    (hh : 0 < h) (hmax : h ≤ 2 * M) (hp : p.Prime)
    (hpd : p ∣ h / Int.gcd (h : ℤ) ((dilation h₀ M : ℤ) * t)) : h₀ < p := by
  apply prime_dvd_reducedDenominator_gt_of_primary_parts (t := t.natAbs) hh
    (fun p hp hp₀ => primary_part_dvd_dilation hp hp₀ hh hmax) hp
  simpa [Int.gcd_def, Int.natAbs_mul] using hpd

theorem dilatedDenominator_eq_one_or_gt {h₀ M h : ℕ} (t : ℤ)
    (hh : 0 < h) (hmax : h ≤ 2 * M) :
    h / Int.gcd (h : ℤ) ((dilation h₀ M : ℤ) * t) = 1 ∨
      h₀ < h / Int.gcd (h : ℤ) ((dilation h₀ M : ℤ) * t) := by
  simpa [Int.gcd_def, Int.natAbs_mul] using
    (reducedDenominator_eq_one_or_gt_of_primary_parts (t := t.natAbs) hh
      (fun p hp hp₀ => primary_part_dvd_dilation hp hp₀ hh hmax))

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Growth comparisons for the absolute parameter threshold

These comparisons concern only the progression length and fixed real constants.
They contain no color-count parameter and can therefore be combined before the
digit-product transfer to choose one absolute threshold.
-/

noncomputable section

open Filter Topology

namespace QuantitativeVanDerWaerden.Scaling

/-- A fixed power times a logarithm is eventually bounded by any prescribed
positive multiple of a strictly larger power. -/
theorem eventually_rpow_log_le_real {a b C eps : ℝ}
    (hab : a < b) (hC : 0 ≤ C) (he : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a * Real.log x ≤ eps * x ^ b := by
  have hC1 : 0 < C + 1 := by linarith
  have hlog : ∀ᶠ x : ℝ in atTop,
      ‖Real.log x‖ ≤ (eps / (C + 1)) * ‖x ^ (b - a)‖ :=
    (isLittleO_log_rpow_atTop (sub_pos.mpr hab)).bound (div_pos he hC1)
  filter_upwards [hlog, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hxpos : 0 < x := zero_lt_one.trans_le hx1
  have hpow : 0 ≤ x ^ a := Real.rpow_nonneg hxpos.le _
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_of_nonneg hlog0,
    Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _)] at hx
  calc
    C * x ^ a * Real.log x ≤ (C + 1) * x ^ a * Real.log x :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) hpow) hlog0
    _ ≤ (C + 1) * x ^ a * ((eps / (C + 1)) * x ^ (b - a)) :=
      mul_le_mul_of_nonneg_left hx (mul_nonneg hC1.le hpow)
    _ = eps * (x ^ a * x ^ (b - a)) := by
      field_simp [hC1.ne']
    _ = eps * x ^ b := by
      rw [← Real.rpow_add hxpos, show a + (b - a) = b by ring]

/-- Natural-input version of the power-logarithm comparison. -/
theorem eventually_rpow_log_le {a b C eps : ℝ}
    (hab : a < b) (hC : 0 ≤ C) (he : 0 < eps) :
    ∀ᶠ k : ℕ in atTop,
      C * (k : ℝ) ^ a * Real.log k ≤ eps * (k : ℝ) ^ b :=
  (eventually_rpow_log_le_real hab hC he).natCast_atTop

/-- A fixed multiple of a power is eventually smaller than a prescribed
positive multiple of any strictly larger power. -/
theorem eventually_rpow_le_real {a b C eps : ℝ}
    (hab : a < b) (_hC : 0 ≤ C) (he : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a ≤ eps * x ^ b := by
  have hlarge : ∀ᶠ x : ℝ in atTop, C / eps ≤ x ^ (b - a) :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop (C / eps)
  filter_upwards [hlarge, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  calc
    C * x ^ a = (eps * x ^ a) * (C / eps) := by
      field_simp [he.ne']
    _ ≤ (eps * x ^ a) * x ^ (b - a) :=
      mul_le_mul_of_nonneg_left hx (mul_nonneg he.le (Real.rpow_nonneg hxpos.le _))
    _ = eps * (x ^ a * x ^ (b - a)) := by ring
    _ = eps * x ^ b := by
      rw [← Real.rpow_add hxpos, show a + (b - a) = b by ring]

/-- Natural-input version of the power comparison. -/
theorem eventually_rpow_le {a b C eps : ℝ}
    (hab : a < b) (hC : 0 ≤ C) (he : 0 < eps) :
    ∀ᶠ k : ℕ in atTop, C * (k : ℝ) ^ a ≤ eps * (k : ℝ) ^ b :=
  (eventually_rpow_le_real hab hC he).natCast_atTop

/-- Every positive real power of natural numbers tends to infinity. -/
theorem tendsto_nat_rpow_atTop {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k : ℕ => (k : ℝ) ^ t) atTop atTop :=
  (tendsto_rpow_atTop ht).comp tendsto_natCast_atTop_atTop

/-- An arbitrary fixed lower threshold is eventually crossed by a positive
real power of natural numbers. -/
theorem eventually_le_nat_rpow {t : ℝ} (ht : 0 < t) (L : ℝ) :
    ∀ᶠ k : ℕ in atTop, L ≤ (k : ℝ) ^ t :=
  (tendsto_nat_rpow_atTop ht).eventually_ge_atTop L

/-- Negative powers of natural numbers tend to zero. -/
theorem tendsto_nat_rpow_neg_zero {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k : ℕ => (k : ℝ) ^ (-t)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop ht).comp tendsto_natCast_atTop_atTop

/-- A positive power in the negative exponent dominates any lower power
times a logarithm. The hypothesis `0 < t` is needed for decay to zero. -/
theorem tendsto_exp_rpow_log_sub_rpow_real {a t C b : ℝ}
    (hat : a < t) (hC : 0 ≤ C) (hb : 0 < b) (ht : 0 < t) :
    Tendsto (fun x : ℝ => Real.exp (C * x ^ a * Real.log x - b * x ^ t))
      atTop (𝓝 0) := by
  have hbound : ∀ᶠ x : ℝ in atTop,
      C * x ^ a * Real.log x ≤ (b / 2) * x ^ t :=
    eventually_rpow_log_le_real hat hC (by linarith)
  have hneg : Tendsto (fun x : ℝ => (-(b / 2)) * x ^ t) atTop atBot :=
    (tendsto_rpow_atTop ht).const_mul_atTop_of_neg (by linarith)
  apply Real.tendsto_exp_atBot.comp
  apply tendsto_atBot_mono' atTop _ hneg
  filter_upwards [hbound] with x hx
  nlinarith

/-- Natural-input exponential decay, used in both perturbation union bounds. -/
theorem tendsto_exp_rpow_log_sub_rpow {a t C b : ℝ}
    (hat : a < t) (hC : 0 ≤ C) (hb : 0 < b) (ht : 0 < t) :
    Tendsto (fun k : ℕ =>
      Real.exp (C * (k : ℝ) ^ a * Real.log k - b * (k : ℝ) ^ t))
      atTop (𝓝 0) := by
  simpa only [Function.comp_def] using
    (tendsto_exp_rpow_log_sub_rpow_real hat hC hb ht).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop)

/-- An exponential of a negative positive power dominates every polynomial
prefactor, including the finite number of local pattern lengths. -/
theorem tendsto_rpow_mul_exp_neg_rpow {a b t : ℝ}
    (hb : 0 < b) (ht : 0 < t) :
    Tendsto (fun k : ℕ =>
      (k : ℝ) ^ a * Real.exp (-b * (k : ℝ) ^ t)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a / t) b hb).comp
    (tendsto_nat_rpow_atTop ht)
  convert h using 1
  funext k
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul (Nat.cast_nonneg k),
    show t * (a / t) = a by field_simp [ht.ne']]

end QuantitativeVanDerWaerden.Scaling

end

end OAI
end
end

section
section
namespace OAI

/-!
# Absolute thresholds for the construction

The eventual assertions here concern natural progression lengths only.  In
particular, their thresholds are chosen before any number of colors is supplied.
-/

noncomputable section

open Filter Topology

namespace QuantitativeVanDerWaerden.Parameters

/-- A convenient finite list of stronger scale inequalities.  Existence is
proved below from the actual parameter definitions. -/
structure BasicScales (k : ℕ) : Prop where
  length_large : 1000 ≤ k
  dimension_large : (1000 : ℝ) ≤ dimension k
  cutoff_small : (cutoff k : ℝ) ≤ (k : ℝ) / 100
  dimension_cutoff_small : (dimension k : ℝ) * cutoff k ≤ k
  short_period_gap : (dimension k : ℝ) ^ 2 < 2 * cutoff k
  flip_small : flipProbability k < 1 / 2

theorem dimension_tendsto :
    Tendsto (fun k : ℕ => (dimension k : ℝ)) atTop atTop := by
  exact tendsto_atTop_mono dimension_lower
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop)

theorem cutoff_tendsto :
    Tendsto (fun k : ℕ => (cutoff k : ℝ)) atTop atTop := by
  exact tendsto_atTop_mono cutoff_lower
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop)

theorem flipProbability_tendsto : Tendsto flipProbability atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ => (k : ℝ) ^ (-1 / 20 : ℝ)) atTop (𝓝 0)
  simpa only [Function.comp_def, neg_div] using
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop)

theorem eventually_basicScales : ∀ᶠ k : ℕ in atTop, BasicScales k := by
  have hM := Scaling.eventually_rpow_le
    (a := (1 / 2 : ℝ)) (b := 1) (C := 2) (eps := 1 / 100)
    (by norm_num) (by norm_num) (by norm_num)
  have hDM := Scaling.eventually_rpow_le
    (a := (3 / 5 : ℝ)) (b := 1) (C := 4) (eps := 1)
    (by norm_num) (by norm_num) (by norm_num)
  have hD2 := Scaling.eventually_rpow_le
    (a := (1 / 5 : ℝ)) (b := 1 / 2) (C := 4) (eps := 1)
    (by norm_num) (by norm_num) (by norm_num)
  have hD := dimension_tendsto.eventually (eventually_ge_atTop (1000 : ℝ))
  have hp := flipProbability_tendsto.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_ge_atTop 1000, hM, hDM, hD2, hD, hp]
    with k hk hM hDM hD2 hD hp
  have hk1 : 1 ≤ k := by omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  refine ⟨hk, hD, ?_, ?_, ?_, hp⟩
  · have := (cutoff_upper hk1).trans hM
    simpa [Real.rpow_one, div_eq_mul_inv, mul_comm] using this
  · have := (dimension_cutoff_upper hk1).trans hDM
    simpa using this
  · have hu := (dimension_sq_upper hk1).trans hD2
    have hl := cutoff_lower k
    have ht := Real.rpow_pos_of_pos hk0 (1 / 2 : ℝ)
    nlinarith

theorem exists_basicScales_threshold : ∃ K : ℕ, ∀ k ≥ K, BasicScales k :=
  eventually_atTop.1 eventually_basicScales

/-- All elementary small-mesh inequalities used in the geometric dichotomy. -/
structure GeometryScales (k : ℕ) : Prop where
  two_cutoff_le_length : 2 * (cutoff k : ℝ) ≤ k
  affine_box : 2 * k * meshScale k < 1
  return_error : 6 * cutoff k * meshScale k / k < 1
  rational_separation : 4 * cutoff k * meshScale k < 1 / 2
  lattice_separation : 2 * meshScale k + 4 * cutoff k * meshScale k < 1
  mesh_lift : 2 * meshScale k * (k + 1) < 1
  cut_error : 4 * cutoff k * meshScale k / k < cutScale k
  cut_small : 4 * cutScale k < 1
  regular_fraction : (4 / 1000 : ℝ) + 1 / dimension k < 1 / 2
  block_loss : 2 * (cutoff k : ℝ) / k ≤ 1 / 16
  heavy_return : 2 * (cutoff k : ℝ) ≤ (k : ℝ) / 10
  light_row_size : (100 : ℝ) ≤ (cutoff k : ℝ) / 10 - 1
  local_event_size : (100 : ℝ) ≤ (dimension k : ℝ) ^ 2 / 2

theorem geometryScales_of_basic {k : ℕ} (h : BasicScales k)
    (hM : (1010 : ℝ) ≤ cutoff k) : GeometryScales k := by
  have hk : (1000 : ℝ) ≤ k := by exact_mod_cast h.length_large
  have hk0 : (0 : ℝ) < k := by linarith
  have hd : (1000 : ℝ) ≤ dimension k := h.dimension_large
  have hd0 : (0 : ℝ) < dimension k := by linarith
  have hm := h.cutoff_small
  have hdm := h.dimension_cutoff_small
  have hk2 : (1000000 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hk3 : 4000 * (k : ℝ) < (k : ℝ) ^ 3 := by
    have := mul_le_mul_of_nonneg_left hk2 hk0.le
    nlinarith
  constructor
  · linarith
  · unfold meshScale
    field_simp
    nlinarith
  · unfold meshScale
    apply (div_lt_iff₀ hk0).2
    field_simp
    nlinarith
  · unfold meshScale
    field_simp
    nlinarith
  · unfold meshScale
    field_simp
    nlinarith
  · unfold meshScale
    field_simp
    nlinarith
  · unfold meshScale cutScale
    apply (div_lt_div_iff₀ hk0 (by positivity : 0 < 1000 * (dimension k : ℝ))).2
    field_simp
    nlinarith
  · unfold cutScale
    field_simp
    nlinarith
  · have hinv : 1 / (dimension k : ℝ) < 1 / 4 :=
      (div_lt_iff₀ hd0).2 (by linarith)
    linarith
  · apply (div_le_iff₀ hk0).2
    linarith
  · linarith
  · linarith
  · nlinarith

theorem eventually_geometryScales : ∀ᶠ k : ℕ in atTop, GeometryScales k := by
  filter_upwards [eventually_basicScales,
    cutoff_tendsto.eventually (eventually_ge_atTop (1010 : ℝ))] with k hk hM
  exact geometryScales_of_basic hk hM

theorem exists_geometryScales_threshold : ∃ K : ℕ, ∀ k ≥ K, GeometryScales k :=
  eventually_atTop.1 eventually_geometryScales

end QuantitativeVanDerWaerden.Parameters

end

end OAI
end
end

section
section
namespace OAI

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

abbrev Data (k : ℕ) := PrimeScale k (dimension k)

/-- Choose the arithmetic data whose existence is proved by the prime and
prime-power scale construction. No coloring or covering data is assumed. -/
noncomputable def choose (k : ℕ) (hk : 3 ≤ k) : Data k :=
  Classical.choice (exists_primeScale (by omega : 2 ≤ k)
    (show 1 ≤ dimension k from dimension_pos (by omega)))

noncomputable def lambda (k : ℕ) : ℕ := dilation ((dimension k) ^ 2) (cutoff k)

noncomputable def groupSize {k : ℕ} (s : Data k) : ℕ := s.q ^ dimension k

abbrev Group {k : ℕ} (s : Data k) := CyclicGroup s.q (dimension k)

theorem lambda_pos (k : ℕ) : 0 < lambda k := dilation_pos _ _

theorem lambda_ne_zero (k : ℕ) : lambda k ≠ 0 := (lambda_pos k).ne'

theorem groupSize_pos {k : ℕ} (s : Data k) : 0 < groupSize s :=
  pow_pos s.pos _

theorem groupSize_ne_zero {k : ℕ} (s : Data k) : groupSize s ≠ 0 :=
  (groupSize_pos s).ne'

/-- Available as a local instance without requiring typeclass inference
to reconstruct the prime-scale record from a projected modulus. -/
theorem groupSize_neZero {k : ℕ} (s : Data k) : NeZero (groupSize s) :=
  ⟨groupSize_ne_zero s⟩

@[instance_reducible] noncomputable def groupFintype {k : ℕ} (s : Data k) : Fintype (Group s) := by
  letI : NeZero (s.q ^ dimension k) := groupSize_neZero s
  exact inferInstance

theorem group_card {k : ℕ} (s : Data k) [Fintype (Group s)] :
    Fintype.card (Group s) = groupSize s := ZMod.card _

theorem groupSize_two_le {k : ℕ} (s : Data k) (hk : 3 ≤ k) :
    2 ≤ groupSize s := by
  exact s.two_le.trans (le_self_pow₀ (by have := s.two_le; omega)
    (dimension_pos (by omega : 1 ≤ k)).ne')

theorem groupSize_eq_prime_pow {k : ℕ} (s : Data k) :
    groupSize s = s.P ^ (s.exponent * dimension k) := by
  simp only [groupSize, s.q_eq_pow, pow_mul]

theorem groupSize_lower {k : ℕ} (s : Data k) (hk : 3 ≤ k) :
    (k : ℝ) ^ (c * k) ≤ (groupSize s : ℝ) :=
  s.cardinal_lower (by omega) (dimension_pos (by omega))

theorem prime_step {k : ℕ} (s : Data k) : k ≤ s.P := s.prime_lower.le

/-- The stronger basic-scale inequalities place every prime in the
dilation strictly below the prime defining the cyclic group. -/
theorem dimension_sq_lt_length {k : ℕ} (h : BasicScales k) :
    (dimension k) ^ 2 < k := by
  have hreal : (dimension k : ℝ) ^ 2 < (k : ℝ) := by
    have hgap := h.short_period_gap
    have hcut := h.cutoff_small
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  exact_mod_cast hreal

theorem lambda_coprime_of_dimension_sq_lt {k : ℕ} (s : Data k)
    (hD : (dimension k) ^ 2 < k) : Nat.Coprime (lambda k) (groupSize s) := by
  rw [groupSize_eq_prime_pow s]
  exact dilation_coprime_prime_pow s.prime (hD.trans s.prime_lower)

theorem lambda_coprime {k : ℕ} (s : Data k) (h : BasicScales k) :
    Nat.Coprime (lambda k) (groupSize s) :=
  lambda_coprime_of_dimension_sq_lt s (dimension_sq_lt_length h)

theorem affine_box_small {k : ℕ} (hk : 3 ≤ k) :
    2 * (k : ℝ) * meshScale k < 1 := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  unfold meshScale
  rw [mul_one_div]
  apply (div_lt_iff₀ (sq_pos_of_pos hk0)).2
  nlinarith

theorem one_le_log_length {k : ℕ} (hk : 3 ≤ k) :
    1 ≤ Real.log (k : ℝ) := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  apply (Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < k)).2
  exact Real.exp_one_lt_d9.le.trans ((by norm_num : (2.7182818286 : ℝ) ≤ 3).trans hkR)

end QuantitativeVanDerWaerden.ConstructionModel

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace QuantitativeVanDerWaerden.Parameters

theorem scalar_log_prime_slack {k : ℕ} (hk : 2 ≤ k) :
    Real.log (2 * (k : ℝ) ^ 2) ≤ 3 * Real.log k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hl : Real.log 2 ≤ Real.log k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hk)
  rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hk0.ne'), Real.log_pow]
  norm_num
  linarith

theorem scalar_dimension_le_two_mul {k : ℕ} (hk : 1 ≤ k) :
    (dimension k : ℝ) ≤ 2 * k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (k : ℝ) ^ (1 / 10 : ℝ) ≤ k := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hkR (show (1 / 10 : ℝ) ≤ 1 by norm_num)
  have := dimension_upper hk
  linarith

/-- The dimension cancels nine tenths of a power of the progression length. -/
theorem scalar_nat_le_dimension_rpow {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) ≤ dimension k * (k : ℝ) ^ (9 / 10 : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  calc
    (k : ℝ) = (k : ℝ) ^ (1 / 10 : ℝ) * (k : ℝ) ^ (9 / 10 : ℝ) := by
      rw [← Real.rpow_add hk0]
      norm_num
    _ ≤ dimension k * (k : ℝ) ^ (9 / 10 : ℝ) :=
      mul_le_mul_of_nonneg_right (dimension_lower k) (Real.rpow_nonneg hk0.le _)

/-- A bound uniform over every prime power permitted by the construction. -/
theorem scalar_log_q_le {k q : ℕ} (hk : 2 ≤ k)
    (hqlog : (dimension k : ℝ) * Real.log q ≤
      c * k * Real.log k + dimension k * Real.log (2 * (k : ℝ) ^ 2)) :
    Real.log q ≤ 4 * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log k := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hDpos : (0 : ℝ) < dimension k := Nat.cast_pos.mpr (dimension_pos hk1)
  have hL : 0 ≤ Real.log k := Real.log_nonneg hkR
  have hP : 1 ≤ (k : ℝ) ^ (9 / 10 : ℝ) :=
    Real.one_le_rpow hkR (by norm_num)
  have hDP := scalar_nat_le_dimension_rpow hk1
  have hDPlow : (dimension k : ℝ) ≤ dimension k * (k : ℝ) ^ (9 / 10 : ℝ) :=
    le_mul_of_one_le_right hDpos.le hP
  have hc : c ≤ 1 := by norm_num [c]
  have hfirst : c * k * Real.log k ≤
      (dimension k * (k : ℝ) ^ (9 / 10 : ℝ)) * Real.log k := by
    apply mul_le_mul_of_nonneg_right _ hL
    exact (mul_le_of_le_one_left (Nat.cast_nonneg k) hc).trans hDP
  have hsecond : (dimension k : ℝ) * Real.log (2 * (k : ℝ) ^ 2) ≤
      3 * (dimension k * (k : ℝ) ^ (9 / 10 : ℝ)) * Real.log k := by
    calc
      (dimension k : ℝ) * Real.log (2 * (k : ℝ) ^ 2) ≤
          dimension k * (3 * Real.log k) :=
        mul_le_mul_of_nonneg_left (scalar_log_prime_slack hk) hDpos.le
      _ ≤ (dimension k * (k : ℝ) ^ (9 / 10 : ℝ)) * (3 * Real.log k) :=
        mul_le_mul_of_nonneg_right hDPlow (by positivity)
      _ = _ := by ring
  apply (mul_le_mul_iff_right₀ hDpos).mp
  nlinarith

/-- The logarithmic size of the inverse small-cell offset. -/
theorem scalar_dimension_log_q_le {k q : ℕ} (hk : 2 ≤ k)
    (hqlog : (dimension k : ℝ) * Real.log q ≤
      c * k * Real.log k + dimension k * Real.log (2 * (k : ℝ) ^ 2)) :
    ((dimension k : ℝ) + 1) * Real.log q ≤ 13 * k * Real.log k := by
  have hk1 : 1 ≤ k := by omega
  have hD1 : (1 : ℝ) ≤ dimension k := by
    exact_mod_cast (show 1 ≤ dimension k by have := dimension_pos hk1; omega)
  have hD0 : (0 : ℝ) ≤ dimension k := Nat.cast_nonneg _
  have hL : 0 ≤ Real.log k := Real.log_natCast_nonneg k
  have hqL : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hslack : (dimension k : ℝ) * Real.log (2 * (k : ℝ) ^ 2) ≤
      6 * k * Real.log k := by
    calc
      (dimension k : ℝ) * Real.log (2 * (k : ℝ) ^ 2) ≤
          dimension k * (3 * Real.log k) :=
        mul_le_mul_of_nonneg_left (scalar_log_prime_slack hk) hD0
      _ ≤ (2 * k) * (3 * Real.log k) :=
        mul_le_mul_of_nonneg_right (scalar_dimension_le_two_mul hk1) (by positivity)
      _ = _ := by ring
  have hc : c ≤ (1 / 2 : ℝ) := by norm_num [c]
  have hck : c * k * Real.log k ≤ (1 / 2 : ℝ) * k * Real.log k :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg k)) hL
  have hdup : ((dimension k : ℝ) + 1) * Real.log q ≤
      (2 * dimension k) * Real.log q :=
    mul_le_mul_of_nonneg_right (by linarith) hqL
  nlinarith

/-- The actual offset `q^(-(D+1))`, written using a natural power. -/
def scalarAlpha (k q : ℕ) : ℝ := 1 / (q : ℝ) ^ (dimension k + 1)

/-- The logarithmic radius of the exponential mesh. -/
def scalarRadius (k q : ℕ) : ℝ := Real.log (1 + 1 / (2 * scalarAlpha k q))

/-- The actual number of positive radial mesh intervals. -/
def scalarMeshSize (k q : ℕ) : ℕ := ⌈(k : ℝ) ^ 2 * scalarRadius k q⌉₊

theorem scalar_q_power_ge_four {k q : ℕ} (hk : 1 ≤ k) (hq : 2 ≤ q) :
    (4 : ℝ) ≤ (q : ℝ) ^ (dimension k + 1) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hD := dimension_pos hk
  calc
    (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
    _ ≤ (q : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hq2 2
    _ ≤ (q : ℝ) ^ (dimension k + 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)

theorem scalarAlpha_pos {k q : ℕ} (hq : 2 ≤ q) : 0 < scalarAlpha k q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  unfold scalarAlpha
  positivity

theorem scalarAlpha_le_quarter {k q : ℕ} (hk : 1 ≤ k) (hq : 2 ≤ q) :
    scalarAlpha k q ≤ (1 / 4 : ℝ) :=
  one_div_le_one_div_of_le (by norm_num) (scalar_q_power_ge_four hk hq)

theorem scalarRadius_pos {k q : ℕ} (hq : 2 ≤ q) : 0 < scalarRadius k q := by
  have ha := scalarAlpha_pos (k := k) hq
  apply Real.log_pos
  have : 0 < (1 : ℝ) / (2 * scalarAlpha k q) := by positivity
  linarith

/-- The mesh logarithmic radius is at most the logarithm of its denominator. -/
theorem scalarRadius_le_dimension_log_q {k q : ℕ}
    (hk : 1 ≤ k) (hq : 2 ≤ q) :
    scalarRadius k q ≤ ((dimension k : ℝ) + 1) * Real.log q := by
  have hp4 := scalar_q_power_ge_four hk hq
  have he : (1 : ℝ) / (2 * scalarAlpha k q) =
      (q : ℝ) ^ (dimension k + 1) / 2 := by
    simp [scalarAlpha, div_eq_mul_inv, mul_inv_rev]
  unfold scalarRadius
  rw [he]
  calc
    Real.log (1 + (q : ℝ) ^ (dimension k + 1) / 2) ≤
        Real.log ((q : ℝ) ^ (dimension k + 1)) :=
      Real.log_le_log (by linarith) (by linarith)
    _ = ((dimension k : ℝ) + 1) * Real.log q := by
      simp only [Real.log_pow, Nat.cast_add, Nat.cast_one]

/-- Explicit logarithmic radius bound for every admissible prime-power choice. -/
theorem scalarRadius_le {k q : ℕ} (hk : 2 ≤ k) (hq : 2 ≤ q)
    (hqlog : (dimension k : ℝ) * Real.log q ≤
      c * k * Real.log k + dimension k * Real.log (2 * (k : ℝ) ^ 2)) :
    scalarRadius k q ≤ 13 * k * Real.log k :=
  (scalarRadius_le_dimension_log_q (by omega) hq).trans
    (scalar_dimension_log_q_le hk hqlog)

/-- An explicit bound on the number of labels in the signed radial mesh. -/
theorem scalarMeshSize_upper {k q : ℕ} (hk : 2 ≤ k) (hq : 2 ≤ q)
    (hlog : 1 ≤ Real.log k)
    (hqlog : (dimension k : ℝ) * Real.log q ≤
      c * k * Real.log k + dimension k * Real.log (2 * (k : ℝ) ^ 2)) :
    2 * (scalarMeshSize k q : ℝ) ≤ 28 * (k : ℝ) ^ 3 * Real.log k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hRpos := scalarRadius_pos (k := k) hq
  have hceil : (scalarMeshSize k q : ℝ) <
      (k : ℝ) ^ 2 * scalarRadius k q + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (sq_nonneg _) hRpos.le)
  have hR := scalarRadius_le hk hq hqlog
  have hradial : (k : ℝ) ^ 2 * scalarRadius k q ≤
      13 * (k : ℝ) ^ 3 * Real.log k := by
    calc
      (k : ℝ) ^ 2 * scalarRadius k q ≤ (k : ℝ) ^ 2 * (13 * k * Real.log k) :=
        mul_le_mul_of_nonneg_left hR (sq_nonneg _)
      _ = _ := by ring
  have hk3 : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ hkR
  have hmass : (1 : ℝ) ≤ (k : ℝ) ^ 3 * Real.log k :=
    one_le_mul_of_one_le_of_one_le hk3 hlog
  nlinarith

end QuantitativeVanDerWaerden.Parameters

end

end OAI
end
end

section
section
namespace OAI

/-!
# The adaptive mesh with the selected scalar parameters

This adapter instantiates the proved adaptive-mesh construction with `H=k⁻²`
and `alpha=q^(-(D+1))`. Its interval count agrees with the scalar ceiling used
in the numerical size estimates.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.Parameters

theorem selected_meshScale_le_eighth {k : ℕ} (hk : 3 ≤ k) :
    meshScale k ≤ (1 / 8 : ℝ) := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  unfold meshScale
  apply (div_le_iff₀ hp).mpr
  nlinarith

theorem selected_meshScale_le_one {k : ℕ} (hk : 3 ≤ k) :
    meshScale k ≤ 1 := (selected_meshScale_le_eighth hk).trans (by norm_num)

/-- The actual exponential mesh for the selected progression length and base. -/
def selectedAdaptiveMesh {k q : ℕ} (hk : 3 ≤ k) (hq : 2 ≤ q) : AdaptiveMesh where
  H := meshScale k
  alpha := scalarAlpha k q
  H_pos := meshScale_pos (by omega)
  H_le := selected_meshScale_le_eighth hk
  alpha_pos := scalarAlpha_pos hq
  alpha_le := scalarAlpha_le_quarter (by omega) hq

@[simp] theorem selectedAdaptiveMesh_H {k q : ℕ} (hk : 3 ≤ k) (hq : 2 ≤ q) :
    (selectedAdaptiveMesh hk hq).H = meshScale k := rfl

@[simp] theorem selectedAdaptiveMesh_alpha {k q : ℕ} (hk : 3 ≤ k) (hq : 2 ≤ q) :
    (selectedAdaptiveMesh hk hq).alpha = scalarAlpha k q := rfl

@[simp] theorem selectedAdaptiveMesh_R {k q : ℕ} (hk : 3 ≤ k) (hq : 2 ≤ q) :
    (selectedAdaptiveMesh hk hq).R = scalarRadius k q := rfl

@[simp] theorem selectedAdaptiveMesh_m {k q : ℕ} (hk : 3 ≤ k) (hq : 2 ≤ q) :
    (selectedAdaptiveMesh hk hq).m = scalarMeshSize k q := by
  unfold AdaptiveMesh.m scalarMeshSize
  congr 1
  change scalarRadius k q / meshScale k = (k : ℝ) ^ 2 * scalarRadius k q
  simp [meshScale, div_eq_mul_inv, mul_comm]

@[simp] theorem selectedAdaptiveMesh_card {k q : ℕ} (hk : 3 ≤ k) (hq : 2 ≤ q) :
    Fintype.card (selectedAdaptiveMesh hk hq).Label = 2 * scalarMeshSize k q := by
  rw [AdaptiveMesh.card_label, selectedAdaptiveMesh_m]

/-- Concrete polynomial bound on the adaptive coordinate-label count. -/
theorem selectedAdaptiveMesh_card_le {k q : ℕ} (hk : 3 ≤ k) (hq : 2 ≤ q)
    (hlog : 1 ≤ Real.log k)
    (hqlog : (dimension k : ℝ) * Real.log q ≤
      c * k * Real.log k + dimension k * Real.log (2 * (k : ℝ) ^ 2)) :
    (Fintype.card (selectedAdaptiveMesh hk hq).Label : ℝ) ≤
      28 * (k : ℝ) ^ 3 * Real.log k := by
  rw [selectedAdaptiveMesh_card]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    scalarMeshSize_upper (by omega) hq hlog hqlog

end QuantitativeVanDerWaerden.Parameters

end

end OAI
end
end

section
section
namespace OAI

/-! Ternary real comparisons, shared independently of arrangement counting. -/

noncomputable section

namespace QuantitativeVanDerWaerden

/-- Literal signs: `0` is negative, `1` is zero, and `2` is positive. -/
def ternarySign (x : ℝ) : Fin 3 :=
  if x < 0 then 0 else if 0 < x then 2 else 1

@[simp] theorem ternarySign_eq_zero (x : ℝ) : ternarySign x = 0 ↔ x < 0 := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simp [ternarySign, hx]
  · simp [hx, ternarySign]
  · simp [ternarySign, hx, not_lt.mpr hx.le]

@[simp] theorem ternarySign_eq_one (x : ℝ) : ternarySign x = 1 ↔ x = 0 := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simp [ternarySign, hx, ne_of_lt hx]
  · simp [hx, ternarySign]
  · simp [ternarySign, hx, not_lt.mpr hx.le, ne_of_gt hx]

@[simp] theorem ternarySign_eq_two (x : ℝ) : ternarySign x = 2 ↔ 0 < x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simp [ternarySign, hx, not_lt.mpr hx.le]
  · simp [hx, ternarySign]
  · simp [ternarySign, hx, not_lt.mpr hx.le]

end QuantitativeVanDerWaerden

end

end OAI
end
end

section
section
namespace OAI

namespace QuantitativeVanDerWaerden.UniformMesh

noncomputable section

/-- The left endpoint of a literal interval in `[0,1)`. -/
def left (n : ℕ) (i : Fin n) : ℝ := (i.val : ℝ) / n

/-- The upper endpoint is excluded. -/
def right (n : ℕ) (i : Fin n) : ℝ := ((i.val : ℝ) + 1) / n

def Contains (n : ℕ) (i : Fin n) (x : ℝ) : Prop :=
  left n i ≤ x ∧ x < right n i

def label (n : ℕ) (hn : 0 < n) (x : ℝ) : Fin n :=
  ⟨⌊(n : ℝ) * Int.fract x⌋₊, by
    apply (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg n) (Int.fract_nonneg x))).2
    have hp : (0 : ℝ) < n := by exact_mod_cast hn
    simpa only [mul_one] using mul_lt_mul_of_pos_left (Int.fract_lt_one x) hp⟩

@[simp] theorem label_val (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (label n hn x).val = ⌊(n : ℝ) * Int.fract x⌋₊ := rfl

theorem left_nonneg (n : ℕ) (i : Fin n) : 0 ≤ left n i := by
  unfold left
  positivity

theorem right_le_one (n : ℕ) (hn : 0 < n) (i : Fin n) : right n i ≤ 1 := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_one hp).2
  exact_mod_cast (Nat.add_one_le_iff.mpr i.isLt)

theorem left_lt_right (n : ℕ) (hn : 0 < n) (i : Fin n) : left n i < right n i := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  exact (div_lt_div_iff_of_pos_right hp).2 (by linarith)

theorem width_eq (n : ℕ) (i : Fin n) : right n i - left n i = 1 / (n : ℝ) := by
  unfold right left
  rw [← sub_div]
  congr 1
  ring

theorem label_mem (n : ℕ) (hn : 0 < n) (x : ℝ) :
    ((label n hn x).val : ℝ) / n ≤ Int.fract x ∧
      Int.fract x < (((label n hn x).val : ℝ) + 1) / n := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have hnonneg := mul_nonneg (Nat.cast_nonneg n) (Int.fract_nonneg x)
  constructor
  · apply (div_le_iff₀ hp).2
    simpa only [label_val, mul_comm] using Nat.floor_le hnonneg
  · apply (lt_div_iff₀ hp).2
    simpa only [label_val, mul_comm] using Nat.lt_floor_add_one ((n : ℝ) * Int.fract x)

theorem label_mem_iff (n : ℕ) (hn : 0 < n) (x : ℝ) (i : Fin n) :
    label n hn x = i ↔ Contains n i (Int.fract x) := by
  constructor
  · rintro rfl
    exact label_mem n hn x
  · intro hi
    have hp : (0 : ℝ) < n := by exact_mod_cast hn
    apply Fin.ext
    change ⌊(n : ℝ) * Int.fract x⌋₊ = i.val
    apply (Nat.floor_eq_iff (mul_nonneg hp.le (Int.fract_nonneg x))).2
    constructor
    · simpa only [mul_comm] using (div_le_iff₀ hp).1 hi.1
    · simpa only [mul_comm] using (lt_div_iff₀ hp).1 hi.2

/-- The literal half-open intervals cover `[0,1)` exactly once. -/
theorem existsUnique_contains (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : 0 ≤ x ∧ x < 1) : ∃! i : Fin n, Contains n i x := by
  have hf : Int.fract x = x := Int.fract_eq_self.2 hx
  refine ⟨label n hn x, ?_, ?_⟩
  · simpa only [hf] using (label_mem_iff n hn x (label n hn x)).1 rfl
  · intro i hi
    exact ((label_mem_iff n hn x i).2 (by simpa only [hf] using hi)).symm

@[simp] theorem label_add_int (n : ℕ) (hn : 0 < n) (x : ℝ) (z : ℤ) :
    label n hn (x + z) = label n hn x := by
  apply Fin.ext
  simp only [label_val, Int.fract_add_intCast]

theorem label_eq_of_integer_difference (n : ℕ) (hn : 0 < n) (x y : ℝ)
    (h : ∃ z : ℤ, x - y = z) : label n hn x = label n hn y := by
  apply Fin.ext
  simp only [label_val, Int.fract_eq_fract.2 h]

/-- Integer floor modulo n recovers the literal fractional-part label. -/
theorem label_cast_eq_emod (n : ℕ) (hn : 0 < n) (x : ℝ) :
    ((label n hn x).val : ℤ) = ⌊(n : ℝ) * x⌋ % (n : ℤ) := by
  have hnonneg := mul_nonneg (Nat.cast_nonneg n) (Int.fract_nonneg x)
  have hf : ((label n hn x).val : ℤ) =
      ⌊(n : ℝ) * x⌋ - (n : ℤ) * ⌊x⌋ := by
    rw [label_val, Int.natCast_floor_eq_floor hnonneg]
    have hrewrite : (n : ℝ) * Int.fract x =
        (n : ℝ) * x - (((n : ℤ) * ⌊x⌋ : ℤ) : ℝ) := by
      simp only [Int.fract, Int.cast_mul, Int.cast_natCast]
      ring
    rw [hrewrite, Int.floor_sub_intCast]
  have hdecomp : ⌊(n : ℝ) * x⌋ =
      ((label n hn x).val : ℤ) + (n : ℤ) * ⌊x⌋ := by omega
  rw [hdecomp, Int.add_mul_emod_self_left, Int.emod_eq_of_lt]
  · exact Int.natCast_nonneg _
  · exact_mod_cast (label n hn x).isLt

theorem label_eq_of_floor_eq (n : ℕ) (hn : 0 < n) (x y : ℝ)
    (h : ⌊(n : ℝ) * x⌋ = ⌊(n : ℝ) * y⌋) : label n hn x = label n hn y := by
  apply Fin.ext
  have hc : ((label n hn x).val : ℤ) = ((label n hn y).val : ℤ) := by
    rw [label_cast_eq_emod, label_cast_eq_emod, h]
  exact_mod_cast hc

/-- Precisely the lifted lattice endpoints lying in a closed target interval. -/
def liftedEndpoints (n : ℕ) (a b : ℝ) : Finset ℤ :=
  Finset.Icc ⌈(n : ℝ) * a⌉ ⌊(n : ℝ) * b⌋

theorem mem_liftedEndpoints (n : ℕ) (hn : 0 < n) (a b : ℝ) (j : ℤ) :
    j ∈ liftedEndpoints n a b ↔ a ≤ (j : ℝ) / n ∧ (j : ℝ) / n ≤ b := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  rw [liftedEndpoints, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨(le_div_iff₀ hp).2 (by simpa only [mul_comm] using hl),
      (div_le_iff₀ hp).2 (by simpa only [mul_comm] using hu)⟩
  · rintro ⟨hl, hu⟩
    exact ⟨by simpa only [mul_comm] using (le_div_iff₀ hp).1 hl,
      by simpa only [mul_comm] using (div_le_iff₀ hp).1 hu⟩

/-- The closed interval may meet both extreme endpoints; hence four, not three. -/
theorem card_liftedEndpoints_le_four (n : ℕ) (hn : 0 < n) (a b : ℝ)
    (hwidth : b - a ≤ 3 / (n : ℝ)) : (liftedEndpoints n a b).card ≤ 4 := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : (n : ℝ) * (b - a) ≤ 3 := by
    simpa only [mul_comm] using (le_div_iff₀ hp).1 hwidth
  have hr : ((⌊(n : ℝ) * b⌋ + 1 - ⌈(n : ℝ) * a⌉ : ℤ) : ℝ) ≤ 4 := by
    push_cast
    nlinarith [Int.floor_le ((n : ℝ) * b), Int.le_ceil ((n : ℝ) * a)]
  have hi : ⌊(n : ℝ) * b⌋ + 1 - ⌈(n : ℝ) * a⌉ ≤ (4 : ℤ) := by exact_mod_cast hr
  rw [liftedEndpoints, Int.card_Icc]
  omega

private theorem floor_le_of_signs_eq (n : ℕ) (hn : 0 < n) (a b x y : ℝ)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hsign : ∀ j ∈ liftedEndpoints n a b,
      ternarySign (x - (j : ℝ) / n) = ternarySign (y - (j : ℝ) / n)) :
    ⌊(n : ℝ) * x⌋ ≤ ⌊(n : ℝ) * y⌋ := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  by_contra h
  let j : ℤ := ⌊(n : ℝ) * y⌋ + 1
  have hjfloor : j ≤ ⌊(n : ℝ) * x⌋ := by dsimp [j]; omega
  have hyj : y < (j : ℝ) / n := by
    apply (lt_div_iff₀ hp).2
    simpa only [j, Int.cast_add, Int.cast_one, mul_comm] using
      Int.lt_floor_add_one ((n : ℝ) * y)
  have hjx : (j : ℝ) / n ≤ x := by
    apply (div_le_iff₀ hp).2
    simpa only [mul_comm] using (Int.le_floor.1 hjfloor)
  have hj : j ∈ liftedEndpoints n a b :=
    (mem_liftedEndpoints n hn a b j).2 ⟨hy.1.trans hyj.le, hjx.trans hx.2⟩
  have hyzero : ternarySign (y - (j : ℝ) / n) = 0 :=
    (ternarySign_eq_zero _).2 (sub_neg.mpr hyj)
  have hxneg : x - (j : ℝ) / n < 0 :=
    (ternarySign_eq_zero _).1 ((hsign j hj).trans hyzero)
  linarith

/-- Literal-label factorization through finitely many ternary comparisons.
No width or counting premise is needed for this determination statement. -/
theorem label_eq_of_signs_eq (n : ℕ) (hn : 0 < n) (a b x y : ℝ)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hsign : ∀ j ∈ liftedEndpoints n a b,
      ternarySign (x - (j : ℝ) / n) = ternarySign (y - (j : ℝ) / n)) :
    label n hn x = label n hn y := by
  apply label_eq_of_floor_eq n hn x y
  exact le_antisymm (floor_le_of_signs_eq n hn a b x y hx hy hsign)
    (floor_le_of_signs_eq n hn a b y x hy hx (fun j hj => (hsign j hj).symm))

end

end QuantitativeVanDerWaerden.UniformMesh

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace QuantitativeVanDerWaerden

/-- The actual two-system full label of a cyclic point. -/
def literalFullLabel (mesh : AdaptiveMesh) (q D lam Ucount : ℕ)
    (hU : 0 < Ucount) (n : CyclicGroup q D) :
    (Fin D → Fin Ucount) × (Fin D → mesh.Label) :=
  (fun i => UniformMesh.label Ucount hU (xRep q D n i),
    fun i => mesh.meshLabel (yRep q D lam n i))

theorem uniformLabel_xRep_eq_iff (q D Ucount : ℕ) (hU : 0 < Ucount)
    (n : CyclicGroup q D) (i : Fin D) (u : Fin Ucount) :
    UniformMesh.label Ucount hU (xRep q D n i) = u ↔
      UniformMesh.Contains Ucount u (xRep q D n i) := by
  have hf := Int.fract_eq_self.mpr (xRep_mem q D n i)
  simpa only [hf] using UniformMesh.label_mem_iff Ucount hU (xRep q D n i) u

theorem meshLabel_yRep_eq_iff (mesh : AdaptiveMesh) (q D lam : ℕ)
    (n : CyclicGroup q D) (i : Fin D) (v : mesh.Label) :
    mesh.meshLabel (yRep q D lam n i) = v ↔
      mesh.Contains v (yRep q D lam n i) := by
  have hy := yRep_mem q D lam n i
  have hc := centered_eq_of_mem hy.1 hy.2
  simpa only [hc] using mesh.meshLabel_eq_iff (yRep q D lam n i) v

theorem literalFullLabel_first_mem (mesh : AdaptiveMesh) (q D lam Ucount : ℕ)
    (hU : 0 < Ucount) (n : CyclicGroup q D) (i : Fin D) :
    UniformMesh.Contains Ucount ((literalFullLabel mesh q D lam Ucount hU n).1 i)
      (xRep q D n i) :=
  (uniformLabel_xRep_eq_iff q D Ucount hU n i _).mp rfl

theorem literalFullLabel_second_mem (mesh : AdaptiveMesh) (q D lam Ucount : ℕ)
    (hU : 0 < Ucount) (n : CyclicGroup q D) (i : Fin D) :
    mesh.Contains ((literalFullLabel mesh q D lam Ucount hU n).2 i)
      (yRep q D lam n i) :=
  (meshLabel_yRep_eq_iff mesh q D lam n i _).mp rfl

/-- Both directions use the actual half-open mesh labels. -/
theorem literalFullLabel_eq_iff (mesh : AdaptiveMesh) (q D lam Ucount : ℕ)
    (hU : 0 < Ucount) (n : CyclicGroup q D)
    (beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)) :
    literalFullLabel mesh q D lam Ucount hU n = beta ↔
      (∀ i, UniformMesh.Contains Ucount (beta.1 i) (xRep q D n i)) ∧
      (∀ i, mesh.Contains (beta.2 i) (yRep q D lam n i)) := by
  constructor
  · intro h
    constructor
    · intro i
      apply (uniformLabel_xRep_eq_iff q D Ucount hU n i (beta.1 i)).mp
      exact congrFun (congrArg Prod.fst h) i
    · intro i
      apply (meshLabel_yRep_eq_iff mesh q D lam n i (beta.2 i)).mp
      exact congrFun (congrArg Prod.snd h) i
  · rintro ⟨hx, hy⟩
    apply Prod.ext
    · funext i
      exact (uniformLabel_xRep_eq_iff q D Ucount hU n i (beta.1 i)).mpr (hx i)
    · funext i
      exact (meshLabel_yRep_eq_iff mesh q D lam n i (beta.2 i)).mpr (hy i)

/-- An unfolded rectangle API, retaining every excluded upper endpoint. -/
theorem literalFullLabel_eq_iff_mem_rectangle (mesh : AdaptiveMesh)
    (q D lam Ucount : ℕ) (hU : 0 < Ucount) (n : CyclicGroup q D)
    (beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)) :
    literalFullLabel mesh q D lam Ucount hU n = beta ↔
      (∀ i, UniformMesh.left Ucount (beta.1 i) ≤ xRep q D n i ∧
        xRep q D n i < UniformMesh.right Ucount (beta.1 i)) ∧
      (∀ i, mesh.left (beta.2 i) ≤ yRep q D lam n i ∧
        yRep q D lam n i < mesh.right (beta.2 i)) :=
  literalFullLabel_eq_iff mesh q D lam Ucount hU n beta

theorem literalFullLabel_first_endpoints (mesh : AdaptiveMesh)
    (D Ucount : ℕ) (hU : 0 < Ucount)
    (beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)) (i : Fin D) :
    0 ≤ UniformMesh.left Ucount (beta.1 i) ∧
      UniformMesh.left Ucount (beta.1 i) < UniformMesh.right Ucount (beta.1 i) ∧
      UniformMesh.right Ucount (beta.1 i) ≤ 1 :=
  ⟨UniformMesh.left_nonneg Ucount (beta.1 i),
    UniformMesh.left_lt_right Ucount hU (beta.1 i),
    UniformMesh.right_le_one Ucount hU (beta.1 i)⟩

theorem literalFullLabel_second_endpoints (mesh : AdaptiveMesh)
    (D Ucount : ℕ)
    (beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)) (i : Fin D) :
    -(1 / 2 : ℝ) ≤ mesh.left (beta.2 i) ∧
      mesh.left (beta.2 i) < mesh.right (beta.2 i) ∧
      mesh.right (beta.2 i) ≤ 1 / 2 :=
  ⟨mesh.left_ge_neg_half (beta.2 i), sub_pos.mp (mesh.width_pos (beta.2 i)),
    mesh.right_le_half (beta.2 i)⟩

theorem literalFullLabel_same_first_distance (mesh : AdaptiveMesh)
    (q D lam Ucount : ℕ) (hU : 0 < Ucount) {a b : CyclicGroup q D}
    (h : literalFullLabel mesh q D lam Ucount hU a =
      literalFullLabel mesh q D lam Ucount hU b) (i : Fin D) :
    |xRep q D a i - xRep q D b i| ≤ 1 / (Ucount : ℝ) := by
  have ha := literalFullLabel_first_mem mesh q D lam Ucount hU a i
  have hb := literalFullLabel_first_mem mesh q D lam Ucount hU b i
  have hi := congrFun (congrArg Prod.fst h) i
  rw [← hi] at hb
  have hw := UniformMesh.width_eq Ucount ((literalFullLabel mesh q D lam Ucount hU a).1 i)
  unfold UniformMesh.Contains at ha hb
  apply abs_le.mpr
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

theorem literalFullLabel_same_second_distance (mesh : AdaptiveMesh)
    (q D lam Ucount : ℕ) (hU : 0 < Ucount) {a b : CyclicGroup q D}
    (h : literalFullLabel mesh q D lam Ucount hU a =
      literalFullLabel mesh q D lam Ucount hU b) (i : Fin D) :
    |yRep q D lam a i - yRep q D lam b i| ≤ 2 * mesh.H := by
  have ha := literalFullLabel_second_mem mesh q D lam Ucount hU a i
  have hb := literalFullLabel_second_mem mesh q D lam Ucount hU b i
  have hi := congrFun (congrArg Prod.snd h) i
  rw [← hi] at hb
  have hw := mesh.width_le_two_H ((literalFullLabel mesh q D lam Ucount hU a).2 i)
  unfold AdaptiveMesh.Contains at ha hb
  unfold AdaptiveMesh.width at hw
  apply abs_le.mpr
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

end QuantitativeVanDerWaerden

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

variable {k : ℕ}

/-- The number of first-system intervals: exactly `1 / Hx`. -/
def uniformCount (k : ℕ) : ℕ := k ^ 2 * lambda k

theorem uniformCount_pos (hk : 3 ≤ k) : 0 < uniformCount k :=
  Nat.mul_pos (pow_pos (by omega : 0 < k) _) (lambda_pos k)

/-- The actual exponential second-system mesh, using the selected base. -/
def mesh (s : Data k) (hk : 3 ≤ k) : AdaptiveMesh :=
  selectedAdaptiveMesh hk s.two_le

@[simp] theorem mesh_H (s : Data k) (hk : 3 ≤ k) :
    (mesh s hk).H = meshScale k := rfl

@[simp] theorem mesh_alpha (s : Data k) (hk : 3 ≤ k) :
    (mesh s hk).alpha = 1 / (s.q : ℝ) ^ (dimension k + 1) := rfl

@[simp] theorem mesh_R (s : Data k) (hk : 3 ≤ k) :
    (mesh s hk).R = scalarRadius k s.q := rfl

@[simp] theorem mesh_m (s : Data k) (hk : 3 ≤ k) :
    (mesh s hk).m = scalarMeshSize k s.q :=
  selectedAdaptiveMesh_m hk s.two_le

theorem mesh_small (s : Data k) (hk : 3 ≤ k) :
    2 * (k : ℝ) * (mesh s hk).H < 1 := affine_box_small hk

abbrev Label (s : Data k) (hk : 3 ≤ k) :=
  (Fin (dimension k) → Fin (uniformCount k)) ×
    (Fin (dimension k) → (mesh s hk).Label)

/-- Actual full labels of actual cyclic points. This specializes the generic
literal-label definition also used in the heavy-label return proof. -/
def fullLabel (s : Data k) (hk : 3 ≤ k) (n : Group s) : Label s hk :=
  literalFullLabel (mesh s hk) s.q (dimension k) (lambda k)
    (uniformCount k) (uniformCount_pos hk) n

def firstLabel (s : Data k) (hk : 3 ≤ k) (n : Group s) :
    Fin (dimension k) → Fin (uniformCount k) := (fullLabel s hk n).1

def secondLabel (s : Data k) (hk : 3 ≤ k) (n : Group s) :
    Fin (dimension k) → (mesh s hk).Label := (fullLabel s hk n).2

@[simp] theorem firstLabel_apply (s : Data k) (hk : 3 ≤ k)
    (n : Group s) (i : Fin (dimension k)) :
    firstLabel s hk n i = UniformMesh.label (uniformCount k)
      (uniformCount_pos hk) (xRep s.q (dimension k) n i) := rfl

@[simp] theorem secondLabel_apply (s : Data k) (hk : 3 ≤ k)
    (n : Group s) (i : Fin (dimension k)) :
    secondLabel s hk n i =
      (mesh s hk).meshLabel (yRep s.q (dimension k) (lambda k) n i) := rfl

theorem fullLabel_eq_pair (s : Data k) (hk : 3 ≤ k) (n : Group s) :
    fullLabel s hk n = (firstLabel s hk n, secondLabel s hk n) := rfl

theorem firstLabel_contains (s : Data k) (hk : 3 ≤ k)
    (n : Group s) (i : Fin (dimension k)) :
    UniformMesh.Contains (uniformCount k) (firstLabel s hk n i)
      (xRep s.q (dimension k) n i) :=
  literalFullLabel_first_mem (mesh s hk) s.q (dimension k) (lambda k)
    (uniformCount k) (uniformCount_pos hk) n i

theorem secondLabel_contains (s : Data k) (hk : 3 ≤ k)
    (n : Group s) (i : Fin (dimension k)) :
    (mesh s hk).Contains (secondLabel s hk n i)
      (yRep s.q (dimension k) (lambda k) n i) :=
  literalFullLabel_second_mem (mesh s hk) s.q (dimension k) (lambda k)
    (uniformCount k) (uniformCount_pos hk) n i

/-- Full-label equality means exactly membership in all the specified
half-open coordinate intervals, including their boundary conventions. -/
theorem fullLabel_eq_iff (s : Data k) (hk : 3 ≤ k)
    (n : Group s) (label : Label s hk) :
    fullLabel s hk n = label ↔
      (∀ i, UniformMesh.Contains (uniformCount k) (label.1 i)
        (xRep s.q (dimension k) n i)) ∧
      (∀ i, (mesh s hk).Contains (label.2 i)
        (yRep s.q (dimension k) (lambda k) n i)) :=
  literalFullLabel_eq_iff (mesh s hk) s.q (dimension k) (lambda k)
    (uniformCount k) (uniformCount_pos hk) n label

theorem uniformWidth_eq :
    1 / (uniformCount k : ℝ) = meshScale k / (lambda k : ℝ) := by
  simp only [uniformCount, Nat.cast_mul, Nat.cast_pow, meshScale, div_div]

theorem first_width (i : Fin (uniformCount k)) :
    UniformMesh.right (uniformCount k) i - UniformMesh.left (uniformCount k) i =
      meshScale k / (lambda k : ℝ) := by
  rw [UniformMesh.width_eq, uniformWidth_eq]

theorem fullLabel_same_first_distance (s : Data k) (hk : 3 ≤ k)
    {a b : Group s} (h : fullLabel s hk a = fullLabel s hk b)
    (i : Fin (dimension k)) :
    |xRep s.q (dimension k) a i - xRep s.q (dimension k) b i| ≤
      meshScale k / (lambda k : ℝ) := by
  rw [← uniformWidth_eq]
  exact literalFullLabel_same_first_distance (mesh s hk) s.q (dimension k)
    (lambda k) (uniformCount k) (uniformCount_pos hk) h i

theorem fullLabel_same_second_distance (s : Data k) (hk : 3 ≤ k)
    {a b : Group s} (h : fullLabel s hk a = fullLabel s hk b)
    (i : Fin (dimension k)) :
    |yRep s.q (dimension k) (lambda k) a i -
      yRep s.q (dimension k) (lambda k) b i| ≤ 2 * meshScale k :=
  literalFullLabel_same_second_distance (mesh s hk) s.q (dimension k)
    (lambda k) (uniformCount k) (uniformCount_pos hk) h i

@[simp] theorem card_first_labels : Fintype.card (Fin (uniformCount k)) = uniformCount k :=
  Fintype.card_fin _

@[simp] theorem card_second_labels (s : Data k) (hk : 3 ≤ k) :
    Fintype.card (mesh s hk).Label = 2 * scalarMeshSize k s.q :=
  selectedAdaptiveMesh_card hk s.two_le

theorem card_labels (s : Data k) (hk : 3 ≤ k) :
    Fintype.card (Label s hk) =
      (uniformCount k) ^ dimension k * (2 * scalarMeshSize k s.q) ^ dimension k := by
  simp only [Label, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, mesh_m]

theorem card_second_labels_le (s : Data k) (hk : 3 ≤ k) :
    (Fintype.card (mesh s hk).Label : ℝ) ≤ 28 * (k : ℝ) ^ 3 * Real.log k :=
  selectedAdaptiveMesh_card_le hk s.two_le (one_le_log_length hk)
    (s.log_upper (by omega) (by have := dimension_pos (show 1 ≤ k by omega); omega))

/-- The actual label word of an ordered cyclic progression. No nonzero-step
condition is needed to define the word; event families impose it separately. -/
def fullLabelWord (s : Data k) (hk : 3 ≤ k) (ad : Group s × Group s) :
    Fin k → Label s hk :=
  fun j => fullLabel s hk (ad.1 + (j.val : Group s) * ad.2)

end QuantitativeVanDerWaerden.ConstructionModel

end

end OAI
end
end

section
section
namespace OAI


namespace QuantitativeVanDerWaerden

open scoped BigOperators

/-- A full label retains the literal first and second interval labels. -/
abbrev FullLabel (D : ℕ) (U : Type uU) (V : Type uV) := (Fin D → U) × (Fin D → V)

/-- The full output is dummy exactly when some second-coordinate output is
dummy. Stationary coordinates are supplied as `some` of their untruncated
label; rotating coordinates use the actual truncated output. -/
noncomputable def assembleLabel {D : ℕ} {U : Type uU} {V : Type uV}
    (first : Fin D → U) (second : Fin D → Option V) : Option (FullLabel D U V) := by
  classical
  exact if h : ∀ i, ∃ v, second i = some v then
    some (first, fun i => Classical.choose (h i)) else none

theorem assembleLabel_eq_none_iff {D : ℕ} {U : Type uU} {V : Type uV}
    (first : Fin D → U) (second : Fin D → Option V) :
    assembleLabel first second = none ↔ ∃ i, second i = none := by
  classical
  constructor
  · intro ha
    by_contra hn
    have hall : ∀ i, ∃ v, second i = some v := by
      intro i
      cases he : second i with
      | none => exact False.elim (hn ⟨i, he⟩)
      | some v => exact ⟨v, rfl⟩
    simp [assembleLabel, hall] at ha
  · rintro ⟨i, hi⟩
    have hn : ¬ ∀ j, ∃ v, second j = some v := by
      intro hall
      obtain ⟨v, hv⟩ := hall i
      rw [hi] at hv
      cases hv
    simp [assembleLabel, hn]

theorem assembleLabel_some {D : ℕ} {U : Type uU} {V : Type uV}
    (first : Fin D → U) (second : Fin D → V) :
    assembleLabel first (fun i => some (second i)) = some (first, second) := by
  classical
  have hall : ∀ i, ∃ v, some (second i) = some v := fun i => ⟨second i, rfl⟩
  have hchoice : (fun i => Classical.choose (hall i)) = second := by
    funext i
    exact (Option.some.inj (Classical.choose_spec (hall i))).symm
  simpa only [assembleLabel, dite_eq_left hall] using
    congrArg (fun f : Fin D → V => some (first, f)) hchoice

/-- Pointwise reconstruction introduces no independent choice of a mask. -/
noncomputable def assembleWord {D h : ℕ} {U : Type uU} {V : Type uV}
    (first : Fin D → Fin h → U) (second : Fin D → Fin h → Option V) :
    Fin h → Option (FullLabel D U V) :=
  fun z => assembleLabel (fun i => first i z) (fun i => second i z)

theorem assembleWord_dummy_iff {D h : ℕ} {U : Type uU} {V : Type uV}
    (first : Fin D → Fin h → U) (second : Fin D → Fin h → Option V) (z : Fin h) :
    assembleWord first second z = none ↔ ∃ i, second i z = none :=
  assembleLabel_eq_none_iff _ _

/-- All tuples of independently allowed scalar words. Dependent coordinate
types permit first words and truncated second words to have different types. -/
noncomputable def coordinateFamily {n : ℕ} {α : Fin n → Type uAlpha}
    (S : ∀ i, Finset (α i)) : Finset (∀ i, α i) := by
  classical
  exact Fintype.piFinset S

theorem card_coordinateFamily_le {n B : ℕ} {α : Fin n → Type uAlpha}
    (S : ∀ i, Finset (α i)) (hS : ∀ i, (S i).card ≤ B) :
    (coordinateFamily S).card ≤ B ^ n := by
  classical
  rw [coordinateFamily, Fintype.card_piFinset]
  calc
    ∏ i, (S i).card ≤ ∏ _i : Fin n, B :=
      Finset.prod_le_prod' (fun i _ => hS i)
    _ = B ^ n := by simp

/-- Arbitrary decoding cannot increase the product count. This applies to
literal full words and to pointwise dummy reconstruction alike. -/
theorem card_decoded_coordinateFamily_le {n B : ℕ} {α : Fin n → Type uAlpha}
    {Word : Type uWord} [DecidableEq Word]
    (S : ∀ i, Finset (α i)) (decode : (∀ i, α i) → Word)
    (hS : ∀ i, (S i).card ≤ B) :
    ((coordinateFamily S).image decode).card ≤ B ^ n :=
  Finset.card_image_le.trans (card_coordinateFamily_le S hS)

/-- The finite union over all rational step vectors and all possible anchor
positions. The scalar families can depend on both, as in the actual re-anchored
breakpoint construction. -/
noncomputable def anchoredFamily {D h : ℕ} {α : Fin (2 * D) → Type uAlpha}
    {Word : Type uWord} [DecidableEq Word]
    (S : (Fin D → Fin h) → Fin h → ∀ i, Finset (α i))
    (decode : (Fin D → Fin h) → Fin h → (∀ i, α i) → Word) : Finset Word := by
  classical
  exact Finset.univ.biUnion fun t => Finset.univ.biUnion fun z =>
    (coordinateFamily (S t z)).image (decode t z)

theorem card_anchoredFamily_le {D h B : ℕ} {α : Fin (2 * D) → Type uAlpha}
    {Word : Type uWord} [DecidableEq Word]
    (S : (Fin D → Fin h) → Fin h → ∀ i, Finset (α i))
    (decode : (Fin D → Fin h) → Fin h → (∀ i, α i) → Word)
    (hS : ∀ t z i, (S t z i).card ≤ B) :
    (anchoredFamily S decode).card ≤ h ^ (D + 1) * B ^ (2 * D) := by
  classical
  unfold anchoredFamily
  calc
    _ ≤ (Finset.univ : Finset (Fin D → Fin h)).card * (h * B ^ (2 * D)) := by
      apply Finset.card_biUnion_le_card_mul
      intro t _
      calc
        _ ≤ (Finset.univ : Finset (Fin h)).card * B ^ (2 * D) := by
          apply Finset.card_biUnion_le_card_mul
          intro z _
          exact card_decoded_coordinateFamily_le (S t z) (decode t z) (hS t z)
        _ = h * B ^ (2 * D) := by simp
    _ = h ^ (D + 1) * B ^ (2 * D) := by
      simp [pow_succ, Nat.mul_assoc]

theorem anchored_polynomial_estimate (D h : ℕ) (hD : 0 < D) (hh : 0 < h) :
    h ^ (D + 1) * (16 * (16004 * D * h + 1) ^ 6) ^ (2 * D) ≤
      (16005 * D * h) ^ (14 * D) := by
  have hDh : 0 < D * h := Nat.mul_pos hD hh
  have hbase : 16004 * D * h + 1 ≤ 16005 * (D * h) := by nlinarith
  have hscalar : 16 * (16004 * D * h + 1) ^ 6 ≤ 16005 ^ 7 * (D * h) ^ 6 := by
    calc
      _ ≤ 16005 * (16005 * (D * h)) ^ 6 :=
        Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hbase 6)
      _ = 16005 ^ 7 * (D * h) ^ 6 := by ring
  have hanchor : h ^ (D + 1) ≤ (D * h) ^ (2 * D) := by
    calc
      _ ≤ (D * h) ^ (D + 1) := Nat.pow_le_pow_left (by nlinarith) _
      _ ≤ (D * h) ^ (2 * D) := Nat.pow_le_pow_right hDh (by omega)
  calc
    _ ≤ (D * h) ^ (2 * D) * (16005 ^ 7 * (D * h) ^ 6) ^ (2 * D) :=
      Nat.mul_le_mul hanchor (Nat.pow_le_pow_left hscalar _)
    _ = 16005 ^ (7 * (2 * D)) * (D * h) ^ (2 * D + 6 * (2 * D)) := by
      rw [mul_pow (16005 ^ 7) ((D * h) ^ 6), ← pow_mul, ← pow_mul,
        mul_left_comm, ← pow_add]
    _ = (16005 * (D * h)) ^ (14 * D) := by
      have h₁ : 7 * (2 * D) = 14 * D := by omega
      have h₂ : 2 * D + 6 * (2 * D) = 14 * D := by omega
      rw [h₁, h₂, mul_pow 16005 (D * h)]
    _ = (16005 * D * h) ^ (14 * D) := by rw [Nat.mul_assoc]

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Actual eligible return-period words

The literal real paths, mesh labels, eligibility predicate, and finite event
indices are shared by counting and long-period geometry. Their definitions do
not depend on arrangement estimates. Counting is proved in `AnchoredPatterns`.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.AnchoredPatterns

open Set
open scoped BigOperators

/-- Starts and drift vectors of an actual local path. -/
structure Realization (D : ℕ) where
  x : Fin D → ℝ
  y : Fin D → ℝ
  u : Fin D → ℝ
  v : Fin D → ℝ

variable {D h : ℕ}

/-- Equivalent to reduced denominator one when `h > 0`; no drift restriction
is part of stationarity. -/
def stationary (lambda : ℕ) (t : Fin D → Fin h) (i : Fin D) : Prop :=
  h ∣ lambda * (t i).val

def firstPath (R : Realization D) (t : Fin D → Fin h) (z : Fin h) (i : Fin D) : ℝ :=
  R.x i + (z.val : ℝ) / h * ((t i).val + R.u i)

def secondPath (R : Realization D) (lambda : ℕ) (t : Fin D → Fin h)
    (z : Fin h) (i : Fin D) : ℝ :=
  R.y i + (z.val : ℝ) / h * ((lambda : ℝ) * (t i).val + R.v i)

def regular (eta : ℝ) (R : Realization D) (lambda : ℕ)
    (t : Fin D → Fin h) (z : Fin h) : Prop :=
  ∀ i, ¬ stationary lambda t i → eta ≤ rho (secondPath R lambda t z i)

def regularPositions (eta : ℝ) (R : Realization D) (lambda : ℕ)
    (t : Fin D → Fin h) : Finset (Fin h) := by
  classical
  exact Finset.univ.filter (regular eta R lambda t)

def fullLabel (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (R : Realization D)
    (lambda : ℕ) (t : Fin D → Fin h) (z : Fin h) : FullLabel D (Fin n) A.Label :=
  (fun i => UniformMesh.label n hn (firstPath R t z i),
    fun i => A.meshLabel (secondPath R lambda t z i))

def recordedWord (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ)
    (R : Realization D) (lambda : ℕ) (t : Fin D → Fin h) :
    Fin h → Option (FullLabel D (Fin n) A.Label) := by
  classical
  exact fun z => if regular eta R lambda t z then
    some (fullLabel n hn A R lambda t z) else none

structure EligibleRealization (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ)
    (lambda : ℕ) (t : Fin D → Fin h) (R : Realization D) : Prop where
  regular_many : h ≤ 2 * (regularPositions eta R lambda t).card
  regular_injective : ∀ z z', regular eta R lambda t z → regular eta R lambda t z' →
    fullLabel n hn A R lambda t z = fullLabel n hn A R lambda t z' → z = z'
  first_drift : ∀ i, |R.u i| ≤ 1 / (n : ℝ)
  rotating_drift : ∀ i, ¬ stationary lambda t i → |R.v i| ≤ A.H
  stationary_drift : ∀ i, stationary lambda t i → ∀ z,
    regular eta R lambda t z → |R.v i| ≤ A.width (A.meshLabel (secondPath R lambda t z i))

/-- The word itself is the pattern. Distinct realizing parameters do not
give distinct eligible objects. -/
def eligibleOptionFullLabel (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ)
    (lambda : ℕ) (t : Fin D → Fin h)
    (word : Fin h → Option (FullLabel D (Fin n) A.Label)) : Prop :=
  ∃ R : Realization D, EligibleRealization n hn A eta lambda t R ∧
    recordedWord n hn A eta R lambda t = word

/-- Actual step/word pairs, rather than a family of realizing parameters. -/
def eligiblePairs (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ)
    (lambda : ℕ) :
    Finset ((Fin D → Fin h) × (Fin h → Option (FullLabel D (Fin n) A.Label))) := by
  classical
  exact Finset.univ.filter (fun p => eligibleOptionFullLabel n hn A eta lambda p.1 p.2)

/-- Incidences with one fixed literal full label. -/
def through (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ) (lambda : ℕ)
    (beta : FullLabel D (Fin n) A.Label) :
    Finset ((Fin D → Fin h) × (Fin h → Option (FullLabel D (Fin n) A.Label))) := by
  classical
  exact (eligiblePairs n hn A eta lambda).filter (fun p => ∃ z, p.2 z = some beta)

@[simp] theorem mem_eligiblePairs (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh)
    (eta : ℝ) (lambda : ℕ)
    (p : (Fin D → Fin h) × (Fin h → Option (FullLabel D (Fin n) A.Label))) :
    p ∈ eligiblePairs n hn A eta lambda ↔
      eligibleOptionFullLabel n hn A eta lambda p.1 p.2 := by
  classical
  simp [eligiblePairs]

@[simp] theorem mem_through (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh)
    (eta : ℝ) (lambda : ℕ) (beta : FullLabel D (Fin n) A.Label)
    (p : (Fin D → Fin h) × (Fin h → Option (FullLabel D (Fin n) A.Label))) :
    p ∈ through n hn A eta lambda beta ↔
      eligibleOptionFullLabel n hn A eta lambda p.1 p.2 ∧ ∃ z, p.2 z = some beta := by
  classical
  simp [through]

theorem recordedWord_eq_some_iff (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ)
    (R : Realization D) (lambda : ℕ) (t : Fin D → Fin h) (z : Fin h)
    (beta : FullLabel D (Fin n) A.Label) :
    recordedWord n hn A eta R lambda t z = some beta ↔
      regular eta R lambda t z ∧ fullLabel n hn A R lambda t z = beta := by
  classical
  by_cases hz : regular eta R lambda t z <;> simp [recordedWord, hz]

end QuantitativeVanDerWaerden.AnchoredPatterns

end

end OAI
end
end

section
section
namespace OAI

/-!
# Residue classes in a finite interval

Each residue class modulo `w` occurs at least `n / w` times in `Fin n`.
On any interval of length at most `w`, reduction modulo `w` is injective.
-/

namespace QuantitativeVanDerWaerden

/-- Each row modulo `w` contains at least one point from each complete block. -/
theorem card_mod_row_lower (n w : ℕ) (hw : 0 < w) (j : Fin w) :
    n / w ≤ (Finset.univ.filter (fun i : Fin n => i.val % w = j.val)).card := by
  let f : Fin (n / w) → Fin n := fun k =>
    ⟨k.val * w + j.val, by
      calc
        k.val * w + j.val < k.val * w + w := Nat.add_lt_add_left j.isLt _
        _ = (k.val + 1) * w := by simp [Nat.add_mul]
        _ ≤ (n / w) * w := Nat.mul_le_mul_right w (Nat.succ_le_of_lt k.isLt)
        _ ≤ n := Nat.div_mul_le_self n w⟩
  have hf : Function.Injective f := by
    intro k l h
    apply Fin.ext
    have hval : k.val * w + j.val = l.val * w + j.val := congrArg Fin.val h
    exact Nat.eq_of_mul_eq_mul_right hw (Nat.add_right_cancel hval)
  have hmem : ∀ k ∈ (Finset.univ : Finset (Fin (n / w))),
      f k ∈ Finset.univ.filter (fun i : Fin n => i.val % w = j.val) := by
    intro k _
    simp [f, Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card_of_injOn f hmem (fun _ _ _ _ h => hf h)

/-- Subtype-cardinality form of `card_mod_row_lower`. -/
theorem card_mod_row_subtype_lower (n w : ℕ) (hw : 0 < w) (j : Fin w) :
    n / w ≤ Fintype.card {i : Fin n // i.val % w = j.val} := by
  simpa only [Fintype.card_subtype] using card_mod_row_lower n w hw j

/-- Equal residues in one interval of width `w` represent the same number. -/
theorem eq_of_mod_eq_of_mem_interval {a w x y : ℕ}
    (hxlo : a ≤ x) (hxhi : x < a + w)
    (hylo : a ≤ y) (hyhi : y < a + w)
    (hmod : x % w = y % w) : x = y := by
  have hxy : Nat.ModEq w x y := hmod
  exact Nat.le_antisymm (hxy.le_of_lt_add (by omega))
    (hxy.symm.le_of_lt_add (by omega))

/-- Cross multiplication gives a comparison of the integer row-size bounds. -/
theorem div_le_div_of_mul_le {M w d L : ℕ}
    (hw : 0 < w) (hd : 0 < d) (h : M * w ≤ d * L) :
    M / d ≤ L / w := by
  apply (Nat.le_div_iff_mul_le hw).mpr
  apply Nat.le_of_mul_le_mul_left (c := d) _ hd
  calc
    d * (M / d * w) = (M / d * d) * w := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ M * w := Nat.mul_le_mul_right w (Nat.div_mul_le_self M d)
    _ ≤ d * L := h

theorem div_ten_le_div_of_sandwich {M w k L : ℕ}
    (hw : 0 < w) (hlo : M * w ≤ k) (hhi : k ≤ 10 * L) :
    M / 10 ≤ L / w :=
  div_le_div_of_mul_le hw (by decide) (hlo.trans hhi)

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Balanced rows for bounded-multiplicity words

Order each label fibre consecutively, then distribute the resulting enumeration
cyclically among the rows. This proves the row decomposition used in the first
family of outer-coloring tests, without assuming a balanced decomposition.
-/


namespace QuantitativeVanDerWaerden

open scoped BigOperators

noncomputable section

variable {β : Type uBeta} [Fintype β]

/-- Labels occurring before `b` in a fixed enumeration. -/
def earlierLabels (b : β) : Finset β := by
  classical
  exact Finset.univ.filter fun a => Fintype.equivFin β a < Fintype.equivFin β b

/-- Starting index of the block belonging to `b`. -/
def blockOffset (c : β → ℕ) (b : β) : ℕ :=
  ∑ a ∈ earlierLabels b, c a

theorem blockOffset_add_le_total (c : β → ℕ) (b : β) :
    blockOffset c b + c b ≤ ∑ a, c a := by
  classical
  have hb : b ∉ earlierLabels b := by simp [earlierLabels]
  calc
    blockOffset c b + c b = ∑ a ∈ insert b (earlierLabels b), c a := by
      rw [Finset.sum_insert hb]
      simp only [blockOffset, Nat.add_comm]
    _ ≤ ∑ a, c a := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem blockOffset_add_le_of_lt (c : β → ℕ) {b d : β}
    (hbd : Fintype.equivFin β b < Fintype.equivFin β d) :
    blockOffset c b + c b ≤ blockOffset c d := by
  classical
  have hb : b ∉ earlierLabels b := by simp [earlierLabels]
  have hsub : insert b (earlierLabels b) ⊆ earlierLabels d := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simpa [earlierLabels] using hbd
    · have hab : Fintype.equivFin β a < Fintype.equivFin β b := by
        simpa [earlierLabels] using ha
      simpa [earlierLabels] using lt_trans hab hbd
  calc
    blockOffset c b + c b = ∑ a ∈ insert b (earlierLabels b), c a := by
      rw [Finset.sum_insert hb]
      simp only [blockOffset, Nat.add_comm]
    _ ≤ blockOffset c d := Finset.sum_le_sum_of_subset hsub

variable (A : β → Type uA) [∀ b, Fintype (A b)]

/-- The position of an element in the concatenation of the label fibres. -/
def groupedIndex (p : Σ b, A b) : Fin (∑ b, Fintype.card (A b)) :=
  ⟨blockOffset (fun b => Fintype.card (A b)) p.1 +
      (Fintype.equivFin (A p.1) p.2).val,
    lt_of_lt_of_le (Nat.add_lt_add_left (Fintype.equivFin (A p.1) p.2).isLt _)
      (blockOffset_add_le_total _ _)⟩

theorem groupedIndex_injective : Function.Injective (groupedIndex A) := by
  intro p q hpq
  have hv := congrArg Fin.val hpq
  change blockOffset (fun b => Fintype.card (A b)) p.1 +
      (Fintype.equivFin (A p.1) p.2).val =
    blockOffset (fun b => Fintype.card (A b)) q.1 +
      (Fintype.equivFin (A q.1) q.2).val at hv
  have he : p.1 = q.1 := by
    by_contra hne
    have hrne : Fintype.equivFin β p.1 ≠ Fintype.equivFin β q.1 :=
      fun h => hne ((Fintype.equivFin β).injective h)
    rcases lt_or_gt_of_ne hrne with hlt | hlt
    · have hoff := blockOffset_add_le_of_lt (fun b => Fintype.card (A b)) hlt
      have hp := (Fintype.equivFin (A p.1) p.2).isLt
      omega
    · have hoff := blockOffset_add_le_of_lt (fun b => Fintype.card (A b)) hlt
      have hq := (Fintype.equivFin (A q.1) q.2).isLt
      omega
  rcases p with ⟨b, x⟩
  rcases q with ⟨d, y⟩
  dsimp only at he hv
  subst d
  have hxy : x = y := (Fintype.equivFin (A b)).injective (Fin.ext (by omega))
  subst y
  rfl

/-- A bijective enumeration which keeps each label fibre contiguous. -/
def groupedEquiv : (Σ b, A b) ≃ Fin (∑ b, Fintype.card (A b)) :=
  Equiv.ofBijective (groupedIndex A)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨groupedIndex_injective A, by simp⟩)

theorem groupedEquiv_val (p : Σ b, A b) :
    (groupedEquiv A p).val = blockOffset (fun b => Fintype.card (A b)) p.1 +
      (Fintype.equivFin (A p.1) p.2).val := rfl

variable {α : Type uAlpha} [Fintype α] [DecidableEq β]

/-- Bounded label multiplicities admit a partition into equally populated
rows, with at most one occurrence of each label in each row. The cardinal
bound is the integer floor, so it applies also to empty rows and words. -/
theorem exists_balanced_rows (f : α → β) (w : ℕ) (hw : 0 < w)
    (hm : ∀ b, Fintype.card {a : α // f a = b} ≤ w) :
    ∃ row : α → Fin w,
      (∀ r, Set.InjOn f {a | row a = r}) ∧
      (∀ r, Fintype.card α / w ≤ Fintype.card {a : α // row a = r}) := by
  classical
  let B : β → Type _ := fun b => {a : α // f a = b}
  let n := ∑ b, Fintype.card (B b)
  let e : α ≃ Fin n := (Equiv.sigmaFiberEquiv f).symm.trans (groupedEquiv B)
  have hn : n = Fintype.card α := by
    calc
      n = Fintype.card (Σ b, B b) := by simp [n]
      _ = Fintype.card α := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  let row : α → Fin w := fun a => ⟨(e a).val % w, Nat.mod_lt _ hw⟩
  refine ⟨row, ?_, ?_⟩
  · intro r x hx y hy hlabel
    have hex : (e x).val = blockOffset (fun b => Fintype.card (B b)) (f x) +
        (Fintype.equivFin (B (f x)) ⟨x, rfl⟩).val := rfl
    have hey : (e y).val = blockOffset (fun b => Fintype.card (B b)) (f y) +
        (Fintype.equivFin (B (f y)) ⟨y, rfl⟩).val := rfl
    have hxp := (Fintype.equivFin (B (f x)) ⟨x, rfl⟩).isLt
    have hyp := (Fintype.equivFin (B (f y)) ⟨y, rfl⟩).isLt
    have hxm : Fintype.card (B (f x)) ≤ w := hm (f x)
    have hym : Fintype.card (B (f y)) ≤ w := hm (f y)
    have hoff : blockOffset (fun b => Fintype.card (B b)) (f x) =
        blockOffset (fun b => Fintype.card (B b)) (f y) := congrArg _ hlabel
    have hmod : (e x).val % w = (e y).val % w :=
      congrArg Fin.val (hx.trans hy.symm)
    apply e.injective
    apply Fin.ext
    exact eq_of_mod_eq_of_mem_interval
      (a := blockOffset (fun b => Fintype.card (B b)) (f x))
      (by omega) (by omega) (by omega) (by omega) hmod
  · intro r
    have hecard : Fintype.card {a : α // row a = r} =
        Fintype.card {i : Fin n // i.val % w = r.val} :=
      Fintype.card_congr (e.subtypeEquiv (fun a => by
        change (⟨(e a).val % w, Nat.mod_lt _ hw⟩ : Fin w) = r ↔ _
        exact Fin.ext_iff))
    rw [hecard, ← hn]
    exact card_mod_row_subtype_lower n w hw r

/-- Explicit finite-set form: the rows partition the positions. -/
theorem exists_balanced_row_finsets (f : α → β) (w : ℕ) (hw : 0 < w)
    (hm : ∀ b, Fintype.card {a : α // f a = b} ≤ w) :
    ∃ rows : Fin w → Finset α,
      (∀ a, ∃! r, a ∈ rows r) ∧
      (∀ r, Set.InjOn f (rows r)) ∧
      (∀ r, Fintype.card α / w ≤ (rows r).card) := by
  classical
  obtain ⟨row, hinj, hcard⟩ := exists_balanced_rows f w hw hm
  refine ⟨fun r => Finset.univ.filter fun a => row a = r, ?_, ?_, ?_⟩
  · intro a
    refine ⟨row a, by simp, ?_⟩
    intro r hr
    simpa using (Finset.mem_filter.mp hr).2.symm
  · intro r x hx y hy hxy
    exact hinj r (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy
  · intro r
    simpa only [Fintype.card_subtype] using hcard r

/-- Light positions in a word admit rows of size at least `M / 10`, once
their number is at least one tenth of `k` and every label has multiplicity at
most `w` with `M * w ≤ k`. -/
theorem exists_light_row_finsets (f : α → β) (M w k : ℕ) (hw : 0 < w)
    (hm : ∀ b, Fintype.card {a : α // f a = b} ≤ w)
    (hwidth : M * w ≤ k) (hlight : k ≤ 10 * Fintype.card α) :
    ∃ rows : Fin w → Finset α,
      (∀ a, ∃! r, a ∈ rows r) ∧
      (∀ r, Set.InjOn f (rows r)) ∧
      (∀ r, M / 10 ≤ (rows r).card) := by
  obtain ⟨rows, hpart, hinj, hcard⟩ := exists_balanced_row_finsets f w hw hm
  exact ⟨rows, hpart, hinj, fun r =>
    (div_ten_le_div_of_sandwich hw hwidth hlight).trans (hcard r)⟩

variable {ι : Type uIndex} [Fintype ι] [DecidableEq ι]

/-- Balance on each fibre of a row assignment implies balance on all positions.
The factor `q = 4` is the quarter-balance used in the outer coloring. -/
theorem row_balance_aggregate (row : α → ι) (p : α → Prop) [DecidablePred p]
    (q : ℕ)
    (hrow : ∀ r,
      (Finset.univ.filter (fun a => row a = r)).card ≤
        q * ((Finset.univ.filter (fun a => row a = r)).filter p).card) :
    Fintype.card α ≤ q * (Finset.univ.filter p).card := by
  classical
  have htotal :
      (∑ r : ι, (Finset.univ.filter (fun a : α => row a = r)).card) =
        Fintype.card α := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset α) (Finset.univ : Finset ι) row
  have hselected :
      (∑ r : ι, ((Finset.univ.filter (fun a : α => row a = r)).filter p).card) =
        (Finset.univ.filter p).card := by
    simpa [Finset.filter_filter, and_comm] using
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ.filter p) (Finset.univ : Finset ι) row
  calc
    Fintype.card α =
        ∑ r : ι, (Finset.univ.filter (fun a : α => row a = r)).card := htotal.symm
    _ ≤ ∑ r : ι,
        q * ((Finset.univ.filter (fun a : α => row a = r)).filter p).card :=
      Finset.sum_le_sum fun r _ => hrow r
    _ = q * (Finset.univ.filter p).card := by rw [← Finset.mul_sum, hselected]

/-- Explicit partition version of `row_balance_aggregate`. The only partition
hypothesis is unique membership; its disjointness and completeness are used. -/
theorem partition_balance_aggregate (rows : ι → Finset α)
    (hpart : ∀ a, ∃! r, a ∈ rows r) (p : α → Prop) [DecidablePred p]
    (q : ℕ) (hrow : ∀ r, (rows r).card ≤ q * ((rows r).filter p).card) :
    Fintype.card α ≤ q * (Finset.univ.filter p).card := by
  classical
  let row : α → ι := fun a => Classical.choose (hpart a).exists
  have hmem : ∀ a, a ∈ rows (row a) := fun a =>
    Classical.choose_spec (hpart a).exists
  have hfiber : ∀ r,
      Finset.univ.filter (fun a : α => row a = r) = rows r := by
    intro r
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ha
      rw [← ha]
      exact hmem a
    · intro ha
      exact (hpart a).unique (hmem a) ha
  apply row_balance_aggregate row p q
  intro r
  simpa only [hfiber r] using hrow r

end

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# A real lower bound for integer row sizes

The natural-number row bound `m / 10 ≤ n` implies a real lower bound with
an absolute loss of one, suitable for the exponential incidence estimates.
-/

namespace QuantitativeVanDerWaerden

/-- Losing one converts the floored row-size bound to a strict real bound. -/
theorem real_div_ten_sub_one_lt {m n : ℕ} (h : m / 10 ≤ n) :
    (m : ℝ) / 10 - 1 < (n : ℝ) := by
  have hnat : m ≤ 10 * n + 9 := by omega
  have hreal : (m : ℝ) ≤ 10 * (n : ℝ) + 9 := by exact_mod_cast hnat
  linarith

/-- The real row-size lower bound used in weighted incidence sums. -/
theorem real_div_ten_sub_one_le {m n : ℕ} (h : m / 10 ≤ n) :
    (m : ℝ) / 10 - 1 ≤ (n : ℝ) :=
  (real_div_ten_sub_one_lt h).le

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI


namespace QuantitativeVanDerWaerden

open scoped BigOperators

theorem outer_log_one_sub_lower {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) :
    -2 * z ≤ Real.log (1 - z) := by
  have hpos : 0 < 1 - z := by linarith
  have hinv : (1 - z)⁻¹ ≤ 1 + 2 * z := by
    rw [← one_div]
    apply (div_le_iff₀ hpos).2
    have hmul : 0 ≤ z * (1 - 2 * z) := mul_nonneg hz (by linarith)
    nlinarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  linarith

theorem outer_exp_neg_two_le_one_sub {z : ℝ} (hz : 0 ≤ z)
    (hzhalf : z ≤ 1 / 2) : Real.exp (-2 * z) ≤ 1 - z := by
  have h := Real.exp_le_exp.mpr (outer_log_one_sub_lower hz hzhalf)
  rwa [Real.exp_log (by linarith : 0 < 1 - z)] at h

theorem outer_exp_sum_le_product {I : Type uI} (s : Finset I) (z : I → ℝ)
    (hz : ∀ i ∈ s, 0 ≤ z i) (hzhalf : ∀ i ∈ s, z i ≤ 1 / 2) :
    Real.exp (-2 * ∑ i ∈ s, z i) ≤ ∏ i ∈ s, (1 - z i) := by
  classical
  revert hz hzhalf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    intro hz hzhalf
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have has : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    have hza := hz a (Finset.mem_insert_self a s)
    have hza' := hzhalf a (Finset.mem_insert_self a s)
    calc
      Real.exp (-2 * (z a + ∑ i ∈ s, z i)) =
          Real.exp (-2 * z a) * Real.exp (-2 * ∑ i ∈ s, z i) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ (1 - z a) * ∏ i ∈ s, (1 - z i) := by
        exact mul_le_mul (outer_exp_neg_two_le_one_sub hza hza')
          (ih (fun i hi => hz i (has i hi)) (fun i hi => hzhalf i (has i hi)))
          (Real.exp_pos _).le (by linarith)

/-- The numerical criterion used for each outer bad event. -/
theorem outer_local_criterion {I : Type uI} (s : Finset I) (z : I → ℝ) (l : ℝ)
    (hl : 100 ≤ l) (hz : ∀ i ∈ s, 0 ≤ z i)
    (hzhalf : ∀ i ∈ s, z i ≤ 1 / 2)
    (hsum : ∑ i ∈ s, z i ≤ l / 500) :
    2 * Real.exp (-l / 8) ≤ Real.exp (-l / 32) * ∏ i ∈ s, (1 - z i) := by
  have htwo : 2 ≤ Real.exp ((1 / 8 - (1 / 32 + 2 / 500)) * l) := by
    have h := Real.add_one_le_exp ((1 / 8 - (1 / 32 + 2 / 500)) * l)
    linarith
  have htail : 2 * Real.exp (-l / 8) ≤ Real.exp (-(1 / 32 + 2 / 500) * l) := by
    calc
      2 * Real.exp (-l / 8) ≤
          Real.exp ((1 / 8 - (1 / 32 + 2 / 500)) * l) * Real.exp (-l / 8) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (-(1 / 32 + 2 / 500) * l) := by
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    2 * Real.exp (-l / 8) ≤ Real.exp (-(1 / 32 + 2 / 500) * l) := htail
    _ ≤ Real.exp (-l / 32) * Real.exp (-2 * ∑ i ∈ s, z i) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    _ ≤ Real.exp (-l / 32) * ∏ i ∈ s, (1 - z i) :=
      mul_le_mul_of_nonneg_left (outer_exp_sum_le_product s z hz hzhalf)
        (Real.exp_pos _).le

theorem outer_weight_pos (l : ℝ) : 0 < Real.exp (-l / 32) := Real.exp_pos _

theorem outer_weight_lt_half {l : ℝ} (hl : 100 ≤ l) :
    Real.exp (-l / 32) < 1 / 2 := by
  have hpos := Real.exp_pos (-l / 32)
  have hlarge : 2 < Real.exp (l / 32) := by
    have h := Real.add_one_le_exp (l / 32)
    linarith
  have hmul : Real.exp (-l / 32) * Real.exp (l / 32) = 1 := by
    rw [← Real.exp_add]
    rw [show -l / 32 + l / 32 = 0 by ring]
    exact Real.exp_zero
  nlinarith

/-- Distinct tests are adjacent precisely when they share a label variable. -/
noncomputable def outerNeighbors {I : Type uI} {Label : Type uLabel} [Fintype I] [DecidableEq I]
    [DecidableEq Label] (support : I → Finset Label) (i : I) : Finset I :=
  Finset.univ.filter fun j => j ≠ i ∧ ¬ Disjoint (support i) (support j)

/-- A per-label incident bound gives the required per-test neighbor bound. -/
theorem outer_neighbor_weight_bound {I : Type uI} {Label : Type uLabel} [Fintype I] [DecidableEq I]
    [DecidableEq Label] (support : I → Finset Label) (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (B : ℝ)
    (hincident : ∀ b, ∑ j ∈ Finset.univ.filter (fun j => b ∈ support j), weight j ≤ B)
    (i : I) :
    ∑ j ∈ outerNeighbors support i, weight j ≤ (support i).card * B := by
  classical
  let n := outerNeighbors support i
  have hcover : ∀ j ∈ n, weight j ≤
      ∑ b ∈ support i, if b ∈ support j then weight j else 0 := by
    intro j hj
    have hnot : ¬ Disjoint (support i) (support j) :=
      (Finset.mem_filter.mp hj).2.2
    obtain ⟨b, hbi, hbj⟩ := Finset.not_disjoint_iff.mp hnot
    have hsingle := Finset.single_le_sum
      (f := fun b => if b ∈ support j then weight j else 0)
      (fun b _ => by split_ifs <;> first | exact hweight j | exact le_rfl) hbi
    simpa only [ite_eq_left hbj] using hsingle
  calc
    ∑ j ∈ n, weight j ≤ ∑ j ∈ n, ∑ b ∈ support i,
        if b ∈ support j then weight j else 0 := Finset.sum_le_sum hcover
    _ = ∑ b ∈ support i, ∑ j ∈ n,
        if b ∈ support j then weight j else 0 := Finset.sum_comm
    _ ≤ ∑ _b ∈ support i, B := by
      apply Finset.sum_le_sum
      intro b hb
      have hsub : n.filter (fun j => b ∈ support j) ⊆
          Finset.univ.filter (fun j => b ∈ support j) := by
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2⟩
      calc
        (∑ j ∈ n, if b ∈ support j then weight j else 0) =
            ∑ j ∈ n.filter (fun j => b ∈ support j), weight j := by
          rw [Finset.sum_filter]
        _ ≤ ∑ j ∈ Finset.univ.filter (fun j => b ∈ support j), weight j :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hweight j)
        _ ≤ B := hincident b
    _ = (support i).card * B := by simp

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI


namespace QuantitativeVanDerWaerden

open scoped BigOperators

theorem outer_weight_le_of_support_lower {n : ℕ} {L : ℝ} (hL : L ≤ (n : ℝ)) :
    Real.exp (-(n : ℝ) / 32) ≤ Real.exp (-L / 32) := by
  apply Real.exp_le_exp.mpr
  linarith

theorem outer_weight_le_of_half_length {n h : ℕ} (hsize : h ≤ 2 * n) :
    Real.exp (-(n : ℝ) / 32) ≤ Real.exp (-(h : ℝ) / 64) := by
  have hsize' : (h : ℝ) ≤ 2 * n := by exact_mod_cast hsize
  apply Real.exp_le_exp.mpr
  linarith

theorem outer_total_weight_bound {I : Type uI} {Label : Type uLabel} (s : Finset I)
    (support : I → Finset Label) (L : ℝ)
    (hsize : ∀ i ∈ s, L ≤ ((support i).card : ℝ)) :
    ∑ i ∈ s, Real.exp (-((support i).card : ℝ) / 32) ≤
      s.card * Real.exp (-L / 32) := by
  calc
    (∑ i ∈ s, Real.exp (-((support i).card : ℝ) / 32)) ≤
        ∑ _i ∈ s, Real.exp (-L / 32) :=
      Finset.sum_le_sum fun i hi => outer_weight_le_of_support_lower (hsize i hi)
    _ = s.card * Real.exp (-L / 32) := by simp

/-- The anchored count through one label gives the local incident-weight
bound, after grouping actual pattern indices by their return period. -/
theorem outer_local_incident_bound {I : Type uI} {Label : Type uLabel} [Fintype I] [DecidableEq I]
    [DecidableEq Label] (support : I → Finset Label) (period : I → ℕ)
    (periods : Finset ℕ) (countBound : ℕ → ℕ)
    (hperiod : ∀ i, period i ∈ periods)
    (hsize : ∀ i, period i ≤ 2 * (support i).card)
    (hcount : ∀ b h,
      (Finset.univ.filter (fun i => b ∈ support i ∧ period i = h)).card ≤ countBound h)
    (b : Label) :
    ∑ i ∈ Finset.univ.filter (fun i => b ∈ support i),
        Real.exp (-((support i).card : ℝ) / 32) ≤
      ∑ h ∈ periods, (countBound h : ℝ) * Real.exp (-(h : ℝ) / 64) := by
  classical
  let incident := Finset.univ.filter (fun i => b ∈ support i)
  have hmap : ∀ i ∈ incident, period i ∈ periods := fun i _ => hperiod i
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_le_sum
  intro h hh
  have hcard : (incident.filter (fun i => period i = h)).card ≤ countBound h := by
    simpa only [incident, Finset.filter_filter] using hcount b h
  calc
    (∑ i ∈ incident.filter (fun i => period i = h),
        Real.exp (-((support i).card : ℝ) / 32)) ≤
        ∑ _i ∈ incident.filter (fun i => period i = h), Real.exp (-(h : ℝ) / 64) := by
      apply Finset.sum_le_sum
      intro i hi
      have hih : period i = h := (Finset.mem_filter.mp hi).2
      simpa only [hih] using outer_weight_le_of_half_length (hsize i)
    _ = ((incident.filter (fun i => period i = h)).card : ℝ) *
        Real.exp (-(h : ℝ) / 64) := by simp
    _ ≤ (countBound h : ℝ) * Real.exp (-(h : ℝ) / 64) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.exp_pos _).le

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# The first family of outer-coloring tests

For each full word with sufficiently many light positions, choose the proved
cyclic row decomposition of its light positions. Its tests are the actual sets
of distinct labels occurring in these rows. All choices depend on the word and
the parameters, before a coloring is chosen.
-/


namespace QuantitativeVanDerWaerden.OuterWordTests

open scoped BigOperators

variable {Label : Type uLabel} [Fintype Label] [DecidableEq Label] {k : ℕ}

/-- Full-word multiplicity of a label. -/
def multiplicity (word : Fin k → Label) (b : Label) : ℕ :=
  (Finset.univ.filter fun i => word i = b).card

/-- Lightness is measured in the full word, before restriction to light positions. -/
def lightPositions (M : ℕ) (word : Fin k → Label) : Finset (Fin k) :=
  Finset.univ.filter fun i => M * multiplicity word (word i) ≤ k

omit [Fintype Label] in
@[simp] theorem mem_lightPositions (M : ℕ) (word : Fin k → Label) (i : Fin k) :
    i ∈ lightPositions M word ↔ M * multiplicity word (word i) ≤ k := by
  simp [lightPositions]

abbrev LightPosition (M : ℕ) (word : Fin k → Label) := ↥(lightPositions M word)

/-- Each restricted label fibre is bounded by the full-word light multiplicity. -/
theorem light_fiber_card_le {Label : Type uLabel} [Fintype Label] [DecidableEq Label]
    {k : ℕ}
    (M : ℕ) (hM : 0 < M) (word : Fin k → Label)
    (b : Label) :
    Fintype.card {i : LightPosition M word // word i = b} ≤ k / M := by
  classical
  by_cases hb : Nonempty {i : LightPosition M word // word i = b}
  · obtain ⟨i⟩ := hb
    have hlight : M * multiplicity word b ≤ k := by
      have hi := (mem_lightPositions M word i.1).mp i.1.property
      simpa only [i.property] using hi
    have hcap : multiplicity word b ≤ k / M :=
      (Nat.le_div_iff_mul_le hM).mpr (by simpa only [Nat.mul_comm] using hlight)
    let emb : {i : LightPosition M word // word i = b} →
        {i : Fin k // word i = b} := fun i => ⟨i.1, i.2⟩
    have hemb : Function.Injective emb := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {i : Fin k // word i = b} => z.val) hxy
    have hcard := Fintype.card_le_of_injective emb hemb
    have hcard' : Fintype.card {i : LightPosition M word // word i = b} ≤
        multiplicity word b := by simpa only [Fintype.card_subtype, multiplicity] using hcard
    exact hcard'.trans hcap
  · have : IsEmpty {i : LightPosition M word // word i = b} :=
      not_nonempty_iff.mp hb
    simp

/-- The actual row decomposition exists for each eligible full word. -/
theorem word_rows_exist (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (word : Fin k → Label) (heligible : k ≤ 10 * (lightPositions M word).card) :
    ∃ rows : Fin (k / M) → Finset (LightPosition M word),
      (∀ i, ∃! r, i ∈ rows r) ∧
      (∀ r, Set.InjOn (fun i : LightPosition M word => word i) (rows r)) ∧
      (∀ r, M / 10 ≤ (rows r).card) := by
  have hw : 0 < k / M := Nat.div_pos hMk hM
  have hwidth : M * (k / M) ≤ k := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self k M
  exact exists_light_row_finsets (fun i : LightPosition M word => word i)
    M (k / M) k hw (light_fiber_card_le M hM word) hwidth
    (by simpa using heligible)

noncomputable def wordRows (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (word : Fin k → Label) (heligible : k ≤ 10 * (lightPositions M word).card) :
    Fin (k / M) → Finset (LightPosition M word) :=
  Classical.choose (word_rows_exist M hM hMk word heligible)

theorem wordRows_spec (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (word : Fin k → Label) (heligible : k ≤ 10 * (lightPositions M word).card) :
    (∀ i, ∃! r, i ∈ wordRows M hM hMk word heligible r) ∧
    (∀ r, Set.InjOn (fun i : LightPosition M word => word i)
      (wordRows M hM hMk word heligible r)) ∧
    (∀ r, M / 10 ≤ (wordRows M hM hMk word heligible r).card) :=
  Classical.choose_spec (word_rows_exist M hM hMk word heligible)

def eligibleWords (M : ℕ) (words : Finset (Fin k → Label)) : Finset (Fin k → Label) :=
  words.filter fun word => k ≤ 10 * (lightPositions M word).card

abbrev TestIndex (M : ℕ) (words : Finset (Fin k → Label)) :=
  ↥(eligibleWords M words) × Fin (k / M)

omit [Fintype Label] in
theorem testIndex_card_le (M : ℕ) (words : Finset (Fin k → Label)) :
    Fintype.card (TestIndex M words) ≤ k * words.card := by
  classical
  calc
    Fintype.card (TestIndex M words) = (eligibleWords M words).card * (k / M) := by
      simp [TestIndex]
    _ ≤ words.card * k := Nat.mul_le_mul
      (Finset.card_le_card (Finset.filter_subset _ _)) (Nat.div_le_self k M)
    _ = k * words.card := Nat.mul_comm _ _

/-- Literal support of an indexed first-family row test. -/
noncomputable def support (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (words : Finset (Fin k → Label)) (i : TestIndex M words) : Finset Label :=
  (wordRows M hM hMk i.1.val (Finset.mem_filter.mp i.1.property).2 i.2).image
    (fun p : LightPosition M i.1.val => i.1.val p)

theorem support_card_eq (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (words : Finset (Fin k → Label)) (i : TestIndex M words) :
    (support M hM hMk words i).card =
      (wordRows M hM hMk i.1.val (Finset.mem_filter.mp i.1.property).2 i.2).card :=
  Finset.card_image_of_injOn
    ((wordRows_spec M hM hMk i.1.val (Finset.mem_filter.mp i.1.property).2).2.1 i.2)

theorem support_card_lower (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (words : Finset (Fin k → Label)) (i : TestIndex M words) :
    M / 10 ≤ (support M hM hMk words i).card := by
  rw [support_card_eq]
  exact (wordRows_spec M hM hMk i.1.val (Finset.mem_filter.mp i.1.property).2).2.2 i.2

theorem support_card_real_lower (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (words : Finset (Fin k → Label)) (i : TestIndex M words) :
    (M : ℝ) / 10 - 1 ≤ ((support M hM hMk words i).card : ℝ) :=
  real_div_ten_sub_one_le (support_card_lower M hM hMk words i)

omit [Fintype Label] in
/-- Restricting to the subtype of light positions does not change selected counts. -/
theorem light_selected_card (M : ℕ) (word : Fin k → Label) (p : Fin k → Prop)
    [DecidablePred p] :
    (Finset.univ.filter (fun i : LightPosition M word => p i)).card =
      ((lightPositions M word).filter p).card := by
  classical
  have himage :
      (Finset.univ.filter (fun i : LightPosition M word => p i)).image Subtype.val =
        (lightPositions M word).filter p := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.property, ha⟩
    · rintro ⟨hi, hp⟩
      exact ⟨⟨i, hi⟩, hp, rfl⟩
  calc
    (Finset.univ.filter (fun i : LightPosition M word => p i)).card =
        ((Finset.univ.filter (fun i : LightPosition M word => p i)).image
          Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = ((lightPositions M word).filter p).card := congrArg Finset.card himage

/-- Balancing every constructed support balances the light positions of each
eligible input word, with its original position multiplicities retained. -/
theorem supports_balance_words (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (words : Finset (Fin k → Label)) (color : Label → Bool)
    (hbalance : ∀ i b, (support M hM hMk words i).card ≤
      4 * ((support M hM hMk words i).filter fun a => color a = b).card) :
    ∀ word ∈ words, k ≤ 10 * (lightPositions M word).card → ∀ b,
      (lightPositions M word).card ≤
        4 * ((lightPositions M word).filter fun i => color (word i) = b).card := by
  classical
  intro word hword heligible b
  let rows := wordRows M hM hMk word heligible
  have hrows := wordRows_spec M hM hMk word heligible
  have hrow : ∀ r, (rows r).card ≤
      4 * ((rows r).filter fun i : LightPosition M word => color (word i) = b).card := by
    intro r
    let i : TestIndex M words :=
      (⟨word, Finset.mem_filter.mpr ⟨hword, heligible⟩⟩, r)
    have hb := hbalance i b
    change ((rows r).image (fun p : LightPosition M word => word p)).card ≤
      4 * (((rows r).image (fun p : LightPosition M word => word p)).filter
        fun a => color a = b).card at hb
    have hinj : Set.InjOn (fun p : LightPosition M word => word p) (rows r) :=
      hrows.2.1 r
    have hinj' : Set.InjOn (fun p : LightPosition M word => word p)
        ((rows r).filter fun p : LightPosition M word => color (word p) = b) := by
      intro x hx y hy hxy
      exact hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy
    rw [Finset.card_image_of_injOn hinj, Finset.filter_image,
      Finset.card_image_of_injOn hinj'] at hb
    exact hb
  have hall := partition_balance_aggregate rows hrows.1
    (fun i : LightPosition M word => color (word i) = b) 4 hrow
  rw [Fintype.card_coe, light_selected_card M word (fun i => color (word i) = b)] at hall
  exact hall

/-- A first-family label-incident sum is bounded using the total test count.
The row index is retained even when supports happen to coincide. -/
theorem incident_weight_le (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (words : Finset (Fin k → Label)) (b : Label) :
    (∑ i ∈ Finset.univ.filter (fun i : TestIndex M words => b ∈ support M hM hMk words i),
        Real.exp (-((support M hM hMk words i).card : ℝ) / 32)) ≤
      ((k * words.card : ℕ) : ℝ) * Real.exp (-((M : ℝ) / 10 - 1) / 32) := by
  classical
  let incident := Finset.univ.filter
    (fun i : TestIndex M words => b ∈ support M hM hMk words i)
  have hcount : incident.card ≤ k * words.card :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans
      (by simpa using testIndex_card_le M words)
  calc
    (∑ i ∈ incident, Real.exp (-((support M hM hMk words i).card : ℝ) / 32)) ≤
        (incident.card : ℝ) * Real.exp (-((M : ℝ) / 10 - 1) / 32) :=
      outer_total_weight_bound incident (support M hM hMk words) _
        (fun i _ => support_card_real_lower M hM hMk words i)
    _ ≤ ((k * words.card : ℕ) : ℝ) * Real.exp (-((M : ℝ) / 10 - 1) / 32) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (Real.exp_pos _).le

end QuantitativeVanDerWaerden.OuterWordTests

end OAI
end
end

section
section
namespace OAI

/-! The exact two balancing properties consumed by the geometric dichotomy.
The existence proof, including actual pattern counts, is in
`EligibleOuterColoring`. -/

namespace QuantitativeVanDerWaerden

/-- The two balancing properties of the selected outer label coloring. -/
structure OuterBalanced {D k : ℕ} (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh)
    (eta : ℝ) (lambda M : ℕ)
    (words : Finset (Fin k → FullLabel D (Fin n) A.Label)) (periods : Finset ℕ)
    (color : FullLabel D (Fin n) A.Label → Bool) : Prop where
  global_words : ∀ word ∈ words,
    k ≤ 10 * (OuterWordTests.lightPositions M word).card → ∀ b,
      (OuterWordTests.lightPositions M word).card ≤
        4 * ((OuterWordTests.lightPositions M word).filter
          fun j => color (word j) = b).card
  eligible_patterns : ∀ h ∈ periods, ∀ t : Fin D → Fin h,
    ∀ R : AnchoredPatterns.Realization D,
      AnchoredPatterns.EligibleRealization n hn A eta lambda t R → ∀ b,
        (AnchoredPatterns.regularPositions eta R lambda t).card ≤
          4 * ((AnchoredPatterns.regularPositions eta R lambda t).filter
            fun z => color (AnchoredPatterns.fullLabel n hn A R lambda t z) = b).card

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

/-- A concrete outer coloring, with its counted family of actual cyclic words.
The family is retained so that its membership proof can be used directly by the
subsequent progression dichotomy. -/
structure OuterChoice {k : ℕ} (s : Data k) (hk : 3 ≤ k) where
  words : Finset (Fin k → Label s hk)
  color : Label s hk → Bool
  word_mem : ∀ ad : Group s × Group s, fullLabelWord s hk ad ∈ words
  card_le : words.card ≤
    (16 * (3 * k ^ 2 *
      (uniformCount k + Fintype.card (mesh s hk).Label) + 1) ^ 6) ^
      (2 * dimension k)
  balanced : OuterBalanced (uniformCount k) (uniformCount_pos hk) (mesh s hk)
    (1 / (1000 * (dimension k : ℝ))) (lambda k) (cutoff k) words
    (Finset.Ioc (dimension k ^ 2) (2 * cutoff k)) color

end QuantitativeVanDerWaerden.ConstructionModel

end

end OAI
end
end

section
section
namespace OAI

noncomputable section


namespace QuantitativeVanDerWaerden

open scoped BigOperators

/-- A real affine form in `e` parameters. -/
structure AffineForm (e : ℕ) where
  linear : Fin e → ℝ
  constant : ℝ

def AffineForm.eval {e : ℕ} (f : AffineForm e) (x : Fin e → ℝ) : ℝ :=
  (∑ j, f.linear j * x j) + f.constant

def signVector {e s : ℕ} (forms : Fin s → AffineForm e) (x : Fin e → ℝ) :
    Fin s → Fin 3 := fun i => ternarySign ((forms i).eval x)

/-- Realized patterns on any specified parameter subset. -/
def realizedSigns {e s : ℕ} (forms : Fin s → AffineForm e)
    (D : Set (Fin e → ℝ)) : Finset (Fin s → Fin 3) := by
  classical
  exact Finset.univ.filter (fun p => ∃ x ∈ D, signVector forms x = p)

@[simp] theorem mem_realizedSigns {e s : ℕ} (forms : Fin s → AffineForm e)
    (D : Set (Fin e → ℝ)) (p : Fin s → Fin 3) :
    p ∈ realizedSigns forms D ↔ ∃ x ∈ D, signVector forms x = p := by
  classical
  simp [realizedSigns]

namespace Arrangement

def linearValue {d : ℕ} (v x : Fin d → ℝ) : ℝ := ∑ j, v j * x j

private theorem linearValue_smul {d : ℕ} (c : ℝ) (v x : Fin d → ℝ) :
    linearValue (c • v) x = c * linearValue v x := by
  simp [linearValue, Finset.mul_sum, mul_assoc]

private theorem linearValue_sum {ι : Type uIndex} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℝ) (x : Fin d → ℝ) :
    linearValue (∑ i, v i) x = ∑ i, linearValue (v i) x := by
  simp only [linearValue, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

private theorem linearValue_neg {d : ℕ} (v x : Fin d → ℝ) :
    linearValue v (-x) = -linearValue v x := by
  simp [linearValue, Finset.sum_neg_distrib]

section StrictSupports

variable {ι : Type uIndex} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- All strict homogeneous threshold supports of the fixed coefficient vectors. -/
def thresholdFamily (v : ι → Fin d → ℝ) : Finset (Finset ι) := by
  classical
  exact Finset.univ.filter (fun t => ∃ x, ∀ i, i ∈ t ↔ 0 < linearValue (v i) x)

@[simp] theorem mem_thresholdFamily {ι : Type uIndex} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (v : ι → Fin d → ℝ) (t : Finset ι) :
    t ∈ thresholdFamily v ↔ ∃ x, ∀ i, i ∈ t ↔ 0 < linearValue (v i) x := by
  classical
  simp [thresholdFamily]

/-- Shattering realizes the positive support of any coefficients on the set. -/
private theorem separates_coefficients (v : ι → Fin d → ℝ) (s : Finset ι)
    (hs : (thresholdFamily v).Shatters s) (c : s → ℝ) :
    ∃ x : Fin d → ℝ, ∀ i : s, 0 < linearValue (v i) x ↔ 0 < c i := by
  classical
  let t := s.filter (fun i => ∃ hi : i ∈ s, 0 < c ⟨i, hi⟩)
  have hts : t ⊆ s := Finset.filter_subset _ _
  obtain ⟨u, hu, hsu⟩ := hs hts
  obtain ⟨x, hx⟩ := (mem_thresholdFamily v u).mp hu
  refine ⟨x, fun i => ?_⟩
  have hi : (i : ι) ∈ u ↔ (i : ι) ∈ t := by
    have h := congrArg (fun a : Finset ι => (i : ι) ∈ a) hsu
    simpa only [Finset.mem_inter, i.property, true_and] using (Iff.of_eq h)
  rw [← hx (i : ι), hi]
  simp [t]

/-- A vanishing linear combination has no positive coefficient: choose
its own positive support, making every scalar product nonnegative. -/
private theorem coefficients_nonpos (v : ι → Fin d → ℝ) (s : Finset ι)
    (hs : (thresholdFamily v).Shatters s) (c : s → ℝ)
    (hc : ∑ i : s, c i • v i = 0) : ∀ i, c i ≤ 0 := by
  classical
  obtain ⟨x, hx⟩ := separates_coefficients v s hs c
  have hsum : (∑ i : s, c i * linearValue (v i) x) = 0 := by
    calc
      _ = linearValue (∑ i : s, c i • v i) x := by
        rw [linearValue_sum]
        exact Finset.sum_congr rfl (fun i _ => (linearValue_smul (c i) (v i) x).symm)
      _ = 0 := by rw [hc]; simp [linearValue]
  have hnonneg (i : s) : 0 ≤ c i * linearValue (v i) x := by
    by_cases hi : 0 < c i
    · exact mul_nonneg hi.le ((hx i).mpr hi).le
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hi)
        (le_of_not_gt (fun h => hi ((hx i).mp h)))
  intro i
  by_contra hi
  have hcpos : 0 < c i := lt_of_not_ge hi
  have hterm : c i * linearValue (v i) x ≤ 0 := by
    calc
      _ ≤ ∑ j : s, c j * linearValue (v j) x :=
        Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
      _ = 0 := hsum
  exact (not_lt_of_ge hterm) (mul_pos hcpos ((hx i).mpr hcpos))

/-- Every shattered coefficient subfamily is genuinely linearly independent. -/
theorem shatters_linearIndependent (v : ι → Fin d → ℝ) (s : Finset ι)
    (hs : (thresholdFamily v).Shatters s) :
    LinearIndependent ℝ (fun i : s => v i) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hnonpos := coefficients_nonpos v s hs c hc i
  have hneg : (∑ j : s, (-c j) • v j) = 0 := by
    simp only [neg_smul, Finset.sum_neg_distrib, hc, neg_zero]
  have hnonneg := coefficients_nonpos v s hs (fun j => -c j) hneg i
  linarith

theorem shatters_card_le (v : ι → Fin d → ℝ) (s : Finset ι)
    (hs : (thresholdFamily v).Shatters s) : s.card ≤ d := by
  simpa only [Fintype.card_coe, Module.finrank_fin_fun] using
    (shatters_linearIndependent v s hs).fintype_card_le_finrank

theorem thresholdFamily_vcDim_le (v : ι → Fin d → ℝ) :
    (thresholdFamily v).vcDim ≤ d := by
  classical
  apply Finset.sup_le
  intro s hs
  exact shatters_card_le v s (Finset.mem_shatterer.mp hs)

/-- Sauer--Shelah, with the dimension premise proved above, gives a
uniform polynomial bound for all strict homogeneous supports. -/
theorem card_thresholdFamily_le (v : ι → Fin d → ℝ) :
    (thresholdFamily v).card ≤ (d + 1) * (Fintype.card ι + 1) ^ d := by
  classical
  calc
    (thresholdFamily v).card ≤ (thresholdFamily v).shatterer.card :=
      Finset.card_le_card_shatterer _
    _ ≤ ∑ k ∈ Finset.Iic (thresholdFamily v).vcDim, (Fintype.card ι).choose k :=
      Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ Finset.Iic d, (Fintype.card ι).choose k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hk).trans (thresholdFamily_vcDim_le v))
      · intro k _ _
        exact Nat.zero_le _
    _ ≤ ∑ _k ∈ Finset.Iic d, (Fintype.card ι + 1) ^ d := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        (Fintype.card ι).choose k ≤ (Fintype.card ι) ^ k := Nat.choose_le_pow _ _
        _ ≤ (Fintype.card ι + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ _) _
        _ ≤ (Fintype.card ι + 1) ^ d :=
          Nat.pow_le_pow_right (Nat.succ_pos _) (Finset.mem_Iic.mp hk)
    _ = (d + 1) * (Fintype.card ι + 1) ^ d := by simp

end StrictSupports

/-- The constant coefficient is the first coordinate of the homogeneous lift. -/
def liftedCoefficients {e : ℕ} (f : AffineForm e) : Fin (e + 1) → ℝ :=
  Fin.cons f.constant f.linear

def liftedPoint {e : ℕ} (x : Fin e → ℝ) : Fin (e + 1) → ℝ := Fin.cons 1 x

theorem linearValue_lift {e : ℕ} (f : AffineForm e) (x : Fin e → ℝ) :
    linearValue (liftedCoefficients f) (liftedPoint x) = f.eval x := by
  simp [linearValue, liftedCoefficients, liftedPoint, AffineForm.eval,
    Fin.sum_univ_succ, add_comm]

def signEncoding {s : ℕ} (p : Fin s → Fin 3) : Finset (Fin s) × Finset (Fin s) :=
  (Finset.univ.filter (fun i => p i = 2), Finset.univ.filter (fun i => p i = 0))

private theorem fin_three_ext {a b : Fin 3}
    (hzero : a = 0 ↔ b = 0) (htwo : a = 2 ↔ b = 2) : a = b := by
  fin_cases a <;> fin_cases b <;> simp_all

theorem signEncoding_injective {s : ℕ} : Function.Injective (@signEncoding s) := by
  intro p q hpq
  funext i
  apply fin_three_ext
  · have h := congrArg (fun a : Finset (Fin s) × Finset (Fin s) => i ∈ a.2) hpq
    simpa [signEncoding] using (Iff.of_eq h)
  · have h := congrArg (fun a : Finset (Fin s) × Finset (Fin s) => i ∈ a.1) hpq
    simpa [signEncoding] using (Iff.of_eq h)

theorem signVector_encoding_mem {e s : ℕ} (forms : Fin s → AffineForm e)
    (x : Fin e → ℝ) :
    signEncoding (signVector forms x) ∈
      (thresholdFamily (fun i => liftedCoefficients (forms i))).product
        (thresholdFamily (fun i => liftedCoefficients (forms i))) := by
  classical
  apply Finset.mem_product.mpr
  constructor
  · apply (mem_thresholdFamily _ _).mpr
    refine ⟨liftedPoint x, fun i => ?_⟩
    simp [signEncoding, signVector, linearValue_lift]
  · apply (mem_thresholdFamily _ _).mpr
    refine ⟨-liftedPoint x, fun i => ?_⟩
    simp [signEncoding, signVector, linearValue_neg, linearValue_lift]

end Arrangement

/-- Polynomial arrangement bound, including zero signs and arbitrary
restrictions of the parameter domain. Its degree is independent of `s`. -/
theorem card_realizedSigns_le {e s : ℕ} (forms : Fin s → AffineForm e)
    (D : Set (Fin e → ℝ)) :
    (realizedSigns forms D).card ≤ (e + 2) ^ 2 * (s + 1) ^ (2 * (e + 1)) := by
  classical
  let v := fun i => Arrangement.liftedCoefficients (forms i)
  have hcard : (realizedSigns forms D).card ≤
      (Arrangement.thresholdFamily v).card * (Arrangement.thresholdFamily v).card := by
    rw [← Finset.card_product]
    apply Finset.card_le_card_of_injOn Arrangement.signEncoding
    · intro p hp
      obtain ⟨x, _, rfl⟩ := (mem_realizedSigns forms D p).mp hp
      exact Arrangement.signVector_encoding_mem forms x
    · exact Arrangement.signEncoding_injective.injOn
  have hbound : (Arrangement.thresholdFamily v).card ≤ (e + 2) * (s + 1) ^ (e + 1) := by
    simpa only [Fintype.card_fin, Nat.add_assoc] using Arrangement.card_thresholdFamily_le v
  calc
    _ ≤ ((e + 2) * (s + 1) ^ (e + 1)) * ((e + 2) * (s + 1) ^ (e + 1)) :=
      hcard.trans (Nat.mul_le_mul hbound hbound)
    _ = (e + 2) ^ 2 * (s + 1) ^ (2 * (e + 1)) := by
      rw [two_mul, pow_add]
      ring

end QuantitativeVanDerWaerden

end

end OAI
end
end

section
section
namespace OAI

/-!
# Exact finite output families determined by affine comparisons

The output type may be infinite, for example an integer-valued floor word.
One representative is selected for each realized ternary sign vector. The
factorization hypothesis then proves that this finite image is exactly the
actual output image on the specified parameter domain. This proves finiteness
and a cardinality bound without assuming either conclusion about the outputs.
-/


namespace QuantitativeVanDerWaerden

theorem finite_outputs_of_comparisons {e s : ℕ} {α : Type uAlpha}
    (forms : Fin s → AffineForm e) (domain : Set (Fin e → ℝ))
    (out : (Fin e → ℝ) → α)
    (hfactor : ∀ x ∈ domain, ∀ y ∈ domain,
      signVector forms x = signVector forms y → out x = out y) :
    ∃ S : Finset α, (∀ w, w ∈ S ↔ ∃ x ∈ domain, out x = w) ∧
      S.card ≤ (e + 2) ^ 2 * (s + 1) ^ (2 * (e + 1)) := by
  classical
  let signs := realizedSigns forms domain
  have hrep : ∀ σ : signs, ∃ x ∈ domain, signVector forms x = σ.val := by
    intro σ
    exact (mem_realizedSigns forms domain σ.val).mp σ.property
  choose point hpoint hsign using hrep
  let outputs : Finset α := signs.attach.image (fun σ => out (point σ))
  refine ⟨outputs, ?_, ?_⟩
  · intro w
    constructor
    · intro hw
      change w ∈ signs.attach.image (fun σ => out (point σ)) at hw
      obtain ⟨σ, _, heq⟩ := Finset.mem_image.mp hw
      exact ⟨point σ, hpoint σ, heq⟩
    · rintro ⟨x, hx, rfl⟩
      let σ : signs := ⟨signVector forms x,
        (mem_realizedSigns forms domain _).mpr ⟨x, hx, rfl⟩⟩
      change out x ∈ signs.attach.image (fun σ => out (point σ))
      refine Finset.mem_image.mpr ⟨σ, Finset.mem_attach _ _, ?_⟩
      exact hfactor (point σ) (hpoint σ) x hx (hsign σ)
  · calc
      outputs.card ≤ signs.attach.card := Finset.card_image_le
      _ = signs.card := Finset.card_attach
      _ ≤ (e + 2) ^ 2 * (s + 1) ^ (2 * (e + 1)) :=
        card_realizedSigns_le forms domain

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI


namespace QuantitativeVanDerWaerden

/-- Decode two independent coordinate systems without identifying their scalar
output types. This is also the global full-word product estimate. -/
theorem card_decoded_twoSystems_le {D B : ℕ} {α : Type uAlpha} {β : Type uBeta} {Word : Type uWord}
    [DecidableEq Word] (firstS : Fin D → Finset α) (secondS : Fin D → Finset β)
    (decode : ((Fin D → α) × (Fin D → β)) → Word)
    (hfirst : ∀ i, (firstS i).card ≤ B) (hsecond : ∀ i, (secondS i).card ≤ B) :
    (((coordinateFamily firstS).product (coordinateFamily secondS)).image decode).card ≤
      B ^ (2 * D) := by
  classical
  calc
    _ ≤ ((coordinateFamily firstS).product (coordinateFamily secondS)).card :=
      Finset.card_image_le
    _ = (coordinateFamily firstS).card * (coordinateFamily secondS).card :=
      Finset.card_product _ _
    _ ≤ B ^ D * B ^ D := Nat.mul_le_mul
      (card_coordinateFamily_le firstS hfirst)
      (card_coordinateFamily_le secondS hsecond)
    _ = B ^ (2 * D) := by rw [two_mul, pow_add]

/-- Literal `(step vector, recorded word)` incidences, retaining the step vector
even when two different steps yield the same word. The two scalar systems have
their actual different output types. -/
noncomputable def anchoredIncidences {D h : ℕ} {U : Type uU} {V : Type uV}
    (firstS : (Fin D → Fin h) → Fin h → Fin D → Finset (Fin h → U))
    (secondS : (Fin D → Fin h) → Fin h → Fin D → Finset (Fin h → Option V)) :
    Finset ((Fin D → Fin h) × (Fin h → Option (FullLabel D U V))) := by
  classical
  exact Finset.univ.biUnion fun t => Finset.univ.biUnion fun z =>
    ((coordinateFamily (firstS t z)).product (coordinateFamily (secondS t z))).image
      (fun p => (t, assembleWord p.1 p.2))

theorem mem_anchoredIncidences_of_mem {D h : ℕ} {U : Type uU} {V : Type uV}
    (firstS : (Fin D → Fin h) → Fin h → Fin D → Finset (Fin h → U))
    (secondS : (Fin D → Fin h) → Fin h → Fin D → Finset (Fin h → Option V))
    (t : Fin D → Fin h) (z : Fin h)
    (first : Fin D → Fin h → U) (second : Fin D → Fin h → Option V)
    (hfirst : ∀ i, first i ∈ firstS t z i)
    (hsecond : ∀ i, second i ∈ secondS t z i) :
    (t, assembleWord first second) ∈ anchoredIncidences firstS secondS := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨t, Finset.mem_univ _, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨z, Finset.mem_univ _, Finset.mem_image.mpr ?_⟩
  refine ⟨(first, second), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
  · exact Fintype.mem_piFinset.mpr hfirst
  · exact Fintype.mem_piFinset.mpr hsecond

theorem card_anchoredIncidences_le {D h B : ℕ} {U : Type uU} {V : Type uV}
    (firstS : (Fin D → Fin h) → Fin h → Fin D → Finset (Fin h → U))
    (secondS : (Fin D → Fin h) → Fin h → Fin D → Finset (Fin h → Option V))
    (hfirst : ∀ t z i, (firstS t z i).card ≤ B)
    (hsecond : ∀ t z i, (secondS t z i).card ≤ B) :
    (anchoredIncidences firstS secondS).card ≤ h ^ (D + 1) * B ^ (2 * D) := by
  classical
  unfold anchoredIncidences
  calc
    _ ≤ (Finset.univ : Finset (Fin D → Fin h)).card * (h * B ^ (2 * D)) := by
      apply Finset.card_biUnion_le_card_mul
      intro t _
      calc
        _ ≤ (Finset.univ : Finset (Fin h)).card * B ^ (2 * D) := by
          apply Finset.card_biUnion_le_card_mul
          intro z _
          exact card_decoded_twoSystems_le (firstS t z) (secondS t z)
            (fun p => (t, assembleWord p.1 p.2)) (hfirst t z) (hsecond t z)
        _ = h * B ^ (2 * D) := by simp
    _ = h ^ (D + 1) * B ^ (2 * D) := by
      simp [pow_succ, Nat.mul_assoc]

theorem card_anchoredIncidences_polynomial_le {D h : ℕ} {U : Type uU} {V : Type uV}
    (hD : 0 < D) (hh : 0 < h)
    (firstS : (Fin D → Fin h) → Fin h → Fin D → Finset (Fin h → U))
    (secondS : (Fin D → Fin h) → Fin h → Fin D → Finset (Fin h → Option V))
    (hfirst : ∀ t z i, (firstS t z i).card ≤ 16 * (16004 * D * h + 1) ^ 6)
    (hsecond : ∀ t z i, (secondS t z i).card ≤ 16 * (16004 * D * h + 1) ^ 6) :
    (anchoredIncidences firstS secondS).card ≤ (16005 * D * h) ^ (14 * D) :=
  (card_anchoredIncidences_le firstS secondS hfirst hsecond).trans
    (anchored_polynomial_estimate D h hD hh)

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI


namespace QuantitativeVanDerWaerden

/-- Literal half-open cells on a single fundamental interval. A centered
partition is represented by translating both its endpoints by `1/2`. -/
structure CirclePartition (Label : Type uLabel) where
  left : Label → ℝ
  right : Label → ℝ
  left_nonneg : ∀ l, 0 ≤ left l
  left_lt_right : ∀ l, left l < right l
  right_le_one : ∀ l, right l ≤ 1
  covers : ∀ x ∈ Set.Ico (0 : ℝ) 1, ∃! l, x ∈ Set.Ico (left l) (right l)

namespace CirclePartition

noncomputable section

variable {Label : Type uLabel} (P : CirclePartition Label)

def label (x : ℝ) : Label :=
  Classical.choose ((P.covers (Int.fract x)
    ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩).exists)

theorem label_mem (x : ℝ) :
    Int.fract x ∈ Set.Ico (P.left (P.label x)) (P.right (P.label x)) :=
  Classical.choose_spec ((P.covers (Int.fract x)
    ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩).exists)

theorem label_eq_iff (x : ℝ) (l : Label) :
    P.label x = l ↔ Int.fract x ∈ Set.Ico (P.left l) (P.right l) := by
  constructor
  · rintro rfl
    exact P.label_mem x
  · intro h
    exact (P.covers (Int.fract x)
      ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩).unique (P.label_mem x) h

theorem label_eq_of_mem (x : ℝ) (l : Label)
    (h : Int.fract x ∈ Set.Ico (P.left l) (P.right l)) : P.label x = l :=
  (P.label_eq_iff x l).mpr h

theorem label_eq_of_fract_eq {x y : ℝ} (h : Int.fract x = Int.fract y) :
    P.label x = P.label y := by
  apply P.label_eq_of_mem
  rw [h]
  exact P.label_mem y

theorem label_eq_of_sub_int {x y : ℝ} (z : ℤ) (h : x - y = (z : ℝ)) :
    P.label x = P.label y :=
  P.label_eq_of_fract_eq (Int.fract_eq_fract.mpr ⟨z, h⟩)

theorem label_add_int (x : ℝ) (z : ℤ) : P.label (x + z) = P.label x :=
  P.label_eq_of_fract_eq (Int.fract_add_intCast x z)

theorem label_sub_int (x : ℝ) (z : ℤ) : P.label (x - z) = P.label x :=
  P.label_eq_of_fract_eq (Int.fract_sub_intCast x z)

/-- Membership in one lifted half-open interval already determines the
periodic label; the integer part need not be known in advance. -/
theorem label_eq_of_lifted_mem (x : ℝ) (z : ℤ) (l : Label)
    (hleft : P.left l + z ≤ x) (hright : x < P.right l + z) :
    P.label x = l := by
  have hzero : 0 ≤ x - z := by linarith [P.left_nonneg l]
  have hone : x - z < 1 := by linarith [P.right_le_one l]
  have hfract : Int.fract x = x - z :=
    Int.fract_eq_iff.mpr ⟨hzero, hone, z, by ring⟩
  apply P.label_eq_of_mem
  rw [hfract]
  constructor <;> linarith

def word (k : ℕ) (a b : ℝ) : Fin k → Label :=
  fun j => P.label (a + (j : ℝ) * b)

theorem word_fract_parameters (k : ℕ) (a b : ℝ) :
    P.word k a b = P.word k (Int.fract a) (Int.fract b) := by
  funext j
  apply P.label_eq_of_sub_int (⌊a⌋ + (j.val : ℤ) * ⌊b⌋)
  simp only [Int.fract, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  ring

/-- Start and step representatives of the global counting argument. -/
def parameterDomain : Set (Fin 2 → ℝ) :=
  {x | x 0 ∈ Set.Ico (0 : ℝ) 1 ∧ x 1 ∈ Set.Ico (0 : ℝ) 1}

def affinePoint {k : ℕ} (j : Fin k) (x : Fin 2 → ℝ) : ℝ :=
  x 0 + (j : ℝ) * x 1

theorem affinePoint_mem {k : ℕ} (j : Fin k) {x : Fin 2 → ℝ}
    (hx : x ∈ parameterDomain) : affinePoint j x ∈ Set.Ico (0 : ℝ) k := by
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_iff.mpr j.isLt
  have hprod : (j : ℝ) * x 1 ≤ j := by
    simpa using mul_le_mul_of_nonneg_left hx.2.2.le hj
  constructor
  · exact add_nonneg hx.1.1 (mul_nonneg hj hx.2.1)
  · dsimp [affinePoint]
    linarith [hx.1.2]

/-- Position, literal label, choice of endpoint, and integer translate. -/
abbrev ComparisonIndex (k : ℕ) (Label : Type uk) := Fin k × Label × Bool × Fin k

def endpoint (l : Label) (upper : Bool) : ℝ :=
  if upper then P.right l else P.left l

def comparison {k : ℕ} (i : ComparisonIndex k Label) : AffineForm 2 where
  linear := ![1, (i.1 : ℝ)]
  constant := -(P.endpoint i.2.1 i.2.2.1 + (i.2.2.2 : ℝ))

theorem comparison_eval {k : ℕ} (i : ComparisonIndex k Label) (x : Fin 2 → ℝ) :
    (P.comparison i).eval x =
      affinePoint i.1 x - (P.endpoint i.2.1 i.2.2.1 + (i.2.2.2 : ℝ)) := by
  simp [comparison, AffineForm.eval, affinePoint, Fin.sum_univ_two]
  ring

variable [Fintype Label]

def comparisons (k : ℕ) : Fin (Fintype.card (ComparisonIndex k Label)) → AffineForm 2 :=
  fun i => P.comparison ((Fintype.equivFin (ComparisonIndex k Label)).symm i)

theorem comparison_count (k : ℕ) :
    Fintype.card (ComparisonIndex k Label) = 2 * k ^ 2 * Fintype.card Label := by
  simp only [ComparisonIndex, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

theorem word_eq_of_signVector_eq {k : ℕ} {x y : Fin 2 → ℝ}
    (hx : x ∈ parameterDomain) (_hy : y ∈ parameterDomain)
    (hs : signVector (P.comparisons k) x = signVector (P.comparisons k) y) :
    P.word k (x 0) (x 1) = P.word k (y 0) (y 1) := by
  classical
  have hsign (i : ComparisonIndex k Label) :
      ternarySign ((P.comparison i).eval x) =
        ternarySign ((P.comparison i).eval y) := by
    have h := congrFun hs ((Fintype.equivFin (ComparisonIndex k Label)) i)
    simpa only [signVector, comparisons, Equiv.symm_apply_apply] using h
  funext j
  let t := affinePoint j x
  have ht := affinePoint_mem j hx
  have hz0 : (0 : ℤ) ≤ ⌊t⌋ := Int.floor_nonneg.mpr ht.1
  have hzk : ⌊t⌋ < (k : ℤ) := Int.floor_lt.mpr (by exact_mod_cast ht.2)
  let z : Fin k := ⟨⌊t⌋.toNat, by omega⟩
  have hzcast : (z : ℝ) = (⌊t⌋ : ℝ) := by
    dsimp [z]
    exact_mod_cast Int.toNat_of_nonneg hz0
  let l := P.label t
  have hcell := P.label_mem t
  change P.left l ≤ t - (⌊t⌋ : ℝ) ∧ t - (⌊t⌋ : ℝ) < P.right l at hcell
  have hl : 0 ≤ t - (P.left l + (z : ℝ)) := by
    rw [hzcast]
    linarith [hcell.1]
  have hr : t - (P.right l + (z : ℝ)) < 0 := by
    rw [hzcast]
    linarith [hcell.2]
  have hleft := hsign (j, l, false, z)
  have hright := hsign (j, l, true, z)
  simp only [comparison_eval, endpoint, Bool.false_eq_true, ite_false, ite_true] at hleft hright
  have hyl : 0 ≤ affinePoint j y - (P.left l + (z : ℝ)) := by
    apply le_of_not_gt
    intro hyneg
    have hzero := (ternarySign_eq_zero _).mpr hyneg
    rw [← hleft] at hzero
    exact (not_lt_of_ge hl) ((ternarySign_eq_zero _).mp hzero)
  have hyr : affinePoint j y - (P.right l + (z : ℝ)) < 0 := by
    apply (ternarySign_eq_zero _).mp
    rw [← hright]
    exact (ternarySign_eq_zero _).mpr hr
  have hylabel : P.label (affinePoint j y) = l :=
    P.label_eq_of_lifted_mem (affinePoint j y) (z.val : ℤ) l
      (by simpa only [Int.cast_natCast] using
        (show P.left l + (z : ℝ) ≤ affinePoint j y by linarith))
      (by simpa only [Int.cast_natCast] using
        (show affinePoint j y < P.right l + (z : ℝ) by linarith))
  exact hylabel.symm

/-- The finite scalar-word family is derived from actual affine comparisons.
The equivalence characterizes its exact image on normalized parameters. -/
theorem exists_exact_word_family (k : ℕ) :
    ∃ S : Finset (Fin k → Label),
      (∀ w, w ∈ S ↔ ∃ x ∈ parameterDomain, P.word k (x 0) (x 1) = w) ∧
      S.card ≤ 16 * (3 * k ^ 2 * Fintype.card Label + 1) ^ 6 := by
  obtain ⟨S, hS, hcard⟩ := finite_outputs_of_comparisons (P.comparisons k)
    parameterDomain (fun x => P.word k (x 0) (x 1))
    (fun _ hx _ hy hs => P.word_eq_of_signVector_eq hx hy hs)
  refine ⟨S, hS, ?_⟩
  have hcount : Fintype.card (ComparisonIndex k Label) ≤
      3 * k ^ 2 * Fintype.card Label := by
    rw [comparison_count]
    nlinarith
  calc
    S.card ≤ 16 * (Fintype.card (ComparisonIndex k Label) + 1) ^ 6 := by
      simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reducePow] using hcard
    _ ≤ 16 * (3 * k ^ 2 * Fintype.card Label + 1) ^ 6 :=
      Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right hcount 1) 6)

/-- Every real start and step belongs to the same counted family, by genuine
integer-periodicity of the literal interval labels. -/
theorem exists_word_family (k : ℕ) :
    ∃ S : Finset (Fin k → Label), (∀ a b : ℝ, P.word k a b ∈ S) ∧
      S.card ≤ 16 * (3 * k ^ 2 * Fintype.card Label + 1) ^ 6 := by
  obtain ⟨S, hS, hcard⟩ := P.exists_exact_word_family k
  refine ⟨S, ?_, hcard⟩
  intro a b
  rw [P.word_fract_parameters]
  apply (hS _).mpr
  refine ⟨![Int.fract a, Int.fract b], ?_, rfl⟩
  exact ⟨⟨Int.fract_nonneg a, Int.fract_lt_one a⟩,
    ⟨Int.fract_nonneg b, Int.fract_lt_one b⟩⟩

variable {OtherLabel : Type uOtherLabel} [Fintype OtherLabel]

/-- The actual full label word of two independent `D`-coordinate progressions. -/
def fullWord (Q : CirclePartition OtherLabel) (D k : ℕ)
    (firstStart firstStep secondStart secondStep : Fin D → ℝ) :
    Fin k → FullLabel D Label OtherLabel := fun j =>
  (fun i => P.word k (firstStart i) (firstStep i) j,
   fun i => Q.word k (secondStart i) (secondStep i) j)

/-- Global full words have a finite cover derived from their actual scalar
interval labels. The common endpoint budget is the sum of the two mesh sizes.
The argument does not require or assume independence of actual cyclic orbit
coordinates: counting all independent real starts and steps gives a cover. -/
theorem exists_fullWord_family (Q : CirclePartition OtherLabel) (D k : ℕ) :
    ∃ S : Finset (Fin k → FullLabel D Label OtherLabel),
      (∀ a b c d : Fin D → ℝ, P.fullWord Q D k a b c d ∈ S) ∧
      S.card ≤ (16 *
        (3 * k ^ 2 * (Fintype.card Label + Fintype.card OtherLabel) + 1) ^ 6) ^
          (2 * D) := by
  classical
  obtain ⟨first, hfirst, hfirstcard⟩ := P.exists_word_family k
  obtain ⟨second, hsecond, hsecondcard⟩ := Q.exists_word_family k
  let decode : ((Fin D → Fin k → Label) × (Fin D → Fin k → OtherLabel)) →
      (Fin k → FullLabel D Label OtherLabel) :=
    fun p j => (fun i => p.1 i j, fun i => p.2 i j)
  let S := ((coordinateFamily (fun _ : Fin D => first)).product
    (coordinateFamily (fun _ : Fin D => second))).image decode
  refine ⟨S, ?_, ?_⟩
  · intro a b c d
    apply Finset.mem_image.mpr
    refine ⟨(fun i => P.word k (a i) (b i), fun i => Q.word k (c i) (d i)),
      Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Fintype.mem_piFinset.mpr (fun i => hfirst (a i) (b i))
    · exact Fintype.mem_piFinset.mpr (fun i => hsecond (c i) (d i))
  · apply card_decoded_twoSystems_le
    · intro _
      exact hfirstcard.trans (Nat.mul_le_mul_left 16
        (Nat.pow_le_pow_left (Nat.add_le_add_right
          (Nat.mul_le_mul_left (3 * k ^ 2) (Nat.le_add_right _ _)) 1) 6))
    · intro _
      exact hsecondcard.trans (Nat.mul_le_mul_left 16
        (Nat.pow_le_pow_left (Nat.add_le_add_right
          (Nat.mul_le_mul_left (3 * k ^ 2) (Nat.le_add_left _ _)) 1) 6))

end
end CirclePartition

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

namespace QuantitativeVanDerWaerden

noncomputable section

/-- The actual uniform mesh, with no extra partition hypothesis. -/
def uniformPartition (n : ℕ) (hn : 0 < n) : CirclePartition (Fin n) where
  left := UniformMesh.left n
  right := UniformMesh.right n
  left_nonneg := UniformMesh.left_nonneg n
  left_lt_right := UniformMesh.left_lt_right n hn
  right_le_one := UniformMesh.right_le_one n hn
  covers := fun x hx => UniformMesh.existsUnique_contains n hn x hx

theorem uniformPartition_label (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (uniformPartition n hn).label x = UniformMesh.label n hn x := by
  apply (uniformPartition n hn).label_eq_of_mem
  exact UniformMesh.label_mem n hn x

/-- The actual centered adaptive mesh, translated to the shared fundamental
interval. This is a translation of cells, not an identification of labels. -/
def adaptivePartition (A : AdaptiveMesh) : CirclePartition A.Label where
  left := fun i => A.left i + 1 / 2
  right := fun i => A.right i + 1 / 2
  left_nonneg := fun i => by linarith [A.left_ge_neg_half i]
  left_lt_right := fun i => by
    have h := A.width_pos i
    dsimp [AdaptiveMesh.width] at h
    linarith
  right_le_one := fun i => by linarith [A.right_le_half i]
  covers := by
    intro x hx
    obtain ⟨i, hi⟩ := A.exists_label
      (show -(1 / 2 : ℝ) ≤ x - 1 / 2 by linarith [hx.1])
      (show x - 1 / 2 < 1 / 2 by linarith [hx.2])
    refine ⟨i, ?_, ?_⟩
    · change A.left i + 1 / 2 ≤ x ∧ x < A.right i + 1 / 2
      rcases hi with ⟨hil, hir⟩
      constructor <;> linarith
    · intro j hj
      apply A.label_unique j i (x := x - 1 / 2) _ hi
      change A.left j ≤ x - 1 / 2 ∧ x - 1 / 2 < A.right j
      constructor <;> linarith [hj.1, hj.2]

theorem adaptivePartition_label (A : AdaptiveMesh) (x : ℝ) :
    (adaptivePartition A).label (x + 1 / 2) = A.meshLabel x := by
  apply (adaptivePartition A).label_eq_of_mem
  have h := A.meshLabel_contains x
  change A.left (A.meshLabel x) ≤ centered x ∧
    centered x < A.right (A.meshLabel x) at h
  change A.left (A.meshLabel x) + 1 / 2 ≤ Int.fract (x + 1 / 2) ∧
    Int.fract (x + 1 / 2) < A.right (A.meshLabel x) + 1 / 2
  have heq : Int.fract (x + 1 / 2) = centered x + 1 / 2 := by
    change (x + 1 / 2) - (⌊x + 1 / 2⌋ : ℝ) =
      (x - (⌊x + 1 / 2⌋ : ℝ)) + 1 / 2
    ring
  rw [heq]
  constructor <;> linarith [h.1, h.2]

end
end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# A counted family covering the actual cyclic label words

The coordinate representatives of a cyclic progression are real affine
progressions modulo integers. Literal partition labels are integer-periodic,
so the actual label word belongs to the global family derived from affine
comparisons. The centered second-system start is shifted by `1/2`; its step
is not shifted. No independence of the cyclic coordinates is assumed.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

variable {k : ℕ}

/-- Exact identification of the actual cyclic word with a word of the two
literal circle partitions, including their half-open boundary conventions. -/
theorem fullLabelWord_eq_partitionWord (s : Data k) (hk : 3 ≤ k)
    (ad : Group s × Group s) :
    fullLabelWord s hk ad =
      (uniformPartition (uniformCount k) (uniformCount_pos hk)).fullWord
        (adaptivePartition (mesh s hk)) (dimension k) k
        (xRep s.q (dimension k) ad.1)
        (xRep s.q (dimension k) ad.2)
        (fun i => yRep s.q (dimension k) (lambda k) ad.1 i + 1 / 2)
        (yRep s.q (dimension k) (lambda k) ad.2) := by
  funext j
  apply Prod.ext
  · funext i
    change UniformMesh.label (uniformCount k) (uniformCount_pos hk)
        (xRep s.q (dimension k) (ad.1 + (j.val : Group s) * ad.2) i) =
      (uniformPartition (uniformCount k) (uniformCount_pos hk)).label
        (xRep s.q (dimension k) ad.1 i +
          (j.val : ℝ) * xRep s.q (dimension k) ad.2 i)
    rw [← uniformPartition_label]
    obtain ⟨z, hz⟩ := xRep_ap_congr s.pos ad.1 ad.2 j.val i
    apply CirclePartition.label_eq_of_sub_int _ z
    simpa only [nsmul_eq_mul, sub_sub] using hz
  · funext i
    change (mesh s hk).meshLabel
        (yRep s.q (dimension k) (lambda k)
          (ad.1 + (j.val : Group s) * ad.2) i) =
      (adaptivePartition (mesh s hk)).label
        ((yRep s.q (dimension k) (lambda k) ad.1 i + 1 / 2) +
          (j.val : ℝ) * yRep s.q (dimension k) (lambda k) ad.2 i)
    rw [← adaptivePartition_label]
    obtain ⟨z, hz⟩ := yRep_ap_congr s.pos (lambda k) ad.1 ad.2 j.val i
    simp only [nsmul_eq_mul] at hz
    apply CirclePartition.label_eq_of_sub_int _ z
    linarith only [hz]

/-- A finite family covering every actual cyclic progression word. The
cardinality bound is proved from the two literal partitions, not supplied
as a hypothesis. The step may be zero. -/
theorem exists_fullLabelWord_family (s : Data k) (hk : 3 ≤ k) :
    ∃ words : Finset (Fin k → Label s hk),
      (∀ ad : Group s × Group s, fullLabelWord s hk ad ∈ words) ∧
      words.card ≤
        (16 * (3 * k ^ 2 *
          (uniformCount k + Fintype.card (mesh s hk).Label) + 1) ^ 6) ^
          (2 * dimension k) := by
  obtain ⟨words, hwords, hcard⟩ :=
    (uniformPartition (uniformCount k) (uniformCount_pos hk)).exists_fullWord_family
      (adaptivePartition (mesh s hk)) (dimension k) k
  refine ⟨words, ?_, ?_⟩
  · intro ad
    rw [fullLabelWord_eq_partitionWord]
    exact hwords _ _ _ _
  · simpa only [Fintype.card_fin] using hcard

/-- The same bound with the actual adaptive mesh cardinality substituted. -/
theorem exists_fullWordFamily (s : Data k) (hk : 3 ≤ k) :
    ∃ words : Finset (Fin k → Label s hk),
      words.card ≤
        (16 * (3 * k ^ 2 *
          (uniformCount k + 2 * scalarMeshSize k s.q) + 1) ^ 6) ^
          (2 * dimension k) ∧
      ∀ a d : Group s, fullLabelWord s hk (a, d) ∈ words := by
  obtain ⟨words, hwords, hcard⟩ := exists_fullLabelWord_family s hk
  refine ⟨words, ?_, fun a d => hwords (a, d)⟩
  simpa only [card_second_labels] using hcard

end QuantitativeVanDerWaerden.ConstructionModel

end

end OAI
end
end

section
section
namespace OAI

open scoped BigOperators


namespace QuantitativeVanDerWaerden.FiniteLocalLemma

/-- A probability on the finite sample space `Ω`, with the event identities
needed by the finite local lemma. -/
structure Probability (Ω : Type uOmega) [Fintype Ω] [DecidableEq Ω] where
  mass : Finset Ω → ℝ
  nonneg : ∀ A, 0 ≤ mass A
  univ : mass Finset.univ = 1
  mono : ∀ {A B}, A ⊆ B → mass A ≤ mass B
  split : ∀ A B, mass (A \ B) + mass (A ∩ B) = mass A

namespace Probability

variable {Ω : Type uOmega} [Fintype Ω] [DecidableEq Ω]

@[simp]
theorem mass_empty (P : Probability Ω) : P.mass ∅ = 0 := by
  have h : P.mass ∅ + P.mass ∅ = P.mass ∅ := by
    simpa using P.split ∅ ∅
  exact add_left_cancel (h.trans (add_zero _).symm)

/-- The probability whose mass at each point is its prescribed weight. -/
noncomputable def ofWeights (weight : Ω → ℝ)
    (weight_nonneg : ∀ ω, 0 ≤ weight ω)
    (weight_sum : ∑ ω, weight ω = 1) : Probability Ω where
  mass A := ∑ ω ∈ A, weight ω
  nonneg A := Finset.sum_nonneg fun ω _ => weight_nonneg ω
  univ := weight_sum
  mono := by
    intro A B hAB
    exact Finset.sum_le_sum_of_subset_of_nonneg hAB fun ω _ _ => weight_nonneg ω
  split A B := by
    exact (add_comm _ _).trans (Finset.sum_inter_add_sum_sdiff A B weight)

@[simp]
theorem ofWeights_mass (weight : Ω → ℝ)
    (weight_nonneg : ∀ ω, 0 ≤ weight ω)
    (weight_sum : ∑ ω, weight ω = 1) (A : Finset Ω) :
    (ofWeights weight weight_nonneg weight_sum).mass A = ∑ ω ∈ A, weight ω := rfl

end Probability

end QuantitativeVanDerWaerden.FiniteLocalLemma

end OAI
end
end

section
section
namespace OAI


namespace QuantitativeVanDerWaerden.FiniteLocalLemma

open scoped BigOperators

variable {Ω : Type uOmega} {I : Type uI} [Fintype Ω] [DecidableEq Ω] [DecidableEq I]

/-- Outcomes avoiding every bad event indexed by `T`. -/
noncomputable def avoid (bad : I → Finset Ω) (T : Finset I) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω => ∀ i ∈ T, ω ∉ bad i

@[simp] theorem mem_avoid {Ω : Type uOmega} {I : Type uI} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq I]
    (bad : I → Finset Ω) (T : Finset I) (ω : Ω) :
    ω ∈ avoid bad T ↔ ∀ i ∈ T, ω ∉ bad i := by
  classical
  simp [avoid]

@[simp] theorem avoid_empty (bad : I → Finset Ω) :
    avoid bad ∅ = Finset.univ := by
  classical
  ext ω
  simp

theorem avoid_insert (bad : I → Finset Ω) (i : I) (T : Finset I) :
    avoid bad (insert i T) = avoid bad T \ bad i := by
  classical
  ext ω
  simp [and_comm]

theorem avoid_antitone (bad : I → Finset Ω) {S T : Finset I} (hST : S ⊆ T) :
    avoid bad T ⊆ avoid bad S := by
  intro ω hω
  rw [mem_avoid] at hω ⊢
  exact fun i hi => hω i (hST hi)

theorem avoid_mass_split (P : Probability Ω) (bad : I → Finset Ω)
    (i : I) (T : Finset I) :
    P.mass (avoid bad (insert i T)) + P.mass (bad i ∩ avoid bad T) =
      P.mass (avoid bad T) := by
  simpa [avoid_insert, Finset.inter_comm] using P.split (avoid bad T) (bad i)

/-- Products of factors in `[0,1]` decrease when more factors are included. -/
theorem prod_antitone_of_unitInterval {S T : Finset I} {f : I → ℝ}
    (hST : S ⊆ T) (h0 : ∀ i ∈ T, 0 ≤ f i) (h1 : ∀ i ∈ T, f i ≤ 1) :
    (∏ i ∈ T, f i) ≤ ∏ i ∈ S, f i := by
  rw [← Finset.prod_sdiff hST]
  exact mul_le_of_le_one_left
    (Finset.prod_nonneg fun i hi => h0 i (hST hi))
    (Finset.prod_le_one
      (fun i hi => h0 i (Finset.mem_sdiff.mp hi).1)
      (fun i hi => h1 i (Finset.mem_sdiff.mp hi).1))

/-- Iterating bounds on intersections with one bad event yields the lower
bound for avoiding a finite collection of further events. -/
theorem avoid_union_lower (P : Probability Ω) (bad : I → Finset Ω)
    (z : I → ℝ) (target S U : Finset I)
    (hz : ∀ i, 0 ≤ 1 - z i)
    (hST : S ⊆ target) (hUT : U ⊆ target) (hSU : Disjoint S U)
    (hcond : ∀ R, R ⊂ target → ∀ i, i ∉ R →
      P.mass (bad i ∩ avoid bad R) ≤ z i * P.mass (avoid bad R)) :
    P.mass (avoid bad S) * (∏ i ∈ U, (1 - z i)) ≤
      P.mass (avoid bad (S ∪ U)) := by
  revert hUT hSU
  induction U using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert i U hiU ih =>
      intro hUT hSU
      have hiT : i ∈ target := hUT (Finset.mem_insert_self i U)
      have hUT' : U ⊆ target := fun j hj => hUT (Finset.mem_insert_of_mem hj)
      have hiS : i ∉ S := by
        intro hiS
        exact Finset.disjoint_left.mp hSU hiS (Finset.mem_insert_self i U)
      have hSU' : Disjoint S U := Finset.disjoint_left.mpr fun j hjS hjU =>
        Finset.disjoint_left.mp hSU hjS (Finset.mem_insert_of_mem hjU)
      have hiR : i ∉ S ∪ U := by simp [hiS, hiU]
      have hRT : S ∪ U ⊆ target := Finset.union_subset hST hUT'
      have hRproper : S ∪ U ⊂ target := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hRT, ?_⟩
        intro heq
        exact hiR (heq.symm ▸ hiT)
      have hbound := hcond (S ∪ U) hRproper i hiR
      have hsplit := avoid_mass_split P bad i (S ∪ U)
      have hstep : (1 - z i) * P.mass (avoid bad (S ∪ U)) ≤
          P.mass (avoid bad (S ∪ insert i U)) := by
        rw [Finset.union_insert]
        nlinarith
      rw [Finset.prod_insert hiU]
      calc
        P.mass (avoid bad S) * ((1 - z i) * ∏ j ∈ U, (1 - z j)) =
            (1 - z i) * (P.mass (avoid bad S) * ∏ j ∈ U, (1 - z j)) := by ring
        _ ≤ (1 - z i) * P.mass (avoid bad (S ∪ U)) :=
          mul_le_mul_of_nonneg_left (ih hUT' hSU') (hz i)
        _ ≤ P.mass (avoid bad (S ∪ insert i U)) := hstep

/-- The simultaneous induction behind the asymmetric local lemma. -/
theorem positive_and_conditional_bound (P : Probability Ω) (bad : I → Finset Ω)
    (neighbors : I → Finset I) (z : I → ℝ)
    (hzpos : ∀ i, 0 < z i) (hzlt : ∀ i, z i < 1)
    (hindependent : ∀ i T, i ∉ T → Disjoint T (neighbors i) →
      P.mass (bad i ∩ avoid bad T) = P.mass (bad i) * P.mass (avoid bad T))
    (hcriterion : ∀ i, P.mass (bad i) ≤ z i * ∏ j ∈ neighbors i, (1 - z j))
    (T : Finset I) :
    0 < P.mass (avoid bad T) ∧
      ∀ i, i ∉ T → P.mass (bad i ∩ avoid bad T) ≤ z i * P.mass (avoid bad T) := by
  refine Finset.strongInductionOn T ?_
  intro T ih
  have hpositive : 0 < P.mass (avoid bad T) := by
    by_cases hT : T = ∅
    · subst T
      simpa only [avoid_empty, P.univ] using (show (0 : ℝ) < 1 by norm_num)
    · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hT
      have hrec := ih (T.erase j) (Finset.erase_ssubset hj)
      have hjnot : j ∉ T.erase j := Finset.notMem_erase j T
      have hbound := hrec.2 j hjnot
      have hsplit := avoid_mass_split P bad j (T.erase j)
      rw [Finset.insert_erase hj] at hsplit
      have hstrict : 0 < (1 - z j) * P.mass (avoid bad (T.erase j)) :=
        mul_pos (sub_pos.mpr (hzlt j)) hrec.1
      nlinarith
  refine ⟨hpositive, ?_⟩
  intro i hiT
  let S := T \ neighbors i
  let U := T ∩ neighbors i
  have hST : S ⊆ T := Finset.sdiff_subset
  have hUT : U ⊆ T := Finset.inter_subset_left
  have hUN : U ⊆ neighbors i := Finset.inter_subset_right
  have hSN : Disjoint S (neighbors i) := by
    exact Finset.disjoint_left.mpr fun j hjS hjN => (Finset.mem_sdiff.mp hjS).2 hjN
  have hSU : Disjoint S U := Finset.disjoint_left.mpr fun j hjS hjU =>
    Finset.disjoint_left.mp hSN hjS (hUN hjU)
  have hSUeq : S ∪ U = T := by
    ext j
    by_cases hj : j ∈ neighbors i <;> simp [S, U, hj]
  have hiS : i ∉ S := fun h => hiT (hST h)
  have hlow : P.mass (avoid bad S) * (∏ j ∈ U, (1 - z j)) ≤
      P.mass (avoid bad T) := by
    rw [← hSUeq]
    exact avoid_union_lower P bad z T S U (fun j => le_of_lt (sub_pos.mpr (hzlt j)))
      hST hUT hSU (fun R hR => (ih R hR).2)
  have hprod : (∏ j ∈ neighbors i, (1 - z j)) ≤ ∏ j ∈ U, (1 - z j) :=
    prod_antitone_of_unitInterval hUN
      (fun j _ => le_of_lt (sub_pos.mpr (hzlt j)))
      (fun j _ => sub_le_self 1 (le_of_lt (hzpos j)))
  have hbad : P.mass (bad i) ≤ z i * ∏ j ∈ U, (1 - z j) :=
    (hcriterion i).trans (mul_le_mul_of_nonneg_left hprod (le_of_lt (hzpos i)))
  calc
    P.mass (bad i ∩ avoid bad T) ≤ P.mass (bad i ∩ avoid bad S) :=
      P.mono (Finset.inter_subset_inter_left (avoid_antitone bad hST))
    _ = P.mass (bad i) * P.mass (avoid bad S) := hindependent i S hiS hSN
    _ ≤ (z i * ∏ j ∈ U, (1 - z j)) * P.mass (avoid bad S) :=
      mul_le_mul_of_nonneg_right hbad (P.nonneg _)
    _ = z i * (P.mass (avoid bad S) * ∏ j ∈ U, (1 - z j)) := by ring
    _ ≤ z i * P.mass (avoid bad T) :=
      mul_le_mul_of_nonneg_left hlow (le_of_lt (hzpos i))

/-- Finite asymmetric local lemma, stated for a finite additive probability. -/
theorem finite_asymmetric_local_lemma [Fintype I]
    (P : Probability Ω) (bad : I → Finset Ω) (neighbors : I → Finset I)
    (z : I → ℝ) (hzpos : ∀ i, 0 < z i) (hzlt : ∀ i, z i < 1)
    (hindependent : ∀ i T, i ∉ T → Disjoint T (neighbors i) →
      P.mass (bad i ∩ avoid bad T) = P.mass (bad i) * P.mass (avoid bad T))
    (hcriterion : ∀ i, P.mass (bad i) ≤ z i * ∏ j ∈ neighbors i, (1 - z j)) :
    0 < P.mass (avoid bad Finset.univ) :=
  (positive_and_conditional_bound P bad neighbors z hzpos hzlt hindependent
    hcriterion Finset.univ).1

theorem exists_avoiding [Fintype I]
    (P : Probability Ω) (bad : I → Finset Ω) (neighbors : I → Finset I)
    (z : I → ℝ) (hzpos : ∀ i, 0 < z i) (hzlt : ∀ i, z i < 1)
    (hindependent : ∀ i T, i ∉ T → Disjoint T (neighbors i) →
      P.mass (bad i ∩ avoid bad T) = P.mass (bad i) * P.mass (avoid bad T))
    (hcriterion : ∀ i, P.mass (bad i) ≤ z i * ∏ j ∈ neighbors i, (1 - z j)) :
    ∃ ω, ∀ i, ω ∉ bad i := by
  have hpos := finite_asymmetric_local_lemma P bad neighbors z hzpos hzlt
    hindependent hcriterion
  have hne : (avoid bad Finset.univ).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    rw [h, P.mass_empty] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  obtain ⟨ω, hω⟩ := hne
  exact ⟨ω, fun i => (mem_avoid bad Finset.univ ω).mp hω i (Finset.mem_univ i)⟩

theorem finite_asymmetric_local_lemma_weights [Fintype I]
    (weight : Ω → ℝ) (weight_nonneg : ∀ ω, 0 ≤ weight ω)
    (weight_sum : ∑ ω, weight ω = 1)
    (bad : I → Finset Ω) (neighbors : I → Finset I)
    (z : I → ℝ) (hzpos : ∀ i, 0 < z i) (hzlt : ∀ i, z i < 1)
    (hindependent : ∀ i T, i ∉ T → Disjoint T (neighbors i) →
      (∑ ω ∈ bad i ∩ avoid bad T, weight ω) =
        (∑ ω ∈ bad i, weight ω) * (∑ ω ∈ avoid bad T, weight ω))
    (hcriterion : ∀ i, (∑ ω ∈ bad i, weight ω) ≤
      z i * ∏ j ∈ neighbors i, (1 - z j)) :
    0 < ∑ ω ∈ avoid bad Finset.univ, weight ω :=
  finite_asymmetric_local_lemma (Probability.ofWeights weight weight_nonneg weight_sum)
    bad neighbors z hzpos hzlt hindependent hcriterion

end QuantitativeVanDerWaerden.FiniteLocalLemma

end OAI
end
end

section
section
namespace OAI


namespace QuantitativeVanDerWaerden

open scoped BigOperators

theorem outer_exists_avoiding_from_incidence
    {Ω : Type uOmega} {I : Type uI} {Label : Type uLabel} [Fintype Ω] [DecidableEq Ω] [Fintype I] [DecidableEq I]
    [DecidableEq Label]
    (P : FiniteLocalLemma.Probability Ω) (bad : I → Finset Ω)
    (support : I → Finset Label)
    (hsize : ∀ i, (100 : ℝ) ≤ (support i).card)
    (htail : ∀ i, P.mass (bad i) ≤ 2 * Real.exp (-((support i).card : ℝ) / 8))
    (hindependent : ∀ i T, i ∉ T → Disjoint T (outerNeighbors support i) →
      P.mass (bad i ∩ FiniteLocalLemma.avoid bad T) =
        P.mass (bad i) * P.mass (FiniteLocalLemma.avoid bad T))
    (hincident : ∀ b,
      ∑ j ∈ Finset.univ.filter (fun j => b ∈ support j),
        Real.exp (-((support j).card : ℝ) / 32) ≤ 1 / 500) :
    ∃ ω, ∀ i, ω ∉ bad i := by
  classical
  let z : I → ℝ := fun i => Real.exp (-((support i).card : ℝ) / 32)
  have hzpos : ∀ i, 0 < z i := fun _ => Real.exp_pos _
  have hzhalf : ∀ i, z i < 1 / 2 := fun i => outer_weight_lt_half (hsize i)
  apply FiniteLocalLemma.exists_avoiding P bad (outerNeighbors support) z hzpos
    (fun i => lt_trans (hzhalf i) (by norm_num)) hindependent
  intro i
  have hsum : ∑ j ∈ outerNeighbors support i, z j ≤ (support i).card / 500 := by
    have h := outer_neighbor_weight_bound support z (fun j => (hzpos j).le)
      (1 / 500) hincident i
    simpa only [div_eq_mul_inv, one_mul] using h
  exact (htail i).trans
    (outer_local_criterion (outerNeighbors support i) z ((support i).card : ℝ)
      (hsize i) (fun j _ => (hzpos j).le) (fun j _ => (hzhalf j).le) hsum)

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# The fair-bit exponential moment bound

Finite Taylor approximations with proved remainder bounds suffice for the
parameter used in the fair-bit tail bound.
-/

namespace QuantitativeVanDerWaerden

/-- The exponential moment bound at the fair-bit tail parameter. -/
theorem cosh_half_le_exp_eighth : Real.cosh (1 / 2 : ℝ) ≤ Real.exp (1 / 8 : ℝ) := by
  have ah : |(1 / 2 : ℝ)| = 1 / 2 := abs_of_nonneg (by norm_num)
  have ae : |(1 / 8 : ℝ)| = 1 / 8 := abs_of_nonneg (by norm_num)
  have hp := Real.exp_bound (x := (1 / 2 : ℝ)) (by rw [ah]; norm_num)
    (n := 4) (by norm_num)
  have hm := Real.exp_bound (x := -(1 / 2 : ℝ)) (by rw [abs_neg, ah]; norm_num)
    (n := 4) (by norm_num)
  have he := Real.exp_bound (x := (1 / 8 : ℝ)) (by rw [ae]; norm_num)
    (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg, ah, ae] at hp hm he
  rw [abs_le] at hp hm he
  rw [Real.cosh_eq]
  linarith [hp.2, hm.2, he.1]

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

noncomputable section


namespace QuantitativeVanDerWaerden
namespace FairBitTail

open scoped BigOperators

variable {Label : Type uLabel} [Fintype Label] [DecidableEq Label]

/-- Each independent fair-bit assignment has this product weight. -/
def weight (_ω : Label → Bool) : ℝ := ∏ _i : Label, (1 / 2 : ℝ)

theorem weight_nonneg {Label : Type uLabel} [Fintype Label] [DecidableEq Label]
    (ω : Label → Bool) : 0 ≤ weight ω := by
  unfold weight
  exact Finset.prod_nonneg (fun _ _ => by norm_num)

/-- The centered deficit contributed by one bit. -/
def deviation (b x : Bool) : ℝ := if x = b then -(1 / 2 : ℝ) else 1 / 2

theorem sum_deviation {Label : Type uLabel} [Fintype Label] [DecidableEq Label]
    (S : Finset Label) (b : Bool) (ω : Label → Bool) :
    (∑ i ∈ S, deviation b (ω i)) =
      (S.card : ℝ) / 2 - ((S.filter fun i => ω i = b).card : ℝ) := by
  classical
  calc
    (∑ i ∈ S, deviation b (ω i)) =
        ∑ i ∈ S, ((1 / 2 : ℝ) - if ω i = b then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold deviation
      split_ifs <;> norm_num
    _ = (S.card : ℝ) / 2 - ((S.filter fun i => ω i = b).card : ℝ) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_boole]
      ring

/-- The exact moment generating function on any distinct label support. -/
theorem exponential_moment (S : Finset Label) (b : Bool) :
    (∑ ω : Label → Bool, weight ω *
      Real.exp (∑ i ∈ S, deviation b (ω i))) =
        Real.cosh (1 / 2 : ℝ) ^ S.card := by
  classical
  calc
    (∑ ω : Label → Bool, weight ω *
        Real.exp (∑ i ∈ S, deviation b (ω i))) =
        ∑ ω : Label → Bool, ∏ i : Label,
          ((1 / 2 : ℝ) * if i ∈ S then Real.exp (deviation b (ω i)) else 1) := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [Finset.prod_mul_distrib, Fintype.prod_ite_mem, Real.exp_sum]
      rfl
    _ = ∏ i : Label, ∑ x : Bool,
          ((1 / 2 : ℝ) * if i ∈ S then Real.exp (deviation b x) else 1) := by
      exact (Fintype.prod_sum (fun (i : Label) (x : Bool) =>
        (1 / 2 : ℝ) * if i ∈ S then Real.exp (deviation b x) else 1)).symm
    _ = ∏ i : Label, if i ∈ S then Real.cosh (1 / 2 : ℝ) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ S
      · cases b <;> simp [hi, deviation, Real.cosh_eq] <;> ring
      · simp [hi]
    _ = Real.cosh (1 / 2 : ℝ) ^ S.card := by simp

theorem exponential_moment_le (S : Finset Label) (b : Bool) :
    (∑ ω : Label → Bool, weight ω *
      Real.exp (∑ i ∈ S, deviation b (ω i))) ≤ Real.exp ((S.card : ℝ) / 8) := by
  rw [exponential_moment]
  calc
    Real.cosh (1 / 2 : ℝ) ^ S.card ≤ Real.exp (1 / 8 : ℝ) ^ S.card :=
      pow_le_pow_left₀ (Real.cosh_pos _).le cosh_half_le_exp_eighth _
    _ = Real.exp ((S.card : ℝ) / 8) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Exponential Markov for the lower tail of either selected bit. -/
theorem one_bit_tail (S : Finset Label) (b : Bool) :
    (∑ ω : Label → Bool,
      if 4 * (S.filter fun i => ω i = b).card < S.card then weight ω else 0) ≤
        Real.exp (-(S.card : ℝ) / 8) := by
  classical
  have hp (ω : Label → Bool) :
      (if 4 * (S.filter fun i => ω i = b).card < S.card then weight ω else 0) ≤
        weight ω * Real.exp (∑ i ∈ S, deviation b (ω i)) /
          Real.exp ((S.card : ℝ) / 4) := by
    by_cases hω : 4 * (S.filter fun i => ω i = b).card < S.card
    · rw [ite_eq_left hω]
      apply (le_div_iff₀ (Real.exp_pos _)).mpr
      apply mul_le_mul_of_nonneg_left _ (weight_nonneg ω)
      apply Real.exp_le_exp.mpr
      rw [sum_deviation]
      have hc : (4 : ℝ) * ((S.filter fun i => ω i = b).card : ℝ) <
          (S.card : ℝ) := by exact_mod_cast hω
      linarith
    · rw [ite_eq_right hω]
      exact div_nonneg (mul_nonneg (weight_nonneg ω) (Real.exp_pos _).le)
        (Real.exp_pos _).le
  calc
    (∑ ω : Label → Bool,
        if 4 * (S.filter fun i => ω i = b).card < S.card then weight ω else 0) ≤
        ∑ ω : Label → Bool,
          weight ω * Real.exp (∑ i ∈ S, deviation b (ω i)) /
            Real.exp ((S.card : ℝ) / 4) := Finset.sum_le_sum (fun ω _ => hp ω)
    _ = (∑ ω : Label → Bool, weight ω *
          Real.exp (∑ i ∈ S, deviation b (ω i))) / Real.exp ((S.card : ℝ) / 4) :=
      (Finset.sum_div _ _ _).symm
    _ ≤ Real.exp ((S.card : ℝ) / 8) / Real.exp ((S.card : ℝ) / 4) :=
      div_le_div_of_nonneg_right (exponential_moment_le S b) (Real.exp_pos _).le
    _ = Real.exp (-(S.card : ℝ) / 8) := by
      rw [← Real.exp_sub]
      congr 1
      ring

/-- Some bit has fewer than a quarter of the tested labels with probability
at most `2 exp(-|S|/8)`. The empty support is included. -/
theorem balancing_tail (S : Finset Label) :
    (∑ ω : Label → Bool,
      if ∃ b : Bool, 4 * (S.filter fun i => ω i = b).card < S.card
      then weight ω else 0) ≤ 2 * Real.exp (-(S.card : ℝ) / 8) := by
  classical
  have hu (ω : Label → Bool) :
      (if ∃ b : Bool, 4 * (S.filter fun i => ω i = b).card < S.card
        then weight ω else 0) ≤
      (if 4 * (S.filter fun i => ω i = false).card < S.card then weight ω else 0) +
      (if 4 * (S.filter fun i => ω i = true).card < S.card then weight ω else 0) := by
    by_cases hf : 4 * (S.filter fun i => ω i = false).card < S.card
    · have he : ∃ b : Bool, 4 * (S.filter fun i => ω i = b).card < S.card := ⟨false, hf⟩
      simp only [ite_eq_left he, ite_eq_left hf]
      apply le_add_of_nonneg_right
      split_ifs
      · exact weight_nonneg ω
      · exact le_rfl
    · by_cases ht : 4 * (S.filter fun i => ω i = true).card < S.card
      · have he : ∃ b : Bool, 4 * (S.filter fun i => ω i = b).card < S.card := ⟨true, ht⟩
        simp [he, hf, ht]
      · have he : ¬ ∃ b : Bool, 4 * (S.filter fun i => ω i = b).card < S.card := by
          rintro ⟨b, hb⟩
          cases b
          · exact hf hb
          · exact ht hb
        simp [he, hf, ht]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hu ω)
  rw [Finset.sum_add_distrib] at hsum
  have hfalse := one_bit_tail S false
  have htrue := one_bit_tail S true
  linarith

end FairBitTail
end QuantitativeVanDerWaerden

end

end OAI
end
end

section
section
namespace OAI


namespace QuantitativeVanDerWaerden

variable {Label : Type uLabel} [Fintype Label] [DecidableEq Label]

/-- A support fails balancing when one bit occurs fewer than a quarter of its
distinct labels. -/
noncomputable def fairBalancingBad (S : Finset Label) : Finset (Label → Bool) := by
  classical
  exact Finset.univ.filter fun ω =>
    ∃ b : Bool, 4 * (S.filter fun i => ω i = b).card < S.card

@[simp] theorem mem_fairBalancingBad (S : Finset Label) (ω : Label → Bool) :
    ω ∈ fairBalancingBad S ↔
      ∃ b : Bool, 4 * (S.filter fun i => ω i = b).card < S.card := by
  classical
  simp [fairBalancingBad]

/-- Avoiding the event says that both bits occupy at least a quarter. -/
theorem not_mem_fairBalancingBad_iff (S : Finset Label) (ω : Label → Bool) :
    ω ∉ fairBalancingBad S ↔
      ∀ b : Bool, S.card ≤ 4 * (S.filter fun i => ω i = b).card := by
  simp only [mem_fairBalancingBad, not_exists, not_lt]

/-- Agreement on the tested labels preserves membership in the bad event. -/
theorem fairBalancingBad_depends (S : Finset Label) (ω η : Label → Bool)
    (h : ∀ i ∈ S, ω i = η i) :
    ω ∈ fairBalancingBad S ↔ η ∈ fairBalancingBad S := by
  classical
  have hf (b : Bool) :
      S.filter (fun i => ω i = b) = S.filter (fun i => η i = b) := by
    apply Finset.filter_congr
    intro i hi
    rw [h i hi]
  simp only [mem_fairBalancingBad, hf]

theorem bernoulli_half_eq_fairWeight {Label : Type uLabel} [Fintype Label] [DecidableEq Label]
    (ω : Label → Bool) :
    FiniteProbability.bernoulliWeight (1 / 2) ω = FairBitTail.weight ω := by
  unfold FiniteProbability.bernoulliWeight FairBitTail.weight
  apply Finset.prod_congr rfl
  intro i _
  cases ω i <;> norm_num [FiniteProbability.bitWeight]

/-- The actual bad-event probability under independent fair Boolean labels. -/
theorem fair_balancing_tail (S : Finset Label) :
    FiniteProbability.prob (FiniteProbability.bernoulliWeight (1 / 2))
      (fairBalancingBad S) ≤ 2 * Real.exp (-(S.card : ℝ) / 8) := by
  classical
  unfold FiniteProbability.prob fairBalancingBad
  rw [Finset.sum_filter]
  simp_rw [bernoulli_half_eq_fairWeight]
  exact FairBitTail.balancing_tail S

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Coloring a finite family of literal supports

The sample space is the actual set of all Boolean assignments to labels. The
events test quarter-balancing on their named supports. Independence is derived
from disjoint supports of the product law, rather than postulated for the tests.
-/


namespace QuantitativeVanDerWaerden

open scoped BigOperators

variable {I : Type uI} {Label : Type uLabel} [Fintype I] [DecidableEq I]
  [Fintype Label] [DecidableEq Label]

/-- Avoidance of tests depends only on the union of their literal supports. -/
theorem outer_avoid_depends {I : Type uI} {Label : Type uLabel} [Fintype I] [DecidableEq I]
    [Fintype Label] [DecidableEq Label]
    (support : I → Finset Label) (T : Finset I) :
    FiniteProbability.DependsOn (T.biUnion support)
      (FiniteLocalLemma.avoid (fun i => fairBalancingBad (support i)) T) := by
  classical
  intro ω η hagree
  simp only [FiniteLocalLemma.mem_avoid]
  have hmem (i : I) (hi : i ∈ T) :
      ω ∈ fairBalancingBad (support i) ↔ η ∈ fairBalancingBad (support i) :=
    fairBalancingBad_depends (support i) ω η
      (fun b hb => hagree b (Finset.mem_biUnion.mpr ⟨i, hi, hb⟩))
  constructor
  · intro h i hi hη
    exact h i hi ((hmem i hi).mpr hη)
  · intro h i hi hω
    exact h i hi ((hmem i hi).mp hω)

theorem outer_nonneighbor_supports_disjoint {I : Type uI} {Label : Type uLabel}
    [Fintype I] [DecidableEq I] [Fintype Label] [DecidableEq Label]
    (support : I → Finset Label)
    (i : I) (T : Finset I) (hiT : i ∉ T)
    (hTN : Disjoint T (outerNeighbors support i)) :
    Disjoint (support i) (T.biUnion support) := by
  classical
  apply Finset.disjoint_left.mpr
  intro b hbi hbT
  obtain ⟨j, hjT, hbj⟩ := Finset.mem_biUnion.mp hbT
  have hjne : j ≠ i := by
    intro h
    subst j
    exact hiT hjT
  have hjN : j ∈ outerNeighbors support i := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ j, hjne, Finset.not_disjoint_iff.mpr ⟨b, hbi, hbj⟩⟩
  exact Finset.disjoint_left.mp hTN hjT hjN

theorem exists_fair_balancing_coloring (support : I → Finset Label)
    (hsize : ∀ i, (100 : ℝ) ≤ (support i).card)
    (hincident : ∀ b,
      ∑ j ∈ Finset.univ.filter (fun j => b ∈ support j),
        Real.exp (-((support j).card : ℝ) / 32) ≤ 1 / 500) :
    ∃ color : Label → Bool, ∀ i b,
      (support i).card ≤ 4 * ((support i).filter fun a => color a = b).card := by
  classical
  let weight : (Label → Bool) → ℝ := FiniteProbability.bernoulliWeight (1 / 2)
  have hw : ∀ ω, 0 ≤ weight ω :=
    FiniteProbability.bernoulliWeight_nonneg (by norm_num) (by norm_num)
  have htotal : ∑ ω, weight ω = 1 := FiniteProbability.sum_bernoulliWeight _
  let P := FiniteLocalLemma.Probability.ofWeights weight hw htotal
  let bad : I → Finset (Label → Bool) := fun i => fairBalancingBad (support i)
  have htail : ∀ i, P.mass (bad i) ≤
      2 * Real.exp (-((support i).card : ℝ) / 8) := by
    intro i
    exact fair_balancing_tail (support i)
  have hindependent : ∀ i T, i ∉ T → Disjoint T (outerNeighbors support i) →
      P.mass (bad i ∩ FiniteLocalLemma.avoid bad T) =
        P.mass (bad i) * P.mass (FiniteLocalLemma.avoid bad T) := by
    intro i T hiT hTN
    exact FiniteProbability.prob_inter_of_disjoint_supports (1 / 2)
      (bad i) (FiniteLocalLemma.avoid bad T) (support i) (T.biUnion support)
      (fairBalancingBad_depends (support i)) (outer_avoid_depends support T)
      (outer_nonneighbor_supports_disjoint support i T hiT hTN)
  obtain ⟨color, hcolor⟩ := outer_exists_avoiding_from_incidence P bad support
    hsize htail hindependent hincident
  refine ⟨color, ?_⟩
  intro i b
  apply Nat.le_of_not_gt
  intro hbad
  exact hcolor i (mem_fairBalancingBad (support i) color |>.mpr ⟨b, hbad⟩)

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI


namespace QuantitativeVanDerWaerden

open scoped BigOperators

theorem outer_sum_incident_split
    {G : Type uG} {L : Type uL} {Label : Type uLabel} [Fintype G] [Fintype L] [DecidableEq G] [DecidableEq L]
    [DecidableEq Label] (gsupport : G → Finset Label) (lsupport : L → Finset Label)
    (b : Label) :
    (∑ i ∈ Finset.univ.filter (fun i : G ⊕ L => b ∈ Sum.elim gsupport lsupport i),
      Real.exp (-((Sum.elim gsupport lsupport i).card : ℝ) / 32)) =
      (∑ i ∈ Finset.univ.filter (fun i => b ∈ gsupport i),
        Real.exp (-((gsupport i).card : ℝ) / 32)) +
      (∑ i ∈ Finset.univ.filter (fun i => b ∈ lsupport i),
        Real.exp (-((lsupport i).card : ℝ) / 32)) := by
  classical
  simp only [Finset.sum_filter, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  apply congrArg₂ (fun x y : ℝ => x + y)
  · refine Finset.sum_congr ?_ ?_
    · apply Finset.ext
      intro i
      simp only [Finset.mem_univ]
    · intro i _
      by_cases hi : b ∈ gsupport i <;> simp only [hi, ite_true, ite_false]
  · refine Finset.sum_congr ?_ ?_
    · apply Finset.ext
      intro i
      simp only [Finset.mem_univ]
    · intro i _
      by_cases hi : b ∈ lsupport i <;> simp only [hi, ite_true, ite_false]

theorem exists_outer_coloring_of_family_counts
    {G : Type uG} {L : Type uL} {Label : Type uLabel} [Fintype G] [Fintype L] [DecidableEq G] [DecidableEq L]
    [Fintype Label] [DecidableEq Label]
    (gsupport : G → Finset Label) (lsupport : L → Finset Label)
    (period : L → ℕ) (periods : Finset ℕ) (countBound : ℕ → ℕ)
    (rowLower : ℝ) (hrowLower : 100 ≤ rowLower)
    (hgsize : ∀ i, rowLower ≤ ((gsupport i).card : ℝ))
    (hlsize : ∀ i, (100 : ℝ) ≤ (lsupport i).card)
    (hperiod : ∀ i, period i ∈ periods)
    (hhalf : ∀ i, period i ≤ 2 * (lsupport i).card)
    (hcount : ∀ b h,
      (Finset.univ.filter (fun i => b ∈ lsupport i ∧ period i = h)).card ≤ countBound h)
    (hbudget : (Fintype.card G : ℝ) * Real.exp (-rowLower / 32) +
      (∑ h ∈ periods, (countBound h : ℝ) * Real.exp (-(h : ℝ) / 64)) ≤ 1 / 500) :
    ∃ color : Label → Bool,
      (∀ i b, (gsupport i).card ≤
        4 * ((gsupport i).filter fun a => color a = b).card) ∧
      (∀ i b, (lsupport i).card ≤
        4 * ((lsupport i).filter fun a => color a = b).card) := by
  classical
  let support : G ⊕ L → Finset Label := Sum.elim gsupport lsupport
  have hsize : ∀ i, (100 : ℝ) ≤ (support i).card := by
    intro i
    cases i with
    | inl i => exact hrowLower.trans (hgsize i)
    | inr i => exact hlsize i
  have hincident : ∀ b,
      ∑ i ∈ Finset.univ.filter (fun i => b ∈ support i),
        Real.exp (-((support i).card : ℝ) / 32) ≤ 1 / 500 := by
    intro b
    have hglobal : (∑ i ∈ Finset.univ.filter (fun i => b ∈ gsupport i),
        Real.exp (-((gsupport i).card : ℝ) / 32)) ≤
        (Fintype.card G : ℝ) * Real.exp (-rowLower / 32) := by
      calc
        _ ≤ ∑ i : G, Real.exp (-((gsupport i).card : ℝ) / 32) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => (Real.exp_pos _).le)
        _ ≤ (Fintype.card G : ℝ) * Real.exp (-rowLower / 32) := by
          simpa only [Finset.card_univ] using
            outer_total_weight_bound Finset.univ gsupport rowLower (fun i _ => hgsize i)
    have hlocal := outer_local_incident_bound lsupport period periods countBound
      hperiod hhalf hcount b
    dsimp only [support]
    rw [outer_sum_incident_split]
    exact (add_le_add hglobal hlocal).trans hbudget
  obtain ⟨color, hcolor⟩ := exists_fair_balancing_coloring support hsize hincident
  exact ⟨color, (fun i b => hcolor (Sum.inl i) b),
    (fun i b => hcolor (Sum.inr i) b)⟩

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Literal support of recorded patterns

A pattern records either a label or `none` at each position. Its support is
exactly the set of recorded labels. If no recorded label occurs twice, counting
labels is equivalent to counting regular positions, also after restricting to
one color. Thus quarter-balancing the support balances the actual positions.
-/


namespace QuantitativeVanDerWaerden.RecordedSupport

variable {Label : Type uLabel} [Fintype Label] [DecidableEq Label] {h : ℕ}

/-- The labels literally recorded by the pattern. -/
noncomputable def support (p : Fin h → Option Label) : Finset Label := by
  classical
  exact Finset.univ.filter fun β => ∃ j, p j = some β

/-- A position is regular exactly when the pattern records a label there. -/
noncomputable def regularPositions (p : Fin h → Option Label) : Finset (Fin h) := by
  classical
  exact Finset.univ.filter fun j => p j ≠ none

/-- Positions at which the recorded label satisfies a specified predicate. -/
noncomputable def positionsWhere (p : Fin h → Option Label) (q : Label → Prop) :
    Finset (Fin h) := by
  classical
  exact Finset.univ.filter fun j => ∃ β, p j = some β ∧ q β

/-- Actual positions carrying a label of the specified color. -/
noncomputable def coloredPositions (p : Fin h → Option Label)
    (color : Label → Bool) (b : Bool) : Finset (Fin h) :=
  positionsWhere p fun β => color β = b

/-- No literal label is recorded at two different positions. -/
def LabelsInjective (p : Fin h → Option Label) : Prop :=
  ∀ a b β, p a = some β → p b = some β → a = b

@[simp] theorem mem_support (p : Fin h → Option Label) (β : Label) :
    β ∈ support p ↔ ∃ j, p j = some β := by
  classical
  simp [support]

@[simp] theorem mem_regularPositions {Label : Type uLabel} [Fintype Label] [DecidableEq Label] {h : ℕ}
    (p : Fin h → Option Label) (j : Fin h) :
    j ∈ regularPositions p ↔ p j ≠ none := by
  classical
  simp [regularPositions]

@[simp] theorem mem_positionsWhere {Label : Type uLabel} [Fintype Label] [DecidableEq Label] {h : ℕ}
    (p : Fin h → Option Label)
    (q : Label → Prop) (j : Fin h) :
    j ∈ positionsWhere p q ↔ ∃ β, p j = some β ∧ q β := by
  classical
  simp [positionsWhere]

@[simp] theorem mem_coloredPositions (p : Fin h → Option Label)
    (color : Label → Bool) (b : Bool) (j : Fin h) :
    j ∈ coloredPositions p color b ↔ ∃ β, p j = some β ∧ color β = b := by
  exact mem_positionsWhere p (fun β => color β = b) j

theorem positionsWhere_true (p : Fin h → Option Label) :
    positionsWhere p (fun _ => True) = regularPositions p := by
  classical
  ext j
  simp only [mem_positionsWhere, mem_regularPositions]
  cases hp : p j <;> simp

theorem positionsWhere_subset_regularPositions (p : Fin h → Option Label)
    (q : Label → Prop) : positionsWhere p q ⊆ regularPositions p := by
  intro j hj
  obtain ⟨β, hβ, _⟩ := (mem_positionsWhere p q j).mp hj
  apply (mem_regularPositions p j).mpr
  rw [hβ]
  exact Option.some_ne_none β

/-- Every subset of the recorded labels has exactly its number of positions.
The hypothesis excludes repetition only for recorded labels; `none` may occur
arbitrarily often. -/
theorem support_filter_card_eq (p : Fin h → Option Label) (hinj : LabelsInjective p)
    (q : Label → Prop) [DecidablePred q] :
    ((support p).filter q).card = (positionsWhere p q).card := by
  classical
  let pos : ∀ β ∈ support p, Fin h := fun β hβ =>
    Classical.choose ((mem_support p β).mp hβ)
  have hpos : ∀ β (hβ : β ∈ support p), p (pos β hβ) = some β := by
    intro β hβ
    exact Classical.choose_spec ((mem_support p β).mp hβ)
  apply Finset.card_bij (fun β hβ => pos β (Finset.mem_filter.mp hβ).1)
  · intro β hβ
    apply (mem_positionsWhere p q _).mpr
    exact ⟨β, hpos β (Finset.mem_filter.mp hβ).1, (Finset.mem_filter.mp hβ).2⟩
  · intro β hβ γ hγ heq
    apply Option.some.inj
    exact (hpos β (Finset.mem_filter.mp hβ).1).symm.trans
      ((congrArg p heq).trans (hpos γ (Finset.mem_filter.mp hγ).1))
  · intro j hj
    obtain ⟨β, hjβ, hqβ⟩ := (mem_positionsWhere p q j).mp hj
    have hβ : β ∈ (support p).filter q :=
      Finset.mem_filter.mpr ⟨(mem_support p β).mpr ⟨j, hjβ⟩, hqβ⟩
    exact ⟨β, hβ, hinj _ _ β (hpos β (Finset.mem_filter.mp hβ).1) hjβ⟩

/-- Distinct recorded labels are in bijection with regular positions. -/
theorem support_card_eq (p : Fin h → Option Label) (hinj : LabelsInjective p) :
    (support p).card = (regularPositions p).card := by
  simpa only [Finset.filter_true, positionsWhere_true] using
    support_filter_card_eq p hinj (fun _ => True)

/-- The bijection also preserves each literal color class. -/
theorem support_color_card_eq (p : Fin h → Option Label) (hinj : LabelsInjective p)
    (color : Label → Bool) (b : Bool) :
    ((support p).filter fun β => color β = b).card =
      (coloredPositions p color b).card :=
  support_filter_card_eq p hinj (fun β => color β = b)

/-- Quarter-balancing the support gives quarter-balancing of regular positions. -/
theorem regular_card_le_four_colored (p : Fin h → Option Label)
    (hinj : LabelsInjective p) (color : Label → Bool) (b : Bool)
    (hbalance : (support p).card ≤ 4 * ((support p).filter fun β => color β = b).card) :
    (regularPositions p).card ≤ 4 * (coloredPositions p color b).card := by
  rw [← support_card_eq p hinj, ← support_color_card_eq p hinj color b]
  exact hbalance

/-- If at least half the positions are regular, each balanced color occupies
at least an eighth of the whole pattern. -/
theorem length_le_eight_colored (p : Fin h → Option Label)
    (hinj : LabelsInjective p) (color : Label → Bool) (b : Bool)
    (hregular : h ≤ 2 * (regularPositions p).card)
    (hbalance : (support p).card ≤ 4 * ((support p).filter fun β => color β = b).card) :
    h ≤ 8 * (coloredPositions p color b).card := by
  calc
    h ≤ 2 * (regularPositions p).card := hregular
    _ ≤ 2 * (4 * (coloredPositions p color b).card) :=
      Nat.mul_le_mul_left 2 (regular_card_le_four_colored p hinj color b hbalance)
    _ = 8 * (coloredPositions p color b).card := by rw [← Nat.mul_assoc]

end QuantitativeVanDerWaerden.RecordedSupport

end OAI
end
end

section
section
namespace OAI

/-!
# Simultaneous balancing of words and recorded local patterns

The global tests are constructed from the actual light-position fibers. The
local tests retain precisely the labels recorded by their Option-valued words.
The only counting inputs are the finite word and anchored-pattern bounds;
all probability, row partitioning and support-to-position conversions are proved.
-/


namespace QuantitativeVanDerWaerden

open scoped BigOperators

theorem exists_outer_word_pattern_coloring
    {Label : Type uLabel} {I : Type uI} [Fintype Label] [DecidableEq Label] [Fintype I] [DecidableEq I]
    {k : ℕ} (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (words : Finset (Fin k → Label))
    (period : I → ℕ) (pattern : ∀ i, Fin (period i) → Option Label)
    (periods : Finset ℕ) (countBound : ℕ → ℕ)
    (hrow : (100 : ℝ) ≤ (M : ℝ) / 10 - 1)
    (hperiod : ∀ i, period i ∈ periods)
    (hperiodLower : ∀ i, 200 ≤ period i)
    (hinj : ∀ i, RecordedSupport.LabelsInjective (pattern i))
    (hregular : ∀ i, period i ≤ 2 * (RecordedSupport.regularPositions (pattern i)).card)
    (hcount : ∀ b h,
      (Finset.univ.filter (fun i => (∃ j, pattern i j = some b) ∧ period i = h)).card ≤
        countBound h)
    (hbudget : ((k * words.card : ℕ) : ℝ) * Real.exp (-((M : ℝ) / 10 - 1) / 32) +
      (∑ h ∈ periods, (countBound h : ℝ) * Real.exp (-(h : ℝ) / 64)) ≤ 1 / 500) :
    ∃ color : Label → Bool,
      (∀ word ∈ words, k ≤ 10 * (OuterWordTests.lightPositions M word).card → ∀ b,
        (OuterWordTests.lightPositions M word).card ≤
          4 * ((OuterWordTests.lightPositions M word).filter
            fun j => color (word j) = b).card) ∧
      (∀ i b, (RecordedSupport.regularPositions (pattern i)).card ≤
        4 * (RecordedSupport.coloredPositions (pattern i) color b).card) := by
  classical
  let gsupport := OuterWordTests.support M hM hMk words
  let lsupport : I → Finset Label := fun i => RecordedSupport.support (pattern i)
  have hlsize : ∀ i, (100 : ℝ) ≤ (lsupport i).card := by
    intro i
    have heq := RecordedSupport.support_card_eq (pattern i) (hinj i)
    have hn : 100 ≤ (lsupport i).card := by
      dsimp only [lsupport]
      rw [heq]
      have hl := hperiodLower i
      have hr := hregular i
      omega
    exact_mod_cast hn
  have hhalf : ∀ i, period i ≤ 2 * (lsupport i).card := by
    intro i
    dsimp only [lsupport]
    rw [RecordedSupport.support_card_eq (pattern i) (hinj i)]
    exact hregular i
  have hlocalcount : ∀ b h,
      (Finset.univ.filter (fun i => b ∈ lsupport i ∧ period i = h)).card ≤ countBound h := by
    intro b h
    simpa only [lsupport, RecordedSupport.mem_support] using hcount b h
  have hbudget' : (Fintype.card (OuterWordTests.TestIndex M words) : ℝ) *
      Real.exp (-((M : ℝ) / 10 - 1) / 32) +
      (∑ h ∈ periods, (countBound h : ℝ) * Real.exp (-(h : ℝ) / 64)) ≤ 1 / 500 := by
    have hc : (Fintype.card (OuterWordTests.TestIndex M words) : ℝ) ≤
        ((k * words.card : ℕ) : ℝ) := by
      exact_mod_cast OuterWordTests.testIndex_card_le M words
    exact (add_le_add_left
      (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le) _).trans hbudget
  obtain ⟨color, hg, hl⟩ := exists_outer_coloring_of_family_counts gsupport lsupport
    period periods countBound ((M : ℝ) / 10 - 1) hrow
    (OuterWordTests.support_card_real_lower M hM hMk words) hlsize hperiod hhalf
    hlocalcount hbudget'
  refine ⟨color, OuterWordTests.supports_balance_words M hM hMk words color hg, ?_⟩
  intro i b
  exact RecordedSupport.regular_card_le_four_colored (pattern i) (hinj i) color b (hl i b)

/-- The light-position alternative already gives the required whole-word
frequency bound, with slack from one fortieth to one hundredth. -/
theorem rich_of_light_balanced {Label : Type uLabel} [DecidableEq Label] {k M : ℕ}
    (word : Fin k → Label) (color : Label → Bool)
    (hlight : k ≤ 10 * (OuterWordTests.lightPositions M word).card)
    (hbalance : ∀ b, (OuterWordTests.lightPositions M word).card ≤
      4 * ((OuterWordTests.lightPositions M word).filter fun j => color (word j) = b).card) :
    ∀ b, k ≤ 100 * (Finset.univ.filter fun j => color (word j) = b).card := by
  classical
  intro b
  have hsub : (OuterWordTests.lightPositions M word).filter (fun j => color (word j) = b) ⊆
      Finset.univ.filter (fun j => color (word j) = b) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2⟩
  have hc := Finset.card_le_card hsub
  have hb := hbalance b
  omega

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Eligibility of literal recorded supports

The recorded-word mask agrees exactly with geometric regularity. Consequently,
the injectivity and density clauses of geometric eligibility provide the
hypotheses used when transferring support balancing to actual positions.
-/

namespace QuantitativeVanDerWaerden.AnchoredPatterns

variable {D h : ℕ}

theorem recordedWord_ne_none_iff (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ)
    (R : Realization D) (lambda : ℕ) (t : Fin D → Fin h) (z : Fin h) :
    recordedWord n hn A eta R lambda t z ≠ none ↔ regular eta R lambda t z := by
  rw [Option.ne_none_iff_exists']
  constructor
  · rintro ⟨β, hβ⟩
    exact ((recordedWord_eq_some_iff n hn A eta R lambda t z β).mp hβ).1
  · intro hz
    refine ⟨fullLabel n hn A R lambda t z, ?_⟩
    exact (recordedWord_eq_some_iff n hn A eta R lambda t z _).mpr ⟨hz, rfl⟩

/-- The literal mask and geometric regularity select the same positions. -/
theorem recordedWord_regularPositions_eq (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh)
    (eta : ℝ) (R : Realization D) (lambda : ℕ) (t : Fin D → Fin h) :
    RecordedSupport.regularPositions (recordedWord n hn A eta R lambda t) =
      regularPositions eta R lambda t := by
  classical
  ext z
  simp only [RecordedSupport.mem_regularPositions, recordedWord_ne_none_iff,
    regularPositions, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Geometric injectivity gives uniqueness of every recorded full label. -/
theorem EligibleRealization.recordedWord_labelsInjective
    {n : ℕ} {hn : 0 < n} {A : AdaptiveMesh} {eta : ℝ} {lambda : ℕ}
    {t : Fin D → Fin h} {R : Realization D}
    (hR : EligibleRealization n hn A eta lambda t R) :
    RecordedSupport.LabelsInjective (recordedWord n hn A eta R lambda t) := by
  intro z z' β hz hz'
  obtain ⟨hzreg, hzlabel⟩ :=
    (recordedWord_eq_some_iff n hn A eta R lambda t z β).mp hz
  obtain ⟨hz'reg, hz'label⟩ :=
    (recordedWord_eq_some_iff n hn A eta R lambda t z' β).mp hz'
  exact hR.regular_injective z z' hzreg hz'reg (hzlabel.trans hz'label.symm)

/-- The eligibility density condition is a literal recorded-position bound. -/
theorem EligibleRealization.recordedWord_regular_many
    {n : ℕ} {hn : 0 < n} {A : AdaptiveMesh} {eta : ℝ} {lambda : ℕ}
    {t : Fin D → Fin h} {R : Realization D}
    (hR : EligibleRealization n hn A eta lambda t R) :
    h ≤ 2 * (RecordedSupport.regularPositions
      (recordedWord n hn A eta R lambda t)).card := by
  rw [recordedWord_regularPositions_eq]
  exact hR.regular_many

/-- Recorded-label uniqueness depends only on the eligible word, regardless
of which eligible realization witnesses it. -/
theorem eligibleOptionFullLabel_labelsInjective
    {n : ℕ} {hn : 0 < n} {A : AdaptiveMesh} {eta : ℝ} {lambda : ℕ}
    {t : Fin D → Fin h} {word : Fin h → Option (FullLabel D (Fin n) A.Label)}
    (hword : eligibleOptionFullLabel n hn A eta lambda t word) :
    RecordedSupport.LabelsInjective word := by
  obtain ⟨R, hR, hrecorded⟩ := hword
  rw [← hrecorded]
  exact hR.recordedWord_labelsInjective

/-- At least half the positions of every eligible word carry a literal label. -/
theorem eligibleOptionFullLabel_regular_many
    {n : ℕ} {hn : 0 < n} {A : AdaptiveMesh} {eta : ℝ} {lambda : ℕ}
    {t : Fin D → Fin h} {word : Fin h → Option (FullLabel D (Fin n) A.Label)}
    (hword : eligibleOptionFullLabel n hn A eta lambda t word) :
    h ≤ 2 * (RecordedSupport.regularPositions word).card := by
  obtain ⟨R, hR, hrecorded⟩ := hword
  rw [← hrecorded]
  exact hR.recordedWord_regular_many

end QuantitativeVanDerWaerden.AnchoredPatterns

end OAI
end
end

section
section
namespace OAI

/-! Actual lifted mesh endpoints and finite spacing bounds.  Endpoint sets
are constructed from the exponential mesh, not supplied as count hypotheses. -/

namespace QuantitativeVanDerWaerden

/-- The elementary one-dimensional packing inequality, with both end points
included.  This formulation has no rounding loss in subsequent estimates. -/
theorem finite_spacing_bound (s : Finset ℝ) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∀ u v : ℝ, u ≤ v →
    (∀ x ∈ s, u ≤ x ∧ x ≤ v) →
    (∀ x ∈ s, ∀ y ∈ s, x < y → δ ≤ y - x) →
    (s.card : ℝ) * δ ≤ v - u + δ := by
  classical
  induction s using Finset.induction_on_min with
  | empty => intro u v huv _ _; simp; linarith
  | @insert a s hmin ih =>
    intro u v huv hmem hsep
    have ha := hmem a (Finset.mem_insert_self _ _)
    have hnot : a ∉ s := by intro h; exact (lt_irrefl a) (hmin a h)
    rw [Finset.card_insert_of_notMem hnot, Nat.cast_add, Nat.cast_one, add_mul]
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst s
      simp
      linarith
    · obtain ⟨b, hb⟩ := hs
      have hgap := hsep a (Finset.mem_insert_self _ _) b
        (Finset.mem_insert_of_mem hb) (hmin b hb)
      have hbv := (hmem b (Finset.mem_insert_of_mem hb)).2
      have hsmall := ih (a + δ) v (by linarith)
        (by
          intro x hx
          have hxv := (hmem x (Finset.mem_insert_of_mem hx)).2
          have hxgap := hsep a (Finset.mem_insert_self _ _) x
            (Finset.mem_insert_of_mem hx) (hmin x hx)
          exact ⟨by linarith, hxv⟩)
        (fun x hx y hy hxy => hsep x (Finset.mem_insert_of_mem hx)
          y (Finset.mem_insert_of_mem hy) hxy)
      linarith

noncomputable def integerTranslatesBetween (r u v : ℝ) : Finset ℝ := by
  classical
  exact (Finset.Icc (⌈u - r⌉ : ℤ) ⌊v - r⌋).image (fun z : ℤ => r + z)

theorem mem_integerTranslatesBetween (r u v x : ℝ) :
    x ∈ integerTranslatesBetween r u v ↔
      u ≤ x ∧ x ≤ v ∧ ∃ z : ℤ, x = r + z := by
  classical
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have h := Finset.mem_Icc.mp hz
    have hl := Int.ceil_le.mp h.1
    have hu := Int.le_floor.mp h.2
    exact ⟨by linarith, by linarith, z, rfl⟩
  · rintro ⟨hlo, hhi, z, rfl⟩
    exact Finset.mem_image.mpr ⟨z, Finset.mem_Icc.mpr
      ⟨Int.ceil_le.mpr (by linarith), Int.le_floor.mpr (by linarith)⟩, rfl⟩

theorem integerTranslatesBetween_card (r u v : ℝ) (huv : u ≤ v)
    (hlen : v - u < 1) : (integerTranslatesBetween r u v).card ≤ 1 := by
  classical
  have hp := finite_spacing_bound (integerTranslatesBetween r u v) 1 (by norm_num)
    u v huv
    (by
      intro x hx
      have h := (mem_integerTranslatesBetween r u v x).mp hx
      exact ⟨h.1, h.2.1⟩)
    (by
      intro x hx y hy hxy
      obtain ⟨_, _, z, rfl⟩ := (mem_integerTranslatesBetween r u v x).mp hx
      obtain ⟨_, _, w, rfl⟩ := (mem_integerTranslatesBetween r u v y).mp hy
      have hzw : (z : ℝ) < w := by linarith
      have hzw' : z < w := by exact_mod_cast hzw
      have hgap : (1 : ℝ) ≤ (w : ℝ) - z := by
        exact_mod_cast (show (1 : ℤ) ≤ w - z by omega)
      linarith)
  have hcard : ((integerTranslatesBetween r u v).card : ℝ) < 2 := by
    simpa only [mul_one] using lt_of_le_of_lt hp (by linarith)
  have hn : (integerTranslatesBetween r u v).card < 2 := by exact_mod_cast hcard
  omega

namespace AdaptiveMesh

variable (A : AdaptiveMesh)

theorem left_lt_half (i : A.Label) : A.left i < 1 / 2 := by
  have hw := A.width_pos i
  have hr := A.right_le_half i
  dsimp [width] at hw
  linarith

theorem contains_left (i : A.Label) : A.Contains i (A.left i) :=
  ⟨le_refl _, sub_pos.mp (A.width_pos i)⟩

theorem centered_of_lift_mem (i : A.Label) (z : ℤ) {x : ℝ}
    (hx : A.Contains i (x - z)) : centered x = x - z := by
  have hl := (A.left_ge_neg_half i).trans hx.1
  have hu := hx.2.trans_le (A.right_le_half i)
  have hc := centered_add_int (x - z) z
  rw [centered_eq_of_mem hl hu] at hc
  simpa only [sub_add_cancel] using hc

theorem label_of_lift_mem (i : A.Label) (z : ℤ) {x : ℝ}
    (hx : A.Contains i (x - z)) : A.meshLabel x = i := by
  apply (A.meshLabel_eq_iff x i).mpr
  rw [A.centered_of_lift_mem i z hx]
  exact hx

theorem lifted_unique (i j : A.Label) (z w : ℤ) {x : ℝ}
    (hi : A.Contains i (x - z)) (hj : A.Contains j (x - w)) :
    i = j ∧ z = w := by
  refine ⟨(A.label_of_lift_mem i z hi).symm.trans (A.label_of_lift_mem j w hj), ?_⟩
  have hzi := A.centered_of_lift_mem i z hi
  have hwj := A.centered_of_lift_mem j w hj
  have he : (z : ℝ) = w := by linarith
  exact_mod_cast he

/-- Every real lift belongs to an actual half-open lifted mesh cell. -/
theorem exists_lift_mem (x : ℝ) :
    ∃ (i : A.Label) (z : ℤ), A.Contains i (x - z) := by
  refine ⟨A.meshLabel x, ⌊x + 1 / 2⌋, ?_⟩
  exact A.meshLabel_contains x

theorem lifted_endpoint_gap (i j : A.Label) (z w : ℤ)
    (h : A.left i + z < A.left j + w) :
    A.right i + z ≤ A.left j + w := by
  by_contra hnot
  have hi : A.Contains i (A.left j + w - z) := ⟨by linarith, by linarith⟩
  have hj : A.Contains j (A.left j + w - w) := by
    simpa only [add_sub_cancel_right] using A.contains_left j
  obtain ⟨hij, hzw⟩ := A.lifted_unique i j z w hi hj
  subst j
  subst w
  exact (lt_irrefl _) h

theorem right_is_lifted_endpoint (i : A.Label) (z : ℤ) :
    ∃ (j : A.Label) (w : ℤ), A.right i + z = A.left j + w := by
  obtain ⟨j, w, hj⟩ := A.exists_lift_mem (A.right i + z)
  have hjlo : A.left j + w ≤ A.right i + z := by linarith [hj.1]
  have hjhi : A.right i + z < A.right j + w := by linarith [hj.2]
  by_contra hnot
  have hstrict : A.left j + w < A.right i + z := by
    apply lt_of_le_of_ne hjlo
    intro he
    exact hnot ⟨j, w, he.symm⟩
  have hipos : A.left i + z < A.right i + z := by
    have hw := A.width_pos i
    dsimp [width] at hw
    linarith
  let p := (max (A.left i + z) (A.left j + w) + (A.right i + z)) / 2
  have hmax : max (A.left i + z) (A.left j + w) < A.right i + z :=
    max_lt hipos hstrict
  have hpi : A.Contains i (p - z) := by
    have hm := le_max_left (A.left i + z) (A.left j + w)
    dsimp [Contains, p]
    constructor <;> linarith
  have hpj : A.Contains j (p - w) := by
    have hm := le_max_right (A.left i + z) (A.left j + w)
    dsimp [Contains, p]
    constructor <;> linarith
  obtain ⟨hij, hzw⟩ := A.lifted_unique i j z w hpi hpj
  subst j
  subst w
  exact (lt_irrefl _) hjhi

noncomputable def endpointsBetween (u v : ℝ) : Finset ℝ := by
  classical
  exact ((Finset.univ.product
    (Finset.Icc (⌈u - 1 / 2⌉ : ℤ) ⌊v + 1 / 2⌋)).image
      (fun p : A.Label × ℤ => A.left p.1 + p.2)).filter
        (fun x => u ≤ x ∧ x ≤ v)

theorem mem_endpointsBetween (u v x : ℝ) :
    x ∈ A.endpointsBetween u v ↔
      u ≤ x ∧ x ≤ v ∧ ∃ (i : A.Label) (z : ℤ), x = A.left i + z := by
  classical
  constructor
  · intro hx
    obtain ⟨himg, hlu, huv⟩ := Finset.mem_filter.mp hx
    obtain ⟨⟨i, z⟩, _, rfl⟩ := Finset.mem_image.mp himg
    exact ⟨hlu, huv, i, z, rfl⟩
  · rintro ⟨hux, hxv, i, z, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hux, hxv⟩
    apply Finset.mem_image.mpr
    refine ⟨(i, z), Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.ceil_le.mpr
      linarith [A.left_lt_half i]
    · apply Int.le_floor.mpr
      linarith [A.left_ge_neg_half i]

/-- The anchor's closed circle neighborhood, realized by one real interval.
An integer translate leaves every label and every width unchanged. -/
noncomputable def neighborhoodEndpoints (i : A.Label) (z : ℤ) : Finset ℝ :=
  A.endpointsBetween (A.left i + z - A.width i) (A.right i + z + A.width i)

theorem neighborhoodEndpoints_card (i : A.Label) (z : ℤ) :
    (A.neighborhoodEndpoints i z).card ≤ 49 := by
  classical
  let u := A.left i + z - A.width i
  let v := A.right i + z + A.width i
  have hw := A.width_pos i
  have huv : u ≤ v := by dsimp [u, v, width] at *; linarith
  have hpack := finite_spacing_bound (A.neighborhoodEndpoints i z)
    (A.width i / 16) (by positivity) u v huv
    (by
      intro x hx
      have h := (A.mem_endpointsBetween u v x).mp hx
      exact ⟨h.1, h.2.1⟩)
    (by
      intro x hx y hy hxy
      obtain ⟨hxlo, hxhi, j, w, rfl⟩ := (A.mem_endpointsBetween u v x).mp hx
      obtain ⟨_, _, k, t, rfl⟩ := (A.mem_endpointsBetween u v y).mp hy
      have hgap := A.lifted_endpoint_gap j k w t hxy
      have hjw := A.neighbor_width i j (le_refl _) (sub_pos.mp hw).le
        (le_refl _) (sub_pos.mp (A.width_pos j)).le
        ⟨z - w, by
          push_cast
          apply abs_le.mpr
          dsimp [u, v] at hxlo hxhi
          dsimp [width] at *
          constructor <;> linarith⟩
      dsimp [width] at hjw ⊢
      linarith)
  have hlen : v - u = 3 * A.width i := by dsimp [u, v, width]; ring
  rw [hlen] at hpack
  have hcard : ((A.neighborhoodEndpoints i z).card : ℝ) ≤ 49 := by
    nlinarith
  exact_mod_cast hcard

noncomputable def activeEndpoints (η u v : ℝ) : Finset ℝ := by
  classical
  exact (A.endpointsBetween u v).filter (fun x => η ≤ rho x)

/-- Active endpoints are separated globally, including across the circle cut:
the complete cell starting at the first endpoint lies before the second. -/
theorem activeEndpoints_spacing (η u v : ℝ) {x y : ℝ}
    (hx : x ∈ A.activeEndpoints η u v) (hy : y ∈ A.activeEndpoints η u v)
    (hxy : x < y) : A.H * η / 4 ≤ y - x := by
  classical
  obtain ⟨hxe, hxa⟩ := Finset.mem_filter.mp hx
  obtain ⟨hye, _⟩ := Finset.mem_filter.mp hy
  obtain ⟨_, _, i, z, rfl⟩ := (A.mem_endpointsBetween u v x).mp hxe
  obtain ⟨_, _, j, w, rfl⟩ := (A.mem_endpointsBetween u v y).mp hye
  rw [rho_add_int] at hxa
  have hw := A.width_bounds_of_closed_mem i (le_refl _)
    (sub_pos.mp (A.width_pos i)).le
  have hgap := A.lifted_endpoint_gap i j z w hxy
  have hH := A.H_pos
  have hmul := mul_le_mul_of_nonneg_left hxa (by positivity : 0 ≤ A.H / 4)
  have hap := mul_nonneg (by positivity : 0 ≤ A.H / 4) A.alpha_pos.le
  dsimp [width] at hw
  nlinarith [hw.1]

theorem activeEndpoints_card_bound (η u v : ℝ) (hη : 0 < η)
    (huv : u ≤ v) (hlen : v - u ≤ 4 * A.H) :
    ((A.activeEndpoints η u v).card : ℝ) ≤ 16 / η + 1 := by
  classical
  have hH := A.H_pos
  have hpack := finite_spacing_bound (A.activeEndpoints η u v)
    (A.H * η / 4) (by positivity) u v huv
    (by
      intro x hx
      have h := (A.mem_endpointsBetween u v x).mp (Finset.mem_filter.mp hx).1
      exact ⟨h.1, h.2.1⟩)
    (fun _ hx _ hy hxy => A.activeEndpoints_spacing η u v hx hy hxy)
  have hd : 0 < A.H * η / 4 := by positivity
  have he : (16 / η + 1) * (A.H * η / 4) = 4 * A.H + A.H * η / 4 := by
    field_simp
    ring
  apply (mul_le_mul_iff_left₀ hd).mp
  rw [he]
  linarith

/-- The only additional discontinuities of the truncated label are the two
threshold points in each period. Equality at either threshold is retained. -/
noncomputable def thresholdPoints (η u v : ℝ) : Finset ℝ :=
  integerTranslatesBetween (η - 1 / 2) u v ∪
    integerTranslatesBetween (1 / 2 - η) u v

noncomputable def truncatedBreakpoints (η u v : ℝ) : Finset ℝ :=
  A.activeEndpoints η u v ∪ thresholdPoints η u v

theorem thresholdPoints_card (η u v : ℝ) (huv : u ≤ v) (hlen : v - u < 1) :
    (thresholdPoints η u v).card ≤ 2 := by
  classical
  exact (Finset.card_union_le _ _).trans (by
    have hl := integerTranslatesBetween_card (η - 1 / 2) u v huv hlen
    have hr := integerTranslatesBetween_card (1 / 2 - η) u v huv hlen
    omega)

theorem truncatedBreakpoints_card_bound (η u v : ℝ) (hη : 0 < η)
    (huv : u ≤ v) (hlen : v - u ≤ 4 * A.H) :
    ((A.truncatedBreakpoints η u v).card : ℝ) ≤ 16 / η + 3 := by
  classical
  have hshort : v - u < 1 := by linarith [A.H_le]
  have he := A.activeEndpoints_card_bound η u v hη huv hlen
  have ht := thresholdPoints_card η u v huv hshort
  have hu := Finset.card_union_le (A.activeEndpoints η u v) (thresholdPoints η u v)
  have htr : ((thresholdPoints η u v).card : ℝ) ≤ 2 := by exact_mod_cast ht
  have hur : ((A.truncatedBreakpoints η u v).card : ℝ) ≤
      (A.activeEndpoints η u v).card + (thresholdPoints η u v).card := by
    exact_mod_cast hu
  linarith

theorem truncatedBreakpoints_card (D : ℕ) (hD : 0 < D) (u v : ℝ)
    (huv : u ≤ v) (hlen : v - u ≤ 4 * A.H) :
    (A.truncatedBreakpoints (1 / (1000 * (D : ℝ))) u v).card ≤ 16004 * D := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  have hc := A.truncatedBreakpoints_card_bound (1 / (1000 * (D : ℝ))) u v
    (by positivity) huv hlen
  have he : (16 : ℝ) / (1 / (1000 * (D : ℝ))) = 16000 * D := by
    field_simp
    ring
  rw [he] at hc
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hb : ((A.truncatedBreakpoints (1 / (1000 * (D : ℝ))) u v).card : ℝ) ≤
      16004 * D := by linarith
  exact_mod_cast hb

end AdaptiveMesh
end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-! Literal three-way breakpoint factorization. All sets below are the actual
endpoint/threshold sets from `AdaptiveMeshCounting`. In particular an equality
at a truncation threshold keeps the original half-open label. -/

namespace QuantitativeVanDerWaerden

theorem continuous_rho : Continuous rho := by
  have h : LipschitzWith 1 rho := LipschitzWith.of_dist_le_mul (fun x y => by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using rho_lipschitz x y)
  exact h.continuous

/-- Equal ternary signs exclude every closed-interval breakpoint when the
two evaluation points are distinct. Equality signs are essential here. -/
theorem no_breakpoint_of_same_signs {B : Finset ℝ} {x y : ℝ} (hxy : x < y)
    (hs : ∀ b ∈ B, ternarySign (x - b) = ternarySign (y - b)) :
    ∀ b ∈ B, ¬ (x ≤ b ∧ b ≤ y) := by
  intro b hb hbetween
  by_cases he : x = b
  · have hone : ternarySign (x - b) = 1 := (ternarySign_eq_one _).mpr (by rw [he]; ring)
    have hy : y - b = 0 := (ternarySign_eq_one _).mp ((hs b hb).symm.trans hone)
    linarith
  · have hx : x < b := lt_of_le_of_ne hbetween.1 he
    have hzero : ternarySign (x - b) = 0 := (ternarySign_eq_zero _).mpr (by linarith)
    have hy : y - b < 0 := (ternarySign_eq_zero _).mp ((hs b hb).symm.trans hzero)
    linarith [hbetween.2]

namespace AdaptiveMesh

variable (A : AdaptiveMesh)

theorem meshLabel_eq_of_no_endpoint {x y : ℝ} (hxy : x ≤ y)
    (hno : ∀ r : ℝ, x ≤ r → r ≤ y →
      ∀ (i : A.Label) (z : ℤ), r ≠ A.left i + z) :
    A.meshLabel x = A.meshLabel y := by
  obtain ⟨i, z, hi⟩ := A.exists_lift_mem x
  have hxlo : A.left i + z ≤ x := by linarith [hi.1]
  have hxhi : x < A.right i + z := by linarith [hi.2]
  have hyhi : y < A.right i + z := by
    by_contra hy
    obtain ⟨j, w, hj⟩ := A.right_is_lifted_endpoint i z
    exact hno (A.right i + z) hxhi.le (le_of_not_gt hy) j w hj
  have hycell : A.Contains i (y - z) := ⟨by linarith, by linarith⟩
  exact (A.label_of_lift_mem i z hi).trans (A.label_of_lift_mem i z hycell).symm

theorem endpoints_determine_label (u v : ℝ) {x y : ℝ}
    (hx : u ≤ x ∧ x ≤ v) (hy : u ≤ y ∧ y ≤ v)
    (hs : ∀ b ∈ A.endpointsBetween u v,
      ternarySign (x - b) = ternarySign (y - b)) : A.meshLabel x = A.meshLabel y := by
  have hordered : ∀ p q : ℝ, u ≤ p ∧ p ≤ v → u ≤ q ∧ q ≤ v → p < q →
      (∀ b ∈ A.endpointsBetween u v, ternarySign (p - b) = ternarySign (q - b)) →
      A.meshLabel p = A.meshLabel q := by
    intro p q hp hq hpq hsign
    have hnone := no_breakpoint_of_same_signs hpq hsign
    apply A.meshLabel_eq_of_no_endpoint hpq.le
    intro r hpr hrq i z he
    have hr : r ∈ A.endpointsBetween u v := (A.mem_endpointsBetween u v r).mpr
      ⟨hp.1.trans hpr, hrq.trans hq.2, i, z, he⟩
    exact hnone r hr ⟨hpr, hrq⟩
  rcases lt_trichotomy x y with h | h | h
  · exact hordered x y hx hy h hs
  · rw [h]
  · exact (hordered y x hy hx h (fun b hb => (hs b hb).symm)).symm

noncomputable def truncatedLabel (η x : ℝ) : Option A.Label := by
  classical
  exact if η ≤ rho x then some (A.meshLabel x) else none

theorem truncatedLabel_eq_none_iff (η x : ℝ) :
    A.truncatedLabel η x = none ↔ rho x < η := by
  classical
  simp [truncatedLabel, not_le]

theorem truncatedLabel_add_int (η x : ℝ) (z : ℤ) :
    A.truncatedLabel η (x + z) = A.truncatedLabel η x := by
  classical
  simp only [truncatedLabel, rho_add_int, A.meshLabel_add_int]

theorem mem_thresholdPoints_of_rho_eq (η u v x : ℝ)
    (hx : u ≤ x ∧ x ≤ v) (he : rho x = η) : x ∈ thresholdPoints η u v := by
  classical
  let z : ℤ := ⌊x + 1 / 2⌋
  have hrep : centered x = x - z := rfl
  have hr : 1 / 2 - |centered x| = η := he
  rcases le_total (centered x) 0 with hn | hp
  · rw [abs_of_nonpos hn] at hr
    apply Finset.mem_union_left
    apply (mem_integerTranslatesBetween (η - 1 / 2) u v x).mpr
    exact ⟨hx.1, hx.2, z, by linarith⟩
  · rw [abs_of_nonneg hp] at hr
    apply Finset.mem_union_right
    apply (mem_integerTranslatesBetween (1 / 2 - η) u v x).mpr
    exact ⟨hx.1, hx.2, z, by linarith⟩

theorem truncatedBreakpoints_determine_label (η u v : ℝ) {x y : ℝ}
    (hx : u ≤ x ∧ x ≤ v) (hy : u ≤ y ∧ y ≤ v)
    (hs : ∀ b ∈ A.truncatedBreakpoints η u v,
      ternarySign (x - b) = ternarySign (y - b)) :
    A.truncatedLabel η x = A.truncatedLabel η y := by
  classical
  have hordered : ∀ p q : ℝ, u ≤ p ∧ p ≤ v → u ≤ q ∧ q ≤ v → p < q →
      (∀ b ∈ A.truncatedBreakpoints η u v,
        ternarySign (p - b) = ternarySign (q - b)) →
      A.truncatedLabel η p = A.truncatedLabel η q := by
    intro p q hp hq hpq hsign
    have hnone := no_breakpoint_of_same_signs hpq hsign
    have hthreshold : ∀ b : ℝ, p ≤ b → b ≤ q → rho b ≠ η := by
      intro b hpb hbq he
      have hb := mem_thresholdPoints_of_rho_eq η u v b
        ⟨hp.1.trans hpb, hbq.trans hq.2⟩ he
      exact hnone b (Finset.mem_union_right _ hb) ⟨hpb, hbq⟩
    have hactive : η ≤ rho p ↔ η ≤ rho q := by
      constructor
      · intro hpactive
        apply le_of_not_gt
        intro hqactive
        obtain ⟨b, hb, he⟩ := intermediate_value_Icc' hpq.le continuous_rho.continuousOn
          (show η ∈ Set.Icc (rho q) (rho p) from ⟨hqactive.le, hpactive⟩)
        exact hthreshold b hb.1 hb.2 he
      · intro hqactive
        apply le_of_not_gt
        intro hpactive
        obtain ⟨b, hb, he⟩ := intermediate_value_Icc hpq.le continuous_rho.continuousOn
          (show η ∈ Set.Icc (rho p) (rho q) from ⟨hpactive.le, hqactive⟩)
        exact hthreshold b hb.1 hb.2 he
    by_cases hpactive : η ≤ rho p
    · have hqactive := hactive.mp hpactive
      have hallactive : ∀ b : ℝ, p ≤ b → b ≤ q → η ≤ rho b := by
        intro b hpb hbq
        apply le_of_not_gt
        intro hbactive
        obtain ⟨t, ht, he⟩ := intermediate_value_Icc' hpb continuous_rho.continuousOn
          (show η ∈ Set.Icc (rho b) (rho p) from ⟨hbactive.le, hpactive⟩)
        exact hthreshold t ht.1 (ht.2.trans hbq) he
      have hlabel : A.meshLabel p = A.meshLabel q := by
        apply A.meshLabel_eq_of_no_endpoint hpq.le
        intro b hpb hbq i z he
        have hb : b ∈ A.activeEndpoints η u v := Finset.mem_filter.mpr
          ⟨(A.mem_endpointsBetween u v b).mpr
            ⟨hp.1.trans hpb, hbq.trans hq.2, i, z, he⟩,
            hallactive b hpb hbq⟩
        exact hnone b (Finset.mem_union_left _ hb) ⟨hpb, hbq⟩
      simp only [truncatedLabel, ite_eq_left hpactive, ite_eq_left hqactive, hlabel]
    · have hqactive : ¬ η ≤ rho q := fun h => hpactive (hactive.mpr h)
      simp only [truncatedLabel, ite_eq_right hpactive, ite_eq_right hqactive]
  rcases lt_trichotomy x y with h | h | h
  · exact hordered x y hx hy h hs
  · rw [h]
  · exact (hordered y x hy hx h (fun b hb => (hs b hb).symm)).symm

/-- A fixed 49-point breakpoint set for the closed neighborhood of an anchor
cell. It is chosen before either free affine parameter is selected. -/
theorem stationary_breakpoint_factorization (i : A.Label) (z : ℤ) :
    ∃ B : Finset ℝ, B.card ≤ 49 ∧
      ∀ x y : ℝ,
        A.left i + z - A.width i ≤ x ∧ x ≤ A.right i + z + A.width i →
        A.left i + z - A.width i ≤ y ∧ y ≤ A.right i + z + A.width i →
        (∀ b ∈ B, ternarySign (x - b) = ternarySign (y - b)) →
        A.meshLabel x = A.meshLabel y := by
  refine ⟨A.neighborhoodEndpoints i z, A.neighborhoodEndpoints_card i z, ?_⟩
  intro x y hx hy hs
  exact A.endpoints_determine_label _ _ hx hy hs

/-- The rotating-coordinate bound is uniform in the location of the target
interval, including intervals crossing the circle cut. -/
theorem rotating_breakpoint_factorization (D : ℕ) (hD : 0 < D) (u v : ℝ)
    (huv : u ≤ v) (hlen : v - u ≤ 4 * A.H) :
    ∃ B : Finset ℝ, B.card ≤ 16004 * D ∧
      ∀ x y : ℝ, u ≤ x ∧ x ≤ v → u ≤ y ∧ y ≤ v →
        (∀ b ∈ B, ternarySign (x - b) = ternarySign (y - b)) →
        A.truncatedLabel (1 / (1000 * (D : ℝ))) x =
          A.truncatedLabel (1 / (1000 * (D : ℝ))) y := by
  refine ⟨A.truncatedBreakpoints (1 / (1000 * (D : ℝ))) u v,
    A.truncatedBreakpoints_card D hD u v huv hlen, ?_⟩
  intro x y hx hy hs
  exact A.truncatedBreakpoints_determine_label _ u v hx hy hs

end AdaptiveMesh
end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

noncomputable section


namespace QuantitativeVanDerWaerden.AnchoredPatterns

open Set
open scoped BigOperators

variable {D h : ℕ}

/-- Only rotating coordinates can produce a dummy scalar output. -/
def secondOutput (A : AdaptiveMesh) (eta : ℝ) (R : Realization D) (lambda : ℕ)
    (t : Fin D → Fin h) (i : Fin D) (z : Fin h) : Option A.Label := by
  classical
  exact if stationary lambda t i then some (A.meshLabel (secondPath R lambda t z i))
    else if eta ≤ rho (secondPath R lambda t z i) then
      some (A.meshLabel (secondPath R lambda t z i)) else none

theorem secondOutput_eq_some_of_regular (A : AdaptiveMesh) (eta : ℝ)
    (R : Realization D) (lambda : ℕ) (t : Fin D → Fin h) (z : Fin h)
    (hz : regular eta R lambda t z) (i : Fin D) :
    secondOutput A eta R lambda t i z = some (A.meshLabel (secondPath R lambda t z i)) := by
  classical
  by_cases hi : stationary lambda t i
  · simp [secondOutput, hi]
  · simp [secondOutput, hi, hz i hi]

/-- Scalar outputs determine the whole recorded word, including its mask.
There is no extra independent factor `2^h`. -/
theorem recordedWord_eq_assembleWord (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh)
    (eta : ℝ) (R : Realization D) (lambda : ℕ) (t : Fin D → Fin h) :
    recordedWord n hn A eta R lambda t =
      assembleWord (fun i z => UniformMesh.label n hn (firstPath R t z i))
        (secondOutput A eta R lambda t) := by
  classical
  funext z
  by_cases hz : regular eta R lambda t z
  · have hs : (fun i => secondOutput A eta R lambda t i z) =
        fun i => some (A.meshLabel (secondPath R lambda t z i)) :=
      funext (secondOutput_eq_some_of_regular A eta R lambda t z hz)
    simp only [recordedWord, ite_eq_left hz, assembleWord, hs, assembleLabel_some, fullLabel]
  · have hi : ∃ i, secondOutput A eta R lambda t i z = none := by
      obtain ⟨i, hi⟩ := not_forall.mp hz
      have hstationary : ¬ stationary lambda t i := by
        intro hs
        exact hi (fun hn => False.elim (hn hs))
      have hcut : ¬ eta ≤ rho (secondPath R lambda t z i) := by
        intro hc
        exact hi (fun _ => hc)
      exact ⟨i, by simp [secondOutput, hstationary, hcut]⟩
    rw [recordedWord, ite_eq_right hz]
    exact ((assembleWord_dummy_iff _ _ z).mpr hi).symm

def anchorCoefficient (z0 z : Fin h) : ℝ := ((z.val : ℝ) - z0.val) / h

def anchoredFirst (R : Realization D) (t : Fin D → Fin h)
    (z0 z : Fin h) (i : Fin D) : ℝ :=
  Int.fract (firstPath R t z0 i) + anchorCoefficient z0 z * (t i).val +
    anchorCoefficient z0 z * R.u i

def anchoredSecond (R : Realization D) (lambda : ℕ) (t : Fin D → Fin h)
    (z0 z : Fin h) (i : Fin D) : ℝ :=
  centered (secondPath R lambda t z0 i) +
    anchorCoefficient z0 z * ((lambda : ℝ) * (t i).val) +
    anchorCoefficient z0 z * R.v i

theorem firstPath_reanchor (R : Realization D) (t : Fin D → Fin h)
    (z0 z : Fin h) (i : Fin D) :
    firstPath R t z i = anchoredFirst R t z0 z i + (⌊firstPath R t z0 i⌋ : ℤ) := by
  simp only [anchoredFirst, firstPath, anchorCoefficient, Int.fract, div_eq_mul_inv]
  ring

theorem secondPath_reanchor (R : Realization D) (lambda : ℕ) (t : Fin D → Fin h)
    (z0 z : Fin h) (i : Fin D) :
    secondPath R lambda t z i = anchoredSecond R lambda t z0 z i +
      (⌊secondPath R lambda t z0 i + 1 / 2⌋ : ℤ) := by
  simp only [anchoredSecond, secondPath, anchorCoefficient, centered, div_eq_mul_inv]
  ring

theorem firstLabel_reanchor (n : ℕ) (hn : 0 < n) (R : Realization D)
    (t : Fin D → Fin h) (z0 z : Fin h) (i : Fin D) :
    UniformMesh.label n hn (firstPath R t z i) =
      UniformMesh.label n hn (anchoredFirst R t z0 z i) := by
  rw [firstPath_reanchor R t z0 z i]
  exact UniformMesh.label_add_int n hn _ _

theorem secondLabel_reanchor (A : AdaptiveMesh) (R : Realization D) (lambda : ℕ)
    (t : Fin D → Fin h) (z0 z : Fin h) (i : Fin D) :
    A.meshLabel (secondPath R lambda t z i) = A.meshLabel (anchoredSecond R lambda t z0 z i) := by
  rw [secondPath_reanchor R lambda t z0 z i]
  exact A.meshLabel_add_int _ _

theorem rho_reanchor (R : Realization D) (lambda : ℕ)
    (t : Fin D → Fin h) (z0 z : Fin h) (i : Fin D) :
    rho (secondPath R lambda t z i) = rho (anchoredSecond R lambda t z0 z i) := by
  rw [secondPath_reanchor R lambda t z0 z i]
  exact rho_add_int _ _

theorem abs_anchorCoefficient_lt_one (hh : 0 < h) (z0 z : Fin h) :
    |anchorCoefficient z0 z| < 1 := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hz0 : (0 : ℝ) ≤ z0.val := by positivity
  have hz : (0 : ℝ) ≤ z.val := by positivity
  have hz0h : (z0.val : ℝ) < h := by exact_mod_cast z0.isLt
  have hzh : (z.val : ℝ) < h := by exact_mod_cast z.isLt
  rw [anchorCoefficient, abs_div, abs_of_pos hhR, div_lt_one hhR, abs_lt]
  constructor <;> linarith

/-- Stationary rational translations are integer shifts, even though the
drift may be nonzero. -/
theorem stationary_translation_integer (lambda : ℕ) (t : Fin D → Fin h)
    (hh : 0 < h) (i : Fin D) (hi : stationary lambda t i) (z0 z : Fin h) :
    ∃ m : ℤ, anchorCoefficient z0 z * ((lambda : ℝ) * (t i).val) = m := by
  obtain ⟨r, hr⟩ := hi
  have hrR : (lambda : ℝ) * (t i).val = (h : ℝ) * r := by exact_mod_cast hr
  refine ⟨((z.val : ℤ) - z0.val) * r, ?_⟩
  rw [hrR]
  have hhR : (h : ℝ) ≠ 0 := by positivity
  simp only [anchorCoefficient, Int.cast_mul, Int.cast_sub, Int.cast_natCast]
  field_simp [hhR]

/-- The two genuinely free scalar parameters are anchor position and drift. -/
def scalarDomain (left right width : ℝ) : Set (Fin 2 → ℝ) :=
  {p | left ≤ p 0 ∧ p 0 ≤ right ∧ |p 1| ≤ width}

def scalarValue (c tau : Fin h → ℝ) (p : Fin 2 → ℝ) (z : Fin h) : ℝ :=
  p 0 + tau z + c z * p 1

private theorem scalarValue_mem (left right width : ℝ) (c tau : Fin h → ℝ)
    (hc : ∀ z, |c z| ≤ 1) (p : Fin 2 → ℝ)
    (hp : p ∈ scalarDomain left right width) (z : Fin h) :
    scalarValue c tau p z ∈ Icc (left + tau z - width) (right + tau z + width) := by
  have hb : |c z * p 1| ≤ width := by
    calc
      |c z * p 1| = |c z| * |p 1| := abs_mul _ _
      _ ≤ 1 * |p 1| := mul_le_mul_of_nonneg_right (hc z) (abs_nonneg _)
      _ ≤ width := by simpa only [one_mul] using hp.2.2
  have hab := abs_le.mp hb
  change left + tau z - width ≤ p 0 + tau z + c z * p 1 ∧
    p 0 + tau z + c z * p 1 ≤ right + tau z + width
  constructor <;> linarith [hp.1, hp.2.1]

private def comparisonForm (c tau b : ℝ) : AffineForm 2 where
  linear := fun j => if j = 0 then 1 else c
  constant := tau - b

private theorem comparisonForm_eval (c tau b : ℝ) (p : Fin 2 → ℝ) :
    (comparisonForm c tau b).eval p = p 0 + tau + c * p 1 - b := by
  simp [AffineForm.eval, comparisonForm, Fin.sum_univ_two]
  ring

/-- A scalar word is counted by its actual affine comparisons. The breakpoint
sets are fixed before the two real parameters are selected. -/
private theorem scalar_family {K : ℕ} {Label : Type uLabel}
    (c tau : Fin h → ℝ) (domain : Set (Fin 2 → ℝ))
    (output : Fin h → ℝ → Label) (B : Fin h → Finset ℝ)
    (hB : ∀ z, (B z).card ≤ K)
    (hfactor : ∀ p ∈ domain, ∀ q ∈ domain, ∀ z,
      (∀ b ∈ B z,
        ternarySign (scalarValue c tau p z - b) =
          ternarySign (scalarValue c tau q z - b)) →
      output z (scalarValue c tau p z) = output z (scalarValue c tau q z)) :
    ∃ S : Finset (Fin h → Label),
      (∀ w, w ∈ S ↔ ∃ p ∈ domain, (fun z => output z (scalarValue c tau p z)) = w) ∧
      S.card ≤ 16 * (K * h + 1) ^ 6 := by
  classical
  let Index := Σ z : Fin h, {b : ℝ // b ∈ B z}
  let e := Fintype.equivFin Index
  let forms : Fin (Fintype.card Index) → AffineForm 2 := fun j =>
    comparisonForm (c (e.symm j).1) (tau (e.symm j).1) (e.symm j).2.val
  obtain ⟨S, hS, hcard⟩ := finite_outputs_of_comparisons forms domain
    (fun p z => output z (scalarValue c tau p z)) (by
      intro p hp q hq hs
      funext z
      apply hfactor p hp q hq z
      intro b hb
      have hj := congrFun hs (e ⟨z, ⟨b, hb⟩⟩)
      have hforms : forms (e ⟨z, ⟨b, hb⟩⟩) = comparisonForm (c z) (tau z) b := by
        dsimp only [forms]
        rw [e.symm_apply_apply]
      change ternarySign ((forms (e ⟨z, ⟨b, hb⟩⟩)).eval p) =
        ternarySign ((forms (e ⟨z, ⟨b, hb⟩⟩)).eval q) at hj
      rw [hforms, comparisonForm_eval, comparisonForm_eval] at hj
      exact hj)
  have hIndex : Fintype.card Index ≤ K * h := by
    calc
      Fintype.card Index = ∑ z : Fin h, (B z).card := by simp [Index]
      _ ≤ ∑ _z : Fin h, K := Finset.sum_le_sum (fun z _ => hB z)
      _ = K * h := by simp [Nat.mul_comm]
  refine ⟨S, hS, ?_⟩
  exact hcard.trans (Nat.mul_le_mul_left 16
    (Nat.pow_le_pow_left (Nat.add_le_add_right hIndex 1) 6))

private theorem uniform_scalar_family (n : ℕ) (hn : 0 < n) (hD : 0 < D)
    (anchor : Fin n) (c tau : Fin h → ℝ) (hc : ∀ z, |c z| ≤ 1) :
    ∃ S : Finset (Fin h → Fin n),
      (∀ w, w ∈ S ↔ ∃ p ∈ scalarDomain (UniformMesh.left n anchor)
        (UniformMesh.right n anchor) (1 / (n : ℝ)),
        (fun z => UniformMesh.label n hn (scalarValue c tau p z)) = w) ∧
      S.card ≤ 16 * (16004 * D * h + 1) ^ 6 := by
  classical
  let lo := fun z => UniformMesh.left n anchor + tau z - 1 / (n : ℝ)
  let hi := fun z => UniformMesh.right n anchor + tau z + 1 / (n : ℝ)
  let B := fun z => (UniformMesh.liftedEndpoints n (lo z) (hi z)).image
    (fun j : ℤ => (j : ℝ) / n)
  apply scalar_family c tau _ (fun _ => UniformMesh.label n hn) B
  · intro z
    have hwidth : hi z - lo z ≤ 3 / (n : ℝ) := by
      have hw := UniformMesh.width_eq n anchor
      dsimp [hi, lo]
      simp only [div_eq_mul_inv] at hw ⊢
      linarith
    calc
      (B z).card ≤ (UniformMesh.liftedEndpoints n (lo z) (hi z)).card :=
        Finset.card_image_le
      _ ≤ 4 := UniformMesh.card_liftedEndpoints_le_four n hn _ _ hwidth
      _ ≤ 16004 * D := by omega
  · intro p hp q hq z hs
    apply UniformMesh.label_eq_of_signs_eq n hn (lo z) (hi z) _ _
      (scalarValue_mem _ _ _ c tau hc p hp z) (scalarValue_mem _ _ _ c tau hc q hq z)
    intro j hj
    exact hs _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)

private theorem stationary_scalar_family (A : AdaptiveMesh) (hD : 0 < D)
    (anchor : A.Label) (c : Fin h → ℝ) (m : Fin h → ℤ)
    (hc : ∀ z, |c z| ≤ 1) :
    ∃ S : Finset (Fin h → Option A.Label),
      (∀ w, w ∈ S ↔ ∃ p ∈ scalarDomain (A.left anchor) (A.right anchor) (A.width anchor),
        (fun z => some (A.meshLabel (scalarValue c (fun z => (m z : ℝ)) p z))) = w) ∧
      S.card ≤ 16 * (16004 * D * h + 1) ^ 6 := by
  classical
  choose B hB hfactor using (fun z => A.stationary_breakpoint_factorization anchor (m z))
  apply scalar_family c (fun z => (m z : ℝ)) _ (fun _ x => some (A.meshLabel x)) B
  · intro z
    exact (hB z).trans (by omega)
  · intro p hp q hq z hs
    exact congrArg some (hfactor z _ _
      (scalarValue_mem _ _ _ c (fun z => (m z : ℝ)) hc p hp z)
      (scalarValue_mem _ _ _ c (fun z => (m z : ℝ)) hc q hq z) hs)

private theorem rotating_scalar_family (A : AdaptiveMesh) (hD : 0 < D)
    (anchor : A.Label) (c tau : Fin h → ℝ) (hc : ∀ z, |c z| ≤ 1) :
    ∃ S : Finset (Fin h → Option A.Label),
      (∀ w, w ∈ S ↔ ∃ p ∈ scalarDomain (A.left anchor) (A.right anchor) A.H,
        (fun z => A.truncatedLabel (1 / (1000 * (D : ℝ))) (scalarValue c tau p z)) = w) ∧
      S.card ≤ 16 * (16004 * D * h + 1) ^ 6 := by
  classical
  let lo := fun z => A.left anchor + tau z - A.H
  let hi := fun z => A.right anchor + tau z + A.H
  have hlen : ∀ z, lo z ≤ hi z ∧ hi z - lo z ≤ 4 * A.H := by
    intro z
    have hw := A.width_le_two_H anchor
    have hwpos := A.width_pos anchor
    dsimp [lo, hi]
    change A.left anchor + tau z - A.H ≤ A.right anchor + tau z + A.H ∧ _
    constructor <;> linarith [A.H_pos, show A.width anchor =
      A.right anchor - A.left anchor from rfl]
  choose B hB hfactor using (fun z =>
    A.rotating_breakpoint_factorization D hD (lo z) (hi z) (hlen z).1 (hlen z).2)
  apply scalar_family c tau _ (fun _ => A.truncatedLabel (1 / (1000 * (D : ℝ)))) B hB
  intro p hp q hq z hs
  exact hfactor z _ _ (scalarValue_mem _ _ _ c tau hc p hp z)
    (scalarValue_mem _ _ _ c tau hc q hq z) hs

/-- The first-coordinate family depends only on the fixed literal anchor,
step vector, and anchor position, not on a realizing path. -/
theorem first_anchored_family (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh)
    (lambda : ℕ) (beta : FullLabel D (Fin n) A.Label) (hD : 0 < D) (hh : 0 < h)
    (t : Fin D → Fin h) (z0 : Fin h) (i : Fin D) :
    ∃ S : Finset (Fin h → Fin n),
      S.card ≤ 16 * (16004 * D * h + 1) ^ 6 ∧
      ∀ R : Realization D,
        EligibleRealization n hn A (1 / (1000 * (D : ℝ))) lambda t R →
        recordedWord n hn A (1 / (1000 * (D : ℝ))) R lambda t z0 = some beta →
        (fun z => UniformMesh.label n hn (firstPath R t z i)) ∈ S := by
  classical
  obtain ⟨S, hS, hcard⟩ := uniform_scalar_family n hn hD (beta.1 i)
    (anchorCoefficient z0) (fun z => anchorCoefficient z0 z * (t i).val)
    (fun z => (abs_anchorCoefficient_lt_one hh z0 z).le)
  refine ⟨S, hcard, ?_⟩
  intro R hR hanchor
  obtain ⟨_, hlabel⟩ := (recordedWord_eq_some_iff n hn A _ R lambda t z0 beta).mp hanchor
  have hlabeli : UniformMesh.label n hn (firstPath R t z0 i) = beta.1 i :=
    congrArg (fun label => label.1 i) hlabel
  have ha := (UniformMesh.label_mem_iff n hn (firstPath R t z0 i) (beta.1 i)).mp hlabeli
  let p : Fin 2 → ℝ := ![Int.fract (firstPath R t z0 i), R.u i]
  apply (hS _).mpr
  refine ⟨p, ⟨ha.1, ha.2.le, hR.first_drift i⟩, ?_⟩
  funext z
  exact (firstLabel_reanchor n hn R t z0 z i).symm

/-- Stationary coordinates use an untruncated mesh label; rotating coordinates
use the actual distance-to-cut truncation. Both have the same uniform bound. -/
theorem second_anchored_family (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh)
    (lambda : ℕ) (beta : FullLabel D (Fin n) A.Label) (hD : 0 < D) (hh : 0 < h)
    (t : Fin D → Fin h) (z0 : Fin h) (i : Fin D) :
    ∃ S : Finset (Fin h → Option A.Label),
      S.card ≤ 16 * (16004 * D * h + 1) ^ 6 ∧
      ∀ R : Realization D,
        EligibleRealization n hn A (1 / (1000 * (D : ℝ))) lambda t R →
        recordedWord n hn A (1 / (1000 * (D : ℝ))) R lambda t z0 = some beta →
        secondOutput A (1 / (1000 * (D : ℝ))) R lambda t i ∈ S := by
  classical
  by_cases hi : stationary lambda t i
  · choose m hm using (fun z => stationary_translation_integer lambda t hh i hi z0 z)
    obtain ⟨S, hS, hcard⟩ := stationary_scalar_family A hD (beta.2 i)
      (anchorCoefficient z0) m (fun z => (abs_anchorCoefficient_lt_one hh z0 z).le)
    refine ⟨S, hcard, ?_⟩
    intro R hR hanchor
    obtain ⟨hz0, hlabel⟩ :=
      (recordedWord_eq_some_iff n hn A _ R lambda t z0 beta).mp hanchor
    have hlabeli : A.meshLabel (secondPath R lambda t z0 i) = beta.2 i :=
      congrArg (fun label => label.2 i) hlabel
    have ha := (A.meshLabel_eq_iff (secondPath R lambda t z0 i) (beta.2 i)).mp hlabeli
    have hb : |R.v i| ≤ A.width (beta.2 i) := by
      rw [← hlabeli]
      exact hR.stationary_drift i hi z0 hz0
    let p : Fin 2 → ℝ := ![centered (secondPath R lambda t z0 i), R.v i]
    apply (hS _).mpr
    refine ⟨p, ⟨ha.1, ha.2.le, hb⟩, ?_⟩
    funext z
    have he : scalarValue (anchorCoefficient z0) (fun z => (m z : ℝ)) p z =
        anchoredSecond R lambda t z0 z i := by
      dsimp [scalarValue, p, anchoredSecond]
      rw [hm z]
    rw [he, secondOutput, ite_eq_left hi, secondLabel_reanchor A R lambda t z0 z i]
  · obtain ⟨S, hS, hcard⟩ := rotating_scalar_family A hD (beta.2 i)
      (anchorCoefficient z0)
      (fun z => anchorCoefficient z0 z * ((lambda : ℝ) * (t i).val))
      (fun z => (abs_anchorCoefficient_lt_one hh z0 z).le)
    refine ⟨S, hcard, ?_⟩
    intro R hR hanchor
    obtain ⟨_, hlabel⟩ :=
      (recordedWord_eq_some_iff n hn A _ R lambda t z0 beta).mp hanchor
    have hlabeli : A.meshLabel (secondPath R lambda t z0 i) = beta.2 i :=
      congrArg (fun label => label.2 i) hlabel
    have ha := (A.meshLabel_eq_iff (secondPath R lambda t z0 i) (beta.2 i)).mp hlabeli
    let p : Fin 2 → ℝ := ![centered (secondPath R lambda t z0 i), R.v i]
    apply (hS _).mpr
    refine ⟨p, ⟨ha.1, ha.2.le, hR.rotating_drift i hi⟩, ?_⟩
    funext z
    change A.truncatedLabel _ (anchoredSecond R lambda t z0 z i) =
      secondOutput A _ R lambda t i z
    simp only [secondOutput, ite_eq_right hi, AdaptiveMesh.truncatedLabel,
      rho_reanchor R lambda t z0 z i, secondLabel_reanchor A R lambda t z0 z i]

/-- The actual union incidence count. The literal eligibility predicate is
filtered before counting. Its pairwise distinctness and half-regular conditions
are retained in the family, although this bound only needs a regular anchor.
No family-cardinality, label-factorization, or independent-mask premise occurs
in this theorem. -/
theorem card_through_le (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (lambda : ℕ)
    (beta : FullLabel D (Fin n) A.Label) (hD : 0 < D) (hh : 0 < h) :
    (through (h := h) n hn A (1 / (1000 * (D : ℝ))) lambda beta).card ≤
      (16005 * D * h) ^ (14 * D) := by
  classical
  choose firstS hfirstcard hfirstmem using
    (fun t z0 i => first_anchored_family n hn A lambda beta hD hh t z0 i)
  choose secondS hsecondcard hsecondmem using
    (fun t z0 i => second_anchored_family n hn A lambda beta hD hh t z0 i)
  refine (Finset.card_le_card (t := anchoredIncidences firstS secondS) ?_).trans
    (card_anchoredIncidences_polynomial_le hD hh firstS secondS hfirstcard hsecondcard)
  intro p hp
  obtain ⟨⟨R, hR, hword⟩, z0, hz0⟩ :=
    (mem_through n hn A _ lambda beta p).mp hp
  have hanchor : recordedWord n hn A (1 / (1000 * (D : ℝ))) R lambda p.1 z0 =
      some beta := by rw [hword]; exact hz0
  have hmem := mem_anchoredIncidences_of_mem firstS secondS p.1 z0
    (fun i z => UniformMesh.label n hn (firstPath R p.1 z i))
    (secondOutput A (1 / (1000 * (D : ℝ))) R lambda p.1)
    (fun i => hfirstmem p.1 z0 i R hR hanchor)
    (fun i => hsecondmem p.1 z0 i R hR hanchor)
  have heq : assembleWord (fun i z => UniformMesh.label n hn (firstPath R p.1 z i))
      (secondOutput A (1 / (1000 * (D : ℝ))) R lambda p.1) = p.2 :=
    (recordedWord_eq_assembleWord n hn A _ R lambda p.1).symm.trans hword
  simpa only [heq, Prod.eta] using hmem

end QuantitativeVanDerWaerden.AnchoredPatterns

end

end OAI
end
end

section
section
namespace OAI

/-!
# Actual tests from eligible return-period patterns

The index records the period and the literal pair of rational step and recorded
word. Realizing parameters are existential witnesses, not extra test indices.
Incidence with a label is exactly the anchored family `AnchoredPatterns.through`.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.EligiblePatternTests

open AnchoredPatterns

variable {D : ℕ}

/-- Each event keeps its actual period, rational step and recorded word. -/
abbrev TestIndex (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ)
    (lambda : ℕ) (periods : Finset ℕ) :=
  (h : ↥periods) × ↥(eligiblePairs (D := D) (h := h.val) n hn A eta lambda)

variable {n : ℕ} {hn : 0 < n} {A : AdaptiveMesh} {eta : ℝ}
  {lambda : ℕ} {periods : Finset ℕ}

def period (i : TestIndex (D := D) n hn A eta lambda periods) : ℕ := i.1.val

def step (i : TestIndex (D := D) n hn A eta lambda periods) :
    Fin D → Fin (period i) := i.2.val.1

def word (i : TestIndex (D := D) n hn A eta lambda periods) :
    Fin (period i) → Option (FullLabel D (Fin n) A.Label) := i.2.val.2

/-- Only the actual non-dummy recorded labels are used by an event. -/
def support (i : TestIndex (D := D) n hn A eta lambda periods) :
    Finset (FullLabel D (Fin n) A.Label) := RecordedSupport.support (word i)

theorem period_mem (i : TestIndex (D := D) n hn A eta lambda periods) :
    period i ∈ periods := i.1.property

theorem word_eligible (i : TestIndex (D := D) n hn A eta lambda periods) :
    eligibleOptionFullLabel n hn A eta lambda (step i) (word i) :=
  (mem_eligiblePairs n hn A eta lambda i.2.val).mp i.2.property

@[simp] theorem mem_support (i : TestIndex (D := D) n hn A eta lambda periods)
    (beta : FullLabel D (Fin n) A.Label) :
    beta ∈ support i ↔ ∃ z, word i z = some beta :=
  RecordedSupport.mem_support (word i) beta

theorem word_labelsInjective (i : TestIndex (D := D) n hn A eta lambda periods) :
    RecordedSupport.LabelsInjective (word i) :=
  eligibleOptionFullLabel_labelsInjective (word_eligible i)

theorem word_regular_many (i : TestIndex (D := D) n hn A eta lambda periods) :
    period i ≤ 2 * (RecordedSupport.regularPositions (word i)).card :=
  eligibleOptionFullLabel_regular_many (word_eligible i)

theorem support_card_eq (i : TestIndex (D := D) n hn A eta lambda periods) :
    (support i).card = (RecordedSupport.regularPositions (word i)).card :=
  RecordedSupport.support_card_eq (word i) (word_labelsInjective i)

theorem period_le_two_support_card
    (i : TestIndex (D := D) n hn A eta lambda periods) :
    period i ≤ 2 * (support i).card := by
  rw [support_card_eq]
  exact word_regular_many i

/-- The actual positions of each balanced color occupy at least an eighth
of the period. -/
theorem period_le_eight_colored
    (i : TestIndex (D := D) n hn A eta lambda periods)
    (color : FullLabel D (Fin n) A.Label → Bool) (b : Bool)
    (hbalance : (support i).card ≤ 4 * ((support i).filter fun beta => color beta = b).card) :
    period i ≤ 8 * (RecordedSupport.coloredPositions (word i) color b).card :=
  RecordedSupport.length_le_eight_colored (word i) (word_labelsInjective i)
    color b (word_regular_many i) hbalance

/-- Incidences in a single period slice of the concrete event index. -/
def incidentSlice (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ)
    (lambda : ℕ) (periods : Finset ℕ) (h : ℕ)
    (beta : FullLabel D (Fin n) A.Label) :
    Finset (TestIndex (D := D) n hn A eta lambda periods) := by
  classical
  exact Finset.univ.filter fun i => period i = h ∧ beta ∈ support i

@[simp] theorem mem_incidentSlice (h : ℕ) (beta : FullLabel D (Fin n) A.Label)
    (i : TestIndex (D := D) n hn A eta lambda periods) :
    i ∈ incidentSlice n hn A eta lambda periods h beta ↔
      period i = h ∧ beta ∈ support i := by
  classical
  simp [incidentSlice]

theorem incidentSlice_card_eq_through (h : ℕ) (hh : h ∈ periods)
    (beta : FullLabel D (Fin n) A.Label) :
    (incidentSlice n hn A eta lambda periods h beta).card =
      (through (h := h) n hn A eta lambda beta).card := by
  classical
  symm
  let tag : ∀ p ∈ through (h := h) n hn A eta lambda beta,
      TestIndex (D := D) n hn A eta lambda periods := fun p hp =>
    ⟨⟨h, hh⟩, ⟨p, (mem_eligiblePairs n hn A eta lambda p).mpr
      ((mem_through n hn A eta lambda beta p).mp hp).1⟩⟩
  apply Finset.card_bij tag
  · intro p hp
    apply (mem_incidentSlice h beta (tag p hp)).mpr
    refine ⟨rfl, ?_⟩
    exact (mem_support (tag p hp) beta).mpr
      ((mem_through n hn A eta lambda beta p).mp hp).2
  · intro p hp q hq hpq
    dsimp only [tag] at hpq
    have hsub := sigma_mk_injective (α := ↥periods)
      (β := fun j : ↥periods =>
        ↥(eligiblePairs (D := D) (h := j.val) n hn A eta lambda))
      (i := ⟨h, hh⟩) hpq
    exact congrArg Subtype.val hsub
  · rintro ⟨⟨h', hh'⟩, ⟨p, hp⟩⟩ hi
    have hi' := (mem_incidentSlice h beta _).mp hi
    change h' = h ∧ beta ∈ RecordedSupport.support p.2 at hi'
    obtain ⟨heq, hbeta⟩ := hi'
    subst h'
    have hp' : p ∈ through (h := h) n hn A eta lambda beta :=
      (mem_through n hn A eta lambda beta p).mpr
        ⟨(mem_eligiblePairs n hn A eta lambda p).mp hp,
          (RecordedSupport.mem_support p.2 beta).mp hbeta⟩
    exact ⟨p, hp', rfl⟩

theorem incidentSlice_eq_empty_of_not_mem (h : ℕ) (hh : h ∉ periods)
    (beta : FullLabel D (Fin n) A.Label) :
    incidentSlice n hn A eta lambda periods h beta = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hih := ((mem_incidentSlice h beta i).mp hi).1
  exact hh (hih ▸ period_mem i)

/-- A bound on canonical anchored pairs applies to the incident slice at every
natural period, including periods outside the finite family. -/
theorem incident_card_le_of_through (countBound : ℕ → ℕ)
    (hcount : ∀ h ∈ periods, ∀ beta : FullLabel D (Fin n) A.Label,
      (through (h := h) n hn A eta lambda beta).card ≤ countBound h)
    (beta : FullLabel D (Fin n) A.Label) (h : ℕ) :
    (Finset.univ.filter (fun i : TestIndex (D := D) n hn A eta lambda periods =>
      beta ∈ support i ∧ period i = h)).card ≤ countBound h := by
  classical
  have hslice : (Finset.univ.filter
      (fun i : TestIndex (D := D) n hn A eta lambda periods =>
        beta ∈ support i ∧ period i = h)) =
      incidentSlice n hn A eta lambda periods h beta := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_incidentSlice,
      and_comm]
  rw [hslice]
  by_cases hh : h ∈ periods
  · rw [incidentSlice_card_eq_through h hh beta]
    exact hcount h hh beta
  · rw [incidentSlice_eq_empty_of_not_mem h hh beta, Finset.card_empty]
    exact Nat.zero_le _

/-- The proved geometric anchored bound applies directly to the actual second
family of outer-coloring events. -/
theorem incident_card_le (hD : 0 < D)
    (hperiods : ∀ h ∈ periods, 0 < h)
    (beta : FullLabel D (Fin n) A.Label) (h : ℕ) :
    (Finset.univ.filter (fun i : TestIndex (D := D) n hn A
        (1 / (1000 * (D : ℝ))) lambda periods =>
      beta ∈ support i ∧ period i = h)).card ≤ (16005 * D * h) ^ (14 * D) := by
  apply incident_card_le_of_through (fun h => (16005 * D * h) ^ (14 * D))
  intro h hh beta
  exact card_through_le n hn A lambda beta hD (hperiods h hh)

end QuantitativeVanDerWaerden.EligiblePatternTests

end

end OAI
end
end

section
section
namespace OAI

/-!
# Outer coloring of the actual eligible geometric patterns

The event indices contain exactly a period and a literal `(step, word)` pair.
Existential real realizations of one word do not increase its event count.
-/

namespace QuantitativeVanDerWaerden

open scoped BigOperators

theorem recordedWord_coloredPositions_eq {D h : ℕ}
    (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ)
    (R : AnchoredPatterns.Realization D) (lambda : ℕ) (t : Fin D → Fin h)
    (color : FullLabel D (Fin n) A.Label → Bool) (b : Bool) :
    RecordedSupport.coloredPositions
        (AnchoredPatterns.recordedWord n hn A eta R lambda t) color b =
      (AnchoredPatterns.regularPositions eta R lambda t).filter
        (fun z => color (AnchoredPatterns.fullLabel n hn A R lambda t z) = b) := by
  classical
  ext z
  simp only [RecordedSupport.mem_coloredPositions,
    AnchoredPatterns.recordedWord_eq_some_iff, Finset.mem_filter,
    AnchoredPatterns.regularPositions, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨beta, ⟨hz, hbeta⟩, hb⟩
    exact ⟨hz, by simpa only [hbeta] using hb⟩
  · rintro ⟨hz, hb⟩
    exact ⟨_, ⟨hz, rfl⟩, hb⟩

theorem exists_outer_coloring_of_eligible_counts
    {D k : ℕ} (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ) (lambda : ℕ)
    (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (words : Finset (Fin k → FullLabel D (Fin n) A.Label))
    (periods : Finset ℕ) (countBound : ℕ → ℕ)
    (hrow : (100 : ℝ) ≤ (M : ℝ) / 10 - 1)
    (hperiodLower : ∀ h ∈ periods, 200 ≤ h)
    (hthrough : ∀ h ∈ periods, ∀ beta : FullLabel D (Fin n) A.Label,
      (AnchoredPatterns.through (h := h) n hn A eta lambda beta).card ≤ countBound h)
    (hbudget : ((k * words.card : ℕ) : ℝ) * Real.exp (-((M : ℝ) / 10 - 1) / 32) +
      (∑ h ∈ periods, (countBound h : ℝ) * Real.exp (-(h : ℝ) / 64)) ≤ 1 / 500) :
    ∃ color : FullLabel D (Fin n) A.Label → Bool,
      (∀ word ∈ words, k ≤ 10 * (OuterWordTests.lightPositions M word).card → ∀ b,
        (OuterWordTests.lightPositions M word).card ≤
          4 * ((OuterWordTests.lightPositions M word).filter
            fun j => color (word j) = b).card) ∧
      (∀ h ∈ periods, ∀ t : Fin D → Fin h, ∀ R : AnchoredPatterns.Realization D,
        AnchoredPatterns.EligibleRealization n hn A eta lambda t R → ∀ b,
          (AnchoredPatterns.regularPositions eta R lambda t).card ≤
            4 * ((AnchoredPatterns.regularPositions eta R lambda t).filter
              fun z => color (AnchoredPatterns.fullLabel n hn A R lambda t z) = b).card) := by
  classical
  let I := EligiblePatternTests.TestIndex (D := D) n hn A eta lambda periods
  let period : I → ℕ := EligiblePatternTests.period
  let pattern : ∀ i : I, Fin (period i) → Option (FullLabel D (Fin n) A.Label) :=
    EligiblePatternTests.word
  have hcount : ∀ beta h,
      (Finset.univ.filter (fun i : I =>
        (∃ j, pattern i j = some beta) ∧ period i = h)).card ≤ countBound h := by
    intro beta h
    simpa only [EligiblePatternTests.mem_support] using
      EligiblePatternTests.incident_card_le_of_through countBound hthrough beta h
  obtain ⟨color, hglobal, hlocal⟩ := exists_outer_word_pattern_coloring M hM hMk words
    period pattern periods countBound hrow EligiblePatternTests.period_mem
    (fun i => hperiodLower (period i) (EligiblePatternTests.period_mem i))
    EligiblePatternTests.word_labelsInjective EligiblePatternTests.word_regular_many
    hcount hbudget
  refine ⟨color, hglobal, ?_⟩
  intro h hh t R hR b
  let p := AnchoredPatterns.recordedWord n hn A eta R lambda t
  have hp : (t, p) ∈ AnchoredPatterns.eligiblePairs n hn A eta lambda := by
    exact (AnchoredPatterns.mem_eligiblePairs n hn A eta lambda (t, p)).mpr ⟨R, hR, rfl⟩
  let i : I := ⟨⟨h, hh⟩, ⟨(t, p), hp⟩⟩
  have hi := hlocal i b
  change (RecordedSupport.regularPositions p).card ≤
    4 * (RecordedSupport.coloredPositions p color b).card at hi
  simpa only [p, AnchoredPatterns.recordedWord_regularPositions_eq,
    recordedWord_coloredPositions_eq] using hi

/-- Actual eligible patterns obey the anchored count theorem, so outer
selection requires only its explicit numerical incident-weight budget. -/
theorem exists_outer_balanced {D k : ℕ} (n : ℕ) (hn : 0 < n)
    (A : AdaptiveMesh) (lambda M : ℕ) (hD : 0 < D) (hM : 0 < M) (hMk : M ≤ k)
    (words : Finset (Fin k → FullLabel D (Fin n) A.Label)) (periods : Finset ℕ)
    (hrow : (100 : ℝ) ≤ (M : ℝ) / 10 - 1)
    (hperiodLower : ∀ h ∈ periods, 200 ≤ h)
    (hbudget : ((k * words.card : ℕ) : ℝ) * Real.exp (-((M : ℝ) / 10 - 1) / 32) +
      (∑ h ∈ periods, (((16005 * D * h) ^ (14 * D) : ℕ) : ℝ) *
        Real.exp (-(h : ℝ) / 64)) ≤ 1 / 500) :
    ∃ color : FullLabel D (Fin n) A.Label → Bool,
      OuterBalanced n hn A (1 / (1000 * (D : ℝ))) lambda M words periods color := by
  classical
  have hthrough : ∀ h ∈ periods, ∀ beta : FullLabel D (Fin n) A.Label,
      (AnchoredPatterns.through (h := h) n hn A (1 / (1000 * (D : ℝ))) lambda beta).card ≤
        (16005 * D * h) ^ (14 * D) := by
    intro h hh beta
    exact AnchoredPatterns.card_through_le n hn A lambda beta hD
      (lt_of_lt_of_le (by decide : 0 < 200) (hperiodLower h hh))
  obtain ⟨color, hglobal, hlocal⟩ := exists_outer_coloring_of_eligible_counts
    n hn A (1 / (1000 * (D : ℝ))) lambda M hM hMk words periods
    (fun h => (16005 * D * h) ^ (14 * D)) hrow hperiodLower hthrough hbudget
  exact ⟨color, ⟨hglobal, hlocal⟩⟩

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Filter Topology

namespace QuantitativeVanDerWaerden.Parameters

theorem log_prime_slack {k : ℕ} (hk : 2 ≤ k) :
    Real.log (2 * (k : ℝ) ^ 2) ≤ 3 * Real.log k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hl : Real.log 2 ≤ Real.log k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hk)
  rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hk0.ne'), Real.log_pow]
  norm_num
  linarith

theorem log_two_le_power_log {k : ℕ} (hk : 2 ≤ k) {a : ℝ} (ha : 0 ≤ a) :
    Real.log 2 ≤ (k : ℝ) ^ a * Real.log k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hl : Real.log 2 ≤ Real.log k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hk)
  calc
    Real.log 2 ≤ Real.log k := hl
    _ ≤ (k : ℝ) ^ a * Real.log k :=
      le_mul_of_one_le_left (Real.log_nonneg hk1) (Real.one_le_rpow hk1 ha)

/-- The exact exponent appearing in the rich-progression union bound. -/
def richEnvelope (k : ℕ) : ℝ :=
  Real.exp (-(21 / 200000 : ℝ) * k * Real.log k +
    2 * dimension k * Real.log (2 * (k : ℝ) ^ 2) + Real.log 2)

theorem richEnvelope_tendsto : Tendsto richEnvelope atTop (𝓝 0) := by
  have hb : ∀ᶠ k : ℕ in atTop, richEnvelope k ≤
      Real.exp (13 * (k : ℝ) ^ (1 / 10 : ℝ) * Real.log k -
        (21 / 200000 : ℝ) * (k : ℝ) ^ (1 : ℝ)) := by
    have hl := (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop)).eventually
      (eventually_ge_atTop (1 : ℝ))
    filter_upwards [eventually_ge_atTop 2, hl] with k hk hlog
    have hk1 : 1 ≤ k := by omega
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hD := dimension_upper hk1
    have hL := log_prime_slack hk
    have hL0 : 0 ≤ Real.log (2 * (k : ℝ) ^ 2) := by
      apply Real.log_nonneg
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    have hDL : 2 * (dimension k : ℝ) * Real.log (2 * (k : ℝ) ^ 2) ≤
        12 * (k : ℝ) ^ (1 / 10 : ℝ) * Real.log k := by
      calc
        _ ≤ (4 * (k : ℝ) ^ (1 / 10 : ℝ)) * Real.log (2 * (k : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hL0
        _ ≤ (4 * (k : ℝ) ^ (1 / 10 : ℝ)) * (3 * Real.log k) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
        _ = _ := by ring
    have htwo := log_two_le_power_log hk (by norm_num : (0 : ℝ) ≤ 1 / 10)
    have hklog : (k : ℝ) ≤ (k : ℝ) * Real.log k :=
      le_mul_of_one_le_right hk0 hlog
    apply Real.exp_le_exp.mpr
    simp only [Real.rpow_one]
    nlinarith
  apply squeeze_zero' (Eventually.of_forall fun k => (Real.exp_pos _).le) hb
  exact Scaling.tendsto_exp_rpow_log_sub_rpow (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Envelope for twice the affine-signature count times the survival bound. -/
def affineEnvelope (C : ℝ) (k : ℕ) : ℝ :=
  Real.exp ((C + 1) * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log k -
    (1 / 4 : ℝ) * (k : ℝ) ^ (19 / 20 : ℝ))

theorem affineEnvelope_tendsto {C : ℝ} (hC : 0 ≤ C) :
    Tendsto (affineEnvelope C) atTop (𝓝 0) := by
  exact Scaling.tendsto_exp_rpow_log_sub_rpow (by norm_num) (by linarith)
    (by norm_num) (by norm_num)

theorem affine_risk_le {k : ℕ} (hk : 2 ≤ k) {C T : ℝ}
    (hT : 0 < T)
    (hentropy : Real.log T ≤ C * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log k) :
    2 * T * Real.exp (-(flipProbability k * k) / 4) ≤ affineEnvelope C k := by
  have htwo := log_two_le_power_log hk (by norm_num : (0 : ℝ) ≤ 9 / 10)
  have hmass := flip_mass (by omega : 0 < k)
  calc
    2 * T * Real.exp (-(flipProbability k * k) / 4) =
        Real.exp (Real.log 2 + Real.log T - (flipProbability k * k) / 4) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_add,
        Real.exp_log (by norm_num), Real.exp_log hT, neg_div]
    _ ≤ affineEnvelope C k := by
      apply Real.exp_le_exp.mpr
      rw [hmass]
      nlinarith

/-- A global-row envelope, from `log T ≤ C k^(3/10) log k`. -/
def rowEnvelope (C : ℝ) (k : ℕ) : ℝ :=
  Real.exp ((C + 2) * (k : ℝ) ^ (3 / 10 : ℝ) * Real.log k -
    (1 / 320 : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ))

theorem rowEnvelope_tendsto {C : ℝ} (hC : 0 ≤ C) :
    Tendsto (rowEnvelope C) atTop (𝓝 0) := by
  exact Scaling.tendsto_exp_rpow_log_sub_rpow (by norm_num) (by linarith)
    (by norm_num) (by norm_num)

theorem eventually_row_risk_le (C : ℝ) : ∀ᶠ k : ℕ in atTop,
    ∀ T : ℝ, 0 < T →
      Real.log T ≤ C * (k : ℝ) ^ (3 / 10 : ℝ) * Real.log k →
      (k : ℝ) * T * Real.exp (-((cutoff k : ℝ) / 10 - 1) / 32) ≤ rowEnvelope C k := by
  have hl := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop)).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_ge_atTop 2, hl] with k hk hlog T hT hentropy
  change 1 ≤ Real.log (k : ℝ) at hlog
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hp : 1 ≤ (k : ℝ) ^ (3 / 10 : ℝ) := Real.one_le_rpow hk1 (by norm_num)
  have hlogbound : Real.log k ≤ (k : ℝ) ^ (3 / 10 : ℝ) * Real.log k :=
    le_mul_of_one_le_left (by linarith) hp
  have hunit : 1 ≤ (k : ℝ) ^ (3 / 10 : ℝ) * Real.log k :=
    one_le_mul_of_one_le_of_one_le hp hlog
  have hM := cutoff_lower k
  calc
    (k : ℝ) * T * Real.exp (-((cutoff k : ℝ) / 10 - 1) / 32) =
        Real.exp (Real.log k + Real.log T - ((cutoff k : ℝ) / 10 - 1) / 32) := by
      simp only [Real.exp_sub, Real.exp_add, Real.exp_log hk0,
        Real.exp_log hT, Real.exp_neg, div_eq_mul_inv, neg_mul]
    _ ≤ rowEnvelope C k := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- One threshold suffices to make both perturbation union bounds less than one.
The scalar entropy constant is fixed before the number of colors is introduced. -/
theorem eventually_perturbation_budget {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ k : ℕ in atTop, richEnvelope k + affineEnvelope C k < 1 := by
  have ht := richEnvelope_tendsto.add (affineEnvelope_tendsto hC)
  have he := ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) + 0 < 1))
  exact he

end QuantitativeVanDerWaerden.Parameters

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace QuantitativeVanDerWaerden.Parameters

theorem ceil_four_hundred_ge (k : ℕ) :
    (k : ℝ) / 400 ≤ ((k + 399) / 400 : ℕ) := by
  have hh : k ≤ 400 * ((k + 399) / 400) := by omega
  have hr : (k : ℝ) ≤ 400 * (((k + 399) / 400 : ℕ) : ℝ) := by exact_mod_cast hh
  linarith

theorem ceil_four_ge (k : ℕ) :
    (k : ℝ) / 4 ≤ ((k + 3) / 4 : ℕ) := by
  have hh : k ≤ 4 * ((k + 3) / 4) := by omega
  have hr : (k : ℝ) ≤ 4 * (((k + 3) / 4 : ℕ) : ℝ) := by exact_mod_cast hh
  linarith

theorem flipProbability_le_one {k : ℕ} (hk : 1 ≤ k) : flipProbability k ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hk) (by norm_num)

theorem flip_integer_power_le {k : ℕ} (hk : 1 ≤ k) :
    flipProbability k ^ ((k + 399) / 400) ≤
      flipProbability k ^ ((k : ℝ) / 400) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge (flipProbability_pos (by omega))
    (flipProbability_le_one hk) (ceil_four_hundred_ge k)

theorem survival_integer_power_le {k : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) ^ ((k + 3) / 4) ≤ Real.exp (-(p * k) / 4) := by
  have he : 1 - p ≤ Real.exp (-p) := by
    have := Real.add_one_le_exp (-p)
    linarith
  calc
    (1 - p) ^ ((k + 3) / 4) ≤ Real.exp (-p) ^ ((k + 3) / 4) :=
      pow_le_pow_left₀ (by linarith) he _
    _ = Real.exp ((((k + 3) / 4 : ℕ) : ℝ) * (-p)) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (-(p * k) / 4) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left (ceil_four_ge k) hp
      nlinarith

theorem real_rich_risk_le {k q : ℕ} (hk : 2 ≤ k) (hq : 0 < q)
    (hlogq : (dimension k : ℝ) * Real.log q ≤
      c * k * Real.log k + (dimension k : ℝ) * Real.log (2 * (k : ℝ) ^ 2)) :
    2 * (q : ℝ) ^ (2 * dimension k) *
        flipProbability k ^ ((k : ℝ) / 400) ≤ richEnvelope k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp := flipProbability_pos (by omega : 0 < k)
  have hqpow : (0 : ℝ) < (q : ℝ) ^ (2 * dimension k) := by positivity
  have hppow : 0 < flipProbability k ^ ((k : ℝ) / 400) :=
    Real.rpow_pos_of_pos hp _
  calc
    _ = Real.exp (Real.log (2 * (q : ℝ) ^ (2 * dimension k) *
        flipProbability k ^ ((k : ℝ) / 400))) :=
      (Real.exp_log (by positivity)).symm
    _ ≤ richEnvelope k := by
      apply Real.exp_le_exp.mpr
      rw [Real.log_mul (by positivity) hppow.ne',
        Real.log_mul (by norm_num) hqpow.ne', Real.log_pow, Real.log_rpow hp]
      rw [flipProbability, Real.log_rpow hk0]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      change _ ≤ -(21 / 200000 : ℝ) * k * Real.log k +
        2 * dimension k * Real.log (2 * (k : ℝ) ^ 2) + Real.log 2
      dsimp [c] at hlogq
      nlinarith

theorem integer_rich_risk_le {k q : ℕ} (hk : 2 ≤ k) (hq : 0 < q)
    (hlogq : (dimension k : ℝ) * Real.log q ≤
      c * k * Real.log k + (dimension k : ℝ) * Real.log (2 * (k : ℝ) ^ 2)) :
    2 * (q : ℝ) ^ (2 * dimension k) *
        flipProbability k ^ ((k + 399) / 400) ≤ richEnvelope k := by
  exact (mul_le_mul_of_nonneg_left (flip_integer_power_le (by omega : 1 ≤ k))
    (by positivity)).trans (real_rich_risk_le hk hq hlogq)

theorem primeScale_rich_risk_le {k : ℕ} (hk : 2 ≤ k)
    (s : PrimeScale k (dimension k)) :
    2 * (s.q : ℝ) ^ (2 * dimension k) *
        flipProbability k ^ ((k + 399) / 400) ≤ richEnvelope k := by
  have hD : 1 ≤ dimension k := dimension_pos (by omega)
  exact integer_rich_risk_le hk s.pos (s.log_upper hk hD)

theorem integer_affine_risk_le {k : ℕ} (hk : 2 ≤ k) {C T : ℝ}
    (hT : 0 < T)
    (hentropy : Real.log T ≤ C * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log k) :
    2 * T * (1 - flipProbability k) ^ ((k + 3) / 4) ≤ affineEnvelope C k := by
  have hp := flipProbability_pos (by omega : 0 < k)
  exact (mul_le_mul_of_nonneg_left
    (survival_integer_power_le hp.le (flipProbability_le_one (by omega : 1 ≤ k)))
    (by positivity)).trans (affine_risk_le hk hT hentropy)

end QuantitativeVanDerWaerden.Parameters

end

end OAI
end
end

section
section
namespace OAI

/-!
# Decay of the local anchored-pattern union bound

The constants in this estimate are fixed independently of the progression length
and of the number of colors.  The sum is finite: its upper endpoint is twice the
cutoff of the construction.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace QuantitativeVanDerWaerden.Parameters

/-- The local union-bound sum, allowing any fixed nonnegative dimension
coefficient in the pattern count. -/
def localTail (C a : ℝ) (k : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc (dimension k ^ 2 + 1) (2 * cutoff k),
    (C * (dimension k : ℝ) * h) ^ (a * dimension k) *
      Real.exp (-(h : ℝ) / 64)

theorem localTail_nonneg (C a : ℝ) (hC : 0 ≤ C) (k : ℕ) :
    0 ≤ localTail C a k := by
  apply Finset.sum_nonneg
  intro h _
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)

/-- The logarithm of every local counting base has the same bound on the
finite interval of lengths. -/
theorem local_count_log_le {C : ℝ} (hC : 1 ≤ C) {k h : ℕ}
    (hk : 1 ≤ k) (hlog : 1 ≤ Real.log k)
    (hh : h ∈ Finset.Icc (dimension k ^ 2 + 1) (2 * cutoff k)) :
    Real.log (C * (dimension k : ℝ) * h) ≤
      (Real.log (8 * C) + 1) * Real.log k := by
  have hCpos : 0 < C := by linarith
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hDpos : (0 : ℝ) < dimension k := Nat.cast_pos.mpr (dimension_pos hk)
  have hh' := Finset.mem_Icc.mp hh
  have hhpos : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hhupper : (h : ℝ) ≤ 2 * cutoff k := by exact_mod_cast hh'.2
  have hbase : 0 < C * (dimension k : ℝ) * h := by positivity
  have hbaseupper : C * (dimension k : ℝ) * h ≤
      (8 * C) * (k : ℝ) ^ (3 / 5 : ℝ) := by
    calc
      C * (dimension k : ℝ) * h ≤ C * dimension k * (2 * cutoff k) :=
        mul_le_mul_of_nonneg_left hhupper (by positivity)
      _ = (2 * C) * ((dimension k : ℝ) * cutoff k) := by ring
      _ ≤ (2 * C) * (4 * (k : ℝ) ^ (3 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_left (dimension_cutoff_upper hk) (by positivity)
      _ = (8 * C) * (k : ℝ) ^ (3 / 5 : ℝ) := by ring
  have hlogC : 0 ≤ Real.log (8 * C) := Real.log_nonneg (by linarith)
  have hlogk : 0 ≤ Real.log k := by linarith
  calc
    Real.log (C * (dimension k : ℝ) * h) ≤
        Real.log ((8 * C) * (k : ℝ) ^ (3 / 5 : ℝ)) :=
      Real.log_le_log hbase hbaseupper
    _ = Real.log (8 * C) + (3 / 5 : ℝ) * Real.log k := by
      rw [Real.log_mul (by positivity : 8 * C ≠ 0)
        (Real.rpow_pos_of_pos hkpos _).ne', Real.log_rpow hkpos]
    _ ≤ (Real.log (8 * C) + 1) * Real.log k := by
      nlinarith [mul_nonneg hlogC (sub_nonneg.mpr hlog)]

/-- A finite envelope from one numerical power-logarithm comparison. -/
theorem localTail_le_of_power_log_le {C a : ℝ} (hC : 1 ≤ C) (ha : 0 ≤ a)
    {k : ℕ} (hk : 1 ≤ k) (hlog : 1 ≤ Real.log k)
    (hsmall : (2 * a * (Real.log (8 * C) + 1)) *
      (k : ℝ) ^ (1 / 10 : ℝ) * Real.log k ≤
        (1 / 128 : ℝ) * (k : ℝ) ^ (1 / 5 : ℝ)) :
    localTail C a k ≤ 4 * (k : ℝ) ^ (1 / 2 : ℝ) *
      Real.exp (-(k : ℝ) ^ (1 / 5 : ℝ) / 128) := by
  have hCpos : 0 < C := by linarith
  have hlogC : 0 ≤ Real.log (8 * C) := Real.log_nonneg (by linarith)
  have hA : 0 ≤ Real.log (8 * C) + 1 := by linarith
  have hlogk : 0 ≤ Real.log k := by linarith
  have hterm : ∀ h ∈ Finset.Icc (dimension k ^ 2 + 1) (2 * cutoff k),
      (C * (dimension k : ℝ) * h) ^ (a * dimension k) *
        Real.exp (-(h : ℝ) / 64) ≤
          Real.exp (-(k : ℝ) ^ (1 / 5 : ℝ) / 128) := by
    intro h hh
    have hh' := Finset.mem_Icc.mp hh
    have hDpos : (0 : ℝ) < dimension k := Nat.cast_pos.mpr (dimension_pos hk)
    have hhpos : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
    have hbase : 0 < C * (dimension k : ℝ) * h := by positivity
    have hhD : (dimension k : ℝ) ^ 2 ≤ h := by
      exact_mod_cast (show dimension k ^ 2 ≤ h by omega)
    have hhpower : (k : ℝ) ^ (1 / 5 : ℝ) ≤ h :=
      (dimension_sq_lower k).trans hhD
    have hcount : a * dimension k * Real.log (C * (dimension k : ℝ) * h) ≤
        (1 / 128 : ℝ) * (k : ℝ) ^ (1 / 5 : ℝ) := by
      calc
        a * dimension k * Real.log (C * (dimension k : ℝ) * h) ≤
            (a * dimension k) * ((Real.log (8 * C) + 1) * Real.log k) :=
          mul_le_mul_of_nonneg_left (local_count_log_le hC hk hlog hh) (by positivity)
        _ ≤ (a * (2 * (k : ℝ) ^ (1 / 10 : ℝ))) *
            ((Real.log (8 * C) + 1) * Real.log k) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (dimension_upper hk) ha)
            (mul_nonneg hA hlogk)
        _ = (2 * a * (Real.log (8 * C) + 1)) *
            (k : ℝ) ^ (1 / 10 : ℝ) * Real.log k := by ring
        _ ≤ _ := hsmall
    rw [Real.rpow_def_of_pos hbase, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hcard : (Finset.Icc (dimension k ^ 2 + 1) (2 * cutoff k)).card ≤
      2 * cutoff k := by
    rw [Nat.card_Icc]
    omega
  have hcardreal :
      ((Finset.Icc (dimension k ^ 2 + 1) (2 * cutoff k)).card : ℝ) ≤
        4 * (k : ℝ) ^ (1 / 2 : ℝ) := by
    have hcard' :
        ((Finset.Icc (dimension k ^ 2 + 1) (2 * cutoff k)).card : ℝ) ≤
          2 * cutoff k := by exact_mod_cast hcard
    have := cutoff_upper hk
    linarith
  calc
    localTail C a k ≤ ∑ _h ∈ Finset.Icc (dimension k ^ 2 + 1) (2 * cutoff k),
        Real.exp (-(k : ℝ) ^ (1 / 5 : ℝ) / 128) := Finset.sum_le_sum hterm
    _ = ((Finset.Icc (dimension k ^ 2 + 1) (2 * cutoff k)).card : ℝ) *
        Real.exp (-(k : ℝ) ^ (1 / 5 : ℝ) / 128) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcardreal (Real.exp_nonneg _)

/-- The local union-bound sum has an eventual bound independent of the number
of colors. -/
theorem eventually_localTail_le {C a : ℝ} (hC : 1 ≤ C) (ha : 0 ≤ a) :
    ∀ᶠ k : ℕ in atTop, localTail C a k ≤
      4 * (k : ℝ) ^ (1 / 2 : ℝ) *
        Real.exp (-(k : ℝ) ^ (1 / 5 : ℝ) / 128) := by
  have hlogC : 0 ≤ Real.log (8 * C) := Real.log_nonneg (by linarith)
  have hcoef : 0 ≤ 2 * a * (Real.log (8 * C) + 1) := by positivity
  have hsmall := Scaling.eventually_rpow_log_le
    (a := (1 / 10 : ℝ)) (b := (1 / 5 : ℝ))
    (C := 2 * a * (Real.log (8 * C) + 1)) (eps := (1 / 128 : ℝ))
    (by norm_num) hcoef (by norm_num)
  have hlog : ∀ᶠ k : ℕ in atTop, 1 ≤ Real.log k :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hsmall, hlog, eventually_ge_atTop (1 : ℕ)] with k hs hl hk
  exact localTail_le_of_power_log_le hC ha hk hl hs

/-- The entire finite local-pattern error tends to zero. -/
theorem tendsto_localTail_zero {C a : ℝ} (hC : 1 ≤ C) (ha : 0 ≤ a) :
    Tendsto (localTail C a) atTop (𝓝 0) := by
  have hdecay := Scaling.tendsto_rpow_mul_exp_neg_rpow
    (a := (1 / 2 : ℝ)) (b := (1 / 128 : ℝ)) (t := (1 / 5 : ℝ))
    (by norm_num) (by norm_num)
  have hbound : Tendsto (fun k : ℕ =>
      4 * (k : ℝ) ^ (1 / 2 : ℝ) *
        Real.exp (-(k : ℝ) ^ (1 / 5 : ℝ) / 128)) atTop (𝓝 0) := by
    have he (x : ℝ) : -(1 / 128 : ℝ) * x = -x / 128 := by ring
    simpa only [he, mul_zero, mul_assoc] using hdecay.const_mul (4 : ℝ)
  exact squeeze_zero' (Eventually.of_forall (localTail_nonneg C a (by linarith)))
    (eventually_localTail_le hC ha) hbound

end QuantitativeVanDerWaerden.Parameters

end

end OAI
end
end

section
section
namespace OAI

/-!
# One absolute threshold for the numerical budgets

The constants in the finite counting bounds are fixed arguments here.  The
threshold is uniform in the prime-power base, the label counts, and the eventual
number of colors.  The finite geometric and counting constructions supply the
displayed numerical bounds; none is hidden inside the threshold assertion.
-/

noncomputable section

open Filter Topology

namespace QuantitativeVanDerWaerden.Parameters

theorem integer_affine_risk_le_max {k : ℕ} (hk : 2 ≤ k) {C T : ℝ}
    (hentropy : Real.log (max 1 T) ≤ C * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log k) :
    2 * T * (1 - flipProbability k) ^ ((k + 3) / 4) ≤ affineEnvelope C k := by
  have hp := flipProbability_le_one (by omega : 1 ≤ k)
  have hmax : 0 < max (1 : ℝ) T := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  calc
    _ ≤ 2 * max 1 T * (1 - flipProbability k) ^ ((k + 3) / 4) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))
        (pow_nonneg (by linarith) _)
    _ ≤ affineEnvelope C k := integer_affine_risk_le hk hmax hentropy

/-- Uniform budget for the exact integer exponents in finite sparse
perturbation.  The base enters only through its proved logarithmic bound. -/
theorem eventually_sparse_budget {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ k : ℕ in atTop, ∀ q : ℕ, 0 < q → ∀ T : ℝ,
      (dimension k : ℝ) * Real.log q ≤
        c * k * Real.log k + (dimension k : ℝ) * Real.log (2 * (k : ℝ) ^ 2) →
      Real.log (max 1 T) ≤ C * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log k →
      2 * (((q ^ dimension k : ℕ) : ℝ)) ^ 2 *
          flipProbability k ^ ((k + 399) / 400) +
        2 * T * (1 - flipProbability k) ^ ((k + 3) / 4) < 1 := by
  filter_upwards [eventually_ge_atTop 2, eventually_perturbation_budget hC]
    with k hk hbudget q hq T hlogq hentropy
  have heq : (((q ^ dimension k : ℕ) : ℝ)) ^ 2 =
      (q : ℝ) ^ (2 * dimension k) := by
    rw [Nat.cast_pow, ← pow_mul, Nat.mul_comm]
  rw [heq]
  exact lt_of_le_of_lt
    (add_le_add (integer_rich_risk_le hk hq hlogq)
      (integer_affine_risk_le_max hk hentropy)) hbudget

/-- The row and anchored local weights together eventually obey the incident
weight bound of the asymmetric local lemma.  Any fixed polynomial exponent is
allowed; in particular this includes the proved `14D` pattern bound. -/
theorem eventually_incident_envelope {G C a : ℝ}
    (hG : 0 ≤ G) (hC : 1 ≤ C) (ha : 0 ≤ a) :
    ∀ᶠ k : ℕ in atTop, rowEnvelope G k + localTail C a k < 1 / 500 := by
  have ht := (rowEnvelope_tendsto hG).add (tendsto_localTail_zero hC ha)
  exact ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) + 0 < 1 / 500))

theorem eventually_incident_budget {G C a : ℝ}
    (hG : 0 ≤ G) (hC : 1 ≤ C) (ha : 0 ≤ a) :
    ∀ᶠ k : ℕ in atTop, ∀ T : ℝ, 0 < T →
      Real.log T ≤ G * (k : ℝ) ^ (3 / 10 : ℝ) * Real.log k →
      (k : ℝ) * T * Real.exp (-((cutoff k : ℝ) / 10 - 1) / 32) +
        localTail C a k < 1 / 500 := by
  filter_upwards [eventually_incident_envelope hG hC ha, eventually_row_risk_le G]
    with k hbudget hrow T hT hentropy
  exact lt_of_le_of_lt (add_le_add_left (hrow T hT hentropy) _) hbudget

/-- One absolute integer threshold satisfies the geometric scales and both
probability budgets simultaneously. No color-count parameter occurs here. -/
theorem exists_uniform_threshold {G A C a : ℝ}
    (hG : 0 ≤ G) (hA : 0 ≤ A) (hC : 1 ≤ C) (ha : 0 ≤ a) :
    ∃ K : ℕ, ∀ k ≥ K,
      32 ≤ k ∧ BasicScales k ∧ GeometryScales k ∧
      rowEnvelope G k + localTail C a k < 1 / 500 ∧
      richEnvelope k + affineEnvelope A k < 1 := by
  apply eventually_atTop.1
  filter_upwards [eventually_ge_atTop 32, eventually_basicScales,
    eventually_geometryScales, eventually_incident_envelope hG hC ha,
    eventually_perturbation_budget hA] with k hk hb hg hi hp
  exact ⟨hk, hb, hg, hi, hp⟩

end QuantitativeVanDerWaerden.Parameters

end

end OAI
end
end

section
section
namespace OAI

/-!
# Finite scalar entropy of the global row count

The estimates below convert an explicit polynomial count into an entropy bound.
All constants and the threshold depend only on the progression length; no
number of colors or selected prime occurs in these statements.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.Parameters

theorem log_twice_cutoff_le {k : ℕ} (hk : 2 ≤ k) :
    Real.log (2 * (cutoff k : ℝ)) ≤ 3 * Real.log k := by
  have hk1 : 1 ≤ k := by omega
  have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hM0 : (0 : ℝ) < cutoff k := by exact_mod_cast cutoff_pos hk1
  have hp : (k : ℝ) ^ (1 / 2 : ℝ) ≤ k := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hk1r (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have hM := cutoff_upper hk1
  have htwo : Real.log 2 ≤ Real.log k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hk)
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h ⊢
    exact h
  calc
    Real.log (2 * (cutoff k : ℝ)) ≤ Real.log (4 * (k : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 4 + Real.log k := Real.log_mul (by norm_num) hk0.ne'
    _ ≤ 3 * Real.log k := by rw [hfour]; linarith

/-- Entropy of the coarse direction count. -/
theorem log_direction_count_le {k : ℕ} (hk : 2 ≤ k) {L : ℝ}
    (hL : Real.log L ≤ (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ))) :
    Real.log L ≤ 12 * (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k := by
  have hk1 : 1 ≤ k := by omega
  have hlog0 : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hk1)
  calc
    Real.log L ≤ (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)) := hL
    _ ≤ (dimension k : ℝ) ^ 2 * (3 * Real.log k) :=
      mul_le_mul_of_nonneg_left (log_twice_cutoff_le hk) (sq_nonneg _)
    _ ≤ (4 * (k : ℝ) ^ (1 / 5 : ℝ)) * (3 * Real.log k) :=
      mul_le_mul_of_nonneg_right (dimension_sq_upper hk1) (by positivity)
    _ = _ := by ring

/-- Polynomial enlargement of the direction count by the mesh construction. -/
theorem mesh_count_le_polynomial {k : ℕ} (hk : 1 ≤ k) {L F : ℝ}
    (hL : 1 ≤ L) (hF : F ≤ (k : ℝ) ^ 2 * L + 28 * (k : ℝ) ^ 3 * Real.log k) :
    F ≤ 29 * (k : ℝ) ^ 4 * L := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk1
  have hk24 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 :=
    pow_le_pow_right₀ hk1 (by norm_num)
  have hlog : Real.log (k : ℝ) ≤ k :=
    (Real.log_le_sub_one_of_pos hk0).trans (by linarith)
  have hfirst : (k : ℝ) ^ 2 * L ≤ (k : ℝ) ^ 4 * L :=
    mul_le_mul_of_nonneg_right hk24 (by linarith)
  have hsecond : (k : ℝ) ^ 3 * Real.log k ≤ (k : ℝ) ^ 4 * L := by
    calc
      (k : ℝ) ^ 3 * Real.log k ≤ (k : ℝ) ^ 3 * k :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = (k : ℝ) ^ 4 := by ring
      _ ≤ (k : ℝ) ^ 4 * L := le_mul_of_one_le_right (by positivity) hL
  linarith

theorem log_mesh_count_le {k : ℕ} (hk : 32 ≤ k) {L F : ℝ}
    (hL : 1 ≤ L) (hFpos : 0 < F)
    (hLlog : Real.log L ≤ (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)))
    (hF : F ≤ (k : ℝ) ^ 2 * L + 28 * (k : ℝ) ^ 3 * Real.log k) :
    Real.log F ≤ 17 * (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k := by
  have hk1 : 1 ≤ k := by omega
  have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk1r
  have hLpos : 0 < L := by linarith
  have hp : 1 ≤ (k : ℝ) ^ (1 / 5 : ℝ) := Real.one_le_rpow hk1r (by norm_num)
  have hlog0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1r
  have hlogp : Real.log (k : ℝ) ≤ (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k :=
    le_mul_of_one_le_left hlog0 hp
  have h29 : Real.log (29 : ℝ) ≤ Real.log k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 29 ≤ k))
  have hdir := log_direction_count_le (by omega : 2 ≤ k) hLlog
  calc
    Real.log F ≤ Real.log (29 * (k : ℝ) ^ 4 * L) :=
      Real.log_le_log hFpos (mesh_count_le_polynomial hk1 hL hF)
    _ = Real.log 29 + 4 * Real.log k + Real.log L := by
      rw [Real.log_mul (by positivity) hLpos.ne',
        Real.log_mul (by norm_num) (pow_ne_zero 4 hk0.ne'), Real.log_pow]
      norm_num
    _ ≤ 17 * (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k := by nlinarith

theorem log_row_base_le {k : ℕ} (hk : 32 ≤ k) {L F : ℝ}
    (hL : 1 ≤ L) (hFone : 1 ≤ F)
    (hLlog : Real.log L ≤ (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)))
    (hF : F ≤ (k : ℝ) ^ 2 * L + 28 * (k : ℝ) ^ 3 * Real.log k) :
    Real.log (3 * (k : ℝ) ^ 2 * F + 1) ≤
      21 * (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk1
  have hFpos : 0 < F := by linarith
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
  have hprod : (1 : ℝ) ≤ (k : ℝ) ^ 2 * F := one_le_mul_of_one_le_of_one_le hk2 hFone
  have hbase : 3 * (k : ℝ) ^ 2 * F + 1 ≤ 4 * (k : ℝ) ^ 2 * F := by nlinarith
  have htwo : Real.log 2 ≤ Real.log k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ k))
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h ⊢
    exact h
  have hlog0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
  have hlogp : Real.log (k : ℝ) ≤ (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k :=
    le_mul_of_one_le_left hlog0 (Real.one_le_rpow hk1 (by norm_num))
  have hmesh := log_mesh_count_le hk hL hFpos hLlog hF
  calc
    Real.log (3 * (k : ℝ) ^ 2 * F + 1) ≤ Real.log (4 * (k : ℝ) ^ 2 * F) :=
      Real.log_le_log (by positivity) hbase
    _ = Real.log 4 + 2 * Real.log k + Real.log F := by
      rw [Real.log_mul (by positivity) hFpos.ne',
        Real.log_mul (by norm_num) (pow_ne_zero 2 hk0.ne'), Real.log_pow]
      norm_num
    _ ≤ 21 * (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k := by rw [hfour]; nlinarith

/-- A finite row-count bound gives an explicit entropy constant for every fixed
polynomial exponent `e`; in particular this applies to exponents six and eight. -/
theorem log_global_count_le {k e : ℕ} (hk : 32 ≤ k) {L F T : ℝ}
    (hL : 1 ≤ L) (hFone : 1 ≤ F) (hT : 0 < T)
    (hLlog : Real.log L ≤ (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)))
    (hF : F ≤ (k : ℝ) ^ 2 * L + 28 * (k : ℝ) ^ 3 * Real.log k)
    (hcount : T ≤ (16 * (3 * (k : ℝ) ^ 2 * F + 1) ^ e) ^ (2 * dimension k)) :
    Real.log T ≤ (16 + 84 * (e : ℝ)) * (k : ℝ) ^ (3 / 10 : ℝ) * Real.log k := by
  have hk1 : 1 ≤ k := by omega
  have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk1r
  have hFpos : 0 < F := by linarith
  have hbasepos : 0 < 3 * (k : ℝ) ^ 2 * F + 1 := by positivity
  have htwo : Real.log 2 ≤ Real.log k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ k))
  have hsixteen : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 4
    norm_num at h ⊢
    exact h
  have hlog0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1r
  have hp : 1 ≤ (k : ℝ) ^ (1 / 5 : ℝ) := Real.one_le_rpow hk1r (by norm_num)
  have hlogp : Real.log (k : ℝ) ≤ (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k :=
    le_mul_of_one_le_left hlog0 hp
  have hbase := log_row_base_le hk hL hFone hLlog hF
  have hinside : Real.log 16 + (e : ℝ) * Real.log (3 * (k : ℝ) ^ 2 * F + 1) ≤
      (4 + 21 * (e : ℝ)) * (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k := by
    have he := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg e : (0 : ℝ) ≤ e)
    rw [hsixteen]
    nlinarith
  have hD : 2 * (dimension k : ℝ) ≤ 4 * (k : ℝ) ^ (1 / 10 : ℝ) := by
    have := dimension_upper hk1
    linarith
  calc
    Real.log T ≤ Real.log ((16 * (3 * (k : ℝ) ^ 2 * F + 1) ^ e) ^ (2 * dimension k)) :=
      Real.log_le_log hT hcount
    _ = (2 * (dimension k : ℝ)) *
        (Real.log 16 + (e : ℝ) * Real.log (3 * (k : ℝ) ^ 2 * F + 1)) := by
      rw [Real.log_pow, Real.log_mul (by norm_num) (pow_ne_zero e hbasepos.ne'),
        Real.log_pow]
      push_cast
      ring
    _ ≤ (2 * (dimension k : ℝ)) *
        ((4 + 21 * (e : ℝ)) * (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k) :=
      mul_le_mul_of_nonneg_left hinside (by positivity)
    _ ≤ (4 * (k : ℝ) ^ (1 / 10 : ℝ)) *
        ((4 + 21 * (e : ℝ)) * (k : ℝ) ^ (1 / 5 : ℝ) * Real.log k) :=
      mul_le_mul_of_nonneg_right hD (by positivity)
    _ = (16 + 84 * (e : ℝ)) *
        ((k : ℝ) ^ (1 / 10 : ℝ) * (k : ℝ) ^ (1 / 5 : ℝ)) * Real.log k := by ring
    _ = _ := by
      rw [← Real.rpow_add hk0]
      norm_num

end QuantitativeVanDerWaerden.Parameters

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Filter Topology
open scoped BigOperators

namespace QuantitativeVanDerWaerden.Parameters

/-- The integer anchored-pattern sum on the half-open interval is exactly the
real-power local tail already estimated above. -/
theorem outer_local_sum_eq_localTail (k : ℕ) :
    (∑ h ∈ Finset.Ioc (dimension k ^ 2) (2 * cutoff k),
      (((16005 * dimension k * h) ^ (14 * dimension k) : ℕ) : ℝ) *
        Real.exp (-(h : ℝ) / 64)) = localTail 16005 14 k := by
  have hinterval : Finset.Ioc (dimension k ^ 2) (2 * cutoff k) =
      Finset.Icc (dimension k ^ 2 + 1) (2 * cutoff k) := by
    ext h
    simp only [Finset.mem_Ioc, Finset.mem_Icc, Nat.lt_iff_add_one_le]
  rw [hinterval]
  unfold localTail
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  rw [Nat.cast_pow, ← Real.rpow_natCast]
  norm_num

/-- The actual finite row and anchored-pattern weights obey the required
incident budget.  The row count may be zero. -/
theorem eventually_outer_counted_budget :
    ∀ᶠ k : ℕ in atTop, ∀ L F : ℝ, 1 ≤ L → 1 ≤ F → ∀ T : ℕ,
      Real.log L ≤ (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)) →
      F ≤ (k : ℝ) ^ 2 * L + 28 * (k : ℝ) ^ 3 * Real.log k →
      (T : ℝ) ≤ (16 * (3 * (k : ℝ) ^ 2 * F + 1) ^ (6 : ℕ)) ^
        (2 * dimension k) →
      ((k * T : ℕ) : ℝ) * Real.exp (-((cutoff k : ℝ) / 10 - 1) / 32) +
        (∑ h ∈ Finset.Ioc (dimension k ^ 2) (2 * cutoff k),
          (((16005 * dimension k * h) ^ (14 * dimension k) : ℕ) : ℝ) *
            Real.exp (-(h : ℝ) / 64)) ≤ 1 / 500 := by
  have hbudget := eventually_incident_budget
    (G := (520 : ℝ)) (C := (16005 : ℝ)) (a := (14 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (32 : ℕ), hbudget]
    with k hk hb L F hL hF T hLlog hmesh hcount
  rw [outer_local_sum_eq_localTail]
  by_cases hT : T = 0
  · subst T
    simp only [Nat.mul_zero, Nat.cast_zero, zero_mul, zero_add]
    have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
    have hzero : Real.log (1 : ℝ) ≤
        520 * (k : ℝ) ^ (3 / 10 : ℝ) * Real.log k := by
      rw [Real.log_one]
      positivity
    have hone := hb 1 (by norm_num) hzero
    have hrow : 0 ≤ (k : ℝ) * 1 *
        Real.exp (-((cutoff k : ℝ) / 10 - 1) / 32) := by positivity
    linarith
  · have hTpos : (0 : ℝ) < T := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hT)
    have hentropy := log_global_count_le (e := 6) hk hL hF hTpos hLlog hmesh hcount
    have hentropy' : Real.log (T : ℝ) ≤
        520 * (k : ℝ) ^ (3 / 10 : ℝ) * Real.log k := by
      norm_num at hentropy
      exact hentropy
    simpa only [Nat.cast_mul] using (hb T hTpos hentropy').le

/-- A single absolute integer threshold works for every admissible finite
direction, mesh and row count. -/
theorem exists_outer_counted_threshold :
    ∃ K : ℕ, 32 ≤ K ∧ ∀ k ≥ K, ∀ L F : ℝ, 1 ≤ L → 1 ≤ F → ∀ T : ℕ,
      Real.log L ≤ (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)) →
      F ≤ (k : ℝ) ^ 2 * L + 28 * (k : ℝ) ^ 3 * Real.log k →
      (T : ℝ) ≤ (16 * (3 * (k : ℝ) ^ 2 * F + 1) ^ (6 : ℕ)) ^
        (2 * dimension k) →
      ((k * T : ℕ) : ℝ) * Real.exp (-((cutoff k : ℝ) / 10 - 1) / 32) +
        (∑ h ∈ Finset.Ioc (dimension k ^ 2) (2 * cutoff k),
          (((16005 * dimension k * h) ^ (14 * dimension k) : ℕ) : ℝ) *
            Real.exp (-(h : ℝ) / 64)) ≤ 1 / 500 := by
  obtain ⟨K, hK⟩ := eventually_atTop.1
    ((eventually_ge_atTop (32 : ℕ)).and eventually_outer_counted_budget)
  exact ⟨K, (hK K le_rfl).1, fun k hk => (hK k hk).2⟩

end QuantitativeVanDerWaerden.Parameters

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Filter
open scoped BigOperators

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

/-- One eventual range works for every admissible prime-power choice. The
finite word count, scale inequalities, and probability budget are all supplied
by the actual construction rather than assumed of the selected coloring. -/
theorem eventually_outerChoice :
    ∀ᶠ k : ℕ in atTop, ∃ hk : 3 ≤ k, ∀ s : Data k, Nonempty (OuterChoice s hk) := by
  filter_upwards [eventually_ge_atTop (32 : ℕ), eventually_geometryScales,
    eventually_outer_counted_budget] with k hk32 hgeom hbudget
  have hk : 3 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  refine ⟨hk, ?_⟩
  intro s
  obtain ⟨words, hwords, hcard⟩ := exists_fullLabelWord_family s hk
  let F : ℝ := ((uniformCount k + Fintype.card (mesh s hk).Label : ℕ) : ℝ)
  have hL : (1 : ℝ) ≤ lambda k := by
    exact_mod_cast (Nat.succ_le_of_lt (lambda_pos k))
  have hF : (1 : ℝ) ≤ F := by
    dsimp [F]
    exact_mod_cast ((Nat.succ_le_of_lt (uniformCount_pos hk)).trans
      (Nat.le_add_right (uniformCount k) (Fintype.card (mesh s hk).Label)))
  have hLlog : Real.log (lambda k : ℝ) ≤
      (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)) := by
    calc
      Real.log (lambda k : ℝ) ≤
          ((dimension k ^ 2 : ℕ) : ℝ) * Real.log (2 * (cutoff k : ℝ)) :=
        log_dilation_le (h₀ := dimension k ^ 2) (cutoff_pos hk1)
      _ = (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)) :=
        congrArg (fun x : ℝ => x * Real.log (2 * (cutoff k : ℝ)))
          (Nat.cast_pow (dimension k) 2)
  have hmesh : F ≤ (k : ℝ) ^ 2 * (lambda k : ℝ) +
      28 * (k : ℝ) ^ 3 * Real.log k := by
    dsimp [F]
    rw [Nat.cast_add, uniformCount, Nat.cast_mul, Nat.cast_pow]
    exact add_le_add_right (card_second_labels_le s hk) _
  have hcount : (words.card : ℝ) ≤
      (16 * (3 * (k : ℝ) ^ 2 * F + 1) ^ (6 : ℕ)) ^ (2 * dimension k) := by
    dsimp [F]
    exact_mod_cast hcard
  have hbudget' := hbudget (lambda k) F hL hF words.card hLlog hmesh hcount
  have hMkR : (cutoff k : ℝ) ≤ k := by
    have htwo := hgeom.two_cutoff_le_length
    have hnonneg : (0 : ℝ) ≤ cutoff k := Nat.cast_nonneg _
    linarith
  have hMk : cutoff k ≤ k := by exact_mod_cast hMkR
  have hperiod : ∀ h ∈ Finset.Ioc (dimension k ^ 2) (2 * cutoff k), 200 ≤ h := by
    intro h hh
    have hD2R : (200 : ℝ) ≤ (dimension k : ℝ) ^ 2 := by
      have := hgeom.local_event_size
      linarith
    have hD2 : 200 ≤ dimension k ^ 2 := by exact_mod_cast hD2R
    exact hD2.trans (Finset.mem_Ioc.mp hh).1.le
  obtain ⟨color, hbalanced⟩ := exists_outer_balanced
    (uniformCount k) (uniformCount_pos hk) (mesh s hk) (lambda k) (cutoff k)
    (dimension_pos hk1) (cutoff_pos hk1) hMk words
    (Finset.Ioc (dimension k ^ 2) (2 * cutoff k))
    hgeom.light_row_size hperiod hbudget'
  exact ⟨⟨words, color, hwords, hcard, hbalanced⟩⟩

/-- Absolute threshold form of the actual outer-coloring choice. It is chosen
before the prime scale or any requested number of final colors. -/
theorem exists_outerChoice_threshold :
    ∃ K : ℕ, 32 ≤ K ∧ ∀ k ≥ K, ∃ hk : 3 ≤ k,
      ∀ s : Data k, Nonempty (OuterChoice s hk) := by
  obtain ⟨K, hK⟩ := eventually_atTop.1
    ((eventually_ge_atTop (32 : ℕ)).and eventually_outerChoice)
  exact ⟨K, (hK K le_rfl).1, fun k hk => (hK k hk).2⟩

end QuantitativeVanDerWaerden.ConstructionModel

end

end OAI
end
end

section
section
namespace OAI

/-!
# Counting literal signatures on affine progressions

Only coefficient triples whose evaluations lie in the specified bounded
interval are counted. Integer threshold comparisons, including equality,
determine their floor words. The proved arrangement estimate in dimension
three gives `25 * (k * (B + 1) + 1)^8`; no cubic arrangement bound is asserted.

The full label word and the floor word determine each original color and
literal `(box, integer band)` key. The product count never renames keys.
-/

noncomputable section


namespace QuantitativeVanDerWaerden

open scoped BigOperators

/-- Evaluation of the three actual quadratic coefficients. -/
def quadraticValue (θ : Fin 3 → ℝ) (j : ℕ) : ℝ :=
  θ 0 + θ 1 * (j : ℝ) + θ 2 * (j : ℝ) ^ 2

def quadraticFloorWord (k : ℕ) (θ : Fin 3 → ℝ) : Fin k → ℤ :=
  fun j => ⌊quadraticValue θ j.val⌋

/-- The evaluation restriction is essential: unrestricted coefficient triples
have infinitely many literal integer floor words. -/
def boundedQuadraticDomain (k B : ℕ) : Set (Fin 3 → ℝ) :=
  {θ | ∀ j : Fin k, 0 ≤ quadraticValue θ j.val ∧ quadraticValue θ j.val ≤ (B : ℝ)}

def quadraticComparisonForm (j b : ℕ) : AffineForm 3 where
  linear := ![1, (j : ℝ), (j : ℝ) ^ 2]
  constant := -(b : ℝ)

theorem quadraticComparisonForm_eval (j b : ℕ) (θ : Fin 3 → ℝ) :
    (quadraticComparisonForm j b).eval θ = quadraticValue θ j - b := by
  simp [quadraticComparisonForm, AffineForm.eval, quadraticValue, Fin.sum_univ_succ]
  ring

/-- One form for every position and every threshold `0,...,B`. -/
def quadraticComparisonForms (k B : ℕ) : Fin (k * (B + 1)) → AffineForm 3 :=
  fun i =>
    let p : Fin k × Fin (B + 1) := finProdFinEquiv.symm i
    quadraticComparisonForm p.1.val p.2.val

@[simp] theorem quadraticComparisonForms_eval (k B : ℕ)
    (j : Fin k) (b : Fin (B + 1)) (θ : Fin 3 → ℝ) :
    (quadraticComparisonForms k B (finProdFinEquiv (j, b))).eval θ =
      quadraticValue θ j.val - b.val := by
  simp only [quadraticComparisonForms, Equiv.symm_apply_apply,
    quadraticComparisonForm_eval]

/-- Testing the threshold equal to the first floor forces the corresponding
lower bound for the second floor. The threshold is an original integer. -/
private theorem floor_le_of_comparisons {B : ℕ} {x y : ℝ}
    (hx0 : 0 ≤ x) (hxB : x ≤ (B : ℝ))
    (h : ∀ b : Fin (B + 1), ternarySign (x - b.val) = ternarySign (y - b.val)) :
    ⌊x⌋ ≤ ⌊y⌋ := by
  have hxI : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx0
  have hxIB : ⌊x⌋ ≤ (B : ℤ) := by
    exact_mod_cast (Int.floor_le x).trans hxB
  let b : Fin (B + 1) := ⟨⌊x⌋.toNat, by omega⟩
  have hbI : (b.val : ℤ) = ⌊x⌋ := by dsimp [b]; omega
  have hbR : (b.val : ℝ) = (⌊x⌋ : ℝ) := by exact_mod_cast hbI
  have hy : (b.val : ℝ) ≤ y := by
    by_contra hy
    have hneg : ternarySign (y - b.val) = 0 :=
      (ternarySign_eq_zero _).mpr (sub_neg.mpr (lt_of_not_ge hy))
    have hxneg := (ternarySign_eq_zero _).mp ((h b).trans hneg)
    rw [hbR] at hxneg
    exact (not_lt_of_ge (sub_nonneg.mpr (Int.floor_le x))) hxneg
  apply Int.le_floor.mpr
  simpa only [hbR] using hy

theorem floor_eq_of_comparisons {B : ℕ} {x y : ℝ}
    (hx : 0 ≤ x ∧ x ≤ (B : ℝ)) (hy : 0 ≤ y ∧ y ≤ (B : ℝ))
    (h : ∀ b : Fin (B + 1), ternarySign (x - b.val) = ternarySign (y - b.val)) :
    ⌊x⌋ = ⌊y⌋ :=
  le_antisymm (floor_le_of_comparisons hx.1 hx.2 h)
    (floor_le_of_comparisons hy.1 hy.2 (fun b => (h b).symm))

/-- Sign equality determines the entire floor word, with both zero and upper
boundary evaluations allowed. -/
theorem quadraticFloorWord_eq_of_signVector_eq (k B : ℕ)
    {θ η : Fin 3 → ℝ} (hθ : θ ∈ boundedQuadraticDomain k B)
    (hη : η ∈ boundedQuadraticDomain k B)
    (h : signVector (quadraticComparisonForms k B) θ =
      signVector (quadraticComparisonForms k B) η) :
    quadraticFloorWord k θ = quadraticFloorWord k η := by
  funext j
  apply floor_eq_of_comparisons (hθ j) (hη j)
  intro b
  have hb := congrFun h (finProdFinEquiv (j, b))
  simpa only [signVector, quadraticComparisonForms_eval] using hb

/-- The genuine coefficients of the squared norm on an affine line. -/
def normSqCoefficients {D : ℕ} (A B : Vec D) : Fin 3 → ℝ :=
  ![normSq A, 2 * (∑ i, A i * B i), normSq B]

theorem quadraticValue_normSqCoefficients {D : ℕ} (A B : Vec D) (j : ℕ) :
    quadraticValue (normSqCoefficients A B) j =
      normSq (fun i => A i + (j : ℝ) * B i) := by
  rw [normSq_affine]
  simp [quadraticValue, normSqCoefficients]
  ring

/-- Coarse natural bound used in the counting estimate. Centered coordinate
bounds imply this for the actual `q`-scaled representative. -/
theorem normSq_scaled_le {D : ℕ} (q : ℕ) (x : Vec D)
    (hx : ∀ i, -(1 / 2 : ℝ) ≤ x i ∧ x i < 1 / 2) :
    normSq (fun i => (q : ℝ) * x i) ≤ ((D * q ^ 2 : ℕ) : ℝ) := by
  have hterm (i : Fin D) : ((q : ℝ) * x i) ^ 2 ≤ (q : ℝ) ^ 2 := by
    have hs : (x i) ^ 2 ≤ 1 := by
      have hp : 0 ≤ (x i + 1 / 2) * (1 / 2 - x i) :=
        mul_nonneg (by linarith [(hx i).1]) (by linarith [(hx i).2])
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (q : ℝ))]
  calc
    normSq (fun i => (q : ℝ) * x i) ≤ ∑ _i : Fin D, (q : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = ((D * q ^ 2 : ℕ) : ℝ) := by simp

theorem normSq_scaled_yRep_bounds (q D dilation : ℕ) (n : CyclicGroup q D) :
    0 ≤ normSq (fun i => (q : ℝ) * yRep q D dilation n i) ∧
      normSq (fun i => (q : ℝ) * yRep q D dilation n i) ≤ ((D * q ^ 2 : ℕ) : ℝ) :=
  ⟨normSq_nonneg _, normSq_scaled_le q _ (fun i => yRep_mem q D dilation n i)⟩

/-- The exact finite image of bounded quadratic floor words. In particular,
the family also covers triples not arising from squared norms. -/
theorem finite_quadraticFloorWords (k B : ℕ) :
    ∃ W : Finset (Fin k → ℤ),
      (∀ w, w ∈ W ↔ ∃ θ ∈ boundedQuadraticDomain k B, quadraticFloorWord k θ = w) ∧
      W.card ≤ 25 * (k * (B + 1) + 1) ^ 8 := by
  obtain ⟨W, hW, hcard⟩ := finite_outputs_of_comparisons
    (quadraticComparisonForms k B) (boundedQuadraticDomain k B) (quadraticFloorWord k)
    (fun _ hθ _ hη h => quadraticFloorWord_eq_of_signVector_eq k B hθ hη h)
  exact ⟨W, hW, hcard⟩

/-- The color and box are fixed functions of the full label, while the band
is the literal integer value. No signature-dependent coding is used. -/
def literalSignature {Label : Type uLabel} {Box : Type uBox} {k : ℕ}
    (color : Label → Bool) (boxOf : Label → Box)
    (labels : Fin k → Label) (bands : Fin k → ℤ) : Fin k → Bool × (Box × ℤ) :=
  fun j => (color (labels j), (boxOf (labels j), bands j))

/-- Finite-image factorization: one full label word and one band word suffice.
The ambient label and box types need not be finite. -/
theorem card_literalSignatures_le_mul {ι : Type uIndex} {Label : Type uLabel} {Box : Type uBox} {k : ℕ}
    [DecidableEq Label] [DecidableEq Box]
    (P : Finset ι) (labels : ι → Fin k → Label) (bands : ι → Fin k → ℤ)
    (color : Label → Bool) (boxOf : Label → Box) (W : Finset (Fin k → ℤ))
    (hW : ∀ p ∈ P, bands p ∈ W) :
    (P.image (fun p => literalSignature color boxOf (labels p) (bands p))).card ≤
      (P.image labels).card * W.card := by
  classical
  let decode : ((Fin k → Label) × (Fin k → ℤ)) → (Fin k → Bool × (Box × ℤ)) :=
    fun x => literalSignature color boxOf x.1 x.2
  have hsub : P.image (fun p => literalSignature color boxOf (labels p) (bands p)) ⊆
      ((P.image labels).product W).image decode := by
    intro σ hσ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hσ
    exact Finset.mem_image.mpr ⟨(labels p, bands p),
      Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, hW p hp⟩, rfl⟩
  calc
    _ ≤ (((P.image labels).product W).image decode).card := Finset.card_le_card hsub
    _ ≤ ((P.image labels).product W).card := Finset.card_image_le
    _ = (P.image labels).card * W.card := Finset.card_product _ _

theorem card_quadraticSignatures_le {ι : Type uIndex} {Label : Type uLabel} {Box : Type uBox} {k B : ℕ}
    [DecidableEq Label] [DecidableEq Box]
    (P : Finset ι) (labels : ι → Fin k → Label) (θ : ι → Fin 3 → ℝ)
    (color : Label → Bool) (boxOf : Label → Box)
    (hθ : ∀ p ∈ P, θ p ∈ boundedQuadraticDomain k B) :
    (P.image (fun p => literalSignature color boxOf (labels p)
      (quadraticFloorWord k (θ p)))).card ≤
      (P.image labels).card * (25 * (k * (B + 1) + 1) ^ 8) := by
  obtain ⟨W, hW, hcard⟩ := finite_quadraticFloorWords k B
  exact (card_literalSignatures_le_mul P labels (fun p => quadraticFloorWord k (θ p))
    color boxOf W (fun p hp => (hW _).mpr ⟨θ p, hθ p hp, rfl⟩)).trans
    (Nat.mul_le_mul_left _ hcard)

/-- Actual affine squared-norm words have the preceding coefficient witnesses.
Affinity and the evaluation bound are stated for the finite family being counted. -/
theorem card_affineNormSignatures_le {ι : Type uIndex} {Label : Type uLabel} {Box : Type uBox} {k D B : ℕ}
    [DecidableEq Label] [DecidableEq Box]
    (P : Finset ι) (labels : ι → Fin k → Label) (point : ι → Fin k → Vec D)
    (color : Label → Bool) (boxOf : Label → Box)
    (haff : ∀ p ∈ P, ∃ A C : Vec D,
      ∀ j : Fin k, point p j = fun i => A i + (j.val : ℝ) * C i)
    (hbound : ∀ p ∈ P, ∀ j, normSq (point p j) ≤ (B : ℝ)) :
    (P.image (fun p => literalSignature color boxOf (labels p)
      (fun j => ⌊normSq (point p j)⌋))).card ≤
      (P.image labels).card * (25 * (k * (B + 1) + 1) ^ 8) := by
  obtain ⟨W, hW, hcard⟩ := finite_quadraticFloorWords k B
  have hmem (p : ι) (hp : p ∈ P) : (fun j => ⌊normSq (point p j)⌋) ∈ W := by
    obtain ⟨A, C, hAC⟩ := haff p hp
    apply (hW _).mpr
    refine ⟨normSqCoefficients A C, ?_, ?_⟩
    · intro j
      rw [quadraticValue_normSqCoefficients, ← hAC j]
      exact ⟨normSq_nonneg _, hbound p hp j⟩
    · funext j
      change ⌊quadraticValue (normSqCoefficients A C) j.val⌋ = _
      rw [quadraticValue_normSqCoefficients, ← hAC j]
  exact (card_literalSignatures_le_mul P labels (fun p j => ⌊normSq (point p j)⌋)
    color boxOf W hmem).trans (Nat.mul_le_mul_left _ hcard)

/-- The concrete centered cyclic representative supplies its own bounded
evaluation domain. The coarse natural threshold is exactly `D*q^2`. -/
theorem card_affine_yRep_signatures_le {ι : Type uIndex} {Label : Type uLabel} {Box : Type uBox} {k q D dilation : ℕ}
    [DecidableEq Label] [DecidableEq Box]
    (P : Finset ι) (labels : ι → Fin k → Label)
    (n : ι → Fin k → CyclicGroup q D) (color : Label → Bool) (boxOf : Label → Box)
    (haff : ∀ p ∈ P, ∃ A C : Vec D, ∀ j : Fin k,
      (fun i => (q : ℝ) * yRep q D dilation (n p j) i) =
        fun i => A i + (j.val : ℝ) * C i) :
    (P.image (fun p => literalSignature color boxOf (labels p)
      (fun j => ⌊normSq (fun i => (q : ℝ) * yRep q D dilation (n p j) i)⌋))).card ≤
      (P.image labels).card * (25 * (k * (D * q ^ 2 + 1) + 1) ^ 8) := by
  apply card_affineNormSignatures_le P labels
    (fun p j i => (q : ℝ) * yRep q D dilation (n p j) i) color boxOf haff
  intro p _ j
  exact (normSq_scaled_yRep_bounds q D dilation (n p j)).2

/-- With full labels the original second-system box is precisely the second
projection, an entire vector of literal interval identities. -/
theorem card_affine_yRep_fullLabel_signatures_le {ι : Type uIndex} {U : Type uU} {V : Type uV} {k q D dilation : ℕ}
    [DecidableEq U] [DecidableEq V]
    (P : Finset ι) (labels : ι → Fin k → FullLabel D U V)
    (n : ι → Fin k → CyclicGroup q D) (color : FullLabel D U V → Bool)
    (haff : ∀ p ∈ P, ∃ A C : Vec D, ∀ j : Fin k,
      (fun i => (q : ℝ) * yRep q D dilation (n p j) i) =
        fun i => A i + (j.val : ℝ) * C i) :
    (P.image (fun p => literalSignature color Prod.snd (labels p)
      (fun j => ⌊normSq (fun i => (q : ℝ) * yRep q D dilation (n p j) i)⌋))).card ≤
      (P.image labels).card * (25 * (k * (D * q ^ 2 + 1) + 1) ^ 8) :=
  card_affine_yRep_signatures_le P labels n color Prod.snd haff

/-- In the finite-key application this map is the subtype's injective
inclusion into the ambient literal box/band pairs. -/
def signatureKeyMap {K : Type uK} {L : Type uL} {k : ℕ} (f : K → L)
    (σ : Fin k → Bool × K) : Fin k → Bool × L :=
  fun j => ((σ j).1, f (σ j).2)

theorem signatureKeyMap_injective {K : Type uK} {L : Type uL} {k : ℕ} {f : K → L}
    (hf : Function.Injective f) : Function.Injective (@signatureKeyMap K L k f) := by
  intro σ τ h
  funext j
  have hj := congrFun h j
  exact Prod.ext (congrArg (fun z : Bool × L => z.1) hj)
    (hf (congrArg (fun z : Bool × L => z.2) hj))

theorem card_signatureKeyMap_image {K : Type uK} {L : Type uL} {k : ℕ}
    [DecidableEq L] (f : K → L) (hf : Function.Injective f)
    (S : Finset (Fin k → Bool × K)) :
    (S.image (signatureKeyMap f)).card = S.card :=
  Finset.card_image_of_injective _ (signatureKeyMap_injective hf)

end QuantitativeVanDerWaerden

end

end OAI
end
end

section
section
namespace OAI

/-!
# Literal signatures of the actual affine cyclic progressions

The family below is defined from the actual centered representative sequence.
Its signatures retain the adaptive mesh's interval identities and the integer
norm band. The label color is fixed before the Bernoulli perturbation.
-/

noncomputable section


namespace QuantitativeVanDerWaerden
namespace CyclicColoring

open SparsePerturbation

/-- The designated affine family is the actual nonzero-step family whose
centered representative vectors are affine in the sample index. -/
def affineProgressions (q D dilation k : ℕ) [NeZero (q ^ D)] :
    Finset (CyclicGroup q D × CyclicGroup q D) := by
  classical
  exact (nonzeroProgressions (q ^ D)).filter fun ad =>
    ∃ A B : Vec D, ∀ j : Fin k,
      yRep q D dilation (ad.1 + (j.val : CyclicGroup q D) * ad.2) =
        fun i => A i + (j.val : ℝ) * B i

theorem affineProgressions_subset (q D dilation k : ℕ) [NeZero (q ^ D)] :
    affineProgressions q D dilation k ⊆ nonzeroProgressions (q ^ D) := by
  classical
  exact Finset.filter_subset _ _

@[simp] theorem mem_affineProgressions {q D dilation k : ℕ} [NeZero (q ^ D)]
    (ad : CyclicGroup q D × CyclicGroup q D) :
    ad ∈ affineProgressions q D dilation k ↔ ad.2 ≠ 0 ∧
      ∃ A B : Vec D, ∀ j : Fin k,
        yRep q D dilation (ad.1 + (j.val : CyclicGroup q D) * ad.2) =
          fun i => A i + (j.val : ℝ) * B i := by
  classical
  simp [affineProgressions]

/-- The first-system labels together with the actual second-system boxes. -/
def actualFullLabel {U : Type uU} (mesh : AdaptiveMesh) (q D dilation : ℕ)
    (first : CyclicGroup q D → Fin D → U) (n : CyclicGroup q D) :
    FullLabel D U mesh.Label :=
  (first n, secondBox mesh q D dilation n)

def actualFullLabelWord {U : Type uU} {k : ℕ}
    (mesh : AdaptiveMesh) (q D dilation : ℕ)
    (first : CyclicGroup q D → Fin D → U)
    (ad : CyclicGroup q D × CyclicGroup q D) : Fin k → FullLabel D U mesh.Label :=
  fun j => actualFullLabel mesh q D dilation first
    (ad.1 + (j.val : CyclicGroup q D) * ad.2)

/-- The actual signature count used by the sparse-perturbation budget. Its only
label-count term is the full nonzero-step cyclic label-word image. -/
theorem card_actual_affine_signatures_le {U : Type uU} [DecidableEq U]
    (mesh : AdaptiveMesh) (q D dilation k : ℕ) [NeZero (q ^ D)]
    (first : CyclicGroup q D → Fin D → U)
    (color : FullLabel D U mesh.Label → Bool) :
    ((affineProgressions q D dilation k).image (cyclicSignature (k := k)
      (fun n => color (actualFullLabel mesh q D dilation first n))
      (perturbationKey mesh q D dilation))).card ≤
      ((nonzeroProgressions (q ^ D)).image
        (actualFullLabelWord (k := k) mesh q D dilation first)).card *
        (25 * (k * (D * q ^ 2 + 1) + 1) ^ 8) := by
  classical
  have hcount := card_affine_yRep_fullLabel_signatures_le
    (affineProgressions q D dilation k)
    (actualFullLabelWord (k := k) mesh q D dilation first)
    (fun ad j => ad.1 + (j.val : CyclicGroup q D) * ad.2) color
    (show ∀ ad ∈ affineProgressions q D dilation k, ∃ A B : Vec D, ∀ j : Fin k,
      (fun i => (q : ℝ) * yRep q D dilation
        (ad.1 + (j.val : CyclicGroup q D) * ad.2) i) =
          fun i => A i + (j.val : ℝ) * B i from by
      intro ad had
      obtain ⟨A, B, hAB⟩ := ((mem_affineProgressions ad).mp had).2
      refine ⟨fun i => (q : ℝ) * A i, fun i => (q : ℝ) * B i, ?_⟩
      intro j
      funext i
      rw [hAB j]
      ring)
  have hlabels :
      ((affineProgressions q D dilation k).image
        (actualFullLabelWord (k := k) mesh q D dilation first)).card ≤
      ((nonzeroProgressions (q ^ D)).image
        (actualFullLabelWord (k := k) mesh q D dilation first)).card :=
    Finset.card_le_card (Finset.image_subset_image (affineProgressions_subset q D dilation k))
  apply le_trans _ (Nat.mul_le_mul_right _ hlabels)
  simpa +instances +unfoldPartialApp only [cyclicSignature, actualFullLabelWord, actualFullLabel, literalSignature,
    perturbationKey, yGeometricKey, geometricKey, scaledYRep] using hcount

end CyclicColoring
end QuantitativeVanDerWaerden

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace QuantitativeVanDerWaerden.Parameters

/-- The additive terms in the finite affine count fit in a factor of three. -/
theorem affine_count_factor_le {k D q : ℝ}
    (hk : 1 ≤ k) (hD : 1 ≤ D) (hq : 1 ≤ q) :
    k * (D * q ^ 2 + 1) + 1 ≤ 3 * k * D * q ^ 2 := by
  have hq2 : 1 ≤ q ^ 2 := by nlinarith
  have hDq : 1 ≤ D * q ^ 2 := one_le_mul_of_one_le_of_one_le hD hq2
  have hprod : k ≤ k * (D * q ^ 2) :=
    le_mul_of_one_le_right (by linarith) hDq
  have hprod1 : 1 ≤ k * (D * q ^ 2) := hk.trans hprod
  nlinarith

/-- A convenient multiplicative form of the actual finite count bound. -/
theorem affine_count_le_simple {k D q Tglob Taff : ℝ}
    (hk : 1 ≤ k) (hD : 1 ≤ D) (hq : 1 ≤ q)
    (hTglob : 0 ≤ Tglob)
    (hcount : Taff ≤ 25 * Tglob * (k * (D * q ^ 2 + 1) + 1) ^ 8) :
    Taff ≤ 25 * Tglob * (3 * k * D * q ^ 2) ^ 8 := by
  apply hcount.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ _ (affine_count_factor_le hk hD hq) 8
  positivity

/-- The rounded dimension contributes at most twice the logarithm of `k`. -/
theorem log_dimension_le_two_log {k : ℕ} (hk : 2 ≤ k) :
    Real.log (dimension k : ℝ) ≤ 2 * Real.log (k : ℝ) := by
  have hk1 : 1 ≤ k := le_trans (by norm_num : 1 ≤ 2) hk
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hD0 : (0 : ℝ) < dimension k := by exact_mod_cast dimension_pos hk1
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
  have hlogtwo : Real.log (2 : ℝ) ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by norm_num) hk2
  have hbound := Real.log_le_log hD0 (dimension_upper hk1)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (ne_of_gt (Real.rpow_pos_of_pos hk0 _)), Real.log_rpow hk0] at hbound
  linarith

/-- The finite affine count has entropy of order `k^(9/10) log k`, with a
constant independent of the number of colors. -/
theorem affine_entropy_bound {k : ℕ} (hk : 32 ≤ k)
    {Taff Tglob q A : ℝ}
    (hTaff : 1 ≤ Taff) (hTglob : 1 ≤ Tglob) (hq : 1 ≤ q) (hA : 0 ≤ A)
    (hcount : Taff ≤ 25 * Tglob *
      ((k : ℝ) * ((dimension k : ℝ) * q ^ 2 + 1) + 1) ^ 8)
    (hglobal : Real.log Tglob ≤
      A * (k : ℝ) ^ (3 / 10 : ℝ) * Real.log (k : ℝ))
    (hprime : Real.log q ≤
      4 * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log (k : ℝ)) :
    Real.log Taff ≤ (A + 108) * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log (k : ℝ) := by
  have hk1 : 1 ≤ k := le_trans (by norm_num : 1 ≤ 32) hk
  have hk2 : 2 ≤ k := le_trans (by norm_num : 2 ≤ 32) hk
  have hk32 : (32 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) < k := by linarith
  have hD1 : (1 : ℝ) ≤ dimension k := by
    exact_mod_cast Nat.succ_le_of_lt (dimension_pos hk1)
  have hD0 : (0 : ℝ) < dimension k := by linarith
  have hq0 : 0 < q := by linarith
  have hg0 : 0 < Tglob := by linarith
  have ha0 : 0 < Taff := by linarith
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
  have hlogD := log_dimension_le_two_log hk2
  have hlog25 : Real.log (25 : ℝ) ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog3 : Real.log (3 : ℝ) ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hsimple := affine_count_le_simple hk1r hD1 hq hg0.le hcount
  have hlogbase :
      Real.log (3 * (k : ℝ) * (dimension k : ℝ) * q ^ 2) =
        Real.log 3 + Real.log (k : ℝ) + Real.log (dimension k : ℝ) +
          2 * Real.log q := by
    rw [Real.log_mul (by positivity) (pow_ne_zero 2 hq0.ne'),
      Real.log_mul (by positivity) hD0.ne',
      Real.log_mul (by norm_num) hk0.ne', Real.log_pow]
    norm_num
  have hlogcount : Real.log Taff ≤ Real.log 25 + Real.log Tglob +
      8 * (Real.log 3 + Real.log (k : ℝ) + Real.log (dimension k : ℝ) +
        2 * Real.log q) := by
    have hb := Real.log_le_log ha0 hsimple
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) hg0.ne', Real.log_pow, hlogbase] at hb
    norm_num at hb ⊢
    exact hb
  have hfinite : Real.log Taff ≤ Real.log Tglob +
      33 * Real.log (k : ℝ) + 16 * Real.log q := by
    linarith only [hlogcount, hlog25, hlog3, hlogD]
  have hsmall : (k : ℝ) ^ (3 / 10 : ℝ) ≤ (k : ℝ) ^ (9 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hk1r (by norm_num)
  have hglobal' : Real.log Tglob ≤
      A * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log (k : ℝ) :=
    hglobal.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsmall hA) hlogk)
  have hscale : Real.log (k : ℝ) ≤
      (k : ℝ) ^ (9 / 10 : ℝ) * Real.log (k : ℝ) :=
    le_mul_of_one_le_left hlogk (Real.one_le_rpow hk1r (by norm_num))
  have hscale0 : 0 ≤ (k : ℝ) ^ (9 / 10 : ℝ) * Real.log (k : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _) hlogk
  nlinarith only [hfinite, hglobal', hprime, hscale, hscale0]

end QuantitativeVanDerWaerden.Parameters

end

end OAI
end
end

section
section
namespace OAI

/-!
# Entropy bound for a possibly empty finite signature set

The natural count may vanish. Taking its maximum with one lets the same
uniform entropy bound feed the sparse-perturbation budget in that case.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.Parameters

/-- Natural signature counts obey the maximum-with-one entropy bound, including
the empty signature set. The finite counting premise is used unchanged. -/
theorem affine_nat_entropy_bound {k T : ℕ} (hk : 32 ≤ k)
    {G q A : ℝ} (hG : 1 ≤ G) (hq : 1 ≤ q) (hA : 0 ≤ A)
    (hcount : (T : ℝ) ≤ 25 * G *
      ((k : ℝ) * ((dimension k : ℝ) * q ^ 2 + 1) + 1) ^ 8)
    (hglobal : Real.log G ≤
      A * (k : ℝ) ^ (3 / 10 : ℝ) * Real.log (k : ℝ))
    (hprime : Real.log q ≤
      4 * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log (k : ℝ)) :
    Real.log (max 1 (T : ℝ)) ≤
      (A + 108) * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log (k : ℝ) := by
  by_cases hT : T = 0
  · subst T
    have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
    simp only [Nat.cast_zero, max_eq_left (by norm_num : (0 : ℝ) ≤ 1), Real.log_one]
    positivity
  · have hTone : (1 : ℝ) ≤ T := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hT
    rw [max_eq_right hTone]
    exact affine_entropy_bound hk hTone hG hq hA hcount hglobal hprime

end QuantitativeVanDerWaerden.Parameters

end

end OAI
end
end

section
section
namespace OAI

/-!
# The sparse budget for the actual construction

The outer choice contains every actual cyclic label word. Its proved row bound
therefore controls the literal signatures of the actual affine family. All
arithmetic and mesh estimates are discharged for the chosen prime-scale data;
the resulting eventual threshold is uniform over those data and outer choices.
-/

noncomputable section

open Filter

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters SparsePerturbation CyclicColoring

variable {k : ℕ}

@[simp] theorem actualFullLabel_eq_fullLabel (s : Data k) (hk : 3 ≤ k)
    (n : Group s) :
    actualFullLabel (mesh s hk) s.q (dimension k) (lambda k)
      (firstLabel s hk) n = fullLabel s hk n := rfl

@[simp] theorem actualFullLabelWord_eq_fullLabelWord (s : Data k) (hk : 3 ≤ k)
    (ad : Group s × Group s) :
    actualFullLabelWord (k := k) (mesh s hk) s.q (dimension k) (lambda k)
      (firstLabel s hk) ad = fullLabelWord s hk ad := rfl

namespace OuterChoice

theorem words_card_pos {s : Data k} {hk : 3 ≤ k} (o : OuterChoice s hk) :
    0 < o.words.card :=
  Finset.card_pos.mpr ⟨fullLabelWord s hk (0, 0), o.word_mem (0, 0)⟩

theorem card_global_words_le {s : Data k} {hk : 3 ≤ k}
    [NeZero (s.q ^ dimension k)] (o : OuterChoice s hk) :
    ((nonzeroProgressions (s.q ^ dimension k)).image
      (actualFullLabelWord (k := k) (mesh s hk) s.q (dimension k) (lambda k)
        (firstLabel s hk))).card ≤ o.words.card := by
  classical
  apply Finset.card_le_card
  intro w hw
  obtain ⟨ad, _, rfl⟩ := Finset.mem_image.mp hw
  exact o.word_mem ad

/-- The degree-six global row count has entropy constant 520. -/
theorem log_words_card_le {s : Data k} {hk : 3 ≤ k}
    (o : OuterChoice s hk) (hk32 : 32 ≤ k) :
    Real.log (o.words.card : ℝ) ≤
      520 * (k : ℝ) ^ (3 / 10 : ℝ) * Real.log k := by
  let F : ℝ := ((uniformCount k + Fintype.card (mesh s hk).Label : ℕ) : ℝ)
  have hL : (1 : ℝ) ≤ lambda k := by
    exact_mod_cast Nat.succ_le_of_lt (lambda_pos k)
  have hF : (1 : ℝ) ≤ F := by
    dsimp [F]
    exact_mod_cast ((Nat.succ_le_of_lt (uniformCount_pos hk)).trans
      (Nat.le_add_right (uniformCount k) (Fintype.card (mesh s hk).Label)))
  have hLlog : Real.log (lambda k : ℝ) ≤
      (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)) := by
    calc
      Real.log (lambda k : ℝ) ≤
          ((dimension k ^ 2 : ℕ) : ℝ) * Real.log (2 * (cutoff k : ℝ)) :=
        log_dilation_le (h₀ := dimension k ^ 2) (cutoff_pos (by omega : 1 ≤ k))
      _ = (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)) :=
        congrArg (fun x : ℝ => x * Real.log (2 * (cutoff k : ℝ)))
          (Nat.cast_pow (dimension k) 2)
  have hmesh : F ≤ (k : ℝ) ^ 2 * (lambda k : ℝ) +
      28 * (k : ℝ) ^ 3 * Real.log k := by
    dsimp [F]
    rw [Nat.cast_add, uniformCount, Nat.cast_mul, Nat.cast_pow]
    exact add_le_add_right (card_second_labels_le s hk) _
  have hcount : (o.words.card : ℝ) ≤
      (16 * (3 * (k : ℝ) ^ 2 * F + 1) ^ (6 : ℕ)) ^
        (2 * dimension k) := by
    dsimp [F]
    exact_mod_cast o.card_le
  have hpos : (0 : ℝ) < o.words.card := by exact_mod_cast o.words_card_pos
  have h := log_global_count_le (e := 6) hk32 hL hF hpos hLlog hmesh hcount
  norm_num at h
  exact h

/-- The actual affine family retains the actual geometric keys and colors. -/
theorem card_affine_signatures_le {s : Data k} {hk : 3 ≤ k}
    [NeZero (s.q ^ dimension k)] (o : OuterChoice s hk) :
    ((affineProgressions s.q (dimension k) (lambda k) k).image
      (cyclicSignature (k := k) (fun n => o.color (fullLabel s hk n))
        (perturbationKey (mesh s hk) s.q (dimension k) (lambda k)))).card ≤
      o.words.card * (25 * (k * (dimension k * s.q ^ 2 + 1) + 1) ^ 8) := by
  classical
  have h := card_actual_affine_signatures_le
    (mesh s hk) s.q (dimension k) (lambda k) k (firstLabel s hk) o.color
  simp only [actualFullLabel_eq_fullLabel] at h
  exact h.trans (Nat.mul_le_mul_right _ o.card_global_words_le)

/-- Literal affine signatures have entropy constant 628, also when their
finite image is empty. -/
theorem log_affine_signatures_le {s : Data k} {hk : 3 ≤ k}
    [NeZero (s.q ^ dimension k)] (o : OuterChoice s hk) (hk32 : 32 ≤ k) :
    Real.log (max 1
      (((affineProgressions s.q (dimension k) (lambda k) k).image
        (cyclicSignature (k := k) (fun n => o.color (fullLabel s hk n))
          (perturbationKey (mesh s hk) s.q (dimension k) (lambda k)))).card : ℝ)) ≤
      628 * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log k := by
  classical
  have hcount := o.card_affine_signatures_le
  have hcast :
      (((affineProgressions s.q (dimension k) (lambda k) k).image
        (cyclicSignature (k := k) (fun n => o.color (fullLabel s hk n))
          (perturbationKey (mesh s hk) s.q (dimension k) (lambda k)))).card : ℝ) ≤
      (o.words.card : ℝ) * (25 *
        ((k : ℝ) * ((dimension k : ℝ) * (s.q : ℝ) ^ 2 + 1) + 1) ^ 8) := by
    exact_mod_cast hcount
  have hcountR :
      (((affineProgressions s.q (dimension k) (lambda k) k).image
        (cyclicSignature (k := k) (fun n => o.color (fullLabel s hk n))
          (perturbationKey (mesh s hk) s.q (dimension k) (lambda k)))).card : ℝ) ≤
      25 * (o.words.card : ℝ) *
        ((k : ℝ) * ((dimension k : ℝ) * (s.q : ℝ) ^ 2 + 1) + 1) ^ 8 := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hcast
  have hG : (1 : ℝ) ≤ o.words.card := by
    exact_mod_cast Nat.succ_le_of_lt o.words_card_pos
  have hq : (1 : ℝ) ≤ s.q := by
    exact_mod_cast (show 1 ≤ s.q by have := s.two_le; omega)
  have hprime := scalar_log_q_le (by omega : 2 ≤ k)
    (s.log_upper (by omega) (dimension_pos (by omega : 1 ≤ k)))
  have h := affine_nat_entropy_bound hk32 hG hq (by norm_num : (0 : ℝ) ≤ 520)
    hcountR (o.log_words_card_le hk32) hprime
  norm_num at h
  exact h

end OuterChoice

/-- A single threshold makes the exact sparse-perturbation budget less than
one for every actual arithmetic datum and every actual outer choice. -/
theorem eventually_outerChoice_sparse_budget :
    ∀ᶠ k : ℕ in atTop, ∀ hk : 3 ≤ k, ∀ s : Data k, ∀ o : OuterChoice s hk,
      letI : NeZero (s.q ^ dimension k) := groupSize_neZero s
      2 * (groupSize s : ℝ) ^ 2 * flipProbability k ^ ((k + 399) / 400) +
        2 * (((affineProgressions s.q (dimension k) (lambda k) k).image
          (cyclicSignature (k := k) (fun n => o.color (fullLabel s hk n))
            (perturbationKey (mesh s hk) s.q (dimension k) (lambda k)))).card : ℝ) *
          (1 - flipProbability k) ^ ((k + 3) / 4) < 1 := by
  filter_upwards [eventually_ge_atTop (32 : ℕ),
    eventually_sparse_budget (C := 628) (by norm_num)] with k hk32 hb hk s o
  let : NeZero (s.q ^ dimension k) := groupSize_neZero s
  exact hb s.q s.pos _
    (s.log_upper (by omega) (dimension_pos (by omega : 1 ≤ k)))
    (o.log_affine_signatures_le hk32)

end QuantitativeVanDerWaerden.ConstructionModel

end

end OAI
end
end

section
section
namespace OAI

/-! Elementary case selection for the geometric dichotomy. Lightness refers
to full-word multiplicities throughout; restriction to a block never changes it. -/


namespace QuantitativeVanDerWaerden

theorem exists_heavy_label_of_few_light {Label : Type uLabel} [DecidableEq Label]
    {k M : ℕ} (word : Fin k → Label)
    (hfew : ¬ k ≤ 10 * (OuterWordTests.lightPositions M word).card) :
    ∃ i : Fin k, k < M * OuterWordTests.multiplicity word (word i) := by
  classical
  have hc : (OuterWordTests.lightPositions M word).card <
      (Finset.univ : Finset (Fin k)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨i, Nat.lt_of_not_ge ?_⟩
  intro h
  exact hi ((OuterWordTests.mem_lightPositions M word i).mpr h)

theorem heavy_label_has_two_visits {Label : Type uLabel} [DecidableEq Label]
    {k M : ℕ} (word : Fin k → Label) (beta : Label) (hMk : M ≤ k)
    (hheavy : k < M * OuterWordTests.multiplicity word beta) :
    ∃ a b : Fin k, a ≠ b ∧ word a = beta ∧ word b = beta := by
  classical
  have hm : 1 < OuterWordTests.multiplicity word beta := by
    by_contra h
    have hle : OuterWordTests.multiplicity word beta ≤ 1 := Nat.le_of_not_gt h
    have hmul := Nat.mul_le_mul_left M hle
    simp only [Nat.mul_one] at hmul
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hm
  exact ⟨a, b, hab, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2⟩

theorem rich_or_heavy_word {Label : Type uLabel} [DecidableEq Label]
    {k M : ℕ} (word : Fin k → Label) (color : Label → Bool)
    (hbalance : k ≤ 10 * (OuterWordTests.lightPositions M word).card →
      ∀ b, (OuterWordTests.lightPositions M word).card ≤
        4 * ((OuterWordTests.lightPositions M word).filter fun j => color (word j) = b).card) :
    (∀ b, k ≤ 100 * (Finset.univ.filter fun j => color (word j) = b).card) ∨
      ((¬ k ≤ 10 * (OuterWordTests.lightPositions M word).card) ∧
        ∃ i : Fin k, k < M * OuterWordTests.multiplicity word (word i)) := by
  classical
  by_cases hlight : k ≤ 10 * (OuterWordTests.lightPositions M word).card
  · exact Or.inl (rich_of_light_balanced word color hlight (hbalance hlight))
  · exact Or.inr ⟨hlight, exists_heavy_label_of_few_light word hlight⟩

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Finite fibers of labels in an indexed word

Natural-number indices make differences and return times convenient. The
cardinality bridge identifies this fiber with the usual multiplicity counted
over `Fin k`, and separation of the fiber excludes every earlier return.
-/


namespace QuantitativeVanDerWaerden

/-- Indices before `k` at which the word has label `l`. -/
noncomputable def labelFiber {β : Type uBeta} (k : ℕ) (f : ℕ → β) (l : β) : Finset ℕ := by
  classical
  exact (Finset.range k).filter (fun j => f j = l)

@[simp]
theorem mem_labelFiber {β : Type uBeta} {k j : ℕ} {f : ℕ → β} {l : β} :
    j ∈ labelFiber k f l ↔ j < k ∧ f j = l := by
  classical
  simp [labelFiber]

open scoped Classical in
/-- The natural-index fiber counts exactly the label multiplicity over `Fin k`. -/
theorem card_labelFiber {β : Type uBeta} (k : ℕ) (f : ℕ → β) (l : β) :
    (labelFiber k f l).card =
      (Finset.univ.filter (fun j : Fin k => f j.val = l)).card := by
  classical
  symm
  refine Finset.card_bij (fun (a : Fin k) _ => a.val) ?_ ?_ ?_
  · intro a ha
    exact mem_labelFiber.mpr ⟨a.isLt, (Finset.mem_filter.mp ha).2⟩
  · intro a ha b hb hab
    exact Fin.ext hab
  · intro b hb
    have h := mem_labelFiber.mp hb
    refine ⟨⟨b, h.1⟩, ?_, rfl⟩
    simpa using h.2

/-- A minimum positive gap between occurrences of a label rules out a return
at every positive time below that gap. -/
theorem no_earlier_label_return {β : Type uBeta} {k j h : ℕ} {f : ℕ → β} {l : β}
    (hj : j ∈ labelFiber k f l) (hjh : j + h < k)
    (hmin : ∀ a ∈ labelFiber k f l, ∀ b ∈ labelFiber k f l,
      a < b → h ≤ b - a) :
    ∀ t, 0 < t → t < h → f (j + t) ≠ l := by
  intro t ht hth hlabel
  have hmem : j + t ∈ labelFiber k f l :=
    mem_labelFiber.mpr ⟨by omega, hlabel⟩
  have hgap := hmin j hj (j + t) hmem (by omega)
  omega

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Real-representative lemmas for the outer-color dichotomy

The integer congruences here are the concrete meaning of equality modulo one.
In particular, the heavy-interval estimate uses only its two endpoint
representatives and does not assume that the path between them avoids a cut.
-/

namespace QuantitativeVanDerWaerden

theorem real_eq_of_integer_difference_small {a b : ℝ}
    (hint : ∃ z : ℤ, a - b = (z : ℝ)) (hsmall : |a - b| < 1) : a = b := by
  obtain ⟨z, hz⟩ := hint
  rw [hz] at hsmall
  have hz0 := integer_zero_of_abs_lt_one hsmall
  simp only [hz0, Int.cast_zero] at hz
  linarith

/-- The short displacement in the two coordinate systems agrees over the reals. -/
theorem dilation_drift_eq {u v lam A B : ℝ}
    (hint : ∃ z : ℤ, v - lam * u = (z : ℝ))
    (hv : |v| ≤ A) (hu : |lam * u| ≤ B) (hsmall : A + B < 1) : v = lam * u := by
  apply real_eq_of_integer_difference_small hint
  exact lt_of_le_of_lt ((abs_sub v (lam * u)).trans (add_le_add hv hu)) hsmall

/-- Endpoint congruence and short total drift give equality before reduction modulo one. -/
theorem heavy_endpoint_eq {Δ a v L T : ℝ}
    (hint : ∃ z : ℤ, Δ - a * v = (z : ℝ))
    (hΔ : |Δ| ≤ L) (hv : |a * v| ≤ T) (hsmall : L + T < 1) : Δ = a * v := by
  apply real_eq_of_integer_difference_small hint
  exact lt_of_le_of_lt ((abs_sub Δ (a * v)).trans (add_le_add hΔ hv)) hsmall

theorem heavy_interval_drift_div {Δ a v L T : ℝ}
    (ha : 0 < a) (hint : ∃ z : ℤ, Δ - a * v = (z : ℝ))
    (hΔ : |Δ| ≤ L) (hv : |a * v| ≤ T) (hsmall : L + T < 1) : |v| ≤ L / a := by
  have heq := heavy_endpoint_eq hint hΔ hv hsmall
  have hmul : a * |v| ≤ L := by
    simpa only [heq, abs_mul, abs_of_pos ha] using hΔ
  exact (le_div_iff₀ ha).2 (by simpa only [mul_comm] using hmul)

/-- The relative-width estimate for every heavy interval in the progression. -/
theorem heavy_interval_relative_drift {Δ a v L T k M : ℝ}
    (hk : 0 < k) (hM : 0 < M) (ha : k / (2 * M) ≤ a)
    (hint : ∃ z : ℤ, Δ - a * v = (z : ℝ))
    (hΔ : |Δ| ≤ L) (hv : |a * v| ≤ T) (hsmall : L + T < 1) :
    |v| ≤ (2 * M / k) * L := by
  have h2M : 0 < 2 * M := by positivity
  have ha0 : 0 < a := lt_of_lt_of_le (div_pos hk h2M) ha
  have heq := heavy_endpoint_eq hint hΔ hv hsmall
  have hmul : a * |v| ≤ L := by
    simpa only [heq, abs_mul, abs_of_pos ha0] using hΔ
  have hak : k ≤ a * (2 * M) := (div_le_iff₀ h2M).1 ha
  have hfinal : |v| * k ≤ 2 * M * L := by
    calc
      |v| * k ≤ |v| * (a * (2 * M)) :=
        mul_le_mul_of_nonneg_left hak (abs_nonneg v)
      _ = (2 * M) * (a * |v|) := by ring
      _ ≤ (2 * M) * L := mul_le_mul_of_nonneg_left hmul h2M.le
  calc
    |v| ≤ (2 * M * L) / k := (le_div_iff₀ hk).2 hfinal
    _ = (2 * M / k) * L := by ring

/-- A discrete nonzero step makes every cut-near adaptive interval narrower
than one step. -/
theorem short_cut_interval_lt_step {H k ρ α width w : ℝ}
    (hH : 0 ≤ H) (hw : w ≠ 0) (hα : α ≤ |w|) (hρ : ρ ≤ k * |w|)
    (hwidth : width ≤ 2 * H * (ρ + α)) (hsmall : 2 * H * (k + 1) < 1) :
    width < |w| := by
  have hstep : 0 < |w| := abs_pos.mpr hw
  have hsum : ρ + α ≤ (k + 1) * |w| := by nlinarith
  calc
    width ≤ 2 * H * (ρ + α) := hwidth
    _ ≤ 2 * H * ((k + 1) * |w|) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (2 * H * (k + 1)) * |w| := by ring
    _ < 1 * |w| := mul_lt_mul_of_pos_right hsmall hstep
    _ = |w| := one_mul _

theorem abs_nat_difference_ge_one {a b : ℕ} (hab : a ≠ b) :
    (1 : ℝ) ≤ |(a : ℝ) - b| := by
  rcases lt_or_gt_of_ne hab with h | h
  · have h' : (a : ℝ) + 1 ≤ b := by exact_mod_cast (Nat.succ_le_of_lt h)
    rw [abs_of_nonpos (by linarith : (a : ℝ) - b ≤ 0)]
    linarith
  · have h' : (b : ℝ) + 1 ≤ a := by exact_mod_cast (Nat.succ_le_of_lt h)
    rw [abs_of_nonneg (by linarith : 0 ≤ (a : ℝ) - b)]
    linarith

/-- Distinct samples of a short nonzero real step cannot occupy an interval
narrower than the step, even if their representatives cross the cut. -/
theorem short_step_not_same_interval {a b k : ℕ} {za zb w : ℝ}
    (hab : a ≠ b) (hak : a < k) (hbk : b < k)
    (hmotion : (k : ℝ) * |w| < 1 / 2)
    (hint : ∃ z : ℤ, (za - zb) - ((a : ℝ) - b) * w = (z : ℝ))
    (hnarrow : |za - zb| < |w|) : False := by
  have hk : 1 ≤ k := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le a) hak)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hak' : (a : ℝ) ≤ k := by exact_mod_cast hak.le
  have hbk' : (b : ℝ) ≤ k := by exact_mod_cast hbk.le
  have hw0 := abs_nonneg w
  have hwsmall : |w| < 1 / 2 := by nlinarith
  have hdiff : |(a : ℝ) - b| ≤ k := abs_le.mpr ⟨by linarith, by linarith⟩
  have hprod : |((a : ℝ) - b) * w| < 1 / 2 := by
    rw [abs_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hdiff hw0) hmotion
  have hzero : za - zb = ((a : ℝ) - b) * w := by
    apply real_eq_of_integer_difference_small hint
    have hh := abs_sub (za - zb) (((a : ℝ) - b) * w)
    linarith
  have hlower : |w| ≤ |((a : ℝ) - b) * w| := by
    rw [abs_mul]
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right (abs_nat_difference_ge_one hab) hw0)
  rw [hzero] at hnarrow
  exact (not_lt_of_ge hlower) hnarrow

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# The minimum positive gap in a finite set of indices

A set of `n` ordered indices whose distinct elements are separated by at least
`h` occupies a span of at least `h * (n - 1)`. Taking the least positive gap
therefore supplies a closest-return pair with this packing bound.
-/

namespace QuantitativeVanDerWaerden

/-- Pairwise separation forces a lower bound on the span of a finite set.
The proof adds the largest index and accounts for its gap from the preceding
largest index. -/
theorem gap_mul_card_sub_one_le_span (J : Finset ℕ) (hJ : J.Nonempty) (h : ℕ)
    (hgap : ∀ i ∈ J, ∀ j ∈ J, i < j → h ≤ j - i) :
    h * (J.card - 1) ≤ J.max' hJ - J.min' hJ := by
  have aux : ∀ s : Finset ℕ, ∀ hs : s.Nonempty,
      (∀ i ∈ s, ∀ j ∈ s, i < j → h ≤ j - i) →
      h * (s.card - 1) ≤ s.max' hs - s.min' hs := by
    intro s
    induction s using Finset.induction_on_max with
    | empty =>
        intro hs
        simp at hs
    | insert a s ha ih =>
        intro hins hsep
        rcases s.eq_empty_or_nonempty with rfl | hs
        · simp
        · have hane : a ∉ s := by
            intro hamem
            exact (ha a hamem).false
          have hmax : s.max' hs < a := ha _ (s.max'_mem hs)
          have hmin : s.min' hs < a := ha _ (s.min'_mem hs)
          have hminmax : s.min' hs ≤ s.max' hs :=
            s.min'_le _ (s.max'_mem hs)
          have hprev := ih hs (fun i hi j hj hij =>
            hsep i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
          have hlast : h ≤ a - s.max' hs :=
            hsep _ (Finset.mem_insert_of_mem (s.max'_mem hs))
              a (Finset.mem_insert_self a s) hmax
          have hcard : 1 ≤ s.card := Finset.card_pos.mpr hs
          have hmul : h * s.card = h * (s.card - 1) + h := by
            calc
              h * s.card = h * ((s.card - 1) + 1) :=
                congrArg (fun n : ℕ => h * n) (Nat.sub_add_cancel hcard).symm
              _ = h * (s.card - 1) + h := by
                simp only [Nat.mul_add, Nat.mul_one]
          rw [Finset.card_insert_of_notMem hane, Nat.add_sub_cancel,
            Finset.max'_insert a s hs, Finset.min'_insert a s hs,
            max_eq_left hmax.le, min_eq_right hmin.le, hmul]
          omega
  exact aux J hJ hgap

/-- Every finite set with at least two elements has an attained minimum
positive gap; its size also obeys the packing bound. -/
theorem exists_min_gap (J : Finset ℕ) (hcard : 2 ≤ J.card) :
    ∃ a ∈ J, ∃ b ∈ J, a < b ∧ 0 < b - a ∧
      (∀ i ∈ J, ∀ j ∈ J, i < j → b - a ≤ j - i) ∧
      (∀ hJ : J.Nonempty,
        (b - a) * (J.card - 1) ≤ J.max' hJ - J.min' hJ) := by
  classical
  have hex : ∃ d : ℕ, ∃ a ∈ J, ∃ b ∈ J, a < b ∧ d = b - a := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < J.card by omega)
    rcases lt_or_gt_of_ne hab with hab | hba
    · exact ⟨b - a, a, ha, b, hb, hab, rfl⟩
    · exact ⟨a - b, b, hb, a, ha, hba, rfl⟩
  obtain ⟨a, ha, b, hb, hab, hd⟩ := Nat.find_spec hex
  have hminimum : ∀ i ∈ J, ∀ j ∈ J, i < j → b - a ≤ j - i := by
    intro i hi j hj hij
    rw [← hd]
    exact Nat.find_min' hex ⟨i, hi, j, hj, hij, rfl⟩
  refine ⟨a, ha, b, hb, hab, Nat.sub_pos_of_lt hab, hminimum, ?_⟩
  intro hJ
  exact gap_mul_card_sub_one_le_span J hJ (b - a) hminimum

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Scalar estimates for a heavy set of return indices

If a set contains more than `k / M` indices and `2 * M ≤ k`, its cardinality
minus one controls the length of the ambient progression. These estimates
convert the span bounds into the rate and gap bounds used for closest returns.
-/

namespace QuantitativeVanDerWaerden

/-- A heavy set has at least two points and a positive span. The span is large
enough to absorb the ambient length after multiplication by `2 * M`. -/
theorem heavy_card_estimates {M : ℝ} {k m : ℕ}
    (hM : 0 < M) (hscale : 2 * M ≤ (k : ℝ))
    (hheavy : (k : ℝ) / M < (m : ℝ)) :
    2 ≤ m ∧ 0 < (m : ℝ) - 1 ∧
      (k : ℝ) ≤ ((m : ℝ) - 1) * (2 * M) ∧ 0 < k := by
  have hkR : 0 < (k : ℝ) :=
    lt_of_lt_of_le (mul_pos (by norm_num) hM) hscale
  have hkm : (k : ℝ) < (m : ℝ) * M := (div_lt_iff₀ hM).mp hheavy
  have hmR : (2 : ℝ) < (m : ℝ) :=
    (mul_lt_mul_iff_left₀ hM).mp (hscale.trans_lt hkm)
  have hmNat : 2 ≤ m := by exact_mod_cast hmR.le
  have hspan : 0 < (m : ℝ) - 1 := by linarith only [hmR]
  have hlower : (k : ℝ) ≤ ((m : ℝ) - 1) * (2 * M) := by
    nlinarith only [hscale, hkm]
  have hkNat : 0 < k := by exact_mod_cast hkR
  exact ⟨hmNat, hspan, hlower, hkNat⟩

/-- Division form of the lower bound on the cardinality minus one. -/
theorem heavy_card_div_lower {M : ℝ} {k m : ℕ}
    (hM : 0 < M) (hscale : 2 * M ≤ (k : ℝ))
    (hheavy : (k : ℝ) / M < (m : ℝ)) :
    (k : ℝ) / (2 * M) ≤ (m : ℝ) - 1 := by
  obtain ⟨_, _, hlower, _⟩ := heavy_card_estimates hM hscale hheavy
  exact (div_le_iff₀ (mul_pos (by norm_num) hM)).mpr hlower

/-- A nonnegative displacement divided by the heavy-set span has rate at most
`2 * M` times the displacement divided by the ambient length. -/
theorem heavy_card_rate_le {M L : ℝ} {k m : ℕ}
    (hM : 0 < M) (hscale : 2 * M ≤ (k : ℝ))
    (hheavy : (k : ℝ) / M < (m : ℝ)) (hL : 0 ≤ L) :
    L / ((m : ℝ) - 1) ≤ 2 * M * L / (k : ℝ) := by
  obtain ⟨_, hspan, hlower, hk⟩ := heavy_card_estimates hM hscale hheavy
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  apply (div_le_div_iff₀ hspan hkR).mpr
  calc
    L * (k : ℝ) ≤ L * (((m : ℝ) - 1) * (2 * M)) :=
      mul_le_mul_of_nonneg_left hlower hL
    _ = (2 * M * L) * ((m : ℝ) - 1) := by ring

/-- A gap whose product with the heavy-set span fits in the ambient length is
at most `2 * M`. This bound does not require the gap to be nonnegative. -/
theorem heavy_card_gap_le {M h : ℝ} {k m : ℕ}
    (hM : 0 < M) (hscale : 2 * M ≤ (k : ℝ))
    (hheavy : (k : ℝ) / M < (m : ℝ))
    (hstep : h * ((m : ℝ) - 1) ≤ (k : ℝ)) :
    h ≤ 2 * M := by
  obtain ⟨_, hspan, hlower, _⟩ := heavy_card_estimates hM hscale hheavy
  apply (mul_le_mul_iff_left₀ hspan).mp
  calc
    h * ((m : ℝ) - 1) ≤ (k : ℝ) := hstep
    _ ≤ ((m : ℝ) - 1) * (2 * M) := hlower
    _ = (2 * M) * ((m : ℝ) - 1) := mul_comm _ _

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Closest return and its real displacement

The finite minimum-gap argument supplies a selected pair. Affinity in a small
box makes its displacement proportional to that of the two extreme selected
indices. Multiplying by the number of gaps avoids any division by the span.
-/


namespace QuantitativeVanDerWaerden

/-- A short affine index gap inherits the endpoint width divided by the number
of gaps. This form makes all four evaluated representatives explicit. -/
theorem affine_pair_bound_of_packing {z : ℕ → ℝ} {a b p q : ℕ}
    {A B L n : ℝ}
    (ha : z a = A + (a : ℝ) * B) (hb : z b = A + (b : ℝ) * B)
    (hp : z p = A + (p : ℝ) * B) (hq : z q = A + (q : ℝ) * B)
    (hab : a ≤ b) (hpq : p ≤ q) (hn : 0 < n)
    (hpacking : ((b : ℝ) - a) * n ≤ (q : ℝ) - p)
    (hwidth : |z q - z p| ≤ L) : |z b - z a| ≤ L / n := by
  have hpair : z b - z a = ((b : ℝ) - a) * B := by rw [ha, hb]; ring
  have hspan : z q - z p = ((q : ℝ) - p) * B := by rw [hp, hq]; ring
  have habR : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
  have hpqR : 0 ≤ (q : ℝ) - p := sub_nonneg.mpr (by exact_mod_cast hpq)
  apply (le_div_iff₀ hn).2
  calc
    |z b - z a| * n = (((b : ℝ) - a) * n) * |B| := by
      rw [hpair, abs_mul, abs_of_nonneg habR]
      ring
    _ ≤ ((q : ℝ) - p) * |B| := mul_le_mul_of_nonneg_right hpacking (abs_nonneg B)
    _ = |z q - z p| := by rw [hspan, abs_mul, abs_of_nonneg hpqR]
    _ ≤ L := hwidth

/-- The preceding displacement estimate on a finite selected set. -/
theorem affine_selected_pair_bound {J : Finset ℕ} (hJ : J.Nonempty)
    {z : ℕ → ℝ} {a b : ℕ} {A B L : ℝ}
    (hcard : 2 ≤ J.card) (ha : a ∈ J) (hb : b ∈ J) (hab : a < b)
    (haff : ∀ j ∈ J, z j = A + (j : ℝ) * B)
    (hpacking : (b - a) * (J.card - 1) ≤ J.max' hJ - J.min' hJ)
    (hwidth : |z (J.max' hJ) - z (J.min' hJ)| ≤ L) :
    |z b - z a| ≤ L / ((J.card : ℝ) - 1) := by
  have hp := J.min'_mem hJ
  have hq := J.max'_mem hJ
  have hpq : J.min' hJ ≤ J.max' hJ := J.min'_le _ hq
  have hc1 : 1 ≤ J.card := le_trans (by decide : 1 ≤ 2) hcard
  have hcR : (2 : ℝ) ≤ J.card := by exact_mod_cast hcard
  have hn : 0 < (J.card : ℝ) - 1 := by linarith
  have hpackingR : (((b - a) * (J.card - 1) : ℕ) : ℝ) ≤
      ((J.max' hJ - J.min' hJ : ℕ) : ℝ) := by exact_mod_cast hpacking
  rw [Nat.cast_mul, Nat.cast_sub hab.le, Nat.cast_sub hc1, Nat.cast_one,
    Nat.cast_sub hpq] at hpackingR
  exact affine_pair_bound_of_packing (haff a ha) (haff b hb)
    (haff _ hp) (haff _ hq) hab.le hpq hn hpackingR hwidth

/-- Convert the minimum-gap packing estimate into the two quotient bounds in
the closest-return argument. -/
theorem selected_gap_bounds {J : Finset ℕ} {k a b : ℕ} {M : ℝ}
    (hJ : J.Nonempty) (hJbound : ∀ j ∈ J, j < k)
    (hM : 0 < M) (hscale : 2 * M ≤ (k : ℝ))
    (hheavy : (k : ℝ) / M < J.card)
    (hpacking : (b - a) * (J.card - 1) ≤ J.max' hJ - J.min' hJ) :
    ((b - a : ℕ) : ℝ) ≤ ((J.max' hJ - J.min' hJ : ℕ) : ℝ) / ((J.card : ℝ) - 1) ∧
      ((J.max' hJ - J.min' hJ : ℕ) : ℝ) / ((J.card : ℝ) - 1) ≤ 2 * M := by
  obtain ⟨hcard, hn, hkden, _⟩ := heavy_card_estimates hM hscale hheavy
  have hc1 : 1 ≤ J.card := le_trans (by decide : 1 ≤ 2) hcard
  have hpackingR : (((b - a) * (J.card - 1) : ℕ) : ℝ) ≤
      ((J.max' hJ - J.min' hJ : ℕ) : ℝ) := by exact_mod_cast hpacking
  rw [Nat.cast_mul, Nat.cast_sub hc1, Nat.cast_one] at hpackingR
  have hspanNat : J.max' hJ - J.min' hJ ≤ k :=
    (Nat.sub_le _ _).trans (hJbound _ (J.max'_mem hJ)).le
  have hspan : ((J.max' hJ - J.min' hJ : ℕ) : ℝ) ≤ k := by exact_mod_cast hspanNat
  refine ⟨(le_div_iff₀ hn).2 hpackingR, (div_le_iff₀ hn).2 ?_⟩
  nlinarith

/-- Taking the difference of two representatives preserves the integer
congruence between the dilated and original coordinate systems. -/
theorem integer_dilation_difference {x y : ℕ → ℝ} {lam : ℝ}
    (h : ∀ j, ∃ m : ℤ, y j - lam * x j = (m : ℝ)) (a b : ℕ) :
    ∃ m : ℤ, (y b - y a) - lam * (x b - x a) = (m : ℝ) := by
  obtain ⟨ma, ha⟩ := h a
  obtain ⟨mb, hb⟩ := h b
  refine ⟨mb - ma, ?_⟩
  calc
    (y b - y a) - lam * (x b - x a) =
        (y b - lam * x b) - (y a - lam * x a) := by ring
    _ = (mb : ℝ) - (ma : ℝ) := by rw [ha, hb]
    _ = ((mb - ma : ℤ) : ℝ) := by push_cast; ring

/-- The actual closest-return and coordinate drift bounds for two systems of
real representatives of arithmetic progressions modulo one. The selected pair
and its minimality are constructed from `J`; affine behavior is proved from
the small-box hypotheses. -/
theorem exists_closest_return_drift {ι : Type uIndex} {J : Finset ℕ} {k : ℕ}
    {M H Hx lam : ℝ} {x y : ℕ → ι → ℝ} {x0 x1 y0 y1 : ι → ℝ}
    (hJbound : ∀ j ∈ J, j < k)
    (hM : 0 < M) (hscale : 2 * M ≤ (k : ℝ))
    (hheavy : (k : ℝ) / M < J.card)
    (hH : 0 ≤ H) (hHx : 0 ≤ Hx) (hHxH : Hx ≤ 2 * H)
    (hsmall : 2 * (k : ℝ) * H < 1)
    (hxbox : ∀ i ∈ J, ∀ j ∈ J, ∀ d, |x j d - x i d| ≤ Hx)
    (hybox : ∀ i ∈ J, ∀ j ∈ J, ∀ d, |y j d - y i d| ≤ 2 * H)
    (hxmod : ∀ j d, ∃ m : ℤ, x j d - x0 d - (j : ℝ) * x1 d = (m : ℝ))
    (hymod : ∀ j d, ∃ m : ℤ, y j d - y0 d - (j : ℝ) * y1 d = (m : ℝ))
    (hlam : 0 ≤ lam) (hlamHx : lam * Hx = H)
    (hdil : ∀ j d, ∃ m : ℤ, y j d - lam * x j d = (m : ℝ))
    (hdriftsmall : 6 * M * H / (k : ℝ) < 1) :
    ∃ j h : ℕ, j ∈ J ∧ j + h ∈ J ∧ 0 < h ∧ j + h < k ∧
      (∀ a ∈ J, ∀ b ∈ J, a < b → h ≤ b - a) ∧
      (∀ hJ : J.Nonempty,
        (h : ℝ) ≤ ((J.max' hJ - J.min' hJ : ℕ) : ℝ) / ((J.card : ℝ) - 1) ∧
        ((J.max' hJ - J.min' hJ : ℕ) : ℝ) / ((J.card : ℝ) - 1) ≤ 2 * M) ∧
      (h : ℝ) ≤ 2 * M ∧
      (∀ d,
        |x (j + h) d - x j d| ≤ Hx / ((J.card : ℝ) - 1) ∧
        |x (j + h) d - x j d| ≤ 2 * M * Hx / (k : ℝ) ∧
        |y (j + h) d - y j d| ≤ (2 * H) / ((J.card : ℝ) - 1) ∧
        |y (j + h) d - y j d| ≤ 4 * M * H / (k : ℝ) ∧
        y (j + h) d - y j d = lam * (x (j + h) d - x j d)) := by
  obtain ⟨hcard, hn, hkden, hk⟩ := heavy_card_estimates hM hscale hheavy
  obtain ⟨a, ha, b, hb, hab, hgap, hminimum, hpacking⟩ := exists_min_gap J hcard
  have hJ : J.Nonempty := ⟨a, ha⟩
  obtain ⟨Ax, Bx, hAx⟩ := exists_affine_of_small_box_vector J x hJbound hH hsmall
    (fun i hi j hj d => (hxbox i hi j hj d).trans hHxH)
    (fun a _ b _ c _ _ _ d =>
      triple_integral_of_integer_errors (fun j => hxmod j d) a b c)
  obtain ⟨Ay, By, hAy⟩ := exists_affine_of_small_box_vector J y hJbound hH hsmall hybox
    (fun a _ b _ c _ _ _ d =>
      triple_integral_of_integer_errors (fun j => hymod j d) a b c)
  have hbounds (hne : J.Nonempty) :=
    selected_gap_bounds hne hJbound hM hscale hheavy (hpacking hne)
  have hgapM : ((b - a : ℕ) : ℝ) ≤ 2 * M := (hbounds hJ).1.trans (hbounds hJ).2
  have heq : a + (b - a) = b := Nat.add_sub_of_le hab.le
  refine ⟨a, b - a, ?_⟩
  rw [heq]
  refine ⟨ha, hb, hgap, hJbound b hb, hminimum, hbounds, hgapM, ?_⟩
  intro d
  have hxshort : |x b d - x a d| ≤ Hx / ((J.card : ℝ) - 1) :=
    affine_selected_pair_bound hJ hcard ha hb hab (fun j hj => hAx j hj d)
      (hpacking hJ) (hxbox _ (J.min'_mem hJ) _ (J.max'_mem hJ) d)
  have hyshort : |y b d - y a d| ≤ (2 * H) / ((J.card : ℝ) - 1) :=
    affine_selected_pair_bound hJ hcard ha hb hab (fun j hj => hAy j hj d)
      (hpacking hJ) (hybox _ (J.min'_mem hJ) _ (J.max'_mem hJ) d)
  have hxrate : |x b d - x a d| ≤ 2 * M * Hx / (k : ℝ) :=
    hxshort.trans (heavy_card_rate_le hM hscale hheavy hHx)
  have hyrate : |y b d - y a d| ≤ 4 * M * H / (k : ℝ) := by
    calc
      |y b d - y a d| ≤ (2 * H) / ((J.card : ℝ) - 1) := hyshort
      _ ≤ 2 * M * (2 * H) / (k : ℝ) :=
        heavy_card_rate_le hM hscale hheavy (by positivity)
      _ = 4 * M * H / (k : ℝ) := by ring
  have hlamrate : |lam * (x b d - x a d)| ≤ 2 * M * H / (k : ℝ) := by
    rw [abs_mul, abs_of_nonneg hlam]
    calc
      lam * |x b d - x a d| ≤ lam * (2 * M * Hx / (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hxrate hlam
      _ = 2 * M * (lam * Hx) / (k : ℝ) := by ring
      _ = 2 * M * H / (k : ℝ) := by rw [hlamHx]
  have hdileq : y b d - y a d = lam * (x b d - x a d) := by
    apply dilation_drift_eq (integer_dilation_difference (fun j => hdil j d) a b)
      hyrate hlamrate
    calc
      4 * M * H / (k : ℝ) + 2 * M * H / (k : ℝ) = 6 * M * H / (k : ℝ) := by ring
      _ < 1 := hdriftsmall
  exact ⟨hxshort, hxrate, hyshort, hyrate, hdileq⟩

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Rational paths from a closest return

The representatives are real vectors with explicitly integral errors along an
arithmetic progression. The minimal return to a half-open rectangular box
forces the integral numerator of the return to be primitive. The proof uses
the actual intermediate sample and uniqueness in a fundamental interval.
-/


namespace QuantitativeVanDerWaerden

/-- Two representatives in the same half-open fundamental interval cannot
differ by a nonzero integer. -/
theorem eq_of_integer_difference_in_fundamental_interval {a x y : ℝ}
    (hx : a ≤ x ∧ x < a + 1) (hy : a ≤ y ∧ y < a + 1)
    (hint : ∃ z : ℤ, x - y = z) : x = y := by
  obtain ⟨z, hz⟩ := hint
  have hsmall : |(z : ℝ)| < 1 := by
    rw [← hz, abs_lt]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hzero := integer_zero_of_abs_lt_one hsmall
  rw [hzero, Int.cast_zero] at hz
  exact sub_eq_zero.mp hz

/-- The intermediate point of a segment in a half-open interval remains in
that interval, including its left endpoint. -/
theorem divided_segment_mem_Ico {a b x y e : ℝ}
    (hx : a ≤ x ∧ x < b) (hy : a ≤ y ∧ y < b) (he : 1 ≤ e) :
    a ≤ x + (y - x) / e ∧ x + (y - x) / e < b := by
  have hepos : 0 < e := by linarith
  have hmul : e * ((y - x) / e) = y - x := mul_div_cancel₀ _ hepos.ne'
  have hxmul := mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hx.1)
  have hxmul' := mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hx.2.le)
  constructor
  · nlinarith [hy.1]
  · nlinarith [hy.2]

/-- An actual repeat gives an integral return numerator. -/
theorem exists_integer_return_numerator {ι : Type uIndex}
    (X : ℕ → ι → ℝ) (A b : ι → ℝ) (j h : ℕ)
    (hAP : ∀ n i, ∃ z : ℤ, X n i - A i - (n : ℝ) * b i = z) :
    ∃ T : ι → ℤ, ∀ i, (h : ℝ) * b i - (X (j + h) i - X j i) = T i := by
  classical
  have hi : ∀ i, ∃ z : ℤ,
      (h : ℝ) * b i - (X (j + h) i - X j i) = z := by
    intro i
    obtain ⟨z₀, hz₀⟩ := hAP j i
    obtain ⟨z₁, hz₁⟩ := hAP (j + h) i
    refine ⟨z₀ - z₁, ?_⟩
    push_cast at hz₁ ⊢
    nlinarith
  choose T hT using hi
  exact ⟨T, hT⟩

/-- Reducing a return numerator modulo its positive denominator gives the
finite rational label and a coordinatewise integer change of the step. -/
theorem reduced_return_numerator {ι : Type uIndex} {h : ℕ} (hh : 0 < h)
    (T : ι → ℤ) (b u : ι → ℝ)
    (hT : ∀ i, (h : ℝ) * b i - u i = T i) :
    ∃ t : ι → ℤ, (∀ i, 0 ≤ t i ∧ t i < h) ∧
      (∀ i, ∃ z : ℤ, T i - t i = (h : ℤ) * z) ∧
      (∀ i, ∃ z : ℤ, b i - ((t i : ℝ) + u i) / h = z) := by
  refine ⟨fun i => T i % (h : ℤ), ?_, ?_, ?_⟩
  · intro i
    exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  · intro i
    exact ⟨T i / (h : ℤ), by linarith [Int.emod_add_mul_ediv (T i) (h : ℤ)]⟩
  · intro i
    refine ⟨T i / (h : ℤ), ?_⟩
    have hid : T i - T i % (h : ℤ) = (h : ℤ) * (T i / (h : ℤ)) := by
      linarith [Int.emod_add_mul_ediv (T i) (h : ℤ)]
    have hr : (T i : ℝ) - (T i % (h : ℤ) : ℤ) =
        (h : ℝ) * (T i / (h : ℤ) : ℤ) := by exact_mod_cast hid
    have hhR : (h : ℝ) ≠ 0 := by positivity
    have hquot : ((T i % (h : ℤ) : ℤ) + u i : ℝ) / h =
        b i - (T i / (h : ℤ) : ℤ) := by
      apply (div_eq_iff hhR).2
      nlinarith [hT i]
    rw [hquot]
    ring

/-- The rational step representation gives the full path modulo integers. -/
theorem rational_path_congr {ι : Type uIndex} {h : ℕ}
    (X : ℕ → ι → ℝ) (A b u : ι → ℝ) (t : ι → ℤ)
    (hAP : ∀ n i, ∃ z : ℤ, X n i - A i - (n : ℝ) * b i = z)
    (hstep : ∀ i, ∃ z : ℤ, b i - ((t i : ℝ) + u i) / h = z)
    (j : ℕ) (i : ι) :
    ∃ z : ℤ, X j i - A i - (j : ℝ) / h * ((t i : ℝ) + u i) = z := by
  obtain ⟨z₁, hz₁⟩ := hAP j i
  obtain ⟨z₂, hz₂⟩ := hstep i
  refine ⟨z₁ + j * z₂, ?_⟩
  calc
    _ = (X j i - A i - (j : ℝ) * b i) +
        (j : ℝ) * (b i - ((t i : ℝ) + u i) / h) := by ring
    _ = _ := by rw [hz₁, hz₂]; push_cast; ring

/-- A common divisor produces a genuine earlier return to the same box.
The hypotheses are the explicit arithmetic-progression errors and the
coordinate intervals; no intermediate return is assumed. -/
theorem divided_return_mem_box {ι : Type uIndex}
    (X : ℕ → ι → ℝ) (A b f lo hi : ι → ℝ) (T : ι → ℤ)
    {j h e l k : ℕ} (he : 1 ≤ e) (hfactor : h = e * l)
    (hend : j + h < k)
    (hAP : ∀ n i, ∃ z : ℤ, X n i - A i - (n : ℝ) * b i = z)
    (hfund : ∀ n, n < k → ∀ i, f i ≤ X n i ∧ X n i < f i + 1)
    (hleft : ∀ i, lo i ≤ X j i ∧ X j i < hi i)
    (hright : ∀ i, lo i ≤ X (j + h) i ∧ X (j + h) i < hi i)
    (hT : ∀ i, (h : ℝ) * b i - (X (j + h) i - X j i) = T i)
    (hdiv : ∀ i, (e : ℤ) ∣ T i) :
    ∀ i, lo i ≤ X (j + l) i ∧ X (j + l) i < hi i := by
  have hel : l ≤ h := by nlinarith
  have hej : j < k := by omega
  have hen : j + l < k := by omega
  have heR : 1 ≤ (e : ℝ) := by exact_mod_cast he
  have hepos : 0 < (e : ℝ) := by linarith
  intro i
  let u := X (j + h) i - X j i
  let C := X j i + u / e
  have hCbox : lo i ≤ C ∧ C < hi i :=
    divided_segment_mem_Ico (hleft i) (hright i) heR
  have hCfund : f i ≤ C ∧ C < f i + 1 :=
    divided_segment_mem_Ico (hfund j hej i) (hfund (j + h) hend i) heR
  obtain ⟨s, hs⟩ := hdiv i
  have hfactorR : (h : ℝ) = (e : ℝ) * l := by exact_mod_cast hfactor
  have hsR : (T i : ℝ) = (e : ℝ) * s := by exact_mod_cast hs
  have hquot : u / (e : ℝ) = (l : ℝ) * b i - s := by
    apply (div_eq_iff hepos.ne').2
    dsimp [u]
    have hTi := hT i
    rw [hfactorR, hsR] at hTi
    nlinarith [hTi]
  obtain ⟨z₀, hz₀⟩ := hAP j i
  obtain ⟨z₁, hz₁⟩ := hAP (j + l) i
  have hcongr : ∃ z : ℤ, X (j + l) i - C = z := by
    refine ⟨z₁ - z₀ + s, ?_⟩
    dsimp only [C]
    rw [hquot]
    push_cast at hz₁ ⊢
    nlinarith
  have heq := eq_of_integer_difference_in_fundamental_interval
    (hfund (j + l) hen i) hCfund hcongr
  rwa [heq]

/-- Minimality of the positive return prohibits every common divisor greater
than one of its integral numerator and its denominator. -/
theorem primitive_of_minimal_box_return {ι : Type uIndex}
    (X : ℕ → ι → ℝ) (A b f lo hi : ι → ℝ) (T : ι → ℤ)
    {j h k : ℕ} (hh : 0 < h) (hend : j + h < k)
    (hAP : ∀ n i, ∃ z : ℤ, X n i - A i - (n : ℝ) * b i = z)
    (hfund : ∀ n, n < k → ∀ i, f i ≤ X n i ∧ X n i < f i + 1)
    (hleft : ∀ i, lo i ≤ X j i ∧ X j i < hi i)
    (hright : ∀ i, lo i ≤ X (j + h) i ∧ X (j + h) i < hi i)
    (hT : ∀ i, (h : ℝ) * b i - (X (j + h) i - X j i) = T i)
    (hmin : ∀ l, 0 < l → l < h →
      ¬ ∀ i, lo i ≤ X (j + l) i ∧ X (j + l) i < hi i) :
    ∀ e : ℕ, e ∣ h → (∀ i, (e : ℤ) ∣ T i) → e ≤ 1 := by
  intro e he hdiv
  by_contra hlarge
  have hegt : 1 < e := by omega
  obtain ⟨l, hfactor⟩ := he
  have hl : 0 < l := by nlinarith
  have hlh : l < h := by nlinarith
  exact hmin l hl hlh (divided_return_mem_box X A b f lo hi T hegt.le
    hfactor hend hAP hfund hleft hright hT hdiv)

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Primitive rational vectors

A denominator and an integer coordinate vector are primitive if they have no
common natural divisor greater than one. Multiplying such a vector by an integer
not divisible by its denominator leaves a nonintegral coordinate. Every such
coordinate stays at least the reciprocal denominator from every integer.
-/


namespace QuantitativeVanDerWaerden

/-- The denominator and all coordinates have no nontrivial common divisor. -/
def PrimitiveVector {ι : Type uIndex} (h : ℕ) (t : ι → ℤ) : Prop :=
  ∀ e : ℕ, e ∣ h → (∀ i, (e : ℤ) ∣ t i) → e ≤ 1

/-- Changing coordinates by multiples of the denominator preserves primitivity. -/
theorem PrimitiveVector.of_congr {ι : Type uIndex} {h : ℕ} {T t : ι → ℤ}
    (hp : PrimitiveVector h T)
    (hcongr : ∀ i, ∃ z : ℤ, T i - t i = (h : ℤ) * z) :
    PrimitiveVector h t := by
  intro e he ht
  apply hp e he
  intro i
  obtain ⟨z, hz⟩ := hcongr i
  have heZ : (e : ℤ) ∣ (h : ℤ) := Int.natCast_dvd_natCast.mpr he
  have hdiff : (e : ℤ) ∣ T i - t i := by
    rw [hz]
    exact dvd_mul_of_dvd_left heZ z
  simpa only [sub_add_cancel] using dvd_add hdiff (ht i)

/-- Coordinates congruent to a common integer multiple of the first vector
do not add a new obstruction to its primitivity. -/
theorem PrimitiveVector.of_sum_congr_mul {ι : Type uIndex} {h : ℕ} {T S : ι → ℤ}
    (hp : PrimitiveVector h (Sum.elim T S)) (a : ℤ)
    (hcongr : ∀ i, ∃ z : ℤ, S i = a * T i + (h : ℤ) * z) :
    PrimitiveVector h T := by
  intro e he ht
  apply hp e he
  intro i
  cases i with
  | inl i => exact ht i
  | inr i =>
    obtain ⟨z, hz⟩ := hcongr i
    change (e : ℤ) ∣ S i
    rw [hz]
    exact dvd_add (dvd_mul_of_dvd_right (ht i) a)
      (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr he) z)

/-- Primitivity forces some multiplied coordinate to remain nonintegral. -/
theorem PrimitiveVector.exists_not_dvd_mul {ι : Type uIndex} [Fintype ι]
    {h : ℕ} {t : ι → ℤ} (hp : PrimitiveVector h t) (hh : 0 < h)
    {a : ℤ} (ha : ¬ (h : ℤ) ∣ a) : ∃ i, ¬ (h : ℤ) ∣ a * t i := by
  classical
  by_contra hnone
  have hall : ∀ i, (h : ℤ) ∣ a * t i := by simpa using hnone
  let g : ℕ := Finset.univ.gcd fun i => (t i).natAbs
  have hgle : Nat.gcd h g ≤ 1 := hp _ (Nat.gcd_dvd_left _ _) (by
    intro i
    exact Int.natCast_dvd.mpr ((Nat.gcd_dvd_right h g).trans
      (Finset.gcd_dvd (Finset.mem_univ i))))
  have hgpos : 0 < Nat.gcd h g := Nat.gcd_pos_of_pos_left g hh
  have hcop : Nat.Coprime h g := Nat.le_antisymm hgle hgpos
  have hmul : h ∣ a.natAbs * g := by
    have hg : h ∣ Finset.univ.gcd (fun i => a.natAbs * (t i).natAbs) := by
      apply Finset.dvd_gcd
      intro i _
      simpa only [Int.natAbs_mul] using (Int.natCast_dvd.mp (hall i))
    simpa only [Finset.gcd_mul_left, normalize_eq] using hg
  exact ha (Int.natCast_dvd.mpr (hcop.dvd_of_dvd_mul_right hmul))

/-- A nonintegral rational with denominator `h` is separated from every integer. -/
theorem rational_separation {h : ℕ} (hh : 0 < h) {b : ℤ}
    (hb : ¬ (h : ℤ) ∣ b) (z : ℤ) :
    1 / (h : ℝ) ≤ |(b : ℝ) / (h : ℝ) - (z : ℝ)| := by
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hn : b - (h : ℤ) * z ≠ 0 := by
    intro he
    exact hb ⟨z, sub_eq_zero.mp he⟩
  have habs : (1 : ℝ) ≤ |(b : ℝ) - (h : ℝ) * (z : ℝ)| := by
    simpa only [Int.cast_one, Int.cast_abs, Int.cast_sub,
      Int.cast_mul, Int.cast_natCast] using
      (Int.cast_mono (R := ℝ) (Int.one_le_abs hn))
  rw [div_sub' hhR.ne', abs_div, abs_of_pos hhR]
  exact div_le_div_of_nonneg_right habs hhR.le

/-- A primitive vector has a coordinate separated from every integer translate. -/
theorem PrimitiveVector.exists_separated_coordinate {ι : Type uIndex} [Fintype ι]
    {h : ℕ} {t : ι → ℤ} (hp : PrimitiveVector h t) (hh : 0 < h)
    {a : ℤ} (ha : ¬ (h : ℤ) ∣ a) :
    ∃ i, ∀ z : ℤ, 1 / (h : ℝ) ≤ |(a : ℝ) * (t i : ℝ) / h - z| := by
  obtain ⟨i, hi⟩ := hp.exists_not_dvd_mul hh ha
  refine ⟨i, fun z => ?_⟩
  simpa only [Int.cast_mul] using rational_separation hh hi z

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Primitive rational paths for the cyclic representatives

A closest positive return to a rectangle in the two representative systems
gives a primitive integer return vector. When the two displacements satisfy
the dilation relation, the first numerator is already primitive. Reducing it
modulo the return time gives the finite rational label and the two full paths.
-/

namespace QuantitativeVanDerWaerden

/-- An actual minimal rectangle return with matching dilated displacement
produces a primitive rational label for both cyclic representative paths. -/
theorem cyclic_primitive_return_path {q D dilation j h k : ℕ} (hq : 0 < q)
    (a d : CyclicGroup q D) (xlo xhi ylo yhi u : Fin D → ℝ)
    (hh : 0 < h) (hend : j + h < k)
    (hxleft : ∀ i, xlo i ≤ xRep q D (a + j • d) i ∧
      xRep q D (a + j • d) i < xhi i)
    (hyleft : ∀ i, ylo i ≤ yRep q D dilation (a + j • d) i ∧
      yRep q D dilation (a + j • d) i < yhi i)
    (hxright : ∀ i, xlo i ≤ xRep q D (a + (j + h) • d) i ∧
      xRep q D (a + (j + h) • d) i < xhi i)
    (hyright : ∀ i, ylo i ≤ yRep q D dilation (a + (j + h) • d) i ∧
      yRep q D dilation (a + (j + h) • d) i < yhi i)
    (hmin : ∀ l, 0 < l → l < h →
      ¬ ((∀ i, xlo i ≤ xRep q D (a + (j + l) • d) i ∧
        xRep q D (a + (j + l) • d) i < xhi i) ∧
        (∀ i, ylo i ≤ yRep q D dilation (a + (j + l) • d) i ∧
        yRep q D dilation (a + (j + l) • d) i < yhi i)))
    (hu : ∀ i, xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i = u i)
    (hv : ∀ i, yRep q D dilation (a + (j + h) • d) i -
      yRep q D dilation (a + j • d) i = (dilation : ℝ) * u i) :
    ∃ t : Fin D → ℤ, (∀ i, 0 ≤ t i ∧ t i < h) ∧ PrimitiveVector h t ∧
      (∀ (n : ℕ) (i : Fin D), ∃ z : ℤ, xRep q D (a + n • d) i - xRep q D a i -
        (n : ℝ) / h * ((t i : ℝ) + u i) = z) ∧
      (∀ (n : ℕ) (i : Fin D), ∃ z : ℤ, yRep q D dilation (a + n • d) i - yRep q D dilation a i -
        (n : ℝ) / h * ((dilation : ℝ) * ((t i : ℝ) + u i)) = z) := by
  let X : ℕ → Fin D → ℝ := fun n => xRep q D (a + n • d)
  let Y : ℕ → Fin D → ℝ := fun n => yRep q D dilation (a + n • d)
  have hXAP : ∀ n i, ∃ z : ℤ, X n i - xRep q D a i -
      (n : ℝ) * xRep q D d i = z := fun n i => xRep_ap_congr hq a d n i
  have hYAP : ∀ n i, ∃ z : ℤ, Y n i - yRep q D dilation a i -
      (n : ℝ) * yRep q D dilation d i = z :=
    fun n i => yRep_ap_congr hq dilation a d n i
  obtain ⟨T, hT⟩ := exists_integer_return_numerator X (xRep q D a) (xRep q D d)
    j h hXAP
  obtain ⟨S, hS⟩ := exists_integer_return_numerator Y (yRep q D dilation a)
    (yRep q D dilation d) j h hYAP
  have hp : PrimitiveVector h (Sum.elim T S) := by
    apply primitive_of_minimal_box_return
      (fun n => Sum.elim (X n) (Y n))
      (Sum.elim (xRep q D a) (yRep q D dilation a))
      (Sum.elim (xRep q D d) (yRep q D dilation d))
      (Sum.elim (fun _ => 0) (fun _ => -(1 / 2 : ℝ)))
      (Sum.elim xlo ylo) (Sum.elim xhi yhi) (Sum.elim T S) hh hend
    · intro n i
      cases i with
      | inl i => exact hXAP n i
      | inr i => exact hYAP n i
    · intro n _ i
      cases i with
      | inl i => simpa only [Sum.elim_inl, zero_add] using xRep_mem q D (a + n • d) i
      | inr i =>
        change -(1 / 2 : ℝ) ≤ yRep q D dilation (a + n • d) i ∧
          yRep q D dilation (a + n • d) i < -(1 / 2 : ℝ) + 1
        constructor
        · exact (yRep_mem q D dilation (a + n • d) i).1
        · linarith [(yRep_mem q D dilation (a + n • d) i).2]
    · intro i
      cases i with
      | inl i => exact hxleft i
      | inr i => exact hyleft i
    · intro i
      cases i with
      | inl i => exact hxright i
      | inr i => exact hyright i
    · intro i
      cases i with
      | inl i => exact hT i
      | inr i => exact hS i
    · intro l hl hlh hmem
      apply hmin l hl hlh
      exact ⟨fun i => hmem (Sum.inl i), fun i => hmem (Sum.inr i)⟩
  have hTu : ∀ i, (h : ℝ) * xRep q D d i - u i = T i := by
    intro i
    simpa only [X, hu i] using hT i
  have hSv : ∀ i, (h : ℝ) * yRep q D dilation d i - (dilation : ℝ) * u i = S i := by
    intro i
    simpa only [Y, hv i] using hS i
  have hcongr : ∀ i, ∃ z : ℤ, S i = (dilation : ℤ) * T i + (h : ℤ) * z := by
    intro i
    obtain ⟨z, hz⟩ := yRep_dilation_congr hq dilation d i
    refine ⟨z, ?_⟩
    have hr : (S i : ℝ) = (dilation : ℝ) * (T i : ℝ) + (h : ℝ) * z := by
      calc
        _ = (h : ℝ) * yRep q D dilation d i - (dilation : ℝ) * u i := (hSv i).symm
        _ = (dilation : ℝ) * ((h : ℝ) * xRep q D d i - u i) +
            (h : ℝ) * (yRep q D dilation d i - (dilation : ℝ) * xRep q D d i) := by ring
        _ = _ := by rw [hTu i, hz]
    exact_mod_cast hr
  have hpT : PrimitiveVector h T := hp.of_sum_congr_mul (dilation : ℤ) hcongr
  obtain ⟨t, htrange, htcongr, htstep⟩ := reduced_return_numerator hh T (xRep q D d) u hTu
  refine ⟨t, htrange, hpT.of_congr htcongr, ?_, ?_⟩
  · exact rational_path_congr X (xRep q D a) (xRep q D d) u t hXAP htstep
  · intro n i
    obtain ⟨z₀, hz₀⟩ := hYAP n i
    obtain ⟨z₁, hz₁⟩ := yRep_dilation_congr hq dilation d i
    obtain ⟨z₂, hz₂⟩ := htstep i
    refine ⟨z₀ + (n : ℤ) * (z₁ + (dilation : ℤ) * z₂), ?_⟩
    calc
      _ = (Y n i - yRep q D dilation a i - (n : ℝ) * yRep q D dilation d i) +
          (n : ℝ) * ((yRep q D dilation d i - (dilation : ℝ) * xRep q D d i) +
            (dilation : ℝ) * (xRep q D d i - ((t i : ℝ) + u i) / h)) := by dsimp [Y]; ring
      _ = _ := by rw [hz₀, hz₁, hz₂]; push_cast; ring

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Closest returns to actual full labels

The occurrence set is the literal full-label fiber in an actual cyclic
progression. The box widths, arithmetic-progression congruences and dilation
congruence are discharged using the concrete mesh and representative APIs.
-/

noncomputable section

namespace QuantitativeVanDerWaerden

def fullLabelFiber (mesh : AdaptiveMesh) (q D lam Ucount : ℕ)
    (hU : 0 < Ucount) (k : ℕ) (a d : CyclicGroup q D)
    (beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)) : Finset ℕ :=
  labelFiber k (fun j => literalFullLabel mesh q D lam Ucount hU (a + j • d)) beta

@[simp] theorem mem_fullLabelFiber {mesh : AdaptiveMesh} {q D lam Ucount k j : ℕ}
    {hU : 0 < Ucount} {a d : CyclicGroup q D}
    {beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)} :
    j ∈ fullLabelFiber mesh q D lam Ucount hU k a d beta ↔
      j < k ∧ literalFullLabel mesh q D lam Ucount hU (a + j • d) = beta :=
  mem_labelFiber

structure IsHeavyLabelReturn (mesh : AdaptiveMesh) (q D lam Ucount k M : ℕ)
    (hU : 0 < Ucount) (a d : CyclicGroup q D)
    (beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)) (j h : ℕ) : Prop where
  start_lt : j < k
  end_lt : j + h < k
  gap_pos : 0 < h
  gap_le : h ≤ 2 * M
  start_label : literalFullLabel mesh q D lam Ucount hU (a + j • d) = beta
  end_label : literalFullLabel mesh q D lam Ucount hU (a + (j + h) • d) = beta
  minimum : ∀ s ∈ fullLabelFiber mesh q D lam Ucount hU k a d beta,
    ∀ t ∈ fullLabelFiber mesh q D lam Ucount hU k a d beta, s < t → h ≤ t - s
  no_earlier : ∀ t, 0 < t → t < h →
    literalFullLabel mesh q D lam Ucount hU (a + (j + t) • d) ≠ beta
  x_card : ∀ i, |xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i| ≤
    (1 / (Ucount : ℝ)) /
      ((fullLabelFiber mesh q D lam Ucount hU k a d beta).card - 1 : ℝ)
  x_rate : ∀ i, |xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i| ≤
    2 * (M : ℝ) * (1 / (Ucount : ℝ)) / (k : ℝ)
  y_card : ∀ i, |yRep q D lam (a + (j + h) • d) i - yRep q D lam (a + j • d) i| ≤
    (2 * mesh.H) /
      ((fullLabelFiber mesh q D lam Ucount hU k a d beta).card - 1 : ℝ)
  y_rate : ∀ i, |yRep q D lam (a + (j + h) • d) i - yRep q D lam (a + j • d) i| ≤
    4 * (M : ℝ) * mesh.H / (k : ℝ)
  dilation_eq : ∀ i,
    yRep q D lam (a + (j + h) • d) i - yRep q D lam (a + j • d) i =
      (lam : ℝ) * (xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i)

/-- A heavy actual full-label fiber has an attained closest return with the
claimed real displacement bounds. No representative or label geometry is
assumed: only the displayed scalar parameter inequalities remain as inputs. -/
theorem exists_heavy_label_return (mesh : AdaptiveMesh) {q D lam Ucount k M : ℕ}
    (hq : 0 < q) (hU : 0 < Ucount) (hM : 0 < M) (hscale : 2 * M ≤ k)
    (a d : CyclicGroup q D)
    (beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label))
    (hheavy : k < M * (fullLabelFiber mesh q D lam Ucount hU k a d beta).card)
    (hwidth : 1 / (Ucount : ℝ) ≤ 2 * mesh.H)
    (hdilation : (lam : ℝ) * (1 / (Ucount : ℝ)) = mesh.H)
    (hsmall : 2 * (k : ℝ) * mesh.H < 1)
    (hdriftsmall : 6 * (M : ℝ) * mesh.H / (k : ℝ) < 1) :
    ∃ j h, IsHeavyLabelReturn mesh q D lam Ucount k M hU a d beta j h := by
  let J := fullLabelFiber mesh q D lam Ucount hU k a d beta
  have hJ : ∀ j ∈ J, j < k := fun _ hj => (mem_fullLabelFiber.mp hj).1
  have hlabels : ∀ j ∈ J, literalFullLabel mesh q D lam Ucount hU (a + j • d) = beta :=
    fun _ hj => (mem_fullLabelFiber.mp hj).2
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hscaleR : 2 * (M : ℝ) ≤ k := by exact_mod_cast hscale
  have hheavyR : (k : ℝ) / M < J.card := by
    apply (div_lt_iff₀ hMR).2
    have hh : (k : ℝ) < (M : ℝ) * (J.card : ℝ) := by exact_mod_cast hheavy
    simpa only [mul_comm] using hh
  have hxbox : ∀ i ∈ J, ∀ j ∈ J, ∀ e,
      |xRep q D (a + j • d) e - xRep q D (a + i • d) e| ≤ 1 / (Ucount : ℝ) := by
    intro i hi j hj e
    exact literalFullLabel_same_first_distance mesh q D lam Ucount hU
      ((hlabels j hj).trans (hlabels i hi).symm) e
  have hybox : ∀ i ∈ J, ∀ j ∈ J, ∀ e,
      |yRep q D lam (a + j • d) e - yRep q D lam (a + i • d) e| ≤ 2 * mesh.H := by
    intro i hi j hj e
    exact literalFullLabel_same_second_distance mesh q D lam Ucount hU
      ((hlabels j hj).trans (hlabels i hi).symm) e
  obtain ⟨j, h, hj, hjh, hh, hend, hmin, _, hgap, hcoord⟩ :=
    exists_closest_return_drift hJ hMR hscaleR hheavyR mesh.H_pos.le
      (by positivity : (0 : ℝ) ≤ 1 / (Ucount : ℝ)) hwidth hsmall hxbox hybox
      (fun n i => xRep_ap_congr hq a d n i)
      (fun n i => yRep_ap_congr hq lam a d n i)
      (Nat.cast_nonneg lam) hdilation
      (fun n i => yRep_dilation_congr hq lam (a + n • d) i) hdriftsmall
  refine ⟨j, h, ?_⟩
  refine {
    start_lt := hJ j hj
    end_lt := hend
    gap_pos := hh
    gap_le := by exact_mod_cast hgap
    start_label := hlabels j hj
    end_label := hlabels (j + h) hjh
    minimum := hmin
    no_earlier := no_earlier_label_return hj hend hmin
    x_card := fun i => (hcoord i).1
    x_rate := fun i => (hcoord i).2.1
    y_card := fun i => (hcoord i).2.2.1
    y_rate := fun i => (hcoord i).2.2.2.1
    dilation_eq := fun i => (hcoord i).2.2.2.2 }

namespace IsHeavyLabelReturn

variable {mesh : AdaptiveMesh} {q D lam Ucount k M j h : ℕ} {hU : 0 < Ucount}
  {a d : CyclicGroup q D} {beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)}
  (R : IsHeavyLabelReturn mesh q D lam Ucount k M hU a d beta j h)

include R

theorem start_rectangle :
    (∀ i, UniformMesh.Contains Ucount (beta.1 i) (xRep q D (a + j • d) i)) ∧
    (∀ i, mesh.Contains (beta.2 i) (yRep q D lam (a + j • d) i)) :=
  (literalFullLabel_eq_iff mesh q D lam Ucount hU _ beta).mp R.start_label

theorem end_rectangle :
    (∀ i, UniformMesh.Contains Ucount (beta.1 i) (xRep q D (a + (j + h) • d) i)) ∧
    (∀ i, mesh.Contains (beta.2 i) (yRep q D lam (a + (j + h) • d) i)) :=
  (literalFullLabel_eq_iff mesh q D lam Ucount hU _ beta).mp R.end_label

theorem no_earlier_rectangle (t : ℕ) (ht : 0 < t) (hth : t < h) :
    ¬ ((∀ i, UniformMesh.Contains Ucount (beta.1 i) (xRep q D (a + (j + t) • d) i)) ∧
      (∀ i, mesh.Contains (beta.2 i) (yRep q D lam (a + (j + t) • d) i))) := by
  intro hrect
  exact R.no_earlier t ht hth
    ((literalFullLabel_eq_iff mesh q D lam Ucount hU _ beta).mpr hrect)

/-- The primitive rational path now follows for this actual heavy label,
using the actual first-coordinate displacement as the drift vector. -/
theorem primitive_return_path (hq : 0 < q) :
    ∃ t : Fin D → ℤ, (∀ i, 0 ≤ t i ∧ t i < h) ∧ PrimitiveVector h t ∧
      (∀ (n : ℕ) (i : Fin D), ∃ z : ℤ,
        xRep q D (a + n • d) i - xRep q D a i - (n : ℝ) / h *
          ((t i : ℝ) + (xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i)) = z) ∧
      (∀ (n : ℕ) (i : Fin D), ∃ z : ℤ,
        yRep q D lam (a + n • d) i - yRep q D lam a i - (n : ℝ) / h *
          ((lam : ℝ) * ((t i : ℝ) +
            (xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i))) = z) := by
  exact cyclic_primitive_return_path hq a d
    (fun i => UniformMesh.left Ucount (beta.1 i))
    (fun i => UniformMesh.right Ucount (beta.1 i))
    (fun i => mesh.left (beta.2 i)) (fun i => mesh.right (beta.2 i))
    (fun i => xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i)
    R.gap_pos R.end_lt R.start_rectangle.1 R.start_rectangle.2
    R.end_rectangle.1 R.end_rectangle.2 R.no_earlier_rectangle (fun _ => rfl) R.dilation_eq

end IsHeavyLabelReturn

end QuantitativeVanDerWaerden

end

end OAI
end
end

section
section
namespace OAI

/-!
# Heavy returns at the selected construction parameters

The occurrence set and multiplicity here use the actual full-label word. The
geometric parameter inequalities are supplied by the independently proved
eventual `GeometryScales` statement.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

variable {k : ℕ}

def labelOccurrences (s : Data k) (hk : 3 ≤ k) (a d : Group s)
    (beta : Label s hk) : Finset ℕ :=
  labelFiber k (fun j => fullLabel s hk (a + j • d)) beta

@[simp] theorem mem_labelOccurrences {s : Data k} {hk : 3 ≤ k} {a d : Group s}
    {beta : Label s hk} {j : ℕ} :
    j ∈ labelOccurrences s hk a d beta ↔ j < k ∧ fullLabel s hk (a + j • d) = beta :=
  mem_labelFiber

open scoped Classical in
/-- The natural occurrence set has exactly the ordinary word multiplicity. -/
theorem card_labelOccurrences (s : Data k) (hk : 3 ≤ k) (a d : Group s)
    (beta : Label s hk) :
    (labelOccurrences s hk a d beta).card =
      (Finset.univ.filter (fun j : Fin k => fullLabelWord s hk (a, d) j = beta)).card := by
  unfold labelOccurrences
  refine (card_labelFiber k (fun j => fullLabel s hk (a + j • d)) beta).trans ?_
  apply congrArg (Finset.card : Finset (Fin k) → ℕ)
  apply Finset.ext
  intro j
  constructor
  · intro hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [fullLabelWord, nsmul_eq_mul] using
      ((@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).mp hi).2
  · intro hi
    apply (@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [fullLabelWord, nsmul_eq_mul] using (Finset.mem_filter.mp hi).2

theorem uniformWidth_le_two_mesh_H (s : Data k) (hk : 3 ≤ k) :
    1 / (uniformCount k : ℝ) ≤ 2 * (mesh s hk).H := by
  rw [uniformWidth_eq, mesh_H]
  have hl : (0 : ℝ) < lambda k := by exact_mod_cast lambda_pos k
  have hl1 : (1 : ℝ) ≤ lambda k := by exact_mod_cast Nat.succ_le_of_lt (lambda_pos k)
  have hH : 0 ≤ meshScale k := (meshScale_pos (by omega : 0 < k)).le
  have hd : meshScale k / (lambda k : ℝ) ≤ meshScale k :=
    (div_le_iff₀ hl).2 (by nlinarith)
  linarith

theorem dilation_uniformWidth (s : Data k) (hk : 3 ≤ k) :
    (lambda k : ℝ) * (1 / (uniformCount k : ℝ)) = (mesh s hk).H := by
  rw [uniformWidth_eq, mesh_H]
  have hl : (lambda k : ℝ) ≠ 0 := by exact_mod_cast lambda_ne_zero k
  field_simp [hl]

/-- A heavy label in the selected construction has the proved actual return.
All scalar return inequalities are instantiated from `GeometryScales`. -/
theorem exists_selected_heavy_label_return (s : Data k) (hk : 3 ≤ k)
    (hg : GeometryScales k) (a d : Group s) (beta : Label s hk)
    (hheavy : k < cutoff k * (labelOccurrences s hk a d beta).card) :
    ∃ j h, IsHeavyLabelReturn (mesh s hk) s.q (dimension k) (lambda k)
      (uniformCount k) k (cutoff k) (uniformCount_pos hk) a d beta j h := by
  have hM : 0 < cutoff k := cutoff_pos (by omega)
  have hscale : 2 * cutoff k ≤ k := by exact_mod_cast hg.two_cutoff_le_length
  apply exists_heavy_label_return (mesh s hk) s.pos (uniformCount_pos hk)
    hM hscale a d beta
  · exact hheavy
  · exact uniformWidth_le_two_mesh_H s hk
  · exact dilation_uniformWidth s hk
  · exact hg.affine_box
  · exact hg.return_error

open scoped Classical in
/-- The same endpoint with heaviness stated as the full-label word's literal
`Fin k` multiplicity, matching the outer-coloring family. -/
theorem exists_selected_heavy_label_return_of_word (s : Data k) (hk : 3 ≤ k)
    (hg : GeometryScales k) (a d : Group s) (beta : Label s hk)
    (hheavy : k < cutoff k *
      (Finset.univ.filter (fun j : Fin k => fullLabelWord s hk (a, d) j = beta)).card) :
    ∃ j h, IsHeavyLabelReturn (mesh s hk) s.q (dimension k) (lambda k)
      (uniformCount k) k (cutoff k) (uniformCount_pos hk) a d beta j h := by
  apply exists_selected_heavy_label_return s hk hg a d beta
  simpa only [card_labelOccurrences] using hheavy

end QuantitativeVanDerWaerden.ConstructionModel

end

end OAI
end
end

section
section
namespace OAI

/-!
# Elementary bounds for the actual coordinate cells

These inequalities follow from the selected mesh and dilation definitions.
They are not extra hypotheses on the finite geometric construction.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

variable {k : ℕ}

theorem uniformWidth_le_meshH (s : Data k) (hk : 3 ≤ k) :
    1 / (uniformCount k : ℝ) ≤ (mesh s hk).H := by
  rw [uniformWidth_eq, mesh_H]
  exact div_le_self (meshScale_pos (by omega : 0 < k)).le
    (by exact_mod_cast lambda_pos k)

theorem lambda_mul_uniformWidth (s : Data k) (hk : 3 ≤ k) :
    (lambda k : ℝ) * (1 / (uniformCount k : ℝ)) = (mesh s hk).H := by
  rw [uniformWidth_eq, mesh_H]
  have hl : (lambda k : ℝ) ≠ 0 := by exact_mod_cast lambda_ne_zero k
  exact mul_div_cancel₀ _ hl

theorem mesh_alpha_le (s : Data k) (hk : 3 ≤ k) :
    (mesh s hk).alpha ≤ 1 / (s.q : ℝ) ^ dimension k := by
  rw [mesh_alpha]
  have hq : (1 : ℝ) ≤ s.q := by exact_mod_cast (show 1 ≤ s.q by have := s.two_le; omega)
  exact one_div_le_one_div_of_le (pow_pos (by exact_mod_cast s.pos) _)
    (pow_le_pow_right₀ hq (Nat.le_succ _))

end QuantitativeVanDerWaerden.ConstructionModel

end

end OAI
end
end

section
section
namespace OAI

/-!
# Denominators after the construction's dilation

The actual dilation contains every primary part of a period of size at most
twice the cutoff whose prime is at most the square of the dimension. Thus a
reduced denominator is either one or exceeds the square of the dimension.
-/

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

/-- The actual dilation kills every period up to the dimension squared. -/
theorem short_period_dvd_lambda {k h : ℕ} (hh : 0 < h)
    (hmax : h ≤ 2 * cutoff k) (hshort : h ≤ dimension k ^ 2) :
    h ∣ lambda k :=
  short_period_dvd_dilation hh hshort hmax

/-- A nonintegral dilated fraction has denominator larger than the dimension
squared. This applies to every natural numerator, including zero. -/
theorem reducedDenominator_gt_of_not_dvd {k h t : ℕ} (hh : 0 < h)
    (hmax : h ≤ 2 * cutoff k) (hnot : ¬ h ∣ lambda k * t) :
    dimension k ^ 2 < h / Nat.gcd h (lambda k * t) := by
  have hparts : ∀ p : ℕ, p.Prime → p ≤ dimension k ^ 2 →
      p ^ h.factorization p ∣ lambda k := by
    intro p hp hp0
    exact primary_part_dvd_dilation hp hp0 hh hmax
  rcases reducedDenominator_eq_one_or_gt_of_primary_parts (t := t) hh hparts with
    hone | hlarge
  · have he : h = Nat.gcd h (lambda k * t) := by
      calc
        h = (h / Nat.gcd h (lambda k * t)) * Nat.gcd h (lambda k * t) :=
          (Nat.div_mul_cancel (Nat.gcd_dvd_left h (lambda k * t))).symm
        _ = Nat.gcd h (lambda k * t) := by rw [hone, one_mul]
    exact (hnot (he.symm ▸ Nat.gcd_dvd_right h (lambda k * t))).elim
  · exact hlarge

end QuantitativeVanDerWaerden.ConstructionModel

end OAI
end
end

section
section
namespace OAI

/-!
# Actual scale consequences for the geometric dichotomy

These bounds use the numerical `GeometryScales` inequalities and the literal
construction mesh. No geometric conclusion is supplied as a hypothesis.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

variable {k : ℕ}

theorem geometry_dimension_ge_three (g : GeometryScales k) : 3 ≤ dimension k := by
  by_contra h
  have hd : dimension k ≤ 2 := by omega
  have hd' : (dimension k : ℝ) ≤ 2 := by exact_mod_cast hd
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (dimension k)) hd' 2
  have hg := g.local_event_size
  norm_num at hs
  nlinarith

theorem geometry_cutoff_pos (hk : 3 ≤ k) : 0 < cutoff k :=
  cutoff_pos (by omega)

theorem geometry_two_cutoff_le_length (g : GeometryScales k) : 2 * cutoff k ≤ k := by
  exact_mod_cast g.two_cutoff_le_length

/-- The rational-return velocity is no larger than the second mesh width. -/
theorem velocity_le_mesh (s : Data k) (hk : 3 ≤ k) (g : GeometryScales k)
    {v : ℝ} (hv : |v| ≤ 4 * cutoff k * (mesh s hk).H / k) :
    |v| ≤ (mesh s hk).H := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hH : 0 ≤ (mesh s hk).H := by
    rw [mesh_H]
    exact (meshScale_pos (show 0 < k by omega)).le
  have hm : 4 * (cutoff k : ℝ) ≤ k := by
    have := g.heavy_return
    linarith
  apply hv.trans
  apply (div_le_iff₀ hk0).2
  have hmul := mul_le_mul_of_nonneg_right hm hH
  nlinarith

/-- The same velocity lies strictly inside the actual cut-off scale. -/
theorem velocity_lt_cut (s : Data k) (hk : 3 ≤ k) (g : GeometryScales k)
    {v : ℝ} (hv : |v| ≤ 4 * cutoff k * (mesh s hk).H / k) :
    |v| < cutScale k := by
  rw [mesh_H] at hv
  exact hv.trans_lt g.cut_error

/-- The total drift over the progression is less than half a unit. -/
theorem velocity_div_small (s : Data k) (hk : 3 ≤ k) (g : GeometryScales k)
    {h : ℕ} (hh : 0 < h) {v : ℝ}
    (hv : |v| ≤ 4 * cutoff k * (mesh s hk).H / k) :
    (k : ℝ) * |v / (h : ℝ)| < 1 / 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  have hd : |v / (h : ℝ)| ≤ |v| := by
    rw [abs_div, abs_of_pos hh0]
    exact div_le_self (abs_nonneg v) hh1
  have hb : (k : ℝ) * |v| ≤ 4 * cutoff k * (mesh s hk).H := by
    have := (le_div_iff₀ hk0).mp hv
    nlinarith
  have hs : 4 * (cutoff k : ℝ) * (mesh s hk).H < 1 / 2 := by
    simpa only [mesh_H] using g.rational_separation
  exact (mul_le_mul_of_nonneg_left hd hk0.le).trans_lt (hb.trans_lt hs)

/-- The error in the lattice lifting argument remains below one integer. -/
theorem lattice_error_small (s : Data k) (hk : 3 ≤ k) (g : GeometryScales k)
    {h : ℕ} (hh : 0 < h) :
    2 * (mesh s hk).H + 4 * cutoff k * (mesh s hk).H / (h : ℝ) < 1 := by
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  have hH : 0 ≤ (mesh s hk).H := by
    rw [mesh_H]
    exact (meshScale_pos (show 0 < k by omega)).le
  have hn : 0 ≤ 4 * (cutoff k : ℝ) * (mesh s hk).H := by positivity
  have hd := div_le_self hn hh1
  have hs : 2 * (mesh s hk).H + 4 * cutoff k * (mesh s hk).H < 1 := by
    simpa only [mesh_H] using g.lattice_separation
  linarith

/-- Distinct rational returns cannot hide inside one first-system cell. -/
theorem twice_period_uniformWidth_lt_one (s : Data k) (hk : 3 ≤ k)
    (g : GeometryScales k) {h : ℕ} (hmax : h ≤ 2 * cutoff k) :
    2 * (h : ℝ) * (1 / (uniformCount k : ℝ)) < 1 := by
  have hH : 0 ≤ (mesh s hk).H := by
    rw [mesh_H]
    exact (meshScale_pos (show 0 < k by omega)).le
  have hm : (h : ℝ) ≤ 2 * cutoff k := by exact_mod_cast hmax
  have hw := mul_le_mul_of_nonneg_left (uniformWidth_le_meshH s hk)
    (show 0 ≤ 2 * (h : ℝ) by positivity)
  have hp := mul_le_mul_of_nonneg_right hm hH
  have hs : 4 * (cutoff k : ℝ) * (mesh s hk).H < 1 / 2 := by
    simpa only [mesh_H] using g.rational_separation
  nlinarith

end QuantitativeVanDerWaerden.ConstructionModel

end

end OAI
end
end

section
section
namespace OAI

/-!
# Rational separation survives the real drift

The proofs use real representative differences and integral errors directly.
They do not assume a separation property of labels: it is deduced from the
primitive rational path and the proved width bound on a label's first intervals.
-/


namespace QuantitativeVanDerWaerden

/-- The scale inequalities from the closest-return argument leave enough
space between distinct rational residues for an entire first-coordinate box. -/
theorem return_separation_margin {h : ℕ} {M H W : ℝ}
    (hh : 0 < h) (hperiod : (h : ℝ) ≤ 2 * M)
    (hW : 0 ≤ W) (hWH : W ≤ H) (hsmall : 4 * M * H < 1) :
    W + (2 * M * W) / h < 1 / (h : ℝ) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hM : 0 ≤ M := by linarith
  have h₁ := mul_le_mul_of_nonneg_right hperiod hW
  have h₂ := mul_le_mul_of_nonneg_left hWH (show 0 ≤ 4 * M by positivity)
  apply (lt_div_iff₀ hhR).2
  have hcancel : (2 * M * W / (h : ℝ)) * h = 2 * M * W :=
    div_mul_cancel₀ _ hhR.ne'
  nlinarith

/-- The drift accumulated between two indices in the progression is at most
the full-length drift divided by the return denominator. -/
theorem index_drift_le {a b k h : ℕ} {u U : ℝ}
    (ha : a < k) (hb : b < k) (hh : 0 < h)
    (hu : (k : ℝ) * |u| ≤ U) :
    |((a : ℝ) - b) / h * u| ≤ U / h := by
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hak : (a : ℝ) ≤ k := by exact_mod_cast ha.le
  have hbk : (b : ℝ) ≤ k := by exact_mod_cast hb.le
  have hd : |(a : ℝ) - b| ≤ k := abs_le.mpr ⟨by linarith, by linarith⟩
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  calc
    _ = (|(a : ℝ) - b| * |u|) / h := by
      rw [abs_mul, abs_div, abs_of_pos hhR]
      ring
    _ ≤ ((k : ℝ) * |u|) / h :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hd (abs_nonneg u)) hhR.le
    _ ≤ U / h := div_le_div_of_nonneg_right hu hhR.le

/-- Indices incongruent modulo the primitive denominator have a separated
coordinate, even after adding the actual small drift and choosing representatives. -/
theorem rational_path_coordinate_separation {ι : Type uIndex} [Fintype ι]
    {k h a b : ℕ} {W U : ℝ} {t : ι → ℤ}
    (X : ℕ → ι → ℝ) (A u : ι → ℝ)
    (hh : 0 < h) (hp : PrimitiveVector h t)
    (hpath : ∀ n, n < k → ∀ i, ∃ z : ℤ,
      X n i - A i - (n : ℝ) / h * ((t i : ℝ) + u i) = z)
    (hdrift : ∀ i, (k : ℝ) * |u i| ≤ U)
    (hmargin : W + U / h < 1 / (h : ℝ))
    (ha : a < k) (hb : b < k) (hab : ¬ (h : ℤ) ∣ (a : ℤ) - b) :
    ∃ i, W < |X a i - X b i| := by
  obtain ⟨i, hi⟩ := hp.exists_separated_coordinate hh hab
  refine ⟨i, ?_⟩
  obtain ⟨za, hza⟩ := hpath a ha i
  obtain ⟨zb, hzb⟩ := hpath b hb i
  have hid : (((a : ℤ) - b : ℤ) : ℝ) * (t i : ℝ) / h -
      ((-(za - zb) : ℤ) : ℝ) =
      (X a i - X b i) - ((a : ℝ) - b) / h * u i := by
    push_cast
    calc
      _ = ((a : ℝ) / h * ((t i : ℝ) + u i) -
          (b : ℝ) / h * ((t i : ℝ) + u i)) +
          ((za : ℝ) - zb) - ((a : ℝ) - b) / h * u i := by ring
      _ = _ := by linarith
  have hsep := hi (-(za - zb))
  rw [hid] at hsep
  have htriangle := abs_sub (X a i - X b i) (((a : ℝ) - b) / h * u i)
  have hsmall := index_drift_le ha hb hh (hdrift i)
  by_contra hnot
  have hle : |X a i - X b i| ≤ W := le_of_not_gt hnot
  linarith

/-- Every occurrence of one label lies in one residue class. The label
hypothesis is only its actual coordinate-width bound. -/
theorem same_label_divisible_index_difference {ι : Type uIndex} {L : Type uL} [Fintype ι]
    {k h a b : ℕ} {W U : ℝ} {t : ι → ℤ}
    (X : ℕ → ι → ℝ) (A u : ι → ℝ) (label : ℕ → L)
    (hh : 0 < h) (hp : PrimitiveVector h t)
    (hpath : ∀ n, n < k → ∀ i, ∃ z : ℤ,
      X n i - A i - (n : ℝ) / h * ((t i : ℝ) + u i) = z)
    (hdrift : ∀ i, (k : ℝ) * |u i| ≤ U)
    (hmargin : W + U / h < 1 / (h : ℝ))
    (hwidth : ∀ n, n < k → ∀ m, m < k → label n = label m →
      ∀ i, |X n i - X m i| ≤ W)
    (ha : a < k) (hb : b < k) (hlab : label a = label b) :
    (h : ℤ) ∣ (a : ℤ) - b := by
  by_contra hn
  obtain ⟨i, hi⟩ := rational_path_coordinate_separation X A u hh hp hpath
    hdrift hmargin ha hb hn
  exact (not_lt_of_ge (hwidth a ha b hb hlab i)) hi

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Full blocks in the long-period alternative

All displacements are actual real representatives modulo an explicitly
integral error. In particular, the heavy anchor in the stationary-coordinate
argument need not be a regular position.
-/

namespace QuantitativeVanDerWaerden

open scoped BigOperators

/-- Re-anchor an actual rational path at the beginning of a full block. -/
theorem rational_full_block_reanchor {k h j₀ : ℕ} {a : ℤ} {y v : ℝ}
    (Y : ℕ → ℝ) (hh : 0 < h) (hfull : j₀ + h ≤ k)
    (hpath : ∀ j, j < k → ∃ e : ℤ,
      Y j - y - (j : ℝ) / h * ((a : ℝ) + v) = e) :
    ∀ z : Fin h, ∃ e : ℤ,
      Y (j₀ + z.val) - Y j₀ - (z.val : ℝ) / h * ((a : ℝ) + v) = e := by
  intro z
  obtain ⟨e₀, he₀⟩ := hpath j₀ (by omega)
  obtain ⟨ez, hez⟩ := hpath (j₀ + z.val) (by omega)
  refine ⟨ez - e₀, ?_⟩
  push_cast at hez ⊢
  calc
    _ = (Y (j₀ + z.val) - y - ((j₀ : ℝ) + z.val) / h * ((a : ℝ) + v)) -
        (Y j₀ - y - (j₀ : ℝ) / h * ((a : ℝ) + v)) := by ring
    _ = _ := by rw [hez, he₀]

/-- A block displacement accumulates at most one unit of its drift vector. -/
theorem full_block_drift_le {h : ℕ} (hh : 0 < h) (z w : Fin h) (v : ℝ) :
    |((z.val : ℝ) - w.val) / h * v| ≤ |v| := by
  have hd := index_drift_le (a := z.val) (b := w.val) (k := h) (h := h)
    (u := v) (U := (h : ℝ) * |v|) z.isLt w.isLt hh le_rfl
  have hhR : (h : ℝ) ≠ 0 := by positivity
  simpa only [mul_div_cancel_left₀ _ hhR] using hd

/-- If the rational step is integral, every pair of block positions is
within one drift amplitude modulo integers, including centered cut crossings. -/
theorem stationary_full_block_distance {h : ℕ} {a : ℤ} {y v : ℝ}
    (Y : Fin h → ℝ) (hh : 0 < h) (hstationary : (h : ℤ) ∣ a)
    (hpath : ∀ z, ∃ e : ℤ,
      Y z - y - (z.val : ℝ) / h * ((a : ℝ) + v) = e)
    (z w : Fin h) :
    ∃ e : ℤ, |centered (Y z) - centered (Y w) - e| ≤ |v| := by
  obtain ⟨c, hc⟩ := hstationary
  obtain ⟨ez, hez⟩ := hpath z
  obtain ⟨ew, hew⟩ := hpath w
  let e : ℤ := ez - ew + ((z.val : ℤ) - w.val) * c -
    ⌊Y z + 1 / 2⌋ + ⌊Y w + 1 / 2⌋
  refine ⟨e, ?_⟩
  have ha : (a : ℝ) = (h : ℝ) * c := by exact_mod_cast hc
  have hhR : (h : ℝ) ≠ 0 := by positivity
  have hquot (u : ℝ) : u / h * (a : ℝ) = u * c := by
    rw [ha]
    field_simp
  have hdiff : centered (Y z) - centered (Y w) - (e : ℝ) =
      ((z.val : ℝ) - w.val) / h * v := by
    dsimp [centered, e]
    push_cast
    have hz : (z.val : ℝ) / h * ((a : ℝ) + v) =
        (z.val : ℝ) * c + (z.val : ℝ) / h * v := by
      rw [mul_add, hquot]
    have hw : (w.val : ℝ) / h * ((a : ℝ) + v) =
        (w.val : ℝ) * c + (w.val : ℝ) / h * v := by
      rw [mul_add, hquot]
    rw [hz] at hez
    rw [hw] at hew
    have hr : ((z.val : ℝ) - w.val) / h * v =
        (z.val : ℝ) / h * v - (w.val : ℝ) / h * v := by ring
    rw [hr]
    nlinarith
  rw [hdiff]
  exact full_block_drift_le hh z w v

/-- Actual stationary-coordinate interval widths satisfy eligibility at
every position, using any heavy anchor, without regularity of that anchor. -/
theorem stationary_full_block_width (A : AdaptiveMesh)
    {h : ℕ} {a : ℤ} {y v : ℝ} (Y : Fin h → ℝ)
    (hh : 0 < h) (hstationary : (h : ℤ) ∣ a)
    (hpath : ∀ z, ∃ e : ℤ,
      Y z - y - (z.val : ℝ) / h * ((a : ℝ) + v) = e)
    (anchor : Fin h)
    (hrelative : |v| ≤ A.width (A.meshLabel (Y anchor)) / 16) :
    ∀ z, |v| ≤ A.width (A.meshLabel (Y z)) := by
  intro z
  have hx := A.meshLabel_contains (Y anchor)
  have hy := A.meshLabel_contains (Y z)
  obtain ⟨e, he⟩ := stationary_full_block_distance Y hh hstationary hpath z anchor
  have hwidthpos := A.width_pos (A.meshLabel (Y anchor))
  have hnear : ∃ e : ℤ, |centered (Y z) - centered (Y anchor) - e| ≤
      2 * A.width (A.meshLabel (Y anchor)) := by
    exact ⟨e, he.trans (by linarith)⟩
  exact hrelative.trans (A.neighbor_width _ _ hx.1 hx.2.le hy.1 hy.2.le hnear)

theorem stationary_relative_width_threshold {M k L v : ℝ}
    (hL : 0 ≤ L) (hsmall : 2 * M / k ≤ 1 / 16)
    (hrelative : |v| ≤ (2 * M / k) * L) : |v| ≤ L / 16 := by
  have h := mul_le_mul_of_nonneg_right hsmall hL
  nlinarith

/-- A truly nonregular sample must be near the cut in its undrifted grid.
The error is explicitly integral; this includes every representative cut. -/
theorem nonregular_implies_grid_near {h : ℕ} (hh : 0 < h)
    (z : Fin h) {a : ℝ} {y v actual η : ℝ}
    (hpath : ∃ e : ℤ,
      actual - y - (z.val : ℝ) / h * (a + v) = e)
    (hdrift : |v| < η) (hbad : rho actual < η) :
    rho (y + (z.val : ℝ) * a / h) < 2 * η := by
  obtain ⟨e, he⟩ := hpath
  have herror : actual - (y + (z.val : ℝ) * a / h) - e =
      (z.val : ℝ) / h * v := by
    calc
      _ = (actual - y - (z.val : ℝ) / h * (a + v) - e) +
          (z.val : ℝ) / h * v := by ring
      _ = _ := by rw [he]; ring
  have hsmall : |(z.val : ℝ) / h * v| ≤ |v| := by
    have hhR : (0 : ℝ) < h := by positivity
    have hz : (z.val : ℝ) ≤ h := by exact_mod_cast z.isLt.le
    have hz0 : (0 : ℝ) ≤ z.val := Nat.cast_nonneg z.val
    rw [abs_mul, abs_of_nonneg (div_nonneg hz0 hhR.le)]
    exact mul_le_of_le_one_left (abs_nonneg v) ((div_le_one hhR).mpr hz)
  have hlip := rho_lipschitz_integer actual (y + (z.val : ℝ) * a / h) e
  rw [herror] at hlip
  have hlow := (abs_le.mp (hlip.trans hsmall)).1
  linarith

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Counting regular positions in a long-period block

The finite union bound is expressed on literal subsets of the block indices.
The coordinate bounds are supplied by the actual rational-grid count.
-/

namespace QuantitativeVanDerWaerden

open scoped BigOperators

theorem regular_count_of_coordinate_bounds {D h : ℕ}
    (rotating : Finset (Fin D)) (bad : Fin D → Finset (Fin h)) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hcount : ∀ i ∈ rotating, ((bad i).card : ℝ) ≤ (h : ℝ) * ε)
    (hsmall : (D : ℝ) * ε ≤ 1 / 2) :
    (h : ℝ) / 2 ≤ ((Finset.univ \ rotating.biUnion bad).card : ℝ) := by
  classical
  have hunion : ((rotating.biUnion bad).card : ℝ) ≤
      ∑ i ∈ rotating, ((bad i).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s := rotating) (t := bad))
  have hsum : (∑ i ∈ rotating, ((bad i).card : ℝ)) ≤
      (rotating.card : ℝ) * ((h : ℝ) * ε) := by
    calc
      _ ≤ ∑ _i ∈ rotating, (h : ℝ) * ε := Finset.sum_le_sum hcount
      _ = _ := by simp
  have hcard : (rotating.card : ℝ) ≤ D := by
    exact_mod_cast (show rotating.card ≤ D by simpa using rotating.card_le_univ)
  have hnonneg : 0 ≤ (h : ℝ) * ε := mul_nonneg (Nat.cast_nonneg h) hε
  have htotal : ((rotating.biUnion bad).card : ℝ) ≤ (h : ℝ) / 2 := by
    calc
      _ ≤ (rotating.card : ℝ) * ((h : ℝ) * ε) := hunion.trans hsum
      _ ≤ (D : ℝ) * ((h : ℝ) * ε) := mul_le_mul_of_nonneg_right hcard hnonneg
      _ = (h : ℝ) * ((D : ℝ) * ε) := by ring
      _ ≤ (h : ℝ) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg h)
      _ = (h : ℝ) / 2 := by ring
  have hsplit : ((Finset.univ \ rotating.biUnion bad).card : ℝ) +
      ((rotating.biUnion bad).card : ℝ) = h := by
    exact_mod_cast (show (Finset.univ \ rotating.biUnion bad).card +
      (rotating.biUnion bad).card = h by
        simpa using Finset.card_sdiff_add_card_eq_card
          (Finset.subset_univ (rotating.biUnion bad)))
  linarith

/-- The finite complement in the union bound is exactly the regular-position
predicate, with equality at the cut-distance threshold retained as regular. -/
theorem regular_positions_eq_complement {D h : ℕ}
    (rotating : Finset (Fin D)) (Y : Fin h → Fin D → ℝ) (η : ℝ) :
    (Finset.univ.filter fun z => ∀ i ∈ rotating, η ≤ rho (Y z i)) =
      Finset.univ \ rotating.biUnion
        (fun i => Finset.univ.filter fun z => rho (Y z i) < η) := by
  classical
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    Finset.mem_biUnion, not_exists, not_and, not_lt]

theorem regular_fraction_constant {D : ℕ} (hD : 3 ≤ D) :
    (D : ℝ) * (4 * (1 / (1000 * (D : ℝ))) + 1 / (D : ℝ) ^ 2) ≤ 1 / 2 := by
  have hDR : (3 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := by linarith
  have hid : (D : ℝ) * (4 * (1 / (1000 * (D : ℝ))) + 1 / (D : ℝ) ^ 2) =
      4 / 1000 + 1 / (D : ℝ) := by
    field_simp [hDpos.ne']
  rw [hid]
  have hrec : 1 / (D : ℝ) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hDR
  linarith

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Multiplicities in a rational circle grid

An integer-periodic predicate samples a rational step `a / h` on precisely
`h / gcd h a` different points, each with multiplicity `gcd h a`.
The proof reindexes actual finite types using division with remainder and the
permutation given by multiplication by a coprime numerator.
-/

namespace QuantitativeVanDerWaerden

/-- Multiplication by a coprime natural number permutes the finite residues. -/
noncomputable def mulModGridEquiv (s b : ℕ) (hs : 0 < s)
    (hcop : Nat.gcd s b = 1) : Equiv.Perm (Fin s) := by
  let f : Fin s → Fin s := fun x => ⟨x.val * b % s, Nat.mod_lt _ hs⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Fin.ext
    have hm : Nat.ModEq s (x.val * b) (y.val * b) := congrArg Fin.val hxy
    exact (Nat.ModEq.cancel_right_of_coprime hcop hm).eq_of_lt_of_lt x.isLt y.isLt
  exact Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, rfl⟩)

@[simp] theorem mulModGridEquiv_val (s b : ℕ) (hs : 0 < s)
    (hcop : Nat.gcd s b = 1) (x : Fin s) :
    (mulModGridEquiv s b hs hcop x).val = x.val * b % s := rfl

/-- An integer-periodic predicate is unchanged when a rational numerator is
reduced modulo its positive denominator. -/
theorem periodic_predicate_div_mod (P : ℝ → Prop)
    (hperiod : ∀ x (n : ℤ), P (x + n) ↔ P x)
    (y : ℝ) (n s : ℕ) (hs : 0 < s) :
    P (y + (n : ℝ) / s) ↔ P (y + ((n % s : ℕ) : ℝ) / s) := by
  have hsR : (s : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) = ((n % s : ℕ) : ℝ) + (s : ℝ) * (n / s : ℕ) := by
    exact_mod_cast (Nat.mod_add_div n s).symm
  have heq : y + (n : ℝ) / s =
      (y + ((n % s : ℕ) : ℝ) / s) + ((n / s : ℕ) : ℝ) := by
    rw [hn]
    field_simp
    ring
  rw [heq]
  simpa only [Int.cast_natCast] using
    hperiod (y + ((n % s : ℕ) : ℝ) / s) (n / s : ℕ)

/-- A full block with a coprime step visits every point of its uniform grid
once, for every integer-periodic predicate. -/
theorem card_coprime_rational_grid_periodic (s b : ℕ) (hs : 0 < s)
    (hcop : Nat.gcd s b = 1) (P : ℝ → Prop) [DecidablePred P]
    (hperiod : ∀ x (n : ℤ), P (x + n) ↔ P x) (y : ℝ) :
    Fintype.card {j : Fin s // P (y + (j.val : ℝ) * b / s)} =
      Fintype.card {j : Fin s // P (y + (j.val : ℝ) / s)} := by
  apply Fintype.card_congr
  apply (mulModGridEquiv s b hs hcop).subtypeEquiv
  intro j
  simpa only [mulModGridEquiv_val, Nat.cast_mul] using
    periodic_predicate_div_mod P hperiod y (j.val * b) s hs

/-- Repeating the rational step for `d` full denominator blocks multiplies
every periodic-predicate count by `d`. -/
theorem card_repeated_rational_grid_periodic (d s b : ℕ) (hs : 0 < s)
    (P : ℝ → Prop) [DecidablePred P]
    (hperiod : ∀ x (n : ℤ), P (x + n) ↔ P x) (y : ℝ) :
    Fintype.card {z : Fin (d * s) // P (y + (z.val : ℝ) * b / s)} =
      d * Fintype.card {j : Fin s // P (y + (j.val : ℝ) * b / s)} := by
  let Q : Fin s → Prop := fun j => P (y + (j.val : ℝ) * b / s)
  let split : {p : Fin d × Fin s // Q p.2} ≃ Fin d × {j : Fin s // Q j} :=
    { toFun := fun p => (p.val.1, ⟨p.val.2, p.property⟩)
      invFun := fun p => ⟨(p.1, p.2.val), p.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hp : ∀ p : Fin d × Fin s,
      Q p.2 ↔ P (y + ((finProdFinEquiv p).val : ℝ) * b / s) := by
    intro p
    change P (y + (p.2.val : ℝ) * b / s) ↔
      P (y + ((p.2.val + s * p.1.val : ℕ) : ℝ) * b / s)
    have hsR : (s : ℝ) ≠ 0 := by positivity
    have heq : y + ((p.2.val + s * p.1.val : ℕ) : ℝ) * b / s =
        (y + (p.2.val : ℝ) * b / s) + ((p.1.val * b : ℕ) : ℝ) := by
      push_cast
      field_simp
      ring
    rw [heq]
    simpa only [Int.cast_natCast] using
      (hperiod (y + (p.2.val : ℝ) * b / s) (p.1.val * b : ℕ)).symm
  calc
    _ = Fintype.card {p : Fin d × Fin s // Q p.2} :=
      (Fintype.card_congr (finProdFinEquiv.subtypeEquiv hp)).symm
    _ = Fintype.card (Fin d × {j : Fin s // Q j}) := Fintype.card_congr split
    _ = _ := by rw [Fintype.card_prod, Fintype.card_fin]

/-- Exact multiplicity of the reduced rational grid. This applies to any
predicate invariant under integer translation, including circle arcs. -/
theorem card_rational_grid_periodic (h a : ℕ) (hh : 0 < h)
    (P : ℝ → Prop) [DecidablePred P]
    (hperiod : ∀ x (n : ℤ), P (x + n) ↔ P x) (y : ℝ) :
    Fintype.card {z : Fin h // P (y + (z.val : ℝ) * a / h)} =
      Nat.gcd h a * Fintype.card {j : Fin (h / Nat.gcd h a) //
        P (y + (j.val : ℝ) / (h / Nat.gcd h a : ℕ))} := by
  let d := Nat.gcd h a
  let s := h / d
  let b := a / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left a hh
  have hs : 0 < s := Nat.div_gcd_pos_of_pos_left a hh
  have hcop : Nat.gcd s b = 1 := Nat.gcd_div_gcd_div_gcd_of_pos_left hh
  have hfactor : h = d * s := (Nat.mul_div_cancel' (Nat.gcd_dvd_left h a)).symm
  have afactor : a = d * b := (Nat.mul_div_cancel' (Nat.gcd_dvd_right h a)).symm
  have hratio (z : ℕ) : (z : ℝ) * a / h = (z : ℝ) * b / s := by
    rw [hfactor, afactor]
    push_cast
    have hdR : (d : ℝ) ≠ 0 := by positivity
    have hsR : (s : ℝ) ≠ 0 := by positivity
    field_simp
  calc
    _ = Fintype.card {z : Fin (d * s) // P (y + (z.val : ℝ) * b / s)} := by
      apply Fintype.card_congr
      apply (finCongr hfactor).subtypeEquiv
      intro z
      change P (y + (z.val : ℝ) * a / h) ↔ P (y + (z.val : ℝ) * b / s)
      rw [hratio]
    _ = d * Fintype.card {j : Fin s // P (y + (j.val : ℝ) * b / s)} :=
      card_repeated_rational_grid_periodic d s b hs P hperiod y
    _ = _ := by rw [card_coprime_rational_grid_periodic s b hs hcop P hperiod y]

/-- Finset-filter form of the exact rational-grid multiplicity formula. -/
theorem card_filter_rational_grid_periodic (h a : ℕ) (hh : 0 < h)
    (P : ℝ → Prop) [DecidablePred P]
    (hperiod : ∀ x (n : ℤ), P (x + n) ↔ P x) (y : ℝ) :
    (Finset.univ.filter (fun z : Fin h => P (y + (z.val : ℝ) * a / h))).card =
      Nat.gcd h a * (Finset.univ.filter (fun j : Fin (h / Nat.gcd h a) =>
        P (y + (j.val : ℝ) / (h / Nat.gcd h a : ℕ)))).card := by
  simpa only [Fintype.card_subtype] using
    card_rational_grid_periodic h a hh P hperiod y

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-! Exact short-arc counts for a shifted rational grid.  The integer lift
below counts the actual points, including closed arc endpoints. -/

namespace QuantitativeVanDerWaerden

open Finset

theorem rho_eq_abs_centered_half_shift (x : ℝ) :
    rho x = |centered (x + 1 / 2)| := by
  let t := centered x
  have ht := centered_mem x
  have hx : x + 1 / 2 = (t + 1 / 2) + (⌊x + 1 / 2⌋ : ℤ) := by
    dsimp [t, centered]
    ring
  rw [hx, centered_add_int]
  change 1 / 2 - |t| = |centered (t + 1 / 2)|
  by_cases hneg : t < 0
  · rw [centered_eq_of_mem (by dsimp [t]; linarith [ht.1]) (by linarith),
      abs_of_neg hneg, abs_of_nonneg (by dsimp [t]; linarith [ht.1])]
    ring
  · have hnonneg : 0 ≤ t := le_of_not_gt hneg
    have he : t + 1 / 2 = (t - 1 / 2) + ((1 : ℤ) : ℝ) := by push_cast; ring
    rw [he, centered_add_int,
      centered_eq_of_mem (by linarith) (by dsimp [t]; linarith [ht.2]),
      abs_of_nonneg hnonneg, abs_of_nonpos (by dsimp [t]; linarith [ht.2])]
    ring

theorem integer_interval_card_le {lo hi : ℝ} (hlo : lo ≤ hi) :
    ((Icc ⌈lo⌉ ⌊hi⌋).card : ℝ) ≤ hi - lo + 1 := by
  have hi' := Int.lt_floor_add_one hi
  have hceil : ⌈lo⌉ ≤ ⌊hi⌋ + 1 := Int.ceil_le.mpr (by push_cast; linarith)
  have hc : ((Icc ⌈lo⌉ ⌊hi⌋).card : ℝ) =
      (⌊hi⌋ : ℝ) + 1 - (⌈lo⌉ : ℝ) := by
    exact_mod_cast Int.card_Icc_of_le ⌈lo⌉ ⌊hi⌋ hceil
  rw [hc]
  linarith [Int.floor_le hi, Int.le_ceil lo]

noncomputable def rationalGridLift (s : ℕ) (y : ℝ) (j : Fin s) : ℤ :=
  (j.val : ℤ) - (s : ℤ) * ⌊y + (j.val : ℝ) / s + 1 / 2⌋

theorem rationalGridLift_identity {s : ℕ} (hs : 0 < s) (y : ℝ) (j : Fin s) :
    (s : ℝ) * centered (y + (j.val : ℝ) / s) =
      (s : ℝ) * y + rationalGridLift s y j := by
  have hsR : (s : ℝ) ≠ 0 := by positivity
  dsimp [rationalGridLift, centered]
  push_cast
  field_simp
  ring

theorem rationalGridLift_injective {s : ℕ} (hs : 0 < s) (y : ℝ) :
    Function.Injective (rationalGridLift s y) := by
  intro i j hij
  let n : ℤ := ⌊y + (i.val : ℝ) / s + 1 / 2⌋ -
    ⌊y + (j.val : ℝ) / s + 1 / 2⌋
  have hn : (i.val : ℝ) - j.val = (s : ℝ) * n := by
    have hR := congrArg (fun z : ℤ => (z : ℝ)) hij
    dsimp [rationalGridLift] at hR
    dsimp [n]
    push_cast at hR ⊢
    nlinarith
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hi : (i.val : ℝ) < s := by exact_mod_cast i.isLt
  have hj : (j.val : ℝ) < s := by exact_mod_cast j.isLt
  have hi0 : (0 : ℝ) ≤ i.val := by positivity
  have hj0 : (0 : ℝ) ≤ j.val := by positivity
  have hnsmall : |(n : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith
  have hnzero := integer_eq_zero_of_abs_lt_one hnsmall
  rw [hnzero, Int.cast_zero, mul_zero] at hn
  apply Fin.ext
  exact_mod_cast (sub_eq_zero.mp hn)

/-- An equally spaced shifted grid has at most `2*e*s+1` points in a
closed circle arc of radius `e`.  This remains true for large radii. -/
theorem uniform_grid_centered_count_le (s : ℕ) (hs : 0 < s) (y e : ℝ)
    (he : 0 ≤ e) :
    (((univ : Finset (Fin s)).filter
      (fun j => |centered (y + (j.val : ℝ) / s)| ≤ e)).card : ℝ) ≤
      2 * e * s + 1 := by
  classical
  let lo := (s : ℝ) * (-e - y)
  let hi := (s : ℝ) * (e - y)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hlh : lo ≤ hi := by dsimp [lo, hi]; nlinarith
  have hcard : ((univ : Finset (Fin s)).filter
      (fun j => |centered (y + (j.val : ℝ) / s)| ≤ e)).card ≤
      (Icc ⌈lo⌉ ⌊hi⌋).card := by
    apply card_le_card_of_injOn (rationalGridLift s y)
    · intro j hj
      have hj' := abs_le.mp (mem_filter.mp hj).2
      have hrep := rationalGridLift_identity hs y j
      apply mem_Icc.mpr
      constructor
      · apply Int.ceil_le.mpr
        dsimp [lo]
        nlinarith [mul_nonneg hsR.le (sub_nonneg.mpr hj'.1)]
      · apply Int.le_floor.mpr
        dsimp [hi]
        nlinarith [mul_nonneg hsR.le (sub_nonneg.mpr hj'.2)]
    · exact (rationalGridLift_injective hs y).injOn
  have hcardR : (((univ : Finset (Fin s)).filter
      (fun j => |centered (y + (j.val : ℝ) / s)| ≤ e)).card : ℝ) ≤
      ((Icc ⌈lo⌉ ⌊hi⌋).card : ℝ) := by exact_mod_cast hcard
  have hbound := hcardR.trans (integer_interval_card_le hlh)
  dsimp [lo, hi] at hbound
  nlinarith

theorem uniform_grid_rho_count_le (s : ℕ) (hs : 0 < s) (y η : ℝ)
    (hη : 0 ≤ η) :
    (((univ : Finset (Fin s)).filter
      (fun j => rho (y + (j.val : ℝ) / s) ≤ 2 * η)).card : ℝ) ≤
      4 * η * s + 1 := by
  have h := uniform_grid_centered_count_le s hs (y + 1 / 2) (2 * η)
    (by positivity)
  have heq : (fun j : Fin s => rho (y + (j.val : ℝ) / s) ≤ 2 * η) =
      (fun j : Fin s => |centered (y + 1 / 2 + (j.val : ℝ) / s)| ≤ 2 * η) := by
    funext j
    rw [rho_eq_abs_centered_half_shift]
    congr 3
    ring
  have hf : (univ.filter (fun j : Fin s => rho (y + (j.val : ℝ) / s) ≤ 2 * η)) =
      (univ.filter (fun j : Fin s =>
        |centered (y + 1 / 2 + (j.val : ℝ) / s)| ≤ 2 * η)) := by
    apply filter_congr
    intro j _
    exact Iff.of_eq (congrFun heq j)
  rw [hf]
  nlinarith

theorem rational_grid_rho_closed_count_le (h a : ℕ) (hh : 0 < h) (y η : ℝ)
    (hη : 0 ≤ η) :
    (((univ : Finset (Fin h)).filter
      (fun z => rho (y + (z.val : ℝ) * a / h) ≤ 2 * η)).card : ℝ) ≤
      (h : ℝ) * (4 * η + 1 / (h / Nat.gcd h a : ℕ)) := by
  classical
  let d := Nat.gcd h a
  let s := h / d
  have hs : 0 < s := Nat.div_gcd_pos_of_pos_left a hh
  have hsR : (s : ℝ) ≠ 0 := by positivity
  have hperiod : ∀ x (n : ℤ), (rho (x + n) ≤ 2 * η) ↔ (rho x ≤ 2 * η) := by
    intro x n
    rw [rho_add_int]
  have hc := card_filter_rational_grid_periodic h a hh
    (fun x => rho x ≤ 2 * η) hperiod y
  have hcR : (((univ : Finset (Fin h)).filter
      (fun z => rho (y + (z.val : ℝ) * a / h) ≤ 2 * η)).card : ℝ) =
      (d : ℝ) * (((univ : Finset (Fin s)).filter
        (fun j => rho (y + (j.val : ℝ) / s) ≤ 2 * η)).card : ℝ) := by
    exact_mod_cast hc
  have hbound := uniform_grid_rho_count_le s hs y η hη
  have hf : (h : ℝ) = (d : ℝ) * s := by
    exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left h a)).symm
  change _ ≤ (h : ℝ) * (4 * η + 1 / (s : ℝ))
  calc
    _ = (d : ℝ) * (((univ : Finset (Fin s)).filter
        (fun j => rho (y + (j.val : ℝ) / s) ≤ 2 * η)).card : ℝ) := hcR
    _ ≤ (d : ℝ) * (4 * η * s + 1) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (h : ℝ) * (4 * η + 1 / (s : ℝ)) := by
      rw [hf]
      field_simp

/-- Strict cut-neighborhood version used for nonregular positions. -/
theorem rational_grid_rho_count_le (h a : ℕ) (hh : 0 < h) (y η : ℝ)
    (hη : 0 ≤ η) :
    (((univ : Finset (Fin h)).filter
      (fun z => rho (y + (z.val : ℝ) * a / h) < 2 * η)).card : ℝ) ≤
      (h : ℝ) * (4 * η + 1 / (h / Nat.gcd h a : ℕ)) := by
  classical
  have hsub : ((univ : Finset (Fin h)).filter
      (fun z => rho (y + (z.val : ℝ) * a / h) < 2 * η)) ⊆
      ((univ : Finset (Fin h)).filter
        (fun z => rho (y + (z.val : ℝ) * a / h) ≤ 2 * η)) := by
    intro z hz
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hz).2.le⟩
  have hcard : (((univ : Finset (Fin h)).filter
      (fun z => rho (y + (z.val : ℝ) * a / h) < 2 * η)).card : ℝ) ≤
      (((univ : Finset (Fin h)).filter
        (fun z => rho (y + (z.val : ℝ) * a / h) ≤ 2 * η)).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  exact hcard.trans (rational_grid_rho_closed_count_le h a hh y η hη)

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-! The regular-position bound instantiated with the actual shifted rational
grids and their actual integer periods. -/

namespace QuantitativeVanDerWaerden

/-- At least half the positions in a full long-period block are regular.
The coordinate count is proved by the rational-grid theorem, including grid
multiplicity; it is not an assumption of this statement. -/
theorem long_block_regular_card {D h : ℕ} (hh : 0 < h) (hD : 0 < D)
    (rotating : Finset (Fin D)) (Y : Fin h → Fin D → ℝ)
    (y v : Fin D → ℝ) (a : Fin D → ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hpath : ∀ i ∈ rotating, ∀ z, ∃ e : ℤ,
      Y z i - y i - (z.val : ℝ) / h * ((a i : ℝ) + v i) = e)
    (hdrift : ∀ i ∈ rotating, |v i| < η)
    (hperiod : ∀ i ∈ rotating, D ^ 2 < h / Nat.gcd h (a i))
    (hsmall : (D : ℝ) * (4 * η + 1 / (D : ℝ) ^ 2) ≤ 1 / 2) :
    (h : ℝ) / 2 ≤
      ((Finset.univ.filter fun z => ∀ i ∈ rotating, η ≤ rho (Y z i)).card : ℝ) := by
  classical
  let bad : Fin D → Finset (Fin h) := fun i =>
    Finset.univ.filter fun z => rho (Y z i) < η
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hcount : ∀ i ∈ rotating, ((bad i).card : ℝ) ≤
      (h : ℝ) * (4 * η + 1 / (D : ℝ) ^ 2) := by
    intro i hi
    let grid : Finset (Fin h) := Finset.univ.filter fun z =>
      rho (y i + (z.val : ℝ) * (a i : ℝ) / h) < 2 * η
    have hsubset : bad i ⊆ grid := by
      intro z hz
      have hbad : rho (Y z i) < η := (Finset.mem_filter.mp hz).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ z, ?_⟩
      exact nonregular_implies_grid_near hh z (hpath i hi z) (hdrift i hi) hbad
    have hcard : ((bad i).card : ℝ) ≤ (grid.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    have hgrid : (grid.card : ℝ) ≤
        (h : ℝ) * (4 * η + 1 / (h / Nat.gcd h (a i) : ℕ)) :=
      rational_grid_rho_count_le h (a i) hh (y i) η hη
    have hperiodR : (D : ℝ) ^ 2 ≤ (h / Nat.gcd h (a i) : ℕ) := by
      exact_mod_cast (hperiod i hi).le
    have hrec : 1 / ((h / Nat.gcd h (a i) : ℕ) : ℝ) ≤ 1 / (D : ℝ) ^ 2 :=
      one_div_le_one_div_of_le (pow_pos hDpos 2) hperiodR
    exact (hcard.trans hgrid).trans
      (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg h))
  rw [regular_positions_eq_complement]
  exact regular_count_of_coordinate_bounds rotating bad (by positivity) hcount hsmall

theorem long_block_regular_card_at_scale {D h : ℕ} (hh : 0 < h) (hD : 3 ≤ D)
    (rotating : Finset (Fin D)) (Y : Fin h → Fin D → ℝ)
    (y v : Fin D → ℝ) (a : Fin D → ℕ)
    (hpath : ∀ i ∈ rotating, ∀ z, ∃ e : ℤ,
      Y z i - y i - (z.val : ℝ) / h * ((a i : ℝ) + v i) = e)
    (hdrift : ∀ i ∈ rotating, |v i| < 1 / (1000 * (D : ℝ)))
    (hperiod : ∀ i ∈ rotating, D ^ 2 < h / Nat.gcd h (a i)) :
    (h : ℝ) / 2 ≤
      ((Finset.univ.filter fun z => ∀ i ∈ rotating,
        1 / (1000 * (D : ℝ)) ≤ rho (Y z i)).card : ℝ) := by
  exact long_block_regular_card hh (by omega) rotating Y y v a _ (by positivity)
    hpath hdrift hperiod (regular_fraction_constant hD)

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Literal eligibility of a heavy long-period block

The actual interval labels are injective along a primitive short-drift block.
The regular-position count and stationary drift conditions are proved from
the rational grid and adaptive mesh, respectively.
-/

namespace QuantitativeVanDerWaerden

open AnchoredPatterns

/-- Primitive rational motion separates the literal first-coordinate mesh
labels throughout a full block, including all irregular positions. -/
theorem full_block_fullLabel_injective {D h : ℕ}
    (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (R : Realization D)
    (lambda : ℕ) (t : Fin D → Fin h) (hh : 0 < h)
    (hprimitive : PrimitiveVector h (fun i => ((t i).val : ℤ)))
    (hfirst : ∀ i, |R.u i| ≤ 1 / (n : ℝ))
    (hscale : 2 * (h : ℝ) * (1 / (n : ℝ)) < 1) :
    Function.Injective (fullLabel n hn A R lambda t) := by
  intro z w hlabel
  by_contra hne
  have hndvd : ¬ (h : ℤ) ∣ (z.val : ℤ) - w.val := by
    intro hdvd
    have hsmall : |(z.val : ℤ) - w.val| < (h : ℤ) := by
      apply abs_lt.mpr
      constructor <;> omega
    have heq := Int.eq_zero_of_abs_lt_dvd hdvd hsmall
    have hzw : z.val = w.val := by exact_mod_cast sub_eq_zero.mp heq
    exact hne (Fin.ext hzw)
  let X : ℕ → Fin D → ℝ := fun j i =>
    Int.fract (R.x i + (j : ℝ) / h * ((t i).val + R.u i))
  have hpath : ∀ j, j < h → ∀ i, ∃ e : ℤ,
      X j i - R.x i - (j : ℝ) / h *
        ((((t i).val : ℤ) : ℝ) + R.u i) = e := by
    intro j _ i
    refine ⟨-⌊R.x i + (j : ℝ) / h * ((t i).val + R.u i)⌋, ?_⟩
    simp only [X, Int.fract, Int.cast_neg, Int.cast_natCast]
    ring
  have hdrift : ∀ i, (h : ℝ) * |R.u i| ≤ (h : ℝ) * (1 / (n : ℝ)) :=
    fun i => mul_le_mul_of_nonneg_left (hfirst i) (Nat.cast_nonneg h)
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hmargin : 1 / (n : ℝ) + ((h : ℝ) * (1 / (n : ℝ))) / h < 1 / (h : ℝ) := by
    rw [mul_div_cancel_left₀ _ hhR.ne']
    apply (lt_div_iff₀ hhR).mpr
    nlinarith
  obtain ⟨i, hi⟩ := rational_path_coordinate_separation X R.x R.u hh hprimitive
    hpath hdrift hmargin z.isLt w.isLt hndvd
  have hilabel : UniformMesh.label n hn (firstPath R t z i) =
      UniformMesh.label n hn (firstPath R t w i) :=
    congrArg (fun L => L.1 i) hlabel
  have hz := UniformMesh.label_mem n hn (firstPath R t z i)
  have hw := UniformMesh.label_mem n hn (firstPath R t w i)
  rw [← hilabel] at hw
  have hwidth : |X z.val i - X w.val i| ≤ 1 / (n : ℝ) := by
    change |Int.fract (firstPath R t z i) - Int.fract (firstPath R t w i)| ≤ _
    have hinterval :
        (((UniformMesh.label n hn (firstPath R t z i)).val : ℝ) + 1) / n -
          ((UniformMesh.label n hn (firstPath R t z i)).val : ℝ) / n = 1 / (n : ℝ) := by
      ring
    apply abs_le.mpr
    constructor <;> linarith [hz.1, hz.2, hw.1, hw.2]
  exact (not_lt_of_ge hwidth) hi

/-- Every actual block satisfying the return-path bounds and containing a
heavy anchor is eligible for the recorded-pattern family. Neither half-block
regularity, distinct labels, nor stationary widths are assumed. -/
theorem heavy_long_block_eligible {D h : ℕ}
    (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (R : Realization D)
    (lambda : ℕ) (t : Fin D → Fin h) (hh : 0 < h) (hD : 3 ≤ D)
    (hprimitive : PrimitiveVector h (fun i => ((t i).val : ℤ)))
    (hfirst : ∀ i, |R.u i| ≤ 1 / (n : ℝ))
    (hscale : 2 * (h : ℝ) * (1 / (n : ℝ)) < 1)
    (hrotating : ∀ i, ¬ stationary lambda t i → |R.v i| ≤ A.H)
    (hnear : ∀ i, ¬ stationary lambda t i → |R.v i| < 1 / (1000 * (D : ℝ)))
    (hperiod : ∀ i, ¬ stationary lambda t i →
      D ^ 2 < h / Nat.gcd h (lambda * (t i).val))
    (anchor : Fin h) (M k : ℝ) (hsmall : 2 * M / k ≤ 1 / 16)
    (hheavy : ∀ i, stationary lambda t i → |R.v i| ≤
      (2 * M / k) * A.width (A.meshLabel (secondPath R lambda t anchor i))) :
    EligibleRealization n hn A (1 / (1000 * (D : ℝ))) lambda t R := by
  classical
  let rotating : Finset (Fin D) := Finset.univ.filter fun i => ¬ stationary lambda t i
  have hregular := long_block_regular_card_at_scale hh hD rotating
    (fun z i => secondPath R lambda t z i) R.y R.v
    (fun i => lambda * (t i).val)
    (by
      intro i _ z
      refine ⟨0, ?_⟩
      simp only [secondPath, Nat.cast_mul, Int.cast_zero]
      ring)
    (by intro i hi; exact hnear i (Finset.mem_filter.mp hi).2)
    (by intro i hi; exact hperiod i (Finset.mem_filter.mp hi).2)
  have hregular' : (h : ℝ) / 2 ≤
      ((regularPositions (1 / (1000 * (D : ℝ))) R lambda t).card : ℝ) := by
    have hpositions : regularPositions (1 / (1000 * (D : ℝ))) R lambda t =
        Finset.univ.filter (fun z : Fin h => ∀ i ∈ rotating,
          1 / (1000 * (D : ℝ)) ≤ rho (secondPath R lambda t z i)) := by
      ext z
      simp [regularPositions, regular, rotating]
    rw [hpositions]
    exact hregular
  refine ⟨?_, ?_, hfirst, hrotating, ?_⟩
  · have hr : (h : ℝ) ≤ 2 *
        ((regularPositions (1 / (1000 * (D : ℝ))) R lambda t).card : ℝ) := by
      linarith
    exact_mod_cast hr
  · intro z w _ _ heq
    exact full_block_fullLabel_injective n hn A R lambda t hh hprimitive hfirst hscale heq
  · intro i hi z _
    have hstationary : (h : ℤ) ∣ ((lambda * (t i).val : ℕ) : ℤ) := by
      exact_mod_cast hi
    apply stationary_full_block_width A (fun z => secondPath R lambda t z i)
      hh hstationary (y := R.y i) (v := R.v i) ?_ anchor ?_ z
    · intro w
      refine ⟨0, ?_⟩
      simp only [secondPath, Nat.cast_mul, Int.cast_natCast, Int.cast_mul, Int.cast_zero]
      ring
    · exact stationary_relative_width_threshold
        (A.width_pos (A.meshLabel (secondPath R lambda t anchor i))).le hsmall (hheavy i hi)

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Coverage by full blocks containing a heavy position

The `b`th full block consists literally of positions `b * h + z`, for `z < h`.
Every full block that is not used consists of light positions. Counting the
disjoint full blocks and the final remainder transfers bounds within used
blocks to counts in the entire interval.
-/

open scoped BigOperators

namespace QuantitativeVanDerWaerden.BlockCoverage

/-- Position `z` in full block `b`. -/
def blockIndex (k h : ℕ) (b : Fin (k / h)) (z : Fin h) : Fin k :=
  ⟨b.val * h + z.val, by
    calc
      b.val * h + z.val < b.val * h + h := Nat.add_lt_add_left z.isLt _
      _ = b.val.succ * h := (Nat.succ_mul _ _).symm
      _ ≤ (k / h) * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt b.isLt)
      _ ≤ k := Nat.div_mul_le_self k h⟩

@[simp]
theorem blockIndex_val (k h : ℕ) (b : Fin (k / h)) (z : Fin h) :
    (blockIndex k h b z).val = b.val * h + z.val := rfl

theorem blockIndex_div (k h : ℕ) (hh : 0 < h)
    (b : Fin (k / h)) (z : Fin h) :
    (blockIndex k h b z).val / h = b.val := by
  change (b.val * h + z.val) / h = b.val
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hh,
    Nat.div_eq_of_lt z.isLt, Nat.zero_add]

theorem blockIndex_injective (k h : ℕ) (b : Fin (k / h)) :
    Function.Injective (blockIndex k h b) := by
  intro z w heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  exact Nat.add_left_cancel hv

def blockPositions (k h : ℕ) (b : Fin (k / h)) : Finset (Fin k) :=
  Finset.univ.image (blockIndex k h b)

@[simp]
theorem card_blockPositions (k h : ℕ) (b : Fin (k / h)) :
    (blockPositions k h b).card = h := by
  rw [blockPositions, Finset.card_image_of_injective _ (blockIndex_injective k h b)]
  simp

theorem blockPositions_disjoint (k h : ℕ) (hh : 0 < h)
    {b c : Fin (k / h)} (hbc : b ≠ c) :
    Disjoint (blockPositions k h b) (blockPositions k h c) := by
  refine Finset.disjoint_left.mpr ?_
  intro p hp hq
  obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hp
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hq
  have hv := congrArg (fun p : Fin k => p.val / h) (hz.trans hw.symm)
  change (blockIndex k h b z).val / h = (blockIndex k h c w).val / h at hv
  rw [blockIndex_div k h hh, blockIndex_div k h hh] at hv
  exact hbc (Fin.ext hv)

def blockUnion (k h : ℕ) (B : Finset (Fin (k / h))) : Finset (Fin k) :=
  B.biUnion (blockPositions k h)

theorem blockUnion_mono (k h : ℕ) {B C : Finset (Fin (k / h))} (hBC : B ⊆ C) :
    blockUnion k h B ⊆ blockUnion k h C := by
  intro p hp
  obtain ⟨b, hb, hp⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr ⟨b, hBC hb, hp⟩

theorem card_blockUnion (k h : ℕ) (hh : 0 < h) (B : Finset (Fin (k / h))) :
    (blockUnion k h B).card = B.card * h := by
  unfold blockUnion
  rw [Finset.card_biUnion (fun b _ c _ hbc => blockPositions_disjoint k h hh hbc)]
  exact Finset.sum_const_nat fun b _ => card_blockPositions k h b

def usedBlocks (k h : ℕ) (heavy : Fin k → Prop) [DecidablePred heavy] :
    Finset (Fin (k / h)) :=
  Finset.univ.filter fun b => ∃ z : Fin h, heavy (blockIndex k h b z)

@[simp]
theorem mem_usedBlocks (k h : ℕ) (heavy : Fin k → Prop) [DecidablePred heavy]
    (b : Fin (k / h)) :
    b ∈ usedBlocks k h heavy ↔ ∃ z : Fin h, heavy (blockIndex k h b z) := by
  simp [usedBlocks]

def lightPositions {k : ℕ} (heavy : Fin k → Prop) [DecidablePred heavy] :
    Finset (Fin k) :=
  Finset.univ.filter fun p => ¬ heavy p

def lightCount {k : ℕ} (heavy : Fin k → Prop) [DecidablePred heavy] : ℕ :=
  (lightPositions heavy).card

/-- Every full-block position not covered by a used block is light. -/
theorem unused_full_positions_light (k h : ℕ) (heavy : Fin k → Prop)
    [DecidablePred heavy] :
    blockUnion k h Finset.univ \ blockUnion k h (usedBlocks k h heavy) ⊆
      lightPositions heavy := by
  intro p hp
  obtain ⟨hfull, hnot⟩ := Finset.mem_sdiff.mp hp
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro hpheavy
  obtain ⟨b, _, hpb⟩ := Finset.mem_biUnion.mp hfull
  obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hpb
  have hb : b ∈ usedBlocks k h heavy := by
    apply (mem_usedBlocks k h heavy b).mpr
    refine ⟨z, ?_⟩
    rw [hz]
    exact hpheavy
  exact hnot (Finset.mem_biUnion.mpr ⟨b, hb, hpb⟩)

theorem full_positions_le_light_add_used (k h : ℕ) (hh : 0 < h)
    (heavy : Fin k → Prop) [DecidablePred heavy] :
    (k / h) * h ≤ lightCount heavy + (usedBlocks k h heavy).card * h := by
  have hsub := blockUnion_mono k h (Finset.subset_univ (usedBlocks k h heavy))
  have hpart := Finset.card_sdiff_add_card_eq_card hsub
  have hlight := Finset.card_le_card (unused_full_positions_light k h heavy)
  have hfull : (blockUnion k h Finset.univ).card = (k / h) * h := by
    simpa using card_blockUnion k h hh Finset.univ
  have hused := card_blockUnion k h hh (usedBlocks k h heavy)
  unfold lightCount
  omega

/-- The final remainder has fewer than `h` positions, and unused full blocks
are charged to individual light positions. -/
theorem usedBlocks_mul_lower (k h : ℕ) (hh : 0 < h)
    (heavy : Fin k → Prop) [DecidablePred heavy] :
    (k : ℝ) - (h : ℝ) - (lightCount heavy : ℝ) ≤
      ((usedBlocks k h heavy).card : ℝ) * (h : ℝ) := by
  have hfull := full_positions_le_light_add_used k h hh heavy
  have hrem := Nat.mod_lt k hh
  have hdiv := Nat.div_add_mod' k h
  have hn : k ≤ h + lightCount heavy + (usedBlocks k h heavy).card * h := by omega
  have hr : (k : ℝ) ≤ (h : ℝ) + (lightCount heavy : ℝ) +
      ((usedBlocks k h heavy).card : ℝ) * (h : ℝ) := by exact_mod_cast hn
  linarith

theorem usedPositions_lower (k h : ℕ) (hh : 0 < h)
    (heavy : Fin k → Prop) [DecidablePred heavy] :
    (k : ℝ) - (h : ℝ) - (lightCount heavy : ℝ) ≤
      ((blockUnion k h (usedBlocks k h heavy)).card : ℝ) := by
  rw [card_blockUnion k h hh, Nat.cast_mul]
  exact usedBlocks_mul_lower k h hh heavy

def blockColorCount (k h : ℕ) (color : Fin k → Bool) (c : Bool)
    (b : Fin (k / h)) : ℕ :=
  ((blockPositions k h b).filter fun p => color p = c).card

def colorCount {k : ℕ} (color : Fin k → Bool) (c : Bool) : ℕ :=
  (Finset.univ.filter fun p => color p = c).card

/-- Counts in any collection of distinct full blocks sum to at most the
corresponding count in the whole interval. -/
theorem sum_blockColorCount_le (k h : ℕ) (hh : 0 < h)
    (B : Finset (Fin (k / h))) (color : Fin k → Bool) (c : Bool) :
    (∑ b ∈ B, blockColorCount k h color c b) ≤ colorCount color c := by
  let sets := fun b => (blockPositions k h b).filter fun p => color p = c
  have hdisj : (B : Set (Fin (k / h))).PairwiseDisjoint sets := by
    intro b _ d _ hbd
    exact (blockPositions_disjoint k h hh hbd).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsub : B.biUnion sets ⊆ Finset.univ.filter (fun p => color p = c) := by
    intro p hp
    obtain ⟨b, _, hp⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj] at hcard
  exact hcard

/-- If every used full block contains at least `h/8` positions of a specified
color, that color occupies at least `(k-h-lightCount)/8` positions globally. -/
theorem colorCount_lower (k h : ℕ) (hh : 0 < h)
    (heavy : Fin k → Prop) [DecidablePred heavy]
    (color : Fin k → Bool) (c : Bool)
    (hblocks : ∀ b ∈ usedBlocks k h heavy,
      (h : ℝ) / 8 ≤ (blockColorCount k h color c b : ℝ)) :
    ((k : ℝ) - (h : ℝ) - (lightCount heavy : ℝ)) / 8 ≤
      (colorCount color c : ℝ) := by
  have hsum : ((usedBlocks k h heavy).card : ℝ) * ((h : ℝ) / 8) ≤
      ∑ b ∈ usedBlocks k h heavy, (blockColorCount k h color c b : ℝ) := by
    calc
      _ = ∑ _b ∈ usedBlocks k h heavy, (h : ℝ) / 8 := by simp
      _ ≤ _ := Finset.sum_le_sum hblocks
  have hupper : (∑ b ∈ usedBlocks k h heavy, (blockColorCount k h color c b : ℝ)) ≤
      (colorCount color c : ℝ) := by
    exact_mod_cast sum_blockColorCount_le k h hh (usedBlocks k h heavy) color c
  have hcoverage := usedBlocks_mul_lower k h hh heavy
  linarith

/-- The one-tenth light-position and block-size bounds give the desired
one-tenth global count for each color. -/
theorem colorCount_tenth (k h : ℕ) (hh : 0 < h)
    (heavy : Fin k → Prop) [DecidablePred heavy]
    (color : Fin k → Bool)
    (hlight : (lightCount heavy : ℝ) ≤ (k : ℝ) / 10)
    (hsmall : (h : ℝ) ≤ (k : ℝ) / 10)
    (hblocks : ∀ b ∈ usedBlocks k h heavy, ∀ c : Bool,
      (h : ℝ) / 8 ≤ (blockColorCount k h color c b : ℝ)) :
    ∀ c : Bool, (k : ℝ) / 10 ≤ (colorCount color c : ℝ) := by
  intro c
  have hglobal := colorCount_lower k h hh heavy color c (fun b hb => hblocks b hb c)
  linarith

end QuantitativeVanDerWaerden.BlockCoverage

end OAI
end
end

section
section
namespace OAI

/-!
# Literal cyclic labels on full blocks

An actual cyclic progression is re-anchored at each full block's initial
position. Its two rational paths differ from the local realization only by
integers, so the literal uniform and adaptive labels agree exactly.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.CyclicBlockLabels

theorem fullBlock_end_le (k h : ℕ) (b : Fin (k / h)) : b.val * h + h ≤ k := by
  calc
    b.val * h + h = b.val.succ * h := (Nat.succ_mul _ _).symm
    _ ≤ (k / h) * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt b.isLt)
    _ ≤ k := Nat.div_mul_le_self k h

/-- The actual cyclic representatives at the beginning of a full block,
with the original displacement vectors retained. -/
def cyclicBlockRealization (q D lambda k h : ℕ)
    (a d : CyclicGroup q D) (u v : Fin D → ℝ) (b : Fin (k / h)) :
    AnchoredPatterns.Realization D where
  x := xRep q D (a + (b.val * h) • d)
  y := yRep q D lambda (a + (b.val * h) • d)
  u := u
  v := v

theorem xRep_block_integer_difference (q D lambda k h : ℕ) (hh : 0 < h)
    (a d : CyclicGroup q D) (u v : Fin D → ℝ) (t : Fin D → Fin h)
    (hX : ∀ j, j < k → ∀ i : Fin D, ∃ e : ℤ,
      xRep q D (a + j • d) i - xRep q D a i -
        (j : ℝ) / h * ((t i).val + u i) = e)
    (b : Fin (k / h)) (z : Fin h) (i : Fin D) :
    ∃ e : ℤ,
      xRep q D (a + (BlockCoverage.blockIndex k h b z).val • d) i -
        AnchoredPatterns.firstPath (cyclicBlockRealization q D lambda k h a d u v b)
          t z i = e := by
  obtain ⟨e, he⟩ := rational_full_block_reanchor
    (k := k) (h := h) (j₀ := b.val * h) (a := ((t i).val : ℤ))
    (y := xRep q D a i) (v := u i)
    (fun j => xRep q D (a + j • d) i) hh (fullBlock_end_le k h b)
    (by
      intro j hj
      simpa only [Int.cast_natCast] using hX j hj i) z
  refine ⟨e, ?_⟩
  simpa only [BlockCoverage.blockIndex_val, AnchoredPatterns.firstPath,
    cyclicBlockRealization, Int.cast_natCast, sub_add_eq_sub_sub] using he

theorem yRep_block_integer_difference (q D lambda k h : ℕ) (hh : 0 < h)
    (a d : CyclicGroup q D) (u v : Fin D → ℝ) (t : Fin D → Fin h)
    (hY : ∀ j, j < k → ∀ i : Fin D, ∃ e : ℤ,
      yRep q D lambda (a + j • d) i - yRep q D lambda a i -
        (j : ℝ) / h * ((lambda : ℝ) * (t i).val + v i) = e)
    (b : Fin (k / h)) (z : Fin h) (i : Fin D) :
    ∃ e : ℤ,
      yRep q D lambda (a + (BlockCoverage.blockIndex k h b z).val • d) i -
        AnchoredPatterns.secondPath (cyclicBlockRealization q D lambda k h a d u v b)
          lambda t z i = e := by
  obtain ⟨e, he⟩ := rational_full_block_reanchor
    (k := k) (h := h) (j₀ := b.val * h)
    (a := (lambda : ℤ) * ((t i).val : ℤ))
    (y := yRep q D lambda a i) (v := v i)
    (fun j => yRep q D lambda (a + j • d) i) hh (fullBlock_end_le k h b)
    (by
      intro j hj
      simpa only [Int.cast_mul, Int.cast_natCast] using hY j hj i) z
  refine ⟨e, ?_⟩
  simpa only [BlockCoverage.blockIndex_val, AnchoredPatterns.secondPath,
    cyclicBlockRealization, Int.cast_mul, Int.cast_natCast, sub_add_eq_sub_sub] using he

/-- The canonical literal cyclic label is exactly the full label of the
local block realization, including every mesh boundary. -/
theorem literalFullLabel_block_eq (mesh : AdaptiveMesh)
    (q D lambda meshN k h : ℕ) (hn : 0 < meshN) (hh : 0 < h)
    (a d : CyclicGroup q D) (u v : Fin D → ℝ) (t : Fin D → Fin h)
    (hX : ∀ j, j < k → ∀ i : Fin D, ∃ e : ℤ,
      xRep q D (a + j • d) i - xRep q D a i -
        (j : ℝ) / h * ((t i).val + u i) = e)
    (hY : ∀ j, j < k → ∀ i : Fin D, ∃ e : ℤ,
      yRep q D lambda (a + j • d) i - yRep q D lambda a i -
        (j : ℝ) / h * ((lambda : ℝ) * (t i).val + v i) = e)
    (b : Fin (k / h)) (z : Fin h) :
    literalFullLabel mesh q D lambda meshN hn
        (a + (BlockCoverage.blockIndex k h b z).val • d) =
      AnchoredPatterns.fullLabel meshN hn mesh
        (cyclicBlockRealization q D lambda k h a d u v b) lambda t z := by
  apply Prod.ext
  · funext i
    exact UniformMesh.label_eq_of_integer_difference meshN hn _ _
      (xRep_block_integer_difference q D lambda k h hh a d u v t hX b z i)
  · funext i
    obtain ⟨e, he⟩ := yRep_block_integer_difference q D lambda k h hh
      a d u v t hY b z i
    have heq : yRep q D lambda (a + (BlockCoverage.blockIndex k h b z).val • d) i =
        AnchoredPatterns.secondPath (cyclicBlockRealization q D lambda k h a d u v b)
          lambda t z i + e := by linarith
    change mesh.meshLabel (yRep q D lambda
      (a + (BlockCoverage.blockIndex k h b z).val • d) i) = _
    rw [heq]
    exact mesh.meshLabel_add_int _ _

/-- Counting a color in the literal positions of a full block is the same
as counting its pullback to the local indices `Fin h`. -/
theorem blockColorCount_eq_local (k h : ℕ)
    (color : Fin k → Bool) (c : Bool) (b : Fin (k / h)) :
    BlockCoverage.blockColorCount k h color c b =
      (Finset.univ.filter fun z : Fin h =>
        color (BlockCoverage.blockIndex k h b z) = c).card := by
  unfold BlockCoverage.blockColorCount BlockCoverage.blockPositions
  rw [Finset.filter_image]
  exact Finset.card_image_of_injective _ (BlockCoverage.blockIndex_injective k h b)

end QuantitativeVanDerWaerden.CyclicBlockLabels

end

end OAI
end
end

section
section
namespace OAI

/-! The long-period case for the coloring pulled back from the actual
two-system full labels of the cyclic progression. -/

namespace QuantitativeVanDerWaerden

open AnchoredPatterns
open scoped Classical

/-- Heavy positions are defined by their literal full-label multiplicity in
the entire progression, rather than within an individual block. -/
noncomputable def literalProgressionHeavy
    (mesh : AdaptiveMesh) (q D lambda n k : ℕ) (hn : 0 < n)
    (a d : CyclicGroup q D) (M : ℝ) (j : Fin k) : Prop := by
  classical
  exact (k : ℝ) / M <
    ((Finset.univ.filter fun l : Fin k =>
      literalFullLabel mesh q D lambda n hn (a + l.val • d) =
        literalFullLabel mesh q D lambda n hn (a + j.val • d)).card : ℝ)

/-- Quarter-balance on at least half the positions gives an eighth of the
whole block. The restriction to regular positions is removed by inclusion. -/
theorem block_color_count_of_regular_balance {h : ℕ}
    (S : Finset (Fin h)) (color : Fin h → Bool) (c : Bool)
    (hmany : h ≤ 2 * S.card)
    (hbalanced : S.card ≤ 4 * (S.filter fun z => color z = c).card) :
    (h : ℝ) / 8 ≤ ((Finset.univ.filter fun z => color z = c).card : ℝ) := by
  have hsub : S.filter (fun z => color z = c) ⊆
      Finset.univ.filter (fun z => color z = c) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, (Finset.mem_filter.mp hz).2⟩
  have hcard := Finset.card_le_card hsub
  have hn : h ≤ 8 * (Finset.univ.filter fun z => color z = c).card := by omega
  have hr : (h : ℝ) ≤ 8 * ((Finset.univ.filter fun z => color z = c).card : ℝ) := by
    exact_mod_cast hn
  linarith

/-- The long-period case of the dichotomy for the actual cyclic pullback
coloring. Half-block regularity and eligibility are proved by the preceding
grid and mesh lemmas. Full blocks are counted through literal indices. -/
theorem literal_long_period_balanced
    (mesh : AdaptiveMesh) (q D lambda n k h : ℕ) (hn : 0 < n)
    (a d : CyclicGroup q D) (M : ℝ) (u v : Fin D → ℝ)
    (t : Fin D → Fin h) (hh : 0 < h) (hD : 3 ≤ D)
    (cstar : FullLabel D (Fin n) mesh.Label → Bool)
    (hprimitive : PrimitiveVector h (fun i => ((t i).val : ℤ)))
    (hX : ∀ j, j < k → ∀ i : Fin D, ∃ e : ℤ,
      xRep q D (a + j • d) i - xRep q D a i -
        (j : ℝ) / h * ((t i).val + u i) = e)
    (hY : ∀ j, j < k → ∀ i : Fin D, ∃ e : ℤ,
      yRep q D lambda (a + j • d) i - yRep q D lambda a i -
        (j : ℝ) / h * ((lambda : ℝ) * (t i).val + v i) = e)
    (hfirst : ∀ i, |u i| ≤ 1 / (n : ℝ))
    (hscale : 2 * (h : ℝ) * (1 / (n : ℝ)) < 1)
    (hrotating : ∀ i, ¬ stationary lambda t i → |v i| ≤ mesh.H)
    (hnear : ∀ i, ¬ stationary lambda t i → |v i| < 1 / (1000 * (D : ℝ)))
    (hperiod : ∀ i, ¬ stationary lambda t i →
      D ^ 2 < h / Nat.gcd h (lambda * (t i).val))
    (hcoef : 2 * M / (k : ℝ) ≤ 1 / 16)
    (hheavy : ∀ j : Fin k, literalProgressionHeavy mesh q D lambda n k hn a d M j →
      ∀ i, |v i| ≤ (2 * M / (k : ℝ)) *
        mesh.width (mesh.meshLabel (yRep q D lambda (a + j.val • d) i)))
    (hlight : (BlockCoverage.lightCount
      (literalProgressionHeavy mesh q D lambda n k hn a d M) : ℝ) ≤ (k : ℝ) / 10)
    (hblocksmall : (h : ℝ) ≤ (k : ℝ) / 10)
    (hbalance : ∀ R : Realization D,
      EligibleRealization n hn mesh (1 / (1000 * (D : ℝ))) lambda t R → ∀ c : Bool,
      (regularPositions (1 / (1000 * (D : ℝ))) R lambda t).card ≤
        4 * ((regularPositions (1 / (1000 * (D : ℝ))) R lambda t).filter
          fun z => cstar (fullLabel n hn mesh R lambda t z) = c).card) :
    ∀ c : Bool, (k : ℝ) / 100 ≤
      ((Finset.univ.filter fun j : Fin k =>
        cstar (literalFullLabel mesh q D lambda n hn (a + j.val • d)) = c).card : ℝ) := by
  classical
  let heavy := literalProgressionHeavy mesh q D lambda n k hn a d M
  let color : Fin k → Bool := fun j =>
    cstar (literalFullLabel mesh q D lambda n hn (a + j.val • d))
  have hblocks : ∀ b ∈ BlockCoverage.usedBlocks k h heavy, ∀ c : Bool,
      (h : ℝ) / 8 ≤ (BlockCoverage.blockColorCount k h color c b : ℝ) := by
    intro b hb c
    obtain ⟨anchor, hanchor⟩ := (BlockCoverage.mem_usedBlocks k h heavy b).mp hb
    let R := CyclicBlockLabels.cyclicBlockRealization q D lambda k h a d u v b
    have hlabels : ∀ z : Fin h,
        literalFullLabel mesh q D lambda n hn
          (a + (BlockCoverage.blockIndex k h b z).val • d) =
        fullLabel n hn mesh R lambda t z :=
      fun z => CyclicBlockLabels.literalFullLabel_block_eq mesh q D lambda n k h hn hh
        a d u v t hX hY b z
    have hanchorWidth : ∀ i, stationary lambda t i → |R.v i| ≤
        (2 * M / (k : ℝ)) *
          mesh.width (mesh.meshLabel (secondPath R lambda t anchor i)) := by
      intro i _
      have hi : mesh.meshLabel
          (yRep q D lambda (a + (BlockCoverage.blockIndex k h b anchor).val • d) i) =
          mesh.meshLabel (secondPath R lambda t anchor i) :=
        congrArg (fun L => L.2 i) (hlabels anchor)
      rw [← hi]
      exact hheavy (BlockCoverage.blockIndex k h b anchor) hanchor i
    have heligible : EligibleRealization n hn mesh (1 / (1000 * (D : ℝ))) lambda t R :=
      heavy_long_block_eligible n hn mesh R lambda t hh hD hprimitive hfirst hscale
        hrotating hnear hperiod anchor M (k : ℝ) hcoef hanchorWidth
    have hlocal := block_color_count_of_regular_balance
      (regularPositions (1 / (1000 * (D : ℝ))) R lambda t)
      (fun z => cstar (fullLabel n hn mesh R lambda t z)) c
      heligible.regular_many (hbalance R heligible c)
    have hsets :
        (Finset.univ.filter fun z : Fin h => color (BlockCoverage.blockIndex k h b z) = c) =
        Finset.univ.filter (fun z : Fin h => cstar (fullLabel n hn mesh R lambda t z) = c) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (cstar (literalFullLabel mesh q D lambda n hn
        (a + (BlockCoverage.blockIndex k h b z).val • d)) = c) ↔ _
      rw [hlabels z]
    rw [CyclicBlockLabels.blockColorCount_eq_local, hsets]
    exact hlocal
  have hglobal := BlockCoverage.colorCount_tenth k h hh heavy color hlight hblocksmall hblocks
  intro c
  have hc := hglobal c
  change (k : ℝ) / 100 ≤ (BlockCoverage.colorCount color c : ℝ)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Heavy and light positions in the actual construction

The real-valued heavy threshold used in the block argument and the integer
light threshold used in the outer word tests classify exactly the same
positions. Both multiplicities count the entire literal progression word.
-/

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters
open scoped Classical

theorem real_heavy_iff (k M m : ℕ) (hM : 0 < M) :
    (k : ℝ) / (M : ℝ) < (m : ℝ) ↔ k < M * m := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [div_lt_iff₀ hM', mul_comm]
  norm_cast

theorem not_real_heavy_iff (k M m : ℕ) (hM : 0 < M) :
    ¬ ((k : ℝ) / (M : ℝ) < (m : ℝ)) ↔ M * m ≤ k := by
  rw [real_heavy_iff k M m hM, not_lt]

variable {k : ℕ}

theorem literalProgressionHeavy_iff_word_heavy (s : Data k) (hk : 3 ≤ k)
    (a d : Group s) (j : Fin k) :
    literalProgressionHeavy (mesh s hk) s.q (dimension k) (lambda k)
      (uniformCount k) k (uniformCount_pos hk) a d (cutoff k) j ↔
    k < cutoff k * OuterWordTests.multiplicity (fullLabelWord s hk (a, d))
      (fullLabelWord s hk (a, d) j) := by
  unfold literalProgressionHeavy
  rw [real_heavy_iff k (cutoff k) _ (cutoff_pos (by omega : 1 ≤ k))]
  unfold OuterWordTests.multiplicity
  apply Iff.of_eq
  apply congrArg (fun n : ℕ => k < cutoff k * n)
  apply congrArg (Finset.card : Finset (Fin k) → ℕ)
  apply Finset.ext
  intro i
  constructor
  · intro hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [fullLabelWord, fullLabel, nsmul_eq_mul] using (Finset.mem_filter.mp hi).2
  · intro hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [fullLabelWord, fullLabel, nsmul_eq_mul] using (Finset.mem_filter.mp hi).2

/-- The two literal finite sets of light positions agree. -/
theorem selected_lightPositions_eq (s : Data k) (hk : 3 ≤ k) (a d : Group s) :
    BlockCoverage.lightPositions
      (literalProgressionHeavy (mesh s hk) s.q (dimension k) (lambda k)
        (uniformCount k) k (uniformCount_pos hk) a d (cutoff k)) =
      OuterWordTests.lightPositions (cutoff k) (fullLabelWord s hk (a, d)) := by
  ext j
  simp only [BlockCoverage.lightPositions, Finset.mem_filter, Finset.mem_univ,
    true_and, OuterWordTests.mem_lightPositions,
    literalProgressionHeavy_iff_word_heavy, not_lt]

/-- The block-coverage light count is exactly the outer-test light count. -/
theorem selected_lightCount_eq (s : Data k) (hk : 3 ≤ k) (a d : Group s) :
    BlockCoverage.lightCount
      (literalProgressionHeavy (mesh s hk) s.q (dimension k) (lambda k)
        (uniformCount k) k (uniformCount_pos hk) a d (cutoff k)) =
      (OuterWordTests.lightPositions (cutoff k) (fullLabelWord s hk (a, d))).card := by
  unfold BlockCoverage.lightCount
  rw [selected_lightPositions_eq]

/-- Failure of the many-light-positions branch supplies the real light-count
bound required by the long-period coloring theorem. -/
theorem selected_lightCount_le_of_few (s : Data k) (hk : 3 ≤ k) (a d : Group s)
    (hfew : ¬ k ≤ 10 *
      (OuterWordTests.lightPositions (cutoff k) (fullLabelWord s hk (a, d))).card) :
    (BlockCoverage.lightCount
      (literalProgressionHeavy (mesh s hk) s.q (dimension k) (lambda k)
        (uniformCount k) k (uniformCount_pos hk) a d (cutoff k)) : ℝ) ≤
      (k : ℝ) / 10 := by
  rw [selected_lightCount_eq]
  have hn : 10 *
      (OuterWordTests.lightPositions (cutoff k) (fullLabelWord s hk (a, d))).card < k :=
    Nat.lt_of_not_ge hfew
  have hr : (10 : ℝ) *
      ((OuterWordTests.lightPositions (cutoff k) (fullLabelWord s hk (a, d))).card : ℝ) <
      (k : ℝ) := by exact_mod_cast hn
  linarith

end QuantitativeVanDerWaerden.ConstructionModel

end OAI
end
end

section
section
namespace OAI

/-!
# Every label lies in one residue class of the closest return

The primitive rational path of an actual heavy-label return separates distinct
residues even after its small real drift. The literal uniform interval width
therefore forces every full-label fiber, including all other heavy fibers, to
lie in a single residue class of this same denominator.
-/

namespace QuantitativeVanDerWaerden.IsHeavyLabelReturn

variable {mesh : AdaptiveMesh} {q D lam Ucount k M j h : ℕ} {hU : 0 < Ucount}
  {a d : CyclicGroup q D} {beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)}
  (R : IsHeavyLabelReturn mesh q D lam Ucount k M hU a d beta j h)

include R

/-- One actual closest return supplies the common residue-class property for
every literal full label on the progression. -/
theorem same_label_divides (hq : 0 < q)
    (hwidth : 1 / (Ucount : ℝ) ≤ mesh.H)
    (hsmall : 4 * (M : ℝ) * mesh.H < 1) :
    ∀ m, m < k → ∀ n, n < k →
      literalFullLabel mesh q D lam Ucount hU (a + m • d) =
        literalFullLabel mesh q D lam Ucount hU (a + n • d) →
      (h : ℤ) ∣ (n : ℤ) - m := by
  obtain ⟨t, _, hp, hx, _⟩ := R.primitive_return_path hq
  have hk : 0 < k := by have := R.end_lt; omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hperiod : (h : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast R.gap_le
  have hmargin := return_separation_margin R.gap_pos hperiod
    (by positivity : (0 : ℝ) ≤ 1 / (Ucount : ℝ)) hwidth hsmall
  have hdrift (i : Fin D) : (k : ℝ) *
      |xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i| ≤
      2 * (M : ℝ) * (1 / (Ucount : ℝ)) := by
    have hr := (le_div_iff₀ hkR).mp (R.x_rate i)
    simpa only [mul_comm] using hr
  intro m hm n hn heq
  exact same_label_divisible_index_difference
    (fun z => xRep q D (a + z • d)) (xRep q D a)
    (fun i => xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i)
    (fun z => literalFullLabel mesh q D lam Ucount hU (a + z • d))
    R.gap_pos hp (fun z _ i => hx z i) hdrift hmargin
    (fun z _ w _ hzw i => literalFullLabel_same_first_distance
      mesh q D lam Ucount hU hzw i) hn hm heq.symm

end QuantitativeVanDerWaerden.IsHeavyLabelReturn

end OAI
end
end

section
section
namespace OAI

namespace QuantitativeVanDerWaerden

/-- The endpoints of a residue fiber of size at least two differ by a positive
number of denominator steps, at least one for each intervening index. -/
theorem residue_fiber_span (J : Finset ℕ) (hJ : J.Nonempty) {h k : ℕ}
    (hh : 0 < h) (hcard : 2 ≤ J.card)
    (hcongr : ∀ a ∈ J, ∀ b ∈ J, (h : ℤ) ∣ (b : ℤ) - (a : ℤ))
    (hbound : ∀ j ∈ J, j < k) :
    ∃ c : ℕ, 0 < c ∧ J.card - 1 ≤ c ∧
      J.max' hJ - J.min' hJ = c * h ∧ c * h < k := by
  have hdiv : ∀ a ∈ J, ∀ b ∈ J, a ≤ b → h ∣ b - a := by
    intro a ha b hb hab
    apply Int.natCast_dvd_natCast.mp
    simpa only [Int.natCast_sub hab] using hcongr a ha b hb
  have hgap : ∀ a ∈ J, ∀ b ∈ J, a < b → h ≤ b - a := by
    intro a ha b hb hab
    exact Nat.le_of_dvd (Nat.sub_pos_of_lt hab) (hdiv a ha b hb hab.le)
  have hpacking := gap_mul_card_sub_one_le_span J hJ h hgap
  have hminmax : J.min' hJ ≤ J.max' hJ := J.min'_le _ (J.max'_mem hJ)
  obtain ⟨c, hc⟩ := hdiv _ (J.min'_mem hJ) _ (J.max'_mem hJ) hminmax
  have hcardc : J.card - 1 ≤ c := Nat.le_of_mul_le_mul_left (by rwa [hc] at hpacking) hh
  have hspan : J.max' hJ - J.min' hJ = c * h := hc.trans (Nat.mul_comm h c)
  refine ⟨c, by omega, hcardc, hspan, ?_⟩
  rw [← hspan]
  exact lt_of_le_of_lt (Nat.sub_le _ _) (hbound _ (J.max'_mem hJ))

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Drift relative to every heavy label interval

All occurrences of a label are in one residue class modulo the primitive
return denominator. Packing these actual occurrence indices gives at least
`card - 1` periods between the extreme visits. Their representatives alone
then determine the real accumulated drift: the integral discrepancy is too
small to be nonzero. No assertion about the path between the visits is used.
-/


namespace QuantitativeVanDerWaerden

/-- At indices differing by `c` denominator periods, the rational numerator
disappears modulo integers and only `c` times the drift remains. -/
theorem rational_path_period_difference {ι : Type uIndex} {h a b c : ℕ}
    (Y : ℕ → ι → ℝ) (A v : ι → ℝ) (s : ι → ℤ)
    (hh : 0 < h) (hab : a ≤ b) (hspan : b - a = c * h)
    (hpath : ∀ n i, ∃ z : ℤ,
      Y n i - A i - (n : ℝ) / h * ((s i : ℝ) + v i) = z) (i : ι) :
    ∃ z : ℤ, (Y b i - Y a i) - (c : ℝ) * v i = z := by
  obtain ⟨za, hza⟩ := hpath a i
  obtain ⟨zb, hzb⟩ := hpath b i
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hspanR : (b : ℝ) - a = (c : ℝ) * h := by
    have hs : ((b - a : ℕ) : ℝ) = (c : ℝ) * h := by exact_mod_cast hspan
    simpa only [Nat.cast_sub hab] using hs
  have hquot : (b : ℝ) / h - (a : ℝ) / h = c := by
    rw [← sub_div, hspanR, mul_div_cancel_right₀ _ hhR]
  have hscale : (b : ℝ) / h * ((s i : ℝ) + v i) -
      (a : ℝ) / h * ((s i : ℝ) + v i) = (c : ℝ) * ((s i : ℝ) + v i) := by
    rw [← sub_mul, hquot]
  refine ⟨(c : ℤ) * s i + zb - za, ?_⟩
  push_cast
  nlinarith

/-- A heavy set of occurrences in one residue class controls the common drift
by the actual width of every one of its coordinate intervals. -/
theorem heavy_fiber_relative_width {ι : Type uIndex} {J : Finset ℕ} {k h : ℕ}
    {M H : ℝ} (Y : ℕ → ι → ℝ) (A v L : ι → ℝ) (s : ι → ℤ)
    (hM : 0 < M) (hscale : 2 * M ≤ (k : ℝ))
    (hheavy : (k : ℝ) / M < J.card) (hh : 0 < h)
    (hbound : ∀ j ∈ J, j < k)
    (hcongr : ∀ a ∈ J, ∀ b ∈ J, (h : ℤ) ∣ (b : ℤ) - a)
    (hpath : ∀ n i, ∃ z : ℤ,
      Y n i - A i - (n : ℝ) / h * ((s i : ℝ) + v i) = z)
    (hbox : ∀ a ∈ J, ∀ b ∈ J, ∀ i, |Y b i - Y a i| ≤ L i)
    (hwidth : ∀ i, L i ≤ 2 * H)
    (hdrift : ∀ i, |v i| ≤ 4 * M * H / (k : ℝ))
    (hsmall : 2 * H + 4 * M * H / (h : ℝ) < 1) :
    ∀ i, |v i| ≤ (2 * M / (k : ℝ)) * L i := by
  obtain ⟨hcard, _, _, hk⟩ := heavy_card_estimates hM hscale hheavy
  have hJ : J.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc, hcount, hspan, hspanbound⟩ :=
    residue_fiber_span J hJ hh hcard hcongr hbound
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hcR : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hcountR : (J.card : ℝ) - 1 ≤ c := by
    have hcast : ((J.card - 1 : ℕ) : ℝ) ≤ c := by exact_mod_cast hcount
    simpa only [Nat.cast_sub (by omega : 1 ≤ J.card), Nat.cast_one] using hcast
  have hclower : (k : ℝ) / (2 * M) ≤ c :=
    (heavy_card_div_lower hM hscale hheavy).trans hcountR
  have hspanR : (c : ℝ) * h ≤ k := by exact_mod_cast hspanbound.le
  have hmin := J.min'_mem hJ
  have hmax := J.max'_mem hJ
  have hminmax : J.min' hJ ≤ J.max' hJ := J.min'_le _ hmax
  intro i
  have hphase := rational_path_period_difference Y A v s hh hminmax hspan hpath i
  have hprod : |(c : ℝ) * v i| ≤ 4 * M * H / (h : ℝ) := by
    rw [abs_mul, abs_of_nonneg hcR]
    apply (le_div_iff₀ hhR).2
    calc
      ((c : ℝ) * |v i|) * h = ((c : ℝ) * h) * |v i| := by ring
      _ ≤ (k : ℝ) * |v i| := mul_le_mul_of_nonneg_right hspanR (abs_nonneg _)
      _ ≤ 4 * M * H := by
        have hv := (le_div_iff₀ hkR).mp (hdrift i)
        simpa only [mul_comm] using hv
  apply heavy_interval_relative_drift hkR hM hclower hphase
    (hbox _ hmin _ hmax i) hprod
  linarith [hwidth i]

/-- Apply the endpoint argument to the actual occurrence fiber of any heavy
label, including labels different from the one that supplied the return. -/
theorem heavy_label_relative_width {ι : Type uIndex} {B : Type uB} {k h j : ℕ}
    {M H : ℝ} (Y : ℕ → ι → ℝ) (A v : ι → ℝ) (s : ι → ℤ)
    (label : ℕ → B) (width : B → ι → ℝ)
    (hM : 0 < M) (hscale : 2 * M ≤ (k : ℝ))
    (hheavy : (k : ℝ) / M < (labelFiber k label (label j)).card) (hh : 0 < h)
    (hcongr : ∀ a, a < k → ∀ b, b < k → label a = label b →
      (h : ℤ) ∣ (b : ℤ) - a)
    (hpath : ∀ n i, ∃ z : ℤ,
      Y n i - A i - (n : ℝ) / h * ((s i : ℝ) + v i) = z)
    (hbox : ∀ a, a < k → ∀ b, b < k → label a = label b →
      ∀ i, |Y b i - Y a i| ≤ width (label a) i)
    (hwidth : ∀ i, width (label j) i ≤ 2 * H)
    (hdrift : ∀ i, |v i| ≤ 4 * M * H / (k : ℝ))
    (hsmall : 2 * H + 4 * M * H / (h : ℝ) < 1) :
    ∀ i, |v i| ≤ (2 * M / (k : ℝ)) * width (label j) i := by
  apply heavy_fiber_relative_width Y A v (width (label j)) s hM hscale hheavy hh
  · intro n hn
    exact (mem_labelFiber.mp hn).1
  · intro a ha b hb
    obtain ⟨ha, hla⟩ := mem_labelFiber.mp ha
    obtain ⟨hb, hlb⟩ := mem_labelFiber.mp hb
    exact hcongr a ha b hb (hla.trans hlb.symm)
  · exact hpath
  · intro a ha b hb i
    obtain ⟨ha, hla⟩ := mem_labelFiber.mp ha
    obtain ⟨hb, hlb⟩ := mem_labelFiber.mp hb
    simpa only [hla] using hbox a ha b hb (hla.trans hlb.symm) i
  · exact hwidth
  · exact hdrift
  · exact hsmall

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Drift relative to actual heavy adaptive intervals

The heavy multiplicity is counted over `Fin k` using the actual literal full
label. Its natural-index fiber has the same cardinality. Equal labels place the
actual centered representatives in the same half-open interval, providing the
width bound required by the general endpoint argument.
-/

namespace QuantitativeVanDerWaerden

/-- Equal literal labels bound the difference by the actual adaptive interval
width, rather than only by the uniform upper bound on mesh widths. -/
theorem literalFullLabel_second_width (mesh : AdaptiveMesh)
    (q D lam Ucount : ℕ) (hU : 0 < Ucount) {a b : CyclicGroup q D}
    (hlabel : literalFullLabel mesh q D lam Ucount hU a =
      literalFullLabel mesh q D lam Ucount hU b) (i : Fin D) :
    |yRep q D lam b i - yRep q D lam a i| ≤
      mesh.width ((literalFullLabel mesh q D lam Ucount hU a).2 i) := by
  have ha := literalFullLabel_second_mem mesh q D lam Ucount hU a i
  have hb := literalFullLabel_second_mem mesh q D lam Ucount hU b i
  have hi := congrFun (congrArg Prod.snd hlabel) i
  rw [← hi] at hb
  unfold AdaptiveMesh.Contains at ha hb
  unfold AdaptiveMesh.width
  apply abs_le.mpr
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

open scoped Classical in
/-- Every heavy literal-label fiber controls the drift relative to the width
of its own adaptive interval in every coordinate. -/
theorem cyclic_heavy_label_relative_width (mesh : AdaptiveMesh)
    {q D lam Ucount k h : ℕ} (hU : 0 < Ucount)
    (a d : CyclicGroup q D) (A v : Fin D → ℝ) (s : Fin D → ℤ) (j : Fin k)
    {M : ℝ} (hM : 0 < M) (hscale : 2 * M ≤ (k : ℝ))
    (hheavy : (k : ℝ) / M <
      (Finset.univ.filter (fun n : Fin k =>
        literalFullLabel mesh q D lam Ucount hU (a + n.val • d) =
        literalFullLabel mesh q D lam Ucount hU (a + j.val • d))).card)
    (hh : 0 < h)
    (hcongr : ∀ m, m < k → ∀ n, n < k →
      literalFullLabel mesh q D lam Ucount hU (a + m • d) =
        literalFullLabel mesh q D lam Ucount hU (a + n • d) →
      (h : ℤ) ∣ (n : ℤ) - m)
    (hpath : ∀ (n : ℕ) (i : Fin D), ∃ z : ℤ,
      yRep q D lam (a + n • d) i - A i -
        (n : ℝ) / h * ((s i : ℝ) + v i) = z)
    (hdrift : ∀ i, |v i| ≤ 4 * M * mesh.H / (k : ℝ))
    (hsmall : 2 * mesh.H + 4 * M * mesh.H / (h : ℝ) < 1) :
    ∀ i, |v i| ≤ (2 * M / (k : ℝ)) *
      mesh.width (mesh.meshLabel (yRep q D lam (a + j.val • d) i)) := by
  classical
  let label := fun n : ℕ => literalFullLabel mesh q D lam Ucount hU (a + n • d)
  have hheavy' : (k : ℝ) / M < (labelFiber k label (label j.val)).card := by
    rw [card_labelFiber]
    convert hheavy using 1; congr
  apply heavy_label_relative_width (j := j.val)
    (fun n => yRep q D lam (a + n • d)) A v s label
    (fun beta i => mesh.width (beta.2 i)) hM hscale hheavy' hh hcongr hpath
  · intro m _ n _ hlabel i
    exact literalFullLabel_second_width mesh q D lam Ucount hU hlabel i
  · intro i
    exact mesh.width_le_two_H _
  · exact hdrift
  · exact hsmall

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

namespace QuantitativeVanDerWaerden.IsHeavyLabelReturn

variable {mesh : AdaptiveMesh} {q D lam Ucount k M j h : ℕ} {hU : 0 < Ucount}
  {a d : CyclicGroup q D} {beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)}
  (R : IsHeavyLabelReturn mesh q D lam Ucount k M hU a d beta j h)

include R

open scoped Classical in
/-- Every heavy label controls the same actual return displacement, even when
it differs from the label used to select the closest return. -/
theorem every_heavy_relative_width (hq : 0 < q) (hM : 0 < M)
    (hscale : 2 * M ≤ k) (hwidth : 1 / (Ucount : ℝ) ≤ mesh.H)
    (hseparate : 4 * (M : ℝ) * mesh.H < 1)
    (hsmall : 2 * mesh.H + 4 * (M : ℝ) * mesh.H / (h : ℝ) < 1) :
    ∀ r : Fin k,
      (k : ℝ) / (M : ℝ) <
        (Finset.univ.filter (fun n : Fin k =>
          literalFullLabel mesh q D lam Ucount hU (a + n.val • d) =
          literalFullLabel mesh q D lam Ucount hU (a + r.val • d))).card →
      ∀ i, |yRep q D lam (a + (j + h) • d) i - yRep q D lam (a + j • d) i| ≤
        (2 * (M : ℝ) / (k : ℝ)) *
          mesh.width (mesh.meshLabel (yRep q D lam (a + r.val • d) i)) := by
  classical
  obtain ⟨t, _, _, _, hy⟩ := R.primitive_return_path hq
  have hpath : ∀ (n : ℕ) (i : Fin D), ∃ z : ℤ,
      yRep q D lam (a + n • d) i - yRep q D lam a i -
        (n : ℝ) / h * (((lam : ℤ) * t i : ℤ) +
          (yRep q D lam (a + (j + h) • d) i - yRep q D lam (a + j • d) i) : ℝ) = z := by
    intro n i
    obtain ⟨z, hz⟩ := hy n i
    refine ⟨z, ?_⟩
    simpa only [Int.cast_mul, Int.cast_natCast, R.dilation_eq i, mul_add] using hz
  intro r hr
  apply cyclic_heavy_label_relative_width (M := (M : ℝ)) mesh hU a d (yRep q D lam a)
    (fun i => yRep q D lam (a + (j + h) • d) i - yRep q D lam (a + j • d) i)
    (fun i => (lam : ℤ) * t i) r
    (by exact_mod_cast hM) (by exact_mod_cast hscale) hr R.gap_pos
    (R.same_label_divides hq hwidth hseparate) hpath R.y_rate hsmall

end QuantitativeVanDerWaerden.IsHeavyLabelReturn

end OAI
end
end

section
section
namespace OAI

/-!
# Finite rational labels for an actual heavy return

The previously proved reduced integer numerator lies in `[0,h)`. Converting
it to `Fin h` preserves primitivity and both rational paths. The second path
uses the actual second-system displacement, via the proved real dilation
identity.
-/

namespace QuantitativeVanDerWaerden.IsHeavyLabelReturn

variable {mesh : AdaptiveMesh} {q D lam Ucount k M j h : ℕ} {hU : 0 < Ucount}
  {a d : CyclicGroup q D} {beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)}
  (R : IsHeavyLabelReturn mesh q D lam Ucount k M hU a d beta j h)

include R

/-- The actual rational return paths with a finite numerator label and the
actual displacements in both coordinate systems. -/
theorem exists_fin_return_path (hq : 0 < q) :
    ∃ t : Fin D → Fin h,
      PrimitiveVector h (fun i => ((t i).val : ℤ)) ∧
      (∀ (n : ℕ) (i : Fin D), ∃ z : ℤ,
        xRep q D (a + n • d) i - xRep q D a i - (n : ℝ) / h *
          ((t i).val + (xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i)) = z) ∧
      (∀ (n : ℕ) (i : Fin D), ∃ z : ℤ,
        yRep q D lam (a + n • d) i - yRep q D lam a i - (n : ℝ) / h *
          ((lam : ℝ) * (t i).val +
            (yRep q D lam (a + (j + h) • d) i - yRep q D lam (a + j • d) i)) = z) := by
  obtain ⟨T, hTrange, hprimitive, hx, hy⟩ := R.primitive_return_path hq
  let t : Fin D → Fin h := fun i =>
    ⟨(T i).toNat, by have hr := hTrange i; omega⟩
  have htInt (i : Fin D) : ((t i).val : ℤ) = T i :=
    Int.toNat_of_nonneg (hTrange i).1
  have htReal (i : Fin D) : ((t i).val : ℝ) = (T i : ℝ) := by
    exact_mod_cast htInt i
  refine ⟨t, ?_, ?_, ?_⟩
  · have ht : (fun i => ((t i).val : ℤ)) = T := funext htInt
    rw [ht]
    exact hprimitive
  · intro n i
    simpa only [htReal i] using hx n i
  · intro n i
    obtain ⟨z, hz⟩ := hy n i
    refine ⟨z, ?_⟩
    rw [htReal i, R.dilation_eq i]
    convert hz using 1; ring

end QuantitativeVanDerWaerden.IsHeavyLabelReturn

end OAI
end
end

section
section
namespace OAI

/-! A failed affine lift of centered circle representatives crosses the cut.

The crossing is allowed at either endpoint of the parameter interval. This is
needed when the initial centered representative is the included endpoint
`-1 / 2` and the affine line immediately leaves the centered interval.
-/

namespace QuantitativeVanDerWaerden

/-- Two centered representatives congruent modulo the integers are equal. -/
theorem centered_representative_unique_of_integer_difference {x y : ℝ}
    (hx : -(1 / 2 : ℝ) ≤ x ∧ x < 1 / 2)
    (hy : -(1 / 2 : ℝ) ≤ y ∧ y < 1 / 2)
    (hcongr : ∃ z : ℤ, x - y = z) : x = y := by
  obtain ⟨z, hz⟩ := hcongr
  have habs : |(z : ℝ)| < 1 := by
    apply abs_lt.mpr
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hz0 : z = 0 := integer_eq_zero_of_abs_lt_one habs
  rw [hz0, Int.cast_zero] at hz
  linarith

/-- A real affine segment starting in the centered interval and ending
outside it meets one of the two boundary representatives of the circle cut. -/
theorem affine_cut_of_leaving_centered_interval {A w T : ℝ}
    (hA : -(1 / 2 : ℝ) ≤ A ∧ A < 1 / 2) (hT : 0 ≤ T)
    (hout : ¬ (-(1 / 2 : ℝ) ≤ A + T * w ∧ A + T * w < 1 / 2)) :
    w ≠ 0 ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧
      ∃ z : ℤ, A + t * w = 1 / 2 + z := by
  by_cases hlow : A + T * w < -(1 / 2 : ℝ)
  · have hw : w < 0 := by
      by_contra h
      have hp := mul_nonneg hT (le_of_not_gt h)
      linarith [hA.1]
    refine ⟨ne_of_lt hw, (-1 / 2 - A) / w, ?_, ?_, -1, ?_⟩
    · exact div_nonneg_of_nonpos (by linarith [hA.1]) hw.le
    · apply (div_le_iff_of_neg hw).mpr
      linarith
    · rw [div_mul_cancel₀ _ (ne_of_lt hw)]
      norm_num
  · have hu : (1 / 2 : ℝ) ≤ A + T * w := by
      by_contra h
      exact hout ⟨le_of_not_gt hlow, lt_of_not_ge h⟩
    have hw : 0 < w := by
      by_contra h
      have hp := mul_nonpos_of_nonneg_of_nonpos hT (le_of_not_gt h)
      linarith [hA.2]
    refine ⟨ne_of_gt hw, (1 / 2 - A) / w, ?_, ?_, 0, ?_⟩
    · exact div_nonneg (by linarith [hA.2]) hw.le
    · apply (div_le_iff₀ hw).mpr
      linarith
    · rw [div_mul_cancel₀ _ (ne_of_gt hw)]
      norm_num

/-- Failure of a real affine lift of a finite centered progression gives a
cut crossing at a real parameter between `0` and `k - 1`. Integer congruence
alone suffices; no assumption on the size of the affine step is needed. -/
theorem failed_centered_lift_cut {Y : ℕ → ℝ} {A w : ℝ} {k : ℕ}
    (hrep : ∀ j, j < k → -(1 / 2 : ℝ) ≤ Y j ∧ Y j < 1 / 2)
    (hbase : Y 0 = A)
    (hcongr : ∀ j, j < k → ∃ z : ℤ, Y j - (A + (j : ℝ) * w) = z)
    (hfail : ∃ j, j < k ∧ Y j ≠ A + (j : ℝ) * w) :
    w ≠ 0 ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ (k : ℝ) - 1 ∧
      ∃ z : ℤ, A + t * w = 1 / 2 + z := by
  obtain ⟨j, hj, hfail⟩ := hfail
  have hA : -(1 / 2 : ℝ) ≤ A ∧ A < 1 / 2 := by
    simpa only [hbase] using hrep 0 (by omega)
  have hout : ¬ (-(1 / 2 : ℝ) ≤ A + (j : ℝ) * w ∧
      A + (j : ℝ) * w < 1 / 2) := by
    intro hmem
    exact hfail (centered_representative_unique_of_integer_difference
      (hrep j hj) hmem (hcongr j hj))
  obtain ⟨hw, t, ht0, htj, z, hz⟩ :=
    affine_cut_of_leaving_centered_interval hA (Nat.cast_nonneg j) hout
  have hjk : (j : ℝ) + 1 ≤ (k : ℝ) := by
    exact_mod_cast (show j + 1 ≤ k from hj)
  exact ⟨hw, t, ht0, by linarith, z, hz⟩

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-! Geometric consequences of the actual cyclic representative system. -/

namespace QuantitativeVanDerWaerden

/-- The coordinate lattice is unchanged when a real step is shifted by an integer. -/
theorem yRep_step_lattice {q D dilation : ℕ} (hq : 0 < q)
    (d : CyclicGroup q D) (i : Fin D) {w : ℝ}
    (hstep : ∃ z : ℤ, yRep q D dilation d i - w = z) :
    ∃ z : ℤ, (q : ℝ) ^ (i.val + 1) * w = z := by
  obtain ⟨z₁, h₁⟩ := yRep_lattice q D dilation d i hq
  obtain ⟨z₂, h₂⟩ := hstep
  refine ⟨z₁ - (q : ℤ) ^ (i.val + 1) * z₂, ?_⟩
  push_cast
  nlinarith [congrArg (fun t : ℝ => (q : ℝ) ^ (i.val + 1) * t) h₂]

/-- Every nonzero lifted coordinate step is at least one coordinate lattice unit. -/
theorem yRep_step_abs_lower {q D dilation : ℕ} (hq : 0 < q)
    (d : CyclicGroup q D) (i : Fin D) {w : ℝ}
    (hstep : ∃ z : ℤ, yRep q D dilation d i - w = z) (hw : w ≠ 0) :
    1 / (q : ℝ) ^ (i.val + 1) ≤ |w| := by
  have hlat : ∃ z : ℤ, ((q ^ (i.val + 1) : ℕ) : ℝ) * w = z := by
    simpa only [Nat.cast_pow] using yRep_step_lattice hq d i hstep
  simpa only [Nat.cast_pow] using lattice_separation (pow_pos hq (i.val + 1)) hlat hw

/-- The mesh cutoff `q^(-(D+1))` lies below every nonzero lifted step. -/
theorem yRep_step_mesh_lower {q D dilation : ℕ} (hq : 0 < q)
    (d : CyclicGroup q D) (i : Fin D) {w : ℝ}
    (hstep : ∃ z : ℤ, yRep q D dilation d i - w = z) (hw : w ≠ 0) :
    1 / (q : ℝ) ^ (D + 1) ≤ 1 / (q : ℝ) ^ D ∧
      1 / (q : ℝ) ^ D ≤ |w| := by
  have hqN : 1 ≤ q := hq
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hqN
  have hpow : 0 < (q : ℝ) ^ (i.val + 1) := by positivity
  constructor
  · exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ hqR (Nat.le_succ D))
  · exact (one_div_le_one_div_of_le hpow
      (pow_le_pow_right₀ hqR (show i.val + 1 ≤ D from i.isLt))).trans
        (yRep_step_abs_lower hq d i hstep hw)

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# The short-period branch of the outer-color dichotomy

A cut crossed by the unreduced real path is close to every sample. The actual
adaptive mesh then makes every sampled interval narrower than the nonzero
step. Two equal labels contradict this, forcing one global real affine lift.
-/


namespace QuantitativeVanDerWaerden

theorem rho_eq_of_integer_difference {x y : ℝ}
    (h : ∃ z : ℤ, x - y = (z : ℝ)) : rho x = rho y := by
  obtain ⟨z, hz⟩ := h
  have he : x = y + z := by linarith
  rw [he, rho_add_int]

theorem rho_half : rho (1 / 2 : ℝ) = 0 := by
  rw [rho_eq_of_closed_mem (by norm_num) le_rfl,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  ring

/-- The circle distance to the cut is at most the real distance to any lift
of that cut. This includes equality at either endpoint. -/
theorem rho_le_distance_to_cut (x : ℝ) (z : ℤ) :
    rho x ≤ |x - (1 / 2 + z)| := by
  have h := rho_lipschitz_integer x (1 / 2) z
  rw [rho_half, sub_zero, abs_of_nonneg (rho_nonneg x)] at h
  simpa only [sub_add_eq_sub_sub] using h

/-- Once the closed real segment hits a cut, every sample is cut-near.
The congruences connect the real path with the actual centered samples. -/
theorem short_segment_cut_rho {Y : ℕ → ℝ} {A w t : ℝ} {k : ℕ} {z : ℤ}
    (hcongr : ∀ j, j < k → ∃ m : ℤ, Y j - (A + (j : ℝ) * w) = (m : ℝ))
    (ht0 : 0 ≤ t) (htk : t ≤ (k : ℝ))
    (hcut : A + t * w = 1 / 2 + z) :
    ∀ j, j < k → rho (Y j) ≤ (k : ℝ) * |w| := by
  intro j hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hjk : (j : ℝ) ≤ k := by exact_mod_cast hj.le
  have hdist : |(j : ℝ) - t| ≤ k := abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    rho (Y j) = rho (A + (j : ℝ) * w) := rho_eq_of_integer_difference (hcongr j hj)
    _ ≤ |A + (j : ℝ) * w - (1 / 2 + z)| := rho_le_distance_to_cut _ z
    _ = |((j : ℝ) - t) * w| := by rw [← hcut]; congr 1; ring
    _ = |(j : ℝ) - t| * |w| := abs_mul _ _
    _ ≤ (k : ℝ) * |w| := mul_le_mul_of_nonneg_right hdist (abs_nonneg w)

/-- A repeated interval forces every centered sample onto the same real lift.
Only the width at one of the repeated samples is needed. -/
theorem short_period_affine_lift {Y : ℕ → ℝ} {A w H α width : ℝ} {k a b : ℕ}
    (hrep : ∀ j, j < k → -(1 / 2 : ℝ) ≤ Y j ∧ Y j < 1 / 2)
    (hbase : Y 0 = A)
    (hcongr : ∀ j, j < k → ∃ z : ℤ, Y j - (A + (j : ℝ) * w) = (z : ℝ))
    (hH : 0 ≤ H) (hmotion : (k : ℝ) * |w| < 1 / 2)
    (hsep : w ≠ 0 → α ≤ |w|) (hsmall : 2 * H * ((k : ℝ) + 1) < 1)
    (hab : a ≠ b) (hak : a < k) (hbk : b < k)
    (hsame : |Y a - Y b| ≤ width)
    (hwidth : width ≤ 2 * H * (rho (Y a) + α)) :
    ∀ j, j < k → Y j = A + (j : ℝ) * w := by
  intro j hj
  by_contra hfail
  obtain ⟨hw, t, ht0, htk, z, hcut⟩ :=
    failed_centered_lift_cut hrep hbase hcongr ⟨j, hj, hfail⟩
  have hrho := short_segment_cut_rho hcongr ht0
    (show t ≤ (k : ℝ) by linarith) hcut a hak
  have hnarrow := short_cut_interval_lt_step hH hw (hsep hw) hrho hwidth hsmall
  have hint : ∃ z : ℤ, (Y a - Y b) - ((a : ℝ) - b) * w = (z : ℝ) := by
    obtain ⟨za, hza⟩ := hcongr a hak
    obtain ⟨zb, hzb⟩ := hcongr b hbk
    refine ⟨za - zb, ?_⟩
    push_cast
    linarith
  exact short_step_not_same_interval hab hak hbk hmotion hint (hsame.trans_lt hnarrow)

theorem AdaptiveMesh.short_period_affine_lift (M : AdaptiveMesh)
    {Y : ℕ → ℝ} {A w : ℝ} {k a b : ℕ}
    (hrep : ∀ j, j < k → -(1 / 2 : ℝ) ≤ Y j ∧ Y j < 1 / 2)
    (hbase : Y 0 = A)
    (hcongr : ∀ j, j < k → ∃ z : ℤ, Y j - (A + (j : ℝ) * w) = (z : ℝ))
    (hmotion : (k : ℝ) * |w| < 1 / 2)
    (hsep : w ≠ 0 → M.alpha ≤ |w|)
    (hsmall : 2 * M.H * ((k : ℝ) + 1) < 1)
    (hab : a ≠ b) (hak : a < k) (hbk : b < k)
    (hsame : M.meshLabel (Y a) = M.meshLabel (Y b)) :
    ∀ j, j < k → Y j = A + (j : ℝ) * w := by
  have hca : centered (Y a) = Y a := centered_eq_of_mem (hrep a hak).1 (hrep a hak).2
  have hcb : centered (Y b) = Y b := centered_eq_of_mem (hrep b hbk).1 (hrep b hbk).2
  have hdist := M.same_label_distance hsame
  rw [hca, hcb] at hdist
  have hcontains := M.meshLabel_contains (Y a)
  rw [hca] at hcontains
  exact QuantitativeVanDerWaerden.short_period_affine_lift hrep hbase hcongr M.H_pos.le
    hmotion hsep hsmall hab hak hbk hdist
    (M.width_bounds_of_closed_mem _ hcontains.1 hcontains.2.le).2

/-- The coordinatewise conclusion gives a single vector affine lift. -/
theorem AdaptiveMesh.short_period_vector_lift (M : AdaptiveMesh)
    {ι : Type uIndex} {Y : ℕ → ι → ℝ} {w : ι → ℝ} {k a b : ℕ}
    (hrep : ∀ i j, j < k → -(1 / 2 : ℝ) ≤ Y j i ∧ Y j i < 1 / 2)
    (hcongr : ∀ i j, j < k →
      ∃ z : ℤ, Y j i - (Y 0 i + (j : ℝ) * w i) = (z : ℝ))
    (hmotion : ∀ i, (k : ℝ) * |w i| < 1 / 2)
    (hsep : ∀ i, w i ≠ 0 → M.alpha ≤ |w i|)
    (hsmall : 2 * M.H * ((k : ℝ) + 1) < 1)
    (hab : a ≠ b) (hak : a < k) (hbk : b < k)
    (hsame : ∀ i, M.meshLabel (Y a i) = M.meshLabel (Y b i)) :
    ∀ j, j < k → Y j = fun i => Y 0 i + (j : ℝ) * w i := by
  intro j hj
  funext i
  exact M.short_period_affine_lift (hrep i) rfl (hcongr i) (hmotion i)
    (hsep i) hsmall hab hak hbk (hsame i) j hj

/-- Short-period lifting for the actual cyclic representatives and actual
adaptive labels. The only remaining inputs are the numerical short-motion
bounds, a congruent step, and a repeated label. -/
theorem AdaptiveMesh.short_period_cyclic_lift (M : AdaptiveMesh)
    {q D dilation k a b : ℕ} (hq : 0 < q)
    (n d : CyclicGroup q D) (w : Fin D → ℝ)
    (hstep : ∀ i, ∃ z : ℤ, yRep q D dilation d i - w i = (z : ℝ))
    (halpha : M.alpha ≤ 1 / (q : ℝ) ^ D)
    (hmotion : ∀ i, (k : ℝ) * |w i| < 1 / 2)
    (hsmall : 2 * M.H * ((k : ℝ) + 1) < 1)
    (hab : a ≠ b) (hak : a < k) (hbk : b < k)
    (hsame : ∀ i, M.meshLabel (yRep q D dilation (n + a • d) i) =
      M.meshLabel (yRep q D dilation (n + b • d) i)) :
    ∀ j, j < k → yRep q D dilation (n + j • d) =
      fun i => yRep q D dilation n i + (j : ℝ) * w i := by
  have hcongr : ∀ i j, j < k → ∃ z : ℤ,
      yRep q D dilation (n + j • d) i -
        (yRep q D dilation (n + 0 • d) i + (j : ℝ) * w i) = (z : ℝ) := by
    intro i j _
    obtain ⟨a, ha⟩ := yRep_ap_congr hq dilation n d j i
    obtain ⟨b, hb⟩ := hstep i
    refine ⟨a + (j : ℤ) * b, ?_⟩
    simp only [zero_nsmul, add_zero, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    nlinarith [congrArg (fun t : ℝ => (j : ℝ) * t) hb]
  have hsep : ∀ i, w i ≠ 0 → M.alpha ≤ |w i| := by
    intro i hi
    exact halpha.trans (yRep_step_mesh_lower hq d i (hstep i) hi).2
  have h := M.short_period_vector_lift
    (fun i j _ => yRep_mem q D dilation (n + j • d) i)
    hcongr hmotion hsep hsmall hab hak hbk hsame
  simpa only [zero_nsmul, add_zero] using h

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Short-period lifting from a rational return path

When the return period divides the dilation, the rational rotation contributes
an integer in every coordinate. The remaining real step is the dilated return
error divided by the period. This connects the actual rational-path identity
to the centered affine lift.
-/

namespace QuantitativeVanDerWaerden

/-- Divisibility of the dilation kills the integer numerator of a rational
return path modulo one. The resulting step is congruent to the actual cyclic
step; the integer witness follows by comparing the two path identities at
index one. -/
theorem rational_path_short_step_congr {q D dilation h : ℕ} (hq : 0 < q)
    (n d : CyclicGroup q D) (t : Fin D → ℤ) (u : Fin D → ℝ)
    (hh : 0 < h) (hdiv : h ∣ dilation)
    (hpath : ∀ (j : ℕ) (i : Fin D), ∃ z : ℤ,
      yRep q D dilation (n + j • d) i - yRep q D dilation n i -
        (j : ℝ) / h * ((dilation : ℝ) * ((t i : ℝ) + u i)) = z) :
    ∀ i, ∃ z : ℤ,
      yRep q D dilation d i - (dilation : ℝ) * u i / h = z := by
  obtain ⟨c, hc⟩ := hdiv
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hcR : (dilation : ℝ) = (h : ℝ) * (c : ℝ) := by exact_mod_cast hc
  intro i
  obtain ⟨z₁, h₁⟩ := hpath 1 i
  obtain ⟨z₂, h₂⟩ := yRep_ap_congr hq dilation n d 1 i
  simp only [Nat.cast_one, one_mul] at h₁ h₂
  have hrotation : (1 / (h : ℝ)) * ((dilation : ℝ) * ((t i : ℝ) + u i)) -
      (dilation : ℝ) * u i / h = (c : ℝ) * (t i : ℝ) := by
    rw [hcR]
    field_simp [hhR]
    ring
  refine ⟨(c : ℤ) * t i + z₁ - z₂, ?_⟩
  push_cast
  linarith

/-- The short-period affine lift with its step congruence supplied by the
actual rational return path. The numerator need not satisfy additional
primitivity or range hypotheses for this branch. -/
theorem AdaptiveMesh.short_period_path_lift (M : AdaptiveMesh)
    {q D dilation h k a b : ℕ} (hq : 0 < q)
    (n d : CyclicGroup q D) (t : Fin D → ℤ) (u : Fin D → ℝ)
    (hh : 0 < h) (hdiv : h ∣ dilation)
    (hpath : ∀ (j : ℕ) (i : Fin D), ∃ z : ℤ,
      yRep q D dilation (n + j • d) i - yRep q D dilation n i -
        (j : ℝ) / h * ((dilation : ℝ) * ((t i : ℝ) + u i)) = z)
    (halpha : M.alpha ≤ 1 / (q : ℝ) ^ D)
    (hmotion : ∀ i, (k : ℝ) * |(dilation : ℝ) * u i / h| < 1 / 2)
    (hsmall : 2 * M.H * ((k : ℝ) + 1) < 1)
    (hab : a ≠ b) (hak : a < k) (hbk : b < k)
    (hsame : ∀ i, M.meshLabel (yRep q D dilation (n + a • d) i) =
      M.meshLabel (yRep q D dilation (n + b • d) i)) :
    ∀ j, j < k → yRep q D dilation (n + j • d) =
      fun i => yRep q D dilation n i +
        (j : ℝ) * ((dilation : ℝ) * u i / h) := by
  exact M.short_period_cyclic_lift hq n d
    (fun i => (dilation : ℝ) * u i / h)
    (rational_path_short_step_congr hq n d t u hh hdiv hpath)
    halpha hmotion hsmall hab hak hbk hsame

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# The actual outer-coloring dichotomy

The coloring is the selected coloring of literal full labels. A progression
with many light positions is balanced by its global word test. Otherwise its
actual closest heavy-label return supplies a primitive rational path. Short
periods lift affinely; long periods satisfy the actual eligible block tests.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

/-- Every actual cyclic progression is either rich in both outer colors or
has an affine lift in the second representative system. -/
theorem OuterChoice.rich_or_affine {k : ℕ} (s : Data k) (hk : 3 ≤ k)
    (o : OuterChoice s hk) (hg : GeometryScales k) (a d : Group s) :
    (∀ b : Bool, k ≤ 100 * (Finset.univ.filter fun j : Fin k =>
      o.color (fullLabelWord s hk (a, d) j) = b).card) ∨
    ∃ A B : Fin (dimension k) → ℝ, ∀ j : Fin k,
      yRep s.q (dimension k) (lambda k) (a + (j.val : Group s) * d) =
        fun i => A i + (j.val : ℝ) * B i := by
  classical
  rcases rich_or_heavy_word (fullLabelWord s hk (a, d)) o.color
    (o.balanced.global_words _ (o.word_mem (a, d))) with hrich | ⟨hfew, r, hr⟩
  · exact Or.inl hrich
  obtain ⟨j, h, R⟩ := exists_selected_heavy_label_return_of_word s hk hg a d
    (fullLabelWord s hk (a, d) r) hr
  let u : Fin (dimension k) → ℝ := fun i =>
    xRep s.q (dimension k) (a + (j + h) • d) i -
      xRep s.q (dimension k) (a + j • d) i
  let v : Fin (dimension k) → ℝ := fun i =>
    yRep s.q (dimension k) (lambda k) (a + (j + h) • d) i -
      yRep s.q (dimension k) (lambda k) (a + j • d) i
  have hvu : ∀ i, v i = (lambda k : ℝ) * u i := R.dilation_eq
  have hv : ∀ i, |v i| ≤ 4 * cutoff k * (mesh s hk).H / k := R.y_rate
  by_cases hshort : h ≤ dimension k ^ 2
  · right
    obtain ⟨T, _, _, _, hY⟩ := R.primitive_return_path s.pos
    have hmotion : ∀ i, (k : ℝ) * |(lambda k : ℝ) * u i / h| < 1 / 2 := by
      intro i
      rw [← hvu i]
      exact velocity_div_small s hk hg R.gap_pos (hv i)
    have hsmall : 2 * (mesh s hk).H * ((k : ℝ) + 1) < 1 := by
      simpa only [mesh_H] using hg.mesh_lift
    have hsame : ∀ i,
        (mesh s hk).meshLabel
          (yRep s.q (dimension k) (lambda k) (a + j • d) i) =
        (mesh s hk).meshLabel
          (yRep s.q (dimension k) (lambda k) (a + (j + h) • d) i) := by
      intro i
      exact congrArg (fun L => L.2 i) (R.start_label.trans R.end_label.symm)
    have hlift := (mesh s hk).short_period_path_lift s.pos a d T u R.gap_pos
      (short_period_dvd_lambda R.gap_pos R.gap_le hshort) hY
      (mesh_alpha_le s hk) hmotion hsmall
      (show j ≠ j + h by have := R.gap_pos; omega) R.start_lt R.end_lt hsame
    refine ⟨yRep s.q (dimension k) (lambda k) a,
      fun i => (lambda k : ℝ) * u i / h, ?_⟩
    intro z
    simpa only [nsmul_eq_mul] using hlift z.val z.isLt
  · left
    obtain ⟨t, hprimitive, hX, hY⟩ := R.exists_fin_return_path s.pos
    have hfirst : ∀ i, |u i| ≤ 1 / (uniformCount k : ℝ) :=
      literalFullLabel_same_first_distance (mesh s hk) s.q (dimension k)
        (lambda k) (uniformCount k) (uniformCount_pos hk)
        (R.end_label.trans R.start_label.symm)
    have hseparate : 4 * (cutoff k : ℝ) * (mesh s hk).H < 1 := by
      have he : 4 * (cutoff k : ℝ) * (mesh s hk).H < 1 / 2 := by
        simpa only [mesh_H] using hg.rational_separation
      linarith
    have hheavy := R.every_heavy_relative_width s.pos (geometry_cutoff_pos hk)
      (geometry_two_cutoff_le_length hg) (uniformWidth_le_meshH s hk)
      hseparate (lattice_error_small s hk hg R.gap_pos)
    have hblocksmall : (h : ℝ) ≤ (k : ℝ) / 10 := by
      have hh : (h : ℝ) ≤ 2 * cutoff k := by exact_mod_cast R.gap_le
      exact hh.trans hg.heavy_return
    have hperiodmem : h ∈ Finset.Ioc (dimension k ^ 2) (2 * cutoff k) :=
      Finset.mem_Ioc.mpr ⟨Nat.lt_of_not_ge hshort, R.gap_le⟩
    have hlong := literal_long_period_balanced (mesh s hk) s.q (dimension k)
      (lambda k) (uniformCount k) k h (uniformCount_pos hk) a d (cutoff k) u v t
      R.gap_pos (geometry_dimension_ge_three hg) o.color hprimitive
      (fun z _ i => hX z i) (fun z _ i => hY z i) hfirst
      (twice_period_uniformWidth_lt_one s hk hg R.gap_le)
      (fun i _ => velocity_le_mesh s hk hg (hv i))
      (fun i _ => velocity_lt_cut s hk hg (hv i))
      (fun i hi => reducedDenominator_gt_of_not_dvd R.gap_pos R.gap_le hi)
      hg.block_loss hheavy (selected_lightCount_le_of_few s hk a d hfew)
      hblocksmall (o.balanced.eligible_patterns h hperiodmem t)
    intro b
    have hc : (k : ℝ) ≤ 100 *
        ((Finset.univ.filter fun z : Fin k =>
          o.color (fullLabelWord s hk (a, d) z) = b).card : ℝ) := by
      have he : (k : ℝ) / 100 ≤
          ((Finset.univ.filter fun z : Fin k =>
            o.color (fullLabelWord s hk (a, d) z) = b).card : ℝ) := by
        refine (hlong b).trans_eq ?_
        apply congrArg (fun n : ℕ => (n : ℝ))
        apply congrArg (Finset.card : Finset (Fin k) → ℕ)
        apply Finset.ext
        intro z
        constructor
        · intro hz
          apply (@Finset.mem_filter _ _ _ _ _).mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          simpa only [fullLabelWord, fullLabel, nsmul_eq_mul] using
            ((@Finset.mem_filter _ _ _ _ _).mp hz).2
        · intro hz
          apply (@Finset.mem_filter _ _ _ _ _).mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          simpa only [fullLabelWord, fullLabel, nsmul_eq_mul] using
            ((@Finset.mem_filter _ _ _ _ _).mp hz).2
      linarith
    exact_mod_cast hc

end QuantitativeVanDerWaerden.ConstructionModel

end

end OAI
end
end

section
section
namespace OAI

/-!
# The unconditional cyclic two-coloring witness

Every parameter, mesh, literal label, outer coloring, geometric key, and finite
probability budget is supplied by its actual construction theorem. The absolute
threshold is chosen before the prime scale and before any final color count.
-/

noncomputable section

open Filter

namespace QuantitativeVanDerWaerden

open Parameters ConstructionModel SparsePerturbation CyclicColoring

theorem construction_key_fiber_card_le_four {k : ℕ} (s : ConstructionModel.Data k)
    (hk : 3 ≤ k) (hbasic : BasicScales k) :
    ∀ a d : ConstructionModel.Group s, d ≠ 0 →
      ∀ key : (Fin (dimension k) → (ConstructionModel.mesh s hk).Label) × ℤ,
      (Finset.univ.filter (fun j : Fin k =>
        perturbationKey (ConstructionModel.mesh s hk) s.q (dimension k)
          (ConstructionModel.lambda k)
          (a + (j.val : ConstructionModel.Group s) * d) = key)).card ≤ 4 := by
  have hunit := ConstructionModel.lambda_coprime s hbasic
  have hunit' : Nat.Coprime (ConstructionModel.lambda k)
      ((s.P ^ s.exponent) ^ dimension k) := by
    simpa only [ConstructionModel.groupSize, s.q_eq_pow] using hunit
  change ∀ a d : CyclicGroup s.q (dimension k), d ≠ 0 →
    ∀ key : (Fin (dimension k) → (ConstructionModel.mesh s hk).Label) × ℤ,
      (Finset.univ.filter (fun j : Fin k =>
        perturbationKey (ConstructionModel.mesh s hk) s.q (dimension k)
          (ConstructionModel.lambda k)
          (a + (j.val : CyclicGroup s.q (dimension k)) * d) = key)).card ≤ 4
  rw [s.q_eq_pow]
  intro a d hd key
  exact perturbationKey_fin_fiber_card_le_four (ConstructionModel.mesh s hk)
    s.prime s.prime_lower.le hunit' (ConstructionModel.mesh_small s hk) a d hd key

/-- The eventual construction uses the actual counted outer witness and the
actual rich-or-affine dichotomy, then samples only the finite geometric-key image. -/
theorem eventually_cyclic_coloring :
    ∀ᶠ k : ℕ in atTop, ∃ N : ℕ, 2 ≤ N ∧
      (k : ℝ) ^ ((1 / 100000 : ℝ) * k) ≤ (N : ℝ) ∧
        ∃ C : ZMod N → Bool, CyclicAvoids C k := by
  filter_upwards [ConstructionModel.eventually_outerChoice, eventually_basicScales,
    eventually_geometryScales, ConstructionModel.eventually_outerChoice_sparse_budget]
    with k houter hbasic hgeom hbudget
  obtain ⟨hk, houter⟩ := houter
  let s : ConstructionModel.Data k := ConstructionModel.choose k hk
  let o : ConstructionModel.OuterChoice s hk := Classical.choice (houter s)
  let : NeZero (s.q ^ dimension k) := ConstructionModel.groupSize_neZero s
  let c₀ : ConstructionModel.Group s → Bool :=
    fun n => o.color (ConstructionModel.fullLabel s hk n)
  let key : ConstructionModel.Group s →
      (Fin (dimension k) → (ConstructionModel.mesh s hk).Label) × ℤ :=
    perturbationKey (ConstructionModel.mesh s hk) s.q (dimension k)
      (ConstructionModel.lambda k)
  let A := affineProgressions s.q (dimension k) (ConstructionModel.lambda k) k
  have hmult : ∀ ad ∈ nonzeroProgressions (s.q ^ dimension k), ∀ a,
      (Finset.univ.filter (fun j : Fin k => (cyclicSignature c₀ key ad j).2 = a)).card ≤ 4 := by
    intro ad had a
    exact construction_key_fiber_card_le_four s hk hbasic ad.1 ad.2
      ((mem_nonzeroProgressions ad).mp had) a
  have hcases : ∀ ad ∈ nonzeroProgressions (s.q ^ dimension k), ad ∈ A ∨ ∀ b,
      k ≤ 100 * (oppositePositions (cyclicSignature (k := k) c₀ key ad) b).card := by
    intro ad had
    rcases ConstructionModel.OuterChoice.rich_or_affine s hk o hgeom ad.1 ad.2 with hrich | haff
    · right
      intro b
      refine (hrich (!b)).trans_eq ?_
      apply congrArg (fun n : ℕ => 100 * n)
      apply congrArg (Finset.card : Finset (Fin k) → ℕ)
      apply Finset.ext
      intro j
      constructor
      · intro hj
        apply (@Finset.mem_filter _ _ _ _ _).mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa only [cyclicSignature, c₀, ConstructionModel.fullLabelWord,
          Bool.eq_not_iff] using ((@Finset.mem_filter _ _ _ _ _).mp hj).2
      · intro hj
        apply (@Finset.mem_filter _ _ _ _ _).mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa only [cyclicSignature, c₀, ConstructionModel.fullLabelWord,
          Bool.eq_not_iff] using ((@Finset.mem_filter _ _ _ _ _).mp hj).2
    · left
      exact (mem_affineProgressions ad).mpr ⟨(mem_nonzeroProgressions ad).mp had, haff⟩
  have hbudget' : 2 * (((s.q ^ dimension k : ℕ) : ℝ)) ^ 2 *
      flipProbability k ^ ((k + 399) / 400) +
      2 * ((A.image (cyclicSignature (k := k) c₀ key)).card : ℝ) *
        (1 - flipProbability k) ^ ((k + 3) / 4) < 1 := by
    simpa only [A, c₀, key, ConstructionModel.groupSize] using hbudget hk s o
  obtain ⟨C, hC⟩ := exists_cyclicAvoids_of_ambient_keys c₀ key A
    (affineProgressions_subset _ _ _ _) (flipProbability_pos (by omega : 0 < k)).le
    hbasic.flip_small.le hmult hcases hbudget'
  refine ⟨ConstructionModel.groupSize s, ConstructionModel.groupSize_two_le s hk, ?_, C, hC⟩
  simpa only [Parameters.c] using ConstructionModel.groupSize_lower s hk

theorem exists_cyclic_coloring :
    ∃ K : ℕ, ∀ k ≥ K, ∃ N : ℕ, 2 ≤ N ∧
      (k : ℝ) ^ ((1 / 100000 : ℝ) * k) ≤ (N : ℝ) ∧
        ∃ C : ZMod N → Bool, CyclicAvoids C k :=
  eventually_atTop.1 eventually_cyclic_coloring

end QuantitativeVanDerWaerden

end

end OAI
end
end

section
section
namespace OAI


namespace QuantitativeVanDerWaerden





end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI


namespace QuantitativeVanDerWaerden

theorem apTerm_lt {a d k N j : ℕ}
    (hbound : a + (k - 1) * d < N) (hj : j < k) : a + j * d < N := by
  have hle : j ≤ k - 1 := by omega
  have := Nat.mul_le_mul_right d hle
  omega

theorem apStart_lt {a d k N : ℕ} (hbound : a + (k - 1) * d < N) : a < N := by
  omega

theorem MonoAP.recolor {α : Type uAlpha} {β : Type uBeta} {c : ℕ → α} {k a d : ℕ}
    (h : MonoAP c k a d) (f : α → β) : MonoAP (f ∘ c) k a d := by
  intro j hj
  exact congrArg f (h j hj)

theorem MonoAP.of_injective_recolor {α : Type uAlpha} {β : Type uBeta} {c : ℕ → α}
    {k a d : ℕ} {f : α → β} (hf : Function.Injective f)
    (h : MonoAP (f ∘ c) k a d) : MonoAP c k a d := by
  intro j hj
  exact hf (h j hj)

theorem HasMonoAP.recolor {α : Type uAlpha} {β : Type uBeta} {c : ℕ → α} {k N : ℕ}
    (h : HasMonoAP c k N) (f : α → β) : HasMonoAP (f ∘ c) k N := by
  obtain ⟨a, d, hd, hb, hm⟩ := h
  exact ⟨a, d, hd, hb, hm.recolor f⟩

theorem HasMonoAP.of_injective_recolor {α : Type uAlpha} {β : Type uBeta} {c : ℕ → α}
    {k N : ℕ} {f : α → β} (hf : Function.Injective f)
    (h : HasMonoAP (f ∘ c) k N) : HasMonoAP c k N := by
  obtain ⟨a, d, hd, hb, hm⟩ := h
  exact ⟨a, d, hd, hb, hm.of_injective_recolor hf⟩

theorem not_hasMonoAP_of_recolor_injective {α : Type uAlpha} {β : Type uBeta} {c : ℕ → α}
    {k N : ℕ} {f : α → β} (hf : Function.Injective f)
    (hc : ¬ HasMonoAP c k N) : ¬ HasMonoAP (f ∘ c) k N :=
  fun h => hc (h.of_injective_recolor hf)

theorem HasMonoAP.mono {α : Type uAlpha} {c : ℕ → α} {k N M : ℕ}
    (h : HasMonoAP c k N) (hNM : N ≤ M) : HasMonoAP c k M := by
  obtain ⟨a, d, hd, hb, hm⟩ := h
  exact ⟨a, d, hd, hb.trans_le hNM, hm⟩

theorem HasMonoAP.mono_length {α : Type uAlpha} {c : ℕ → α} {k l N : ℕ}
    (h : HasMonoAP c k N) (hlk : l ≤ k) : HasMonoAP c l N := by
  obtain ⟨a, d, hd, hb, hm⟩ := h
  have hpred : l - 1 ≤ k - 1 := by omega
  have hmul := Nat.mul_le_mul_right d hpred
  refine ⟨a, d, hd, by omega, ?_⟩
  intro j hj
  exact hm j (hj.trans_le hlk)

theorem HasMonoAP.length_le {α : Type uAlpha} {c : ℕ → α} {k N : ℕ}
    (h : HasMonoAP c k N) (hk : 0 < k) : k ≤ N := by
  obtain ⟨a, d, hd, hb, _⟩ := h
  have hmul : k - 1 ≤ (k - 1) * d := by
    simpa using Nat.mul_le_mul_left (k - 1) (show 1 ≤ d by omega)
  omega

theorem HasMonoAP.congr {α : Type uAlpha} {c c' : ℕ → α} {k N : ℕ}
    (h : HasMonoAP c k N) (heq : ∀ n < N, c n = c' n) :
    HasMonoAP c' k N := by
  obtain ⟨a, d, hd, hb, hm⟩ := h
  refine ⟨a, d, hd, hb, ?_⟩
  intro j hj
  rw [← heq _ (apTerm_lt hb hj), ← heq _ (apStart_lt hb)]
  exact hm j hj

theorem HasMonoAP.translate {α : Type uAlpha} {c : ℕ → α} {k N offset : ℕ}
    (h : HasMonoAP (fun n => c (offset + n)) k N) :
    HasMonoAP c k (offset + N) := by
  obtain ⟨a, d, hd, hb, hm⟩ := h
  refine ⟨offset + a, d, hd, by omega, ?_⟩
  intro j hj
  simpa only [Nat.add_assoc] using hm j hj

theorem IsRamsey.mono {α : Type uAlpha} {k N M : ℕ}
    (h : IsRamsey α k N) (hNM : N ≤ M) : IsRamsey α k M :=
  fun c => (h c).mono hNM

theorem IsRamsey.of_injective {α : Type uAlpha} {β : Type uBeta} {k N : ℕ}
    (h : IsRamsey β k N) {f : α → β} (hf : Function.Injective f) :
    IsRamsey α k N := by
  intro c
  exact (h (f ∘ c)).of_injective_recolor hf

theorem isRamsey_one (α : Type uAlpha) : IsRamsey α 1 1 := by
  intro c
  refine ⟨0, 1, by omega, by norm_num, ?_⟩
  intro j hj
  have : j = 0 := by omega
  simp [this]

theorem isRamsey_subsingleton (α : Type uAlpha) [Subsingleton α] {k : ℕ}
    (hk : 0 < k) : IsRamsey α k k := by
  intro c
  refine ⟨0, 1, by omega, by omega, ?_⟩
  exact fun _ _ => Subsingleton.elim _ _

/-- A literal finite-coloring formulation of the same progression. -/
def FiniteHasMonoAP {α : Type uAlpha} {N : ℕ} (c : Fin N → α) (k : ℕ) : Prop :=
  ∃ a d, 0 < d ∧ ∃ hbound : a + (k - 1) * d < N,
    ∀ j : Fin k,
      c ⟨a + j.val * d, apTerm_lt hbound j.isLt⟩ =
        c ⟨a, apStart_lt hbound⟩

def restrictColor {α : Type uAlpha} (c : ℕ → α) (N : ℕ) : Fin N → α :=
  fun n => c n.val

theorem hasMonoAP_iff_finite_restriction {α : Type uAlpha} (c : ℕ → α) (k N : ℕ) :
    HasMonoAP c k N ↔ FiniteHasMonoAP (restrictColor c N) k := by
  constructor
  · rintro ⟨a, d, hd, hb, hm⟩
    exact ⟨a, d, hd, hb, fun j => hm j.val j.isLt⟩
  · rintro ⟨a, d, hd, hb, hm⟩
    exact ⟨a, d, hd, hb, fun j hj => hm ⟨j, hj⟩⟩

/-- Only the finitely many colors on `[0,N)` matter. The nonempty color type
allows every finite coloring to be extended beyond that interval. -/
theorem isRamsey_iff_finite (α : Type uAlpha) [Nonempty α] (k N : ℕ) :
    IsRamsey α k N ↔ ∀ c : Fin N → α, FiniteHasMonoAP c k := by
  classical
  constructor
  · intro h c
    let extended : ℕ → α := fun n =>
      if hn : n < N then c ⟨n, hn⟩ else Classical.choice ‹Nonempty α›
    have hc := (hasMonoAP_iff_finite_restriction extended k N).mp (h extended)
    have heq : restrictColor extended N = c := by
      funext n
      simp [restrictColor, extended, n.isLt]
    rwa [heq] at hc
  · intro h c
    exact (hasMonoAP_iff_finite_restriction c k N).mpr (h (restrictColor c N))

theorem W_le_of_isRamsey {r k N : ℕ} (hN : 0 < N)
    (h : IsRamsey (Fin r) k N) : W r k ≤ N :=
  Nat.sInf_le ⟨hN, h⟩

theorem W_spec_of_finite {r k : ℕ}
    (hfinite : ∃ N, 0 < N ∧ IsRamsey (Fin r) k N) :
    0 < W r k ∧ IsRamsey (Fin r) k (W r k) :=
  Nat.sInf_mem hfinite

/-- An avoiding coloring gives a strict lower bound once finiteness has been
proved. Monotonicity is used: failure at one size alone is not minimality. -/
theorem lt_W_of_avoiding {r k N : ℕ}
    (hfinite : ∃ M, 0 < M ∧ IsRamsey (Fin r) k M)
    (c : ℕ → Fin r) (hc : ¬ HasMonoAP c k N) : N < W r k := by
  have hw := W_spec_of_finite hfinite
  by_contra hn
  exact hc ((hw.2.mono (by omega)) c)

theorem lt_W_of_not_isRamsey {r k N : ℕ}
    (hfinite : ∃ M, 0 < M ∧ IsRamsey (Fin r) k M)
    (hN : ¬ IsRamsey (Fin r) k N) : N < W r k := by
  have hw := W_spec_of_finite hfinite
  by_contra hn
  exact hN (hw.2.mono (by omega))

theorem W_one (r : ℕ) : W r 1 = 1 := by
  have hw := W_spec_of_finite (r := r) ⟨1, by omega, isRamsey_one (Fin r)⟩
  have hu := W_le_of_isRamsey (r := r) (by omega : 0 < 1) (isRamsey_one (Fin r))
  omega

theorem W_one_color {k : ℕ} (hk : 0 < k) : W 1 k = k := by
  have hramsey := isRamsey_subsingleton (Fin 1) hk
  have hw := W_spec_of_finite (r := 1) ⟨k, hk, hramsey⟩
  have hu := W_le_of_isRamsey hk hramsey
  have hl := (hw.2 (fun _ => (0 : Fin 1))).length_le hk
  omega

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# The digit-product transfer

For a cyclic avoiding coloring modulo `N`, color an integer by the colors of
its first `m` base-`N` digits. The first nonzero digit of a positive common
difference supplies a nonzero cyclic step. The arithmetic proof uses finite
divisibility, so it applies to composite bases as well as prime bases.

The explicit avoiding-coloring theorems are unconditional. Statements about
`W` consume the genuine finite Ramsey witness, supplied by `UpperBound` at
the final assembly; finiteness is not built into the definition of `W`.
-/


namespace QuantitativeVanDerWaerden

/-- Select the last dividing base power below a positive difference bound.
No primality assumption is needed. -/
theorem exists_base_factor {N d m : ℕ} (hd : 0 < d) (hbound : d < N ^ m) :
    ∃ i < m, ∃ e, d = N ^ i * e ∧ ¬ N ∣ e := by
  have hnot : ¬ N ^ m ∣ d := by
    intro h
    exact (not_le_of_gt hbound) (Nat.le_of_dvd hd h)
  let hex : ∃ t : ℕ, ¬ N ^ t ∣ d := ⟨m, hnot⟩
  have ht_le : Nat.find hex ≤ m := Nat.find_min' hex hnot
  have ht_pos : 0 < Nat.find hex := by
    by_contra h
    have ht_zero : Nat.find hex = 0 := by omega
    have hdvd : N ^ Nat.find hex ∣ d := by rw [ht_zero]; simp
    exact Nat.find_spec hex hdvd
  let i := Nat.find hex - 1
  have hi : i < Nat.find hex := by dsimp [i]; omega
  have hi_succ : i + 1 = Nat.find hex := by dsimp [i]; omega
  have hdiv : N ^ i ∣ d := by
    by_contra h
    exact Nat.find_min hex hi h
  obtain ⟨e, he⟩ := hdiv
  refine ⟨i, by omega, e, he, ?_⟩
  rintro ⟨q, hq⟩
  apply Nat.find_spec hex
  refine ⟨q, ?_⟩
  rw [← hi_succ, pow_succ, he, hq]
  exact (Nat.mul_assoc (N ^ i) N q).symm

/-- Exact quotient arithmetic at a coordinate whose base power divides the
common difference. This is the entire carry argument. -/
theorem div_ap_of_base_factor {N d i e : ℕ} (hN : 0 < N)
    (hd : d = N ^ i * e) (a j : ℕ) :
    (a + j * d) / N ^ i = a / N ^ i + j * e := by
  rw [hd, Nat.mul_left_comm j (N ^ i) e]
  exact Nat.add_mul_div_left a (j * e) (pow_pos hN i)

/-- A digit is identified with its residue, so an extra remainder is redundant. -/
def digitColor {N : ℕ} {α : Type uAlpha} (C : ZMod N → α) (m : ℕ) :
    ℕ → (Fin m → α) :=
  fun n i => C ((n / N ^ i.val : ℕ) : ZMod N)

theorem digitColor_avoids {N k m : ℕ} {α : Type uAlpha} {C : ZMod N → α}
    (hN : 2 ≤ N) (hk : 2 ≤ k) (hC : CyclicAvoids C k) :
    ¬ HasMonoAP (digitColor C m) k (N ^ m) := by
  rintro ⟨a, d, hd, hbound, hmono⟩
  have hd_le : d ≤ (k - 1) * d := by
    simpa using Nat.mul_le_mul_right d (show 1 ≤ k - 1 by omega)
  have hd_bound : d < N ^ m := by omega
  obtain ⟨i, him, e, hde, he⟩ := exists_base_factor hd hd_bound
  have he_nonzero : (e : ZMod N) ≠ 0 := by
    intro hz
    exact he ((ZMod.natCast_eq_zero_iff e N).mp hz)
  apply hC ((a / N ^ i : ℕ) : ZMod N) (e : ZMod N) he_nonzero
  intro j hj
  have hcoord := congrFun (hmono j hj) (⟨i, him⟩ : Fin m)
  change C (((a + j * d) / N ^ i : ℕ) : ZMod N) =
    C ((a / N ^ i : ℕ) : ZMod N) at hcoord
  rw [div_ap_of_base_factor (by omega : 0 < N) hde a j] at hcoord
  simpa only [Nat.cast_add, Nat.cast_mul] using hcoord

/-- Explicit recoloring into any sufficiently large standard finite palette. -/
noncomputable def finiteColorEmbedding {α : Type uAlpha} [Fintype α] {r : ℕ}
    (h : Fintype.card α ≤ r) : α ↪ Fin r :=
  (Fintype.equivFin α).toEmbedding.trans (Fin.castLEEmb h)

theorem exists_digit_product_avoiding {N k m r : ℕ} {α : Type uAlpha} [Fintype α]
    {C : ZMod N → α} (hN : 2 ≤ N) (hk : 2 ≤ k) (hC : CyclicAvoids C k)
    (hcolors : Fintype.card α ^ m ≤ r) :
    ∃ c : ℕ → Fin r, ¬ HasMonoAP c k (N ^ m) := by
  classical
  have hcard : Fintype.card (Fin m → α) ≤ r := by
    rwa [Fintype.card_pi_const]
  let e := finiteColorEmbedding hcard
  refine ⟨e ∘ digitColor C m, ?_⟩
  exact not_hasMonoAP_of_recolor_injective e.injective (digitColor_avoids hN hk hC)

theorem digit_product_not_isRamsey {N k m r : ℕ} {α : Type uAlpha} [Fintype α]
    {C : ZMod N → α} (hN : 2 ≤ N) (hk : 2 ≤ k) (hC : CyclicAvoids C k)
    (hcolors : Fintype.card α ^ m ≤ r) : ¬ IsRamsey (Fin r) k (N ^ m) := by
  obtain ⟨c, hc⟩ := exists_digit_product_avoiding hN hk hC hcolors
  exact fun h => hc (h c)

/-- The finite witness is provided by the proved upper-bound construction. -/
theorem digit_product_lt_W {N k m r : ℕ} {α : Type uAlpha} [Fintype α]
    {C : ZMod N → α} (hN : 2 ≤ N) (hk : 2 ≤ k) (hC : CyclicAvoids C k)
    (hcolors : Fintype.card α ^ m ≤ r)
    (hfinite : ∃ M, 0 < M ∧ IsRamsey (Fin r) k M) : N ^ m < W r k := by
  exact lt_W_of_not_isRamsey hfinite (digit_product_not_isRamsey hN hk hC hcolors)

theorem binary_digit_product_lt_W {N k m : ℕ} {C : ZMod N → Bool}
    (hN : 2 ≤ N) (hk : 2 ≤ k) (hC : CyclicAvoids C k)
    (hfinite : ∃ M, 0 < M ∧ IsRamsey (Fin (2 ^ m)) k M) :
    N ^ m < W (2 ^ m) k := by
  apply digit_product_lt_W hN hk hC _ hfinite
  simp

theorem binary_digit_product_log_lt_W {N k r : ℕ} {C : ZMod N → Bool}
    (hN : 2 ≤ N) (hk : 2 ≤ k) (hr : 2 ≤ r) (hC : CyclicAvoids C k)
    (hfinite : ∃ M, 0 < M ∧ IsRamsey (Fin r) k M) :
    N ^ Nat.log 2 r < W r k := by
  apply digit_product_lt_W hN hk hC _ hfinite
  simpa using Nat.pow_log_le_self 2 (show r ≠ 0 by omega)

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI


namespace QuantitativeVanDerWaerden

/-- The inner recursion, with the bound for the preceding length supplied. -/
def focusSize (previous : ℕ → ℕ) (r : ℕ) : ℕ → ℕ
  | 0 => 1
  | t + 1 => 2 * focusSize previous r t * previous (r ^ focusSize previous r t)

/-- Length is the recursion argument; all color counts at the previous
length are available before the next length is constructed. -/
def Fcore : ℕ → ℕ → ℕ
  | 0, _ => 1
  | 1, _ => 1
  | 2, r => r + 1
  | k + 3, r => focusSize (Fcore (k + 2)) r r

def F (r k : ℕ) : ℕ := Fcore k r

@[simp] theorem F_one (r : ℕ) : F r 1 = 1 := rfl
@[simp] theorem F_two (r : ℕ) : F r 2 = r + 1 := rfl
theorem F_recursion (r k : ℕ) :
    F r (k + 3) = focusSize (fun q => F q (k + 2)) r r := rfl

theorem focusSize_pos {previous : ℕ → ℕ} {r : ℕ}
    (hp : ∀ q, 0 < q → 0 < previous q) (hr : 0 < r) (t : ℕ) :
    0 < focusSize previous r t := by
  induction t with
  | zero => exact Nat.zero_lt_one
  | succ t ih =>
    exact Nat.mul_pos (Nat.mul_pos (by decide) ih) (hp _ (pow_pos hr _))

theorem Fcore_pos (k : ℕ) : ∀ r, 0 < r → 0 < Fcore k r := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | _ | k
    · intro r hr; exact Nat.zero_lt_one
    · intro r hr; exact Nat.zero_lt_one
    · intro r hr; exact Nat.zero_lt_succ r
    · intro r hr
      exact focusSize_pos (ih (k + 2) (by omega)) hr r

theorem F_pos {r k : ℕ} (hr : 0 < r) : 0 < F r k := Fcore_pos k r hr

private theorem hasMonoAP_two_of_lt {α : Type uAlpha} {c : ℕ → α} {a b N : ℕ}
    (hab : a < b) (hb : b < N) (hc : c a = c b) : HasMonoAP c 2 N := by
  refine ⟨a, b - a, by omega, by simpa [Nat.add_sub_of_le (Nat.le_of_lt hab)] using hb, ?_⟩
  intro j hj
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · simp
  · simpa [Nat.add_sub_of_le (Nat.le_of_lt hab)] using hc.symm

theorem isRamsey_two (α : Type uAlpha) [Fintype α] :
    IsRamsey α 2 (Fintype.card α + 1) := by
  classical
  intro c
  obtain ⟨a, b, hab, hc⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun n : Fin (Fintype.card α + 1) => c n.val) (by simp)
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hasMonoAP_two_of_lt hlt b.isLt hc
  · exact hasMonoAP_two_of_lt hlt a.isLt hc.symm

/-- A focus with distinct arm colors. The arms have length `k - 1`, and
adding their common next point would give a progression of length `k`. -/
structure Focus {α : Type uAlpha} (c : ℕ → α) (k N t : ℕ) where
  point : ℕ
  point_lt : point < N
  start : Fin t → ℕ
  step : Fin t → ℕ
  step_pos : ∀ i, 0 < step i
  ends : ∀ i, start i + (k - 1) * step i = point
  mono : ∀ i, MonoAP c (k - 1) (start i) (step i)
  colors_injective : Function.Injective (fun i => c (start i))

theorem Focus.color_ne {α : Type uAlpha} {c : ℕ → α} {k N t : ℕ}
    (f : Focus c k N t) (ha : ¬ HasMonoAP c k N) (i : Fin t) :
    c f.point ≠ c (f.start i) := by
  intro he
  apply ha
  refine ⟨f.start i, f.step i, f.step_pos i, ?_, ?_⟩
  · rw [f.ends i]; exact f.point_lt
  · intro j hj
    by_cases h : j < k - 1
    · exact f.mono i j h
    · have hj' : j = k - 1 := by omega
      rw [hj', f.ends i]
      exact he

private theorem fin_cases_injective {α : Type uAlpha} {t : ℕ} {a : α} {g : Fin t → α}
    (hg : Function.Injective g) (ha : ∀ i, a ≠ g i) :
    Function.Injective (Fin.cases a g) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro _; rfl
    · intro hij; exact False.elim (ha j hij)
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hij; exact False.elim (ha i hij.symm)
    · intro hij; exact congrArg Fin.succ (hg hij)

theorem Focus.impossible {α : Type uAlpha} [Fintype α] {c : ℕ → α} {k N : ℕ}
    (f : Focus c k N (Fintype.card α)) (ha : ¬ HasMonoAP c k N) : False := by
  have h := Fintype.card_le_of_injective
    (Fin.cases (c f.point) (fun i => c (f.start i)))
    (fin_cases_injective f.colors_injective (f.color_ne ha))
  simp only [Fintype.card_fin] at h
  omega

def blockWord {α : Type uAlpha} (c : ℕ → α) (m b : ℕ) : Fin m → α :=
  fun x => c (b * m + x.val)

private theorem matching_point {α : Type uAlpha} {c : ℕ → α} {m k b d j x : ℕ}
    (h : MonoAP (blockWord c m) k b d) (hj : j < k) (hx : x < m) :
    c ((b + j * d) * m + x) = c (b * m + x) :=
  congrFun (h j hj) ⟨x, hx⟩

/-- The next block is allocated, even though its word need not match. -/
private theorem next_block_lt {k b d B : ℕ} (hk : 3 ≤ k)
    (hb : b + (k - 2) * d < B) : b + (k - 1) * d < 2 * B := by
  have hpred : k - 1 = (k - 2) + 1 := by omega
  have hd : d ≤ (k - 2) * d := by
    simpa using Nat.mul_le_mul_right d (show 1 ≤ k - 2 by omega)
  rw [hpred, Nat.add_mul, one_mul]
  omega

/-- Copy the old arms into matching blocks and add the arm supplied by
the old focus. All positions and differences are kept explicitly. -/
theorem focus_lift {α : Type uAlpha} {c : ℕ → α} {k m B b d t : ℕ}
    (hk : 3 ≤ k) (hm : 0 < m) (hd : 0 < d)
    (hb : b + (k - 2) * d < B)
    (hw : MonoAP (blockWord c m) (k - 1) b d)
    (old : Focus (fun x => c (b * m + x)) k m t)
    (ha : ¬ HasMonoAP (fun x => c (b * m + x)) k m) :
    Nonempty (Focus c k (2 * m * B) (t + 1)) := by
  let q := b + (k - 1) * d
  have hq : q < 2 * B := next_block_lt hk hb
  have hpoint : q * m + old.point < 2 * m * B := by
    calc
      q * m + old.point < q * m + m := Nat.add_lt_add_left old.point_lt _
      _ = (q + 1) * m := by ring
      _ ≤ (2 * B) * m := Nat.mul_le_mul_right m (by omega)
      _ = 2 * m * B := by ring
  let starts : Fin (t + 1) → ℕ :=
    Fin.cases (b * m + old.point) (fun i => b * m + old.start i)
  let steps : Fin (t + 1) → ℕ :=
    Fin.cases (m * d) (fun i => m * d + old.step i)
  refine ⟨{
    point := q * m + old.point
    point_lt := hpoint
    start := starts
    step := steps
    step_pos := ?_
    ends := ?_
    mono := ?_
    colors_injective := ?_ }⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Nat.mul_pos hm hd
    · exact Nat.lt_of_lt_of_le (old.step_pos i) (Nat.le_add_left _ _)
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · dsimp [starts, steps, q]; ring
    · change b * m + old.start i + (k - 1) * (m * d + old.step i) = _
      calc
        _ = q * m + (old.start i + (k - 1) * old.step i) := by dsimp [q]; ring
        _ = q * m + old.point := by rw [old.ends i]
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j hj
      change c (b * m + old.point + j * (m * d)) = c (b * m + old.point)
      rw [show b * m + old.point + j * (m * d) =
        (b + j * d) * m + old.point by ring]
      exact matching_point hw hj old.point_lt
    · intro j hj
      have hx : old.start i + j * old.step i < m := by
        have hle := Nat.mul_le_mul_right (old.step i) (show j ≤ k - 1 by omega)
        have he := old.ends i
        have hp := old.point_lt
        omega
      change c (b * m + old.start i + j * (m * d + old.step i)) =
        c (b * m + old.start i)
      rw [show b * m + old.start i + j * (m * d + old.step i) =
        (b + j * d) * m + (old.start i + j * old.step i) by ring]
      exact (matching_point hw hj hx).trans (old.mono i j hj)
  · have hi := fin_cases_injective old.colors_injective (old.color_ne ha)
    have he (i : Fin (t + 1)) : c (starts i) =
        Fin.cases (c (b * m + old.point)) (fun i => c (b * m + old.start i)) i := by
      refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
    intro i j hij
    exact hi ((he i).symm.trans (hij.trans (he j)))

/-- The inner focusing induction, simultaneously for every finite color
type so that complete block words can themselves serve as colors. -/
theorem focusing {α : Type u} [Fintype α] {previous : ℕ → ℕ} {k : ℕ}
    (hk : 3 ≤ k) (hr : 0 < Fintype.card α)
    (hp : ∀ r, 0 < r → 0 < previous r)
    (hprevious : ∀ (β : Type u) [Fintype β], 0 < Fintype.card β →
      IsRamsey β (k - 1) (previous (Fintype.card β))) :
    ∀ (t : ℕ) (c : ℕ → α),
      ¬ HasMonoAP c k (focusSize previous (Fintype.card α) t) →
      Nonempty (Focus c k (focusSize previous (Fintype.card α) t) t) := by
  classical
  intro t
  induction t with
  | zero =>
    intro c ha
    exact ⟨{
      point := 0
      point_lt := Nat.zero_lt_one
      start := Fin.elim0
      step := Fin.elim0
      step_pos := fun i => Fin.elim0 i
      ends := fun i => Fin.elim0 i
      mono := fun i => Fin.elim0 i
      colors_injective := fun i => Fin.elim0 i }⟩
  | succ t ih =>
    intro c ha
    let m := focusSize previous (Fintype.card α) t
    let B := previous (Fintype.card α ^ m)
    have hm : 0 < m := focusSize_pos hp hr t
    have hcard : Fintype.card (Fin m → α) = Fintype.card α ^ m := by
      simp only [Fintype.card_fun, Fintype.card_fin]
    have hwc := hprevious (Fin m → α) (by rw [hcard]; exact pow_pos hr m)
    rw [hcard] at hwc
    obtain ⟨b, d, hd, hb, hw⟩ := hwc (blockWord c m)
    have hb' : b + (k - 2) * d < B := by
      simpa only [Nat.sub_sub] using hb
    have hstart : b < B := by omega
    have hinside : b * m + m ≤ 2 * m * B := by
      calc
        b * m + m = (b + 1) * m := by ring
        _ ≤ B * m := Nat.mul_le_mul_right m (by omega)
        _ ≤ (2 * B) * m := Nat.mul_le_mul_right m (by omega)
        _ = 2 * m * B := by ring
    have havoid : ¬ HasMonoAP (fun x => c (b * m + x)) k m := by
      intro h
      apply ha
      exact h.translate.mono hinside
    obtain ⟨old⟩ := ih (fun x => c (b * m + x)) havoid
    exact focus_lift hk hm hd hb' hw old havoid

theorem isRamsey_Fcore (k : ℕ) (hk : 0 < k) :
    ∀ (α : Type u) [Fintype α], 0 < Fintype.card α →
      IsRamsey α k (Fcore k (Fintype.card α)) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | _ | k
    · omega
    · intro α _ hr; exact isRamsey_one α
    · intro α _ hr; exact isRamsey_two α
    · intro α _ hr c
      classical
      by_contra ha
      have hprev : ∀ (β : Type u) [Fintype β], 0 < Fintype.card β →
          IsRamsey β (k + 3 - 1) (Fcore (k + 2) (Fintype.card β)) := by
        intro β _ hβ
        simpa using ih (k + 2) (by omega) (by omega) β hβ
      obtain ⟨f⟩ := focusing (k := k + 3) (by omega) hr
        (Fcore_pos (k + 2)) hprev (Fintype.card α) c ha
      exact f.impossible ha

theorem isRamsey_F (α : Type uAlpha) [Fintype α] {k : ℕ}
    (hk : 0 < k) (hr : 0 < Fintype.card α) :
    IsRamsey α k (F (Fintype.card α) k) := isRamsey_Fcore k hk α hr

/-- Unconditional finiteness for every positive color count and length. -/
theorem finite_ramsey {r k : ℕ} (hr : 0 < r) (hk : 0 < k) :
    ∃ N, 0 < N ∧ IsRamsey (Fin r) k N := by
  refine ⟨F r k, F_pos hr, ?_⟩
  simpa only [Fintype.card_fin] using isRamsey_F (Fin r) hk (by simpa using hr)

theorem W_le_F {r k : ℕ} (hr : 0 < r) (hk : 0 < k) : W r k ≤ F r k := by
  apply W_le_of_isRamsey (F_pos hr)
  simpa only [Fintype.card_fin] using isRamsey_F (Fin r) hk (by simpa using hr)

theorem W_spec {r k : ℕ} (hr : 0 < r) (hk : 0 < k) :
    0 < W r k ∧ IsRamsey (Fin r) k (W r k) := W_spec_of_finite (finite_ramsey hr hk)

theorem W_two {r : ℕ} (hr : 0 < r) : W r 2 = r + 1 := by
  let c : ℕ → Fin r := fun n => ⟨n % r, Nat.mod_lt n hr⟩
  have ha : ¬ HasMonoAP c 2 r := by
    rintro ⟨a, d, hd, hb, hm⟩
    have hb' : a + d < r := by simpa using hb
    have ha' : a < r := by omega
    have he := congrArg Fin.val (hm 1 (by omega))
    dsimp [c] at he
    simp only [one_mul, Nat.mod_eq_of_lt hb', Nat.mod_eq_of_lt ha'] at he
    omega
  have hl := lt_W_of_avoiding (finite_ramsey hr (by omega : 0 < 2)) c ha
  have hu := W_le_F hr (by omega : 0 < 2)
  rw [F_two] at hu
  omega

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

namespace QuantitativeVanDerWaerden

/-- The product of any number of copies of one cyclic Boolean coloring. -/
theorem cyclic_binary_product_lower {N k m : ℕ} {C : ZMod N → Bool}
    (hN : 2 ≤ N) (hk : 2 ≤ k) (hC : CyclicAvoids C k) :
    N ^ m < W (2 ^ m) k := by
  exact binary_digit_product_lt_W hN hk hC
    (finite_ramsey (pow_pos (by decide : 0 < (2 : ℕ)) m) (by omega))

theorem cyclic_binary_color_lower {N k r : ℕ} {C : ZMod N → Bool}
    (hN : 2 ≤ N) (hk : 2 ≤ k) (hr : 2 ≤ r) (hC : CyclicAvoids C k) :
    N ^ Nat.log 2 r < W r k := by
  exact binary_digit_product_log_lt_W hN hk hr hC
    (finite_ramsey (by omega) (by omega))

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

namespace QuantitativeVanDerWaerden

open Filter

/-- The integer logarithm in the product construction is the floor of the
real base-two logarithm. -/
theorem natLog_two_eq_floor_log (r : ℕ) :
    Nat.log 2 r = ⌊Real.log (r : ℝ) / Real.log 2⌋₊ := by
  simpa [Real.logb] using (Real.natFloor_logb_natCast 2 r).symm

/-- A uniform lower estimate for the number of usable binary digits. -/
theorem log_div_two_log_two_le_natLog {r : ℕ} (hr : 2 ≤ r) :
    Real.log (r : ℝ) / (2 * Real.log 2) ≤ (Nat.log 2 r : ℝ) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hm : 1 ≤ Nat.log 2 r := Nat.log_pos (by omega) hr
  have hmreal : (1 : ℝ) ≤ (Nat.log 2 r : ℝ) := by exact_mod_cast hm
  have hp : (r : ℝ) < (2 : ℝ) ^ (Nat.log 2 r + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by omega : 1 < 2) r)
  have hupper := Real.log_lt_log hrpos hp
  rw [Real.log_pow] at hupper
  simp only [Nat.cast_add, Nat.cast_one] at hupper
  apply (div_le_iff₀ (mul_pos (by norm_num) hlog)).2
  nlinarith

/-- A bound of the form `k^(a*k)` with positive fixed `a` forces the full
kth-root limit, with no subsequence restriction. -/
theorem tendsto_kthRoot_of_eventually_rpow_bound
    {F : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (h : ∀ᶠ k : ℕ in atTop, (k : ℝ) ^ (a * k) ≤ F k) :
    Tendsto (fun k : ℕ => (F k) ^ (1 / (k : ℝ))) atTop atTop := by
  have hbase : Tendsto (fun k : ℕ => (k : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono' atTop ?_ hbase
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with k hk hkpos
  have hkreal : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  calc
    (k : ℝ) ^ a = ((k : ℝ) ^ (a * k)) ^ (1 / (k : ℝ)) := by
      rw [← Real.rpow_mul hkreal.le]
      congr 1
      field_simp
    _ ≤ (F k) ^ (1 / (k : ℝ)) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hkreal.le _) hk (by positivity)

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI


namespace QuantitativeVanDerWaerden

open Filter

/-- The main real-power lower bound implies a rate uniform in the number
of colors. The color-dependent integer logarithm is estimated explicitly. -/
theorem log_ratio_lower_of_rpow_bound {A c : ℝ} {r k : ℕ}
    (hc : 0 ≤ c) (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hbound : (k : ℝ) ^ (c * k * (Nat.log 2 r : ℝ)) < A) :
    (c / (2 * Real.log 2)) * Real.log (k : ℝ) ≤
      Real.log A / ((k : ℝ) * Real.log (r : ℝ)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hrone : (1 : ℝ) < r := by exact_mod_cast (by omega : 1 < r)
  have hlogr : 0 < Real.log (r : ℝ) := Real.log_pos hrone
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have hlogs := Real.log_lt_log (Real.rpow_pos_of_pos hkpos _) hbound
  rw [Real.log_rpow hkpos] at hlogs
  have hmul :
      c * (k : ℝ) * (Real.log (r : ℝ) / (2 * Real.log 2)) * Real.log (k : ℝ) ≤
        c * (k : ℝ) * (Nat.log 2 r : ℝ) * Real.log (k : ℝ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (log_div_two_log_two_le_natLog hr)
        (mul_nonneg hc hkpos.le)) hlogk
  have hden : 0 < (k : ℝ) * Real.log (r : ℝ) := mul_pos hkpos hlogr
  calc
    (c / (2 * Real.log 2)) * Real.log (k : ℝ) =
        (c * (k : ℝ) * (Real.log (r : ℝ) / (2 * Real.log 2)) *
          Real.log (k : ℝ)) / ((k : ℝ) * Real.log (r : ℝ)) := by
      field_simp
    _ ≤ (c * (k : ℝ) * (Nat.log 2 r : ℝ) * Real.log (k : ℝ)) /
        ((k : ℝ) * Real.log (r : ℝ)) :=
      div_le_div_of_nonneg_right hmul hden.le
    _ ≤ Real.log A / ((k : ℝ) * Real.log (r : ℝ)) :=
      div_le_div_of_nonneg_right hlogs.le hden.le

/-- The large-color exponential lower bound gives a rate independent of
the progression length. -/
theorem log_ratio_lower_of_exp_bound {A r : ℝ} (hr : 1 < r)
    (hbound : Real.exp ((Real.log r) ^ 2 / (64 * Real.log 2)) < A) :
    Real.log r / (64 * Real.log 2) ≤ Real.log A / Real.log r := by
  have hlogr : 0 < Real.log r := Real.log_pos hr
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogs := Real.log_lt_log (Real.exp_pos _) hbound
  rw [Real.log_exp] at hlogs
  apply (le_div_iff₀ hlogr).2
  calc
    (Real.log r / (64 * Real.log 2)) * Real.log r =
        (Real.log r) ^ 2 / (64 * Real.log 2) := by ring
    _ ≤ Real.log A := hlogs.le

/-- A common eventual lower bound proves divergence of the actual real
infima. Nonemptiness is explicit; the common lower bound supplies the
lower-boundedness required by conditional completeness. -/
theorem tendsto_iInf_atTop_of_uniform_lower {ι : Type uIndex} [Nonempty ι]
    {F : ℕ → ι → ℝ} {g : ℕ → ℝ}
    (hg : Tendsto g atTop atTop)
    (h : ∀ᶠ n : ℕ in atTop, ∀ i, g n ≤ F n i) :
    Tendsto (fun n => ⨅ i, F n i) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ hg
  exact h.mono (fun n hn => le_ciInf hn)

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

namespace QuantitativeVanDerWaerden

open Filter

/-- A single threshold for all color counts yields divergence of the actual
infimum over all integers `r ≥ 2`. -/
theorem uniform_length_rate_tendsto
    {F : ℕ → ℕ → ℝ} {c : ℝ} {K : ℕ} (hc : 0 < c)
    (hbound : ∀ k ≥ K, ∀ r ≥ 2,
      (k : ℝ) ^ (c * k * (Nat.log 2 r : ℝ)) < F r k) :
    Tendsto (fun k : ℕ => ⨅ r : {r : ℕ // 2 ≤ r},
      Real.log (F r.val k) / ((k : ℝ) * Real.log (r.val : ℝ))) atTop atTop := by
  let : Nonempty {r : ℕ // 2 ≤ r} := ⟨⟨2, le_rfl⟩⟩
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcoef : 0 < c / (2 * Real.log 2) := by positivity
  apply tendsto_iInf_atTop_of_uniform_lower (hlog.const_mul_atTop hcoef)
  filter_upwards [eventually_ge_atTop (max K 2)] with k hk
  intro r
  exact log_ratio_lower_of_rpow_bound hc.le r.property
    ((le_max_right K 2).trans hk) (hbound k ((le_max_left K 2).trans hk) r.val r.property)

/-- The superpolynomial color estimate is uniform in every progression
length at least three, including the real infimum conclusion. -/
theorem uniform_color_rate_tendsto
    {F : ℕ → ℕ → ℝ} {R : ℕ}
    (hbound : ∀ r ≥ R, ∀ k ≥ 3,
      Real.exp ((Real.log (r : ℝ)) ^ 2 / (64 * Real.log 2)) < F r k) :
    Tendsto (fun r : ℕ => ⨅ k : {k : ℕ // 3 ≤ k},
      Real.log (F r k.val) / Real.log (r : ℝ)) atTop atTop := by
  let : Nonempty {k : ℕ // 3 ≤ k} := ⟨⟨3, le_rfl⟩⟩
  have hlog : Tendsto (fun r : ℕ => Real.log (r : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hden : 0 < (64 : ℝ) * Real.log 2 := by positivity
  apply tendsto_iInf_atTop_of_uniform_lower (hlog.atTop_div_const hden)
  filter_upwards [eventually_ge_atTop (max R 2)] with r hr
  intro k
  have hrone : (1 : ℝ) < r := by
    exact_mod_cast (by have := (le_max_right R 2).trans hr; omega : 1 < r)
  exact log_ratio_lower_of_exp_bound hrone
    (hbound r ((le_max_left R 2).trans hr) k.val k.property)

/-- Every fixed number of colors at least two has the full kth-root limit. -/
theorem fixed_color_kthRoot_tendsto
    {F : ℕ → ℕ → ℝ} {c : ℝ} {K : ℕ} (hc : 0 < c)
    (hbound : ∀ k ≥ K, ∀ r ≥ 2,
      (k : ℝ) ^ (c * k * (Nat.log 2 r : ℝ)) < F r k)
    {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun k : ℕ => (F r k) ^ (1 / (k : ℝ))) atTop atTop := by
  have hm : (0 : ℝ) < (Nat.log 2 r : ℝ) := by
    exact_mod_cast (Nat.log_pos (by omega : 1 < 2) hr)
  apply tendsto_kthRoot_of_eventually_rpow_bound (mul_pos hc hm)
  filter_upwards [eventually_ge_atTop K] with k hk
  simpa only [mul_assoc, mul_left_comm, mul_comm] using (hbound k hk r hr).le

/-- A quadratic logarithmic lower bound dominates every fixed power.
This statement even allows an arbitrary real exponent. -/
theorem polynomial_ratio_tendsto_of_exp_sq_log
    {F : ℕ → ℝ} {C : ℝ} (hC : 0 < C) (A : ℝ)
    (hbound : ∀ᶠ r : ℕ in atTop,
      Real.exp ((Real.log (r : ℝ)) ^ 2 / C) < F r) :
    Tendsto (fun r : ℕ => F r / (r : ℝ) ^ A) atTop atTop := by
  have hlog : Tendsto (fun r : ℕ => Real.log (r : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
  filter_upwards [hbound, eventually_ge_atTop (2 : ℕ),
    hlog.eventually_ge_atTop (C * (A + 1))] with r hb hr hlarge
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hlogr : 0 ≤ Real.log (r : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  have hquad : (A + 1) * Real.log (r : ℝ) ≤ (Real.log (r : ℝ)) ^ 2 / C := by
    apply (le_div_iff₀ hC).2
    nlinarith [mul_nonneg hlogr (sub_nonneg.mpr hlarge)]
  have hpow : (r : ℝ) ^ (A + 1) ≤ F r := by
    calc
      (r : ℝ) ^ (A + 1) = Real.exp (Real.log (r : ℝ) * (A + 1)) :=
        Real.rpow_def_of_pos hrpos _
      _ ≤ Real.exp ((Real.log (r : ℝ)) ^ 2 / C) :=
        Real.exp_le_exp.mpr (by simpa only [mul_comm] using hquad)
      _ ≤ F r := hb.le
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hrpos A)).2
  calc
    (r : ℝ) * (r : ℝ) ^ A = (r : ℝ) ^ (A + 1) := by
      rw [Real.rpow_add hrpos, Real.rpow_one]
      ring
    _ ≤ F r := hpow

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

namespace QuantitativeVanDerWaerden

open Filter

/-- One threshold supplies actual avoiding cyclic colorings independently
of the eventual number of colors. This is a proposition, not an axiom. -/
def CyclicLowerBound (c : ℝ) : Prop :=
  ∃ K : ℕ, ∀ k ≥ K, ∃ N : ℕ,
    2 ≤ N ∧ (k : ℝ) ^ (c * k) ≤ (N : ℝ) ∧
      ∃ C : ZMod N → Bool, CyclicAvoids C k

/-- The same cyclic coloring works for every number of digits. -/
theorem uniform_lower_of_cyclicLowerBound {c : ℝ} (hcyclic : CyclicLowerBound c) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ r ≥ 2,
      (k : ℝ) ^ (c * k * (Nat.log 2 r : ℝ)) < (W r k : ℝ) := by
  obtain ⟨K, hK⟩ := hcyclic
  refine ⟨max K 2, ?_⟩
  intro k hk r hr
  have hk2 : 2 ≤ k := (le_max_right K 2).trans hk
  obtain ⟨N, hN, hsize, C, hC⟩ := hK k ((le_max_left K 2).trans hk)
  have hprod := cyclic_binary_color_lower hN hk2 hr hC
  calc
    (k : ℝ) ^ (c * k * (Nat.log 2 r : ℝ)) =
        ((k : ℝ) ^ (c * k)) ^ Nat.log 2 r :=
      Real.rpow_mul_natCast (Nat.cast_nonneg k) _ _
    _ ≤ (N : ℝ) ^ Nat.log 2 r :=
      pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg k) _) hsize _
    _ < (W r k : ℝ) := by exact_mod_cast hprod

/-- The fixed-color full limit from a proved cyclic construction. -/
theorem kthRoot_tendsto_of_cyclicLowerBound {c : ℝ} (hc : 0 < c)
    (hcyclic : CyclicLowerBound c) {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun k : ℕ => (W r k : ℝ) ^ (1 / (k : ℝ))) atTop atTop := by
  obtain ⟨K, hK⟩ := uniform_lower_of_cyclicLowerBound hcyclic
  exact fixed_color_kthRoot_tendsto (F := fun r k => (W r k : ℝ))
    (c := c) (K := K) (r := r) hc hK hr

/-- The infimum over all color counts retains one absolute threshold. -/
theorem length_rate_tendsto_of_cyclicLowerBound {c : ℝ} (hc : 0 < c)
    (hcyclic : CyclicLowerBound c) :
    Tendsto (fun k : ℕ => ⨅ r : {r : ℕ // 2 ≤ r},
      Real.log (W r.val k : ℝ) / ((k : ℝ) * Real.log (r.val : ℝ))) atTop atTop := by
  obtain ⟨K, hK⟩ := uniform_lower_of_cyclicLowerBound hcyclic
  exact uniform_length_rate_tendsto (F := fun r k => (W r k : ℝ))
    (c := c) (K := K) hc hK

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

namespace QuantitativeVanDerWaerden
namespace LargeColor

open scoped BigOperators

def half (b u : ℕ) : Bool := decide (u < (b + 1) / 2)

/-- The same-half bound is strict for both even and odd bases. -/
theorem half_coefficient_bound {b x y z : ℕ} (_hb : 2 ≤ b)
    (hx : x < b) (hy : y < b) (hz : z < b)
    (hxy : half b x = half b y) (hzy : half b z = half b y) :
    |(x : ℤ) - 2 * y + z| < b := by
  rw [abs_lt]
  by_cases h₁ : x < (b + 1) / 2 <;>
    by_cases h₂ : y < (b + 1) / 2 <;>
    by_cases h₃ : z < (b + 1) / 2 <;>
    simp_all [half] <;> omega

/-- A zero base expansion with signed coefficients strictly smaller than
the base has all coefficients zero. -/
theorem coefficients_zero {b : ℕ} (hb : 2 ≤ b) :
    ∀ {s : ℕ} (a : Fin s → ℤ),
      (∀ i, |a i| < (b : ℤ)) →
      (∑ i, a i * (b : ℤ) ^ (i : ℕ)) = 0 → ∀ i, a i = 0 := by
  intro s
  induction s with
  | zero => intro a ha hs i; exact i.elim0
  | succ s ih =>
    intro a ha hs
    have hsplit : a 0 + (b : ℤ) *
        (∑ i : Fin s, a i.succ * (b : ℤ) ^ (i : ℕ)) = 0 := by
      calc
        _ = ∑ i : Fin (s + 1), a i * (b : ℤ) ^ (i : ℕ) := by
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
          rw [Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = 0 := hs
    have hdiv : (b : ℤ) ∣ a 0 := by
      refine ⟨-(∑ i : Fin s, a i.succ * (b : ℤ) ^ (i : ℕ)), ?_⟩
      linarith [hsplit]
    have hzero : a 0 = 0 := Int.eq_zero_of_abs_lt_dvd hdiv (ha 0)
    have htail : (∑ i : Fin s, a i.succ * (b : ℤ) ^ (i : ℕ)) = 0 := by
      rw [hzero, zero_add] at hsplit
      exact (mul_eq_zero.mp hsplit).resolve_left (by exact_mod_cast (by omega : b ≠ 0))
    intro i
    refine Fin.cases hzero (fun j => ?_) i
    exact ih (fun j : Fin s => a j.succ) (fun j => ha j.succ) htail j

/-- Equal sums of squares and a coordinatewise midpoint force equality. -/
theorem equal_of_midpoint_equal_norm {s : ℕ} (x y z : Fin s → ℤ)
    (hm : ∀ i, x i - 2 * y i + z i = 0)
    (hxy : (∑ i, x i ^ 2) = ∑ i, y i ^ 2)
    (hzy : (∑ i, z i ^ 2) = ∑ i, y i ^ 2) : x = y := by
  have hsq : (∑ i, (x i - z i) ^ 2) = 0 := by
    calc
      _ = ∑ i, (2 * x i ^ 2 + 2 * z i ^ 2 - 4 * y i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hmid : x i + z i = 2 * y i := by linarith [hm i]
        have hmidSq := congrArg (fun t : ℤ => t ^ 2) hmid
        nlinarith [hmidSq]
      _ = 2 * (∑ i, x i ^ 2) + 2 * (∑ i, z i ^ 2) -
          4 * (∑ i, y i ^ 2) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ = 0 := by rw [hxy, hzy]; ring
  funext i
  have hi : (x i - z i) ^ 2 ≤ ∑ j, (x j - z j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j - z j)) (Finset.mem_univ i)
  rw [hsq] at hi
  have hxz : x i = z i := by nlinarith [sq_nonneg (x i - z i)]
  linarith [hm i]

def normSq {b s : ℕ} (x : Fin s → Fin b) : ℕ := ∑ i, (x i).val ^ 2

theorem normSq_le {b s : ℕ} (x : Fin s → Fin b) :
    normSq x ≤ s * (b - 1) ^ 2 := by
  calc
    _ ≤ ∑ _i : Fin s, (b - 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hx : (x i).val ≤ b - 1 := by have := (x i).isLt; omega
      exact Nat.pow_le_pow_left hx 2
    _ = _ := by simp

abbrev Color (b s : ℕ) := (Fin s → Bool) × Fin (s * (b - 1) ^ 2 + 1)

def vectorColor {b s : ℕ} (x : Fin s → Fin b) : Color b s :=
  (fun i => half b (x i).val, ⟨normSq x, Nat.lt_succ_of_le (normSq_le x)⟩)

theorem card_color (b s : ℕ) :
    Fintype.card (Color b s) = 2 ^ s * (s * (b - 1) ^ 2 + 1) := by
  simp [Color]

theorem vector_eq_of_monochromatic_midpoint {b s : ℕ} (hb : 2 ≤ b)
    (x y z : Fin s → Fin b)
    (hxy : vectorColor x = vectorColor y)
    (hzy : vectorColor z = vectorColor y)
    (hm : ((finFunctionFinEquiv x).val : ℤ) -
      2 * (finFunctionFinEquiv y).val + (finFunctionFinEquiv z).val = 0) : x = y := by
  have hhxy : ∀ i, half b (x i).val = half b (y i).val :=
    fun i => congrFun (congrArg Prod.fst hxy) i
  have hhzy : ∀ i, half b (z i).val = half b (y i).val :=
    fun i => congrFun (congrArg Prod.fst hzy) i
  have hnx : normSq x = normSq y := congrArg (fun c : Color b s => c.2.val) hxy
  have hnz : normSq z = normSq y := congrArg (fun c : Color b s => c.2.val) hzy
  change (∑ i, (x i).val ^ 2) = ∑ i, (y i).val ^ 2 at hnx
  change (∑ i, (z i).val ^ 2) = ∑ i, (y i).val ^ 2 at hnz
  have hsum : (∑ i, ((x i).val : ℤ) ^ 2) = ∑ i, ((y i).val : ℤ) ^ 2 := by
    exact_mod_cast hnx
  have hsumz : (∑ i, ((z i).val : ℤ) ^ 2) = ∑ i, ((y i).val : ℤ) ^ 2 := by
    exact_mod_cast hnz
  have hcoeff : ∀ i, ((x i).val : ℤ) - 2 * (y i).val + (z i).val = 0 := by
    apply coefficients_zero hb
      (fun i => ((x i).val : ℤ) - 2 * (y i).val + (z i).val)
    · intro i
      exact half_coefficient_bound hb (x i).isLt (y i).isLt (z i).isLt
        (hhxy i) (hhzy i)
    · simp only [finFunctionFinEquiv_apply, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] at hm
      simpa only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        mul_assoc, ← Finset.mul_sum] using hm
  have heq := equal_of_midpoint_equal_norm
    (fun i => ((x i).val : ℤ)) (fun i => ((y i).val : ℤ))
    (fun i => ((z i).val : ℤ)) hcoeff hsum hsumz
  funext i
  apply Fin.ext
  exact_mod_cast congrFun heq i

def digits (b s : ℕ) (hb : 0 < b) (n : ℕ) : Fin s → Fin b :=
  finFunctionFinEquiv.symm ⟨n % b ^ s, Nat.mod_lt _ (pow_pos hb s)⟩

theorem digits_value {b s : ℕ} (hb : 0 < b) {n : ℕ} (hn : n < b ^ s) :
    (finFunctionFinEquiv (digits b s hb n)).val = n := by
  simp [digits, Nat.mod_eq_of_lt hn]

def coloring (b s : ℕ) (hb : 0 < b) : ℕ → Color b s :=
  fun n => vectorColor (digits b s hb n)

theorem coloring_avoids_three {b s : ℕ} (hb : 2 ≤ b) :
    ¬ HasMonoAP (coloring b s (by omega)) 3 (b ^ s) := by
  rintro ⟨a, d, hd, hbound, hm⟩
  have hbpos : 0 < b := by omega
  have ha : a < b ^ s := apStart_lt hbound
  have ha1 : a + d < b ^ s := by simpa using apTerm_lt hbound (by decide : 1 < 3)
  have ha2 : a + 2 * d < b ^ s := by simpa using apTerm_lt hbound (by decide : 2 < 3)
  have hc1 : coloring b s hbpos (a + d) = coloring b s hbpos a := by
    simpa using hm 1 (by decide)
  have hc2 : coloring b s hbpos (a + 2 * d) = coloring b s hbpos a := by
    simpa using hm 2 (by decide)
  have hvec := vector_eq_of_monochromatic_midpoint hb
    (digits b s hbpos a) (digits b s hbpos (a + d))
    (digits b s hbpos (a + 2 * d)) hc1.symm (hc2.trans hc1.symm) (by
      rw [digits_value hbpos ha, digits_value hbpos ha1, digits_value hbpos ha2]
      push_cast
      ring)
  have heq := congrArg (fun v : Fin s → Fin b => (finFunctionFinEquiv v).val) hvec
  rw [digits_value hbpos ha, digits_value hbpos ha1] at heq
  omega

theorem coloring_avoids {b s k : ℕ} (hb : 2 ≤ b) (hk : 3 ≤ k) :
    ¬ HasMonoAP (coloring b s (by omega)) k (b ^ s) :=
  fun h => coloring_avoids_three hb (h.mono_length hk)

/-- The exact ambient cardinality suffices to recolor into `Fin r`. -/
theorem exists_avoiding {b s k r : ℕ} (hb : 2 ≤ b) (hk : 3 ≤ k)
    (hcolors : 2 ^ s * (s * (b - 1) ^ 2 + 1) ≤ r) :
    ∃ c : ℕ → Fin r, ¬ HasMonoAP c k (b ^ s) := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Color b s) (β := Fin r) (by simpa [card_color] using hcolors)
  exact ⟨e ∘ coloring b s (by omega),
    not_hasMonoAP_of_recolor_injective e.injective (coloring_avoids hb hk)⟩

theorem pow_lt_W {b s k r : ℕ} (hb : 2 ≤ b) (hk : 3 ≤ k)
    (hcolors : 2 ^ s * (s * (b - 1) ^ 2 + 1) ≤ r)
    (hfinite : ∃ M, 0 < M ∧ IsRamsey (Fin r) k M) : b ^ s < W r k := by
  obtain ⟨c, hc⟩ := exists_avoiding hb hk hcolors
  exact lt_W_of_avoiding hfinite c hc

end LargeColor
end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

namespace QuantitativeVanDerWaerden
namespace LargeColor

/-- The ambient color count is bounded by a convenient quartic expression. -/
theorem color_count_le_quartic {b s : ℕ} (hb : 1 ≤ b) :
    2 ^ s * (s * (b - 1) ^ 2 + 1) ≤ (2 ^ s) ^ 2 * b ^ 2 := by
  have hp : (b - 1) ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left (Nat.sub_le b 1) 2
  have hsq : 1 ≤ b ^ 2 := by simpa using Nat.pow_le_pow_left hb 2
  have hs : s + 1 ≤ 2 ^ s := Nat.succ_le_of_lt (Nat.lt_two_pow_self : s < 2 ^ s)
  calc
    _ ≤ 2 ^ s * ((s + 1) * b ^ 2) := by
      apply Nat.mul_le_mul_left
      have hmul := Nat.mul_le_mul_left s hp
      nlinarith
    _ ≤ 2 ^ s * (2 ^ s * b ^ 2) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hs)
    _ = _ := by ring

noncomputable def base (r : ℕ) : ℕ := ⌊Real.exp (Real.log (r : ℝ) / 4)⌋₊

noncomputable def dimension (r : ℕ) : ℕ := ⌊Real.log (r : ℝ) / (4 * Real.log 2)⌋₊

theorem half_le_floor {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hn : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hn' : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hn
  have hlt := Nat.lt_floor_add_one x
  linarith

theorem log_large {r : ℕ} (hr : 256 ≤ r) :
    8 * Real.log 2 ≤ Real.log (r : ℝ) := by
  calc
    _ = Real.log ((2 : ℝ) ^ 8) := by rw [Real.log_pow]; norm_num
    _ ≤ Real.log (r : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hr)

theorem base_le_exp (r : ℕ) :
    (base r : ℝ) ≤ Real.exp (Real.log (r : ℝ) / 4) :=
  Nat.floor_le (Real.exp_pos _).le

theorem base_ge_two {r : ℕ} (hr : 256 ≤ r) : 2 ≤ base r := by
  apply Nat.le_floor
  apply (Real.log_le_iff_le_exp (by norm_num : 0 < (2 : ℝ))).mp
  have hlog := log_large hr
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

theorem dimension_argument_ge_one {r : ℕ} (hr : 256 ≤ r) :
    1 ≤ Real.log (r : ℝ) / (4 * Real.log 2) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ (by positivity : 0 < 4 * Real.log 2)).mpr
  have hlog := log_large hr
  linarith

theorem two_pow_dimension_le {r : ℕ} (hr : 256 ≤ r) :
    (2 : ℝ) ^ dimension r ≤ Real.exp (Real.log (r : ℝ) / 4) := by
  apply (Real.log_le_iff_le_exp (by positivity)).mp
  rw [Real.log_pow]
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : (dimension r : ℝ) ≤ Real.log (r : ℝ) / (4 * Real.log 2) :=
    Nat.floor_le (by linarith [dimension_argument_ge_one hr])
  have hmul := (le_div_iff₀ (by positivity : 0 < 4 * Real.log 2)).mp hs
  nlinarith

theorem parameter_color_count {r : ℕ} (hr : 256 ≤ r) :
    2 ^ dimension r * (dimension r * (base r - 1) ^ 2 + 1) ≤ r := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hfour : Real.exp (Real.log (r : ℝ) / 4) ^ 4 = (r : ℝ) := by
    rw [← Real.exp_nat_mul]
    convert Real.exp_log hrpos using 1
    congr 1
    ring
  have hquart : ((2 : ℝ) ^ dimension r) ^ 2 * (base r : ℝ) ^ 2 ≤ (r : ℝ) := by
    calc
      _ ≤ Real.exp (Real.log (r : ℝ) / 4) ^ 2 *
          Real.exp (Real.log (r : ℝ) / 4) ^ 2 := by
        gcongr
        · exact two_pow_dimension_le hr
        · exact base_le_exp r
      _ = Real.exp (Real.log (r : ℝ) / 4) ^ 4 := by ring
      _ = (r : ℝ) := hfour
  have hnat : (2 ^ dimension r) ^ 2 * base r ^ 2 ≤ r := by exact_mod_cast hquart
  exact (color_count_le_quartic (b := base r) (s := dimension r)
    (by have := base_ge_two hr; omega)).trans hnat

theorem dimension_lower {r : ℕ} (hr : 256 ≤ r) :
    Real.log (r : ℝ) / (8 * Real.log 2) ≤ (dimension r : ℝ) := by
  have htwo : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  calc
    _ = (Real.log (r : ℝ) / (4 * Real.log 2)) / 2 := by
      field_simp [htwo]
      ring
    _ ≤ (dimension r : ℝ) := half_le_floor (dimension_argument_ge_one hr)

theorem log_base_lower {r : ℕ} (hr : 256 ≤ r) :
    Real.log (r : ℝ) / 8 ≤ Real.log (base r : ℝ) := by
  have hb : (2 : ℝ) ≤ (base r : ℝ) := by exact_mod_cast base_ge_two hr
  have ht : 1 ≤ Real.exp (Real.log (r : ℝ) / 4) := by linarith [base_le_exp r]
  have hhalf : Real.exp (Real.log (r : ℝ) / 4) / 2 ≤ (base r : ℝ) :=
    half_le_floor ht
  have hlog := Real.log_le_log (by positivity) hhalf
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hlog
  linarith [log_large hr]

theorem parameter_size {r : ℕ} (hr : 256 ≤ r) :
    Real.exp ((Real.log (r : ℝ)) ^ 2 / (64 * Real.log 2)) ≤
      ((base r ^ dimension r : ℕ) : ℝ) := by
  have hb : 0 < (base r : ℝ) := by exact_mod_cast (by have := base_ge_two hr; omega : 0 < base r)
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  rw [Nat.cast_pow]
  apply (Real.le_log_iff_exp_le (pow_pos hb _)).mp
  rw [Real.log_pow]
  calc
    _ = (Real.log (r : ℝ) / (8 * Real.log 2)) * (Real.log (r : ℝ) / 8) := by
      field_simp
      ring
    _ ≤ (dimension r : ℝ) * Real.log (base r : ℝ) :=
      mul_le_mul (dimension_lower hr) (log_base_lower hr) (by positivity) (by positivity)

theorem exp_bound {r k : ℕ} (hr : 256 ≤ r) (hk : 3 ≤ k) :
    Real.exp ((Real.log (r : ℝ)) ^ 2 / (64 * Real.log 2)) < (W r k : ℝ) := by
  have hnat : base r ^ dimension r < W r k :=
    pow_lt_W (base_ge_two hr) hk (parameter_color_count hr)
      (finite_ramsey (by omega) (by omega))
  exact (parameter_size hr).trans_lt (by exact_mod_cast hnat)

end LargeColor
end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

/-!
# Unconditional growth in the number of colors

These conclusions use the actual digit norm coloring and proved finite upper
bound. They do not assume the uniform two-color construction used for growth
in the progression length.
-/

namespace QuantitativeVanDerWaerden

open Filter

/-- Uniform divergence over every integer progression length at least three. -/
theorem color_rate_tendsto :
    Tendsto (fun r : ℕ => ⨅ k : {k : ℕ // 3 ≤ k},
      Real.log (W r k.val : ℝ) / Real.log (r : ℝ)) atTop atTop := by
  exact uniform_color_rate_tendsto (F := fun r k => (W r k : ℝ)) (R := 256)
    (fun r hr k hk => LargeColor.exp_bound hr hk)

/-- For every fixed progression length at least three, the number grows
faster than every fixed real power of the number of colors. -/
theorem fixed_length_polynomial_ratio_tendsto {k : ℕ} (hk : 3 ≤ k) (A : ℝ) :
    Tendsto (fun r : ℕ => (W r k : ℝ) / (r : ℝ) ^ A) atTop atTop := by
  apply polynomial_ratio_tendsto_of_exp_sq_log
    (F := fun r => (W r k : ℝ)) (C := 64 * Real.log 2) (by positivity) A
  filter_upwards [eventually_ge_atTop (256 : ℕ)] with r hr
  exact LargeColor.exp_bound hr hk

end QuantitativeVanDerWaerden

end OAI
end
end

section
section
namespace OAI

namespace QuantitativeVanDerWaerden

open Filter

/-- An absolute quantitative lower bound, uniform over all color counts. -/
theorem uniform_lower_bound_oai :
    ∃ K : ℕ, ∀ k ≥ K, ∀ r ≥ 2,
      (k : ℝ) ^ ((1 / 100000 : ℝ) * k * (Nat.log 2 r : ℝ)) < (W r k : ℝ) := by
  exact uniform_lower_of_cyclicLowerBound exists_cyclic_coloring

/-- The same bound with the floor of the real base-two logarithm. -/
theorem uniform_lower_bound_floor :
    ∃ K : ℕ, ∀ k ≥ K, ∀ (r : ℕ), r ≥ 2 →
      (k : ℝ) ^ ((1 / 100000 : ℝ) * k *
        (⌊Real.log (r : ℝ) / Real.log 2⌋₊ : ℝ)) < (W r k : ℝ) := by
  obtain ⟨K, hK⟩ := uniform_lower_bound_oai
  refine ⟨K, ?_⟩
  intro k hk r hr
  rw [← natLog_two_eq_floor_log]
  exact hK k hk r hr

/-- The existential-constant formulation, with a single absolute threshold. -/
theorem exists_uniform_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k ≥ K, ∀ r ≥ 2,
      (k : ℝ) ^ (c * k * (Nat.log 2 r : ℝ)) < (W r k : ℝ) := by
  exact ⟨1 / 100000, by norm_num, uniform_lower_bound_oai⟩

/-- For each fixed color count at least two, the full kth-root limit diverges. -/
theorem kthRoot_tendsto {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun k : ℕ => (W r k : ℝ) ^ (1 / (k : ℝ))) atTop atTop := by
  exact kthRoot_tendsto_of_cyclicLowerBound (c := 1 / 100000)
    (by norm_num) exists_cyclic_coloring hr

/-- The actual infimum over every color count at least two diverges. -/
theorem length_rate_tendsto :
    Tendsto (fun k : ℕ => ⨅ r : {r : ℕ // 2 ≤ r},
      Real.log (W r.val k : ℝ) / ((k : ℝ) * Real.log (r.val : ℝ))) atTop atTop := by
  exact length_rate_tendsto_of_cyclicLowerBound (c := 1 / 100000)
    (by norm_num) exists_cyclic_coloring

end QuantitativeVanDerWaerden

end OAI
end
end

theorem solution : type_of% @OAI.QuantitativeVanDerWaerden.uniform_lower_bound_oai := @OAI.QuantitativeVanDerWaerden.uniform_lower_bound_oai
