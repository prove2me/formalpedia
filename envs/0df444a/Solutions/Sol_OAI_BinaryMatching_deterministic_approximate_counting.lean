-- Prove2me | solution 1 for OAI.BinaryMatching.deterministic_approximate_counting
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-24T23:38:05.381736+00:00
-- url     : https://prove2.me/submissions/dd84a001-e4bc-4825-9219-9a1a2b216215

import Mathlib
import Definitions.Def_BinaryMatching
import Definitions.Def_OAIStdSimplexCompat

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

universe u_1 u_2

section
section
namespace OAI


namespace MatchingEntropy
namespace LooplessGraph
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
end LooplessGraph
end MatchingEntropy

namespace BinaryMatching








end BinaryMatching

end OAI
end
end

section
section
namespace OAI

/-!
Probability vectors on finite types, with their convexity and compactness properties.
The function-space simplex is the range of the weights of `Convexity.StdSimplex`.
-/

noncomputable section

open scoped BigOperators

namespace MatchingEntropy

/-- Nonnegative real weights with total mass one. -/
def probabilitySimplex (Index : Type*) [Fintype Index] : Set (Index → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

theorem probabilitySimplex_eq_range (Index : Type*) [Fintype Index] :
    probabilitySimplex Index =
      Set.range (fun simplex : Convexity.StdSimplex ℝ Index ↦ ⇑simplex.weights) := by
  rw [Convexity.StdSimplex.range_toFun_comp_weights]
  ext weights
  simp [probabilitySimplex]

theorem convex_probabilitySimplex (Index : Type*) [Fintype Index] :
    Convex ℝ (probabilitySimplex Index) := by
  intro leftWeights leftMem rightWeights rightMem leftScale rightScale
    leftNonneg rightNonneg total
  constructor
  · intro index
    exact add_nonneg (mul_nonneg leftNonneg (leftMem.1 index))
      (mul_nonneg rightNonneg (rightMem.1 index))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, leftMem.2, rightMem.2, mul_one, total]

theorem single_mem_probabilitySimplex {Index : Type*} [Fintype Index]
    [DecidableEq Index] (index : Index) : Pi.single index 1 ∈ probabilitySimplex Index := by
  constructor
  · intro other
    simp only [Pi.single_apply]
    split <;> norm_num
  · simp

theorem probabilitySimplex_le_one {Index : Type*} [Fintype Index] {weights : Index → ℝ}
    (mem : weights ∈ probabilitySimplex Index) (index : Index) : weights index ≤ 1 := by
  rw [← mem.2]
  exact Finset.single_le_sum (fun other _ ↦ mem.1 other) (Finset.mem_univ index)

theorem isCompact_probabilitySimplex (Index : Type*) [Fintype Index] :
    IsCompact (probabilitySimplex Index) := by
  rw [probabilitySimplex_eq_range]
  exact isCompact_range
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ Index).continuous

end MatchingEntropy

end

end OAI
end
end

section
section
namespace OAI

/-!
Finite loopless multigraphs, perfect matching indicators, and their convex hull.
The edge type distinguishes parallel edges. Feasible laws are probability vectors
on perfect matchings with a prescribed mean.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

instance incidentDecidable (G : LooplessGraph V E) (v : V) (e : E) :
    Decidable (G.Incident v e) := inferInstanceAs (Decidable (G.left e = v ∨ G.right e = v))

def indicator (G : LooplessGraph V E) (M : G.Matching) (e : E) : ℝ :=
  if e ∈ M.val then 1 else 0

def polytope (G : LooplessGraph V E) : Set (E → ℝ) :=
  convexHull ℝ (Set.range G.indicator)

def mean (G : LooplessGraph V E) (p : G.Matching → ℝ) (e : E) : ℝ :=
  ∑ M, p M * G.indicator M e

def feasibleLaws (G : LooplessGraph V E) (y : E → ℝ) : Set (G.Matching → ℝ) :=
  {p | p ∈ probabilitySimplex G.Matching ∧ G.mean p = y}

omit [Fintype V] [Fintype E] [DecidableEq V] in
@[simp] theorem indicator_nonneg (G : LooplessGraph V E) (M : G.Matching) (e : E) :
    0 ≤ G.indicator M e := by
  simp only [indicator]
  split <;> norm_num

omit [Fintype V] [Fintype E] [DecidableEq V] in
@[simp] theorem indicator_le_one (G : LooplessGraph V E) (M : G.Matching) (e : E) :
    G.indicator M e ≤ 1 := by
  simp only [indicator]
  split <;> norm_num

omit [Fintype V] [DecidableEq V] in
theorem continuous_mean (G : LooplessGraph V E) : Continuous G.mean := by
  unfold mean
  fun_prop

def meanLinear (G : LooplessGraph V E) : (G.Matching → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun := G.mean
  map_add' p q := by
    ext e
    simp [mean, add_mul, Finset.sum_add_distrib]
  map_smul' a p := by
    ext e
    simp [mean, mul_assoc, Finset.mul_sum]

omit [Fintype V] [DecidableEq V] in
theorem mean_mem_polytope (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) : G.mean p ∈ G.polytope := by
  have h := (convex_convexHull ℝ (Set.range G.indicator)).sum_mem
    (fun M _ ↦ hp.1 M) hp.2 (fun M _ ↦ subset_convexHull ℝ _ (Set.mem_range_self M))
  have he : G.mean p = ∑ M, p M • G.indicator M := by
    ext e
    simp [mean]
  rw [he]
  exact h

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mean_single (G : LooplessGraph V E) (M : G.Matching) :
    G.mean (Pi.single M 1) = G.indicator M := by
  classical
  ext e
  simp [mean, Pi.single_apply, ite_mul]

omit [Fintype V] [DecidableEq V] in
/-- Exact equivalence between the convex hull of matching indicators and feasible finite laws. -/
theorem mem_polytope_iff (G : LooplessGraph V E) (y : E → ℝ) :
    y ∈ G.polytope ↔ (G.feasibleLaws y).Nonempty := by
  classical
  constructor
  · intro hy
    have hc : Convex ℝ (G.mean '' probabilitySimplex G.Matching) :=
      (convex_probabilitySimplex G.Matching).linear_image G.meanLinear
    have hs : Set.range G.indicator ⊆ G.mean '' probabilitySimplex G.Matching := by
      rintro _ ⟨M, rfl⟩
      exact ⟨Pi.single M 1, single_mem_probabilitySimplex M, G.mean_single M⟩
    obtain ⟨p, hp, rfl⟩ := convexHull_min hs hc hy
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact G.mean_mem_polytope hp

omit [Fintype V] [DecidableEq V] in
theorem compact_feasibleLaws (G : LooplessGraph V E) (y : E → ℝ) :
    IsCompact (G.feasibleLaws y) := by
  exact (isCompact_probabilitySimplex G.Matching).inter_right
    (isClosed_eq G.continuous_mean continuous_const)

omit [Fintype V] [DecidableEq V] in
theorem compact_polytope (G : LooplessGraph V E) : IsCompact G.polytope := by
  have heq : G.polytope = G.mean '' probabilitySimplex G.Matching := by
    ext y
    rw [G.mem_polytope_iff]
    rfl
  rw [heq]
  exact (isCompact_probabilitySimplex G.Matching).image G.continuous_mean


end LooplessGraph

end MatchingEntropy

end

end OAI
end
end

section
section
namespace OAI

/-!
Finite Shannon entropy and attainment of its supremum over feasible matching laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

def marginalEntropy (y : E → ℝ) : ℝ := entropy y

def maxMatchingEntropy (G : LooplessGraph V E) (y : E → ℝ) : ℝ :=
  sSup (entropy '' G.feasibleLaws y)



/-- Shannon entropy is the literal sum of negative probability-log-probability terms. -/
theorem entropy_eq {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    entropy p = -(∑ i, p i * Real.log (p i)) := by
  simp [entropy, Real.negMulLog, Finset.sum_neg_distrib, neg_mul]

theorem continuous_entropy {ι : Type*} [Fintype ι] :
    Continuous (entropy : (ι → ℝ) → ℝ) := by
  unfold entropy
  fun_prop

theorem entropy_nonneg {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) : 0 ≤ entropy p := by
  apply Finset.sum_nonneg
  intro i _
  exact Real.negMulLog_nonneg (hp.1 i)
    (probabilitySimplex_le_one hp i)

/-- The entropy bound used in the counting reduction, including zero probabilities. -/
theorem entropy_le_log_card {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) : entropy p ≤ Real.log (Fintype.card ι) := by
  have hn : 0 < Fintype.card ι := by
    by_contra h
    have hz : Fintype.card ι = 0 := Nat.eq_zero_of_not_pos h
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hz
    simpa using hp.2
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    Real.negMulLog_le_one_sub_self (mul_nonneg hnR.le (hp.1 i)))
  simp_rw [Real.negMulLog_mul] at h
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    hp.2, one_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hp.2] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, sub_self] at h
  change Real.negMulLog (Fintype.card ι) + (Fintype.card ι : ℝ) * entropy p ≤ 0 at h
  rw [Real.negMulLog] at h
  nlinarith

namespace LooplessGraph

omit [Fintype V] [DecidableEq V] in
theorem coordinate_mem_Icc (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) (e : E) : y e ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨p, hp, rfl⟩ := (G.mem_polytope_iff y).mp hy
  constructor
  · exact Finset.sum_nonneg (fun M _ ↦ mul_nonneg (hp.1 M) (G.indicator_nonneg M e))
  · calc
      ∑ M, p M * G.indicator M e ≤ ∑ M, p M * 1 :=
        Finset.sum_le_sum (fun M _ ↦ mul_le_mul_of_nonneg_left (G.indicator_le_one M e) (hp.1 M))
      _ = 1 := by simpa using hp.2


omit [Fintype E] [DecidableEq E] in
/-- Counting the two distinct endpoints; parallel identities are never collapsed. -/
theorem incident_vertex_sum (G : LooplessGraph V E) (e : E) :
    (∑ v, if G.Incident v e then (1 : ℕ) else 0) = 2 := by
  classical
  have he (v : V) : (if G.Incident v e then (1 : ℕ) else 0) =
      (if G.left e = v then 1 else 0) + (if G.right e = v then 1 else 0) := by
    by_cases hl : G.left e = v <;> by_cases hr : G.right e = v
    · exact False.elim (G.loopless e (hl.trans hr.symm))
    · simp [Incident, hl, hr]
    · simp [Incident, hl, hr]
    · simp [Incident, hl, hr]
  simp_rw [he, Finset.sum_add_distrib]
  simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem matching_incident_sum (G : LooplessGraph V E) (M : G.Matching) (v : V) :
    (∑ e ∈ M.val, if G.Incident v e then (1 : ℕ) else 0) = 1 := by
  classical
  obtain ⟨e, ⟨he, hv⟩, hu⟩ := M.property v
  rw [Finset.sum_eq_single e]
  · simp [hv]
  · intro e' he' hne
    have hn : ¬ G.Incident v e' := fun hv' ↦ hne (hu e' ⟨he', hv'⟩)
    simp [hn]
  · simp [he]

omit [Fintype E] [DecidableEq E] in
theorem matching_card_twice (G : LooplessGraph V E) (M : G.Matching) :
    2 * M.val.card = Fintype.card V := by
  classical
  calc
    2 * M.val.card = ∑ e ∈ M.val, ∑ v, if G.Incident v e then (1 : ℕ) else 0 := by
      simp_rw [G.incident_vertex_sum]
      simp [Nat.mul_comm]
    _ = ∑ v, ∑ e ∈ M.val, if G.Incident v e then (1 : ℕ) else 0 := Finset.sum_comm
    _ = Fintype.card V := by
      simp_rw [G.matching_incident_sum]
      simp

omit [Fintype E] [DecidableEq E] in
theorem matching_card (G : LooplessGraph V E) {m : ℕ}
    (hV : Fintype.card V = 2 * m) (M : G.Matching) : M.val.card = m := by
  have h := G.matching_card_twice M
  omega

theorem indicator_sum (G : LooplessGraph V E) {m : ℕ}
    (hV : Fintype.card V = 2 * m) (M : G.Matching) :
    ∑ e, G.indicator M e = (m : ℝ) := by
  simp [indicator, G.matching_card hV M]

/-- All feasible marginal vectors have mass m, as in the entropy proof. -/
theorem marginal_sum (G : LooplessGraph V E) {m : ℕ}
    (hV : Fintype.card V = 2 * m) {y : E → ℝ} (hy : y ∈ G.polytope) :
    ∑ e, y e = (m : ℝ) := by
  obtain ⟨p, hp, rfl⟩ := (G.mem_polytope_iff y).mp hy
  simp_rw [mean]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, G.indicator_sum hV]
  rw [← Finset.sum_mul, hp.2, one_mul]

end LooplessGraph

omit [Fintype V] [DecidableEq V] in
/-- The supremum in the definition of H is a genuine attained maximum. -/
theorem maxMatchingEntropy_attained (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) :
    ∃ p ∈ G.feasibleLaws y, entropy p = maxMatchingEntropy G y := by
  have hc := (G.compact_feasibleLaws y).image continuous_entropy
  have hn := ((G.mem_polytope_iff y).mp hy).image entropy
  obtain ⟨p, hp, hpe⟩ := hc.sSup_mem hn
  exact ⟨p, hp, hpe⟩

omit [Fintype V] [DecidableEq V] in
theorem maxMatchingEntropy_nonneg (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) : 0 ≤ maxMatchingEntropy G y := by
  obtain ⟨p, hp, he⟩ := maxMatchingEntropy_attained G hy
  rw [← he]
  exact entropy_nonneg hp.1

omit [Fintype V] [DecidableEq V] in
theorem maxMatchingEntropy_le_log_card (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) :
    maxMatchingEntropy G y ≤ Real.log (Fintype.card G.Matching) := by
  obtain ⟨p, hp, he⟩ := maxMatchingEntropy_attained G hy
  rw [← he]
  exact entropy_le_log_card hp.1

omit [Fintype V] [DecidableEq V] in
theorem entropy_le_maxMatchingEntropy (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y) :
    entropy p ≤ maxMatchingEntropy G y := by
  apply le_csSup
  · exact ((G.compact_feasibleLaws y).image continuous_entropy).bddAbove
  · exact ⟨p, hp, rfl⟩

end MatchingEntropy

end

end OAI
end
end

section
section
namespace OAI

/-!
Support and first-order identities for entropy-maximizing matching laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Concavity of actual finite-law Shannon entropy. -/
theorem entropy_mix_ge {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t) * entropy p + t * entropy q ≤
      entropy (fun i => (1-t)*p i + t*q i) := by
  unfold entropy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.2
    (hp i) (hq i) (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)

/-- A zero probability gains a strict logarithmic bonus under mixing.
This is the boundary argument needed to obtain a positive entropy optimizer
on the entire face, not an assumed regularity of H. -/
theorem entropy_mix_zero_bonus {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) {j : ι} (hj : p j = 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t) * entropy p + t * entropy q + q j * Real.negMulLog t ≤
      entropy (fun i => (1-t)*p i + t*q i) := by
  classical
  have hterm : ∀ i, (1-t) * Real.negMulLog (p i) + t * Real.negMulLog (q i) +
      (if i=j then q j * Real.negMulLog t else 0) ≤
        Real.negMulLog ((1-t)*p i+t*q i) := by
    intro i
    by_cases hi : i=j
    · subst i
      simp only [hj, Real.negMulLog_zero, mul_zero, zero_add, ite_true,
        Real.negMulLog_mul]
      linarith
    · simp only [hi, ↓reduceIte, add_zero]
      simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.2
        (hp i) (hq i) (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, entropy] using hh

/-- Every entropy maximizer on a convex feasible set has maximal support. -/
theorem entropy_maximizer_support {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hmax : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      entropy (fun i => (1-t)*p i+t*q i) ≤ entropy p) {j : ι} (hjq : 0 < q j) :
    0 < p j := by
  by_contra hj
  have hj0 : p j = 0 := le_antisymm (le_of_not_gt hj) (hp j)
  have hqp : entropy q ≤ entropy p := by simpa using hmax 1 (by constructor <;> norm_num)
  let c := (entropy p-entropy q)/(q j)+1
  have hc : 0 < c := by dsimp [c]; positivity
  let t := Real.exp (-c)
  have htp : 0 < t := Real.exp_pos _
  have ht : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨htp.le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hc.le)⟩
  have hbonus := (entropy_mix_zero_bonus hp hq hj0 ht).trans (hmax t ht)
  have hlog : Real.log t = -c := Real.log_exp _
  rw [Real.negMulLog, hlog] at hbonus
  have he : q j * c = entropy p-entropy q+q j := by
    dsimp [c]
    field_simp
  nlinarith

omit [Fintype V] [DecidableEq V] in
/-- The preceding support conclusion for the concrete matching-law optimizer. -/
theorem matching_optimizer_support (G : LooplessGraph V E) {y : E → ℝ}
    {p q : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hq : q ∈ G.feasibleLaws y) (hopt : entropy p = maxMatchingEntropy G y)
    {M : G.Matching} (hM : 0 < q M) : 0 < p M := by
  apply entropy_maximizer_support hp.1.1 hq.1.1 _ hM
  intro t ht
  apply le_trans (entropy_le_maxMatchingEntropy (G := G) (y := y) ?_) (le_of_eq hopt.symm)
  constructor
  · exact convex_probabilitySimplex _ hp.1 hq.1
      (sub_nonneg.mpr ht.2) ht.1 (by ring)
  · calc
      G.mean (fun i => (1-t)*p i+t*q i) =
          (1-t) • G.mean p + t • G.mean q := by
        exact (G.meanLinear).map_add ((1-t) • p) (t • q) |>.trans (by
          rw [LinearMap.map_smul, LinearMap.map_smul]; rfl)
      _ = y := by rw [hp.2, hq.2]; ext e; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring


/-- Supporting-line inequality for -x log x, with no positivity assumption
on the comparison probability x. -/
theorem negMulLog_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    Real.negMulLog x ≤ -x * Real.log y + y-x := by
  have h := mul_le_mul_of_nonneg_left
    (Real.negMulLog_le_one_sub_self (div_nonneg hx hy.le)) hy.le
  have he : Real.negMulLog x = -x * Real.log y + y * Real.negMulLog (x/y) := by
    calc
      Real.negMulLog x = Real.negMulLog (y * (x/y)) := by congr 1; field_simp
      _ = (x/y) * Real.negMulLog y + y * Real.negMulLog (x/y) := Real.negMulLog_mul _ _
      _ = _ := by unfold Real.negMulLog; field_simp
  rw [he]
  have hdiv : y * (x/y) = x := by field_simp
  nlinarith

/-- Gibbs' inequality on a finite set, with the exact support condition
needed on boundary faces. -/
theorem entropy_le_crossEntropy {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (hq : q ∈ probabilitySimplex ι)
    (hsupp : ∀ i, p i = 0 → q i = 0) :
    entropy q ≤ -∑ i, q i * Real.log (p i) := by
  have hterm : ∀ i, Real.negMulLog (q i) ≤
      -(q i * Real.log (p i)) + p i-q i := by
    intro i
    by_cases hi : p i = 0
    · simp [hi, hsupp i hi]
    · simpa only [neg_mul] using negMulLog_tangent (hq.1 i)
        (lt_of_le_of_ne (hp.1 i) (Ne.symm hi))
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ => hterm i
  simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, hp.2, hq.2, add_sub_cancel_right, entropy] using hh

/-- Derivative of entropy along a line supported on the positive probabilities. -/
theorem entropy_line_hasDerivAt {ι : Type*} [Fintype ι] (p v : ι → ℝ)
    (hsupp : ∀ i, p i = 0 → v i = 0) :
    HasDerivAt (fun t : ℝ => entropy (fun i => p i+t*v i))
      (-∑ i, v i * Real.log (p i) - ∑ i, v i) 0 := by
  have hd : ∀ i, HasDerivAt (fun t : ℝ => Real.negMulLog (p i+t*v i))
      ((-Real.log (p i)-1)*v i) 0 := by
    intro i
    by_cases hi : p i = 0
    · simpa only [hi, hsupp i hi, mul_zero, add_zero, Real.negMulLog_zero] using
        (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    · have hp : p i+(0 : ℝ)*v i ≠ 0 := by simpa using hi
      simpa only [zero_mul, add_zero, one_mul, Function.comp_def, id_eq] using
        (Real.hasDerivAt_negMulLog hp).comp 0
          (((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (p i))
  have he : (∑ i, (-Real.log (p i)-1)*v i) =
      -∑ i, v i*Real.log (p i) - ∑ i, v i := by
    simp_rw [sub_mul, one_mul, neg_mul, mul_comm (Real.log (p _))]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [← he]
  simpa only [entropy, Finset.sum_apply] using (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i))

omit [Fintype V] [DecidableEq V] in
/-- The log probabilities of the actual optimizer annihilate every feasible
mass/mean-preserving linear variation. No exponential representation assumed. -/
theorem matching_optimizer_log_annihilates (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y) (v : G.Matching → ℝ)
    (hvsum : ∑ M, v M = 0) (hvmean : G.mean v = 0)
    (hsupp : ∀ M, p M = 0 → v M = 0) :
    ∑ M, v M * Real.log (p M) = 0 := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ M, 0 ≤ p M+t*v M := by
    apply Filter.eventually_all.mpr
    intro M
    by_cases hM : p M = 0
    · exact Filter.Eventually.of_forall (fun t => by simp [hM, hsupp M hM])
    · have hpos : 0 < p M := lt_of_le_of_ne (hp.1.1 M) (Ne.symm hM)
      have hc : Continuous (fun t : ℝ => p M+t*v M) := by fun_prop
      have hh : {t : ℝ | 0 < p M+t*v M} ∈ 𝓝 0 :=
        (isOpen_lt continuous_const hc).mem_nhds (by simpa using hpos)
      exact Filter.Eventually.mono hh (fun t ht => ht.le)
  have hlocal : IsLocalMax (fun t : ℝ => entropy (fun M => p M+t*v M)) 0 := by
    filter_upwards [hev] with t ht
    have hmean : G.mean (fun M => p M+t*v M) = y := by
      change G.meanLinear (p+t • v) = y
      rw [map_add, map_smul]
      change G.mean p + t • G.mean v = y
      rw [hp.2, hvmean, smul_zero, add_zero]
    have hsum : ∑ M, (p M+t*v M) = 1 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp.1.2, hvsum, mul_zero, add_zero]
    have hle := entropy_le_maxMatchingEntropy (G := G) ⟨⟨ht, hsum⟩, hmean⟩
    simpa only [zero_mul, add_zero, ← hopt] using hle
  have hh := hlocal.deriv_eq_zero
  rw [(entropy_line_hasDerivAt p v hsupp).deriv, hvsum] at hh
  linarith


/-- A finite nonnegative vector permits small positive motion in any direction
which does not point outwards at its zero coordinates. -/
theorem exists_pos_nonneg_perturb {ι : Type*} [Fintype ι] (p v : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hz : ∀ i, p i = 0 → 0 ≤ v i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, 0 ≤ p i+t*v i := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, p i ≠ 0 → 0 ≤ p i+t*v i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : p i = 0
    · exact Filter.Eventually.of_forall (fun _ h => (h hi).elim)
    · have hc : Continuous (fun t : ℝ => p i+t*v i) := by fun_prop
      have hh : {t : ℝ | 0 < p i+t*v i} ∈ 𝓝 0 :=
        (isOpen_lt continuous_const hc).mem_nhds
          (by simpa using lt_of_le_of_ne (hp i) (Ne.symm hi))
      exact Filter.Eventually.mono hh (fun t ht _ => ht.le)
  have he' := (hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Set.Ioi 0)
  obtain ⟨t, ht, htp⟩ := he'.exists
  refine ⟨t, htp, fun i => ?_⟩
  by_cases hi : p i = 0
  · rw [hi, zero_add]
    exact mul_nonneg htp.le (hz i hi)
  · exact ht i hi

omit [Fintype V] [DecidableEq V] in
/-- The support of an optimizing law is a face: every law at a mean generated
by that support is itself supported there. This avoids assuming a face
representation of the marginal polytope in the entropy-optimization step. -/
theorem matching_optimizer_face_support (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y)
    {q r : G.Matching → ℝ} (hq : q ∈ probabilitySimplex G.Matching)
    (hr : r ∈ probabilitySimplex G.Matching) (hmean : G.mean q = G.mean r)
    (hrsupport : ∀ M, p M = 0 → r M = 0) :
    ∀ M, p M = 0 → q M = 0 := by
  obtain ⟨t, htp, ht⟩ := exists_pos_nonneg_perturb p (q-r) hp.1.1
    (fun M hM => by simpa [hrsupport M hM] using hq.1 M)
  have hsum : ∑ M, (p M+t*(q-r) M) = 1 := by
    simp only [Pi.sub_apply, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, hp.1.2, hq.2, hr.2]
    ring
  have hmean' : G.mean (fun M => p M+t*(q-r) M) = y := by
    change G.meanLinear (p+t • (q-r)) = y
    rw [map_add, map_smul, map_sub]
    change G.mean p + t • (G.mean q-G.mean r) = y
    rw [hp.2, hmean, sub_self, smul_zero, add_zero]
  intro M hM
  by_contra hqM
  have hqMp : 0 < q M := lt_of_le_of_ne (hq.1 M) (Ne.symm hqM)
  have hpM := matching_optimizer_support G hp ⟨⟨ht, hsum⟩, hmean'⟩ hopt
    (M := M) (by simpa [hM, hrsupport M hM] using mul_pos htp hqMp)
  simp [hM] at hpM

end MatchingEntropy

end

end OAI
end
end

section
section
namespace OAI

/-!
Finite exponential tilts, partition functions, and entropy duality on a face.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Finite exponential partition function, based on a probability law p. -/
def partition {ι : Type*} [Fintype ι] (p a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, p i * Real.exp (t*a i)

def tiltedLaw {ι : Type*} [Fintype ι] (p a : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  p i * Real.exp (t*a i) / partition p a t

theorem partition_pos {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (t : ℝ) : 0 < partition p a t := by
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hp.1 i)).mp
    (show 0 < ∑ i, p i by rw [hp.2]; norm_num)
  exact (Finset.sum_pos_iff_of_nonneg (fun i _ => mul_nonneg (hp.1 i) (Real.exp_pos _).le)).mpr
    ⟨i, Finset.mem_univ _, mul_pos hi (Real.exp_pos _)⟩

@[simp] theorem partition_zero {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) : partition p a 0 = 1 := by
  simpa only [partition, zero_mul, Real.exp_zero, mul_one] using hp.2

theorem tiltedLaw_mem_simplex {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (t : ℝ) :
    tiltedLaw p a t ∈ probabilitySimplex ι := by
  refine ⟨fun i => div_nonneg (mul_nonneg (hp.1 i) (Real.exp_pos _).le)
    (partition_pos hp a t).le, ?_⟩
  simp only [tiltedLaw, ← Finset.sum_div]
  exact div_self (partition_pos hp a t).ne'

/-- Gibbs' variational inequality for the explicit finite partition function,
including all boundary laws supported on p. -/
theorem entropy_partition_bound {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (hq : q ∈ probabilitySimplex ι)
    (hsupp : ∀ i, p i = 0 → q i = 0) (a : ι → ℝ) (t : ℝ) :
    entropy q ≤ Real.log (partition p a t) - ∑ i, q i*Real.log (p i) -
      t * ∑ i, q i*a i := by
  have hlog : ∀ i, q i * Real.log (tiltedLaw p a t i) =
      q i * Real.log (p i) + t*(q i*a i) - q i*Real.log (partition p a t) := by
    intro i
    by_cases hi : p i = 0
    · simp [hsupp i hi]
    · rw [tiltedLaw, Real.log_div (mul_ne_zero hi (Real.exp_ne_zero _))
        (partition_pos hp a t).ne', Real.log_mul hi (Real.exp_ne_zero _), Real.log_exp]
      ring
  calc
    entropy q ≤ -∑ i, q i*Real.log (tiltedLaw p a t i) :=
      entropy_le_crossEntropy (tiltedLaw_mem_simplex hp a t) hq (by
        intro i hi
        have hii : p i = 0 := by
          have := (div_eq_zero_iff).mp hi
          rcases this with hh | hh
          · exact (mul_eq_zero.mp hh).resolve_right (Real.exp_ne_zero _)
          · exact ((partition_pos hp a t).ne' hh).elim
        exact hsupp i hii)
    _ = _ := by
      simp_rw [hlog]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul, hq.2, one_mul]
      ring


/-- A score affine in the matching vector; the constant permits centering
without changing the duality calculation. -/
def linearScore (G : LooplessGraph V E) (u : E → ℝ) (c : ℝ) (M : G.Matching) : ℝ :=
  (∑ e, u e * G.indicator M e) - c

omit [Fintype V] [DecidableEq V] in
theorem sum_mean_assoc (G : LooplessGraph V E) (p : G.Matching → ℝ) (u : E → ℝ) :
    (∑ M, p M * (∑ e, u e * G.indicator M e)) = ∑ e, u e * G.mean p e := by
  simp only [LooplessGraph.mean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro M _
  ring

omit [Fintype V] [DecidableEq V] in
theorem linearScore_expectation (G : LooplessGraph V E) (p : G.Matching → ℝ)
    (u : E → ℝ) (c : ℝ) :
    (∑ M, p M * linearScore G u c M) =
      (∑ e, u e * G.mean p e) - c * ∑ M, p M := by
  simp only [linearScore, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [sum_mean_assoc]
  ring

omit [Fintype V] [DecidableEq V] in
/-- A genuine upper bound on the actual maximum entropy at every mean in the
optimizer's face. This is proved from Gibbs' inequality, not assumed as a
replacement definition of H. -/
theorem matching_entropy_dual_bound (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y)
    {r : G.Matching → ℝ} (hr : r ∈ probabilitySimplex G.Matching)
    (hrsupport : ∀ M, p M = 0 → r M = 0)
    (u : E → ℝ) (c t : ℝ) :
    maxMatchingEntropy G (G.mean r) ≤
      Real.log (partition p (linearScore G u c) t) - ∑ M, r M * Real.log (p M) -
        t * ∑ M, r M * linearScore G u c M := by
  obtain ⟨q, hq, heq⟩ := maxMatchingEntropy_attained G (G.mean_mem_polytope hr)
  have hsuppq := matching_optimizer_face_support G hp hopt hq.1 hr hq.2 hrsupport
  have hmean : G.mean (q-r) = 0 := by
    change G.meanLinear (q-r) = 0
    rw [map_sub]
    change G.mean q-G.mean r = 0
    rw [hq.2, sub_self]
  have hsum : ∑ M, (q-r) M = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hq.1.2, hr.2, sub_self]
  have hlog := matching_optimizer_log_annihilates G hp hopt (q-r) hsum hmean
    (fun M hM => by simp [hsuppq M hM, hrsupport M hM])
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] at hlog
  have hscore : (∑ M, q M*linearScore G u c M) = ∑ M, r M*linearScore G u c M := by
    rw [linearScore_expectation, linearScore_expectation, hq.2, hq.1.2, hr.2]
  rw [← heq]
  simpa only [hlog, hscore] using entropy_partition_bound hp.1 hq.1 hsuppq
    (linearScore G u c) t

end MatchingEntropy

end

end OAI
end
end

section
section
namespace OAI

/-!
Derivatives of entropy and log-partition, and the nonlinear entropy barrier.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

/-- First derivative of a finite exponential partition function. -/
theorem partition_hasDerivAt {ι : Type*} [Fintype ι] (p a : ι → ℝ) (t : ℝ) :
    HasDerivAt (partition p a) (partition (fun i => p i*a i) a t) t := by
  apply HasDerivAt.fun_sum
  intro i _
  simpa only [one_mul, id_eq, mul_assoc, mul_comm, mul_left_comm] using
    (((hasDerivAt_id t).mul_const (a i)).exp.const_mul (p i))

/-- The logarithmic partition derivative, with no infinite optimization
or interchange of limits: only finite sums. -/
theorem logPartition_hasDerivAt {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => Real.log (partition p a t))
      (partition (fun i => p i*a i) a t / partition p a t) t :=
  (partition_hasDerivAt p a t).log (partition_pos hp a t).ne'

/-- The second derivative of log-partition at the base law is variance. -/
theorem logPartition_second {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) :
    HasDerivAt (fun t => partition (fun i => p i*a i) a t / partition p a t)
      ((∑ i, p i*(a i)^2) - (∑ i, p i*a i)^2) 0 := by
  have hd := (partition_hasDerivAt (fun i => p i*a i) a 0).div
    (partition_hasDerivAt p a 0) (partition_pos hp a 0).ne'
  refine hd.congr_deriv ?_
  simp only [partition, zero_mul, Real.exp_zero, mul_one, hp.2, one_pow, div_one]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

/-- The explicit first derivative along a supported affine marginal path. -/
def entropyLineD {ι : Type*} [Fintype ι] (x v : ι → ℝ) (t : ℝ) : ℝ :=
  -∑ i, v i * Real.log (x i+t*v i) - ∑ i, v i

theorem entropy_line_hasDerivAt_at {ι : Type*} [Fintype ι] (x v : ι → ℝ)
    (t : ℝ) (h : ∀ i, x i+t*v i ≠ 0 ∨ v i = 0) :
    HasDerivAt (fun t : ℝ => entropy (fun i => x i+t*v i)) (entropyLineD x v t) t := by
  have hd : ∀ i, HasDerivAt (fun t : ℝ => Real.negMulLog (x i+t*v i))
      ((-Real.log (x i+t*v i)-1)*v i) t := by
    intro i
    rcases h i with hi | hi
    · simpa only [one_mul, Function.comp_def, id_eq] using
        (Real.hasDerivAt_negMulLog hi).comp t
          (((hasDerivAt_id t).mul_const (v i)).const_add (x i))
    · simpa only [hi, mul_zero, add_zero] using (hasDerivAt_const t (Real.negMulLog (x i)))
  have he : (∑ i, (-Real.log (x i+t*v i)-1)*v i) = entropyLineD x v t := by
    simp_rw [sub_mul, one_mul, neg_mul, mul_comm (Real.log (x _+t*v _))]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    rfl
  rw [← he]
  simpa only [entropy, Finset.sum_apply] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i))

theorem entropy_line_deriv_eventually {ι : Type*} [Fintype ι] (x v : ι → ℝ)
    (hsupp : ∀ i, x i = 0 → v i = 0) :
    deriv (fun t : ℝ => entropy (fun i => x i+t*v i)) =ᶠ[𝓝 0] entropyLineD x v := by
  have hh : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, x i+t*v i ≠ 0 ∨ v i = 0 := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : x i = 0
    · exact Filter.Eventually.of_forall (fun t => Or.inr (hsupp i hi))
    · have hc : ContinuousAt (fun t : ℝ => x i+t*v i) 0 := by fun_prop
      have hn := hc.eventually_ne (show x i+(0:ℝ)*v i ≠ 0 by simpa using hi)
      exact hn.mono (fun t ht => Or.inl ht)
  filter_upwards [hh] with t ht
  exact (entropy_line_hasDerivAt_at x v t ht).deriv

theorem entropyLineD_hasDerivAt {ι : Type*} [Fintype ι] (x v : ι → ℝ)
    (hsupp : ∀ i, x i = 0 → v i = 0) :
    HasDerivAt (entropyLineD x v) (-∑ i, (v i)^2/x i) 0 := by
  have hd : ∀ i, HasDerivAt (fun t : ℝ => v i*Real.log (x i+t*v i))
      ((v i)^2/x i) 0 := by
    intro i
    by_cases hi : x i = 0
    · simpa only [hi, hsupp i hi, zero_mul, zero_pow (by omega : 2 ≠ 0), zero_div] using
        (hasDerivAt_const (0:ℝ) (0:ℝ))
    · have hh := ((((hasDerivAt_id (0:ℝ)).mul_const (v i)).const_add (x i)).log
          (by simpa using hi)).const_mul (v i)
      simpa only [id_eq, one_mul, zero_mul, add_zero, pow_two, mul_div_assoc] using hh
  change HasDerivAt (fun t : ℝ => -(∑ i, v i*Real.log (x i+t*v i)) - ∑ i, v i)
    (-∑ i, (v i)^2/x i) 0
  exact (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i)).neg.sub_const (∑ i, v i)

theorem entropy_line_second {ι : Type*} [Fintype ι] (x v : ι → ℝ)
    (hsupp : ∀ i, x i = 0 → v i = 0) :
    HasDerivAt (deriv (fun t : ℝ => entropy (fun i => x i+t*v i)))
      (-∑ i, (v i)^2/x i) 0 :=
  (entropyLineD_hasDerivAt x v hsupp).congr_of_eventuallyEq
    (entropy_line_deriv_eventually x v hsupp)

def entropyBarrier (m h : ℝ) : ℝ := h-8*m*(1-Real.exp (-h/m))
def entropyBarrierD (m h : ℝ) : ℝ := 1-8*Real.exp (-h/m)

theorem entropyBarrier_hasDerivAt {m : ℝ} (hm : m ≠ 0) (h : ℝ) :
    HasDerivAt (entropyBarrier m) (entropyBarrierD m h) h := by
  have he := (((hasDerivAt_id h).neg.div_const m).exp.const_sub 1).const_mul (8*m)
  have hd := (hasDerivAt_id h).sub he
  refine hd.congr_deriv ?_
  dsimp [entropyBarrierD]
  field_simp

theorem entropyBarrierD_hasDerivAt (m h : ℝ) :
    HasDerivAt (entropyBarrierD m) (8*Real.exp (-h/m)/m) h := by
  have hd := (((hasDerivAt_id h).neg.div_const m).exp.const_mul 8).const_sub 1
  refine hd.congr_deriv ?_
  dsimp
  ring

/-- Second derivative of the scalar barrier composed with any twice
explicitly differentiable path. -/
theorem barrier_second_path {m : ℝ} (hm : m ≠ 0) {f fD : ℝ → ℝ} {fDD : ℝ}
    (hf : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt f (fD t) t)
    (hDD : HasDerivAt fD fDD 0) :
    HasDerivAt (deriv (fun t => entropyBarrier m (f t)))
      (entropyBarrierD m (f 0)*fDD +
        (8*Real.exp (-f 0/m)/m)*(fD 0)^2) 0 := by
  have h0 : HasDerivAt f (fD 0) 0 := hf.self_of_nhds
  have he : deriv (fun t => entropyBarrier m (f t)) =ᶠ[𝓝 (0:ℝ)]
      (fun t => entropyBarrierD m (f t)*fD t) := by
    filter_upwards [hf] with t ht
    exact ((entropyBarrier_hasDerivAt hm (f t)).comp t ht).deriv
  have hd := ((entropyBarrierD_hasDerivAt m (f 0)).comp 0 h0).mul hDD
  have hd' : HasDerivAt (fun t => entropyBarrierD m (f t)*fD t)
      (entropyBarrierD m (f 0)*fDD +
        (8*Real.exp (-f 0/m)/m)*(fD 0)^2) 0 := by
    refine hd.congr_deriv ?_
    dsimp only [Function.comp_apply]
    ring
  exact hd'.congr_of_eventuallyEq he



/-- A direct second-derivative calculation for the affine-law comparison
path used below. -/
theorem second_deriv_quadratic_adjustment {f fD g gD : ℝ → ℝ} {fDD gDD c₀ c₁ v : ℝ}
    (hf : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt f (fD t) t)
    (hg : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt g (gD t) t)
    (hfD : HasDerivAt fD fDD 0) (hgD : HasDerivAt gD gDD 0) :
    HasDerivAt (deriv (fun t => f t+c₀+t*c₁+t^2*v-g t))
      (fDD+2*v-gDD) 0 := by
  have hfirst : deriv (fun t => f t+c₀+t*c₁+t^2*v-g t) =ᶠ[𝓝 (0:ℝ)]
      (fun t => fD t+c₁+2*t*v-gD t) := by
    filter_upwards [hf, hg] with t hft hgt
    have hd := (((hft.add_const c₀).fun_add ((hasDerivAt_id t).mul_const c₁)).fun_add
      (((hasDerivAt_id t).fun_pow 2).mul_const v)).fun_sub hgt
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq, one_mul,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using hd.deriv
  have hd := ((hfD.add_const c₁).fun_add
    (((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const v)).fun_sub hgD
  have hd' : HasDerivAt (fun t => fD t+c₁+2*t*v-gD t) (fDD+2*v-gDD) 0 := by
    simpa only [Pi.add_apply, Pi.sub_apply, id_eq, mul_one] using hd
  exact hd'.congr_of_eventuallyEq hfirst


/-- The necessary one-dimensional second-derivative test, also when the
second derivative is defined by Lean's totalized derivative. -/
theorem second_deriv_nonpos_of_local_max {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra h
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge h
  have hmin := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hm, hmin] with y h₁ h₂
    exact le_antisymm h₁ h₂
  have hh := he.deriv.deriv_eq
  simp only [deriv_const', deriv_const] at hh
  linarith


/-- All first derivatives on a neighborhood, including boundary coordinates
whose admissible direction is zero. -/
theorem entropy_line_eventually_hasDerivAt {ι : Type*} [Fintype ι] (x v : ι → ℝ)
    (hsupp : ∀ i, x i = 0 → v i = 0) :
    ∀ᶠ t : ℝ in 𝓝 0,
      HasDerivAt (fun t : ℝ => entropy (fun i => x i+t*v i)) (entropyLineD x v t) t := by
  have hh : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, x i+t*v i ≠ 0 ∨ v i = 0 := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : x i = 0
    · exact Filter.Eventually.of_forall (fun t => Or.inr (hsupp i hi))
    · have hc : ContinuousAt (fun t : ℝ => x i+t*v i) 0 := by fun_prop
      have hn := hc.eventually_ne (show x i+(0:ℝ)*v i ≠ 0 by simpa using hi)
      exact hn.mono (fun t ht => Or.inl ht)
  exact hh.mono (fun t ht => entropy_line_hasDerivAt_at x v t ht)

theorem entropy_barrier_line_second {ι : Type*} [Fintype ι]
    (x v : ι → ℝ) (hsupp : ∀ i, x i = 0 → v i = 0) {m : ℝ} (_hm : m ≠ 0) :
    HasDerivAt (fun t => entropyBarrierD m (entropy (fun i => x i+t*v i))*entropyLineD x v t)
      ((8*Real.exp (-entropy x/m)-1)*(∑ i, (v i)^2/x i) +
        (8*Real.exp (-entropy x/m)/m)*(entropyLineD x v 0)^2) 0 := by
  have h0 := (entropy_line_eventually_hasDerivAt x v hsupp).self_of_nhds
  have hd := ((entropyBarrierD_hasDerivAt m (entropy (fun i => x i+(0:ℝ)*v i))).comp 0 h0).mul
    (entropyLineD_hasDerivAt x v hsupp)
  refine hd.congr_deriv ?_
  simp only [Function.comp_apply, zero_mul, add_zero, entropyBarrierD]
  ring

/-- The exact second variation along affine laws, proved solely by ordinary
one-variable derivatives and the finite log-partition variance identity. -/
theorem entropy_second_variation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x v : ι → ℝ) (hsupp : ∀ i, x i = 0 → v i = 0)
    {p : κ → ℝ} (hp : p ∈ probabilitySimplex κ) (a : κ → ℝ)
    (hcenter : ∑ i, p i*a i = 0) {m : ℝ} (hm : m ≠ 0) (c₀ c₁ : ℝ)
    (hlocal : IsLocalMax (fun t => entropyBarrier m (entropy (fun i => x i+t*v i)) +
      c₀+t*c₁+t^2*(∑ i, p i*(a i)^2)-Real.log (partition p a t)) 0) :
    (8*Real.exp (-entropy x/m)-1)*(∑ i, (v i)^2/x i) +
      (8*Real.exp (-entropy x/m)/m)*(entropyLineD x v 0)^2 +
      (∑ i, p i*(a i)^2) ≤ 0 := by
  have hf : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt
      (fun t => entropyBarrier m (entropy (fun i => x i+t*v i)))
      (entropyBarrierD m (entropy (fun i => x i+t*v i))*entropyLineD x v t) t := by
    filter_upwards [entropy_line_eventually_hasDerivAt x v hsupp] with t ht
    exact (entropyBarrier_hasDerivAt hm _).comp t ht
  have hg : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt (fun t => Real.log (partition p a t))
      (partition (fun i => p i*a i) a t / partition p a t) t :=
    Filter.Eventually.of_forall (logPartition_hasDerivAt hp a)
  have hd := second_deriv_quadratic_adjustment (c₀ := c₀) (c₁ := c₁)
    (v := ∑ i, p i*(a i)^2) hf hg (entropy_barrier_line_second x v hsupp hm)
    (logPartition_second hp a)
  have hc : ContinuousAt (fun t => entropyBarrier m (entropy (fun i => x i+t*v i)) +
      c₀+t*c₁+t^2*(∑ i, p i*(a i)^2)-Real.log (partition p a t)) 0 := by
    apply ContinuousAt.sub
    · apply ContinuousAt.add
      · apply ContinuousAt.add
        · exact hf.self_of_nhds.continuousAt.add_const c₀
        · fun_prop
      · fun_prop
    · exact hg.self_of_nhds.continuousAt
  have hh := second_deriv_nonpos_of_local_max hlocal hc
  rw [hd.deriv, hcenter] at hh
  nlinarith

end MatchingEntropy

end

end OAI
end
end

section
section
namespace OAI

/-!
The second-variation inequality at a maximum of the actual entropy defect.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def entropyDefect (G : LooplessGraph V E) (m : ℝ) (y : E → ℝ) : ℝ :=
  entropyBarrier m (entropy y)-maxMatchingEntropy G y

theorem score_law_eventually_simplex {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (hcenter : ∑ i, p i*a i = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, (fun i => p i+t*(p i*a i)) ∈ probabilitySimplex ι := by
  have hh : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 < 1+t*a i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : Continuous (fun t : ℝ => 1+t*a i) := by fun_prop
    exact (isOpen_lt continuous_const hc).mem_nhds (by norm_num)
  filter_upwards [hh] with t ht
  constructor
  · intro i
    have h := mul_nonneg (hp.1 i) (ht i).le
    nlinarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp.2, hcenter]
    ring

omit [Fintype V] [DecidableEq V] in
theorem mean_score_support (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) (a : G.Matching → ℝ) :
    ∀ e, G.mean p e = 0 → G.mean (fun M => p M*a M) e = 0 := by
  intro e he
  have hterms : ∀ M, p M*G.indicator M e = 0 := by
    have hh := (Finset.sum_eq_zero_iff_of_nonneg
      (fun M (_ : M ∈ Finset.univ) => mul_nonneg (hp.1 M) (G.indicator_nonneg M e))).mp he
    exact fun M => hh M (Finset.mem_univ M)
  apply Finset.sum_eq_zero
  intro M _
  calc
    _ = a M*(p M*G.indicator M e) := by ring
    _ = 0 := by rw [hterms, mul_zero]

omit [Fintype V] [DecidableEq V] in
/-- A maximum of the *actual* entropy defect satisfies the second-variation
inequality. The comparison uses optimizing probability laws rather than a replacement for H. -/
theorem matching_defect_second_variation (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p = maxMatchingEntropy G x) {m : ℝ} (hm : m ≠ 0)
    (hmax : ∀ y ∈ G.polytope, entropyDefect G m y ≤ entropyDefect G m x)
    (u : E → ℝ) (c : ℝ) (hcenter : ∑ M, p M*linearScore G u c M = 0) :
    (8*Real.exp (-entropy x/m)-1)*
        (∑ e, (G.mean (fun M => p M*linearScore G u c M) e)^2/x e) +
      (8*Real.exp (-entropy x/m)/m)*
        (entropyLineD x (G.mean (fun M => p M*linearScore G u c M)) 0)^2 +
      (∑ M, p M*(linearScore G u c M)^2) ≤ 0 := by
  let a := linearScore G u c
  let v := G.mean (fun M => p M*a M)
  let c₀ := ∑ M, p M*Real.log (p M)
  let c₁ := ∑ M, (p M*a M)*Real.log (p M)
  have hsupp : ∀ e, x e = 0 → v e = 0 := by
    rw [← hp.2]
    exact mean_score_support G hp.1 a
  apply entropy_second_variation x v hsupp hp.1 a hcenter hm c₀ c₁
  filter_upwards [score_law_eventually_simplex hp.1 a hcenter] with t ht
  let r := fun M => p M+t*(p M*a M)
  have hr : r ∈ probabilitySimplex G.Matching := ht
  have hrmean : G.mean r = fun e => x e+t*v e := by
    change G.meanLinear (p+t • (fun M => p M*a M)) = _
    rw [map_add, map_smul]
    change G.mean p+t • v = _
    rw [hp.2]
    rfl
  have hdual := matching_entropy_dual_bound G hp hopt hr
    (fun M hM => by dsimp [r]; simp [hM]) u c t
  have hscore : (∑ M, r M*a M) = t*(∑ M, p M*(a M)^2) := by
    dsimp [r]
    simp_rw [add_mul, mul_assoc t, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hcenter, zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro M _
    ring
  have hlog : (∑ M, r M*Real.log (p M)) = c₀+t*c₁ := by
    dsimp [r, c₀, c₁]
    simp_rw [add_mul, mul_assoc t, Finset.sum_add_distrib, ← Finset.mul_sum]
  change maxMatchingEntropy G (G.mean r) ≤
    Real.log (partition p a t) - (∑ M, r M*Real.log (p M)) - t*(∑ M, r M*a M) at hdual
  rw [hlog, hscore] at hdual
  have hmaxr := hmax (G.mean r) (G.mean_mem_polytope hr)
  dsimp only [entropyDefect] at hmaxr
  have hzero := partition_zero hp.1 a
  simp only [zero_mul, zero_pow (by omega : 2 ≠ 0), add_zero, hzero,
    Real.log_one, sub_zero]
  rw [← hopt] at hmaxr
  rw [entropy_eq p] at hmaxr
  rw [← hrmean]
  dsimp only [c₀] at *
  nlinarith

end MatchingEntropy

end

end OAI
end
end

section
section
namespace OAI

/-!
Degree and odd-cut constraints for the perfect matching polytope.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

/-- Exactly one endpoint in S; edge identities are kept, including parallels. -/
def Crosses (G : LooplessGraph V E) (S : Finset V) (e : E) : Prop :=
  (G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.left e ∉ S ∧ G.right e ∈ S)

instance crossesDecidable (G : LooplessGraph V E) (S : Finset V) (e : E) :
    Decidable (G.Crosses S e) := inferInstanceAs (Decidable
      ((G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.left e ∉ S ∧ G.right e ∈ S)))

def cut (G : LooplessGraph V E) (S : Finset V) : Finset E :=
  Finset.univ.filter (G.Crosses S)

def degree (G : LooplessGraph V E) (x : E → ℝ) (v : V) : ℝ :=
  ∑ e, if G.Incident v e then x e else 0

def cutMass (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ G.cut S, x e

/-- The degree and odd-cut constraint system. -/
def constraintPolytope (G : LooplessGraph V E) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ v, G.degree x v = 1) ∧
    (∀ S : Finset V, Odd S.card → 1 ≤ G.cutMass x S)}

omit [Fintype V] [DecidableEq E] in
@[simp] theorem mem_cut (G : LooplessGraph V E) (S : Finset V) (e : E) :
    e ∈ G.cut S ↔ G.Crosses S e := by simp [cut]

omit [Fintype E] [DecidableEq E] in
theorem crosses_compl (G : LooplessGraph V E) (S : Finset V) (e : E) :
    G.Crosses Sᶜ e ↔ G.Crosses S e := by
  simp only [Crosses, Finset.mem_compl, not_not]
  tauto

omit [DecidableEq E] in
@[simp] theorem cut_compl (G : LooplessGraph V E) (S : Finset V) :
    G.cut Sᶜ = G.cut S := by ext; simp [crosses_compl]

omit [Fintype V] in
theorem degree_indicator (G : LooplessGraph V E) (M : G.Matching) (v : V) :
    G.degree (G.indicator M) v = 1 := by
  obtain ⟨e, ⟨he, hev⟩, huniq⟩ := M.property v
  rw [degree, Finset.sum_eq_single e]
  · simp [hev, indicator, he]
  · intro e' _ hne
    by_cases hv : G.Incident v e'
    · have hh : e' ∉ M.val := by
        intro hm
        exact hne (huniq e' ⟨hm, hv⟩)
      simp [hv, indicator, hh]
    · simp [hv]
  · simp

omit [Fintype V] in
theorem degree_mean (G : LooplessGraph V E) (p : G.Matching → ℝ) (v : V) :
    G.degree (G.mean p) v = ∑ M, p M := by
  classical
  have he : ∀ e, (if G.Incident v e then G.mean p e else 0) =
      ∑ M, p M*(if G.Incident v e then G.indicator M e else 0) := by
    intro e
    by_cases h : G.Incident v e <;> simp [h, mean]
  unfold degree
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  rw [← Finset.mul_sum]
  change p M*G.degree (G.indicator M) v = p M
  rw [G.degree_indicator, mul_one]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem incidence_sum (G : LooplessGraph V E) (e : E) (S : Finset V) :
    (∑ v ∈ S, if G.Incident v e then (1:ℕ) else 0) =
      (if G.left e ∈ S then 1 else 0) + (if G.right e ∈ S then 1 else 0) := by
  have hv : ∀ v, (if G.Incident v e then (1:ℕ) else 0) =
      (if v = G.left e then 1 else 0) + (if v = G.right e then 1 else 0) := by
    intro v
    by_cases hl : v = G.left e <;> by_cases hr : v = G.right e
    · exact ((G.loopless e) (hl.symm.trans hr)).elim
    · simp [Incident, hl, G.loopless e, Ne.symm (G.loopless e)]
    · simp [Incident, hr, G.loopless e, Ne.symm (G.loopless e)]
    · simp [Incident, Ne.symm hl, Ne.symm hr, hl, hr]
  simp_rw [hv, Finset.sum_add_distrib]
  simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem matching_incidence_count (G : LooplessGraph V E) (M : G.Matching)
    (S : Finset V) :
    (∑ e ∈ M.val, ((if G.left e ∈ S then (1:ℕ) else 0) +
      (if G.right e ∈ S then 1 else 0))) = S.card := by
  have hsum : ∀ v, (∑ e ∈ M.val, if G.Incident v e then (1:ℕ) else 0) = 1 := by
    intro v
    obtain ⟨e, ⟨he, hev⟩, hu⟩ := M.property v
    rw [Finset.sum_eq_single e]
    · simp [hev]
    · intro e' he' hh
      have hv : ¬G.Incident v e' := fun hv => hh (hu e' ⟨he', hv⟩)
      simp [hv]
    · simp [he]
  calc
    _ = ∑ e ∈ M.val, ∑ v ∈ S, if G.Incident v e then (1:ℕ) else 0 := by
      simp_rw [incidence_sum]
    _ = ∑ v ∈ S, ∑ e ∈ M.val, if G.Incident v e then (1:ℕ) else 0 := Finset.sum_comm
    _ = S.card := by simp_rw [hsum]; simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem matching_crosses_odd (G : LooplessGraph V E) (M : G.Matching)
    (S : Finset V) (hS : Odd S.card) : ∃ e ∈ M.val, G.Crosses S e := by
  by_contra h
  push Not at h
  have heq : ∀ e ∈ M.val, ((if G.left e ∈ S then (1:ℕ) else 0) +
      (if G.right e ∈ S then 1 else 0)) = 2*(if G.left e ∈ S then 1 else 0) := by
    intro e he
    have hc := h e he
    simp only [Crosses] at hc
    by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;>
      simp_all
  have hh := G.matching_incidence_count M S
  have heqsum := Finset.sum_congr rfl heq
  rw [heqsum, ← Finset.mul_sum] at hh
  obtain ⟨k, hk⟩ := hS
  omega


omit [Fintype V] [DecidableEq E] in
theorem degree_linear (G : LooplessGraph V E) (x y : E → ℝ) (a b : ℝ) (v : V) :
    G.degree (a • x+b • y) v = a*G.degree x v+b*G.degree y v := by
  have he : ∀ e, (if G.Incident v e then (a • x+b • y) e else 0) =
      a*(if G.Incident v e then x e else 0)+b*(if G.Incident v e then y e else 0) := by
    intro e
    by_cases h : G.Incident v e <;> simp [h]
  simp only [degree, he, Finset.sum_add_distrib, ← Finset.mul_sum]

omit [Fintype V] [DecidableEq E] in
theorem cutMass_linear (G : LooplessGraph V E) (x y : E → ℝ) (a b : ℝ) (S : Finset V) :
    G.cutMass (a • x+b • y) S = a*G.cutMass x S+b*G.cutMass y S := by
  simp [cutMass, Finset.sum_add_distrib, Finset.mul_sum]

omit [Fintype V] [DecidableEq E] in
theorem convex_constraintPolytope (G : LooplessGraph V E) :
    Convex ℝ G.constraintPolytope := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun e => add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e)), ?_, ?_⟩
  · intro v
    rw [degree_linear, hx.2.1, hy.2.1, mul_one, mul_one, hab]
  · intro S hS
    rw [cutMass_linear]
    calc
      1 = a*1+b*1 := by linarith
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hx.2.2 S hS) ha)
        (mul_le_mul_of_nonneg_left (hy.2.2 S hS) hb)

omit [Fintype V] in
theorem indicator_mem_constraintPolytope (G : LooplessGraph V E) (M : G.Matching) :
    G.indicator M ∈ G.constraintPolytope := by
  refine ⟨?_, G.degree_indicator M, ?_⟩
  · intro e; simp [indicator]; split <;> norm_num
  · intro S hS
    obtain ⟨e, he, hc⟩ := G.matching_crosses_odd M S hS
    have h := Finset.single_le_sum (f := G.indicator M)
      (s := G.cut S) (a := e) (by intro e' _; simp [indicator]; split <;> norm_num)
      ((G.mem_cut S e).mpr hc)
    simpa only [cutMass, indicator, he, ite_true] using h

omit [Fintype V] in
theorem polytope_subset_constraintPolytope (G : LooplessGraph V E) :
    G.polytope ⊆ G.constraintPolytope := by
  apply convexHull_min
  · rintro x ⟨M, rfl⟩
    exact G.indicator_mem_constraintPolytope M
  · exact G.convex_constraintPolytope

omit [Fintype V] [DecidableEq E] in
theorem constraint_coordinate_le_one (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) (e : E) : x e ≤ 1 := by
  have h := Finset.single_le_sum (f := fun e' => if G.Incident (G.left e) e' then x e' else 0)
    (s := Finset.univ) (a := e) (by
      intro e' _; split; exact hx.1 e'; rfl) (Finset.mem_univ e)
  have he : G.Incident (G.left e) e := Or.inl rfl
  change (if G.Incident (G.left e) e then x e else 0) ≤ G.degree x (G.left e) at h
  simpa only [he, ite_true, hx.2.1] using h

omit [Fintype V] [DecidableEq E] in
theorem continuous_degree (G : LooplessGraph V E) (v : V) :
    Continuous (fun x : E → ℝ => G.degree x v) := by
  unfold degree
  apply continuous_finsetSum
  intro e _
  split <;> fun_prop

omit [Fintype V] [DecidableEq E] in
theorem continuous_cutMass (G : LooplessGraph V E) (S : Finset V) :
    Continuous (fun x : E → ℝ => G.cutMass x S) := by
  unfold cutMass
  fun_prop

omit [Fintype V] [DecidableEq E] in
theorem isClosed_constraintPolytope (G : LooplessGraph V E) :
    IsClosed G.constraintPolytope := by
  simp only [constraintPolytope, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter fun e => isClosed_le continuous_const (continuous_apply e)).inter
    ((isClosed_iInter fun v => isClosed_eq (G.continuous_degree v) continuous_const).inter
      (isClosed_iInter fun S => isClosed_iInter fun _ =>
        isClosed_le continuous_const (G.continuous_cutMass S)))

omit [Fintype V] [DecidableEq E] in
theorem isCompact_constraintPolytope (G : LooplessGraph V E) :
    IsCompact G.constraintPolytope := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : E → ℝ) 1)).of_isClosed_subset
    G.isClosed_constraintPolytope
  intro x hx
  exact ⟨hx.1, fun e => G.constraint_coordinate_le_one hx e⟩

end LooplessGraph

end MatchingEntropy

end

end OAI
end
end

section
section
namespace OAI

/-!
Finite pushforwards and couplings with a prescribed common marginal.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

/-- Finite pushforward weights. -/
def fiberMass {A C : Type*} [Fintype A] [DecidableEq C]
    (p : A → ℝ) (f : A → C) (c : C) : ℝ := ∑ a, if f a = c then p a else 0

theorem fiberMass_nonneg {A C : Type*} [Fintype A] [DecidableEq C]
    {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (f : A → C) (c : C) :
    0 ≤ fiberMass p f c := by
  apply Finset.sum_nonneg
  intro a _
  split <;> simp_all

theorem le_fiberMass_self {A C : Type*} [Fintype A] [DecidableEq C]
    {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (f : A → C) (a : A) :
    p a ≤ fiberMass p f (f a) := by
  have h := Finset.single_le_sum (s := Finset.univ) (a := a)
    (f := fun b => if f b = f a then p b else 0)
    (by intro b _; split <;> simp_all) (Finset.mem_univ a)
  simpa only [fiberMass, ite_true] using h

/-- The explicit cut-choice coupling. Only equal choices receive mass. -/
def jointLaw {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    (p : A → ℝ) (q : B → ℝ) (f : A → C) (g : B → C) (z : A × B) : ℝ :=
  if f z.1 = g z.2 then p z.1*q z.2 / fiberMass p f (f z.1) else 0

theorem jointLaw_nonneg {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b)
    (f : A → C) (g : B → C) (z : A × B) : 0 ≤ jointLaw p q f g z := by
  unfold jointLaw
  split
  · exact div_nonneg (mul_nonneg (hp _) (hq _)) (fiberMass_nonneg hp f _)
  · rfl

theorem jointLaw_first {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : ∀ a, 0 ≤ p a)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (a : A) : (∑ b, jointLaw p q f g (a,b)) = p a := by
  have heq : ∀ b, jointLaw p q f g (a,b) =
      (p a / fiberMass p f (f a)) * (if g b=f a then q b else 0) := by
    intro b
    by_cases h : f a=g b
    · simp only [jointLaw, h, ite_true]
      ring
    · simp [jointLaw, h, Ne.symm h]
  simp_rw [heq]
  rw [← Finset.mul_sum]
  change p a / fiberMass p f (f a) * fiberMass q g (f a) = p a
  rw [← hcompat]
  by_cases hz : fiberMass p f (f a) = 0
  · have ha : p a = 0 := le_antisymm (by simpa [hz] using le_fiberMass_self hp f a) (hp a)
    simp [ha]
  · exact div_mul_cancel₀ _ hz

theorem jointLaw_second {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hq : ∀ b, 0 ≤ q b)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (b : B) : (∑ a, jointLaw p q f g (a,b)) = q b := by
  have heq : ∀ a, jointLaw p q f g (a,b) =
      (q b / fiberMass q g (g b)) * (if f a=g b then p a else 0) := by
    intro a
    by_cases h : f a=g b
    · simp only [jointLaw, h, ite_true, ← hcompat]
      ring
    · simp [jointLaw, h]
  simp_rw [heq]
  rw [← Finset.mul_sum]
  change q b / fiberMass q g (g b) * fiberMass p f (g b) = q b
  rw [hcompat]
  by_cases hz : fiberMass q g (g b) = 0
  · have hb : q b = 0 := le_antisymm (by simpa [hz] using le_fiberMass_self hq g b) (hq b)
    simp [hb]
  · exact div_mul_cancel₀ _ hz

theorem jointLaw_mem_simplex {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : p ∈ probabilitySimplex A) (hq : q ∈ probabilitySimplex B)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c) :
    jointLaw p q f g ∈ probabilitySimplex (A × B) := by
  refine ⟨jointLaw_nonneg hp.1 hq.1 f g, ?_⟩
  rw [Fintype.sum_prod_type]
  simp_rw [jointLaw_first hp.1 f g hcompat]
  exact hp.2

theorem sum_subtype_supported {A : Type*} [Fintype A] (P : A → Prop) [DecidablePred P]
    (w : A → ℝ) (hsupp : ∀ a, ¬P a → w a = 0) :
    (∑ a : {a // P a}, w a.val) = ∑ a, w a := by
  have hh : (∑ a : {a // ¬P a}, w a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact hsupp a.val a.property
  simpa only [hh, add_zero] using (Fintype.sum_subtype_add_sum_subtype P w)

/-- No mass is lost in retaining only compatible pairs. -/
theorem compatible_jointLaw_mem_simplex {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : p ∈ probabilitySimplex A) (hq : q ∈ probabilitySimplex B)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c) :
    (fun z : {z : A × B // f z.1=g z.2} => jointLaw p q f g z.val) ∈
      probabilitySimplex {z : A × B // f z.1=g z.2} := by
  refine ⟨fun z => jointLaw_nonneg hp.1 hq.1 f g z.val, ?_⟩
  rw [sum_subtype_supported (fun z : A × B => f z.1=g z.2) (jointLaw p q f g)
    (by intro z hz; simp [jointLaw, hz])]
  exact (jointLaw_mem_simplex hp hq f g hcompat).2

theorem fiberMass_sum {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C]
    (p : A → ℝ) (f : A → C) : ∑ c, fiberMass p f c = ∑ a, p a := by
  unfold fiberMass
  rw [Finset.sum_comm]
  simp

theorem fiberMass_expect {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C]
    (p : A → ℝ) (f : A → C) (h : C → ℝ) :
    ∑ c, fiberMass p f c * h c = ∑ a, p a*h (f a) := by
  unfold fiberMass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp

theorem fiberMass_mem_simplex {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C]
    {p : A → ℝ} (hp : p ∈ probabilitySimplex A) (f : A → C) :
    fiberMass p f ∈ probabilitySimplex C :=
  ⟨fiberMass_nonneg hp.1 f, (fiberMass_sum p f).trans hp.2⟩

theorem jointLaw_expect_first {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : ∀ a, 0 ≤ p a)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (h : A → ℝ) : ∑ z : A × B, jointLaw p q f g z * h z.1 = ∑ a, p a*h a := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul, jointLaw_first hp f g hcompat]

theorem jointLaw_expect_second {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hq : ∀ b, 0 ≤ q b)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (h : B → ℝ) : ∑ z : A × B, jointLaw p q f g z * h z.2 = ∑ b, q b*h b := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, jointLaw_second hq f g hcompat]

theorem compatible_jointLaw_expect_first {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : ∀ a, 0 ≤ p a)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (h : A → ℝ) :
    ∑ z : {z : A × B // f z.1=g z.2}, jointLaw p q f g z.val * h z.val.1 = ∑ a, p a*h a := by
  rw [sum_subtype_supported (fun z : A × B => f z.1=g z.2)
    (fun z => jointLaw p q f g z * h z.1)
    (by intro z hz; simp [jointLaw, hz])]
  exact jointLaw_expect_first hp f g hcompat h

theorem compatible_jointLaw_expect_second {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hq : ∀ b, 0 ≤ q b)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (h : B → ℝ) :
    ∑ z : {z : A × B // f z.1=g z.2}, jointLaw p q f g z.val * h z.val.2 = ∑ b, q b*h b := by
  rw [sum_subtype_supported (fun z : A × B => f z.1=g z.2)
    (fun z => jointLaw p q f g z * h z.2)
    (by intro z hz; simp [jointLaw, hz])]
  exact jointLaw_expect_second hq f g hcompat h

end MatchingEntropy

end

end OAI
end
end

section
section
namespace OAI

/-!
Contraction of tight odd cuts and gluing of perfect matchings and their laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

/-- Contraction of the complement of S to a new vertex. Edges retain identities;
only edges with both endpoints outside S are discarded. -/
def onSide (G : LooplessGraph V E) (S : Finset V) :
    LooplessGraph (Option {v // v ∈ S}) {e // G.left e ∈ S ∨ G.right e ∈ S} where
  left e := if h : G.left e.val ∈ S then some ⟨G.left e.val, h⟩ else none
  right e := if h : G.right e.val ∈ S then some ⟨G.right e.val, h⟩ else none
  loopless e := by
    dsimp
    split_ifs with hl hr
    · intro he
      have hv := Option.some.inj he
      exact G.loopless e.val (congrArg Subtype.val hv)
    · simp
    · simp
    · rename_i hr
      exact (e.property.elim hl hr).elim


omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem onSide_incident_some (G : LooplessGraph V E) (S : Finset V)
    (v : {v // v ∈ S}) (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    (G.onSide S).Incident (some v) e ↔ G.Incident v.val e.val := by
  have hf : ∀ (w : V),
      (if h : w ∈ S then some (⟨w,h⟩ : {v // v ∈ S}) else none) = some v ↔ w=v.val := by
    intro w
    by_cases hw : w ∈ S
    · simp only [hw, ↓reduceDIte, Option.some.injEq]
      exact Subtype.ext_iff
    · simp only [hw, ↓reduceDIte]
      constructor
      · intro h
        cases h
      · intro he
        exact (hw (he.symm ▸ v.property)).elim
  change ((if h : G.left e.val ∈ S then some ⟨G.left e.val,h⟩ else none) = some v ∨
    (if h : G.right e.val ∈ S then some ⟨G.right e.val,h⟩ else none) = some v) ↔ _
  rw [hf, hf]
  rfl

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem onSide_incident_none (G : LooplessGraph V E) (S : Finset V)
    (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    (G.onSide S).Incident none e ↔ G.Crosses S e.val := by
  simp only [Incident, onSide, Crosses]
  by_cases hl : G.left e.val ∈ S <;> by_cases hr : G.right e.val ∈ S <;>
    simp [hl, hr]
  exact (e.property.elim hl hr).elim

def boundaryEdge (G : LooplessGraph V E) (S : Finset V) (M : (G.onSide S).Matching) :
    {e // G.left e ∈ S ∨ G.right e ∈ S} := Classical.choose (M.property none)

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem boundaryEdge_mem (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) : G.boundaryEdge S M ∈ M.val :=
  (Classical.choose_spec (M.property none)).1.1

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem boundaryEdge_crosses (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) : G.Crosses S (G.boundaryEdge S M).val :=
  (G.onSide_incident_none S _).mp (Classical.choose_spec (M.property none)).1.2

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem eq_boundaryEdge (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) {e : {e // G.left e ∈ S ∨ G.right e ∈ S}}
    (he : e ∈ M.val) (hc : G.Crosses S e.val) : e = G.boundaryEdge S M :=
  (Classical.choose_spec (M.property none)).2 e ⟨he, (G.onSide_incident_none S e).mpr hc⟩

def liftedEdges (G : LooplessGraph V E) (S : Finset V) (M : (G.onSide S).Matching) : Finset E :=
  M.val.image Subtype.val

omit [Fintype V] [Fintype E] in
theorem mem_liftedEdges (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    e.val ∈ G.liftedEdges S M ↔ e ∈ M.val := by
  simp only [liftedEdges, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, he⟩
    have he' : a = e := Subtype.ext he
    simpa only [he'] using ha
  · intro he
    exact ⟨e, he, rfl⟩

omit [Fintype V] [Fintype E] in
theorem liftedEdges_keep (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) {e : E} (he : e ∈ G.liftedEdges S M) :
    G.left e ∈ S ∨ G.right e ∈ S := by
  rcases Finset.mem_image.mp he with ⟨a, _, rfl⟩
  exact a.property

omit [Fintype V] [Fintype E] in
theorem lifted_cross_eq_boundary (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) {e : E} (he : e ∈ G.liftedEdges S M)
    (hc : G.Crosses S e) : e = (G.boundaryEdge S M).val := by
  let e' : {e // G.left e ∈ S ∨ G.right e ∈ S} := ⟨e, G.liftedEdges_keep S M he⟩
  exact congrArg Subtype.val (G.eq_boundaryEdge S M ((G.mem_liftedEdges S M e').mp he) hc)

omit [Fintype V] [Fintype E] in
theorem boundary_mem_lifted (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) : (G.boundaryEdge S M).val ∈ G.liftedEdges S M :=
  (G.mem_liftedEdges S M _).mpr (G.boundaryEdge_mem S M)

omit [Fintype E] [DecidableEq E] in
theorem crosses_of_kept_both (G : LooplessGraph V E) (S : Finset V) (e : E)
    (h₁ : G.left e ∈ S ∨ G.right e ∈ S)
    (h₂ : G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ) : G.Crosses S e := by
  simp only [Finset.mem_compl] at h₂
  unfold Crosses
  tauto

omit [Fintype E] in
/-- A compatible pair only duplicates its common boundary edge. -/
theorem lifted_other_subset (G : LooplessGraph V E) (S : Finset V)
    (M₁ : (G.onSide S).Matching) (M₂ : (G.onSide Sᶜ).Matching)
    (heq : (G.boundaryEdge S M₁).val = (G.boundaryEdge Sᶜ M₂).val)
    {e : E} (he : e ∈ G.liftedEdges Sᶜ M₂)
    (hkeep : G.left e ∈ S ∨ G.right e ∈ S) : e ∈ G.liftedEdges S M₁ := by
  have hc := G.crosses_of_kept_both S e hkeep (G.liftedEdges_keep Sᶜ M₂ he)
  have hcb : G.Crosses Sᶜ e := (G.crosses_compl S e).mpr hc
  rw [G.lifted_cross_eq_boundary Sᶜ M₂ he hcb, ← heq]
  exact G.boundary_mem_lifted S M₁

omit [Fintype E] in
/-- Gluing compatible perfect matchings preserves each retained edge choice. -/
theorem mem_glued_left (G : LooplessGraph V E) (S : Finset V)
    (M₁ : (G.onSide S).Matching) (M₂ : (G.onSide Sᶜ).Matching)
    (heq : (G.boundaryEdge S M₁).val = (G.boundaryEdge Sᶜ M₂).val)
    (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    e.val ∈ G.liftedEdges S M₁ ∪ G.liftedEdges Sᶜ M₂ ↔ e ∈ M₁.val := by
  simp only [Finset.mem_union]
  constructor
  · rintro (h | h)
    · exact (G.mem_liftedEdges S M₁ e).mp h
    · exact (G.mem_liftedEdges S M₁ e).mp (G.lifted_other_subset S M₁ M₂ heq h e.property)
  · intro h
    exact Or.inl ((G.mem_liftedEdges S M₁ e).mpr h)

omit [Fintype E] in
theorem mem_glued_right (G : LooplessGraph V E) (S : Finset V)
    (M₁ : (G.onSide S).Matching) (M₂ : (G.onSide Sᶜ).Matching)
    (heq : (G.boundaryEdge S M₁).val = (G.boundaryEdge Sᶜ M₂).val)
    (e : {e // G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ}) :
    e.val ∈ G.liftedEdges S M₁ ∪ G.liftedEdges Sᶜ M₂ ↔ e ∈ M₂.val := by
  simp only [Finset.mem_union]
  constructor
  · rintro (h | h)
    · have hc := G.crosses_of_kept_both S e.val (G.liftedEdges_keep S M₁ h) e.property
      have he := (G.lifted_cross_eq_boundary S M₁ h hc).trans heq
      apply (G.mem_liftedEdges Sᶜ M₂ e).mp
      rw [he]
      exact G.boundary_mem_lifted Sᶜ M₂
    · exact (G.mem_liftedEdges Sᶜ M₂ e).mp h
  · intro h
    exact Or.inr ((G.mem_liftedEdges Sᶜ M₂ e).mpr h)

omit [Fintype E] in
theorem glued_perfect (G : LooplessGraph V E) (S : Finset V)
    (M₁ : (G.onSide S).Matching) (M₂ : (G.onSide Sᶜ).Matching)
    (heq : (G.boundaryEdge S M₁).val = (G.boundaryEdge Sᶜ M₂).val) :
    G.IsPerfectMatching (G.liftedEdges S M₁ ∪ G.liftedEdges Sᶜ M₂) := by
  intro v
  by_cases hv : v ∈ S
  · obtain ⟨e, ⟨he, hev⟩, hu⟩ := M₁.property (some ⟨v,hv⟩)
    have hev' := (G.onSide_incident_some S ⟨v,hv⟩ e).mp hev
    refine ⟨e.val, ⟨(G.mem_glued_left S M₁ M₂ heq e).mpr he, hev'⟩, ?_⟩
    rintro f ⟨hf, hfv⟩
    have hk : G.left f ∈ S ∨ G.right f ∈ S := by
      rcases hfv with h | h
      · exact Or.inl (h.symm ▸ hv)
      · exact Or.inr (h.symm ▸ hv)
    let f' : {e // G.left e ∈ S ∨ G.right e ∈ S} := ⟨f,hk⟩
    have hf' : f' ∈ M₁.val := (G.mem_glued_left S M₁ M₂ heq f').mp hf
    exact congrArg Subtype.val (hu f' ⟨hf', (G.onSide_incident_some S ⟨v,hv⟩ f').mpr hfv⟩)
  · have hv' := Finset.mem_compl.mpr hv
    obtain ⟨e, ⟨he, hev⟩, hu⟩ := M₂.property (some ⟨v,hv'⟩)
    have hev' := (G.onSide_incident_some Sᶜ ⟨v,hv'⟩ e).mp hev
    refine ⟨e.val, ⟨(G.mem_glued_right S M₁ M₂ heq e).mpr he, hev'⟩, ?_⟩
    rintro f ⟨hf, hfv⟩
    have hk : G.left f ∈ Sᶜ ∨ G.right f ∈ Sᶜ := by
      rcases hfv with h | h
      · exact Or.inl (h.symm ▸ hv')
      · exact Or.inr (h.symm ▸ hv')
    let f' : {e // G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ} := ⟨f,hk⟩
    have hf' : f' ∈ M₂.val := (G.mem_glued_right S M₁ M₂ heq f').mp hf
    exact congrArg Subtype.val (hu f' ⟨hf', (G.onSide_incident_some Sᶜ ⟨v,hv'⟩ f').mpr hfv⟩)

def glueMatching (G : LooplessGraph V E) (S : Finset V)
    (z : {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching //
      (G.boundaryEdge S z.1).val = (G.boundaryEdge Sᶜ z.2).val}) : G.Matching :=
  ⟨G.liftedEdges S z.val.1 ∪ G.liftedEdges Sᶜ z.val.2,
    G.glued_perfect S z.val.1 z.val.2 z.property⟩

omit [Fintype E] in
theorem indicator_glue_left (G : LooplessGraph V E) (S : Finset V)
    (z : {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching //
      (G.boundaryEdge S z.1).val = (G.boundaryEdge Sᶜ z.2).val})
    (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    G.indicator (G.glueMatching S z) e.val = (G.onSide S).indicator z.val.1 e := by
  simp only [indicator, glueMatching, G.mem_glued_left S z.val.1 z.val.2 z.property e]

omit [Fintype E] in
theorem indicator_glue_right (G : LooplessGraph V E) (S : Finset V)
    (z : {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching //
      (G.boundaryEdge S z.1).val = (G.boundaryEdge Sᶜ z.2).val})
    (e : {e // G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ}) :
    G.indicator (G.glueMatching S z) e.val = (G.onSide Sᶜ).indicator z.val.2 e := by
  simp only [indicator, glueMatching, G.mem_glued_right S z.val.1 z.val.2 z.property e]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem boundary_eq_iff_mem (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) (e : {e // G.left e ∈ S ∨ G.right e ∈ S})
    (hc : G.Crosses S e.val) : (G.boundaryEdge S M).val=e.val ↔ e ∈ M.val := by
  constructor
  · intro h
    have he : G.boundaryEdge S M = e := Subtype.ext h
    exact he ▸ G.boundaryEdge_mem S M
  · intro h
    exact (congrArg Subtype.val (G.eq_boundaryEdge S M h hc)).symm

omit [Fintype V] in
theorem boundary_fiber (G : LooplessGraph V E) (S : Finset V)
    (p : (G.onSide S).Matching → ℝ) (e : {e // G.left e ∈ S ∨ G.right e ∈ S})
    (hc : G.Crosses S e.val) :
    fiberMass p (fun M => (G.boundaryEdge S M).val) e.val = (G.onSide S).mean p e := by
  unfold fiberMass mean
  apply Finset.sum_congr rfl
  intro M _
  simp only [G.boundary_eq_iff_mem S M e hc, indicator]
  split <;> simp

omit [Fintype V] in
theorem boundary_fiber_zero (G : LooplessGraph V E) (S : Finset V)
    (p : (G.onSide S).Matching → ℝ) (e : E) (hc : ¬G.Crosses S e) :
    fiberMass p (fun M => (G.boundaryEdge S M).val) e = 0 := by
  apply Finset.sum_eq_zero
  intro M _
  have he : (G.boundaryEdge S M).val ≠ e := by
    intro h
    exact hc (h ▸ G.boundaryEdge_crosses S M)
  simp [he]

/-- Exact coupling across a cut, for multigraphs with distinct edge identities. -/
theorem couple_laws (G : LooplessGraph V E) (S : Finset V) (x : E → ℝ)
    {p : (G.onSide S).Matching → ℝ} {q : (G.onSide Sᶜ).Matching → ℝ}
    (hp : p ∈ probabilitySimplex (G.onSide S).Matching)
    (hq : q ∈ probabilitySimplex (G.onSide Sᶜ).Matching)
    (hpx : ∀ e, (G.onSide S).mean p e = x e.val)
    (hqx : ∀ e, (G.onSide Sᶜ).mean q e = x e.val) :
    ∃ r, r ∈ G.feasibleLaws x := by
  let f := fun M : (G.onSide S).Matching => (G.boundaryEdge S M).val
  let g := fun M : (G.onSide Sᶜ).Matching => (G.boundaryEdge Sᶜ M).val
  have hc : ∀ e, fiberMass p f e = fiberMass q g e := by
    intro e
    by_cases he : G.Crosses S e
    · have hk : G.left e ∈ S ∨ G.right e ∈ S := he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
      have he' := (G.crosses_compl S e).mpr he
      have hk' : G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ := he'.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
      rw [G.boundary_fiber S p ⟨e,hk⟩ he, G.boundary_fiber Sᶜ q ⟨e,hk'⟩ he', hpx, hqx]
    · have he' : ¬G.Crosses Sᶜ e := fun h => he ((G.crosses_compl S e).mp h)
      rw [G.boundary_fiber_zero S p e he, G.boundary_fiber_zero Sᶜ q e he']
  let Z := {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching // f z.1=g z.2}
  let w : Z → ℝ := fun z => jointLaw p q f g z.val
  have hw : w ∈ probabilitySimplex Z := compatible_jointLaw_mem_simplex hp hq f g hc
  refine ⟨fiberMass w (G.glueMatching S), fiberMass_mem_simplex hw _, ?_⟩
  ext e
  rw [mean, fiberMass_expect]
  by_cases he : G.left e ∈ S ∨ G.right e ∈ S
  · have hi : ∀ z : Z, G.indicator (G.glueMatching S z) e =
        (G.onSide S).indicator z.val.1 ⟨e,he⟩ := fun z => G.indicator_glue_left S z ⟨e,he⟩
    simp_rw [hi]
    exact (compatible_jointLaw_expect_first hp.1 f g hc
      (fun M => (G.onSide S).indicator M ⟨e,he⟩)).trans (hpx ⟨e,he⟩)
  · have he' : G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ := by
      simp only [not_or] at he
      exact Or.inl (Finset.mem_compl.mpr he.1)
    have hi : ∀ z : Z, G.indicator (G.glueMatching S z) e =
        (G.onSide Sᶜ).indicator z.val.2 ⟨e,he'⟩ := fun z => G.indicator_glue_right S z ⟨e,he'⟩
    simp_rw [hi]
    exact (compatible_jointLaw_expect_second hq.1 f g hc
      (fun M => (G.onSide Sᶜ).indicator M ⟨e,he'⟩)).trans (hqx ⟨e,he'⟩)

def sideMap (S : Finset V) (v : V) : Option {v // v ∈ S} :=
  if h : v ∈ S then some ⟨v,h⟩ else none

def liftVertices (S : Finset V) (T : Finset (Option {v // v ∈ S})) : Finset V :=
  Finset.univ.filter (fun v => sideMap S v ∈ T)

@[simp] theorem mem_liftVertices (S : Finset V)
    (T : Finset (Option {v // v ∈ S})) (v : V) :
    v ∈ liftVertices S T ↔ sideMap S v ∈ T := by simp [liftVertices]

omit [Fintype V] in
@[simp] theorem sideMap_some (S : Finset V) (v : {v // v ∈ S}) :
    sideMap S v.val = some v := by
  simp [sideMap, v.property]

theorem liftVertices_card (S : Finset V) (T : Finset (Option {v // v ∈ S}))
    (hn : none ∉ T) : (liftVertices S T).card = T.card := by
  apply Finset.card_bij (fun v _ => sideMap S v)
  · intro v hv
    exact (mem_liftVertices S T v).mp hv
  · intro v hv w hw he
    have hvS : v ∈ S := by
      by_contra h
      have hmem := (mem_liftVertices S T v).mp hv
      simp only [sideMap, h, ↓reduceDIte] at hmem
      exact hn hmem
    have hwS : w ∈ S := by
      by_contra h
      have hmem := (mem_liftVertices S T w).mp hw
      simp only [sideMap, h, ↓reduceDIte] at hmem
      exact hn hmem
    simp only [sideMap, hvS, hwS, ↓reduceDIte, Option.some.injEq] at he
    exact congrArg Subtype.val he
  · intro t ht
    cases t with
    | none => exact (hn ht).elim
    | some v => exact ⟨v.val, by simpa only [mem_liftVertices, sideMap_some] using ht, sideMap_some S v⟩

omit [Fintype E] [DecidableEq E] in
theorem onSide_cut_crosses (G : LooplessGraph V E) (S : Finset V)
    (T : Finset (Option {v // v ∈ S})) (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    (G.onSide S).Crosses T e ↔ G.Crosses (liftVertices S T) e.val := by
  simp only [Crosses, mem_liftVertices]
  rfl

omit [Fintype E] [DecidableEq E] in
theorem crosses_lift_kept (G : LooplessGraph V E) (S : Finset V)
    (T : Finset (Option {v // v ∈ S})) (e : E)
    (he : G.Crosses (liftVertices S T) e) : G.left e ∈ S ∨ G.right e ∈ S := by
  by_contra h
  simp only [not_or] at h
  simp only [Crosses, mem_liftVertices, sideMap, h.1, h.2, ↓reduceDIte] at he
  tauto

omit [DecidableEq E] in
theorem onSide_cutMass (G : LooplessGraph V E) (S : Finset V)
    (x : E → ℝ) (T : Finset (Option {v // v ∈ S})) :
    (G.onSide S).cutMass (fun e => x e.val) T = G.cutMass x (liftVertices S T) := by
  simp only [cutMass, cut, Finset.sum_filter]
  simp_rw [G.onSide_cut_crosses S T]
  exact sum_subtype_supported (fun e => G.left e ∈ S ∨ G.right e ∈ S)
    (fun e => if G.Crosses (liftVertices S T) e then x e else 0)
    (by intro e he; rw [ite_eq_right (fun hc => he (G.crosses_lift_kept S T e hc))])

omit [Fintype V] [DecidableEq E] in
theorem onSide_degree_some (G : LooplessGraph V E) (S : Finset V)
    (x : E → ℝ) (v : {v // v ∈ S}) :
    (G.onSide S).degree (fun e => x e.val) (some v) = G.degree x v.val := by
  simp only [degree]
  simp_rw [G.onSide_incident_some S v]
  apply sum_subtype_supported (fun e => G.left e ∈ S ∨ G.right e ∈ S)
    (fun e => if G.Incident v.val e then x e else 0)
  intro e he
  rw [ite_eq_right]
  rintro (h | h)
  · exact he (Or.inl (h.symm ▸ v.property))
  · exact he (Or.inr (h.symm ▸ v.property))

omit [Fintype V] [DecidableEq E] in
theorem onSide_degree_none (G : LooplessGraph V E) (S : Finset V) (x : E → ℝ) :
    (G.onSide S).degree (fun e => x e.val) none = G.cutMass x S := by
  simp only [degree, cutMass, cut, Finset.sum_filter]
  simp_rw [G.onSide_incident_none S]
  apply sum_subtype_supported (fun e => G.left e ∈ S ∨ G.right e ∈ S)
    (fun e => if G.Crosses S e then x e else 0)
  intro e he
  rw [ite_eq_right]
  rintro (h | h)
  · exact he (Or.inl h.1)
  · exact he (Or.inr h.2)

theorem odd_compl_of_even {W : Type*} [Fintype W] [DecidableEq W]
    (hn : Even (Fintype.card W)) {T : Finset W} (hT : Odd T.card) : Odd Tᶜ.card := by
  rcases hn with ⟨k,hk⟩
  rcases hT with ⟨l,hl⟩
  have hle := Finset.card_le_univ T
  rw [Finset.card_compl]
  refine ⟨k-l-1, ?_⟩
  omega

omit [DecidableEq E] in
/-- Exact inheritance of the odd-cut system under contraction of a tight odd cut. -/
theorem restriction_mem_constraints (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) (S : Finset V) (hS : Odd S.card)
    (htight : G.cutMass x S = 1) :
    (fun e : {e // G.left e ∈ S ∨ G.right e ∈ S} => x e.val) ∈
      (G.onSide S).constraintPolytope := by
  refine ⟨fun e => hx.1 e.val, ?_, ?_⟩
  · intro v
    cases v with
    | none => exact (G.onSide_degree_none S x).trans htight
    | some v => exact (G.onSide_degree_some S x v).trans (hx.2.1 v.val)
  · intro T hT
    by_cases hn : none ∈ T
    · have hn' : none ∉ Tᶜ := by simpa using hn
      have hnEven : Even (Fintype.card (Option {v // v ∈ S})) := by
        simp only [Fintype.card_option, Fintype.card_coe]
        exact hS.add_odd odd_one
      have hTc := odd_compl_of_even hnEven hT
      have hh := hx.2.2 (liftVertices S Tᶜ) (by rwa [liftVertices_card S Tᶜ hn'])
      rw [← G.onSide_cutMass S x Tᶜ] at hh
      simpa only [cutMass, cut_compl] using hh
    · rw [G.onSide_cutMass S x T]
      exact hx.2.2 _ (by rwa [liftVertices_card S T hn])

end LooplessGraph

end MatchingEntropy

end

end OAI
end
end

section
section
namespace OAI

/-!
Finite polyhedra, local perturbations, and quotient dimension bounds.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

section PolyhedralPrelude
variable {I J : Type*} [Fintype I] [Fintype J]

def finitePolyhedron (L : I → (J → ℝ) →ₗ[ℝ] ℝ) (b : I → ℝ) : Set (J → ℝ) :=
  {x | ∀ i, L i x ≤ b i}

/-- Finite slack, with every active equation preserved, permits both signs. -/
theorem finitePolyhedron_eventually_line (L : I → (J → ℝ) →ₗ[ℝ] ℝ) (b : I → ℝ)
    {x : J → ℝ} (hx : x ∈ finitePolyhedron L b) (u : J → ℝ)
    (hu : ∀ i, L i x = b i → L i u = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, x+t • u ∈ finitePolyhedron L b := by
  apply Filter.eventually_all.mpr
  intro i
  by_cases hi : L i x=b i
  · apply Filter.Eventually.of_forall
    intro t
    rw [map_add, map_smul, hu i hi, smul_zero, add_zero, hi]
  · have hlt : L i x < b i := lt_of_le_of_ne (hx i) hi
    have hc : Continuous (fun t : ℝ => L i (x+t • u)) :=
      (L i).continuous_of_finiteDimensional.comp (by fun_prop)
    have hh : ∀ᶠ t : ℝ in 𝓝 0, L i (x+t • u) < b i :=
      (isOpen_lt hc continuous_const).mem_nhds (by simpa using hlt : L i (x+(0:ℝ) • u) < b i)
    exact hh.mono fun t ht => le_of_lt ht

/-- Radial expansion about x preserves every active inequality for arbitrary
nearby feasible points. Inactive inequalities are handled by finite slack. -/
theorem finitePolyhedron_eventually_expand (L : I → (J → ℝ) →ₗ[ℝ] ℝ) (b : I → ℝ)
    {x : J → ℝ} (hx : x ∈ finitePolyhedron L b) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ y in 𝓝[finitePolyhedron L b] x, x+t⁻¹ • (y-x) ∈ finitePolyhedron L b := by
  apply Filter.eventually_all.mpr
  intro i
  by_cases hi : L i x=b i
  · filter_upwards [eventually_mem_nhdsWithin] with y hy
    rw [map_add, map_smul, map_sub, hi]
    change b i+t⁻¹ * (L i y-b i) ≤ b i
    have hh := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le) (sub_nonpos.mpr (hy i))
    linarith
  · have hlt : L i x < b i := lt_of_le_of_ne (hx i) hi
    have hc : Continuous (fun y : J → ℝ => L i (x+t⁻¹ • (y-x))) :=
      (L i).continuous_of_finiteDimensional.comp (by fun_prop)
    have hh : ∀ᶠ y : J → ℝ in 𝓝 x, L i (x+t⁻¹ • (y-x)) < b i :=
      (isOpen_lt hc continuous_const).mem_nhds (by simpa using hlt : L i (x+t⁻¹ • (x-x)) < b i)
    exact (hh.filter_mono nhdsWithin_le_nhds).mono fun y hy => le_of_lt hy

omit [Fintype J] in
theorem extreme_point_direction_zero (P : Set (J → ℝ)) {x : J → ℝ}
    (hx : x ∈ Set.extremePoints ℝ P) (u : J → ℝ)
    (hu : ∀ᶠ t : ℝ in 𝓝 0, x+t • u ∈ P) : u=0 := by
  have hu' : ∀ᶠ t : ℝ in 𝓝 0, x+(-t) • u ∈ P := by
    have hc : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by simpa using (continuous_neg.tendsto (0:ℝ))
    exact hc.eventually hu
  -- choose a strictly positive point using the right-hand punctured neighborhood
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, (x+t • u ∈ P ∧ x+(-t) • u ∈ P) ∧ 0<t :=
    ((hu.and hu').filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  obtain ⟨a,⟨ha,hna⟩,ha0⟩ := hh.exists
  have hseg : x ∈ openSegment ℝ (x+a • u) (x+(-a) • u) := by
    refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have he := (mem_extremePoints.mp hx).2 _ ha _ hna hseg |>.1
  ext j
  have hj := congrFun he j
  change x j+a*u j=x j at hj
  change u j=0
  exact (mul_eq_zero.mp (by linarith : a*u j=0)).resolve_left (ne_of_gt ha0)


section LinearHelper
open Module
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module ℝ A] [Module ℝ B] [Module ℝ C]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]

theorem quotient_finrank_le_of_ker_le (U : Submodule ℝ A) (f : A →ₗ[ℝ] B)
    (h : f.ker ≤ U) : finrank ℝ (A ⧸ U) ≤ finrank ℝ B := by
  have h1 := U.finrank_quotient_add_finrank
  have h2 := f.finrank_range_add_finrank_ker
  have h3 := Submodule.finrank_mono h
  have h4 : finrank ℝ f.range ≤ finrank ℝ B := Submodule.finrank_le _
  omega

theorem quotient_finrank_le_pair (U : Submodule ℝ A) (W : Submodule ℝ B) (Z : Submodule ℝ C)
    (f : A →ₗ[ℝ] B) (g : A →ₗ[ℝ] C)
    (h : ∀ u, f u ∈ W → g u ∈ Z → u ∈ U) :
    finrank ℝ (A ⧸ U) ≤ finrank ℝ (B ⧸ W)+finrank ℝ (C ⧸ Z) := by
  let F := (W.mkQ.comp f).prod (Z.mkQ.comp g)
  have hk : F.ker ≤ U := by
    intro u hu
    have hh : (W.mkQ (f u), Z.mkQ (g u))=0 := hu
    have hW : f u ∈ W := by
      have hq := congrArg Prod.fst hh
      simpa using hq
    have hZ : g u ∈ Z := by
      have hq := congrArg Prod.snd hh
      simpa using hq
    exact h u hW hZ
  simpa using quotient_finrank_le_of_ker_le U F hk

end LinearHelper
end PolyhedralPrelude

end MatchingEntropy

end

end OAI
end
end

section
section
namespace OAI

/-!
Tutte's criterion and Edmonds' perfect matching polytope theorem for multigraphs.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

/-- The simple support graph forgets only parallel-edge identities. -/
def supportSimple (G : LooplessGraph V E) (x : E → ℝ) : SimpleGraph V where
  Adj v w := ∃ e, 0 < x e ∧ ((G.left e=v ∧ G.right e=w) ∨ (G.left e=w ∧ G.right e=v))
  symm := ⟨by intro v w; rintro ⟨e,hx,h⟩; exact ⟨e,hx,h.symm⟩⟩
  loopless := ⟨by
    intro v
    rintro ⟨e,_,(⟨hl,hr⟩ | ⟨hl,hr⟩)⟩ <;> exact G.loopless e (hl.trans hr.symm)⟩

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
 theorem supportSimple_edge (G : LooplessGraph V E) {x : E → ℝ} {e : E} (he : 0 < x e) :
    (G.supportSimple x).Adj (G.left e) (G.right e) := ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩

theorem sum_pred_le_one {C : Type*} [Fintype C] (P : C → Prop) [DecidablePred P]
    (huniq : ∀ a b, P a → P b → a=b) : (∑ c, if P c then (1 : ℝ) else 0) ≤ 1 := by
  by_cases h : ∃ a, P a
  · obtain ⟨a,ha⟩ := h
    rw [Finset.sum_eq_single a]
    · simp [ha]
    · intro b _ hb
      rw [ite_eq_right]
      intro hPb
      exact hb (huniq b a hPb ha)
    · simp
  · simp only [not_exists] at h
    simp [h]

omit [Fintype V] [DecidableEq E] in
/-- The weighted cut-counting argument in Tutte's criterion. -/
theorem odd_family_bound (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {C : Type*} [Fintype C] [DecidableEq C]
    (U : Finset V) (T : C → Finset V)
    (hodd : ∀ c, Odd (T c).card)
    (hdisj : ∀ c v, v ∈ T c → v ∉ U)
    (huniq : ∀ a b v, v ∈ T a → v ∈ T b → a=b)
    (hclosed : ∀ e, 0 < x e → G.left e ∉ U → G.right e ∉ U →
      ∀ c, G.left e ∈ T c ↔ G.right e ∈ T c) :
    Fintype.card C ≤ U.card := by
  have hcuts : (Fintype.card C : ℝ) ≤ ∑ c, G.cutMass x (T c) := by
    calc
      _ = ∑ c : C, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun c _ => hx.2.2 (T c) (hodd c)
  have hedges : ∀ e, (∑ c, if G.Crosses (T c) e then x e else 0) ≤
      (if G.left e ∈ U then x e else 0) + (if G.right e ∈ U then x e else 0) := by
    intro e
    by_cases hz : x e=0
    · simp [hz]
    have hp : 0 < x e := lt_of_le_of_ne (hx.1 e) (Ne.symm hz)
    by_cases hl : G.left e ∈ U <;> by_cases hr : G.right e ∈ U
    · have hzero : ∀ c, ¬G.Crosses (T c) e := by
        intro c hc
        rcases hc with h | h
        · exact hdisj c _ h.1 hl
        · exact hdisj c _ h.2 hr
      simp [hzero, hl, hr, hx.1 e]
    · have heq : ∀ c, G.Crosses (T c) e ↔ G.right e ∈ T c := by
        intro c
        have hn : G.left e ∉ T c := fun h => hdisj c _ h hl
        simp [Crosses, hn]
      simp_rw [heq]
      have hcount := sum_pred_le_one (fun c => G.right e ∈ T c)
        (fun a b => huniq a b (G.right e))
      have heq' : (∑ c, if G.right e ∈ T c then x e else 0) =
          (∑ c, if G.right e ∈ T c then (1 : ℝ) else 0) * x e := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        split <;> simp
      rw [heq']
      simpa [hl, hr] using mul_le_mul_of_nonneg_right hcount (hx.1 e)
    · have heq : ∀ c, G.Crosses (T c) e ↔ G.left e ∈ T c := by
        intro c
        have hn : G.right e ∉ T c := fun h => hdisj c _ h hr
        simp [Crosses, hn]
      simp_rw [heq]
      have hcount := sum_pred_le_one (fun c => G.left e ∈ T c)
        (fun a b => huniq a b (G.left e))
      have heq' : (∑ c, if G.left e ∈ T c then x e else 0) =
          (∑ c, if G.left e ∈ T c then (1 : ℝ) else 0) * x e := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        split <;> simp
      rw [heq']
      simpa [hl, hr] using mul_le_mul_of_nonneg_right hcount (hx.1 e)
    · have hzero : ∀ c, ¬G.Crosses (T c) e := by
        intro c hc
        have hiff := hclosed e hp hl hr c
        unfold Crosses at hc
        tauto
      simp [hzero, hl, hr]
  have hdegree : ∑ v ∈ U, G.degree x v = (U.card : ℝ) := by
    simp_rw [hx.2.1]
    simp
  have hsum : (∑ e : E, ((if G.left e ∈ U then x e else 0) +
      (if G.right e ∈ U then x e else 0))) = ∑ v ∈ U, G.degree x v := by
    simp only [degree]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    have hf : ∀ v, (if G.Incident v e then x e else 0) =
        (if G.left e = v then x e else 0) + (if G.right e = v then x e else 0) := by
      intro v
      by_cases hl : G.left e=v <;> by_cases hr : G.right e=v
      · exact (G.loopless e (hl.trans hr.symm)).elim
      all_goals simp [Incident, hl, hr]
    simp_rw [hf]
    rw [Finset.sum_add_distrib]
    simp
  have hbound := (Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hedges e))
  rw [hsum, hdegree] at hbound
  have hcutEq : (∑ c, G.cutMass x (T c)) = ∑ e, ∑ c, if G.Crosses (T c) e then x e else 0 := by
    simp only [cutMass, cut, Finset.sum_filter]
    exact Finset.sum_comm
  exact_mod_cast hcuts.trans (hcutEq ▸ hbound)


omit [DecidableEq E] in
theorem supportSimple_has_perfectMatching (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) :
    ∃ M : (G.supportSimple x).Subgraph, M.IsPerfectMatching := by
  classical
  apply SimpleGraph.tutte.mpr
  intro U
  let H := (⊤ : (G.supportSimple x).Subgraph).deleteVerts U
  let C := H.coe.oddComponents
  let : Fintype C := Fintype.ofFinite C
  let T : C → Finset V := fun c => (Subtype.val '' c.val.supp).toFinset
  have hnot : ∀ v : H.verts, v.val ∉ U := by
    intro v
    have hv := v.property
    simpa [H] using hv
  have hT : ∀ c : C, ∀ v : V, v ∈ T c ↔ ∃ w : H.verts, w ∈ c.val.supp ∧ w.val=v := by
    intro c v
    simp [T]
  have hodd : ∀ c : C, Odd (T c).card := by
    intro c
    have hc := c.property
    change Odd c.val.supp.ncard at hc
    change Odd ((Subtype.val '' c.val.supp).toFinset.card)
    rw [← Set.ncard_eq_toFinset_card', Set.ncard_image_of_injective _ Subtype.val_injective]
    exact hc
  have hdisj : ∀ c v, v ∈ T c → v ∉ U.toFinset := by
    intro c v hv
    obtain ⟨w,_,rfl⟩ := (hT c v).mp hv
    simpa using hnot w
  have huniq : ∀ a b v, v ∈ T a → v ∈ T b → a=b := by
    intro a b v ha hb
    obtain ⟨wa,hwa,rfl⟩ := (hT a v).mp ha
    obtain ⟨wb,hwb,he⟩ := (hT b wa.val).mp hb
    have hw : wb=wa := Subtype.ext he
    subst wb
    exact Subtype.ext (SimpleGraph.ConnectedComponent.eq_of_common_vertex hwa hwb)
  have hclosed : ∀ e, 0<x e → G.left e ∉ U.toFinset → G.right e ∉ U.toFinset →
      ∀ c, G.left e ∈ T c ↔ G.right e ∈ T c := by
    intro e he hl hr c
    have hl' : G.left e ∈ H.verts := by simpa [H] using hl
    have hr' : G.right e ∈ H.verts := by simpa [H] using hr
    have ha : H.Adj (G.left e) (G.right e) := by
      simpa [H, SimpleGraph.Subgraph.deleteVerts_adj] using
        And.intro hl (And.intro hr (G.supportSimple_edge he))
    change G.left e ∈ (Subtype.val '' c.val.supp).toFinset ↔
      G.right e ∈ (Subtype.val '' c.val.supp).toFinset
    simp only [Set.mem_toFinset]
    exact ⟨fun h => SimpleGraph.ConnectedComponent.mem_coe_supp_of_adj h hr' ha,
      fun h => SimpleGraph.ConnectedComponent.mem_coe_supp_of_adj h hl' ha.symm⟩
  have hb := G.odd_family_bound hx U.toFinset T hodd hdisj huniq hclosed
  change ¬ U.ncard < H.coe.oddComponents.ncard
  have hcard : Fintype.card C = H.coe.oddComponents.ncard := by
    simp [C, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rw [hcard] at hb
  exact not_lt_of_ge (by simpa only [← Set.ncard_eq_toFinset_card'] using hb)


theorem exists_supported_matching (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) :
    ∃ M : G.Matching, ∀ e ∈ M.val, 0 < x e := by
  classical
  obtain ⟨M,hM⟩ := G.supportSimple_has_perfectMatching hx
  have he : ∀ q ∈ M.edgeSet, ∃ e, 0<x e ∧ s(G.left e,G.right e)=q := by
    intro q
    induction q using Sym2.inductionOn with
    | hf v w =>
      intro hq
      obtain ⟨e,he,hor⟩ := (SimpleGraph.Subgraph.mem_edgeSet.mp hq).adj_sub
      refine ⟨e,he,Sym2.eq_iff.mpr hor⟩
  let f : M.edgeSet → E := fun q => (he q.val q.property).choose
  have hf : ∀ q, 0<x (f q) ∧ s(G.left (f q),G.right (f q))=q.val :=
    fun q => (he q.val q.property).choose_spec
  let F : Finset E := Finset.univ.image f
  have hF : G.IsPerfectMatching F := by
    intro v
    obtain ⟨w,hw,hu⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM v
    let q : M.edgeSet := ⟨s(v,w),SimpleGraph.Subgraph.mem_edgeSet.mpr hw⟩
    refine ⟨f q,⟨Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩,?_⟩,?_⟩
    · rcases Sym2.eq_iff.mp (hf q).2 with h | h
      · exact Or.inl h.1
      · exact Or.inr h.2
    · intro e he'
      obtain ⟨q',_,rfl⟩ := Finset.mem_image.mp he'.1
      have hq : q'=q := by
        apply Subtype.ext
        rcases he'.2 with hl | hr
        · have hval : q'.val=s(v,G.right (f q')) := by rw [← (hf q').2, hl]
          have hAdj : M.Adj v (G.right (f q')) :=
            SimpleGraph.Subgraph.mem_edgeSet.mp (hval ▸ q'.property)
          rw [hval, hu _ hAdj]
        · have hval : q'.val=s(v,G.left (f q')) := by
            rw [← (hf q').2, hr, Sym2.eq_swap]
          have hAdj : M.Adj v (G.left (f q')) :=
            SimpleGraph.Subgraph.mem_edgeSet.mp (hval ▸ q'.property)
          rw [hval, hu _ hAdj]
      exact congrArg f hq
  refine ⟨⟨F,hF⟩,?_⟩
  intro e he'
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp he'
  exact (hf q).1


omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem crosses_singleton (G : LooplessGraph V E) (v : V) (e : E) :
    G.Crosses {v} e ↔ G.Incident v e := by
  have hh := G.loopless e
  simp only [Crosses, Finset.mem_singleton, Incident]
  have hn : ¬ (G.left e=v ∧ G.right e=v) := fun h => hh (h.1.trans h.2.symm)
  tauto

omit [Fintype V] [DecidableEq E] in
@[simp] theorem cutMass_singleton (G : LooplessGraph V E) (x : E → ℝ) (v : V) :
    G.cutMass x {v} = G.degree x v := by
  simp [cutMass,cut,Finset.sum_filter,degree]

omit [DecidableEq E] in
/-- Local two-sided perturbations for the degree and odd-cut constraint system. -/
theorem constraint_eventually_line (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) (u : E → ℝ)
    (hzero : ∀ e, x e=0 → u e=0) (hdeg : ∀ v, G.degree u v=0)
    (hcut : ∀ S, Odd S.card → G.cutMass x S=1 → G.cutMass u S=0) :
    ∀ᶠ t : ℝ in 𝓝 0, x+t • u ∈ G.constraintPolytope := by
  have hn : ∀ᶠ t : ℝ in 𝓝 0, ∀ e, 0≤(x+t • u) e := by
    apply Filter.eventually_all.mpr
    intro e
    by_cases he : x e=0
    · exact Filter.Eventually.of_forall (by intro t; simp [he,hzero e he])
    · have hp : 0<x e := lt_of_le_of_ne (hx.1 e) (Ne.symm he)
      have hc : Continuous (fun t : ℝ => (x+t • u) e) := by fun_prop
      have hh : ∀ᶠ t : ℝ in 𝓝 0, 0<(x+t • u) e := (isOpen_lt continuous_const hc).mem_nhds
        (by simpa using hp : 0<(x+(0:ℝ) • u) e)
      exact hh.mono fun t ht => ht.le
  have hodd : ∀ᶠ t : ℝ in 𝓝 0, ∀ S : Finset V, Odd S.card → 1≤G.cutMass (x+t • u) S := by
    apply Filter.eventually_all.mpr
    intro S
    by_cases hS : Odd S.card
    · by_cases ht : G.cutMass x S=1
      · exact Filter.Eventually.of_forall (by
          intro t _
          have he := G.cutMass_linear x u 1 t S
          simp only [one_smul, one_mul, hcut S hS ht, mul_zero, add_zero, ht] at he
          exact he.ge)
      · have hp : 1<G.cutMass x S := lt_of_le_of_ne (hx.2.2 S hS) (Ne.symm ht)
        have hc : Continuous (fun t : ℝ => G.cutMass (x+t • u) S) :=
          (G.continuous_cutMass S).comp (by fun_prop)
        have hh : ∀ᶠ t : ℝ in 𝓝 0, 1<G.cutMass (x+t • u) S := (isOpen_lt continuous_const hc).mem_nhds
          (by simpa using hp : 1<G.cutMass (x+(0:ℝ) • u) S)
        exact hh.mono fun t ht _ => ht.le
    · exact Filter.Eventually.of_forall fun _ h => (hS h).elim
  filter_upwards [hn,hodd] with t hn hodd
  refine ⟨hn,?_,hodd⟩
  intro v
  have he := G.degree_linear x u 1 t v
  simpa only [one_smul, one_mul, hdeg, mul_zero, add_zero, hx.2.1] using he

omit [Fintype V] [DecidableEq E] in
 theorem degree_sub (G : LooplessGraph V E) (x y : E → ℝ) (v : V) :
    G.degree (x-y) v = G.degree x v-G.degree y v := by
  have h := G.degree_linear x y 1 (-1) v
  simpa [sub_eq_add_neg] using h

omit [Fintype V] [DecidableEq E] in
 theorem cutMass_sub (G : LooplessGraph V E) (x y : E → ℝ) (S : Finset V) :
    G.cutMass (x-y) S = G.cutMass x S-G.cutMass y S := by
  have h := G.cutMass_linear x y 1 (-1) S
  simpa [sub_eq_add_neg] using h

omit [DecidableEq E] in
/-- Without a nontrivial tight odd cut, only degrees constrain a supported direction. -/
theorem trivial_tight_cut_preserved (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V))
    (hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1)
    (u : E → ℝ) (hdeg : ∀ v, G.degree u v=0) :
    ∀ S, Odd S.card → G.cutMass x S=1 → G.cutMass u S=0 := by
  intro S hS ht
  have hc := odd_compl_of_even heven hS
  have hsmall : S.card=1 ∨ Sᶜ.card=1 := by
    have hn : ¬ (3≤S.card ∧ 3≤Sᶜ.card) := fun h => hnt ⟨S,hS,h.1,h.2,ht⟩
    rcases hS with ⟨k,hk⟩
    rcases hc with ⟨l,hl⟩
    omega
  rcases hsmall with hs | hs
  · obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hs
    simpa using hdeg v
  · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hs
    have hh : G.cutMass u Sᶜ=0 := by rw [hv,cutMass_singleton,hdeg]
    simpa only [cutMass,cut_compl] using hh

 theorem extreme_no_tight_integral (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ Set.extremePoints ℝ G.constraintPolytope)
    (hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1) :
    ∃ M : G.Matching, G.indicator M=x := by
  have hxQ := (mem_extremePoints.mp hx).1
  obtain ⟨M,hM⟩ := G.exists_supported_matching hxQ
  have hd : ∀ v, G.degree (G.indicator M-x) v=0 := by
    intro v
    rw [degree_sub,degree_indicator,hxQ.2.1,sub_self]
  have hz : ∀ e, x e=0 → (G.indicator M-x) e=0 := by
    intro e he
    have hn : e ∉ M.val := fun h => (hM e h).ne' he
    simp [indicator,hn,he]
  have hu := G.constraint_eventually_line hxQ (G.indicator M-x) hz hd
    (G.trivial_tight_cut_preserved heven hnt _ hd)
  have he := extreme_point_direction_zero G.constraintPolytope hx _ hu
  exact ⟨M,sub_eq_zero.mp he⟩


/-- Induction over even orders, using only proved cut coupling and Mathlib Tutte. -/
theorem constraint_subset_polytope_aux (n : ℕ) :
    ∀ {W F : Type*} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (G : LooplessGraph W F), Fintype.card W=n → Even n →
      G.constraintPolytope ⊆ G.polytope := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W F _ _ _ _ G hcard heven
    have heven' : Even (Fintype.card W) := hcard ▸ heven
    have hex : Set.extremePoints ℝ G.constraintPolytope ⊆ G.polytope := by
      intro x hx
      have hxQ := (mem_extremePoints.mp hx).1
      by_cases hcut : ∃ S : Finset W, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1
      · obtain ⟨S,hS,hlo,hhi,ht⟩ := hcut
        have hc := odd_compl_of_even heven' hS
        have hlt1 : Fintype.card (Option {v // v ∈ S}) < n := by
          simp only [Fintype.card_option,Fintype.card_coe]
          have hco := Finset.card_compl S
          omega
        have hlt2 : Fintype.card (Option {v // v ∈ Sᶜ}) < n := by
          simp only [Fintype.card_option,Fintype.card_coe]
          have hco := Finset.card_compl S
          have hle := Finset.card_le_univ S
          omega
        have hv1 : Even (Fintype.card (Option {v // v ∈ S})) := by
          simpa only [Fintype.card_option,Fintype.card_coe] using hS.add_odd odd_one
        have hv2 : Even (Fintype.card (Option {v // v ∈ Sᶜ})) := by
          simpa only [Fintype.card_option,Fintype.card_coe] using hc.add_odd odd_one
        have hx1 := ih _ hlt1 (G.onSide S) rfl hv1 (G.restriction_mem_constraints hxQ S hS ht)
        have htc : G.cutMass x Sᶜ=1 := by simpa only [cutMass,cut_compl] using ht
        have hx2 := ih _ hlt2 (G.onSide Sᶜ) rfl hv2 (G.restriction_mem_constraints hxQ Sᶜ hc htc)
        obtain ⟨p,hp,hpx⟩ := ((G.onSide S).mem_polytope_iff _).mp hx1
        obtain ⟨q,hq,hqx⟩ := ((G.onSide Sᶜ).mem_polytope_iff _).mp hx2
        exact (G.mem_polytope_iff x).mpr (G.couple_laws S x hp hq (congrFun hpx) (congrFun hqx))
      · obtain ⟨M,rfl⟩ := G.extreme_no_tight_integral heven' hx hcut
        exact subset_convexHull ℝ _ (Set.mem_range_self M)
    rw [← closure_convexHull_extremePoints G.isCompact_constraintPolytope G.convex_constraintPolytope]
    exact closure_minimal (convexHull_min hex (convex_convexHull ℝ _)) G.compact_polytope.isClosed

/-- Edmonds' perfect matching polytope equality, with parallel edges retained. -/
theorem polytope_eq_constraints (G : LooplessGraph V E) (heven : Even (Fintype.card V)) :
    G.polytope = G.constraintPolytope := by
  exact Set.Subset.antisymm G.polytope_subset_constraintPolytope
    (constraint_subset_polytope_aux (Fintype.card V) G rfl heven)

end LooplessGraph

end MatchingEntropy

end

end OAI
end
end

section
section
namespace OAI

/-!
Active face spaces, their codimension bounds, and local radial extension.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

/-- Restrict the ambient vector space to the genuinely positive edge coordinates. -/
def positiveExtension (x : E → ℝ) : ({e // 0<x e} → ℝ) →ₗ[ℝ] (E → ℝ) := by
  classical
  exact {
    toFun := fun u e => if h : 0<x e then u ⟨e,h⟩ else 0
    map_add' := by intro u v; ext e; by_cases h : 0<x e <;> simp [h]
    map_smul' := by intro a u; ext e; by_cases h : 0<x e <;> simp [h] }

omit [Fintype E] [DecidableEq E] in
@[simp] theorem positiveExtension_pos (x : E → ℝ) (u : {e // 0<x e} → ℝ)
    (e : {e // 0<x e}) : positiveExtension x u e.val=u e := by
  simp [positiveExtension,e.property]

omit [Fintype E] [DecidableEq E] in
@[simp] theorem positiveExtension_zero (x : E → ℝ) (u : {e // 0<x e} → ℝ)
    {e : E} (he : x e=0) : positiveExtension x u e=0 := by
  simp [positiveExtension,he]

def degreeLinear (G : LooplessGraph V E) : (E → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun := G.degree
  map_add' := by
    intro u v
    ext w
    simpa using G.degree_linear u v 1 1 w
  map_smul' := by
    intro a u
    ext w
    simp only [degree,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    split <;> simp

def cutLinear (G : LooplessGraph V E) (S : Finset V) : (E → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun u => G.cutMass u S
  map_add' := by intro u v; simpa using G.cutMass_linear u v 1 1 S
  map_smul' := by intro a u; simp [cutMass,Finset.mul_sum]

/-- The exact active degree and odd-cut kernel, on the positive edge support. -/
def faceSpace (G : LooplessGraph V E) (x : E → ℝ) : Submodule ℝ ({e // 0<x e} → ℝ) where
  carrier := {u | G.degreeLinear (positiveExtension x u)=0 ∧
    ∀ S : Finset V, Odd S.card → G.cutMass x S=1 → G.cutLinear S (positiveExtension x u)=0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    refine ⟨by simp only [map_add,hu.1,hv.1,add_zero],?_⟩
    intro S hS ht
    simp only [map_add,hu.2 S hS ht,hv.2 S hS ht,add_zero]
  smul_mem' := by
    intro a u hu
    refine ⟨by simp only [map_smul,hu.1,smul_zero],?_⟩
    intro S hS ht
    simp only [map_smul,hu.2 S hS ht,smul_zero]

def faceCodimension (G : LooplessGraph V E) (x : E → ℝ) : ℕ :=
  Module.finrank ℝ (({e // 0<x e} → ℝ) ⧸ G.faceSpace x)

omit [DecidableEq E] in
 theorem faceCodimension_no_tight (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V))
    (hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1) :
    G.faceCodimension x ≤ Fintype.card V := by
  classical
  let F := G.degreeLinear.comp (positiveExtension x)
  have hk : F.ker ≤ G.faceSpace x := by
    intro u hu
    have hd : G.degreeLinear (positiveExtension x u)=0 := hu
    refine ⟨hd,?_⟩
    exact G.trivial_tight_cut_preserved heven hnt _ (congrFun hd)
  simpa [faceCodimension] using quotient_finrank_le_of_ker_le (G.faceSpace x) F hk

omit [DecidableEq E] in
 theorem faceSpace_eventually_line (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {u : {e // 0<x e} → ℝ} (hu : u ∈ G.faceSpace x) :
    ∀ᶠ t : ℝ in 𝓝 0, x+t • positiveExtension x u ∈ G.constraintPolytope := by
  exact G.constraint_eventually_line hx _ (fun e he => positiveExtension_zero x u he)
    (congrFun hu.1) hu.2

omit [Fintype V] [DecidableEq E] in
 theorem faceSpace_of_eventually_line (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {u : {e // 0<x e} → ℝ}
    (hu : ∀ᶠ t : ℝ in 𝓝 0, x+t • positiveExtension x u ∈ G.constraintPolytope) :
    u ∈ G.faceSpace x := by
  have hu' : ∀ᶠ t : ℝ in 𝓝 0, x+(-t) • positiveExtension x u ∈ G.constraintPolytope := by
    have hc : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by simpa using continuous_neg.tendsto (0:ℝ)
    exact hc.eventually hu
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (x+t • positiveExtension x u ∈ G.constraintPolytope ∧
        x+(-t) • positiveExtension x u ∈ G.constraintPolytope) ∧ 0<t :=
    ((hu.and hu').filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  obtain ⟨a,⟨ha,hna⟩,ha0⟩ := hh.exists
  refine ⟨?_,?_⟩
  · ext v
    have he := G.degree_linear x (positiveExtension x u) 1 a v
    simp only [one_smul,one_mul,hx.2.1,ha.2.1] at he
    change G.degree (positiveExtension x u) v=0
    nlinarith
  · intro S hS ht
    have he := G.cutMass_linear x (positiveExtension x u) 1 a S
    have he' := G.cutMass_linear x (positiveExtension x u) 1 (-a) S
    simp only [one_smul,one_mul,ht] at he he'
    have hp := ha.2.2 S hS
    have hn := hna.2.2 S hS
    change G.cutMass (positiveExtension x u) S=0
    nlinarith


abbrev sideMarginal (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) :
    {e // G.left e ∈ S ∨ G.right e ∈ S} → ℝ := fun e => x e.val

def sideRestriction (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) :
    ({e // 0<x e} → ℝ) →ₗ[ℝ] ({e // 0<G.sideMarginal x S e} → ℝ) where
  toFun := fun u e => u ⟨e.val.val,e.property⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
 theorem positiveExtension_side (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V)
    (u : {e // 0<x e} → ℝ) (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    positiveExtension (G.sideMarginal x S) (G.sideRestriction x S u) e =
      positiveExtension x u e.val := by
  rfl

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
 theorem sideMarginal_line (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V)
    (u : {e // 0<x e} → ℝ) (t : ℝ) :
    G.sideMarginal (x+t • positiveExtension x u) S = G.sideMarginal x S +
      t • positiveExtension (G.sideMarginal x S) (G.sideRestriction x S u) := by
  rfl

/-- Pullbacks of both contraction face spaces preserve every original active cut,
including cuts crossing the chosen tight cut. This is the substantive coupling step. -/
theorem faceSpace_of_side_spaces (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.constraintPolytope)
    (S : Finset V) (hS : Odd S.card) (ht : G.cutMass x S=1)
    {u : {e // 0<x e} → ℝ}
    (h1 : G.sideRestriction x S u ∈ (G.onSide S).faceSpace (G.sideMarginal x S))
    (h2 : G.sideRestriction x Sᶜ u ∈ (G.onSide Sᶜ).faceSpace (G.sideMarginal x Sᶜ)) :
    u ∈ G.faceSpace x := by
  have hc := odd_compl_of_even heven hS
  have htc : G.cutMass x Sᶜ=1 := by simpa only [cutMass,cut_compl] using ht
  have hx1 := G.restriction_mem_constraints hx S hS ht
  have hx2 := G.restriction_mem_constraints hx Sᶜ hc htc
  have hv1 : Even (Fintype.card (Option {v // v ∈ S})) := by
    simpa only [Fintype.card_option,Fintype.card_coe] using hS.add_odd odd_one
  have hv2 : Even (Fintype.card (Option {v // v ∈ Sᶜ})) := by
    simpa only [Fintype.card_option,Fintype.card_coe] using hc.add_odd odd_one
  apply G.faceSpace_of_eventually_line hx
  filter_upwards [(G.onSide S).faceSpace_eventually_line hx1 h1,
    (G.onSide Sᶜ).faceSpace_eventually_line hx2 h2] with t ht1 ht2
  rw [← G.sideMarginal_line x S u t] at ht1
  rw [← G.sideMarginal_line x Sᶜ u t] at ht2
  have hp1 : G.sideMarginal (x+t • positiveExtension x u) S ∈ (G.onSide S).polytope := by
    rwa [(G.onSide S).polytope_eq_constraints hv1]
  have hp2 : G.sideMarginal (x+t • positiveExtension x u) Sᶜ ∈ (G.onSide Sᶜ).polytope := by
    rwa [(G.onSide Sᶜ).polytope_eq_constraints hv2]
  obtain ⟨p,hp,hpx⟩ := ((G.onSide S).mem_polytope_iff _).mp hp1
  obtain ⟨q,hq,hqx⟩ := ((G.onSide Sᶜ).mem_polytope_iff _).mp hp2
  have hp := (G.mem_polytope_iff _).mpr (G.couple_laws S _ hp hq (congrFun hpx) (congrFun hqx))
  exact G.polytope_subset_constraintPolytope hp

 theorem faceCodimension_le_sides (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.constraintPolytope)
    (S : Finset V) (hS : Odd S.card) (ht : G.cutMass x S=1) :
    G.faceCodimension x ≤ (G.onSide S).faceCodimension (G.sideMarginal x S) +
      (G.onSide Sᶜ).faceCodimension (G.sideMarginal x Sᶜ) := by
  classical
  exact quotient_finrank_le_pair (G.faceSpace x) ((G.onSide S).faceSpace (G.sideMarginal x S))
    ((G.onSide Sᶜ).faceSpace (G.sideMarginal x Sᶜ))
    (G.sideRestriction x S) (G.sideRestriction x Sᶜ)
    (fun _ => G.faceSpace_of_side_spaces heven hx S hS ht)

/-- Strong face-codimension induction for even orders at least four. -/
theorem faceCodimension_strong_aux (n : ℕ) :
    ∀ {W F : Type*} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (G : LooplessGraph W F), Fintype.card W=n → Even n → 4≤n →
      ∀ x ∈ G.constraintPolytope, G.faceCodimension x ≤ 2*(n-2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W F _ _ _ _ G hcard heven hfour x hx
    have heven' : Even (Fintype.card W) := hcard ▸ heven
    by_cases hcut : ∃ S : Finset W, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1
    · obtain ⟨S,hS,hlo,hhi,ht⟩ := hcut
      have hc := odd_compl_of_even heven' hS
      have hlt1 : Fintype.card (Option {v // v ∈ S}) < n := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hco := Finset.card_compl S
        omega
      have hlt2 : Fintype.card (Option {v // v ∈ Sᶜ}) < n := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hco := Finset.card_compl S
        have hle := Finset.card_le_univ S
        omega
      have hv1 : Even (Fintype.card (Option {v // v ∈ S})) := by
        simpa only [Fintype.card_option,Fintype.card_coe] using hS.add_odd odd_one
      have hv2 : Even (Fintype.card (Option {v // v ∈ Sᶜ})) := by
        simpa only [Fintype.card_option,Fintype.card_coe] using hc.add_odd odd_one
      have hn1 : 4≤Fintype.card (Option {v // v ∈ S}) := by
        simp only [Fintype.card_option,Fintype.card_coe]; omega
      have hn2 : 4≤Fintype.card (Option {v // v ∈ Sᶜ}) := by
        simp only [Fintype.card_option,Fintype.card_coe]; omega
      have hx1 := G.restriction_mem_constraints hx S hS ht
      have htc : G.cutMass x Sᶜ=1 := by simpa only [cutMass,cut_compl] using ht
      have hx2 := G.restriction_mem_constraints hx Sᶜ hc htc
      have hb1 := ih _ hlt1 (G.onSide S) rfl hv1 hn1 _ hx1
      have hb2 := ih _ hlt2 (G.onSide Sᶜ) rfl hv2 hn2 _ hx2
      have hb := G.faceCodimension_le_sides heven' hx S hS ht
      have hsum : Fintype.card (Option {v // v ∈ S}) + Fintype.card (Option {v // v ∈ Sᶜ})=n+2 := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hh := Finset.card_compl_add_card S
        omega
      change (G.onSide S).faceCodimension (G.sideMarginal x S) ≤ _ at hb1
      change (G.onSide Sᶜ).faceCodimension (G.sideMarginal x Sᶜ) ≤ _ at hb2
      omega
    · have hb := G.faceCodimension_no_tight heven' hcut
      omega

/-- The precise coarse face-codimension estimate used by the entropy argument. -/
theorem faceCodimension_bound (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.polytope) :
    G.faceCodimension x ≤ 2*Fintype.card V := by
  by_cases hn : 4≤Fintype.card V
  · have hb := faceCodimension_strong_aux (Fintype.card V) G rfl heven hn x
      (G.polytope_subset_constraintPolytope hx)
    omega
  · have hnt : ¬ ∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1 := by
      rintro ⟨S,_,hlo,hhi,_⟩
      have hh := Finset.card_compl_add_card S
      omega
    have hb := G.faceCodimension_no_tight heven hnt
    omega


omit [Fintype V] [DecidableEq E] in
 theorem degree_add_smul (G : LooplessGraph V E) (x u : E → ℝ) (t : ℝ) (v : V) :
    G.degree (x+t • u) v=G.degree x v+t*G.degree u v := by
  simpa using G.degree_linear x u 1 t v

omit [Fintype V] [DecidableEq E] in
 theorem cutMass_add_smul (G : LooplessGraph V E) (x u : E → ℝ) (t : ℝ) (S : Finset V) :
    G.cutMass (x+t • u) S=G.cutMass x S+t*G.cutMass u S := by
  simpa using G.cutMass_linear x u 1 t S

omit [DecidableEq E] in
/-- Radial extension for this actual matching polytope. This is needed to prove
lower semicontinuity of the maximum entropy without assuming its regularity. -/
theorem constraint_eventually_expand (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {t : ℝ} (ht : 0<t) :
    ∀ᶠ y in 𝓝[G.constraintPolytope] x, x+t⁻¹ • (y-x) ∈ G.constraintPolytope := by
  have hn : ∀ᶠ y in 𝓝[G.constraintPolytope] x, ∀ e, 0≤(x+t⁻¹ • (y-x)) e := by
    apply Filter.eventually_all.mpr
    intro e
    by_cases he : x e=0
    · filter_upwards [eventually_mem_nhdsWithin] with y hy
      simpa [he] using mul_nonneg (inv_nonneg.mpr ht.le) (hy.1 e)
    · have hp : 0<x e := lt_of_le_of_ne (hx.1 e) (Ne.symm he)
      have hc : Continuous (fun y : E → ℝ => (x+t⁻¹ • (y-x)) e) := by fun_prop
      have hh : ∀ᶠ y : E → ℝ in 𝓝 x, 0<(x+t⁻¹ • (y-x)) e :=
        (isOpen_lt continuous_const hc).mem_nhds (by simpa using hp)
      exact (hh.filter_mono nhdsWithin_le_nhds).mono fun y hy => hy.le
  have hodd : ∀ᶠ y in 𝓝[G.constraintPolytope] x,
      ∀ S : Finset V, Odd S.card → 1≤G.cutMass (x+t⁻¹ • (y-x)) S := by
    apply Filter.eventually_all.mpr
    intro S
    by_cases hS : Odd S.card
    · by_cases hs : G.cutMass x S=1
      · filter_upwards [eventually_mem_nhdsWithin] with y hy _
        rw [cutMass_add_smul,cutMass_sub,hs]
        have hh := mul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr (hy.2.2 S hS))
        linarith
      · have hp : 1<G.cutMass x S := lt_of_le_of_ne (hx.2.2 S hS) (Ne.symm hs)
        have hc : Continuous (fun y : E → ℝ => G.cutMass (x+t⁻¹ • (y-x)) S) :=
          (G.continuous_cutMass S).comp (by fun_prop)
        have hh : ∀ᶠ y : E → ℝ in 𝓝 x, 1<G.cutMass (x+t⁻¹ • (y-x)) S :=
          (isOpen_lt continuous_const hc).mem_nhds (by simpa using hp)
        exact (hh.filter_mono nhdsWithin_le_nhds).mono fun y hy _ => hy.le
    · exact Filter.Eventually.of_forall fun _ h => (hS h).elim
  filter_upwards [hn,hodd,eventually_mem_nhdsWithin] with y hn hodd hy
  refine ⟨hn,?_,hodd⟩
  intro v
  rw [degree_add_smul,degree_sub,hx.2.1,hy.2.1]
  ring

 theorem polytope_eventually_expand (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.polytope) {t : ℝ} (ht : 0<t) :
    ∀ᶠ y in 𝓝[G.polytope] x, x+t⁻¹ • (y-x) ∈ G.polytope := by
  rw [G.polytope_eq_constraints heven] at hx ⊢
  exact G.constraint_eventually_expand hx ht

end LooplessGraph

end MatchingEntropy

end

end OAI
end
end

section
section
namespace OAI

/-!
Boundary lower semicontinuity of maximum entropy and attainment of the entropy defect.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
/-- Concavity of H follows from mixing genuine optimizing probability laws. -/
theorem maxMatchingEntropy_mix_ge (G : LooplessGraph V E) {x y : E → ℝ}
    (hx : x ∈ G.polytope) (hy : y ∈ G.polytope) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t)*maxMatchingEntropy G x+t*maxMatchingEntropy G y ≤
      maxMatchingEntropy G ((1-t) • x+t • y) := by
  obtain ⟨p,hp,hpe⟩ := maxMatchingEntropy_attained G hx
  obtain ⟨q,hq,hqe⟩ := maxMatchingEntropy_attained G hy
  rw [← hpe,← hqe]
  apply (entropy_mix_ge hp.1.1 hq.1.1 ht).trans
  apply entropy_le_maxMatchingEntropy
  refine ⟨convex_probabilitySimplex _ hp.1 hq.1 (sub_nonneg.mpr ht.2) ht.1 (by ring),?_⟩
  change G.meanLinear ((1-t) • p+t • q) = _
  rw [map_add,map_smul,map_smul]
  change (1-t) • G.mean p+t • G.mean q = _
  rw [hp.2,hq.2]

/-- Boundary lower semicontinuity, using the finite matching-polytope constraints.
A fixed small mixing coefficient suffices for each prescribed entropy tolerance. -/
theorem maxMatchingEntropy_lowerSemicontinuousOn (G : LooplessGraph V E)
    (heven : Even (Fintype.card V)) :
    LowerSemicontinuousOn (maxMatchingEntropy G) G.polytope := by
  intro x hx r hr
  have hn := maxMatchingEntropy_nonneg G hx
  have hden : 0 < maxMatchingEntropy G x+1 := by linarith
  have ha : 0 < min (1:ℝ) ((maxMatchingEntropy G x-r)/(maxMatchingEntropy G x+1)) :=
    lt_min (by norm_num) (div_pos (sub_pos.mpr hr) hden)
  obtain ⟨t,ht0,htt⟩ := exists_between ha
  have ht1 : t<1 := htt.trans_le (min_le_left _ _)
  have htb : t*(maxMatchingEntropy G x+1) < maxMatchingEntropy G x-r :=
    (lt_div_iff₀ hden).mp (htt.trans_le (min_le_right _ _))
  filter_upwards [G.polytope_eventually_expand heven hx ht0] with y hy
  have hh := maxMatchingEntropy_mix_ge G hx hy ⟨ht0.le,ht1.le⟩
  have he : (1-t) • x+t • (x+t⁻¹ • (y-x))=y := by
    ext e
    simp only [Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
    field_simp
    ring
  rw [he] at hh
  have hz := mul_nonneg ht0.le (maxMatchingEntropy_nonneg G hy)
  nlinarith

/-- The actual entropy defect attains a maximum on the closed matching polytope. -/
theorem entropyDefect_attains_max (G : LooplessGraph V E)
    (heven : Even (Fintype.card V)) (hPM : Nonempty G.Matching) (m : ℝ) :
    ∃ x ∈ G.polytope, ∀ y ∈ G.polytope, entropyDefect G m y ≤ entropyDefect G m x := by
  have hc : Continuous (fun y : E → ℝ => entropyBarrier m (entropy y)) := by
    have hb : Continuous (entropyBarrier m) := by unfold entropyBarrier; fun_prop
    exact hb.comp continuous_entropy
  have hs : UpperSemicontinuousOn (entropyDefect G m) G.polytope := by
    change UpperSemicontinuousOn (fun y => entropyBarrier m (entropy y)-maxMatchingEntropy G y) G.polytope
    simpa only [sub_eq_add_neg, Pi.neg_apply] using
      hc.continuousOn.upperSemicontinuousOn.add
        (maxMatchingEntropy_lowerSemicontinuousOn G heven).neg
  have hn : G.polytope.Nonempty := by
    obtain ⟨M⟩ := hPM
    exact ⟨G.indicator M,subset_convexHull ℝ _ (Set.mem_range_self M)⟩
  exact UpperSemicontinuousOn.exists_isMaxOn hn G.compact_polytope hs

end MatchingEntropy

end

end OAI
end
end

section
section
namespace OAI

/-!
Positive semidefinite covariance matrices, rank, trace, and a spectral inequality.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

def weightedColumns (p : A → ℝ) (b : A → I → ℝ) : Matrix I A ℝ :=
  fun i a => Real.sqrt (p a) * b a i

def covariance (p : A → ℝ) (b : A → I → ℝ) : Matrix I I ℝ :=
  weightedColumns p b * (weightedColumns p b)ᵀ

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_posSemidef (p : A → ℝ) (b : A → I → ℝ) :
    (covariance p b).PosSemidef := by
  simpa only [covariance, conjTranspose_eq_transpose_of_trivial] using
    posSemidef_self_mul_conjTranspose (weightedColumns p b)

omit [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem covariance_entry {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ) (i j : I) :
    covariance p b i j = ∑ a, p a*b a i*b a j := by
  unfold covariance
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp only [weightedColumns, Matrix.transpose_apply]
  calc
    _ = (Real.sqrt (p a))^2 * b a i * b a j := by ring
    _ = _ := by rw [Real.sq_sqrt (hp a)]

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_mulVec {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ)
    (u : I → ℝ) (i : I) :
    (covariance p b *ᵥ u) i = ∑ a, p a*b a i*(b a ⬝ᵥ u) := by
  simp only [Matrix.mulVec, dotProduct, covariance_entry hp, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_quadratic {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ)
    (u : I → ℝ) : u ⬝ᵥ (covariance p b *ᵥ u) = ∑ a, p a*(b a ⬝ᵥ u)^2 := by
  rw [dotProduct]
  simp_rw [covariance_mulVec hp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ i, u i*(p a*b a i*(b a ⬝ᵥ u))) =
      (∑ i, b a i*u i)*(p a*(b a ⬝ᵥ u)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = p a*(b a ⬝ᵥ u)^2 := by rw [← dotProduct]; ring

def weightedDirectionSpace (p : A → ℝ) (b : A → I → ℝ) : Submodule ℝ (I → ℝ) :=
  Submodule.span ℝ (Set.range fun a : {a // 0 < p a} => b a.val)

omit [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem weightedColumns_span {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ) :
    Submodule.span ℝ (Set.range (weightedColumns p b).col) = weightedDirectionSpace p b := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    by_cases ha : 0 < p a
    · have hb : b a ∈ weightedDirectionSpace p b := Submodule.subset_span ⟨⟨a,ha⟩,rfl⟩
      exact Submodule.smul_mem _ (Real.sqrt (p a)) hb
    · have hz := le_antisymm (le_of_not_gt ha) (hp a)
      have he : (weightedColumns p b).col a = 0 := by
        ext i
        simp [weightedColumns, Matrix.col, hz]
      rw [he]
      exact (weightedDirectionSpace p b).zero_mem
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    have hb : (weightedColumns p b).col a.val ∈
        Submodule.span ℝ (Set.range (weightedColumns p b).col) := Submodule.subset_span ⟨a.val,rfl⟩
    have hs : Real.sqrt (p a.val) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 a.property)
    have hh := Submodule.smul_mem _ (Real.sqrt (p a.val))⁻¹ hb
    have he : (Real.sqrt (p a.val))⁻¹ • (weightedColumns p b).col a.val = b a.val := by
      ext i
      change (Real.sqrt (p a.val))⁻¹ * (Real.sqrt (p a.val) * b a.val i) = _
      rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
    rw [he] at hh
    exact hh

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_rank {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ) :
    (covariance p b).rank = Module.finrank ℝ (weightedDirectionSpace p b) := by
  rw [covariance, rank_self_mul_transpose, rank_eq_finrank_span_cols, weightedColumns_span hp]

def normalizedCentered (v : A → I → ℝ) (x : I → ℝ) (a : A) (i : I) : ℝ :=
  (v a i-x i)/Real.sqrt (x i)

omit [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem normalizedCentered_mean {p : A → ℝ} (hp : ∑ a, p a = 1)
    (v : A → I → ℝ) (x : I → ℝ) (hx : ∀ i, ∑ a, p a*v a i = x i) (i : I) :
    ∑ a, p a*normalizedCentered v x a i = 0 := by
  simp only [normalizedCentered, ← mul_div_assoc, mul_sub, ← Finset.sum_div,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul, hx, sub_self, zero_div]

omit [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem normalizedCentered_variance {p : A → ℝ} (hp : ∑ a, p a = 1)
    (v : A → I → ℝ) (hv : ∀ a i, (v a i)^2=v a i) (x : I → ℝ)
    (hx : ∀ i, ∑ a, p a*v a i = x i) (hxp : ∀ i, 0 < x i) (i : I) :
    ∑ a, p a*(normalizedCentered v x a i)^2 = 1-x i := by
  have heq : ∀ a, p a*(normalizedCentered v x a i)^2 =
      (p a*v a i-2*x i*(p a*v a i)+(x i)^2*p a)/x i := by
    intro a
    rw [normalizedCentered, div_pow, Real.sq_sqrt (hxp i).le, ← mul_div_assoc]
    congr 1
    calc
      _ = p a*(v a i)^2-2*x i*(p a*v a i)+(x i)^2*p a := by ring
      _ = _ := by rw [hv]
  simp_rw [heq]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hx, hp, mul_one]
  field_simp [ne_of_gt (hxp i)]
  ring

omit [DecidableEq A] [DecidableEq I] in
theorem normalized_covariance_trace {p : A → ℝ} (hp : p ∈ probabilitySimplex A)
    (v : A → I → ℝ) (hv : ∀ a i, (v a i)^2=v a i) (x : I → ℝ)
    (hx : ∀ i, ∑ a, p a*v a i = x i) (hxp : ∀ i, 0 < x i) :
    (covariance p (normalizedCentered v x)).trace = Fintype.card I - ∑ i, x i := by
  unfold Matrix.trace Matrix.diag
  simp_rw [covariance_entry hp.1]
  have heq : ∀ i, (∑ a, p a*normalizedCentered v x a i*normalizedCentered v x a i) = 1-x i := by
    intro i
    simpa only [pow_two, mul_assoc] using
      normalizedCentered_variance hp.2 v hv x hx hxp i
  simp_rw [heq]
  simp

/-- Spectral form of the second-variation step, using the full (possibly
singular) covariance rather than introducing an inverse on its image. -/
theorem covariance_rank_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {a : ℝ}
    (hsecond : ∀ u : ι → ℝ,
      (a - 1) * ((C *ᵥ u) ⬝ᵥ (C *ᵥ u)) + u ⬝ᵥ (C *ᵥ u) ≤ 0) :
    (C.rank : ℝ) ≤ (1-a) * C.trace := by
  let eig := hC.isHermitian.eigenvalues
  have heig : ∀ i, 0 ≤ eig i := hC.eigenvalues_nonneg
  have hone : ∀ i, eig i ≠ 0 → 1 ≤ (1-a) * eig i := by
    intro i hi
    let v : ι → ℝ := hC.isHermitian.eigenvectorBasis i
    have hv : v ⬝ᵥ v = 1 := by
      have hn := hC.isHermitian.eigenvectorBasis.orthonormal.1 i
      have hi : inner ℝ (hC.isHermitian.eigenvectorBasis i)
          (hC.isHermitian.eigenvectorBasis i) = 1 := by
        rw [real_inner_self_eq_norm_sq, hn]
        norm_num
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hi
    have he : C *ᵥ v = eig i • v := hC.isHermitian.mulVec_eigenvectorBasis i
    have hs := hsecond v
    rw [he] at hs
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, hv, mul_one] at hs
    have hp : 0 < eig i := lt_of_le_of_ne (heig i) (Ne.symm hi)
    nlinarith
  rw [hC.isHermitian.rank_eq_card_non_zero_eigs,
    hC.isHermitian.trace_eq_sum_eigenvalues]
  change (Fintype.card {i // eig i ≠ 0} : ℝ) ≤ (1-a) * ∑ i, eig i
  rw [Finset.mul_sum]
  calc
    _ = ∑ i : {i // eig i ≠ 0}, (1 : ℝ) := by simp
    _ ≤ ∑ i : {i // eig i ≠ 0}, (1-a) * eig i := Finset.sum_le_sum fun i _ => hone i i.property
    _ = ∑ i, (1-a) * eig i := by
      have hz : (∑ i : {i // ¬ eig i ≠ 0}, (1-a) * eig i) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [not_ne_iff.mp i.property, mul_zero]
      simpa only [hz, add_zero] using
        (Fintype.sum_subtype_add_sum_subtype (fun i => eig i ≠ 0)
          (fun i => (1-a) * eig i))

/-- The numerical contradiction following covariance rank and trace. -/
theorem covariance_contradiction {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {a m s : ℝ}
    (hm : 0 < m) (hs : 8*m < s) (hrank : s-4*m ≤ C.rank)
    (htrace : C.trace = s-m) (ha : 8*m/s ≤ a)
    (hsecond : ∀ u : ι → ℝ,
      (a-1) * ((C *ᵥ u) ⬝ᵥ (C *ᵥ u)) + u ⬝ᵥ (C *ᵥ u) ≤ 0) : False := by
  have hb := covariance_rank_bound hC hsecond
  rw [htrace] at hb
  have hsp : 0 < s := by linarith
  have hsmp : 0 < s-m := by linarith
  have hau : a ≤ 3*m/(s-m) := by
    apply (le_div_iff₀ hsmp).mpr
    nlinarith
  have hcross := (div_le_div_iff₀ hsp hsmp).mp (ha.trans hau)
  nlinarith [mul_pos hm (show 0 < 5*s-8*m by linarith)]

end MatchingEntropy

end

end OAI
end
end

section
section
namespace OAI

/-!
Normalized matching covariance: face rank, exact trace, and second variation.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Normalized matching directions on exactly the positive edge support. -/
def matchingNormalized (G : LooplessGraph V E) (x : E → ℝ) :
    G.Matching → {e // 0 < x e} → ℝ :=
  normalizedCentered (fun M e => G.indicator M e.val) (fun e => x e.val)

omit [Fintype V] [DecidableEq V] in
theorem matchingNormalized_average (G : LooplessGraph V E) {x y : E → ℝ}
    {q : G.Matching → ℝ} (hq : q ∈ G.feasibleLaws y) (e : {e // 0 < x e}) :
    (∑ M, q M*matchingNormalized G x M e)=(y e.val-x e.val)/Real.sqrt (x e.val) := by
  simp only [matchingNormalized,normalizedCentered,← mul_div_assoc,mul_sub,
    ← Finset.sum_div,Finset.sum_sub_distrib,← Finset.sum_mul,hq.1.2,one_mul]
  rw [show (∑ M, q M*G.indicator M e.val)=y e.val from congrFun hq.2 e.val]

omit [Fintype V] [DecidableEq V] in
/-- A feasible two-sided direction has a positive-side law supported on the
entropy optimizer at its midpoint. -/
theorem midpoint_law_support (G : LooplessGraph V E) {x v : E → ℝ} {a : ℝ}
    {p q r : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hq : q ∈ G.feasibleLaws (x+a • v))
    (hr : r ∈ G.feasibleLaws (x+(-a) • v)) :
    ∀ M, 0 < q M → 0 < p M := by
  let w : G.Matching → ℝ := (1/2:ℝ) • q+(1/2:ℝ) • r
  have hw : w ∈ G.feasibleLaws x := by
    refine ⟨convex_probabilitySimplex _ hq.1 hr.1 (by norm_num) (by norm_num) (by norm_num),?_⟩
    change G.meanLinear ((1/2:ℝ) • q+(1/2:ℝ) • r) = _
    rw [map_add,map_smul,map_smul]
    change (1/2:ℝ) • G.mean q+(1/2:ℝ) • G.mean r = _
    rw [hq.2,hr.2]
    ext e
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  intro M hM
  apply matching_optimizer_support G hp hw hopt
  change 0 < (1/2:ℝ)*q M+(1/2:ℝ)*r M
  have hh := hr.1.1 M
  linarith

/-- Every active-face direction belongs to the optimizer's normalized covariance
span. No face support or dimension assertion is being supplied as a hypothesis. -/
theorem normalized_face_mem (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws x) (hopt : entropy p=maxMatchingEntropy G x)
    {u : {e // 0 < x e} → ℝ} (hu : u ∈ G.faceSpace x) :
    (fun e => u e/Real.sqrt (x e.val)) ∈ weightedDirectionSpace p (matchingNormalized G x) := by
  have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p,hp⟩
  have hev := G.faceSpace_eventually_line (G.polytope_subset_constraintPolytope hx) hu
  have hneg : ∀ᶠ t : ℝ in 𝓝 0, x+(-t) • LooplessGraph.positiveExtension x u ∈ G.constraintPolytope := by
    have hc : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by simpa using continuous_neg.tendsto (0:ℝ)
    exact hc.eventually hev
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (x+t • LooplessGraph.positiveExtension x u ∈ G.constraintPolytope ∧
      x+(-t) • LooplessGraph.positiveExtension x u ∈ G.constraintPolytope) ∧ 0 < t :=
    ((hev.and hneg).filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  obtain ⟨a,⟨ha,hna⟩,ha0⟩ := hh.exists
  rw [← G.polytope_eq_constraints heven] at ha hna
  obtain ⟨q,hq⟩ := (G.mem_polytope_iff _).mp ha
  obtain ⟨r,hr⟩ := (G.mem_polytope_iff _).mp hna
  have hsupp := midpoint_law_support G hp hopt hq hr
  have hsum : (∑ M, q M • matchingNormalized G x M) ∈
      weightedDirectionSpace p (matchingNormalized G x) := by
    apply Submodule.sum_mem
    intro M _
    by_cases hM : 0 < p M
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨M,hM⟩,rfl⟩)
    · have hq0 : q M=0 := le_antisymm (le_of_not_gt fun hqM => hM (hsupp M hqM)) (hq.1.1 M)
      simp only [hq0,zero_smul]
      exact Submodule.zero_mem _
  have hin := Submodule.smul_mem _ a⁻¹ hsum
  have he : a⁻¹ • (∑ M, q M • matchingNormalized G x M) =
      (fun e => u e/Real.sqrt (x e.val)) := by
    ext e
    simp only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
    rw [matchingNormalized_average G hq]
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,LooplessGraph.positiveExtension_pos]
    field_simp
    ring
  rwa [he] at hin

def normalizeLinear (x : E → ℝ) :
    ({e // 0 < x e} → ℝ) →ₗ[ℝ] ({e // 0 < x e} → ℝ) where
  toFun := fun u e => u e/Real.sqrt (x e.val)
  map_add' := by intro u v; ext e; exact add_div _ _ _
  map_smul' := by intro a u; ext e; exact mul_div_assoc _ _ _

/-- Face codimension gives a lower bound for the rank of the genuine covariance. -/
theorem matching_covariance_rank (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws x) (hopt : entropy p=maxMatchingEntropy G x) :
    Fintype.card {e // 0 < x e} ≤ 2*Fintype.card V+
      (covariance p (matchingNormalized G x)).rank := by
  let W := weightedDirectionSpace p (matchingNormalized G x)
  let L : G.faceSpace x →ₗ[ℝ] W :=
    ((normalizeLinear x).comp (G.faceSpace x).subtype).codRestrict W
      (fun u => normalized_face_mem G heven hp hopt u.property)
  have hi : Function.Injective L := by
    intro u v huv
    apply Subtype.ext
    funext e
    have hh := congrFun (congrArg Subtype.val huv) e
    change u.val e/Real.sqrt (x e.val)=v.val e/Real.sqrt (x e.val) at hh
    exact (div_left_inj' (ne_of_gt (Real.sqrt_pos.mpr e.property))).mp hh
  have hdim := LinearMap.finrank_le_finrank_of_injective hi
  have hq := (G.faceSpace x).finrank_quotient_add_finrank
  have hc := G.faceCodimension_bound heven ((G.mem_polytope_iff x).mpr ⟨p,hp⟩)
  rw [covariance_rank hp.1.1]
  have hq' : G.faceCodimension x+Module.finrank ℝ (G.faceSpace x)=Fintype.card {e // 0 < x e} := by
    simpa only [LooplessGraph.faceCodimension,Module.finrank_pi,Module.finrank_self,Finset.sum_const,
      Finset.card_univ,smul_eq_mul,mul_one] using hq
  change Module.finrank ℝ (G.faceSpace x) ≤ Module.finrank ℝ W at hdim
  dsimp only [W] at hdim
  omega


omit [DecidableEq E] in
theorem sum_positive_support (x f : E → ℝ) (hf : ∀ e, ¬ 0 < x e → f e=0) :
    (∑ e, f e) = ∑ e : {e // 0 < x e}, f e.val := by
  classical
  have hz : (∑ e : {e // ¬ 0 < x e}, f e.val)=0 :=
    Finset.sum_eq_zero fun e _ => hf e.val e.property
  have hh := Fintype.sum_subtype_add_sum_subtype (fun e => 0 < x e) f
  rw [hz,add_zero] at hh
  exact hh.symm

def matchingScoreWeights (x : E → ℝ) (u : {e // 0 < x e} → ℝ) : E → ℝ :=
  LooplessGraph.positiveExtension x (fun e => u e/Real.sqrt (x e.val))

omit [Fintype V] [DecidableEq V] in
theorem matchingNormalized_score (G : LooplessGraph V E) (x : E → ℝ)
    (u : {e // 0 < x e} → ℝ) (M : G.Matching) :
    linearScore G (matchingScoreWeights x u) (∑ e, matchingScoreWeights x u e*x e) M =
      matchingNormalized G x M ⬝ᵥ u := by
  classical
  unfold linearScore
  rw [← Finset.sum_sub_distrib]
  rw [sum_positive_support x _ (fun e he => by simp [matchingScoreWeights,LooplessGraph.positiveExtension,he])]
  rw [dotProduct]
  apply Finset.sum_congr rfl
  intro e _
  simp only [matchingScoreWeights,LooplessGraph.positiveExtension_pos,matchingNormalized,normalizedCentered]
  ring

omit [Fintype V] [DecidableEq V] in
theorem matchingNormalized_mulVec (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (u : {e // 0 < x e} → ℝ) (e : {e // 0 < x e}) :
    (covariance p (matchingNormalized G x) *ᵥ u) e =
      G.mean (fun M => p M * linearScore G (matchingScoreWeights x u)
        (∑ e, matchingScoreWeights x u e*x e) M) e.val / Real.sqrt (x e.val) := by
  let a := linearScore G (matchingScoreWeights x u) (∑ e, matchingScoreWeights x u e*x e)
  have hcenter : ∑ M, p M*a M=0 := by
    dsimp only [a]
    rw [linearScore_expectation,hp.2,hp.1.2,mul_one,sub_self]
  calc
    _ = ∑ M, (p M*a M*G.indicator M e.val-x e.val*(p M*a M))/Real.sqrt (x e.val) := by
      rw [covariance_mulVec hp.1.1]
      apply Finset.sum_congr rfl
      intro M _
      rw [← matchingNormalized_score G x u M]
      change p M*((G.indicator M e.val-x e.val)/Real.sqrt (x e.val))*a M = _
      ring
    _ = _ := by
      rw [← Finset.sum_div,Finset.sum_sub_distrib,← Finset.mul_sum,hcenter,mul_zero,sub_zero]
      rfl

/-- The normalized covariance has the exact trace s-m. -/
theorem matching_covariance_trace (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) {m : ℕ}
    (hV : Fintype.card V=2*m) :
    (covariance p (matchingNormalized G x)).trace = Fintype.card {e // 0 < x e}-(m:ℝ) := by
  have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p,hp⟩
  have hsum : (∑ e : {e // 0 < x e}, x e.val)=(m:ℝ) := by
    rw [← G.marginal_sum hV hx]
    exact (sum_positive_support x x (fun e he => le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1)).symm
  unfold matchingNormalized
  rw [normalized_covariance_trace hp.1 _ ?_ _ ?_ (fun e => e.property),hsum]
  · intro M e
    simp only [LooplessGraph.indicator]
    split <;> norm_num
  · intro e
    exact congrFun hp.2 e.val

omit [Fintype V] [DecidableEq V] in
/-- Convert the genuine second variation into the covariance spectral inequality. -/
theorem matching_covariance_second_variation (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x) {m : ℝ} (hm : 0 < m)
    (hmax : ∀ y ∈ G.polytope, entropyDefect G m y ≤ entropyDefect G m x)
    (u : {e // 0 < x e} → ℝ) :
    (8*Real.exp (-entropy x/m)-1)*
        ((covariance p (matchingNormalized G x) *ᵥ u) ⬝ᵥ
          (covariance p (matchingNormalized G x) *ᵥ u)) +
      u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) ≤ 0 := by
  let w := matchingScoreWeights x u
  let c := ∑ e, w e*x e
  let a := linearScore G w c
  have hcenter : ∑ M, p M*a M=0 := by
    dsimp only [a,c]
    rw [linearScore_expectation,hp.2,hp.1.2,mul_one,sub_self]
  have hh := matching_defect_second_variation G hp hopt hm.ne' hmax w c hcenter
  have hnorm : (∑ e, (G.mean (fun M => p M*a M) e)^2/x e) =
      (covariance p (matchingNormalized G x) *ᵥ u) ⬝ᵥ
        (covariance p (matchingNormalized G x) *ᵥ u) := by
    have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p,hp⟩
    rw [sum_positive_support x _ (fun e he => by
      have hz : x e=0 := le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1
      simp [hz])]
    rw [dotProduct]
    apply Finset.sum_congr rfl
    intro e _
    rw [matchingNormalized_mulVec G hp,← sq,div_pow,Real.sq_sqrt e.property.le]
  have hquad : (∑ M, p M*(a M)^2) = u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) := by
    rw [covariance_quadratic hp.1.1]
    apply Finset.sum_congr rfl
    intro M _
    rw [← matchingNormalized_score G x u M]
  change (8*Real.exp (-entropy x/m)-1)*(∑ e, (G.mean (fun M => p M*a M) e)^2/x e)+
    (8*Real.exp (-entropy x/m)/m)*(entropyLineD x (G.mean (fun M => p M*a M)) 0)^2+
    (∑ M, p M*(a M)^2) ≤ 0 at hh
  rw [hnorm,hquad] at hh
  have hpterm : 0 ≤ (8*Real.exp (-entropy x/m)/m)*
      (entropyLineD x (G.mean (fun M => p M*a M)) 0)^2 := by positivity
  linarith

end MatchingEntropy

end

end OAI
end
end

section
section
namespace OAI

/-!
The nonlinear entropy defect bound
`F - H ≤ 8m (1 - exp (-F/m))` for finite loopless multigraphs on `2m` vertices,
and the perfect matching count bound `[k exp (-8 (1 - 1/k))]^m`,
with its coarse bound `(exp (-8) k)^m`, when the entire edge set
is partitioned into `k ≥ 1` perfect matchings.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The small-entropy regime of the nonlinear barrier function. -/
theorem entropy_barrier_ge_id {t : ℝ} (ht : 0 ≤ t) (h8 : t ≤ Real.log 8) :
    t ≤ 8 * (1-Real.exp (-t)) := by
  have he : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  have he8 : Real.exp t ≤ 8 := by
    have hh := Real.exp_le_exp.mpr h8
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 8)] at hh
    exact hh
  have hlog := Real.log_le_sub_one_of_pos (Real.exp_pos t)
  rw [Real.log_exp] at hlog
  have hin := Real.exp_neg t
  rw [hin]
  have hp := Real.exp_pos t
  apply (mul_le_mul_iff_right₀ hp).mp
  have hmain : t * Real.exp t ≤ 8 * (Real.exp t - 1) := by
    have : t ≤ Real.exp t - 1 := hlog
    nlinarith
  have hprod : Real.exp t * (8*(1-(Real.exp t)⁻¹)) = 8*(Real.exp t-1) := by
    field_simp [hp.ne']
  calc
    Real.exp t * t = t * Real.exp t := mul_comm _ _
    _ ≤ 8 * (Real.exp t-1) := hmain
    _ = _ := hprod.symm


/-- Entropy on s positive edge coordinates of total mass m is at most m log(s/m). -/
theorem marginal_entropy_support_bound (G : LooplessGraph V E) {m : ℕ}
    (hm : 0 < m) (hV : Fintype.card V=2*m) {x : E → ℝ} (hx : x ∈ G.polytope) :
    0 ≤ entropy x ∧ 0 < Fintype.card {e // 0 < x e} ∧
      entropy x ≤ (m:ℝ)*Real.log ((Fintype.card {e // 0 < x e}:ℝ)/(m:ℝ)) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hmass := G.marginal_sum hV hx
  have hn : ∀ e, 0 ≤ x e := fun e => (G.coordinate_mem_Icc hx e).1
  have hz : ∀ e, ¬ 0 < x e → x e=0 := fun e he => le_antisymm (le_of_not_gt he) (hn e)
  have hsum : (∑ e : {e // 0 < x e}, x e.val)=(m:ℝ) :=
    (sum_positive_support x x hz).symm.trans hmass
  have hent : entropy (fun e : {e // 0 < x e} => x e.val)=entropy x := by
    unfold entropy
    exact (sum_positive_support x (fun e => Real.negMulLog (x e))
      (fun e he => by rw [hz e he,Real.negMulLog_zero])).symm
  have hpossum : 0 < ∑ e, x e := by rw [hmass]; exact hmR
  obtain ⟨e,_,he⟩ := (Finset.sum_pos_iff_of_nonneg (fun e _ => hn e)).mp hpossum
  have hs : 0 < Fintype.card {e // 0 < x e} := Fintype.card_pos_iff.mpr ⟨⟨e,he⟩⟩
  have hsR : (0:ℝ) < Fintype.card {e // 0 < x e} := by exact_mod_cast hs
  refine ⟨Finset.sum_nonneg (fun e _ => Real.negMulLog_nonneg (hn e) (G.coordinate_mem_Icc hx e).2),hs,?_⟩
  let c : ℝ := (Fintype.card {e // 0 < x e}:ℝ)/(m:ℝ)
  have hc : 0 < c := div_pos hsR hmR
  have hcm : c*(m:ℝ)=Fintype.card {e // 0 < x e} := div_mul_cancel₀ _ hmR.ne'
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun e : {e // 0 < x e} => fun _ =>
    Real.negMulLog_le_one_sub_self (mul_nonneg hc.le e.property.le))
  simp_rw [Real.negMulLog_mul] at hb
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum,hsum,
    Finset.sum_sub_distrib,← Finset.mul_sum,hsum] at hb
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hb
  change (m:ℝ)*Real.negMulLog c+c*entropy (fun e : {e // 0 < x e} => x e.val) ≤
    (Fintype.card {e // 0 < x e}:ℝ)-c*(m:ℝ) at hb
  rw [hent,Real.negMulLog,hcm,sub_self] at hb
  change entropy x ≤ (m:ℝ)*Real.log c
  nlinarith

/-- Main entropy comparison, for every marginal in the actual matching polytope. -/
theorem entropy_main (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m)
    (hPM : Nonempty G.Matching) (y : E → ℝ) (hy : y ∈ G.polytope) :
    marginalEntropy y - maxMatchingEntropy G y ≤
      8 * (m : ℝ) * (1 - Real.exp (-marginalEntropy y / (m : ℝ))) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have heven : Even (Fintype.card V) := by rw [hV]; exact even_two_mul m
  obtain ⟨x,hx,hmax⟩ := entropyDefect_attains_max G heven hPM (m:ℝ)
  by_contra htarget
  have hypos : 0 < entropyDefect G (m:ℝ) y := by
    dsimp [entropyDefect,entropyBarrier,marginalEntropy] at *
    linarith
  have hpos : 0 < entropyDefect G (m:ℝ) x := hypos.trans_le (hmax y hy)
  obtain ⟨p,hp,hopt⟩ := maxMatchingEntropy_attained G hx
  obtain ⟨hxnon,hspos,hentropy⟩ := marginal_entropy_support_bound G hm hV hx
  have hH := maxMatchingEntropy_nonneg G hx
  let s : ℝ := Fintype.card {e // 0 < x e}
  have hsR : 0 < s := by dsimp only [s]; exact_mod_cast hspos
  have hrpos : 0 < s/(m:ℝ) := div_pos hsR hmR
  have hu : entropy x/(m:ℝ) ≤ Real.log (s/(m:ℝ)) := by
    apply (div_le_iff₀ hmR).mpr
    simpa only [mul_comm] using hentropy
  have hlo : Real.log 8 < entropy x/(m:ℝ) := by
    by_contra hle
    have hb := entropy_barrier_ge_id (div_nonneg hxnon hmR.le) (le_of_not_gt hle)
    have hb' := (div_le_iff₀ hmR).mp hb
    dsimp only [entropyDefect,entropyBarrier] at hpos
    rw [neg_div] at hpos
    nlinarith
  have hs8 : 8*(m:ℝ) < s := by
    have hh := (Real.log_lt_log_iff (by norm_num : (0:ℝ)<8) hrpos).mp (hlo.trans_le hu)
    exact (lt_div_iff₀ hmR).mp hh
  have ha : 8*(m:ℝ)/s ≤ 8*Real.exp (-entropy x/(m:ℝ)) := by
    have hh := Real.exp_le_exp.mpr (neg_le_neg hu)
    rw [Real.exp_neg,Real.exp_log hrpos,inv_div] at hh
    rw [neg_div,mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hh (by norm_num)
  have hrankNat := matching_covariance_rank G heven hp hopt
  rw [hV] at hrankNat
  have hrankR : s ≤ 2*(2*(m:ℝ))+(covariance p (matchingNormalized G x)).rank := by
    dsimp only [s]
    exact_mod_cast hrankNat
  have hrank : s-4*(m:ℝ) ≤ (covariance p (matchingNormalized G x)).rank := by linarith
  exact covariance_contradiction (covariance_posSemidef p (matchingNormalized G x)) hmR hs8
    hrank (matching_covariance_trace G hp hV) ha
    (matching_covariance_second_variation G hp hopt hmR hmax)


omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- An edge partition into k matchings places the exact uniform edge vector in P. -/
theorem uniform_decomposition_mem (G : LooplessGraph V E) {k : ℕ} (hk : 1 ≤ k)
    (M : Fin k → G.Matching)
    (hpartition : ∀ e : E, ∃! i : Fin k, e ∈ (M i).val) :
    (fun _ : E => 1/(k:ℝ)) ∈ G.polytope := by
  classical
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsum : (∑ i : Fin k, (1/(k:ℝ)))=1 := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  have hmean := (convex_convexHull ℝ (Set.range G.indicator)).sum_mem
    (fun (i : Fin k) _ => (one_div_pos.mpr hkR).le) hsum
    (fun i _ => subset_convexHull ℝ _ (Set.mem_range_self (M i)))
  have heq : (∑ i : Fin k, (1/(k:ℝ)) • G.indicator (M i)) = (fun _ : E => 1/(k:ℝ)) := by
    ext e
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [← Finset.mul_sum]
    have hi : (∑ i : Fin k, G.indicator (M i) e)=1 := by
      obtain ⟨i,hi,hu⟩ := hpartition e
      rw [Finset.sum_eq_single i]
      · simp [LooplessGraph.indicator,hi]
      · intro j _ hji
        have hj : e ∉ (M j).val := fun h => hji (hu j h)
        simp [LooplessGraph.indicator,hj]
      · simp
    rw [hi,mul_one]
  rwa [heq] at hmean

/-- The exact decomposable-graph count theorem, including its coarser bound. -/
theorem count_main (G : LooplessGraph V E) (m k : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (hk : 1 ≤ k)
    (M : Fin k → G.Matching)
    (hpartition : ∀ e : E, ∃! i : Fin k, e ∈ (M i).val) :
    ((k : ℝ) * Real.exp (-8 * (1 - 1 / (k : ℝ)))) ^ m ≤
        (Fintype.card G.Matching : ℝ) ∧
      (Real.exp (-8) * (k : ℝ)) ^ m ≤
        ((k : ℝ) * Real.exp (-8 * (1 - 1 / (k : ℝ)))) ^ m := by
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hPM : Nonempty G.Matching := ⟨M ⟨0,by omega⟩⟩
  let x : E → ℝ := fun _ => 1/(k:ℝ)
  have hx : x ∈ G.polytope := uniform_decomposition_mem G hk M hpartition
  have hh : marginalEntropy x=(m:ℝ)*Real.log (k:ℝ) := by
    have hlog : Real.negMulLog (1/(k:ℝ))=(1/(k:ℝ))*Real.log (k:ℝ) := by
      rw [one_div,Real.negMulLog,Real.log_inv]
      ring
    change (∑ e : E, Real.negMulLog (1/(k:ℝ)))=_
    simp_rw [hlog]
    rw [← Finset.sum_mul]
    exact congrArg (fun t : ℝ => t*Real.log (k:ℝ)) (G.marginal_sum hV hx)
  have hi := entropy_main G m hm hV hPM x hx
  have hH := maxMatchingEntropy_le_log_card G hx
  have hexp : Real.exp (-((m:ℝ)*Real.log (k:ℝ))/(m:ℝ))=1/(k:ℝ) := by
    have he : -((m:ℝ)*Real.log (k:ℝ))/(m:ℝ) = -Real.log (k:ℝ) := by
      field_simp
    rw [he,Real.exp_neg,Real.exp_log hkR]
    simp only [one_div]
  rw [hh,hexp] at hi
  have hlogbound : (m:ℝ)*(Real.log (k:ℝ)+(-8*(1-1/(k:ℝ)))) ≤
      Real.log (Fintype.card G.Matching:ℝ) := by nlinarith
  have hN : (0:ℝ) < Fintype.card G.Matching := by
    exact_mod_cast Fintype.card_pos_iff.mpr hPM
  constructor
  · have he := Real.exp_le_exp.mpr hlogbound
    rw [Real.exp_log hN,Real.exp_nat_mul,Real.exp_add,Real.exp_log hkR] at he
    exact he
  · apply pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le hkR.le)
    have he : Real.exp (-8) ≤ Real.exp (-8*(1-1/(k:ℝ))) := by
      apply Real.exp_le_exp.mpr
      have hq := (one_div_pos.mpr hkR).le
      nlinarith
    calc
      Real.exp (-8)*(k:ℝ) = (k:ℝ)*Real.exp (-8) := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left he hkR.le

end MatchingEntropy

end

end OAI
end
end

section
section
namespace OAI


section

noncomputable section
open scoped BigOperators Topology
open Filter
namespace MatchingEntropy

variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def binaryEntropy (x : E → ℝ) : ℝ := entropy x + entropy (fun e => 1 - x e)

def separableLower (x : E → ℝ) : ℝ := entropy x - 3 * entropy (fun e => 1 - x e)

def structuralBase (k : ℕ) : ℝ :=
  if k = 1 then 1 else (k : ℝ) * (1 - 1 / (k : ℝ)) ^ (3 * (k - 1))

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem continuous_separableLower : Continuous (separableLower (E := E)) := by
  exact continuous_entropy.sub (continuous_const.mul (continuous_entropy.comp (by fun_prop)))

def separableLineD (x v : E → ℝ) (t : ℝ) : ℝ :=
  entropyLineD x v t - 3 * entropyLineD (fun e => 1-x e) (fun e => -v e) t

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem separable_line_eventually_hasDerivAt (x v : E → ℝ)
    (hzero : ∀ e, x e = 0 → v e = 0) (hone : ∀ e, x e = 1 → v e = 0) :
    ∀ᶠ t : ℝ in 𝓝 0,
      HasDerivAt (fun t => separableLower (fun e => x e+t*v e))
        (separableLineD x v t) t := by
  have hbar : ∀ e, 1-x e=0 → -v e=0 := by
    intro e he
    rw [hone e (by linarith), neg_zero]
  filter_upwards [entropy_line_eventually_hasDerivAt x v hzero,
    entropy_line_eventually_hasDerivAt (fun e => 1-x e) (fun e => -v e) hbar]
    with t ht hb
  have he : (fun t => separableLower (fun e => x e+t*v e)) =
      (fun t => entropy (fun e => x e+t*v e) -
        3 * entropy (fun e => (1-x e)+t*(-v e))) := by
    funext t
    unfold separableLower
    congr 2
    congr 1
    funext e
    ring
  rw [he]
  exact ht.sub (hb.const_mul 3)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem separableLineD_hasDerivAt (x v : E → ℝ)
    (hzero : ∀ e, x e = 0 → v e = 0) (hone : ∀ e, x e = 1 → v e = 0) :
    HasDerivAt (separableLineD x v)
      (-(∑ e, (v e)^2/x e) + 3*(∑ e, (v e)^2/(1-x e))) 0 := by
  have hbar : ∀ e, 1-x e=0 → -v e=0 := by
    intro e he
    rw [hone e (by linarith), neg_zero]
  have hd := (entropyLineD_hasDerivAt x v hzero).sub
    ((entropyLineD_hasDerivAt (fun e => 1-x e) (fun e => -v e) hbar).const_mul 3)
  exact hd.congr_deriv (by simp only [neg_sq]; ring)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem separable_second_variation {A : Type*} [Fintype A]
    (x v : E → ℝ) (hzero : ∀ e, x e=0 → v e=0) (hone : ∀ e, x e=1 → v e=0)
    {p : A → ℝ} (hp : p ∈ probabilitySimplex A) (a : A → ℝ)
    (hcenter : ∑ i, p i*a i=0) (c₀ c₁ : ℝ)
    (hlocal : IsLocalMax (fun t => separableLower (fun e => x e+t*v e) +
      c₀+t*c₁+t^2*(∑ i, p i*(a i)^2)-Real.log (partition p a t)) 0) :
    -(∑ e, (v e)^2/x e) + 3*(∑ e, (v e)^2/(1-x e)) +
      (∑ i, p i*(a i)^2) ≤ 0 := by
  have hf := separable_line_eventually_hasDerivAt x v hzero hone
  have hg : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt (fun t => Real.log (partition p a t))
      (partition (fun i => p i*a i) a t / partition p a t) t :=
    Filter.Eventually.of_forall (logPartition_hasDerivAt hp a)
  have hd := second_deriv_quadratic_adjustment (c₀ := c₀) (c₁ := c₁)
    (v := ∑ i, p i*(a i)^2) hf hg (separableLineD_hasDerivAt x v hzero hone)
    (logPartition_second hp a)
  have hc : ContinuousAt (fun t => separableLower (fun e => x e+t*v e) +
      c₀+t*c₁+t^2*(∑ i, p i*(a i)^2)-Real.log (partition p a t)) 0 := by
    apply ContinuousAt.sub
    · apply ContinuousAt.add
      · apply ContinuousAt.add
        · exact hf.self_of_nhds.continuousAt.add_const c₀
        · fun_prop
      · fun_prop
    · exact hg.self_of_nhds.continuousAt
  have hh := second_deriv_nonpos_of_local_max hlocal hc
  rw [hd.deriv, hcenter] at hh
  nlinarith

omit [Fintype V] [DecidableEq V] in
theorem mean_score_one (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) (a : G.Matching → ℝ)
    (hcenter : ∑ M, p M*a M=0) :
    ∀ e, G.mean p e=1 → G.mean (fun M => p M*a M) e=0 := by
  intro e he
  have hz : ∑ M, p M*(1-G.indicator M e)=0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hp.2]
    change 1-G.mean p e=0
    rw [he, sub_self]
  have hterms : ∀ M, p M*(1-G.indicator M e)=0 := by
    exact fun M => (Finset.sum_eq_zero_iff_of_nonneg
      (fun M (_ : M ∈ Finset.univ) =>
        mul_nonneg (hp.1 M) (sub_nonneg.mpr (G.indicator_le_one M e)))).mp hz M (by simp)
  calc
    _ = ∑ M, p M*a M := by
      apply Finset.sum_congr rfl
      intro M _
      have hh := hterms M
      have hh' : a M*(p M*(1-G.indicator M e))=0 := by rw [hh, mul_zero]
      nlinarith [hh']
    _ = 0 := hcenter

omit [Fintype V] [DecidableEq V] in

theorem matching_separable_second_variation (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hmax : ∀ y ∈ G.polytope, separableLower y-maxMatchingEntropy G y ≤
      separableLower x-maxMatchingEntropy G x)
    (u : E → ℝ) (c : ℝ) (hcenter : ∑ M, p M*linearScore G u c M=0) :
    -(∑ e, (G.mean (fun M => p M*linearScore G u c M) e)^2/x e) +
      3*(∑ e, (G.mean (fun M => p M*linearScore G u c M) e)^2/(1-x e)) +
      (∑ M, p M*(linearScore G u c M)^2) ≤ 0 := by
  let a := linearScore G u c
  let v := G.mean (fun M => p M*a M)
  let c₀ := ∑ M, p M*Real.log (p M)
  let c₁ := ∑ M, (p M*a M)*Real.log (p M)
  have hzero : ∀ e, x e=0 → v e=0 := by
    rw [← hp.2]
    exact mean_score_support G hp.1 a
  have hone : ∀ e, x e=1 → v e=0 := by
    rw [← hp.2]
    exact mean_score_one G hp.1 a hcenter
  apply separable_second_variation x v hzero hone hp.1 a hcenter c₀ c₁
  filter_upwards [score_law_eventually_simplex hp.1 a hcenter] with t ht
  let r := fun M => p M+t*(p M*a M)
  have hr : r ∈ probabilitySimplex G.Matching := ht
  have hrmean : G.mean r=fun e => x e+t*v e := by
    change G.meanLinear (p+t • (fun M => p M*a M)) = _
    rw [map_add, map_smul]
    change G.mean p+t • v = _
    rw [hp.2]
    rfl
  have hdual := matching_entropy_dual_bound G hp hopt hr
    (fun M hM => by dsimp [r]; simp [hM]) u c t
  have hscore : (∑ M, r M*a M)=t*(∑ M, p M*(a M)^2) := by
    dsimp [r]
    simp_rw [add_mul, mul_assoc t, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hcenter, zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro M _
    ring
  have hlog : (∑ M, r M*Real.log (p M))=c₀+t*c₁ := by
    dsimp [r, c₀, c₁]
    simp_rw [add_mul, mul_assoc t, Finset.sum_add_distrib, ← Finset.mul_sum]
  change maxMatchingEntropy G (G.mean r) ≤
    Real.log (partition p a t) - (∑ M, r M*Real.log (p M)) - t*(∑ M, r M*a M) at hdual
  rw [hlog, hscore] at hdual
  have hmaxr := hmax (G.mean r) (G.mean_mem_polytope hr)
  have hpart := partition_zero hp.1 a
  simp only [zero_mul, zero_pow (by omega : 2 ≠ 0), add_zero, hpart,
    Real.log_one, sub_zero]
  rw [← hopt, entropy_eq p] at hmaxr
  rw [← hrmean]
  dsimp only [c₀] at *
  nlinarith

end MatchingEntropy
end
end

end OAI
end
end

section
section
namespace OAI


section

noncomputable section
open scoped BigOperators
open Matrix
namespace MatchingEntropy

theorem spectral_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℝ} (hC : C.IsHermitian) (e : I) :
    C e e = ∑ i, hC.eigenvalues i * (hC.eigenvectorBasis i e)^2 := by
  have hh := congrArg (fun A : Matrix I I ℝ => A e e) hC.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hh
  simpa only [mul_apply, diagonal_apply, star_eq_conjTranspose, conjTranspose_apply,
    star_trivial, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq,
    mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Matrix.IsHermitian.eigenvectorUnitary_apply, pow_two, mul_comm, mul_left_comm,
    mul_assoc] using hh

theorem covariance_weighted_rank {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℝ} (hC : C.PosSemidef) (w : I → ℝ)
    (hsecond : ∀ u : I → ℝ,
      u ⬝ᵥ (C *ᵥ u) ≤ ∑ e, w e * ((C *ᵥ u) e)^2) :
    (C.rank : ℝ) ≤ ∑ e, w e * C e e := by
  let eig := hC.isHermitian.eigenvalues
  let b := hC.isHermitian.eigenvectorBasis
  have heig : ∀ i, 0 ≤ eig i := hC.eigenvalues_nonneg
  have hone : ∀ i, eig i ≠ 0 → 1 ≤ eig i * (∑ e, w e * (b i e)^2) := by
    intro i hi
    let v : I → ℝ := b i
    have hv : v ⬝ᵥ v=1 := by
      have hn := b.orthonormal.1 i
      have hb : inner ℝ (b i) (b i)=1 := by
        rw [real_inner_self_eq_norm_sq, hn]
        norm_num
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hb
    have he : C *ᵥ v=eig i • v := hC.isHermitian.mulVec_eigenvectorBasis i
    have hs := hsecond v
    rw [he] at hs
    simp only [dotProduct_smul, smul_eq_mul, hv, mul_one, Pi.smul_apply] at hs
    have heq : (∑ e, w e*(eig i * v e)^2) =
        (eig i)^2 * (∑ e, w e*(v e)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    rw [heq] at hs
    have hp : 0 < eig i := lt_of_le_of_ne (heig i) (Ne.symm hi)
    nlinarith
  rw [hC.isHermitian.rank_eq_card_non_zero_eigs]
  calc
    (Fintype.card {i // eig i ≠ 0} : ℝ) = ∑ i : {i // eig i ≠ 0}, (1:ℝ) := by simp
    _ ≤ ∑ i : {i // eig i ≠ 0}, eig i * (∑ e, w e*(b i e)^2) :=
      Finset.sum_le_sum fun i _ => hone i i.property
    _ = ∑ i, eig i * (∑ e, w e*(b i e)^2) := by
      exact sum_subtype_supported (fun i => eig i ≠ 0)
        (fun i => eig i * (∑ e, w e*(b i e)^2))
        (by intro i hi; rw [not_ne_iff.mp hi, zero_mul])
    _ = ∑ e, w e * C e e := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [spectral_diagonal hC.isHermitian e, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [eig, b]
      ring

end MatchingEntropy
end
end

end OAI
end
end

section
section
namespace OAI


section

noncomputable section
open scoped BigOperators Topology
open Matrix Filter
namespace MatchingEntropy
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem separableDefect_attains_max (G : LooplessGraph V E)
    (heven : Even (Fintype.card V)) (hPM : Nonempty G.Matching) :
    ∃ x ∈ G.polytope, ∀ y ∈ G.polytope,
      separableLower y-maxMatchingEntropy G y ≤ separableLower x-maxMatchingEntropy G x := by
  have hs : UpperSemicontinuousOn (fun y => separableLower y-maxMatchingEntropy G y)
      G.polytope := by
    simpa only [sub_eq_add_neg, Pi.neg_apply] using
      continuous_separableLower.continuousOn.upperSemicontinuousOn.add
        (maxMatchingEntropy_lowerSemicontinuousOn G heven).neg
  have hn : G.polytope.Nonempty := by
    obtain ⟨M⟩ := hPM
    exact ⟨G.indicator M,subset_convexHull ℝ _ (Set.mem_range_self M)⟩
  exact UpperSemicontinuousOn.exists_isMaxOn hn G.compact_polytope hs

theorem matching_covariance_rank_face (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws x) (hopt : entropy p=maxMatchingEntropy G x) :
    Fintype.card {e // 0 < x e} ≤ G.faceCodimension x+
      (covariance p (matchingNormalized G x)).rank := by
  let W := weightedDirectionSpace p (matchingNormalized G x)
  let L : G.faceSpace x →ₗ[ℝ] W :=
    ((normalizeLinear x).comp (G.faceSpace x).subtype).codRestrict W
      (fun u => normalized_face_mem G heven hp hopt u.property)
  have hi : Function.Injective L := by
    intro u v huv
    apply Subtype.ext
    funext e
    have hh := congrFun (congrArg Subtype.val huv) e
    change u.val e/Real.sqrt (x e.val)=v.val e/Real.sqrt (x e.val) at hh
    exact (div_left_inj' (ne_of_gt (Real.sqrt_pos.mpr e.property))).mp hh
  have hdim := LinearMap.finrank_le_finrank_of_injective hi
  have hq := (G.faceSpace x).finrank_quotient_add_finrank
  rw [covariance_rank hp.1.1]
  have hq' : G.faceCodimension x+Module.finrank ℝ (G.faceSpace x)=Fintype.card {e // 0 < x e} := by
    simpa only [LooplessGraph.faceCodimension,Module.finrank_pi,Module.finrank_self,Finset.sum_const,
      Finset.card_univ,smul_eq_mul,mul_one] using hq
  change Module.finrank ℝ (G.faceSpace x) ≤ Module.finrank ℝ W at hdim
  dsimp only [W] at hdim
  omega

theorem faceCodimension_strict (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hn : 0 < Fintype.card V) (hx : x ∈ G.polytope) :
    G.faceCodimension x < 2*Fintype.card V := by
  by_cases hn4 : 4 ≤ Fintype.card V
  · have hb := LooplessGraph.faceCodimension_strong_aux (Fintype.card V) G rfl heven hn4 x
      (G.polytope_subset_constraintPolytope hx)
    omega
  · have hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1 := by
      rintro ⟨S,_,hlo,hhi,_⟩
      have hh := Finset.card_compl_add_card S
      omega
    have hb := G.faceCodimension_no_tight heven hnt
    omega

omit [Fintype V] [DecidableEq V] in

theorem matching_separable_covariance (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hmax : ∀ y ∈ G.polytope, separableLower y-maxMatchingEntropy G y ≤
      separableLower x-maxMatchingEntropy G x)
    (u : {e // 0 < x e} → ℝ) :
    u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) ≤
      ∑ e, (1-3*x e.val/(1-x e.val))*((covariance p (matchingNormalized G x) *ᵥ u) e)^2 := by
  let w := matchingScoreWeights x u
  let c := ∑ e, w e*x e
  let a := linearScore G w c
  let v := G.mean (fun M => p M*a M)
  have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p,hp⟩
  have hcenter : ∑ M, p M*a M=0 := by
    dsimp only [a,c]
    rw [linearScore_expectation,hp.2,hp.1.2,mul_one,sub_self]
  have hh := matching_separable_second_variation G hp hopt hmax w c hcenter
  have hzero : ∀ e, ¬0 < x e → v e=0 := by
    intro e he
    have he0 : x e=0 := le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1
    exact mean_score_support G hp.1 a e (by rw [hp.2,he0])
  have hnorm : (∑ e, (v e)^2/x e) =
      ∑ e, ((covariance p (matchingNormalized G x) *ᵥ u) e)^2 := by
    rw [sum_positive_support x _ (fun e he => by rw [hzero e he]; simp)]
    apply Finset.sum_congr rfl
    intro e _
    rw [matchingNormalized_mulVec G hp,div_pow,Real.sq_sqrt e.property.le]
  have hbar : (∑ e, (v e)^2/(1-x e)) =
      ∑ e, x e.val/(1-x e.val)*((covariance p (matchingNormalized G x) *ᵥ u) e)^2 := by
    rw [sum_positive_support x _ (fun e he => by rw [hzero e he]; simp)]
    apply Finset.sum_congr rfl
    intro e _
    rw [matchingNormalized_mulVec G hp,div_pow,Real.sq_sqrt e.property.le]
    change (v e.val)^2/(1-x e.val)=x e.val/(1-x e.val)*((v e.val)^2/x e.val)
    field_simp [ne_of_gt e.property]
  have hquad : (∑ M, p M*(a M)^2)=u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) := by
    rw [covariance_quadratic hp.1.1]
    apply Finset.sum_congr rfl
    intro M _
    rw [← matchingNormalized_score G x u M]
  change -(∑ e, (v e)^2/x e)+3*(∑ e, (v e)^2/(1-x e))+(∑ M,p M*(a M)^2) ≤ 0 at hh
  rw [hnorm,hbar,hquad] at hh
  have heq : (∑ e, (1-3*x e.val/(1-x e.val))*((covariance p (matchingNormalized G x) *ᵥ u) e)^2) =
      (∑ e, ((covariance p (matchingNormalized G x) *ᵥ u) e)^2)-
      3*(∑ e, x e.val/(1-x e.val)*((covariance p (matchingNormalized G x) *ᵥ u) e)^2) := by
    simp_rw [sub_mul,one_mul,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [heq]
  linarith

omit [Fintype V] [DecidableEq V] in
theorem matching_covariance_diagonal (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) (e : {e // 0<x e}) :
    covariance p (matchingNormalized G x) e e=1-x e.val := by
  rw [covariance_entry hp.1.1]
  have hh := normalizedCentered_variance hp.1.2
    (fun M (e : {e // 0<x e}) => G.indicator M e.val)
    (by intro M e; simp only [LooplessGraph.indicator]; split <;> norm_num)
    (fun e => x e.val) (fun e => congrFun hp.2 e.val) (fun e => e.property) e
  convert hh using 1
  apply Finset.sum_congr rfl
  intro M _
  change p M*matchingNormalized G x M e*matchingNormalized G x M e=
    p M*(matchingNormalized G x M e)^2
  ring

theorem separable_max_has_forced (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hn : 0 < Fintype.card V) (hx : x ∈ G.polytope)
    (hmax : ∀ y ∈ G.polytope, separableLower y-maxMatchingEntropy G y ≤
      separableLower x-maxMatchingEntropy G x) : ∃ e, x e=1 := by
  by_contra hforced
  push Not at hforced
  obtain ⟨p,hp,hopt⟩ := maxMatchingEntropy_attained G hx
  have hsecond := covariance_weighted_rank (covariance_posSemidef p (matchingNormalized G x))
    (fun e => 1-3*x e.val/(1-x e.val)) (matching_separable_covariance G hp hopt hmax)
  have htrace : (∑ e : {e // 0<x e}, (1-3*x e.val/(1-x e.val))*
      covariance p (matchingNormalized G x) e e) = Fintype.card {e // 0<x e}-2*(Fintype.card V:ℝ) := by
    have he (e : {e // 0<x e}) : (1-3*x e.val/(1-x e.val))*
        covariance p (matchingNormalized G x) e e=1-4*x e.val := by
      rw [matching_covariance_diagonal G hp]
      have hh : 1-x e.val ≠ 0 := sub_ne_zero.mpr (Ne.symm (hforced e.val))
      field_simp
      ring
    simp_rw [he]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum]
    obtain ⟨r,hr⟩ := heven
    have hv : Fintype.card V=2*r := by omega
    have hs : (∑ e : {e // 0<x e}, x e.val)=(r:ℝ) := by
      rw [← G.marginal_sum hv hx]
      exact (sum_positive_support x x (fun e he =>
        le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1)).symm
    rw [hs,hv]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Nat.cast_mul,Nat.cast_ofNat]
    ring
  rw [htrace] at hsecond
  have hrank := matching_covariance_rank_face G heven hp hopt
  have hstrict := faceCodimension_strict G heven hn hx
  have hrankR : (Fintype.card {e // 0<x e}:ℝ) ≤ G.faceCodimension x+
      (covariance p (matchingNormalized G x)).rank := by exact_mod_cast hrank
  have hstrictR : (G.faceCodimension x:ℝ)<2*(Fintype.card V:ℝ) := by exact_mod_cast hstrict
  linarith

end MatchingEntropy
end
end

end OAI
end
end

section
section
namespace OAI


section

noncomputable section
open scoped BigOperators
namespace MatchingEntropy
namespace LooplessGraph
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def RemainingVertex (G : LooplessGraph V E) (e₀ : E) (v : V) : Prop :=
  ¬G.Incident v e₀

instance remainingVertexDecidable (G : LooplessGraph V E) (e₀ : E) (v : V) :
    Decidable (G.RemainingVertex e₀ v) := inferInstanceAs (Decidable (¬G.Incident v e₀))

def RemainingEdge (G : LooplessGraph V E) (e₀ e : E) : Prop :=
  G.RemainingVertex e₀ (G.left e) ∧ G.RemainingVertex e₀ (G.right e)

instance remainingEdgeDecidable (G : LooplessGraph V E) (e₀ e : E) :
    Decidable (G.RemainingEdge e₀ e) := inferInstanceAs
      (Decidable (G.RemainingVertex e₀ (G.left e) ∧ G.RemainingVertex e₀ (G.right e)))

def deleteEndpoints (G : LooplessGraph V E) (e₀ : E) :
    LooplessGraph {v // G.RemainingVertex e₀ v} {e // G.RemainingEdge e₀ e} where
  left e := ⟨G.left e.val, e.property.1⟩
  right e := ⟨G.right e.val, e.property.2⟩
  loopless e he := G.loopless e.val (congrArg Subtype.val he)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem remainingEdge_ne (G : LooplessGraph V E) (e₀ : E)
    {e : E} (he : G.RemainingEdge e₀ e) : e ≠ e₀ := by
  rintro rfl
  exact he.1 (Or.inl rfl)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem remaining_of_incident (G : LooplessGraph V E) (e₀ : E)
    {e : E} (he : G.RemainingEdge e₀ e) {v : V} (hv : G.Incident v e) :
    G.RemainingVertex e₀ v := by
  rcases hv with h | h
  · exact h ▸ he.1
  · exact h ▸ he.2

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
@[simp] theorem deleteEndpoints_incident (G : LooplessGraph V E) (e₀ : E)
    (v : {v // G.RemainingVertex e₀ v}) (e : {e // G.RemainingEdge e₀ e}) :
    (G.deleteEndpoints e₀).Incident v e ↔ G.Incident v.val e.val := by
  simp only [Incident, deleteEndpoints, Subtype.ext_iff]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem matching_common_vertex (G : LooplessGraph V E) (M : G.Matching)
    {e f : E} (he : e ∈ M.val) (hf : f ∈ M.val) {v : V}
    (hve : G.Incident v e) (hvf : G.Incident v f) : e=f := by
  obtain ⟨g, _, hg⟩ := M.property v
  exact (hg e ⟨he,hve⟩).trans (hg f ⟨hf,hvf⟩).symm

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in

theorem matching_remaining (G : LooplessGraph V E) (e₀ : E) (M : G.Matching)
    (h₀ : e₀ ∈ M.val) {e : E} (he : e ∈ M.val) (hne : e ≠ e₀) :
    G.RemainingEdge e₀ e := by
  constructor
  · intro hv
    exact hne (G.matching_common_vertex M he h₀ (Or.inl rfl) hv)
  · intro hv
    exact hne (G.matching_common_vertex M he h₀ (Or.inr rfl) hv)

def addForced (G : LooplessGraph V E) (e₀ : E) (N : (G.deleteEndpoints e₀).Matching) :
    G.Matching := by
  refine ⟨insert e₀ (N.val.image Subtype.val), ?_⟩
  intro v
  by_cases hv : G.Incident v e₀
  · refine ⟨e₀, ⟨by simp, hv⟩, ?_⟩
    rintro f ⟨hf,hfv⟩
    rcases Finset.mem_insert.mp hf with h | h
    · exact h
    · obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp h
      exact False.elim (G.remaining_of_incident e₀ g.property hfv hv)
  · let v' : {v // G.RemainingVertex e₀ v} := ⟨v,hv⟩
    obtain ⟨f,⟨hf,hfv⟩, hu⟩ := N.property v'
    refine ⟨f.val, ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨f,hf,rfl⟩),
      (G.deleteEndpoints_incident e₀ v' f).mp hfv⟩, ?_⟩
    rintro g ⟨hg,hgv⟩
    rcases Finset.mem_insert.mp hg with h | h
    · exact False.elim (hv (h ▸ hgv))
    · obtain ⟨g',hg',rfl⟩ := Finset.mem_image.mp h
      exact congrArg Subtype.val (hu g' ⟨hg', (G.deleteEndpoints_incident e₀ v' g').mpr hgv⟩)

omit [Fintype V] [Fintype E] in
@[simp] theorem mem_addForced (G : LooplessGraph V E) (e₀ : E)
    (N : (G.deleteEndpoints e₀).Matching) (e : E) :
    e ∈ (G.addForced e₀ N).val ↔ e=e₀ ∨ ∃ h : G.RemainingEdge e₀ e, ⟨e,h⟩ ∈ N.val := by
  simp only [addForced, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (h | ⟨f,hf,rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨f.property,hf⟩
  · rintro (h | ⟨h,he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨e,h⟩,he,rfl⟩

omit [Fintype V] [Fintype E] in
@[simp] theorem mem_addForced_remaining (G : LooplessGraph V E) (e₀ : E)
    (N : (G.deleteEndpoints e₀).Matching) (e : {e // G.RemainingEdge e₀ e}) :
    e.val ∈ (G.addForced e₀ N).val ↔ e ∈ N.val := by
  rw [mem_addForced]
  simp only [G.remainingEdge_ne e₀ e.property, false_or]
  exact ⟨fun ⟨_,h⟩ => h, fun h => ⟨e.property,h⟩⟩

def removeForced (G : LooplessGraph V E) (e₀ : E)
    (M : {M : G.Matching // e₀ ∈ M.val}) : (G.deleteEndpoints e₀).Matching := by
  refine ⟨M.val.val.subtype (G.RemainingEdge e₀), ?_⟩
  intro v
  obtain ⟨e,⟨he,hev⟩,hu⟩ := M.val.property v.val
  have hne : e ≠ e₀ := by rintro rfl; exact v.property hev
  have hrem := G.matching_remaining e₀ M.val M.property he hne
  refine ⟨⟨e,hrem⟩, ⟨by simpa using he,
    (G.deleteEndpoints_incident e₀ v ⟨e,hrem⟩).mpr hev⟩, ?_⟩
  rintro f ⟨hf,hfv⟩
  apply Subtype.ext
  exact hu f.val ⟨by simpa using hf, (G.deleteEndpoints_incident e₀ v f).mp hfv⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem mem_removeForced (G : LooplessGraph V E) (e₀ : E)
    (M : {M : G.Matching // e₀ ∈ M.val}) (e : {e // G.RemainingEdge e₀ e}) :
    e ∈ (G.removeForced e₀ M).val ↔ e.val ∈ M.val.val := by
  simp [removeForced]

def forcedMatchingEquiv (G : LooplessGraph V E) (e₀ : E) :
    (G.deleteEndpoints e₀).Matching ≃ {M : G.Matching // e₀ ∈ M.val} where
  toFun N := ⟨G.addForced e₀ N, (G.mem_addForced e₀ N e₀).mpr (Or.inl rfl)⟩
  invFun M := G.removeForced e₀ M
  left_inv N := by
    apply Subtype.ext
    ext e
    exact (G.mem_removeForced e₀ _ e).trans (G.mem_addForced_remaining e₀ N e)
  right_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    ext e
    rw [mem_addForced]
    constructor
    · rintro (rfl | ⟨h,he⟩)
      · exact M.property
      · exact (G.mem_removeForced e₀ M ⟨e,h⟩).mp he
    · intro he
      by_cases h : e=e₀
      · exact Or.inl h
      · exact Or.inr ⟨G.matching_remaining e₀ M.val M.property he h,
          (G.mem_removeForced e₀ M _).mpr he⟩

omit [Fintype V] [Fintype E] in
theorem addForced_injective (G : LooplessGraph V E) (e₀ : E) :
    Function.Injective (G.addForced e₀) := by
  intro N N' h
  apply (G.forcedMatchingEquiv e₀).injective
  exact Subtype.ext h

omit [Fintype E] [DecidableEq E] in
theorem remaining_vertex_card (G : LooplessGraph V E) (e₀ : E) :
    Fintype.card {v // G.RemainingVertex e₀ v} + 2 = Fintype.card V := by
  have he : Fintype.card {v // G.Incident v e₀}=2 := by
    rw [Fintype.card_subtype]
    have hf : Finset.univ.filter (fun v => G.Incident v e₀)={G.left e₀, G.right e₀} := by
      ext v
      simp [Incident, eq_comm]
    rw [hf, Finset.card_pair (G.loopless e₀)]
  have h := Fintype.card_subtype_compl (G.Incident · e₀)
  have hle := Fintype.card_subtype_le (G.Incident · e₀)
  change Fintype.card {v // ¬G.Incident v e₀} + 2 = Fintype.card V
  omega

omit [Fintype V] [Fintype E] in
@[simp] theorem range_addForced (G : LooplessGraph V E) (e₀ : E) (M : G.Matching) :
    M ∈ Set.range (G.addForced e₀) ↔ e₀ ∈ M.val := by
  constructor
  · rintro ⟨N,rfl⟩
    exact (G.mem_addForced e₀ N e₀).mpr (Or.inl rfl)
  · intro h
    refine ⟨G.removeForced e₀ ⟨M,h⟩, ?_⟩
    exact congrArg Subtype.val ((G.forcedMatchingEquiv e₀).apply_symm_apply ⟨M,h⟩)

omit [Fintype V] [DecidableEq V] in
theorem law_support_of_mean_one (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) {e₀ : E} (he : G.mean p e₀=1)
    (M : G.Matching) (hM : e₀ ∉ M.val) : p M=0 := by
  have hz : ∑ N, p N*(1-G.indicator N e₀)=0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hp.2]
    change 1-G.mean p e₀=0
    rw [he, sub_self]
  have hh := (Finset.sum_eq_zero_iff_of_nonneg
    (fun N (_ : N ∈ Finset.univ) =>
      mul_nonneg (hp.1 N) (sub_nonneg.mpr (G.indicator_le_one N e₀)))).mp hz M (by simp)
  simpa [indicator,hM] using hh

omit [Fintype V] in

theorem forcedLaw_feasible (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) (e₀ : E) (he : x e₀=1) :
    (fun N => p (G.addForced e₀ N)) ∈ (G.deleteEndpoints e₀).feasibleLaws
      (fun e => x e.val) := by
  have hs : ∀ M, e₀ ∉ M.val → p M=0 :=
    G.law_support_of_mean_one hp.1 (by rw [hp.2,he])
  refine ⟨⟨fun N => hp.1.1 _, ?_⟩, ?_⟩
  · rw [← hp.1.2]
    apply Fintype.sum_of_injective (G.addForced e₀) (G.addForced_injective e₀)
    · intro M hM
      exact hs M (fun hh => hM ((G.range_addForced e₀ M).mpr hh))
    · intro N
      rfl
  · funext e
    rw [← congrFun hp.2 e.val]
    apply Fintype.sum_of_injective (G.addForced e₀) (G.addForced_injective e₀)
    · intro M hM
      rw [hs M (fun hh => hM ((G.range_addForced e₀ M).mpr hh)),zero_mul]
    · intro N
      simp only [indicator,mem_addForced_remaining]

omit [Fintype V] [DecidableEq V] in

theorem forced_coordinate_zero (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1) {e : E}
    (hneq : e ≠ e₀) (hrem : ¬G.RemainingEdge e₀ e) : x e=0 := by
  obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
  rw [← congrFun hp.2 e]
  apply Finset.sum_eq_zero
  intro M _
  by_cases hM : e₀ ∈ M.val
  · have hh : e ∉ M.val := fun hh => hrem (G.matching_remaining e₀ M hM hh hneq)
    simp [indicator,hh]
  · rw [G.law_support_of_mean_one hp.1 (by rw [hp.2,he]) M hM,zero_mul]

omit [Fintype V] in

theorem separableLower_forced (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1) :
    separableLower (fun e : {e // G.RemainingEdge e₀ e} => x e.val)=separableLower x := by
  have hz : ∀ e, ¬G.RemainingEdge e₀ e →
      Real.negMulLog (x e)=0 ∧ Real.negMulLog (1-x e)=0 := by
    intro e h
    by_cases hneq : e=e₀
    · simp [hneq,he]
    · simp [G.forced_coordinate_zero hx e₀ he hneq h]
  unfold separableLower entropy
  rw [sum_subtype_supported _ _ (fun e h => (hz e h).1),
    sum_subtype_supported _ _ (fun e h => (hz e h).2)]

end LooplessGraph

theorem entropy_fiberMass_injective {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (p : A → ℝ) (f : A → B) (hf : Function.Injective f) :
    entropy (fiberMass p f)=entropy p := by
  classical
  have hself (a : A) : fiberMass p f (f a)=p a := by
    simp [fiberMass,hf.eq_iff]
  have hzero (b : B) (hb : b ∉ Set.range f) : fiberMass p f b=0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact ite_eq_right (fun h => hb ⟨a,h⟩)
  symm
  apply Fintype.sum_of_injective f hf
  · intro b hb
    rw [hzero b hb,Real.negMulLog_zero]
  · intro a
    rw [hself]

namespace LooplessGraph
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
omit [Fintype V] in

theorem liftForced_feasible (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1)
    {q : (G.deleteEndpoints e₀).Matching → ℝ}
    (hq : q ∈ (G.deleteEndpoints e₀).feasibleLaws (fun e => x e.val)) :
    fiberMass q (G.addForced e₀) ∈ G.feasibleLaws x := by
  refine ⟨fiberMass_mem_simplex hq.1 _, ?_⟩
  funext e
  rw [mean,fiberMass_expect]
  by_cases heq : e=e₀
  · subst e
    simpa [indicator] using hq.1.2.trans he.symm
  · by_cases hr : G.RemainingEdge e₀ e
    · change (∑ N, q N*G.indicator (G.addForced e₀ N) e)=_
      have hm (N : (G.deleteEndpoints e₀).Matching) :
          G.indicator (G.addForced e₀ N) e = (G.deleteEndpoints e₀).indicator N ⟨e,hr⟩ := by
        simp only [indicator,G.mem_addForced_remaining e₀ N ⟨e,hr⟩]
      simp_rw [hm]
      exact congrFun hq.2 ⟨e,hr⟩
    · rw [G.forced_coordinate_zero hx e₀ he heq hr]
      apply Finset.sum_eq_zero
      intro N _
      simp [indicator,heq,hr]

omit [Fintype V] in

theorem maxMatchingEntropy_forced_le (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1) :
    maxMatchingEntropy (G.deleteEndpoints e₀) (fun e => x e.val) ≤ maxMatchingEntropy G x := by
  obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
  have hr := G.forcedLaw_feasible hp e₀ he
  have hx' := ((G.deleteEndpoints e₀).mem_polytope_iff _).mpr ⟨_,hr⟩
  obtain ⟨q,hq,hopt⟩ := maxMatchingEntropy_attained (G.deleteEndpoints e₀) hx'
  rw [← hopt,← entropy_fiberMass_injective q _ (G.addForced_injective e₀)]
  exact entropy_le_maxMatchingEntropy G (G.liftForced_feasible hx e₀ he hq)

end LooplessGraph
end MatchingEntropy
end
end

end OAI
end
end

section
section
namespace OAI


section

noncomputable section
open scoped BigOperators Topology
namespace MatchingEntropy

theorem separable_lower_aux (n : ℕ) :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessGraph V E), Fintype.card V=n → Even n →
      ∀ x ∈ G.polytope, separableLower x ≤ maxMatchingEntropy G x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E _ _ _ _ G hcard heven y hy
    by_cases hn : n=0
    · have : IsEmpty V := Fintype.card_eq_zero_iff.mp (hcard.trans hn)
      have : IsEmpty E := ⟨fun e => isEmptyElim (G.left e)⟩
      simpa [separableLower,entropy] using maxMatchingEntropy_nonneg G hy
    · have heven' : Even (Fintype.card V) := hcard ▸ heven
      have hPM : Nonempty G.Matching := by
        obtain ⟨p,hp⟩ := (G.mem_polytope_iff y).mp hy
        by_contra h
        have : IsEmpty G.Matching := not_nonempty_iff.mp h
        simpa using hp.1.2
      obtain ⟨x,hx,hmax⟩ := separableDefect_attains_max G heven' hPM
      obtain ⟨e₀,he₀⟩ := separable_max_has_forced G heven' (by omega) hx hmax
      have hc := G.remaining_vertex_card e₀
      have hlt : Fintype.card {v // G.RemainingVertex e₀ v}<n := by omega
      have hev : Even (Fintype.card {v // G.RemainingVertex e₀ v}) := by
        obtain ⟨r,hr⟩ := heven
        refine ⟨r-1,?_⟩
        omega
      obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
      have hs := G.forcedLaw_feasible hp e₀ he₀
      have hxr := ((G.deleteEndpoints e₀).mem_polytope_iff _).mpr ⟨_,hs⟩
      have hsmall := ih _ hlt (G.deleteEndpoints e₀) rfl hev _ hxr
      rw [G.separableLower_forced hx e₀ he₀] at hsmall
      have hxbound := hsmall.trans (G.maxMatchingEntropy_forced_le hx e₀ he₀)
      have hcompare := hmax y hy
      linarith

variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem separable_lower (G : LooplessGraph V E) (hPM : Nonempty G.Matching)
    (x : E → ℝ) (hx : x ∈ G.polytope) : separableLower x ≤ maxMatchingEntropy G x := by
  obtain ⟨M⟩ := hPM
  have hev : Even (Fintype.card V) := ⟨M.val.card, by have hh := G.matching_card_twice M; omega⟩
  exact separable_lower_aux (Fintype.card V) G rfl hev x hx

end MatchingEntropy
end
end

end OAI
end
end

section
section
namespace OAI


section

noncomputable section
open scoped BigOperators
namespace MatchingEntropy

theorem entropy_le_subprob_crossEntropy {I : Type*} [Fintype I] {p q : I → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i ≤ 1) (hq : q ∈ probabilitySimplex I)
    (hsupp : ∀ i, p i=0 → q i=0) :
    entropy q ≤ -∑ i, q i*Real.log (p i) := by
  have hterm : ∀ i, Real.negMulLog (q i) ≤ -(q i*Real.log (p i))+p i-q i := by
    intro i
    by_cases hi : p i=0
    · simp [hi,hsupp i hi]
    · simpa only [neg_mul] using negMulLog_tangent (hq.1 i)
        (lt_of_le_of_ne (hp i) (Ne.symm hi))
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ => hterm i
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_neg_distrib,hq.2] at hh
  change entropy q ≤ -(∑ i, q i*Real.log (p i))+(∑ i,p i)-1 at hh
  linarith

variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

def matchingBits (G : LooplessGraph V E) (M : G.Matching) : E → Bool :=
  fun e => decide (e ∈ M.val)

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem matchingBits_injective (G : LooplessGraph V E) : Function.Injective G.matchingBits := by
  intro M N h
  apply Subtype.ext
  ext e
  have he := congrFun h e
  simpa only [matchingBits,decide_eq_decide] using he

end LooplessGraph

def productBoolean (x : E → ℝ) (b : E → Bool) : ℝ :=
  ∏ e, if b e then x e else 1-x e

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem productBoolean_nonneg {x : E → ℝ} (hx : ∀ e, x e ∈ Set.Icc (0:ℝ) 1)
    (b : E → Bool) : 0 ≤ productBoolean x b := by
  apply Finset.prod_nonneg
  intro e _
  split
  · exact (hx e).1
  · exact sub_nonneg.mpr (hx e).2

omit [Fintype V] [DecidableEq V] in
theorem productBoolean_sum (x : E → ℝ) : (∑ b : E → Bool, productBoolean x b)=1 := by
  unfold productBoolean
  rw [← Fintype.prod_sum (fun e (b : Bool) => if b then x e else 1-x e)]
  simp

omit [Fintype V] [DecidableEq V] in
theorem matchingBoolean_sum_le (G : LooplessGraph V E) {x : E → ℝ}
    (hx : ∀ e, x e ∈ Set.Icc (0:ℝ) 1) :
    (∑ M, productBoolean x (G.matchingBits M)) ≤ 1 := by
  rw [← productBoolean_sum x]
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image G.matchingBits, productBoolean x b := by
      rw [Finset.sum_image]
      intro M _ N _ h
      exact G.matchingBits_injective h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun b _ _ => productBoolean_nonneg hx b)

omit [Fintype V] [DecidableEq V] in
theorem matching_boolean_factor_pos (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) {M : G.Matching} (hM : 0<p M) (e : E) :
    0<(if G.matchingBits M e then x e else 1-x e) := by
  unfold LooplessGraph.matchingBits
  by_cases he : e ∈ M.val
  · simp only [he,decide_true,ite_true]
    have hh := Finset.single_le_sum (f := fun N => p N*G.indicator N e)
      (s := Finset.univ) (fun N _ => mul_nonneg (hp.1.1 N) (G.indicator_nonneg N e))
      (Finset.mem_univ M)
    have hm : G.indicator M e=1 := by simp [LooplessGraph.indicator,he]
    rw [hm,mul_one] at hh
    change p M ≤ G.mean p e at hh
    rw [hp.2] at hh
    exact hM.trans_le hh
  · simp only [he,decide_false]
    have hh := Finset.single_le_sum (f := fun N => p N*(1-G.indicator N e))
      (s := Finset.univ) (fun N _ => mul_nonneg (hp.1.1 N)
        (sub_nonneg.mpr (G.indicator_le_one N e))) (Finset.mem_univ M)
    have hm : G.indicator M e=0 := by simp [LooplessGraph.indicator,he]
    simp only [hm,sub_zero,mul_one,mul_sub,Finset.sum_sub_distrib,hp.1.2] at hh
    change p M ≤ 1-G.mean p e at hh
    rw [hp.2] at hh
    exact hM.trans_le hh

omit [Fintype V] [DecidableEq V] in

theorem matching_entropy_le_binary (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) : entropy p ≤ binaryEntropy x := by
  have hx := G.coordinate_mem_Icc ((G.mem_polytope_iff x).mpr ⟨p,hp⟩)
  have hprod (M : G.Matching) (hM : 0<p M) : 0<productBoolean x (G.matchingBits M) :=
    Finset.prod_pos (fun e _ => matching_boolean_factor_pos G hp hM e)
  have hcross := entropy_le_subprob_crossEntropy
    (fun M => productBoolean_nonneg hx (G.matchingBits M)) (matchingBoolean_sum_le G hx) hp.1
    (fun M hzero => le_antisymm (le_of_not_gt (fun hM => (ne_of_gt (hprod M hM)) hzero)) (hp.1.1 M))
  have hlog (M : G.Matching) : p M*Real.log (productBoolean x (G.matchingBits M)) =
      ∑ e, p M*(G.indicator M e*Real.log (x e)+(1-G.indicator M e)*Real.log (1-x e)) := by
    by_cases hzero : p M=0
    · simp [hzero]
    · have hpos : 0<p M := lt_of_le_of_ne (hp.1.1 M) (Ne.symm hzero)
      rw [productBoolean,Real.log_prod (fun e _ => ne_of_gt (matching_boolean_factor_pos G hp hpos e)),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      simp only [LooplessGraph.matchingBits,LooplessGraph.indicator]
      by_cases he : e ∈ M.val <;> simp [he]
  have heq : -(∑ M, p M*Real.log (productBoolean x (G.matchingBits M)))=binaryEntropy x := by
    simp_rw [hlog]
    rw [Finset.sum_comm]
    have he (e : E) : (∑ M, p M*(G.indicator M e*Real.log (x e)+
        (1-G.indicator M e)*Real.log (1-x e)))=
        x e*Real.log (x e)+(1-x e)*Real.log (1-x e) := by
      simp_rw [mul_add,← mul_assoc,Finset.sum_add_distrib,← Finset.sum_mul]
      have hmean : (∑ M,p M*G.indicator M e)=x e := congrFun hp.2 e
      have hbar : (∑ M,p M*(1-G.indicator M e))=1-x e := by
        simp_rw [mul_sub,mul_one,Finset.sum_sub_distrib,hp.1.2,hmean]
      rw [hmean,hbar]
    simp_rw [he]
    rw [Finset.sum_add_distrib,neg_add_rev]
    dsimp only [binaryEntropy]
    rw [entropy_eq,entropy_eq]
    ring
  rwa [heq] at hcross

omit [Fintype V] [DecidableEq V] in
theorem maxMatchingEntropy_le_binary (G : LooplessGraph V E) (x : E → ℝ)
    (hx : x ∈ G.polytope) : maxMatchingEntropy G x ≤ binaryEntropy x := by
  obtain ⟨p,hp,hopt⟩ := maxMatchingEntropy_attained G hx
  rw [← hopt]
  exact matching_entropy_le_binary G hp

end MatchingEntropy
end
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode

abbrev Store (r : ℕ) := Fin r → List Bool

inductive Instr (r : ℕ) (L : Type)
  | go : L → Instr r L
  | push : Fin r → Bool → L → Instr r L
  | pop : Fin r → L → Instr r L
  | branch : Fin r → L → L → L → Instr r L

namespace Instr
variable {r : ℕ} {L L' : Type}

def map (f : L → L') : Instr r L → Instr r L'
  | .go q => .go (f q)
  | .push k b q => .push k b (f q)
  | .pop k q => .pop k (f q)
  | .branch k e z o => .branch k (f e) (f z) (f o)

def eval : Instr r L → Store r → L × Store r
  | .go q,s => (q,s)
  | .push k b q,s => (q,Function.update s k (b::s k))
  | .pop k q,s => (q,Function.update s k (s k).tail)
  | .branch k e z o,s => ((s k).head?.elim e (fun b => if b then o else z),s)

@[simp] theorem eval_map (f : L → L') (i : Instr r L) (s : Store r) :
    (i.map f).eval s = (f (i.eval s).1,(i.eval s).2) := by
  cases i <;> simp only [map,eval]
  rename_i k e z o
  cases h : (s k).head? with
  | none => rfl
  | some b => cases b <;> rfl

abbrev Stmt (r : ℕ) (L : Type) := Turing.TM2.Stmt (fun _ : Fin r => Bool) L (Option Bool)

def target (q : Option L) : Stmt r L :=
  .load (fun _ => none) (q.elim .halt (fun l => .goto (fun _ => l)))

def translate : Instr r (Option L) → Stmt r L
  | .go q => target q
  | .push k b q => .push k (fun _ => b) (target q)
  | .pop k q => .pop k (fun _ _ => none) (target q)
  | .branch k e z o => .peek k (fun _ h => h)
      (.branch Option.isNone (target e) (.branch (fun h => h.getD false) (target o) (target z)))

@[simp] theorem target_step (q : Option L) (v : Option Bool) (s : Store r) :
    Turing.TM2.stepAux (target q) v s = ⟨q,none,s⟩ := by cases q <;> rfl

@[simp] theorem translate_step (i : Instr r (Option L)) (v : Option Bool) (s : Store r) :
    Turing.TM2.stepAux i.translate v s = ⟨(i.eval s).1,none,(i.eval s).2⟩ := by
  cases i with
  | go q => exact target_step q v s
  | push k b q => simp only [translate,Turing.TM2.stepAux,target_step,eval]
  | pop k q => simp only [translate,Turing.TM2.stepAux,target_step,eval]
  | branch k e z o =>
    simp only [translate,Turing.TM2.stepAux,target_step,eval]
    cases h : (s k).head? with
    | none => rfl
    | some b => cases b <;> rfl
end Instr

structure Block (r : ℕ) where
  Label : Type
  finite : Fintype Label
  entry : Label
  code : Label → Instr r (Option Label)

attribute [instance] Block.finite

inductive Steps {r : ℕ} {L : Type} (code : L → Instr r (Option L)) :
    Option L → Store r → Option L → Store r → ℕ → Prop
  | refl (q s) : Steps code q s q s 0
  | next (q s q' s' t)
      (rest : Steps code ((code q).eval s).1 ((code q).eval s).2 q' s' t) :
      Steps code (some q) s q' s' (t+1)

namespace Steps
variable {r : ℕ} {L L' : Type} {code : L → Instr r (Option L)}

theorem trans {q s q' s' q'' s'' t u}
    (h : Steps code q s q' s' t) (h' : Steps code q' s' q'' s'' u) :
    Steps code q s q'' s'' (t+u) := by
  induction h with
  | refl => simpa using h'
  | next q s q' s' t h ih => simpa [Nat.add_right_comm] using Steps.next q s _ _ _ (ih h')

theorem map (code' : L' → Instr r (Option L')) (f : L → L') (last : Option L')
    (hcode : ∀ l, code' (f l)=(code l).map (fun q => q.elim last (some ∘ f)))
    {q s q' s' t} (h : Steps code q s q' s' t) :
    Steps code' (q.elim last (some ∘ f)) s (q'.elim last (some ∘ f)) s' t := by
  induction h with
  | refl => exact .refl _ _
  | next q s q' s' t h ih =>
    apply Steps.next
    simpa only [hcode,Instr.eval_map] using ih

abbrev cfg (q : Option L) (s : Store r) :
    Turing.TM2.Cfg (fun _ : Fin r => Bool) L (Option Bool) := ⟨q,none,s⟩

theorem simulation {q s q' s' t} (h : Steps code q s q' s' t) :
    (fun o => o.bind (Turing.TM2.step (fun l => (code l).translate)))^[t]
      (some (cfg q s)) = some (cfg q' s') := by
  induction h with
  | refl => rfl
  | next q s q' s' t h ih =>
    rw [Function.iterate_succ_apply]
    simpa only [Option.bind_some,Turing.TM2.step,Instr.translate_step] using ih
end Steps

namespace Block
variable {r : ℕ}

def primitive (i : Instr r Unit) : Block r where
  Label := Unit
  finite := inferInstance
  entry := ()
  code _ := i.map (fun _ => none)

def seq (a b : Block r) : Block r where
  Label := a.Label ⊕ b.Label
  finite := inferInstance
  entry := .inl a.entry
  code := fun l => match l with
    | .inl q => (a.code q).map (fun t => t.elim (some (.inr b.entry)) (fun u => some (.inl u)))
    | .inr q => (b.code q).map (Option.map Sum.inr)

def cases (k : Fin r) (e z o : Block r) : Block r where
  Label := Unit ⊕ (e.Label ⊕ (z.Label ⊕ o.Label))
  finite := inferInstance
  entry := .inl ()
  code := fun l => match l with
    | .inl _ => .branch k (some (.inr (.inl e.entry)))
        (some (.inr (.inr (.inl z.entry)))) (some (.inr (.inr (.inr o.entry))))
    | .inr (.inl q) => (e.code q).map (Option.map (Sum.inr ∘ Sum.inl))
    | .inr (.inr (.inl q)) => (z.code q).map (Option.map (Sum.inr ∘ Sum.inr ∘ Sum.inl))
    | .inr (.inr (.inr q)) => (o.code q).map (Option.map (Sum.inr ∘ Sum.inr ∘ Sum.inr))

def loop (k : Fin r) (b : Block r) : Block r where
  Label := Unit ⊕ b.Label
  finite := inferInstance
  entry := .inl ()
  code := fun l => match l with
    | .inl _ => .branch k none (some (.inr b.entry)) (some (.inr b.entry))
    | .inr q => (b.code q).map (fun t => t.elim (some (.inl ())) (fun u => some (.inr u)))

abbrev Runs (b : Block r) (s s' : Store r) (t : ℕ) : Prop :=
  Steps b.code (some b.entry) s none s' t

theorem primitive_runs (i : Instr r Unit) (s : Store r) :
    (primitive i).Runs s (i.eval s).2 1 := by
  apply Steps.next
  simp only [primitive,Instr.eval_map]
  exact .refl _ _

theorem seq_runs (a b : Block r) {s s' s'' : Store r} {t u : ℕ}
    (ha : a.Runs s s' t) (hb : b.Runs s' s'' u) : (a.seq b).Runs s s'' (t+u) := by
  have h₁ := ha.map (a.seq b).code Sum.inl (some (Sum.inr b.entry)) (fun _ => rfl)
  have h₂ := hb.map (a.seq b).code Sum.inr none (by
    intro l
    change (b.code l).map _ = (b.code l).map _
    congr 1
    funext t
    cases t <;> rfl)
  exact h₁.trans h₂

def machine (b : Block r) (input output : Fin r) : Turing.FinTM2 where
  K := Fin r
  k₀ := input
  k₁ := output
  Γ _ := Bool
  Λ := b.Label
  main := b.entry
  σ := Option Bool
  initialState := none
  m l := (b.code l).translate

theorem machine_finite (b : Block r) (input output : Fin r) (k : (b.machine input output).K) :
    Finite ((b.machine input output).Γ k) := by
  change Finite Bool
  infer_instance

def machine_runs (b : Block r) (input output : Fin r) (s s' : List Bool) {t : ℕ}
    (h : b.Runs (Function.update (fun _ => []) input s)
      (Function.update (fun _ => []) output s') t) :
    Turing.TM2OutputsInTime (b.machine input output) s (some s') t := by
  refine ⟨⟨t,?_⟩,le_rfl⟩
  have hini : Turing.initList (b.machine input output) s =
      Steps.cfg (some b.entry) (Function.update (fun _ => []) input s) := by
    simp only [Turing.initList,machine,Steps.cfg]
    congr 1
    funext k
    by_cases hk : k=input
    · subst k; rfl
    · simp [Function.update,hk]
  have hout : Turing.haltList (b.machine input output) s' =
      Steps.cfg none (Function.update (fun _ => []) output s') := by
    simp only [Turing.haltList,machine,Steps.cfg]
    congr 1
    funext k
    by_cases hk : k=output
    · subst k; rfl
    · simp [Function.update,hk]
  change (fun o => o.bind (Turing.TM2.step (fun l => (b.code l).translate)))^[t]
    (some (Turing.initList (b.machine input output) s)) =
    some (Turing.haltList (b.machine input output) s')
  rw [hini,hout]
  exact h.simulation
end Block
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
namespace Block
variable {r : ℕ}

private theorem option_map_elim {α β : Type} (f : α → β) :
    Option.map f = fun q => q.elim none (some ∘ f) := by funext q; cases q <;> rfl

theorem cases_runs_empty (k : Fin r) (e z o : Block r) {s s' : Store r} {t : ℕ}
    (hs : s k=[]) (he : e.Runs s s' t) : (cases k e z o).Runs s s' (t+1) := by
  apply Steps.next
  have h := he.map (cases k e z o).code (Sum.inr ∘ Sum.inl) none (by
    intro l
    change (e.code l).map _ = (e.code l).map _
    rw [option_map_elim]; rfl)
  simpa only [cases,Instr.eval,hs,List.head?_nil,Option.elim_none,Option.elim_some,
    Function.comp_apply] using h

theorem cases_runs_false (k : Fin r) (e z o : Block r) {s s' : Store r} {t : ℕ}
    (hs : (s k).head?=some false) (hz : z.Runs s s' t) : (cases k e z o).Runs s s' (t+1) := by
  apply Steps.next
  have h := hz.map (cases k e z o).code (Sum.inr ∘ Sum.inr ∘ Sum.inl) none (by
    intro l
    change (z.code l).map _ = (z.code l).map _
    rw [option_map_elim]; rfl)
  simpa only [cases,Instr.eval,hs,Option.elim_none,Option.elim_some,
    Function.comp_apply,Bool.false_eq_true,ite_false] using h

theorem cases_runs_true (k : Fin r) (e z o : Block r) {s s' : Store r} {t : ℕ}
    (hs : (s k).head?=some true) (ho : o.Runs s s' t) : (cases k e z o).Runs s s' (t+1) := by
  apply Steps.next
  have h := ho.map (cases k e z o).code (Sum.inr ∘ Sum.inr ∘ Sum.inr) none (by
    intro l
    change (o.code l).map _ = (o.code l).map _
    rw [option_map_elim]; rfl)
  simpa only [cases,Instr.eval,hs,Option.elim_none,Option.elim_some,
    Function.comp_apply,ite_true] using h

theorem loop_runs_empty (k : Fin r) (b : Block r) (s : Store r) (hs : s k=[]) :
    (loop k b).Runs s s 1 := by
  apply Steps.next
  simp only [loop,Instr.eval,hs,List.head?_nil,Option.elim_none]
  exact .refl _ _

theorem loop_runs_step (k : Fin r) (b : Block r) {s s' s'' : Store r} {t u : ℕ}
    (hs : s k≠[]) (hb : b.Runs s s' t) (hl : (loop k b).Runs s' s'' u) :
    (loop k b).Runs s s'' (t+u+1) := by
  apply Steps.next
  have h := hb.map (loop k b).code Sum.inr (some (Sum.inl ())) (fun _ => rfl)
  have hh := h.trans hl
  cases he : s k with
  | nil => exact (hs he).elim
  | cons a l =>
    cases a <;> simpa only [loop,Instr.eval,he,List.head?_cons,Option.elim_none,
      Option.elim_some,Function.comp_apply,Bool.false_eq_true,ite_false,ite_true] using hh

def skip : Block r := primitive (.go ())
def push (k : Fin r) (b : Bool) : Block r := primitive (.push k b ())
def pop (k : Fin r) : Block r := primitive (.pop k ())

theorem skip_runs (s : Store r) : skip.Runs s s 1 := primitive_runs _ s

theorem push_runs (k : Fin r) (b : Bool) (s : Store r) :
    (push k b).Runs s (Function.update s k (b::s k)) 1 := primitive_runs _ s

theorem pop_runs (k : Fin r) (s : Store r) :
    (pop k).Runs s (Function.update s k (s k).tail) 1 := primitive_runs _ s

def clear (k : Fin r) : Block r := loop k (pop k)

theorem clear_runs (k : Fin r) (s : Store r) :
    (clear k).Runs s (Function.update s k []) (2*(s k).length+1) := by
  generalize hl : s k=l
  induction l generalizing s with
  | nil =>
    have he : Function.update s k []=s := by rw [←hl,Function.update_eq_self]
    rw [he]
    exact loop_runs_empty k (pop k) s hl
  | cons a l ih =>
    let s' := Function.update s k l
    have hi := ih s' (by simp [s'])
    have hp : (pop k).Runs s s' 1 := by simpa [s',hl] using pop_runs k s
    have hx := loop_runs_step k (pop k) (by simp [hl]) hp hi
    have ht : 1+(2*l.length+1)+1=2*(a::l).length+1 := by simp only [List.length_cons]; omega
    rw [ht] at hx
    simpa only [clear,s',Function.update_idem] using hx

def moveBody (src dst : Fin r) : Block r :=
  cases src skip ((pop src).seq (push dst false)) ((pop src).seq (push dst true))

def reverseInto (src dst : Fin r) : Block r := loop src (moveBody src dst)

theorem moveBody_runs (src dst : Fin r) (hne : src≠dst) (s : Store r) (a : Bool) (l : List Bool)
    (hs : s src=a::l) :
    (moveBody src dst).Runs s (Function.update (Function.update s src l) dst (a::s dst)) 3 := by
  have hp : (pop src).Runs s (Function.update s src l) 1 := by
    simpa only [hs,List.tail_cons] using pop_runs src s
  have ht := push_runs dst a (Function.update s src l)
  rw [Function.update_of_ne hne.symm] at ht
  have hseq : ((pop src).seq (push dst a)).Runs s
      (Function.update (Function.update s src l) dst (a::s dst)) 2 := by
    exact seq_runs _ _ hp ht
  cases a with
  | false => exact cases_runs_false _ _ _ _ (by simp [hs]) hseq
  | true => exact cases_runs_true _ _ _ _ (by simp [hs]) hseq

theorem reverseInto_runs (src dst : Fin r) (hne : src≠dst) (s : Store r) :
    (reverseInto src dst).Runs s
      (Function.update (Function.update s src []) dst ((s src).reverse++s dst))
      (4*(s src).length+1) := by
  generalize hl : s src=l
  induction l generalizing s with
  | nil =>
    have he : Function.update (Function.update s src []) dst ([].reverse++s dst)=s := by
      rw [←hl,Function.update_eq_self]
      simp [hl]
    rw [he]
    exact loop_runs_empty src (moveBody src dst) s hl
  | cons a l ih =>
    let s' := Function.update (Function.update s src l) dst (a::s dst)
    have hs' : s' src=l := by simp [s',hne]
    have hi := ih s' hs'
    have hm := moveBody_runs src dst hne s a l hl
    have hx := loop_runs_step src (moveBody src dst) (by simp [hl]) hm hi
    have he : Function.update (Function.update s' src []) dst (l.reverse++s' dst)=
        Function.update (Function.update s src []) dst ((a::l).reverse++s dst) := by
      funext k
      by_cases hk : k=dst
      · subst k; simp [List.reverse_cons,List.append_assoc,s']
      · by_cases hks : k=src
        · subst k; simp [hne,s']
        · simp [Function.update_of_ne,hk,hks,s']
    rw [he] at hx
    have ht : 3+(4*l.length+1)+1=4*(a::l).length+1 := by simp only [List.length_cons]; omega
    rw [ht] at hx
    exact hx

end Block
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode.Block
variable {r : ℕ}

def moveTwoBody (src dst aux : Fin r) : Block r :=
  cases src skip
    ((pop src).seq ((push dst false).seq (push aux false)))
    ((pop src).seq ((push dst true).seq (push aux true)))

def reverseIntoTwo (src dst aux : Fin r) : Block r := loop src (moveTwoBody src dst aux)

lemma moveTwoBody_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) (a : Bool) (l : List Bool) (hs : s src=a::l) :
    (moveTwoBody src dst aux).Runs s
      (Function.update (Function.update (Function.update s src l) dst (a::s dst)) aux (a::s aux)) 4 := by
  have hp : (pop src).Runs s (Function.update s src l) 1 := by
    simpa only [hs,List.tail_cons] using pop_runs src s
  have hd := push_runs dst a (Function.update s src l)
  rw [Function.update_of_ne hsd.symm] at hd
  have ha := push_runs aux a (Function.update (Function.update s src l) dst (a::s dst))
  rw [Function.update_of_ne hda.symm,Function.update_of_ne hsa.symm] at ha
  have hseq : ((pop src).seq ((push dst a).seq (push aux a))).Runs s
      (Function.update (Function.update (Function.update s src l) dst (a::s dst)) aux (a::s aux)) 3 :=
    seq_runs _ _ hp (seq_runs _ _ hd ha)
  cases a with
  | false => exact cases_runs_false _ _ _ _ (by simp [hs]) hseq
  | true => exact cases_runs_true _ _ _ _ (by simp [hs]) hseq

lemma reverseIntoTwo_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) :
    (reverseIntoTwo src dst aux).Runs s
      (Function.update (Function.update (Function.update s src []) dst ((s src).reverse++s dst))
        aux ((s src).reverse++s aux)) (5*(s src).length+1) := by
  generalize hl : s src=l
  induction l generalizing s with
  | nil =>
    have he : Function.update (Function.update (Function.update s src []) dst ([].reverse++s dst))
        aux ([].reverse++s aux)=s := by
      rw [←hl,Function.update_eq_self]
      simp only [hl,List.reverse_nil,List.nil_append,Function.update_eq_self]
    rw [he]
    exact loop_runs_empty src (moveTwoBody src dst aux) s hl
  | cons a l ih =>
    let s' := Function.update (Function.update (Function.update s src l) dst (a::s dst)) aux (a::s aux)
    have hs' : s' src=l := by simp [s',hsd,hsa]
    have hi := ih s' hs'
    have hm := moveTwoBody_runs src dst aux hsd hsa hda s a l hl
    have hx := loop_runs_step src (moveTwoBody src dst aux) (by simp [hl]) hm hi
    have he : Function.update (Function.update (Function.update s' src []) dst (l.reverse++s' dst))
        aux (l.reverse++s' aux)=
        Function.update (Function.update (Function.update s src []) dst ((a::l).reverse++s dst))
          aux ((a::l).reverse++s aux) := by
      funext k
      by_cases hka : k=aux
      · subst k; simp [List.reverse_cons,List.append_assoc,s']
      · by_cases hkd : k=dst
        · subst k; simp [hda,List.reverse_cons,List.append_assoc,s']
        · by_cases hks : k=src
          · subst k; simp [hsd,hsa,s']
          · simp [Function.update_of_ne,hka,hkd,hks,s']
    rw [he] at hx
    have ht : 4+(5*l.length+1)+1=5*(a::l).length+1 := by simp only [List.length_cons]; omega
    rw [ht] at hx
    exact hx

def copy (src dst aux : Fin r) : Block r :=
  (clear dst).seq ((reverseInto src aux).seq (reverseIntoTwo aux src dst))

lemma copy_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) (ha : s aux=[]) :
    (copy src dst aux).Runs s (Function.update s dst (s src))
      (2*(s dst).length+9*(s src).length+3) := by
  let s₁ := Function.update s dst []
  let s₂ := Function.update (Function.update s₁ src []) aux ((s₁ src).reverse++s₁ aux)
  have h₁ := clear_runs dst s
  have h₂ := reverseInto_runs src aux hsa s₁
  have h₃ := reverseIntoTwo_runs aux src dst hsa.symm hda.symm hsd s₂
  have he : Function.update
      (Function.update (Function.update s₂ aux []) src ((s₂ aux).reverse++s₂ src))
        dst ((s₂ aux).reverse++s₂ dst)=Function.update s dst (s src) := by
    funext k
    by_cases hkd : k=dst
    · subst k; simp [s₂,s₁,hsd,hsa,hda,hsd.symm,hda.symm,ha]
    · by_cases hks : k=src
      · subst k; simp [s₂,s₁,hsd,hsa,hda,hsd.symm,hda.symm,ha]
      · by_cases hka : k=aux
        · subst k; simp [s₂,s₁,hsd,hsa,hda,ha,Ne.symm]
        · simp [s₂,s₁,Function.update_of_ne,hkd,hks,hka]
  rw [he] at h₃
  have hh := seq_runs (clear dst) _ h₁ (seq_runs _ _ h₂ h₃)
  change (copy src dst aux).Runs s (Function.update s dst (s src)) _ at hh
  have hlen₁ : (s₁ src).length=(s src).length := by simp [s₁,hsd]
  have hlen₂ : (s₂ aux).length=(s src).length := by simp [s₂,s₁,hsd,hda.symm,ha]
  rw [hlen₁,hlen₂] at hh
  have ht : (2*(s dst).length+1)+(4*(s src).length+1+(5*(s src).length+1))=
      2*(s dst).length+9*(s src).length+3 := by omega
  rw [ht] at hh
  exact hh

end BinaryMatching.StackCode.Block
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode

noncomputable def liftStore {r R : ℕ} (f : Fin r → Fin R) (s : Store r) (base : Store R) : Store R :=
  fun k => if h : ∃ i,f i=k then s h.choose else base k

lemma liftStore_at {r R : ℕ} (f : Fin r → Fin R) (hf : Function.Injective f)
    (s : Store r) (base : Store R) (i : Fin r) : liftStore f s base (f i)=s i := by
  classical
  unfold liftStore
  have h : ∃ j,f j=f i := ⟨i,rfl⟩
  rw [dite_eq_left h]
  rw [hf h.choose_spec]

lemma liftStore_outside {r R : ℕ} (f : Fin r → Fin R) (s : Store r) (base : Store R)
    (k : Fin R) (hk : ∀ i,f i≠k) : liftStore f s base k=base k := by
  classical
  exact dite_eq_right (by simpa only [not_exists] using hk)

lemma liftStore_update {r R : ℕ} (f : Fin r → Fin R) (hf : Function.Injective f)
    (s : Store r) (base : Store R) (i : Fin r) (v : List Bool) :
    liftStore f (Function.update s i v) base=Function.update (liftStore f s base) (f i) v := by
  classical
  funext k
  by_cases hk : ∃ j,f j=k
  · obtain ⟨j,rfl⟩ := hk
    rw [liftStore_at f hf]
    by_cases hji : j=i
    · subst j; simp
    · rw [Function.update_of_ne hji,Function.update_of_ne (fun h => hji (hf h)),liftStore_at f hf]
  · have ho : ∀ j,f j≠k := by simpa only [not_exists] using hk
    rw [liftStore_outside f _ base k ho,Function.update_of_ne (ho i).symm,
      liftStore_outside f _ base k ho]

lemma liftStore_eq {r R : ℕ} (f : Fin r → Fin R) (s : Store r) (base : Store R)
    (h : ∀ i,base (f i)=s i) : liftStore f s base=base := by
  classical
  funext k
  unfold liftStore
  split_ifs with hk
  · rw [←h, hk.choose_spec]
  · rfl

namespace Instr
variable {r R : ℕ} {L : Type}

def rename (f : Fin r → Fin R) : Instr r L → Instr R L
  | .go q => .go q
  | .push k b q => .push (f k) b q
  | .pop k q => .pop (f k) q
  | .branch k e z o => .branch (f k) e z o

lemma eval_rename (f : Fin r → Fin R) (hf : Function.Injective f) (i : Instr r L)
    (s : Store r) (base : Store R) :
    (i.rename f).eval (liftStore f s base)=((i.eval s).1,liftStore f (i.eval s).2 base) := by
  cases i with
  | go q => rfl
  | push k b q => simp only [rename,eval,liftStore_at f hf,liftStore_update f hf]
  | pop k q => simp only [rename,eval,liftStore_at f hf,liftStore_update f hf]
  | branch k e z o => simp only [rename,eval,liftStore_at f hf]
end Instr

namespace Steps
variable {r R : ℕ} {L : Type} {code : L → Instr r (Option L)}

lemma rename (f : Fin r → Fin R) (hf : Function.Injective f) (base : Store R)
    {q s q' s' t} (h : Steps code q s q' s' t) :
    Steps (fun l => (code l).rename f) q (liftStore f s base) q' (liftStore f s' base) t := by
  induction h with
  | refl => exact .refl _ _
  | next q s q' s' t h ih =>
    apply Steps.next
    simpa only [Instr.eval_rename f hf] using ih
end Steps

namespace Block
variable {r R : ℕ}

def rename (b : Block r) (f : Fin r → Fin R) : Block R where
  Label := b.Label
  finite := b.finite
  entry := b.entry
  code l := (b.code l).rename f

lemma rename_runs (b : Block r) (f : Fin r → Fin R) (hf : Function.Injective f)
    (base : Store R) {s s' : Store r} {t : ℕ} (h : b.Runs s s' t) :
    (b.rename f).Runs (liftStore f s base) (liftStore f s' base) t := h.rename f hf base

end Block
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Finset Polynomial

lemma polynomial_eval_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  simp only [Polynomial.eval_eq_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i)

def volume {r : ℕ} (s : Store r) : ℕ := ∑ i,(s i).length

lemma volume_update {r : ℕ} (s : Store r) (k : Fin r) (v : List Bool) :
    volume (Function.update s k v)+(s k).length=volume s+v.length := by
  classical
  simp only [volume]
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ k),
    ←Finset.sum_erase_add (Finset.univ) (fun i => (s i).length) (Finset.mem_univ k)]
  simp only [Function.update_self]
  have he : ∑ i∈Finset.univ.erase k,(Function.update s k v i).length =
      ∑ i∈Finset.univ.erase k,(s i).length := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [he]
  omega

lemma volume_instruction {r : ℕ} {L : Type} (i : Instr r L) (s : Store r) :
    volume (i.eval s).2≤volume s+1 := by
  cases i with
  | go q => exact Nat.le_succ _
  | push k b q =>
    have h := volume_update s k (b::s k)
    simp only [Instr.eval,List.length_cons] at *
    omega
  | pop k q =>
    have h := volume_update s k (s k).tail
    have hh : (s k).tail.length≤(s k).length := by simp
    simp only [Instr.eval] at *
    omega
  | branch k e z o => exact Nat.le_succ _

lemma Steps.volume_bound {r : ℕ} {L : Type} {code : L → Instr r (Option L)}
    {q s q' s' t} (h : Steps code q s q' s' t) : volume s'≤volume s+t := by
  induction h with
  | refl => exact le_rfl
  | next q s q' s' t h ih =>
    have he := volume_instruction (code q) s
    omega

lemma volume_single {r : ℕ} (k : Fin r) (s : List Bool) :
    volume (Function.update (fun _ => []) k s)=s.length := by
  classical
  unfold volume
  rw [Finset.sum_eq_single k]
  · simp
  · intro i hi hik
    simp [Function.update_of_ne hik]
  · simp

structure Routine {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) where
  scratch : ℕ
  block : Block (scratch+1)
  time : Polynomial ℕ
  correct : ∀ a, ∃ t≤time.eval (ea a).length,
    block.Runs (Function.update (fun _ => []) 0 (ea a))
      (Function.update (fun _ => []) 0 (eb (f a))) t

namespace Routine
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
  {ec : γ → List Bool} {f : α → β} {g : β → γ}

lemma length_bound (p : Routine ea eb f) (a : α) :
    (eb (f a)).length≤(ea a).length+p.time.eval (ea a).length := by
  obtain ⟨t,ht,h⟩ := p.correct a
  have hv := h.volume_bound
  simp only [volume_single] at hv
  omega

private def embedding (r s : ℕ) : Fin (r+1) → Fin (r+s+1) :=
  Fin.castLE (by omega)

private lemma embedding_injective (r s : ℕ) : Function.Injective (embedding r s) := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Fin (r+s+1) => x.val) h)

private lemma embedding_zero (r s : ℕ) : embedding r s 0=0 := rfl

lemma lift_initial {r R : ℕ} (hR : 0<R) (f : Fin (r+1) → Fin R) (hf : Function.Injective f)
    (hz : f 0=⟨0,hR⟩) (v : List Bool) :
    liftStore f (Function.update (fun _ => []) 0 v) (fun _ => [])=
      Function.update (fun _ => []) ⟨0,hR⟩ v := by
  rw [liftStore_update f hf,hz]
  congr 1
  exact liftStore_eq f _ _ (fun _ => rfl)

noncomputable def comp (p : Routine ea eb f) (q : Routine eb ec g) : Routine ea ec (g ∘ f) where
  scratch := p.scratch+q.scratch
  block := (p.block.rename (embedding p.scratch q.scratch)).seq
    (q.block.rename (fun i => ⟨i.val,by have := i.isLt; omega⟩))
  time := p.time+q.time.comp (X+p.time)
  correct a := by
    obtain ⟨t,ht,hp⟩ := p.correct a
    obtain ⟨u,hu,hq⟩ := q.correct (f a)
    let f₁ := embedding p.scratch q.scratch
    let f₂ : Fin (q.scratch+1) → Fin (p.scratch+q.scratch+1) :=
      fun i => ⟨i.val,by have := i.isLt; omega⟩
    have hf₁ : Function.Injective f₁ := embedding_injective _ _
    have hf₂ : Function.Injective f₂ := by
      intro i j h
      exact Fin.ext (congrArg (fun x : Fin (p.scratch+q.scratch+1) => x.val) h)
    have hm₁ := p.block.rename_runs f₁ hf₁ (fun _ => []) hp
    have hm₂ := q.block.rename_runs f₂ hf₂ (fun _ => []) hq
    rw [lift_initial (by omega) f₁ hf₁ rfl,lift_initial (by omega) f₁ hf₁ rfl] at hm₁
    rw [lift_initial (by omega) f₂ hf₂ rfl,lift_initial (by omega) f₂ hf₂ rfl] at hm₂
    refine ⟨t+u,?_,Block.seq_runs _ _ hm₁ hm₂⟩
    simp only [Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_X]
    exact Nat.add_le_add ht (hu.trans (polynomial_eval_mono q.time (p.length_bound a)))

noncomputable def machine (p : Routine ea eb f) : Turing.TM2ComputableInPolyTime ea eb f where
  tm := p.block.machine 0 0
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := p.time
  outputsFun a := by
    let t := (p.correct a).choose
    have ht := (p.correct a).choose_spec.1
    have h := (p.correct a).choose_spec.2
    have hm := p.block.machine_runs 0 0 (ea a) (eb (f a)) h
    change Turing.TM2OutputsInTime (p.block.machine 0 0) (List.map id (ea a))
      (some (List.map id (eb (f a)))) (p.time.eval (ea a).length)
    rw [List.map_id_fun,List.map_id_fun]
    exact ⟨hm.toEvalsTo,hm.steps_le_m.trans ht⟩

lemma machine_alphabets_finite (p : Routine ea eb f) (k : p.machine.tm.K) :
    Finite (p.machine.tm.Γ k) := by
  change Finite Bool
  infer_instance

end Routine
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode

def pairBits : List Bool → List Bool → List Bool
  | [],y => true::y
  | b::x,y => false::b::pairBits x y

@[simp] lemma pairBits_length (x y : List Bool) : (pairBits x y).length=2*x.length+y.length+1 := by
  induction x with
  | nil => simp [pairBits]
  | cons b x ih => simp only [pairBits,List.length_cons,ih]; omega

namespace Block
variable {r : ℕ}

def tagBody (src dst : Fin r) : Block r :=
  cases src skip ((pop src).seq ((push dst false).seq (push dst false)))
    ((pop src).seq ((push dst true).seq (push dst false)))

def tagAll (src dst : Fin r) : Block r := loop src (tagBody src dst)

lemma tagBody_runs (src dst : Fin r) (hne : src≠dst) (s : Store r) (b : Bool) (l : List Bool)
    (hs : s src=b::l) :
    (tagBody src dst).Runs s (Function.update (Function.update s src l) dst (false::b::s dst)) 4 := by
  have hp : (pop src).Runs s (Function.update s src l) 1 := by
    simpa only [hs,List.tail_cons] using pop_runs src s
  have hb := push_runs dst b (Function.update s src l)
  rw [Function.update_of_ne hne.symm] at hb
  have hf := push_runs dst false (Function.update (Function.update s src l) dst (b::s dst))
  simp only [Function.update_self,Function.update_idem] at hf
  have hx := seq_runs _ _ hp (seq_runs _ _ hb hf)
  cases b with
  | false => exact cases_runs_false _ _ _ _ (by simp [hs]) hx
  | true => exact cases_runs_true _ _ _ _ (by simp [hs]) hx

lemma pairBits_eq (x y : List Bool) :
    pairBits x y=x.flatMap (fun b => [false,b])++true::y := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [pairBits,ih]

lemma tagAll_runs (src dst : Fin r) (hne : src≠dst) (x y : List Bool) (s : Store r)
    (hs : s src=x.reverse) (hd : s dst=y) :
    (tagAll src dst).Runs s
      (Function.update (Function.update s src []) dst (x.flatMap (fun b => [false,b])++y))
      (5*x.length+1) := by
  induction x using List.reverseRecOn generalizing y s with
  | nil =>
    have he : Function.update (Function.update s src []) dst
        ([].flatMap (fun b => [false,b])++y)=s := by
      simp only [List.reverse_nil] at hs
      simp only [List.flatMap_nil,List.nil_append]
      rw [←hs,Function.update_eq_self,←hd,Function.update_eq_self]
    rw [he]
    apply loop_runs_empty
    simpa using hs
  | append_singleton x b ih =>
    have hs' : s src=b::x.reverse := by simpa using hs
    let s' := Function.update (Function.update s src x.reverse) dst (false::b::s dst)
    have hm := tagBody_runs src dst hne s b x.reverse hs'
    have hi := ih (false::b::y) s' (by simp [s',hne]) (by simp [s',hd])
    have hx := loop_runs_step src (tagBody src dst) (by simp [hs']) hm hi
    have he : Function.update (Function.update s' src []) dst
        (x.flatMap (fun b => [false,b])++false::b::y)=
        Function.update (Function.update s src []) dst
          ((x++[b]).flatMap (fun b => [false,b])++y) := by
      funext k
      by_cases hk : k=dst
      · subst k; simp [List.flatMap_append,List.append_assoc]
      · by_cases hks : k=src
        · subst k; simp [s',hne]
        · simp [s',Function.update_of_ne,hk,hks]
    rw [he] at hx
    have ht : 4+(5*x.length+1)+1=5*(x++[b]).length+1 := by simp; omega
    rw [ht] at hx
    exact hx

def pairInto (src dst aux : Fin r) : Block r :=
  (reverseInto src aux).seq ((push dst true).seq (tagAll aux dst))

lemma pairInto_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) (ha : s aux=[]) :
    (pairInto src dst aux).Runs s
      (Function.update (Function.update s src []) dst (pairBits (s src) (s dst)))
      (9*(s src).length+3) := by
  let s₁ := Function.update (Function.update s src []) aux ((s src).reverse++s aux)
  let s₂ := Function.update s₁ dst (true::s₁ dst)
  have h₁ := reverseInto_runs src aux hsa s
  have h₂ := push_runs dst true s₁
  have h₃ := tagAll_runs aux dst hda.symm (s src) (true::s dst) s₂
    (by simp [s₂,s₁,hda.symm,ha]) (by simp [s₂,s₁,hda,hsd.symm])
  rw [←pairBits_eq] at h₃
  have he : Function.update (Function.update s₂ aux []) dst (pairBits (s src) (s dst))=
      Function.update (Function.update s src []) dst (pairBits (s src) (s dst)) := by
    funext k
    by_cases hkd : k=dst
    · subst k; simp
    · by_cases hks : k=src
      · subst k; simp [s₂,s₁,hsd,hsa]
      · by_cases hka : k=aux
        · subst k; simp [s₂,s₁,ha,hda.symm,hsa.symm]
        · simp [s₂,s₁,Function.update_of_ne,hkd,hks,hka]
  rw [he] at h₃
  have hx := seq_runs _ _ h₁ (seq_runs _ _ h₂ h₃)
  have ht : (4*(s src).length+1)+(1+(5*(s src).length+1))=9*(s src).length+3 := by omega
  rw [ht] at hx
  exact hx

def moveInto (src dst aux : Fin r) : Block r :=
  (reverseInto src aux).seq (reverseInto aux dst)

lemma moveInto_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) (hd : s dst=[]) (ha : s aux=[]) :
    (moveInto src dst aux).Runs s
      (Function.update (Function.update s src []) dst (s src)) (8*(s src).length+2) := by
  let s' := Function.update (Function.update s src []) aux ((s src).reverse++s aux)
  have h₁ := reverseInto_runs src aux hsa s
  have h₂ := reverseInto_runs aux dst hda.symm s'
  have he : Function.update (Function.update s' aux []) dst ((s' aux).reverse++s' dst)=
      Function.update (Function.update s src []) dst (s src) := by
    funext k
    by_cases hkd : k=dst
    · subst k; simp [s',ha,hd,hda,hsd.symm]
    · by_cases hks : k=src
      · subst k; simp [s',hsd,hsa]
      · by_cases hka : k=aux
        · subst k; simp [ha,hda.symm,hsa.symm]
        · simp [s',Function.update_of_ne,hkd,hks,hka]
  rw [he] at h₂
  have hh := seq_runs _ _ h₁ h₂
  have hl : (s' aux).length=(s src).length := by simp [s',ha]
  rw [hl] at hh
  have ht : (4*(s src).length+1)+(4*(s src).length+1)=8*(s src).length+2 := by omega
  rw [ht] at hh
  exact hh

def decodeRev (src dst : Fin r) : Block r where
  Label := Fin 7
  finite := inferInstance
  entry := 0
  code k := match k.val with
    | 0 => .branch src none (some 1) (some 6)
    | 1 => .pop src (some 2)
    | 2 => .branch src none (some 3) (some 4)
    | 3 => .push dst false (some 5)
    | 4 => .push dst true (some 5)
    | 5 => .pop src (some 0)
    | _ => .pop src none

lemma decodeRev_runs (src dst : Fin r) (hne : src≠dst) (x y : List Bool) (s : Store r)
    (hs : s src=pairBits x y) :
    (decodeRev src dst).Runs s
      (Function.update (Function.update s src y) dst (x.reverse++s dst)) (5*x.length+2) := by
  induction x generalizing s with
  | nil =>
    have hx : s src=true::y := hs
    have he : Function.update (Function.update s src y) dst ([].reverse++s dst)=
        Function.update s src y := by
      simp only [List.reverse_nil,List.nil_append]
      rw [←Function.update_of_ne hne.symm y s,Function.update_eq_self]
    rw [he]
    apply Steps.next
    simp [decodeRev,Instr.eval,hx]
    apply Steps.next
    simp [Instr.eval,hx]
    exact .refl _ _
  | cons b x ih =>
    let s' := Function.update (Function.update s dst (b::s dst)) src (pairBits x y)
    have hs' : s' src=pairBits x y := by simp [s']
    have hi := ih s' hs'
    have he : Function.update (Function.update s' src y) dst (x.reverse++s' dst)=
        Function.update (Function.update s src y) dst ((b::x).reverse++s dst) := by
      funext k
      by_cases hkd : k=dst
      · subst k; simp [s',hne.symm,List.reverse_cons,List.append_assoc]
      · by_cases hks : k=src
        · subst k; simp [s',hne]
        · simp [s',Function.update_of_ne,hkd,hks]
    rw [he] at hi
    have ht : 5*(b::x).length+2=(5*x.length+2)+1+1+1+1+1 := by simp; omega
    rw [ht]
    apply Steps.next
    simp [decodeRev,Instr.eval,hs,pairBits]
    apply Steps.next
    simp [Instr.eval,hs,pairBits]
    cases b <;>
      (apply Steps.next
       simp [Instr.eval]
       apply Steps.next
       simp [Instr.eval,hne.symm]
       apply Steps.next
       simp [Instr.eval,hne]
       convert hi using 1; simp [s',Function.update_comm hne,Function.update_idem,Block.Runs,decodeRev])

end Block
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode

lemma lift_clean {r R : ℕ} (f : Fin (r+1) → Fin R) (hf : Function.Injective f)
    (s : Store R) (hs : ∀ i : Fin (r+1), i≠0 → s (f i)=[]) (v : List Bool) :
    liftStore f (Function.update (fun _ => []) 0 v) s=Function.update s (f 0) v := by
  classical
  funext k
  by_cases hk : ∃ i,f i=k
  · obtain ⟨i,rfl⟩ := hk
    rw [liftStore_at f hf]
    by_cases hi : i=0
    · subst i; simp
    · rw [Function.update_of_ne hi,Function.update_of_ne (fun h => hi (hf h)),hs i hi]
  · rw [liftStore_outside f _ _ k (by simpa only [not_exists] using hk),
      Function.update_of_ne (fun h => hk ⟨0,h.symm⟩)]

namespace Routine
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

lemma run_at (p : Routine ea eb f) {R : ℕ} (ι : Fin (p.scratch+1) → Fin R)
    (hι : Function.Injective ι) (s : Store R) (a : α)
    (hinput : s (ι 0)=ea a) (hclean : ∀ i, i≠0 → s (ι i)=[]) :
    ∃ t ≤ p.time.eval (ea a).length,
      (p.block.rename ι).Runs s (Function.update s (ι 0) (eb (f a))) t := by
  obtain ⟨t,ht,h⟩ := p.correct a
  have hh := p.block.rename_runs ι hι s h
  rw [lift_clean ι hι s hclean,lift_clean ι hι s hclean,
    ←hinput,Function.update_eq_self] at hh
  exact ⟨t,ht,hh⟩

noncomputable def reindex {α' β' : Type} (p : Routine ea eb f) (ea' : α' → List Bool)
    (eb' : β' → List Bool) (f' : α' → β') (u : α' → α)
    (hin : ∀ a,ea (u a)=ea' a) (hout : ∀ a,eb (f (u a))=eb' (f' a)) :
    Routine ea' eb' f' where
  scratch := p.scratch
  block := p.block
  time := p.time
  correct a := by simpa only [hin,hout] using p.correct (u a)

noncomputable def identity (ea : α → List Bool) : Routine ea ea id where
  scratch := 0
  block := Block.skip
  time := 1
  correct a := ⟨1,by simp,Block.skip_runs _⟩

end Routine
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

namespace PairRegisters

def left (p q : ℕ) (i : Fin (p+1)) : Fin (p+q+3) := ⟨i.val,by have := i.isLt; omega⟩
def right (p q : ℕ) (i : Fin (q+1)) : Fin (p+q+3) := ⟨p+1+i.val,by have := i.isLt; omega⟩
def aux (p q : ℕ) : Fin (p+q+3) := ⟨p+q+2,by omega⟩

@[simp] lemma left_zero (p q : ℕ) : left p q 0=0 := rfl
lemma left_inj (p q : ℕ) : Function.Injective (left p q) := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin (p+q+3) => k.val) h)
lemma right_inj (p q : ℕ) : Function.Injective (right p q) := by
  intro i j h
  have hh := congrArg (fun k : Fin (p+q+3) => k.val) h
  simp only [right] at hh
  exact Fin.ext (by omega)
@[simp] lemma left_ne_right (p q : ℕ) (i : Fin (p+1)) (j : Fin (q+1)) : left p q i≠right p q j := by
  intro h
  have hh := congrArg (fun k : Fin (p+q+3) => k.val) h
  simp only [left,right] at hh
  have := i.isLt
  omega
@[simp] lemma left_ne_aux (p q : ℕ) (i : Fin (p+1)) : left p q i≠aux p q := by
  intro h
  have hh := congrArg (fun k : Fin (p+q+3) => k.val) h
  simp only [left,aux] at hh
  have := i.isLt
  omega
@[simp] lemma right_ne_aux (p q : ℕ) (i : Fin (q+1)) : right p q i≠aux p q := by
  intro h
  have hh := congrArg (fun k : Fin (p+q+3) => k.val) h
  simp only [right,aux] at hh
  have := i.isLt
  omega
@[simp] lemma zero_ne_right (p q : ℕ) (j : Fin (q+1)) : (0:Fin (p+q+3))≠right p q j :=
  left_ne_right p q 0 j
@[simp] lemma zero_ne_aux (p q : ℕ) : (0:Fin (p+q+3))≠aux p q := left_ne_aux p q 0

end PairRegisters

namespace Routine
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
  {ec : γ → List Bool} {f : α → β} {g : α → γ}

noncomputable def pair (p : Routine ea eb f) (q : Routine ea ec g) :
    Routine ea (fun z : β×γ => pairBits (eb z.1) (ec z.2)) (fun a => (f a,g a)) where
  scratch := p.scratch+q.scratch+2
  block :=
    let fst := (0:Fin (p.scratch+q.scratch+3))
    let snd := PairRegisters.right p.scratch q.scratch 0
    let aux := PairRegisters.aux p.scratch q.scratch
    (Block.copy fst snd aux).seq
      ((p.block.rename (PairRegisters.left p.scratch q.scratch)).seq
        ((q.block.rename (PairRegisters.right p.scratch q.scratch)).seq
          ((Block.pairInto fst snd aux).seq (Block.moveInto snd fst aux))))
  time := 100*(X+p.time+q.time+1)
  correct a := by
    let R := p.scratch+q.scratch+3
    let d := PairRegisters.right p.scratch q.scratch 0
    let aux := PairRegisters.aux p.scratch q.scratch
    have h0d : (0:Fin R)≠d := PairRegisters.zero_ne_right _ _ _
    have h0a : (0:Fin R)≠aux := PairRegisters.zero_ne_aux _ _
    have hda : d≠aux := PairRegisters.right_ne_aux _ _ _
    let s₀ : Store R := Function.update (fun _ => []) 0 (ea a)
    let s₁ := Function.update s₀ d (ea a)
    let s₂ := Function.update s₁ 0 (eb (f a))
    let s₃ := Function.update s₂ d (ec (g a))
    let s₄ := Function.update (Function.update s₃ 0 []) d (pairBits (eb (f a)) (ec (g a)))
    have hc : (Block.copy 0 d aux).Runs s₀ s₁ (9*(ea a).length+3) := by
      simpa [s₀,s₁,h0d.symm] using Block.copy_runs 0 d aux h0d h0a hda s₀
        (by simp [s₀,h0a.symm])
    obtain ⟨t,ht,hp⟩ := p.run_at (PairRegisters.left p.scratch q.scratch)
      (PairRegisters.left_inj _ _) s₁ a (by simp [s₁,s₀,h0d]) (by
        intro i hi
        have hne : PairRegisters.left p.scratch q.scratch i≠0 := by
          simpa only [←PairRegisters.left_zero p.scratch q.scratch] using
            (fun h => hi (PairRegisters.left_inj _ _ h))
        simp [s₁,s₀,d,PairRegisters.left_ne_right,hne])
    obtain ⟨u,hu,hq⟩ := q.run_at (PairRegisters.right p.scratch q.scratch)
      (PairRegisters.right_inj _ _) s₂ a (by
        change s₂ d=ea a
        simp [s₂,s₁,h0d.symm]) (by
        intro i hi
        have hne : PairRegisters.right p.scratch q.scratch i≠d :=
          fun h => hi (PairRegisters.right_inj _ _ h)
        have hn0 : PairRegisters.right p.scratch q.scratch i≠0 :=
          (PairRegisters.zero_ne_right _ _ _).symm
        simp [s₂,s₁,s₀,Function.update_of_ne,hne,hn0])
    change (p.block.rename (PairRegisters.left _ _)).Runs s₁ s₂ t at hp
    change (q.block.rename (PairRegisters.right _ _)).Runs s₂ s₃ u at hq
    have h₃ : (Block.pairInto 0 d aux).Runs s₃ s₄ (9*(eb (f a)).length+3) := by
      simpa [s₄,s₃,s₂,h0d] using Block.pairInto_runs 0 d aux h0d h0a hda s₃
        (by simp [s₃,s₂,s₁,s₀,h0a.symm,hda.symm])
    have h₄ := Block.moveInto_runs d 0 aux h0d.symm hda h0a s₄
      (by simp [s₄,h0d]) (by simp [s₄,s₃,s₂,s₁,s₀,h0a.symm,hda.symm])
    have hf : Function.update (Function.update s₄ d []) 0 (s₄ d)=
        Function.update (fun _ => []) 0 (pairBits (eb (f a)) (ec (g a))) := by
      funext k
      by_cases hk : k=0
      · subst k; simp [s₄]
      · by_cases hkd : k=d
        · subst k; simp [h0d.symm]
        · simp [s₄,s₃,s₂,s₁,s₀,Function.update_of_ne,hk,hkd]
    rw [hf] at h₄
    have hlen : (s₄ d).length=(pairBits (eb (f a)) (ec (g a))).length := by simp [s₄]
    rw [hlen] at h₄
    have hrun := Block.seq_runs _ _ hc (Block.seq_runs _ _ hp
      (Block.seq_runs _ _ hq (Block.seq_runs _ _ h₃ h₄)))
    refine ⟨_,?_,hrun⟩
    simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one,pairBits_length]
    have hf := p.length_bound a
    have hg := q.length_bound a
    omega

end Routine
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Routine
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool)

noncomputable def first :
    Routine (fun z : α×β => pairBits (ea z.1) (eb z.2)) ea Prod.fst where
  scratch := 1
  block := (Block.decodeRev 0 1).seq ((Block.clear 0).seq (Block.reverseInto 1 0))
  time := 10*X+10
  correct a := by
    let s₀ : Store 2 := Function.update (fun _ => []) 0 (pairBits (ea a.1) (eb a.2))
    let s₁ := Function.update (Function.update s₀ 0 (eb a.2)) 1 (ea a.1).reverse
    let s₂ := Function.update s₁ 0 []
    have h₁ : (Block.decodeRev 0 1).Runs s₀ s₁ (5*(ea a.1).length+2) := by
      simpa [s₁,s₀] using Block.decodeRev_runs (0:Fin 2) 1 (by decide) (ea a.1) (eb a.2)
        s₀ (by simp [s₀])
    have h₂ : (Block.clear 0).Runs s₁ s₂ (2*(eb a.2).length+1) := by
      simpa [s₁] using Block.clear_runs (0:Fin 2) s₁
    have h₃ := Block.reverseInto_runs (1:Fin 2) 0 (by decide) s₂
    have he : Function.update (Function.update s₂ 1 []) 0 ((s₂ 1).reverse++s₂ 0)=
        Function.update (fun _ => []) 0 (ea a.1) := by
      funext k
      fin_cases k <;> simp [s₂,s₁,s₀]
    rw [he] at h₃
    have hl : (s₂ 1).length=(ea a.1).length := by simp [s₂,s₁]
    rw [hl] at h₃
    refine ⟨_,?_,Block.seq_runs _ _ h₁ (Block.seq_runs _ _ h₂ h₃)⟩
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,pairBits_length]
    omega

noncomputable def second :
    Routine (fun z : α×β => pairBits (ea z.1) (eb z.2)) eb Prod.snd where
  scratch := 1
  block := (Block.decodeRev 0 1).seq (Block.clear 1)
  time := 10*X+10
  correct a := by
    let s₀ : Store 2 := Function.update (fun _ => []) 0 (pairBits (ea a.1) (eb a.2))
    let s₁ := Function.update (Function.update s₀ 0 (eb a.2)) 1 (ea a.1).reverse
    have h₁ : (Block.decodeRev 0 1).Runs s₀ s₁ (5*(ea a.1).length+2) := by
      simpa [s₁,s₀] using Block.decodeRev_runs (0:Fin 2) 1 (by decide) (ea a.1) (eb a.2)
        s₀ (by simp [s₀])
    have h₂ := Block.clear_runs (1:Fin 2) s₁
    have he : Function.update s₁ 1 []=Function.update (fun _ => []) 0 (eb a.2) := by
      funext k
      fin_cases k <;> simp [s₁,s₀]
    rw [he] at h₂
    have hl : (s₁ 1).length=(ea a.1).length := by simp [s₁]
    rw [hl] at h₂
    refine ⟨_,?_,Block.seq_runs _ _ h₁ h₂⟩
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,pairBits_length]
    omega

end Routine
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Block
variable {r : ℕ}
def dropTwo (k : Fin r) : Block r := (pop k).seq (pop k)
lemma dropTwo_runs (k : Fin r) (s : Store r) (a b : Bool) (l : List Bool)
    (hs : s k=a::b::l) :
    (dropTwo k).Runs s (Function.update s k l) 2 := by
  have h₁ := pop_runs k s
  have h₂ := pop_runs k (Function.update s k (s k).tail)
  have h := seq_runs _ _ h₁ h₂
  simpa [dropTwo,hs,Function.update_idem] using h

def emit (k : Fin r) : List Bool → Block r
  | [] => skip
  | b::l => (emit k l).seq (push k b)
lemma emit_runs (k : Fin r) (x : List Bool) (s : Store r) :
    (emit k x).Runs s (Function.update s k (x++s k)) (x.length+1) := by
  induction x with
  | nil => simpa [emit] using skip_runs s
  | cons b x ih =>
    have h := seq_runs _ _ ih (push_runs k b (Function.update s k (x++s k)))
    simpa [emit,Function.update_idem,Nat.add_assoc] using h
end Block
namespace Routine
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
  {f g : α → β}

noncomputable def constant (ea : α → List Bool) (eb : β → List Bool) (b : β) :
    Routine ea eb (fun _ => b) where
  scratch := 0
  block := (Block.clear 0).seq (Block.emit 0 (eb b))
  time := 2*X+C ((eb b).length+2)
  correct a := by
    have h := Block.seq_runs _ _ (Block.clear_runs (0:Fin 1)
      (Function.update (fun _ => []) 0 (ea a)))
      (Block.emit_runs (0:Fin 1) (eb b)
        (Function.update (Function.update (fun _ => []) 0 (ea a)) 0 []))
    refine ⟨2*(ea a).length+1+((eb b).length+1),?_,?_⟩
    · simpa only [eval_add,eval_mul,eval_ofNat,eval_X,eval_C,Function.update_self]
        using (show 2*(ea a).length+1+((eb b).length+1)≤2*(ea a).length+((eb b).length+2) by omega)
    · simpa only [Function.update_idem,Function.update_self,List.append_nil] using h

noncomputable def select (p : Routine ea eb f) (q : Routine ea eb g) :
    Routine (fun z : Bool×α => pairBits [z.1] (ea z.2)) eb
      (fun z => if z.1 then g z.2 else f z.2) where
  scratch := p.scratch+q.scratch
  block :=
    let ι : Fin (p.scratch+1) → Fin (p.scratch+q.scratch+1) :=
      fun i => ⟨i.val,by have := i.isLt; omega⟩
    let κ : Fin (q.scratch+1) → Fin (p.scratch+q.scratch+1) :=
      fun i => ⟨i.val,by have := i.isLt; omega⟩
    (Block.pop 0).seq (Block.cases 0 Block.skip
      ((Block.dropTwo 0).seq (p.block.rename ι))
      ((Block.dropTwo 0).seq (q.block.rename κ)))
  time := p.time+q.time+4
  correct z := by
    let R := p.scratch+q.scratch+1
    let ι : Fin (p.scratch+1) → Fin R := fun i => ⟨i.val,by have := i.isLt; omega⟩
    let κ : Fin (q.scratch+1) → Fin R := fun i => ⟨i.val,by have := i.isLt; omega⟩
    have hι : Function.Injective ι := fun i j h => Fin.ext (congrArg (fun k : Fin R => k.val) h)
    have hκ : Function.Injective κ := fun i j h => Fin.ext (congrArg (fun k : Fin R => k.val) h)
    let s₀ : Store R := Function.update (fun _ => []) 0 (pairBits [z.1] (ea z.2))
    let s₁ : Store R := Function.update (fun _ => []) 0 (z.1::true::ea z.2)
    let s₂ : Store R := Function.update (fun _ => []) 0 (ea z.2)
    have hp : (Block.pop 0).Runs s₀ s₁ 1 := by
      simpa [s₀,s₁,pairBits,Function.update_idem] using Block.pop_runs (0:Fin R) s₀
    have hd : (Block.dropTwo 0).Runs s₁ s₂ 2 := by
      simpa [s₁,s₂,Function.update_idem] using Block.dropTwo_runs (0:Fin R) s₁ z.1 true
        (ea z.2) (by simp [s₁])
    have hp₀ := p.run_at ι hι s₂ z.2 (by simp [s₂,ι]) (by
      intro i hi
      have hk : ι i≠0 := fun h => hi (hι h)
      simp [s₂,Function.update_of_ne hk])
    have hq₀ := q.run_at κ hκ s₂ z.2 (by simp [s₂,κ]) (by
      intro i hi
      have hk : κ i≠0 := fun h => hi (hκ h)
      simp [s₂,Function.update_of_ne hk])
    have hlen : (ea z.2).length≤(pairBits [z.1] (ea z.2)).length := by
      simp only [pairBits_length,List.length_singleton]
      omega
    have ht₁ := polynomial_eval_mono p.time hlen
    have ht₂ := polynomial_eval_mono q.time hlen
    rcases z with ⟨b,a⟩
    cases b with
    | false =>
      obtain ⟨t,ht,hr⟩ := hp₀
      have hx := Block.cases_runs_false (0:Fin R) Block.skip
        ((Block.dropTwo 0).seq (p.block.rename ι)) ((Block.dropTwo 0).seq (q.block.rename κ))
        (by simp [s₁]) (Block.seq_runs _ _ hd hr)
      refine ⟨1+(2+t+1),?_,?_⟩
      · simp only [eval_add,eval_ofNat]
        dsimp only at ht₁ ht₂ ht
        omega
      · simpa [s₂,ι,Function.update_idem] using Block.seq_runs _ _ hp hx
    | true =>
      obtain ⟨t,ht,hr⟩ := hq₀
      have hx := Block.cases_runs_true (0:Fin R) Block.skip
        ((Block.dropTwo 0).seq (p.block.rename ι)) ((Block.dropTwo 0).seq (q.block.rename κ))
        (by simp [s₁]) (Block.seq_runs _ _ hd hr)
      refine ⟨1+(2+t+1),?_,?_⟩
      · simp only [eval_add,eval_ofNat]
        dsimp only at ht₁ ht₂ ht
        omega
      · simpa [s₂,κ,Function.update_idem] using Block.seq_runs _ _ hp hx

end Routine
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

def unary (n : ℕ) : List Bool := List.replicate n true
@[simp] lemma unary_length (n : ℕ) : (unary n).length=n := by simp [unary]
@[simp] lemma unary_reverse (n : ℕ) : (unary n).reverse=unary n := by simp [unary]
@[simp] lemma unary_zero : unary 0=[] := rfl
@[simp] lemma unary_succ (n : ℕ) : unary (n+1)=true::unary n := by simp [unary,List.replicate_succ]

namespace Routine
variable {α : Type} {ea : α → List Bool} {f : α → α}

lemma iterate_runs_at (p : Routine ea ea f) {R : ℕ}
    (ι : Fin (p.scratch+1) → Fin R) (hι : Function.Injective ι)
    (counter : Fin R) (hc : ∀ i,ι i≠counter) (B n : ℕ) (a : α) (s : Store R)
    (hin : s (ι 0)=ea a) (hclean : ∀ i,i≠0 → s (ι i)=[]) (hcount : s counter=unary n)
    (hb : ∀ j≤n,(ea (f^[j] a)).length≤B) :
    ∃ t≤n*(p.time.eval B+2)+1,
      (Block.loop counter ((Block.pop counter).seq (p.block.rename ι))).Runs s
        (Function.update (Function.update s counter []) (ι 0) (ea (f^[n] a))) t := by
  induction n generalizing a s with
  | zero =>
    have he : Function.update (Function.update s counter []) (ι 0) (ea (f^[0] a))=s := by
      simp only [Function.iterate_zero, id_eq]
      have hc0 : s counter=[] := hcount
      rw [←hin,←hc0,Function.update_eq_self,Function.update_eq_self]
    rw [he]
    exact ⟨1,by simp,Block.loop_runs_empty _ _ _ (by simpa using hcount)⟩
  | succ n ih =>
    let s₁ := Function.update s counter (unary n)
    let s₂ := Function.update s₁ (ι 0) (ea (f a))
    have hp : (Block.pop counter).Runs s s₁ 1 := by
      simpa [s₁,hcount] using Block.pop_runs counter s
    obtain ⟨t,ht,hp₀⟩ := p.run_at ι hι s₁ a (by simpa [s₁,hc] using hin) (by
      intro i hi
      simpa [s₁,hc] using hclean i hi)
    change (p.block.rename ι).Runs s₁ s₂ t at hp₀
    obtain ⟨u,hu,hi⟩ := ih (f a) s₂ (by simp [s₂]) (by
      intro i hi
      have hne : ι i≠ι 0 := fun h => hi (hι h)
      simp [s₂,s₁,Function.update_of_ne hne,hc,hclean i hi])
      (by simp [s₂,s₁,(hc 0).symm]) (by
        intro j hj
        simpa only [Function.iterate_succ_apply] using hb (j+1) (by omega))
    have he : Function.update (Function.update s₂ counter []) (ι 0) (ea (f^[n] (f a)))=
        Function.update (Function.update s counter []) (ι 0) (ea (f^[n+1] a)) := by
      funext k
      by_cases hk : k=ι 0
      · subst k; simp [Function.iterate_succ_apply]
      · by_cases hkc : k=counter
        · subst k; simp [(hc 0).symm]
        · simp [s₂,s₁,Function.update_of_ne,hk,hkc]
    rw [he] at hi
    have hh := Block.loop_runs_step counter ((Block.pop counter).seq (p.block.rename ι))
      (by simp [hcount]) (Block.seq_runs _ _ hp hp₀) hi
    refine ⟨_,?_,hh⟩
    have ht' : t≤p.time.eval B := ht.trans (polynomial_eval_mono p.time (by simpa using hb 0 (by omega)))
    nlinarith

noncomputable def boundedIterate {δ : Type} (p : Routine ea ea f)
    (count : δ → ℕ) (initial : δ → α) (P : Polynomial ℕ)
    (hbound : ∀ d j,j≤count d → (ea (f^[j] (initial d))).length≤
      P.eval (pairBits (unary (count d)) (ea (initial d))).length) :
    Routine (fun d => pairBits (unary (count d)) (ea (initial d))) ea
      (fun d => f^[count d] (initial d)) where
  scratch := p.scratch+1
  block :=
    let ι : Fin (p.scratch+1) → Fin (p.scratch+2) := fun i => ⟨i.val,by omega⟩
    let c : Fin (p.scratch+2) := ⟨p.scratch+1,by omega⟩
    (Block.decodeRev 0 c).seq (Block.loop c ((Block.pop c).seq (p.block.rename ι)))
  time := X*(p.time.comp P+7)+3
  correct d := by
    let R := p.scratch+2
    let ι : Fin (p.scratch+1) → Fin R := fun i => ⟨i.val,by omega⟩
    let c : Fin R := ⟨p.scratch+1,by omega⟩
    have hι : Function.Injective ι := fun i j h => Fin.ext (congrArg (fun k : Fin R => k.val) h)
    have hc : ∀ i,ι i≠c := by
      intro i h
      have hh := congrArg (fun k : Fin R => k.val) h
      have hi := i.isLt
      simp only [ι,c] at hh
      omega
    have h0c : (0:Fin R)≠c := hc 0
    let e := pairBits (unary (count d)) (ea (initial d))
    let s₀ : Store R := Function.update (fun _ => []) 0 e
    let s₁ : Store R := Function.update (Function.update s₀ 0 (ea (initial d))) c (unary (count d))
    have hd : (Block.decodeRev 0 c).Runs s₀ s₁ (5*count d+2) := by
      simpa [s₁,s₀,h0c.symm] using Block.decodeRev_runs (0:Fin R) c h0c
        (unary (count d)) (ea (initial d)) s₀ (by simp [s₀,e])
    obtain ⟨t,ht,hi⟩ := p.iterate_runs_at ι hι c hc (P.eval e.length) (count d) (initial d) s₁
      (by change s₁ 0=_; simp [s₁,h0c]) (by
        intro i hi
        have hne : ι i≠0 := fun h => hi (hι h)
        simp [s₁,s₀,Function.update_of_ne,hne,hc])
      (by simp [s₁]) (hbound d)
    have he : Function.update (Function.update s₁ c []) (ι 0) (ea (f^[count d] (initial d)))=
        Function.update (fun _ => []) 0 (ea (f^[count d] (initial d))) := by
      funext k
      change Function.update (Function.update s₁ c []) 0 _ k=_
      by_cases hk : k=0
      · subst k; simp
      · by_cases hkc : k=c
        · subst k; simp [h0c.symm]
        · simp [s₁,s₀,Function.update_of_ne,hk,hkc]
    rw [he] at hi
    refine ⟨_,?_,Block.seq_runs _ _ hd hi⟩
    simp only [eval_add,eval_mul,eval_X,eval_comp,eval_ofNat]
    change 5*count d+2+t≤e.length*(p.time.eval (P.eval e.length)+7)+3
    have hn : count d≤e.length := by simp [e,pairBits_length]; omega
    have hmul := Nat.mul_le_mul_right (p.time.eval (P.eval e.length)+7) hn
    nlinarith

end Routine
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Routine

noncomputable def append : Routine (fun z : List Bool×List Bool => pairBits z.1 z.2) id
    (fun z => z.1++z.2) where
  scratch := 1
  block := (Block.decodeRev 0 1).seq (Block.reverseInto 1 0)
  time := 10*X+10
  correct z := by
    let s₀ : Store 2 := Function.update (fun _ => []) 0 (pairBits z.1 z.2)
    let s₁ := Function.update (Function.update s₀ 0 z.2) 1 z.1.reverse
    have h₁ : (Block.decodeRev 0 1).Runs s₀ s₁ (5*z.1.length+2) := by
      simpa [s₁,s₀] using Block.decodeRev_runs (0:Fin 2) 1 (by decide) z.1 z.2
        s₀ (by simp [s₀])
    have h₂ := Block.reverseInto_runs (1:Fin 2) 0 (by decide) s₁
    have he : Function.update (Function.update s₁ 1 []) 0 ((s₁ 1).reverse++s₁ 0)=
        Function.update (fun _ => []) 0 (z.1++z.2) := by
      funext k
      fin_cases k <;> simp [s₁,s₀]
    rw [he] at h₂
    have hl : (s₁ 1).length=z.1.length := by simp [s₁]
    rw [hl] at h₂
    refine ⟨_,?_,Block.seq_runs _ _ h₁ h₂⟩
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,pairBits_length]
    omega

noncomputable def pushBit (b : Bool) : Routine (id : List Bool → List Bool) id (List.cons b) where
  scratch := 0
  block := Block.push 0 b
  time := 1
  correct x := by
    refine ⟨1,by simp,?_⟩
    simpa [Function.update_idem] using Block.push_runs (0:Fin 1) b (Function.update (fun _ => []) 0 x)

noncomputable def tail : Routine (id : List Bool → List Bool) id List.tail where
  scratch := 0
  block := Block.pop 0
  time := 1
  correct x := by
    refine ⟨1,by simp,?_⟩
    simpa [Function.update_idem] using Block.pop_runs (0:Fin 1) (Function.update (fun _ => []) 0 x)

noncomputable def isEmpty : Routine (id : List Bool → List Bool) (fun b : Bool => [b]) List.isEmpty where
  scratch := 0
  block := Block.cases 0 (Block.push 0 true)
    ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 false))
  time := 2*X+3
  correct x := by
    let s : Store 1 := Function.update (fun _ => []) 0 x
    have hfalse := Block.seq_runs _ _ (Block.clear_runs (0:Fin 1) s)
      (Block.push_runs (0:Fin 1) false (Function.update s 0 []))
    have htrue := Block.push_runs (0:Fin 1) true s
    cases x with
    | nil =>
      have hh := Block.cases_runs_empty (0:Fin 1) (Block.push 0 true)
        ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 false)) (by simp [s]) htrue
      refine ⟨2,by simp,?_⟩
      simpa [s,Function.update_idem] using hh
    | cons b l =>
      cases b with
      | false =>
        have hh := Block.cases_runs_false (0:Fin 1) (Block.push 0 true)
          ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 false))
          (by simp [s]) hfalse
        refine ⟨2*(l.length+1)+3,?_,?_⟩
        · simp
        · simpa [s,Function.update_idem,Nat.add_assoc] using hh
      | true =>
        have hh := Block.cases_runs_true (0:Fin 1) (Block.push 0 true)
          ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 false))
          (by simp [s]) hfalse
        refine ⟨2*(l.length+1)+3,?_,?_⟩
        · simp
        · simpa [s,Function.update_idem,Nat.add_assoc] using hh

end Routine
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Block
variable {r : ℕ}
def lengthInto (src dst : Fin r) : Block r := loop src ((pop src).seq (push dst true))
lemma lengthInto_runs (src dst : Fin r) (hne : src≠dst) (s : Store r) :
    (lengthInto src dst).Runs s
      (Function.update (Function.update s src []) dst (unary (s src).length++s dst))
      (3*(s src).length+1) := by
  generalize hl : s src=l
  induction l generalizing s with
  | nil =>
    have he : Function.update (Function.update s src []) dst (unary 0++s dst)=s := by
      simp only [unary_zero,List.nil_append]
      rw [←hl,Function.update_eq_self,Function.update_eq_self]
    change (lengthInto src dst).Runs s
      (Function.update (Function.update s src []) dst (unary 0++s dst)) 1
    rw [he]
    exact loop_runs_empty src _ s hl
  | cons b l ih =>
    let s' := Function.update (Function.update s src l) dst (true::s dst)
    have hp : (pop src).Runs s (Function.update s src l) 1 := by
      simpa [hl] using pop_runs src s
    have ht : (push dst true).Runs (Function.update s src l) s' 1 := by
      simpa [s',hne.symm] using push_runs dst true (Function.update s src l)
    have hi := ih s' (by simp [s',hne])
    have he : Function.update (Function.update s' src []) dst (unary l.length++s' dst)=
        Function.update (Function.update s src []) dst (unary (b::l).length++s dst) := by
      funext k
      by_cases hk : k=dst
      · subst k
        simp only [Function.update_self,s',List.length_cons,unary]
        simp only [List.replicate_succ',List.append_assoc,List.singleton_append]
      · by_cases hks : k=src
        · subst k; simp [s',hne]
        · simp [s',Function.update_of_ne,hk,hks]
    rw [he] at hi
    have h := loop_runs_step src ((pop src).seq (push dst true)) (by simp [hl])
      (seq_runs _ _ hp ht) hi
    have heq : 2+(3*l.length+1)+1=3*(b::l).length+1 := by simp; omega
    rw [heq] at h
    exact h
end Block
namespace Routine
variable {α : Type}
noncomputable def codeLength (ea : α → List Bool) : Routine ea unary (fun a => (ea a).length) where
  scratch := 1
  block := (Block.lengthInto 0 1).seq (Block.reverseInto 1 0)
  time := 7*X+2
  correct a := by
    let s₀ : Store 2 := Function.update (fun _ => []) 0 (ea a)
    let s₁ := Function.update (Function.update s₀ 0 []) 1 (unary (ea a).length)
    have h₁ : (Block.lengthInto 0 1).Runs s₀ s₁ (3*(ea a).length+1) := by
      simpa [s₀,s₁] using Block.lengthInto_runs (0:Fin 2) 1 (by decide) s₀
    have h₂ := Block.reverseInto_runs (1:Fin 2) 0 (by decide) s₁
    have he : Function.update (Function.update s₁ 1 []) 0 ((s₁ 1).reverse++s₁ 0)=
        Function.update (fun _ => []) 0 (unary (ea a).length) := by
      funext k
      fin_cases k <;> simp [s₁,s₀]
    rw [he] at h₂
    have hl : (s₁ 1).length=(ea a).length := by simp [s₁]
    rw [hl] at h₂
    refine ⟨_,?_,Block.seq_runs _ _ h₁ h₂⟩
    simp only [eval_add,eval_mul,eval_ofNat,eval_X]
    omega
end Routine
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
class Coding (α : Type) where
  encode : α → List Bool
export Coding (encode)
instance : Coding ℕ := ⟨unary⟩
instance : Coding Bool := ⟨fun b => [b]⟩
instance : Coding Unit := ⟨fun _ => []⟩
instance {α β : Type} [Coding α] [Coding β] : Coding (α×β) :=
  ⟨fun z => pairBits (encode z.1) (encode z.2)⟩

def listCode {α : Type} (ea : α → List Bool) : List α → List Bool
  | [] => []
  | a::l => pairBits (ea a) (listCode ea l)
instance {α : Type} [Coding α] : Coding (List α) := ⟨listCode encode⟩

@[simp] lemma encode_nat (n : ℕ) : encode n=unary n := rfl
@[simp] lemma encode_bool (b : Bool) : encode b=[b] := rfl
@[simp] lemma encode_pair {α β : Type} [Coding α] [Coding β] (a : α) (b : β) :
    encode (a,b)=pairBits (encode a) (encode b) := rfl
@[simp] lemma encode_prod {α β : Type} [Coding α] [Coding β] (z : α×β) :
    encode z=pairBits (encode z.1) (encode z.2) := rfl

@[simp] lemma code_nil {α : Type} [Coding α] : encode ([]:List α)=[] := rfl
@[simp] lemma code_cons {α : Type} [Coding α] (a : α) (l : List α) :
    encode (a::l)=pairBits (encode a) (encode l) := rfl

lemma pairBits_append (x y z : List Bool) : pairBits x (y++z)=pairBits x y++z := by
  induction x with
  | nil => rfl
  | cons b x ih => simpa only [pairBits,List.cons_append,Function.comp_apply] using congrArg (List.cons false ∘ List.cons b) ih

lemma code_append {α : Type} [Coding α] (l m : List α) : encode (l++m)=encode l++encode m := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.cons_append,code_cons,ih,pairBits_append]

lemma list_length_le_code {α : Type} [Coding α] (l : List α) : l.length≤(encode l).length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.length_cons,code_cons,pairBits_length]; omega

@[fun_prop] def Poly {α β : Type} [Coding α] [Coding β] (f : α → β) : Prop :=
  Nonempty (Routine encode encode f)

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]
noncomputable def routine {f : α → β} (h : Poly f) : Routine encode encode f := Classical.choice h

@[fun_prop] theorem identity : Poly (fun a : α => a) := ⟨Routine.identity encode⟩
@[fun_prop] theorem constant (b : β) : Poly (fun _ : α => b) := ⟨Routine.constant encode encode b⟩
@[fun_prop] theorem comp (f : β → γ) (g : α → β) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => f (g a)) := ⟨hg.routine.comp hf.routine⟩
@[fun_prop] theorem pair (f : α → β) (g : α → γ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => (f a,g a)) := ⟨hf.routine.pair hg.routine⟩
@[fun_prop] theorem first (f : α → β×γ) (hf : Poly f) : Poly (fun a => (f a).1) :=
  ⟨hf.routine.comp (Routine.first encode encode)⟩
@[fun_prop] theorem second (f : α → β×γ) (hf : Poly f) : Poly (fun a => (f a).2) :=
  ⟨hf.routine.comp (Routine.second encode encode)⟩

@[fun_prop] theorem cond (b : α → Bool) (f g : α → β) (hb : Poly b) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => if b a then g a else f a) := by
  let p := (hb.routine.pair (Routine.identity encode)).comp (hf.routine.select hg.routine)
  exact ⟨p⟩

@[fun_prop] theorem codeLength : Poly (fun a : α => (encode a).length) := ⟨Routine.codeLength encode⟩

theorem boundedIterate (f : α → α) (hf : Poly f) (P : Polynomial ℕ)
    (h : ∀ (z : ℕ×α) j,j≤z.1 → (encode (f^[j] z.2)).length≤P.eval (encode z).length) :
    Poly (fun z : ℕ×α => f^[z.1] z.2) :=
  ⟨hf.routine.boundedIterate Prod.fst Prod.snd P h⟩

theorem congr {f g : α → β} (hf : Poly f) (h : ∀ a,f a=g a) : Poly g := by
  have he : f=g := funext h
  rwa [←he]

end Poly
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Routine
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
  {f : α×List α → β}

noncomputable def listCases (b : β)
    (p : Routine (fun z : α×List α => pairBits (ea z.1) (listCode ea z.2)) eb f) :
    Routine (listCode ea) eb (fun l => match l with | [] => b | a::l => f (a,l)) where
  scratch := p.scratch
  block := Block.cases 0 (Block.emit 0 (eb b)) p.block p.block
  time := p.time+C ((eb b).length+2)
  correct l := by
    let s : Store (p.scratch+1) := Function.update (fun _ => []) 0 (listCode ea l)
    cases l with
    | nil =>
      have he := Block.emit_runs (0:Fin (p.scratch+1)) (eb b) s
      have hh := Block.cases_runs_empty (0:Fin (p.scratch+1)) (Block.emit 0 (eb b))
        p.block p.block (by simp [s,listCode]) he
      refine ⟨(eb b).length+1+1,?_,?_⟩
      · simp only [eval_add,eval_C]
        omega
      · simpa [s,listCode,Function.update_idem] using hh
    | cons a l =>
      obtain ⟨t,ht,hp⟩ := p.correct (a,l)
      change p.block.Runs s (Function.update (fun _ => []) 0 (eb (f (a,l)))) t at hp
      refine ⟨t+1,?_,?_⟩
      · simp only [eval_add,eval_C,listCode] at *
        omega
      · cases ha : ea a with
        | nil => exact Block.cases_runs_true _ _ _ _ (by simp [listCode,ha,pairBits]) hp
        | cons x xs => exact Block.cases_runs_false _ _ _ _ (by simp [listCode,ha,pairBits]) hp
end Routine
namespace Poly
variable {α β : Type} [Coding α] [Coding β]

@[fun_prop] theorem listCases (b : β) (f : α×List α → β) (hf : Poly f) :
    Poly (fun l => match l with | [] => b | a::l => f (a,l)) :=
  ⟨Routine.listCases encode encode b hf.routine⟩

@[fun_prop] theorem listCons : Poly (fun z : α×List α => z.1::z.2) := by
  refine ⟨(Routine.identity (encode : α×List α → List Bool)).reindex encode encode
    (fun z : α×List α => z.1::z.2) id (fun _ => rfl) (fun _ => rfl)⟩

@[fun_prop] theorem listTail : Poly (List.tail : List α → List α) := by
  exact listCases [] Prod.snd (by fun_prop)

@[fun_prop] theorem listHeadD (a : α) : Poly (fun l : List α => l.headD a) := by
  exact (listCases a Prod.fst (by fun_prop)).congr (fun l => by cases l <;> rfl)

@[fun_prop] theorem listIsEmpty : Poly (List.isEmpty : List α → Bool) := by
  exact listCases true (fun _ : α×List α => false) (by fun_prop)

@[fun_prop] theorem listAppend : Poly (fun z : List α×List α => z.1++z.2) := by
  refine ⟨Routine.append.reindex encode encode (fun z : List α×List α => z.1++z.2)
    (fun z => (encode z.1,encode z.2)) (fun _ => rfl) ?_⟩
  intro z
  exact (code_append z.1 z.2).symm

end Poly
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Poly

@[fun_prop] theorem natSucc : Poly (fun n : ℕ => n+1) := by
  refine ⟨(Routine.pushBit true).reindex encode encode (fun n : ℕ => n+1) unary
    (fun _ => rfl) ?_⟩
  intro n
  simp

@[fun_prop] theorem natPred : Poly (Nat.pred : ℕ → ℕ) := by
  refine ⟨Routine.tail.reindex encode encode Nat.pred unary (fun _ => rfl) ?_⟩
  intro n
  cases n <;> simp

@[fun_prop] theorem natZeroTest : Poly (fun n : ℕ => decide (n=0)) := by
  refine ⟨Routine.isEmpty.reindex encode encode (fun n : ℕ => decide (n=0)) unary
    (fun _ => rfl) ?_⟩
  intro n
  cases n <;> simp

@[fun_prop] theorem natAdd : Poly (fun z : ℕ×ℕ => z.1+z.2) := by
  refine ⟨Routine.append.reindex encode encode (fun z : ℕ×ℕ => z.1+z.2)
    (fun z => (unary z.1,unary z.2)) (fun _ => rfl) ?_⟩
  intro z
  simp only [id_eq,encode_nat,unary,List.replicate_add]

@[fun_prop] theorem natSub : Poly (fun z : ℕ×ℕ => z.1-z.2) := by
  have hp : Poly (fun z : ℕ×ℕ => Nat.pred^[z.1] z.2) :=
    boundedIterate Nat.pred natPred X (by
      intro z j hj
      simp only [Nat.pred_iterate,encode_nat,unary_length,encode_prod,pairBits_length,eval_X]
      omega)
  have h : Poly (fun z : ℕ×ℕ => Nat.pred^[z.2] z.1) := by fun_prop
  exact h.congr (fun z => Nat.pred_iterate z.1 z.2)

@[fun_prop] theorem boolNot : Poly (Bool.not : Bool → Bool) := by
  have h : Poly (fun b : Bool => if b then false else true) := by fun_prop
  exact h.congr (fun b => by cases b <;> rfl)

@[fun_prop] theorem boolAnd : Poly (fun z : Bool×Bool => z.1 && z.2) := by
  have h : Poly (fun z : Bool×Bool => if z.1 then z.2 else false) := by fun_prop
  exact h.congr (fun z => by cases z.1 <;> rfl)

@[fun_prop] theorem boolOr : Poly (fun z : Bool×Bool => z.1 || z.2) := by
  have h : Poly (fun z : Bool×Bool => if z.1 then true else z.2) := by fun_prop
  exact h.congr (fun z => by cases z.1 <;> rfl)

@[fun_prop] theorem natLE : Poly (fun z : ℕ×ℕ => decide (z.1≤z.2)) := by
  have h : Poly (fun z : ℕ×ℕ => decide (z.1-z.2=0)) := comp _ _ natZeroTest natSub
  exact h.congr (fun z => by simp [Nat.sub_eq_zero_iff_le])

@[fun_prop] theorem natLT : Poly (fun z : ℕ×ℕ => decide (z.1<z.2)) := by
  have hle : Poly (fun z : ℕ×ℕ => decide (z.2≤z.1)) := comp _ (fun z : ℕ×ℕ => (z.2,z.1)) natLE (by fun_prop)
  have h : Poly (fun z : ℕ×ℕ => !(decide (z.2≤z.1))) := comp _ _ boolNot hle
  exact h.congr (fun z => by simp [←decide_not])

@[fun_prop] theorem natEQ : Poly (fun z : ℕ×ℕ => decide (z.1=z.2)) := by
  have hle : Poly (fun z : ℕ×ℕ => decide (z.2≤z.1)) := comp _ (fun z : ℕ×ℕ => (z.2,z.1)) natLE (by fun_prop)
  have h : Poly (fun z : ℕ×ℕ => decide (z.1≤z.2) && decide (z.2≤z.1)) :=
    comp _ _ boolAnd (pair _ _ natLE hle)
  exact h.congr (fun z => by simp [le_antisymm_iff])

private def addStep (z : ℕ×ℕ) : ℕ×ℕ := (z.1,z.2+z.1)
private lemma addStep_iterate (n : ℕ) (z : ℕ×ℕ) : addStep^[n] z=(z.1,z.2+n*z.1) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply',ih,addStep,Nat.add_mul,Nat.add_assoc]

@[fun_prop] theorem natMul : Poly (fun z : ℕ×ℕ => z.1*z.2) := by
  have hs : Poly addStep := by unfold addStep; fun_prop
  have hi : Poly (fun z : ℕ×(ℕ×ℕ) => addStep^[z.1] z.2) :=
    boundedIterate addStep hs ((X+1)^2) (by
      intro z j hj
      simp only [addStep_iterate,encode_prod,encode_nat,unary_length,pairBits_length,
        eval_pow,eval_add,eval_X,eval_one]
      have hh : j*z.2.1≤z.1*z.2.1 := Nat.mul_le_mul_right _ hj
      nlinarith [sq_nonneg (z.1:ℤ),sq_nonneg (z.2.1:ℤ)])
  have h : Poly (fun z : ℕ×ℕ => (addStep^[z.2] (z.1,0)).2) := by fun_prop
  exact h.congr (fun z => by simp [addStep_iterate,Nat.mul_comm])

@[fun_prop] theorem natMin : Poly (fun z : ℕ×ℕ => min z.1 z.2) := by
  have h : Poly (fun z : ℕ×ℕ => if decide (z.1≤z.2) then z.1 else z.2) := by fun_prop
  exact h.congr (fun z => by simp [min_def])

@[fun_prop] theorem natMax : Poly (fun z : ℕ×ℕ => max z.1 z.2) := by
  have h : Poly (fun z : ℕ×ℕ => if decide (z.1≤z.2) then z.2 else z.1) := by fun_prop
  exact h.congr (fun z => by simp [max_def])

variable {α : Type} [Coding α]
@[fun_prop] theorem natLe_apply (f g : α → ℕ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a≤g a)) := comp _ _ natLE (pair _ _ hf hg)
@[fun_prop] theorem natLt_apply (f g : α → ℕ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a<g a)) := comp _ _ natLT (pair _ _ hf hg)
@[fun_prop] theorem natEq_apply (f g : α → ℕ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a=g a)) := comp _ _ natEQ (pair _ _ hf hg)
@[fun_prop] theorem natPow (k : ℕ) : Poly (fun n : ℕ => n^k) := by
  induction k with
  | zero => simpa only [pow_zero] using (constant (α := ℕ) (1:ℕ))
  | succ k ih =>
    have h : Poly (fun n : ℕ => n^k*n) := comp _ _ natMul (pair _ _ ih identity)
    exact h.congr (fun n => (pow_succ n k).symm)
end Poly
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma code_drop_le {α : Type} [Coding α] (l : List α) (n : ℕ) :
    (encode (l.drop n)).length≤(encode l).length := by
  have h := congrArg (fun xs => (encode xs).length) (List.take_append_drop n l)
  rw [code_append,List.length_append] at h
  omega

def foldStep {α β : Type} (a₀ : α) (f : β×α → β) (z : List α×β) : List α×β :=
  if z.1.isEmpty then z else (z.1.tail,f (z.2,z.1.headD a₀))

lemma foldStep_iterate {α β : Type} (a₀ : α) (f : β×α → β) (n : ℕ) (z : List α×β) :
    (foldStep a₀ f)^[n] z=(z.1.drop n,(z.1.take n).foldl (fun b a => f (b,a)) z.2) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rcases z with ⟨l,b⟩
    cases l with
    | nil => simp [Function.iterate_succ_apply,foldStep,ih]
    | cons a l => simp [Function.iterate_succ_apply,foldStep,ih]

namespace Poly
variable {α β : Type} [Coding α] [Coding β]

theorem listFold (a₀ : α) (f : β×α → β) (hf : Poly f) (P : Polynomial ℕ)
    (hb : ∀ (z : List α×β) k,
      (encode ((z.1.take k).foldl (fun b a => f (b,a)) z.2)).length≤P.eval (encode z).length) :
    Poly (fun z : List α×β => z.1.foldl (fun b a => f (b,a)) z.2) := by
  have hs : Poly (foldStep a₀ f) := by unfold foldStep; fun_prop
  have hi : Poly (fun z : ℕ×(List α×β) => (foldStep a₀ f)^[z.1] z.2) :=
    boundedIterate (foldStep a₀ f) hs (X+P) (by
      intro z j hj
      rw [foldStep_iterate]
      have hl := code_drop_le z.2.1 j
      have hn : (encode z.2).length≤(encode z).length := by
        simp only [encode_prod,pairBits_length]
        omega
      have hacc := (hb z.2 j).trans (polynomial_eval_mono P hn)
      simp only [encode_prod,pairBits_length,eval_add,eval_X] at *
      omega)
  have h : Poly (fun z : List α×β => ((foldStep a₀ f)^[(encode z.1).length] z).2) :=
    second _ (comp _ (fun z : List α×β => ((encode z.1).length,z)) hi
      (pair _ _ (comp _ Prod.fst codeLength (first _ identity)) identity))
  exact h.congr (fun z => by
    rw [foldStep_iterate]
    simp only [List.take_of_length_le (list_length_le_code z.1)])

omit [Coding α] in
private lemma count_fold (l : List α) (b : ℕ) :
    l.foldl (fun b _ => b+1) b=b+l.length := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih,Nat.add_comm,Nat.add_left_comm]

@[fun_prop] theorem listLength [Inhabited α] : Poly (List.length : List α → ℕ) := by
  have hf : Poly (fun z : ℕ×α => z.1+1) := by fun_prop
  have hfold := listFold (default:α) (fun z : ℕ×α => z.1+1) hf X (by
    intro z k
    rw [count_fold]
    have hk : (z.1.take k).length≤z.1.length := by simp only [List.length_take]; exact Nat.min_le_right _ _
    have hl := list_length_le_code z.1
    simp only [encode_nat,unary_length,encode_prod,pairBits_length,eval_X]
    omega)
  have hh : Poly (fun l : List α => l.foldl (fun b _ => b+1) 0) :=
    comp _ (fun l : List α => (l,0)) hfold (by fun_prop)
  exact hh.congr (fun l => by simp)

end Poly
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma element_code_le {α : Type} [Coding α] (l : List α) (a : α) (ha : a∈l) :
    (encode a).length≤(encode l).length := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.mem_cons] at ha
    simp only [code_cons,pairBits_length]
    rcases ha with rfl | ha
    · omega
    · have hh := ih ha; omega

lemma list_code_bound {α : Type} [Coding α] (l : List α) (M : ℕ)
    (hb : ∀ a∈l,(encode a).length≤M) : (encode l).length≤l.length*(2*M+1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hb a (by simp)
    have hl := ih (fun a ha => hb a (List.mem_cons_of_mem _ ha))
    simp only [code_cons,pairBits_length,List.length_cons]
    nlinarith

lemma code_reverse_length {α : Type} [Coding α] (l : List α) :
    (encode l.reverse).length=(encode l).length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.reverse_cons,code_append,pairBits_length,ih]; omega

lemma append_map_fold {α β : Type} (f : α → β) (l : List α) (b : List β) :
    l.foldl (fun b a => b++[f a]) b=b++l.map f := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih,List.append_assoc]

lemma append_fold {α : Type} (l : List (List α)) (b : List α) :
    l.foldl (fun b a => b++a) b=b++l.flatten := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih,List.append_assoc]

lemma code_flatten_le {α : Type} [Coding α] (l : List (List α)) :
    (encode l.flatten).length≤(encode l).length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatten_cons,code_append,List.length_append,code_cons,pairBits_length]; omega

namespace Poly
variable {α β : Type} [Coding α] [Coding β]

@[fun_prop] theorem listMap [Inhabited α] (f : α → β) (hf : Poly f) : Poly (List.map f) := by
  let p := hf.routine.time
  have hs : Poly (fun z : List β×α => z.1++[f z.2]) := by fun_prop
  have hfold := listFold (default:α) (fun z : List β×α => z.1++[f z.2]) hs
    (X+X*(2*(X+p)+1)) (by
      intro z k
      rw [append_map_fold,code_append,List.length_append]
      let N := (encode z).length
      have help : ∀ a∈z.1.take k,(encode a).length≤N := by
        intro a ha
        have hh := element_code_le z.1 a (List.mem_of_mem_take ha)
        simp only [N,encode_prod,pairBits_length]
        omega
      have hb : ∀ b∈(z.1.take k).map f,(encode b).length≤N+p.eval N := by
        intro b hb
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
        have ht := hf.routine.length_bound a
        have hh := help a ha
        have hm := polynomial_eval_mono p hh
        exact ht.trans (Nat.add_le_add hh hm)
      have hmap := list_code_bound ((z.1.take k).map f) (N+p.eval N) hb
      have ht : (z.1.take k).length≤N := (show (z.1.take k).length≤z.1.length by simp only [List.length_take]; exact Nat.min_le_right _ _).trans
        ((list_length_le_code z.1).trans (by simp only [N,encode_prod,pairBits_length]; omega))
      have hmul := Nat.mul_le_mul_right (2*(N+p.eval N)+1) ht
      simp only [List.length_map] at hmap
      have hb₀ : (encode z.2).length≤N := by simp only [N,encode_prod,pairBits_length]; omega
      simp only [eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
      change (encode z.2).length+(encode ((z.1.take k).map f)).length≤N+N*(2*(N+p.eval N)+1)
      omega)
  have hh : Poly (fun l : List α => l.foldl (fun b a => b++[f a]) []) :=
    comp _ (fun l : List α => (l,[])) hfold (by fun_prop)
  exact hh.congr (fun l => by rw [append_map_fold,List.nil_append])

@[fun_prop] theorem listFlatten : Poly (List.flatten : List (List α) → List α) := by
  have hs : Poly (fun z : List α×List α => z.1++z.2) := by fun_prop
  have hfold := listFold ([]:List α) (fun z : List α×List α => z.1++z.2) hs X (by
    intro z k
    rw [append_fold,code_append,List.length_append]
    have h₁ := code_flatten_le (z.1.take k)
    have h₂ : (encode (z.1.take k)).length≤(encode z.1).length := by
      have hh := congrArg (fun l => (encode l).length) (List.take_append_drop k z.1)
      rw [code_append,List.length_append] at hh
      omega
    simp only [eval_X,encode_prod,pairBits_length]
    omega)
  have hh : Poly (fun l : List (List α) => l.foldl (fun b a => b++a) []) :=
    comp _ (fun l : List (List α) => (l,[])) hfold (by fun_prop)
  exact hh.congr (fun l => by simp [append_fold])

@[fun_prop] theorem listFlatMap [Inhabited α] (f : α → List β) (hf : Poly f) :
    Poly (List.flatMap f) := by
  have hm := listMap f hf
  have hl : Poly (List.flatten : List (List β) → List β) := listFlatten
  have hh : Poly (fun l : List α => (l.map f).flatten) := comp _ _ hl hm
  exact hh

@[fun_prop] theorem listFilter [Inhabited α] (f : α → Bool) (hf : Poly f) :
    Poly (List.filter f) := by
  have hs : Poly (fun a => if f a then [a] else []) := by fun_prop
  have hh := listFlatMap (fun a => if f a then [a] else []) hs
  exact hh.congr (fun l => by
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.filter_cons,ih]; split <;> simp_all)

end Poly
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma code_take_le {α : Type} [Coding α] (l : List α) (n : ℕ) :
    (encode (l.take n)).length≤(encode l).length := by
  have h := congrArg (fun xs => (encode xs).length) (List.take_append_drop n l)
  rw [code_append,List.length_append] at h
  omega

lemma code_replicate {α : Type} [Coding α] (a : α) (n : ℕ) :
    (encode (List.replicate n a)).length=n*(2*(encode a).length+1) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ,code_cons,pairBits_length,ih]; nlinarith

def dupStep {α : Type} (z : α×List α) : α×List α := (z.1,z.1::z.2)
lemma dupStep_iterate {α : Type} (n : ℕ) (z : α×List α) :
    dupStep^[n] z=(z.1,List.replicate n z.1++z.2) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply',ih,dupStep,List.replicate_succ]

lemma code_zip_bound {α β : Type} [Coding α] [Coding β] (l : List α) (m : List β) :
    (encode (l.zip m)).length≤2*(encode l).length+(encode m).length := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    cases m with
    | nil => simp
    | cons b m =>
      have h := ih m
      simp only [List.zip_cons_cons,code_cons,encode_prod,pairBits_length]
      omega

def zipStep {α β : Type} [Inhabited α] [Inhabited β]
    (z : List α×(List β×List (α×β))) : List α×(List β×List (α×β)) :=
  (z.1.tail,z.2.1.tail,if z.1.isEmpty || z.2.1.isEmpty then z.2.2
    else z.2.2++[(z.1.headD default,z.2.1.headD default)])

lemma zipStep_iterate {α β : Type} [Inhabited α] [Inhabited β]
    (n : ℕ) (z : List α×(List β×List (α×β))) :
    zipStep^[n] z=(z.1.drop n,z.2.1.drop n,
      z.2.2++(z.1.take n).zip (z.2.1.take n)) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rcases z with ⟨l,m,o⟩
    cases l <;> cases m <;>
      simp [Function.iterate_succ_apply,zipStep,ih,List.append_assoc]

lemma zip_take_right_of_ge {α β : Type} (l : List α) (m : List β) (n : ℕ)
    (hn : l.length≤n) : l.zip (m.take n)=l.zip m := by
  induction l generalizing m n with
  | nil => simp
  | cons a l ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      cases m with
      | nil => simp
      | cons b m => simp only [List.take_succ_cons,List.zip_cons_cons,ih m n (by simpa using hn)]

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

@[fun_prop] theorem listReplicate : Poly (fun z : ℕ×α => List.replicate z.1 z.2) := by
  have hs : Poly (dupStep : α×List α → α×List α) := by unfold dupStep; fun_prop
  have hi : Poly (fun z : ℕ×(α×List α) => dupStep^[z.1] z.2) :=
    boundedIterate dupStep hs ((X+1)^2) (by
      intro z j hj
      rw [dupStep_iterate]
      simp only [encode_prod,pairBits_length,code_append,List.length_append,code_replicate,
        encode_nat,unary_length,eval_pow,eval_add,eval_X,eval_one]
      have hm := Nat.mul_le_mul_right (2*(encode z.2.1).length+1) hj
      nlinarith)
  have h : Poly (fun z : ℕ×α => (dupStep^[z.1] (z.2,[])).2) :=
    second _ (comp _ (fun z : ℕ×α => (z.1,(z.2,[]))) hi (by fun_prop))
  exact h.congr (fun z => by simp [dupStep_iterate])

@[fun_prop] theorem listZip [Inhabited α] [Inhabited β] :
    Poly (fun z : List α×List β => z.1.zip z.2) := by
  have hs : Poly (zipStep : List α×(List β×List (α×β)) → _) := by unfold zipStep; fun_prop
  have hi : Poly (fun z : ℕ×(List α×(List β×List (α×β))) => zipStep^[z.1] z.2) :=
    boundedIterate zipStep hs (2*X) (by
      intro z j hj
      rw [zipStep_iterate]
      have h₁ := code_drop_le z.2.1 j
      have h₂ := code_drop_le z.2.2.1 j
      have h₃ := code_take_le z.2.1 j
      have h₄ := code_take_le z.2.2.1 j
      have h₅ := code_zip_bound (z.2.1.take j) (z.2.2.1.take j)
      simp only [encode_prod,pairBits_length,code_append,List.length_append,encode_nat,unary_length,
        eval_mul,eval_ofNat,eval_X]
      omega)
  have h : Poly (fun z : List α×List β => (zipStep^[(encode z.1).length] (z.1,z.2,[])).2.2) := by
    apply second
    apply second
    apply comp _ (fun z : List α×List β => ((encode z.1).length,(z.1,z.2,[]))) hi
    apply pair
    · exact comp _ Prod.fst codeLength (first _ identity)
    · fun_prop
  exact h.congr (fun z => by
    rw [zipStep_iterate]
    simp only [List.nil_append,List.take_of_length_le (list_length_le_code z.1)]
    exact zip_take_right_of_ge z.1 z.2 _ (list_length_le_code z.1))

@[fun_prop] theorem listMapParam [Inhabited α] [Inhabited γ]
    (f : γ×α → β) (hf : Poly f) : Poly (fun z : γ×List α => z.2.map (fun a => f (z.1,a))) := by
  have hm : Poly (List.map f) := listMap f hf
  have h : Poly (fun z : γ×List α => (List.zip (List.replicate z.2.length z.1) z.2).map f) := by fun_prop
  exact h.congr (fun z => by
    have hz : List.zip (List.replicate z.2.length z.1) z.2=z.2.map (fun a => (z.1,a)) := by
      induction z.2 with
      | nil => rfl
      | cons a l ih => simpa only [List.length_cons,List.replicate_succ,List.zip_cons_cons,List.map_cons] using congrArg (List.cons (z.1,a)) ih
    simp [hz,List.map_map,Function.comp_def])

end Poly
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Poly
variable {α β γ δ : Type} [Coding α] [Coding β] [Coding γ] [Coding δ]

theorem reindex {f : α → β} (hf : Poly f) (g : γ → δ) (i : γ → α)
    (hin : ∀ x,encode x=encode (i x))
    (hout : ∀ x,encode (f (i x))=encode (g x)) : Poly g :=
  ⟨hf.routine.reindex encode encode g i (fun x => (hin x).symm) hout⟩

theorem iterateFrom (step : α → α) (hs : Poly step) (count : β → ℕ) (initial : β → α)
    (hc : Poly count) (hi : Poly initial) (P : Polynomial ℕ)
    (hb : ∀ b j,j≤count b → (encode (step^[j] (initial b))).length≤
      P.eval (encode (count b,initial b)).length) :
    Poly (fun b => step^[count b] (initial b)) := by
  let paired := (pair count initial hc hi).routine
  let setup : Routine encode (fun b => encode (count b,initial b)) (id : β → β) :=
    paired.reindex encode (fun b => encode (count b,initial b)) id id
      (fun _ => rfl) (fun _ => rfl)
  exact ⟨setup.comp (hs.routine.boundedIterate count initial P hb)⟩

end Poly
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode

instance {α : Type} [Coding α] : Coding (Option α) := ⟨fun x => encode x.toList⟩
instance {α β : Type} [Coding α] [Coding β] : Coding (Sum α β) :=
  ⟨fun x => match x with | .inl a => encode ([a],([]:List β)) | .inr b => encode (([]:List α),[b])⟩

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

@[fun_prop] theorem some : Poly (Option.some : α → Option α) := by
  have h : Poly (fun a : α => [a]) := by fun_prop
  exact h.reindex Option.some id (fun _ => rfl) (fun _ => rfl)

@[fun_prop] theorem optionToList : Poly (Option.toList : Option α → List α) :=
  identity.reindex Option.toList Option.toList (fun _ => rfl) (fun _ => rfl)

@[fun_prop] theorem optionGetD (a : α) : Poly (fun x : Option α => x.getD a) := by
  have h : Poly (fun x : Option α => x.toList.headD a) := comp _ _ (listHeadD a) optionToList
  exact h.congr (fun x => by cases x <;> rfl)

@[fun_prop] theorem optionIsSome : Poly (Option.isSome : Option α → Bool) := by
  have h : Poly (fun x : Option α => !x.toList.isEmpty) := by fun_prop
  exact h.congr (fun x => by cases x <;> rfl)

@[fun_prop] theorem optionMap [Inhabited α] (f : α → β) (hf : Poly f) :
    Poly (Option.map f) := by
  have h : Poly (fun x : Option α => x.toList.map f) := by fun_prop
  exact h.reindex (Option.map f) id (fun _ => rfl) (fun x => by cases x <;> rfl)

@[fun_prop] theorem optionElim [Inhabited α] (b : β) (f : α → β) (hf : Poly f) :
    Poly (fun x : Option α => x.elim b f) := by
  have h : Poly (fun x : Option α => if x.isSome then f (x.getD default) else b) := by fun_prop
  exact h.congr (fun x => by cases x <;> rfl)

@[fun_prop] theorem sumInl : Poly (Sum.inl : α → Sum α β) := by
  have h : Poly (fun a : α => ([a],([]:List β))) := by fun_prop
  exact h.reindex Sum.inl id (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem sumInr : Poly (Sum.inr : β → Sum α β) := by
  have h : Poly (fun b : β => (([]:List α),[b])) := by fun_prop
  exact h.reindex Sum.inr id (fun _ => rfl) (fun _ => rfl)

@[fun_prop] theorem sumCases [Inhabited α] [Inhabited β]
    (f : α → γ) (g : β → γ) (hf : Poly f) (hg : Poly g) :
    Poly (Sum.elim f g) := by
  let repr : Sum α β → List α×List β :=
    fun x => match x with | .inl a => ([a],[]) | .inr b => ([],[b])
  have h : Poly (fun z : List α×List β => if z.1.isEmpty then g (z.2.headD default)
      else f (z.1.headD default)) := by fun_prop
  exact h.reindex (Sum.elim f g) repr (fun x => by cases x <;> rfl)
    (fun x => by cases x <;> rfl)

end Poly
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma bounded_stops {α : Type} (f : α → α) (active : α → Bool) (rank : α → ℕ)
    (hfix : ∀ a,active a=false → f a=a)
    (hdec : ∀ a,active a=true → rank (f a)+1≤rank a) :
    ∀ n a,rank a≤n → active (f^[n] a)=false := by
  intro n
  induction n with
  | zero =>
    intro a ha
    cases h : active a with
    | false => simpa using h
    | true => have hh := hdec a h; omega
  | succ n ih =>
    intro a ha
    cases h : active a with
    | false => rw [Function.iterate_fixed (hfix a h)]; exact h
    | true =>
      rw [Function.iterate_succ_apply]
      apply ih
      have hh := hdec a h
      omega

def divActive (z : ℕ×(ℕ×ℕ)) : Bool := decide (0<z.1) && decide (z.1≤z.2.1)
def divStep (z : ℕ×(ℕ×ℕ)) : ℕ×(ℕ×ℕ) :=
  if divActive z then (z.1,(z.2.1-z.1,z.2.2+1)) else z

lemma divStep_spec (z : ℕ×(ℕ×ℕ)) :
    (divStep z).1=z.1 ∧ (divStep z).2.1≤z.2.1 ∧ (divStep z).2.2≤z.2.2+1 ∧
      (divStep z).2.1+z.1*(divStep z).2.2=z.2.1+z.1*z.2.2 := by
  unfold divStep
  split_ifs with h
  · have hz : 0<z.1 ∧ z.1≤z.2.1 := by simpa [divActive] using h
    have he := Nat.sub_add_cancel hz.2
    dsimp only
    refine ⟨rfl,Nat.sub_le _ _,le_rfl,?_⟩
    nlinarith
  · simp

lemma divIterate_spec (n : ℕ) (z : ℕ×(ℕ×ℕ)) :
    (divStep^[n] z).1=z.1 ∧ (divStep^[n] z).2.1≤z.2.1 ∧ (divStep^[n] z).2.2≤z.2.2+n ∧
      (divStep^[n] z).2.1+z.1*(divStep^[n] z).2.2=z.2.1+z.1*z.2.2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h₁,h₂,h₃,h₄⟩ := divStep_spec (divStep^[n] z)
    rw [ih.1] at h₁ h₄
    exact ⟨h₁,h₂.trans ih.2.1,by omega,h₄.trans ih.2.2.2⟩

lemma divIterate_stops (n m : ℕ) : divActive (divStep^[n] (m,n,0))=false := by
  apply bounded_stops divStep divActive (fun z => z.2.1)
    (fun z hz => by simp [divStep,hz]) (fun z hz => ?_) n (m,n,0) le_rfl
  have hh : 0<z.1 ∧ z.1≤z.2.1 := by simpa [divActive] using hz
  simp only [divStep,hz,ite_true]
  omega

lemma divIterate_result (n m : ℕ) : (divStep^[n] (m,n,0)).2=(n%m,n/m) := by
  obtain ⟨hm,_,_,hh⟩ := divIterate_spec n (m,n,0)
  have hs := divIterate_stops n m
  by_cases hm0 : m=0
  · subst m
    have hf : divStep (0,n,0)=(0,n,0) := by simp [divStep,divActive]
    rw [Function.iterate_fixed hf]
    simp
  · have hr : (divStep^[n] (m,n,0) ).2.1 < m := by
      have hpos : 0 < m := Nat.pos_of_ne_zero hm0
      simpa [divActive,hm,hpos] using hs
    simp only [Nat.mul_zero,Nat.add_zero] at hh
    have hq : n/m=(divStep^[n] (m,n,0)).2.2 := by
      apply Nat.div_eq_of_lt_le
      · nlinarith
      · nlinarith
    apply Prod.ext
    · have hn := Nat.mod_add_div n m
      rw [hq] at hn
      omega
    · exact hq.symm

namespace Poly
@[fun_prop] theorem natDivMod : Poly (fun z : ℕ×ℕ => (z.1%z.2,z.1/z.2)) := by
  have hs : Poly divStep := by unfold divStep divActive; fun_prop
  have hi : Poly (fun z : ℕ×(ℕ×(ℕ×ℕ)) => divStep^[z.1] z.2) :=
    boundedIterate divStep hs X (by
      intro z j hj
      obtain ⟨h₁,h₂,h₃,_⟩ := divIterate_spec j z.2
      simp only [encode_prod,pairBits_length,encode_nat,unary_length,eval_X,h₁]
      omega)
  have hh : Poly (fun z : ℕ×ℕ => (divStep^[z.1] (z.2,z.1,0)).2) := by fun_prop
  exact hh.congr (fun z => divIterate_result z.1 z.2)

@[fun_prop] theorem natDiv : Poly (fun z : ℕ×ℕ => z.1/z.2) := by
  have h : Poly (fun z : ℕ×ℕ => (z.1%z.2,z.1/z.2).2) := second _ natDivMod
  exact h
@[fun_prop] theorem natMod : Poly (fun z : ℕ×ℕ => z.1%z.2) := by
  have h : Poly (fun z : ℕ×ℕ => (z.1%z.2,z.1/z.2).1) := first _ natDivMod
  exact h
end Poly
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

def intParts (z : ℤ) : Bool×ℕ := (decide (z<0),z.natAbs)
def fromParts (p : Bool×ℕ) : ℤ := if p.1 then -(p.2:ℤ) else p.2
instance : Coding ℤ := ⟨fun z => encode (intParts z)⟩
@[simp] lemma encode_int (z : ℤ) : encode z=encode (intParts z) := rfl
lemma fromParts_parts (z : ℤ) : fromParts (intParts z)=z := by
  simp only [fromParts,intParts,decide_eq_true_eq]
  split_ifs with h
  · exact (Int.eq_neg_natAbs_of_nonpos (le_of_lt h)).symm
  · exact Int.natAbs_of_nonneg (le_of_not_gt h)

lemma intParts_nat (n : ℕ) : intParts (n:ℤ)=(false,n) := by
  have h : ¬ (n:ℤ)<0 := by omega
  simp [intParts,h]
lemma intParts_fromParts (p : Bool×ℕ) :
    intParts (fromParts p)=(p.1 && !(decide (p.2=0)),p.2) := by
  rcases p with ⟨b,n⟩
  cases b with
  | false => simp [fromParts,intParts_nat]
  | true =>
    by_cases hn : n=0
    · subst n; simp [intParts,fromParts]
    · simp [intParts,fromParts,Nat.pos_iff_ne_zero,hn]

namespace Poly
@[fun_prop] theorem intParts_poly : Poly intParts := by
  exact ⟨(Routine.identity (encode : Bool×ℕ → List Bool)).reindex encode encode intParts intParts
    (fun _ => rfl) (fun _ => rfl)⟩

@[fun_prop] theorem natCastInt : Poly (Int.ofNat : ℕ → ℤ) := by
  have h : Poly (fun n : ℕ => (false,n)) := by fun_prop
  refine ⟨h.routine.reindex encode encode Int.ofNat id (fun _ => rfl) ?_⟩
  intro n
  change encode (false,n)=encode (intParts (n:ℤ))
  rw [intParts_nat]

@[fun_prop] theorem natToInt : Poly (fun n : ℕ => (n:ℤ)) := natCastInt

@[fun_prop] theorem fromParts_poly : Poly fromParts := by
  have h : Poly (fun p : Bool×ℕ => (p.1 && !(decide (p.2=0)),p.2)) := by
    apply pair
    · exact comp _ _ boolAnd (pair _ _ (by fun_prop) (comp _ _ boolNot (comp _ _ natZeroTest (by fun_prop))))
    · fun_prop
  refine ⟨h.routine.reindex encode encode fromParts id (fun _ => rfl) ?_⟩
  intro p
  simp only [id_eq,encode_int,intParts_fromParts]

@[fun_prop] theorem intNatAbs : Poly (Int.natAbs : ℤ → ℕ) := by
  have h : Poly (fun z : ℤ => (intParts z).2) := second _ intParts_poly
  exact h

@[fun_prop] theorem intSign : Poly (fun z : ℤ => decide (z<0)) := by
  have h : Poly (fun z : ℤ => (intParts z).1) := first _ intParts_poly
  exact h

@[fun_prop] theorem intNeg : Poly (fun z : ℤ => -z) := by
  have h : Poly (fun z : ℤ => fromParts (!(intParts z).1,(intParts z).2)) := by fun_prop
  exact h.congr (fun z => by cases z <;> simp [intParts,fromParts])

def addParts (p : (Bool×ℕ)×(Bool×ℕ)) : ℤ :=
  if p.1.1 then
    if p.2.1 then fromParts (true,p.1.2+p.2.2)
    else if decide (p.2.2≤p.1.2) then fromParts (true,p.1.2-p.2.2)
    else fromParts (false,p.2.2-p.1.2)
  else if p.2.1 then
    if decide (p.1.2≤p.2.2) then fromParts (true,p.2.2-p.1.2)
    else fromParts (false,p.1.2-p.2.2)
  else fromParts (false,p.1.2+p.2.2)

lemma addParts_eq (p q : Bool×ℕ) : addParts (p,q)=fromParts p+fromParts q := by
  rcases p with ⟨b,n⟩; rcases q with ⟨c,m⟩
  cases b <;> cases c <;> simp only [addParts,fromParts,Bool.false_eq_true,ite_false,ite_true,
    decide_eq_true_eq]
  · omega
  · split_ifs <;> omega
  · split_ifs <;> omega
  · omega

@[fun_prop] theorem intAdd : Poly (fun z : ℤ×ℤ => z.1+z.2) := by
  have ha : Poly addParts := by unfold addParts; fun_prop
  have h : Poly (fun z : ℤ×ℤ => addParts (intParts z.1,intParts z.2)) := by fun_prop
  exact h.congr (fun z => by rw [addParts_eq,fromParts_parts,fromParts_parts])

@[fun_prop] theorem intSub : Poly (fun z : ℤ×ℤ => z.1-z.2) := by
  have h : Poly (fun z : ℤ×ℤ => z.1+ -z.2) := by fun_prop
  exact h.congr (fun z => sub_eq_add_neg _ _)

@[fun_prop] theorem intMul : Poly (fun z : ℤ×ℤ => z.1*z.2) := by
  have hm : Poly (fun p : (Bool×ℕ)×(Bool×ℕ) => fromParts
      (if p.1.1 then !p.2.1 else p.2.1,p.1.2*p.2.2)) := by fun_prop
  have hp : Poly (fun z : ℤ×ℤ => (intParts z.1,intParts z.2)) :=
    pair _ _ (comp _ Prod.fst intParts_poly (first _ identity))
      (comp _ Prod.snd intParts_poly (second _ identity))
  have h := comp _ _ hm hp
  have he (p q : Bool×ℕ) :
      fromParts (if p.1 then !q.1 else q.1,p.2*q.2)=fromParts p*fromParts q := by
    rcases p with ⟨b,n⟩; rcases q with ⟨c,m⟩
    cases b <;> cases c <;> simp [fromParts]
  exact h.congr (fun z => by dsimp only; rw [he,fromParts_parts,fromParts_parts])

@[fun_prop] theorem intLE : Poly (fun z : ℤ×ℤ => decide (z.1≤z.2)) := by
  have h : Poly (fun z : ℤ×ℤ => !(decide (z.2-z.1<0))) := by
    exact comp _ _ boolNot (comp _ _ intSign (comp _ (fun z : ℤ×ℤ => (z.2,z.1)) intSub (by fun_prop)))
  exact h.congr (fun z => by simp [←decide_not,sub_neg])

@[fun_prop] theorem intLT : Poly (fun z : ℤ×ℤ => decide (z.1<z.2)) := by
  have h : Poly (fun z : ℤ×ℤ => decide (z.1-z.2<0)) := comp _ _ intSign intSub
  exact h.congr (fun z => by simp [sub_neg])

@[fun_prop] theorem intEQ : Poly (fun z : ℤ×ℤ => decide (z.1=z.2)) := by
  have h : Poly (fun z : ℤ×ℤ => decide ((z.1-z.2).natAbs=0)) :=
    comp _ _ natZeroTest (comp _ _ intNatAbs intSub)
  exact h.congr (fun z => by simp [sub_eq_zero])

@[fun_prop] theorem intMin : Poly (fun z : ℤ×ℤ => min z.1 z.2) := by
  have h : Poly (fun z : ℤ×ℤ => if decide (z.1≤z.2) then z.1 else z.2) := by fun_prop
  exact h.congr (fun z => by simp [min_def])
@[fun_prop] theorem intMax : Poly (fun z : ℤ×ℤ => max z.1 z.2) := by
  have h : Poly (fun z : ℤ×ℤ => if decide (z.1≤z.2) then z.2 else z.1) := by fun_prop
  exact h.congr (fun z => by simp [max_def])
@[fun_prop] theorem intToNat : Poly (Int.toNat : ℤ → ℕ) := by
  have h : Poly (fun z : ℤ => if (intParts z).1 then 0 else (intParts z).2) := by fun_prop
  exact h.congr (fun z => by cases z <;> simp [intParts])
variable {α : Type} [Coding α]
@[fun_prop] theorem intLt_apply (f g : α → ℤ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a<g a)) := comp _ _ intLT (pair _ _ hf hg)
@[fun_prop] theorem intLe_apply (f g : α → ℤ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a≤g a)) := comp _ _ intLE (pair _ _ hf hg)
end Poly
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma code_option_none {α : Type} [Coding α] : encode (none:Option α)=[] := rfl
lemma code_option_some {α : Type} [Coding α] (a : α) :
    (encode (some a)).length=2*(encode a).length+1 := by
  change (encode ([a]:List α)).length=_
  simp

lemma fold_code_additive {α β : Type} [Coding α] [Coding β]
    (f : β×α → β) (C : ℕ)
    (hf : ∀ z,(encode (f z)).length≤(encode z.1).length+C*(2*(encode z.2).length+1))
    (l : List α) (b : β) :
    (encode (l.foldl (fun b a => f (b,a)) b)).length≤
      (encode b).length+C*(encode l).length := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    have h := hf (b,a)
    have hi := ih (f (b,a))
    simp only [List.foldl_cons,code_cons,pairBits_length]
    nlinarith

namespace Poly
variable {α β : Type} [Coding α] [Coding β]

theorem listFoldAdd [Inhabited α] (f : β×α → β) (hf : Poly f) (C : ℕ)
    (hb : ∀ z,(encode (f z)).length≤(encode z.1).length+C*(2*(encode z.2).length+1)) :
    Poly (fun z : List α×β => z.1.foldl (fun b a => f (b,a)) z.2) := by
  apply listFold default f hf ((Polynomial.C C+1)*X)
  intro z k
  have hh := fold_code_additive f C hb (z.1.take k) z.2
  have ht := code_take_le z.1 k
  have hm := Nat.mul_le_mul_left C ht
  simp only [encode_prod,pairBits_length,eval_mul,eval_add,eval_C,eval_one,eval_X]
  nlinarith

@[fun_prop] theorem listDrop : Poly (fun z : ℕ×List α => z.2.drop z.1) := by
  have hi := boundedIterate (List.tail:List α → List α) listTail X (by
    intro z j hj
    have he : ∀ (k : ℕ) (l : List α),List.tail^[k] l=l.drop k := by
      intro k l
      induction k with
      | zero => simp
      | succ k ih => simp [Function.iterate_succ_apply',ih,List.tail_drop]
    rw [he]
    have hh := code_drop_le z.2 j
    simp only [encode_prod,pairBits_length,eval_X]
    omega)
  apply hi.congr
  intro z
  induction z.1 generalizing z with
  | zero => simp
  | succ k ih => simp [Function.iterate_succ_apply',ih,List.tail_drop]

@[fun_prop] theorem listGetD (a : α) : Poly (fun z : List α×ℕ => z.1[z.2]?.getD a) := by
  have h : Poly (fun z : List α×ℕ => (z.1.drop z.2).headD a) := by fun_prop
  exact h.congr (fun z => by simp only [List.headD_eq_head?_getD,List.head?_drop])

@[fun_prop] theorem listNatSum : Poly (List.sum : List ℕ → ℕ) := by
  have hfold := listFoldAdd (fun z : ℕ×ℕ => z.1+z.2) natAdd 1 (by
    intro z; simp only [encode_nat,unary_length]; omega)
  have h : Poly (fun l : List ℕ => l.foldl (·+·) 0) := comp _ (fun l : List ℕ => (l,0)) hfold (by fun_prop)
  exact h.congr (fun l => by simp [List.sum_eq_foldl])

@[fun_prop] theorem listIntSum : Poly (List.sum : List ℤ → ℤ) := by
  have hfold := listFoldAdd (fun z : ℤ×ℤ => z.1+z.2) intAdd 1 (by
    intro z
    have h := Int.natAbs_add_le z.1 z.2
    simp only [encode_int,encode_prod,pairBits_length,intParts,encode_bool,List.length_singleton,
      encode_nat,unary_length]
    omega)
  have h : Poly (fun l : List ℤ => l.foldl (·+·) 0) := comp _ (fun l : List ℤ => (l,0)) hfold (by fun_prop)
  exact h.congr (fun l => by simp [List.sum_eq_foldl])

end Poly

def rangeStep (z : ℕ×List ℕ) : ℕ×List ℕ := (z.1+1,z.2++[z.1])
lemma rangeStep_iterate (k : ℕ) (z : ℕ×List ℕ) :
    rangeStep^[k] z=(z.1+k,z.2++List.range' z.1 k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp [Function.iterate_succ_apply',ih,rangeStep,List.range'_concat,List.append_assoc,Nat.add_assoc]

namespace Poly
@[fun_prop] theorem listRange : Poly List.range := by
  have hs : Poly rangeStep := by unfold rangeStep; fun_prop
  have hi : Poly (fun z : ℕ×(ℕ×List ℕ) => rangeStep^[z.1] z.2) :=
    boundedIterate rangeStep hs (8*(X+1)^2) (by
      intro z j hj
      rw [rangeStep_iterate]
      have hb := list_code_bound (List.range' z.2.1 j) (z.2.1+j) (by
        intro a ha
        obtain ⟨i,hi,he⟩ := List.mem_range'.mp ha
        simp only [encode_nat,unary_length]
        omega)
      simp only [List.length_range'] at hb
      simp only [encode_prod,pairBits_length,encode_nat,unary_length,code_append,List.length_append,
        eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
      nlinarith [Nat.mul_le_mul hj hj, Nat.mul_le_mul_right z.2.1 hj])
  have h : Poly (fun n : ℕ => (rangeStep^[n] (0,[])).2) := by fun_prop
  exact h.congr (fun n => by simp [rangeStep_iterate,List.range_eq_range'])
end Poly
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.UnitFlow
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Matrix (V : Type*) := V → V → ℤ

def divergence (b : Matrix V) (i : V) : ℤ := ∑ j, b i j

def cutCapacity (c : V → V → ℕ) (S : Finset V) : ℕ :=
  ∑ i ∈ S, ∑ j ∈ Sᶜ, c i j

def cutFlow (b : Matrix V) (S : Finset V) : ℤ :=
  ∑ i ∈ S, ∑ j ∈ Sᶜ, b i j

structure Feasible (c : V → V → ℕ) (a z : V) (b : Matrix V) : Prop where
  antisymm : ∀ i j, b i j = -b j i
  capacity : ∀ i j, b i j ≤ c i j
  conservation : ∀ i, i ≠ a → i ≠ z → divergence b i = 0

omit [DecidableEq V] in
lemma feasible_zero (c : V → V → ℕ) (a z : V) :
    Feasible c a z (fun _ _ => 0) where
  antisymm _ _ := by simp
  capacity _ _ := by positivity
  conservation _ _ _ := by simp [divergence]

omit [Fintype V] [DecidableEq V] in
lemma antisymm_internal (b : Matrix V) (h : ∀ i j, b i j = -b j i)
    (S : Finset V) : (∑ i ∈ S, ∑ j ∈ S, b i j) = 0 := by
  have hh : (∑ i ∈ S, ∑ j ∈ S, b i j) = -(∑ i ∈ S, ∑ j ∈ S, b i j) := by
    calc
      _ = ∑ i ∈ S, ∑ j ∈ S, -b j i := by
        apply sum_congr rfl; intro i hi
        apply sum_congr rfl; intro j hj
        exact h i j
      _ = -(∑ i ∈ S, ∑ j ∈ S, b j i) := by simp
      _ = _ := by rw [sum_comm]
  omega

lemma divergence_cut (b : Matrix V) (h : ∀ i j, b i j = -b j i)
    (S : Finset V) : (∑ i ∈ S, divergence b i) = cutFlow b S := by
  have split : ∀ i, divergence b i = (∑ j ∈ S, b i j) + ∑ j ∈ Sᶜ, b i j := by
    intro i
    exact (sum_add_sum_compl S (fun j => b i j)).symm
  simp_rw [split]
  rw [sum_add_distrib, antisymm_internal b h S, zero_add]
  rfl

lemma source_cut {c : V → V → ℕ} {a z : V} {b : Matrix V}
    (h : Feasible c a z b) (S : Finset V) (ha : a ∈ S) (hz : z ∉ S) :
    cutFlow b S = divergence b a := by
  rw [← divergence_cut b h.antisymm]
  exact sum_eq_single a (fun i hi hia => h.conservation i hia (by intro e; subst i; exact hz hi))
    (fun hna => (hna ha).elim)

lemma cutFlow_le_capacity {c : V → V → ℕ} {b : Matrix V}
    (h : ∀ i j, b i j ≤ c i j) (S : Finset V) :
    cutFlow b S ≤ cutCapacity c S := by
  simp only [cutFlow, cutCapacity, Nat.cast_sum]
  exact sum_le_sum (fun i _ => sum_le_sum (fun j _ => h i j))

lemma weak_duality {c : V → V → ℕ} {a z : V} {b : Matrix V}
    (h : Feasible c a z b) (S : Finset V) (ha : a ∈ S) (hz : z ∉ S) :
    divergence b a ≤ cutCapacity c S := by
  rw [← source_cut h S ha hz]
  exact cutFlow_le_capacity h.capacity S

lemma saturated_minimum {c : V → V → ℕ} {a z : V} {b : Matrix V}
    (h : Feasible c a z b) (S : Finset V) (ha : a ∈ S) (hz : z ∉ S)
    (hsat : ∀ i ∈ S, ∀ j ∉ S, b i j = c i j) :
    ∀ T : Finset V, a ∈ T → z ∉ T → cutCapacity c S ≤ cutCapacity c T := by
  have heq : cutFlow b S = cutCapacity c S := by
    simp only [cutFlow, cutCapacity, Nat.cast_sum]
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro j hj
    exact hsat i hi j (mem_compl.mp hj)
  intro T hTa hTz
  have := weak_duality h T hTa hTz
  rw [← source_cut h S ha hz, heq] at this
  exact_mod_cast this

omit [DecidableEq V] in
lemma source_bound {c : V → V → ℕ} {a z : V} {b : Matrix V}
    (h : Feasible c a z b) : divergence b a ≤ ∑ j, (c a j : ℤ) :=
  sum_le_sum (fun j _ => h.capacity a j)

def arc (u v : V) : Matrix V := fun i j =>
  (if i=u ∧ j=v then 1 else 0) - (if i=v ∧ j=u then 1 else 0)

omit [Fintype V] in
lemma arc_antisymm (u v i j : V) : arc u v i j = -arc u v j i := by
  simp only [arc]
  have h₁ : (i=u ∧ j=v) ↔ (j=v ∧ i=u) := and_comm
  have h₂ : (i=v ∧ j=u) ↔ (j=u ∧ i=v) := and_comm
  simp only [h₁, h₂]
  ring

lemma arc_divergence (u v i : V) : divergence (arc u v) i =
    (if i=u then 1 else 0) - (if i=v then 1 else 0) := by
  simp only [divergence, arc, sum_sub_distrib]
  simp_rw [ite_and]
  simp

def pathFlow : List V → Matrix V
  | [] => fun _ _ => 0
  | [_] => fun _ _ => 0
  | v::u::p => fun i j => pathFlow (u::p) i j + arc u v i j

omit [Fintype V] in
lemma pathFlow_antisymm (p : List V) (i j : V) :
    pathFlow p i j = -pathFlow p j i := by
  induction p using List.twoStepInduction with
  | nil => simp [pathFlow]
  | singleton v => simp [pathFlow]
  | cons_cons v u p _ ih =>
    simp only [pathFlow]
    rw [ih, arc_antisymm]
    ring

lemma pathFlow_divergence (p : List V) (i : V) :
    divergence (pathFlow p) i =
      (if p.getLast? = some i then 1 else 0) -
      (if p.head? = some i then 1 else 0) := by
  induction p using List.twoStepInduction with
  | nil => simp [pathFlow, divergence]
  | singleton v => simp [pathFlow, divergence]
  | cons_cons v u p _ ih =>
    rw [show divergence (pathFlow (v::u::p)) i =
        divergence (pathFlow (u::p)) i + divergence (arc u v) i by
      simp [divergence, pathFlow, sum_add_distrib]]
    rw [ih, arc_divergence]
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_cons_cons]
    by_cases hiu : i=u <;> by_cases hiv : i=v <;> simp_all [eq_comm, sub_eq_add_neg]

omit [Fintype V] in
lemma pathFlow_zero_of_not_mem (p : List V) (i j : V) (hi : i ∉ p) :
    pathFlow p i j = 0 := by
  induction p using List.twoStepInduction with
  | nil => rfl
  | singleton v => rfl
  | cons_cons v u p _ ih =>
    have hiv : i ≠ v := by intro hh; exact hi (by simp [hh])
    have hit : i ∉ u::p := by intro hh; exact hi (List.mem_cons_of_mem _ hh)
    have hiu : i ≠ u := by intro hh; exact hit (by simp [hh])
    simp [pathFlow, ih u hit, arc, hiv, hiu]

omit [Fintype V] in
lemma pathFlow_le_one (p : List V) (hp : p.Nodup) (i j : V) : pathFlow p i j ≤ 1 := by
  induction p using List.twoStepInduction with
  | nil => simp [pathFlow]
  | singleton v => simp [pathFlow]
  | cons_cons v u p _ ih =>
    have hv : v ∉ u::p := hp.notMem
    have htail := ih u hp.of_cons
    by_cases hiv : i = v
    · subst i
      simp only [pathFlow]
      rw [pathFlow_zero_of_not_mem _ _ _ hv]
      simp only [arc]
      split_ifs <;> omega
    · by_cases hjv : j = v
      · subst j
        have hz : pathFlow (u::p) i v = 0 := by
          rw [pathFlow_antisymm, pathFlow_zero_of_not_mem _ _ _ hv, neg_zero]
        simp only [pathFlow]
        rw [hz]
        simp only [arc]
        split_ifs <;> omega
      · simpa [pathFlow, arc, hiv, hjv] using htail

omit [Fintype V] in
lemma pathFlow_pos_relation (R : V → V → Prop) (p : List V) (hp : p.Nodup)
    (hc : p.IsChain (fun v u => R u v)) (i j : V) (hij : 0 < pathFlow p i j) :
    R i j := by
  induction p using List.twoStepInduction with
  | nil => simp [pathFlow] at hij
  | singleton v => simp [pathFlow] at hij
  | cons_cons v u p _ ih =>
    have hv : v ∉ u::p := hp.notMem
    have huv : u ≠ v := by intro e; exact hv (by simp [e])
    have ht : (u::p).IsChain (fun v u => R u v) := hc.tail
    have hr : R u v := (List.isChain_cons_cons.mp hc).1
    by_cases hiv : i = v
    · subst i
      simp only [pathFlow] at hij
      rw [pathFlow_zero_of_not_mem _ _ _ hv] at hij
      simp only [arc] at hij
      by_cases hju : j=u <;> simp [huv, huv.symm, hju] at hij
    · by_cases hjv : j = v
      · subst j
        have hz : pathFlow (u::p) i v = 0 := by
          rw [pathFlow_antisymm, pathFlow_zero_of_not_mem _ _ _ hv, neg_zero]
        simp only [pathFlow] at hij
        rw [hz] at hij
        by_cases hiu : i=u
        · simpa [hiu] using hr
        · simp [arc, hiu, hiv] at hij
      · apply ih u hp.of_cons ht
        simpa [pathFlow, arc, hiv, hjv] using hij

lemma augment_feasible {c : V → V → ℕ} {a z : V} {b : Matrix V}
    (hb : Feasible c a z b) (p : List V) (hp : p.Nodup)
    (hc : p.IsChain (fun v u => b u v < c u v))
    (hhead : p.head? = some z) (hlast : p.getLast? = some a) :
    Feasible c a z (fun i j => b i j + pathFlow p i j) where
  antisymm i j := by rw [hb.antisymm, pathFlow_antisymm]; ring
  capacity i j := by
    have hcap := hb.capacity i j
    by_cases hpos : 0 < pathFlow p i j
    · have hres := pathFlow_pos_relation (fun u v => b u v < c u v) p hp hc i j hpos
      have hle := pathFlow_le_one p hp i j
      omega
    · omega
  conservation i hia hiz := by
    simp only [divergence, sum_add_distrib]
    change divergence b i + divergence (pathFlow p) i = 0
    rw [hb.conservation i hia hiz, pathFlow_divergence, hhead, hlast]
    simp [Ne.symm hia, Ne.symm hiz]

lemma augment_value {a z : V} (haz : a ≠ z) (b : Matrix V) (p : List V)
    (hhead : p.head? = some z) (hlast : p.getLast? = some a) :
    divergence (fun i j => b i j + pathFlow p i j) a = divergence b a + 1 := by
  simp only [divergence, sum_add_distrib]
  change divergence b a + divergence (pathFlow p) a = _
  rw [pathFlow_divergence, hhead, hlast]
  simp [Ne.symm haz, divergence]

end BinaryMatching.UnitFlow
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.CutAlgebra
open Finset UnitFlow
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

abbrev cross (S : Finset V) (i j : V) : Prop := i∈S ∧ j∉S

lemma cutCapacity_eq (c : V → V → ℕ) (S : Finset V) :
    cutCapacity c S = ∑ i, ∑ j, if cross S i j then c i j else 0 := by
  simp only [cutCapacity,cross,ite_and]
  simp [Finset.sum_ite_irrel]
  apply sum_congr rfl; intro i hi
  have hSc : Sᶜ = univ.filter (fun j => j∉S) := by ext j; simp
  rw [hSc,sum_filter]
  simp

lemma cut_compl (c : V → V → ℕ) (hc : ∀ i j, c i j=c j i) (S : Finset V) :
    cutCapacity c Sᶜ = cutCapacity c S := by
  rw [cutCapacity_eq,cutCapacity_eq,sum_comm]
  apply sum_congr rfl; intro i hi
  apply sum_congr rfl; intro j hj
  simp only [cross,mem_compl,not_not]
  rw [hc j i]
  by_cases his : i∈S <;> by_cases hjs : j∈S <;> simp [his,hjs]

lemma cut_submodular (c : V → V → ℕ) (S A : Finset V) :
    cutCapacity c (S∩A) + cutCapacity c (S∪A) ≤ cutCapacity c S + cutCapacity c A := by
  simp only [cutCapacity_eq,← sum_add_distrib]
  apply sum_le_sum; intro i hi
  apply sum_le_sum; intro j hj
  by_cases his : i∈S <;> by_cases hia : i∈A <;>
    by_cases hjs : j∈S <;> by_cases hja : j∈A <;>
    simp [cross,his,hia,hjs,hja]

def push (c : V → V → ℕ) (f : V → W) (i j : W) : ℕ :=
  if i=j then 0 else ∑ u, ∑ v, if f u=i ∧ f v=j then c u v else 0

def lift (f : V → W) (T : Finset W) : Finset V := univ.filter (fun v => f v∈T)

omit [DecidableEq V] [Fintype W] in
lemma mem_lift (f : V → W) (T : Finset W) (v : V) : v∈lift f T ↔ f v∈T := by
  simp [lift]

omit [DecidableEq V] [Fintype W] in
lemma push_symm (c : V → V → ℕ) (hc : ∀ i j, c i j=c j i) (f : V → W) :
    ∀ i j, push c f i j=push c f j i := by
  intro i j
  by_cases hij : i=j
  · subst j; rfl
  simp only [push,ite_eq_right hij,ite_eq_right (Ne.symm hij)]
  rw [sum_comm]
  apply sum_congr rfl; intro u hu
  apply sum_congr rfl; intro v hv
  rw [hc v u]
  simp only [and_comm]

omit [DecidableEq V] [Fintype W] in
lemma push_diag (c : V → V → ℕ) (f : V → W) (i : W) : push c f i i=0 := by
  simp [push]

omit [DecidableEq V] [DecidableEq W] in
lemma sum_four_swap (h : W → W → V → V → ℕ) :
    (∑ i, ∑ j, ∑ u, ∑ v, h i j u v) = ∑ u, ∑ v, ∑ i, ∑ j, h i j u v := by
  calc
    _ = ∑ i, ∑ u, ∑ j, ∑ v, h i j u v := by
      apply sum_congr rfl; intro i hi
      rw [sum_comm]
    _ = ∑ u, ∑ i, ∑ j, ∑ v, h i j u v := by rw [sum_comm]
    _ = ∑ u, ∑ i, ∑ v, ∑ j, h i j u v := by
      apply sum_congr rfl; intro u hu
      apply sum_congr rfl; intro i hi
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl; intro u hu
      rw [sum_comm]

lemma cut_push (c : V → V → ℕ) (f : V → W) (T : Finset W) :
    cutCapacity (push c f) T = cutCapacity c (lift f T) := by
  rw [cutCapacity_eq,cutCapacity_eq]
  have he : ∀ i j, (if cross T i j then push c f i j else 0) =
      ∑ u, ∑ v, if cross T (f u) (f v) ∧ f u=i ∧ f v=j then c u v else 0 := by
    intro i j
    by_cases hh : cross T i j
    · have hij : i≠j := by intro h; subst j; exact hh.2 hh.1
      simp only [ite_eq_left hh,push,ite_eq_right hij]
      apply sum_congr rfl; intro u hu
      apply sum_congr rfl; intro v hv
      by_cases hui : f u=i <;> by_cases hvj : f v=j <;> simp_all
    · simp only [ite_eq_right hh]
      symm
      apply sum_eq_zero; intro u hu
      apply sum_eq_zero; intro v hv
      by_cases hui : f u=i <;> by_cases hvj : f v=j <;> simp_all
  simp_rw [he]
  rw [sum_four_swap]
  apply sum_congr rfl; intro u hu
  apply sum_congr rfl; intro v hv
  simp only [cross,mem_lift]
  by_cases hh : f u∈T ∧ f v∉T
  · simp only [hh,true_and]
    simp [ite_and,Finset.sum_ite_irrel,eq_comm]
  · simp [hh]

omit [DecidableEq V] in

lemma push_total_le (c : V → V → ℕ) (f : V → W) :
    (∑ i, ∑ j, push c f i j) ≤ ∑ u, ∑ v, c u v := by
  calc
    _ ≤ ∑ i, ∑ j, ∑ u, ∑ v, if f u=i ∧ f v=j then c u v else 0 := by
      apply sum_le_sum; intro i hi
      apply sum_le_sum; intro j hj
      simp only [push]
      split_ifs <;> omega
    _ = _ := by
      rw [sum_four_swap]
      apply sum_congr rfl; intro u hu
      apply sum_congr rfl; intro v hv
      simp [ite_and,Finset.sum_ite_irrel,eq_comm]

end BinaryMatching.CutAlgebra
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.ResidualSearch
open Finset
variable {n : ℕ}
abbrev Table (n : ℕ) := Fin n → Option (List (Fin n))

def initial (a : Fin n) : Table n := fun v => if v=a then some [a] else none

def predecessor (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (v : Fin n) : Option (Fin n) :=
  (List.finRange n).find? (fun u => decide (R u v) && (p u).isSome)

def step (R : Fin n → Fin n → Prop) [DecidableRel R] (p : Table n) : Table n :=
  fun v => match p v with
  | some l => some l
  | none => match predecessor R p v with
    | none => none
    | some u => (p u).map (fun l => v::l)

def search (R : Fin n → Fin n → Prop) [DecidableRel R] (a : Fin n) : ℕ → Table n
  | 0 => initial a
  | k+1 => step R (search R a k)

def reached (p : Table n) : Finset (Fin n) := univ.filter (fun v => (p v).isSome)

def Closed (R : Fin n → Fin n → Prop) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v, R u v → v ∈ S

structure Good (R : Fin n → Fin n → Prop) (a : Fin n) (p : Table n) : Prop where
  head : ∀ v l, p v=some l → l.head?=some v
  last : ∀ v l, p v=some l → l.getLast?=some a
  simple : ∀ v l, p v=some l → l.Nodup
  chain : ∀ v l, p v=some l → l.IsChain (fun v u => R u v)
  visited : ∀ v l, p v=some l → ∀ u∈l, (p u).isSome

lemma mem_reached (p : Table n) (v : Fin n) : v∈reached p ↔ (p v).isSome := by
  simp [reached]

lemma predecessor_some (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (v u : Fin n) (h : predecessor R p v=some u) :
    R u v ∧ (p u).isSome := by
  have := List.find?_some h
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using this

lemma predecessor_exists (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (v : Fin n) :
    (predecessor R p v).isSome ↔ ∃ u, R u v ∧ (p u).isSome := by
  simp [predecessor, List.find?_isSome, Bool.and_eq_true]

lemma step_old (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (v : Fin n) (l : List (Fin n)) (h : p v=some l) :
    step R p v=some l := by simp [step, h]

lemma step_some (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (v : Fin n) (l : List (Fin n)) (h : step R p v=some l) :
    p v=some l ∨ (p v=none ∧ ∃ u t, p u=some t ∧ R u v ∧ l=v::t) := by
  unfold step at h
  cases he : p v with
  | some t => simp only [he] at h; exact Or.inl h
  | none =>
    simp only [he] at h
    cases hu : predecessor R p v with
    | none => simp [hu] at h
    | some u =>
      have hh := predecessor_some R p v u hu
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hh.2
      simp [hu, ht] at h
      exact Or.inr ⟨rfl, u, t, ht, hh.1, h.symm⟩

lemma step_reached (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (v : Fin n) :
    v∈reached (step R p) ↔ v∈reached p ∨ ∃ u∈reached p, R u v := by
  simp only [mem_reached]
  constructor
  · intro h
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp h
    rcases step_some R p v l hl with ho | ⟨_,u,t,ht,hr,_⟩
    · exact Or.inl (by simp [ho])
    · exact Or.inr ⟨u, by simp [ht], hr⟩
  · rintro (ho | ⟨u,hu,hr⟩)
    · obtain ⟨l,hl⟩ := Option.isSome_iff_exists.mp ho
      simp [step_old R p v l hl]
    · cases hv : p v with
      | some l => simp [step_old R p v l hv]
      | none =>
        have hh : (predecessor R p v).isSome := (predecessor_exists R p v).2 ⟨u,hr,hu⟩
        obtain ⟨w,hw⟩ := Option.isSome_iff_exists.mp hh
        obtain ⟨l,hl⟩ := Option.isSome_iff_exists.mp (predecessor_some R p v w hw).2
        simp [step,hv,hw,hl]

lemma reached_mono (R : Fin n → Fin n → Prop) [DecidableRel R] (p : Table n) :
    reached p ⊆ reached (step R p) := fun v hv => (step_reached R p v).2 (Or.inl hv)

lemma good_initial (R : Fin n → Fin n → Prop) (a : Fin n) : Good R a (initial a) := by
  constructor
  all_goals intro v l h; by_cases hv : v=a
  all_goals simp [initial,hv] at h
  all_goals subst v; subst l
  · rfl
  · rfl
  · simp
  · simp
  · intro u hu; simpa [initial] using hu

lemma good_step (R : Fin n → Fin n → Prop) [DecidableRel R]
    (a : Fin n) (p : Table n) (hp : Good R a p) : Good R a (step R p) := by
  have hpaths : ∀ v l, step R p v=some l →
      l.head?=some v ∧ l.getLast?=some a ∧ l.Nodup ∧
      l.IsChain (fun v u => R u v) ∧ ∀ u∈l, (step R p u).isSome := by
    intro v l hl
    rcases step_some R p v l hl with ho | ⟨hv,u,t,ht,hr,hlt⟩
    · refine ⟨hp.head v l ho, hp.last v l ho, hp.simple v l ho, hp.chain v l ho, ?_⟩
      intro u hu
      exact (mem_reached _ _).mp (reached_mono R p ((mem_reached _ _).mpr (hp.visited v l ho u hu)))
    · subst l
      have hvnot : v∉t := by
        intro hh
        have hhv := hp.visited u t ht v hh
        simp [hv] at hhv
      have htnon : t≠[] := by
        intro hnil
        have hh := hp.head u t ht
        simp [hnil] at hh
      refine ⟨rfl, ?_, (hp.simple u t ht).cons hvnot, ?_, ?_⟩
      · cases t with
        | nil => exact (htnon rfl).elim
        | cons w t => simpa only [List.getLast?_cons_cons] using hp.last u (w::t) ht
      · apply (hp.chain u t ht).cons
        intro w hw
        rw [hp.head u t ht] at hw
        simp only [Option.mem_some_iff] at hw
        subst w
        exact hr
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hwt
        · simp [hl]
        · exact (mem_reached _ _).mp (reached_mono R p
            ((mem_reached _ _).mpr (hp.visited u t ht w hwt)))
  exact ⟨fun v l h => (hpaths v l h).1, fun v l h => (hpaths v l h).2.1,
    fun v l h => (hpaths v l h).2.2.1, fun v l h => (hpaths v l h).2.2.2.1,
    fun v l h => (hpaths v l h).2.2.2.2⟩

lemma good_search (R : Fin n → Fin n → Prop) [DecidableRel R] (a : Fin n) (k : ℕ) :
    Good R a (search R a k) := by
  induction k with
  | zero => exact good_initial R a
  | succ k ih => exact good_step R a _ ih

lemma closed_step_eq (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (hc : Closed R (reached p)) : reached (step R p) = reached p := by
  ext v
  rw [step_reached]
  constructor
  · rintro (h | ⟨u,hu,hr⟩)
    · exact h
    · exact hc u hu v hr
  · exact Or.inl

lemma closed_step (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (hc : Closed R (reached p)) : Closed R (reached (step R p)) := by
  rw [closed_step_eq R p hc]
  exact hc

lemma card_increases (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (hc : ¬Closed R (reached p)) :
    (reached p).card < (reached (step R p)).card := by
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨reached_mono R p, ?_⟩
  intro heq
  apply hc
  intro u hu v hr
  rw [heq]
  exact (step_reached R p v).2 (Or.inr ⟨u, hu, hr⟩)

lemma closed_or_card (R : Fin n → Fin n → Prop) [DecidableRel R]
    (a : Fin n) (k : ℕ) :
    Closed R (reached (search R a k)) ∨ k+1 ≤ (reached (search R a k)).card := by
  induction k with
  | zero =>
    right
    apply card_pos.mpr
    refine ⟨a, ?_⟩
    simp [search,mem_reached,initial]
  | succ k ih =>
    by_cases hc : Closed R (reached (search R a k))
    · exact Or.inl (closed_step R _ hc)
    · have hh := ih.resolve_left hc
      have hlt := card_increases R _ hc
      right
      change k+1+1 ≤ (reached (step R (search R a k))).card
      omega

lemma search_closed (R : Fin n → Fin n → Prop) [DecidableRel R] (a : Fin n) :
    Closed R (reached (search R a n)) := by
  rcases closed_or_card R a n with h | h
  · exact h
  · have hc := card_le_univ (reached (search R a n))
    simp only [Fintype.card_fin] at hc
    omega

lemma source_reached (R : Fin n → Fin n → Prop) [DecidableRel R] (a : Fin n) (k : ℕ) :
    a ∈ reached (search R a k) := by
  induction k with
  | zero => simp [search,mem_reached,initial]
  | succ k ih => exact reached_mono R _ ih

lemma search_path (R : Fin n → Fin n → Prop) [DecidableRel R]
    (a z : Fin n) (p : List (Fin n)) (hp : search R a n z = some p) :
    p.head?=some z ∧ p.getLast?=some a ∧ p.Nodup ∧
      p.IsChain (fun v u => R u v) := by
  have h := good_search R a n
  exact ⟨h.head z p hp, h.last z p hp, h.simple z p hp, h.chain z p hp⟩

lemma search_no_path (R : Fin n → Fin n → Prop) [DecidableRel R]
    (a z : Fin n) (hp : search R a n z = none) :
    a∈reached (search R a n) ∧ z∉reached (search R a n) ∧
      Closed R (reached (search R a n)) := by
  exact ⟨source_reached R a n, by simp [mem_reached,hp], search_closed R a⟩

end BinaryMatching.ResidualSearch
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.UnitMincut
open Finset UnitFlow ResidualSearch
variable {n : ℕ}

def residual (c : Fin n → Fin n → ℕ) (b : Matrix (Fin n)) : Fin n → Fin n → Prop :=
  fun i j => b i j < c i j
instance residualDecidable (c : Fin n → Fin n → ℕ) (b : Matrix (Fin n)) :
    DecidableRel (residual c b) := fun _ _ => inferInstanceAs (Decidable (_ < (_ : ℤ)))

def augment (c : Fin n → Fin n → ℕ) (a z : Fin n) (b : Matrix (Fin n)) : Matrix (Fin n) :=
  match search (residual c b) a n z with
  | none => b
  | some p => fun i j => b i j + pathFlow p i j

def iterate (c : Fin n → Fin n → ℕ) (a z : Fin n) : ℕ → Matrix (Fin n)
  | 0 => fun _ _ => 0
  | k+1 => augment c a z (iterate c a z k)

def sourceCapacity (c : Fin n → Fin n → ℕ) (a : Fin n) : ℕ := ∑ j, c a j

def mincut (c : Fin n → Fin n → ℕ) (a z : Fin n) : Finset (Fin n) :=
  let b := iterate c a z (sourceCapacity c a)
  reached (search (residual c b) a n)

lemma augment_of_none (c : Fin n → Fin n → ℕ) (a z : Fin n) (b : Matrix (Fin n))
    (h : search (residual c b) a n z=none) : augment c a z b=b := by
  simp [augment,h]

lemma augment_of_some (c : Fin n → Fin n → ℕ) (a z : Fin n) (b : Matrix (Fin n))
    (p : List (Fin n)) (h : search (residual c b) a n z=some p) :
    augment c a z b = (fun i j => b i j + pathFlow p i j) := by
  simp [augment,h]

lemma augment_preserves (c : Fin n → Fin n → ℕ) (a z : Fin n) (b : Matrix (Fin n))
    (hb : Feasible c a z b) : Feasible c a z (augment c a z b) := by
  cases he : search (residual c b) a n z with
  | none => rwa [augment_of_none c a z b he]
  | some p =>
    rw [augment_of_some c a z b p he]
    obtain ⟨hhead,hlast,hnd,hchain⟩ := search_path (residual c b) a z p he
    exact augment_feasible hb p hnd hchain hhead hlast

lemma iterate_feasible (c : Fin n → Fin n → ℕ) (a z : Fin n) (k : ℕ) :
    Feasible c a z (iterate c a z k) := by
  induction k with
  | zero => exact feasible_zero c a z
  | succ k ih => exact augment_preserves c a z _ ih

lemma iterate_none_or_value (c : Fin n → Fin n → ℕ) (a z : Fin n) (haz : a≠z) (k : ℕ) :
    search (residual c (iterate c a z k)) a n z=none ∨
      divergence (iterate c a z k) a = k := by
  induction k with
  | zero => exact Or.inr (by simp [iterate,divergence])
  | succ k ih =>
    cases he : search (residual c (iterate c a z k)) a n z with
    | none =>
      left
      rwa [iterate,augment_of_none c a z _ he]
    | some p =>
      have hv := ih.resolve_left (by simp [he])
      right
      rw [iterate,augment_of_some c a z _ p he]
      obtain ⟨hhead,hlast,_,_⟩ := search_path (residual c (iterate c a z k)) a z p he
      rw [augment_value haz _ p hhead hlast,hv]
      simp

lemma final_no_path (c : Fin n → Fin n → ℕ) (a z : Fin n) (haz : a≠z) :
    search (residual c (iterate c a z (sourceCapacity c a))) a n z=none := by
  rcases iterate_none_or_value c a z haz (sourceCapacity c a) with h | h
  · exact h
  · cases he : search (residual c (iterate c a z (sourceCapacity c a))) a n z with
    | none => rfl
    | some p =>
      have hfeas := iterate_feasible c a z (sourceCapacity c a + 1)
      have hbound := source_bound hfeas
      rw [iterate,augment_of_some c a z _ p he] at hbound
      obtain ⟨hhead,hlast,_,_⟩ :=
        search_path (residual c (iterate c a z (sourceCapacity c a))) a z p he
      rw [augment_value haz _ p hhead hlast,h] at hbound
      have hc : (sourceCapacity c a : ℤ) = ∑ j, (c a j : ℤ) := by
        simp [sourceCapacity]
      rw [← hc] at hbound
      omega

theorem mincut_correct (c : Fin n → Fin n → ℕ) (a z : Fin n) (haz : a≠z) :
    a∈mincut c a z ∧ z∉mincut c a z ∧
      ∀ T : Finset (Fin n), a∈T → z∉T → cutCapacity c (mincut c a z) ≤ cutCapacity c T := by
  let b := iterate c a z (sourceCapacity c a)
  have hb : Feasible c a z b := iterate_feasible c a z _
  have hn : search (residual c b) a n z=none := final_no_path c a z haz
  obtain ⟨ha,hz,hclosed⟩ := search_no_path (residual c b) a z hn
  refine ⟨ha,hz,saturated_minimum hb _ ha hz ?_⟩
  intro i hi j hj
  apply le_antisymm (hb.capacity i j)
  by_contra hnot
  have hr : residual c b i j := lt_of_not_ge hnot
  exact hj (hclosed i hi j hr)

end BinaryMatching.UnitMincut
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.TerminalMincut
open Finset UnitFlow UnitMincut
variable {n : ℕ}

def Separates (U S : Finset (Fin n)) : Prop :=
  ∃ a∈U, ∃ z∈U, a∈S ∧ z∉S

def pairCuts (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) : List (Finset (Fin n)) :=
  (((List.finRange n).product (List.finRange n)).filter
    (fun az => decide (az.1∈U ∧ az.2∈U ∧ az.1≠az.2))).map
    (fun az => mincut c az.1 az.2)

def terminalCut (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) : Finset (Fin n) :=
  ((pairCuts c U).argmin (cutCapacity c)).getD ∅

lemma mem_pairCuts (c : Fin n → Fin n → ℕ) (U S : Finset (Fin n)) :
    S∈pairCuts c U ↔ ∃ a∈U, ∃ z∈U, a≠z ∧ S=mincut c a z := by
  simp only [pairCuts,List.mem_map,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a,z⟩,⟨_,ha,hz,haz⟩,hS⟩
    exact ⟨a,ha,z,hz,haz,hS.symm⟩
  · rintro ⟨a,ha,z,hz,haz,hS⟩
    exact ⟨(a,z),⟨by simp,ha,hz,haz⟩,hS.symm⟩

lemma pairCuts_nonempty (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) (hU : 2≤U.card) :
    pairCuts c U ≠ [] := by
  obtain ⟨a,ha,z,hz,haz⟩ := Finset.one_lt_card.mp hU
  have hm := (mem_pairCuts c U (mincut c a z)).2 ⟨a,ha,z,hz,haz,rfl⟩
  intro hh
  simp [hh] at hm

lemma terminalCut_mem (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) (hU : 2≤U.card) :
    terminalCut c U∈(pairCuts c U).argmin (cutCapacity c) := by
  have hn := pairCuts_nonempty c U hU
  unfold terminalCut
  cases he : (pairCuts c U).argmin (cutCapacity c) with
  | none => exact (hn (List.argmin_eq_none.mp he)).elim
  | some S => simp

lemma terminalCut_correct (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) (hU : 2≤U.card) :
    Separates U (terminalCut c U) ∧
      ∀ T : Finset (Fin n), Separates U T → cutCapacity c (terminalCut c U) ≤ cutCapacity c T := by
  have hmem := terminalCut_mem c U hU
  obtain ⟨a,ha,z,hz,haz,heq⟩ := (mem_pairCuts c U _).1 (List.argmin_mem hmem)
  constructor
  · obtain ⟨hac,hzc,_⟩ := mincut_correct c a z haz
    exact ⟨a,ha,z,hz,heq.symm ▸ hac,heq.symm ▸ hzc⟩
  · intro T hT
    obtain ⟨u,hu,v,hv,huT,hvT⟩ := hT
    have huv : u≠v := by intro hh; subst v; exact hvT huT
    have hpair := (mem_pairCuts c U (mincut c u v)).2 ⟨u,hu,v,hv,huv,rfl⟩
    exact (List.le_of_mem_argmin hpair hmem).trans ((mincut_correct c u v huv).2.2 T huT hvT)

end BinaryMatching.TerminalMincut
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.OddCutParity
open Finset UnitFlow CutAlgebra TerminalMincut
variable {n : ℕ}

def OddSide (U S : Finset (Fin n)) : Prop := Odd (S∩U).card
instance oddSideDecidable (U S : Finset (Fin n)) : Decidable (OddSide U S) :=
  inferInstanceAs (Decidable (Odd _))

lemma terminal_partition (U A : Finset (Fin n)) :
    (A∩U).card + (Aᶜ∩U).card=U.card := by
  simpa only [sdiff_eq_inter_compl,inter_comm] using card_inter_add_card_sdiff U A

lemma even_other (U A : Finset (Fin n)) (hU : Even U.card) (hA : Even (A∩U).card) :
    Even (Aᶜ∩U).card := by
  have hh := terminal_partition U A
  rw [Nat.even_iff] at hU hA ⊢
  omega

lemma odd_other (U A : Finset (Fin n)) (hU : Even U.card) (hA : OddSide U A) :
    OddSide U Aᶜ := by
  have hh := terminal_partition U A
  rw [Nat.even_iff] at hU
  change Odd (A∩U).card at hA
  change Odd (Aᶜ∩U).card
  rw [Nat.odd_iff] at hA ⊢
  omega

lemma odd_separates (U S : Finset (Fin n)) (hU : Even U.card) (hS : OddSide U S) :
    Separates U S := by
  have hc := odd_other U S hU hS
  have hp : 0<(S∩U).card := by have := Nat.odd_iff.mp hS; omega
  have hpc : 0<(Sᶜ∩U).card := by have := Nat.odd_iff.mp hc; omega
  obtain ⟨a,ha⟩ := card_pos.mp hp
  obtain ⟨z,hz⟩ := card_pos.mp hpc
  exact ⟨a,(mem_inter.mp ha).2,z,(mem_inter.mp hz).2,
    (mem_inter.mp ha).1,mem_compl.mp (mem_inter.mp hz).1⟩

lemma separate_cards (U A : Finset (Fin n)) (hA : Separates U A) :
    0<(A∩U).card ∧ 0<(Aᶜ∩U).card := by
  obtain ⟨a,ha,z,hz,haa,hza⟩ := hA
  exact ⟨card_pos.mpr ⟨a,mem_inter.mpr ⟨haa,ha⟩⟩,
    card_pos.mpr ⟨z,mem_inter.mpr ⟨mem_compl.mpr hza,hz⟩⟩⟩

lemma split_odd (U S A : Finset (Fin n)) (hS : OddSide U S)
    (hnot : ¬OddSide (A∩U) S) : OddSide (Aᶜ∩U) S := by
  have hh := terminal_partition (S∩U) A
  have h₁ : A∩(S∩U)=S∩(A∩U) := by ext v; simp; tauto
  have h₂ : Aᶜ∩(S∩U)=S∩(Aᶜ∩U) := by ext v; simp; tauto
  rw [h₁,h₂] at hh
  simp only [OddSide,Nat.odd_iff] at hS hnot ⊢
  omega

def contractMap (A : Finset (Fin n)) (r : Fin n) (v : Fin n) : Fin n :=
  if v∈A then v else r

lemma lift_contract (A T : Finset (Fin n)) (r : Fin n) :
    lift (contractMap A r) T = if r∈T then (T∩A)∪Aᶜ else T∩A := by
  ext v
  by_cases hv : v∈A <;> by_cases hr : r∈T <;>
    simp [mem_lift,contractMap,hv,hr]

lemma lift_card (U A T : Finset (Fin n)) (r : Fin n) :
    (lift (contractMap A r) T∩U).card =
      (T∩(A∩U)).card + if r∈T then (Aᶜ∩U).card else 0 := by
  rw [lift_contract]
  split_ifs with hr
  · have hd : Disjoint ((T∩A)∩U) (Aᶜ∩U) := by
      apply disjoint_left.mpr
      intro v hv hw
      exact (mem_compl.mp (mem_inter.mp hw).1) (mem_inter.mp (mem_inter.mp hv).1).2
    rw [union_inter_distrib_right,card_union_of_disjoint hd]
    rw [inter_assoc]
  · simp only [inter_assoc,add_zero]

lemma odd_lift_iff (U A T : Finset (Fin n)) (r : Fin n)
    (he : Even (Aᶜ∩U).card) :
    OddSide U (lift (contractMap A r) T) ↔ OddSide (A∩U) T := by
  simp only [OddSide,lift_card,Nat.odd_iff]
  rw [Nat.even_iff] at he
  split_ifs <;> omega

lemma lift_of_subset (A T : Finset (Fin n)) (r : Fin n) (hr : r∉A) (hT : T⊆A) :
    lift (contractMap A r) T=T := by
  have hrt : r∉T := fun h => hr (hT h)
  rw [lift_contract,ite_eq_right hrt,inter_eq_left.mpr hT]

lemma cut_contract_subset (c : Fin n → Fin n → ℕ) (A T : Finset (Fin n))
    (r : Fin n) (hr : r∉A) (hT : T⊆A) :
    cutCapacity (push c (contractMap A r)) T=cutCapacity c T := by
  rw [cut_push,lift_of_subset A T r hr hT]

lemma odd_subset_iff (U A T : Finset (Fin n)) (hT : T⊆A) :
    OddSide (A∩U) T ↔ OddSide U T := by
  have hh : T∩(A∩U)=T∩U := by rw [←inter_assoc,inter_eq_left.mpr hT]
  rw [OddSide,OddSide,hh]

end BinaryMatching.OddCutParity
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.OddCutUncross
open Finset UnitFlow CutAlgebra TerminalMincut OddCutParity
variable {n : ℕ}

lemma separates_compl (U A : Finset (Fin n)) (hA : Separates U A) : Separates U Aᶜ := by
  obtain ⟨a,ha,z,hz,haa,hza⟩ := hA
  exact ⟨z,hz,a,ha,mem_compl.mpr hza,by simpa using haa⟩

lemma uncross_on_side (c : Fin n → Fin n → ℕ) (hc : ∀ i j, c i j=c j i)
    (U A S : Finset (Fin n)) (hsep : Separates U A) (heven : Even (A∩U).card)
    (hmin : ∀ T, Separates U T → cutCapacity c A ≤ cutCapacity c T)
    (hinside : OddSide (A∩U) S) :
    ∃ T, T⊆A ∧ OddSide U T ∧ cutCapacity c T ≤ cutCapacity c S := by
  obtain ⟨a,ha,b,hb,haa,hba⟩ := hsep
  have horient : ∃ S', OddSide (A∩U) S' ∧ cutCapacity c S'=cutCapacity c S ∧
      ∃ z∈U, z∉A ∧ z∉S' := by
    by_cases hex : ∃ z∈U, z∉A ∧ z∉S
    · exact ⟨S,hinside,rfl,hex⟩
    · have hbS : b∈S := by
        by_contra hh
        exact hex ⟨b,hb,hba,hh⟩
      exact ⟨Sᶜ,odd_other (A∩U) S heven hinside,cut_compl c hc S,
        b,hb,hba,by simpa using hbS⟩
  obtain ⟨S',hodd,hcap,z,hz,hza,hzs⟩ := horient
  have hunion : Separates U (S'∪A) :=
    ⟨a,ha,z,hz,mem_union_right _ haa,by simpa only [mem_union,not_or] using And.intro hzs hza⟩
  have hlow := hmin (S'∪A) hunion
  have hsub := cut_submodular c S' A
  refine ⟨S'∩A,inter_subset_right,?_,?_⟩
  · simpa only [OddSide,inter_assoc] using hodd
  · omega

end BinaryMatching.OddCutUncross
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.OddMincut
open Finset UnitFlow UnitMincut TerminalMincut CutAlgebra OddCutParity OddCutUncross
variable {n : ℕ}

def outside (A : Finset (Fin n)) : Option (Fin n) :=
  (List.finRange n).find? (fun v => decide (v∉A))

lemma outside_some (A : Finset (Fin n)) (hA : Aᶜ.Nonempty) :
    ∃ r, outside A=some r ∧ r∉A := by
  obtain ⟨v,hv⟩ := hA
  have hv' : v∉A := mem_compl.mp hv
  cases he : outside A with
  | none =>
    have hh := List.find?_eq_none.mp he v (by simp)
    simp [hv'] at hh
  | some r =>
    have hh := List.find?_some (show (List.finRange n).find?
      (fun v => decide (v∉A))=some r from he)
    exact ⟨r,rfl,by simpa using hh⟩

def cheaper (c : Fin n → Fin n → ℕ) (S T : Finset (Fin n)) : Finset (Fin n) :=
  if cutCapacity c S ≤ cutCapacity c T then S else T

lemma cheaper_le_left (c : Fin n → Fin n → ℕ) (S T : Finset (Fin n)) :
    cutCapacity c (cheaper c S T) ≤ cutCapacity c S := by
  unfold cheaper; split_ifs <;> omega

lemma cheaper_le_right (c : Fin n → Fin n → ℕ) (S T : Finset (Fin n)) :
    cutCapacity c (cheaper c S T) ≤ cutCapacity c T := by
  unfold cheaper; split_ifs <;> omega

lemma cheaper_odd (c : Fin n → Fin n → ℕ) (U S T : Finset (Fin n))
    (hS : OddSide U S) (hT : OddSide U T) : OddSide U (cheaper c S T) := by
  unfold cheaper; split_ifs <;> assumption

def recurse : ℕ → (Fin n → Fin n → ℕ) → Finset (Fin n) → Finset (Fin n)
  | 0,_,_ => ∅
  | k+1,c,U =>
    let A := terminalCut c U
    if OddSide U A then A else
      match outside A, outside Aᶜ with
      | some r, some q =>
        cheaper c
          (lift (contractMap A r) (recurse k (push c (contractMap A r)) (A∩U)))
          (lift (contractMap Aᶜ q) (recurse k (push c (contractMap Aᶜ q)) (Aᶜ∩U)))
      | _,_ => ∅

lemma recurse_correct (fuel : ℕ) (c : Fin n → Fin n → ℕ)
    (hc : ∀ i j, c i j=c j i) (U : Finset (Fin n)) (he : Even U.card)
    (hU : 2≤U.card) (hbound : U.card≤fuel) :
    OddSide U (recurse fuel c U) ∧
      ∀ S, OddSide U S → cutCapacity c (recurse fuel c U) ≤ cutCapacity c S := by
  induction fuel generalizing c U with
  | zero => omega
  | succ k ih =>
    let A := terminalCut c U
    obtain ⟨hsep,hmin⟩ := terminalCut_correct c U hU
    change Separates U A at hsep
    change ∀ T, Separates U T → cutCapacity c A ≤ cutCapacity c T at hmin
    by_cases hodd : OddSide U A
    · have heq : recurse (k+1) c U=A := by
        rw [recurse]
        change (if OddSide U A then A else _)=A
        exact ite_eq_left hodd
      rw [heq]
      exact ⟨hodd,fun S hS => hmin S (odd_separates U S he hS)⟩
    · have heA : Even (A∩U).card := by
        simp only [OddSide,Nat.odd_iff] at hodd
        rw [Nat.even_iff]; omega
      have heB := even_other U A he heA
      obtain ⟨hposA,hposB⟩ := separate_cards U A hsep
      have hpart := terminal_partition U A
      have htwoA : 2≤(A∩U).card := by rw [Nat.even_iff] at heA; omega
      have htwoB : 2≤(Aᶜ∩U).card := by rw [Nat.even_iff] at heB; omega
      have hboundA : (A∩U).card≤k := by omega
      have hboundB : (Aᶜ∩U).card≤k := by omega
      have hnonA : A.Nonempty := by
        obtain ⟨v,hv⟩ := card_pos.mp hposA
        exact ⟨v,(mem_inter.mp hv).1⟩
      have hnonB : Aᶜ.Nonempty := by
        obtain ⟨v,hv⟩ := card_pos.mp hposB
        exact ⟨v,(mem_inter.mp hv).1⟩
      obtain ⟨r,hr,hrA⟩ := outside_some A hnonB
      obtain ⟨q,hq,hqB⟩ := outside_some Aᶜ (by simpa using hnonA)
      let f := contractMap A r
      let g := contractMap Aᶜ q
      let X := recurse k (push c f) (A∩U)
      let Y := recurse k (push c g) (Aᶜ∩U)
      obtain ⟨hX,minX⟩ := ih (push c f) (push_symm c hc f) (A∩U) heA htwoA hboundA
      obtain ⟨hY,minY⟩ := ih (push c g) (push_symm c hc g) (Aᶜ∩U) heB htwoB hboundB
      change OddSide (A∩U) X at hX
      change OddSide (Aᶜ∩U) Y at hY
      have hLX : OddSide U (lift f X) := (odd_lift_iff U A X r heB).2 hX
      have hLY : OddSide U (lift g Y) :=
        (odd_lift_iff U Aᶜ Y q (by simpa using heA)).2 hY
      have heq : recurse (k+1) c U=cheaper c (lift f X) (lift g Y) := by
        rw [recurse]
        change (if OddSide U A then A else _) = _
        rw [ite_eq_right hodd,hr,hq]
      rw [heq]
      refine ⟨cheaper_odd c U _ _ hLX hLY,?_⟩
      intro S hS
      by_cases hSA : OddSide (A∩U) S
      · obtain ⟨T,hTA,hT,hcap⟩ := uncross_on_side c hc U A S hsep heA hmin hSA
        have hchild := (odd_subset_iff U A T hTA).2 hT
        have hminT := minX T hchild
        change cutCapacity (push c f) X ≤ cutCapacity (push c f) T at hminT
        rw [cut_push] at hminT
        rw [show f=contractMap A r from rfl,cut_contract_subset c A T r hrA hTA] at hminT
        exact (cheaper_le_left c _ _).trans (hminT.trans hcap)
      · have hSB := split_odd U S A hS hSA
        have hminB : ∀ T, Separates U T → cutCapacity c Aᶜ ≤ cutCapacity c T := by
          simpa only [cut_compl c hc] using hmin
        obtain ⟨T,hTB,hT,hcap⟩ := uncross_on_side c hc U Aᶜ S
          (separates_compl U A hsep) heB hminB hSB
        have hchild := (odd_subset_iff U Aᶜ T hTB).2 hT
        have hminT := minY T hchild
        change cutCapacity (push c g) Y ≤ cutCapacity (push c g) T at hminT
        rw [cut_push] at hminT
        rw [show g=contractMap Aᶜ q from rfl,cut_contract_subset c Aᶜ T q hqB hTB] at hminT
        exact (cheaper_le_right c _ _).trans (hminT.trans hcap)

def oddCut (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) : Finset (Fin n) :=
  recurse U.card c U

 theorem oddCut_correct (c : Fin n → Fin n → ℕ) (hc : ∀ i j, c i j=c j i)
    (U : Finset (Fin n)) (he : Even U.card) (hU : 2≤U.card) :
    OddSide U (oddCut c U) ∧
      ∀ S, OddSide U S → cutCapacity c (oddCut c U) ≤ cutCapacity c S :=
  recurse_correct U.card c hc U he hU le_rfl

end BinaryMatching.OddMincut
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Algorithm
open Finset
variable {n : ℕ}

abbrev Table (n : ℕ) (α : Type) := Vector (Vector α n) n

def tabulate {α : Type} (f : Fin n → Fin n → α) : Table n α :=
  Vector.ofFn (fun i => Vector.ofFn (f i))

def entry {α : Type} (a : Table n α) (e : Pair n) : α := a[e.val.1][e.val.2]

@[simp] theorem at_tabulate {α : Type} (f : Fin n → Fin n → α) (e : Pair n) :
    entry (tabulate f) e=f e.val.1 e.val.2 := by simp [entry,tabulate]

def toTable {α : Type} [Zero α] (f : Pair n → α) : Table n α :=
  tabulate (fun i j => if h : i < j then f ⟨(i,j),h⟩ else 0)

@[simp] theorem at_toTable {α : Type} [Zero α] (f : Pair n → α) (e : Pair n) :
    entry (toTable f) e=f e := by simp [at_tabulate,toTable,e.property]

def capacities (a : Table n ℤ) (i j : Fin n) : ℕ :=
  if i < j then (a[i][j]).toNat else if j < i then (a[j][i]).toNat else 0

def q (n : ℕ) : ℕ := Fintype.card (Pair n)
def K (n : ℕ) : ℕ := Nat.clog 2 (q n)
def B (G : Input) : ℕ := (G.records.map (fun e => Nat.log2 e.multiplicity)).foldl max 0
def L (G : Input) : ℕ := 100*(G.n+B G+1)^3
def A₀ (n : ℕ) : ℕ := 10*n^2
def M₀ (G : Input) : ℕ := q G.n*(K G.n+L G)*(2+A₀ G.n)
def D₀ (G : Input) : ℕ := q G.n*(K G.n+L G+M₀ G)^2

def beta (G : Input) (e : Pair G.n) : ℤ :=
  if multiplicity G e=0 then -(L G:ℤ) else (Nat.log2 (multiplicity G e):ℤ)

structure Piece where
  slope : ℤ
  constant : ℚ
  deriving Inhabited, DecidableEq

def Piece.eval (p : Piece) (t : ℚ) : ℚ := p.slope*t+p.constant

def pieces (k : ℕ) : List Piece :=
  (List.range k).map (fun j => ⟨(j:ℤ)-1,(2:ℚ)⁻¹^j⟩) ++ [⟨k,0⟩]

def selectedPiece (k : ℕ) (t : ℚ) : Piece :=
  ((pieces k).argmin (fun p => p.eval t)).getD ⟨k,0⟩

def psi (k : ℕ) (t : ℚ) : ℚ := (selectedPiece k t).eval t

def slope (k : ℕ) (t : ℚ) : ℤ := (selectedPiece k t).slope

structure Affine (n : ℕ) where
  coeff : Pair n → ℤ
  constant : ℤ

def Affine.eval (a : Affine n) (x : Pair n → ℚ) : ℚ :=
  (∑ e, (a.coeff e:ℚ)*x e)+a.constant

def zeroRow : Affine n := ⟨fun _ => 0,0⟩
def degreeRow (v : Fin n) (positive : Bool) : Affine n :=
  ⟨fun e => if e.val.1=v ∨ e.val.2=v then (if positive then 1 else -1) else 0,
    if positive then -1 else 1⟩
def cutRow (S : Finset (Fin n)) : Affine n :=
  ⟨fun e => if (e.val.1∈S ∧ e.val.2∉S) ∨ (e.val.2∈S ∧ e.val.1∉S) then -1 else 0,1⟩

def activeRows (a : Table n ℤ) : List (Affine n) :=
  zeroRow :: ((List.finRange n).flatMap (fun v => [degreeRow v true,degreeRow v false])) ++
    [cutRow (OddMincut.oddCut (capacities a) univ)]

def coordinates (D : ℕ) (a : Table n ℤ) (e : Pair n) : ℚ := entry a e/(D:ℚ)

def activeRow (D : ℕ) (a : Table n ℤ) : Affine n :=
  ((activeRows a).argmax (fun r => r.eval (coordinates D a))).getD zeroRow

def trialValue (G : Input) (a : Table G.n ℤ) (r : Affine G.n) : ℚ :=
  (∑ e, (psi (K G.n) (coordinates (D₀ G) a e)+(beta G e:ℚ)*coordinates (D₀ G) a e)) -
    (M₀ G:ℚ)*r.eval (coordinates (D₀ G) a)

def gradient (G : Input) (a : Table G.n ℤ) (r : Affine G.n) (e : Pair G.n) : ℤ :=
  slope (K G.n) (coordinates (D₀ G) a e)+beta G e-(M₀ G:ℤ)*r.coeff e

def update (G : Input) (a : Table G.n ℤ) (r : Affine G.n) : Table G.n ℤ :=
  toTable (fun e => min (D₀ G:ℤ) (max 0 (entry a e+gradient G a r e)))

structure State (n : ℕ) where
  numerators : Table n ℤ
  best : Option ℚ

def step (G : Input) (s : State G.n) : State G.n :=
  let r := activeRow (D₀ G) s.numerators
  let value := trialValue G s.numerators r
  ⟨update G s.numerators r, some (s.best.elim value (max value))⟩

def initial (n : ℕ) : State n := ⟨tabulate (fun _ _ => 0),none⟩

def iterate (G : Input) : ℕ → State G.n
  | 0 => initial G.n
  | t+1 => step G (iterate G t)

def R (G : Input) : ℤ := ⌊((iterate G (q G.n*D₀ G)).best).getD 0⌋

def estimate (G : Input) : ℕ :=
  let r := R G
  if r < -10*(G.n:ℤ) then 0 else 2^(r-5*(G.n:ℤ)).toNat

def covered (G : Input) : Finset ℕ :=
  ((G.records.filter (fun e => 0<e.multiplicity)).flatMap (fun e => [e.left,e.right])).toFinset

def rawMultiplicity (G : Input) (i j : ℕ) : ℕ :=
  ((G.records.find? (fun r => r.left=i && r.right=j)).map Record.multiplicity).getD 0

def approximate (G : Input) : ℕ :=
  if G.n=0 then 1 else
  if Odd G.n then 0 else
  if G.n=2 then rawMultiplicity G 0 1 else
  if (covered G).card<G.n then 0 else estimate G

end BinaryMatching.Algorithm
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.DenseOracle
open Finset UnitFlow CutAlgebra OddCutParity
variable {n : ℕ}

abbrev Matrix (n : ℕ) (α : Type) := Vector (Vector α n) n

def make {α : Type} (f : Fin n → Fin n → α) : Matrix n α :=
  Vector.ofFn (fun i => Vector.ofFn (f i))

def view {α : Type} (a : Matrix n α) : Fin n → Fin n → α := fun i j => a[i][j]

@[simp] lemma view_make {α : Type} (f : Fin n → Fin n → α) : view (make f)=f := by
  funext i j; simp [view,make]

abbrev Paths (n : ℕ) := Vector (Option (List (Fin n))) n

def pathView (p : Paths n) : ResidualSearch.Table n := fun v => p[v]

def pathInitial (a : Fin n) : Paths n := Vector.ofFn (ResidualSearch.initial a)

def pathStep (c : Matrix n ℕ) (b : Matrix n ℤ) (p : Paths n) : Paths n :=
  Vector.ofFn (ResidualSearch.step (UnitMincut.residual (view c) (view b)) (pathView p))

def search (c : Matrix n ℕ) (b : Matrix n ℤ) (a : Fin n) : ℕ → Paths n
  | 0 => pathInitial a
  | k+1 => pathStep c b (search c b a k)

lemma pathView_ofFn (p : ResidualSearch.Table n) : pathView (Vector.ofFn p)=p := by
  funext v; simp [pathView]

lemma search_view (c : Matrix n ℕ) (b : Matrix n ℤ) (a : Fin n) (k : ℕ) :
    pathView (search c b a k)=ResidualSearch.search (UnitMincut.residual (view c) (view b)) a k := by
  induction k with
  | zero => exact pathView_ofFn _
  | succ k ih => simp only [search,pathStep,pathView_ofFn,ih,ResidualSearch.search]

def augment (c : Matrix n ℕ) (a z : Fin n) (b : Matrix n ℤ) : Matrix n ℤ :=
  match (search c b a n)[z] with
  | none => b
  | some p => make (fun i j => view b i j+pathFlow p i j)

def iterate (c : Matrix n ℕ) (a z : Fin n) : ℕ → Matrix n ℤ
  | 0 => make (fun _ _ => 0)
  | k+1 => augment c a z (iterate c a z k)

lemma augment_view (c : Matrix n ℕ) (a z : Fin n) (b : Matrix n ℤ) :
    view (augment c a z b)=UnitMincut.augment (view c) a z (view b) := by
  have hs := congrFun (search_view c b a n) z
  change (search c b a n)[z]=_ at hs
  simp only [augment,hs,UnitMincut.augment]
  cases h : ResidualSearch.search (UnitMincut.residual (view c) (view b)) a n z <;>
    simp only [view_make]

lemma iterate_view (c : Matrix n ℕ) (a z : Fin n) (k : ℕ) :
    view (iterate c a z k)=UnitMincut.iterate (view c) a z k := by
  induction k with
  | zero => exact view_make _
  | succ k ih => simp only [iterate,augment_view,ih,UnitMincut.iterate]

def mincut (c : Matrix n ℕ) (a z : Fin n) : Finset (Fin n) :=
  let b := iterate c a z (UnitMincut.sourceCapacity (view c) a)
  ResidualSearch.reached (pathView (search c b a n))

lemma mincut_eq (c : Matrix n ℕ) (a z : Fin n) : mincut c a z=UnitMincut.mincut (view c) a z := by
  unfold mincut UnitMincut.mincut
  dsimp only
  rw [search_view]
  have h := iterate_view c a z (UnitMincut.sourceCapacity (view c) a)
  rw [h]

def terminalCut (c : Matrix n ℕ) (U : Finset (Fin n)) : Finset (Fin n) :=
  let cuts := (((List.finRange n).product (List.finRange n)).filter
    (fun az => decide (az.1∈U ∧ az.2∈U ∧ az.1≠az.2))).map
    (fun az => mincut c az.1 az.2)
  ((cuts.argmin (cutCapacity (view c))).getD ∅)

lemma terminalCut_eq (c : Matrix n ℕ) (U : Finset (Fin n)) :
    terminalCut c U=TerminalMincut.terminalCut (view c) U := by
  simp only [terminalCut,mincut_eq,TerminalMincut.terminalCut,TerminalMincut.pairCuts]

def contract (c : Matrix n ℕ) (f : Fin n → Fin n) : Matrix n ℕ := make (push (view c) f)

@[simp] lemma contract_view (c : Matrix n ℕ) (f : Fin n → Fin n) :
    view (contract c f)=push (view c) f := view_make _

def recurse : ℕ → Matrix n ℕ → Finset (Fin n) → Finset (Fin n)
  | 0,_,_ => ∅
  | k+1,c,U =>
    let A := terminalCut c U
    if OddSide U A then A else
      match OddMincut.outside A, OddMincut.outside Aᶜ with
      | some r,some q =>
        let f := contractMap A r
        let g := contractMap Aᶜ q
        let X := recurse k (contract c f) (A∩U)
        let Y := recurse k (contract c g) (Aᶜ∩U)
        OddMincut.cheaper (view c) (lift f X) (lift g Y)
      | _,_ => ∅

lemma recurse_eq (k : ℕ) (c : Matrix n ℕ) (U : Finset (Fin n)) :
    recurse k c U=OddMincut.recurse k (view c) U := by
  induction k generalizing c U with
  | zero => rfl
  | succ k ih =>
    simp only [recurse,terminalCut_eq,OddMincut.recurse]
    split
    · rfl
    · cases h₁ : OddMincut.outside (TerminalMincut.terminalCut (view c) U) <;>
        cases h₂ : OddMincut.outside (TerminalMincut.terminalCut (view c) U)ᶜ <;>
        simp only [ih,contract_view]

def oddCut (c : Matrix n ℕ) (U : Finset (Fin n)) : Finset (Fin n) := recurse U.card c U

lemma oddCut_eq (c : Matrix n ℕ) (U : Finset (Fin n)) :
    oddCut c U=OddMincut.oddCut (view c) U := recurse_eq _ _ _

 theorem oddCut_correct (c : Matrix n ℕ) (hc : ∀ i j, view c i j=view c j i)
    (U : Finset (Fin n)) (he : Even U.card) (hU : 2≤U.card) :
    OddSide U (oddCut c U) ∧
      ∀ S, OddSide U S → cutCapacity (view c) (oddCut c U) ≤ cutCapacity (view c) S := by
  rw [oddCut_eq]
  exact OddMincut.oddCut_correct _ hc _ he hU

end BinaryMatching.DenseOracle
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

@[fun_prop] theorem mapWith [Inhabited α] [Inhabited β]
    (l : α → List β) (f : α×β → γ) (hl : Poly l) (hf : Poly f) :
    Poly (fun a => (l a).map (fun b => f (a,b))) :=
  comp _ (fun a => (a,l a)) (listMapParam f hf) (by fun_prop)

@[fun_prop] theorem flatMapWith [Inhabited α] [Inhabited β]
    (l : α → List β) (f : α×β → List γ) (hl : Poly l) (hf : Poly f) :
    Poly (fun a => (l a).flatMap (fun b => f (a,b))) := by
  have h : Poly (fun a => ((l a).map (fun b => f (a,b))).flatten) :=
    comp _ _ (listFlatten (α := γ)) (mapWith l f hl hf)
  exact h.congr (fun a => rfl)

@[fun_prop] theorem listHeadOption : Poly (List.head? : List α → Option α) := by
  exact (listCases none (fun z : α×List α => Option.some z.1) (by fun_prop)).congr
    (fun l => by cases l <;> rfl)

@[fun_prop] theorem listFilterParam [Inhabited α] [Inhabited β]
    (f : α×β → Bool) (hf : Poly f) :
    Poly (fun z : α×List β => z.2.filter (fun b => f (z.1,b))) := by
  have h : Poly (fun z : α×List β => ((z.2.map fun b => (z.1,b)).filter f).map Prod.snd) := by
    exact comp _ _ (listMap Prod.snd (by fun_prop))
      (comp _ _ (listFilter f hf) (listMapParam (fun z : α×β => z) identity))
  exact h.congr (fun z => by simp [List.filter_map,Function.comp_def])

@[fun_prop] theorem filterWith [Inhabited α] [Inhabited β]
    (l : α → List β) (f : α×β → Bool) (hl : Poly l) (hf : Poly f) :
    Poly (fun a => (l a).filter (fun b => f (a,b))) :=
  comp _ (fun a => (a,l a)) (listFilterParam f hf) (by fun_prop)

@[fun_prop] theorem listFind [Inhabited α] (p : α → Bool) (hp : Poly p) :
    Poly (List.find? p) := by
  have h : Poly (fun l : List α => (l.filter p).head?) := by fun_prop
  exact h.congr (fun l => by
    induction l with
    | nil => rfl
    | cons a l ih => cases h : p a <;> simp [h,ih])

@[fun_prop] theorem listFindParam [Inhabited α] [Inhabited β]
    (p : α×β → Bool) (hp : Poly p) :
    Poly (fun z : α×List β => z.2.find? (fun b => p (z.1,b))) := by
  have h : Poly (fun z : α×List β => (z.2.filter (fun b => p (z.1,b))).head?) :=
    comp _ _ listHeadOption (listFilterParam p hp)
  exact h.congr (fun z => by
    have hh : ∀ l : List β,(l.filter (fun b => p (z.1,b))).head?=l.find? (fun b => p (z.1,b)) := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih => cases h : p (z.1,a) <;> simp [h,ih]
    exact hh _)

@[fun_prop] theorem findWith [Inhabited α] [Inhabited β]
    (l : α → List β) (p : α×β → Bool) (hl : Poly l) (hp : Poly p) :
    Poly (fun a => (l a).find? (fun b => p (a,b))) :=
  comp _ (fun a => (a,l a)) (listFindParam p hp) (by fun_prop)

end Poly
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw
open Finset
abbrev Matrix (α : Type) := List (List α)
abbrev Cut := List Bool
abbrev Paths := List (Option (List ℕ))

def nth {α : Type} [Inhabited α] (l : List α) (i : ℕ) : α := l[i]?.getD default
def get {α : Type} [Inhabited α] (a : Matrix α) (i j : ℕ) : α := nth (nth a i) j
def tab {α : Type} (n : ℕ) (f : ℕ → α) : List α := (List.range n).map f
def matrix {α : Type} (n : ℕ) (f : ℕ → ℕ → α) : Matrix α := tab n (fun i => tab n (f i))
def view {α : Type} [Inhabited α] (n : ℕ) (a : Matrix α) : Fin n → Fin n → α :=
  fun i j => get a i.val j.val
def mem (S : Cut) (i : ℕ) : Bool := nth S i
def empty (n : ℕ) : Cut := List.replicate n false
def full (n : ℕ) : Cut := List.replicate n true
def inter (n : ℕ) (S T : Cut) : Cut := tab n (fun i => mem S i && mem T i)
def compl (n : ℕ) (S : Cut) : Cut := tab n (fun i => !mem S i)
def cardinal (S : Cut) : ℕ := (S.filter id).length

def vectorRep {n : ℕ} {α : Type} (f : Fin n → α) : List α := List.ofFn f
def matrixRep {n : ℕ} {α : Type} (f : Fin n → Fin n → α) : Matrix α :=
  vectorRep (fun i => vectorRep (f i))
def cutRep {n : ℕ} (S : Finset (Fin n)) : Cut := vectorRep (fun i => decide (i∈S))
def pathRep {n : ℕ} (p : ResidualSearch.Table n) : Paths :=
  vectorRep (fun i => (p i).map (List.map Fin.val))

lemma tab_eq_ofFn {α : Type} (n : ℕ) (f : ℕ → α) :
    tab n f=List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp [tab]
  · intro i hi hi'
    simp [tab]

lemma range_eq_fin (n : ℕ) : List.range n=(List.finRange n).map Fin.val := by
  have h := tab_eq_ofFn n id
  simpa [tab,List.finRange,List.map_ofFn,Function.comp_def] using h

@[simp] lemma at_rep {n : ℕ} {α : Type} [Inhabited α] (f : Fin n → α) (i : Fin n) :
    nth (vectorRep f) i.val=f i := by simp [nth,vectorRep,i.isLt]

@[simp] lemma get_rep {n : ℕ} {α : Type} [Inhabited α] (f : Fin n → Fin n → α) (i j : Fin n) :
    get (matrixRep f) i.val j.val=f i j := by simp [get,matrixRep]

@[simp] lemma mem_rep {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    mem (cutRep S) i.val=decide (i∈S) := by simp [mem,cutRep]

lemma tab_eq_rep {n : ℕ} {α : Type} (g : ℕ → α) (f : Fin n → α)
    (h : ∀ i,g i.val=f i) : tab n g=vectorRep f := by
  rw [tab_eq_ofFn]; congr 1; funext i; exact h i
lemma matrix_eq_rep {n : ℕ} {α : Type} (g : ℕ → ℕ → α) (f : Fin n → Fin n → α)
    (h : ∀ i j,g i.val j.val=f i j) : matrix n g=matrixRep f := by
  apply tab_eq_rep
  intro i
  exact tab_eq_rep _ _ (h i)

lemma empty_rep (n : ℕ) : empty n=cutRep (∅:Finset (Fin n)) := by
  simp [empty,cutRep,vectorRep]
lemma full_rep (n : ℕ) : full n=cutRep (univ:Finset (Fin n)) := by
  simp [full,cutRep,vectorRep]
lemma inter_rep {n : ℕ} (S T : Finset (Fin n)) :
    inter n (cutRep S) (cutRep T)=cutRep (S∩T) := by
  apply tab_eq_rep
  intro i
  simp
lemma compl_rep {n : ℕ} (S : Finset (Fin n)) : compl n (cutRep S)=cutRep Sᶜ := by
  apply tab_eq_rep
  intro i
  simp only [mem_rep,Finset.mem_compl,decide_not]
lemma cardinal_rep {n : ℕ} (S : Finset (Fin n)) : cardinal (cutRep S)=S.card := by
  unfold cardinal cutRep vectorRep
  have hh : List.ofFn (fun i : Fin n => decide (i∈S))=
    (List.finRange n).map (fun i => decide (i∈S)) := by
      simp [List.finRange,List.map_ofFn,Function.comp_def]
  rw [hh]
  rw [List.filter_map]
  simp only [List.length_map]
  rw [←List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  simp

lemma sum_tab {α : Type} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    (tab n f).sum=∑ i : Fin n,f i.val := by rw [tab_eq_ofFn,List.sum_ofFn]

end BinaryMatching.Raw
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma argAux_code {α : Type} [Coding α] (r : α → α → Prop) [DecidableRel r]
    (z : Option α×α) :
    (encode (List.argAux r z.1 z.2)).length≤(encode z.1).length+2*(encode z.2).length+1 := by
  rcases z with ⟨o,a⟩
  cases o with
  | none => simp [List.argAux,code_option_none,code_option_some]
  | some b =>
    simp only [List.argAux]
    split_ifs <;> simp only [code_option_some] <;> omega

namespace Poly
variable {α β : Type} [Coding α] [Coding β]

@[fun_prop] theorem argAux [Inhabited α] (r : α → α → Prop) [DecidableRel r]
    (hr : Poly (fun z : α×α => decide (r z.1 z.2))) :
    Poly (fun z : Option α×α => List.argAux r z.1 z.2) := by
  have h : Poly (fun z : Option α×α => if z.1.isSome then
      if decide (r z.2 (z.1.getD default)) then Option.some z.2 else z.1 else Option.some z.2) := by
    apply cond
    · fun_prop
    · fun_prop
    · apply cond
      · exact comp _ (fun z : Option α×α => (z.2,z.1.getD default)) hr (by fun_prop)
      · fun_prop
      · fun_prop
  exact h.congr (fun z => by cases z.1 <;> simp [List.argAux])

theorem listArgAux [Inhabited α] (r : α → α → Prop) [DecidableRel r]
    (hr : Poly (fun z : α×α => decide (r z.1 z.2))) :
    Poly (fun l : List α => l.foldl (List.argAux r) none) := by
  have hf := listFoldAdd (fun z : Option α×α => List.argAux r z.1 z.2)
    (argAux r hr) 1 (by intro z; simpa only [one_mul,Nat.add_assoc] using argAux_code r z)
  exact comp _ (fun l : List α => (l,(none:Option α))) hf (by fun_prop)

@[fun_prop] theorem listArgmin [Inhabited α] [Preorder β] [DecidableLT β]
    (hb : Poly (fun z : β×β => decide (z.1<z.2))) (f : α → β) (hf : Poly f) :
    Poly (List.argmin f) := by
  apply listArgAux (fun a b => f a<f b)
  exact comp _ (fun z : α×α => (f z.1,f z.2)) hb (by fun_prop)

@[fun_prop] theorem listArgmax [Inhabited α] [Preorder β] [DecidableLT β]
    (hb : Poly (fun z : β×β => decide (z.1<z.2))) (f : α → β) (hf : Poly f) :
    Poly (List.argmax f) := by
  apply listArgAux (fun a b => f b<f a)
  exact comp _ (fun z : α×α => (f z.2,f z.1)) hb (by fun_prop)

end Poly

lemma argmin_map_exact {α β γ : Type} [Preorder γ] [DecidableLT γ]
    (l : List α) (f : α → β) (g : β → γ) :
    (l.map f).argmin g=(l.argmin (g ∘ f)).map f := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    simp only [List.map_append,List.map_singleton,List.argmin_concat,ih]
    cases h : l.argmin (g ∘ f) with
    | none => rfl
    | some b => simp only [Option.map_some,Function.comp_apply]; split_ifs <;> rfl

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

@[fun_prop] theorem listArgminParam [Inhabited α] [Inhabited γ]
    [Preorder β] [DecidableLT β]
    (hb : Poly (fun z : β×β => decide (z.1<z.2))) (f : γ×α → β) (hf : Poly f) :
    Poly (fun z : γ×List α => z.2.argmin (fun a => f (z.1,a))) := by
  have hm : Poly (fun z : γ×List α => z.2.map (fun a => (z.1,a))) :=
    listMapParam (fun z : γ×α => z) identity
  have h : Poly (fun z : γ×List α => ((z.2.map fun a => (z.1,a)).argmin f).map Prod.snd) := by
    apply comp _ _ (optionMap Prod.snd (by fun_prop))
    exact comp _ _ (listArgmin hb f hf) hm
  exact h.congr (fun z => by
    rw [argmin_map_exact]
    simp [Option.map_map,Function.comp_def])

@[fun_prop] theorem listArgmaxParam [Inhabited α] [Inhabited γ]
    [Preorder β] [DecidableLT β]
    (hb : Poly (fun z : β×β => decide (z.1<z.2))) (f : γ×α → β) (hf : Poly f) :
    Poly (fun z : γ×List α => z.2.argmax (fun a => f (z.1,a))) := by
  let : Coding βᵒᵈ := inferInstanceAs (Coding β)
  apply @listArgminParam α βᵒᵈ γ _ _ _ _ _ _ _ _ f hf
  exact comp (fun z : β×β => decide (z.1<z.2)) (fun z : β×β => (z.2,z.1)) hb (by fun_prop)

end Poly
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Poly

@[fun_prop] theorem intDivNat : Poly (fun z : ℤ×ℕ => z.1/(z.2:ℤ)) := by
  have h : Poly (fun z : ℤ×ℕ => if decide (z.2=0) then (0:ℤ) else
      if decide (z.1<0) then -(((z.1.natAbs-1)/z.2+1:ℕ):ℤ)
      else ((z.1.natAbs/z.2:ℕ):ℤ)) := by fun_prop
  exact h.congr (fun z => by
    by_cases hd : z.2=0
    · simp [hd]
    · have hp : (0:ℤ)<z.2 := by exact_mod_cast (Nat.pos_of_ne_zero hd)
      simp only [hd,decide_false,Bool.false_eq_true,ite_false,decide_eq_true_eq]
      by_cases ha : z.1<0
      · rw [ite_eq_left ha]
        change -(((z.1.natAbs-1)/z.2+1:ℕ):ℤ)=Int.ediv z.1 (z.2:ℤ)
        rw [Int.ediv_of_neg_of_pos ha hp]
        have ha' : 0<z.1.natAbs := Int.natAbs_pos.mpr (ne_of_lt ha)
        have habs : (z.1.natAbs:ℤ) = -z.1 := by omega
        rw [Nat.cast_add,Nat.cast_one,Int.natCast_ediv,Nat.cast_sub (by omega : 1≤z.1.natAbs),Nat.cast_one,habs]
      · rw [ite_eq_right ha,Int.natCast_ediv,Int.natAbs_of_nonneg (le_of_not_gt ha)])

end Poly

def cappedDouble (z : ℕ×ℕ) : ℕ×ℕ := (z.1,min z.1 (2*z.2))
lemma cappedDouble_bound (z : ℕ×ℕ) (k : ℕ) :
    (cappedDouble^[k] z).1=z.1 ∧ (cappedDouble^[k] z).2≤z.1+z.2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    constructor
    · exact ih.1
    · dsimp only [cappedDouble]
      rw [ih.1]
      exact (Nat.min_le_left _ _).trans (Nat.le_add_right _ _)

lemma cappedDouble_iterate (cap k : ℕ) :
    cappedDouble^[k] (cap,min cap 1)=(cap,min cap (2^k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih]
    simp only [cappedDouble,pow_succ]
    congr 1
    omega

namespace Poly

@[fun_prop] theorem pow2Capped : Poly (fun z : ℕ×ℕ => min z.1 (2^z.2)) := by
  have hs : Poly cappedDouble := by unfold cappedDouble; fun_prop
  have hi := boundedIterate cappedDouble hs (2*X) (by
    intro z j hj
    have hb := cappedDouble_bound z.2 j
    simp only [encode_prod,pairBits_length,encode_nat,unary_length,eval_mul,eval_ofNat,eval_X]
    omega)
  have h : Poly (fun z : ℕ×ℕ => (cappedDouble^[z.2] (z.1,min z.1 1)).2) := by fun_prop
  exact h.congr (fun z => by rw [cappedDouble_iterate])

end Poly
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode.Poly
open BinaryMatching.Raw
variable {α β : Type} [Coding α] [Coding β]

@[fun_prop] theorem rawNth [Inhabited β] (l : α → List β) (i : α → ℕ)
    (hl : Poly l) (hi : Poly i) : Poly (fun a => nth (l a) (i a)) :=
  comp _ _ (listGetD default) (pair l i hl hi)
@[fun_prop] theorem rawGet [Inhabited β] (m : α → Matrix β) (i j : α → ℕ)
    (hm : Poly m) (hi : Poly i) (hj : Poly j) : Poly (fun a => get (m a) (i a) (j a)) := by
  unfold Raw.get
  fun_prop
@[fun_prop] theorem rawMem (S : α → Cut) (i : α → ℕ) (hS : Poly S) (hi : Poly i) :
    Poly (fun a => mem (S a) (i a)) := by unfold mem; fun_prop
@[fun_prop] theorem rawTab [Inhabited α] (n : α → ℕ) (f : α×ℕ → β)
    (hn : Poly n) (hf : Poly f) : Poly (fun a => tab (n a) (fun i => f (a,i))) := by
  unfold tab
  apply mapWith _ _ (by fun_prop) hf
@[fun_prop] theorem rawMatrix [Inhabited α] (n : α → ℕ) (f : (α×ℕ)×ℕ → β)
    (hn : Poly n) (hf : Poly f) : Poly (fun a => matrix (n a) (fun i j => f ((a,i),j))) := by
  unfold matrix
  exact rawTab n (fun z => tab (n z.1) (fun j => f (z,j))) hn
    (rawTab (fun z : α×ℕ => n z.1) f (by fun_prop) hf)

@[fun_prop] theorem rawEmpty : Poly empty := by unfold empty; fun_prop
@[fun_prop] theorem rawFull : Poly full := by unfold full; fun_prop
@[fun_prop] theorem rawInter : Poly (fun z : ℕ×(Cut×Cut) => inter z.1 z.2.1 z.2.2) := by
  unfold inter
  exact rawTab Prod.fst (fun z : (ℕ×(Cut×Cut))×ℕ => mem z.1.2.1 z.2 && mem z.1.2.2 z.2)
    (by fun_prop) (by fun_prop)
@[fun_prop] theorem rawCompl : Poly (fun z : ℕ×Cut => compl z.1 z.2) := by
  unfold Raw.compl
  exact rawTab Prod.fst (fun z : (ℕ×Cut)×ℕ => !mem z.1.2 z.2) (by fun_prop) (by fun_prop)
@[fun_prop] theorem rawCardinal : Poly cardinal := by
  unfold cardinal
  fun_prop

@[fun_prop] theorem uncurriedOptionMap [Inhabited α] [Inhabited β]
    (f : α×β → β) (hf : Poly f) :
    Poly (fun z : α×Option β => z.2.map (fun b => f (z.1,b))) := by
  have h : Poly (fun z : α×Option β => if z.2.isSome then
      Option.some (f (z.1,z.2.getD default)) else none) := by fun_prop
  exact h.congr (fun z => by cases z.2 <;> rfl)

end BinaryMatching.StackCode.Poly
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open BinaryMatching.Raw

@[simp] lemma code_bool_length (b : Bool) : (encode b).length=1 := rfl
@[simp] lemma code_nat_length (n : ℕ) : (encode n).length=n := unary_length n
@[simp] lemma code_int_length (z : ℤ) : (encode z).length=z.natAbs+3 := by
  simp only [encode_int,encode_prod,pairBits_length,intParts,code_bool_length,code_nat_length]
  omega
@[simp] lemma code_pair_length {α β : Type} [Coding α] [Coding β] (z : α×β) :
    (encode z).length=2*(encode z.1).length+(encode z.2).length+1 := pairBits_length _ _

lemma pair_left_le {α β : Type} [Coding α] [Coding β] (z : α×β) :
    (encode z.1).length≤(encode z).length := by simp only [code_pair_length]; omega
lemma pair_right_le {α β : Type} [Coding α] [Coding β] (z : α×β) :
    (encode z.2).length≤(encode z).length := by simp only [code_pair_length]; omega

lemma nth_code_bound {α : Type} [Coding α] [Inhabited α] (l : List α) (i M : ℕ)
    (hd : (encode (default:α)).length≤M) (h : ∀ a∈l,(encode a).length≤M) :
    (encode (nth l i)).length≤M := by
  unfold nth
  cases hi : l[i]? with
  | none => exact hd
  | some a =>
    exact h a (List.mem_of_getElem? hi)

lemma nth_code_le {α : Type} [Coding α] [Inhabited α] (l : List α) (i : ℕ) :
    (encode (nth l i)).length≤(encode l).length+(encode (default:α)).length := by
  apply nth_code_bound
  · omega
  · intro a ha
    have hh := element_code_le l a ha
    omega

lemma tab_code_bound {α : Type} [Coding α] (n M : ℕ) (f : ℕ → α)
    (h : ∀ i,i<n → (encode (f i)).length≤M) :
    (encode (tab n f)).length≤n*(2*M+1) := by
  have hh := list_code_bound (tab n f) M (by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    exact h _ (List.mem_range.mp hi))
  simpa only [tab,List.length_map,List.length_range] using hh

lemma matrix_code_bound {α : Type} [Coding α] (n M : ℕ) (f : ℕ → ℕ → α)
    (h : ∀ i,i<n → ∀ j,j<n → (encode (f i j)).length≤M) :
    (encode (matrix n f)).length≤n*(2*(n*(2*M+1))+1) := by
  apply tab_code_bound
  intro i hi
  exact tab_code_bound _ _ _ (h i hi)

lemma cut_code_length (S : Cut) : (encode S).length=3*S.length := by
  induction S with
  | nil => rfl
  | cons b S ih => simp only [code_cons,pairBits_length,code_bool_length,ih,List.length_cons]; omega

lemma option_prepend_bound (v : ℕ) (p : Option (List ℕ)) :
    (encode (p.map (v::·))).length≤(encode p).length+4*v+2 := by
  cases p with
  | none => simp only [Option.map_none,code_option_none,List.length_nil]; omega
  | some l => simp only [Option.map_some,code_option_some,code_cons,pairBits_length,code_nat_length]; omega

end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

structure Bits where
  data : List Bool
  deriving Inhabited
instance : Coding Bits := ⟨Bits.data⟩
@[simp] lemma encode_Bits (b : Bits) : encode b=b.data := rfl

namespace Routine
noncomputable def headBool : Routine (id : List Bool → List Bool) (fun b : Bool => [b])
    (fun l => l.headD false) where
  scratch := 0
  block := Block.cases 0 (Block.push 0 false)
    ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 true))
  time := 2*X+3
  correct l := by
    let s : Store 1 := Function.update (fun _ => []) 0 l
    have hfalse := Block.seq_runs _ _ (Block.clear_runs (0:Fin 1) s)
      (Block.push_runs (0:Fin 1) false (Function.update s 0 []))
    have htrue := Block.seq_runs _ _ (Block.clear_runs (0:Fin 1) s)
      (Block.push_runs (0:Fin 1) true (Function.update s 0 []))
    cases l with
    | nil =>
      have hh := Block.cases_runs_empty (0:Fin 1) (Block.push 0 false)
        ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 true))
        (by simp [s]) (Block.push_runs (0:Fin 1) false s)
      exact ⟨2,by simp,by simpa [s,Function.update_idem] using hh⟩
    | cons b l =>
      cases b with
      | false =>
        have hh := Block.cases_runs_false (0:Fin 1) (Block.push 0 false)
          ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 true))
          (by simp [s]) hfalse
        exact ⟨2*(l.length+1)+3,by simp,by simpa [s,Function.update_idem,Nat.add_assoc] using hh⟩
      | true =>
        have hh := Block.cases_runs_true (0:Fin 1) (Block.push 0 false)
          ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 true))
          (by simp [s]) htrue
        exact ⟨2*(l.length+1)+3,by simp,by simpa [s,Function.update_idem,Nat.add_assoc] using hh⟩
end Routine

namespace Poly
@[fun_prop] theorem bitsTail : Poly (fun b : Bits => Bits.mk b.data.tail) :=
  ⟨Routine.tail.reindex encode encode _ Bits.data (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem bitsEmpty : Poly (fun b : Bits => b.data.isEmpty) :=
  ⟨Routine.isEmpty.reindex encode encode _ Bits.data (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem bitsHead : Poly (fun b : Bits => b.data.headD false) :=
  ⟨Routine.headBool.reindex encode encode _ Bits.data (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem bitsLength : Poly (fun b : Bits => b.data.length) := Poly.codeLength
@[fun_prop] theorem bitsAppend : Poly (fun z : Bits×Bits => Bits.mk (z.1.data++z.2.data)) :=
  ⟨Routine.append.reindex encode encode _ (fun z : Bits×Bits => (z.1.data,z.2.data)) (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem bitsSingleton : Poly (fun b : Bool => Bits.mk [b]) :=
  ⟨(Routine.identity (fun b : Bool => [b])).reindex encode encode _ id (fun _ => rfl) (fun _ => rfl)⟩
end Poly

def encodeBitsStep (z : Bits×List Bool) : Bits×List Bool :=
  if z.1.data.isEmpty then z else (⟨z.1.data.tail⟩,z.2++[z.1.data.headD false])
lemma encodeBitsStep_iterate (j : ℕ) (b : Bits) (acc : List Bool) :
    encodeBitsStep^[j] (b,acc)=(⟨b.data.drop j⟩,acc++b.data.take j) := by
  induction j generalizing b acc with
  | zero => simp
  | succ j ih =>
    cases b with | mk l =>
    cases l with
    | nil => simp [Function.iterate_succ_apply,encodeBitsStep,ih]
    | cons a l => simp [Function.iterate_succ_apply,encodeBitsStep,ih,List.append_assoc]

namespace Poly
@[fun_prop] theorem bitsDecode : Poly (fun b : Bits => b.data) := by
  have ht : Poly (fun z : Bits×List Bool => Bits.mk z.1.data.tail) :=
    Poly.comp _ Prod.fst bitsTail (by fun_prop)
  have hh : Poly (fun z : Bits×List Bool => z.1.data.headD false) :=
    Poly.comp _ Prod.fst bitsHead (by fun_prop)
  have hs : Poly encodeBitsStep := by
    exact Poly.cond _ _ _ (Poly.comp _ Prod.fst bitsEmpty (by fun_prop))
      (Poly.pair _ _ ht (by fun_prop)) Poly.identity
  have hi := Poly.boundedIterate encodeBitsStep hs (5*X+1) (by
    intro z j hj
    rw [show z.2=(z.2.1,z.2.2) from rfl,encodeBitsStep_iterate]
    simp only [code_pair_length,encode_Bits,code_append,List.length_append,cut_code_length,
      List.length_drop,List.length_take,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,code_nat_length]
    omega)
  have h := Poly.second _ (Poly.comp _ (fun b : Bits => (b.data.length,(b,([]:List Bool)))) hi (by fun_prop))
  exact h.congr (fun b => by rw [encodeBitsStep_iterate]; simp)

private lemma bits_fold (l acc : List Bool) :
    l.foldl (fun b a => Bits.mk (b.data++[a])) (Bits.mk acc)=Bits.mk (acc++l) := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih => simp [ih,List.append_assoc]

@[fun_prop] theorem bitsEncode : Poly (fun l : List Bool => Bits.mk l) := by
  have hf : Poly (fun z : Bits×Bool => Bits.mk (z.1.data++[z.2])) := by
    exact Poly.comp _ (fun z : Bits×Bool => (z.1,Bits.mk [z.2])) bitsAppend (Poly.pair _ _ (by fun_prop) (Poly.comp _ Prod.snd bitsSingleton (by fun_prop)))
  have hfold := Poly.listFold false _ hf X (by
    intro z k
    rw [show z.2=Bits.mk z.2.data from rfl,bits_fold]
    have hl := list_length_le_code z.1
    simp only [encode_Bits,List.length_append,List.length_take,eval_X,code_pair_length]
    omega)
  have h := Poly.comp _ (fun l : List Bool => (l,Bits.mk [])) hfold (by fun_prop)
  exact h.congr (fun l => by rw [bits_fold]; rfl)
end Poly
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Poly
variable {α : Type} [Coding α] [Inhabited α]
@[fun_prop] theorem listReverse : Poly (List.reverse : List α → List α) := by
  have hf := listFoldAdd (fun z : List α×α => z.2::z.1) (by fun_prop) 1 (by
    intro z
    simp only [code_cons,pairBits_length]
    omega)
  have hh := comp _ (fun l : List α => (l,([]:List α))) hf (by fun_prop)
  exact hh.congr (fun l => by simp)
@[fun_prop] theorem listTake : Poly (fun z : ℕ×List α => z.2.take z.1) := by
  have hh : Poly (fun z : ℕ×List α => (z.2.reverse.drop (z.2.length-z.1)).reverse) := by fun_prop
  exact hh.congr (fun z => by rw [←List.reverse_take,List.reverse_reverse])
end Poly
end BinaryMatching.StackCode

namespace BinaryMatching.Parse
open StackCode Polynomial

def zeroPrefix (l : List Bool) : ℕ := l.foldr (fun b k => if b then 0 else k+1) 0
lemma zeroPrefix_delimited (k : ℕ) (l : List Bool) : zeroPrefix (List.replicate k false++true::l)=k := by
  induction k with
  | zero => simp [zeroPrefix]
  | succ k ih =>
    change zeroPrefix (false::(List.replicate k false++true::l))=k+1
    change zeroPrefix (List.replicate k false++true::l)+1=k+1
    rw [ih]
lemma zeroPrefix_le (l : List Bool) : zeroPrefix l≤l.length := by
  induction l with
  | nil => simp [zeroPrefix]
  | cons b l ih => cases b <;> simp_all [zeroPrefix]

@[fun_prop] theorem zeroPrefix_poly : Poly zeroPrefix := by
  have hf := Poly.listFoldAdd (fun z : ℕ×Bool => if z.2 then 0 else z.1+1) (by fun_prop) 1 (by
    intro z
    cases z.2 <;> simp)
  have hh := Poly.comp _ (fun l : List Bool => (l.reverse,0)) hf (by fun_prop)
  exact hh.congr (fun _ => by simp [zeroPrefix])

def numeral (l : List Bool) : List Bool×List Bool :=
  let k := zeroPrefix l
  ((l.drop (k+1)).take k,l.drop (2*k+1))
lemma numeral_encode (n : ℕ) (l : List Bool) : numeral (encodeNat n++l)=(n.bits,l) := by
  unfold numeral encodeNat
  rw [List.append_assoc,List.cons_append,zeroPrefix_delimited]
  simp [List.drop_append,List.drop_replicate]
  rw [show n.bits.length-(2*n.bits.length+1)=0 by omega,
    show 2*n.bits.length+1-n.bits.length=n.bits.length+1 by omega]
  simp
lemma numeral_nil : numeral []=([],[]) := rfl
lemma numeral_lengths (l : List Bool) : (numeral l).1.length≤l.length ∧ (numeral l).2.length≤l.length := by
  simp only [numeral,List.length_take,List.length_drop]
  omega
@[fun_prop] theorem numeral_poly : Poly numeral := by unfold numeral; fun_prop

def value (l : List Bool) : ℕ := l.foldr Nat.bit 0
lemma value_bits (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit b n h ih => simpa only [Nat.bits_append_bit n b h,value,List.foldr_cons] using congrArg (Nat.bit b) ih

def capStep (z : (ℕ×ℕ)×Bool) : ℕ×ℕ := (z.1.1,min z.1.1 (2*z.1.2+if z.2 then 1 else 0))
lemma capStep_fold (b : ℕ) (l : List Bool) (a : ℕ) :
    l.foldr (fun c z => capStep (z,c)) (b,min b a)=(b,min b (l.foldr Nat.bit a)) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [List.foldr_cons,ih]
    apply Prod.ext
    · rfl
    · cases c <;> simp [capStep,List.foldr_cons,Nat.bit] <;> omega

def boundedValue (b : ℕ) (l : List Bool) : ℕ := (l.reverse.foldl (fun z c => capStep (z,c)) (b,0)).2
lemma boundedValue_eq (b : ℕ) (l : List Bool) : boundedValue b l=min b (value l) := by
  unfold boundedValue
  rw [List.foldl_reverse,show (b,0)=(b,min b 0) by simp,capStep_fold]
  rfl
lemma boundedValue_bits (b n : ℕ) : boundedValue b n.bits=min b n := by rw [boundedValue_eq,value_bits]
lemma capStep_fold_bound (l : List Bool) (z : ℕ×ℕ) :
    (l.foldl (fun z c => capStep (z,c)) z).1=z.1 ∧
    (l.foldl (fun z c => capStep (z,c)) z).2≤ max z.1 z.2 := by
  induction l generalizing z with
  | nil => exact ⟨rfl,Nat.le_max_right _ _⟩
  | cons c l ih =>
    obtain ⟨h₁,h₂⟩ := ih (capStep (z,c))
    refine ⟨h₁,?_⟩
    have hh : (capStep (z,c)).2≤z.1 := min_le_left _ _
    exact h₂.trans (max_le (by exact Nat.le_max_left _ _) (hh.trans (Nat.le_max_left _ _)))
@[fun_prop] theorem boundedValue_poly : Poly (fun z : ℕ×List Bool => boundedValue z.1 z.2) := by
  have hs : Poly capStep := by unfold capStep; fun_prop
  have hf := Poly.listFold false capStep hs (4*X+2) (by
    intro z k
    obtain ⟨h₁,h₂⟩ := capStep_fold_bound (z.1.take k) z.2
    simp only [code_pair_length,code_nat_length,h₁,eval_add,eval_mul,eval_ofNat,eval_X]
    omega)
  unfold boundedValue
  exact Poly.second _ (Poly.comp _ (fun z : ℕ×List Bool => (z.2.reverse,(z.1,0))) hf (by fun_prop))

lemma log2_bits_length (n : ℕ) : n.log2=n.bits.length-1 := by
  by_cases hn : n=0
  · simp [hn]
  have h₁ := (Nat.lt_size).mpr (Nat.log2_self_le hn)
  have h₂ := (Nat.size_le).mpr (Nat.lt_log2_self (n := n))
  rw [←Nat.size_eq_bits_len] at h₁ h₂
  omega
lemma bits_nil_iff (n : ℕ) : n.bits=[] ↔ n=0 := by
  rw [←List.length_eq_zero_iff,Nat.size_eq_bits_len,Nat.size_eq_zero]
end BinaryMatching.Parse
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Parse
open StackCode Polynomial
abbrev RecordBits := List Bool×(List Bool×List Bool)
def recordRepr (r : Record) : RecordBits := (r.left.bits,(r.right.bits,r.multiplicity.bits))
def record (l : List Bool) : RecordBits×List Bool :=
  let a := numeral l
  let b := numeral a.2
  let c := numeral b.2
  ((a.1,(b.1,c.1)),c.2)
lemma record_encode (r : Record) (l : List Bool) : record (encodeRecord r++l)=(recordRepr r,l) := by
  unfold record encodeRecord
  simp only [List.append_assoc,numeral_encode]
  rfl
lemma record_size (l : List Bool) : (record l).2.length≤l.length ∧
    (encode (record l).1).length≤20*l.length+10 := by
  have h₁ := numeral_lengths l
  have h₂ := numeral_lengths (numeral l).2
  have h₃ := numeral_lengths (numeral (numeral l).2).2
  simp only [record,code_pair_length,cut_code_length]
  omega
@[fun_prop] theorem record_poly : Poly record := by unfold record; fun_prop

def recordStep (z : List Bool×List RecordBits) : List Bool×List RecordBits :=
  if z.1.isEmpty then z else ((record z.1).2,z.2++[(record z.1).1])
lemma recordStep_nil (k : ℕ) (l : List RecordBits) : recordStep^[k] ([],l)=([],l) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl
lemma encodeRecord_ne_nil (r : Record) : encodeRecord r≠[] := by
  simp [encodeRecord,encodeNat]
lemma recordStep_encode (r : Record) (l : List Bool) (acc : List RecordBits) :
    recordStep (encodeRecord r++l,acc)=(l,acc++[recordRepr r]) := by
  simp [recordStep, List.isEmpty_iff, List.append_eq_nil_iff, encodeRecord_ne_nil, record_encode]
lemma recordStep_records (rs : List Record) (acc : List RecordBits) :
    recordStep^[rs.length] (rs.flatMap encodeRecord,acc)=([],acc++rs.map recordRepr) := by
  induction rs generalizing acc with
  | nil => simp
  | cons r rs ih =>
    rw [List.length_cons,Function.iterate_succ_apply,List.flatMap_cons,recordStep_encode,ih]
    simp [List.append_assoc]
lemma records_length_le_bits (rs : List Record) : rs.length≤(rs.flatMap encodeRecord).length := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hr := List.length_pos_iff.mpr (encodeRecord_ne_nil r)
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega

def records (l : List Bool) : List RecordBits := (recordStep^[l.length] (l,[])).2
lemma records_encoded (rs : List Record) : records (rs.flatMap encodeRecord)=rs.map recordRepr := by
  unfold records
  have h := records_length_le_bits rs
  rw [show (rs.flatMap encodeRecord).length=((rs.flatMap encodeRecord).length-rs.length)+rs.length by omega,
    Function.iterate_add_apply,recordStep_records]
  simp only [List.nil_append,recordStep_nil]

lemma recordStep_size (z : List Bool×List RecordBits) : (recordStep z).1.length≤z.1.length ∧
    (encode (recordStep z).2).length≤(encode z.2).length+40*z.1.length+21 := by
  have hr := record_size z.1
  unfold recordStep
  split_ifs
  · simp; omega
  · simp only [code_append,List.length_append,code_cons,pairBits_length,List.length_nil,code_nil]
    omega
lemma recordStep_iterate_size (k : ℕ) (z : List Bool×List RecordBits) :
    (recordStep^[k] z).1.length≤z.1.length ∧
    (encode (recordStep^[k] z).2).length≤(encode z.2).length+k*(40*z.1.length+21) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := recordStep_size (recordStep^[k] z)
    constructor
    · exact h.1.trans ih.1
    · nlinarith
@[fun_prop] theorem records_poly : Poly records := by
  have hs : Poly recordStep := by unfold recordStep; fun_prop
  have hi := Poly.boundedIterate recordStep hs (100*(X+1)^2) (by
    intro z j hj
    obtain ⟨h₁,h₂⟩ := recordStep_iterate_size j z.2
    have he : (encode (recordStep^[j] z.2)).length ≤
        6*z.2.1.length+(encode z.2.2).length+j*(40*z.2.1.length+21)+1 := by
      simp only [code_pair_length,cut_code_length]
      omega
    have hl : z.2.1.length≤(encode z).length := by simp only [code_pair_length,code_nat_length,cut_code_length]; omega
    have hk : j≤(encode z).length := by simp only [code_pair_length,code_nat_length]; omega
    have ha : (encode z.2.2).length≤(encode z).length := by simp only [code_pair_length]; omega
    have hm := Nat.mul_le_mul hk hl
    simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
    nlinarith)
  exact Poly.second _ (Poly.comp _ (fun l : List Bool => (l.length,(l,([]:List RecordBits)))) hi (by fun_prop))

def input (l : List Bool) : List Bool×List RecordBits :=
  let a := numeral l
  (a.1,records (numeral a.2).2)
lemma input_encoded (G : Input) : input (encodeInput G)=(G.n.bits,G.records.map recordRepr) := by
  unfold input encodeInput
  simp only [List.append_assoc,numeral_encode,records_encoded]
@[fun_prop] theorem input_poly : Poly input := by unfold input; fun_prop
end BinaryMatching.Parse
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset

def Piece.evalReal (p : Piece) (t : ℝ) : ℝ := (p.slope:ℝ)*t+(p.constant:ℝ)

def selectedReal (k : ℕ) (t : ℝ) : Piece := by
  classical
  exact ((pieces k).argmin (fun p => p.evalReal t)).getD ⟨k,0⟩

def psiReal (k : ℕ) (t : ℝ) : ℝ := (selectedReal k t).evalReal t

def dyadic (j : ℕ) : ℝ := (2:ℝ)⁻¹^j

lemma pieces_nonempty (k : ℕ) : pieces k ≠ [] := by simp [pieces]

lemma selectedPiece_mem_argmin (k : ℕ) (t : ℚ) :
    selectedPiece k t ∈ (pieces k).argmin (fun p => p.eval t) := by
  unfold selectedPiece
  cases he : (pieces k).argmin (fun p => p.eval t) with
  | none => exact (pieces_nonempty k (List.argmin_eq_none.mp he)).elim
  | some p => simp

lemma selectedReal_mem_argmin (k : ℕ) (t : ℝ) :
    selectedReal k t ∈ (pieces k).argmin (fun p => p.evalReal t) := by
  classical
  unfold selectedReal
  cases he : (pieces k).argmin (fun p => p.evalReal t) with
  | none => exact (pieces_nonempty k (List.argmin_eq_none.mp he)).elim
  | some p => simp

lemma psiReal_le_piece (k : ℕ) (t : ℝ) (p : Piece) (hp : p∈pieces k) :
    psiReal k t ≤ p.evalReal t :=
  List.le_of_mem_argmin hp (selectedReal_mem_argmin k t)

lemma le_psiReal (k : ℕ) (t b : ℝ) (h : ∀ p∈pieces k,b≤p.evalReal t) :
    b ≤ psiReal k t := h _ (List.argmin_mem (selectedReal_mem_argmin k t))

lemma realPsi_cast (k : ℕ) (t : ℚ) : psiReal k (t:ℝ)=(psi k t:ℝ) := by
  have cast_eval (p : Piece) : p.evalReal (t:ℝ)=(p.eval t:ℝ) := by
    simp [Piece.eval,Piece.evalReal]
  apply le_antisymm
  · have h := psiReal_le_piece k (t:ℝ) _ (List.argmin_mem (selectedPiece_mem_argmin k t))
    simpa only [cast_eval,psi] using h
  · apply le_psiReal
    intro p hp
    rw [cast_eval]
    exact_mod_cast (List.le_of_mem_argmin hp (selectedPiece_mem_argmin k t))

lemma psiReal_concave (k : ℕ) : ConcaveOn ℝ Set.univ (psiReal k) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  apply le_psiReal
  intro p hp
  have hx := psiReal_le_piece k x p hp
  have hy := psiReal_le_piece k y p hp
  simp only [smul_eq_mul]
  calc
    a*psiReal k x+b*psiReal k y ≤ a*p.evalReal x+b*p.evalReal y := by gcongr
    _ = p.evalReal (a*x+b*y) := by
      simp only [Piece.evalReal]
      have hh := congrArg (fun t => t*(p.constant:ℝ)) hab
      nlinarith [hh]

lemma mem_pieces (k : ℕ) (p : Piece) :
    p∈pieces k ↔ p=⟨k,0⟩ ∨ ∃ j<k,p=⟨(j:ℤ)-1,(2:ℚ)⁻¹^j⟩ := by
  simp only [pieces,List.mem_append,List.mem_map,List.mem_range,List.mem_singleton]
  aesop

lemma first_mem_pieces (k : ℕ) : (⟨k,0⟩:Piece)∈pieces k := (mem_pieces k _).2 (Or.inl rfl)
lemma chord_mem_pieces (k j : ℕ) (hj : j<k) :
    (⟨(j:ℤ)-1,(2:ℚ)⁻¹^j⟩:Piece)∈pieces k := (mem_pieces k _).2 (Or.inr ⟨j,hj,rfl⟩)

lemma chord_eval (j : ℕ) (t : ℝ) :
    (⟨(j:ℤ)-1,(2:ℚ)⁻¹^j⟩:Piece).evalReal t=((j:ℝ)-1)*t+dyadic j := by
  simp [Piece.evalReal,dyadic]

lemma first_eval (k : ℕ) (t : ℝ) : (⟨k,0⟩:Piece).evalReal t=(k:ℝ)*t := by
  simp [Piece.evalReal]

lemma dyadic_pos (j : ℕ) : 0<dyadic j := by unfold dyadic; positivity
lemma dyadic_nonneg (j : ℕ) : 0≤dyadic j := (dyadic_pos j).le
lemma dyadic_succ (j : ℕ) : dyadic (j+1)=dyadic j/2 := by simp [dyadic,pow_succ,div_eq_mul_inv]
lemma dyadic_zero : dyadic 0=1 := by simp [dyadic]
lemma dyadic_mul_pow (j : ℕ) : dyadic j*(2:ℝ)^j=1 := by
  rw [dyadic,←mul_pow]; norm_num

lemma dyadic_scale (j l : ℕ) (h : l≤j) : dyadic l=(2:ℝ)^(j-l)*dyadic j := by
  have hj : j=l+(j-l) := by omega
  conv_rhs => rw [hj,dyadic,pow_add]
  rw [Nat.add_sub_cancel_left]
  change (2:ℝ)⁻¹^l=(2:ℝ)^(j-l)*((2:ℝ)⁻¹^l*(2:ℝ)⁻¹^(j-l))
  calc
    _ = (2:ℝ)⁻¹^l*1 := (mul_one _).symm
    _ = _ := by rw [←dyadic_mul_pow (j-l)]; unfold dyadic; ring

lemma chord_above_knot (l j : ℕ) :
    (j:ℝ)*dyadic j ≤ ((l:ℝ)-1)*dyadic j+dyadic l := by
  rcases lt_trichotomy l j with h|h|h
  · have hp : 1+(j-l:ℕ) ≤ (2:ℕ)^(j-l) := by
      have hh := one_add_mul_le_pow (show (-2:ℝ)≤1 by norm_num) (j-l)
      norm_num at hh
      exact_mod_cast hh
    have hpR : (1:ℝ)+(j:ℝ)-(l:ℝ) ≤ (2:ℝ)^(j-l) := by
      have := Nat.cast_le (α:=ℝ).mpr hp
      push_cast [Nat.cast_sub h.le] at this
      linarith
    rw [dyadic_scale j l h.le]
    nlinarith [mul_le_mul_of_nonneg_right hpR (dyadic_nonneg j)]
  · subst l; ring_nf; rfl
  · have hh : (j:ℝ)+1≤l := by exact_mod_cast h
    nlinarith [dyadic_nonneg j,dyadic_nonneg l]

lemma psiReal_knot (k j : ℕ) (hj : j≤k) : psiReal k (dyadic j)=(j:ℝ)*dyadic j := by
  apply le_antisymm
  · rcases lt_or_eq_of_le hj with h|h
    · have hh := psiReal_le_piece k (dyadic j) _ (chord_mem_pieces k j h)
      rw [chord_eval] at hh
      nlinarith
    · subst j
      simpa only [first_eval] using psiReal_le_piece k (dyadic k) _ (first_mem_pieces k)
  · apply le_psiReal
    intro p hp
    rcases (mem_pieces k p).1 hp with rfl|⟨l,_,rfl⟩
    · rw [first_eval]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (dyadic_nonneg j)
    · rw [chord_eval]; exact chord_above_knot l j

lemma psiReal_zero (k : ℕ) : psiReal k 0=0 := by
  apply le_antisymm
  · simpa only [first_eval,mul_zero] using psiReal_le_piece k 0 _ (first_mem_pieces k)
  · apply le_psiReal
    intro p hp
    rcases (mem_pieces k p).1 hp with rfl|⟨j,_,rfl⟩
    · simp [first_eval]
    · simpa only [chord_eval,mul_zero,zero_add] using dyadic_nonneg j

end
end BinaryMatching.Algorithm
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset

lemma concave_affine_chord {S : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ S f)
    {l u t p c : ℝ} (hl : l∈S) (hu : u∈S) (hlu : l<u) (ht : t∈Set.Icc l u)
    (hfl : f l=p*l+c) (hfu : f u=p*u+c) : p*t+c≤f t := by
  let b := (t-l)/(u-l)
  have hd : 0<u-l := sub_pos.mpr hlu
  have hb : 0≤b := div_nonneg (sub_nonneg.mpr ht.1) hd.le
  have hb1 : b≤1 := (div_le_one hd).2 (by linarith [ht.2])
  have he : (1-b)*l+b*u=t := by dsimp [b]; field_simp; ring
  have hc := hf.2 hl hu (sub_nonneg.mpr hb1) hb (sub_add_cancel 1 b)
  simp only [smul_eq_mul] at hc
  rw [he,hfl,hfu] at hc
  calc
    p*t+c=(1-b)*(p*l+c)+b*(p*u+c) := by rw [←he]; ring
    _ ≤ f t := hc

lemma psiReal_on_first (k : ℕ) {t : ℝ} (ht : t∈Set.Icc 0 (dyadic k)) :
    psiReal k t=(k:ℝ)*t := by
  apply le_antisymm
  · simpa only [first_eval] using psiReal_le_piece k t _ (first_mem_pieces k)
  · simpa only [add_zero] using concave_affine_chord (psiReal_concave k)
      (Set.mem_univ 0) (Set.mem_univ (dyadic k)) (dyadic_pos k) ht
      (p:=(k:ℝ)) (c:=0) (by simp [psiReal_zero]) (by rw [psiReal_knot k k le_rfl]; ring)

lemma psiReal_on_chord (k j : ℕ) (hj : j<k) {t : ℝ}
    (ht : t∈Set.Icc (dyadic (j+1)) (dyadic j)) :
    psiReal k t=((j:ℝ)-1)*t+dyadic j := by
  apply le_antisymm
  · simpa only [chord_eval] using psiReal_le_piece k t _ (chord_mem_pieces k j hj)
  · apply concave_affine_chord (psiReal_concave k) (Set.mem_univ _) (Set.mem_univ _)
      (show dyadic (j+1)<dyadic j by rw [dyadic_succ]; linarith [dyadic_pos j]) ht
    · rw [psiReal_knot k (j+1) hj,dyadic_succ,Nat.cast_add,Nat.cast_one]; ring
    · rw [psiReal_knot k j hj.le]; ring

lemma dyadic_cover (k : ℕ) {t : ℝ} (ht : t∈Set.Icc 0 1) :
    t≤dyadic k ∨ ∃ j<k,t∈Set.Icc (dyadic (j+1)) (dyadic j) := by
  induction k with
  | zero => exact Or.inl (by simpa only [dyadic_zero] using ht.2)
  | succ k ih =>
    by_cases h : t≤dyadic (k+1)
    · exact Or.inl h
    · right
      rcases ih with h'|⟨j,hj,hjt⟩
      · exact ⟨k,Nat.lt_succ_self k,le_of_not_ge h,h'⟩
      · exact ⟨j,Nat.lt_succ_of_lt hj,hjt⟩

def phi (t : ℝ) : ℝ := Real.negMulLog t / Real.log 2

lemma log_two_pos : 0<Real.log 2 := Real.log_pos (by norm_num)
lemma half_le_log_two : (1/2:ℝ)≤Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ)<2⁻¹ by norm_num)
  rw [Real.log_inv] at h
  norm_num at h
  linarith

lemma log_dyadic (j : ℕ) : Real.log (dyadic j)=-(j:ℝ)*Real.log 2 := by
  simp [dyadic,Real.log_pow,Real.log_inv]

lemma phi_dyadic (j : ℕ) : phi (dyadic j)=(j:ℝ)*dyadic j := by
  simp only [phi,Real.negMulLog_def,log_dyadic]
  field_simp [log_two_pos.ne']

lemma phi_zero : phi 0=0 := by simp [phi]

lemma phi_concave : ConcaveOn ℝ (Set.Ici 0) phi := by
  refine ⟨convex_Ici 0,?_⟩
  intro x hx y hy a b ha hb hab
  have hh := Real.concaveOn_negMulLog.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hh ⊢
  have hd := div_le_div_of_nonneg_right hh log_two_pos.le
  simpa only [phi,add_div,mul_div_assoc] using hd

lemma phi_le_one {t : ℝ} (ht : t∈Set.Icc 0 1) : phi t≤1 := by
  have hp : (fun b : Bool => if b then t else 1-t) ∈ MatchingEntropy.probabilitySimplex Bool := by
    constructor
    · intro b; cases b <;> simp [ht.1,sub_nonneg.mpr ht.2]
    · simp
  have hh := MatchingEntropy.entropy_le_log_card hp
  simp only [MatchingEntropy.entropy,Fintype.sum_bool,Fintype.card_bool,Bool.false_eq_true,
    ↓reduceIte,Nat.cast_ofNat] at hh
  have hn := Real.negMulLog_nonneg (sub_nonneg.mpr ht.2) (by linarith [ht.1] : 1-t≤1)
  unfold phi
  apply (div_le_one log_two_pos).2
  linarith

lemma phi_mul (u v : ℝ) : phi (u*v)=v*phi u+u*phi v := by
  simp only [phi,Real.negMulLog_mul]; ring

lemma phi_lower_first (k : ℕ) {t : ℝ} (ht : t∈Set.Icc 0 (dyadic k)) :
    (k:ℝ)*t ≤ phi t := by
  simpa only [add_zero] using concave_affine_chord phi_concave
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (dyadic_nonneg k)) (dyadic_pos k) ht
    (p:=(k:ℝ)) (c:=0) (by simp [phi_zero]) (by rw [phi_dyadic]; ring)

lemma phi_lower_chord (j : ℕ) {t : ℝ} (ht : t∈Set.Icc (dyadic (j+1)) (dyadic j)) :
    ((j:ℝ)-1)*t+dyadic j≤phi t := by
  apply concave_affine_chord phi_concave (Set.mem_Ici.mpr (dyadic_nonneg _))
    (Set.mem_Ici.mpr (dyadic_nonneg _))
    (show dyadic (j+1)<dyadic j by rw [dyadic_succ]; linarith [dyadic_pos j]) ht
  · rw [phi_dyadic,dyadic_succ,Nat.cast_add,Nat.cast_one]; ring
  · rw [phi_dyadic]; ring

lemma phi_upper_chord (j : ℕ) {t : ℝ} (ht : t∈Set.Icc (dyadic (j+1)) (dyadic j)) :
    phi t≤((j:ℝ)+1)*t := by
  have ht0 : 0<t := (dyadic_pos _).trans_le ht.1
  have hh := Real.log_le_log (dyadic_pos (j+1)) ht.1
  rw [log_dyadic,Nat.cast_add,Nat.cast_one] at hh
  unfold phi
  apply (div_le_iff₀ log_two_pos).2
  rw [Real.negMulLog_def]
  nlinarith [mul_le_mul_of_nonneg_left hh ht0.le]

lemma phi_error_first (k : ℕ) {t : ℝ} (ht : t∈Set.Icc 0 (dyadic k)) :
    phi t-(k:ℝ)*t≤dyadic k := by
  let r := t/dyadic k
  have hr : r∈Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg ht.1 (dyadic_nonneg k),(div_le_one (dyadic_pos k)).2 ht.2⟩
  have he : dyadic k*r=t := by dsimp [r]; field_simp [ne_of_gt (dyadic_pos k)]
  have hh := phi_mul (dyadic k) r
  rw [he,phi_dyadic] at hh
  have hu := mul_le_mul_of_nonneg_left (phi_le_one hr) (dyadic_nonneg k)
  nlinarith [hh,he]

theorem dyadic_entropy_error (k : ℕ) {t : ℝ} (ht : t∈Set.Icc 0 1) :
    0≤phi t-psiReal k t ∧ phi t-psiReal k t≤t+dyadic k := by
  rcases dyadic_cover k ht with h|⟨j,hj,hjt⟩
  · rw [psiReal_on_first k ⟨ht.1,h⟩]
    exact ⟨sub_nonneg.mpr (phi_lower_first k ⟨ht.1,h⟩),
      (phi_error_first k ⟨ht.1,h⟩).trans (by linarith [ht.1])⟩
  · rw [psiReal_on_chord k j hj hjt]
    have hlo := phi_lower_chord j hjt
    have hhi := phi_upper_chord j hjt
    have hd := dyadic_nonneg k
    constructor <;> linarith [hjt.2]

end
end BinaryMatching.Algorithm
end

end OAI
end
end

section
section
namespace OAI


section

noncomputable section
open Finset
namespace MatchingEntropy

variable {I : Type*} [Fintype I]

def expSum (a : I → ℝ) : ℝ := ∑ i, Real.exp (a i)
def expLaw (a : I → ℝ) (i : I) : ℝ := Real.exp (a i)/expSum a

lemma expSum_pos [Nonempty I] (a : I → ℝ) : 0<expSum a :=
  sum_pos (fun i _ => Real.exp_pos (a i)) univ_nonempty

lemma expLaw_simplex [Nonempty I] (a : I → ℝ) : expLaw a∈probabilitySimplex I := by
  refine ⟨fun i => (div_pos (Real.exp_pos _) (expSum_pos a)).le,?_⟩
  simp only [expLaw,←sum_div]
  exact div_self (expSum_pos a).ne'

lemma log_expLaw [Nonempty I] (a : I → ℝ) (i : I) :
    Real.log (expLaw a i)=a i-Real.log (expSum a) := by
  rw [expLaw,Real.log_div (Real.exp_ne_zero _) (expSum_pos a).ne',Real.log_exp]

lemma expLaw_cross [Nonempty I] (a : I → ℝ) {p : I → ℝ}
    (hp : p∈probabilitySimplex I) :
    -(∑ i,p i*Real.log (expLaw a i))=Real.log (expSum a)-∑ i,p i*a i := by
  simp only [log_expLaw,mul_sub,sum_sub_distrib,←sum_mul,hp.2,one_mul]
  ring

lemma expSum_variational_le [Nonempty I] (a : I → ℝ) {p : I → ℝ}
    (hp : p∈probabilitySimplex I) : entropy p+∑ i,p i*a i≤Real.log (expSum a) := by
  have hh := entropy_le_crossEntropy (expLaw_simplex a) hp
    (fun i hi => False.elim ((div_pos (Real.exp_pos _) (expSum_pos a)).ne' hi))
  rw [expLaw_cross a hp] at hh
  linarith

lemma expSum_variational_eq [Nonempty I] (a : I → ℝ) :
    entropy (expLaw a)+∑ i,expLaw a i*a i=Real.log (expSum a) := by
  rw [entropy_eq,expLaw_cross a (expLaw_simplex a)]
  ring

namespace LooplessGraph
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def score (G : LooplessGraph V E) (β : E → ℝ) (M : G.Matching) : ℝ :=
  ∑ e∈M.val,β e

def weightedZ (G : LooplessGraph V E) (β : E → ℝ) : ℝ :=
  expSum (fun M => Real.log 2*G.score β M)

omit [Fintype V] [DecidableEq V] in
lemma score_indicator (G : LooplessGraph V E) (β : E → ℝ) (M : G.Matching) :
    G.score β M=∑ e, β e*G.indicator M e := by
  simp [score,indicator]

omit [Fintype V] [DecidableEq V] in
lemma mean_score (G : LooplessGraph V E) (β : E → ℝ) (p : G.Matching → ℝ) :
    (∑ M,p M*G.score β M)=∑ e,β e*G.mean p e := by
  simp only [score_indicator,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro e _
  simp only [mean,mul_sum]
  apply sum_congr rfl; intro M _; ring

omit [Fintype V] [DecidableEq V] in
lemma complement_entropy_le_mass (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x∈G.polytope) : entropy (fun e => 1-x e)≤∑ e,x e := by
  apply sum_le_sum; intro e _
  have hh := Real.negMulLog_le_one_sub_self (sub_nonneg.mpr (G.coordinate_mem_Icc hx e).2)
  simpa only [sub_sub_cancel] using hh

lemma entropy_binary_scale (G : LooplessGraph V E) (hPM : Nonempty G.Matching)
    {r : ℕ} (hV : Fintype.card V=2*r) {x : E → ℝ} (hx : x∈G.polytope) :
    entropy x/Real.log 2-4*(Fintype.card V:ℝ)≤ maxMatchingEntropy G x/Real.log 2 ∧
    maxMatchingEntropy G x/Real.log 2≤entropy x/Real.log 2+(Fintype.card V:ℝ) := by
  have hl := separable_lower G hPM x hx
  have hu := maxMatchingEntropy_le_binary G x hx
  have hc := G.complement_entropy_le_mass hx
  rw [G.marginal_sum hV hx] at hc
  have hv : (Fintype.card V:ℝ)=2*(r:ℝ) := by exact_mod_cast hV
  have hlog := BinaryMatching.Algorithm.half_le_log_two
  have hr : (0:ℝ)≤r := by positivity
  have hprod := mul_le_mul_of_nonneg_right hlog hr
  dsimp only [separableLower,binaryEntropy] at hl hu
  constructor
  · apply (le_div_iff₀ BinaryMatching.Algorithm.log_two_pos).2
    rw [sub_mul,div_mul_cancel₀ _ BinaryMatching.Algorithm.log_two_pos.ne',hv]
    nlinarith
  · apply (div_le_iff₀ BinaryMatching.Algorithm.log_two_pos).2
    rw [add_mul,div_mul_cancel₀ _ BinaryMatching.Algorithm.log_two_pos.ne',hv]
    nlinarith

omit [Fintype V] [DecidableEq V] in
lemma weighted_variational_le (G : LooplessGraph V E) [Nonempty G.Matching]
    (β : E → ℝ) {x : E → ℝ} (hx : x∈G.polytope) :
    maxMatchingEntropy G x/Real.log 2+∑ e,β e*x e≤Real.log (G.weightedZ β)/Real.log 2 := by
  obtain ⟨p,hp,hh⟩ := maxMatchingEntropy_attained G hx
  have h := expSum_variational_le (fun M => Real.log 2*G.score β M) hp.1
  have he : (∑ M,p M*(Real.log 2*G.score β M))=Real.log 2*(∑ e,β e*x e) := by
    rw [mul_sum]
    conv_lhs => arg 2; ext M; rw [mul_left_comm]
    rw [←mul_sum,G.mean_score,hp.2,mul_sum]
  rw [he,hh] at h
  apply (le_div_iff₀ BinaryMatching.Algorithm.log_two_pos).2
  calc
    _ = maxMatchingEntropy G x+Real.log 2*(∑ e,β e*x e) := by
      rw [add_mul,div_mul_cancel₀ _ BinaryMatching.Algorithm.log_two_pos.ne']; ring
    _ ≤ _ := h

omit [Fintype V] [DecidableEq V] in
lemma weighted_variational_attained (G : LooplessGraph V E) [Nonempty G.Matching]
    (β : E → ℝ) : ∃ x∈G.polytope,
      Real.log (G.weightedZ β)/Real.log 2≤ maxMatchingEntropy G x/Real.log 2+∑ e,β e*x e := by
  let p := expLaw (fun M => Real.log 2*G.score β M)
  have hp := expLaw_simplex (fun M => Real.log 2*G.score β M)
  have hpx : p∈G.feasibleLaws (G.mean p) := ⟨hp,rfl⟩
  refine ⟨G.mean p,(G.mem_polytope_iff _).mpr ⟨p,hpx⟩,?_⟩
  have he := expSum_variational_eq (fun M => Real.log 2*G.score β M)
  have he' : (∑ M,p M*(Real.log 2*G.score β M))=Real.log 2*(∑ e,β e*G.mean p e) := by
    calc
      _ = Real.log 2*(∑ M,p M*G.score β M) := by
        rw [mul_sum]; apply sum_congr rfl; intro M _; ring
      _ = _ := by rw [G.mean_score]
  change entropy p+(∑ M,p M*(Real.log 2*G.score β M))=Real.log (G.weightedZ β) at he
  rw [he'] at he
  apply (div_le_iff₀ BinaryMatching.Algorithm.log_two_pos).2
  have hH := entropy_le_maxMatchingEntropy G hpx
  calc
    _ ≤ maxMatchingEntropy G (G.mean p)+Real.log 2*(∑ e,β e*G.mean p e) := by linarith
    _ = _ := by rw [add_mul,div_mul_cancel₀ _ BinaryMatching.Algorithm.log_two_pos.ne']; ring
end LooplessGraph
end MatchingEntropy
end
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching
noncomputable section
open Finset
variable {n : ℕ}

lemma sum_pairs (f : Fin n → Fin n → ℝ) :
    (∑ e : Pair n, f e.val.1 e.val.2)=∑ i,∑ j,if i < j then f i j else 0 := by
  let s : Finset (Fin n × Fin n) := univ.filter (fun ij => ij.1 < ij.2)
  have hs : ∀ ij : Fin n × Fin n,ij∈s ↔ ij.1 < ij.2 := by simp [s]
  rw [←sum_subtype s hs (fun ij => f ij.1 ij.2)]
  rw [show s=univ.filter (fun ij => ij.1 < ij.2) from rfl,sum_filter,Fintype.sum_prod_type]

lemma sum_skip (g : Fin n → ℝ) (v : Fin n) :
    (∑ j,if j=v then 0 else g j)=(∑ j,g j)-g v := by
  have hh : (∑ j,g j)=(∑ j,if j=v then 0 else g j)+g v := by
    calc
      _ = ∑ j, ((if j=v then 0 else g j)+(if j=v then g j else 0)) := by
        apply sum_congr rfl; intro j _; split_ifs <;> simp
      _ = _ := by rw [sum_add_distrib]; simp
  linarith

lemma degree_from_symm (f : Fin n → Fin n → ℝ) (hf : ∀ i j,f i j=f j i) (v : Fin n) :
    (completeGraph n).degree (fun e => f e.val.1 e.val.2) v =
      ∑ j,if j=v then 0 else f v j := by
  change (∑ e : Pair n,if e.val.1=v ∨ e.val.2=v then f e.val.1 e.val.2 else 0)=_
  rw [sum_pairs (fun i j => if i=v ∨ j=v then f i j else 0)]
  have he (i j : Fin n) :
      (if i < j then (if i=v ∨ j=v then f i j else 0) else 0) =
      (if i=v then (if i < j then f i j else 0) else 0)+
      (if j=v then (if i < j then f i j else 0) else 0) := by
    by_cases hiv : i=v <;> by_cases hjv : j=v <;> by_cases hij : i < j <;> simp_all
  simp_rw [he,sum_add_distrib]
  have hleft : (∑ i,∑ j,if i=v then (if i < j then f i j else 0) else 0)=
      ∑ j,if v < j then f v j else 0 := by
    simp [Finset.sum_ite_irrel]
  have hright : (∑ i,∑ j,if j=v then (if i < j then f i j else 0) else 0)=
      ∑ j,if j < v then f v j else 0 := by
    simp only [sum_ite_eq',mem_univ,ite_true]
    apply sum_congr rfl; intro j _; rw [hf j v]
  rw [hleft,hright,←sum_add_distrib]
  apply sum_congr rfl; intro j _
  rcases lt_trichotomy j v with h|h|h
  · simp [h, ne_of_lt h, not_lt_of_ge h.le]
  · subst j; simp
  · simp [h, ne_of_gt h, not_lt_of_ge h.le]

lemma degree_constant (b : ℝ) (v : Fin n) :
    (completeGraph n).degree (fun _ => b) v=((n:ℝ)-1)*b := by
  rw [degree_from_symm (fun _ _ => b) (fun _ _ => rfl),sum_skip]
  simp; ring

lemma degree_vertex_add (d : Fin n → ℝ) (v : Fin n) :
    (completeGraph n).degree (fun e => d e.val.1+d e.val.2) v =
      ((n:ℝ)-2)*d v+∑ j,d j := by
  rw [degree_from_symm (fun i j => d i+d j) (fun _ _ => add_comm _ _),sum_skip]
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin]
  ring

lemma cut_from_symm (f : Fin n → Fin n → ℝ) (hf : ∀ i j,f i j=f j i)
    (S : Finset (Fin n)) :
    (completeGraph n).cutMass (fun e => f e.val.1 e.val.2) S =
      ∑ i∈S,∑ j∈Sᶜ,f i j := by
  unfold MatchingEntropy.LooplessGraph.cutMass MatchingEntropy.LooplessGraph.cut
  rw [sum_filter]
  change (∑ e : Pair n,if (e.val.1∈S ∧ e.val.2∉S) ∨ (e.val.1∉S ∧ e.val.2∈S)
    then f e.val.1 e.val.2 else 0)=_
  rw [sum_pairs (fun i j => if (i∈S ∧ j∉S) ∨ (i∉S ∧ j∈S) then f i j else 0)]
  have he (i j : Fin n) :
      (if i < j then (if (i∈S ∧ j∉S) ∨ (i∉S ∧ j∈S) then f i j else 0) else 0) =
        (if i < j ∧ i∈S ∧ j∉S then f i j else 0)+
        (if i < j ∧ i∉S ∧ j∈S then f i j else 0) := by
    by_cases hij : i < j <;> by_cases hi : i∈S <;> by_cases hj : j∈S <;> simp [hij,hi,hj]
  simp_rw [he,sum_add_distrib]
  have hswap : (∑ i,∑ j,if i < j ∧ i∉S ∧ j∈S then f i j else 0)=
      ∑ i,∑ j,if j < i ∧ i∈S ∧ j∉S then f i j else 0 := by
    rw [sum_comm]
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _
    rw [hf j i]
    by_cases hij : j < i <;> by_cases hi : i∈S <;> by_cases hj : j∈S <;> simp [hij,hi,hj]
  rw [hswap,←sum_add_distrib]
  simp_rw [←sum_add_distrib]
  have hterm (i j : Fin n) :
      (if i < j ∧ i∈S ∧ j∉S then f i j else 0)+
        (if j < i ∧ i∈S ∧ j∉S then f i j else 0)=
        if i∈S ∧ j∉S then f i j else 0 := by
    rcases lt_trichotomy i j with h|h|h
    · simp [h,not_lt_of_ge h.le]
    · subst j; simp
    · simp [h,not_lt_of_ge h.le]
  simp_rw [hterm]
  have hS : S=univ.filter (fun i => i∈S) := by ext i; simp
  have hSc : Sᶜ=univ.filter (fun j => j∉S) := by ext j; simp
  conv_rhs => rw [hS]; rw [sum_filter]
  simp only [ite_and]
  apply sum_congr rfl; intro i _
  by_cases hi : i∈S
  · simp only [hi,ite_true]
    rw [←hS,hSc,sum_filter]
  · simp only [hi,ite_false,sum_const_zero]

lemma cut_constant (b : ℝ) (S : Finset (Fin n)) :
    (completeGraph n).cutMass (fun _ => b) S=(S.card:ℝ)*(Sᶜ.card:ℝ)*b := by
  rw [cut_from_symm (fun _ _ => b) (fun _ _ => rfl)]
  simp [mul_assoc]

lemma q_le_square : Fintype.card (Pair n) ≤ n^2 := by
  calc
    _ ≤ Fintype.card (Fin n × Fin n) := Fintype.card_subtype_le _
    _ = n^2 := by simp [pow_two]

end
end BinaryMatching
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching
noncomputable section
open Finset MatchingEntropy
variable {n : ℕ}

lemma degree_add (x z : Pair n → ℝ) (v : Fin n) :
    (completeGraph n).degree (fun e => x e+z e) v=
      (completeGraph n).degree x v+(completeGraph n).degree z v := by
  simpa only [one_smul,one_mul,Pi.add_def] using (completeGraph n).degree_linear x z 1 1 v

lemma cut_add (x z : Pair n → ℝ) (S : Finset (Fin n)) :
    (completeGraph n).cutMass (fun e => x e+z e) S=
      (completeGraph n).cutMass x S+(completeGraph n).cutMass z S := by
  simpa only [one_smul,one_mul,Pi.add_def] using (completeGraph n).cutMass_linear x z 1 1 S

lemma cut_bound {z : Pair n → ℝ} {b : ℝ} (hb : 0≤b) (hz : ∀ e, |z e|≤b)
    (S : Finset (Fin n)) : |(completeGraph n).cutMass z S|≤Fintype.card (Pair n)*b := by
  calc
    _ ≤ ∑ e∈(completeGraph n).cut S, |z e| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e∈(completeGraph n).cut S, b := sum_le_sum (fun e _ => hz e)
    _ = ((completeGraph n).cut S).card*b := by simp
    _ ≤ Fintype.card (Pair n)*b := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_univ _) hb

def degreeCorrection (x : Pair n → ℝ) (e : Pair n) : ℝ :=
  let d := fun v => 1-(completeGraph n).degree x v
  (d e.val.1+d e.val.2)/((n:ℝ)-2)-(∑ v,d v)/(((n:ℝ)-2)*((n:ℝ)-1))

lemma correction_degree (hn : 4≤n) (x : Pair n → ℝ) (v : Fin n) :
    (completeGraph n).degree (fun e => x e+degreeCorrection x e) v=1 := by
  have hn' : (4:ℝ)≤n := by exact_mod_cast hn
  have h2 : (n:ℝ)-2≠0 := by linarith
  have h1 : (n:ℝ)-1≠0 := by linarith
  let d := fun v => 1-(completeGraph n).degree x v
  rw [degree_add]
  have hc : degreeCorrection x = ((n:ℝ)-2)⁻¹ • (fun e : Pair n => d e.val.1+d e.val.2) +
      (-1:ℝ) • (fun _ => (∑ v,d v)/(((n:ℝ)-2)*((n:ℝ)-1))) := by
    funext e; simp only [degreeCorrection,d,Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring
  rw [hc,(completeGraph n).degree_linear,degree_vertex_add,degree_constant]
  dsimp [d]
  field_simp
  ring

lemma correction_bound (hn : 4≤n) {x : Pair n → ℝ} {w : ℝ} (hw : 0≤w)
    (hdeg : ∀ v, |(completeGraph n).degree x v-1|≤w) (e : Pair n) :
    |degreeCorrection x e|≤2*w := by
  have hn' : (4:ℝ)≤n := by exact_mod_cast hn
  have h2 : 0<(n:ℝ)-2 := by linarith
  have h1 : 0<(n:ℝ)-1 := by linarith
  let d := fun v => 1-(completeGraph n).degree x v
  have hd (v) : |d v|≤w := by dsimp [d]; rw [abs_sub_comm]; exact hdeg v
  have hsum : |∑ v,d v|≤(n:ℝ)*w := by
    calc
      _ ≤ ∑ v,|d v| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v : Fin n,w := sum_le_sum (fun v _ => hd v)
      _ = _ := by simp
  have ha : |(d e.val.1+d e.val.2)/((n:ℝ)-2)|≤w := by
    rw [abs_div,abs_of_pos h2,div_le_iff₀ h2]
    have hh := abs_add_le (d e.val.1) (d e.val.2)
    nlinarith [hd e.val.1,hd e.val.2]
  have hb : |(∑ v,d v)/(((n:ℝ)-2)*((n:ℝ)-1))|≤w := by
    rw [abs_div,abs_of_pos (mul_pos h2 h1),div_le_iff₀ (mul_pos h2 h1)]
    have hp : (n:ℝ)≤((n:ℝ)-2)*((n:ℝ)-1) := by nlinarith
    exact hsum.trans (by nlinarith [mul_le_mul_of_nonneg_right hp hw])
  exact (abs_sub _ _).trans (by dsimp [degreeCorrection] at *; linarith [ha,hb])

def uniform (n : ℕ) : Pair n → ℝ := fun _ => 1/((n:ℝ)-1)

lemma uniform_box (hn : 4≤n) (e : Pair n) : uniform n e∈Set.Icc (0:ℝ) 1 := by
  have hn' : (4:ℝ)≤n := by exact_mod_cast hn
  constructor
  · exact div_nonneg (by norm_num) (by linarith)
  · exact (div_le_one (by linarith)).2 (by linarith)

lemma uniform_degree (hn : 4≤n) (v : Fin n) :
    (completeGraph n).degree (uniform n) v=1 := by
  unfold uniform
  rw [degree_constant]
  have hn' : (4:ℝ)≤n := by exact_mod_cast hn
  field_simp [show (n:ℝ)-1≠0 by linarith]

def TrivialCut (S : Finset (Fin n)) : Prop := S.card=1 ∨ Sᶜ.card=1

lemma trivial_cut_degree {x : Pair n → ℝ} (hx : ∀ v,(completeGraph n).degree x v=1)
    {S : Finset (Fin n)} (hS : TrivialCut S) : (completeGraph n).cutMass x S=1 := by
  rcases hS with h|h
  · obtain ⟨v,rfl⟩ := card_eq_one.mp h
    simpa using hx v
  · obtain ⟨v,hv⟩ := card_eq_one.mp h
    have he : (completeGraph n).cutMass x S=(completeGraph n).cutMass x Sᶜ := by
      simp only [LooplessGraph.cutMass,LooplessGraph.cut_compl]
    rw [he,hv,LooplessGraph.cutMass_singleton,hx]

lemma uniform_nontrivial_cut (heven : Even n) {S : Finset (Fin n)} (hodd : Odd S.card)
    (hS : ¬TrivialCut S) : (3/2:ℝ)≤(completeGraph n).cutMass (uniform n) S := by
  have hcards : S.card+Sᶜ.card=n := by simp
  have ha : 3≤S.card := by
    have ho := Nat.odd_iff.mp hodd
    have hh : S.card≠1 := fun h => hS (Or.inl h)
    omega
  have hb : 3≤Sᶜ.card := by
    have ho := Nat.odd_iff.mp hodd
    have he := Nat.even_iff.mp heven
    have hh : Sᶜ.card≠1 := fun h => hS (Or.inr h)
    omega
  have ha' : (3:ℝ)≤S.card := by exact_mod_cast ha
  have hb' : (3:ℝ)≤Sᶜ.card := by exact_mod_cast hb
  have hc' : (S.card:ℝ)+Sᶜ.card=n := by exact_mod_cast hcards
  have hn : (6:ℝ)≤n := by linarith
  unfold uniform
  rw [cut_constant]
  rw [mul_one_div,le_div_iff₀ (by linarith : 0<(n:ℝ)-1)]
  have hp := mul_nonneg (sub_nonneg.mpr ha') (sub_nonneg.mpr hb')
  nlinarith

lemma uniform_feasible (hn : 4≤n) (heven : Even n) :
    uniform n∈(completeGraph n).polytope := by
  rw [(completeGraph n).polytope_eq_constraints (by simpa using heven)]
  refine ⟨fun e => (uniform_box hn e).1,uniform_degree hn,?_⟩
  intro S hS
  by_cases ht : TrivialCut S
  · rw [trivial_cut_degree (uniform_degree hn) ht]
  · linarith [uniform_nontrivial_cut heven hS ht]

theorem feasibility_repair (hn : 4≤n) (heven : Even n) {x : Pair n → ℝ}
    (hx : ∀ e,x e∈Set.Icc (0:ℝ) 1) {w : ℝ} (hw : 0≤w)
    (hdeg : ∀ v, |(completeGraph n).degree x v-1|≤w)
    (hcut : ∀ S : Finset (Fin n),Odd S.card → 1-w≤(completeGraph n).cutMass x S) :
    ∃ y∈(completeGraph n).polytope,∀ e,|y e-x e|≤(2+10*(n:ℝ)^2)*w := by
  let A : ℝ := 10*(n:ℝ)^2
  let c := degreeCorrection x
  let x' := fun e => x e+c e
  let t := min 1 (A*w)
  let y : Pair n → ℝ := (1-t) • x'+t • uniform n
  have hn' : (4:ℝ)≤n := by exact_mod_cast hn
  have hA : 0≤A := by dsimp [A]; positivity
  have ht : 0≤t := le_min (by norm_num) (mul_nonneg hA hw)
  have ht1 : t≤1 := min_le_left _ _
  have htw : t≤A*w := min_le_right _ _
  have hc := correction_bound hn hw hdeg
  have hx'd := correction_degree hn x
  have hx'lo (e) : -2*w≤x' e := by
    have hh := (abs_le.mp (hc e)).1
    dsimp [x',c]; linarith [(hx e).1]
  have hx'cut (S) (hS : Odd S.card) :
      1-(1+2*(Fintype.card (Pair n):ℝ))*w≤(completeGraph n).cutMass x' S := by
    have hh := (abs_le.mp (cut_bound (mul_nonneg (by norm_num) hw) hc S)).1
    dsimp [x',c]; rw [cut_add]
    linarith [hcut S hS]
  have hA1 : 2≤A/((n:ℝ)-1) := by
    apply (le_div_iff₀ (by linarith)).2
    dsimp [A]; nlinarith
  have hA2 : 1+2*(Fintype.card (Pair n):ℝ)≤A/2 := by
    have hq : (Fintype.card (Pair n):ℝ)≤(n:ℝ)^2 := by exact_mod_cast q_le_square (n:=n)
    dsimp [A]; nlinarith
  have hyd : ∀ v,(completeGraph n).degree y v=1 := by
    intro v; dsimp [y]; rw [LooplessGraph.degree_linear,hx'd,uniform_degree hn]; ring
  have hy : y∈(completeGraph n).polytope := by
    by_cases hbig : 1≤A*w
    · have htt : t=1 := min_eq_left hbig
      simpa only [y,htt,sub_self,zero_smul,one_smul,zero_add] using uniform_feasible hn heven
    · have htt : t=A*w := min_eq_right (le_of_not_ge hbig)
      rw [(completeGraph n).polytope_eq_constraints (by simpa using heven)]
      refine ⟨?_,hyd,?_⟩
      · intro e
        have h0 := mul_le_mul_of_nonneg_left (hx'lo e) (sub_nonneg.mpr ht1)
        have h1 := mul_le_mul_of_nonneg_right hA1 hw
        change 0≤(1-t)*x' e+t*uniform n e
        unfold uniform
        rw [htt] at *
        simp only [div_eq_mul_inv] at h1 ⊢
        nlinarith [mul_nonneg ht hw]
      · intro S hS
        by_cases htr : TrivialCut S
        · rw [trivial_cut_degree hyd htr]
        · have h0 := mul_le_mul_of_nonneg_left (hx'cut S hS) (sub_nonneg.mpr ht1)
          have h1 := mul_le_mul_of_nonneg_left (uniform_nontrivial_cut heven hS htr) ht
          have h2 := mul_le_mul_of_nonneg_right hA2 hw
          dsimp [y]; rw [LooplessGraph.cutMass_linear]
          have hqw : 0≤(1+2*(Fintype.card (Pair n):ℝ))*w := by positivity
          rw [htt] at *
          nlinarith [mul_nonneg ht hqw]
  refine ⟨y,hy,fun e => ?_⟩
  have hu : |uniform n e-x e|≤1 := by
    rw [abs_le]; constructor <;> linarith [(uniform_box hn e).1,(uniform_box hn e).2,(hx e).1,(hx e).2]
  have he : y e-x e=(1-t)*c e+t*(uniform n e-x e) := by dsimp [y,x']; ring
  rw [he]
  calc
    _ ≤ |(1-t)*c e|+|t*(uniform n e-x e)| := abs_add_le _ _
    _ = (1-t)*|c e|+t*|uniform n e-x e| := by rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr ht1),abs_of_nonneg ht]
    _ ≤ (1-t)*(2*w)+t*1 := add_le_add (mul_le_mul_of_nonneg_left (hc e) (sub_nonneg.mpr ht1)) (mul_le_mul_of_nonneg_left hu ht)
    _ ≤ (2+10*(n:ℝ)^2)*w := by dsimp [A] at htw; nlinarith [mul_nonneg ht hw]

end
end BinaryMatching
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy
variable {n : ℕ}

def Affine.evalReal (r : Affine n) (x : Pair n → ℝ) : ℝ :=
  (∑ e,(r.coeff e:ℝ)*x e)+r.constant

def allRows (n : ℕ) : List (Affine n) :=
  zeroRow :: ((List.finRange n).flatMap (fun v => [degreeRow v true,degreeRow v false])) ++
    (univ.toList.filter (fun S : Finset (Fin n) => decide (Odd S.card))).map cutRow

def maxRow (x : Pair n → ℝ) : Affine n := by
  classical
  exact ((allRows n).argmax (fun r => r.evalReal x)).getD zeroRow

def violation (x : Pair n → ℝ) : ℝ := (maxRow x).evalReal x

lemma maxRow_mem_argmax (x : Pair n → ℝ) :
    maxRow x ∈ (allRows n).argmax (fun r => r.evalReal x) := by
  classical
  unfold maxRow
  cases he : (allRows n).argmax (fun r => r.evalReal x) with
  | none => have hh := List.argmax_eq_none.mp he; simp [allRows] at hh
  | some r => simp

lemma row_le_violation (x : Pair n → ℝ) (r : Affine n) (hr : r∈allRows n) :
    r.evalReal x≤violation x := List.le_of_mem_argmax hr (maxRow_mem_argmax x)

lemma violation_le (x : Pair n → ℝ) (b : ℝ) (h : ∀ r∈allRows n,r.evalReal x≤b) :
    violation x≤b := h _ (List.argmax_mem (maxRow_mem_argmax x))

lemma mem_allRows (r : Affine n) : r∈allRows n ↔
    r=zeroRow ∨ (∃ v,r=degreeRow v true ∨ r=degreeRow v false) ∨
      ∃ S : Finset (Fin n),Odd S.card ∧ r=cutRow S := by
  simp only [allRows,List.mem_append,List.mem_cons,List.mem_flatMap,List.mem_finRange,
    true_and,List.mem_map,List.mem_filter,mem_toList,mem_univ]
  aesop

lemma zero_row_eval (x : Pair n → ℝ) : (zeroRow : Affine n).evalReal x=0 := by
  simp [Affine.evalReal,zeroRow]

lemma degree_row_eval_pos (x : Pair n → ℝ) (v : Fin n) :
    (degreeRow v true).evalReal x=(completeGraph n).degree x v-1 := by
  simp [Affine.evalReal,degreeRow,LooplessGraph.degree,LooplessGraph.Incident,completeGraph,
    ite_mul,sub_eq_add_neg]
  apply sum_congr rfl; intro e _; rfl

lemma degree_row_eval_neg (x : Pair n → ℝ) (v : Fin n) :
    (degreeRow v false).evalReal x=1-(completeGraph n).degree x v := by
  simp only [Affine.evalReal,degreeRow,Bool.false_eq_true,↓reduceIte,Int.cast_one,
    Int.cast_ite,Int.cast_neg,Int.cast_zero,ite_mul,neg_one_mul,zero_mul]
  have he : (∑ e : Pair n,if e.val.1=v ∨ e.val.2=v then -x e else 0)=
      -(completeGraph n).degree x v := by
    simp only [LooplessGraph.degree,LooplessGraph.Incident,completeGraph,←sum_neg_distrib]
    apply sum_congr rfl; intro e _; split_ifs <;> simp_all
  rw [he]; ring

lemma cut_row_eval (x : Pair n → ℝ) (S : Finset (Fin n)) :
    (cutRow S).evalReal x=1-(completeGraph n).cutMass x S := by
  have he (e : Pair n) : ((e.val.1∈S ∧ e.val.2∉S) ∨ (e.val.2∈S ∧ e.val.1∉S)) ↔
      (completeGraph n).Crosses S e := by
    simp only [LooplessGraph.Crosses,completeGraph]; tauto
  simp only [Affine.evalReal,cutRow,he,Int.cast_ite,Int.cast_neg,Int.cast_one,
    Int.cast_zero,ite_mul,neg_one_mul,zero_mul]
  have hsum : (∑ e : Pair n,if (completeGraph n).Crosses S e then -x e else 0)=
      -(completeGraph n).cutMass x S := by
    simp only [LooplessGraph.cutMass,LooplessGraph.cut,sum_filter,←sum_neg_distrib]
    apply sum_congr rfl; intro e _; split_ifs <;> simp_all
  rw [hsum]; ring

lemma violation_nonneg (x : Pair n → ℝ) : 0≤violation x := by
  simpa only [zero_row_eval] using row_le_violation x zeroRow ((mem_allRows _).2 (Or.inl rfl))

lemma degree_violation (x : Pair n → ℝ) (v : Fin n) :
    |(completeGraph n).degree x v-1|≤violation x := by
  have hp := row_le_violation x (degreeRow v true)
    ((mem_allRows _).2 (Or.inr (Or.inl ⟨v,Or.inl rfl⟩)))
  have hm := row_le_violation x (degreeRow v false)
    ((mem_allRows _).2 (Or.inr (Or.inl ⟨v,Or.inr rfl⟩)))
  rw [degree_row_eval_pos] at hp; rw [degree_row_eval_neg] at hm
  exact abs_le.mpr ⟨by linarith,hp⟩

lemma cut_violation (x : Pair n → ℝ) (S : Finset (Fin n)) (hS : Odd S.card) :
    1-violation x≤(completeGraph n).cutMass x S := by
  have hh := row_le_violation x (cutRow S)
    ((mem_allRows _).2 (Or.inr (Or.inr ⟨S,hS,rfl⟩)))
  rw [cut_row_eval] at hh; linarith

lemma violation_feasible (heven : Even n) {x : Pair n → ℝ}
    (hx : x∈(completeGraph n).polytope) : violation x=0 := by
  rw [(completeGraph n).polytope_eq_constraints (by simpa using heven)] at hx
  apply le_antisymm _ (violation_nonneg x)
  apply violation_le
  intro r hr
  rcases (mem_allRows r).1 hr with rfl|⟨v,rfl|rfl⟩|⟨S,hS,rfl⟩
  · rw [zero_row_eval]
  · rw [degree_row_eval_pos,hx.2.1]; norm_num
  · rw [degree_row_eval_neg,hx.2.1]; norm_num
  · rw [cut_row_eval]; linarith [hx.2.2 S hS]

lemma violation_repair (hn : 4≤n) (heven : Even n) (x : Pair n → ℝ)
    (hx : ∀ e,x e∈Set.Icc (0:ℝ) 1) : ∃ y∈(completeGraph n).polytope,
      ∀ e,|y e-x e|≤(2+10*(n:ℝ)^2)*violation x :=
  feasibility_repair hn heven hx (violation_nonneg x) (degree_violation x) (cut_violation x)

lemma row_difference (r : Affine n) (x z : Pair n → ℝ) :
    r.evalReal z=r.evalReal x+∑ e,(r.coeff e:ℝ)*(z e-x e) := by
  simp only [Affine.evalReal,mul_sub,sum_sub_distrib]; ring

lemma row_coeff_bound (r : Affine n) (hr : r∈allRows n) (e : Pair n) : |(r.coeff e:ℝ)|≤1 := by
  rcases (mem_allRows r).1 hr with rfl|⟨v,rfl|rfl⟩|⟨S,_,rfl⟩
  · simp [zeroRow]
  · simp only [degreeRow,↓reduceIte]; split_ifs <;> norm_num
  · simp only [degreeRow,Bool.false_eq_true,↓reduceIte]; split_ifs <;> norm_num
  · simp only [cutRow]; split_ifs <;> norm_num

lemma active_row_subgradient (x : Pair n → ℝ) (r : Affine n)
    (hr : r∈allRows n) (ha : r.evalReal x=violation x) (z : Pair n → ℝ) :
    violation x+∑ e,(r.coeff e:ℝ)*(z e-x e)≤violation z := by
  rw [←ha,←row_difference]
  exact row_le_violation z r hr

lemma eval_cast (a : Affine n) (x : Pair n → ℚ) :
    a.evalReal (fun e => (x e:ℝ))=(a.eval x:ℝ) := by
  simp [Affine.eval,Affine.evalReal]

lemma capacities_symm (a : Table n ℤ) (i j : Fin n) : capacities a i j=capacities a j i := by
  unfold capacities
  rcases lt_trichotomy i j with h|h|h
  · simp [h,not_lt_of_ge h.le]
  · subst j; rfl
  · simp [h,not_lt_of_ge h.le]

lemma capacities_pair (a : Table n ℤ) (e : Pair n) :
    capacities a e.val.1 e.val.2=(entry a e).toNat := by
  simp [capacities,e.property,entry]

lemma cut_coordinates (D : ℕ) (a : Table n ℤ) (ha : ∀ e,0≤entry a e)
    (S : Finset (Fin n)) :
    (completeGraph n).cutMass (fun e => (coordinates D a e:ℝ)) S=
      (UnitFlow.cutCapacity (capacities a) S:ℝ)/(D:ℝ) := by
  have hx : (fun e => (coordinates D a e:ℝ))=
      (fun e : Pair n => (capacities a e.val.1 e.val.2:ℝ)/(D:ℝ)) := by
    funext e
    simp only [coordinates,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,capacities_pair]
    have he : ((entry a e).toNat:ℝ)=((entry a e:ℤ):ℝ) := by exact_mod_cast Int.toNat_of_nonneg (ha e)
    rw [he]
  rw [hx,cut_from_symm (fun i j => (capacities a i j:ℝ)/(D:ℝ)) (fun i j => by rw [capacities_symm a i j])]
  simp only [UnitFlow.cutCapacity,Nat.cast_sum,sum_div]

lemma activeRows_nonempty (a : Table n ℤ) : activeRows a≠[] := by simp [activeRows]

lemma activeRow_mem_argmax (D : ℕ) (a : Table n ℤ) :
    activeRow D a∈(activeRows a).argmax (fun r => r.eval (coordinates D a)) := by
  unfold activeRow
  cases he : (activeRows a).argmax (fun r => r.eval (coordinates D a)) with
  | none => exact (activeRows_nonempty a (List.argmax_eq_none.mp he)).elim
  | some r => simp

lemma mem_activeRows (a : Table n ℤ) (r : Affine n) : r∈activeRows a ↔
    r=zeroRow ∨ (∃ v,r=degreeRow v true ∨ r=degreeRow v false) ∨
      r=cutRow (OddMincut.oddCut (capacities a) univ) := by
  simp only [activeRows,List.mem_append,List.mem_cons,List.mem_flatMap,List.mem_finRange,
    true_and]
  aesop

lemma activeRow_correct (hn : 2≤n) (heven : Even n) {D : ℕ} (hD : 0<D)
    (a : Table n ℤ) (ha : ∀ e,0≤entry a e) :
    activeRow D a∈allRows n ∧
      (activeRow D a).evalReal (fun e => (coordinates D a e:ℝ))=
        violation (fun e => (coordinates D a e:ℝ)) := by
  let S₀ := OddMincut.oddCut (capacities a) univ
  have hh := OddMincut.oddCut_correct (capacities a) (capacities_symm a) univ
    (by simpa using heven) (by simpa using hn)
  have hodd : Odd S₀.card := by simpa [OddCutParity.OddSide] using hh.1
  have hmin (S : Finset (Fin n)) (hS : Odd S.card) :
      UnitFlow.cutCapacity (capacities a) S₀≤UnitFlow.cutCapacity (capacities a) S :=
    hh.2 S (by simpa [OddCutParity.OddSide] using hS)
  have hsub : ∀ r∈activeRows a,r∈allRows n := by
    intro r hr
    rcases (mem_activeRows a r).1 hr with h|h|h
    · exact (mem_allRows r).2 (Or.inl h)
    · exact (mem_allRows r).2 (Or.inr (Or.inl h))
    · exact (mem_allRows r).2 (Or.inr (Or.inr ⟨S₀,hodd,h⟩))
  have ham := List.argmax_mem (activeRow_mem_argmax D a)
  refine ⟨hsub _ ham,le_antisymm (row_le_violation _ _ (hsub _ ham)) ?_⟩
  apply violation_le
  intro r hr
  have hdom (r' : Affine n) (hr' : r'∈activeRows a) :
      r'.evalReal (fun e => (coordinates D a e:ℝ))≤
        (activeRow D a).evalReal (fun e => (coordinates D a e:ℝ)) := by
    simp only [eval_cast]
    exact_mod_cast List.le_of_mem_argmax hr' (activeRow_mem_argmax D a)
  rcases (mem_allRows r).1 hr with h|h|⟨S,hS,rfl⟩
  · exact hdom r ((mem_activeRows a r).2 (Or.inl h))
  · exact hdom r ((mem_activeRows a r).2 (Or.inr (Or.inl h)))
  · apply le_trans _ (hdom (cutRow S₀) ((mem_activeRows a _).2 (Or.inr (Or.inr rfl))))
    rw [cut_row_eval,cut_row_eval,cut_coordinates D a ha,cut_coordinates D a ha]
    have hd : (0:ℝ)≤D := (Nat.cast_pos.mpr hD).le
    have hle : (UnitFlow.cutCapacity (capacities a) S₀:ℝ)≤
        UnitFlow.cutCapacity (capacities a) S := by exact_mod_cast hmin S hS
    linarith [div_le_div_of_nonneg_right hle hd]

end
end BinaryMatching.Algorithm
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset

lemma foldl_max_le (l : List ℕ) (a b : ℕ) (ha : a≤b) (hl : ∀ x∈l,x≤b) :
    l.foldl max a≤b := by
  induction l generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    exact ih (max a x) (max_le ha (hl x (by simp))) (fun y hy => hl y (by simp [hy]))

lemma le_foldl_max (l : List ℕ) (a : ℕ) : a≤l.foldl max a := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih (max a x))

lemma mem_le_foldl_max (l : List ℕ) (a x : ℕ) (hx : x∈l) : x≤l.foldl max a := by
  induction l generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl|h
    · exact (le_max_right a x).trans (le_foldl_max ys (max a x))
    · exact ih (max a y) h

lemma record_log_le_B (G : Input) (r : Record) (hr : r∈G.records) : Nat.log2 r.multiplicity≤B G :=
  mem_le_foldl_max _ 0 _ (List.mem_map.mpr ⟨r,hr,rfl⟩)

lemma multiplicity_log_le_B (G : Input) (e : Pair G.n) : Nat.log2 (multiplicity G e)≤B G := by
  unfold multiplicity
  cases he : G.records.find? (fun r => r.left=e.val.1.val && r.right=e.val.2.val) with
  | none => simp
  | some r => exact record_log_le_B G r (List.mem_of_find?_eq_some he)

lemma B_le_L (G : Input) : B G≤L G := by
  have h : B G≤G.n+B G+1 := by omega
  have hp : 1≤G.n+B G+1 := by omega
  have hpow : G.n+B G+1≤(G.n+B G+1)^3 := by exact Nat.le_self_pow (by omega) _
  unfold L
  omega

lemma beta_bound (G : Input) (e : Pair G.n) : |(beta G e:ℝ)|≤L G := by
  unfold beta
  split_ifs
  · simp
  · have hh := (multiplicity_log_le_B G e).trans (B_le_L G)
    norm_cast

lemma piece_slope_bound (k : ℕ) (p : Piece) (hp : p∈pieces k) : |(p.slope:ℝ)|≤k := by
  rcases (mem_pieces k p).1 hp with rfl|⟨j,hj,rfl⟩
  · simp
  · simp only [Int.cast_sub,Int.cast_natCast,Int.cast_one]
    have hj' : (j:ℝ)+1≤k := by exact_mod_cast hj
    have hj0 : (0:ℝ)≤j := by positivity
    rw [abs_le]; constructor <;> linarith

lemma piece_supergradient (k : ℕ) (p : Piece) (hp : p∈pieces k) (x : ℝ)
    (ha : p.evalReal x=psiReal k x) (z : ℝ) :
    psiReal k z≤psiReal k x+(p.slope:ℝ)*(z-x) := by
  have hh := psiReal_le_piece k z p hp
  rw [←ha]
  calc
    _ ≤ p.evalReal z := hh
    _ = p.evalReal x+(p.slope:ℝ)*(z-x) := by unfold Piece.evalReal; ring

lemma selectedPiece_supergradient (k : ℕ) (x : ℚ) (z : ℝ) :
    psiReal k z≤psiReal k (x:ℝ)+(slope k x:ℝ)*(z-(x:ℝ)) := by
  apply piece_supergradient k (selectedPiece k x)
    (List.argmin_mem (selectedPiece_mem_argmin k x)) (x:ℝ) _ z
  rw [realPsi_cast]
  simp [Piece.evalReal,Piece.eval,psi]

lemma psiReal_abs_sub (k : ℕ) (x y : ℝ) : |psiReal k x-psiReal k y|≤k*|x-y| := by
  have h (a b : ℝ) : psiReal k a-psiReal k b≤k*|a-b| := by
    have hm := List.argmin_mem (selectedReal_mem_argmin k b)
    have hh := piece_supergradient k (selectedReal k b) hm b rfl a
    have hb := piece_slope_bound k _ hm
    have hab := le_abs_self ((selectedReal k b).slope*(a-b))
    rw [abs_mul] at hab
    have hu := mul_le_mul_of_nonneg_right hb (abs_nonneg (a-b))
    linarith
  rw [abs_le]
  have hx := h x y
  have hy := h y x
  rw [abs_sub_comm y x] at hy
  exact ⟨by linarith,hx⟩

def objective (G : Input) (x : Pair G.n → ℝ) : ℝ :=
  ∑ e, (psiReal (K G.n) (x e)+(beta G e:ℝ)*x e)

def penalized (G : Input) (x : Pair G.n → ℝ) : ℝ :=
  objective G x-(M₀ G:ℝ)*violation x

lemma objective_lipschitz (G : Input) (x y : Pair G.n → ℝ) :
    |objective G x-objective G y|≤(K G.n+L G:ℝ)*∑ e,|x e-y e| := by
  unfold objective
  rw [←sum_sub_distrib,mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum; intro e _
  have he : psiReal (K G.n) (x e)+(beta G e:ℝ)*x e-
      (psiReal (K G.n) (y e)+(beta G e:ℝ)*y e)=
      (psiReal (K G.n) (x e)-psiReal (K G.n) (y e))+(beta G e:ℝ)*(x e-y e) := by ring
  rw [he]
  have hb := mul_le_mul_of_nonneg_right (beta_bound G e) (abs_nonneg (x e-y e))
  have hh := abs_add_le (psiReal (K G.n) (x e)-psiReal (K G.n) (y e)) ((beta G e:ℝ)*(x e-y e))
  rw [abs_mul] at hh
  linarith [psiReal_abs_sub (K G.n) (x e) (y e)]

lemma exact_penalty (G : Input) (hn : 4≤G.n) (heven : Even G.n)
    (x : Pair G.n → ℝ) (hx : ∀ e,x e∈Set.Icc (0:ℝ) 1) :
    ∃ y∈(completeGraph G.n).polytope,penalized G x≤objective G y := by
  obtain ⟨y,hy,hdist⟩ := violation_repair hn heven x hx
  refine ⟨y,hy,?_⟩
  have hsum : (∑ e,|x e-y e|)≤(q G.n:ℝ)*(2+10*(G.n:ℝ)^2)*violation x := by
    calc
      _ ≤ ∑ _e : Pair G.n,(2+10*(G.n:ℝ)^2)*violation x := by
        apply sum_le_sum; intro e _; rw [abs_sub_comm]; exact hdist e
      _ = _ := by simp [q,mul_assoc]
  have hh := objective_lipschitz G x y
  have hmul := mul_le_mul_of_nonneg_left hsum (show (0:ℝ)≤K G.n+L G by positivity)
  have hM : (M₀ G:ℝ)=(q G.n:ℝ)*(K G.n+L G)*(2+10*(G.n:ℝ)^2) := by
    simp [M₀,A₀]
  unfold penalized
  rw [hM]
  have hab := le_abs_self (objective G x-objective G y)
  nlinarith

lemma penalized_feasible (G : Input) (heven : Even G.n) {x : Pair G.n → ℝ}
    (hx : x∈(completeGraph G.n).polytope) : penalized G x=objective G x := by
  simp [penalized,violation_feasible heven hx]

lemma trialValue_cast (G : Input) (a : Table G.n ℤ) (r : Affine G.n) :
    (trialValue G a r:ℝ)=objective G (fun e => (coordinates (D₀ G) a e:ℝ))-
        (M₀ G:ℝ)*r.evalReal (fun e => (coordinates (D₀ G) a e:ℝ)) := by
  simp [trialValue,objective,realPsi_cast,eval_cast]

lemma trialValue_correct (G : Input) (hn : 2≤G.n) (heven : Even G.n)
    (hD : 0<D₀ G) (a : Table G.n ℤ) (ha : ∀ e,0≤entry a e) :
    (trialValue G a (activeRow (D₀ G) a):ℝ)=
      penalized G (fun e => (coordinates (D₀ G) a e:ℝ)) := by
  rw [trialValue_cast,(activeRow_correct hn heven hD a ha).2]
  rfl

lemma gradient_supergradient (G : Input) (hn : 2≤G.n) (heven : Even G.n)
    (hD : 0<D₀ G) (a : Table G.n ℤ) (ha : ∀ e,0≤entry a e)
    (z : Pair G.n → ℝ) :
    penalized G z≤penalized G (fun e => (coordinates (D₀ G) a e:ℝ))+
      ∑ e,(gradient G a (activeRow (D₀ G) a) e:ℝ)*(z e-(coordinates (D₀ G) a e:ℝ)) := by
  let x := fun e => (coordinates (D₀ G) a e:ℝ)
  let r := activeRow (D₀ G) a
  obtain ⟨hr,hract⟩ := activeRow_correct hn heven hD a ha
  have hrow := active_row_subgradient x r hr hract z
  have hf : objective G z≤objective G x+
      ∑ e,((slope (K G.n) (coordinates (D₀ G) a e):ℝ)+(beta G e:ℝ))*(z e-x e) := by
    rw [objective,objective,←sum_add_distrib]
    apply sum_le_sum; intro e _
    have hh := selectedPiece_supergradient (K G.n) (coordinates (D₀ G) a e) (z e)
    dsimp [x] at *; nlinarith
  have hm := mul_le_mul_of_nonneg_left hrow (show (0:ℝ)≤M₀ G by positivity)
  have hgrad : (∑ e,(gradient G a r e:ℝ)*(z e-x e))=
      (∑ e,((slope (K G.n) (coordinates (D₀ G) a e):ℝ)+(beta G e:ℝ))*(z e-x e))-
        (M₀ G:ℝ)*∑ e,(r.coeff e:ℝ)*(z e-x e) := by
    simp only [gradient,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_natCast,
      sub_mul,sum_sub_distrib,mul_assoc,mul_sum]
  change penalized G z≤penalized G x+∑ e,(gradient G a r e:ℝ)*(z e-x e)
  rw [hgrad]
  unfold penalized
  linarith

lemma gradient_bound (G : Input) (hn : 2≤G.n) (heven : Even G.n)
    (hD : 0<D₀ G) (a : Table G.n ℤ) (ha : ∀ e,0≤entry a e) (e : Pair G.n) :
    |(gradient G a (activeRow (D₀ G) a) e:ℝ)|≤K G.n+L G+M₀ G := by
  have hrow := row_coeff_bound _ (activeRow_correct hn heven hD a ha).1 e
  have hs := piece_slope_bound (K G.n) _ (List.argmin_mem
    (selectedPiece_mem_argmin (K G.n) (coordinates (D₀ G) a e)))
  change |(slope (K G.n) (coordinates (D₀ G) a e):ℝ)|≤K G.n at hs
  have hm := mul_le_mul_of_nonneg_left hrow (show (0:ℝ)≤M₀ G by positivity)
  have hcast : (gradient G a (activeRow (D₀ G) a) e:ℝ)=
      (slope (K G.n) (coordinates (D₀ G) a e):ℝ)+(beta G e:ℝ)-
        (M₀ G:ℝ)*((activeRow (D₀ G) a).coeff e:ℝ) := by simp [gradient]
  rw [hcast]
  have hh := abs_sub ((slope (K G.n) (coordinates (D₀ G) a e):ℝ)+(beta G e:ℝ))
    ((M₀ G:ℝ)*((activeRow (D₀ G) a).coeff e:ℝ))
  rw [abs_mul,abs_of_nonneg (show (0:ℝ)≤M₀ G by positivity)] at hh
  linarith [abs_add_le (slope (K G.n) (coordinates (D₀ G) a e):ℝ) (beta G e:ℝ),beta_bound G e]

lemma gradient_square_bound (G : Input) (hn : 2≤G.n) (heven : Even G.n)
    (hD : 0<D₀ G) (a : Table G.n ℤ) (ha : ∀ e,0≤entry a e) :
    (∑ e,(gradient G a (activeRow (D₀ G) a) e:ℝ)^2)≤D₀ G := by
  calc
    _ ≤ ∑ _e : Pair G.n,(K G.n+L G+M₀ G:ℝ)^2 := by
      apply sum_le_sum; intro e _
      have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (gradient_bound G hn heven hD a ha e)
      simpa only [sq_abs] using hh
    _ = D₀ G := by simp [D₀,q]

end
end BinaryMatching.Algorithm
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

lemma q_pos {n : ℕ} (hn : 2 ≤ n) : 0 < q n := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by change 0 < 1; omega⟩⟩

lemma D₀_pos (G : Input) (hn : 2 ≤ G.n) : 0 < D₀ G := by
  have hL : 0 < L G := by unfold L; positivity
  exact Nat.mul_pos (q_pos hn) (pow_pos (by omega) _)

lemma clip_sq_le {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) (t : ℝ) :
    (min 1 (max 0 t)-z)^2 ≤ (t-z)^2 := by
  by_cases ht : t ≤ 0
  · rw [max_eq_left ht, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg ht hz.1, sq_nonneg t]
  · have ht0 : 0 ≤ t := le_of_not_ge ht
    rw [max_eq_right ht0]
    by_cases ht1 : 1 ≤ t
    · rw [min_eq_left ht1]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (show 0 ≤ t+1-2*z by linarith [hz.2])]
    · rw [min_eq_right (le_of_not_ge ht1)]

lemma update_box (G : Input) (a : Table G.n ℤ) (r : Affine G.n) (e : Pair G.n) :
    entry (update G a r) e ∈ Set.Icc (0:ℤ) (D₀ G) := by
  rw [update, at_toTable]
  exact ⟨le_min (Int.natCast_nonneg _) (le_max_left _ _), min_le_left _ _⟩

lemma iterate_box (G : Input) (j : ℕ) (e : Pair G.n) :
    entry (iterate G j).numerators e ∈ Set.Icc (0:ℤ) (D₀ G) := by
  cases j with
  | zero => simp [iterate, initial, at_tabulate]
  | succ j => exact update_box G _ _ e

def point (G : Input) (j : ℕ) (e : Pair G.n) : ℝ :=
  (coordinates (D₀ G) (iterate G j).numerators e : ℝ)

def sampledValue (G : Input) (j : ℕ) : ℚ :=
  trialValue G (iterate G j).numerators (activeRow (D₀ G) (iterate G j).numerators)

lemma coordinates_cast {n : ℕ} (D : ℕ) (a : Table n ℤ) (e : Pair n) :
    (coordinates D a e : ℝ) = (↑(entry a e) : ℝ)/(D:ℝ) := by
  simp [coordinates]

lemma point_box (G : Input) (hn : 2 ≤ G.n) (j : ℕ) (e : Pair G.n) :
    point G j e ∈ Set.Icc (0:ℝ) 1 := by
  have hD : (0:ℝ) < D₀ G := by exact_mod_cast D₀_pos G hn
  have ha := iterate_box G j e
  have ha' : (↑(entry (iterate G j).numerators e) : ℝ) ∈ Set.Icc (0:ℝ) (D₀ G) :=
    ⟨by exact_mod_cast ha.1, by exact_mod_cast ha.2⟩
  rw [point, coordinates_cast]
  exact ⟨div_nonneg ha'.1 hD.le, (div_le_one hD).mpr ha'.2⟩

lemma point_zero (G : Input) (e : Pair G.n) : point G 0 e=0 := by
  simp [point, coordinates, iterate, initial, at_tabulate]

lemma point_succ (G : Input) (hn : 2 ≤ G.n) (j : ℕ) (e : Pair G.n) :
    point G (j+1) e = min 1 (max 0 (point G j e+
      (gradient G (iterate G j).numerators (activeRow (D₀ G) (iterate G j).numerators) e:ℝ)/(D₀ G:ℝ))) := by
  have hD : (0:ℝ) < D₀ G := by exact_mod_cast D₀_pos G hn
  simp only [point, iterate, step, coordinates_cast, update, at_toTable,
    Int.cast_min, Int.cast_max, Int.cast_natCast, Int.cast_zero, Int.cast_add]
  rw [← min_div_div_right hD.le, ← max_div_div_right hD.le]
  rw [div_self hD.ne', zero_div, add_div]

lemma sampledValue_correct (G : Input) (hn : 2 ≤ G.n) (heven : Even G.n) (j : ℕ) :
    (sampledValue G j:ℝ)=penalized G (point G j) :=
  trialValue_correct G hn heven (D₀_pos G hn) _ (fun e => (iterate_box G j e).1)

lemma best_spec (G : Input) (t : ℕ) :
    ∃ v : ℚ, (iterate G (t+1)).best=some v ∧
      (∃ j < t+1, sampledValue G j=v) ∧
      ∀ j < t+1, sampledValue G j≤v := by
  induction t with
  | zero =>
    refine ⟨sampledValue G 0, rfl, ⟨0, by omega, rfl⟩, ?_⟩
    intro j hj
    have : j=0 := by omega
    subst j; rfl
  | succ t ih =>
    obtain ⟨v, hv, ⟨i, hi, hiv⟩, hmax⟩ := ih
    refine ⟨max (sampledValue G (t+1)) v, ?_, ?_, ?_⟩
    · change some ((iterate G (t+1)).best.elim (sampledValue G (t+1))
        (max (sampledValue G (t+1)))) = _
      rw [hv]; rfl
    · by_cases h : v ≤ sampledValue G (t+1)
      · exact ⟨t+1, by omega, (max_eq_left h).symm⟩
      · exact ⟨i, by omega, hiv.trans (max_eq_right (le_of_not_ge h)).symm⟩
    · intro j hj
      by_cases h : j=t+1
      · subst j; exact le_max_left _ _
      · exact (hmax j (by omega)).trans (le_max_right _ _)

def squareDistance {I : Type*} [Fintype I] (x z : I → ℝ) : ℝ :=
  ∑ e, (x e-z e)^2

lemma squareDistance_nonneg {I : Type*} [Fintype I] (x z : I → ℝ) :
    0 ≤ squareDistance x z := sum_nonneg fun _e _ => sq_nonneg _

lemma squareDistance_zero_bound (G : Input) (z : Pair G.n → ℝ)
    (hz : ∀ e, z e∈Set.Icc (0:ℝ) 1) : squareDistance (point G 0) z ≤ q G.n := by
  calc
    _ ≤ ∑ _e : Pair G.n, (1:ℝ) := by
      apply sum_le_sum; intro e _
      rw [point_zero]; nlinarith [(hz e).1, (hz e).2]
    _ = _ := by simp [q]

lemma distance_step (G : Input) (hn : 2 ≤ G.n) (heven : Even G.n) (j : ℕ)
    (z : Pair G.n → ℝ) (hz : ∀ e,z e∈Set.Icc (0:ℝ) 1) :
    2*(penalized G z-penalized G (point G j)) ≤
      (D₀ G:ℝ)*(squareDistance (point G j) z-squareDistance (point G (j+1)) z)+1 := by
  let x := point G j
  let g := fun e => (gradient G (iterate G j).numerators
    (activeRow (D₀ G) (iterate G j).numerators) e:ℝ)
  let D : ℝ := D₀ G
  have hD : 0<D := by change 0<(D₀ G:ℝ); exact_mod_cast D₀_pos G hn
  have hs : squareDistance (point G (j+1)) z ≤ ∑ e,(x e+g e/D-z e)^2 := by
    apply sum_le_sum; intro e _
    rw [point_succ G hn]
    exact clip_sq_le (hz e) _
  have he : D*(∑ e,(x e+g e/D-z e)^2) = D*squareDistance x z+
      2*(∑ e,g e*(x e-z e))+(∑ e,(g e)^2)/D := by
    calc
      _ = ∑ e, (D*(x e-z e)^2+2*(g e*(x e-z e))+(g e)^2/D) := by
        rw [mul_sum]
        apply sum_congr rfl; intro e _
        field_simp; ring
      _ = _ := by simp only [sum_add_distrib, ← mul_sum, ← sum_div, squareDistance]
  have hb : (∑ e,(g e)^2)/D ≤ 1 := by
    apply (div_le_one hD).mpr
    exact gradient_square_bound G hn heven (D₀_pos G hn) _ (fun e => (iterate_box G j e).1)
  have hg := gradient_supergradient G hn heven (D₀_pos G hn) (iterate G j).numerators
    (fun e => (iterate_box G j e).1) z
  have hsign : (∑ e,g e*(x e-z e)) = -(∑ e,g e*(z e-x e)) := by
    rw [← sum_neg_distrib]; apply sum_congr rfl; intro e _; ring
  change penalized G z ≤ penalized G x+∑ e,g e*(z e-x e) at hg
  have hh := mul_le_mul_of_nonneg_left hs hD.le
  rw [he, hsign] at hh
  change 2*(penalized G z-penalized G x) ≤ D*(squareDistance x z-squareDistance (point G (j+1)) z)+1
  linarith

lemma trial_max_bound (G : Input) (hn : 2 ≤ G.n) (heven : Even G.n) :
    ∃ v : ℚ, (iterate G (q G.n*D₀ G)).best=some v ∧
      (∃ j < q G.n*D₀ G, sampledValue G j=v) ∧
      ∀ z : Pair G.n → ℝ, (∀ e,z e∈Set.Icc (0:ℝ) 1) →
        penalized G z ≤ (v:ℝ)+1 := by
  let T := q G.n*D₀ G
  have hT : 0<T := Nat.mul_pos (q_pos hn) (D₀_pos G hn)
  obtain ⟨v,hv,hatt,hmax⟩ := best_spec G (T-1)
  have heT : T-1+1=T := by omega
  rw [heT] at hv hatt hmax
  refine ⟨v,hv,hatt,?_⟩
  intro z hz
  have htR : (0:ℝ)<T := by exact_mod_cast hT
  have hsteps := sum_le_sum (s := range T) (fun j _ => distance_step G hn heven j z hz)
  have hilower : (T:ℝ)*(2*(penalized G z-(v:ℝ))) ≤
      ∑ j∈range T,2*(penalized G z-penalized G (point G j)) := by
    calc
      _ = ∑ _j∈range T,2*(penalized G z-(v:ℝ)) := by simp
      _ ≤ _ := by
        apply sum_le_sum; intro j hj
        have hjv : (sampledValue G j:ℝ)≤(v:ℝ) := by
          exact_mod_cast hmax j (mem_range.mp hj)
        rw [sampledValue_correct G hn heven] at hjv
        linarith
  have htel : (∑ j∈range T, ((D₀ G:ℝ)*
      (squareDistance (point G j) z-squareDistance (point G (j+1)) z)+1)) =
      (D₀ G:ℝ)*(squareDistance (point G 0) z-squareDistance (point G T) z)+T := by
    rw [sum_add_distrib,←mul_sum,sum_range_sub']
    simp
  rw [htel] at hsteps
  have hend := squareDistance_nonneg (point G T) z
  have hstart := squareDistance_zero_bound G z hz
  have hD : (0:ℝ)<D₀ G := by exact_mod_cast D₀_pos G hn
  have he : (T:ℝ)=(q G.n:ℝ)*(D₀ G:ℝ) := by dsimp [T]; norm_cast
  have hdist : (D₀ G:ℝ)*(squareDistance (point G 0) z-squareDistance (point G T) z)≤T := by
    rw [he]; nlinarith
  nlinarith

theorem R_objective_bracket (G : Input) (hn : 4 ≤ G.n) (heven : Even G.n) :
    (∃ y∈(completeGraph G.n).polytope,(R G:ℝ)≤objective G y) ∧
      ∀ z∈(completeGraph G.n).polytope,objective G z≤(R G:ℝ)+2 := by
  obtain ⟨v,hv,⟨j,_hj,hjv⟩,hbound⟩ := trial_max_bound G (by omega) heven
  have hR : (R G:ℝ)=(Int.floor (v:ℝ):ℝ) := by
    simp only [R,hv,Option.getD_some,Rat.floor_cast]
  have hfloor : (R G:ℝ)≤(v:ℝ) := by rw [hR]; exact Int.floor_le _
  have hvfloor : (v:ℝ)<(R G:ℝ)+1 := by rw [hR]; exact Int.lt_floor_add_one _
  constructor
  · obtain ⟨y,hy,hyval⟩ := exact_penalty G hn heven (point G j) (point_box G (by omega) j)
    refine ⟨y,hy,hfloor.trans ?_⟩
    rw [←hjv,sampledValue_correct G (by omega) heven]
    exact hyval
  · intro z hz
    have hh := hbound z ((completeGraph G.n).coordinate_mem_Icc hz)
    rw [penalized_feasible G heven hz] at hh
    linarith

end
end BinaryMatching.Algorithm
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

def smoothObjective (G : Input) (x : Pair G.n → ℝ) : ℝ :=
  entropy x/Real.log 2+∑ e,(beta G e:ℝ)*x e

def Z (G : Input) : ℝ := (completeGraph G.n).weightedZ (fun e => (beta G e:ℝ))
def logZ (G : Input) : ℝ := Real.log (Z G)/Real.log 2

lemma complete_matching_nonempty {n : ℕ} (hn : 4≤ n) (heven : Even n) :
    Nonempty (completeGraph n).Matching := by
  obtain ⟨p,hp⟩ := ((completeGraph n).mem_polytope_iff _).mp (uniform_feasible hn heven)
  by_contra h
  have : IsEmpty (completeGraph n).Matching := not_nonempty_iff.mp h
  simpa using hp.1.2

lemma mass_half {n : ℕ} (heven : Even n) {x : Pair n → ℝ}
    (hx : x∈(completeGraph n).polytope) : (∑ e,x e)=(n:ℝ)/2 := by
  obtain ⟨r,hr⟩ := heven
  have hn : Fintype.card (Fin n)=2*r := by simp; omega
  rw [(completeGraph n).marginal_sum hn hx]
  have hn' : (n:ℝ)=2*(r:ℝ) := by exact_mod_cast (show n=2*r by omega)
  rw [hn']; ring

lemma q_dyadic_le_one (n : ℕ) : (q n:ℝ)*dyadic (K n)≤1 := by
  have hh : (q n:ℝ)≤(2:ℝ)^(K n) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1<2) (q n)
  rw [dyadic,inv_pow,←div_eq_mul_inv]
  exact (div_le_one (by positivity)).mpr hh

lemma objective_compare (G : Input) (hn : 2≤ G.n) (heven : Even G.n)
    {x : Pair G.n → ℝ} (hx : x∈(completeGraph G.n).polytope) :
    objective G x≤ smoothObjective G x ∧ smoothObjective G x≤ objective G x+G.n := by
  have he : smoothObjective G x-objective G x=
      ∑ e,(phi (x e)-psiReal (K G.n) (x e)) := by
    simp only [smoothObjective,objective,phi,entropy,sum_add_distrib,sum_sub_distrib,←sum_div]
    ring
  have hnon : 0≤∑ e,(phi (x e)-psiReal (K G.n) (x e)) :=
    sum_nonneg fun e _ => (dyadic_entropy_error (K G.n) ((completeGraph G.n).coordinate_mem_Icc hx e)).1
  have hupper : (∑ e,(phi (x e)-psiReal (K G.n) (x e)))≤(G.n:ℝ)/2+1 := by
    calc
      _ ≤ ∑ e,(x e+dyadic (K G.n)) := sum_le_sum fun e _ =>
        (dyadic_entropy_error (K G.n) ((completeGraph G.n).coordinate_mem_Icc hx e)).2
      _ = (G.n:ℝ)/2+(q G.n:ℝ)*dyadic (K G.n) := by
        rw [sum_add_distrib,mass_half heven hx]; simp [q]
      _ ≤ _ := by linarith [q_dyadic_le_one G.n]
  have hn' : (2:ℝ)≤ G.n := by exact_mod_cast hn
  constructor <;> linarith

lemma Z_pos (G : Input) (hn : 4≤ G.n) (heven : Even G.n) : 0< Z G := by
  have := complete_matching_nonempty hn heven
  exact expSum_pos _

lemma smooth_lower_partition (G : Input) (hn : 4≤ G.n) (heven : Even G.n)
    {x : Pair G.n → ℝ} (hx : x∈(completeGraph G.n).polytope) :
    smoothObjective G x-4*(G.n:ℝ)≤ logZ G := by
  have hPM := complete_matching_nonempty hn heven
  obtain ⟨r,hr⟩ := heven
  have hn' : Fintype.card (Fin G.n)=2*r := by simp; omega
  have hent := ((completeGraph G.n).entropy_binary_scale hPM hn' hx).1
  have hvar := (completeGraph G.n).weighted_variational_le (fun e => (beta G e:ℝ)) hx
  simp only [Fintype.card_fin] at hent
  dsimp only [smoothObjective,logZ,Z]
  linarith

lemma smooth_upper_partition (G : Input) (hn : 4≤ G.n) (heven : Even G.n) :
    ∃ x∈(completeGraph G.n).polytope,logZ G≤ smoothObjective G x+G.n := by
  have hPM := complete_matching_nonempty hn heven
  obtain ⟨x,hx,hvar⟩ := (completeGraph G.n).weighted_variational_attained (fun e => (beta G e:ℝ))
  obtain ⟨r,hr⟩ := heven
  have hn' : Fintype.card (Fin G.n)=2*r := by simp; omega
  have hent := ((completeGraph G.n).entropy_binary_scale hPM hn' hx).2
  simp only [Fintype.card_fin] at hent
  refine ⟨x,hx,?_⟩
  dsimp only [smoothObjective,logZ,Z]
  linarith

theorem R_partition_bracket (G : Input) (hn : 4≤ G.n) (heven : Even G.n) :
    (R G:ℝ)-4*(G.n:ℝ)≤ logZ G ∧ logZ G≤(R G:ℝ)+3*(G.n:ℝ) := by
  obtain ⟨⟨y,hy,hylow⟩,hupp⟩ := R_objective_bracket G hn heven
  constructor
  · have hobj := (objective_compare G (by omega) heven hy).1
    have hpart := smooth_lower_partition G hn heven hy
    linarith
  · obtain ⟨x,hx,hpart⟩ := smooth_upper_partition G hn heven
    have hobj := (objective_compare G (by omega) heven hx).2
    have hU := hupp x hx
    have hn' : (4:ℝ)≤ G.n := by exact_mod_cast hn
    linarith

end
end BinaryMatching.Algorithm
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

def edgeWeight (G : Input) (e : Pair G.n) : ℝ := Real.exp (Real.log 2*(beta G e:ℝ))
def matchingWeight (G : Input) (M : (completeGraph G.n).Matching) : ℝ :=
  ∏ e∈M.val,edgeWeight G e

def validMatching (G : Input) (M : (completeGraph G.n).Matching) : Prop :=
  ∀ e∈M.val,0< multiplicity G e

def goodWeight (G : Input) (M : (completeGraph G.n).Matching) : ℝ :=
  @ite ℝ (validMatching G M) (Classical.propDecidable _) (matchingWeight G M) 0

def badWeight (G : Input) (M : (completeGraph G.n).Matching) : ℝ :=
  @ite ℝ (validMatching G M) (Classical.propDecidable _) 0 (matchingWeight G M)

def Zgood (G : Input) : ℝ := ∑ M,goodWeight G M
def Zbad (G : Input) : ℝ := ∑ M,badWeight G M

def multProduct (G : Input) (M : (completeGraph G.n).Matching) : ℕ :=
  ∏ e∈M.val,multiplicity G e

lemma matchingWeight_exp (G : Input) (M : (completeGraph G.n).Matching) :
    matchingWeight G M=Real.exp (Real.log 2*((completeGraph G.n).score (fun e => (beta G e:ℝ)) M)) := by
  rw [LooplessGraph.score,mul_sum,Real.exp_sum]
  rfl

lemma matchingWeight_pos (G : Input) (M : (completeGraph G.n).Matching) : 0< matchingWeight G M := by
  rw [matchingWeight_exp]; exact Real.exp_pos _

lemma Z_decompose (G : Input) : Z G=Zgood G+Zbad G := by
  unfold Z LooplessGraph.weightedZ expSum Zgood Zbad
  rw [←sum_add_distrib]
  apply sum_congr rfl; intro M _
  rw [←matchingWeight_exp]
  unfold goodWeight badWeight
  split_ifs <;> simp

lemma goodWeight_nonneg (G : Input) (M : (completeGraph G.n).Matching) : 0≤ goodWeight G M := by
  unfold goodWeight; split_ifs
  · exact (matchingWeight_pos G M).le
  · rfl

lemma badWeight_nonneg (G : Input) (M : (completeGraph G.n).Matching) : 0≤ badWeight G M := by
  unfold badWeight; split_ifs
  · rfl
  · exact (matchingWeight_pos G M).le

lemma Zgood_nonneg (G : Input) : 0≤ Zgood G := sum_nonneg fun M _ => goodWeight_nonneg G M
lemma Zbad_nonneg (G : Input) : 0≤ Zbad G := sum_nonneg fun M _ => badWeight_nonneg G M

lemma edgeWeight_present (G : Input) (e : Pair G.n) (he : 0< multiplicity G e) :
    edgeWeight G e=(2:ℝ)^Nat.log2 (multiplicity G e) := by
  rw [edgeWeight,beta,ite_eq_right (by omega),Int.cast_natCast,mul_comm,Real.exp_nat_mul]
  rw [Real.exp_log (by norm_num : (0:ℝ)<2)]

lemma edgeWeight_rounding (G : Input) (e : Pair G.n) (he : 0< multiplicity G e) :
    (multiplicity G e:ℝ)/2≤ edgeWeight G e ∧ edgeWeight G e≤(multiplicity G e:ℝ) := by
  rw [edgeWeight_present G e he]
  have hlo := Nat.log2_self_le (show multiplicity G e≠0 by omega)
  have hhi : multiplicity G e<2^(Nat.log2 (multiplicity G e)+1) := Nat.lt_log2_self
  have hlo' : (2:ℝ)^Nat.log2 (multiplicity G e)≤(multiplicity G e:ℝ) := by exact_mod_cast hlo
  have hhi' : (multiplicity G e:ℝ)<(2:ℝ)^(Nat.log2 (multiplicity G e)+1) := by exact_mod_cast hhi
  rw [pow_succ] at hhi'
  constructor <;> linarith

lemma invalid_product_zero (G : Input) (M : (completeGraph G.n).Matching)
    (hM : ¬validMatching G M) : multProduct G M=0 := by
  classical
  unfold validMatching at hM
  push Not at hM
  obtain ⟨e,he,hzero⟩ := hM
  unfold multProduct
  exact prod_eq_zero he (by omega)

lemma goodWeight_le_product (G : Input) (M : (completeGraph G.n).Matching) :
    goodWeight G M≤(multProduct G M:ℝ) := by
  unfold goodWeight
  split_ifs with hM
  · unfold matchingWeight multProduct
    push_cast
    exact prod_le_prod (fun e _ => (Real.exp_pos _).le)
      (fun e he => (edgeWeight_rounding G e (hM e he)).2)
  · positivity

lemma goodWeight_ge_product (G : Input) (M : (completeGraph G.n).Matching) :
    (2:ℝ)⁻¹^M.val.card*(multProduct G M:ℝ)≤ goodWeight G M := by
  unfold goodWeight
  split_ifs with hM
  · calc
      _ = ∏ e∈M.val,((multiplicity G e:ℝ)/2) := by
        simp only [div_eq_mul_inv,prod_mul_distrib,prod_const,multProduct,Nat.cast_prod]
        ring
      _ ≤ _ := prod_le_prod (fun e _ => by positivity)
        (fun e he => (edgeWeight_rounding G e (hM e he)).1)
  · rw [invalid_product_zero G M hM,Nat.cast_zero,mul_zero]

lemma Zgood_bracket (G : Input) {r : ℕ} (hn : G.n=2*r) :
    (2:ℝ)⁻¹^r*(count G:ℝ)≤ Zgood G ∧ Zgood G≤(count G:ℝ) := by
  have hc (M : (completeGraph G.n).Matching) : M.val.card=r :=
    (completeGraph G.n).matching_card (by simpa) M
  have hncast : (count G:ℝ)=∑ M,(multProduct G M:ℝ) := by simp [count,multProduct]
  rw [hncast]
  constructor
  · rw [mul_sum]
    exact sum_le_sum fun M _ => by simpa only [hc M] using goodWeight_ge_product G M
  · exact sum_le_sum fun M _ => goodWeight_le_product G M

lemma positive_count_valid (G : Input) (hN : 0< count G) :
    ∃ M : (completeGraph G.n).Matching, validMatching G M := by
  have hsum : 0<∑ M,multProduct G M := hN
  obtain ⟨M,_hM,hprod⟩ := (sum_pos_iff_of_nonneg (fun M _ => Nat.zero_le (multProduct G M))).mp hsum
  refine ⟨M,?_⟩
  by_contra h
  rw [invalid_product_zero G M h] at hprod
  omega

lemma validWeight_ge_one (G : Input) (M : (completeGraph G.n).Matching)
    (hM : validMatching G M) : 1≤ goodWeight G M := by
  rw [goodWeight,ite_eq_left hM]
  apply one_le_prod
  intro e he
  rw [edgeWeight_present G e (hM e he)]
  exact one_le_pow₀ (by norm_num)

lemma Zgood_ge_one (G : Input) (hN : 0< count G) : 1≤ Zgood G := by
  obtain ⟨M,hM⟩ := positive_count_valid G hN
  exact (validWeight_ge_one G M hM).trans
    (single_le_sum (fun N _ => goodWeight_nonneg G N) (mem_univ M))

lemma beta_le_B (G : Input) (e : Pair G.n) : (beta G e:ℝ)≤(B G:ℝ) := by
  unfold beta
  split_ifs
  · simp only [Int.cast_neg,Int.cast_natCast]
    have : (0:ℝ)≤ B G := by positivity
    have : (0:ℝ)≤ L G := by positivity
    linarith
  · exact_mod_cast multiplicity_log_le_B G e

lemma matching_card_bound (n : ℕ) : Fintype.card (completeGraph n).Matching≤2^(q n) := by
  calc
    _ ≤ Fintype.card (Finset (Pair n)) :=
      Fintype.card_le_of_injective (fun M => M.val) Subtype.val_injective
    _ = _ := by rw [Fintype.card_finset]; rfl

lemma badWeight_bound (G : Input) {r : ℕ} (hn : G.n=2*r)
    (M : (completeGraph G.n).Matching) :
    badWeight G M≤ Real.exp (Real.log 2*((B G:ℝ)*r-L G)) := by
  classical
  unfold badWeight
  split_ifs with hM
  · exact (Real.exp_pos _).le
  · have hbad := hM
    unfold validMatching at hbad
    push Not at hbad
    obtain ⟨e,he,hzero⟩ := hbad
    have hz : multiplicity G e=0 := by omega
    have hbe : (beta G e:ℝ)=-(L G:ℝ) := by simp [beta,hz]
    have hc : M.val.card=r := (completeGraph G.n).matching_card (by simpa) M
    have hsingle := single_le_sum (s := M.val) (f := fun e => (B G:ℝ)-(beta G e:ℝ))
      (fun e _ => sub_nonneg.mpr (beta_le_B G e)) he
    rw [hbe,sum_sub_distrib,sum_const,hc,nsmul_eq_mul] at hsingle
    have hB : (0:ℝ)≤ B G := by positivity
    have hsum : (∑ e∈M.val,(beta G e:ℝ))≤(B G:ℝ)*r-L G := by nlinarith
    rw [matchingWeight_exp]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hsum log_two_pos.le

lemma Zbad_bound (G : Input) {r : ℕ} (hn : G.n=2*r) :
    Zbad G≤ Real.exp (Real.log 2*((q G.n:ℝ)+(B G:ℝ)*r-L G)) := by
  calc
    _ ≤ ∑ _M : (completeGraph G.n).Matching, Real.exp (Real.log 2*((B G:ℝ)*r-L G)) :=
      sum_le_sum fun M _ => badWeight_bound G hn M
    _ = (Fintype.card (completeGraph G.n).Matching:ℝ)*Real.exp (Real.log 2*((B G:ℝ)*r-L G)) := by simp
    _ ≤ (2:ℝ)^(q G.n)*Real.exp (Real.log 2*((B G:ℝ)*r-L G)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast matching_card_bound G.n
    _ = _ := by
      have he : (2:ℝ)^(q G.n)=Real.exp ((q G.n:ℝ)*Real.log 2) := by
        rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
      rw [he,←Real.exp_add]
      congr 1
      ring

lemma completion_parameter_bound (G : Input) {r : ℕ} (hn : G.n=2*r) :
    q G.n+B G*r+20*G.n≤ L G := by
  let t := G.n+B G+1
  have ht1 : 1≤ t := by dsimp [t]; omega
  have hnt : G.n≤ t := by dsimp [t]; omega
  have hBt : B G≤ t := by dsimp [t]; omega
  have hrt : r≤ t := by omega
  have hq : q G.n≤ t^2 := (q_le_square (n := G.n)).trans (Nat.pow_le_pow_left hnt 2)
  have hBr : B G*r≤ t^2 := by simpa only [pow_two] using Nat.mul_le_mul hBt hrt
  have ht13 : t≤ t^3 := Nat.le_self_pow (by omega) t
  have ht23 : t^2≤ t^3 := by
    calc
      t^2=t^2*1 := by ring
      _ ≤ t^2*t := Nat.mul_le_mul_left _ ht1
      _ = _ := by ring
  change _≤100*t^3
  omega

lemma Zbad_small (G : Input) (heven : Even G.n) :
    Zbad G≤ Real.exp (Real.log 2*(-20*(G.n:ℝ))) := by
  obtain ⟨r,hr⟩ := heven
  have hn : G.n=2*r := by omega
  have hh := Zbad_bound G hn
  have hdom : (q G.n:ℝ)+(B G:ℝ)*r+20*(G.n:ℝ)≤ L G := by
    exact_mod_cast completion_parameter_bound G hn
  apply hh.trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ log_two_pos.le
  linarith

theorem completion_bracket (G : Input) (hn : 4≤ G.n) (heven : Even G.n) :
    (count G=0 → logZ G≤-20*(G.n:ℝ)) ∧
    (0< count G → 1≤ Z G ∧ (2:ℝ)⁻¹^(G.n/2)*(count G:ℝ)≤ Z G ∧ Z G≤2*(count G:ℝ)) := by
  have hbad := Zbad_small G heven
  have hNsplit := Z_decompose G
  have hsmall : Zbad G≤1 := by
    apply hbad.trans (Real.exp_le_one_iff.mpr _)
    exact mul_nonpos_of_nonneg_of_nonpos log_two_pos.le (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hn2 : G.n=2*(G.n/2) := by
    obtain ⟨r,hr⟩ := heven
    omega
  have hgood := Zgood_bracket G hn2
  constructor
  · intro hN
    have hg : Zgood G=0 := le_antisymm (by simpa only [hN,Nat.cast_zero] using hgood.2) (Zgood_nonneg G)
    have hz : Z G≤ Real.exp (Real.log 2*(-20*(G.n:ℝ))) := by linarith
    have hl := Real.log_le_log (Z_pos G hn heven) hz
    rw [Real.log_exp] at hl
    unfold logZ
    apply (div_le_iff₀ log_two_pos).2
    nlinarith
  · intro hN
    have hng : 1≤ Zgood G := Zgood_ge_one G hN
    have hN' : (1:ℝ)≤ count G := by exact_mod_cast hN
    have hbn := Zbad_nonneg G
    constructor
    · linarith
    constructor
    · linarith [hgood.1]
    · linarith [hgood.2]

end
end BinaryMatching.Algorithm
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

lemma zero_test (G : Input) (hn : 4 ≤ G.n) (heven : Even G.n) :
    R G < -10*(G.n:ℤ) ↔ count G = 0 := by
  have hp := R_partition_bracket G hn heven
  have hc := completion_bracket G hn heven
  have hn' : (4:ℝ) ≤ G.n := by exact_mod_cast hn
  constructor
  · intro hr
    by_contra hN
    have hNpos : 0 < count G := Nat.pos_of_ne_zero hN
    have hz : 0 ≤ logZ G := by
      unfold logZ
      exact div_nonneg (Real.log_nonneg (hc.2 hNpos).1) log_two_pos.le
    have hr' : (R G:ℝ) < -10*(G.n:ℝ) := by exact_mod_cast hr
    linarith [hp.2]
  · intro hN
    have hz := hc.1 hN
    have hr' : (R G:ℝ) < -10*(G.n:ℝ) := by linarith [hp.1]
    exact_mod_cast hr'

lemma log_count_bracket (G : Input) (hn : 4 ≤ G.n) (heven : Even G.n)
    (hN : 0 < count G) :
    (R G:ℝ)-5*(G.n:ℝ) ≤ Real.log (count G)/Real.log 2 ∧
      Real.log (count G)/Real.log 2 ≤ (R G:ℝ)+4*(G.n:ℝ) := by
  have hp := R_partition_bracket G hn heven
  obtain ⟨_hone,hlo,hhi⟩ := (completion_bracket G hn heven).2 hN
  have hN' : (0:ℝ) < count G := by exact_mod_cast hN
  have hn' : (4:ℝ) ≤ G.n := by exact_mod_cast hn
  have hlo' := Real.log_le_log (show (0:ℝ) < 2⁻¹^(G.n/2)*(count G:ℝ) by positivity) hlo
  have hhi' := Real.log_le_log (Z_pos G hn heven) hhi
  rw [Real.log_mul (by positivity) hN'.ne',Real.log_pow,Real.log_inv] at hlo'
  rw [Real.log_mul (by norm_num) hN'.ne'] at hhi'
  have hdiv : ((G.n/2:ℕ):ℝ) ≤ (G.n:ℝ) := by exact_mod_cast Nat.div_le_self G.n 2
  dsimp only [logZ] at hp
  constructor
  · apply (le_div_iff₀ log_two_pos).2
    have hpart := (le_div_iff₀ log_two_pos).1 hp.1
    nlinarith [log_two_pos]
  · apply (div_le_iff₀ log_two_pos).2
    have hpart := (div_le_iff₀ log_two_pos).1 hp.2
    nlinarith [mul_le_mul_of_nonneg_right hdiv log_two_pos.le]

theorem estimate_correct (G : Input) (hn : 4 ≤ G.n) (heven : Even G.n) :
    estimate G ≤ count G ∧ count G ≤ 2^(9*G.n)*estimate G ∧
      (estimate G=0 ↔ count G=0) := by
  by_cases hN : count G=0
  · have hr : R G < -(10*(G.n:ℤ)) := by simpa only [neg_mul] using (zero_test G hn heven).2 hN
    simp [estimate,hr,hN]
  · have hNpos : 0 < count G := Nat.pos_of_ne_zero hN
    have hr : ¬R G < -(10*(G.n:ℤ)) := by simpa only [←neg_mul,zero_test G hn heven] using hN
    have he : estimate G=2^(R G-5*(G.n:ℤ)).toNat := by simp [estimate,hr]
    let rho := (R G-5*(G.n:ℤ)).toNat
    have he' : estimate G=2^rho := he
    have hrhol : (R G:ℝ)-5*(G.n:ℝ) ≤ (rho:ℝ) := by
      have hi : R G-5*(G.n:ℤ) ≤ (rho:ℤ) := Int.self_le_toNat _
      exact_mod_cast hi
    have hNc : (0:ℝ) < count G := by exact_mod_cast hNpos
    have hN1 : (1:ℝ) ≤ count G := by exact_mod_cast hNpos
    have hlog0 : 0 ≤ Real.log (count G)/Real.log 2 :=
      div_nonneg (Real.log_nonneg hN1) log_two_pos.le
    have hbracket := log_count_bracket G hn heven hNpos
    have hrhou : (rho:ℝ) ≤ Real.log (count G)/Real.log 2 := by
      by_cases hnon : 0 ≤ R G-5*(G.n:ℤ)
      · have hh : (rho:ℤ)=R G-5*(G.n:ℤ) := Int.toNat_of_nonneg hnon
        have hh' : (rho:ℝ)=(R G:ℝ)-5*(G.n:ℝ) := by exact_mod_cast hh
        rw [hh']; exact hbracket.1
      · have hz : rho=0 := Int.toNat_of_nonpos (by omega)
        simpa only [hz,Nat.cast_zero] using hlog0
    have hlow : (2:ℝ)^rho ≤ (count G:ℝ) := by
      apply (Real.log_le_log_iff (by positivity) hNc).1
      rw [Real.log_pow]
      exact (le_div_iff₀ log_two_pos).1 hrhou
    have hupp : (count G:ℝ) ≤ (2:ℝ)^(9*G.n)*(2:ℝ)^rho := by
      apply (Real.log_le_log_iff hNc (by positivity)).1
      rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]
      have hh : Real.log (count G)/Real.log 2 ≤ (9*G.n:ℕ)+(rho:ℝ) := by
        push_cast; linarith [hbracket.2]
      have hh' := (div_le_iff₀ log_two_pos).1 hh
      push_cast at hh' ⊢
      nlinarith
    have hlow' : 2^rho ≤ count G := by exact_mod_cast hlow
    have hupp' : count G ≤ 2^(9*G.n)*2^rho := by exact_mod_cast hupp
    rw [he']
    refine ⟨hlow',hupp',?_⟩
    simp [hN]

end
end BinaryMatching.Algorithm
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

lemma count_zero_vertices (G : Input) (hn : G.n=0) : count G=1 := by
  classical
  let M : (completeGraph G.n).Matching := ⟨∅,fun v => by have := v.isLt; omega⟩
  have hM (N : (completeGraph G.n).Matching) : N=M := by
    apply Subtype.ext
    apply Finset.eq_empty_of_forall_notMem
    intro e _
    have := e.val.1.isLt
    omega
  unfold count
  rw [sum_eq_single M]
  · simp [M]
  · intro N _ hne
    exact (hne (hM N)).elim
  · simp

lemma count_odd_vertices (G : Input) (hn : Odd G.n) : count G=0 := by
  classical
  have hempty : IsEmpty (completeGraph G.n).Matching := ⟨fun M => by
    have hh := (completeGraph G.n).matching_card_twice M
    simp only [Fintype.card_fin] at hh
    obtain ⟨r,hr⟩ := hn
    omega⟩
  simp [count]

lemma count_two_vertices (G : Input) (hn : G.n=2) : count G=rawMultiplicity G 0 1 := by
  classical
  let e : Pair G.n := ⟨(⟨0,by omega⟩,⟨1,by omega⟩),by simp⟩
  have heq (f : Pair G.n) : f=e := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · have hh := f.property; have h1 := f.val.1.isLt; have h2 := f.val.2.isLt
      dsimp [e] at hh ⊢; omega
    · have hh := f.property; have h1 := f.val.1.isLt; have h2 := f.val.2.isLt
      dsimp [e] at hh ⊢; omega
  have heinc (v : Fin G.n) : (completeGraph G.n).Incident v e := by
    have hv := v.isLt
    change e.val.1=v ∨ e.val.2=v
    by_cases hz : v.val=0
    · left; apply Fin.ext; exact hz.symm
    · right; apply Fin.ext; dsimp [e]; omega
  let M : (completeGraph G.n).Matching := ⟨{e},fun v => ⟨e,⟨by simp,heinc v⟩,
    fun _ h => by simpa only [mem_singleton] using h.1⟩⟩
  have hM (N : (completeGraph G.n).Matching) : N=M := by
    apply Subtype.ext
    apply Finset.ext
    intro f
    have hfn := heq f
    obtain ⟨g,hg,_⟩ := N.property e.val.1
    have hgn := heq g
    have hmem : e∈N.val := hgn ▸ hg.1
    simp only [M,mem_singleton,hfn]
    exact iff_true_intro hmem
  unfold count
  rw [sum_eq_single M]
  · simp only [M,prod_singleton]
    unfold multiplicity rawMultiplicity
    dsimp [e]
    cases G.records.find? (fun r => r.left=0 && r.right=1) <;> rfl
  · intro N _ hne
    exact (hne (hM N)).elim
  · simp

lemma present_endpoints_covered (G : Input) (e : Pair G.n) (he : 0 < multiplicity G e) :
    e.val.1.val∈covered G ∧ e.val.2.val∈covered G := by
  unfold multiplicity at he
  cases hf : G.records.find? (fun r => r.left=e.val.1.val && r.right=e.val.2.val) with
  | none => simp only [hf] at he; omega
  | some r =>
    have hr := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hp
    simp only [hf] at he
    have hr' : r∈G.records.filter (fun r => 0 < r.multiplicity) := by simp [hr,he]
    constructor
    · simp only [covered,List.mem_toFinset,List.mem_flatMap]
      refine ⟨r,hr',?_⟩
      simp [hp.1]
    · simp only [covered,List.mem_toFinset,List.mem_flatMap]
      refine ⟨r,hr',?_⟩
      simp [hp.2]

lemma positive_count_covered (G : Input) (hN : 0 < count G) : G.n ≤ (covered G).card := by
  obtain ⟨M,hM⟩ := positive_count_valid G hN
  have hsub : range G.n ⊆ covered G := by
    intro v hv
    let w : Fin G.n := ⟨v,mem_range.mp hv⟩
    obtain ⟨e,⟨he,hinc⟩,_⟩ := M.property w
    have hep := present_endpoints_covered G e (hM e he)
    rcases hinc with h|h
    · have hh : e.val.1.val=v := congrArg Fin.val h
      simpa only [hh] using hep.1
    · have hh : e.val.2.val=v := congrArg Fin.val h
      simpa only [hh] using hep.2
  simpa only [card_range] using card_le_card hsub

lemma count_zero_of_uncovered (G : Input) (hu : (covered G).card < G.n) : count G=0 := by
  by_contra hN
  have := positive_count_covered G (Nat.pos_of_ne_zero hN)
  omega

theorem approximate_correct (G : Input) :
    approximate G ≤ count G ∧ count G ≤ 2^(9*G.n)*approximate G ∧
      (approximate G=0 ↔ count G=0) := by
  unfold approximate
  split_ifs with hn0 hodd hn2 hcover
  · rw [count_zero_vertices G hn0,hn0]
    norm_num
  · rw [count_odd_vertices G hodd]
    simp
  · rw [count_two_vertices G hn2]
    refine ⟨le_rfl,?_,Iff.rfl⟩
    exact Nat.le_mul_of_pos_left _ (by positivity)
  · rw [count_zero_of_uncovered G hcover]
    simp
  · have heven : Even G.n := Nat.not_odd_iff_even.mp hodd
    have hn : 4 ≤ G.n := by
      obtain ⟨r,hr⟩ := heven
      omega
    exact estimate_correct G hn heven

end
end BinaryMatching.Algorithm
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset

def inputLength (G : Input) : ℕ := (encodeInput G).length

lemma encodeNat_length (n : ℕ) : (encodeNat n).length=2*n.bits.length+1 := by
  simp [encodeNat]; omega

lemma encodeRecord_length (r : Record) :
    (encodeRecord r).length=2*(r.left.bits.length+r.right.bits.length+r.multiplicity.bits.length)+3 := by
  simp only [encodeRecord,List.length_append,encodeNat_length]
  omega

lemma records_length_le_input (G : Input) : G.records.length≤ inputLength G := by
  have hh (rs : List Record) : rs.length≤(rs.flatMap encodeRecord).length := by
    induction rs with
    | nil => simp
    | cons r rs ih =>
      simp only [List.length_cons,List.flatMap_cons,List.length_append,encodeRecord_length]
      omega
  have := hh G.records
  simp only [inputLength,encodeInput,List.length_append]
  omega

lemma record_bits_le_input (G : Input) (r : Record) (hr : r∈G.records) :
    r.multiplicity.bits.length≤ inputLength G := by
  have hh : (encodeRecord r).length≤(G.records.flatMap encodeRecord).length := by
    rw [List.length_flatMap]
    exact List.le_sum_of_mem (List.mem_map.mpr ⟨r,hr,rfl⟩)
  rw [encodeRecord_length] at hh
  unfold inputLength encodeInput
  simp only [List.length_append]
  omega

lemma log2_le_bits (m : ℕ) : Nat.log2 m≤ m.bits.length := by
  by_cases hm : m=0
  · subst m; simp
  · rw [Nat.size_eq_bits_len]
    exact (Nat.lt_size.mpr (Nat.log2_self_le hm)).le

lemma B_le_input (G : Input) : B G≤ inputLength G := by
  apply foldl_max_le _ _ _ (Nat.zero_le _)
  intro b hb
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hb
  exact (log2_le_bits r.multiplicity).trans (record_bits_le_input G r hr)

lemma covered_card_le_records (G : Input) : (covered G).card≤2*G.records.length := by
  have hh := List.toFinset_card_le
    ((G.records.filter (fun e => 0< e.multiplicity)).flatMap (fun e => [e.left,e.right]))
  have hlen : ((G.records.filter (fun e => 0< e.multiplicity)).flatMap (fun e => [e.left,e.right])).length=
      2*(G.records.filter (fun e => 0< e.multiplicity)).length := by
    rw [List.length_flatMap]
    simp
    omega
  rw [hlen] at hh
  exact hh.trans (Nat.mul_le_mul_left 2 (List.length_filter_le _ _))

lemma positive_count_order_bound (G : Input) (hN : 0< count G) : G.n≤2*inputLength G := by
  exact (positive_count_covered G hN).trans
    ((covered_card_le_records G).trans (Nat.mul_le_mul_left _ (records_length_le_input G)))

lemma multiplicity_pow_bound (G : Input) (e : Pair G.n) : multiplicity G e≤2^(B G+1) := by
  apply (Nat.lt_log2_self (n := multiplicity G e)).le.trans
  exact Nat.pow_le_pow_right (by norm_num) (by have := multiplicity_log_le_B G e; omega)

lemma count_pow_bound (G : Input) : count G≤2^((B G+2)*q G.n) := by
  have hM (M : (completeGraph G.n).Matching) : multProduct G M≤2^((B G+1)*q G.n) := by
    calc
      _ ≤ ∏ _e∈M.val,2^(B G+1) := prod_le_prod' (fun e _ => multiplicity_pow_bound G e)
      _ = (2^(B G+1))^M.val.card := by simp
      _ ≤ (2^(B G+1))^(q G.n) :=
        Nat.pow_le_pow_right (by positivity) (card_le_univ M.val)
      _ = _ := by rw [pow_mul]
  calc
    _ ≤ ∑ _M : (completeGraph G.n).Matching,2^((B G+1)*q G.n) := sum_le_sum fun M _ => hM M
    _ = Fintype.card (completeGraph G.n).Matching*2^((B G+1)*q G.n) := by simp
    _ ≤ 2^(q G.n)*2^((B G+1)*q G.n) := Nat.mul_le_mul_right _ (matching_card_bound G.n)
    _ = _ := by rw [←pow_add]; congr 1; ring

lemma approximate_bits_bound (G : Input) :
    (approximate G).bits.length≤4*(inputLength G)^2*(inputLength G+2)+1 := by
  by_cases hN : count G=0
  · have ha := (approximate_correct G).2.2.mpr hN
    simp [ha]
  · have hNpos : 0< count G := Nat.pos_of_ne_zero hN
    have hn := positive_count_order_bound G hNpos
    have hb := B_le_input G
    have hq : q G.n≤4*(inputLength G)^2 := by
      apply (q_le_square (n := G.n)).trans
      calc
        G.n^2≤(2*inputLength G)^2 := Nat.pow_le_pow_left hn 2
        _ = _ := by ring
    have hExp : (B G+2)*q G.n≤4*(inputLength G)^2*(inputLength G+2) := by
      have := Nat.mul_le_mul (Nat.add_le_add_right hb 2) hq
      nlinarith
    rw [Nat.size_eq_bits_len]
    apply (Nat.size_le_size (approximate_correct G).1).trans
    apply (Nat.size_le_size (count_pow_bound G)).trans
    rw [Nat.size_pow]
    omega

theorem approximate_polynomial_output :
    ∃ P : Polynomial ℕ,∀ G,(approximate G).bits.length≤ P.eval (encodeInput G).length := by
  refine ⟨Polynomial.C 4*Polynomial.X^2*(Polynomial.X+Polynomial.C 2)+Polynomial.C 1,?_⟩
  intro G
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,
    Polynomial.eval_C,inputLength] using approximate_bits_bound G

end
end BinaryMatching.Algorithm
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Algorithm
open Finset

def tau (G : Input) : ℕ := G.n+B G+1

def Q (G : Input) : ℕ := D₀ G*2^(K G.n)

lemma tau_pos (G : Input) : 0<tau G := by unfold tau; omega
lemma order_le_tau (G : Input) : G.n≤tau G := by unfold tau; omega
lemma B_le_tau (G : Input) : B G≤tau G := by unfold tau; omega

lemma K_le_q (n : ℕ) : K n≤q n :=
  Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_two_pow_self))

lemma q_le_tau_sq (G : Input) : q G.n≤(tau G)^2 :=
  q_le_square.trans (Nat.pow_le_pow_left (order_le_tau G) 2)

lemma tau_pow_mono (G : Input) {i j : ℕ} (h : i≤j) : (tau G)^i≤(tau G)^j :=
  Nat.pow_le_pow_right (tau_pos G) h

lemma K_L_bound (G : Input) : K G.n+L G≤101*(tau G)^3 := by
  have hk : K G.n≤(tau G)^3 :=
    (K_le_q G.n).trans ((q_le_tau_sq G).trans (tau_pow_mono G (by omega)))
  change K G.n+100*(tau G)^3≤_
  omega

lemma A₀_bound (G : Input) : 2+A₀ G.n≤12*(tau G)^2 := by
  have hn := Nat.pow_le_pow_left (order_le_tau G) 2
  have ht : 1≤(tau G)^2 := one_le_pow₀ (tau_pos G)
  unfold A₀
  omega

lemma M₀_bound (G : Input) : M₀ G≤1212*(tau G)^7 := by
  calc
    _ ≤ (tau G)^2*(101*(tau G)^3)*(12*(tau G)^2) :=
      Nat.mul_le_mul (Nat.mul_le_mul (q_le_tau_sq G) (K_L_bound G)) (A₀_bound G)
    _ = _ := by ring

lemma K_L_M_bound (G : Input) : K G.n+L G+M₀ G≤1313*(tau G)^7 := by
  have hk := (K_L_bound G).trans (Nat.mul_le_mul_left 101 (tau_pow_mono G (by omega : 3≤7)))
  have hm := M₀_bound G
  omega

lemma D₀_bound (G : Input) : D₀ G≤1313^2*(tau G)^16 := by
  calc
    _ ≤ (tau G)^2*(1313*(tau G)^7)^2 :=
      Nat.mul_le_mul (q_le_tau_sq G) (Nat.pow_le_pow_left (K_L_M_bound G) 2)
    _ = _ := by ring

lemma iterations_bound (G : Input) : q G.n*D₀ G≤1313^2*(tau G)^18 := by
  calc
    _ ≤ (tau G)^2*(1313^2*(tau G)^16) := Nat.mul_le_mul (q_le_tau_sq G) (D₀_bound G)
    _ = _ := by ring

lemma pow_K_bound (n : ℕ) (hn : 2≤n) : 2^(K n)≤2*q n := by
  have hq := q_pos hn
  by_cases he : q n=1
  · simp [K,he]
  · have hq' : 1<q n := by omega
    have hk : 0<K n := by
      unfold K
      rw [Nat.pos_iff_ne_zero]
      intro h
      have hh := Nat.le_pow_clog (by omega : 1<2) (q n)
      rw [h] at hh
      simp at hh
      omega
    have hh := Nat.pow_pred_clog_lt_self (by omega : 1<2) hq'
    change 2^(K n-1)<q n at hh
    calc
      _ = 2^(K n-1)*2 := by rw [←pow_succ]; congr 1; omega
      _ ≤ q n*2 := Nat.mul_le_mul_right _ hh.le
      _ = _ := by omega

lemma Q_bound (G : Input) (hn : 2≤G.n) : Q G≤2*1313^2*(tau G)^18 := by
  calc
    _ ≤ (1313^2*(tau G)^16)*(2*(tau G)^2) :=
      Nat.mul_le_mul (D₀_bound G) ((pow_K_bound G.n hn).trans (Nat.mul_le_mul_left 2 (q_le_tau_sq G)))
    _ = _ := by ring

lemma tau_input_bound (G : Input) (hguard : G.n≤(covered G).card) :
    tau G≤3*inputLength G+1 := by
  have hn := hguard.trans ((covered_card_le_records G).trans
    (Nat.mul_le_mul_left 2 (records_length_le_input G)))
  have hb := B_le_input G
  unfold tau
  omega

end BinaryMatching.Algorithm
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Algorithm
open Finset
local instance : Preorder ℤ := Int.instLinearOrder.toPreorder

private lemma argmin_map {α β γ : Type} [LinearOrder γ] (l : List α) (f : α → β)
    (g : β → γ) : (l.map f).argmin g=(l.argmin (g ∘ f)).map f := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.map_append,List.map_singleton,List.argmin_concat,List.argmin_concat,ih]
    cases h : l.argmin (g ∘ f) with
    | none => rfl
    | some b => simp only [Option.map_some,Function.comp_apply]; split_ifs <;> rfl

private lemma argmin_congr_on {α β γ : Type} [LinearOrder β] [LinearOrder γ]
    (l : List α) (f : α → β) (g : α → γ)
    (h : ∀ a∈l, ∀ b∈l, f a<f b ↔ g a<g b) : l.argmin f=l.argmin g := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    have hl (b : α) (hb : b∈l) : b∈l++[a] := List.mem_append_left _ hb
    have ha : a∈l++[a] := by simp
    rw [List.argmin_concat,List.argmin_concat,ih (fun b hb c hc => h b (hl b hb) c (hl c hc))]
    cases hg : l.argmin g with
    | none => rfl
    | some b =>
      simp only
      simp only [h a ha b (hl b (List.argmin_mem hg))]

private lemma argmax_congr_on {α β γ : Type} [LinearOrder β] [LinearOrder γ]
    (l : List α) (f : α → β) (g : α → γ)
    (h : ∀ a∈l, ∀ b∈l, f a<f b ↔ g a<g b) : l.argmax f=l.argmax g :=
  @argmin_congr_on α βᵒᵈ γᵒᵈ _ _ l f g (fun a ha b hb => h b hb a ha)

def indexedPiece (k j : ℕ) : Piece :=
  if j<k then ⟨(j:ℤ)-1,(2:ℚ)⁻¹^j⟩ else ⟨k,0⟩

def pieceNumerator (k D : ℕ) (a : ℤ) (j : ℕ) : ℤ :=
  (indexedPiece k j).slope*a*2^k + if j<k then (D:ℤ)*2^(k-j) else 0

lemma pieces_indexed (k : ℕ) : pieces k=(List.range (k+1)).map (indexedPiece k) := by
  rw [List.range_succ,List.map_append,List.map_singleton]
  unfold pieces
  congr 1
  · apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    simp only [indexedPiece,ite_eq_left hj]
  · simp [indexedPiece]

lemma pieceNumerator_cast (k D j : ℕ) (hD : 0<D) (hj : j≤k) (a : ℤ) :
    (pieceNumerator k D a j:ℚ)=(D:ℚ)*2^k*(indexedPiece k j).eval (a/(D:ℚ)) := by
  have hD' : (D:ℚ)≠0 := by exact_mod_cast hD.ne'
  have hp : (2:ℚ)^k=(2:ℚ)^j*2^(k-j) := by rw [←pow_add,Nat.add_sub_of_le hj]
  unfold pieceNumerator Piece.eval indexedPiece
  split_ifs with hjk
  · push_cast
    rw [inv_pow]
    field_simp
    nlinarith [hp]
  · push_cast
    field_simp
    ring

def selectedIndex (k D : ℕ) (a : ℤ) : ℕ :=
  ((List.range (k+1)).argmin (pieceNumerator k D a)).getD k

lemma selectedIndex_mem (k D : ℕ) (a : ℤ) :
    selectedIndex k D a∈(List.range (k+1)).argmin (pieceNumerator k D a) := by
  unfold selectedIndex
  cases h : (List.range (k+1)).argmin (pieceNumerator k D a) with
  | none => have hh := List.argmin_eq_none.mp h; simp at hh
  | some j => rfl

lemma selectedIndex_le (k D : ℕ) (a : ℤ) : selectedIndex k D a≤k := by
  have h := List.argmin_mem (selectedIndex_mem k D a)
  simpa only [List.mem_range,Nat.lt_succ_iff] using h

lemma selectedPiece_index (k D : ℕ) (hD : 0<D) (a : ℤ) :
    selectedPiece k (a/(D:ℚ))=indexedPiece k (selectedIndex k D a) := by
  have hQ : (0:ℚ)<(D:ℚ)*2^k := mul_pos (by exact_mod_cast hD) (by positivity)
  have hc := argmin_congr_on (List.range (k+1))
    (fun j => (indexedPiece k j).eval (a/(D:ℚ))) (pieceNumerator k D a) (by
      intro i hi j hj
      have hi' : i≤k := by simpa only [List.mem_range,Nat.lt_succ_iff] using hi
      have hj' : j≤k := by simpa only [List.mem_range,Nat.lt_succ_iff] using hj
      rw [←mul_lt_mul_iff_right₀ hQ]
      rw [←pieceNumerator_cast k D i hD hi' a,←pieceNumerator_cast k D j hD hj' a]
      exact_mod_cast Iff.rfl)
  unfold selectedPiece selectedIndex
  rw [pieces_indexed,argmin_map]
  change (((List.range (k+1)).argmin (fun j => (indexedPiece k j).eval (a/(D:ℚ)))).map
    (indexedPiece k)).getD _=_
  rw [hc]
  cases h : (List.range (k+1)).argmin (pieceNumerator k D a) with
  | none => simp [indexedPiece]
  | some j => rfl

def scaledPsi (k D : ℕ) (a : ℤ) : ℤ := pieceNumerator k D a (selectedIndex k D a)
def scaledSlope (k D : ℕ) (a : ℤ) : ℤ := (indexedPiece k (selectedIndex k D a)).slope

lemma scaledPsi_cast (k D : ℕ) (hD : 0<D) (a : ℤ) :
    (scaledPsi k D a:ℚ)=(D:ℚ)*2^k*psi k (a/(D:ℚ)) := by
  unfold scaledPsi psi
  rw [selectedPiece_index k D hD]
  exact pieceNumerator_cast k D _ hD (selectedIndex_le k D a) a

lemma scaledSlope_eq (k D : ℕ) (hD : 0<D) (a : ℤ) :
    scaledSlope k D a=slope k (a/(D:ℚ)) := by
  unfold scaledSlope slope
  rw [selectedPiece_index k D hD]

variable {n : ℕ}

def rowNumerator (D : ℕ) (a : Table n ℤ) (r : Affine n) : ℤ :=
  (∑ e,r.coeff e*entry a e)+r.constant*D

lemma rowNumerator_cast (D : ℕ) (hD : 0<D) (a : Table n ℤ) (r : Affine n) :
    (rowNumerator D a r:ℚ)=(D:ℚ)*r.eval (coordinates D a) := by
  have hD' : (D:ℚ)≠0 := by exact_mod_cast hD.ne'
  simp only [rowNumerator,Affine.eval,coordinates,Int.cast_add,Int.cast_sum,Int.cast_mul,
    Int.cast_natCast,mul_add,mul_sum]
  congr 1
  · apply sum_congr rfl
    intro e he
    field_simp
  · ring

def integralRows (a : Table n ℤ) : List (Affine n) :=
  zeroRow :: ((List.finRange n).flatMap (fun v => [degreeRow v true,degreeRow v false])) ++
    [cutRow (DenseOracle.oddCut (DenseOracle.make (capacities a)) univ)]

lemma integralRows_eq (a : Table n ℤ) : integralRows a=activeRows a := by
  simp only [integralRows,DenseOracle.oddCut_eq,DenseOracle.view_make,activeRows]

def integralRow (D : ℕ) (a : Table n ℤ) : Affine n :=
  ((integralRows a).argmax (rowNumerator D a)).getD zeroRow

lemma integralRow_eq (D : ℕ) (hD : 0<D) (a : Table n ℤ) :
    integralRow D a=activeRow D a := by
  unfold integralRow activeRow
  rw [integralRows_eq]
  congr 1
  apply argmax_congr_on
  intro r hr s hs
  rw [←Int.cast_lt (R := ℚ),rowNumerator_cast D hD,rowNumerator_cast D hD]
  exact mul_lt_mul_iff_right₀ (by exact_mod_cast hD)

def integralValue (G : Input) (a : Table G.n ℤ) (r : Affine G.n) : ℤ :=
  (∑ e, (scaledPsi (K G.n) (D₀ G) (entry a e)+beta G e*entry a e*2^(K G.n))) -
    (M₀ G:ℤ)*rowNumerator (D₀ G) a r*2^(K G.n)

def integralGradient (G : Input) (a : Table G.n ℤ) (r : Affine G.n) (e : Pair G.n) : ℤ :=
  scaledSlope (K G.n) (D₀ G) (entry a e)+beta G e-(M₀ G:ℤ)*r.coeff e

def integralUpdate (G : Input) (a : Table G.n ℤ) (r : Affine G.n) : Table G.n ℤ :=
  toTable (fun e => min (D₀ G:ℤ) (max 0 (entry a e+integralGradient G a r e)))

lemma integralGradient_eq (G : Input) (hn : 2≤G.n) (a : Table G.n ℤ) (r : Affine G.n) :
    integralGradient G a r=gradient G a r := by
  funext e
  simp only [integralGradient,gradient,coordinates,scaledSlope_eq _ _ (D₀_pos G hn)]

lemma integralUpdate_eq (G : Input) (hn : 2≤G.n) (a : Table G.n ℤ) (r : Affine G.n) :
    integralUpdate G a r=update G a r := by
  simp only [integralUpdate,update,integralGradient_eq G hn]

lemma integralValue_cast (G : Input) (hn : 2≤G.n) (a : Table G.n ℤ) (r : Affine G.n) :
    (integralValue G a r:ℚ)=(Q G:ℚ)*trialValue G a r := by
  have hD : (D₀ G:ℚ)≠0 := by exact_mod_cast (D₀_pos G hn).ne'
  simp only [integralValue,Int.cast_sub,Int.cast_sum,Int.cast_add,Int.cast_mul,Int.cast_pow,
    Int.cast_ofNat,Int.cast_natCast,scaledPsi_cast _ _ (D₀_pos G hn),
    rowNumerator_cast _ (D₀_pos G hn),trialValue,Q,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
    mul_sub,mul_sum,mul_add,coordinates]
  congr 1
  · apply sum_congr rfl
    intro e he
    field_simp
  · ring

structure IntegralState (n : ℕ) where
  numerators : Table n ℤ
  best : Option ℤ

def integralStep (G : Input) (s : IntegralState G.n) : IntegralState G.n :=
  let r := integralRow (D₀ G) s.numerators
  let value := integralValue G s.numerators r
  ⟨integralUpdate G s.numerators r,some (s.best.elim value (max value))⟩

def integralInitial (n : ℕ) : IntegralState n := ⟨tabulate (fun _ _ => 0),none⟩

def integralIterate (G : Input) : ℕ → IntegralState G.n
  | 0 => integralInitial G.n
  | t+1 => integralStep G (integralIterate G t)

end BinaryMatching.Algorithm
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Algorithm
local instance : Preorder ℤ := Int.instLinearOrder.toPreorder

lemma Q_pos (G : Input) (hn : 2≤G.n) : 0<Q G :=
  Nat.mul_pos (D₀_pos G hn) (by positivity)

def decodeIntegral (G : Input) (s : IntegralState G.n) : State G.n :=
  ⟨s.numerators,s.best.map (fun v : ℤ => (v:ℚ)/(Q G:ℚ))⟩

lemma integralValue_div (G : Input) (hn : 2≤G.n) (a : Table G.n ℤ) (r : Affine G.n) :
    (integralValue G a r:ℚ)/(Q G:ℚ)=trialValue G a r := by
  rw [integralValue_cast G hn]
  have hQ : (Q G:ℚ)≠0 := by exact_mod_cast (Q_pos G hn).ne'
  exact mul_div_cancel_left₀ _ hQ

lemma decodeIntegral_step (G : Input) (hn : 2≤G.n) (s : IntegralState G.n) :
    decodeIntegral G (integralStep G s)=step G (decodeIntegral G s) := by
  obtain ⟨a,b⟩ := s
  dsimp only [decodeIntegral,integralStep,step]
  rw [integralRow_eq _ (D₀_pos G hn),integralUpdate_eq G hn]
  congr 1
  cases b with
  | none => simp only [Option.map_none,Option.elim_none,Option.map_some,integralValue_div G hn]
  | some v =>
    simp only [Option.map_some,Option.elim_some,Int.cast_max]
    rw [←max_div_div_right (by positivity : (0:ℚ)≤Q G),integralValue_div G hn]

lemma decodeIntegral_iterate (G : Input) (hn : 2≤G.n) (j : ℕ) :
    decodeIntegral G (integralIterate G j)=iterate G j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [integralIterate,decodeIntegral_step G hn,ih,iterate]

lemma integralIterate_table (G : Input) (hn : 2≤G.n) (j : ℕ) :
    (integralIterate G j).numerators=(iterate G j).numerators :=
  congrArg State.numerators (decodeIntegral_iterate G hn j)

lemma integralIterate_best (G : Input) (hn : 2≤G.n) (j : ℕ) :
    ((integralIterate G j).best.map (fun v : ℤ => (v:ℚ)/(Q G:ℚ)))=(iterate G j).best :=
  congrArg State.best (decodeIntegral_iterate G hn j)

def integralR (G : Input) : ℤ := ((integralIterate G (q G.n*D₀ G)).best).getD 0/(Q G:ℤ)

lemma integralR_eq (G : Input) (hn : 2≤G.n) : integralR G=R G := by
  unfold integralR R
  rw [←integralIterate_best G hn]
  cases h : (integralIterate G (q G.n*D₀ G)).best with
  | none => simp
  | some v => simp only [Option.getD_some,Option.map_some,Int.floor_div_natCast,Int.floor_intCast]

def integralEstimate (G : Input) : ℕ :=
  let r := integralR G
  if r < -10*(G.n:ℤ) then 0 else 2^(r-5*(G.n:ℤ)).toNat

lemma integralEstimate_eq (G : Input) (hn : 2≤G.n) : integralEstimate G=estimate G := by
  simp only [integralEstimate,estimate,integralR_eq G hn]

def integralApproximate (G : Input) : ℕ :=
  if G.n=0 then 1 else
  if Odd G.n then 0 else
  if G.n=2 then rawMultiplicity G 0 1 else
  if (covered G).card<G.n then 0 else integralEstimate G

lemma integralApproximate_eq (G : Input) : integralApproximate G=approximate G := by
  unfold integralApproximate approximate
  split_ifs with hzero hodd htwo hguard
  any_goals rfl
  apply integralEstimate_eq
  have hne : G.n≠1 := by intro h; rw [h] at hodd; exact hodd (by decide)
  omega

lemma integralApproximate_correct (G : Input) :
    integralApproximate G≤count G ∧ count G≤2^(9*G.n)*integralApproximate G ∧
      (integralApproximate G=0 ↔ count G=0) := by
  rw [integralApproximate_eq]
  exact approximate_correct G

end BinaryMatching.Algorithm
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

def guardedStep {α : Type} [Coding α] [Inhabited α] (f : α → α) (z : ℕ×α) : ℕ×α :=
  (z.1,if (encode (f z.2)).length≤z.1 then f z.2 else z.2)

lemma guardedStep_size {α : Type} [Coding α] [Inhabited α] (f : α → α) (z : ℕ×α) (j : ℕ) :
    ((guardedStep f)^[j] z).1=z.1 ∧
      (encode ((guardedStep f)^[j] z).2).length≤ max z.1 (encode z.2).length := by
  induction j with
  | zero => exact ⟨rfl,Nat.le_max_right _ _⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    constructor
    · exact ih.1
    · simp only [guardedStep,ih.1]
      split_ifs with h
      · exact h.trans (Nat.le_max_left _ _)
      · exact ih.2

lemma guardedStep_eq {α : Type} [Coding α] [Inhabited α] (f : α → α) (B : ℕ) (a : α) (k : ℕ)
    (h : ∀ j,j≤k → (encode (f^[j] a)).length≤B) :
    (guardedStep f)^[k] (B,a)=(B,f^[k] a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih (fun j hj => h j (by omega))]
    have hh := h (k+1) le_rfl
    rw [Function.iterate_succ_apply'] at hh
    simp only [guardedStep,ite_eq_left hh,Function.iterate_succ_apply']

namespace Poly
variable {α : Type} [Coding α] [Inhabited α]
@[fun_prop] theorem guardedStep_poly (f : α → α) (hf : Poly f) : Poly (guardedStep f) := by
  unfold guardedStep
  have hc : Poly (fun z : ℕ×α => (encode (f z.2)).length) :=
    Poly.comp _ (fun z : ℕ×α => f z.2) Poly.codeLength (by fun_prop)
  have hh : Poly (fun z : ℕ×α => (z.1,if decide ((encode (f z.2)).length≤z.1) then f z.2 else z.2)) := by fun_prop
  exact hh.congr (fun _ => by simp)

@[fun_prop] theorem guardedIterate (f : α → α) (hf : Poly f) :
    Poly (fun z : ℕ×(ℕ×α) => ((guardedStep f)^[z.1] z.2).2) := by
  apply second
  apply boundedIterate (guardedStep f) (guardedStep_poly f hf) (3*X+1)
  intro z j hj
  have hh := guardedStep_size f z.2 j
  rw [code_pair_length,hh.1,code_nat_length]
  have hb : max z.2.1 (encode z.2.2).length≤(encode z).length := by
    simp only [code_pair_length,code_nat_length]
    omega
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
  have hN : z.2.1≤(encode z).length := by simp only [code_pair_length,code_nat_length]; omega
  omega
end Poly
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

def capDouble (z : ℕ×ℕ) : ℕ×ℕ := (z.1,min z.1 (2*z.2))
lemma capDouble_spec (z : ℕ×ℕ) (k : ℕ) :
    (capDouble^[k] z).1=z.1 ∧ (capDouble^[k] z).2≤ max z.1 z.2 := by
  induction k with
  | zero => exact ⟨rfl,Nat.le_max_right _ _⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨ih.1,(min_le_left _ _).trans (by rw [ih.1]; exact Nat.le_max_left _ _)⟩

lemma capDouble_start (b k : ℕ) : (capDouble^[k] (b,min b 1))=(b,min b (2^k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih]
    change (b,min b (2*min b (2^k)))=(b,min b (2^(k+1)))
    rw [pow_succ]
    congr 1
    omega

def cappedPow2 (b k : ℕ) : ℕ := (capDouble^[k] (b,min b 1)).2
lemma cappedPow2_eq (b k : ℕ) : cappedPow2 b k=min b (2^k) := by
  simp only [cappedPow2,capDouble_start]
lemma cappedPow2_of_le (b k : ℕ) (h : 2^k≤b) : cappedPow2 b k=2^k := by
  rw [cappedPow2_eq,min_eq_right h]

namespace Poly
@[fun_prop] theorem capDouble_poly : Poly capDouble := by unfold capDouble; fun_prop
@[fun_prop] theorem cappedPow2_poly : Poly (fun z : ℕ×ℕ => cappedPow2 z.1 z.2) := by
  have hi : Poly (fun z : ℕ×(ℕ×ℕ) => capDouble^[z.1] z.2) :=
    boundedIterate capDouble capDouble_poly (3*X+1) (by
      intro z j hj
      obtain ⟨h₁,h₂⟩ := capDouble_spec z.2 j
      rw [code_pair_length,h₁,code_nat_length,code_nat_length]
      have hm : max z.2.1 z.2.2≤(encode z).length := by
        simp only [code_pair_length,code_nat_length]; omega
      have hn : z.2.1≤(encode z).length := by
        simp only [code_pair_length,code_nat_length]; omega
      simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
      omega)
  unfold cappedPow2
  fun_prop
end Poly
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw.Optimize
open Algorithm Finset StackCode
local instance : Preorder ℤ := Int.instLinearOrder.toPreorder

abbrev Row := Matrix ℤ × ℤ
abbrev IntState := Matrix ℤ × Option ℤ
structure Params where
  n : ℕ
  q : ℕ
  k : ℕ
  L : ℕ
  D : ℕ
  M : ℕ
  pow : ℕ
  beta : Matrix ℤ
  deriving Inhabited
abbrev ParamData := ℕ×(ℕ×(ℕ×(ℕ×(ℕ×(ℕ×(ℕ×Matrix ℤ))))))
def Params.repr (p : Params) : ParamData := (p.n,(p.q,(p.k,(p.L,(p.D,(p.M,(p.pow,p.beta)))))))
instance : Coding Params := ⟨fun p => encode p.repr⟩
def Params.ofData (z : ParamData) : Params := ⟨z.1,z.2.1,z.2.2.1,z.2.2.2.1,z.2.2.2.2.1,z.2.2.2.2.2.1,z.2.2.2.2.2.2.1,z.2.2.2.2.2.2.2⟩

@[simp] lemma Params.ofData_repr (p : Params) : Params.ofData p.repr=p := rfl

def tableRep {n : ℕ} (a : Table n ℤ) : Matrix ℤ := matrixRep (fun i j => a[i][j])
def rowRep {n : ℕ} (r : Affine n) : Row := (tableRep (toTable r.coeff),r.constant)
def stateRep {n : ℕ} (s : IntegralState n) : IntState := (tableRep s.numerators,s.best)
def params (G : Input) : Params := ⟨G.n,q G.n,K G.n,L G,D₀ G,M₀ G,2^(K G.n),tableRep (toTable (Algorithm.beta G))⟩

def upperSum (n : ℕ) (f : ℕ → ℕ → ℤ) : ℤ :=
  (tab n (fun i => (tab n (fun j => if i<j then f i j else 0)).sum)).sum

lemma upperSum_rep {n : ℕ} (f : Pair n → ℤ) (g : ℕ → ℕ → ℤ)
    (h : ∀ e : Pair n,g e.val.1.val e.val.2.val=f e) : upperSum n g=∑ e,f e := by
  unfold upperSum
  rw [sum_tab]
  simp_rw [sum_tab]
  have hh : ∀ i j : Fin n,(if i.val<j.val then g i.val j.val else 0)=
      if h' : i<j then f ⟨(i,j),h'⟩ else 0 := by
    intro i j
    by_cases hij : i<j
    · simp only [dite_eq_left hij,show i.val<j.val from hij,ite_true]
      exact h ⟨(i,j),hij⟩
    · simp only [dite_eq_right hij,show ¬i.val<j.val from hij,ite_false]
  simp_rw [hh]
  rw [←Fintype.sum_prod_type (f := fun ij : Fin n×Fin n => if h' : ij.1 < ij.2 then f ⟨ij,h'⟩ else 0)]
  symm
  apply Fintype.sum_of_injective (fun e : Pair n => e.val) Subtype.val_injective f _
  · intro ij hij
    by_cases h' : ij.1 < ij.2
    · exact False.elim (hij ⟨⟨ij,h'⟩,rfl⟩)
    · simp only [dite_eq_right h']
  · intro e
    simp only [dite_eq_left e.property]

lemma get_tableRep {n : ℕ} (a : Table n ℤ) (i j : Fin n) : get (tableRep a) i.val j.val=a[i][j] :=
  get_rep _ _ _
lemma get_rowRep {n : ℕ} (r : Affine n) (e : Pair n) : get (rowRep r).1 e.val.1.val e.val.2.val=r.coeff e := by
  rw [rowRep,get_tableRep]
  exact at_toTable _ e
lemma get_beta (G : Input) (e : Pair G.n) : get (params G).beta e.val.1.val e.val.2.val=Algorithm.beta G e := by
  change get (tableRep (toTable (Algorithm.beta G))) e.val.1.val e.val.2.val=_
  rw [get_tableRep]
  exact at_toTable _ e

def rowNumerator (D : ℕ) (a : Matrix ℤ) (r : Row) : ℤ :=
  upperSum a.length (fun i j => get r.1 i j*get a i j)+r.2*D
lemma tableRep_length {n : ℕ} (a : Table n ℤ) : (tableRep a).length=n := by simp [tableRep,matrixRep,vectorRep]
lemma rowNumerator_rep {n : ℕ} (D : ℕ) (a : Table n ℤ) (r : Affine n) :
    rowNumerator D (tableRep a) (rowRep r)=Algorithm.rowNumerator D a r := by
  unfold rowNumerator Algorithm.rowNumerator
  rw [tableRep_length]
  congr 1
  apply upperSum_rep
  intro e
  rw [get_rowRep,get_tableRep]
  rfl

def indexedSlope (k j : ℕ) : ℤ := if j<k then (j:ℤ)-1 else k
def pieceNumerator (k D pow : ℕ) (a : ℤ) (j : ℕ) : ℤ :=
  indexedSlope k j*a*pow+if j<k then (D:ℤ)*(cappedPow2 pow (k-j):ℕ) else 0
lemma pieceNumerator_rep (k D : ℕ) (a : ℤ) (j : ℕ) :
    pieceNumerator k D (2^k) a j=Algorithm.pieceNumerator k D a j := by
  have hp : 2^(k-j)≤2^k := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  simp only [pieceNumerator,cappedPow2_of_le _ _ hp,Algorithm.pieceNumerator,
    indexedSlope,indexedPiece]
  split_ifs <;> push_cast <;> rfl

def selectedIndex (k D pow : ℕ) (a : ℤ) : ℕ :=
  ((List.range (k+1)).argmin (pieceNumerator k D pow a)).getD k
lemma selectedIndex_rep (k D : ℕ) (a : ℤ) : selectedIndex k D (2^k) a=Algorithm.selectedIndex k D a := by
  have hf : pieceNumerator k D (2^k) a=Algorithm.pieceNumerator k D a := funext (pieceNumerator_rep k D a)
  rw [selectedIndex,Algorithm.selectedIndex,hf]
def scaledPsi (p : Params) (a : ℤ) : ℤ := pieceNumerator p.k p.D p.pow a (selectedIndex p.k p.D p.pow a)
def scaledSlope (p : Params) (a : ℤ) : ℤ := indexedSlope p.k (selectedIndex p.k p.D p.pow a)
lemma scaledPsi_rep (G : Input) (a : ℤ) : scaledPsi (params G) a=Algorithm.scaledPsi (K G.n) (D₀ G) a := by
  simp only [scaledPsi,params,selectedIndex_rep,pieceNumerator_rep,Algorithm.scaledPsi]
lemma scaledSlope_rep (G : Input) (a : ℤ) : scaledSlope (params G) a=Algorithm.scaledSlope (K G.n) (D₀ G) a := by
  simp only [scaledSlope,params,selectedIndex_rep,Algorithm.scaledSlope,indexedSlope,indexedPiece]
  split_ifs <;> rfl
end BinaryMatching.Raw.Optimize
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw
open Finset

def residual (c : Matrix ℕ) (b : Matrix ℤ) (i j : ℕ) : Bool :=
  decide (get b i j < ((get c i j : ℕ):ℤ))
def initial (n a : ℕ) : Paths := tab n (fun v => if v=a then some [a] else none)
def predecessor (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (p : Paths) (v : ℕ) : Option ℕ :=
  (List.range n).find? (fun u => residual c b u v && (nth p u).isSome)
def pathStep (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (p : Paths) : Paths :=
  tab n (fun v => match nth p v with
    | some l => some l
    | none => match predecessor n c b p v with
      | none => none
      | some u => (nth p u).map (fun l => v::l))
def search (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (a k : ℕ) : Paths :=
  (pathStep n c b)^[k] (initial n a)
def reached (n : ℕ) (p : Paths) : Cut := tab n (fun v => (nth p v).isSome)

@[simp] lemma nth_pathRep {n : ℕ} (p : ResidualSearch.Table n) (v : Fin n) :
    nth (pathRep p) v.val=(p v).map (List.map Fin.val) := by simp [pathRep]

lemma residual_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (b : UnitFlow.Matrix (Fin n)) (i j : Fin n) :
    residual (matrixRep c) (matrixRep b) i.val j.val=decide (UnitMincut.residual c b i j) := by
  simp only [residual,UnitMincut.residual,get_rep]
  rfl

lemma initial_rep {n : ℕ} (a : Fin n) : initial n a.val=pathRep (ResidualSearch.initial a) := by
  apply tab_eq_rep
  intro v
  simp only [ResidualSearch.initial]
  by_cases hv : v=a
  · simp [hv]
  · have hval : v.val≠a.val := fun h => hv (Fin.ext h)
    simp [hv,hval]

lemma predecessor_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (b : UnitFlow.Matrix (Fin n))
    (p : ResidualSearch.Table n) (v : Fin n) :
    predecessor n (matrixRep c) (matrixRep b) (pathRep p) v.val=
      (ResidualSearch.predecessor (UnitMincut.residual c b) p v).map Fin.val := by
  unfold predecessor ResidualSearch.predecessor
  rw [range_eq_fin,List.find?_map]
  congr 1
  congr 1
  funext u
  simp only [Function.comp_apply,residual_rep,nth_pathRep,Option.isSome_map]

lemma pathStep_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (b : UnitFlow.Matrix (Fin n))
    (p : ResidualSearch.Table n) :
    pathStep n (matrixRep c) (matrixRep b) (pathRep p)=
      pathRep (ResidualSearch.step (UnitMincut.residual c b) p) := by
  apply tab_eq_rep
  intro v
  rw [nth_pathRep]
  simp only [ResidualSearch.step]
  cases hp : p v with
  | some l => rfl
  | none =>
    simp only [Option.map_none,predecessor_rep]
    cases hu : ResidualSearch.predecessor (UnitMincut.residual c b) p v with
    | none => rfl
    | some u =>
      simp only [Option.map_some,nth_pathRep,Option.map_map]
      rfl

lemma search_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (b : UnitFlow.Matrix (Fin n))
    (a : Fin n) (k : ℕ) : search n (matrixRep c) (matrixRep b) a.val k=
      pathRep (ResidualSearch.search (UnitMincut.residual c b) a k) := by
  induction k with
  | zero => exact initial_rep a
  | succ k ih =>
    simp only [search,Function.iterate_succ_apply'] at *
    rw [ih,pathStep_rep]
    rfl

lemma reached_rep {n : ℕ} (p : ResidualSearch.Table n) :
    reached n (pathRep p)=cutRep (ResidualSearch.reached p) := by
  apply tab_eq_rep
  intro v
  simp only [nth_pathRep,Option.isSome_map,ResidualSearch.mem_reached]
  cases p v <;> rfl

def pathFlow (p : List ℕ) (i j : ℕ) : ℤ :=
  ((p.zip p.tail).map (fun vu =>
    (if i=vu.2 ∧ j=vu.1 then 1 else 0)-(if i=vu.1 ∧ j=vu.2 then 1 else 0))).sum

lemma pathFlow_rep {n : ℕ} (p : List (Fin n)) (i j : Fin n) :
    pathFlow (p.map Fin.val) i.val j.val=UnitFlow.pathFlow p i j := by
  induction p using List.twoStepInduction with
  | nil => simp [pathFlow,UnitFlow.pathFlow]
  | singleton v => simp [pathFlow,UnitFlow.pathFlow]
  | cons_cons v u p _ ih =>
    have hv : (i.val=v.val)↔i=v := Fin.ext_iff.symm
    have hu : (i.val=u.val)↔i=u := Fin.ext_iff.symm
    have jv : (j.val=v.val)↔j=v := Fin.ext_iff.symm
    have ju : (j.val=u.val)↔j=u := Fin.ext_iff.symm
    simp only [pathFlow,List.map_cons,List.tail_cons,List.zip_cons_cons,List.sum_cons,
      UnitFlow.pathFlow,UnitFlow.arc,hv,hu,jv,ju] at *
    rw [ih]
    omega
end BinaryMatching.Raw
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw
open StackCode

def PathSize (p : Paths) (M : ℕ) : Prop := ∀ q∈p,(encode q).length≤M

lemma initial_size (n a : ℕ) : PathSize (initial n a) (4*a+3) := by
  intro q hq
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hq
  split_ifs
  · simp only [code_option_some,code_cons,code_nat_length,code_nil,List.length_nil,pairBits_length]
    omega
  · simp only [code_option_none,List.length_nil]; omega

lemma pathStep_size (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (p : Paths) (M : ℕ)
    (hp : PathSize p M) : PathSize (pathStep n c b p) (M+4*n+2) := by
  intro q hq
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hq
  have hvn := List.mem_range.mp hv
  have hsize (u : ℕ) : (encode (nth p u)).length≤M :=
    nth_code_bound p u M (Nat.zero_le M) hp
  change (encode (match nth p v with
    | some l => some l
    | none => match predecessor n c b p v with
      | none => none
      | some u => (nth p u).map (fun l => v::l))).length≤_
  cases h : nth p v with
  | some l => dsimp only; have hh := hsize v; rw [h] at hh; omega
  | none =>
    cases hu : predecessor n c b p v with
    | none => simp only [code_option_none,List.length_nil]; omega
    | some u =>
      dsimp only
      have hh := option_prepend_bound v (nth p u)
      have he := hsize u
      omega

lemma search_size (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (a k : ℕ) :
    PathSize (search n c b a k) (4*a+3+k*(4*n+2)) := by
  induction k with
  | zero => simpa only [search,Function.iterate_zero,id_eq,Nat.zero_mul,Nat.add_zero] using initial_size n a
  | succ k ih =>
    have hh := pathStep_size n c b _ _ ih
    simpa only [search,Function.iterate_succ_apply',Nat.add_mul,Nat.one_mul,Nat.add_assoc] using hh

lemma search_length (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (a k : ℕ) :
    (search n c b a k).length=n := by
  cases k with
  | zero => simp [search,initial,tab]
  | succ k => simp [search,Function.iterate_succ_apply',pathStep,tab]

lemma search_code_bound (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (a k : ℕ) :
    (encode (search n c b a k)).length≤n*(2*(4*a+3+k*(4*n+2))+1) := by
  have h := list_code_bound _ _ (search_size n c b a k)
  rwa [search_length] at h

end BinaryMatching.Raw
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode.Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ] [Inhabited β]

theorem optionCasesWith (p : α → Option β) (f : α → γ) (g : α×β → γ)
    (hp : Poly p) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => match p a with | none => f a | Option.some b => g (a,b)) := by
  have h : Poly (fun a => if (p a).isSome then g (a,(p a).getD default) else f a) := by fun_prop
  exact h.congr (fun a => by cases p a <;> rfl)

theorem optionMapWith (p : α → Option β) (g : α×β → γ) (hp : Poly p) (hg : Poly g) :
    Poly (fun a => (p a).map (fun b => g (a,b))) := by
  have h := optionCasesWith p (fun _ => (none:Option γ))
    (fun z => Option.some (g z)) hp (by fun_prop) (by fun_prop)
  exact h.congr (fun a => by cases p a <;> rfl)
end BinaryMatching.StackCode.Poly
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw
open StackCode Polynomial
abbrev SearchContext := ℕ×(Matrix ℕ×(Matrix ℤ×ℕ))
abbrev SearchState := SearchContext×Paths

def searchStep (s : SearchState) : SearchState :=
  (s.1,pathStep s.1.1 s.1.2.1 s.1.2.2.1 s.2)
def searchInitial (z : SearchContext×ℕ) : SearchState :=
  (z.1,initial z.1.1 z.1.2.2.2)

lemma searchStep_iterate (z : SearchContext×ℕ) (j : ℕ) :
    searchStep^[j] (searchInitial z)=(z.1,search z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 j) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply',ih,searchStep,search]

namespace Compiler
open StackCode.Poly

@[fun_prop] theorem residual_poly :
    Poly (fun z : (Matrix ℕ×Matrix ℤ)×(ℕ×ℕ) => residual z.1.1 z.1.2 z.2.1 z.2.2) := by
  unfold residual
  fun_prop

@[fun_prop] theorem initial_poly : Poly (fun z : ℕ×ℕ => initial z.1 z.2) := by
  unfold initial
  apply Poly.rawTab Prod.fst (fun z : (ℕ×ℕ)×ℕ => if z.2=z.1.2 then Option.some [z.1.2] else none)
  · fun_prop
  · have h : Poly (fun z : (ℕ×ℕ)×ℕ => if decide (z.2=z.1.2) then Option.some [z.1.2] else none) := by fun_prop
    exact h.congr (fun z => by simp)

@[fun_prop] theorem predecessor_poly :
    Poly (fun z : ((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ =>
      predecessor z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2) := by
  unfold predecessor
  apply Poly.findWith (fun z => List.range z.1.1.1)
    (fun z : (((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ)×ℕ =>
      residual z.1.1.1.2.1 z.1.1.1.2.2 z.2 z.1.2 && (nth z.1.1.2 z.2).isSome)
  · fun_prop
  · have hr := Poly.comp _ (fun z : (((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ)×ℕ =>
        ((z.1.1.1.2.1,z.1.1.1.2.2),(z.2,z.1.2))) residual_poly (by fun_prop)
    have hs : Poly (fun z : (((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ)×ℕ =>
        (nth z.1.1.2 z.2).isSome) := by fun_prop
    exact Poly.comp _ _ Poly.boolAnd (Poly.pair _ _ hr hs)

def pathEntry (z : ((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ) : Option (List ℕ) :=
  match nth z.1.2 z.2 with
  | Option.some l => Option.some l
  | none => match predecessor z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2 with
    | none => none
    | Option.some u => (nth z.1.2 u).map (fun l => z.2::l)

@[fun_prop] theorem pathEntry_poly : Poly pathEntry := by
  have h := Poly.optionCasesWith
    (fun z : ((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ => nth z.1.2 z.2)
    (fun z => match predecessor z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2 with
      | none => none
      | Option.some u => (nth z.1.2 u).map (fun l => z.2::l))
    (fun z => Option.some z.2)
    (by fun_prop)
    (by
      have hi := Poly.optionCasesWith
        (fun z : ((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ => predecessor z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2)
        (fun _ => (none:Option (List ℕ)))
        (fun z => (nth z.1.1.2 z.2).map (fun l => z.1.2::l))
        predecessor_poly (by fun_prop)
        (Poly.optionMapWith (fun z : (((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ)×ℕ => nth z.1.1.2 z.2)
          (fun z => z.1.1.2::z.2) (by fun_prop) (by fun_prop))
      exact hi.congr (fun z => by cases predecessor z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2 <;> rfl))
    (by fun_prop)
  exact h.congr (fun z => by unfold pathEntry; cases nth z.1.2 z.2 <;> rfl)

@[fun_prop] theorem pathStep_poly :
    Poly (fun z : (ℕ×(Matrix ℕ×Matrix ℤ))×Paths => pathStep z.1.1 z.1.2.1 z.1.2.2 z.2) := by
  exact Poly.rawTab (fun z => z.1.1) pathEntry (by fun_prop) pathEntry_poly

@[fun_prop] theorem searchStep_poly : Poly searchStep := by
  unfold searchStep
  apply Poly.pair
  · fun_prop
  · exact Poly.comp _ (fun s : SearchState => ((s.1.1,(s.1.2.1,s.1.2.2.1)),s.2))
      pathStep_poly (by fun_prop)

@[fun_prop] theorem searchInitial_poly : Poly searchInitial := by
  unfold searchInitial
  apply Poly.pair
  · fun_prop
  · exact Poly.comp _ (fun z : SearchContext×ℕ => (z.1.1,z.1.2.2.2)) initial_poly (by fun_prop)

@[fun_prop] theorem search_poly : Poly (fun z : SearchContext×ℕ =>
    search z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2) := by
  have hi := Poly.iterateFrom searchStep searchStep_poly Prod.snd searchInitial (by fun_prop)
    searchInitial_poly (100*(X+1)^3) (by
      intro z j hj
      rw [searchStep_iterate]
      let N := (encode (z.2,searchInitial z)).length
      have hctx : (encode z.1).length≤N := by
        simp only [N,searchInitial,code_pair_length,code_nat_length]; omega
      have hn : z.1.1≤N := by
        have := (pair_left_le z.1).trans hctx
        simpa only [code_nat_length] using this
      have ha : z.1.2.2.2≤N := by
        have := (pair_right_le z.1.2.2).trans ((pair_right_le z.1.2).trans ((pair_right_le z.1).trans hctx))
        simpa only [code_nat_length] using this
      have hk : j≤N := by
        simp only [N,code_pair_length,code_nat_length]; omega
      have hb := search_code_bound z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 j
      have hm : z.1.1*(2*(4*z.1.2.2.2+3+j*(4*z.1.1+2))+1)≤
          N*(2*(4*N+3+N*(4*N+2))+1) := by gcongr
      simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
      change (encode (z.1,search z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 j)).length≤100*(N+1)^3
      rw [code_pair_length]
      have hbb := hb.trans hm
      nlinarith)
  have h := Poly.second _ hi
  exact h.congr (fun z => by rw [searchStep_iterate])

end Compiler
end BinaryMatching.Raw
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw
open Finset

def augment (n : ℕ) (c : Matrix ℕ) (a z : ℕ) (b : Matrix ℤ) : Matrix ℤ :=
  match nth (search n c b a n) z with
  | none => b
  | some p => matrix n (fun i j => get b i j+pathFlow p i j)
def flow (n : ℕ) (c : Matrix ℕ) (a z k : ℕ) : Matrix ℤ :=
  (augment n c a z)^[k] (matrix n (fun _ _ => 0))
def sourceCapacity (n : ℕ) (c : Matrix ℕ) (a : ℕ) : ℕ := (tab n (get c a)).sum
def mincut (n : ℕ) (c : Matrix ℕ) (a z : ℕ) : Cut :=
  reached n (search n c (flow n c a z (sourceCapacity n c a)) a n)
def cutCapacity (n : ℕ) (c : Matrix ℕ) (S : Cut) : ℕ :=
  (tab n (fun i => (tab n (fun j => if mem S i && !mem S j then get c i j else 0)).sum)).sum

def pairs (n : ℕ) : List (ℕ×ℕ) := (List.range n).flatMap (fun i => (List.range n).map (i,·))
def pairCuts (n : ℕ) (c : Matrix ℕ) (U : Cut) : List Cut :=
  ((pairs n).filter (fun az => mem U az.1 && mem U az.2 && decide (az.1≠az.2))).map
    (fun az => mincut n c az.1 az.2)
def terminalCut (n : ℕ) (c : Matrix ℕ) (U : Cut) : Cut :=
  ((pairCuts n c U).argmin (cutCapacity n c)).getD (empty n)

lemma augment_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (a z : Fin n) (b : UnitFlow.Matrix (Fin n)) :
    augment n (matrixRep c) a.val z.val (matrixRep b)=matrixRep (UnitMincut.augment c a z b) := by
  unfold augment
  rw [search_rep,nth_pathRep]
  unfold UnitMincut.augment
  cases h : ResidualSearch.search (UnitMincut.residual c b) a n z with
  | none => rfl
  | some p =>
    simp only [Option.map_some]
    apply matrix_eq_rep
    intro i j
    simp only [get_rep,pathFlow_rep]
lemma flow_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (a z : Fin n) (k : ℕ) :
    flow n (matrixRep c) a.val z.val k=matrixRep (UnitMincut.iterate c a z k) := by
  induction k with
  | zero => exact matrix_eq_rep _ _ (fun _ _ => rfl)
  | succ k ih =>
    simp only [flow,Function.iterate_succ_apply'] at *
    rw [ih,augment_rep]
    rfl
lemma sourceCapacity_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (a : Fin n) :
    sourceCapacity n (matrixRep c) a.val=UnitMincut.sourceCapacity c a := by
  simp [sourceCapacity,sum_tab,UnitMincut.sourceCapacity]
lemma mincut_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (a z : Fin n) :
    mincut n (matrixRep c) a.val z.val=cutRep (UnitMincut.mincut c a z) := by
  simp only [mincut,sourceCapacity_rep,flow_rep,search_rep,reached_rep,UnitMincut.mincut]
lemma cutCapacity_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (S : Finset (Fin n)) :
    cutCapacity n (matrixRep c) (cutRep S)=UnitFlow.cutCapacity c S := by
  simp only [cutCapacity,sum_tab,mem_rep,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,
    decide_eq_false_iff_not,get_rep]
  simp only [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [Finset.sum_ite_mem,Finset.univ_inter]
  unfold UnitFlow.cutCapacity
  apply Finset.sum_congr rfl
  intro i hi
  rw [show Sᶜ=univ.filter (fun j => j∉S) by ext; simp]
  simp only [Finset.sum_filter]

lemma pairs_rep (n : ℕ) : pairs n=(((List.finRange n).product (List.finRange n)).map
    (fun az => (az.1.val,az.2.val))) := by
  simp only [pairs,List.product,range_eq_fin,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]

lemma pairCuts_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) :
    pairCuts n (matrixRep c) (cutRep U)=(TerminalMincut.pairCuts c U).map cutRep := by
  unfold pairCuts TerminalMincut.pairCuts
  rw [pairs_rep,List.filter_map,List.map_map,List.map_map]
  have hp : (fun az : Fin n×Fin n => mem (cutRep U) az.1.val && mem (cutRep U) az.2.val &&
      decide (az.1.val≠az.2.val))=(fun az => decide (az.1∈U ∧ az.2∈U ∧ az.1≠az.2)) := by
    funext az
    simp [Fin.ext_iff,Bool.and_assoc]
  simp only [Function.comp_def]
  rw [hp]
  apply List.map_congr_left
  intro az haz
  exact mincut_rep c az.1 az.2

lemma argmin_map_eq {α β : Type} (f : α → β) (l : List α) (g : β → ℕ) :
    (l.map f).argmin g=(l.argmin (g ∘ f)).map f := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.map_append,List.map_singleton,List.argmin_concat,List.argmin_concat,ih]
    cases h : l.argmin (g ∘ f) with
    | none => rfl
    | some b => simp only [Option.map_some,Function.comp_apply]; split_ifs <;> rfl

lemma terminalCut_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) :
    terminalCut n (matrixRep c) (cutRep U)=cutRep (TerminalMincut.terminalCut c U) := by
  unfold terminalCut TerminalMincut.terminalCut
  rw [pairCuts_rep,argmin_map_eq]
  have hg : cutCapacity n (matrixRep c) ∘ cutRep=UnitFlow.cutCapacity c := by
    funext S; exact cutCapacity_rep c S
  rw [hg,empty_rep]
  cases h : (TerminalMincut.pairCuts c U).argmin (UnitFlow.cutCapacity c) <;> rfl

end BinaryMatching.Raw
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw
open StackCode

lemma nth_property {α : Type} [Inhabited α] (P : α → Prop) (l : List α) (i : ℕ)
    (hd : P default) (h : ∀ a∈l,P a) : P (nth l i) := by
  unfold nth
  cases hi : l[i]? with
  | none => exact hd
  | some a => exact h a (List.mem_of_getElem? hi)

def MatrixBound (b : Matrix ℤ) (M : ℕ) : Prop := ∀ row∈b,∀ v∈row,v.natAbs≤M

def Square {α : Type} (n : ℕ) (b : Matrix α) : Prop := b.length=n ∧ ∀ row∈b,row.length=n

lemma matrix_square {α : Type} (n : ℕ) (f : ℕ → ℕ → α) : Square n (matrix n f) := by
  constructor
  · simp [matrix,tab]
  · intro row hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    simp [tab]

lemma matrix_bound (n M : ℕ) (f : ℕ → ℕ → ℤ) (h : ∀ i,i<n → ∀ j,j<n → (f i j).natAbs≤M) :
    MatrixBound (matrix n f) M := by
  intro row hr v hv
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
  exact h _ (List.mem_range.mp hi) _ (List.mem_range.mp hj)

lemma get_abs_bound (b : Matrix ℤ) (M : ℕ) (hb : MatrixBound b M) (i j : ℕ) :
    (get b i j).natAbs≤M := by
  apply nth_property (fun z : ℤ => z.natAbs≤M)
  · exact Nat.zero_le _
  · apply nth_property (fun row : List ℤ => ∀ v∈row,v.natAbs≤M)
    · intro v hv; cases hv
    · exact hb

lemma matrix_bound_code (n M : ℕ) (b : Matrix ℤ) (hs : Square n b) (hb : MatrixBound b M) :
    (encode b).length≤n*(2*(n*(2*(M+3)+1))+1) := by
  have hh := list_code_bound b (n*(2*(M+3)+1)) (by
    intro row hr
    have hrow := list_code_bound row (M+3) (by
      intro v hv
      rw [code_int_length]
      have he := hb row hr v hv
      omega)
    rwa [hs.2 row hr] at hrow)
  rwa [hs.1] at hh

lemma pathFlow_abs (p : List ℕ) (i j : ℕ) : (pathFlow p i j).natAbs≤p.length := by
  induction p using List.twoStepInduction with
  | nil => simp [pathFlow]
  | singleton a => simp [pathFlow]
  | cons_cons v u p _ ih =>
    have hip := ih u
    have he : pathFlow (v::u::p) i j=
        ((if i=u ∧ j=v then 1 else 0)-(if i=v ∧ j=u then 1 else 0))+
        pathFlow (u::p) i j := by
      simp [pathFlow]
    rw [he]
    have hsmall : (((if i=u ∧ j=v then 1 else 0)-(if i=v ∧ j=u then 1 else 0)):ℤ).natAbs≤1 := by
      split_ifs <;> decide
    have h := Int.natAbs_add_le
      (((if i=u ∧ j=v then 1 else 0)-(if i=v ∧ j=u then 1 else 0)):ℤ) (pathFlow (u::p) i j)
    simp only [List.length_cons] at *
    omega

lemma search_path_bound (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (a z : ℕ) (p : List ℕ)
    (hp : nth (search n c b a n) z=some p) : p.length≤4*a+3+n*(4*n+2) := by
  have hh := nth_code_bound (search n c b a n) z (4*a+3+n*(4*n+2))
    (Nat.zero_le _) (search_size n c b a n)
  rw [hp,code_option_some] at hh
  have hl := list_length_le_code p
  omega

lemma augment_bound (n : ℕ) (c : Matrix ℕ) (a z : ℕ) (b : Matrix ℤ) (M : ℕ)
    (hb : MatrixBound b M) : MatrixBound (augment n c a z b) (M+(4*a+3+n*(4*n+2))) := by
  unfold augment
  cases hp : nth (search n c b a n) z with
  | none => intro row hr v hv; have := hb row hr v hv; omega
  | some p =>
    apply matrix_bound
    intro i hi j hj
    have hh := Int.natAbs_add_le (get b i j) (pathFlow p i j)
    have h₁ := get_abs_bound b M hb i j
    have h₂ := (pathFlow_abs p i j).trans (search_path_bound n c b a z p hp)
    omega

lemma augment_square (n : ℕ) (c : Matrix ℕ) (a z : ℕ) (b : Matrix ℤ)
    (hb : Square n b) : Square n (augment n c a z b) := by
  unfold augment
  split
  · exact hb
  · exact matrix_square _ _

lemma flow_bound (n : ℕ) (c : Matrix ℕ) (a z k : ℕ) :
    MatrixBound (flow n c a z k) (k*(4*a+3+n*(4*n+2))) := by
  induction k with
  | zero => simpa only [flow,Function.iterate_zero,Function.id_def,Nat.zero_mul] using matrix_bound n 0 (fun _ _ => 0) (fun _ _ _ _ => le_rfl)
  | succ k ih =>
    have hh := augment_bound n c a z _ _ ih
    simpa only [flow,Function.iterate_succ_apply',Nat.add_mul,Nat.one_mul] using hh

lemma flow_square (n : ℕ) (c : Matrix ℕ) (a z k : ℕ) : Square n (flow n c a z k) := by
  induction k with
  | zero => exact matrix_square _ _
  | succ k ih => simpa only [flow,Function.iterate_succ_apply'] using augment_square n c a z _ ih
lemma flow_code_bound (n : ℕ) (c : Matrix ℕ) (a z k : ℕ) :
    (encode (flow n c a z k)).length≤n*(2*(n*(2*(k*(4*a+3+n*(4*n+2))+3)+1))+1) :=
  matrix_bound_code _ _ _ (flow_square n c a z k) (flow_bound n c a z k)
end BinaryMatching.Raw
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw
open StackCode Polynomial
abbrev FlowContext := ℕ×(Matrix ℕ×(ℕ×ℕ))
abbrev FlowState := FlowContext×Matrix ℤ

def flowStep (s : FlowState) : FlowState :=
  (s.1,augment s.1.1 s.1.2.1 s.1.2.2.1 s.1.2.2.2 s.2)
def flowInitial (z : FlowContext×ℕ) : FlowState :=
  (z.1,matrix z.1.1 (fun _ _ => 0))
lemma flowStep_iterate (z : FlowContext×ℕ) (j : ℕ) :
    flowStep^[j] (flowInitial z)=(z.1,flow z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 j) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply',ih,flowStep,flow]

namespace Compiler
open StackCode.Poly
@[fun_prop] theorem reached_poly : Poly (fun z : ℕ×Paths => reached z.1 z.2) := by
  unfold reached
  exact Poly.rawTab Prod.fst (fun z : (ℕ×Paths)×ℕ => (nth z.1.2 z.2).isSome)
    (by fun_prop) (by fun_prop)
@[fun_prop] theorem pathFlow_poly : Poly (fun z : List ℕ×(ℕ×ℕ) => pathFlow z.1 z.2.1 z.2.2) := by
  unfold pathFlow
  have h : Poly (fun z : (List ℕ×(ℕ×ℕ))×(ℕ×ℕ) =>
      ((if decide (z.1.2.1=z.2.2) && decide (z.1.2.2=z.2.1) then 1 else 0)-
       (if decide (z.1.2.1=z.2.1) && decide (z.1.2.2=z.2.2) then 1 else 0):ℤ)) := by fun_prop
  have hm := Poly.mapWith (fun z : List ℕ×(ℕ×ℕ) => z.1.zip z.1.tail) _ (by fun_prop) h
  exact (Poly.comp List.sum _ Poly.listIntSum hm).congr (fun z => by simp only [Bool.and_eq_true,decide_eq_true_eq])
@[fun_prop] theorem augment_poly : Poly (fun z : FlowState =>
    augment z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2) := by
  have hp : Poly (fun z : FlowState => nth (search z.1.1 z.1.2.1 z.2 z.1.2.2.1 z.1.1) z.1.2.2.2) := by
    apply Poly.rawNth
    · exact Poly.comp _ (fun z : FlowState => ((z.1.1,(z.1.2.1,(z.2,z.1.2.2.1))),z.1.1))
        search_poly (by fun_prop)
    · fun_prop
  have hm : Poly (fun z : FlowState×List ℕ => matrix z.1.1.1 (fun i j => get z.1.2 i j+pathFlow z.2 i j)) := by
    apply Poly.rawMatrix (fun z : FlowState×List ℕ => z.1.1.1)
      (fun z : ((FlowState×List ℕ)×ℕ)×ℕ => get z.1.1.1.2 z.1.2 z.2+pathFlow z.1.1.2 z.1.2 z.2)
    · fun_prop
    · have hp := Poly.comp _ (fun z : ((FlowState×List ℕ)×ℕ)×ℕ => (z.1.1.2,(z.1.2,z.2)))
        pathFlow_poly (by fun_prop)
      fun_prop
  have h := Poly.optionCasesWith
    (fun z : FlowState => nth (search z.1.1 z.1.2.1 z.2 z.1.2.2.1 z.1.1) z.1.2.2.2)
    Prod.snd
    (fun z => matrix z.1.1.1 (fun i j => get z.1.2 i j+pathFlow z.2 i j)) hp (by fun_prop) hm
  exact h.congr (fun z => by unfold augment; cases nth (search z.1.1 z.1.2.1 z.2 z.1.2.2.1 z.1.1) z.1.2.2.2 <;> rfl)
@[fun_prop] theorem flowStep_poly : Poly flowStep := Poly.pair _ _ (by fun_prop) augment_poly
@[fun_prop] theorem flowInitial_poly : Poly flowInitial := by
  unfold flowInitial
  apply Poly.pair
  · fun_prop
  · exact Poly.rawMatrix (fun z : FlowContext×ℕ => z.1.1) (fun _ => (0:ℤ)) (by fun_prop) (by fun_prop)
@[fun_prop] theorem flow_poly : Poly (fun z : FlowContext×ℕ =>
    flow z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2) := by
  have hi := Poly.iterateFrom flowStep flowStep_poly Prod.snd flowInitial (by fun_prop)
    flowInitial_poly (1000*(X+1)^5) (by
      intro z j hj
      rw [flowStep_iterate]
      let N := (encode (z.2,flowInitial z)).length
      have hctx : (encode z.1).length≤N := by
        simp only [N,flowInitial,code_pair_length,code_nat_length]; omega
      have hn : z.1.1≤N := by
        have := (pair_left_le z.1).trans hctx
        simpa only [code_nat_length] using this
      have ha : z.1.2.2.1≤N := by
        have := (pair_left_le z.1.2.2).trans ((pair_right_le z.1.2).trans ((pair_right_le z.1).trans hctx))
        simpa only [code_nat_length] using this
      have hk : j≤N := by
        simp only [N,code_pair_length,code_nat_length]; omega
      have hb := flow_code_bound z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 j
      have hm : z.1.1*(2*(z.1.1*(2*(j*(4*z.1.2.2.1+3+z.1.1*(4*z.1.1+2))+3)+1))+1)≤
          N*(2*(N*(2*(N*(4*N+3+N*(4*N+2))+3)+1))+1) := by gcongr
      simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
      change (encode (z.1,flow z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 j)).length≤1000*(N+1)^5
      rw [code_pair_length]
      dsimp only
      have hbb := hb.trans hm
      calc
        _ ≤ 2*N+N*(2*(N*(2*(N*(4*N+3+N*(4*N+2))+3)+1))+1)+1 := by omega
        _ ≤ 1000*(N+1)^5 := by ring_nf; omega)
  exact (Poly.second _ hi).congr (fun z => by rw [flowStep_iterate])
@[fun_prop] theorem sourceCapacity_poly : Poly (fun z : ℕ×(Matrix ℕ×ℕ) => sourceCapacity z.1 z.2.1 z.2.2) := by
  unfold sourceCapacity
  apply Poly.comp List.sum _ Poly.listNatSum
  exact Poly.rawTab Prod.fst (fun z : (ℕ×(Matrix ℕ×ℕ))×ℕ => get z.1.2.1 z.1.2.2 z.2)
    (by fun_prop) (by fun_prop)
@[fun_prop] theorem mincut_poly : Poly (fun z : FlowContext => mincut z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold mincut
  have hs : Poly (fun z : FlowContext => sourceCapacity z.1 z.2.1 z.2.2.1) :=
    Poly.comp _ (fun z : FlowContext => (z.1,(z.2.1,z.2.2.1))) sourceCapacity_poly (by fun_prop)
  have hf : Poly (fun z : FlowContext => flow z.1 z.2.1 z.2.2.1 z.2.2.2 (sourceCapacity z.1 z.2.1 z.2.2.1)) :=
    Poly.comp _ (fun z : FlowContext => (z,sourceCapacity z.1 z.2.1 z.2.2.1)) flow_poly (by fun_prop)
  have hsearch := Poly.comp _ (fun z : FlowContext =>
    ((z.1,(z.2.1,(flow z.1 z.2.1 z.2.2.1 z.2.2.2 (sourceCapacity z.1 z.2.1 z.2.2.1),z.2.2.1))),z.1)) search_poly (by fun_prop)
  exact Poly.comp _ (fun z : FlowContext =>
    (z.1,search z.1 z.2.1 (flow z.1 z.2.1 z.2.2.1 z.2.2.2 (sourceCapacity z.1 z.2.1 z.2.2.1)) z.2.2.1 z.1)) reached_poly (by fun_prop)
@[fun_prop] theorem cutCapacity_poly : Poly (fun z : ℕ×(Matrix ℕ×Cut) => cutCapacity z.1 z.2.1 z.2.2) := by
  unfold cutCapacity
  apply Poly.comp List.sum _ Poly.listNatSum
  apply Poly.rawTab Prod.fst (fun z : (ℕ×(Matrix ℕ×Cut))×ℕ =>
    (tab z.1.1 (fun j => if mem z.1.2.2 z.2 && !mem z.1.2.2 j then get z.1.2.1 z.2 j else 0)).sum)
  · fun_prop
  · apply Poly.comp List.sum _ Poly.listNatSum
    apply Poly.rawTab (fun z : (ℕ×(Matrix ℕ×Cut))×ℕ => z.1.1)
      (fun z : ((ℕ×(Matrix ℕ×Cut))×ℕ)×ℕ => if mem z.1.1.2.2 z.1.2 && !mem z.1.1.2.2 z.2 then
        get z.1.1.2.1 z.1.2 z.2 else 0)
    · fun_prop
    · fun_prop
@[fun_prop] theorem pairs_poly : Poly pairs := by
  unfold pairs
  apply Poly.flatMapWith List.range (fun z : ℕ×ℕ => (List.range z.1).map (fun j => (z.2,j))) (by fun_prop)
  exact Poly.mapWith (fun z : ℕ×ℕ => List.range z.1) (fun z : (ℕ×ℕ)×ℕ => (z.1.2,z.2)) (by fun_prop) (by fun_prop)
@[fun_prop] theorem pairCuts_poly : Poly (fun z : ℕ×(Matrix ℕ×Cut) => pairCuts z.1 z.2.1 z.2.2) := by
  unfold pairCuts
  apply Poly.mapWith _ (fun z : (ℕ×(Matrix ℕ×Cut))×(ℕ×ℕ) => mincut z.1.1 z.1.2.1 z.2.1 z.2.2)
  · apply Poly.filterWith _ (fun z : (ℕ×(Matrix ℕ×Cut))×(ℕ×ℕ) =>
      mem z.1.2.2 z.2.1 && mem z.1.2.2 z.2.2 && decide (z.2.1≠z.2.2))
    · fun_prop
    · have h : Poly (fun z : (ℕ×(Matrix ℕ×Cut))×(ℕ×ℕ) =>
        mem z.1.2.2 z.2.1 && mem z.1.2.2 z.2.2 && !decide (z.2.1=z.2.2)) := by fun_prop
      exact h.congr (fun z => by simp)
  · exact Poly.comp _ (fun z : (ℕ×(Matrix ℕ×Cut))×(ℕ×ℕ) => (z.1.1,(z.1.2.1,z.2))) mincut_poly (by fun_prop)
@[fun_prop] theorem terminalCut_poly : Poly (fun z : ℕ×(Matrix ℕ×Cut) => terminalCut z.1 z.2.1 z.2.2) := by
  unfold terminalCut
  have hf := Poly.listArgminParam Poly.natLT
    (fun z : (ℕ×Matrix ℕ)×Cut => cutCapacity z.1.1 z.1.2 z.2)
    (Poly.comp _ (fun z : (ℕ×Matrix ℕ)×Cut => (z.1.1,(z.1.2,z.2))) cutCapacity_poly (by fun_prop))
  have ha := Poly.comp _ (fun z : ℕ×(Matrix ℕ×Cut) => ((z.1,z.2.1),pairCuts z.1 z.2.1 z.2.2)) hf (by fun_prop)
  have h : Poly (fun z : ℕ×(Matrix ℕ×Cut) => if ((pairCuts z.1 z.2.1 z.2.2).argmin (cutCapacity z.1 z.2.1)).isSome then
      ((pairCuts z.1 z.2.1 z.2.2).argmin (cutCapacity z.1 z.2.1)).getD default else empty z.1) := by fun_prop
  exact h.congr (fun z => by cases (pairCuts z.1 z.2.1 z.2.2).argmin (cutCapacity z.1 z.2.1) <;> rfl)
end Compiler
end BinaryMatching.Raw
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw
open Finset

def outside (n : ℕ) (A : Cut) : Option ℕ := (List.range n).find? (fun i => !mem A i)
def contractMap (A : Cut) (r i : ℕ) : ℕ := if mem A i then i else r
def contract (n : ℕ) (c : Matrix ℕ) (A : Cut) (r : ℕ) : Matrix ℕ :=
  matrix n (fun i j => if i=j then 0 else
    (tab n (fun u => (tab n (fun v =>
      if contractMap A r u=i ∧ contractMap A r v=j then get c u v else 0)).sum)).sum)
def lift (n : ℕ) (A : Cut) (r : ℕ) (S : Cut) : Cut :=
  tab n (fun i => mem S (contractMap A r i))
def cheaper (n : ℕ) (c : Matrix ℕ) (S T : Cut) : Cut :=
  if cutCapacity n c S≤cutCapacity n c T then S else T

lemma outside_rep {n : ℕ} (A : Finset (Fin n)) :
    outside n (cutRep A)=(OddMincut.outside A).map Fin.val := by
  unfold outside OddMincut.outside
  rw [range_eq_fin,List.find?_map]
  congr 1
  congr 1
  funext i
  simp only [Function.comp_apply,mem_rep,decide_not]

lemma contractMap_rep {n : ℕ} (A : Finset (Fin n)) (r i : Fin n) :
    contractMap (cutRep A) r.val i.val=(OddCutParity.contractMap A r i).val := by
  simp only [contractMap,mem_rep,decide_eq_true_eq,OddCutParity.contractMap]
  split_ifs <;> rfl

lemma contract_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (A : Finset (Fin n)) (r : Fin n) :
    contract n (matrixRep c) (cutRep A) r.val=
      matrixRep (CutAlgebra.push c (OddCutParity.contractMap A r)) := by
  apply matrix_eq_rep
  intro i j
  simp only [Fin.ext_iff,contractMap_rep,sum_tab,get_rep,CutAlgebra.push]

lemma lift_rep {n : ℕ} (A S : Finset (Fin n)) (r : Fin n) :
    lift n (cutRep A) r.val (cutRep S)=cutRep (CutAlgebra.lift (OddCutParity.contractMap A r) S) := by
  apply tab_eq_rep
  intro i
  simp only [contractMap_rep,mem_rep,CutAlgebra.mem_lift]

lemma cheaper_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (S T : Finset (Fin n)) :
    cheaper n (matrixRep c) (cutRep S) (cutRep T)=cutRep (OddMincut.cheaper c S T) := by
  simp only [cheaper,cutCapacity_rep,OddMincut.cheaper]
  split_ifs <;> rfl
end BinaryMatching.Raw
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw.Compiler
open StackCode StackCode.Poly
@[fun_prop] theorem doubleNatSum {α : Type} [Coding α] [Inhabited α]
    (n : α → ℕ) (f : (α×ℕ)×ℕ → ℕ) (hn : Poly n) (hf : Poly f) :
    Poly (fun a => (tab (n a) (fun i => (tab (n a) (fun j => f ((a,i),j))).sum)).sum) := by
  apply Poly.comp List.sum _ Poly.listNatSum
  apply Poly.rawTab n (fun z : α×ℕ => (tab (n z.1) (fun j => f (z,j))).sum) hn
  apply Poly.comp List.sum _ Poly.listNatSum
  exact Poly.rawTab (fun z : α×ℕ => n z.1) f (by fun_prop) hf

@[fun_prop] theorem outside_poly : Poly (fun z : ℕ×Cut => outside z.1 z.2) := by
  unfold outside
  exact Poly.findWith (fun z : ℕ×Cut => List.range z.1)
    (fun z : (ℕ×Cut)×ℕ => !mem z.1.2 z.2) (by fun_prop) (by fun_prop)
@[fun_prop] theorem contractMap_poly : Poly (fun z : Cut×(ℕ×ℕ) => contractMap z.1 z.2.1 z.2.2) := by
  unfold contractMap
  fun_prop
@[fun_prop] theorem contract_poly : Poly (fun z : ℕ×(Matrix ℕ×(Cut×ℕ)) => contract z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold contract
  apply Poly.rawMatrix Prod.fst
    (fun z : ((ℕ×(Matrix ℕ×(Cut×ℕ)))×ℕ)×ℕ => if z.1.2=z.2 then 0 else
      (tab z.1.1.1 (fun u => (tab z.1.1.1 (fun v =>
        if contractMap z.1.1.2.2.1 z.1.1.2.2.2 u=z.1.2 ∧ contractMap z.1.1.2.2.1 z.1.1.2.2.2 v=z.2
        then get z.1.1.2.1 u v else 0)).sum)).sum)
  · fun_prop
  · have hs := doubleNatSum
      (fun z : ((ℕ×(Matrix ℕ×(Cut×ℕ)))×ℕ)×ℕ => z.1.1.1)
      (fun z : ((((ℕ×(Matrix ℕ×(Cut×ℕ)))×ℕ)×ℕ)×ℕ)×ℕ =>
        if decide (contractMap z.1.1.1.1.2.2.1 z.1.1.1.1.2.2.2 z.1.2=z.1.1.1.2) &&
          decide (contractMap z.1.1.1.1.2.2.1 z.1.1.1.1.2.2.2 z.2=z.1.1.2)
        then get z.1.1.1.1.2.1 z.1.2 z.2 else 0)
      (by fun_prop) (by fun_prop)
    have h : Poly (fun z : ((ℕ×(Matrix ℕ×(Cut×ℕ)))×ℕ)×ℕ => if decide (z.1.2=z.2) then 0 else
        (tab z.1.1.1 (fun u => (tab z.1.1.1 (fun v =>
          if decide (contractMap z.1.1.2.2.1 z.1.1.2.2.2 u=z.1.2) && decide (contractMap z.1.1.2.2.1 z.1.1.2.2.2 v=z.2)
          then get z.1.1.2.1 u v else 0)).sum)).sum) := by
      fun_prop
    exact h.congr (fun z => by simp only [decide_eq_true_eq,Bool.and_eq_true])
@[fun_prop] theorem lift_poly : Poly (fun z : ℕ×(Cut×(ℕ×Cut)) => lift z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold lift
  exact Poly.rawTab Prod.fst
    (fun z : (ℕ×(Cut×(ℕ×Cut)))×ℕ => mem z.1.2.2.2 (contractMap z.1.2.1 z.1.2.2.1 z.2))
    (by fun_prop) (by fun_prop)
@[fun_prop] theorem cheaper_poly : Poly (fun z : ℕ×(Matrix ℕ×(Cut×Cut)) => cheaper z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold cheaper
  have h : Poly (fun z : ℕ×(Matrix ℕ×(Cut×Cut)) =>
      if decide (cutCapacity z.1 z.2.1 z.2.2.1≤cutCapacity z.1 z.2.1 z.2.2.2) then z.2.2.1 else z.2.2.2) := by fun_prop
  exact h.congr (fun _ => by simp)
end BinaryMatching.Raw.Compiler
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.RecursiveEval

inductive Branch (A B C : Type) where
  | leaf : B → Branch A B C
  | fork : C → A → A → Branch A B C

inductive Command (A C : Type) where
  | call : ℕ → A → Command A C
  | join : C → Command A C

abbrev State (A B C : Type) := List (Command A C) × List B

variable {A B C : Type} (zero : B) (expand : A → Branch A B C)
  (combine : C → B → B → B)

def value : ℕ → A → B
  | 0,_ => zero
  | k+1,a => match expand a with
    | .leaf b => b
    | .fork c x y => combine c (value k x) (value k y)

def cost : ℕ → A → ℕ
  | 0,_ => 1
  | k+1,a => match expand a with
    | .leaf _ => 1
    | .fork _ x y => 2+cost k x+cost k y

def calls : ℕ → A → ℕ
  | 0,_ => 1
  | k+1,a => match expand a with
    | .leaf _ => 1
    | .fork _ x y => 1+calls k x+calls k y

def step (s : State A B C) : State A B C :=
  match s.1 with
  | [] => s
  | .call 0 _ :: w => (w,zero::s.2)
  | .call (k+1) a :: w => match expand a with
    | .leaf b => (w,b::s.2)
    | .fork c x y => (.call k x::.call k y::.join c::w,s.2)
  | .join c :: w => match s.2 with
    | y::x::v => (w,combine c x y::v)
    | _ => ([],s.2)

lemma cost_le_calls (k : ℕ) (a : A) : cost expand k a≤2*calls expand k a := by
  induction k generalizing a with
  | zero => simp [cost,calls]
  | succ k ih =>
    simp only [cost,calls]
    cases h : expand a with
    | leaf b => simp
    | fork c x y => dsimp only; have h₁ := ih x; have h₂ := ih y; omega

lemma runs (k : ℕ) (a : A) (w : List (Command A C)) (v : List B) :
    (step zero expand combine)^[cost expand k a] (.call k a::w,v)=
      (w,value zero expand combine k a::v) := by
  induction k generalizing a w v with
  | zero => simp [cost,step,value]
  | succ k ih =>
    cases h : expand a with
    | leaf b => simp [cost,step,value,h]
    | fork c x y =>
      rw [cost,h]
      dsimp only
      have he : 2+cost expand k x+cost expand k y=(1+cost expand k y)+cost expand k x+1 := by omega
      rw [he,Function.iterate_succ_apply]
      simp only [step,h]
      rw [Function.iterate_add_apply,ih,Function.iterate_add_apply,ih]
      simp only [Function.iterate_one,step,value,h]

lemma runs_extra (k : ℕ) (a : A) (N : ℕ) (hN : cost expand k a≤N) :
    (step zero expand combine)^[N] ([.call k a],[])=
      ([],[value zero expand combine k a]) := by
  have hn : N=(N-cost expand k a)+cost expand k a := by omega
  rw [hn,Function.iterate_add_apply,runs]
  apply Function.iterate_fixed
  rfl

end BinaryMatching.RecursiveEval
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.DenseOracle
open Finset UnitFlow CutAlgebra OddCutParity
variable {n : ℕ}

def total (c : Fin n → Fin n → ℕ) : ℕ := ∑ i, ∑ j, c i j

lemma entry_le_total (c : Fin n → Fin n → ℕ) (i j : Fin n) : c i j≤total c :=
  (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)).trans
    (single_le_sum (fun x _ => Nat.zero_le (∑ y, c x y)) (mem_univ i))

lemma source_le_total (c : Fin n → Fin n → ℕ) (a : Fin n) :
    UnitMincut.sourceCapacity c a≤total c := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ a)

lemma push_total_le (c : Fin n → Fin n → ℕ) (f : Fin n → Fin n) :
    total (push c f)≤total c := by
  calc
    _ ≤ ∑ i,∑ j,∑ u,∑ v,if f u=i ∧ f v=j then c u v else 0 := by
      apply sum_le_sum; intro i hi
      apply sum_le_sum; intro j hj
      unfold push
      split_ifs
      · exact Nat.zero_le _
      · rfl
    _ = ∑ u,∑ v,∑ i,∑ j,if f u=i ∧ f v=j then c u v else 0 := sum_four_swap _
    _ = total c := by simp [total,ite_and,Finset.sum_ite_irrel,eq_comm]

lemma contract_total_le (c : Matrix n ℕ) (f : Fin n → Fin n) :
    total (view (contract c f))≤total (view c) := by
  rw [contract_view]
  exact push_total_le _ _

lemma feasible_abs_bound (c : Fin n → Fin n → ℕ) (a z : Fin n) (b : UnitFlow.Matrix (Fin n))
    (hb : Feasible c a z b) (i j : Fin n) : (b i j).natAbs≤total c := by
  have hu : b i j≤(total c:ℤ) := (hb.capacity i j).trans (by exact_mod_cast entry_le_total c i j)
  have hl : b j i≤(total c:ℤ) := (hb.capacity j i).trans (by exact_mod_cast entry_le_total c j i)
  rw [hb.antisymm j i] at hl
  have hh : |b i j|≤(total c:ℤ) := abs_le.mpr ⟨by omega,hu⟩
  rw [←Int.natCast_natAbs] at hh
  exact_mod_cast hh

lemma flow_abs_bound (c : Matrix n ℕ) (a z : Fin n) (k : ℕ) (i j : Fin n) :
    (view (iterate c a z k) i j).natAbs≤total (view c) := by
  rw [iterate_view]
  exact feasible_abs_bound _ _ _ _ (UnitMincut.iterate_feasible _ _ _ _) _ _

lemma path_length_bound (c : Matrix n ℕ) (b : Matrix n ℤ) (a : Fin n) (k : ℕ)
    (v : Fin n) (p : List (Fin n)) (hp : (search c b a k)[v]=some p) : p.length≤n := by
  have hs := congrFun (search_view c b a k) v
  change (search c b a k)[v]=_ at hs
  rw [hs] at hp
  have hh := (ResidualSearch.good_search (UnitMincut.residual (view c) (view b)) a k).simple v p hp
  simpa only [Fintype.card_fin] using hh.length_le_card

def calls : ℕ → Matrix n ℕ → Finset (Fin n) → ℕ
  | 0,_,_ => 1
  | k+1,c,U =>
    let A := terminalCut c U
    if OddSide U A then 1 else
      match OddMincut.outside A, OddMincut.outside Aᶜ with
      | some r,some q =>
        1+calls k (contract c (contractMap A r)) (A∩U)+
          calls k (contract c (contractMap Aᶜ q)) (Aᶜ∩U)
      | _,_ => 1

lemma calls_bound (fuel : ℕ) (c : Matrix n ℕ) (U : Finset (Fin n))
    (he : Even U.card) (hU : 2≤U.card) (hbound : U.card≤fuel) :
    calls fuel c U≤U.card-1 := by
  induction fuel generalizing c U with
  | zero => omega
  | succ k ih =>
    let A := terminalCut c U
    obtain ⟨hsep,_⟩ := TerminalMincut.terminalCut_correct (view c) U hU
    rw [←terminalCut_eq] at hsep
    change TerminalMincut.Separates U A at hsep
    by_cases hodd : OddSide U A
    · have hcall : calls (k+1) c U=1 := by
        rw [calls]
        change (if OddSide U A then 1 else _)=1
        exact ite_eq_left hodd
      rw [hcall]; omega
    · have heA : Even (A∩U).card := by
        simp only [OddSide,Nat.odd_iff] at hodd
        rw [Nat.even_iff]; omega
      have heB := even_other U A he heA
      obtain ⟨hposA,hposB⟩ := separate_cards U A hsep
      have hpart := terminal_partition U A
      have htwoA : 2≤(A∩U).card := by rw [Nat.even_iff] at heA; omega
      have htwoB : 2≤(Aᶜ∩U).card := by rw [Nat.even_iff] at heB; omega
      have hboundA : (A∩U).card≤k := by omega
      have hboundB : (Aᶜ∩U).card≤k := by omega
      rw [calls]
      change (if OddSide U A then 1 else _ )≤_
      rw [ite_eq_right hodd]
      split
      · rename_i r q hr hq
        have h₁ := ih (contract c (contractMap A r)) (A∩U) heA htwoA hboundA
        have h₂ := ih (contract c (contractMap Aᶜ q)) (Aᶜ∩U) heB htwoB hboundB
        change 1+calls k (contract c (contractMap A r)) (A∩U)+
          calls k (contract c (contractMap Aᶜ q)) (Aᶜ∩U)≤U.card-1
        omega
      · omega

lemma initial_total_bound (G : Input) (j : ℕ) :
    total (Algorithm.capacities (Algorithm.iterate G j).numerators)≤G.n^2*Algorithm.D₀ G := by
  have hh (i k : Fin G.n) : Algorithm.capacities (Algorithm.iterate G j).numerators i k≤Algorithm.D₀ G := by
    unfold Algorithm.capacities
    split_ifs with hik hki
    · have hb := (Algorithm.iterate_box G j ⟨(i,k),hik⟩).2
      exact Int.toNat_le.mpr (by simpa only [Algorithm.entry] using hb)
    · have hb := (Algorithm.iterate_box G j ⟨(k,i),hki⟩).2
      exact Int.toNat_le.mpr (by simpa only [Algorithm.entry] using hb)
    · exact Nat.zero_le _
  calc
    _ ≤ ∑ _i : Fin G.n,∑ _k : Fin G.n,Algorithm.D₀ G :=
      sum_le_sum fun i _ => sum_le_sum fun k _ => hh i k
    _ = _ := by simp; ring

end BinaryMatching.DenseOracle
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw
open RecursiveEval
abbrev OddArg := Matrix ℕ×Cut
abbrev OddJoin := Matrix ℕ×(Cut×(ℕ×ℕ))

def oddExpand (n : ℕ) (a : OddArg) : Branch OddArg Cut OddJoin :=
  let A := terminalCut n a.1 a.2
  if cardinal (inter n A a.2)%2=1 then .leaf A else
    match outside n A,outside n (compl n A) with
    | some r,some q => .fork (a.1,(A,(r,q)))
        (contract n a.1 A r,inter n A a.2)
        (contract n a.1 (compl n A) q,inter n (compl n A) a.2)
    | _,_ => .leaf (empty n)
def oddCombine (n : ℕ) (c : OddJoin) (X Y : Cut) : Cut :=
  cheaper n c.1 (lift n c.2.1 c.2.2.1 X) (lift n (compl n c.2.1) c.2.2.2 Y)
def oddValue (n k : ℕ) (a : OddArg) : Cut :=
  value (empty n) (oddExpand n) (oddCombine n) k a

theorem oddValue_rep {n : ℕ} (k : ℕ) (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) :
    oddValue n k (matrixRep c,cutRep U)=cutRep (OddMincut.recurse k c U) := by
  induction k generalizing c U with
  | zero => exact empty_rep _
  | succ k ih =>
    simp only [oddValue,value,oddExpand,terminalCut_rep,inter_rep,cardinal_rep,compl_rep,outside_rep,
      OddMincut.recurse,OddCutParity.OddSide,Nat.odd_iff]
    split_ifs with hodd
    · rfl
    · cases hr : OddMincut.outside (TerminalMincut.terminalCut c U) <;>
        cases hq : OddMincut.outside (TerminalMincut.terminalCut c U)ᶜ <;>
        simp only [Option.map_none,Option.map_some,contract_rep]
      · exact empty_rep _
      · exact empty_rep _
      · exact empty_rep _
      · rename_i r q
        change oddCombine n (matrixRep c,(cutRep (TerminalMincut.terminalCut c U),(r.val,q.val)))
          (oddValue n k (matrixRep _,cutRep _)) (oddValue n k (matrixRep _,cutRep _))=_
        rw [ih,ih]
        simp only [oddCombine,compl_rep,lift_rep,cheaper_rep]

theorem oddCalls_rep {n : ℕ} (k : ℕ) (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) :
    calls (oddExpand n) k (matrixRep c,cutRep U)=
      DenseOracle.calls k (DenseOracle.make c) U := by
  induction k generalizing c U with
  | zero => rfl
  | succ k ih =>
    simp only [calls,oddExpand,terminalCut_rep,inter_rep,cardinal_rep,compl_rep,outside_rep,
      DenseOracle.calls,DenseOracle.terminalCut_eq,DenseOracle.view_make,OddCutParity.OddSide,Nat.odd_iff]
    split_ifs with hodd
    · rfl
    · cases hr : OddMincut.outside (TerminalMincut.terminalCut c U) <;>
        cases hq : OddMincut.outside (TerminalMincut.terminalCut c U)ᶜ <;>
        simp only [Option.map_none,Option.map_some,contract_rep]
      all_goals simp only [ih,DenseOracle.contract,DenseOracle.view_make]

theorem oddCost_bound {n : ℕ} (c : Fin n → Fin n → ℕ) (U : Finset (Fin n))
    (he : Even U.card) (hU : 2≤U.card) :
    cost (oddExpand n) U.card (matrixRep c,cutRep U)≤2*n := by
  have hb := DenseOracle.calls_bound U.card (DenseOracle.make c) U he hU le_rfl
  rw [←oddCalls_rep] at hb
  have hc := cost_le_calls (oddExpand n) U.card (matrixRep c,cutRep U)
  have hu := Finset.card_le_univ U
  simp only [Fintype.card_fin] at hu
  omega
end BinaryMatching.Raw
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.RecursiveEval
open StackCode

def branchRepr {A B C : Type} : Branch A B C → Sum B (C×(A×A))
  | .leaf b => .inl b
  | .fork c x y => .inr (c,(x,y))
def commandRepr {A C : Type} : Command A C → Sum (ℕ×A) C
  | .call k a => .inl (k,a)
  | .join c => .inr c
instance {A B C : Type} [Coding A] [Coding B] [Coding C] : Coding (Branch A B C) := ⟨fun b => encode (branchRepr b)⟩
instance {A C : Type} [Coding A] [Coding C] : Coding (Command A C) := ⟨fun c => encode (commandRepr c)⟩
instance {A C : Type} [Inhabited A] : Inhabited (Command A C) := ⟨.call 0 default⟩

namespace Compile
open StackCode.Poly
variable {A B C D P : Type} [Coding A] [Coding B] [Coding C] [Coding D] [Coding P]
@[fun_prop] theorem leaf_poly : Poly (Branch.leaf : B → Branch A B C) :=
  (Poly.sumInl (β := C×(A×A))).reindex Branch.leaf id (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem fork_poly : Poly (fun z : C×(A×A) => Branch.fork z.1 z.2.1 z.2.2 : C×(A×A) → Branch A B C) :=
  (Poly.sumInr (α := B)).reindex (fun z : C×(A×A) => Branch.fork z.1 z.2.1 z.2.2) id (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem call_poly : Poly (fun z : ℕ×A => Command.call z.1 z.2 : ℕ×A → Command A C) :=
  (Poly.sumInl (β := C)).reindex (fun z : ℕ×A => Command.call z.1 z.2) id (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem join_poly : Poly (Command.join : C → Command A C) :=
  (Poly.sumInr (α := ℕ×A)).reindex Command.join id (fun _ => rfl) (fun _ => rfl)

@[fun_prop] theorem branchCasesWith [Inhabited A] [Inhabited B] [Inhabited C]
    (p : P → Branch A B C) (f : P×B → D) (g : P×(C×(A×A)) → D)
    (hp : Poly p) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => match p a with | .leaf b => f (a,b) | .fork c x y => g (a,(c,(x,y)))) := by
  have hr : Poly (fun a => branchRepr (p a)) :=
    hp.reindex (fun a => branchRepr (p a)) id (fun _ => rfl) (fun _ => rfl)
  let repr : Sum B (C×(A×A)) → List B×List (C×(A×A)) :=
    fun x => match x with | .inl b => ([b],[]) | .inr c => ([],[c])
  have hc : Poly repr := Poly.identity.reindex repr repr (fun x => by cases x <;> rfl) (fun _ => rfl)
  have h : Poly (fun a => if (repr (branchRepr (p a))).1.isEmpty then
      g (a,(repr (branchRepr (p a))).2.headD default) else
      f (a,(repr (branchRepr (p a))).1.headD default)) := by fun_prop
  exact h.congr (fun a => by cases p a <;> rfl)

@[fun_prop] theorem commandCasesWith [Inhabited A] [Inhabited C]
    (p : P → Command A C) (f : P×(ℕ×A) → D) (g : P×C → D)
    (hp : Poly p) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => match p a with | .call k x => f (a,(k,x)) | .join c => g (a,c)) := by
  have hr : Poly (fun a => commandRepr (p a)) :=
    hp.reindex (fun a => commandRepr (p a)) id (fun _ => rfl) (fun _ => rfl)
  let repr : Sum (ℕ×A) C → List (ℕ×A)×List C :=
    fun x => match x with | .inl b => ([b],[]) | .inr c => ([],[c])
  have hc : Poly repr := Poly.identity.reindex repr repr (fun x => by cases x <;> rfl) (fun _ => rfl)
  have h : Poly (fun a => if (repr (commandRepr (p a))).1.isEmpty then
      g (a,(repr (commandRepr (p a))).2.headD default) else
      f (a,(repr (commandRepr (p a))).1.headD default)) := by fun_prop
  exact h.congr (fun a => by cases p a <;> rfl)
end Compile
end BinaryMatching.RecursiveEval
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.RecursiveEval
open StackCode
variable {A B C : Type}

def CommandGood (K : ℕ) (PA : A → Prop) (PC : C → Prop) : Command A C → Prop
  | .call k a => k≤K ∧ PA a
  | .join c => PC c

def StateGood (K : ℕ) (PA : A → Prop) (PB : B → Prop) (PC : C → Prop) (s : State A B C) : Prop :=
  (∀ c∈s.1,CommandGood K PA PC c) ∧ (∀ b∈s.2,PB b)

lemma step_good (zero : B) (expand : A → Branch A B C) (combine : C → B → B → B)
    (K : ℕ) (PA : A → Prop) (PB : B → Prop) (PC : C → Prop)
    (hz : PB zero)
    (he : ∀ a,PA a → match expand a with | .leaf b => PB b | .fork c x y => PC c ∧ PA x ∧ PA y)
    (hc : ∀ c,PC c → ∀ x,PB x → ∀ y,PB y → PB (combine c x y))
    (s : State A B C) (hs : StateGood K PA PB PC s) :
    StateGood K PA PB PC (step zero expand combine s) := by
  rcases s with ⟨w,v⟩
  rcases hs with ⟨hw,hv⟩
  cases w with
  | nil => exact ⟨hw,hv⟩
  | cons cmd w =>
    have hw' : ∀ c∈w,CommandGood K PA PC c := fun c h => hw c (List.mem_cons_of_mem _ h)
    have hcmd := hw cmd List.mem_cons_self
    cases cmd with
    | call k a =>
      rcases hcmd with ⟨hk,ha⟩
      cases k with
      | zero =>
        exact ⟨hw',by simpa only [step,List.mem_cons,forall_eq_or_imp] using And.intro hz hv⟩
      | succ k =>
        have hh := he a ha
        cases h : expand a with
        | leaf b =>
          simp only [h] at hh
          simp only [step,h,StateGood]
          exact ⟨hw',by simpa only [List.mem_cons,forall_eq_or_imp] using And.intro hh hv⟩
        | fork c x y =>
          simp only [h] at hh
          simp only [step,h,StateGood]
          refine ⟨?_,hv⟩
          intro d hd
          simp only [List.mem_cons] at hd
          rcases hd with rfl|rfl|rfl|hd
          · exact ⟨by omega,hh.2.1⟩
          · exact ⟨by omega,hh.2.2⟩
          · exact hh.1
          · exact hw' d hd
    | join c =>
      cases v with
      | nil => exact ⟨by simp [step],hv⟩
      | cons y v =>
        cases v with
        | nil => exact ⟨by simp [step],hv⟩
        | cons x v =>
          simp only [step,StateGood]
          refine ⟨hw',?_⟩
          intro b hb
          rcases List.mem_cons.mp hb with rfl|hb
          · exact hc c hcmd x (hv x (by simp)) y (hv y (by simp))
          · exact hv b (by simp [hb])

lemma step_length (zero : B) (expand : A → Branch A B C) (combine : C → B → B → B)
    (s : State A B C) :
    (step zero expand combine s).1.length+(step zero expand combine s).2.length ≤ s.1.length+s.2.length+2 := by
  rcases s with ⟨w,v⟩
  cases w with
  | nil => simp [step]
  | cons cmd w =>
    cases cmd with
    | call k a =>
      cases k with
      | zero => simp [step]; omega
      | succ k => cases h : expand a <;> simp [step,h] <;> omega
    | join c => cases v with
      | nil => simp [step]
      | cons y v => cases v <;> simp [step]; omega

lemma iterate_length (zero : B) (expand : A → Branch A B C) (combine : C → B → B → B)
    (s : State A B C) (j : ℕ) :
    ((step zero expand combine)^[j] s).1.length+((step zero expand combine)^[j] s).2.length ≤ s.1.length+s.2.length+2*j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hh := step_length zero expand combine ((step zero expand combine)^[j] s)
    omega

lemma iterate_good (zero : B) (expand : A → Branch A B C) (combine : C → B → B → B)
    (K : ℕ) (PA : A → Prop) (PB : B → Prop) (PC : C → Prop)
    (hz : PB zero)
    (he : ∀ a,PA a → match expand a with | .leaf b => PB b | .fork c x y => PC c ∧ PA x ∧ PA y)
    (hc : ∀ c,PC c → ∀ x,PB x → ∀ y,PB y → PB (combine c x y))
    (s : State A B C) (hs : StateGood K PA PB PC s) (j : ℕ) :
    StateGood K PA PB PC ((step zero expand combine)^[j] s) := by
  induction j with
  | zero => exact hs
  | succ j ih => rw [Function.iterate_succ_apply']; exact step_good zero expand combine K PA PB PC hz he hc _ ih

lemma code_call {A C : Type} [Coding A] [Coding C] (k : ℕ) (a : A) :
    (encode (Command.call k a : Command A C)).length=8*k+4*(encode a).length+7 := by
  change (pairBits (pairBits (pairBits (encode k) (encode a)) []) []).length=_
  simp only [pairBits_length,List.length_nil,code_nat_length]
  omega
lemma code_join {A C : Type} [Coding A] [Coding C] (c : C) :
    (encode (Command.join c : Command A C)).length=2*(encode c).length+2 := by
  change (pairBits [] (pairBits (encode c) [])).length=_
  simp only [pairBits_length,List.length_nil]
  omega

lemma state_code_bound [Coding A] [Coding B] [Coding C] (s : State A B C) (M : ℕ)
    (hw : ∀ c∈s.1,(encode c).length≤M) (hv : ∀ b∈s.2,(encode b).length≤M) :
    (encode s).length≤2*(s.1.length+s.2.length)*(2*M+1)+1 := by
  have h₁ := list_code_bound s.1 M hw
  have h₂ := list_code_bound s.2 M hv
  rw [code_pair_length]
  nlinarith
end BinaryMatching.RecursiveEval
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.RecursiveEval
open StackCode
variable {A B C P : Type}

def paramStep (zero : P → B) (expand : P → A → Branch A B C)
    (combine : P → C → B → B → B) (z : P×State A B C) : P×State A B C :=
  (z.1,step (zero z.1) (expand z.1) (combine z.1) z.2)

lemma paramStep_iterate (zero : P → B) (expand : P → A → Branch A B C)
    (combine : P → C → B → B → B) (z : P×State A B C) (k : ℕ) :
    (paramStep zero expand combine)^[k] z=
      (z.1,(step (zero z.1) (expand z.1) (combine z.1))^[k] z.2) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply',ih,paramStep]

namespace Compile
open StackCode.Poly
variable [Coding A] [Coding B] [Coding C] [Coding P]
  [Inhabited A] [Inhabited B] [Inhabited C]

def execCommand (zero : P → B) (expand : P → A → Branch A B C)
    (combine : P → C → B → B → B) (z : (P×State A B C)×Command A C) : State A B C :=
  match z.2 with
  | .call k a => if k=0 then (z.1.2.1.tail,zero z.1.1::z.1.2.2) else
    match expand z.1.1 a with
    | .leaf b => (z.1.2.1.tail,b::z.1.2.2)
    | .fork c x y => (.call (k-1) x::.call (k-1) y::.join c::z.1.2.1.tail,z.1.2.2)
  | .join c => if 2≤z.1.2.2.length then
      (z.1.2.1.tail,combine z.1.1 c (z.1.2.2.tail.headD default) (z.1.2.2.headD default)::z.1.2.2.tail.tail)
    else ([],z.1.2.2)

@[fun_prop] theorem execCommand_poly (zero : P → B) (expand : P → A → Branch A B C)
    (combine : P → C → B → B → B) (hz : Poly zero)
    (he : Poly (fun z : P×A => expand z.1 z.2))
    (hc : Poly (fun z : P×(C×(B×B)) => combine z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Poly (execCommand zero expand combine) := by
  unfold execCommand
  apply commandCasesWith Prod.snd
    (fun z : ((P×State A B C)×Command A C)×(ℕ×A) =>
      if z.2.1=0 then (z.1.1.2.1.tail,zero z.1.1.1::z.1.1.2.2) else
      match expand z.1.1.1 z.2.2 with
      | .leaf b => (z.1.1.2.1.tail,b::z.1.1.2.2)
      | .fork c x y => (.call (z.2.1-1) x::.call (z.2.1-1) y::.join c::z.1.1.2.1.tail,z.1.1.2.2))
    (fun z => if 2≤z.1.1.2.2.length then
      (z.1.1.2.1.tail,combine z.1.1.1 z.2 (z.1.1.2.2.tail.headD default) (z.1.1.2.2.headD default)::z.1.1.2.2.tail.tail)
      else ([],z.1.1.2.2))
  · fun_prop
  · have hb₀ := branchCasesWith
      (fun z : ((P×State A B C)×Command A C)×(ℕ×A) => expand z.1.1.1 z.2.2)
      (fun z => (z.1.1.1.2.1.tail,z.2::z.1.1.1.2.2))
      (fun z => (Command.call (z.1.2.1-1) z.2.2.1::Command.call (z.1.2.1-1) z.2.2.2::
        Command.join z.2.1::z.1.1.1.2.1.tail,z.1.1.1.2.2))
      (by fun_prop) (by fun_prop) (by fun_prop)
    have hb : Poly (fun z : ((P×State A B C)×Command A C)×(ℕ×A) =>
        match expand z.1.1.1 z.2.2 with
        | .leaf b => (z.1.1.2.1.tail,b::z.1.1.2.2)
        | .fork c x y => (.call (z.2.1-1) x::.call (z.2.1-1) y::.join c::z.1.1.2.1.tail,z.1.1.2.2)) :=
      hb₀.congr (fun z => by cases expand z.1.1.1 z.2.2 <;> rfl)
    have h : Poly (fun z : ((P×State A B C)×Command A C)×(ℕ×A) =>
        if decide (z.2.1=0) then (z.1.1.2.1.tail,zero z.1.1.1::z.1.1.2.2) else
        match expand z.1.1.1 z.2.2 with
        | .leaf b => (z.1.1.2.1.tail,b::z.1.1.2.2)
        | .fork c x y => (.call (z.2.1-1) x::.call (z.2.1-1) y::.join c::z.1.1.2.1.tail,z.1.1.2.2)) := by fun_prop
    exact h.congr (fun _ => by simp)
  · have h : Poly (fun z : ((P×State A B C)×Command A C)×C => if decide (2≤z.1.1.2.2.length) then
        (z.1.1.2.1.tail,combine z.1.1.1 z.2 (z.1.1.2.2.tail.headD default) (z.1.1.2.2.headD default)::z.1.1.2.2.tail.tail)
        else ([],z.1.1.2.2)) := by fun_prop
    exact h.congr (fun _ => by simp)

@[fun_prop] theorem paramStep_poly (zero : P → B) (expand : P → A → Branch A B C)
    (combine : P → C → B → B → B) (hz : Poly zero)
    (he : Poly (fun z : P×A => expand z.1 z.2))
    (hc : Poly (fun z : P×(C×(B×B)) => combine z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Poly (paramStep zero expand combine) := by
  have hx := execCommand_poly zero expand combine hz he hc
  have h : Poly (fun z : P×State A B C =>
      (z.1,if z.2.1.isEmpty then z.2 else execCommand zero expand combine (z,z.2.1.headD default))) := by fun_prop
  apply h.congr
  intro z
  rcases z with ⟨p,w,v⟩
  unfold paramStep
  cases w with
  | nil => rfl
  | cons a w =>
    cases a with
    | call k a =>
      cases k <;> rfl
    | join c =>
      cases v with
      | nil => simp [execCommand,step]
      | cons b v => cases v <;> simp [execCommand,step]
end Compile
end BinaryMatching.RecursiveEval
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw
open StackCode RecursiveEval

def ArgGood (n B : ℕ) (a : OddArg) : Prop :=
  ∃ (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)),a=(matrixRep c,cutRep U) ∧ DenseOracle.total c≤B
def CutGood (n : ℕ) (S : Cut) : Prop := ∃ U : Finset (Fin n),S=cutRep U
def JoinGood (n B : ℕ) (a : OddJoin) : Prop :=
  ∃ (c : Fin n → Fin n → ℕ) (A : Finset (Fin n)) (r q : Fin n),
    a=(matrixRep c,(cutRep A,(r.val,q.val))) ∧ DenseOracle.total c≤B

lemma oddExpand_good (n B : ℕ) (a : OddArg) (ha : ArgGood n B a) :
    match oddExpand n a with
    | .leaf S => CutGood n S
    | .fork c x y => JoinGood n B c ∧ ArgGood n B x ∧ ArgGood n B y := by
  obtain ⟨c,U,rfl,hc⟩ := ha
  simp only [oddExpand,terminalCut_rep,inter_rep,cardinal_rep,compl_rep,outside_rep]
  split_ifs
  · exact ⟨_,rfl⟩
  · cases hr : OddMincut.outside (TerminalMincut.terminalCut c U) <;>
      cases hq : OddMincut.outside (TerminalMincut.terminalCut c U)ᶜ <;>
      simp only [Option.map_none,Option.map_some,contract_rep]
    · exact ⟨_,empty_rep _⟩
    · exact ⟨_,empty_rep _⟩
    · exact ⟨_,empty_rep _⟩
    · rename_i r q
      refine ⟨⟨c,_,r,q,rfl,hc⟩,⟨_,_,rfl,?_⟩,⟨_,_,rfl,?_⟩⟩ <;>
        exact (DenseOracle.push_total_le _ _).trans hc

lemma oddCombine_good (n B : ℕ) (c : OddJoin) (hc : JoinGood n B c)
    (X : Cut) (hX : CutGood n X) (Y : Cut) (hY : CutGood n Y) : CutGood n (oddCombine n c X Y) := by
  obtain ⟨c,A,r,q,rfl,hc⟩ := hc
  obtain ⟨X,rfl⟩ := hX
  obtain ⟨Y,rfl⟩ := hY
  simp only [oddCombine,compl_rep,lift_rep,cheaper_rep]
  exact ⟨_,rfl⟩

lemma vectorRep_code_bound {α : Type} [Coding α] {n : ℕ} (f : Fin n → α) (M : ℕ)
    (h : ∀ i,(encode (f i)).length≤M) :
    (encode (vectorRep f)).length≤n*(2*M+1) := by
  have hh := list_code_bound (vectorRep f) M (by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact h i)
  simpa only [vectorRep,List.length_ofFn] using hh

lemma matrixRep_code_bound {n : ℕ} (c : Fin n → Fin n → ℕ) (B : ℕ)
    (h : DenseOracle.total c≤B) : (encode (matrixRep c)).length≤n*(2*(n*(2*B+1))+1) := by
  apply vectorRep_code_bound
  intro i
  apply vectorRep_code_bound
  intro j
  simpa only [code_nat_length] using (DenseOracle.entry_le_total c i j).trans h

lemma cutRep_code_length {n : ℕ} (S : Finset (Fin n)) : (encode (cutRep S)).length=3*n := by
  rw [cut_code_length]
  simp only [cutRep,vectorRep,List.length_ofFn]

def oddWordBound (n B : ℕ) : ℕ := 1000*(n+1)^2*(B+1)
def oddBudget (n B : ℕ) : ℕ := 100000*(n+1)^3*(B+1)

lemma arg_code_bound (n B : ℕ) (a : OddArg) (ha : ArgGood n B a) :
    (encode a).length≤100*(n+1)^2*(B+1) := by
  obtain ⟨c,U,rfl,hc⟩ := ha
  have hh := matrixRep_code_bound c B hc
  simp only [code_pair_length,cutRep_code_length]
  calc
    _ ≤ 2*(n*(2*(n*(2*B+1))+1))+3*n+1 := by omega
    _ ≤ _ := by ring_nf; omega
lemma join_code_bound (n B : ℕ) (a : OddJoin) (ha : JoinGood n B a) :
    (encode a).length≤100*(n+1)^2*(B+1) := by
  obtain ⟨c,A,r,q,rfl,hc⟩ := ha
  have hh := matrixRep_code_bound c B hc
  have hr := r.isLt
  have hq := q.isLt
  simp only [code_pair_length,cutRep_code_length,code_nat_length]
  calc
    _ ≤ 2*(n*(2*(n*(2*B+1))+1))+9*n+3 := by omega
    _ ≤ _ := by ring_nf; omega

lemma command_code_bound (n B : ℕ) (c : Command OddArg OddJoin)
    (hc : CommandGood n (ArgGood n B) (JoinGood n B) c) : (encode c).length≤oddWordBound n B := by
  cases c with
  | call k a =>
    obtain ⟨hk,ha⟩ := hc
    have hh := arg_code_bound n B a ha
    rw [code_call]
    unfold oddWordBound
    calc
      _ ≤ 8*n+4*(100*(n+1)^2*(B+1))+7 := by omega
      _ ≤ _ := by ring_nf; omega
  | join c =>
    have hh := join_code_bound n B c hc
    rw [code_join]
    unfold oddWordBound
    calc
      _ ≤ 2*(100*(n+1)^2*(B+1))+2 := by omega
      _ ≤ _ := by ring_nf; omega
lemma cut_code_bound (n B : ℕ) (S : Cut) (hS : CutGood n S) : (encode S).length≤oddWordBound n B := by
  obtain ⟨S,rfl⟩ := hS
  rw [cutRep_code_length]
  unfold oddWordBound
  ring_nf
  omega

lemma oddOrbit_bound {n : ℕ} (c : Fin n → Fin n → ℕ) (U : Finset (Fin n))
    (B : ℕ) (hB : DenseOracle.total c≤B) (j : ℕ) (hj : j≤2*n) :
    (encode ((paramStep empty oddExpand oddCombine)^[j]
      (n,([Command.call U.card (matrixRep c,cutRep U)],[])))).length≤oddBudget n B := by
  rw [paramStep_iterate]
  dsimp only
  have hz : CutGood n (empty n) := ⟨_,empty_rep _⟩
  have hU : U.card≤n := by simpa only [Fintype.card_fin] using Finset.card_le_univ U
  have hgood : StateGood n (ArgGood n B) (CutGood n) (JoinGood n B)
      ([Command.call U.card (matrixRep c,cutRep U)],[]) := by
    constructor
    · intro a ha
      obtain rfl := List.mem_singleton.mp ha
      exact ⟨hU,⟨c,U,rfl,hB⟩⟩
    · simp
  have hg := iterate_good (empty n) (oddExpand n) (oddCombine n) n (ArgGood n B) (CutGood n) (JoinGood n B)
    hz (fun a ha => by
      have hh := oddExpand_good n B a ha
      cases h : oddExpand n a <;> simpa only [h] using hh) (oddCombine_good n B) _ hgood j
  have hl := iterate_length (empty n) (oddExpand n) (oddCombine n)
    ([Command.call U.card (matrixRep c,cutRep U)],[]) j
  simp only [List.length_singleton,List.length_nil,Nat.add_zero] at hl
  have hs := state_code_bound _ (oddWordBound n B)
    (fun cmd hc => command_code_bound n B cmd (hg.1 cmd hc))
    (fun S hS => cut_code_bound n B S (hg.2 S hS))
  have hlen : ((step (empty n) (oddExpand n) (oddCombine n))^[j]
      ([Command.call U.card (matrixRep c,cutRep U)],[])).1.length+
    ((step (empty n) (oddExpand n) (oddCombine n))^[j]
      ([Command.call U.card (matrixRep c,cutRep U)],[])).2.length≤1+4*n := by omega
  have hm := Nat.add_le_add_right
    (Nat.mul_le_mul_right (2*oddWordBound n B+1) (Nat.mul_le_mul_left 2 hlen)) 1
  rw [code_pair_length,code_nat_length]
  dsimp only
  have hss := hs.trans hm
  calc
    _ ≤ 2*n+(2*(1+4*n)*(2*oddWordBound n B+1)+1)+1 := by omega
    _ ≤ oddBudget n B := by unfold oddWordBound oddBudget; ring_nf; omega
end BinaryMatching.Raw
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw
open StackCode RecursiveEval

def rawTotal (c : Matrix ℕ) : ℕ := c.flatten.sum
lemma rawTotal_rep {n : ℕ} (c : Fin n → Fin n → ℕ) : rawTotal (matrixRep c)=DenseOracle.total c := by
  simp only [rawTotal,matrixRep,vectorRep,List.sum_flatten,List.map_ofFn,List.sum_ofFn,DenseOracle.total,Function.comp_def]

def oddFlat (z : ℕ×(Matrix ℕ×Cut)) : Cut :=
  let s := ((guardedStep (paramStep empty oddExpand oddCombine))^[2*z.1]
    (oddBudget z.1 (rawTotal z.2.1),(z.1,([Command.call (cardinal z.2.2) (z.2.1,z.2.2)],[])))).2
  s.2.2.headD []

theorem oddFlat_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (U : Finset (Fin n))
    (he : Even U.card) (hU : 2≤U.card) :
    oddFlat (n,(matrixRep c,cutRep U))=cutRep (OddMincut.oddCut c U) := by
  unfold oddFlat
  simp only [rawTotal_rep,cardinal_rep]
  rw [guardedStep_eq (paramStep empty oddExpand oddCombine)
    (oddBudget n (DenseOracle.total c)) (n,([Command.call U.card (matrixRep c,cutRep U)],[])) (2*n)
    (fun j hj => oddOrbit_bound c U _ le_rfl j hj)]
  rw [paramStep_iterate]
  rw [runs_extra (empty n) (oddExpand n) (oddCombine n) U.card
    (matrixRep c,cutRep U) (2*n) (oddCost_bound c U he hU)]
  exact oddValue_rep _ c U

namespace Compiler
open StackCode.Poly RecursiveEval.Compile
@[fun_prop] theorem rawTotal_poly : Poly rawTotal := by unfold rawTotal; fun_prop
@[fun_prop] theorem oddBudget_poly : Poly (fun z : ℕ×ℕ => oddBudget z.1 z.2) := by unfold oddBudget; fun_prop
@[fun_prop] theorem oddExpand_poly : Poly (fun z : ℕ×OddArg => oddExpand z.1 z.2) := by
  let A (z : ℕ×OddArg) := terminalCut z.1 z.2.1 z.2.2
  have hA : Poly A := terminalCut_poly
  have h : Poly (fun z : ℕ×OddArg =>
      if decide (cardinal (inter z.1 (A z) z.2.2)%2=1) then Branch.leaf (A z) else
      if (outside z.1 (A z)).isSome && (outside z.1 (compl z.1 (A z))).isSome then
        Branch.fork (z.2.1,(A z,((outside z.1 (A z)).getD 0,(outside z.1 (compl z.1 (A z))).getD 0)))
          (contract z.1 z.2.1 (A z) ((outside z.1 (A z)).getD 0),inter z.1 (A z) z.2.2)
          (contract z.1 z.2.1 (compl z.1 (A z)) ((outside z.1 (compl z.1 (A z))).getD 0),inter z.1 (compl z.1 (A z)) z.2.2)
      else Branch.leaf (empty z.1) : (ℕ×OddArg) → Branch OddArg Cut OddJoin) := by fun_prop
  exact h.congr (fun z => by
    unfold oddExpand
    dsimp only [A]
    simp only [decide_eq_true_eq]
    by_cases hp : cardinal (inter z.1 (terminalCut z.1 z.2.1 z.2.2) z.2.2)%2=1
    · simp only [ite_eq_left hp]
    · simp only [ite_eq_right hp]
      cases outside z.1 (terminalCut z.1 z.2.1 z.2.2) <;>
        cases outside z.1 (compl z.1 (terminalCut z.1 z.2.1 z.2.2)) <;> rfl)
@[fun_prop] theorem oddCombine_poly : Poly (fun z : ℕ×(OddJoin×(Cut×Cut)) => oddCombine z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold oddCombine
  fun_prop
@[fun_prop] theorem oddFlat_poly : Poly oddFlat := by
  have hs := paramStep_poly empty oddExpand oddCombine rawEmpty oddExpand_poly oddCombine_poly
  have hg := Poly.guardedIterate (paramStep empty oddExpand oddCombine) hs
  have hi := Poly.comp _ (fun z : ℕ×(Matrix ℕ×Cut) =>
    (2*z.1,(oddBudget z.1 (rawTotal z.2.1),(z.1,([Command.call (cardinal z.2.2) (z.2.1,z.2.2)],[]))))) hg (by fun_prop)
  exact Poly.comp (fun s : ℕ×State OddArg Cut OddJoin => s.2.2.headD []) _ (by fun_prop) hi
end Compiler
end BinaryMatching.Raw
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw.Optimize
open Algorithm Finset
local instance : Preorder ℤ := Int.instLinearOrder.toPreorder

def capacities (n : ℕ) (a : Matrix ℤ) : Matrix ℕ :=
  matrix n (fun i j => if i < j then (get a i j).toNat else if j < i then (get a j i).toNat else 0)
lemma capacities_rep {n : ℕ} (a : Table n ℤ) :
    capacities n (tableRep a)=matrixRep (Algorithm.capacities a) := by
  apply matrix_eq_rep
  intro i j
  simp only [get_tableRep,Algorithm.capacities,Fin.lt_def]

def zeroRow (n : ℕ) : Row := (matrix n (fun _ _ => 0),0)
def degreeRow (n v : ℕ) (positive : Bool) : Row :=
  (matrix n (fun i j => if i < j then
    if i=v ∨ j=v then (if positive then 1 else -1) else 0 else 0),if positive then -1 else 1)
def cutRow (n : ℕ) (S : Cut) : Row :=
  (matrix n (fun i j => if i < j then
    if (mem S i && !mem S j) || (mem S j && !mem S i) then -1 else 0 else 0),1)
lemma zeroRow_rep (n : ℕ) : zeroRow n=rowRep (Algorithm.zeroRow (n := n)) := by
  apply Prod.ext
  · apply matrix_eq_rep
    intro i j
    simp [toTable,tabulate,Algorithm.zeroRow]
  · rfl
lemma degreeRow_rep {n : ℕ} (v : Fin n) (b : Bool) : degreeRow n v.val b=rowRep (Algorithm.degreeRow v b) := by
  apply Prod.ext
  · apply matrix_eq_rep
    intro i j
    by_cases h : i < j <;> simp [toTable,tabulate,Algorithm.degreeRow,Fin.ext_iff,h]
  · rfl
lemma cutRow_rep {n : ℕ} (S : Finset (Fin n)) : cutRow n (cutRep S)=rowRep (Algorithm.cutRow S) := by
  apply Prod.ext
  · apply matrix_eq_rep
    intro i j
    by_cases h : i < j <;> simp [toTable,tabulate,Algorithm.cutRow,h]
  · rfl

def rows (n : ℕ) (a : Matrix ℤ) : List Row :=
  zeroRow n :: ((List.range n).flatMap (fun v => [degreeRow n v true,degreeRow n v false])) ++
    [cutRow n (oddFlat (n,(capacities n a,full n)))]
lemma rows_rep {n : ℕ} (hn : 2≤n) (he : Even n) (a : Table n ℤ) :
    rows n (tableRep a)=(integralRows a).map rowRep := by
  have hu : (univ : Finset (Fin n)).card=n := Fintype.card_fin n
  unfold rows integralRows
  rw [capacities_rep,full_rep,oddFlat_rep _ _ (by simpa only [hu] using he) (by simpa only [hu] using hn)]
  simp only [zeroRow_rep,cutRow_rep,List.map_append,List.map_cons,List.map_nil,
    DenseOracle.oddCut_eq,DenseOracle.view_make]
  congr 2
  rw [range_eq_fin,List.flatMap_map,List.map_flatMap]
  congr 1
  funext v
  simp only [degreeRow_rep,List.map_cons,List.map_nil]

lemma argmax_map {α β γ : Type} [Preorder γ] [DecidableLT γ] (l : List α) (f : α → β) (g : β → γ) :
    (l.map f).argmax g=(l.argmax (g ∘ f)).map f :=
  @StackCode.argmin_map_exact α β γᵒᵈ _ _ l f g

def selectedRow (n D : ℕ) (a : Matrix ℤ) : Row :=
  ((rows n a).argmax (rowNumerator D a)).getD (zeroRow n)
lemma selectedRow_rep {n : ℕ} (hn : 2≤n) (he : Even n) (D : ℕ) (a : Table n ℤ) :
    selectedRow n D (tableRep a)=rowRep (integralRow D a) := by
  unfold selectedRow integralRow
  rw [rows_rep hn he,argmax_map]
  have hf : rowNumerator D (tableRep a) ∘ rowRep=Algorithm.rowNumerator D a := by
    funext r
    exact rowNumerator_rep D a r
  rw [hf]
  cases h : (integralRows a).argmax (Algorithm.rowNumerator D a) with
  | none => exact zeroRow_rep n
  | some r => rfl
end BinaryMatching.Raw.Optimize
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Algorithm
open Finset
variable {n : ℕ}
private lemma int_two_abs : (2:ℤ).natAbs=2 := rfl

lemma beta_abs_nat (G : Input) (e : Pair G.n) : (beta G e).natAbs ≤ L G := by
  have h := beta_bound G e
  have h' : |beta G e| ≤ (L G:ℤ) := by exact_mod_cast h
  rw [←Int.natCast_natAbs] at h'
  exact_mod_cast h'

lemma indexed_slope_abs (k j : ℕ) (hj : j ≤ k) : (indexedPiece k j).slope.natAbs ≤ k := by
  have hm : indexedPiece k j∈pieces k := by
    rw [pieces_indexed]
    exact List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),rfl⟩
  have h := piece_slope_bound k _ hm
  have h' : |(indexedPiece k j).slope| ≤ (k:ℤ) := by exact_mod_cast h
  rw [←Int.natCast_natAbs] at h'
  exact_mod_cast h'

lemma pieceNumerator_abs (k D j : ℕ) (hj : j ≤ k) (a : ℤ) (ha : a.natAbs ≤ D) :
    (pieceNumerator k D a j).natAbs ≤ (k+1)*D*2^k := by
  have hs := indexed_slope_abs k j hj
  have hp : 2^(k-j) ≤ 2^k := Nat.pow_le_pow_right (by omega) (Nat.sub_le k j)
  unfold pieceNumerator
  refine (Int.natAbs_add_le _ _).trans ?_
  simp only [Int.natAbs_mul,Int.natAbs_pow,int_two_abs]
  split_ifs
  · have h₁ := Nat.mul_le_mul_right (2^k) (Nat.mul_le_mul hs ha)
    have h₂ := Nat.mul_le_mul_left D hp
    simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast,int_two_abs]
    nlinarith
  · simpa only [Int.natAbs_zero,Nat.add_zero] using
      (Nat.mul_le_mul_right (2^k) (Nat.mul_le_mul (hs.trans (Nat.le_succ k)) ha))

lemma integralRow_mem (D : ℕ) (a : Table n ℤ) : integralRow D a∈integralRows a := by
  unfold integralRow
  cases h : (integralRows a).argmax (rowNumerator D a) with
  | none => simp [integralRows]
  | some r => exact List.argmax_mem h

lemma integral_row_coeff (a : Table n ℤ) (r : Affine n) (hr : r∈integralRows a)
    (e : Pair n) : (r.coeff e).natAbs ≤ 1 := by
  rw [integralRows_eq] at hr
  rcases (mem_activeRows a r).mp hr with rfl|⟨v,rfl|rfl⟩|rfl
  · simp [zeroRow]
  · simp only [degreeRow,↓reduceIte]; split_ifs <;> norm_num
  · simp only [degreeRow,Bool.false_eq_true,↓reduceIte]; split_ifs <;> norm_num
  · simp only [cutRow]; split_ifs <;> norm_num

lemma integral_row_constant (a : Table n ℤ) (r : Affine n) (hr : r∈integralRows a) :
    r.constant.natAbs ≤ 1 := by
  rw [integralRows_eq] at hr
  rcases (mem_activeRows a r).mp hr with rfl|⟨v,rfl|rfl⟩|rfl <;>
    simp [zeroRow,degreeRow,cutRow]

lemma rowNumerator_abs (D : ℕ) (a : Table n ℤ) (ha : ∀ e,(entry a e).natAbs ≤ D)
    (r : Affine n) (hr : r∈integralRows a) : (rowNumerator D a r).natAbs ≤ (q n+1)*D := by
  have hs : (∑ e,r.coeff e*entry a e).natAbs ≤ q n*D := by
    calc
      _  ≤  ∑ e,(r.coeff e*entry a e).natAbs := Int.natAbs_sum_le _ _
      _  ≤  ∑ _e : Pair n,D := sum_le_sum fun e _ => by
        rw [Int.natAbs_mul]
        simpa using Nat.mul_le_mul (integral_row_coeff a r hr e) (ha e)
      _ = _ := by simp [q]
  have hc : (r.constant*(D:ℤ)).natAbs ≤ D := by
    rw [Int.natAbs_mul,Int.natAbs_natCast]
    simpa using Nat.mul_le_mul_right D (integral_row_constant a r hr)
  exact (Int.natAbs_add_le _ _).trans (by nlinarith)

lemma scaledPsi_abs (k D : ℕ) (a : ℤ) (ha : a.natAbs ≤ D) :
    (scaledPsi k D a).natAbs ≤ (k+1)*D*2^k :=
  pieceNumerator_abs k D _ (selectedIndex_le k D a) a ha

lemma scaledSlope_abs (k D : ℕ) (a : ℤ) : (scaledSlope k D a).natAbs ≤ k :=
  indexed_slope_abs k _ (selectedIndex_le k D a)

def operandBound (G : Input) : ℕ :=
  Q G*(q G.n*(K G.n+L G+1)+M₀ G*(q G.n+1))

lemma integralValue_abs (G : Input) (a : Table G.n ℤ)
    (ha : ∀ e,(entry a e).natAbs ≤ D₀ G) (r : Affine G.n) (hr : r∈integralRows a) :
    (integralValue G a r).natAbs ≤ operandBound G := by
  have he (e : Pair G.n) :
      (scaledPsi (K G.n) (D₀ G) (entry a e)+beta G e*entry a e*2^(K G.n)).natAbs
         ≤ (K G.n+L G+1)*Q G := by
    have h₁ := scaledPsi_abs (K G.n) (D₀ G) (entry a e) (ha e)
    have h₂ : (beta G e*entry a e*2^(K G.n)).natAbs ≤ L G*Q G := by
      simp only [Int.natAbs_mul,Int.natAbs_pow,int_two_abs]
      calc
        _  ≤  L G*D₀ G*2^(K G.n) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (beta_abs_nat G e) (ha e))
        _ = _ := by unfold Q; ring
    exact (Int.natAbs_add_le _ _).trans (by unfold Q at *; nlinarith)
  have hs : (∑ e,(scaledPsi (K G.n) (D₀ G) (entry a e)+beta G e*entry a e*2^(K G.n))).natAbs
       ≤ q G.n*((K G.n+L G+1)*Q G) := by
    calc
      _ ≤ ∑ e,(scaledPsi (K G.n) (D₀ G) (entry a e)+beta G e*entry a e*2^(K G.n)).natAbs :=
        Int.natAbs_sum_le _ _
      _ ≤ ∑ _e : Pair G.n,(K G.n+L G+1)*Q G := sum_le_sum (fun e _ => he e)
      _ = _ := by simp only [sum_const,card_univ,smul_eq_mul,q]
  have hc : ((M₀ G:ℤ)*rowNumerator (D₀ G) a r*2^(K G.n)).natAbs ≤ M₀ G*(q G.n+1)*Q G := by
    simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast,int_two_abs]
    calc
      _  ≤  M₀ G*((q G.n+1)*D₀ G)*2^(K G.n) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (rowNumerator_abs _ a ha r hr))
      _ = _ := by unfold Q; ring
  exact (Int.natAbs_sub_le _ _).trans (by unfold operandBound; nlinarith)

lemma integralGradient_abs (G : Input) (a : Table G.n ℤ) (r : Affine G.n)
    (hr : r∈integralRows a) (e : Pair G.n) :
    (integralGradient G a r e).natAbs ≤ K G.n+L G+M₀ G := by
  have h₁ := scaledSlope_abs (K G.n) (D₀ G) (entry a e)
  have h₂ := beta_abs_nat G e
  have h₃ : ((M₀ G:ℤ)*r.coeff e).natAbs ≤ M₀ G := by
    rw [Int.natAbs_mul,Int.natAbs_natCast]
    simpa using Nat.mul_le_mul_left (M₀ G) (integral_row_coeff a r hr e)
  exact (Int.natAbs_sub_le _ _).trans (by
    have hh := Int.natAbs_add_le (scaledSlope (K G.n) (D₀ G) (entry a e)) (beta G e)
    omega)

lemma integralIterate_abs (G : Input) (hn : 2 ≤ G.n) (t : ℕ) (e : Pair G.n) :
    (entry (integralIterate G t).numerators e).natAbs ≤ D₀ G := by
  rw [integralIterate_table G hn]
  have h := iterate_box G t e
  have hh : |entry (iterate G t).numerators e| ≤ (D₀ G:ℤ) := by rw [abs_of_nonneg h.1]; exact h.2
  rw [←Int.natCast_natAbs] at hh
  exact_mod_cast hh

lemma integralBest_abs (G : Input) (hn : 2 ≤ G.n) (t : ℕ) (v : ℤ)
    (hv : v∈(integralIterate G t).best) : v.natAbs ≤ operandBound G := by
  induction t generalizing v with
  | zero => simp [integralIterate,integralInitial] at hv
  | succ t ih =>
    let a := (integralIterate G t).numerators
    let r := integralRow (D₀ G) a
    have hrow : r∈integralRows a := integralRow_mem _ _
    have hval := integralValue_abs G a (integralIterate_abs G hn t) r hrow
    change v∈some ((integralIterate G t).best.elim (integralValue G a r) (max (integralValue G a r))) at hv
    have he := Option.mem_some_iff.mp hv
    subst v
    cases hb : (integralIterate G t).best with
    | none => simpa only [Option.elim_none] using hval
    | some w =>
      have hw := ih w hb
      simp only [Option.elim_some]
      by_cases hh : w ≤ integralValue G a r
      · rwa [max_eq_left hh]
      · rwa [max_eq_right (le_of_not_ge hh)]

lemma operandBound_polynomial (G : Input) (hn : 2 ≤ G.n) :
    operandBound G ≤ 5052*1313^2*(tau G)^27 := by
  have ht := tau_pos G
  have hq := q_le_tau_sq G
  have hkl : K G.n+L G+1 ≤ 102*(tau G)^3 := by
    have hp : 1 ≤ (tau G)^3 := one_le_pow₀ ht
    have hh := K_L_bound G
    omega
  have hq1 : q G.n+1 ≤ 2*(tau G)^2 := by
    have hp : 1 ≤ (tau G)^2 := one_le_pow₀ ht
    omega
  have hsmall : q G.n*(K G.n+L G+1) ≤ 102*(tau G)^9 := by
    calc
      _  ≤  (tau G)^2*(102*(tau G)^3) := Nat.mul_le_mul hq hkl
      _ = 102*(tau G)^5 := by ring
      _  ≤  _ := Nat.mul_le_mul_left _ (tau_pow_mono G (by omega))
  have hlarge : M₀ G*(q G.n+1) ≤ 2424*(tau G)^9 := by
    calc
      _  ≤  (1212*(tau G)^7)*(2*(tau G)^2) := Nat.mul_le_mul (M₀_bound G) hq1
      _ = _ := by ring
  calc
    _  ≤  (2*1313^2*(tau G)^18)*(2526*(tau G)^9) :=
      Nat.mul_le_mul (Q_bound G hn) (by omega)
    _ = _ := by ring

end BinaryMatching.Algorithm
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw.Optimize
open Algorithm Finset StackCode
local instance : Preorder ℤ := Int.instLinearOrder.toPreorder

def value (p : Params) (a : Matrix ℤ) (r : Row) : ℤ :=
  upperSum p.n (fun i j => scaledPsi p (get a i j)+get p.beta i j*get a i j*p.pow)-
    (p.M:ℤ)*rowNumerator p.D a r*p.pow
lemma value_rep (G : Input) (a : Table G.n ℤ) (r : Affine G.n) :
    value (params G) (tableRep a) (rowRep r)=integralValue G a r := by
  unfold value integralValue
  rw [rowNumerator_rep]
  congr 1
  change upperSum G.n _=_
  apply upperSum_rep
  intro e
  rw [get_tableRep,get_beta,scaledPsi_rep]
  rfl

def gradient (p : Params) (a : Matrix ℤ) (r : Row) (i j : ℕ) : ℤ :=
  scaledSlope p (get a i j)+get p.beta i j-(p.M:ℤ)*get r.1 i j
lemma gradient_rep (G : Input) (a : Table G.n ℤ) (r : Affine G.n) (e : Pair G.n) :
    gradient (params G) (tableRep a) (rowRep r) e.val.1.val e.val.2.val=integralGradient G a r e := by
  unfold gradient integralGradient
  rw [get_tableRep,get_beta,get_rowRep,scaledSlope_rep]
  rfl

def update (p : Params) (a : Matrix ℤ) (r : Row) : Matrix ℤ :=
  matrix p.n (fun i j => if i < j then min (p.D:ℤ) (max 0 (get a i j+gradient p a r i j)) else 0)
lemma update_rep (G : Input) (a : Table G.n ℤ) (r : Affine G.n) :
    update (params G) (tableRep a) (rowRep r)=tableRep (integralUpdate G a r) := by
  change matrix G.n _=matrixRep _
  apply matrix_eq_rep
  intro i j
  change (if i.val<j.val then _ else 0)=(integralUpdate G a r)[i][j]
  by_cases h : i < j
  · simp [integralUpdate,toTable,tabulate,h,get_tableRep,
      gradient_rep G a r ⟨(i,j),h⟩,show (params G).D=D₀ G from rfl,entry]
  · simp [integralUpdate,toTable,tabulate,h]

def step (z : Params×IntState) : Params×IntState :=
  let r := selectedRow z.1.n z.1.D z.2.1
  let v := value z.1 z.2.1 r
  (z.1,(update z.1 z.2.1 r,some (z.2.2.elim v (max v))))

def initial (p : Params) : Params×IntState := (p,(matrix p.n (fun _ _ => 0),none))
lemma initial_rep (G : Input) : initial (params G)=(params G,stateRep (integralInitial G.n)) := by
  change (params G,(matrix G.n (fun _ _ => 0),none))=(params G,(tableRep (integralInitial G.n).numerators,none))
  apply congrArg (fun a : Matrix ℤ => (params G,(a,(none:Option ℤ))))
  apply matrix_eq_rep
  intro i j
  simp [integralInitial,tabulate]
lemma step_rep (G : Input) (hn : 2≤G.n) (he : Even G.n) (s : IntegralState G.n) :
    step (params G,stateRep s)=(params G,stateRep (integralStep G s)) := by
  dsimp only [step]
  rw [show (stateRep s).1=tableRep s.numerators from rfl,
    show (params G).n=G.n from rfl,selectedRow_rep hn he,value_rep,update_rep]
  rfl
lemma step_iterate_rep (G : Input) (hn : 2≤G.n) (he : Even G.n) (k : ℕ) :
    step^[k] (initial (params G))=(params G,stateRep (integralIterate G k)) := by
  induction k with
  | zero => exact initial_rep G
  | succ k ih => rw [Function.iterate_succ_apply',ih,step_rep G hn he]; rfl

lemma integralIterate_lower (G : Input) (t : ℕ) (i j : Fin G.n) (h : ¬i < j) :
    (integralIterate G t).numerators[i][j]=0 := by
  cases t with
  | zero => simp [integralIterate,integralInitial,tabulate]
  | succ t => simp [integralIterate,integralStep,integralUpdate,toTable,tabulate,h]
lemma integralIterate_all_abs (G : Input) (hn : 2≤G.n) (t : ℕ) (i j : Fin G.n) :
    ((integralIterate G t).numerators[i][j]).natAbs≤D₀ G := by
  by_cases hij : i < j
  · exact integralIterate_abs G hn t ⟨(i,j),hij⟩
  · rw [integralIterate_lower G t i j hij]
    exact Nat.zero_le _

def operandBound (p : Params) : ℕ := p.D*p.pow*(p.q*(p.k+p.L+1)+p.M*(p.q+1))
def budget (p : Params) : ℕ :=
  2*(encode p).length+2*(p.n*(2*(p.n*(2*(p.D+3)+1))+1))+(2*(operandBound p+3)+1)+2

lemma state_code_bound (G : Input) (hn : 2≤G.n) (t : ℕ) :
    (encode (params G,stateRep (integralIterate G t))).length≤budget (params G) := by
  have ht : (encode (tableRep (integralIterate G t).numerators)).length≤
      G.n*(2*(G.n*(2*(D₀ G+3)+1))+1) := by
    apply vectorRep_code_bound
    intro i
    apply vectorRep_code_bound
    intro j
    rw [code_int_length]
    exact Nat.add_le_add_right (integralIterate_all_abs G hn t i j) 3
  have hb : (encode (integralIterate G t).best).length≤2*(Algorithm.operandBound G+3)+1 := by
    cases h : (integralIterate G t).best with
    | none => simp only [code_option_none,List.length_nil]; omega
    | some v =>
      simp only [code_option_some,code_int_length]
      have hv := integralBest_abs G hn t v h
      omega
  simp only [code_pair_length,stateRep] at ht ⊢
  change 2*(encode (params G)).length+
    (2*(encode (tableRep (integralIterate G t).numerators)).length+
     (encode (integralIterate G t).best).length+1)+1≤_
  change _≤2*(encode (params G)).length+2*(G.n*(2*(G.n*(2*(D₀ G+3)+1))+1))+
    (2*(Algorithm.operandBound G+3)+1)+2
  omega

def run (p : Params) : IntState :=
  (((guardedStep step)^[p.q*p.D] (budget p,initial p)).2).2
lemma run_rep (G : Input) (hn : 2≤G.n) (he : Even G.n) :
    run (params G)=stateRep (integralIterate G (q G.n*D₀ G)) := by
  unfold run
  rw [guardedStep_eq step (budget (params G)) (initial (params G)) _ (by
    intro j hj
    rw [step_iterate_rep G hn he]
    exact state_code_bound G hn j),step_iterate_rep G hn he]
  rfl

def result (p : Params) : ℤ := (run p).2.getD 0/(p.D*p.pow:ℕ)
lemma result_rep (G : Input) (hn : 2≤G.n) (he : Even G.n) : result (params G)=integralR G := by
  unfold result integralR
  rw [run_rep G hn he]
  rfl
end BinaryMatching.Raw.Optimize
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw.Optimize.Compiler
open StackCode StackCode.Poly
local instance : Preorder ℤ := Int.instLinearOrder.toPreorder

@[fun_prop] theorem paramsRepr_poly : Poly Params.repr :=
  (Poly.identity (α := ParamData)).reindex Params.repr Params.repr (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem paramsOfData_poly : Poly Params.ofData :=
  (Poly.identity (α := ParamData)).reindex Params.ofData id (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem params_n : Poly Params.n :=
  Poly.comp (fun z : ParamData => z.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_q : Poly Params.q :=
  Poly.comp (fun z : ParamData => z.2.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_k : Poly Params.k :=
  Poly.comp (fun z : ParamData => z.2.2.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_L : Poly Params.L :=
  Poly.comp (fun z : ParamData => z.2.2.2.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_D : Poly Params.D :=
  Poly.comp (fun z : ParamData => z.2.2.2.2.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_M : Poly Params.M :=
  Poly.comp (fun z : ParamData => z.2.2.2.2.2.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_pow : Poly Params.pow :=
  Poly.comp (fun z : ParamData => z.2.2.2.2.2.2.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_beta : Poly Params.beta :=
  Poly.comp (fun z : ParamData => z.2.2.2.2.2.2.2) Params.repr (by fun_prop) paramsRepr_poly

@[fun_prop] theorem doubleIntSum {α : Type} [Coding α] [Inhabited α]
    (n : α → ℕ) (f : (α×ℕ)×ℕ → ℤ) (hn : Poly n) (hf : Poly f) :
    Poly (fun a => (tab (n a) (fun i => (tab (n a) (fun j => f ((a,i),j))).sum)).sum) := by
  apply Poly.comp List.sum _ Poly.listIntSum
  apply Poly.rawTab n (fun z : α×ℕ => (tab (n z.1) (fun j => f (z,j))).sum) hn
  apply Poly.comp List.sum _ Poly.listIntSum
  exact Poly.rawTab (fun z : α×ℕ => n z.1) f (by fun_prop) hf

@[fun_prop] theorem upperSum_poly {α : Type} [Coding α] [Inhabited α]
    (n : α → ℕ) (f : (α×ℕ)×ℕ → ℤ) (hn : Poly n) (hf : Poly f) :
    Poly (fun a => upperSum (n a) (fun i j => f ((a,i),j))) := by
  have h := doubleIntSum n (fun z : (α×ℕ)×ℕ => if decide (z.1.2<z.2) then f z else 0) hn (by fun_prop)
  exact h.congr (fun a => by simp only [upperSum,decide_eq_true_eq])

@[fun_prop] theorem rowNumerator_poly : Poly (fun z : ℕ×(Matrix ℤ×Row) => rowNumerator z.1 z.2.1 z.2.2) := by
  have hh := upperSum_poly (fun z : ℕ×(Matrix ℤ×Row) => z.2.1.length)
    (fun z : ((ℕ×(Matrix ℤ×Row))×ℕ)×ℕ => get z.1.1.2.2.1 z.1.2 z.2*get z.1.1.2.1 z.1.2 z.2)
    (by fun_prop) (by fun_prop)
  unfold rowNumerator
  fun_prop

@[fun_prop] theorem indexedSlope_poly : Poly (fun z : ℕ×ℕ => indexedSlope z.1 z.2) := by
  have h : Poly (fun z : ℕ×ℕ => if decide (z.2<z.1) then (z.2:ℤ)-1 else (z.1:ℤ)) := by fun_prop
  exact h.congr (fun _ => by simp only [indexedSlope,decide_eq_true_eq])

@[fun_prop] theorem pieceNumerator_poly : Poly (fun z : (ℕ×(ℕ×ℕ))×(ℤ×ℕ) =>
    pieceNumerator z.1.1 z.1.2.1 z.1.2.2 z.2.1 z.2.2) := by
  have h : Poly (fun z : (ℕ×(ℕ×ℕ))×(ℤ×ℕ) => indexedSlope z.1.1 z.2.2*z.2.1*(z.1.2.2:ℤ)+
      if decide (z.2.2<z.1.1) then (z.1.2.1:ℤ)*(cappedPow2 z.1.2.2 (z.1.1-z.2.2):ℤ) else 0) := by fun_prop
  exact h.congr (fun _ => by simp only [pieceNumerator,decide_eq_true_eq])

@[fun_prop] theorem selectedIndex_poly : Poly (fun z : (ℕ×(ℕ×ℕ))×ℤ => selectedIndex z.1.1 z.1.2.1 z.1.2.2 z.2) := by
  let arg (z : (ℕ×(ℕ×ℕ))×ℤ) := (List.range (z.1.1+1)).argmin (pieceNumerator z.1.1 z.1.2.1 z.1.2.2 z.2)
  have ha : Poly arg := by
    apply Poly.comp _ (fun z : (ℕ×(ℕ×ℕ))×ℤ => (z,List.range (z.1.1+1)))
      (Poly.listArgminParam Poly.intLT (fun z : ((ℕ×(ℕ×ℕ))×ℤ)×ℕ => pieceNumerator z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2)
        (Poly.comp _ (fun z : ((ℕ×(ℕ×ℕ))×ℤ)×ℕ => (z.1.1,(z.1.2,z.2))) pieceNumerator_poly (by fun_prop)))
      (by fun_prop)
  have h : Poly (fun z : (ℕ×(ℕ×ℕ))×ℤ => if (arg z).isSome then (arg z).getD 0 else z.1.1) := by fun_prop
  exact h.congr (fun z => by change _=(arg z).getD _; cases arg z <;> rfl)

@[fun_prop] theorem selectedIndex_params_poly : Poly (fun z : Params×ℤ => selectedIndex z.1.k z.1.D z.1.pow z.2) :=
  Poly.comp _ (fun z : Params×ℤ => ((z.1.k,(z.1.D,z.1.pow)),z.2)) selectedIndex_poly (by fun_prop)
@[fun_prop] theorem scaledPsi_poly : Poly (fun z : Params×ℤ => scaledPsi z.1 z.2) :=
  Poly.comp _ (fun z : Params×ℤ => ((z.1.k,(z.1.D,z.1.pow)),(z.2,selectedIndex z.1.k z.1.D z.1.pow z.2)))
    pieceNumerator_poly (by fun_prop)
@[fun_prop] theorem scaledSlope_poly : Poly (fun z : Params×ℤ => scaledSlope z.1 z.2) :=
  Poly.comp _ (fun z : Params×ℤ => (z.1.k,selectedIndex z.1.k z.1.D z.1.pow z.2)) indexedSlope_poly (by fun_prop)
end BinaryMatching.Raw.Optimize.Compiler
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw.Optimize.Compiler
open StackCode StackCode.Poly BinaryMatching.Raw.Compiler
local instance : Preorder ℤ := Int.instLinearOrder.toPreorder

@[fun_prop] theorem capacities_poly : Poly (fun z : ℕ×Matrix ℤ => capacities z.1 z.2) := by
  have h := Poly.rawMatrix Prod.fst (fun z : ((ℕ×Matrix ℤ)×ℕ)×ℕ =>
    if decide (z.1.2<z.2) then (get z.1.1.2 z.1.2 z.2).toNat else
    if decide (z.2<z.1.2) then (get z.1.1.2 z.2 z.1.2).toNat else 0) (by fun_prop) (by fun_prop)
  exact h.congr (fun _ => by simp only [capacities,decide_eq_true_eq])
@[fun_prop] theorem zeroRow_poly : Poly zeroRow := by
  unfold zeroRow
  apply Poly.pair
  · exact Poly.rawMatrix id (fun _ => (0:ℤ)) (by fun_prop) (by fun_prop)
  · fun_prop
@[fun_prop] theorem degreeRow_poly : Poly (fun z : ℕ×(ℕ×Bool) => degreeRow z.1 z.2.1 z.2.2) := by
  have h := Poly.rawMatrix Prod.fst (fun z : ((ℕ×(ℕ×Bool))×ℕ)×ℕ =>
    if decide (z.1.2<z.2) then
      if decide (z.1.2=z.1.1.2.1) || decide (z.2=z.1.1.2.1) then (if z.1.1.2.2 then (1:ℤ) else -1) else 0 else 0)
    (by fun_prop) (by fun_prop)
  have hh := Poly.pair _ (fun z : ℕ×(ℕ×Bool) => if z.2.2 then (-1:ℤ) else 1) h (by fun_prop)
  exact hh.congr (fun _ => by simp only [degreeRow,Bool.or_eq_true,decide_eq_true_eq])
@[fun_prop] theorem cutRow_poly : Poly (fun z : ℕ×Cut => cutRow z.1 z.2) := by
  have h := Poly.rawMatrix Prod.fst (fun z : ((ℕ×Cut)×ℕ)×ℕ =>
    if decide (z.1.2<z.2) then
      if (mem z.1.1.2 z.1.2 && !mem z.1.1.2 z.2) || (mem z.1.1.2 z.2 && !mem z.1.1.2 z.1.2) then (-1:ℤ) else 0 else 0)
    (by fun_prop) (by fun_prop)
  exact (Poly.pair _ (fun _ => (1:ℤ)) h (by fun_prop)).congr (fun _ => by simp only [cutRow,decide_eq_true_eq])
@[fun_prop] theorem rows_poly : Poly (fun z : ℕ×Matrix ℤ => rows z.1 z.2) := by
  have hd : Poly (fun z : ℕ×Matrix ℤ => (List.range z.1).flatMap (fun v => [degreeRow z.1 v true,degreeRow z.1 v false])) :=
    Poly.flatMapWith (fun z : ℕ×Matrix ℤ => List.range z.1)
      (fun z : (ℕ×Matrix ℤ)×ℕ => [degreeRow z.1.1 z.2 true,degreeRow z.1.1 z.2 false]) (by fun_prop) (by fun_prop)
  unfold rows
  fun_prop
@[fun_prop] theorem selectedRow_poly : Poly (fun z : ℕ×(ℕ×Matrix ℤ) => selectedRow z.1 z.2.1 z.2.2) := by
  let arg (z : ℕ×(ℕ×Matrix ℤ)) := (rows z.1 z.2.2).argmax (rowNumerator z.2.1 z.2.2)
  have ha : Poly arg :=
    Poly.comp _ (fun z : ℕ×(ℕ×Matrix ℤ) => (z,rows z.1 z.2.2))
      (Poly.listArgmaxParam Poly.intLT (fun z : (ℕ×(ℕ×Matrix ℤ))×Row => rowNumerator z.1.2.1 z.1.2.2 z.2)
        (by fun_prop)) (by fun_prop)
  have h : Poly (fun z : ℕ×(ℕ×Matrix ℤ) => if (arg z).isSome then (arg z).getD (default:Row) else zeroRow z.1) := by fun_prop
  exact h.congr (fun z => by change _=(arg z).getD _; cases arg z <;> rfl)
end BinaryMatching.Raw.Optimize.Compiler
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw.Optimize.Compiler
open StackCode StackCode.Poly BinaryMatching.Raw.Compiler
local instance : Preorder ℤ := Int.instLinearOrder.toPreorder

@[fun_prop] theorem value_poly : Poly (fun z : Params×(Matrix ℤ×Row) => value z.1 z.2.1 z.2.2) := by
  have hs := upperSum_poly (fun z : Params×(Matrix ℤ×Row) => z.1.n)
    (fun z : ((Params×(Matrix ℤ×Row))×ℕ)×ℕ =>
      scaledPsi z.1.1.1 (get z.1.1.2.1 z.1.2 z.2)+
      get z.1.1.1.beta z.1.2 z.2*get z.1.1.2.1 z.1.2 z.2*(z.1.1.1.pow:ℤ))
    (by fun_prop) (by fun_prop)
  unfold value
  fun_prop
@[fun_prop] theorem gradient_poly : Poly (fun z : (Params×(Matrix ℤ×Row))×(ℕ×ℕ) =>
    gradient z.1.1 z.1.2.1 z.1.2.2 z.2.1 z.2.2) := by unfold gradient; fun_prop
@[fun_prop] theorem update_poly : Poly (fun z : Params×(Matrix ℤ×Row) => update z.1 z.2.1 z.2.2) := by
  have hg : Poly (fun z : ((Params×(Matrix ℤ×Row))×ℕ)×ℕ => gradient z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2) :=
    Poly.comp _ (fun z : ((Params×(Matrix ℤ×Row))×ℕ)×ℕ => (z.1.1,(z.1.2,z.2))) gradient_poly (by fun_prop)
  have h := Poly.rawMatrix (fun z : Params×(Matrix ℤ×Row) => z.1.n)
    (fun z : ((Params×(Matrix ℤ×Row))×ℕ)×ℕ => if decide (z.1.2<z.2) then
      min (z.1.1.1.D:ℤ) (max 0 (get z.1.1.2.1 z.1.2 z.2+gradient z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2)) else 0)
    (by fun_prop) (by fun_prop)
  exact h.congr (fun _ => by simp only [update,decide_eq_true_eq])
@[fun_prop] theorem step_poly : Poly step := by
  let r (z : Params×IntState) := selectedRow z.1.n z.1.D z.2.1
  let v (z : Params×IntState) := value z.1 z.2.1 (r z)
  have hr : Poly r := by dsimp [r]; fun_prop
  have hv : Poly v := by dsimp [v]; fun_prop
  have h := Poly.optionCasesWith (fun z : Params×IntState => z.2.2) v
    (fun z : (Params×IntState)×ℤ => max (v z.1) z.2) (by fun_prop) hv (by fun_prop)
  have hm : Poly (fun z : Params×IntState => match z.2.2 with | none => v z | Option.some w => max (v z) w) :=
    h.congr (fun z => by cases z.2.2 <;> rfl)
  have hh := Poly.pair (fun z : Params×IntState => z.1)
    (fun z : Params×IntState => (update z.1 z.2.1 (r z),Option.some (match z.2.2 with | none => v z | Option.some w => max (v z) w)))
    (by fun_prop) (Poly.pair _ _ (by fun_prop) (Poly.comp _ _ Poly.some hm))
  exact hh.congr (fun z => by unfold step; dsimp [r,v]; cases z.2.2 <;> rfl)
@[fun_prop] theorem initial_poly : Poly initial := by
  unfold initial
  have hh := Poly.rawMatrix Params.n (fun _ => (0:ℤ)) (by fun_prop) (by fun_prop)
  fun_prop
@[fun_prop] theorem operandBound_poly : Poly operandBound := by unfold operandBound; fun_prop
@[fun_prop] theorem budget_poly : Poly budget := by unfold budget; fun_prop
@[fun_prop] theorem run_poly : Poly run := by
  have h := Poly.comp _ (fun p : Params => (p.q*p.D,(budget p,initial p)))
    (Poly.guardedIterate step step_poly) (by fun_prop)
  exact Poly.second _ h
@[fun_prop] theorem result_poly : Poly result := by
  exact Poly.comp _ (fun p : Params => ((run p).2.getD 0,p.D*p.pow)) Poly.intDivNat (by fun_prop)
end BinaryMatching.Raw.Optimize.Compiler
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.StackCode

def unaryClog (x : ℕ) : ℕ :=
  ((List.range (x+1)).find? (fun j => decide (x≤cappedPow2 x j))).getD 0

lemma unaryClog_eq (x : ℕ) : unaryClog x=Nat.clog 2 x := by
  have hk : Nat.clog 2 x≤x := Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
  have hp (j : ℕ) : (x≤cappedPow2 x j) ↔ Nat.clog 2 x≤j := by
    rw [cappedPow2_eq,le_min_iff]
    simpa only [le_refl,true_and] using (Nat.clog_le_iff_le_pow (by decide : 1<2) (x := x) (y := j)).symm
  have hf : (List.range (x+1)).find? (fun j => decide (x≤cappedPow2 x j))=some (Nat.clog 2 x) := by
    apply List.find?_eq_some_iff_getElem.mpr
    refine ⟨by simp [hp],Nat.clog 2 x,by simpa using Nat.lt_succ_of_le hk,by simp,?_⟩
    intro j hj
    simp only [List.getElem_range,Bool.not_eq_true',decide_eq_false_iff_not,hp]
    omega
  simp only [unaryClog,hf,Option.getD_some]

namespace Poly
@[fun_prop] theorem natClog2 : Poly (Nat.clog 2) := by
  have hf := Poly.findWith (fun x : ℕ => List.range (x+1))
    (fun z : ℕ×ℕ => decide (z.1≤cappedPow2 z.1 z.2)) (by fun_prop) (by fun_prop)
  have h : Poly unaryClog := by unfold unaryClog; fun_prop
  exact h.congr unaryClog_eq

@[fun_prop] theorem powClog2 : Poly (fun x : ℕ => 2^(Nat.clog 2 x)) := by
  have hbound (x : ℕ) : 2^(Nat.clog 2 x)≤2*x+1 := by
    by_cases hx : x≤1
    · rw [Nat.clog_of_right_le_one hx]; simp
    · have hpos : 0<Nat.clog 2 x := Nat.clog_pos (by decide) (by omega)
      have hh : 2^(Nat.clog 2 x-1)<x := by
        simpa only [Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self (by decide : 1<2) (by omega : 1<x)
      have he : 2^(Nat.clog 2 x)=2^(Nat.clog 2 x-1)*2 := by rw [←pow_succ,Nat.sub_add_cancel hpos]
      rw [he]
      omega
  have h : Poly (fun x : ℕ => cappedPow2 (2*x+1) (Nat.clog 2 x)) := by fun_prop
  exact h.congr (fun x => cappedPow2_of_le _ _ (hbound x))
end Poly
end BinaryMatching.StackCode
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw.InputData
open StackCode Algorithm Raw.Optimize
abbrev Rec := ℕ×(ℕ×List Bool)
abbrev Data := ℕ×List Rec

def repr (r : Record) : Rec := (r.left,(r.right,r.multiplicity.bits))
def decodeRecord (b : ℕ) (r : Parse.RecordBits) : Rec :=
  (Parse.boundedValue b r.1,(Parse.boundedValue b r.2.1,r.2.2))
lemma decodeRecord_repr (G : Input) (b : ℕ) (hb : G.n≤b) (r : Record) (hr : r∈G.records) :
    decodeRecord b (Parse.recordRepr r)=repr r := by
  have hv := G.valid r hr
  simp only [decodeRecord,Parse.recordRepr,Parse.boundedValue_bits,repr]
  rw [min_eq_right (by omega : r.left≤b),min_eq_right (by omega : r.right≤b)]
@[fun_prop] theorem decodeRecord_poly : Poly (fun z : ℕ×Parse.RecordBits => decodeRecord z.1 z.2) := by
  unfold decodeRecord
  fun_prop

def bound (rs : List Parse.RecordBits) : ℕ := 2*rs.length+1
def decode (z : List Bool×List Parse.RecordBits) : Data :=
  (Parse.boundedValue (bound z.2) z.1,z.2.map (decodeRecord (bound z.2)))
lemma decode_encoded (G : Input) (hn : G.n≤2*G.records.length) :
    decode (G.n.bits,G.records.map Parse.recordRepr)=(G.n,G.records.map repr) := by
  unfold decode
  simp only [bound,List.length_map,Parse.boundedValue_bits]
  rw [min_eq_right (by omega : G.n≤2*G.records.length+1)]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro r hr
  exact decodeRecord_repr G _ (by omega) r hr
lemma decode_n_encoded (G : Input) :
    (decode (G.n.bits,G.records.map Parse.recordRepr)).1=min (2*G.records.length+1) G.n := by
  simp only [decode,bound,List.length_map,Parse.boundedValue_bits]
lemma decode_length (z : List Bool×List Parse.RecordBits) : (decode z).2.length=z.2.length := by simp [decode]
@[fun_prop] theorem decode_poly : Poly decode := by
  have hm := Poly.mapWith (fun z : List Bool×List Parse.RecordBits => z.2)
    (fun z : (List Bool×List Parse.RecordBits)×Parse.RecordBits => decodeRecord (bound z.1.2) z.2)
    (by fun_prop) (by unfold bound; fun_prop)
  unfold decode bound
  fun_prop

def multiplicityBits (rs : List Rec) (i j : ℕ) : List Bool :=
  ((rs.find? (fun a => a.1=i && a.2.1=j)).map (fun a => a.2.2)).getD []
lemma multiplicityBits_repr (G : Input) (i j : ℕ) :
    multiplicityBits (G.records.map repr) i j=(rawMultiplicity G i j).bits := by
  unfold multiplicityBits rawMultiplicity
  rw [List.find?_map]
  change (((G.records.find? (fun r => r.left=i && r.right=j)).map repr).map (fun a => a.2.2)).getD []=_
  cases G.records.find? (fun r => r.left=i && r.right=j) <;> rfl
lemma multiplicityBits_pair (G : Input) (e : Pair G.n) :
    multiplicityBits (G.records.map repr) e.val.1.val e.val.2.val=(multiplicity G e).bits := by
  rw [multiplicityBits_repr]
  unfold rawMultiplicity multiplicity
  cases G.records.find? (fun r => r.left=e.val.1.val && r.right=e.val.2.val) <;> rfl
@[fun_prop] theorem multiplicityBits_poly : Poly (fun z : List Rec×(ℕ×ℕ) => multiplicityBits z.1 z.2.1 z.2.2) := by
  have hf := Poly.findWith (fun z : List Rec×(ℕ×ℕ) => z.1)
    (fun z : (List Rec×(ℕ×ℕ))×Rec => decide (z.2.1=z.1.2.1) && decide (z.2.2.1=z.1.2.2)) (by fun_prop) (by fun_prop)
  unfold multiplicityBits
  fun_prop

def bitsBudget (rs : List Rec) : ℕ := (rs.map (fun r => r.2.2.length-1)).foldl max 0
lemma bitsBudget_repr (G : Input) : bitsBudget (G.records.map repr)=B G := by
  unfold bitsBudget B
  simp only [List.map_map,Function.comp_def,repr,←Parse.log2_bits_length]
@[fun_prop] theorem bitsBudget_poly : Poly bitsBudget := by
  have hf := Poly.listFoldAdd (fun z : ℕ×ℕ => max z.1 z.2) Poly.natMax 1 (by
    intro z
    simp only [code_nat_length]
    omega)
  exact Poly.comp _ (fun rs : List Rec => (rs.map (fun r => r.2.2.length-1),0)) hf (by fun_prop)

def pairs (n : ℕ) : ℕ := (upperSum n (fun _ _ => (1:ℤ))).toNat
lemma pairs_eq (n : ℕ) : pairs n=q n := by
  have h := upperSum_rep (fun _ : Pair n => (1:ℤ)) (fun _ _ => (1:ℤ)) (fun _ => rfl)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at h
  unfold pairs
  rw [h]
  simp [q]
@[fun_prop] theorem pairs_poly : Poly pairs := by
  have h := Raw.Optimize.Compiler.upperSum_poly id (fun _ => (1:ℤ)) (by fun_prop) (by fun_prop)
  unfold pairs
  fun_prop

def betaValue (rs : List Rec) (L i j : ℕ) : ℤ :=
  let bits := multiplicityBits rs i j
  if bits.isEmpty then -(L:ℤ) else (bits.length-1:ℕ)
lemma betaValue_repr (G : Input) (e : Pair G.n) :
    betaValue (G.records.map repr) (L G) e.val.1.val e.val.2.val=Algorithm.beta G e := by
  unfold betaValue Algorithm.beta
  rw [multiplicityBits_pair]
  simp only [List.isEmpty_iff,Parse.bits_nil_iff,Parse.log2_bits_length]
@[fun_prop] theorem betaValue_poly : Poly (fun z : (List Rec×ℕ)×(ℕ×ℕ) => betaValue z.1.1 z.1.2 z.2.1 z.2.2) := by
  unfold betaValue
  fun_prop

def betaMatrix (n : ℕ) (rs : List Rec) (L : ℕ) : Matrix ℤ :=
  matrix n (fun i j => if i < j then betaValue rs L i j else 0)
lemma betaMatrix_repr (G : Input) :
    betaMatrix G.n (G.records.map repr) (L G)=tableRep (toTable (Algorithm.beta G)) := by
  apply matrix_eq_rep
  intro i j
  by_cases hij : i < j
  · simp [toTable,tabulate,hij,betaValue_repr G ⟨(i,j),hij⟩]
  · simp [toTable,tabulate,hij]
@[fun_prop] theorem betaMatrix_poly : Poly (fun z : Data×ℕ => betaMatrix z.1.1 z.1.2 z.2) := by
  have hb : Poly (fun z : ((Data×ℕ)×ℕ)×ℕ => betaValue z.1.1.1.2 z.1.1.2 z.1.2 z.2) :=
    Poly.comp _ (fun z : ((Data×ℕ)×ℕ)×ℕ => ((z.1.1.1.2,z.1.1.2),(z.1.2,z.2))) betaValue_poly (by fun_prop)
  have h := Poly.rawMatrix (fun z : Data×ℕ => z.1.1)
    (fun z : ((Data×ℕ)×ℕ)×ℕ => if decide (z.1.2<z.2) then betaValue z.1.1.1.2 z.1.1.2 z.1.2 z.2 else 0)
    (by fun_prop) (by fun_prop)
  exact h.congr (fun _ => by simp only [betaMatrix,decide_eq_true_eq])

def parameters (z : Data) : Params :=
  let q := pairs z.1
  let k := Nat.clog 2 q
  let l := 100*(z.1+bitsBudget z.2+1)^3
  let m := q*(k+l)*(2+10*z.1^2)
  let d := q*(k+l+m)^2
  ⟨z.1,q,k,l,d,m,2^(Nat.clog 2 q),betaMatrix z.1 z.2 l⟩
lemma parameters_repr (G : Input) : parameters (G.n,G.records.map repr)=params G := by
  simp only [parameters,pairs_eq,bitsBudget_repr,params,K,L,M₀,D₀,A₀]
  congr 1
  exact betaMatrix_repr G
@[fun_prop] theorem parameters_poly : Poly parameters := by
  let p (z : Data) : ParamData :=
    let q := pairs z.1
    let k := Nat.clog 2 q
    let l := 100*(z.1+bitsBudget z.2+1)^3
    let m := q*(k+l)*(2+10*z.1^2)
    let d := q*(k+l+m)^2
    (z.1,(q,(k,(l,(d,(m,(2^(Nat.clog 2 q),betaMatrix z.1 z.2 l)))))))
  have hb : Poly (fun z : Data => betaMatrix z.1 z.2 (100*(z.1+bitsBudget z.2+1)^3)) :=
    Poly.comp _ (fun z : Data => (z,100*(z.1+bitsBudget z.2+1)^3)) betaMatrix_poly (by fun_prop)
  have hpw : Poly (fun z : Data => 2^(Nat.clog 2 (pairs z.1))) :=
    Poly.comp _ (fun z : Data => pairs z.1) Poly.powClog2 (by fun_prop)
  have hp : Poly p := by dsimp only [p]; fun_prop
  exact Poly.comp _ p Raw.Optimize.Compiler.paramsOfData_poly hp
end BinaryMatching.Raw.InputData
end

end OAI
end
end

section
section
namespace OAI

section

namespace BinaryMatching.Raw.InputData
open StackCode Algorithm Optimize

def powerBits (k : ℕ) : List Bool := List.replicate k false++[true]
lemma powerBits_eq (k : ℕ) : powerBits k=(2^k).bits := by
  induction k with
  | zero => simp [powerBits]
  | succ k ih =>
    rw [pow_succ,Nat.mul_comm,Nat.bit0_bits (2^k) (by positivity)]
    simpa only [powerBits,List.replicate_succ,List.cons_append] using congrArg (List.cons false) ih
@[fun_prop] theorem powerBits_poly : Poly powerBits := by unfold powerBits; fun_prop

def smallSolve (z : Data) : List Bool :=
  if z.1=0 then [true] else
  if z.1%2=1 then [] else
  if z.1=2 then multiplicityBits z.2 0 1 else
  let r := result (parameters z)
  if r < -10*(z.1:ℤ) then [] else powerBits (r-5*(z.1:ℤ)).toNat

def smallEstimate (G : Input) : ℕ :=
  if G.n=0 then 1 else
  if G.n%2=1 then 0 else
  if G.n=2 then rawMultiplicity G 0 1 else integralEstimate G
lemma smallSolve_repr (G : Input) : smallSolve (G.n,G.records.map repr)=(smallEstimate G).bits := by
  unfold smallSolve smallEstimate
  dsimp only
  by_cases hn0 : G.n=0
  · simp only [hn0,ite_true]; rfl
  simp only [hn0,ite_false]
  by_cases ho : G.n%2=1
  · simp only [ho,ite_true]; rfl
  simp only [ho,ite_false]
  by_cases hn2 : G.n=2
  · simpa only [hn2,ite_true] using multiplicityBits_repr G 0 1
  simp only [hn2,ite_false]
  have he : Even G.n := Nat.even_iff.mpr (by omega)
  have hn : 2≤G.n := by omega
  rw [parameters_repr,result_rep G hn he]
  dsimp only [integralEstimate]
  split_ifs
  · rfl
  · exact powerBits_eq _
@[fun_prop] theorem smallSolve_poly : Poly smallSolve := by
  have h : Poly (fun z : Data => if decide (z.1=0) then [true] else
      if decide (z.1%2=1) then [] else if decide (z.1=2) then multiplicityBits z.2 0 1 else
      if decide (result (parameters z) < -10*(z.1:ℤ)) then [] else
        powerBits (result (parameters z)-5*(z.1:ℤ)).toNat) := by fun_prop
  exact h.congr (fun z => by simp only [smallSolve,decide_eq_true_eq])

def solve (z : Data) : List Bool := if 2*z.2.length<z.1 then [] else smallSolve z

def sparseEstimate (G : Input) : ℕ := if 2*G.records.length<G.n then 0 else smallEstimate G
lemma sparseEstimate_correct (G : Input) :
    sparseEstimate G≤count G ∧ count G≤2^(9*G.n)*sparseEstimate G ∧ (sparseEstimate G=0 ↔ count G=0) := by
  unfold sparseEstimate
  split_ifs with hguard
  · have hz := count_zero_of_uncovered G (lt_of_le_of_lt (covered_card_le_records G) hguard)
    simp [hz]
  · unfold smallEstimate
    split_ifs with hn0 hodd hn2
    · rw [count_zero_vertices G hn0,hn0]
      norm_num
    · rw [count_odd_vertices G (Nat.odd_iff.mpr hodd)]
      simp
    · rw [count_two_vertices G hn2]
      refine ⟨le_rfl,?_,Iff.rfl⟩
      exact Nat.le_mul_of_pos_left _ (by positivity)
    · have hn : 4≤G.n := by omega
      have he : Even G.n := Nat.even_iff.mpr (by omega)
      rw [integralEstimate_eq G (by omega)]
      exact estimate_correct G hn he

lemma sparseEstimate_eq_approximate (G : Input) : sparseEstimate G=approximate G := by
  unfold sparseEstimate
  split_ifs with hg
  · symm
    exact (approximate_correct G).2.2.mpr
      (count_zero_of_uncovered G (lt_of_le_of_lt (covered_card_le_records G) hg))
  · unfold smallEstimate approximate
    simp only [Nat.odd_iff]
    split_ifs with hn0 ho hn2 hc
    · rfl
    · rfl
    · rfl
    · rw [integralEstimate_eq G (by omega)]
      exact (estimate_correct G (by omega) (Nat.even_iff.mpr (by omega))).2.2.mpr
        (count_zero_of_uncovered G hc)
    · exact integralEstimate_eq G (by omega)

lemma solve_decoded (G : Input) :
    solve (decode (G.n.bits,G.records.map Parse.recordRepr))=(sparseEstimate G).bits := by
  unfold solve sparseEstimate
  rw [decode_length,List.length_map,decode_n_encoded]
  by_cases hg : 2*G.records.length<G.n
  · rw [ite_eq_left hg,ite_eq_left (by omega)]
    rfl
  · rw [ite_eq_right hg,ite_eq_right (by omega),decode_encoded G (by omega),smallSolve_repr]
@[fun_prop] theorem solve_poly : Poly solve := by
  have hh : Poly (fun z : Data => if decide (2*z.2.length<z.1) then [] else smallSolve z) := by fun_prop
  exact hh.congr (fun z => by simp only [solve,decide_eq_true_eq])

def runInput (l : List Bool) : List Bool := solve (decode (Parse.input l))
lemma runInput_encoded (G : Input) : runInput (encodeInput G)=(sparseEstimate G).bits := by
  rw [runInput,Parse.input_encoded,solve_decoded]
@[fun_prop] theorem runInput_poly : Poly runInput := by unfold runInput; fun_prop

def bitAlgorithm (b : Bits) : Bits := ⟨runInput b.data⟩
theorem bitAlgorithm_poly : Poly bitAlgorithm := by
  change Poly (fun b : Bits => Bits.mk (runInput b.data))
  exact Poly.comp Bits.mk (fun b : Bits => runInput b.data) Poly.bitsEncode
    (Poly.comp runInput Bits.data runInput_poly Poly.bitsDecode)

noncomputable def binaryRoutine : Routine Bits.data Bits.data bitAlgorithm := bitAlgorithm_poly.routine
lemma bitAlgorithm_encoded (G : Input) :
    (bitAlgorithm ⟨encodeInput G⟩).data=(sparseEstimate G).bits := by
  change runInput (encodeInput G)=(sparseEstimate G).bits
  exact runInput_encoded G

noncomputable def countingRoutine : Routine encodeInput Nat.bits sparseEstimate :=
  binaryRoutine.reindex encodeInput Nat.bits sparseEstimate (fun G => Bits.mk (encodeInput G))
    (fun _ => rfl) bitAlgorithm_encoded

theorem deterministic_approximate_counting_oai :
    ∃ A : Input → ℕ,
      ∃ machine : Turing.TM2ComputableInPolyTime encodeInput Nat.bits A,
        (∀ k, Finite (machine.tm.Γ k)) ∧
        (∃ P : Polynomial ℕ, ∀ G,(A G).bits.length≤P.eval (encodeInput G).length) ∧
        ∀ G,A G≤count G ∧ count G≤2^(9*G.n)*A G ∧ (A G=0 ↔ count G=0) := by
  refine ⟨sparseEstimate,countingRoutine.machine,countingRoutine.machine_alphabets_finite,?_,sparseEstimate_correct⟩
  refine ⟨Polynomial.X+countingRoutine.time,?_⟩
  intro G
  simpa only [Polynomial.eval_add,Polynomial.eval_X] using countingRoutine.length_bound G
end BinaryMatching.Raw.InputData

namespace BinaryMatching

theorem deterministic_approximate_counting_oai :
    ∃ A : Input → ℕ,
      ∃ machine : Turing.TM2ComputableInPolyTime encodeInput Nat.bits A,
        (∀ k, Finite (machine.tm.Γ k)) ∧
        (∃ P : Polynomial ℕ, ∀ G,(A G).bits.length≤P.eval (encodeInput G).length) ∧
        ∀ G,A G≤count G ∧ count G≤2^(9*G.n)*A G ∧ (A G=0 ↔ count G=0) :=
  Raw.InputData.deterministic_approximate_counting_oai
end BinaryMatching
end

end OAI
end
end

theorem solution : type_of% @OAI.BinaryMatching.deterministic_approximate_counting_oai := @OAI.BinaryMatching.deterministic_approximate_counting_oai
