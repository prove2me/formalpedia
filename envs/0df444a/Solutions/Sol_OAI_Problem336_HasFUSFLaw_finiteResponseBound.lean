-- Prove2me | solution 1 for OAI.Problem336.HasFUSFLaw.finiteResponseBound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:39:34.463982+00:00
-- url     : https://prove2.me/submissions/4fddc807-25eb-4f18-a115-4ae93e86bcd8

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.Nodup
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Definitions.Def_FreeUniformSpanningForest
import Definitions.Def_OAIS336000

section
-- module Solutions.OAIS_P336.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_BinaryLawUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem336.BinaryLaw

theorem measure_ext_of_signed_cylinders {I : Type*} {μ ν : Measure (I → Bool)} [IsFiniteMeasure μ]
    (h : ∀ A B : Finset I,
      μ {x | (∀ e ∈ A, x e = true) ∧ (∀ e ∈ B, x e = false)} =
      ν {x | (∀ e ∈ A, x e = true) ∧ (∀ e ∈ B, x e = false)}) : μ = ν := by
  classical
  let F : (s : Finset I) → Measure (s → Bool) :=
    fun s => μ.map s.restrict
  have hμ : IsProjectiveLimit μ F := fun s => rfl
  have hν : IsProjectiveLimit ν F := by
    intro s
    apply Measure.ext_of_singleton
    intro a
    let f : I → Bool := fun e => if he : e ∈ s then a ⟨e, he⟩ else false
    let A := s.filter (fun e => f e = true)
    let B := s.filter (fun e => f e = false)
    have hset : s.restrict ⁻¹' ({a} : Set (s → Bool)) =
        {x | (∀ e ∈ A, x e = true) ∧ (∀ e ∈ B, x e = false)} := by
      ext x
      change (s.restrict x = a) ↔ _
      constructor
      · intro hx
        constructor
        · intro e he
          obtain ⟨hes, he⟩ := Finset.mem_filter.mp he
          have hx' := congrFun hx (⟨e, hes⟩ : s)
          simpa [f, hes, ← hx'] using he
        · intro e he
          obtain ⟨hes, he⟩ := Finset.mem_filter.mp he
          have hx' := congrFun hx (⟨e, hes⟩ : s)
          simpa [f, hes, ← hx'] using he
      · intro hx
        funext e
        have hf : f e = a e := by simp [f, e.property]
        cases ha : a e
        · exact hx.2 e (Finset.mem_filter.mpr ⟨e.property, hf.trans ha⟩)
        · exact hx.1 e (Finset.mem_filter.mpr ⟨e.property, hf.trans ha⟩)
    change (ν.map s.restrict) {a} = (μ.map s.restrict) {a}
    rw [Measure.map_apply (Finset.measurable_restrict s) (measurableSet_singleton a),
      Measure.map_apply (Finset.measurable_restrict s) (measurableSet_singleton a), hset]
    exact (h A B).symm
  exact hμ.unique hν

end Problem336.BinaryLaw

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CylinderLimitMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem336

theorem clopen_measure_eq_of_mapClusterPt
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] [HasOuterApproxClosed E]
    {α : Type*} {F : Filter α} {μs : α → ProbabilityMeasure E}
    {μ : ProbabilityMeasure E} (hμ : MapClusterPt μ F μs)
    {S : Set E} (hS : IsClopen S) {L : ℝ≥0∞}
    (hL : Tendsto (fun a => (μs a : Measure E) S) F (𝓝 L)) :
    (μ : Measure E) S = L := by
  let G := 𝓝 μ ⊓ Filter.map μs F
  have : G.NeBot := hμ.neBot
  have ht : Tendsto (id : ProbabilityMeasure E → ProbabilityMeasure E) G (𝓝 μ) := by
    change G ≤ 𝓝 μ
    exact inf_le_left
  have hv := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto ht hS
  have hev : Tendsto (fun ν : ProbabilityMeasure E => (ν : Measure E) S) G
      (𝓝 ((μ : Measure E) S)) := by
    simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, id_eq,
      Function.comp_def] using (ENNReal.continuous_coe.tendsto _).comp hv
  have hl : Tendsto (fun ν : ProbabilityMeasure E => (ν : Measure E) S)
      (Filter.map μs F) (𝓝 L) := tendsto_map'_iff.mpr hL
  exact tendsto_nhds_unique hev (hl.mono_left inf_le_right)

theorem isClopen_boolCylinder {I : Type*} (A B : Finset I) :
    IsClopen {x : I → Bool |
      (∀ i ∈ A, x i = true) ∧ (∀ i ∈ B, x i = false)} := by
  have h (s : Finset I) (b : Bool) :
      IsClopen {x : I → Bool | ∀ i ∈ s, x i = b} := by
    have heq : {x : I → Bool | ∀ i ∈ s, x i = b} =
        ⋂ i ∈ s, (fun x : I → Bool => x i) ⁻¹' {b} := by
      ext x
      simp
    rw [heq]
    exact isClopen_biInter_finset fun i _ =>
      (isClopen_discrete ({b} : Set Bool)).preimage (continuous_apply i)
  exact (h A true).inter (h B false)

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_BinaryWeakConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem336.BinaryLaw

theorem tendsto_iff_signedCylinders
    {I α : Type*} [Countable I] {F : Filter α}
    {μs : α → ProbabilityMeasure (I → Bool)}
    {μ : ProbabilityMeasure (I → Bool)} :
    Tendsto μs F (𝓝 μ) ↔ ∀ A B : Finset I,
      Tendsto (fun a => (μs a : Measure (I → Bool)) (signedCylinder A B)) F
        (𝓝 ((μ : Measure (I → Bool)) (signedCylinder A B))) := by
  constructor
  · intro h A B
    have hv := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto h
      (Problem336.isClopen_boolCylinder A B)
    simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      Function.comp_def, signedCylinder] using (ENNReal.continuous_coe.tendsto _).comp hv
  · intro h
    apply tendsto_nhds_of_unique_mapClusterPt
    intro ν hν
    apply ProbabilityMeasure.toMeasure_injective
    apply measure_ext_of_signed_cylinders
    intro A B
    exact Problem336.clopen_measure_eq_of_mapClusterPt hν
      (Problem336.isClopen_boolCylinder A B) (h A B)

end Problem336.BinaryLaw

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CauchyBinet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix Polynomial
open scoped BigOperators

namespace Problem336.CauchyBinet

variable {R m n : Type*} [CommRing R]
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem coeff_det_one_add_X_smul_card (M : Matrix n n R) :
    (Matrix.det (1 + (X : R[X]) • M.map C)).coeff (Fintype.card n) = M.det := by
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  have hsets : (Finset.univ : Finset n).powersetCard (Fintype.card n) =
      {Finset.univ} := by
    ext s
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.mem_singleton]
    exact Finset.card_eq_iff_eq_univ s
  rw [hsets, Finset.sum_singleton]
  let e : (Finset.univ : Finset n) ≃ n :=
    { toFun := Subtype.val
      invFun := fun i => ⟨i, Finset.mem_univ i⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Matrix.det_submatrix_equiv_self e M

theorem det_one_add_X_mul_comm (A : Matrix n m R) (B : Matrix m n R) :
    Matrix.det (1 + (X : R[X]) • (A * B).map C) =
      Matrix.det (1 + (X : R[X]) • (B * A).map C) := by
  simpa only [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul] using
    Matrix.det_one_add_mul_comm ((X : R[X]) • A.map C) (B.map C)

theorem det_mul_eq_sum_principal_minors (A : Matrix n m R) (B : Matrix m n R) :
    Matrix.det (A * B) =
      ∑ s ∈ (Finset.univ : Finset m).powersetCard (Fintype.card n),
        Matrix.det ((B * A).submatrix (Subtype.val : s → m) (Subtype.val : s → m)) := by
  rw [← coeff_det_one_add_X_smul_card (A * B), det_one_add_X_mul_comm A B,
    Matrix.coeff_det_one_add_X_smul_eq_sum_minors]

omit [DecidableEq m] [DecidableEq n] in
theorem columnMinor_map {S : Type*} [CommRing S]
    (A : Matrix n m R) (f : R →+* S) (s : ColumnSets n m) :
    columnMinor (A.map f) s = (columnMinor A s).map f := rfl

omit [DecidableEq n] in
theorem columnMinor_map_det {S : Type*} [CommRing S]
    (A : Matrix n m R) (f : R →+* S) (s : ColumnSets n m) :
    (columnMinor (A.map f) s).det = f (columnMinor A s).det := by
  rw [columnMinor_map]
  exact (RingHom.map_det f (columnMinor A s)).symm

theorem det_mul_eq_sum_minors (A : Matrix n m R) (B : Matrix m n R) :
    Matrix.det (A * B) =
      ∑ s : ColumnSets n m,
        (columnMinor A s).det *
          (B.submatrix Subtype.val (columnIndexEquiv s)).det := by
  rw [det_mul_eq_sum_principal_minors, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Matrix.submatrix_mul_equiv B A Subtype.val (columnIndexEquiv s) Subtype.val,
    Matrix.det_mul]
  exact mul_comm _ _

omit [DecidableEq n] in
theorem columnMinor_mul_diagonal (A : Matrix n m R) (w : m → R)
    (s : ColumnSets n m) :
    columnMinor (A * Matrix.diagonal w) s =
      columnMinor A s * Matrix.diagonal (fun j : (s.val : Finset m) => w j.val) := by
  ext i j
  simp [columnMinor, Matrix.mul_diagonal]

theorem det_weighted_gram_eq_sum_sq_minors (A : Matrix n m R) (w : m → R) :
    Matrix.det (A * Matrix.diagonal w * A.transpose) =
      ∑ s : ColumnSets n m,
        (∏ j : (s.val : Finset m), w j.val) * (columnMinor A s).det ^ 2 := by
  rw [det_mul_eq_sum_minors]
  apply Finset.sum_congr rfl
  intro s _
  have ht : A.transpose.submatrix Subtype.val (columnIndexEquiv s) =
      (columnMinor A s).transpose := rfl
  rw [columnMinor_mul_diagonal, Matrix.det_mul, Matrix.det_diagonal,
    ht, Matrix.det_transpose]
  ring

theorem det_weighted_gram_eq_sum_of_sq_minors
    (A : Matrix n m R) (w : m → R) (P : Finset m → Prop) [DecidablePred P]
    (hminor : ∀ s : ColumnSets n m,
      (columnMinor A s).det ^ 2 = if P s.val then 1 else 0) :
    Matrix.det (A * Matrix.diagonal w * A.transpose) =
      ∑ s ∈ (Finset.univ : Finset m).powersetCard (Fintype.card n),
        if P s then ∏ j ∈ s, w j else 0 := by
  rw [det_weighted_gram_eq_sum_sq_minors,
    ← Finset.sum_coe_sort (ColumnSets n m)
      (fun s : Finset m => if P s then ∏ j ∈ s, w j else 0)]
  apply Finset.sum_congr rfl
  intro s _
  rw [hminor s]
  by_cases hs : P s.val
  · simp only [ite_eq_left hs, mul_one]
    exact Finset.prod_coe_sort s.val w
  · simp only [ite_eq_right hs, mul_zero]

theorem det_weighted_gram_eq_sum_filter
    (A : Matrix n m R) (w : m → R) (P : Finset m → Prop) [DecidablePred P]
    (hminor : ∀ s : ColumnSets n m,
      (columnMinor A s).det ^ 2 = if P s.val then 1 else 0) :
    Matrix.det (A * Matrix.diagonal w * A.transpose) =
      ∑ s ∈ ((Finset.univ : Finset m).powersetCard (Fintype.card n)).filter P,
        ∏ j ∈ s, w j := by
  rw [det_weighted_gram_eq_sum_of_sq_minors A w P hminor, Finset.sum_filter]

theorem det_weighted_gram_map_eq_sum_filter {S : Type*} [CommRing S]
    (A : Matrix n m R) (f : R →+* S) (w : m → S)
    (P : Finset m → Prop) [DecidablePred P]
    (hminor : ∀ s : ColumnSets n m,
      (columnMinor A s).det ^ 2 = if P s.val then 1 else 0) :
    Matrix.det (A.map f * Matrix.diagonal w * (A.map f).transpose) =
      ∑ s ∈ ((Finset.univ : Finset m).powersetCard (Fintype.card n)).filter P,
        ∏ j ∈ s, w j := by
  apply det_weighted_gram_eq_sum_filter
  intro s
  rw [columnMinor_map_det, ← map_pow, hminor s]
  by_cases hs : P s.val <;> simp [hs]

end Problem336.CauchyBinet

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_ReducedLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem336.ReducedLaplacian

open scoped BigOperators Matrix

variable {V E : Type*}

theorem potential_eq_of_connected (src dst : E → V) (hconn : Connected src dst)
    (x : V → ℝ) (hedge : ∀ e, x (src e) = x (dst e)) (u v : V) : x u = x v := by
  have hp := hconn u v
  induction hp with
  | refl => rfl
  | @tail b c hab hbc ih =>
      apply ih.trans
      obtain ⟨e, h | h⟩ := hbc
      · simpa [h.1, h.2] using hedge e
      · simpa [h.1, h.2] using (hedge e).symm

variable [DecidableEq V]

variable [Fintype V]

lemma sum_indicator_mul (root : V) (x : {v : V // v ≠ root} → ℝ) (v : V) :
    (∑ i : {v : V // v ≠ root}, (if i.val = v then (1 : ℝ) else 0) * x i) =
      extendZero root x v := by
  classical
  by_cases hv : v ≠ root
  · rw [extendZero, dite_eq_left hv]
    rw [Finset.sum_eq_single ⟨v, hv⟩]
    · simp
    · intro b _ hb
      have hb' : b.val ≠ v := fun h => hb (Subtype.ext h)
      simp [hb']
    · simp
  · have hv' : v = root := not_ne_iff.mp hv
    subst v
    rw [extendZero_root]
    apply Finset.sum_eq_zero
    intro i _
    simp [i.property]

theorem reducedGradient_mulVec (src dst : E → V) (root : V)
    (x : {v : V // v ≠ root} → ℝ) (e : E) :
    (reducedGradient src dst root *ᵥ x) e =
      extendZero root x (src e) - extendZero root x (dst e) := by
  simp only [Matrix.mulVec, dotProduct, reducedGradient, sub_mul, Finset.sum_sub_distrib]
  rw [sum_indicator_mul, sum_indicator_mul]

theorem reducedGradient_mulVec_injective (src dst : E → V) (root : V)
    (hconn : Connected src dst) :
    Function.Injective (reducedGradient src dst root).mulVec := by
  intro x y hxy
  have hedge : ∀ e,
      (extendZero root x - extendZero root y) (src e) =
      (extendZero root x - extendZero root y) (dst e) := by
    intro e
    have h := congrFun hxy e
    rw [reducedGradient_mulVec, reducedGradient_mulVec] at h
    simp only [Pi.sub_apply]
    linarith
  funext v
  have h := potential_eq_of_connected src dst hconn
    (extendZero root x - extendZero root y) hedge v.val root
  exact sub_eq_zero.mp (by simpa using h)

variable [Fintype E] [DecidableEq E]

theorem weightedLaplacian_posDef (src dst : E → V) (root : V) (w : E → ℝ)
    (hconn : Connected src dst) (hw : ∀ e, 0 < w e) :
    (weightedLaplacian src dst root w).PosDef := by
  have hd : (Matrix.diagonal w).PosDef := Matrix.PosDef.diagonal hw
  have h := hd.conjTranspose_mul_mul_same
    (reducedGradient_mulVec_injective src dst root hconn)
  simpa [weightedLaplacian, Matrix.conjTranspose_eq_transpose_of_trivial] using h

theorem weightedLaplacian_isUnit (src dst : E → V) (root : V) (w : E → ℝ)
    (hconn : Connected src dst) (hw : ∀ e, 0 < w e) :
    IsUnit (weightedLaplacian src dst root w) :=
  (weightedLaplacian_posDef src dst root w hconn hw).isUnit

theorem weightedLaplacian_det_ne_zero (src dst : E → V) (root : V) (w : E → ℝ)
    (hconn : Connected src dst) (hw : ∀ e, 0 < w e) :
    (weightedLaplacian src dst root w).det ≠ 0 := by
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (weightedLaplacian_isUnit src dst root w hconn hw))

end Problem336.ReducedLaplacian

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CodeLaplacian
attribute [-instance] _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem336

open scoped Matrix

variable {G : GraphCode} {K : FiniteSubgraphCode}

theorem code_edgeAdj_iff (hK : IsFiniteConnectedSubgraph G K) (u v : K.1) :
    ReducedLaplacian.EdgeAdj (codeSource hK) (codeTarget hK) u v ↔
      SubgraphAdj K u.val v.val := by
  constructor
  · rintro ⟨e, h | h⟩
    · refine ⟨u.property, v.property, ?_⟩
      have hs := congrArg Subtype.val h.1
      have ht := congrArg Subtype.val h.2
      change e.val.1 = u.val at hs
      change e.val.2 = v.val at ht
      rw [← hs, ← ht]
      have hlt := (hK.2.1 e.val e.property).2.2.1
      simpa only [rawPair, ite_eq_left hlt, Prod.mk.eta] using e.property
    · refine ⟨u.property, v.property, ?_⟩
      have hs := congrArg Subtype.val h.1
      have ht := congrArg Subtype.val h.2
      change e.val.1 = v.val at hs
      change e.val.2 = u.val at ht
      rw [← hs, ← ht]
      have hlt := (hK.2.1 e.val e.property).2.2.1
      have hnot : ¬e.val.2 < e.val.1 := Nat.not_lt.mpr (Nat.le_of_lt hlt)
      simpa only [rawPair, ite_eq_right hnot, Prod.mk.eta] using e.property
  · intro h
    refine ⟨⟨rawPair u.val v.val, h.2.2⟩, ?_⟩
    by_cases huv : u.val < v.val
    · left
      constructor <;> apply Subtype.ext <;> simp [codeSource, codeTarget, rawPair, huv]
    · right
      constructor <;> apply Subtype.ext <;> simp [codeSource, codeTarget, rawPair, huv]

theorem code_endpoints_connected (hK : IsFiniteConnectedSubgraph G K) :
    ReducedLaplacian.Connected (codeSource hK) (codeTarget hK) := by
  intro u v
  have liftPath {a b : ℕ} (hab : Relation.ReflTransGen (SubgraphAdj K) a b) :
      ∀ (ha : a ∈ K.1) (hb : b ∈ K.1),
        Relation.ReflTransGen
          (ReducedLaplacian.EdgeAdj (codeSource hK) (codeTarget hK))
          (⟨a, ha⟩ : K.1) (⟨b, hb⟩ : K.1) := by
    induction hab with
    | refl => intro _ _; exact .refl
    | @tail b c hab hbc ih =>
      intro ha hc
      exact (ih ha hbc.1).tail
        ((code_edgeAdj_iff hK ⟨b, hbc.1⟩ ⟨c, hc⟩).2 hbc)
  exact liftPath (hK.2.2 u.val u.property v.val v.property) u.property v.property

theorem codeWeightedLaplacian_det_ne_zero (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (w : K.2 → ℝ) (hw : ∀ e, 0 < w e) :
    (codeWeightedLaplacian hK root w).det ≠ 0 :=
  ReducedLaplacian.weightedLaplacian_det_ne_zero
    (codeSource hK) (codeTarget hK) root w (code_endpoints_connected hK) hw

end Problem336

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteIncidenceBridge
attribute [-instance] _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336.FiniteIncidence

theorem edgeAdj_iff_treeAdj (V : Finset ℕ) (T : Finset (ℕ × ℕ))
    (h : ValidEdges V T) (u v : V) :
    ReducedLaplacian.EdgeAdj (src V T h) (dst V T h) u v ↔
      TreeAdj T u.val v.val := by
  constructor
  · rintro ⟨e, he | he⟩
    · have h1 := congrArg Subtype.val he.1
      have h2 := congrArg Subtype.val he.2
      change e.val.1 = u.val at h1
      change e.val.2 = v.val at h2
      change rawPair u.val v.val ∈ T
      rw [← h1, ← h2]
      simp [rawPair, (h e.val e.property).2.2, e.property]
    · have h1 := congrArg Subtype.val he.1
      have h2 := congrArg Subtype.val he.2
      change e.val.1 = v.val at h1
      change e.val.2 = u.val at h2
      change rawPair u.val v.val ∈ T
      rw [← h1, ← h2]
      simp [rawPair, Nat.not_lt_of_ge (le_of_lt (h e.val e.property).2.2), e.property]
  · intro ht
    change rawPair u.val v.val ∈ T at ht
    by_cases huv : u.val < v.val
    · refine ⟨⟨(u.val, v.val), by simpa [rawPair, huv] using ht⟩, Or.inl ?_⟩
      exact ⟨Subtype.ext rfl, Subtype.ext rfl⟩
    · refine ⟨⟨(v.val, u.val), by simpa [rawPair, huv] using ht⟩, Or.inr ?_⟩
      exact ⟨Subtype.ext rfl, Subtype.ext rfl⟩

theorem treeAdj_endpoints_mem {V : Finset ℕ} {T : Finset (ℕ × ℕ)}
    (h : ValidEdges V T) {u v : ℕ} (huv : TreeAdj T u v) :
    u ∈ V ∧ v ∈ V := by
  have hm := h (rawPair u v) huv
  by_cases hlt : u < v
  · simpa [rawPair, hlt] using And.intro hm.1 hm.2.1
  · simpa [rawPair, hlt] using And.intro hm.2.1 hm.1

theorem treePath_endpoint_mem {V : Finset ℕ} {T : Finset (ℕ × ℕ)}
    (h : ValidEdges V T) {u v : ℕ} (hu : u ∈ V)
    (hp : Relation.ReflTransGen (TreeAdj T) u v) : v ∈ V := by
  induction hp with
  | refl => exact hu
  | tail _ hbc _ => exact (treeAdj_endpoints_mem h hbc).2

theorem treePath_lift {V : Finset ℕ} {T : Finset (ℕ × ℕ)}
    (h : ValidEdges V T) {u v : ℕ} (hu : u ∈ V) (hv : v ∈ V)
    (hp : Relation.ReflTransGen (TreeAdj T) u v) :
    Relation.ReflTransGen (ReducedLaplacian.EdgeAdj (src V T h) (dst V T h))
      ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction hp with
  | refl => exact .refl
  | @tail b c hab hbc ih =>
      have hb : b ∈ V := treePath_endpoint_mem h hu hab
      exact (ih hb).tail ((edgeAdj_iff_treeAdj V T h ⟨b, hb⟩ ⟨c, hv⟩).mpr hbc)

theorem connected_iff_treePaths (V : Finset ℕ) (T : Finset (ℕ × ℕ))
    (h : ValidEdges V T) :
    ReducedLaplacian.Connected (src V T h) (dst V T h) ↔
      ∀ u ∈ V, ∀ v ∈ V, Relation.ReflTransGen (TreeAdj T) u v := by
  constructor
  · intro hc u hu v hv
    exact Relation.ReflTransGen.lift Subtype.val
      (fun a b hab => (edgeAdj_iff_treeAdj V T h a b).mp hab) _ _
      (hc ⟨u, hu⟩ ⟨v, hv⟩)
  · intro hc u v
    exact treePath_lift h u.property v.property (hc u.val u.property v.val v.property)

theorem treeOn_iff_connected {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) {T : Finset (ℕ × ℕ)} (hT : T ⊆ K.2) :
    TreeOn K T ↔ T.card + 1 = K.1.card ∧
      ReducedLaplacian.Connected
        (src K.1 T (validEdges_of_subgraph hK hT))
        (dst K.1 T (validEdges_of_subgraph hK hT)) := by
  rw [connected_iff_treePaths]
  exact ⟨fun ht => ht.2, fun ht => ⟨hT, ht⟩⟩

end Problem336.FiniteIncidence

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_DisconnectedIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix

namespace Problem336.IncidenceDisconnected

variable {V E : Type*}

theorem reachable_endpoints_iff (src dst : E → V) (r : V) (e : E) :
    Relation.ReflTransGen (EndpointAdj src dst) r (src e) ↔
      Relation.ReflTransGen (EndpointAdj src dst) r (dst e) := by
  constructor
  · intro h
    exact h.tail ⟨e, Or.inl ⟨rfl, rfl⟩⟩
  · intro h
    exact h.tail ⟨e, Or.inr ⟨rfl, rfl⟩⟩

variable [Fintype V] [DecidableEq V]

theorem sum_reduced_indicator (r : V) (f : V → ℝ) (hr : f r = 0) (v : V) :
    (∑ i : {v : V // v ≠ r}, f i.1 * (if i.1 = v then 1 else 0)) = f v := by
  by_cases hv : v = r
  · subst v
    rw [hr]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [ite_eq_right i.property, mul_zero]
  · have heq (i : {v : V // v ≠ r}) : i.1 = v ↔ i = ⟨v, hv⟩ :=
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp only [mul_ite, mul_one, mul_zero, heq]
    simp

theorem vecMul_reducedIncidence (r : V) (src dst : E → V)
    (f : V → ℝ) (hr : f r = 0) :
    (fun i : {v : V // v ≠ r} => f i.1) ᵥ* reducedIncidence r src dst =
      fun e => f (src e) - f (dst e) := by
  ext e
  simp only [Matrix.vecMul, dotProduct, reducedIncidence, mul_sub, Finset.sum_sub_distrib]
  rw [sum_reduced_indicator r f hr, sum_reduced_indicator r f hr]

theorem exists_nonzero_vecMul_reducedIncidence_eq_zero
    (r : V) (src dst : E → V)
    (hdis : ¬ ∀ v, Relation.ReflTransGen (EndpointAdj src dst) r v) :
    ∃ f : {v : V // v ≠ r} → ℝ, f ≠ 0 ∧ f ᵥ* reducedIncidence r src dst = 0 := by
  classical
  obtain ⟨v, hv⟩ := not_forall.mp hdis
  let f : V → ℝ := fun w => if Relation.ReflTransGen (EndpointAdj src dst) r w then 0 else 1
  have hr : f r = 0 := by simp [f, Relation.ReflTransGen.refl]
  have hvr : v ≠ r := by
    intro heq
    subst v
    exact hv Relation.ReflTransGen.refl
  refine ⟨fun w => f w.1, ?_, ?_⟩
  · intro hz
    have h := congr_fun hz ⟨v, hvr⟩
    simp [f, hv] at h
  · rw [vecMul_reducedIncidence r src dst f hr]
    funext e
    have heq := reachable_endpoints_iff src dst r e
    simp only [f, heq, sub_self, Pi.zero_apply]

theorem det_reducedIncidence_eq_zero_of_not_connected
    (r : V) (src dst : {v : V // v ≠ r} → V)
    (hdis : ¬ ∀ v, Relation.ReflTransGen (EndpointAdj src dst) r v) :
    (reducedIncidence r src dst).det = 0 := by
  exact Matrix.exists_vecMul_eq_zero_iff.mp
    (exists_nonzero_vecMul_reducedIncidence_eq_zero r src dst hdis)

end Problem336.IncidenceDisconnected

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_IncidenceUnimodular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix

namespace Problem336.Incidence

variable {V E : Type*} [DecidableEq V]

lemma sum_endpoint_indicator {n : ℕ} (f : Fin n → V)
    (hf : Function.Injective f) (v : V) :
    (∑ i, if f i = v then (1 : ℝ) else 0) =
      if ∃ i, f i = v then 1 else 0 := by
  classical
  by_cases hv : ∃ i, f i = v
  · obtain ⟨i, rfl⟩ := hv
    simp [hf.eq_iff]
  · rw [ite_eq_right hv]
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (fun hi => hv ⟨i, hi⟩)

lemma incidence_column_sum {n : ℕ} (src dst : E → V)
    (f : Fin n → V) (hf : Function.Injective f) (e : E) :
    (∑ i, signedIncidence src dst (f i) e) =
      (if ∃ i, f i = src e then 1 else 0) -
      (if ∃ i, f i = dst e then 1 else 0) := by
  simp only [signedIncidence, Finset.sum_sub_distrib,
    sum_endpoint_indicator f hf]

lemma incidence_source_only {n : ℕ} (src dst : E → V)
    (f : Fin n → V) (hf : Function.Injective f) (e : E)
    (i : Fin n) (hsrc : f i = src e) (hdst : ¬ ∃ k, f k = dst e) :
    (fun k => signedIncidence src dst (f k) e) = Pi.single i 1 := by
  ext k
  have hkd : f k ≠ dst e := fun hk => hdst ⟨k, hk⟩
  simp [signedIncidence, ← hsrc, hf.eq_iff, hkd, Pi.single_apply]

lemma incidence_target_only {n : ℕ} (src dst : E → V)
    (f : Fin n → V) (hf : Function.Injective f) (e : E)
    (i : Fin n) (hdst : f i = dst e) (hsrc : ¬ ∃ k, f k = src e) :
    (fun k => signedIncidence src dst (f k) e) = Pi.single i (-1) := by
  ext k
  have hks : f k ≠ src e := fun hk => hsrc ⟨k, hk⟩
  simp [signedIncidence, ← hdst, hf.eq_iff, hks, Pi.single_apply]
  split_ifs <;> norm_num

theorem signedIncidence_minor_mem_sign (src dst : E → V) (n : ℕ)
    (f : Fin n → V) (g : Fin n → E) (hf : Function.Injective f) :
    ((signedIncidence src dst).submatrix f g).det ∈ Set.range SignType.cast := by
  classical
  induction n with
  | zero =>
      exact ⟨1, by simp⟩
  | succ n ih =>
      let A := (signedIncidence src dst).submatrix f g
      by_cases hsplit : ∃ j,
          ((∃ i, f i = src (g j)) ∧ ¬ ∃ i, f i = dst (g j)) ∨
          ((∃ i, f i = dst (g j)) ∧ ¬ ∃ i, f i = src (g j))
      · obtain ⟨j, hj⟩ := hsplit
        have hsingle : ∃ i : Fin (n + 1), ∃ s : SignType,
            (fun k => A k j) = Pi.single i (s.cast : ℝ) := by
          rcases hj with ⟨⟨i, hi⟩, hother⟩ | ⟨⟨i, hi⟩, hother⟩
          · exact ⟨i, 1, incidence_source_only src dst f hf (g j) i hi hother⟩
          · refine ⟨i, -1, ?_⟩
            simpa [A] using incidence_target_only src dst f hf (g j) i hi hother
        obtain ⟨i, s, hs⟩ := hsingle
        have hdet := Matrix.det_succ_column A j
        rw [Fintype.sum_eq_single i] at hdet
        · have hii : A i j = s.cast := by
            simpa using congrFun hs i
          rw [hii] at hdet
          change A.det ∈ Set.range SignType.cast
          rw [hdet]
          change _ ∈ MonoidHom.mrange SignType.castHom.toMonoidHom
          refine mul_mem (mul_mem ?_ (Set.mem_range_self s)) ?_
          · apply pow_mem
            exact ⟨-1, by simp⟩
          · exact ih (f ∘ i.succAbove) (g ∘ j.succAbove)
              (hf.comp Fin.succAbove_right_injective)
        · intro k hki
          have hkj : A k j = 0 := by
            simpa [Pi.single_eq_of_ne hki] using congrFun hs k
          simp [hkj]
      · have hsum : ∀ j : Fin (n + 1), ∑ i, A i j = 0 := by
          intro j
          have hiff : (∃ i, f i = src (g j)) ↔ (∃ i, f i = dst (g j)) := by
            constructor
            · intro h
              by_contra hn
              exact hsplit ⟨j, Or.inl ⟨h, hn⟩⟩
            · intro h
              by_contra hn
              exact hsplit ⟨j, Or.inr ⟨h, hn⟩⟩
          change (∑ i, signedIncidence src dst (f i) (g j)) = 0
          rw [incidence_column_sum src dst f hf]
          simp only [hiff, sub_self]
        have hdet : A.det = 0 := by
          rw [Matrix.det_eq_sum_column_mul_submatrix_succAbove_succAbove_det
            A 0 0 (fun j _ => hsum j), hsum 0, mul_zero, zero_mul]
        exact ⟨0, by simpa using hdet.symm⟩

theorem signedIncidence_isTotallyUnimodular (src dst : E → V) :
    (signedIncidence src dst).IsTotallyUnimodular := by
  intro n f g hf _
  exact signedIncidence_minor_mem_sign src dst n f g hf

theorem signedIncidence_submatrix_det_mem_sign {ι : Type*}
    [Fintype ι] [DecidableEq ι] (src dst : E → V)
    (f : ι → V) (g : ι → E) :
    ((signedIncidence src dst).submatrix f g).det ∈ Set.range SignType.cast := by
  exact (Matrix.isTotallyUnimodular_iff_fintype _).mp
    (signedIncidence_isTotallyUnimodular src dst) ι f g

theorem signedIncidence_det_sq_eq_one_of_ne_zero {ι : Type*}
    [Fintype ι] [DecidableEq ι] (src dst : E → V)
    (f : ι → V) (g : ι → E)
    (hdet : ((signedIncidence src dst).submatrix f g).det ≠ 0) :
    (((signedIncidence src dst).submatrix f g).det)^2 = 1 := by
  obtain ⟨s, hs⟩ := signedIncidence_submatrix_det_mem_sign src dst f g
  rw [← hs] at hdet ⊢
  cases s with
  | zero => exact (hdet rfl).elim
  | neg => norm_num [SignType.cast]
  | pos => norm_num [SignType.cast]

end Problem336.Incidence

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_IncidenceMinorClassification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix

namespace Problem336.IncidenceMinor

open ReducedLaplacian Classical

variable {V E : Type*}

theorem connected_iff_root_reachable (src dst : E → V) (root : V) :
    Connected src dst ↔
      ∀ v, Relation.ReflTransGen (EdgeAdj src dst) root v := by
  constructor
  · intro h v
    exact h root v
  · intro h
    let : Std.Symm (EdgeAdj src dst) := ⟨fun _ _ ⟨e, he⟩ => ⟨e, he.symm⟩⟩
    intro u v
    exact (symm (h u)).trans (h v)

variable [Fintype V] [DecidableEq V]

theorem reducedGradient_det_ne_zero (root : V)
    (src dst : {v : V // v ≠ root} → V) (hconn : Connected src dst) :
    (reducedGradient src dst root).det ≠ 0 := by
  have hu : IsUnit (reducedGradient src dst root) :=
    Matrix.mulVec_injective_iff_isUnit.mp
      (reducedGradient_mulVec_injective src dst root hconn)
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)

theorem reducedGradient_det_eq_zero (root : V)
    (src dst : {v : V // v ≠ root} → V) (hconn : ¬Connected src dst) :
    (reducedGradient src dst root).det = 0 := by
  have hroot : ¬∀ v, Relation.ReflTransGen (EdgeAdj src dst) root v :=
    fun h => hconn ((connected_iff_root_reachable src dst root).mpr h)
  change ((IncidenceDisconnected.reducedIncidence root src dst)ᵀ).det = 0
  rw [Matrix.det_transpose]
  exact IncidenceDisconnected.det_reducedIncidence_eq_zero_of_not_connected
    root src dst hroot

theorem reducedGradient_det_sq_eq_indicator (root : V)
    (src dst : {v : V // v ≠ root} → V) :
    (reducedGradient src dst root).det ^ 2 =
      if Connected src dst then 1 else 0 := by
  classical
  by_cases hc : Connected src dst
  · rw [ite_eq_left hc]
    have hd := reducedGradient_det_ne_zero root src dst hc
    have hs := Incidence.signedIncidence_det_sq_eq_one_of_ne_zero
      src dst (fun v : {v : V // v ≠ root} => v.val) id
      (by
        change ((reducedGradient src dst root)ᵀ).det ≠ 0
        simpa only [Matrix.det_transpose] using hd)
    change ((reducedGradient src dst root)ᵀ).det ^ 2 = 1 at hs
    simpa only [Matrix.det_transpose] using hs
  · rw [ite_eq_right hc, reducedGradient_det_eq_zero root src dst hc]
    norm_num

theorem selected_minor_det_sq_eq_indicator (src dst : E → V) (root : V)
    (f : {v : V // v ≠ root} → E) :
    (((reducedGradient src dst root)ᵀ).submatrix id f).det ^ 2 =
      if Connected (src ∘ f) (dst ∘ f) then 1 else 0 := by
  have heq : ((reducedGradient src dst root)ᵀ).submatrix id f =
      (reducedGradient (src ∘ f) (dst ∘ f) root)ᵀ := rfl
  rw [heq, Matrix.det_transpose, reducedGradient_det_sq_eq_indicator]

end Problem336.IncidenceMinor

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CodedIncidenceMinors
attribute [-instance] _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix
open Classical

namespace Problem336.FiniteIncidence

theorem edgeAdj_comp_equiv {V E F : Type*} (s t : E → V) (e : F ≃ E) (u v : V) :
    ReducedLaplacian.EdgeAdj (s ∘ e) (t ∘ e) u v ↔
      ReducedLaplacian.EdgeAdj s t u v := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨e a, ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨e.symm a, ?_⟩
    simpa only [Function.comp_apply, e.apply_symm_apply] using ha

theorem connected_comp_equiv {V E F : Type*} (s t : E → V) (e : F ≃ E) :
    ReducedLaplacian.Connected (s ∘ e) (t ∘ e) ↔
      ReducedLaplacian.Connected s t := by
  have hrel : ReducedLaplacian.EdgeAdj (s ∘ e) (t ∘ e) =
      ReducedLaplacian.EdgeAdj s t :=
    funext fun u => funext fun v => propext (edgeAdj_comp_equiv s t e u v)
  simp only [ReducedLaplacian.Connected, hrel]

theorem selectedEdges_subset {K : FiniteSubgraphCode} (s : Finset K.2) :
    selectedEdges s ⊆ K.2 := by
  intro p hp
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hp
  exact a.property

theorem selectedEdges_card_add_one {K : FiniteSubgraphCode} (root : K.1)
    (s : CauchyBinet.ColumnSets {v : K.1 // v ≠ root} K.2) :
    (selectedEdges s.val).card + 1 = K.1.card := by
  rw [selectedEdges_card, (Finset.mem_powersetCard.mp s.property).2,
    Fintype.card_subtype_compl (fun v : K.1 => v = root), Fintype.card_coe,
    Fintype.card_subtype_eq]
  have hpos : 0 < K.1.card := Finset.card_pos.mpr ⟨root.val, root.property⟩
  omega

theorem columnMinor_det_sq_eq_treeOn
    {G : GraphCode} {K : FiniteSubgraphCode} (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1)
    (s : CauchyBinet.ColumnSets {v : K.1 // v ≠ root} K.2) :
    (CauchyBinet.columnMinor
      (ReducedLaplacian.reducedGradient
        (src K.1 K.2 (validEdges_of_subgraph hK (fun _ hp => hp)))
        (dst K.1 K.2 (validEdges_of_subgraph hK (fun _ hp => hp))) root).transpose s).det ^ 2 =
      if TreeOn K (selectedEdges s.val) then 1 else 0 := by
  let hv := validEdges_of_subgraph hK (fun _ hp => hp)
  let A := (ReducedLaplacian.reducedGradient (src K.1 K.2 hv) (dst K.1 K.2 hv) root).transpose
  let ix := CauchyBinet.columnIndexEquiv s
  let f : {v : K.1 // v ≠ root} → K.2 := fun i => (ix.symm i).val
  have hdet : (CauchyBinet.columnMinor A s).det = (A.submatrix id f).det := by
    calc
      _ = ((CauchyBinet.columnMinor A s).submatrix ix.symm ix.symm).det :=
        (Matrix.det_submatrix_equiv_self ix.symm _).symm
      _ = _ := by
        congr 1
        ext i j
        simp [CauchyBinet.columnMinor, Matrix.submatrix, ix, f]
  change (CauchyBinet.columnMinor A s).det ^ 2 = _
  rw [hdet]
  change (((ReducedLaplacian.reducedGradient
    (src K.1 K.2 hv) (dst K.1 K.2 hv) root).transpose).submatrix id f).det ^ 2 = _
  rw [IncidenceMinor.selected_minor_det_sq_eq_indicator]
  let hs := validEdges_of_subgraph hK (selectedEdges_subset s.val)
  let e : {v : K.1 // v ≠ root} ≃ selectedEdges s.val :=
    ix.symm.trans (selectedEdgeEquiv s.val)
  have hc : ReducedLaplacian.Connected (src K.1 K.2 hv ∘ f) (dst K.1 K.2 hv ∘ f) ↔
      ReducedLaplacian.Connected (src K.1 (selectedEdges s.val) hs)
        (dst K.1 (selectedEdges s.val) hs) := by
    change ReducedLaplacian.Connected
      (src K.1 (selectedEdges s.val) hs ∘ e)
      (dst K.1 (selectedEdges s.val) hs ∘ e) ↔ _
    exact connected_comp_equiv _ _ e
  rw [hc]
  have ht : TreeOn K (selectedEdges s.val) ↔
      ReducedLaplacian.Connected (src K.1 (selectedEdges s.val) hs)
        (dst K.1 (selectedEdges s.val) hs) := by
    rw [treeOn_iff_connected hK (selectedEdges_subset s.val)]
    exact and_iff_right (selectedEdges_card_add_one root s)
  simp only [← ht]

end Problem336.FiniteIncidence

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_SubtypeSubsetSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.SubtypeSubsetSums

variable {α : Type*}

theorem sum_powersetCard {R : Type*} [AddCommMonoid R]
    (s : Finset α) (k : ℕ) (F : Finset α → R) :
    (∑ T ∈ (Finset.univ : Finset s).powersetCard k, F (forget s T)) =
      ∑ T ∈ s.powersetCard k, F T := by
  have hm := Finset.powersetCard_map
    (Function.Embedding.subtype (· ∈ s)) k (Finset.univ : Finset s)
  have hu : (Finset.univ : Finset s).map
      (Function.Embedding.subtype (· ∈ s)) = s := forget_univ s
  rw [hu] at hm
  rw [hm, Finset.sum_map]
  rfl

theorem prod_forget {R : Type*} [CommMonoid R]
    (s : Finset α) (T : Finset s) (c : α → R) :
    (∏ e ∈ forget s T, c e) = ∏ e ∈ T, c e.val := by
  exact Finset.prod_map T (Function.Embedding.subtype (· ∈ s)) c

theorem sum_powersetCard_filter {R : Type*} [AddCommMonoid R]
    (s : Finset α) (k : ℕ) (P : Finset α → Prop) [DecidablePred P]
    (F : Finset α → R) :
    (∑ T ∈ ((Finset.univ : Finset s).powersetCard k).filter (fun T => P (forget s T)),
      F (forget s T)) =
      ∑ T ∈ (s.powersetCard k).filter P, F T := by
  simp only [Finset.sum_filter]
  exact sum_powersetCard s k (fun T => if P T then F T else 0)

end Problem336.SubtypeSubsetSums

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CodedMatrixTree
attribute [-instance] _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix
open Classical

namespace Problem336

variable {G : GraphCode} {K : FiniteSubgraphCode}

theorem spanningTrees_eq_powersetCard_filter (root : K.1) :
    spanningTrees K = (K.2.powersetCard (Fintype.card {v : K.1 // v ≠ root})).filter
      (TreeOn K) := by
  have hc : Fintype.card {v : K.1 // v ≠ root} = K.1.card - 1 := by
    rw [Fintype.card_subtype_compl (fun v : K.1 => v = root),
      Fintype.card_coe, Fintype.card_subtype_eq]
  ext T
  simp only [spanningTrees, Finset.mem_filter, Finset.mem_powerset,
    Finset.mem_powersetCard]
  constructor
  · rintro ⟨hsub, ht⟩
    exact ⟨⟨hsub, by rw [hc]; have := ht.2.1; omega⟩, ht⟩
  · rintro ⟨⟨hsub, _⟩, ht⟩
    exact ⟨hsub, ht⟩

theorem codeIncidence_minor_sq (hK : IsFiniteConnectedSubgraph G K) (root : K.1)
    (s : CauchyBinet.ColumnSets {v : K.1 // v ≠ root} K.2) :
    (CauchyBinet.columnMinor (codeIncidence hK root) s).det ^ 2 =
      if TreeOn K (SubtypeSubsetSums.forget K.2 s.val) then 1 else 0 :=
  FiniteIncidence.columnMinor_det_sq_eq_treeOn hK root s

theorem codeIncidence_weighted_partition {R : Type*} [CommRing R]
    (hK : IsFiniteConnectedSubgraph G K) (root : K.1)
    (f : ℝ →+* R) (c : (ℕ × ℕ) → R) :
    Matrix.det ((codeIncidence hK root).map f *
      Matrix.diagonal (fun e : K.2 => c e.val) *
      ((codeIncidence hK root).map f).transpose) =
      ∑ T ∈ spanningTrees K, ∏ p ∈ T, c p := by
  rw [CauchyBinet.det_weighted_gram_map_eq_sum_filter
    (codeIncidence hK root) f (fun e : K.2 => c e.val)
    (fun s => TreeOn K (SubtypeSubsetSums.forget K.2 s))
    (codeIncidence_minor_sq hK root)]
  calc
    _ = ∑ s ∈ ((Finset.univ : Finset K.2).powersetCard
          (Fintype.card {v : K.1 // v ≠ root})).filter
          (fun s => TreeOn K (SubtypeSubsetSums.forget K.2 s)),
        ∏ p ∈ SubtypeSubsetSums.forget K.2 s, c p := by
      apply Finset.sum_congr rfl
      intro s _
      exact (SubtypeSubsetSums.prod_forget K.2 s c).symm
    _ = ∑ T ∈ (K.2.powersetCard
          (Fintype.card {v : K.1 // v ≠ root})).filter (TreeOn K),
        ∏ p ∈ T, c p :=
      SubtypeSubsetSums.sum_powersetCard_filter K.2 _ (TreeOn K) (fun T => ∏ p ∈ T, c p)
    _ = _ := by rw [← spanningTrees_eq_powersetCard_filter root]

theorem codeWeightedLaplacian_tree_partition
    (hK : IsFiniteConnectedSubgraph G K) (root : K.1)
    (c : (ℕ × ℕ) → ℝ) :
    (codeWeightedLaplacian hK root (fun e => c e.val)).det =
      ∑ T ∈ spanningTrees K, ∏ p ∈ T, c p := by
  simpa only [RingHom.coe_id, Matrix.map_id, codeIncidence, Matrix.transpose_transpose,
    codeWeightedLaplacian, ReducedLaplacian.weightedLaplacian] using
    codeIncidence_weighted_partition hK root (RingHom.id ℝ) c

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_InclusionPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Polynomial Matrix
open Polynomial Finset

namespace Problem336
namespace InclusionPolynomial

variable {E R : Type*} [DecidableEq E] [CommRing R]

theorem coeff_marked_power (T F : Finset E) :
    ((1 + X : R[X]) ^ (T ∩ F).card).coeff F.card = if F ⊆ T then 1 else 0 := by
  rw [Polynomial.coeff_one_add_X_pow]
  by_cases h : F ⊆ T
  · have hI : T ∩ F = F := Finset.inter_eq_right.mpr h
    simp [h, hI]
  · have hlt : (T ∩ F).card < F.card := by
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.inter_subset_right, ?_⟩
      intro heq
      apply h
      rw [← heq]
      exact Finset.inter_subset_left
    simp [h, Nat.choose_eq_zero_of_lt hlt]

theorem coeff_partition (trees : Finset (Finset E)) (w : Finset E → R) (F : Finset E) :
    (∑ T ∈ trees, C (w T) * (1 + X : R[X]) ^ (T ∩ F).card).coeff F.card =
      ∑ T ∈ trees with F ⊆ T, w T := by
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, coeff_marked_power]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> simp

theorem coeff_det_one_add_X_top {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι R) :
    ((1 + (X : R[X]) • K.map C).det).coeff (Fintype.card ι) = K.det := by
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  simp only [← Finset.card_univ (α := ι), Finset.powersetCard_self,
    Finset.sum_singleton]
  exact Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (fun i : ι => Finset.mem_univ i)) K

end InclusionPolynomial
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PolynomialGramUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Matrix

namespace Problem336.Determinantal

variable {ν κ : Type*} [Fintype ν] [DecidableEq ν] [Fintype κ] [DecidableEq κ]

theorem map_nonsing_inv_of_isUnit {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (L : Matrix ν ν R) (hL : IsUnit L.det) :
    (L.map φ)⁻¹ = L⁻¹.map φ := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hL]
  simp

theorem det_polynomial_rank_update
    (L : Matrix ν ν ℝ) (hL : IsUnit L.det)
    (U : Matrix ν κ ℝ) (V : Matrix κ ν ℝ) :
    (L.map Polynomial.C + (Polynomial.X : Polynomial ℝ) • (U * V).map Polynomial.C).det =
      Polynomial.C L.det *
        (1 + (Polynomial.X : Polynomial ℝ) • (V * L⁻¹ * U).map Polynomial.C).det := by
  have hdet : (L.map Polynomial.C).det = Polynomial.C L.det := by
    exact (Polynomial.C.map_det L).symm
  have hLC : IsUnit (L.map Polynomial.C).det := by
    rw [hdet]
    exact hL.map (Polynomial.C : ℝ →+* Polynomial ℝ)
  have h := Matrix.det_add_mul ((Polynomial.X : Polynomial ℝ) • U.map Polynomial.C)
    (V.map Polynomial.C) hLC
  rw [map_nonsing_inv_of_isUnit Polynomial.C L hL] at h
  simpa only [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul,
    hdet] using h

theorem det_polynomial_weighted_columns
    (L : Matrix ν ν ℝ) (hL : IsUnit L.det)
    (A : Matrix ν κ ℝ) (c : κ → ℝ) :
    (L.map Polynomial.C + (Polynomial.X : Polynomial ℝ) •
      (A * Matrix.diagonal c * A.transpose).map Polynomial.C).det =
      Polynomial.C L.det *
        (1 + (Polynomial.X : Polynomial ℝ) •
          (Matrix.diagonal c * (A.transpose * L⁻¹ * A)).map Polynomial.C).det := by
  simpa only [Matrix.mul_assoc] using
    det_polynomial_rank_update L hL A (Matrix.diagonal c * A.transpose)

end Problem336.Determinantal

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_MarkedGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix

namespace Problem336.Determinantal

variable {ν ι R : Type*} [finiteRows : Fintype ν] [decidableRows : DecidableEq ν]
variable [Fintype ι] [DecidableEq ι] [CommRing R]

omit [Fintype ι] in

theorem prod_marked_weights (c : ι → R) (T S : Finset ι) (z : R) :
    (∏ e ∈ T, c e * (if e ∈ S then 1 + z else 1)) =
      (∏ e ∈ T, c e) * (1 + z) ^ (T ∩ S).card := by
  rw [Finset.prod_mul_distrib]
  congr 1
  simp only [Finset.prod_ite, Finset.prod_const, Finset.filter_mem_eq_inter,
    one_pow, mul_one]

omit finiteRows decidableRows in
private theorem gram_entry [Fintype ν] [DecidableEq ν] {E : Type*}
    [Fintype E] [DecidableEq E]
    (A : Matrix ν E R) (c : E → R) (i j : ν) :
    (A * Matrix.diagonal c * A.transpose) i j = ∑ e, A i e * c e * A j e := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

theorem gram_marked_diagonal (A : Matrix ν ι R) (c : ι → R)
    (S : Finset ι) (z : R) :
    A * Matrix.diagonal (fun e => c e * (if e ∈ S then 1 + z else 1)) * A.transpose =
      A * Matrix.diagonal c * A.transpose +
        z • (A.submatrix id (Subtype.val : S → ι) *
          Matrix.diagonal (fun e : S => c e) *
          (A.submatrix id (Subtype.val : S → ι)).transpose) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, gram_entry,
    Matrix.submatrix_apply, id_eq]
  have hterm (e : ι) : A i e * (c e * (if e ∈ S then 1 + z else 1)) * A j e =
      A i e * c e * A j e + (if e ∈ S then z * (A i e * c e * A j e) else 0) := by
    split_ifs <;> ring
  have hsub : (∑ e : S, A i e * c e * A j e) =
      ∑ e ∈ S, A i e * c e * A j e :=
    Finset.sum_coe_sort S (fun e : ι => A i e * c e * A j e)
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, hsub]
  congr 1
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

theorem det_marked_weighted_gram (A : Matrix ν ι ℝ) (c : ι → ℝ)
    (hA : IsUnit (A * Matrix.diagonal c * A.transpose).det) (S : Finset ι) :
    (A.map Polynomial.C * Matrix.diagonal (fun e =>
      Polynomial.C (c e) * (if e ∈ S then 1 + (Polynomial.X : Polynomial ℝ) else 1)) *
      (A.map Polynomial.C).transpose).det =
      Polynomial.C (A * Matrix.diagonal c * A.transpose).det *
        (1 + (Polynomial.X : Polynomial ℝ) •
          (Matrix.diagonal (fun e : S => c e) *
            ((A.submatrix id (Subtype.val : S → ι)).transpose *
              (A * Matrix.diagonal c * A.transpose)⁻¹ *
              A.submatrix id (Subtype.val : S → ι))).map Polynomial.C).det := by
  have hm := gram_marked_diagonal (A.map Polynomial.C)
    (fun e => Polynomial.C (c e)) S (Polynomial.X : Polynomial ℝ)
  have hm' : A.map Polynomial.C * Matrix.diagonal (fun e =>
      Polynomial.C (c e) * (if e ∈ S then 1 + (Polynomial.X : Polynomial ℝ) else 1)) *
      (A.map Polynomial.C).transpose =
      (A * Matrix.diagonal c * A.transpose).map Polynomial.C +
        (Polynomial.X : Polynomial ℝ) •
          (A.submatrix id (Subtype.val : S → ι) *
            Matrix.diagonal (fun e : S => c e) *
            (A.submatrix id (Subtype.val : S → ι)).transpose).map Polynomial.C := by
    simpa only [Matrix.map_mul, Matrix.diagonal_map (map_zero Polynomial.C),
      Matrix.transpose_map, Matrix.submatrix_map] using hm
  rw [hm']
  exact det_polynomial_weighted_columns _ hA _ _

end Problem336.Determinantal

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CodedInclusion
attribute [-instance] _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Polynomial Matrix
open Classical Polynomial

namespace Problem336

variable {G : GraphCode} {K : FiniteSubgraphCode}

theorem code_tree_marker_identity (hK : IsFiniteConnectedSubgraph G K) (root : K.1)
    (c : (ℕ × ℕ) → ℝ) (hc : ∀ e : K.2, 0 < c e.val) (S : Finset K.2) :
    (∑ T ∈ spanningTrees K, C (∏ p ∈ T, c p) *
      (1 + (X : ℝ[X])) ^ (T ∩ SubtypeSubsetSums.forget K.2 S).card) =
      C (∑ T ∈ spanningTrees K, ∏ p ∈ T, c p) *
        (1 + (X : ℝ[X]) • (codeTransferCurrent hK root c S).map C).det := by
  have hA : IsUnit ((codeIncidence hK root) *
      Matrix.diagonal (fun e : K.2 => c e.val) * (codeIncidence hK root).transpose).det := by
    apply isUnit_iff_ne_zero.mpr
    simpa only [codeIncidence, Matrix.transpose_transpose, codeWeightedLaplacian,
      ReducedLaplacian.weightedLaplacian] using
      codeWeightedLaplacian_det_ne_zero hK root (fun e => c e.val) hc
  have hp := codeIncidence_weighted_partition hK root C
    (fun p => C (c p) *
      (if p ∈ SubtypeSubsetSums.forget K.2 S then 1 + (X : ℝ[X]) else 1))
  simp only [SubtypeSubsetSums.mem_forget] at hp
  have hm := Determinantal.det_marked_weighted_gram
    (codeIncidence hK root) (fun e : K.2 => c e.val) hA S
  rw [hp] at hm
  have hZ : ((codeIncidence hK root) * Matrix.diagonal (fun e : K.2 => c e.val) *
      (codeIncidence hK root).transpose).det =
      ∑ T ∈ spanningTrees K, ∏ p ∈ T, c p := by
    exact codeWeightedLaplacian_tree_partition hK root c
  rw [hZ] at hm
  simpa only [Determinantal.prod_marked_weights, ← map_prod,
    codeTransferCurrent, codeWeightedLaplacian, ReducedLaplacian.weightedLaplacian,
    codeIncidence, Matrix.transpose_transpose, Matrix.mul_assoc] using hm

theorem code_tree_inclusion_mass (hK : IsFiniteConnectedSubgraph G K) (root : K.1)
    (c : (ℕ × ℕ) → ℝ) (hc : ∀ e : K.2, 0 < c e.val) (S : Finset K.2) :
    (∑ T ∈ (spanningTrees K).filter (fun T => SubtypeSubsetSums.forget K.2 S ⊆ T),
      ∏ p ∈ T, c p) =
      (∑ T ∈ spanningTrees K, ∏ p ∈ T, c p) * (codeTransferCurrent hK root c S).det := by
  have hp := congrArg (fun p : ℝ[X] => p.coeff (SubtypeSubsetSums.forget K.2 S).card)
    (code_tree_marker_identity hK root c hc S)
  rw [InclusionPolynomial.coeff_partition, Polynomial.coeff_C_mul] at hp
  have ht := InclusionPolynomial.coeff_det_one_add_X_top (codeTransferCurrent hK root c S)
  simp only [Fintype.card_coe, SubtypeSubsetSums.card_forget] at hp ht
  rwa [ht] at hp

theorem code_tree_inclusion_ratio (hK : IsFiniteConnectedSubgraph G K) (root : K.1)
    (c : (ℕ × ℕ) → ℝ) (hc : ∀ e : K.2, 0 < c e.val) (S : Finset K.2) :
    (∑ T ∈ (spanningTrees K).filter (fun T => SubtypeSubsetSums.forget K.2 S ⊆ T),
      ∏ p ∈ T, c p) / (∑ T ∈ spanningTrees K, ∏ p ∈ T, c p) =
      (codeTransferCurrent hK root c S).det := by
  have hZ : (∑ T ∈ spanningTrees K, ∏ p ∈ T, c p) ≠ 0 := by
    rw [← codeWeightedLaplacian_tree_partition hK root c]
    exact codeWeightedLaplacian_det_ne_zero hK root (fun e => c e.val) hc
  rw [code_tree_inclusion_mass hK root c hc S]
  exact mul_div_cancel_left₀ _ hZ

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteGradientResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.FiniteGradientResponse

variable {ι : Type*}

theorem abs_sum_mul_le (E : Finset ι) (row direction : ι → ℝ)
    (L D : ℝ) (hD : 0 ≤ D)
    (hrow : (∑ i ∈ E, |row i|) ≤ L)
    (hdir : ∀ i ∈ E, |direction i| ≤ D) :
    |∑ i ∈ E, row i * direction i| ≤ L * D := by
  calc
    |∑ i ∈ E, row i * direction i| ≤ ∑ i ∈ E, |row i * direction i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ E, |row i| * D := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hdir i hi) (abs_nonneg _)
    _ = (∑ i ∈ E, |row i|) * D := (Finset.sum_mul _ _ _).symm
    _ ≤ L * D := mul_le_mul_of_nonneg_right hrow hD

theorem response_le_of_line_derivative (E : Finset ι)
    (p : (ι → ℝ) → ℝ) (row : (ι → ℝ) → ι → ℝ)
    (h k : ι → ℝ) (L D : ℝ) (hD : 0 ≤ D)
    (hdir : ∀ i ∈ E, |k i - h i| ≤ D)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => p (segmentField h k s))
        (∑ i ∈ E, row (segmentField h k t) i * (k i - h i)) t)
    (hrow : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      (∑ i ∈ E, |row (segmentField h k t) i|) ≤ L) :
    |p k - p h| ≤ L * D := by
  have hbound : ‖p (segmentField h k 1) - p (segmentField h k 0)‖ ≤ L * D := by
    apply norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := fun s => p (segmentField h k s))
      (f' := fun t => ∑ i ∈ E, row (segmentField h k t) i * (k i - h i))
    · intro t ht
      exact (hderiv t ht).hasDerivWithinAt
    · intro t ht
      simpa only [Real.norm_eq_abs] using
        abs_sum_mul_le E (row (segmentField h k t)) (fun i => k i - h i)
          L D hD (hrow t ht) hdir
  simpa only [segmentField_one, segmentField_zero, Real.norm_eq_abs] using hbound

end Problem336.FiniteGradientResponse

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_TransferCurrent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Operator

namespace Problem336.TransferCurrent

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma bilinear_symmetric {M : Matrix n n ℝ} (hM : Mᵀ = M) (a b : n → ℝ) :
    bilinear M a b = bilinear M b a := by
  simpa [bilinear, hM] using Matrix.dotProduct_transpose_mulVec M a b

lemma inverse_symmetric {M : Matrix n n ℝ} (hM : Mᵀ = M) :
    (M⁻¹)ᵀ = M⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, hM]

omit [DecidableEq n] in
lemma bilinear_rankOne (M : Matrix n n ℝ) (a b : n → ℝ) :
    bilinear (M * Matrix.vecMulVec b b * M) a a =
      bilinear M a b * bilinear M b a := by
  simp [bilinear, ← Matrix.mulVec_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.mulVec_smul, dotProduct_smul, op_smul_eq_smul, mul_comm]

omit [DecidableEq n] in
lemma bilinear_neg (M : Matrix n n ℝ) (a b : n → ℝ) :
    bilinear (-M) a b = -bilinear M a b := by
  simp [bilinear, Matrix.neg_mulVec]

omit [DecidableEq n] in
lemma bilinear_smul (c : ℝ) (M : Matrix n n ℝ) (a b : n → ℝ) :
    bilinear (c • M) a b = c * bilinear M a b := by
  simp [bilinear, Matrix.smul_mulVec, dotProduct_smul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype n] [DecidableEq n] [DecidableEq ι] in
lemma laplacian_symmetric (a : ι → n → ℝ) (h : ι → ℝ) :
    (laplacian a h)ᵀ = laplacian a h := by
  simp [laplacian, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.transpose_vecMulVec]

attribute [local instance] OAI.Problem336.TransferCurrent.instTopologicalSpaceMatrixReal_solutions
omit [DecidableEq ι] in

lemma sum_weighted_transfer_sq (a : ι → n → ℝ) (h : ι → ℝ)
    (hL : IsUnit (laplacian a h)) (e : ι) :
    (∑ f, Real.exp (h f) * (bilinear (laplacian a h)⁻¹ (a e) (a f))^2) =
      bilinear (laplacian a h)⁻¹ (a e) (a e) := by
  let M := laplacian a h
  have hs : (M⁻¹)ᵀ = M⁻¹ := inverse_symmetric (laplacian_symmetric a h)
  have hterm (f : ι) :
      Real.exp (h f) * (bilinear M⁻¹ (a e) (a f))^2 =
      bilinear (M⁻¹ * (Real.exp (h f) • Matrix.vecMulVec (a f) (a f)) * M⁻¹)
        (a e) (a e) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, bilinear_smul, bilinear_rankOne,
      bilinear_symmetric hs (a f) (a e)]
    ring
  change (∑ f, Real.exp (h f) * (bilinear M⁻¹ (a e) (a f))^2) = _
  simp_rw [hterm]
  have hsum := map_sum (bilinearCLM (a e) (a e))
    (fun f => M⁻¹ * (Real.exp (h f) • Matrix.vecMulVec (a f) (a f)) * M⁻¹)
    Finset.univ
  simp only [bilinearCLM_apply] at hsum
  rw [← hsum, ← Matrix.sum_mul, ← Matrix.mul_sum]
  change bilinear (M⁻¹ * M * M⁻¹) (a e) (a e) = bilinear M⁻¹ (a e) (a e)
  rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hL), Matrix.one_mul]

omit [DecidableEq ι] in
lemma responseSquare_nonneg (a : ι → n → ℝ) (h : ι → ℝ) (e f : ι) :
    0 ≤ responseSquare a h e f := by
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (sq_nonneg _)

omit [DecidableEq ι] in
lemma responseSquare_self (a : ι → n → ℝ) (h : ι → ℝ) (e : ι) :
    responseSquare a h e e = (marginal a h e)^2 := by
  unfold responseSquare marginal
  ring

omit [DecidableEq ι] in
lemma sum_responseSquare (a : ι → n → ℝ) (h : ι → ℝ)
    (hL : IsUnit (laplacian a h)) (e : ι) :
    ∑ f, responseSquare a h e f = marginal a h e := by
  have hs := congrArg (fun x : ℝ => Real.exp (h e) * x)
    (sum_weighted_transfer_sq a h hL e)
  simpa only [Finset.mul_sum, marginal, responseSquare, mul_assoc] using hs

omit [DecidableEq ι] in
lemma marginal_nonneg (a : ι → n → ℝ) (h : ι → ℝ)
    (hL : IsUnit (laplacian a h)) (e : ι) : 0 ≤ marginal a h e := by
  rw [← sum_responseSquare a h hL e]
  exact Finset.sum_nonneg (fun f _ => responseSquare_nonneg a h e f)

omit [DecidableEq ι] in
lemma marginal_le_one (a : ι → n → ℝ) (h : ι → ℝ)
    (hL : IsUnit (laplacian a h)) (e : ι) : marginal a h e ≤ 1 := by
  have hsq : responseSquare a h e e ≤ ∑ f, responseSquare a h e f :=
    Finset.single_le_sum (fun f _ => responseSquare_nonneg a h e f) (Finset.mem_univ e)
  rw [sum_responseSquare a h hL e, responseSquare_self] at hsq
  nlinarith [sq_nonneg (marginal a h e - 1)]

lemma response_self (a : ι → n → ℝ) (h : ι → ℝ) (e : ι) :
    response a h e e = marginal a h e * (1 - marginal a h e) := by
  simp only [response, ite_true, responseSquare_self]
  ring

lemma response_ne_nonpos (a : ι → n → ℝ) (h : ι → ℝ)
    {e f : ι} (hef : e ≠ f) : response a h e f ≤ 0 := by
  simp only [response, ite_eq_right hef, zero_sub]
  exact neg_nonpos.mpr (responseSquare_nonneg a h e f)

lemma sum_response (a : ι → n → ℝ) (h : ι → ℝ)
    (hL : IsUnit (laplacian a h)) (e : ι) : ∑ f, response a h e f = 0 := by
  simp only [response, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, sum_responseSquare a h hL e, sub_self]

lemma sum_abs_response (a : ι → n → ℝ) (h : ι → ℝ)
    (hL : IsUnit (laplacian a h)) (e : ι) :
    ∑ f, |response a h e f| = 2 * marginal a h e * (1 - marginal a h e) := by
  have hd : 0 ≤ response a h e e := by
    rw [response_self]
    exact mul_nonneg (marginal_nonneg a h hL e)
      (sub_nonneg.mpr (marginal_le_one a h hL e))
  have habs (f : ι) : |response a h e f| =
      (if e = f then 2 * response a h e e else 0) - response a h e f := by
    by_cases hef : e = f
    · subst f
      rw [ite_eq_left rfl, abs_of_nonneg hd]
      ring
    · rw [ite_eq_right hef, zero_sub, abs_of_nonpos (response_ne_nonpos a h hef)]
  simp_rw [habs]
  rw [Finset.sum_sub_distrib, sum_response a h hL e]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, sub_zero]
  rw [response_self]
  ring

end Problem336.TransferCurrent

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_TransferCurrentLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Operator

namespace Problem336.TransferCurrent

variable {n : Type*} [Fintype n] [DecidableEq n]

attribute [local instance] OAI.Problem336.TransferCurrent.instTopologicalSpaceMatrixReal_solutions_1
lemma hasDerivAt_inverse_curve (M : ℝ → Matrix n n ℝ) (D : Matrix n n ℝ) (t : ℝ)
    (hM : HasDerivAt M D t) (hU : IsUnit (M t)) :
    HasDerivAt (fun s => (M s)⁻¹) (-((M t)⁻¹ * D * (M t)⁻¹)) t := by
  rcases hU with ⟨u, hu⟩
  have h := (hasFDerivAt_ringInverse (𝕜 := ℝ) u).comp_hasDerivAt_of_eq t hM hu
  simpa only [Function.comp_def, ← Matrix.nonsing_inv_eq_ringInverse,
    neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    Matrix.coe_units_inv, hu] using h

lemma hasDerivAt_bilinear_inverse_curve (M : ℝ → Matrix n n ℝ) (D : Matrix n n ℝ)
    (t : ℝ) (hM : HasDerivAt M D t) (hU : IsUnit (M t)) (a b : n → ℝ) :
    HasDerivAt (fun s => bilinear (M s)⁻¹ a b)
      (-bilinear ((M t)⁻¹ * D * (M t)⁻¹) a b) t := by
  have h := (bilinearCLM a b).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_inverse_curve M D t hM hU)
  simpa only [Function.comp_def, bilinearCLM_apply, bilinear_neg] using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open FiniteGradientResponse

omit [Fintype ι] [DecidableEq ι] in
lemma hasDerivAt_segmentField_apply (h k : ι → ℝ) (i : ι) (t : ℝ) :
    HasDerivAt (fun s => segmentField h k s i) (k i - h i) t := by
  simpa only [segmentField, Function.id_def, one_mul] using
    ((hasDerivAt_id t).mul_const (k i - h i)).const_add (h i)

omit [DecidableEq ι] in
lemma hasDerivAt_laplacian_segment (a : ι → n → ℝ) (h k : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => laplacian a (segmentField h k s))
      (∑ f, (Real.exp (segmentField h k t f) * (k f - h f)) •
        Matrix.vecMulVec (a f) (a f)) t := by
  have hf (f : ι) : HasDerivAt
      (fun s => Real.exp (segmentField h k s f) • Matrix.vecMulVec (a f) (a f))
      ((Real.exp (segmentField h k t f) * (k f - h f)) • Matrix.vecMulVec (a f) (a f)) t :=
    (hasDerivAt_segmentField_apply h k f t).exp.smul_const _
  simpa only [laplacian, Finset.sum_apply] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun f _ => hf f)

omit [DecidableEq ι] in
lemma bilinear_laplacian_direction (a : ι → n → ℝ) (h d : ι → ℝ) (e : ι) :
    Real.exp (h e) * bilinear
      ((laplacian a h)⁻¹ *
        (∑ f, (Real.exp (h f) * d f) • Matrix.vecMulVec (a f) (a f)) *
          (laplacian a h)⁻¹) (a e) (a e) =
      ∑ f, responseSquare a h e f * d f := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  change Real.exp (h e) * bilinearCLM (a e) (a e) (∑ f,
    (laplacian a h)⁻¹ * ((Real.exp (h f) * d f) • Matrix.vecMulVec (a f) (a f)) *
      (laplacian a h)⁻¹) = _
  rw [map_sum, Finset.mul_sum]
  simp only [bilinearCLM_apply]
  apply Finset.sum_congr rfl
  intro f hf
  rw [Matrix.mul_smul, Matrix.smul_mul, bilinear_smul, bilinear_rankOne,
    bilinear_symmetric (inverse_symmetric (laplacian_symmetric a h)) (a f) (a e)]
  unfold responseSquare
  ring

lemma hasDerivAt_marginal_segment (a : ι → n → ℝ) (h k : ι → ℝ) (e : ι) (t : ℝ)
    (hL : IsUnit (laplacian a (segmentField h k t))) :
    HasDerivAt (fun s => marginal a (segmentField h k s) e)
      (∑ f, response a (segmentField h k t) e f * (k f - h f)) t := by
  let H := segmentField h k t
  let D := ∑ f, (Real.exp (H f) * (k f - h f)) • Matrix.vecMulVec (a f) (a f)
  have hB := hasDerivAt_bilinear_inverse_curve
    (fun s => laplacian a (segmentField h k s)) D t
    (hasDerivAt_laplacian_segment a h k t) hL (a e) (a e)
  have hprod := (hasDerivAt_segmentField_apply h k e t).exp.mul hB
  have hv : (Real.exp (H e) * (k e - h e)) * bilinear (laplacian a H)⁻¹ (a e) (a e) +
      Real.exp (H e) * -bilinear ((laplacian a H)⁻¹ * D * (laplacian a H)⁻¹) (a e) (a e) =
      ∑ f, response a H e f * (k f - h f) := by
    rw [mul_neg]
    change (Real.exp (H e) * (k e - h e)) * bilinear (laplacian a H)⁻¹ (a e) (a e) +
      -(Real.exp (H e) * bilinear ((laplacian a H)⁻¹ *
        (∑ f, (Real.exp (H f) * (k f - h f)) • Matrix.vecMulVec (a f) (a f)) *
          (laplacian a H)⁻¹) (a e) (a e)) = _
    rw [bilinear_laplacian_direction]
    simp only [response, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    unfold marginal
    ring
  change HasDerivAt (fun s => marginal a (segmentField h k s) e)
    (∑ f, response a H e f * (k f - h f)) t
  rw [← hv]
  exact hprod

lemma marginal_sub_le_half (a : ι → n → ℝ) (h k : ι → ℝ) (e : ι)
    (D : ℝ) (hD : 0 ≤ D) (hdir : ∀ f, |k f - h f| ≤ D)
    (hL : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (laplacian a (segmentField h k t))) :
    |marginal a k e - marginal a h e| ≤ (1 : ℝ) / 2 * D := by
  apply response_le_of_line_derivative Finset.univ (fun H => marginal a H e)
    (fun H f => response a H e f) h k (1 / 2) D hD
  · intro f hf
    exact hdir f
  · intro t ht
    exact hasDerivAt_marginal_segment a h k e t (hL t ht)
  · intro t ht
    rw [sum_abs_response a _ (hL t ⟨ht.1, ht.2.le⟩) e]
    nlinarith [sq_nonneg (marginal a (segmentField h k t) e - 1 / 2)]

end Problem336.TransferCurrent

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_IncidenceResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix

namespace Problem336.TransferCurrent

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] in

lemma laplacian_reducedGradient (src dst : E → V) (root : V) (h : E → ℝ) :
    laplacian (ReducedLaplacian.reducedGradient src dst root) h =
      ReducedLaplacian.weightedLaplacian src dst root (fun e => Real.exp (h e)) := by
  ext i j
  simp [laplacian, ReducedLaplacian.weightedLaplacian, Matrix.mul_apply,
    Matrix.diagonal, Matrix.vecMulVec, Matrix.of_apply, Matrix.sum_apply, smul_eq_mul, mul_comm, mul_assoc]

lemma incidence_marginal_sub_le_half (src dst : E → V) (root : V)
    (hconn : ReducedLaplacian.Connected src dst) (h k : E → ℝ) (e : E)
    (D : ℝ) (hD : 0 ≤ D) (hdir : ∀ f, |k f - h f| ≤ D) :
    |marginal (ReducedLaplacian.reducedGradient src dst root) k e -
      marginal (ReducedLaplacian.reducedGradient src dst root) h e| ≤ (1 : ℝ) / 2 * D := by
  apply marginal_sub_le_half _ h k e D hD hdir
  intro t ht
  rw [laplacian_reducedGradient]
  exact ReducedLaplacian.weightedLaplacian_isUnit src dst root _ hconn
    (fun f => Real.exp_pos _)

end Problem336.TransferCurrent

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_USTResponse
attribute [-instance] _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem336.USTResponse

lemma inclusion_eq_ratio (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ)
    (e : FiniteEdge K) : inclusion K h e =
      (∑ T : TreeSample K, weight K h T * indicator K T e) / partition K h := by
  simp only [inclusion, FiniteResponse.mean, mass, div_mul_eq_mul_div,
    Finset.sum_div]

end Problem336.USTResponse

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_WeightedTreeBorel
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.WeightedTree

@[simp] theorem extendField_apply (y : EdgeCode → ℝ) (e : EdgeCode) :
    extendField y e.1 = y e := by
  simp only [extendField, dite_eq_left e.2]

end Problem336.WeightedTree

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_WeightedTreeResponse
attribute [-instance] _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem336.WeightedTree

theorem ustResponse_weight_eq (K : FiniteSubgraphCode) (h : Field)
    (T : USTResponse.TreeSample K) :
    USTResponse.weight K (fun e => h e.1) T = weight h T.1 := by
  classical
  have hsub : T.1 ⊆ K.2 := (USTResponse.tree_property K T).1
  unfold USTResponse.weight USTResponse.indicator weight
  congr 1
  rw [← Finset.sum_subtype K.2 (fun _ => Iff.rfl)
    (fun e => h e * if e ∈ T.1 then (1 : ℝ) else 0)]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr hsub]

theorem ustResponse_partition_eq (K : FiniteSubgraphCode) (h : Field) :
    USTResponse.partition K (fun e => h e.1) = partition K h := by
  classical
  unfold USTResponse.partition
  simp_rw [ustResponse_weight_eq]
  exact (Finset.sum_subtype (spanningTrees K) (fun _ => Iff.rfl)
    (fun T => weight h T)).symm

theorem ustResponse_inclusion_eq (K : FiniteSubgraphCode) (h : Field)
    (e : USTResponse.FiniteEdge K) :
    USTResponse.inclusion K (fun f => h f.1) e = inclusion K e.1 h := by
  classical
  rw [USTResponse.inclusion_eq_ratio, ustResponse_partition_eq]
  unfold inclusion
  congr 1
  simp_rw [ustResponse_weight_eq]
  unfold USTResponse.indicator
  rw [← Finset.sum_subtype (spanningTrees K) (fun _ => Iff.rfl)
    (fun T => weight h T * if e.1 ∈ T then (1 : ℝ) else 0)]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  rfl

end Problem336.WeightedTree

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CodedMarginal
attribute [-instance] _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open Classical

namespace Problem336

variable {G : GraphCode} {K : FiniteSubgraphCode}

lemma codeTransferCurrent_apply_bilinear (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (c : (ℕ × ℕ) → ℝ) (S : Finset K.2) (e f : S) :
    codeTransferCurrent hK root c S e f = c e.val.val *
      TransferCurrent.bilinear (codeWeightedLaplacian hK root (fun a => c a.val))⁻¹
        (ReducedLaplacian.reducedGradient (codeSource hK) (codeTarget hK) root e.val)
        (ReducedLaplacian.reducedGradient (codeSource hK) (codeTarget hK) root f.val) := by
  simp only [codeTransferCurrent, Matrix.mul_apply, Matrix.diagonal,
    Matrix.submatrix_apply, Matrix.transpose_apply, codeIncidence,
    Matrix.of_apply, TransferCurrent.bilinear, Matrix.mulVec, dotProduct,
    ite_mul, zero_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, id_eq]
  ring

lemma codeTransferCurrent_singleton (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (h : (ℕ × ℕ) → ℝ) (e : K.2) :
    (codeTransferCurrent hK root (fun p => Real.exp (h p)) {e}).det =
      TransferCurrent.marginal
        (ReducedLaplacian.reducedGradient (codeSource hK) (codeTarget hK) root)
        (fun f => h f.val) e := by
  let : Unique ({e} : Finset K.2) :=
    { default := ⟨e, by simp⟩
      uniq := by intro f; apply Subtype.ext; exact Finset.mem_singleton.mp f.property }
  rw [Matrix.det_unique, codeTransferCurrent_apply_bilinear]
  unfold TransferCurrent.marginal
  rw [TransferCurrent.laplacian_reducedGradient]
  rfl

theorem weightedTree_inclusion_eq_marginal (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (h : WeightedTree.Field) (e : K.2) :
    WeightedTree.inclusion K e.val h =
      TransferCurrent.marginal
        (ReducedLaplacian.reducedGradient (codeSource hK) (codeTarget hK) root)
        (fun f => h f.val) e := by
  have hr := code_tree_inclusion_ratio hK root (fun p => Real.exp (h p))
    (fun _ => Real.exp_pos _) {e}
  rw [codeTransferCurrent_singleton] at hr
  simpa only [WeightedTree.inclusion, WeightedTree.numerator, WeightedTree.partition,
    WeightedTree.weight, Real.exp_sum, SubtypeSubsetSums.forget, Finset.map_singleton,
    Function.Embedding.subtype_apply, Finset.singleton_subset_iff] using hr

theorem USTResponse.inclusion_eq_transferCurrent (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (h : USTResponse.FiniteEdge K → ℝ) (e : USTResponse.FiniteEdge K) :
    USTResponse.inclusion K h e =
      TransferCurrent.marginal
        (ReducedLaplacian.reducedGradient (codeSource hK) (codeTarget hK) root) h e := by
  let ext : WeightedTree.Field := fun p => if hp : p ∈ K.2 then h ⟨p, hp⟩ else 0
  have hext : (fun f : K.2 => ext f.val) = h := by
    funext f
    simp only [ext, dite_eq_left f.property]
  rw [← hext, WeightedTree.ustResponse_inclusion_eq]
  exact weightedTree_inclusion_eq_marginal hK root ext e

theorem USTResponse.inclusion_response_connected (hK : IsFiniteConnectedSubgraph G K)
    (a b : USTResponse.FiniteEdge K → ℝ) (e : USTResponse.FiniteEdge K)
    (D : ℝ) (hD : 0 ≤ D) (hab : ∀ f, |b f - a f| ≤ D) :
    |USTResponse.inclusion K b e - USTResponse.inclusion K a e| ≤ D / 2 := by
  obtain ⟨v, hv⟩ := hK.1
  let root : K.1 := ⟨v, hv⟩
  rw [USTResponse.inclusion_eq_transferCurrent hK root,
    USTResponse.inclusion_eq_transferCurrent hK root]
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using
    TransferCurrent.incidence_marginal_sub_le_half (codeSource hK) (codeTarget hK) root
      (code_endpoints_connected hK) a b e D hD hab

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_ExhaustionExistence
attribute [-instance] _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336

theorem reflTransGen_finite_rooted_support {α : Type*} [DecidableEq α]
    {r : α → α → Prop} {a b : α} (h : Relation.ReflTransGen r a b) :
    ∃ S : Finset α, a ∈ S ∧ b ∈ S ∧
      ∀ v ∈ S, Relation.ReflTransGen
        (fun x y => x ∈ S ∧ y ∈ S ∧ r x y) a v := by
  induction h with
  | refl =>
      refine ⟨{a}, by simp, by simp, ?_⟩
      intro v hv
      have : v = a := Finset.mem_singleton.mp hv
      subst v
      exact .refl
  | @tail b c hab hbc ih =>
      obtain ⟨S, ha, hb, hS⟩ := ih
      have lift {v : α} (hv : v ∈ S) :
          Relation.ReflTransGen
            (fun x y => x ∈ insert c S ∧ y ∈ insert c S ∧ r x y) a v :=
        Relation.ReflTransGen.mono (fun x y hxy =>
          ⟨Finset.mem_insert_of_mem hxy.1,
            Finset.mem_insert_of_mem hxy.2.1, hxy.2.2⟩) a v (hS v hv)
      refine ⟨insert c S, Finset.mem_insert_of_mem ha, by simp, ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact (lift hb).tail
          ⟨Finset.mem_insert_of_mem hb, Finset.mem_insert_self _ _, hbc⟩
      · exact lift hv

private theorem adj_symm_exhaustion {G : GraphCode} {u v : ℕ}
    (h : Adj G u v) : Adj G v u := by
  unfold Adj at *
  rw [G.2.2 v u]
  exact h

private theorem adj_ne_exhaustion {G : GraphCode} {u v : ℕ}
    (h : Adj G u v) : u ≠ v := by
  intro huv
  subst v
  unfold Adj at h
  rw [G.2.1 u] at h
  cases h

theorem subgraphAdj_inducedFiniteCode_iff {G : GraphCode} {S : Finset ℕ}
    {u v : ℕ} :
    SubgraphAdj (inducedFiniteCode G S) u v ↔
      u ∈ S ∧ v ∈ S ∧ Adj G u v := by
  unfold SubgraphAdj rawPair
  change (u ∈ S ∧ v ∈ S ∧
    (if u < v then (u, v) else (v, u)) ∈ (inducedFiniteCode G S).2) ↔ _
  by_cases huv : u < v
  · simp only [ite_eq_left huv, mem_inducedFiniteCode_edges]
    tauto
  · simp only [ite_eq_right huv, mem_inducedFiniteCode_edges]
    constructor
    · rintro ⟨hu, hv, _, _, _, hadj⟩
      exact ⟨hu, hv, adj_symm_exhaustion hadj⟩
    · rintro ⟨hu, hv, hadj⟩
      exact ⟨hu, hv, hv, hu,
        lt_of_le_of_ne (Nat.le_of_not_gt huv) (Ne.symm (adj_ne_exhaustion hadj)),
        adj_symm_exhaustion hadj⟩

theorem inducedFiniteCode_connected_of_rooted {G : GraphCode} {S : Finset ℕ}
    {a : ℕ} (ha : a ∈ S)
    (hS : ∀ v ∈ S, Relation.ReflTransGen
      (fun x y => x ∈ S ∧ y ∈ S ∧ Adj G x y) a v) :
    IsFiniteConnectedSubgraph G (inducedFiniteCode G S) := by
  refine ⟨⟨a, ha⟩, ?_, ?_⟩
  · intro p hp
    exact mem_inducedFiniteCode_edges.mp hp
  · intro u hu v hv
    have forward (w : ℕ) (hw : w ∈ S) :
        Relation.ReflTransGen (SubgraphAdj (inducedFiniteCode G S)) a w :=
      Relation.ReflTransGen.mono
        (fun x y hxy => subgraphAdj_inducedFiniteCode_iff.mpr hxy) a w (hS w hw)
    have backward : Relation.ReflTransGen (SubgraphAdj (inducedFiniteCode G S)) u a := by
      have h := forward u hu
      induction h with
      | refl => exact .refl
      | @tail b c hab hbc ih =>
          have hc := subgraphAdj_inducedFiniteCode_iff.mp hbc
          exact (Relation.ReflTransGen.single
            (subgraphAdj_inducedFiniteCode_iff.mpr
              ⟨hc.2.1, hc.1, adj_symm_exhaustion hc.2.2⟩)).trans (ih hc.1)
    exact backward.trans (forward v hv)

theorem GraphConnected.exists_connected_exhaustion {G : GraphCode}
    (hG : GraphConnected G) :
    ∃ H : ℕ → FiniteSubgraphCode, IsConnectedExhaustion G H := by
  classical
  have supports : ∀ n : ℕ, ∃ S : Finset ℕ, 0 ∈ S ∧ n ∈ S ∧
      ∀ v ∈ S, Relation.ReflTransGen
        (fun x y => x ∈ S ∧ y ∈ S ∧ Adj G x y) 0 v :=
    fun n => reflTransGen_finite_rooted_support (hG 0 n)
  choose S hzero hn hroot using supports
  let V : ℕ → Finset ℕ := fun n => (Finset.range (n + 1)).biUnion S
  have hsub {n i : ℕ} (hi : i ≤ n) : S i ⊆ V n := by
    intro u hu
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr (by omega), hu⟩
  have hvertex (n : ℕ) : n ∈ V n := hsub (le_refl n) (hn n)
  have hzeroV (n : ℕ) : 0 ∈ V n := hsub (Nat.zero_le n) (hzero 0)
  have hmono {n m : ℕ} (hnm : n ≤ m) : V n ⊆ V m := by
    intro u hu
    obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.mp hu
    exact hsub (by have := Finset.mem_range.mp hi; omega) hui
  have hrootV (n : ℕ) (v : ℕ) (hv : v ∈ V n) :
      Relation.ReflTransGen
        (fun x y => x ∈ V n ∧ y ∈ V n ∧ Adj G x y) 0 v := by
    obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
    have hisub : S i ⊆ V n := hsub (by have := Finset.mem_range.mp hi; omega)
    exact Relation.ReflTransGen.mono
      (fun x y hxy => ⟨hisub hxy.1, hisub hxy.2.1, hxy.2.2⟩)
      0 v (hroot i v hvi)
  refine ⟨fun n => inducedFiniteCode G (V n), ?_, ?_, ?_⟩
  · intro n
    exact inducedFiniteCode_connected_of_rooted (hzeroV n) (hrootV n)
  · intro n
    refine ⟨hmono (Nat.le_succ n), ?_⟩
    intro p hp
    obtain ⟨hu, hv, hlt, hadj⟩ := mem_inducedFiniteCode_edges.mp hp
    exact mem_inducedFiniteCode_edges.mpr
      ⟨hmono (Nat.le_succ n) hu, hmono (Nat.le_succ n) hv, hlt, hadj⟩
  · intro u v huv hadj
    refine ⟨v, mem_inducedFiniteCode_edges.mpr ?_⟩
    exact ⟨hmono (Nat.le_of_lt huv) (hvertex u), hvertex v, huv, hadj⟩

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteUSTMeasure
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem336

attribute [local instance] Classical.propDecidable

lemma measurableSet_edgeCylinder (A B : Finset EdgeCode) :
    MeasurableSet (edgeCylinder A B) := by
  unfold edgeCylinder
  convert (A.measurableSet_biInter fun e _ =>
    (measurable_pi_apply e) (measurableSet_singleton true)).inter
    (B.measurableSet_biInter fun e _ =>
    (measurable_pi_apply e) (measurableSet_singleton false)) using 1
  ext X
  simp

lemma finiteUSTMeasure_edgeCylinder (K : FiniteSubgraphCode) (A B : Finset EdgeCode) :
    finiteUSTMeasure K (edgeCylinder A B) = ustCylinder K A B := by
  classical
  rw [finiteUSTMeasure_apply K _ (measurableSet_edgeCylinder A B)]
  simp only [ustCylinder, edgeCylinder, Set.mem_ofPred_eq, finiteTreeConfiguration,
    decide_eq_true_eq, decide_eq_false_iff_not]
  congr 2
  apply congrArg Finset.card
  ext T
  simp

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FUSFExistenceReduction
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem336

theorem HasFUSFLaw.tendsto_finiteUSTProbabilityMeasure
    {G : GraphCode} {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id)
    (H : ℕ → FiniteSubgraphCode) (hH : IsConnectedExhaustion G H) :
    Tendsto (fun n => finiteUSTProbabilityMeasure (H n)
      (FiniteEncoding.spanningTrees_nonempty (hH.1 n))) atTop (𝓝 μ) := by
  apply BinaryLaw.tendsto_iff_signedCylinders.mpr
  intro A B
  change Tendsto (fun n => finiteUSTMeasure (H n) (edgeCylinder A B)) atTop
    (𝓝 ((μ : Measure EdgeConfiguration) (edgeCylinder A B)))
  simp only [finiteUSTMeasure_edgeCylinder]
  exact hμ.2 H hH A B

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PosteriorTiltLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace Problem336.TiltLimit

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω]

theorem tendsto_integral_continuous [CompactSpace Ω]
    {J : Type*} {l : Filter J} {μs : J → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hμ : Tendsto μs l (𝓝 μ)) {f : Ω → ℝ} (hf : Continuous f) :
    Tendsto (fun j => ∫ x, f x ∂(μs j : Measure Ω)) l
      (𝓝 (∫ x, f x ∂(μ : Measure Ω))) := by
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ
    (BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩)

theorem integral_exp_pos [CompactSpace Ω] (μ : ProbabilityMeasure Ω)
    {h : Ω → ℝ} (hh : Continuous h) :
    0 < ∫ x, Real.exp (h x) ∂(μ : Measure Ω) := by
  apply MeasureTheory.integral_exp_pos
  exact (BoundedContinuousFunction.mkOfCompact ⟨_, (Real.continuous_exp.comp hh)⟩).integrable _

theorem tendsto_tiltedMean [CompactSpace Ω]
    {J : Type*} {l : Filter J} {μs : J → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hμ : Tendsto μs l (𝓝 μ)) {h X : Ω → ℝ} (hh : Continuous h) (hX : Continuous X) :
    Tendsto (fun j => tiltedMean (μs j) h X) l (𝓝 (tiltedMean μ h X)) := by
  exact (tendsto_integral_continuous hμ (hX.mul (Real.continuous_exp.comp hh))).div
    (tendsto_integral_continuous hμ (Real.continuous_exp.comp hh)) (ne_of_gt (integral_exp_pos μ hh))

theorem response_bound_of_tendsto [CompactSpace Ω]
    {J : Type*} {l : Filter J} [l.NeBot]
    {μs : J → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hμ : Tendsto μs l (𝓝 μ)) {h h' X : Ω → ℝ}
    (hh : Continuous h) (hh' : Continuous h') (hX : Continuous X) {C : ℝ}
    (hbound : ∀ᶠ j in l, |tiltedMean (μs j) h X - tiltedMean (μs j) h' X| ≤ C) :
    |tiltedMean μ h X - tiltedMean μ h' X| ≤ C := by
  exact le_of_tendsto
    ((tendsto_tiltedMean hμ hh hX).sub (tendsto_tiltedMean hμ hh' hX)).abs hbound

variable {I : Type*}

theorem continuous_finiteEnergy (S : Finset I) (h : I → ℝ) :
    Continuous (finiteEnergy S h) := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul (continuous_bit.comp (continuous_apply i))

variable [Countable I]

theorem finiteTiltMean_response_bound_of_tendsto
    {J : Type*} {l : Filter J} [l.NeBot]
    {μs : J → ProbabilityMeasure (I → Bool)} {μ : ProbabilityMeasure (I → Bool)}
    (hμ : Tendsto μs l (𝓝 μ)) (S : Finset I) (h h' : I → ℝ) (e : I) {C : ℝ}
    (hbound : ∀ᶠ j in l,
      |finiteTiltMean (μs j) S h e - finiteTiltMean (μs j) S h' e| ≤ C) :
    |finiteTiltMean μ S h e - finiteTiltMean μ S h' e| ≤ C :=
  response_bound_of_tendsto hμ (continuous_finiteEnergy S h) (continuous_finiteEnergy S h')
    (continuous_bit.comp (continuous_apply e)) hbound

end Problem336.TiltLimit

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteUSTIntegrals
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace Problem336

lemma integral_finiteUSTMeasure (K : FiniteSubgraphCode)
    (f : EdgeConfiguration → ℝ) :
    (∫ X, f X ∂finiteUSTMeasure K) =
      (∑ T ∈ spanningTrees K, f (finiteTreeConfiguration T)) /
        (↑(spanningTrees K).card : ℝ) := by
  rw [finiteUSTMeasure, integral_smul_measure,
    integral_finsetSum_measure (fun T _ => integrable_dirac (by simp))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_USTFiniteTilt
attribute [-instance] _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem336.USTResponse

lemma finiteTilt_of_mem (K : FiniteSubgraphCode) (S : Finset (ℕ × ℕ))
    (t : ℝ) (y : (ℕ × ℕ) → ℝ) (e : ℕ × ℕ) (he : e ∈ K.2) :
    finiteTilt K S t y e = inclusion K (observationField K S t y) ⟨e, he⟩ := by
  simp [finiteTilt, he]

lemma finiteTilt_of_not_mem (K : FiniteSubgraphCode) (S : Finset (ℕ × ℕ))
    (t : ℝ) (y : (ℕ × ℕ) → ℝ) (e : ℕ × ℕ) (he : e ∉ K.2) :
    finiteTilt K S t y e = 0 := by
  simp [finiteTilt, he]

theorem finiteTilt_response_of_response (K : FiniteSubgraphCode)
    (hresponse : ∀ (a b : FiniteEdge K → ℝ) (e : FiniteEdge K) (D : ℝ),
      0 ≤ D → (∀ f, |b f - a f| ≤ D) →
        |inclusion K b e - inclusion K a e| ≤ D / 2)
    (S : Finset (ℕ × ℕ)) (t : ℝ) (y y' : (ℕ × ℕ) → ℝ) (e : ℕ × ℕ)
    (D : ℝ) (hD : 0 ≤ D) (hy : ∀ f ∈ S, |y' f - y f| ≤ D) :
    |finiteTilt K S t y' e - finiteTilt K S t y e| ≤ D / 2 := by
  by_cases he : e ∈ K.2
  · rw [finiteTilt_of_mem K S t y' e he, finiteTilt_of_mem K S t y e he]
    apply hresponse _ _ _ D hD
    intro f
    by_cases hf : f.1 ∈ S
    · simpa only [observationField, ite_eq_left hf, sub_sub_sub_cancel_right] using hy f.1 hf
    · simpa only [observationField, ite_eq_right hf, sub_self, abs_zero] using hD
  · simp only [finiteTilt, dite_eq_right he, sub_self, abs_zero]
    exact div_nonneg hD (by norm_num)

end Problem336.USTResponse

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_USTPosteriorResponse
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem336.USTResponse

lemma bit_finiteTreeConfiguration (T : Finset (ℕ × ℕ)) (e : EdgeCode) :
    TiltLimit.bit (finiteTreeConfiguration T e) = if e.1 ∈ T then 1 else 0 := by
  classical
  by_cases he : e.1 ∈ T <;> simp [TiltLimit.bit, finiteTreeConfiguration, he]

private lemma sum_restrict_support (K T S : Finset (ℕ × ℕ))
    (hT : T ⊆ K) (h : (ℕ × ℕ) → ℝ) :
    (∑ p ∈ K, (if p ∈ S then h p else 0) * (if p ∈ T then 1 else 0)) =
      ∑ p ∈ S, h p * (if p ∈ T then 1 else 0) := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hT]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  simp only [Finset.filter_mem_eq_inter, Finset.inter_comm]

lemma finiteEnergy_eq_observationField (K : FiniteSubgraphCode)
    (T : TreeSample K) (S : Finset EdgeCode) (h : EdgeCode → ℝ) :
    TiltLimit.finiteEnergy S h (finiteTreeConfiguration T.1) =
      ∑ f : FiniteEdge K,
        observationField K (S.image Subtype.val) 0 (extendMarks h) f * indicator K T f := by
  classical
  simp only [observationField, zero_div, sub_zero, indicator]
  rw [← Finset.sum_subtype K.2 (fun _ => Iff.rfl)
    (fun p => (if p ∈ S.image Subtype.val then extendMarks h p else 0) *
      (if p ∈ T.1 then (1 : ℝ) else 0))]
  rw [sum_restrict_support K.2 T.1 (S.image Subtype.val) (tree_property K T).1]
  rw [Finset.sum_image]
  · simp only [TiltLimit.finiteEnergy, extendMarks_coe, bit_finiteTreeConfiguration]
  · intro a _ b _ hab
    exact Subtype.val_injective hab

lemma exp_finiteEnergy_eq_weight (K : FiniteSubgraphCode)
    (T : TreeSample K) (S : Finset EdgeCode) (h : EdgeCode → ℝ) :
    Real.exp (TiltLimit.finiteEnergy S h (finiteTreeConfiguration T.1)) =
      weight K (observationField K (S.image Subtype.val) 0 (extendMarks h)) T := by
  rw [finiteEnergy_eq_observationField]
  rfl

lemma tiltedMean_finiteUSTProbability (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty)
    (energy obs : EdgeConfiguration → ℝ) :
    TiltLimit.tiltedMean (finiteUSTProbability K hne) energy obs =
      (∑ T : TreeSample K, obs (finiteTreeConfiguration T.1) *
        Real.exp (energy (finiteTreeConfiguration T.1))) /
      (∑ T : TreeSample K, Real.exp (energy (finiteTreeConfiguration T.1))) := by
  have hc : ((spanningTrees K).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hne
  unfold TiltLimit.tiltedMean
  change (∫ X, obs X * Real.exp (energy X) ∂finiteUSTMeasure K) /
    (∫ X, Real.exp (energy X) ∂finiteUSTMeasure K) = _
  rw [integral_finiteUSTMeasure, integral_finiteUSTMeasure,
    div_div_div_cancel_right₀ hc]
  congr 1 <;> exact Finset.sum_subtype (spanningTrees K) (fun _ => Iff.rfl) _

lemma finiteTiltMean_eq_weight_ratio (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty) (S : Finset EdgeCode)
    (h : EdgeCode → ℝ) (e : EdgeCode) :
    TiltLimit.finiteTiltMean (finiteUSTProbability K hne) S h e =
      (∑ T : TreeSample K, TiltLimit.bit (finiteTreeConfiguration T.1 e) *
        weight K (observationField K (S.image Subtype.val) 0 (extendMarks h)) T) /
      partition K (observationField K (S.image Subtype.val) 0 (extendMarks h)) := by
  rw [TiltLimit.finiteTiltMean, tiltedMean_finiteUSTProbability]
  simp_rw [exp_finiteEnergy_eq_weight]
  rfl

theorem finiteTiltMean_eq_finiteTilt (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty) (S : Finset EdgeCode)
    (h : EdgeCode → ℝ) (e : EdgeCode) :
    TiltLimit.finiteTiltMean (finiteUSTProbability K hne) S h e =
      finiteTilt K (S.image Subtype.val) 0 (extendMarks h) e.1 := by
  rw [finiteTiltMean_eq_weight_ratio]
  by_cases he : e.1 ∈ K.2
  · rw [finiteTilt_of_mem K _ 0 _ e.1 he, inclusion_eq_ratio]
    congr 1
    apply Finset.sum_congr rfl
    intro T _
    simp [bit_finiteTreeConfiguration, indicator, mul_comm]
  · rw [finiteTilt_of_not_mem K _ 0 _ e.1 he]
    have hz (T : TreeSample K) : TiltLimit.bit (finiteTreeConfiguration T.1 e) = 0 := by
      rw [bit_finiteTreeConfiguration, ite_eq_right]
      exact fun ht => he ((tree_property K T).1 ht)
    simp_rw [hz, zero_mul]
    simp

theorem finiteUST_posterior_response_of_response (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty)
    (hresponse : ∀ (a b : FiniteEdge K → ℝ) (e : FiniteEdge K) (D : ℝ),
      0 ≤ D → (∀ f, |b f - a f| ≤ D) →
        |inclusion K b e - inclusion K a e| ≤ D / 2)
    (S : Finset EdgeCode) (h h' : EdgeCode → ℝ) (e : EdgeCode)
    (D : ℝ) (hD : 0 ≤ D) (hh : ∀ f ∈ S, |h' f - h f| ≤ D) :
    |TiltLimit.finiteTiltMean (finiteUSTProbability K hne) S h' e -
      TiltLimit.finiteTiltMean (finiteUSTProbability K hne) S h e| ≤ D / 2 := by
  rw [finiteTiltMean_eq_finiteTilt, finiteTiltMean_eq_finiteTilt]
  apply finiteTilt_response_of_response K hresponse (S.image Subtype.val) 0
    (extendMarks h) (extendMarks h') e.1 D hD
  intro p hp
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hp
  simpa only [extendMarks_coe] using hh f hf

end Problem336.USTResponse

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FUSFPosteriorResponse
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem336

theorem HasFUSFLaw.finiteTiltMean_response
    {G : GraphCode} (hc : GraphConnected G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id)
    (S : Finset EdgeCode) (h h' : EdgeCode → ℝ) (e : EdgeCode)
    (D : ℝ) (hD : 0 ≤ D) (hh : ∀ f ∈ S, |h f - h' f| ≤ D) :
    |TiltLimit.finiteTiltMean μ S h e - TiltLimit.finiteTiltMean μ S h' e| ≤ D / 2 := by
  obtain ⟨H, hH⟩ := hc.exists_connected_exhaustion
  apply TiltLimit.finiteTiltMean_response_bound_of_tendsto
    (hμ.tendsto_finiteUSTProbabilityMeasure H hH) S h h' e
  apply Filter.Eventually.of_forall
  intro n
  exact USTResponse.finiteUST_posterior_response_of_response (H n)
    (FiniteEncoding.spanningTrees_nonempty (hH.1 n))
    (USTResponse.inclusion_response_connected (hH.1 n)) S h' h e D hD hh

theorem HasFUSFLaw.finiteResponseBound_oai
    {G : GraphCode} (hc : GraphConnected G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id)
    (S : EdgeCode → ℕ → Finset EdgeCode) :
    PosteriorDrift.FiniteResponseBound μ S (1 / 2 : ℝ) := by
  intro e n h h' D hD hh
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using
    hμ.finiteTiltMean_response hc (S e n) h h' e D hD hh

end Problem336

end

end OAI
end

theorem solution : type_of% @OAI.Problem336.HasFUSFLaw.finiteResponseBound_oai := @OAI.Problem336.HasFUSFLaw.finiteResponseBound_oai
