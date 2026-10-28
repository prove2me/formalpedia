-- Prove2me | solution 1 for OAI.Problem336.exists_hasFUSFLaw
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:38:27.029003+00:00
-- url     : https://prove2.me/submissions/cd7325d4-85ac-45a8-80cf-6c8a1cadcc35

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.Nodup
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_AlgebraicCycleSpace
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336

 theorem finiteCycleSpace_mono {K L : FiniteSubgraphCode} (h : K.2 ⊆ L.2) :
    finiteCycleSpace K ≤ finiteCycleSpace L := by
  apply inf_le_inf_right
  exact Finsupp.supported_mono (fun _ he => h he)

 theorem IsConnectedExhaustion.finiteCodeEdges_monotone {G : GraphCode}
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H) :
    Monotone (fun n => finiteCodeEdges (H n)) := by
  apply monotone_nat_of_le_succ
  intro n e he
  exact (hH.2.1 n).2 he

 theorem IsConnectedExhaustion.iUnion_finiteCodeEdges {G : GraphCode}
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H) :
    (⋃ n, finiteCodeEdges (H n)) = graphCodeEdges G := by
  ext e
  constructor
  · intro he
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp he
    exact ((hH.1 n).2.1 e.1 hn).2.2.2
  · intro he
    obtain ⟨n, hn⟩ := hH.2.2 e.1.1 e.1.2 e.2 he
    exact Set.mem_iUnion.mpr ⟨n, hn⟩

 theorem IsConnectedExhaustion.finiteCycleSpace_monotone {G : GraphCode}
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H) :
    Monotone (fun n => finiteCycleSpace (H n)) := by
  apply monotone_nat_of_le_succ
  intro n
  exact finiteCycleSpace_mono (hH.2.1 n).2

 theorem IsConnectedExhaustion.iSup_finiteCycleSpace {G : GraphCode}
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H) :
    (⨆ n, finiteCycleSpace (H n)) = graphCycleSpace G := by
  have hm : Monotone (fun n => Finsupp.supported ℝ ℝ (finiteCodeEdges (H n))) :=
    fun _ _ h => Finsupp.supported_mono (hH.finiteCodeEdges_monotone h)
  unfold finiteCycleSpace graphCycleSpace
  rw [← hm.directed_le.iSup_inf_eq, ← Finsupp.supported_iUnion,
    hH.iUnion_finiteCodeEdges]

 theorem IsConnectedExhaustion.finiteHilbertCycleSpace_monotone {G : GraphCode}
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H) :
    Monotone (fun n => finiteHilbertCycleSpace (H n)) := by
  intro m n hmn
  exact Submodule.map_mono (hH.finiteCycleSpace_monotone hmn)

 theorem IsConnectedExhaustion.closure_iSup_finiteHilbertCycleSpace {G : GraphCode}
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H) :
    (⨆ n, finiteHilbertCycleSpace (H n)).topologicalClosure = closedGraphCycleSpace G := by
  unfold finiteHilbertCycleSpace closedGraphCycleSpace
  rw [← Submodule.map_iSup, hH.iSup_finiteCycleSpace]

end Problem336

end

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

theorem measurableSet_signedCylinder {I : Type*} (A B : Finset I) :
    MeasurableSet (signedCylinder A B) := by
  unfold signedCylinder
  convert (A.measurableSet_biInter fun e _ =>
    (measurable_pi_apply e) (measurableSet_singleton true)).inter
    (B.measurableSet_biInter fun e _ =>
    (measurable_pi_apply e) (measurableSet_singleton false)) using 1
  ext x
  simp

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

theorem measure_ext_of_positive_cylinders {I : Type*} {μ ν : Measure (I → Bool)}
    [IsFiniteMeasure μ]
    (h : ∀ A : Finset I, μ {x | ∀ e ∈ A, x e = true} =
      ν {x | ∀ e ∈ A, x e = true}) : μ = ν := by
  classical
  apply measure_ext_of_signed_cylinders
  intro A B
  change μ (signedCylinder A B) = ν (signedCylinder A B)
  induction B using Finset.induction_on generalizing A with
  | empty => simpa [signedCylinder] using h A
  | @insert e B he ih =>
    have hu : signedCylinder A B =
        signedCylinder (insert e A) B ∪ signedCylinder A (insert e B) := by
      ext x
      simp only [signedCylinder, Set.mem_ofPred_eq, Set.mem_union, Finset.mem_insert,
        forall_eq_or_imp]
      cases x e <;> simp
    have hd : Disjoint (signedCylinder (insert e A) B)
        (signedCylinder A (insert e B)) := by
      rw [Set.disjoint_left]
      intro x hx hy
      have ht := hx.1 e (Finset.mem_insert_self e A)
      have hf := hy.2 e (Finset.mem_insert_self e B)
      exact Bool.noConfusion (ht.symm.trans hf)
    have hsplit (ρ : Measure (I → Bool)) :
        ρ (signedCylinder A B) = ρ (signedCylinder (insert e A) B) +
          ρ (signedCylinder A (insert e B)) := by
      rw [hu, measure_union hd (measurableSet_signedCylinder A (insert e B))]
    have heq := ih A
    rw [hsplit μ, hsplit ν, ← ih (insert e A)] at heq
    exact (ENNReal.add_right_inj (measure_ne_top μ _)).mp heq

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

theorem exists_probabilityMeasure_of_clopen_limits
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [T2Space E] [CompactSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    {ι : Type*} (μn : ℕ → ProbabilityMeasure E)
    (S : ι → Set E) (hS : ∀ i, IsClopen (S i)) (L : ι → ℝ≥0∞)
    (hL : ∀ i, Tendsto (fun n => (μn n : Measure E) (S i)) atTop (𝓝 (L i))) :
    ∃ μ : ProbabilityMeasure E, ∀ i, (μ : Measure E) (S i) = L i := by
  obtain ⟨μ, hμ⟩ := exists_clusterPt_of_compactSpace (Filter.map μn atTop)
  exact ⟨μ, fun i => clopen_measure_eq_of_mapClusterPt hμ (hS i) (hL i)⟩

theorem exists_probabilityMeasure_tendsto_of_clopen_limits
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [T2Space E] [CompactSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    {ι : Type*} (μn : ℕ → ProbabilityMeasure E)
    (S : ι → Set E) (hS : ∀ i, IsClopen (S i))
    (hsep : ∀ μ ν : ProbabilityMeasure E,
      (∀ i, (μ : Measure E) (S i) = (ν : Measure E) (S i)) → μ = ν)
    (L : ι → ℝ≥0∞)
    (hL : ∀ i, Tendsto (fun n => (μn n : Measure E) (S i)) atTop (𝓝 (L i))) :
    ∃ μ : ProbabilityMeasure E,
      (∀ i, (μ : Measure E) (S i) = L i) ∧ Tendsto μn atTop (𝓝 μ) := by
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_of_clopen_limits μn S hS L hL
  refine ⟨μ, hμ, tendsto_nhds_of_unique_mapClusterPt (fun ν hν => ?_)⟩
  exact hsep ν μ fun i =>
    (clopen_measure_eq_of_mapClusterPt hν (hS i) (hL i)).trans (hμ i).symm

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

theorem tendsto_iff_positiveCylinders
    {I α : Type*} [Countable I] {F : Filter α}
    {μs : α → ProbabilityMeasure (I → Bool)}
    {μ : ProbabilityMeasure (I → Bool)} :
    Tendsto μs F (𝓝 μ) ↔ ∀ A : Finset I,
      Tendsto (fun a => (μs a : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true}) F
        (𝓝 ((μ : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true})) := by
  constructor
  · intro h A
    simpa [signedCylinder] using (tendsto_iff_signedCylinders.mp h) A ∅
  · intro h
    apply tendsto_nhds_of_unique_mapClusterPt
    intro ν hν
    apply ProbabilityMeasure.toMeasure_injective
    apply measure_ext_of_positive_cylinders
    intro A
    have hS : IsClopen {x : I → Bool | ∀ i ∈ A, x i = true} := by
      simpa using Problem336.isClopen_boolCylinder A ∅
    exact Problem336.clopen_measure_eq_of_mapClusterPt hν hS (h A)

theorem exists_weakLimit_of_positiveCylinder_limits
    {I : Type*} [Countable I]
    (μn : ℕ → ProbabilityMeasure (I → Bool)) (L : Finset I → ℝ≥0∞)
    (hL : ∀ A, Tendsto
      (fun n => (μn n : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true})
      atTop (𝓝 (L A))) :
    ∃ μ : ProbabilityMeasure (I → Bool),
      (∀ A, (μ : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true} = L A) ∧
      Tendsto μn atTop (𝓝 μ) := by
  apply Problem336.exists_probabilityMeasure_tendsto_of_clopen_limits μn
    (fun A => {x | ∀ i ∈ A, x i = true}) _ _ L hL
  · intro A
    simpa using Problem336.isClopen_boolCylinder A ∅
  · intro μ ν h
    apply ProbabilityMeasure.toMeasure_injective
    exact measure_ext_of_positive_cylinders h

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
-- module Solutions.OAIS_P336.SpanningForest_FiniteCycleIncidence
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336

 theorem finiteFlowEmbedding_range (K : FiniteSubgraphCode) :
    LinearMap.range (finiteFlowEmbedding K) = Finsupp.supported ℝ ℝ (finiteCodeEdges K) := by
  rw [finiteFlowEmbedding, Fintype.range_linearCombination, Finsupp.supported_eq_span_single]
  congr 1
  ext f
  simp

 theorem finiteIncidence_mulVec (K : FiniteSubgraphCode)
    (x : finiteCodeEdges K → ℝ) (v : ↥K.1) :
    (finiteIncidence K).mulVec x v = edgeBoundary (finiteFlowEmbedding K x) v.1 := by
  classical
  simp only [finiteIncidence, Matrix.mulVec, dotProduct, finiteFlowEmbedding,
    Fintype.linearCombination_apply, map_sum, map_smul, edgeBoundary_single,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.sub_apply,
    Finsupp.single_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro e he
  simp only [eq_comm]
  ring

 theorem IsFiniteConnectedSubgraph.boundary_eq_zero_outside {G : GraphCode}
    {K : FiniteSubgraphCode} (hK : IsFiniteConnectedSubgraph G K)
    (x : finiteCodeEdges K → ℝ) {v : ℕ} (hv : v ∉ K.1) :
    edgeBoundary (finiteFlowEmbedding K x) v = 0 := by
  classical
  simp only [finiteFlowEmbedding, Fintype.linearCombination_apply,
    map_sum, map_smul, edgeBoundary_single, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.single_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro e he
  have hends := hK.2.1 e.1.1 e.2
  have hleft : e.1.1.1 ≠ v := fun h => hv (h ▸ hends.1)
  have hright : e.1.1.2 ≠ v := fun h => hv (h ▸ hends.2.1)
  simp [hleft, hright]

 theorem IsFiniteConnectedSubgraph.finiteCycleSpace_eq_incidenceKernel {G : GraphCode}
    {K : FiniteSubgraphCode} (hK : IsFiniteConnectedSubgraph G K) :
    finiteCycleSpace K =
      (LinearMap.ker (Matrix.mulVecLin (finiteIncidence K))).map (finiteFlowEmbedding K) := by
  classical
  apply le_antisymm
  · intro f hf
    have hs : f ∈ LinearMap.range (finiteFlowEmbedding K) := by
      rw [finiteFlowEmbedding_range]
      exact hf.1
    obtain ⟨x, rfl⟩ := hs
    apply Submodule.mem_map.mpr
    refine ⟨x, ?_, rfl⟩
    change (finiteIncidence K).mulVec x = 0
    funext v
    rw [finiteIncidence_mulVec]
    exact congrArg (fun f : ℕ →₀ ℝ => f v.1) hf.2
  · intro f hf
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hf
    refine ⟨?_, ?_⟩
    · rw [← finiteFlowEmbedding_range]
      exact ⟨x, rfl⟩
    · change edgeBoundary (finiteFlowEmbedding K x) = 0
      ext v
      by_cases hv : v ∈ K.1
      · have hrow := congrArg (fun y : ↥K.1 → ℝ => y ⟨v, hv⟩) hx
        simpa only [Matrix.mulVecLin_apply, finiteIncidence_mulVec, Pi.zero_apply, Finsupp.zero_apply] using hrow
      · exact hK.boundary_eq_zero_outside x hv

 theorem IsFiniteConnectedSubgraph.finiteHilbertCycleSpace_eq_incidenceKernel {G : GraphCode}
    {K : FiniteSubgraphCode} (hK : IsFiniteConnectedSubgraph G K) :
    finiteHilbertCycleSpace K =
      (LinearMap.ker (Matrix.mulVecLin (finiteIncidence K))).map
        (edgeFlowToHilbert.comp (finiteFlowEmbedding K)) := by
  rw [finiteHilbertCycleSpace, hK.finiteCycleSpace_eq_incidenceKernel, Submodule.map_comp]

 theorem IsFiniteConnectedSubgraph.finiteHilbertCycleSpace_eq_euclideanKernel {G : GraphCode}
    {K : FiniteSubgraphCode} (hK : IsFiniteConnectedSubgraph G K) :
    finiteHilbertCycleSpace K =
      (LinearMap.ker (Matrix.toEuclideanLin (finiteIncidence K))).map
        (finiteHilbertEmbedding K).toLinearMap := by
  classical
  rw [hK.finiteHilbertCycleSpace_eq_incidenceKernel]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨WithLp.toLp 2 x, ?_, rfl⟩
    change Matrix.toEuclideanLin (finiteIncidence K) (WithLp.toLp 2 x) = 0
    change (finiteIncidence K).mulVec x = 0 at hx
    simp only [Matrix.toLpLin_apply, hx, WithLp.toLp_zero]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.ofLp, ?_, rfl⟩
    change (finiteIncidence K).mulVec x.ofLp = 0
    change Matrix.toEuclideanLin (finiteIncidence K) x = 0 at hx
    have hh := congrArg WithLp.ofLp hx
    simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_zero] using hh

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_IncidenceCirculation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
open Matrix

namespace Problem336.IncidenceCirculation

variable {V E R : Type*} [DecidableEq V] [Fintype V] [Fintype E] [CommRing R]

theorem sum_divergence (src dst : E → V) (x : E → R) :
    ∑ v, (incidence src dst *ᵥ x) v = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_incidence_column, zero_mul]
  exact Finset.sum_const_zero

theorem divergence_eq_zero_of_off_root (src dst : E → V) (root : V) (x : E → R)
    (h : ∀ v, v ≠ root → (incidence src dst *ᵥ x) v = 0) :
    incidence src dst *ᵥ x = 0 := by
  have hroot : (incidence src dst *ᵥ x) root = 0 := by
    have hsum := sum_divergence src dst x
    rwa [Finset.sum_eq_single root (fun v _ hv => h v hv) (by simp)] at hsum
  funext v
  by_cases hv : v = root
  · simpa [hv] using hroot
  · exact h v hv

theorem reduced_mulVec_eq_zero_iff (src dst : E → V) (root : V) (x : E → R) :
    reducedIncidence src dst root *ᵥ x = 0 ↔ incidence src dst *ᵥ x = 0 := by
  constructor
  · intro h
    apply divergence_eq_zero_of_off_root src dst root x
    intro v hv
    exact congrFun h ⟨v, hv⟩
  · intro h
    funext v
    exact congrFun h v.1

end Problem336.IncidenceCirculation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_TransferProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336
namespace TransferProjection

section Abstract

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem adjoint_rightInverse_projection
    (A : E →ₗ[ℝ] F) (B : F →ₗ[ℝ] F)
    (hB : (A ∘ₗ A.adjoint) ∘ₗ B = LinearMap.id) (x : E) :
    A.kerᗮ.starProjection x = A.adjoint (B (A x)) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · rw [A.orthogonal_ker]
    exact ⟨B (A x), rfl⟩
  · rw [Submodule.orthogonal_orthogonal]
    change A (x - A.adjoint (B (A x))) = 0
    rw [map_sub]
    have h := LinearMap.congr_fun hB (A x)
    change A (A.adjoint (B (A x))) = A x at h
    rw [h, sub_self]

theorem adjoint_rightInverse_eq_complement
    (A : E →ₗ[ℝ] F) (B : F →ₗ[ℝ] F)
    (hB : (A ∘ₗ A.adjoint) ∘ₗ B = LinearMap.id) (x : E) :
    A.adjoint (B (A x)) = x - A.ker.starProjection x := by
  rw [← adjoint_rightInverse_projection A B hB x]
  exact A.ker.starProjection_orthogonal_val x

end Abstract

section Embedding

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem map_projection_adjoint (j : E →ₗᵢ[ℝ] H) (C : Submodule ℝ E) (x : H) :
    (C.map j.toLinearMap).starProjection x =
      j (C.starProjection (j.toContinuousLinearMap.adjoint x)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨C.starProjection (j.toContinuousLinearMap.adjoint x),
      C.starProjection_apply_mem _, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [inner_sub_left]
    change inner ℝ x (j y) -
      inner ℝ (j (C.starProjection (j.toContinuousLinearMap.adjoint x))) (j y) = 0
    have ha : inner ℝ x (j y) = inner ℝ (j.toContinuousLinearMap.adjoint x) y :=
      (j.toContinuousLinearMap.adjoint_inner_left y x).symm
    rw [j.inner_map_map, ha, ← inner_sub_left]
    exact C.starProjection_inner_eq_zero _ y hy

theorem range_projection_adjoint (j : E →ₗᵢ[ℝ] H) (x : H) :
    j.toLinearMap.range.starProjection x = j (j.toContinuousLinearMap.adjoint x) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  simpa [Submodule.starProjection_top] using
    map_projection_adjoint j (⊤ : Submodule ℝ E) x

theorem embedded_complement_projection (j : E →ₗᵢ[ℝ] H)
    (C : Submodule ℝ E) (x : H) :
    j (j.toContinuousLinearMap.adjoint x -
      C.starProjection (j.toContinuousLinearMap.adjoint x)) =
      j.toLinearMap.range.starProjection x - (C.map j.toLinearMap).starProjection x := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [map_sub, range_projection_adjoint, map_projection_adjoint]

end Embedding

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem transferMatrix_eq_complement (A : Matrix m n ℝ)
    (hA : IsUnit (A * A.transpose).det) (x : EuclideanSpace ℝ n) :
    (transferMatrix A).toEuclideanLin x =
      x - A.toEuclideanLin.ker.starProjection x := by
  have hadj : A.transpose.toEuclideanLin = A.toEuclideanLin.adjoint := by
    simpa using A.toEuclideanLin_conjTranspose_eq_adjoint
  have hright :
      (A.toEuclideanLin ∘ₗ A.toEuclideanLin.adjoint) ∘ₗ
        (A * A.transpose)⁻¹.toEuclideanLin = LinearMap.id := by
    rw [← hadj, ← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same]
    rw [Matrix.mul_nonsing_inv _ hA, Matrix.toLpLin_one]
  have h := adjoint_rightInverse_eq_complement A.toEuclideanLin
    (A * A.transpose)⁻¹.toEuclideanLin hright x
  simpa only [transferMatrix, Matrix.toLpLin_mul_same, LinearMap.comp_apply, hadj] using h

theorem embedded_transferMatrix_eq_difference
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : Matrix m n ℝ) (hA : IsUnit (A * A.transpose).det)
    (j : EuclideanSpace ℝ n →ₗᵢ[ℝ] H) (x : H) :
    j ((transferMatrix A).toEuclideanLin (j.toContinuousLinearMap.adjoint x)) =
      j.toLinearMap.range.starProjection x -
        (A.toEuclideanLin.ker.map j.toLinearMap).starProjection x := by
  rw [transferMatrix_eq_complement A hA]
  exact embedded_complement_projection j A.toEuclideanLin.ker x

end TransferProjection
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_ReducedCycleKernel
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336
namespace ReducedCycleKernel

variable {G : GraphCode} {K : FiniteSubgraphCode}

theorem finiteIncidence_eq_incidence (hK : IsFiniteConnectedSubgraph G K) :
    finiteIncidence K = IncidenceCirculation.incidence (codeSource hK) (codeDestination hK) := by
  classical
  ext v e
  simp only [finiteIncidence, IncidenceCirculation.incidence, codeSource, codeDestination,
    Subtype.ext_iff]

theorem reducedFiniteIncidence_eq_incidence (hK : IsFiniteConnectedSubgraph G K)
    (root : ↥K.1) :
    reducedFiniteIncidence K root =
      IncidenceCirculation.reducedIncidence (codeSource hK) (codeDestination hK) root := by
  classical
  ext v e
  exact congrFun (congrFun (finiteIncidence_eq_incidence hK) v.1) e

theorem reducedFiniteIncidence_mulVec_eq_zero_iff
    (hK : IsFiniteConnectedSubgraph G K) (root : ↥K.1)
    (x : finiteCodeEdges K → ℝ) :
    (reducedFiniteIncidence K root).mulVec x = 0 ↔ (finiteIncidence K).mulVec x = 0 := by
  classical
  rw [reducedFiniteIncidence_eq_incidence hK, finiteIncidence_eq_incidence hK]
  exact IncidenceCirculation.reduced_mulVec_eq_zero_iff _ _ _ _

theorem codeEndpoints_connected (hK : IsFiniteConnectedSubgraph G K) :
    ReducedLaplacian.Connected (codeSource hK) (codeDestination hK) := by
  intro u v
  refine Relation.ReflTransGen.mono ?_ u v (Problem336.code_endpoints_connected hK u v)
  intro a b hab
  obtain ⟨e, he⟩ := hab
  let e' : finiteCodeEdges K := ⟨⟨e.1, (hK.2.1 e.1 e.2).2.2.1⟩, e.2⟩
  refine ⟨e', ?_⟩
  simpa only [codeSource, codeDestination, Problem336.codeSource, Problem336.codeTarget, e'] using he

theorem reducedFiniteIncidence_eq_gradient_transpose
    (hK : IsFiniteConnectedSubgraph G K) (root : ↥K.1) :
    reducedFiniteIncidence K root =
      (ReducedLaplacian.reducedGradient (codeSource hK) (codeDestination hK) root).transpose := by
  classical
  rw [reducedFiniteIncidence_eq_incidence hK]
  rfl

theorem reducedFiniteIncidence_gram_isUnit
    (hK : IsFiniteConnectedSubgraph G K) (root : ↥K.1) :
    IsUnit ((reducedFiniteIncidence K root) * (reducedFiniteIncidence K root).transpose).det := by
  classical
  apply isUnit_iff_ne_zero.mpr
  have hd := ReducedLaplacian.weightedLaplacian_det_ne_zero
    (codeSource hK) (codeDestination hK) root (fun _ => 1)
    (codeEndpoints_connected hK) (fun _ => by norm_num)
  simpa [ReducedLaplacian.weightedLaplacian,
    reducedFiniteIncidence_eq_gradient_transpose hK root] using hd

theorem reducedFiniteIncidence_euclideanKernel
    (hK : IsFiniteConnectedSubgraph G K) (root : ↥K.1) :
    (reducedFiniteIncidence K root).toEuclideanLin.ker = (finiteIncidence K).toEuclideanLin.ker := by
  classical
  ext x
  simpa only [LinearMap.mem_ker, Matrix.toLpLin_apply,
    WithLp.toLp_eq_zero] using reducedFiniteIncidence_mulVec_eq_zero_iff hK root x.ofLp

theorem finiteHilbertCycleSpace_eq_reducedKernel
    (hK : IsFiniteConnectedSubgraph G K) (root : ↥K.1) :
    finiteHilbertCycleSpace K =
      ((reducedFiniteIncidence K root).toEuclideanLin.ker).map
        (finiteHilbertEmbedding K).toLinearMap := by
  rw [reducedFiniteIncidence_euclideanKernel hK]
  exact hK.finiteHilbertCycleSpace_eq_euclideanKernel

theorem finite_transfer_eq_coordinate_sub_cycle
    (hK : IsFiniteConnectedSubgraph G K) (root : ↥K.1)
    (hGram : IsUnit ((reducedFiniteIncidence K root) *
      (reducedFiniteIncidence K root).transpose).det) (x : EdgeHilbert) :
    finiteHilbertEmbedding K
      ((TransferProjection.transferMatrix (reducedFiniteIncidence K root)).toEuclideanLin
        ((finiteHilbertEmbedding K).toContinuousLinearMap.adjoint x)) =
      (finiteHilbertEmbedding K).toLinearMap.range.starProjection x -
        (finiteHilbertCycleSpace K).starProjection x := by
  classical
  rw [TransferProjection.embedded_transferMatrix_eq_difference _ hGram]
  congr 1
  congr 1
  congr 1
  exact (finiteHilbertCycleSpace_eq_reducedKernel hK root).symm

theorem finite_transfer_eq_coordinate_sub_cycle_of_connected
    (hK : IsFiniteConnectedSubgraph G K) (root : ↥K.1) (x : EdgeHilbert) :
    finiteHilbertEmbedding K
      ((TransferProjection.transferMatrix (reducedFiniteIncidence K root)).toEuclideanLin
        ((finiteHilbertEmbedding K).toContinuousLinearMap.adjoint x)) =
      (finiteHilbertEmbedding K).toLinearMap.range.starProjection x -
        (finiteHilbertCycleSpace K).starProjection x :=
  finite_transfer_eq_coordinate_sub_cycle hK root
    (reducedFiniteIncidence_gram_isUnit hK root) x

theorem finiteHilbertEmbedding_basis (K : FiniteSubgraphCode) (e : finiteCodeEdges K) :
    finiteHilbertEmbedding K (EuclideanSpace.basisFun (finiteCodeEdges K) ℝ e) =
      lp.single 2 e.1 (1 : ℝ) := by
  classical
  change finiteHilbertEmbeddingLinear K _ = _
  rw [finiteHilbertEmbeddingLinear_sum]
  simp

theorem finite_transfer_entry_eq_projection
    (hK : IsFiniteConnectedSubgraph G K) (root : ↥K.1) (e f : finiteCodeEdges K) :
    TransferProjection.transferMatrix (reducedFiniteIncidence K root) e f =
      inner ℝ (lp.single 2 e.1 (1 : ℝ))
        ((finiteHilbertEmbedding K).toLinearMap.range.starProjection (lp.single 2 f.1 (1 : ℝ)) -
          (finiteHilbertCycleSpace K).starProjection (lp.single 2 f.1 (1 : ℝ))) := by
  classical
  rw [← finite_transfer_eq_coordinate_sub_cycle_of_connected hK root]
  rw [← finiteHilbertEmbedding_basis K e, ← finiteHilbertEmbedding_basis K f]
  have hj : (finiteHilbertEmbedding K).toContinuousLinearMap.adjoint
      (finiteHilbertEmbedding K (EuclideanSpace.basisFun (finiteCodeEdges K) ℝ f)) =
      EuclideanSpace.basisFun (finiteCodeEdges K) ℝ f := by
    have hh := congrArg (fun F => F (EuclideanSpace.basisFun (finiteCodeEdges K) ℝ f))
      (finiteHilbertEmbedding K).adjoint_comp_self
    exact hh
  rw [hj, (finiteHilbertEmbedding K).inner_map_map, EuclideanSpace.basisFun_inner]
  simp [Matrix.toLpLin_apply]

end ReducedCycleKernel
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CodeTransferKernel
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336
namespace CodeTransferKernel

open scoped Matrix

variable {G : GraphCode} {K : FiniteSubgraphCode}

theorem incidence_eq_submatrix (hK : IsFiniteConnectedSubgraph G K) (root : K.1) :
    incidence hK root =
      (ReducedCycleKernel.reducedFiniteIncidence K root).submatrix id (edgeEquiv hK) := by
  classical
  ext v e
  simp only [incidence, ReducedLaplacian.reducedGradient, Matrix.transpose_apply,
    ReducedCycleKernel.reducedFiniteIncidence, finiteIncidence, Matrix.submatrix_apply,
    edgeEquiv, Equiv.coe_fn_mk, id_eq, Problem336.codeSource, Problem336.codeTarget,
    Subtype.ext_iff]

theorem gram_submatrix {m n p : Type*} [Fintype n] [Fintype p]
    (A : Matrix m n ℝ) (e : p ≃ n) :
    A.submatrix id e * (A.submatrix id e).transpose = A * A.transpose := by
  change A.submatrix id e * A.transpose.submatrix e id = A * A.transpose
  simpa only [Matrix.submatrix_id_id] using
    Matrix.submatrix_mul_equiv A A.transpose id e id

theorem transferMatrix_submatrix {m n p : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [Fintype p] (A : Matrix m n ℝ) (e : p ≃ n) :
    TransferProjection.transferMatrix (A.submatrix id e) =
      (TransferProjection.transferMatrix A).submatrix e e := by
  rw [TransferProjection.transferMatrix, gram_submatrix]
  change A.transpose.submatrix e id * (A * A.transpose)⁻¹ * A.submatrix id e = _
  ext i j
  rfl

theorem transfer_entry_eq_projection (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (e f : K.2) :
    TransferProjection.transferMatrix (incidence hK root) e f =
      inner ℝ (lp.single 2 (edgeEquiv hK e).1 (1 : ℝ))
        ((finiteHilbertEmbedding K).toLinearMap.range.starProjection
            (lp.single 2 (edgeEquiv hK f).1 (1 : ℝ)) -
          (finiteHilbertCycleSpace K).starProjection
            (lp.single 2 (edgeEquiv hK f).1 (1 : ℝ))) := by
  rw [incidence_eq_submatrix, transferMatrix_submatrix]
  exact ReducedCycleKernel.finite_transfer_entry_eq_projection hK root
    (edgeEquiv hK e) (edgeEquiv hK f)

end CodeTransferKernel
end Problem336

end

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

theorem codeWeightedLaplacian_det_eq_tree_count
    (hK : IsFiniteConnectedSubgraph G K) (root : K.1) :
    (codeWeightedLaplacian hK root (fun _ => 1)).det = (spanningTrees K).card := by
  simpa using codeWeightedLaplacian_tree_partition hK root (fun _ => 1)

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
-- module Solutions.OAIS_P336.SpanningForest_CoordinateTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology ENNReal

namespace Problem336.CoordinateTruncation

variable {ι 𝕜 : Type*} [DecidableEq ι] [RCLike 𝕜]

lemma truncate_eq_sum (s : Finset ι) (x : Space ι 𝕜) :
    truncate s x = ∑ i ∈ s, lp.single 2 i (x i) := by
  simp only [truncate, sum_apply, ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply]
  rfl

@[simp] theorem truncate_apply (s : Finset ι) (x : Space ι 𝕜) (i : ι) :
    truncate s x i = if i ∈ s then x i else 0 := by
  rw [truncate_eq_sum]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Finset.sum_pi_single]

omit [DecidableEq ι] in
theorem supported_mono {s t : Set ι} (h : s ⊆ t) :
    supported (𝕜 := 𝕜) s ≤ supported t := by
  intro x hx i hi
  exact hx i (fun hs => hi (h hs))

theorem single_mem_supported {s : Set ι} {i : ι} (hi : i ∈ s) (a : 𝕜) :
    lp.single 2 i a ∈ supported s := by
  intro j hj
  have hji : j ≠ i := by intro h; subst j; exact hj hi
  simp [lp.single_apply, Pi.single_eq_of_ne hji]

theorem truncate_mem_supported (s : Finset ι) (x : Space ι 𝕜) :
    truncate s x ∈ supported (s : Set ι) := by
  intro i hi
  simp only [Finset.mem_coe] at hi
  simp [hi]

theorem sub_truncate_mem_orthogonal (s : Finset ι) (x : Space ι 𝕜) :
    x - truncate s x ∈ (supported (s : Set ι))ᗮ := by
  intro y hy
  rw [lp.inner_eq_tsum]
  have hz : ∀ i, inner 𝕜 (y i) ((x - truncate s x) i) = 0 := by
    intro i
    by_cases hi : i ∈ s
    · simp [hi]
    · have hyi : y i = 0 := hy i hi
      simp [hyi]
  simp only [hz, tsum_zero]

theorem starProjection_supported (s : Finset ι) :
    (supported (𝕜 := 𝕜) (s : Set ι)).starProjection = truncate s := by
  apply ContinuousLinearMap.ext
  intro x
  exact Submodule.eq_starProjection_of_mem_orthogonal
    (truncate_mem_supported s x) (sub_truncate_mem_orthogonal s x)

theorem closure_iSup_supported (s : ℕ → Finset ι) (S : Set ι)
    (hcover : ∀ i, i ∈ S ↔ ∃ n, i ∈ s n) :
    (⨆ n, supported (𝕜 := 𝕜) (s n : Set ι)).topologicalClosure = supported S := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply iSup_le
      intro n
      apply supported_mono
      intro i hi
      exact (hcover i).mpr ⟨n, hi⟩
    · exact supported_isClosed S
  · intro x hx
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    apply mem_closure_of_tendsto
      (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)
    apply Eventually.of_forall
    intro t
    apply Submodule.sum_mem
    intro i hi
    by_cases his : i ∈ S
    · obtain ⟨n, hin⟩ := (hcover i).mp his
      exact Submodule.mem_iSup_of_mem n (single_mem_supported hin (x i))
    · simp only [hx i his, lp.single_zero]
      exact Submodule.zero_mem _

theorem tendsto_truncate_supported (s : ℕ → Finset ι) (hmono : Monotone s)
    (S : Set ι) (hcover : ∀ i, i ∈ S ↔ ∃ n, i ∈ s n) (x : Space ι 𝕜) :
    Tendsto (fun n => truncate (s n) x) atTop
      (𝓝 ((supported S).starProjection x)) := by
  have h := Submodule.starProjection_tendsto_closure_iSup
    (fun n => supported (𝕜 := 𝕜) (s n : Set ι))
    (fun m n hmn => supported_mono (hmono hmn)) x
  simpa only [starProjection_supported, closure_iSup_supported s S hcover] using h

end Problem336.CoordinateTruncation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GraphCoordinateTruncation
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace Problem336.CoordinateTruncation

theorem exhaustion_finiteEdges_monotone {G : GraphCode}
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H) :
    Monotone (fun n => finiteEdges (H n)) := by
  apply monotone_nat_of_le_succ
  intro n e he
  apply (mem_finiteEdges (H (n + 1)) e).mpr
  exact (hH.2.1 n).2 ((mem_finiteEdges (H n) e).mp he)

theorem exhaustion_graphEdges {G : GraphCode} {H : ℕ → FiniteSubgraphCode}
    (hH : IsConnectedExhaustion G H) (e : EdgeCode) :
    e ∈ graphEdges G ↔ ∃ n, e ∈ finiteEdges (H n) := by
  constructor
  · intro he
    obtain ⟨n, hn⟩ := hH.2.2 e.1.1 e.1.2 e.2 he
    exact ⟨n, (mem_finiteEdges (H n) e).mpr hn⟩
  · rintro ⟨n, hn⟩
    exact ((hH.1 n).2.1 e.1 ((mem_finiteEdges (H n) e).mp hn)).2.2.2

theorem graph_truncate_tendsto {G : GraphCode} {H : ℕ → FiniteSubgraphCode}
    (hH : IsConnectedExhaustion G H) (x : Space EdgeCode ℝ) :
    Tendsto (fun n => truncate (finiteEdges (H n)) x) atTop
      (𝓝 ((supported (graphEdges G)).starProjection x)) :=
  tendsto_truncate_supported (fun n => finiteEdges (H n))
    (exhaustion_finiteEdges_monotone hH) (graphEdges G) (exhaustion_graphEdges hH) x

end Problem336.CoordinateTruncation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GraphFreeKernel
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.finiteCodeEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology ENNReal

namespace Problem336.FreeKernel

open CoordinateTruncation

theorem cycle_projection_tendsto {G : GraphCode} {H : ℕ → FiniteSubgraphCode}
    (hH : IsConnectedExhaustion G H) (x : EdgeHilbert) :
    Tendsto (fun n => (finiteHilbertCycleSpace (H n)).starProjection x) atTop
      (𝓝 ((closedGraphCycleSpace G).starProjection x)) := by
  have h := Submodule.starProjection_tendsto_closure_iSup
    (fun n => finiteHilbertCycleSpace (H n)) hH.finiteHilbertCycleSpace_monotone x
  simpa only [hH.closure_iSup_finiteHilbertCycleSpace] using h

theorem finiteKernel_tendsto {G : GraphCode} {H : ℕ → FiniteSubgraphCode}
    (hH : IsConnectedExhaustion G H) (x : EdgeHilbert) :
    Tendsto (fun n => finiteKernel (H n) x) atTop (𝓝 (graphKernel G x)) := by
  simpa only [finiteKernel, graphKernel, sub_apply] using
    (graph_truncate_tendsto hH x).sub (cycle_projection_tendsto hH x)

theorem finiteKernel_inner_tendsto {G : GraphCode} {H : ℕ → FiniteSubgraphCode}
    (hH : IsConnectedExhaustion G H) (x y : EdgeHilbert) :
    Tendsto (fun n => inner ℝ x (finiteKernel (H n) y)) atTop
      (𝓝 (inner ℝ x (graphKernel G y))) :=
  tendsto_const_nhds.inner (finiteKernel_tendsto hH y)

theorem finiteKernel_minor_tendsto {G : GraphCode} {H : ℕ → FiniteSubgraphCode}
    (hH : IsConnectedExhaustion G H) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → EdgeHilbert) :
    Tendsto (fun n => Matrix.det (fun i j => inner ℝ (v i) (finiteKernel (H n) (v j))))
      atTop (𝓝 (Matrix.det (fun i j => inner ℝ (v i) (graphKernel G (v j))))) := by
  have hd : Continuous (Matrix.det : Matrix ι ι ℝ → ℝ) := continuous_id.matrix_det
  apply (hd.tendsto _).comp
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  exact finiteKernel_inner_tendsto hH (v i) (v j)

theorem finiteKernel_edge_minor_tendsto {G : GraphCode} {H : ℕ → FiniteSubgraphCode}
    (hH : IsConnectedExhaustion G H) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → EdgeCode) :
    Tendsto (fun n => Matrix.det (fun i j =>
      inner ℝ (edgeVector (e i)) (finiteKernel (H n) (edgeVector (e j)))))
      atTop (𝓝 (Matrix.det (fun i j => kernelEntry G (e i) (e j)))) :=
  finiteKernel_minor_tendsto hH (fun i => edgeVector (e i))

theorem finiteInclusionMinor_tendsto {G : GraphCode} {H : ℕ → FiniteSubgraphCode}
    (hH : IsConnectedExhaustion G H) (A : Finset EdgeCode) :
    Tendsto (fun n => finiteInclusionMinor (H n) A) atTop
      (𝓝 (inclusionMinorLimit G A)) := by
  simpa only [finiteInclusionMinor, inclusionMinorLimit, Function.comp_def] using
    (ENNReal.continuous_ofReal.tendsto _).comp
      (finiteKernel_edge_minor_tendsto hH (fun e : A => e.1))

theorem common_inclusion_limits_of_finite_identity (G : GraphCode)
    (hfinite : ∀ K : FiniteSubgraphCode, IsFiniteConnectedSubgraph G K →
      ∀ A : Finset EdgeCode, ustCylinder K A ∅ = finiteInclusionMinor K A) :
    ∀ H : ℕ → FiniteSubgraphCode, IsConnectedExhaustion G H →
      ∀ A : Finset EdgeCode, Tendsto (fun n => ustCylinder (H n) A ∅) atTop
        (𝓝 (inclusionMinorLimit G A)) := by
  intro H hH A
  simpa only [hfinite _ (hH.1 _) A] using finiteInclusionMinor_tendsto hH A

theorem finiteCycle_le_supported (K : FiniteSubgraphCode) :
    finiteHilbertCycleSpace K ≤ supported (finiteEdges K : Set EdgeCode) := by
  rintro x ⟨f, hf, rfl⟩ e he
  rw [edgeFlowToHilbert_apply]
  apply Finsupp.notMem_support_iff.mp
  intro hes
  apply he
  exact (mem_finiteEdges K e).mpr (((mem_finiteCycleSpace K f).mp hf).1 e hes)

theorem finiteKernel_mem_supported (K : FiniteSubgraphCode) (x : EdgeHilbert) :
    finiteKernel K x ∈ supported (finiteEdges K : Set EdgeCode) :=
  (supported (finiteEdges K : Set EdgeCode)).sub_mem
    (truncate_mem_supported (finiteEdges K) x)
    (finiteCycle_le_supported K ((finiteHilbertCycleSpace K).starProjection_apply_mem x))

theorem finiteKernel_inner_edge_eq_zero_of_not_mem (K : FiniteSubgraphCode)
    (e : EdgeCode) (x : EdgeHilbert) (he : e.1 ∉ K.2) :
    inner ℝ (edgeVector e) (finiteKernel K x) = 0 := by
  rw [edgeVector, lp.inner_single_left]
  have hz := finiteKernel_mem_supported K x e
    (fun h => he ((mem_finiteEdges K e).mp h))
  simpa using hz

end Problem336.FreeKernel

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteKernelEmbedding
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.FreeKernel

open CoordinateTruncation

theorem finiteHilbertEmbedding_mem_supported (K : FiniteSubgraphCode)
    (x : EuclideanSpace ℝ (finiteCodeEdges K)) :
    finiteHilbertEmbedding K x ∈ supported (finiteEdges K : Set EdgeCode) := by
  change finiteHilbertEmbeddingLinear K x ∈ supported (finiteEdges K : Set EdgeCode)
  rw [finiteHilbertEmbeddingLinear_sum]
  apply Submodule.sum_mem
  intro e he
  apply Submodule.smul_mem
  exact single_mem_supported ((mem_finiteEdges K e.1).mpr e.2) 1

@[simp] theorem truncate_finiteHilbertEmbedding (K : FiniteSubgraphCode)
    (x : EuclideanSpace ℝ (finiteCodeEdges K)) :
    truncate (finiteEdges K) (finiteHilbertEmbedding K x) = finiteHilbertEmbedding K x := by
  rw [← starProjection_supported]
  exact Submodule.starProjection_eq_self_iff.mpr (finiteHilbertEmbedding_mem_supported K x)

end Problem336.FreeKernel

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteKernelBridge
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
namespace Problem336.FiniteKernelBridge
open CoordinateTruncation

theorem embedding_range (K : FiniteSubgraphCode) :
    (finiteHilbertEmbedding K).toLinearMap.range =
      supported (finiteEdges K : Set EdgeCode) := by
  classical
  apply le_antisymm
  · rintro x ⟨y, rfl⟩ e he
    exact FreeKernel.finiteHilbertEmbedding_mem_supported K y e he
  · intro x hx
    refine ⟨WithLp.toLp 2 (fun e : finiteCodeEdges K => x e.1), ?_⟩
    apply lp.ext
    funext e
    by_cases he : e ∈ finiteEdges K
    · exact finiteHilbertEmbedding_apply K _ ⟨e, (mem_finiteEdges K e).mp he⟩
    · exact (FreeKernel.finiteHilbertEmbedding_mem_supported K _ e he).trans (hx e he).symm

theorem embedding_projection (K : FiniteSubgraphCode) :
    (finiteHilbertEmbedding K).toLinearMap.range.starProjection =
      truncate (finiteEdges K) := by
  simpa only [embedding_range] using (starProjection_supported (𝕜 := ℝ) (finiteEdges K))

end Problem336.FiniteKernelBridge

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CodedTransferProjection
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336
namespace CodeTransferKernel

variable {G : GraphCode} {K : FiniteSubgraphCode}

theorem codeTransferCurrent_one (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (S : Finset K.2) :
    codeTransferCurrent hK root (fun _ => 1) S =
      (TransferProjection.transferMatrix (incidence hK root)).submatrix
        (Subtype.val : S → K.2) (Subtype.val : S → K.2) := by
  classical
  simp only [codeTransferCurrent, Matrix.diagonal_one, Matrix.one_mul,
    codeWeightedLaplacian, ReducedLaplacian.weightedLaplacian, Matrix.mul_one,
    TransferProjection.transferMatrix, incidence, codeIncidence,
    Matrix.transpose_transpose]
  rfl

theorem codeTransferCurrent_one_entry (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (S : Finset K.2) (e f : S) :
    codeTransferCurrent hK root (fun _ => 1) S e f =
      inner ℝ (lp.single 2 (edgeEquiv hK e.1).1 (1 : ℝ))
        ((finiteHilbertEmbedding K).toLinearMap.range.starProjection
            (lp.single 2 (edgeEquiv hK f.1).1 (1 : ℝ)) -
          (finiteHilbertCycleSpace K).starProjection
            (lp.single 2 (edgeEquiv hK f.1).1 (1 : ℝ))) := by
  rw [codeTransferCurrent_one]
  exact transfer_entry_eq_projection hK root e.1 f.1

theorem codeTransferCurrent_one_eq_finiteKernel (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (S : Finset K.2) :
    codeTransferCurrent hK root (fun _ => 1) S =
      fun e f : S => inner ℝ (FreeKernel.edgeVector (edgeEquiv hK e.1).1)
        (FreeKernel.finiteKernel K (FreeKernel.edgeVector (edgeEquiv hK f.1).1)) := by
  ext e f
  rw [codeTransferCurrent_one_entry, FiniteKernelBridge.embedding_projection]
  rfl

theorem code_tree_inclusion_ratio_finiteKernel (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (S : Finset K.2) :
    (((spanningTrees K).filter
      (fun T => SubtypeSubsetSums.forget K.2 S ⊆ T)).card : ℝ) /
        (spanningTrees K).card =
      Matrix.det (fun e f : S =>
        inner ℝ (FreeKernel.edgeVector (edgeEquiv hK e.1).1)
          (FreeKernel.finiteKernel K (FreeKernel.edgeVector (edgeEquiv hK f.1).1))) := by
  have h := code_tree_inclusion_ratio hK root (fun _ => 1) (fun _ => by norm_num) S
  simpa only [Finset.prod_const_one, Finset.sum_const, nsmul_eq_mul, mul_one,
    codeTransferCurrent_one_eq_finiteKernel] using h

end CodeTransferKernel
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_Exhaustion
attribute [-instance] _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter

namespace Problem336

theorem GraphConnected.exists_adj {G : GraphCode} (hG : GraphConnected G) (u : ℕ) :
    ∃ v, Adj G u v := by
  rcases (hG u (u + 1)).cases_head with h | ⟨v, huv, _⟩
  · omega
  · exact ⟨v, huv⟩

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
-- module Solutions.OAIS_P336.SpanningForest_FiniteUSTLimit
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

theorem finiteUSTMeasure_positiveCylinder (K : FiniteSubgraphCode)
    (A : Finset EdgeCode) :
    finiteUSTMeasure K {x | ∀ e ∈ A, x e = true} = ustCylinder K A ∅ := by
  simpa [edgeCylinder] using finiteUSTMeasure_edgeCylinder K A ∅

theorem exists_finiteUST_limit_of_inclusion_limits
    (H : ℕ → FiniteSubgraphCode)
    (hH : ∀ n, (spanningTrees (H n)).Nonempty)
    (L : Finset EdgeCode → ℝ≥0∞)
    (hL : ∀ A, Tendsto (fun n => ustCylinder (H n) A ∅) atTop (𝓝 (L A))) :
    ∃ μ : ProbabilityMeasure EdgeConfiguration,
      (∀ A, (μ : Measure EdgeConfiguration) {x | ∀ e ∈ A, x e = true} = L A) ∧
      Tendsto (fun n => finiteUSTProbabilityMeasure (H n) (hH n)) atTop (𝓝 μ) := by
  apply BinaryLaw.exists_weakLimit_of_positiveCylinder_limits
    (fun n => finiteUSTProbabilityMeasure (H n) (hH n)) L
  intro A
  simpa only [finiteUSTProbabilityMeasure, ProbabilityMeasure.coe_mk,
    finiteUSTMeasure_positiveCylinder] using hL A

theorem exists_hasFUSFLaw_of_common_inclusion_limits
    (G : GraphCode) (H : ℕ → FiniteSubgraphCode)
    (hH : IsConnectedExhaustion G H)
    (hne : ∀ H' : ℕ → FiniteSubgraphCode, IsConnectedExhaustion G H' →
      ∀ n, (spanningTrees (H' n)).Nonempty)
    (L : Finset EdgeCode → ℝ≥0∞)
    (hL : ∀ H' : ℕ → FiniteSubgraphCode, IsConnectedExhaustion G H' →
      ∀ A, Tendsto (fun n => ustCylinder (H' n) A ∅) atTop (𝓝 (L A))) :
    ∃ μ : ProbabilityMeasure EdgeConfiguration,
      HasFUSFLaw G (μ : Measure EdgeConfiguration) id := by
  obtain ⟨μ, hμ, _⟩ := exists_finiteUST_limit_of_inclusion_limits H (hne H hH) L (hL H hH)
  refine ⟨μ, (fun e => measurable_pi_apply e), ?_⟩
  intro H' hH' A B
  have hw : Tendsto (fun n => finiteUSTProbabilityMeasure (H' n) (hne H' hH' n))
      atTop (𝓝 μ) := by
    apply BinaryLaw.tendsto_iff_positiveCylinders.mpr
    intro C
    simpa only [finiteUSTProbabilityMeasure, ProbabilityMeasure.coe_mk,
      finiteUSTMeasure_positiveCylinder, hμ C] using hL H' hH' C
  have hc := BinaryLaw.tendsto_iff_signedCylinders.mp hw A B
  change Tendsto (fun n => finiteUSTMeasure (H' n) (edgeCylinder A B)) atTop
    (𝓝 ((μ : Measure EdgeConfiguration) (edgeCylinder A B))) at hc
  simp only [finiteUSTMeasure_edgeCylinder] at hc
  exact hc

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

theorem exists_hasFUSFLaw_of_inclusion_limits
    (G : GraphCode) (H : ℕ → FiniteSubgraphCode)
    (hH : IsConnectedExhaustion G H)
    (L : Finset EdgeCode → ℝ≥0∞)
    (hL : ∀ H' : ℕ → FiniteSubgraphCode, IsConnectedExhaustion G H' →
      ∀ A, Tendsto (fun n => ustCylinder (H' n) A ∅) atTop (𝓝 (L A))) :
    ∃ μ : ProbabilityMeasure EdgeConfiguration,
      HasFUSFLaw G (μ : Measure EdgeConfiguration) id :=
  exists_hasFUSFLaw_of_common_inclusion_limits G H hH
    (fun _ hH' n => FiniteEncoding.spanningTrees_nonempty (hH'.1 n)) L hL

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteKernelSupport
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.finiteCodeEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336.FreeKernel

open CoordinateTruncation

theorem finiteKernel_minor_eq_zero_of_absent
    (K : FiniteSubgraphCode) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → EdgeCode) (i : ι) (hi : (e i).1 ∉ K.2) :
    Matrix.det (fun a b => inner ℝ (edgeVector (e a))
      (finiteKernel K (edgeVector (e b)))) = 0 :=
  Matrix.det_eq_zero_of_row_eq_zero i fun j =>
    finiteKernel_inner_edge_eq_zero_of_not_mem K (e i) (edgeVector (e j)) hi

theorem ustCylinder_eq_zero_of_required_absent (K : FiniteSubgraphCode)
    (A B : Finset EdgeCode) (e : EdgeCode) (he : e ∈ A) (habs : e.1 ∉ K.2) :
    ustCylinder K A B = 0 := by
  classical
  have hz : ∀ T ∈ spanningTrees K,
      ¬ ((∀ a ∈ A, a.1 ∈ T) ∧ (∀ b ∈ B, b.1 ∉ T)) := by
    intro T hT hc
    have hsub : T ⊆ K.2 := (Finset.mem_filter.mp hT).2.1
    exact habs (hsub (hc.1 e he))
  simp only [ustCylinder, ENNReal.div_eq_zero_iff, Nat.cast_eq_zero,
    Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact Or.inl hz

theorem inclusion_identity_of_contained_identity (K : FiniteSubgraphCode)
    (hinside : ∀ A : Finset EdgeCode, (∀ e ∈ A, e.1 ∈ K.2) →
      ustCylinder K A ∅ = ENNReal.ofReal
        (Matrix.det (fun e f : A => inner ℝ (edgeVector e.1)
          (finiteKernel K (edgeVector f.1))))) :
    ∀ A : Finset EdgeCode, ustCylinder K A ∅ = ENNReal.ofReal
      (Matrix.det (fun e f : A => inner ℝ (edgeVector e.1)
        (finiteKernel K (edgeVector f.1)))) := by
  classical
  intro A
  by_cases hA : ∀ e ∈ A, e.1 ∈ K.2
  · exact hinside A hA
  · push Not at hA
    obtain ⟨e, he, habs⟩ := hA
    rw [ustCylinder_eq_zero_of_required_absent K A ∅ e he habs,
      finiteKernel_minor_eq_zero_of_absent K (fun e : A => e.1) ⟨e, he⟩ habs]
    simp

end Problem336.FreeKernel

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_IntrinsicExhaustion
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336
namespace IntrinsicExhaustion

theorem vertexBall_mono (G : GraphCode) (c : ℕ) : Monotone (vertexBall G c) :=
  monotone_nat_of_le_succ (fun _ _ hv => Or.inl hv)

@[simp] theorem center_mem_vertexBall (G : GraphCode) (c n : ℕ) :
    c ∈ vertexBall G c n :=
  vertexBall_mono G c (Nat.zero_le n) rfl

theorem exists_mem_vertexBall_of_reachable {G : GraphCode} {c v : ℕ}
    (h : Relation.ReflTransGen (Adj G) c v) :
    ∃ n, v ∈ vertexBall G c n := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | @tail v w hpath hadj ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, Or.inr ⟨v, hn, hadj⟩⟩

theorem GraphConnected.exists_mem_vertexBall {G : GraphCode}
    (hG : GraphConnected G) (c v : ℕ) :
    ∃ n, v ∈ vertexBall G c n :=
  exists_mem_vertexBall_of_reachable (hG c v)

theorem edgeBall_mono (G : GraphCode) (e : EdgeCode) : Monotone (edgeBall G e) := by
  intro n m hnm v hv
  exact hv.elim (fun h => Or.inl (vertexBall_mono G e.1.1 hnm h))
    (fun h => Or.inr (vertexBall_mono G e.1.2 hnm h))

@[simp] theorem fst_mem_edgeBall (G : GraphCode) (e : EdgeCode) (n : ℕ) :
    e.1.1 ∈ edgeBall G e n := Or.inl (center_mem_vertexBall G e.1.1 n)

@[simp] theorem snd_mem_edgeBall (G : GraphCode) (e : EdgeCode) (n : ℕ) :
    e.1.2 ∈ edgeBall G e n := Or.inr (center_mem_vertexBall G e.1.2 n)

theorem GraphConnected.exists_mem_edgeBall {G : GraphCode}
    (hG : GraphConnected G) (e : EdgeCode) (v : ℕ) :
    ∃ n, v ∈ edgeBall G e n := by
  obtain ⟨n, hn⟩ := GraphConnected.exists_mem_vertexBall hG e.1.1 v
  exact ⟨n, Or.inl hn⟩

theorem vertexBall_reachable {G : GraphCode} {c v n : ℕ}
    (hv : v ∈ vertexBall G c n) :
    Relation.ReflTransGen
      (fun x y => x ∈ vertexBall G c n ∧ y ∈ vertexBall G c n ∧ Adj G x y) c v := by
  induction n generalizing v with
  | zero =>
    have : v = c := hv
    subst v
    exact .refl
  | succ n ih =>
    have hlift : ∀ {v}, v ∈ vertexBall G c n →
        Relation.ReflTransGen
          (fun x y => x ∈ vertexBall G c (n + 1) ∧
            y ∈ vertexBall G c (n + 1) ∧ Adj G x y) c v := by
      intro v hv
      apply Relation.ReflTransGen.mono (fun x y h =>
        ⟨Or.inl h.1, Or.inl h.2.1, h.2.2⟩) _ _ (ih hv)
    rcases hv with hv | ⟨u, hu, huv⟩
    · exact hlift hv
    · exact (hlift hu).tail ⟨Or.inl hu, Or.inr ⟨u, hu, huv⟩, huv⟩

theorem edgeBall_reachable {G : GraphCode} {e : EdgeCode} {v n : ℕ}
    (he : Adj G e.1.1 e.1.2) (hv : v ∈ edgeBall G e n) :
    Relation.ReflTransGen
      (fun x y => x ∈ edgeBall G e n ∧ y ∈ edgeBall G e n ∧ Adj G x y) e.1.1 v := by
  rcases hv with hv | hv
  · exact Relation.ReflTransGen.mono
      (fun x y h => ⟨Or.inl h.1, Or.inl h.2.1, h.2.2⟩) _ _ (vertexBall_reachable hv)
  · exact (Relation.ReflTransGen.single
      ⟨fst_mem_edgeBall G e n, snd_mem_edgeBall G e n, he⟩).trans
        (Relation.ReflTransGen.mono
          (fun x y h => ⟨Or.inr h.1, Or.inr h.2.1, h.2.2⟩) _ _ (vertexBall_reachable hv))

private theorem ballAdj_symm {G : GraphCode} {u v : ℕ} (h : Adj G u v) : Adj G v u :=
  (G.2.2 v u).trans h

private theorem ballAdj_ne {G : GraphCode} {u v : ℕ} (h : Adj G u v) : u ≠ v := by
  rintro rfl
  have hfalse := G.2.1 u
  simp [Adj, hfalse] at h

@[simp] theorem rawPair_mem_ballInducedSubgraph (G : GraphCode) (s : Finset ℕ)
    (u v : ℕ) :
    rawPair u v ∈ (ballInducedSubgraph G s).2 ↔ u ∈ s ∧ v ∈ s ∧ Adj G u v := by
  by_cases huv : u < v
  · simp [rawPair, huv]
  · simp only [rawPair, ite_eq_right huv, mem_ballInducedSubgraph_edges]
    constructor
    · rintro ⟨hv, hu, _, hAdj⟩
      exact ⟨hu, hv, ballAdj_symm hAdj⟩
    · rintro ⟨hu, hv, hAdj⟩
      exact ⟨hv, hu, lt_of_le_of_ne (Nat.le_of_not_gt huv) (Ne.symm (ballAdj_ne hAdj)),
        ballAdj_symm hAdj⟩

@[simp] theorem subgraphAdj_ballInducedSubgraph (G : GraphCode) (s : Finset ℕ)
    (u v : ℕ) :
    SubgraphAdj (ballInducedSubgraph G s) u v ↔ u ∈ s ∧ v ∈ s ∧ Adj G u v := by
  simp only [SubgraphAdj, ballInducedSubgraph_vertices, rawPair_mem_ballInducedSubgraph]
  tauto

@[simp] theorem subgraphAdj_edgeBallSubgraph (G : GraphCode)
    (hG : GraphLocallyFinite G) (e : EdgeCode) (n u v : ℕ) :
    SubgraphAdj (edgeBallSubgraph G hG e n) u v ↔
      u ∈ edgeBall G e n ∧ v ∈ edgeBall G e n ∧ Adj G u v := by
  simp [edgeBallSubgraph]

theorem isFiniteConnectedSubgraph_edgeBallSubgraph {G : GraphCode}
    (hG : GraphLocallyFinite G) (e : EdgeCode) (he : Adj G e.1.1 e.1.2) (n : ℕ) :
    IsFiniteConnectedSubgraph G (edgeBallSubgraph G hG e n) := by
  refine ⟨⟨e.1.1, by simp⟩, ?_, ?_⟩
  · intro p hp
    simpa [edgeBallSubgraph] using hp
  · intro u hu v hv
    have path (w : ℕ) (hw : w ∈ (edgeBallSubgraph G hG e n).1) :
        Relation.ReflTransGen (SubgraphAdj (edgeBallSubgraph G hG e n)) e.1.1 w := by
      apply Relation.ReflTransGen.mono (fun x y hxy =>
        (subgraphAdj_edgeBallSubgraph G hG e n x y).mpr hxy) _ _
        (edgeBall_reachable he ((mem_edgeBallSubgraph_vertices G hG e n w).mp hw))
    let : Std.Symm (SubgraphAdj (edgeBallSubgraph G hG e n)) := ⟨fun x y hxy => by
      rw [subgraphAdj_edgeBallSubgraph] at hxy ⊢
      exact ⟨hxy.2.1, hxy.1, ballAdj_symm hxy.2.2⟩⟩
    exact (symm (path u hu)).trans (path v hv)

theorem isConnectedExhaustion_edgeBallSubgraph {G : GraphCode}
    (hC : GraphConnected G) (hL : GraphLocallyFinite G)
    (e : EdgeCode) (he : Adj G e.1.1 e.1.2) :
    IsConnectedExhaustion G (edgeBallSubgraph G hL e) := by
  refine ⟨isFiniteConnectedSubgraph_edgeBallSubgraph hL e he, ?_, ?_⟩
  · intro n
    constructor
    · intro v hv
      rw [mem_edgeBallSubgraph_vertices] at hv ⊢
      exact edgeBall_mono G e (Nat.le_succ n) hv
    · intro p hp
      rw [mem_edgeBallSubgraph_edges] at hp ⊢
      exact ⟨edgeBall_mono G e (Nat.le_succ n) hp.1,
        edgeBall_mono G e (Nat.le_succ n) hp.2.1, hp.2.2⟩
  · intro u v huv hAdj
    obtain ⟨m, hm⟩ := GraphConnected.exists_mem_edgeBall hC e u
    obtain ⟨n, hn⟩ := GraphConnected.exists_mem_edgeBall hC e v
    refine ⟨max m n, ?_⟩
    rw [mem_edgeBallSubgraph_edges]
    exact ⟨edgeBall_mono G e (le_max_left m n) hm,
      edgeBall_mono G e (le_max_right m n) hn, huv, hAdj⟩

end IntrinsicExhaustion
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_USTInclusionCount
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem336.USTInclusionCount

theorem ustCylinder_positive_toReal (K : FiniteSubgraphCode) (A : Finset EdgeCode) :
    (ustCylinder K A ∅).toReal =
      (((spanningTrees K).filter (fun T => edgePairs A ⊆ T)).card : ℝ) /
        ((spanningTrees K).card : ℝ) := by
  classical
  simp [ustCylinder, edgePairs_subset_iff, ENNReal.toReal_div]

theorem supportedPairs_map (K : FiniteSubgraphCode) (A : Finset EdgeCode)
    (hA : ∀ e ∈ A, e.val ∈ K.2) :
    (supportedPairs K A).map (Function.Embedding.subtype (fun p => p ∈ K.2)) =
      edgePairs A :=
  Finset.subtype_map_of_mem (fun _ hp => (edgePairs_subset_iff A K.2).mpr hA hp)

theorem det_required_reindex {R : Type*} [CommRing R]
    (K : FiniteSubgraphCode) (A : Finset EdgeCode)
    (hA : ∀ e ∈ A, e.val ∈ K.2) (M : Matrix K.2 K.2 R) :
    Matrix.det (fun e f : A =>
      M ⟨e.val.val, hA e.val e.property⟩ ⟨f.val.val, hA f.val f.property⟩) =
      Matrix.det (M.submatrix
        (Subtype.val : supportedPairs K A → K.2)
        (Subtype.val : supportedPairs K A → K.2)) := by
  exact Matrix.det_submatrix_equiv_self (requiredEdgeEquiv K A hA)
    (M.submatrix Subtype.val Subtype.val)

end Problem336.USTInclusionCount

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_USTFiniteDeterminantal
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ENNReal

namespace Problem336.FreeKernel

open USTInclusionCount

variable {G : GraphCode} {K : FiniteSubgraphCode}

theorem ustCylinder_toReal_eq_finiteKernel_minor_of_contained
    (hK : IsFiniteConnectedSubgraph G K) (A : Finset EdgeCode)
    (hA : ∀ e ∈ A, e.val ∈ K.2) :
    (ustCylinder K A ∅).toReal =
      Matrix.det (fun e f : A => inner ℝ (edgeVector e.val)
        (finiteKernel K (edgeVector f.val))) := by
  classical
  let root : K.1 := ⟨hK.1.choose, hK.1.choose_spec⟩
  have hf : SubtypeSubsetSums.forget K.2 (supportedPairs K A) = edgePairs A :=
    supportedPairs_map K A hA
  rw [ustCylinder_positive_toReal]
  have hc := CodeTransferKernel.code_tree_inclusion_ratio_finiteKernel hK root
    (supportedPairs K A)
  rw [hf] at hc
  rw [hc]
  exact (det_required_reindex K A hA
    (fun e f : K.2 => inner ℝ (edgeVector (CodeTransferKernel.edgeEquiv hK e).val)
      (finiteKernel K (edgeVector (CodeTransferKernel.edgeEquiv hK f).val)))).symm

theorem spanningTrees_card_ne_zero (hK : IsFiniteConnectedSubgraph G K) :
    (spanningTrees K).card ≠ 0 := by
  let root : K.1 := ⟨hK.1.choose, hK.1.choose_spec⟩
  have hd := codeWeightedLaplacian_det_ne_zero hK root (fun _ => 1)
    (fun _ => by norm_num)
  rw [codeWeightedLaplacian_det_eq_tree_count] at hd
  exact_mod_cast hd

theorem ustCylinder_eq_finiteKernel_minor_of_contained
    (hK : IsFiniteConnectedSubgraph G K) (A : Finset EdgeCode)
    (hA : ∀ e ∈ A, e.val ∈ K.2) :
    ustCylinder K A ∅ = ENNReal.ofReal
      (Matrix.det (fun e f : A => inner ℝ (edgeVector e.val)
        (finiteKernel K (edgeVector f.val)))) := by
  rw [← ustCylinder_toReal_eq_finiteKernel_minor_of_contained hK A hA]
  apply (ENNReal.ofReal_toReal ?_).symm
  unfold ustCylinder
  apply ENNReal.div_ne_top
  · exact ENNReal.natCast_ne_top _
  · exact_mod_cast spanningTrees_card_ne_zero hK

theorem ustCylinder_eq_finiteKernel_minor
    (hK : IsFiniteConnectedSubgraph G K) (A : Finset EdgeCode) :
    ustCylinder K A ∅ = ENNReal.ofReal
      (Matrix.det (fun e f : A => inner ℝ (edgeVector e.val)
        (finiteKernel K (edgeVector f.val)))) :=
  inclusion_identity_of_contained_identity K
    (ustCylinder_eq_finiteKernel_minor_of_contained hK) A

end Problem336.FreeKernel

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GraphFUSFLaw
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336

theorem exists_connectedExhaustion (G : GraphCode)
    (hC : GraphConnected G) (hL : GraphLocallyFinite G) :
    ∃ H : ℕ → FiniteSubgraphCode, IsConnectedExhaustion G H := by
  obtain ⟨v, hv⟩ := hC.exists_adj 0
  have hv0 : v ≠ 0 := by
    intro h
    subst v
    simp [Adj, G.2.1 0] at hv
  let e : EdgeCode := ⟨(0, v), Nat.pos_of_ne_zero hv0⟩
  exact ⟨IntrinsicExhaustion.edgeBallSubgraph G hL e,
    IntrinsicExhaustion.isConnectedExhaustion_edgeBallSubgraph hC hL e hv⟩

theorem exists_hasFUSFLaw_of_finite_identity (G : GraphCode)
    (hC : GraphConnected G) (hL : GraphLocallyFinite G)
    (hfinite : ∀ K : FiniteSubgraphCode, IsFiniteConnectedSubgraph G K →
      ∀ A : Finset EdgeCode,
        ustCylinder K A ∅ = FreeKernel.finiteInclusionMinor K A) :
    ∃ μ : ProbabilityMeasure EdgeConfiguration,
      HasFUSFLaw G (μ : Measure EdgeConfiguration) id := by
  obtain ⟨H, hH⟩ := exists_connectedExhaustion G hC hL
  exact exists_hasFUSFLaw_of_inclusion_limits G H hH
    (FreeKernel.inclusionMinorLimit G)
    (FreeKernel.common_inclusion_limits_of_finite_identity G hfinite)

theorem exists_hasFUSFLaw_oai (G : GraphCode)
    (hC : GraphConnected G) (hL : GraphLocallyFinite G) :
    ∃ μ : ProbabilityMeasure EdgeConfiguration,
      HasFUSFLaw G (μ : Measure EdgeConfiguration) id := by
  apply exists_hasFUSFLaw_of_finite_identity G hC hL
  intro K hK A
  exact FreeKernel.ustCylinder_eq_finiteKernel_minor hK A

end Problem336

end

end OAI
end

theorem solution : type_of% @OAI.Problem336.exists_hasFUSFLaw_oai := @OAI.Problem336.exists_hasFUSFLaw_oai
