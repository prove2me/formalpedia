-- Prove2me | solution 1 for OAI.Problem336.fusf_is_factor_iid
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:42:04.313906+00:00
-- url     : https://prove2.me/submissions/b10f0598-80f6-4d94-b8df-86d117bb28f3

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
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Definitions.Def_FreeUniformSpanningForest
import Definitions.Def_OAIS336000
import Theorems.Thm_OAI_Problem336_FinalFactor_worksOnGraph

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
-- module Solutions.OAIS_P336.SpanningForest_EdgeAllocation
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem336
namespace EdgeAllocation

lemma source_relabel (σ : Equiv ℕ ℕ) {key : ℕ → ℝ}
    (hkey : Function.Injective key) (e : EdgeCode) :
    source (relabelLabels σ key) (mapEdge σ e) = σ (source key e) := by
  have hne : key e.1.1 ≠ key e.1.2 := fun h => Nat.ne_of_lt e.2 (hkey h)
  by_cases hs : σ e.1.1 < σ e.1.2
  · simp [source, mapEdge, mkEdge, hs, relabelLabels]
    split_ifs <;> rfl
  · by_cases hk : key e.1.1 < key e.1.2
    · simp [source, mapEdge, mkEdge, hs, relabelLabels, hk, not_lt_of_gt hk]
    · have hr : key e.1.2 < key e.1.1 := lt_of_le_of_ne (le_of_not_gt hk) hne.symm
      simp [source, mapEdge, mkEdge, hs, relabelLabels, hk, hr]

lemma target_relabel (σ : Equiv ℕ ℕ) {key : ℕ → ℝ}
    (hkey : Function.Injective key) (e : EdgeCode) :
    target (relabelLabels σ key) (mapEdge σ e) = σ (target key e) := by
  have hne : key e.1.1 ≠ key e.1.2 := fun h => Nat.ne_of_lt e.2 (hkey h)
  by_cases hs : σ e.1.1 < σ e.1.2
  · simp [target, mapEdge, mkEdge, hs, relabelLabels]
    split_ifs <;> rfl
  · by_cases hk : key e.1.1 < key e.1.2
    · simp [target, mapEdge, mkEdge, hs, relabelLabels, hk, not_lt_of_gt hk]
    · have hr : key e.1.2 < key e.1.1 := lt_of_le_of_ne (le_of_not_gt hk) hne.symm
      simp [target, mapEdge, mkEdge, hs, relabelLabels, hk, hr]

end EdgeAllocation
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_EdgeAction
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336

theorem mapEdge_injective (σ : Equiv ℕ ℕ) : Function.Injective (mapEdge σ) :=
  (edgeEquiv σ).injective

theorem mapEdge_surjective (σ : Equiv ℕ ℕ) : Function.Surjective (mapEdge σ) :=
  (edgeEquiv σ).surjective

@[simp] theorem mapEdge_inj (σ : Equiv ℕ ℕ) (e f : EdgeCode) :
    mapEdge σ e = mapEdge σ f ↔ e = f := (mapEdge_injective σ).eq_iff

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GraphBalls
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336

theorem withinRadius_succ (G : GraphCode) (n u v : ℕ) :
    withinRadius G (n + 1) u v ↔ withinRadius G n u v ∨
      ∃ w, withinRadius G n u w ∧ Adj G w v := Iff.rfl

theorem measurableSet_adj (u v : ℕ) :
    MeasurableSet {G : GraphCode | Adj G u v} := by
  exact measurableSet_eq_fun
    ((measurable_pi_apply v).comp ((measurable_pi_apply u).comp measurable_subtype_coe))
    measurable_const

theorem measurableSet_withinRadius (n u v : ℕ) :
    MeasurableSet {G : GraphCode | withinRadius G n u v} := by
  induction n generalizing u v with
  | zero =>
      by_cases h : u = v <;> simp [withinRadius, h]
  | succ n ih =>
      simp only [withinRadius, Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
      exact (ih u v).union (MeasurableSet.iUnion fun w =>
        (ih u w).inter (measurableSet_adj w v))

@[simp] theorem withinRadius_relabel (σ : Equiv ℕ ℕ) (G : GraphCode)
    (n u v : ℕ) :
    withinRadius (relabelGraph σ G) n (σ u) (σ v) ↔ withinRadius G n u v := by
  induction n generalizing u v with
  | zero => simp [withinRadius]
  | succ n ih =>
      simp only [withinRadius_succ, ih]
      constructor
      · rintro (h | ⟨w, hw, hwv⟩)
        · exact Or.inl h
        · right
          refine ⟨σ.symm w, ?_, ?_⟩
          · simpa using (ih u (σ.symm w)).mp (by simpa using hw)
          · simpa [Adj, relabelGraph] using hwv
      · rintro (h | ⟨w, hw, hwv⟩)
        · exact Or.inl h
        · right
          exact ⟨σ w, (ih u w).mpr hw, by simpa [Adj, relabelGraph] using hwv⟩

theorem measurableSet_mem_edgeBall (n v : ℕ) (e : EdgeCode) :
    MeasurableSet {G : GraphCode | v ∈ edgeBall G n e} :=
  (measurableSet_withinRadius n e.val.1 v).union
    (measurableSet_withinRadius n e.val.2 v)

theorem mem_edgeBall_mkEdge (G : GraphCode) (n u v w : ℕ) (h : u ≠ v) :
    w ∈ edgeBall G n (mkEdge u v h) ↔
      withinRadius G n u w ∨ withinRadius G n v w := by
  unfold edgeBall mkEdge
  split_ifs <;> simp only [Set.mem_ofPred_eq]; tauto

@[simp] theorem mem_edgeBall_mapEdge (σ : Equiv ℕ ℕ) (G : GraphCode)
    (n v : ℕ) (e : EdgeCode) :
    σ v ∈ edgeBall (relabelGraph σ G) n (mapEdge σ e) ↔ v ∈ edgeBall G n e := by
  unfold mapEdge
  rw [mem_edgeBall_mkEdge]
  simp only [withinRadius_relabel]
  rfl

theorem edgeBall_relabel (σ : Equiv ℕ ℕ) (G : GraphCode)
    (n : ℕ) (e : EdgeCode) :
    edgeBall (relabelGraph σ G) n (mapEdge σ e) = σ '' edgeBall G n e := by
  ext v
  constructor
  · intro hv
    refine ⟨σ.symm v, ?_, by simp⟩
    exact (mem_edgeBall_mapEdge σ G n (σ.symm v) e).mp (by simpa using hv)
  · rintro ⟨w, hw, rfl⟩
    exact (mem_edgeBall_mapEdge σ G n w e).mpr hw

theorem measurable_edgeBall (n : ℕ) (e : EdgeCode) :
    Measurable (fun G : GraphCode => edgeBall G n e) := by
  exact Measurable.of_eval fun v =>
    measurableSet_setOfPred.mp (measurableSet_mem_edgeBall n v e)

theorem measurable_edgeBall_joint :
    Measurable (fun q : GraphCode × (ℕ × EdgeCode) => edgeBall q.1 q.2.1 q.2.2) :=
  measurable_from_prod_countable_left fun ne => measurable_edgeBall ne.1 ne.2

theorem finiteSetCode_eq_iff (s : Set ℕ) (t : Finset ℕ) :
    finiteSetCode s = t ↔ s = (t : Set ℕ) ∨ (t = ∅ ∧ ¬s.Finite) := by
  classical
  by_cases hs : s.Finite
  · simp only [finiteSetCode, hs, not_true_eq_false, and_false, or_false]
    rw [← Finset.coe_inj]
    simp
  · have hne : s ≠ (t : Set ℕ) := fun h => hs (h ▸ t.finite_toSet)
    simp [finiteSetCode, hs, hne, eq_comm]

theorem measurable_finiteSetCode : Measurable finiteSetCode := by
  have hf (t : Finset ℕ) : MeasurableSet {s : Set ℕ | finiteSetCode s = t} := by
    simp only [finiteSetCode_eq_iff]
    exact ((measurable_id.eq_const (t : Set ℕ)).or
      (measurable_const.and (measurableSet_setOfPred.mp
        Set.Countable.ofPred_finite.measurableSet).not)).setOf
  exact measurable_to_countable fun s => hf (finiteSetCode s)

theorem measurable_edgeBallCode :
    Measurable (fun q : GraphCode × (ℕ × EdgeCode) => edgeBallCode q.1 q.2.1 q.2.2) :=
  measurable_finiteSetCode.comp measurable_edgeBall_joint

theorem finiteSetCode_image (σ : Equiv ℕ ℕ) (s : Set ℕ) :
    finiteSetCode (σ '' s) = (finiteSetCode s).image σ := by
  classical
  by_cases hs : s.Finite
  · rw [finiteSetCode_of_finite s hs,
      finiteSetCode_of_finite (σ '' s) (hs.image σ)]
    exact hs.toFinset_image σ (hs.image σ)
  · have hi : ¬(σ '' s).Finite := fun h => hs (h.of_finite_image σ.injective.injOn)
    simp [finiteSetCode, hs, hi]

theorem edgeBallCode_relabel (σ : Equiv ℕ ℕ) (G : GraphCode)
    (n : ℕ) (e : EdgeCode) :
    edgeBallCode (relabelGraph σ G) n (mapEdge σ e) = (edgeBallCode G n e).image σ := by
  unfold edgeBallCode
  rw [edgeBall_relabel, finiteSetCode_image]

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_AllPairAllocation
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem336.AllPairAllocation

theorem radius_relabel (σ : Equiv ℕ ℕ) (G : GraphCode) (u v : ℕ) :
    radius (relabelGraph σ G) (σ u) (σ v) = radius G u v := by
  classical
  unfold radius
  apply Nat.find_congr'
  intro n
  simp only [radiusPredicate, withinRadius_relabel]

theorem measurable_radius (u v : ℕ) :
    Measurable (fun G : GraphCode => radius G u v) := by
  classical
  unfold radius
  apply measurable_find
  intro n
  simp only [radiusPredicate, Set.ofPred_or]
  refine (measurableSet_withinRadius n u v).union ?_
  convert (MeasurableSet.iUnion (fun m => measurableSet_withinRadius m u v)).compl using 1
  ext G
  simp

theorem ballRank_relabel (σ : Equiv ℕ ℕ) (G : GraphCode) (key : ℕ → ℝ)
    (n u v : ℕ) :
    ballRank (relabelGraph σ G) (relabelLabels σ key) n (σ u) (σ v) =
      ballRank G key n u v := by
  unfold ballRank
  have hs : {w | withinRadius (relabelGraph σ G) n (σ u) w ∧
      relabelLabels σ key w < relabelLabels σ key (σ v)} =
      σ '' {w | withinRadius G n u w ∧ key w < key v} := by
    ext w
    constructor
    · intro h
      refine ⟨σ.symm w, ?_, σ.apply_symm_apply w⟩
      constructor
      · exact (withinRadius_relabel σ G n u (σ.symm w)).mp (by simpa using h.1)
      · simpa [relabelLabels] using h.2
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(withinRadius_relabel σ G n u x).mpr hx.1,
        by simpa [relabelLabels] using hx.2⟩
  rw [hs, Set.ncard_image_of_injective _ σ.injective]

theorem coordinate_relabel (σ : Equiv ℕ ℕ) (G : GraphCode) {key : ℕ → ℝ}
    (hk : Function.Injective key) (e : EdgeCode) :
    coordinate (relabelGraph σ G) (relabelLabels σ key) (mapEdge σ e) =
      (σ (coordinate G key e).1, (coordinate G key e).2) := by
  simp only [coordinate, EdgeAllocation.source_relabel σ hk,
    EdgeAllocation.target_relabel σ hk, radius_relabel, ballRank_relabel]

theorem coordinateNat_relabel (σ : Equiv ℕ ℕ) (G : GraphCode) {key : ℕ → ℝ}
    (hk : Function.Injective key) (e : EdgeCode) :
    coordinateNat (relabelGraph σ G) (relabelLabels σ key) (mapEdge σ e) =
      (σ (coordinateNat G key e).1, (coordinateNat G key e).2) := by
  simp only [coordinateNat, coordinate_relabel σ G hk]

theorem measurable_radius_joint :
    Measurable (fun q : GraphCode × (ℕ × ℕ) => radius q.1 q.2.1 q.2.2) :=
  measurable_from_prod_countable_left fun p => measurable_radius p.1 p.2

theorem measurable_ballRank (n u v : ℕ) :
    Measurable (fun q : GraphCode × (ℕ → ℝ) => ballRank q.1 q.2 n u v) := by
  apply measurable_ncard.comp
  apply measurable_set_iff.mpr
  intro w
  change Measurable (fun q : GraphCode × (ℕ → ℝ) =>
    withinRadius q.1 n u w ∧ q.2 w < q.2 v)
  apply Measurable.and
  · exact (measurableSet_setOfPred.mp (measurableSet_withinRadius n u w)).comp measurable_fst
  · exact measurableSet_setOfPred.mp
      (measurableSet_lt (measurable_snd.eval) (measurable_snd.eval))

theorem measurable_ballRank_joint :
    Measurable (fun q : (GraphCode × (ℕ → ℝ)) × (ℕ × (ℕ × ℕ)) =>
      ballRank q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2) :=
  measurable_from_prod_countable_left fun p => measurable_ballRank p.1 p.2.1 p.2.2

theorem measurable_coordinate :
    Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      coordinate q.1.1 q.1.2 q.2) := by
  have hs : Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      EdgeAllocation.source q.1.2 q.2) :=
    EdgeAllocation.measurable_source_joint.comp (measurable_fst.snd.prodMk measurable_snd)
  have ht : Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      EdgeAllocation.target q.1.2 q.2) :=
    EdgeAllocation.measurable_target_joint.comp (measurable_fst.snd.prodMk measurable_snd)
  have hn : Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      radius q.1.1 (EdgeAllocation.source q.1.2 q.2) (EdgeAllocation.target q.1.2 q.2)) :=
    measurable_radius_joint.comp (measurable_fst.fst.prodMk (hs.prodMk ht))
  exact hs.prodMk (hn.prodMk (measurable_ballRank_joint.comp
    (measurable_fst.prodMk (hn.prodMk (hs.prodMk ht)))))

theorem measurable_coordinateNat :
    Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      coordinateNat q.1.1 q.1.2 q.2) := by
  have hm : Measurable (fun c : ℕ × (ℕ × ℕ) => (c.1, Nat.pair c.2.1 c.2.2)) :=
    Measurable.of_discrete
  exact hm.comp measurable_coordinate

end Problem336.AllPairAllocation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_NoCollisionExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336

theorem injective_relabelLabels_iff (σ : Equiv ℕ ℕ) (U : ℕ → ℝ) :
    Function.Injective (relabelLabels σ U) ↔ Function.Injective U := by
  constructor
  · intro h u v huv
    have heq : relabelLabels σ U (σ u) = relabelLabels σ U (σ v) := by
      simpa [relabelLabels] using huv
    exact σ.injective (h heq)
  · intro h u v huv
    exact σ.symm.injective (h huv)

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_AllPairIID
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem336.AllPairIID

theorem measurable_raw_joint :
    Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode => raw q.1.1 q.1.2 q.2) := by
  have hk := EdgeIID.measurable_keys.comp
    (measurable_fst.snd : Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode => q.1.2))
  have hp := EdgeIID.measurable_pool.comp
    (measurable_fst.snd : Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode => q.1.2))
  have ha := AllPairAllocation.measurable_coordinateNat.comp
    ((measurable_fst.fst.prodMk hk).prodMk measurable_snd)
  have he : Measurable (fun p : ((ℕ × ℕ) → ℝ) × (ℕ × ℕ) => p.1 p.2) :=
    measurable_from_prod_countable_left fun p => measurable_pi_apply p
  exact he.comp (hp.prodMk ha)

theorem measurable_uniformRule :
    Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      uniformRule q.1.1 q.1.2 q.2) := by
  classical
  exact Measurable.ite
    (measurable_injective_keyField.comp
      (EdgeIID.measurable_keys.comp measurable_fst.snd)).setOf
    measurable_raw_joint measurable_const

theorem measurable_uniformRule_uncurried :
    Measurable (fun q : GraphCode × ((ℕ → ℝ) × EdgeCode) =>
      uniformRule q.1 q.2.1 q.2.2) :=
  measurable_uniformRule.comp
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)

theorem raw_relabel (σ : Equiv ℕ ℕ) (G : GraphCode) (U : ℕ → ℝ)
    (hk : Function.Injective (EdgeIID.keys U)) (e : EdgeCode) :
    raw (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) = raw G U e := by
  unfold raw
  rw [show EdgeIID.keys (relabelLabels σ U) = relabelLabels σ (EdgeIID.keys U) from rfl,
    AllPairAllocation.coordinateNat_relabel σ G hk]
  simp [EdgeIID.pool, EdgeIID.expanded, relabelLabels]

theorem uniformRule_equivariant (σ : Equiv ℕ ℕ) (G : GraphCode)
    (U : ℕ → ℝ) (e : EdgeCode) :
    uniformRule (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) =
      uniformRule G U e := by
  by_cases hk : Function.Injective (EdgeIID.keys U)
  · simp only [uniformRule,
      show EdgeIID.keys (relabelLabels σ U) = relabelLabels σ (EdgeIID.keys U) from rfl,
      injective_relabelLabels_iff, hk, ite_true]
    exact raw_relabel σ G U hk e
  · simp only [uniformRule,
      show EdgeIID.keys (relabelLabels σ U) = relabelLabels σ (EdgeIID.keys U) from rfl,
      injective_relabelLabels_iff, hk, ite_false]

end Problem336.AllPairIID

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_Picard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace Problem336.Picard

variable {ι : Type*}

lemma measurable_parametric_intervalIntegral
    {α : Type*} [MeasurableSpace α] (f : α → ℝ → ℝ)
    (hf : Measurable (Function.uncurry f)) (a d : α → ℝ)
    (ha : Measurable a) (hd : Measurable d) :
    Measurable (fun x => ∫ s in a x..d x, f x s) := by
  classical
  have hi (a d : α → ℝ) (ha : Measurable a) (hd : Measurable d) :
      Measurable (fun x => ∫ s in Ioc (a x) (d x), f x s) := by
    have hm : Measurable (fun q : α × ℝ =>
        if a q.1 < q.2 ∧ q.2 ≤ d q.1 then f q.1 q.2 else 0) := by
      exact Measurable.ite
        ((measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
          (measurableSet_le measurable_snd (hd.comp measurable_fst))) hf measurable_const
    have hh := hm.stronglyMeasurable.integral_prod_right' (ν := volume)
    convert hh.measurable using 1
    funext x
    rw [← integral_indicator measurableSet_Ioc]
    simp only [Set.indicator, Set.mem_Ioc]
  exact (hi a d ha hd).sub (hi d a hd ha)

lemma measurable_iterate
    {α : Type*} [MeasurableSpace α]
    (w : α → ι → ℝ → ℝ) (b : α → ℝ → (ι → ℝ) → ι → ℝ)
    (hw : ∀ i, Measurable (fun p : α × ℝ => w p.1 i p.2))
    (hb : ∀ i, Measurable
      (fun p : α × (ℝ × (ι → ℝ)) => b p.1 p.2.1 p.2.2 i)) :
    ∀ n i, Measurable (fun p : α × ℝ => iterate (w p.1) (b p.1) n i p.2) := by
  intro n
  induction n with
  | zero => exact hw
  | succ n ih =>
    intro i
    apply (hw i).add
    apply measurable_parametric_intervalIntegral
      (fun p : α × ℝ => fun s => b p.1 s
        (fun j => iterate (w p.1) (b p.1) n j s) i)
      _ (fun _ => 0) Prod.snd measurable_const measurable_snd
    exact (hb i).comp (measurable_fst.fst.prodMk
      (measurable_snd.prodMk (Measurable.of_eval (fun j =>
        (ih j).comp (measurable_fst.fst.prodMk measurable_snd)))))

lemma measurable_decode
    {α : Type*} [MeasurableSpace α]
    (w : α → ι → ℝ → ℝ) (b : α → ℝ → (ι → ℝ) → ι → ℝ)
    (hw : ∀ i, Measurable (fun p : α × ℝ => w p.1 i p.2))
    (hb : ∀ i, Measurable
      (fun p : α × (ℝ × (ι → ℝ)) => b p.1 p.2.1 p.2.2 i)) (i : ι) :
    Measurable (fun p : α × ℝ => decode (w p.1) (b p.1) i p.2) := by
  exact (StronglyMeasurable.limUnder (l := atTop)
    (fun n => (measurable_iterate w b hw hb n i).stronglyMeasurable)).measurable

lemma iterate_relabel
    {κ : Type*} (e : ι ≃ κ)
    (w : ι → ℝ → ℝ) (w' : κ → ℝ → ℝ)
    (b : ℝ → (ι → ℝ) → ι → ℝ) (b' : ℝ → (κ → ℝ) → κ → ℝ)
    (hw : ∀ i t, w' (e i) t = w i t)
    (hb : ∀ t (y : ι → ℝ) i,
      b' t (fun k => y (e.symm k)) (e i) = b t y i) :
    ∀ n i t, iterate w' b' n (e i) t = iterate w b n i t := by
  intro n
  induction n with
  | zero => exact hw
  | succ n ih =>
    intro i t
    simp only [iterate, hw]
    congr 1
    apply congrArg (fun f : ℝ → ℝ => ∫ s in (0 : ℝ)..t, f s)
    funext s
    have hfield : (fun k => iterate w' b' n k s) =
        (fun k => iterate w b n (e.symm k) s) := by
      funext k
      simpa using ih (e.symm k) s
    rw [hfield]
    exact hb s (fun j => iterate w b n j s) i

lemma decode_relabel
    {κ : Type*} (e : ι ≃ κ)
    (w : ι → ℝ → ℝ) (w' : κ → ℝ → ℝ)
    (b : ℝ → (ι → ℝ) → ι → ℝ) (b' : ℝ → (κ → ℝ) → κ → ℝ)
    (hw : ∀ i t, w' (e i) t = w i t)
    (hb : ∀ t (y : ι → ℝ) i,
      b' t (fun k => y (e.symm k)) (e i) = b t y i) (i : ι) (t : ℝ) :
    decode w' b' (e i) t = decode w b i t := by
  unfold decode
  congr 1
  funext n
  exact iterate_relabel e w w' b b' hw hb n i t

end Problem336.Picard

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FactorAssembly
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Problem336
namespace FactorAssembly

theorem measurable_decodedPath {b : GraphDrift} {w : GraphNoise}
    (hb : DriftBorel b) (hw : NoiseBorel w) (e : EdgeCode) :
    Measurable (fun p : (GraphCode × (ℕ → ℝ)) × ℝ =>
      Picard.decode (w p.1.1 p.1.2) (b p.1.1) e p.2) := by
  apply Picard.measurable_decode
    (w := fun p : GraphCode × (ℕ → ℝ) => w p.1 p.2)
    (b := fun p : GraphCode × (ℕ → ℝ) => b p.1) hw
  intro i
  exact (hb i).comp (measurable_fst.fst.prodMk measurable_snd)

theorem measurable_decodedSlope {b : GraphDrift} {w : GraphNoise}
    (hb : DriftBorel b) (hw : NoiseBorel w) (e : EdgeCode) (n : ℕ) :
    Measurable (fun p : GraphCode × (ℕ → ℝ) => decodedSlope b w p.1 p.2 e n) := by
  exact ((measurable_decodedPath hb hw e).comp
    (measurable_id.prodMk measurable_const)).div_const (n : ℝ)

theorem measurable_rule_edge {b : GraphDrift} {w : GraphNoise}
    (hb : DriftBorel b) (hw : NoiseBorel w) (e : EdgeCode) :
    Measurable (fun p : GraphCode × (ℕ → ℝ) => rule b w p.1 p.2 e) := by
  classical
  have hl : Measurable (fun p : GraphCode × (ℕ → ℝ) =>
      limsup (decodedSlope b w p.1 p.2 e) atTop) :=
    Measurable.limsup (fun n => measurable_decodedSlope hb hw e n)
  change Measurable (fun p : GraphCode × (ℕ → ℝ) =>
    if (1 / 2 : ℝ) < limsup (decodedSlope b w p.1 p.2 e) atTop then true else false)
  exact Measurable.ite (measurableSet_lt measurable_const hl) measurable_const measurable_const

theorem ruleBorel_of_coordinate_measurable (Phi : FactorRule)
    (hPhi : ∀ e, Measurable (fun p : GraphCode × (ℕ → ℝ) => Phi p.1 p.2 e)) :
    RuleBorel Phi := by
  have hall : Measurable (fun p : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      Phi p.1.1 p.1.2 p.2) :=
    measurable_from_prod_countable_left hPhi
  have hpair : Measurable (fun q : GraphCode × ((ℕ → ℝ) × EdgeCode) =>
      ((q.1, q.2.1), q.2.2)) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  exact hall.comp hpair

theorem rule_borel {b : GraphDrift} {w : GraphNoise}
    (hb : DriftBorel b) (hw : NoiseBorel w) : RuleBorel (rule b w) :=
  ruleBorel_of_coordinate_measurable (rule b w) (measurable_rule_edge hb hw)

theorem decodedPath_relabel {b : GraphDrift} {w : GraphNoise}
    (hb : DriftEquivariant b) (hw : NoiseEquivariant w)
    (σ : Equiv ℕ ℕ) (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode) (t : ℝ) :
    Picard.decode (w (relabelGraph σ G) (relabelLabels σ U))
      (b (relabelGraph σ G)) (mapEdge σ e) t =
      Picard.decode (w G U) (b G) e t := by
  exact Picard.decode_relabel (edgeEquiv σ) (w G U)
    (w (relabelGraph σ G) (relabelLabels σ U)) (b G) (b (relabelGraph σ G))
    (hw σ G U) (hb σ G) e t

theorem rule_equivariant {b : GraphDrift} {w : GraphNoise}
    (hb : DriftEquivariant b) (hw : NoiseEquivariant w) :
    RuleEquivariant (rule b w) := by
  classical
  intro σ G U e
  have hs : decodedSlope b w (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) =
      decodedSlope b w G U e := by
    funext n
    exact congrArg (fun x : ℝ => x / (n : ℝ)) (decodedPath_relabel hb hw σ G U e n)
  simp only [rule, hs]

end FactorAssembly
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_WienerSampler
attribute [-instance] _root_.OAI.Problem336.CanonicalBrownianReference.law_probability _root_.OAI.Problem336.CanonicalBrownianReference.noiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.WienerSampler

attribute [local instance] OAI.Problem336.WienerSampler.instMeasurableSpacePath
attribute [local instance] OAI.Problem336.WienerSampler.instBorelSpacePath
theorem measurable_sample : Measurable sample :=
  (Classical.choose_spec (exists_uniform01_sampler GlobalWiener.wienerMeasure)).1

end Problem336.WienerSampler

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_AllPairWiener
attribute [-instance] _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.AllPairWiener
open FactorAssembly
attribute [local instance] OAI.Problem336.AllPairWiener.instMeasurableSpacePath
local instance instBorelSpacePath : BorelSpace Path := ⟨rfl⟩

theorem measurable_pathEval : Measurable (Function.uncurry pathEval) :=
  ContinuousEval.continuous_eval.measurable.comp
    (measurable_fst.prodMk (continuous_real_toNNReal.measurable.comp measurable_snd))

theorem measurable_paths :
    Measurable (fun q : GraphCode × ((ℕ → ℝ) × EdgeCode) => paths q.1 q.2.1 q.2.2) :=
  WienerSampler.measurable_sample.comp AllPairIID.measurable_uniformRule_uncurried

theorem paths_equivariant (σ : Equiv ℕ ℕ) (G : GraphCode)
    (U : ℕ → ℝ) (e : EdgeCode) :
    paths (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) = paths G U e :=
  congrArg WienerSampler.sample (AllPairIID.uniformRule_equivariant σ G U e)

theorem noise_borel : NoiseBorel noise := by
  intro e
  have hp : Measurable (fun p : (GraphCode × (ℕ → ℝ)) × ℝ => paths p.1.1 p.1.2 e) :=
    measurable_paths.comp (measurable_fst.fst.prodMk
      (measurable_fst.snd.prodMk measurable_const))
  exact measurable_pathEval.comp (hp.prodMk measurable_snd)

theorem noise_equivariant : NoiseEquivariant noise := by
  intro σ G U e t
  exact congrArg (fun w => pathEval w t) (paths_equivariant σ G U e)

end Problem336.AllPairWiener

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CanonicalDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Problem336
namespace CanonicalDrift

theorem measurable_outerLimit {X : Type*} [MeasurableSpace X]
    {b : ℕ → X → ℝ} (hb : ∀ n, Measurable (b n)) :
    Measurable (outerLimit b) :=
  Measurable.limsup hb

end CanonicalDrift
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_InducedCode
attribute [-instance] _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem336

private theorem inducedCode_adj_symm (G : GraphCode) (u v : ℕ) : Adj G u v ↔ Adj G v u := by
  unfold Adj
  rw [G.2.2 u v]

private theorem inducedCode_adj_ne {G : GraphCode} {u v : ℕ} (h : Adj G u v) : u ≠ v := by
  intro huv
  subst v
  unfold Adj at h
  rw [G.2.1 u] at h
  contradiction

@[simp] theorem rawPair_mem_inducedCode_edges (G : GraphCode) (S : Finset ℕ) (u v : ℕ) :
    rawPair u v ∈ (inducedCode G S).2 ↔ u ∈ S ∧ v ∈ S ∧ Adj G u v := by
  rw [mem_inducedCode_edges]
  by_cases h : u < v
  · simp only [rawPair, ite_eq_left h]
    tauto
  · simp only [rawPair, ite_eq_right h]
    constructor
    · rintro ⟨hv, hu, _, hadj⟩
      exact ⟨hu, hv, (inducedCode_adj_symm G v u).mp hadj⟩
    · rintro ⟨hu, hv, hadj⟩
      exact ⟨hv, hu, by have := inducedCode_adj_ne hadj; omega,
        (inducedCode_adj_symm G u v).mp hadj⟩

@[simp] theorem subgraphAdj_inducedCode (G : GraphCode) (S : Finset ℕ) (u v : ℕ) :
    SubgraphAdj (inducedCode G S) u v ↔ u ∈ S ∧ v ∈ S ∧ Adj G u v := by
  simp only [SubgraphAdj, inducedCode_vertices, rawPair_mem_inducedCode_edges]
  tauto

theorem measurable_inducedCode {X : Type*} [MeasurableSpace X]
    {G : X → GraphCode} {S : X → Finset ℕ}
    (hG : Measurable G) (hS : Measurable S) :
    Measurable (fun x => inducedCode (G x) (S x)) := by
  have hedges : Measurable (fun x => (inducedCode (G x) (S x)).2) := by
    apply measurable_finset_iff.mpr
    intro p
    have ha : Measurable (fun x => Adj (G x) p.1 p.2) := by
      exact ((measurable_pi_apply p.2).comp
        ((measurable_pi_apply p.1).comp (measurable_subtype_coe.comp hG))).eq_const true
    have hu := (measurable_finset_iff.mp hS) p.1
    have hv := (measurable_finset_iff.mp hS) p.2
    simpa only [mem_inducedCode_edges] using hu.and (hv.and (measurable_const.and ha))
  exact hS.prodMk hedges

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_IntrinsicBridge
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336.Intrinsic

theorem measurable_exhaustion :
    Measurable (fun q : GraphCode × (ℕ × EdgeCode) => exhaustion q.1 q.2.2 q.2.1) := by
  exact measurable_inducedCode measurable_fst measurable_edgeBallCode

end Problem336.Intrinsic

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GraphTreePosterior
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.GraphTreePosterior

theorem measurable_energy (T : Finset (ℕ × ℕ)) (S : Finset EdgeCode) :
    Measurable (fun q : ℝ × (EdgeCode → ℝ) => energy T S q.1 q.2) := by
  classical
  apply Finset.measurable_sum
  intro f _
  by_cases hf : f.1 ∈ T
  · have hy : Measurable (fun q : ℝ × (EdgeCode → ℝ) => q.2 f) :=
      (measurable_pi_apply f).comp measurable_snd
    have ht : Measurable (fun q : ℝ × (EdgeCode → ℝ) => q.1 / 2) :=
      measurable_fst.div_const (2 : ℝ)
    simpa only [hf, ite_true, Pi.sub_def] using hy.sub ht
  · simp only [hf, ite_false]
    exact measurable_const

theorem measurable_weight (T : Finset (ℕ × ℕ)) (S : Finset EdgeCode) :
    Measurable (fun q : ℝ × (EdgeCode → ℝ) => weight T S q.1 q.2) :=
  (measurable_energy T S).exp

theorem measurable_partition (K : FiniteSubgraphCode) (S : Finset EdgeCode) :
    Measurable (fun q : ℝ × (EdgeCode → ℝ) => partition K S q.1 q.2) :=
  Finset.measurable_sum _ (fun T _ => measurable_weight T S)

theorem measurable_numerator (K : FiniteSubgraphCode) (e : EdgeCode) (S : Finset EdgeCode) :
    Measurable (fun q : ℝ × (EdgeCode → ℝ) => numerator K e S q.1 q.2) :=
  Finset.measurable_sum _ (fun T _ => measurable_weight T S)

theorem measurable_mean (K : FiniteSubgraphCode) (e : EdgeCode) (S : Finset EdgeCode) :
    Measurable (fun q : ℝ × (EdgeCode → ℝ) => mean K e S q.1 q.2) :=
  (measurable_numerator K e S).div (measurable_partition K S)

theorem measurable_mean_joint :
    Measurable (fun q : (FiniteSubgraphCode × (EdgeCode × Finset EdgeCode)) ×
        (ℝ × (EdgeCode → ℝ)) => mean q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2) := by
  apply measurable_from_prod_countable_right
  intro q
  exact measurable_mean q.1 q.2.1 q.2.2

theorem measurable_edgeCodes : Measurable edgeCodes := measurable_of_countable _

theorem measurable_finiteBallMean (e : EdgeCode) (n m : ℕ) :
    Measurable (fun q : GraphCode × (ℝ × (EdgeCode → ℝ)) =>
      finiteBallMean q.1 e n m q.2.1 q.2.2) := by
  let Ω := GraphCode × (ℝ × (EdgeCode → ℝ))
  have hK0 : Measurable (fun G : GraphCode => Intrinsic.exhaustion G e m) :=
    Intrinsic.measurable_exhaustion.comp (measurable_id.prodMk
      (measurable_const : Measurable (fun _ : GraphCode => (m, e))))
  have hS0 : Measurable (fun G : GraphCode => Intrinsic.exhaustion G e n) :=
    Intrinsic.measurable_exhaustion.comp (measurable_id.prodMk
      (measurable_const : Measurable (fun _ : GraphCode => (n, e))))
  have hK : Measurable (fun q : Ω => Intrinsic.exhaustion q.1 e m) :=
    hK0.comp measurable_fst
  have hS : Measurable (fun q : Ω => edgeCodes (Intrinsic.exhaustion q.1 e n)) :=
    measurable_edgeCodes.comp (hS0.comp measurable_fst)
  have hE : Measurable (fun _ : Ω => e) := measurable_const
  have hF : Measurable (fun q : Ω => q.2) := measurable_snd
  have hArgs := (hK.prodMk (hE.prodMk hS)).prodMk hF
  have h := measurable_mean_joint.comp hArgs
  simpa only [Function.comp_def, finiteBallMean] using h

end Problem336.GraphTreePosterior

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_IntrinsicTreeDrift
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace Problem336.GraphTreePosterior

theorem measurable_innerMean (e : EdgeCode) (n : ℕ) :
    Measurable (fun q : GraphCode ×
        (ℝ × (EdgeCode → ℝ)) => innerMean q.1 e n q.2.1 q.2.2) := by
  exact CanonicalDrift.measurable_outerLimit (fun m => measurable_finiteBallMean e n m)

theorem measurable_drift (e : EdgeCode) :
    Measurable (fun q : GraphCode ×
        (ℝ × (EdgeCode → ℝ)) => drift q.1 q.2.1 q.2.2 e) := by
  exact CanonicalDrift.measurable_outerLimit (fun n => measurable_innerMean e n)

end Problem336.GraphTreePosterior

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

theorem weight_image (T : Finset (ℕ × ℕ)) (φ : (ℕ × ℕ) → (ℕ × ℕ))
    (a b : Field) (hinj : Set.InjOn φ (T : Set (ℕ × ℕ)))
    (hfield : ∀ p ∈ T, b (φ p) = a p) :
    weight b (T.image φ) = weight a T := by
  classical
  unfold weight
  congr 1
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl hfield
  · intro p hp q hq hpq
    exact hinj hp hq hpq

end Problem336.WeightedTree

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_WeightedTreeTransport
attribute [-instance] _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem336.WeightedTree

theorem partition_eq_sum_trees (K : FiniteSubgraphCode) (h : Field) :
    partition K h = ∑ T : USTResponse.TreeSample K, weight h T.1 := by
  classical
  exact Finset.sum_subtype (spanningTrees K) (fun _ => Iff.rfl) (fun T => weight h T)

theorem numerator_eq_sum_trees (K : FiniteSubgraphCode) (e : ℕ × ℕ) (h : Field) :
    numerator K e h = ∑ T : USTResponse.TreeSample K,
      if e ∈ T.1 then weight h T.1 else 0 := by
  classical
  unfold numerator
  rw [Finset.sum_filter]
  exact Finset.sum_subtype (spanningTrees K) (fun _ => Iff.rfl)
    (fun T => if e ∈ T then weight h T else 0)

theorem inclusion_eq_of_tree_equiv (K K' : FiniteSubgraphCode)
    (τ : USTResponse.TreeSample K ≃ USTResponse.TreeSample K')
    (a b : Field) (e e' : ℕ × ℕ)
    (hw : ∀ T, weight b (τ T).1 = weight a T.1)
    (he : ∀ T, e' ∈ (τ T).1 ↔ e ∈ T.1) :
    inclusion K' e' b = inclusion K e a := by
  classical
  unfold inclusion
  rw [partition_eq_sum_trees, partition_eq_sum_trees,
    numerator_eq_sum_trees, numerator_eq_sum_trees]
  rw [← τ.sum_comp (fun T => weight b T.1)]
  rw [← τ.sum_comp (fun T => if e' ∈ T.1 then weight b T.1 else 0)]
  simp_rw [hw, he]

end Problem336.WeightedTree

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteUSTRelabel
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal

namespace Problem336

theorem mem_relabelEdgeSet_iff (σ : Equiv ℕ ℕ) (T : Finset (ℕ × ℕ))
    (hT : ∀ p ∈ T, p.1 < p.2) (e : EdgeCode) :
    (mapEdge σ e).val ∈ relabelEdgeSet σ T ↔ e.val ∈ T := by
  simpa only [TreeAdj, mapEdge, mkEdge_val, rawPair_of_lt e.property] using
    treeAdj_relabelEdgeSet σ T hT e.val.1 e.val.2

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_IntrinsicRelabel
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336

theorem relabelFiniteSubgraph_inducedCode (σ : Equiv ℕ ℕ) (G : GraphCode)
    (S : Finset ℕ) :
    relabelFiniteSubgraph σ (inducedCode G S) =
      inducedCode (relabelGraph σ G) (S.image σ) := by
  apply Prod.ext
  · rfl
  · ext p
    change p ∈ ((inducedCode G S).2.image (relabelPair σ)) ↔
      p ∈ (inducedCode (relabelGraph σ G) (S.image σ)).2
    constructor
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
      rcases (mem_inducedCode_edges G S q).mp hq with ⟨hu, hv, _, ha⟩
      apply (rawPair_mem_inducedCode_edges (relabelGraph σ G) (S.image σ) _ _).mpr
      exact ⟨Finset.mem_image_of_mem σ hu, Finset.mem_image_of_mem σ hv,
        by simpa [Adj, relabelGraph] using ha⟩
    · intro hp
      rcases (mem_inducedCode_edges (relabelGraph σ G) (S.image σ) p).mp hp with
        ⟨hu, hv, hlt, ha⟩
      have hu' : σ.symm p.1 ∈ S := by
        rcases Finset.mem_image.mp hu with ⟨u, hu, he⟩
        rw [← he]
        simpa using hu
      have hv' : σ.symm p.2 ∈ S := by
        rcases Finset.mem_image.mp hv with ⟨v, hv, he⟩
        rw [← he]
        simpa using hv
      refine Finset.mem_image.mpr ⟨rawPair (σ.symm p.1) (σ.symm p.2), ?_, ?_⟩
      · apply (rawPair_mem_inducedCode_edges G S _ _).mpr
        exact ⟨hu', hv', by simpa [Adj, relabelGraph] using ha⟩
      · simp only [relabelPair_rawPair, Equiv.apply_symm_apply, rawPair_of_lt hlt]

namespace Intrinsic

theorem exhaustion_relabel (σ : Equiv ℕ ℕ) (G : GraphCode) (e : EdgeCode) (n : ℕ) :
    exhaustion (relabelGraph σ G) (mapEdge σ e) n =
      relabelFiniteSubgraph σ (exhaustion G e n) := by
  unfold exhaustion
  rw [edgeBallCode_relabel, relabelFiniteSubgraph_inducedCode]

end Intrinsic

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_WeightedTreeEquiv
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336.WeightedTree

theorem finiteField_relabel_mapEdge (σ : Equiv ℕ ℕ) (S : Finset (ℕ × ℕ))
    (hS : ∀ p ∈ S, p.1 < p.2) (t : ℝ) (h : Field) (e : EdgeCode) :
    finiteField (relabelEdgeSet σ S) t (relabelField σ h) (mapEdge σ e).1 =
      finiteField S t h e.1 := by
  simp only [finiteField, mem_relabelEdgeSet_iff σ S hS e, relabelField_mapEdge]

theorem finiteTilt_relabel (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode)
    (hK : ∀ p ∈ K.2, p.1 < p.2) (S : Finset (ℕ × ℕ))
    (hS : ∀ p ∈ S, p.1 < p.2) (t : ℝ) (h : Field) (e : EdgeCode) :
    inclusion (relabelFiniteSubgraph σ K) (mapEdge σ e).1
        (finiteField (relabelEdgeSet σ S) t (relabelField σ h)) =
      inclusion K e.1 (finiteField S t h) := by
  apply inclusion_eq_of_tree_equiv K _ (treeRelabelEquiv σ K hK)
    (finiteField S t h) _ e.1 (mapEdge σ e).1
  · intro T
    apply weight_image
    · intro p hp q hq hpq
      exact relabelPair_injOn σ (tree_canonical hK T p hp)
        (tree_canonical hK T q hq) hpq
    · intro p hp
      simpa only [← relabelPair_edge] using
        finiteField_relabel_mapEdge σ S hS t h ⟨p, tree_canonical hK T p hp⟩
  · intro T
    exact mem_relabelEdgeSet_iff σ T.1 (tree_canonical hK T) e

theorem inclusion_congr_on_edges (K : FiniteSubgraphCode) (a b : Field)
    (e : ℕ × ℕ) (h : ∀ p ∈ K.2, a p = b p) :
    inclusion K e a = inclusion K e b := by
  symm
  apply inclusion_eq_of_tree_equiv K K (Equiv.refl _) a b e e
  · intro T
    unfold weight
    congr 1
    exact Finset.sum_congr rfl (fun p hp =>
      (h p ((USTResponse.tree_property K T).1 hp)).symm)
  · intro T
    rfl

theorem extendField_relabel_canonical (σ : Equiv ℕ ℕ) (y : EdgeCode → ℝ)
    (p : ℕ × ℕ) (hp : p.1 < p.2) :
    extendField (fun e => y (mapEdge σ.symm e)) p =
      relabelField σ (extendField y) p := by
  let e : EdgeCode := ⟨p, hp⟩
  change extendField (fun e => y (mapEdge σ.symm e)) e.1 =
    extendField y (relabelPair σ.symm e.1)
  rw [relabelPair_edge, extendField_apply, extendField_apply]

theorem finiteTilt_edgeField_relabel (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode)
    (hK : ∀ p ∈ K.2, p.1 < p.2) (S : Finset (ℕ × ℕ))
    (hS : ∀ p ∈ S, p.1 < p.2) (t : ℝ) (y : EdgeCode → ℝ) (e : EdgeCode) :
    inclusion (relabelFiniteSubgraph σ K) (mapEdge σ e).1
        (finiteField (relabelEdgeSet σ S) t
          (extendField (fun f => y (mapEdge σ.symm f)))) =
      inclusion K e.1 (finiteField S t (extendField y)) := by
  rw [← finiteTilt_relabel σ K hK S hS t (extendField y) e]
  apply inclusion_congr_on_edges
  intro p hp
  have hp' : p.1 < p.2 := relabelEdgeSet_valid σ K.2 hK p hp
  simp only [finiteField, extendField_relabel_canonical σ y p hp']

end Problem336.WeightedTree

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GraphTreePosteriorEquiv
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem336.GraphTreePosterior

theorem energy_eq_pairField (T : Finset (ℕ × ℕ)) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) :
    energy T S t y = ∑ p ∈ T,
      WeightedTree.finiteField (S.image Subtype.val) t (WeightedTree.extendField y) p := by
  classical
  have hs : (∑ p ∈ S.image Subtype.val,
      if p ∈ T then WeightedTree.extendField y p - t / 2 else 0) =
      energy T S t y := by
    rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
    simp only [WeightedTree.extendField_apply, energy]
  unfold WeightedTree.finiteField
  rw [Finset.sum_ite_mem] at hs ⊢
  rw [Finset.inter_comm] at hs
  exact hs.symm

theorem mean_eq_weightedTree (K : FiniteSubgraphCode) (e : EdgeCode)
    (S : Finset EdgeCode) (t : ℝ) (y : EdgeCode → ℝ) :
    mean K e S t y = WeightedTree.inclusion K e.1
      (WeightedTree.finiteField (S.image Subtype.val) t (WeightedTree.extendField y)) := by
  have hw (T : Finset (ℕ × ℕ)) : weight T S t y =
      WeightedTree.weight
        (WeightedTree.finiteField (S.image Subtype.val) t (WeightedTree.extendField y)) T := by
    unfold weight WeightedTree.weight
    rw [energy_eq_pairField]
  simp only [mean, numerator, partition, WeightedTree.inclusion,
    WeightedTree.numerator, WeightedTree.partition, hw]

private theorem observed_pairs_relabel (σ : Equiv ℕ ℕ) (S : Finset EdgeCode) :
    (S.image (mapEdge σ)).image Subtype.val =
      relabelEdgeSet σ (S.image Subtype.val) := by
  classical
  simp only [relabelEdgeSet, Finset.image_image]
  apply Finset.image_congr
  intro e _
  exact (relabelPair_edge σ e).symm

theorem mean_relabel (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode)
    (hK : ∀ p ∈ K.2, p.1 < p.2) (e : EdgeCode) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) :
    mean (relabelFiniteSubgraph σ K) (mapEdge σ e) (S.image (mapEdge σ)) t
      (fun f => y (mapEdge σ.symm f)) = mean K e S t y := by
  classical
  rw [mean_eq_weightedTree, mean_eq_weightedTree, observed_pairs_relabel]
  apply WeightedTree.finiteTilt_edgeField_relabel σ K hK
  intro p hp
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hp
  exact f.2

theorem edgeCodes_relabel (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode)
    (hK : ∀ p ∈ K.2, p.1 < p.2) :
    edgeCodes (relabelFiniteSubgraph σ K) = (edgeCodes K).image (mapEdge σ) := by
  classical
  ext f
  obtain ⟨e, rfl⟩ := mapEdge_surjective σ f
  rw [mem_edgeCodes]
  change (mapEdge σ e).1 ∈ relabelEdgeSet σ K.2 ↔ _
  rw [mem_relabelEdgeSet_iff σ K.2 hK e]
  constructor
  · intro he
    exact Finset.mem_image.mpr ⟨e, (mem_edgeCodes K e).mpr he, rfl⟩
  · intro he
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
    have hfe' := mapEdge_injective σ hfe
    subst f
    exact (mem_edgeCodes K e).mp hf

theorem finiteBallMean_relabel (σ : Equiv ℕ ℕ) (G : GraphCode)
    (e : EdgeCode) (n m : ℕ) (t : ℝ) (y : EdgeCode → ℝ) :
    finiteBallMean (relabelGraph σ G) (mapEdge σ e) n m t
      (fun f => y (mapEdge σ.symm f)) = finiteBallMean G e n m t y := by
  have hK (k : ℕ) : ∀ p ∈ (Intrinsic.exhaustion G e k).2, p.1 < p.2 := by
    intro p hp
    exact ((mem_inducedCode_edges G (edgeBallCode G k e) p).mp hp).2.2.1
  simp only [finiteBallMean, Intrinsic.exhaustion_relabel,
    edgeCodes_relabel σ _ (hK n)]
  exact mean_relabel σ _ (hK m) e _ t y

theorem innerMean_relabel (σ : Equiv ℕ ℕ) (G : GraphCode)
    (e : EdgeCode) (n : ℕ) (t : ℝ) (y : EdgeCode → ℝ) :
    innerMean (relabelGraph σ G) (mapEdge σ e) n t
      (fun f => y (mapEdge σ.symm f)) = innerMean G e n t y := by
  simp only [innerMean, CanonicalDrift.outerLimit, finiteBallMean_relabel]

theorem drift_relabel (σ : Equiv ℕ ℕ) (G : GraphCode)
    (t : ℝ) (y : EdgeCode → ℝ) (e : EdgeCode) :
    drift (relabelGraph σ G) t (fun f => y (mapEdge σ.symm f)) (mapEdge σ e) =
      drift G t y e := by
  simp only [drift, CanonicalDrift.outerLimit, innerMean_relabel]

end Problem336.GraphTreePosterior

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FinalFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem336.FinalFactor

theorem rule_borel : RuleBorel rule :=
  FactorAssembly.rule_borel GraphTreePosterior.measurable_drift
    AllPairWiener.noise_borel

theorem rule_equivariant : RuleEquivariant rule :=
  FactorAssembly.rule_equivariant GraphTreePosterior.drift_relabel
    AllPairWiener.noise_equivariant

theorem exists_factor :
    ∃ Phi : FactorRule, RuleBorel Phi ∧ RuleEquivariant Phi ∧
      ∀ G : GraphCode, WorksOnGraph Phi G :=
  ⟨rule, rule_borel, rule_equivariant, worksOnGraph⟩

end Problem336.FinalFactor

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_Relabeling
attribute [-instance] _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336

@[simp] theorem relabelGraph_refl (G : GraphCode) :
    relabelGraph (Equiv.refl ℕ) G = G := by
  apply Subtype.ext
  rfl

@[simp] theorem relabelLabels_refl (U : ℕ → ℝ) :
    relabelLabels (Equiv.refl ℕ) U = U := rfl

@[simp] theorem relabelGraph_trans (σ τ : Equiv ℕ ℕ) (G : GraphCode) :
    relabelGraph (σ.trans τ) G = relabelGraph τ (relabelGraph σ G) := by
  apply Subtype.ext
  rfl

@[simp] theorem relabelLabels_trans (σ τ : Equiv ℕ ℕ) (U : ℕ → ℝ) :
    relabelLabels (σ.trans τ) U = relabelLabels τ (relabelLabels σ U) := rfl

@[simp] theorem relabelGraph_symm (σ : Equiv ℕ ℕ) (G : GraphCode) :
    relabelGraph σ.symm (relabelGraph σ G) = G := by
  apply Subtype.ext
  funext u v
  simp [relabelGraph]

@[simp] theorem relabelLabels_symm (σ : Equiv ℕ ℕ) (U : ℕ → ℝ) :
    relabelLabels σ.symm (relabelLabels σ U) = U := by
  funext u
  simp [relabelLabels]

@[simp] theorem adj_relabelGraph (σ : Equiv ℕ ℕ) (G : GraphCode) (u v : ℕ) :
    Adj (relabelGraph σ G) u v ↔ Adj G (σ.symm u) (σ.symm v) := Iff.rfl

@[simp] theorem adj_relabelGraph_apply (σ : Equiv ℕ ℕ) (G : GraphCode) (u v : ℕ) :
    Adj (relabelGraph σ G) (σ u) (σ v) ↔ Adj G u v := by
  simp

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_Factor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Problem336

theorem fusf_is_factor_iid_oai :
    ∃ Phi : FactorRule, RuleBorel Phi ∧ RuleEquivariant Phi ∧ ∀ G : GraphCode, WorksOnGraph Phi G := by
  exact FinalFactor.exists_factor

end Problem336

end

end OAI
end

theorem solution : type_of% @OAI.Problem336.fusf_is_factor_iid_oai := @OAI.Problem336.fusf_is_factor_iid_oai
