-- Prove2me | solution 1 for OAI.Problem336.FinalFactor.worksOnGraph
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:39:33.341664+00:00
-- url     : https://prove2.me/submissions/be891e2a-ab7f-4bc1-8b63-07c1f741abf0

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
import Theorems.Thm_OAI_Problem336_CanonicalBrownianSampler_raw_innovation_hasLaw
import Theorems.Thm_OAI_Problem336_HasFUSFLaw_finiteResponseBound
import Theorems.Thm_OAI_Problem336_exists_hasFUSFLaw

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

lemma rawPair_source_target (key : ℕ → ℝ) (e : EdgeCode) :
    rawPair (source key e) (target key e) = e.1 := by
  unfold source target
  split_ifs with h
  · simp [rawPair, e.2]
  · simp [rawPair, Nat.not_lt.mpr (Nat.le_of_lt e.2)]

end EdgeAllocation
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

theorem exists_withinRadius_of_reachable {G : GraphCode} {u v : ℕ}
    (h : Relation.ReflTransGen (Adj G) u v) :
    ∃ n, withinRadius G n u v := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail huv hvw ih =>
      rcases ih with ⟨n, hn⟩
      exact ⟨n + 1, Or.inr ⟨_, hn, hvw⟩⟩

theorem exists_withinRadius (G : GraphCode) (hG : GraphConnected G) (u v : ℕ) :
    ∃ n, withinRadius G n u v :=
  exists_withinRadius_of_reachable (hG u v)

theorem finite_withinRadius (G : GraphCode) (hG : GraphLocallyFinite G)
    (n u : ℕ) : Set.Finite {v | withinRadius G n u v} := by
  induction n with
  | zero => simp [withinRadius]
  | succ n ih =>
      have hf := ih.biUnion (fun w _ => hG w)
      convert ih.union hf using 1
      ext v
      simp [withinRadius]

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

theorem finite_edgeBall (G : GraphCode) (hG : GraphLocallyFinite G)
    (n : ℕ) (e : EdgeCode) : (edgeBall G n e).Finite :=
  (finite_withinRadius G hG n e.val.1).union
    (finite_withinRadius G hG n e.val.2)

theorem measurableSet_mem_edgeBall (n v : ℕ) (e : EdgeCode) :
    MeasurableSet {G : GraphCode | v ∈ edgeBall G n e} :=
  (measurableSet_withinRadius n e.val.1 v).union
    (measurableSet_withinRadius n e.val.2 v)

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

@[simp] theorem mem_edgeBallCode (G : GraphCode) (hG : GraphLocallyFinite G)
    (n v : ℕ) (e : EdgeCode) : v ∈ edgeBallCode G n e ↔ v ∈ edgeBall G n e := by
  simp [edgeBallCode, finiteSetCode, finite_edgeBall G hG n e]

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

theorem withinRadius_radius (G : GraphCode) (hc : GraphConnected G) (u v : ℕ) :
    withinRadius G (radius G u v) u v := by
  classical
  have h := Nat.find_spec (exists_radiusPredicate G u v)
  exact h.resolve_right (not_not.mpr (exists_withinRadius G hc u v))

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

theorem ballRank_strictMono {G : GraphCode} (hf : GraphLocallyFinite G)
    {key : ℕ → ℝ} {n u v w : ℕ} (hv : withinRadius G n u v)
    (hvw : key v < key w) : ballRank G key n u v < ballRank G key n u w := by
  apply Set.ncard_lt_ncard
  · refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro x hx
      exact ⟨hx.1, hx.2.trans hvw⟩
    · intro heq
      have hmem : v ∈ {x | withinRadius G n u x ∧ key x < key w} := ⟨hv, hvw⟩
      rw [← heq] at hmem
      exact (lt_irrefl (key v)) hmem.2
  · exact (finite_withinRadius G hf n u).subset (fun _ h => h.1)

theorem ballRank_injOn {G : GraphCode} (hf : GraphLocallyFinite G)
    {key : ℕ → ℝ} (hk : Function.Injective key) (n u : ℕ) :
    Set.InjOn (ballRank G key n u) {v | withinRadius G n u v} := by
  intro v hv w hw hrank
  apply hk
  rcases lt_trichotomy (key v) (key w) with h | h | h
  · exact False.elim ((ne_of_lt (ballRank_strictMono hf hv h)) hrank)
  · exact h
  · exact False.elim ((ne_of_lt (ballRank_strictMono hf hw h)) hrank.symm)

theorem coordinate_injective {G : GraphCode} (hc : GraphConnected G)
    (hf : GraphLocallyFinite G) {key : ℕ → ℝ} (hk : Function.Injective key) :
    Function.Injective (coordinate G key) := by
  intro e f h
  have hu : EdgeAllocation.source key e = EdgeAllocation.source key f := congrArg Prod.fst h
  have hn : radius G (EdgeAllocation.source key e) (EdgeAllocation.target key e) =
      radius G (EdgeAllocation.source key f) (EdgeAllocation.target key f) :=
    congrArg (fun x => x.2.1) h
  have hr : ballRank G key
      (radius G (EdgeAllocation.source key e) (EdgeAllocation.target key e))
      (EdgeAllocation.source key e) (EdgeAllocation.target key e) =
    ballRank G key
      (radius G (EdgeAllocation.source key f) (EdgeAllocation.target key f))
      (EdgeAllocation.source key f) (EdgeAllocation.target key f) :=
    congrArg (fun x => x.2.2) h
  rw [← hn, ← hu] at hr
  have hvf : withinRadius G
      (radius G (EdgeAllocation.source key e) (EdgeAllocation.target key e))
      (EdgeAllocation.source key e) (EdgeAllocation.target key f) := by
    rw [hn, hu]
    exact withinRadius_radius G hc _ _
  have hv := ballRank_injOn hf hk _ _ (withinRadius_radius G hc _ _) hvf hr
  apply Subtype.ext
  rw [← EdgeAllocation.rawPair_source_target key e,
    ← EdgeAllocation.rawPair_source_target key f, hu, hv]

theorem coordinateNat_injective {G : GraphCode} (hc : GraphConnected G)
    (hf : GraphLocallyFinite G) {key : ℕ → ℝ} (hk : Function.Injective key) :
    Function.Injective (coordinateNat G key) := by
  intro e f h
  apply coordinate_injective hc hf hk
  simp only [coordinateNat, Prod.mk.injEq, Nat.pair_eq_pair] at h
  exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)

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
-- module Solutions.OAIS_P336.SpanningForest_LabelNoCollision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem336.LabelNoCollision

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Ω → ℝ}

theorem marginal (h : IsVertexIID P U) (i : ℕ) {s : Set ℝ}
    (hs : MeasurableSet s) : P (U i ⁻¹' s) = uniform01 s := by
  change P {ω | U i ω ∈ s} = uniform01 s
  simpa using h.2 {i} (fun _ => s) (by simpa using hs)

theorem map_marginal (h : IsVertexIID P U) (i : ℕ) : P.map (U i) = uniform01 := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (h.1 i) hs]
  exact marginal h i hs

theorem independent (h : IsVertexIID P U) : iIndepFun U P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s sets hs
  calc
    P (⋂ i ∈ s, U i ⁻¹' sets i) = P {ω | ∀ i ∈ s, U i ω ∈ sets i} := by
      congr 1
      ext ω
      simp
    _ = ∏ i ∈ s, uniform01 (sets i) := h.2 s sets hs
    _ = ∏ i ∈ s, P (U i ⁻¹' sets i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (marginal h i (hs i hi)).symm

end Problem336.LabelNoCollision

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_UniformSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped unitInterval

namespace Problem336

local instance instIsProbabilityMeasureRealUniform01 : IsProbabilityMeasure uniform01 := sampler_uniform01_probability

theorem privatePoolLaw_probability : IsProbabilityMeasure privatePoolLaw := by
  unfold privatePoolLaw
  infer_instance

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CanonicalIID
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace Problem336.CanonicalIID

private theorem uniform_probability : IsProbabilityMeasure uniform01 := by
  rw [uniform01_eq_map_unitInterval]
  exact Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

local instance instIsProbabilityMeasureRealUniform01 : IsProbabilityMeasure uniform01 := uniform_probability

theorem map_labels {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {U : ℕ → Ω → ℝ} (h : IsVertexIID P U) :
    P.map (fun ω i => U i ω) = privatePoolLaw := by
  rw [iIndepFun.map_fun_eq_infinitePi_map h.1 (LabelNoCollision.independent h)]
  simp only [LabelNoCollision.map_marginal h]
  rfl

theorem canonical_isVertexIID :
    IsVertexIID privatePoolLaw (fun i U => U i) := by
  constructor
  · intro i
    exact measurable_pi_apply i
  · intro s A hA
    have hInd : iIndepFun (fun (i : ℕ) (U : ℕ → ℝ) => U i) privatePoolLaw :=
      iIndepFun_infinitePi (P := fun _ : ℕ => uniform01) (X := fun _ x => x)
        (fun _ => measurable_id)
    calc
      privatePoolLaw {U | ∀ i ∈ s, U i ∈ A i} =
          privatePoolLaw (⋂ i ∈ s, (fun U : ℕ → ℝ => U i) ⁻¹' A i) := by
        congr 1
        ext U
        simp
      _ = ∏ i ∈ s, privatePoolLaw ((fun U : ℕ → ℝ => U i) ⁻¹' A i) :=
        hInd.measure_inter_preimage_eq_mul s hA
      _ = ∏ i ∈ s, uniform01 (A i) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hm : privatePoolLaw.map (fun U : ℕ → ℝ => U i) = uniform01 :=
          Measure.infinitePi_map_eval (fun _ : ℕ => uniform01) i
        have heq := congrArg (fun μ : Measure ℝ => μ (A i)) hm
        rwa [Measure.map_apply (measurable_pi_apply i) (hA i hi)] at heq

theorem transfer_hasFUSFLaw {Ω : Type} [MeasurableSpace Ω]
    {G : GraphCode} {P : Measure Ω} {U : ℕ → Ω → ℝ}
    {X : (ℕ → ℝ) → EdgeConfiguration} (hU : IsVertexIID P U)
    (hX : HasFUSFLaw G privatePoolLaw X) :
    HasFUSFLaw G P (fun ω => X (fun i => U i ω)) := by
  have hlabels : Measurable (fun ω i => U i ω) := Measurable.of_eval hU.1
  constructor
  · intro e
    exact (hX.1 e).comp hlabels
  · intro H hH A B
    have hE : MeasurableSet {l : ℕ → ℝ |
        (∀ e ∈ A, X l e = true) ∧ (∀ e ∈ B, X l e = false)} := by
      exact ((Measurable.forall (fun e => measurable_const.imp ((hX.1 e).eq_const true))).and
        (Measurable.forall (fun e => measurable_const.imp ((hX.1 e).eq_const false)))).setOf
    have heq := congrArg (fun μ : Measure (ℕ → ℝ) => μ {l |
      (∀ e ∈ A, X l e = true) ∧ (∀ e ∈ B, X l e = false)}) (map_labels hU)
    rw [Measure.map_apply hlabels hE] at heq
    exact heq ▸ hX.2 H hH A B

theorem worksOnGraph_iff_canonical (Phi : FactorRule) (G : GraphCode) :
    WorksOnGraph Phi G ↔
      (GraphConnected G → GraphLocallyFinite G → HasFUSFLaw G privatePoolLaw (Phi G)) := by
  constructor
  · intro h hconn hfin
    exact h hconn hfin (ℕ → ℝ) privatePoolLaw (fun i U => U i) canonical_isVertexIID
  · intro h hconn hfin Ω _ P U hU
    exact transfer_hasFUSFLaw hU (h hconn hfin)

end Problem336.CanonicalIID

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_RandomReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem336.RandomReindex

theorem map_prod_fiberwise
    {K V W : Type*} [MeasurableSpace K] [MeasurableSpace V] [MeasurableSpace W]
    (κ : Measure K) (ν : Measure V) (η : Measure W)
    [SFinite ν] [SFinite η]
    (f : K → V → W)
    (hf : Measurable (fun p : K × V => f p.1 p.2))
    (hmap : ∀ᵐ k ∂κ, ν.map (f k) = η) :
    (κ.prod ν).map (fun p : K × V => (p.1, f p.1 p.2)) = κ.prod η := by
  have hpair : Measurable (fun p : K × V => (p.1, f p.1 p.2)) :=
    measurable_fst.prodMk hf
  ext s hs
  rw [Measure.map_apply hpair hs, Measure.prod_apply (hs.preimage hpair),
    Measure.prod_apply hs]
  apply lintegral_congr_ae
  filter_upwards [hmap] with k hk
  change ν ((f k) ⁻¹' (Prod.mk k ⁻¹' s)) = η (Prod.mk k ⁻¹' s)
  have hfk : Measurable (f k) := hf.comp measurable_prodMk_left
  rw [← hk, Measure.map_apply hfk (hs.preimage measurable_prodMk_left)]

theorem measurable_random_eval
    {K J V : Type*} [MeasurableSpace K] [MeasurableSpace J]
    [Countable J] [MeasurableSingletonClass J] [MeasurableSpace V]
    (a : K → J) (ha : Measurable a) :
    Measurable (fun p : K × (J → V) => p.2 (a p.1)) := by
  have hev : Measurable (fun p : J × (J → V) => p.2 p.1) :=
    measurable_from_prod_countable_right (fun j => measurable_pi_apply j)
  exact hev.comp ((ha.comp measurable_fst).prodMk measurable_snd)

theorem measurable_select
    {K I J V : Type*} [MeasurableSpace K] [MeasurableSpace J]
    [Countable J] [MeasurableSingletonClass J] [MeasurableSpace V]
    (a : K → I → J) (ha : ∀ i, Measurable (fun k => a k i)) :
    Measurable (fun p : K × (J → V) => fun i => p.2 (a p.1 i)) := by
  exact Measurable.of_eval (fun i => measurable_random_eval (fun k => a k i) (ha i))

theorem map_random_injective_reindex
    {K I J V : Type*} [MeasurableSpace K] [MeasurableSpace J]
    [Countable J] [MeasurableSingletonClass J] [MeasurableSpace V]
    (κ : Measure K) (ν : Measure V) [IsProbabilityMeasure ν]
    (a : K → I → J) (ha : ∀ i, Measurable (fun k => a k i))
    (hinj : ∀ᵐ k ∂κ, Function.Injective (a k)) :
    (κ.prod (Measure.infinitePi (fun _ : J => ν))).map
        (fun p : K × (J → V) => (p.1, fun i => p.2 (a p.1 i))) =
      κ.prod (Measure.infinitePi (fun _ : I => ν)) := by
  apply map_prod_fiberwise κ (Measure.infinitePi (fun _ : J => ν))
    (Measure.infinitePi (fun _ : I => ν))
    (fun k v i => v (a k i)) (measurable_select a ha)
  filter_upwards [hinj] with k hk
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : J => ν) hk

theorem map_random_injective_reindex_of_joint_law
    {Ω K I J V : Type*} [MeasurableSpace Ω] [MeasurableSpace K]
    [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
    [MeasurableSpace V]
    (P : Measure Ω) (κ : Measure K) (ν : Measure V) [IsProbabilityMeasure ν]
    (key : Ω → K) (pool : Ω → J → V)
    (hkey : Measurable key) (hpool : Measurable pool)
    (hlaw : P.map (fun ω => (key ω, pool ω)) =
      κ.prod (Measure.infinitePi (fun _ : J => ν)))
    (a : K → I → J) (ha : ∀ i, Measurable (fun k => a k i))
    (hinj : ∀ᵐ k ∂κ, Function.Injective (a k)) :
    P.map (fun ω => (key ω, fun i => pool ω (a (key ω) i))) =
      κ.prod (Measure.infinitePi (fun _ : I => ν)) := by
  have hm : Measurable (fun p : K × (J → V) =>
      (p.1, fun i => p.2 (a p.1 i))) :=
    measurable_fst.prodMk (measurable_select a ha)
  rw [← map_random_injective_reindex κ ν a ha hinj, ← hlaw,
    Measure.map_map hm (hkey.prodMk hpool)]
  rfl

theorem prod_diagonal_null
    {V : Type*} [MeasurableSpace V] [MeasurableEq V]
    (ν : Measure V) [SFinite ν] [NullSingletonClass ν] :
    (ν.prod ν) (Set.diagonal V) = 0 := by
  rw [Measure.prod_apply measurableSet_diagonal]
  have hsection (v : V) : Prod.mk v ⁻¹' Set.diagonal V = {v} := by
    ext w
    simp [Set.diagonal, eq_comm]
  simp [hsection]

theorem ae_injective_infinitePi
    {J V : Type*} [Countable J] [MeasurableSpace V] [MeasurableEq V]
    (ν : Measure V) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    ∀ᵐ v ∂Measure.infinitePi (fun _ : J => ν), Function.Injective v := by
  have hne (i j : J) (hij : i ≠ j) :
      ∀ᵐ v ∂Measure.infinitePi (fun _ : J => ν), v i ≠ v j := by
    have hd := prod_diagonal_null ν
    rw [← Measure.infinitePi_map_eval_prod (P := fun _ : J => ν) hij,
      Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
        measurableSet_diagonal] at hd
    simpa only [ae_iff, Set.preimage, Set.mem_diagonal_iff, not_not] using hd
  have hall : ∀ i j : J,
      ∀ᵐ v ∂Measure.infinitePi (fun _ : J => ν), i ≠ j → v i ≠ v j := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hij))
    · exact (hne i j hij).mono (fun _ h _ => h)
  filter_upwards [ae_all_iff.2 (fun i => ae_all_iff.2 (hall i))] with v hv
  intro i j heq
  by_contra hij
  exact hv i j hij heq

end Problem336.RandomReindex

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_IIDBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem336.RandomReindex

theorem indepFun_infinitePi_blocks
    {I J L V : Type*} [MeasurableSpace V]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (a : I → J) (b : L → J)
    (hab : Disjoint (Set.range a) (Set.range b)) :
    IndepFun (fun v : J → V => fun i => v (a i))
      (fun v : J → V => fun l => v (b l))
      (Measure.infinitePi (fun _ : J => ν)) := by
  have hi : iIndep (fun j : J =>
      MeasurableSpace.comap (fun v : J → V => v j) inferInstance)
      (Measure.infinitePi (fun _ : J => ν)) :=
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  have hblocks := indep_iSup_of_disjoint
    (fun j : J => (measurable_iff_comap_le.mp (measurable_pi_apply j))) hi hab
  apply indep_of_indep_of_le hblocks
  · rw [MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro i
    exact le_iSup_of_le (a i) (le_iSup_of_le ⟨i, rfl⟩ le_rfl)
  · rw [MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro l
    exact le_iSup_of_le (b l) (le_iSup_of_le ⟨l, rfl⟩ le_rfl)

theorem map_infinitePi_two_blocks
    {I J L V : Type*} [MeasurableSpace V]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (a : I → J) (b : L → J)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : Disjoint (Set.range a) (Set.range b)) :
    (Measure.infinitePi (fun _ : J => ν)).map
        (fun v : J → V => ((fun i => v (a i)), (fun l => v (b l)))) =
      (Measure.infinitePi (fun _ : I => ν)).prod
        (Measure.infinitePi (fun _ : L => ν)) := by
  rw [(indepFun_infinitePi_blocks ν a b hab).map_prod_eq_prod_map_map
    (Measurable.aemeasurable (Measurable.of_eval (fun i => measurable_pi_apply (a i))))
    (Measurable.aemeasurable (Measurable.of_eval (fun l => measurable_pi_apply (b l)))),
    Measure.map_infinitePi_infinitePi_of_inj ha,
    Measure.map_infinitePi_infinitePi_of_inj hb]

end Problem336.RandomReindex

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_EdgeIID
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem336.EdgeIID

local instance instNullSingletonClassRealUniform01 : NullSingletonClass uniform01 := by
  unfold uniform01
  infer_instance

attribute [local instance] OAI.Problem336.EdgeIID.instIsProbabilityMeasureStreamStreamLaw
theorem map_stream : uniform01.map stream = streamLaw :=
  (Classical.choose_spec (exists_uniform01_sampler streamLaw)).2

attribute [local instance] OAI.Problem336.EdgeIID.instIsProbabilityMeasureRealUniform01
theorem map_expanded :
    privatePoolLaw.map expanded =
      Measure.infinitePi (fun _ : ℕ × Option ℕ => uniform01) := by
  have hm : Measurable (fun U : ℕ → ℝ => fun v => stream (U v)) := by fun_prop
  have heq : expanded = (MeasurableEquiv.curry ℕ (Option ℕ) ℝ).symm ∘
      (fun U : ℕ → ℝ => fun v => stream (U v)) := rfl
  rw [heq, ← Measure.map_map (MeasurableEquiv.curry ℕ (Option ℕ) ℝ).symm.measurable hm]
  unfold privatePoolLaw
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_stream)]
  simp only [map_stream, streamLaw]
  exact Measure.infinitePi_map_curry_symm (fun (_ : ℕ) (_ : Option ℕ) => uniform01)

theorem map_keys_pool :
    privatePoolLaw.map (fun U => (keys U, pool U)) =
      privatePoolLaw.prod (Measure.infinitePi (fun _ : ℕ × ℕ => uniform01)) := by
  let a : ℕ → ℕ × Option ℕ := fun v => (v, none)
  let b : ℕ × ℕ → ℕ × Option ℕ := fun p => (p.1, some p.2)
  have ha : Function.Injective a := by
    intro i j h
    exact congrArg Prod.fst h
  have hb : Function.Injective b := by
    intro p q h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext h1 (Option.some.inj h2)
  have hab : Disjoint (Set.range a) (Set.range b) := by
    rw [Set.disjoint_left]
    rintro _ ⟨v, rfl⟩ ⟨p, h⟩
    have hh := congrArg Prod.snd h
    simp [a, b] at hh
  have hm : Measurable (fun z : (ℕ × Option ℕ) → ℝ =>
      ((fun v => z (a v)), (fun p => z (b p)))) := by fun_prop
  have heq : (fun U => (keys U, pool U)) =
      (fun z : (ℕ × Option ℕ) → ℝ =>
        ((fun v => z (a v)), (fun p => z (b p)))) ∘ expanded := rfl
  rw [heq, ← Measure.map_map hm measurable_expanded, map_expanded]
  exact RandomReindex.map_infinitePi_two_blocks uniform01 a b ha hb hab

theorem map_keys : privatePoolLaw.map keys = privatePoolLaw := by
  have h := congrArg (fun μ : Measure ((ℕ → ℝ) × ((ℕ × ℕ) → ℝ)) =>
    μ.map Prod.fst) map_keys_pool
  rw [Measure.map_map measurable_fst (measurable_keys.prodMk measurable_pool),
    Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

theorem ae_injective_keys : ∀ᵐ U ∂privatePoolLaw, Function.Injective (keys U) := by
  apply ae_of_ae_map measurable_keys.aemeasurable
  rw [map_keys]
  exact RandomReindex.ae_injective_infinitePi uniform01

end Problem336.EdgeIID

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

local instance instIsProbabilityMeasureRealUniform01 : IsProbabilityMeasure uniform01 := sampler_uniform01_probability
local instance instIsProbabilityMeasureForallNatRealPrivatePoolLaw : IsProbabilityMeasure privatePoolLaw := privatePoolLaw_probability
local instance instNullSingletonClassRealUniform01 : NullSingletonClass uniform01 := by
  unfold uniform01
  infer_instance

theorem measurable_coordinate_fixed (G : GraphCode) (e : EdgeCode) :
    Measurable (fun key => AllPairAllocation.coordinateNat G key e) :=
  AllPairAllocation.measurable_coordinateNat.comp
    ((measurable_const.prodMk measurable_id).prodMk measurable_const)

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

theorem measurable_raw (G : GraphCode) (e : EdgeCode) :
    Measurable (fun U => raw G U e) :=
  measurable_raw_joint.comp
    ((measurable_const.prodMk measurable_id).prodMk measurable_const)

theorem map_keys_raw (G : GraphCode) (hc : GraphConnected G) (hf : GraphLocallyFinite G) :
    privatePoolLaw.map (fun U => (EdgeIID.keys U, raw G U)) =
      privatePoolLaw.prod (Measure.infinitePi (fun _ : EdgeCode => uniform01)) := by
  apply RandomReindex.map_random_injective_reindex_of_joint_law
    privatePoolLaw privatePoolLaw uniform01 EdgeIID.keys EdgeIID.pool
    EdgeIID.measurable_keys EdgeIID.measurable_pool EdgeIID.map_keys_pool
    (fun key (e : EdgeCode) => AllPairAllocation.coordinateNat G key e)
    (measurable_coordinate_fixed G)
  filter_upwards [RandomReindex.ae_injective_infinitePi (J := ℕ) uniform01] with key hk
  exact AllPairAllocation.coordinateNat_injective hc hf hk

theorem map_raw (G : GraphCode) (hc : GraphConnected G) (hf : GraphLocallyFinite G) :
    privatePoolLaw.map (raw G) = Measure.infinitePi (fun _ : EdgeCode => uniform01) := by
  have h := congrArg (fun μ : Measure ((ℕ → ℝ) × (EdgeCode → ℝ)) => μ.map Prod.snd)
    (map_keys_raw G hc hf)
  rw [Measure.map_map measurable_snd
      (EdgeIID.measurable_keys.prodMk (Measurable.of_eval (measurable_raw G))),
    Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h

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

theorem measurable_uniformRule_fixed (G : GraphCode) (e : EdgeCode) :
    Measurable (fun U => uniformRule G U e) :=
  measurable_uniformRule.comp
    ((measurable_const.prodMk measurable_id).prodMk measurable_const)

theorem map_uniformRule (G : GraphCode) (hc : GraphConnected G) (hf : GraphLocallyFinite G) :
    privatePoolLaw.map (uniformRule G) =
      Measure.infinitePi (fun _ : EdgeCode => uniform01) := by
  rw [← map_raw G hc hf]
  apply Measure.map_congr
  filter_upwards [EdgeIID.ae_injective_keys] with U hU
  funext e
  simp [uniformRule, hU]

theorem uniformRule_law {Ω : Type} [MeasurableSpace Ω]
    (G : GraphCode) (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    (P : Measure Ω) (U : ℕ → Ω → ℝ) (hU : IsVertexIID P U) :
    P.map (fun ω e => uniformRule G (fun v => U v ω) e) =
      Measure.infinitePi (fun _ : EdgeCode => uniform01) := by
  have hm : Measurable (fun ω v => U v ω) := Measurable.of_eval hU.1
  rw [show (fun ω e => uniformRule G (fun v => U v ω) e) =
      uniformRule G ∘ (fun ω v => U v ω) from rfl,
    ← Measure.map_map (Measurable.of_eval (measurable_uniformRule_fixed G)) hm,
    CanonicalIID.map_labels hU]
  exact map_uniformRule G hc hf

theorem sampled_uniformRule_law {Ω Y : Type} [MeasurableSpace Ω]
    [MeasurableSpace Y] (ν : Measure Y)
    (sample : ℝ → Y) (hsample : Measurable sample)
    (hsample_law : uniform01.map sample = ν)
    (G : GraphCode) (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    (P : Measure Ω) (U : ℕ → Ω → ℝ) (hU : IsVertexIID P U) :
    P.map (fun ω e => sample (uniformRule G (fun v => U v ω) e)) =
      Measure.infinitePi (fun _ : EdgeCode => ν) := by
  have hm : Measurable (fun ω e => uniformRule G (fun v => U v ω) e) :=
    (Measurable.of_eval (measurable_uniformRule_fixed G)).comp
      (Measurable.of_eval hU.1)
  have hs : Measurable (fun x : EdgeCode → ℝ => fun e => sample (x e)) :=
    Measurable.of_eval (fun e => hsample.comp (measurable_pi_apply e))
  rw [show (fun ω e => sample (uniformRule G (fun v => U v ω) e)) =
      (fun x : EdgeCode → ℝ => fun e => sample (x e)) ∘
        (fun ω e => uniformRule G (fun v => U v ω) e) from rfl,
    ← Measure.map_map hs hm, uniformRule_law G hc hf P U hU,
    Measure.infinitePi_map_pi]
  · simp only [hsample_law]
  · intro e
    exact hsample

end Problem336.AllPairIID

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
-- module Solutions.OAIS_P336.SpanningForest_AllPairObservation
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem336.AllPairObservation

theorem observations_mono (G : GraphCode) (e : EdgeCode) :
    Monotone (observations G e) := by
  intro n m hnm a ha
  rw [mem_observations] at ha ⊢
  exact ⟨ha.1, IntrinsicExhaustion.edgeBall_mono G e hnm ha.2.1,
    IntrinsicExhaustion.edgeBall_mono G e hnm ha.2.2⟩

theorem exists_mem_observations {G : GraphCode} (hc : GraphConnected G)
    (hf : GraphLocallyFinite G) (e a : EdgeCode) :
    ∃ n, a ∈ observations G e n := by
  obtain ⟨n, hn⟩ := IntrinsicExhaustion.GraphConnected.exists_mem_edgeBall hc e a.1.1
  obtain ⟨m, hm⟩ := IntrinsicExhaustion.GraphConnected.exists_mem_edgeBall hc e a.1.2
  refine ⟨max n m, (mem_observations G e a _).mpr ⟨hf, ?_, ?_⟩⟩
  · exact IntrinsicExhaustion.edgeBall_mono G e (le_max_left n m) hn
  · exact IntrinsicExhaustion.edgeBall_mono G e (le_max_right n m) hm

end Problem336.AllPairObservation

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

theorem withinRadius_iff_vertexBall (G : GraphCode) (n u v : ℕ) :
    withinRadius G n u v ↔ v ∈ IntrinsicExhaustion.vertexBall G u n := by
  induction n generalizing v with
  | zero => simp [withinRadius, IntrinsicExhaustion.vertexBall, eq_comm]
  | succ n ih =>
      simp only [withinRadius, IntrinsicExhaustion.mem_vertexBall_succ, ih]

theorem edgeBall_eq_selected (G : GraphCode) (e : EdgeCode) (n : ℕ) :
    Problem336.edgeBall G n e = IntrinsicExhaustion.edgeBall G e n := by
  ext v
  simp only [Problem336.edgeBall, IntrinsicExhaustion.edgeBall,
    Set.mem_ofPred_eq, Set.mem_union, withinRadius_iff_vertexBall]

theorem measurable_exhaustion :
    Measurable (fun q : GraphCode × (ℕ × EdgeCode) => exhaustion q.1 q.2.2 q.2.1) := by
  exact measurable_inducedCode measurable_fst measurable_edgeBallCode

theorem exhaustion_eq_edgeBallSubgraph (G : GraphCode) (hf : GraphLocallyFinite G)
    (e : EdgeCode) (n : ℕ) :
    exhaustion G e n = IntrinsicExhaustion.edgeBallSubgraph G hf e n := by
  apply Prod.ext
  · ext v
    simp only [exhaustion, inducedCode_vertices, mem_edgeBallCode G hf,
      IntrinsicExhaustion.mem_edgeBallSubgraph_vertices, edgeBall_eq_selected]
  · ext p
    simp only [exhaustion, mem_inducedCode_edges, mem_edgeBallCode G hf,
      IntrinsicExhaustion.mem_edgeBallSubgraph_edges, edgeBall_eq_selected]

theorem isConnectedExhaustion (G : GraphCode) (hc : GraphConnected G)
    (hf : GraphLocallyFinite G) (e : EdgeCode) (he : Adj G e.val.1 e.val.2) :
    IsConnectedExhaustion G (exhaustion G e) := by
  have hfun : exhaustion G e = IntrinsicExhaustion.edgeBallSubgraph G hf e :=
    funext fun n => exhaustion_eq_edgeBallSubgraph G hf e n
  rw [hfun]
  exact IntrinsicExhaustion.isConnectedExhaustion_edgeBallSubgraph hc hf e he

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

theorem mean_of_not_mem {K : FiniteSubgraphCode} {e : EdgeCode}
    (he : e.1 ∉ K.2) (S : Finset EdgeCode) (t : ℝ) (y : EdgeCode → ℝ) :
    mean K e S t y = 0 := by
  classical
  have hempty : (spanningTrees K).filter (fun T => e.1 ∈ T) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro T hT heT
    have hTree : TreeOn K T := (Finset.mem_filter.mp hT).2
    exact he (hTree.1 heT)
  simp [mean, numerator, hempty]

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
-- module Solutions.OAIS_P336.SpanningForest_AllPairIntrinsicBridge
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336.AllPairObservation

attribute [local instance] Classical.propDecidable

theorem mem_edgeCodes_exhaustion_iff {G : GraphCode}
    (hf : GraphLocallyFinite G) (e a : EdgeCode) (n : ℕ) :
    a ∈ GraphTreePosterior.edgeCodes (Intrinsic.exhaustion G e n) ↔
      a ∈ observations G e n ∧ Adj G a.1.1 a.1.2 := by
  rw [GraphTreePosterior.mem_edgeCodes,
    Intrinsic.exhaustion_eq_edgeBallSubgraph G hf,
    IntrinsicExhaustion.mem_edgeBallSubgraph_edges, mem_observations]
  simp only [hf, true_and, a.2]
  tauto

theorem edgeCodes_exhaustion_subset_observations {G : GraphCode}
    (hf : GraphLocallyFinite G) (e : EdgeCode) (n : ℕ) :
    GraphTreePosterior.edgeCodes (Intrinsic.exhaustion G e n) ⊆
      observations G e n := by
  intro a ha
  exact ((mem_edgeCodes_exhaustion_iff hf e a n).mp ha).1

theorem not_adj_of_mem_observations_not_mem_edgeCodes {G : GraphCode}
    (hf : GraphLocallyFinite G) (e a : EdgeCode) (n : ℕ)
    (ha : a ∈ observations G e n)
    (hnot : a ∉ GraphTreePosterior.edgeCodes (Intrinsic.exhaustion G e n)) :
    ¬ Adj G a.1.1 a.1.2 := by
  intro hadj
  exact hnot ((mem_edgeCodes_exhaustion_iff hf e a n).mpr ⟨ha, hadj⟩)

end Problem336.AllPairObservation

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
-- module Solutions.OAIS_P336.SpanningForest_FUSFLawSupport
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Problem336

theorem ustCylinder_eq_zero_of_present_not_mem
    (K : FiniteSubgraphCode) (A B : Finset EdgeCode) (e : EdgeCode)
    (he : e ∈ A) (hne : e.1 ∉ K.2) :
    ustCylinder K A B = 0 := by
  classical
  unfold ustCylinder
  apply ENNReal.div_eq_zero_iff.mpr
  left
  rw [Nat.cast_eq_zero, Finset.card_eq_zero]
  apply Finset.ext
  intro T
  simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
  rintro ⟨hT, hgood⟩
  have ht : T ⊆ K.2 ∧ TreeOn K T := by
    simpa only [spanningTrees, Finset.mem_filter, Finset.mem_powerset] using hT
  exact hne (ht.2.1 (hgood.1 e he))

theorem ustCylinder_eq_zero_of_nonedge
    {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K)
    (A B : Finset EdgeCode) (e : EdgeCode) (he : e ∈ A)
    (hne : ¬ Adj G e.1.1 e.1.2) :
    ustCylinder K A B = 0 := by
  apply ustCylinder_eq_zero_of_present_not_mem K A B e he
  intro hmem
  exact hne (hK.2.1 e.1 hmem).2.2.2

theorem HasFUSFLaw.measure_cylinder_eq_zero_of_nonedge
    {Ω : Type} [MeasurableSpace Ω] {G : GraphCode}
    {P : Measure Ω} {X : Ω → EdgeConfiguration}
    (hX : HasFUSFLaw G P X)
    (H : ℕ → FiniteSubgraphCode) (hH : IsConnectedExhaustion G H)
    (A B : Finset EdgeCode) (e : EdgeCode) (he : e ∈ A)
    (hne : ¬ Adj G e.1.1 e.1.2) :
    P {ω | (∀ f ∈ A, X ω f = true) ∧ (∀ f ∈ B, X ω f = false)} = 0 := by
  have hconv := hX.2 H hH A B
  have hzero : (fun n => ustCylinder (H n) A B) = fun _ => 0 := by
    funext n
    exact ustCylinder_eq_zero_of_nonedge (hH.1 n) A B e he hne
  rw [hzero] at hconv
  exact tendsto_nhds_unique hconv tendsto_const_nhds

theorem HasFUSFLaw.measure_present_eq_zero_of_nonedge
    {Ω : Type} [MeasurableSpace Ω] {G : GraphCode}
    {P : Measure Ω} {X : Ω → EdgeConfiguration}
    (hX : HasFUSFLaw G P X)
    (H : ℕ → FiniteSubgraphCode) (hH : IsConnectedExhaustion G H)
    (e : EdgeCode) (hne : ¬ Adj G e.1.1 e.1.2) :
    P {ω | X ω e = true} = 0 := by
  simpa using hX.measure_cylinder_eq_zero_of_nonedge H hH {e} ∅ e
    (Finset.mem_singleton_self e) hne

theorem HasFUSFLaw.ae_false_of_nonedge
    {Ω : Type} [MeasurableSpace Ω] {G : GraphCode}
    {P : Measure Ω} {X : Ω → EdgeConfiguration}
    (hX : HasFUSFLaw G P X)
    (H : ℕ → FiniteSubgraphCode) (hH : IsConnectedExhaustion G H)
    (e : EdgeCode) (hne : ¬ Adj G e.1.1 e.1.2) :
    ∀ᵐ ω ∂P, X ω e = false := by
  rw [ae_iff]
  simpa only [Bool.not_eq_false] using
    hX.measure_present_eq_zero_of_nonedge H hH e hne

theorem HasFUSFLaw.ae_subgraph
    {Ω : Type} [MeasurableSpace Ω] {G : GraphCode}
    {P : Measure Ω} {X : Ω → EdgeConfiguration}
    (hX : HasFUSFLaw G P X)
    (H : ℕ → FiniteSubgraphCode) (hH : IsConnectedExhaustion G H) :
    ∀ᵐ ω ∂P, ∀ e : EdgeCode, X ω e = true → Adj G e.1.1 e.1.2 := by
  rw [ae_all_iff]
  intro e
  by_cases he : Adj G e.1.1 e.1.2
  · exact Filter.Eventually.of_forall (fun _ _ => he)
  · filter_upwards [hX.ae_false_of_nonedge H hH e he] with ω hω
    intro htrue
    simp [hω] at htrue

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
-- module Solutions.OAIS_P336.SpanningForest_FUSFLawUnique
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal Topology

namespace Problem336

theorem measurableSet_configurationCylinder (A B : Finset EdgeCode) :
    MeasurableSet (configurationCylinder A B) := by
  unfold configurationCylinder
  convert (A.measurableSet_biInter fun e _ =>
    (measurable_pi_apply e) (measurableSet_singleton true)).inter
    (B.measurableSet_biInter fun e _ =>
    (measurable_pi_apply e) (measurableSet_singleton false)) using 1
  ext x
  simp

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

lemma integral_ratio_finiteUSTMeasure (K : FiniteSubgraphCode)
    (hK : (spanningTrees K).Nonempty) (f g : EdgeConfiguration → ℝ) :
    (∫ X, f X ∂finiteUSTMeasure K) / (∫ X, g X ∂finiteUSTMeasure K) =
      (∑ T ∈ spanningTrees K, f (finiteTreeConfiguration T)) /
        (∑ T ∈ spanningTrees K, g (finiteTreeConfiguration T)) := by
  rw [integral_finiteUSTMeasure, integral_finiteUSTMeasure]
  exact div_div_div_cancel_right₀ (by exact_mod_cast hK.card_pos.ne') _ _

end Problem336

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

theorem outerLimit_mem_Icc {X : Type*} {b : ℕ → X → ℝ}
    {a c : ℝ} (hb : ∀ n x, b n x ∈ Set.Icc a c) (x : X) :
    outerLimit b x ∈ Set.Icc a c := by
  have hu : atTop.IsBoundedUnder (· ≤ ·) (fun n => b n x) :=
    isBoundedUnder_of ⟨c, fun n => (hb n x).2⟩
  have hl : atTop.IsCoboundedUnder (· ≤ ·) (fun n => b n x) :=
    isCoboundedUnder_le_of_le atTop fun n => (hb n x).1
  constructor
  · exact le_limsup_of_frequently_le
      (Eventually.of_forall fun n => (hb n x).1).frequently hu
  · exact limsup_le_of_le hl (Eventually.of_forall fun n => (hb n x).2)

theorem outerLimit_le_add {X Y : Type*}
    {b : ℕ → X → ℝ} {c : ℕ → Y → ℝ}
    {lo hi : ℝ} (hb : ∀ n x, lo ≤ b n x)
    (hc : ∀ n y, c n y ∈ Set.Icc lo hi)
    {x : X} {y : Y} {d : ℝ} (hbc : ∀ n, b n x ≤ c n y + d) :
    outerLimit b x ≤ outerLimit c y + d := by
  have hbl : atTop.IsCoboundedUnder (· ≤ ·) (fun n => b n x) :=
    isCoboundedUnder_le_of_le atTop fun n => hb n x
  have hcu : atTop.IsBoundedUnder (· ≤ ·) (fun n => c n y) :=
    isBoundedUnder_of ⟨hi, fun n => (hc n y).2⟩
  have hcl : atTop.IsCoboundedUnder (· ≤ ·) (fun n => c n y) :=
    isCoboundedUnder_le_of_le atTop fun n => (hc n y).1
  have hcdu : atTop.IsBoundedUnder (· ≤ ·) (fun n => c n y + d) :=
    isBoundedUnder_of ⟨hi + d, fun n => add_le_add (hc n y).2 le_rfl⟩
  exact (limsup_le_limsup (Eventually.of_forall hbc) hbl hcdu).trans_eq
    (limsup_add_const atTop (fun n => c n y) d hcu hcl)

theorem abs_outerLimit_sub_le {X : Type*} {b : ℕ → X → ℝ}
    {lo hi : ℝ} (hb : ∀ n x, b n x ∈ Set.Icc lo hi)
    {x y : X} {d : ℝ} (hxy : ∀ n, |b n x - b n y| ≤ d) :
    |outerLimit b x - outerLimit b y| ≤ d := by
  apply abs_le.mpr
  constructor
  · have h := outerLimit_le_add (fun n x => (hb n x).1) hb
      (x := y) (y := x) (d := d) (fun n => by
        have h := (abs_le.mp (hxy n)).1
        linarith)
    linarith
  · have h := outerLimit_le_add (fun n x => (hb n x).1) hb
      (x := x) (y := y) (d := d) (fun n => by
        have h := (abs_le.mp (hxy n)).2
        linarith)
    linarith

theorem outerLimit_eq_of_tendsto {X : Type*} {b : ℕ → X → ℝ}
    {x : X} {a : ℝ} (h : Tendsto (fun n => b n x) atTop (nhds a)) :
    outerLimit b x = a :=
  h.limsup_eq

end CanonicalDrift
end Problem336

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

theorem innerMean_eq_of_tendsto {G : GraphCode}
    (e : EdgeCode) (n : ℕ) (t : ℝ) (y : EdgeCode → ℝ) {a : ℝ}
    (h : Tendsto (fun m => finiteBallMean G e n m t y) atTop (nhds a)) :
    innerMean G e n t y = a := CanonicalDrift.outerLimit_eq_of_tendsto h

theorem finiteBallMean_of_not_adj {G : GraphCode}
    (e : EdgeCode) (he : ¬ Adj G e.1.1 e.1.2) (n m : ℕ)
    (t : ℝ) (y : EdgeCode → ℝ) : finiteBallMean G e n m t y = 0 := by
  apply mean_of_not_mem
  intro hmem
  exact he ((mem_inducedCode_edges G (edgeBallCode G m e) e.1).mp hmem).2.2.2

theorem drift_of_not_adj {G : GraphCode}
    (e : EdgeCode) (he : ¬ Adj G e.1.1 e.1.2) (t : ℝ) (y : EdgeCode → ℝ) :
    drift G t y e = 0 := by
  simp only [drift, innerMean, CanonicalDrift.outerLimit,
    finiteBallMean_of_not_adj e he, limsup_const]

end Problem336.GraphTreePosterior

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

omit [TopologicalSpace Ω] [OpensMeasurableSpace Ω] in

theorem measurable_tiltedMean {A : Type*} [MeasurableSpace A]
    (μ : ProbabilityMeasure Ω) (h X : A → Ω → ℝ)
    (hh : Measurable (Function.uncurry h))
    (hX : Measurable (Function.uncurry X)) :
    Measurable (fun a => tiltedMean μ (h a) (X a)) := by
  exact ((hX.mul hh.exp).stronglyMeasurable.integral_prod_right).measurable.div
    (hh.exp.stronglyMeasurable.integral_prod_right).measurable

theorem tiltedMean_mem_Icc [CompactSpace Ω] (μ : ProbabilityMeasure Ω)
    {h X : Ω → ℝ} (hh : Continuous h) (hX : Continuous X)
    (hb : ∀ x, X x ∈ Set.Icc (0 : ℝ) 1) :
    tiltedMean μ h X ∈ Set.Icc (0 : ℝ) 1 := by
  have hd := integral_exp_pos μ hh
  have hi : Integrable (fun x => Real.exp (h x)) (μ : Measure Ω) :=
    (BoundedContinuousFunction.mkOfCompact ⟨_, Real.continuous_exp.comp hh⟩).integrable _
  have hn : Integrable (fun x => X x * Real.exp (h x)) (μ : Measure Ω) :=
    (BoundedContinuousFunction.mkOfCompact ⟨_, hX.mul (Real.continuous_exp.comp hh)⟩).integrable _
  constructor
  · exact div_nonneg (integral_nonneg (fun x => mul_nonneg (hb x).1 (Real.exp_pos _).le)) hd.le
  · apply (div_le_one₀ hd).2
    exact integral_mono hn hi (fun x => mul_le_of_le_one_left (Real.exp_pos _).le (hb x).2)

variable {I : Type*}

theorem continuous_finiteEnergy (S : Finset I) (h : I → ℝ) :
    Continuous (finiteEnergy S h) := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul (continuous_bit.comp (continuous_apply i))

variable [Countable I]

theorem tendsto_finiteTiltMean
    {J : Type*} {l : Filter J}
    {μs : J → ProbabilityMeasure (I → Bool)} {μ : ProbabilityMeasure (I → Bool)}
    (hμ : Tendsto μs l (𝓝 μ)) (S : Finset I) (h : I → ℝ) (e : I) :
    Tendsto (fun j => finiteTiltMean (μs j) S h e) l (𝓝 (finiteTiltMean μ S h e)) :=
  tendsto_tiltedMean hμ (continuous_finiteEnergy S h)
    (continuous_bit.comp (continuous_apply e))

theorem finiteTiltMean_mem_Icc (μ : ProbabilityMeasure (I → Bool))
    (S : Finset I) (h : I → ℝ) (e : I) :
    finiteTiltMean μ S h e ∈ Set.Icc (0 : ℝ) 1 := by
  apply tiltedMean_mem_Icc μ (continuous_finiteEnergy S h)
    (continuous_bit.comp (continuous_apply e))
  intro x
  cases hx : x e <;> simp [bit, hx]

omit [Countable I] in

theorem measurable_finitePosterior (μ : ProbabilityMeasure (I → Bool))
    (S : Finset I) (e : I) :
    Measurable (fun p : ℝ × (I → ℝ) =>
      finiteTiltMean μ S (fun i => p.2 i - p.1 / 2) e) := by
  apply measurable_tiltedMean
  · change Measurable (fun q : (ℝ × (I → ℝ)) × (I → Bool) =>
      ∑ i ∈ S, (q.1.2 i - q.1.1 / 2) * bit (q.2 i))
    apply Finset.measurable_sum
    intro i hi
    have hfield : Measurable (fun q : (ℝ × (I → ℝ)) × (I → Bool) =>
        q.1.2 i - q.1.1 / 2) :=
      (((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).sub
        ((measurable_fst.comp measurable_fst).div_const 2))
    have hbit : Measurable (fun q : (ℝ × (I → ℝ)) × (I → Bool) => bit (q.2 i)) :=
      continuous_bit.measurable.comp ((measurable_pi_apply i).comp measurable_snd)
    exact hfield.mul hbit
  · change Measurable (fun q : (ℝ × (I → ℝ)) × (I → Bool) => bit (q.2 e))
    exact continuous_bit.measurable.comp ((measurable_pi_apply e).comp measurable_snd)

end Problem336.TiltLimit

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_IntrinsicPosteriorIdentification
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Problem336.GraphTreePosterior

theorem finiteEnergy_finiteTreeConfiguration (T : Finset (ℕ × ℕ))
    (S : Finset EdgeCode) (t : ℝ) (y : EdgeCode → ℝ) :
    TiltLimit.finiteEnergy S (fun f => y f - t / 2) (finiteTreeConfiguration T) =
      energy T S t y := by
  classical
  unfold TiltLimit.finiteEnergy energy
  apply Finset.sum_congr rfl
  intro f hf
  by_cases h : f.1 ∈ T <;> simp [TiltLimit.bit, finiteTreeConfiguration, h]

theorem mean_eq_finiteUSTProbabilityMeasure_tilt (K : FiniteSubgraphCode)
    (hK : (spanningTrees K).Nonempty) (e : EdgeCode) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) :
    mean K e S t y =
      TiltLimit.finiteTiltMean (finiteUSTProbabilityMeasure K hK) S
        (fun f => y f - t / 2) e := by
  classical
  unfold TiltLimit.finiteTiltMean TiltLimit.tiltedMean
  change mean K e S t y =
    (∫ X, TiltLimit.bit (X e) *
      Real.exp (TiltLimit.finiteEnergy S (fun f => y f - t / 2) X)
      ∂finiteUSTMeasure K) /
    (∫ X, Real.exp (TiltLimit.finiteEnergy S (fun f => y f - t / 2) X)
      ∂finiteUSTMeasure K)
  rw [integral_ratio_finiteUSTMeasure K hK]
  simp only [finiteEnergy_finiteTreeConfiguration]
  unfold mean numerator partition weight
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases h : e.1 ∈ T <;> simp [TiltLimit.bit, finiteTreeConfiguration, h]

theorem tendsto_finiteBallMean_of_hasFUSFLaw
    {G : GraphCode} (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id)
    (e : EdgeCode) (he : Adj G e.1.1 e.1.2)
    (n : ℕ) (t : ℝ) (y : EdgeCode → ℝ) :
    Tendsto (fun m => finiteBallMean G e n m t y) atTop
      (𝓝 (TiltLimit.finiteTiltMean μ (edgeCodes (Intrinsic.exhaustion G e n))
        (fun f => y f - t / 2) e)) := by
  have hH := Intrinsic.isConnectedExhaustion G hc hf e he
  have hweak := hμ.tendsto_finiteUSTProbabilityMeasure (Intrinsic.exhaustion G e) hH
  have hseq : (fun m => finiteBallMean G e n m t y) =
      (fun m => TiltLimit.finiteTiltMean
        (finiteUSTProbabilityMeasure (Intrinsic.exhaustion G e m)
          (FiniteEncoding.spanningTrees_nonempty (hH.1 m)))
        (edgeCodes (Intrinsic.exhaustion G e n)) (fun f => y f - t / 2) e) := by
    funext m
    exact mean_eq_finiteUSTProbabilityMeasure_tilt _ _ _ _ _ _
  rw [hseq]
  exact TiltLimit.tendsto_finiteTiltMean hweak _ _ _

theorem innerMean_eq_finiteTiltMean_of_hasFUSFLaw
    {G : GraphCode} (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id)
    (e : EdgeCode) (he : Adj G e.1.1 e.1.2)
    (n : ℕ) (t : ℝ) (y : EdgeCode → ℝ) :
    innerMean G e n t y =
      TiltLimit.finiteTiltMean μ (edgeCodes (Intrinsic.exhaustion G e n))
        (fun f => y f - t / 2) e :=
  innerMean_eq_of_tendsto e n t y
    (tendsto_finiteBallMean_of_hasFUSFLaw hc hf hμ e he n t y)

end Problem336.GraphTreePosterior

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PosteriorDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Problem336.PosteriorDrift
open TiltLimit

variable {I : Type*} [Countable I]

omit [Countable I] in
theorem measurable_drift_coordinate (μ : ProbabilityMeasure (I → Bool))
    (S : I → ℕ → Finset I) (e : I) :
    Measurable (fun p : ℝ × (I → ℝ) => drift μ S p.1 p.2 e) :=
  CanonicalDrift.measurable_outerLimit (fun n => measurable_finitePosterior μ (S e n) e)

theorem drift_mem_Icc (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I)
    (t : ℝ) (y : I → ℝ) (e : I) : drift μ S t y e ∈ Set.Icc (0 : ℝ) 1 :=
  CanonicalDrift.outerLimit_mem_Icc (b := finiteStage μ S e)
    (fun n (p : ℝ × (I → ℝ)) =>
      finiteTiltMean_mem_Icc μ (S e n) (fun i => p.2 i - p.1 / 2) e) (t, y)

theorem drift_response (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I)
    {L : ℝ} (hresponse : FiniteResponseBound μ S L)
    (t : ℝ) (y y' : I → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hdiff : ∀ i, |y i - y' i| ≤ D) (e : I) :
    |drift μ S t y e - drift μ S t y' e| ≤ L * D := by
  apply CanonicalDrift.abs_outerLimit_sub_le (b := finiteStage μ S e)
    (fun n (p : ℝ × (I → ℝ)) =>
      finiteTiltMean_mem_Icc μ (S e n) (fun i => p.2 i - p.1 / 2) e)
  intro n
  apply hresponse e n _ _ D hD
  intro i hi
  simpa only [sub_sub_sub_cancel_right] using hdiff i

end Problem336.PosteriorDrift

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PosteriorSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem336.TiltLimit

variable {Ω : Type*} [MeasurableSpace Ω]

variable {I : Type*}

theorem finiteTiltMean_eq_zero_of_ae_absent
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (h : I → ℝ) (e : I)
    (he : ∀ᵐ x ∂(μ : Measure (I → Bool)), x e = false) :
    finiteTiltMean μ S h e = 0 := by
  unfold finiteTiltMean tiltedMean
  have hn : (∫ x, bit (x e) * Real.exp (finiteEnergy S h x)
      ∂(μ : Measure (I → Bool))) = 0 := by
    calc
      _ = ∫ _x, (0 : ℝ) ∂(μ : Measure (I → Bool)) := by
        apply integral_congr_ae
        filter_upwards [he] with x hx
        simp [hx, bit]
      _ = 0 := integral_zero _ _
  rw [hn, zero_div]

theorem limsup_finiteTiltMean_eq_zero_of_ae_absent
    (μ : ProbabilityMeasure (I → Bool)) (S : ℕ → Finset I)
    (h : ℕ → I → ℝ) (e : I)
    (he : ∀ᵐ x ∂(μ : Measure (I → Bool)), x e = false) :
    Filter.limsup (fun n => finiteTiltMean μ (S n) (h n) e) Filter.atTop = 0 := by
  simp only [finiteTiltMean_eq_zero_of_ae_absent μ _ _ e he]
  exact Filter.limsup_const (f := (Filter.atTop : Filter ℕ)) (b := (0 : ℝ))

end Problem336.TiltLimit

namespace Problem336.PosteriorDrift
open TiltLimit

variable {I : Type*}

theorem drift_eq_zero_of_ae_absent
    (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I)
    (t : ℝ) (y : I → ℝ) (e : I)
    (he : ∀ᵐ x ∂(μ : Measure (I → Bool)), x e = false) :
    drift μ S t y e = 0 :=
  limsup_finiteTiltMean_eq_zero_of_ae_absent μ (S e) (fun _ i => y i - t / 2) e he

end Problem336.PosteriorDrift

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_IntrinsicPosteriorDrift
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336.GraphTreePosterior

theorem drift_eq_posteriorDrift_of_hasFUSFLaw
    {G : GraphCode} (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id)
    (e : EdgeCode) (he : Adj G e.1.1 e.1.2)
    (t : ℝ) (y : EdgeCode → ℝ) :
    drift G t y e =
      PosteriorDrift.drift μ (fun f n => edgeCodes (Intrinsic.exhaustion G f n)) t y e := by
  unfold drift PosteriorDrift.drift
  congr 1
  funext n q
  exact innerMean_eq_finiteTiltMean_of_hasFUSFLaw hc hf hμ e he n q.1 q.2

theorem drift_eq_posteriorDrift_all_of_hasFUSFLaw
    {G : GraphCode} (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id)
    (e : EdgeCode) (t : ℝ) (y : EdgeCode → ℝ) :
    drift G t y e =
      PosteriorDrift.drift μ (fun f n => edgeCodes (Intrinsic.exhaustion G f n)) t y e := by
  by_cases he : Adj G e.1.1 e.1.2
  · exact drift_eq_posteriorDrift_of_hasFUSFLaw hc hf hμ e he t y
  · obtain ⟨H, hH⟩ := hc.exists_connected_exhaustion
    have habsent : ∀ᵐ X ∂(μ : Measure EdgeConfiguration), X e = false :=
      hμ.ae_false_of_nonedge H hH e he
    rw [drift_of_not_adj e he t y,
      PosteriorDrift.drift_eq_zero_of_ae_absent μ _ t y e habsent]

end Problem336.GraphTreePosterior

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PosteriorNullCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem336.TiltLimit

theorem finiteEnergy_eq_of_zero_extra {I : Type*}
    {S T : Finset I} (hST : S ⊆ T) (h : I → ℝ) (x : I → Bool)
    (hzero : ∀ i ∈ T, i ∉ S → x i = false) :
    finiteEnergy S h x = finiteEnergy T h x := by
  classical
  apply Finset.sum_subset hST
  intro i hi hiS
  simp [hzero i hi hiS, bit]

theorem finiteTiltMean_eq_of_zero_extra {I : Type*}
    (ν : ProbabilityMeasure (I → Bool)) {S T : Finset I} (hST : S ⊆ T)
    (hzero : ∀ᵐ x ∂(ν : Measure (I → Bool)), ∀ i ∈ T, i ∉ S → x i = false)
    (h : I → ℝ) (e : I) :
    finiteTiltMean ν S h e = finiteTiltMean ν T h e := by
  have henergy : finiteEnergy S h =ᵐ[(ν : Measure (I → Bool))] finiteEnergy T h :=
    hzero.mono (fun x hx => finiteEnergy_eq_of_zero_extra hST h x hx)
  unfold finiteTiltMean tiltedMean
  congr 1
  · apply integral_congr_ae
    filter_upwards [henergy] with x hx
    rw [hx]
  · apply integral_congr_ae
    filter_upwards [henergy] with x hx
    rw [hx]

end Problem336.TiltLimit

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_AllPairPosteriorDrift
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336.GraphTreePosterior

theorem finiteTiltMean_eq_allPair_of_hasFUSFLaw
    {G : GraphCode} (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id)
    (e : EdgeCode) (n : ℕ) (h : EdgeCode → ℝ) (a : EdgeCode) :
    TiltLimit.finiteTiltMean μ (edgeCodes (Intrinsic.exhaustion G e n)) h a =
      TiltLimit.finiteTiltMean μ (AllPairObservation.observations G e n) h a := by
  apply TiltLimit.finiteTiltMean_eq_of_zero_extra μ
    (AllPairObservation.edgeCodes_exhaustion_subset_observations hf e n)
  obtain ⟨H, hH⟩ := hc.exists_connected_exhaustion
  filter_upwards [hμ.ae_subgraph H hH] with X hX
  intro f hT hS
  cases hxf : X f with
  | false => rfl
  | true =>
      exact False.elim
        (AllPairObservation.not_adj_of_mem_observations_not_mem_edgeCodes hf e f n hT hS
          (hX f hxf))

theorem drift_eq_allPair_posteriorDrift_of_hasFUSFLaw
    {G : GraphCode} (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id)
    (e : EdgeCode) (t : ℝ) (y : EdgeCode → ℝ) :
    drift G t y e =
      PosteriorDrift.drift μ (AllPairObservation.observations G) t y e := by
  rw [drift_eq_posteriorDrift_all_of_hasFUSFLaw hc hf hμ]
  change Filter.limsup
      (fun n => TiltLimit.finiteTiltMean μ (edgeCodes (Intrinsic.exhaustion G e n))
        (fun f => y f - t / 2) e) Filter.atTop =
    Filter.limsup
      (fun n => TiltLimit.finiteTiltMean μ (AllPairObservation.observations G e n)
        (fun f => y f - t / 2) e) Filter.atTop
  apply Filter.limsup_congr
  exact Filter.Eventually.of_forall fun n =>
    finiteTiltMean_eq_allPair_of_hasFUSFLaw hc hf hμ e n (fun f => y f - t / 2) e

theorem drift_fun_eq_allPair_posteriorDrift_of_hasFUSFLaw
    {G : GraphCode} (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id) :
    drift G = PosteriorDrift.drift μ (AllPairObservation.observations G) := by
  funext t y e
  exact drift_eq_allPair_posteriorDrift_of_hasFUSFLaw hc hf hμ e t y

end Problem336.GraphTreePosterior

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

lemma intervalIntegrable_of_measurable_bounded
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ t, |f t| ≤ C)
    (a d : ℝ) : IntervalIntegrable f volume a d := by
  constructor
  · apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hf.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hC t
  · apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hf.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hC t

lemma continuous_iterate
    (w : ι → ℝ → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ)
    (hw : ∀ i, Continuous (w i))
    (hb : ∀ i, Measurable (fun p : ℝ × (ι → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1) :
    ∀ n i, Continuous (iterate w b n i) := by
  intro n
  induction n with
  | zero => exact hw
  | succ n ih =>
    intro i
    have hm : Measurable (fun s => b s (fun j => iterate w b n j s) i) := by
      exact (hb i).comp (measurable_id.prodMk (Measurable.of_eval (fun j => (ih j).measurable)))
    exact (hw i).add (intervalIntegral.continuous_primitive
      (intervalIntegrable_of_measurable_bounded hm (fun s => hbound s _ i)) 0)

lemma integral_majorant (L t : ℝ) (n : ℕ) :
    (∫ s in (0 : ℝ)..t, L * majorant L s n) = majorant L t (n + 1) := by
  have heq : (fun s : ℝ => L * majorant L s n) =
      (fun s : ℝ => (L ^ (n + 1) / (n + 1).factorial) * s ^ (n + 1)) := by
    funext s
    simp only [majorant, pow_succ]
    ring
  rw [heq, intervalIntegral.integral_const_mul, integral_pow]
  simp only [zero_pow (by omega : n + 1 + 1 ≠ 0), sub_zero, majorant]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

lemma measurable_drift_iterate
    (w : ι → ℝ → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ)
    (hw : ∀ i, Continuous (w i))
    (hb : ∀ i, Measurable (fun p : ℝ × (ι → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1) (n : ℕ) (i : ι) :
    Measurable (fun s => b s (fun j => iterate w b n j s) i) := by
  exact (hb i).comp (measurable_id.prodMk (Measurable.of_eval (fun j => (continuous_iterate w b hw hb hbound n j).measurable)))

lemma intervalIntegrable_drift_iterate
    (w : ι → ℝ → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ)
    (hw : ∀ i, Continuous (w i))
    (hb : ∀ i, Measurable (fun p : ℝ × (ι → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1) (n : ℕ) (i : ι) (a d : ℝ) :
    IntervalIntegrable (fun s => b s (fun j => iterate w b n j s) i) volume a d := by
  exact intervalIntegrable_of_measurable_bounded
    (measurable_drift_iterate w b hw hb hbound n i) (fun s => hbound s _ i) a d

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

end FactorAssembly
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FactorLawTransport
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem336.FactorAssembly

theorem measurable_rule_section {Phi : FactorRule} (hPhi : RuleBorel Phi)
    (G : GraphCode) : Measurable (Phi G) := by
  apply measurable_pi_iff.mpr
  intro e
  exact hPhi.comp (measurable_const.prodMk
    (measurable_id.prodMk measurable_const))

theorem hasFUSFLaw_of_map_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {G : GraphCode} {P : Measure Ω} {Q : Measure Ω'}
    {X : Ω → EdgeConfiguration} {Y : Ω' → EdgeConfiguration}
    (hX : Measurable X) (hY : HasFUSFLaw G Q Y)
    (hLaw : P.map X = Q.map Y) : HasFUSFLaw G P X := by
  refine ⟨fun e => (measurable_pi_apply e).comp hX, ?_⟩
  intro H hH A B
  have hc : P (X ⁻¹' configurationCylinder A B) =
      Q (Y ⁻¹' configurationCylinder A B) := by
    rw [← Measure.map_apply hX (measurableSet_configurationCylinder A B),
      ← Measure.map_apply (Measurable.of_eval hY.1)
        (measurableSet_configurationCylinder A B), hLaw]
  change Filter.Tendsto (fun n => ustCylinder (H n) A B) Filter.atTop
    (nhds (P (X ⁻¹' configurationCylinder A B)))
  rw [hc]
  exact hY.2 H hH A B

end Problem336.FactorAssembly

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_BitRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal

namespace Problem336

theorem measurable_slopeReadout : Measurable slopeReadout := by
  have h : Measurable (fun z : ℕ → ℝ =>
      limsup (fun n : ℕ => z (n + 1) / (n + 1 : ℝ)) atTop) :=
    Measurable.limsup (fun n => (measurable_pi_apply (n + 1)).div_const _)
  exact Measurable.ite (measurableSet_lt measurable_const h)
    measurable_const measurable_const

theorem slopeReadout_of_tendsto {z : ℕ → ℝ} {b : Bool}
    (h : Tendsto (fun n : ℕ => z (n + 1) / (n + 1 : ℝ)) atTop
      (𝓝 (bitValue b))) :
    slopeReadout z = b := by
  unfold slopeReadout
  rw [h.limsup_eq]
  cases b <;> norm_num [bitValue]

theorem slopeReadout_linear_add_noise (b : Bool) (noise : ℕ → ℝ)
    (hnoise : Tendsto (fun n : ℕ => noise (n + 1) / (n + 1 : ℝ)) atTop (𝓝 0)) :
    slopeReadout (fun n => (n : ℝ) * bitValue b + noise n) = b := by
  apply slopeReadout_of_tendsto
  have h := (tendsto_const_nhds (x := bitValue b) (f := atTop)).add hnoise
  simp only [add_zero] at h
  convert h using 1
  ext n
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  simp [add_div, hn]

theorem brownian_integer_slopes {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => B (n : ℝ≥0) ω / (n : ℝ)) atTop (𝓝 0) := by
  let X : ℕ → Ω → ℝ := fun n ω => B ((n + 1 : ℕ) : ℝ≥0) ω - B (n : ℝ≥0) ω
  have hdist (n : ℕ) :
      nndist (((n + 1 : ℕ) : ℝ≥0) : ℝ) ((n : ℝ≥0) : ℝ) = (1 : ℝ≥0) := by
    apply NNReal.eq
    simp [coe_nndist]
  have hlaw (n : ℕ) : HasLaw (X n) (gaussianReal 0 1) P := by
    have h := hB.hasLaw_sub (((n + 1 : ℕ) : ℝ≥0)) (n : ℝ≥0)
    change HasLaw (X n)
      (gaussianReal 0 (nndist (((n + 1 : ℕ) : ℝ≥0) : ℝ) ((n : ℝ≥0) : ℝ))) P at h
    rw [hdist n] at h
    exact h
  have hindep : iIndepFun X P := hB.hasIndepIncrements.nat Nat.mono_cast
  have hmean : P[X 0] = 0 := by
    rw [(hlaw 0).integral_eq, integral_id_gaussianReal]
  have hstrong := strong_law_ae_real X (hlaw 0).hasGaussianLaw.integrable
    (fun _ _ h => hindep.indepFun h) (fun n => (hlaw n).identDistrib (hlaw 0))
  rw [hmean] at hstrong
  filter_upwards [hstrong, hB.eval_zero_ae_eq_zero] with ω hω hzero
  have hsum (n : ℕ) : (∑ i ∈ Finset.range n, X i ω) = B (n : ℝ≥0) ω := by
    simpa only [X, Nat.cast_zero, hzero, sub_zero] using
      Finset.sum_range_sub (fun n : ℕ => B (n : ℝ≥0) ω) n
  simpa only [hsum] using hω

theorem ae_slopeReadout_brownian_observation {I Ω : Type*} [Countable I]
    [MeasurableSpace Ω] {P : Measure Ω} (X : Ω → I → Bool)
    (B : I → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, (fun i => slopeReadout
      (fun n => (n : ℝ) * bitValue (X ω i) + B i (n : ℝ≥0) ω)) = X ω := by
  have hslopes : ∀ᵐ ω ∂P, ∀ i,
      Tendsto (fun n : ℕ => B i (n : ℝ≥0) ω / (n : ℝ)) atTop (𝓝 0) :=
    ae_all_iff.mpr (fun i => brownian_integer_slopes (hB i))
  filter_upwards [hslopes] with ω hω
  funext i
  apply slopeReadout_linear_add_noise
  simpa only [Nat.cast_add, Nat.cast_one] using
    (tendsto_add_atTop_iff_nat 1).mpr (hω i)

theorem measurable_configurationReadout {I : Type*} :
    Measurable (configurationReadout (I := I)) :=
  Measurable.of_eval fun i => measurable_slopeReadout.comp (measurable_pi_apply i)

theorem brownian_observation_readout_hasLaw {I Ω : Type*} [Countable I]
    [MeasurableSpace Ω] {P : Measure Ω} {ν : Measure (I → Bool)}
    (X : Ω → I → Bool) (hX : HasLaw X ν P)
    (B : I → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P) :
    HasLaw (fun ω => configurationReadout
      (fun i (n : ℕ) => (n : ℝ) * bitValue (X ω i) + B i (n : ℝ≥0) ω)) ν P :=
  hX.congr (ae_slopeReadout_brownian_observation X B hB)

theorem sampler_hasLaw_of_brownian_inversion
    {I Ω W Ω' : Type*} [Countable I]
    [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {ρ : Measure W} {ν : Measure (I → Bool)}
    {X : Ω → I → Bool} (hX : HasLaw X ν P)
    {B : I → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) P)
    {innovation : Ω → W} (hinnovation : HasLaw innovation ρ P)
    {fresh : Ω' → W} (hfresh : HasLaw fresh ρ P')
    {Z : W → I → ℕ → ℝ} (hZ : Measurable Z)
    (hinverse : ∀ᵐ ω ∂P, Z (innovation ω) =
      fun i (n : ℕ) => (n : ℝ) * bitValue (X ω i) + B i (n : ℝ≥0) ω) :
    HasLaw (fun ω => configurationReadout (Z (fresh ω))) ν P' := by
  have href : HasLaw (fun ω => configurationReadout (Z (innovation ω))) ν P := by
    apply (brownian_observation_readout_hasLaw X hX B hB).congr
    filter_upwards [hinverse] with ω hω
    rw [hω]
  exact HasLaw.comp_of_hasLaw_comp
    (f := fun w : W => configurationReadout (Z w))
    (measurable_configurationReadout.comp hZ).aemeasurable hinnovation hfresh href

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PicardBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped Topology NNReal

namespace Problem336.DeterministicDecoder

lemma picardBound_nonneg {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) (n : ℕ) :
    0 ≤ picardBound L T n := by
  unfold picardBound
  positivity

lemma picardBound_le_exp_term {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) (n : ℕ) :
    picardBound L T n ≤ T * ((L * T) ^ n / n.factorial) := by
  have hfac : (n.factorial : ℝ) ≤ ((n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  calc
    picardBound L T n = T * (L * T) ^ n / (n + 1).factorial := by
      simp only [picardBound, mul_pow, pow_succ]
      ring
    _ ≤ T * (L * T) ^ n / n.factorial := by
      apply div_le_div_of_nonneg_left
      · positivity
      · positivity
      · exact hfac
    _ = T * ((L * T) ^ n / n.factorial) := by ring

lemma summable_picardBound {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) :
    Summable (picardBound L T) := by
  exact Summable.of_nonneg_of_le (picardBound_nonneg hL hT)
    (picardBound_le_exp_term hL hT)
    ((Real.summable_pow_div_factorial (L * T)).mul_left T)

lemma tendsto_picardBound_zero {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) :
    Tendsto (picardBound L T) atTop (𝓝 0) :=
  (summable_picardBound hL hT).tendsto_atTop_zero

end Problem336.DeterministicDecoder

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PicardUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace Problem336.DeterministicDecoder

theorem integral_picardBound (L t : ℝ) (n : ℕ) :
    (∫ s in (0 : ℝ)..t, L * picardBound L s n) = picardBound L t (n + 1) := by
  exact Picard.integral_majorant L t n

theorem solution_picard_bound {I : Type*} (L : ℝ) (hL : 0 ≤ L)
    (b : ℝ → (I → ℝ) → I → ℝ) (z : ℕ → ℝ → I → ℝ)
    (x : ℝ → I → ℝ)
    (hb : ∀ t, 0 ≤ t → ∀ y i, |b t y i| ≤ 1)
    (hlip : BoundedDifferenceResponse b L)
    (hint : ∀ n t, 0 ≤ t → ∀ i,
      IntervalIntegrable (fun s => b s (z n s) i) volume 0 t)
    (hxint : ∀ t, 0 ≤ t → ∀ i,
      IntervalIntegrable (fun s => b s (x s) i) volume 0 t)
    (hstep : ∀ n t i,
      z (n + 1) t i = z 0 t i + ∫ s in (0 : ℝ)..t, b s (z n s) i)
    (hsol : ∀ t, 0 ≤ t → ∀ i,
      x t i = z 0 t i + ∫ s in (0 : ℝ)..t, b s (x s) i) :
    ∀ n t, 0 ≤ t → ∀ i,
      |x t i - z n t i| ≤ picardBound L t n := by
  intro n
  induction n with
  | zero =>
      intro t ht i
      rw [hsol t ht, add_sub_cancel_left, picardBound_zero, ← Real.norm_eq_abs]
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := t) (C := (1 : ℝ))
        (f := fun s => b s (x s) i) (fun s hs => by
          rw [uIoc_of_le ht] at hs
          exact (Real.norm_eq_abs _).le.trans (hb s hs.1.le _ i))
      simpa only [sub_zero, abs_of_nonneg ht, one_mul] using h
  | succ n ih =>
      intro t ht i
      rw [hsol t ht, hstep n, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub (hxint t ht i) (hint n t ht i),
        ← Real.norm_eq_abs]
      calc
        ‖∫ s in (0 : ℝ)..t, b s (x s) i - b s (z n s) i‖
            ≤ ∫ s in (0 : ℝ)..t, L * picardBound L s n := by
          apply intervalIntegral.norm_integral_le_of_norm_le ht
          · apply Filter.Eventually.of_forall
            intro s hs
            rw [Real.norm_eq_abs]
            exact hlip s hs.1.le _ _ _ (picardBound_nonneg hL hs.1.le n)
              (ih s hs.1.le) i
          · exact (show Continuous (fun s => L * picardBound L s n) by
              unfold picardBound
              fun_prop).intervalIntegrable _ _
        _ = picardBound L t (n + 1) := integral_picardBound L t n

end Problem336.DeterministicDecoder

namespace Problem336.Picard

theorem solution_iterate_bound {I : Type*}
    (w x : I → ℝ → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (hw : ∀ i, Continuous (w i)) (hx : ∀ i, Measurable (x i))
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ (s : ℝ) (y y' : I → ℝ) (D : ℝ),
      0 ≤ D → (∀ j, |y j - y' j| ≤ D) →
      ∀ i, |b s y i - b s y' i| ≤ L * D)
    (hsol : ∀ t, 0 ≤ t → ∀ i,
      x i t = w i t + ∫ s in (0 : ℝ)..t, b s (fun j => x j s) i) :
    ∀ n i t, 0 ≤ t →
      |x i t - iterate w b n i t| ≤ majorant L t n := by
  have hxi (t : ℝ) (i : I) :
      IntervalIntegrable (fun s => b s (fun j => x j s) i) volume 0 t := by
    apply intervalIntegrable_of_measurable_bounded
    · exact (hb i).comp (measurable_id.prodMk (Measurable.of_eval hx))
    · exact fun s => hbound s _ i
  have h := DeterministicDecoder.solution_picard_bound L hL b
    (fun n t i => iterate w b n i t) (fun t i => x i t)
    (fun t _ y i => hbound t y i)
    (fun t _ y y' D hD hdiff i => hresponse t y y' D hD hdiff i)
    (fun n t _ i => intervalIntegrable_drift_iterate w b hw hb hbound n i 0 t)
    (fun t _ i => hxi t i) (fun _ _ _ => rfl) hsol
  exact fun n i t ht => h n t ht i

theorem decode_eq_solution {I : Type*}
    (w x : I → ℝ → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (hw : ∀ i, Continuous (w i)) (hx : ∀ i, Measurable (x i))
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ (s : ℝ) (y y' : I → ℝ) (D : ℝ),
      0 ≤ D → (∀ j, |y j - y' j| ≤ D) →
      ∀ i, |b s y i - b s y' i| ≤ L * D)
    (hsol : ∀ t, 0 ≤ t → ∀ i,
      x i t = w i t + ∫ s in (0 : ℝ)..t, b s (fun j => x j s) i) :
    ∀ i t, 0 ≤ t → decode w b i t = x i t := by
  intro i t ht
  apply Filter.Tendsto.limUnder_eq
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ => dist_nonneg)
  · intro n
    simpa only [Real.dist_eq, abs_sub_comm] using
      solution_iterate_bound w x b hw hx hb hbound hL hresponse hsol n i t ht
  · exact DeterministicDecoder.tendsto_picardBound_zero hL ht

end Problem336.Picard

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PicardSamplerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem336.PicardSampler

lemma sample_apply_unshifted {I W : Type*}
    (w : W → I → ℝ → ℝ) (b : ℝ → (I → ℝ) → I → ℝ) (q : W) (i : I) :
    sample w b q i =
      if (1 / 2 : ℝ) < limsup
        (fun n : ℕ => Picard.decode (w q) b i n / (n : ℝ)) atTop
      then true else false := by
  have hshift := Filter.limsup_nat_add
    (fun n : ℕ => Picard.decode (w q) b i n / (n : ℝ)) 1
  simpa only [sample, configurationReadout, decodedIntegers, slopeReadout,
    Nat.cast_add, Nat.cast_one] using
    congrArg (fun r : ℝ => if (1 / 2 : ℝ) < r then true else false) hshift

lemma measurable_decodedIntegers {I W : Type*} [MeasurableSpace W]
    (w : W → I → ℝ → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (hw : ∀ i, Measurable (fun p : W × ℝ => w p.1 i p.2))
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i)) :
    Measurable (decodedIntegers w b) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro n
  have hd := Picard.measurable_decode w (fun _ => b) hw
    (fun i => (hb i).comp measurable_snd) i
  exact hd.comp (measurable_id.prodMk measurable_const)

theorem hasLaw_of_integral_coupling
    {I Ω W Ω' : Type*} [Countable I]
    [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {ρ : Measure W} {ν : Measure (I → Bool)}
    {X : Ω → I → Bool} (hX : HasLaw X ν P)
    {B : I → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) P)
    {innovation : Ω → W} (hinnovation : HasLaw innovation ρ P)
    {fresh : Ω' → W} (hfresh : HasLaw fresh ρ P')
    (w : W → I → ℝ → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (hw : ∀ i, Measurable (fun p : W × ℝ => w p.1 i p.2))
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ t y y' D, 0 ≤ D → (∀ j, |y j - y' j| ≤ D) →
      ∀ i, |b t y i - b t y' i| ≤ L * D)
    (Y : Ω → I → ℝ → ℝ)
    (hpaths : ∀ᵐ ω ∂P, (∀ i, Continuous (w (innovation ω) i)) ∧
      (∀ i, Measurable (Y ω i)))
    (heq : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∀ i,
      Y ω i t = w (innovation ω) i t +
        ∫ s in (0 : ℝ)..t, b s (fun j => Y ω j s) i)
    (hobs : ∀ᵐ ω ∂P, ∀ i (n : ℕ),
      Y ω i n = (n : ℝ) * bitValue (X ω i) + B i (n : ℝ≥0) ω) :
    HasLaw (fun ω => sample w b (fresh ω)) ν P' := by
  apply sampler_hasLaw_of_brownian_inversion hX hB hinnovation hfresh
    (measurable_decodedIntegers w b hw hb)
  filter_upwards [hpaths, heq, hobs] with ω hp he ho
  funext i n
  exact (Picard.decode_eq_solution (w (innovation ω)) (Y ω) b hp.1 hp.2
    hb hbound hL hresponse he i n (Nat.cast_nonneg n)).trans (ho i n)

end Problem336.PicardSampler

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FactorSampler
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem336.FactorAssembly

theorem rule_eq_sample (b : GraphDrift) (w : GraphNoise) (G : GraphCode) :
    rule b w G = PicardSampler.sample (w G) (b G) := by
  funext U e
  exact (PicardSampler.sample_apply_unshifted (w G) (b G) U e).symm

theorem canonical_hasFUSFLaw_of_sampler_hasLaw
    {b : GraphDrift} {w : GraphNoise} (hb : DriftBorel b) (hw : NoiseBorel w)
    (G : GraphCode) {ν : Measure EdgeConfiguration}
    (hν : HasFUSFLaw G ν id)
    (hLaw : HasLaw (PicardSampler.sample (w G) (b G)) ν privatePoolLaw) :
    HasFUSFLaw G privatePoolLaw (rule b w G) := by
  have hm : Measurable (rule b w G) :=
    measurable_rule_section (rule_borel hb hw) G
  have heq : privatePoolLaw.map (rule b w G) = ν.map id := by
    rw [rule_eq_sample, hLaw.map_eq, Measure.map_id]
  exact hasFUSFLaw_of_map_eq (X := rule b w G) (Y := id) hm hν heq

end Problem336.FactorAssembly

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PicardNonnegativeTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped Topology NNReal

namespace Problem336.Picard.NonnegativeTime

variable {ι : Type*}

theorem continuous_extendInput {w : ι → ℝ≥0 → ℝ}
    (hw : ∀ i, Continuous (w i)) (i : ι) : Continuous (extendInput w i) :=
  (hw i).comp continuous_real_toNNReal

theorem measurable_extendInput
    {α : Type*} [MeasurableSpace α] (w : α → ι → ℝ≥0 → ℝ)
    (hw : ∀ i, Measurable (fun p : α × ℝ≥0 => w p.1 i p.2))
    (i : ι) : Measurable (fun p : α × ℝ => extendInput (w p.1) i p.2) :=
  (hw i).comp (measurable_fst.prodMk
    (continuous_real_toNNReal.measurable.comp measurable_snd))

end Problem336.Picard.NonnegativeTime

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PicardNonnegativeSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem336.PicardSampler.NonnegativeTime

open Picard.NonnegativeTime

theorem hasLaw_of_integral_coupling
    {I Ω W Ω' : Type*} [Countable I]
    [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {ρ : Measure W} {ν : Measure (I → Bool)}
    {X : Ω → I → Bool} (hX : HasLaw X ν P)
    {B : I → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) P)
    {innovation : Ω → W} (hinnovation : HasLaw innovation ρ P)
    {fresh : Ω' → W} (hfresh : HasLaw fresh ρ P')
    (w : W → I → ℝ≥0 → ℝ) (b : ℝ → (I → ℝ) → I → ℝ)
    (hw : ∀ i, Measurable (fun p : W × ℝ≥0 => w p.1 i p.2))
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ t y z D, 0 ≤ D → (∀ j, |y j - z j| ≤ D) →
      ∀ i, |b t y i - b t z i| ≤ L * D)
    (Y : Ω → I → ℝ≥0 → ℝ)
    (hpaths : ∀ᵐ ω ∂P, (∀ i, Continuous (w (innovation ω) i)) ∧
      (∀ i, Measurable (Y ω i)))
    (heq : ∀ᵐ ω ∂P, ∀ (t : ℝ≥0) i,
      Y ω i t = w (innovation ω) i t +
        ∫ s in (0 : ℝ)..(t : ℝ), b s (fun j => Y ω j (Real.toNNReal s)) i)
    (hobs : ∀ᵐ ω ∂P, ∀ i (n : ℕ),
      Y ω i n = (n : ℝ) * bitValue (X ω i) + B i (n : ℝ≥0) ω) :
    HasLaw (fun ω => sample w b (fresh ω)) ν P' := by
  apply PicardSampler.hasLaw_of_integral_coupling hX hB hinnovation hfresh
    (fun q => extendInput (w q)) b (measurable_extendInput w hw)
    hb hbound hL hresponse (fun ω => extendInput (Y ω))
  · filter_upwards [hpaths] with ω hω
    exact ⟨continuous_extendInput hω.1,
      fun i => (hω.2 i).comp continuous_real_toNNReal.measurable⟩
  · filter_upwards [heq] with ω hω
    intro t ht i
    simpa only [extendInput, Real.coe_toNNReal t ht] using hω (Real.toNNReal t) i
  · filter_upwards [hobs] with ω hω
    intro i n
    simpa only [extendInput, Real.toNNReal_natCast] using hω i n

end Problem336.PicardSampler.NonnegativeTime

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GlobalWiener
attribute [-instance] _root_.OAI.Problem336.CanonicalBrownianReference.law_probability _root_.OAI.Problem336.CanonicalBrownianReference.noiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace Problem336.GlobalWiener

attribute [local instance] OAI.Problem336.GlobalWiener.instMeasurableSpacePath
theorem isBrownian_wienerMeasure :
    IsBrownianReal (fun t (w : Path) => w t) wienerMeasure :=
  (Classical.choose_spec exists_wiener).2

end Problem336.GlobalWiener

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

theorem map_sample : uniform01.map sample = GlobalWiener.wienerMeasure :=
  (Classical.choose_spec (exists_uniform01_sampler GlobalWiener.wienerMeasure)).2

end Problem336.WienerSampler

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_AllPairWiener
attribute [-instance] _root_.OAI.Problem336.CanonicalBrownianReference.law_probability _root_.OAI.Problem336.CanonicalBrownianReference.noiseLaw_probability _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
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

theorem measurable_paths_field (G : GraphCode) : Measurable (paths G) := by
  apply Measurable.of_eval
  intro e
  exact WienerSampler.measurable_sample.comp (AllPairIID.measurable_uniformRule_fixed G e)

theorem paths_hasLaw {Ω : Type} [MeasurableSpace Ω]
    (G : GraphCode) (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    (P : Measure Ω) (U : ℕ → Ω → ℝ) (hU : IsVertexIID P U) :
    HasLaw (fun ω => paths G (fun v => U v ω)) law P := by
  refine ⟨((measurable_paths_field G).comp (Measurable.of_eval hU.1)).aemeasurable, ?_⟩
  exact AllPairIID.sampled_uniformRule_law GlobalWiener.wienerMeasure
    WienerSampler.sample WienerSampler.measurable_sample WienerSampler.map_sample
    G hc hf P U hU

theorem noise_borel : NoiseBorel noise := by
  intro e
  have hp : Measurable (fun p : (GraphCode × (ℕ → ℝ)) × ℝ => paths p.1.1 p.1.2 e) :=
    measurable_paths.comp (measurable_fst.fst.prodMk
      (measurable_fst.snd.prodMk measurable_const))
  exact measurable_pathEval.comp (hp.prodMk measurable_snd)

theorem sampler_hasLaw_of_product
    (b : GraphDrift) (G : GraphCode) (hc : GraphConnected G)
    (hf : GraphLocallyFinite G) {ν : Measure EdgeConfiguration}
    (hLaw : HasLaw (PicardSampler.NonnegativeTime.sample
      (fun (W : EdgeCode → Path) e t => W e t) (b G)) ν law) :
    HasLaw (PicardSampler.sample (noise G) (b G)) ν privatePoolLaw := by
  exact hLaw.comp (paths_hasLaw G hc hf privatePoolLaw
    (fun v U => U v) CanonicalIID.canonical_isVertexIID)

end Problem336.AllPairWiener

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_BrownianReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.BrownianReference

variable {A W I : Type*} [MeasurableSpace A] [MeasurableSpace W]
  (ν : Measure A) (ρ : Measure W) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]

omit [IsProbabilityMeasure ν] in
theorem hidden_hasLaw : HasLaw (fun q : A × (I → W) => q.1) ν (coupling ν ρ) :=
  measurePreserving_fst.hasLaw

theorem noise_coordinate_preserving (i : I) :
    MeasurePreserving (fun q : A × (I → W) => q.2 i) (coupling ν ρ) ρ :=
  (measurePreserving_eval_infinitePi (fun _ : I => ρ) i).comp measurePreserving_snd

theorem preBrownian_process {b : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal b ρ) (i : I) :
    IsPreBrownianReal (fun t (q : A × (I → W)) => b t (q.2 i)) (coupling ν ρ) := by
  constructor
  intro S
  exact (hB.hasLaw S).comp (noise_coordinate_preserving ν ρ i).hasLaw

theorem brownian_process {b : ℝ≥0 → W → ℝ} (hB : IsBrownianReal b ρ) (i : I) :
    IsBrownianReal (fun t (q : A × (I → W)) => b t (q.2 i)) (coupling ν ρ) where
  toIsPreBrownianReal := preBrownian_process ν ρ hB.toIsPreBrownianReal i
  cont := (noise_coordinate_preserving ν ρ i).quasiMeasurePreserving.ae hB.cont

end Problem336.BrownianReference

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CanonicalBrownianReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace Problem336.CanonicalBrownianReference

variable {I : Type*} (μ : ProbabilityMeasure (I → Bool))

attribute [local instance] OAI.Problem336.CanonicalBrownianReference.instMeasurableSpacePath
theorem hidden_hasLaw : HasLaw hidden (μ : Measure (I → Bool)) (law μ) :=
  BrownianReference.hidden_hasLaw (μ : Measure (I → Bool)) GlobalWiener.wienerMeasure

theorem noise_brownian (i : I) : IsBrownianReal (noise i) (law μ) :=
  BrownianReference.brownian_process (μ : Measure (I → Bool))
    GlobalWiener.wienerMeasure GlobalWiener.isBrownian_wienerMeasure i

end Problem336.CanonicalBrownianReference

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_ContinuousPathLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem336.ContinuousPathLaw

variable {I T : Type*} [TopologicalSpace T]
  [TopologicalSpace.SeparableSpace T] [Nonempty T]
  [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]
  [StandardBorelSpace C(T, ℝ)]

omit [TopologicalSpace.SeparableSpace T] [Nonempty T]
  [StandardBorelSpace C(T, ℝ)] in
lemma measurable_raw : Measurable (raw (I := I) (T := T)) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro t
  exact (show Continuous (fun x : C(T, ℝ) => x t) by fun_prop).measurable.comp
    (measurable_pi_apply i)

omit [StandardBorelSpace C(T, ℝ)] in
lemma measurable_denseEval : Measurable (denseEval (I := I) (T := T)) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro n
  exact (show Continuous (fun x : C(T, ℝ) =>
    x (TopologicalSpace.denseSeq T n)) by fun_prop).measurable.comp (measurable_pi_apply i)

omit [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]
  [StandardBorelSpace C(T, ℝ)] in
lemma denseEval_injective : Function.Injective (denseEval (I := I) (T := T)) := by
  intro x y h
  funext i
  apply DFunLike.coe_injective
  apply (TopologicalSpace.denseRange_denseSeq T).equalizer (x i).continuous (y i).continuous
  funext n
  exact congrFun (congrFun h i) n

lemma measurableEmbedding_denseEval [Countable I] :
    MeasurableEmbedding (denseEval (I := I) (T := T)) :=
  measurable_denseEval.measurableEmbedding denseEval_injective

theorem measure_eq_of_raw [Countable I] {μ ν : Measure (I → C(T, ℝ))}
    (h : μ.map raw = ν.map raw) : μ = ν := by
  let r : (I → T → ℝ) → I → ℕ → ℝ :=
    fun x i n => x i (TopologicalSpace.denseSeq T n)
  have hr : Measurable r := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro n
    exact (measurable_pi_apply (TopologicalSpace.denseSeq T n)).comp (measurable_pi_apply i)
  apply measurableEmbedding_denseEval.map_injective
  calc
    μ.map denseEval = (μ.map raw).map r := (Measure.map_map hr measurable_raw).symm
    _ = (ν.map raw).map r := congrArg (Measure.map r) h
    _ = ν.map denseEval := Measure.map_map hr measurable_raw

theorem exists_measurable_lift_of_aemeasurable [Countable I]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (U : Ω → I → T → ℝ)
    (hU : ∀ i t, AEMeasurable (fun ω => U ω i t) μ)
    (hc : ∀ᵐ ω ∂μ, ∀ i, Continuous (U ω i)) :
    ∃ X : Ω → I → C(T, ℝ), Measurable X ∧
      (fun ω => raw (X ω)) =ᵐ[μ] U := by
  classical
  let X : Ω → I → C(T, ℝ) := fun ω i =>
    if h : ∀ j, Continuous (U ω j) then ⟨U ω i, h i⟩ else 0
  have hraw : (fun ω => raw (X ω)) =ᵐ[μ] U := by
    filter_upwards [hc] with ω hω
    funext i t
    simp [X, raw, hω]
  have hd : AEMeasurable (denseEval ∘ X) μ := by
    apply aemeasurable_pi_iff.mpr
    intro i
    apply aemeasurable_pi_iff.mpr
    intro n
    apply (hU i (TopologicalSpace.denseSeq T n)).congr
    filter_upwards [hraw] with ω hω
    exact (congrFun (congrFun hω i) (TopologicalSpace.denseSeq T n)).symm
  have hX : AEMeasurable X μ :=
    measurableEmbedding_denseEval.aemeasurable_comp_iff.mp hd
  refine ⟨hX.mk X, hX.measurable_mk, ?_⟩
  filter_upwards [hX.ae_eq_mk, hraw] with ω heq hω
  rw [← heq]
  exact hω

theorem exists_measurable_lift_with_law [Countable I]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (U : Ω → I → T → ℝ)
    (hU : ∀ i t, AEMeasurable (fun ω => U ω i t) μ)
    (hc : ∀ᵐ ω ∂μ, ∀ i, Continuous (U ω i))
    {ν : Measure (I → C(T, ℝ))} (hlaw : μ.map U = ν.map raw) :
    ∃ X : Ω → I → C(T, ℝ), Measurable X ∧
      (fun ω => raw (X ω)) =ᵐ[μ] U ∧ μ.map X = ν := by
  obtain ⟨X, hX, heq⟩ := exists_measurable_lift_of_aemeasurable U hU hc
  refine ⟨X, hX, heq, measure_eq_of_raw ?_⟩
  rw [Measure.map_map measurable_raw hX]
  exact (Measure.map_congr heq).trans hlaw

end Problem336.ContinuousPathLaw

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_ContinuousPathSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.ContinuousPathSampler

variable {I : Type*}
  [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]

lemma measurable_raw_eval (i : I) :
    Measurable (fun p : (I → C(ℝ≥0, ℝ)) × ℝ≥0 =>
      ContinuousPathLaw.raw p.1 i p.2) := by
  have hm : Measurable (fun p : (I → C(ℝ≥0, ℝ)) × ℝ≥0 => (p.1 i, p.2)) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
  exact (show Continuous (fun p : C(ℝ≥0, ℝ) × ℝ≥0 => p.1 p.2) by
    fun_prop).measurable.comp hm

theorem hasLaw_of_raw_integral_coupling [Countable I]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {ρ : Measure (I → C(ℝ≥0, ℝ))} {ν : Measure (I → Bool)}
    {X : Ω → I → Bool} (hX : HasLaw X ν P)
    {B : I → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) P)
    (U : Ω → I → ℝ≥0 → ℝ)
    (hU : ∀ i t, AEMeasurable (fun ω => U ω i t) P)
    (hUc : ∀ᵐ ω ∂P, ∀ i, Continuous (U ω i))
    (hUlaw : P.map U = ρ.map ContinuousPathLaw.raw)
    {fresh : Ω' → I → C(ℝ≥0, ℝ)} (hfresh : HasLaw fresh ρ P')
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ t y z D, 0 ≤ D → (∀ j, |y j - z j| ≤ D) →
      ∀ i, |b t y i - b t z i| ≤ L * D)
    (Y : Ω → I → ℝ≥0 → ℝ)
    (hY : ∀ᵐ ω ∂P, ∀ i, Measurable (Y ω i))
    (heq : ∀ᵐ ω ∂P, ∀ (t : ℝ≥0) i,
      Y ω i t = U ω i t +
        ∫ s in (0 : ℝ)..(t : ℝ), b s (fun j => Y ω j (Real.toNNReal s)) i)
    (hobs : ∀ᵐ ω ∂P, ∀ i (n : ℕ),
      Y ω i n = (n : ℝ) * bitValue (X ω i) + B i (n : ℝ≥0) ω) :
    HasLaw (fun ω => PicardSampler.NonnegativeTime.sample
      ContinuousPathLaw.raw b (fresh ω)) ν P' := by
  obtain ⟨V, hVm, hVeq, hVlaw⟩ :=
    ContinuousPathLaw.exists_measurable_lift_with_law U hU hUc hUlaw
  have hV : HasLaw V ρ P := ⟨hVm.aemeasurable, hVlaw⟩
  apply PicardSampler.NonnegativeTime.hasLaw_of_integral_coupling hX hB hV hfresh
    ContinuousPathLaw.raw b measurable_raw_eval hb hbound hL hresponse Y
  · filter_upwards [hY] with ω hω
    exact ⟨fun i => (V ω i).continuous, hω⟩
  · filter_upwards [heq, hVeq] with ω hω hvω
    intro t i
    rw [show ContinuousPathLaw.raw (V ω) i t = U ω i t from
      congrFun (congrFun hvω i) t]
    exact hω t i
  · exact hobs

end Problem336.ContinuousPathSampler

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_RawInnovationSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem336.RawInnovationSampler

variable {I Ω : Type*}

theorem hasLaw_of_raw_innovation [Countable I]
    [MeasurableSpace Ω] {Ω' : Type*} [MeasurableSpace Ω']
    [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]
    {P : Measure Ω} {P' : Measure Ω'}
    {ρ : Measure (I → C(ℝ≥0, ℝ))} {ν : Measure (I → Bool)}
    {X : Ω → I → Bool} (hX : HasLaw X ν P)
    {B : I → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsBrownianReal (B i) P)
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (hbound : ∀ t y i, |b t y i| ≤ 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ t y z D, 0 ≤ D → (∀ j, |y j - z j| ≤ D) →
      ∀ i, |b t y i - b t z i| ≤ L * D)
    (hinnovation : HasLaw (rawInnovation X B b) (ρ.map ContinuousPathLaw.raw) P)
    {fresh : Ω' → I → C(ℝ≥0, ℝ)} (hfresh : HasLaw fresh ρ P') :
    HasLaw (fun ω => PicardSampler.NonnegativeTime.sample
      ContinuousPathLaw.raw b (fresh ω)) ν P' := by
  have hBc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => B i t ω) :=
    ae_all_iff.mpr (fun i => (hB i).cont)
  have hYc : ∀ᵐ ω ∂P, ∀ i, Continuous (observation X B ω i) := by
    filter_upwards [hBc] with ω hω
    intro i
    exact (continuous_subtype_val.mul continuous_const).add (hω i)
  have hIc : ∀ᵐ ω ∂P, ∀ i, Continuous (rawInnovation X B b ω i) := by
    filter_upwards [hYc] with ω hω
    intro i
    have hm : Measurable (fun s : ℝ =>
        b s (fun j => observation X B ω j s.toNNReal) i) :=
      (hb i).comp (measurable_id.prodMk (Measurable.of_eval (fun j => ((hω j).comp continuous_real_toNNReal).measurable)))
    have hi : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t,
        b s (fun j => observation X B ω j s.toNNReal) i) :=
      intervalIntegral.continuous_primitive
        (Picard.intervalIntegrable_of_measurable_bounded hm
          (fun s => hbound s _ i)) 0
    change Continuous (fun t => rawInnovation X B b ω i t)
    simp_rw [rawInnovation_apply]
    exact (hω i).sub (hi.comp continuous_subtype_val)
  apply ContinuousPathSampler.hasLaw_of_raw_integral_coupling hX
    (fun i => (hB i).toIsPreBrownianReal) (rawInnovation X B b)
    (fun i t => (measurable_pi_apply t).comp_aemeasurable
      ((measurable_pi_apply i).comp_aemeasurable hinnovation.aemeasurable)) hIc hinnovation.map_eq hfresh
    b hb hbound hL hresponse (observation X B)
  · filter_upwards [hYc] with ω hω
    exact fun i => (hω i).measurable
  · exact Eventually.of_forall (fun ω t i => by rw [rawInnovation_apply]; ring)
  · exact Eventually.of_forall (fun _ _ _ => rfl)

end Problem336.RawInnovationSampler

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CanonicalBrownianSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace Problem336.CanonicalBrownianSampler

attribute [local instance] OAI.Problem336.CanonicalBrownianSampler.instMeasurableSpacePath
local instance instBorelSpacePath : BorelSpace GlobalWiener.Path := ⟨rfl⟩

open CanonicalBrownianReference

variable {I : Type*} [countableIndices : Countable I]

theorem hasLaw_sample
    (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I)
    (hS : ∀ e, Monotone (S e)) (hcover : ∀ e i, ∃ n, i ∈ S e n)
    {L : ℝ} (hL : 0 ≤ L) (hresponse : PosteriorDrift.FiniteResponseBound μ S L) :
    HasLaw (PicardSampler.NonnegativeTime.sample ContinuousPathLaw.raw
      (PosteriorDrift.drift μ S)) (μ : Measure (I → Bool)) (noiseLaw I) := by
  have hfresh : HasLaw (id : (I → GlobalWiener.Path) → I → GlobalWiener.Path)
      (noiseLaw I) (noiseLaw I) := ⟨measurable_id.aemeasurable, Measure.map_id⟩
  exact RawInnovationSampler.hasLaw_of_raw_innovation (hidden_hasLaw μ)
    (noise_brownian μ) (PosteriorDrift.drift μ S)
    (PosteriorDrift.measurable_drift_coordinate μ S)
    (fun t y i => by
      have h := PosteriorDrift.drift_mem_Icc μ S t y i
      rw [abs_of_nonneg h.1]
      exact h.2) hL
    (fun t y z D hD hdiff i => PosteriorDrift.drift_response μ S hresponse
      t y z hD hdiff i) (raw_innovation_hasLaw μ S hS hcover) hfresh

end Problem336.CanonicalBrownianSampler

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

theorem sample_hasLaw {G : GraphCode}
    (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id) :
    HasLaw (PicardSampler.NonnegativeTime.sample
      (fun (W : EdgeCode → GlobalWiener.Path) e t => W e t)
      (GraphTreePosterior.drift G)) (μ : Measure EdgeConfiguration) AllPairWiener.law := by
  rw [GraphTreePosterior.drift_fun_eq_allPair_posteriorDrift_of_hasFUSFLaw hc hf hμ]
  exact CanonicalBrownianSampler.hasLaw_sample μ (AllPairObservation.observations G)
    (AllPairObservation.observations_mono G)
    (fun e f => AllPairObservation.exists_mem_observations hc hf e f)
    (L := (1 / 2 : ℝ)) (by norm_num) (hμ.finiteResponseBound hc _)

theorem worksOnGraph_oai (G : GraphCode) : WorksOnGraph rule G := by
  apply (CanonicalIID.worksOnGraph_iff_canonical rule G).mpr
  intro hc hf
  obtain ⟨μ, hμ⟩ := exists_hasFUSFLaw G hc hf
  exact FactorAssembly.canonical_hasFUSFLaw_of_sampler_hasLaw
    GraphTreePosterior.measurable_drift AllPairWiener.noise_borel G hμ
    (AllPairWiener.sampler_hasLaw_of_product GraphTreePosterior.drift G hc hf
      (sample_hasLaw hc hf hμ))

end Problem336.FinalFactor

end

end OAI
end

theorem solution : type_of% @OAI.Problem336.FinalFactor.worksOnGraph_oai := @OAI.Problem336.FinalFactor.worksOnGraph_oai
