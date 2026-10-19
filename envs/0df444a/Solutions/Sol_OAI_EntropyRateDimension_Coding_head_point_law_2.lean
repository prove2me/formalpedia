-- Prove2me | solution 2 for OAI.EntropyRateDimension.Coding.head_point_law
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:07:13.223988+00:00
-- url     : https://prove2.me/submissions/00baf214-d7c2-4367-a453-0994d517c3e8

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/CodingIntegrals.lean:L27-L53
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Coding.head_point_law. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals

-- ---- from OAI.MeasureTheory.SelfSimilar.Basic ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace System
variable {ι : Type uι} [Fintype ι]

theorem affine_continuous (S : System ι) (i : ι) : Continuous (S.affine i) := by
  unfold affine
  fun_prop

end System

namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

end System

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.Bernoulli ----
namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology

namespace EntropyRateDimension
namespace Bernoulli

variable {α : Type uα} [MeasurableSpace α]

theorem shift_measurable : Measurable (shift (α := α)) :=
  measurable_pi_iff.mpr fun n => measurable_pi_apply (n+1)

theorem shift_preserving (p : Measure α) [IsProbabilityMeasure p] :
    MeasurePreserving shift (Measure.infinitePi (fun _ : ℕ => p))
      (Measure.infinitePi (fun _ : ℕ => p)) where
  measurable := shift_measurable
  map_eq := by
    have hi : iIndepFun (fun n : ℕ => (@Function.eval ℕ (fun _ => α) n))
        (Measure.infinitePi fun _ : ℕ => p) :=
      iIndepFun_infinitePi (fun _ : ℕ => measurable_id)
    have hh := (hi.precomp Nat.succ_injective).map_fun_eq_infinitePi_map
      (fun n => measurable_pi_apply (n+1))
    change Measure.map (fun ω : ℕ → α => fun n => ω (n+1))
      (Measure.infinitePi fun _ : ℕ => p) = _
    simpa only [Measure.infinitePi_map_eval, Function.eval] using hh

theorem head_indep_tail (p : Measure α) [IsProbabilityMeasure p] :
    IndepFun (fun ω : ℕ → α => ω 0) shift (Measure.infinitePi fun _ : ℕ => p) := by
  let m : ℕ → MeasurableSpace (ℕ → α) := fun n =>
    MeasurableSpace.comap (fun ω : ℕ → α => ω n) inferInstance
  have hi : iIndep m (Measure.infinitePi fun _ : ℕ => p) :=
    iIndepFun_infinitePi (fun _ : ℕ => measurable_id)
  have h := indep_iSup_of_disjoint (fun n => (measurable_pi_apply n).comap_le) hi
    (S := {0}) (T := Set.range Nat.succ) (by
      apply Set.disjoint_left.mpr
      rintro n (hn : n = 0) ⟨k,hk⟩
      omega)
  apply indep_of_indep_of_le h
  · exact le_iSup_of_le 0 (le_iSup_of_le rfl le_rfl)
  · change MeasurableSpace.comap shift
      (⨆ k : ℕ, MeasurableSpace.comap (Function.eval k) (inferInstance : MeasurableSpace α)) ≤ _
    rw [MeasurableSpace.comap_iSup]
    apply iSup_le
    intro k
    rw [MeasurableSpace.comap_comp]
    exact le_iSup_of_le (k+1) (le_iSup_of_le ⟨k,rfl⟩ le_rfl)

theorem head_tail_law (p : Measure α) [IsProbabilityMeasure p] :
    (Measure.infinitePi fun _ : ℕ => p).map (fun ω => (ω 0,shift ω)) =
      p.prod (Measure.infinitePi fun _ : ℕ => p) := by
  rw [(head_indep_tail p).map_prod_eq_prod_map_map
    (measurable_pi_apply 0).aemeasurable shift_measurable.aemeasurable,
    Measure.infinitePi_map_eval, (shift_preserving p).map_eq]

end Bernoulli
end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.Coding ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
namespace EntropyRateDimension
namespace Coding
open Filter Set
open scoped Topology

variable {ι : Type uι} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem slope_shift (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    slope S ω (n+1) = S.ratio (ω 0) * slope S (shift ω) n := by
  simp only [slope, Finset.prod_range_succ', shift]
  ring

theorem point_shift (S : System ι) (ω : ℕ → ι) :
    point S ω = S.affine (ω 0) (point S (shift ω)) := by
  rw [point, (term_summable S ω).tsum_eq_zero_add]
  have he : (fun n => term S ω (n+1)) = fun n => S.ratio (ω 0)*term S (shift ω) n := by
    funext n
    simp only [term, slope_shift, shift]
    ring
  rw [he, tsum_mul_left]
  simp only [term, slope_zero, one_mul, System.affine, point]
  ring

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem head_tail_point_law (S : System ι) :
    (addressMeasure S).map (fun ω => (ω 0,point S (shift ω))) =
      (symbolMeasure S).prod (law S) := by
  have h := congrArg (Measure.map (Prod.map id (point S)))
    (Bernoulli.head_tail_law (symbolMeasure S))
  rw [Measure.map_map (measurable_id.prodMap (point_measurable S))
      ((measurable_pi_apply 0).prodMk Bernoulli.shift_measurable)] at h
  rw [← Measure.map_prod_map _ _ measurable_id (point_measurable S), Measure.map_id] at h
  exact h

end Coding
end EntropyRateDimension

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.CodingIntegrals ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter EntropyRateDimension.Bernoulli
open scoped Topology BigOperators ENNReal
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI
theorem head_point_law (S : System ι) :
    (addressMeasure S).map (fun ω => (ω 0,point S ω)) =
      ∑ i, (Measure.dirac i).prod (S.component (law S) i) := by
  classical
  let f : ι × ℝ → ι × ℝ := fun z => (z.1,S.affine z.1 z.2)
  have hf : Measurable f := by
    apply measurable_fst.prodMk
    exact (((measurable_of_finite S.ratio).comp measurable_fst).mul measurable_snd).add
      ((measurable_of_finite S.offset).comp measurable_fst)
  have hh := congrArg (Measure.map f) (head_tail_point_law S)
  have hp : Measurable (fun ω : ℕ → ι => (ω 0,point S (shift ω))) :=
    (measurable_pi_apply 0).prodMk ((point_measurable S).comp shift_measurable)
  rw [Measure.map_map hf hp] at hh
  have he : f ∘ (fun ω => (ω 0,point S (shift ω))) = fun ω => (ω 0,point S ω) := by
    funext ω
    exact Prod.ext rfl (point_shift S ω).symm
  rw [he] at hh
  rw [hh]
  change ((∑ i, ENNReal.ofReal (S.weight i) • Measure.dirac i).prod (law S)).map f = _
  rw [← Measure.sum_fintype,Measure.prod_sum_left,Measure.sum_fintype,
    Measure.map_finset_sum hf.aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.prod_smul_left,Measure.map_smul _ _ f,Measure.dirac_prod,
    Measure.map_map hf measurable_prodMk_left,System.component,Measure.prod_smul_right,
    Measure.dirac_prod,Measure.map_map measurable_prodMk_left (S.affine_continuous i).measurable]
  rfl

end EntropyRateDimension.Coding

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Coding
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Metric Set Filter EntropyRateDimension.Bernoulli
open scoped Topology BigOperators ENNReal
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.Coding.head_point_law.{uι} := @_root_.OAI.EntropyRateDimension.Coding.head_point_law.{uι}
