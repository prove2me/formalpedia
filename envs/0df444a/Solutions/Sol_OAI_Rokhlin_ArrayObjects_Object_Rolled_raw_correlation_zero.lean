-- Prove2me | solution 1 for OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_correlation_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:08:30.942363+00:00
-- url     : https://prove2.me/submissions/0303957b-023d-40c7-969c-547f5251299e

import Mathlib
import Definitions.Def_OAIQ3Ro002
import Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_exists_raw_finite_levels
import Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_raw_correlation_forces_coefficient
import Theorems.Thm_OAI_Rokhlin_local_moving_cancellation

section
-- module Solutions.OAIQ3_Rok.Compat
attribute [-instance] _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
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
-- module Solutions.OAIQ3_Rok.MultipleMixing_Arrays
attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.columnGroupKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.columnPairKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunArrαYOfNatNatComplexMemAddSubgroupLpENNRealSubmoduleRawSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunCellComplexMemAddSubgroupLpOfNatENNRealSubmoduleSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleColumnActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleCommonActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleRowActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatCellSlotLocal _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallCellSlotTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallYRawTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYColumnCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYRowCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.rowPairKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.splitRowKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.arrayLaw_probability _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.localLaw_probability _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section

open MeasureTheory ProbabilityTheory
universe u
namespace ArrayObjects

section

attribute [instance] InitialLaws.probability

attribute [instance] Object.probability

end


end ArrayObjects

open scoped InnerProductSpace

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

end

section
open MeasureTheory ProbabilityTheory
variable {Ω U : Type*} [MeasurableSpace Ω] [MeasurableSpace U] [MeasurableSpace.CountablyGenerated Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (u : Ω → U) (hu : Measurable u)
  (κ : Kernel U Ω) [IsMarkovKernel κ]

include hu in

lemma conditional_kernel_equivariant
    (hκ : HasCondDistrib id u κ μ) (T : Ω ≃ᵐ Ω) (S : U ≃ᵐ U)
    (hT : MeasurePreserving T μ μ) (hfactor : u ∘ T = S ∘ u) :
    κ.map T =ᵐ[μ.map u] κ.comap S S.measurable := by
  have h₁ : HasCondDistrib T (u ∘ T) κ μ := by
    refine ⟨(hu.comp T.measurable |>.prodMk T.measurable).aemeasurable,?_⟩
    have hp : μ.map (u ∘ T) = μ.map u := by
      rw [←Measure.map_map hu T.measurable,hT.map_eq]
    rw [hp]
    calc
      μ.map (fun x => (u (T x),T x)) =
          (μ.map T).map (fun x => (u x,x)) := by
        exact (Measure.map_map (μ := μ) (hu.prodMk measurable_id) T.measurable).symm
      _ = μ.map u ⊗ₘ κ := by rw [hT.map_eq]; exact hκ.map_eq
  have h₂ := h₁.measurableEquiv_comp_right S.symm
  have hc : S.symm ∘ (u ∘ T) = u := by
    rw [hfactor]
    funext x
    exact S.symm_apply_apply _
  rw [hc] at h₂
  have h₃ := hκ.comp_left T.measurable
  exact Kernel.ae_eq_of_compProd_eq (h₃.map_eq.symm.trans h₂.map_eq)
end

namespace ArrayObjects
open MeasureTheory ProbabilityTheory
universe u
variable {I Y Z : Type u} [MeasurableSpace Y] [MeasurableSpace Z]

namespace Object
variable [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T} (M : Object I base)

lemma parameterLaw_invariant (n : ℕ) :
    MeasurePreserving (amap M.timeU n) (M.parameterLaw n) (M.parameterLaw n) := by
  refine ⟨measurable_amap M.timeU.measurable n,?_⟩
  change ((M.law n).map (amap M.par n)).map (amap M.timeU n) = _
  rw [Measure.map_map (measurable_amap M.timeU.measurable _) (measurable_amap M.measurable_par _)]
  have he : amap (I := I) M.timeU n ∘ amap M.par n = amap M.par n ∘ amap M.timeY n := by
    rw [←amap_comp,←amap_comp,M.time_par]
  rw [he,←Measure.map_map (measurable_amap M.measurable_par _) (measurable_amap M.timeY.measurable _),
    (M.invariant n).map_eq]
  rfl

lemma ownKernel_time_equivariant (n : ℕ) :
    (M.ownKernel n).map (amap M.timeY n) =ᵐ[M.parameterLaw n]
      (M.ownKernel n).comap (amap M.timeU n) (measurable_amap M.timeU.measurable n) := by
  apply conditional_kernel_equivariant (M.law n) (amap M.par n)
    (measurable_amap M.measurable_par _) (M.ownKernel n) (M.ownKernel_conditional n)
    (amapEquiv M.timeY n) (amapEquiv M.timeU n) (M.invariant n)
  change amap M.par n ∘ amap M.timeY n = amap M.timeU n ∘ amap M.par n
  rw [←amap_comp,←amap_comp,M.time_par]

lemma ownKernel_time_preserving (n : ℕ) :
    ∀ᵐ p ∂M.parameterLaw n, MeasurePreserving (amap M.timeY n)
      (M.ownKernel n p) (M.ownKernel n (amap M.timeU n p)) := by
  filter_upwards [M.ownKernel_time_equivariant n] with p hp
  exact ⟨measurable_amap M.timeY.measurable n,
    (Kernel.map_apply _ (measurable_amap M.timeY.measurable n) _).symm.trans hp⟩
end Object
end ArrayObjects

open MeasureTheory ProbabilityTheory

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_ExactLines
attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.arrayLaw_probability _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.localLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory ProbabilityTheory Set

theorem ae_map_descent {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [StandardBorelSpace Ω] [StandardBorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → S} (hf : Measurable f)
    {P : S → Prop} (hP : ∀ᵐ ω ∂μ, P (f ω)) : ∀ᵐ s ∂μ.map f, P s := by
  let : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  let κ := condDistrib id f μ
  have hnull : NullMeasurableSet {ω | P (f ω)} μ := by
    exact NullMeasurableSet.congr (nullMeasurableSet_univ (μ := μ))
      (by filter_upwards [hP] with ω hω; exact propext (iff_of_true trivial hω))
  obtain ⟨t,ht,htm,hte⟩ := hnull.exists_measurable_subset_ae_eq
  have hta : ∀ᵐ ω ∂μ, ω ∈ t := by
    filter_upwards [hP,hte] with ω hω he
    exact he.mpr hω
  have hgood : ∀ᵐ s ∂μ.map f, ∀ᵐ ω ∂κ s, ω ∈ t ∧ f ω = s := by
    apply Measure.ae_ae_of_ae_compProd (p := fun p : S × Ω => p.2 ∈ t ∧ f p.2 = p.1)
    change ∀ᵐ p ∂μ.map f ⊗ₘ condDistrib id f μ, p.2 ∈ t ∧ f p.2 = p.1
    rw [compProd_map_condDistrib aemeasurable_id]
    apply (ae_map_iff (hf.prodMk measurable_id).aemeasurable
      ((htm.preimage measurable_snd).inter (measurableSet_eq_fun (hf.comp measurable_snd) measurable_fst))).mpr
    filter_upwards [hta] with ω hω
    exact ⟨hω,rfl⟩
  filter_upwards [hgood] with s hs
  obtain ⟨ω,hω,he⟩ := hs.exists
  rw [←he]
  exact ht hω
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set

universe u
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma rawTuple_time_commute : rawTuple M ∘ amap M.timeY 1 =
    (fun y : I → Arr I M.Y 0 => fun i => amap M.timeY 0 (y i)) ∘ rawTuple M := rfl

lemma rawTuple_time_preserving :
    ∀ᵐ p ∂M.parameterLaw 1,
      MeasurePreserving (fun y : I → Arr I M.Y 0 => fun i => amap M.timeY 0 (y i))
        (rawTupleKernel M p) (rawTupleKernel M (amap M.timeU 1 p)) := by
  filter_upwards [M.ownKernel_time_preserving 1] with p hp
  have htime : Measurable (fun y : I → Arr I M.Y 0 => fun i => amap M.timeY 0 (y i)) :=
    Measurable.of_eval fun i => (measurable_amap M.timeY.measurable 0).comp (measurable_pi_apply i)
  refine ⟨htime,?_⟩
  rw [rawTupleKernel,Kernel.map_apply _ (measurable_rawTuple M),
    Kernel.map_apply _ (measurable_rawTuple M),Measure.map_map htime (measurable_rawTuple M),
    ←rawTuple_time_commute M,←Measure.map_map (measurable_rawTuple M) (measurable_amap M.timeY.measurable 1),hp.map_eq]

lemma tupleParameter_time (p : Arr I M.U 1) (i : I) :
    tupleParameter M (amap M.timeU 1 p) i = amap M.timeU 0 (tupleParameter M p i) := rfl

lemma goodTuple_time_preserving
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M) :
    ∀ᵐ p ∂M.parameterLaw 1,
      MeasurePreserving (fun y : I → Arr I M.Y 0 => fun i => amap M.timeY 0 (y i))
        (Λ p) (Λ (amap M.timeU 1 p)) := by
  filter_upwards [rawTuple_time_preserving M,hL,
    (M.parameterLaw_invariant 1).quasiMeasurePreserving.ae hL] with p hp h1 h2
  rw [h1,h2]; exact hp

end ArrayObjects.Object.Rolled

section
open MeasureTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable (Y : Type*) [MeasurableSpace Y]

variable {Y} (μ : Measure Y)

lemma projectiveCircle_mul (f g : Y → Circle) (hf : Measurable f) (hg : Measurable g) :
    projectiveCircle μ (fun y => f y * g y) (hf.mul hg) =
      projectiveCircle μ f hf * projectiveCircle μ g hg := rfl

end

open MeasureTheory Set

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_FibreMeasures
attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.arrayLaw_probability _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.localLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {U Z : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Z] [StandardBorelSpace Z]

namespace BorelFibreEnumeration
variable {S : Set (U × Z)} (E : BorelFibreEnumeration S)

lemma ae_mem (ν : Measure U) : ∀ᵐ x ∂E.measure ν, x ∈ S := by
  rw [measure,E.measurableEmbedding_point.ae_map_iff]
  exact Filter.Eventually.of_forall (fun x => E.mem _ _ x.property)

end BorelFibreEnumeration
end

namespace BorelFibreEnumeration

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {P U Z : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U] [MeasurableSpace Z] [StandardBorelSpace Z]
  {S : Set (U × Z)} (E : BorelFibreEnumeration S)

lemma ae_base (ν : Measure U) [SigmaFinite ν] {P : U → Prop} (h : ∀ᵐ u ∂ν, P u) :
    ∀ᵐ x ∂E.measure ν, P x.1 := by
  rw [measure,E.measurableEmbedding_point.ae_map_iff]
  have h' : ∀ᵐ x ∂ν.prod Measure.count, P x.1 := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := (Measure.count : Measure ℕ))).ae h
  have hs : ∀ᵐ x ∂(ν.prod Measure.count).restrict E.indexDomain, P x.1 :=
    ae_restrict_of_ae h'
  rw [←map_comap_subtype_coe E.measurable_indexDomain] at hs
  exact (MeasurableEmbedding.subtype_coe E.measurable_indexDomain).ae_map_iff.mp hs

end BorelFibreEnumeration

namespace ArrayObjects.Object.Rolled

open ContinuousLinearMap MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace


universe u
variable {I : Type u} [Fintype I] [retained13 : DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

omit [DecidableEq I] in
lemma ownKernel_tuple_time_preserving : ∀ᵐ p ∂M.parameterLaw 1, ∀ i,
    MeasurePreserving (amap M.timeY 0) (M.ownKernel 0 (tupleParameter M p i))
      (M.ownKernel 0 (amap M.timeU 0 (tupleParameter M p i))) := by
  apply ae_all_iff.mpr
  intro i
  exact (show MeasurePreserving (plane 0 0 i) (M.parameterLaw 1) (M.parameterLaw 0) from
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩).quasiMeasurePreserving.ae
      (M.ownKernel_time_preserving 0)

omit [DecidableEq I] in
lemma localGraph_time_equiv (i : I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S}) :
    ∀ᵐ u ∂M.parameterLaw 0,
      ∃ e : {q // (u,q) ∈ S} ≃ {q // (amap M.timeU 0 u,q) ∈ S},
        ∀ q, (e q).val = HilbertCode.transport (amap M.timeU 0) (amapEquiv M.timeY 0) q.val := by
  have hp : ∀ᵐ p ∂M.parameterLaw 1,
      ∃ e : {q // (tupleParameter M p i,q) ∈ S} ≃
        {q // (amap M.timeU 0 (tupleParameter M p i),q) ∈ S},
        ∀ q, (e q).val = HilbertCode.transport (amap M.timeU 0) (amapEquiv M.timeY 0) q.val := by
    filter_upwards [ownKernel_tuple_time_preserving M,goodTuple_time_preserving M Λ hL,hS,
      (M.parameterLaw_invariant 1).quasiMeasurePreserving.ae hS] with p hk hΛ h1 h2
    refine ⟨localGraphTimeEquiv (M.ownKernel 0) Λ (tupleParameter M) (amapEquiv M.timeU 0)
      (amapEquiv M.timeY 0) p (amap M.timeU 1 p) (tupleParameter_time M p) hk hΛ hm S i ?_ ?_,fun _ => rfl⟩
    · intro q
      exact (Set.ext_iff.mp (h1 i) q).symm
    · intro q
      exact (Set.ext_iff.mp (h2 i) q).symm
  have hd := ae_map_descent (P := fun u =>
    ∃ e : {q // (u,q) ∈ S} ≃ {q // (amap M.timeU 0 u,q) ∈ S},
      ∀ q, (e q).val = HilbertCode.transport (amap M.timeU 0) (amapEquiv M.timeY 0) q.val)
    (M.parameterLaw 1) (measurable_plane 0 0 i) hp
  rwa [M.parameterLaw_consistent 0 0 i] at hd

end ArrayObjects.Object.Rolled

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

omit [DecidableEq I] [IsMarkovKernel Λ] in
lemma localGraph_code_properties (i : I) (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S}) :
    ∀ᵐ u ∂M.parameterLaw 0, ∀ q, (u,q) ∈ S →
      q.base = u ∧ q.IsCanonical ∧ q.IsUnimodular := by
  have hp : ∀ᵐ p ∂M.parameterLaw 1, ∀ q, (tupleParameter M p i,q) ∈ S →
      q.base = tupleParameter M p i ∧ q.IsCanonical ∧ q.IsUnimodular := by
    filter_upwards [hS] with p hp
    intro q hq
    have he : (p,q) ∈ rawLineGraph M Λ i := (Set.ext_iff.mp (hp i) q).mpr hq
    obtain ⟨a,ha,hq⟩ := he
    change a i = q at hq
    rw [←hq]
    exact ⟨ha.1 i,ha.2.1 i⟩
  have hd := ae_map_descent (P := fun u => ∀ q, (u,q) ∈ S →
    q.base = u ∧ q.IsCanonical ∧ q.IsUnimodular) (M.parameterLaw 1)
    (measurable_plane 0 0 i) hp
  rwa [M.parameterLaw_consistent 0 0 i] at hd

end ArrayObjects.Object.Rolled

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in
lemma parameterLaw_proper (n : ℕ) (J : Finset I) (hJ : J ≠ Finset.univ) :
    (M.parameterLaw (n+1)).map (planes n J) = Measure.pi (fun _ : J => M.parameterLaw n) := by
  unfold Object.parameterLaw
  rw [Measure.map_map (measurable_planes _ _) (measurable_amap M.measurable_par _)]
  have he : planes n J ∘ amap M.par (n+1) =
      (fun z : J → Arr I M.Y n => fun j => amap M.par n (z j)) ∘ planes n J := rfl
  have hg : Measurable (fun z : J → Arr I M.Y n => fun j => amap M.par n (z j)) :=
    Measurable.of_eval fun j => (measurable_amap M.measurable_par n).comp (measurable_pi_apply j)
  rw [he,←Measure.map_map hg (measurable_planes n J),M.proper n J hJ,
    Measure.pi_map_pi (fun _ => (measurable_amap M.measurable_par n).aemeasurable)]

lemma parameter_pair_preserving (hk : 3 ≤ Fintype.card I) (s t : I) (hst : s ≠ t) :
    MeasurePreserving (fun p => (tupleParameter M p s,tupleParameter M p t))
      (M.parameterLaw 1) ((M.parameterLaw 0).prod (M.parameterLaw 0)) := by
  have hJ : ({s,t} : Finset I) ≠ Finset.univ := by
    intro h
    have hcard : ({s,t} : Finset I).card = 2 := by simp [hst]
    rw [h,Finset.card_univ] at hcard
    omega
  let s' : ({s,t} : Finset I) := ⟨s,by simp⟩
  let t' : ({s,t} : Finset I) := ⟨t,by simp⟩
  have hne : s' ≠ t' := fun h => hst (congrArg Subtype.val h)
  have hi : iIndepFun (fun i : ({s,t} : Finset I) => Function.eval i)
      (Measure.pi (fun _ : ({s,t} : Finset I) => M.parameterLaw 0)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hp : MeasurePreserving (fun z : ({s,t} : Finset I) → Arr I M.U 0 => (z s',z t'))
      (Measure.pi (fun _ => M.parameterLaw 0)) ((M.parameterLaw 0).prod (M.parameterLaw 0)) := by
    refine ⟨(measurable_pi_apply _).prodMk (measurable_pi_apply _),?_⟩
    rw [(hi.indepFun hne).map_prod_eq_prod_map_map (measurable_pi_apply s').aemeasurable
      (measurable_pi_apply t').aemeasurable,
      (measurePreserving_eval (fun _ : ({s,t} : Finset I) => M.parameterLaw 0) s').map_eq,
      (measurePreserving_eval (fun _ : ({s,t} : Finset I) => M.parameterLaw 0) t').map_eq]
  exact hp.comp ⟨measurable_planes 0 {s,t},parameterLaw_proper M 0 {s,t} hJ⟩

end ArrayObjects.Object.Rolled

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_OrbitCancellation
attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.arrayLaw_probability _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.localLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U) (S : Set (U × HilbertCode κ))

omit [DecidableEq I] in
lemma localCodeEquivGroup_val (p : P) (i : I)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (hS : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} = {q | (u p i,q) ∈ S})
    (q : {q // (u p i,q) ∈ S}) :
    (localCodeEquivGroup κ Λ u S p i hm hS q).val = HilbertCode.projective (u p i) q.val := rfl

end

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] (κ : Kernel U Y) [IsMarkovKernel κ]
    (S : Set (U × HilbertCode κ)) (a b : U)
    (e : {q // (a,q) ∈ S} ≃ {q // (b,q) ∈ S})
    (F : ProjectiveCircle (κ a) ≃* ProjectiveCircle (κ b))
    (he : ∀ q, F (HilbertCode.projective a q.val) = HilbertCode.projective b (e q).val)

lemma localProjectiveTransport_val (g : localProjectiveGroup κ S a) :
    (localProjectiveTransport κ S a b e F he g).val = F g.val := rfl
end

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U) (S : Set (U × HilbertCode κ))
lemma localProjectiveMatching_code (hk : 3 ≤ Fintype.card I) (p : P)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (hind : ∀ j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Y => y t) (Λ p)) (i j : I)
    (hSi : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} = {q | (u p i,q) ∈ S})
    (hSj : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a j = q} = {q | (u p j,q) ∈ S})
    (a : I → HilbertCode κ) (ha : (p,a) ∈ exactCodeSet κ Λ u) :
    localProjectiveMatching κ Λ u S hk p hm hind i j hSi hSj
      (localCodeEquivGroup κ Λ u S p i hm hSi
        ⟨a i,(Set.ext_iff.mp hSi _).mp ⟨a,ha,rfl⟩⟩) =
    localCodeEquivGroup κ Λ u S p j hm hSj
        ⟨a j,(Set.ext_iff.mp hSj _).mp ⟨a,ha,rfl⟩⟩ := by
  let v : exactProjectiveTuples (Λ p) (fun t => κ (u p t)) :=
    ⟨fun t => HilbertCode.projective (u p t) (a t),exact_code_projective_mem κ Λ u hm ha⟩
  let ei := MonoidHom.ofInjective (exactProjectiveSlot_injective hk (Λ p) (fun t => κ (u p t)) hm hind i)
  let ej := MonoidHom.ofInjective (exactProjectiveSlot_injective hk (Λ p) (fun t => κ (u p t)) hm hind j)
  apply Subtype.ext
  change (ej (ei.symm (ei v))).val = (ej v).val
  rw [ei.symm_apply_apply]
end

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
attribute [local instance] Classical.propDecidable
variable {U Y C : Type*} [MeasurableSpace U] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] (κ : Kernel U Y) [IsMarkovKernel κ]
    (S : Set (U × HilbertCode κ))

lemma localGroupCode_equiv (a : U)
    (e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a)
    (he : ∀ q, (e q).val = HilbertCode.projective a q.val)
    (q : {q // (a,q) ∈ S}) : localGroupCode κ S a (e q) = q.val := by
  have h : ∃ r, (a,r) ∈ S ∧ HilbertCode.projective a r = (e q).val := ⟨q.val,q.property,(he q).symm⟩
  rw [localGroupCode,dite_eq_left h]
  have hh := h.choose_spec
  have heq : e ⟨h.choose,hh.1⟩ = e q := Subtype.ext ((he _).trans hh.2)
  exact congrArg Subtype.val (e.injective heq)

lemma localGroupBlock_equiv (ψ : U × HilbertCode κ → C) (a : U)
    (e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a)
    (he : ∀ q, (e q).val = HilbertCode.projective a q.val)
    (q : {q // (a,q) ∈ S}) : localGroupBlock κ S ψ a (e q) = ψ (a,q.val) := by
  unfold localGroupBlock
  rw [localGroupCode_equiv κ S a e he q]

lemma localProjectiveTransport_block (ψ : U × HilbertCode κ → C) (a b : U)
    (e : {q // (a,q) ∈ S} ≃ {q // (b,q) ∈ S})
    (F : ProjectiveCircle (κ a) ≃* ProjectiveCircle (κ b))
    (he : ∀ q, F (HilbertCode.projective a q.val) = HilbertCode.projective b (e q).val)
    (ea : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a)
    (ha : ∀ q, (ea q).val = HilbertCode.projective a q.val)
    (eb : {q // (b,q) ∈ S} ≃ localProjectiveGroup κ S b)
    (hb : ∀ q, (eb q).val = HilbertCode.projective b q.val)
    (D : C → C) (hψ : ∀ q : {q // (a,q) ∈ S}, ψ (b,(e q).val) = D (ψ (a,q.val))) :
    ∀ g, localGroupBlock κ S ψ b (localProjectiveTransport κ S a b e F he g) =
      D (localGroupBlock κ S ψ a g) := by
  intro g
  obtain ⟨q,rfl⟩ := ea.surjective g
  have hh : localProjectiveTransport κ S a b e F he (ea q) = eb (e q) := by
    apply Subtype.ext
    rw [localProjectiveTransport_val,ha,he,hb]
  rw [hh,localGroupBlock_equiv κ S ψ b eb hb,localGroupBlock_equiv κ S ψ a ea ha]
  exact hψ q

variable {P I : Type*} [MeasurableSpace P] [Fintype I] [DecidableEq I]
    (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ] (u : P → I → U)
lemma localProjectiveMatching_block (hk : 3 ≤ Fintype.card I) (p : P)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (hind : ∀ j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Y => y t) (Λ p)) (i j : I)
    (hSi : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} = {q | (u p i,q) ∈ S})
    (hSj : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a j = q} = {q | (u p j,q) ∈ S})
    (ψ : U × HilbertCode κ → C) (D : C → C)
    (hψ : ∀ a, (p,a) ∈ exactCodeSet κ Λ u → ψ (u p j,a j) = D (ψ (u p i,a i))) :
    ∀ g, localGroupBlock κ S ψ (u p j)
      (localProjectiveMatching κ Λ u S hk p hm hind i j hSi hSj g) =
      D (localGroupBlock κ S ψ (u p i) g) := by
  intro g
  let e := localCodeEquivGroup κ Λ u S p i hm hSi
  obtain ⟨q,rfl⟩ := e.surjective g
  obtain ⟨a,ha,hai⟩ := (Set.ext_iff.mp hSi _).mpr q.property
  have hq : q = ⟨a i,(Set.ext_iff.mp hSi _).mp ⟨a,ha,rfl⟩⟩ := Subtype.ext hai.symm
  subst q
  change localGroupBlock κ S ψ (u p j)
    (localProjectiveMatching κ Λ u S hk p hm hind i j hSi hSj
      (localCodeEquivGroup κ Λ u S p i hm hSi _)) = _
  rw [localProjectiveMatching_code κ Λ u S hk p hm hind i j hSi hSj a ha]
  rw [localGroupBlock_equiv κ S ψ (u p j) _ (localCodeEquivGroup_val κ Λ u S p j hm hSj)]
  rw [localGroupBlock_equiv κ S ψ (u p i) _ (localCodeEquivGroup_val κ Λ u S p i hm hSi)]
  exact hψ a ha
end

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {Y : Type*} [MeasurableSpace Y]

lemma projectiveTime_apply (E : Y ≃ᵐ Y) (μ ν : Measure Y) (hE : MeasurePreserving E μ ν)
    (f : Y → Circle) (hf : Measurable f) :
    projectiveTime E μ ν hE (projectiveCircle μ f hf) =
      projectiveCircle ν (f ∘ E.symm) (hf.comp E.symm.measurable) := rfl

namespace HilbertCode
variable {U : Type*} [MeasurableSpace U] [MeasurableSpace.CountablyGenerated Y]
  {κ : Kernel U Y} [IsMarkovKernel κ]
lemma projective_transport (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ)
    (hq : q.IsUnimodular) (hE : MeasurePreserving E (κ q.base) (κ (F q.base))) :
    projective (F q.base) (transport F E q) =
      projectiveTime E (κ q.base) (κ (F q.base)) hE (projective q.base q) := by
  rw [projective,projective,projectiveTime_apply,projectiveCircle_eq_iff]
  obtain ⟨c,hc,hr⟩ := transport_representative F E q hq hE
  let d : Circle := ⟨c,mem_sphere_zero_iff_norm.mpr hc⟩
  refine ⟨d,?_⟩
  have ht := circleRep_ae (transport F E q) (transport_unimodular F E q)
  have hs := (MeasurePreserving.symm E hE).quasiMeasurePreserving.ae_eq_comp (circleRep_ae q hq)
  filter_upwards [ht,hr,hs] with y hty hry hsy
  apply Circle.coe_injective
  exact hty.trans (hry.trans (congrArg (c * ·) hsy.symm))
end HilbertCode
end

section
open MeasureTheory Set
variable {U P B : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace P] [StandardBorelSpace P]
  (ν : Measure U) [IsProbabilityMeasure ν] (π : Measure P) [IsProbabilityMeasure π]
  (s t : P → U) (hst : MeasurePreserving (fun p => (s p,t p)) π (ν.prod ν))
  (A : U → Type*) [∀ u, Group (A u)] (block : ∀ u, A u → B) (D : B ≃ B)

include hst in

lemma exists_block_preserving_trivialization
    (h : ∀ᵐ p ∂π, ∃ e : A (s p) ≃* A (t p), ∀ a, block (t p) (e a) = D (block (s p) a)) :
    ∃ u₀ : U, ∀ᵐ u ∂ν, ∃ J : A u₀ ≃* A u, ∀ a, block u (J a) = block u₀ a := by
  have hp : ∀ᵐ z ∂ν.prod ν, ∃ e : A z.1 ≃* A z.2,
      ∀ a, block z.2 (e a) = D (block z.1 a) := by
    rw [←hst.map_eq]
    exact ae_map_descent π hst.measurable h
  obtain ⟨uS,huS⟩ := (Measure.ae_ae_of_ae_prod hp).exists
  obtain ⟨u₀,e₀,he₀⟩ := huS.exists
  refine ⟨u₀,huS.mono ?_⟩
  intro u hu
  obtain ⟨e,he⟩ := hu
  refine ⟨e₀.symm.trans e,fun a => ?_⟩
  change block u (e (e₀.symm a)) = block u₀ a
  rw [he,←he₀,e₀.apply_symm_apply]

include hst in
lemma exists_good_block_preserving_trivialization (Q : U → Prop) (hQ : ∀ᵐ u ∂ν, Q u)
    (h : ∀ᵐ p ∂π, ∃ e : A (s p) ≃* A (t p), ∀ a, block (t p) (e a) = D (block (s p) a)) :
    ∃ u₀ : U, Q u₀ ∧ ∀ᵐ u ∂ν, ∃ J : A u₀ ≃* A u, ∀ a, block u (J a) = block u₀ a := by
  obtain ⟨v,hv⟩ := exists_block_preserving_trivialization ν π s t hst A block D h
  obtain ⟨u₀,hu₀,e,he⟩ := (hQ.and hv).exists
  refine ⟨u₀,hu₀,hv.mono ?_⟩
  intro u hu
  obtain ⟨e',he'⟩ := hu
  refine ⟨e.symm.trans e',fun a => ?_⟩
  change block u (e' (e.symm a)) = _
  rw [he',←he,e.apply_symm_apply]

omit [StandardBorelSpace U] in

lemma exists_block_automorphism
    (u₀ : U) (hJ : ∀ᵐ u ∂ν, ∃ J : A u₀ ≃* A u, ∀ a, block u (J a) = block u₀ a)
    (T : U → U) (hT : MeasurePreserving T ν ν) (S : B ≃ B)
    (ht : ∀ᵐ u ∂ν, ∃ τ : A u ≃* A (T u), ∀ a, block (T u) (τ a) = S (block u a)) :
    ∃ G : A u₀ ≃* A u₀, ∀ a, block u₀ (G a) = S.symm (block u₀ a) := by
  obtain ⟨u,hu,htu,htime⟩ := (hJ.and ((hT.quasiMeasurePreserving.ae hJ).and ht)).exists
  obtain ⟨J,hJ₁⟩ := hu
  obtain ⟨J',hJ₂⟩ := htu
  obtain ⟨τ,hτ⟩ := htime
  let V : A u₀ ≃* A u₀ := J.trans (τ.trans J'.symm)
  have hV (a) : block u₀ (V a) = S (block u₀ a) := by
    change block u₀ (J'.symm (τ (J a))) = _
    rw [←hJ₂,J'.apply_symm_apply,hτ,hJ₁]
  refine ⟨V.symm,fun a => ?_⟩
  apply S.injective
  rw [S.apply_symm_apply,←hV,V.apply_symm_apply]
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})

include hm hS in
omit [DecidableEq I] in
lemma localGraph_group_equiv (i : I) :
    ∀ᵐ a ∂M.parameterLaw 0, ∃ e : {q // (a,q) ∈ S} ≃ localProjectiveGroup (M.ownKernel 0) S a,
      ∀ q, (e q).val = HilbertCode.projective a q.val := by
  have hp : ∀ᵐ p ∂M.parameterLaw 1,
      ∃ e : {q // (tupleParameter M p i,q) ∈ S} ≃
        localProjectiveGroup (M.ownKernel 0) S (tupleParameter M p i),
        ∀ q, (e q).val = HilbertCode.projective (tupleParameter M p i) q.val := by
    filter_upwards [hS] with p hp
    exact ⟨localCodeEquivGroup (M.ownKernel 0) Λ (tupleParameter M) S p i (hm p) (hp i),
      localCodeEquivGroup_val (M.ownKernel 0) Λ (tupleParameter M) S p i (hm p) (hp i)⟩
  have hd := ae_map_descent (P := fun a =>
    ∃ e : {q // (a,q) ∈ S} ≃ localProjectiveGroup (M.ownKernel 0) S a,
      ∀ q, (e q).val = HilbertCode.projective a q.val)
    (M.parameterLaw 1) (measurable_plane 0 0 i) hp
  rwa [M.parameterLaw_consistent 0 0 i] at hd

include hm hS in
lemma localGraph_matching_blocks {C : Type*} (hk : 3 ≤ Fintype.card I)
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p)) (s t : I)
    (ψ : RawLabel M → C) (D : C → C)
    (hψ : ∀ᵐ p ∂M.parameterLaw 1, ∀ a, (p,a) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) →
      ψ (tupleParameter M p t,a t) = D (ψ (tupleParameter M p s,a s))) :
    ∀ᵐ p ∂M.parameterLaw 1,
      ∃ e : localProjectiveGroup (M.ownKernel 0) S (tupleParameter M p s) ≃*
          localProjectiveGroup (M.ownKernel 0) S (tupleParameter M p t),
        ∀ g, localGroupBlock (M.ownKernel 0) S ψ (tupleParameter M p t) (e g) =
          D (localGroupBlock (M.ownKernel 0) S ψ (tupleParameter M p s) g) := by
  filter_upwards [hS,hψ] with p hp hψ
  exact ⟨localProjectiveMatching (M.ownKernel 0) Λ (tupleParameter M) S hk p (hm p) (hind p) s t (hp s) (hp t),
    localProjectiveMatching_block (M.ownKernel 0) S Λ (tupleParameter M) hk p (hm p) (hind p) s t
      (hp s) (hp t) ψ D hψ⟩

include hm hS in
omit [DecidableEq I] in
lemma localGraph_time_blocks {C : Type*} (i : I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (ψ : RawLabel M → C) (D : C → C)
    (hψ : ∀ᵐ a ∂M.parameterLaw 0, ∀ q, (a,q) ∈ S → ψ (rawLabelTime M (a,q)) = D (ψ (a,q))) :
    ∀ᵐ a ∂M.parameterLaw 0,
      ∃ τ : localProjectiveGroup (M.ownKernel 0) S a ≃*
          localProjectiveGroup (M.ownKernel 0) S (amap M.timeU 0 a),
        ∀ g, localGroupBlock (M.ownKernel 0) S ψ (amap M.timeU 0 a) (τ g) =
          D (localGroupBlock (M.ownKernel 0) S ψ a g) := by
  classical
  have heq := localGraph_group_equiv M Λ hm S hS i
  filter_upwards [localGraph_time_equiv M Λ i hL hm S hS,
    M.ownKernel_time_preserving 0,localGraph_code_properties M Λ i S hS,
    heq,(M.parameterLaw_invariant 0).quasiMeasurePreserving.ae heq,hψ]
      with a hcode htime hprop hea heb hψ
  obtain ⟨e,he⟩ := hcode
  obtain ⟨ea,ha⟩ := hea
  obtain ⟨eb,hb⟩ := heb
  let F := projectiveTime (amapEquiv M.timeY 0) (M.ownKernel 0 a)
    (M.ownKernel 0 (amap M.timeU 0 a)) htime
  have hf (q : {q // (a,q) ∈ S}) : F (HilbertCode.projective a q.val) =
      HilbertCode.projective (amap M.timeU 0 a) (e q).val := by
    rw [he]
    have hq := hprop q.val q.property
    have hh (b : Arr I M.U 0) (hb : q.val.base = b)
        (ht : MeasurePreserving (amapEquiv M.timeY 0) (M.ownKernel 0 b)
          (M.ownKernel 0 (amap M.timeU 0 b))) :
        projectiveTime (amapEquiv M.timeY 0) (M.ownKernel 0 b)
          (M.ownKernel 0 (amap M.timeU 0 b)) ht (HilbertCode.projective b q.val) =
        HilbertCode.projective (amap M.timeU 0 b)
          (HilbertCode.transport (amap M.timeU 0) (amapEquiv M.timeY 0) q.val) := by
      subst b
      exact (HilbertCode.projective_transport (amap M.timeU 0) (amapEquiv M.timeY 0)
        q.val hq.2.2 ht).symm
    exact hh a hq.1 htime
  refine ⟨localProjectiveTransport (M.ownKernel 0) S a (amap M.timeU 0 a) e F hf,?_⟩
  apply localProjectiveTransport_block (M.ownKernel 0) S ψ a (amap M.timeU 0 a) e F hf ea ha eb hb D
  intro q
  rw [he]
  exact hψ q.val q.property
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Set
variable {U Y C : Type*} [MeasurableSpace U] [StandardBorelSpace U]
    [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
    (κ : Kernel U Y) [IsMarkovKernel κ] (S : Set (U × HilbertCode κ))
    (E : BorelFibreEnumeration S)

include E in
omit [StandardBorelSpace U] in
lemma localGroup_countable (a : U)
    (e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a) :
    Countable (localProjectiveGroup κ S a) := by
  have hc : {q | (a,q) ∈ S}.Countable := by
    apply (Set.countable_range (fun n => E.section_ n a)).mono
    intro q hq
    obtain ⟨n,_,hn⟩ := E.cover a q hq
    exact ⟨n,hn⟩
  let : Countable {q // (a,q) ∈ S} := hc.to_subtype
  exact e.symm.injective.countable

omit [StandardBorelSpace U] in
lemma localGroupBlock_symm (ψ : U × HilbertCode κ → C) (a : U)
    (e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a)
    (he : ∀ q, (e q).val = HilbertCode.projective a q.val)
    (g : localProjectiveGroup κ S a) :
    localGroupBlock κ S ψ a g = ψ (a,(e.symm g).val) := by
  have h := localGroupBlock_equiv κ S ψ a e he (e.symm g)
  simpa only [e.apply_symm_apply] using h

omit [StandardBorelSpace U] in
lemma localGroupBlock_finite (ψ : U × HilbertCode κ → C) (a : U)
    (e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a)
    (he : ∀ q, (e q).val = HilbertCode.projective a q.val) (b : C)
    (hb : {q | (a,q) ∈ S ∧ ψ (a,q) = b}.Finite) :
    {g | localGroupBlock κ S ψ a g = b}.Finite := by
  apply Set.Finite.of_injOn (f := fun g => (e.symm g).val) _ _ hb
  · intro g hg
    exact ⟨(e.symm g).property,(localGroupBlock_symm κ S ψ a e he g).symm.trans hg⟩
  · intro g _ h _ heq
    exact e.symm.injective (Subtype.ext heq)

variable (ν : Measure U) [IsProbabilityMeasure ν] (ψ : U × HilbertCode κ → C)
    (a₀ : U)
    (hJ : ∀ᵐ a ∂ν, ∃ J : localProjectiveGroup κ S a₀ ≃* localProjectiveGroup κ S a,
      ∀ g, localGroupBlock κ S ψ a (J g) = localGroupBlock κ S ψ a₀ g)
    (he : ∀ᵐ a ∂ν, ∃ e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a,
      ∀ q, (e q).val = HilbertCode.projective a q.val)

include hJ he in
lemma localGroupBlock_nonempty (b : positiveLevels (E.measure ν) ψ) :
    {g | localGroupBlock κ S ψ a₀ g = b.val}.Nonempty := by
  by_contra hn
  have hz : ∀ᵐ z ∂E.measure ν, ψ z ≠ b.val := by
    filter_upwards [E.ae_mem ν,E.ae_base ν hJ,E.ae_base ν he] with z hz hj he
    obtain ⟨J,hj⟩ := hj
    obtain ⟨e,he⟩ := he
    intro hzb
    apply hn
    refine ⟨J.symm (e ⟨z.2,hz⟩),?_⟩
    change localGroupBlock κ S ψ a₀ (J.symm (e ⟨z.2,hz⟩)) = b.val
    rw [←hj,J.apply_symm_apply,localGroupBlock_equiv κ S ψ z.1 e he]
    exact hzb
  exact b.property (by simpa only [ae_iff,not_not] using hz)
end

section
open MeasureTheory ProbabilityTheory Set
variable {U Y C : Type*} [MeasurableSpace U] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (κ : Kernel U Y) [IsMarkovKernel κ] (S : Set (U × HilbertCode κ))
    (ψ : U × HilbertCode κ → C)

lemma localBlock_card_le (a₀ a : U) (b : C)
    (hb : {g : localProjectiveGroup κ S a₀ | localGroupBlock κ S ψ a₀ g = b}.Finite)
    (J : localProjectiveGroup κ S a₀ ≃* localProjectiveGroup κ S a)
    (hJ : ∀ g, localGroupBlock κ S ψ a (J g) = localGroupBlock κ S ψ a₀ g)
    (e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a)
    (he : ∀ q, (e q).val = HilbertCode.projective a q.val) :
    ∃ h : {q | (a,q) ∈ S ∧ ψ (a,q) = b}.Finite, h.toFinset.card ≤ hb.toFinset.card := by
  classical
  let A : Set (HilbertCode κ) := {q | (a,q) ∈ S ∧ ψ (a,q) = b}
  let B : Set (localProjectiveGroup κ S a₀) := {g | localGroupBlock κ S ψ a₀ g = b}
  let map : A → B := fun q => ⟨J.symm (e ⟨q.val,q.property.1⟩),by
    change localGroupBlock κ S ψ a₀ (J.symm (e ⟨q.val,q.property.1⟩)) = b
    rw [←hJ,J.apply_symm_apply,localGroupBlock_equiv κ S ψ a e he]
    exact q.property.2⟩
  have hi : Function.Injective map := by
    intro q r h
    have h' := J.symm.injective (congrArg Subtype.val h)
    have hh : (⟨q.val,q.property.1⟩ : {q // (a,q) ∈ S}) = ⟨r.val,r.property.1⟩ := e.injective h'
    exact Subtype.ext (Subtype.mk.inj hh)
  let : Finite B := hb.to_subtype
  let : Finite A := Finite.of_injective map hi
  have hf : A.Finite := Set.toFinite A
  refine ⟨hf,?_⟩
  have h := Nat.card_le_card_of_injective map hi
  change A.ncard ≤ B.ncard at h
  rw [Set.ncard_eq_toFinset_card A hf,Set.ncard_eq_toFinset_card B hb] at h
  exact h
end

namespace ArrayObjects.Object.Rolled

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

section FiniteBlocks
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (s t : I) (hst : s ≠ t)

include hM hk hL hm hind hS Eπ Eσ hst in
lemma exists_raw_finite_blocks :
    ∃ (ψ : RawLabel M → LabelOrbitVector) (a₀ : Arr I M.U 0),
      Measurable ψ ∧
      (positiveLevels (E.measure (M.parameterLaw 0)) ψ).Countable ∧
      Countable (localProjectiveGroup (M.ownKernel 0) S a₀) ∧
      (∀ g : localProjectiveGroup (M.ownKernel 0) S a₀,
        localGroupBlock (M.ownKernel 0) S ψ a₀ g ∈ positiveLevels (E.measure (M.parameterLaw 0)) ψ) ∧
      (∀ b : positiveLevels (E.measure (M.parameterLaw 0)) ψ,
        {g | localGroupBlock (M.ownKernel 0) S ψ a₀ g = b.val}.Finite ∧
        {g | localGroupBlock (M.ownKernel 0) S ψ a₀ g = b.val}.Nonempty) ∧
      (∀ᵐ a ∂M.parameterLaw 0,
        ∃ J : localProjectiveGroup (M.ownKernel 0) S a₀ ≃* localProjectiveGroup (M.ownKernel 0) S a,
          ∀ g, localGroupBlock (M.ownKernel 0) S ψ a (J g) = localGroupBlock (M.ownKernel 0) S ψ a₀ g) ∧
      (∃ G : localProjectiveGroup (M.ownKernel 0) S a₀ ≃* localProjectiveGroup (M.ownKernel 0) S a₀,
        ∀ g, localGroupBlock (M.ownKernel 0) S ψ a₀ (G g) =
          labelShiftSecond.symm (localGroupBlock (M.ownKernel 0) S ψ a₀ g)) ∧
      (∀ᵐ a ∂M.parameterLaw 0, ∀ b : positiveLevels (E.measure (M.parameterLaw 0)) ψ,
        {q | (a,q) ∈ S ∧ ψ (a,q) = b.val}.Finite) ∧
      (∀ᵐ a ∂M.parameterLaw 0, ∀ q, (a,q) ∈ S →
        ψ (a,q) ∈ positiveLevels (E.measure (M.parameterLaw 0)) ψ) ∧
      (∀ᵐ a ∂M.parameterLaw 0, ∀ q, (a,q) ∈ S →
        ψ (rawLabelTime M (a,q)) = labelShiftSecond (ψ (a,q))) := by
  obtain ⟨ψ,hψ,hBc,hpos,hfinite,hfib,hD,hV,htr,ht⟩ :=
    exists_raw_finite_levels M Λ hM hk hL hm hind S hS E Eπ Eσ s t hst
  let A : Arr I M.U 0 → Type _ := fun a => localProjectiveGroup (M.ownKernel 0) S a
  let block := localGroupBlock (M.ownKernel 0) S ψ
  have heq := localGraph_group_equiv M Λ hm S hS s
  let Q : Arr I M.U 0 → Prop := fun a =>
    (∃ e : {q // (a,q) ∈ S} ≃ A a, ∀ q, (e q).val = HilbertCode.projective a q.val) ∧
    (∀ q, (a,q) ∈ S → ψ (a,q) ∈ positiveLevels (E.measure (M.parameterLaw 0)) ψ) ∧
    (∀ b : positiveLevels (E.measure (M.parameterLaw 0)) ψ,
      {q | (a,q) ∈ S ∧ ψ (a,q) = b.val}.Finite)
  have hQ : ∀ᵐ a ∂M.parameterLaw 0, Q a := heq.and (hpos.and hfib)
  obtain ⟨a₀,ha₀,hJ⟩ := exists_good_block_preserving_trivialization
    (M.parameterLaw 0) (M.parameterLaw 1) (fun p => tupleParameter M p s) (fun p => tupleParameter M p t)
    (parameter_pair_preserving M hk s t hst) A block labelShiftFirst.toEquiv Q hQ
    (localGraph_matching_blocks M Λ hm S hS hk hind s t ψ labelShiftFirst htr)
  obtain ⟨e,he⟩ := ha₀.1
  refine ⟨ψ,a₀,hψ,hBc,localGroup_countable (M.ownKernel 0) S E a₀ e,?_,?_,hJ,?_,hfib,hpos,ht⟩
  · intro g
    rw [localGroupBlock_symm (M.ownKernel 0) S ψ a₀ e he]
    exact ha₀.2.1 _ (e.symm g).property
  · intro b
    exact ⟨localGroupBlock_finite (M.ownKernel 0) S ψ a₀ e he b.val (ha₀.2.2 b),
      localGroupBlock_nonempty (M.ownKernel 0) S E (M.parameterLaw 0) ψ a₀ hJ heq b⟩
  · exact exists_block_automorphism (M.parameterLaw 0) A block a₀ hJ
      (amap M.timeU 0) (M.parameterLaw_invariant 0) labelShiftSecond.toEquiv
      (localGraph_time_blocks M Λ hm S hS s hL ψ labelShiftSecond ht)
end FiniteBlocks


attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
end ArrayObjects.Object.Rolled

section
open MeasureTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)

lemma projectiveRep_class (g : ProjectiveCircle μ) :
    projectiveCircle μ (projectiveRep μ g) (measurableCircle_measurable Y _) = g := by
  by_cases hg : g = 1
  · subst g
    simp only [projectiveRep]
    exact projectiveCircle_one μ
  · rw [projectiveRep,ite_eq_right hg]
    exact Quotient.out_eq g

lemma projectiveRep_one : projectiveRep μ 1 = 1 := by simp [projectiveRep]

lemma projectiveCharacter_measurable (g : ProjectiveCircle μ) :
    Measurable (projectiveCharacter μ g) :=
  measurable_subtype_coe.comp (measurableCircle_measurable Y _)

lemma projectiveCharacter_mul (g h : ProjectiveCircle μ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      (fun y => projectiveCharacter μ g y * projectiveCharacter μ h y) =ᵐ[μ]
        fun y => c * projectiveCharacter μ (g*h) y := by
  have he : projectiveCircle μ (fun y => projectiveRep μ g y * projectiveRep μ h y)
      ((measurableCircle_measurable Y _).mul (measurableCircle_measurable Y _)) =
      projectiveCircle μ (projectiveRep μ (g*h)) (measurableCircle_measurable Y _) := by
    rw [projectiveCircle_mul _ _ _ (measurableCircle_measurable Y _)
      (measurableCircle_measurable Y _),projectiveRep_class,projectiveRep_class,projectiveRep_class]
  obtain ⟨c,hc⟩ := (projectiveCircle_eq_iff μ _ _ _ _).mp he
  refine ⟨(c : ℂ),Circle.norm_coe c,?_⟩
  filter_upwards [hc] with y hy
  exact congrArg (fun c : Circle => (c : ℂ)) hy

lemma projectiveCharacters_of_zero_mean (L : Subgroup (ProjectiveCircle μ))
    (hm : ∀ g : L, g ≠ 1 → ∫ y, projectiveCharacter μ g.val y ∂μ = 0) :
    ProjectiveCharacters μ (fun g : Additive L => projectiveCharacter μ g.toMul.val) where
  measurable g := (projectiveCharacter_measurable μ _).aestronglyMeasurable
  modulus _ := Filter.Eventually.of_forall fun _ => Circle.norm_coe _
  zero := Filter.Eventually.of_forall fun _ => by
    change (projectiveRep μ 1 _ : ℂ) = 1
    rw [projectiveRep_one]; rfl
  mul g h := projectiveCharacter_mul μ g.toMul.val h.toMul.val
  mean g hg := hm g.toMul hg
end

section
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] (κ : Kernel U Y) [IsMarkovKernel κ]

lemma measurable_absoluteCoefficient (f : Y → ℂ) (hf : Measurable f) :
    Measurable (absoluteCoefficient κ f) := by
  have hm : Measurable (fun p : (U × HilbertCode κ) × Y => (p.1.2,p.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hrep : Measurable (fun p : (U × HilbertCode κ) × Y =>
      HilbertCode.representative (κ := κ) (p.1.2,p.2)) :=
    (HilbertCode.measurable_representative (κ := κ)).comp hm
  have hr : Measurable (fun p : (U × HilbertCode κ) × Y =>
      (HilbertCode.circleRep p.1.2 p.2 : ℂ)) :=
    measurable_subtype_coe.comp (measurable_circleOfValue.comp hrep)
  exact ((hf.comp measurable_snd).mul (continuous_star.measurable.comp hr)).stronglyMeasurable.integral_kernel_prod_right
    (κ := κ.comap Prod.fst measurable_fst) |>.norm.measurable

lemma absoluteCoefficient_nonneg (f : Y → ℂ) (z : U × HilbertCode κ) :
    0 ≤ absoluteCoefficient κ f z := norm_nonneg _

lemma absoluteCoefficient_le (f : Y → ℂ) (C : ℝ) (z : U × HilbertCode κ)
    (hf : ∀ᵐ y ∂κ z.1, ‖f y‖ ≤ C) : absoluteCoefficient κ f z ≤ C := by
  have hb : ∀ᵐ y ∂κ z.1, ‖f y * conj (HilbertCode.circleRep z.2 y : ℂ)‖ ≤ C := by
    filter_upwards [hf] with y hy
    simpa only [norm_mul,Complex.norm_conj,Circle.norm_coe,mul_one] using hy
  simpa [absoluteCoefficient, Measure.real] using
    norm_integral_le_of_norm_le_const hb

omit [MeasurableSpace.CountablyGenerated Y] in
lemma norm_integral_mul_conj_of_phase {μ : Measure Y} (f g h : Y → ℂ) (c : ℂ)
    (hc : ‖c‖ = 1) (he : g =ᵐ[μ] fun y => c * h y) :
    ‖∫ y, f y * conj (g y) ∂μ‖ = ‖∫ y, f y * conj (h y) ∂μ‖ := by
  have ht : (fun y => f y * conj (g y)) =ᵐ[μ]
      fun y => conj c * (f y * conj (h y)) := he.mono fun y hy => by
    dsimp only at hy ⊢
    rw [hy,map_mul]; ring
  rw [integral_congr_ae ht,integral_const_mul,norm_mul,Complex.norm_conj,hc,one_mul]

end

namespace BorelFibreEnumeration
open MeasureTheory Set
open scoped BigOperators

section
attribute [local instance] Classical.propDecidable
variable {U Z W : Type*} [MeasurableSpace U] [MeasurableSpace Z] [MeasurableSpace W]
variable {S : Set (U × Z)} (E : BorelFibreEnumeration S)

lemma measurable_fibreSum (F : U × Z → ℝ) (hF : Measurable F) :
    Measurable (E.fibreSum F) := by
  apply Measurable.tsum
  intro n
  exact Measurable.ite (E.measurable_domain n)
    (hF.comp (measurable_id.prodMk (E.measurable_section n))) measurable_const

lemma fibreSum_eq_tsum (F : U × Z → ℝ) (a : U) :
    E.fibreSum F a = ∑' z : {z : Z // (a,z) ∈ S}, F (a,z.val) := by
  rw [fibreSum,←(E.sumFibreEquiv a).tsum_eq]
  exact (tsum_subtype {n | a ∈ E.domain n} (fun n => F (a,E.section_ n a))).symm

lemma fibreSum_eq_finite_sum (F : U × Z → ℝ) (a : U) (h : {z | (a,z) ∈ S}.Finite) :
    E.fibreSum F a = ∑ z ∈ h.toFinset, F (a,z) := by
  rw [E.fibreSum_eq_tsum]
  let : Fintype {z : Z // (a,z) ∈ S} := h.fintype
  rw [tsum_fintype]
  exact (Finset.sum_subtype h.toFinset (fun z => h.mem_toFinset (a := z)) (fun z => F (a,z))).symm

lemma fibreSum_nonneg (F : U × Z → ℝ) (hF : ∀ z, 0 ≤ F z) (a : U) :
    0 ≤ E.fibreSum F a := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact hF _
  · exact le_rfl

lemma fibreSum_eq_zero_iff (F : U × Z → ℝ) (hF : ∀ z, 0 ≤ F z)
    (a : U) (h : {z | (a,z) ∈ S}.Finite) :
    E.fibreSum F a = 0 ↔ ∀ z, (a,z) ∈ S → F (a,z) = 0 := by
  rw [E.fibreSum_eq_finite_sum F a h,Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hF (a,z))]
  simp only [h.mem_toFinset,Set.mem_ofPred_eq]

variable {R : Set (U × W)} (D : BorelFibreEnumeration R)
lemma fibreSum_transport (a b : U) (e : {z : Z // (a,z) ∈ S} ≃ {w : W // (b,w) ∈ R})
    (F : U × Z → ℝ) (G : U × W → ℝ)
    (he : ∀ z, F (a,z.val) = G (b,(e z).val)) : E.fibreSum F a = D.fibreSum G b := by
  rw [E.fibreSum_eq_tsum,D.fibreSum_eq_tsum,←e.tsum_eq]
  exact tsum_congr he

end

variable {U Z C : Type*} [MeasurableSpace U] [MeasurableSpace Z]
  [MeasurableSpace C] [MeasurableSingletonClass C]
  {S : Set (U × Z)} (E : BorelFibreEnumeration S)

lemma fibreSum_le_card_mul (F : U × Z → ℝ) (c : ℝ) (a : U)
    (h : {z | (a,z) ∈ S}.Finite) (hF : ∀ z, (a,z) ∈ S → F (a,z) ≤ c) :
    E.fibreSum F a ≤ h.toFinset.card * c := by
  rw [E.fibreSum_eq_finite_sum F a h]
  calc
    _ ≤ ∑ _z ∈ h.toFinset, c := Finset.sum_le_sum fun z hz => hF z (h.mem_toFinset.mp hz)
    _ = _ := by simp

lemma exists_positive_block (ν : Measure U) [IsFiniteMeasure ν]
    (ψ : U × Z → C) (hψ : Measurable ψ) (B : Set C) (hB : B.Countable)
    (F : U × Z → ℝ) (hF : Measurable F) (hF0 : ∀ z, 0 ≤ F z)
    (c : ℝ) (hc : 0 ≤ c) (hFc : ∀ z, F z ≤ c)
    (hcover : ∀ᵐ a ∂ν, ∀ z, (a,z) ∈ S → ψ (a,z) ∈ B)
    (hfinite : ∀ b ∈ B, ∃ N : ℕ, ∀ᵐ a ∂ν,
      ∃ h : {z | (a,z) ∈ S ∧ ψ (a,z) = b}.Finite, h.toFinset.card ≤ N)
    (hn : ¬ (∀ᵐ a ∂ν, ∀ z, (a,z) ∈ S → F (a,z) = 0)) :
    ∃ b ∈ B, 0 < ∫ a, (E.restrictLevel ψ hψ b).fibreSum F a ∂ν := by
  classical
  let : Countable B := hB.to_subtype
  by_contra hh
  have hz (b : B) : ∀ᵐ a ∂ν, (E.restrictLevel ψ hψ b.val).fibreSum F a = 0 := by
    obtain ⟨N,hN⟩ := hfinite b.val b.property
    have h0 : ∀ a, 0 ≤ (E.restrictLevel ψ hψ b.val).fibreSum F a :=
      (E.restrictLevel ψ hψ b.val).fibreSum_nonneg F hF0
    have hi : Integrable ((E.restrictLevel ψ hψ b.val).fibreSum F) ν := by
      apply Integrable.mono' (integrable_const ((N : ℝ) * c))
        ((E.restrictLevel ψ hψ b.val).measurable_fibreSum F hF).aestronglyMeasurable
      filter_upwards [hN] with a ha
      obtain ⟨h,hcard⟩ := ha
      rw [Real.norm_eq_abs,abs_of_nonneg (h0 a)]
      exact ((E.restrictLevel ψ hψ b.val).fibreSum_le_card_mul F c a h
        (fun z _ => hFc (a,z))).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hc)
    have he : ∫ a, (E.restrictLevel ψ hψ b.val).fibreSum F a ∂ν = 0 := by
      apply le_antisymm
      · exact not_lt.mp (fun h => hh ⟨b.val,b.property,h⟩)
      · exact integral_nonneg h0
    exact (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall h0) hi).mp he
  apply hn
  have hf (b : B) : ∀ᵐ a ∂ν, {z | (a,z) ∈ S ∧ ψ (a,z) = b.val}.Finite := by
    obtain ⟨N,hN⟩ := hfinite b.val b.property
    exact hN.mono fun a ha => ha.choose
  filter_upwards [hcover,ae_all_iff.mpr hz,ae_all_iff.mpr hf] with a ha hz hf
  intro z hzS
  let b : B := ⟨ψ (a,z),ha z hzS⟩
  exact ((E.restrictLevel ψ hψ b.val).fibreSum_eq_zero_iff F hF0 a (hf b)).mp
    (hz b) z ⟨hzS,rfl⟩

end BorelFibreEnumeration

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

variable (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (s t : I) (hst : s ≠ t)

include hM hk hL hm hind hS Eπ Eσ hst in
lemma exists_positive_raw_block (i : I) (f : I → Arr I M.Y 0 → ℂ)
    (hf : ∀ j, Measurable (f j)) (hb : ∀ j y, ‖f j y‖ ≤ 1)
    (hpos : (∫ y, ∏ j, f j (plane 0 0 j y) ∂M.law 1) ≠ 0) :
    Nonempty (PositiveRawBlock M S E (f i)) := by
  obtain ⟨ψ,a₀,hψ,hBc,hcount,hall,hfinite,hJ,⟨G,hG⟩,hfib,hcover,ht⟩ :=
    exists_raw_finite_blocks M Λ hM hk hL hm hind S hS E Eπ Eσ s t hst
  have he := localGraph_group_equiv M Λ hm S hS i
  have hfin : ∀ b ∈ positiveLevels (E.measure (M.parameterLaw 0)) ψ, ∃ N : ℕ,
      ∀ᵐ a ∂M.parameterLaw 0,
      ∃ h : {q | (a,q) ∈ S ∧ ψ (a,q) = b}.Finite, h.toFinset.card ≤ N := by
    intro b hb
    have hB := (hfinite ⟨b,hb⟩).1
    refine ⟨hB.toFinset.card,?_⟩
    filter_upwards [he,hJ] with a he hJ
    obtain ⟨e,he⟩ := he
    obtain ⟨J,hJ⟩ := hJ
    exact localBlock_card_le (M.ownKernel 0) S ψ a₀ a b hB J hJ e he
  have hh := E.exists_positive_block (M.parameterLaw 0) ψ hψ
    (positiveLevels (E.measure (M.parameterLaw 0)) ψ) hBc
    (absoluteCoefficient (M.ownKernel 0) (f i))
    (measurable_absoluteCoefficient (M.ownKernel 0) (f i) (hf i))
    (absoluteCoefficient_nonneg (M.ownKernel 0) (f i)) 1 zero_le_one
    (fun z => absoluteCoefficient_le _ _ 1 z (Filter.Eventually.of_forall (hb i)))
    hcover hfin (raw_correlation_forces_coefficient M Λ hM hk hL hm S hS i f hf hb hpos)
  obtain ⟨b,hb,hpos⟩ := hh
  exact ⟨⟨ψ,hψ,a₀,b,(hfinite ⟨b,hb⟩).1,G,hG,hJ,ht,hpos⟩⟩
end ArrayObjects.Object.Rolled

section
open MeasureTheory Set
variable {U Z C : Type*} [MeasurableSpace U] [MeasurableSpace Z]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    {S : Set (U × Z)} (E : BorelFibreEnumeration S)
    (ψ : U × Z → C) (hψ : Measurable ψ)

lemma fibreLevelSum_transport (a b : U) (e : {z // (a,z) ∈ S} ≃ {z // (b,z) ∈ S})
    (D : C ≃ C) (he : ∀ z, ψ (b,(e z).val) = D (ψ (a,z.val))) (c : C)
    (F G : U × Z → ℝ) (hFG : ∀ z, F (a,z.val) = G (b,(e z).val)) :
    (E.restrictLevel ψ hψ (D.symm c)).fibreSum F a =
      (E.restrictLevel ψ hψ c).fibreSum G b := by
  apply BorelFibreEnumeration.fibreSum_transport _ _ a b (fibreLevelEquiv ψ a b e D he c)
  intro z
  exact hFG ⟨z.val,z.property.1⟩
end

section
open MeasureTheory Set Filter
open scoped Topology
variable {U Z C : Type*} [MeasurableSpace U] [MeasurableSpace Z]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    {S : Set (U × Z)} (E : BorelFibreEnumeration S)
    (ψ : U × Z → C) (hψ : Measurable ψ) (D : C ≃ C) (b : C)
    (F : ℕ → U × Z → ℝ)

lemma measurable_movingFibreSum (hm : ∀ n, Measurable (F n)) (n : ℕ) :
    Measurable (movingFibreSum E ψ hψ D b F n) :=
  (E.restrictLevel ψ hψ _).measurable_fibreSum _ (hm n)

variable (ν : Measure U) (T : U → U) (hT : MeasurePreserving T ν ν)
lemma movingFibreSum_step
    (h : ∀ᵐ a ∂ν, ∃ e : {z // (a,z) ∈ S} ≃ {z // (T a,z) ∈ S},
      (∀ z, ψ (T a,(e z).val) = D (ψ (a,z.val))) ∧
      (∀ n z, F (n+1) (a,z.val) = F n (T a,(e z).val))) (n : ℕ) :
    movingFibreSum E ψ hψ D b F (n+1) =ᵐ[ν]
      (movingFibreSum E ψ hψ D b F n) ∘ T := by
  filter_upwards [h] with a ha
  obtain ⟨e,he,hF⟩ := ha
  change (E.restrictLevel ψ hψ _).fibreSum _ a = (E.restrictLevel ψ hψ _).fibreSum _ (T a)
  rw [Function.iterate_succ_apply']
  exact fibreLevelSum_transport E ψ hψ a (T a) e D he _ _ _ (hF n)

include hT in
lemma movingFibreSum_iterate
    (hstep : ∀ n, movingFibreSum E ψ hψ D b F (n+1) =ᵐ[ν]
      (movingFibreSum E ψ hψ D b F n) ∘ T) (n : ℕ) :
    movingFibreSum E ψ hψ D b F n =ᵐ[ν]
      (movingFibreSum E ψ hψ D b F 0) ∘ T^[n] := by
  induction n with
  | zero => exact Eventually.of_forall fun _ => rfl
  | succ n ih =>
    filter_upwards [hstep n,hT.quasiMeasurePreserving.ae_eq_comp ih] with a h1 h2
    exact h1.trans h2

include hT in
lemma movingFibreSum_integral [IsFiniteMeasure ν]
    (hm : ∀ n, Measurable (F n))
    (hstep : ∀ n, movingFibreSum E ψ hψ D b F (n+1) =ᵐ[ν]
      (movingFibreSum E ψ hψ D b F n) ∘ T) (n : ℕ) :
    ∫ a, movingFibreSum E ψ hψ D b F n a ∂ν =
      ∫ a, movingFibreSum E ψ hψ D b F 0 a ∂ν := by
  rw [integral_congr_ae (movingFibreSum_iterate E ψ hψ D b F ν T hT hstep n)]
  have hmap := integral_map (hT.iterate n).measurable.aemeasurable
    ((measurable_movingFibreSum E ψ hψ D b F hm 0).aestronglyMeasurable (μ := ν.map (T^[n])))
  rw [(hT.iterate n).map_eq] at hmap
  exact hmap.symm

include hT in
lemma movingFibreSum_bound
    (hstep : ∀ n, movingFibreSum E ψ hψ D b F (n+1) =ᵐ[ν]
      (movingFibreSum E ψ hψ D b F n) ∘ T) (c : ℝ)
    (hb : ∀ᵐ a ∂ν, 0 ≤ movingFibreSum E ψ hψ D b F 0 a ∧
      movingFibreSum E ψ hψ D b F 0 a ≤ c) (n : ℕ) :
    ∀ᵐ a ∂ν, 0 ≤ movingFibreSum E ψ hψ D b F n a ∧ movingFibreSum E ψ hψ D b F n a ≤ c := by
  filter_upwards [movingFibreSum_iterate E ψ hψ D b F ν T hT hstep n,
    (hT.iterate n).quasiMeasurePreserving.ae hb] with a he ha
  rwa [he]
end

section
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] (κ : Kernel U Y) [IsMarkovKernel κ]
lemma absoluteCoefficient_transport (F : U → U) (E : Y ≃ᵐ Y)
    (f : Y → ℂ) (q : HilbertCode κ) (hq : q.IsUnimodular)
    (hE : MeasurePreserving E (κ q.base) (κ (F q.base))) :
    absoluteCoefficient κ f (F q.base,HilbertCode.transport F E q) =
      absoluteCoefficient κ (f ∘ E) (q.base,q) := by
  obtain ⟨d,hd,hr⟩ := HilbertCode.transport_representative F E q hq hE
  have ht := HilbertCode.circleRep_ae (HilbertCode.transport F E q)
    (HilbertCode.transport_unimodular F E q)
  have hs := (MeasurePreserving.symm E hE).quasiMeasurePreserving.ae_eq_comp (HilbertCode.circleRep_ae q hq)
  have he : (fun y => (HilbertCode.circleRep (HilbertCode.transport F E q) y : ℂ)) =ᵐ[κ (F q.base)]
      fun y => d * (HilbertCode.circleRep q (E.symm y) : ℂ) := by
    filter_upwards [ht,hr,hs] with y h1 h2 h3
    exact h1.trans (h2.trans (congrArg (d * ·) h3.symm))
  rw [absoluteCoefficient,norm_integral_mul_conj_of_phase _ _ _ d hd he]
  rw [←hE.integral_comp E.measurableEmbedding (fun y => f y * conj (HilbertCode.circleRep q (E.symm y) : ℂ))]
  simp only [E.symm_apply_apply,absoluteCoefficient,Function.comp_apply]
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [retained14 : DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (i : I) (E : BorelFibreEnumeration S)
    (ψ : RawLabel M → LabelOrbitVector) (hψ : Measurable ψ)
    (ht : ∀ᵐ a ∂M.parameterLaw 0, ∀ q, (a,q) ∈ S →
      ψ (rawLabelTime M (a,q)) = labelShiftSecond (ψ (a,q)))

include hL hm hS ht i in
include retained14 in
lemma raw_moving_sum_step (b : LabelOrbitVector) (f : Arr I M.Y 0 → ℂ) (n : ℕ) :
    movingFibreSum E ψ hψ labelShiftSecond.toEquiv b
      (fun n => absoluteCoefficient (M.ownKernel 0) (f ∘ (amap M.timeY 0)^[n])) (n+1) =ᵐ[M.parameterLaw 0]
      (movingFibreSum E ψ hψ labelShiftSecond.toEquiv b
        (fun n => absoluteCoefficient (M.ownKernel 0) (f ∘ (amap M.timeY 0)^[n])) n) ∘ amap M.timeU 0 := by
  let _ := retained14
  apply movingFibreSum_step
  filter_upwards [localGraph_time_equiv M Λ i hL hm S hS,
    localGraph_code_properties M Λ i S hS, M.ownKernel_time_preserving 0,ht] with a he hq htime ht
  obtain ⟨e,he⟩ := he
  refine ⟨e,?_,?_⟩
  · intro q
    rw [he]
    exact ht q q.property
  · intro n q
    rw [he]
    obtain ⟨hb,_,hu⟩ := hq q q.property
    have H := absoluteCoefficient_transport (M.ownKernel 0) (amap M.timeU 0)
      (amapEquiv M.timeY 0) (f ∘ (amap M.timeY 0)^[n]) q.val hu (by rw [hb]; exact htime)
    rw [hb] at H
    rw [H]
    congr 1
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {Y I : Type*} [MeasurableSpace Y] [Fintype I] [DecidableEq I]
lemma exactCircleTuples_mean_zero (hk : 3 ≤ Fintype.card I)
    (μ : Measure (I → Y)) [IsProbabilityMeasure μ] (ν : I → Measure Y)
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) μ (ν i))
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) μ)
    (f : I → MeasurableCircle Y) (hf : f ∈ exactCircleTuples μ)
    (i : I) (hi : projectiveCircle (ν i) (f i) (measurableCircle_measurable Y (f i)) ≠ 1) :
    ∫ y, (f i y : ℂ) ∂ν i = 0 := by
  have hfm (j : I) : Measurable (fun y : Y => (f j y : ℂ)) :=
    measurable_subtype_coe.comp (measurableCircle_measurable Y (f j))
  have hpm (j : I) : Measurable (fun y : I → Y => (f j (y j) : ℂ)) :=
    (hfm j).comp (measurable_pi_apply j)
  have hpn (j : I) : ∀ᵐ y ∂μ, ‖(f j (y j) : ℂ)‖ = 1 :=
    Filter.Eventually.of_forall fun _ => Circle.norm_coe _
  have hpi (j : I) : iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Y => (f t (y t) : ℂ)) μ :=
    (hind j).comp (fun t y => (f t y : ℂ)) (fun t => hfm t)
  obtain ⟨c,hc⟩ := hf
  have hc' : ∀ᵐ y ∂μ, ∏ j, (f j (y j) : ℂ) = (c : ℂ) := by
    filter_upwards [hc] with y hy
    exact (map_prod Circle.coeHom _ _).symm.trans (congrArg (fun a : Circle => (a : ℂ)) hy)
  have hx := exact_tuple_dichotomy hk (fun j (y : I → Y) => (f j (y j) : ℂ))
    (fun j => (hpm j).aestronglyMeasurable) hpn hpi (c : ℂ) (Circle.norm_coe c) hc'
  rcases hx with hz | he
  · rw [←(hm i).map_eq,integral_map (hm i).aemeasurable (hfm i).aestronglyMeasurable]
    exact hz i
  · exfalso
    apply hi
    let a : Circle := ⟨∫ y, (f i (y i) : ℂ) ∂μ,mem_sphere_zero_iff_norm.mpr (he i).2⟩
    have hj : ∀ᵐ y ∂μ, f i (y i) = a :=
      (he i).1.mono fun _ h => Circle.coe_injective h
    have hj' : (f i : Y → Circle) =ᵐ[ν i] fun _ => a := by
      rw [←(hm i).map_eq]
      apply (ae_map_iff (hm i).measurable.aemeasurable
        (measurableSet_eq_fun (measurableCircle_measurable Y (f i)) measurable_const)).mpr
      exact hj
    rw [←projectiveCircle_one (ν i),projectiveCircle_eq_iff]
    exact ⟨a,by simpa only [mul_one] using hj'⟩

lemma exactProjectiveSlot_mean_zero (hk : 3 ≤ Fintype.card I)
    (μ : Measure (I → Y)) [IsProbabilityMeasure μ] (ν : I → Measure Y)
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) μ (ν i))
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) μ) (i : I)
    (g : ProjectiveCircle (ν i)) (hg : g ∈ (exactProjectiveSlot μ ν i).range) (hne : g ≠ 1) :
    ∫ y, projectiveCharacter (ν i) g y ∂ν i = 0 := by
  obtain ⟨a,ha⟩ := hg
  obtain ⟨f,hf,hfa⟩ := a.property
  have hfi : projectiveCircle (ν i) (f i) (measurableCircle_measurable Y (f i)) = g := by
    change tupleProjectivize ν f i = g
    rw [hfa]
    exact ha
  have hz := exactCircleTuples_mean_zero hk μ ν hm hind f hf i (fun h => hne (hfi.symm.trans h))
  have he : projectiveCircle (ν i) (projectiveRep (ν i) g) (measurableCircle_measurable Y _) =
      projectiveCircle (ν i) (f i) (measurableCircle_measurable Y _) :=
    (projectiveRep_class (ν i) g).trans hfi.symm
  obtain ⟨c,hc⟩ := (projectiveCircle_eq_iff (ν i) _ _ _ _).mp he
  have hc' : projectiveCharacter (ν i) g =ᵐ[ν i] fun y => (c : ℂ) * (f i y : ℂ) :=
    hc.mono fun _ h => congrArg (fun c : Circle => (c : ℂ)) h
  rw [integral_congr_ae hc',integral_const_mul,hz,mul_zero]
end

section
open MeasureTheory ProbabilityTheory Set
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U) (S : Set (U × HilbertCode κ))
lemma localProjectiveCharacters (hk : 3 ≤ Fintype.card I) (p : P) (i : I)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (hind : ∀ j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Y => y t) (Λ p))
    (hS : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} = {q | (u p i,q) ∈ S}) :
    ProjectiveCharacters (κ (u p i))
      (fun g : Additive (localProjectiveGroup κ S (u p i)) =>
        projectiveCharacter (κ (u p i)) g.toMul.val) := by
  apply projectiveCharacters_of_zero_mean
  intro g hg
  apply exactProjectiveSlot_mean_zero hk (Λ p) (fun j => κ (u p j)) hm hind i g.val
  · rw [←localProjectiveGroup_eq κ Λ u S p i hm hS]
    exact g.property
  · intro he
    apply hg
    exact Subtype.ext he
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
include hk hm hind hS in
lemma localGraph_projectiveCharacters (i : I) :
    ∀ᵐ a ∂M.parameterLaw 0, ProjectiveCharacters (M.ownKernel 0 a)
      (fun g : Additive (localProjectiveGroup (M.ownKernel 0) S a) =>
        projectiveCharacter (M.ownKernel 0 a) g.toMul.val) := by
  have hp : ∀ᵐ p ∂M.parameterLaw 1, ProjectiveCharacters (M.ownKernel 0 (tupleParameter M p i))
      (fun g : Additive (localProjectiveGroup (M.ownKernel 0) S (tupleParameter M p i)) =>
        projectiveCharacter (M.ownKernel 0 (tupleParameter M p i)) g.toMul.val) := by
    filter_upwards [hS] with p hp
    exact localProjectiveCharacters (M.ownKernel 0) Λ (tupleParameter M) S hk p i (hm p) (hind p) (hp i)
  have hd := ae_map_descent (P := fun a => ProjectiveCharacters (M.ownKernel 0 a)
    (fun g : Additive (localProjectiveGroup (M.ownKernel 0) S a) =>
      projectiveCharacter (M.ownKernel 0 a) g.toMul.val))
    (M.parameterLaw 1) (measurable_plane 0 0 i) hp
  rwa [M.parameterLaw_consistent 0 0 i] at hd
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ComplexConjugate
variable {X Y L A : Type*} [MeasurableSpace X] [MeasurableSpace Y] [AddCommGroup L]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    {μ : Measure X} [IsProbabilityMeasure μ]
    {η : Measure Y} [IsProbabilityMeasure η]
    (x : Y → X) (hx : MeasurePreserving x η μ)
    (t : ℕ → X → X) (ht : ∀ m, MeasurePreserving (t m) μ μ)
    (htadd : ∀ a b z, t (a+b) z = t b (t a z))
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun m => μ (A ∩ t m ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
    (a : X → A) (ha : Measurable a) (v : A → ℂ)
    (hcenter : ∫ z, v (a z) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => wordEntropy (η := μ) (fun m z => a (t m z)) n / n)
      atTop (𝓝 0))
    {χ : L → Y → ℂ} (hχ : ProjectiveCharacters η χ)
    (G : L ≃ₗ[ℤ] L)

variable {U : Type*} [MeasurableSpace U] (ν : Measure U) [IsProbabilityMeasure ν]

lemma constant_integral_zero_of_bounded_cesaro (s : ℕ → U → ℝ) (C c : ℝ)
    (hC : 0 ≤ C) (hs : ∀ n, AEStronglyMeasurable (s n) ν)
    (hb : ∀ n, ∀ᵐ u ∂ν, 0 ≤ s n u ∧ s n u ≤ C)
    (hc : ∀ n, ∫ u, s n u ∂ν = c)
    (hlim : ∀ᵐ u ∂ν, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N, s m u)
      atTop (𝓝 0)) : c = 0 := by
  let F : ℕ → U → ℝ := fun N u => (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N, s m u
  have hsi (n : ℕ) : Integrable (s n) ν :=
    Integrable.mono' (integrable_const C) (hs n) ((hb n).mono fun u hu => by
      rw [Real.norm_eq_abs,abs_of_nonneg hu.1]
      exact hu.2)
  have hfm (N : ℕ) : AEStronglyMeasurable (F N) ν :=
    (Finset.aestronglyMeasurable_fun_sum _ (fun m _ => hs m)).const_mul _
  have hfb (N : ℕ) : ∀ᵐ u ∂ν, ‖F N u‖ ≤ C := by
    filter_upwards [ae_all_iff.mpr hb] with u hu
    have hn : 0 ≤ F N u := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun m _ => (hu m).1)
    rw [Real.norm_eq_abs,abs_of_nonneg hn]
    have hle : ∑ m ∈ Finset.range N, s m u ≤ N * C := by
      calc
        _ ≤ ∑ _m ∈ Finset.range N, C := Finset.sum_le_sum fun m _ => (hu m).2
        _ = _ := by simp
    by_cases hN : N=0
    · subst N; simpa [F] using hC
    · unfold F
      calc
        _ ≤ (N : ℝ)⁻¹ * ((N : ℝ) * C) := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (Nat.cast_nonneg _))
        _ = C := by rw [←mul_assoc,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN),one_mul]
  have hfint (N : ℕ) (hN : N ≠ 0) : ∫ u, F N u ∂ν = c := by
    simp only [F,integral_const_mul,integral_finsetSum _ (fun m _ => hsi m),hc,
      Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [←mul_assoc,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN),one_mul]
  have hd := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => C)
    hfm (integrable_const C) hfb hlim
  have he : (fun N : ℕ => ∫ u, F N u ∂ν) =ᶠ[atTop] fun _ => c := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact hfint N (by omega)
  have hd' : Tendsto (fun _ : ℕ => c) atTop (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using hd.congr' he
  exact tendsto_nhds_unique tendsto_const_nhds hd'
end

namespace ArrayObjects.Object
open MeasureTheory
universe u
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
lemma selected_time_iterate (n : ℕ) (y : Arr I M.Y 0) :
    M.x (zeroEquiv I M.Y ((amap M.timeY 0)^[n] y)) =
      (T^[n]) (M.x (zeroEquiv I M.Y y)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    have h : M.x (M.timeY (zeroEquiv I M.Y ((amap M.timeY 0)^[n] y))) =
      T (M.x (zeroEquiv I M.Y ((amap M.timeY 0)^[n] y))) := congrFun M.time_x _
    exact h.trans (congrArg T ih)
end ArrayObjects.Object

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

section RawCorrelation
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (s t : I) (hst : s ≠ t)
    {μ : Measure X} [IsProbabilityMeasure μ] (hμ : M.localLaw.map M.x = μ)
    (hT : MeasurePreserving T μ μ)
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n => μ (A ∩ (T^[n]) ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (α : X → A) (hα : Measurable α) (v : A → ℂ)
    (hcenter : ∫ z, v (α z) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => wordEntropy (η := μ) (fun m z => α ((T^[m]) z)) n / n)
      atTop (𝓝 0))
include hM hk hL hm hind hS E Eπ Eσ hst hμ hT hmix hα hcenter hH in
lemma raw_correlation_zero_oai (i : I) (f : I → Arr I M.Y 0 → ℂ)
    (hf : ∀ j, Measurable (f j)) (hb : ∀ j y, ‖f j y‖ ≤ 1)
    (hi : ∀ y, f i y = v (α (M.x (zeroEquiv I M.Y y)))) :
    (∫ y, ∏ j, f j (plane 0 0 j y) ∂M.law 1) = 0 := by
  classical
  by_contra hn
  obtain ⟨P⟩ := exists_positive_raw_block M Λ hM hk hL hm hind S hS E Eπ Eσ s t hst i f hf hb hn
  let F := fun n => absoluteCoefficient (M.ownKernel 0) (f i ∘ (amap M.timeY 0)^[n])
  let bsum := movingFibreSum E P.ψ P.measurable_ψ labelShiftSecond.toEquiv P.b F
  have hFm (n : ℕ) : Measurable (F n) := measurable_absoluteCoefficient _ _
    ((hf i).comp ((measurable_amap M.timeY.measurable 0).iterate n))
  have hstep (n : ℕ) : bsum (n+1) =ᵐ[M.parameterLaw 0] (bsum n) ∘ amap M.timeU 0 :=
    raw_moving_sum_step M Λ hL hm S hS i E P.ψ P.measurable_ψ P.time_labels P.b (f i) n
  have he := localGraph_group_equiv M Λ hm S hS i
  let C : ℝ := P.finite_block.toFinset.card
  have hbound0 : ∀ᵐ a ∂M.parameterLaw 0, 0 ≤ bsum 0 a ∧ bsum 0 a ≤ C := by
    filter_upwards [he,P.identifications] with a ha hJ
    obtain ⟨e,he⟩ := ha
    obtain ⟨J,hJ⟩ := hJ
    obtain ⟨hfin,hcard⟩ := localBlock_card_le (M.ownKernel 0) S P.ψ P.a₀ a P.b P.finite_block J hJ e he
    constructor
    · exact (E.restrictLevel P.ψ P.measurable_ψ P.b).fibreSum_nonneg _
        (absoluteCoefficient_nonneg _ _) a
    · have h := (E.restrictLevel P.ψ P.measurable_ψ P.b).fibreSum_le_card_mul
        (F 0) 1 a hfin (fun q _ => absoluteCoefficient_le _ _ 1 (a,q)
          (Eventually.of_forall (hb i)))
      exact h.trans (by simpa only [mul_one] using (Nat.cast_le (α := ℝ)).mpr hcard)
  have hzero := constant_integral_zero_of_bounded_cesaro (M.parameterLaw 0) bsum C
    (∫ a, bsum 0 a ∂M.parameterLaw 0) (Nat.cast_nonneg _) (fun n =>
      (measurable_movingFibreSum E P.ψ P.measurable_ψ labelShiftSecond.toEquiv P.b F hFm n).aestronglyMeasurable)
    (movingFibreSum_bound E P.ψ P.measurable_ψ labelShiftSecond.toEquiv P.b F
      (M.parameterLaw 0) (amap M.timeU 0) (M.parameterLaw_invariant 0) hstep C hbound0)
    (movingFibreSum_integral E P.ψ P.measurable_ψ labelShiftSecond.toEquiv P.b F
      (M.parameterLaw 0) (amap M.timeU 0) (M.parameterLaw_invariant 0) hFm hstep) ?_
  · exact (ne_of_gt P.positive) hzero
  · filter_upwards [he,P.identifications,localGraph_projectiveCharacters M Λ hk hm hind S hS i,
      M.ownKernel_zero_image] with a ha hJ hχ hxa
    obtain ⟨e,he⟩ := ha
    obtain ⟨J,hJ⟩ := hJ
    have hx : MeasurePreserving (M.x ∘ zeroEquiv I M.Y) (M.ownKernel 0 a) μ :=
      ⟨M.measurable_x.comp (zeroEquiv I M.Y).measurable,hxa.trans hμ⟩
    apply local_moving_cancellation (M.ownKernel 0) S E P.ψ P.measurable_ψ
      labelShiftSecond.toEquiv P.a₀ a P.b P.finite_block P.G P.block_shift J hJ e he hχ
      (M.x ∘ zeroEquiv I M.Y) hx (fun n => T^[n]) (fun n => hT.iterate n)
      (fun c d z => by rw [Nat.add_comm,Function.iterate_add_apply]) hmix α hα v hcenter hH
      (amap M.timeY 0) (f i)
    intro n y
    rw [hi,M.selected_time_iterate]
    rfl
end RawCorrelation
universe u
end ArrayObjects.Object.Rolled

end Rokhlin

end

end OAI
end

theorem solution.{u, u_1} : type_of% @OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_correlation_zero_oai.{u, u_1} := @OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_correlation_zero_oai.{u, u_1}
