-- Prove2me | solution 1 for OAI.Rokhlin.ArrayObjects.Object.Rolled.exists_raw_finite_levels
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:03:41.055681+00:00
-- url     : https://prove2.me/submissions/9fde4c67-02f4-4fef-b58e-ef9987fc9d67
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ3Ro002
import Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_rawCounting_partial_unitary

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_HilbertCodes
attribute [-instance] _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  (κ : Kernel U Y) [IsMarkovKernel κ]

namespace HilbertCode
variable {κ}
lemma measurable_base : Measurable (base (κ := κ)) := measurable_fst.comp measurable_subtype_coe

end HilbertCode
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  {κ : Kernel U Y} [IsMarkovKernel κ]

lemma measurable_hilbert_encode {V : Type*} [MeasurableSpace V]
    (u : V → U) (hu : Measurable u) (s : ∀ v, Lp ℂ 2 (κ (u v)))
    (f : V × Y → ℂ) (hf : Measurable f)
    (he : ∀ v, (s v : Y → ℂ) =ᵐ[κ (u v)] (fun y => f (v,y))) :
    Measurable (fun v => HilbertCode.encode (u v) (s v)) := by
  apply Measurable.subtype_mk
  apply hu.prodMk
  apply Measurable.of_eval
  intro n
  have hdist : (fun v => dist (s v) (hilbertTests (κ (u v)) n)) =
      fun v => Real.sqrt (Complex.re (∫ y,
        inner ℂ (f (v,y)-hilbertTestFunction (hilbertTestKeys n) y)
          (f (v,y)-hilbertTestFunction (hilbertTestKeys n) y) ∂κ (u v))) := by
    funext v
    exact lp_dist_of_representatives _ _ _ _ (he v) (hilbertTestVector_coe _ _)
  change Measurable (fun v => dist (s v) (hilbertTests (κ (u v)) n))
  rw [hdist]
  have hh := hf.sub ((hilbertTestFunction_measurable (hilbertTestKeys n)).comp measurable_snd)
  exact Real.continuous_sqrt.measurable.comp
    (Complex.continuous_re.measurable.comp
      ((hh.stronglyMeasurable.inner hh.stronglyMeasurable).integral_kernel_prod_right
        (κ := κ.comap u hu)).measurable)
end

namespace HilbertCode
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ]

lemma measurable_coefficient (n : ℕ) : Measurable (fun p : HilbertCode κ => coefficient p n) := by
  have hh : StronglyMeasurable (fun p : HilbertCode κ × Y =>
      inner ℂ (hilbertTestFunction (hilbertTestKeys n) p.2) (representative p)) :=
    ((hilbertTestFunction_measurable _).comp measurable_snd).stronglyMeasurable.inner
      measurable_representative.stronglyMeasurable
  exact (hh.integral_kernel_prod_right (κ := κ.comap base measurable_base)
    (f := fun p y => inner ℂ (hilbertTestFunction (hilbertTestKeys n) y) (representative (p,y)))).measurable

lemma measurableSet_isCanonical : MeasurableSet {p : HilbertCode κ | IsCanonical p} := by
  simp only [IsCanonical,RayCanonical,←coefficient_eq,Set.ofPred_exists,Set.ofPred_and,Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
      measurableSet_eq_fun (measurable_coefficient m) measurable_const
  · exact (measurableSet_lt measurable_const (Complex.continuous_re.measurable.comp (measurable_coefficient n))).inter
      (measurableSet_eq_fun (Complex.continuous_im.measurable.comp (measurable_coefficient n)) measurable_const)

lemma measurableSet_isUnimodular : MeasurableSet {p : HilbertCode κ | IsUnimodular p} := by
  have ht : MeasurableSet {p : HilbertCode κ × Y | ‖representative p‖ ≠ 1} :=
    (measurableSet_eq_fun measurable_representative.norm measurable_const).compl
  have hm := Kernel.measurable_kernel_prodMk_left (κ := κ.comap base measurable_base) ht
  exact measurableSet_eq_fun hm measurable_const

end HilbertCode

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
variable {P U Y I : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

omit [StandardBorelSpace P] [StandardBorelSpace U] [DecidableEq I] in
lemma measurable_exactCodeMean : Measurable (exactCodeMean κ Λ) := by
  have hh : StronglyMeasurable (fun t : (P × (I → HilbertCode κ)) × (I → Y) =>
      ∏ i, HilbertCode.representative (t.1.2 i,t.2 i)) := by
    apply Measurable.stronglyMeasurable
    apply Finset.measurable_prod
    intro i _
    exact HilbertCode.measurable_representative.comp
      (((measurable_pi_apply i).comp measurable_fst.snd).prodMk
        ((measurable_pi_apply i).comp measurable_snd))
  exact (hh.integral_kernel_prod_right (κ := Λ.comap Prod.fst measurable_fst)
    (f := fun (t : P × (I → HilbertCode κ)) (y : I → Y) =>
      ∏ i, HilbertCode.representative (t.2 i,y i))).measurable

omit [DecidableEq I] in
omit [StandardBorelSpace P] in
lemma measurableSet_exactCodeSet (hu : Measurable u) : MeasurableSet (exactCodeSet κ Λ u) := by
  have hbase (i : I) : MeasurableSet {t : P × (I → HilbertCode κ) | (t.2 i).base = u t.1 i} :=
    measurableSet_eq_fun
      ((HilbertCode.measurable_base (κ := κ)).comp ((measurable_pi_apply i).comp measurable_snd))
      (((measurable_pi_apply i).comp hu).comp measurable_fst)
  have hcan (i : I) : MeasurableSet {t : P × (I → HilbertCode κ) |
      HilbertCode.IsCanonical (t.2 i) ∧ HilbertCode.IsUnimodular (t.2 i)} :=
    (HilbertCode.measurableSet_isCanonical.inter HilbertCode.measurableSet_isUnimodular).preimage
      ((measurable_pi_apply i).comp measurable_snd)
  have hb : MeasurableSet {t : P × (I → HilbertCode κ) | ∀ i, (t.2 i).base = u t.1 i} := by
    convert MeasurableSet.iInter hbase using 1
    all_goals try with_reducible_and_instances rfl
    ext t
    simp
  have hc : MeasurableSet {t : P × (I → HilbertCode κ) |
      ∀ i, HilbertCode.IsCanonical (t.2 i) ∧ HilbertCode.IsUnimodular (t.2 i)} := by
    convert MeasurableSet.iInter hcan using 1
    all_goals try with_reducible_and_instances rfl
    ext t
    simp
  exact hb.inter (hc.inter (measurableSet_eq_fun (measurable_exactCodeMean κ Λ).norm measurable_const))

end

section
open MeasureTheory ProbabilityTheory Set Topology
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

variable {P U Y : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ]
  {u : P → U}

lemma MeasurableSection.zero (hu : Measurable u) :
    MeasurableSection (κ := κ) (u := u) (fun _ => 0) := by
  exact measurable_hilbert_encode u hu _ (fun _ => 0) measurable_const
    (fun _ => Lp.coeFn_zero _ _ _)

end

namespace HilbertCode

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ]

lemma measurable_unitPhase : Measurable (unitPhase (κ := κ)) := by
  have hm : Measurable (fun q : UnitCode κ => coefficient q.val (firstCoefficient q)) :=
    Measurable.find (fun n => (measurable_coefficient n).comp measurable_subtype_coe)
      (fun n => (measurableSet_eq_fun ((measurable_coefficient n).comp measurable_subtype_coe)
        measurable_const).compl) unitCode_exists_coefficient
  exact (Complex.continuous_ofReal.measurable.comp hm.norm).div hm

lemma measurable_normalizeUnit : Measurable (normalizeUnit (κ := κ)) := by
  apply measurable_hilbert_encode (fun q : UnitCode κ => q.val.base)
    (measurable_base.comp measurable_subtype_coe) _
    (fun qy => unitPhase qy.1 * representative (qy.1.val,qy.2))
  · exact (measurable_unitPhase.comp measurable_fst).mul
      (measurable_representative.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))
  · intro q
    filter_upwards [Lp.coeFn_smul (unitPhase q) q.val.decode,representative_eq_decode q.val]
      with y h1 h2
    exact h1.trans (congrArg (unitPhase q * ·) h2.symm)

lemma measurable_circleRep_comp (E : Y ≃ᵐ Y) :
    Measurable (fun qy : HilbertCode κ × Y => circleRep (κ := κ) qy.1 (E.symm qy.2)) := by
  have hm : Measurable (fun qy : HilbertCode κ × Y => (qy.1,E.symm qy.2)) :=
    measurable_fst.prodMk (E.symm.measurable.comp measurable_snd)
  have hr : Measurable (fun qy : HilbertCode κ × Y => representative (κ := κ) (qy.1,E.symm qy.2)) :=
    (measurable_representative (κ := κ)).comp hm
  exact measurable_circleOfValue.comp hr

lemma measurable_transportRaw (F : U → U) (hF : Measurable F) (E : Y ≃ᵐ Y) :
    Measurable (transportRaw (κ := κ) F E) := by
  unfold transportRaw
  apply measurable_hilbert_encode (κ := κ) (fun q : HilbertCode κ => F q.base)
    (hF.comp (measurable_base (κ := κ)))
    (fun q => circleLp (κ (F q.base)) (circleRep (κ := κ) q ∘ E.symm)
      ((measurable_circleRep_fixed q).comp E.symm.measurable))
    (fun qy : HilbertCode κ × Y => (circleRep (κ := κ) qy.1 (E.symm qy.2) : ℂ))
  · exact measurable_subtype_coe.comp (measurable_circleRep_comp (κ := κ) E)
  · intro q
    exact circleLp_coe _ _ _

lemma measurable_transport (F : U → U) (hF : Measurable F) (E : Y ≃ᵐ Y) :
    Measurable (transport (κ := κ) F E) :=
  measurable_normalizeUnit.comp (Measurable.subtype_mk (measurable_transportRaw F hF E))

end HilbertCode

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

end Rokhlin

end

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
-- module Solutions.OAIQ3_Rok.MultipleMixing_Joinings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

namespace JoiningOperator

open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal


section
variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {τ : Measure Z}
  {x : Ω → X} {y : Ω → Y} {z : X → Z}

lemma pull_adjoint_pull (hx : MeasurePreserving x μ ν) :
    (pull hx).adjoint ∘L pull hx = ContinuousLinearMap.id ℂ (Lp ℂ 2 ν) := by
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (pull hx)).mp
  intro g
  exact Lp.norm_compMeasurePreserving g hx

lemma pull_comp (hx : MeasurePreserving x μ ν) (hz : MeasurePreserving z ν τ) :
    pull (hz.comp hx) = pull hx ∘L pull hz := by
  apply ContinuousLinearMap.ext
  intro f
  exact Lp.compMeasurePreserving_comp_apply f hz hx

lemma operator_pullback {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {f : Ω' → Ω} (hf : MeasurePreserving f μ' μ)
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ) :
    operator (hx.comp hf) (hy.comp hf) = operator hx hy := by
  simp only [operator]
  rw [pull_comp hf hx, pull_comp hf hy, adjoint_comp]
  calc
    ((pull hx).adjoint ∘L (pull hf).adjoint) ∘L (pull hf ∘L pull hy) =
        (pull hx).adjoint ∘L (((pull hf).adjoint ∘L pull hf) ∘L pull hy) := by
      simp only [comp_assoc]
    _ = (pull hx).adjoint ∘L pull hy := by rw [pull_adjoint_pull, id_comp]

end
section

variable {Ω X Y : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y}
  {x : Ω → X} {y : Ω → Y}

lemma pull_range (hx : MeasurePreserving x μ ν) :
    LinearMap.range (pull hx).toLinearMap =
      lpMeas ℂ ℂ (MeasurableSpace.comap x inferInstance) 2 μ := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    apply mem_lpMeas_iff_aestronglyMeasurable.mpr
    have hm : StronglyMeasurable[MeasurableSpace.comap x inferInstance] (fun ω => g (x ω)) :=
      g.1.stronglyMeasurable.comp_measurable (Measurable.of_comap_le le_rfl)
    exact hm.aestronglyMeasurable.congr (Lp.coeFn_compMeasurePreserving g hx).symm
  · intro hf
    have hm := mem_lpMeas_iff_aestronglyMeasurable.mp hf
    obtain ⟨g, hg, he⟩ := hm.stronglyMeasurable_mk.exists_eq_measurable_comp
    have hfe : f =ᵐ[μ] g ∘ x := hm.ae_eq_mk.trans (Filter.Eventually.of_forall (congrFun he))
    have hLp : MemLp g 2 ν := by
      rw [← hx.map_eq]
      exact (memLp_map_measure_iff hg.aestronglyMeasurable hx.aemeasurable).mpr
        ((memLp_congr_ae hfe).mp (Lp.memLp f))
    refine ⟨hLp.toLp g, ?_⟩
    apply Lp.ext
    exact (Lp.coeFn_compMeasurePreserving (hLp.toLp g) hx).trans
      ((hx.quasiMeasurePreserving.ae_eq_comp hLp.coeFn_toLp).trans hfe.symm)

lemma pull_adjoint_projection (hx : MeasurePreserving x μ ν) (f : Lp ℂ 2 μ) :
    pull hx ((pull hx).adjoint f) =
      (condExpL2 ℂ ℂ hx.measurable.comap_le f : Lp ℂ 2 μ) := by
  let S := lpMeas ℂ ℂ (MeasurableSpace.comap x inferInstance) 2 μ
  let : Fact (MeasurableSpace.comap x inferInstance ≤ mΩ) := ⟨hx.measurable.comap_le⟩
  change _ = S.starProjection f
  apply (S.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_).symm
  · change _ ∈ lpMeas ℂ ℂ (MeasurableSpace.comap x inferInstance) 2 μ
    rw [← pull_range hx]
    exact ⟨(pull hx).adjoint f, rfl⟩
  · intro u hu
    change u ∈ lpMeas ℂ ℂ (MeasurableSpace.comap x inferInstance) 2 μ at hu
    rw [← pull_range hx] at hu
    obtain ⟨g, rfl⟩ := hu
    rw [inner_sub_left]
    change inner ℂ f (pull hx g) -
      inner ℂ (pull hx ((pull hx).adjoint f)) (pull hx g) = 0
    rw [← adjoint_inner_left, ← adjoint_inner_left]
    change inner ℂ ((pull hx).adjoint f) g -
      inner ℂ (((pull hx).adjoint ∘L pull hx) ((pull hx).adjoint f)) g = 0
    rw [pull_adjoint_pull]
    simp


end


end JoiningOperator

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
open MeasureTheory ProbabilityTheory Set
variable {P U Y I : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

lemma exactCode_slot_embedding (hu : Measurable u) (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) (i : I) :
    MeasurableEmbedding (fun t : ExactCodeTuple κ Λ u => (t.1.1,t.1.2 i)) := by
  let : StandardBorelSpace (ExactCodeTuple κ Λ u) :=
    (measurableSet_exactCodeSet κ Λ u hu).standardBorel
  apply Measurable.measurableEmbedding
    (measurable_subtype_coe.fst.prodMk ((measurable_pi_apply i).comp measurable_subtype_coe.snd))
  intro a b hab
  have hp : a.1.1 = b.1.1 := congrArg (fun x : P × HilbertCode κ => x.1) hab
  have hi : a.1.2 i = b.1.2 i := congrArg (fun x : P × HilbertCode κ => x.2) hab
  have hb : (a.1.1,b.1.2) ∈ exactCodeSet κ Λ u := by rw [hp]; exact b.property
  exact Subtype.ext (Prod.ext hp (exactCode_unique_slot κ Λ u hk hm hind a.property hb i hi))

lemma measurable_exactMatching (hu : Measurable u) (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) (i : I) :
    Measurable (exactMatching κ Λ u i) := by
  apply (exactCode_slot_embedding κ Λ u hu hk hm hind i).measurable_extend
    measurable_subtype_coe.snd
  apply Measurable.of_eval
  intro j
  exact MeasurableSection.zero (((measurable_pi_apply j).comp hu).comp measurable_fst)

lemma exactMatching_exact (hu : Measurable u) (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) (i : I)
    {p : P} {a : I → HilbertCode κ} (ha : (p,a) ∈ exactCodeSet κ Λ u) :
    exactMatching κ Λ u i (p,a i) = a :=
  (exactCode_slot_embedding κ Λ u hu hk hm hind i).injective.extend_apply _ _ ⟨(p,a),ha⟩
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

lemma comapBase_preserving (π : Measure P) [SigmaFinite π] (ν : Measure U) [SigmaFinite ν]
    (t : P → U) (ht : MeasurePreserving t π ν) :
    MeasurePreserving (fun x : P × Z => (t x.1,x.2)) ((E.comapBase t ht.measurable).measure π)
      (E.measure ν) := by
  apply (E.comapBase t ht.measurable).measurePreserving_fibrewise E π ν t ht
    Prod.snd measurable_snd
  exact Filter.Eventually.of_forall (fun _ => ⟨Equiv.refl _,fun _ => rfl⟩)

omit [StandardBorelSpace P] [MeasurableSpace U] [StandardBorelSpace U] in
lemma lintegral_indicator_kernel (η : Measure P) (D : Set U) (u : U)
    (g : P → ℝ≥0∞) :
    D.indicator (fun _ => ∫⁻ p, g p ∂η) u = ∫⁻ p, D.indicator (fun _ => g p) u ∂η := by
  classical
  by_cases hu : u ∈ D <;> simp [hu]

lemma parameter_conditional (μ : Measure P) [SigmaFinite μ] (ν : Measure U) [SigmaFinite ν]
    (t : P → U) (ht : MeasurePreserving t μ ν)
    (η : Kernel U P) [IsMarkovKernel η] (hη : HasCondDistrib id t η μ) :
    HasCondDistrib Prod.fst (fun x : P × Z => (t x.1,x.2))
      (η.comap (Prod.fst : U × Z → U) (@measurable_fst U Z _ ‹MeasurableSpace Z›)) ((E.comapBase t ht.measurable).measure μ) := by
  have hobs := E.comapBase_preserving μ ν t ht
  refine ⟨(hobs.measurable.prodMk measurable_fst).aemeasurable,?_⟩
  rw [hobs.map_eq]
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (hobs.measurable.prodMk measurable_fst)]
  have hleft := (E.comapBase t ht.measurable).lintegral_measure μ
    (fun x : P × Z => F ((t x.1,x.2),x.1)) (hF.comp (hobs.measurable.prodMk measurable_fst))
  rw [hleft]
  rw [Measure.lintegral_compProd hF]
  have hg : Measurable (fun x : U × Z => ∫⁻ p, F (x,p) ∂η x.1) :=
    Measurable.lintegral_kernel_prod_right (f := fun x p => F (x,p)) hF (κ := η.comap (Prod.fst : U × Z → U) measurable_fst)
  simp only [Kernel.comap_apply]
  rw [E.lintegral_measure ν _ hg]
  let H : U × P → ℝ≥0∞ := fun up => ∑' n, (E.domain n).indicator
    (fun u => F ((u,E.section_ n u),up.2)) up.1
  have hH : Measurable H := by
    apply Measurable.tsum
    intro n
    exact ((hF.comp ((measurable_fst.prodMk ((E.measurable_section n).comp measurable_fst)).prodMk
      measurable_snd)).indicator ((E.measurable_domain n).preimage measurable_fst))
  have hpair : MeasurePreserving (fun p => (t p,p)) μ (ν ⊗ₘ η) :=
    ⟨ht.measurable.prodMk measurable_id,by simpa only [ht.map_eq,id_eq] using hη.map_eq⟩
  have he := hpair.lintegral_comp hH
  rw [Measure.lintegral_compProd hH] at he
  change (∫⁻ p, H (t p,p) ∂μ) = _
  rw [he]
  apply lintegral_congr
  intro u
  dsimp only [H]
  rw [lintegral_tsum]
  · apply tsum_congr
    intro n
    symm
    exact lintegral_indicator_kernel (η u) (E.domain n) u (fun p => F ((u,E.section_ n u),p))
  · intro n
    by_cases hu : u ∈ E.domain n
    · have hf : Measurable (fun p : P => F ((u,E.section_ n u),p)) :=
        hF.comp (measurable_const.prodMk measurable_id)
      convert hf.aemeasurable using 1
      all_goals try with_reducible_and_instances rfl
      ext p
      exact Set.indicator_of_mem hu _
    · simp only [Set.indicator_of_notMem hu]
      exact measurable_const.aemeasurable
end BorelFibreEnumeration

namespace ConditionalTransport
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [MeasurableSpace B] [MeasurableSpace C]
  {μ : Measure Ω} [SFinite μ] {x : Ω → A} {y : Ω → B}
  {κ : Kernel A B} [IsSFiniteKernel κ]

lemma with_observation (h : HasCondDistrib y x κ μ) :
    HasCondDistrib (fun ω => (x ω,y ω)) x (Kernel.id ×ₖ κ) μ := by
  refine ⟨h.aemeasurable_fst.prodMk h.aemeasurable,?_⟩
  have hm : Measurable (fun ab : A × B => (ab.1,ab)) := measurable_fst.prodMk measurable_id
  have hmap : μ.map (fun ω => (x ω,x ω,y ω)) =
      ((μ.map x) ⊗ₘ κ).map (fun ab : A × B => (ab.1,ab)) := by
    rw [←h.map_eq, AEMeasurable.map_map_of_aemeasurable
      hm.aemeasurable h.aemeasurable]
    rfl
  rw [hmap]
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hm]
  have hf' : Measurable (fun ab : A × B => f (ab.1,ab)) := hf.comp hm
  rw [Measure.lintegral_compProd hf',
    Measure.lintegral_compProd hf]
  apply lintegral_congr
  intro a
  have hfa : Measurable (fun ab : A × B => f (a,ab)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  rw [Kernel.lintegral_id_prod hfa κ a]

lemma map_observation (h : HasCondDistrib y x κ μ) (f : A × B → C) (hf : Measurable f) :
    HasCondDistrib (fun ω => f (x ω,y ω)) x ((Kernel.id ×ₖ κ).map f) μ :=
  (with_observation h).comp_left hf
end ConditionalTransport

namespace BorelFibreEnumeration
open MeasureTheory ProbabilityTheory Set
variable {P U Z W : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U] [MeasurableSpace Z] [StandardBorelSpace Z]
  [MeasurableSpace W] [StandardBorelSpace W]
  {S : Set (P × Z)} (E : BorelFibreEnumeration S)
  {R : Set (U × W)} (D : BorelFibreEnumeration R)

include D in
lemma parameter_conditional_of_fibrewise
    (μ : Measure P) [SigmaFinite μ] (ν : Measure U) [SigmaFinite ν]
    (t : P → U) (ht : MeasurePreserving t μ ν)
    (f : P × Z → W) (hf : Measurable f)
    (he : ∀ᵐ p ∂μ, ∃ e : {z : Z // (p,z) ∈ S} ≃ {w : W // (t p,w) ∈ R},
      ∀ z, (e z).val = f (p,z.val))
    (η : Kernel U P) [IsMarkovKernel η] (hη : HasCondDistrib id t η μ) :
    HasCondDistrib Prod.fst (fun x : P × Z => (t x.1,f x))
      (η.comap (Prod.fst : U × W → U) (@measurable_fst U W _ ‹MeasurableSpace W›))
      (E.measure μ) := by
  have hobs : MeasurePreserving (fun x : P × Z => (x.1,f x)) (E.measure μ)
      ((D.comapBase t ht.measurable).measure μ) :=
    E.measurePreserving_fibrewise (D.comapBase t ht.measurable) μ μ id
      (MeasurePreserving.id μ) f hf he
  have hp := D.comapBase_preserving μ ν t ht
  have hc := D.parameter_conditional μ ν t ht η hη
  change HasLaw _ _ _ at hc ⊢
  rw [hp.map_eq] at hc
  have hout : MeasurePreserving (fun x : P × Z => (t x.1,f x)) (E.measure μ) (D.measure ν) :=
    hp.comp hobs
  rw [hout.map_eq]
  exact hc.comp hobs.hasLaw
end BorelFibreEnumeration

namespace Kernel
open MeasureTheory ProbabilityTheory
variable {A B C D E F : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace F]

lemma depMap_markov (κ : ProbabilityTheory.Kernel A B) [IsMarkovKernel κ] (f : A × B → C)
    (hf : Measurable f) : IsMarkovKernel (depMap κ f) := by
  unfold depMap
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _ hf

end Kernel

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

lemma measurable_rawMatchedLabel (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p)) (a b : I) :
    Measurable (rawMatchedLabel M Λ a b) := by
  exact ((measurable_plane _ _ _).comp measurable_snd).prodMk
    ((measurable_pi_apply b).comp ((measurable_exactMatching (M.ownKernel 0) Λ
      (tupleParameter M) (measurable_tupleParameter M) hk hm hind a).comp
      (measurable_snd.prodMk measurable_fst.snd)))

lemma rawLabelTransition_markov (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p)) (a b : I) :
    IsMarkovKernel (rawLabelTransition M Λ a b) :=
  Rokhlin.Kernel.depMap_markov _ _ (measurable_rawMatchedLabel M Λ hk hm hind a b)

lemma rawCounting_parameter_given_label (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M))) (a : I) :
    HasCondDistrib Prod.fst (rawLabelSlot M a)
      ((M.parameterCoordinateKernel a).comap (Prod.fst : RawLabel M → Arr I M.U 0)
        (@measurable_fst (Arr I M.U 0) (HilbertCode (M.ownKernel 0)) _ inferInstance))
      (Eπ.measure (M.parameterLaw 1)) := by
  have he : ∀ᵐ p ∂M.parameterLaw 1, ∃ e :
      {q : I → HilbertCode (M.ownKernel 0) //
        (p,q) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)} ≃
      {q : HilbertCode (M.ownKernel 0) // (tupleParameter M p a,q) ∈ S},
      ∀ z, (e z).val = z.val a := by
    filter_upwards [hS] with p hp
    exact ⟨exactFibreSlotEquiv (M.ownKernel 0) Λ (tupleParameter M) hk hm hind S p a
      (hp a),fun _ => rfl⟩
  have hη : HasCondDistrib id (fun p => tupleParameter M p a)
      (M.parameterCoordinateKernel a) (M.parameterLaw 1) :=
    ⟨((measurable_plane _ _ _).prodMk measurable_id).aemeasurable,
      (compProd_map_condDistrib measurable_id.aemeasurable).symm⟩
  exact Eπ.parameter_conditional_of_fibrewise E (M.parameterLaw 1) (M.parameterLaw 0)
    (fun p => tupleParameter M p a)
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
    (fun x => x.2 a) ((measurable_pi_apply a).comp measurable_snd) he
    (M.parameterCoordinateKernel a) hη

lemma rawCounting_label_transition (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M))) (a b : I) :
    HasCondDistrib (rawLabelSlot M b) (rawLabelSlot M a) (rawLabelTransition M Λ a b)
      (Eπ.measure (M.parameterLaw 1)) := by
  have h := ConditionalTransport.map_observation
    (rawCounting_parameter_given_label M Λ hk hm hind S hS E Eπ a)
    (rawMatchedLabel M Λ a b) (measurable_rawMatchedLabel M Λ hk hm hind a b)
  change HasLaw _ _ _ at h ⊢
  apply h.congr
  filter_upwards [Eπ.ae_mem (M.parameterLaw 1)] with v hv
  refine Prod.ext (by rfl) ?_
  refine Prod.ext (by rfl) ?_
  dsimp only [rawLabelSlot,rawMatchedLabel]
  rw [exactMatching_exact (M.ownKernel 0) Λ (tupleParameter M)
    (measurable_tupleParameter M) hk hm hind a hv]
end ArrayObjects.Object.Rolled

namespace BorelFibreEnumeration
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {P Q U Z : Type*} [MeasurableSpace Q] [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U] [MeasurableSpace Z] [StandardBorelSpace Z]
  {S : Set (U × Z)} (E : BorelFibreEnumeration S)

lemma observation_conditional (μ : Measure P) [SigmaFinite μ] (ν : Measure U) [SigmaFinite ν]
    (t : P → U) (ht : MeasurePreserving t μ ν)
    (o : P → Q) (ho : Measurable o) (η : Kernel U Q) [IsMarkovKernel η] (hη : HasCondDistrib o t η μ) :
    HasCondDistrib (fun x : P × Z => o x.1) (fun x : P × Z => (t x.1,x.2))
      (η.comap (Prod.fst : U × Z → U) (@measurable_fst U Z _ ‹MeasurableSpace Z›)) ((E.comapBase t ht.measurable).measure μ) := by
  have hobs := E.comapBase_preserving μ ν t ht
  refine ⟨(hobs.measurable.prodMk (ho.comp measurable_fst)).aemeasurable,?_⟩
  rw [hobs.map_eq]
  apply Measure.ext_of_lintegral
  intro F hF
  have hjoint : Measurable (fun x : P × Z => ((t x.1,x.2),o x.1)) :=
    hobs.measurable.prodMk (ho.comp measurable_fst)
  rw [lintegral_map hF hjoint]
  have hleft := (E.comapBase t ht.measurable).lintegral_measure μ
    (fun x : P × Z => F ((t x.1,x.2),o x.1)) (hF.comp (hobs.measurable.prodMk (ho.comp measurable_fst)))
  rw [hleft]
  rw [Measure.lintegral_compProd hF]
  have hg : Measurable (fun x : U × Z => ∫⁻ p, F (x,p) ∂η x.1) :=
    Measurable.lintegral_kernel_prod_right (f := fun x p => F (x,p)) hF (κ := η.comap (Prod.fst : U × Z → U) measurable_fst)
  simp only [Kernel.comap_apply]
  rw [E.lintegral_measure ν _ hg]
  let H : U × Q → ℝ≥0∞ := fun up => ∑' n, (E.domain n).indicator
    (fun u => F ((u,E.section_ n u),up.2)) up.1
  have hH : Measurable H := by
    apply Measurable.tsum
    intro n
    exact ((hF.comp ((measurable_fst.prodMk ((E.measurable_section n).comp measurable_fst)).prodMk
      measurable_snd)).indicator ((E.measurable_domain n).preimage measurable_fst))
  have hpair : MeasurePreserving (fun p => (t p,o p)) μ (ν ⊗ₘ η) :=
    ⟨ht.measurable.prodMk ho,by simpa only [ht.map_eq] using hη.map_eq⟩
  have he := hpair.lintegral_comp hH
  rw [Measure.lintegral_compProd hH] at he
  change (∫⁻ p, H (t p,o p) ∂μ) = _
  rw [he]
  apply lintegral_congr
  intro u
  dsimp only [H]
  rw [lintegral_tsum]
  · apply tsum_congr
    intro n
    symm
    exact lintegral_indicator_kernel (η u) (E.domain n) u (fun p => F ((u,E.section_ n u),p))
  · intro n
    by_cases hu : u ∈ E.domain n
    · have hf : Measurable (fun p : Q => F ((u,E.section_ n u),p)) :=
        hF.comp (measurable_const.prodMk measurable_id)
      convert hf.aemeasurable using 1
      all_goals try with_reducible_and_instances rfl
      ext p
      exact Set.indicator_of_mem hu _
    · simp only [Set.indicator_of_notMem hu]
      exact measurable_const.aemeasurable
end BorelFibreEnumeration

section
open MeasureTheory ProbabilityTheory Set
namespace BorelFibreEnumeration
variable {P Q U Z W : Type*} [MeasurableSpace Q] [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U] [MeasurableSpace Z] [StandardBorelSpace Z]
  [MeasurableSpace W] [StandardBorelSpace W]
  {S : Set (P × Z)} (E : BorelFibreEnumeration S)
  {R : Set (U × W)} (D : BorelFibreEnumeration R)

include D in
lemma observation_conditional_of_fibrewise
    (μ : Measure P) [SigmaFinite μ] (ν : Measure U) [SigmaFinite ν]
    (t : P → U) (ht : MeasurePreserving t μ ν)
    (f : P × Z → W) (hf : Measurable f)
    (he : ∀ᵐ p ∂μ, ∃ e : {z : Z // (p,z) ∈ S} ≃ {w : W // (t p,w) ∈ R},
      ∀ z, (e z).val = f (p,z.val))
    (o : P → Q) (ho : Measurable o) (η : Kernel U Q) [IsMarkovKernel η] (hη : HasCondDistrib o t η μ) :
    HasCondDistrib (fun x : P × Z => o x.1) (fun x : P × Z => (t x.1,f x))
      (η.comap (Prod.fst : U × W → U) (@measurable_fst U W _ ‹MeasurableSpace W›))
      (E.measure μ) := by
  have hobs : MeasurePreserving (fun x : P × Z => (x.1,f x)) (E.measure μ)
      ((D.comapBase t ht.measurable).measure μ) :=
    E.measurePreserving_fibrewise (D.comapBase t ht.measurable) μ μ id
      (MeasurePreserving.id μ) f hf he
  have hp := D.comapBase_preserving μ ν t ht
  have hc := D.observation_conditional μ ν t ht o ho η hη
  change HasLaw _ _ _ at hc ⊢
  rw [hp.map_eq] at hc
  have hout : MeasurePreserving (fun x : P × Z => (t x.1,f x)) (E.measure μ) (D.measure ν) :=
    hp.comp hobs
  rw [hout.map_eq]
  exact hc.comp hobs.hasLaw
end BorelFibreEnumeration

end

namespace SigmaFiniteConditional
open MeasureTheory ProbabilityTheory
variable {Ω A B : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure Ω} [SigmaFinite μ] {x : Ω → A} {y : Ω → B}
  {κ : Kernel A B} [IsMarkovKernel κ]

omit [SigmaFinite μ] in
lemma sigmaFinite_trim (hx : Measurable x) [hσ : SigmaFinite (μ.map x)] :
    SigmaFinite (μ.trim hx.comap_le) := by
  rw [←map_trim_comap hx] at hσ
  exact SigmaFinite.of_map _ (Measurable.of_comap_le (le_refl _)).aemeasurable hσ

lemma condExp_of_kernel (hx : Measurable x) [SigmaFinite (μ.map x)]
    (h : HasCondDistrib y x κ μ) (g : B → ℂ) (hg : StronglyMeasurable g)
    (hgi : Integrable (fun ω => g (y ω)) μ) :
    μ[(fun ω => g (y ω)) | MeasurableSpace.comap x inferInstance] =ᵐ[μ]
      (fun ω => ∫ b, g b ∂κ (x ω)) := by
  let := sigmaFinite_trim (μ := μ) hx
  have hm : StronglyMeasurable (fun a => ∫ b, g b ∂κ a) := hg.integral_kernel
  have hj : Integrable (fun ab : A × B => g ab.2) ((μ.map x) ⊗ₘ κ) := by
    rw [←h.map_eq]
    exact (integrable_map_measure (hg.comp_measurable measurable_snd).aestronglyMeasurable
      h.aemeasurable).mpr hgi
  have hi : Integrable (fun a => ∫ b, g b ∂κ a) (μ.map x) := by
    exact hj.integral_compProd
  have hix : Integrable (fun ω => ∫ b, g b ∂κ (x ω)) μ :=
    (integrable_map_measure hm.aestronglyMeasurable hx.aemeasurable).mp hi
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hx.comap_le hgi
    (fun _ _ _ => hix.integrableOn) _
    ((hm.comp_measurable (Measurable.of_comap_le le_rfl)).aestronglyMeasurable)
  rintro _ ⟨s,hs,rfl⟩ _
  rw [←setIntegral_map hs hm.aestronglyMeasurable hx.aemeasurable]
  have he := Measure.setIntegral_compProd hs MeasurableSet.univ hj.integrableOn
  simp only [Measure.restrict_univ] at he
  rw [←he,←h.map_eq]
  have hgm : AEStronglyMeasurable (fun ab : A × B => g ab.2)
      (μ.map (fun ω => (x ω,y ω))) := (hg.comp_measurable measurable_snd).aestronglyMeasurable
  rw [setIntegral_map (hs.prod MeasurableSet.univ) hgm h.aemeasurable]
  have hset : (fun ω => (x ω,y ω)) ⁻¹' (s ×ˢ Set.univ) = x ⁻¹' s := by
    ext ω
    simp
  rw [hset]
end SigmaFiniteConditional

namespace JoiningOperator
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal


section
variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} [SigmaFinite μ] {ν : Measure X} [SigmaFinite ν]
  {ρ : Measure Y} {τ : Measure Z} [SigmaFinite τ]
  {x : Ω → X} {y : Ω → Y} {z : X → Z}

omit [SigmaFinite μ] in
lemma operator_ae_eq_condExp_integrable
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (g : Lp ℂ 2 ρ) (hgi : Integrable (g : Y → ℂ) ρ) :
    (fun ω => operator hx hy g (x ω)) =ᵐ[μ]
      μ[(fun ω => g (y ω)) | MeasurableSpace.comap x inferInstance] := by
  have hσ : SigmaFinite (μ.map x) := by rw [hx.map_eq]; infer_instance
  let := SigmaFiniteConditional.sigmaFinite_trim (μ := μ) hx.measurable
  have hp := pull_adjoint_projection hx (pull hy g)
  have hi : Integrable (pull hy g : Ω → ℂ) μ :=
    ((hy.integrable_comp g.1.stronglyMeasurable.aestronglyMeasurable).mpr hgi).congr (Lp.coeFn_compMeasurePreserving g hy).symm
  have hc := (Lp.memLp (pull hy g)).condExpL2_ae_eq_condExp' (𝕜 := ℂ) hx.measurable.comap_le hi
  rw [Lp.toLp_coeFn, ←hp] at hc
  exact (Lp.coeFn_compMeasurePreserving (operator hx hy g) hx).symm.trans
    (hc.trans (condExp_congr_ae (Lp.coeFn_compMeasurePreserving g hy)))

end

variable {Ω P Z I : Type*} [MeasurableSpace Ω] [MeasurableSpace P] [MeasurableSpace Z]
  {μ : Measure Ω} [SigmaFinite μ] {π : Measure P} [SigmaFinite π]
  {ξ : Measure Z} [SigmaFinite ξ]

lemma operator_congr {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {μ₁ : Measure A} {μ₂ : Measure B} {μ₃ : Measure C}
    {f f' : A → B} {g g' : A → C}
    (hf : MeasurePreserving f μ₁ μ₂) (hg : MeasurePreserving g μ₁ μ₃)
    (hf' : MeasurePreserving f' μ₁ μ₂) (hg' : MeasurePreserving g' μ₁ μ₃)
    (he : f = f') (he' : g = g') : operator hf hg = operator hf' hg' := by
  subst f'; subst g'; rfl

end JoiningOperator

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
lemma measurable_rawLabelTimeInv : Measurable (rawLabelTimeInv M) :=
  ((measurable_amap M.timeU.symm.measurable 0).comp measurable_fst).prodMk
    ((HilbertCode.measurable_transport _ (measurable_amap M.timeU.symm.measurable 0) _).comp measurable_snd)

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

include retained13 in
lemma rawCounting_time_preserving (i : I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S}) (E : BorelFibreEnumeration S) :
    MeasurePreserving (rawLabelTime M) (E.measure (M.parameterLaw 0)) (E.measure (M.parameterLaw 0)) := by
  let _ := retained13
  apply E.measurePreserving_fibrewise E _ _ (amap M.timeU 0) (M.parameterLaw_invariant 0)
    (fun z => HilbertCode.transport (amap M.timeU 0) (amapEquiv M.timeY 0) z.2)
    ((HilbertCode.measurable_transport _ (measurable_amap M.timeU.measurable 0) _).comp measurable_snd)
  exact localGraph_time_equiv M Λ i hL hm S hS

omit [DecidableEq I] in
lemma rawTupleCounting_time_preserving
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M))) :
    MeasurePreserving (rawLabelTupleTime M) (Eπ.measure (M.parameterLaw 1)) (Eπ.measure (M.parameterLaw 1)) := by
  apply Eπ.measurePreserving_fibrewise Eπ _ _ (amap M.timeU 1) (M.parameterLaw_invariant 1)
    (fun z i => HilbertCode.transport (amap M.timeU 0) (amapEquiv M.timeY 0) (z.2 i))
    (Measurable.of_eval fun i => (HilbertCode.measurable_transport _
      (measurable_amap M.timeU.measurable 0) _).comp ((measurable_pi_apply i).comp measurable_snd))
  filter_upwards [ownKernel_tuple_time_preserving M,goodTuple_time_preserving M Λ hL] with p hk hΛ
  exact ⟨exactCodeEquivTransport (M.ownKernel 0) Λ (tupleParameter M) (amapEquiv M.timeU 0)
    (amapEquiv M.timeY 0) p (amap M.timeU 1 p) (tupleParameter_time M p) hk hΛ (hm p)
    (hm (amap M.timeU 1 p)),fun _ => rfl⟩
end ArrayObjects.Object.Rolled

section
open MeasureTheory ContinuousLinearMap
variable {Z : Type*} [MeasurableSpace Z] (ξ : Measure Z)
  (τ σ : Z → Z) (hτ : MeasurePreserving τ ξ ξ) (hσ : MeasurePreserving σ ξ ξ)

lemma aeLpTime_coe (hστ : ∀ᵐ z ∂ξ, σ (τ z) = z) (v : Lp ℂ 2 ξ) :
    (aeLpTime ξ τ σ hτ hσ hστ v : Z → ℂ) =ᵐ[ξ] (fun z => v (τ z)) :=
  Lp.coeFn_compMeasurePreserving v hτ

include hτ in
omit hσ in
lemma inverse_measurePreserving (hσm : Measurable σ) (hστ : ∀ᵐ z ∂ξ, σ (τ z) = z) :
    MeasurePreserving σ ξ ξ := by
  refine ⟨hσm,?_⟩
  calc
    ξ.map σ = (ξ.map τ).map σ := congrArg (Measure.map σ) hτ.map_eq.symm
    _ = ξ.map (σ ∘ τ) := Measure.map_map hσm hτ.measurable
    _ = ξ.map id := Measure.map_congr hστ
    _ = ξ := Measure.map_id
end

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

omit [DecidableEq I] [IsMarkovKernel Λ] in
lemma rawLabelTime_left_inverse (i : I) (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S}) (E : BorelFibreEnumeration S) :
    ∀ᵐ z ∂E.measure (M.parameterLaw 0), rawLabelTimeInv M (rawLabelTime M z) = z := by
  filter_upwards [E.ae_mem (M.parameterLaw 0),
    E.ae_base (M.parameterLaw 0) (localGraph_code_properties M Λ i S hS),
    E.ae_base (M.parameterLaw 0) (M.ownKernel_time_preserving 0)] with z hz hq htime
  obtain ⟨hb,hc,hu⟩ := hq z.2 hz
  apply Prod.ext
  · exact (amapEquiv M.timeU 0).symm_apply_apply z.1
  · exact HilbertCode.transport_inverse (amapEquiv M.timeU 0)
      (amapEquiv M.timeY 0) z.2 hu hc (by rw [hb]; exact htime)
end ArrayObjects.Object.Rolled

namespace JoiningOperator
open MeasureTheory ContinuousLinearMap
variable {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
  (ρ : Measure W) (ξ : Measure Z) (x y : W → Z)
  (hx : MeasurePreserving x ρ ξ) (hy : MeasurePreserving y ρ ξ)
  (τ : Z → Z) (hτ : MeasurePreserving τ ξ ξ)
  (t : W → W) (ht : MeasurePreserving t ρ ρ)

include ht in
lemma operator_time_conjugate (hxt : x ∘ t = τ ∘ x) (hyt : y ∘ t = τ ∘ y) :
    (pull hτ).adjoint ∘L operator hx hy ∘L pull hτ = operator hx hy := by
  have he : operator (hτ.comp hx) (hτ.comp hy) = operator (hx.comp ht) (hy.comp ht) := by
    exact operator_congr _ _ _ _ hxt.symm hyt.symm
  rw [operator,pull_comp hx hτ,pull_comp hy hτ,adjoint_comp] at he
  simpa only [operator,comp_assoc] using he.trans (operator_pullback ht hx hy)

include ht in
lemma operator_commutes_time (hxt : x ∘ t = τ ∘ x) (hyt : y ∘ t = τ ∘ y)
    (V : Lp ℂ 2 ξ ≃ₗᵢ[ℂ] Lp ℂ 2 ξ) (hV : (V : Lp ℂ 2 ξ →L[ℂ] Lp ℂ 2 ξ) = pull hτ) :
    ∀ v, V (operator hx hy v) = operator hx hy (V v) := by
  have he := operator_time_conjugate ρ ξ x y hx hy τ hτ t ht hxt hyt
  rw [←hV,V.adjoint_eq_symm] at he
  intro v
  have hh := congrArg (fun A : Lp ℂ 2 ξ →L[ℂ] Lp ℂ 2 ξ => V (A v)) he
  change V (V.symm (operator hx hy (V v))) = V (operator hx hy v) at hh
  rw [V.apply_symm_apply] at hh
  exact hh.symm
end JoiningOperator

section

open ContinuousLinearMap
open scoped InnerProductSpace

open MeasureTheory Filter

theorem countable_essential_image_of_countable_fibres
    {Z U C : Type*} [MeasurableSpace Z] [MeasurableSpace U]
    [MeasurableSpace C] [MeasurableEq C]
    (ξ : Measure Z) [SigmaFinite ξ] (ν : Measure U) [IsProbabilityMeasure ν]
    (ψ : Z → C) (hψ : Measurable ψ) (D : C ≃ᵐ C)
    (q : U → ℕ → C) (hq : ∀ n, Measurable (fun u => q u n))
    (hocc : ∀ᵐ z ∂ξ, ∀ᵐ u ∂ν, ∃ n, D (ψ z) = q u n) :
    ∃ S : Set C, S.Countable ∧ ∀ᵐ z ∂ξ, ψ z ∈ S := by
  have hm : MeasurableSet {zu : Z × U | ∃ n, D (ψ zu.1) = q zu.2 n} := by
    simp_rw [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro n
    exact measurableSet_eq_fun (D.measurable.comp (hψ.comp measurable_fst))
      ((hq n).comp measurable_snd)
  obtain ⟨u, hu⟩ := ((MeasureTheory.Measure.ae_ae_comm hm).mp hocc).exists
  refine ⟨D.symm '' Set.range (q u), (Set.countable_range (q u)).image D.symm, ?_⟩
  filter_upwards [hu] with z hz
  obtain ⟨n, hn⟩ := hz
  exact ⟨q u n, ⟨n, rfl⟩, by rw [← hn, D.symm_apply_apply]⟩

variable {H J K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem deterministic_transition_of_norm_eq
    (U : H →ₗᵢ[ℂ] K) (V : J →ₗᵢ[ℂ] K) (v : J)
    (hn : ‖(U.toContinuousLinearMap.adjoint ∘L V.toContinuousLinearMap) v‖ = ‖v‖) :
    U ((U.toContinuousLinearMap.adjoint ∘L V.toContinuousLinearMap) v) = V v := by
  let M := U.toContinuousLinearMap.adjoint ∘L V.toContinuousLinearMap
  have hi : inner ℂ (U (M v)) (V v) = inner ℂ (M v) (M v) := by
    change inner ℂ (U.toContinuousLinearMap (M v)) (V v) = _
    rw [← adjoint_inner_right]
    rfl
  have hz : ‖U (M v) - V v‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ), U.norm_map, V.norm_map, hi, inner_self_eq_norm_sq, hn]
    ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
end

section
open ContinuousLinearMap
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

lemma partialUnitary_commutingRange (M : H →L[ℂ] H)
    (h₁ : M = M.adjoint * M * M) (h₂ : M = M * M * M.adjoint)
    (V : H ≃ₗᵢ[ℂ] H) (hV : ∀ v, V (M v) = M (V v)) :
    Commute (partialUnitary M h₁ h₂) (commutingRangeUnitary M V hV) := by
  apply LinearIsometryEquiv.ext
  intro v
  apply Subtype.ext
  exact (hV v).symm
end

section
open MeasureTheory

variable {Z H : Type*} [MeasurableSpace Z] (ξ : Measure Z)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (U : H →ₗᵢ[ℂ] Lp ℂ 2 ξ) (D S : H ≃ₗᵢ[ℂ] H) (v : H)

lemma measurable_labelOrbit : Measurable (labelOrbit ξ U D S v) :=
  Measurable.of_eval fun p => (Lp.stronglyMeasurable (labelOrbitLP ξ U D S v p)).measurable

lemma labelOrbitLP_first (p : ℤ × ℤ) :
    labelOrbitLP ξ U D S v (p.1+1,p.2) = U (D ((D ^ p.1) ((S ^ p.2) v))) := by
  unfold labelOrbitLP
  rw [show p.1+1 = 1+p.1 by omega,zpow_add,zpow_one]
  rfl

lemma labelOrbitLP_second (hDS : Commute D S) (p : ℤ × ℤ) :
    labelOrbitLP ξ U D S v (p.1,p.2+1) = U (S ((D ^ p.1) ((S ^ p.2) v))) := by
  unfold labelOrbitLP
  rw [show p.2+1 = 1+p.2 by omega,zpow_add,zpow_one]
  have h := (hDS.zpow_left p.1).eq
  exact congrArg U (congrArg (fun e : H ≃ₗᵢ[ℂ] H => e ((S ^ p.2) v)) h)

variable {W : Type*} [MeasurableSpace W] (ρ : Measure W)
  (source target : W → Z)
lemma labelOrbit_transition
    (hdet : ∀ w : H, ∀ᵐ x ∂ρ, U w (target x) = U (D w) (source x)) :
    ∀ᵐ x ∂ρ, labelOrbit ξ U D S v (target x) =
      labelShiftFirst (labelOrbit ξ U D S v (source x)) := by
  have ha (p : ℤ × ℤ) := hdet ((D ^ p.1) ((S ^ p.2) v))
  filter_upwards [ae_all_iff.mpr ha] with x hx
  funext p
  change labelOrbitLP ξ U D S v p (target x) = labelOrbitLP ξ U D S v (p.1+1,p.2) (source x)
  rw [labelOrbitLP_first]
  exact hx p

lemma labelOrbit_time (hDS : Commute D S) (τ : Z → Z)
    (htime : ∀ w : H, ∀ᵐ z ∂ξ, U w (τ z) = U (S w) z) :
    ∀ᵐ z ∂ξ, labelOrbit ξ U D S v (τ z) =
      labelShiftSecond (labelOrbit ξ U D S v z) := by
  have ha (p : ℤ × ℤ) := htime ((D ^ p.1) ((S ^ p.2) v))
  filter_upwards [ae_all_iff.mpr ha] with z hz
  funext p
  change labelOrbitLP ξ U D S v p (τ z) = labelOrbitLP ξ U D S v (p.1,p.2+1) z
  rw [labelOrbitLP_second ξ U D S v hDS]
  exact hz p

lemma labelOrbit_zero : labelOrbitLP ξ U D S v (0,0) = U v := by
  simp [labelOrbitLP]
end

section
open MeasureTheory
open scoped ENNReal
variable {Z : Type*} [MeasurableSpace Z] (ξ : Measure Z) [SigmaFinite ξ]

lemma exists_positive_memLp_two : ∃ f : Z → ℝ,
    Measurable f ∧ (∀ z, 0 < f z ∧ f z ≤ 1) ∧ Integrable f ξ ∧ MemLp f 2 ξ := by
  obtain ⟨g,hg,hm,hi⟩ := exists_pos_lintegral_lt_of_sigmaFinite ξ (by simp : (1 : ℝ≥0∞) ≠ 0)
  let f : Z → ℝ := fun z => min (g z : ℝ) 1
  have hf : Measurable f := (measurable_coe_nnreal_real.comp hm).min measurable_const
  have hpos (z) : 0 < f z := lt_min (hg z) zero_lt_one
  have hle (z) : f z ≤ 1 := min_le_right _ _
  have hgint : Integrable (fun z => (g z : ℝ)) ξ := by
    have hh := integrable_toReal_of_lintegral_ne_top (hm.coe_nnreal_ennreal.aemeasurable) (ne_top_of_lt hi)
    simpa only [ENNReal.coe_toReal] using hh
  have hfi : Integrable f ξ := hgint.mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs,abs_of_pos (hpos z)]; exact min_le_left _ _))
  refine ⟨f,hf,fun z => ⟨hpos z,hle z⟩,hfi,?_⟩
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  apply hfi.mono' (hf.norm.pow_const 2).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),Real.norm_eq_abs,abs_of_pos (hpos z)]
  nlinarith [hpos z,hle z]
end

namespace JoiningOperator

open Set MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal

section KernelRepresentatives
variable {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
  {ρ : Measure W} [SigmaFinite ρ] {ξ : Measure Z} [SigmaFinite ξ]
  {source target : W → Z}
  (hs : MeasurePreserving source ρ ξ) (ht : MeasurePreserving target ρ ξ)
  (K : Kernel Z Z) [IsMarkovKernel K]
  (hK : HasCondDistrib target source K ρ)

include hK in
lemma operator_integral_representative (g : Lp ℂ 2 ξ) (f : Z → ℂ)
    (hf : StronglyMeasurable f) (hfi : Integrable f ξ) (hg : (g : Z → ℂ) =ᵐ[ξ] f) :
    (operator hs ht g : Z → ℂ) =ᵐ[ξ] (fun z => ∫ y, f y ∂K z) := by
  have hσ : SigmaFinite (ρ.map source) := by rw [hs.map_eq]; infer_instance
  have hgi := hfi.congr hg.symm
  have he := operator_ae_eq_condExp_integrable hs ht g hgi
  have hx : (fun w => g (target w)) =ᵐ[ρ] (fun w => f (target w)) := ht.quasiMeasurePreserving.ae hg
  have hc := SigmaFiniteConditional.condExp_of_kernel hs.measurable hK f hf
    ((ht.integrable_comp hf.aestronglyMeasurable).mpr hfi)
  have he' := he.trans ((condExp_congr_ae hx).trans hc)
  have hd := (ae_map_iff hs.measurable.aemeasurable
    (measurableSet_eq_fun (Lp.stronglyMeasurable (operator hs ht g)).measurable
      hf.integral_kernel.measurable)).mpr he'
  rwa [hs.map_eq] at hd

include hs ht hK in
omit [SigmaFinite ρ] in
lemma kernel_integrable (f : Z → ℝ) (hf : Measurable f) (hfi : Integrable f ξ) :
    ∀ᵐ z ∂ξ, Integrable f (K z) := by
  have hj : Integrable (fun zy : Z × Z => f zy.2) (ξ ⊗ₘ K) := by
    rw [←hs.map_eq,←hK.map_eq]
    exact (integrable_map_measure (hf.comp measurable_snd).aestronglyMeasurable
      hK.aemeasurable).mpr ((ht.integrable_comp hf.aestronglyMeasurable).mpr hfi)
  exact hj.ae_of_compProd

include K hK in

lemma exists_positive_range_vector : ∃ v : Lp ℂ 2 ξ,
    v ∈ (operator hs ht).range ∧ ∀ᵐ z ∂ξ, 0 < (v z).re := by
  obtain ⟨f,hf,hpos,hfi,hflp⟩ := Rokhlin.exists_positive_memLp_two ξ
  have hfc : MemLp (fun z => (f z : ℂ)) 2 ξ := hflp.ofReal
  let g : Lp ℂ 2 ξ := hfc.toLp _
  refine ⟨operator hs ht g,⟨g,rfl⟩,?_⟩
  have he := operator_integral_representative hs ht K hK g (fun z => (f z : ℂ))
    (Complex.measurable_ofReal.comp hf).stronglyMeasurable hfi.ofReal hfc.coeFn_toLp
  filter_upwards [he,kernel_integrable hs ht K hK f hf hfi] with z hz hi
  rw [hz,integral_complex_ofReal]
  change 0 < ∫ y, f y ∂K z
  apply (integral_pos_iff_support_of_nonneg (fun y => (hpos y).1.le) hi).mpr
  have he : Function.support f = univ := by
    ext y
    simp only [Function.mem_support,mem_univ,iff_true]
    exact ne_of_gt (hpos y).1
  rw [he,measure_univ]
  exact zero_lt_one
end KernelRepresentatives


variable {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
  {ρ : Measure W} [SigmaFinite ρ] {ξ : Measure Z} [SigmaFinite ξ]
  {source target : W → Z}
  (hs : MeasurePreserving source ρ ξ) (ht : MeasurePreserving target ρ ξ)

omit [SigmaFinite ρ] [SigmaFinite ξ] in
lemma deterministic_on_range
    (h₁ : operator hs ht = (operator hs ht).adjoint * operator hs ht * operator hs ht)
    (v : (operator hs ht).range) :
    ∀ᵐ x ∂ρ, v.val (target x) = operator hs ht v.val (source x) := by
  let U : Lp ℂ 2 ξ →ₗᵢ[ℂ] Lp ℂ 2 ρ := Lp.compMeasurePreservingₗᵢ ℂ source hs
  let V : Lp ℂ 2 ξ →ₗᵢ[ℂ] Lp ℂ 2 ρ := Lp.compMeasurePreservingₗᵢ ℂ target ht
  have hn : ‖(U.toContinuousLinearMap.adjoint ∘L V.toContinuousLinearMap) v.val‖ = ‖v.val‖ :=
    partial_unitary_norm_on_range (operator hs ht) h₁ v.val v.property
  have he : U (operator hs ht v.val) = V v.val :=
    deterministic_transition_of_norm_eq U V v.val hn
  have h : (U (operator hs ht v.val) : W → ℂ) =ᵐ[ρ] (V v.val : W → ℂ) := Lp.ext_iff.mp he
  filter_upwards [h,Lp.coeFn_compMeasurePreserving (operator hs ht v.val) hs,
    Lp.coeFn_compMeasurePreserving v.val ht] with w hw h1 h2
  exact h2.symm.trans (hw.symm.trans h1)

lemma exists_orbit_vector
    (h₁ : operator hs ht = (operator hs ht).adjoint * operator hs ht * operator hs ht)
    (h₂ : operator hs ht = operator hs ht * operator hs ht * (operator hs ht).adjoint)
    (V : Lp ℂ 2 ξ ≃ₗᵢ[ℂ] Lp ℂ 2 ξ)
    (hV : ∀ v, V (operator hs ht v) = operator hs ht (V v))
    (τ : Z → Z) (htime : ∀ v : Lp ℂ 2 ξ, (V v : Z → ℂ) =ᵐ[ξ] fun z => v (τ z))
    (K : Kernel Z Z) [IsMarkovKernel K] (hK : HasCondDistrib target source K ρ) :
    ∃ (ψ : Z → LabelOrbitVector) (v : Lp ℂ 2 ξ),
      Measurable ψ ∧ (∀ z, ψ z (0,0) = v z) ∧
      (∀ᵐ z ∂ξ, 0 < (v z).re) ∧
      (∀ᵐ w ∂ρ, ψ (target w) = labelShiftFirst (ψ (source w))) ∧
      (∀ᵐ z ∂ξ, ψ (τ z) = labelShiftSecond (ψ z)) := by
  obtain ⟨v,hvr,hvp⟩ := exists_positive_range_vector hs ht K hK
  let vr : (operator hs ht).range := ⟨v,hvr⟩
  let U := (operator hs ht).range.subtypeₗᵢ
  let D := partialUnitary (operator hs ht) h₁ h₂
  let S := commutingRangeUnitary (operator hs ht) V hV
  have hDS : Commute D S := partialUnitary_commutingRange _ h₁ h₂ V hV
  refine ⟨labelOrbit ξ U D S vr,v,measurable_labelOrbit _ _ _ _ _,?_,hvp,?_,?_⟩
  · intro z
    exact congrArg (fun g : Lp ℂ 2 ξ => g z) (labelOrbit_zero ξ U D S vr)
  · exact labelOrbit_transition ξ U D S vr ρ source target (deterministic_on_range hs ht h₁)
  · exact labelOrbit_time ξ U D S vr hDS τ (fun w => (htime w.val).symm)
end JoiningOperator

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

variable (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

lemma rawCounting_target_parameter_independent (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (s t : I) (hst : s ≠ t) :
    MeasurePreserving (fun z : RawLabelTuple M => (rawLabelSlot M s z,(rawLabelSlot M t z).1))
      (Eπ.measure (M.parameterLaw 1)) ((E.measure (M.parameterLaw 0)).prod (M.parameterLaw 0)) := by
  have he : ∀ᵐ p ∂M.parameterLaw 1, ∃ e :
      {q : I → HilbertCode (M.ownKernel 0) //
        (p,q) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)} ≃
      {q : HilbertCode (M.ownKernel 0) // (tupleParameter M p s,q) ∈ S},
      ∀ z, (e z).val = z.val s := by
    filter_upwards [hS] with p hp
    exact ⟨exactFibreSlotEquiv (M.ownKernel 0) Λ (tupleParameter M) hk hm hind S p s
      (hp s),fun _ => rfl⟩
  have hη : HasCondDistrib (fun p => tupleParameter M p t) (fun p => tupleParameter M p s)
      (Kernel.const (Arr I M.U 0) (M.parameterLaw 0)) (M.parameterLaw 1) := by
    refine ⟨((measurable_plane _ _ _).prodMk (measurable_plane _ _ _)).aemeasurable,?_⟩
    change (M.parameterLaw 1).map (fun p => (tupleParameter M p s,tupleParameter M p t)) =
      (M.parameterLaw 1).map (plane 0 0 s) ⊗ₘ Kernel.const _ (M.parameterLaw 0)
    rw [M.parameterLaw_consistent,Measure.compProd_const]
    exact (parameter_pair_preserving M hk s t hst).map_eq
  have hc := Eπ.observation_conditional_of_fibrewise E (M.parameterLaw 1) (M.parameterLaw 0)
    (fun p => tupleParameter M p s) ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
    (fun z => z.2 s) ((measurable_pi_apply s).comp measurable_snd) he
    (fun p => tupleParameter M p t) (measurable_plane _ _ _)
    (Kernel.const _ (M.parameterLaw 0)) hη
  refine ⟨(measurable_rawLabelSlot M s).prodMk (measurable_rawLabelSlot M t).fst,?_⟩
  have hh := hc.map_eq
  rw [(rawCounting_coordinate_preserving M Λ hk hm hind S hS E Eπ s).map_eq] at hh
  change (Eπ.measure (M.parameterLaw 1)).map (fun z => (rawLabelSlot M s z,(rawLabelSlot M t z).1)) =
    E.measure (M.parameterLaw 0) ⊗ₘ Kernel.const _ (M.parameterLaw 0) at hh
  rwa [Measure.compProd_const] at hh
end ArrayObjects.Object.Rolled

namespace BorelFibreEnumeration
open MeasureTheory Set
variable {U Z : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Z] [StandardBorelSpace Z]
  {S : Set (U × Z)} (E : BorelFibreEnumeration S)

lemma ae_fibre_all (ν : Measure U) [SigmaFinite ν] {P : U × Z → Prop}
    (h : ∀ᵐ x ∂E.measure ν, P x) :
    ∀ᵐ u ∂ν, ∀ z, (u,z) ∈ S → P (u,z) := by
  rw [measure,E.measurableEmbedding_point.ae_map_iff] at h
  have hh : ∀ᵐ x ∂(ν.prod Measure.count).restrict E.indexDomain,
      P (x.1,E.section_ x.2 x.1) := by
    rw [←map_comap_subtype_coe E.measurable_indexDomain]
    exact (MeasurableEmbedding.subtype_coe E.measurable_indexDomain).ae_map_iff.mpr h
  have hprod := (ae_restrict_iff' E.measurable_indexDomain).mp hh
  have ha := Measure.ae_ae_of_ae_prod hprod
  filter_upwards [ha] with u hu
  have hon : ∀ n : ℕ, u ∈ E.domain n → P (u,E.section_ n u) := by
    simpa only [Measure.ae_count_iff,indexDomain,Set.mem_ofPred_eq] using hu
  intro z hz
  obtain ⟨n,hn,rfl⟩ := E.cover u z hz
  exact hon n hn
end BorelFibreEnumeration

section
open MeasureTheory Set
variable {U Z C W : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Z] [StandardBorelSpace Z] [MeasurableSpace C] [MeasurableEq C]
  [MeasurableSpace W] {S : Set (U × Z)} (E : BorelFibreEnumeration S)
  (ν : Measure U) [IsProbabilityMeasure ν] (ρ : Measure W) [SigmaFinite ρ]
  (source target : W → U × Z)

omit [SigmaFinite ρ] in

lemma countable_orbit_image (ht : MeasurePreserving target ρ (E.measure ν))
    (hpp : MeasurePreserving (fun w => (source w,(target w).1)) ρ ((E.measure ν).prod ν))
    (ψ : U × Z → C) (hψ : Measurable ψ) (D : C ≃ᵐ C)
    (hD : ∀ᵐ w ∂ρ, ψ (target w) = D (ψ (source w))) :
    ∃ R : Set C, R.Countable ∧ ∀ᵐ z ∂E.measure ν, ψ z ∈ R := by
  let q : U → ℕ → C := fun u n => ψ (u,E.section_ n u)
  have hq (n : ℕ) : Measurable (fun u => q u n) :=
    hψ.comp (measurable_id.prodMk (E.measurable_section n))
  have hmeas : MeasurableSet {zu : (U × Z) × U | ∃ n, D (ψ zu.1) = q zu.2 n} := by
    simp_rw [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun n => measurableSet_eq_fun
      (D.measurable.comp (hψ.comp measurable_fst)) ((hq n).comp measurable_snd)
  have hw : ∀ᵐ w ∂ρ, ∃ n, D (ψ (source w)) = q (target w).1 n := by
    filter_upwards [hD,ht.quasiMeasurePreserving.ae (E.ae_mem ν)] with w hw hm
    obtain ⟨n,_,hn⟩ := E.cover (target w).1 (target w).2 hm
    exact ⟨n,hw.symm.trans (congrArg ψ (Prod.ext rfl hn.symm))⟩
  have hp : ∀ᵐ zu ∂(E.measure ν).prod ν, ∃ n, D (ψ zu.1) = q zu.2 n := by
    rw [←hpp.map_eq]
    exact (ae_map_iff hpp.measurable.aemeasurable hmeas).mpr hw
  exact countable_essential_image_of_countable_fibres (E.measure ν) ν ψ hψ D q hq
    (Measure.ae_ae_of_ae_prod hp)
end

section
open MeasureTheory ProbabilityTheory Set ContinuousLinearMap
namespace ArrayObjects.Object.Rolled
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

include hM hk hL hm hind hS Eσ hst in
lemma rawCounting_exists_orbit :
    ∃ (ψ : RawLabel M → LabelOrbitVector) (v : Lp ℂ 2 (E.measure (M.parameterLaw 0))),
      Measurable ψ ∧ (∀ z, ψ z (0,0) = v z) ∧
      (∀ᵐ z ∂E.measure (M.parameterLaw 0), 0 < (v z).re) ∧
      (∀ᵐ w ∂Eπ.measure (M.parameterLaw 1), ψ (rawLabelSlot M t w) = labelShiftFirst (ψ (rawLabelSlot M s w))) ∧
      (∀ᵐ z ∂E.measure (M.parameterLaw 0), ψ (rawLabelTime M z) = labelShiftSecond (ψ z)) ∧
      (∃ R : Set LabelOrbitVector, R.Countable ∧ ∀ᵐ z ∂E.measure (M.parameterLaw 0), ψ z ∈ R) := by
  let hq := rawCounting_coordinate_preserving M Λ hk hm hind S hS E Eπ
  have hτ := rawCounting_time_preserving M Λ s hL hm S hS E
  have hi := rawLabelTime_left_inverse M Λ s S hS E
  have hσ := inverse_measurePreserving (E.measure (M.parameterLaw 0)) (rawLabelTime M)
    (rawLabelTimeInv M) hτ (measurable_rawLabelTimeInv M) hi
  let V := aeLpTime _ _ _ hτ hσ hi
  have hV : ∀ v, V (JoiningOperator.operator (hq s) (hq t) v) =
      JoiningOperator.operator (hq s) (hq t) (V v) :=
    JoiningOperator.operator_commutes_time _ _ _ _ (hq s) (hq t) _ hτ _
      (rawTupleCounting_time_preserving M Λ hL hm Eπ) rfl rfl V rfl
  have hA := rawCounting_partial_unitary M Λ hM hk hL hm hind S hS E Eπ Eσ s t hst
  let := rawLabelTransition_markov M Λ hk hm hind s t
  obtain ⟨ψ,v,hψ,hzero,hpos,htr,htime⟩ := JoiningOperator.exists_orbit_vector (hq s) (hq t)
    hA.1 hA.2 V hV (rawLabelTime M) (aeLpTime_coe _ _ _ hτ hσ hi)
    (rawLabelTransition M Λ s t) (rawCounting_label_transition M Λ hk hm hind S hS E Eπ s t)
  refine ⟨ψ,v,hψ,hzero,hpos,htr,htime,?_⟩
  exact countable_orbit_image E (M.parameterLaw 0) (Eπ.measure (M.parameterLaw 1))
    (rawLabelSlot M s) (rawLabelSlot M t) (hq t)
    (rawCounting_target_parameter_independent M Λ hk hm hind S hS E Eπ s t hst)
    ψ hψ labelShiftFirst htr
end ArrayObjects.Object.Rolled
end

namespace BorelFibreEnumeration
open MeasureTheory Set
open scoped ENNReal
variable {U Z : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Z] [StandardBorelSpace Z]
  {S : Set (U × Z)} (E : BorelFibreEnumeration S)

lemma restrictGraph_mass (ν : Measure U) [SigmaFinite ν]
    (Q : Set (U × Z)) (hQ : MeasurableSet Q) :
    (E.restrictGraph Q hQ).measure ν univ = E.measure ν Q := by
  rw [←lintegral_one,←lintegral_indicator_one hQ]
  change (∫⁻ u, (1 : ℝ≥0∞) ∂(E.restrictGraph Q hQ).measure ν) =
    ∫⁻ a, Q.indicator (fun _ => (1 : ℝ≥0∞)) a ∂E.measure ν
  rw [(E.restrictGraph Q hQ).lintegral_measure ν (fun _ => 1) measurable_const,
    E.lintegral_measure ν (Q.indicator (fun _ => 1)) (measurable_const.indicator hQ)]
  apply lintegral_congr
  intro u
  apply tsum_congr
  intro n
  classical
  simp only [restrictGraph,indicator_apply,mem_ofPred]
  split_ifs <;> simp_all

lemma ae_finite_fibres (ν : Measure U) [SigmaFinite ν]
    (hν : E.measure ν univ < ∞) : ∀ᵐ u ∂ν, {z | (u,z) ∈ S}.Finite := by
  let g : U → ℝ≥0∞ := fun u => ∑' n, (E.domain n).indicator (fun _ => 1) u
  have hg : Measurable g := Measurable.tsum fun n => measurable_const.indicator (E.measurable_domain n)
  have hi : ∫⁻ u, g u ∂ν ≠ ∞ := by
    rw [←E.lintegral_measure ν (fun _ => 1) measurable_const,lintegral_one]
    exact hν.ne
  filter_upwards [ae_lt_top hg hi] with u hu
  have he : g u = Measure.count {n : ℕ | u ∈ E.domain n} := by
    rw [←lintegral_indicator_one (Set.to_countable _).measurableSet,lintegral_count]
    rfl
  rw [he,Measure.count_apply_lt_top] at hu
  have hr : {z | (u,z) ∈ S} = (fun n => E.section_ n u) '' {n | u ∈ E.domain n} := by
    ext z
    constructor
    · intro hz
      obtain ⟨n,hn,he⟩ := E.cover u z hz
      exact ⟨n,hn,he⟩
    · rintro ⟨n,hn,rfl⟩
      exact E.mem n u hn
  rw [hr]
  exact hu.image _

lemma ae_finite_level (ν : Measure U) [SigmaFinite ν]
    (Q : Set (U × Z)) (hQ : MeasurableSet Q) (hν : E.measure ν Q < ∞) :
    ∀ᵐ u ∂ν, {z | (u,z) ∈ S ∧ (u,z) ∈ Q}.Finite := by
  apply (E.restrictGraph Q hQ).ae_finite_fibres ν
  rw [E.restrictGraph_mass ν Q hQ]
  exact hν
end BorelFibreEnumeration

section
open MeasureTheory Set
open scoped ENNReal
variable {Z C W : Type*} [MeasurableSpace Z] [MeasurableSpace C]
  [MeasurableSingletonClass C] [MeasurableSpace W]
  (ξ : Measure Z) (ψ : Z → C)

omit [MeasurableSpace C] [MeasurableSingletonClass C] in
lemma positiveLevels_countable (S : Set C) (hSc : S.Countable)
    (hS : ∀ᵐ z ∂ξ, ψ z ∈ S) : (positiveLevels ξ ψ).Countable := by
  apply hSc.mono
  intro b hb
  by_contra hbS
  have he : ∀ᵐ z ∂ξ, ψ z ≠ b := hS.mono fun z hz he => hbS (he ▸ hz)
  have hz : ξ {z | ψ z = b} = 0 := by simpa only [ae_iff,not_not] using he
  exact hb hz

omit [MeasurableSpace C] [MeasurableSingletonClass C] in
lemma ae_mem_positiveLevels (S : Set C) (hSc : S.Countable)
    (hS : ∀ᵐ z ∂ξ, ψ z ∈ S) : ∀ᵐ z ∂ξ, ψ z ∈ positiveLevels ξ ψ := by
  let : Countable S := hSc.to_subtype
  have h (b : S) : ∀ᵐ z ∂ξ, ψ z = b.val → b.val ∈ positiveLevels ξ ψ := by
    by_cases hb : ξ {z | ψ z = b.val} = 0
    · have he : ∀ᵐ z ∂ξ, ψ z ≠ b.val := by simpa only [ae_iff,not_not] using hb
      exact he.mono fun _ hz he => False.elim (hz he)
    · exact Filter.Eventually.of_forall fun _ _ => hb
  filter_upwards [hS,ae_all_iff.mpr h] with z hz hb
  exact hb ⟨ψ z,hz⟩ rfl

omit [MeasurableSingletonClass C] in
lemma joining_transport_invariant (hψ : Measurable ψ) (ρ : Measure W)
    (source target : W → Z) (hs : MeasurePreserving source ρ ξ)
    (ht : MeasurePreserving target ρ ξ) (D : C ≃ᵐ C)
    (hD : (ψ ∘ target) =ᵐ[ρ] (D ∘ ψ ∘ source)) :
    MeasurePreserving D (ξ.map ψ) (ξ.map ψ) := by
  refine ⟨D.measurable,?_⟩
  rw [←hs.map_eq,Measure.map_map hψ hs.measurable,
    Measure.map_map D.measurable (hψ.comp hs.measurable),←Measure.map_congr hD,
    ←Measure.map_map hψ ht.measurable,ht.map_eq]
  rw [←Measure.map_map hψ hs.measurable,hs.map_eq]

omit [MeasurableSpace C] [MeasurableSingletonClass C] in

lemma finite_positive_level_mass (v : Lp ℂ 2 ξ) (c : C → ℂ)
    (hcoord : ∀ᵐ z ∂ξ, c (ψ z) = v z) (hpos : ∀ᵐ z ∂ξ, v z ≠ 0)
    (b : positiveLevels ξ ψ) : ξ {z | ψ z = b.val} < ∞ := by
  have hb : c b.val ≠ 0 := by
    intro hb
    have he : ∀ᵐ z ∂ξ, ψ z ≠ b.val := by
      filter_upwards [hcoord,hpos] with z hz hp he
      exact hp (hz.symm.trans ((congrArg c he).trans hb))
    exact b.property (by simpa only [ae_iff,not_not] using he)
  have hi : Integrable (fun z => ‖v z‖ ^ 2) ξ := (Lp.memLp v).integrable_norm_pow (by decide : 2 ≠ 0)
  have hbound := hi.measure_ge_lt_top (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hb))
  apply lt_of_le_of_lt _ hbound
  apply measure_mono_ae
  filter_upwards [hcoord] with z hz hzb
  change ‖c b.val‖ ^ 2 ≤ ‖v z‖ ^ 2
  rw [←hz,hzb]
end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ArrayObjects.Object.Rolled
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
lemma exists_raw_finite_levels_oai :
    ∃ ψ : RawLabel M → LabelOrbitVector,
      Measurable ψ ∧
      (positiveLevels (E.measure (M.parameterLaw 0)) ψ).Countable ∧
      (∀ᵐ u ∂M.parameterLaw 0, ∀ q, (u,q) ∈ S →
        ψ (u,q) ∈ positiveLevels (E.measure (M.parameterLaw 0)) ψ) ∧
      (∀ b : positiveLevels (E.measure (M.parameterLaw 0)) ψ,
        E.measure (M.parameterLaw 0) {z | ψ z = b.val} < ∞) ∧
      (∀ᵐ u ∂M.parameterLaw 0, ∀ b : positiveLevels (E.measure (M.parameterLaw 0)) ψ,
        {q | (u,q) ∈ S ∧ ψ (u,q) = b.val}.Finite) ∧
      MeasurePreserving labelShiftFirst ((E.measure (M.parameterLaw 0)).map ψ)
        ((E.measure (M.parameterLaw 0)).map ψ) ∧
      MeasurePreserving labelShiftSecond ((E.measure (M.parameterLaw 0)).map ψ)
        ((E.measure (M.parameterLaw 0)).map ψ) ∧
      (∀ᵐ p ∂M.parameterLaw 1, ∀ a, (p,a) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) →
        ψ (tupleParameter M p t,a t) = labelShiftFirst (ψ (tupleParameter M p s,a s))) ∧
      (∀ᵐ u ∂M.parameterLaw 0, ∀ q, (u,q) ∈ S →
        ψ (rawLabelTime M (u,q)) = labelShiftSecond (ψ (u,q))) := by
  obtain ⟨ψ,v,hψ,hzero,hpos,htr,htime,R,hRc,hR⟩ :=
    rawCounting_exists_orbit M Λ hM hk hL hm hind S hS E Eπ Eσ s t hst
  have hBc := positiveLevels_countable (E.measure (M.parameterLaw 0)) ψ R hRc hR
  let : Countable (positiveLevels (E.measure (M.parameterLaw 0)) ψ) := hBc.to_subtype
  have hb (b : positiveLevels (E.measure (M.parameterLaw 0)) ψ) :
      E.measure (M.parameterLaw 0) {z | ψ z = b.val} < ∞ := by
    apply finite_positive_level_mass _ ψ v (fun c => c (0,0))
      (Filter.Eventually.of_forall hzero) _ b
    filter_upwards [hpos] with z hz
    intro he
    rw [he,Complex.zero_re] at hz
    exact lt_irrefl _ hz
  refine ⟨ψ,hψ,hBc,E.ae_fibre_all _ (ae_mem_positiveLevels _ ψ R hRc hR),hb,?_,?_,?_,
    Eπ.ae_fibre_all _ htr,E.ae_fibre_all _ htime⟩
  · apply ae_all_iff.mpr
    intro b
    exact E.ae_finite_level _ {z | ψ z = b.val} (measurableSet_eq_fun hψ measurable_const) (hb b)
  · exact joining_transport_invariant _ ψ hψ _ (rawLabelSlot M s) (rawLabelSlot M t)
      (rawCounting_coordinate_preserving M Λ hk hm hind S hS E Eπ s)
      (rawCounting_coordinate_preserving M Λ hk hm hind S hS E Eπ t) labelShiftFirst htr
  · exact joining_transport_invariant _ ψ hψ _ id (rawLabelTime M) (MeasurePreserving.id _)
      (rawCounting_time_preserving M Λ s hL hm S hS E) labelShiftSecond htime
end ArrayObjects.Object.Rolled

end Rokhlin

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Rokhlin.ArrayObjects.Object.Rolled.exists_raw_finite_levels_oai.{u} := @OAI.Rokhlin.ArrayObjects.Object.Rolled.exists_raw_finite_levels_oai.{u}
