-- Prove2me | solution 2 for OAI.Rokhlin.ArrayObjects.Object.Rolled.exists_raw_finite_levels
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T01:48:44.221922+00:00
-- url     : https://prove2.me/submissions/3d43b4d1-e901-4264-810f-768b0ffb2b27

import Mathlib
import Definitions.Def_OAIQ3Ro002

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
attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.columnGroupKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.columnPairKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunArrαYOfNatNatComplexMemAddSubgroupLpENNRealSubmoduleRawSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunCellComplexMemAddSubgroupLpOfNatENNRealSubmoduleSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleColumnActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleCommonActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleRowActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatCellSlotLocal _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallCellSlotTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallYRawTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYColumnCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYRowCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.rowPairKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.splitRowKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Saturating.instNonemptyDataKind _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.arrayLaw_probability _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.localLaw_probability _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
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

namespace FiniteKernel

variable {ι X : Type*} {Y : ι → Type*}
  [Fintype ι] [MeasurableSpace X] [∀ i, MeasurableSpace (Y i)]

theorem map_pi {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)]
    (κ : ∀ i, Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)]
    (f : ∀ i, Y i → Z i) (hf : ∀ i, Measurable (f i)) :
    letI : ∀ i, IsMarkovKernel ((κ i).map (f i)) :=
      fun i => Kernel.IsMarkovKernel.map (κ i) (hf i)
    (pi κ).map (fun y i => f i (y i)) = pi (fun i => (κ i).map (f i)) := by
  ext x : 1
  rw [Kernel.map_apply _ (by fun_prop)]
  simp only [pi_apply, Kernel.map_apply _ (hf _)]
  exact Measure.pi_map_pi (fun i => (hf i).aemeasurable)

end FiniteKernel

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

namespace ConditionalTransport
variable {Ω Ω' A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

omit [MeasurableSpace Ω] in

theorem comap_le_of_factor {f : Ω → A} {g : Ω → C} {p : C → A}
    (hp : Measurable p) (h : f = p ∘ g) :
    MeasurableSpace.comap f inferInstance ≤ MeasurableSpace.comap g inferInstance := by
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hp.comap_le

end ConditionalTransport

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)


lemma row_reveal (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I) (a : I) (ha : a ∉ R) (n : ℕ) :
    HasCondDistrib (plane (n + 1) 0 a)
      (fun y => (amap M.par (n + 2) y, parents M R (n + 1) y))
      (((M.ownKernel (n + 1)).comap (plane (n + 1) 0 a)
        (measurable_plane _ _ _)).prodMkRight (R → Arr I M.Y (n + 1)))
      (M.law (n + 2)) := by
  let N := object M hM R hR a ha
  let e := objectExtension M hM R hR a ha
  let p : Arr I (Parameter M R) (n + 1) → Arr I M.U (n + 1) :=
    amap (fun z => z.1 a) (n + 1)
  have hpm : Measurable p := measurable_amap ((measurable_pi_apply a).comp measurable_fst) _
  have hs := hM.hasCondDistrib e n .parameter
    (amap M.par (n + 1)) (amap (parameter M R) (n + 1)) id p
    (measurable_amap M.measurable_par _) (measurable_amap (measurable_parameter M R) _)
    measurable_id hpm rfl rfl rfl
  have hp := ConditionalTransport.pullback
    (show MeasurePreserving (roll (Y := M.Y) (n + 1)) (M.law (n + 2)) (N.law (n + 1)) from
      ⟨(roll (n + 1)).measurable, rfl⟩)
    (measurable_amap (measurable_parameter M R) _) hs
  have h := hp.measurableEquiv_comp_right (parameterEquiv M R (n + 1))
  change HasCondDistrib ((id ∘ amap (Function.eval a) (n + 1)) ∘ roll (n + 1))
    (parameterEquiv M R (n + 1) ∘ amap (parameter M R) (n + 1) ∘ roll (n + 1))
    (((M.ownKernel (n + 1)).comap p hpm).comap (parameterEquiv M R (n + 1)).symm
      (parameterEquiv M R (n + 1)).symm.measurable) (M.law (n + 2)) at h
  rw [Function.id_comp, select_roll, parameterEquiv_observation] at h
  have hk : (((M.ownKernel (n + 1)).comap p hpm).comap
      (parameterEquiv M R (n + 1)).symm (parameterEquiv M R (n + 1)).symm.measurable) =
      (((M.ownKernel (n + 1)).comap (plane (n + 1) 0 a)
        (measurable_plane _ _ _)).prodMkRight (R → Arr I M.Y (n + 1))) := by
    ext z : 1
    change M.ownKernel (n + 1) (p ((parameterEquiv M R (n + 1)).symm z)) =
      M.ownKernel (n + 1) (plane (n + 1) 0 a z.1)
    congr 1
    funext v
    change z.1 (Fin.cons a v) = z.1 ((0 : Fin (n + 2)).insertNth a v)
    rw [Fin.insertNth_zero']
  rw [hk] at h
  exact h

theorem rows_conditional (hM : M.IsSaturated) (J : Finset I)
    (hJ : J ≠ Finset.univ) (n : ℕ) :
    HasCondDistrib (fun y => fun a : J => plane (n + 1) 0 (a : I) y)
      (amap M.par (n + 2))
      (FiniteKernel.pi (fun a : J => (M.ownKernel (n + 1)).comap
        (plane (n + 1) 0 (a : I)) (measurable_plane _ _ _))) (M.law (n + 2)) := by
  apply ConditionalReveal.finite_reveal (M.law (n + 2)) (amap M.par (n + 2))
    (measurable_amap M.measurable_par _)
    (fun a : I => plane (n + 1) 0 a)
    (fun a : I => (M.ownKernel (n + 1)).comap (plane (n + 1) 0 a)
      (measurable_plane _ _ _)) J
  intro R hRJ a ha haR
  have hstrict : R ⊂ J := (Finset.ssubset_iff_subset_ne).mpr ⟨hRJ, by
    intro he; subst R; exact haR ha⟩
  have hcardR := Finset.card_lt_card hstrict
  have hcardJ := Finset.card_lt_card
    ((Finset.ssubset_iff_subset_ne).mpr ⟨Finset.subset_univ J, hJ⟩)
  rw [Finset.card_univ] at hcardJ
  exact row_reveal M hM R (by omega) a haR n

end ArrayObjects.Object.Rolled

namespace ConditionalScreens
variable {Ω S Z O : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
  [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
  [MeasurableSpace O] [StandardBorelSpace O] [Nonempty O]

theorem reverse_screen {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : Ω → S} {z : Ω → Z} {o : Ω → O}
    (hs : Measurable s) (hz : Measurable z) (ho : Measurable o)
    (f : Z → S) (hf : Measurable f) (g : O → S) (hg : Measurable g)
    (hsz : s = f ∘ z) (hso : s = g ∘ o)
    (κ : Kernel S O) [IsMarkovKernel κ] (l : Kernel S Z) [IsMarkovKernel l]
    (hκ : HasCondDistrib o s κ μ)
    (hl : HasCondDistrib z o (l.comap g hg) μ) :
    HasCondDistrib o z (κ.comap f hf) μ := by
  have hl' : HasCondDistrib z (fun ω => (s ω, o ω)) (l.prodMkRight O) μ := by
    apply ConditionalTransport.recondition ho (hs.prodMk ho) hz hl
    · apply le_antisymm
      · exact ConditionalTransport.comap_le_of_factor measurable_snd rfl
      · apply ConditionalTransport.comap_le_of_factor (hg.prodMk measurable_id)
        simpa only [Function.comp_def, id_eq] using congrArg (fun v => fun ω => (v ω, o ω)) hso
    · filter_upwards [] with ω
      change l (g (o ω)) = l (s ω)
      rw [hso]; rfl
  have hh := screening hκ l hl'
  apply ConditionalTransport.recondition (hs.prodMk hz) hz ho hh
  · apply le_antisymm
    · apply ConditionalTransport.comap_le_of_factor (hf.prodMk measurable_id)
      simpa only [Function.comp_def, id_eq] using congrArg (fun v => fun ω => (v ω, z ω)) hsz
    · exact ConditionalTransport.comap_le_of_factor measurable_snd rfl
  · filter_upwards [] with ω
    change κ (s ω) = κ (f (z ω))
    rw [hsz]; rfl

end ConditionalScreens

namespace FiniteKernel
variable {ι : Type*} [Fintype ι] {Y S : ι → Type*}
  [∀ i, MeasurableSpace (Y i)] [∀ i, StandardBorelSpace (Y i)] [∀ i, Nonempty (Y i)]
  [∀ i, MeasurableSpace (S i)]

theorem independent_observation (μ : ∀ i, Measure (Y i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : ∀ i, Y i → S i)
    (hf : ∀ i, Measurable (f i)) :
    HasCondDistrib (id : (∀ i, Y i) → (∀ i, Y i)) (fun y i => f i (y i))
      (pi (fun i => (condDistrib id (f i) (μ i)).comap (Function.eval i)
        (measurable_pi_apply i))) (Measure.pi μ) := by
  refine ⟨((Measurable.of_eval (fun i => (hf i).comp (measurable_pi_apply i))).prodMk
    measurable_id).aemeasurable, ?_⟩
  let (i : ι) : IsProbabilityMeasure ((μ i).map (f i)) :=
    (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (hf i).aemeasurable
  apply (zipEquiv S Y).measurableEmbedding.map_injective
  rw [Measure.pi_map_pi (fun i => (hf i).aemeasurable), compProd_pi]
  rw [Measure.map_map (zipEquiv S Y).measurable (by fun_prop)]
  change (Measure.pi μ).map (fun y i => (f i (y i), y i)) =
    Measure.pi (fun i => (μ i).map (f i) ⊗ₘ condDistrib id (f i) (μ i))
  calc
    _ = Measure.pi (fun i => (μ i).map (fun y => (f i y, y))) :=
      Measure.pi_map_pi (fun i => ((hf i).prodMk measurable_id).aemeasurable)
    _ = _ := ?_
  congr 1
  funext i
  exact (compProd_map_condDistrib (μ := μ i) (X := f i)
    (Y := id) measurable_id.aemeasurable).symm

end FiniteKernel

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma outside_row_screen (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (a j₀ : I) (n : ℕ) :
    HasCondDistrib (plane (n + 1) 0 a) (planes (n + 1) (Outside j₀))
      ((condDistrib id (planes n (Outside j₀)) (M.law (n + 1))).comap
        (fun o : Outside j₀ → Arr I M.Y (n + 1) => fun j => plane n 0 a (o j))
        (Measurable.of_eval (fun j => (measurable_plane _ _ _).comp (measurable_pi_apply j))))
      (M.law (n + 2)) := by
  have hR : (∅ : Finset I).card + 2 ≤ Fintype.card I := by simpa using hI
  let N := object M hM ∅ hR a (Finset.notMem_empty a)
  let e := objectExtension M hM ∅ hR a (Finset.notMem_empty a)
  let p : (Outside j₀ → Arr I (State M) n) → (Outside j₀ → Arr I M.Y n) :=
    fun o j => amap (Function.eval a) n (o j)
  have hpm : Measurable p := Measurable.of_eval (fun j =>
    (measurable_amap (measurable_pi_apply a) n).comp (measurable_pi_apply j))
  have hs := hM.hasCondDistrib e n (.outside j₀)
    (planes n (Outside j₀)) (planes (Y := State M) n (Outside j₀))
    (id : Arr I M.Y (n + 1) → Arr I M.Y (n + 1)) p
    (measurable_planes _ _) (measurable_planes _ _) measurable_id hpm rfl rfl rfl
  have hp := ConditionalTransport.pullback
    (show MeasurePreserving (roll (Y := M.Y) (n + 1)) (M.law (n + 2)) (N.law (n + 1)) from
      ⟨(roll (n + 1)).measurable, rfl⟩) (measurable_planes _ _) hs
  let E : (Outside j₀ → Arr I (State M) n) ≃ᵐ (Outside j₀ → Arr I M.Y (n + 1)) :=
    MeasurableEquiv.piCongrRight (fun _ => (roll n).symm)
  change HasCondDistrib ((id ∘ amap (Function.eval a) (n + 1)) ∘ roll (n + 1))
    (planes (Y := State M) n (Outside j₀) ∘ roll (n + 1))
    ((condDistrib (id : Arr I M.Y (n + 1) → Arr I M.Y (n + 1))
      (planes n (Outside j₀)) (M.law (n + 1))).comap p hpm) (M.law (n + 2)) at hp
  have h := hp.measurableEquiv_comp_right E
  change HasCondDistrib ((id ∘ amap (Function.eval a) (n + 1)) ∘ roll (n + 1))
    (E ∘ planes n (Outside j₀) ∘ roll (n + 1))
    (((condDistrib id (planes n (Outside j₀)) (M.law (n + 1))).comap p hpm).comap
      E.symm E.symm.measurable) (M.law (n + 2)) at h
  have he : E ∘ planes n (Outside j₀) ∘ roll (n + 1) = planes (n + 1) (Outside j₀) := by
    rw [planes_roll]
    funext y j
    change (roll n).symm (roll n (planes (n + 1) (Outside j₀) y j)) = _
    exact (roll n).symm_apply_apply _
  rw [Function.id_comp, select_roll, he] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext o : 1
  change condDistrib id (planes n (Outside j₀)) (M.law (n + 1))
    (fun j => plane n 0 a (o j)) =
    condDistrib id (planes n (Outside j₀)) (M.law (n + 1)) (p (E.symm o))
  congr 1
  funext j
  exact (congrFun (select_roll n a) (o j)).symm

omit [DecidableEq I] in

lemma plane_first_last (n : ℕ) (a j : I) :
    plane (Y := M.Y) n 0 a ∘ plane (n + 1) (Fin.last (n + 1)) j =
      plane n (Fin.last n) j ∘ plane (n + 1) 0 a := by
  funext y v
  change y ((Fin.last (n + 1)).insertNth j ((0 : Fin (n + 1)).insertNth a v)) =
    y ((0 : Fin (n + 2)).insertNth a ((Fin.last n).insertNth j v))
  simp only [Fin.insertNth_last', Fin.insertNth_zero']
  rw [cons_snoc]

theorem columns_given_row (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (a j₀ : I) (n : ℕ) :
    HasCondDistrib (planes (n + 1) (Outside j₀)) (plane (n + 1) 0 a)
      (FiniteKernel.pi (fun j : Outside j₀ =>
        (condDistrib id (plane n 0 a) (M.law (n + 1))).comap
          (plane n (Fin.last n) j) (measurable_plane _ _ _))) (M.law (n + 2)) := by
  let f : Arr I M.Y (n + 1) → Outside j₀ → Arr I M.Y n := planes n (Outside j₀)
  let g : (Outside j₀ → Arr I M.Y (n + 1)) → Outside j₀ → Arr I M.Y n :=
    fun o j => plane n 0 a (o j)
  have hf : Measurable f := measurable_planes _ _
  have hg : Measurable g := Measurable.of_eval (fun j =>
    (measurable_plane _ _ _).comp (measurable_pi_apply j))
  let κ := FiniteKernel.pi (fun _j : Outside j₀ =>
    (condDistrib (id : Arr I M.Y (n + 1) → Arr I M.Y (n + 1))
      (plane n 0 a) (M.law (n + 1))).comap
        (Function.eval _j) (measurable_pi_apply _j))
  let l := condDistrib (id : Arr I M.Y (n + 1) → Arr I M.Y (n + 1)) f (M.law (n + 1))
  have hJ : Outside j₀ ≠ Finset.univ := by
    intro he
    have hj : j₀ ∈ Outside j₀ := he ▸ Finset.mem_univ j₀
    simp only [Outside, Finset.mem_erase, ne_eq, not_true_eq_false, false_and] at hj
  have ho : MeasurePreserving (planes (n + 1) (Outside j₀)) (M.law (n + 2))
      (Measure.pi (fun _ : Outside j₀ => M.law (n + 1))) :=
    ⟨measurable_planes _ _, M.proper _ _ hJ⟩
  have hk := ConditionalTransport.pullback ho hg
    (FiniteKernel.independent_observation (fun _ : Outside j₀ => M.law (n + 1))
      (fun _ => plane n 0 a) (fun _ => measurable_plane _ _ _))
  have hs : g ∘ planes (n + 1) (Outside j₀) = f ∘ plane (n + 1) 0 a := by
    funext y j
    exact congrFun (plane_first_last M n a j) y
  have h := ConditionalScreens.reverse_screen
    (hg.comp (measurable_planes _ _)) (measurable_plane _ _ _) (measurable_planes _ _)
    f hf g hg hs rfl κ l hk (outside_row_screen M hM hI a j₀ n)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext z : 1
  rfl

end ArrayObjects.Object.Rolled

namespace FiniteKernel
lemma map_eval {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    (κ : ∀ i, Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)] (i : ι) :
    (pi κ).map (Function.eval i) = κ i := by
  ext x : 1
  rw [Kernel.map_apply _ (measurable_pi_apply i)]
  exact (measurePreserving_eval (fun j => κ j x) i).map_eq
end FiniteKernel

namespace ArrayObjects.Object
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in
lemma plane_conditional (hI : 2 ≤ Fintype.card I) (n : ℕ) (a : I) :
    HasCondDistrib (plane n (Fin.last n) a) (amap M.par (n + 1))
      ((M.ownKernel n).comap (plane n (Fin.last n) a) (measurable_plane _ _ _))
      (M.law (n + 1)) := by
  have hproper : ({a} : Finset I) ≠ Finset.univ := by
    intro he
    have hc := congrArg Finset.card he
    simp only [Finset.card_singleton, Finset.card_univ] at hc
    omega
  have h := (M.planes_conditional n {a} hproper).comp_left
    (measurable_pi_apply (⟨a, Finset.mem_singleton_self a⟩ : ({a} : Finset I)))
  rw [FiniteKernel.map_eval] at h
  exact h

omit [DecidableEq I] in

lemma column_parameter_given_cell (hI : 2 ≤ Fintype.card I) (a : I) :
    HasCondDistrib (amap M.par 1) (plane 0 0 a)
      ((M.parameterCoordinateKernel a).comap (amap M.par 0)
        (measurable_amap M.measurable_par 0)) (M.law 1) := by
  have hc : HasCondDistrib (id : Arr I M.U 1 → Arr I M.U 1) (plane 0 0 a)
      (M.parameterCoordinateKernel a) (M.parameterLaw 1) :=
    ⟨((measurable_plane _ _ _).prodMk measurable_id).aemeasurable,
      (compProd_map_condDistrib measurable_id.aemeasurable).symm⟩
  have hq := ConditionalTransport.pullback
    (show MeasurePreserving (amap M.par 1) (M.law 1) (M.parameterLaw 1) from
      ⟨measurable_amap M.measurable_par _, rfl⟩) (measurable_plane _ _ _) hc
  exact ConditionalScreens.reverse_screen
    (s := amap M.par 0 ∘ plane 0 0 a) (z := plane 0 0 a) (o := amap M.par 1)
    ((measurable_amap M.measurable_par 0).comp (measurable_plane _ _ _))
    (measurable_plane _ _ _) (measurable_amap M.measurable_par _)
    (amap M.par 0) (measurable_amap M.measurable_par _) (plane 0 0 a)
    (measurable_plane _ _ _) rfl rfl (M.parameterCoordinateKernel a) (M.ownKernel 0)
    hq (M.plane_conditional hI 0 a)

omit [DecidableEq I] in

lemma shared_parameter_kernel (hI : 2 ≤ Fintype.card I) (a : I) :
    (fun s => (condDistrib (id : Arr I M.Y 1 → Arr I M.Y 1) (plane 0 0 a)
      (M.law 1) s).map (amap M.par 1)) =ᵐ[M.law 0]
    fun s => M.parameterCoordinateKernel a (amap M.par 0 s) := by
  let κ := condDistrib (id : Arr I M.Y 1 → Arr I M.Y 1) (plane 0 0 a) (M.law 1)
  have h : HasCondDistrib id (plane 0 0 a) κ (M.law 1) :=
    ⟨((measurable_plane _ _ _).prodMk measurable_id).aemeasurable,
      (compProd_map_condDistrib measurable_id.aemeasurable).symm⟩
  have hm := h.comp_left (measurable_amap M.measurable_par 1)
  have he := Kernel.ae_eq_of_compProd_eq
    (hm.map_eq.symm.trans (M.column_parameter_given_cell hI a).map_eq)
  rw [show (M.law 1).map (plane 0 0 a) = M.law 0 from M.consistent 0 0 a] at he
  exact he.mono (fun s hs => by
    simpa only [Kernel.map_apply _ (measurable_amap M.measurable_par _), Kernel.comap_apply] using hs)

end ArrayObjects.Object

namespace ConditionalTransport
variable {Ω Ω' A B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [MeasurableSpace B]

theorem pushforward {P : Measure Ω} {Q : Measure Ω'} {f : Ω → Ω'}
    {E : Ω' → A} {O : Ω' → B} {κ : Kernel A B}
    (hf : MeasurePreserving f P Q) (hE : Measurable E) (hO : Measurable O)
    (h : HasCondDistrib (O ∘ f) (E ∘ f) κ P) : HasCondDistrib O E κ Q := by
  refine ⟨(hE.prodMk hO).aemeasurable, ?_⟩
  have he : P.map (E ∘ f) = Q.map E := by
    rw [← Measure.map_map hE hf.measurable, hf.map_eq]
  have hj : P.map (fun ω => (E (f ω), O (f ω))) = Q.map (fun ω => (E ω, O ω)) := by
    change P.map ((fun ω => (E ω, O ω)) ∘ f) = _
    rw [← Measure.map_map (hE.prodMk hO) hf.measurable, hf.map_eq]
  rw [← he]
  exact hj.symm.trans h.map_eq
end ConditionalTransport

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem columns_parameter_given_row (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (a j₀ : I) :
    HasCondDistrib (fun y => fun j : Outside j₀ => amap M.par 1 (planes 1 (Outside j₀) y j))
      (amap M.par 1 ∘ plane 1 0 a)
      (FiniteKernel.pi (fun j : Outside j₀ => (M.parameterCoordinateKernel a).comap
        (plane 0 0 j) (measurable_plane _ _ _))) (M.law 2) := by
  let κ := condDistrib (id : Arr I M.Y 1 → Arr I M.Y 1) (plane 0 0 a) (M.law 1)
  let η := FiniteKernel.pi (fun j : Outside j₀ => (M.parameterCoordinateKernel a).comap
    (plane 0 0 j) (measurable_plane _ _ _))
  have h := (columns_given_row M hM hI a j₀ 0).comp_left
    (Measurable.of_eval (fun j => (measurable_amap M.measurable_par 1).comp
      (measurable_pi_apply j)))
  simp only [Function.comp_def] at h
  rw [FiniteKernel.map_pi _ _ (fun _ => measurable_amap M.measurable_par 1)] at h
  have he : ∀ᵐ z ∂M.law 1, ∀ j : Outside j₀,
      (κ (plane 0 0 j z)).map (amap M.par 1) =
        M.parameterCoordinateKernel a (amap M.par 0 (plane 0 0 j z)) := by
    rw [ae_all_iff]
    intro j
    exact (show MeasurePreserving (plane 0 0 (j : I)) (M.law 1) (M.law 0) from
      ⟨measurable_plane _ _ _, M.consistent 0 0 j⟩).quasiMeasurePreserving.ae_eq_comp
      (M.shared_parameter_kernel hI a)
  have hk : HasCondDistrib
      (fun y => fun j : Outside j₀ => amap M.par 1 (planes 1 (Outside j₀) y j))
      (plane 1 0 a) (η.comap (amap M.par 1) (measurable_amap M.measurable_par 1))
      (M.law 2) := by
    refine ⟨h.aemeasurable, h.map_eq.trans (Measure.compProd_congr ?_)⟩
    rw [M.consistent 1 0 a]
    filter_upwards [he] with z hz
    change Measure.pi (fun j : Outside j₀ =>
      ((κ.comap (plane 0 (Fin.last 0) j) (measurable_plane _ _ _)).map (amap M.par 1)) z) =
      Measure.pi (fun j : Outside j₀ => M.parameterCoordinateKernel a
        (plane 0 0 j (amap M.par 1 z)))
    congr 1
    funext j
    rw [Kernel.map_apply _ (measurable_amap M.measurable_par _), Kernel.comap_apply,
      Fin.last_zero]
    exact hz j
  exact hk.comp_right

theorem parameter_geometry_outside (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (a j₀ : I) :
    HasCondDistrib (planes 1 (Outside j₀)) (plane 1 0 a)
      (FiniteKernel.pi (fun j : Outside j₀ => (M.parameterCoordinateKernel a).comap
        (plane 0 0 j) (measurable_plane _ _ _))) (M.parameterLaw 2) := by
  apply ConditionalTransport.pushforward
    (show MeasurePreserving (amap M.par 2) (M.law 2) (M.parameterLaw 2) from
      ⟨measurable_amap M.measurable_par _, rfl⟩)
    (measurable_plane _ _ _) (measurable_planes _ _)
  exact columns_parameter_given_row M hM hI a j₀

theorem parameter_geometry (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (a : I) (J : Finset I) (hJ : J ≠ Finset.univ) :
    HasCondDistrib (planes 1 J) (plane 1 0 a)
      (FiniteKernel.pi (fun j : J => (M.parameterCoordinateKernel a).comap
        (plane 0 0 j) (measurable_plane _ _ _))) (M.parameterLaw 2) := by
  have hex : ∃ j₀ : I, j₀ ∉ J := by
    by_contra he
    push Not at he
    exact hJ (Finset.eq_univ_iff_forall.mpr he)
  obtain ⟨j₀, hj₀⟩ := hex
  let e : J ↪ Outside j₀ :=
    ⟨fun j => ⟨j, by
      simp only [Outside, Finset.mem_erase, Finset.mem_univ, and_true]
      exact fun he => hj₀ (he ▸ j.property)⟩,
      fun _ _ he => Subtype.ext (congrArg (fun z : Outside j₀ => (z : I)) he)⟩
  have h := (parameter_geometry_outside M hM hI a j₀).comp_left
    (Measurable.of_eval (fun i => measurable_pi_apply (e i)))
  rw [FiniteKernel.pi_precomp] at h
  exact h

end ArrayObjects.Object.Rolled

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

namespace ConditionalFibres
variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [StandardBorelSpace Y]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {u : Ω → U} {x : Ω → X} {y : Ω → Y}
  {η : Kernel U Ω} [IsMarkovKernel η] {κ : Kernel (U × X) Y} [IsMarkovKernel κ]

theorem marginal (hx : Measurable x) (hη : HasCondDistrib id u η μ)
    {α : Kernel U X} [IsMarkovKernel α] (hα : HasCondDistrib x u α μ) :
    ∀ᵐ a ∂μ.map u, MeasurePreserving x (η a) (α a) := by
  let : IsMarkovKernel (η.map x) := Kernel.IsMarkovKernel.map η hx
  have he : η.map x =ᵐ[μ.map u] α :=
    Kernel.ae_eq_of_compProd_eq ((hη.comp_left hx).map_eq.symm.trans hα.map_eq)
  filter_upwards [he] with a ha
  exact ⟨hx, (Kernel.map_apply η hx a).symm.trans ha⟩

end ConditionalFibres

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

lemma operator_adjoint (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ) :
    (operator hx hy).adjoint = operator hy hx := by simp [operator]

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

lemma inner_operator (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    inner ℂ g (operator hx hy h) = ∫ ω, inner ℂ (g (x ω)) (h (y ω)) ∂μ := by
  change inner ℂ g ((pull hx).adjoint (pull hy h)) = _
  rw [adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving g hx, Lp.coeFn_compMeasurePreserving h hy]
    with ω hg hh
  change inner ℂ (Lp.compMeasurePreserving x hx g ω) (Lp.compMeasurePreserving y hy h ω) = _
  rw [hg, hh]
  rfl

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
open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u
variable {I : Type u} [Fintype I] [retained10 : DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma row_marginal_fibre (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I) (i : I) :
    ∀ᵐ e ∂M.parameterLaw 2, MeasurePreserving (plane 1 0 i) (M.ownKernel 2 e)
      (M.ownKernel 1 (plane 1 0 i e)) := by
  have hproper : ({i} : Finset I) ≠ Finset.univ := by
    intro he
    have := congrArg Finset.card he
    simp only [Finset.card_singleton,Finset.card_univ] at this
    omega
  have h := (rows_conditional M hM {i} hproper 0).comp_left
    (measurable_pi_apply (⟨i,Finset.mem_singleton_self i⟩ : ({i} : Finset I)))
  rw [FiniteKernel.map_eval] at h
  exact ConditionalFibres.marginal (measurable_plane _ _ _)
    (M.ownKernel_conditional 2) h

omit [DecidableEq I] in
lemma column_marginal_fibre (hI : 2 ≤ Fintype.card I) (i : I) :
    ∀ᵐ e ∂M.parameterLaw 2, MeasurePreserving (plane 1 (Fin.last 1) i) (M.ownKernel 2 e)
      (M.ownKernel 1 (plane 1 (Fin.last 1) i e)) := by
  exact ConditionalFibres.marginal (measurable_plane _ _ _) (M.ownKernel_conditional 2)
    (M.plane_conditional hI 1 i)

end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Set
section
lemma iIndepFun_map_iff_measurable {A B J C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [Fintype J] (μ : Measure A) [IsProbabilityMeasure μ]
    (f : B → J → C) (g : A → B) (hf : ∀ j, Measurable (fun b => f b j)) (hg : Measurable g) :
    iIndepFun (fun j b => f b j) (μ.map g) ↔ iIndepFun (fun j a => f (g a) j) μ := by
  let : IsProbabilityMeasure (μ.map g) := (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hg.aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun j => (hf j).aemeasurable),
    iIndepFun_iff_map_fun_eq_pi_map (f := fun j a => f (g a) j) (fun j => ((hf j).comp hg).aemeasurable)]
  simp only [Measure.map_map (Measurable.of_eval hf) hg,
    Measure.map_map (hf _) hg]
  rfl
end
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

section
open MeasureTheory ProbabilityTheory
namespace FiniteKernel
variable {ι S Y : Type*} [Fintype ι] [MeasurableSpace S] [MeasurableSpace Y]
lemma map_pair (κ : ι → Kernel S Y) [∀ i, IsMarkovKernel (κ i)]
    (i j : ι) (hij : i ≠ j) :
    (pi κ).map (fun y => (y i,y j)) = κ i ×ₖ κ j := by
  ext s : 1
  rw [Kernel.map_apply _ ((measurable_pi_apply i).prodMk (measurable_pi_apply j)),pi_apply,Kernel.prod_apply]
  have hi : iIndepFun (fun i : ι => Function.eval i) (Measure.pi (fun i => κ i s)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  rw [(hi.indepFun hij).map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable,
    (measurePreserving_eval (fun i => κ i s) i).map_eq,
    (measurePreserving_eval (fun i => κ i s) j).map_eq]
end FiniteKernel
namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
lemma parameter_pair_geometry (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (a j t : I) (hjt : j ≠ t) :
    HasCondDistrib (fun e => (plane 1 (Fin.last 1) j e,plane 1 (Fin.last 1) t e))
      (plane 1 0 a)
      ((M.parameterCoordinateKernel a).comap (plane 0 0 j) (measurable_plane _ _ _) ×ₖ
       (M.parameterCoordinateKernel a).comap (plane 0 0 t) (measurable_plane _ _ _))
      (M.parameterLaw 2) := by
  have hpair : ({j,t} : Finset I) ≠ Finset.univ := by
    intro h
    have := pair_complement_nonempty hk j t
    simp only [h,Finset.compl_univ,Finset.not_nonempty_empty] at this
  let j' : ({j,t} : Finset I) := ⟨j,by simp⟩
  let t' : ({j,t} : Finset I) := ⟨t,by simp⟩
  have hne : j' ≠ t' := fun h => hjt (congrArg Subtype.val h)
  have h := (parameter_geometry M hM (by omega) a {j,t} hpair).comp_left
    ((measurable_pi_apply j').prodMk (measurable_pi_apply t'))
  rw [FiniteKernel.map_pair _ j' t' hne] at h
  exact h
end ArrayObjects.Object.Rolled
end

namespace ArrayObjects.Object.Rolled

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

section CircleSlotIndicators

attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in
lemma parameter_cell_commute (a j : I) (e : Arr I M.U 2) :
    tupleParameter M (plane 1 0 a e) j = tupleParameter M (plane 1 (Fin.last 1) j e) a := by
  funext x
  simp only [tupleParameter,plane]
  congr 1
  funext t
  fin_cases t <;> rfl

end CircleSlotIndicators


universe u
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)
lemma exactCode_of_circle_tuple {p : P} {a : I → HilbertCode κ}
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hb : ∀ i, (a i).base = u p i)
    (hcan : ∀ i, (a i).IsCanonical ∧ (a i).IsUnimodular)
    (c : Circle)
    (he : ∀ᵐ y ∂Λ p, ∏ i, HilbertCode.circleRep (a i) (y i) = c) :
    (p,a) ∈ exactCodeSet κ Λ u := by
  refine ⟨hb,hcan,?_⟩
  have hrep (i) : ∀ᵐ y ∂Λ p,
      (HilbertCode.circleRep (a i) (y i) : ℂ) = HilbertCode.representative (a i,y i) := by
    have h := HilbertCode.circleRep_ae (a i) (hcan i).2
    rw [hb i] at h
    exact (hm i).quasiMeasurePreserving.ae h
  have hmean : (fun y => ∏ i, HilbertCode.representative (a i,y i)) =ᵐ[Λ p]
      fun _ => (c : ℂ) := by
    filter_upwards [he,ae_all_iff.mpr hrep] with y hy hr
    calc
      _ = ∏ i, (HilbertCode.circleRep (a i) (y i) : ℂ) :=
        Finset.prod_congr rfl (fun i _ => (hr i).symm)
      _ = ((∏ i, HilbertCode.circleRep (a i) (y i) : Circle) : ℂ) :=
        (map_prod Circle.coeHom (fun i => HilbertCode.circleRep (a i) (y i)) Finset.univ).symm
      _ = _ := congrArg (fun z : Circle => (z : ℂ)) hy
  change ‖∫ y, ∏ i, HilbertCode.representative (a i,y i) ∂Λ p‖ = 1
  rw [integral_congr_ae hmean,integral_const,probReal_univ,one_smul,Circle.norm_coe]
end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
attribute [local instance] OAI.Rokhlin.instMeasurableSpaceCircle_solutions_5
lemma independent_circle_product_constant
    (f : I → Ω → Circle) (hf : ∀ i, Measurable (f i))
    (hind : iIndepFun f μ) (c : Circle)
    (he : ∀ᵐ x ∂μ, ∏ i, f i x = c) :
    ∀ i, ∃ d : Circle, f i =ᵐ[μ] fun _ => d := by
  classical
  let g : I → Ω → ℂ := fun i x => (f i x : ℂ)
  have hg (i) : Measurable (g i) := measurable_subtype_coe.comp (hf i)
  have hgi : iIndepFun g μ := by
    exact hind.comp (fun (_ : I) (z : Circle) => (z : ℂ)) (fun _ => measurable_subtype_coe)
  have hprod : (∏ i, ∫ x, g i x ∂μ) = (c : ℂ) := by
    rw [←hgi.integral_fun_prod_eq_prod_integral (fun i => (hg i).aestronglyMeasurable)]
    have he' : (fun x => ∏ i, g i x) =ᵐ[μ] fun _ => (c : ℂ) := by
      filter_upwards [he] with x hx
      exact (map_prod Circle.coeHom _ _).symm.trans (congrArg (fun z : Circle => (z : ℂ)) hx)
    rw [integral_congr_ae he',integral_const,probReal_univ,one_smul]
  have hle (i) : ‖∫ x, g i x ∂μ‖ ≤ 1 := by
    calc
      _ ≤ ∫ x, ‖g i x‖ ∂μ := norm_integral_le_integral_norm _
      _ = 1 := by simp only [g,Circle.norm_coe,integral_const,probReal_univ,smul_eq_mul,one_mul]
  have hnorm : (∏ i, ‖∫ x, g i x ∂μ‖) = 1 := by
    rw [←norm_prod,hprod,Circle.norm_coe]
  intro i
  have hone : ‖∫ x, g i x ∂μ‖ = 1 := by
    apply le_antisymm (hle i)
    calc
      1 = ‖∫ x, g i x ∂μ‖ * ∏ j ∈ Finset.univ.erase i, ‖∫ x, g j x ∂μ‖ := by
        rw [mul_comm,Finset.prod_erase_mul _ _ (Finset.mem_univ i),hnorm]
      _ ≤ ‖∫ x, g i x ∂μ‖ * 1 := mul_le_mul_of_nonneg_left
        (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun j _ => hle j)) (norm_nonneg _)
      _ = _ := mul_one _
  have heq : g i =ᵐ[μ] fun _ => ∫ x, g i x ∂μ := by
    rcases ae_eq_const_or_norm_integral_lt_of_norm_le_const
      (μ := μ) (f := g i) (C := (1 : ℝ))
      (Filter.Eventually.of_forall fun x => (Circle.norm_coe (f i x)).le) with h | h
    · simpa only [average_eq_integral,Function.const_def] using h
    · simp only [hone,probReal_univ,one_mul,lt_self_iff_false] at h
  refine ⟨⟨∫ x, g i x ∂μ,mem_sphere_zero_iff_norm.mpr hone⟩,?_⟩
  exact heq.mono fun _ h => Circle.coe_injective h
end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] OAI.Rokhlin.instMeasurableSpaceCircle_solutions_6
local instance instBorelSpaceCircle_solutions_6 : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))
variable {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype J]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma circle_square_consistency [DecidableEq I]
    (f : I → J → Ω → Circle) (hf : ∀ i j, Measurable (f i j))
    (a : I)
    (hind : iIndepFun (fun i : (Finset.univ.erase a : Finset I) =>
      fun x => ∏ j, f i j x) μ)
    (c : J → Circle) (hc : ∀ j, ∀ᵐ x ∂μ, ∏ i, f i j x = c j)
    (d : Circle) (hd : ∀ᵐ x ∂μ, ∏ j, f a j x = d) :
    ∀ i, ∃ e : Circle, ∀ᵐ x ∂μ, ∏ j, f i j x = e := by
  have ht : ∀ᵐ x ∂μ, ∏ i, ∏ j, f i j x = ∏ j, c j := by
    filter_upwards [ae_all_iff.mpr hc] with x hx
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl (fun j _ => hx j)
  have hp : ∀ᵐ x ∂μ,
      ∏ i : (Finset.univ.erase a : Finset I), ∏ j, f i j x = (∏ j, c j) / d := by
    filter_upwards [ht,hd] with x htx hdx
    rw [Finset.prod_coe_sort (Finset.univ.erase a) (fun i => ∏ j, f i j x)]
    apply (eq_div_iff_mul_eq').mpr
    rw [←hdx,Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
    exact htx
  have hfm (i : (Finset.univ.erase a : Finset I)) : Measurable (fun x => ∏ j, f i j x) :=
    Finset.measurable_prod _ (fun j _ => hf i j)
  have he := independent_circle_product_constant μ
    (fun i : (Finset.univ.erase a : Finset I) => fun x => ∏ j, f i j x)
    hfm hind ((∏ j, c j) / d) hp
  intro i
  by_cases hi : i = a
  · subst i; exact ⟨d,hd⟩
  · exact he ⟨i,Finset.mem_erase.mpr ⟨hi,Finset.mem_univ i⟩⟩
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma whole_rows_independent_fibre (hM : M.IsSaturated) (a : I) :
    ∀ᵐ e ∂M.parameterLaw 2, iIndepFun
      (fun i : (Finset.univ.erase a : Finset I) => plane 1 0 (i : I)) (M.ownKernel 2 e) := by
  have hp := ConditionalFibres.marginal (measurable_parents M (Finset.univ.erase a) 1)
    (M.ownKernel_conditional 2)
    (rows_conditional M hM (Finset.univ.erase a) (by
      intro he; have := Finset.mem_univ a; rw [←he] at this; exact Finset.notMem_erase a _ this) 0)
  filter_upwards [hp] with e he
  change MeasurePreserving _ _ (Measure.pi (fun i : (Finset.univ.erase a : Finset I) =>
    M.ownKernel 1 (plane 1 0 (i : I) e))) at he
  have h := iIndepFun_pi (μ := fun i : (Finset.univ.erase a : Finset I) =>
    M.ownKernel 1 (plane 1 0 (i : I) e)) (fun _ => measurable_id.aemeasurable)
  rw [←he.map_eq] at h
  exact (iIndepFun_map_iff_measurable (M.ownKernel 2 e)
    (fun (z : ∀ _ : (Finset.univ.erase a : Finset I), Arr I M.Y 1) i => z i)
    (fun y i => plane 1 0 (i : I) y) (fun i => measurable_pi_apply i)
    (measurable_parents M _ _)).mp h

lemma rawSquare_marginals (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M) :
    ∀ᵐ e ∂M.parameterLaw 2, (∀ i, MeasurePreserving
      (rawTuple M ∘ plane 1 0 i) (M.ownKernel 2 e) (Λ (plane 1 0 i e))) ∧
      (∀ j, MeasurePreserving (rawTuple M ∘ plane 1 (Fin.last 1) j)
        (M.ownKernel 2 e) (Λ (plane 1 (Fin.last 1) j e))) := by
  have hrow (i : I) : ∀ᵐ e ∂M.parameterLaw 2,
      Λ (plane 1 0 i e) = rawTupleKernel M (plane 1 0 i e) :=
    (show MeasurePreserving (plane 1 0 i) (M.parameterLaw 2) (M.parameterLaw 1) from
      ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩).quasiMeasurePreserving.ae hL
  have hcol (j : I) : ∀ᵐ e ∂M.parameterLaw 2,
      Λ (plane 1 (Fin.last 1) j e) = rawTupleKernel M (plane 1 (Fin.last 1) j e) :=
    (show MeasurePreserving (plane 1 (Fin.last 1) j) (M.parameterLaw 2) (M.parameterLaw 1) from
      ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩).quasiMeasurePreserving.ae hL
  filter_upwards [ae_all_iff.mpr hrow,ae_all_iff.mpr hcol,
    ae_all_iff.mpr (row_marginal_fibre M hM hI),ae_all_iff.mpr (column_marginal_fibre M hI)]
    with e hr hc hmr hmc
  constructor
  · intro i
    rw [hr i]
    exact (MeasurePreserving.mk (measurable_rawTuple M)
      (Kernel.map_apply _ (measurable_rawTuple M) _).symm).comp (hmr i)
  · intro j
    rw [hc j]
    exact (MeasurePreserving.mk (measurable_rawTuple M)
      (Kernel.map_apply _ (measurable_rawTuple M) _).symm).comp (hmc j)

lemma rawSquare_exact_consistency (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j))) :
    ∀ᵐ e ∂M.parameterLaw 2, ∀ (q : I → I → HilbertCode (M.ownKernel 0)) (a : I),
      (∀ j, (plane 1 (Fin.last 1) j e,fun i => q i j) ∈
        exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)) →
      (plane 1 0 a e,q a) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) →
      ∀ i, (plane 1 0 i e,q i) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) := by
  filter_upwards [rawSquare_marginals M hM hI Λ hL,
    ae_all_iff.mpr (whole_rows_independent_fibre M hM)] with e hmar hind q a hcodes hr
  let f : I → I → Arr I M.Y 2 → Circle := fun i j y =>
    HilbertCode.circleRep (q i j) (missingRow M 0 j i y)
  have hf (i j : I) : Measurable (f i j) :=
    (HilbertCode.measurable_circleRep_fixed _).comp (measurable_missingRow M _ _ _)
  choose c hconst using fun j => exactCode_circle_tuple (M.ownKernel 0) Λ (tupleParameter M)
    (hm _) (hcodes j)
  have hcol (j : I) : ∀ᵐ y ∂M.ownKernel 2 e, ∏ i, f i j y = c j := by
    have h := (hmar.2 j).quasiMeasurePreserving.ae (hconst j)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr! 3 with y i
    exact congrArg (HilbertCode.circleRep (q i j)) (congrFun (plane_first_last M 0 i j) y).symm
  obtain ⟨d,hd⟩ := exactCode_circle_tuple (M.ownKernel 0) Λ (tupleParameter M) (hm _) hr
  have hrow : ∀ᵐ y ∂M.ownKernel 2 e, ∏ j, f a j y = d :=
    (hmar.1 a).quasiMeasurePreserving.ae hd
  have hi : iIndepFun (fun i : (Finset.univ.erase a : Finset I) => fun y => ∏ j, f i j y)
      (M.ownKernel 2 e) := by
    exact (hind a).comp (fun (i : (Finset.univ.erase a : Finset I)) (y : Arr I M.Y 1) =>
      ∏ j, HilbertCode.circleRep (q i j) (plane 0 0 j y)) (fun i =>
        Finset.measurable_prod _ (fun j _ =>
          (HilbertCode.measurable_circleRep_fixed _).comp (measurable_plane _ _ _)))
  have hex := circle_square_consistency (M.ownKernel 2 e) f hf a hi c hcol d hrow
  intro i
  obtain ⟨b,hb⟩ := hex i
  have hbe : ∀ᵐ z ∂Λ (plane 1 0 i e), ∏ j, HilbertCode.circleRep (q i j) (z j) = b := by
    have hh := ae_map_descent (P := fun z : I → Arr I M.Y 0 =>
      ∏ j, HilbertCode.circleRep (q i j) (z j) = b)
      (M.ownKernel 2 e) (hmar.1 i).measurable hb
    rwa [(hmar.1 i).map_eq] at hh
  apply exactCode_of_circle_tuple (M.ownKernel 0) Λ (tupleParameter M) (hm _) _ _ b hbe
  · intro j
    exact ((hcodes j).1 i).trans (parameter_cell_commute M i j e).symm
  · intro j
    exact (hcodes j).2.1 i
end ArrayObjects.Object.Rolled

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

section
open MeasureTheory ProbabilityTheory Set
variable {P Q U Y I : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace Q] [StandardBorelSpace Q]
  [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U) (row col : Q → I → P)

omit [StandardBorelSpace P] [MeasurableSpace Q] [StandardBorelSpace Q] [StandardBorelSpace U] in
lemma exactSquare_unique_cell (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p))
    {e : Q} {q r : I → I → HilbertCode κ}
    (hq : (e,q) ∈ exactSquareSet κ Λ u row col)
    (hr : (e,r) ∈ exactSquareSet κ Λ u row col) (a s : I) (he : q a s = r a s) : q = r := by
  have hc : (fun i => q i s) = fun i => r i s :=
    exactCode_unique_slot κ Λ u hk hm hind (hq.2 s) (hr.2 s) a he
  funext i
  exact exactCode_unique_slot κ Λ u hk hm hind (hq.1 i) (hr.1 i) s (congrFun hc i)

end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

lemma rawSquare_row_completion (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S}) :
    ∀ᵐ e ∂M.parameterLaw 2, ∀ (a : I) (r : I → HilbertCode (M.ownKernel 0)),
      (plane 1 0 a e,r) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) →
      ∃ q : I → I → HilbertCode (M.ownKernel 0), (e,q) ∈ rawExactSquare M Λ ∧ q a = r := by
  have hr (a : I) := (show MeasurePreserving (plane 1 0 a)
    (M.parameterLaw 2) (M.parameterLaw 1) from
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩).quasiMeasurePreserving.ae hS
  have hc (s : I) := (show MeasurePreserving (plane 1 (Fin.last 1) s)
    (M.parameterLaw 2) (M.parameterLaw 1) from
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩).quasiMeasurePreserving.ae hS
  filter_upwards [ae_all_iff.mpr hr,ae_all_iff.mpr hc,
    rawSquare_exact_consistency M hM (by omega) Λ hL hm] with e hrow hcol hcons a r hr
  have hex (s : I) : ∃ b : I → HilbertCode (M.ownKernel 0),
      (plane 1 (Fin.last 1) s e,b) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) ∧ b a = r s := by
    have hs : (tupleParameter M (plane 1 0 a e) s,r s) ∈ S :=
      (Set.ext_iff.mp (hrow a s) _).mp ⟨r,hr,rfl⟩
    rw [parameter_cell_commute M a s e] at hs
    exact (Set.ext_iff.mp (hcol s a) _).mpr hs
  choose b hb hba using hex
  let q : I → I → HilbertCode (M.ownKernel 0) := fun i s => b s i
  have hqa : q a = r := funext hba
  have hqc (s : I) : (plane 1 (Fin.last 1) s e,fun i => q i s) ∈
      exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) := hb s
  refine ⟨q,⟨hcons q a hqc ?_,hqc⟩,hqa⟩
  rwa [hqa]

lemma rawSquare_column_completion (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S}) :
    ∀ᵐ e ∂M.parameterLaw 2, ∀ (s : I) (c : I → HilbertCode (M.ownKernel 0)),
      (plane 1 (Fin.last 1) s e,c) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) →
      ∃ q : I → I → HilbertCode (M.ownKernel 0), (e,q) ∈ rawExactSquare M Λ ∧
        (fun i => q i s) = c := by
  obtain ⟨a⟩ : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  have hr := (show MeasurePreserving (plane 1 0 a) (M.parameterLaw 2) (M.parameterLaw 1) from
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩).quasiMeasurePreserving.ae hS
  have hc (s : I) := (show MeasurePreserving (plane 1 (Fin.last 1) s)
    (M.parameterLaw 2) (M.parameterLaw 1) from
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩).quasiMeasurePreserving.ae hS
  filter_upwards [hr,ae_all_iff.mpr hc,rawSquare_row_completion M Λ hM hk hL hm S hS]
    with e hrow hcol hcompl s c hc
  have hs : (tupleParameter M (plane 1 (Fin.last 1) s e) a,c a) ∈ S :=
    (Set.ext_iff.mp (hcol s a) _).mp ⟨c,hc,rfl⟩
  rw [←parameter_cell_commute M a s e] at hs
  obtain ⟨r,hr,hrs⟩ := (Set.ext_iff.mp (hrow s) _).mpr hs
  obtain ⟨q,hq,hqa⟩ := hcompl a r hr
  refine ⟨q,hq,?_⟩
  exact exactCode_unique_slot (M.ownKernel 0) Λ (tupleParameter M) hk hm hind
    (hq.2 s) hc a ((congrFun hqa s).trans hrs)

lemma rawSquare_row_bijective (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (e : Arr I M.U 2) (a : I)
    (hc : ∀ r, (plane 1 0 a e,r) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) →
      ∃ q : I → I → HilbertCode (M.ownKernel 0), (e,q) ∈ rawExactSquare M Λ ∧ q a = r) :
    ∃ f : {q : I → I → HilbertCode (M.ownKernel 0) // (e,q) ∈ rawExactSquare M Λ} ≃
        {r : I → HilbertCode (M.ownKernel 0) //
          (plane 1 0 a e,r) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)},
      ∀ q, (f q).val = q.val a := by
  let f : {q : I → I → HilbertCode (M.ownKernel 0) // (e,q) ∈ rawExactSquare M Λ} →
      {r : I → HilbertCode (M.ownKernel 0) //
          (plane 1 0 a e,r) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)} :=
    fun q => ⟨q.val a,q.property.1 a⟩
  have hf : Function.Bijective f := by
    constructor
    · intro q r he
      apply Subtype.ext
      exact exactSquare_unique_cell (M.ownKernel 0) Λ (tupleParameter M)
        (fun e i => plane 1 0 i e) (fun e j => plane 1 (Fin.last 1) j e) hk hm hind
        q.property r.property a a (congrFun (congrArg Subtype.val he) a)
    · intro r
      obtain ⟨q,hq,he⟩ := hc r.val r.property
      exact ⟨⟨q,hq⟩,Subtype.ext he⟩
  exact ⟨Equiv.ofBijective f hf,fun _ => rfl⟩

lemma rawSquare_col_bijective (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (e : Arr I M.U 2) (s : I)
    (hc : ∀ r, (plane 1 (Fin.last 1) s e,r) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) →
      ∃ q : I → I → HilbertCode (M.ownKernel 0), (e,q) ∈ rawExactSquare M Λ ∧ (fun i => q i s) = r) :
    ∃ f : {q : I → I → HilbertCode (M.ownKernel 0) // (e,q) ∈ rawExactSquare M Λ} ≃
        {r : I → HilbertCode (M.ownKernel 0) //
          (plane 1 (Fin.last 1) s e,r) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)},
      ∀ q, (f q).val = fun i => q.val i s := by
  let f : {q : I → I → HilbertCode (M.ownKernel 0) // (e,q) ∈ rawExactSquare M Λ} →
      {r : I → HilbertCode (M.ownKernel 0) //
          (plane 1 (Fin.last 1) s e,r) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)} :=
    fun q => ⟨fun i => q.val i s,q.property.2 s⟩
  have hf : Function.Bijective f := by
    constructor
    · intro q r he
      apply Subtype.ext
      exact exactSquare_unique_cell (M.ownKernel 0) Λ (tupleParameter M)
        (fun e i => plane 1 0 i e) (fun e j => plane 1 (Fin.last 1) j e) hk hm hind
        q.property r.property s s (congrFun (congrArg Subtype.val he) s)
    · intro r
      obtain ⟨q,hq,he⟩ := hc r.val r.property
      exact ⟨⟨q,hq⟩,Subtype.ext he⟩
  exact ⟨Equiv.ofBijective f hf,fun _ => rfl⟩

lemma rawCounting_rows_preserving (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (a : I) :
    MeasurePreserving (fun x : Arr I M.U 2 × (I → I → HilbertCode (M.ownKernel 0)) =>
      (plane 1 0 a x.1,x.2 a)) (Eσ.measure (M.parameterLaw 2)) (Eπ.measure (M.parameterLaw 1)) := by
  apply Eσ.measurePreserving_fibrewise Eπ _ _ (plane 1 0 a)
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
    (fun x => x.2 a) ((measurable_pi_apply a).comp measurable_snd)
  filter_upwards [rawSquare_row_completion M Λ hM hk hL hm S hS] with e he
  exact rawSquare_row_bijective M Λ hk hm hind e a (he a)

lemma rawCounting_columns_preserving (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (s : I) :
    MeasurePreserving (fun x : Arr I M.U 2 × (I → I → HilbertCode (M.ownKernel 0)) =>
      (plane 1 (Fin.last 1) s x.1,fun i => x.2 i s))
      (Eσ.measure (M.parameterLaw 2)) (Eπ.measure (M.parameterLaw 1)) := by
  apply Eσ.measurePreserving_fibrewise Eπ _ _ (plane 1 (Fin.last 1) s)
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
    (fun x i => x.2 i s) (Measurable.of_eval fun i =>
      (measurable_pi_apply s).comp ((measurable_pi_apply i).comp measurable_snd))
  filter_upwards [rawSquare_column_completion M Λ hM hk hL hm hind S hS] with e he
  exact rawSquare_col_bijective M Λ hk hm hind e s (he s)

end ArrayObjects.Object.Rolled

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

lemma depMap_apply (κ : ProbabilityTheory.Kernel A B) [IsSFiniteKernel κ]
    {f : A × B → C} (hf : Measurable f) (a : A) :
    depMap κ f a = (κ a).map (fun b => f (a,b)) := by
  rw [depMap,ProbabilityTheory.Kernel.map_apply _ hf,
    ProbabilityTheory.Kernel.prod_apply,ProbabilityTheory.Kernel.id_apply,Measure.dirac_prod,
    Measure.map_map hf measurable_prodMk_left]
  rfl

lemma depMap_comap (κ : ProbabilityTheory.Kernel A B) [IsSFiniteKernel κ]
    {f : A × B → C} (hf : Measurable f) (g : D → A) (hg : Measurable g) :
    (depMap κ f).comap g hg = depMap (κ.comap g hg) (fun db => f (g db.1,db.2)) := by
  have hfg : Measurable (fun db : D × B => f (g db.1,db.2)) :=
    hf.comp ((hg.comp measurable_fst).prodMk measurable_snd)
  ext d : 1
  rw [ProbabilityTheory.Kernel.comap_apply,depMap_apply κ hf,
    depMap_apply _ hfg,
    ProbabilityTheory.Kernel.comap_apply]

lemma depMap_prod (κ : ProbabilityTheory.Kernel A B) (η : ProbabilityTheory.Kernel A C)
    [IsSFiniteKernel κ] [IsSFiniteKernel η]
    {f : A × B → D} {g : A × C → E} (hf : Measurable f) (hg : Measurable g) :
    depMap (κ ×ₖ η) (fun x => (f (x.1,x.2.1),g (x.1,x.2.2))) =
      depMap κ f ×ₖ depMap η g := by
  have hfg : Measurable (fun x : A × (B × C) => (f (x.1,x.2.1),g (x.1,x.2.2))) :=
    (hf.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
      (hg.comp (measurable_fst.prodMk measurable_snd.snd))
  ext a : 1
  rw [depMap_apply _ hfg,
    ProbabilityTheory.Kernel.prod_apply,ProbabilityTheory.Kernel.prod_apply,
    depMap_apply _ hf,depMap_apply _ hg]
  exact (Measure.map_prod_map (κ a) (η a) (hf.comp measurable_prodMk_left)
    (hg.comp measurable_prodMk_left)).symm
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

namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

lemma rawCounting_parameter_pair_given_row (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (a s t : I) (hst : s ≠ t) :
    HasCondDistrib (fun x : RawLabelSquare M =>
      (plane 1 (Fin.last 1) s x.1,plane 1 (Fin.last 1) t x.1))
      (rawLabelRow M a)
      (((M.parameterCoordinateKernel a).comap (plane 0 0 s) (measurable_plane _ _ _) ×ₖ
        (M.parameterCoordinateKernel a).comap (plane 0 0 t) (measurable_plane _ _ _)).comap
          (Prod.fst : RawLabelTuple M → Arr I M.U 1)
          (@measurable_fst (Arr I M.U 1) (I → HilbertCode (M.ownKernel 0)) _ inferInstance)) (Eσ.measure (M.parameterLaw 2)) := by
  have he := (rawSquare_row_completion M Λ hM hk hL hm S hS).mono
    (fun e he => rawSquare_row_bijective M Λ hk hm hind e a (he a))
  exact Eσ.observation_conditional_of_fibrewise Eπ _ _ (plane 1 0 a)
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
    (fun x => x.2 a) ((measurable_pi_apply a).comp measurable_snd) he
    (fun e => (plane 1 (Fin.last 1) s e,plane 1 (Fin.last 1) t e))
    ((measurable_plane _ _ _).prodMk (measurable_plane _ _ _)) _
    (parameter_pair_geometry M hM hk a s t hst)

lemma rawCounting_target_pair_given_row (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (a b s t : I) (hst : s ≠ t) :
    HasCondDistrib (fun x : RawLabelSquare M =>
      (rawLabelSlot M s (rawLabelRow M b x),rawLabelSlot M t (rawLabelRow M b x)))
      (rawLabelRow M a)
      ((rawLabelTransition M Λ a b).comap (rawLabelSlot M s) (measurable_rawLabelSlot M s) ×ₖ
       (rawLabelTransition M Λ a b).comap (rawLabelSlot M t) (measurable_rawLabelSlot M t))
      (Eσ.measure (M.parameterLaw 2)) := by
  let κ := (M.parameterCoordinateKernel a).comap (Prod.fst : RawLabel M → Arr I M.U 0)
    (@measurable_fst (Arr I M.U 0) (HilbertCode (M.ownKernel 0)) _ inferInstance)
  let fs : RawLabelTuple M × Arr I M.U 1 → RawLabel M :=
    fun x => rawMatchedLabel M Λ a b (rawLabelSlot M s x.1,x.2)
  let ft : RawLabelTuple M × Arr I M.U 1 → RawLabel M :=
    fun x => rawMatchedLabel M Λ a b (rawLabelSlot M t x.1,x.2)
  have hfs : Measurable fs := (measurable_rawMatchedLabel M Λ hk hm hind a b).comp
    (((measurable_rawLabelSlot M s).comp measurable_fst).prodMk measurable_snd)
  have hft : Measurable ft := (measurable_rawMatchedLabel M Λ hk hm hind a b).comp
    (((measurable_rawLabelSlot M t).comp measurable_fst).prodMk measurable_snd)
  have hpair : Measurable (fun x : RawLabelTuple M × (Arr I M.U 1 × Arr I M.U 1) =>
      (fs (x.1,x.2.1),ft (x.1,x.2.2))) :=
    (hfs.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
      (hft.comp (measurable_fst.prodMk measurable_snd.snd))
  have hbase := rawCounting_parameter_pair_given_row M Λ hM hk hL hm hind S hS Eπ Eσ a s t hst
  have hker : (((M.parameterCoordinateKernel a).comap (plane 0 0 s) (measurable_plane _ _ _) ×ₖ
        (M.parameterCoordinateKernel a).comap (plane 0 0 t) (measurable_plane _ _ _)).comap
          (Prod.fst : RawLabelTuple M → Arr I M.U 1)
            (@measurable_fst (Arr I M.U 1) (I → HilbertCode (M.ownKernel 0)) _ inferInstance)) =
      κ.comap (rawLabelSlot M s) (measurable_rawLabelSlot M s) ×ₖ
      κ.comap (rawLabelSlot M t) (measurable_rawLabelSlot M t) := by
    ext x : 1
    simp only [Kernel.comap_apply,Kernel.prod_apply,κ,rawLabelSlot,tupleParameter]
  rw [hker] at hbase
  have h := ConditionalTransport.map_observation hbase _ hpair
  change HasCondDistrib _ _ (Rokhlin.Kernel.depMap _ _) _ at h
  rw [Rokhlin.Kernel.depMap_prod _ _ hfs hft] at h
  have hs := Rokhlin.Kernel.depMap_comap κ
    (measurable_rawMatchedLabel M Λ hk hm hind a b) (rawLabelSlot M s) (measurable_rawLabelSlot M s)
  have ht := Rokhlin.Kernel.depMap_comap κ
    (measurable_rawMatchedLabel M Λ hk hm hind a b) (rawLabelSlot M t) (measurable_rawLabelSlot M t)
  change (rawLabelTransition M Λ a b).comap _ _ = Rokhlin.Kernel.depMap _ fs at hs
  change (rawLabelTransition M Λ a b).comap _ _ = Rokhlin.Kernel.depMap _ ft at ht
  rw [←hs,←ht] at h
  change HasLaw _ _ _ at h ⊢
  apply h.congr
  filter_upwards [Eσ.ae_mem (M.parameterLaw 2)] with x hx
  refine Prod.ext (by rfl) ?_
  dsimp only [fs,ft,rawMatchedLabel,rawLabelSlot,rawLabelRow]
  rw [exactMatching_exact (M.ownKernel 0) Λ (tupleParameter M)
      (measurable_tupleParameter M) hk hm hind a (hx.2 s),
    exactMatching_exact (M.ownKernel 0) Λ (tupleParameter M)
      (measurable_tupleParameter M) hk hm hind a (hx.2 t)]
  rw [parameter_cell_commute M b s x.1,parameter_cell_commute M b t x.1]
end ArrayObjects.Object.Rolled
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

lemma screened_operator_integrable
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hz : MeasurePreserving z ν τ) {κ : Kernel Z Y} [IsMarkovKernel κ]
    (h : HasCondDistrib y x (κ.comap z hz.measurable) μ)
    (g : Lp ℂ 2 ρ) (hgi : Integrable (g : Y → ℂ) ρ) :
    operator hx hy g = (pull hz ∘L operator (hz.comp hx) hy) g := by
  have hσx : SigmaFinite (μ.map x) := by rw [hx.map_eq]; infer_instance
  have hσz : SigmaFinite (μ.map (z ∘ x)) := by rw [(hz.comp hx).map_eq]; infer_instance
  apply (Lp.compMeasurePreservingₗᵢ ℂ x hx).injective
  change pull hx (operator hx hy g) = (pull hx ∘L pull hz) (operator (hz.comp hx) hy g)
  rw [←pull_comp]
  apply Lp.ext
  have hi : Integrable (fun ω => g (y ω)) μ := (hy.integrable_comp g.1.stronglyMeasurable.aestronglyMeasurable).mpr hgi
  have hce := (SigmaFiniteConditional.condExp_of_kernel hx.measurable h g
    g.1.stronglyMeasurable hi).trans
    (SigmaFiniteConditional.condExp_of_kernel (hz.measurable.comp hx.measurable)
      h.comp_right g g.1.stronglyMeasurable hi).symm
  exact (Lp.coeFn_compMeasurePreserving _ hx).trans
    ((operator_ae_eq_condExp_integrable hx hy g hgi).trans
      (hce.trans ((operator_ae_eq_condExp_integrable (hz.comp hx) hy g hgi).symm.trans
        (Lp.coeFn_compMeasurePreserving _ (hz.comp hx)).symm)))

theorem screened_operator_sigmaFinite
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hz : MeasurePreserving z ν τ) {κ : Kernel Z Y} [IsMarkovKernel κ]
    (h : HasCondDistrib y x (κ.comap z hz.measurable) μ) :
    operator hx hy = pull hz ∘L operator (hz.comp hx) hy := by
  apply ContinuousLinearMap.ext
  apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (fun g => operator hx hy g = (pull hz ∘L operator (hz.comp hx) hy) g)
  · intro c s hs hμs
    apply screened_operator_integrable hx hy hz h
    change Integrable (indicatorConstLp 2 hs hμs.ne c : Y → ℂ) ρ
    apply Integrable.congr _ (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs.ne) (c := c)).symm
    exact (integrable_indicator_iff hs).mpr (integrableOn_const (C := c) hμs.ne)
  · intro f g hf hg hfg hF hG
    simp only [map_add,hF,hG]
  · exact isClosed_eq (operator hx hy).continuous
      (pull hz ∘L operator (hz.comp hx) hy).continuous
end
section

variable {Ω R X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure Ω} [SigmaFinite μ] {σ : Measure R} [SigmaFinite σ]
  {ν : Measure X} {ρ : Measure Y}
  {r : Ω → R} {x : Ω → X} {y : Ω → Y}
  {κ : Kernel R X} {η : Kernel R Y} [IsMarkovKernel κ] [IsMarkovKernel η]

lemma product_operator_inner_integrable
    (hr : MeasurePreserving r μ σ) (hx : MeasurePreserving x μ ν)
    (hy : MeasurePreserving y μ ρ) (h : HasCondDistrib (fun ω => (x ω,y ω)) r (κ ×ₖ η) μ)
    (f : Lp ℂ 2 ν) (g : Lp ℂ 2 ρ)
    (hfi : Integrable (f : X → ℂ) ν) (hgi : Integrable (g : Y → ℂ) ρ) :
    inner ℂ f (operator hx hy g) =
      inner ℂ (operator hr hx f) (operator hr hy g) := by
  have hσ : SigmaFinite (μ.map r) := by rw [hr.map_eq]; infer_instance
  have hf : HasCondDistrib x r κ μ := by simpa using h.fst
  have hg : HasCondDistrib y r η μ := by simpa using h.snd
  have hfx : Integrable (fun ω => f (x ω)) μ :=
    (hx.integrable_comp f.1.stronglyMeasurable.aestronglyMeasurable).mpr hfi
  have hgy : Integrable (fun ω => g (y ω)) μ :=
    (hy.integrable_comp g.1.stronglyMeasurable.aestronglyMeasurable).mpr hgi
  have hef := (operator_ae_eq_condExp_integrable hr hx f hfi).trans
    (SigmaFiniteConditional.condExp_of_kernel hr.measurable hf f f.1.stronglyMeasurable hfx)
  have heg := (operator_ae_eq_condExp_integrable hr hy g hgi).trans
    (SigmaFiniteConditional.condExp_of_kernel hr.measurable hg g g.1.stronglyMeasurable hgy)
  let F : R × (X × Y) → ℂ := fun u => inner ℂ (f u.2.1) (g u.2.2)
  have hFm : StronglyMeasurable F :=
    (f.1.stronglyMeasurable.comp_measurable measurable_snd.fst).inner
      (g.1.stronglyMeasurable.comp_measurable measurable_snd.snd)
  have hi : Integrable (fun ω => inner ℂ (f (x ω)) (g (y ω))) μ := by
    apply (L2.integrable_inner (pull hx f) (pull hy g)).congr
    filter_upwards [Lp.coeFn_compMeasurePreserving f hx,Lp.coeFn_compMeasurePreserving g hy]
      with ω h1 h2
    change inner ℂ (Lp.compMeasurePreserving x hx f ω)
      (Lp.compMeasurePreserving y hy g ω) = _
    rw [h1,h2]
    rfl
  have hFi : Integrable F ((μ.map r) ⊗ₘ (κ ×ₖ η)) := by
    rw [←h.map_eq]
    exact (integrable_map_measure hFm.aestronglyMeasurable h.aemeasurable).mpr hi
  rw [inner_operator]
  calc
    (∫ ω, inner ℂ (f (x ω)) (g (y ω)) ∂μ) = ∫ u, F u ∂(μ.map r) ⊗ₘ (κ ×ₖ η) :=
      h.integral_comp hFm.aestronglyMeasurable
    _ = ∫ u, inner ℂ (∫ z, f z ∂κ u) (∫ z, g z ∂η u) ∂μ.map r := by
      rw [Measure.integral_compProd hFi]
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [F,Kernel.prod_apply,RCLike.inner_apply]
      simp_rw [mul_comm (g _) _]
      rw [integral_prod_mul (μ := κ u) (ν := η u)
        (fun z => starRingEnd ℂ (f z)) (fun z => g z),integral_conj]
      exact mul_comm _ _
    _ = ∫ ω, inner ℂ (∫ z, f z ∂κ (r ω)) (∫ z, g z ∂η (r ω)) ∂μ := by
      apply integral_map hr.aemeasurable
      exact ((f.1.stronglyMeasurable.integral_kernel).inner
        (g.1.stronglyMeasurable.integral_kernel)).aestronglyMeasurable
    _ = ∫ ω, inner ℂ (operator hr hx f (r ω)) (operator hr hy g (r ω)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hef,heg] with ω h1 h2
      rw [h1,h2]
    _ = inner ℂ (operator hr hx f) (operator hr hy g) := by
      rw [L2.inner_def]
      exact hr.hasLaw.integral_comp (f := fun u =>
        inner ℂ (operator hr hx f u) (operator hr hy g u))
        (((operator hr hx f).1.stronglyMeasurable).inner (𝕜 := ℂ)
          (operator hr hy g).1.stronglyMeasurable).aestronglyMeasurable

lemma indicator_integrable {A : Type*} [MeasurableSpace A] (ζ : Measure A)
    (s : Set A) (hs : MeasurableSet s) (hζ : ζ s < ∞) (c : ℂ) :
    Integrable (indicatorConstLp 2 hs hζ.ne c : A → ℂ) ζ := by
  apply Integrable.congr _ (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hζ.ne) (c := c)).symm
  exact (integrable_indicator_iff hs).mpr (integrableOn_const (C := c) hζ.ne)

theorem product_operator
    (hr : MeasurePreserving r μ σ) (hx : MeasurePreserving x μ ν)
    (hy : MeasurePreserving y μ ρ) (h : HasCondDistrib (fun ω => (x ω,y ω)) r (κ ×ₖ η) μ) :
    operator hx hy = (operator hr hx).adjoint ∘L operator hr hy := by
  have htest (g : Lp ℂ 2 ρ) (hgi : Integrable (g : Y → ℂ) ρ) (f : Lp ℂ 2 ν) :
      inner ℂ f (operator hx hy g) = inner ℂ (operator hr hx f) (operator hr hy g) := by
    apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (fun f => inner ℂ f (operator hx hy g) = inner ℂ (operator hr hx f) (operator hr hy g))
    · intro d t ht hν
      exact product_operator_inner_integrable hr hx hy h _ g (indicator_integrable ν t ht hν d) hgi
    · intro f₁ f₂ hf₁ hf₂ hfg h1 h2
      simp only [map_add,inner_add_left,h1,h2]
    · exact isClosed_eq (continuous_id.inner continuous_const)
        ((operator hr hx).continuous.inner continuous_const)
  have hi : ∀ (f : Lp ℂ 2 ν) (g : Lp ℂ 2 ρ),
      inner ℂ f (operator hx hy g) = inner ℂ (operator hr hx f) (operator hr hy g) := by
    intro f
    apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (fun g => inner ℂ f (operator hx hy g) = inner ℂ (operator hr hx f) (operator hr hy g))
    · intro c s hs hρ
      exact htest _ (indicator_integrable ρ s hs hρ c) f
    · intro g₁ g₂ hg₁ hg₂ hfg h1 h2
      simp only [map_add,inner_add_right,h1,h2]
    · exact isClosed_eq (continuous_const.inner (operator hx hy).continuous)
        (continuous_const.inner (operator hr hy).continuous)
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro f
  rw [ContinuousLinearMap.comp_apply,adjoint_inner_right]
  exact hi f g

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

lemma square_operator (row col : I → Ω → P) (slot : I → P → Z)
    (hr : ∀ a, MeasurePreserving (row a) μ π)
    (hc : ∀ s, MeasurePreserving (col s) μ π)
    (hq : ∀ i, MeasurePreserving (slot i) π ξ)
    (hcomm : ∀ a s, slot s ∘ row a = slot a ∘ col s)
    (a b s t : I) (K : Kernel Z Z) [IsMarkovKernel K]
    (h : HasCondDistrib (fun ω => (slot s (row b ω),slot t (row b ω))) (row a)
      (K.comap (slot s) (hq s).measurable ×ₖ K.comap (slot t) (hq t).measurable) μ) :
    operator (hq s) (hq t) = (operator (hq a) (hq b)).adjoint ∘L
      operator (hq s) (hq t) ∘L operator (hq a) (hq b) := by
  have hscreen (j : I)
      (hj : HasCondDistrib (slot j ∘ row b) (row a) (K.comap (slot j) (hq j).measurable) μ) :
      operator (hr a) ((hq j).comp (hr b)) = pull (hq j) ∘L operator (hq a) (hq b) := by
    rw [screened_operator_sigmaFinite (hr a) ((hq j).comp (hr b)) (hq j) hj]
    have hcol := operator_congr ((hq j).comp (hr a)) ((hq j).comp (hr b))
      ((hq a).comp (hc j)) ((hq b).comp (hc j)) (hcomm a j) (hcomm b j)
    rw [hcol,operator_pullback (hc j) (hq a) (hq b)]
  have hfst : HasCondDistrib (slot s ∘ row b) (row a) (K.comap (slot s) (hq s).measurable) μ :=
    by simpa only [Kernel.fst_prod, Function.comp_def] using h.fst
  have hsnd : HasCondDistrib (slot t ∘ row b) (row a) (K.comap (slot t) (hq t).measurable) μ :=
    by simpa only [Kernel.snd_prod, Function.comp_def] using h.snd
  have hp := product_operator (hr a) ((hq s).comp (hr b)) ((hq t).comp (hr b)) h
  rw [operator_pullback (hr b) (hq s) (hq t),hscreen s hfst,hscreen t hsnd] at hp
  apply hp.trans
  simp only [adjoint_comp,comp_assoc]
  rfl

end JoiningOperator

namespace ArrayObjects.Object.Rolled

open ContinuousLinearMap MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace

section RawLabelCells
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

omit [DecidableEq I] in
lemma rawLabel_cell_commute (a s : I) :
    rawLabelSlot M s ∘ rawLabelRow M a = rawLabelSlot M a ∘ rawLabelColumn M s := by
  funext x
  exact Prod.ext (parameter_cell_commute M a s x.1) rfl

lemma rawCounting_square_operator (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
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
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (a b s t : I) (hst : s ≠ t) :
    let hq := rawCounting_coordinate_preserving M Λ hk hm hind S hS E Eπ
    JoiningOperator.operator (hq s) (hq t) =
      (JoiningOperator.operator (hq a) (hq b)).adjoint ∘L
        JoiningOperator.operator (hq s) (hq t) ∘L
          JoiningOperator.operator (hq a) (hq b) := by
  let := rawLabelTransition_markov M Λ hk hm hind a b
  exact JoiningOperator.square_operator (rawLabelRow M) (rawLabelColumn M) (rawLabelSlot M)
    (rawCounting_rows_preserving M Λ hM hk hL hm hind S hS Eπ Eσ)
    (rawCounting_columns_preserving M Λ hM hk hL hm hind S hS Eπ Eσ)
    (rawCounting_coordinate_preserving M Λ hk hm hind S hS E Eπ)
    (rawLabel_cell_commute M) a b s t (rawLabelTransition M Λ a b)
    (rawCounting_target_pair_given_row M Λ hM hk hL hm hind S hS Eπ Eσ a b s t hst)
end RawLabelCells


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
namespace JoiningOperator
lemma partial_unitary_of_squares_aux {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A B : H →L[ℂ] H)
    (hb : B = A.adjoint) (hb' : B.adjoint = A)
    (h1 : A = A.adjoint ∘L A ∘L A) (h2 : A = B.adjoint ∘L A ∘L B) :
    A = A.adjoint * A * A ∧ A = A * A * A.adjoint := by
  constructor
  · simpa only [ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_assoc] using h1
  · rw [hb',hb] at h2
    simpa only [ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_assoc] using h2

lemma partial_unitary_of_squares {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    {μ : Measure W} {ν : Measure Z} {f g : W → Z}
    (hf : MeasurePreserving f μ ν) (hg : MeasurePreserving g μ ν)
    (h1 : operator hf hg = (operator hf hg).adjoint ∘L operator hf hg ∘L operator hf hg)
    (h2 : operator hf hg = (operator hg hf).adjoint ∘L operator hf hg ∘L operator hg hf) :
    operator hf hg = (operator hf hg).adjoint * operator hf hg * operator hf hg ∧
      operator hf hg = operator hf hg * operator hf hg * (operator hf hg).adjoint :=
  partial_unitary_of_squares_aux _ _ (operator_adjoint hf hg).symm
    (operator_adjoint hg hf) h1 h2
end JoiningOperator
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

include hM hL Eσ hst in
lemma rawCounting_partial_unitary :
    let hq := rawCounting_coordinate_preserving M Λ hk hm hind S hS E Eπ
    let A := JoiningOperator.operator (hq s) (hq t)
    A = A.adjoint * A * A ∧ A = A * A * A.adjoint := by
  dsimp only
  exact JoiningOperator.partial_unitary_of_squares _ _
    (rawCounting_square_operator M Λ hM hk hL hm hind S hS E Eπ Eσ s t s t hst)
    (rawCounting_square_operator M Λ hM hk hL hm hind S hS E Eπ Eσ t s s t hst)

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
