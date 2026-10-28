-- Prove2me | solution 1 for OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_exact_split_span
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:04:04.95623+00:00
-- url     : https://prove2.me/submissions/267b5e52-32f9-4a5e-b29c-43b0d48b40a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ3Ro002
import Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_grouped_column_contraction_projection
import Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_grouped_polar_a_field
import Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_grouped_polar_b_field
import Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_grouped_polar_data
import Theorems.Thm_OAI_Rokhlin_MeasurablePolarRectangle_torus_coordinates

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

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

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

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in

lemma plane_first_last (n : ℕ) (a j : I) :
    plane (Y := M.Y) n 0 a ∘ plane (n + 1) (Fin.last (n + 1)) j =
      plane n (Fin.last n) j ∘ plane (n + 1) 0 a := by
  funext y v
  change y ((Fin.last (n + 1)).insertNth j ((0 : Fin (n + 1)).insertNth a v)) =
    y ((0 : Fin (n + 2)).insertNth a ((Fin.last n).insertNth j v))
  simp only [Fin.insertNth_last', Fin.insertNth_zero']
  rw [cons_snoc]

end ArrayObjects.Object.Rolled

namespace FiniteKernel
variable {ι X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem pi_split {S T W : Finset ι} (hS : S ⊆ W) (hT : T ⊆ W)
    (hST : Disjoint S T) (κ : ι → Kernel X Y) [∀ i, IsMarkovKernel (κ i)] :
    (pi (fun i : W => κ i)).map
      (fun y => ((fun i : S => y ⟨i, hS i.property⟩), (fun i : T => y ⟨i, hT i.property⟩))) =
      (pi (fun i : S => κ i)) ×ₖ (pi (fun i : T => κ i)) := by
  let e : S ⊕ T ↪ W := ⟨Sum.elim
    (fun i : S => (⟨i, hS i.property⟩ : W))
    (fun i : T => (⟨i, hT i.property⟩ : W)), by
      intro a b hab
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (Subtype.ext (congrArg (fun z : W => (z : ι)) hab))
        | inr b =>
          have he : (a : ι) = b := congrArg (fun z : W => (z : ι)) hab
          exact False.elim (Finset.disjoint_left.mp hST a.property (he ▸ b.property))
      | inr a =>
        cases b with
        | inl b =>
          have he : (a : ι) = b := congrArg (fun z : W => (z : ι)) hab
          exact False.elim (Finset.disjoint_left.mp hST b.property (he ▸ a.property))
        | inr b => exact congrArg Sum.inr (Subtype.ext (congrArg (fun z : W => (z : ι)) hab))⟩
  ext x : 1
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply]
  change (Measure.pi (fun i : W => κ i x)).map _ =
    (Measure.pi (fun i : S => κ i x)).prod (Measure.pi (fun i : T => κ i x))
  have he := measure_pi_precomp (fun i : W => κ i x) e
  have hh := (measurePreserving_sumPiEquivProdPi (fun i : S ⊕ T => κ (e i) x)).map_eq
  rw [← he, Measure.map_map (MeasurableEquiv.sumPiEquivProdPi (fun _ : S ⊕ T => Y)).measurable
    (Measurable.of_eval (fun i => measurable_pi_apply (e i)))] at hh
  exact hh
end FiniteKernel

namespace ConditionalReveal
variable {ι Ω X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y]

theorem disjoint_families (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Ω → X) (y : ι → Ω → Y)
    (κ : ι → Kernel X Y) [∀ i, IsMarkovKernel (κ i)]
    {S T W : Finset ι} (hS : S ⊆ W) (hT : T ⊆ W) (hST : Disjoint S T)
    (h : HasCondDistrib (fun ω => fun i : W => y i ω) E
      (FiniteKernel.pi (fun i : W => κ i)) μ) :
    HasCondDistrib (fun ω => fun i : T => y i ω)
      (fun ω => (E ω, fun i : S => y i ω))
      ((FiniteKernel.pi (fun i : T => κ i)).prodMkRight (S → Y)) μ := by
  have hh := h.comp_left (show Measurable (fun z : W → Y =>
      ((fun i : S => z ⟨i, hS i.property⟩), (fun i : T => z ⟨i, hT i.property⟩))) from by fun_prop)
  rw [FiniteKernel.pi_split hS hT hST κ, ← ConditionalScreens.compProd_prodMkRight] at hh
  exact hh.of_compProd
end ConditionalReveal

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem columns_with_parents (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I) (n : ℕ)
    (J : Finset I) (hJ : J ≠ Finset.univ) :
    HasCondDistrib (planes (n + 1) J) (parentData M R n)
      (FiniteKernel.pi (fun j : J => columnKernel M R n j)) (M.law (n + 2)) := by
  have hi : ∀ S : Finset I, S ⊂ R → IsConditional M S := by
    intro S hS
    apply isConditional M hM S
    have hc := Finset.card_lt_card hS
    omega
  have hc := proper_conditional M hM R hR hi n J hJ
  have hp := ConditionalTransport.pullback
    (show MeasurePreserving (roll (Y := M.Y) (n + 1)) (M.law (n + 2)) (law M (n + 1)) from
      ⟨(roll (n + 1)).measurable, rfl⟩)
    (measurable_amap (measurable_parameter M R) _) hc
  have hd := hp.measurableEquiv_comp_right (parameterEquiv M R (n + 1))
  have h := hd.comp_left (Measurable.of_eval (fun j : J =>
    (roll n).symm.measurable.comp (measurable_pi_apply j)))
  have ho : (fun z : J → Arr I (State M) n => fun j => (roll n).symm (z j)) ∘
      planes n J ∘ roll (n + 1) = planes (n + 1) J := by
    rw [planes_roll]
    funext y j
    exact (roll n).symm_apply_apply _
  change HasCondDistrib
    ((fun z : J → Arr I (State M) n => fun j => (roll n).symm (z j)) ∘
      planes n J ∘ roll (n + 1))
    (parameterEquiv M R (n + 1) ∘ amap (parameter M R) (n + 1) ∘ roll (n + 1))
    _ (M.law (n + 2)) at h
  rw [ho, parameterEquiv_observation] at h
  change HasCondDistrib (planes (n + 1) J) (parentData M R n) _ (M.law (n + 2)) at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext p : 1
  rw [Kernel.map_apply _ (Measurable.of_eval (fun j : J =>
    (roll n).symm.measurable.comp (measurable_pi_apply j)))]
  change Measure.pi (fun j : J => columnKernel M R n j p) =
    (Measure.pi (fun j : J => ownPosterior M R n
      (plane n (Fin.last n) j ((parameterEquiv M R (n + 1)).symm p)))).map _
  simp only [Function.comp_def]
  rw [Measure.pi_map_pi (fun _ => (roll n).symm.measurable.aemeasurable)]
  simp only [columnKernel, Kernel.comap_apply, Function.comp_apply,
    Kernel.map_apply _ (roll n).symm.measurable]


omit [DecidableEq I] in
lemma columnRestrict_planes (A J : Finset I) (n : ℕ) :
    columnRestrict M A J n ∘ planes (n + 1) J = cells M A J n := by
  funext y j a
  exact congrFun (plane_first_last M n a j) y

end ArrayObjects.Object.Rolled

end

open MeasureTheory ProbabilityTheory

namespace ConditionalFibres
variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [StandardBorelSpace Y]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {u : Ω → U} {x : Ω → X} {y : Ω → Y}
  {η : Kernel U Ω} [IsMarkovKernel η] {κ : Kernel (U × X) Y} [IsMarkovKernel κ]

omit [StandardBorelSpace X] [StandardBorelSpace Y] [IsProbabilityMeasure μ] [IsMarkovKernel κ] in
lemma chain {α : Kernel U X} [IsMarkovKernel α]
    (hx : HasCondDistrib x u α μ)
    (hy : HasCondDistrib y (fun ω => (u ω, x ω)) κ μ) :
    HasCondDistrib (fun ω => (x ω, y ω)) u (α ⊗ₖ κ) μ := by
  refine ⟨hx.aemeasurable_fst.prodMk
    (hx.aemeasurable_snd.prodMk hy.aemeasurable_snd), ?_⟩
  calc
    μ.map (fun ω => (u ω, x ω, y ω)) =
        (μ.map (fun ω => ((u ω, x ω), y ω))).map MeasurableEquiv.prodAssoc := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hy.aemeasurable]
      rfl
    _ = ((μ.map u ⊗ₘ α) ⊗ₘ κ).map MeasurableEquiv.prodAssoc := by
      rw [hy.map_eq, hx.map_eq]
    _ = μ.map u ⊗ₘ (α ⊗ₖ κ) := Measure.compProd_assoc'

theorem disintegrate (hx : Measurable x) (hy : Measurable y)
    (hη : HasCondDistrib id u η μ)
    (hκ : HasCondDistrib y (fun ω => (u ω, x ω)) κ μ) :
    ∀ᵐ a ∂μ.map u, HasCondDistrib y x (κ.sectR a) (η a) := by
  let : IsMarkovKernel (η.map x) := Kernel.IsMarkovKernel.map η hx
  let : IsMarkovKernel (η.map (fun ω => (x ω, y ω))) :=
    Kernel.IsMarkovKernel.map η (hx.prodMk hy)
  have hpair := chain (hη.comp_left hx) hκ
  have hother := hη.comp_left (hx.prodMk hy)
  have he : η.map (fun ω => (x ω, y ω)) =ᵐ[μ.map u] (η.map x) ⊗ₖ κ :=
    Kernel.ae_eq_of_compProd_eq (hother.map_eq.symm.trans hpair.map_eq)
  filter_upwards [he] with a ha
  refine ⟨(hx.prodMk hy).aemeasurable, ?_⟩
  rw [Kernel.map_apply _ (hx.prodMk hy), Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.map_apply _ hx] at ha
  exact ha

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
attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunArrαYOfNatNatComplexMemAddSubgroupLpENNRealSubmoduleRawSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunCellComplexMemAddSubgroupLpOfNatENNRealSubmoduleSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatCellSlotLocal _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallCellSlotTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallYRawTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYColumnCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYRowCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.arrayLaw_probability _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.localLaw_probability
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

lemma pull_norm_le (hx : MeasurePreserving x μ ν) : ‖pull hx‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simp [pull]

lemma operator_norm_le (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ) :
    ‖operator hx hy‖ ≤ 1 := by
  apply le_trans (opNorm_comp_le _ _)
  simpa using (fun leftBound rightNonneg rightBound => (mul_le_of_le_one_left rightNonneg leftBound).trans rightBound) (by simpa using pull_norm_le hx) (norm_nonneg _) (pull_norm_le hy)

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

lemma operator_ae_eq_condExp [IsFiniteMeasure μ]
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ) (h : Lp ℂ 2 ρ) :
    (fun ω => operator hx hy h (x ω)) =ᵐ[μ]
      μ[(fun ω => h (y ω)) | MeasurableSpace.comap x inferInstance] := by
  have hp := pull_adjoint_projection hx (pull hy h)
  have hc := (Lp.memLp (pull hy h)).condExpL2_ae_eq_condExp (𝕜 := ℂ) hx.measurable.comap_le
  rw [Lp.toLp_coeFn, ← hp] at hc
  exact (Lp.coeFn_compMeasurePreserving (operator hx hy h) hx).symm.trans
    (hc.trans (condExp_congr_ae (Lp.coeFn_compMeasurePreserving h hy)))


end
section

variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] [MeasurableSpace Z]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure X} {ρ : Measure Y}
  {τ : Measure Z} {x : Ω → X} {y : Ω → Y} {z : X → Z}

lemma condExp_of_kernel (hx : Measurable x) {κ : Kernel X Y} [IsMarkovKernel κ]
    (h : HasCondDistrib y x κ μ) (g : Y → ℂ) (hg : StronglyMeasurable g)
    (hgi : Integrable (fun ω => g (y ω)) μ) :
    μ[(fun ω => g (y ω)) | MeasurableSpace.comap x inferInstance] =ᵐ[μ]
      (fun ω => ∫ v, g v ∂κ (x ω)) := by
  have he : condDistrib y x μ =ᵐ[μ.map x] κ :=
    condDistrib_ae_eq_of_measure_eq_compProd h.aemeasurable_fst h.aemeasurable_snd h.map_eq
  have he' := ae_of_ae_map hx.aemeasurable he
  filter_upwards [condExp_ae_eq_integral_condDistrib hx h.aemeasurable_snd hg hgi, he']
    with ω hω heω
  exact hω.trans (by rw [heω])

lemma screened_condExp (hx : Measurable x) (hz : Measurable z)
    {κ : Kernel Z Y} [IsMarkovKernel κ] (h : HasCondDistrib y x (κ.comap z hz) μ)
    (g : Y → ℂ) (hg : StronglyMeasurable g) (hgi : Integrable (fun ω => g (y ω)) μ) :
    μ[(fun ω => g (y ω)) | MeasurableSpace.comap x inferInstance] =ᵐ[μ]
      μ[(fun ω => g (y ω)) | MeasurableSpace.comap (z ∘ x) inferInstance] :=
  (condExp_of_kernel hx h g hg hgi).trans
    (condExp_of_kernel (hz.comp hx) h.comp_right g hg hgi).symm

theorem screened_operator (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hz : MeasurePreserving z ν τ) {κ : Kernel Z Y} [IsMarkovKernel κ]
    (h : HasCondDistrib y x (κ.comap z hz.measurable) μ) :
    operator hx hy = pull hz ∘L operator (hz.comp hx) hy := by
  apply ContinuousLinearMap.ext
  intro g
  apply (Lp.compMeasurePreservingₗᵢ ℂ x hx).injective
  change pull hx (operator hx hy g) = (pull hx ∘L pull hz) (operator (hz.comp hx) hy g)
  rw [← pull_comp]
  apply Lp.ext
  have hgi : Integrable (fun ω => g (y ω)) μ :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) ((Lp.memLp g).comp_measurePreserving hy)
  have hce := screened_condExp hx.measurable hz.measurable h g g.1.stronglyMeasurable hgi
  exact (Lp.coeFn_compMeasurePreserving _ hx).trans
    ((operator_ae_eq_condExp hx hy g).trans
      (hce.trans ((operator_ae_eq_condExp (hz.comp hx) hy g).symm.trans
        (Lp.coeFn_compMeasurePreserving _ (hz.comp hx)).symm)))


end


end JoiningOperator

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory

universe u
variable {I : Type u} [Fintype I] [retained7 : DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in
lemma parameterEquiv_plane (P : Finset I) (n : ℕ) (j : I) (v : ParentData M P n) :
    parameterEquiv M P n (plane n (Fin.last n) j ((parameterEquiv M P (n+1)).symm v)) =
      (plane (n+1) (Fin.last (n+1)) j v.1,
        fun p : P => plane n (Fin.last n) j (v.2 p)) := by
  apply Prod.ext
  · funext w
    simp [parameterEquiv, plane, Fin.insertNth_last', cons_snoc]
  · rfl

include retained7 in
lemma columnKernel_eq_posterior (P : Finset I) (n : ℕ) (j : I) (v : ParentData M P n) :
    columnKernel M P n j v = posterior M P n
      (plane (n+1) (Fin.last (n+1)) j v.1,
        fun p : P => plane n (Fin.last n) j (v.2 p)) := by
  let _ := retained7
  simp only [columnKernel,Kernel.comap_apply,Function.comp_apply,
    Kernel.map_apply _ (roll n).symm.measurable,ownPosterior, Kernel.map_apply _ (roll n).measurable]
  rw [Measure.map_map (roll n).symm.measurable (roll n).measurable,
    MeasurableEquiv.symm_comp_self,Measure.map_id,parameterEquiv_plane]

lemma columns_group_screen (hM : M.IsSaturated) (P R S : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hRS : Disjoint R S)
    (hproper : R ∪ S ≠ Finset.univ) (n : ℕ) :
    HasCondDistrib (planes (n+1) S) (wholeGroupData M P R n)
      ((columnGroupKernel M P S n).comap (columnOwnData M P R S n)
        (measurable_columnOwnData M P R S n)) (M.law (n+2)) := by
  have h := ConditionalReveal.disjoint_families (M.law (n+2)) (parentData M P n)
    (fun j => plane (n+1) (Fin.last (n+1)) j) (columnKernel M P n)
    Finset.subset_union_left Finset.subset_union_right hRS
    (columns_with_parents M hM P hP n (R∪S) hproper)
  have he : (columnGroupKernel M P S n).comap (columnOwnData M P R S n)
      (measurable_columnOwnData M P R S n) =
      (FiniteKernel.pi (fun j : S => columnKernel M P n j)).prodMkRight (R → Arr I M.Y (n+1)) := by
    ext v : 1
    change Measure.pi (fun j : S => posterior M P n _) =
      Measure.pi (fun j : S => columnKernel M P n j v.1)
    congr 1
    funext j
    exact (columnKernel_eq_posterior M P n j v.1).symm
  rw [he]
  exact h

end ArrayObjects.Object.Rolled

namespace JoiningOperator
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace

section

variable {U X Y : Type*} [MeasurableSpace U] [MeasurableSpace X] [MeasurableSpace Y]
  (κ : Kernel U (X × Y)) (ν : Measure X) (ρ : Measure Y)

lemma family_eq (u : U) (hx : MeasurePreserving Prod.fst (κ u) ν)
    (hy : MeasurePreserving Prod.snd (κ u) ρ) : family κ ν ρ u = operator hx hy := by
  classical
  unfold family
  split_ifs with h
  · rfl
  · exact (h ⟨hx, hy⟩).elim

lemma family_norm_le (u : U) : ‖family κ ν ρ u‖ ≤ 1 := by
  classical
  unfold family
  split_ifs with h
  · exact operator_norm_le h.1 h.2
  · simp

variable {κ ν ρ} {m : Measure U}

lemma family_inner (hm : ∀ᵐ u ∂m,
    MeasurePreserving Prod.fst (κ u) ν ∧ MeasurePreserving Prod.snd (κ u) ρ)
    (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    (fun u => inner ℂ g (family κ ν ρ u h)) =ᵐ[m]
      (fun u => ∫ p, inner ℂ (g p.1) (h p.2) ∂κ u) := by
  filter_upwards [hm] with u hu
  rw [family_eq κ ν ρ u hu.1 hu.2]
  exact inner_operator hu.1 hu.2 g h

lemma family_inner_aestronglyMeasurable (hm : ∀ᵐ u ∂m,
    MeasurePreserving Prod.fst (κ u) ν ∧ MeasurePreserving Prod.snd (κ u) ρ)
    (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    AEStronglyMeasurable (fun u => inner ℂ g (family κ ν ρ u h)) m := by
  have hf : StronglyMeasurable (fun p : X × Y => inner ℂ (g p.1) (h p.2)) :=
    (g.1.stronglyMeasurable.comp_measurable measurable_fst).inner
      (h.1.stronglyMeasurable.comp_measurable measurable_snd)
  exact hf.integral_kernel.aestronglyMeasurable.congr (family_inner hm g h).symm

end


end JoiningOperator

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in
lemma columnPairRestrict_planes (A B S : Finset I) (n : ℕ) :
    (fun y => (columnRestrict M A S n y,columnRestrict M B S n y)) ∘ planes (n+1) S =
      fun y => (cells M A S n y,cells M B S n y) := by
  funext y
  exact Prod.ext (congrFun (columnRestrict_planes M A S n) y)
    (congrFun (columnRestrict_planes M B S n) y)

lemma columnPair_conditional (hM : M.IsSaturated) (P A B R S : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hRS : Disjoint R S)
    (hproper : R ∪ S ≠ Finset.univ) (n : ℕ) :
    HasCondDistrib (fun y => (cells M A S n y,cells M B S n y)) (wholeGroupData M P R n)
      ((columnPairKernel M P A B S n).comap (columnOwnData M P R S n)
        (measurable_columnOwnData M P R S n)) (M.law (n+2)) := by
  have h := (columns_group_screen M hM P R S hP hRS hproper n).comp_left
    ((measurable_columnRestrict M A S n).prodMk (measurable_columnRestrict M B S n))
  rw [← Kernel.comap_map_comm _ _ (by fun_prop)] at h
  simpa only [columnPairKernel,columnPairRestrict_planes] using h

end ArrayObjects.Object.Rolled
end

section
open MeasureTheory ProbabilityTheory
namespace ConditionalFibres
variable {Ω U X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {u : Ω → U}
  {η : Kernel U Ω} [IsMarkovKernel η]

lemma indep_of_screen [StandardBorelSpace X] [StandardBorelSpace Y]
    {x : Ω → X} {y : Ω → Y} {α : Kernel U Y} [IsMarkovKernel α]
    (hx : Measurable x) (hy : Measurable y)
    (hη : HasCondDistrib id u η μ)
    (h : HasCondDistrib y (fun ω => (u ω,x ω)) (α.prodMkRight X) μ) :
    ∀ᵐ a ∂μ.map u, IndepFun x y (η a) := by
  filter_upwards [disintegrate hx hy hη h] with a ha
  have he : (α.prodMkRight X).sectR a = Kernel.const X (α a) := by
    ext x : 1
    rfl
  rw [he] at ha
  apply (indepFun_iff_map_prod_eq_prod_map_map hx.aemeasurable hy.aemeasurable).mpr
  rw [ha.map_eq, ha.hasLaw_of_const.map_eq, Measure.compProd_const]

end ConditionalFibres

namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma rows_indep_fibre (hM : M.IsSaturated) (P A : Finset I)
    (hPA : Disjoint P A) (hproper : P ∪ A ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      IndepFun (parents M P (n+1)) (parents M A (n+1)) (M.ownKernel (n+2) e) := by
  have h := ConditionalReveal.disjoint_families (M.law (n+2)) (amap M.par (n+2))
    (fun a => plane (n+1) 0 a)
    (fun a => (M.ownKernel (n+1)).comap (plane (n+1) 0 a) (measurable_plane _ _ _))
    Finset.subset_union_left Finset.subset_union_right hPA
    (rows_conditional M hM (P∪A) hproper n)
  exact ConditionalFibres.indep_of_screen (measurable_parents M P _) (measurable_parents M A _)
    (M.ownKernel_conditional (n+2)) h

lemma columns_indep_fibre (S D : Finset I)
    (hSD : Disjoint S D) (hproper : S ∪ D ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      IndepFun (planes (n+1) S) (planes (n+1) D) (M.ownKernel (n+2) e) := by
  have h := ConditionalReveal.disjoint_families (M.law (n+2)) (amap M.par (n+2))
    (fun j => plane (n+1) (Fin.last (n+1)) j)
    (fun j => (M.ownKernel (n+1)).comap (plane (n+1) (Fin.last (n+1)) j) (measurable_plane _ _ _))
    Finset.subset_union_left Finset.subset_union_right hSD
    (M.planes_conditional (n+1) (S∪D) hproper)
  exact ConditionalFibres.indep_of_screen (measurable_planes _ _) (measurable_planes _ _)
    (M.ownKernel_conditional (n+2)) h

lemma cells_indep_rows_fibre (hM : M.IsSaturated) (P A S R : Finset I)
    (hPA : Disjoint P A) (hproper : P ∪ A ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      IndepFun (cells M P S n) (cells M A R n) (M.ownKernel (n+2) e) := by
  filter_upwards [rows_indep_fibre M hM P A hPA hproper n] with e he
  exact he.comp (measurable_rowRestrict M P S n) (measurable_rowRestrict M A R n)

lemma cells_indep_columns_fibre (P A S R : Finset I)
    (hSR : Disjoint S R) (hproper : S ∪ R ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      IndepFun (cells M P S n) (cells M A R n) (M.ownKernel (n+2) e) := by
  filter_upwards [columns_indep_fibre M S R hSR hproper n] with e he
  simpa only [columnRestrict_planes] using
    he.comp (measurable_columnRestrict M P S n) (measurable_columnRestrict M A R n)

end ArrayObjects.Object.Rolled
end

namespace JoiningOperator

open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal

section ConditionalMarginals

section
variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {u : Ω → U} {x : Ω → X} {y : Ω → Y} {κ : Kernel U (X × Y)} [IsMarkovKernel κ]
  {ν : Measure X} {ρ : Measure Y}

lemma conditional_pair_marginals [StandardBorelSpace X] [StandardBorelSpace Y]
    (hu : Measurable u) (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hκ : HasCondDistrib (fun ω => (x ω, y ω)) u κ μ)
    (hux : IndepFun u x μ) (huy : IndepFun u y μ) :
    ∀ᵐ a ∂μ.map u,
      MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ := by
  have : IsProbabilityMeasure ν := hx.map_eq ▸ (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hx.aemeasurable
  have : IsProbabilityMeasure ρ := hy.map_eq ▸ (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hy.aemeasurable
  have : IsMarkovKernel (κ.map Prod.fst) := Kernel.IsMarkovKernel.map κ measurable_fst
  have : IsMarkovKernel (κ.map Prod.snd) := Kernel.IsMarkovKernel.map κ measurable_snd
  have hxc : HasCondDistrib x u (Kernel.const U ν) μ := by
    refine ⟨(hu.prodMk hx.measurable).aemeasurable, ?_⟩
    rw [Measure.compProd_const, ← hx.map_eq]
    exact hux.map_prod_eq_prod_map_map hu.aemeasurable hx.aemeasurable
  have hyc : HasCondDistrib y u (Kernel.const U ρ) μ := by
    refine ⟨(hu.prodMk hy.measurable).aemeasurable, ?_⟩
    rw [Measure.compProd_const, ← hy.map_eq]
    exact huy.map_prod_eq_prod_map_map hu.aemeasurable hy.aemeasurable
  have he1 := Kernel.ae_eq_of_compProd_eq
    ((hκ.comp_left measurable_fst).map_eq.symm.trans hxc.map_eq)
  have he2 := Kernel.ae_eq_of_compProd_eq
    ((hκ.comp_left measurable_snd).map_eq.symm.trans hyc.map_eq)
  filter_upwards [he1, he2] with a ha hb
  exact ⟨⟨measurable_fst, (Kernel.map_apply κ measurable_fst a).symm.trans ha⟩,
    ⟨measurable_snd, (Kernel.map_apply κ measurable_snd a).symm.trans hb⟩⟩

omit [IsProbabilityMeasure μ] in
lemma integrable_inner_comp (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    Integrable (fun ω => inner ℂ (g (x ω)) (h (y ω))) μ := by
  apply (L2.integrable_inner (pull hx g) (pull hy h)).congr
  filter_upwards [Lp.coeFn_compMeasurePreserving g hx, Lp.coeFn_compMeasurePreserving h hy]
    with ω hg hh
  change inner ℂ (Lp.compMeasurePreserving x hx g ω) (Lp.compMeasurePreserving y hy h ω) = _
  rw [hg, hh]
  rfl

lemma family_setIntegral (hu : Measurable u)
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hκ : HasCondDistrib (fun ω => (x ω, y ω)) u κ μ)
    (hm : ∀ᵐ a ∂μ.map u,
      MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (A : Set U) (hA : MeasurableSet A) (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    ∫ a in A, inner ℂ g (family κ ν ρ a h) ∂μ.map u =
      ∫ ω in u ⁻¹' A, inner ℂ (g (x ω)) (h (y ω)) ∂μ := by
  let f : U × (X × Y) → ℂ := fun p =>
    (Prod.fst ⁻¹' A).indicator (fun p => inner ℂ (g p.2.1) (h p.2.2)) p
  have hfm : StronglyMeasurable f :=
    ((g.1.stronglyMeasurable.comp_measurable (by fun_prop)).inner
      (h.1.stronglyMeasurable.comp_measurable (by fun_prop))).indicator (measurable_fst hA)
  have hfi : Integrable f (μ.map u ⊗ₘ κ) := by
    rw [← hκ.map_eq]
    apply (integrable_map_measure hfm.aestronglyMeasurable hκ.aemeasurable).mpr
    exact (integrable_inner_comp hx hy g h).indicator (hu hA)
  calc
    _ = ∫ a in A, ∫ p, inner ℂ (g p.1) (h p.2) ∂κ a ∂μ.map u :=
      setIntegral_congr_ae hA ((family_inner hm g h).mono (fun _ ha _ => ha))
    _ = ∫ a, ∫ p, f (a, p) ∂κ a ∂μ.map u := by
      rw [← integral_indicator hA]
      apply integral_congr_ae
      filter_upwards with a
      by_cases ha : a ∈ A <;> simp [f, ha]
    _ = ∫ p, f p ∂μ.map u ⊗ₘ κ := (Measure.integral_compProd hfi).symm
    _ = ∫ ω, f (u ω, x ω, y ω) ∂μ := (hκ.integral_comp hfm.aestronglyMeasurable).symm
    _ = _ := by
      change ∫ ω, (u ⁻¹' A).indicator (fun ω => inner ℂ (g (x ω)) (h (y ω))) ω ∂μ = _
      exact integral_indicator (hu hA)

end


lemma ae_eq_zero_of_rectangles {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
    {m : Measure (U × Y)} {f : U × Y → ℂ} (hf : Integrable f m)
    (hz : ∀ A B, MeasurableSet A → MeasurableSet B → ∫ p in A ×ˢ B, f p ∂m = 0) :
    f =ᵐ[m] 0 := by
  suffices ∀ S, MeasurableSet S → ∫ p in S, f p ∂m = 0 from
    hf.ae_eq_zero_of_forall_setIntegral_eq_zero (fun S hS _ => this S hS)
  intro S hS
  induction S, hS using MeasurableSpace.induction_on_inter generateFrom_prod.symm
      isPiSystem_prod with
  | empty => simp
  | basic S hS =>
    obtain ⟨A, hA, B, hB, rfl⟩ := hS
    exact hz A B hA hB
  | compl S hS ih =>
    have htot : ∫ p, f p ∂m = 0 := by
      simpa using hz Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
    simpa [ih, htot] using integral_add_compl hS hf
  | iUnion S hdis hS ih => simp [integral_iUnion hS hdis hf.integrableOn, ih]

variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  {m : Measure (U × Y)} {ρ : Measure Y}

lemma coe_weightedTest (hy : MeasurePreserving Prod.snd m ρ)
    (A : Set U) (hA : MeasurableSet A) (h : Lp ℂ 2 ρ) :
    (weightedTest hy A hA h : U × Y → ℂ) =ᵐ[m]
      (Prod.fst ⁻¹' A).indicator (fun p => h p.2) := MemLp.coeFn_toLp _

lemma weightedTest_indicator [IsFiniteMeasure m] [IsFiniteMeasure ρ]
    (hy : MeasurePreserving Prod.snd m ρ)
    (A : Set U) (hA : MeasurableSet A) (B : Set Y) (hB : MeasurableSet B) :
    weightedTest hy A hA (indicatorConstLp 2 hB (measure_ne_top ρ B) (1 : ℂ)) =
      indicatorConstLp 2 (hA.prod hB) (measure_ne_top m _) (1 : ℂ) := by
  apply Lp.ext
  filter_upwards [coe_weightedTest hy A hA (indicatorConstLp 2 hB (measure_ne_top ρ B) (1 : ℂ)),
    hy.quasiMeasurePreserving.ae (indicatorConstLp_coeFn (p := 2) (hs := hB) (hμs := measure_ne_top ρ B) (c := (1 : ℂ))),
    indicatorConstLp_coeFn (p := 2) (hs := hA.prod hB) (hμs := measure_ne_top m _) (c := (1 : ℂ))]
    with p hp hq hr
  rw [hp, hr]
  by_cases ha : p.1 ∈ A <;> by_cases hb : p.2 ∈ B <;> simp_all


end ConditionalMarginals


variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {u : Ω → U} {x : Ω → X} {y : Ω → Y} {κ : Kernel U (X × Y)} [IsMarkovKernel κ]
  {ν : Measure X} {ρ : Measure Y}

lemma weighted_inner (hu : Measurable u)
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hκ : HasCondDistrib (fun ω => (x ω, y ω)) u κ μ)
    (hm : ∀ᵐ a ∂μ.map u,
      MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (A : Set U) (hA : MeasurableSet A) (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    inner ℂ g (operator hx ⟨hu.prodMk hy.measurable, rfl⟩
      (weightedTest (snd_observation hu hy) A hA h)) =
      ∫ a in A, inner ℂ g (family κ ν ρ a h) ∂μ.map u := by
  rw [inner_operator, family_setIntegral hu hx hy hκ hm A hA]
  rw [← integral_indicator (hu hA)]
  apply integral_congr_ae
  have hz : MeasurePreserving (fun ω => (u ω, y ω)) μ (μ.map (fun ω => (u ω, y ω))) :=
    ⟨hu.prodMk hy.measurable, rfl⟩
  filter_upwards [hz.quasiMeasurePreserving.ae_eq_comp
    (coe_weightedTest (snd_observation hu hy) A hA h)] with ω hω
  simp only [Function.comp_apply] at hω
  rw [hω]
  by_cases ha : u ω ∈ A <;> simp [ha]

omit [IsMarkovKernel κ] in
lemma family_inner_integrable (hu : Measurable u)
    (hm : ∀ᵐ a ∂μ.map u,
      MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    Integrable (fun a => inner ℂ g (family κ ν ρ a h)) (μ.map u) := by
  have : IsProbabilityMeasure (μ.map u) := (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hu.aemeasurable
  apply Integrable.of_bound (family_inner_aestronglyMeasurable hm g h) (‖g‖ * ‖h‖)
  filter_upwards with a
  calc
    _ ≤ ‖g‖ * ‖family κ ν ρ a h‖ := norm_inner_le_norm _ _
    _ ≤ ‖g‖ * (‖family κ ν ρ a‖ * ‖h‖) :=
      mul_le_mul_of_nonneg_left ((family κ ν ρ a).le_opNorm h) (norm_nonneg _)
    _ ≤ _ := by grw [family_norm_le]; simp

lemma active_kernel [SecondCountableTopology (Lp ℂ 2 ρ)]
    (hu : Measurable u) (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hκ : HasCondDistrib (fun ω => (x ω, y ω)) u κ μ)
    (hm : ∀ᵐ a ∂μ.map u,
      MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (g : Lp ℂ 2 ν) :
    (operator hx ⟨hu.prodMk hy.measurable, rfl⟩).adjoint g = 0 ↔
      ∀ᵐ a ∂μ.map u, (family κ ν ρ a).adjoint g = 0 := by
  let Q := operator hx (show MeasurePreserving (fun ω => (u ω, y ω)) μ
    (μ.map (fun ω => (u ω, y ω))) from ⟨hu.prodMk hy.measurable, rfl⟩)
  have : IsProbabilityMeasure (μ.map (fun ω => (u ω, y ω))) :=
    (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (hu.prodMk hy.measurable).aemeasurable
  have : IsProbabilityMeasure ρ := hy.map_eq ▸ (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hy.aemeasurable
  constructor
  · intro hz
    have hh (h : Lp ℂ 2 ρ) : ∀ᵐ a ∂μ.map u, inner ℂ g (family κ ν ρ a h) = 0 := by
      apply (family_inner_integrable hu hm g h).ae_eq_zero_of_forall_setIntegral_eq_zero
      intro A hA _
      rw [← weighted_inner hu hx hy hκ hm A hA, ← adjoint_inner_left, hz, inner_zero_left]
    filter_upwards [ae_all_iff.mpr (fun n => hh (TopologicalSpace.denseSeq (Lp ℂ 2 ρ) n))]
      with a ha
    have he : (fun h : Lp ℂ 2 ρ => inner ℂ ((family κ ν ρ a).adjoint g) h) =
        (fun _ => (0 : ℂ)) := by
      apply (TopologicalSpace.denseRange_denseSeq (Lp ℂ 2 ρ)).equalizer (by fun_prop) (by fun_prop)
      funext n
      simpa only [Function.comp_apply, adjoint_inner_left] using ha n
    exact (inner_self_eq_zero (𝕜 := ℂ)).mp (congrFun he ((family κ ν ρ a).adjoint g))
  · intro hz
    apply Lp.ext
    apply (ae_eq_zero_of_rectangles (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp (Q.adjoint g))) ?_).trans
      (Lp.coeFn_zero _ _ _).symm
    intro A B hA hB
    rw [← L2.inner_indicatorConstLp_one (hA.prod hB) (measure_ne_top _ _)]
    apply inner_eq_zero_symm.mp
    rw [← weightedTest_indicator (snd_observation hu hy) A hA B hB, adjoint_inner_left]
    change inner ℂ g (operator hx ⟨hu.prodMk hy.measurable, rfl⟩ _) = 0
    rw [weighted_inner hu hx hy hκ hm A hA]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae hz] with a ha
    simp only [← adjoint_inner_left, ha, inner_zero_left, Pi.zero_apply]

end JoiningOperator

namespace JoiningOperator
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal

section
variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {u : Ω → U} {x : Ω → X} {y : Ω → Y} {κ : Kernel U (X × Y)} [IsMarkovKernel κ]
  {ν : Measure X} {ρ : Measure Y}

lemma active_eq_essentialRange [SecondCountableTopology (Lp ℂ 2 ρ)]
    (hu : Measurable u) (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hκ : HasCondDistrib (fun ω => (x ω, y ω)) u κ μ)
    (hm : ∀ᵐ a ∂μ.map u,
      MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ) :
    (LinearMap.range (operator hx ⟨hu.prodMk hy.measurable, rfl⟩).toLinearMap).topologicalClosure =
      essentialRange (μ.map u) (family κ ν ρ) := by
  let Q := operator hx (show MeasurePreserving (fun ω => (u ω, y ω)) μ
    (μ.map (fun ω => (u ω, y ω))) from ⟨hu.prodMk hy.measurable, rfl⟩)
  have hker : Q.adjoint.ker = essentialKernel (μ.map u) (fun a => (family κ ν ρ a).adjoint) := by
    ext g
    exact active_kernel hu hx hy hκ hm g
  have h := (orthogonal_ker Q.adjoint).symm
  rw [adjoint_adjoint, hker] at h
  exact h
end


end JoiningOperator

namespace ArrayObjects.Object.Rolled
open scoped ENNReal
open MeasureTheory ProbabilityTheory
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma cells_conditional (hM : M.IsSaturated) (A S : Finset I)
    (hA : A ≠ Finset.univ) (n : ℕ) :
    HasCondDistrib (cells M A S n) (amap M.par (n+2)) (groupMarginal M A S n) (M.law (n+2)) := by
  exact (rows_conditional M hM A hA n).comp_left (measurable_rowRestrict M A S n)

lemma cells_fibre_marginal (hM : M.IsSaturated) (A S : Finset I)
    (hA : A ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      MeasurePreserving (cells M A S n) (M.ownKernel (n+2) e) (cellLaw M A S n e) :=
  ConditionalFibres.marginal (measurable_cells M A S n) (M.ownKernel_conditional (n+2))
    (cells_conditional M hM A S hA n)

omit [DecidableEq I] in
lemma rowPair_fixed_conditional (A R S D : Finset I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      HasCondDistrib (fun y => (cells M A S n y,cells M A D n y)) (cells M A R n)
        ((rowPairKernel M A R S D n).sectR e) (M.ownKernel (n+2) e) := by
  apply ConditionalFibres.disintegrate (measurable_cells M A R n) (by fun_prop)
    (M.ownKernel_conditional (n+2))
  exact ⟨((measurable_amap M.measurable_par _).prodMk (measurable_cells M A R n)).prodMk
    ((measurable_cells M A S n).prodMk (measurable_cells M A D n)) |>.aemeasurable, (compProd_map_condDistrib (μ := M.law (n+2))
    ((measurable_cells M A S n).prodMk (measurable_cells M A D n)).aemeasurable).symm⟩

lemma columnPair_own_conditional (hM : M.IsSaturated) (P A B S : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hS : S ≠ Finset.univ) (n : ℕ) :
    HasCondDistrib (fun y => (cells M A S n y,cells M B S n y)) (groupData M P S n)
      (columnPairKernel M P A B S n) (M.law (n+2)) := by
  have h := (columnPair_conditional M hM P A B ∅ S hP (Finset.disjoint_empty_left S)
    (by simpa using hS) n).comp_right
  exact h

lemma columnPair_fixed_conditional (hM : M.IsSaturated) (P A B S : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hS : S ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      HasCondDistrib (fun y => (cells M A S n y,cells M B S n y)) (cells M P S n)
        ((columnPairKernel M P A B S n).sectR e) (M.ownKernel (n+2) e) :=
  ConditionalFibres.disintegrate (measurable_cells M P S n) (by fun_prop)
    (M.ownKernel_conditional (n+2)) (columnPair_own_conditional M hM P A B S hP hS n)

omit [DecidableEq I] in
lemma fibreRowEdge_eq (A R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    fibreRowEdge M A R S D n e = JoiningOperator.family ((rowPairKernel M A R S D n).sectR e)
      (cellLaw M A S n e) (cellLaw M A D n e) := by
  ext x h
  rfl

omit [DecidableEq I] in
lemma fibreColumnEdge_eq (P A B S : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    fibreColumnEdge M P A B S n e = JoiningOperator.family ((columnPairKernel M P A B S n).sectR e)
      (cellLaw M A S n e) (cellLaw M B S n e) := by
  ext x h
  rfl

lemma rowPair_fixed_marginals (hM : M.IsSaturated) (A R S D : Finset I)
    (hA : A ≠ Finset.univ) (hRS : Disjoint R S) (hRD : Disjoint R D)
    (hproperRS : R ∪ S ≠ Finset.univ) (hproperRD : R ∪ D ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ᵐ x ∂(M.ownKernel (n+2) e).map (cells M A R n),
        MeasurePreserving Prod.fst (rowPairKernel M A R S D n (e,x)) (cellLaw M A S n e) ∧
        MeasurePreserving Prod.snd (rowPairKernel M A R S D n (e,x)) (cellLaw M A D n e) := by
  filter_upwards [rowPair_fixed_conditional M A R S D n,
    cells_fibre_marginal M hM A S hA n, cells_fibre_marginal M hM A D hA n,
    cells_indep_columns_fibre M A A R S hRS hproperRS n,
    cells_indep_columns_fibre M A A R D hRD hproperRD n] with e hκ hs hd hrs hrd
  exact JoiningOperator.conditional_pair_marginals (measurable_cells M A R n) hs hd hκ hrs hrd

lemma columnPair_fixed_marginals (hM : M.IsSaturated) (P A B S : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hS : S ≠ Finset.univ)
    (hA : A ≠ Finset.univ) (hB : B ≠ Finset.univ)
    (hPA : Disjoint P A) (hPB : Disjoint P B)
    (hproperPA : P ∪ A ≠ Finset.univ) (hproperPB : P ∪ B ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ᵐ c ∂(M.ownKernel (n+2) e).map (cells M P S n),
        MeasurePreserving Prod.fst (columnPairKernel M P A B S n (e,c)) (cellLaw M A S n e) ∧
        MeasurePreserving Prod.snd (columnPairKernel M P A B S n (e,c)) (cellLaw M B S n e) := by
  filter_upwards [columnPair_fixed_conditional M hM P A B S hP hS n,
    cells_fibre_marginal M hM A S hA n, cells_fibre_marginal M hM B S hB n,
    cells_indep_rows_fibre M hM P A S S hPA hproperPA n,
    cells_indep_rows_fibre M hM P B S S hPB hproperPB n] with e hκ hs hd hrs hrd
  exact JoiningOperator.conditional_pair_marginals (measurable_cells M P S n) hs hd hκ hrs hrd

end ArrayObjects.Object.Rolled

section

namespace TriplePartition
variable {I : Type*} [Fintype I] [DecidableEq I] (s : TriplePartition I)
lemma properPA : s.P ∪ s.A ≠ Finset.univ := by
  intro h
  obtain ⟨b,hb⟩ := s.nonemptyB
  exact Finset.disjoint_left.mp (Finset.disjoint_union_left.mpr ⟨s.disjointPB,s.disjointAB⟩)
    (h ▸ Finset.mem_univ b) hb
lemma properPB : s.P ∪ s.B ≠ Finset.univ := by
  intro h
  obtain ⟨a,ha⟩ := s.nonemptyA
  exact Finset.disjoint_left.mp (Finset.disjoint_union_left.mpr ⟨s.disjointPA,s.disjointAB.symm⟩)
    (h ▸ Finset.mem_univ a) ha
lemma properAB : s.A ∪ s.B ≠ Finset.univ := by
  intro h
  obtain ⟨p,hp⟩ := s.nonemptyP
  exact Finset.disjoint_left.mp (Finset.disjoint_union_left.mpr ⟨s.disjointPA.symm,s.disjointPB.symm⟩)
    (h ▸ Finset.mem_univ p) hp
lemma properP : s.P ≠ Finset.univ := by
  intro h
  apply s.properPA
  simp [h]
lemma properA : s.A ≠ Finset.univ := by
  intro h
  apply s.properPA
  simp [h]
lemma properB : s.B ≠ Finset.univ := by
  intro h
  apply s.properPB
  simp [h]
end TriplePartition

open MeasureTheory
end

namespace StrongUnitary
open MeasureTheory Filter Topology
open scoped Topology
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SecondCountableTopology E]

lemma code_injective : Function.Injective (code : (E ≃ₗᵢ[ℂ] H) → ℕ → H) := by
  intro U V h
  apply DFunLike.ext'
  exact (TopologicalSpace.denseRange_denseSeq E).equalizer U.continuous V.continuous h

lemma code_embedding : IsEmbedding (code : (E ≃ₗᵢ[ℂ] H) → ℕ → H) :=
  ⟨⟨rfl⟩, code_injective⟩

instance t2 : T2Space (E ≃ₗᵢ[ℂ] H) := code_embedding.t2Space
instance metrizable : TopologicalSpace.MetrizableSpace (E ≃ₗᵢ[ℂ] H) := code_embedding.metrizableSpace
instance secondCountable [SecondCountableTopology H] : SecondCountableTopology (E ≃ₗᵢ[ℂ] H) :=
  code_embedding.secondCountableTopology

lemma continuous_eval : Continuous (fun p : (E ≃ₗᵢ[ℂ] H) × E => p.1 p.2) := by
  apply continuous_prod_of_dense_continuous_lipschitzWith' _ 1
    (TopologicalSpace.denseRange_denseSeq E)
  · intro U; exact U.isometry.lipschitz
  · rintro _ ⟨n, rfl⟩
    exact (continuous_apply n).comp code_embedding.continuous

lemma continuous_apply (v : E) : Continuous (fun U : E ≃ₗᵢ[ℂ] H => U v) :=
  continuous_eval.comp (continuous_id.prodMk continuous_const)

lemma continuous_iff {X : Type*} [TopologicalSpace X] {f : X → E ≃ₗᵢ[ℂ] H} :
    Continuous f ↔ ∀ v, Continuous (fun x => f x v) := by
  constructor
  · intro h v; exact (continuous_apply v).comp h
  · intro h
    exact code_embedding.isInducing.continuous_iff.mpr (continuous_pi (fun n => h _))

lemma tendsto_iff {X : Type*} {l : Filter X} {f : X → E ≃ₗᵢ[ℂ] H} {U : E ≃ₗᵢ[ℂ] H} :
    Tendsto f l (𝓝 U) ↔ ∀ v, Tendsto (fun x => f x v) l (𝓝 (U v)) := by
  constructor
  · intro h v; exact ((continuous_apply v).tendsto U).comp h
  · intro h
    exact code_embedding.isInducing.tendsto_nhds_iff.mpr (tendsto_pi_nhds.mpr (fun n => h _))

lemma continuous_symm [SecondCountableTopology H] :
    Continuous (fun U : E ≃ₗᵢ[ℂ] H => U.symm) := by
  rw [_root_.continuous_iff_continuousAt]
  intro U
  apply tendsto_iff.mpr
  intro v
  rw [tendsto_iff_dist_tendsto_zero]
  have hh := ((continuous_apply (U.symm v)).tendsto U).dist (tendsto_const_nhds (x := v))
  have he (V : E ≃ₗᵢ[ℂ] H) : dist (V.symm v) (U.symm v) = dist (V (U.symm v)) v := by
    rw [← V.dist_map, V.apply_symm_apply, dist_comm]
  simp only [he, U.apply_symm_apply, dist_self] at hh ⊢
  exact hh

instance topologicalGroup : IsTopologicalGroup (E ≃ₗᵢ[ℂ] E) where
  continuous_mul := continuous_iff.mpr (fun v =>
    continuous_eval.comp (continuous_fst.prodMk ((continuous_apply v).comp continuous_snd)))
  continuous_inv := continuous_symm
end StrongUnitary

namespace ArrayObjects.Object.Rolled

open ContinuousLinearMap MeasureTheory ProbabilityTheory
open scoped ENNReal


universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma pairPair_conditional (hM : M.IsSaturated) (P A B R S D : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hR : R ≠ Finset.univ) (n : ℕ) :
    HasCondDistrib (fun y => ((cells M A R n y,cells M B R n y),
      (cells M P S n y,cells M P D n y))) (groupData M P R n)
      ((columnPairKernel M P A B R n) ×ₖ (rowPairKernel M P R S D n)) (M.law (n+2)) := by
  let H : WholeGroupData M P ∅ n → GroupData M P R n ×
      ((S → P → Arr I M.Y n) × (D → P → Arr I M.Y n)) := fun q =>
    ((q.1.1,rowRestrict M P R n q.1.2),
      (rowRestrict M P S n q.1.2,rowRestrict M P D n q.1.2))
  have hH : Measurable H := by
    exact ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_rowRestrict M P R n).comp (measurable_snd.comp measurable_fst))).prodMk
        (((measurable_rowRestrict M P S n).comp (measurable_snd.comp measurable_fst)).prodMk
          ((measurable_rowRestrict M P D n).comp (measurable_snd.comp measurable_fst)))
  have hh := columnPair_conditional M hM P A B ∅ R hP (Finset.disjoint_empty_left R)
    (by simpa using hR) n
  have he : (columnPairKernel M P A B R n).comap (columnOwnData M P ∅ R n)
      (measurable_columnOwnData M P ∅ R n) =
      ((columnPairKernel M P A B R n).prodMkRight
        ((S → P → Arr I M.Y n) × (D → P → Arr I M.Y n))).comap H hH := by
    ext q : 1
    rfl
  rw [he] at hh
  have hx := hh.comp_right
  have hc : HasCondDistrib (fun y => (cells M P S n y,cells M P D n y))
      (groupData M P R n) (rowPairKernel M P R S D n) (M.law (n+2)) := by
    exact ⟨((measurable_groupData M P R n).prodMk
      ((measurable_cells M P S n).prodMk (measurable_cells M P D n))).aemeasurable,
      (compProd_map_condDistrib (μ := M.law (n+2))
        ((measurable_cells M P S n).prodMk (measurable_cells M P D n)).aemeasurable).symm⟩
  have h := ConditionalFibres.chain hc hx
  rw [ConditionalScreens.compProd_prodMkRight] at h
  have h' := h.comp_left measurable_swap
  simpa only [Function.comp_def,Prod.swap_prod_mk,Kernel.map_prod_swap] using h'

lemma pairPair_fixed_conditional (hM : M.IsSaturated) (P A B R S D : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hR : R ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      HasCondDistrib (fun y => ((cells M A R n y,cells M B R n y),
        (cells M P S n y,cells M P D n y))) (cells M P R n)
        (((columnPairKernel M P A B R n).sectR e) ×ₖ ((rowPairKernel M P R S D n).sectR e))
        (M.ownKernel (n+2) e) := by
  let : StandardBorelSpace (R → A → Arr I M.Y n) := inferInstance
  let : StandardBorelSpace (R → B → Arr I M.Y n) := inferInstance
  let : StandardBorelSpace (S → P → Arr I M.Y n) := inferInstance
  let : StandardBorelSpace (D → P → Arr I M.Y n) := inferInstance
  have h := ConditionalFibres.disintegrate (measurable_cells M P R n) (by fun_prop)
    (M.ownKernel_conditional (n+2)) (pairPair_conditional M hM P A B R S D hP hR n)
  filter_upwards [h] with e he
  have hk : ((columnPairKernel M P A B R n) ×ₖ (rowPairKernel M P R S D n)).sectR e =
      ((columnPairKernel M P A B R n).sectR e) ×ₖ ((rowPairKernel M P R S D n).sectR e) := by
    ext z : 1
    simp only [Kernel.sectR_apply, Kernel.prod_apply]
  rwa [hk] at he
end ArrayObjects.Object.Rolled

section

open MeasureTheory Filter
open scoped Topology ProbabilityTheory


section MeasureSupport

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Y] [T2Space Z]

theorem mem_support_map_of_continuous {μ : Measure X} {f : X → Y}
    (hf : Continuous f) {x : X} (hx : x ∈ μ.support) :
    f x ∈ (μ.map f).support := by
  rw [Measure.support_eq_forall_isOpen]
  intro U hxU hU
  rw [Measure.map_apply hf.measurable hU.measurableSet]
  exact (Measure.mem_support_iff_forall x).mp hx (f ⁻¹' U)
    (hf.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU))

omit [BorelSpace X] in

theorem eqOn_support_of_ae_eq {μ : Measure X} {f g : X → Z}
    (hf : Continuous f) (hg : Continuous g) (h : f =ᵐ[μ] g) :
    Set.EqOn f g μ.support :=
  Measure.support_subset_of_isClosed (isClosed_eq hf hg) h

omit [BorelSpace X] [BorelSpace Y] in

theorem eqOn_support_prod_of_ae_eq {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {f g : X × Y → Z}
    (hf : Continuous f) (hg : Continuous g) (h : f =ᵐ[μ.prod ν] g) :
    ∀ x ∈ μ.support, ∀ y ∈ ν.support, f (x, y) = g (x, y) := by
  have h' : ∀ᵐ x ∂μ, ∀ y ∈ ν.support, f (x, y) = g (x, y) := by
    filter_upwards [Measure.ae_ae_of_ae_prod h] with x hx
    exact eqOn_support_of_ae_eq (hf.comp (continuous_const.prodMk continuous_id))
      (hg.comp (continuous_const.prodMk continuous_id)) hx
  intro x hx y hy
  exact eqOn_support_of_ae_eq (hf.comp (continuous_id.prodMk continuous_const))
    (hg.comp (continuous_id.prodMk continuous_const)) (h'.mono fun _ ht => ht y hy) hx

end MeasureSupport

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

theorem continuous_translateProbability [FirstCountableTopology G] (ρ : ProbabilityMeasure G) :
    Continuous (fun p : G × G => translateProbability ρ p.1 p.2) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have hrepr : (fun p : G × G => ∫ a, f a ∂(translateProbability ρ p.1 p.2 : Measure G)) =
      (fun p : G × G => ∫ a, f (p.1 * a * p.2⁻¹) ∂(ρ : Measure G)) := by
    funext p
    rw [translateProbability_toMeasure]
    exact integral_map ((continuous_const.mul continuous_id).mul
      continuous_const).measurable.aemeasurable f.continuous.measurable.aestronglyMeasurable
  rw [hrepr]
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro p
    exact (f.continuous.comp ((continuous_const.mul continuous_id).mul
      continuous_const)).measurable.aestronglyMeasurable
  · intro p
    exact Eventually.of_forall fun a => f.norm_coe_le_norm _
  · exact integrable_const _
  · exact Eventually.of_forall fun a =>
      f.continuous.comp ((continuous_fst.mul continuous_const).mul continuous_snd.inv)

theorem translateProbability_eq_on_support
    [FirstCountableTopology G] [HasOuterApproxClosed G]
    (ρ τ : ProbabilityMeasure G)
    (h : ∀ᵐ p ∂(τ : Measure G).prod τ,
      translateProbability ρ p.1 p.2 = ρ) :
    ∀ u ∈ (τ : Measure G).support, ∀ v ∈ (τ : Measure G).support,
      translateProbability ρ u v = ρ := by
  exact eqOn_support_prod_of_ae_eq (continuous_translateProbability ρ) continuous_const h

theorem map_mulLeft_inv_eq_of_eq (μ : Measure G) (u : G)
    (h : μ.map (u * ·) = μ) : μ.map (u⁻¹ * ·) = μ := by
  calc
    μ.map (u⁻¹ * ·) = (μ.map (u * ·)).map (u⁻¹ * ·) := by rw [h]
    _ = μ.map id := by
      rw [Measure.map_map (g := fun x => u⁻¹ * x) (f := fun x => u * x)
        (continuous_const.mul continuous_id).measurable
        (continuous_const.mul continuous_id).measurable]
      congr 1
      funext a
      simp
    _ = μ := Measure.map_id

theorem common_abelian_support_of_translated_laws
    [FirstCountableTopology G] [HasOuterApproxClosed G]
    (ρ τ : ProbabilityMeasure G)
    (hρ1 : (1 : G) ∈ (ρ : Measure G).support)
    (hτ1 : (1 : G) ∈ (τ : Measure G).support)
    (hρ : ∀ᵐ p ∂(τ : Measure G).prod τ,
      translateProbability ρ p.1 p.2 = ρ)
    (hτ : ∀ᵐ p ∂(ρ : Measure G).prod ρ,
      translateProbability τ p.1 p.2 = τ)
    (hcomm : ∀ u ∈ (ρ : Measure G).support,
      ∀ v ∈ (τ : Measure G).support, u * v = v * u) :
    ∃ H : Subgroup G, IsClosed (H : Set G) ∧
      (ρ : Measure G).support = H ∧ (τ : Measure G).support = H ∧
      (∀ u ∈ H, ∀ v ∈ H, u * v = v * u) ∧
      (∀ u ∈ H, (ρ : Measure G).map (u * ·) = ρ) := by
  have hρ' := translateProbability_eq_on_support ρ τ hρ
  have hτ' := translateProbability_eq_on_support τ ρ hτ
  have hleftρ : ∀ u ∈ (τ : Measure G).support,
      (ρ : Measure G).map (u * ·) = ρ := by
    intro u hu
    simpa using congrArg ProbabilityMeasure.toMeasure (hρ' u hu 1 hτ1)
  have hleftτ : ∀ u ∈ (ρ : Measure G).support,
      (τ : Measure G).map (u * ·) = τ := by
    intro u hu
    simpa using congrArg ProbabilityMeasure.toMeasure (hτ' u hu 1 hρ1)
  have hsub₁ : (τ : Measure G).support ⊆ (ρ : Measure G).support := by
    intro u hu
    have hm := mem_support_map_of_continuous (f := fun x => u * x)
      (continuous_const.mul continuous_id : Continuous (u * ·)) hρ1
    simpa [hleftρ u hu] using hm
  have hsub₂ : (ρ : Measure G).support ⊆ (τ : Measure G).support := by
    intro u hu
    have hm := mem_support_map_of_continuous (f := fun x => u * x)
      (continuous_const.mul continuous_id : Continuous (u * ·)) hτ1
    simpa [hleftτ u hu] using hm
  have heq : (τ : Measure G).support = (ρ : Measure G).support :=
    Set.Subset.antisymm hsub₁ hsub₂
  have hinv : ∀ u ∈ (ρ : Measure G).support,
      (ρ : Measure G).map (u * ·) = ρ := fun u hu => hleftρ u (hsub₂ hu)
  let H : Subgroup G :=
    { carrier := (ρ : Measure G).support
      one_mem' := hρ1
      mul_mem' := by
        intro u v hu hv
        have hm := mem_support_map_of_continuous (f := fun x => u * x)
          (continuous_const.mul continuous_id : Continuous (u * ·)) hv
        simpa [hinv u hu] using hm
      inv_mem' := by
        intro u hu
        have hm := mem_support_map_of_continuous (f := fun x => u⁻¹ * x)
          (continuous_const.mul continuous_id : Continuous (u⁻¹ * ·)) hρ1
        simpa [map_mulLeft_inv_eq_of_eq (ρ : Measure G) u (hinv u hu)] using hm }
  exact ⟨H, Measure.isClosed_support, rfl, heq,
    fun u hu v hv => hcomm u hu v (hsub₂ hv), hinv⟩

theorem normalized_rectangle_support
    [T2Space G] [SecondCountableTopology G]
    (μ ν : Measure (G × G)) [SFinite μ] [SFinite ν]
    (hμ1 : (1, 1) ∈ μ.support) (hν1 : (1, 1) ∈ ν.support)
    (hrect : ∀ᵐ p ∂μ.prod ν, p.1.1 * p.2.2 = p.2.1 * p.1.2) :
    μ.map Prod.fst = μ.map Prod.snd ∧
    ν.map Prod.fst = ν.map Prod.snd ∧
    (1 : G) ∈ (μ.map Prod.fst).support ∧
    (1 : G) ∈ (ν.map Prod.fst).support ∧
    (∀ u ∈ (μ.map Prod.fst).support, ∀ v ∈ (ν.map Prod.fst).support,
      u * v = v * u) := by
  have hsup := eqOn_support_prod_of_ae_eq
    ((continuous_fst.fst).mul (continuous_snd.snd))
    ((continuous_snd.fst).mul (continuous_fst.snd)) hrect
  have hdiagμ : ∀ᵐ p ∂μ, p.1 = p.2 := by
    filter_upwards [Measure.support_mem_ae (μ := μ)] with p hp
    simpa using hsup p hp (1, 1) hν1
  have hdiagν : ∀ᵐ p ∂ν, p.1 = p.2 := by
    filter_upwards [Measure.support_mem_ae (μ := ν)] with p hp
    simpa using (hsup (1, 1) hμ1 p hp).symm
  refine ⟨Measure.map_congr hdiagμ, Measure.map_congr hdiagν,
    mem_support_map_of_continuous continuous_fst hμ1,
    mem_support_map_of_continuous continuous_fst hν1, ?_⟩
  have hcomm : ∀ᵐ p ∂(μ.map Prod.fst).prod (ν.map Prod.fst),
      p.1 * p.2 = p.2 * p.1 := by
    rw [Measure.map_prod_map μ ν measurable_fst measurable_fst]
    apply (ae_map_iff (measurable_fst.prodMap measurable_fst).aemeasurable
      (isClosed_eq (continuous_fst.mul continuous_snd)
        (continuous_snd.mul continuous_fst)).measurableSet).mpr
    have hmeas : MeasurableSet {p : (G × G) × (G × G) |
        p.1.1 * p.2.1 = p.2.1 * p.1.1} :=
      (isClosed_eq (continuous_fst.fst.mul continuous_snd.fst)
        (continuous_snd.fst.mul continuous_fst.fst)).measurableSet
    apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
    filter_upwards [Measure.ae_ae_of_ae_prod hrect, hdiagμ] with p hp hdp
    filter_upwards [hp, hdiagν] with q hpq hdq
    simpa only [hdp, hdq] using hpq
  exact eqOn_support_prod_of_ae_eq (continuous_fst.mul continuous_snd)
    (continuous_snd.mul continuous_fst) hcomm

theorem translated_law_of_rectangle (ρ : ProbabilityMeasure G)
    (μ : Measure (G × G)) (hf : μ.map Prod.fst = ρ) (hs : μ.map Prod.snd = ρ)
    (u v : G) (h : ∀ᵐ p ∂μ, p.1 * v = u * p.2) :
    translateProbability ρ u v = ρ := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [translateProbability_toMeasure]
  calc
    (ρ : Measure G).map (fun a => u * a * v⁻¹) =
        (μ.map Prod.snd).map (fun a => u * a * v⁻¹) := by rw [hs]
    _ = μ.map ((fun a => u * a * v⁻¹) ∘ Prod.snd) :=
      Measure.map_map (g := fun a => u * a * v⁻¹) (f := Prod.snd)
        ((continuous_const.mul continuous_id).mul continuous_const).measurable measurable_snd
    _ = μ.map Prod.fst := by
      apply Measure.map_congr
      filter_upwards [h] with p hp
      change u * p.2 * v⁻¹ = p.1
      rw [← hp]
      simp [mul_assoc]
    _ = ρ := hf

theorem ae_translated_law_of_rectangle [T2Space G] [SecondCountableTopology G]
    (ρ : ProbabilityMeasure G) (μ ν : Measure (G × G)) [SFinite μ] [SFinite ν]
    (hf : μ.map Prod.fst = ρ) (hs : μ.map Prod.snd = ρ)
    (h : ∀ᵐ p ∂μ.prod ν, p.1.1 * p.2.2 = p.2.1 * p.1.2) :
    ∀ᵐ q ∂ν, translateProbability ρ q.1 q.2 = ρ := by
  have hmeas : MeasurableSet {p : (G × G) × (G × G) |
      p.1.1 * p.2.2 = p.2.1 * p.1.2} :=
    (isClosed_eq (continuous_fst.fst.mul continuous_snd.snd)
      (continuous_snd.fst.mul continuous_fst.snd)).measurableSet
  have h' := (Measure.ae_ae_comm hmeas).mp (Measure.ae_ae_of_ae_prod h)
  filter_upwards [h'] with q hq
  exact translated_law_of_rectangle ρ μ hf hs q.1 q.2 hq

theorem ae_translated_law_of_kernel_rectangle
    [T2Space G] [SecondCountableTopology G] [HasOuterApproxClosed G]
    {Z : Type*} [MeasurableSpace Z] (σ : Measure Z)
    (μ ν : ProbabilityTheory.Kernel Z (G × G))
    [ProbabilityTheory.IsSFiniteKernel μ] [ProbabilityTheory.IsSFiniteKernel ν]
    (ρ : ProbabilityMeasure G)
    (h : ∀ᵐ z ∂σ,
      (μ z).map Prod.fst = ρ ∧ (μ z).map Prod.snd = ρ ∧
      ∀ᵐ p ∂(μ z).prod (ν z), p.1.1 * p.2.2 = p.2.1 * p.1.2) :
    ∀ᵐ q ∂ν ∘ₘ σ, translateProbability ρ q.1 q.2 = ρ := by
  apply Measure.ae_comp_of_ae_ae
    (isClosed_eq (continuous_translateProbability ρ) continuous_const).measurableSet
  filter_upwards [h] with z hz
  exact ae_translated_law_of_rectangle ρ (μ z) (ν z) hz.1 hz.2.1 hz.2.2

theorem normalized_polar_group_from_kernels
    [T2Space G] [SecondCountableTopology G] [HasOuterApproxClosed G]
    {Z : Type*} [MeasurableSpace Z] (σ : Measure Z)
    (μ ν : ProbabilityTheory.Kernel Z (G × G))
    [ProbabilityTheory.IsSFiniteKernel μ] [ProbabilityTheory.IsSFiniteKernel ν]
    (ρ τ : ProbabilityMeasure G)
    (h : ∀ᵐ z ∂σ,
      (μ z).map Prod.fst = ρ ∧ (μ z).map Prod.snd = ρ ∧
      (ν z).map Prod.fst = τ ∧ (ν z).map Prod.snd = τ ∧
      ∀ᵐ p ∂(μ z).prod (ν z), p.1.1 * p.2.2 = p.2.1 * p.1.2)
    (hμ : μ ∘ₘ σ = (ρ : Measure G).prod ρ)
    (hν : ν ∘ₘ σ = (τ : Measure G).prod τ)
    (z₀ : Z)
    (h₀ : (μ z₀).map Prod.fst = ρ ∧ (ν z₀).map Prod.fst = τ ∧
      (1, 1) ∈ (μ z₀).support ∧ (1, 1) ∈ (ν z₀).support ∧
      ∀ᵐ p ∂(μ z₀).prod (ν z₀), p.1.1 * p.2.2 = p.2.1 * p.1.2) :
    ∃ H : Subgroup G, IsClosed (H : Set G) ∧
      (ρ : Measure G).support = H ∧ (τ : Measure G).support = H ∧
      (∀ u ∈ H, ∀ v ∈ H, u * v = v * u) ∧
      (∀ u ∈ H, (ρ : Measure G).map (u * ·) = ρ) := by
  have hnormal := normalized_rectangle_support (μ z₀) (ν z₀)
    h₀.2.2.1 h₀.2.2.2.1 h₀.2.2.2.2
  rw [h₀.1, h₀.2.1] at hnormal
  have hρ : ∀ᵐ q ∂(τ : Measure G).prod τ,
      translateProbability ρ q.1 q.2 = ρ := by
    rw [← hν]
    apply ae_translated_law_of_kernel_rectangle σ μ ν ρ
    filter_upwards [h] with z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.2.2⟩
  have hτ : ∀ᵐ p ∂(ρ : Measure G).prod ρ,
      translateProbability τ p.1 p.2 = τ := by
    rw [← hμ]
    apply ae_translated_law_of_kernel_rectangle σ ν μ τ
    filter_upwards [h] with z hz
    refine ⟨hz.2.2.1, hz.2.2.2.1, ?_⟩
    have ht := (Measure.measurePreserving_swap (μ := ν z) (ν := μ z)).quasiMeasurePreserving.ae hz.2.2.2.2
    filter_upwards [ht] with p hp
    exact hp.symm
  exact common_abelian_support_of_translated_laws ρ τ
    hnormal.2.2.1 hnormal.2.2.2.1 hρ hτ hnormal.2.2.2.2

end

namespace StrongUnitary
open MeasureTheory ProbabilityTheory
open scoped Topology
variable {H₁ H₂ H₃ H₄ : Type*}
  [NormedAddCommGroup H₁] [NormedSpace ℂ H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [NormedSpace ℂ H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [NormedSpace ℂ H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [NormedSpace ℂ H₄] [SecondCountableTopology H₄]

omit [SecondCountableTopology H₃] in
lemma continuous_trans : Continuous (fun p : (H₁ ≃ₗᵢ[ℂ] H₂) × (H₂ ≃ₗᵢ[ℂ] H₃) =>
    p.1.trans p.2) := by
  apply continuous_iff.mpr
  intro v
  exact continuous_eval.comp (continuous_snd.prodMk ((continuous_apply v).comp continuous_fst))

lemma support_rectangle (μ : Measure ((H₂ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₃)))
    (ν : Measure ((H₃ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₂))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hr : ∀ᵐ p ∂μ.prod ν, p.2.2.trans p.1.1 = p.1.2.trans p.2.1) :
    ∃ a₀ b₀ c₀ d₀, (a₀,b₀) ∈ μ.support ∧ (c₀,d₀) ∈ ν.support ∧
      d₀.trans a₀ = b₀.trans c₀ := by
  obtain ⟨⟨a₀,b₀⟩, hab⟩ := (show ∀ᵐ p ∂μ, p ∈ μ.support from Measure.support_mem_ae).exists
  obtain ⟨⟨c₀,d₀⟩, hcd⟩ := (show ∀ᵐ p ∂ν, p ∈ ν.support from Measure.support_mem_ae).exists
  refine ⟨a₀,b₀,c₀,d₀,hab,hcd,?_⟩
  exact eqOn_support_prod_of_ae_eq
    (continuous_trans.comp (continuous_snd.snd.prodMk continuous_fst.fst))
    (continuous_trans.comp (continuous_fst.snd.prodMk continuous_snd.fst)) hr
      (a₀,b₀) hab (c₀,d₀) hcd

omit [SecondCountableTopology H₁] in
lemma continuous_normalizeA (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂) :
    Continuous (normalizeA a₀ d₀) := by
  apply continuous_iff.mpr
  intro v
  exact (d₀.trans a₀).symm.continuous.comp (continuous_apply (d₀ v))
omit [SecondCountableTopology H₃] in
lemma continuous_normalizeB (b₀ : H₄ ≃ₗᵢ[ℂ] H₃) : Continuous (normalizeB b₀) := by
  apply continuous_iff.mpr
  intro v
  exact b₀.symm.continuous.comp (continuous_apply v)
omit [SecondCountableTopology H₁] [SecondCountableTopology H₂] in
lemma continuous_normalizeC (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (b₀ : H₄ ≃ₗᵢ[ℂ] H₃) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂) :
    Continuous (normalizeC a₀ b₀ d₀) := by
  apply continuous_iff.mpr
  intro v
  exact (d₀.trans a₀).symm.continuous.comp (continuous_apply (b₀ v))
omit [SecondCountableTopology H₂] in
lemma continuous_normalizeD (d₀ : H₄ ≃ₗᵢ[ℂ] H₂) : Continuous (normalizeD d₀) := by
  apply continuous_iff.mpr
  intro v
  exact d₀.symm.continuous.comp (continuous_apply v)

omit [SecondCountableTopology H₁] [SecondCountableTopology H₂] [SecondCountableTopology H₃] [SecondCountableTopology H₄] in
lemma normalized_rectangle (a₀ a : H₂ ≃ₗᵢ[ℂ] H₁) (b₀ b : H₄ ≃ₗᵢ[ℂ] H₃)
    (c : H₃ ≃ₗᵢ[ℂ] H₁) (d₀ d : H₄ ≃ₗᵢ[ℂ] H₂)
    (hr : d.trans a = b.trans c) :
    normalizeA a₀ d₀ a * normalizeD d₀ d = normalizeC a₀ b₀ d₀ c * normalizeB b₀ b := by
  ext v
  have hh := congrArg (fun L : H₄ ≃ₗᵢ[ℂ] H₁ => L v) hr
  simpa [normalizeA, normalizeB, normalizeC, normalizeD] using congrArg (d₀.trans a₀).symm hh

omit [SecondCountableTopology H₁] [SecondCountableTopology H₂] [SecondCountableTopology H₃] [SecondCountableTopology H₄] in
lemma normalized_reference (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (b₀ : H₄ ≃ₗᵢ[ℂ] H₃)
    (c₀ : H₃ ≃ₗᵢ[ℂ] H₁) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂)
    (hr : d₀.trans a₀ = b₀.trans c₀) :
    normalizeA a₀ d₀ a₀ = 1 ∧ normalizeB b₀ b₀ = 1 ∧
    normalizeC a₀ b₀ d₀ c₀ = 1 ∧ normalizeD d₀ d₀ = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext v; simp [normalizeA]
  · ext v; simp [normalizeB]
  · ext v
    change (d₀.trans a₀).symm ((b₀.trans c₀) v) = v
    rw [← hr]
    exact (d₀.trans a₀).symm_apply_apply v
  · ext v; simp [normalizeD]

end StrongUnitary

section
open MeasureTheory ProbabilityTheory
variable {Z X Y A B : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace A] [MeasurableSpace B]
  {f : X → A} {g : Y → B}
lemma map_pair_fst (μ : Measure (X × Y)) (hf : Measurable f) (hg : Measurable g) :
    (μ.map (Prod.map f g)).map Prod.fst = (μ.map Prod.fst).map f := by
  rw [Measure.map_map measurable_fst (hf.prodMap hg), Measure.map_map hf measurable_fst]
  rfl
lemma map_pair_snd (μ : Measure (X × Y)) (hf : Measurable f) (hg : Measurable g) :
    (μ.map (Prod.map f g)).map Prod.snd = (μ.map Prod.snd).map g := by
  rw [Measure.map_map measurable_snd (hf.prodMap hg), Measure.map_map hg measurable_snd]
  rfl
lemma kernel_map_pair_fst (κ : Kernel Z (X × Y)) (z : Z) (hf : Measurable f) (hg : Measurable g) :
    ((κ.map (Prod.map f g)) z).map Prod.fst = ((κ z).map Prod.fst).map f := by
  rw [Kernel.map_apply κ (hf.prodMap hg), map_pair_fst _ hf hg]
lemma kernel_map_pair_snd (κ : Kernel Z (X × Y)) (z : Z) (hf : Measurable f) (hg : Measurable g) :
    ((κ.map (Prod.map f g)) z).map Prod.snd = ((κ z).map Prod.snd).map g := by
  rw [Kernel.map_apply κ (hf.prodMap hg), map_pair_snd _ hf hg]

lemma kernel_map_pair_comp (σ : Measure Z) (κ : Kernel Z (X × Y)) (ν : Measure X) (ρ : Measure Y)
    [SFinite σ] [IsSFiniteKernel κ] [SFinite ν] [SFinite ρ]
    (hf : Measurable f) (hg : Measurable g) (hκ : κ ∘ₘ σ = ν.prod ρ) :
    (κ.map (Prod.map f g)) ∘ₘ σ = (ν.map f).prod (ρ.map g) := by
  rw [← Measure.map_comp _ _ (hf.prodMap hg), hκ, ← Measure.map_prod_map _ _ hf hg]

end

namespace StrongUnitary
open MeasureTheory ProbabilityTheory
open scoped Topology
variable {Z H₁ H₂ H₃ H₄ : Type*} [MeasurableSpace Z]
  [NormedAddCommGroup H₁] [NormedSpace ℂ H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [NormedSpace ℂ H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [NormedSpace ℂ H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [NormedSpace ℂ H₄] [SecondCountableTopology H₄]

lemma mapped_normalized_rectangle
    (μ : Measure ((H₂ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₃)))
    (ν : Measure ((H₃ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₂))) [SFinite μ] [SFinite ν]
    (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (b₀ : H₄ ≃ₗᵢ[ℂ] H₃) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂)
    (hr : ∀ᵐ p ∂μ.prod ν, p.2.2.trans p.1.1 = p.1.2.trans p.2.1) :
    ∀ᵐ p ∂(μ.map (Prod.map (normalizeA a₀ d₀) (normalizeB b₀))).prod
      (ν.map (Prod.map (normalizeC a₀ b₀ d₀) (normalizeD d₀))),
      p.1.1 * p.2.2 = p.2.1 * p.1.2 := by
  let fm := (continuous_normalizeA a₀ d₀).prodMap (continuous_normalizeB b₀)
  let gm := (continuous_normalizeC a₀ b₀ d₀).prodMap (continuous_normalizeD d₀)
  rw [Measure.map_prod_map _ _ fm.measurable gm.measurable]
  apply (ae_map_iff (fm.prodMap gm).measurable.aemeasurable
    (isClosed_eq (continuous_fst.fst.mul continuous_snd.snd)
      (continuous_snd.fst.mul continuous_fst.snd)).measurableSet).mpr
  exact hr.mono fun p hp => normalized_rectangle a₀ p.1.1 b₀ p.1.2 p.2.1 d₀ p.2.2 hp

omit [SecondCountableTopology H₁] in
lemma normalized_supports
    (μ : Measure ((H₂ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₃)))
    (ν : Measure ((H₃ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₂)))
    (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (b₀ : H₄ ≃ₗᵢ[ℂ] H₃)
    (c₀ : H₃ ≃ₗᵢ[ℂ] H₁) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂)
    (hab : (a₀,b₀) ∈ μ.support) (hcd : (c₀,d₀) ∈ ν.support)
    (hr : d₀.trans a₀ = b₀.trans c₀) :
    (1,1) ∈ (μ.map (Prod.map (normalizeA a₀ d₀) (normalizeB b₀))).support ∧
    (1,1) ∈ (ν.map (Prod.map (normalizeC a₀ b₀ d₀) (normalizeD d₀))).support := by
  have hh := normalized_reference a₀ b₀ c₀ d₀ hr
  constructor
  · have hm := mem_support_map_of_continuous
      ((continuous_normalizeA a₀ d₀).prodMap (continuous_normalizeB b₀)) hab
    simpa only [Prod.map_apply, hh.1, hh.2.1] using hm
  · have hm := mem_support_map_of_continuous
      ((continuous_normalizeC a₀ b₀ d₀).prodMap (continuous_normalizeD d₀)) hcd
    simpa only [Prod.map_apply, hh.2.2.1, hh.2.2.2] using hm


lemma polar_normalization (σ : Measure Z) [IsProbabilityMeasure σ]
    (μ : Kernel Z ((H₂ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₃))) [IsMarkovKernel μ]
    (ν : Kernel Z ((H₃ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₂))) [IsMarkovKernel ν]
    (ρa : ProbabilityMeasure (H₂ ≃ₗᵢ[ℂ] H₁)) (ρb : ProbabilityMeasure (H₄ ≃ₗᵢ[ℂ] H₃))
    (ρc : ProbabilityMeasure (H₃ ≃ₗᵢ[ℂ] H₁)) (ρd : ProbabilityMeasure (H₄ ≃ₗᵢ[ℂ] H₂))
    (h : ∀ᵐ z ∂σ, (μ z).map Prod.fst = ρa ∧ (μ z).map Prod.snd = ρb ∧
      (ν z).map Prod.fst = ρc ∧ (ν z).map Prod.snd = ρd ∧
      ∀ᵐ p ∂(μ z).prod (ν z), p.2.2.trans p.1.1 = p.1.2.trans p.2.1)
    (hμ : μ ∘ₘ σ = (ρa : Measure _).prod ρb)
    (hν : ν ∘ₘ σ = (ρc : Measure _).prod ρd) :
    ∃ (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (b₀ : H₄ ≃ₗᵢ[ℂ] H₃) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂)
      (G : Subgroup (H₄ ≃ₗᵢ[ℂ] H₄)),
      IsClosed (G : Set (H₄ ≃ₗᵢ[ℂ] H₄)) ∧
      (ρa : Measure _).map (normalizeA a₀ d₀) = (ρb : Measure _).map (normalizeB b₀) ∧
      (ρc : Measure _).map (normalizeC a₀ b₀ d₀) = (ρd : Measure _).map (normalizeD d₀) ∧
      ((ρa : Measure _).map (normalizeA a₀ d₀)).support = G ∧
      ((ρc : Measure _).map (normalizeC a₀ b₀ d₀)).support = G ∧
      (∀ u ∈ G, ∀ v ∈ G, u * v = v * u) ∧
      (∀ u ∈ G, ((ρa : Measure _).map (normalizeA a₀ d₀)).map (u * ·) =
        (ρa : Measure _).map (normalizeA a₀ d₀)) := by
  obtain ⟨z₀,hz₀⟩ := h.exists
  obtain ⟨a₀,b₀,c₀,d₀,hab,hcd,hr⟩ := support_rectangle (μ z₀) (ν z₀) hz₀.2.2.2.2
  let fa := normalizeA a₀ d₀
  let fb := normalizeB b₀
  let fc := normalizeC a₀ b₀ d₀
  let fd := normalizeD d₀
  have hfa : Measurable fa := (continuous_normalizeA a₀ d₀).measurable
  have hfb : Measurable fb := (continuous_normalizeB b₀).measurable
  have hfc : Measurable fc := (continuous_normalizeC a₀ b₀ d₀).measurable
  have hfd : Measurable fd := (continuous_normalizeD d₀).measurable
  let κ := μ.map (Prod.map fa fb)
  let ξ := ν.map (Prod.map fc fd)
  let ρ : ProbabilityMeasure (H₄ ≃ₗᵢ[ℂ] H₄) := ρa.map hfa.aemeasurable
  let τ : ProbabilityMeasure (H₄ ≃ₗᵢ[ℂ] H₄) := ρc.map hfc.aemeasurable
  have hf : ∀ᵐ z ∂σ, (κ z).map Prod.fst = ρ ∧ (κ z).map Prod.snd = (ρb : Measure _).map fb ∧
      (ξ z).map Prod.fst = τ ∧ (ξ z).map Prod.snd = (ρd : Measure _).map fd := by
    filter_upwards [h] with z hz
    simp only [κ, ξ, kernel_map_pair_fst _ _ hfa hfb, kernel_map_pair_snd _ _ hfa hfb,
      kernel_map_pair_fst _ _ hfc hfd, kernel_map_pair_snd _ _ hfc hfd,
      hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1]
    exact ⟨rfl,trivial,rfl,trivial⟩
  have hrect : ∀ᵐ z ∂σ, ∀ᵐ p ∂(κ z).prod (ξ z), p.1.1*p.2.2 = p.2.1*p.1.2 := by
    filter_upwards [h] with z hz
    dsimp [κ, ξ]
    rw [Kernel.map_apply _ (hfa.prodMap hfb), Kernel.map_apply _ (hfc.prodMap hfd)]
    exact mapped_normalized_rectangle (μ z) (ν z) a₀ b₀ d₀ hz.2.2.2.2
  have h₀rect : ∀ᵐ p ∂(κ z₀).prod (ξ z₀), p.1.1*p.2.2 = p.2.1*p.1.2 := by
    dsimp [κ, ξ]
    rw [Kernel.map_apply _ (hfa.prodMap hfb), Kernel.map_apply _ (hfc.prodMap hfd)]
    exact mapped_normalized_rectangle (μ z₀) (ν z₀) a₀ b₀ d₀ hz₀.2.2.2.2
  have h₀support : (1,1) ∈ (κ z₀).support ∧ (1,1) ∈ (ξ z₀).support := by
    dsimp [κ, ξ]
    rw [Kernel.map_apply _ (hfa.prodMap hfb), Kernel.map_apply _ (hfc.prodMap hfd)]
    exact normalized_supports (μ z₀) (ν z₀) a₀ b₀ c₀ d₀ hab hcd hr
  have h₀fa : (κ z₀).map Prod.fst = ρ := by
    rw [kernel_map_pair_fst _ _ hfa hfb, hz₀.1]; rfl
  have h₀fb : (κ z₀).map Prod.snd = (ρb : Measure _).map fb := by
    rw [kernel_map_pair_snd _ _ hfa hfb, hz₀.2.1]
  have h₀fc : (ξ z₀).map Prod.fst = τ := by
    rw [kernel_map_pair_fst _ _ hfc hfd, hz₀.2.2.1]; rfl
  have h₀fd : (ξ z₀).map Prod.snd = (ρd : Measure _).map fd := by
    rw [kernel_map_pair_snd _ _ hfc hfd, hz₀.2.2.2.1]
  have hn := normalized_rectangle_support (κ z₀) (ξ z₀) h₀support.1 h₀support.2 h₀rect
  have heρ : (ρ : Measure _) = (ρb : Measure _).map fb := h₀fa.symm.trans (hn.1.trans h₀fb)
  have heτ : (τ : Measure _) = (ρd : Measure _).map fd := h₀fc.symm.trans (hn.2.1.trans h₀fd)
  have hκ : κ ∘ₘ σ = (ρ : Measure _).prod ρ := by
    rw [kernel_map_pair_comp σ μ _ _ hfa hfb hμ, ←heρ]; rfl
  have hξ : ξ ∘ₘ σ = (τ : Measure _).prod τ := by
    rw [kernel_map_pair_comp σ ν _ _ hfc hfd hν, ←heτ]; rfl
  obtain ⟨G,hG,hρ,hτ,hcomm,hinv⟩ := normalized_polar_group_from_kernels σ κ ξ ρ τ
    (by filter_upwards [hf,hrect] with z hz hrz
        exact ⟨hz.1, hz.2.1.trans heρ.symm, hz.2.2.1, hz.2.2.2.trans heτ.symm, hrz⟩)
    hκ hξ z₀ ⟨h₀fa,h₀fc,h₀support.1,h₀support.2,h₀rect⟩
  exact ⟨a₀,b₀,d₀,G,hG,heρ,heτ,hρ,hτ,hcomm,hinv⟩
end StrongUnitary

namespace ConditionalFibres
open MeasureTheory ProbabilityTheory
variable {Ω Z V : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace V]
  {μ : Measure Ω} [SFinite μ] {z : Ω → Z} {v : Ω → V}
  {κ : Kernel Z V} [IsSFiniteKernel κ]
lemma law_comp (h : HasCondDistrib v z κ μ) : κ ∘ₘ μ.map z = μ.map v := by
  rw [← Measure.snd_compProd, ← h.map_eq, Measure.snd_map_prodMk₀ h.aemeasurable_fst]

lemma ae_kernel (h : HasCondDistrib v z κ μ) {p : V → Prop}
    (hp : MeasurableSet {v | p v}) (hv : ∀ᵐ ω ∂μ, p (v ω)) :
    ∀ᵐ a ∂μ.map z, ∀ᵐ b ∂κ a, p b := by
  apply Measure.ae_ae_of_ae_compProd (p := fun q => p q.2)
  rw [←h.map_eq]
  exact (ae_map_iff h.aemeasurable (hp.preimage measurable_snd)).mpr hv
end ConditionalFibres

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
variable {Ω Z X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [NormedSpace ℂ H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [NormedSpace ℂ H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [NormedSpace ℂ H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [NormedSpace ℂ H₄] [SecondCountableTopology H₄]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (μX : Measure X) (μY : Measure Y) (μC : Measure C) (μD : Measure D)
  [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
  [IsProbabilityMeasure μC] [IsProbabilityMeasure μD]
  {z : Ω → Z} {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  (κ : Kernel Z (X × Y)) (ξ : Kernel Z (C × D)) [IsMarkovKernel κ] [IsMarkovKernel ξ]
  (a : X → H₂ ≃ₗᵢ[ℂ] H₁) (b : Y → H₄ ≃ₗᵢ[ℂ] H₃)
  (p : C → H₃ ≃ₗᵢ[ℂ] H₁) (q : D → H₄ ≃ₗᵢ[ℂ] H₂)

lemma polar_pair_laws (ha : Measurable a) (hb : Measurable b)
    (hp : Measurable p) (hq : Measurable q)
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) z κ μ)
    (hξ : HasCondDistrib (fun ω => (c ω,d ω)) z ξ μ)
    (hpair : HasCondDistrib (fun ω => ((x ω,y ω),(c ω,d ω))) z (κ ×ₖ ξ) μ)
    (hκm : ∀ᵐ v ∂μ.map z, (κ v).map Prod.fst = μX ∧ (κ v).map Prod.snd = μY)
    (hξm : ∀ᵐ v ∂μ.map z, (ξ v).map Prod.fst = μC ∧ (ξ v).map Prod.snd = μD)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (μX.prod μY))
    (hcd : MeasurePreserving (fun ω => (c ω,d ω)) μ (μC.prod μD))
    (hr : ∀ᵐ ω ∂μ, (q (d ω)).trans (a (x ω)) = (b (y ω)).trans (p (c ω))) :
    let α := κ.map (Prod.map a b)
    let β := ξ.map (Prod.map p q)
    (∀ᵐ v ∂μ.map z, (α v).map Prod.fst = μX.map a ∧ (α v).map Prod.snd = μY.map b ∧
      (β v).map Prod.fst = μC.map p ∧ (β v).map Prod.snd = μD.map q ∧
      ∀ᵐ w ∂(α v).prod (β v), w.2.2.trans w.1.1 = w.1.2.trans w.2.1) ∧
    α ∘ₘ μ.map z = (μX.map a).prod (μY.map b) ∧
    β ∘ₘ μ.map z = (μC.map p).prod (μD.map q) := by
  let R : ((H₂ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₃)) ×
      ((H₃ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₂)) → Prop :=
    fun w => w.2.2.trans w.1.1 = w.1.2.trans w.2.1
  have hmR : MeasurableSet {w | R w} :=
    (isClosed_eq (StrongUnitary.continuous_trans.comp (continuous_snd.snd.prodMk continuous_fst.fst))
      (StrongUnitary.continuous_trans.comp (continuous_fst.snd.prodMk continuous_snd.fst))).measurableSet
  have hr' := ConditionalFibres.ae_kernel hpair (hmR.preimage ((ha.prodMap hb).prodMap (hp.prodMap hq))) hr
  refine ⟨?_, kernel_map_pair_comp _ _ _ _ ha hb ((ConditionalFibres.law_comp hκ).trans hxy.map_eq),
    kernel_map_pair_comp _ _ _ _ hp hq ((ConditionalFibres.law_comp hξ).trans hcd.map_eq)⟩
  filter_upwards [hκm,hξm,hr'] with v hm hn hv
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [kernel_map_pair_fst _ _ ha hb,hm.1]
  · rw [kernel_map_pair_snd _ _ ha hb,hm.2]
  · rw [kernel_map_pair_fst _ _ hp hq,hn.1]
  · rw [kernel_map_pair_snd _ _ hp hq,hn.2]
  · rw [Kernel.map_apply _ (ha.prodMap hb),Kernel.map_apply _ (hp.prodMap hq),
      Measure.map_prod_map _ _ (ha.prodMap hb) (hp.prodMap hq)]
    apply (ae_map_iff ((ha.prodMap hb).prodMap (hp.prodMap hq)).aemeasurable hmR).mpr
    simpa only [Kernel.prod_apply] using hv
end

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
variable {Ω Z X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄] [SecondCountableTopology H₄]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {μX : Measure X} {μY : Measure Y} {μC : Measure C} {μD : Measure D}
  [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
  [IsProbabilityMeasure μC] [IsProbabilityMeasure μD]
  {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  {F : X → H₂ →L[ℂ] H₁} {G : Y → H₄ →L[ℂ] H₃}
  {K : C → H₃ →L[ℂ] H₁} {N : D → H₄ →L[ℂ] H₂}

lemma MeasurablePolarRectangle.haar_normalization
    (R : MeasurablePolarRectangle μ μX μY μC μD F G K N x y c d)
    {z : Ω → Z} (hz : Measurable z)
    (κ : Kernel Z (X × Y)) (ξ : Kernel Z (C × D)) [IsMarkovKernel κ] [IsMarkovKernel ξ]
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) z κ μ)
    (hξ : HasCondDistrib (fun ω => (c ω,d ω)) z ξ μ)
    (hpair : HasCondDistrib (fun ω => ((x ω,y ω),(c ω,d ω))) z (κ ×ₖ ξ) μ)
    (hκm : ∀ᵐ v ∂μ.map z, (κ v).map Prod.fst = μX ∧ (κ v).map Prod.snd = μY)
    (hξm : ∀ᵐ v ∂μ.map z, (ξ v).map Prod.fst = μC ∧ (ξ v).map Prod.snd = μD)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (μX.prod μY))
    (hcd : MeasurePreserving (fun ω => (c ω,d ω)) μ (μC.prod μD)) : R.HasHaarNormalization := by
  have : IsProbabilityMeasure (μ.map z) := (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hz.aemeasurable
  obtain ⟨h,hμ,hν⟩ := polar_pair_laws μX μY μC μD κ ξ
    R.a.unitary R.b.unitary R.p.unitary R.q.unitary R.a.measurable R.b.measurable
    R.p.measurable R.q.measurable hκ hξ hpair hκm hξm hxy hcd R.rectangle
  have := Kernel.IsMarkovKernel.map κ (R.a.measurable.prodMap R.b.measurable)
  have := Kernel.IsMarkovKernel.map ξ (R.p.measurable.prodMap R.q.measurable)
  exact StrongUnitary.polar_normalization (μ.map z)
    (κ.map (Prod.map R.a.unitary R.b.unitary)) (ξ.map (Prod.map R.p.unitary R.q.unitary))
    ⟨μX.map R.a.unitary,(fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) R.a.measurable.aemeasurable⟩
    ⟨μY.map R.b.unitary,(fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) R.b.measurable.aemeasurable⟩
    ⟨μC.map R.p.unitary,(fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) R.p.measurable.aemeasurable⟩
    ⟨μD.map R.q.unitary,(fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) R.q.measurable.aemeasurable⟩ h hμ hν
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal
local instance instFactNeENNRealOfNatTop_4 : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem grouped_haar_normalization (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ R : GroupedPolarData M rows cols n e, R.HasHaarNormalization := by
  filter_upwards [pairPair_fixed_conditional M hM rows.P rows.A rows.B cols.P cols.A cols.B
      rows.cardP cols.properP n,
    columnPair_fixed_conditional M hM rows.P rows.A rows.B cols.P rows.cardP cols.properP n,
    rowPair_fixed_conditional M rows.P cols.P cols.A cols.B n,
    columnPair_fixed_marginals M hM rows.P rows.A rows.B cols.P rows.cardP cols.properP
      rows.properA rows.properB rows.disjointPA rows.disjointPB rows.properPA rows.properPB n,
    rowPair_fixed_marginals M hM rows.P cols.P cols.A cols.B rows.properP
      cols.disjointPA cols.disjointPB cols.properPA cols.properPB n,
    cells_fibre_marginal M hM rows.A cols.P rows.properA n,
    cells_fibre_marginal M hM rows.B cols.P rows.properB n,
    cells_fibre_marginal M hM rows.P cols.A rows.properP n,
    cells_fibre_marginal M hM rows.P cols.B rows.properP n,
    cells_indep_rows_fibre M hM rows.A rows.B cols.P cols.P rows.disjointAB rows.properAB n,
    cells_indep_columns_fibre M rows.P rows.P cols.A cols.B cols.disjointAB cols.properAB n]
      with e hpair hκ hξ hκm hξm hx hy hc hd hxy hcd
  intro R
  apply R.haar_normalization (measurable_cells M rows.P cols.P n)
    ((columnPairKernel M rows.P rows.A rows.B cols.P n).sectR e)
    ((rowPairKernel M rows.P cols.P cols.A cols.B n).sectR e) hκ hξ hpair
  · exact hκm.mono fun _ h => ⟨h.1.map_eq,h.2.map_eq⟩
  · exact hξm.mono fun _ h => ⟨h.1.map_eq,h.2.map_eq⟩
  · refine ⟨hx.measurable.prodMk hy.measurable, ?_⟩
    rw [←hx.map_eq,←hy.map_eq]
    exact hxy.map_prod_eq_prod_map_map hx.measurable.aemeasurable hy.measurable.aemeasurable
  · refine ⟨hc.measurable.prodMk hd.measurable, ?_⟩
    rw [←hc.map_eq,←hd.map_eq]
    exact hcd.map_prod_eq_prod_map_map hc.measurable.aemeasurable hd.measurable.aemeasurable
end ArrayObjects.Object.Rolled

namespace JoiningOperator
open MeasureTheory ContinuousLinearMap
variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {τ : Measure Z}
  {x : Ω → X} {y : Ω → Y} {z : Ω → Z}

lemma active_observation_eq (hx : MeasurePreserving x μ ν)
    (hy : MeasurePreserving y μ ρ) (hz : MeasurePreserving z μ τ)
    (hobs : MeasurableSpace.comap y inferInstance = MeasurableSpace.comap z inferInstance) :
    (LinearMap.range (operator hx hy).toLinearMap).topologicalClosure =
      (LinearMap.range (operator hx hz).toLinearMap).topologicalClosure := by
  congr 1
  change LinearMap.range ((pull hx).adjoint.toLinearMap.comp (pull hy).toLinearMap) =
    LinearMap.range ((pull hx).adjoint.toLinearMap.comp (pull hz).toLinearMap)
  rw [LinearMap.range_comp, LinearMap.range_comp, pull_range hy, pull_range hz, hobs]

end JoiningOperator

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Tensors
attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunArrαYOfNatNatComplexMemAddSubgroupLpENNRealSubmoduleRawSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunCellComplexMemAddSubgroupLpOfNatENNRealSubmoduleSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatCellSlotLocal _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallCellSlotTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallYRawTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYColumnCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYRowCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.arrayLaw_probability _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.localLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory
open scoped InnerProductSpace
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

omit [SFinite μ] in
lemma coe_tensorLp (g : Lp ℂ 2 μ) (h : Lp ℂ 2 ν) :
    (tensorLp g h : X × Y → ℂ) =ᵐ[μ.prod ν] (fun p => g p.1 * h p.2) :=
  MemLp.coeFn_toLp _

end

section
open MeasureTheory
open scoped InnerProductSpace ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

lemma tensorLp_indicator (A : Set X) (hA : MeasurableSet A) (B : Set Y) (hB : MeasurableSet B) :
    tensorLp (indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℂ))
      (indicatorConstLp 2 hB (measure_ne_top ν B) (1 : ℂ)) =
        indicatorConstLp 2 (hA.prod hB) (measure_ne_top (μ.prod ν) _) (1 : ℂ) := by
  apply Lp.ext
  have hf : Measure.QuasiMeasurePreserving Prod.fst (μ.prod ν) μ :=
    Measure.quasiMeasurePreserving_fst
  have hs : Measure.QuasiMeasurePreserving Prod.snd (μ.prod ν) ν :=
    Measure.quasiMeasurePreserving_snd
  filter_upwards [coe_tensorLp (indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℂ))
    (indicatorConstLp 2 hB (measure_ne_top ν B) (1 : ℂ)),
    hf.ae (indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := measure_ne_top μ A) (c := (1 : ℂ))),
    hs.ae (indicatorConstLp_coeFn (p := 2) (hs := hB) (hμs := measure_ne_top ν B) (c := (1 : ℂ))),
    indicatorConstLp_coeFn (p := 2) (hs := hA.prod hB) (hμs := measure_ne_top (μ.prod ν) _) (c := (1 : ℂ))]
    with p ht hp hq hr
  rw [ht, hp, hq, hr]
  by_cases ha : p.1 ∈ A <;> by_cases hb : p.2 ∈ B <;> simp [ha, hb]

lemma dense_tensorLp :
    (Submodule.span ℂ (Set.range (fun p : Lp ℂ 2 μ × Lp ℂ 2 ν => tensorLp p.1 p.2))).topologicalClosure = ⊤ := by
  let S := Submodule.span ℂ (Set.range (fun p : Lp ℂ 2 μ × Lp ℂ 2 ν => tensorLp p.1 p.2))
  have hS : Sᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro f hf
    change f = 0
    apply Lp.ext
    apply (JoiningOperator.ae_eq_zero_of_rectangles
      ((Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) ?_).trans
      (Lp.coeFn_zero _ _ _).symm
    intro A B hA hB
    rw [← L2.inner_indicatorConstLp_one (hA.prod hB) (measure_ne_top _ _), ← tensorLp_indicator A hA B hB]
    exact S.inner_right_of_mem_orthogonal
      (Submodule.subset_span ⟨(_, _), rfl⟩) hf
  rw [← Submodule.orthogonal_orthogonal_eq_closure, hS, Submodule.bot_orthogonal_eq_top]

end

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
variable {X Y H : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma closure_tensor_image (A : Lp ℂ 2 (μ.prod ν) →L[ℂ] H) :
    (Submodule.span ℂ (Set.range (fun p : Lp ℂ 2 μ × Lp ℂ 2 ν => A (tensorLp p.1 p.2)))).topologicalClosure =
      (LinearMap.range A.toLinearMap).topologicalClosure := by
  let S := (Submodule.span ℂ (Set.range (fun p : Lp ℂ 2 μ × Lp ℂ 2 ν => A (tensorLp p.1 p.2)))).topologicalClosure
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro z ⟨⟨g,h⟩, rfl⟩
      exact (Submodule.le_topologicalClosure _) ⟨tensorLp g h, rfl⟩
    · exact Submodule.isClosed_topologicalClosure _
  · apply Submodule.topologicalClosure_minimal
    · rintro z ⟨v,rfl⟩
      have hclosed : IsClosed (S.comap A.toLinearMap : Set (Lp ℂ 2 (μ.prod ν))) :=
        (Submodule.isClosed_topologicalClosure _).preimage A.continuous
      have ht : (⊤ : Submodule ℂ (Lp ℂ 2 (μ.prod ν))) ≤ S.comap A.toLinearMap := by
        rw [← dense_tensorLp]
        apply Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) hclosed
        rintro z ⟨⟨g,h⟩,rfl⟩
        exact (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨(g,h),rfl⟩)
      exact ht (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ (Lp ℂ 2 (μ.prod ν))))
    · exact Submodule.isClosed_topologicalClosure _

omit [CompleteSpace H] in

lemma restricted_contractions_span (A : Lp ℂ 2 (μ.prod ν) →L[ℂ] H)
    (D : Submodule ℂ H) [D.HasOrthogonalProjection]
    (P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (Q : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hA : D ≤ (LinearMap.range A.toLinearMap).topologicalClosure)
    (hPQ : ∀ g h, D.starProjection (A (tensorLp g h)) = A (tensorLp (P g) (Q h))) :
    (Submodule.span ℂ (Set.range (fun p : Lp ℂ 2 μ × Lp ℂ 2 ν => A (tensorLp (P p.1) (Q p.2))))).topologicalClosure = D := by
  let S := (Submodule.span ℂ (Set.range (fun p : Lp ℂ 2 μ × Lp ℂ 2 ν => A (tensorLp (P p.1) (Q p.2))))).topologicalClosure
  have hDS : ∀ v ∈ (LinearMap.range A.toLinearMap).topologicalClosure,
      D.starProjection v ∈ S := by
    intro v hv
    have hclosed : IsClosed (S.comap D.starProjection.toLinearMap : Set H) :=
      (Submodule.isClosed_topologicalClosure _).preimage D.starProjection.continuous
    have hh : (LinearMap.range A.toLinearMap).topologicalClosure ≤ S.comap D.starProjection.toLinearMap := by
      rw [← closure_tensor_image A]
      apply Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) hclosed
      rintro z ⟨⟨g,h⟩,rfl⟩
      change D.starProjection (A (tensorLp g h)) ∈ S
      rw [hPQ]
      exact (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨(g,h),rfl⟩)
    exact hh hv
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro z ⟨⟨g,h⟩,rfl⟩
      change A (tensorLp (P g) (Q h)) ∈ D
      rw [← hPQ]
      exact D.starProjection_apply_mem _
    · exact D.isTopCompl_orthogonal.isClosed
  · intro v hv
    have hh := hDS v (hA hv)
    rwa [D.starProjection_eq_self_iff.mpr hv] at hh

end

namespace JoiningOperator
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal
variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Ω}
  {η : Measure U} {ν : Measure X} {ρ : Measure Y}
  {u : Ω → U} {x : Ω → X} {y : Ω → Y}

lemma active_eq_essentialRange_product [IsProbabilityMeasure μ]
    [SecondCountableTopology (Lp ℂ 2 ρ)]
    {κ : Kernel U (X × Y)} [IsMarkovKernel κ]
    (hu : MeasurePreserving u μ η) (hx : MeasurePreserving x μ ν)
    (hy : MeasurePreserving y μ ρ)
    (huy : MeasurePreserving (fun ω => (u ω,y ω)) μ (η.prod ρ))
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) u κ μ)
    (hm : ∀ᵐ a ∂η, MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ) :
    (LinearMap.range (operator hx huy).toLinearMap).topologicalClosure =
      essentialRange η (family κ ν ρ) := by
  have h := active_eq_essentialRange hu.measurable hx hy hκ (by simpa only [hu.map_eq] using hm)
  calc
    _ = (LinearMap.range (operator hx ⟨hu.measurable.prodMk hy.measurable,rfl⟩).toLinearMap).topologicalClosure :=
      active_observation_eq hx huy ⟨hu.measurable.prodMk hy.measurable,rfl⟩ rfl
    _ = _ := by simpa only [hu.map_eq] using h
end JoiningOperator

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal

local instance instFactNeENNRealOfNatTop_9 : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma rowActive_eq_range (hM : M.IsSaturated) (A : Finset I) (hA : A ≠ Finset.univ)
    (cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ (hr : MeasurePreserving (cells M A cols.P n) (M.ownKernel (n+2) e) (cellLaw M A cols.P n e))
      (hst : MeasurePreserving (fun y => (cells M A cols.A n y,cells M A cols.B n y))
        (M.ownKernel (n+2) e) ((cellLaw M A cols.A n e).prod (cellLaw M A cols.B n e))),
      rowActive M A cols.P cols.A cols.B n e =
        (LinearMap.range (JoiningOperator.operator hr hst).toLinearMap).topologicalClosure := by
  filter_upwards [cells_fibre_marginal M hM A cols.A hA n,
    cells_fibre_marginal M hM A cols.B hA n,
    rowPair_fixed_conditional M A cols.A cols.P cols.B n,
    rowPair_fixed_marginals M hM A cols.A cols.P cols.B hA
      cols.disjointPA.symm cols.disjointAB (by simpa [Finset.union_comm] using cols.properPA)
      cols.properAB n] with e hs ht hκ hm
  intro hr hst
  rw [hs.map_eq] at hm
  unfold rowActive
  rw [fibreRowEdge_eq]
  exact (JoiningOperator.active_eq_essentialRange_product hs hr ht hst hκ hm).symm

lemma columnActive_eq_range (hM : M.IsSaturated) (rows : TriplePartition I)
    (R : Finset I) (hR : R ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ (hr : MeasurePreserving (cells M rows.P R n) (M.ownKernel (n+2) e) (cellLaw M rows.P R n e))
      (hst : MeasurePreserving (fun y => (cells M rows.A R n y,cells M rows.B R n y))
        (M.ownKernel (n+2) e) ((cellLaw M rows.A R n e).prod (cellLaw M rows.B R n e))),
      columnActive M rows.P rows.A rows.B R n e =
        (LinearMap.range (JoiningOperator.operator hr hst).toLinearMap).topologicalClosure := by
  filter_upwards [cells_fibre_marginal M hM rows.A R rows.properA n,
    cells_fibre_marginal M hM rows.B R rows.properB n,
    columnPair_fixed_conditional M hM rows.A rows.P rows.B R rows.swapPA.cardP hR n,
    columnPair_fixed_marginals M hM rows.A rows.P rows.B R rows.swapPA.cardP hR
      rows.properP rows.properB rows.disjointPA.symm rows.disjointAB
      (by simpa [Finset.union_comm] using rows.properPA) rows.properAB n] with e hs ht hκ hm
  intro hr hst
  rw [hs.map_eq] at hm
  unfold columnActive
  rw [fibreColumnEdge_eq]
  exact (JoiningOperator.active_eq_essentialRange_product hs hr ht hst hκ hm).symm

end ArrayObjects.Object.Rolled

namespace JoiningOperator

open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal


variable {Ω Z X Y A B C : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {η : Measure Z}
  {α : Measure A} {β : Measure B} {τ : Measure C}
  {x : Ω → X} {y : Ω → Y} {z : Ω → Z} {a : X → A} {b : Y → B} {c : Z → C}
  [SFinite ν] [SFinite ρ]

lemma tensor_pull [SFinite β] (ha : MeasurePreserving a ν α) (hb : MeasurePreserving b ρ β)
    (g : Lp ℂ 2 α) (h : Lp ℂ 2 β) :
    tensorLp (pull ha g) (pull hb h) = pull (ha.prod hb) (tensorLp g h) := by
  apply Lp.ext
  filter_upwards [coe_tensorLp (pull ha g) (pull hb h),
    (ha.prod hb).quasiMeasurePreserving.ae (coe_tensorLp g h),
    Lp.coeFn_compMeasurePreserving (tensorLp g h) (ha.prod hb),
    Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_compMeasurePreserving g ha),
    Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_compMeasurePreserving h hb)] with p hp ht hpull hga hhb
  exact hp.trans ((congrArg₂ (· * ·) hga hhb).trans (ht.symm.trans hpull.symm))

lemma contraction_pull [SFinite β] (hz : MeasurePreserving z μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ))
    (ha : MeasurePreserving a ν α) (hb : MeasurePreserving b ρ β)
    (g : Lp ℂ 2 α) (h : Lp ℂ 2 β) :
    contraction hz hxy (pull ha g) (pull hb h) =
      operator hz ((ha.prod hb).comp hxy) (tensorLp g h) := by
  unfold contraction operator
  rw [tensor_pull ha hb, pull_comp hxy (ha.prod hb)]
  rfl

lemma contraction_mem_screen
    [IsProbabilityMeasure μ] [StandardBorelSpace A] [Nonempty A]
    [StandardBorelSpace B] [Nonempty B]
    (hz : MeasurePreserving z μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ))
    (ha : MeasurePreserving a ν α) (hb : MeasurePreserving b ρ β)
    (hc : MeasurePreserving c η τ)
    {κ : Kernel C (A × B)} [IsMarkovKernel κ]
    (hκ : HasCondDistrib (fun ω => (a (x ω),b (y ω))) z (κ.comap c hc.measurable) μ)
    (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ)
    (hg : g ∈ lpMeas ℂ ℂ (MeasurableSpace.comap a inferInstance) 2 ν)
    (hh : h ∈ lpMeas ℂ ℂ (MeasurableSpace.comap b inferInstance) 2 ρ) :
    contraction hz hxy g h ∈ lpMeas ℂ ℂ (MeasurableSpace.comap c inferInstance) 2 η := by
  have : SFinite β := hb.map_eq ▸ inferInstanceAs (SFinite (ρ.map b))
  rw [←pull_range ha] at hg
  rw [←pull_range hb] at hh
  obtain ⟨g,rfl⟩ := hg
  obtain ⟨h,rfl⟩ := hh
  change contraction hz hxy (pull ha g) (pull hb h) ∈ _
  rw [contraction_pull hz hxy ha hb g h, screened_operator hz ((ha.prod hb).comp hxy) hc hκ]
  rw [←pull_range hc]
  exact ⟨operator (hc.comp hz) ((ha.prod hb).comp hxy) (tensorLp g h),rfl⟩

end JoiningOperator

section
open MeasureTheory ProbabilityTheory
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]

lemma measure_eq_graph_of_ratio (μ : Measure (G × G)) (ρ : Measure G) (a : G)
    (hρ : μ.map Prod.snd = ρ) (hr : ∀ᵐ p ∂μ, p.1 * p.2⁻¹ = a) :
    μ = ρ.map (fun b => (a*b,b)) := by
  have hg : Measurable (fun b : G => (a*b,b)) :=
    (measurable_const.mul measurable_id).prodMk measurable_id
  rw [←hρ, Measure.map_map hg measurable_snd]
  calc
    μ = μ.map id := (Measure.map_id).symm
    _ = μ.map ((fun b => (a*b,b)) ∘ Prod.snd) := by
      apply Measure.map_congr
      filter_upwards [hr] with p hp
      apply Prod.ext
      · change p.1 = a*p.2
        rw [←hp, mul_assoc, inv_mul_cancel, mul_one]
      · rfl

lemma ratioKernel_apply (ρ : Measure G) [SFinite ρ] (a : G) :
    ratioKernel ρ a = ρ.map (fun b => (a*b,b)) := by
  have hm : Measurable (fun p : G × G => (p.1*p.2,p.2)) :=
    (measurable_fst.mul measurable_snd).prodMk measurable_snd
  rw [ratioKernel, Kernel.map_apply _ hm]
  simp only [Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply]
  rw [Measure.dirac_prod]
  rw [Measure.map_map hm (measurable_prodMk_left (x := a))]
  rfl

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  {μ : Measure Ω} {z : Ω → Z} {v : Ω → G × G}

lemma hasCondDistrib_ratio {κ : Kernel Z (G × G)} [IsMarkovKernel κ]
    (hκ : HasCondDistrib v z κ μ) (ρ : Measure G) [IsProbabilityMeasure ρ]
    (c : Z → G) (hc : Measurable c)
    (hm : ∀ᵐ t ∂μ.map z, (κ t).map Prod.snd = ρ)
    (hr : ∀ᵐ t ∂μ.map z, ∀ᵐ p ∂κ t, p.1*p.2⁻¹ = c t) :
    HasCondDistrib v z ((ratioKernel ρ).comap c hc) μ := by
  refine ⟨hκ.aemeasurable, hκ.map_eq.trans (Measure.compProd_congr ?_)⟩
  filter_upwards [hm,hr] with t ht htr
  change κ t = ratioKernel ρ (c t)
  rw [ratioKernel_apply]
  exact measure_eq_graph_of_ratio (κ t) ρ (c t) ht htr

end

namespace JoiningOperator

open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal

section FactorFields
variable {Ω Z X Y A B C : Type*}
  [MeasurableSpace Ω] [mZ : MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {η : Measure Z}
  {α : Measure A} {β : Measure B} {τ : Measure C}
  {x : Ω → X} {y : Ω → Y} {z : Ω → Z} {a : X → A} {b : Y → B} {c : Z → C}

lemma common_space_le_screen
    [IsProbabilityMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    [StandardBorelSpace A] [Nonempty A] [StandardBorelSpace B] [Nonempty B]
    (hz : MeasurePreserving z μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ))
    (ha : MeasurePreserving a ν α) (hb : MeasurePreserving b ρ β)
    (hc : MeasurePreserving c η τ)
    {κ : Kernel C (A × B)} [IsMarkovKernel κ]
    (hκ : HasCondDistrib (fun ω => (a (x ω),b (y ω))) z (κ.comap c hc.measurable) μ)
    (D : Submodule ℂ (Lp ℂ 2 η)) [D.HasOrthogonalProjection]
    (P : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (Q : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ)
    (hD : D ≤ (LinearMap.range (operator hz hxy).toLinearMap).topologicalClosure)
    (hPQ : ∀ g h, D.starProjection (contraction hz hxy g h) =
      contraction hz hxy (P g) (Q h))
    (hP : ∀ g, P g ∈ lpMeas ℂ ℂ (MeasurableSpace.comap a inferInstance) 2 ν)
    (hQ : ∀ h, Q h ∈ lpMeas ℂ ℂ (MeasurableSpace.comap b inferInstance) 2 ρ) :
    D ≤ lpMeas ℂ ℂ (MeasurableSpace.comap c inferInstance) 2 η := by
  rw [←restricted_contractions_span (operator hz hxy) D P Q hD hPQ]
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,h⟩,rfl⟩
    exact contraction_mem_screen hz hxy ha hb hc hκ (P g) (Q h) (hP g) (hQ h)
  · exact isClosed_aestronglyMeasurable hc.measurable.comap_le

lemma common_space_le_ratio
    {G : Type*} [gG : Group G] [mG : MeasurableSpace G] [hG : MeasurableMul₂ G]
    [StandardBorelSpace G] [Nonempty G]
    [IsProbabilityMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    {a : X → G} {b : Y → G} {c : Z → G}
    (hz : MeasurePreserving z μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ))
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    {κ : Kernel Z (G × G)} [IsMarkovKernel κ]
    (hκ : HasCondDistrib (fun ω => (a (x ω),b (y ω))) z κ μ)
    (σ : Measure G) [IsProbabilityMeasure σ]
    (hm : ∀ᵐ t ∂η, (κ t).map Prod.snd = σ)
    (hr : ∀ᵐ t ∂η, ∀ᵐ p ∂κ t, p.1*p.2⁻¹ = c t)
    (D : Submodule ℂ (Lp ℂ 2 η)) [D.HasOrthogonalProjection]
    (P : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (Q : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ)
    (hD : D ≤ (LinearMap.range (operator hz hxy).toLinearMap).topologicalClosure)
    (hPQ : ∀ g h, D.starProjection (contraction hz hxy g h) =
      contraction hz hxy (P g) (Q h))
    (hP : ∀ g, P g ∈ lpMeas ℂ ℂ (MeasurableSpace.comap a inferInstance) 2 ν)
    (hQ : ∀ h, Q h ∈ lpMeas ℂ ℂ (MeasurableSpace.comap b inferInstance) 2 ρ) :
    D ≤ lpMeas ℂ ℂ (MeasurableSpace.comap c inferInstance) 2 η := by
  have hscreen := hasCondDistrib_ratio hκ σ c hc (by simpa only [hz.map_eq] using hm)
    (by simpa only [hz.map_eq] using hr)
  exact common_space_le_screen hz hxy ⟨ha,rfl⟩ ⟨hb,rfl⟩ ⟨hc,rfl⟩
    hscreen D P Q hD hPQ hP hQ

end FactorFields


end JoiningOperator

section
open MeasureTheory
variable {X G : Type*} [TopologicalSpace X] [CompactSpace X] [Group G]

lemma characterAlgebra_span (χ : G →* C(X,ℂ)) (hs : ∀ g, star (χ g) = χ g⁻¹) :
    (characterAlgebra χ hs).toSubmodule = Submodule.span ℂ (Set.range χ) := by
  change (Algebra.adjoin ℂ (Set.range χ)).toSubmodule = _
  rw [Algebra.adjoin_eq_span]
  rw [←MonoidHom.coe_mrange χ, (MonoidHom.mrange χ).closure_eq]

lemma dense_character_span (χ : G →* C(X,ℂ)) (hs : ∀ g, star (χ g) = χ g⁻¹)
    (hsep : ∀ x y : X, x ≠ y → ∃ g, χ g x ≠ χ g y) :
    (Submodule.span ℂ (Set.range χ)).topologicalClosure = ⊤ := by
  have hA : (characterAlgebra χ hs).SeparatesPoints := by
    intro x y hxy
    obtain ⟨g,hg⟩ := hsep x y hxy
    refine ⟨(χ g : X → ℂ), ⟨χ g, Algebra.subset_adjoin ⟨g,rfl⟩, rfl⟩, hg⟩
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (characterAlgebra χ hs) hA
  have hh := congrArg (fun A : StarSubalgebra ℂ C(X,ℂ) => A.toSubalgebra.toSubmodule) h
  change (characterAlgebra χ hs).toSubmodule.topologicalClosure = ⊤ at hh
  rwa [characterAlgebra_span] at hh

end

section
open MeasureTheory
open scoped ENNReal
variable {I : Type*}

lemma torusWord_star (w : FreeGroup I) : star (torusWord w) = torusWord w⁻¹ := by
  ext x
  change star ((torusWordCircle w x : Circle) : ℂ) = (torusWordCircle w⁻¹ x : ℂ)
  rw [map_inv]
  exact (Circle.coe_inv_eq_conj (torusWordCircle w x)).symm

lemma torusWord_dense :
    (Submodule.span ℂ (Set.range (torusWord (I := I)))).topologicalClosure = ⊤ := by
  apply dense_character_span _ torusWord_star
  intro x y hxy
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
  refine ⟨FreeGroup.of i, ?_⟩
  simpa only [torusWord_of] using (fun h => hi (Subtype.ext h))

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
lemma dense_span_image (A : E →L[ℂ] F) (hA : DenseRange A) (s : Set E)
    (hs : (Submodule.span ℂ s).topologicalClosure = ⊤) :
    (Submodule.span ℂ (A '' s)).topologicalClosure = ⊤ := by
  let P := (Submodule.span ℂ (A '' s)).topologicalClosure
  have hspan : Submodule.span ℂ s ≤ P.comap A.toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨x,hx,rfl⟩)
  have htop : ⊤ ≤ P.comap A.toLinearMap := by
    rw [←hs]
    exact Submodule.topologicalClosure_minimal _ hspan
      ((Submodule.isClosed_topologicalClosure _).preimage A.continuous)
  apply top_unique
  intro x hx
  exact (Submodule.isClosed_topologicalClosure _).closure_subset_iff.mpr
    (Set.range_subset_iff.mpr (fun v => htop (show v ∈ (⊤ : Submodule ℂ E) from trivial)))
    (by rw [hA.closure_range]; trivial : x ∈ closure (Set.range A))

lemma dense_span_continuous_toLp {X J : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    (f : J → C(X,ℂ)) (hf : (Submodule.span ℂ (Set.range f)).topologicalClosure = ⊤) :
    (Submodule.span ℂ (Set.range (fun j => ContinuousMap.toLp 2 μ ℂ (f j)))).topologicalClosure = ⊤ := by
  have hD : DenseRange (ContinuousMap.toLp 2 μ ℂ : C(X,ℂ) →L[ℂ] Lp ℂ 2 μ) :=
    ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num : (2 : ENNReal) ≠ ∞)
  have h := dense_span_image (ContinuousMap.toLp 2 μ ℂ : C(X,ℂ) →L[ℂ] Lp ℂ 2 μ) hD
    (Set.range f) hf
  simpa only [←Set.range_comp, Function.comp_def] using h

attribute [local instance] OAI.Rokhlin.instMeasurableSpaceCircle_solutions_1
attribute [local instance] OAI.Rokhlin.instBorelSpaceCircle_solutions_1
lemma torusWord_L2_dense [Countable I] (μ : Measure (I → Circle)) [IsFiniteMeasure μ] :
    (Submodule.span ℂ (Set.range (fun w => ContinuousMap.toLp 2 μ ℂ (torusWord (I := I) w)))).topologicalClosure = ⊤ := by
  exact dense_span_continuous_toLp μ (torusWord (I := I)) torusWord_dense

end

variable {I : Type*}

lemma torusWordCircle_inv (w : FreeGroup I) (x : I → Circle) :
    torusWordCircle w x⁻¹ = (torusWordCircle w x)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_left
  rw [←torusWordCircle_mul, inv_mul_cancel, torusWordCircle_one]

lemma torusWord_ratio (w : FreeGroup I) (x y : I → Circle) :
    torusWord w (x*y⁻¹) = torusWord w x * star (torusWord w y) := by
  change (torusCharacter w (x*y⁻¹) : ℂ) =
    (torusCharacter w x : ℂ) * star (torusCharacter w y : ℂ)
  rw [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv_eq_conj]
  rfl


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
open MeasureTheory
open scoped ENNReal
variable {E F J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma closure_image_dense_span (A : E →L[ℂ] F) (v : J → E)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    (Submodule.span ℂ (Set.range (fun j => A (v j)))).topologicalClosure =
      (LinearMap.range A.toLinearMap).topologicalClosure := by
  let S := (Submodule.span ℂ (Set.range (fun j => A (v j)))).topologicalClosure
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact Submodule.le_topologicalClosure _ ⟨v j,rfl⟩
    · exact Submodule.isClosed_topologicalClosure _
  · apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x,rfl⟩
      have hc : IsClosed (S.comap A.toLinearMap : Set E) :=
        (Submodule.isClosed_topologicalClosure _).preimage A.continuous
      have hs : Submodule.span ℂ (Set.range v) ≤ S.comap A.toLinearMap := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j,rfl⟩
        exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨j,rfl⟩)
      have hh : ⊤ ≤ S.comap A.toLinearMap := by
        rw [←hv]
        exact Submodule.topologicalClosure_minimal _ hs hc
      exact hh (show x ∈ (⊤ : Submodule ℂ E) from trivial)
    · exact Submodule.isClosed_topologicalClosure _

variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {ν : Measure X} {x : Ω → X}

lemma pullback_dense_span (hx : MeasurePreserving x μ ν) (v : J → Lp ℂ 2 ν)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    (Submodule.span ℂ (Set.range (fun j => JoiningOperator.pull hx (v j)))).topologicalClosure =
      lpMeas ℂ ℂ (MeasurableSpace.comap x inferInstance) 2 μ := by
  rw [closure_image_dense_span _ _ hv, JoiningOperator.pull_range]
  let : Fact (MeasurableSpace.comap x inferInstance ≤ mΩ) := ⟨hx.measurable.comap_le⟩
  exact (isClosed_aestronglyMeasurable hx.measurable.comap_le).submodule_topologicalClosure_eq

attribute [local instance] OAI.Rokhlin.instMeasurableSpaceCircle_solutions_2
attribute [local instance] OAI.Rokhlin.instBorelSpaceCircle_solutions_2
lemma torusWord_pullback_dense {I : Type*} [Countable I] [IsFiniteMeasure μ]
    (γ : Ω → I → Circle) (hγ : Measurable γ) :
    (Submodule.span ℂ (Set.range (fun w => JoiningOperator.pull (MeasurePreserving.mk hγ rfl)
      (ContinuousMap.toLp 2 (μ.map γ) ℂ (torusWord (I := I) w))))).topologicalClosure =
      lpMeas ℂ ℂ (MeasurableSpace.comap γ inferInstance) 2 μ := by
  exact pullback_dense_span (MeasurePreserving.mk hγ rfl) _ (torusWord_L2_dense (μ.map γ))

end

namespace JoiningOperator
open MeasureTheory ProbabilityTheory
open scoped ENNReal

section
variable {Ω Z X Y I : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y] [Countable I]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {η : Measure Z}
  [IsFiniteMeasure ν] [IsFiniteMeasure ρ] [IsFiniteMeasure η]
  {x : Ω → X} {y : Ω → Y} {z : Ω → Z}

attribute [local instance] OAI.Rokhlin.JoiningOperator.instMeasurableSpaceCircle_solutions
attribute [local instance] OAI.Rokhlin.JoiningOperator.instBorelSpaceCircle_solutions
lemma torusWord_contraction
    (hz : MeasurePreserving z μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ))
    (a : X → I → Circle) (b : Y → I → Circle) (c : Z → I → Circle)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (hr : ∀ᵐ ω ∂μ, c (z ω) = a (x ω) * (b (y ω))⁻¹)
    (w : FreeGroup I) :
    pull (MeasurePreserving.mk hc rfl) (ContinuousMap.toLp 2 (η.map c) ℂ (torusWord w)) =
      contraction hz hxy
        (pull (MeasurePreserving.mk ha rfl) (ContinuousMap.toLp 2 (ν.map a) ℂ (torusWord w)))
        (star (pull (MeasurePreserving.mk hb rfl) (ContinuousMap.toLp 2 (ρ.map b) ℂ (torusWord w)))) := by
  let f := ContinuousMap.toLp 2 (η.map c) ℂ (torusWord w)
  let g := ContinuousMap.toLp 2 (ν.map a) ℂ (torusWord w)
  let h := ContinuousMap.toLp 2 (ρ.map b) ℂ (torusWord w)
  let hc' : MeasurePreserving c η (η.map c) := ⟨hc,rfl⟩
  let ha' : MeasurePreserving a ν (ν.map a) := ⟨ha,rfl⟩
  let hb' : MeasurePreserving b ρ (ρ.map b) := ⟨hb,rfl⟩
  have he : pull hz (pull hc' f) = pull hxy (tensorLp (pull ha' g) (star (pull hb' h))) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (pull hc' f) hz,
      hz.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f hc'),
      (hc'.comp hz).quasiMeasurePreserving.ae (ContinuousMap.coeFn_toLp (η.map c) (𝕜 := ℂ) (p := 2) (torusWord w)),
      Lp.coeFn_compMeasurePreserving (tensorLp (pull ha' g) (star (pull hb' h))) hxy,
      hxy.quasiMeasurePreserving.ae (coe_tensorLp (pull ha' g) (star (pull hb' h))),
      hxy.quasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_compMeasurePreserving g ha')),
      hxy.quasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_star (pull hb' h))),
      hxy.quasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_compMeasurePreserving h hb')),
      hxy.quasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst.ae
        (ha'.quasiMeasurePreserving.ae (ContinuousMap.coeFn_toLp (ν.map a) (𝕜 := ℂ) (p := 2) (torusWord w)))),
      hxy.quasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_snd.ae
        (hb'.quasiMeasurePreserving.ae (ContinuousMap.coeFn_toLp (ρ.map b) (𝕜 := ℂ) (p := 2) (torusWord w)))),
      hr] with ω hf1 hf2 hf3 ht1 ht2 hg1 hh1 hh2 hg2 hh3 hrω
    calc
      _ = torusWord w (c (z ω)) := hf1.trans (hf2.trans hf3)
      _ = torusWord w (a (x ω)) * star (torusWord w (b (y ω))) := by rw [hrω,torusWord_ratio]
      _ = (pull ha' g) (x ω) * star ((pull hb' h) (y ω)) := by
        rw [show (pull ha' g) (x ω) = torusWord w (a (x ω)) from hg1.trans hg2,
          show (pull hb' h) (y ω) = torusWord w (b (y ω)) from hh2.trans hh3]
      _ = _ := (ht1.trans (ht2.trans (congrArg (_ * ·) hh1))).symm
  have hh := congrArg (fun q => (pull hz).adjoint q) he
  have hid := congrArg (fun A : Lp ℂ 2 η →L[ℂ] Lp ℂ 2 η => A (pull hc' f)) (pull_adjoint_pull hz)
  change (pull hz).adjoint (pull hz (pull hc' f)) = pull hc' f at hid
  rw [hid] at hh
  exact hh

end

variable {Ω Z X Y I : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y] [Countable I]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {η : Measure Z}
  [retained8 : IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ] [IsFiniteMeasure η]
  {x : Ω → X} {y : Ω → Y} {z : Ω → Z}

attribute [local instance] OAI.Rokhlin.JoiningOperator.instMeasurableSpaceCircle_solutions_1
include retained8 in
lemma ratio_field_le_active
    (hz : MeasurePreserving z μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ))
    (a : X → I → Circle) (b : Y → I → Circle) (c : Z → I → Circle)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (hr : ∀ᵐ ω ∂μ, c (z ω) = a (x ω) * (b (y ω))⁻¹) :
    lpMeas ℂ ℂ (MeasurableSpace.comap c inferInstance) 2 η ≤
      (LinearMap.range (operator hz hxy).toLinearMap).topologicalClosure := by
  let _ := retained8
  erw [←torusWord_pullback_dense (μ := η) c hc]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨w,rfl⟩
  exact ⟨_, (torusWord_contraction hz hxy a b c ha hb hc hr w).symm⟩

end JoiningOperator

namespace ConditionalFibres
open MeasureTheory ProbabilityTheory
lemma ae_kernel_joint {Ω Z V : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSpace V] {μ : Measure Ω} [SFinite μ] {z : Ω → Z} {v : Ω → V}
    {κ : Kernel Z V} [IsSFiniteKernel κ] (h : HasCondDistrib v z κ μ) {p : Z × V → Prop}
    (hp : MeasurableSet {q | p q}) (hv : ∀ᵐ ω ∂μ, p (z ω,v ω)) :
    ∀ᵐ a ∂μ.map z, ∀ᵐ b ∂κ a, p (a,b) := by
  apply Measure.ae_ae_of_ae_compProd
  rw [←h.map_eq]
  exact (ae_map_iff h.aemeasurable hp).mpr hv
end ConditionalFibres

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal
attribute [local instance] OAI.Rokhlin.ArrayObjects.Object.Rolled.instMeasurableSpaceCircle
local instance instBorelSpaceCircle : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

local instance instFactNeENNRealOfNatTop_11_rf89681_1 : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
theorem grouped_torus_completeness (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∃ (J : Type u) (_ : Countable J)
        (A : (cols.P → rows.A → Arr I M.Y n) → J → Circle)
        (B : (cols.P → rows.B → Arr I M.Y n) → J → Circle)
        (P : (cols.A → rows.P → Arr I M.Y n) → J → Circle)
        (Q : (cols.B → rows.P → Arr I M.Y n) → J → Circle)
        (H : (cols.P → rows.P → Arr I M.Y n) → J → Circle),
        Measurable A ∧ Measurable B ∧ Measurable P ∧ Measurable Q ∧ Measurable H ∧
        commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e =
          lpMeas ℂ ℂ (MeasurableSpace.comap H inferInstance) 2 (cellLaw M rows.P cols.P n e) ∧
        (∀ᵐ y ∂M.ownKernel (n+2) e,
          H (cells M rows.P cols.P n y) = A (cells M rows.A cols.P n y) *
            (B (cells M rows.B cols.P n y))⁻¹) ∧
        (∀ᵐ y ∂M.ownKernel (n+2) e,
          H (cells M rows.P cols.P n y) = P (cells M rows.P cols.A n y) *
            (Q (cells M rows.P cols.B n y))⁻¹) := by
  filter_upwards [grouped_polar_data M hM rows cols n,
    grouped_haar_normalization M hM rows cols n,
    grouped_polar_a_field M hM rows cols n,grouped_polar_b_field M hM rows cols n,
    pairPair_fixed_conditional M hM rows.P rows.A rows.B cols.P cols.A cols.B
      rows.cardP cols.properP n,
    columnPair_fixed_conditional M hM rows.P rows.A rows.B cols.P rows.cardP cols.properP n,
    rowPair_fixed_conditional M rows.P cols.P cols.A cols.B n,
    columnPair_fixed_marginals M hM rows.P rows.A rows.B cols.P rows.cardP cols.properP
      rows.properA rows.properB rows.disjointPA rows.disjointPB rows.properPA rows.properPB n,
    rowPair_fixed_marginals M hM rows.P cols.P cols.A cols.B rows.properP
      cols.disjointPA cols.disjointPB cols.properPA cols.properPB n,
    cells_fibre_marginal M hM rows.P cols.P rows.properP n,
    cells_fibre_marginal M hM rows.A cols.P rows.properA n,
    cells_fibre_marginal M hM rows.B cols.P rows.properB n,
    cells_fibre_marginal M hM rows.P cols.A rows.properP n,
    cells_fibre_marginal M hM rows.P cols.B rows.properP n,
    cells_indep_rows_fibre M hM rows.A rows.B cols.P cols.P rows.disjointAB rows.properAB n,
    cells_indep_columns_fibre M rows.P rows.P cols.A cols.B cols.disjointAB cols.properAB n,
    columnActive_eq_range M hM rows cols.P cols.properP n,
    rowActive_eq_range M hM rows.P rows.properP cols n,
    grouped_column_contraction_projection M hM rows cols n]
      with e hRd hHaar haField hbField hpair hκ hξ hκm hξm hz hx hy hc hd hxy hcd hcol hrow hproj
  obtain ⟨R⟩ := hRd
  obtain ⟨J,hJ,A,B,P,Q,H,hA,hB,hP,hQ,hH,hfa,hfb,hra,hrb⟩ :=
    R.torus_coordinates (hHaar R)
      ((columnPairKernel M rows.P rows.A rows.B cols.P n).sectR e)
      ((rowPairKernel M rows.P cols.P cols.A cols.B n).sectR e) hκ hξ hpair
      (hκm.mono fun _ h => ⟨h.1.map_eq,h.2.map_eq⟩)
      (hξm.mono fun _ h => ⟨h.1.map_eq,h.2.map_eq⟩)
  let : Countable J := hJ
  let : Group (J → Circle) := (inferInstance : CommGroup (J → Circle)).toGroup
  let : MeasurableMul₂ (J → Circle) := inferInstance
  have haF := haField R
  have hbF := hbField R
  rw [hfa] at haF
  rw [hfb] at hbF
  let hXY : MeasurePreserving (fun y => (cells M rows.A cols.P n y,cells M rows.B cols.P n y))
      (M.ownKernel (n+2) e) ((cellLaw M rows.A cols.P n e).prod (cellLaw M rows.B cols.P n e)) :=
    ⟨hx.measurable.prodMk hy.measurable, by
      rw [←hx.map_eq,←hy.map_eq]
      exact hxy.map_prod_eq_prod_map_map hx.measurable.aemeasurable hy.measurable.aemeasurable⟩
  let hPQ : MeasurePreserving (fun y => (cells M rows.P cols.A n y,cells M rows.P cols.B n y))
      (M.ownKernel (n+2) e) ((cellLaw M rows.P cols.A n e).prod (cellLaw M rows.P cols.B n e)) :=
    ⟨hc.measurable.prodMk hd.measurable, by
      rw [←hc.map_eq,←hd.map_eq]
      exact hcd.map_prod_eq_prod_map_map hc.measurable.aemeasurable hd.measurable.aemeasurable⟩
  let α := ((columnPairKernel M rows.P rows.A rows.B cols.P n).sectR e).map (Prod.map A B)
  let : IsMarkovKernel α := Kernel.IsMarkovKernel.map _ (hA.prodMap hB)
  have hα : HasCondDistrib (fun y => (A (cells M rows.A cols.P n y),B (cells M rows.B cols.P n y)))
      (cells M rows.P cols.P n) α (M.ownKernel (n+2) e) := hκ.comp_left (hA.prodMap hB)
  let σ := (cellLaw M rows.B cols.P n e).map B
  let : IsProbabilityMeasure σ := (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hB.aemeasurable
  have hm : ∀ᵐ v ∂cellLaw M rows.P cols.P n e, (α v).map Prod.snd = σ := by
    rw [hz.map_eq] at hκm
    filter_upwards [hκm] with v hv
    dsimp only [α,σ]
    exact (kernel_map_pair_snd ((columnPairKernel M rows.P rows.A rows.B cols.P n).sectR e) v hA hB).trans
      (congrArg (fun m => m.map B) hv.2.map_eq)
  have hr : ∀ᵐ v ∂cellLaw M rows.P cols.P n e, ∀ᵐ w ∂α v, w.1*w.2⁻¹ = H v := by
    rw [←hz.map_eq]
    exact ConditionalFibres.ae_kernel_joint hα
      (measurableSet_eq_fun (Measurable.of_eval fun j =>
        ((measurable_pi_apply j).comp measurable_snd.fst).mul
          (((measurable_pi_apply j).comp measurable_snd.snd).inv))
        (hH.comp measurable_fst)) (hra.mono fun _ h => h.symm)
  refine ⟨J,hJ,A,B,P,Q,H,hA,hB,hP,hQ,hH,le_antisymm ?_ ?_,hra,hrb⟩
  · apply JoiningOperator.common_space_le_ratio (G := J → Circle) (gG := inferInstance) (mG := inferInstance) (hG := inferInstance) (a := A) (b := B) (c := H)
      hz hXY hA hB hH hα σ hm hr _
      (commonActive M rows.A rows.P rows.B cols.P cols.A cols.B n e).starProjection
      (commonActive M rows.B rows.P rows.A cols.P cols.A cols.B n e).starProjection
    · rw [←hcol hz hXY]
      exact inf_le_right
    · exact hproj hz hXY
    · intro g
      exact haF (Submodule.starProjection_apply_mem _ g)
    · intro h
      exact hbF (Submodule.starProjection_apply_mem _ h)
  · apply le_inf
    · rw [hrow hz hPQ]
      exact JoiningOperator.ratio_field_le_active hz hPQ P Q H hP hQ hH hrb
    · rw [hcol hz hXY]
      exact JoiningOperator.ratio_field_le_active hz hXY A B H hA hB hH hra
end ArrayObjects.Object.Rolled

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in
lemma cells_pair_preserving {A B S D : Finset I} {n : ℕ} {e : Arr I M.U (n+2)}
    (ha : MeasurePreserving (cells M A S n) (M.ownKernel (n+2) e) (cellLaw M A S n e))
    (hb : MeasurePreserving (cells M B D n) (M.ownKernel (n+2) e) (cellLaw M B D n e))
    (hi : IndepFun (cells M A S n) (cells M B D n) (M.ownKernel (n+2) e)) :
    MeasurePreserving (fun y => (cells M A S n y,cells M B D n y))
      (M.ownKernel (n+2) e) ((cellLaw M A S n e).prod (cellLaw M B D n e)) := by
  refine ⟨ha.measurable.prodMk hb.measurable,?_⟩
  rw [←ha.map_eq,←hb.map_eq]
  exact hi.map_prod_eq_prod_map_map ha.measurable.aemeasurable hb.measurable.aemeasurable

end ArrayObjects.Object.Rolled

namespace JoiningOperator
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {Ω Z X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure Ω) (η : Measure Z) [IsFiniteMeasure η]
  (x : Ω → X) (y : Ω → Y) (z : Ω → Z)

lemma circle_mem_splitExact (f : Z → Circle) (g : X → Circle) (h : Y → Circle)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (he : ∀ᵐ ω ∂μ, f (z ω) = g (x ω) * h (y ω)) :
    circleLp η f hf ∈ splitExact μ η x y z :=
  ⟨f,g,h,hf,hg,hh,1,(one_smul _ _).symm,he⟩

variable {μ η x y z}

lemma circleLp_contraction {ν : Measure X} {ρ : Measure Y}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hz : MeasurePreserving z μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ))
    (f : Z → Circle) (g : X → Circle) (h : Y → Circle)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (he : ∀ᵐ ω ∂μ, f (z ω) = g (x ω)*h (y ω)) :
    circleLp η f hf = contraction hz hxy (circleLp ν g hg) (circleLp ρ h hh) := by
  have hx := (measurePreserving_fst (μ := ν) (ν := ρ)).comp hxy
  have hy := (measurePreserving_snd (μ := ν) (ν := ρ)).comp hxy
  have hp : pull hz (circleLp η f hf) = pull hxy (tensorLp (circleLp ν g hg) (circleLp ρ h hh)) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (circleLp η f hf) hz,
      hz.quasiMeasurePreserving.ae (circleLp_coe η f hf),
      Lp.coeFn_compMeasurePreserving (tensorLp (circleLp ν g hg) (circleLp ρ h hh)) hxy,
      hxy.quasiMeasurePreserving.ae (coe_tensorLp (circleLp ν g hg) (circleLp ρ h hh)),
      hx.quasiMeasurePreserving.ae (circleLp_coe ν g hg),
      hy.quasiMeasurePreserving.ae (circleLp_coe ρ h hh),he] with ω h1 h2 h3 h4 h5 h6 h7
    calc
      _ = (f (z ω) : ℂ) := h1.trans h2
      _ = (g (x ω) : ℂ)*(h (y ω) : ℂ) := congrArg ((↑) : Circle → ℂ) h7
      _ = _ := (h3.trans (h4.trans (congrArg₂ (·*·) h5 h6))).symm
  have hid := congrArg (fun A : Lp ℂ 2 η →L[ℂ] Lp ℂ 2 η => A (circleLp η f hf)) (pull_adjoint_pull hz)
  exact hid.symm.trans (congrArg (fun q => (pull hz).adjoint q) hp)

lemma splitExact_le_active {ν : Measure X} {ρ : Measure Y}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hz : MeasurePreserving z μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ)) :
    splitExact μ η x y z ⊆ (LinearMap.range (operator hz hxy).toLinearMap).topologicalClosure := by
  rintro v ⟨f,g,h,hf,hg,hh,c,rfl,he⟩
  exact (LinearMap.range (operator hz hxy).toLinearMap).topologicalClosure.smul_mem c
    (Submodule.le_topologicalClosure _ ⟨_,(circleLp_contraction hz hxy f g h hf hg hh he).symm⟩)
end JoiningOperator

section
open MeasureTheory
open scoped ENNReal
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {Ω J : Type*} [MeasurableSpace Ω] [Countable J]
    (μ : Measure Ω) [IsFiniteMeasure μ] (γ : Ω → J → Circle) (hγ : Measurable γ)

lemma torus_circle_pull (w : FreeGroup J) :
    circleLp μ (fun x => torusWordCircle w (γ x)) ((torusWordCircle w).continuous.measurable.comp hγ) =
      JoiningOperator.pull (MeasurePreserving.mk hγ rfl)
        (ContinuousMap.toLp 2 (μ.map γ) ℂ (torusWord w)) := by
  apply Lp.ext
  filter_upwards [circleLp_coe μ (fun x => torusWordCircle w (γ x)) ((torusWordCircle w).continuous.measurable.comp hγ),
    Lp.coeFn_compMeasurePreserving (ContinuousMap.toLp 2 (μ.map γ) ℂ (torusWord w)) (MeasurePreserving.mk hγ rfl),
    (MeasurePreserving.mk hγ rfl).quasiMeasurePreserving.ae (ContinuousMap.coeFn_toLp (μ.map γ) (𝕜 := ℂ) (p := 2) (torusWord w))]
      with x h1 h2 h3
  exact h1.trans (h2.trans h3).symm

lemma torus_circle_dense :
    (Submodule.span ℂ (Set.range (fun w => circleLp μ (fun x => torusWordCircle w (γ x))
      ((torusWordCircle w).continuous.measurable.comp hγ)))).topologicalClosure =
      lpMeas ℂ ℂ (MeasurableSpace.comap γ inferInstance) 2 μ := by
  simp_rw [torus_circle_pull μ γ hγ]
  exact torusWord_pullback_dense γ hγ
end

namespace JoiningOperator
open MeasureTheory
open scoped ENNReal
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {Ω Z X Y P Q J : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace P] [MeasurableSpace Q]
    [Countable J] (μ : Measure Ω) (η : Measure Z) [IsFiniteMeasure η]
    (x : Ω → X) (y : Ω → Y) (p : Ω → P) (q : Ω → Q) (z : Ω → Z)

lemma torus_exact_split (A : X → J → Circle) (B : Y → J → Circle) (H : Z → J → Circle)
    (hA : Measurable A) (hB : Measurable B) (hH : Measurable H)
    (he : ∀ᵐ ω ∂μ, H (z ω) = A (x ω) * (B (y ω))⁻¹) (w : FreeGroup J) :
    circleLp η (fun v => torusWordCircle w (H v)) ((torusWordCircle w).continuous.measurable.comp hH) ∈
      splitExact μ η x y z := by
  apply circle_mem_splitExact μ η x y z _ (fun v => torusWordCircle w (A v))
    (fun v => (torusWordCircle w (B v))⁻¹) _
    ((torusWordCircle w).continuous.measurable.comp hA)
    (((torusWordCircle w).continuous.measurable.comp hB).inv)
  filter_upwards [he] with ω hω
  rw [hω,torusWordCircle_mul,torusWordCircle_inv]

lemma torus_split_inter_span
    (A : X → J → Circle) (B : Y → J → Circle)
    (C : P → J → Circle) (D : Q → J → Circle) (H : Z → J → Circle)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D) (hH : Measurable H)
    (he : ∀ᵐ ω ∂μ, H (z ω) = A (x ω) * (B (y ω))⁻¹)
    (hf : ∀ᵐ ω ∂μ, H (z ω) = C (p ω) * (D (q ω))⁻¹)
    (V : Submodule ℂ (Lp ℂ 2 η)) (hV : IsClosed (V : Set (Lp ℂ 2 η)))
    (hsub : splitExact μ η x y z ∩ splitExact μ η p q z ⊆ V)
    (hfield : V = lpMeas ℂ ℂ (MeasurableSpace.comap H inferInstance) 2 η) :
    (Submodule.span ℂ (splitExact μ η x y z ∩ splitExact μ η p q z)).topologicalClosure = V := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hsub) hV
  · rw [hfield,←torus_circle_dense η H hH]
    apply Submodule.topologicalClosure_mono
    apply Submodule.span_mono
    rintro v ⟨w,rfl⟩
    exact ⟨torus_exact_split μ η x y z A B H hA hB hH he w,
      torus_exact_split μ η p q z C D H hC hD hH hf w⟩
end JoiningOperator

namespace ArrayObjects.Object.Rolled

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma grouped_exact_split_span_oai (hM : M.IsSaturated) (P R : Finset I)
    (s : ComplementSplit P) (t : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      (Submodule.span ℂ (rowSplitExact M P R t n e ∩ columnSplitExact M P R s n e)).topologicalClosure =
        commonActive M P s.A s.B R t.A t.B n e := by
  filter_upwards [grouped_torus_completeness M hM s.partition t.partition n,
    rowActive_eq_range M hM P s.partition.properP t.partition n,
    columnActive_eq_range M hM s.partition R t.partition.properP n,
    cells_fibre_marginal M hM P R s.partition.properP n,
    cells_fibre_marginal M hM P t.A s.partition.properP n,
    cells_fibre_marginal M hM P t.B s.partition.properP n,
    cells_fibre_marginal M hM s.A R s.partition.properA n,
    cells_fibre_marginal M hM s.B R s.partition.properB n,
    cells_indep_columns_fibre M P P t.A t.B t.disjointAB t.partition.properAB n,
    cells_indep_rows_fibre M hM s.A s.B R R s.disjointAB s.partition.properAB n]
      with e he hr hc hz hpa hpb hap hbp hri hci
  obtain ⟨J,hJ,A,B,C,D,H,hA,hB,hC,hD,hH,hF,hAB,hCD⟩ := he
  let : Countable J := hJ
  let hrow := cells_pair_preserving M hpa hpb hri
  let hcol := cells_pair_preserving M hap hbp hci
  apply JoiningOperator.torus_split_inter_span _ _ _ _ _ _ _ C D A B H hC hD hA hB hH hCD hAB _ _ _ hF
  · exact IsClosed.inter (essentialRange.isClosed (cellLaw M P t.A n e) (fibreRowEdge M P t.A R t.B n e))
      (essentialRange.isClosed (cellLaw M s.A R n e) (fibreColumnEdge M s.A P s.B R n e))
  · rintro v ⟨hv,hw⟩
    constructor
    · rw [hr hz hrow]
      exact JoiningOperator.splitExact_le_active hz hrow hv
    · rw [hc hz hcol]
      exact JoiningOperator.splitExact_le_active hz hcol hw

end ArrayObjects.Object.Rolled

open MeasureTheory Set

end Rokhlin

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_exact_split_span_oai.{u} := @OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_exact_split_span_oai.{u}
