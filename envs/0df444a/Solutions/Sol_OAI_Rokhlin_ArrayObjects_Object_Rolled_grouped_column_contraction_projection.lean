-- Prove2me | solution 1 for OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_column_contraction_projection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:04:03.495991+00:00
-- url     : https://prove2.me/submissions/23b5855e-3905-43b9-8bc2-4e1ae7af7f89

import Mathlib
import Definitions.Def_OAIQ3Ro002
import Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_grouped_active_intersections

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
/-- Mathlib's newer name for `aemeasurable_pi_lambda` (with `f` implicit). -/
theorem _root_.AEMeasurable.of_eval {δ ι : Type*} [Countable ι] {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {μ : MeasureTheory.Measure δ} {f : δ → ∀ i, π i}
    (h : ∀ i, AEMeasurable (fun a => f a i) μ) : AEMeasurable f μ := aemeasurable_pi_lambda f h
end OAICompat434

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

lemma aestronglyMeasurable_of_inner {U H : Type*} [MeasurableSpace U]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [SecondCountableTopology H] {μ : Measure U} {f : U → H}
    (hf : ∀ h : H, AEStronglyMeasurable (fun u => inner ℂ h (f u)) μ) :
    AEStronglyMeasurable f μ := by
  borelize H
  let e : H → ℕ → ℂ := fun h n => inner ℂ (TopologicalSpace.denseSeq H n) h
  have hec : Continuous e := by fun_prop
  have hei : Function.Injective e := by
    intro v w h
    have hh : (fun z : H => inner ℂ z v) = (fun z : H => inner ℂ z w) := by
      apply (TopologicalSpace.denseRange_denseSeq H).equalizer (by fun_prop) (by fun_prop)
      funext n
      exact congrFun h n
    apply sub_eq_zero.mp
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [inner_sub_right, congrFun hh (v - w), sub_self]
  have he := hec.measurableEmbedding hei
  apply (he.aemeasurable_comp_iff.mp ?_).aestronglyMeasurable
  exact AEMeasurable.of_eval (fun n => (hf (TopologicalSpace.denseSeq H n)).aemeasurable)

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

lemma family_aestronglyMeasurable [SecondCountableTopology (Lp ℂ 2 ν)]
    (hm : ∀ᵐ u ∂m,
    MeasurePreserving Prod.fst (κ u) ν ∧ MeasurePreserving Prod.snd (κ u) ρ)
    (h : Lp ℂ 2 ρ) : AEStronglyMeasurable (fun u => family κ ν ρ u h) m :=
  aestronglyMeasurable_of_inner (fun g => family_inner_aestronglyMeasurable hm g h)

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

lemma cells_indep_rows_fibre (hM : M.IsSaturated) (P A S R : Finset I)
    (hPA : Disjoint P A) (hproper : P ∪ A ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      IndepFun (cells M P S n) (cells M A R n) (M.ownKernel (n+2) e) := by
  filter_upwards [rows_indep_fibre M hM P A hPA hproper n] with e he
  exact he.comp (measurable_rowRestrict M P S n) (measurable_rowRestrict M A R n)

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
lemma fibreColumnEdge_eq (P A B S : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    fibreColumnEdge M P A B S n e = JoiningOperator.family ((columnPairKernel M P A B S n).sectR e)
      (cellLaw M A S n e) (cellLaw M B S n e) := by
  ext x h
  rfl

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

omit [MeasurableSpace Ω] in
lemma pair_comap_swap (a : Ω → Y) (b : Ω → Z) :
    MeasurableSpace.comap (fun ω => (a ω,b ω)) inferInstance =
      MeasurableSpace.comap (fun ω => (b ω,a ω)) inferInstance := by
  change ((inferInstance : MeasurableSpace Y).prod (inferInstance : MeasurableSpace Z)).comap _ =
    ((inferInstance : MeasurableSpace Z).prod (inferInstance : MeasurableSpace Y)).comap _
  rw [MeasurableSpace.comap_prodMk, MeasurableSpace.comap_prodMk, sup_comm]
end JoiningOperator

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
namespace JoiningOperator

variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {η : Measure U} {ν : Measure X} {ρ : Measure Y}
  {u : Ω → U} {x : Ω → X} {y : Ω → Y}
  {κ : Kernel U (X × Y)} [IsMarkovKernel κ]

lemma family_active_swap_conditioner [SecondCountableTopology (Lp ℂ 2 ρ)]
    [SecondCountableTopology (Lp ℂ 2 η)]
    {ξ : Kernel Y (X × U)} [IsMarkovKernel ξ]
    (hu : MeasurePreserving u μ η) (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) u κ μ)
    (hmκ : ∀ᵐ a ∂η, MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (hξ : HasCondDistrib (fun ω => (x ω,u ω)) y ξ μ)
    (hmξ : ∀ᵐ a ∂ρ, MeasurePreserving Prod.fst (ξ a) ν ∧ MeasurePreserving Prod.snd (ξ a) η) :
    essentialRange η (family κ ν ρ) = essentialRange ρ (family ξ ν η) := by
  have h₁ := active_eq_essentialRange hu.measurable hx hy hκ (hu.map_eq.symm ▸ hmκ)
  have h₂ := active_eq_essentialRange hy.measurable hx hu hξ (hy.map_eq.symm ▸ hmξ)
  rw [hu.map_eq] at h₁
  rw [hy.map_eq] at h₂
  exact h₁.symm.trans ((active_observation_eq hx _ _ (pair_comap_swap u y)).trans h₂)

end JoiningOperator
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal


section
local instance instFactNeENNRealOfNatTop_5 : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma columnActive_swap (hM : M.IsSaturated) (rows : TriplePartition I)
    (R : Finset I) (hR : R ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      columnActive M rows.P rows.A rows.B R n e = columnActive M rows.P rows.B rows.A R n e := by
  filter_upwards [cells_fibre_marginal M hM rows.A R rows.properA n,
    cells_fibre_marginal M hM rows.P R rows.properP n,
    cells_fibre_marginal M hM rows.B R rows.properB n,
    columnPair_fixed_conditional M hM rows.A rows.P rows.B R (by
      have := rows.card_eq; have := Finset.card_pos.mpr rows.nonemptyP
      have := Finset.card_pos.mpr rows.nonemptyB; omega) hR n,
    columnPair_fixed_conditional M hM rows.B rows.P rows.A R (by
      have := rows.card_eq; have := Finset.card_pos.mpr rows.nonemptyP
      have := Finset.card_pos.mpr rows.nonemptyA; omega) hR n,
    columnPair_fixed_marginals M hM rows.A rows.P rows.B R (by
      have := rows.card_eq; have := Finset.card_pos.mpr rows.nonemptyP
      have := Finset.card_pos.mpr rows.nonemptyB; omega) hR rows.properP rows.properB
      rows.disjointPA.symm rows.disjointAB (by simpa [Finset.union_comm] using rows.properPA) rows.properAB n,
    columnPair_fixed_marginals M hM rows.B rows.P rows.A R (by
      have := rows.card_eq; have := Finset.card_pos.mpr rows.nonemptyP
      have := Finset.card_pos.mpr rows.nonemptyA; omega) hR rows.properP rows.properA
      rows.disjointPB.symm rows.disjointAB.symm
      (by simpa [Finset.union_comm] using rows.properPB)
      (by simpa [Finset.union_comm] using rows.properAB) n] with e hs hr ht hκ hξ hmκ hmξ
  rw [hs.map_eq] at hmκ
  rw [ht.map_eq] at hmξ
  unfold columnActive
  rw [fibreColumnEdge_eq,fibreColumnEdge_eq]
  exact JoiningOperator.family_active_swap_conditioner hs hr ht hκ hmκ hξ hmξ

end
universe u

end ArrayObjects.Object.Rolled

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

namespace JoiningOperator
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal
variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Ω}
  {η : Measure U} {ν : Measure X} {ρ : Measure Y}
  {u : Ω → U} {x : Ω → X} {y : Ω → Y}
  [SFinite η] [SFinite ρ]

omit [SFinite η] in
lemma contraction_inner (hx : MeasurePreserving x μ ν)
    (huy : MeasurePreserving (fun ω => (u ω, y ω)) μ (η.prod ρ))
    (f : Lp ℂ 2 ν) (g : Lp ℂ 2 η) (h : Lp ℂ 2 ρ) :
    inner ℂ f (contraction hx huy g h) =
      ∫ ω, g (u ω) * inner ℂ (f (x ω)) (h (y ω)) ∂μ := by
  rw [contraction, inner_operator]
  apply integral_congr_ae
  filter_upwards [huy.quasiMeasurePreserving.ae (coe_tensorLp g h)] with ω hω
  rw [hω]
  simp only [RCLike.inner_apply]
  ring

omit [SFinite η] in
lemma contraction_integrand (hx : MeasurePreserving x μ ν)
    (huy : MeasurePreserving (fun ω => (u ω, y ω)) μ (η.prod ρ))
    (f : Lp ℂ 2 ν) (g : Lp ℂ 2 η) (h : Lp ℂ 2 ρ) :
    Integrable (fun ω => g (u ω) * inner ℂ (f (x ω)) (h (y ω))) μ := by
  apply (integrable_inner_comp hx huy f (tensorLp g h)).congr
  filter_upwards [huy.quasiMeasurePreserving.ae (coe_tensorLp g h)] with ω hω
  rw [hω]
  simp only [RCLike.inner_apply]
  ring

variable [IsFiniteMeasure η] [SecondCountableTopology (Lp ℂ 2 ν)]
  {κ : Kernel U (X × Y)} [IsMarkovKernel κ]

omit [SFinite η] [SFinite ρ] [IsMarkovKernel κ] in
lemma family_weight_integrable
    (hm : ∀ᵐ a ∂η, MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (g : Lp ℂ 2 η) (h : Lp ℂ 2 ρ) :
    Integrable (fun a => g a • family κ ν ρ a h) η := by
  apply ((Lp.memLp g).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).smul_bdd ‖h‖
    (family_aestronglyMeasurable hm h)
  filter_upwards with a
  calc
    _ ≤ ‖family κ ν ρ a‖ * ‖h‖ := (family κ ν ρ a).le_opNorm h
    _ ≤ _ := by grw [family_norm_le]; simp

omit [SFinite η] in
lemma contraction_integral (hu : MeasurePreserving u μ η)
    (hx : MeasurePreserving x μ ν)
    (huy : MeasurePreserving (fun ω => (u ω, y ω)) μ (η.prod ρ))
    (hκ : HasCondDistrib (fun ω => (x ω, y ω)) u κ μ)
    (hm : ∀ᵐ a ∂η, MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (g : Lp ℂ 2 η) (h : Lp ℂ 2 ρ) :
    contraction hx huy g h = ∫ a, g a • family κ ν ρ a h ∂η := by
  have : IsFiniteMeasure (μ.map u) := hu.map_eq.symm ▸ inferInstance
  apply ext_inner_left ℂ
  intro f
  rw [contraction_inner, ← integral_inner (family_weight_integrable hm g h)]
  let F : U × (X × Y) → ℂ := fun p => g p.1 * inner ℂ (f p.2.1) (h p.2.2)
  have hFm : StronglyMeasurable F :=
    (g.1.stronglyMeasurable.comp_measurable (by fun_prop)).mul
      ((f.1.stronglyMeasurable.comp_measurable (by fun_prop)).inner
        (h.1.stronglyMeasurable.comp_measurable (by fun_prop)))
  have hFi : Integrable F (μ.map u ⊗ₘ κ) := by
    rw [← hκ.map_eq]
    apply (integrable_map_measure hFm.aestronglyMeasurable hκ.aemeasurable).mpr
    exact contraction_integrand hx huy f g h
  calc
    _ = ∫ p, F p ∂μ.map u ⊗ₘ κ := hκ.integral_comp hFm.aestronglyMeasurable
    _ = ∫ a, ∫ p, F (a,p) ∂κ a ∂μ.map u := Measure.integral_compProd hFi
    _ = ∫ a, g a * (∫ p, inner ℂ (f p.1) (h p.2) ∂κ a) ∂η := by
      rw [hu.map_eq]
      simp only [F, integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [family_inner hm f h] with a ha
      rw [inner_smul_right, ha]

omit [SFinite η] in
lemma contraction_projection (hu : MeasurePreserving u μ η)
    (hx : MeasurePreserving x μ ν)
    (huy : MeasurePreserving (fun ω => (u ω, y ω)) μ (η.prod ρ))
    (hκ : HasCondDistrib (fun ω => (x ω, y ω)) u κ μ)
    (hm : ∀ᵐ a ∂η, MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (P : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (Q : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ)
    (hPQ : ∀ᵐ a ∂η, P ∘L family κ ν ρ a = family κ ν ρ a ∘L Q)
    (g : Lp ℂ 2 η) (h : Lp ℂ 2 ρ) :
    P (contraction hx huy g h) = contraction hx huy g (Q h) := by
  rw [contraction_integral hu hx huy hκ hm,
    contraction_integral hu hx huy hκ hm,
    ← P.integral_comp_comm (family_weight_integrable hm g h)]
  apply integral_congr_ae
  filter_upwards [hPQ] with a ha
  rw [map_smul]
  exact congrArg (g a • ·) (congrArg (fun L : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ν => L h) ha)
end JoiningOperator

namespace JoiningOperator
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal
variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Ω}
  {η : Measure U} {ν : Measure X} {ρ : Measure Y}
  {u : Ω → U} {x : Ω → X} {y : Ω → Y}

lemma contraction_swap [SFinite η] [SFinite ρ] (hx : MeasurePreserving x μ ν)
    (huy : MeasurePreserving (fun ω => (u ω,y ω)) μ (η.prod ρ))
    (hyu : MeasurePreserving (fun ω => (y ω,u ω)) μ (ρ.prod η))
    (g : Lp ℂ 2 η) (h : Lp ℂ 2 ρ) :
    contraction hx huy g h = contraction hx hyu h g := by
  apply ext_inner_left ℂ
  intro f
  rw [contraction_inner,contraction_inner]
  apply integral_congr_ae
  filter_upwards with ω
  simp only [RCLike.inner_apply]
  ring

lemma contraction_projection_both
    [IsFiniteMeasure η] [IsFiniteMeasure ρ]
    (hx : MeasurePreserving x μ ν)
    (huy : MeasurePreserving (fun ω => (u ω,y ω)) μ (η.prod ρ))
    (hyu : MeasurePreserving (fun ω => (y ω,u ω)) μ (ρ.prod η))
    (D : Submodule ℂ (Lp ℂ 2 ν)) [D.HasOrthogonalProjection]
    (P : Submodule ℂ (Lp ℂ 2 η)) [P.HasOrthogonalProjection]
    (Q : Submodule ℂ (Lp ℂ 2 ρ)) [Q.HasOrthogonalProjection]
    (hr : ∀ g h, D.starProjection (contraction hx huy g h) = contraction hx huy g (Q.starProjection h))
    (hl : ∀ h g, D.starProjection (contraction hx hyu h g) = contraction hx hyu h (P.starProjection g))
    (g : Lp ℂ 2 η) (h : Lp ℂ 2 ρ) :
    D.starProjection (contraction hx huy g h) =
      contraction hx huy (P.starProjection g) (Q.starProjection h) := by
  calc
    _ = D.starProjection (D.starProjection (contraction hx huy g h)) := by
      rw [D.starProjection_eq_self_iff.mpr (D.starProjection_apply_mem _)]
    _ = D.starProjection (contraction hx huy g (Q.starProjection h)) := by rw [hr]
    _ = D.starProjection (contraction hx hyu (Q.starProjection h) g) := by rw [contraction_swap hx huy hyu]
    _ = contraction hx hyu (Q.starProjection h) (P.starProjection g) := hl _ _
    _ = _ := contraction_swap hx hyu huy _ _

end JoiningOperator

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal

section
local instance instFactNeENNRealOfNatTop_8 : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma commonActive_swapRows (hM : M.IsSaturated) (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e =
        commonActive M rows.P rows.B rows.A cols.P cols.A cols.B n e := by
  filter_upwards [columnActive_swap M hM rows cols.P cols.properP n] with e he
  simp only [commonActive,he]

lemma grouped_first_column_edge (hM : M.IsSaturated) (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ᵐ s ∂cellLaw M rows.A cols.P n e,
        (commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e).starProjection ∘L
          fibreColumnEdge M rows.A rows.P rows.B cols.P n e s =
        fibreColumnEdge M rows.A rows.P rows.B cols.P n e s ∘L
          (commonActive M rows.B rows.P rows.A cols.P cols.A cols.B n e).starProjection := by
  filter_upwards [grouped_active_intersections M hM rows.swapPA cols.swapPA n,
    commonActive_swapRows M hM rows.swapPB cols n] with e he hs
  dsimp only [TriplePartition.swapPA,TriplePartition.swapPB] at he hs
  have hp : (commonActive M rows.B rows.A rows.P cols.P cols.A cols.B n e).starProjection =
      (commonActive M rows.B rows.P rows.A cols.P cols.A cols.B n e).starProjection := by congr 1
  filter_upwards [he.2.2.1] with s h
  rw [hp] at h
  exact h

lemma grouped_second_column_edge (hM : M.IsSaturated) (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ᵐ t ∂cellLaw M rows.B cols.P n e,
        (commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e).starProjection ∘L
          fibreColumnEdge M rows.B rows.P rows.A cols.P n e t =
        fibreColumnEdge M rows.B rows.P rows.A cols.P n e t ∘L
          (commonActive M rows.A rows.P rows.B cols.P cols.A cols.B n e).starProjection := by
  filter_upwards [grouped_first_column_edge M hM rows.swapAB cols n,
    commonActive_swapRows M hM rows cols n] with e he hs
  have hp : (commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e).starProjection =
      (commonActive M rows.P rows.B rows.A cols.P cols.A cols.B n e).starProjection := by congr 1
  filter_upwards [he] with t h
  rw [hp]
  exact h

theorem grouped_column_contraction_projection_oai (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ (hr : MeasurePreserving (cells M rows.P cols.P n) (M.ownKernel (n+2) e) (cellLaw M rows.P cols.P n e))
      (hst : MeasurePreserving (fun y => (cells M rows.A cols.P n y,cells M rows.B cols.P n y))
        (M.ownKernel (n+2) e) ((cellLaw M rows.A cols.P n e).prod (cellLaw M rows.B cols.P n e)))
      (g : Lp ℂ 2 (cellLaw M rows.A cols.P n e)) (h : Lp ℂ 2 (cellLaw M rows.B cols.P n e)),
      (commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e).starProjection
        (JoiningOperator.contraction hr hst g h) =
      JoiningOperator.contraction hr hst
        ((commonActive M rows.A rows.P rows.B cols.P cols.A cols.B n e).starProjection g)
        ((commonActive M rows.B rows.P rows.A cols.P cols.A cols.B n e).starProjection h) := by
  let rr := rows.swapPA
  let rt := rows.swapPB
  filter_upwards [grouped_first_column_edge M hM rows cols n,grouped_second_column_edge M hM rows cols n,
    cells_fibre_marginal M hM rows.A cols.P rows.properA n,
    cells_fibre_marginal M hM rows.B cols.P rows.properB n,
    columnPair_fixed_conditional M hM rows.A rows.P rows.B cols.P rr.cardP cols.properP n,
    columnPair_fixed_conditional M hM rows.B rows.P rows.A cols.P rt.cardP cols.properP n,
    columnPair_fixed_marginals M hM rows.A rows.P rows.B cols.P rr.cardP cols.properP
      rows.properP rows.properB rows.disjointPA.symm rows.disjointAB
      (by simpa [Finset.union_comm] using rows.properPA) rows.properAB n,
    columnPair_fixed_marginals M hM rows.B rows.P rows.A cols.P rt.cardP cols.properP
      rows.properP rows.properA rows.disjointPB.symm rows.disjointAB.symm
      (by simpa [Finset.union_comm] using rows.properPB)
      (by simpa [Finset.union_comm] using rows.properAB) n] with e hq hp hs ht hκ hξ hmκ hmξ
  intro hr hst g h
  rw [hs.map_eq] at hmκ
  rw [ht.map_eq] at hmξ
  simp only [fibreColumnEdge_eq] at hq hp
  let hts : MeasurePreserving (fun y => (cells M rows.B cols.P n y,cells M rows.A cols.P n y))
      (M.ownKernel (n+2) e) ((cellLaw M rows.B cols.P n e).prod (cellLaw M rows.A cols.P n e)) :=
    Measure.measurePreserving_swap.comp hst
  apply JoiningOperator.contraction_projection_both hr hst hts _ _ _
  · intro g h
    exact JoiningOperator.contraction_projection hs hr hst hκ hmκ _ _ hq g h
  · intro h g
    exact JoiningOperator.contraction_projection ht hr hts hξ hmξ _ _ hp h g

end

universe u

end ArrayObjects.Object.Rolled


end Rokhlin

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_column_contraction_projection_oai.{u} := @OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_column_contraction_projection_oai.{u}
