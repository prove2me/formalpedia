-- Prove2me | solution 1 for OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_active_to_column_exact
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:56:14.297953+00:00
-- url     : https://prove2.me/submissions/5fb439ae-cf5f-4841-9c24-93ae623e72eb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ3Ro002
import Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_grouped_exact_split_span

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
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

attribute [local instance] OAI.Rokhlin.instMeasurableSpaceCircle_circleLp
lemma circleLp_congr {f g : X → Circle} (hf : Measurable f) (hg : Measurable g)
    (he : f =ᵐ[μ] g) : circleLp μ f hf = circleLp μ g hg := by
  apply Lp.ext
  filter_upwards [circleLp_coe μ f hf, circleLp_coe μ g hg,he] with x h1 h2 h3
  rw [h1,h2,h3]

lemma circleLp_inner (f g : X → Circle) (hf : Measurable f) (hg : Measurable g) :
    inner ℂ (circleLp μ f hf) (circleLp μ g hg) =
      ∫ x, conj (f x : ℂ) * (g x : ℂ) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [circleLp_coe μ f hf,circleLp_coe μ g hg] with x h1 h2
  rw [h1,h2]
  simp only [RCLike.inner_apply,starRingEnd_apply]
  ring

attribute [local instance] OAI.Rokhlin.instBorelSpaceCircle_circleLp
lemma circleLp_phase (c : Circle) (f : X → Circle) (hf : Measurable f) :
    circleLp μ (fun x => c*f x) (measurable_const.mul hf) = (c : ℂ) • circleLp μ f hf := by
  apply Lp.ext
  filter_upwards [circleLp_coe μ (fun x => c*f x) (measurable_const.mul hf),
    circleLp_coe μ f hf,Lp.coeFn_smul (c : ℂ) (circleLp μ f hf)] with x h1 h2 h3
  rw [h1,h3]
  change (c : ℂ) * (f x : ℂ) = (c : ℂ) * (circleLp μ f hf x)
  rw [h2]
end

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

end ArrayObjects.Object

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
variable {I Ω Y : Type*} [MeasurableSpace Y]

lemma field_finset_observation (f : I → Ω → Y) (s : Finset I) :
    MeasurableSpace.comap (fun ω (i : s) => f i ω) inferInstance =
      ⨆ i ∈ s, MeasurableSpace.comap (f i) inferInstance := by
  rw [MeasurableSpace.comap_process_pi]
  simp only [iSup_subtype]

lemma field_pair_finset_union [DecidableEq I] (f : I → Ω → Y) (s t : Finset I) :
    MeasurableSpace.comap (fun ω => ((fun (i : s) => f i ω),(fun (i : t) => f i ω))) inferInstance =
      MeasurableSpace.comap (fun ω (i : ↥(s ∪ t)) => f i ω) inferInstance := by
  change ((inferInstance : MeasurableSpace (s → Y)).prod (inferInstance : MeasurableSpace (t → Y))).comap _ = _
  rw [MeasurableSpace.comap_prodMk,field_finset_observation,field_finset_observation,field_finset_observation]
  simp only [Finset.mem_union,iSup_or]
  rw [iSup_sup_eq]

lemma field_finset_grid {J : Type*} (f : I → J → Ω → Y) (s : Finset I) (t : Finset J) :
    MeasurableSpace.comap (fun ω (i : s) (j : t) => f i j ω) inferInstance =
      ⨆ i ∈ s, ⨆ j ∈ t, MeasurableSpace.comap (f i j) inferInstance := by
  rw [MeasurableSpace.comap_process_pi]
  simp_rw [MeasurableSpace.comap_process_pi]
  simp only [iSup_subtype]

lemma field_grid_pair_inner_union {J : Type*} [DecidableEq J]
    (f : I → J → Ω → Y) (r : Finset I) (s t : Finset J) :
    MeasurableSpace.comap (fun ω => ((fun (i : r) (j : s) => f i j ω),
      (fun (i : r) (j : t) => f i j ω))) inferInstance =
      MeasurableSpace.comap (fun ω (i : r) (j : ↥(s ∪ t)) => f i j ω) inferInstance := by
  change ((inferInstance : MeasurableSpace (r → s → Y)).prod (inferInstance : MeasurableSpace (r → t → Y))).comap _ = _
  rw [MeasurableSpace.comap_prodMk,field_finset_grid,field_finset_grid,field_finset_grid]
  simp only [Finset.mem_union,iSup_or]
  simp only [iSup_sup_eq]
end

section
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace ComplementSplit
variable {P : Finset I}

lemma union_eq (s : ComplementSplit P) : s.A ∪ s.B = Pᶜ := by
  ext i
  constructor
  · intro hi
    refine Finset.mem_compl.mpr (fun hip => ?_)
    rcases Finset.mem_union.mp hi with h | h
    · exact Finset.disjoint_left.mp s.disjointPA hip h
    · exact Finset.disjoint_left.mp s.disjointPB hip h
  · intro hi
    have hp : i ∉ P := Finset.mem_compl.mp hi
    have hu : i ∈ P ∪ s.A ∪ s.B := s.cover ▸ Finset.mem_univ i
    simpa only [Finset.mem_union,hp,false_or] using hu

end ComplementSplit
end

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

lemma rowActive_complement_invariant (hM : M.IsSaturated) (P R : Finset I)
    (hP : P ≠ Finset.univ) (s t : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      rowActive M P R s.A s.B n e = rowActive M P R t.A t.B n e := by
  filter_upwards [rowActive_eq_range M hM P hP s.partition n,
    rowActive_eq_range M hM P hP t.partition n,
    cells_fibre_marginal M hM P R hP n,
    cells_fibre_marginal M hM P s.A hP n,cells_fibre_marginal M hM P s.B hP n,
    cells_fibre_marginal M hM P t.A hP n,cells_fibre_marginal M hM P t.B hP n,
    cells_indep_columns_fibre M P P s.A s.B s.disjointAB s.partition.properAB n,
    cells_indep_columns_fibre M P P t.A t.B t.disjointAB t.partition.properAB n]
      with e hs ht hz hsa hsb hta htb his hit
  let hS := cells_pair_preserving M hsa hsb his
  let hT := cells_pair_preserving M hta htb hit
  rw [hs hz hS,ht hz hT]
  apply JoiningOperator.active_observation_eq hz hS hT
  change MeasurableSpace.comap (fun y => ((fun (j : s.A) (a : P) => missingRow M n j a y),
    (fun (j : s.B) (a : P) => missingRow M n j a y))) inferInstance =
    MeasurableSpace.comap (fun y => ((fun (j : t.A) (a : P) => missingRow M n j a y),
    (fun (j : t.B) (a : P) => missingRow M n j a y))) inferInstance
  rw [field_pair_finset_union (fun j y (a : P) => missingRow M n j a y) s.A s.B,
    field_pair_finset_union (fun j y (a : P) => missingRow M n j a y) t.A t.B,s.union_eq,t.union_eq]

lemma columnActive_complement_invariant (hM : M.IsSaturated) (P R : Finset I)
    (hR : R ≠ Finset.univ) (s t : ComplementSplit P) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      columnActive M P s.A s.B R n e = columnActive M P t.A t.B R n e := by
  filter_upwards [columnActive_eq_range M hM s.partition R hR n,
    columnActive_eq_range M hM t.partition R hR n,
    cells_fibre_marginal M hM P R s.partition.properP n,
    cells_fibre_marginal M hM s.A R s.partition.properA n,
    cells_fibre_marginal M hM s.B R s.partition.properB n,
    cells_fibre_marginal M hM t.A R t.partition.properA n,
    cells_fibre_marginal M hM t.B R t.partition.properB n,
    cells_indep_rows_fibre M hM s.A s.B R R s.disjointAB s.partition.properAB n,
    cells_indep_rows_fibre M hM t.A t.B R R t.disjointAB t.partition.properAB n]
      with e hs ht hz hsa hsb hta htb his hit
  let hS := cells_pair_preserving M hsa hsb his
  let hT := cells_pair_preserving M hta htb hit
  rw [hs hz hS,ht hz hT]
  apply JoiningOperator.active_observation_eq hz hS hT
  change MeasurableSpace.comap (fun y => ((fun (j : R) (a : s.A) => missingRow M n j a y),
    (fun (j : R) (a : s.B) => missingRow M n j a y))) inferInstance =
    MeasurableSpace.comap (fun y => ((fun (j : R) (a : t.A) => missingRow M n j a y),
    (fun (j : R) (a : t.B) => missingRow M n j a y))) inferInstance
  rw [field_grid_pair_inner_union,field_grid_pair_inner_union,s.union_eq,t.union_eq]

lemma commonActive_complement_invariant (hM : M.IsSaturated) (P R : Finset I)
    (s s' : ComplementSplit P) (t t' : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      commonActive M P s.A s.B R t.A t.B n e = commonActive M P s'.A s'.B R t'.A t'.B n e := by
  filter_upwards [rowActive_complement_invariant M hM P R s.partition.properP t t' n,
    columnActive_complement_invariant M hM P R t.partition.properP s s' n] with e hr hc
  exact congrArg₂ (· ⊓ ·) hr hc
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
attribute [local instance] OAI.Rokhlin.instMeasurableSpaceCircle_solutions_3
local instance instBorelSpaceCircle_solutions_3 : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))
variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {x : Ω → X} {y : Ω → Y} {z : Ω → Z}

lemma ternary_unit_const_of_nonzero_mean
    (f : Z → Circle) (g : X → Circle) (h : Y → Circle)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hx : AEMeasurable x μ) (hy : AEMeasurable y μ) (hz : AEMeasurable z μ)
    (hxy : IndepFun x y μ) (hxz : IndepFun x z μ) (hyz : IndepFun y z μ)
    (he : ∀ᵐ ω ∂μ, f (z ω) = g (x ω) * h (y ω))
    (hne : (∫ ω, (f (z ω) : ℂ) ∂μ) ≠ 0) :
    ∃ a : Circle, ∀ᵐ ω ∂μ, f (z ω) = a := by
  let F := fun ω => (f (z ω) : ℂ)
  let G := fun ω => (g (x ω) : ℂ)
  let H := fun ω => (h (y ω) : ℂ)
  have hf' : Measurable (fun q => (f q : ℂ)) := measurable_subtype_coe.comp hf
  have hg' : Measurable (fun q => (g q : ℂ)) := measurable_subtype_coe.comp hg
  have hh' : Measurable (fun q => (h q : ℂ)) := measurable_subtype_coe.comp hh
  have hfm : AEStronglyMeasurable F μ := (hf'.comp_aemeasurable hz).aestronglyMeasurable
  have hgm : AEStronglyMeasurable G μ := (hg'.comp_aemeasurable hx).aestronglyMeasurable
  have hhm : AEStronglyMeasurable H μ := (hh'.comp_aemeasurable hy).aestronglyMeasurable
  have heF : F =ᵐ[μ] fun ω => G ω * H ω := he.mono fun ω hω => congrArg ((↑) : Circle → ℂ) hω
  have heG : G =ᵐ[μ] fun ω => F ω * conj (H ω) := by
    filter_upwards [heF] with ω hω
    rw [hω, mul_assoc,←Complex.inv_eq_conj (Circle.norm_coe _),mul_inv_cancel₀ (Circle.coe_ne_zero _),mul_one]
  have heH : H =ᵐ[μ] fun ω => F ω * conj (G ω) := by
    filter_upwards [heF] with ω hω
    rw [hω,mul_comm (G ω),mul_assoc,←Complex.inv_eq_conj (Circle.norm_coe _),mul_inv_cancel₀ (Circle.coe_ne_zero _),mul_one]
  have ha : ‖∫ ω, F ω ∂μ‖ = ‖∫ ω, G ω ∂μ‖ * ‖∫ ω, H ω ∂μ‖ := by
    rw [integral_congr_ae heF,show (∫ ω, G ω * H ω ∂μ) = (∫ ω, G ω ∂μ) * (∫ ω, H ω ∂μ) from (hxy.comp hg' hh').integral_fun_mul_eq_mul_integral hgm hhm,norm_mul]
  have hb : ‖∫ ω, G ω ∂μ‖ = ‖∫ ω, F ω ∂μ‖ * ‖∫ ω, H ω ∂μ‖ := by
    rw [integral_congr_ae heG,show (∫ ω, F ω * conj (H ω) ∂μ) = (∫ ω, F ω ∂μ) * (∫ ω, conj (H ω) ∂μ) from (hyz.symm.comp hf' (Complex.continuous_conj.measurable.comp hh')).integral_fun_mul_eq_mul_integral hfm hhm.star,
      integral_conj,norm_mul,Complex.norm_conj]
  have hc : ‖∫ ω, H ω ∂μ‖ = ‖∫ ω, F ω ∂μ‖ * ‖∫ ω, G ω ∂μ‖ := by
    rw [integral_congr_ae heH,show (∫ ω, F ω * conj (G ω) ∂μ) = (∫ ω, F ω ∂μ) * (∫ ω, conj (G ω) ∂μ) from (hxz.symm.comp hf' (Complex.continuous_conj.measurable.comp hg')).integral_fun_mul_eq_mul_integral hfm hgm.star,
      integral_conj,norm_mul,Complex.norm_conj]
  have hA : 0 < ‖∫ ω, F ω ∂μ‖ := norm_pos_iff.mpr hne
  have hB : 0 ≤ ‖∫ ω, G ω ∂μ‖ := norm_nonneg _
  have hC : 0 ≤ ‖∫ ω, H ω ∂μ‖ := norm_nonneg _
  have hBpos : 0 < ‖∫ ω, G ω ∂μ‖ := by nlinarith [ha]
  have hCone : ‖∫ ω, H ω ∂μ‖ = 1 := by nlinarith [ha,hb]
  have hBone : ‖∫ ω, G ω ∂μ‖ = 1 := by nlinarith [ha,hc,hCone]
  have hAone : ‖∫ ω, F ω ∂μ‖ = 1 := by rw [ha,hBone,hCone,mul_one]
  let a : Circle := ⟨∫ ω, F ω ∂μ, by exact mem_sphere_zero_iff_norm.mpr hAone⟩
  have hconst := ae_eq_mean_of_norm_mean_eq_one F
    (Filter.Eventually.of_forall fun ω => Circle.norm_coe _) hAone
  exact ⟨a,hconst.mono fun _ ht => Circle.ext ht⟩

lemma ternary_line_dichotomy
    (f f' : Z → Circle) (g g' : X → Circle) (h h' : Y → Circle)
    (hf : Measurable f) (hf' : Measurable f')
    (hg : Measurable g) (hg' : Measurable g') (hh : Measurable h) (hh' : Measurable h')
    (hx : AEMeasurable x μ) (hy : AEMeasurable y μ) (hz : AEMeasurable z μ)
    (hxy : IndepFun x y μ) (hxz : IndepFun x z μ) (hyz : IndepFun y z μ)
    (he : ∀ᵐ ω ∂μ, f (z ω) = g (x ω) * h (y ω))
    (he' : ∀ᵐ ω ∂μ, f' (z ω) = g' (x ω) * h' (y ω)) :
    (∫ ω, (f (z ω) : ℂ) * conj (f' (z ω) : ℂ) ∂μ) = 0 ∨
      ∃ a : Circle, ∀ᵐ ω ∂μ, f (z ω) = a * f' (z ω) := by
  by_cases hn : (∫ ω, (f (z ω) : ℂ) * conj (f' (z ω) : ℂ) ∂μ) = 0
  · exact Or.inl hn
  right
  have hp : ∀ᵐ ω ∂μ, f (z ω)*(f' (z ω))⁻¹ =
      (g (x ω)*(g' (x ω))⁻¹) * (h (y ω)*(h' (y ω))⁻¹) := by
    filter_upwards [he,he'] with ω hω hω'
    rw [hω,hω',mul_inv_rev]
    ac_rfl
  obtain ⟨a,ha⟩ := ternary_unit_const_of_nonzero_mean
    (fun q => f q*(f' q)⁻¹) (fun q => g q*(g' q)⁻¹) (fun q => h q*(h' q)⁻¹)
    (hf.mul hf'.inv) (hg.mul hg'.inv) (hh.mul hh'.inv) hx hy hz hxy hxz hyz hp
    (by simpa only [Circle.coe_mul,Circle.coe_inv_eq_conj] using hn)
  exact ⟨a,ha.mono fun _ he => mul_inv_eq_iff_eq_mul.mp he⟩
end

namespace JoiningOperator
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {Ω Z X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure Ω) (η : Measure Z) [IsFiniteMeasure η]
  (x : Ω → X) (y : Ω → Y) (z : Ω → Z)

lemma smul_mem_splitExact (c : ℂ) {v : Lp ℂ 2 η} (hv : v ∈ splitExact μ η x y z) :
    c • v ∈ splitExact μ η x y z := by
  obtain ⟨f,g,h,hf,hg,hh,d,hv,he⟩ := hv
  exact ⟨f,g,h,hf,hg,hh,c*d,by rw [hv,mul_smul],he⟩

lemma circle_mem_splitExact (f : Z → Circle) (g : X → Circle) (h : Y → Circle)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (he : ∀ᵐ ω ∂μ, f (z ω) = g (x ω) * h (y ω)) :
    circleLp η f hf ∈ splitExact μ η x y z :=
  ⟨f,g,h,hf,hg,hh,1,(one_smul _ _).symm,he⟩

variable {μ η x y z}

lemma circleLp_dichotomy [IsProbabilityMeasure μ]
    (hz : MeasurePreserving z μ η) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hxy : IndepFun x y μ) (hxz : IndepFun x z μ) (hyz : IndepFun y z μ)
    (f f' : Z → Circle) (g g' : X → Circle) (h h' : Y → Circle)
    (hf : Measurable f) (hf' : Measurable f')
    (hg : Measurable g) (hg' : Measurable g') (hh : Measurable h) (hh' : Measurable h')
    (he : ∀ᵐ ω ∂μ, f (z ω) = g (x ω) * h (y ω))
    (he' : ∀ᵐ ω ∂μ, f' (z ω) = g' (x ω) * h' (y ω)) :
    inner ℂ (circleLp η f hf) (circleLp η f' hf') = 0 ∨
      ∃ a : Circle, circleLp η f hf = (a : ℂ) • circleLp η f' hf' := by
  rcases ternary_line_dichotomy f f' g g' h h' hf hf' hg hg' hh hh' hx hy hz.measurable.aemeasurable
    hxy hxz hyz he he' with ho | ⟨a,ha⟩
  · left
    apply inner_eq_zero_symm.mp
    rw [circleLp_inner]
    have hi : (∫ v, conj (f' v : ℂ) * (f v : ℂ) ∂η) =
        ∫ ω, conj (f' (z ω) : ℂ) * (f (z ω) : ℂ) ∂μ :=
      by
        rw [←hz.map_eq]
        exact integral_map hz.measurable.aemeasurable (by fun_prop)
    rw [hi]
    simpa only [mul_comm] using ho
  · right
    have ha' : f =ᵐ[η] fun v => a*f' v := by
      rw [←hz.map_eq]
      exact (ae_map_iff hz.measurable.aemeasurable
        (measurableSet_eq_fun hf (measurable_const.mul hf'))).mpr ha
    exact ⟨a,(circleLp_congr η hf (measurable_const.mul hf') ha').trans (circleLp_phase η a f' hf')⟩

lemma splitExact_dichotomy [IsProbabilityMeasure μ]
    (hz : MeasurePreserving z μ η) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hxy : IndepFun x y μ) (hxz : IndepFun x z μ) (hyz : IndepFun y z μ)
    {v w : Lp ℂ 2 η} (hv : v ∈ splitExact μ η x y z) (hw : w ∈ splitExact μ η x y z) :
    inner ℂ v w = 0 ∨ ∃ c : ℂ, v = c • w := by
  obtain ⟨f,g,h,hf,hg,hh,c,rfl,he⟩ := hv
  obtain ⟨f',g',h',hf',hg',hh',d,rfl,he'⟩ := hw
  rcases circleLp_dichotomy hz hx hy hxy hxz hyz f f' g g' h h' hf hf' hg hg' hh hh' he he'
    with ho | ⟨a,ha⟩
  · left
    simp only [inner_smul_left,inner_smul_right,ho,mul_zero]
  · by_cases hd : d = 0
    · left
      simp only [hd,zero_smul,inner_zero_right]
    · right
      refine ⟨c*(a : ℂ)*d⁻¹,?_⟩
      rw [ha,smul_smul,smul_smul,mul_assoc,mul_assoc,inv_mul_cancel₀ hd,mul_one]

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
open scoped InnerProductSpace
variable {H A B : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma nonzero_inner_in_closedSpan (S : Set H) (v : H) (hv : v ≠ 0)
    (hmem : v ∈ (Submodule.span ℂ S).topologicalClosure) :
    ∃ w ∈ S, inner ℂ v w ≠ 0 := by
  by_contra! h
  have ho : v ∈ (Submodule.span ℂ S)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact h w hw
    | zero => simp
    | add x y hx hy ihx ihy => simp only [inner_add_right,ihx,ihy,add_zero]
    | smul c x hx ih => simp only [inner_smul_right,ih,mul_zero]
  have ht : v ∈ ((Submodule.span ℂ S).topologicalClosure)ᗮ := by
    simpa only [Submodule.orthogonal_closure] using ho
  exact hv (inner_self_eq_zero.mp (((Submodule.mem_orthogonal' _ v).mp ht) v hmem))

end

namespace ArrayObjects.Object.Rolled

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma rowSplitExact_dichotomy (hM : M.IsSaturated) (P R : Finset I) (hP : P ≠ Finset.univ)
    (s : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ v ∈ rowSplitExact M P R s n e, ∀ w ∈ rowSplitExact M P R s n e,
        inner ℂ v w = 0 ∨ ∃ c : ℂ, v = c • w := by
  filter_upwards [cells_fibre_marginal M hM P R hP n,
    cells_indep_columns_fibre M P P s.A s.B s.disjointAB s.partition.properAB n,
    cells_indep_columns_fibre M P P s.A R s.disjointPA.symm
      (by simpa only [Finset.union_comm] using s.partition.properPA) n,
    cells_indep_columns_fibre M P P s.B R s.disjointPB.symm
      (by simpa only [Finset.union_comm] using s.partition.properPB) n] with e hz hxy hxz hyz
  exact fun v hv w hw => JoiningOperator.splitExact_dichotomy hz
    (measurable_cells M P s.A n).aemeasurable (measurable_cells M P s.B n).aemeasurable hxy hxz hyz hv hw

omit [DecidableEq I] in
lemma proper_columns_product (P S : Finset I) (hS : S ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      MeasurePreserving (fun y (j : S) => oneColumn M P n j y) (M.ownKernel (n+2) e)
        (Measure.pi (fun j : S => columnCellLaw M P n e j)) := by
  have hp := ConditionalFibres.marginal (measurable_planes (n+1) S)
    (M.ownKernel_conditional (n+2)) (M.planes_conditional (n+1) S hS)
  filter_upwards [hp] with e he
  have hg := measurePreserving_pi
    (fun j : S => M.ownKernel (n+1) (plane (n+1) (Fin.last (n+1)) j e))
    (fun j : S => columnCellLaw M P n e j)
    (f := fun _ y (i : P) => plane n 0 i y)
    (fun _ => MeasurePreserving.mk (by fun_prop) rfl)
  have hm := hg.comp he
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext y j i
  exact (congrFun (plane_first_last M n i j) y).symm

lemma proper_rows_product (hM : M.IsSaturated) (R A : Finset I) (hA : A ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      MeasurePreserving (fun y (i : A) => oneRow M R n i y) (M.ownKernel (n+2) e)
        (Measure.pi (fun i : A => rowCellLaw M R n e i)) := by
  have hp := ConditionalFibres.marginal (measurable_parents M A (n+1))
    (M.ownKernel_conditional (n+2)) (rows_conditional M hM A hA n)
  filter_upwards [hp] with e he
  have hg := measurePreserving_pi
    (fun i : A => M.ownKernel (n+1) (plane (n+1) 0 i e))
    (fun i : A => rowCellLaw M R n e i)
    (f := fun _ y (j : R) => plane n (Fin.last n) j y)
    (fun _ => MeasurePreserving.mk (by fun_prop) rfl)
  exact hg.comp he
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I A B : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace A]
  (μ : I → Measure A) [∀ i, IsProbabilityMeasure (μ i)]

lemma measurePreserving_hybrid (s : Finset I) :
    MeasurePreserving (hybrid s) (Measure.pi (fun i => (μ i).prod (μ i))) (Measure.pi μ) := by
  exact measurePreserving_pi (fun i => (μ i).prod (μ i)) μ (f := fun i p => if i ∈ s then p.1 else p.2) (by
  intro i
  by_cases hi : i ∈ s
  · simpa only [hybrid,hi,ite_true] using
      (measurePreserving_fst (μ := μ i) (ν := μ i))
  · simpa only [hybrid,hi,ite_false] using
      (measurePreserving_snd (μ := μ i) (ν := μ i)))

lemma ae_eq_const_of_omit (f : (I → A) → B)
    (g : ∀ i, (({j : I // j ≠ i}) → A) → B)
    (h : ∀ i, ∀ᵐ x ∂Measure.pi μ, f x = g i (fun j => x j)) :
    ∃ b, ∀ᵐ x ∂Measure.pi μ, f x = b := by
  have hh (s : Finset I) : ∀ᵐ x ∂Measure.pi (fun i => (μ i).prod (μ i)),
      f (hybrid s x) = f (hybrid ∅ x) := by
    induction s using Finset.induction_on with
    | empty => exact Filter.Eventually.of_forall fun _ => rfl
    | @insert i s hi hs =>
      filter_upwards [(measurePreserving_hybrid μ (insert i s)).quasiMeasurePreserving.ae (h i),
        (measurePreserving_hybrid μ s).quasiMeasurePreserving.ae (h i),hs] with x h1 h2 h3
      rw [h1,←h3,h2]
      congr 1
      funext j
      simp only [hybrid,Finset.mem_insert, j.property, false_or]
  have he : ∀ᵐ x ∂(Measure.pi μ).prod (Measure.pi μ), f x.1 = f x.2 := by
    have hp := (measurePreserving_arrowProdEquivProdArrow A A I μ μ).symm
        (MeasurableEquiv.arrowProdEquivProdArrow A A I)
    filter_upwards [hp.quasiMeasurePreserving.ae (hh Finset.univ)] with x hx
    change f (fun i => if i ∈ Finset.univ then x.1 i else x.2 i) =
      f (fun i => if i ∈ (∅ : Finset I) then x.1 i else x.2 i) at hx
    simpa only [Finset.mem_univ,ite_true,Finset.notMem_empty,ite_false] using hx
  obtain ⟨x,hx⟩ := (Measure.ae_ae_of_ae_prod he).exists
  exact ⟨f x,hx.mono fun _ he => he.symm⟩

lemma pure_product_of_singleton_splits {G : Type*} [CommGroup G]
    (f : (I → A) → G) (a : I → A → G)
    (b : ∀ i, (({j : I // j ≠ i}) → A) → G)
    (h : ∀ i, ∀ᵐ x ∂Measure.pi μ, f x = a i (x i) * b i (fun j => x j)) :
    ∃ c, ∀ᵐ x ∂Measure.pi μ, f x = c * ∏ i, a i (x i) := by
  let F (x : I → A) := f x * (∏ i, a i (x i))⁻¹
  let B (i : I) (x : ({j : I // j ≠ i}) → A) :=
    b i x * (∏ j : ({j : I // j ≠ i}), a j (x j))⁻¹
  have hi : ∀ i, ∀ᵐ x ∂Measure.pi μ, F x = B i (fun j => x j) := by
    intro i
    filter_upwards [h i] with x hx
    dsimp only [F,B]
    rw [hx,←Finset.prod_erase_mul Finset.univ (fun j => a j (x j)) (Finset.mem_univ i)]
    have hp : (∏ j : ({j : I // j ≠ i}), a j (x j)) =
        ∏ j ∈ Finset.univ.erase i, a j (x j) := by
      classical
      exact (Finset.prod_subtype (p := fun j => j ≠ i) (Finset.univ.erase i)
        (fun j => by simp only [Finset.mem_erase, Finset.mem_univ, and_true])
        (fun j => a j (x j))).symm
    rw [hp]
    simp only [mul_inv_rev]
    simp only [mul_assoc, mul_left_comm, mul_inv_cancel_left]
  obtain ⟨c,hc⟩ := ae_eq_const_of_omit μ F B hi
  refine ⟨c,hc.mono fun x hx => ?_⟩
  exact (mul_inv_eq_iff_eq_mul.mp hx)
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {Ω Z X Y : Type*} [MeasurableSpace Ω] [retained9 : MeasurableSpace Z]
    [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure Ω} {η : Measure Z} [IsProbabilityMeasure η]
    {x : Ω → X} {y : Ω → Y} {z : Ω → Z}

lemma circle_split_witness (hz : MeasurePreserving z μ η) (f : Z → Circle) (hf : Measurable f)
    (hv : circleLp η f hf ∈ JoiningOperator.splitExact μ η x y z) :
    ∃ (g : X → Circle) (h : Y → Circle), Measurable g ∧ Measurable h ∧
      ∀ᵐ ω ∂μ, f (z ω) = g (x ω) * h (y ω) := by
  obtain ⟨f',g,h,hf',hg,hh,c,hv,he⟩ := hv
  have hn : ‖c‖ = 1 := by
    have hh := congrArg norm hv
    simpa only [circleLp_norm,norm_smul,mul_one] using hh.symm
  let a : Circle := ⟨c,mem_sphere_zero_iff_norm.mpr hn⟩
  have hfg : ∀ᵐ v ∂η, f v = a*f' v := by
    filter_upwards [circleLp_coe η f hf,circleLp_coe η f' hf',Lp.coeFn_smul c (circleLp η f' hf')] with v h1 h2 h3
    apply Subtype.ext
    change (f v : ℂ) = c * (f' v : ℂ)
    rw [←h1,hv,h3]
    change c * circleLp η f' hf' v = c * (f' v : ℂ)
    rw [h2]
  refine ⟨fun u => a*g u,h,measurable_const.mul hg,hh,?_⟩
  filter_upwards [hz.quasiMeasurePreserving.ae hfg,he] with ω h1 h2
  rw [h1,h2,mul_assoc]

variable {I A : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [MeasurableSpace A]
    (ν : I → Measure A) [∀ i, IsProbabilityMeasure (ν i)]

include retained9 in
lemma full_product_of_exact_splits (u : Ω → I → A)
    (hu : MeasurePreserving u μ (Measure.pi ν)) (f : Z → Circle)
    (a : I → A → Circle) (b : ∀ i, ({j : I // j ≠ i} → A) → Circle)
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i))
    (he : ∀ i, ∀ᵐ ω ∂μ, f (z ω) = a i (u ω i) * b i (fun j => u ω j)) :
    ∃ c : Circle, ∀ᵐ ω ∂μ, f (z ω) = c * ∏ i, a i (u ω i) := by
  let _ := retained9
  let i₀ : I := Classical.choice inferInstance
  let F (v : I → A) := a i₀ (v i₀) * b i₀ (fun j => v j)
  have hF : Measurable F := (ha i₀ |>.comp (measurable_pi_apply i₀)).mul
    (hb i₀ |>.comp (Measurable.of_eval (fun _ => measurable_pi_apply _)))
  have hs : ∀ i, ∀ᵐ v ∂Measure.pi ν, F v = a i (v i) * b i (fun j => v j) := by
    intro i
    rw [←hu.map_eq]
    apply (ae_map_iff hu.measurable.aemeasurable (measurableSet_eq_fun hF
      ((ha i |>.comp (measurable_pi_apply i)).mul
        (hb i |>.comp (Measurable.of_eval (fun _ => measurable_pi_apply _)))))).mpr
    filter_upwards [he i₀,he i] with ω h0 hi
    exact h0.symm.trans hi
  obtain ⟨c,hc⟩ := pure_product_of_singleton_splits ν F a b hs
  refine ⟨c,?_⟩
  filter_upwards [he i₀,hu.quasiMeasurePreserving.ae hc] with ω h0 hc
  exact h0.trans hc
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

section
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma complement_proper {P : Finset I} (hP : P.Nonempty) : Pᶜ ≠ Finset.univ := by
  obtain ⟨i,hi⟩ := hP
  intro h
  have := Finset.mem_compl.mp (h.symm ▸ Finset.mem_univ i)
  exact this hi

lemma row_all_splits_product (hM : M.IsSaturated) (P R : Finset I)
    (s : ComplementSplit P) (t : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ (f : (R → P → Arr I M.Y n) → Circle) (hf : Measurable f),
        (∀ t' : ComplementSplit R, circleLp (cellLaw M P R n e) f hf ∈ rowSplitExact M P R t' n e) →
        ∃ (a : ↥(Rᶜ) → (P → Arr I M.Y n) → Circle) (c : Circle),
          (∀ i, Measurable (a i)) ∧ ∀ᵐ y ∂M.ownKernel (n+2) e,
            f (cells M P R n y) = c * ∏ i : ↥(Rᶜ), a i (oneColumn M P n i y) := by
  let : Nonempty ↥(Rᶜ) := Finset.Nonempty.to_subtype (by
    have := t.two_le_card_compl
    exact Finset.card_pos.mp (by omega))
  filter_upwards [cells_fibre_marginal M hM P R s.partition.properP n,
    proper_columns_product M P Rᶜ (complement_proper t.nonemptyP) n] with e hz hp
  intro f hf h
  have hw (i : ↥(Rᶜ)) := circle_split_witness hz f hf (h (t.singletonFor i))
  choose g b hg hb he using hw
  let a (i : ↥(Rᶜ)) (v : P → Arr I M.Y n) : Circle := g i (fun _ p => v p)
  let d (i : ↥(Rᶜ)) (v : {j : ↥(Rᶜ) // j ≠ i} → (P → Arr I M.Y n)) : Circle :=
    b i (fun j p => v (ComplementSplit.restIndex i j) p)
  have ha : ∀ i, Measurable (a i) := by intro i; exact (hg i).comp (by fun_prop)
  have hd : ∀ i, Measurable (d i) := by intro i; exact (hb i).comp (by fun_prop)
  have he' (i : ↥(Rᶜ)) : ∀ᵐ y ∂M.ownKernel (n+2) e,
      f (cells M P R n y) = a i (oneColumn M P n i y) * d i (fun j => oneColumn M P n j.val y) := by
    filter_upwards [he i] with y hy
    convert hy using 2
    · dsimp only [a]
      apply congrArg (g i)
      funext j p
      have hj : (j : I) = i := Finset.mem_singleton.mp j.property
      simp only [cells,oneColumn,hj]
    · rfl
  obtain ⟨c,hc⟩ := full_product_of_exact_splits (fun i : ↥(Rᶜ) => columnCellLaw M P n e i)
    (fun y (j : ↥(Rᶜ)) => oneColumn M P n j y) hp f a d ha hd he'
  exact ⟨a,c,ha,hc⟩

lemma column_all_splits_product (hM : M.IsSaturated) (P R : Finset I)
    (s : ComplementSplit P) (_t : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ (f : (R → P → Arr I M.Y n) → Circle) (hf : Measurable f),
        (∀ s' : ComplementSplit P, circleLp (cellLaw M P R n e) f hf ∈ columnSplitExact M P R s' n e) →
        ∃ (a : ↥(Pᶜ) → (R → Arr I M.Y n) → Circle) (c : Circle),
          (∀ i, Measurable (a i)) ∧ ∀ᵐ y ∂M.ownKernel (n+2) e,
            f (cells M P R n y) = c * ∏ i : ↥(Pᶜ), a i (oneRow M R n i y) := by
  let : Nonempty ↥(Pᶜ) := Finset.Nonempty.to_subtype (by
    have := s.two_le_card_compl
    exact Finset.card_pos.mp (by omega))
  filter_upwards [cells_fibre_marginal M hM P R s.partition.properP n,
    proper_rows_product M hM R Pᶜ (complement_proper s.nonemptyP) n] with e hz hp
  intro f hf h
  have hw (i : ↥(Pᶜ)) := circle_split_witness hz f hf (h (s.singletonFor i))
  choose g b hg hb he using hw
  let a (i : ↥(Pᶜ)) (v : R → Arr I M.Y n) : Circle := g i (fun j _ => v j)
  let d (i : ↥(Pᶜ)) (v : {j : ↥(Pᶜ) // j ≠ i} → (R → Arr I M.Y n)) : Circle :=
    b i (fun p j => v (ComplementSplit.restIndex i j) p)
  have ha : ∀ i, Measurable (a i) := by intro i; exact (hg i).comp (by fun_prop)
  have hd : ∀ i, Measurable (d i) := by intro i; exact (hb i).comp (by fun_prop)
  have he' (i : ↥(Pᶜ)) : ∀ᵐ y ∂M.ownKernel (n+2) e,
      f (cells M P R n y) = a i (oneRow M R n i y) * d i (fun j => oneRow M R n j.val y) := by
    filter_upwards [he i] with y hy
    convert hy using 2
    · dsimp only [a]
      apply congrArg (g i)
      funext p j
      have hj : (j : I) = i := Finset.mem_singleton.mp j.property
      simp only [cells,oneRow,hj]
    · rfl
  obtain ⟨c,hc⟩ := full_product_of_exact_splits (fun i : ↥(Pᶜ) => rowCellLaw M R n e i)
    (fun y (j : ↥(Pᶜ)) => oneRow M R n j y) hp f a d ha hd he'
  exact ⟨a,c,ha,hc⟩
end

attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma zero_mem_fullExact (P R : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    (0 : Lp ℂ 2 (cellLaw M P R n e)) ∈ fullExact M P R n e := by
  refine ⟨1,measurable_const,0,by simp,?_,?_⟩ <;>
    exact ⟨1,1,fun _ => measurable_const,Filter.Eventually.of_forall (by intro y; simp)⟩

lemma allSplitExact_subset_fullExact (hM : M.IsSaturated) (P R : Finset I)
    (s : ComplementSplit P) (t : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      allSplitExact M P R n e ⊆ fullExact M P R n e := by
  filter_upwards [row_all_splits_product M hM P R s t n,column_all_splits_product M hM P R s t n]
    with e hr hc
  intro v hv
  obtain ⟨f,g,h,hf,hg,hh,c,hv',he⟩ := hv.1 t
  by_cases hz : c = 0
  · rw [hz,zero_smul] at hv'
    rw [hv']
    exact zero_mem_fullExact M P R n e
  have hrow : ∀ t' : ComplementSplit R, circleLp (cellLaw M P R n e) f hf ∈ rowSplitExact M P R t' n e := by
    intro t'
    have h := JoiningOperator.smul_mem_splitExact _ _ _ _ _ c⁻¹ (hv.1 t')
    rwa [hv',smul_smul,inv_mul_cancel₀ hz,one_smul] at h
  have hcol : ∀ s' : ComplementSplit P, circleLp (cellLaw M P R n e) f hf ∈ columnSplitExact M P R s' n e := by
    intro s'
    have h := JoiningOperator.smul_mem_splitExact _ _ _ _ _ c⁻¹ (hv.2 s')
    rwa [hv',smul_smul,inv_mul_cancel₀ hz,one_smul] at h
  exact ⟨f,hf,c,hv',hr f hf hrow,hc f hf hcol⟩

end ArrayObjects.Object.Rolled

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

namespace ArrayObjects.Object.Rolled

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma grouped_full_row_column_exact (hM : M.IsSaturated) (P R : Finset I)
    (s : ComplementSplit P) (t : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂M.parameterLaw (n+2), ∀ v,
      (∀ t' : ComplementSplit R, v ∈ rowSplitExact M P R t' n e) →
      v ∈ columnActive M P s.A s.B R n e → v ∈ fullExact M P R n e := by
  have hspans := ae_all_iff.mpr fun s' : ComplementSplit P => grouped_exact_split_span M hM P R s' t n
  have hinvs := ae_all_iff.mpr fun s' : ComplementSplit P =>
    commonActive_complement_invariant M hM P R s' s t t n
  filter_upwards [hspans,hinvs,rowSplitExact_dichotomy M hM P R s.partition.properP t n,
    allSplitExact_subset_fullExact M hM P R s t n,
    rowActive_eq_range M hM P s.partition.properP t.partition n,
    cells_fibre_marginal M hM P R s.partition.properP n,
    cells_fibre_marginal M hM P t.A s.partition.properP n,
    cells_fibre_marginal M hM P t.B s.partition.properP n,
    cells_indep_columns_fibre M P P t.A t.B t.disjointAB t.partition.properAB n]
    with e hspan hinv horth hfull hr hz ha hb hab
  intro v hrow hcol
  by_cases hv0 : v = 0
  · subst v
    exact zero_mem_fullExact M P R n e
  have hactive : v ∈ rowActive M P R t.A t.B n e := by
    let hpair := cells_pair_preserving M ha hb hab
    rw [hr hz hpair]
    exact JoiningOperator.splitExact_le_active hz hpair (hrow t)
  apply hfull
  refine ⟨hrow,?_⟩
  intro s'
  have hv : v ∈ (Submodule.span ℂ (rowSplitExact M P R t n e ∩
      columnSplitExact M P R s' n e)).topologicalClosure := by
    rw [hspan s',hinv s']
    exact ⟨hactive,hcol⟩
  obtain ⟨w,hw,hn⟩ := nonzero_inner_in_closedSpan _ v hv0 hv
  obtain ⟨c,hc⟩ := (horth v (hrow t) w hw.1).resolve_left hn
  rw [hc]
  exact JoiningOperator.smul_mem_splitExact _ _ _ _ _ c hw.2
end ArrayObjects.Object.Rolled

namespace JoiningOperator
open MeasureTheory
variable {Ω Ω' X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Ω} {μ' : Measure Ω'} {ν : Measure X}
  {f : Ω' → Ω} {x : Ω → X} {y : Ω → Y}

lemma measurePreserving_of_comp (hf : MeasurePreserving f μ' μ) (hx : Measurable x)
    (hxf : MeasurePreserving (x ∘ f) μ' ν) : MeasurePreserving x μ ν := by
  refine ⟨hx,?_⟩
  rw [←hf.map_eq,Measure.map_map hx hf.measurable]
  exact hxf.map_eq

end JoiningOperator

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in
lemma cells_field (A J : Finset I) (n : ℕ) :
    MeasurableSpace.comap (cells M A J n) inferInstance =
      ⨆ j ∈ J, ⨆ a ∈ A, MeasurableSpace.comap (missingRow M n j a) inferInstance := by
  exact field_finset_grid (fun j a y => missingRow M n j a y) J A

end ArrayObjects.Object.Rolled

namespace JoiningOperator
open MeasureTheory ContinuousLinearMap
variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {τ : Measure Z}
  {x : Ω → X} {y : Ω → Y}

omit [MeasurableSpace Ω] [MeasurableSpace Y] in
lemma pullEquiv_coe (e : X ≃ᵐ Z) (he : MeasurePreserving e ν τ) :
    (pullEquiv e he : Lp ℂ 2 τ →L[ℂ] Lp ℂ 2 ν) = pull he := rfl

lemma operator_reparam (e : X ≃ᵐ Z) (he : MeasurePreserving e ν τ)
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ) :
    pull he ∘L operator (he.comp hx) hy = operator hx hy := by
  have hh : pull he ∘L (pull he).adjoint = ContinuousLinearMap.id ℂ (Lp ℂ 2 ν) := by
    rw [←pullEquiv_coe e he]
    rw [LinearIsometryEquiv.adjoint_eq_symm]
    apply ContinuousLinearMap.ext
    intro f
    exact (pullEquiv e he).apply_symm_apply f
  calc
    pull he ∘L operator (he.comp hx) hy =
        (pull he ∘L (pull he).adjoint) ∘L operator hx hy := by
      unfold operator
      rw [pull_comp hx he,adjoint_comp]
      simp only [comp_assoc]
    _ = operator hx hy := by rw [hh,id_comp]

lemma active_reparam (e : X ≃ᵐ Z) (he : MeasurePreserving e ν τ)
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ) (v : Lp ℂ 2 τ) :
    v ∈ (LinearMap.range (operator (he.comp hx) hy).toLinearMap).topologicalClosure ↔
    pull he v ∈ (LinearMap.range (operator hx hy).toLinearMap).topologicalClosure := by
  let E := pullEquiv e he
  have hr : E '' Set.range (operator (he.comp hx) hy) = Set.range (operator hx hy) := by
    rw [←Set.range_comp]
    have hcomp := operator_reparam e he hx hy
    exact congrArg (fun f : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ν => Set.range f) hcomp
  have hc := E.toHomeomorph.image_closure (s := Set.range (operator (he.comp hx) hy))
  change E '' closure (Set.range (operator (he.comp hx) hy)) = closure (E '' Set.range (operator (he.comp hx) hy)) at hc
  rw [hr] at hc
  change v ∈ closure (Set.range (operator (he.comp hx) hy)) ↔
    E v ∈ closure (Set.range (operator hx hy))
  rw [←hc]
  constructor
  · exact fun hv => ⟨v,hv,rfl⟩
  · rintro ⟨w,hw,hwe⟩
    exact E.injective hwe ▸ hw
end JoiningOperator

section
open MeasureTheory ProbabilityTheory
section
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
lemma circleLp_pull {e : X → Y} (he : MeasurePreserving e μ ν) (f : Y → Circle) (hf : Measurable f) :
    JoiningOperator.pull he (circleLp ν f hf) = circleLp μ (f ∘ e) (hf.comp he.measurable) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (circleLp ν f hf) he,
    he.quasiMeasurePreserving.ae (circleLp_coe ν f hf),
    circleLp_coe μ (f ∘ e) (hf.comp he.measurable)] with x h1 h2 h3
  exact h1.trans (h2.trans h3.symm)
end
namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in
lemma collapse_cell_row (a j : I) : collapseCell M a j ∘ cells M {a} {j} 0 =
    plane 0 0 j ∘ plane 1 0 a := rfl
omit [DecidableEq I] in
lemma collapse_cell_column (a j : I) : collapseCell M a j ∘ cells M {a} {j} 0 =
    plane 0 0 a ∘ plane 1 (Fin.last 1) j := (plane_first_last M 0 a j).symm

lemma rawSlotActive_eq (i : I) (ν : Measure (Arr I M.Y 0)) (p : Arr I M.U 1)
    (h : MeasurePreserving (plane 0 0 i) (M.ownKernel 1 p) ν) :
    rawSlotActive M i ν p = (LinearMap.range (JoiningOperator.operator h
      (MeasurePreserving.mk (measurable_slotRest M i) rfl)).toLinearMap).topologicalClosure := by
  rw [rawSlotActive,dite_eq_left h]

lemma column_rest_field_mixed (a j : I) (s : ComplementSplit ({a} : Finset I)) :
    MeasurableSpace.comap (fun y => (cells M s.A {j} 0 y,cells M s.B {j} 0 y)) inferInstance =
      MeasurableSpace.comap (slotRest M a ∘ plane 1 (Fin.last 1) j) inferInstance := by
  change ((inferInstance : MeasurableSpace (({j} : Finset I) → s.A → Arr I M.Y 0)).prod
    (inferInstance : MeasurableSpace (({j} : Finset I) → s.B → Arr I M.Y 0))).comap _ = _
  rw [MeasurableSpace.comap_prodMk,cells_field,cells_field]
  simp only [Finset.mem_singleton,iSup_iSup_eq_left]
  have he (t : I) : missingRow M 0 j t = plane 0 0 t ∘ plane 1 (Fin.last 1) j := by
    exact (plane_first_last M 0 t j).symm
  simp_rw [he]
  have h := field_finset_observation (fun t (y : Arr I M.Y 2) => plane 0 0 t (plane 1 (Fin.last 1) j y)) (s.A ∪ s.B)
  simp only [Finset.mem_union,iSup_or,iSup_sup_eq] at h
  rw [s.union_eq] at h
  exact h.symm

lemma singleton_collapse_preserving (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I) (a j : I) :
    ∀ᵐ e ∂M.parameterLaw 2, MeasurePreserving (collapseCell M a j) (cellLaw M {a} {j} 0 e)
      (M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))) := by
  have ha : ({a} : Finset I) ≠ Finset.univ := by
    intro he
    have := congrArg Finset.card he
    simp only [Finset.card_singleton,Finset.card_univ] at this
    omega
  let hr : MeasurePreserving (plane 1 0 a) (M.parameterLaw 2) (M.parameterLaw 1) :=
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent 1 0 a⟩
  have hm := ConditionalFibres.marginal (measurable_plane 0 0 j)
    (M.ownKernel_conditional 1) (M.plane_conditional hI 0 j)
  filter_upwards [cells_fibre_marginal M hM {a} {j} ha 0,row_marginal_fibre M hM hI a,
    hr.quasiMeasurePreserving.ae hm] with e hc hr hm
  exact JoiningOperator.measurePreserving_of_comp hc (collapseCell M a j).measurable
    (by rw [collapse_cell_row]; exact hm.comp hr)

lemma columnActive_mixed_slot (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (a j : I) (hj : ({j} : Finset I) ≠ Finset.univ) (s : ComplementSplit ({a} : Finset I)) :
    ∀ᵐ e ∂M.parameterLaw 2, ∀ (ν : Measure (Arr I M.Y 0))
      (he : MeasurePreserving (collapseCell M a j) (cellLaw M {a} {j} 0 e) ν) (v : Lp ℂ 2 ν),
      v ∈ rawSlotActive M a ν (plane 1 (Fin.last 1) j e) ↔
      JoiningOperator.pull he v ∈ columnActive M {a} s.A s.B {j} 0 e := by
  filter_upwards [columnActive_eq_range M hM s.partition {j} hj 0,
    cells_fibre_marginal M hM {a} {j} s.partition.properP 0,
    cells_fibre_marginal M hM s.A {j} s.partition.properA 0,
    cells_fibre_marginal M hM s.B {j} s.partition.properB 0,
    cells_indep_rows_fibre M hM s.A s.B {j} {j} s.disjointAB s.partition.properAB 0,
    column_marginal_fibre M hI j] with e hv hx hA hB hAB hr
  intro ν he v
  let hst := cells_pair_preserving M hA hB hAB
  have hraw := he.comp hx
  rw [collapse_cell_column] at hraw
  have hs : MeasurePreserving (plane 0 0 a) (M.ownKernel 1 (plane 1 (Fin.last 1) j e)) ν :=
    JoiningOperator.measurePreserving_of_comp hr (measurable_plane _ _ _) hraw
  rw [hv hx hst,←JoiningOperator.active_reparam (collapseCell M a j) he hx hst]
  have h := JoiningOperator.active_observation_eq (he.comp hx) hst
    ((MeasurePreserving.mk (measurable_slotRest M a) rfl).comp hr) (column_rest_field_mixed M a j s)
  rw [h,rawSlotActive_eq M a ν _ hs]
  have hh : JoiningOperator.operator (he.comp hx)
      ((MeasurePreserving.mk (measurable_slotRest M a) rfl).comp hr) =
      JoiningOperator.operator hs (MeasurePreserving.mk (measurable_slotRest M a) rfl) := by
    have hc := collapse_cell_column M a j
    have hop : JoiningOperator.operator (he.comp hx)
        ((MeasurePreserving.mk (measurable_slotRest M a) rfl).comp hr) =
        JoiningOperator.operator (hs.comp hr)
          ((MeasurePreserving.mk (measurable_slotRest M a) rfl).comp hr) := by
      congr 1
    exact hop.trans (JoiningOperator.operator_pullback hr hs (MeasurePreserving.mk (measurable_slotRest M a) rfl))
  rw [hh]

end ArrayObjects.Object.Rolled
end

section
variable {I : Type*} [Fintype I] [DecidableEq I]
omit [DecidableEq I] in
lemma singleton_proper (hk : 2 ≤ Fintype.card I) (i : I) : ({i} : Finset I) ≠ Finset.univ := by
  intro h
  have := congrArg Finset.card h
  simp only [Finset.card_singleton,Finset.card_univ] at this
  omega
end

section
open MeasureTheory
open scoped BigOperators
variable {I Y : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Y]
attribute [local instance] OAI.Rokhlin.instMeasurableSpaceCircle_solutions_4
local instance instBorelSpaceCircle_solutions_4 : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))

omit [MeasurableSpace Y] in
lemma circleComplete_self (i : I) (f : Y → Circle) (a : ↥(({i} : Finset I)ᶜ) → Y → Circle) :
    circleComplete i f a i = f := by funext y; simp [circleComplete]

lemma measurable_circleComplete (i : I) (f : Y → Circle) (a : ↥(({i} : Finset I)ᶜ) → Y → Circle)
    (hf : Measurable f) (ha : ∀ j, Measurable (a j)) (j : I) : Measurable (circleComplete i f a j) := by
  unfold circleComplete
  by_cases h : j = i
  · simpa only [dite_eq_left h] using hf
  · simp only [dite_eq_right h]
    exact measurable_inv.comp (ha ⟨j,by simpa using h⟩)

lemma prod_complement (i : I) (g : I → Circle) :
    (∏ j, g j) = g i * ∏ j : ↥(({i} : Finset I)ᶜ), g j := by
  rw [Fintype.prod_eq_mul_prod_compl i g,Finset.prod_coe_sort]

omit [MeasurableSpace Y] in
lemma circleComplete_prod (i : I) (f : Y → Circle) (a : ↥(({i} : Finset I)ᶜ) → Y → Circle)
    (y : I → Y) (c : Circle) (h : f (y i) = c * ∏ j, a j (y j)) :
    ∏ j, circleComplete i f a j (y j) = c := by
  rw [prod_complement i,circleComplete_self]
  have ht (j : ↥(({i} : Finset I)ᶜ)) : circleComplete i f a j (y j) = (a j (y j))⁻¹ := by
    have hj : (j : I) ≠ i := fun h => (Finset.mem_compl.mp j.property) (Finset.mem_singleton.mpr h)
    simp only [circleComplete,dite_eq_right hj]
  simp only [ht,Finset.prod_inv_distrib,h,mul_assoc,mul_inv_cancel,mul_one]

lemma prod_equation_solve (i : I) (g : I → Circle) (c : Circle) (h : ∏ j, g j = c) :
    g i = c * ∏ j : ↥(({i} : Finset I)ᶜ), (g j)⁻¹ := by
  rw [Finset.prod_inv_distrib,←h,prod_complement i,mul_assoc,mul_inv_cancel,mul_one]
end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
section
variable {I : Type*} [Fintype I] [DecidableEq I]
lemma prod_complement_split (i : I) (s : ComplementSplit ({i} : Finset I)) (g : I → Circle) :
    (∏ j : ↥(({i} : Finset I)ᶜ), g j) = (∏ j : s.A, g j) * ∏ j : s.B, g j := by
  rw [Finset.prod_coe_sort,Finset.prod_coe_sort,Finset.prod_coe_sort,←s.union_eq,
    Finset.prod_union s.disjointAB]
end
namespace ArrayObjects.Object.Rolled

section
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma raw_tuple_rowSplitExact (a j : I) (s : ComplementSplit ({j} : Finset I))
    (e : Arr I M.U 2)
    (hr : MeasurePreserving (plane 1 0 a) (M.ownKernel 2 e) (M.ownKernel 1 (plane 1 0 a e)))
    (f : I → Arr I M.Y 0 → Circle) (hf : ∀ i, Measurable (f i)) (c : Circle)
    (he : ∀ᵐ y ∂M.ownKernel 1 (plane 1 0 a e), ∏ i, f i (plane 0 0 i y) = c) :
    circleLp (cellLaw M {a} {j} 0 e) (f j ∘ collapseCell M a j)
      ((hf j).comp (collapseCell M a j).measurable) ∈ rowSplitExact M {a} {j} s 0 e := by
  let g : (s.A → ({a} : Finset I) → Arr I M.Y 0) → Circle :=
    fun z => c * ∏ i : s.A, (f i (z i ⟨a,Finset.mem_singleton_self a⟩))⁻¹
  let h : (s.B → ({a} : Finset I) → Arr I M.Y 0) → Circle :=
    fun z => ∏ i : s.B, (f i (z i ⟨a,Finset.mem_singleton_self a⟩))⁻¹
  have hg : Measurable g := measurable_const.mul (Finset.measurable_prod _ fun i _ =>
    ((hf i).comp ((measurable_pi_apply (⟨a,Finset.mem_singleton_self a⟩ : ({a} : Finset I))).comp (measurable_pi_apply i))).inv)
  have hh : Measurable h := Finset.measurable_prod _ fun i _ =>
    ((hf i).comp ((measurable_pi_apply (⟨a,Finset.mem_singleton_self a⟩ : ({a} : Finset I))).comp (measurable_pi_apply i))).inv
  apply JoiningOperator.circle_mem_splitExact _ _ _ _ _ (f j ∘ collapseCell M a j) g h
    ((hf j).comp (collapseCell M a j).measurable) hg hh
  filter_upwards [hr.quasiMeasurePreserving.ae he] with y hy
  have ht := prod_equation_solve j (fun i => f i (plane 0 0 i (plane 1 0 a y))) c hy
  rw [prod_complement_split j s (fun i => (f i (plane 0 0 i (plane 1 0 a y)))⁻¹)] at ht
  change f j (plane 0 0 j (plane 1 0 a y)) =
    (c * ∏ i : s.A, (f i (plane 0 0 i (plane 1 0 a y)))⁻¹) *
      ∏ i : s.B, (f i (plane 0 0 i (plane 1 0 a y)))⁻¹
  simpa only [mul_assoc] using ht

end

attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in
lemma oneRow_single_column (a j : I) (y : Arr I M.Y 2) :
    oneRow M {j} 0 a y = fun _ => plane 0 0 a (plane 1 (Fin.last 1) j y) := by
  funext t
  have ht : (t : I) = j := Finset.mem_singleton.mp t.property
  simp only [oneRow,ht]
  exact (congrFun (plane_first_last M 0 a j) y).symm

lemma fullExact_raw_column (a j : I) (e : Arr I M.U 2)
    (ν : Measure (Arr I M.Y 0)) [IsFiniteMeasure ν]
    (hm : MeasurePreserving (collapseCell M a j) (cellLaw M {a} {j} 0 e) ν)
    (hc : MeasurePreserving (plane 1 (Fin.last 1) j) (M.ownKernel 2 e)
      (M.ownKernel 1 (plane 1 (Fin.last 1) j e)))
    (v : Lp ℂ 2 ν) (hv : JoiningOperator.pull hm v ∈ fullExact M {a} {j} 0 e) :
    v ∈ rawExactCone M a ν (plane 1 (Fin.last 1) j e) := by
  obtain ⟨f,hf,d,he,_,b,c,hb,hprod⟩ := hv
  let g : Arr I M.Y 0 → Circle := f ∘ (collapseCell M a j).symm
  have hg : Measurable g := hf.comp (collapseCell M a j).symm.measurable
  have hvg : v = d • circleLp ν g hg := by
    apply (JoiningOperator.pullEquiv (collapseCell M a j) hm).injective
    change JoiningOperator.pull hm v = JoiningOperator.pull hm (d • circleLp ν g hg)
    rw [map_smul,circleLp_pull]
    have hgf : g ∘ collapseCell M a j = f := by
      funext z
      exact congrArg f ((collapseCell M a j).symm_apply_apply z)
    simpa only [hgf] using he
  let B : ↥(({a} : Finset I)ᶜ) → Arr I M.Y 0 → Circle := fun t y => b t (fun _ => y)
  have hB (t) : Measurable (B t) := (hb t).comp (Measurable.of_eval fun _ => measurable_id)
  refine ⟨circleComplete a g B,measurable_circleComplete a g B hg hB,c,d,?_,?_⟩
  · simpa only [circleComplete_self] using hvg
  · rw [←hc.map_eq]
    apply ae_map_descent _ hc.measurable
    filter_upwards [hprod] with y hy
    apply circleComplete_prod a g B _ c
    have hcell : (collapseCell M a j).symm (plane 0 0 a (plane 1 (Fin.last 1) j y)) =
        cells M {a} {j} 0 y := by
      apply (collapseCell M a j).injective
      rw [(collapseCell M a j).apply_symm_apply]
      exact (congrFun (collapse_cell_column M a j) y).symm
    simpa only [g,Function.comp_apply,hcell,B,oneRow_single_column] using hy

lemma raw_row_active_to_column_exact_oai (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I) (a j : I) :
    ∀ᵐ e ∂M.parameterLaw 2, ∀ (f : I → Arr I M.Y 0 → Circle)
      (hf : ∀ i, Measurable (f i)) (c : Circle),
      (∀ᵐ y ∂M.ownKernel 1 (plane 1 0 a e), ∏ i, f i (plane 0 0 i y) = c) →
      let ν := M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))
      let v := circleLp ν (f j) (hf j)
      v ∈ rawSlotActive M a ν (plane 1 (Fin.last 1) j e) →
      v ∈ rawExactCone M a ν (plane 1 (Fin.last 1) j e) := by
  let s := singletonSplit hk a
  let t := singletonSplit hk j
  have hI : 2 ≤ Fintype.card I := by omega
  filter_upwards [grouped_full_row_column_exact M hM {a} {j} s t 0,
    row_marginal_fibre M hM hI a,column_marginal_fibre M hI j,
    singleton_collapse_preserving M hM hI a j,
    columnActive_mixed_slot M hM hI a j (singleton_proper hI j) s]
    with e hfull hr hc hm hcol
  intro f hf c he
  dsimp only
  intro hv
  apply fullExact_raw_column M a j e _ hm hc
  apply hfull
  · intro t'
    rw [circleLp_pull]
    exact raw_tuple_rowSplitExact M a j t' e hr f hf c he
  · exact (hcol _ hm _).mp hv

end ArrayObjects.Object.Rolled
end

open MeasureTheory Set

end Rokhlin

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_active_to_column_exact_oai.{u} := @OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_active_to_column_exact_oai.{u}
