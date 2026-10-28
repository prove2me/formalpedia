-- Prove2me | solution 1 for OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_indicators_equal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:56:58.982987+00:00
-- url     : https://prove2.me/submissions/e7df219e-b6f6-4db9-b4f7-c2c4bd29fc12
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ3Ro002
import Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_grouped_active_intersections
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

lemma field_finset_grid {J : Type*} (f : I → J → Ω → Y) (s : Finset I) (t : Finset J) :
    MeasurableSpace.comap (fun ω (i : s) (j : t) => f i j ω) inferInstance =
      ⨆ i ∈ s, ⨆ j ∈ t, MeasurableSpace.comap (f i j) inferInstance := by
  rw [MeasurableSpace.comap_process_pi]
  simp_rw [MeasurableSpace.comap_process_pi]
  simp only [iSup_subtype]

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

section
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma orthogonal_line_projection (S C : Set H) (V : Submodule ℂ H)
    [V.HasOrthogonalProjection] (hCV : (Submodule.span ℂ C).topologicalClosure = V)
    (hCS : C ⊆ S)
    (horth : ∀ v ∈ S, ∀ w ∈ S, inner ℂ v w = 0 ∨ ∃ c : ℂ, v = c • w)
    {v : H} (hv : v ∈ S) : V.starProjection v = 0 ∨ V.starProjection v = v := by
  by_cases hm : v ∈ V
  · exact Or.inr (V.starProjection_eq_self_iff.mpr hm)
  · left
    apply V.starProjection_apply_eq_zero_iff.mpr
    rw [←hCV,Submodule.orthogonal_closure,Submodule.mem_orthogonal']
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      rcases horth v hv w (hCS hw) with ho | ⟨c,hc⟩
      · exact ho
      · exact (hm (hc.symm ▸ V.smul_mem c (hCV ▸ Submodule.le_topologicalClosure _ (Submodule.subset_span hw)))).elim
    | zero => simp
    | add x y hx hy ihx ihy => simp only [inner_add_right,ihx,ihy,add_zero]
    | smul c x hx ih => simp only [inner_smul_right,ih,mul_zero]

end

section
open MeasureTheory
open scoped InnerProductSpace ENNReal ComplexConjugate
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma lp_star_zero : star (0 : Lp ℂ 2 μ) = 0 := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (0 : Lp ℂ 2 μ),Lp.coeFn_zero ℂ 2 μ] with x hs hz
  simp only [Pi.zero_apply,Pi.star_apply] at hs hz ⊢
  rw [hs,hz,star_zero]

lemma lp_star_sub (f g : Lp ℂ 2 μ) : star (f-g) = star f-star g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (f-g),Lp.coeFn_star f,Lp.coeFn_star g,
    Lp.coeFn_sub f g,Lp.coeFn_sub (star f) (star g)] with x hs hf hg hd hd'
  simp only [Pi.star_apply,Pi.sub_apply] at hs hf hg hd hd'
  rw [hs,hd,star_sub,hd',hf,hg]

lemma lp_inner_star_star (f g : Lp ℂ 2 μ) :
    inner ℂ (star f) (star g) = star (inner ℂ f g) := by
  rw [L2.inner_def,L2.inner_def]
  change _ = conj (∫ x, inner ℂ (f x) (g x) ∂μ)
  rw [←integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f,Lp.coeFn_star g] with x hf hg
  simp only [Pi.star_apply] at hf hg
  rw [hf,hg]
  simp only [RCLike.inner_apply,starRingEnd_apply,star_mul,star_star,mul_comm]

lemma lp_inner_star_right (f g : Lp ℂ 2 μ) :
    inner ℂ f (star g) = star (inner ℂ (star f) g) := by
  simpa only [star_star] using lp_inner_star_star (star f) g

lemma lp_star_projection (V : Submodule ℂ (Lp ℂ 2 μ)) [V.HasOrthogonalProjection]
    (hV : ∀ v ∈ V, star v ∈ V) (f : Lp ℂ 2 μ) :
    V.starProjection (star f) = star (V.starProjection f) := by
  apply V.eq_starProjection_of_mem_of_inner_eq_zero
    (hV _ (V.starProjection_apply_mem f))
  intro w hw
  rw [←lp_star_sub]
  have h := V.starProjection_inner_eq_zero f (star w) (hV w hw)
  have hs := lp_inner_star_star (f - V.starProjection f) (star w)
  simpa only [star_star,h,star_zero] using hs
end

namespace JoiningOperator
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ComplexConjugate
variable {Ω X Y U : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace U]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y}
  {x : Ω → X} {y : Ω → Y}

lemma operator_star (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (h : Lp ℂ 2 ρ) : operator hx hy (star h) = star (operator hx hy h) := by
  apply ext_inner_left ℂ
  intro g
  rw [inner_operator,lp_inner_star_right,inner_operator]
  change _ = conj (∫ ω, inner ℂ (star g (x ω)) (h (y ω)) ∂μ)
  rw [←integral_conj]
  apply integral_congr_ae
  filter_upwards [hx.quasiMeasurePreserving.ae (Lp.coeFn_star g),
    hy.quasiMeasurePreserving.ae (Lp.coeFn_star h)] with ω hg hh
  simp only [Pi.star_apply] at hg hh
  rw [hg,hh]
  simp only [RCLike.inner_apply,starRingEnd_apply,star_mul,star_star,mul_comm]

lemma family_adjoint_star (κ : Kernel U (X × Y)) (ν : Measure X) (ρ : Measure Y)
    (u : U) (h : Lp ℂ 2 ν) :
    (family κ ν ρ u).adjoint (star h) = star ((family κ ν ρ u).adjoint h) := by
  classical
  unfold family
  split_ifs with hp
  · rw [operator_adjoint]
    exact operator_star hp.2 hp.1 h
  · simpa only [map_zero,zero_apply] using lp_star_zero.symm

lemma family_active_star (κ : Kernel U (X × Y)) (ν : Measure X) (ρ : Measure Y)
    (m : Measure U) {v : Lp ℂ 2 ν} (hv : v ∈ essentialRange m (family κ ν ρ)) :
    star v ∈ essentialRange m (family κ ν ρ) := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro k hk
  have hs : star k ∈ essentialKernel m (fun u => (family κ ν ρ u).adjoint) := by
    change ∀ᵐ u ∂m, (family κ ν ρ u).adjoint (star k) = 0
    change ∀ᵐ u ∂m, (family κ ν ρ u).adjoint k = 0 at hk
    filter_upwards [hk] with u hu
    rw [family_adjoint_star,hu,lp_star_zero]
  rw [lp_inner_star_right,(Submodule.mem_orthogonal _ _).mp hv (star k) hs,star_zero]

attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
lemma operator_circle_exact [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (f : X → Circle) (g : Y → Circle) (hf : Measurable f) (hg : Measurable g)
    (c : Circle) (he : ∀ᵐ ω ∂μ, g (y ω) = c * f (x ω)) :
    operator hx hy (circleLp ρ g hg) = (c : ℂ) • circleLp ν f hf := by
  have hp : pull hy (circleLp ρ g hg) = (c : ℂ) • pull hx (circleLp ν f hf) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (circleLp ρ g hg) hy,
      Lp.coeFn_compMeasurePreserving (circleLp ν f hf) hx,
      hy.quasiMeasurePreserving.ae (circleLp_coe ρ g hg),
      hx.quasiMeasurePreserving.ae (circleLp_coe ν f hf),
      Lp.coeFn_smul (c : ℂ) (pull hx (circleLp ν f hf)),he]
      with ω h1 h2 h3 h4 h5 he
    calc
      _ = (g (y ω) : ℂ) := h1.trans h3
      _ = (c : ℂ) * (f (x ω) : ℂ) := congrArg ((↑) : Circle → ℂ) he
      _ = _ := (h5.trans (congrArg (fun z : ℂ => (c : ℂ)*z) (h2.trans h4))).symm
  change (pull hx).adjoint (pull hy (circleLp ρ g hg)) = _
  rw [hp,map_smul]
  congr 1
  exact congrArg (fun A : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν => A (circleLp ν f hf)) (pull_adjoint_pull hx)
end JoiningOperator

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
omit [DecidableEq I] in
lemma rowActive_star (A R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2))
    {v : Lp ℂ 2 (cellLaw M A R n e)} (hv : v ∈ rowActive M A R S D n e) :
    star v ∈ rowActive M A R S D n e := by
  unfold rowActive at *
  rw [fibreRowEdge_eq] at *
  exact JoiningOperator.family_active_star _ _ _ _ hv
omit [DecidableEq I] in
lemma columnActive_star (P A B R : Finset I) (n : ℕ) (e : Arr I M.U (n+2))
    {v : Lp ℂ 2 (cellLaw M P R n e)} (hv : v ∈ columnActive M P A B R n e) :
    star v ∈ columnActive M P A B R n e := by
  unfold columnActive at *
  rw [fibreColumnEdge_eq] at *
  exact JoiningOperator.family_active_star _ _ _ _ hv
omit [DecidableEq I] in
lemma commonActive_star (P A B R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2))
    {v : Lp ℂ 2 (cellLaw M P R n e)} (hv : v ∈ commonActive M P A B R S D n e) :
    star v ∈ commonActive M P A B R S D n e :=
  ⟨rowActive_star M _ _ _ _ _ _ hv.1,columnActive_star M _ _ _ _ _ _ hv.2⟩
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory
variable {Ω S Z : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace Z]
  [StandardBorelSpace Ω] [StandardBorelSpace S] [StandardBorelSpace Z]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Ω → S} {z : Ω → Z}
  {κ : Kernel S Z} [IsSFiniteKernel κ]
lemma conditional_ae_descent (hs : Measurable s) (hz : Measurable z)
    (hκ : HasCondDistrib z s κ μ) {P : S → Z → Prop} (hP : ∀ᵐ ω ∂μ, P (s ω) (z ω)) :
    ∀ᵐ a ∂μ.map s, ∀ᵐ b ∂κ a, P a b := by
  apply Measure.ae_ae_of_ae_compProd (p := fun p : S × Z => P p.1 p.2)
  rw [←hκ.map_eq]
  exact ae_map_descent μ (hs.prodMk hz) hP
end

namespace JoiningOperator
open MeasureTheory ProbabilityTheory
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {Ω X Y R : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace R]
  [StandardBorelSpace Ω] [StandardBorelSpace X] [StandardBorelSpace Y] [StandardBorelSpace R]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure X} {ρ : Measure Y}
  [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
  {x : Ω → X} {y : Ω → Y} {r : Ω → R}
  {κ : Kernel R (X × Y)} [IsSFiniteKernel κ]

lemma family_circle_exact (hx : Measurable x) (hy : Measurable y) (hr : Measurable r)
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) r κ μ)
    (hm : ∀ᵐ a ∂μ.map r, MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (f : X → Circle) (g : Y → Circle) (c : R → Circle)
    (hf : Measurable f) (hg : Measurable g)
    (he : ∀ᵐ ω ∂μ, g (y ω) = c (r ω) * f (x ω)) :
    ∀ᵐ a ∂μ.map r, family κ ν ρ a (circleLp ρ g hg) = (c a : ℂ) • circleLp ν f hf := by
  have h := conditional_ae_descent (κ := κ)
    (P := fun a p => g p.2 = c a * f p.1) hr (hx.prodMk hy) hκ he
  filter_upwards [h,hm] with a ha hm
  rw [family_eq κ ν ρ a hm.1 hm.2]
  exact operator_circle_exact hm.1 hm.2 f g hf hg (c a) ha
end JoiningOperator

section
open MeasureTheory
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure X} {ρ : Measure Y}
lemma binary_projection_transfer (D : Submodule ℂ (Lp ℂ 2 ν)) (E : Submodule ℂ (Lp ℂ 2 ρ))
    [D.HasOrthogonalProjection] [E.HasOrthogonalProjection]
    (hE : ∀ w ∈ E, star w ∈ E)
    (F : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ν)
    (hF : D.starProjection ∘L F = F ∘L E.starProjection)
    (v : Lp ℂ 2 ν) (w : Lp ℂ 2 ρ) (c : ℂ) (hc : c ≠ 0) (hv : v ≠ 0)
    (he : F (star w) = c • v)
    (hw : E.starProjection w = 0 ∨ E.starProjection w = w) :
    D.starProjection v = v ↔ E.starProjection w = w := by
  have hi := congrArg (fun A : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ν => A (star w)) hF
  simp only [ContinuousLinearMap.comp_apply,he,map_smul,lp_star_projection E hE] at hi
  constructor
  · intro hd
    rcases hw with hz | hid
    · rw [hz,lp_star_zero,map_zero,hd] at hi
      exact (hv ((smul_eq_zero.mp hi).resolve_left hc)).elim
    · exact hid
  · intro hid
    rw [hid,he] at hi
    exact (smul_right_injective _ hc) hi
end

section
open MeasureTheory
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
lemma circleLp_inv (f : X → Circle) (hf : Measurable f) :
    circleLp μ (fun x => (f x)⁻¹) hf.inv = star (circleLp μ f hf) := by
  apply Lp.ext
  filter_upwards [circleLp_coe μ (fun x => (f x)⁻¹) hf.inv,circleLp_coe μ f hf,
    Lp.coeFn_star (circleLp μ f hf)] with x h1 h2 h3
  rw [h1,h3]
  change (↑((f x)⁻¹) : ℂ) = star (circleLp μ f hf x)
  rw [h2,Circle.coe_inv_eq_conj]
  rfl
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
lemma rowSplitExact_le_rowActive (hM : M.IsSaturated) (P R : Finset I)
    (hP : P ≠ Finset.univ) (t : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂M.parameterLaw (n+2), rowSplitExact M P R t n e ⊆ rowActive M P R t.A t.B n e := by
  filter_upwards [rowActive_eq_range M hM P hP t.partition n,
    cells_fibre_marginal M hM P R hP n,
    cells_fibre_marginal M hM P t.A hP n,
    cells_fibre_marginal M hM P t.B hP n,
    cells_indep_columns_fibre M P P t.A t.B t.disjointAB t.partition.properAB n]
    with e hr hz ha hb hab
  rw [hr hz (cells_pair_preserving M ha hb hab)]
  exact JoiningOperator.splitExact_le_active hz (cells_pair_preserving M ha hb hab)

lemma grouped_row_membership_transfer (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂M.parameterLaw (n+2),
      ∀ (f : (cols.A → rows.A → Arr I M.Y n) → Circle)
        (g : (cols.B → rows.A → Arr I M.Y n) → Circle)
        (c : (cols.P → rows.A → Arr I M.Y n) → Circle)
        (hf : Measurable f) (hg : Measurable g) (_hc : Measurable c),
        (∀ᵐ y ∂M.ownKernel (n+2) e,
          (g (cells M rows.A cols.B n y))⁻¹ =
            c (cells M rows.A cols.P n y) * f (cells M rows.A cols.A n y)) →
        (circleLp (cellLaw M rows.A cols.A n e) f hf ∈ columnActive M rows.A rows.P rows.B cols.A n e ↔
         circleLp (cellLaw M rows.A cols.B n e) g hg ∈ columnActive M rows.A rows.P rows.B cols.B n e) := by
  filter_upwards [grouped_active_intersections M hM rows cols n,
    grouped_exact_split_span M hM rows.A cols.B rows.swapPA.split cols.swapPB.swapAB.split n,
    rowSplitExact_dichotomy M hM rows.A cols.B rows.properA cols.swapPB.swapAB.split n,
    rowSplitExact_le_rowActive M hM rows.A cols.A rows.properA cols.swapPA.split n,
    rowSplitExact_le_rowActive M hM rows.A cols.B rows.properA cols.swapPB.swapAB.split n,
    rowPair_fixed_conditional M rows.A cols.P cols.A cols.B n,
    rowPair_fixed_marginals M hM rows.A cols.P cols.A cols.B rows.properA
      cols.disjointPA cols.disjointPB cols.properPA cols.properPB n,
    cells_fibre_marginal M hM rows.A cols.P rows.properA n]
      with e hi hs ho hra hrb hk hm hp
  intro f g c hf hg hc he
  have hfex : circleLp (cellLaw M rows.A cols.A n e) f hf ∈
      rowSplitExact M rows.A cols.A cols.swapPA.split n e := by
    apply JoiningOperator.circle_mem_splitExact _ _ _ _ _ f (fun z => (c z)⁻¹) (fun z => (g z)⁻¹) hf hc.inv hg.inv
    filter_upwards [he] with y hy
    rw [hy]
    simp only [inv_mul_cancel_left]
  have hgex : circleLp (cellLaw M rows.A cols.B n e) g hg ∈
      rowSplitExact M rows.A cols.B cols.swapPB.swapAB.split n e := by
    apply JoiningOperator.circle_mem_splitExact _ _ _ _ _ g (fun z => (c z)⁻¹) (fun z => (f z)⁻¹) hg hc.inv hf.inv
    filter_upwards [he] with y hy
    have h := congrArg Inv.inv hy
    simpa only [inv_inv,mul_inv_rev,mul_comm] using h
  have hw := orthogonal_line_projection
    (rowSplitExact M rows.A cols.B cols.swapPB.swapAB.split n e)
    (rowSplitExact M rows.A cols.B cols.swapPB.swapAB.split n e ∩
      columnSplitExact M rows.A cols.B rows.swapPA.split n e)
    (commonActive M rows.A rows.P rows.B cols.B cols.P cols.A n e)
    hs Set.inter_subset_left ho hgex
  have heq := JoiningOperator.family_circle_exact
    (measurable_cells M rows.A cols.A n) (measurable_cells M rows.A cols.B n)
    (measurable_cells M rows.A cols.P n) hk hm f (fun z => (g z)⁻¹) c hf hg.inv he
  rw [←hp.map_eq] at hi
  have ht : ∀ᵐ r ∂(M.ownKernel (n+2) e).map (cells M rows.A cols.P n),
      (commonActive M rows.A rows.P rows.B cols.A cols.P cols.B n e).starProjection
          (circleLp (cellLaw M rows.A cols.A n e) f hf) = circleLp (cellLaw M rows.A cols.A n e) f hf ↔
      (commonActive M rows.A rows.P rows.B cols.B cols.P cols.A n e).starProjection
          (circleLp (cellLaw M rows.A cols.B n e) g hg) = circleLp (cellLaw M rows.A cols.B n e) g hg := by
    filter_upwards [hi.1,heq] with r hir her
    apply binary_projection_transfer _ _ (fun _ hv => commonActive_star M _ _ _ _ _ _ _ _ hv)
      (fibreRowEdge M rows.A cols.P cols.A cols.B n e r) hir
      _ _ (c r : ℂ) (Circle.coe_ne_zero _) (circleLp_ne_zero _ f hf) _ hw
    rw [fibreRowEdge_eq]
    rwa [circleLp_inv] at her
  rw [hp.map_eq] at ht
  obtain ⟨r,hr⟩ := ht.exists
  have hfa : circleLp (cellLaw M rows.A cols.A n e) f hf ∈ rowActive M rows.A cols.A cols.P cols.B n e := hra hfex
  have hgb : circleLp (cellLaw M rows.A cols.B n e) g hg ∈ rowActive M rows.A cols.B cols.P cols.A n e := hrb hgex
  simpa only [Submodule.starProjection_eq_self_iff,commonActive,Submodule.mem_inf,
    hfa,hgb,true_and] using hr
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
open MeasureTheory ProbabilityTheory
open scoped BigOperators
section
variable {I : Type*} [Fintype I] [DecidableEq I]
lemma prod_pair_solve (j t : I) (hjt : j ≠ t) (g : I → Circle) (c : Circle)
    (h : ∏ s, g s = c) :
    (g t)⁻¹ = c⁻¹ * (∏ s : ↥(({j,t} : Finset I)ᶜ), g s) * g j := by
  have ht : (g j * g t) * (∏ s : ↥(({j,t} : Finset I)ᶜ), g s) = c := by
    rw [Finset.prod_coe_sort, ←Finset.prod_pair hjt, Finset.prod_mul_prod_compl]
    exact h
  rw [←ht]
  simp [mul_inv_rev,mul_assoc,mul_comm,mul_left_comm]
end
namespace ArrayObjects.Object.Rolled
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
lemma raw_row_membership_transfer (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (a j t : I) (hjt : j ≠ t) :
    ∀ᵐ e ∂M.parameterLaw 2, ∀ (f : I → Arr I M.Y 0 → Circle)
      (hf : ∀ i, Measurable (f i)) (c : Circle),
      (∀ᵐ y ∂M.ownKernel 1 (plane 1 0 a e), ∏ i, f i (plane 0 0 i y) = c) →
      (circleLp (M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))) (f j) (hf j) ∈
        rawSlotActive M a (M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))) (plane 1 (Fin.last 1) j e) ↔
      circleLp (M.ownKernel 0 (plane 0 0 t (plane 1 0 a e))) (f t) (hf t) ∈
        rawSlotActive M a (M.ownKernel 0 (plane 0 0 t (plane 1 0 a e))) (plane 1 (Fin.last 1) t e)) := by
  have hI : 2 ≤ Fintype.card I := by omega
  let s := singletonSplit hk a
  let rows := s.partition.swapPA
  let cols := pairPartition hk j t hjt
  filter_upwards [grouped_row_membership_transfer M hM rows cols 0,
    columnActive_mixed_slot M hM hI a j (singleton_proper hI j) s,
    columnActive_mixed_slot M hM hI a t (singleton_proper hI t) s,
    singleton_collapse_preserving M hM hI a j,
    singleton_collapse_preserving M hM hI a t,
    row_marginal_fibre M hM hI a] with e he hj ht hmj hmt hr
  intro f hf c hc
  rw [hj _ hmj,ht _ hmt,circleLp_pull,circleLp_pull]
  let r : (cols.P → rows.A → Arr I M.Y 0) → Circle :=
    fun z => c⁻¹ * ∏ i : cols.P, f i (z i ⟨a,Finset.mem_singleton_self a⟩)
  have hmr : Measurable r := measurable_const.mul (Finset.measurable_prod _ fun i _ =>
    (hf i).comp ((measurable_pi_apply _).comp (measurable_pi_apply i)))
  apply he (f j ∘ collapseCell M a j) (f t ∘ collapseCell M a t) r
    ((hf j).comp (collapseCell M a j).measurable) ((hf t).comp (collapseCell M a t).measurable) hmr
  filter_upwards [hr.quasiMeasurePreserving.ae hc] with y hy
  exact prod_pair_solve j t hjt (fun i => f i (plane 0 0 i (plane 1 0 a y))) c hy
end ArrayObjects.Object.Rolled
end

section
open MeasureTheory ProbabilityTheory Set
variable {P Ω X Y U : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]
  [retained12 : StandardBorelSpace Ω] [StandardBorelSpace X]
  [StandardBorelSpace Y] [Nonempty Y]
  (Λ : Kernel P Ω) [IsMarkovKernel Λ] (x : Ω → X) (y : Ω → Y)
  (hx : Measurable x) (hy : Measurable y)

omit [StandardBorelSpace Ω] in
include hx hy in
lemma joiningPosterior_conditional (p : P) :
    HasCondDistrib y x ((joiningPosterior Λ x y).sectR p) (Λ p) := by
  let K := Λ.map (fun ω => (x ω,y ω))
  let : IsMarkovKernel K := Kernel.IsMarkovKernel.map _ (hx.prodMk hy)
  have h := congrArg (fun K : Kernel P (X × Y) => K p) (Kernel.disintegrate K K.condKernel)
  rw [Kernel.compProd_apply_eq_compProd_sectR,Kernel.fst_apply,Kernel.map_apply _ (hx.prodMk hy)] at h
  refine ⟨(hx.prodMk hy).aemeasurable,?_⟩
  rw [Measure.map_map measurable_fst (hx.prodMk hy)] at h
  exact h.symm

variable (κ : Kernel U X) [IsMarkovKernel κ] (u : P → U)
  (f : Y → ℂ) (hf : Measurable f) (B : ℝ) (hB : ∀ z, ‖f z‖ ≤ B)

lemma posteriorVector_eq_operator (p : P)
    (hxm : MeasurePreserving x (Λ p) (κ (u p))) :
    posteriorVector Λ x y κ u f hf B hB p =
      JoiningOperator.operator hxm (MeasurePreserving.mk hy rfl)
        ((MemLp.of_bound hf.aestronglyMeasurable B
          (Filter.Eventually.of_forall hB) : MemLp f 2 ((Λ p).map y)).toLp f) := by
  let g := (MemLp.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall hB) : MemLp f 2 ((Λ p).map y)).toLp f
  have he : (fun ω => g (y ω)) =ᵐ[Λ p] (fun ω => f (y ω)) :=
    (MeasurePreserving.mk hy rfl).quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp _)
  have hl : Integrable (fun ω => f (y ω)) (Λ p) :=
    (MemLp.of_bound (hf.comp hy).aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun ω => hB (y ω))) : MemLp (fun ω => f (y ω)) 2 (Λ p)).integrable (by norm_num)
  have hop := JoiningOperator.operator_ae_eq_condExp hxm (MeasurePreserving.mk hy rfl) g
  have hce := JoiningOperator.condExp_of_kernel hxm.measurable (joiningPosterior_conditional Λ x y hxm.measurable hy p)
    f hf.stronglyMeasurable hl
  have hop' : (fun ω => JoiningOperator.operator hxm (MeasurePreserving.mk hy rfl) g (x ω)) =ᵐ[Λ p]
      (fun ω => ∫ z, f z ∂joiningPosterior Λ x y (p,x ω)) :=
    hop.trans ((condExp_congr_ae he).trans hce)
  have hh : ∀ᵐ z ∂(Λ p).map x, posteriorVector Λ x y κ u f hf B hB p z =
      JoiningOperator.operator hxm (MeasurePreserving.mk hy rfl) g z := by
    apply ae_map_descent _ hxm.measurable
    filter_upwards [hxm.quasiMeasurePreserving.ae_eq_comp
      (posterior_memLp Λ x y κ u f hf B hB p).coeFn_toLp,hop'] with ω hv ho
    exact hv.trans ho.symm
  rw [hxm.map_eq] at hh
  exact Lp.ext hh
end

section
open MeasureTheory ProbabilityTheory Set
variable {Y : Type*} [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
variable {P Ω X U : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace U] [StandardBorelSpace Ω] [StandardBorelSpace X]
  [StandardBorelSpace Y] [Nonempty Y]
  (Λ : Kernel P Ω) [IsMarkovKernel Λ] (x : Ω → X) (y : Ω → Y)
  (κ : Kernel U X) [IsMarkovKernel κ] (u : P → U)

lemma posteriorTest_eq_operator (hy : Measurable y) (p : P)
    (hxm : MeasurePreserving x (Λ p) (κ (u p))) (n : ℕ) :
    posteriorTest Λ x y κ u n p =
      JoiningOperator.operator hxm (MeasurePreserving.mk hy rfl) (hilbertTests ((Λ p).map y) n) := by
  rw [posteriorTest,posteriorVector_eq_operator Λ x y hy κ u _ _ _ _ p hxm]
  congr 1
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans (hilbertTestVector_coe _ _).symm

lemma operator_range_le_iff_tests {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (L : A →L[ℂ] B)
    (v : ℕ → A) (hv : DenseRange v) (S : Submodule ℂ B) (hS : IsClosed (S : Set B)) :
    (LinearMap.range L.toLinearMap).topologicalClosure ≤ S ↔ ∀ n, L (v n) ∈ S := by
  constructor
  · intro h n
    exact h (Submodule.le_topologicalClosure _ ⟨v n,rfl⟩)
  · intro h
    apply Submodule.topologicalClosure_minimal _ _ hS
    rintro _ ⟨a,rfl⟩
    exact hv.induction_on a (hS.preimage L.continuous) h
end

section
open MeasureTheory ProbabilityTheory
section
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
lemma operator_range_eq_span_tests {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (L : A →L[ℂ] B)
    (v : ℕ → A) (hv : DenseRange v) :
    (LinearMap.range L.toLinearMap).topologicalClosure =
      (Submodule.span ℂ (Set.range (fun n => L (v n)))).topologicalClosure := by
  apply le_antisymm
  · apply (operator_range_le_iff_tests L v hv _ (Submodule.isClosed_topologicalClosure _)).mpr
    intro n
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n,rfl⟩)
  · apply Submodule.topologicalClosure_mono
    apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    exact ⟨v n,rfl⟩

end
namespace ArrayObjects.Object.Rolled
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma rawSlotTest_eq_operator (i : I) (p : Arr I M.U 1)
    (hp : MeasurePreserving (plane 0 0 i) (M.ownKernel 1 p)
      (M.ownKernel 0 (plane 0 0 i p))) (n : ℕ) :
    rawSlotTest M i n p = JoiningOperator.operator hp
      (MeasurePreserving.mk (measurable_slotRest M i) rfl)
      (hilbertTests ((M.ownKernel 1 p).map (slotRest M i)) n) :=
  posteriorTest_eq_operator _ _ _ _ _ (measurable_slotRest M i) p hp n

lemma rawSlotActive_eq_testSpan (hI : 2 ≤ Fintype.card I) (i : I) :
    ∀ᵐ p ∂M.parameterLaw 1,
      rawSlotActive M i (M.ownKernel 0 (plane 0 0 i p)) p = rawSlotTestSpan M i p := by
  have hm := ConditionalFibres.marginal (measurable_plane 0 0 i)
    (M.ownKernel_conditional 1) (M.plane_conditional hI 0 i)
  filter_upwards [hm] with p hp
  have hp' : MeasurePreserving (plane 0 0 i) (M.ownKernel 1 p)
      (M.ownKernel 0 (plane 0 0 i p)) := hp
  rw [rawSlotActive_eq M i _ p hp',rawSlotTestSpan]
  have ht : (fun n => rawSlotTest M i n p) = (fun n => JoiningOperator.operator hp'
      (MeasurePreserving.mk (measurable_slotRest M i) rfl)
      (hilbertTests ((M.ownKernel 1 p).map (slotRest M i)) n)) :=
    funext (rawSlotTest_eq_operator M i p hp')
  rw [ht]
  exact operator_range_eq_span_tests _ _ (hilbertTests_dense _)

variable {P : Type*} [MeasurableSpace P]

lemma rawSlotIndicator_eq_true_iff (i : I) (f : P → Arr I M.Y 0 → Circle)
    (hf : Measurable (Function.uncurry f)) (p : P) (q : Arr I M.U 1) :
    rawSlotIndicator M i f hf p q = true ↔
      circleLp (M.ownKernel 0 (plane 0 0 i q)) (f p)
        (hf.comp (measurable_const.prodMk measurable_id)) ∈ rawSlotTestSpan M i q := by
  classical
  exact decide_eq_true_iff
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

lemma rawSlotIndicator_on_square (hI : 2 ≤ Fintype.card I) (a j : I)
    (f : Arr I M.U 1 → Arr I M.Y 0 → Circle)
    (hf : Measurable (Function.uncurry f)) :
    ∀ᵐ e ∂M.parameterLaw 2,
      rawSlotIndicator M a f hf (plane 1 0 a e) (plane 1 (Fin.last 1) j e) = true ↔
      circleLp (M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))) (f (plane 1 0 a e))
        (hf.comp (measurable_const.prodMk measurable_id)) ∈
      rawSlotActive M a (M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))) (plane 1 (Fin.last 1) j e) := by
  have hmp : MeasurePreserving (plane 1 (Fin.last 1) j) (M.parameterLaw 2) (M.parameterLaw 1) :=
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
  filter_upwards [hmp.quasiMeasurePreserving.ae (rawSlotActive_eq_testSpan M hI a)] with e he
  rw [rawSlotIndicator_eq_true_iff,←he]
  have hloc : plane 0 0 j (plane 1 0 a e) = plane 0 0 a (plane 1 (Fin.last 1) j e) := by
    funext x
    simp only [plane]
    congr 1
    funext t
    fin_cases t <;> rfl

  rw [hloc]

lemma raw_row_indicators_equal_oai (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (a j t : I) (hjt : j ≠ t)
    (f : Arr I M.U 1 → I → Arr I M.Y 0 → Circle)
    (hf : ∀ i, Measurable (fun py : Arr I M.U 1 × Arr I M.Y 0 => f py.1 i py.2))
    (he : ∀ᵐ p ∂M.parameterLaw 1, ∃ c : Circle,
      ∀ᵐ y ∂M.ownKernel 1 p, ∏ i, f p i (plane 0 0 i y) = c) :
    ∀ᵐ e ∂M.parameterLaw 2,
      rawSlotIndicator M a (fun p => f p j) (hf j) (plane 1 0 a e) (plane 1 (Fin.last 1) j e) =
      rawSlotIndicator M a (fun p => f p t) (hf t) (plane 1 0 a e) (plane 1 (Fin.last 1) t e) := by
  have hr : MeasurePreserving (plane 1 0 a) (M.parameterLaw 2) (M.parameterLaw 1) :=
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
  filter_upwards [raw_row_membership_transfer M hM hk a j t hjt,
    rawSlotIndicator_on_square M (by omega) a j (fun p => f p j) (hf j),
    rawSlotIndicator_on_square M (by omega) a t (fun p => f p t) (hf t),hr.quasiMeasurePreserving.ae he]
    with e htrans hj ht hex
  obtain ⟨c,hc⟩ := hex
  apply Bool.eq_iff_iff.mpr
  rw [hj,ht]
  exact htrans (f (plane 1 0 a e))
    (fun i => (hf i).comp (measurable_const.prodMk measurable_id)) c hc

end CircleSlotIndicators


universe u
end ArrayObjects.Object.Rolled

open MeasureTheory Set

end Rokhlin

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_indicators_equal_oai.{u} := @OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_indicators_equal_oai.{u}
