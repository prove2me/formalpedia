-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteSetKernel_map_pullback_translate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:10:12.828262+00:00
-- url     : https://prove2.me/submissions/3a5e3d2e-09cb-4c50-b0f5-1cecb84dec81

import Mathlib
import Definitions.Def_MarkovProcess_V3H_FiniteTime_DenseTimeFiniteShift_11c70184
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelShift_14b03019
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelShift_4030eb49
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
noncomputable section

@[simp]
private theorem finiteSetTranslateEquiv_apply (s : NNReal) (I : Finset NNReal) (t : I) :
    (finiteSetTranslateEquiv s I t : NNReal) = s + t :=
  rfl


private theorem measurable_pullbackFiniteSetTranslate {alpha : Type*} [MeasurableSpace alpha]
    (s : NNReal) (I : Finset NNReal) :
    Measurable (pullbackFiniteSetTranslate (alpha := alpha) s I) :=
  measurable_pi_iff.mpr fun t ↦ measurable_pi_apply (finiteSetTranslateEquiv s I t)

private def finiteSetTranslateFinOrderIso (s : NNReal) (I : Finset NNReal) :
    Fin I.card ≃o Fin (finiteSetTranslate s I).card :=
  Fin.castOrderIso (by simp only [finiteSetTranslate, Finset.card_map])

private theorem finiteSetTimes_translate (s : NNReal) (I : Finset NNReal) :
    (finiteSetTimes (finiteSetTranslate s I)).restrict
        (finiteSetTranslateFinOrderIso s I).toOrderEmbedding =
      (finiteSetTimes I).translate s := by
  let e := (finiteSetTranslateFinOrderIso s I).toOrderEmbedding
  have hcard : (finiteSetTranslate s I).card = I.card := by
    simp only [finiteSetTranslate, Finset.card_map]
  have hleft :
      (fun i : Fin I.card ↦ finiteSetTimes (finiteSetTranslate s I) (e i)) =
        (finiteSetTranslate s I).orderEmbOfFin hcard := by
    apply Finset.orderEmbOfFin_unique hcard
    · intro i
      exact Finset.orderEmbOfFin_mem _ rfl (e i)
    · exact (finiteSetTimes (finiteSetTranslate s I)).strictMono.comp e.strictMono
  have hright :
      (fun i : Fin I.card ↦ s + finiteSetTimes I i) =
        (finiteSetTranslate s I).orderEmbOfFin hcard := by
    apply Finset.orderEmbOfFin_unique hcard
    · intro i
      exact Finset.mem_map_of_mem (addLeftEmbedding s)
        (Finset.orderEmbOfFin_mem I rfl i)
    · intro i j hij
      simpa only [add_comm] using add_lt_add_left ((finiteSetTimes I).strictMono hij) s
  apply DFunLike.ext _ _
  intro i
  exact congrFun (hleft.trans hright.symm) i

private theorem pullback_orderedPathToFiniteSet {alpha : Type*}
    (s : NNReal) (I : Finset NNReal) :
    pullbackFiniteSetTranslate (alpha := alpha) s I ∘
        orderedPathToFiniteSet (α := alpha) (finiteSetTranslate s I) =
      orderedPathToFiniteSet I ∘ FiniteOrderedTimes.restrictPath
        (finiteSetTranslateFinOrderIso s I).toOrderEmbedding := by
  funext path t
  apply congrArg path
  apply (finiteSetTimes (finiteSetTranslate s I)).injective
  have hshifted :
      finiteSetTimes (finiteSetTranslate s I)
          (((finiteSetTranslate s I).orderIsoOfFin rfl).symm
            (finiteSetTranslateEquiv s I t)) =
        s + t := by
    change (((finiteSetTranslate s I).orderIsoOfFin rfl
      (((finiteSetTranslate s I).orderIsoOfFin rfl).symm
        (finiteSetTranslateEquiv s I t)) : finiteSetTranslate s I) : NNReal) = s + t
    rw [OrderIso.apply_symm_apply]
    exact finiteSetTranslateEquiv_apply s I t
  have htimes := congrArg
    (fun times : FiniteOrderedTimes I.card ↦
      times ((I.orderIsoOfFin rfl).symm t))
    (finiteSetTimes_translate s I)
  have horiginal : finiteSetTimes I ((I.orderIsoOfFin rfl).symm t) = t := by
    change (((I.orderIsoOfFin rfl) ((I.orderIsoOfFin rfl).symm t) : I) : NNReal) = t
    exact congrArg Subtype.val ((I.orderIsoOfFin rfl).apply_symm_apply t)
  change finiteSetTimes (finiteSetTranslate s I)
      ((finiteSetTranslateFinOrderIso s I).toOrderEmbedding
        ((I.orderIsoOfFin rfl).symm t)) =
    s + finiteSetTimes I ((I.orderIsoOfFin rfl).symm t) at htimes
  rw [horiginal] at htimes
  rw [hshifted]
  exact htimes.symm

variable {alpha : Type*} [MeasurableSpace alpha]

theorem solution
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (s : NNReal) (I : Finset NNReal) :
    (finiteSetKernel P (finiteSetTranslate s I)).map
        (pullbackFiniteSetTranslate (alpha := alpha) s I) =
      (finiteSetKernel P I).comp (P s) := by
  rw [finiteSetKernel_eq_map, finiteSetKernel_eq_map, ← Kernel.map_comp_right]
  · rw [pullback_orderedPathToFiniteSet, Kernel.map_comp_right]
    · rw [hP.p2m_embedded_df60a2ab25853e30 P
          (finiteSetTimes (finiteSetTranslate s I))
          (finiteSetTranslateFinOrderIso s I).toOrderEmbedding,
        finiteSetTimes_translate, hP.p2m_embedded_0ec3a889487f427f P s,
        Kernel.map_comp]
    · exact FiniteOrderedTimes.measurable_restrictPath
        (finiteSetTranslateFinOrderIso s I).toOrderEmbedding
    · exact measurable_orderedPathToFiniteSet I
  · exact measurable_orderedPathToFiniteSet (finiteSetTranslate s I)
  · exact measurable_pullbackFiniteSetTranslate s I

end
