-- Prove2me | solution 1 for Kac.measure_notYet_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:15:29.686147+00:00
-- url     : https://prove2.me/submissions/795d3b37-0641-4b92-933f-a822be45142d

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_notYet_succ
public import Theorems.Thm_Kac_measurableSet_notYet
attribute [local simp] Kac.notYet_succ

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {A : Set α}
namespace Kac
theorem _root_.solution (hf : MeasurePreserving f μ μ) (hA : MeasurableSet A) (n : ℕ) :
    μ (notYet f A n) = μ (A ∩ f ⁻¹' notYet f A n) + μ (notYet f A (n + 1)) := by
  have hmeas := measurableSet_notYet hf.measurable hA n
  have hsplit : f ⁻¹' notYet f A n
      = (A ∩ f ⁻¹' notYet f A n) ∪ (Aᶜ ∩ f ⁻¹' notYet f A n) := by
    rw [← union_inter_distrib_right, union_compl_self, univ_inter]
  have hdisj : Disjoint (A ∩ f ⁻¹' notYet f A n) (Aᶜ ∩ f ⁻¹' notYet f A n) :=
    Set.disjoint_left.mpr (fun x hx hx' => hx'.1 hx.1)
  calc μ (notYet f A n) = μ (f ⁻¹' notYet f A n) :=
        (hf.measure_preimage hmeas.nullMeasurableSet).symm
    _ = μ ((A ∩ f ⁻¹' notYet f A n) ∪ (Aᶜ ∩ f ⁻¹' notYet f A n)) := by rw [← hsplit]
    _ = μ (A ∩ f ⁻¹' notYet f A n) + μ (Aᶜ ∩ f ⁻¹' notYet f A n) :=
        measure_union hdisj (hA.compl.inter (hf.measurable hmeas))
    _ = μ (A ∩ f ⁻¹' notYet f A n) + μ (notYet f A (n + 1)) := by rw [notYet_succ]
end Kac
