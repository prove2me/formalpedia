-- Prove2me | solution 1 for Kac.measure_firstHit_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:24:51.556737+00:00
-- url     : https://prove2.me/submissions/524b8c3a-7814-40cd-8e66-1bba052ea703

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_notYet_zero
public import Theorems.Thm_Kac_notYet_succ
public import Theorems.Thm_Kac_notYet_eq_union
public import Theorems.Thm_Kac_disjoint_firstHit_notYet_succ
public import Theorems.Thm_Kac_firstHit_succ
public import Theorems.Thm_Kac_measurableSet_notYet
attribute [local simp] Kac.notYet_zero
attribute [local simp] Kac.notYet_succ

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {A : Set α}
namespace Kac
theorem _root_.solution (hf : MeasurePreserving f μ μ) (hA : MeasurableSet A) (hAfin : μ A ≠ ∞)
    (n : ℕ) : μ (firstHit f A n) = μ (A ∩ f ⁻¹' notYet f A n) := by
  have hfm := hf.measurable
  have hE : ∀ k, MeasurableSet (firstHit f A k) := fun k =>
    (measurableSet_notYet hfm hA k).inter (hfm.iterate k hA)
  induction n with
  | zero => simp [firstHit]
  | succ n ih =>
    -- the preimage of `firstHit n` splits into the points of `A` returning at time `n + 1`, and
    -- `firstHit (n + 1)`
    have h1 : μ (firstHit f A n)
        = μ (A ∩ f ⁻¹' firstHit f A n) + μ (firstHit f A (n + 1)) := by
      rw [firstHit_succ, ← hf.measure_preimage (hE n).nullMeasurableSet]
      have hsplit : f ⁻¹' firstHit f A n
          = (A ∩ f ⁻¹' firstHit f A n) ∪ (Aᶜ ∩ f ⁻¹' firstHit f A n) := by
        rw [← union_inter_distrib_right, union_compl_self, univ_inter]
      conv_lhs => rw [hsplit]
      exact measure_union (Set.disjoint_left.mpr fun x hx hx' => hx'.1 hx.1)
        (hA.compl.inter (hfm (hE n)))
    -- the points of `A` not returned within `n` steps lose the same set
    have h2 : μ (A ∩ f ⁻¹' notYet f A n)
        = μ (A ∩ f ⁻¹' firstHit f A n) + μ (A ∩ f ⁻¹' notYet f A (n + 1)) := by
      conv_lhs => rw [notYet_eq_union n, preimage_union, inter_union_distrib_left]
      exact measure_union
        (((disjoint_firstHit_notYet_succ n).preimage f).mono inter_subset_right
          inter_subset_right)
        (hA.inter (hfm (measurableSet_notYet hfm hA (n + 1))))
    have hfin : μ (A ∩ f ⁻¹' firstHit f A n) ≠ ∞ :=
      ne_top_of_le_ne_top hAfin (measure_mono inter_subset_left)
    rw [ih, h2] at h1
    exact ((add_right_inj_of_ne_top hfin).mp h1).symm
end Kac
