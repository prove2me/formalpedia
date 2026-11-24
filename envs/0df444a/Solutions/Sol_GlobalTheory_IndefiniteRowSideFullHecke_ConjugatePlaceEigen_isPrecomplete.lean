-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.isPrecomplete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:11:01.774298+00:00
-- url     : https://prove2.me/submissions/1739fb5c-a4e7-424c-9219-07848738ed54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ConjugatePlaceEigen
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ConjugatePlaceEigen_inv_p_lt_one
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ConjugatePlaceEigen_mem_iff_norm
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ConjugatePlaceEigen_smodEq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Out
open Ideal
variable (p : ℕ) [hp : Fact p.Prime]
namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen
theorem _root_.solution : IsPrecomplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := by
  refine ⟨fun f hf => ?_⟩
  have h : ∀ {m n : ℕ}, m ≤ n → ‖(f m : ℂ_[p]) - (f n : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ m :=
    fun hmn => (smodEq_iff p _ _ _).1 (hf hmn)
  have hc : CauchySeq fun n => (f n : ℂ_[p]) := by
    refine cauchySeq_of_le_geometric (p : ℝ)⁻¹ 1 (inv_p_lt_one p) fun n => ?_
    rw [dist_eq_norm, _root_.one_mul]
    exact h (Nat.le_succ n)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  have hm : ∀ m : ℕ, ‖(f m : ℂ_[p]) - L‖ ≤ (p : ℝ)⁻¹ ^ m := fun m =>
    le_of_tendsto ((tendsto_const_nhds.sub hL).norm)
      ((Filter.eventually_ge_atTop m).mono fun n hn => h hn)
  have hLO : L ∈ 𝓞_ℂ_[p] := by
    rw [mem_iff_norm]
    exact le_of_tendsto hL.norm
      (Filter.Eventually.of_forall fun n => (mem_iff_norm p _).1 (f n).2)
  exact ⟨⟨L, hLO⟩, fun n => (smodEq_iff p n _ _).2 (hm n)⟩
end GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen
