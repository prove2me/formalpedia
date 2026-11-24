-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.isHausdorff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:12:38.747834+00:00
-- url     : https://prove2.me/submissions/eb201da0-bad4-4dc0-bae5-ca8a05145e41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ConjugatePlaceEigen
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ConjugatePlaceEigen_smodEq_iff
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ConjugatePlaceEigen_tendsto_inv_p_pow

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
theorem _root_.solution : IsHausdorff (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := by
  refine ⟨fun x hx => ?_⟩
  have h : ∀ n : ℕ, ‖(x : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ n := fun n => by
    simpa using (smodEq_iff p n x 0).1 (hx n)
  have h0 : ‖(x : ℂ_[p])‖ ≤ 0 :=
    ge_of_tendsto (tendsto_inv_p_pow p) (Filter.Eventually.of_forall h)
  exact Subtype.ext (norm_le_zero_iff.1 h0)
end GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen
