-- Prove2me | solution 1 for GlobalTheory.ThickeningDetermines.secIdeal_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:34:46.677814+00:00
-- url     : https://prove2.me/submissions/51cd81e4-a86d-4c3b-bf01-1f62bfc5ad77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ThickeningDetermines
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Cartier EffCartierData TopologicalSpace
variable {X Y : Scheme.{0}} {N : LB X}
namespace GlobalTheory.ThickeningDetermines
theorem _root_.solution (hN : N.IsLB) (s : N.Sec) (φ : Y ⟶ X) [QuasiCompact φ]
    (h : ∀ j, (φ.app _).hom (s.f j) = 0) : secIdeal hN s ≤ φ.ker := by
  have loc : ∀ x : X, ∃ (W : X.affineOpens) (i : N.ι), x ∈ W.1 ∧ W.1 ≤ N.U i := fun x ↦ by
    obtain ⟨i, hi⟩ := exists_mem_chart hN x
    obtain ⟨W, hxW, hW⟩ := exists_affine_le hi
    exact ⟨W, i, hxW, hW⟩
  choose W i hx hW using loc
  refine Scheme.IdealSheafData.le_of_iSup_eq_top W
    (eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hx x⟩) fun x ↦ ?_
  refine (ideal_locIdeal _ _ _ _ (W x) (i x) (hW x)).trans_le ?_
  rw [Ideal.span_singleton_le_iff_mem, Scheme.Hom.ker_apply, RingHom.mem_ker, app_resG, h,
    map_zero]
end GlobalTheory.ThickeningDetermines
