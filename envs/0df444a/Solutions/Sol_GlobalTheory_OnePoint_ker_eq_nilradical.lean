-- Prove2me | solution 1 for GlobalTheory.OnePoint.ker_eq_nilradical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:16:09.426334+00:00
-- url     : https://prove2.me/submissions/4e377d9d-7075-45be-b47f-33c07710dbe9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
import Theorems.Thm_GlobalTheory_OnePoint_nilradical_le_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
namespace GlobalTheory.OnePoint
theorem _root_.solution {T X : Scheme.{u}} [IsReduced T] (g : T ⟶ X) [QuasiCompact g]
    [Surjective g] : g.ker = X.nilradical := by
  refine le_antisymm ?_ (nilradical_le_ker g)
  rw [← Scheme.IdealSheafData.vanishingIdeal_top,
    ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
  intro x _
  obtain ⟨t, rfl⟩ := g.surjective x
  exact g.range_subset_ker_support ⟨t, rfl⟩
end GlobalTheory.OnePoint
