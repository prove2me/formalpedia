-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgSplit.decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:52.182658+00:00
-- url     : https://prove2.me/submissions/e717f462-178b-476a-89d8-5c9991d525e3

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgSplit
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}
namespace GlobalTheory.CompanionTheory.RgSplit
theorem _root_.solution (hh : IsHerm s h) (δ : L) (e f x : V) :
    x = ca hh δ f x • e + cb hh δ e x • f + pr hh δ e f x := by
  rw [pr_apply]; abel
end GlobalTheory.CompanionTheory.RgSplit
