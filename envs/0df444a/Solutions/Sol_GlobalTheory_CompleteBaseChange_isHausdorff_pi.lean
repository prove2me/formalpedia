-- Prove2me | solution 1 for GlobalTheory.CompleteBaseChange.isHausdorff_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:23.896081+00:00
-- url     : https://prove2.me/submissions/9e5cd7bd-1912-405a-863b-8b3c804408fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsPolynomialSubMem
import Theorems.Thm_GlobalTheory_CompleteBaseChange_mem_smul_top_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompleteBaseChange
namespace GlobalTheory.CompleteBaseChange
theorem _root_.solution {R M : Type*} (ι : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    {J : Ideal R} (hJ : J.FG) [IsHausdorff J M] : IsHausdorff J (ι → M) := by
  refine ⟨fun x hx => funext fun j => IsHausdorff.haus' (I := J) (x j) fun n => ?_⟩
  exact SModEq.sub_mem.2 ((mem_smul_top_pi hJ.pow _).1 (SModEq.sub_mem.1 (hx n)) j)
end GlobalTheory.CompleteBaseChange
