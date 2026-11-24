-- Prove2me | solution 1 for GlobalTheory.BK.frob_mem_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:16:02.847709+00:00
-- url     : https://prove2.me/submissions/d503a141-a9f7-4e4d-8a12-350fef8a9907

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Theorems.Thm_GlobalTheory_BK_wS_anti
import Theorems.Thm_GlobalTheory_BK_frob_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]
variable {O K}
namespace GlobalTheory.BK
theorem _root_.solution (l : ℕ) [Fact l.Prime] {e : ℕ} {f : K⟦X⟧} (hf : f ∈ S O K e) :
    frob K l f ∈ S O K e :=
  ⟨fun n => (frob_bound l (wS_nonneg e) (fun _ _ => wS_anti e) f n).trans (hf.1 _),
    squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n))
      (frob_bound l (wS_nonneg e) (fun _ _ => wS_anti e) f)
      (hf.2.comp (Nat.tendsto_div_const_atTop (Fact.out : l.Prime).ne_zero))⟩
end GlobalTheory.BK
