-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.map_zeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:49:01.07202+00:00
-- url     : https://prove2.me/submissions/fb03722e-970f-4a30-94d7-cd82430494a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_PhiMod_lphi_apply
import Theorems.Thm_GlobalTheory_BK_PhiMod_zeta_mem_uPow
import Theorems.Thm_GlobalTheory_BK_PhiMod_zeta_eq
import Theorems.Thm_GlobalTheory_BK_PhiMod_zeta_unique

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
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]
open GlobalTheory.BK.PhiMod
variable (P : PhiMod O K l e a ι)
variable {P}
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution {Q : PhiMod O K l e a κ} (g : Vec K a ι →ₗ[K] Vec K a κ)
    (h1 : ∀ v ∈ uPow K a ι 1, g v ∈ uPow K a κ 1) (hg : ∀ v, g (P.phi v) = Q.phi (g v))
    (hN : ∀ v, g (P.conn v) = Q.conn (g v)) (y : Vec K a ι) : g (P.zeta y) = Q.zeta (g y) :=
  Q.zeta_unique (h1 _ (P.zeta_mem_uPow y)) (by
    conv_lhs => rw [zeta_eq, lphi_apply, map_smul, hg, map_sub, hN]
    rfl)
end GlobalTheory.BK.PhiMod
