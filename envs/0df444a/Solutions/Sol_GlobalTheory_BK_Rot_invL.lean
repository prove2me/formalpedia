-- Prove2me | solution 1 for GlobalTheory.BK.Rot.invL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:09:37.007982+00:00
-- url     : https://prove2.me/submissions/f1af5e78-c852-4629-9ab9-d72916dd8024

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [IsUltrametricDist K] [IsUnitBall O K]
namespace GlobalTheory.BK
namespace Rot
theorem _root_.solution {B : Subalgebra O K⟦X⟧} (h : Rot e B) : Rot e (invL l B) := by
  rintro c hc f ⟨n, hn⟩
  exact ⟨n, by simpa using h c hc _ hn⟩
end Rot
end GlobalTheory.BK
