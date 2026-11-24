-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.NearZero.NL_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:10:19.277985+00:00
-- url     : https://prove2.me/submissions/283381cf-45b9-4615-877d-7afae24d9b1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleTraceAddCharNormEqOneNearZero
import Theorems.Thm_GlobalTheory_JR_WeilQuad_NearZero_finite_K_L

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.NearZero
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.WeilQuad.NearZero
theorem _root_.solution [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) : A.NL (0 : A.L) = 0 := by
  letI : Field A.K := hK.toField
  have := finite_K_L A
  haveI : Nontrivial A.L := ⟨hL.exists_pair_ne⟩
  exact Algebra.norm_zero
end GlobalTheory.JR.WeilQuad.NearZero
