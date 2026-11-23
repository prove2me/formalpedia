-- Prove2me | solution 1 for GlobalTheory.HeckeTate.IsUnimod.bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:37.571999+00:00
-- url     : https://prove2.me/submissions/ca77feb9-fb73-46b3-bf7c-2a9847a48b07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HeckeTate
variable {R : Type} [CommRing R] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
variable {σ : R ≃+* R} {B : M →+ M →+ ℤ} {B' : M' →+ M' →+ ℤ}
namespace GlobalTheory.HeckeTate
namespace IsUnimod
theorem _root_.solution (h : IsUnimod σ B) : Function.Bijective B := h.2.2
end IsUnimod
end GlobalTheory.HeckeTate
