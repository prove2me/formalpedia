-- Prove2me | solution 1 for GlobalTheory.HeckeTate.IsUnimod.ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:50:05.877685+00:00
-- url     : https://prove2.me/submissions/94b6e4f2-16eb-4d21-9688-0d5e49e5b675

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_skew
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_bij

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
theorem _root_.solution (h : IsUnimod σ B) {x y : M} (e : ∀ a, B a x = B a y) : x = y :=
  h.bij.1 (AddMonoidHom.ext fun a => by rw [h.skew x, h.skew y, e])
end IsUnimod
end GlobalTheory.HeckeTate
