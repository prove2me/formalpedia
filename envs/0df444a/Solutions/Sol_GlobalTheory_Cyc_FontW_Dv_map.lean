-- Prove2me | solution 1 for GlobalTheory.Cyc.FontW.Dv_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:53.85737+00:00
-- url     : https://prove2.me/submissions/d61ea340-001d-4413-927d-06b563e41c8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRight
import Theorems.Thm_GlobalTheory_Cyc_FontW_mem_Dv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.FontW
namespace GlobalTheory.Cyc.FontW
theorem _root_.solution {l r : ℕ} {M M' F : Type*} [AddCommGroup M] [AddCommGroup M'] [FunLike F M M']
    [AddMonoidHomClass F M M'] (f : F) {x : M} (hx : x ∈ Dv l r M) : f x ∈ Dv l r M' := by
  obtain ⟨y, rfl⟩ := mem_Dv.1 hx
  exact mem_Dv.2 ⟨f y, (map_nsmul f _ _).symm⟩
end GlobalTheory.Cyc.FontW
