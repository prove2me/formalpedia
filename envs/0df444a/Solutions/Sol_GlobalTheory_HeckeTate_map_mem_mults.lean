-- Prove2me | solution 1 for GlobalTheory.HeckeTate.map_mem_mults
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:50:37.526149+00:00
-- url     : https://prove2.me/submissions/5b56e7b4-1f11-425c-9169-6fe438b7ae71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
import Theorems.Thm_GlobalTheory_HeckeTate_mem_mults

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
theorem _root_.solution {N : R} (u : M →ₗ[R] M') {x : M} (hx : x ∈ mults M N) : u x ∈ mults M' N := by
  obtain ⟨y, rfl⟩ := mem_mults.1 hx
  exact mem_mults.2 ⟨u y, map_smul u _ _⟩
end GlobalTheory.HeckeTate
