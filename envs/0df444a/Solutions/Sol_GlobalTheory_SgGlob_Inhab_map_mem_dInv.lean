-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.map_mem_dInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:15:01.290201+00:00
-- url     : https://prove2.me/submissions/f42c26ce-7745-4ae0-8ed8-8092a6682263

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_map_mem_int
import Theorems.Thm_P2M_GlobalTheory_SgGlob_Inhab_mem_one_iff__00678d2868dc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.SgGlob.Inhab
theorem _root_.solution (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {x : E} (hx : x ∈ dInv E 1) :
    σ x ∈ dInv E 1 := by
  rw [dInv, pow_one, coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv,
    FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))] at hx ⊢
  intro a ha
  have h := hx (σ a) ((mem_one_iff' _).2 (map_mem_int σ ((mem_one_iff' _).1 ha)))
  let e : E ≃ₐ[ℚ] E := AlgEquiv.ofBijective σ.toRatAlgHom (Function.Involutive.bijective hσ)
  have he : e (x * σ a) = σ x * a := by
    change σ (x * σ a) = _
    rw [map_mul, hσ]
  rw [Algebra.traceForm_apply] at h ⊢
  rwa [← he, Algebra.trace_eq_of_algEquiv]
end GlobalTheory.SgGlob.Inhab
