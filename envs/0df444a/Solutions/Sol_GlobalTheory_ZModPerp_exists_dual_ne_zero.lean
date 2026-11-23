-- Prove2me | solution 1 for GlobalTheory.ZModPerp.exists_dual_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:06.138805+00:00
-- url     : https://prove2.me/submissions/8e7849b1-e3aa-49a9-9da6-c6819be73721

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_OrthogonalFreeOfPerfectAltZmod
import Theorems.Thm_GlobalTheory_ZModPerp_dvd_of_forall_mul_eq_zero
import Theorems.Thm_GlobalTheory_ZModPerp_isPrincipalIdealRing_zmod
import Theorems.Thm_GlobalTheory_ZModPerp_baer_zmod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory GlobalTheory.ZModPerp
namespace GlobalTheory.ZModPerp
theorem _root_.solution {n : ℕ} [NeZero n] {M : Type*} [AddCommGroup M] [Module (ZMod n) M]
    {q : M} (hq : q ≠ 0) : ∃ f : Dual (ZMod n) M, f q ≠ 0 := by
  obtain ⟨x, hx⟩ := ((isPrincipalIdealRing_zmod n).principal
    (LinearMap.ker (LinearMap.toSpanSingleton (ZMod n) M q))).principal
  have hx' : ∀ a : ZMod n, a • q = 0 ↔ x ∣ a := fun a => by
    rw [← Ideal.mem_span_singleton, ← Ideal.submodule_span_eq, ← hx]
    simp
  obtain ⟨c, hc, hc0⟩ : ∃ c : ZMod n, c * x = 0 ∧ c ≠ 0 := by
    by_contra! H
    have := dvd_of_forall_mul_eq_zero x 1 fun a ha => by simp [H a ha]
    exact hq (by simpa using (hx' 1).mpr this)
  have H : ∀ a : ZMod n, a • q = 0 → (RingHom.id (ZMod n)) a • c = 0 := fun a ha => by
    obtain ⟨b, rfl⟩ := (hx' a).mp ha
    simp only [RingHom.id_apply, smul_eq_mul]
    linear_combination b * hc
  let φ := LinearPMap.mkSpanSingleton' q c H
  obtain ⟨f, hf⟩ := (baer_zmod n).extension_property φ.domain.subtype
    φ.domain.subtype_injective φ.toFun
  refine ⟨f, ?_⟩
  have := LinearMap.congr_fun hf ⟨q, Submodule.mem_span_singleton_self q⟩
  have h2 := LinearPMap.mkSpanSingleton'_apply_self q c H (Submodule.mem_span_singleton_self q)
  have h3 : f q = c := this.trans h2
  rwa [h3]
end GlobalTheory.ZModPerp
