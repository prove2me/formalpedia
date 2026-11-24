-- Prove2me | solution 1 for GlobalTheory.SatMinor.isUnit_int_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:31:36.536408+00:00
-- url     : https://prove2.me/submissions/d74808c9-5d11-4351-a4bf-8d169d9f9912

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitMinorOfIntegralMatrix
import Theorems.Thm_GlobalTheory_SatMinor_mem_int_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.SatMinor
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.SatMinor
theorem _root_.solution (x : PadicComplexInt p) : IsUnit x ↔ ‖(x : ℂ_[p])‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ‖((u : PadicComplexInt p) : ℂ_[p])‖ ≤ 1 := (mem_int_iff _).1 (u : PadicComplexInt p).2
    have h2 : ‖((u⁻¹ : (PadicComplexInt p)ˣ) : PadicComplexInt p).1‖ ≤ 1 :=
      (mem_int_iff _).1 ((u⁻¹ : (PadicComplexInt p)ˣ) : PadicComplexInt p).2
    have h3 : ((u : PadicComplexInt p) : ℂ_[p]) * ((u⁻¹ : (PadicComplexInt p)ˣ) : PadicComplexInt p).1 = 1 := by
      exact congrArg Subtype.val u.mul_inv
    have h4 := congrArg norm h3
    rw [norm_mul, norm_one] at h4
    nlinarith [norm_nonneg ((u : PadicComplexInt p) : ℂ_[p]),
      norm_nonneg (((u⁻¹ : (PadicComplexInt p)ˣ) : PadicComplexInt p).1)]
  · intro h
    have h0 : (x : ℂ_[p]) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
    have hm : (x : ℂ_[p])⁻¹ ∈ PadicComplexInt p := by
      rw [mem_int_iff, norm_inv, h, inv_one]
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hm⟩, Subtype.ext (by simp [h0])⟩
end GlobalTheory.SatMinor
