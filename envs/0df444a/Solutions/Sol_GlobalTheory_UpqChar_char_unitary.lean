-- Prove2me | solution 1 for GlobalTheory.UpqChar.char_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:43:31.433832+00:00
-- url     : https://prove2.me/submissions/99aeca69-936c-4503-a975-9f9fef92d667

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupContinuousCharEqDetZpowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryPQContinuousCharacterEqDetPowProd
import Theorems.Thm_GlobalTheory_T_unitaryGroup_continuous_char_eq_det_zpow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.UpqChar
namespace GlobalTheory.UpqChar
theorem _root_.solution {p : ℕ} (f : Matrix.unitaryGroup (Fin p) ℂ → ℂ)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hn : ∀ a, ‖f a‖ = 1) (hc : Continuous f) :
    ∃ x : ℤ, ∀ a, f a = (Matrix.det (a : Matrix (Fin p) (Fin p) ℂ)) ^ x := by
  have hone : f 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    have hne : f 1 ≠ 0 := fun h0 => by simpa [h0] using hn 1
    exact mul_left_cancel₀ hne (by rw [mul_one]; exact h.symm)
  have hmem : ∀ a, f a ∈ Submonoid.unitSphere ℂ := fun a => mem_sphere_zero_iff_norm.2 (hn a)
  let c : Matrix.unitaryGroup (Fin p) ℂ →* Circle :=
    { toFun := fun a => ⟨f a, hmem a⟩
      map_one' := Circle.ext hone
      map_mul' := fun a b => Circle.ext (hmul a b) }
  have hcont : Continuous c := Continuous.subtype_mk hc hmem
  obtain ⟨m, hm⟩ := GlobalTheory.T.unitaryGroup_continuous_char_eq_det_zpow p c hcont
  exact ⟨m, fun a => hm a⟩
end GlobalTheory.UpqChar
