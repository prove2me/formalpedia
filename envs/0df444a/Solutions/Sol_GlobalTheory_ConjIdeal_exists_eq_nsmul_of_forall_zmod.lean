-- Prove2me | solution 1 for GlobalTheory.ConjIdeal.exists_eq_nsmul_of_forall_zmod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:18.434516+00:00
-- url     : https://prove2.me/submissions/09f30203-83c7-48f5-8a75-6a569d1104fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqNsmulOfForallAddChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ConjIdeal
namespace GlobalTheory.ConjIdeal
theorem _root_.solution {X : Type*} [AddCommGroup X] [Module.Free ℤ X] (M : ℕ) (v : X)
    (h : ∀ t : X →+ ZMod M, t v = 0) : ∃ z : X, v = M • z := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  have hd : ∀ i, (M : ℤ) ∣ b.repr v i := fun i => by
    have := h ((Int.castAddHom (ZMod M)).comp (b.coord i).toAddMonoidHom)
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using this
  refine ⟨b.repr.symm ((b.repr v).mapRange (fun n => n / (M : ℤ)) (by simp)), ?_⟩
  apply b.repr.injective
  ext i
  simp [Int.mul_ediv_cancel' (hd i)]
end GlobalTheory.ConjIdeal
