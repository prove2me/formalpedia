-- Prove2me | solution 1 for GlobalTheory.HilbFam.TwistMem.exists_lift_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:30:31.898172+00:00
-- url     : https://prove2.me/submissions/4ac45e8e-7096-421f-bd2c-0555f38ceedf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemHilbertLatticeTwistIffLift
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam GlobalTheory.HilbFam.TwistMem
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HilbFam.TwistMem
theorem _root_.solution (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℤ,
      ((A.map (Int.cast : ℤ → ZMod N)).map (ZMod.cast : ZMod N → ℤ)).map (Int.cast : ℤ → F)
        = A.map (Int.cast : ℤ → F) + (N : F) • B.map (Int.cast : ℤ → F) := by
  have h : ∀ a : ℤ, ∃ b : ℤ, (ZMod.cast (a : ZMod N) : ℤ) = a + N * b := by
    intro a
    have h1 : ((a : ℤ) : ZMod N) = (((ZMod.cast (a : ZMod N) : ℤ) : ℤ) : ZMod N) := by
      simp
    obtain ⟨b, hb⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).1 h1
    exact ⟨b, by linarith⟩
  choose f hf using h
  refine ⟨A.map f, ?_⟩
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hf]
  push_cast
  ring
end GlobalTheory.HilbFam.TwistMem
