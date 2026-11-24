-- Prove2me | solution 1 for GlobalTheory.QNorm.card_sq_eq_one_sUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:43:46.889473+00:00
-- url     : https://prove2.me/submissions/df537089-a13e-45b6-86d6-9e2041715eab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSqsTopOfFgStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsNumberFieldFgStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FinrankSUnitsNumberFieldAddOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresSUnitsNumberField
import Theorems.Thm_GlobalTheory_QNorm_mem_sUnits


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Nat.card {a : sUnits F S // a ^ 2 = 1} = 2 := by
  have hm : (-1 : Fˣ) ∈ sUnits F S := by
    rw [mem_sUnits]; intro v _; simp
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, by simp⟩, ⟨⟨-1, hm⟩, Subtype.ext (by simp)⟩, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun a : {a : sUnits F S // a ^ 2 = 1} => ((a.1.1 : Fˣ) : F)) h
    simp only [OneMemClass.coe_one, Units.val_one, Units.val_neg] at h1
    norm_num at h1
  · rw [Set.eq_univ_iff_forall]
    rintro ⟨⟨a, ha⟩, h⟩
    have h1 : (a : F) ^ 2 = 1 := by
      have := congrArg (fun a : sUnits F S => ((a.1 : Fˣ) : F)) h
      simpa using this
    rcases sq_eq_one_iff.mp h1 with h2 | h2
    · left
      exact Subtype.ext (Subtype.ext (Units.ext h2))
    · right
      exact Subtype.ext (Subtype.ext (Units.ext h2))
end GlobalTheory.QNorm
