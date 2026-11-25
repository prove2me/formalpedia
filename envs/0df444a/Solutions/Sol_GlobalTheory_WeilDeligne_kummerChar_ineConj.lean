-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.kummerChar_ineConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:21:51.82287+00:00
-- url     : https://prove2.me/submissions/329c79c8-c79d-4905-8c84-ba47360daf06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
import Theorems.Thm_GlobalTheory_WeilDeligne_cycZ_weil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.WeilDeligne
theorem _root_.solution {h : IsPlaceOver A w} (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (a : Eˣ)
    (g : Weil h) (σ : Ine (F := E) A) :
    ((kummerChar h hl a (ineConj g σ)).toAdd : ℚ_[l]) =
      ((normV w : ℕ) : ℚ_[l]) ^ deg g * ((kummerChar h hl a σ).toAdd : ℚ_[l]) := by
  have h0 := kummer_mul l a (g : G E Ω) (g : G E Ω)⁻¹
  rw [mul_inv_cancel, kummer_one] at h0
  rw [toAdd_kummerChar, toAdd_kummerChar, coe_ineConj, mul_assoc, kummer_mul, kummer_mul,
    cycZ_of_mem_Ine h hl σ.2, Units.val_one, one_mul, mul_add, add_left_comm, ← h0, add_zero,
    ← cycZ_weil hl g]
  push_cast; rfl
end GlobalTheory.WeilDeligne
