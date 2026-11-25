-- Prove2me | solution 1 for GlobalTheory.UTrans.TvKill.exists_dual_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:35.117723+00:00
-- url     : https://prove2.me/submissions/d882ef23-57b2-4d89-8c04-c54fa2aca713

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryCharacterKillsUnitaryTransvections
import Theorems.Thm_GlobalTheory_UTrans_TvKill_exists_dual
import Theorems.Thm_GlobalTheory_UTrans_Calc_hf_add_left
import Theorems.Thm_GlobalTheory_UTrans_Calc_hf_add_right
import Theorems.Thm_GlobalTheory_UTrans_Calc_hf_conj
import Theorems.Thm_GlobalTheory_UTrans_Calc_hf_smul_left
import Theorems.Thm_GlobalTheory_UTrans_Calc_hf_smul_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.TvKill
open GlobalTheory.UTrans GlobalTheory.UTrans.Calc
variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.UTrans.TvKill
theorem _root_.solution [CharZero E] (hG : IsHerm σ G) {x : Fin n → E} (hx : x ≠ 0)
    (hxx : hf σ G x x = 0) : ∃ y, hf σ G x y = 1 ∧ hf σ G y y = 0 := by
  obtain ⟨y, hy⟩ := exists_dual hG hx
  have hyx : hf σ G y x = 1 := by rw [← hf_conj σ G hG.invol hG.herm, hy, map_one]
  have hc : σ (-(hf σ G y y / 2)) = -(hf σ G y y / 2) := by
    rw [map_neg, map_div₀, hf_conj σ G hG.invol hG.herm, map_ofNat]
  refine ⟨y + (-(hf σ G y y / 2)) • x, ?_, ?_⟩
  · rw [hf_add_right, hf_smul_right, hxx, hy]; ring
  · simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hc, hxx, hy, hyx]
    ring
end GlobalTheory.UTrans.TvKill
