-- Prove2me | solution 1 for GlobalTheory.Cyc.norm_pow_sub_one_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:43:57.691784+00:00
-- url     : https://prove2.me/submissions/3d8c249a-e0d9-449d-a278-a4434eaa125f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneOfNotDvd
import Theorems.Thm_GlobalTheory_Cyc_geom_sum_one_add_expand
import Theorems.Thm_GlobalTheory_Cyc_padicInt_norm_add_eq_of_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.Cyc
theorem _root_.solution (x : ℤ_[l]) (hx : ‖x - 1‖ < 1) (n : ℕ) (hn : ¬ l ∣ n) :
    ‖x ^ n - 1‖ = ‖x - 1‖ := by
  obtain ⟨z, hz⟩ := geom_sum_one_add_expand (x - 1) n
  rw [add_sub_cancel] at hz
  have hn1 : ‖(n : ℤ_[l])‖ = 1 := by
    apply le_antisymm (PadicInt.norm_le_one _)
    by_contra h
    push_neg at h
    have h' : ‖((n : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
    rw [PadicInt.norm_int_lt_one_iff_dvd] at h'
    exact hn (Int.natCast_dvd_natCast.mp h')
  have e : (n : ℤ_[l]) + (n.choose 2 : ℕ) * (x - 1) + (x - 1) ^ 2 * z
      = n + (x - 1) * ((n.choose 2 : ℕ) + (x - 1) * z) := by ring
  rw [hz, norm_mul, e, padicInt_norm_add_eq_of_lt, hn1, mul_one]
  rw [hn1, norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)) hx
end GlobalTheory.Cyc
