-- Prove2me | solution 1 for GlobalTheory.Mem.posDirichlet_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:20:48.668888+00:00
-- url     : https://prove2.me/submissions/f0a0d28b-db42-448d-a12c-320b4511c993

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRay
import Theorems.Thm_GlobalTheory_Mem_sum_characters_nonneg
import Theorems.Thm_GlobalTheory_Mem_norm_character
import Theorems.Thm_GlobalTheory_Mem_natCast_pow_cpow_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem
namespace GlobalTheory.Mem
theorem _root_.solution {G : Type} [CommGroup G] [Fintype G] [Fintype (G →* ℂˣ)] (g : G)
    {q : ℕ} (hq : 2 ≤ q) :
    PosDirichlet (fun s => ∑ χ : G →* ℂˣ, -Complex.log (1 - (χ g : ℂ) * (q : ℂ) ^ (-s))) := by
  refine ⟨ℕ, fun k => (∑ χ : G →* ℂˣ, (χ (g ^ k) : ℂ)).re / k, fun k => q ^ k,
    fun k => div_nonneg (Complex.nonneg_iff.1 (sum_characters_nonneg _)).1 (Nat.cast_nonneg _),
    fun k => pow_ne_zero _ (by omega), fun s hs => ?_⟩
  have h1 : ∀ χ : G →* ℂˣ, ‖(χ g : ℂ) * (q : ℂ) ^ (-s)‖ < 1 := by
    intro χ
    rw [norm_mul, norm_character, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast hq
    · simp only [neg_re]; linarith
  have h2 := hasSum_sum (s := Finset.univ)
    (fun χ _ => Complex.hasSum_taylorSeries_neg_log (h1 χ))
  convert h2 using 2 with k
  have h3 : (((∑ χ : G →* ℂˣ, (χ (g ^ k) : ℂ)).re : ℝ) : ℂ) = ∑ χ : G →* ℂˣ, (χ (g ^ k) : ℂ) :=
    (Complex.eq_re_of_ofReal_le (r := 0) (by simpa using sum_characters_nonneg (g ^ k))).symm
  rw [Complex.ofReal_div, h3, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Nat.cast_pow, natCast_pow_cpow_comm, mul_pow, map_pow, Units.val_pow_eq_pow_val]
  push_cast
  ring
end GlobalTheory.Mem
