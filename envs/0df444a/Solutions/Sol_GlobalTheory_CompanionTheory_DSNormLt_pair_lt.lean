-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSNormLt.pair_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:36.326447+00:00
-- url     : https://prove2.me/submissions/1384f304-9bc5-435b-b26c-e90249e1b378

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_sig_anti
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_sig_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_pair_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_term_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSNormLt
open CompanionTheory.D.DSIC
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSNormLt
theorem _root_.solution (t : Fin n → Fin n → ℝ) (ht : ∀ a b, t b a = - t a b) (h1 : ∀ a b, |t a b| ≤ 1)
    {lam : Fin n → ℝ} (hl : StrictAnti lam) (c d : Fin n) (hcd : c ≠ d) (hne : t c d = - sig c d) :
    ∑ a, lam a * ((∑ b, t a b) / 2) < ∑ a, lam a * ((∑ b, sig a b) / 2) := by
  have e1 := pair_eq t ht lam
  have e2 := pair_eq sig sig_anti lam
  have hle : ∀ a b, t a b * (lam a - lam b) ≤ sig a b * (lam a - lam b) := fun a b => by
    rw [sig_mul hl.antitone]; exact term_le (h1 a b)
  have : ∑ a, ∑ b, t a b * (lam a - lam b) < ∑ a, ∑ b, sig a b * (lam a - lam b) := by
    refine Finset.sum_lt_sum (fun a _ => Finset.sum_le_sum fun b _ => hle a b) ⟨c, mem_univ _, ?_⟩
    refine Finset.sum_lt_sum (fun b _ => hle c b) ⟨d, mem_univ _, ?_⟩
    rw [hne, neg_mul, sig_mul hl.antitone]
    have : 0 < |lam c - lam d| := abs_pos.2 (sub_ne_zero.2 fun h => hcd (hl.injective h))
    linarith
  linarith
end GlobalTheory.CompanionTheory.DSNormLt
