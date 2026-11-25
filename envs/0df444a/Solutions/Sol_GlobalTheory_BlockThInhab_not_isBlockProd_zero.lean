-- Prove2me | solution 1 for GlobalTheory.BlockThInhab.not_isBlockProd_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:31:52.349344+00:00
-- url     : https://prove2.me/submissions/feb32d8e-07f1-4d01-b918-fa0aa4e96556

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_IsBlockProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NotIsBlockProdZero
import Theorems.Thm_GlobalTheory_BlockThInhab_poly_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BlockThInhab
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.BlockTh
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (n : ℕ)
namespace GlobalTheory.BlockThInhab
theorem _root_.solution (K : Type) [Field K] : ¬ IsBlockProd (0 : MvPolynomial (LtN Dw n) K) := by
  rintro ⟨nb, bs, -, h⟩
  exact Finset.prod_ne_zero_iff.2 (fun j _ => poly_ne_zero Dw n K (bs j)) h.symm
end GlobalTheory.BlockThInhab
