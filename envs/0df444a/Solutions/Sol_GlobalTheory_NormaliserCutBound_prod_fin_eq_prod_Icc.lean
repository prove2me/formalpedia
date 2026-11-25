-- Prove2me | solution 1 for GlobalTheory.NormaliserCutBound.prod_fin_eq_prod_Icc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:01:53.177127+00:00
-- url     : https://prove2.me/submissions/7c6b6d29-e268-423d-aec2-db7edd471da0

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TwoBracketsLePowMulProdEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ProdFinEqProdIcc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
open GlobalTheory GlobalTheory.NormaliserCutBound
namespace GlobalTheory.NormaliserCutBound
theorem _root_.solution (n : ℕ) (f : Fin n → ℝ) (g : ℕ → ℝ)
    (h : ∀ s : Fin n, g (s.val + 1) = f s) : ∏ s, f s = ∏ s ∈ Finset.Icc 1 n, g s := by
  have h1 : ∏ s, f s = ∏ s : Fin n, g (s.val + 1) := Finset.prod_congr rfl (fun s _ => (h s).symm)
  rw [h1, Fin.prod_univ_eq_prod_range (fun s => g (s + 1)) n, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.prod_Ico_eq_prod_range]
  simp [add_comm]
end GlobalTheory.NormaliserCutBound
