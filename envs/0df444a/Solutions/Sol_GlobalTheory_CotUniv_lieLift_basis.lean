-- Prove2me | solution 1 for GlobalTheory.CotUniv.lieLift_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:00:07.837079+00:00
-- url     : https://prove2.me/submissions/2c9a8ccf-94fe-48f8-9da7-6365b39416ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FstHomCompSqzOfLeibniz
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_UniversalDerivation
import Theorems.Thm_GlobalTheory_CotUniv_lieLift_mk
import Theorems.Thm_GlobalTheory_SquareZeroLeibnizPoint_sqzOfLeibniz_fst
import Theorems.Thm_GlobalTheory_SquareZeroLeibnizPoint_sqzOfLeibniz_snd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SquareZeroLeibnizPoint.sqzOfLeibniz_fst
attribute [local simp] GlobalTheory.SquareZeroLeibnizPoint.sqzOfLeibniz_snd



set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory GlobalTheory.CotUniv
variable {O : Type} [CommRing O] {p g : ℕ} {M : Type} [AddCommGroup M] [Module O M]
namespace GlobalTheory.CotUniv
theorem _root_.solution (m : Fin g → M) (hm : ∀ k, p • m k = 0) (k : Fin g) :
    lieLift O m hm (lieBasis O p g k) = m k := by
  rw [lieBasis, lieLift_mk, Finset.sum_eq_single k]
  · simp
  · intro j _ hj; simp [hj]
  · simp
end GlobalTheory.CotUniv
