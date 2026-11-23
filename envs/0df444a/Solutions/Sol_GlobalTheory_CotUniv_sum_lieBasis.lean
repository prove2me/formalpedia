-- Prove2me | solution 1 for GlobalTheory.CotUniv.sum_lieBasis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:44.330396+00:00
-- url     : https://prove2.me/submissions/cf7877f1-2199-41a8-ac79-898a22eb6313

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FstHomCompSqzOfLeibniz
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_UniversalDerivation
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
theorem _root_.solution (l : Fin g → O) :
    ∑ k, l k • lieBasis O p g k = Submodule.Quotient.mk l := by
  have h : l = ∑ k, l k • (Pi.single k 1 : Fin g → O) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [h]
  rw [← Submodule.mkQ_apply, map_sum]
  rfl
end GlobalTheory.CotUniv
