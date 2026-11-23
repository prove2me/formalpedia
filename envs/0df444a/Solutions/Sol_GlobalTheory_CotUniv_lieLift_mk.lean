-- Prove2me | solution 1 for GlobalTheory.CotUniv.lieLift_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:32:26.458662+00:00
-- url     : https://prove2.me/submissions/806b5856-22e5-4ba3-966f-0e097c6ab9e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FstHomCompSqzOfLeibniz
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_UniversalDerivation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory GlobalTheory.CotUniv
variable {O : Type} [CommRing O] {p g : ℕ} {M : Type} [AddCommGroup M] [Module O M]
namespace GlobalTheory.CotUniv
theorem _root_.solution (m : Fin g → M) (hm : ∀ k, p • m k = 0) (l : Fin g → O) :
    lieLift O m hm (Submodule.Quotient.mk l) = ∑ k, l k • m k :=
  Fintype.linearCombination_apply O m l
end GlobalTheory.CotUniv
