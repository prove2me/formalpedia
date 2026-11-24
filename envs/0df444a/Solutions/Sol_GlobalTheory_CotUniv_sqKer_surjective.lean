-- Prove2me | solution 1 for GlobalTheory.CotUniv.sqKer_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:01:25.845824+00:00
-- url     : https://prove2.me/submissions/ed52bddb-782d-40a1-85e8-fc4e4cd8ca6d

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
variable {R₀ : Type} [CommRing R₀] (O : LAlg R₀)
  (M : Type) [AddCommGroup M] [Module (O : Type) M]
variable {O M}
variable (O M)
variable {O M}
namespace GlobalTheory.CotUniv
theorem _root_.solution : Function.Surjective (sqKer : M → (sqProj O M).ker) := fun x =>
  ⟨SqExt.snd (O := (O : Type)) (M := M) x.1,
    Subtype.ext (SqExt.ext (O := (O : Type)) (M := M) (Eq.symm x.2) rfl)⟩
end GlobalTheory.CotUniv
