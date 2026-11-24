-- Prove2me | solution 1 for GlobalTheory.CotUniv.snd_leibniz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:01:23.342037+00:00
-- url     : https://prove2.me/submissions/d526805f-e271-4e45-9845-1196a76617d3

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
variable {R₀ : Type} [CommRing R₀] {B : BX R₀} {O A : LAlg R₀} {p g : ℕ}
  {sO : LHom O A} {ε : LHom A O} {y : B.G A} {w : Fin g → B.gg}
variable {M : Type} [AddCommGroup M] [Module (O : Type) M]
namespace GlobalTheory.CotUniv
theorem _root_.solution (φ : LHom A (sqAlg O M)) (h2 : (sqProj O M).comp φ = ε) (f f' : (A : Type)) :
    SqExt.snd (O := (O : Type)) (M := M) (φ.1 (f * f')) =
      ε.1 f • SqExt.snd (O := (O : Type)) (M := M) (φ.1 f') +
        ε.1 f' • SqExt.snd (O := (O : Type)) (M := M) (φ.1 f) := by
  rw [map_mul, ← h2]
  exact SqExt.snd_mul (O := (O : Type)) (M := M) _ _
end GlobalTheory.CotUniv
