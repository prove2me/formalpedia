-- Prove2me | solution 1 for GlobalTheory.CotUniv.snd_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:01:24.118954+00:00
-- url     : https://prove2.me/submissions/4e84ef05-268e-426b-9d4a-a324f3984e3f

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
variable {R₀ : Type} [CommRing R₀] {B : BX R₀} {O A : LAlg R₀} {p g : ℕ}
  {sO : LHom O A} {ε : LHom A O} {y : B.G A} {w : Fin g → B.gg}
variable {M : Type} [AddCommGroup M] [Module (O : Type) M]
namespace GlobalTheory.CotUniv
theorem _root_.solution (φ : LHom A (sqAlg O M)) (h1 : φ.comp sO = sqIncl O M) (o : (O : Type))
    (f : (A : Type)) :
    SqExt.snd (O := (O : Type)) (M := M) (φ.1 (sO.1 o * f)) =
      o • SqExt.snd (O := (O : Type)) (M := M) (φ.1 f) := by
  have h : φ.1 (sO.1 o) = SqExt.mk (M := M) o 0 := congrArg (fun ψ => ψ.1 o) h1
  rw [map_mul, h]
  refine (SqExt.snd_mul (O := (O : Type)) (M := M) _ _).trans ?_
  simp
end GlobalTheory.CotUniv
