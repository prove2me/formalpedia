-- Prove2me | solution 1 for GlobalTheory.CotUniv.sqMap_comp_sO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:01:26.532838+00:00
-- url     : https://prove2.me/submissions/6bed5fb6-a5b2-40ec-ad83-0cc2676b2fcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FstHomCompSqzOfLeibniz
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_UniversalDerivation
import Theorems.Thm_GlobalTheory_CotUniv_lhom_ext

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
variable {M' : Type} [AddCommGroup M'] [Module (O : Type) M']
namespace GlobalTheory.CotUniv
theorem _root_.solution (φ : LHom A (sqAlg O M)) (h1 : φ.comp sO = sqIncl O M)
    (u : M →ₗ[(O : Type)] M') : ((sqMap u).comp φ).comp sO = sqIncl O M' :=
  lhom_ext fun o => by
    have h : φ.1 (sO.1 o) = SqExt.mk (M := M) o 0 := congrArg (fun ψ => ψ.1 o) h1
    change (sqMap u).1 (φ.1 (sO.1 o)) = _
    rw [h]
    exact SqExt.ext (O := (O : Type)) (M := M') rfl (map_zero u)
end GlobalTheory.CotUniv
