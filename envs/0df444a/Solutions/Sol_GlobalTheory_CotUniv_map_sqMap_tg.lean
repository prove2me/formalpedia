-- Prove2me | solution 1 for GlobalTheory.CotUniv.map_sqMap_tg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:00:10.756978+00:00
-- url     : https://prove2.me/submissions/c085b32a-4ae7-4ff4-ae4e-0c8053706422

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
variable {M' : Type} [AddCommGroup M'] [Module (O : Type) M']
namespace GlobalTheory.CotUniv
theorem _root_.solution (B : BX R₀) {ι : Type} [Fintype ι] (w : ι → B.gg) (m : ι → M)
    (u : M →ₗ[(O : Type)] M') :
    B.map (sqMap u) (B.tg (sqProj O M) (sqProj_sqZero O M) (∑ k, w k ⊗ₜ[R₀] sqKer (m k))) =
      B.tg (sqProj O M') (sqProj_sqZero O M') (∑ k, w k ⊗ₜ[R₀] sqKer (u (m k))) := by
  rw [← B.tg_nat (sqProj O M) (sqProj O M') (sqProj_sqZero O M) (sqProj_sqZero O M') (sqMap u)
    (fun _ h => h), map_sum]
  rfl
end GlobalTheory.CotUniv
