-- Prove2me | solution 1 for GlobalTheory.CotUniv.tg_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:19:16.884976+00:00
-- url     : https://prove2.me/submissions/0eaa0582-e3e4-4232-a259-226367cacab9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FstHomCompSqzOfLeibniz
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_UniversalDerivation
import Theorems.Thm_GlobalTheory_CotUniv_smul_sqKer
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
variable {M' : Type} [AddCommGroup M'] [Module (O : Type) M']
namespace GlobalTheory.CotUniv
theorem _root_.solution {E : Type} [CommRing E] (Ac : OAct B O p E) (a : E) (gb : Module.Basis (Fin g) R₀ B.gg)
    (m : Fin g → M) (hm : ∀ k, p • m k = 0) (x : torP B p (sqAlg O M))
    (hx : (x : B.G (sqAlg O M)) = tgPt B O gb m) :
    (Ac.act a (sqAlg O M) (sqIncl O M) x : B.G (sqAlg O M)) =
      tgPt B O gb fun k' => ∑ k, algebraMap R₀ (O : Type) (gb.repr (Ac.actL a (gb k)) k') • m k := by
  have hk : ∀ k, p • (sqKer (m k) : (sqProj O M).ker) = 0 := fun k => by
    rw [← map_nsmul, hm, map_zero]
  have hx' : x = ∑ k, (⟨B.tg (sqProj O M) (sqProj_sqZero O M) (gb k ⊗ₜ[R₀] sqKer (m k)),
      tg_torP B p _ _ _ _ (hk k)⟩ : torP B p (sqAlg O M)) := by
    refine Subtype.ext ?_
    rw [hx, AddSubmonoidClass.coe_finset_sum, tgPt, map_sum]
  rw [hx', map_sum, AddSubmonoidClass.coe_finset_sum]
  simp only [Ac.act_tg a (sqIncl O M) (sqProj O M) (sqProj_sqZero O M) _ _ (hk _)]
  rw [← map_sum, tgPt]
  congr 1
  simp only [map_sum, TensorProduct.tmul_sum, ← smul_sqKer, ← TensorProduct.smul_tmul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← TensorProduct.sum_tmul, gb.sum_repr]
end GlobalTheory.CotUniv
