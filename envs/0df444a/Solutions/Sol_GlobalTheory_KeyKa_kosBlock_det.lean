-- Prove2me | solution 1 for GlobalTheory.KeyKa.kosBlock_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:31:10.663581+00:00
-- url     : https://prove2.me/submissions/7274f9b5-1d00-436a-b369-afcfdfd444f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfSupport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KosBlockMulKosD
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_det_blockDiagonal__2f448d0cb1ca


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa
variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}
namespace GlobalTheory.KeyKa
theorem _root_.solution (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R) :
    (kosBlock C P : Matrix (KIx g d N) (KIx g d N) R).det =
      (∏ j ∈ Finset.range (g + 1), (C j).det ^ g.choose j) * P.det := by
  rw [kosBlock, Matrix.det_fromBlocks_zero₂₁, ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal']
  congr 1
  rw [← Finset.powerset_univ, Finset.prod_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_congr rfl (g := fun _ => (C j).det), Finset.prod_const, Finset.card_powersetCard]
  · simp
  · intro I hI
    rw [(Finset.mem_powersetCard.mp hI).2]
end GlobalTheory.KeyKa
