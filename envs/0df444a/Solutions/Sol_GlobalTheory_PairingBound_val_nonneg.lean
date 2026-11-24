-- Prove2me | solution 1 for GlobalTheory.PairingBound.val_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:19:51.025146+00:00
-- url     : https://prove2.me/submissions/6c6b2829-e77e-4174-8f56-fd082aabe514

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodDenominatorBound
import Theorems.Thm_GlobalTheory_PairingBound_ord_alg_nonneg
import Theorems.Thm_GlobalTheory_PairingBound_ord_l_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.PairingBound
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]
namespace GlobalTheory.PairingBound
theorem _root_.solution (l : ℕ) (hl : l ≠ 0) (h : (l : O) ∈ IsLocalRing.maximalIdeal O) (x : O) :
    0 ≤ val_vp O l (algebraMap O K x) := by
  unfold val_vp
  split_ifs with hx
  · exact le_top
  · have hx' : x ≠ 0 := by rintro rfl; exact hx (map_zero _)
    exact WithTop.coe_le_coe.2 (div_nonneg (by exact_mod_cast ord_alg_nonneg O x hx')
      (by exact_mod_cast (ord_l_pos O (K := K) l hl h).le))
end GlobalTheory.PairingBound
