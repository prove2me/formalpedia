-- Prove2me | solution 1 for GlobalTheory.PairingBound.val_le_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:34.244953+00:00
-- url     : https://prove2.me/submissions/57d17f7a-92cf-46d5-9aa0-10ad281783cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodDenominatorBound
import Theorems.Thm_P2M_GlobalTheory_PairingBound_ord_mul__d392fa035f29
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
theorem _root_.solution (l : ℕ) (hl : l ≠ 0) (h : (l : O) ∈ IsLocalRing.maximalIdeal O) {x y : O} (hy : y ≠ 0)
    (hxy : x ∣ y) : val_vp O l (algebraMap O K x) ≤ val_vp O l (algebraMap O K y) := by
  obtain ⟨z, rfl⟩ := hxy
  have hx : x ≠ 0 := left_ne_zero_of_mul hy
  have hz : z ≠ 0 := right_ne_zero_of_mul hy
  have inj := IsFractionRing.injective O K
  have hx' : algebraMap O K x ≠ 0 := (map_ne_zero_iff _ inj).2 hx
  have hz' : algebraMap O K z ≠ 0 := (map_ne_zero_iff _ inj).2 hz
  have hy' : algebraMap O K (x * z) ≠ 0 := (map_ne_zero_iff _ inj).2 hy
  unfold val_vp
  rw [if_neg hx', if_neg hy', map_mul, ord_mul' O hx' hz']
  refine WithTop.coe_le_coe.2 (div_le_div_of_nonneg_right ?_ (by exact_mod_cast (ord_l_pos O (K := K) l hl h).le))
  push_cast
  linarith [(by exact_mod_cast ord_alg_nonneg O z hz : (0 : ℚ) ≤ ord_vw O (algebraMap O K z))]
end GlobalTheory.PairingBound
