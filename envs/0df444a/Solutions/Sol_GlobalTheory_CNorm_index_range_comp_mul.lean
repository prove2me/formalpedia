-- Prove2me | solution 1 for GlobalTheory.CNorm.index_range_comp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:06:58.077746+00:00
-- url     : https://prove2.me/submissions/e164c59e-f297-4bf0-8266-1d5b4c8521b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexRangeKerIterateEndomorphism
import Theorems.Thm_GlobalTheory_CNorm_card_ker_comp_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution {M : Type} [CommGroup M] (f g : M →* M) :
    (f.comp g).range.index * Nat.card f.ker * Nat.card g.ker =
      f.range.index * g.range.index * Nat.card (f.comp g).ker := by
  have h1 : (f.comp g).range.index = (g.range ⊔ f.ker).index * f.range.index := by
    rw [MonoidHom.range_comp, Subgroup.index_map]
  have h2 : g.range.relIndex f.ker * (g.range ⊔ f.ker).index = g.range.index := by
    rw [← Subgroup.relIndex_sup_left, Subgroup.relIndex_mul_index le_sup_left]
  have h3 : Nat.card (g.range.subgroupOf f.ker) * g.range.relIndex f.ker = Nat.card f.ker :=
    Subgroup.card_mul_index _
  rw [h1, card_ker_comp_eq, ← h2, ← h3]
  ring
end GlobalTheory.CNorm
