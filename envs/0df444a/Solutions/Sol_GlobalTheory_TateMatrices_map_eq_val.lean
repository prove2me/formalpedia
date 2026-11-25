-- Prove2me | solution 1 for GlobalTheory.TateMatrices.map_eq_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:03:51.269163+00:00
-- url     : https://prove2.me/submissions/8d47b18a-20c7-4e2b-94d3-037f702c1d2c

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_CharR
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsTateMatricesLink
import Theorems.Thm_GlobalTheory_TateMatrices_sub_val_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2
noncomputable section
open GlobalTheory
open GlobalTheory.TateMatrices
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.TateMatrices
theorem _root_.solution {S : Type} [CommRing S] (φ : ℤ_[p] →+* S) (n : ℕ) (h : (p : S) ^ n = 0)
    (c : ℤ_[p]) : φ c = ((PadicInt.toZModPow n c).val : S) := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (sub_val_mem n c)
  have h2 := congrArg φ hb
  rw [map_mul, map_pow, map_natCast, h, mul_zero, map_sub, map_natCast] at h2
  exact (sub_eq_zero.1 h2.symm)
end GlobalTheory.TateMatrices
