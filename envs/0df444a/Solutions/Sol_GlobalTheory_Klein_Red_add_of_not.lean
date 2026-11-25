-- Prove2me | solution 1 for GlobalTheory.Klein.Red.add_of_not
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:12:45.696739+00:00
-- url     : https://prove2.me/submissions/45ea17b3-787f-4b21-84fe-e9be16a7ec4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReductionSetSubgroup
import Theorems.Thm_GlobalTheory_Klein_chord_norm_le_one
import Theorems.Thm_GlobalTheory_Klein_norm_two_of_ne
import Theorems.Thm_GlobalTheory_Klein_Red_neg
import Theorems.Thm_GlobalTheory_Klein_Red_add_lattice
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
import Theorems.Thm_GlobalTheory_weierstrassP_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticePointEquiv_mk



set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
open GlobalTheory GlobalTheory.Klein
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.Klein
namespace Red
theorem _root_.solution {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r u w : ℂ} (hg : Good ι L r)
    (hu : ¬ Red ι L r u) (hw : Red ι L r w) : Red ι L r (u + w) := by
  by_cases hL : u ∈ L.lattice
  · rw [add_comm]; exact hw.add_lattice hL
  have ha : 1 < ‖ι (L.weierstrassP u - r)‖ := not_le.1 fun h => hu ⟨hL, h⟩
  have hne : L.weierstrassP u ≠ L.weierstrassP w := fun h => by
    rw [h] at ha; exact absurd hw.2 (not_le.2 ha)
  refine ⟨fun h => hu ?_, ?_⟩
  · have := hw.neg.add_lattice h
    rwa [show -w + (u + w) = u by ring] at this
  obtain ⟨hp, hk₂, hk₁, hk₀, -⟩ := hg
  have hs := (GlobalTheory.weierstrassP_add L hL hw.1 hne).1
  have e1 := L.derivWeierstrassP_sq u hL
  have e2 := L.derivWeierstrassP_sq w hw.1
  have hd := sub_ne_zero.2 hne
  have key : ∀ x y : ℂ, y ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃ →
      ι y ^ 2 = 4 * ι (x - r) ^ 3 + ι (12 * r) * ι (x - r) ^ 2 + ι (12 * r ^ 2 - L.g₂) * ι (x - r)
        + ι (4 * r ^ 3 - L.g₂ * r - L.g₃) := fun x y h => by
    have : y ^ 2 = 4 * (x - r) ^ 3 + (12 * r) * (x - r) ^ 2 + (12 * r ^ 2 - L.g₂) * (x - r)
        + (4 * r ^ 3 - L.g₂ * r - L.g₃) := by linear_combination h
    rw [← map_pow, this, map_add, map_add, map_add, map_mul ι 4, map_mul ι (12 * r),
      map_mul ι _ (x - r), map_pow, map_pow, map_ofNat]
  refine chord_norm_le_one (norm_two_of_ne hp) ha hw.2 hk₂ hk₁ hk₀ (key _ _ e1) (key _ _ e2) ?_
  have : 4 * ((L.weierstrassP u - r) - (L.weierstrassP w - r)) ^ 2 * (L.weierstrassP (u + w) - r)
      = (L.derivWeierstrassP u - L.derivWeierstrassP w) ^ 2
        - (4 * ((L.weierstrassP u - r) + (L.weierstrassP w - r)) + 12 * r)
          * ((L.weierstrassP u - r) - (L.weierstrassP w - r)) ^ 2 := by
    rw [hs]; field_simp; ring
  have := congrArg ι this
  simpa only [map_mul, map_sub, map_add, map_pow, map_ofNat] using this
end Red
end GlobalTheory.Klein
