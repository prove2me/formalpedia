-- Prove2me | solution 1 for GroundTheory.PAdicHodge.isRegular_of_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:18:12.934306+00:00
-- url     : https://prove2.me/submissions/4dcee8ad-fcff-4efa-b5c9-42c40df643c9

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible
import Definitions.Def_GroundTheory_PAdicHodge_AdmissibleField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open TensorProduct Module
variable (G F B : Type*) [Group G] [Field F] [Field B] [Algebra F B] [MulSemiringAction G B]
namespace GroundTheory.PAdicHodge
theorem _root_.solution : IsRegular G F B where
  image_fixedPoints := by
    let := IsFractionRing.mulSemiringAction G B (FractionRing B)
    have hmap : ∀ (g : G) (b : B), g • algebraMap B (FractionRing B) b =
        algebraMap B (FractionRing B) (g • b) := fun g b =>
      IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b
    have hinj := IsFractionRing.injective B (FractionRing B)
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩ g
      rw [hmap, hb g]
    · intro hy
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors B) y
      have hs : (s : B) ≠ 0 := nonZeroDivisors.ne_zero s.2
      have e : IsLocalization.mk' (FractionRing B) a s =
          algebraMap B (FractionRing B) (a * (s : B)⁻¹) := by
        rw [IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, mul_assoc, inv_mul_cancel₀ hs, mul_one]
      refine ⟨a * (s : B)⁻¹, fun g => hinj ?_, e.symm⟩
      rw [← hmap, ← e]
      exact hy g
  isUnit_of_mem_span b hb _ := hb.isUnit
end GroundTheory.PAdicHodge
