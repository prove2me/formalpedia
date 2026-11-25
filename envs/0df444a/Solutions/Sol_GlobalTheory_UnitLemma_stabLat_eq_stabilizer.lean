-- Prove2me | solution 1 for GlobalTheory.UnitLemma.stabLat_eq_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:13.645171+00:00
-- url     : https://prove2.me/submissions/7dd3c427-7efc-4a69-ba49-33b45bbcc321

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableLatticeOrbitCountEqSumOrbits
import Theorems.Thm_GlobalTheory_UnitLemma_stLat_smul_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma
variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]
namespace GlobalTheory.UnitLemma
theorem _root_.solution (g : A) (L : stLat O E g) :
    stabLat O (L : Submodule O A) = MulAction.stabilizer Aˣ L := by
  ext t
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, stLat_smul_val]
  constructor
  · intro h
    ext x
    rw [mem_mulLat_iff]
    have := h (((t⁻¹ : Aˣ) : A) * x)
    rw [← mul_assoc, Units.mul_inv, one_mul] at this
    exact this
  · intro h y
    have := SetLike.ext_iff.mp h ((t : A) * y)
    rw [mem_mulLat_iff, ← mul_assoc, Units.inv_mul, one_mul] at this
    exact this
end GlobalTheory.UnitLemma
