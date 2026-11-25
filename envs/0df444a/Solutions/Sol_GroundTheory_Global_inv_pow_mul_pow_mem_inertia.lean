-- Prove2me | solution 1 for GroundTheory.Global.inv_pow_mul_pow_mem_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:46.845599+00:00
-- url     : https://prove2.me/submissions/8fe32a2b-2668-4832-9bbb-3dce83183c1a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField Polynomial
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S]
namespace GroundTheory.Global
theorem _root_.solution {P : Ideal S} {a b : G} (ha : a ∈ MulAction.stabilizer G P)
    (hab : b * a⁻¹ ∈ P.inertia G) (m : ℕ) : (a ^ m)⁻¹ * b ^ m ∈ P.inertia G := by
  induction m with
  | zero => simp [one_mem]
  | succ m ih =>
    have h1 := mul_mul_inv_mem_inertia (inv_mem ha) (mul_mem ih hab)
    rw [inv_inv] at h1
    convert h1 using 1
    rw [pow_succ, pow_succ]
    group
end GroundTheory.Global
