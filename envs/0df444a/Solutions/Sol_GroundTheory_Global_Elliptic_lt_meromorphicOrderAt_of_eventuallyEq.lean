-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.lt_meromorphicOrderAt_of_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:07:16.00052+00:00
-- url     : https://prove2.me/submissions/741743e2-b1d0-4543-8b9d-60d34b294c73

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set Polynomial
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f w : ℂ → ℂ} {x : ℂ} {n : ℤ}
    (hw : AnalyticAt ℂ w x) (hw0 : w x = 0)
    (h : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ n * w z) :
    (n : WithTop ℤ) < meromorphicOrderAt f x := by
  have e : (fun z ↦ (z - x) ^ n * w z) = (fun z ↦ z - x) ^ n * w := rfl
  have hm : MeromorphicAt ((fun z ↦ z - x) ^ n) x :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt (x := x)).zpow n
  rw [meromorphicOrderAt_congr h, e, meromorphicOrderAt_mul hm hw.meromorphicAt,
    meromorphicOrderAt_zpow_id_sub_const]
  have hpos : (1 : WithTop ℤ) ≤ meromorphicOrderAt w x := by
    rw [hw.meromorphicOrderAt_eq]
    have h1 : analyticOrderAt w x ≠ 0 := by
      rw [Ne, hw.analyticOrderAt_eq_zero]
      simpa using hw0
    cases h : analyticOrderAt w x with
    | top => simp
    | coe m =>
      rw [h] at h1
      have : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (by exact_mod_cast h1)
      simp only [ENat.map_natCast]
      exact_mod_cast this
  cases ho : meromorphicOrderAt w x with
  | top => simp
  | coe m =>
    rw [ho] at hpos
    have : (1 : ℤ) ≤ m := by exact_mod_cast hpos
    exact_mod_cast (by omega : n < n + m)
end GroundTheory.Global.Elliptic
