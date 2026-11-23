-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.g_eq_of_torsion_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:26.201107+00:00
-- url     : https://prove2.me/submissions/0ab961a3-adf4-4bf0-9921-2843f12eaa32

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_eq
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_eq_zero_of_subsingleton


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u v
open Representation
open GroundTheory.ProfCoh.AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution (A : Type u) [AddCommGroup A] [DistribMulAction Γ A]
    [Finite (ModN A l)] (hA : ∀ a : A, l • a = 0 → a = 0) :
    d.g A = d.toFun (ModN A l) (modNRep Γ A l) := by
  have : Subsingleton (TorsN A l) := ⟨fun x y => Subtype.ext (by
    rw [hA x ((mem_ker_lsmul_iff l (x : A)).1 x.2), hA y ((mem_ker_lsmul_iff l (y : A)).1 y.2)])⟩
  rw [d.g_eq A, d.toFun_eq_zero_of_subsingleton (X := TorsN A l), sub_zero]
end GroundTheory.ProfCoh.AdditiveFunction
