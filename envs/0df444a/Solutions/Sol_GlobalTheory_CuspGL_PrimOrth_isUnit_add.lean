-- Prove2me | solution 1 for GlobalTheory.CuspGL.PrimOrth.isUnit_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:04:07.78556+00:00
-- url     : https://prove2.me/submissions/00816688-3231-4cf1-91fe-33226881aaf7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndomorphismInnerProductPrimitiveMobiu

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.PrimOrth
variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
namespace GlobalTheory.CuspGL.PrimOrth
theorem _root_.solution [FiniteDimensional F V] {A : Submodule F V} {g h : Module.End F V} (hh : h ∈ nilRad A)
    (hg : ∀ x ∈ A, g x ∈ A) (hu : IsUnit g) : IsUnit (g + h) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot] at hu
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hinj : Function.Injective (g.restrict hg) := by
    intro a b hab
    exact Subtype.ext (hu (congrArg Subtype.val hab))
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  have hx' : g x + h x = 0 := hx
  have hgx : g x ∈ A := by
    rw [eq_neg_of_add_eq_zero_left hx']
    exact A.neg_mem (hh.1 x)
  obtain ⟨w, hw⟩ := hsurj ⟨g x, hgx⟩
  have hwx : (w : V) = x := hu (congrArg Subtype.val hw)
  have hxA : x ∈ A := hwx ▸ w.2
  rw [hh.2 x hxA, add_zero] at hx'
  exact hu (by rw [hx', map_zero])
end GlobalTheory.CuspGL.PrimOrth
