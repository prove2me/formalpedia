-- Prove2me | solution 1 for GlobalTheory.CatCoh.commAlgFunctorCocyclesOne_eq_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:08.175035+00:00
-- url     : https://prove2.me/submissions/9f11d9af-d2fa-43a8-87ec-220cfc7ea573

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory
open GlobalTheory GlobalTheory.CatCoh
universe v u v' u' v'' u''
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
variable (F)
namespace GlobalTheory.CatCoh
theorem _root_.solution : Z1 F = LinearMap.ker (d1 F) := by
  ext f
  rw [LinearMap.mem_ker]
  constructor
  · intro hf
    funext T T' T'' φ ψ
    have h : f T T'' (φ ≫ ψ) = mp F ψ (f T T' φ) + f T' T'' ψ := hf φ ψ
    show mp F ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = 0
    linear_combination -h
  · intro hf T T' T'' φ ψ
    have h := congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') φ) ψ
    change mp F ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = 0 at h
    show f T T'' (φ ≫ ψ) = mp F ψ (f T T' φ) + f T' T'' ψ
    linear_combination -h
end GlobalTheory.CatCoh
