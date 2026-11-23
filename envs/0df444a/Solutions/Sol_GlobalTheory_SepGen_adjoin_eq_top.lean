-- Prove2me | solution 1 for GlobalTheory.SepGen.adjoin_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:04.14169+00:00
-- url     : https://prove2.me/submissions/8cb71872-5d17-452c-a941-99710e6bca34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparable
import Theorems.Thm_GlobalTheory_SepGen_charpoly_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.SepGen
variable {E : Type} [Field E] {A : Type} [CommRing A] [Algebra E A] [Module.Finite E A]
namespace GlobalTheory.SepGen
theorem _root_.solution (y : A) (hs : (LinearMap.mulLeft E y).charpoly.Separable) :
    Algebra.adjoin E ({y} : Set A) = ⊤ := by
  have hi : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  have h1 := natDegree_le_of_dvd (charpoly_dvd y hs _ (minpoly.aeval E y)) (minpoly.ne_zero hi)
  rw [LinearMap.charpoly_natDegree] at h1
  have h2 : Module.finrank E (Algebra.adjoin E ({y} : Set A)) = (minpoly E y).natDegree :=
    (Algebra.adjoin.powerBasis hi).finrank
  have h3 : Subalgebra.toSubmodule (Algebra.adjoin E ({y} : Set A)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (h1.trans h2.ge))
  rw [← Algebra.toSubmodule_eq_top]
  exact h3
end GlobalTheory.SepGen
