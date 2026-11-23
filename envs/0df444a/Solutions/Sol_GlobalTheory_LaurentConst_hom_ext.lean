-- Prove2me | solution 1 for GlobalTheory.LaurentConst.hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:02.889669+00:00
-- url     : https://prove2.me/submissions/7b9607d7-abc4-4ead-85dd-7772b49d9a55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentConst
open AddMonoidAlgebra
attribute [-simp] LaurentPolynomial.single_eq_C_mul_T
variable {L R : Type} [CommRing L] [CommRing R]
namespace GlobalTheory.LaurentConst
theorem _root_.solution {A : Type} [CommRing A] {f g : AddMonoidAlgebra L ℤ →+* A}
    (h₀ : ∀ c, f (single 0 c) = g (single 0 c)) (h₁ : f (single 1 1) = g (single 1 1)) : f = g := by
  have := MonoidHom.ext_mint (f := f.toMonoidHom.comp (AddMonoidAlgebra.of L ℤ))
    (g := g.toMonoidHom.comp (AddMonoidAlgebra.of L ℤ)) h₁
  exact AddMonoidAlgebra.ringHom_ext h₀ fun n ↦ DFunLike.congr_fun this (Multiplicative.ofAdd n)
end GlobalTheory.LaurentConst
