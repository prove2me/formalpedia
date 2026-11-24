-- Prove2me | solution 1 for GlobalTheory.InertiaAlmostAll.exists_int_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:47:35.948011+00:00
-- url     : https://prove2.me/submissions/2993dd5d-c4bd-4c54-80c5-aeb47ddbcd8b

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinitePlacesInertiaNotFixingFiniteExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.InertiaAlmostAll
namespace GlobalTheory.InertiaAlmostAll
theorem _root_.solution (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (y : Ω) : ∃ c : ℤ, c ≠ 0 ∧ IsIntegral ℤ ((c : Ω) * y) := by
  haveI : Algebra.IsAlgebraic ℤ F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := F)).mpr inferInstance
  haveI : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ F Ω
  obtain ⟨c, hc, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) y).exists_integral_multiple
  exact ⟨c, hc, by simpa [zsmul_eq_mul] using h⟩
end GlobalTheory.InertiaAlmostAll
