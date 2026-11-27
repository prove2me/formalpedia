-- Prove2me | solution 1 for GlobalTheory.exists_multigraded_hilbertPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:19.224279+00:00
-- url     : https://prove2.me/submissions/ad4d80b6-b0cc-427d-b8b3-b400ef80eaf0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
import Theorems.Thm_GlobalTheory_MultiHilbert_eventuallyPoly_hilbertFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory
theorem _root_.solution : ∀ (K σ : Type) [Field K] [Finite σ] (r : ℕ) (col : σ → Fin r) (I : Ideal (MvPolynomial σ K)), (∀ F ∈ I, ∀ n : Fin r → ℕ, MvPolynomial.weightedHomogeneousComponent (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n F ∈ I) → ∃ (Φ : MvPolynomial (Fin r) ℚ) (n₀ : ℕ), ∀ n : Fin r → ℕ, (∀ k, n₀ ≤ n k) → ((Module.finrank K ↥(MvPolynomial.weightedHomogeneousSubmodule K (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n) : ℕ) : ℚ) - ((Module.finrank K ↥(MvPolynomial.weightedHomogeneousSubmodule K (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n ⊓ I.restrictScalars K) : ℕ) : ℚ) = MvPolynomial.eval (fun k => (n k : ℚ)) Φ :=
  fun _ _ _ _ _ col I hI => GlobalTheory.MultiHilbert.eventuallyPoly_hilbertFun col I hI
end GlobalTheory
