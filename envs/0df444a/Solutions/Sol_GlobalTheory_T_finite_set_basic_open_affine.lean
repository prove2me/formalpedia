-- Prove2me | solution 1 for GlobalTheory.T.finite_set_basic_open_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:09:40.464732+00:00
-- url     : https://prove2.me/submissions/e5133e3f-da48-4323-967f-a7ca8c5424ea

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteSetBasicOpenAffine
import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteSetBasicOpenAffineStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PrimeAvoid_exists_basicOpen_between


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X : Scheme.{0}} (U V₀ : X.Opens), IsAffineOpen U → V₀ ≤ U → ∀ K : Set X, K.Finite → K ⊆ V₀ → ∃ f : Γ(X, U), K ⊆ X.basicOpen f ∧ X.basicOpen f ≤ V₀ := by
  first | exact @GlobalTheory.CompanionTheory.PrimeAvoid.exists_basicOpen_between | exact GlobalTheory.CompanionTheory.PrimeAvoid.exists_basicOpen_between | (intros; apply GlobalTheory.CompanionTheory.PrimeAvoid.exists_basicOpen_between <;> assumption)
end _root_.GlobalTheory.T
