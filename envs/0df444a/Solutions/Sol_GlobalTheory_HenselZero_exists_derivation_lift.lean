-- Prove2me | solution 1 for GlobalTheory.HenselZero.exists_derivation_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:45:57.758483+00:00
-- url     : https://prove2.me/submissions/208c062e-84a8-487d-b6e9-af1a17844cb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FormallySmoothQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HenselZero
open IsLocalRing GlobalTheory.SqZero
namespace GlobalTheory.HenselZero
theorem _root_.solution {R S K : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
    [CommRing K] [Algebra R K] (u : S →ₐ[R] K) (hu : Function.Surjective u) (D : S →ₗ[R] K)
    (hD : ∀ a b, D (a * b) = u a * D b + u b * D a) : ∃ τ : Derivation R S S, ∀ a, u (τ a) = D a := by
  let _ : Algebra S K := (u : S →+* K).toAlgebra
  have : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq fun r => (u.commutes r).symm
  let D' : Derivation R S K := Derivation.mk' D hD
  obtain ⟨l, hl⟩ := Module.projective_lifting_property (Algebra.linearMap S K) D'.liftKaehlerDifferential hu
  refine ⟨l.compDer (KaehlerDifferential.D R S), fun a => ?_⟩
  exact (congr($hl (KaehlerDifferential.D R S a))).trans (D'.liftKaehlerDifferential_comp_D a)
end GlobalTheory.HenselZero
