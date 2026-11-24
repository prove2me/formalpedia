-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_algebraMap_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:36:02.568843+00:00
-- url     : https://prove2.me/submissions/643f6f45-7be9-408b-8254-c9db89bac59d

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreePullbackAffine

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] [Algebra A B] :
    FiniteFreeHom (algebraMap A B) ↔ Module.Free A B ∧ Module.Finite A B := by
  have h : (algebraMap A B).toAlgebra = ‹Algebra A B› := Algebra.algebra_ext _ _ fun _ => rfl
  simp only [GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom]
  rw [h]
end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
