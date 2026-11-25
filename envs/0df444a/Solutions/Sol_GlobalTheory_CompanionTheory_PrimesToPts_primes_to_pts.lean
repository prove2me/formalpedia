-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrimesToPts.primes_to_pts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:38:10.01626+00:00
-- url     : https://prove2.me/submissions/f9b85a42-3c93-46f0-b388-d2e3d29b39df

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_BasicOpenNormFibreIff
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_PrimesToPts_mem_basicOpen_iff_toSpec__539c058bfd78
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_PrimesToPts_comap_toSpec__ae60923711e0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
namespace GlobalTheory.CompanionTheory.PrimesToPts
private theorem to_spec_gamma_bijective (X : Scheme.{0}) [IsAffine X] : Function.Bijective X.toSpecΓ := by
  rw [← Scheme.isoSpec_hom]
  refine ⟨fun a b h => ?_, fun y => ⟨X.isoSpec.inv y, Scheme.inv_hom_apply _ _⟩⟩
  have h' := congrArg X.isoSpec.inv h
  rwa [Scheme.hom_inv_apply, Scheme.hom_inv_apply] at h'
end GlobalTheory.CompanionTheory.PrimesToPts
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrimesToPts
namespace GlobalTheory.CompanionTheory.PrimesToPts
theorem _root_.solution : ∀ {P D : Scheme.{0}} [IsAffine P] [IsAffine D] (v : P ⟶ D) (N : Γ(D, ⊤)) (e : Γ(P, ⊤)), (∀ p : PrimeSpectrum Γ(D, ⊤), N ∉ p.asIdeal ↔ ∀ q : PrimeSpectrum Γ(P, ⊤), q.asIdeal.comap v.appTop.hom = p.asIdeal → e ∉ q.asIdeal) → ∀ y : D, y ∈ D.basicOpen N ↔ ∀ z : P, v z = y → z ∈ P.basicOpen e := by
  intro P D _ _ v N e hN y
  refine (GlobalTheory.CompanionTheory.PrimesToPts.mem_basicOpen_iff_toSpecΓ N y).trans ((hN (D.toSpecΓ y)).trans ?_)
  constructor
  · intro H z hz
    refine (GlobalTheory.CompanionTheory.PrimesToPts.mem_basicOpen_iff_toSpecΓ e z).2 (H _ ?_)
    exact (GlobalTheory.CompanionTheory.PrimesToPts.comap_toSpecΓ v z).trans (by rw [hz])
  · intro H q hq
    obtain ⟨z, rfl⟩ := (to_spec_gamma_bijective P).2 q
    have hz : v z = y := by
      apply (to_spec_gamma_bijective D).1
      apply PrimeSpectrum.ext
      exact (GlobalTheory.CompanionTheory.PrimesToPts.comap_toSpecΓ v z).symm.trans hq
    exact (GlobalTheory.CompanionTheory.PrimesToPts.mem_basicOpen_iff_toSpecΓ e z).1 (H z hz)
end GlobalTheory.CompanionTheory.PrimesToPts
