-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.tsum_rep_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:17:36.493662+00:00
-- url     : https://prove2.me/submissions/d699610b-4baa-4039-a156-9b58d3218202

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WallLawOfSectionLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_rep_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution {G : Type} [Group G] {X : Type} [AddCommMonoid X] [TopologicalSpace X]
    {P Γ : Subgroup G} (F : G → X) (hF : ∀ δ ∈ Γ, δ ∈ P → ∀ x, F (δ * x) = F x) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    ∑' q : Cos P Γ, F (rep q * (γ * g)) = ∑' q : Cos P Γ, F (rep q * g) := by
  rw [← Equiv.tsum_eq (cosMul P Γ ⟨γ, hγ⟩) (fun q : Cos P Γ => F (rep q * g))]
  refine tsum_congr fun q => ?_
  have hq : cosMul P Γ ⟨γ, hγ⟩ q = Quotient.mk _ (Quotient.out q * ⟨γ, hγ⟩) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  obtain ⟨δ, h1, h2, h3⟩ := rep_mk (P := P) (Quotient.out q * (⟨γ, hγ⟩ : Γ))
  rw [hq, h3, mul_assoc δ, hF δ h1 h2]
  simp [rep, mul_assoc]
end GlobalTheory.CompanionTheory.RgEis
