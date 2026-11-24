-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Averaging.bijective_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:09:38.766511+00:00
-- url     : https://prove2.me/submissions/5dbace04-b115-4935-b44d-94f39f06259f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteCovolumeUnimodular
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ClosedSubgroupQuotientMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuotientMeasureTower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Averaging
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {G₁ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
namespace GlobalTheory.CompanionTheory.SW.Averaging
theorem _root_.solution (ι : G₁ →* G) (hι : Function.Injective ι)
    (Γ : Subgroup G) (Γ₁ : Subgroup G₁) (hΓ : ∀ u ∈ Γ₁, ι u ∈ Γ)
    {Q : Type} (r : Q → G) (hr : ∀ q, r q ∈ Γ)
    (hQ : ∀ γ ∈ Γ, ∃! q, ∃ u ∈ Γ₁, γ = ι u * r q) :
    Function.Bijective (fun p : Q × Γ₁ =>
      (⟨ι (p.2 : G₁)⁻¹ * r p.1, Γ.mul_mem (hΓ _ (Γ₁.inv_mem p.2.2)) (hr p.1)⟩ : Γ)) := by
  constructor
  · rintro ⟨q, v⟩ ⟨q', v'⟩ h
    have hval : ι (v : G₁)⁻¹ * r q = ι (v' : G₁)⁻¹ * r q' := congrArg Subtype.val h
    obtain ⟨q₀, -, huniq⟩ := hQ _ (Γ.mul_mem (hΓ _ (Γ₁.inv_mem v.2)) (hr q))
    have hq : q = q' := by
      rw [huniq q ⟨(v : G₁)⁻¹, Γ₁.inv_mem v.2, rfl⟩, huniq q' ⟨(v' : G₁)⁻¹, Γ₁.inv_mem v'.2, hval⟩]
    subst hq
    have h3 : ι (v : G₁)⁻¹ = ι (v' : G₁)⁻¹ := mul_right_cancel hval
    have hv : (v : G₁) = v' := inv_injective (hι h3)
    simp only [Prod.mk.injEq, true_and]
    exact Subtype.ext hv
  · rintro ⟨γ, hγ⟩
    obtain ⟨q, ⟨u, hu, hγu⟩, -⟩ := hQ γ hγ
    refine ⟨(q, ⟨u⁻¹, Γ₁.inv_mem hu⟩), ?_⟩
    apply Subtype.ext
    show ι (u⁻¹)⁻¹ * r q = γ
    rw [inv_inv]
    exact hγu.symm
end GlobalTheory.CompanionTheory.SW.Averaging
