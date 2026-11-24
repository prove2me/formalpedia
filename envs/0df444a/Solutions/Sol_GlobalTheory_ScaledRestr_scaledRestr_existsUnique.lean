-- Prove2me | solution 1 for GlobalTheory.ScaledRestr.scaledRestr_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:53:36.627951+00:00
-- url     : https://prove2.me/submissions/b2734480-0acd-4292-bbdd-b1ecac6a8a7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegrality
import Theorems.Thm_GlobalTheory_ScaledRestr_inK_injective
import Theorems.Thm_GlobalTheory_ScaledRestr_exists_scaled_image
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.ScaledRestr
namespace GlobalTheory.ScaledRestr
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → ∀ i, ∃! M : Module.End O H, IsScaledRestr D (N i) M := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hlat hEig e f hG N hN i
  haveI : Module.Free O H := hlat.1
  have hinj := inK_injective (O := O) K H
  have hD : ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ := hEig.2.2.1.2
  let g : H →ₗ[O] K ⊗[O] H := (algebraMap O K D) • ((N i).restrictScalars O ∘ₗ inK K H)
  have hg : ∀ h, g h ∈ LinearMap.range (inK K H) := by
    intro h
    obtain ⟨m, hm⟩ := exists_scaled_image φ ρ D e f hD hG (N i) i (hN i) h
    exact ⟨m, hm⟩
  refine ⟨(LinearEquiv.ofInjective (inK K H) hinj).symm.toLinearMap ∘ₗ (g.codRestrict _ hg), ?_, ?_⟩
  · intro h
    have := (LinearEquiv.ofInjective (inK K H) hinj).apply_symm_apply (g.codRestrict _ hg h)
    rw [Subtype.ext_iff, LinearEquiv.ofInjective_apply] at this
    simpa [g] using this
  · intro M hM
    ext h
    apply hinj
    rw [hM h]
    have := (LinearEquiv.ofInjective (inK K H) hinj).apply_symm_apply (g.codRestrict _ hg h)
    rw [Subtype.ext_iff, LinearEquiv.ofInjective_apply] at this
    simpa [g] using this.symm
end GlobalTheory.ScaledRestr
