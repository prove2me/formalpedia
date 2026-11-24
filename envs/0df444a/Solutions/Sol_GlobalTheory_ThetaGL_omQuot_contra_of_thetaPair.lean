-- Prove2me | solution 1 for GlobalTheory.ThetaGL.omQuot_contra_of_thetaPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:59:08.357332+00:00
-- url     : https://prove2.me/submissions/f03d4224-ca3d-4f29-9372-7287dd364091

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_IsParahoricVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairContragredientQuotient
import Theorems.Thm_GlobalTheory_ThetaGL_DualPair_ev_tmul
import Theorems.Thm_GlobalTheory_ThetaGL_DualPair_ev_injective
import Theorems.Thm_GlobalTheory_ThetaGL_DualPair_exists_ev_eq
import Theorems.Thm_GlobalTheory_ThetaGL_DualPair_ev_map
import Theorems.Thm_GlobalTheory_SplitWeil_om_isSmoothRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ThetaGL.DualPair.ev_tmul

set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct
open GlobalTheory.ThetaGL.DualPair
namespace GlobalTheory.ThetaGL
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W), IsSmoothChar μ → IsAdmissible π → ThetaPair μ σ π → OmQuot μ σ (contra π) := by
  intro k _ _ _ _ r n μ V _ _ W _ _ σ π hμ hπ ⟨B, hB0, hB⟩
  obtain ⟨-, hmul, -, -, hop⟩ := om_isSmoothRepresentation k (Fin r) (Fin n) μ hμ
  have hone := (om_isSmoothRepresentation k (Fin r) (Fin n) μ hμ).1
  have hmem : ∀ Φ, B Φ ∈ LinearMap.range (ev V π) := by
    intro Φ
    let S : Subgroup (GL (Fin n) k) :=
      { carrier := {h | om μ (1 : GL (Fin r) k) h Φ.1 = Φ.1}
        one_mem' := hone _
        mul_mem' := fun {x y} hx hy => by
          show om μ (1 : GL (Fin r) k) (x * y) Φ.1 = Φ.1
          have := hmul 1 1 x y Φ.1
          rw [mul_one] at this
          rw [this, hy, hx]
        inv_mem' := fun {x} hx => by
          show om μ (1 : GL (Fin r) k) x⁻¹ Φ.1 = Φ.1
          have hx' : om μ (1 : GL (Fin r) k) x Φ.1 = Φ.1 := hx
          conv_lhs => rw [← hx']
          have := hmul 1 1 x⁻¹ x Φ.1
          rw [mul_one, inv_mul_cancel, hone] at this
          exact this.symm }
    have hSo : IsOpen (S : Set (GL (Fin n) k)) :=
      (hop Φ.1 Φ.2).preimage (Continuous.prodMk continuous_const continuous_id)
    have hKo : IsOpen ((S ⊓ KO k (Fin n) : Subgroup _) : Set (GL (Fin n) k)) :=
      hSo.inter SplitFlip.isOpen_KO
    have hKc : IsCompact ((S ⊓ KO k (Fin n) : Subgroup _) : Set (GL (Fin n) k)) :=
      SplitFlip.isCompact_KO.of_isClosed_subset
        (Subgroup.isClosed_of_isOpen _ hKo) Set.inter_subset_right
    obtain ⟨t, ht⟩ := exists_ev_eq π hπ _ hKo hKc (B Φ) fun h hh x => by
      have := hB 1 h Φ Φ (hh.1 : om μ (1 : GL (Fin r) k) h Φ.1 = Φ.1).symm x
      simpa using this
    exact ⟨t, ht⟩
  let e := LinearEquiv.ofInjective (ev V π) (ev_injective π)
  let f : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] V ⊗[ℂ] smoothPart π.dual :=
    e.symm.toLinearMap ∘ₗ B.codRestrict _ hmem
  have hf : ∀ Φ, ev V π (f Φ) = B Φ := fun Φ => by
    have := e.apply_symm_apply (B.codRestrict _ hmem Φ)
    exact congrArg Subtype.val this
  refine ⟨f, fun h0 => hB0 (LinearMap.ext fun Φ => ?_), fun g h Φ Φ' hΦ => ?_⟩
  · rw [← hf, h0]
    simp
  · apply ev_injective π
    refine LinearMap.ext fun w => ?_
    rw [ev_map, hf, hf, ← hB g h Φ Φ' hΦ (π h⁻¹ w), ← Module.End.mul_apply, ← map_mul]
    simp
end GlobalTheory.ThetaGL
