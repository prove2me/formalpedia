-- Prove2me | solution 1 for GlobalTheory.HostModel.formallyUnramified_of_isCoprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:55:13.515718+00:00
-- url     : https://prove2.me/submissions/55e3c595-e726-414d-94a8-b1a955ff8037

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Theorems.Thm_GlobalTheory_HostModel_sq_sub_smul_derivation_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.HostModel
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (σ : B →+* B)
    (hσ : ∀ b, σ (σ b) = b) (hfix : ∀ b, σ b = b → b ∈ Set.range (algebraMap A B)) (w₁ w₂ : B)
    (h : IsCoprime (w₁ - σ w₁) (w₂ - σ w₂)) : Algebra.FormallyUnramified A B := by
  have hD : ∀ b, KaehlerDifferential.D A B b = 0 := fun b => by
    obtain ⟨u, v, huv⟩ : IsCoprime ((w₁ - σ w₁) ^ 2) ((w₂ - σ w₂) ^ 2) := h.pow
    rw [← one_smul B (KaehlerDifferential.D A B b), ← huv, add_smul, mul_smul, mul_smul,
      sq_sub_smul_derivation_eq_zero _ σ hσ hfix, sq_sub_smul_derivation_eq_zero _ σ hσ hfix, smul_zero, smul_zero,
      add_zero]
  have hbot : (⊤ : Submodule B (Ω[B⁄A])) = ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
    rintro _ ⟨b, rfl⟩
    exact hD b
  refine ⟨⟨fun x y => ?_⟩⟩
  have hz : ∀ z : Ω[B⁄A], z = 0 := fun z => by
    rw [← Submodule.mem_bot B, ← hbot]
    trivial
  rw [hz x, hz y]
end GlobalTheory.HostModel
