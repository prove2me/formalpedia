-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.exists_eq_zpow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:27:44.977471+00:00
-- url     : https://prove2.me/submissions/73d16d9f-8946-4448-98ab-337854c0f6da

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable (h : IsPlaceOver A w)
variable {h}
variable [IsAlgClosure E Ω]
namespace GlobalTheory.WeilDeligne
theorem _root_.solution {φ : Weil h} (hφ : deg φ = 1) (σ : Weil h) :
    ∃ τ : Ine (F := E) A, σ = φ ^ deg σ * ineIncl h τ := by
  have h0 : deg ((φ ^ deg σ)⁻¹ * σ) = 0 := by simp [hφ]
  refine ⟨⟨_, deg_eq_zero_iff.mp h0⟩, ?_⟩
  rw [← inv_mul_eq_iff_eq_mul]
  rfl
end GlobalTheory.WeilDeligne
