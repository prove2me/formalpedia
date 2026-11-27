-- Prove2me | solution 1 for GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:34:48.84285+00:00
-- url     : https://prove2.me/submissions/afe06a8a-319d-445a-bbc5-6c6fae763063

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsRationalIsometryOfTraceIsometry
import Theorems.Thm_GlobalTheory_TraceIsometry_eq_or_eq_neg_of_norm_eq
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_GlobalTheory_FrameFibre_eq_zero_of_trace
import Theorems.Thm_GlobalTheory_FrameFibre_exists_matrix
import Theorems.Thm_GlobalTheory_FrameFibre_exists_smul_eq
import Theorems.Thm_GlobalTheory_FrameFibre_herm_smul_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix
open GlobalTheory GlobalTheory.TraceIsometry
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.TraceIsometry
namespace _root_.GlobalTheory.TraceIsometry
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (r : ℕ) (X X' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = ‖τ X'.ξ0‖) →
    ∀ (gam : X.Λ ≃ₗ[𝓞 E] X'.Λ), (∀ u v : X.Λ, Algebra.trace ℚ E (-X'.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm
    (gam u : Fin r → E) (gam v : Fin r → E)) = Algebra.trace ℚ E (-X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm
    (u : Fin r → E) (v : Fin r → E))) → ∃ (a : GL (Fin r) E) (ε : E), (ε = 1 ∨ ε = -1) ∧
    X'.ξ0 = ε * X.ξ0 ∧ (∀ v : X.Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) =
    (gam v : Fin r → E)) ∧ (∀ v, v ∈ X.Λ ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ X'.Λ) ∧
    ∀ u v, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u)
    ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = ε * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v := by
  intro E _ _ _ r X X' hξ gam hgam
  obtain ⟨ε, hε1, hεξ⟩ : ∃ ε : E, (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 := by
    rcases _root_.GlobalTheory.TraceIsometry.eq_or_eq_neg_of_norm_eq X.ξ0_im X'.ξ0_im hξ with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_mul]⟩
  have hsp : ∀ Y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r, Submodule.span E (Set.range Y.Λ.subtype) = ⊤ := by
    intro Y
    have : Set.range Y.Λ.subtype = (Y.Λ : Set (Fin r → E)) := by ext; simp
    rw [this]
    exact Y.Λ_span
  obtain ⟨A, hA⟩ := _root_.GlobalTheory.FrameFibre.exists_matrix X.Λ.subtype
    Subtype.val_injective (hsp X) (X'.Λ.subtype ∘ₗ gam.toLinearMap)
  obtain ⟨B, hB⟩ := _root_.GlobalTheory.FrameFibre.exists_matrix X'.Λ.subtype
    Subtype.val_injective (hsp X') (X.Λ.subtype ∘ₗ gam.symm.toLinearMap)
  have hA' : ∀ v : X.Λ, A *ᵥ (v : Fin r → E) = (gam v : Fin r → E) := fun v => hA v
  have hB' : ∀ w : X'.Λ, B *ᵥ (w : Fin r → E) = (gam.symm w : Fin r → E) := fun w => hB w
  have hBA : B * A = 1 := by
    have hlin : Matrix.mulVecLin (B * A) = LinearMap.id := by
      apply LinearMap.ext_on X.Λ_span
      intro v hv
      simp only [Matrix.mulVecLin_apply, LinearMap.id_apply]
      rw [← Matrix.mulVec_mulVec, show A *ᵥ v = _ from hA' ⟨v, hv⟩, hB']
      simp
    apply Matrix.ext_of_mulVec_single
    intro i
    have h1 := LinearMap.congr_fun hlin (Pi.single i 1)
    simp only [Matrix.mulVecLin_apply, LinearMap.id_apply] at h1
    rw [h1, Matrix.one_mulVec]
  have hsm : ∀ (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (x y : Fin r → E),
      _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (c • x) y = (c : E) * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y := by
    intro G c x y
    have h1 := _root_.GlobalTheory.FrameFibre.herm_smul_smul G (c : E) 1 x y
    rw [one_smul, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc_one, mul_one] at h1
    rw [← h1]
    rfl
  have hL : ∀ u v : X.Λ, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E)) =
      ε * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v := by
    intro u v
    have hD : -X'.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm (gam u) (gam v) - -X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v = 0 := by
      apply _root_.GlobalTheory.FrameFibre.eq_zero_of_trace
      intro c
      have h1 := hgam (c • u) v
      rw [LinearEquiv.map_smul, Submodule.coe_smul, Submodule.coe_smul, hsm, hsm] at h1
      rw [mul_sub, map_sub, sub_eq_zero, mul_left_comm (c : E), mul_left_comm (c : E)]
      exact h1
    rw [hεξ, ← hA' u, ← hA' v] at hD
    have hε2 : ε * ε = 1 := by rcases hε1 with h | h <;> rw [h] <;> ring
    apply mul_left_cancel₀ X.ξ0_ne
    linear_combination (-ε) * hD -
      X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E)) * hε2
  have hall : ∀ u v : Fin r → E, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm (A *ᵥ u) (A *ᵥ v) = ε * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v := by
    intro u v
    obtain ⟨c, u', hc, hu'⟩ := _root_.GlobalTheory.FrameFibre.exists_smul_eq X.Λ.subtype (hsp X) u
    obtain ⟨d, v', hd, hv'⟩ := _root_.GlobalTheory.FrameFibre.exists_smul_eq X.Λ.subtype (hsp X) v
    have h1 := hL u' v'
    have hu'' : (u' : Fin r → E) = (c : E) • u := hu'.symm
    have hv'' : (v' : Fin r → E) = (d : E) • v := hv'.symm
    rw [hu'', hv'', Matrix.mulVec_smul, Matrix.mulVec_smul, _root_.GlobalTheory.FrameFibre.herm_smul_smul,
      _root_.GlobalTheory.FrameFibre.herm_smul_smul] at h1
    have hc' : (c : E) ≠ 0 := by exact_mod_cast hc
    have hd' : (d : E) ≠ 0 := by exact_mod_cast hd
    have hcc : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (d : E) ≠ 0 := by
      intro h0
      apply hd'
      rw [← _root_.ReciprocityTheory.ChartRestriction.G.FD.cc_cc (d : E), h0, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc_zero]
    apply mul_left_cancel₀ (mul_ne_zero hc' hcc)
    linear_combination h1
  refine ⟨⟨A, B, (mul_eq_one_comm.mp hBA), hBA⟩, ε, hε1, hεξ, hA', ?_, hall⟩
  intro v
  change v ∈ X.Λ ↔ A *ᵥ v ∈ X'.Λ
  constructor
  · intro hv
    rw [show A *ᵥ v = _ from hA' ⟨v, hv⟩]
    exact (gam ⟨v, hv⟩).2
  · intro hv
    have h1 : B *ᵥ (A *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
    rw [← h1, show B *ᵥ (A *ᵥ v) = _ from hB' ⟨A *ᵥ v, hv⟩]
    exact (gam.symm _).2
end _root_.GlobalTheory.TraceIsometry
end GlobalTheory.TraceIsometry
