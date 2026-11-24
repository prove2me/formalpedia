-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HypSplit.exists_partner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:24:13.258694+00:00
-- url     : https://prove2.me/submissions/f4348225-fda9-42d0-a7d2-43d81ae5363f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IsotropicVectorSplitsHyperbolicPlane
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_hLin_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_hE_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.SW.HypSplit.hLin_apply

set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HypSplit
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)
variable {σ J}
namespace GlobalTheory.CompanionTheory.SW.HypSplit
theorem _root_.solution (hσ : ∀ a, σ (σ a) = a) (hJ : IsHermND σ J) (h2 : (2 : E) ≠ 0)
    (x : Fin M → E) (hx : x ≠ 0) (hxx : hE σ J x x = 0) :
    ∃ y, hE σ J x y = 1 ∧ hE σ J y y = 0 := by
  have hr : Matrix.vecMul (fun i => σ (x i)) J ≠ 0 := by
    intro h0
    have h1 := Matrix.eq_zero_of_vecMul_eq_zero hJ.2 h0
    apply hx
    funext i
    have h3 := congrFun h1 i
    simpa using h3
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hr
  have hj' : Matrix.vecMul (fun i => σ (x i)) J j ≠ 0 := hj
  obtain ⟨y₀, h1⟩ : ∃ y₀, hE σ J x y₀ = 1 := by
    refine ⟨Pi.single j (Matrix.vecMul (fun i => σ (x i)) J j)⁻¹, ?_⟩
    rw [hE_eq_dot, dotProduct_single, mul_inv_cancel₀ hj']
  have conj := hE_conj (J := J) hσ hJ.1
  have h1' : hE σ J y₀ x = 1 := by rw [← conj, h1, map_one]
  have hc : σ (hE σ J y₀ y₀) = hE σ J y₀ y₀ := conj _ _
  set c := hE σ J y₀ y₀ with hcdef
  have hc2 : σ (c / 2) = c / 2 := by rw [map_div₀, hc, map_ofNat]
  have hxy : hE σ J x (y₀ - (c / 2) • x) = 1 := by
    have := (hLin σ J x).map_sub y₀ ((c / 2) • x)
    simp only [map_smul, hLin_apply, smul_eq_mul, hxx, h1] at this
    simpa using this
  have hy₀y : hE σ J y₀ (y₀ - (c / 2) • x) = c / 2 := by
    have := (hLin σ J y₀).map_sub y₀ ((c / 2) • x)
    simp only [map_smul, hLin_apply, smul_eq_mul, h1', ← hcdef] at this
    rw [this]; field_simp; ring
  refine ⟨y₀ - (c / 2) • x, hxy, ?_⟩
  have := (hLin σ J (y₀ - (c / 2) • x)).map_sub y₀ ((c / 2) • x)
  simp only [map_smul, hLin_apply, smul_eq_mul] at this
  rw [this, ← conj y₀, hy₀y, hc2, ← conj x, hxy, map_one]
  ring
end GlobalTheory.CompanionTheory.SW.HypSplit
