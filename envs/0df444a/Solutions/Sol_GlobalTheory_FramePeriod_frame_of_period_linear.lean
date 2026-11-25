-- Prove2me | solution 1 for GlobalTheory.FramePeriod.frame_of_period_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:09:36.4938+00:00
-- url     : https://prove2.me/submissions/6fa07329-8299-4987-8b37-2440379a0e3e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameOfPeriodLinear
import Theorems.Thm_GlobalTheory_FramePeriod_loc_compare
import Theorems.Thm_GlobalTheory_FramePeriod_block_of_allPer
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_GlobalTheory_CMLattice_exists_basis_of_cmType
import Theorems.Thm_GlobalTheory_FramePeriod_allPer_bijective
import Theorems.Thm_GlobalTheory_FramePeriod_allPer_symm
import Theorems.Thm_GlobalTheory_FramePeriod_cmType
import Theorems.Thm_GlobalTheory_FramePeriod_exists_loc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FramePeriod
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FramePeriod
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ)) (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1), FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → ∀ (P : D.La →+ (Fin g → ℂ)), ∀ x ∈ FD.GG Ψ Gm D.q, ∀ x' ∈ FD.GG Ψ Gm D.q, (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → ∀ (P' : D.La →+ (Fin g → ℂ)), (∀ v k, P' v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x' (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x' (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → ∀ h : Matrix (Fin g) (Fin g) ℂ, (∀ v, P' v = h *ᵥ P v) → ∃ b : FD.Frame Ψ r, x' = FD.rmul x b ∧ (∀ τ (a c : Fin r), (c : ℕ) < D.q → D.q ≤ (a : ℕ) → b τ a c = 0) ∧ (∀ k k', (idx k).1 = (idx k').1 → ((idx k).2 : ℕ) < D.q → ((idx k').2 : ℕ) < D.q → h k k' = b (idx k).1 (idx k').2 (idx k).2) ∧ (∀ k k', (idx k).1 = (idx k').1 → D.q ≤ ((idx k).2 : ℕ) → D.q ≤ ((idx k').2 : ℕ) → h k k' = (FD.mat b (idx k).1)⁻¹ (idx k).2 (idx k').2) ∧ ∀ k k', ty k ≠ ty k' → h k k' = 0 := by
  classical
  intro E _ _ _ H D r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos ⟨hφ, hspan, hG, hdet, hEF⟩ P x hx x' hx' hP P' hP' h hh
  have hcm := cmType H Ψ hΨ
  have hloc := fun τ : Ψ => (exists_loc τ.1 Gm hG D.q (FD.mat x τ) (hx τ).1 (hx τ).2).1
  have hbij := allPer_bijective Gm D.q x idx hloc
  have hQ : ∀ v, P v = allPer Gm D.q x idx (CMLattice.embAll Ψ r (φ v)) := fun v =>
    funext fun k => hP v k
  have hQ' : ∀ v, P' v = allPer Gm D.q x' idx (CMLattice.embAll Ψ r (φ v)) := fun v =>
    funext fun k => hP' v k
  have := D.fin
  obtain ⟨b, hb⟩ := CMLattice.exists_basis_of_cmType Ψ hcm r (LinearMap.range φ)
    (Module.Finite.iff_fg.1 inferInstance) (by rw [LinearMap.coe_range]; exact hspan)
  have hall : ∀ y, allPer Gm D.q x' idx y = h *ᵥ allPer Gm D.q x idx y := by
    have : allPer Gm D.q x' idx = (h.mulVecLin.restrictScalars ℝ) ∘ₗ allPer Gm D.q x idx := by
      apply b.ext
      intro i
      obtain ⟨_, ⟨v, rfl⟩, hv⟩ := (hb (b i)).1 (Submodule.subset_span ⟨i, rfl⟩)
      rw [← hv, ← hQ', hh, hQ]
      rfl
    intro y
    rw [this]; rfl
  have hblock := block_of_allPer Gm D.q x x' idx h hbij.2 hall
  let K : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ =>
    Matrix.of fun a c => h (idx.symm (τ, a)) (idx.symm (τ, c))
  have hK0 : ∀ τ (a c : Fin r), ¬ ((a : ℕ) < D.q ↔ (c : ℕ) < D.q) → K τ a c = 0 := by
    intro τ a c hac
    apply hblock
    simpa using hac
  have hK : ∀ (τ : Ψ) u, locPer τ.1 Gm D.q (FD.mat x' τ) u =
      K τ *ᵥ locPer τ.1 Gm D.q (FD.mat x τ) u := by
    intro τ u
    funext a
    have h1 := congrFun (allPer_symm Gm D.q x' idx (fun _ => u) τ) a
    rw [← h1, hall, mulVec, mulVec, dotProduct, dotProduct, ← idx.symm.sum_comp, Fintype.sum_prod_type,
      Finset.sum_eq_single τ]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [← allPer_symm Gm D.q x idx (fun _ => u) τ]
      rfl
    · intro σ _ hσ
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [hblock, zero_mul]
      simp [hσ.symm]
    · simp
  have hc := fun τ : Ψ => loc_compare τ.1 Gm hdet D.q (FD.mat x τ) (FD.mat x' τ) (K τ) (hx τ).1 (hx' τ).1
    (hK0 τ) (hK τ)
  have hhK : ∀ k k', (idx k).1 = (idx k').1 → h k k' = K (idx k).1 (idx k).2 (idx k').2 := by
    intro k k' e
    simp only [K, of_apply]
    conv_rhs => rw [Prod.mk.eta, e, Prod.mk.eta]
    simp
  refine ⟨fun τ => ((FD.mat x τ)⁻¹ * FD.mat x' τ : Matrix (Fin r) (Fin r) ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · funext τ
    exact (Matrix.mul_nonsing_inv_cancel_left (FD.mat x τ) (FD.mat x' τ)
      (isUnit_iff_ne_zero.2 (hx τ).1)).symm
  · intro τ a c hcq ha
    exact ((hc τ).1 c a hcq).symm.trans (hK0 τ c a (by simp [hcq, ha]))
  · intro k k' e h1 _
    rw [hhK k k' e]
    exact (hc _).1 _ _ h1
  · intro k k' e h1 _
    rw [hhK k k' e]
    exact (hc _).2 _ _ h1
  · intro k k' hne
    apply hblock
    rintro ⟨e1, e2⟩
    apply hne
    rw [hty, hty, e1]
    simp only [e2]
end GlobalTheory.FramePeriod
