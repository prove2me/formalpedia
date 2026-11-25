-- Prove2me | solution 1 for GlobalTheory.FrameFibre.exists_level_block_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:46:42.456087+00:00
-- url     : https://prove2.me/submissions/b6db728f-3ef6-4d5e-b968-486fb3487caf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameOfPeriodLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsEqNsmulOfDvdPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Theorems.Thm_GlobalTheory_FrameFibre_exists_gl
import Theorems.Thm_GlobalTheory_FrameFibre_herm_of_trace
import Theorems.Thm_GlobalTheory_FrameFibre_lact_mem_GG
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_GlobalTheory_FramePeriod_cmType
import Theorems.Thm_GlobalTheory_FramePeriod_frame_of_period_linear
import Theorems.Thm_GlobalTheory_FramePeriod_isPeriod_frame
import Theorems.Thm_GlobalTheory_LevelHalf_trivial_mod_of_trivial_on_half
import Theorems.Thm_GlobalTheory_per_move
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FrameFibre
variable {E : Type} [Field E] [NumberField E] {r : ℕ}
variable [IsCMField E]
namespace GlobalTheory.FrameFibre
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : (U.Di i).La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (idx : Fin g ≃ Ψ × Fin r) (Pf : FD.Frame Ψ r → ((U.Di i).La →+ (Fin g → ℂ))), (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ k, ty k = if ((idx k).2 : ℕ) < (U.Di i).q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1) → FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, (((U.Di i).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → r = (U.Di i).p + (U.Di i).q → (∀ x v k, Pf x v k = if ((idx k).2 : ℕ) < (U.Di i).q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → ∀ x ∈ FD.GG Ψ Gm (U.Di i).q, ∀ x' ∈ FD.GG Ψ Gm (U.Di i).q, U.u i (Pf x) = U.u i (Pf x') → ∃ (γ : GL (Fin r) E) (b : FD.Frame Ψ r), FD.IsUStab Gm (LinearMap.range φ) γ ∧ (∀ v, ∃ w, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ v = φ v + l.M • φ w) ∧ (∀ v, ∃ w, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ v = φ v + l.A • φ w) ∧ x' = FD.rmul (FD.lact γ x) b ∧ ∀ τ (a c : Fin r), (c : ℕ) < (U.Di i).q → (U.Di i).q ≤ (a : ℕ) → b τ a c = 0 := by
  classical
  intro E _ _ _ H D l Xo σ g ty U i r ξ Gm φ Ψ idx Pf hΨ hty hξ hpos hlat hr hPf x hx x' hx' hu
  have hper := (FramePeriod.isPeriod_frame E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hlat hr).2
  obtain ⟨gam, h, hiso, hhalf, hA, hh⟩ :=
    (U.fibre i _ _ ((hper x hx).2 _ (hPf x)) ((hper x' hx').2 _ (hPf x'))).1 hu
  have hM := LevelHalf.trivial_mod_of_trivial_on_half E H (U.Di i) l gam hiso hhalf
  obtain ⟨γ, hγ⟩ := exists_gl φ hlat.1 hlat.2.1 gam
  have hξ0 : ξ ≠ 0 := by
    have hcm := FramePeriod.cmType H Ψ hΨ
    obtain ⟨s⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ Ψ := by
      by_cases h : ComplexEmbedding.conjugate s ∈ Ψ
      · exact ⟨_, h⟩
      · exact ⟨s, (hcm s).2 h⟩
    rintro rfl
    simpa using hpos τ hτ
  have hun := herm_of_trace φ hlat.2.1 Gm γ ξ hξ0 fun v w => by
    rw [hγ, hγ, ← hlat.2.2.2.2, ← hlat.2.2.2.2, hiso]
  have hmove := (per_move E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hlat).2.1 x γ (Pf x)
    (Pf (FD.lact γ x)) hun (hPf x) (hPf _)
  obtain ⟨b, hb, hb0, -⟩ := FramePeriod.frame_of_period_linear E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty
    hξ hpos hlat (Pf (FD.lact γ x)) _ (lact_mem_GG hun hx) x' hx' (hPf _) (Pf x') (hPf _)
    (LinearMap.toMatrix' h.toLinearMap) fun v => by
      obtain ⟨a, rfl⟩ := gam.surjective v
      rw [LinearMap.toMatrix'_mulVec, hh, hmove a (gam a) (hγ a).symm]
      rfl
  refine ⟨γ, b, ⟨hun, fun y => ⟨?_, ?_⟩⟩, fun v => ?_, fun v => ?_, hb, hb0⟩
  · rintro ⟨v, rfl⟩
    exact ⟨gam v, (hγ v).symm⟩
  · rintro ⟨v, hv⟩
    refine ⟨gam.symm v, ?_⟩
    apply (Matrix.mulVec_injective_of_isUnit γ.isUnit)
    rw [hγ, LinearEquiv.apply_symm_apply, hv]
  · obtain ⟨e, he⟩ := hM v
    exact ⟨e, by rw [hγ, he, map_add, map_nsmul]⟩
  · obtain ⟨e, he⟩ := hA v
    exact ⟨e, by rw [hγ, he, map_add, map_nsmul]⟩
end GlobalTheory.FrameFibre
