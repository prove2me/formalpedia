-- Prove2me | solution 1 for GlobalTheory.periods_eq_frame_periods
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:12:58.300745+00:00
-- url     : https://prove2.me/submissions/93f3db14-0199-4888-8ae4-505e9aa219d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodsEqFramePeriods
import Theorems.Thm_GlobalTheory_FramePeriod_isPeriod_frame
import Theorems.Thm_GlobalTheory_exists_frame_of_isPeriod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : (U.Di i).La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (idx : Fin g ≃ Ψ × Fin r) (Pf : FD.Frame Ψ r → ((U.Di i).La →+ (Fin g → ℂ))), (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ k, ty k = if ((idx k).2 : ℕ) < (U.Di i).q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1) → FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, (((U.Di i).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → r = (U.Di i).p + (U.Di i).q → (∀ x v k, Pf x v k = if ((idx k).2 : ℕ) < (U.Di i).q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → (∀ x ∈ FD.GG Ψ Gm (U.Di i).q, IsPeriod (U.Di i) ty (Pf x) ∧ U.u i (Pf x) ≫ Xo.s = spMap σ) ∧ ∀ P, IsPeriod (U.Di i) ty P → ∃ x ∈ FD.GG Ψ Gm (U.Di i).q, Pf x = P := by
  intro E _ _ _ H D l Xo σ g ty U i r ξ Gm φ Ψ idx Pf hΨ hty hξ hpos hφ hr hPf
  refine ⟨fun x hx => ?_, fun P hP => ?_⟩
  · have h := ((FramePeriod.isPeriod_frame E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hφ
      hr).2 x hx).2 (Pf x) (hPf x)
    exact ⟨h, U.over_σ i _ h⟩
  · obtain ⟨x, hx, h⟩ := exists_frame_of_isPeriod E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos
      hφ hr P hP
    exact ⟨x, hx, AddMonoidHom.ext fun v => funext fun k => (hPf x v k).trans (h v k).symm⟩
end GlobalTheory
