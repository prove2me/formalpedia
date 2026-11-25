-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.LieModel.isGrNorm_iff_formGramAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:32:41.269799+00:00
-- url     : https://prove2.me/submissions/6a7876a1-cb8d-4d2d-89ba-9cb71ee5cfcc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_HodgeIPIffHodgeFormConj
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_LieModel_gramAt_iff_formGramAt
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_leadMinor_transpose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
variable {M : LieModel G ξ E} {L : LB G.left} {V : Lat ξ E} {r : ℕ} {b₀ : Fin r → E} {i : Fin r}
  {z : Spec (CommRingCat.of ℂ) ⟶ X} {t : Ω} {ν : ℝ}
namespace GlobalTheory.CompanionTheory.Ar
namespace LieModel
theorem _root_.solution : M.IsGrNorm L V b₀ i z t ν ↔
    ∃ (h : genPt ξ ⤳ centre z) (b : Fin r → E) (Γ : Matrix (Fin r) (Fin r) ℂ),
      (∀ s, flagStep Ω b s = flagStep Ω b₀ s) ∧ V.IsFrameAt b ⟨centre z, h⟩ ∧ b i - t • b₀ i ∈ flagStep Ω b₀ i ∧
        M.FormGramAt L z b Γ ∧ Γ.PosDef ∧ ν = Real.sqrt (leadMinor Γ (i + 1) / leadMinor Γ i) := by
  constructor
  · rintro ⟨h, b, Γ, h1, h2, h3, h4, h5, rfl⟩
    exact ⟨h, b, Γ.transpose, h1, h2, h3, M.gramAt_iff_formGramAt.1 h4, h5.transpose, by
      rw [leadMinor_transpose, leadMinor_transpose]⟩
  · rintro ⟨h, b, Γ, h1, h2, h3, h4, h5, rfl⟩
    exact ⟨h, b, Γ.transpose, h1, h2, h3, M.gramAt_iff_formGramAt.2 h4, h5.transpose, by
      rw [leadMinor_transpose, leadMinor_transpose]⟩
end LieModel
end GlobalTheory.CompanionTheory.Ar
