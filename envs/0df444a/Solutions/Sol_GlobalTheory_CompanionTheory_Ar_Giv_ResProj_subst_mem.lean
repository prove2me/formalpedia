-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Giv.ResProj.subst_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:36:01.787907+00:00
-- url     : https://prove2.me/submissions/db0dc8a2-0982-49e4-8d29-3553533b3e3c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoin
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_cone_homog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Giv
open GlobalTheory.CompanionTheory.Ar.Giv.ResProj
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
variable {M : ℕ}
local notation "𝔅" => (fun _ : Unit => Fin M)
namespace GlobalTheory.CompanionTheory.Ar.Giv.ResProj
theorem _root_.solution {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ _ : Unit, Fin M) → Ω)
    {G : Fin M → MRing ι} {g : K → ℕ} (hG : ∀ i, IsMultiHomog (G i) g)
    (hrel : ∀ i j, y' ⟨(), i⟩ * aeval y (G j) = y' ⟨(), j⟩ * aeval y (G i))
    (hy' : ∃ i, y' ⟨(), i⟩ ≠ 0) {F : MRing (joinIdx ι 𝔅)} (hF : F ∈ mCoordIdeal (joinVec y y')) :
    subst G F ∈ mCoordIdeal y := by
  obtain ⟨i₀, hi₀⟩ := hy'
  have hlam : ∀ i, aeval y (G i) = y' ⟨(), i⟩ * (aeval y (G i₀) / y' ⟨(), i₀⟩) := by
    intro i
    rw [mul_div_assoc', eq_div_iff hi₀, mul_comm]
    exact hrel i₀ i
  let S : MvPolynomial (K ⊕ Unit) Ω →ₐ[Ω] MvPolynomial K Ω :=
    aeval (Sum.elim X fun _ => C (aeval y (G i₀) / y' ⟨(), i₀⟩) * ∏ k, X k ^ g k)
  have hc : (mConeMap y).comp (subst G) = (S.restrictScalars ℤ).comp (mConeMap (joinVec y y')) := by
    refine MvPolynomial.algHom_ext fun p => ?_
    obtain ⟨k | ⟨⟩, i⟩ := p
    · simp [subst, mConeMap, joinVec, S]
    · have h1 : subst G (X (⟨Sum.inr (), i⟩ : Σ k, joinIdx ι 𝔅 k)) = G i := by simp [subst, joinVec]
      have h2 : mConeMap (joinVec y y') (X (⟨Sum.inr (), i⟩ : Σ k, joinIdx ι 𝔅 k)) =
          C (y' ⟨(), i⟩) * X (Sum.inr ()) := by simp [mConeMap, joinVec]
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply]
      rw [h1, h2, cone_homog y (hG i), hlam i]
      simp [S, map_mul, mul_assoc]
  have h0 := AlgHom.congr_fun hc F
  have hF' : mConeMap (joinVec y y') F = 0 := hF
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, hF', map_zero] at h0
  exact h0
end GlobalTheory.CompanionTheory.Ar.Giv.ResProj
