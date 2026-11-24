-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Giv.ResProj.cross_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:38:16.787712+00:00
-- url     : https://prove2.me/submissions/c2412a03-c163-47bb-a929-6c6adc18c2db

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoin
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_evC_rename_inl
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_cross_mem

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
variable {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ _ : Unit, Fin M) → Ω) {G : Fin M → MRing ι} {g : K → ℕ}
namespace GlobalTheory.CompanionTheory.Ar.Giv.ResProj
theorem _root_.solution (hG : ∀ i, IsMultiHomog (G i) g)
    (hrel : ∀ i j, y' ⟨(), i⟩ * aeval y (G j) = y' ⟨(), j⟩ * aeval y (G i))
    {z : (Σ k, joinIdx ι 𝔅 k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (joinVec y y'))) (i j : Fin M) :
    z ⟨Sum.inr (), i⟩ * evC (z ∘ joinInl ι 𝔅) (G j) = z ⟨Sum.inr (), j⟩ * evC (z ∘ joinInl ι 𝔅) (G i) := by
  have h := hz.2 _ (cross_mem y y' hG hrel i j)
  rw [map_sub, map_sub, map_mul, map_mul, map_mul, map_mul, map_X, map_X, eval_X, eval_X] at h
  have e := fun f => evC_rename_inl (ι₂ := 𝔅) z f
  simp only [evC] at e ⊢
  rw [e, e] at h
  exact sub_eq_zero.mp h
end GlobalTheory.CompanionTheory.Ar.Giv.ResProj
