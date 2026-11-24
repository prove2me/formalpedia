-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Giv.ResProj.cross_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:21:39.048705+00:00
-- url     : https://prove2.me/submissions/b6478e30-8b17-4cfe-a665-4ad17a14b492

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoin
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_cone_rename_inl
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
variable {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ _ : Unit, Fin M) → Ω) {G : Fin M → MRing ι} {g : K → ℕ}
namespace GlobalTheory.CompanionTheory.Ar.Giv.ResProj
theorem _root_.solution (hG : ∀ i, IsMultiHomog (G i) g)
    (hrel : ∀ i j, y' ⟨(), i⟩ * aeval y (G j) = y' ⟨(), j⟩ * aeval y (G i)) (i j : Fin M) :
    (X (⟨Sum.inr (), i⟩ : Σ k, joinIdx ι 𝔅 k) : MRing (joinIdx ι 𝔅)) * rename (joinInl ι 𝔅) (G j) -
      X (⟨Sum.inr (), j⟩ : Σ k, joinIdx ι 𝔅 k) * rename (joinInl ι 𝔅) (G i) ∈ mCoordIdeal (joinVec y y') := by
  have key : ∀ (f : MRing ι) (a : K → ℕ), IsMultiHomog f a → mConeMap (joinVec y y') (rename (joinInl ι 𝔅) f) =
      C (aeval y f) * ∏ k, X (Sum.inl k) ^ a k := by
    intro f a hf
    have h1 := AlgHom.congr_fun (cone_rename_inl (ι₂ := 𝔅) y y') f
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h1
    have h2 : mConeMap (joinVec y y') (rename (joinInl ι 𝔅) f) =
        rename (Sum.inl : K → K ⊕ Unit) (mConeMap y f) := h1
    rw [h2, cone_homog y hf, map_mul, rename_C, map_prod]
    exact congrArg _ (Finset.prod_congr rfl fun k _ => by rw [map_pow, rename_X])
  have hX : ∀ i : Fin M, mConeMap (joinVec y y') (X (⟨Sum.inr (), i⟩ : Σ k, joinIdx ι 𝔅 k)) =
      C (y' ⟨(), i⟩) * X (Sum.inr ()) := by
    intro i
    simp [mConeMap, joinVec]
  unfold mCoordIdeal
  rw [RingHom.mem_ker]
  show mConeMap (joinVec y y') _ = 0
  rw [map_sub, map_mul, map_mul, key _ _ (hG j), key _ _ (hG i), hX, hX]
  have h3 := congrArg (C : Ω →+* MvPolynomial (K ⊕ Unit) Ω) (hrel i j)
  simp only [map_mul] at h3
  linear_combination (X (Sum.inr ()) * ∏ k, (X (Sum.inl k) : MvPolynomial (K ⊕ Unit) Ω) ^ g k) * h3
end GlobalTheory.CompanionTheory.Ar.Giv.ResProj
