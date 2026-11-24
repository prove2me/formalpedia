-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.wedge_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:57:42.265914+00:00
-- url     : https://prove2.me/submissions/88b62aaf-8775-41aa-a702-da3bc0966493

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_HodgeAlt_alt__Multi_4e0913c07ff2
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_ext2
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_map2
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_eq_zero_of_alt
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R V V' : Type} [CommRing R] [AddCommGroup V] [AddCommGroup V'] [Module R V] [Module R V']
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution [Module.Finite R V] [Module.Projective R V] (p q m : V →ₗ[R] V')
    (P Q : V' →ₗ[R] V) (hPp : ∀ v, P (p v) = v) (hPq : ∀ v, P (q v) = 0) (hQp : ∀ v, Q (p v) = 0)
    (hQq : ∀ v, Q (q v) = v) (hm : ∀ v, m v = p v + q v) (τ : ⋀[R]^2 V)
    (h : exteriorPower.map 2 m τ = exteriorPower.map 2 p τ + exteriorPower.map 2 q τ) : τ = 0 := by
  refine eq_zero_of_alt τ fun l l' ↦ ?_
  have h1 : alt (l ∘ₗ P) (l' ∘ₗ Q) ∘ₗ exteriorPower.map 2 m = alt l l' := ext2 fun a b ↦ by
    simp only [LinearMap.comp_apply, map2, alt_ιMulti, hm, map_add, hPp, hPq, hQp, hQq, add_zero,
      zero_add, map_zero]
  have h2 : alt (l ∘ₗ P) (l' ∘ₗ Q) ∘ₗ exteriorPower.map 2 p = 0 := ext2 fun a b ↦ by
    simp only [LinearMap.comp_apply, map2, alt_ιMulti, hQp, LinearMap.zero_apply, map_zero]
    ring
  have h3 : alt (l ∘ₗ P) (l' ∘ₗ Q) ∘ₗ exteriorPower.map 2 q = 0 := ext2 fun a b ↦ by
    simp only [LinearMap.comp_apply, map2, alt_ιMulti, hPq, LinearMap.zero_apply, map_zero]
    ring
  have e := congrArg (alt (l ∘ₗ P) (l' ∘ₗ Q)) h
  rw [map_add, show alt (l ∘ₗ P) (l' ∘ₗ Q) (exteriorPower.map 2 m τ) = alt l l' τ from
      LinearMap.congr_fun h1 τ, show alt (l ∘ₗ P) (l' ∘ₗ Q) (exteriorPower.map 2 p τ) = 0 from
      LinearMap.congr_fun h2 τ, show alt (l ∘ₗ P) (l' ∘ₗ Q) (exteriorPower.map 2 q τ) = 0 from
      LinearMap.congr_fun h3 τ, add_zero] at e
  exact e
end GlobalTheory.CompanionTheory.HodgeAlt
