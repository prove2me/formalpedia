-- Prove2me | solution 1 for GlobalTheory.HostModel.eq_of_genRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:33:22.613582+00:00
-- url     : https://prove2.me/submissions/a123e565-5a30-4330-a55e-73b0f14fb1e4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsWitDataLevelAgree
import Theorems.Thm_GlobalTheory_ToricData_hom_eq_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HostModel
open ToricData
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {l : Level H} (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k)
variable (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F]
variable [Algebra (FractionRing k) F]
  (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
    algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)))
include hF
namespace GlobalTheory.HostModel
theorem _root_.solution {n : ℕ} (e : 𝓞 E ≃ₗ[𝓞 E] 𝓞 E) (x : 𝓞 E → F) (q₀ : QkPt (arcIn c k bF).D₀ F n)
    (q₁ q₂ : QkPt (witP c k bF).toPre F n) (hy : q₁.y = q₂.y)
    (h₁ : ∀ z, GenRel (witIso c k bF) (q₁.g.s (e z)) (q₀.g.s z) (x z))
    (h₂ : ∀ z, GenRel (witIso c k bF) (q₂.g.s (e z)) (q₀.g.s z) (x z)) : q₁ = q₂ := by
  obtain ⟨y₀, g₀, e₀⟩ := q₀
  obtain ⟨y₁, g₁, e₁⟩ := q₁
  obtain ⟨y₂, g₂, e₂⟩ := q₂
  obtain ⟨t₀, rfl⟩ := (pt_bijective (fun _ : 𝓞 E => (1 : (FractionRing k)ˣ)) F).2 g₀
  obtain ⟨t₁, rfl⟩ := (pt_bijective (arcExp (X := 𝓞 E) k (arcForm l)) F).2 g₁
  obtain ⟨t₂, rfl⟩ := (pt_bijective (arcExp (X := 𝓞 E) k (arcForm l)) F).2 g₂
  obtain rfl : y₁ = y₂ := hy
  obtain rfl : t₁ = t₂ := hom_eq_iff.1 fun χ => by
    obtain ⟨z, rfl⟩ := e.surjective χ
    exact Units.ext (((genRel_pt_iff _ _ _ F hF _ _ _ _ _).1 (h₁ z)).trans
      ((genRel_pt_iff _ _ _ F hF _ _ _ _ _).1 (h₂ z)).symm)
  rfl
end GlobalTheory.HostModel
