-- Prove2me | solution 1 for GlobalTheory.VolFin.eventually_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:11:47.629482+00:00
-- url     : https://prove2.me/submissions/6a0f6fa9-9a43-461e-b3e6-660196ceddc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleGlobalSectionsFunctionFieldIff
import Theorems.Thm_GlobalTheory_VolFin_gen_rs
import Theorems.Thm_GlobalTheory_VolFin_mem_basicOpen_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
open GlobalTheory.AbLaw (rs pw)
noncomputable section
open GlobalTheory GlobalTheory.VolFin
variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
namespace GlobalTheory.VolFin
theorem _root_.solution {W D : X.Opens} (hW : IsAffineOpen W) (h) (u : Γ(X, W))
    (hu : gen W h u ≠ 0) (hD : X.basicOpen u ≤ D) (hD') (a : Γ(X, D)) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ b, gen W h b = gen D hD' a * gen W h u ^ n := by
  have := hW.isLocalization_basicOpen u
  have hb := (mem_basicOpen_iff h u).2 hu
  obtain ⟨⟨b, _, m, rfl⟩, hm⟩ := IsLocalization.surj (Submonoid.powers u) (rs X hD a)
  have h1 : gen D hD' a * gen W h u ^ m = gen W h b := by
    have h2 := congrArg (gen _ hb) hm
    rw [map_mul, gen_rs] at h2
    have h3 : ∀ x : Γ(X, W), gen _ hb (algebraMap Γ(X, W) Γ(X, X.basicOpen u) x) = gen W h x :=
      fun x => gen_rs (X.basicOpen_le u) hb x
    rw [h3, h3, map_pow] at h2
    exact h2
  filter_upwards [Filter.eventually_ge_atTop m] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact ⟨b * u ^ k, by rw [map_mul, map_pow, ← h1, pow_add, _root_.mul_assoc]⟩
end GlobalTheory.VolFin
