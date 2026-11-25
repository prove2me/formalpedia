-- Prove2me | solution 1 for GlobalTheory.TraceDescent.exactAt_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:58:21.814094+00:00
-- url     : https://prove2.me/submissions/ce4798fa-6cf4-474b-8584-4b2c3f070dbb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExactAtSectionCubeOfMulPullback
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_cubeComplex_exactAt_succ_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory
noncomputable section
open GlobalTheory GlobalTheory.TraceDescent
open GlobalTheory.AbLaw.PowVanish
namespace GlobalTheory.TraceDescent
theorem _root_.solution {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (A B : GlobalTheory.Cube.{0} κ R)
    (φ : ∀ s, A.obj s →+ B.obj s) (T : ∀ s, B.obj s →+ B.obj s)
    (hφ : ∀ {s t : Finset κ} (h : s ⊆ t) x, φ t (Cube.res A h x) = Cube.res B h (φ s x))
    (hT : ∀ {s t : Finset κ} (h : s ⊆ t) x, T t (Cube.res B h x) = Cube.res B h (T s x))
    (inj : ∀ s, Function.Injective (φ s)) (n : ℕ) (hn : IsUnit (n : R))
    (himg : ∀ s y, ∃ x, φ s x = T s y) (htr : ∀ s x, T s (φ s x) = n • φ s x) (p : ℕ)
    (H : (cubeComplex B).ExactAt p) : (cubeComplex A).ExactAt p := by
  have dφ : ∀ q (x : Cube.Term A q), Cube.d B q (fun s => φ s.1 (x s)) = fun t => φ t.1 (Cube.d A q x t) :=
    fun q x => funext fun t => by
      simp only [Cube.d_apply, map_sum, map_zsmul, hφ]
  have dT : ∀ q (x : Cube.Term B q), Cube.d B q (fun s => T s.1 (x s)) = fun t => T t.1 (Cube.d B q x t) :=
    fun q x => funext fun t => by
      simp only [Cube.d_apply, map_sum, map_zsmul, hT]
  rcases p with _ | p
  · rw [cubeComplex_exactAt_zero_iff'] at H ⊢
    intro x y hxy
    have : (fun s => φ s.1 (x s) : Cube.Term B 0) = fun s => φ s.1 (y s) := H (by rw [dφ, dφ, hxy])
    exact funext fun s => inj _ (congrFun this s)
  · rw [cubeComplex_exactAt_succ_iff] at H ⊢
    intro x
    refine ⟨fun hx => ?_, fun ⟨y, hy⟩ => hy ▸ Cube.d_d A p y⟩
    obtain ⟨y, hy⟩ := (H (fun s => φ s.1 (x s))).1 (by
      rw [dφ, hx]; exact funext fun t => map_zero _)
    choose z hz using fun s : {s : Finset κ // s.card = p} => himg s.1 (y s)
    have key : Cube.d A p z = (n : R) • x := funext fun t => inj _ (by
      have e := congrFun (dφ p z) t
      have e' := congrFun (dT p y) t
      simp only [hz] at e
      rw [← e, e', hy, htr, Pi.smul_apply, Nat.cast_smul_eq_nsmul, map_nsmul])
    obtain ⟨u, hu⟩ := hn.exists_left_inv
    exact ⟨u • z, by rw [map_smul, key, smul_smul, hu, one_smul]⟩
end GlobalTheory.TraceDescent
