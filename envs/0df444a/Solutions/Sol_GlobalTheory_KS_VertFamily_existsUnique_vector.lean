-- Prove2me | solution 1 for GlobalTheory.KS.VertFamily.existsUnique_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:51:51.296375+00:00
-- url     : https://prove2.me/submissions/a90cc9cc-ba32-4971-a0ae-c7f7b993bbf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationOfFibreOfKillsBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationUniformisedAbelianVarietyUniqueVecStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangent
import Theorems.Thm_GlobalTheory_KS_VertFamily_ex_over
import Theorems.Thm_GlobalTheory_KS_VertFamily_ptDer_fderiv
import Theorems.Thm_GlobalTheory_KS_VertFamily_fderiv_constFn
import Theorems.Thm_GlobalTheory_KS_VertFamily_fn_eq
import Theorems.Thm_GlobalTheory_T_germDerivation_of_fibre_of_kills_base
import Theorems.Thm_GlobalTheory_T_germDerivation_uniformised_abelianVariety_unique_vector


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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.VertFamily
variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)
namespace GlobalTheory.KS.VertFamily
theorem _root_.solution : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ z δ, PtDer ((u.ex z).left ≫ m) δ → (∀ r, δ ⊤ (constFn p ⊤ r) = 0) → ∃! w, ∀ W f, z ∈ dom u m W → δ W f = fderiv ℂ (fn u m W f) z w := by
  intro P₀ u Hm χ hG R _ x₀ X p m _ hpb z δ hδ hc
  obtain ⟨hex, huniq⟩ := GlobalTheory.T.germDerivation_of_fibre_of_kills_base P₀.A R x₀ X p m hpb (u.ex z).left (ex_over u z)
  obtain ⟨δ₀, hδ₀, hc₀, hδδ₀⟩ := hex δ hδ hc
  obtain ⟨w, hw, hwu⟩ := GlobalTheory.T.germDerivation_uniformised_abelianVariety_unique_vector P₀ u Hm χ hG z δ₀ hδ₀ hc₀
  refine ⟨w, fun W f hz => ?_, fun w' hw' => hwu w' fun O f hO => ?_⟩
  · rw [hδδ₀ W f hz, hw (m ⁻¹ᵁ W) ((m.app W).hom f) hz, fn_eq]
  · have hD := ptDer_fderiv u z w'
    have hpt : PtDer (u.ex z).left
        (fun O f => δ₀ O f - fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w') := by
      refine ⟨fun V hV f f' => ?_, fun V hV f f' => ?_, fun V V' hle hV f => ?_⟩
      · have h1 := hδ₀.add V hV f f'
        have h2 := hD.add V hV f f'
        linear_combination h1 - h2
      · have h1 := hδ₀.mul V hV f f'
        have h2 := hD.mul V hV f f'
        linear_combination h1 - h2
      · have h1 := hδ₀.res V V' hle hV f
        have h2 := hD.res V V' hle hV f
        linear_combination h1 - h2
    have key := huniq _ hpt (fun a => by
        have h1 := hc₀ a
        have h2 := fderiv_constFn u z w' a
        linear_combination h1 - h2)
      (fun V f hV => by
        have h1 := hδδ₀ V f hV
        have h2 := hw' V f hV
        rw [fn_eq] at h2
        linear_combination h2 - h1) O f hO
    exact sub_eq_zero.mp key
end GlobalTheory.KS.VertFamily
