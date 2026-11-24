-- Prove2me | solution 1 for GlobalTheory.KS.exists_locDerK_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:21:20.484003+00:00
-- url     : https://prove2.me/submissions/03b36386-1df1-4d4f-be46-8adcf0b29d79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDerivationExtendOfFormallySmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLocalDerivationAlongFibreFieldOfAffiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationLiftSmoothOverField
import Theorems.Thm_GlobalTheory_KS_liftConstHomK_smooth
import Theorems.Thm_GlobalTheory_KS_app_constFn_of_commK
import Theorems.Thm_GlobalTheory_T_existsUnique_localDerivationAlongFibreField_of_affine
import Theorems.Thm_P2M_GlobalTheory_T_exists_derivation_extend__1951aa00d8a1


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
open GlobalTheory GlobalTheory.KS
namespace GlobalTheory.KS
theorem _root_.solution : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (x₀ : R →+* K) (Y X : Scheme.{0}) (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W₀ : X.Opens), Smooth p → m ≫ p = q ≫ spMap x₀ → IsDerK x₀ D → IsAffineOpen W₀ → ∃ d, LocDerK q p m D W₀ d := by
  intro K _ R _ x₀ Y X q p m D W₀ hp hm hD hW
  letI : Algebra R Γ(X, W₀) := (liftConstHomK p W₀).toAlgebra
  haveI : Algebra.Smooth R Γ(X, W₀) := liftConstHomK_smooth p W₀ hp hW
  have hc : ∀ a, (m.app W₀).hom (algebraMap R Γ(X, W₀) a) = liftConstHomK q (m ⁻¹ᵁ W₀) (x₀ a) :=
    fun a => app_constFn_of_commK x₀ q p m hm W₀ a
  obtain ⟨d₀, h1, h2, h3⟩ := GlobalTheory.T.exists_derivation_extend' R Γ(X, W₀) Γ(Y, m ⁻¹ᵁ W₀) (m.app W₀).hom
    (fun r => liftConstHomK q (m ⁻¹ᵁ W₀) (D r)) (fun a b => by rw [hD.1, map_add])
    (fun a b => by rw [hD.2, hc, hc, map_add, map_mul, map_mul])
  obtain ⟨d, hd, -⟩ := (GlobalTheory.T.existsUnique_localDerivationAlongFibreField_of_affine K R Y X q p m D W₀ hW).1 d₀ h1 h2 h3
  exact ⟨d, hd⟩
end GlobalTheory.KS
