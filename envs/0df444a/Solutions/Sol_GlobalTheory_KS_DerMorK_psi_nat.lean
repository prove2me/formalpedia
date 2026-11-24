-- Prove2me | solution 1 for GlobalTheory.KS.DerMorK.psi_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:42:45.439849+00:00
-- url     : https://prove2.me/submissions/e963fa8b-8c52-4c54-8707-66e137c0a8df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHomOfDerivation
import Theorems.Thm_GlobalTheory_KS_DerMorK_res_constFn
import Theorems.Thm_GlobalTheory_KS_DerMorK_res_app

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
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.DerMorK
variable {K : Type} [Field K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K} (π : Y' ⟶ Sp (DualNumber K)) (ρ : Y' ⟶ Y)
  {R : Type} [CommRing R] {D : R → K} {X : Scheme.{0}} {p : X ⟶ Sp R} {m : Y ⟶ X}
  {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
namespace GlobalTheory.KS.DerMorK
theorem _root_.solution (hd : LocDerK q p m D ⊤ d) (W W' : X.Opens) (h : W' ≤ W) (f : Γ(X, W)) :
    psi π ρ hd W' (resG X h f) = resG Y' ((ρ ≫ m).preimage_mono h) (psi π ρ hd W f) := by
  have h1 : m ⁻¹ᵁ W' ≤ m ⁻¹ᵁ W := m.preimage_mono h
  have h2 : (ρ.app (m ⁻¹ᵁ W')).hom ((m.app W').hom (resG X h f)) +
      constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W') DualNumber.eps * (ρ.app (m ⁻¹ᵁ W')).hom (d W' (resG X h f)) =
      resG Y' (ρ.preimage_mono h1) ((ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f) +
      constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W) DualNumber.eps * (ρ.app (m ⁻¹ᵁ W)).hom (d W f)) := by
    rw [hd.res W W' h le_top, rsT, dif_pos h1, res_app, res_app, res_app, map_add, map_mul, res_constFn]
  exact h2
end GlobalTheory.KS.DerMorK
