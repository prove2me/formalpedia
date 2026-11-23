-- Prove2me | solution 1 for GlobalTheory.IntegralCoord.exists_basis_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:47.743811+00:00
-- url     : https://prove2.me/submissions/fc7f71ca-eeb7-4342-b0cc-27d8e36db399

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsBasisOfEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_sval_pullSec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IntegralCoord
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
namespace GlobalTheory.IntegralCoord
theorem _root_.solution {S : Scheme.{0}} {A T : Over S} {L : LB A.left} {K : Type} [Fintype K]
    {φ : K → (A.left ⟶ A.left)} {ε : K → ℤ} {m : ℕ} (b₀ : Fin m → LB.Sec (LB.LinComb L φ ε))
    (hb : IsSecBasis (T := T) (A := A) _ (fun i => DVR.pullSec L φ ε (b₀ i) (snd T A).left))
    (φ' : K → ((T ⊗ A).left ⟶ A.left)) (h : φ' = fun k => (snd T A).left ≫ φ k) :
    ∃ b : Fin m → LB.Sec (LB.LinComb L φ' ε), IsSecBasis (T := T) (A := A) _ b ∧
      ∀ i (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J →
        sval (b i) r z J = sval (b₀ i) (r ≫ (snd T A).left) z J := by
  subst h
  exact ⟨_, hb, fun i Z r z J hJ => sval_pullSec φ ε (b₀ i) (snd T A).left r z hJ⟩
end GlobalTheory.IntegralCoord
