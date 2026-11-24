-- Prove2me | solution 1 for GlobalTheory.FamPull.cubN_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:51:49.3348+00:00
-- url     : https://prove2.me/submissions/e17a8578-48b2-46a9-8474-9f3048aaeab4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.FamPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
namespace GlobalTheory.FamPull
theorem _root_.solution {A U : Type} [CommGroup A] [CommGroup U] (θ θ' : A → A → A → U) (Ω : A → U)
    (h : ∀ a b c, θ a b c = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
      θ' a b c) (k : ℕ) (a m x : A) :
    cubN θ k a m x = Ω (a * m ^ k * x) * (Ω (a * m ^ k))⁻¹ * (Ω (a * x))⁻¹ * Ω a *
      ((Ω (m * x))⁻¹ * Ω m * Ω x * (Ω 1)⁻¹) ^ k * cubN θ' k a m x := by
  induction k with
  | zero => simp [cubN]
  | succ k ih =>
    simp only [cubN, Finset.prod_range_succ] at ih ⊢
    rw [ih, h, pow_succ m, ← _root_.mul_assoc a, pow_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
end GlobalTheory.FamPull
