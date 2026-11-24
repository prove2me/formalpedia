-- Prove2me | solution 1 for GlobalTheory.KeyPow.normalAt_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:24:33.732849+00:00
-- url     : https://prove2.me/submissions/2509ad77-4ff8-4847-9422-2f884cd5ead2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Theorems.Thm_GlobalTheory_KeyPow_smul_one_row

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.KeyPow
namespace GlobalTheory.KeyPow
theorem _root_.solution (x : KeyIn ℂ) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) :
    NormalAt x τ 1 a b 1 ↔ ∃ u : HolUnif x.P.A x.P.L x.P.g,
      τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧
      (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
      u.IsRig x.rig ∧ u.IsFn x.th (thetaChar τ a b) ∧
      ∀ i, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x.v i) := by
  unfold NormalAt
  simp only [smul_one_row]
  constructor
  · rintro ⟨u, h1, h2, h3, h4, h5, h6⟩
    refine ⟨u, h1, h2, h3, h4, ?_, h6⟩
    convert h5 using 1
    funext z
    simp
  · rintro ⟨u, h1, h2, h3, h4, h5, h6⟩
    refine ⟨u, h1, h2, h3, h4, ?_, h6⟩
    convert h5 using 1
    funext z
    simp
end GlobalTheory.KeyPow
