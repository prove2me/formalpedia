-- Prove2me | solution 1 for GlobalTheory.KS.PtDual.fst_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:07.41018+00:00
-- url     : https://prove2.me/submissions/c59e6935-59c5-42f5-8bbe-6fb7064441f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPoint
import Theorems.Thm_GlobalTheory_KS_PtDual_ev_comp
import Theorems.Thm_GlobalTheory_KS_PtDual_le_preimage_iff
import Theorems.Thm_P2M_GlobalTheory_valAt__eq_valAtHom_eb5802171cfc


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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.PtDual
variable {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S]
namespace GlobalTheory.KS.PtDual
theorem _root_.solution {y : Sp ℂ ⟶ X} {v : Sp (DualNumber ℂ) ⟶ X} (hv : pt0 ≫ v = y) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W)
    (f : Γ(X, W)) : (ev v W h f).fst = valAt' y W f := by
  subst hv
  have h' := (le_preimage_iff v W).1 h
  rw [valAt'_eq_valAtHom _ h']
  exact (ev_comp _ v W h h' f).symm
end GlobalTheory.KS.PtDual
