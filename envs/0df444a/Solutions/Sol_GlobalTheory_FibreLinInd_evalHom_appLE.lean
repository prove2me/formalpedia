-- Prove2me | solution 1 for GlobalTheory.FibreLinInd.evalHom_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:03.094393+00:00
-- url     : https://prove2.me/submissions/48d3cc2d-85ba-471c-90cd-ad9b4f3a0492

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenSetOfLinearIndependentOnFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FibreLinInd
variable {K : Type} [Field K] {P G : Scheme.{0}}
namespace GlobalTheory.FibreLinInd
theorem _root_.solution (h : Sp K ⟶ P) (U : P.Opens) (hU : ⊤ ≤ h ⁻¹ᵁ U) (π : P ⟶ G) (V : G.Opens)
    (hV : U ≤ π ⁻¹ᵁ V) (a : Γ(G, V)) :
    evalHom h U hU (π.appLE V U hV a) = valF (h ≫ π) V a := by
  have hle : ⊤ ≤ (h ≫ π) ⁻¹ᵁ V := fun y hy => hV (hU hy)
  rw [valF, dif_pos hle, ← Scheme.Hom.appLE_comp_appLE h π V U ⊤ hV hU]
  rfl
end GlobalTheory.FibreLinInd
