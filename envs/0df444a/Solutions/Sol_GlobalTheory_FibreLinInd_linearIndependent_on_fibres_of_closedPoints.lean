-- Prove2me | solution 1 for GlobalTheory.FibreLinInd.linearIndependent_on_fibres_of_closedPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:41:49.084279+00:00
-- url     : https://prove2.me/submissions/9fc79e81-59a7-49bd-b136-46177b4c03ac

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenSetOfLinearIndependentOnFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LinearIndependentOnFibresOfClosedPoints
import Theorems.Thm_GlobalTheory_FibreLinInd_geometric_of_field
import Theorems.Thm_GlobalTheory_FibreLinInd_isOpen_setOf_linearIndependent_on_fibres
import Theorems.Thm_GlobalTheory_jacobson_closedPoints_tools_int


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
namespace GlobalTheory.FibreLinInd
theorem _root_.solution :
    ∀ (G Z : Scheme.{0}) (π : Z ⟶ Sp ℤ) [LocallyOfFiniteType π] (f : G ⟶ Z) [Flat f] [LocallyOfFinitePresentation f] (L : LB G), L.IsLB → ∀ (r : ℕ) (s : Fin r → LB.Sec L), let P : Z → Prop := fun z => ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Z), Set.range x = {z} → ∀ c : Fin r → K, (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x → ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0; (∀ z, IsClosed ({z} : Set Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Z), Set.range x = {z} ∧ ∀ c : Fin r → K, (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x → ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0) → ∀ z, P z := by
  intro G Z π _ f _ _ L hL r s P h z
  let U : Z.Opens := ⟨{z | P z}, isOpen_setOf_linearIndependent_on_fibres G Z f L hL r s⟩
  have hU : U = ⊤ := (GlobalTheory.jacobson_closedPoints_tools_int Z π).2.2.1 U ⊤ fun y hy => by
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨K, _, x, hx, hz⟩ := h y hy
    intro K' _ _ x' hx' c hc
    exact geometric_of_field G Z f L r s y K x hx hz K' x' hx' c hc
  have : z ∈ U := by rw [hU]; trivial
  exact this
end GlobalTheory.FibreLinInd
