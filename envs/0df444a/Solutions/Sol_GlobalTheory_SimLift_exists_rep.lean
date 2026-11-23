-- Prove2me | solution 1 for GlobalTheory.SimLift.exists_rep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:23.748227+00:00
-- url     : https://prove2.me/submissions/a4337763-cd96-40c3-a19a-7e705d7c12a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ModNOfDvdModulus
import Theorems.Thm_GlobalTheory_SimLift_ext_form
import Theorems.Thm_GlobalTheory_SimLift_exists_vec

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
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.SimLift
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
namespace GlobalTheory.SimLift
theorem _root_.solution (B : D.La → D.La → ℤ) (h1 : ∀ a a' b, B (a + a') b = B a b + B a' b)
    (h2 : ∀ a b b', B a (b + b') = B a b + B a b')
    (h3 : ∀ (c : 𝓞 E) a b, B (c • a) b = B a (H.bar c • b)) :
    ∃ u : D.La →ₗ[𝓞 E] D.La, ∀ a b, D.EF (u a) b = B a b := by
  choose u hu using fun a => exists_vec D (B a) (h2 a)
  refine ⟨⟨⟨u, fun a a' => ext_form D fun b => ?_⟩, fun c a => ext_form D fun b => ?_⟩, hu⟩
  · rw [map_add, LinearMap.add_apply, hu, hu, hu, h1]
  · simp only [RingHom.id_apply]
    rw [D.adj, hu, hu, h3]
end GlobalTheory.SimLift
