-- Prove2me | solution 1 for GlobalTheory.GenScheme.exists_torus_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:57:57.882722+00:00
-- url     : https://prove2.me/submissions/c8b6b9a7-7e41-4198-ba1b-de5777d65ef6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties

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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory
open GlobalTheory.GenScheme
variable {B : Scheme.{0}} {κ : Type} {N : κ → LB B} {G : Scheme.{0}} {q : G ⟶ B}
  {u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ}
open SplitTorus
namespace GlobalTheory.GenScheme
theorem _root_.solution {S : Scheme.{0}} {T : Over S} (t : κ → Γ(T.left, ⊤)ˣ) :
    ∃ a : T ⟶ splitTorus S (κ →₀ ℤ), ∀ k, val a (Finsupp.single k 1) = (t k).val := by
  refine ⟨ofVal (Finsupp.liftAddHom fun k => zmultiplesHom _ (Additive.ofMul (t k))), fun k => ?_⟩
  rw [val_ofVal]
  simp
end GlobalTheory.GenScheme
