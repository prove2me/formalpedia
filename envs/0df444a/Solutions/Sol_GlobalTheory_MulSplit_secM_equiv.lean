-- Prove2me | solution 1 for GlobalTheory.MulSplit.secM_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:51:47.639873+00:00
-- url     : https://prove2.me/submissions/ef23b45e-105b-426b-99be-eedcaaf9879e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights
import Theorems.Thm_GlobalTheory_MulSplit_ev_inj
import Theorems.Thm_GlobalTheory_MulSplit_mem_Sg

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.MulSplit
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S}
namespace GlobalTheory.MulSplit
theorem _root_.solution {L : LB A.left} (hL : L.IsLB) (a : ℤ) :
    Nonempty (SecM A L a T ≃ₗ[Γ(T.left, ⊤)] Sg L (fst T A).left (Finsupp.single (snd T A).left a)) := by
  let f : SecM A L a T →ₗ[Γ(T.left, ⊤)] Vals L (fst T A).left :=
    { toFun := fun s => ev (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) _ (SecM.toSec A s)
      map_add' := fun s t => ev_add fun _ => rfl
      map_smul' := fun c s => ev_smul c fun _ => rfl }
  have hf : Function.Injective f := fun s t h => Subtype.ext (funext (ev_inj hL h))
  have hr : LinearMap.range f = Sg L (fst T A).left (Finsupp.single (snd T A).left a) := by
    ext v
    rw [mem_Sg hL (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (Fin.sum_univ_one _)]
    exact ⟨fun ⟨s, hs⟩ => ⟨SecM.toSec A s, hs⟩, fun ⟨s, hs⟩ => ⟨SecM.ofSec A s, hs⟩⟩
  exact ⟨(LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ hr)⟩
end GlobalTheory.MulSplit
