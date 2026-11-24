-- Prove2me | solution 1 for GlobalTheory.SS.Ord.multilinear_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:20:42.913584+00:00
-- url     : https://prove2.me/submissions/a83a9d22-8cbb-44b1-b021-fdf0acf27e00

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder

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
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Ord
namespace GlobalTheory.SS.Ord
theorem _root_.solution {S P Q I : Type} [CommRing S] [AddCommGroup P] [Module S P] [AddCommGroup Q]
    [Module S Q] [Fintype I] [DecidableEq I] (f : MultilinearMap S (fun _ : I => P) Q) (G : Set P)
    (N : Submodule S Q) (h : ∀ v : I → P, (∀ i, v i ∈ G) → f v ∈ N) (v : I → P)
    (hv : ∀ i, v i ∈ Submodule.span S G) : f v ∈ N := by
  have key : ∀ s : Finset I, ∀ v : I → P, (∀ i, v i ∈ Submodule.span S G) → (∀ i, i ∉ s → v i ∈ G) → f v ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun v _ h' => h v fun i => h' i (by simp)
    | insert a s ha ih =>
      intro v h1 h2
      have : Submodule.span S G ≤ N.comap (f.toLinearMap v a) := by
        refine Submodule.span_le.2 fun g hg => ?_
        refine ih (Function.update v a g) (fun i => ?_) (fun i hi => ?_)
        · by_cases e : i = a
          · subst e; simpa using Submodule.subset_span hg
          · simpa [Function.update_of_ne e] using h1 i
        · by_cases e : i = a
          · subst e; simpa using hg
          · rw [Function.update_of_ne e]; exact h2 i (by simp [e, hi])
      simpa using this (h1 a)
  exact key Finset.univ v hv (by simp)
end GlobalTheory.SS.Ord
