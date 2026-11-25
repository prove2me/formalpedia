-- Prove2me | solution 1 for GlobalTheory.ZJ.SplitPull.exists_basis_pushout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:02:40.452158+00:00
-- url     : https://prove2.me/submissions/8760833f-adda-480c-a30a-972197804334

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PullPullAndSplitPull
import Theorems.Thm_GlobalTheory_ZJ_SplitPull_free_of_isField
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open GlobalTheory.ZJ
noncomputable section
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.SplitPull
namespace GlobalTheory.ZJ.SplitPull
theorem _root_.solution {R R' : CommRingCat.{0}} (hR : IsField R) (b : R ⟶ R') :
    ∃ (J : Type) (e : J → R'), ∀ (A A' : CommRingCat.{0}) (a : R ⟶ A) (p : A ⟶ A') (q : R' ⟶ A'),
      IsPushout a b p q →
      (∀ u : A', ∃ (s : Finset J) (x : J → A), u = ∑ l ∈ s, p.hom (x l) * q.hom (e l)) ∧
      ∀ (s : Finset J) (x : J → A), ∑ l ∈ s, p.hom (x l) * q.hom (e l) = 0 → ∀ l ∈ s, x l = 0 := by
  letI := b.hom.toAlgebra
  haveI : Module.Free R R' := free_of_isField hR
  let e := Module.Free.chooseBasis R R'
  refine ⟨_, e, fun A A' a p q h => ?_⟩
  letI := a.hom.toAlgebra
  letI := p.hom.toAlgebra
  letI := q.hom.toAlgebra
  letI := (p.hom.comp a.hom).toAlgebra
  haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  have hp : Algebra.IsPushout R A R' A' := CommRingCat.isPushout_iff_isPushout.mp h
  let B := hp.out.basis e
  have hB : ∀ l, B l = q.hom (e l) := fun l => hp.out.basis_apply e l
  refine ⟨fun u => ⟨(B.repr u).support, B.repr u, ?_⟩, fun s x hx => ?_⟩
  · conv_lhs => rw [← B.linearCombination_repr u]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hB, Algebra.smul_def]; rfl
  · refine linearIndependent_iff'.1 B.linearIndependent s x ?_
    rw [← hx]
    exact Finset.sum_congr rfl fun l _ => by rw [hB, Algebra.smul_def]; rfl
end GlobalTheory.ZJ.SplitPull
