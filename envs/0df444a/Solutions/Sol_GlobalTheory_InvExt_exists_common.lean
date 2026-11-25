-- Prove2me | solution 1 for GlobalTheory.InvExt.exists_common
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:15:29.246329+00:00
-- url     : https://prove2.me/submissions/386abf1d-63af-4fa4-85c6-486caccaa6a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsInverseExtensionProperClosure
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


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
open GlobalTheory GlobalTheory.InvExt
namespace GlobalTheory.InvExt
theorem _root_.solution {X : Scheme.{0}} {k k' : Type} [Field k] [Field k'] (u : Sp k ⟶ X)
    (u' : Sp k' ⟶ X) (x : Sp k) (x' : Sp k') (h : u x = u' x') :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (v : Sp K ⟶ Sp k) (v' : Sp K ⟶ Sp k'),
      v ≫ u = v' ≫ u' := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x x' h
  let F := (pullback u u').residueField z
  let w : Sp (AlgebraicClosure F) ⟶ pullback u u' :=
    spMap (algebraMap F (AlgebraicClosure F)) ≫ (pullback u u').fromSpecResidueField z
  exact ⟨AlgebraicClosure F, inferInstance, inferInstance, w ≫ pullback.fst _ _,
    w ≫ pullback.snd _ _, by simp [pullback.condition]⟩
end GlobalTheory.InvExt
