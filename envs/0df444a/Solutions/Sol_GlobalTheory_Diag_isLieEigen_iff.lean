-- Prove2me | solution 1 for GlobalTheory.Diag.isLieEigen_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:24:58.807511+00:00
-- url     : https://prove2.me/submissions/ed4decad-ea31-4564-a10e-8174ecfc8fd7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LeftEqIffLieVecSmul
import Theorems.Thm_GlobalTheory_Diag_diagAct_act
import Theorems.Thm_GlobalTheory_Diag_epsVec_comp_diagMap
import Theorems.Thm_GlobalTheory_Diag_left_eq_epsScaleR_iff
import Theorems.Thm_GlobalTheory_Diag_epsScaleR_base_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent IsLieComb IsLieBasis OAct epsPt
  IsLieEigen LieMult)
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.Diag
variable {S : Scheme.{0}} {k : Type} [Field k] (t : Sp k ⟶ S) {O : Type} [CommRing O]
  {X : Type} [AddCommGroup X] [Module O X] (τ : O →+* k)
namespace GlobalTheory.Diag
theorem _root_.solution (v : epsPt t ⟶ splitTorus S X) :
    IsLieEigen (diagAct S O X) t τ v ↔
      ∃ c : X →+ k, epsVec _ c = v ∧ ∀ (a : O) (x : X), c (a • x) = τ a * c x := by
  unfold IsLieEigen
  have ht : t = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) ≫ t := by
    rw [← Category.assoc, fstHom_base, Category.id_comp]
  rw [reduces_iff ht v, ← exists_epsVec_iff]
  constructor
  · rintro ⟨⟨c, rfl⟩, h2⟩
    refine ⟨c, rfl, fun a x => ?_⟩
    have h := (left_eq_epsScaleR_iff (τ a) (epsScaleR_base_comp t (τ a)) c _).1 (h2 a)
    rw [diagAct_act, epsVec_comp_diagMap] at h
    have := congrArg (fun f => f x) (epsVec_injective h)
    simpa using this
  · rintro ⟨c, rfl, hc⟩
    refine ⟨⟨c, rfl⟩, fun a => ?_⟩
    refine (left_eq_epsScaleR_iff (τ a) (epsScaleR_base_comp t (τ a)) c _).2 ?_
    rw [diagAct_act, epsVec_comp_diagMap]
    congr 1
    ext x
    simpa using hc a x
end GlobalTheory.Diag
