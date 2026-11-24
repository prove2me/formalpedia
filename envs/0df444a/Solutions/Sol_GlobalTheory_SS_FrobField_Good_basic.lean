-- Prove2me | solution 1 for GlobalTheory.SS.FrobField.Good.basic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:16:45.232262+00:00
-- url     : https://prove2.me/submissions/4f03d8f0-a673-4756-b321-55c9e3400861

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFrobGBaseChange
import Theorems.Thm_GlobalTheory_SS_FrobField_Q_res

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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobField
namespace GlobalTheory.SS.FrobField
namespace Good
theorem _root_.solution {X : Scheme.{0}} {F : End X} {q : ℕ} (hq : 0 < q) {U : X.Opens} (hU : IsAffineOpen U)
    (H : ∀ f, Good F q U f) (g : Γ(X, U)) (f : Γ(X, X.basicOpen g)) : Good F q (X.basicOpen g) f := by
  have := hU.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g f
  obtain ⟨m, hm, qa, qg⟩ := (H a).two (H g)
  have hb : X.basicOpen g = (show X ⟶ X from F ^ m) ⁻¹ᵁ X.basicOpen g := by
    obtain ⟨h, e⟩ := qg
    have h1 := Scheme.basicOpen_appLE (show X ⟶ X from F ^ m) U U h.le g
    erw [e] at h1
    rw [Scheme.basicOpen_pow _ _ (pow_pos hq m)] at h1
    refine h1.trans (inf_eq_right.2 ?_)
    exact ((show X ⟶ X from F ^ m).preimage_mono (X.basicOpen_le g)).trans h.ge
  obtain ⟨_, ea⟩ := qa.res (X.basicOpen_le g) hb
  obtain ⟨_, eg⟩ := qg.res (X.basicOpen_le g) hb
  refine ⟨m, hm, hb, ?_⟩
  change _ = algebraMap Γ(X, U) Γ(X, X.basicOpen g) a ^ _ at ea
  change _ = algebraMap Γ(X, U) Γ(X, X.basicOpen g) g ^ _ at eg
  have hu : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen g) g) := IsLocalization.Away.algebraMap_isUnit g
  have h2 := congrArg ((show X ⟶ X from F ^ m).appLE _ _ hb.le).hom ha
  rw [map_mul, map_pow] at h2
  erw [ea, eg] at h2
  rw [← ha, mul_pow, ← pow_mul, ← pow_mul, mul_comm n] at h2
  exact (hu.pow _).mul_right_cancel h2
end Good
end GlobalTheory.SS.FrobField
