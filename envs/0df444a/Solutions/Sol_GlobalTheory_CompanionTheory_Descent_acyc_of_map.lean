-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.acyc_of_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:01:21.487016+00:00
-- url     : https://prove2.me/submissions/43aa2aa3-8986-45b4-908c-8f05712cfcf9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCover
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_pull_d
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_d_d
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_pull_aug
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_d_aug

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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Descent
variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
variable {C D E : Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]
namespace GlobalTheory.CompanionTheory.Descent
theorem _root_.solution (hCx : CxSt) (hA : AffAcycSt) (f : D ⥤ AffOp X) (f' : E ⥤ AffOp X) (σ : E ⥤ D) (h)
    (W : X.affineOpens) (hle hle')
    (Q1 : ∀ x, dn (f ⋙ OAff s) 0 x = 0 → pulln (rm s f f' σ h) 0 x = 0 → x = 0)
    (Q2 : ∀ n x, dn (f ⋙ OAff s) (n + 1) x = 0 →
      (∃ y, dn (f' ⋙ OAff s) n y = pulln (rm s f f' σ h) (n + 1) x) → ∃ y, dn (f ⋙ OAff s) n y = x)
    (A : Acyc s f' W.1 hle') : Acyc s f W.1 hle := by
  refine ⟨fun a b hab ↦ A.1 ?_, fun x ↦ ⟨fun hx ↦ ?_, ?_⟩, fun n x ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
  · rw [← pull_aug s f f' σ h W.1 hle hle', ← pull_aug s f f' σ h W.1 hle hle', hab]
  · have k : dn (f' ⋙ OAff s) 0 (pulln (rm s f f' σ h) 0 x) = 0 := by
      rw [← pull_d hCx, hx, map_zero]
    obtain ⟨w, hw⟩ := (A.2.1 _).1 k
    refine ⟨w, sub_eq_zero.1 (Q1 _ ?_ ?_)⟩
    · rw [map_sub, d_aug s hCx hA, hx, sub_zero]
    · rw [map_sub, pull_aug s f f' σ h W.1 hle hle', hw, sub_self]
  · rintro ⟨w, rfl⟩
    exact d_aug s hCx hA f W hle w
  · have k : dn (f' ⋙ OAff s) (n + 1) (pulln (rm s f f' σ h) (n + 1) x) = 0 := by
      rw [← pull_d hCx, hx, map_zero]
    exact Q2 n x hx ((A.2.2 n _).1 k)
  · rintro ⟨y, rfl⟩
    exact d_d hCx n y
end GlobalTheory.CompanionTheory.Descent
