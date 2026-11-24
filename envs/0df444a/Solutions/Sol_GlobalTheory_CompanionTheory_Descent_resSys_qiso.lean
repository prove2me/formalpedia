-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.resSys_qiso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:38:53.491583+00:00
-- url     : https://prove2.me/submissions/7429eeaf-d59d-4043-b907-8f0c4a9cb176

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCover
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_res_self
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_Acyc_congr
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_allQIso_congr
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_acyc_of_cone
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_compare
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_meet_le
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_meet_le_left
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_meet_le_right
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_acyc_of_cover

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
variable (hi : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))
include hi
namespace GlobalTheory.CompanionTheory.Descent
theorem _root_.solution (hCx : CxSt) (hHt : HtpySt) (hQ : QCalcSt) (hFub : FubiniSt) (hA : AffAcycSt)
    {P : Type} [SemilatticeInf P] (S : Sys X P) : AllQIso (resSys s S) := by
  let f : AffOp X ⥤ AffOp X := 𝟭 _
  let w := wFun hi f S.fn
  have h₁ : ∀ T, (w.obj T).unop.1 ≤ (f.obj T.1).unop.1 := fun _ ↦ inf_le_left
  have h₂ : ∀ T, (w.obj T).unop.1 ≤ (S.fn.obj T.2).unop.1 := fun _ ↦ inf_le_right
  have h₃ : ∀ d, (S.fn.obj d).unop.1 ≤ (w.obj (S.fn.obj d, d)).unop.1 := fun _ ↦ le_inf le_rfl le_rfl
  have hr := compare s hCx hQ hFub f S.fn w S.fn h₁ h₂ h₃ (fun U ↦ ?_) (fun a ↦ ?_)
  · exact allQIso_congr (fun i z ↦ funext fun c ↦ res_self s _ _) hr
  · let v' : P →o X.affineOpens :=
      ⟨fun a ↦ meet hi U.unop (S.u a), fun a b h ↦ meet_le hi le_rfl (S.mono h)⟩
    have hle' : ∀ a, (v' a).1 ≤ U.unop.1 := fun _ ↦ inf_le_left
    have hinf' : ∀ a b, (v' (a ⊓ b)).1 = (v' a).1 ⊓ (v' b).1 := fun a b ↦ by
      change U.unop.1 ⊓ (S.u (a ⊓ b)).1 = (U.unop.1 ⊓ (S.u a).1) ⊓ (U.unop.1 ⊓ (S.u b).1)
      rw [S.map_inf, inf_inf_distrib_left]
    have hcov' : ⨆ a, (v' a).1 = U.unop.1 := by
      refine le_antisymm (iSup_le hle') ?_
      change _ ≤ ⨆ a, U.unop.1 ⊓ (S.u a).1
      rw [← inf_iSup_eq, S.cover, inf_top_eq]
    exact (acyc_of_cover s hi hCx hHt hQ hFub hA v' hinf' U.unop hle' hcov').congr s
      (CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _))
  · refine acyc_of_cone s hCx hHt hA _ (S.fn.obj a).unop _ (S.fn.obj a) (le_inf le_rfl le_rfl)
      (CategoryTheory.Prod.sectR (S.fn.obj a) (AffOp X) ⋙ CategoryTheory.Prod.swap _ _ ⋙
        wFun hi (𝟭 _) (𝟭 _)) (fun T ↦ (homOfLE (meet_le_left hi T.unop _)).op) (fun T ↦ (homOfLE (meet_le_right hi T.unop _)).op)
      (fun T ↦ ?_)
    exact le_inf (le_inf inf_le_left inf_le_right) inf_le_right
end GlobalTheory.CompanionTheory.Descent
