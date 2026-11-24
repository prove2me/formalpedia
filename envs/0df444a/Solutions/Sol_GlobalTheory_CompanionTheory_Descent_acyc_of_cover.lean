-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.acyc_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:30:38.370852+00:00
-- url     : https://prove2.me/submissions/27be126f-c648-4192-a09d-b2559a34b985

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCover
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_Acyc_congr
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_acyc_fin
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_acyc_of_map
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_acyc_member
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_compare
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_meet_le
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_exists_finite_cover
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



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
    {P : Type} [SemilatticeInf P] (v : P →o X.affineOpens)
    (hinf : ∀ a b, (v (a ⊓ b)).1 = (v a).1 ⊓ (v b).1) (W : X.affineOpens) (hle : ∀ a, (v a).1 ≤ W.1)
    (hcov : ⨆ a, (v a).1 = W.1) :
    Acyc s v.monotone.functor.op W.1 (fun T ↦ hle T.unop) := by
  obtain ⟨T, hT⟩ := exists_finite_cover v W hcov
  let Q : Set P := infClosure (T : Set P)
  letI : SemilatticeInf Q := Subtype.semilatticeInf (fun x y hx hy ↦ infClosed_infClosure hx hy)
  haveI : Finite Q := (T.finite_toSet.infClosure).to_subtype
  let vQ : Q →o X.affineOpens := ⟨fun q ↦ v q.1, fun a b h ↦ v.monotone h⟩
  have hleQ : ∀ a, (vQ a).1 ≤ W.1 := fun a ↦ hle a.1
  have hinfQ : ∀ a b, (vQ (a ⊓ b)).1 = (vQ a).1 ⊓ (vQ b).1 := fun a b ↦ hinf a.1 b.1
  have hcovQ' : W.1 ≤ ⨆ a, (vQ a).1 := hT.trans (iSup_le fun a ↦
    le_iSup (fun q : Q ↦ (vQ q).1) ⟨a.1, subset_infClosure a.2⟩)
  have hcovQ : ⨆ a, (vQ a).1 = W.1 := le_antisymm (iSup_le hleQ) hcovQ'
  let fP : Pᵒᵖ ⥤ AffOp X := v.monotone.functor.op
  let fQ : Qᵒᵖ ⥤ AffOp X := vQ.monotone.functor.op
  let σ : Qᵒᵖ ⥤ Pᵒᵖ := (Subtype.mono_coe _ : Monotone (Subtype.val : Q → P)).functor.op
  let w := wFun hi fP fQ
  have h₁ : ∀ T, (w.obj T).unop.1 ≤ (fP.obj T.1).unop.1 := fun _ ↦ inf_le_left
  have h₂ : ∀ T, (w.obj T).unop.1 ≤ (fQ.obj T.2).unop.1 := fun _ ↦ inf_le_right
  have h₃ : ∀ d, (fQ.obj d).unop.1 ≤ (w.obj (σ.obj d, d)).unop.1 := fun _ ↦ le_inf le_rfl le_rfl
  have hr := compare s hCx hQ hFub fP fQ w σ h₁ h₂ h₃ (fun c ↦ ?_) (fun d ↦ ?_)
  · exact acyc_of_map s hCx hA fP fQ σ _ W _ (fun T ↦ hleQ T.unop)
      (fun x hx hx' ↦ by
        obtain ⟨y, hy⟩ := hr.1.1 x hx ⟨0, by rw [hx', map_zero]⟩
        simpa using hy.symm)
      (fun n x hx hy ↦ (hr.2 n).1 x hx hy)
      (acyc_fin s hA vQ W hleQ hinfQ hcovQ)
  · let v' : Q →o X.affineOpens :=
      ⟨fun q ↦ meet hi (v c.unop) (vQ q), fun a b h ↦ meet_le hi le_rfl (vQ.monotone h)⟩
    have hle' : ∀ q, (v' q).1 ≤ (v c.unop).1 := fun _ ↦ inf_le_left
    have hinf' : ∀ a b, (v' (a ⊓ b)).1 = (v' a).1 ⊓ (v' b).1 := fun a b ↦ by
      change (v c.unop).1 ⊓ (vQ (a ⊓ b)).1 = ((v c.unop).1 ⊓ (vQ a).1) ⊓ ((v c.unop).1 ⊓ (vQ b).1)
      rw [hinfQ, inf_inf_distrib_left]
    have hcov' : ⨆ a, (v' a).1 = (v c.unop).1 := by
      refine le_antisymm (iSup_le hle') ?_
      change _ ≤ ⨆ a, (v c.unop).1 ⊓ (vQ a).1
      rw [← inf_iSup_eq]
      exact le_inf le_rfl ((hle _).trans hcovQ')
    exact (acyc_fin s hA v' (v c.unop) hle' hinf' hcov').congr s
      (CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _))
  · refine acyc_member s hCx hHt hA _ (vQ d.unop) _ d.unop.1 (le_inf le_rfl le_rfl) (fun a ↦ ?_)
    change (v a).1 ⊓ (vQ d.unop).1 ≤ (v (a ⊓ d.unop.1)).1 ⊓ (vQ d.unop).1
    rw [hinf]
    exact le_inf (le_inf inf_le_left inf_le_right) inf_le_right
end GlobalTheory.CompanionTheory.Descent
