-- Prove2me | solution 1 for GlobalTheory.InvFieldBasis.evalPt_expPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:51:59.470399+00:00
-- url     : https://prove2.me/submissions/50674f75-8547-4c98-bf1a-ee3e807cc55b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningFieldStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PreimageTranslate
import Theorems.Thm_GlobalTheory_InvFieldBasis_evalPt_translate
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply


section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS GlobalTheory.TangentOrigin GlobalTheory.SqZero GlobalTheory.LieBaseChange
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD pushR pullR fB)
open TrivSqZeroExt (inl inr)
noncomputable section
namespace GlobalTheory.InvFieldBasis
variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] {n : ℕ}
variable {C : Type} [CommRing C] [Algebra K C]
variable {B : Type} [CommRing B] [Algebra K B]
private lemma evalPt_congr' {B : Type} [CommRing B] {Z : Scheme.{0}} {x y : Sp B ⟶ Z} (hxy : x = y)
    (O : Z.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ O) (hy : ⊤ ≤ y ⁻¹ᵁ O) (s : Γ(Z, O)) : evalPt x O hx s = evalPt y O hy s := by
  subst hxy
  rfl
end GlobalTheory.InvFieldBasis
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS GlobalTheory.TangentOrigin GlobalTheory.SqZero GlobalTheory.LieBaseChange
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD pushR pullR fB)
open TrivSqZeroExt (inl inr)
noncomputable section
open GlobalTheory GlobalTheory.InvFieldBasis
variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] {n : ℕ}
variable {C : Type} [CommRing C] [Algebra K C]
variable {B : Type} [CommRing B] [Algebra K B]
namespace GlobalTheory.InvFieldBasis
theorem _root_.solution {v : Fin n → (epsR K ⟶ G)} (hv : ∀ i, IsTangent (v i))
    {dd : Fin n → ∀ O : G.left.Opens, Γ(G.left, O) → Γ(G.left, O)} (hd : ∀ i, IsInvDer (v i) (dd i))
    (e : Fin n → B) (he : ∀ i j, e i * e j = 0)
    (z : sp (R₀ := K) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O) :
    ∃ h' : ⊤ ≤ (expPt v e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
      evalPt _ O h' f = evalPt z.left O h f + ∑ i, e i * evalPt z.left O h (dd i O f) := by
  induction n with
  | zero =>
    have h1 : expPt v e (fun i => he i i) * z = z := by
      simp only [expPt, List.ofFn_zero, List.prod_nil]
      exact _root_.one_mul z
    refine ⟨by rw [h1]; exact h, fun f => ?_⟩
    have hx : (expPt v e (fun i => he i i) * z).left = z.left := congrArg (fun w => w.left) h1
    exact (evalPt_congr' hx O _ h f).trans (by simp)
  | succ n ih =>
    have hs : expPt v e (fun i => he i i) * z =
        (Chart.spMap (epsTo K (e 0) (he 0 0)) ≫ v 0 : sp (R₀ := K) B ⟶ G) *
          (expPt (fun i => v i.succ) (fun i => e i.succ) (fun i => he i.succ i.succ) * z) := by
      rw [← _root_.mul_assoc]
      congr 1
      simp only [expPt, List.ofFn_succ, List.prod_cons]
    obtain ⟨h1, H1⟩ := ih (v := fun i => v i.succ) (hv := fun i => hv i.succ) (dd := fun i => dd i.succ)
      (hd := fun i => hd i.succ) (e := fun i => e i.succ) (he := fun i j => he i.succ j.succ)
    obtain ⟨h2, H2⟩ := evalPt_translate (hv 0) (hd 0) (e 0) (he 0 0) _ O h1
    refine ⟨by rw [hs]; exact h2, fun f => ?_⟩
    have hx : (expPt v e (fun i => he i i) * z).left =
        ((Chart.spMap (epsTo K (e 0) (he 0 0)) ≫ v 0 : sp (R₀ := K) B ⟶ G) *
          (expPt (fun i => v i.succ) (fun i => e i.succ) (fun i => he i.succ i.succ) * z)).left :=
      congrArg (fun w => w.left) hs
    rw [evalPt_congr' hx O _ h2 f, H2 f, H1 f, H1 (dd 0 O f), Fin.sum_univ_succ]
    have hz : e 0 * ∑ i : Fin n, e i.succ * evalPt z.left O h (dd i.succ O (dd 0 O f)) = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun i _ => by rw [← _root_.mul_assoc, he 0 i.succ]; simp
    rw [_root_.mul_add, hz]
    ring
end GlobalTheory.InvFieldBasis
