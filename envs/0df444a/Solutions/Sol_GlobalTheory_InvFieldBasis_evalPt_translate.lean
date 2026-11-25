-- Prove2me | solution 1 for GlobalTheory.InvFieldBasis.evalPt_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:17:42.449457+00:00
-- url     : https://prove2.me/submissions/07083454-639f-4552-b2b3-f0d0a6ec1e95

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
import Theorems.Thm_GlobalTheory_InvFieldBasis_preimage_translate
import Theorems.Thm_GlobalTheory_InvFieldBasis_evalPt_pbT
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
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
private lemma evalPt_add {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Sp B ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a b : Γ(Z, O)) : evalPt x O h (a + b) = evalPt x O h a + evalPt x O h b := by
  unfold evalPt
  exact map_add _ a b
private lemma evalPt_mul {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Sp B ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a b : Γ(Z, O)) : evalPt x O h (a * b) = evalPt x O h a * evalPt x O h b := by
  unfold evalPt
  exact map_mul _ a b
private lemma evalPt_constFn' {B A : Type} [CommRing B] [CommRing A] {Z : Scheme.{0}} (x : Sp B ⟶ Z)
    (q : Z ⟶ Sp A) (φ : A →+* B) (hq : x ≫ q = Spec.map (CommRingCat.ofHom φ)) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a : A) : evalPt x O h (constFn q O a) = φ a := by
  unfold evalPt constFn
  have e1 : ∀ (g : Sp B ⟶ Sp A) (e : ⊤ ≤ g ⁻¹ᵁ ⊤), g.appLE ⊤ ⊤ e = g.appTop := fun g e => by
    simp only [Scheme.Hom.appLE]
    rw [show (homOfLE e).op = 𝟙 _ from Subsingleton.elim _ _]
    exact Category.comp_id _
  rw [← CommRingCat.comp_apply, ← Category.assoc]
  erw [Scheme.Hom.appLE_comp_appLE]
  rw [e1, hq, Scheme.ΓSpecIso_naturality]
  simp
variable {B : Type} [CommRing B] [Algebra K B]
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
theorem _root_.solution {v : epsR K ⟶ G} (hv : IsTangent v)
    {dd : ∀ O : G.left.Opens, Γ(G.left, O) → Γ(G.left, O)} (hd : IsInvDer v dd) (e : B) (he : e * e = 0)
    (z : sp (R₀ := K) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O) :
    ∃ h' : ⊤ ≤ ((Chart.spMap (epsTo K e he) ≫ v : sp (R₀ := K) B ⟶ G) * z).left ⁻¹ᵁ O, ∀ f,
      evalPt _ O h' f = evalPt z.left O h f + e * evalPt z.left O h (dd O f) := by
  let t : sp (R₀ := K) B ⟶ epsR K ⊗ G := lift (Chart.spMap (epsTo K e he)) z
  have ht1 : t ≫ ((fst (epsR K) G ≫ v) * snd (epsR K) G) =
      (Chart.spMap (epsTo K e he) ≫ v : sp (R₀ := K) B ⟶ G) * z := by
    rw [MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd]
  have ht2 : t ≫ snd (epsR K) G = z := lift_snd _ _
  have ht3 : t ≫ fst (epsR K) G = Chart.spMap (epsTo K e he) := lift_fst _ _
  have hP := preimage_translate hv O
  have hc : ∀ {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens), f ⁻¹ᵁ (g ⁻¹ᵁ U) = (f ≫ g) ⁻¹ᵁ U :=
    fun _ _ _ => rfl
  have hO : t.left ⁻¹ᵁ ((snd (epsR K) G).left ⁻¹ᵁ O) = z.left ⁻¹ᵁ O := by
    rw [hc, ← Over.comp_left, ht2]
  have hO' : ((Chart.spMap (epsTo K e he) ≫ v : sp (R₀ := K) B ⟶ G) * z).left ⁻¹ᵁ O = z.left ⁻¹ᵁ O := by
    rw [← ht1, Over.comp_left, ← hc, hP, hO]
  have hT : ⊤ ≤ t.left ⁻¹ᵁ ((snd (epsR K) G).left ⁻¹ᵁ O) := hO ▸ h
  refine ⟨hO' ▸ h, fun f => ?_⟩
  have e1 : evalPt t.left _ hT (pbT (snd (epsR K) G).left f ((snd (epsR K) G).left ⁻¹ᵁ O)) =
      evalPt z.left O h f :=
    evalPt_pbT t.left _ le_rfl hT z.left (by rw [← Over.comp_left, ht2]) h f
  have e2 : evalPt t.left _ hT (pbT (snd (epsR K) G).left (dd O f) ((snd (epsR K) G).left ⁻¹ᵁ O)) =
      evalPt z.left O h (dd O f) :=
    evalPt_pbT t.left _ le_rfl hT z.left (by rw [← Over.comp_left, ht2]) h (dd O f)
  have e3 : evalPt t.left _ hT (constFn (R := DualNumber K) (fst (epsR K) G).left
      ((snd (epsR K) G).left ⁻¹ᵁ O) DualNumber.eps) = e := by
    rw [evalPt_constFn' t.left (fst (epsR K) G).left (epsTo K e he : DualNumber K →+* B)]
    · simp
    · rw [← Over.comp_left, ht3]
      rfl
  rw [← evalPt_pbT t.left ((fst (epsR K) G ≫ v) * snd (epsR K) G).left hP.ge hT
    ((Chart.spMap (epsTo K e he) ≫ v : sp (R₀ := K) B ⟶ G) * z).left (by rw [← Over.comp_left, ht1]) _ f,
    hd O f, evalPt_add, evalPt_mul, e1, e2, e3]
end GlobalTheory.InvFieldBasis
