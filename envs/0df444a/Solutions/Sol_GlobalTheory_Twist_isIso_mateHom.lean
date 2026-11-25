-- Prove2me | solution 1 for GlobalTheory.Twist.isIso_mateHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:12:17.183622+00:00
-- url     : https://prove2.me/submissions/ce179647-52ea-40f6-9414-527dc224cefc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasicoherentOfLocallyIso
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self val_res le_iSup_inf unitMod homOfLinear isoOfLinear toMod)
open GlobalTheory
open GlobalTheory.Twist
variable {X Y : Scheme.{0}}
variable {F G : X.Modules}
variable {C D : Type*} [Category C] [Category D] {P : C ⥤ D} {Q : D ⥤ C} (adj : P ⊣ Q)
  (S : C ⥤ C) (T : D ⥤ D) (e : Q ⋙ S ≅ T ⋙ Q)
namespace GlobalTheory.Twist
theorem _root_.solution [S.IsEquivalence] [T.IsEquivalence] (A : C) : IsIso (mateHom adj S T e A) := by
  have key (B : D) : Function.Bijective
      fun ψ : T.obj (P.obj A) ⟶ T.obj B => mateHom adj S T e A ≫ ψ := by
    have h₁ : Function.Bijective fun χ : P.obj A ⟶ B => T.map χ :=
      (Functor.FullyFaithful.ofFullyFaithful T).map_bijective _ _
    rw [← Function.Bijective.of_comp_iff _ h₁, ← Function.Bijective.of_comp_iff'
      (adj.homEquiv (S.obj A) (T.obj B)).bijective]
    have h₂ : Function.Bijective fun χ : A ⟶ Q.obj B => S.map χ :=
      (Functor.FullyFaithful.ofFullyFaithful S).map_bijective _ _
    have h₃ : Function.Bijective fun χ : S.obj A ⟶ S.obj (Q.obj B) =>
        (χ ≫ e.hom.app B : S.obj A ⟶ Q.obj (T.obj B)) :=
      (Iso.homToEquiv (e.app B)).bijective
    convert (h₃.comp h₂).comp (adj.homEquiv A B).bijective using 1
    ext χ
    have h₄ := e.hom.naturality χ
    dsimp at h₄ ⊢
    rw [Adjunction.homEquiv_naturality_right, mateHom, Equiv.apply_symm_apply, Category.assoc,
      Adjunction.homEquiv_unit, S.map_comp_assoc, h₄]
  refine isIso_of_coyoneda_map_bijective _ fun B => ?_
  let i := T.objObjPreimageIso B
  have h₅ : Function.Bijective fun ψ : T.obj (P.obj A) ⟶ T.obj (T.objPreimage B) => ψ ≫ i.hom :=
    (Iso.homToEquiv i).bijective
  have h₆ : Function.Bijective fun ψ : P.obj (S.obj A) ⟶ T.obj (T.objPreimage B) => ψ ≫ i.hom :=
    (Iso.homToEquiv i).bijective
  rw [← Function.Bijective.of_comp_iff _ h₅]
  convert h₆.comp (key _) using 1
  ext ψ
  simp
end GlobalTheory.Twist
