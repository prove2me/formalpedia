-- Prove2me | solution 1 for GlobalTheory.AdmLoc.Ea_equiv_of_class_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:34:01.746519+00:00
-- url     : https://prove2.me/submissions/765e87a0-8ecf-4f61-ab65-99b024dd7caa

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_ReciprocityTheory_BasicDefinitions_AdRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Theorems.Thm_GlobalTheory_AdmLoc_twistRep_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdmLoc
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open ReciprocityTheory.Def (Z1 B1 H1 d0 d1 C1)
open scoped Pointwise
variable {O G : Type} [CommRing O] [Group G]
variable {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
variable [TopologicalSpace G]
variable (W : Representation O G M) (χ : G →* Oˣ) {X : Type} [AddCommGroup X] [Module O X] {c : O}
    (hc : ∀ x : X, c • x = 0)
namespace GlobalTheory.AdmLoc
theorem _root_.solution {z z' : ↥(Z1 (twCoef W χ X) ⊤)}
    (h : (Submodule.Quotient.mk z : H1 (twCoef W χ X) ⊤) = Submodule.Quotient.mk z') :
    ∃ e : ((M ⊗[O] X) × (O ⧸ Ideal.span {c})) ≃ₗ[O] ((M ⊗[O] X) × (O ⧸ Ideal.span {c})),
      (∀ g x, e (Ea W χ hc z g x) = Ea W χ hc z' g (e x)) ∧ (∀ m, e (m, 0) = (m, 0)) ∧ ∀ x, (e x).2 = x.2 := by
  obtain ⟨b, -, hb⟩ := (Submodule.Quotient.eq _).mp h
  have hb' : ∀ g, twCoef W χ X g b - b = (z : G → M ⊗[O] X) g - (z' : G → M ⊗[O] X) g := fun g => congrFun hb g
  let f := cycMap (smul_tensor_eq_zero (M := M) hc) b
  refine ⟨LinearEquiv.ofLinearMap
    ((LinearMap.id.coprod f).prod (LinearMap.snd O _ _)) ((LinearMap.id.coprod (-f)).prod (LinearMap.snd O _ _))
    (LinearMap.ext fun x => by simp) (LinearMap.ext fun x => by simp), ?_, fun m => by simp, fun x => by simp⟩
  rintro g ⟨m, y⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  simp only [Ea, twistRep_apply, map_smul]
  congr 1
  change (twCoef W χ X g m + y • (z : G → M ⊗[O] X) g + y • b, Ideal.Quotient.mk _ y) =
    (twCoef W χ X g (m + y • b) + y • (z' : G → M ⊗[O] X) g, Ideal.Quotient.mk _ y)
  rw [map_add, map_smul, eq_add_of_sub_eq (hb' g)]
  congr 1
  simp only [smul_add, smul_sub]
  abel
end GlobalTheory.AdmLoc
