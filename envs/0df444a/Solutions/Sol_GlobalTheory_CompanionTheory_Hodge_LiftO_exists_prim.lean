-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.LiftO.exists_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:36:04.127954+00:00
-- url     : https://prove2.me/submissions/4f716a1d-8f08-468e-ae66-431a8a7c9e21

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_evT_tmul
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.LiftO
variable {R : Type} [CommRing R] {C E : Type} [Category.{0} C] [Category.{0} E]
  {F : C ⥤ CommAlgCat.{0} R} {G : E ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.Hodge.LiftO
theorem _root_.solution (muF : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (hF : ∀ f ω T T' φ, muF (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (t : Z1 F ⊗[R] Glob1 F) (h0 : (H1.mk F).rTensor (Glob1 F) t = 0) :
    ∃ β : A0 F, ∀ T T' φ, muF t T T' φ = β T' - p1 F φ (β T) := by
  let d' : C0 F →ₗ[R] Z1 F := (d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)
  have hex : Function.Exact d' (H1.mk F) := fun y ↦ by
    rw [H1.mk_eq_zero]
    exact ⟨fun ⟨g, hg⟩ ↦ ⟨g, Subtype.ext hg⟩, fun ⟨g, hg⟩ ↦ ⟨g, congrArg Subtype.val hg⟩⟩
  have key : ∀ (s : C0 F ⊗[R] Glob1 F) (T T' : C) (φ : T ⟶ T'),
      muF ((d').rTensor (Glob1 F) s) T T' φ = evT s T' - p1 F φ (evT s T) := fun s ↦ by
    induction s using TensorProduct.induction_on with
    | zero => intro T T' φ; simp
    | tmul g ω =>
      intro T T' φ
      rw [LinearMap.rTensor_tmul, hF, evT_tmul, evT_tmul, oneFormsMapOfFunctorMorphism_smul, ← ω.2 φ, ← sub_smul]
      rfl
    | add x y hx hy =>
      intro T T' φ
      simp only [map_add, Pi.add_apply, hx, hy]
      abel
  obtain ⟨s, rfl⟩ := (rTensor_exact (Glob1 F) hex (H1.mk_surjective F) t).1 h0
  exact ⟨evT s, key s⟩
end GlobalTheory.CompanionTheory.Hodge.LiftO
