-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotLoc.equiv_general
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:16:35.929705+00:00
-- url     : https://prove2.me/submissions/26535a19-816b-424e-af8b-83888554e380

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_equiv_of_universal
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_phiOf_good
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_exists_lift
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_opAct_central
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_compHom_tower
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_tensor_ext
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_one_tmul_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_kaehler_ext
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLoc
namespace GlobalTheory.CompanionTheory.CotLoc
theorem _root_.solution {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {e : Sp R ⟶ X}
    (hes : e ≫ s = 𝟙 _) {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W]
    [IsCentralScalar R W] {y₀ : Sp (TrivSqZeroExt R W) ⟶ X} (hcot : IsCot s e W y₀)
    {R' : Type} [CommRing R'] [Algebra R R'] {A C : Type} [CommRing A] [CommRing C] [Algebra C A]
    [Algebra A R'] {j : Sp A ⟶ X} {k : Sp C ⟶ Sp R} [IsOpenImmersion j] [Mono k]
    (hjs : j ≫ s = spMap (algebraMap C A) ≫ k)
    (hje : spMap (algebraMap A R') ≫ j = spMap (algebraMap R R') ≫ e)
    {P : Type} [AddCommGroup P] [Module R' P] (eP : (R' ⊗[A] KaehlerDifferential C A) ≃ₗ[R'] P) :
    Nonempty ((R' ⊗[R] W) ≃ₗ[R'] P) := by
  letI := opAct R' (R' ⊗[R] W)
  haveI := opAct_central R' (R' ⊗[R] W)
  letI := opAct R' P
  haveI := opAct_central R' P
  letI : Module R P := Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' P := compHom_tower R R' P
  let d : A →+ P :=
    { toFun := fun a => eP ((1 : R') ⊗ₜ[A] KaehlerDifferential.D C A a)
      map_zero' := by simp
      map_add' := fun a b => by simp [TensorProduct.tmul_add] }
  have hd : ∀ a, d a = eP ((1 : R') ⊗ₜ[A] KaehlerDifferential.D C A a) := fun _ => rfl
  have hm : ∀ a b, d (a * b) = algebraMap A R' a • d b + algebraMap A R' b • d a := by
    intro a b
    simp only [hd, Derivation.leibniz, TensorProduct.tmul_add, one_tmul_smul, map_add, map_smul]
  have hc : ∀ c : C, d (algebraMap C A c) = 0 := by
    intro c
    simp [hd]
  refine equiv_of_universal hcot hes hjs hje (TensorProduct.mk R R' W 1) (phiOf d hm)
    (phiOf_good d hm hc) ?_ ?_ ?_ ?_
  · intro u
    refine ⟨u.liftBaseChange R', ?_⟩
    ext w
    simp
  · intro ψ hψ
    obtain ⟨v, hv⟩ := exists_lift ψ hψ
    refine ⟨v ∘ₗ eP.symm.toLinearMap, RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_⟩
    · have := congrArg (fun f => f a) hψ.1
      simpa [tsz, phiOf] using this.symm
    · have := hv a
      simpa [tsz, phiOf, hd] using this
  · intro f g h
    exact tensor_ext fun w => congrArg (fun f => f w) h
  · intro f g h
    have key : f ∘ₗ eP.toLinearMap = g ∘ₗ eP.toLinearMap := by
      refine kaehler_ext fun a => ?_
      have := congrArg (fun F => (F a).snd) h
      simpa [tsz, phiOf, hd] using this
    refine LinearMap.ext fun x => ?_
    have := congrArg (fun F => F (eP.symm x)) key
    simpa using this
end GlobalTheory.CompanionTheory.CotLoc
