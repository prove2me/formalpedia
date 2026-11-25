-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotLoc.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:27:18.131536+00:00
-- url     : https://prove2.me/submissions/cb4ecde1-5b7b-4e1c-a1bc-71f0f83526a0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
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
variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {e : Sp R ⟶ X}
  {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W] [IsCentralScalar R W]
  {y₀ : Sp (TrivSqZeroExt R W) ⟶ X}
  {R' : Type} [CommRing R'] [Algebra R R'] {A C : Type} [CommRing A] [CommRing C] [Algebra C A]
  [Algebra A R'] {j : Sp A ⟶ X} {k : Sp C ⟶ Sp R}
variable {M : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
  [Module R M] [IsScalarTower R R' M]
variable {N : Type} [AddCommGroup N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N]
  [Module R N] [IsScalarTower R R' N]
namespace GlobalTheory.CompanionTheory.CotLoc
theorem _root_.solution (ψ : A →+* TrivSqZeroExt R' M) (hψ : Good (C := C) ψ) :
    ∃ v : (R' ⊗[A] KaehlerDifferential C A) →ₗ[R'] M,
      ∀ a, v (1 ⊗ₜ KaehlerDifferential.D C A a) = (ψ a).snd := by
  letI : Module A M := Module.compHom M (algebraMap A R')
  haveI : IsScalarTower A R' M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module C M := Module.compHom M ((algebraMap A R').comp (algebraMap C A))
  haveI : IsScalarTower C A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hfst : ∀ a, (ψ a).fst = algebraMap A R' a := fun a => congrArg (fun f => f a) hψ.1
  have hC : ∀ c, ψ (algebraMap C A c) =
      TrivSqZeroExt.inl (algebraMap A R' (algebraMap C A c)) := fun c => congrArg (fun f => f c) hψ.2
  let l : A →ₗ[C] M :=
    { toFun := fun a => (ψ a).snd
      map_add' := fun a b => by simp
      map_smul' := fun c a => by
        rw [Algebra.smul_def, map_mul, hC]
        simp }
  let d : Derivation C A M := Derivation.mk' l (fun a b => by
    show (ψ (a * b)).snd = a • (ψ b).snd + b • (ψ a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, op_smul_eq_smul]
    rfl)
  refine ⟨d.liftKaehlerDifferential.liftBaseChange R', fun a => ?_⟩
  rw [LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]
  rfl
end GlobalTheory.CompanionTheory.CotLoc
