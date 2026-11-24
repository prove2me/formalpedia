-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotLift.isCot_of_lifting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:55:35.666496+00:00
-- url     : https://prove2.me/submissions/91363de5-a461-4380-8574-2f5665ff53d4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedImmersionUniversalSquareZero
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLift_spMap_comp_spMap
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLift_spMap_inj
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLift_tsz_theta
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLift_snd_tsz_theta
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
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLift
namespace GlobalTheory.CompanionTheory.CotLift
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X) (P : Type) [CommRing P] (α : R →+* P) (ε : P →+* R) (j : Sp P ⟶ X), ε.comp α = RingHom.id R → (∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) → j ≫ s = spMap α → spMap ε ≫ j = e → Mono j → (∀ (Q B : Type) [CommRing Q] [CommRing B] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ X), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → ∃ φ : P →+* Q, spMap φ ≫ j = y) → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module R W) (_ : Module Rᵐᵒᵖ W) (_ : IsCentralScalar R W) (y₀ : Sp (TrivSqZeroExt R W) ⟶ X), IsCot s e W y₀ := by
  intro R _ X s e P _ α ε j h hsq hj hje hm hlift
  haveI := hm
  refine ⟨KerW α ε, inferInstance, inferInstance, inferInstance, inferInstance, spMap (theta h hsq) ≫ j, ?_⟩
  unfold IsCot
  refine ⟨?_, ?_, ?_⟩
  · have e1 : (theta h hsq).comp α = TrivSqZeroExt.inlHom R (KerW α ε) := by
      refine RingHom.ext fun r ↦ TrivSqZeroExt.ext ?_ (KerW.ext' ?_)
      · simp [eps_alpha h]
      · simp [eps_alpha h]
    rw [Category.assoc, hj, spMap_comp_spMap, e1]
  · have e1 : (TrivSqZeroExt.fstHom R R (KerW α ε)).toRingHom.comp (theta h hsq) = ε :=
      RingHom.ext fun a ↦ theta_fst h hsq a
    rw [← Category.assoc, spMap_comp_spMap, e1, hje]
  · intro B _ _ M _ _ _ _ _ _ y hy1 hy2
    obtain ⟨φ, hφ⟩ := hlift (TrivSqZeroExt B M) B (TrivSqZeroExt.fstHom B B M).toRingHom (algebraMap R B) y
      (fun b ↦ ⟨TrivSqZeroExt.inl b, rfl⟩)
      (fun a b ha hb ↦ by
        have ha' : a.fst = 0 := ha
        have hb' : b.fst = 0 := hb
        apply TrivSqZeroExt.ext <;> simp [ha', hb']) hy2
    have hα : φ.comp α = (TrivSqZeroExt.inlHom B M).comp (algebraMap R B) := spMap_inj (by
      rw [← spMap_comp_spMap, ← hj, ← Category.assoc, hφ, hy1])
    have hf : (TrivSqZeroExt.fstHom B B M).toRingHom.comp φ = (algebraMap R B).comp ε :=
      spMap_inj ((cancel_mono j).1 (by
        rw [← spMap_comp_spMap, Category.assoc, hφ, hy2, ← spMap_comp_spMap, Category.assoc, hje]))
    have hf' : ∀ a, (φ a).fst = algebraMap R B (ε a) := fun a ↦ congrArg (fun f ↦ f a) hf
    refine ⟨uOf φ hα hf', ?_, ?_⟩
    · change y = spMap (tsz (uOf φ hα hf')) ≫ spMap (theta h hsq) ≫ j
      rw [← Category.assoc, spMap_comp_spMap, tsz_theta, hφ]
    · intro u' hu'
      have e1 : (tsz u').comp (theta h hsq) = φ := spMap_inj ((cancel_mono j).1 (by
        rw [← spMap_comp_spMap, Category.assoc, hφ]
        exact hu'.symm))
      refine LinearMap.ext fun w ↦ ?_
      rw [← snd_tsz_theta (B := B) h hsq u' w, e1]
      rfl
end GlobalTheory.CompanionTheory.CotLift
