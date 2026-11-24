-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LKDens.burnside
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:42:10.906155+00:00
-- url     : https://prove2.me/submissions/331cb667-fba5-4274-82f5-168da800835a

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_RhoSurj
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LKDens
open CompanionTheory.D.LK
open CompanionTheory.D.DSIC (KStab)
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.LKDens
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V)
    (hnt : Nontrivial V) (hirr : ∀ W : Submodule ℂ V, (∀ a : A, ∀ w ∈ W, ρ a w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Function.Surjective ρ := by
  classical
  letI : Module A V := Module.compHom V (ρ : A →+* Module.End ℂ V)
  have hsm : ∀ (a : A) (x : V), a • x = ρ a x := fun _ _ => rfl
  haveI : IsScalarTower ℂ A V := ⟨fun c a x => by simp [hsm]⟩
  haveI : IsSimpleModule A V := by
    rw [isSimpleModule_iff]
    refine { eq_bot_or_eq_top := fun W => ?_ }
    rcases hirr (W.restrictScalars ℂ) (fun a w hw => W.smul_mem a hw) with h | h
    · left; exact (Submodule.restrictScalars_eq_bot_iff ℂ A V).1 h
    · right; exact (Submodule.restrictScalars_eq_top_iff ℂ A V).1 h
  have hscal : ∀ φ : Module.End A V, ∃ c : ℂ, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := V) ℂ).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  intro f
  let F : Module.End (Module.End A V) V :=
    { toFun := f
      map_add' := fun x y => by simp
      map_smul' := fun φ m => by
        obtain ⟨c, hc⟩ := hscal φ
        simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
  let b := Module.finBasis ℂ V
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
  refine ⟨r, b.ext fun i => ?_⟩
  exact (hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))).symm
end GlobalTheory.CompanionTheory.LKDens
