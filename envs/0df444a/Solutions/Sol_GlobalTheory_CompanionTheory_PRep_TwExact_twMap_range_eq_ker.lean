-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:42:52.345779+00:00
-- url     : https://prove2.me/submissions/ad7d742d-157c-43aa-8754-059d58dd6ac9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_MirabolicDerivatives_TwistedKernels_TwKerLeComapOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteSupport
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwKerEqMapOfSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistedJacquetExactSmooth
import Theorems.Thm_GlobalTheory_CompanionTheory_PRep_JacExact_twKer_reflect
import Theorems.Thm_GlobalTheory_CompanionTheory_PRep_twKer_map_closed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.BZMir
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PRep GlobalTheory.CompanionTheory.PRep.TwExact
namespace GlobalTheory.CompanionTheory.PRep.TwExact
theorem _root_.solution : ∀ {G V₁ V₂ V₃ : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂)
    (ρ₃ : Representation ℂ G V₃), IsSmooth ρ₁ → IsSmooth ρ₂ → IsSmooth ρ₃ →
    ∀ (N : Subgroup G) (θ : N →* ℂˣ), IsOpen (θ.ker : Set N) →
    (∀ s : Finset G, (↑s : Set G) ⊆ N → ∃ L : Subgroup G, L ≤ N ∧ (↑s : Set G) ⊆ L ∧
      IsCompact (L : Set G)) →
    ∀ (f : V₁ →ₗ[ℂ] V₂) (g : V₂ →ₗ[ℂ] V₃) (hf : ∀ x v, f (ρ₁ x v) = ρ₂ x (f v))
      (hg : ∀ x v, g (ρ₂ x v) = ρ₃ x (g v)), LinearMap.range f = LinearMap.ker g →
    LinearMap.range (twMap ρ₁ ρ₂ N θ f hf) = LinearMap.ker (twMap ρ₂ ρ₃ N θ g hg) := by
  intro G V₁ V₂ V₃ _ _ _ _ _ _ _ _ _ ρ₁ ρ₂ ρ₃ h₁ h₂ h₃ N θ hθ hN f g hf hg hfg
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (GlobalTheory.PRep.twKer ρ₁ N θ) x
    rw [LinearMap.mem_ker]
    have hv : g (f v) = 0 := by
      have h0 : f v ∈ LinearMap.ker g := hfg ▸ LinearMap.mem_range_self f v
      exact LinearMap.mem_ker.mp h0
    simp only [GlobalTheory.BZMir.twMap, Submodule.mapQ_apply, hv, Submodule.Quotient.mk_zero]
  · intro x hx
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective (GlobalTheory.PRep.twKer ρ₂ N θ) x
    rw [LinearMap.mem_ker] at hx
    simp only [GlobalTheory.BZMir.twMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    have hKinv : ∀ x : G, LinearMap.ker g ≤ (LinearMap.ker g).comap (ρ₂ x) := by
      intro x u hu
      rw [Submodule.mem_comap, LinearMap.mem_ker, hg, LinearMap.mem_ker.mp hu, map_zero]
    let ρq : Representation ℂ G (V₂ ⧸ LinearMap.ker g) :=
      { toFun := fun x => (LinearMap.ker g).mapQ (LinearMap.ker g) (ρ₂ x) (hKinv x)
        map_one' := by
          ext u
          simp
        map_mul' := by
          intro x y
          ext u
          simp [Module.End.mul_apply] }
    have hq : GlobalTheory.PRep.IsSmooth ρq := by
      intro u
      obtain ⟨w0, rfl⟩ := Submodule.Quotient.mk_surjective _ u
      rw [isOpen_iff_forall_mem_open]
      intro x0 hx0
      refine ⟨(fun y => x0 * y) '' {y | ρ₂ y w0 = w0}, ?_, isOpenMap_mul_left x0 _ (h₂ w0),
        ⟨1, by simp, by simp⟩⟩
      rintro _ ⟨y, hy, rfl⟩
      rw [Set.mem_ofPred_eq] at hy hx0 ⊢
      have e1 : ρq y (Submodule.Quotient.mk w0) = Submodule.Quotient.mk (ρ₂ y w0) := rfl
      rw [map_mul, Module.End.mul_apply, e1, hy, hx0]
    let gb : (V₂ ⧸ LinearMap.ker g) →ₗ[ℂ] V₃ := (LinearMap.ker g).liftQ g le_rfl
    have hgb_inj : Function.Injective gb := by
      intro a b hab
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      have hab' : g a = g b := hab
      rw [Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, hab', sub_self]
    have hgb_eq : ∀ (x : G) (u : V₂ ⧸ LinearMap.ker g), gb (ρq x u) = ρ₃ x (gb u) := by
      intro x u
      obtain ⟨w0, rfl⟩ := Submodule.Quotient.mk_surjective _ u
      exact hg x w0
    have hmem : (Submodule.Quotient.mk w : V₂ ⧸ LinearMap.ker g) ∈ GlobalTheory.PRep.twKer ρq N θ :=
      GlobalTheory.CompanionTheory.PRep.JacExact.twKer_reflect ρq ρ₃ hq h₃ N θ hθ hN gb hgb_inj hgb_eq _ hx
    rw [GlobalTheory.CompanionTheory.PRep.twKer_map_closed ρ₂ ρq N θ (LinearMap.ker g).mkQ
      (Submodule.mkQ_surjective _) (fun x v => rfl)] at hmem
    obtain ⟨w', hw', hw'eq⟩ := hmem
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq, ← hfg, LinearMap.mem_range] at hw'eq
    obtain ⟨v, hv⟩ := hw'eq
    rw [LinearMap.mem_range]
    refine ⟨Submodule.Quotient.mk (-v), ?_⟩
    simp only [GlobalTheory.BZMir.twMap, Submodule.mapQ_apply, map_neg, hv]
    rw [Submodule.Quotient.eq]
    have e2 : -(w' - w) - w = -w' := by abel
    rw [e2]
    exact Submodule.neg_mem _ hw'
end GlobalTheory.CompanionTheory.PRep.TwExact
