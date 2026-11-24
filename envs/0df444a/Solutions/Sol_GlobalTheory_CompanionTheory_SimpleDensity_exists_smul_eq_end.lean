-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SimpleDensity.exists_smul_eq_end
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:05:11.408868+00:00
-- url     : https://prove2.me/submissions/7d519218-11ad-4a90-b41d-86f8e0baa7c7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmulEqOnFinset
import Theorems.Thm_GlobalTheory_CompanionTheory_SimpleDensity_exists_smul_eq_on_finset
import Theorems.Thm_GlobalTheory_CompanionTheory_SimpleDensity_exists_scalar_of_simple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SimpleDensity
namespace GlobalTheory.CompanionTheory.SimpleDensity
theorem _root_.solution : ∀ (A : Type) [Ring A] [Algebra ℂ A] (J : Type) [Fintype J] (M : J → Type)
    [∀ j, AddCommGroup (M j)] [∀ j, Module ℂ (M j)] [∀ j, Module A (M j)] [∀ j, IsScalarTower ℂ A (M j)]
    [∀ j, FiniteDimensional ℂ (M j)] [∀ j, IsSimpleModule A (M j)],
    (∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j) →
      ∀ f : ∀ j, Module.End ℂ (M j), ∃ a : A, ∀ j (x : M j), a • x = f j x := by
  intro A _ _ J _ M _ _ _ _ _ _ hiso f
  classical
  have hne : ∀ i j, i ≠ j → ∀ φ : M i →ₗ[A] M j, φ = 0 := by
    intro i j hij φ
    by_contra h
    exact hij (hiso i j ⟨LinearEquiv.ofBijective φ (LinearMap.bijective_of_ne_zero h)⟩)
  have hf : ∀ i (φ : M i →ₗ[A] M i) x,
      (f i).toAddMonoidHom (φ x) = φ ((f i).toAddMonoidHom x) := by
    intro i φ x
    obtain ⟨c, hc⟩ := exists_scalar_of_simple φ
    simp [hc]
  let b : ∀ j, Module.Basis (Module.Free.ChooseBasisIndex ℂ (M j)) ℂ (M j) := fun j => Module.Free.chooseBasis ℂ (M j)
  haveI : ∀ j, Fintype (Module.Free.ChooseBasisIndex ℂ (M j)) := fun j => inferInstance
  let s : Finset (∀ j, M j) :=
    Finset.univ.biUnion fun j => Finset.univ.image fun k => (Pi.single j (b j k) : ∀ j, M j)
  obtain ⟨r, hr⟩ := exists_smul_eq_on_finset M hne (fun j => (f j).toAddMonoidHom) hf s
  refine ⟨r, fun j x => ?_⟩
  have hlin : (Algebra.lsmul ℂ ℂ (M j) r : Module.End ℂ (M j)) = f j := by
    refine (b j).ext fun k => ?_
    have hm : (Pi.single j (b j k) : ∀ j, M j) ∈ s :=
      Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩⟩
    have := hr _ hm j
    simpa using this.symm
  exact LinearMap.congr_fun hlin x
end GlobalTheory.CompanionTheory.SimpleDensity
