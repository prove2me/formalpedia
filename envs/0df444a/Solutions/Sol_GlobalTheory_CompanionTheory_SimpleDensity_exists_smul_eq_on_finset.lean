-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SimpleDensity.exists_smul_eq_on_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:38:50.712796+00:00
-- url     : https://prove2.me/submissions/f3f5d528-b84d-4827-9a18-755365e22371

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmulEqOnFinset

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
theorem _root_.solution {R ι : Type} [Ring R] [Fintype ι] (M : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, IsSimpleModule R (M i)]
    (hne : ∀ i j, i ≠ j → ∀ φ : M i →ₗ[R] M j, φ = 0)
    (f : ∀ i, M i →+ M i)
    (hf : ∀ i (φ : M i →ₗ[R] M i) x, f i (φ x) = φ (f i x))
    (s : Finset (∀ i, M i)) :
    ∃ r : R, ∀ m ∈ s, ∀ i, f i (m i) = r • m i := by
  classical
  have key : ∀ (φ : Module.End R (∀ i, M i)) (m : ∀ i, M i) (i : ι),
      φ m i = ((LinearMap.proj i) ∘ₗ φ ∘ₗ LinearMap.single R M i) (m i) := by
    intro φ m i
    have hm : m = ∑ j, Pi.single j (m j) := (Finset.univ_sum_single m).symm
    conv_lhs => rw [hm]
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i]
    · rfl
    · intro j _ hj
      have := hne j i hj ((LinearMap.proj i) ∘ₗ φ ∘ₗ LinearMap.single R M j)
      exact LinearMap.congr_fun this (m j)
    · simp
  let F : Module.End (Module.End R (∀ i, M i)) (∀ i, M i) :=
    { toFun := fun m i => f i (m i)
      map_add' := fun a b => by ext i; simp
      map_smul' := fun φ m => by
        ext i
        simp only [Module.End.smul_def, RingHom.id_apply]
        rw [key φ m i, key φ _ i, hf] }
  obtain ⟨r, hr⟩ := jacobson_density F s
  exact ⟨r, fun m hm i => congrFun (hr m hm) i⟩
end GlobalTheory.CompanionTheory.SimpleDensity
