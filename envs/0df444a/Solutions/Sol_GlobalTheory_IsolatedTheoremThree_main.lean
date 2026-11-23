-- Prove2me | solution 1 for GlobalTheory.IsolatedTheoremThree.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:28.983179+00:00
-- url     : https://prove2.me/submissions/ea611cfd-6546-4508-823a-8b7c7ed63643

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ImportsMore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IsolatedTheoremThree
namespace GlobalTheory.IsolatedTheoremThree
theorem _root_.solution : (let d1 : (R : Type) → {A : Type} → [inst : CommRing R] → [inst_1 : CommRing A] → [inst_2 : Algebra R A] → (ℕ → A) → ℕ → Submodule R A := @(fun (R : Type) {A : Type} [CommRing R] [CommRing A] [Algebra R A] (γ : ℕ → A) (N : ℕ) ↦ Submodule.span R (γ '' {m : ℕ | m < N})); ∀ {R A : Type} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A], (∀ (n : ℕ), IsUnit (↑(Nat.factorial n) : A)) → ∀ (ξ : R) (γ : ℕ → A), (∀ (n : ℕ), (↑(Nat.factorial n) : A) * γ n = (Algebra.algebraMap R A : R → A) ξ ^ n) → ∀ (N : ℕ), ∀ w ∈ Submodule.span R (Set.range γ), ∃ w₁ ∈ d1 R γ N, (Algebra.algebraMap R A : R → A) ξ ^ N ∣ w - w₁) := by
  intro d1 R A _ _ _ hfac ξ γ hγ N w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, rfl⟩ := hw
    by_cases hn : n < N
    · exact ⟨γ n, Submodule.subset_span ⟨n, hn, rfl⟩, by simp⟩
    · refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [sub_zero]
      obtain ⟨u, hu⟩ := hfac n
      have hg : γ n = ↑u⁻¹ * algebraMap R A ξ ^ n := by
        rw [← hγ n, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
      have hp : algebraMap R A ξ ^ n = algebraMap R A ξ ^ N * algebraMap R A ξ ^ (n - N) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hg, hp]
      exact Dvd.intro (↑u⁻¹ * algebraMap R A ξ ^ (n - N)) (by ring)
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hda⟩ := hx
    obtain ⟨b, hb, hdb⟩ := hy
    refine ⟨a + b, Submodule.add_mem _ ha hb, ?_⟩
    rw [show x + y - (a + b) = (x - a) + (y - b) by ring]
    exact dvd_add hda hdb
  | smul r x _ hx =>
    obtain ⟨a, ha, hda⟩ := hx
    refine ⟨r • a, Submodule.smul_mem _ r ha, ?_⟩
    rw [← smul_sub, Algebra.smul_def]
    exact Dvd.dvd.mul_left hda _
end GlobalTheory.IsolatedTheoremThree
