-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:03:15.168875+00:00
-- url     : https://prove2.me/submissions/781ebe1e-9818-4b48-bf35-e13aa225c3ee

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraFunctionCalculus
import Theorems.Thm_GlobalTheory_CompanionTheory_AdProj_entryMul_poly_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdProj
namespace GlobalTheory.CompanionTheory.AdProj
theorem _root_.solution {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ) :
    Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤 → (∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤) →
      ∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤 := by
  intro hD hbr f X hX
  obtain ⟨S, hS⟩ : ∃ S : Finset ℝ, ∀ i j, h i - h j ∈ S :=
    ⟨Finset.univ.image (fun q : Fin n × Fin n => h q.1 - h q.2),
      fun i j => Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩⟩
  have key : ∀ x ∈ S, (Lagrange.interpolate S id f).eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (s := S) (r := f) Function.injective_id.injOn hx
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℝ, ∀ i j, p.eval (h i - h j) = f (h i - h j) :=
    ⟨Lagrange.interpolate S id f, fun i j => key _ (hS i j)⟩
  have heq : (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) = entryMul h (fun t => p.eval t) X := by
    ext i j
    simp only [entryMul, Matrix.of_apply, hp]
  rw [heq]
  exact entryMul_poly_mem 𝔤 h hD hbr hX p
end GlobalTheory.CompanionTheory.AdProj
