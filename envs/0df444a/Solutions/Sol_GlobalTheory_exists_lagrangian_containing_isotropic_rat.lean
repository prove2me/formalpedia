-- Prove2me | solution 1 for GlobalTheory.exists_lagrangian_containing_isotropic_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:44:41.632893+00:00
-- url     : https://prove2.me/submissions/a5819b66-701f-4ca0-97f7-197f1bbd6c5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLagrangianContainingIsotropicRat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open Module
namespace GlobalTheory
theorem _root_.solution : ∀ (g r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (I : Submodule ℚ (Fin r → ℚ)), r = 2 * g → Mqᵀ = -Mq → Mq.det ≠ 0 → (∀ x ∈ I, ∀ y ∈ I, x ⬝ᵥ Mq *ᵥ y = 0) → ∃ L : Submodule ℚ (Fin r → ℚ), I ≤ L ∧ (∀ x ∈ L, ∀ y ∈ L, x ⬝ᵥ Mq *ᵥ y = 0) ∧ Module.finrank ℚ L = g := by
  classical
  intro g r M I hr hskew hdet hI
  set B : LinearMap.BilinForm ℚ (Fin r → ℚ) := Matrix.toBilin' M with hBdef
  have hB : ∀ v w, B v w = v ⬝ᵥ M *ᵥ w := fun v w => by
    simp [hBdef, Matrix.toBilin'_apply']
  have hskewB : ∀ v w, B v w = - B w v := by
    intro v w
    rw [hB, hB, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hskew, Matrix.neg_mulVec,
      neg_dotProduct, dotProduct_comm]
  have hBalt : ∀ v, B v v = 0 := fun v => by have := hskewB v v; linarith
  have hnd : B.Nondegenerate := LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' M hdet
  have hIB : ∀ x ∈ I, ∀ y ∈ I, B x y = 0 := fun x hx y hy => by rw [hB]; exact hI x hx y hy
  let P : ℕ → Prop := fun n => ∃ L : Submodule ℚ (Fin r → ℚ), I ≤ L ∧
    (∀ x ∈ L, ∀ y ∈ L, B x y = 0) ∧ finrank ℚ L = n
  have PI : P (finrank ℚ I) := ⟨I, le_rfl, hIB, rfl⟩
  have hIr : finrank ℚ I ≤ r := by simpa using Submodule.finrank_le I
  obtain ⟨L, hIL, hLiso, hLdim⟩ : P (Nat.findGreatest P r) := Nat.findGreatest_spec hIr PI
  have hmax : ∀ v, (∀ l ∈ L, B v l = 0) → v ∈ L := by
    intro v hvL
    by_contra hv
    have hlt : L < L ⊔ Submodule.span ℚ {v} := lt_of_le_of_ne le_sup_left (fun h => hv (by
      rw [h]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))
    have hiso : ∀ x ∈ L ⊔ Submodule.span ℚ {v}, ∀ y ∈ L ⊔ Submodule.span ℚ {v}, B x y = 0 := by
      intro x hx y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
      obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hb'
      have h1 := hLiso a ha a' ha'
      have h2 := hvL a' ha'
      have h3 : B a v = 0 := by rw [hskewB, hvL a ha, neg_zero]
      have h4 := hBalt v
      simp [map_add, map_smul, h1, h2, h3, h4]
    have hP : P (finrank ℚ ↥(L ⊔ Submodule.span ℚ {v})) :=
      ⟨_, hIL.trans le_sup_left, hiso, rfl⟩
    have h5 := Nat.le_findGreatest (by simpa using Submodule.finrank_le (L ⊔ Submodule.span ℚ {v})) hP
    have h6 := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hLo : B.orthogonal L = L := by
    apply le_antisymm
    · intro x hx
      exact hmax x (fun l hl => by rw [hskewB, hx l hl, neg_zero])
    · intro x hx l hl
      exact hLiso l hl x hx
  have hdim := LinearMap.BilinForm.finrank_orthogonal hnd L
  rw [hLo] at hdim
  have hV : finrank ℚ (Fin r → ℚ) = r := by simp
  rw [hV] at hdim
  have hLr : finrank ℚ L ≤ r := by simpa using Submodule.finrank_le L
  refine ⟨L, hIL, fun x hx y hy => by rw [← hB]; exact hLiso x hx y hy, ?_⟩
  omega
end GlobalTheory
