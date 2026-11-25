-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.exists_countable_conj_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:28.868617+00:00
-- url     : https://prove2.me/submissions/ab324ad1-8d1f-4301-9326-d5f0256c8291

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_associated_monicAssoc
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_exists_cyclic_decomposition
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_exists_conj_of_equiv
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_finite_monic_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Polynomial
universe u
variable {F : Type u} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution (f : F[X]) :
    ∃ s : Set (GL (Fin n) F), s.Countable ∧ ∀ x : GL (Fin n) F,
      (x : Matrix (Fin n) (Fin n) F).charpoly = f → ∃ y ∈ s, ∃ g : GL (Fin n) F,
        x = g * y * g⁻¹ := by
  classical
  by_cases hf : f = 0
  · refine ⟨∅, Set.countable_empty, fun x hx => ?_⟩
    exact absurd (hx.trans hf) (Matrix.charpoly_monic _).ne_zero
  let D := {g : F[X] // g.Monic ∧ g ∣ f}
  have : Finite D := (finite_monic_dvd hf).to_subtype
  let N : (Σ k : ℕ, Fin k → D) → Type u := fun t =>
    DirectSum (Fin t.1) fun j => F[X] ⧸ F[X] ∙ (t.2 j).1
  let R : (Σ k : ℕ, Fin k → D) → Prop := fun t => ∃ y : GL (Fin n) F,
    Nonempty (Module.AEval' (Matrix.toLin' (y : Matrix (Fin n) (Fin n) F)) ≃ₗ[F[X]] N t)
  let rep : (Σ k : ℕ, Fin k → D) → GL (Fin n) F := fun t => if h : R t then h.choose else 1
  refine ⟨Set.range rep, Set.countable_range rep, fun x hx => ?_⟩
  obtain ⟨ι, hι, q, hq0, hqd, ⟨e⟩⟩ := exists_cyclic_decomposition (x : Matrix (Fin n) (Fin n) F)
  let σ := Fintype.equivFin ι
  let t : Σ k : ℕ, Fin k → D := ⟨Fintype.card ι, fun j =>
    ⟨monicAssoc (q (σ.symm j)), monicAssoc_monic (hq0 _), (monicAssoc_dvd _).trans (hx ▸ hqd _)⟩⟩
  have hspan : ∀ j : Fin (Fintype.card ι),
      (F[X] ∙ q (σ.symm j)) = (F[X] ∙ (t.2 j).1) := fun j =>
    Ideal.span_singleton_eq_span_singleton.2 (associated_monicAssoc (hq0 _))
  let e' : Module.AEval' (Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)) ≃ₗ[F[X]] N t :=
    e.trans ((DirectSum.lequivCongrLeft F[X] σ).trans
      (DFinsupp.mapRange.linearEquiv fun j => Submodule.quotEquivOfEq _ _ (hspan j)))
  have hR : R t := ⟨x, ⟨e'⟩⟩
  obtain ⟨e''⟩ := hR.choose_spec
  refine ⟨rep t, ⟨t, rfl⟩, ?_⟩
  have hrep : rep t = hR.choose := dif_pos hR
  rw [hrep]
  exact exists_conj_of_equiv (e'.trans e''.symm)
end GroundTheory.Automorphic.ContragredientTranspose
