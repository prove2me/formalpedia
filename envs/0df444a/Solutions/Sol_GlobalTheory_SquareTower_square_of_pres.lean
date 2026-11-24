-- Prove2me | solution 1 for GlobalTheory.SquareTower.square_of_pres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:57:12.082804+00:00
-- url     : https://prove2.me/submissions/682f1e05-d770-44f0-a392-45b1e355ed89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquarePresentationOfTower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.SquareTower
open MvPolynomial
namespace GlobalTheory.SquareTower
theorem _root_.solution {R T ι σ : Type} [CommRing R] [CommRing T] [Algebra R T] {n : ℕ}
    (P : Algebra.Presentation R T ι σ) (e : Fin n ≃ ι) (f : Fin n ≃ σ) :
    ∃ (s : ℕ) (φ : MvPolynomial (Fin s) R →ₐ[R] T) (g : Fin s → MvPolynomial (Fin s) R),
      Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g) := by
  let E : MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial ι R := renameEquiv R e
  refine ⟨n, (aeval P.val).comp E.toAlgHom, fun i => E.symm (P.relation (f i)), ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := P.toGenerators.algebraMap_surjective y
    refine ⟨E.symm x, ?_⟩
    show aeval P.val (E (E.symm x)) = y
    rw [E.apply_symm_apply, ← hx, Algebra.Generators.algebraMap_eq]
    rfl
  · have h1 : Set.range (fun i => E.symm (P.relation (f i))) = E.symm '' Set.range P.relation := by
      rw [← Set.range_comp]
      exact f.surjective.range_comp (⇑E.symm ∘ P.relation)
    rw [h1, ← Ideal.map_span, P.span_range_relation_eq_ker, Algebra.Generators.ker_eq_ker_aeval_val]
    ext x
    rw [RingHom.mem_ker, Ideal.mem_map_of_equiv]
    constructor
    · intro hx
      refine ⟨E x, ?_, by simp⟩
      rw [RingHom.mem_ker]; simpa using hx
    · rintro ⟨y, hy, rfl⟩
      rw [RingHom.mem_ker] at hy
      simpa using hy
end GlobalTheory.SquareTower
