-- Prove2me | solution 1 for GlobalTheory.Mem.ImagQuad.exists_field_sq_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:55:46.086235+00:00
-- url     : https://prove2.me/submissions/226ab1b9-db3d-4e39-8c50-39dc262bcf27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RingOfIntegersSqrtNegThreeModFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsImagQuadIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.ImagQuad
open QuadraticZeta
namespace GlobalTheory.Mem.ImagQuad
theorem _root_.solution (d : ℕ) (hd : 0 < d) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (r : K),
      finrank ℚ K = 2 ∧ r ^ 2 = -(d : K) := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  set p : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.C (d : ℚ) with hp
  have hpdeg : p.natDegree = 2 := by
    rw [hp]; compute_degree!
  have hpmon : p.Monic := by
    rw [hp]; monicity!
  have hroot : ∀ x : ℚ, ¬ p.IsRoot x := by
    intro x hx
    simp only [hp, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hx
    nlinarith [sq_nonneg x]
  have hirr : Irreducible p :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hpdeg]; decide) hroot
  have : Fact (Irreducible p) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  have : FiniteDimensional ℚ (AdjoinRoot p) := pb.finite
  have : NumberField (AdjoinRoot p) := ⟨⟩
  refine ⟨AdjoinRoot p, inferInstance, inferInstance, AdjoinRoot.root p, ?_, ?_⟩
  · rw [pb.finrank, AdjoinRoot.powerBasis_dim, hpdeg]
  · have h := AdjoinRoot.eval₂_root p
    simp only [hp, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at h
    rw [eq_neg_iff_add_eq_zero, ← h]
    simp
end GlobalTheory.Mem.ImagQuad
