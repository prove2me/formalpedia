-- Prove2me | solution 1 for NumberField.Units.exists_minkowskiUnit
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:53:46.924814+00:00
-- url     : https://prove2.me/submissions/62e2f277-6139-4c80-b401-99ff67acf405

import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.LinearAlgebra.Matrix.Gershgorin

open NumberField

namespace MINK

open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem

variable {K : Type*} [Field K] [NumberField K]

/-- The Galois conjugate `σ ε` of a unit `ε`. -/
noncomputable def conj (σ : K ≃ₐ[ℚ] K) (ε : (𝓞 K)ˣ) : (𝓞 K)ˣ :=
  Units.map (RingOfIntegers.mapRingEquiv σ.toRingEquiv).toMonoidHom ε

lemma place_conj (σ : K ≃ₐ[ℚ] K) (ε : (𝓞 K)ˣ) (w : InfinitePlace K) :
    w (algebraMap (𝓞 K) K (conj σ ε)) = (σ.symm • w) (algebraMap (𝓞 K) K ε) := by
  rw [InfinitePlace.smul_apply]; simp [conj]

lemma log_conj_neg {ε : (𝓞 K)ˣ} (hε : ∀ w : InfinitePlace K, w ≠ w₀ → Real.log (w ε) < 0)
    (σ : K ≃ₐ[ℚ] K) (j : InfinitePlace K) (hj : j ≠ σ • w₀) :
    Real.log (j (conj σ ε)) < 0 := by
  have := place_conj σ ε j
  rw [this]
  apply hε
  intro h
  apply hj
  rw [← h, ← AlgEquiv.aut_inv, smul_inv_smul]

end MINK

open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem in
theorem solution (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K] :
    ∃ ε : (𝓞 K)ˣ, (Subgroup.closure (Set.range fun σ : K ≃ₐ[ℚ] K =>
      Units.map (RingOfIntegers.mapRingEquiv σ.toRingEquiv).toMonoidHom ε)).FiniteIndex := by
  classical
  obtain ⟨ε, hε⟩ := exists_unit K (w₀ : InfinitePlace K)
  refine ⟨ε, ?_⟩
  have htrans : ∀ w : InfinitePlace K, ∃ σ : K ≃ₐ[ℚ] K, σ • (w₀ : InfinitePlace K) = w :=
    fun w => exists_smul_eq_of_comap_eq (Subsingleton.elim _ _)
  choose σ hσ using htrans
  let u : Fin (rank K) → (𝓞 K)ˣ := fun i => MINK.conj (σ (equivFinRank K i)) ε
  have hmax : IsMaxRank u := by
    rw [← regOfFamily_ne_zero_iff, regOfFamily_eq_det', abs_ne_zero]
    apply det_ne_zero_of_sum_row_lt_diag
    intro k
    simp only [Matrix.of_apply, u, Equiv.apply_symm_apply, logEmbedding_component]
    set a := fun j : {w : InfinitePlace K // w ≠ w₀} =>
      (mult j.val : ℝ) * Real.log (j.val (MINK.conj (σ k.val) ε : K)) with ha
    have hoff : ∀ j ∈ Finset.univ.erase k, ‖a j‖ = - a j := fun j hj => by
      rw [Real.norm_eq_abs, abs_of_neg]
      refine mul_neg_of_pos_of_neg (Nat.cast_pos.mpr mult_pos) ?_
      refine MINK.log_conj_neg hε _ _ ?_
      rw [hσ]
      exact fun h => (Finset.ne_of_mem_erase hj) (Subtype.ext h)
    have hsum := sum_logEmbedding_component (MINK.conj (σ k.val) ε)
    simp only [logEmbedding_component] at hsum
    change ∑ j, a j = _ at hsum
    have hpos : 0 < -(mult (w₀ : InfinitePlace K) : ℝ) *
        Real.log (w₀ (MINK.conj (σ k.val) ε : K)) := by
      refine mul_pos_of_neg_of_neg (neg_neg_of_pos (Nat.cast_pos.mpr mult_pos)) ?_
      refine MINK.log_conj_neg hε _ _ ?_
      rw [hσ]
      exact fun h => k.prop h.symm
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hsum
    change ∑ j ∈ Finset.univ.erase k, ‖a j‖ < ‖a k‖
    rw [Finset.sum_congr rfl hoff, Finset.sum_neg_distrib]
    have := le_abs_self (a k)
    rw [← Real.norm_eq_abs] at this
    linarith
  have hfin := isMaxRank_iff_closure_finiteIndex.mp hmax
  refine Subgroup.finiteIndex_of_le (H := Subgroup.closure (Set.range u)) ?_
  exact Subgroup.closure_mono (by rintro _ ⟨i, rfl⟩; exact ⟨σ _, rfl⟩)
