-- Prove2me | solution 1 for GlobalTheory.SmoothForms.GelfGen.trace_symb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:41:29.931086+00:00
-- url     : https://prove2.me/submissions/2a228bcc-6f58-4175-9664-dd4db9889a62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GelfAMemAdjoinLow
import Theorems.Thm_GlobalTheory_SmoothForms_GelfGen_exists_eig
import Theorems.Thm_GlobalTheory_SmoothForms_GelfGen_newton_closure
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_sum_mem_symb
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_symb_mul
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_trace_pow_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms
noncomputable section
open GlobalTheory.SmoothForms.PermWord
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.GelfGen
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace GlobalTheory.SmoothForms.GelfGen
theorem _root_.solution (E : Fin n → Fin n → A) (k : ℕ) :
    ∃ c ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val),
      (((Matrix.of (gen n)) ^ (k + 1)).trace, c) ∈ symb E (k + 1) := by
  set C := Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val)
  let R := MvPolynomial (Fin n × Fin n) ℂ
  let K := AlgebraicClosure (FractionRing R)
  have hinj : Function.Injective (algebraMap R K) := by
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) K]
    exact (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective _ _)
  obtain ⟨l, hl⟩ := exists_eig ((Matrix.of (gen n)).map (algebraMap R K))
  have htr : ∀ j, algebraMap R K ((Matrix.of (gen n)) ^ j).trace = ∑ i, l i ^ j := by
    intro j
    rw [← hl, ← Matrix.map_pow]
    simp [Matrix.trace, map_sum]
  let P : ℕ → K → Prop := fun j p => ∃ q : R, ∃ c ∈ C, algebraMap R K q = p ∧ (q, c) ∈ symb E j
  have key := newton_closure l P
    ⟨1, 1, one_mem _, map_one _, Submodule.subset_span ⟨[], rfl, by simp [wd]⟩⟩
    (fun j => ⟨0, 0, zero_mem _, map_zero _, zero_mem _⟩)
    (by
      rintro j _ _ ⟨q, c, hc, rfl, h⟩ ⟨q', c', hc', rfl, h'⟩
      exact ⟨q + q', c + c', add_mem hc hc', map_add _ _ _, by simpa using add_mem h h'⟩)
    (by
      rintro j a _ ⟨q, c, hc, rfl, h⟩
      refine ⟨a • q, a • c, Subalgebra.smul_mem _ hc a, ?_, by simpa using Submodule.smul_mem _ a h⟩
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def])
    (by
      rintro i j _ _ ⟨q, c, hc, rfl, h⟩ ⟨q', c', hc', rfl, h'⟩
      exact ⟨q * q', c * c', mul_mem hc hc', map_mul _ _ _, by simpa using symb_mul E h h'⟩)
    (by
      intro j hj1 hjn
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      refine ⟨_, gelfA E k, Algebra.subset_adjoin ⟨⟨k, by omega⟩, rfl⟩, htr _, ?_⟩
      rw [trace_pow_eq]
      unfold gelfA
      exact sum_mem_symb E (fun idx : Fin (k + 1) → Fin n => idx) fun idx a => idx (a + 1))
    (k + 1) (by omega)
  obtain ⟨q, c, hc, hq, h⟩ := key
  rw [← htr] at hq
  rw [hinj hq] at h
  exact ⟨c, hc, h⟩
end GlobalTheory.SmoothForms.GelfGen
