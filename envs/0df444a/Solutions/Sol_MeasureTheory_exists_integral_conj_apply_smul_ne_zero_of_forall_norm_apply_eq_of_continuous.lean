-- Prove2me | solution 1 for MeasureTheory.exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/59cb53f1-0a80-586a-bbcb-da4a154f2df3

import Mathlib
import Theorems.Thm_ContinuousMap_ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate Kronecker InnerProductSpace

namespace PWProof

section Reps

variable {K : Type*} [Group K] [TopologicalSpace K]

noncomputable def kronRep {n m : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (ρ' : K →* Matrix (Fin m) (Fin m) ℂ) :
    K →* Matrix (Fin (n * m)) (Fin (n * m)) ℂ where
  toFun k := Matrix.reindex finProdFinEquiv finProdFinEquiv (ρ k ⊗ₖ ρ' k)
  map_one' := by
    rw [map_one, map_one, Matrix.one_kronecker_one, Matrix.reindex_apply]
    exact Matrix.submatrix_one_equiv _
  map_mul' a b := by
    rw [map_mul, map_mul, Matrix.mul_kronecker_mul, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply]
    exact (Matrix.submatrix_mul_equiv _ _ _ _ _).symm

omit [TopologicalSpace K] in
theorem kronRep_apply {n m : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (ρ' : K →* Matrix (Fin m) (Fin m) ℂ)
    (k : K) (i j : Fin n) (i' j' : Fin m) :
    kronRep ρ ρ' k (finProdFinEquiv (i, i')) (finProdFinEquiv (j, j')) = ρ k i j * ρ' k i' j' := by
  simp [kronRep, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]

theorem continuous_kronRep {n m : ℕ} {ρ : K →* Matrix (Fin n) (Fin n) ℂ} {ρ' : K →* Matrix (Fin m) (Fin m) ℂ}
    (hρ : Continuous ρ) (hρ' : Continuous ρ') : Continuous (kronRep ρ ρ') := by
  refine continuous_matrix fun a b => ?_
  show Continuous fun k => (ρ k ⊗ₖ ρ' k) (finProdFinEquiv.symm a) (finProdFinEquiv.symm b)
  simp only [Matrix.kroneckerMap_apply]
  exact (hρ.matrix_elem _ _).mul (hρ'.matrix_elem _ _)

noncomputable def conjRep {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) : K →* Matrix (Fin n) (Fin n) ℂ :=
  (RingHom.mapMatrix (starRingEnd ℂ)).toMonoidHom.comp ρ

omit [TopologicalSpace K] in
theorem conjRep_apply {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (k : K) (i j : Fin n) :
    conjRep ρ k i j = conj (ρ k i j) := rfl

theorem continuous_conjRep {n : ℕ} {ρ : K →* Matrix (Fin n) (Fin n) ℂ} (hρ : Continuous ρ) :
    Continuous (conjRep ρ) := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun k => conj (ρ k i j)
  exact (hρ.matrix_elem i j).star

omit [TopologicalSpace K] in

theorem apply_inv_mul_eq_one_of_apply_eq {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) {k k' : K}
    (h : ρ k = ρ k') : ρ (k'⁻¹ * k) = 1 := by
  rw [map_mul, h, ← map_mul, inv_mul_cancel, map_one]

end Reps

section Algebra

variable (K : Type*) [Group K] [TopologicalSpace K]

def coeffSet : Set C(K, ℂ) :=
  {f | ∃ (n : ℕ) (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (i j : Fin n), Continuous ρ ∧ ∀ k, f k = ρ k i j}

variable {K}

noncomputable def coeffFn {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) (i j : Fin n) : C(K, ℂ) :=
  ⟨fun k => ρ k i j, hρ.matrix_elem i j⟩

theorem coeffFn_mem {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) (i j : Fin n) :
    coeffFn ρ hρ i j ∈ coeffSet K :=
  ⟨n, ρ, i, j, hρ, fun _ => rfl⟩

theorem one_mem_coeffSet : (1 : C(K, ℂ)) ∈ coeffSet K :=
  ⟨1, 1, 0, 0, continuous_const, fun k => by simp⟩

theorem mul_mem_coeffSet {f g : C(K, ℂ)} (hf : f ∈ coeffSet K) (hg : g ∈ coeffSet K) : f * g ∈ coeffSet K := by
  obtain ⟨n, ρ, i, j, hρ, hfρ⟩ := hf
  obtain ⟨m, ρ', i', j', hρ', hgρ⟩ := hg
  refine ⟨n * m, kronRep ρ ρ', finProdFinEquiv (i, i'), finProdFinEquiv (j, j'), continuous_kronRep hρ hρ', fun k => ?_⟩
  rw [ContinuousMap.mul_apply, hfρ, hgρ, kronRep_apply]

theorem star_mem_coeffSet {f : C(K, ℂ)} (hf : f ∈ coeffSet K) : star f ∈ coeffSet K := by
  obtain ⟨n, ρ, i, j, hρ, hfρ⟩ := hf
  refine ⟨n, conjRep ρ, i, j, continuous_conjRep hρ, fun k => ?_⟩
  rw [ContinuousMap.star_apply, hfρ, conjRep_apply]
  rfl

variable (K)

noncomputable def coeffStarSubalgebra : StarSubalgebra ℂ C(K, ℂ) where
  carrier := Submodule.span ℂ (coeffSet K)
  mul_mem' {a b} ha hb := by
    have hab : a * b ∈ Submodule.span ℂ (coeffSet K) * Submodule.span ℂ (coeffSet K) := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at hab
    refine Submodule.span_le.mpr ?_ hab
    rintro _ ⟨f, hf, g, hg, rfl⟩
    exact Submodule.subset_span (mul_mem_coeffSet hf hg)
  one_mem' := Submodule.subset_span one_mem_coeffSet
  add_mem' ha hb := Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c (Submodule.subset_span one_mem_coeffSet)
  star_mem' {a} ha := by
    show star a ∈ Submodule.span ℂ (coeffSet K)
    refine Submodule.span_induction (p := fun a _ => star a ∈ Submodule.span ℂ (coeffSet K)) ?_ ?_ ?_ ?_ ha
    · exact fun f hf => Submodule.subset_span (star_mem_coeffSet hf)
    · show star (0 : C(K, ℂ)) ∈ Submodule.span ℂ (coeffSet K)
      rw [star_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      show star (x + y) ∈ Submodule.span ℂ (coeffSet K)
      rw [star_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      show star (c • x) ∈ Submodule.span ℂ (coeffSet K)
      rw [star_smul]; exact Submodule.smul_mem _ _ hx

theorem mem_coeffStarSubalgebra_iff (f : C(K, ℂ)) :
    f ∈ coeffStarSubalgebra K ↔ f ∈ Submodule.span ℂ (coeffSet K) := Iff.rfl

variable {K}

theorem coeffStarSubalgebra_separatesPoints
    (hsep : ∀ k : K, k ≠ 1 → ∃ (n : ℕ) (ρ : K →* Matrix (Fin n) (Fin n) ℂ), Continuous ρ ∧ ρ k ≠ 1) :
    (coeffStarSubalgebra K).SeparatesPoints := by
  intro x y hxy
  have hne : y⁻¹ * x ≠ 1 := fun h => hxy (by rw [inv_mul_eq_one] at h; exact h.symm)
  obtain ⟨n, ρ, hρ, h1⟩ := hsep _ hne
  have hρxy : ρ x ≠ ρ y := fun h => h1 (apply_inv_mul_eq_one_of_apply_eq ρ h)
  obtain ⟨i, j, hij⟩ : ∃ i j, ρ x i j ≠ ρ y i j := by
    by_contra hc
    push Not at hc
    exact hρxy (Matrix.ext fun i j => hc i j)
  exact ⟨coeffFn ρ hρ i j, ⟨coeffFn ρ hρ i j, Submodule.subset_span (coeffFn_mem ρ hρ i j), rfl⟩, hij⟩

end Algebra

end PWProof

open PWProof in
theorem solution
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : K →* (H →L[ℂ] H))
    (hπn : ∀ (k : K) (v : H), ‖π k v‖ = ‖v‖)
    (hπc : ∀ v : H, Continuous fun k : K => π k v)
    (hsep : ∀ k : K, k ≠ 1 →
      ∃ (n : ℕ) (ρ : K →* Matrix (Fin n) (Fin n) ℂ), Continuous ρ ∧ ρ k ≠ 1)
    (v : H) (hv : v ≠ 0) :
    ∃ (n : ℕ) (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (i j : Fin n), Continuous ρ ∧
      ∫ k, (conj ((ρ k) i j)) • (π k v) ∂μ ≠ 0 := by
  classical
  by_contra hall
  push Not at hall

  haveI : μ.IsOpenPosMeasure := inferInstance

  set β : C(K, ℂ) := ⟨fun k => ⟪π k v, v⟫_ℂ, (hπc v).inner continuous_const⟩ with hβ

  have hcoeff : ∀ f ∈ coeffSet K, ∫ k, f k * β k ∂μ = 0 := by
    rintro f ⟨n, ρ, i, j, hρ, hfρ⟩
    have hint : Integrable (fun k => (conj (ρ k i j)) • π k v) μ := by
      refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · exact ((hρ.matrix_elem i j).star).smul (hπc v)
      · exact IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _)
    have h0 := hall n ρ i j hρ
    calc ∫ k, f k * β k ∂μ = ∫ k, conj ⟪v, (conj (ρ k i j)) • π k v⟫_ℂ ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          show f k * ⟪π k v, v⟫_ℂ = conj ⟪v, (conj (ρ k i j)) • π k v⟫_ℂ
          rw [inner_smul_right, map_mul, Complex.conj_conj, inner_conj_symm, hfρ]
      _ = conj (∫ k, ⟪v, (conj (ρ k i j)) • π k v⟫_ℂ ∂μ) := integral_conj
      _ = conj ⟪v, ∫ k, (conj (ρ k i j)) • π k v ∂μ⟫_ℂ := by rw [integral_inner hint v]
      _ = 0 := by rw [h0, inner_zero_right, map_zero]

  have halg : ∀ f ∈ coeffStarSubalgebra K, ∫ k, f k * β k ∂μ = 0 := by
    intro f hf
    rw [mem_coeffStarSubalgebra_iff] at hf
    have hint : ∀ g : C(K, ℂ), Integrable (fun k => g k * β k) μ := fun g =>
      Continuous.integrable_of_hasCompactSupport (g.continuous.mul β.continuous)
        (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
    refine Submodule.span_induction (p := fun f _ => ∫ k, f k * β k ∂μ = 0) hcoeff ?_ ?_ ?_ hf
    · simp
    · intro x y _ _ hx hy
      simp only [ContinuousMap.add_apply, add_mul]
      rw [integral_add (hint x) (hint y), hx, hy, add_zero]
    · intro c x _ hx
      simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, hx, mul_zero]

  have hae := ContinuousMap.ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero μ
    (coeffStarSubalgebra K) (coeffStarSubalgebra_separatesPoints hsep) β halg
  have hβ0 : (β : K → ℂ) = 0 := (Continuous.ae_eq_iff_eq μ β.continuous continuous_const).mp hae
  have h1 : ⟪v, v⟫_ℂ = 0 := by
    have := congrFun hβ0 1
    simpa [hβ, map_one] using this
  exact hv (inner_self_eq_zero.mp h1)

end S_MeasureTheory_exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous
end P2MW
export P2MW.S_MeasureTheory_exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous (solution)
