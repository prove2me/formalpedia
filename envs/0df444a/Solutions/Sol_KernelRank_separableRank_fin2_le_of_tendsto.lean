-- Prove2me | solution 1 for KernelRank.separableRank_fin2_le_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:41:41.841933+00:00
-- url     : https://prove2.me/submissions/0f49f3a5-c6fc-4809-963f-d78bc974aec6

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
import Theorems.Thm_KernelRank_IsSumOfProducts_comp
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_eta
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same


section
open Complex Polynomial
open scoped Topology
namespace KernelRank
section LowerSemicontinuity
private lemma det_mul_eq_zero_of_lt {𝕜 : Type*} [Field 𝕜] {r : ℕ}
    (U : Matrix (Fin (r + 1)) (Fin r) 𝕜) (V : Matrix (Fin r) (Fin (r + 1)) 𝕜) :
    (U * V).det = 0 := by
  by_contra hne
  have hunit : IsUnit (U * V) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne)
  obtain ⟨M, hM⟩ := hunit.exists_left_inv
  have hinj : Function.Injective (Matrix.mulVecLin V) := by
    intro v₁ v₂ hv
    have hv' : V.mulVec v₁ = V.mulVec v₂ := hv
    have h1 : (M * (U * V)).mulVec v₁ = (M * (U * V)).mulVec v₂ := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, hv']
    simpa [hM] using h1
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_fin_fun] at hle
  omega
private lemma isSumOfProducts_mono {𝕜 : Type*} [CommSemiring 𝕜] {ι : Type*} [Fintype ι]
    {X : ι → Type*} [Nonempty ι] {K : (∀ i, X i) → 𝕜} {m n : ℕ} (hmn : m ≤ n)
    (hK : IsSumOfProducts K m) : IsSumOfProducts K n := by
  obtain ⟨f, hf⟩ := hK
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨fun k i x => if h : (k : ℕ) < m then f ⟨k, h⟩ i x else 0, fun x => ?_⟩
  have h1 : (∑ k : Fin n, ∏ i : ι,
      (if h : (k : ℕ) < m then f ⟨k, h⟩ i (x i) else (0 : 𝕜))) =
      ∑ k ∈ Finset.range n, ∏ i : ι, (if h : k < m then f ⟨k, h⟩ i (x i) else 0) :=
    Fin.sum_univ_eq_sum_range
      (fun k => ∏ i : ι, if h : k < m then f ⟨k, h⟩ i (x i) else (0 : 𝕜)) n
  have h2 : (∑ k ∈ Finset.range m, ∏ i : ι,
      (if h : k < m then f ⟨k, h⟩ i (x i) else (0 : 𝕜))) =
      ∑ k ∈ Finset.range n, ∏ i : ι, (if h : k < m then f ⟨k, h⟩ i (x i) else 0) := by
    refine Finset.sum_subset (Finset.range_mono hmn) fun k _ hk => ?_
    have hnot : ¬ k < m := by simpa using hk
    simp only [hnot, ↓reduceDIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i₀) rfl
  have h3 : (∑ k : Fin m, ∏ i : ι, f k i (x i)) =
      ∑ k ∈ Finset.range m, ∏ i : ι, (if h : k < m then f ⟨k, h⟩ i (x i) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => ∏ i : ι, if h : k < m then f ⟨k, h⟩ i (x i) else (0 : 𝕜)) m]
    refine Finset.sum_congr rfl fun k _ => Finset.prod_congr rfl fun i _ => ?_
    simp [k.isLt]
  rw [hf, h3, h2, ← h1]
private lemma exists_submatrix_det_ne_zero_of_not_isSumOfProducts {𝕜 α : Type*} [Field 𝕜]
    {K : (Fin 2 → α) → 𝕜} {r : ℕ} (hnot : ¬ IsSumOfProducts K r) :
    ∀ k ≤ r + 1, ∃ (x y : Fin k → α),
      (Matrix.of fun p q => K (fin2Vec (x q) (y p))).det ≠ 0
  | 0, _ => ⟨Fin.elim0, Fin.elim0, by simp⟩
  | k + 1, hk => by
    obtain ⟨x, y, hdet⟩ :=
      exists_submatrix_det_ne_zero_of_not_isSumOfProducts hnot k (by omega)
    let A : Matrix (Fin k) (Fin k) 𝕜 := Matrix.of fun p q => K (fin2Vec (x q) (y p))
    have hA_det : A.det ≠ 0 := hdet
    let K_app (z : Fin 2 → α) : 𝕜 :=
      ∑ p : Fin k, K (fin2Vec (z 0) (y p)) *
        ∑ q : Fin k, A⁻¹ q p * K (fin2Vec (x q) (z 1))
    have hK_app_prod : IsSumOfProducts K_app k := by
      refine ⟨fun p => fin2Vec (fun u => K (fin2Vec u (y p)))
        (fun v => ∑ q : Fin k, A⁻¹ q p * K (fin2Vec (x q) v)), fun z => ?_⟩
      simp [K_app, Fin.prod_univ_two]
    have hK_app_r : IsSumOfProducts K_app r :=
      isSumOfProducts_mono (by omega) hK_app_prod
    have hne_fun : K ≠ K_app := fun heq => hnot (heq ▸ hK_app_r)
    obtain ⟨z₀, hz₀⟩ : ∃ z₀, K z₀ ≠ K_app z₀ := Function.ne_iff.mp hne_fun
    let x' : Fin k ⊕ Fin 1 → α := Sum.elim x (fun _ => z₀ 0)
    let y' : Fin k ⊕ Fin 1 → α := Sum.elim y (fun _ => z₀ 1)
    let B : Matrix (Fin k) (Fin 1) 𝕜 := Matrix.of fun p _ => K (fin2Vec (z₀ 0) (y p))
    let C : Matrix (Fin 1) (Fin k) 𝕜 := Matrix.of fun _ q => K (fin2Vec (x q) (z₀ 1))
    let D : Matrix (Fin 1) (Fin 1) 𝕜 := Matrix.of fun _ _ => K (fin2Vec (z₀ 0) (z₀ 1))
    let _ : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA_det)
    have hinv_eq : ⅟A = A⁻¹ := Matrix.invOf_eq_nonsing_inv A
    have hfb_det : (Matrix.fromBlocks A B C D).det ≠ 0 := by
      rw [Matrix.det_fromBlocks₁₁, hinv_eq]
      refine mul_ne_zero hA_det ?_
      rw [Matrix.det_fin_one]
      have hschur : (D - C * A⁻¹ * B) 0 0 = K z₀ - K_app z₀ := by
        have hz_eta : fin2Vec (z₀ 0) (z₀ 1) = z₀ := fin2Vec_eta z₀
        change D 0 0 - ((C * A⁻¹) * B) 0 0 = K z₀ - K_app z₀
        simp only [D, C, B, K_app, Matrix.of_apply, Matrix.mul_apply, hz_eta]
        congr 1
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => by ring
      rw [hschur]
      exact sub_ne_zero.mpr hz₀
    let e : Fin k ⊕ Fin 1 ≃ Fin (k + 1) := finSumFinEquiv
    refine ⟨x' ∘ e.symm, y' ∘ e.symm, ?_⟩
    have hsub : (Matrix.of fun p q : Fin (k + 1) =>
        K (fin2Vec ((x' ∘ e.symm) q) ((y' ∘ e.symm) p))) =
        Matrix.reindex e e (Matrix.fromBlocks A B C D) := by
      ext p q
      rcases h1 : e.symm p with p₀ | p₁ <;> rcases h2 : e.symm q with q₀ | q₁ <;>
        simp [Matrix.reindex_apply, Matrix.submatrix_apply, h1, h2, x', y', A, B, C, D,
          Matrix.fromBlocks]
    rw [hsub, Matrix.det_reindex_self]
    exact hfb_det
end LowerSemicontinuity
section AdjugateBorderRank
end AdjugateBorderRank
section UniversalApproximation
end UniversalApproximation
end KernelRank
end

set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank
namespace KernelRank
theorem _root_.solution {𝕜 α ι : Type*} [Field 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] [T2Space 𝕜] {l : Filter ι} [l.NeBot]
    {F : ι → (Fin 2 → α) → 𝕜} {K : (Fin 2 → α) → 𝕜} {r : ℕ}
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (r : ℕ))
    (htend : ∀ z, Filter.Tendsto (fun i => F i z) l (𝓝 (K z))) :
    separableRank K ≤ (r : ℕ) := by
  by_contra hnot_le
  have hnot_prod : ¬ IsSumOfProducts K r := fun hK => hnot_le (iInf₂_le r hK)
  obtain ⟨x, y, hdet_ne⟩ :=
    exists_submatrix_det_ne_zero_of_not_isSumOfProducts hnot_prod (r + 1) le_rfl
  let M (G : (Fin 2 → α) → 𝕜) : Matrix (Fin (r + 1)) (Fin (r + 1)) 𝕜 :=
    Matrix.of fun p q => G (fin2Vec (x q) (y p))
  have hdet_tend : Filter.Tendsto (fun i => (M (F i)).det) l (𝓝 (M K).det) := by
    have hM_t : Filter.Tendsto (fun i => M (F i)) l (𝓝 (M K)) :=
      tendsto_pi_nhds.mpr fun p => tendsto_pi_nhds.mpr fun q => htend (fin2Vec (x q) (y p))
    exact (Continuous.matrix_det continuous_id).continuousAt.tendsto.comp hM_t
  have hdet_zero : ∀ᶠ i in l, (M (F i)).det = 0 := by
    filter_upwards [hrank] with i hi
    have hex : ∃ N ≤ r, IsSumOfProducts (F i) N := by
      by_contra hno
      push Not at hno
      have hgt : ((r : ℕ) : ℕ∞) < separableRank (F i) := by
        have hle : ((r + 1 : ℕ) : ℕ∞) ≤ separableRank (F i) :=
          le_iInf₂ fun N hN => by
            have : r < N := lt_of_not_ge fun hNr => hno N hNr hN
            exact_mod_cast Nat.succ_le_of_lt this
        exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self r) hle
      exact not_lt_of_ge hi hgt
    obtain ⟨N, hNr, hprodN⟩ := hex
    obtain ⟨f, hf⟩ := isSumOfProducts_mono hNr hprodN
    let U : Matrix (Fin (r + 1)) (Fin r) 𝕜 := Matrix.of fun p k => f k 1 (y p)
    let V : Matrix (Fin r) (Fin (r + 1)) 𝕜 := Matrix.of fun k q => f k 0 (x q)
    have hfac : M (F i) = U * V := by
      ext p q
      simp only [M, U, V, Matrix.of_apply, Matrix.mul_apply, hf, Fin.prod_univ_two,
        fin2Vec_zero, fin2Vec_one]
      refine Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hfac]
    exact det_mul_eq_zero_of_lt U V
  have hzero_lim : Filter.Tendsto (fun i => (M (F i)).det) l (𝓝 0) :=
    tendsto_const_nhds.congr' (hdet_zero.mono fun _ h => h.symm)
  exact hdet_ne (tendsto_nhds_unique hdet_tend hzero_lim)
end KernelRank
