-- Prove2me | solution 1 for ModernConvex.Spectral.eigVec_monotone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:38:47.750855+00:00
-- url     : https://prove2.me/submissions/d80bf457-c61d-4f35-aac2-68055d2356d8

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR

open Matrix ModernConvex.Spectral

lemma g70mc1_qexp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] E) (μ : ι → ℝ)
    (hb : ∀ j, T (b j) = μ j • b j) (x : E) :
    inner ℝ (T x) x = ∑ j, μ j * (inner ℝ (b j) x) ^ 2 := by
  have hx : T x = ∑ j, (μ j * inner ℝ (b j) x) • b j := by
    conv_lhs => rw [← b.sum_repr' x]
    simp only [map_sum, map_smul, hb, smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  rw [hx, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left]; ring

lemma g70mc1_nsq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    inner ℝ x x = ∑ j, (inner ℝ (b j) x) ^ 2 := by
  rw [← b.sum_inner_mul_inner x x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_comm x (b j)]; ring

lemma g70mc1_weyl {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} (hN : Module.finrank ℝ E = N) (T T' : E →ₗ[ℝ] E)
    (hT : T.IsSymmetric) (hT' : T'.IsSymmetric)
    (h : ∀ x, inner ℝ (T' x) x ≤ inner ℝ (T x) x) (i : Fin N) :
    hT'.eigenvalues hN i ≤ hT.eigenvalues hN i := by
  classical
  set b := hT.eigenvectorBasis hN
  set b' := hT'.eigenvectorBasis hN
  set μ := hT.eigenvalues hN
  set μ' := hT'.eigenvalues hN
  let L : E →ₗ[ℝ] ({j : Fin N // j ≠ i} → ℝ) :=
    LinearMap.pi (fun j => if (j : Fin N) < i then innerₛₗ ℝ (b j) else innerₛₗ ℝ (b' j))
  have hlt : Module.finrank ℝ ({j : Fin N // j ≠ i} → ℝ) < Module.finrank ℝ E := by
    rw [Module.finrank_fintype_fun_eq_card, hN, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_unique]
    have := i.isLt; omega
  have hker := LinearMap.ker_ne_bot_of_finrank_lt hlt (f := L)
  obtain ⟨x, hxk, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker] at hxk
  have hc : ∀ j : Fin N, j < i → inner ℝ (b j) x = 0 := by
    intro j hj
    have := congrFun hxk ⟨j, ne_of_lt hj⟩
    simpa [L, hj] using this
  have hc' : ∀ j : Fin N, i < j → inner ℝ (b' j) x = 0 := by
    intro j hj
    have := congrFun hxk ⟨j, ne_of_gt hj⟩
    simpa [L, not_lt.2 hj.le] using this
  have hxx : 0 < inner ℝ x x := real_inner_self_pos.2 hx0
  have e1 := g70mc1_qexp b T μ (fun j => by
    rw [hT.apply_eigenvectorBasis hN j]; rfl) x
  have e2 := g70mc1_qexp b' T' μ' (fun j => by
    rw [hT'.apply_eigenvectorBasis hN j]; rfl) x
  have n1 := g70mc1_nsq b x
  have n2 := g70mc1_nsq b' x
  have hanti := hT.eigenvalues_antitone hN
  have hanti' := hT'.eigenvalues_antitone hN
  have up : inner ℝ (T x) x ≤ μ i * inner ℝ x x := by
    rw [e1, n1, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rcases lt_or_ge j i with hj | hj
    · rw [hc j hj]; simp
    · exact mul_le_mul_of_nonneg_right (hanti hj) (sq_nonneg _)
  have lo : μ' i * inner ℝ x x ≤ inner ℝ (T' x) x := by
    rw [e2, n2, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rcases lt_or_ge i j with hj | hj
    · rw [hc' j hj]; simp
    · exact mul_le_mul_of_nonneg_right (hanti' hj) (sq_nonneg _)
  have := (lo.trans (h x)).trans up
  exact le_of_mul_le_mul_right this hxx

lemma g70mc1_eigmono {m : ℕ} (X X' : Matrix (Fin m) (Fin m) ℝ) (hX : X.IsHermitian)
    (hX' : X'.IsHermitian) (h : (X - X').PosSemidef) :
    ∀ i : Fin m, eigVec X' i ≤ eigVec X i := by
  intro i
  unfold eigVec
  rw [dif_pos hX, dif_pos hX']
  unfold IsHermitian.eigenvalues₀
  apply g70mc1_weyl
  intro x
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  have := h.dotProduct_mulVec_nonneg (WithLp.ofLp x)
  simp only [star_trivial, sub_mulVec, dotProduct_sub] at this
  have e : ∀ Y : Matrix (Fin m) (Fin m) ℝ,
      WithLp.ofLp (Matrix.toEuclideanLin Y x) = Y *ᵥ WithLp.ofLp x := fun Y => rfl
  rw [e, e]; simp only [star_trivial]
  linarith

theorem solution {m : ℕ} (X X' : Matrix (Fin m) (Fin m) ℝ) (hX : X.IsHermitian)
    (hX' : X'.IsHermitian) (h : (X - X').PosSemidef) :
    ∀ i : Fin m, eigVec X' i ≤ eigVec X i := by
  exact g70mc1_eigmono X X' hX hX' h

