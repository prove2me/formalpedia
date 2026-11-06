-- Prove2me | solution 1 for GuthMaynard.card_le_mul_topSingularValue_sq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:33:00.195774+00:00
-- url     : https://prove2.me/submissions/af7cf5b2-7595-496f-a6b2-ed3524eb0996

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

open Complex MeasureTheory FourierTransform
open scoped ENNReal InnerProductSpace

private lemma weight_one (w : ℝ → ℝ) (hw : IsWeight w) : w 1 = 0 := by
  have hc : ContinuousWithinAt w (Set.Iio 1) 1 :=
    hw.smooth.continuous.continuousAt.continuousWithinAt
  have hzero : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
      (nhdsWithin 1 (Set.Iio 1)) (nhds (w 1)) := by
    apply hc.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hwx : w x = 0 := by
      by_contra hne
      have hx' := hw.support_subset hne
      exact (not_le_of_gt hx) hx'.1
    exact hwx
  exact tendsto_nhds_unique hzero tendsto_const_nhds

private lemma norm_sq_le_singularValues_zero_sq_mul
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (T : E →ₗ[𝕜] F) (hd : 0 < Module.finrank 𝕜 E) (x : E) :
    ‖T x‖ ^ 2 ≤ T.singularValues 0 ^ 2 * ‖x‖ ^ 2 := by
  let hT := T.isSymmetric_adjoint_comp_self
  let B := hT.eigenvectorBasis (rfl : Module.finrank 𝕜 E = Module.finrank 𝕜 E)
  let i0 : Fin (Module.finrank 𝕜 E) := ⟨0, hd⟩
  letI : NeZero (Module.finrank 𝕜 E) := ⟨Nat.ne_of_gt hd⟩
  have heig (i : Fin (Module.finrank 𝕜 E)) :
      hT.eigenvalues rfl i ≤ T.singularValues 0 ^ 2 := by
    calc
      hT.eigenvalues rfl i ≤ hT.eigenvalues rfl i0 :=
        hT.eigenvalues_antitone rfl (Fin.zero_le i)
      _ = T.singularValues 0 ^ 2 := (T.sq_singularValues_fin rfl i0).symm
  have hnorm : ‖T x‖ ^ 2 = RCLike.re (inner 𝕜 x ((T.adjoint ∘ₗ T) x)) := by
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq]
  have hquad : RCLike.re (inner 𝕜 x ((T.adjoint ∘ₗ T) x)) =
      ∑ i, hT.eigenvalues rfl i * ‖B.repr x i‖ ^ 2 := by
    rw [← B.sum_inner_mul_inner x ((T.adjoint ∘ₗ T) x), map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← inner_conj_symm]
    simp only [← B.repr_apply_apply]
    rw [hT.eigenvectorBasis_apply_self_apply]
    calc
      RCLike.re ((starRingEnd 𝕜) (B.repr x i) *
          ((hT.eigenvalues rfl i : 𝕜) * B.repr x i)) =
          RCLike.re ((hT.eigenvalues rfl i : 𝕜) *
            ((starRingEnd 𝕜) (B.repr x i) * B.repr x i)) := by
        congr 1
        ring
      _ = hT.eigenvalues rfl i * ‖B.repr x i‖ ^ 2 := by
        rw [RCLike.conj_mul]
        simp
  rw [hnorm, hquad]
  calc
    (∑ i, hT.eigenvalues rfl i * ‖B.repr x i‖ ^ 2) ≤
        ∑ _i, T.singularValues 0 ^ 2 * ‖B.repr x _i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (heig i) (sq_nonneg _)
    _ = T.singularValues 0 ^ 2 * ‖x‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      simpa only [B.repr_apply_apply] using B.sum_sq_norm_inner_right x

private lemma smoothedPoly_eq_sum (w : ℝ → ℝ) (hw : IsWeight w) (N : ℕ) (hN : 1 ≤ N)
    (b : ℕ → ℂ) (W : Finset ℝ) (t : ℝ) (ht : t ∈ W) :
    smoothedPoly w N b t =
      ∑ n : Finset.Ioc N (2 * N), weightMatrix w N W ⟨t, ht⟩ n * b n := by
  classical
  unfold smoothedPoly
  rw [Finset.Icc_eq_cons_Ioc (by omega : N ≤ 2 * N), Finset.sum_cons]
  have hdiv : (N : ℝ) / N = 1 := by
    field_simp
  have hterm : (w ((N : ℝ) / N) : ℂ) * b N * (N : ℂ) ^ ((t : ℂ) * I) = 0 := by
    rw [hdiv, weight_one w hw]
    simp
  rw [hterm, zero_add]
  simp [weightMatrix]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro n hn
  ring

private lemma matrix_apply (w : ℝ → ℝ) (hw : IsWeight w) (N : ℕ) (hN : 1 ≤ N)
    (b : ℕ → ℂ) (W : Finset ℝ) (t : ℝ) (ht : t ∈ W) :
    (Matrix.toEuclideanLin (weightMatrix w N W)
      (WithLp.toLp 2 (fun n : Finset.Ioc N (2 * N) => b n))) ⟨t, ht⟩ =
      smoothedPoly w N b t := by
  rw [smoothedPoly_eq_sum w hw N hN b W t ht]
  rfl

private lemma coefficient_norm_sq_le (N : ℕ) (b : ℕ → ℂ) (hb : ∀ n, ‖b n‖ ≤ 1) :
    ‖(WithLp.toLp 2 (fun n : Finset.Ioc N (2 * N) => b n) :
      EuclideanSpace ℂ (Finset.Ioc N (2 * N)))‖ ^ 2 ≤ (N : ℝ) := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  calc
    (∑ n : Finset.Ioc N (2 * N), ‖b n‖ ^ 2) ≤
        ∑ _n : Finset.Ioc N (2 * N), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      nlinarith [hb n, norm_nonneg (b n)]
    _ = (N : ℝ) := by
      simp
      omega

private lemma real_algebra (N r s c : ℝ) (hN : 0 < N)
    (h : c * (N ^ r) ^ 2 ≤ N * s ^ 2) :
    c ≤ N ^ (1 - 2 * r) * s ^ 2 := by
  have hp : (N ^ r) ^ 2 = N ^ (2 * r) := by
    calc
      (N ^ r) ^ 2 = (N ^ r) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = N ^ (r * 2) := (Real.rpow_mul hN.le r 2).symm
      _ = N ^ (2 * r) := by ring_nf
  have hid : N ^ (2 * r) * N ^ (1 - 2 * r) = N := by
    rw [← Real.rpow_add hN]
    convert Real.rpow_one N using 2 <;> ring
  have hmul := mul_le_mul_of_nonneg_right h
    (Real.rpow_nonneg hN.le (1 - 2 * r))
  rw [hp] at hmul
  have hleft : c * N ^ (2 * r) * N ^ (1 - 2 * r) = N * c := by
    calc
      c * N ^ (2 * r) * N ^ (1 - 2 * r) =
          c * (N ^ (2 * r) * N ^ (1 - 2 * r)) := by ring
      _ = c * N := by rw [hid]
      _ = N * c := mul_comm _ _
  have hright : N * s ^ 2 * N ^ (1 - 2 * r) = N * (N ^ (1 - 2 * r) * s ^ 2) := by
    ring
  rw [hleft, hright] at hmul
  exact le_of_mul_le_mul_left hmul hN

end GuthMaynard

open GuthMaynard

theorem solution (w : ℝ → ℝ) (hw : IsWeight w) :
    ∃ C : ℝ, ∀ (N : ℕ), 1 ≤ N → ∀ (σ : ℝ) (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ,
      (∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖smoothedPoly w N b t‖) →
      (W.card : ℝ) ≤ C * (N : ℝ) ^ (1 - 2 * σ) * topSingularValue (weightMatrix w N W) ^ 2 := by
  classical
  refine ⟨1, ?_⟩
  intro N hN σ b hb W hW
  simp only [one_mul]
  let A := weightMatrix w N W
  let x : EuclideanSpace ℂ (Finset.Ioc N (2 * N)) :=
    WithLp.toLp 2 (fun n : Finset.Ioc N (2 * N) => b n)
  let n0 : Finset.Ioc N (2 * N) := ⟨N + 1, by simp only [Finset.mem_Ioc]; omega⟩
  letI : Nonempty (Finset.Ioc N (2 * N)) := ⟨n0⟩
  have hd : 0 < Module.finrank ℂ (EuclideanSpace ℂ (Finset.Ioc N (2 * N))) := by
    rw [finrank_euclideanSpace, Fintype.card_pos_iff]
    exact inferInstance
  have hspec : ‖Matrix.toEuclideanLin A x‖ ^ 2 ≤
      topSingularValue A ^ 2 * ‖x‖ ^ 2 := by
    exact norm_sq_le_singularValues_zero_sq_mul (Matrix.toEuclideanLin A) hd x
  have hbvec : ‖x‖ ^ 2 ≤ (N : ℝ) := by
    exact coefficient_norm_sq_le N b hb
  have hmap : ‖Matrix.toEuclideanLin A x‖ ^ 2 ≤
      (N : ℝ) * topSingularValue A ^ 2 := by
    calc
      ‖Matrix.toEuclideanLin A x‖ ^ 2 ≤ topSingularValue A ^ 2 * ‖x‖ ^ 2 := hspec
      _ ≤ topSingularValue A ^ 2 * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hbvec (sq_nonneg _)
      _ = (N : ℝ) * topSingularValue A ^ 2 := mul_comm _ _
  have hsum : (W.card : ℝ) * ((N : ℝ) ^ σ) ^ 2 ≤
      ‖Matrix.toEuclideanLin A x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      (W.card : ℝ) * ((N : ℝ) ^ σ) ^ 2 =
          ∑ _t : W, ((N : ℝ) ^ σ) ^ 2 := by simp
      _ ≤ ∑ t : W, ‖Matrix.toEuclideanLin A x t‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro t ht
        have hlarge := hW t t.property
        have happ : Matrix.toEuclideanLin A x t = smoothedPoly w N b t := by
          exact matrix_apply w hw N hN b W t t.property
        rw [happ]
        nlinarith [hlarge, Real.rpow_nonneg (Nat.cast_nonneg N) σ,
          norm_nonneg (smoothedPoly w N b t)]
  have hmain : (W.card : ℝ) * ((N : ℝ) ^ σ) ^ 2 ≤
      (N : ℝ) * topSingularValue A ^ 2 := hsum.trans hmap
  exact real_algebra (N : ℝ) σ (topSingularValue A) (W.card : ℝ)
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)) hmain
