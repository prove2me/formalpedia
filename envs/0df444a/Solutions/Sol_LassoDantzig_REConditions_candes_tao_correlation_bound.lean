-- Prove2me | solution 1 for LassoDantzig.REConditions.candes_tao_correlation_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:35:17.235167+00:00
-- url     : https://prove2.me/submissions/0e8d2fb5-f8f6-4017-b8ff-809375b56f65

import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

lemma aux_ct_norm {k : ℕ} (c : Fin k → ℝ) :
    ‖(WithLp.toLp 2 c : EuclideanSpace ℝ (Fin k))‖ = Real.sqrt (∑ j, c j ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.norm_eq_abs, sq_abs]

lemma aux_ct_inner {k : ℕ} (a b : Fin k → ℝ) :
    inner ℝ (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin k)) (WithLp.toLp 2 b) =
      ∑ i, a i * b i := by
  simp [PiLp.inner_apply, mul_comm]

lemma aux_ct_cs {k : ℕ} (a b : Fin k → ℝ) :
    ∑ i, a i * b i ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) := by
  rw [← aux_ct_inner, ← aux_ct_norm, ← aux_ct_norm]
  exact real_inner_le_norm _ _

lemma aux_ct_opbound {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ c : Fin M → ℝ, Real.sqrt (∑ i, X.mulVec c i ^ 2) ≤ C * Real.sqrt (∑ j, c j ^ 2) := by
  let L : EuclideanSpace ℝ (Fin M) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 X)
  refine ⟨‖L‖, norm_nonneg _, fun c => ?_⟩
  have h := L.le_opNorm (WithLp.toLp 2 c)
  rw [← aux_ct_norm, ← aux_ct_norm]
  have hL : L (WithLp.toLp 2 c) = WithLp.toLp 2 (X.mulVec c) := by
    simp [L, Matrix.toLpLin_toLp]
  rw [hL] at h
  exact h

lemma aux_ct_sumsq_pos {k : ℕ} (c : Fin k → ℝ) (hc : c ≠ 0) : 0 < ∑ j, c j ^ 2 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
  have h := Finset.single_le_sum (f := fun j => c j ^ 2) (fun i _ => sq_nonneg (c i))
    (Finset.mem_univ j)
  have hj' : c j ≠ 0 := by simpa using hj
  have : 0 < c j ^ 2 := by positivity
  linarith

lemma aux_ct_theta_bdd {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (m1 m2 : ℕ) :
    BddAbove (corrSet X m1 m2) := by
  obtain ⟨C, hC0, hC⟩ := aux_ct_opbound X
  refine ⟨C ^ 2 / n, ?_⟩
  rintro t ⟨I1, I2, -, -, -, c1, c2, -, -, hc1, hc2, rfl⟩
  have ha : 0 < Real.sqrt (∑ j, c1 j ^ 2) := Real.sqrt_pos.mpr (aux_ct_sumsq_pos _ hc1)
  have hb : 0 < Real.sqrt (∑ j, c2 j ^ 2) := Real.sqrt_pos.mpr (aux_ct_sumsq_pos _ hc2)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have h1 := aux_ct_cs (X.mulVec c1) (X.mulVec c2)
  have h2 := hC c1
  have h3 := hC c2
  have h4 := mul_le_mul h2 h3 (Real.sqrt_nonneg _) (by positivity)
  rw [div_le_div_iff₀ (by positivity) hnR]
  have : ∑ i, X.mulVec c1 i * X.mulVec c2 i ≤
      C ^ 2 * (Real.sqrt (∑ j, c1 j ^ 2) * Real.sqrt (∑ j, c2 j ^ 2)) := by
    nlinarith
  nlinarith

lemma aux_ct_neg_mem {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (m1 m2 : ℕ) (t : ℝ)
    (ht : t ∈ corrSet X m1 m2) : -t ∈ corrSet X m1 m2 := by
  obtain ⟨I1, I2, hd, h1, h2, c1, c2, hs1, hs2, hc1, hc2, rfl⟩ := ht
  refine ⟨I1, I2, hd, h1, h2, -c1, c2, fun j hj => by simp [hs1 j hj], hs2,
    neg_ne_zero.mpr hc1, hc2, ?_⟩
  simp [Matrix.mulVec_neg, neg_div, Finset.sum_neg_distrib]

lemma aux_ct_theta_nonneg {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (hM : 2 ≤ M) (m1 m2 : ℕ)
    (h1 : 1 ≤ m1) (h2 : 1 ≤ m2) : 0 ≤ theta X m1 m2 := by
  classical
  have hne : (corrSet X m1 m2).Nonempty := by
    let i0 : Fin M := ⟨0, by omega⟩
    let i1 : Fin M := ⟨1, by omega⟩
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    refine ⟨_, {i0}, {i1}, ?_, by simpa using h1, by simpa using h2, Pi.single i0 1,
      Pi.single i1 1, ?_, ?_, ?_, ?_, rfl⟩
    · simpa using h01
    · intro j hj
      have : j ≠ i0 := by simpa using hj
      simp [this]
    · intro j hj
      have : j ≠ i1 := by simpa using hj
      simp [this]
    · simp
    · simp
  obtain ⟨t, ht⟩ := hne
  have hb := aux_ct_theta_bdd X m1 m2
  have a1 := le_csSup hb ht
  have a2 := le_csSup hb (aux_ct_neg_mem X m1 m2 t ht)
  unfold theta
  linarith

lemma aux_ct_phi_le {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (u : ℕ) (c : Fin M → ℝ)
    (h1 : 1 ≤ sparsity c) (h2 : sparsity c ≤ u) :
    phiMin X u ≤ gramQuad X c / ∑ j, c j ^ 2 := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro q ⟨x, -, -, rfl⟩
    unfold gramQuad
    apply div_nonneg _ (Finset.sum_nonneg fun j _ => sq_nonneg _)
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => sq_nonneg _)
  · exact ⟨c, h1, h2, rfl⟩

lemma aux_ct_span {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (J : Finset (Fin M))
    (w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ colSpan X J) :
    ∃ c : Fin M → ℝ, (∀ j, j ∉ J → c j = 0) ∧ WithLp.toLp 2 (X.mulVec c) = w := by
  classical
  unfold colSpan at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨Pi.single j 1, fun i hi => ?_, ?_⟩
    · have : i ≠ j := fun h => hi (h ▸ hj)
      simp [this]
    · congr 1
      ext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c1, h1, rfl⟩ := hx
    obtain ⟨c2, h2, rfl⟩ := hy
    exact ⟨c1 + c2, fun j hj => by simp [h1 j hj, h2 j hj], by simp [Matrix.mulVec_add]⟩
  | smul a x _ hx =>
    obtain ⟨c1, h1, rfl⟩ := hx
    exact ⟨a • c1, fun j hj => by simp [h1 j hj], by simp [Matrix.mulVec_smul]⟩

lemma aux_ct_restrict_sq {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) :
    ∑ j, restrict δ J j ^ 2 = ∑ j ∈ J, δ j ^ 2 := by
  classical
  unfold restrict
  simp [ite_pow, Finset.sum_ite_mem]

end LassoDantzig.REConditions

open LassoDantzig.REConditions

theorem solution {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M) (s : ℕ) (hs : 1 ≤ s)
    (δ : Fin M → ℝ) (J J' : Finset (Fin M)) (hdisj : Disjoint J J')
    (hJ : J.card ≤ s) (hJ' : J'.card ≤ 2 * s) (hφ : 0 < phiMin X (2 * s)) :
    1 / Real.sqrt n * projNorm X J' (X.mulVec (restrict δ J)) ≤
      theta X s (2 * s) / Real.sqrt (phiMin X (2 * s)) * l2On δ J := by
  classical
  set v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (X.mulVec (restrict δ J)) with hv
  set K := colSpan X J' with hK
  have hmem : K.starProjection v ∈ K := K.starProjection_apply_mem v
  obtain ⟨c, hcs, hc⟩ := aux_ct_span X J' _ hmem
  have hproj : projNorm X J' (X.mulVec (restrict δ J)) = Real.sqrt (∑ i, X.mulVec c i ^ 2) := by
    change ‖K.starProjection v‖ = _
    rw [← hc, aux_ct_norm]
  have hsq : ‖K.starProjection v‖ ^ 2 = inner ℝ v (K.starProjection v) := by
    rw [← real_inner_self_eq_norm_sq, K.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hmem]
  rw [← hc, aux_ct_norm, hv, aux_ct_inner,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)] at hsq
  rw [hproj]
  have hθ0 : 0 ≤ theta X s (2 * s) := aux_ct_theta_nonneg X hM s (2 * s) hs (by omega)
  have hφs : 0 < Real.sqrt (phiMin X (2 * s)) := Real.sqrt_pos.mpr hφ
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have ha0 : 0 ≤ l2On δ J := Real.sqrt_nonneg _
  by_cases hS : ∑ i, X.mulVec c i ^ 2 = 0
  · rw [hS, Real.sqrt_zero, mul_zero]
    positivity
  have hSpos : 0 < ∑ i, X.mulVec c i ^ 2 :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hS)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hSpos
  have hd0 : restrict δ J ≠ 0 := by
    intro h
    rw [h] at hsq
    simp at hsq
    exact hS hsq
  have hl2 : l2On δ J = Real.sqrt (∑ j, restrict δ J j ^ 2) := by
    unfold l2On
    rw [aux_ct_restrict_sq]
  rw [hl2]
  set a := Real.sqrt (∑ j, restrict δ J j ^ 2) with ha
  set b := Real.sqrt (∑ j, c j ^ 2) with hb
  have hapos : 0 < a := Real.sqrt_pos.mpr (aux_ct_sumsq_pos _ hd0)
  have hbpos : 0 < b := Real.sqrt_pos.mpr (aux_ct_sumsq_pos _ hc0)
  have hmemθ : (∑ i, X.mulVec (restrict δ J) i * X.mulVec c i) / ((n:ℝ) * a * b) ∈
      corrSet X s (2 * s) :=
    ⟨J, J', hdisj, hJ, hJ', restrict δ J, c, fun j hj => by simp [restrict, hj], hcs, hd0,
      hc0, rfl⟩
  have hle := le_csSup (aux_ct_theta_bdd X s (2 * s)) hmemθ
  have hT : (∑ i, X.mulVec (restrict δ J) i * X.mulVec c i) ≤
      theta X s (2 * s) * ((n:ℝ) * a * b) := by
    rw [div_le_iff₀ (by positivity)] at hle
    exact hle
  have hsub : supp c ⊆ J' := by
    intro j hj
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_contra h
    exact hj (hcs j h)
  have hsp2 : sparsity c ≤ 2 * s := (Finset.card_le_card hsub).trans hJ'
  have hsp1 : 1 ≤ sparsity c := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc0
    have hj' : c j ≠ 0 := by simpa using hj
    exact Finset.card_pos.mpr ⟨j, by simp [supp, hj']⟩
  have hφle := aux_ct_phi_le X (2 * s) c hsp1 hsp2
  unfold gramQuad at hφle
  have hb2 : b ^ 2 = ∑ j, c j ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [← hb2, le_div_iff₀ (by positivity)] at hφle
  set S := ∑ i, X.mulVec c i ^ 2 with hSdef
  set T := ∑ i, X.mulVec (restrict δ J) i * X.mulVec c i with hTdef
  set θ := theta X s (2 * s)
  set φ := phiMin X (2 * s)
  have hN2 : Real.sqrt S ^ 2 = S := Real.sq_sqrt hSpos.le
  have hNpos : 0 < Real.sqrt S := Real.sqrt_pos.mpr hSpos
  set N := Real.sqrt S
  have hr2 : Real.sqrt n ^ 2 = (n:ℝ) := Real.sq_sqrt hnR.le
  have hq2 : Real.sqrt φ ^ 2 = φ := Real.sq_sqrt hφ.le
  set r := Real.sqrt (n:ℝ)
  set q := Real.sqrt φ
  -- hφle : φ * b^2 ≤ 1/n * S
  have hA : r * q * b ≤ N := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : (n:ℝ) * φ * b ^ 2 ≤ S := by
      have := mul_le_mul_of_nonneg_left hφle hnR.le
      have e : (n:ℝ) * (1 / n * S) = S := by field_simp
      rw [e] at this
      nlinarith
    have : N ^ 2 < (r * q * b) ^ 2 := by
      apply pow_lt_pow_left₀ hcon hNpos.le (by norm_num)
    rw [mul_pow, mul_pow, hr2, hq2, hN2] at this
    linarith
  have hB : N ^ 2 ≤ θ * r ^ 2 * a * b := by
    rw [hN2, hr2]; rw [hsq]; linarith
  have hC : N ^ 2 * q ≤ θ * r * a * N := by
    have h1 : N ^ 2 * q ≤ θ * r ^ 2 * a * b * q := mul_le_mul_of_nonneg_right hB hφs.le
    have h2 : θ * r * a * (r * q * b) ≤ θ * r * a * N :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    nlinarith
  have hD : N * q ≤ θ * a * r := by
    by_contra hcon
    rw [not_le] at hcon
    have := mul_lt_mul_of_pos_left hcon hNpos
    nlinarith
  rw [one_div_mul_eq_div, div_mul_eq_mul_div, div_le_div_iff₀ hsn hφs]
  linarith
