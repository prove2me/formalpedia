-- Prove2me | solution 1 for ModernConvex.CQRepr.cqr_closedness_lemma
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:10:41.550694+00:00
-- url     : https://prove2.me/submissions/2f0ce870-1754-476a-b129-de93835b3075

import Mathlib
import Definitions.Def_ModernConvex_CQRepr_CQR

open Matrix

open ModernConvex.CQRepr

theorem g70mc2_coord_le_euc {ι : Type*} [Fintype ι] (v : ι → ℝ) (i : ι) : |v i| ≤ eucNorm v := by
  unfold eucNorm
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => v j ^ 2)
    (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))

theorem g70mc2_norm_le_euc {ι : Type*} [Fintype ι] (v : ι → ℝ) : ‖v‖ ≤ eucNorm v := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
  rw [Real.norm_eq_abs]; exact g70mc2_coord_le_euc v i

theorem g70mc2_euc_le_norm {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    eucNorm v ≤ Real.sqrt (Fintype.card ι) * ‖v‖ := by
  unfold eucNorm
  rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.sqrt_le_sqrt
  calc ∑ i, v i ^ 2 ≤ ∑ _i : ι, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        rw [← sq_abs (v i), ← Real.norm_eq_abs]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2
    _ = _ := by simp

theorem g70mc2_euc_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ eucNorm v :=
  Real.sqrt_nonneg _

/-- Lemma A: a uniform bound. -/
theorem g70mc2_bound {ι : Type*} [Fintype ι] (Kc : Set (ι → ℝ)) (hKc : IsClosed Kc)
    (hsm : ∀ c : ℝ, 0 < c → ∀ y ∈ Kc, c • y ∈ Kc) (R : Submodule ℝ (ι → ℝ))
    (hR : ∀ q ∈ R, q ∈ Kc → q = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w, ∀ q ∈ R, w + q ∈ Kc → δ * ‖q‖ ≤ ‖w‖ := by
  rcases Kc.eq_empty_or_nonempty with hE | hKne
  · exact ⟨1, one_pos, fun w q _ h => by rw [hE] at h; exact absurd h (Set.notMem_empty _)⟩
  set S : Set (ι → ℝ) := (R : Set (ι → ℝ)) ∩ Metric.sphere 0 1
  rcases S.eq_empty_or_nonempty with hS | hSne
  · refine ⟨1, one_pos, fun w q hq _ => ?_⟩
    by_contra hlt
    have hq0 : q ≠ 0 := by rintro rfl; simp at hlt
    have hmem : ‖q‖⁻¹ • q ∈ S := ⟨R.smul_mem _ hq, by
      simp [norm_smul, norm_ne_zero_iff.mpr hq0]⟩
    rw [hS] at hmem; exact hmem
  have hRc : IsClosed (R : Set (ι → ℝ)) := Submodule.closed_of_finiteDimensional R
  have hScpt : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded (hRc.inter Metric.isClosed_sphere)
    exact Metric.isBounded_sphere.subset Set.inter_subset_right
  obtain ⟨q0, hq0S, hmin⟩ := hScpt.exists_isMinOn hSne
    ((Metric.continuous_infDist_pt Kc).continuousOn)
  have hq0nK : q0 ∉ Kc := by
    intro h
    have := hR q0 hq0S.1 h
    have h1 := hq0S.2
    rw [this] at h1; simp at h1
  have hδ : 0 < Metric.infDist q0 Kc := (hKc.notMem_iff_infDist_pos hKne).mp hq0nK
  refine ⟨_, hδ, fun w q hq hwq => ?_⟩
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hmem : ‖q‖⁻¹ • q ∈ S := ⟨R.smul_mem _ hq, by
      simp [norm_smul, norm_ne_zero_iff.mpr hq0]⟩
  have h1 := hmin hmem
  simp only [Set.mem_setOf_eq] at h1
  have h2 : Metric.infDist (‖q‖⁻¹ • q) Kc ≤ dist (‖q‖⁻¹ • q) (‖q‖⁻¹ • (w + q)) :=
    Metric.infDist_le_dist_of_mem (hsm _ (inv_pos.mpr hn) _ hwq)
  rw [dist_eq_norm, ← smul_sub, norm_smul, norm_inv, norm_norm,
    show q - (w + q) = -w by abel, norm_neg] at h2
  have h3 : Metric.infDist q0 Kc ≤ ‖q‖⁻¹ * ‖w‖ := h1.trans h2
  calc Metric.infDist q0 Kc * ‖q‖ ≤ ‖q‖⁻¹ * ‖w‖ * ‖q‖ := mul_le_mul_of_nonneg_right h3 hn.le
    _ = ‖w‖ := by field_simp

/-- Lemma B: limits. -/
theorem g70mc2_limit {ι : Type*} [Fintype ι] (Kc : Set (ι → ℝ)) (hKc : IsClosed Kc)
    (hsm : ∀ c : ℝ, 0 < c → ∀ y ∈ Kc, c • y ∈ Kc) (R : Submodule ℝ (ι → ℝ))
    (hR : ∀ q ∈ R, q ∈ Kc → q = 0) (a : ℕ → ι → ℝ) (a0 : ι → ℝ)
    (ha : Filter.Tendsto a Filter.atTop (nhds a0)) (q : ℕ → ι → ℝ) (hq : ∀ k, q k ∈ R)
    (haq : ∀ k, a k + q k ∈ Kc) : ∃ q0 ∈ R, a0 + q0 ∈ Kc := by
  obtain ⟨δ, hδ, hb⟩ := g70mc2_bound Kc hKc hsm R hR
  obtain ⟨M, hM⟩ : ∃ M, ∀ k, ‖a k‖ ≤ M := by
    obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto a ha).exists_norm_le
    exact ⟨M, fun k => hM _ ⟨k, rfl⟩⟩
  have hqb : ∀ k, q k ∈ Metric.closedBall (0 : ι → ℝ) (M / δ) := by
    intro k
    rw [mem_closedBall_zero_iff, le_div_iff₀ hδ, mul_comm]
    exact (hb _ _ (hq k) (haq k)).trans (hM k)
  obtain ⟨q0, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hqb
  have hRc : IsClosed (R : Set (ι → ℝ)) := Submodule.closed_of_finiteDimensional R
  refine ⟨q0, hRc.mem_of_tendsto hlim (Filter.Eventually.of_forall fun k => hq _), ?_⟩
  exact hKc.mem_of_tendsto ((ha.comp hφ.tendsto_atTop).add hlim)
    (Filter.Eventually.of_forall fun k => haq _)

theorem g70mc2_cone_closed (K : IceCreamProduct) : IsClosed K.cone := by
  have : K.cone = ⋂ j : Fin K.N, {y : K.Idx → ℝ |
      Real.sqrt (∑ i : Fin (K.d j), y ⟨j, Fin.castSucc i⟩ ^ 2) ≤ y ⟨j, Fin.last (K.d j)⟩} := by
    ext y; simp [IceCreamProduct.cone]
  rw [this]
  exact isClosed_iInter fun j => isClosed_le (by fun_prop) (by fun_prop)

theorem g70mc2_cone_smul (K : IceCreamProduct) (c : ℝ) (hc : 0 ≤ c) (y : K.Idx → ℝ)
    (hy : y ∈ K.cone) : c • y ∈ K.cone := by
  intro j
  have := hy j
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  exact mul_le_mul_of_nonneg_left this hc

theorem g70mc2_cone_add (K : IceCreamProduct) (y z : K.Idx → ℝ)
    (hy : y ∈ K.cone) (hz : z ∈ K.cone) : y + z ∈ K.cone := by
  intro j
  have h1 := hy j
  have h2 := hz j
  let Y : EuclideanSpace ℝ (Fin (K.d j)) := WithLp.toLp 2 fun i => y ⟨j, Fin.castSucc i⟩
  let Z : EuclideanSpace ℝ (Fin (K.d j)) := WithLp.toLp 2 fun i => z ⟨j, Fin.castSucc i⟩
  have hY : ‖Y‖ = Real.sqrt (∑ i : Fin (K.d j), y ⟨j, Fin.castSucc i⟩ ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp [Y]
  have hZ : ‖Z‖ = Real.sqrt (∑ i : Fin (K.d j), z ⟨j, Fin.castSucc i⟩ ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp [Z]
  have hYZ : ‖Y + Z‖ = Real.sqrt (∑ i : Fin (K.d j), (y + z) ⟨j, Fin.castSucc i⟩ ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp [Y, Z]
  have := norm_add_le Y Z
  have hYZ' : Real.sqrt (∑ i : Fin (K.d j), (y + z) ⟨j, Fin.castSucc i⟩ ^ 2) ≤
      (y + z) ⟨j, Fin.last (K.d j)⟩ := by
    rw [← hYZ, Pi.add_apply]; linarith
  exact hYZ'

theorem g70mc2_hR {p : ℕ} (K : IceCreamProduct) (Q : Matrix K.Idx (Fin p) ℝ)
    (hQ : ∀ v : Fin p → ℝ, Q *ᵥ v ∈ K.cone → Q *ᵥ v = 0) :
    ∀ q ∈ LinearMap.range (Matrix.mulVecLin Q), q ∈ K.cone → q = 0 := by
  rintro q ⟨v, rfl⟩ h
  exact hQ v h

theorem g70mc2_closed {n p : ℕ} (K : IceCreamProduct) (P : Matrix K.Idx (Fin n) ℝ)
    (Q : Matrix K.Idx (Fin p) ℝ) (r : K.Idx → ℝ)
    (hQ : ∀ v : Fin p → ℝ, Q *ᵥ v ∈ K.cone → Q *ᵥ v = 0) : IsClosed (cqrSet K P Q r) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨xs, hxs, hlim⟩ := mem_closure_iff_seq_limit.mp hx
  choose u hu using hxs
  have hc : Continuous fun x : Fin n → ℝ => P *ᵥ x + r :=
    ((Matrix.mulVecLin P).continuous_of_finiteDimensional).add continuous_const
  obtain ⟨q0, ⟨v, rfl⟩, hq0⟩ := g70mc2_limit K.cone (g70mc2_cone_closed K)
    (fun c hc y hy => g70mc2_cone_smul K c hc.le y hy) _ (g70mc2_hR K Q hQ)
    (fun k => P *ᵥ xs k + r) (P *ᵥ x + r) ((hc.tendsto x).comp hlim)
    (fun k => Q *ᵥ u k) (fun k => ⟨u k, rfl⟩) (fun k => by
      have := hu k; simpa [add_right_comm] using this)
  exact ⟨v, by simpa [add_right_comm] using hq0⟩

theorem solution {n p : ℕ} (K : IceCreamProduct) (P : Matrix K.Idx (Fin n) ℝ)
    (Q : Matrix K.Idx (Fin p) ℝ) (r : K.Idx → ℝ)
    (hQ : ∀ v : Fin p → ℝ, Q *ᵥ v ∈ K.cone → Q *ᵥ v = 0) :
    (∃ C : ℝ, ∀ (y : Fin n → ℝ) (v : Fin p → ℝ), P *ᵥ y + Q *ᵥ v + r ∈ K.cone →
        eucNorm (Q *ᵥ v) ≤ C * (1 + eucNorm (P *ᵥ y + r))) ∧
      IsClosed (cqrSet K P Q r) := by
  refine ⟨?_, g70mc2_closed K P Q r hQ⟩
  obtain ⟨δ, hδ, hb⟩ := g70mc2_bound K.cone (g70mc2_cone_closed K)
    (fun c hc y hy => g70mc2_cone_smul K c hc.le y hy) _ (g70mc2_hR K Q hQ)
  refine ⟨Real.sqrt (Fintype.card K.Idx) / δ, fun y v h => ?_⟩
  have h1 := hb (P *ᵥ y + r) (Q *ᵥ v) ⟨v, rfl⟩ (by simpa [add_right_comm] using h)
  have h2 := g70mc2_euc_le_norm (Q *ᵥ v)
  have h3 := g70mc2_norm_le_euc (P *ᵥ y + r)
  have h4 := g70mc2_euc_nonneg (P *ᵥ y + r)
  have hs := Real.sqrt_nonneg (Fintype.card K.Idx : ℝ)
  have h5 : ‖Q *ᵥ v‖ ≤ eucNorm (P *ᵥ y + r) / δ := by
    rw [le_div_iff₀ hδ, mul_comm]; linarith
  calc eucNorm (Q *ᵥ v) ≤ Real.sqrt (Fintype.card K.Idx) * (eucNorm (P *ᵥ y + r) / δ) :=
        h2.trans (mul_le_mul_of_nonneg_left h5 hs)
    _ ≤ Real.sqrt (Fintype.card K.Idx) / δ * (1 + eucNorm (P *ᵥ y + r)) := by
        rw [mul_div_assoc', div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ hδ.le
        nlinarith
