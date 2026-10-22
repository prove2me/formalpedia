-- Prove2me | solution 1 for ModernConvex.CQRepr.legendre_cqr
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:20:11.915694+00:00
-- url     : https://prove2.me/submissions/df79bd6f-2d0c-42e3-8a3b-7d3b056ba38d

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
def g70mc2_IsCC {ι : Type*} (K : Set (ι → ℝ)) : Prop :=
  K.Nonempty ∧ (∀ a ∈ K, ∀ a' ∈ K, a + a' ∈ K) ∧ (∀ a ∈ K, ∀ t : ℝ, 0 ≤ t → t • a ∈ K)

def g70mc2_dual {ι : Type*} [Fintype ι] (K : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {l | ∀ a ∈ K, 0 ≤ l ⬝ᵥ a}

theorem g70mc2_vec {κ : Type*} [Fintype κ] [DecidableEq κ] (g : (κ → ℝ) →ₗ[ℝ] ℝ) :
    ∀ z : κ → ℝ, g z = (fun j => g (Pi.single j 1)) ⬝ᵥ z := by
  intro z
  conv_lhs => rw [show z = ∑ j, z j • Pi.single j (1:ℝ) by
    ext k; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum, dotProduct, mul_comm]


lemma g70mc2_convex {ι : Type*} [Fintype ι] {K : Set (ι → ℝ)} (hK : g70mc2_IsCC K) : Convex ℝ K := by
  intro a ha b hb s t hs ht _
  exact hK.2.1 _ (hK.2.2 a ha s hs) _ (hK.2.2 b hb t ht)


lemma g70mc2_ball_cone {ι : Type*} [Fintype ι] {K : Set (ι → ℝ)} (hK : g70mc2_IsCC K) {k0 : ι → ℝ}
    (hk0 : k0 ∈ interior K) (k : ι → ℝ) (hk : k ∈ K) : k0 + k ∈ interior K := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hk0)
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨ε, hε, fun z hz => ?_⟩
  have : z - k ∈ K := hball (by
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    rwa [show z - k - k0 = z - (k0 + k) by abel])
  simpa using hK.2.1 _ this _ hk

open scoped Pointwise in
lemma g70mc2_smul_int {ι : Type*} [Fintype ι] {K : Set (ι → ℝ)} (hK : g70mc2_IsCC K) {k0 : ι → ℝ}
    (hk0 : k0 ∈ interior K) {t : ℝ} (ht : 0 < t) : t • k0 ∈ interior K := by
  have h1 : t • K ⊆ K := by
    rintro _ ⟨k, hk, rfl⟩; exact hK.2.2 k hk t ht.le
  have : t • k0 ∈ t • interior K := ⟨k0, hk0, rfl⟩
  rw [← interior_smul₀ ht.ne'] at this
  exact interior_mono h1 this

lemma g70mc2_scalar {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] (K : Set (ι → ℝ)) (hK : g70mc2_IsCC K)
    (A : Matrix (ι) (κ) ℝ) (b : ι → ℝ) (c : κ → ℝ) (d : ℝ)
    (hS : ∃ x : κ → ℝ, A *ᵥ x - b ∈ interior K)
    (h : ∀ x : κ → ℝ, A *ᵥ x - b ∈ K → d ≤ c ⬝ᵥ x) :
    ∃ l : ι → ℝ, l ∈ g70mc2_dual K ∧ Aᵀ *ᵥ l = c ∧ d ≤ l ⬝ᵥ b := by
  obtain ⟨x0, hx0⟩ := hS
  by_cases hc : c = 0
  · refine ⟨0, fun a _ => by simp, by simp [hc], ?_⟩
    have := h x0 (interior_subset hx0); simp [hc] at this; simpa using this
  have hcc : 0 < c ⬝ᵥ c := by
    have h0 : 0 ≤ c ⬝ᵥ c := Finset.sum_nonneg fun i _ => mul_self_nonneg (c i)
    exact lt_of_le_of_ne h0 (Ne.symm (fun h' => hc (dotProduct_self_eq_zero.mp h')))
  set U : Set (ι → ℝ) := (fun x => A *ᵥ x - b) '' {x | c ⬝ᵥ x < d} with hU
  have hpt : ∀ s : ℝ, c ⬝ᵥ ((s / (c ⬝ᵥ c)) • c) = s := by
    intro s; rw [dotProduct_smul, smul_eq_mul]; field_simp
  have hUc : Convex ℝ U := by
    rintro _ ⟨x1, hx1, rfl⟩ _ ⟨x2, hx2, rfl⟩ s t hs ht hst
    refine ⟨s • x1 + t • x2, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, dotProduct_add, dotProduct_smul, smul_eq_mul] at hx1 hx2 ⊢
      rcases eq_or_lt_of_le hs with h0 | hpos
      · subst h0; have : t = 1 := by linarith
        subst this; linarith
      · have h1 := mul_lt_mul_of_pos_left hx1 hpos
        have h2 := mul_le_mul_of_nonneg_left hx2.le ht
        have : s * d + t * d = d := by rw [← add_mul, hst, one_mul]
        linarith
    · ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec_add, mulVec_smul]
      linear_combination (b i) * hst
  have hdisj : Disjoint (interior K) U := by
    rw [Set.disjoint_left]
    rintro _ hk ⟨x, hx, rfl⟩
    have := h x (interior_subset hk)
    simp only [Set.mem_setOf_eq] at hx; linarith
  obtain ⟨f, u, hfK, hfU⟩ := geometric_hahn_banach_open (g70mc2_convex hK).interior isOpen_interior hUc hdisj
  set g : ι → ℝ := fun j => f (Pi.single j 1)
  have hg : ∀ z, f z = g ⬝ᵥ z := g70mc2_vec f.toLinearMap
  clear_value g
  set lam := -g with hlam
  clear_value lam
  have hAt : ∀ (v : ι → ℝ) (x : κ → ℝ), (Aᵀ *ᵥ v) ⬝ᵥ x = v ⬝ᵥ (A *ᵥ x) := by
    intro v x; rw [dotProduct_mulVec, mulVec_transpose, dotProduct_comm]
  -- lam ∈ K*
  have hlamK : lam ∈ g70mc2_dual K := by
    intro k hk
    by_contra hneg; push Not at hneg
    have hgk : 0 < g ⬝ᵥ k := by rw [hlam, neg_dotProduct] at hneg; linarith
    have ht : 0 < (u - g ⬝ᵥ (A *ᵥ x0 - b)) / (g ⬝ᵥ k) + 1 := by
      have := hfK _ hx0; rw [hg] at this
      have : 0 < u - g ⬝ᵥ (A *ᵥ x0 - b) := by linarith
      positivity
    have := hfK _ (g70mc2_ball_cone hK hx0 _ (hK.2.2 k hk _ ht.le))
    rw [hg, dotProduct_add, dotProduct_smul, smul_eq_mul, add_mul, div_mul_cancel₀ _ hgk.ne'] at this
    linarith
  -- u ≥ 0
  have hu : 0 ≤ u := by
    by_contra hneg; push Not at hneg
    have hk0 := hfK _ hx0; rw [hg] at hk0
    have hgk0 : g ⬝ᵥ (A *ᵥ x0 - b) < 0 := by linarith
    have ht : 0 < u / (2 * g ⬝ᵥ (A *ᵥ x0 - b)) := div_pos_of_neg_of_neg hneg (by linarith)
    have := hfK _ (g70mc2_smul_int hK hx0 ht)
    rw [hg, dotProduct_smul, smul_eq_mul] at this
    have e : u / (2 * g ⬝ᵥ (A *ᵥ x0 - b)) * (g ⬝ᵥ (A *ᵥ x0 - b)) = u / 2 := by
      rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hgk0.ne]
    linarith
  -- on U
  have hU' : ∀ x, c ⬝ᵥ x < d → (Aᵀ *ᵥ lam) ⬝ᵥ x - lam ⬝ᵥ b ≤ -u := by
    intro x hx
    have := hfU _ ⟨x, hx, rfl⟩
    rw [hg, dotProduct_sub] at this
    rw [hAt, hlam, neg_dotProduct, neg_dotProduct]; linarith
  set w := Aᵀ *ᵥ lam with hw
  clear_value w
  obtain ⟨x1, hx1d⟩ : ∃ x1 : κ → ℝ, x1 = ((d - 1) / (c ⬝ᵥ c)) • c := ⟨_, rfl⟩
  have hx1 : c ⬝ᵥ x1 < d := by rw [hx1d, hpt]; linarith
  -- w ⊥ (c⊥)
  have hperp : ∀ z, c ⬝ᵥ z = 0 → w ⬝ᵥ z = 0 := by
    intro z hz
    by_contra hne
    have key : ∀ s : ℝ, s * (w ⬝ᵥ z) ≤ -u - w ⬝ᵥ x1 + lam ⬝ᵥ b := by
      intro s
      have := hU' (x1 + s • z) (by rw [dotProduct_add, dotProduct_smul, hz, smul_eq_mul]; linarith)
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at this; linarith
    have := key ((-u - w ⬝ᵥ x1 + lam ⬝ᵥ b + 1) / (w ⬝ᵥ z))
    rw [div_mul_cancel₀ _ hne] at this; linarith
  set μ := (w ⬝ᵥ c) / (c ⬝ᵥ c) with hμ
  clear_value μ
  have hwμ : w = μ • c := by
    have hz : c ⬝ᵥ (w - μ • c) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hμ, dotProduct_comm c w]; field_simp; ring
    have h1 := hperp _ hz
    have hz' : (w - μ • c) ⬝ᵥ c = 0 := by rw [dotProduct_comm]; exact hz
    have h2 : (w - μ • c) ⬝ᵥ (w - μ • c) = 0 := by
      rw [sub_dotProduct, h1, smul_dotProduct]; simp [hz, hz']
    exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp h2)
  -- μ > 0
  have hμpos : 0 < μ := by
    rcases lt_trichotomy μ 0 with hneg | hzero | hpos
    · exfalso
      set C := |-u - μ * (c ⬝ᵥ x1) + lam ⬝ᵥ b| + 1 with hC
      have hden : 0 < -μ * (c ⬝ᵥ c) := mul_pos (by linarith) hcc
      set sc := C / (-μ * (c ⬝ᵥ c))
      have hsc : 0 < sc := div_pos (by positivity) hden
      have := hU' (x1 - sc • c) (by
        rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
        have : 0 < sc * (c ⬝ᵥ c) := mul_pos hsc hcc
        linarith)
      rw [hwμ, smul_dotProduct, dotProduct_sub, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
      have e : μ * (c ⬝ᵥ x1 - sc * (c ⬝ᵥ c)) = μ * (c ⬝ᵥ x1) + C := by
        have : sc * (-μ * (c ⬝ᵥ c)) = C := div_mul_cancel₀ _ hden.ne'
        linear_combination this
      rw [e] at this
      have := le_abs_self (-u - μ * (c ⬝ᵥ x1) + lam ⬝ᵥ b)
      linarith
    · exfalso
      have hw0 : w = 0 := by rw [hwμ, hzero, zero_smul]
      have h1 := hU' x1 hx1
      rw [hw0, zero_dotProduct] at h1
      have hk0 := hfK _ hx0
      rw [hg, dotProduct_sub, ← hAt] at hk0
      have : Aᵀ *ᵥ g = -w := by rw [hw, hlam, mulVec_neg, neg_neg]
      rw [this, hw0, neg_zero, zero_dotProduct] at hk0
      rw [hlam, neg_dotProduct] at h1
      linarith
    · exact hpos
  refine ⟨μ⁻¹ • lam, fun a ha => ?_, ?_, ?_⟩
  · rw [smul_dotProduct, smul_eq_mul]; exact mul_nonneg (inv_pos.mpr hμpos).le (hlamK a ha)
  · rw [mulVec_smul, ← hw, hwμ, smul_smul, inv_mul_cancel₀ hμpos.ne', one_smul]
  · rw [smul_dotProduct, smul_eq_mul]
    by_contra hlt; push Not at hlt
    obtain ⟨s, hsd⟩ : ∃ s : ℝ, s = (μ⁻¹ * lam ⬝ᵥ b + d) / 2 := ⟨_, rfl⟩
    have hs : s < d := by rw [hsd]; linarith
    have := hU' ((s / (c ⬝ᵥ c)) • c) (by rw [hpt]; exact hs)
    rw [hwμ, smul_dotProduct, hpt, smul_eq_mul] at this
    have : s ≤ μ⁻¹ * lam ⬝ᵥ b := by
      rw [le_inv_mul_iff₀ hμpos]; linarith
    rw [hsd] at this; linarith



theorem g70mc2_block_dot (K : IceCreamProduct) (l z : K.Idx → ℝ) :
    l ⬝ᵥ z = ∑ j : Fin K.N, ((∑ i : Fin (K.d j), l ⟨j, Fin.castSucc i⟩ * z ⟨j, Fin.castSucc i⟩) +
      l ⟨j, Fin.last _⟩ * z ⟨j, Fin.last _⟩) := by
  unfold dotProduct
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_castSucc]

theorem g70mc2_self_dual1 (K : IceCreamProduct) (l z : K.Idx → ℝ) (hl : l ∈ K.cone)
    (hz : z ∈ K.cone) : 0 ≤ l ⬝ᵥ z := by
  rw [g70mc2_block_dot]
  refine Finset.sum_nonneg fun j _ => ?_
  have h1 := hl j
  have h2 := hz j
  have cs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i : Fin (K.d j) => -l ⟨j, Fin.castSucc i⟩)
    (fun i => z ⟨j, Fin.castSucc i⟩)
  simp only [neg_mul, Finset.sum_neg_distrib, neg_sq] at cs
  have h3 := mul_le_mul h1 h2 (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans h1)
  linarith

theorem g70mc2_self_dual2 (K : IceCreamProduct) (l : K.Idx → ℝ)
    (hl : ∀ z ∈ K.cone, 0 ≤ l ⬝ᵥ z) : l ∈ K.cone := by
  intro j
  set s := Real.sqrt (∑ i : Fin (K.d j), l ⟨j, Fin.castSucc i⟩ ^ 2) with hs
  have key : ∀ c : ℝ, s ≤ c → 0 ≤ -s ^ 2 + l ⟨j, Fin.last _⟩ * c := by
    intro c hc
    let z : K.Idx → ℝ := fun x => if x.1 = j then (if x.2 = Fin.last _ then c else -(l x)) else 0
    have hz : z ∈ K.cone := by
      intro j'
      by_cases hj : j' = j
      · subst hj
        simp only [z, if_true, Fin.castSucc_ne_last, if_false, neg_sq]
        exact hc
      · simp [z, hj]
    have := hl z hz
    rw [g70mc2_block_dot, Finset.sum_eq_single j] at this
    · simp only [z, if_true, Fin.castSucc_ne_last, if_false] at this
      have hss : s ^ 2 = ∑ i : Fin (K.d j), l ⟨j, Fin.castSucc i⟩ ^ 2 :=
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
      have : ∑ i : Fin (K.d j), l ⟨j, Fin.castSucc i⟩ * -l ⟨j, Fin.castSucc i⟩ = -s ^ 2 := by
        rw [hss, ← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
      linarith
    · intro j' _ hj; simp [z, hj]
    · simp
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hs0 with h0 | hpos
  · have := key (s + 1) (by linarith)
    rw [← h0] at this ⊢; nlinarith
  · have := key s le_rfl
    nlinarith

theorem g70mc2_At {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (v : ι → ℝ)
    (x : κ → ℝ) : (Aᵀ *ᵥ v) ⬝ᵥ x = v ⬝ᵥ (A *ᵥ x) := by
  rw [dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

theorem g70mc2_isCC (K : IceCreamProduct) : g70mc2_IsCC K.cone :=
  ⟨⟨0, fun j => by simp⟩, fun a ha a' ha' => g70mc2_cone_add K a a' ha ha',
    fun a ha t ht => g70mc2_cone_smul K t ht a ha⟩

theorem g70mc2_leg_iff {n : ℕ} (f : (Fin n → ℝ) → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (y : Fin n → ℝ) (s : ℝ) :
    legendre f y ≤ (s : EReal) ↔ ∀ (x : Fin n → ℝ) (t : ℝ), f x ≤ (t : EReal) → y ⬝ᵥ x - t ≤ s := by
  unfold legendre
  rw [iSup_le_iff]
  constructor
  · intro h x t hft
    have h1 := h x
    have h2 : ((y ⬝ᵥ x : ℝ) : EReal) - (t : EReal) ≤ ((y ⬝ᵥ x : ℝ) : EReal) - f x :=
      EReal.sub_le_sub le_rfl hft
    rw [← EReal.coe_sub] at h2
    exact EReal.coe_le_coe_iff.mp (h2.trans h1)
  · intro h x
    induction hfx : f x using EReal.rec with
    | bot => exact absurd hfx (hbot x)
    | top => simp
    | coe t =>
      rw [← EReal.coe_sub]
      exact EReal.coe_le_coe_iff.mpr (h x t (le_of_eq hfx))

theorem solution {n q : ℕ} (K : IceCreamProduct) (A : Matrix K.Idx (Fin n) ℝ)
    (p : K.Idx → ℝ) (B : Matrix K.Idx (Fin q) ℝ) (b : K.Idx → ℝ)
    (f : (Fin n → ℝ) → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hf : ∀ (x : Fin n → ℝ) (t : ℝ),
      f x ≤ (t : EReal) ↔ ∃ u : Fin q → ℝ, A *ᵥ x + t • p + B *ᵥ u + b ∈ K.cone)
    (hstrict : ∃ (x : Fin n → ℝ) (t : ℝ) (u : Fin q → ℝ),
      A *ᵥ x + t • p + B *ᵥ u + b ∈ interior K.cone) :
    ∀ (y : Fin n → ℝ) (s : ℝ), legendre f y ≤ (s : EReal) ↔
      ∃ ξ : K.Idx → ℝ, Aᵀ *ᵥ ξ = -y ∧ Bᵀ *ᵥ ξ = 0 ∧ p ⬝ᵥ ξ = 1 ∧ b ⬝ᵥ ξ ≤ s ∧ ξ ∈ K.cone := by
  intro y s
  rw [g70mc2_leg_iff f hbot]
  let P1 : Matrix K.Idx Unit ℝ := Matrix.of fun i _ => p i
  have hP1 : ∀ t : ℝ, P1 *ᵥ (fun _ => t) = t • p := by
    intro t; ext i; simp [P1, mulVec, dotProduct, mul_comm]
  have hP1t : ∀ l : K.Idx → ℝ, P1ᵀ *ᵥ l = fun _ => p ⬝ᵥ l := by
    intro l; ext i; simp [P1, mulVec, dotProduct]
  let M := Matrix.fromCols A (Matrix.fromCols P1 B)
  have hM : ∀ (x : Fin n → ℝ) (t : ℝ) (u : Fin q → ℝ),
      M *ᵥ Sum.elim x (Sum.elim (fun _ => t) u) = A *ᵥ x + t • p + B *ᵥ u := by
    intro x t u
    simp only [M, fromCols_mulVec_sumElim, hP1, add_assoc]
  constructor
  · intro h
    obtain ⟨x0, t0, u0, hx0⟩ := hstrict
    obtain ⟨l, hlK, hlM, hlb⟩ := g70mc2_scalar K.cone (g70mc2_isCC K) M (-b)
      (Sum.elim (-y) (Sum.elim (fun _ => 1) 0)) (-s)
      ⟨Sum.elim x0 (Sum.elim (fun _ => t0) u0), by rw [hM, sub_neg_eq_add]; exact hx0⟩
      (fun z hz => by
        have hz' : A *ᵥ (z ∘ Sum.inl) + z (Sum.inr (Sum.inl ())) • p + B *ᵥ (fun i => z (Sum.inr (Sum.inr i))) + b ∈ K.cone := by
          have e : z = Sum.elim (z ∘ Sum.inl) (Sum.elim (fun _ => z (Sum.inr (Sum.inl ())))
              (fun i => z (Sum.inr (Sum.inr i)))) := by
            ext (i | (u | i)) <;> rfl
          rw [e, hM, sub_neg_eq_add] at hz; exact hz
        have := h _ _ ((hf _ _).mpr ⟨_, hz'⟩)
        have e : Sum.elim (-y) (Sum.elim (fun _ => 1) 0) ⬝ᵥ z =
            -(y ⬝ᵥ (z ∘ Sum.inl)) + z (Sum.inr (Sum.inl ())) := by
          simp [dotProduct, Fintype.sum_sum_type]
        rw [e]; linarith)
    have hl : l ∈ K.cone := g70mc2_self_dual2 K l hlK
    simp only [M, transpose_fromCols, fromRows_mulVec, hP1t] at hlM
    have h1 : Aᵀ *ᵥ l = -y := funext fun i => congrFun hlM (Sum.inl i)
    have h2 : Bᵀ *ᵥ l = 0 := funext fun i => congrFun hlM (Sum.inr (Sum.inr i))
    have h3 : p ⬝ᵥ l = 1 := congrFun hlM (Sum.inr (Sum.inl ()))
    refine ⟨l, h1, h2, h3, ?_, hl⟩
    rw [dotProduct_neg] at hlb
    rw [dotProduct_comm]; linarith
  · rintro ⟨ξ, h1, h2, h3, h4, hξ⟩ x t hft
    obtain ⟨u, hu⟩ := (hf x t).mp hft
    have hpos := g70mc2_self_dual1 K ξ _ hξ hu
    have hB : ξ ⬝ᵥ (B *ᵥ u) = 0 := by rw [← g70mc2_At, h2, zero_dotProduct]
    have hA : ξ ⬝ᵥ (A *ᵥ x) = -(y ⬝ᵥ x) := by rw [← g70mc2_At, h1, neg_dotProduct]
    rw [dotProduct_add, dotProduct_add, dotProduct_add, hB, hA, dotProduct_smul, smul_eq_mul,
      dotProduct_comm ξ p, h3, dotProduct_comm ξ b] at hpos
    linarith
