-- Prove2me | solution 1 for ModernConvex.CQRepr.conic_hull_cqr
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:36:05.26945+00:00
-- url     : https://prove2.me/submissions/ab6ec9ee-d194-431e-9458-76a5f1897f47

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

abbrev g70mc2_ext (K : IceCreamProduct) : IceCreamProduct :=
  ⟨K.N + 1, Fin.cons 1 K.d, fun j => Fin.cases le_rfl (fun j => K.two_le j) j⟩

theorem g70mc2_ext_mem (K : IceCreamProduct) (v : (g70mc2_ext K).Idx → ℝ) :
    v ∈ (g70mc2_ext K).cone ↔
      (fun y : K.Idx => v ⟨y.1.succ, y.2⟩) ∈ K.cone ∧
        Real.sqrt (v ⟨0, 0⟩ ^ 2) ≤ v ⟨0, Fin.last 1⟩ := by
  unfold IceCreamProduct.cone
  simp only [Set.mem_setOf_eq]
  rw [Fin.forall_fin_succ, and_comm]
  apply and_congr Iff.rfl
  apply Iff.of_eq
  congr 1
  exact congrArg Real.sqrt (Fin.sum_univ_one (fun x : Fin 1 => v ⟨0, Fin.castSucc x⟩ ^ 2))

theorem g70mc2_Xt_cqr {n p : ℕ} (K : IceCreamProduct) (A : Matrix K.Idx (Fin n) ℝ)
    (B : Matrix K.Idx (Fin p) ℝ) (b : K.Idx → ℝ) :
    IsCQr {z : Fin (n + 1) → ℝ | (∃ u : Fin p → ℝ,
        A *ᵥ Fin.init z + B *ᵥ u + z (Fin.last n) • b ∈ K.cone) ∧ 0 ≤ z (Fin.last n)} := by
  let A0 : Matrix K.Idx (Fin (n + 1)) ℝ := fun y c => Fin.lastCases (b y) (fun c' => A y c') c
  let A2 : Matrix (g70mc2_ext K).Idx (Fin (n + 1)) ℝ := fun x c =>
    Fin.cases (motive := fun j => Fin ((g70mc2_ext K).d j + 1) → ℝ)
      (fun i => if i.val = 1 then (if c = Fin.last n then 1 else 0) else 0)
      (fun j i => A0 ⟨j, i⟩ c) x.1 x.2
  let B2 : Matrix (g70mc2_ext K).Idx (Fin p) ℝ := fun x c =>
    Fin.cases (motive := fun j => Fin ((g70mc2_ext K).d j + 1) → ℝ)
      (fun _ => 0) (fun j i => B ⟨j, i⟩ c) x.1 x.2
  refine ⟨g70mc2_ext K, p, A2, B2, 0, ?_⟩
  ext z
  simp only [cqrSet, Set.mem_setOf_eq, add_zero]
  have hA0 : A0 *ᵥ z = A *ᵥ Fin.init z + z (Fin.last n) • b := by
    ext y
    simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, A0, Fin.lastCases_castSucc,
      Fin.lastCases_last, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.init]
    ring
  have hr : ∀ u : Fin p → ℝ, (fun y : K.Idx => (A2 *ᵥ z + B2 *ᵥ u) ⟨y.1.succ, y.2⟩) =
      A0 *ᵥ z + B *ᵥ u := by
    intro u; ext y; rfl
  have h00 : ∀ u : Fin p → ℝ, (A2 *ᵥ z + B2 *ᵥ u) ⟨0, 0⟩ = 0 := by
    intro u
    simp only [Pi.add_apply, mulVec, dotProduct, A2, B2, Fin.cases_zero]
    simp
  have h01 : ∀ u : Fin p → ℝ, (A2 *ᵥ z + B2 *ᵥ u) ⟨0, Fin.last 1⟩ = z (Fin.last n) := by
    intro u
    simp only [Pi.add_apply, mulVec, dotProduct, A2, B2, Fin.cases_zero]
    simp
  constructor
  · rintro ⟨⟨u, hu⟩, ht⟩
    refine ⟨u, (g70mc2_ext_mem K _).mpr ⟨?_, ?_⟩⟩
    · rw [hr, hA0]; convert hu using 1; abel
    · rw [h00, h01]; simpa using ht
  · rintro ⟨u, hu⟩
    obtain ⟨h1, h2⟩ := (g70mc2_ext_mem K _).mp hu
    rw [hr, hA0] at h1
    rw [h00, h01] at h2
    refine ⟨⟨u, by convert h1 using 1; abel⟩, by simpa using h2⟩

theorem g70mc2_A0 {n : ℕ} (K : IceCreamProduct) (A : Matrix K.Idx (Fin n) ℝ) (b : K.Idx → ℝ)
    (z : Fin (n + 1) → ℝ) :
    (fun y c => Fin.lastCases (b y) (fun c' => A y c') c : Matrix K.Idx (Fin (n + 1)) ℝ) *ᵥ z =
      A *ᵥ Fin.init z + z (Fin.last n) • b := by
  ext y
  simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.lastCases_castSucc,
    Fin.lastCases_last, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.init]
  ring

theorem g70mc2_zero_mem (K : IceCreamProduct) : (0 : K.Idx → ℝ) ∈ K.cone := fun j => by simp

theorem solution {n p : ℕ} (K : IceCreamProduct) (A : Matrix K.Idx (Fin n) ℝ)
    (B : Matrix K.Idx (Fin p) ℝ) (b : K.Idx → ℝ) (X : Set (Fin n → ℝ))
    (hX : X = cqrSet K A B b) (hne : X.Nonempty) :
    let Xt : Set (Fin (n + 1) → ℝ) :=
      {z | (∃ u : Fin p → ℝ, A *ᵥ Fin.init z + B *ᵥ u + z (Fin.last n) • b ∈ K.cone) ∧
        0 ≤ z (Fin.last n)}
    (conicHull X ⊆ Xt ∧ Xt ⊆ closure (conicHull X) ∧
        (IsClosed X → Bornology.IsBounded X → IsCQr (conicHull X))) ∧
      ((∀ u : Fin p → ℝ, B *ᵥ u ∈ K.cone → B *ᵥ u = 0) →
        Xt = closure (conicHull X) ∧ IsCQr (closure (conicHull X))) := by
  intro Xt
  have hXt_cqr : IsCQr Xt := g70mc2_Xt_cqr K A B b
  subst hX
  obtain ⟨x0, u0, hx0⟩ := hne
  have pos_mem : ∀ z ∈ Xt, 0 < z (Fin.last n) → z ∈ conicHull (cqrSet K A B b) := by
    rintro z ⟨⟨u, hu⟩, -⟩ ht
    refine Or.inl ⟨ht, (z (Fin.last n))⁻¹ • u, ?_⟩
    have := g70mc2_cone_smul K (z (Fin.last n))⁻¹ (inv_nonneg.mpr ht.le) _ hu
    convert this using 1
    simp only [mulVec_smul, smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  have sub1 : conicHull (cqrSet K A B b) ⊆ Xt := by
    rintro z (⟨ht, u, hu⟩ | hz0)
    · refine ⟨⟨z (Fin.last n) • u, ?_⟩, ht.le⟩
      have := g70mc2_cone_smul K (z (Fin.last n)) ht.le _ hu
      convert this using 1
      simp only [mulVec_smul, smul_add, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    · rw [Set.mem_singleton_iff] at hz0
      subst hz0
      refine ⟨⟨0, ?_⟩, le_rfl⟩
      have : Fin.init (0 : Fin (n + 1) → ℝ) = 0 := rfl
      simpa [this] using g70mc2_zero_mem K
  have zero_case : ∀ z ∈ Xt, z (Fin.last n) = 0 →
      ∃ u, A *ᵥ Fin.init z + B *ᵥ u ∈ K.cone := by
    rintro z ⟨⟨u, hu⟩, -⟩ h0
    rw [h0, zero_smul, add_zero] at hu
    exact ⟨u, hu⟩
  have sub2 : Xt ⊆ closure (conicHull (cqrSet K A B b)) := by
    intro z hz
    rcases hz.2.lt_or_eq with htpos | ht0
    · exact subset_closure (pos_mem z hz htpos)
    obtain ⟨u, hu⟩ := zero_case z hz ht0.symm
    let w : Fin (n + 1) → ℝ := Fin.snoc x0 1
    have hlim : Filter.Tendsto (fun k : ℕ => z + (1 / ((k : ℝ) + 1)) • w) Filter.atTop
        (nhds z) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const w
      simpa using (tendsto_const_nhds (x := z)).add this
    refine mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun k => ?_)
    set ε : ℝ := 1 / ((k : ℝ) + 1) with hε
    have hεp : 0 < ε := by positivity
    have hlast : (z + ε • w) (Fin.last n) = ε := by
      simp [w, ← ht0]
    have hinit : Fin.init (z + ε • w) = Fin.init z + ε • x0 := by
      ext i; simp [Fin.init, w]
    refine Or.inl ⟨by rw [hlast]; exact hεp, ε⁻¹ • u + u0, ?_⟩
    rw [hlast, hinit]
    have := g70mc2_cone_add K _ _ (g70mc2_cone_smul K ε⁻¹ (inv_nonneg.mpr hεp.le) _ hu) hx0
    convert this using 1
    simp only [smul_add, smul_smul, inv_mul_cancel₀ hεp.ne', one_smul, mulVec_add, mulVec_smul]
    abel
  refine ⟨⟨sub1, sub2, fun _ hbdd => ?_⟩, fun hB => ?_⟩
  · have heq : conicHull (cqrSet K A B b) = Xt := by
      refine le_antisymm sub1 fun z hz => ?_
      rcases hz.2.lt_or_eq with htpos | ht0
      · exact pos_mem z hz htpos
      right
      obtain ⟨u, hu⟩ := zero_case z hz ht0.symm
      have hx : Fin.init z = 0 := by
        by_contra hne
        obtain ⟨R, hR⟩ := hbdd.exists_norm_le
        have hn : 0 < ‖Fin.init z‖ := norm_pos_iff.mpr hne
        set s : ℝ := (R + ‖x0‖ + 1) / ‖Fin.init z‖
        have hs : 0 ≤ s := by
          have := (norm_nonneg x0).trans (hR x0 ⟨u0, hx0⟩)
          positivity
        have hmem : x0 + s • Fin.init z ∈ cqrSet K A B b := by
          refine ⟨u0 + s • u, ?_⟩
          have := g70mc2_cone_add K _ _ hx0 (g70mc2_cone_smul K s hs _ hu)
          convert this using 1
          simp only [mulVec_add, mulVec_smul, smul_add]; abel
        have h1 := hR _ hmem
        have h2 : ‖s • Fin.init z‖ ≤ ‖x0 + s • Fin.init z‖ + ‖x0‖ := by
          calc ‖s • Fin.init z‖ = ‖(x0 + s • Fin.init z) - x0‖ := by simp
            _ ≤ _ := norm_sub_le _ _
        rw [norm_smul, Real.norm_of_nonneg hs, div_mul_cancel₀ _ hn.ne'] at h2
        linarith
      rw [Set.mem_singleton_iff]
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using ht0.symm
      · simpa [Fin.init] using congrFun hx j
    rw [heq]; exact hXt_cqr
  · have hclosed : IsClosed Xt := by
      have : Xt = cqrSet K (fun y c => Fin.lastCases (b y) (fun c' => A y c') c) B 0 ∩
          {z | 0 ≤ z (Fin.last n)} := by
        ext z
        simp only [Xt, cqrSet, Set.mem_inter_iff, Set.mem_setOf_eq, g70mc2_A0, add_zero]
        constructor
        · rintro ⟨⟨u, hu⟩, ht⟩; exact ⟨⟨u, by convert hu using 1; abel⟩, ht⟩
        · rintro ⟨⟨u, hu⟩, ht⟩; exact ⟨⟨u, by convert hu using 1; abel⟩, ht⟩
      rw [this]
      exact (g70mc2_closed K _ B 0 hB).inter (isClosed_le continuous_const (continuous_apply _))
    have heq : Xt = closure (conicHull (cqrSet K A B b)) :=
      le_antisymm sub2 (closure_minimal sub1 hclosed)
    exact ⟨heq, heq ▸ hXt_cqr⟩
