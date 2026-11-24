-- Prove2me | solution 1 for L1ResistanceCount.Counting.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T20:36:42.820671+00:00
-- url     : https://prove2.me/submissions/c18eccf3-f322-4842-a7cb-823508bb051a

import Mathlib
import Definitions.Def_L1ResistanceCount_Counting_Obstacle

open scoped InnerProductSpace

theorem pinv_apply_of_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (y : E)
    (hy : y ∈ (LinearMap.ker T)ᗮ) :
    T (HarmonicGames.Decomposition.pinv T y) = y := by
  have hr : y ∈ LinearMap.range T := by
    have h1 := hT.orthogonal_range
    rw [← h1, Submodule.orthogonal_orthogonal] at hy
    exact hy
  obtain ⟨v, rfl⟩ := hr
  set K := LinearMap.ker T
  set u : E := v - K.starProjection v with hu
  have huK : u ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have hTu : T u = T v := by
    have : T (K.starProjection v) = 0 := Submodule.starProjection_apply_mem K v
    simp [hu, this]
  set S := LinearMap.range (T ∘ₗ Kᗮ.subtype)
  have hmem : T v ∈ S := ⟨⟨u, huK⟩, by simpa using hTu⟩
  unfold HarmonicGames.Decomposition.pinv
  have hp : S.orthogonalProjectionOnto (T v) = ⟨T v, hmem⟩ := by
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨T v, hmem⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  have h2 : (LinearEquiv.ofInjective (T ∘ₗ Kᗮ.subtype) (HarmonicGames.Decomposition.pinv_restrict_injective T)).symm ⟨T v, hmem⟩ = ⟨u, huK⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext (by simpa using hTu.symm)
  erw [hp, h2]
  simpa using hTu

open EffResSparsify.Sampling Matrix

theorem form_eq {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (z y : V → ℝ) :
    z ⬝ᵥ (G.laplacian *ᵥ y) = ∑ f, G.w f * (G.incidence *ᵥ z) f * (G.incidence *ᵥ y) f := by
  unfold WGraph.laplacian WGraph.weightMatrix
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, dotProduct]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp [Matrix.mulVec_diagonal]
  ring

theorem effRes_eq {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (e : E) :
    G.effRes e = (G.incidence e) ⬝ᵥ (G.lapPinv *ᵥ (G.incidence e)) := by
  unfold WGraph.effRes
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  exact (Matrix.dotProduct_mulVec _ _ _).symm

theorem inner_eq_dot {V : Type*} [Fintype V] (u v : EuclideanSpace ℝ V) :
    inner ℝ u v = (WithLp.ofLp u) ⬝ᵥ (WithLp.ofLp v) := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

theorem T_apply {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℝ)
    (v : EuclideanSpace ℝ V) :
    (Matrix.toEuclideanLin M v).ofLp = M *ᵥ v.ofLp := by
  simp [Matrix.toEuclideanLin_apply]


theorem inc_mulVec {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (z : V → ℝ) (e : E) :
    (G.incidence *ᵥ z) e = z (G.head e) - z (G.tail e) := by
  have hne := G.head_ne_tail e
  have : ∀ v, G.incidence e v * z v = (if v = G.head e then z v else 0) - (if v = G.tail e then z v else 0) := by
    intro v
    unfold WGraph.incidence
    by_cases h1 : v = G.head e
    · subst h1; simp [hne]
    · by_cases h2 : v = G.tail e
      · subst h2; simp [h1, Ne.symm hne]
      · simp [h1, h2]
  simp only [Matrix.mulVec, dotProduct, this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem lap_apply {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (z : V → ℝ) (s : V) :
    (G.laplacian *ᵥ z) s = ∑ e, G.w e * G.incidence e s * (z (G.head e) - z (G.tail e)) := by
  unfold WGraph.laplacian WGraph.weightMatrix
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [Matrix.mulVec_diagonal, inc_mulVec]
  ring

theorem quad_zero {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (u : V → ℝ) (h : u ⬝ᵥ (G.laplacian *ᵥ u) = 0) (e : E) :
    u (G.head e) = u (G.tail e) := by
  rw [form_eq] at h
  have h2 : ∀ f ∈ Finset.univ, 0 ≤ G.w f * (G.incidence *ᵥ u) f * (G.incidence *ᵥ u) f :=
    fun f _ => by
      have := G.w_pos f
      nlinarith [sq_nonneg ((G.incidence *ᵥ u) f)]
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg h2).1 h e (Finset.mem_univ e)
  have := G.w_pos e
  have h5 : G.w e * ((G.incidence *ᵥ u) e) ^ 2 = 0 := by rw [← h3]; ring
  rcases mul_eq_zero.1 h5 with h | h
  · linarith
  · have := pow_eq_zero_iff (by norm_num) |>.1 h
    rw [inc_mulVec] at this; linarith

theorem lap_one {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (k : ℝ) : G.laplacian *ᵥ (fun _ => k) = 0 := by
  ext s; rw [lap_apply]; simp

theorem const_of_ker {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (hG : G.IsConnected) (u : V → ℝ) (hu : G.laplacian *ᵥ u = 0) (a b : V) :
    u a = u b := by
  have h0 : u ⬝ᵥ (G.laplacian *ᵥ u) = 0 := by rw [hu]; simp
  have hq := quad_zero G u h0
  have hr : G.toSimpleGraph.Reachable a b := hG.preconnected a b
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons h _ ih =>
    rw [← ih]
    simp only [WGraph.toSimpleGraph, SimpleGraph.fromRel_adj] at h
    rcases h.2 with ⟨e, h1, h2⟩ | ⟨e, h1, h2⟩
    · rw [← h1, ← h2]; exact hq e
    · rw [← h1, ← h2]; exact (hq e).symm

theorem lap_symm {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) : (Matrix.toEuclideanLin G.laplacian).IsSymmetric := by
  intro u v
  rw [inner_eq_dot, inner_eq_dot, T_apply, T_apply, dotProduct_comm, form_eq, form_eq]
  exact Finset.sum_congr rfl fun f _ => by ring

theorem pinv_facts {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (hG : G.IsConnected) (c : V → ℝ) (hc : ∑ v, c v = 0) :
    G.laplacian *ᵥ (G.lapPinv *ᵥ c) = c ∧ ∑ v, (G.lapPinv *ᵥ c) v = 0 := by
  set T := Matrix.toEuclideanLin G.laplacian with hTdef
  have hsym := lap_symm G
  have hy : WithLp.toLp 2 c ∈ (LinearMap.ker T)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have h0 : G.laplacian *ᵥ u.ofLp = 0 := by
      have := congrArg WithLp.ofLp hu
      rwa [hTdef, T_apply] at this
    obtain ⟨v0⟩ := hG.nonempty
    have : ∀ v, u.ofLp v = u.ofLp v0 := fun v => const_of_ker G hG _ h0 v v0
    rw [inner_eq_dot]
    simp only [dotProduct, this]
    rw [← Finset.mul_sum, hc, mul_zero]
  have hP : (Matrix.toEuclideanLin G.lapPinv) = HarmonicGames.Decomposition.pinv T := by
    unfold WGraph.lapPinv
    simp [hTdef]
  have h6 : (HarmonicGames.Decomposition.pinv T (WithLp.toLp 2 c)).ofLp = G.lapPinv *ᵥ c := by
    rw [← hP, T_apply]
  constructor
  · have := pinv_apply_of_mem T hsym _ hy
    have h5 := congrArg WithLp.ofLp this
    rw [hTdef, T_apply, h6] at h5
    simpa using h5
  · have hm : HarmonicGames.Decomposition.pinv T (WithLp.toLp 2 c) ∈ (LinearMap.ker T)ᗮ := by
      unfold HarmonicGames.Decomposition.pinv
      simp only [LinearMap.coe_comp, Function.comp_apply]
      exact Subtype.property _
    rw [Submodule.mem_orthogonal] at hm
    have h1 : WithLp.toLp 2 (fun _ : V => (1:ℝ)) ∈ LinearMap.ker T := by
      rw [LinearMap.mem_ker, hTdef]
      apply WithLp.ofLp_injective
      rw [T_apply]; exact lap_one G 1
    have := hm _ h1
    rw [inner_eq_dot, h6] at this
    simpa [dotProduct] using this

theorem trace_sum {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (hG : G.IsConnected) :
    ∑ e, G.w e * G.effRes e = (Fintype.card V : ℝ) - 1 := by
  have h1 : ∑ e, G.w e * G.effRes e = Matrix.trace (G.lapPinv * G.laplacian) := by
    have : Matrix.trace (G.weightMatrix * (G.incidence * G.lapPinv * G.incidenceᵀ))
        = Matrix.trace (G.lapPinv * G.laplacian) := by
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm G.incidence]
      unfold WGraph.laplacian
      simp only [Matrix.mul_assoc]
    rw [← this]
    simp [Matrix.trace, WGraph.weightMatrix, WGraph.effRes, Matrix.diagonal_mul]
  have h2 : ∀ u : V, (G.lapPinv * G.laplacian) u u = 1 - 1 / (Fintype.card V : ℝ) := by
    intro u
    set e : V → ℝ := Pi.single u 1 with hedef
    set c : V → ℝ := G.laplacian *ᵥ e with hcdef
    have hc : ∑ v, c v = 0 := by
      have := form_eq G (fun _ => (1:ℝ)) e
      simp only [inc_mulVec, sub_self, mul_zero, zero_mul, Finset.sum_const_zero] at this
      simpa [dotProduct, hcdef] using this
    obtain ⟨hL, hs⟩ := pinv_facts G hG c hc
    set y := G.lapPinv *ᵥ c with hydef
    have hk : ∀ a b, y a - e a = y b - e b := by
      intro a b
      apply const_of_ker G hG (y - e)
      rw [Matrix.mulVec_sub, hL]; simp [hcdef]
    have hy : ∀ b, y b = e b + (y u - 1) := by
      intro b
      have := hk b u
      have he : e u = 1 := by simp [hedef]
      linarith
    have hn : (Fintype.card V : ℝ) ≠ 0 := by
      haveI := hG.nonempty
      exact Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have hsum : ∑ b, y b = 1 + (Fintype.card V : ℝ) * (y u - 1) := by
      obtain ⟨k, hkk⟩ : ∃ k, k = y u - 1 := ⟨_, rfl⟩
      rw [← hkk]
      have : ∀ b ∈ Finset.univ, y b = e b + k := fun b _ => by rw [hy b, hkk]
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
      simp [hedef]
    have hyu : y u = 1 - 1 / (Fintype.card V : ℝ) := by
      rw [hsum] at hs
      field_simp
      field_simp at hs
      linarith
    have : (G.lapPinv * G.laplacian) u u = y u := by
      have h3 : (G.lapPinv * G.laplacian) *ᵥ e = y := by
        rw [← Matrix.mulVec_mulVec]
      rw [← h3]
      simp [Matrix.mulVec, dotProduct, hedef, Pi.single_apply]
    rw [this, hyu]
  have hn : (Fintype.card V : ℝ) ≠ 0 := by
    haveI := hG.nonempty
    exact Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [h1, Matrix.trace]
  simp only [Matrix.diag, h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

open L1ResistanceCount.Counting

theorem lap_dot_comm {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (x y : V → ℝ) : x ⬝ᵥ (G.laplacian *ᵥ y) = y ⬝ᵥ (G.laplacian *ᵥ x) := by
  rw [form_eq, form_eq]
  exact Finset.sum_congr rfl fun f _ => by ring

theorem obj_expand {n m : ℕ} (G : WeightedGraph n m) (lam : ℝ) (s : Fin n) (z u : Vector n) (t : ℝ) :
    obstacleObjective G lam s (z + t • u) = obstacleObjective G lam s z
      + t * (u ⬝ᵥ (G.laplacian *ᵥ z) - u s + lam * ∑ v, u v)
      + t ^ 2 * quadratic G.laplacian u / 2 := by
  have hc := lap_dot_comm G z u
  unfold obstacleObjective quadratic dot
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  change (z + t • u) ⬝ᵥ (G.laplacian *ᵥ z + t • G.laplacian *ᵥ u) / 2 - _ + _ = _
  simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  change _ = z ⬝ᵥ (G.laplacian *ᵥ z) / 2 - z s + lam * ∑ v, z v + t * (u ⬝ᵥ (G.laplacian *ᵥ z) - u s + lam * ∑ v, u v) + t ^ 2 * (u ⬝ᵥ (G.laplacian *ᵥ u)) / 2
  rw [hc]; ring

theorem quad_nonneg {n m : ℕ} (G : WeightedGraph n m) (u : Vector n) : 0 ≤ quadratic G.laplacian u := by
  unfold quadratic dot
  change 0 ≤ u ⬝ᵥ (G.laplacian *ᵥ u)
  rw [form_eq]
  refine Finset.sum_nonneg fun f _ => ?_
  have := G.w_pos f
  nlinarith [sq_nonneg ((G.incidence *ᵥ u) f)]

theorem descent (a Q T : ℝ) (hQ : 0 ≤ Q) (hT : 0 < T)
    (h : ∀ t, 0 < t → t ≤ T → 0 ≤ t * a + t ^ 2 * Q / 2) : 0 ≤ a := by
  by_contra hneg
  push_neg at hneg
  set t := min T (-a / (Q + 1)) with ht
  have h1 : 0 < t := lt_min hT (div_pos (by linarith) (by linarith))
  have h2 : t ≤ T := min_le_left _ _
  have h3 : t ≤ -a / (Q + 1) := min_le_right _ _
  have h4 : t * (Q + 1) ≤ -a := by
    rwa [le_div_iff₀ (by linarith)] at h3
  have := h t h1 h2
  nlinarith [mul_pos h1 h1]

theorem lap_nonpos {n m : ℕ} (G : WeightedGraph n m) (s : Fin n) (z : Vector n)
    (hnn : nonnegative z) (hs : z s = 0) : (G.laplacian *ᵥ z) s ≤ 0 := by
  rw [lap_apply]
  refine Finset.sum_nonpos fun e _ => ?_
  have hw := G.w_pos e
  unfold WGraph.incidence
  by_cases h1 : s = G.head e
  · subst h1
    have := hnn (G.tail e)
    simp [hs]
    nlinarith
  · by_cases h2 : s = G.tail e
    · subst h2
      have := hnn (G.head e)
      simp [hs, h1]
      nlinarith
    · simp [h1, h2]

theorem kkt_s {n m : ℕ} (G : WeightedGraph n m) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) (s : Fin n)
    (z : Vector n) (hz : IsObstacleMinimizer G lam s z) :
    (G.laplacian *ᵥ z) s = 1 - lam := by
  obtain ⟨hnn, hmin⟩ := hz
  have hexp : ∀ (v : Fin n) (t : ℝ),
      obstacleObjective G lam s (z + t • Pi.single v 1)
        = obstacleObjective G lam s z
          + t * ((G.laplacian *ᵥ z) v - (if v = s then 1 else 0) + lam)
          + t ^ 2 * quadratic G.laplacian (Pi.single v 1) / 2 := by
    intro v t
    rw [obj_expand]
    have : (Pi.single v (1:ℝ) : Vector n) ⬝ᵥ (G.laplacian *ᵥ z) = (G.laplacian *ᵥ z) v := by
      simp [dotProduct_single]
    rw [this]
    simp only [Pi.single_apply, eq_comm (a := s)]
    simp
  have hpos : ∀ v, 0 ≤ (G.laplacian *ᵥ z) v - (if v = s then 1 else 0) + lam := by
    intro v
    refine descent _ (quadratic G.laplacian (Pi.single v 1)) 1 (quad_nonneg G _) one_pos ?_
    intro t ht _
    have hy : nonnegative (z + t • (Pi.single v 1 : Vector n)) := by
      intro w
      have := hnn w
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      split_ifs <;> nlinarith
    have := hmin _ hy
    rw [hexp] at this
    linarith
  have hneg : ∀ v, 0 < z v → (G.laplacian *ᵥ z) v - (if v = s then 1 else 0) + lam ≤ 0 := by
    intro v hv
    have : 0 ≤ -((G.laplacian *ᵥ z) v - (if v = s then 1 else 0) + lam) := by
      refine descent _ (quadratic G.laplacian (Pi.single v 1)) (z v) (quad_nonneg G _) hv ?_
      intro t ht htz
      have hy : nonnegative (z + (-t) • (Pi.single v 1 : Vector n)) := by
        intro w
        have := hnn w
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        split_ifs with hw
        · subst hw; linarith
        · linarith
      have := hmin _ hy
      rw [hexp] at this
      nlinarith
    linarith
  have hzs : 0 < z s := by
    rcases (hnn s).lt_or_eq with h | h
    · exact h
    · exfalso
      have := lap_nonpos G s z hnn h.symm
      have := hpos s
      simp at this
      linarith
  have := hneg s hzs
  have := hpos s
  simp at *
  linarith

theorem quad_const {n m : ℕ} (G : WeightedGraph n m) (hG : G.IsConnected) (u : Vector n)
    (h : quadratic G.laplacian u = 0) (a b : Fin n) : u a = u b := by
  unfold quadratic dot at h
  have hq := quad_zero G u h
  have hr : G.toSimpleGraph.Reachable a b := hG.preconnected a b
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons h _ ih =>
    rw [← ih]
    simp only [WGraph.toSimpleGraph, SimpleGraph.fromRel_adj] at h
    rcases h.2 with ⟨e, h1, h2⟩ | ⟨e, h1, h2⟩
    · rw [← h1, ← h2]; exact hq e
    · rw [← h1, ← h2]; exact (hq e).symm

theorem quad_smul {n m : ℕ} (G : WeightedGraph n m) (c : ℝ) (x : Vector n) :
    quadratic G.laplacian (c • x) = c ^ 2 * quadratic G.laplacian x := by
  unfold quadratic dot
  change (c • x) ⬝ᵥ (G.laplacian *ᵥ (c • x)) = c ^ 2 * (x ⬝ᵥ (G.laplacian *ᵥ x))
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
  simp only [smul_eq_mul]; ring

theorem unique_min {n m : ℕ} (G : WeightedGraph n m) (hG : G.IsConnected)
    (lam : ℝ) (hlam : 1 / (n : ℝ) < lam) (s : Fin n) (z1 z2 : Vector n)
    (h1 : IsObstacleMinimizer G lam s z1) (h2 : IsObstacleMinimizer G lam s z2) : z1 = z2 := by
  haveI := hG.nonempty
  have hn : (0:ℝ) < n := by
    have : 0 < Fintype.card (Fin n) := Fintype.card_pos_iff.2 ‹Nonempty (Fin n)›
    simpa using this
  have hl : 1 < lam * n := by
    have := mul_lt_mul_of_pos_right hlam hn
    rwa [one_div, inv_mul_cancel₀ hn.ne'] at this
  obtain ⟨hn1, hm1⟩ := h1
  obtain ⟨hn2, hm2⟩ := h2
  set u : Vector n := z2 - z1 with hu
  set A := u ⬝ᵥ (G.laplacian *ᵥ z1) - u s + lam * ∑ v, u v with hA
  set Q := quadratic G.laplacian u with hQ
  have hQ0 := quad_nonneg G u
  have e1 : obstacleObjective G lam s z2 = obstacleObjective G lam s z1 + A + Q / 2 := by
    have := obj_expand G lam s z1 u 1
    have h' : z1 + (1:ℝ) • u = z2 := by simp [hu]
    rw [h'] at this
    rw [this]; ring
  have hmid : nonnegative (z1 + (1/2 : ℝ) • u) := by
    intro v
    have := hn1 v; have := hn2 v
    simp only [hu, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linarith
  have e2 := obj_expand G lam s z1 u (1/2)
  have l1 := hm1 _ hmid
  have l2 := hm1 _ hn2
  have l3 := hm2 _ hn1
  have hQz : Q = 0 := by nlinarith
  have hc := quad_const G hG u hQz
  have hsum : ∑ v, u v = n * u s := by
    simp [Finset.sum_congr rfl fun v _ => hc v s]
  have hLz : u ⬝ᵥ (G.laplacian *ᵥ z1) = 0 := by
    have : u = fun _ => u s := funext fun v => hc v s
    rw [lap_dot_comm, this, lap_one]; simp
  have hA0 : A = 0 := by nlinarith
  have : u s * (lam * n - 1) = 0 := by
    rw [hA, hLz, hsum] at hA0; linarith
  have hus : u s = 0 := by
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith
  funext v
  have := hc v s
  have : z2 v - z1 v = 0 := by
    have h3 : u v = 0 := by rw [hc v s, hus]
    simpa [hu] using h3
  linarith

theorem exists_min {n m : ℕ} (G : WeightedGraph n m) (hG : G.IsConnected)
    (lam : ℝ) (hlam : 1 / (n : ℝ) < lam) (s : Fin n) :
    ∃ z, IsObstacleMinimizer G lam s z := by
  haveI := hG.nonempty
  have hn : (0:ℝ) < n := by
    have : 0 < Fintype.card (Fin n) := Fintype.card_pos_iff.2 ‹Nonempty (Fin n)›
    simpa using this
  have hcont : Continuous (obstacleObjective G lam s) := by
    unfold obstacleObjective quadratic dot
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hcontq : Continuous (quadratic G.laplacian) := by
    unfold quadratic dot
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hf0 : obstacleObjective G lam s 0 = 0 := by
    simp [obstacleObjective, quadratic, dot]
  have hclnn : IsClosed {x : Vector n | nonnegative x} := by
    have : {x : Vector n | nonnegative x} = ⋂ v, {x : Vector n | 0 ≤ x v} := by
      ext x; simp [nonnegative]
    rw [this]
    exact isClosed_iInter fun v => isClosed_le continuous_const (continuous_apply v)
  have hclsum : IsClosed {x : Vector n | ∑ v, x v = 1} :=
    isClosed_eq (continuous_finset_sum _ fun v _ => continuous_apply v) continuous_const
  have hcls : IsClosed {x : Vector n | lam ≤ x s} :=
    isClosed_le continuous_const (continuous_apply s)
  set K : Set (Vector n) := {x | nonnegative x} ∩ {x | ∑ v, x v = 1} ∩ {x | lam ≤ x s} with hK
  have hKsub : K ⊆ Set.Icc (0 : Vector n) (fun _ => 1) := by
    intro x hx
    obtain ⟨⟨h1, h2⟩, _⟩ := hx
    refine ⟨fun v => h1 v, fun v => ?_⟩
    have : x v ≤ ∑ w, x w :=
      Finset.single_le_sum (f := fun w => x w) (fun w _ => h1 w) (Finset.mem_univ v)
    simp only [Set.mem_setOf_eq] at h2
    linarith
  have hKc : IsCompact K :=
    (isCompact_Icc (a := (0 : Vector n)) (b := fun _ => 1)).of_isClosed_subset
      ((hclnn.inter hclsum).inter hcls) hKsub
  have hpos : ∀ x ∈ K, 0 < quadratic G.laplacian x := by
    intro x hx
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    simp only [Set.mem_setOf_eq] at h2 h3
    rcases (quad_nonneg G x).lt_or_eq with h | h
    · exact h
    · exfalso
      have hc := quad_const G hG x h.symm
      have : ∑ v, x v = n * x s := by simp [Finset.sum_congr rfl fun v _ => hc v s]
      have h4 : x s = 1 / n := by field_simp; linarith
      linarith
  obtain ⟨ε, hε, hεK⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ε ≤ quadratic G.laplacian x := by
    rcases K.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨x0, hx0, hmin⟩ := hKc.exists_isMinOn h hcontq.continuousOn
      exact ⟨_, hpos x0 hx0, fun x hx => hmin hx⟩
  have hbound : ∀ z : Vector n, nonnegative z → obstacleObjective G lam s z ≤ 0 →
      ∑ v, z v ≤ 2 / ε := by
    intro z hz hfz
    set T := ∑ v, z v with hT
    have hT0 : 0 ≤ T := Finset.sum_nonneg fun v _ => hz v
    rcases hT0.lt_or_eq with hTp | hTz
    · set x : Vector n := T⁻¹ • z with hx
      have hxnn : nonnegative x := fun v => by
        simp only [hx, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hT0) (hz v)
      have hxsum : ∑ v, x v = 1 := by
        simp only [hx, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        rw [← hT]; exact inv_mul_cancel₀ hTp.ne'
      have hzx : z = T • x := by
        simp only [hx, smul_smul, mul_inv_cancel₀ hTp.ne', one_smul]
      have hxs : x s ≤ 1 := by
        have : x s ≤ ∑ w, x w :=
          Finset.single_le_sum (f := fun w => x w) (fun w _ => hxnn w) (Finset.mem_univ s)
        linarith
      have hfz' : T ^ 2 * quadratic G.laplacian x / 2 - T * x s + lam * T ≤ 0 := by
        have := hfz
        unfold obstacleObjective at this
        rw [hzx, quad_smul] at this
        simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hxsum] at this
        nlinarith
      have hq0 := quad_nonneg G x
      by_cases hxs' : lam ≤ x s
      · have hxK : x ∈ K := ⟨⟨hxnn, hxsum⟩, hxs'⟩
        have h5 := hεK x hxK
        have h6 : T * quadratic G.laplacian x / 2 ≤ x s - lam := by
          by_contra hcon
          push_neg at hcon
          nlinarith
        rw [le_div_iff₀ hε]
        have h7 := mul_le_mul_of_nonneg_left h5 hT0
        have hl0 : 0 < lam := lt_trans (by positivity) hlam
        linarith
      · push_neg at hxs'
        exfalso
        have : T * quadratic G.laplacian x / 2 ≤ x s - lam := by
          by_contra hcon
          push_neg at hcon
          nlinarith
        nlinarith [mul_nonneg hT0 hq0]
    · rw [← hTz]; positivity
  set M := 2 / ε with hM
  set S : Set (Vector n) := {x | nonnegative x} ∩ {x | obstacleObjective G lam s x ≤ 0} with hS
  have hSsub : S ⊆ Set.Icc (0 : Vector n) (fun _ => M) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hx
    refine ⟨fun v => h1 v, fun v => ?_⟩
    have : x v ≤ ∑ w, x w :=
      Finset.single_le_sum (f := fun w => x w) (fun w _ => h1 w) (Finset.mem_univ v)
    exact this.trans (hbound x h1 h2)
  have hSc : IsCompact S :=
    (isCompact_Icc (a := (0 : Vector n)) (b := fun _ => M)).of_isClosed_subset
      (hclnn.inter (isClosed_le hcont continuous_const)) hSsub
  have h0S : (0 : Vector n) ∈ S := ⟨fun v => le_refl _, by simp [hf0]⟩
  obtain ⟨z0, hz0, hmin⟩ := hSc.exists_isMinOn ⟨0, h0S⟩ hcont.continuousOn
  refine ⟨z0, hz0.1, fun y hy => ?_⟩
  by_cases hyS : obstacleObjective G lam s y ≤ 0
  · exact hmin ⟨hy, hyS⟩
  · push_neg at hyS
    have := hmin h0S
    simp only [Set.mem_setOf_eq] at this
    rw [hf0] at this
    linarith

theorem exists_unique_min {n m : ℕ} (G : WeightedGraph n m) (hG : G.IsConnected)
    (lam : ℝ) (hlam : 1 / (n : ℝ) < lam) (s : Fin n) :
    ∃! z, IsObstacleMinimizer G lam s z := by
  obtain ⟨z, hz⟩ := exists_min G hG lam hlam s
  exact ⟨z, hz, fun y hy => unique_min G hG lam hlam s y z hy hz⟩


theorem kkt_bounds {n m : ℕ} (G : WeightedGraph n m) (lam : ℝ) (s : Fin n)
    (z : Vector n) (hz : IsObstacleMinimizer G lam s z) :
    (∀ v, (unitVector s - G.laplacian *ᵥ z) v ≤ lam) ∧
    (∀ v, 0 < z v → (unitVector s - G.laplacian *ᵥ z) v = lam) := by
  obtain ⟨hnn, hmin⟩ := hz
  have hexp : ∀ (v : Fin n) (t : ℝ),
      obstacleObjective G lam s (z + t • Pi.single v 1)
        = obstacleObjective G lam s z
          + t * ((G.laplacian *ᵥ z) v - (if v = s then 1 else 0) + lam)
          + t ^ 2 * quadratic G.laplacian (Pi.single v 1) / 2 := by
    intro v t
    rw [obj_expand]
    have : (Pi.single v (1:ℝ) : Vector n) ⬝ᵥ (G.laplacian *ᵥ z) = (G.laplacian *ᵥ z) v := by
      simp [dotProduct_single]
    rw [this]
    simp only [Pi.single_apply, eq_comm (a := s)]
    simp
  have hpos : ∀ v, 0 ≤ (G.laplacian *ᵥ z) v - (if v = s then 1 else 0) + lam := by
    intro v
    refine descent _ (quadratic G.laplacian (Pi.single v 1)) 1 (quad_nonneg G _) one_pos ?_
    intro t ht _
    have hy : nonnegative (z + t • (Pi.single v 1 : Vector n)) := by
      intro w
      have := hnn w
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      split_ifs <;> nlinarith
    have := hmin _ hy
    rw [hexp] at this
    linarith
  have hneg : ∀ v, 0 < z v → (G.laplacian *ᵥ z) v - (if v = s then 1 else 0) + lam ≤ 0 := by
    intro v hv
    have : 0 ≤ -((G.laplacian *ᵥ z) v - (if v = s then 1 else 0) + lam) := by
      refine descent _ (quadratic G.laplacian (Pi.single v 1)) (z v) (quad_nonneg G _) hv ?_
      intro t ht htz
      have hy : nonnegative (z + (-t) • (Pi.single v 1 : Vector n)) := by
        intro w
        have := hnn w
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        split_ifs with hw
        · subst hw; linarith
        · linarith
      have := hmin _ hy
      rw [hexp] at this
      nlinarith
    linarith
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · have := hpos v
    simp only [Pi.sub_apply, unitVector]
    linarith
  · have := hpos v
    have := hneg v hv
    simp only [Pi.sub_apply, unitVector]
    linarith

theorem pot_min {n m : ℕ} (G : WeightedGraph n m) (hG : G.IsConnected)
    (lam : ℝ) (hlam : 1 / (n : ℝ) < lam) (s : Fin n) :
    IsObstacleMinimizer G lam s (obstaclePotential G lam s) := by
  have h := exists_unique_min G hG lam hlam s
  simp only [obstaclePotential, dif_pos h]
  exact h.exists.choose_spec

theorem cross_nonneg {n m : ℕ} (G : WeightedGraph n m) (lam : ℝ) (a b : Fin n)
    (z w : Vector n) (hz : IsObstacleMinimizer G lam a z) (hw : IsObstacleMinimizer G lam b w) :
    0 ≤ (z - w) ⬝ᵥ ((unitVector a - G.laplacian *ᵥ z) - (unitVector b - G.laplacian *ᵥ w)) := by
  obtain ⟨ha1, ha2⟩ := kkt_bounds G lam a z hz
  obtain ⟨hb1, hb2⟩ := kkt_bounds G lam b w hw
  have e1 : z ⬝ᵥ (unitVector a - G.laplacian *ᵥ z) = lam * ∑ v, z v := by
    rw [Finset.mul_sum, dotProduct]
    refine Finset.sum_congr rfl fun v _ => ?_
    rcases hz.1 v |>.lt_or_eq with h | h
    · rw [ha2 v h]; ring
    · rw [← h]; ring
  have e2 : w ⬝ᵥ (unitVector b - G.laplacian *ᵥ w) = lam * ∑ v, w v := by
    rw [Finset.mul_sum, dotProduct]
    refine Finset.sum_congr rfl fun v _ => ?_
    rcases hw.1 v |>.lt_or_eq with h | h
    · rw [hb2 v h]; ring
    · rw [← h]; ring
  have i1 : z ⬝ᵥ (unitVector b - G.laplacian *ᵥ w) ≤ lam * ∑ v, z v := by
    rw [Finset.mul_sum, dotProduct]
    exact Finset.sum_le_sum fun v _ => by
      have := hz.1 v; have := hb1 v; nlinarith
  have i2 : w ⬝ᵥ (unitVector a - G.laplacian *ᵥ z) ≤ lam * ∑ v, w v := by
    rw [Finset.mul_sum, dotProduct]
    exact Finset.sum_le_sum fun v _ => by
      have := hw.1 v; have := ha1 v; nlinarith
  simp only [sub_dotProduct, dotProduct_sub] at e1 e2 i1 i2 ⊢
  linarith

theorem solution {n m : ℕ} (G : WeightedGraph n m) (hG : G.IsConnected)
    (lam : ℝ) (hlam : 1 / (n : ℝ) < lam) (hlam' : lam < 1 / 2)
    (s t : Fin n) (hst : s ≠ t) :
    0 ≤ regularizedResistance G lam s t ∧
    regularizedResistance G lam s t ≤ pairResistance G s t := by
  set zs := obstaclePotential G lam s
  set zt := obstaclePotential G lam t
  have hs := pot_min G hG lam hlam s
  have ht := pot_min G hG lam hlam t
  have hc := cross_nonneg G lam s t zs zt hs ht
  set d : Vector n := differenceVector s t with hd
  set x : Vector n := zs - zt with hx
  set D : Vector n := (unitVector s - G.laplacian *ᵥ zs) - (unitVector t - G.laplacian *ᵥ zt) with hD
  have hLx : G.laplacian *ᵥ x = d - D := by
    rw [hx, hD, hd, differenceVector, Matrix.mulVec_sub]; abel
  have hdsum : ∑ v, d v = 0 := by
    simp [hd, differenceVector, unitVector, Finset.sum_sub_distrib]
  obtain ⟨hp1, -⟩ := pinv_facts G hG d hdsum
  set p : Vector n := G.lapPinv *ᵥ d with hp
  have hRl : regularizedResistance G lam s t = d ⬝ᵥ x := rfl
  have hR : pairResistance G s t = d ⬝ᵥ p := by
    simp only [pairResistance, hp, hd, differenceVector, unitVector, dotProduct, Matrix.mulVec,
      Pi.sub_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      sub_mul, mul_sub, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hxLx : 0 ≤ x ⬝ᵥ (G.laplacian *ᵥ x) := quad_nonneg G x
  have hyLy : 0 ≤ (p - x) ⬝ᵥ (G.laplacian *ᵥ (p - x)) := quad_nonneg G (p - x)
  have hxD : 0 ≤ x ⬝ᵥ D := hc
  have h1 : d ⬝ᵥ x = x ⬝ᵥ (G.laplacian *ᵥ x) + x ⬝ᵥ D := by
    rw [hLx, ← dotProduct_add, dotProduct_comm d x]; congr 1; abel
  have hLy : G.laplacian *ᵥ (p - x) = D := by
    rw [Matrix.mulVec_sub, hp1, hLx]; abel
  have h2 : d ⬝ᵥ (p - x) = (p - x) ⬝ᵥ (G.laplacian *ᵥ (p - x)) + x ⬝ᵥ D := by
    have e : d = G.laplacian *ᵥ (p - x) + G.laplacian *ᵥ x := by
      rw [← Matrix.mulVec_add, sub_add_cancel, hp1]
    have c := lap_dot_comm G x (p - x)
    rw [dotProduct_comm d, e, dotProduct_add, hLy, ← hLy, ← c, hLy]
  refine ⟨?_, ?_⟩
  · rw [hRl, h1]; linarith
  · rw [hRl, hR]
    have : d ⬝ᵥ (p - x) = d ⬝ᵥ p - d ⬝ᵥ x := dotProduct_sub _ _ _
    linarith
