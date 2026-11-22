-- Prove2me | solution 1 for L1ResistanceCount.Counting.lemma_2_1_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T20:52:02.969266+00:00
-- url     : https://prove2.me/submissions/53b79489-814e-4a13-bbc8-9c5f50ee0a94

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

theorem lap_solves {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (e : E) :
    G.laplacian *ᵥ (G.lapPinv *ᵥ G.incidence e) = G.incidence e := by
  set T := Matrix.toEuclideanLin G.laplacian with hTdef
  have hsym : T.IsSymmetric := by
    intro u v
    rw [inner_eq_dot, inner_eq_dot, hTdef, T_apply, T_apply, dotProduct_comm, form_eq, form_eq]
    exact Finset.sum_congr rfl fun f _ => by ring
  have hy : WithLp.toLp 2 (G.incidence e) ∈ (LinearMap.ker T)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have h0 : G.laplacian *ᵥ u.ofLp = 0 := by
      have := congrArg WithLp.ofLp hu
      rwa [hTdef, T_apply] at this
    have h1 : ∑ f, G.w f * (G.incidence *ᵥ u.ofLp) f * (G.incidence *ᵥ u.ofLp) f = 0 := by
      rw [← form_eq, h0]; simp
    have h2 : ∀ f ∈ Finset.univ, 0 ≤ G.w f * (G.incidence *ᵥ u.ofLp) f * (G.incidence *ᵥ u.ofLp) f :=
      fun f _ => by
        have := G.w_pos f
        nlinarith [sq_nonneg ((G.incidence *ᵥ u.ofLp) f)]
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg h2).1 h1 e (Finset.mem_univ e)
    have h4 : (G.incidence *ᵥ u.ofLp) e = 0 := by
      have := G.w_pos e
      have : G.w e * ((G.incidence *ᵥ u.ofLp) e) ^ 2 = 0 := by rw [← h3]; ring
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact pow_eq_zero_iff (by norm_num) |>.1 h
    rw [inner_eq_dot]
    simpa [Matrix.mulVec, dotProduct_comm] using h4
  have := pinv_apply_of_mem T hsym _ hy
  have h5 := congrArg WithLp.ofLp this
  rw [hTdef, T_apply] at h5
  have h6 : (HarmonicGames.Decomposition.pinv T (WithLp.toLp 2 (G.incidence e))).ofLp
      = G.lapPinv *ᵥ G.incidence e := by
    have : Matrix.toEuclideanLin G.lapPinv = HarmonicGames.Decomposition.pinv T := by
      unfold WGraph.lapPinv
      simp [hTdef]
    rw [← this, T_apply]
  rw [h6] at h5
  simpa using h5

theorem bounds {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (e : E) : 0 < G.w e * G.effRes e ∧ G.w e * G.effRes e ≤ 1 := by
  set x := G.lapPinv *ᵥ G.incidence e with hx
  have hL : G.laplacian *ᵥ x = G.incidence e := lap_solves G e
  have hR : G.effRes e = G.incidence e ⬝ᵥ x := effRes_eq G e
  have hce : (G.incidence *ᵥ x) e = G.effRes e := by
    rw [hR]; rfl
  have hsum : G.effRes e = ∑ f, G.w f * (G.incidence *ᵥ x) f * (G.incidence *ᵥ x) f := by
    rw [← form_eq, hL, hR, dotProduct_comm]
  have hnn : ∀ f ∈ Finset.univ, 0 ≤ G.w f * (G.incidence *ᵥ x) f * (G.incidence *ᵥ x) f :=
    fun f _ => by
      have := G.w_pos f
      nlinarith [sq_nonneg ((G.incidence *ᵥ x) f)]
  have hpos : 0 < G.effRes e := by
    rcases (Finset.sum_nonneg hnn).lt_or_eq with h | h
    · rw [hsum]; exact h
    · exfalso
      have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h.symm
      have hc : ∀ f, (G.incidence *ᵥ x) f = 0 := by
        intro f
        have := hz f (Finset.mem_univ f)
        have hw := G.w_pos f
        have : G.w f * ((G.incidence *ᵥ x) f) ^ 2 = 0 := by rw [← this]; ring
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · exact pow_eq_zero_iff (by norm_num) |>.1 h
      have hbb : G.incidence e ⬝ᵥ G.incidence e = 0 := by
        nth_rewrite 2 [← hL]
        rw [form_eq]
        simp [hc]
      have := dotProduct_self_eq_zero.1 hbb
      have h1 := congrFun this (G.head e)
      simp [WGraph.incidence] at h1
  have hle : G.w e * (G.incidence *ᵥ x) e * (G.incidence *ᵥ x) e ≤ G.effRes e := by
    rw [hsum]
    exact Finset.single_le_sum (f := fun f => G.w f * (G.incidence *ᵥ x) f * (G.incidence *ᵥ x) f)
      hnn (Finset.mem_univ e)
  rw [hce] at hle
  refine ⟨mul_pos (G.w_pos e) hpos, ?_⟩
  nlinarith

theorem solution {n m : ℕ} (G : L1ResistanceCount.Counting.WeightedGraph n m)
    (hG : G.IsConnected) :
    ∀ e, 0 < G.w e * G.effRes e ∧ G.w e * G.effRes e ≤ 1 := fun e => bounds G e
