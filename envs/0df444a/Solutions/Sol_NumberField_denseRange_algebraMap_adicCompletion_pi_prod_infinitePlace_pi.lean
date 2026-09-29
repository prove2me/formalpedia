-- Prove2me | solution 1 for NumberField.denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/57bb4b4c-e70b-55a4-b03d-340bf0a467a4

import Mathlib
import Theorems.Thm_AbsoluteValue_exists_forall_sub_lt_of_pairwise_not_isEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi

set_option autoImplicit false

namespace P2mS26B6b

open NumberField IsDedekindDomain

theorem norm_algebraMap_completion {K : Type*} [Field K] (w : InfinitePlace K) (x : K) :
    ‖algebraMap K w.Completion x‖ = w x := by
  rw [show algebraMap K w.Completion x = (((WithAbs.equiv w.1).symm x : WithAbs w.1) : w.Completion) from rfl,
    NumberField.InfinitePlace.Completion.norm_coe]
  simp

theorem denseRange_algebraMap_completion {K : Type*} [Field K] (w : InfinitePlace K) :
    DenseRange (algebraMap K w.Completion) := by
  have h := UniformSpace.Completion.denseRange_coe (α := WithAbs w.1)
  exact (NumberField.InfinitePlace.Completion.ofCompletion_surjective w).denseRange.comp
    (h.comp (WithAbs.equiv w.1).symm.surjective.denseRange (UniformSpace.Completion.continuous_coe _))
    (NumberField.InfinitePlace.Completion.continuous_ofCompletion w)

theorem denseRange_algebraMap_adicCompletion {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) : DenseRange (algebraMap K (v.adicCompletion K)) := by
  exact IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v)

theorem isNontrivial_and_pairwise_not_isEquiv {K : Type*} [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (∀ i, (Sum.elim (fun v : S => NumberField.place (algebraMap K (v.1.adicCompletion K)))
        (fun w : InfinitePlace K => w.1) i).IsNontrivial) ∧
    Pairwise (fun i j => ¬ (Sum.elim (fun v : S => NumberField.place (algebraMap K (v.1.adicCompletion K)))
        (fun w : InfinitePlace K => w.1) i).IsEquiv
      (Sum.elim (fun v : S => NumberField.place (algebraMap K (v.1.adicCompletion K)))
        (fun w : InfinitePlace K => w.1) j)) := by
  set V := Sum.elim (fun v : S => NumberField.place (algebraMap K (v.1.adicCompletion K)))
        (fun w : InfinitePlace K => w.1) with hV
  have hVl : ∀ (v : S) (x : K), V (Sum.inl v) x = ‖algebraMap K (v.1.adicCompletion K) x‖ := fun v x =>
    NumberField.place_apply _ _
  have hemb : ∀ v : S, NumberField.FinitePlace.embedding v.1 = algebraMap K (v.1.adicCompletion K) := fun v => rfl

  have hlt : ∀ (v : S) (x : 𝓞 K), V (Sum.inl v) (algebraMap (𝓞 K) K x) < 1 ↔ x ∈ v.1.asIdeal := by
    intro v x
    rw [hVl, ← hemb]
    exact NumberField.FinitePlace.norm_lt_one_iff_mem K v.1 x
  have h2v : ∀ v : S, V (Sum.inl v) (2 : K) ≤ 1 := by
    intro v
    have h := NumberField.FinitePlace.norm_le_one K v.1 (2 : 𝓞 K)
    rw [map_ofNat, hemb] at h
    rw [hVl]; exact h
  have h2w : ∀ w : InfinitePlace K, V (Sum.inr w) (2 : K) = 2 := by
    intro w
    show w (2 : K) = 2
    rw [← NumberField.InfinitePlace.norm_embedding_eq, map_ofNat]
    exact Complex.norm_two

  have hfin2 : ∀ v : S, ¬ V (Sum.inl v) (2⁻¹ : K) < 1 := by
    intro v h
    rw [map_inv₀] at h
    have hpos : 0 < V (Sum.inl v) (2 : K) := (V (Sum.inl v)).pos two_ne_zero
    have : 1 < V (Sum.inl v) (2 : K) := by
      rcases (inv_lt_one_iff₀.1 h) with h' | h'
      · exact absurd h' (not_le.2 hpos)
      · exact h'
    exact absurd (h2v v) (not_le.2 this)
  have hinf2 : ∀ w : InfinitePlace K, V (Sum.inr w) (2⁻¹ : K) < 1 := by
    intro w
    rw [map_inv₀, h2w]; norm_num
  refine ⟨?_, ?_⟩
  · rintro (v | w)
    · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.1.ne_bot
      refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
      · exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hx0
      · exact ne_of_lt ((hlt v x).2 hx)
    · exact w.isNontrivial
  · rintro (v | w) (v' | w') hij heq
    · have hvv : v.1 ≠ v'.1 := fun h => hij (by rw [Subtype.ext h])
      have hnle : ¬ (v.1.asIdeal ≤ v'.1.asIdeal) := fun hle =>
        hvv (HeightOneSpectrum.ext (v.1.isMaximal.eq_of_le v'.1.isPrime.ne_top hle))
      obtain ⟨x, hxv, hxv'⟩ := Set.not_subset.1 hnle
      rw [AbsoluteValue.isEquiv_iff_lt_one_iff] at heq
      exact hxv' ((hlt v' x).1 ((heq _).1 ((hlt v x).2 hxv)))
    · rw [AbsoluteValue.isEquiv_iff_lt_one_iff] at heq
      exact hfin2 v ((heq _).2 (hinf2 w'))
    · rw [AbsoluteValue.isEquiv_iff_lt_one_iff] at heq
      exact hfin2 v' ((heq _).1 (hinf2 w))
    · have hww : w ≠ w' := fun h => hij (by rw [h])
      exact hww (NumberField.InfinitePlace.eq_iff_isEquiv.2 heq)

end P2mS26B6b

theorem solution {K : Type*} [Field K] [NumberField K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    DenseRange (fun x : K =>
      ((fun v : S => algebraMap K (v.1.adicCompletion K) x),
       (fun w : NumberField.InfinitePlace K => algebraMap K w.Completion x))) := by
  classical
  obtain ⟨hV, hne⟩ := P2mS26B6b.isNontrivial_and_pairwise_not_isEquiv S
  intro z
  rw [mem_closure_iff_nhds]
  intro t ht
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := mem_nhds_prod_iff.1 ht
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.mem_nhds_iff.1 ht₁
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.mem_nhds_iff.1 ht₂

  have hd₁ : ∀ v : S, ∃ k : K, dist (algebraMap K (v.1.adicCompletion K) k) (z.1 v) < ε₁ / 2 := by
    intro v
    obtain ⟨k, hk⟩ := (P2mS26B6b.denseRange_algebraMap_adicCompletion v.1).exists_dist_lt (z.1 v) (half_pos hε₁)
    exact ⟨k, by rw [dist_comm]; exact hk⟩
  have hd₂ : ∀ w : NumberField.InfinitePlace K, ∃ k : K, dist (algebraMap K w.Completion k) (z.2 w) < ε₂ / 2 := by
    intro w
    obtain ⟨k, hk⟩ := (P2mS26B6b.denseRange_algebraMap_completion w).exists_dist_lt (z.2 w) (half_pos hε₂)
    exact ⟨k, by rw [dist_comm]; exact hk⟩
  choose k₁ hk₁ using hd₁
  choose k₂ hk₂ using hd₂

  obtain ⟨x, hx⟩ := AbsoluteValue.exists_forall_sub_lt_of_pairwise_not_isEquiv hV hne (Sum.elim k₁ k₂)
    (lt_min (half_pos hε₁) (half_pos hε₂))
  refine ⟨_, hsub ⟨hb₁ ?_, hb₂ ?_⟩, Set.mem_range_self x⟩
  · rw [Metric.mem_ball, dist_pi_lt_iff hε₁]
    intro v
    have h1 : dist (algebraMap K (v.1.adicCompletion K) x) (algebraMap K (v.1.adicCompletion K) (k₁ v)) < ε₁ / 2 := by
      rw [dist_eq_norm, ← map_sub, ← NumberField.place_apply]
      exact (hx (Sum.inl v)).trans_le (min_le_left _ _)
    calc dist (algebraMap K (v.1.adicCompletion K) x) (z.1 v)
        ≤ dist (algebraMap K (v.1.adicCompletion K) x) (algebraMap K (v.1.adicCompletion K) (k₁ v))
          + dist (algebraMap K (v.1.adicCompletion K) (k₁ v)) (z.1 v) := dist_triangle _ _ _
      _ < ε₁ / 2 + ε₁ / 2 := add_lt_add h1 (hk₁ v)
      _ = ε₁ := add_halves ε₁
  · rw [Metric.mem_ball, dist_pi_lt_iff hε₂]
    intro w
    have h1 : dist (algebraMap K w.Completion x) (algebraMap K w.Completion (k₂ w)) < ε₂ / 2 := by
      rw [dist_eq_norm, ← map_sub, P2mS26B6b.norm_algebraMap_completion]
      exact (hx (Sum.inr w)).trans_le (min_le_right _ _)
    calc dist (algebraMap K w.Completion x) (z.2 w)
        ≤ dist (algebraMap K w.Completion x) (algebraMap K w.Completion (k₂ w))
          + dist (algebraMap K w.Completion (k₂ w)) (z.2 w) := dist_triangle _ _ _
      _ < ε₂ / 2 + ε₂ / 2 := add_lt_add h1 (hk₂ w)
      _ = ε₂ := add_halves ε₂

end S_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi
end P2MW
export P2MW.S_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi (solution)
