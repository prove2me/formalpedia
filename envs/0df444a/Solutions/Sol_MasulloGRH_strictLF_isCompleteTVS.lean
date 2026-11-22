-- Prove2me | solution 1 for MasulloGRH.strictLF_isCompleteTVS
-- status  : ACCEPTED   (prove)
-- author  : @Miikka
-- created : 2026-11-21T11:07:15.813121+00:00
-- url     : https://prove2.me/submissions/eb7a0ea5-f5a9-4c99-b2de-58b0e4079c4d

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_strictLF_hlcs_and_closed_steps
import Theorems.Thm_MasulloGRH_strictLF_nhds_zero_of_absConvex_traces

set_option autoImplicit false

open MasulloGRH Topology Filter Pointwise


namespace CompAux

lemma conv_sum {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E} (hS : Convex ℝ S)
    (h0 : (0 : E) ∈ S) {ι : Type*} (s : Finset ι) (r : ι → ℝ) (v : ι → E)
    (hr : ∀ i ∈ s, 0 ≤ r i) (hR : ∑ i ∈ s, r i ≤ 1) (hv : ∀ i ∈ s, v i ∈ S) :
    ∑ i ∈ s, r i • v i ∈ S := by
  rcases (Finset.sum_nonneg hr).eq_or_lt with h | h
  · have hz : ∀ i ∈ s, r i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hr).1 h.symm
    rw [Finset.sum_eq_zero (fun i hi => by rw [hz i hi, zero_smul])]
    exact h0
  · set R := ∑ i ∈ s, r i with hRdef
    have hz : ∑ i ∈ s, (r i / R) • v i ∈ S :=
      hS.sum_mem (fun i hi => div_nonneg (hr i hi) h.le)
        (by rw [← Finset.sum_div, div_self h.ne']) hv
    have := hS.smul_mem_of_zero_mem h0 hz ⟨h.le, hR⟩
    rw [Finset.smul_sum] at this
    convert this using 2 with i hi
    rw [smul_smul]
    congr 1
    field_simp

lemma cb_nhds {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {ι : Type*} {q : SeminormFamily ℂ E ι} (hq : WithSeminorms q) (U : Set E)
    (hU : U ∈ 𝓝 (0 : E)) : ∃ V ∈ 𝓝 (0 : E), V ⊆ U ∧ Convex ℝ V ∧ Balanced ℂ V := by
  obtain ⟨V, hV, hVU⟩ := hq.hasBasis.mem_iff.1 hU
  refine ⟨V, hq.hasBasis.mem_of_mem hV, hVU, ?_⟩
  obtain ⟨i, r, hr, rfl⟩ := (SeminormFamily.basisSets_iff q).1 hV
  exact ⟨Seminorm.convex_ball _ _ _, Seminorm.balanced_ball_zero _ _⟩

lemma three {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    (U : Set E) (hU : U ∈ 𝓝 (0 : E)) : ∃ V ∈ 𝓝 (0 : E), (∀ a ∈ V, -a ∈ V) ∧
      ∀ a ∈ V, ∀ b ∈ V, ∀ c ∈ V, a + b + c ∈ U := by
  obtain ⟨V1, hV1, h1⟩ := exists_nhds_zero_half hU
  obtain ⟨V2, hV2, h2⟩ := exists_nhds_zero_half hV1
  have hW : V1 ∩ V2 ∈ 𝓝 (0 : E) := inter_mem hV1 hV2
  refine ⟨(V1 ∩ V2) ∩ -(V1 ∩ V2), inter_mem hW (neg_mem_nhds_zero _ hW), ?_, ?_⟩
  · rintro a ⟨h, h'⟩
    exact ⟨h', by simpa using h⟩
  · rintro a ⟨⟨-, ha2⟩, -⟩ b ⟨⟨-, hb2⟩, -⟩ c ⟨⟨hc1, -⟩, -⟩
    exact h1 _ (h2 a ha2 b hb2) c hc1

lemma ext_sum {E : Type*} [AddCommGroup E] [Module ℝ E] (c : ℕ → ℝ) (w : ℕ → E) {N K : ℕ}
    (h : N ≤ K) :
    ∑ j ∈ Finset.range K, c j • (if j < N then w j else 0) = ∑ j ∈ Finset.range N, c j • w j := by
  rw [← Finset.sum_range_add_sum_Ico _ h]
  have h2 : ∑ j ∈ Finset.Ico N K, c j • (if j < N then w j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_Ico] at hj
    simp [show ¬ j < N by omega]
  rw [h2, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  simp [hj]

lemma geom_le (K : ℕ) : ∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ (j + 1) ≤ 1 := by
  have := sum_geometric_two_le K
  have e : ∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ (j + 1) =
      (∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j) * (1 / 2) := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; rw [pow_succ]
  rw [e]; linarith

end CompAux

open CompAux in
theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsStrictLF E) : IsCompleteTVS E := by
  obtain ⟨X, hmono, hexh, hX, htop⟩ := hE
  obtain ⟨hHL, -⟩ := strictLF_hlcs_and_closed_steps E X hmono hexh hX htop
  obtain ⟨ι, _, q, hq⟩ := hHL.1
  haveI := hq.topologicalAddGroup
  haveI := hq.continuousSMul
  haveI : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  refine ⟨hHL.2, fun 𝓕 h𝓕 => ?_⟩
  obtain ⟨hne, hC⟩ := h𝓕
  -- Step A: the filter localizes to one step
  have hA : ∃ n, ∀ U ∈ 𝓝 (0 : E), ∀ A ∈ 𝓕, ∃ a ∈ A, ∃ u ∈ U, a + u ∈ X n := by
    by_contra hcon
    push_neg at hcon
    choose U hU A hA hAU using hcon
    choose V hVn hVU hVc hVb using fun n => cb_nhds hq (U n) (hU n)
    let V' : ℕ → Set E := fun n => ⋂ j ∈ Finset.range (n + 1), V j
    have hV'n : ∀ n, V' n ∈ 𝓝 (0 : E) := fun n =>
      (biInter_finset_mem (Finset.range (n + 1))).2 (fun j _ => hVn j)
    have hV'c : ∀ n, Convex ℝ (V' n) := fun n => convex_iInter₂ (fun j _ => hVc j)
    have hV'b : ∀ n, Balanced ℂ (V' n) := fun n => balanced_iInter₂ (fun j _ => hVb j)
    have hV'0 : ∀ n, (0 : E) ∈ V' n := fun n => mem_of_mem_nhds (hV'n n)
    have hV'anti : ∀ {j k : ℕ}, k ≤ j → V' j ⊆ V' k := by
      intro j k hkj x hx
      simp only [V', Set.mem_iInter, Finset.mem_range] at hx ⊢
      intro i hi
      exact hx i (by omega)
    have hV'U : ∀ n, V' n ⊆ U n := fun n x hx => hVU n (by
      simp only [V', Set.mem_iInter, Finset.mem_range] at hx
      exact hx n (by omega))
    let c : ℕ → ℝ := fun j => (1 / 2 : ℝ) ^ (j + 1)
    have hcpos : ∀ j, 0 < c j := fun j => by positivity
    let W : Set E := {x | ∃ N : ℕ, ∃ w : ℕ → E, (∀ j, w j ∈ V' j ∧ w j ∈ X j) ∧
      x = ∑ j ∈ Finset.range N, c j • w j}
    have hWc : Convex ℝ W := by
      rintro x ⟨N, w, hw, rfl⟩ y ⟨M, w', hw', rfl⟩ a b ha hb hab
      refine ⟨max N M, fun j => a • (if j < N then w j else 0) + b • (if j < M then w' j else 0),
        fun j => ⟨?_, ?_⟩, ?_⟩
      · refine hV'c j ?_ ?_ ha hb hab
        · split_ifs
          · exact (hw j).1
          · exact hV'0 j
        · split_ifs
          · exact (hw' j).1
          · exact hV'0 j
      · refine (X j).add_mem ((X j).smul_of_tower_mem a ?_) ((X j).smul_of_tower_mem b ?_)
        · split_ifs
          · exact (hw j).2
          · exact (X j).zero_mem
        · split_ifs
          · exact (hw' j).2
          · exact (X j).zero_mem
      · simp only [smul_add, Finset.sum_add_distrib]
        rw [← ext_sum c w (le_max_left N M), ← ext_sum c w' (le_max_right N M),
          Finset.smul_sum, Finset.smul_sum]
        congr 1
        · apply Finset.sum_congr rfl; intro j _; rw [smul_comm]
        · apply Finset.sum_congr rfl; intro j _; rw [smul_comm]
    have hWb : Balanced ℂ W := by
      intro z hz
      rintro _ ⟨x, ⟨N, w, hw, rfl⟩, rfl⟩
      refine ⟨N, fun j => z • w j, fun j => ⟨hV'b j z hz (Set.smul_mem_smul_set (hw j).1),
        (X j).smul_mem z (hw j).2⟩, ?_⟩
      show z • (∑ j ∈ Finset.range N, c j • w j) = _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl; intro j _; rw [smul_comm]
    have hWtr : ∀ n, ((↑) : X n → E) ⁻¹' W ∈ 𝓝 (0 : X n) := by
      intro n
      have h1 : (c n) • V' n ∈ 𝓝 (0 : E) :=
        (set_smul_mem_nhds_zero_iff (hcpos n).ne').2 (hV'n n)
      have h0 : ((0 : X n) : E) = 0 := rfl
      have h2 : ((↑) : X n → E) ⁻¹' ((c n) • V' n) ∈ 𝓝 (0 : X n) :=
        continuous_subtype_val.continuousAt.preimage_mem_nhds (h0 ▸ h1)
      refine Filter.mem_of_superset h2 ?_
      intro z hz
      obtain ⟨v, hv, hvz⟩ := Set.mem_smul_set.1 hz
      have hvX : v ∈ X n := by
        have : v = (c n)⁻¹ • (z : E) := by
          rw [← hvz, smul_smul, inv_mul_cancel₀ (hcpos n).ne', one_smul]
        rw [this]
        exact (X n).smul_of_tower_mem _ z.2
      refine ⟨n + 1, fun j => if j = n then v else 0, fun j => ?_, ?_⟩
      · dsimp only
        by_cases h : j = n
        · subst h; rw [if_pos rfl]; exact ⟨hv, hvX⟩
        · rw [if_neg h]; exact ⟨hV'0 j, (X j).zero_mem⟩
      · rw [Finset.sum_eq_single n]
        · simp [hvz]
        · intro j _ hj; simp [hj]
        · intro h; simp at h
    have hWn := strictLF_nhds_zero_of_absConvex_traces E X hmono hexh hX htop W hWc hWb hWtr
    haveI := hne
    obtain ⟨B, hB, hBB⟩ := hC W hWn
    obtain ⟨x0, hx0⟩ := Filter.nonempty_of_mem hB
    obtain ⟨k, hk⟩ := hexh x0
    obtain ⟨y, hyB, hyA⟩ := Filter.nonempty_of_mem (inter_mem hB (hA k))
    obtain ⟨N, w, hw, hsum⟩ := hBB y hyB x0 hx0
    let K := max N k
    let w' : ℕ → E := fun j => if j < N then w j else 0
    have hw'1 : ∀ j, w' j ∈ V' j := fun j => by
      simp only [w']; split_ifs
      · exact (hw j).1
      · exact hV'0 j
    have hw'2 : ∀ j, w' j ∈ X j := fun j => by
      simp only [w']; split_ifs
      · exact (hw j).2
      · exact (X j).zero_mem
    have hsum' : y - x0 = ∑ j ∈ Finset.range K, c j • w' j := by
      rw [hsum]; exact (ext_sum c w (le_max_left N k)).symm
    rw [← Finset.sum_range_add_sum_Ico _ (le_max_right N k)] at hsum'
    set hd := ∑ j ∈ Finset.range k, c j • w' j
    set tl := ∑ j ∈ Finset.Ico k K, c j • w' j
    have hhd : hd ∈ X k := by
      apply Submodule.sum_mem
      intro j hj
      rw [Finset.mem_range] at hj
      exact (X k).smul_of_tower_mem _ (hmono hj.le (hw'2 j))
    have htl : tl ∈ V' k := by
      apply conv_sum (hV'c k) (hV'0 k)
      · intro j _; exact (hcpos j).le
      · calc ∑ j ∈ Finset.Ico k K, c j ≤ ∑ j ∈ Finset.range K, c j :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (fun j hj => by simp only [Finset.mem_Ico] at hj; simp; omega)
                (fun j _ _ => (hcpos j).le)
          _ ≤ 1 := geom_le K
      · intro j hj
        rw [Finset.mem_Ico] at hj
        exact hV'anti hj.1 (hw'1 j)
    have hntl : -tl ∈ U k := by
      apply hV'U k
      have := hV'b k (-1) (by simp) (Set.smul_mem_smul_set htl)
      simpa using this
    apply hAU k y hyA (-tl) hntl
    have : y + -tl = x0 + hd := by
      have e : y = x0 + (hd + tl) := by rw [← hsum']; abel
      rw [e]; abel
    rw [this]
    exact (X k).add_mem hk hhd
  -- Step B: the trace on the step is Cauchy
  obtain ⟨n, hn⟩ := hA
  let g : Filter (X n) := Filter.comap ((↑) : X n → E) (𝓕 + 𝓝 (0 : E))
  have hgne : g.NeBot := by
    rw [Filter.comap_neBot_iff]
    intro t ht
    obtain ⟨A, hA, U, hU, hAU⟩ := Filter.mem_add.1 ht
    obtain ⟨a, ha, u, hu, hau⟩ := hn U hU A hA
    exact ⟨⟨a + u, hau⟩, hAU (Set.add_mem_add ha hu)⟩
  have hnhds : ∀ U' ∈ 𝓝 (0 : X n), ∃ U ∈ 𝓝 (0 : E), ((↑) : X n → E) ⁻¹' U ⊆ U' := by
    intro U' hU'
    rw [nhds_subtype, Filter.mem_comap] at hU'
    exact hU'
  have hgC : IsCauchyFilter g := by
    refine ⟨hgne, fun U' hU' => ?_⟩
    obtain ⟨U, hU, hUU'⟩ := hnhds U' hU'
    obtain ⟨V, hV, hVneg, hV3⟩ := three U hU
    obtain ⟨A, hA, hAA⟩ := hC V hV
    refine ⟨((↑) : X n → E) ⁻¹' (A + V),
      Filter.preimage_mem_comap (Filter.mem_add.2 ⟨A, hA, V, hV, subset_rfl⟩), ?_⟩
    intro x hx y hy
    obtain ⟨a, ha, v, hv, hxe⟩ := Set.mem_add.1 hx
    obtain ⟨a', ha', v', hv', hye⟩ := Set.mem_add.1 hy
    apply hUU'
    show ((x - y : X n) : E) ∈ U
    have e : ((x - y : X n) : E) = (a - a') + v + -v' := by
      rw [Submodule.coe_sub, ← hxe, ← hye]; abel
    rw [e]
    exact hV3 _ (hAA a ha a' ha') v hv _ (hVneg v' hv')
  obtain ⟨z, hz⟩ := (hX n).2.1.2 g hgC
  -- Step C: the filter converges to the limit
  refine ⟨(z : E), ?_⟩
  intro S hS
  have hU : (fun y => (z : E) + y) ⁻¹' S ∈ 𝓝 (0 : E) := by
    have : Tendsto (fun y => (z : E) + y) (𝓝 0) (𝓝 (z : E)) := by
      simpa using (tendsto_const_nhds (x := (z : E))).add (tendsto_id (x := 𝓝 (0 : E)))
    exact this hS
  obtain ⟨V, hV, hVneg, hV3⟩ := three _ hU
  obtain ⟨A, hA, hAA⟩ := hC V hV
  have hC1 : ((↑) : X n → E) ⁻¹' (A + V) ∈ g :=
    Filter.preimage_mem_comap (Filter.mem_add.2 ⟨A, hA, V, hV, subset_rfl⟩)
  have hC2 : (fun w : X n => (w : E) - z) ⁻¹' V ∈ g := by
    apply hz
    apply (continuous_subtype_val.sub continuous_const).continuousAt.preimage_mem_nhds
    simpa using hV
  obtain ⟨w, hw1, hw2⟩ := Filter.nonempty_of_mem (inter_mem hC1 hC2)
  obtain ⟨a0, ha0, v0, hv0, he⟩ := Set.mem_add.1 hw1
  refine Filter.mem_of_superset hA ?_
  intro a ha
  have := hV3 _ (hAA a ha a0 ha0) _ (hVneg v0 hv0) _ hw2
  have heq : (z : E) + ((a - a0) + -v0 + ((w : E) - z)) = a := by rw [← he]; abel
  rw [Set.mem_preimage, heq] at this
  exact this
