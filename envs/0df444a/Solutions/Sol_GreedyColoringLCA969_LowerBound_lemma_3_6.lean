-- Prove2me | solution 1 for GreedyColoringLCA969.LowerBound.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:41:13.1862+00:00
-- url     : https://prove2.me/submissions/c2278a5a-3e35-419a-ab6f-63ccf16e654f

import Definitions.Def_GreedyColoringLCA969_LowerBound_GraphBasics

open scoped Classical BigOperators
namespace GreedyColoringLCA969.LowerBound

private theorem bounded_overlap_packing {α β : Type} [Fintype α] [Fintype β]
    (W : Finset α) (B : α → Finset β) (D : ℕ) (b : ℝ) (hb : 0 < b)
    (hB : ∀ u ∈ W, (B u).Nonempty ∧ (B u).card ≤ D)
    (hfreq : ∀ x, ((W.filter (fun u => x ∈ B u)).card : ℝ) ≤ b) :
    ∃ I : Finset α, I ⊆ W ∧
      (W.card : ℝ) ≤ (I.card : ℝ) * D * b ∧
      ∀ u ∈ I, ∀ v ∈ I, u ≠ v → Disjoint (B u) (B v) := by
  classical
  let P (I : Finset α) := I ⊆ W ∧
    ∀ u ∈ I, ∀ v ∈ I, u ≠ v → Disjoint (B u) (B v)
  obtain ⟨I, _, hI⟩ := Finite.exists_le_maximal (p := P)
    (a := (∅ : Finset α)) (by simp [P])
  have hcover : W ⊆ I.biUnion (fun u => W.filter (fun v => ¬Disjoint (B u) (B v))) := by
    intro v hv
    by_contra hnot
    have hdisj : ∀ u ∈ I, Disjoint (B u) (B v) := by
      intro u hu
      exact not_not.mp (fun h => hnot (Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_filter.mpr ⟨hv, h⟩⟩))
    have hins : P (insert v I) := by
      refine ⟨Finset.insert_subset hv hI.prop.1, ?_⟩
      intro u hu w hw hne
      simp only [Finset.mem_insert] at hu hw
      rcases hu with rfl | hu
      · rcases hw with rfl | hw
        · exact (hne rfl).elim
        · exact (hdisj w hw).symm
      · rcases hw with rfl | hw
        · exact hdisj u hu
        · exact hI.prop.2 u hu w hw hne
    have heq := hI.eq_of_le hins (Finset.subset_insert _ _)
    have hvI : v ∈ I := heq ▸ Finset.mem_insert_self v I
    obtain ⟨x, hx⟩ := (hB v hv).1
    exact Finset.disjoint_left.mp (hdisj v hvI) hx hx
  have hconf (u : α) (hu : u ∈ I) :
      ((W.filter (fun v => ¬Disjoint (B u) (B v))).card : ℝ) ≤ D * b := by
    have hsub : W.filter (fun v => ¬Disjoint (B u) (B v)) ⊆
        (B u).biUnion (fun x => W.filter (fun v => x ∈ B v)) := by
      intro v hv
      obtain ⟨x, hxu, hxv⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hv).2
      exact Finset.mem_biUnion.mpr ⟨x, hxu, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1, hxv⟩⟩
    calc
      _ ≤ (((B u).biUnion (fun x => W.filter (fun v => x ∈ B v))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ x ∈ B u, ((W.filter (fun v => x ∈ B v)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ B u, b := Finset.sum_le_sum (fun x _ => hfreq x)
      _ = (B u).card * b := by simp
      _ ≤ D * b := mul_le_mul_of_nonneg_right (by exact_mod_cast (hB u (hI.prop.1 hu)).2) hb.le
  refine ⟨I, hI.prop.1, ?_, hI.prop.2⟩
  calc
    (W.card : ℝ) ≤ ((I.biUnion (fun u => W.filter (fun v => ¬Disjoint (B u) (B v)))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ u ∈ I, ((W.filter (fun v => ¬Disjoint (B u) (B v))).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ I, D * b := Finset.sum_le_sum hconf
    _ = (I.card : ℝ) * D * b := by simp [mul_assoc]

private theorem neighborhood_packing (N D : ℕ) (hD : 1 ≤ D) (H : Digraph N)
    (hOut : ∀ u, (outNeighbors H u).card ≤ D) (Vprime : Finset (Fin N))
    (hLoops : ∀ u ∈ Vprime, H u u) (L : ℝ) (hL : 1 ≤ L)
    (hLarge : (2 : ℝ) * D * L ^ D ≤ (Vprime.card : ℝ)) :
    ∃ U S : Finset (Fin N), U ⊆ Vprime ∧
      L / (2 * D) ≤ (U.card : ℝ) ∧ S.card ≤ D ∧ Disjoint U S ∧
      ∀ u ∈ U, ∀ v ∈ U, u ≠ v → outNeighbors H u ∩ outNeighbors H v ⊆ S := by
  classical
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  let F (S : Finset (Fin N)) := Vprime.filter (fun u => S ⊆ outNeighbors H u)
  let P (S : Finset (Fin N)) := S.card ≤ D ∧
    (Vprime.card : ℝ) / L ^ S.card ≤ ((F S).card : ℝ)
  obtain ⟨S, _, hS⟩ := Finite.exists_le_maximal (p := P)
    (a := (∅ : Finset (Fin N))) (by simp [P, F])
  have hSsize : S.card ≤ D := hS.prop.1
  have hFlarge : (Vprime.card : ℝ) / L ^ S.card ≤ ((F S).card : ℝ) := hS.prop.2
  have hpow : (2 : ℝ) * D * L ^ S.card ≤ (Vprime.card : ℝ) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hSsize) (by positivity)).trans hLarge
  have hFtwo : (2 : ℝ) * D ≤ ((F S).card : ℝ) :=
    le_trans ((le_div_iff₀ (pow_pos hLp _)).mpr hpow) hFlarge
  have hSlt : S.card < D := by
    by_contra hn
    have heq : S.card = D := le_antisymm hSsize (by omega)
    have hFS : F S ⊆ S := by
      intro u hu
      have hu' := Finset.mem_filter.mp hu
      have hEq : S = outNeighbors H u := Finset.eq_of_subset_of_card_le hu'.2 (heq ▸ hOut u)
      rw [hEq]
      simp [outNeighbors, hLoops u hu'.1]
    have hle : ((F S).card : ℝ) ≤ D := by exact_mod_cast (Finset.card_le_card hFS).trans hSsize
    linarith
  have hfreq (x : Fin N) (hx : x ∉ S) :
      (((F S).filter (fun u => H u x)).card : ℝ) <
        (Vprime.card : ℝ) / L ^ (S.card + 1) := by
    by_contra hn
    have hEq : F (insert x S) = (F S).filter (fun u => H u x) := by
      ext u
      simp only [F, Finset.mem_filter, Finset.insert_subset_iff]
      simp only [outNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    have hins : P (insert x S) := by
      change (insert x S).card ≤ D ∧
        (Vprime.card : ℝ) / L ^ (insert x S).card ≤ ((F (insert x S)).card : ℝ)
      rw [Finset.card_insert_of_notMem hx, hEq]
      exact ⟨by omega, le_of_not_gt hn⟩
    have heq := hS.eq_of_le hins (Finset.subset_insert _ _)
    exact hx (heq ▸ Finset.mem_insert_self x S)
  let W := F S \ S
  let B (u : Fin N) := outNeighbors H u \ S
  let b : ℝ := (Vprime.card : ℝ) / L ^ (S.card + 1)
  have hnpos : (0 : ℝ) < Vprime.card := lt_of_lt_of_le (by positivity) hpow
  have hbp : 0 < b := div_pos hnpos (pow_pos hLp _)
  have hB : ∀ u ∈ W, (B u).Nonempty ∧ (B u).card ≤ D := by
    intro u hu
    have huW := Finset.mem_sdiff.mp hu
    have huV := (Finset.mem_filter.mp huW.1).1
    refine ⟨⟨u, ?_⟩, (Finset.card_le_card Finset.sdiff_subset).trans (hOut u)⟩
    simp [B, outNeighbors, hLoops u huV, huW.2]
  have hbfreq (x : Fin N) : ((W.filter (fun u => x ∈ B u)).card : ℝ) ≤ b := by
    by_cases hx : x ∈ S
    · simp [B, hx, hbp.le]
    · have hsub : W.filter (fun u => x ∈ B u) ⊆ (F S).filter (fun u => H u x) := by
        intro u hu
        have hu' := Finset.mem_filter.mp hu
        exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hu'.1).1,
          by simpa [B, outNeighbors] using (Finset.mem_sdiff.mp hu'.2).1⟩
      calc
        _ ≤ (((F S).filter (fun u => H u x)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
        _ ≤ b := (hfreq x hx).le
  obtain ⟨U, hUW, hcard, hdisj⟩ := bounded_overlap_packing W B D b hbp hB (fun x => by
    convert hbfreq x using 1
    apply congrArg (fun s : Finset (Fin N) => (s.card : ℝ))
    ext u
    simp only [Finset.mem_filter])
  have hWcard : (Vprime.card : ℝ) / L ^ S.card - D ≤ (W.card : ℝ) := by
    have hcount := Finset.card_sdiff_add_card_inter (F S) S
    have hinter := Finset.card_le_card (Finset.inter_subset_right (s₁ := F S) (s₂ := S))
    have hcount' : ((F S).card : ℝ) = (W.card : ℝ) + ((F S ∩ S).card : ℝ) := by exact_mod_cast hcount.symm
    have hinter' : ((F S ∩ S).card : ℝ) ≤ D := by exact_mod_cast hinter.trans hSsize
    linarith
  refine ⟨U, S, hUW.trans (Finset.sdiff_subset.trans (Finset.filter_subset _ _)), ?_, hSsize, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * D)).mpr
    have hhalf : (Vprime.card : ℝ) / (2 * L ^ S.card) ≤ (W.card : ℝ) := by
      have hdiv : (2 : ℝ) * D ≤ (Vprime.card : ℝ) / L ^ S.card :=
        (le_div_iff₀ (pow_pos hLp _)).mpr hpow
      have heq : (Vprime.card : ℝ) / (2 * L ^ S.card) = ((Vprime.card : ℝ) / L ^ S.card) / 2 := by ring
      rw [heq]
      linarith
    have hmul : L * (Vprime.card : ℝ) ≤
        (U.card : ℝ) * (2 * D) * (Vprime.card : ℝ) := by
      have hmain := hhalf.trans hcard
      dsimp [b] at hmain
      have := (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L ^ S.card)
        (by positivity : (0 : ℝ) < L ^ (S.card + 1))).mp
        (show (Vprime.card : ℝ) / (2 * L ^ S.card) ≤ ((U.card : ℝ) * D * (Vprime.card : ℝ)) / L ^ (S.card + 1) by
          simpa only [mul_div_assoc] using hmain)
      rw [pow_succ] at this
      nlinarith [pow_pos hLp S.card]
    exact (mul_le_mul_iff_left₀ hnpos).mp (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
  · exact Finset.disjoint_of_subset_left hUW Finset.sdiff_disjoint
  · intro u hu v hv hne x hx
    by_contra hxS
    have hxu : x ∈ B u := Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx).1, hxS⟩
    have hxv : x ∈ B v := Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx).2, hxS⟩
    exact Finset.disjoint_left.mp (hdisj u hu v hv hne) hxu hxv

end GreedyColoringLCA969.LowerBound

open GreedyColoringLCA969.LowerBound

theorem solution (N D : ℕ) (hD : 1 ≤ D) (H : Digraph N)
    (hOut : ∀ u, (outNeighbors H u).card ≤ D) (Vprime : Finset (Fin N))
    (hSize : 2 ≤ Vprime.card) (hLoops : ∀ u ∈ Vprime, H u u)
    (hLarge : (2 : ℝ) * D * (log2 (Vprime.card : ℝ)) ^ D ≤ (Vprime.card : ℝ)) :
    ∃ U S : Finset (Fin N), U ⊆ Vprime ∧
      log2 (Vprime.card : ℝ) / (2 * D) ≤ (U.card : ℝ) ∧ S.card ≤ D ∧
      Disjoint U S ∧
      ∀ u ∈ U, ∀ v ∈ U, u ≠ v → outNeighbors H u ∩ outNeighbors H v ⊆ S := by
  apply neighborhood_packing N D hD H hOut Vprime hLoops _ _ hLarge
  change 1 ≤ Real.logb 2 (Vprime.card : ℝ)
  rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  exact (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by norm_num)
    (by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hSize))).mpr (by exact_mod_cast hSize)
