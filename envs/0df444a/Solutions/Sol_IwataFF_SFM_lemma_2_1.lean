-- Prove2me | solution 1 for IwataFF.SFM.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:29:59.241368+00:00
-- url     : https://prove2.me/submissions/10311584-3ac6-43e1-82f4-2143c3233025

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic
open IwataFF.SFM


theorem g70op_take_succ_toFinset {α : Type} [DecidableEq α] (L : List α) (k : ℕ)
    (hk : k < L.length) : (L.take (k + 1)).toFinset = insert L[k] (L.take k).toFinset := by
  rw [List.take_succ_eq_append_getElem hk, List.toFinset_append]
  ext b; simp [or_comm]

theorem g70op_greedy_prefix_sum {α : Type} [DecidableEq α] (V : Finset α)
    (f : Finset α → ℝ) (L : List α) (hL : IsOrdering V L) :
    ∀ k, k ≤ L.length → ∑ v ∈ (L.take k).toFinset, greedy f L v =
      f (L.take k).toFinset - f ∅ := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hkl : k < L.length := by omega
    have haL : L[k] ∈ L := List.getElem_mem hkl
    have hidx : L.idxOf L[k] = k := hL.1.idxOf_getElem k hkl
    have hnot : L[k] ∉ (L.take k).toFinset := by
      rw [List.mem_toFinset, List.mem_take_iff_idxOf_lt haL, hidx]; omega
    have hg : greedy f L L[k] = f (insert L[k] (L.take k).toFinset) - f (L.take k).toFinset := by
      unfold greedy; rw [if_pos haL, hidx, g70op_take_succ_toFinset L k hkl]
    rw [g70op_take_succ_toFinset L k hkl, Finset.sum_insert hnot, ih (by omega), hg]
    ring

theorem g70op_greedy_le {α : Type} [DecidableEq α] (V : Finset α)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (L : List α) (hL : IsOrdering V L) (X : Finset α) (hX : X ⊆ V) :
    ∑ v ∈ X, greedy f L v ≤ f X := by
  have hsubV : ∀ k, (L.take k).toFinset ⊆ V := by
    intro k b hb
    rw [List.mem_toFinset] at hb
    exact (hL.2 b).mp (List.mem_of_mem_take hb)
  have key : ∀ k, k ≤ L.length →
      ∑ v ∈ X ∩ (L.take k).toFinset, greedy f L v ≤ f (X ∩ (L.take k).toFinset) - f ∅ := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hkl : k < L.length := by omega
      have ih' := ih (by omega)
      have haL : L[k] ∈ L := List.getElem_mem hkl
      have haV : L[k] ∈ V := (hL.2 _).mp haL
      have hidx : L.idxOf L[k] = k := hL.1.idxOf_getElem k hkl
      have hnot : L[k] ∉ (L.take k).toFinset := by
        rw [List.mem_toFinset, List.mem_take_iff_idxOf_lt haL, hidx]; omega
      have hg : greedy f L L[k] =
          f (insert L[k] (L.take k).toFinset) - f (L.take k).toFinset := by
        unfold greedy; rw [if_pos haL, hidx, g70op_take_succ_toFinset L k hkl]
      rw [g70op_take_succ_toFinset L k hkl]
      by_cases haX : L[k] ∈ X
      · rw [Finset.inter_insert_of_mem haX]
        have hn2 : L[k] ∉ X ∩ (L.take k).toFinset := fun h => hnot (Finset.mem_inter.mp h).2
        rw [Finset.sum_insert hn2, hg]
        have hA : insert L[k] (X ∩ (L.take k).toFinset) ⊆ V :=
          Finset.insert_subset haV (fun b hb => hX (Finset.mem_inter.mp hb).1)
        have := hsub _ hA _ (hsubV k)
        have e1 : insert L[k] (X ∩ (L.take k).toFinset) ∪ (L.take k).toFinset =
            insert L[k] (L.take k).toFinset := by
          ext b; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_inter]; tauto
        have e2 : insert L[k] (X ∩ (L.take k).toFinset) ∩ (L.take k).toFinset =
            X ∩ (L.take k).toFinset := by
          ext b; simp only [Finset.mem_insert, Finset.mem_inter]
          constructor
          · rintro ⟨rfl | h, h2⟩
            · exact absurd h2 hnot
            · exact h
          · rintro h; exact ⟨Or.inr h, h.2⟩
        rw [e1, e2] at this
        linarith
      · rw [Finset.inter_insert_of_notMem haX]; exact ih'
  have := key L.length le_rfl
  rw [List.take_length] at this
  have e : X ∩ L.toFinset = X := by
    ext b; rw [Finset.mem_inter, List.mem_toFinset, hL.2]; exact ⟨fun h => h.1, fun h => ⟨h, hX h⟩⟩
  rw [e, hf0, sub_zero] at this
  exact this

theorem g70op_greedy_base {α : Type} [DecidableEq α] (V : Finset α)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (L : List α) (hL : IsOrdering V L) : greedy f L ∈ basePoly V f := by
  refine ⟨fun a ha => ?_, ?_, fun X hX => g70op_greedy_le V f hsub hf0 L hL X hX⟩
  · unfold greedy; rw [if_neg (fun h => ha ((hL.2 a).mp h))]
  · have := g70op_greedy_prefix_sum V f L hL L.length le_rfl
    rw [List.take_length, hf0, sub_zero] at this
    have e : L.toFinset = V := by ext b; rw [List.mem_toFinset]; exact hL.2 b
    rw [e] at this; exact this

theorem g70op_greedy_get {α : Type} [DecidableEq α] (f : Finset α → ℝ) (L : List α)
    (hL : L.Nodup) (i : ℕ) (hi : i < L.length) :
    greedy f L L[i] = f (L.take (i+1)).toFinset - f (L.take i).toFinset := by
  unfold greedy; rw [if_pos (List.getElem_mem hi), hL.idxOf_getElem i hi]


theorem solution {α : Type} [DecidableEq α] (V : Finset α) (hV : V.Nonempty)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (L : List α) (hL : IsOrdering V L) (u v : α) (huv : ImmSucc L u v) :
    greedy f (swapAdj L u v) =
        greedy f L +
          (f ((prefixSet L u).erase v) - f (prefixSet L u) + greedy f L v) • (chi u - chi v) ∧
      ec V f (greedy f L) u v =
        f ((prefixSet L u).erase v) - f (prefixSet L u) + greedy f L v := by
  obtain ⟨hvL, hnext⟩ := huv
  obtain ⟨k, hk⟩ : ∃ k, L.idxOf v = k := ⟨_, rfl⟩
  rw [hk] at hnext
  have hkl : k < L.length := by rw [← hk]; exact List.idxOf_lt_length_of_mem hvL
  have hk1 : k + 1 < L.length := by
    by_contra h; push Not at h; rw [List.getElem?_eq_none h] at hnext; cases hnext
  have hLk : L[k] = v := by subst hk; exact List.getElem_idxOf hkl
  have hLk1 : L[k+1] = u := by
    rw [List.getElem?_eq_getElem hk1] at hnext; exact Option.some.inj hnext
  have hne : u ≠ v := by
    intro h
    have := (hL.1.getElem_inj_iff (i := k+1) (j := k)).mp (hLk1.trans (h.trans hLk.symm))
    omega
  have huL : u ∈ L := by rw [← hLk1]; exact List.getElem_mem hk1
  have hidxu : L.idxOf u = k + 1 := by rw [← hLk1]; exact hL.1.idxOf_getElem _ hk1
  obtain ⟨σ, hσ⟩ : ∃ σ : α → α, ∀ a, σ a = if a = u then v else if a = v then u else a :=
    ⟨_, fun _ => rfl⟩
  have hσu : σ u = v := by rw [hσ, if_pos rfl]
  have hσv : σ v = u := by rw [hσ, if_neg hne.symm, if_pos rfl]
  have hσo : ∀ a, a ≠ u → a ≠ v → σ a = a := fun a h1 h2 => by rw [hσ, if_neg h1, if_neg h2]
  have hσσ : ∀ a, σ (σ a) = a := by
    intro a
    by_cases h1 : a = u
    · rw [h1, hσu, hσv]
    · by_cases h2 : a = v
      · rw [h2, hσv, hσu]
      · rw [hσo a h1 h2, hσo a h1 h2]
  have hσinj : Function.Injective σ := fun a b h => by rw [← hσσ a, h, hσσ]
  have hL' : swapAdj L u v = L.map σ := by
    unfold swapAdj; congr 1; funext a; rw [hσ]
  rw [hL']
  have hmemT : ∀ j a, a ∈ L → (a ∈ (L.take j).toFinset ↔ L.idxOf a < j) := fun j a ha => by
    rw [List.mem_toFinset]; exact List.mem_take_iff_idxOf_lt ha
  have himg : ∀ j, ((L.map σ).take j).toFinset = (L.take j).toFinset.image σ := by
    intro j; ext a; simp [← List.map_take]
  have hmemimg : ∀ (S : Finset α) a, a ∈ S.image σ ↔ σ a ∈ S := by
    intro S a; rw [Finset.mem_image]; constructor
    · rintro ⟨b, hb, rfl⟩; rwa [hσσ]
    · intro h; exact ⟨σ a, h, hσσ a⟩
  have hfix : ∀ j, j ≠ k + 1 → (L.take j).toFinset.image σ = (L.take j).toFinset := by
    intro j hj; ext a; rw [hmemimg]
    by_cases h1 : a = u
    · rw [h1, hσu, hmemT j _ hvL, hmemT j _ huL, hk, hidxu]; omega
    · by_cases h2 : a = v
      · rw [h2, hσv, hmemT j _ hvL, hmemT j _ huL, hk, hidxu]; omega
      · rw [hσo a h1 h2]
  set P := (L.take k).toFinset with hP
  have hT1 : (L.take (k+1)).toFinset = insert v P := by
    rw [g70op_take_succ_toFinset L k hkl, hLk]
  have hT2 : (L.take (k+2)).toFinset = insert u (insert v P) := by
    rw [g70op_take_succ_toFinset L (k+1) hk1, hLk1, hT1]
  have hvP : v ∉ P := by rw [hP, hmemT k v hvL, hk]; omega
  have huP : u ∉ P := by rw [hP, hmemT k u huL, hidxu]; omega
  have hpre : prefixSet L u = insert u (insert v P) := by
    unfold prefixSet; rw [hidxu]; exact hT2
  have herase : (insert u (insert v P)).erase v = insert u P := by
    ext a; simp only [Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2 | h2 | h2⟩
      · exact Or.inl h2
      · exact absurd h2 h1
      · exact Or.inr h2
    · rintro (h | h)
      · exact ⟨h ▸ hne, Or.inl h⟩
      · exact ⟨fun e => hvP (e ▸ h), Or.inr (Or.inr h)⟩
  have hfixP : P.image σ = P := hfix k (by omega)
  have himg1 : (L.take (k+1)).toFinset.image σ = insert u P := by
    rw [hT1, Finset.image_insert, hσv, hfixP]
  have hnd' : (L.map σ).Nodup := hL.1.map hσinj
  have g' : ∀ i (hi : i < L.length), greedy f (L.map σ) (σ L[i]) =
      f ((L.take (i+1)).toFinset.image σ) - f ((L.take i).toFinset.image σ) := by
    intro i hi
    have := g70op_greedy_get f (L.map σ) hnd' i (by simpa using hi)
    rw [List.getElem_map] at this
    rw [this, himg, himg]
  have gL : ∀ i (hi : i < L.length), greedy f L L[i] =
      f (L.take (i+1)).toFinset - f (L.take i).toFinset := g70op_greedy_get f L hL.1
  have gu' : greedy f (L.map σ) u = f (insert u P) - f P := by
    have := g' k hkl; rw [hLk, hσv, himg1, hfix k (by omega)] at this; exact this
  have gv' : greedy f (L.map σ) v = f (insert u (insert v P)) - f (insert u P) := by
    have := g' (k+1) hk1; rw [hLk1, hσu, hfix (k+2) (by omega), hT2, himg1] at this
    exact this
  have gu : greedy f L u = f (insert u (insert v P)) - f (insert v P) := by
    have := gL (k+1) hk1; rw [hLk1, hT2, hT1] at this; exact this
  have gv : greedy f L v = f (insert v P) - f P := by
    have := gL k hkl; rw [hLk, hT1] at this; exact this
  rw [hpre, herase]
  have part1 : greedy f (L.map σ) = greedy f L +
      (f (insert u P) - f (insert u (insert v P)) + greedy f L v) • (chi u - chi v) := by
    funext a
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    by_cases haL : a ∈ L
    · by_cases h1 : a = u
      · rw [h1, gu', gu, gv]; simp [chi, hne]; ring
      · by_cases h2 : a = v
        · rw [h2, gv', gv]; simp [chi, hne.symm]; ring
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem haL
          have hi1 : i ≠ k + 1 := fun e => h1 (by subst e; exact hLk1)
          have hi0 : i ≠ k := fun e => h2 (by subst e; exact hLk)
          have := g' i hi
          rw [hσo _ h1 h2, hfix (i+1) (by omega), hfix i hi1] at this
          rw [this, gL i hi]; simp [chi, h1, h2]
    · have hnu : a ≠ u := fun e => haL (e ▸ huL)
      have hnv : a ≠ v := fun e => haL (e ▸ hvL)
      have hna : a ∉ L.map σ := by
        rw [List.mem_map]; rintro ⟨b, hb, hba⟩
        have : b = a := by rw [← hσσ b, hba, hσo a hnu hnv]
        exact haL (this ▸ hb)
      unfold greedy; rw [if_neg hna, if_neg haL]; simp [chi, hnu, hnv]
  refine ⟨part1, ?_⟩
  -- exchange capacity
  have hord' : IsOrdering V (L.map σ) := by
    refine ⟨hnd', fun a => ?_⟩
    rw [List.mem_map, ← hL.2]
    constructor
    · rintro ⟨b, hb, rfl⟩
      by_cases h1 : b = u
      · rw [h1, hσu]; exact hvL
      · by_cases h2 : b = v
        · rw [h2, hσv]; exact huL
        · rw [hσo b h1 h2]; exact hb
    · intro ha; exact ⟨σ a, by
        by_cases h1 : a = u
        · rw [h1, hσu]; exact hvL
        · by_cases h2 : a = v
          · rw [h2, hσv]; exact huL
          · rw [hσo a h1 h2]; exact ha, hσσ a⟩
  set c := f (insert u P) - f (insert u (insert v P)) + greedy f L v with hc
  have hgreat : IsGreatest {t : ℝ | greedy f L + t • (chi u - chi v) ∈ basePoly V f} c := by
    refine ⟨?_, fun t ht => ?_⟩
    · show greedy f L + c • (chi u - chi v) ∈ basePoly V f
      rw [← part1]; exact g70op_greedy_base V f hsub hf0 _ hord'
    · have hsubV : insert u P ⊆ V := by
        intro a ha; rw [← hL.2]
        rcases Finset.mem_insert.mp ha with h | h
        · rw [h]; exact huL
        · rw [hP, List.mem_toFinset] at h; exact List.mem_of_mem_take h
      have h := ht.2.2 (insert u P) hsubV
      unfold xsum at h
      rw [Finset.sum_insert huP] at h
      have hs : ∑ a ∈ P, (greedy f L + t • (chi u - chi v)) a = ∑ a ∈ P, greedy f L a := by
        refine Finset.sum_congr rfl fun a ha => ?_
        have h1 : a ≠ u := fun e => huP (e ▸ ha)
        have h2 : a ≠ v := fun e => hvP (e ▸ ha)
        simp [chi, h1, h2]
      rw [hs, g70op_greedy_prefix_sum V f L hL k hkl.le, hf0] at h
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, chi, if_pos rfl,
        if_neg hne] at h
      simp only [ite_true, sub_zero, mul_one] at h
      rw [← hP] at h
      rw [hc, gv]; rw [gu] at h
      linarith
  exact hgreat.csSup_eq
