-- Prove2me | solution 1 for MulticlassDS.Compress.lemma13_orientation_le_d
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T12:21:55.2948+00:00
-- url     : https://prove2.me/submissions/9e52acb9-0dbb-40b6-82ee-c972575b51a3

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_MulticlassDS_Compress_OneInclusion

open MulticlassDS.Compress

theorem solution {Y : Type*} (d : ℕ) (H : Set (Fin (d + 1) → Y))
    (hH : dsDim H ≤ d) :
    ∃ σ : Orientation H, ∀ v ∈ H, outdeg σ v ≤ d := by
  classical
  -- the edge of direction i through v, as a set of vertices of H
  obtain ⟨cls, hmem⟩ : ∃ cls : Fin (d + 1) → (Fin (d + 1) → Y) → Set (Fin (d + 1) → Y),
      ∀ i v u, u ∈ cls i v ↔ u ∈ H ∧ AgreeOff i u v :=
    ⟨fun i v => {u | u ∈ H ∧ AgreeOff i u v}, fun _ _ _ => Iff.rfl⟩
  have cls_eq : ∀ i u v, AgreeOff i u v → cls i u = cls i v := by
    intro i u v h
    ext w
    rw [hmem, hmem]
    constructor
    · rintro ⟨hw, hwu⟩
      exact ⟨hw, fun j hj => (hwu j hj).trans (h j hj)⟩
    · rintro ⟨hw, hwv⟩
      exact ⟨hw, fun j hj => (hwv j hj).trans (h j hj).symm⟩
  have self_mem : ∀ i v, v ∈ H → v ∈ cls i v := fun i v hv => (hmem i v v).2 ⟨hv, fun _ _ => rfl⟩
  -- no finite nonempty subset of H is a pseudo-cube
  have key : ∀ s : Finset H, s.Nonempty → ∃ v ∈ s, ∃ i, ∀ u ∈ s, AgreeOff i u.1 v.1 → u = v := by
    intro s hs
    by_contra hcon
    push_neg at hcon
    have hsh : DSShatters H (id : Fin (d + 1) → Fin (d + 1)) := by
      refine ⟨(fun v : H => v.1) '' (s : Set H), ?_, ?_⟩
      · rintro _ ⟨v, -, rfl⟩
        exact ⟨v.1, v.2, rfl⟩
      · unfold IsPseudoCube
        refine ⟨?_, s.finite_toSet.image _, ?_⟩
        · obtain ⟨v, hv⟩ := hs
          exact ⟨v.1, v, hv, rfl⟩
        · rintro _ ⟨v, hv, rfl⟩ i
          obtain ⟨u, hu, hag, hne⟩ := hcon v hv i
          refine ⟨u.1, ⟨u, hu, rfl⟩, ?_, hag⟩
          intro heq
          apply hne
          apply Subtype.ext
          funext j
          by_cases hj : j = i
          · subst hj
            exact heq
          · exact hag j hj
    have h1 : ((d + 1 : ℕ) : ℕ∞) ≤ dsDim H := by
      unfold dsDim
      exact le_iSup_of_le (d + 1) (le_iSup_of_le id (le_iSup_of_le hsh le_rfl))
    have h2 : d + 1 ≤ d := Nat.cast_le.mp (h1.trans hH)
    omega
  -- Hall's condition
  obtain ⟨t, ht⟩ : ∃ t : H → Finset (Fin (d + 1) × Set (Fin (d + 1) → Y)),
      ∀ v, t v = Finset.univ.image (fun i => (i, cls i v.1)) := ⟨_, fun _ => rfl⟩
  have hall : ∀ s : Finset H, s.card ≤ (s.biUnion t).card := by
    intro s
    refine Finset.strongInduction (p := fun s => s.card ≤ (s.biUnion t).card) ?_ s
    intro s ih
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    obtain ⟨v, hv, i, hi⟩ := key s hs
    have h1 := ih (s.erase v) (Finset.erase_ssubset hv)
    have hnot : (i, cls i v.1) ∉ (s.erase v).biUnion t := by
      intro hm
      rw [Finset.mem_biUnion] at hm
      obtain ⟨u, hu, hut⟩ := hm
      rw [ht, Finset.mem_image] at hut
      obtain ⟨j, -, hj⟩ := hut
      rw [Prod.mk.injEq] at hj
      obtain ⟨hji, hj2⟩ := hj
      rw [hji] at hj2
      rw [Finset.mem_erase] at hu
      apply hu.1
      apply hi u hu.2
      have := self_mem i u.1 u.2
      rw [hj2] at this
      exact ((hmem _ _ _).mp this).2
    have hsub : insert (i, cls i v.1) ((s.erase v).biUnion t) ⊆ s.biUnion t := by
      intro e he
      rw [Finset.mem_insert] at he
      rcases he with rfl | he
      · exact Finset.mem_biUnion.mpr ⟨v, hv, by rw [ht]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
      · exact Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.erase_subset _ _) he
    have h3 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot] at h3
    have h4 := Finset.card_erase_add_one hv
    omega
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  have hf : ∀ v : H, cls (f v).1 v.1 = (f v).2 := by
    intro v
    have := hft v
    rw [ht, Finset.mem_image] at this
    obtain ⟨i, -, hi⟩ := this
    rw [← hi]
  obtain ⟨f', hf'⟩ : ∃ f' : (Fin (d + 1) → Y) → Fin (d + 1) × Set (Fin (d + 1) → Y),
      ∀ w (hw : w ∈ H), f' w = f ⟨w, hw⟩ :=
    ⟨fun w => if hw : w ∈ H then f ⟨w, hw⟩ else (0, ∅), fun w hw => dif_pos hw⟩
  -- the head of an edge: the vertex matched to it, if any, else any vertex of the edge
  let P : Fin (d + 1) → Set (Fin (d + 1) → Y) → (Fin (d + 1) → Y) → Prop :=
    fun i c w => w ∈ c ∧ ((∃ u ∈ c, f' u = (i, c)) → f' w = (i, c))
  have hex : ∀ i v, v ∈ H → ∃ w, P i (cls i v) w := by
    intro i v hv
    by_cases h : ∃ u ∈ cls i v, f' u = (i, cls i v)
    · obtain ⟨u, hu, hfu⟩ := h
      exact ⟨u, hu, fun _ => hfu⟩
    · exact ⟨v, self_mem i v hv, fun h' => absurd h' h⟩
  let head : Fin (d + 1) → (Fin (d + 1) → Y) → (Fin (d + 1) → Y) :=
    fun i v => @Classical.epsilon _ ⟨v⟩ (P i (cls i v))
  have hspec : ∀ i v, v ∈ H → P i (cls i v) (head i v) :=
    fun i v hv => Classical.epsilon_spec (hex i v hv)
  refine ⟨⟨head, fun i v hv => ((hmem _ _ _).mp (hspec i v hv).1).1,
    fun i v hv => ((hmem _ _ _).mp (hspec i v hv).1).2, ?_⟩, ?_⟩
  · intro i u hu v hv h
    show @Classical.epsilon _ ⟨u⟩ (P i (cls i u)) = @Classical.epsilon _ ⟨v⟩ (P i (cls i v))
    rw [cls_eq i u v h]
  · intro v hv
    obtain ⟨i0, hi0⟩ : ∃ i0, (f ⟨v, hv⟩).1 = i0 := ⟨_, rfl⟩
    have hfix : head i0 v = v := by
      obtain ⟨hw, himp⟩ := hspec i0 v hv
      have hwH := ((hmem _ _ _).mp hw).1
      have hfv : f' v = (i0, cls i0 v) := by
        rw [hf' v hv, ← hi0, (hf ⟨v, hv⟩ : cls (f ⟨v, hv⟩).1 v = _)]
      have := himp ⟨v, self_mem i0 v hv, hfv⟩
      rw [← hfv, hf' _ hwH, hf' v hv] at this
      exact congrArg Subtype.val (hfinj this)
    unfold outdeg
    calc _ ≤ (Finset.univ.erase i0).card := by
          apply Finset.card_le_card
          intro j hj
          rw [Finset.mem_filter] at hj
          rw [Finset.mem_erase]
          refine ⟨?_, Finset.mem_univ _⟩
          rintro rfl
          exact hj.2 hfix
      _ = d := by rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
