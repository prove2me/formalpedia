-- Prove2me | solution 1 for KVVMatching.Ranking.ranking_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-11T00:55:08.996441+00:00
-- url     : https://prove2.me/submissions/93a1c107-7ac2-475f-9b73-4f5f5a6eeb7b

import Definitions.Def_KVVMatching_Ranking_Algorithms
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPerfectMatchingBij

-- BEGIN COMPLETE MODULE GreedyChoice
section

namespace KVVMatching.Ranking.Proof

variable {n : ℕ}

noncomputable def pick (rank : Equiv.Perm (Fin n)) (s : Finset (Fin n)) : Option (Fin n) := by
  classical
  exact if h : s.Nonempty then some (rank ((s.image rank.symm).min' (h.image _))) else none

lemma pick_none_iff (rank : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    pick rank s = none ↔ s = ∅ := by
  classical
  unfold pick
  split_ifs with h
  · simp only [false_iff]
    exact Finset.nonempty_iff_ne_empty.mp h
  · simp_all

lemma pick_some_iff (rank : Equiv.Perm (Fin n)) (s : Finset (Fin n)) (v : Fin n) :
    pick rank s = some v ↔ v ∈ s ∧ ∀ w ∈ s, rank.symm v ≤ rank.symm w := by
  classical
  unfold pick
  split_ifs with h
  · constructor
    · intro hv
      have he := Option.some.inj hv
      subst v
      constructor
      · have hm := Finset.min'_mem (s.image rank.symm) (h.image _)
        rcases Finset.mem_image.mp hm with ⟨w, hw, he⟩
        rw [← he, rank.apply_symm_apply]
        exact hw
      · intro w hw
        simpa using Finset.min'_le (s.image rank.symm) (rank.symm w)
          (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    · rintro ⟨hv, hmin⟩
      congr 1
      apply rank.symm.injective
      simp only [Equiv.symm_apply_apply]
      apply le_antisymm
      · exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
      · rcases Finset.mem_image.mp (Finset.min'_mem (s.image rank.symm) (h.image _)) with ⟨w, hw, he⟩
        rw [← he]
        exact hmin w hw
  · simp only [false_iff, not_and]
    intro hv
    exact (h ⟨v, hv⟩).elim

lemma pick_mem {rank : Equiv.Perm (Fin n)} {s : Finset (Fin n)} {v : Fin n}
    (h : pick rank s = some v) : v ∈ s := (pick_some_iff rank s v).mp h |>.1

lemma pick_le {rank : Equiv.Perm (Fin n)} {s : Finset (Fin n)} {v w : Fin n}
    (h : pick rank s = some v) (hw : w ∈ s) : rank.symm v ≤ rank.symm w :=
  (pick_some_iff rank s v).mp h |>.2 w hw

lemma pick_eq_of_order {r s : Equiv.Perm (Fin n)} {F : Finset (Fin n)}
    (h : ∀ v ∈ F, ∀ w ∈ F, r.symm v ≤ r.symm w ↔ s.symm v ≤ s.symm w) :
    pick r F = pick s F := by
  cases hr : pick r F with
  | none =>
    have hF := (pick_none_iff r F).mp hr
    simp [hF, pick]
  | some v =>
    have hv := (pick_some_iff r F v).mp hr
    exact ((pick_some_iff s F v).mpr ⟨hv.1, fun w hw => (h v hv.1 w hw).mp (hv.2 w hw)⟩).symm

end KVVMatching.Ranking.Proof
end
-- END COMPLETE MODULE GreedyChoice

-- BEGIN COMPLETE MODULE FreeRun
section

namespace KVVMatching.Ranking.Proof

variable {n : ℕ}

noncomputable def eligible (adj : Fin n → Fin n → Prop) (F : Finset (Fin n))
    (u : Fin n) : Finset (Fin n) := by classical exact F.filter (adj u)

@[simp] lemma mem_eligible (adj : Fin n → Fin n → Prop) (F : Finset (Fin n))
    (u v : Fin n) : v ∈ eligible adj F u ↔ v ∈ F ∧ adj u v := by
  classical
  simp [eligible]

noncomputable def nextFree (rank : Equiv.Perm (Fin n)) (adj : Fin n → Fin n → Prop)
    (F : Finset (Fin n)) (u : Fin n) : Finset (Fin n) :=
  match pick rank (eligible adj F u) with
  | none => F
  | some v => F.erase v

noncomputable def run (rank : Equiv.Perm (Fin n)) (adj : Fin n → Fin n → Prop)
    (F : Finset (Fin n)) : List (Fin n) → Finset (Fin n × Fin n)
  | [] => ∅
  | u :: l => match pick rank (eligible adj F u) with
    | none => run rank adj F l
    | some v => insert (u,v) (run rank adj (F.erase v) l)

lemma nextFree_subset (rank : Equiv.Perm (Fin n)) (adj : Fin n → Fin n → Prop)
    (F : Finset (Fin n)) (u : Fin n) : nextFree rank adj F u ⊆ F := by
  unfold nextFree
  split
  · exact Finset.Subset.refl F
  · exact Finset.erase_subset _ _

lemma run_mem {rank : Equiv.Perm (Fin n)} {adj : Fin n → Fin n → Prop}
    {F : Finset (Fin n)} {l : List (Fin n)} {u v : Fin n}
    (h : (u,v) ∈ run rank adj F l) : u ∈ l ∧ v ∈ F ∧ adj u v := by
  induction l generalizing F with
  | nil => simp [run] at h
  | cons a l ih =>
    unfold run at h
    split at h
    · exact ⟨List.mem_cons_of_mem a (ih h).1, (ih h).2⟩
    · rename_i w hw
      rcases Finset.mem_insert.mp h with he | ht
      · have he1 := congrArg Prod.fst he
        have he2 := congrArg Prod.snd he
        change u = a at he1
        change v = w at he2
        subst u; subst v
        exact ⟨List.mem_cons_self, (mem_eligible _ _ _ _).mp (pick_mem hw)⟩
      · obtain ⟨hu,hv,he⟩ := ih ht
        exact ⟨List.mem_cons_of_mem a hu, Finset.mem_of_mem_erase hv, he⟩

lemma run_order_congr {r s : Equiv.Perm (Fin n)} {adj : Fin n → Fin n → Prop}
    {F : Finset (Fin n)} (l : List (Fin n))
    (h : ∀ v ∈ F, ∀ w ∈ F, r.symm v ≤ r.symm w ↔ s.symm v ≤ s.symm w) :
    run r adj F l = run s adj F l := by
  induction l generalizing F with
  | nil => rfl
  | cons u l ih =>
    have hc : pick r (eligible adj F u) = pick s (eligible adj F u) :=
      pick_eq_of_order fun v hv w hw => h v ((mem_eligible _ _ _ _).mp hv).1
        w ((mem_eligible _ _ _ _).mp hw).1
    simp only [run, ← hc]
    split
    · exact ih h
    · congr 1
      exact ih (fun v hv w hw => h v (Finset.mem_of_mem_erase hv) w (Finset.mem_of_mem_erase hw))

end KVVMatching.Ranking.Proof
end
-- END COMPLETE MODULE FreeRun

-- BEGIN COMPLETE MODULE FreeMonotonicity
section

namespace KVVMatching.Ranking.Proof

variable {n : ℕ}

lemma nextFree_mono (rank : Equiv.Perm (Fin n)) (adj : Fin n → Fin n → Prop)
    {F G : Finset (Fin n)} (hFG : F ⊆ G) (u : Fin n) :
    nextFree rank adj F u ⊆ nextFree rank adj G u := by
  classical
  intro z hz
  unfold nextFree at hz ⊢
  cases hf : pick rank (eligible adj F u) <;>
    cases hg : pick rank (eligible adj G u) <;> simp only [hf] at hz ⊢
  · exact hFG hz
  · rename_i y
    apply Finset.mem_erase.mpr
    refine ⟨?_, hFG hz⟩
    intro hzy
    subst z
    have hy := (mem_eligible _ _ _ _).mp (pick_mem hg)
    have he := (pick_none_iff _ _).mp hf
    have : y ∈ eligible adj F u := (mem_eligible _ _ _ _).mpr ⟨hz,hy.2⟩
    simp [he] at this
  · exact hFG (Finset.mem_of_mem_erase hz)
  · rename_i x y
    apply Finset.mem_erase.mpr
    refine ⟨?_, hFG (Finset.mem_of_mem_erase hz)⟩
    intro hzy
    subst z
    have hx := (mem_eligible _ _ _ _).mp (pick_mem hf)
    have hy := (mem_eligible _ _ _ _).mp (pick_mem hg)
    have hxy : x = y := rank.symm.injective (le_antisymm
      (pick_le hf ((mem_eligible _ _ _ _).mpr ⟨Finset.mem_of_mem_erase hz,hy.2⟩))
      (pick_le hg ((mem_eligible _ _ _ _).mpr ⟨hFG hx.1,hx.2⟩)))
    exact (Finset.mem_erase.mp hz).1 hxy.symm

lemma pick_mono {rank : Equiv.Perm (Fin n)} {adj : Fin n → Fin n → Prop}
    {F G : Finset (Fin n)} (hFG : F ⊆ G) {u v : Fin n}
    (hv : pick rank (eligible adj F u) = some v) :
    ∃ w, pick rank (eligible adj G u) = some w ∧ rank.symm w ≤ rank.symm v := by
  have he : v ∈ eligible adj G u := by
    obtain ⟨hvF,hav⟩ := (mem_eligible _ _ _ _).mp (pick_mem hv)
    exact (mem_eligible _ _ _ _).mpr ⟨hFG hvF,hav⟩
  cases hg : pick rank (eligible adj G u) with
  | none =>
    have hempty := (pick_none_iff _ _).mp hg
    simp [hempty] at he
  | some w => exact ⟨w,rfl,pick_le hg he⟩

lemma run_mono {rank : Equiv.Perm (Fin n)} {adj : Fin n → Fin n → Prop}
    {F G : Finset (Fin n)} (hFG : F ⊆ G) (l : List (Fin n))
    {u v : Fin n} (hv : (u,v) ∈ run rank adj F l) :
    ∃ w, (u,w) ∈ run rank adj G l ∧ rank.symm w ≤ rank.symm v := by
  classical
  induction l generalizing F G with
  | nil => simp [run] at hv
  | cons a l ih =>
    have hnext := nextFree_mono rank adj hFG a
    cases hf : pick rank (eligible adj F a) with
    | none =>
      have ht : (u,v) ∈ run rank adj (nextFree rank adj F a) l := by
        simpa [run, nextFree, hf] using hv
      obtain ⟨w,hw,hle⟩ := ih hnext ht
      refine ⟨w,?_,hle⟩
      cases hg : pick rank (eligible adj G a) <;> simp_all [run, nextFree]
    | some x =>
      simp only [run, hf] at hv
      rcases Finset.mem_insert.mp hv with he | ht
      · obtain ⟨hu,hv⟩ := Prod.mk.inj he
        subst u; subst v
        obtain ⟨w,hw,hle⟩ := pick_mono hFG hf
        exact ⟨w,by simp [run,hw],hle⟩
      · have ht' : (u,v) ∈ run rank adj (nextFree rank adj F a) l := by
          simpa [nextFree,hf] using ht
        obtain ⟨w,hw,hle⟩ := ih hnext ht'
        refine ⟨w,?_,hle⟩
        cases hg : pick rank (eligible adj G a) <;> simp_all [run,nextFree]

end KVVMatching.Ranking.Proof
end
-- END COMPLETE MODULE FreeMonotonicity

-- BEGIN COMPLETE MODULE UnmatchedDeletion
section

namespace KVVMatching.Ranking.Proof

variable {n : ℕ}

lemma pick_erase_of_not_selected (r : Equiv.Perm (Fin n)) (F : Finset (Fin n))
    (v : Fin n) (h : pick r F ≠ some v) : pick r (F.erase v) = pick r F := by
  classical
  cases hc : pick r F with
  | none => simpa [(pick_none_iff _ _).mp hc] using (pick_none_iff r (∅ : Finset (Fin n))).mpr rfl
  | some w =>
    apply (pick_some_iff _ _ _).mpr
    obtain ⟨hw,hm⟩ := (pick_some_iff _ _ _).mp hc
    have hwv : w ≠ v := by intro he; subst w; exact h hc
    exact ⟨Finset.mem_erase.mpr ⟨hwv,hw⟩,fun z hz => hm z (Finset.mem_of_mem_erase hz)⟩

lemma eligible_erase (adj : Fin n → Fin n → Prop) (F : Finset (Fin n))
    (u v : Fin n) : eligible adj (F.erase v) u = (eligible adj F u).erase v := by
  classical
  ext w
  simp [and_assoc]

lemma run_erase_of_unmatched (r : Equiv.Perm (Fin n)) (adj : Fin n → Fin n → Prop)
    (F : Finset (Fin n)) (l : List (Fin n)) (v : Fin n)
    (h : ∀ u, (u,v) ∉ run r adj F l) :
    run r adj (F.erase v) l = run r adj F l := by
  classical
  induction l generalizing F with
  | nil => rfl
  | cons a l ih =>
    have hn : pick r (eligible adj F a) ≠ some v := by
      intro hv
      exact h a (by simp [run,hv])
    have hc : pick r (eligible adj (F.erase v) a) = pick r (eligible adj F a) := by
      rw [eligible_erase]
      exact pick_erase_of_not_selected r _ v hn
    simp only [run,hc]
    cases hp : pick r (eligible adj F a) with
    | none =>
      exact ih F (fun u => by simpa [run,hp] using h u)
    | some w =>
      have ht : ∀ u, (u,v) ∉ run r adj (F.erase w) l := by
        intro u hu
        exact h u (by simp [run,hp,hu])
      have he : (F.erase v).erase w = (F.erase w).erase v := by
        ext z; simp [and_left_comm]
      change insert (a,w) (run r adj ((F.erase v).erase w) l) = _
      rw [he]
      rw [ih (F.erase w) ht]

lemma run_partner_of_unmatched (r : Equiv.Perm (Fin n)) (adj : Fin n → Fin n → Prop)
    (F : Finset (Fin n)) (l : List (Fin n)) (u v : Fin n)
    (hu : u ∈ l) (hv : v ∈ F) (he : adj u v)
    (hn : ∀ a, (a,v) ∉ run r adj F l) :
    ∃ w, (u,w) ∈ run r adj F l ∧ r.symm w < r.symm v := by
  classical
  induction l generalizing F with
  | nil => simp at hu
  | cons a l ih =>
    have hnv : pick r (eligible adj F a) ≠ some v := by
      intro hc
      exact hn a (by simp [run,hc])
    rcases List.mem_cons.mp hu with hau | hul
    · subst a
      have hvE : v ∈ eligible adj F u := (mem_eligible _ _ _ _).mpr ⟨hv,he⟩
      cases hc : pick r (eligible adj F u) with
      | none => simp [(pick_none_iff _ _).mp hc] at hvE
      | some w =>
        refine ⟨w,by simp [run,hc],lt_of_le_of_ne (pick_le hc hvE) ?_⟩
        intro heq
        have : v = w := r.symm.injective heq.symm
        subst w
        exact hnv hc
    · cases hc : pick r (eligible adj F a) with
      | none =>
        obtain ⟨w,hw,hle⟩ := ih F hul hv (fun b => by simpa [run,hc] using hn b)
        exact ⟨w,by simpa [run,hc] using hw,hle⟩
      | some z =>
        have hvz : v ≠ z := by intro hz; subst z; exact hnv hc
        obtain ⟨w,hw,hle⟩ := ih (F.erase z) hul (Finset.mem_erase.mpr ⟨hvz,hv⟩)
          (fun b hb => hn b (by simp [run,hc,hb]))
        exact ⟨w,by simp [run,hc,hw],hle⟩

end KVVMatching.Ranking.Proof
end
-- END COMPLETE MODULE UnmatchedDeletion

-- BEGIN COMPLETE MODULE RunMatching
section

namespace KVVMatching.Ranking.Proof

variable {n : ℕ}

lemma run_isMatching (r : Equiv.Perm (Fin n)) (adj : Fin n → Fin n → Prop)
    (F : Finset (Fin n)) (l : List (Fin n)) (hl : l.Nodup) : IsMatching (run r adj F l) := by
  classical
  induction l generalizing F with
  | nil => simp [run,IsMatching]
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp hl
    cases hc : pick r (eligible adj F a) with
    | none => simpa [run,hc] using ih F hl
    | some v =>
      have ht := ih (F.erase v) hl
      have hfirst : ∀ e ∈ run r adj (F.erase v) l, e.1 ≠ a := by
        intro ⟨u,w⟩ he heq
        exact ha (heq ▸ (run_mem he).1)
      have hsecond : ∀ e ∈ run r adj (F.erase v) l, e.2 ≠ v := by
        intro ⟨u,w⟩ he
        exact (Finset.mem_erase.mp (run_mem he).2.1).1
      simp only [run,hc]
      constructor
      · intro e he f hf heq
        rcases Finset.mem_insert.mp he with rfl | he <;>
          rcases Finset.mem_insert.mp hf with rfl | hf
        · rfl
        · exact False.elim (hfirst f hf heq.symm)
        · exact False.elim (hfirst e he heq)
        · exact ht.1 e he f hf heq
      · intro e he f hf heq
        rcases Finset.mem_insert.mp he with rfl | he <;>
          rcases Finset.mem_insert.mp hf with rfl | hf
        · rfl
        · exact False.elim (hsecond f hf heq.symm)
        · exact False.elim (hsecond e he heq)
        · exact ht.2 e he f hf heq

noncomputable def free (M : Finset (Fin n × Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => ¬ secondMatched M v)

@[simp] lemma mem_free (M : Finset (Fin n × Fin n)) (v : Fin n) :
    v ∈ free M ↔ ¬ secondMatched M v := by classical simp [free]

@[simp] lemma free_empty : free (∅ : Finset (Fin n × Fin n)) = Finset.univ := by
  ext v
  simp [secondMatched]

lemma free_insert (M : Finset (Fin n × Fin n)) (u v : Fin n) :
    free (insert (u,v) M) = (free M).erase v := by
  classical
  ext w
  have h : secondMatched (insert (u,v) M) w ↔ w = v ∨ secondMatched M w := by
    constructor
    · rintro ⟨e,he,hew⟩
      rcases Finset.mem_insert.mp he with rfl | he
      · exact Or.inl hew.symm
      · exact Or.inr ⟨e,he,hew⟩
    · rintro (rfl | h)
      · exact ⟨(u,w),Finset.mem_insert_self _ _,rfl⟩
      · obtain ⟨e,he,hew⟩ := h
        exact ⟨e,Finset.mem_insert_of_mem he,hew⟩
  simp [h,not_or]

noncomputable def step (r : Equiv.Perm (Fin n)) (adj : Fin n → Fin n → Prop)
    (M : Finset (Fin n × Fin n)) (u : Fin n) : Finset (Fin n × Fin n) :=
  match pick r (eligible adj (free M) u) with
  | none => M
  | some v => insert (u,v) M

lemma fold_step_eq (r : Equiv.Perm (Fin n)) (adj : Fin n → Fin n → Prop)
    (l : List (Fin n)) (M : Finset (Fin n × Fin n)) :
    l.foldl (step r adj) M = M ∪ run r adj (free M) l := by
  classical
  induction l generalizing M with
  | nil => simp [run]
  | cons u l ih =>
    simp only [List.foldl_cons,step,run]
    cases hc : pick r (eligible adj (free M) u) with
    | none => exact ih M
    | some v =>
      rw [ih,free_insert]
      simp [Finset.insert_union,Finset.union_insert]

end KVVMatching.Ranking.Proof
end
-- END COMPLETE MODULE RunMatching

-- BEGIN COMPLETE MODULE NativeRun
section

namespace KVVMatching.Ranking.Proof

variable {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma native_eligible (r : Equiv.Perm (Fin n)) (adj : Fin n → Fin n → Prop)
    (M : Finset (Fin n × Fin n)) (u : Fin n) :
    (Finset.univ.filter (fun k => adj u (r k) ∧ ¬ secondMatched M (r k))) =
      (eligible adj (free M) u).image r.symm := by
  classical
  ext k
  simp [and_comm, Equiv.symm_apply_eq]

lemma native_step (r : Equiv.Perm (Fin n)) (adj : Fin n → Fin n → Prop)
    (M : Finset (Fin n × Fin n)) (u : Fin n) :
    (if he : (Finset.univ.filter (fun k => adj u (r k) ∧ ¬ secondMatched M (r k))).Nonempty
      then insert (u,r ((Finset.univ.filter (fun k => adj u (r k) ∧ ¬ secondMatched M (r k))).min' he)) M
      else M) = step r adj M u := by
  classical
  rw [native_eligible]
  unfold step pick
  by_cases h : (eligible adj (free M) u).Nonempty
  · simp [h]
  · simp [h]

lemma native_run_eq (adj : Fin n → Fin n → Prop) (arrivals r : Equiv.Perm (Fin n)) :
    greedyRun adj arrivals r (fun _ _ _ => false) =
      run r adj Finset.univ ((List.finRange n).map arrivals) := by
  classical
  have hval : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  unfold greedyRun
  rw [← hval,List.foldl_map]
  have hs : (fun M (i : Fin n) =>
      if ht : (i : ℕ) < n then
        let a : Fin n := ⟨(i : ℕ),ht⟩
        let v := arrivals a
        if (false : Bool) then M else
          let eligible : Finset (Fin n) := Finset.univ.filter
            (fun k => adj v (r k) ∧ ¬ secondMatched M (r k))
          if he : eligible.Nonempty then insert (v,r (eligible.min' he)) M else M
      else M) = (fun M i => step r adj M (arrivals i)) := by
    funext M i
    simp only [i.isLt, dite_true, Bool.false_eq_true, ↓reduceIte]
    exact native_step r adj M (arrivals i)
  change (List.finRange n).foldl _ ∅ = _
  rw [hs]
  rw [← List.foldl_map,fold_step_eq]
  simp

lemma native_run_matching (adj : Fin n → Fin n → Prop) (arrivals r : Equiv.Perm (Fin n)) :
    IsMatching (greedyRun adj arrivals r (fun _ _ _ => false)) := by
  rw [native_run_eq]
  exact run_isMatching r adj _ _ ((List.nodup_finRange n).map arrivals.injective)

end KVVMatching.Ranking.Proof
end
-- END COMPLETE MODULE NativeRun

-- BEGIN COMPLETE MODULE RankChangeCoupling
section

namespace KVVMatching.Ranking.Proof

variable {n : ℕ}

lemma run_rank_change (adj : Fin n → Fin n → Prop) (r s : Equiv.Perm (Fin n))
    (l : List (Fin n)) (u v : Fin n) (hu : u ∈ l) (he : adj u v)
    (hn : ∀ a, (a,v) ∉ run r adj Finset.univ l)
    (horder : ∀ a, a ≠ v → ∀ b, b ≠ v →
      (r.symm a ≤ r.symm b ↔ s.symm a ≤ s.symm b))
    (hshift : ∀ a, a ≠ v → (s.symm a : ℕ) ≤ (r.symm a : ℕ) + 1) :
    ∃ w, (u,w) ∈ run s adj Finset.univ l ∧ s.symm w ≤ r.symm v := by
  classical
  obtain ⟨w,hw,hlt⟩ := run_partner_of_unmatched r adj Finset.univ l u v hu
    (Finset.mem_univ v) he hn
  have hwv : w ≠ v := by rintro rfl; exact (lt_irrefl _ hlt)
  have hd := run_erase_of_unmatched r adj Finset.univ l v hn
  have hc : run r adj (Finset.univ.erase v) l = run s adj (Finset.univ.erase v) l :=
    run_order_congr l (fun a ha b hb => horder a (Finset.mem_erase.mp ha).1
      b (Finset.mem_erase.mp hb).1)
  have hw' : (u,w) ∈ run s adj (Finset.univ.erase v) l := by rw [← hc,hd]; exact hw
  obtain ⟨z,hz,hle⟩ := run_mono (Finset.erase_subset v Finset.univ) l hw'
  refine ⟨z,hz,?_⟩
  have hs := hshift w hwv
  have hlt' : (r.symm w : ℕ) < (r.symm v : ℕ) := hlt
  have hle' : (s.symm z : ℕ) ≤ (s.symm w : ℕ) := hle
  change (s.symm z : ℕ) ≤ (r.symm v : ℕ)
  omega

lemma native_rank_change (adj : Fin n → Fin n → Prop) (arrivals r s : Equiv.Perm (Fin n))
    (u v : Fin n) (he : adj u v)
    (hn : ¬ secondMatched (greedyRun adj arrivals r (fun _ _ _ => false)) v)
    (horder : ∀ a, a ≠ v → ∀ b, b ≠ v →
      (r.symm a ≤ r.symm b ↔ s.symm a ≤ s.symm b))
    (hshift : ∀ a, a ≠ v → (s.symm a : ℕ) ≤ (r.symm a : ℕ) + 1) :
    ∃ w, (u,w) ∈ greedyRun adj arrivals s (fun _ _ _ => false) ∧ s.symm w ≤ r.symm v := by
  rw [native_run_eq] at hn ⊢
  apply run_rank_change adj r s _ u v _ he _ horder hshift
  · exact List.mem_map.mpr ⟨arrivals.symm u,List.mem_finRange _,arrivals.apply_symm_apply u⟩
  · intro a ha
    exact hn ⟨(a,v),ha,rfl⟩

end KVVMatching.Ranking.Proof
end
-- END COMPLETE MODULE RankChangeCoupling

-- BEGIN COMPLETE MODULE MatchingCounts
section

namespace KVVMatching.Ranking.Proof

variable {n : ℕ}

noncomputable def rankSet (π : Equiv.Perm (Fin n)) (M : Finset (Fin n × Fin n)) :
    Finset (Fin n) := M.image (fun e => π.symm e.1)

theorem mem_rankSet (π : Equiv.Perm (Fin n)) (M : Finset (Fin n × Fin n)) (r : Fin n) :
    r ∈ rankSet π M ↔ ∃ g, (π r, g) ∈ M := by
  classical
  simp only [rankSet, Finset.mem_image]
  constructor
  · rintro ⟨⟨b,g⟩, he, hr⟩
    exact ⟨g, by simpa only [Prod.fst, Equiv.symm_apply_eq] using
      (show (π r,g) ∈ M from by simpa [← hr] using he)⟩
  · rintro ⟨g, hg⟩
    exact ⟨(π r,g), hg, by simp⟩

theorem rankSet_card (π : Equiv.Perm (Fin n)) (M : Finset (Fin n × Fin n))
    (hM : IsMatching M) : (rankSet π M).card = M.card := by
  classical
  apply Finset.card_image_iff.mpr
  intro e he f hf h
  exact hM.1 e he f hf (π.symm.injective h)

noncomputable def partnerPrefix (π : Equiv.Perm (Fin n))
    (τ : Equiv.Perm (Fin n)) (M : Finset (Fin n × Fin n)) (t : Fin n) : Finset (Fin n) :=
  (M.filter (fun e => π.symm e.1 ≤ t)).image (fun e => τ.symm e.2)

theorem mem_partnerPrefix (π τ : Equiv.Perm (Fin n)) (M : Finset (Fin n × Fin n))
    (t v : Fin n) (w : Fin n) (hw : (w,τ v) ∈ M) (hr : π.symm w ≤ t) :
    v ∈ partnerPrefix π τ M t := by
  classical
  exact Finset.mem_image.mpr ⟨(w,τ v), Finset.mem_filter.mpr ⟨hw,hr⟩, by simp⟩

theorem partnerPrefix_card_le (π τ : Equiv.Perm (Fin n))
    (M : Finset (Fin n × Fin n)) (hM : IsMatching M) (t : Fin n) :
    (partnerPrefix π τ M t).card ≤ ((rankSet π M).filter (fun r => r ≤ t)).card := by
  classical
  have hi : Set.InjOn (fun e : Fin n × Fin n => π.symm e.1)
      (↑(M.filter (fun e => π.symm e.1 ≤ t)) : Set (Fin n × Fin n)) := by
    intro e he f hf h
    exact hM.1 e (Finset.mem_of_mem_filter e he) f (Finset.mem_of_mem_filter f hf)
      (π.symm.injective h)
  calc
    (partnerPrefix π τ M t).card ≤ (M.filter (fun e => π.symm e.1 ≤ t)).card :=
      Finset.card_image_le
    _ = ((M.filter (fun e => π.symm e.1 ≤ t)).image (fun e => π.symm e.1)).card :=
      (Finset.card_image_iff.mpr hi).symm
    _ = ((rankSet π M).filter (fun r => r ≤ t)).card := by
      congr 1
      ext r
      simp only [Finset.mem_image, Finset.mem_filter, rankSet]
      constructor
      · rintro ⟨e, ⟨he,ht⟩,rfl⟩
        exact ⟨⟨e,he,rfl⟩,ht⟩
      · rintro ⟨⟨e,he,rfl⟩,ht⟩
        exact ⟨e,⟨he,ht⟩,rfl⟩

end KVVMatching.Ranking.Proof
end
-- END COMPLETE MODULE MatchingCounts

-- BEGIN COMPLETE MODULE MoveRank
section

namespace KVVMatching.Ranking.Proof

variable {n : ℕ}

/-- Move one boy to a prescribed position, retaining the order of all others. -/
def moveRank (π : Equiv.Perm (Fin (n + 1))) (v t : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 1)) :=
  ((finSuccEquiv' t).trans (finSuccEquiv' (π.symm v)).symm).trans π

@[simp] theorem moveRank_at (π : Equiv.Perm (Fin (n + 1))) (v t : Fin (n + 1)) :
    moveRank π v t t = v := by
  simp [moveRank]

@[simp] theorem moveRank_symm_at (π : Equiv.Perm (Fin (n + 1))) (v t : Fin (n + 1)) :
    (moveRank π v t).symm v = t := by
  exact (moveRank π v t).symm_apply_eq.mpr (moveRank_at π v t).symm

theorem moveRank_restore (π : Equiv.Perm (Fin (n + 1))) (v t : Fin (n + 1)) :
    moveRank (moveRank π v t) v (π.symm v) = π := by
  ext i
  simp [moveRank]

theorem moveRank_self (π : Equiv.Perm (Fin (n + 1))) (t : Fin (n + 1)) :
    moveRank π (π t) t = π := by
  ext i
  simp [moveRank]

theorem moveRank_symm_other (π : Equiv.Perm (Fin (n + 1))) (v t w : Fin (n + 1))
    (hw : w ≠ v) : ∃ k : Fin n,
      π.symm w = (π.symm v).succAbove k ∧
      (moveRank π v t).symm w = t.succAbove k := by
  have hne : π.symm w ≠ π.symm v := fun h => hw (π.symm.injective h)
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hne
  refine ⟨k, hk.symm, ?_⟩
  simp [moveRank, ← hk]

theorem succAbove_lt_iff (p : Fin (n + 1)) (i j : Fin n) :
    p.succAbove i < p.succAbove j ↔ i < j := by
  simp only [Fin.succAbove]
  split_ifs <;> simp_all only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] <;> omega

theorem moveRank_preserves (π : Equiv.Perm (Fin (n + 1))) (v t x y : Fin (n + 1))
    (hx : x ≠ v) (hy : y ≠ v) :
    (moveRank π v t).symm x < (moveRank π v t).symm y ↔ π.symm x < π.symm y := by
  obtain ⟨i, hi, hi'⟩ := moveRank_symm_other π v t x hx
  obtain ⟨j, hj, hj'⟩ := moveRank_symm_other π v t y hy
  rw [hi, hj, hi', hj', succAbove_lt_iff, succAbove_lt_iff]

theorem moveRank_position_le (π : Equiv.Perm (Fin (n + 1))) (v t w : Fin (n + 1))
    (hw : w ≠ v) : ((moveRank π v t).symm w).val ≤ (π.symm w).val + 1 := by
  obtain ⟨i, hi, hi'⟩ := moveRank_symm_other π v t w hw
  rw [hi, hi']
  simp only [Fin.succAbove]
  split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ] <;> omega

/-- Uniform reinsertion is a bijection once the original position is retained. -/
def reinsertionEquiv (t : Fin (n + 1)) :
    (Equiv.Perm (Fin (n + 1)) × Fin (n + 1)) ≃
      (Equiv.Perm (Fin (n + 1)) × Fin (n + 1)) where
  toFun p := (moveRank p.1 p.2 t, p.1.symm p.2)
  invFun p := (moveRank p.1 (p.1 t) p.2, p.1 t)
  left_inv := by
    rintro ⟨π, v⟩
    simp only [moveRank_at, moveRank_restore]
  right_inv := by
    rintro ⟨π, i⟩
    apply Prod.ext
    · simpa only [Equiv.symm_apply_apply] using moveRank_restore π (π t) i
    · simp

end KVVMatching.Ranking.Proof
end
-- END COMPLETE MODULE MoveRank

-- BEGIN COMPLETE MODULE ReinsertionAverage
section

namespace KVVMatching.Ranking.Proof

variable {n : ℕ}

theorem sum_reinsertion (t : Fin (n + 1))
    (F : Equiv.Perm (Fin (n + 1)) → ℝ) :
    (∑ π, ∑ v, F (moveRank π v t)) = (n + 1 : ℝ) * ∑ π, F π := by
  have h := (reinsertionEquiv t).sum_comp (fun p => F p.1)
  simp only [Fintype.sum_prod_type] at h
  change (∑ π, ∑ v, F (moveRank π v t)) = ∑ π, ∑ _v : Fin (n + 1), F π at h
  rw [h]
  simp [Finset.sum_mul, mul_comm]

open Classical in
theorem unmatched_reinsertion_bound (t : Fin (n + 1))
    (hit : Equiv.Perm (Fin (n + 1)) → Fin (n + 1) → Prop)
    (good : Equiv.Perm (Fin (n + 1)) → Finset (Fin (n + 1)))
    (h : ∀ π v, ¬ hit (moveRank π v t) v → v ∈ good π) :
    (n + 1 : ℝ) * (∑ π, if hit π (π t) then (0 : ℝ) else 1) ≤
      ∑ π, ((good π).card : ℝ) := by
  classical
  rw [← sum_reinsertion t (fun π => if hit π (π t) then (0 : ℝ) else 1)]
  apply Finset.sum_le_sum
  intro π _
  simp only [moveRank_at]
  calc
    (∑ v, if hit (moveRank π v t) v then (0 : ℝ) else 1) ≤
        ∑ v, if v ∈ good π then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hh : hit (moveRank π v t) v
      · simp only [hh, if_true]
        split_ifs <;> norm_num
      · simp [hh, h π v hh]
    _ = ((good π).card : ℝ) := by simp

end KVVMatching.Ranking.Proof
end
-- END COMPLETE MODULE ReinsertionAverage

-- BEGIN COMPLETE MODULE PrefixAverage
section

namespace KVVMatching.Ranking.Proof

variable {n : ℕ}

noncomputable def prefixCard (R : Finset (Fin n)) (k : ℕ) : ℝ :=
  ((R.filter (fun r => r.val < k)).card : ℝ)

@[simp] theorem prefixCard_zero (R : Finset (Fin n)) : prefixCard R 0 = 0 := by
  simp [prefixCard]

@[simp] theorem prefixCard_full (R : Finset (Fin n)) : prefixCard R n = R.card := by
  simp [prefixCard]

open Classical in
theorem prefixCard_step (R : Finset (Fin n)) (k : ℕ) (hk : k < n) :
    prefixCard R (k+1) - prefixCard R k = if (⟨k,hk⟩ : Fin n) ∈ R then 1 else 0 := by
  have hsplit : R.filter (fun r => r.val < k+1) =
      (R.filter (fun r => r.val < k)) ∪ (R.filter (fun r => r.val = k)) := by
    ext r
    by_cases hr : r ∈ R <;> simp [hr, Nat.le_iff_lt_or_eq]
  have hdis : Disjoint (R.filter (fun r => r.val < k)) (R.filter (fun r => r.val = k)) := by
    apply Finset.disjoint_left.mpr
    intro r hr hs
    simp only [Finset.mem_filter] at hr hs
    omega
  have heq : R.filter (fun r => r.val = k) =
      if (⟨k,hk⟩ : Fin n) ∈ R then {⟨k,hk⟩} else ∅ := by
    ext r
    simp only [Finset.mem_filter]
    split_ifs with h
    · simp only [Finset.mem_singleton]
      constructor
      · intro hr; exact Fin.ext hr.2
      · rintro rfl; exact ⟨h,rfl⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      intro hr he
      apply h
      simpa only [show r = ⟨k,hk⟩ from Fin.ext he] using hr
  simp only [prefixCard, hsplit, Finset.card_union_of_disjoint hdis, Nat.cast_add]
  rw [heq]
  split_ifs <;> simp

theorem prefixCard_le_form (R : Finset (Fin n)) (t : Fin n) :
    prefixCard R (t.val+1) = ((R.filter (fun r => r ≤ t)).card : ℝ) := by
  have heq : R.filter (fun r => r.val < t.val+1) = R.filter (fun r => r ≤ t) := by
    apply Finset.filter_congr
    intro r _
    change r.val < t.val + 1 ↔ r.val ≤ t.val
    omega
  exact congrArg (fun s : Finset (Fin n) => (s.card : ℝ)) heq

end KVVMatching.Ranking.Proof
end
-- END COMPLETE MODULE PrefixAverage

-- BEGIN COMPLETE MODULE RankingScalar
section

open Filter Topology

namespace KVVMatching.Ranking.Proof

/-- The finite recurrence behind the uniform RANKING estimate. -/
theorem ranking_recurrence (n : ℕ) (hn : 0 < n) (S : ℕ → ℝ)
    (hzero : S 0 = 0)
    (hstep : ∀ t < n, (n : ℝ) ≤ (n + 1 : ℝ) * S (t + 1) - n * S t) :
    ∀ t ≤ n, (n : ℝ) * (1 - ((n : ℝ) / (n + 1)) ^ t) ≤ S t := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : (0 : ℝ) < n + 1 := by positivity
  intro t ht
  induction t with
  | zero => simp [hzero]
  | succ t ih =>
    have hi := ih (by omega)
    have hs := hstep t (by omega)
    have heq : (n + 1 : ℝ) * (n * (1 - ((n : ℝ) / (n + 1)) ^ (t + 1))) =
        n + n * (n * (1 - ((n : ℝ) / (n + 1)) ^ t)) := by
      rw [pow_succ]
      field_simp
      ring
    apply (mul_le_mul_iff_right₀ hd).mp
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hi (le_of_lt hn0)]

theorem ranking_ratio_tendsto :
    Tendsto (fun n : ℕ => ((n : ℝ) / (n + 1)) ^ n) atTop
      (𝓝 (Real.exp (-1))) := by
  have h := (Real.tendsto_one_add_div_pow_exp (1 : ℝ)).inv₀ (Real.exp_ne_zero 1)
  rw [← Real.exp_neg] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [← inv_pow]
  congr 1
  field_simp

theorem ranking_uniform_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      1 - Real.exp (-1) - ε ≤ 1 - ((n : ℝ) / (n + 1)) ^ n := by
  have h := ranking_ratio_tendsto.eventually
    (gt_mem_nhds (show Real.exp (-1) < Real.exp (-1) + ε by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine ⟨max N 1, by omega, ?_⟩
  intro n hn
  have := hN n (le_trans (le_max_left _ _) hn)
  linarith

end KVVMatching.Ranking.Proof
end
-- END COMPLETE MODULE RankingScalar

-- BEGIN COMPLETE MODULE FiniteRankingBound
section

namespace KVVMatching.Ranking.Proof

open Classical in
theorem finite_ranking_bound {α : Type*} [Fintype α] [Nonempty α]
    (n : ℕ) (hn : 0 < n) (R : α → Finset (Fin n))
    (h : ∀ t : Fin n,
      (n : ℝ) * (∑ a, if t ∈ R a then (0 : ℝ) else 1) ≤
        ∑ a, (((R a).filter (fun r => r ≤ t)).card : ℝ)) :
    (n : ℝ) * (1 - ((n : ℝ)/(n+1))^n) ≤
      (Fintype.card α : ℝ)⁻¹ * ∑ a, ((R a).card : ℝ) := by
  let C : ℝ := Fintype.card α
  have hC : 0 < C := by dsimp [C]; positivity
  let U : ℕ → ℝ := fun k => ∑ a, prefixCard (R a) k
  let S : ℕ → ℝ := fun k => C⁻¹ * U k
  have hzero : S 0 = 0 := by simp [S,U]
  have hstep : ∀ k < n, (n : ℝ) ≤ (n+1 : ℝ)*S (k+1)-n*S k := by
    intro k hk
    have hsum : (∑ a, if (⟨k,hk⟩ : Fin n) ∈ R a then (0 : ℝ) else 1) =
        C - (U (k+1)-U k) := by
      calc
        _ = ∑ a, (1 - (prefixCard (R a) (k+1)-prefixCard (R a) k)) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [prefixCard_step (R a) k hk]
          split_ifs <;> norm_num
        _ = _ := by simp [Finset.sum_sub_distrib,U,C]
    have hh := h ⟨k,hk⟩
    rw [hsum] at hh
    have hright : (∑ a, (((R a).filter (fun r => r ≤ (⟨k,hk⟩ : Fin n))).card : ℝ)) =
        U (k+1) := by
      apply Finset.sum_congr rfl
      intro a _
      exact (prefixCard_le_form (R a) ⟨k,hk⟩).symm
    rw [hright] at hh
    have hraw : (n : ℝ)*C ≤ (n+1 : ℝ)*U (k+1)-n*U k := by nlinarith
    calc
      (n : ℝ) = C⁻¹ * ((n : ℝ)*C) := by field_simp
      _ ≤ C⁻¹ * ((n+1 : ℝ)*U (k+1)-n*U k) :=
        mul_le_mul_of_nonneg_left hraw (le_of_lt (inv_pos.mpr hC))
      _ = (n+1 : ℝ)*S (k+1)-n*S k := by dsimp [S]; ring
  have hf := ranking_recurrence n hn S hzero hstep n le_rfl
  simpa [S,U,C] using hf

end KVVMatching.Ranking.Proof
end
-- END COMPLETE MODULE FiniteRankingBound

-- BEGIN COMPLETE MODULE RankingCounting
section

namespace KVVMatching.Ranking.Proof

variable {n : ℕ}

theorem rankSet_hit (π : Equiv.Perm (Fin n)) (M : Finset (Fin n × Fin n)) (r : Fin n) :
    r ∈ rankSet π M ↔ firstMatched M (π r) := by
  rw [mem_rankSet]
  constructor
  · rintro ⟨g,hg⟩; exact ⟨(π r,g),hg,rfl⟩
  · rintro ⟨⟨b,g⟩,he,hb⟩
    exact ⟨g, by simpa only [Prod.fst] using hb ▸ he⟩

theorem matching_family_bound
    (M : Equiv.Perm (Fin (n+1)) → Finset (Fin (n+1) × Fin (n+1)))
    (hM : ∀ π, IsMatching (M π)) (τ : Equiv.Perm (Fin (n+1)))
    (hc : ∀ π v t, ¬ firstMatched (M (moveRank π v t)) v →
      ∃ w, (w,τ v) ∈ M π ∧ π.symm w ≤ t) :
    (n+1 : ℝ) * (1 - ((n+1 : ℝ)/(n+2))^(n+1)) ≤
      ((n+1).factorial : ℝ)⁻¹ * ∑ π, ((M π).card : ℝ) := by
  classical
  have hb := finite_ranking_bound (n+1) (by omega) (fun π => rankSet π (M π)) (by
    intro t
    have h := unmatched_reinsertion_bound t (fun π v => firstMatched (M π) v)
      (fun π => partnerPrefix π τ (M π) t) (by
        intro π v hv
        obtain ⟨w,hw,hr⟩ := hc π v t hv
        exact mem_partnerPrefix π τ (M π) t v w hw hr)
    simp only [← rankSet_hit] at h
    simp only [Nat.cast_add, Nat.cast_one]
    apply h.trans
    apply Finset.sum_le_sum
    intro π _
    exact_mod_cast partnerPrefix_card_le π τ (M π) (hM π) t)
  simpa only [Fintype.card_perm, Fintype.card_fin, rankSet_card _ _ (hM _),
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two] using hb

end KVVMatching.Ranking.Proof
end
-- END COMPLETE MODULE RankingCounting

-- BEGIN COMPLETE MODULE NativeRankingBound
section

namespace KVVMatching.Ranking.Proof

variable {n : ℕ}

theorem ranking_matching (adj : Fin n → Fin n → Prop) (π : Equiv.Perm (Fin n)) :
    IsMatching (rankingMatching adj π) := by
  classical
  have h := native_run_matching (fun g b => adj b g) Fin.revPerm π
  constructor
  · intro e he f hf hef
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hf
    exact congrArg Prod.swap (h.2 a ha b hb hef)
  · intro e he f hf hef
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hf
    exact congrArg Prod.swap (h.1 a ha b hb hef)

theorem ranking_reinsertion (adj : Fin (n+1) → Fin (n+1) → Prop)
    (τ : Equiv.Perm (Fin (n+1))) (hτ : ∀ v, adj v (τ v))
    (π : Equiv.Perm (Fin (n+1))) (v t : Fin (n+1))
    (hv : ¬ firstMatched (rankingMatching adj (moveRank π v t)) v) :
    ∃ w, (w,τ v) ∈ rankingMatching adj π ∧ π.symm w ≤ t := by
  classical
  have hn : ¬ secondMatched
      (greedyRun (fun g b => adj b g) Fin.revPerm (moveRank π v t) (fun _ _ _ => false)) v := by
    rintro ⟨⟨g,b⟩,he,hb⟩
    apply hv
    exact ⟨(b,g),Finset.mem_image.mpr ⟨(g,b),he,rfl⟩,hb⟩
  have ho : ∀ a, a ≠ v → ∀ b, b ≠ v →
      ((moveRank π v t).symm a ≤ (moveRank π v t).symm b ↔ π.symm a ≤ π.symm b) := by
    intro a ha b hb
    exact le_iff_le_iff_lt_iff_lt.mpr (moveRank_preserves π v t b a hb ha)
  have hs : ∀ a, a ≠ v → (π.symm a : ℕ) ≤ ((moveRank π v t).symm a : ℕ)+1 := by
    intro a ha
    simpa only [moveRank_restore] using
      moveRank_position_le (moveRank π v t) v (π.symm v) a ha
  obtain ⟨w,hw,hr⟩ := native_rank_change (fun g b => adj b g) Fin.revPerm
    (moveRank π v t) π (τ v) v (hτ v) hn ho hs
  exact ⟨w,Finset.mem_image.mpr ⟨(τ v,w),hw,rfl⟩,by simpa using hr⟩

theorem native_finite_bound (adj : Fin (n+1) → Fin (n+1) → Prop)
    (τ : Equiv.Perm (Fin (n+1))) (hτ : ∀ v, adj v (τ v)) :
    (n+1 : ℝ) * (1-((n+1 : ℝ)/(n+2))^(n+1)) ≤ rankingExpectation adj := by
  exact matching_family_bound (rankingMatching adj) (ranking_matching adj) τ
    (ranking_reinsertion adj τ hτ)

end KVVMatching.Ranking.Proof
end
-- END COMPLETE MODULE NativeRankingBound

-- BEGIN COMPLETE MODULE RankingRoot
section

namespace KVVMatching.Ranking

/-- The RANKING guarantee drawn from Theorem 1 with Lemmas 3 and 5.
The asymptotic threshold is uniform over all graphs of a given size. -/
theorem ranking_guarantee (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (n : ℕ), N ≤ n → ∀ (adj : Fin n → Fin n → Prop),
      (∃ τ : Fin n ≃ Fin n,
        DiscreteConvex.IntegralConvexityB.IsPerfectMatchingBij
          {p : Fin n × Fin n | adj p.1 p.2} τ) →
      (1 - Real.exp (-1) - ε) * (n : ℝ) ≤ rankingExpectation adj := by
  obtain ⟨N,hN,hbound⟩ := Proof.ranking_uniform_threshold ε hε
  refine ⟨N, ?_⟩
  intro n hn adj hperfect
  obtain ⟨τ,hτ⟩ := hperfect
  cases n with
  | zero => omega
  | succ k =>
    have hf := Proof.native_finite_bound adj τ hτ
    have hr := hbound (k+1) hn
    calc
      (1 - Real.exp (-1) - ε) * (↑(k+1) : ℝ) ≤
          (1 - ((↑(k+1) : ℝ)/(↑(k+1)+1))^(k+1)) * ↑(k+1) :=
        mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)
      _ ≤ rankingExpectation adj := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two, mul_comm] using hf


end KVVMatching.Ranking


theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (n : ℕ), N ≤ n → ∀ (adj : Fin n → Fin n → Prop),
      (∃ τ : Fin n ≃ Fin n,
        DiscreteConvex.IntegralConvexityB.IsPerfectMatchingBij
          {p : Fin n × Fin n | adj p.1 p.2} τ) →
      (1 - Real.exp (-1) - ε) * (n : ℝ) ≤ KVVMatching.Ranking.rankingExpectation adj := KVVMatching.Ranking.ranking_guarantee ε hε
end
-- END COMPLETE MODULE RankingRoot
