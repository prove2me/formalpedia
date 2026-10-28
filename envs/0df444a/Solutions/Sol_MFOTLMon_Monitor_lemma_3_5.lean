-- Prove2me | solution 1 for MFOTLMon.Monitor.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T21:31:29.463642+00:00
-- url     : https://prove2.me/submissions/998f9de3-a48c-4cd0-abc8-a4427c8ebbc8

import Definitions.Def_MFOTLMon_Monitor_Constructions
import Definitions.Def_MFOTLMon_Monitor_Automatic

namespace MFOTLMon.Monitor

variable {S : Signature}

@[simp] theorem mem_freeList (φ : Formula S) (x : ℕ) : x ∈ freeList φ ↔ x ∈ free φ := by
  exact Finset.mem_sort (· ≤ ·)

theorem freeList_nodup (φ : Formula S) : (freeList φ).Nodup :=
  Finset.sort_nodup _ _

@[simp] theorem freeList_prev (I : Interval) (φ : Formula S) :
    freeList (.prev I φ) = freeList φ := rfl

@[simp] theorem freeList_next (I : Interval) (φ : Formula S) :
    freeList (.next I φ) = freeList φ := rfl

theorem freeList_since_left (I : Interval) (φ ψ : Formula S) (h : free φ = free ψ) :
    freeList (.since I φ ψ) = freeList φ := by
  simp only [freeList, free, h, Finset.union_self]

theorem freeList_until_left (I : Interval) (φ ψ : Formula S) (h : free φ = free ψ) :
    freeList (.until I φ ψ) = freeList φ := by
  simp only [freeList, free, h, Finset.union_self]

theorem freeList_map_congr (φ : Formula S) (v w : ℕ → ℕ)
    (h : ∀ x ∈ free φ, v x = w x) : (freeList φ).map v = (freeList φ).map w :=
  List.map_congr_left fun x hx => h x ((mem_freeList φ x).mp hx)

theorem assign_on (v : ℕ → ℕ) (xs ds : List ℕ) (x : ℕ) (hx : x ∈ xs) :
    assign v xs ds x = ds.getD (xs.idxOf x) 0 := by
  simp only [assign, if_pos hx]

theorem assign_off (v : ℕ → ℕ) (xs ds : List ℕ) (x : ℕ) (hx : x ∉ xs) :
    assign v xs ds x = v x := by
  simp only [assign, if_neg hx]

theorem assign_map_on (v w : ℕ → ℕ) (xs : List ℕ) (x : ℕ) (hx : x ∈ xs) :
    assign w xs (xs.map v) x = v x := by
  simp only [assign, if_pos hx, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_idxOf hx, Option.map_some, Option.getD_some]

theorem assign_agree (v w : ℕ → ℕ) (xs ds : List ℕ) (x : ℕ) (hx : x ∈ xs) :
    assign v xs ds x = assign w xs ds x := by
  simp only [assign, if_pos hx]

theorem map_assign (v : ℕ → ℕ) (xs ds : List ℕ) (hxs : xs.Nodup)
    (hlen : ds.length = xs.length) : xs.map (assign v xs ds) = ds := by
  apply List.ext_getElem (by simpa only [List.length_map] using hlen.symm)
  intro i hi hj
  have hix : i < xs.length := by simpa only [List.length_map] using hi
  rw [List.getElem_map, assign_on _ _ _ _ (List.getElem_mem hix), hxs.idxOf_getElem i hix]
  exact List.getD_eq_getElem _ _ hj

theorem evalTerm_congr_free (const : S.C → ℕ) (t : Term S) (v w : ℕ → ℕ)
    (h : ∀ x ∈ termVars t, v x = w x) : evalTerm const v t = evalTerm const w t := by
  cases t with
  | inl x => exact h x (by simp only [termVars, Finset.mem_singleton])
  | inr c => rfl

theorem sat_congr_free (D : TempStruct S) (φ : Formula S) (v w : ℕ → ℕ) (i : ℕ)
    (h : ∀ x ∈ free φ, v x = w x) : Sat D φ v i ↔ Sat D φ w i := by
  induction φ generalizing v w i with
  | eq t t' =>
      have ht := evalTerm_congr_free D.const t v w fun x hx => h x (Finset.mem_union_left _ hx)
      have ht' := evalTerm_congr_free D.const t' v w fun x hx => h x (Finset.mem_union_right _ hx)
      simp only [Sat, ht, ht']
  | pred r ts =>
      have he : (fun k => evalTerm D.const v (ts k)) = fun k => evalTerm D.const w (ts k) := by
        funext k
        exact evalTerm_congr_free D.const (ts k) v w fun x hx =>
          h x (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hx⟩)
      simp only [Sat, he]
  | neg φ ih => exact not_congr (ih v w i h)
  | or φ ψ ihφ ihψ =>
      exact or_congr (ihφ v w i fun x hx => h x (Finset.mem_union_left _ hx))
        (ihψ v w i fun x hx => h x (Finset.mem_union_right _ hx))
  | ex x φ ih =>
      apply exists_congr
      intro d
      apply ih
      intro y hy
      by_cases hyx : y = x
      · subst y; simp only [Function.update_self]
      · have hh := h y (Finset.mem_erase.mpr ⟨hyx, hy⟩)
        simpa only [Function.update_of_ne hyx] using hh
  | prev I φ ih => exact and_congr_right fun _ => and_congr_right fun _ => ih v w (i - 1) h
  | next I φ ih => exact and_congr_right fun _ => ih v w (i + 1) h
  | since I φ ψ ihφ ihψ =>
      apply exists_congr
      intro j
      apply and_congr_right
      intro _
      apply and_congr_right
      intro _
      apply and_congr
      · exact ihψ v w j fun x hx => h x (Finset.mem_union_right _ hx)
      · apply forall_congr'
        intro k
        exact imp_congr_right fun _ => imp_congr_right fun _ =>
          ihφ v w k fun x hx => h x (Finset.mem_union_left _ hx)
  | «until» I φ ψ ihφ ihψ =>
      apply exists_congr
      intro j
      apply and_congr_right
      intro _
      apply and_congr_right
      intro _
      apply and_congr
      · exact ihψ v w j fun x hx => h x (Finset.mem_union_right _ hx)
      · apply forall_congr'
        intro k
        exact imp_congr_right fun _ => imp_congr_right fun _ =>
          ihφ v w k fun x hx => h x (Finset.mem_union_left _ hx)

theorem extSat_congr_free (rels : S.R → Set (List ℕ)) (const : S.C → ℕ)
    (P : Formula S → Set (List ℕ)) (φ : Formula S) (v w : ℕ → ℕ)
    (h : ∀ x ∈ free φ, v x = w x) : ExtSat rels const P φ v ↔ ExtSat rels const P φ w := by
  induction φ generalizing v w with
  | eq t t' =>
      have ht := evalTerm_congr_free const t v w fun x hx => h x (Finset.mem_union_left _ hx)
      have ht' := evalTerm_congr_free const t' v w fun x hx => h x (Finset.mem_union_right _ hx)
      simp only [ExtSat, ht, ht']
  | pred r ts =>
      have he : (fun k => evalTerm const v (ts k)) = fun k => evalTerm const w (ts k) := by
        funext k
        exact evalTerm_congr_free const (ts k) v w fun x hx =>
          h x (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hx⟩)
      simp only [ExtSat, he]
  | neg φ ih => exact not_congr (ih v w h)
  | or φ ψ ihφ ihψ =>
      exact or_congr (ihφ v w fun x hx => h x (Finset.mem_union_left _ hx))
        (ihψ v w fun x hx => h x (Finset.mem_union_right _ hx))
  | ex x φ ih =>
      apply exists_congr
      intro d
      apply ih
      intro y hy
      by_cases hyx : y = x
      · subst y; simp only [Function.update_self]
      · have hh := h y (Finset.mem_erase.mpr ⟨hyx, hy⟩)
        simpa only [Function.update_of_ne hyx] using hh
  | prev I φ _ => simp only [ExtSat, freeList_map_congr (.prev I φ) v w h]
  | next I φ _ => simp only [ExtSat, freeList_map_congr (.next I φ) v w h]
  | since I φ ψ _ _ => simp only [ExtSat, freeList_map_congr (.since I φ ψ) v w h]
  | «until» I φ ψ _ _ => simp only [ExtSat, freeList_map_congr (.until I φ ψ) v w h]

theorem satSet_support (D : TempStruct S) (φ : Formula S) (i : ℕ) (ds : List ℕ)
    (h : ds ∈ satSet D φ i) : ds.length = (freeList φ).length := h.1

theorem hatSet_support (rels : S.R → Set (List ℕ)) (const : S.C → ℕ)
    (P : Formula S → Set (List ℕ)) (φ : Formula S) (ds : List ℕ)
    (h : ds ∈ hatSet rels const P φ) : ds.length = (freeList φ).length := h.1

theorem satSet_map_iff (D : TempStruct S) (φ : Formula S) (v : ℕ → ℕ) (i : ℕ) :
    (freeList φ).map v ∈ satSet D φ i ↔ Sat D φ v i := by
  constructor
  · rintro ⟨_, w, hw⟩
    exact (sat_congr_free D φ _ v i fun x hx =>
      assign_map_on v w (freeList φ) x ((mem_freeList φ x).mpr hx)).mp hw
  · intro hv
    refine ⟨List.length_map _, v, ?_⟩
    exact (sat_congr_free D φ _ v i fun x hx =>
      assign_map_on v v (freeList φ) x ((mem_freeList φ x).mpr hx)).mpr hv

theorem hatSet_map_iff (rels : S.R → Set (List ℕ)) (const : S.C → ℕ)
    (P : Formula S → Set (List ℕ)) (φ : Formula S) (v : ℕ → ℕ) :
    (freeList φ).map v ∈ hatSet rels const P φ ↔ ExtSat rels const P φ v := by
  constructor
  · rintro ⟨_, w, hw⟩
    exact (extSat_congr_free rels const P φ _ v fun x hx =>
      assign_map_on v w (freeList φ) x ((mem_freeList φ x).mpr hx)).mp hw
  · intro hv
    refine ⟨List.length_map _, v, ?_⟩
    exact (extSat_congr_free rels const P φ _ v fun x hx =>
      assign_map_on v v (freeList φ) x ((mem_freeList φ x).mpr hx)).mpr hv

theorem satSet_iff (D : TempStruct S) (φ : Formula S) (i : ℕ) (ds : List ℕ) :
    ds ∈ satSet D φ i ↔ ds.length = (freeList φ).length ∧
      Sat D φ (assign (fun _ => 0) (freeList φ) ds) i := by
  constructor
  · rintro ⟨hlen, v, hv⟩
    refine ⟨hlen, ?_⟩
    exact (sat_congr_free D φ _ _ i fun x hx =>
      assign_agree v (fun _ => 0) (freeList φ) ds x ((mem_freeList φ x).mpr hx)).mp hv
  · rintro ⟨hlen, hv⟩
    exact ⟨hlen, (fun _ => 0), hv⟩

theorem hatSet_iff (rels : S.R → Set (List ℕ)) (const : S.C → ℕ)
    (P : Formula S → Set (List ℕ)) (φ : Formula S) (ds : List ℕ) :
    ds ∈ hatSet rels const P φ ↔ ds.length = (freeList φ).length ∧
      ExtSat rels const P φ (assign (fun _ => 0) (freeList φ) ds) := by
  constructor
  · rintro ⟨hlen, v, hv⟩
    refine ⟨hlen, ?_⟩
    exact (extSat_congr_free rels const P φ _ _ fun x hx =>
      assign_agree v (fun _ => 0) (freeList φ) ds x ((mem_freeList φ x).mpr hx)).mp hv
  · rintro ⟨hlen, hv⟩
    exact ⟨hlen, (fun _ => 0), hv⟩

theorem extSat_iff_sat (D : TempStruct S) (i : ℕ) (P : Formula S → Set (List ℕ))
    (φ : Formula S) (hP : ∀ ψ ∈ tsub φ, P ψ = satSet D ψ i) (v : ℕ → ℕ) :
    ExtSat (D.rel i) D.const P φ v ↔ Sat D φ v i := by
  induction φ generalizing v with
  | eq t t' => rfl
  | pred r ts => rfl
  | neg φ ih => exact not_congr (ih hP v)
  | or φ ψ ihφ ihψ =>
      exact or_congr (ihφ (fun α hα => hP α (List.mem_append_left _ hα)) v)
        (ihψ (fun α hα => hP α (List.mem_append_right _ hα)) v)
  | ex x φ ih => exact exists_congr fun d => ih hP (Function.update v x d)
  | prev I φ _ =>
      change (freeList (Formula.prev I φ)).map v ∈ P (Formula.prev I φ) ↔ _
      rw [hP _ (by simp only [tsub, List.mem_singleton])]
      exact satSet_map_iff D _ v i
  | next I φ _ =>
      change (freeList (Formula.next I φ)).map v ∈ P (Formula.next I φ) ↔ _
      rw [hP _ (by simp only [tsub, List.mem_singleton])]
      exact satSet_map_iff D _ v i
  | since I φ ψ _ _ =>
      change (freeList (Formula.since I φ ψ)).map v ∈ P (Formula.since I φ ψ) ↔ _
      rw [hP _ (by simp only [tsub, List.mem_singleton])]
      exact satSet_map_iff D _ v i
  | «until» I φ ψ _ _ =>
      change (freeList (Formula.until I φ ψ)).map v ∈ P (Formula.until I φ ψ) ↔ _
      rw [hP _ (by simp only [tsub, List.mem_singleton])]
      exact satSet_map_iff D _ v i

theorem hatSet_eq_satSet (D : TempStruct S) (i : ℕ) (P : Formula S → Set (List ℕ))
    (φ : Formula S) (hP : ∀ ψ ∈ tsub φ, P ψ = satSet D ψ i) :
    hatSet (D.rel i) D.const P φ = satSet D φ i := by
  ext ds
  rw [hatSet_iff, satSet_iff, extSat_iff_sat D i P φ hP]

theorem prevP_satSet (D : TempStruct S) (I : Interval) (β : Formula S) (i : ℕ) :
    prevP D.τ I i (satSet D β (i - 1)) = satSet D (.prev I β) i := by
  ext ds
  by_cases h : 0 < i ∧ I.Mem (D.τ i - D.τ (i - 1))
  · rw [prevP, if_pos h, satSet_iff, satSet_iff]
    change (_ ∧ Sat D β _ (i - 1)) ↔ (_ ∧ 0 < i ∧ I.Mem _ ∧ Sat D β _ (i - 1))
    exact ⟨fun hd => ⟨hd.1, h.1, h.2, hd.2⟩, fun hd => ⟨hd.1, hd.2.2.2⟩⟩
  · rw [prevP, if_neg h]
    simp only [Set.mem_empty_iff_false, false_iff]
    rintro ⟨_, _, hpos, hmem, _⟩
    exact h ⟨hpos, hmem⟩

theorem nextP_satSet (D : TempStruct S) (I : Interval) (β : Formula S) (i : ℕ) :
    nextP D.τ I i (satSet D β (i + 1)) = satSet D (.next I β) i := by
  ext ds
  by_cases h : I.Mem (D.τ (i + 1) - D.τ i)
  · rw [nextP, if_pos h, satSet_iff, satSet_iff]
    change (_ ∧ Sat D β _ (i + 1)) ↔ (_ ∧ I.Mem _ ∧ Sat D β _ (i + 1))
    exact ⟨fun hd => ⟨hd.1, h, hd.2⟩, fun hd => ⟨hd.1, hd.2.2⟩⟩
  · rw [nextP, if_neg h]
    simp only [Set.mem_empty_iff_false, false_iff]
    rintro ⟨_, _, hmem, _⟩
    exact h hmem

theorem satSet_since_iff (D : TempStruct S) (I : Interval) (β γ : Formula S)
    (hfree : free β = free γ) (i : ℕ) (a : List ℕ) :
    a ∈ satSet D (.since I β γ) i ↔
      ∃ j, j ≤ i ∧ I.Mem (D.τ i - D.τ j) ∧ a ∈ satSet D γ j ∧
        ∀ k, j < k → k ≤ i → a ∈ satSet D β k := by
  have hfg : freeList β = freeList γ := by
    simp only [freeList, hfree]
  simp only [satSet_iff, freeList_since_left I β γ hfree, hfg, Sat]
  constructor
  · rintro ⟨hlen, j, hji, hI, hγ, hβ⟩
    exact ⟨j, hji, hI, ⟨hlen, hγ⟩, fun k hjk hki => ⟨hlen, hβ k hjk hki⟩⟩
  · rintro ⟨j, hji, hI, ⟨hlen, hγ⟩, hβ⟩
    exact ⟨hlen, j, hji, hI, hγ, fun k hjk hki => (hβ k hjk hki).2⟩

theorem satSet_until_iff (D : TempStruct S) (I : Interval) (β γ : Formula S)
    (hfree : free β = free γ) (i : ℕ) (a : List ℕ) :
    a ∈ satSet D (.until I β γ) i ↔
      ∃ j, i ≤ j ∧ I.Mem (D.τ j - D.τ i) ∧ a ∈ satSet D γ j ∧
        ∀ k, i ≤ k → k < j → a ∈ satSet D β k := by
  have hfg : freeList β = freeList γ := by
    simp only [freeList, hfree]
  simp only [satSet_iff, freeList_until_left I β γ hfree, hfg, Sat]
  constructor
  · rintro ⟨hlen, j, hij, hI, hγ, hβ⟩
    exact ⟨j, hij, hI, ⟨hlen, hγ⟩, fun k hik hkj => ⟨hlen, hβ k hik hkj⟩⟩
  · rintro ⟨j, hij, hI, ⟨hlen, hγ⟩, hβ⟩
    exact ⟨hlen, j, hij, hI, hγ, fun k hik hkj => (hβ k hik hkj).2⟩

theorem satSet_until_offset_iff (D : TempStruct S) (I : Interval) (β γ : Formula S)
    (hfree : free β = free γ) (i : ℕ) (a : List ℕ) :
    a ∈ satSet D (.until I β γ) i ↔
      ∃ j, I.Mem (D.τ (i + j) - D.τ i) ∧ a ∈ satSet D γ (i + j) ∧
        ∀ k, k < j → a ∈ satSet D β (i + k) := by
  rw [satSet_until_iff D I β γ hfree]
  constructor
  · rintro ⟨j, hij, hI, hγ, hβ⟩
    have he : i + (j - i) = j := by omega
    refine ⟨j - i, ?_, ?_, ?_⟩
    · simpa only [he] using hI
    · simpa only [he] using hγ
    · intro k hk
      exact hβ (i + k) (by omega) (by omega)
  · rintro ⟨j, hI, hγ, hβ⟩
    refine ⟨i + j, Nat.le_add_right i j, hI, hγ, ?_⟩
    intro k hik hkj
    have he : i + (k - i) = k := by omega
    simpa only [he] using hβ (k - i) (by omega)

end MFOTLMon.Monitor

namespace MFOTLMon.Monitor

open Classical

variable {α β : Type}

theorem language_regular_empty : Language.IsRegular (0 : Language α) := by
  let M : DFA α Unit := ⟨fun s _ ↦ s, (), ∅⟩
  exact ⟨Unit, inferInstance, M, rfl⟩

theorem language_regular_univ : Language.IsRegular (⊤ : Language α) := by
  let M : DFA α Unit := ⟨fun s _ ↦ s, (), Set.univ⟩
  exact ⟨Unit, inferInstance, M, rfl⟩

theorem language_regular_preimage_filterMap (f : α → Option β) {L : Language β}
    (hL : L.IsRegular) : Language.IsRegular (List.filterMap f ⁻¹' L : Language α) := by
  obtain ⟨σ, hσ, M, hM⟩ := hL
  let N : DFA α σ :=
    { step := fun s a ↦ match f a with
        | none => s
        | some b => M.step s b
      start := M.start
      accept := M.accept }
  have heval (w : List α) (s : σ) : N.evalFrom s w = M.evalFrom s (w.filterMap f) := by
    induction w generalizing s with
    | nil => rfl
    | cons a w ih =>
      cases h : f a <;> simp [DFA.evalFrom_cons, N, h, ih]
  refine ⟨σ, hσ, N, ?_⟩
  ext w
  change N.evalFrom N.start w ∈ N.accept ↔ w.filterMap f ∈ L
  rw [heval]
  change M.evalFrom M.start (w.filterMap f) ∈ M.accept ↔ _
  rw [← hM]
  rfl

theorem language_regular_preimage_map (f : α → β) {L : Language β}
    (hL : L.IsRegular) : Language.IsRegular (List.map f ⁻¹' L : Language α) := by
  simpa only [List.filterMap_eq_map'] using
    language_regular_preimage_filterMap (fun a ↦ some (f a)) hL

theorem language_regular_image_filterMap (f : α → Option β) {L : Language α}
    (hL : L.IsRegular) : Language.IsRegular (List.filterMap f '' L : Language β) := by
  classical
  obtain ⟨σ, hσ, M, hM⟩ := hL
  let N : εNFA β σ :=
    { step := fun s b ↦ {t | ∃ a, f a = b ∧ M.step s a = t}
      start := {M.start}
      accept := M.accept }
  have hpath (v : List (Option β)) (s t : σ) :
      N.IsPath s t v ↔ ∃ u : List α, u.map f = v ∧ M.evalFrom s u = t := by
    induction v generalizing s t with
    | nil =>
      simp only [εNFA.isPath_nil]
      constructor
      · intro h
        exact ⟨[], rfl, h⟩
      · rintro ⟨u, hu, ht⟩
        have : u = [] := List.map_eq_nil_iff.mp hu
        simpa [this] using ht
    | cons b v ih =>
      constructor
      · intro hp
        cases hp with
        | cons q _ _ _ _ hq hp =>
          obtain ⟨a, ha, hstep⟩ := hq
          obtain ⟨u, hu, hrun⟩ := (ih q t).mp hp
          refine ⟨a :: u, by simp only [List.map_cons, ha, hu], ?_⟩
          simpa only [DFA.evalFrom_cons, hstep] using hrun
      · rintro ⟨u, hu, hrun⟩
        cases u with
        | nil => simp at hu
        | cons a u =>
          obtain ⟨ha, hu⟩ := List.cons.inj hu
          exact .cons (M.step s a) s t b v ⟨a, ha, rfl⟩
            ((ih (M.step s a) t).mpr ⟨u, hu, hrun⟩)
  have hreduce (u : List α) : (u.map f).reduceOption = u.filterMap f := by
    induction u with
    | nil => rfl
    | cons a u ih => cases h : f a <;> simp [h, ih]
  refine ⟨Set σ, inferInstance, N.toNFA.toDFA, ?_⟩
  rw [NFA.toDFA_correct, εNFA.toNFA_correct]
  ext v
  rw [N.mem_accepts_iff_exists_path]
  constructor
  · rintro ⟨s, t, v', hs, ht, hv', hp⟩
    have hs' : s = M.start := hs
    obtain ⟨u, hu, hrun⟩ := (hpath v' s t).mp hp
    refine ⟨u, ?_, ?_⟩
    · rw [← hM]
      change M.evalFrom M.start u ∈ M.accept
      simpa only [← hs', hrun] using ht
    · rw [← hreduce, hu, hv']
  · rintro ⟨u, hu, rfl⟩
    refine ⟨M.start, M.evalFrom M.start u, u.map f, rfl, ?_, hreduce u, ?_⟩
    · rw [← hM] at hu
      exact hu
    · exact (hpath (u.map f) _ _).mpr ⟨u, rfl, rfl⟩

theorem regular_empty {Γ : Type} [Fintype Γ] (rep : DomainRep Γ) (n : ℕ) :
    RegularRel rep n ∅ := by
  have h : relLang rep.L rep.ν n ∅ = (0 : Language (Fin n → Option Γ)) := by
    ext w
    simp [relLang, Language.zero_def]
  rw [RegularRel, h]
  exact language_regular_empty

end MFOTLMon.Monitor

namespace MFOTLMon.Monitor

open Classical

variable {Γ : Type}

/-- A track consists of a word followed by padding, with no letters after padding starts. -/
def PaddedWord : List (Option Γ) → Prop
  | [] => True
  | none :: w => ∀ a ∈ w, a = none
  | some _ :: w => PaddedWord w

theorem paddedWord_replicate (n : ℕ) : PaddedWord (List.replicate n (none : Option Γ)) := by
  cases n with
  | zero => trivial
  | succ n =>
      intro a ha
      exact (List.mem_replicate.mp ha).2

theorem paddedWord_map_append (u : List Γ) (n : ℕ) :
    PaddedWord (u.map some ++ List.replicate n none) := by
  induction u with
  | nil => exact paddedWord_replicate n
  | cons a u ih => exact ih

theorem paddedWord_iff (w : List (Option Γ)) :
    PaddedWord w ↔ ∃ (u : List Γ) (n : ℕ), w = u.map some ++ List.replicate n none := by
  constructor
  · intro hw
    induction w with
    | nil => exact ⟨[], 0, rfl⟩
    | cons a w ih =>
      cases a with
      | none =>
          have ht : w = List.replicate w.length none := List.eq_replicate_iff.mpr ⟨rfl, hw⟩
          refine ⟨[], w.length + 1, ?_⟩
          simpa only [List.map_nil, List.nil_append, List.replicate_succ] using
            congrArg (List.cons none) ht
      | some a =>
          obtain ⟨u, n, hu⟩ := ih hw
          exact ⟨a :: u, n, by simp [hu]⟩
  · rintro ⟨u, n, rfl⟩
    exact paddedWord_map_append u n

theorem language_regular_paddedWord :
    Language.IsRegular ({w | PaddedWord w} : Language (Option Γ)) := by
  let M : DFA (Option Γ) (Option Bool) :=
    { step := fun s a ↦ match s, a with
        | none, _ => none
        | some false, some _ => some false
        | some false, none => some true
        | some true, none => some true
        | some true, some _ => none
      start := some false
      accept := {s | s.isSome} }
  have hdead (w : List (Option Γ)) : M.evalFrom none w = none := by
    induction w with
    | nil => rfl
    | cons a w ih => exact ih
  have hlocked (w : List (Option Γ)) :
      M.evalFrom (some true) w ∈ M.accept ↔ ∀ a ∈ w, a = none := by
    induction w with
    | nil => simp [M, DFA.evalFrom_nil]
    | cons a w ih =>
        cases a <;> simp [DFA.evalFrom_cons, M, hdead, ih]
  have hstart (w : List (Option Γ)) : M.evalFrom (some false) w ∈ M.accept ↔ PaddedWord w := by
    induction w with
    | nil => simp [M, PaddedWord, DFA.evalFrom_nil]
    | cons a w ih =>
        cases a <;> simp [DFA.evalFrom_cons, M, hlocked, PaddedWord, ih]
  refine ⟨Option Bool, inferInstance, M, ?_⟩
  ext w
  exact hstart w

theorem language_regular_padded {L : Language Γ} (hL : L.IsRegular) :
    Language.IsRegular
      ({w : List (Option Γ) | PaddedWord w ∧ w.reduceOption ∈ L} : Language (Option Γ)) := by
  have he : ({w : List (Option Γ) | PaddedWord w ∧ w.reduceOption ∈ L} : Language (Option Γ)) =
      ({w | PaddedWord w} : Language (Option Γ)) ⊓
        (List.filterMap id ⁻¹' L : Language (Option Γ)) := by
    ext w
    rfl
  rw [he]
  exact language_regular_paddedWord.inf (language_regular_preimage_filterMap id hL)

theorem optionPad_eq (u : List Γ) (n : ℕ) (h : u.length ≤ n) :
    (List.ofFn (n := n) fun p ↦ u[(p : ℕ)]?) =
      u.map some ++ List.replicate (n - u.length) none := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_map, List.length_replicate]
    omega
  · intro j hj hj'
    by_cases hju : j < u.length
    · simp [hju]
    · have hge : u.length ≤ j := by omega
      simp [List.getElem_append, hju]

theorem conv_track {n : ℕ} (ws : Fin n → List Γ) (i : Fin n) :
    (conv ws).map (fun c ↦ c i) =
      (ws i).map some ++ List.replicate ((conv ws).length - (ws i).length) none := by
  have hlen : (ws i).length ≤ Finset.univ.sup (fun j ↦ (ws j).length) :=
    Finset.le_sup (f := fun j ↦ (ws j).length) (Finset.mem_univ i)
  simpa only [conv, List.map_ofFn, Function.comp_def, List.length_ofFn] using
    optionPad_eq (ws i) _ hlen

theorem conv_track_reduceOption {n : ℕ} (ws : Fin n → List Γ) (i : Fin n) :
    ((conv ws).map (fun c ↦ c i)).reduceOption = ws i := by
  rw [conv_track, List.reduceOption_append, List.reduceOption_replicate_none, List.append_nil]
  change ((ws i).map some).filterMap id = ws i
  simp only [List.filterMap_map, Function.comp_def, id_eq, List.filterMap_some]

end MFOTLMon.Monitor

namespace MFOTLMon.Monitor

open Classical

variable {Γ : Type}

/-- The final column is active, with the empty word allowed. -/
def LastActive {n : ℕ} (w : List (Fin n → Option Γ)) : Prop :=
  match w.getLast? with
  | none => True
  | some c => ∃ i, c i ≠ none

theorem lastActive_iff {n : ℕ} (w : List (Fin n → Option Γ)) :
    LastActive w ↔ w = [] ∨
      ∃ (u : List (Fin n → Option Γ)) (c : Fin n → Option Γ),
        w = u ++ [c] ∧ ∃ i, c i ≠ none := by
  constructor
  · intro h
    cases hl : w.getLast? with
    | none => exact Or.inl (List.getLast?_eq_none_iff.mp hl)
    | some c =>
      obtain ⟨u, hu⟩ := List.getLast?_eq_some_iff.mp hl
      exact Or.inr ⟨u, c, hu, by simpa only [LastActive, hl] using h⟩
  · rintro (rfl | ⟨u, c, rfl, hc⟩)
    · trivial
    · simpa only [LastActive, List.getLast?_append, List.getLast?_singleton,
        Option.some_or] using hc

theorem language_regular_lastActive (n : ℕ) :
    Language.IsRegular ({w : List (Fin n → Option Γ) | LastActive w} :
      Language (Fin n → Option Γ)) := by
  let M : DFA (Fin n → Option Γ) Bool :=
    { step := fun _ c ↦ decide (∃ i, c i ≠ none)
      start := true
      accept := {b | b = true} }
  have heval (s : Bool) (w : List (Fin n → Option Γ)) :
      M.evalFrom s w = match w.getLast? with
        | none => s
        | some c => decide (∃ i, c i ≠ none) := by
    induction w using List.reverseRecOn with
    | nil => rfl
    | append_singleton w c _ =>
      simp only [DFA.evalFrom_append_singleton, M, List.getLast?_append,
        List.getLast?_singleton, Option.some_or]
  refine ⟨Bool, inferInstance, M, ?_⟩
  ext w
  change M.evalFrom true w = true ↔ LastActive w
  rw [heval]
  cases hl : w.getLast? <;> simp only [LastActive, hl, decide_eq_true_eq]

theorem paddedWord_reconstruct (w : List (Option Γ)) (hw : PaddedWord w) :
    w = w.reduceOption.map some ++ List.replicate (w.length - w.reduceOption.length) none := by
  obtain ⟨u, k, rfl⟩ := (paddedWord_iff w).mp hw
  have hs : (u.map some).reduceOption = u := by
    change (u.map some).filterMap id = u
    simp only [List.filterMap_map, Function.comp_def, id_eq, List.filterMap_some]
  simp [List.reduceOption_append, hs]

theorem paddedWord_length_of_last (w : List (Option Γ)) (hw : PaddedWord w) (a : Γ)
    (hlast : w.getLast? = some (some a)) : w.reduceOption.length = w.length := by
  obtain ⟨u, k, rfl⟩ := (paddedWord_iff w).mp hw
  have hs : (u.map some).reduceOption = u := by
    change (u.map some).filterMap id = u
    simp only [List.filterMap_map, Function.comp_def, id_eq, List.filterMap_some]
  cases k with
  | zero => simp [hs]
  | succ k =>
    simp [List.getLast?_append, List.getLast?_replicate] at hlast

theorem conv_lastActive {n : ℕ} (ws : Fin n → List Γ) : LastActive (conv ws) := by
  cases hl : (conv ws).getLast? with
  | none => simp only [LastActive, hl]
  | some c =>
    rw [LastActive, hl]
    cases n with
    | zero => simp [conv] at hl
    | succ n =>
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
        (fun i : Fin (n + 1) ↦ (ws i).length)
      have hlen : (conv ws).length = (ws i).length := by
        simpa only [conv, List.length_ofFn] using hi
      have ht := congrArg List.getLast? (conv_track ws i)
      simp only [hlen, Nat.sub_self, List.replicate_zero, List.append_nil,
        List.getLast?_map, hl, Option.map_some] at ht
      cases hiLast : (ws i).getLast? with
      | none => simp [hiLast] at ht
      | some a =>
        have he : c i = some a := by
          simpa only [hiLast, Option.map_some, Option.some.injEq] using ht
        exact ⟨i, by rw [he]; exact Option.some_ne_none a⟩

theorem conv_decoded_eq {n : ℕ} (w : List (Fin n → Option Γ))
    (htracks : ∀ i, PaddedWord (w.map (fun c ↦ c i))) (hactive : LastActive w) :
    conv (fun i ↦ (w.map (fun c ↦ c i)).reduceOption) = w := by
  let ws : Fin n → List Γ := fun i ↦ (w.map (fun c ↦ c i)).reduceOption
  have hbound (i : Fin n) : (ws i).length ≤ w.length := by
    simpa only [ws, List.length_map] using
      List.reduceOption_length_le (w.map (fun c ↦ c i))
  have hle : Finset.univ.sup (fun i ↦ (ws i).length) ≤ w.length :=
    Finset.sup_le fun i _ ↦ hbound i
  have hge : w.length ≤ Finset.univ.sup (fun i ↦ (ws i).length) := by
    cases hl : w.getLast? with
    | none =>
      have hw : w = [] := List.getLast?_eq_none_iff.mp hl
      simp only [hw, List.length_nil, Nat.zero_le]
    | some c =>
      obtain ⟨i, hi⟩ : ∃ i, c i ≠ none := by simpa only [LastActive, hl] using hactive
      cases hci : c i with
      | none => exact False.elim (hi hci)
      | some a =>
        have ht : (w.map (fun c ↦ c i)).getLast? = some (some a) := by
          simp only [List.getLast?_map, hl, Option.map_some, hci]
        have he : (ws i).length = w.length := by
          simpa only [ws, List.length_map] using
            paddedWord_length_of_last _ (htracks i) a ht
        have hb : (ws i).length ≤ Finset.univ.sup (fun i ↦ (ws i).length) :=
          Finset.le_sup (f := fun i ↦ (ws i).length) (Finset.mem_univ i)
        omega
  have hlen : (conv ws).length = w.length := by
    simpa only [conv, List.length_ofFn] using le_antisymm hle hge
  have hmap (i : Fin n) : (conv ws).map (fun c ↦ c i) = w.map (fun c ↦ c i) := by
    rw [conv_track, hlen]
    simpa only [ws, List.length_map] using (paddedWord_reconstruct _ (htracks i)).symm
  apply List.ext_getElem hlen
  intro j hj hk
  funext i
  have he := congrArg (fun u : List (Option Γ) ↦ u[j]?) (hmap i)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem hk, Option.map_some, Option.some.injEq] at he
  exact he

theorem relLang_univ_iff (L : Language Γ) (ν : List Γ → ℕ) (n : ℕ)
    (w : List (Fin n → Option Γ)) :
    w ∈ relLang L ν n Set.univ ↔
      (∀ i, PaddedWord (w.map (fun c ↦ c i)) ∧
        (w.map (fun c ↦ c i)).reduceOption ∈ L) ∧ LastActive w := by
  constructor
  · rintro ⟨ws, hw, _, rfl⟩
    refine ⟨?_, conv_lastActive ws⟩
    intro i
    constructor
    · rw [conv_track]
      exact paddedWord_map_append _ _
    · rw [conv_track_reduceOption]
      exact hw i
  · rintro ⟨htracks, hactive⟩
    exact ⟨fun i ↦ (w.map (fun c ↦ c i)).reduceOption,
      fun i ↦ (htracks i).2, Set.mem_univ _,
      conv_decoded_eq w (fun i ↦ (htracks i).1) hactive⟩

private theorem valid_regular_forall {ι α : Type} [Fintype ι] (P : ι → Language α)
    (hP : ∀ i, (P i).IsRegular) : Language.IsRegular ({w | ∀ i, w ∈ P i} : Language α) := by
  have hf (s : Finset ι) : Language.IsRegular ({w | ∀ i ∈ s, w ∈ P i} : Language α) := by
    induction s using Finset.induction_on with
    | empty =>
      have he : ({w | ∀ i ∈ (∅ : Finset ι), w ∈ P i} : Language α) = (⊤ : Language α) := by
        ext w
        change (∀ i ∈ (∅ : Finset ι), w ∈ P i) ↔ True
        simp
      rw [he]
      exact language_regular_univ
    | @insert i s hi ih =>
      have he : ({w | ∀ j ∈ insert i s, w ∈ P j} : Language α) =
          P i ⊓ ({w | ∀ j ∈ s, w ∈ P j} : Language α) := by
        ext w
        change (∀ j ∈ insert i s, w ∈ P j) ↔ w ∈ P i ∧ ∀ j ∈ s, w ∈ P j
        simp only [Finset.mem_insert, forall_eq_or_imp]
      rw [he]
      exact (hP i).inf ih
  have huniv : ({w | ∀ i, w ∈ P i} : Language α) =
      ({w | ∀ i ∈ (Finset.univ : Finset ι), w ∈ P i} : Language α) := by
    ext w
    change (∀ i, w ∈ P i) ↔ ∀ i ∈ (Finset.univ : Finset ι), w ∈ P i
    simp
  rw [huniv]
  exact hf Finset.univ

theorem valid_convolution_regular {Γ : Type} [Fintype Γ] (rep : DomainRep Γ) (n : ℕ) :
    (relLang rep.L rep.ν n Set.univ).IsRegular := by
  have htracks :
      Language.IsRegular ({w : List (Fin n → Option Γ) | ∀ i : Fin n,
        PaddedWord (w.map (fun c ↦ c i)) ∧
        (w.map (fun c ↦ c i)).reduceOption ∈ rep.L} : Language (Fin n → Option Γ)) := by
    exact valid_regular_forall
      (fun i ↦ List.map (fun c : Fin n → Option Γ ↦ c i) ⁻¹'
        ({u | PaddedWord u ∧ u.reduceOption ∈ rep.L} : Language (Option Γ)))
      (fun i ↦ language_regular_preimage_map (fun c : Fin n → Option Γ ↦ c i)
        (language_regular_padded rep.L_regular))
  have h := htracks.inf (language_regular_lastActive (Γ := Γ) n)
  have he : relLang rep.L rep.ν n Set.univ =
      ({w : List (Fin n → Option Γ) | (∀ i : Fin n,
        PaddedWord (w.map (fun c ↦ c i)) ∧
        (w.map (fun c ↦ c i)).reduceOption ∈ rep.L) ∧ LastActive w} :
        Language (Fin n → Option Γ)) := by
    ext w
    exact relLang_univ_iff rep.L rep.ν n w
  rw [he]
  exact h

end MFOTLMon.Monitor

namespace MFOTLMon.Monitor

open Classical

variable {S : Signature} {Γ : Type}

theorem conv_injective {n : ℕ} : Function.Injective (conv (Γ := Γ) (k := n)) := by
  intro ws₁ ws₂ h
  funext i
  rw [← conv_track_reduceOption ws₁ i, ← conv_track_reduceOption ws₂ i, h]

theorem relLang_congr {L : Language Γ} {ν : List Γ → ℕ} {n : ℕ} {A B : Set (List ℕ)}
    (h : ∀ ds : List ℕ, ds.length = n → (ds ∈ A ↔ ds ∈ B)) :
    relLang L ν n A = relLang L ν n B := by
  ext w
  simp only [relLang]
  apply exists_congr
  intro ws
  exact and_congr_right fun _ ↦ and_congr_left fun _ ↦ h _ List.length_ofFn

theorem regular_congr [Fintype Γ] {rep : DomainRep Γ} {n : ℕ} {A B : Set (List ℕ)}
    (h : ∀ ds : List ℕ, ds.length = n → (ds ∈ A ↔ ds ∈ B))
    (hA : RegularRel rep n A) : RegularRel rep n B := by
  rwa [RegularRel, ← relLang_congr h]

theorem regular_univ [Fintype Γ] (rep : DomainRep Γ) (n : ℕ) :
    RegularRel rep n Set.univ :=
  valid_convolution_regular rep n

theorem relLang_union (L : Language Γ) (ν : List Γ → ℕ) (n : ℕ) (A B : Set (List ℕ)) :
    relLang L ν n (A ∪ B) = relLang L ν n A + relLang L ν n B := by
  ext w
  change (∃ ws, (∀ i, ws i ∈ L) ∧ (List.ofFn (fun i ↦ ν (ws i)) ∈ A ∨
    List.ofFn (fun i ↦ ν (ws i)) ∈ B) ∧ conv ws = w) ↔
    (∃ ws, (∀ i, ws i ∈ L) ∧ List.ofFn (fun i ↦ ν (ws i)) ∈ A ∧ conv ws = w) ∨
    (∃ ws, (∀ i, ws i ∈ L) ∧ List.ofFn (fun i ↦ ν (ws i)) ∈ B ∧ conv ws = w)
  aesop

theorem regular_union [Fintype Γ] {rep : DomainRep Γ} {n : ℕ} {A B : Set (List ℕ)}
    (hA : RegularRel rep n A) (hB : RegularRel rep n B) :
    RegularRel rep n (A ∪ B) := by
  rw [RegularRel, relLang_union]
  exact hA.add hB

theorem relLang_inter (L : Language Γ) (ν : List Γ → ℕ) (n : ℕ) (A B : Set (List ℕ)) :
    relLang L ν n (A ∩ B) = relLang L ν n A ⊓ relLang L ν n B := by
  ext w
  change (∃ ws, (∀ i, ws i ∈ L) ∧ (List.ofFn (fun i ↦ ν (ws i)) ∈ A ∧
    List.ofFn (fun i ↦ ν (ws i)) ∈ B) ∧ conv ws = w) ↔
    (∃ ws, (∀ i, ws i ∈ L) ∧ List.ofFn (fun i ↦ ν (ws i)) ∈ A ∧ conv ws = w) ∧
    (∃ ws, (∀ i, ws i ∈ L) ∧ List.ofFn (fun i ↦ ν (ws i)) ∈ B ∧ conv ws = w)
  constructor
  · rintro ⟨ws, hL, ⟨hA, hB⟩, rfl⟩
    exact ⟨⟨ws, hL, hA, rfl⟩, ⟨ws, hL, hB, rfl⟩⟩
  · rintro ⟨⟨ws₁, hL₁, hA, rfl⟩, ⟨ws₂, _, hB, hconv⟩⟩
    have heq := conv_injective hconv
    subst ws₂
    exact ⟨ws₁, hL₁, ⟨hA, hB⟩, rfl⟩

theorem regular_inter [Fintype Γ] {rep : DomainRep Γ} {n : ℕ} {A B : Set (List ℕ)}
    (hA : RegularRel rep n A) (hB : RegularRel rep n B) :
    RegularRel rep n (A ∩ B) := by
  rw [RegularRel, relLang_inter]
  exact hA.inf hB

theorem relLang_compl (L : Language Γ) (ν : List Γ → ℕ) (n : ℕ) (A : Set (List ℕ)) :
    relLang L ν n Aᶜ = relLang L ν n Set.univ ⊓ (relLang L ν n A)ᶜ := by
  ext w
  change (∃ ws, (∀ i, ws i ∈ L) ∧ List.ofFn (fun i ↦ ν (ws i)) ∉ A ∧ conv ws = w) ↔
    (∃ ws, (∀ i, ws i ∈ L) ∧ List.ofFn (fun i ↦ ν (ws i)) ∈ Set.univ ∧ conv ws = w) ∧
    ¬ (∃ ws, (∀ i, ws i ∈ L) ∧ List.ofFn (fun i ↦ ν (ws i)) ∈ A ∧ conv ws = w)
  constructor
  · rintro ⟨ws, hL, hnotA, rfl⟩
    refine ⟨⟨ws, hL, trivial, rfl⟩, ?_⟩
    rintro ⟨ws', _, hA, hconv⟩
    have heq := conv_injective hconv
    subst ws'
    exact hnotA hA
  · rintro ⟨⟨ws, hL, _, rfl⟩, hnot⟩
    refine ⟨ws, hL, ?_, rfl⟩
    intro hA
    exact hnot ⟨ws, hL, hA, rfl⟩

theorem regular_compl [Fintype Γ] {rep : DomainRep Γ} {n : ℕ} {A : Set (List ℕ)}
    (hA : RegularRel rep n A) : RegularRel rep n Aᶜ := by
  rw [RegularRel, relLang_compl]
  exact (regular_univ rep n).inf hA.compl

theorem regular_finset_union [Fintype Γ] {ι : Type} (rep : DomainRep Γ) (n : ℕ)
    (s : Finset ι) (P : ι → Set (List ℕ)) (hP : ∀ i ∈ s, RegularRel rep n (P i)) :
    RegularRel rep n {ds | ∃ i ∈ s, ds ∈ P i} := by
  induction s using Finset.induction_on with
  | empty =>
    refine regular_congr (A := ∅) (fun ds _ ↦ ?_) (regular_empty rep n)
    simp
  | @insert i s hi ih =>
    have h₁ := hP i (Finset.mem_insert_self i s)
    have h₂ := ih (fun j hj ↦ hP j (Finset.mem_insert_of_mem hj))
    refine regular_congr (fun ds _ ↦ ?_) (regular_union h₁ h₂)
    change (ds ∈ P i ∨ ∃ j ∈ s, ds ∈ P j) ↔ ∃ j ∈ insert i s, ds ∈ P j
    simp only [Finset.mem_insert, exists_eq_or_imp]

theorem regular_finset_inter [Fintype Γ] {ι : Type} (rep : DomainRep Γ) (n : ℕ)
    (s : Finset ι) (P : ι → Set (List ℕ)) (hP : ∀ i ∈ s, RegularRel rep n (P i)) :
    RegularRel rep n {ds | ∀ i ∈ s, ds ∈ P i} := by
  induction s using Finset.induction_on with
  | empty =>
    refine regular_congr (A := Set.univ) (fun ds _ ↦ ?_) (regular_univ rep n)
    simp
  | @insert i s hi ih =>
    have h₁ := hP i (Finset.mem_insert_self i s)
    have h₂ := ih (fun j hj ↦ hP j (Finset.mem_insert_of_mem hj))
    refine regular_congr (fun ds _ ↦ ?_) (regular_inter h₁ h₂)
    change (ds ∈ P i ∧ ∀ j ∈ s, ds ∈ P j) ↔ ∀ j ∈ insert i s, ds ∈ P j
    simp only [Finset.mem_insert, forall_eq_or_imp]

def projLetter {m n : ℕ} (f : Fin m → Fin n) (c : Fin n → Option Γ) :
    Option (Fin m → Option Γ) :=
  if ∀ i : Fin m, c (f i) = none then none else some (fun i ↦ c (f i))

private theorem ofFn_eq_map_range {α : Type} (N : ℕ) (h : ℕ → α) :
    List.ofFn (n := N) (fun p : Fin N ↦ h (p : ℕ)) = (List.range N).map h := by
  apply List.ext_getElem
  · simp
  · intro j hj₁ hj₂
    simp

theorem filterMap_projLetter_conv {m n : ℕ} (f : Fin m → Fin n) (ws : Fin n → List Γ) :
    (conv ws).filterMap (projLetter f) = conv (ws ∘ f) := by
  let L₁ := Finset.univ.sup fun j : Fin n ↦ (ws j).length
  let L₂ := Finset.univ.sup fun i : Fin m ↦ (ws (f i)).length
  have hle : L₂ ≤ L₁ := by
    apply Finset.sup_le
    intro i _
    exact Finset.le_sup (f := fun j : Fin n ↦ (ws j).length) (Finset.mem_univ (f i))
  let h₁ : ℕ → (Fin n → Option Γ) := fun p j ↦ (ws j)[p]?
  let h₂ : ℕ → (Fin m → Option Γ) := fun p i ↦ (ws (f i))[p]?
  have hlt (p : ℕ) (hp : p < L₂) : projLetter f (h₁ p) = some (h₂ p) := by
    obtain ⟨i, _, hi⟩ := Finset.lt_sup_iff.mp hp
    have hne : ¬ (∀ i' : Fin m, h₁ p (f i') = none) := by
      intro hall
      have hnone := hall i
      change (ws (f i))[p]? = none at hnone
      rw [List.getElem?_eq_getElem hi] at hnone
      exact Option.some_ne_none _ hnone
    simp only [projLetter, if_neg hne]
    rfl
  have hge (p : ℕ) (hp : L₂ ≤ p) : projLetter f (h₁ p) = none := by
    have hall : ∀ i : Fin m, h₁ p (f i) = none := by
      intro i
      change (ws (f i))[p]? = none
      have hlen : (ws (f i)).length ≤ L₂ :=
        Finset.le_sup (f := fun i' : Fin m ↦ (ws (f i')).length) (Finset.mem_univ i)
      exact List.getElem?_eq_none (by omega)
    simp only [projLetter, if_pos hall]
  have hprefix (k : ℕ) (hk : k ≤ L₂) :
      ((List.range k).map h₁).filterMap (projLetter f) = (List.range k).map h₂ := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.filterMap_append, List.map_append,
        ih (by omega)]
      simp [hlt k (by omega)]
  have hsuffix (d : ℕ) :
      ((List.range (L₂ + d)).map h₁).filterMap (projLetter f) = (List.range L₂).map h₂ := by
    induction d with
    | zero => exact hprefix L₂ le_rfl
    | succ d ih =>
      rw [← Nat.add_assoc, List.range_succ, List.map_append, List.filterMap_append, ih]
      simp [hge (L₂ + d) (by omega)]
  change (List.ofFn (n := L₁) (fun p ↦ h₁ (p : ℕ))).filterMap (projLetter f) =
    List.ofFn (n := L₂) (fun p ↦ h₂ (p : ℕ))
  rw [ofFn_eq_map_range L₁ h₁, ofFn_eq_map_range L₂ h₂]
  have hL₁ : L₁ = L₂ + (L₁ - L₂) := by omega
  rw [hL₁]
  exact hsuffix (L₁ - L₂)

theorem regular_pullback [Fintype Γ] {rep : DomainRep Γ} {m n : ℕ} (f : Fin m → Fin n)
    {A : Set (List ℕ)} (hA : RegularRel rep m A) :
    RegularRel rep n {ds | ds.length = n ∧
      List.ofFn (fun i : Fin m ↦ ds.getD (f i) 0) ∈ A} := by
  have hget (ws : Fin n → List Γ) :
      List.ofFn (fun i : Fin m ↦ (List.ofFn (fun j : Fin n ↦ rep.ν (ws j))).getD (f i) 0) =
        List.ofFn (fun i : Fin m ↦ rep.ν ((ws ∘ f) i)) := by
    apply List.ext_getElem (by simp)
    intro i hi₁ hi₂
    simp
  have he : relLang rep.L rep.ν n {ds | ds.length = n ∧
      List.ofFn (fun i : Fin m ↦ ds.getD (f i) 0) ∈ A} =
      relLang rep.L rep.ν n Set.univ ⊓
        (List.filterMap (projLetter f) ⁻¹' relLang rep.L rep.ν m A) := by
    ext w
    change (∃ ws, (∀ j, ws j ∈ rep.L) ∧
      (List.ofFn (fun j ↦ rep.ν (ws j)) ∈ {ds | ds.length = n ∧
        List.ofFn (fun i : Fin m ↦ ds.getD (f i) 0) ∈ A}) ∧ conv ws = w) ↔
      (∃ ws, (∀ j, ws j ∈ rep.L) ∧ List.ofFn (fun j ↦ rep.ν (ws j)) ∈ Set.univ ∧ conv ws = w) ∧
      w.filterMap (projLetter f) ∈ relLang rep.L rep.ν m A
    constructor
    · rintro ⟨ws, hL, ⟨_, hmem⟩, rfl⟩
      rw [hget ws] at hmem
      refine ⟨⟨ws, hL, trivial, rfl⟩, ?_⟩
      rw [filterMap_projLetter_conv]
      exact ⟨ws ∘ f, fun i ↦ hL (f i), hmem, rfl⟩
    · rintro ⟨⟨ws, hL, _, rfl⟩, hmem⟩
      rw [filterMap_projLetter_conv] at hmem
      obtain ⟨us, _, hus, hconv⟩ := hmem
      have heq := conv_injective hconv
      subst us
      refine ⟨ws, hL, ⟨List.length_ofFn, ?_⟩, rfl⟩
      rw [hget ws]
      exact hus
  rw [RegularRel, he]
  exact (regular_univ rep n).inf (language_regular_preimage_filterMap (projLetter f) hA)

private def snocWord {α : Type} {n : ℕ} (ws : Fin n → α) (u : α) (j : Fin (n + 1)) : α :=
  if h : (j : ℕ) < n then ws ⟨j, h⟩ else u

private theorem snocWord_castSucc {α : Type} {n : ℕ} (ws : Fin n → α) (u : α) (i : Fin n) :
    snocWord ws u i.castSucc = ws i := by
  simp [snocWord, i.isLt]

private theorem snocWord_last {α : Type} {n : ℕ} (ws : Fin n → α) (u : α) :
    snocWord ws u (Fin.last n) = u := by
  simp [snocWord]

private theorem ofFn_succ_append {α : Type} {n : ℕ} (g : Fin (n + 1) → α) :
    List.ofFn g = List.ofFn (fun i : Fin n ↦ g i.castSucc) ++ [g (Fin.last n)] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ (f := g),
      List.ofFn_succ (f := fun i : Fin (n + 1) ↦ g i.castSucc), List.cons_append]
    exact congrArg (List.cons (g 0)) (ih (fun i ↦ g i.succ))

theorem regular_projLast [Fintype Γ] {rep : DomainRep Γ} {n : ℕ} {A : Set (List ℕ)}
    (hA : RegularRel rep (n + 1) A) :
    RegularRel rep n {ds | ds.length = n ∧ ∃ d : ℕ, ds ++ [d] ∈ A} := by
  have he : relLang rep.L rep.ν n {ds | ds.length = n ∧ ∃ d : ℕ, ds ++ [d] ∈ A} =
      List.filterMap (projLetter (Fin.castSucc : Fin n → Fin (n + 1))) ''
        relLang rep.L rep.ν (n + 1) A := by
    ext w
    change (∃ ws, (∀ i, ws i ∈ rep.L) ∧
      (List.ofFn (fun i ↦ rep.ν (ws i)) ∈ {ds | ds.length = n ∧ ∃ d : ℕ, ds ++ [d] ∈ A}) ∧
      conv ws = w) ↔
      ∃ v ∈ relLang rep.L rep.ν (n + 1) A,
        v.filterMap (projLetter (Fin.castSucc : Fin n → Fin (n + 1))) = w
    constructor
    · rintro ⟨ws, hL, ⟨_, d, hd⟩, rfl⟩
      obtain ⟨u, huL, rfl⟩ := rep.ν_surj d
      let ws' : Fin (n + 1) → List Γ := snocWord ws u
      have hL' (j : Fin (n + 1)) : ws' j ∈ rep.L := by
        dsimp only [ws', snocWord]
        split_ifs with h
        · exact hL ⟨j, h⟩
        · exact huL
      have hcomp : ws' ∘ Fin.castSucc = ws := by
        funext i
        exact snocWord_castSucc ws u i
      have hofFn : List.ofFn (fun j : Fin (n + 1) ↦ rep.ν (ws' j)) =
          List.ofFn (fun i : Fin n ↦ rep.ν (ws i)) ++ [rep.ν u] := by
        rw [ofFn_succ_append]
        simp only [ws', snocWord_castSucc, snocWord_last]
      refine ⟨conv ws', ⟨ws', hL', ?_, rfl⟩, ?_⟩
      · rwa [hofFn]
      · rw [filterMap_projLetter_conv, hcomp]
    · rintro ⟨v, ⟨ws', hL', hmem, rfl⟩, rfl⟩
      rw [filterMap_projLetter_conv]
      refine ⟨ws' ∘ Fin.castSucc, fun i ↦ hL' i.castSucc,
        ⟨List.length_ofFn, rep.ν (ws' (Fin.last n)), ?_⟩, rfl⟩
      rw [ofFn_succ_append] at hmem
      exact hmem
  rw [RegularRel, he]
  exact language_regular_image_filterMap _ hA

theorem language_regular_singleton {α : Type} (u : List α) :
    Language.IsRegular ({u} : Language α) := by
  induction u with
  | nil =>
    let M : DFA α Bool :=
      { step := fun _ _ ↦ false
        start := true
        accept := {b | b = true} }
    have hfalse (w : List α) : M.evalFrom false w = false := by
      induction w with
      | nil => rfl
      | cons _ _ ih => exact ih
    refine ⟨Bool, inferInstance, M, ?_⟩
    ext w
    change M.evalFrom true w = true ↔ w = []
    cases w with
    | nil => simp [DFA.evalFrom_nil]
    | cons a w =>
      rw [DFA.evalFrom_cons]
      change M.evalFrom false w = true ↔ a :: w = []
      rw [hfalse]
      simp
  | cons a u ih =>
    obtain ⟨σ, hσ, M, hM⟩ := ih
    let N : DFA α (Option (Option σ)) :=
      { step := fun s b ↦ match s with
          | none => none
          | some none => if b = a then some (some M.start) else none
          | some (some q) => some (some (M.step q b))
        start := some none
        accept := {s | match s with | some (some q) => q ∈ M.accept | _ => False} }
    have hnone (w : List α) : N.evalFrom none w = none := by
      induction w with
      | nil => rfl
      | cons _ _ ihw => exact ihw
    have hsome (q : σ) (w : List α) :
        N.evalFrom (some (some q)) w = some (some (M.evalFrom q w)) := by
      induction w generalizing q with
      | nil => rfl
      | cons b w ihw => exact ihw (M.step q b)
    refine ⟨Option (Option σ), inferInstance, N, ?_⟩
    ext w
    cases w with
    | nil =>
      change N.evalFrom (some none) [] ∈ N.accept ↔ [] = a :: u
      simp [N, DFA.evalFrom_nil]
    | cons b w =>
      change N.evalFrom (some none) (b :: w) ∈ N.accept ↔ b :: w = a :: u
      rw [DFA.evalFrom_cons]
      dsimp only [N]
      by_cases hba : b = a
      · subst b
        rw [if_pos rfl, hsome]
        change w ∈ M.accepts ↔ a :: w = a :: u
        rw [hM]
        exact (List.cons_eq_cons.trans (and_iff_right rfl)).symm
      · rw [if_neg hba, hnone]
        simp [hba]

theorem regular_const [Fintype Γ] (rep : DomainRep Γ) (c : ℕ) :
    RegularRel rep 1 {[c]} := by
  obtain ⟨u, huL, rfl⟩ := rep.ν_surj c
  let L₂ : Language (Fin 2 → Option Γ) :=
    relLang rep.L rep.ν 2 {l | ∃ d : ℕ, l = [d, d]} ⊓
      (List.map (fun x : Fin 2 → Option Γ ↦ x 1) ⁻¹'
        (List.filterMap id ⁻¹' ({u} : Language Γ)))
  have hL₂ : L₂.IsRegular :=
    rep.eq_regular.inf
      (language_regular_preimage_map _
        (language_regular_preimage_filterMap id (language_regular_singleton u)))
  have he : relLang rep.L rep.ν 1 {[rep.ν u]} =
      List.filterMap (projLetter (Fin.castSucc : Fin 1 → Fin 2)) '' L₂ := by
    ext w
    change (∃ ws, (∀ i, ws i ∈ rep.L) ∧
      List.ofFn (fun i : Fin 1 ↦ rep.ν (ws i)) = [rep.ν u] ∧ conv ws = w) ↔
      ∃ v ∈ L₂, v.filterMap (projLetter (Fin.castSucc : Fin 1 → Fin 2)) = w
    constructor
    · rintro ⟨ws, hL, hν, rfl⟩
      have hν0 : rep.ν (ws 0) = rep.ν u := by
        simpa only [List.ofFn_succ, List.ofFn_zero, List.cons.injEq, and_true] using hν
      let ws' : Fin 2 → List Γ := snocWord ws u
      have hL' (j : Fin 2) : ws' j ∈ rep.L := by
        dsimp only [ws', snocWord]
        split_ifs with h
        · exact hL ⟨j, h⟩
        · exact huL
      have hcomp : ws' ∘ Fin.castSucc = ws := by
        funext i
        exact snocWord_castSucc ws u i
      have hws0 : ws' 0 = ws 0 := snocWord_castSucc ws u 0
      have hws1 : ws' 1 = u := snocWord_last ws u
      refine ⟨conv ws', ⟨⟨ws', hL', ⟨rep.ν u, ?_⟩, rfl⟩, ?_⟩, ?_⟩
      · simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, hws0, hws1, hν0]
      · change ((conv ws').map (fun x : Fin 2 → Option Γ ↦ x 1)).reduceOption ∈ ({u} : Language Γ)
        rw [conv_track_reduceOption, hws1]
        rfl
      · rw [filterMap_projLetter_conv, hcomp]
    · rintro ⟨v, ⟨⟨ws', hL', ⟨d, hd⟩, rfl⟩, htrack⟩, rfl⟩
      change ((conv ws').map (fun x : Fin 2 → Option Γ ↦ x 1)).reduceOption = u at htrack
      rw [conv_track_reduceOption] at htrack
      rw [filterMap_projLetter_conv]
      refine ⟨ws' ∘ Fin.castSucc, fun i ↦ hL' i.castSucc, ?_, rfl⟩
      simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, List.cons.injEq,
        and_true] at hd ⊢
      change rep.ν (ws' 0) = rep.ν u
      rw [hd.1, ← hd.2, htrack]
  rw [RegularRel, he]
  exact language_regular_image_filterMap _ hL₂

private theorem getD_eq_getElem_of_lt (ds : List ℕ) (j : ℕ) (hj : j < ds.length) :
    ds.getD j 0 = ds[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

private theorem getD_append_left (ds cs : List ℕ) (j : ℕ) (hj : j < ds.length) :
    (ds ++ cs).getD j 0 = ds.getD j 0 := by
  have hj' : j < (ds ++ cs).length := by simp; omega
  rw [getD_eq_getElem_of_lt _ _ hj', getD_eq_getElem_of_lt _ _ hj, List.getElem_append_left hj]

private theorem getD_append_right (ds cs : List ℕ) (k : ℕ) :
    (ds ++ cs).getD (ds.length + k) 0 = cs.getD k 0 := by
  by_cases hk : k < cs.length
  · have hk' : ds.length + k < (ds ++ cs).length := by simp; omega
    rw [getD_eq_getElem_of_lt _ _ hk', getD_eq_getElem_of_lt _ _ hk]
    simp [List.getElem_append_right]
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

private theorem getD_append_singleton_last (ds : List ℕ) (c : ℕ) :
    (ds ++ [c]).getD ds.length 0 = c := by
  have h := getD_append_right ds [c] 0
  simpa using h

theorem eq_ofFn_castSucc_append_last (ds : List ℕ) (n : ℕ) (h : ds.length = n + 1) :
    ds = List.ofFn (fun i : Fin n ↦ ds.getD (Fin.castSucc i) 0) ++ [ds.getD n 0] := by
  apply List.ext_getElem
  · simp [h]
  · intro j hj₁ hj₂
    by_cases hj : j < n
    · rw [List.getElem_append_left (by simpa using hj)]
      simp only [List.getElem_ofFn, Fin.val_castSucc]
      exact (getD_eq_getElem_of_lt ds j hj₁).symm
    · have hjeq : j = n := by omega
      subst j
      rw [List.getElem_append_right (by simp)]
      simp only [List.length_ofFn, Nat.sub_self, List.getElem_singleton]
      exact (getD_eq_getElem_of_lt ds n hj₁).symm

theorem regular_append_const [Fintype Γ] {rep : DomainRep Γ} {n : ℕ} {A : Set (List ℕ)}
    (hA : RegularRel rep n A) (c : ℕ) :
    RegularRel rep (n + 1) {ds | ∃ a, a.length = n ∧ a ∈ A ∧ ds = a ++ [c]} := by
  have h₁ := regular_pullback (Fin.castSucc : Fin n → Fin (n + 1)) hA
  have h₂ := regular_pullback (fun _ : Fin 1 ↦ Fin.last n) (regular_const rep c)
  refine regular_congr (fun ds hlen ↦ ?_) (regular_inter h₁ h₂)
  change (ds.length = n + 1 ∧ List.ofFn (fun i : Fin n ↦ ds.getD (Fin.castSucc i) 0) ∈ A) ∧
    (ds.length = n + 1 ∧ List.ofFn (fun _ : Fin 1 ↦ ds.getD (Fin.last n) 0) ∈ ({[c]} : Set (List ℕ))) ↔
    ∃ a, a.length = n ∧ a ∈ A ∧ ds = a ++ [c]
  constructor
  · rintro ⟨⟨_, hA'⟩, ⟨_, hc'⟩⟩
    have hlast : ds.getD n 0 = c := by
      simpa only [List.ofFn_succ, List.ofFn_zero, Set.mem_singleton_iff,
        List.cons.injEq, and_true, Fin.val_last] using hc'
    refine ⟨List.ofFn (fun i : Fin n ↦ ds.getD (Fin.castSucc i) 0), List.length_ofFn, hA', ?_⟩
    rw [← hlast]
    exact eq_ofFn_castSucc_append_last ds n hlen
  · rintro ⟨a, ha_len, haA, rfl⟩
    have htake : List.ofFn (fun i : Fin n ↦ (a ++ [c]).getD (Fin.castSucc i) 0) = a := by
      apply List.ext_getElem (by simp [ha_len])
      intro i hi₁ hi₂
      simp only [List.getElem_ofFn, Fin.val_castSucc]
      rw [getD_append_left a [c] i hi₂, getD_eq_getElem_of_lt a i hi₂]
    have hlast : (a ++ [c]).getD n 0 = c := by
      rw [← ha_len]
      exact getD_append_singleton_last a c
    refine ⟨⟨hlen, ?_⟩, ⟨hlen, ?_⟩⟩
    · rwa [htake]
    · simp only [List.ofFn_succ, List.ofFn_zero, Fin.val_last, hlast, Set.mem_singleton_iff]

theorem regular_spec_last [Fintype Γ] {rep : DomainRep Γ} {n : ℕ} {A : Set (List ℕ)}
    (hA : RegularRel rep (n + 1) A) (c : ℕ) :
    RegularRel rep n {ds | ds.length = n ∧ ds ++ [c] ∈ A} := by
  have h₂ := regular_pullback (fun _ : Fin 1 ↦ Fin.last n) (regular_const rep c)
  have hproj := regular_projLast (regular_inter hA h₂)
  refine regular_congr (fun ds hlen ↦ ?_) hproj
  change (ds.length = n ∧ ∃ d : ℕ, ds ++ [d] ∈ A ∧
    ((ds ++ [d]).length = n + 1 ∧
      List.ofFn (fun _ : Fin 1 ↦ (ds ++ [d]).getD (Fin.last n) 0) ∈ ({[c]} : Set (List ℕ)))) ↔
    ds.length = n ∧ ds ++ [c] ∈ A
  constructor
  · rintro ⟨_, d, hdA, _, hdc⟩
    have hlast : (ds ++ [d]).getD n 0 = d := by
      rw [← hlen]
      exact getD_append_singleton_last ds d
    have hd : d = c := by
      simpa only [List.ofFn_succ, List.ofFn_zero, Set.mem_singleton_iff,
        List.cons.injEq, and_true, Fin.val_last, hlast] using hdc
    subst d
    exact ⟨hlen, hdA⟩
  · rintro ⟨_, hcA⟩
    have hlast : (ds ++ [c]).getD n 0 = c := by
      rw [← hlen]
      exact getD_append_singleton_last ds c
    refine ⟨hlen, c, hcA, by simp [hlen], ?_⟩
    simp only [List.ofFn_succ, List.ofFn_zero, Fin.val_last, hlast, Set.mem_singleton_iff]

theorem regular_spec_append [Fintype Γ] {rep : DomainRep Γ} {n : ℕ} (cs : List ℕ)
    {A : Set (List ℕ)} (hA : RegularRel rep (n + cs.length) A) :
    RegularRel rep n {ds | ds.length = n ∧ ds ++ cs ∈ A} := by
  induction cs generalizing n A with
  | nil =>
    refine regular_congr (fun ds hlen ↦ ?_) hA
    simp [hlen]
  | cons c cs ih =>
    have hA' : RegularRel rep (n + 1 + cs.length) A := by
      simpa only [List.length_cons, Nat.add_right_comm, Nat.add_assoc] using hA
    have h₁ := regular_spec_last (ih hA') c
    refine regular_congr (fun ds hlen ↦ ?_) h₁
    change (ds.length = n ∧ (ds ++ [c]).length = n + 1 ∧ (ds ++ [c]) ++ cs ∈ A) ↔
      ds.length = n ∧ ds ++ (c :: cs) ∈ A
    simp [hlen, List.append_assoc]

theorem regular_evalTerms [Fintype Γ] (rep : DomainRep Γ) (const : S.C → ℕ)
    (xs : List ℕ) {m : ℕ} (ts : Fin m → Term S)
    (hts : ∀ k (x : ℕ), ts k = .inl x → x ∈ xs)
    {A : Set (List ℕ)} (hA : RegularRel rep m A) :
    RegularRel rep xs.length {ds | ds.length = xs.length ∧
      List.ofFn (fun k : Fin m ↦ evalTerm const (assign (fun _ ↦ 0) xs ds) (ts k)) ∈ A} := by
  let n := xs.length
  let cs : List ℕ := List.ofFn (fun k : Fin m ↦ evalTerm const (fun _ ↦ 0) (ts k))
  have hcs : cs.length = m := List.length_ofFn
  let f : Fin m → Fin (n + cs.length) := fun k ↦
    match ts k with
    | .inl x =>
      ⟨xs.idxOf x, by
        have h₁ : xs.idxOf x ≤ n := List.idxOf_le_length
        have h₂ := k.2
        omega⟩
    | .inr _ => ⟨n + k.1, by have := k.2; omega⟩
  have hpull := regular_spec_append cs (regular_pullback f hA)
  refine regular_congr (fun ds hlen ↦ ?_) hpull
  change (ds.length = n ∧ (ds ++ cs).length = n + cs.length ∧
    List.ofFn (fun k : Fin m ↦ (ds ++ cs).getD (f k) 0) ∈ A) ↔
    ds.length = n ∧
      List.ofFn (fun k : Fin m ↦ evalTerm const (assign (fun _ ↦ 0) xs ds) (ts k)) ∈ A
  have heval : List.ofFn (fun k : Fin m ↦ (ds ++ cs).getD (f k) 0) =
      List.ofFn (fun k : Fin m ↦ evalTerm const (assign (fun _ ↦ 0) xs ds) (ts k)) := by
    apply List.ext_getElem (by simp)
    intro k hk₁ hk₂
    simp only [List.getElem_ofFn]
    let k' : Fin m := ⟨k, by simpa using hk₁⟩
    change (ds ++ cs).getD (f k') 0 = evalTerm const (assign (fun _ ↦ 0) xs ds) (ts k')
    cases htk : ts k' with
    | inl x =>
      have hx : x ∈ xs := hts k' x htk
      have hidx : xs.idxOf x < ds.length := by
        rw [hlen]
        exact List.idxOf_lt_length_of_mem hx
      have hf : (f k' : ℕ) = xs.idxOf x := by simp [f, htk]
      rw [hf, getD_append_left ds cs _ hidx, ← assign_on (fun _ ↦ 0) xs ds x hx]
      rfl
    | inr c =>
      have hf : (f k' : ℕ) = ds.length + k'.1 := by
        rw [hlen]
        simp [f, n, htk]
      have hkcs : k'.1 < cs.length := by simp [hcs, k'.2]
      rw [hf, getD_append_right ds cs k'.1, getD_eq_getElem_of_lt cs k'.1 hkcs]
      simp [cs, htk, evalTerm]
  dsimp only [n]
  rw [heval]
  simp [hlen]

theorem regular_extSat_of_subset [Fintype Γ] (rep : DomainRep Γ)
    (rels : S.R → Set (List ℕ)) (const : S.C → ℕ) (P : Formula S → Set (List ℕ))
    (ψ φ : Formula S) (hsub : free ψ ⊆ free φ)
    (hψ : RegularRel rep (freeList ψ).length (hatSet rels const P ψ)) :
    RegularRel rep (freeList φ).length {ds | ds.length = (freeList φ).length ∧
      ExtSat rels const P ψ (assign (fun _ ↦ 0) (freeList φ) ds)} := by
  let ys := freeList ψ
  let xs := freeList φ
  have hmem (k : Fin ys.length) : ys[k] ∈ xs := by
    rw [mem_freeList]
    exact hsub ((mem_freeList ψ _).mp (List.getElem_mem k.2))
  let f : Fin ys.length → Fin xs.length := fun k ↦
    ⟨xs.idxOf ys[k], List.idxOf_lt_length_of_mem (hmem k)⟩
  have hpull := regular_pullback f hψ
  refine regular_congr (fun ds hlen ↦ ?_) hpull
  change (ds.length = xs.length ∧ List.ofFn (fun k : Fin ys.length ↦ ds.getD (f k) 0) ∈ hatSet rels const P ψ) ↔
    ds.length = xs.length ∧ ExtSat rels const P ψ (assign (fun _ ↦ 0) xs ds)
  have hmap : List.ofFn (fun k : Fin ys.length ↦ ds.getD (f k) 0) =
      ys.map (assign (fun _ ↦ 0) xs ds) := by
    apply List.ext_getElem (by simp)
    intro k hk₁ hk₂
    simp only [List.getElem_ofFn, List.getElem_map]
    let k' : Fin ys.length := ⟨k, by simpa using hk₁⟩
    exact (assign_on (fun _ ↦ 0) xs ds ys[k'] (hmem k')).symm
  rw [hmap, hatSet_map_iff]

private theorem regular_hatSet_temporal [Fintype Γ] (rep : DomainRep Γ)
    (rels : S.R → Set (List ℕ)) (const : S.C → ℕ) (P : Formula S → Set (List ℕ))
    (α : Formula S)
    (hExt : ∀ v, ExtSat rels const P α v ↔ (freeList α).map v ∈ P α)
    (hP : RegularRel rep (freeList α).length (P α)) :
    RegularRel rep (freeList α).length (hatSet rels const P α) := by
  refine regular_congr (fun ds hlen ↦ ?_) hP
  rw [hatSet_iff, hExt, map_assign (fun _ ↦ 0) (freeList α) ds (freeList_nodup α) hlen]
  simp [hlen]

theorem regular_hatSet [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S)
    (hD : IsAutomatic rep D) (i : ℕ) (P : Formula S → Set (List ℕ)) (φ : Formula S)
    (hP : ∀ ψ ∈ tsub φ, RegularRel rep (freeList ψ).length (P ψ)) :
    RegularRel rep (freeList φ).length (hatSet (D.rel i) D.const P φ) := by
  induction φ with
  | eq t₁ t₂ =>
    let xs := freeList (.eq t₁ t₂)
    let ts : Fin 2 → Term S := ![t₁, t₂]
    have hts : ∀ k (x : ℕ), ts k = .inl x → x ∈ xs := by
      intro k x hkx
      rw [mem_freeList]
      fin_cases k
      · apply Finset.mem_union_left
        change t₁ = .inl x at hkx
        simp [hkx, termVars]
      · apply Finset.mem_union_right
        change t₂ = .inl x at hkx
        simp [hkx, termVars]
    have hreg := regular_evalTerms rep D.const xs ts hts rep.eq_regular
    refine regular_congr (fun ds hlen ↦ ?_) hreg
    rw [hatSet_iff]
    change (ds.length = xs.length ∧
      ∃ d : ℕ, List.ofFn (fun k : Fin 2 ↦ evalTerm D.const (assign (fun _ ↦ 0) xs ds) (ts k)) = [d, d]) ↔
      ds.length = xs.length ∧
        evalTerm D.const (assign (fun _ ↦ 0) xs ds) t₁ = evalTerm D.const (assign (fun _ ↦ 0) xs ds) t₂
    simp only [List.ofFn_succ, List.ofFn_zero, List.cons.injEq, and_true, exists_eq_right']
    rfl
  | pred r ts =>
    let xs := freeList (.pred r ts)
    have hts : ∀ k (x : ℕ), ts k = .inl x → x ∈ xs := by
      intro k x hkx
      rw [mem_freeList]
      simp only [free, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨k, by simp [hkx, termVars]⟩
    have hreg := regular_evalTerms rep D.const xs ts hts (hD i r)
    refine regular_congr (fun ds hlen ↦ ?_) hreg
    rw [hatSet_iff]
    rfl
  | neg ψ ih =>
    have hreg := regular_compl (ih hP)
    refine regular_congr (fun ds hlen ↦ ?_) hreg
    change ds ∉ hatSet (D.rel i) D.const P ψ ↔ ds ∈ hatSet (D.rel i) D.const P (.neg ψ)
    rw [hatSet_iff, hatSet_iff]
    have hlen' : ds.length = (freeList ψ).length := hlen
    change ¬ (ds.length = (freeList ψ).length ∧
      ExtSat (D.rel i) D.const P ψ (assign (fun _ ↦ 0) (freeList ψ) ds)) ↔
      ds.length = (freeList ψ).length ∧
        ¬ ExtSat (D.rel i) D.const P ψ (assign (fun _ ↦ 0) (freeList ψ) ds)
    simp [hlen']
  | or ψ₁ ψ₂ ih₁ ih₂ =>
    have h₁ := regular_extSat_of_subset rep (D.rel i) D.const P ψ₁ (.or ψ₁ ψ₂)
      Finset.subset_union_left (ih₁ fun α hα ↦ hP α (List.mem_append_left _ hα))
    have h₂ := regular_extSat_of_subset rep (D.rel i) D.const P ψ₂ (.or ψ₁ ψ₂)
      Finset.subset_union_right (ih₂ fun α hα ↦ hP α (List.mem_append_right _ hα))
    refine regular_congr (fun ds hlen ↦ ?_) (regular_union h₁ h₂)
    rw [hatSet_iff]
    change ((ds.length = (freeList (.or ψ₁ ψ₂)).length ∧
      ExtSat (D.rel i) D.const P ψ₁ (assign (fun _ ↦ 0) (freeList (.or ψ₁ ψ₂)) ds)) ∨
      (ds.length = (freeList (.or ψ₁ ψ₂)).length ∧
      ExtSat (D.rel i) D.const P ψ₂ (assign (fun _ ↦ 0) (freeList (.or ψ₁ ψ₂)) ds))) ↔
      ds.length = (freeList (.or ψ₁ ψ₂)).length ∧
        (ExtSat (D.rel i) D.const P ψ₁ (assign (fun _ ↦ 0) (freeList (.or ψ₁ ψ₂)) ds) ∨
          ExtSat (D.rel i) D.const P ψ₂ (assign (fun _ ↦ 0) (freeList (.or ψ₁ ψ₂)) ds))
    simp [hlen]
  | ex x ψ ih =>
    let xs := freeList (.ex x ψ)
    let ys := freeList ψ
    have hmem (k : Fin ys.length) (hne : ys[(k : ℕ)] ≠ x) : ys[(k : ℕ)] ∈ xs := by
      rw [mem_freeList]
      exact Finset.mem_erase.mpr ⟨hne, (mem_freeList ψ _).mp (List.getElem_mem k.2)⟩
    let f : Fin ys.length → Fin (xs.length + 1) := fun k ↦
      if ys[(k : ℕ)] = x then Fin.last xs.length
      else ⟨xs.idxOf ys[(k : ℕ)], by
        have := List.idxOf_le_length (a := ys[(k : ℕ)]) (l := xs)
        omega⟩
    have hproj := regular_projLast (regular_pullback f (ih hP))
    refine regular_congr (fun ds hlen ↦ ?_) hproj
    rw [hatSet_iff]
    change (ds.length = xs.length ∧ ∃ d : ℕ, (ds ++ [d]).length = xs.length + 1 ∧
      List.ofFn (fun k : Fin ys.length ↦ (ds ++ [d]).getD (f k) 0) ∈ hatSet (D.rel i) D.const P ψ) ↔
      ds.length = xs.length ∧
        ∃ d : ℕ, ExtSat (D.rel i) D.const P ψ (Function.update (assign (fun _ ↦ 0) xs ds) x d)
    have hmap (d : ℕ) : List.ofFn (fun k : Fin ys.length ↦ (ds ++ [d]).getD (f k) 0) =
        ys.map (Function.update (assign (fun _ ↦ 0) xs ds) x d) := by
      apply List.ext_getElem (by simp)
      intro k hk₁ hk₂
      simp only [List.getElem_ofFn, List.getElem_map]
      let k' : Fin ys.length := ⟨k, by simpa using hk₁⟩
      change (ds ++ [d]).getD (f k') 0 =
        Function.update (assign (fun _ ↦ 0) xs ds) x d ys[(k' : ℕ)]
      by_cases hkx : ys[(k' : ℕ)] = x
      · have hf : (f k' : ℕ) = ds.length := by
          rw [hlen]
          simp [f, xs, hkx]
        rw [hf, getD_append_singleton_last ds d, hkx, Function.update_self]
      · have hf : (f k' : ℕ) = xs.idxOf ys[(k' : ℕ)] := by simp [f, hkx]
        have hidx : xs.idxOf ys[(k' : ℕ)] < ds.length := by
          rw [hlen]
          exact List.idxOf_lt_length_of_mem (hmem k' hkx)
        rw [hf, getD_append_left ds [d] _ hidx, Function.update_of_ne hkx,
          assign_on (fun _ ↦ 0) xs ds ys[(k' : ℕ)] (hmem k' hkx)]
    have hlen' : ds.length = xs.length := hlen
    simp only [hlen', List.length_append, List.length_singleton, true_and]
    apply exists_congr
    intro d
    rw [hmap d, hatSet_map_iff]
  | prev I ψ _ =>
    exact regular_hatSet_temporal rep (D.rel i) D.const P (.prev I ψ) (fun _ ↦ Iff.rfl)
      (hP _ (by simp [tsub]))
  | next I ψ _ =>
    exact regular_hatSet_temporal rep (D.rel i) D.const P (.next I ψ) (fun _ ↦ Iff.rfl)
      (hP _ (by simp [tsub]))
  | since I ψ₁ ψ₂ _ _ =>
    exact regular_hatSet_temporal rep (D.rel i) D.const P (.since I ψ₁ ψ₂) (fun _ ↦ Iff.rfl)
      (hP _ (by simp [tsub]))
  | «until» I ψ₁ ψ₂ _ _ =>
    exact regular_hatSet_temporal rep (D.rel i) D.const P (.until I ψ₁ ψ₂) (fun _ ↦ Iff.rfl)
      (hP _ (by simp [tsub]))

end MFOTLMon.Monitor

open MFOTLMon.Monitor

namespace MFOTLMon.Monitor

theorem lemma_3_5_proved {S : Signature} {Γ : Type} [Fintype Γ] (rep : DomainRep Γ)
    (D : TempStruct S) (hD : IsAutomatic rep D) (I : Interval) (β : Formula S)
    (P : Formula S → ℕ → Set (List ℕ)) :
    let B : ℕ → Set (List ℕ) := fun j => hatSet (D.rel j) D.const (fun ψ => P ψ j) β
    (RegularRel rep (freeList (Formula.prev I β)).length (prevP D.τ I 0 (B 0)) ∧
      prevP D.τ I 0 (B 0) = satSet D (Formula.prev I β) 0 ∧
      satSet D (Formula.prev I β) 0 = ∅) ∧
    ∀ i, 0 < i →
      (∀ φ ∈ tsub β, RegularRel rep (freeList φ).length (P φ (i - 1)) ∧
        P φ (i - 1) = satSet D φ (i - 1)) →
      RegularRel rep (freeList (Formula.prev I β)).length (prevP D.τ I i (B (i - 1))) ∧
        prevP D.τ I i (B (i - 1)) = satSet D (Formula.prev I β) i := by
  dsimp only
  constructor
  · have he (A : Set (List ℕ)) : prevP D.τ I 0 A = ∅ := by
      exact if_neg (fun h => (Nat.lt_irrefl 0) h.1)
    have hs : satSet D (Formula.prev I β) 0 = ∅ := by
      rw [← prevP_satSet D I β 0, he]
    rw [he, hs]
    exact ⟨regular_empty rep _, rfl, rfl⟩
  · intro i hi hP
    have hreg := regular_hatSet rep D hD (i - 1) (fun ψ => P ψ (i - 1)) β (fun φ hφ => (hP φ hφ).1)
    have heq := hatSet_eq_satSet D (i - 1) (fun ψ => P ψ (i - 1)) β (fun φ hφ => (hP φ hφ).2)
    constructor
    · by_cases hmem : I.Mem (D.τ i - D.τ (i - 1))
      · have hguard : 0 < i ∧ I.Mem (D.τ i - D.τ (i - 1)) := ⟨hi, hmem⟩
        rw [prevP, if_pos hguard, freeList_prev]
        exact hreg
      · have hguard : ¬ (0 < i ∧ I.Mem (D.τ i - D.τ (i - 1))) := fun h => hmem h.2
        rw [prevP, if_neg hguard]
        exact regular_empty rep (freeList (Formula.prev I β)).length
    · rw [heq]
      exact prevP_satSet D I β i

end MFOTLMon.Monitor

theorem solution {S : Signature} {Γ : Type} [Fintype Γ] (rep : DomainRep Γ)
    (D : TempStruct S) (hD : IsAutomatic rep D) (I : Interval) (β : Formula S)
    (P : Formula S → ℕ → Set (List ℕ)) :
    let B : ℕ → Set (List ℕ) := fun j => hatSet (D.rel j) D.const (fun ψ => P ψ j) β
    (RegularRel rep (freeList (Formula.prev I β)).length (prevP D.τ I 0 (B 0)) ∧
      prevP D.τ I 0 (B 0) = satSet D (Formula.prev I β) 0 ∧
      satSet D (Formula.prev I β) 0 = ∅) ∧
    ∀ i, 0 < i →
      (∀ φ ∈ tsub β, RegularRel rep (freeList φ).length (P φ (i - 1)) ∧
        P φ (i - 1) = satSet D φ (i - 1)) →
      RegularRel rep (freeList (Formula.prev I β)).length (prevP D.τ I i (B (i - 1))) ∧
        prevP D.τ I i (B (i - 1)) = satSet D (Formula.prev I β) i := by
  exact lemma_3_5_proved rep D hD I β P
