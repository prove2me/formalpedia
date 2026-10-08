-- Prove2me | solution 1 for ListUpdate.mtf_two_competitive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:11:42.411189+00:00
-- url     : https://prove2.me/submissions/b15dbcfa-5646-4d43-9aa1-a1edb91d950a

import Mathlib

set_option autoImplicit false

namespace MTFProof

theorem idxOf_insertIdx_ne {α : Type*} [DecidableEq α] (x y : α) (hxy : y ≠ x) :
    ∀ (n : ℕ) (l : List α), n ≤ l.length →
    (l.insertIdx n x).idxOf y = if l.idxOf y < n then l.idxOf y else l.idxOf y + 1 := by
  intro n
  induction n with
  | zero =>
    intro l _
    simp [List.idxOf_cons_ne _ (Ne.symm hxy)]
  | succ n ih =>
    intro l hl
    cases l with
    | nil => simp at hl
    | cons a t =>
      simp only [List.insertIdx_succ_cons, List.length_cons] at hl ⊢
      by_cases hay : a = y
      · subst hay; simp
      · rw [List.idxOf_cons_ne _ hay, List.idxOf_cons_ne _ hay, ih t (by omega)]
        split_ifs <;> omega

theorem idxOf_insertIdx_self {α : Type*} [DecidableEq α] (x : α) :
    ∀ (n : ℕ) (l : List α), n ≤ l.length → x ∉ l → (l.insertIdx n x).idxOf x = n := by
  intro n
  induction n with
  | zero => intro l _ _; simp
  | succ n ih =>
    intro l hl hx
    cases l with
    | nil => simp at hl
    | cons a t =>
      simp only [List.insertIdx_succ_cons, List.length_cons, List.mem_cons, not_or] at hl hx ⊢
      rw [List.idxOf_cons_ne _ (Ne.symm hx.1), ih t (by omega) hx.2]

theorem insertIdx_erase_self {α : Type*} [DecidableEq α] (l : List α) (x : α) (hx : x ∈ l) :
    (l.erase x).insertIdx (l.idxOf x) x = l := by
  have hi : l.idxOf x < l.length := List.idxOf_lt_length_of_mem hx
  rw [List.erase_eq_eraseIdx_of_idxOf rfl]
  have := List.insertIdx_eraseIdx_getElem hi
  rwa [List.getElem_idxOf] at this

theorem idxOf_of_erase {α : Type*} [DecidableEq α] (l : List α) (x y : α) (hx : x ∈ l)
    (hxy : y ≠ x) :
    l.idxOf y = if (l.erase x).idxOf y < l.idxOf x then (l.erase x).idxOf y
      else (l.erase x).idxOf y + 1 := by
  have hi : l.idxOf x < l.length := List.idxOf_lt_length_of_mem hx
  have hlen : (l.erase x).length = l.length - 1 := List.length_erase_of_mem hx
  have h := idxOf_insertIdx_ne x y hxy (l.idxOf x) (l.erase x) (by omega)
  rwa [insertIdx_erase_self l x hx] at h

theorem card_filter_idxOf_lt {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup) (n : ℕ) :
    (l.toFinset.filter (fun y => l.idxOf y < n)).card = min n l.length := by
  have : l.toFinset.filter (fun y => l.idxOf y < n) = (l.take n).toFinset := by
    ext y
    simp only [Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨hy, h⟩
      exact (List.mem_take_iff_idxOf_lt hy).2 h
    · intro h
      have hy : y ∈ l := List.mem_of_mem_take h
      exact ⟨hy, (List.mem_take_iff_idxOf_lt hy).1 h⟩
  rw [this, List.toFinset_card_of_nodup (hl.sublist (List.take_sublist _ _)), List.length_take]

/-- inversion pairs -/
def inv {α : Type*} [DecidableEq α] (S : Finset α) (l1 l2 : List α) : Finset (α × α) :=
  (S ×ˢ S).filter (fun p => l1.idxOf p.1 < l1.idxOf p.2 ∧ l2.idxOf p.2 < l2.idxOf p.1)

theorem inv_self {α : Type*} [DecidableEq α] (S : Finset α) (l : List α) :
    (inv S l l).card = 0 := by
  rw [Finset.card_eq_zero, inv, Finset.filter_eq_empty_iff]
  intro p _ h
  omega

theorem swap_spec {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup) (p : ℕ) :
    List.Perm (l.take p ++ ((l.drop p).take 2).reverse ++ l.drop (p + 2)) l ∧
    ∀ (S : Finset α) (M : List α),
      (inv S M (l.take p ++ ((l.drop p).take 2).reverse ++ l.drop (p + 2))).card
        ≤ (inv S M l).card + 1 := by
  have hdd : l.drop (p + 2) = (l.drop p).drop 2 := by
    rw [List.drop_drop]
  have hl0 : l = l.take p ++ l.drop p := (List.take_append_drop p l).symm
  rcases hD : l.drop p with _ | ⟨a, _ | ⟨b, R⟩⟩
  · have : l.take p ++ (([] : List α).take 2).reverse ++ ([] : List α).drop 2 = l := by
      rw [hD] at hl0; simpa using hl0.symm
    rw [hdd, hD, this]
    exact ⟨List.Perm.refl _, fun _ _ => by omega⟩
  · have : l.take p ++ ([a].take 2).reverse ++ [a].drop 2 = l := by
      rw [hD] at hl0; simpa using hl0.symm
    rw [hdd, hD, this]
    exact ⟨List.Perm.refl _, fun _ _ => by omega⟩
  · rw [hdd, hD]
    simp only [List.take_succ_cons, List.take_zero, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.drop_succ_cons, List.drop_zero, List.cons_append,
      List.append_assoc]
    set X := l.take p with hX
    rw [hD] at hl0
    rw [hl0] at hl
    -- l = X ++ a :: b :: R
    have hnd := hl
    rw [List.nodup_append] at hnd
    obtain ⟨_, hndR, hdisj⟩ := hnd
    have haX : a ∉ X := fun h => hdisj a h a (by simp) rfl
    have hbX : b ∉ X := fun h => hdisj b h b (by simp) rfl
    have hab : a ≠ b := by
      intro h; subst h; simp at hndR
    refine ⟨?_, ?_⟩
    · rw [hl0]
      exact List.Perm.append_left _ (List.Perm.swap _ _ _)
    · intro S M
      set l' := X ++ b :: a :: R with hl'
      have fa : l.idxOf a = X.length := by
        rw [hl0, List.idxOf_append_of_notMem haX]; simp
      have fb : l.idxOf b = X.length + 1 := by
        rw [hl0, List.idxOf_append_of_notMem hbX, List.idxOf_cons_ne _ hab]; simp
      have ga : l'.idxOf a = X.length + 1 := by
        rw [hl', List.idxOf_append_of_notMem haX, List.idxOf_cons_ne _ (Ne.symm hab)]; simp
      have gb : l'.idxOf b = X.length := by
        rw [hl', List.idxOf_append_of_notMem hbX]; simp
      have key : ∀ y, y = a ∨ y = b ∨
          (l'.idxOf y = l.idxOf y ∧ (l.idxOf y < X.length ∨ X.length + 1 < l.idxOf y)) := by
        intro y
        by_cases hya : y = a
        · exact Or.inl hya
        by_cases hyb : y = b
        · exact Or.inr (Or.inl hyb)
        right; right
        by_cases hyX : y ∈ X
        · rw [hl', hl0, List.idxOf_append_of_mem hyX, List.idxOf_append_of_mem hyX]
          exact ⟨rfl, Or.inl (List.idxOf_lt_length_of_mem hyX)⟩
        · rw [hl', hl0, List.idxOf_append_of_notMem hyX, List.idxOf_append_of_notMem hyX,
            List.idxOf_cons_ne _ (Ne.symm hyb), List.idxOf_cons_ne _ (Ne.symm hya),
            List.idxOf_cons_ne _ (Ne.symm hya), List.idxOf_cons_ne _ (Ne.symm hyb)]
          exact ⟨rfl, Or.inr (by omega)⟩
      have hsub : inv S M l' ⊆ insert (a, b) (inv S M l) := by
        rintro ⟨p1, p2⟩ h
        simp only [inv, Finset.mem_filter, Finset.mem_product] at h
        rw [Finset.mem_insert]
        simp only [inv, Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
        rcases key p1 with rfl | rfl | ⟨e1, r1⟩ <;> rcases key p2 with rfl | rfl | ⟨e2, r2⟩
        all_goals first
          | exact Or.inl ⟨rfl, rfl⟩
          | (right; refine ⟨⟨h1, h2⟩, h3, ?_⟩; omega)
      calc (inv S M l').card ≤ (insert (a, b) (inv S M l)).card := Finset.card_le_card hsub
        _ ≤ (inv S M l).card + 1 := Finset.card_insert_le _ _

theorem fold_spec {α : Type*} [DecidableEq α] (S : Finset α) (M : List α) :
    ∀ (ps : List ℕ) (l : List α), l.Nodup →
      List.Perm (ps.foldl (fun (l : List α) (p : ℕ) =>
        l.take p ++ ((l.drop p).take 2).reverse ++ l.drop (p + 2)) l) l ∧
      (inv S M (ps.foldl (fun (l : List α) (p : ℕ) =>
        l.take p ++ ((l.drop p).take 2).reverse ++ l.drop (p + 2)) l)).card
        ≤ (inv S M l).card + ps.length := by
  intro ps
  induction ps with
  | nil => intro l _; simp
  | cons p ps ih =>
    intro l hl
    rw [List.foldl_cons]
    obtain ⟨hp, hc⟩ := swap_spec l hl p
    obtain ⟨h1, h2⟩ := ih _ (hp.nodup_iff.2 hl)
    refine ⟨h1.trans hp, ?_⟩
    have := hc S M
    simp only [List.length_cons]
    omega

theorem step_spec {α : Type*} [DecidableEq α] (L M B : List α) (hM : List.Perm M L)
    (hB : List.Perm B L) (hL : L.Nodup) (x : α) (hx : x ∈ L) (d : ℕ) (hd : d ≤ B.idxOf x) :
    (inv L.toFinset (x :: M.erase x) ((B.erase x).insertIdx d x)).card + M.idxOf x
      ≤ (inv L.toFinset M B).card + B.idxOf x + d := by
  have hMn : M.Nodup := hM.nodup_iff.2 hL
  have hBn : B.Nodup := hB.nodup_iff.2 hL
  have hxM : x ∈ M := hM.mem_iff.2 hx
  have hxB : x ∈ B := hB.mem_iff.2 hx
  have hSM : L.toFinset = M.toFinset := List.toFinset_eq_of_perm _ _ hM.symm
  have hSB : L.toFinset = B.toFinset := List.toFinset_eq_of_perm _ _ hB.symm
  have hkl : M.idxOf x < M.length := List.idxOf_lt_length_of_mem hxM
  have hil : B.idxOf x < B.length := List.idxOf_lt_length_of_mem hxB
  have hBlen : (B.erase x).length = B.length - 1 := List.length_erase_of_mem hxB
  have hxBe : x ∉ B.erase x := hBn.not_mem_erase
  have pM' : ∀ y, y ≠ x → (x :: M.erase x).idxOf y = (M.erase x).idxOf y + 1 := fun y hy =>
    List.idxOf_cons_ne _ (Ne.symm hy)
  have pM'x : (x :: M.erase x).idxOf x = 0 := by simp
  have pM : ∀ y, y ≠ x → M.idxOf y = if (M.erase x).idxOf y < M.idxOf x then
      (M.erase x).idxOf y else (M.erase x).idxOf y + 1 :=
    fun y hy => idxOf_of_erase M x y hxM hy
  have pA : ∀ y, y ≠ x → ((B.erase x).insertIdx d x).idxOf y = if (B.erase x).idxOf y < d then
      (B.erase x).idxOf y else (B.erase x).idxOf y + 1 :=
    fun y hy => idxOf_insertIdx_ne x y hy d (B.erase x) (by omega)
  have pAx : ((B.erase x).insertIdx d x).idxOf x = d :=
    idxOf_insertIdx_self x d (B.erase x) (by omega) hxBe
  have pB : ∀ y, y ≠ x → B.idxOf y = if (B.erase x).idxOf y < B.idxOf x then
      (B.erase x).idxOf y else (B.erase x).idxOf y + 1 :=
    fun y hy => idxOf_of_erase B x y hxB hy
  have cK : (L.toFinset.filter (fun y => M.idxOf y < M.idxOf x)).card = M.idxOf x := by
    rw [hSM, card_filter_idxOf_lt M hMn]; omega
  have cIb : (L.toFinset.filter (fun y => B.idxOf y < B.idxOf x)).card = B.idxOf x := by
    rw [hSB, card_filter_idxOf_lt B hBn]; omega
  have cDd : (L.toFinset.filter (fun y => B.idxOf y < d)).card = d := by
    rw [hSB, card_filter_idxOf_lt B hBn]; omega
  have c1 : inv L.toFinset (x :: M.erase x) ((B.erase x).insertIdx d x) ⊆
      (inv L.toFinset M B).filter (fun p => p.1 ≠ x ∧ p.2 ≠ x) ∪
        (L.toFinset.filter (fun y => B.idxOf y < d)).image (fun b => (x, b)) := by
    rintro ⟨p1, p2⟩ h
    simp only [inv, Finset.mem_filter, Finset.mem_product] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    rw [Finset.mem_union, Finset.mem_image]
    by_cases e2 : p2 = x
    · rw [e2, pM'x] at h3; omega
    by_cases e1 : p1 = x
    · rw [e1] at h4
      right
      refine ⟨p2, ?_, by rw [e1]⟩
      rw [Finset.mem_filter]
      refine ⟨h2, ?_⟩
      rw [pAx, pA p2 e2] at h4
      rw [pB p2 e2]
      split_ifs at h4 ⊢ <;> omega
    · left
      simp only [inv, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨⟨h1, h2⟩, ?_, ?_⟩, e1, e2⟩
      · rw [pM' p1 e1, pM' p2 e2] at h3
        rw [pM p1 e1, pM p2 e2]
        split_ifs <;> omega
      · rw [pA p1 e1, pA p2 e2] at h4
        rw [pB p1 e1, pB p2 e2]
        split_ifs at h4 ⊢ <;> omega
  have c2 : (inv L.toFinset M B).filter (fun p => p.1 ≠ x ∧ p.2 ≠ x) ∪
      ((L.toFinset.filter (fun y => M.idxOf y < M.idxOf x)) \
        (L.toFinset.filter (fun y => B.idxOf y < B.idxOf x))).image (fun b => (b, x))
        ⊆ inv L.toFinset M B := by
    intro p hp
    rw [Finset.mem_union] at hp
    rcases hp with hp | hp
    · exact (Finset.mem_filter.1 hp).1
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hp
      rw [Finset.mem_sdiff] at hb
      obtain ⟨hbK, hbI⟩ := hb
      rw [Finset.mem_filter] at hbK hbI
      have hbI' : ¬ B.idxOf b < B.idxOf x := fun h => hbI ⟨hbK.1, h⟩
      have hbx : b ≠ x := by rintro rfl; omega
      have hbB : b ∈ B := hB.mem_iff.2 (List.mem_toFinset.1 hbK.1)
      have hne : B.idxOf b ≠ B.idxOf x := fun h => hbx ((List.idxOf_inj hbB).1 h)
      simp only [inv, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hbK.1, List.mem_toFinset.2 hx⟩, hbK.2, by omega⟩
  have hdisj : Disjoint ((inv L.toFinset M B).filter (fun p => p.1 ≠ x ∧ p.2 ≠ x))
      (((L.toFinset.filter (fun y => M.idxOf y < M.idxOf x)) \
        (L.toFinset.filter (fun y => B.idxOf y < B.idxOf x))).image (fun b => (b, x))) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hp'
    exact (Finset.mem_filter.1 hp).2.2 rfl
  have e1 := Finset.card_le_card c1
  have e1' := Finset.card_union_le ((inv L.toFinset M B).filter (fun p => p.1 ≠ x ∧ p.2 ≠ x))
    ((L.toFinset.filter (fun y => B.idxOf y < d)).image (fun b => (x, b)))
  have e1'' := Finset.card_image_le (s := L.toFinset.filter (fun y => B.idxOf y < d))
    (f := fun b => (x, b))
  have e2 := Finset.card_le_card c2
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)] at e2
  have e3 := Finset.card_le_card_sdiff_add_card
    (s := L.toFinset.filter (fun y => M.idxOf y < M.idxOf x))
    (t := L.toFinset.filter (fun y => B.idxOf y < B.idxOf x))
  omega

theorem tele : ∀ (m : ℕ) (c r : Fin m → ℕ) (Φ : Fin (m + 1) → ℕ),
    (∀ t, Φ t.succ + c t ≤ Φ t.castSucc + r t) →
    (∑ t, c t) + Φ (Fin.last m) ≤ (∑ t, r t) + Φ 0 := by
  intro m
  induction m with
  | zero => intro c r Φ _; simp
  | succ m ih =>
    intro c r Φ h
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have h1 := ih (fun t => c t.castSucc) (fun t => r t.castSucc) (fun t => Φ t.castSucc)
      (fun t => by have := h t.castSucc; rw [Fin.succ_castSucc] at this; exact this)
    have h2 := h (Fin.last m)
    simp only [Fin.succ_last, Fin.castSucc_zero, Nat.succ_eq_add_one] at h1 h2 ⊢
    omega

end MTFProof

theorem solution {α : Type*} [DecidableEq α]
    (L : List α) (hL : L.Nodup) (m : ℕ) (req : Fin m → α) (hreq : ∀ t, req t ∈ L)
    (M : Fin (m + 1) → List α) (hM0 : M 0 = L)
    (hM : ∀ t : Fin m, M t.succ = req t :: (M t.castSucc).erase (req t))
    (paid : Fin m → List ℕ) (dest : Fin m → ℕ)
    (A : Fin (m + 1) → List α) (B : Fin m → List α) (hA0 : A 0 = L)
    (hB : ∀ t : Fin m, B t = (paid t).foldl
      (fun (l : List α) (p : ℕ) => l.take p ++ ((l.drop p).take 2).reverse ++ l.drop (p + 2))
      (A t.castSucc))
    (hdest : ∀ t : Fin m, dest t ≤ (B t).idxOf (req t))
    (hA : ∀ t : Fin m, A t.succ = ((B t).erase (req t)).insertIdx (dest t) (req t)) :
    (∑ t, ((M t.castSucc).idxOf (req t) + 1)) + (∑ t, ((B t).idxOf (req t) - dest t)) + m ≤
      2 * (∑ t, ((B t).idxOf (req t) + 1)) + ∑ t, (paid t).length := by
  have hinv : ∀ t : Fin (m + 1), List.Perm (M t) L ∧ List.Perm (A t) L := by
    intro t
    induction t using Fin.induction with
    | zero => rw [hM0, hA0]; exact ⟨List.Perm.refl _, List.Perm.refl _⟩
    | succ t ih =>
      obtain ⟨ihM, ihA⟩ := ih
      have hAn : (A t.castSucc).Nodup := ihA.nodup_iff.2 hL
      have hBp : List.Perm (B t) (A t.castSucc) := by
        rw [hB t]; exact (MTFProof.fold_spec L.toFinset L (paid t) (A t.castSucc) hAn).1
      have hBL := hBp.trans ihA
      have hxB : req t ∈ B t := hBL.mem_iff.2 (hreq t)
      have hxM : req t ∈ M t.castSucc := ihM.mem_iff.2 (hreq t)
      refine ⟨?_, ?_⟩
      · rw [hM t]; exact (List.perm_cons_erase hxM).symm.trans ihM
      · rw [hA t]
        have hi := List.idxOf_lt_length_of_mem hxB
        have hlen := List.length_erase_of_mem hxB
        have hd := hdest t
        exact (List.perm_insertIdx _ _ (by omega)).trans
          ((List.perm_cons_erase hxB).symm.trans hBL)
  have hBL : ∀ t : Fin m, List.Perm (B t) L := by
    intro t
    have hAn : (A t.castSucc).Nodup := (hinv t.castSucc).2.nodup_iff.2 hL
    have hBp : List.Perm (B t) (A t.castSucc) := by
      rw [hB t]; exact (MTFProof.fold_spec L.toFinset L (paid t) (A t.castSucc) hAn).1
    exact hBp.trans (hinv t.castSucc).2
  have key := MTFProof.tele m
    (fun t => ((M t.castSucc).idxOf (req t) + 1) + ((B t).idxOf (req t) - dest t) + 1)
    (fun t => 2 * ((B t).idxOf (req t) + 1) + (paid t).length)
    (fun t => (MTFProof.inv L.toFinset (M t) (A t)).card) (fun t => by
      have hs := MTFProof.step_spec L (M t.castSucc) (B t) (hinv t.castSucc).1 (hBL t) hL
        (req t) (hreq t) (dest t) (hdest t)
      rw [← hM t, ← hA t] at hs
      have hAn : (A t.castSucc).Nodup := (hinv t.castSucc).2.nodup_iff.2 hL
      have hf : (MTFProof.inv L.toFinset (M t.castSucc) (B t)).card ≤
          (MTFProof.inv L.toFinset (M t.castSucc) (A t.castSucc)).card + (paid t).length := by
        rw [hB t]
        exact (MTFProof.fold_spec L.toFinset (M t.castSucc) (paid t) (A t.castSucc) hAn).2
      have := hdest t
      omega)
  rw [hM0, hA0, MTFProof.inv_self] at key
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, ← Finset.mul_sum] at key ⊢
  omega
