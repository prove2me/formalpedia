-- Prove2me | solution 1 for ImprovedMMS.Additive.lemma_3_13
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:14:05.689488+00:00
-- url     : https://prove2.me/submissions/fc5cef38-423c-443b-8d82-c5feb83a4e77

import Mathlib
import Definitions.Def_ImprovedMMS_Additive_Bipartite

set_option autoImplicit false
open ImprovedMMS.Additive

theorem ims_percyc {β : Type*} [DecidableEq β] (T : Finset β) (hTne : T.Nonempty) (g : β → β)
    (hg : ∀ y ∈ T, g y ∈ T) :
    ∃ C ⊆ T, C.Nonempty ∧ (∀ y ∈ C, g y ∈ C) ∧ Set.InjOn g C := by
  obtain ⟨t₀, ht₀⟩ := hTne
  have hit : ∀ (z : β), z ∈ T → ∀ k : ℕ, g^[k] z ∈ T := by
    intro z hz k
    induction k with
    | zero => simpa using hz
    | succ k ih => rw [Function.iterate_succ_apply']; exact hg _ ih
  obtain ⟨a, ha, b, hb, hab, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (T.card + 1)) (t := T) (f := fun k => g^[k] t₀) (by simp)
    (fun k _ => hit t₀ ht₀ k)
  have key : ∃ z ∈ T, ∃ p : ℕ, 0 < p ∧ g^[p] z = z := by
    rcases lt_or_gt_of_ne hab with h | h
    · refine ⟨g^[a] t₀, hit t₀ ht₀ a, b - a, by omega, ?_⟩
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]
      exact heq.symm
    · refine ⟨g^[b] t₀, hit t₀ ht₀ b, a - b, by omega, ?_⟩
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]
      exact heq
  obtain ⟨z, hzT, p, hp, hzp⟩ := key
  have hper : ∀ k, g^[k + p] z = g^[k] z := by
    intro k
    rw [Function.iterate_add_apply, hzp]
  refine ⟨(Finset.range p).image (fun k => g^[k] z), ?_, ⟨z, ?_⟩, ?_, ?_⟩
  · intro y hy
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
    exact hit z hzT k
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hp, rfl⟩
  · intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_range] at hk
    have e : g (g^[k] z) = g^[k + 1] z := (Function.iterate_succ_apply' g k z).symm
    rw [e]
    by_cases hk1 : k + 1 < p
    · exact Finset.mem_image.mpr ⟨k + 1, Finset.mem_range.mpr hk1, rfl⟩
    · have : k + 1 = p := by omega
      rw [this, hzp]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hp, rfl⟩
  · intro y hy y' hy' hyy
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    obtain ⟨k', _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy')
    have e1 : ∀ j, g^[j] z = g^[p - 1] (g (g^[j] z)) := by
      intro j
      calc g^[j] z = g^[j + p] z := (hper j).symm
        _ = g^[(p - 1) + (j + 1)] z := by congr 1; omega
        _ = g^[p - 1] (g^[j + 1] z) := Function.iterate_add_apply g (p - 1) (j + 1) z
        _ = g^[p - 1] (g (g^[j] z)) := congrArg _ (Function.iterate_succ_apply' g j z)
    calc g^[k] z = g^[p - 1] (g (g^[k] z)) := e1 k
      _ = g^[p - 1] (g (g^[k'] z)) := by rw [hyy]
      _ = g^[k'] z := (e1 k').symm

theorem ims_nocyc {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (w : α → β → ℝ) (Mt : Finset (α × β)) (hM : IsMCMWM E w Mt)
    (C : Finset β) (xm : β → α) (h : β → β)
    (hxm : ∀ y ∈ C, (xm y, y) ∈ Mt) (hhC : ∀ y ∈ C, h y ∈ C) (hinj : Set.InjOn h C)
    (hE' : ∀ y ∈ C, (xm (h y), y) ∈ E) :
    ∑ y ∈ C, w (xm (h y)) y ≤ ∑ y ∈ C, w (xm y) y := by
  obtain ⟨⟨⟨hsub, hM1, hM2⟩, hmax⟩, hw⟩ := hM
  set F : Finset (α × β) := Mt.filter (fun e => e.2 ∉ C) with hF
  set G : Finset (α × β) := C.image (fun y => (xm (h y), y)) with hG
  have hFG : Disjoint F G := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp he'
    exact (Finset.mem_filter.mp he).2 hy
  have hGinj : Set.InjOn (fun y => (xm (h y), y)) C := by
    intro y _ y' _ hyy
    exact (Prod.mk.inj hyy).2
  have hGcard : G.card = C.card := Finset.card_image_of_injOn hGinj
  set K : Finset (α × β) := Mt.filter (fun e => e.2 ∈ C) with hK
  have hKcard : K.card = C.card := by
    refine Finset.card_bij (fun e _ => e.2) ?_ ?_ ?_
    · intro e he; exact (Finset.mem_filter.mp he).2
    · intro e he e' he' hh
      exact hM2 e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 hh
    · intro y hy
      exact ⟨(xm y, y), Finset.mem_filter.mpr ⟨hxm y hy, hy⟩, rfl⟩
  have hMtcard : Mt.card = F.card + K.card := by
    rw [hF, hK]
    have := Finset.card_filter_add_card_filter_not (s := Mt) (fun e : α × β => e.2 ∈ C)
    omega
  have hMtsum : ∑ e ∈ Mt, w e.1 e.2 = ∑ e ∈ F, w e.1 e.2 + ∑ y ∈ C, w (xm y) y := by
    have h1 := Finset.sum_filter_add_sum_filter_not Mt (fun e : α × β => e.2 ∈ C)
      (fun e => w e.1 e.2)
    have h2 : ∑ e ∈ K, w e.1 e.2 = ∑ y ∈ C, w (xm y) y := by
      refine Finset.sum_bij (fun e _ => e.2) ?_ ?_ ?_ ?_
      · intro e he; exact (Finset.mem_filter.mp he).2
      · intro e he e' he' hh
        exact hM2 e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 hh
      · intro y hy
        exact ⟨(xm y, y), Finset.mem_filter.mpr ⟨hxm y hy, hy⟩, rfl⟩
      · intro e he
        have hy := (Finset.mem_filter.mp he).2
        have : e = (xm e.2, e.2) :=
          hM2 e (Finset.mem_filter.mp he).1 _ (hxm e.2 hy) rfl
        conv_lhs => rw [this]
    rw [hK] at h2
    rw [hF]
    linarith
  have hM'sum : ∑ e ∈ F ∪ G, w e.1 e.2 = ∑ e ∈ F, w e.1 e.2 + ∑ y ∈ C, w (xm (h y)) y := by
    rw [Finset.sum_union hFG, hG, Finset.sum_image hGinj]
  have hmatch : IsMatching E (F ∪ G) := by
    have hFMt : ∀ e ∈ F, e ∈ Mt ∧ e.2 ∉ C := fun e he => Finset.mem_filter.mp he
    have hGe : ∀ e ∈ G, ∃ y ∈ C, e = (xm (h y), y) := by
      intro e he
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp he
      exact ⟨y, hy, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      rcases Finset.mem_union.mp he with he | he
      · exact hsub (hFMt e he).1
      · obtain ⟨y, hy, rfl⟩ := hGe e he
        exact hE' y hy
    · intro e he e' he' hh
      rcases Finset.mem_union.mp he with he | he <;> rcases Finset.mem_union.mp he' with he' | he'
      · exact hM1 e (hFMt e he).1 e' (hFMt e' he').1 hh
      · obtain ⟨y, hy, rfl⟩ := hGe e' he'
        have := hM1 e (hFMt e he).1 _ (hxm (h y) (hhC y hy)) hh
        exact absurd (this ▸ (hFMt e he).2) (by simpa using hhC y hy)
      · obtain ⟨y, hy, rfl⟩ := hGe e he
        have := hM1 _ (hxm (h y) (hhC y hy)) e' (hFMt e' he').1 hh
        exact absurd (this ▸ (hFMt e' he').2) (by simpa using hhC y hy)
      · obtain ⟨y, hy, rfl⟩ := hGe e he
        obtain ⟨y', hy', rfl⟩ := hGe e' he'
        have h3 := hM1 _ (hxm (h y) (hhC y hy)) _ (hxm (h y') (hhC y' hy')) hh
        have h4 : h y = h y' := (Prod.mk.inj h3).2
        have := hinj hy hy' h4
        rw [this]
    · intro e he e' he' hh
      rcases Finset.mem_union.mp he with he | he <;> rcases Finset.mem_union.mp he' with he' | he'
      · exact hM2 e (hFMt e he).1 e' (hFMt e' he').1 hh
      · obtain ⟨y, hy, rfl⟩ := hGe e' he'
        exact absurd (hh ▸ hy) (hFMt e he).2
      · obtain ⟨y, hy, rfl⟩ := hGe e he
        exact absurd (hh ▸ hy) (hFMt e' he').2
      · obtain ⟨y, hy, rfl⟩ := hGe e he
        obtain ⟨y', hy', rfl⟩ := hGe e' he'
        have : y = y' := hh
        rw [this]
  have hcard' : (F ∪ G).card = Mt.card := by
    rw [Finset.card_union_of_disjoint hFG, hGcard, hMtcard, hKcard]
  have hmax' : IsMaxMatching E (F ∪ G) :=
    ⟨hmatch, fun M'' hM'' => (hmax M'' hM'').trans hcard'.ge⟩
  have := hw (F ∪ G) hmax'
  rw [hM'sum, hMtsum] at this
  linarith

theorem solution {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (E : Finset (α × β)) (hE : E ⊆ X ×ˢ Y) (w : α → β → ℝ)
    (Mt : Finset (α × β)) (hM : IsMCMWM E w Mt)
    (T : Finset β) (hT : T ⊆ Mt.image Prod.snd) (hTne : T.Nonempty) :
    (∃ yj ∈ T, ∀ xj : α, (xj, yj) ∈ Mt → ∀ yi ∈ T, ∀ xi : α, (xi, yi) ∈ Mt →
        (xi, yj) ∈ E → w xi yj ≤ w xj yj) ∧
    (∃ yj ∈ T, ∀ xj : α, (xj, yj) ∈ Mt → ∀ yi ∈ T, ∀ xi : α, (xi, yi) ∈ Mt →
        (xj, yi) ∈ E → w xj yi ≤ w xi yi) ∧
    (∀ yi ∈ T, ∀ xi : α, (xi, yi) ∈ Mt → ∀ xj ∈ X, (∀ y : β, (xj, y) ∉ Mt) →
        (xj, yi) ∈ E → w xj yi ≤ w xi yi) := by
  classical
  have hMM := hM.1
  obtain ⟨⟨hsub, hM1, hM2⟩, hmax⟩ := hMM
  -- a mate function
  obtain ⟨t₀, ht₀⟩ := hTne
  have hmate : ∀ y ∈ T, ∃ x, (x, y) ∈ Mt := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (hT hy)
    exact ⟨e.1, he⟩
  haveI : Nonempty α := by
    obtain ⟨x, _⟩ := hmate t₀ ht₀
    exact ⟨x⟩
  let xm : β → α := fun y => Classical.epsilon (fun x => (x, y) ∈ Mt)
  have hxm : ∀ y ∈ T, (xm y, y) ∈ Mt := fun y hy => Classical.epsilon_spec (hmate y hy)
  have huniq : ∀ x y, (x, y) ∈ Mt → x = xm y := by
    intro x y hxy
    have hy : y ∈ T ∨ True := Or.inr trivial
    have : (x, y) ∈ Mt → ∃ x', (x', y) ∈ Mt := fun h => ⟨x, h⟩
    have h2 : (xm y, y) ∈ Mt := Classical.epsilon_spec (p := fun x => (x, y) ∈ Mt) ⟨x, hxy⟩
    have := hM2 _ hxy _ h2 rfl
    exact (Prod.mk.inj this).1
  haveI : Nonempty β := ⟨t₀⟩
  refine ⟨?_, ?_, ?_⟩
  · -- winner
    have : ∃ yj ∈ T, ∀ yi ∈ T, (xm yi, yj) ∈ E → w (xm yi) yj ≤ w (xm yj) yj := by
      by_contra hno
      push_neg at hno
      choose! g hgT hgE hgw using hno
      obtain ⟨C, hCT, hCne, hgC, hginj⟩ := ims_percyc T ⟨t₀, ht₀⟩ g hgT
      have h1 := ims_nocyc E w Mt hM C xm g (fun y hy => hxm y (hCT hy)) hgC hginj
        (fun y hy => hgE y (hCT hy))
      have h2 := Finset.sum_lt_sum_of_nonempty hCne
        (fun y hy => hgw y (hCT hy))
      linarith
    obtain ⟨yj, hyj, hall⟩ := this
    refine ⟨yj, hyj, ?_⟩
    intro xj hxj yi hyi xi hxi hE'
    rw [huniq xj yj hxj, huniq xi yi hxi] at *
    exact hall yi hyi hE'
  · -- loser
    have : ∃ yj ∈ T, ∀ yi ∈ T, (xm yj, yi) ∈ E → w (xm yj) yi ≤ w (xm yi) yi := by
      by_contra hno
      push_neg at hno
      choose! g hgT hgE hgw using hno
      obtain ⟨C, hCT, hCne, hgC, hginj⟩ := ims_percyc T ⟨t₀, ht₀⟩ g hgT
      have hsurj : ∀ z ∈ C, ∃ y ∈ C, g y = z := by
        intro z hz
        obtain ⟨y, hy, hyz⟩ := Finset.surj_on_of_inj_on_of_card_le (s := C) (t := C)
          (fun y _ => g y) (fun y hy => hgC y hy) (fun a b ha hb hab => hginj ha hb hab)
          le_rfl z hz
        exact ⟨y, hy, hyz.symm⟩
      choose! h hhC hgh using hsurj
      have hhinj : Set.InjOn h C := by
        intro z hz z' hz' hzz
        rw [← hgh z hz, ← hgh z' hz', hzz]
      have h1 := ims_nocyc E w Mt hM C xm h (fun y hy => hxm y (hCT hy)) hhC hhinj
        (fun z hz => by
          have := hgE (h z) (hCT (hhC z hz))
          rwa [hgh z hz] at this)
      have h2 := Finset.sum_lt_sum_of_nonempty hCne
        (fun z hz => by
          have := hgw (h z) (hCT (hhC z hz))
          rwa [hgh z hz] at this)
      linarith
    obtain ⟨yj, hyj, hall⟩ := this
    refine ⟨yj, hyj, ?_⟩
    intro xj hxj yi hyi xi hxi hE'
    rw [huniq xj yj hxj, huniq xi yi hxi] at *
    exact hall yi hyi hE'
  · -- unsaturated vertices
    intro yi hyi xi hxi xj hxj hun hxjE
    set M' : Finset (α × β) := insert (xj, yi) (Mt.erase (xi, yi)) with hM'
    have hnotin : (xj, yi) ∉ Mt.erase (xi, yi) := fun h => hun yi (Finset.mem_of_mem_erase h)
    have hmatch : IsMatching E M' := by
      refine ⟨?_, ?_, ?_⟩
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact hxjE
        · exact hsub (Finset.mem_of_mem_erase he)
      · intro e he e' he' hh
        rcases Finset.mem_insert.mp he with rfl | he <;> rcases Finset.mem_insert.mp he' with rfl | he'
        · rfl
        · have hx : xj = e'.1 := hh
          have hmem := Finset.mem_of_mem_erase he'
          have : (xj, e'.2) ∈ Mt := by rw [hx]; exact hmem
          exact absurd this (hun e'.2)
        · have hx : e.1 = xj := hh
          have hmem := Finset.mem_of_mem_erase he
          have : (xj, e.2) ∈ Mt := by rw [← hx]; exact hmem
          exact absurd this (hun e.2)
        · exact hM1 e (Finset.mem_of_mem_erase he) e' (Finset.mem_of_mem_erase he') hh
      · intro e he e' he' hh
        rcases Finset.mem_insert.mp he with rfl | he <;> rcases Finset.mem_insert.mp he' with rfl | he'
        · rfl
        · exfalso
          have := hM2 e' (Finset.mem_of_mem_erase he') (xi, yi) hxi (by simpa using hh.symm)
          exact (Finset.mem_erase.mp he').1 this
        · exfalso
          have := hM2 e (Finset.mem_of_mem_erase he) (xi, yi) hxi (by simpa using hh)
          exact (Finset.mem_erase.mp he).1 this
        · exact hM2 e (Finset.mem_of_mem_erase he) e' (Finset.mem_of_mem_erase he') hh
    have hcard : M'.card = Mt.card := by
      rw [hM', Finset.card_insert_of_notMem hnotin, Finset.card_erase_of_mem hxi]
      have : 0 < Mt.card := Finset.card_pos.mpr ⟨_, hxi⟩
      omega
    have hmax' : IsMaxMatching E M' :=
      ⟨hmatch, fun M'' hM'' => (hmax M'' hM'').trans hcard.ge⟩
    have := hM.2 M' hmax'
    rw [hM', Finset.sum_insert hnotin] at this
    have h5 := Finset.add_sum_erase Mt (fun e : α × β => w e.1 e.2) hxi
    simp only at h5
    linarith
