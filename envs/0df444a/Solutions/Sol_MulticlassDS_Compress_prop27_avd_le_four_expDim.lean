-- Prove2me | solution 1 for MulticlassDS.Compress.prop27_avd_le_four_expDim
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T00:35:13.630012+00:00
-- url     : https://prove2.me/submissions/5bfdca83-8587-48d6-96bb-3a67c4c65139

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Shifting

open MulticlassDS.Compress

noncomputable def solE {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (v : Fin n → Fin p) :
    Finset (Fin n → Fin p) := by
  classical
  exact Finset.univ.filter (fun u => u ∈ H ∧ AgreeOff i u v)

theorem solE_mem {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (v u : Fin n → Fin p) :
    u ∈ solE H i v ↔ u ∈ H ∧ AgreeOff i u v := by
  unfold solE
  simp

theorem solE_ncard {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (v : Fin n → Fin p) :
    {u ∈ H | AgreeOff i u v}.ncard = (solE H i v).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext u
  simp [solE_mem]

def solCands {n p k : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (S : Fin k → Fin n)
    (x : Fin k → Fin p) : Set (Fin n → Fin p) :=
  {v | v ∈ H ∧ ∀ j, S j ≠ i → v (S j) = x j}

noncomputable def solBest {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n)
    (C : Set (Fin n → Fin p)) : Option (Fin n → Fin p) := by
  classical
  exact if h : ∃ v ∈ C, ∀ u ∈ C, (solE H i u).card ≤ (solE H i v).card then some h.choose
    else none

theorem solBest_spec {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n)
    (C : Set (Fin n → Fin p)) (hne : C.Nonempty) :
    ∃ b, solBest H i C = some b ∧ b ∈ C ∧ ∀ u ∈ C, (solE H i u).card ≤ (solE H i b).card := by
  have h : ∃ v ∈ C, ∀ u ∈ C, (solE H i u).card ≤ (solE H i v).card :=
    Set.exists_max_image C (fun u => (solE H i u).card) (Set.toFinite C) hne
  refine ⟨h.choose, ?_, h.choose_spec.1, h.choose_spec.2⟩
  unfold solBest
  rw [dif_pos h]

noncomputable def solF {n p k : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (S : Fin k → Fin n)
    (j0 : Fin k) (x : Fin k → Fin p) : Fin k → Fin p :=
  match solBest H i (solCands H i S x) with
  | none => x
  | some b => if ht : (x j0 : ℕ) < (solE H i b).card then
      (((solE H i b).equivFin.symm ⟨x j0, ht⟩).1) ∘ S else x

theorem solF_eq {n p k : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (S : Fin k → Fin n)
    (j0 : Fin k) (x : Fin k → Fin p) (b : Fin n → Fin p)
    (hb : solBest H i (solCands H i S x) = some b) (ht : (x j0 : ℕ) < (solE H i b).card) :
    solF H i S j0 x = (((solE H i b).equivFin.symm ⟨x j0, ht⟩).1) ∘ S := by
  unfold solF
  rw [hb]
  dsimp only
  rw [dif_pos ht]

theorem sol_claim22 {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (k : ℕ)
    (S : Fin k → Fin n) :
    (proj (shift i H) S).encard ≤ (proj H S).encard := by
  classical
  by_cases hi : ∃ j0, S j0 = i
  swap
  · push_neg at hi
    apply Set.encard_le_encard
    rintro x ⟨g, ⟨v, hv, hag, -⟩, hgx⟩
    refine ⟨v, hv, ?_⟩
    rw [← hgx]
    funext j
    exact (hag (S j) (hi j)).symm
  obtain ⟨j0, hj0⟩ := hi
  have hstruct : ∀ x ∈ proj (shift i H) S, (∀ j, S j = i → x j = x j0) ∧
      ∃ b, solBest H i (solCands H i S x) = some b ∧ b ∈ solCands H i S x ∧
        (x j0 : ℕ) < (solE H i b).card := by
    rintro x ⟨g, ⟨v, hv, hag, hlt⟩, hgx⟩
    have hx : ∀ j, x j = g (S j) := fun j => by rw [← hgx]; rfl
    refine ⟨fun j hj => by rw [hx j, hx j0, hj, hj0], ?_⟩
    have hvC : v ∈ solCands H i S x := ⟨hv, fun j hj => by rw [hx j]; exact (hag (S j) hj).symm⟩
    obtain ⟨b, hb, hbC, hmax⟩ := solBest_spec H i (solCands H i S x) ⟨v, hvC⟩
    refine ⟨b, hb, hbC, ?_⟩
    rw [solE_ncard] at hlt
    have := hmax v hvC
    rw [hx j0, hj0]
    omega
  apply Set.encard_le_encard_of_injOn (f := solF H i S j0)
  · intro x hx
    obtain ⟨-, b, hb, -, ht⟩ := hstruct x hx
    rw [solF_eq H i S j0 x b hb ht]
    exact ⟨_, ((solE_mem H i b _).mp ((solE H i b).equivFin.symm ⟨x j0, ht⟩).2).1, rfl⟩
  · intro x hx y hy hxy
    obtain ⟨hxi, bx, hbx, hbxC, htx⟩ := hstruct x hx
    obtain ⟨hyi, b2, hby, hbyC, hty⟩ := hstruct y hy
    rw [solF_eq H i S j0 x bx hbx htx, solF_eq H i S j0 y b2 hby hty] at hxy
    set ex := (solE H i bx).equivFin.symm ⟨x j0, htx⟩ with hex
    set ey := (solE H i b2).equivFin.symm ⟨y j0, hty⟩ with hey
    have hexm := (solE_mem H i bx _).mp ex.2
    have heym := (solE_mem H i b2 _).mp ey.2
    have hoff : ∀ j, S j ≠ i → x j = y j := by
      intro j hj
      have h1 := congrFun hxy j
      simp only [Function.comp] at h1
      rw [← hbxC.2 j hj, ← hbyC.2 j hj, ← hexm.2 (S j) hj, ← heym.2 (S j) hj]
      exact h1
    have hC : solCands H i S x = solCands H i S y := by
      ext v
      simp only [solCands, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun j hj => (h2 j hj).trans (hoff j hj)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun j hj => (h2 j hj).trans (hoff j hj).symm⟩
    rw [hC, hby] at hbx
    obtain rfl : b2 = bx := Option.some.inj hbx
    have hi_eq : ex.1 i = ey.1 i := by
      have h1 := congrFun hxy j0
      simp only [Function.comp, hj0] at h1
      exact h1
    have hfun : ex.1 = ey.1 := by
      funext m
      by_cases hm : m = i
      · rw [hm]; exact hi_eq
      · rw [hexm.2 m hm, heym.2 m hm]
    have hsub : ex = ey := Subtype.ext hfun
    have hfin := (solE H i b2).equivFin.symm.injective hsub
    have hval : ((x j0 : ℕ)) = y j0 := Fin.mk.inj_iff.mp hfin
    have hj : x j0 = y j0 := Fin.ext hval
    funext j
    by_cases hSj : S j = i
    · rw [hxi j hSj, hyi j hSj, hj]
    · exact hoff j hSj

theorem sol_proj_ncard_le {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (k : ℕ)
    (S : Fin k → Fin n) : (proj (shift i H) S).ncard ≤ (proj H S).ncard := by
  have h := sol_claim22 H i k S
  rw [← (Set.toFinite (proj (shift i H) S)).cast_ncard_eq,
    ← (Set.toFinite (proj H S)).cast_ncard_eq] at h
  exact_mod_cast h

theorem sol_proj_id {n p : ℕ} (X : Set (Fin n → Fin p)) : proj X (id : Fin n → Fin n) = X := by
  unfold proj
  simp

def solCl {n p : ℕ} (H : Set (Fin n → Fin p)) (j : Fin n) (v : Fin n → Fin p) :
    Set (Fin n → Fin p) :=
  {u ∈ H | AgreeOff j u v}

theorem solCl_eq_iff {n p : ℕ} (H : Set (Fin n → Fin p)) (j : Fin n) {a b : Fin n → Fin p}
    (ha : a ∈ H) : solCl H j a = solCl H j b ↔ AgreeOff j a b := by
  constructor
  · intro h
    have : a ∈ solCl H j a := ⟨ha, fun _ _ => rfl⟩
    rw [h] at this
    exact this.2
  · intro hab
    ext u
    constructor
    · rintro ⟨hu, hua⟩
      exact ⟨hu, fun m hm => (hua m hm).trans (hab m hm)⟩
    · rintro ⟨hu, hub⟩
      exact ⟨hu, fun m hm => (hub m hm).trans (hab m hm).symm⟩

theorem sol_edge_sum {n p : ℕ} (H : Set (Fin n → Fin p)) (j : Fin n) :
    (∑ᶠ e ∈ edgesDir H j, ((e.ncard : ℝ) - 1)) = H.ncard - (edgesDir H j).ncard := by
  classical
  have hHf : H.Finite := Set.toFinite H
  have hEf : (edgesDir H j).Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hEf, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, mul_one, Set.ncard_eq_toFinset_card _ hEf]
  have h1 : (∑ e ∈ hEf.toFinset, e.ncard) = H.ncard := by
    rw [Set.ncard_eq_toFinset_card H hHf,
      Finset.card_eq_sum_card_fiberwise (f := solCl H j) (t := hEf.toFinset)]
    · apply Finset.sum_congr rfl
      intro e he
      obtain ⟨w, hw, rfl⟩ := (hEf.mem_toFinset).mp he
      have hset : ((hHf.toFinset.filter fun a => solCl H j a = solCl H j w :
          Finset (Fin n → Fin p)) : Set (Fin n → Fin p)) = solCl H j w := by
        ext u
        simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
        constructor
        · rintro ⟨hu, h⟩
          exact ⟨hu, (solCl_eq_iff H j hu).mp h⟩
        · rintro ⟨hu, h⟩
          exact ⟨hu, (solCl_eq_iff H j hu).mpr h⟩
      change (solCl H j w).ncard = _
      rw [← hset, Set.ncard_coe_finset]
      rfl
    · intro x hx
      rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hx
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      exact ⟨x, hx, rfl⟩
  rw [← h1]
  push_cast
  ring

theorem sol_edges_proj {m p : ℕ} (H : Set (Fin (m + 1) → Fin p)) (j : Fin (m + 1)) :
    (edgesDir H j).ncard = (proj H j.succAbove).ncard := by
  have hker : ∀ a b : Fin (m + 1) → Fin p,
      a ∘ j.succAbove = b ∘ j.succAbove ↔ AgreeOff j a b := by
    intro a b
    constructor
    · intro h l hl
      obtain ⟨z, rfl⟩ := Fin.exists_succAbove_eq hl
      exact congrFun h z
    · intro h
      funext z
      exact h _ (Fin.succAbove_ne j z)
  set T := (fun v => (solCl H j v, v ∘ j.succAbove)) '' H with hT
  have e1 : edgesDir H j = Prod.fst '' T := by
    rw [hT, Set.image_image]
    rfl
  have e2 : proj H j.succAbove = Prod.snd '' T := by
    rw [hT, Set.image_image]
    rfl
  have i1 : Set.InjOn Prod.fst T := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
    simp only at h
    have hab := (solCl_eq_iff H j ha).mp h
    simp only [Prod.mk.injEq]
    exact ⟨h, (hker a b).mpr hab⟩
  have i2 : Set.InjOn Prod.snd T := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
    simp only at h
    have hab := (hker a b).mp h
    simp only [Prod.mk.injEq]
    exact ⟨(solCl_eq_iff H j ha).mpr hab, h⟩
  rw [e1, e2, i1.ncard_image, i2.ncard_image]

theorem sol_eqv {α : Type} (E E' : Finset α) (hE : E = E') (a b : α) (ha : a ∈ E)
    (hb : b ∈ E') (h : ((E.equivFin ⟨a, ha⟩ : Fin E.card) : ℕ) = (E'.equivFin ⟨b, hb⟩ : ℕ)) :
    a = b := by
  subst hE
  have := E.equivFin.injective (Fin.ext h)
  exact congrArg Subtype.val this

theorem sol_solE_card_le {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (v : Fin n → Fin p) :
    (solE H i v).card ≤ p := by
  classical
  have := Finset.card_le_card_of_injOn (fun u : Fin n → Fin p => u i) (t := (Finset.univ : Finset (Fin p)))
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (by
      intro a ha b hb hab
      have ha' := ((solE_mem H i v a).mp ha).2
      have hb' := ((solE_mem H i v b).mp hb).2
      funext m
      by_cases hm : m = i
      · rw [hm]; exact hab
      · rw [ha' m hm, hb' m hm])
  simpa using this

theorem sol_shift_card {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) :
    (shift i H).ncard = H.ncard := by
  classical
  apply le_antisymm
  · have := sol_proj_ncard_le H i n id
    rwa [sol_proj_id, sol_proj_id] at this
  · have hmem : ∀ h ∈ H, h ∈ solE H i h := fun h hh => (solE_mem H i h h).mpr ⟨hh, fun _ _ => rfl⟩
    let φ : (Fin n → Fin p) → (Fin n → Fin p) := fun h =>
      if hh : h ∈ H then Function.update h i
        ⟨((solE H i h).equivFin ⟨h, hmem h hh⟩ : ℕ),
          lt_of_lt_of_le ((solE H i h).equivFin ⟨h, hmem h hh⟩).isLt (sol_solE_card_le H i h)⟩
      else h
    have hφ : ∀ h (hh : h ∈ H), φ h = Function.update h i
        ⟨((solE H i h).equivFin ⟨h, hmem h hh⟩ : ℕ),
          lt_of_lt_of_le ((solE H i h).equivFin ⟨h, hmem h hh⟩).isLt (sol_solE_card_le H i h)⟩ :=
      fun h hh => dif_pos hh
    apply Set.ncard_le_ncard_of_injOn φ
    · intro h hh
      rw [hφ h hh]
      refine ⟨h, hh, fun m hm => Function.update_of_ne hm _ _, ?_⟩
      rw [Function.update_self, solE_ncard]
      exact ((solE H i h).equivFin ⟨h, hmem h hh⟩).isLt
    · intro a ha b hb hab
      rw [hφ a ha, hφ b hb] at hab
      have hoff : AgreeOff i a b := by
        intro m hm
        have := congrFun hab m
        rwa [Function.update_of_ne hm, Function.update_of_ne hm] at this
      have hE : solE H i a = solE H i b := by
        ext u
        rw [solE_mem, solE_mem]
        constructor
        · rintro ⟨hu, h⟩
          exact ⟨hu, fun m hm => (h m hm).trans (hoff m hm)⟩
        · rintro ⟨hu, h⟩
          exact ⟨hu, fun m hm => (h m hm).trans (hoff m hm).symm⟩
      have hi := congrFun hab i
      rw [Function.update_self, Function.update_self] at hi
      exact sol_eqv _ _ hE a b (hmem a ha) (hmem b hb) (Fin.mk.inj_iff.mp hi)

theorem sol_cor23 {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) :
    expDim (shift i H) ≤ expDim H := by
  unfold expDim
  refine iSup_le fun k => iSup_le fun S => iSup_le fun hk => ?_
  exact le_iSup_of_le k (le_iSup_of_le S
    (le_iSup_of_le (hk.trans (sol_claim22 H i k S)) le_rfl))

theorem sol_claim26 {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) :
    avd' H ≤ avd' (shift i H) := by
  classical
  cases n with
  | zero => exact i.elim0
  | succ m =>
    unfold avd'
    rw [sol_shift_card H i]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro j _
    rw [sol_edge_sum H j, sol_edge_sum (shift i H) j, sol_shift_card H i,
      sol_edges_proj H j, sol_edges_proj (shift i H) j]
    have h := sol_proj_ncard_le H i m j.succAbove
    have h' : ((proj (shift i H) j.succAbove).ncard : ℝ) ≤ (proj H j.succAbove).ncard := by
      exact_mod_cast h
    linarith

theorem solE_congr {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) {a b : Fin n → Fin p}
    (hoff : AgreeOff i a b) : solE H i a = solE H i b := by
  ext u
  rw [solE_mem, solE_mem]
  constructor
  · rintro ⟨hu, h⟩
    exact ⟨hu, fun m hm => (h m hm).trans (hoff m hm)⟩
  · rintro ⟨hu, h⟩
    exact ⟨hu, fun m hm => (h m hm).trans (hoff m hm).symm⟩

noncomputable def solR {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (h : Fin n → Fin p) : ℕ := by
  classical
  exact ((solE H i h).filter (fun u => u i < h i)).card

theorem solR_le {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (h : Fin n → Fin p) :
    solR H i h ≤ h i := by
  classical
  unfold solR
  have := Finset.card_le_card_of_injOn (fun u : Fin n → Fin p => (u i : ℕ))
    (s := (solE H i h).filter (fun u => u i < h i)) (t := Finset.range (h i)) (by
      intro u hu
      rw [Finset.mem_coe, Finset.mem_filter] at hu
      rw [Finset.mem_coe, Finset.mem_range]
      exact hu.2) (by
      intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter, solE_mem] at ha hb
      funext m
      by_cases hm : m = i
      · rw [hm]; exact Fin.ext hab
      · rw [ha.1.2 m hm, hb.1.2 m hm])
  simpa using this

theorem solR_lt {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (h : Fin n → Fin p)
    (hh : h ∈ H) : solR H i h < (solE H i h).card := by
  classical
  unfold solR
  apply Finset.card_lt_card
  rw [Finset.filter_ssubset]
  exact ⟨h, (solE_mem H i h h).mpr ⟨hh, fun _ _ => rfl⟩, lt_irrefl _⟩

theorem solR_inj {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) {a b : Fin n → Fin p}
    (ha : a ∈ H) (hb : b ∈ H) (hoff : AgreeOff i a b) (hr : solR H i a = solR H i b) :
    a = b := by
  classical
  have hE := solE_congr H i hoff
  have key : ∀ x y : Fin n → Fin p, x ∈ H → y ∈ H → solE H i x = solE H i y →
      x i < y i → solR H i x < solR H i y := by
    intro x y hx hy hxy hlt
    unfold solR
    rw [hxy]
    apply Finset.card_lt_card
    refine ⟨fun u hu => ?_, fun hsub => ?_⟩
    · rw [Finset.mem_filter] at hu ⊢
      exact ⟨hu.1, lt_trans hu.2 hlt⟩
    · have hxm : x ∈ (solE H i y).filter (fun u => u i < y i) := by
        rw [Finset.mem_filter, ← hxy]
        exact ⟨(solE_mem H i x x).mpr ⟨hx, fun _ _ => rfl⟩, hlt⟩
      have := Finset.mem_filter.mp (hsub hxm)
      exact lt_irrefl _ this.2
  have hai : a i = b i := by
    rcases lt_trichotomy (a i) (b i) with h | h | h
    · exact absurd hr (key a b ha hb hE h).ne
    · exact h
    · exact absurd hr (key b a hb ha hE.symm h).ne'
  funext m
  by_cases hm : m = i
  · rw [hm]; exact hai
  · exact hoff m hm

noncomputable def solPhi {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (h : Fin n → Fin p) :
    Fin n → Fin p :=
  Function.update h i ⟨solR H i h, lt_of_le_of_lt (solR_le H i h) (h i).isLt⟩

theorem solPhi_injOn {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) :
    Set.InjOn (solPhi H i) H := by
  intro a ha b hb hab
  unfold solPhi at hab
  have hoff : AgreeOff i a b := by
    intro m hm
    have := congrFun hab m
    rwa [Function.update_of_ne hm, Function.update_of_ne hm] at this
  have hi := congrFun hab i
  rw [Function.update_self, Function.update_self] at hi
  exact solR_inj H i ha hb hoff (Fin.mk.inj_iff.mp hi)

theorem solPhi_image {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) :
    solPhi H i '' H = shift i H := by
  apply Set.eq_of_subset_of_ncard_le
  · rintro _ ⟨h, hh, rfl⟩
    refine ⟨h, hh, fun m hm => Function.update_of_ne hm _ _, ?_⟩
    unfold solPhi
    rw [Function.update_self, solE_ncard]
    exact solR_lt H i h hh
  · rw [(solPhi_injOn H i).ncard_image, sol_shift_card]
  · exact Set.toFinite _

noncomputable def solW {n p : ℕ} (h : Fin n → Fin p) : ℕ := ∑ j, (h j : ℕ)

noncomputable def solMu {n p : ℕ} (H : Set (Fin n → Fin p)) : ℕ := ∑ᶠ h ∈ H, solW h

theorem solW_update {n p : ℕ} (h : Fin n → Fin p) (i : Fin n) (x : Fin p) :
    solW (Function.update h i x) + h i = solW h + x := by
  classical
  unfold solW
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    Function.update_self]
  have : ∑ j ∈ Finset.univ.erase i, ((Function.update h i x j : Fin p) : ℕ) =
      ∑ j ∈ Finset.univ.erase i, (h j : ℕ) :=
    Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  rw [this]
  ring

theorem solMu_lt {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (hne : shift i H ≠ H) :
    solMu (shift i H) < solMu H := by
  classical
  have hHf : H.Finite := Set.toFinite H
  unfold solMu
  rw [← solPhi_image H i, finsum_mem_image (solPhi_injOn H i),
    finsum_mem_eq_finite_toFinset_sum _ hHf, finsum_mem_eq_finite_toFinset_sum _ hHf]
  have hw : ∀ h, solW (solPhi H i h) + h i = solW h + solR H i h := by
    intro h
    unfold solPhi
    rw [solW_update]
  apply Finset.sum_lt_sum
  · intro h _
    have := hw h
    have := solR_le H i h
    omega
  · by_contra hcon
    push_neg at hcon
    apply hne
    rw [← solPhi_image H i]
    have hfix : ∀ h ∈ H, solPhi H i h = h := by
      intro h hh
      have h1 := hcon h (hHf.mem_toFinset.mpr hh)
      have h2 := hw h
      have h3 := solR_le H i h
      have hr : solR H i h = h i := by omega
      unfold solPhi
      apply Function.update_eq_self_iff.mpr
      exact Fin.ext hr
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      rw [hfix h hh]; exact hh
    · intro hg
      exact ⟨g, hg, hfix g hg⟩

theorem sol_iter {n p : ℕ} : ∀ (N : ℕ) (H : Set (Fin n → Fin p)), solMu H < N →
    ∃ D : Set (Fin n → Fin p), (∀ i, shift i D = D) ∧ avd' H ≤ avd' D ∧ expDim D ≤ expDim H := by
  intro N
  induction N with
  | zero => intro H h; omega
  | succ N ih =>
    intro H hH
    by_cases hfix : ∀ i, shift i H = H
    · exact ⟨H, hfix, le_rfl, le_rfl⟩
    · push_neg at hfix
      obtain ⟨i, hi⟩ := hfix
      have hlt := solMu_lt H i hi
      obtain ⟨D, hD, h1, h2⟩ := ih (shift i H) (by omega)
      exact ⟨D, hD, (sol_claim26 H i).trans h1, h2.trans (sol_cor23 H i)⟩

theorem sol_zero_mem {n p : ℕ} {D : Set (Fin n → Fin p)} (hfix : ∀ i, shift i D = D)
    {h : Fin n → Fin p} (hh : h ∈ D) (i : Fin n) (z : Fin p) (hz : (z : ℕ) = 0) :
    Function.update h i z ∈ D := by
  rw [← hfix i]
  refine ⟨h, hh, fun m hm => Function.update_of_ne hm _ _, ?_⟩
  rw [Function.update_self, hz]
  exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨h, hh, fun _ _ => rfl⟩

theorem sol_zero_set {n p : ℕ} {D : Set (Fin n → Fin p)} (hfix : ∀ i, shift i D = D)
    {h : Fin n → Fin p} (hh : h ∈ D) (z : Fin p) (hz : (z : ℕ) = 0) (Z : Finset (Fin n)) :
    (fun m => if m ∈ Z then z else h m) ∈ D := by
  classical
  refine Finset.induction_on Z ?_ ?_
  · simpa using hh
  · intro a Z _ ih
    have e : (fun m => if m ∈ insert a Z then z else h m) =
        Function.update (fun m => if m ∈ Z then z else h m) a z := by
      funext m
      by_cases hm : m = a
      · subst hm; simp
      · simp [Function.update_of_ne hm, hm]
    rw [e]
    exact sol_zero_mem hfix ih a z hz

theorem sol_supp_le {n p : ℕ} {D : Set (Fin n → Fin p)} (hfix : ∀ i, shift i D = D)
    {h : Fin n → Fin p} (hh : h ∈ D) (k : ℕ) (hk : expDim D ≤ k) :
    (Finset.univ.filter (fun j => (h j : ℕ) ≠ 0)).card ≤ k := by
  classical
  set T := Finset.univ.filter (fun j => (h j : ℕ) ≠ 0) with hT
  rcases T.eq_empty_or_nonempty with he | ⟨j0, _⟩
  · rw [he]; simp
  let z : Fin p := ⟨0, by have := (h j0).isLt; omega⟩
  let S : Fin T.card → Fin n := fun l => (T.equivFin.symm l).1
  have hSinj : Function.Injective S := Subtype.val_injective.comp T.equivFin.symm.injective
  have hS : ∀ l, (h (S l) : ℕ) ≠ 0 := fun l => (Finset.mem_filter.mp (T.equivFin.symm l).2).2
  let w : (Fin T.card → Bool) → (Fin T.card → Fin p) := fun c l => if c l then h (S l) else z
  have hne : ∀ l, h (S l) ≠ z := fun l e => hS l (by rw [e])
  have hw_inj : Function.Injective w := by
    intro c c' hcc
    funext l
    have hl := congrFun hcc l
    simp only [w] at hl
    cases hc : c l <;> cases hc' : c' l
    · rfl
    · simp [hc, hc'] at hl
      first | exact absurd hl (hne l) | exact absurd hl.symm (hne l)
    · simp [hc, hc'] at hl
      first | exact absurd hl (hne l) | exact absurd hl.symm (hne l)
    · rfl
  have hw_mem : ∀ c, w c ∈ proj D S := by
    intro c
    let Z := (Finset.univ.filter (fun l => c l = false)).image S
    refine ⟨fun m => if m ∈ Z then z else h m, sol_zero_set hfix hh z rfl Z, ?_⟩
    funext l
    have hmem : S l ∈ Z ↔ c l = false := by
      simp only [Z, hSinj.mem_finset_image, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Function.comp, w]
    cases hc : c l
    · rw [if_pos (hmem.mpr hc)]; simp
    · rw [if_neg (fun hm => by rw [hmem.mp hm] at hc; exact Bool.false_ne_true hc)]; simp
  have hcard : (2 : ℕ∞) ^ T.card ≤ (proj D S).encard := by
    have hsub : ((Finset.univ.image w : Finset (Fin T.card → Fin p)) : Set (Fin T.card → Fin p)) ⊆
        proj D S := by
      intro x hx
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hx
      exact hw_mem c
    have := Set.encard_le_encard hsub
    rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hw_inj] at this
    simpa using this
  have hle : (T.card : ℕ∞) ≤ expDim D := by
    unfold expDim
    exact le_iSup_of_le T.card (le_iSup_of_le S (le_iSup_of_le hcard le_rfl))
  exact_mod_cast hle.trans hk

theorem sol_dir_count {m p : ℕ} {D : Set (Fin (m + 1) → Fin p)} (hfix : ∀ i, shift i D = D)
    (j : Fin (m + 1)) :
    (D.ncard : ℝ) - (edgesDir D j).ncard =
      ((Set.toFinite D).toFinset.filter (fun h => (h j : ℕ) ≠ 0)).card := by
  classical
  set F := (Set.toFinite D).toFinset with hF
  have hproj : (proj D j.succAbove).ncard = (F.filter (fun h => (h j : ℕ) = 0)).card := by
    rw [← Set.ncard_coe_finset]
    have hD0 : ((F.filter (fun h => (h j : ℕ) = 0) : Finset _) : Set (Fin (m + 1) → Fin p)) =
        {h | h ∈ D ∧ (h j : ℕ) = 0} := by
      ext h
      simp [hF]
    rw [hD0]
    have himg : proj D j.succAbove = (fun h => h ∘ j.succAbove) '' {h | h ∈ D ∧ (h j : ℕ) = 0} := by
      apply Set.Subset.antisymm
      · rintro _ ⟨v, hv, rfl⟩
        let z0 : Fin p := ⟨0, by have := (v j).isLt; omega⟩
        refine ⟨Function.update v j z0, ⟨sol_zero_mem hfix hv j z0 rfl, by simp [z0]⟩, ?_⟩
        funext l
        simp [Function.update_of_ne (Fin.succAbove_ne j l)]
      · rintro _ ⟨v, hv, rfl⟩
        exact ⟨v, hv.1, rfl⟩
    rw [himg]
    apply Set.InjOn.ncard_image
    rintro a ⟨ha, ha0⟩ b ⟨hb, hb0⟩ hab
    funext l
    by_cases hl : l = j
    · subst hl; exact Fin.ext (ha0.trans hb0.symm)
    · obtain ⟨z, rfl⟩ := Fin.exists_succAbove_eq hl
      exact congrFun hab z
  rw [sol_edges_proj, hproj, Set.ncard_eq_toFinset_card D (Set.toFinite D), ← hF]
  have := Finset.card_filter_add_card_filter_not (s := F) (fun h => (h j : ℕ) = 0)
  rw [← this]
  push_cast
  ring

theorem sol_avd'_fixed {n p : ℕ} {D : Set (Fin n → Fin p)} (hfix : ∀ i, shift i D = D)
    (k : ℕ) (hk : expDim D ≤ k) : avd' D ≤ k := by
  classical
  cases n with
  | zero => unfold avd'; simp
  | succ m =>
    set F := (Set.toFinite D).toFinset with hF
    unfold avd'
    have hrw : ∀ j : Fin (m + 1), (∑ᶠ e ∈ edgesDir D j, ((e.ncard : ℝ) - 1)) =
        ((F.filter (fun h => (h j : ℕ) ≠ 0)).card : ℝ) := by
      intro j
      rw [sol_edge_sum, sol_dir_count hfix j]
    rw [Finset.sum_congr rfl (fun j _ => hrw j), Set.ncard_eq_toFinset_card D (Set.toFinite D), ← hF]
    have hsum : (∑ j : Fin (m + 1), (F.filter (fun h => (h j : ℕ) ≠ 0)).card) ≤ F.card * k := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
      calc (∑ h ∈ F, ∑ j : Fin (m + 1), if (h j : ℕ) ≠ 0 then 1 else 0)
          ≤ ∑ h ∈ F, k := by
            apply Finset.sum_le_sum
            intro h hh
            have := sol_supp_le hfix ((Set.toFinite D).mem_toFinset.mp hh) k hk
            simpa [Finset.card_filter] using this
        _ = F.card * k := by simp
    have hsumR : (∑ j : Fin (m + 1), ((F.filter (fun h => (h j : ℕ) ≠ 0)).card : ℝ)) ≤
        (F.card : ℝ) * k := by exact_mod_cast hsum
    rcases Nat.eq_zero_or_pos F.card with h0 | hpos
    · rw [h0]; simp
    · rw [div_le_iff₀ (by exact_mod_cast hpos)]
      linarith

open Classical in
theorem sol_deg_dir {n p : ℕ} (H : Set (Fin n → Fin p)) (j : Fin n) :
    ((Set.toFinite H).toFinset.filter (fun v => ∃ u ∈ H, u ≠ v ∧ AgreeOff j u v)).card +
      2 * (edgesDir H j).ncard ≤ 2 * H.ncard := by
  classical
  set F := (Set.toFinite H).toFinset with hF
  have hEf : (edgesDir H j).Finite := Set.toFinite _
  set G := F.filter (fun v => ∃ u ∈ H, u ≠ v ∧ AgreeOff j u v) with hG
  have hmaps : ∀ s : Finset (Fin n → Fin p), s ⊆ F →
      ((s : Set (Fin n → Fin p))).MapsTo (solCl H j) (hEf.toFinset : Set _) := by
    intro s hs x hx
    have hxH : x ∈ H := (Set.toFinite H).mem_toFinset.mp (hs (Finset.mem_coe.mp hx))
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact ⟨x, hxH, rfl⟩
  rw [Set.ncard_eq_toFinset_card H (Set.toFinite H), ← hF, Set.ncard_eq_toFinset_card _ hEf,
    Finset.card_eq_sum_card_fiberwise (s := G) (hmaps G (Finset.filter_subset _ _)),
    Finset.card_eq_sum_card_fiberwise (s := F) (hmaps F (subset_refl _)),
    Finset.card_eq_sum_ones hEf.toFinset, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨w, hw, rfl⟩ := hEf.mem_toFinset.mp he
  show (G.filter (fun a => solCl H j a = solCl H j w)).card + 2 * 1 ≤
    2 * (F.filter (fun a => solCl H j a = solCl H j w)).card
  have hwF : w ∈ F.filter (fun a => solCl H j a = solCl H j w) :=
    Finset.mem_filter.mpr ⟨(Set.toFinite H).mem_toFinset.mpr hw, rfl⟩
  have hpos : 0 < (F.filter (fun a => solCl H j a = solCl H j w)).card :=
    Finset.card_pos.mpr ⟨w, hwF⟩
  have hsub : G.filter (fun a => solCl H j a = solCl H j w) ⊆
      F.filter (fun a => solCl H j a = solCl H j w) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨(Finset.mem_filter.mp hx.1).1, hx.2⟩
  have hle := Finset.card_le_card hsub
  by_cases h2 : 2 ≤ (F.filter (fun a => solCl H j a = solCl H j w)).card
  · omega
  · have hz : (G.filter (fun a => solCl H j a = solCl H j w)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro v hv
      apply h2
      rw [Finset.mem_filter, hG, Finset.mem_filter] at hv
      obtain ⟨⟨hvF, u, hu, huv, hag⟩, hvw⟩ := hv
      have hvH : v ∈ H := (Set.toFinite H).mem_toFinset.mp hvF
      have huw : solCl H j u = solCl H j w := by
        rw [← hvw]; exact (solCl_eq_iff H j hu).mpr hag
      have : 1 < (F.filter (fun a => solCl H j a = solCl H j w)).card :=
        Finset.one_lt_card.mpr ⟨u, Finset.mem_filter.mpr ⟨(Set.toFinite H).mem_toFinset.mpr hu, huw⟩,
          v, Finset.mem_filter.mpr ⟨hvF, hvw⟩, huv⟩
      omega
    omega

theorem sol_avd_le {n p : ℕ} (H : Set (Fin n → Fin p)) : avd H ≤ 2 * avd' H := by
  classical
  set F := (Set.toFinite H).toFinset with hF
  unfold avd avd'
  rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite H), ← hF]
  have hdeg : (∑ v ∈ F, deg H v) =
      ∑ j, (F.filter (fun v => ∃ u ∈ H, u ≠ v ∧ AgreeOff j u v)).card := by
    unfold deg
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have key : (∑ v ∈ F, (deg H v : ℝ)) ≤
      2 * ∑ j, (∑ᶠ e ∈ edgesDir H j, ((e.ncard : ℝ) - 1)) := by
    rw [← Nat.cast_sum, hdeg, Finset.mul_sum, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [sol_edge_sum]
    have := sol_deg_dir H j
    have h' : ((F.filter (fun v => ∃ u ∈ H, u ≠ v ∧ AgreeOff j u v)).card : ℝ) +
        2 * (edgesDir H j).ncard ≤ 2 * H.ncard := by exact_mod_cast this
    linarith
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right key (Nat.cast_nonneg _)

theorem solution {n p : ℕ} (H : Set (Fin n → Fin p)) (dE : ℕ)
    (hE : expDim H = dE) :
    avd H ≤ 4 * dE := by
  obtain ⟨D, hfix, h1, h2⟩ := sol_iter (solMu H + 1) H (Nat.lt_succ_self _)
  have h3 := sol_avd'_fixed hfix dE (h2.trans hE.le)
  have h4 := sol_avd_le H
  have h5 : (0 : ℝ) ≤ dE := Nat.cast_nonneg _
  have : avd H ≤ 4 * (dE : ℝ) := by linarith
  exact_mod_cast this
