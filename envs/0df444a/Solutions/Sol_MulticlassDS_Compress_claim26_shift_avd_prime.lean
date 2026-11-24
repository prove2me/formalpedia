-- Prove2me | solution 1 for MulticlassDS.Compress.claim26_shift_avd_prime
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T00:19:25.992861+00:00
-- url     : https://prove2.me/submissions/a94f773d-7c35-4f2e-9de0-0be66f74aa5a

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

theorem solution {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) :
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
