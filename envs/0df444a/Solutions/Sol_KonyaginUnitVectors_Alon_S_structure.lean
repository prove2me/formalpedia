-- Prove2me | solution 1 for KonyaginUnitVectors.Alon.S_structure
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T14:16:54.349363+00:00
-- url     : https://prove2.me/submissions/eb002da6-e3a2-43af-9d47-bc8cd656176b

import Mathlib
import Definitions.Def_KonyaginUnitVectors_AlonConstruction
import Theorems.Thm_KonyaginUnitVectors_Alon_bch6_independent

set_option autoImplicit false

namespace KonyaginUnitVectors.Alon

lemma pk_add_self {F : Type*} [Field F] [CharP F 2] (g : F × F × F) : g + g = 0 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> exact CharTwo.add_self_eq_zero _

lemma pk_nsmul {F : Type*} [Field F] [CharP F 2] (n : ℕ) (g : F × F × F) :
    n • g = if Odd n then g else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, ih]
    by_cases h : Odd n <;> simp [h, Nat.odd_add_one, pk_add_self]

lemma pk_mem_W0 {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F] {x : F} :
    x ∈ W0 F ↔ x ≠ 0 ∧ Algebra.trace (ZMod 2) F (x ^ 9) = 0 := by
  simp [W0]

lemma pk_mem_W1 {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F] {x : F} :
    x ∈ W1 F ↔ x ≠ 0 ∧ Algebra.trace (ZMod 2) F (x ^ 9) ≠ 0 := by
  simp [W1]

lemma pk_W_ne {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F] {a b : F}
    (ha : a ∈ W0 F) (hb : b ∈ W1 F) : a ≠ b := by
  rintro rfl
  exact (pk_mem_W1.1 hb).2 (pk_mem_W0.1 ha).2

/-- PROOF.md Lemma 3': a vanishing sum of at most six `γ z`, `z ≠ 0`, has every multiplicity even. -/
lemma pk_parity {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    [DecidableEq F] (m : Multiset F) (hm0 : ∀ x ∈ m, x ≠ 0) (hm : Multiset.card m ≤ 6)
    (hs : (m.map (gamma F)).sum = 0) (x : F) : Even (m.count x) := by
  set T : Finset F := m.toFinset.filter (fun x => Odd (m.count x)) with hT
  have hsum : (m.map (gamma F)).sum = ∑ x ∈ T, gamma F x := by
    rw [Finset.sum_multiset_map_count, hT, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [pk_nsmul]
  have hT' : ∑ x ∈ T, gamma F x = 0 := hsum.symm.trans hs
  have h1 : ∑ x ∈ T, x = 0 := by
    have := congrArg Prod.fst hT'
    simpa [Prod.fst_sum, gamma] using this
  have h3 : ∑ x ∈ T, x ^ 3 = 0 := by
    have := congrArg (fun g => g.2.1) hT'
    simpa [Prod.fst_sum, Prod.snd_sum, gamma] using this
  have h5 : ∑ x ∈ T, x ^ 5 = 0 := by
    have := congrArg (fun g => g.2.2) hT'
    simpa [Prod.fst_sum, Prod.snd_sum, gamma] using this
  have hT0 : (0 : F) ∉ T := by
    intro h
    rw [hT, Finset.mem_filter, Multiset.mem_toFinset] at h
    exact hm0 0 h.1 rfl
  have hTc : T.card ≤ 6 :=
    (Finset.card_filter_le _ _).trans ((Multiset.toFinset_card_le m).trans hm)
  have hTe : T = ∅ := bch6_independent T hT0 hTc h1 h3 h5
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hx : x ∈ T := by
    rw [hT, Finset.mem_filter, Multiset.mem_toFinset]
    exact ⟨Multiset.count_pos.1 hodd.pos, hodd⟩
  rw [hTe] at hx
  exact absurd hx (Finset.notMem_empty x)

lemma pk_inj (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F] :
    Set.InjOn (fun p : F × F => gamma F p.1 + gamma F p.2) ↑(W0 F ×ˢ W1 F) := by
  classical
  rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp'
  obtain ⟨hx, hy⟩ := hp
  obtain ⟨hx', hy'⟩ := hp'
  simp only at h
  have hxy : x ≠ y := pk_W_ne hx hy
  have hxy' : x ≠ y' := pk_W_ne hx hy'
  have hyx : y ≠ x := hxy.symm
  have hyx' : y ≠ x' := (pk_W_ne hx' hy).symm
  have hs : ((x ::ₘ y ::ₘ x' ::ₘ ({y'} : Multiset F)).map (gamma F)).sum = 0 := by
    simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
      Multiset.sum_singleton]
    rw [← add_assoc, h]
    exact pk_add_self _
  have hm0 : ∀ z ∈ (x ::ₘ y ::ₘ x' ::ₘ ({y'} : Multiset F)), z ≠ 0 := by
    intro z hz
    simp only [Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact (pk_mem_W0.1 hx).1
    · exact (pk_mem_W1.1 hy).1
    · exact (pk_mem_W0.1 hx').1
    · exact (pk_mem_W1.1 hy').1
  have hcard : Multiset.card (x ::ₘ y ::ₘ x' ::ₘ ({y'} : Multiset F)) ≤ 6 := by simp
  have hxx : x = x' := by
    by_contra hne
    have := pk_parity _ hm0 hcard hs x
    simp [hxy, hxy', hne] at this
  have hyy : y = y' := by
    by_contra hne
    have := pk_parity _ hm0 hcard hs y
    simp [hyx, hyx', hne] at this
  rw [hxx, hyy]

end KonyaginUnitVectors.Alon

open KonyaginUnitVectors.Alon

theorem solution (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F] :
    Set.InjOn (fun p : F × F => gamma F p.1 + gamma F p.2) ↑(W0 F ×ˢ W1 F) ∧
    (∀ p ∈ W0 F ×ˢ W1 F, gamma F p.1 + gamma F p.2 ≠ 0) ∧
    (∀ s₁ ∈ Sset F, ∀ s₂ ∈ Sset F, ∀ s₃ ∈ Sset F, s₁ + s₂ + s₃ ≠ 0) ∧
    (Sset F).card = (W0 F).card * (W1 F).card ∧
    (W0 F).card + (W1 F).card + 1 = Fintype.card F := by
  classical
  have hinj := pk_inj F
  refine ⟨hinj, ?_, ?_, ?_, ?_⟩
  · -- (b)
    rintro ⟨x, y⟩ hp h
    have hxy := Finset.mem_product.1 hp
    have h1 := congrArg Prod.fst h
    simp only [gamma, Prod.fst_add, Prod.fst_zero] at h1
    have : x = y := by
      have := eq_neg_of_add_eq_zero_left h1
      rwa [CharTwo.neg_eq] at this
    exact pk_W_ne hxy.1 hxy.2 this
  · -- (c)
    intro s₁ h₁ s₂ h₂ s₃ h₃ hsum
    simp only [Sset, Finset.mem_image, Finset.mem_product] at h₁ h₂ h₃
    obtain ⟨⟨x₁, y₁⟩, ⟨hx₁, hy₁⟩, rfl⟩ := h₁
    obtain ⟨⟨x₂, y₂⟩, ⟨hx₂, hy₂⟩, rfl⟩ := h₂
    obtain ⟨⟨x₃, y₃⟩, ⟨hx₃, hy₃⟩, rfl⟩ := h₃
    simp only at hsum
    have hs : (((x₁ ::ₘ x₂ ::ₘ ({x₃} : Multiset F)) + (y₁ ::ₘ y₂ ::ₘ ({y₃} : Multiset F))).map
        (gamma F)).sum = 0 := by
      simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_cons, Multiset.map_singleton,
        Multiset.sum_cons, Multiset.sum_singleton]
      rw [← hsum]
      abel
    have hm0 : ∀ z ∈ ((x₁ ::ₘ x₂ ::ₘ ({x₃} : Multiset F)) + (y₁ ::ₘ y₂ ::ₘ ({y₃} : Multiset F))),
        z ≠ 0 := by
      intro z hz
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at hz
      rcases hz with (rfl | rfl | rfl) | (rfl | rfl | rfl)
      · exact (pk_mem_W0.1 hx₁).1
      · exact (pk_mem_W0.1 hx₂).1
      · exact (pk_mem_W0.1 hx₃).1
      · exact (pk_mem_W1.1 hy₁).1
      · exact (pk_mem_W1.1 hy₂).1
      · exact (pk_mem_W1.1 hy₃).1
    have hcard : Multiset.card ((x₁ ::ₘ x₂ ::ₘ ({x₃} : Multiset F)) +
        (y₁ ::ₘ y₂ ::ₘ ({y₃} : Multiset F))) ≤ 6 := by simp
    have hev := pk_parity _ hm0 hcard hs
    have heven : Even (∑ x ∈ W0 F, ((x₁ ::ₘ x₂ ::ₘ ({x₃} : Multiset F)) +
        (y₁ ::ₘ y₂ ::ₘ ({y₃} : Multiset F))).count x) :=
      Finset.even_sum _ (fun x _ => hev x)
    have h2z : ∀ x ∈ W0 F, (y₁ ::ₘ y₂ ::ₘ ({y₃} : Multiset F)).count x = 0 := by
      intro x hx
      rw [Multiset.count_eq_zero]
      simp only [Multiset.mem_cons, Multiset.mem_singleton, not_or]
      exact ⟨pk_W_ne hx hy₁, pk_W_ne hx hy₂, pk_W_ne hx hy₃⟩
    have hsum3 : ∑ x ∈ W0 F, ((x₁ ::ₘ x₂ ::ₘ ({x₃} : Multiset F)) +
        (y₁ ::ₘ y₂ ::ₘ ({y₃} : Multiset F))).count x = 3 := by
      rw [Finset.sum_congr rfl (fun x hx => by rw [Multiset.count_add, h2z x hx, add_zero])]
      rw [Multiset.sum_count_eq_card]
      · simp
      · intro a ha
        simp only [Multiset.mem_cons, Multiset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl
        · exact hx₁
        · exact hx₂
        · exact hx₃
    rw [hsum3] at heven
    exact absurd heven (by decide)
  · -- cardinality of `S`
    unfold Sset
    rw [Finset.card_image_of_injOn hinj, Finset.card_product]
  · -- partition of `F*`
    have hdisj : Disjoint (W0 F) (W1 F) := by
      rw [Finset.disjoint_left]
      intro a ha ha'
      exact pk_W_ne ha ha' rfl
    have hunion : W0 F ∪ W1 F = Finset.univ.erase 0 := by
      ext x
      simp only [Finset.mem_union, pk_mem_W0, pk_mem_W1, Finset.mem_erase, Finset.mem_univ,
        and_true]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        by_cases h : Algebra.trace (ZMod 2) F (x ^ 9) = 0
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
    have hc := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hc
    have hpos : 0 < Fintype.card F := Fintype.card_pos
    omega

#print axioms solution
