-- Prove2me | solution 1 for GraphMatching.maximal_matching_half
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:26:32.734616+00:00
-- url     : https://prove2.me/submissions/f0970bc1-495b-4be0-9d38-9a10ea829b96

import Mathlib
import Definitions.Def_GraphMatching_basic

namespace MTSPKV

open Finset GraphMatching

section Matching

variable {W : Type*}

theorem isMatching_empty (H : SimpleGraph W) : IsMatching H ∅ := by
  simp [IsMatching]

variable [Fintype W] {H : SimpleGraph W}

theorem card_le_matchingNumber {M : Finset (Sym2 W)} (hM : IsMatching H M) :
    M.card ≤ matchingNumber H := by
  classical
  unfold matchingNumber
  exact Finset.le_sup (f := Finset.card) (mem_filter.2 ⟨mem_univ _, hM⟩)

theorem exists_matching_card (H : SimpleGraph W) :
    ∃ M, IsMatching H M ∧ M.card = matchingNumber H := by
  classical
  unfold matchingNumber
  obtain ⟨M, hM, h⟩ := Finset.exists_mem_eq_sup
    ((univ : Finset (Finset (Sym2 W))).filter (IsMatching H))
    ⟨∅, mem_filter.2 ⟨mem_univ _, isMatching_empty H⟩⟩ Finset.card
  exact ⟨M, (mem_filter.1 hM).2, h.symm⟩

theorem vcNumber_le {C : Finset W} (hC : IsVC H C) : vcNumber H ≤ C.card := by
  classical
  unfold vcNumber
  exact Nat.find_min' _ ⟨C, hC, rfl⟩

theorem exists_vc_card (H : SimpleGraph W) : ∃ C, IsVC H C ∧ C.card = vcNumber H := by
  classical
  unfold vcNumber
  exact Nat.find_spec (⟨_, univ, isVC_univ H, rfl⟩ : ∃ n, ∃ C : Finset W, IsVC H C ∧ C.card = n)

/-- Weak LP duality: a matching has size at most the value of any fractional vertex cover. -/
theorem card_le_sum_of_frac {M : Finset (Sym2 W)} (hM : IsMatching H M) (Y : W → ℝ)
    (hY0 : ∀ x, 0 ≤ Y x) (hY : ∀ x z, H.Adj x z → 1 ≤ Y x + Y z) :
    (M.card : ℝ) ≤ ∑ x, Y x := by
  classical
  let F : Sym2 W → Finset W := fun e => univ.filter (· ∈ e)
  have h1 : ∀ e ∈ M, (1 : ℝ) ≤ ∑ x ∈ F e, Y x := by
    intro e he
    have hE := hM.1 e he
    induction e using Sym2.ind with
    | h a b =>
      have hab : H.Adj a b := hE
      have hne : a ≠ b := hab.ne
      have : F s(a, b) = {a, b} := by
        ext x; simp [F]
      rw [this, sum_pair hne]
      exact hY a b hab
  have hdisj : (M : Set (Sym2 W)).PairwiseDisjoint F := by
    intro e he f hf hef
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [F, mem_filter, mem_univ, true_and] at hx hx'
    exact hM.2 e he f hf hef x hx hx'
  calc (M.card : ℝ) = ∑ _e ∈ M, (1 : ℝ) := by simp
    _ ≤ ∑ e ∈ M, ∑ x ∈ F e, Y x := sum_le_sum h1
    _ = ∑ x ∈ M.biUnion F, Y x := (sum_biUnion hdisj).symm
    _ ≤ ∑ x, Y x := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ => hY0 x)

/-- Any matching is at most as large as any vertex cover. -/
theorem matching_le_vc {M : Finset (Sym2 W)} {C : Finset W} (hM : IsMatching H M)
    (hC : IsVC H C) : M.card ≤ C.card := by
  classical
  have := card_le_sum_of_frac hM (fun x => if x ∈ C then (1 : ℝ) else 0)
    (fun x => by split_ifs <;> norm_num)
    (fun x z hxz => by
      rcases hC x z hxz with h | h <;> simp only [h, if_true] <;> split_ifs <;> norm_num)
  rw [sum_boole] at this
  have hC' : (univ.filter (· ∈ C)) = C := by ext; simp
  rw [hC'] at this
  exact_mod_cast this

theorem matchingNumber_le_vcNumber (H : SimpleGraph W) : matchingNumber H ≤ vcNumber H := by
  obtain ⟨M, hM, hMc⟩ := exists_matching_card H
  obtain ⟨C, hC, hCc⟩ := exists_vc_card H
  rw [← hMc, ← hCc]
  exact matching_le_vc hM hC

/-- A maximal matching is a 2-approximation of the maximum matching. -/
theorem maximal_matching_half {M : Finset (Sym2 W)} (_hM : IsMatching H M)
    (hmax : ∀ e ∈ H.edgeSet, ∃ f ∈ M, ∃ x, x ∈ e ∧ x ∈ f) :
    matchingNumber H ≤ 2 * M.card := by
  classical
  let F : Sym2 W → Finset W := fun e => univ.filter (· ∈ e)
  have hC : IsVC H (M.biUnion F) := by
    intro x z hxz
    obtain ⟨f, hf, w, hw, hwf⟩ := hmax s(x, z) hxz
    rcases Sym2.mem_iff.1 hw with rfl | rfl
    · left; exact mem_biUnion.2 ⟨f, hf, by simp [F, hwf]⟩
    · right; exact mem_biUnion.2 ⟨f, hf, by simp [F, hwf]⟩
  have hF : ∀ e ∈ M, (F e).card ≤ 2 := by
    intro e _
    induction e using Sym2.ind with
    | h a b =>
      calc (F s(a, b)).card ≤ ({a, b} : Finset W).card := by
            apply card_le_card; intro x; simp [F]
        _ ≤ 2 := card_le_two
  calc matchingNumber H ≤ vcNumber H := matchingNumber_le_vcNumber H
    _ ≤ (M.biUnion F).card := vcNumber_le hC
    _ ≤ ∑ e ∈ M, (F e).card := card_biUnion_le
    _ ≤ ∑ _e ∈ M, 2 := sum_le_sum hF
    _ = 2 * M.card := by rw [sum_const, smul_eq_mul, mul_comm]

end Matching

section Konig

variable {V : Type*} [Fintype V]

/-- König's theorem for a graph on `Bool × V` all of whose edges join the two sides. -/
theorem konig (H : SimpleGraph (Bool × V))
    (hH : ∀ a u b v, H.Adj (a, u) (b, v) → a ≠ b) :
    vcNumber H = matchingNumber H := by
  classical
  let N : Finset V → Finset V := fun A =>
    univ.filter (fun v => ∃ u ∈ A, H.Adj (false, u) (true, v))
  obtain ⟨A, -, hA⟩ := Finset.exists_max_image (univ : Finset (Finset V))
    (fun B => (B.card : ℤ) - (N B).card) univ_nonempty
  have hN0 : N ∅ = ∅ := by ext; simp [N]
  have hk : (N A).card ≤ A.card := by
    have := hA ∅ (mem_univ _)
    simp only [hN0, card_empty, Nat.cast_zero, sub_zero] at this
    omega
  set k := A.card - (N A).card with hkdef
  -- vertex cover side
  have hvc : vcNumber H ≤ Fintype.card V - k := by
    let C : Finset (Bool × V) := Aᶜ.image (Prod.mk false) ∪ (N A).image (Prod.mk true)
    have hC : IsVC H C := by
      rintro ⟨a, u⟩ ⟨b, v⟩ huv
      have hab := hH a u b v huv
      cases a <;> cases b
      · exact absurd rfl hab
      · by_cases hu : u ∈ A
        · right; simp only [C, mem_union, mem_image]
          right; exact ⟨v, by simp [N]; exact ⟨u, hu, huv⟩, rfl⟩
        · left; simp only [C, mem_union, mem_image]
          left; exact ⟨u, by simpa using hu, rfl⟩
      · by_cases hv : v ∈ A
        · left; simp only [C, mem_union, mem_image]
          right; exact ⟨u, by simp [N]; exact ⟨v, hv, huv.symm⟩, rfl⟩
        · right; simp only [C, mem_union, mem_image]
          left; exact ⟨v, by simpa using hv, rfl⟩
      · exact absurd rfl hab
    have hcard : C.card ≤ Fintype.card V - A.card + (N A).card := by
      calc C.card ≤ (Aᶜ.image (Prod.mk false)).card + ((N A).image (Prod.mk true)).card :=
            card_union_le _ _
        _ ≤ Aᶜ.card + (N A).card := add_le_add card_image_le card_image_le
        _ = _ := by rw [card_compl]
    have := vcNumber_le hC
    have hAV : A.card ≤ Fintype.card V := card_le_univ A
    omega
  -- matching side via Hall's theorem with `k` dummy vertices
  let t : V → Finset (V ⊕ Fin k) := fun u => (N {u}).disjSum univ
  have hall : ∀ s : Finset V, s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨u0, hu0⟩
    · simp
    have hsub : (N s).disjSum (univ : Finset (Fin k)) ⊆ s.biUnion t := by
      intro x hx
      rcases x with v | j
      · rw [inl_mem_disjSum] at hx
        simp only [N, mem_filter, mem_univ, true_and] at hx
        obtain ⟨u, hu, huv⟩ := hx
        exact mem_biUnion.2 ⟨u, hu, by simp [t, N, huv]⟩
      · exact mem_biUnion.2 ⟨u0, hu0, by simp [t]⟩
    have h1 := card_le_card hsub
    rw [card_disjSum, card_univ, Fintype.card_fin] at h1
    have h2 : (s.card : ℤ) - (N s).card ≤ A.card - (N A).card := hA s (mem_univ _)
    omega
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  let h : V → V := fun u => Sum.elim id (fun _ => u) (f u)
  let Q := univ.filter (fun u => (f u).isLeft = true)
  have hQ : ∀ u ∈ Q, f u = Sum.inl (h u) := by
    intro u hu
    simp only [Q, mem_filter, mem_univ, true_and] at hu
    simp only [h]
    rcases hfu : f u with v | j
    · rfl
    · rw [hfu] at hu; simp at hu
  have hQR : Fintype.card V - k ≤ Q.card := by
    have h1 : Q.card + (univ.filter (fun u => ¬ (f u).isLeft = true)).card = univ.card :=
      card_filter_add_card_filter_not (s := (univ : Finset V)) (fun u => (f u).isLeft = true)
    have h2 : (univ.filter (fun u => ¬ (f u).isLeft = true)).card ≤ k := by
      have := card_le_card_of_injOn (s := univ.filter (fun u => ¬ (f u).isLeft = true))
        (t := (univ : Finset (Fin k)).map Function.Embedding.inr) f
        (by
          intro u hu
          have hu : ¬ (f u).isLeft = true := by simpa using hu
          simp only [coe_map, coe_univ, Set.image_univ, Set.mem_range,
            Function.Embedding.inr_apply]
          rcases hfu : f u with v | j
          · rw [hfu] at hu; simp at hu
          · exact ⟨j, rfl⟩)
        (hfinj.injOn)
      simpa using this
    rw [card_univ] at h1
    omega
  let M : Finset (Sym2 (Bool × V)) := Q.image (fun u => s((false, u), (true, h u)))
  have hMcard : M.card = Q.card := by
    apply card_image_of_injOn
    intro u _ u' _ huu
    simp only at huu
    rw [Sym2.eq_iff] at huu
    simp at huu
    exact huu.1
  have hM : IsMatching H M := by
    constructor
    · intro e he
      obtain ⟨u, hu, rfl⟩ := mem_image.1 he
      have := hft u
      rw [hQ u hu] at this
      simp only [t, inl_mem_disjSum, N, mem_filter, mem_univ, true_and, mem_singleton,
        exists_eq_left] at this
      exact this
    · intro e he e' he' hne x hx hx'
      obtain ⟨u, hu, rfl⟩ := mem_image.1 he
      obtain ⟨u', hu', rfl⟩ := mem_image.1 he'
      have huu : u ≠ u' := by rintro rfl; exact hne rfl
      have hhu : h u ≠ h u' := by
        intro hh
        apply huu
        apply hfinj
        rw [hQ u hu, hQ u' hu', hh]
      rw [Sym2.mem_iff] at hx hx'
      rcases hx with rfl | rfl <;> rcases hx' with h' | h' <;> simp_all
  have := card_le_matchingNumber hM
  have := matchingNumber_le_vcNumber H
  omega

theorem konig_doubleCover (G : SimpleGraph V) :
    vcNumber (doubleCover G) = matchingNumber (doubleCover G) :=
  konig _ (fun a u b v h => ((doubleCover_adj G a b u v).1 h).1)

end Konig

section FracVC

variable {V : Type*} [Fintype V]

omit [Fintype V] in
theorem isFracVC_one (G : SimpleGraph V) : IsFracVC G (fun _ => 1) :=
  ⟨fun _ => ⟨zero_le_one, le_rfl⟩, fun _ _ _ => by norm_num⟩

theorem fracVC_set_nonempty (G : SimpleGraph V) :
    {t | ∃ y, IsFracVC G y ∧ t = ∑ v, y v}.Nonempty :=
  ⟨_, _, isFracVC_one G, rfl⟩

theorem fracVC_set_bddBelow (G : SimpleGraph V) :
    BddBelow {t | ∃ y, IsFracVC G y ∧ t = ∑ v, y v} := by
  refine ⟨0, ?_⟩
  rintro t ⟨y, hy, rfl⟩
  exact sum_nonneg (fun v _ => (hy.1 v).1)

theorem fracVC_nonneg (G : SimpleGraph V) : 0 ≤ fracVC G :=
  le_csInf (fracVC_set_nonempty G) (by
    rintro t ⟨y, hy, rfl⟩
    exact sum_nonneg (fun v _ => (hy.1 v).1))

theorem fracVC_le {G : SimpleGraph V} {y : V → ℝ} (hy : IsFracVC G y) :
    fracVC G ≤ ∑ v, y v :=
  csInf_le (fracVC_set_bddBelow G) ⟨y, hy, rfl⟩

/-- Weak duality on the double cover: `μ(doubleCover G) ≤ 2 ∑ y` for any fractional VC `y`. -/
theorem matchingNumber_le_two_mul_sum {G : SimpleGraph V} {y : V → ℝ} (hy : IsFracVC G y) :
    (matchingNumber (doubleCover G) : ℝ) ≤ 2 * ∑ v, y v := by
  obtain ⟨M, hM, hMc⟩ := exists_matching_card (doubleCover G)
  have := card_le_sum_of_frac hM (fun p => y p.2) (fun p => (hy.1 p.2).1)
    (fun p q hpq => hy.2 _ _ ((doubleCover_adj G _ _ _ _).1 hpq).2)
  rw [Fintype.sum_prod_type, Fintype.sum_bool, hMc] at this
  linarith

/-- The fractional vertex cover number is half the matching number of the double cover. -/
theorem fracVC_eq (G : SimpleGraph V) :
    2 * fracVC G = (matchingNumber (doubleCover G) : ℝ) := by
  classical
  apply le_antisymm
  · obtain ⟨C, hC, hCc⟩ := exists_vc_card (doubleCover G)
    rw [konig_doubleCover] at hCc
    let ind : Bool × V → ℝ := fun p => if p ∈ C then 1 else 0
    let y : V → ℝ := fun v => (ind (false, v) + ind (true, v)) / 2
    have hind : ∀ p, 0 ≤ ind p ∧ ind p ≤ 1 := fun p => by
      simp only [ind]; split_ifs <;> norm_num
    have hy : IsFracVC G y := by
      refine ⟨fun v => ?_, fun u v huv => ?_⟩
      · have := hind (false, v); have := hind (true, v)
        simp only [y]; constructor <;> linarith
      · have h1 := hC (false, u) (true, v) ((doubleCover_adj G _ _ _ _).2 ⟨by decide, huv⟩)
        have h2 := hC (true, u) (false, v) ((doubleCover_adj G _ _ _ _).2 ⟨by decide, huv⟩)
        have h3 := hind (false, u); have h4 := hind (true, u)
        have h5 := hind (false, v); have h6 := hind (true, v)
        have e1 : ∀ p, p ∈ C → ind p = 1 := fun p hp => by simp [ind, hp]
        simp only [y]
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
          · have := e1 _ h1; have := e1 _ h2; linarith
    have hsum : ∑ v, y v = (C.card : ℝ) / 2 := by
      have hc : (C.card : ℝ) = ∑ p, ind p := by
        simp only [ind]
        rw [sum_boole]
        congr 2
        ext; simp
      rw [hc, Fintype.sum_prod_type, Fintype.sum_bool]
      simp only [y]
      rw [← sum_div, sum_add_distrib]
      ring
    have := fracVC_le hy
    rw [hsum, hCc] at this
    linarith
  · have : (matchingNumber (doubleCover G) : ℝ) / 2 ≤ fracVC G :=
      le_csInf (fracVC_set_nonempty G) (by
        rintro t ⟨y, hy, rfl⟩
        have := matchingNumber_le_two_mul_sum hy
        linarith)
    linarith

end FracVC

end MTSPKV

open GraphMatching in
theorem solution {W : Type*} [Fintype W] (H : SimpleGraph W) (M : Finset (Sym2 W))
    (hM : IsMatching H M) (hmax : ∀ e ∈ H.edgeSet, ∃ f ∈ M, ∃ x, x ∈ e ∧ x ∈ f) :
    matchingNumber H ≤ 2 * M.card :=
  MTSPKV.maximal_matching_half hM hmax
