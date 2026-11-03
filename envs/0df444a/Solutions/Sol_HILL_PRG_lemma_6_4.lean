-- Prove2me | solution 1 for HILL.PRG.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:25:21.413073+00:00
-- url     : https://prove2.me/submissions/f65b6dbe-7975-44b9-ba35-a4d8dbcfc92a

import Mathlib
import Definitions.Def_HILL_PRG_Model
import Definitions.Def_HILL_PRG_Constructions

open HILL.PRG
open scoped BigOperators

set_option maxHeartbeats 800000

namespace Lemma64Proof

noncomputable def fiber {α β : Type*} [Fintype α] (g : α → β) (x : α) : Finset α := by
  classical
  exact Finset.univ.filter (fun x' => g x' = g x)

noncomputable def fiberCard {α β : Type*} [Fintype α] (g : α → β) (x : α) : ℕ :=
  (fiber g x).card

@[simp]
lemma mem_fiber {α β : Type*} [Fintype α] (g : α → β) {x x' : α} :
    x' ∈ fiber g x ↔ g x' = g x := by
  classical
  simp [fiber]

lemma mem_fiber_self {α β : Type*} [Fintype α] (g : α → β) (x : α) :
    x ∈ fiber g x := by
  simp

lemma fiberCard_pos {α β : Type*} [Fintype α] (g : α → β) (x : α) :
    0 < fiberCard g x :=
  Finset.card_pos.mpr ⟨x, mem_fiber_self g x⟩

lemma filter_eq_fiber {α β : Type*} [Fintype α] [DecidableEq β] (g : α → β) (x : α) :
    Finset.univ.filter (fun x' => g x' = g x) = fiber g x := by
  ext z
  simp

lemma entropyOf_univ_eq {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [DecidableEq β]
    (g : α → β) :
    entropyOf (Finset.univ : Finset α) g =
      Real.logb 2 (Fintype.card α) -
        (∑ x : α, Real.logb 2 (fiberCard g x)) / (Fintype.card α) := by
  unfold entropyOf shannonOn lawOn
  let N : ℝ := (Fintype.card α : ℝ)
  have hN_pos : 0 < N := by dsimp [N]; exact Nat.cast_pos.mpr Fintype.card_pos
  have hcard : (Finset.univ : Finset α).card = Fintype.card α := Finset.card_univ
  have hterm : ∀ y ∈ (Finset.univ : Finset α).image g,
      -((((Finset.univ.filter (fun x => g x = y)).card : ℝ) / ((Finset.univ : Finset α).card : ℝ)) *
        Real.logb 2 (((Finset.univ.filter (fun x => g x = y)).card : ℝ) /
          ((Finset.univ : Finset α).card : ℝ))) =
      ∑ x ∈ Finset.univ.filter (fun x => g x = y),
        (Real.logb 2 N - Real.logb 2 (fiberCard g x)) / N := by
    intro y hy
    rw [hcard]
    change -(((Finset.univ.filter (fun x => g x = y)).card : ℝ) / N *
      Real.logb 2 (((Finset.univ.filter (fun x => g x = y)).card : ℝ) / N)) = _
    obtain ⟨x₀, _, rfl⟩ := Finset.mem_image.mp hy
    have hcongr : ∑ x ∈ Finset.univ.filter (fun x => g x = g x₀),
        (Real.logb 2 N - Real.logb 2 (fiberCard g x)) / N =
      ∑ _x ∈ fiber g x₀, (Real.logb 2 N - Real.logb 2 (fiberCard g x₀)) / N := by
      rw [filter_eq_fiber]
      refine Finset.sum_congr rfl (fun x hx => ?_)
      have hx' : g x = g x₀ := (mem_fiber g).mp hx
      have hf : fiber g x = fiber g x₀ := by ext z; simp [hx']
      simp [fiberCard, hf]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul, filter_eq_fiber]
    change -((fiberCard g x₀ : ℝ) / N * Real.logb 2 ((fiberCard g x₀ : ℝ) / N)) =
      (fiberCard g x₀ : ℝ) * ((Real.logb 2 N - Real.logb 2 (fiberCard g x₀)) / N)
    have hfc_pos : (0 : ℝ) < (fiberCard g x₀ : ℝ) :=
      Nat.cast_pos.mpr (fiberCard_pos g x₀)
    rw [Real.logb_div hfc_pos.ne' hN_pos.ne']
    ring
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_image_of_mem g (Finset.mem_univ x))]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change (N * Real.logb 2 N - ∑ x : α, Real.logb 2 (fiberCard g x)) / N =
    Real.logb 2 N - (∑ x : α, Real.logb 2 (fiberCard g x)) / N
  rw [sub_div, mul_div_cancel_left₀ _ hN_pos.ne']

lemma sum_pi_coord {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (k : ℕ) (ϕ : α → ℝ) (j : Fin k) :
    (∑ w : Fin k → α, ϕ (w j)) / (Fintype.card (Fin k → α) : ℝ) =
      (∑ a : α, ϕ a) / (Fintype.card α : ℝ) := by
  let e := (Equiv.piSplitAt j (fun _ : Fin k => α)).symm
  have hsum : (∑ w : Fin k → α, ϕ (w j)) =
      (Fintype.card ({i : Fin k // i ≠ j} → α) : ℝ) * (∑ a : α, ϕ a) := by
    rw [← Equiv.sum_comp e]
    change ∑ p : α × ({i : Fin k // i ≠ j} → α), ϕ (e p j) = _
    have hej : ∀ p : α × ({i : Fin k // i ≠ j} → α), e p j = p.1 := by
      intro p; simp [e]
    simp_rw [hej]
    rw [Fintype.sum_prod_type_right]
    dsimp only
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (Fin k → α) : ℝ) =
      (Fintype.card ({i : Fin k // i ≠ j} → α) : ℝ) * (Fintype.card α : ℝ) := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_prod] at hc
    exact_mod_cast ( by linarith [hc] :
      Fintype.card (Fin k → α) = Fintype.card ({i : Fin k // i ≠ j} → α) * Fintype.card α )
  have hpos : (0 : ℝ) < (Fintype.card ({i : Fin k // i ≠ j} → α) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  rw [hsum, hcard, mul_div_mul_left _ _ hpos.ne']

lemma sum_pi_sum {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (k : ℕ) (ϕ : α → ℝ) :
    (∑ w : Fin k → α, ∑ j : Fin k, ϕ (w j)) / (Fintype.card (Fin k → α) : ℝ) =
      (k : ℝ) * ((∑ a : α, ϕ a) / (Fintype.card α : ℝ)) := by
  rw [Finset.sum_comm, Finset.sum_div]
  simp_rw [sum_pi_coord k ϕ]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma binary_logb_split_bound (a c : ℕ) :
    (a : ℝ) * (Real.logb 2 (a + c) - Real.logb 2 a) +
      (c : ℝ) * (Real.logb 2 (a + c) - Real.logb 2 c) ≤
      if a + c ≤ 1 then 0 else (a + c : ℝ) := by
  split_ifs with hle
  · have hcases : a = 0 ∨ c = 0 := by omega
    rcases hcases with rfl | rfl <;> simp
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · rcases Nat.eq_zero_or_pos c with rfl | hc
      · simp
      · have ha' : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr ha
        have hc' : (0 : ℝ) < (c : ℝ) := Nat.cast_pos.mpr hc
        have hac' : (0 : ℝ) < (a : ℝ) + (c : ℝ) := by positivity
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have h1 := Real.log_le_sub_one_of_pos (show 0 < ((a : ℝ) + (c : ℝ)) / (2 * (a : ℝ)) by positivity)
        have h2 := Real.log_le_sub_one_of_pos (show 0 < ((a : ℝ) + (c : ℝ)) / (2 * (c : ℝ)) by positivity)
        have h1' : (a : ℝ) * (Real.log ((a : ℝ) + (c : ℝ)) - Real.log (a : ℝ) - Real.log 2) ≤
            ((c : ℝ) - (a : ℝ)) / 2 := by
          rw [Real.log_div hac'.ne' (by positivity), Real.log_mul (by norm_num) ha'.ne'] at h1
          have hmul := mul_le_mul_of_nonneg_left h1 ha'.le
          have hrhs : (a : ℝ) * (((a : ℝ) + (c : ℝ)) / (2 * (a : ℝ)) - 1) = ((c : ℝ) - (a : ℝ)) / 2 := by
            field_simp; ring
          linarith
        have h2' : (c : ℝ) * (Real.log ((a : ℝ) + (c : ℝ)) - Real.log (c : ℝ) - Real.log 2) ≤
            ((a : ℝ) - (c : ℝ)) / 2 := by
          rw [Real.log_div hac'.ne' (by positivity), Real.log_mul (by norm_num) hc'.ne'] at h2
          have hmul := mul_le_mul_of_nonneg_left h2 hc'.le
          have hrhs : (c : ℝ) * (((a : ℝ) + (c : ℝ)) / (2 * (c : ℝ)) - 1) = ((a : ℝ) - (c : ℝ)) / 2 := by
            field_simp; ring
          linarith
        have hsum : (a : ℝ) * (Real.log ((a : ℝ) + (c : ℝ)) - Real.log (a : ℝ)) +
            (c : ℝ) * (Real.log ((a : ℝ) + (c : ℝ)) - Real.log (c : ℝ)) ≤
            ((a : ℝ) + (c : ℝ)) * Real.log 2 := by linarith
        unfold Real.logb
        rw [← sub_div, ← mul_div_assoc, ← sub_div, ← mul_div_assoc, ← add_div, div_le_iff₀ hlog2]
        exact hsum

lemma bool_split_fiberCard_sum_le {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (g : α → β) (b : α → Bool) :
    ∑ w : α, (Real.logb 2 (fiberCard g w) - Real.logb 2 (fiberCard (fun x => (b x, g x)) w)) ≤
      ((Finset.univ.filter (fun w : α => 1 < fiberCard g w)).card : ℝ) := by
  let gD := fun x : α => (b x, g x)
  have h_on_fiber : ∀ y ∈ (Finset.univ : Finset α).image g,
      ∑ w ∈ Finset.univ.filter (fun x => g x = y),
        (Real.logb 2 (fiberCard g w) - Real.logb 2 (fiberCard gD w)) ≤
      ∑ w ∈ Finset.univ.filter (fun x => g x = y),
        (if 1 < fiberCard g w then (1 : ℝ) else 0) := by
    intro y hy
    obtain ⟨w₀, _, rfl⟩ := Finset.mem_image.mp hy
    let F := fiber g w₀
    let Ft := F.filter (fun x => b x = true)
    let Ff := F.filter (fun x => b x = false)
    have hpart : Ft ∪ Ff = F := by
      ext x; simp only [Ft, Ff, Finset.mem_union, Finset.mem_filter]
      cases b x <;> simp
    have hdisj : Disjoint Ft Ff := by
      rw [Finset.disjoint_filter]
      intro x _ h1 h2; rw [h1] at h2; cases h2
    have hcard_sum : Ft.card + Ff.card = F.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hpart]
    have hF_congr : ∀ w ∈ F, fiberCard g w = F.card := by
      intro w hw
      have hw' : g w = g w₀ := (mem_fiber g).mp hw
      have hf : fiber g w = F := by ext z; simp [F, hw']
      simp [fiberCard, hf]
    have hFt_congr : ∀ w ∈ Ft, fiberCard gD w = Ft.card := by
      intro w hw
      rcases Finset.mem_filter.mp hw with ⟨hwF, hbw⟩
      have hw' : g w = g w₀ := (mem_fiber g).mp hwF
      have hf : fiber gD w = Ft := by
        ext z; simp [Ft, F, gD, hw', hbw, and_comm]
      simp [fiberCard, hf]
    have hFf_congr : ∀ w ∈ Ff, fiberCard gD w = Ff.card := by
      intro w hw
      rcases Finset.mem_filter.mp hw with ⟨hwF, hbw⟩
      have hw' : g w = g w₀ := (mem_fiber g).mp hwF
      have hf : fiber gD w = Ff := by
        ext z; simp [Ff, F, gD, hw', hbw, and_comm]
      simp [fiberCard, hf]
    rw [filter_eq_fiber]
    change ∑ w ∈ F, (Real.logb 2 (fiberCard g w) - Real.logb 2 (fiberCard gD w)) ≤
      ∑ w ∈ F, (if 1 < fiberCard g w then (1 : ℝ) else 0)
    rw [← hpart, Finset.sum_union hdisj]
    have hsum_t : ∑ w ∈ Ft, (Real.logb 2 (fiberCard g w) - Real.logb 2 (fiberCard gD w)) =
        (Ft.card : ℝ) * (Real.logb 2 (Ft.card + Ff.card) - Real.logb 2 Ft.card) := by
      have : ∑ w ∈ Ft, (Real.logb 2 (fiberCard g w) - Real.logb 2 (fiberCard gD w)) =
          ∑ _w ∈ Ft, (Real.logb 2 F.card - Real.logb 2 Ft.card) := by
        refine Finset.sum_congr rfl (fun w hw => ?_)
        rw [hF_congr w (Finset.mem_filter.mp hw).1, hFt_congr w hw]
      rw [this, Finset.sum_const, nsmul_eq_mul, ← hcard_sum]
      push_cast; rfl
    have hsum_f : ∑ w ∈ Ff, (Real.logb 2 (fiberCard g w) - Real.logb 2 (fiberCard gD w)) =
        (Ff.card : ℝ) * (Real.logb 2 (Ft.card + Ff.card) - Real.logb 2 Ff.card) := by
      have : ∑ w ∈ Ff, (Real.logb 2 (fiberCard g w) - Real.logb 2 (fiberCard gD w)) =
          ∑ _w ∈ Ff, (Real.logb 2 F.card - Real.logb 2 Ff.card) := by
        refine Finset.sum_congr rfl (fun w hw => ?_)
        rw [hF_congr w (Finset.mem_filter.mp hw).1, hFf_congr w hw]
      rw [this, Finset.sum_const, nsmul_eq_mul, ← hcard_sum]
      push_cast; rfl
    have hrhs : ∑ w ∈ F, (if 1 < fiberCard g w then (1 : ℝ) else 0) =
        if Ft.card + Ff.card ≤ 1 then 0 else (Ft.card + Ff.card : ℝ) := by
      have : ∑ w ∈ F, (if 1 < fiberCard g w then (1 : ℝ) else 0) =
          ∑ _w ∈ F, (if 1 < F.card then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun w hw => ?_)
        rw [hF_congr w hw]
      rw [this, Finset.sum_const, nsmul_eq_mul, ← hcard_sum]
      split_ifs with h1 h2
      · omega
      · push_cast; ring
      · push_cast; ring
      · omega
    rw [hsum_t, hsum_f, hpart, hrhs]
    exact binary_logb_split_bound Ft.card Ff.card
  rw [← Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_image_of_mem g (Finset.mem_univ x))]
  calc ∑ y ∈ Finset.univ.image g, ∑ w ∈ Finset.univ.filter (fun x => g x = y),
        (Real.logb 2 (fiberCard g w) - Real.logb 2 (fiberCard gD w))
    ≤ ∑ y ∈ Finset.univ.image g, ∑ w ∈ Finset.univ.filter (fun x => g x = y),
        (if 1 < fiberCard g w then (1 : ℝ) else 0) := Finset.sum_le_sum h_on_fiber
  _ = ∑ w ∈ (Finset.univ : Finset α), (if 1 < fiberCard g w then (1 : ℝ) else 0) :=
        Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_image_of_mem g (Finset.mem_univ x)) _
  _ = ((Finset.univ.filter (fun w : α => 1 < fiberCard g w)).card : ℝ) := by
        rw [Finset.card_filter]; push_cast; rfl

lemma cube_card (n : ℕ) : (cube n).card = 2 ^ n := by
  change (Finset.univ.image (fun v : Fin n → Bool => List.ofFn v)).card = _
  rw [Finset.card_image_of_injective _ List.ofFn_injective]
  simp

lemma mem_cube {n : ℕ} {x : Bits} : x ∈ cube n ↔ x.length = n := by
  constructor
  · intro hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    simp
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨fun i : Fin n => x[i.val]'(by omega), Finset.mem_univ _, ?_⟩
    apply List.ext_getElem
    · simpa using hx.symm
    · intro i hi hj
      simp

lemma hash_length (h : HashFamily) (hh : h.IsUniversal) (n : ℕ)
    (key x : Bits) (hk : key ∈ cube (h.keyLen n)) (hx : x ∈ cube (h.inLen n)) :
    h.eval n key x ∈ cube (h.outLen n) := by
  obtain ⟨_, _, _, _, M, _, heval⟩ := hh.1
  exact mem_cube.mpr (heval n key x hk hx).2

lemma card_cube_filter_take_eq {M L : ℕ} (hL : L ≤ M) {a : Bits} (ha : a ∈ cube M) :
    ((cube M).filter (fun a' => a'.take L = a.take L)).card = 2 ^ (M - L) := by
  have ha_len : a.length = M := mem_cube.mp ha
  have htake_len : (a.take L).length = L := by simp [ha_len, hL]
  have himg : (cube (M - L)).image (fun w => a.take L ++ w) =
      (cube M).filter (fun a' => a'.take L = a.take L) := by
    ext a'
    simp only [Finset.mem_image, Finset.mem_filter, mem_cube]
    constructor
    · rintro ⟨w, hw_len, rfl⟩
      refine ⟨by simp [htake_len, hw_len, hL], ?_⟩
      rw [List.take_append_of_le_length (by omega), List.take_take, Nat.min_self]
    · rintro ⟨ha'_len, htake⟩
      refine ⟨a'.drop L, by simp [ha'_len], ?_⟩
      rw [← htake, List.take_append_drop]
  rw [← himg, Finset.card_image_of_injective _ (fun w₁ w₂ h => by simpa using h), cube_card]

lemma hash_prefix_collision_card (h : HashFamily) (hh : h.IsUniversal) (n : ℕ)
    {u u' : Bits} (hu : u ∈ cube (h.inLen n)) (hu' : u' ∈ cube (h.inLen n)) (hne : u ≠ u')
    {L : ℕ} (hL : L ≤ h.outLen n) :
    (((cube (h.keyLen n)).filter
      (fun key => (h.eval n key u').take L = (h.eval n key u).take L)).card) * 2 ^ L =
      2 ^ (h.keyLen n) := by
  let M := h.outLen n
  let K := h.keyLen n
  let P := (cube M ×ˢ cube M).filter (fun p : Bits × Bits => p.2.take L = p.1.take L)
  have hP_card : P.card = 2 ^ M * 2 ^ (M - L) := by
    have h1 : P.card = ∑ a ∈ cube M, ((cube M).filter (fun a' => a'.take L = a.take L)).card := by
      dsimp [P]
      rw [Finset.card_filter, Finset.sum_product]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.card_filter]
    rw [h1, Finset.sum_congr rfl (fun a ha => card_cube_filter_take_eq hL ha),
      Finset.sum_const, cube_card, smul_eq_mul]
  have hpart : (cube K).filter (fun key => (h.eval n key u').take L = (h.eval n key u).take L) =
      P.biUnion (fun p => (cube K).filter (fun key => h.eval n key u = p.1 ∧ h.eval n key u' = p.2)) := by
    ext key
    simp only [Finset.mem_filter, Finset.mem_biUnion, P, Prod.exists, Finset.mem_product]
    constructor
    · rintro ⟨hk, htake⟩
      exact ⟨h.eval n key u, h.eval n key u',
        ⟨⟨hash_length h hh n key u hk hu, hash_length h hh n key u' hk hu'⟩, htake⟩,
        hk, rfl, rfl⟩
    · rintro ⟨a, a', ⟨_, htake⟩, hk, rfl, rfl⟩
      exact ⟨hk, htake⟩
  have hdisj : (P : Set (Bits × Bits)).PairwiseDisjoint
      (fun p => (cube K).filter (fun key => h.eval n key u = p.1 ∧ h.eval n key u' = p.2)) := by
    intro p₁ _ p₂ _ hpne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro key hk₁ hk₂
    rcases Finset.mem_filter.mp hk₁ with ⟨_, h1, h2⟩
    rcases Finset.mem_filter.mp hk₂ with ⟨_, h3, h4⟩
    exact hpne (Prod.ext (h1.symm.trans h3) (h2.symm.trans h4))
  have hcard_sum : ((cube K).filter (fun key => (h.eval n key u').take L = (h.eval n key u).take L)).card *
      2 ^ (2 * M) = P.card * 2 ^ K := by
    rw [hpart, Finset.card_biUnion hdisj, Finset.sum_mul]
    have hcongr : ∀ p ∈ P,
        ((cube K).filter (fun key => h.eval n key u = p.1 ∧ h.eval n key u' = p.2)).card * 2 ^ (2 * M) =
        2 ^ K := by
      intro p hp
      rcases (Finset.mem_filter.mp hp).1 |> Finset.mem_product.mp with ⟨hp1, hp2⟩
      exact hh.2 n u u' p.1 p.2 hu hu' hne hp1 hp2
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul]
  have h2M : 2 ^ M * 2 ^ (M - L) * 2 ^ L = 2 ^ (2 * M) := by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hL, ← pow_add, two_mul]
  have hmul : (((cube K).filter (fun key => (h.eval n key u').take L = (h.eval n key u).take L)).card * 2 ^ L) *
      2 ^ (2 * M) = 2 ^ K * 2 ^ (2 * M) := by
    calc (((cube K).filter (fun key => (h.eval n key u').take L = (h.eval n key u).take L)).card * 2 ^ L) *
          2 ^ (2 * M)
      = (((cube K).filter (fun key => (h.eval n key u').take L = (h.eval n key u).take L)).card *
          2 ^ (2 * M)) * 2 ^ L := by ring
    _ = (P.card * 2 ^ K) * 2 ^ L := by rw [hcard_sum]
    _ = 2 ^ K * (2 ^ M * 2 ^ (M - L) * 2 ^ L) := by rw [hP_card]; ring
    _ = 2 ^ K * 2 ^ (2 * M) := by rw [h2M]
  exact Nat.eq_of_mul_eq_mul_right (by positivity) hmul

abbrev Ω₀ (n r : ℕ) := (Fin n → Bool) × Fin n × (Fin r → Bool)
abbrev Ω₁ (n r : ℕ) := Ω₀ n r × (Fin n → Bool)

def fP (F : FunEns) (h : HashFamily) (n : ℕ) (w₀ : Ω₀ n (h.keyLen n)) :
    Bits × Bits × Fin n × Bits :=
  fPrime64 F h n w₀.1 w₀.2.1 w₀.2.2

def gE1 (F : FunEns) (h : HashFamily) (n : ℕ) (w : Ω₁ n (h.keyLen n)) :
    (Bits × Bits × Fin n × Bits) × (Fin n → Bool) :=
  (fP F h n w.1, w.2)

def b1 (n r : ℕ) (w : Ω₁ n r) : Bool :=
  ip (List.ofFn w.1.1) (List.ofFn w.2)

def gD1 (F : FunEns) (h : HashFamily) (n : ℕ) (w : Ω₁ n (h.keyLen n)) :
    Bool × (Bits × Bits × Fin n × Bits) × (Fin n → Bool) :=
  (b1 n (h.keyLen n) w, gE1 F h n w)

lemma fiberCard_gE1 (F : FunEns) (h : HashFamily) (n : ℕ) (w : Ω₁ n (h.keyLen n)) :
    fiberCard (gE1 F h n) w = fiberCard (fP F h n) w.1 := by
  have hf : fiber (gE1 F h n) w = (fiber (fP F h n) w.1).image (fun w₀' => (w₀', w.2)) := by
    ext ⟨w₀', y'⟩
    simp only [mem_fiber, Finset.mem_image, Prod.mk.injEq, gE1]
    constructor
    · rintro ⟨h1, rfl⟩; exact ⟨w₀', h1, rfl, rfl⟩
    · rintro ⟨w₀'', h1, rfl, rfl⟩; exact ⟨h1, rfl⟩
  unfold fiberCard
  rw [hf, Finset.card_image_of_injective _ (fun a b hab => (Prod.ext_iff.mp hab).1)]

lemma filter_one_lt_fiberCard_gE1 (F : FunEns) (h : HashFamily) (n : ℕ) :
    ((Finset.univ.filter (fun w : Ω₁ n (h.keyLen n) => 1 < fiberCard (gE1 F h n) w)).card : ℝ) /
      (Fintype.card (Ω₁ n (h.keyLen n)) : ℝ) =
    ((Finset.univ.filter (fun w₀ : Ω₀ n (h.keyLen n) => 1 < fiberCard (fP F h n) w₀)).card : ℝ) /
      (Fintype.card (Ω₀ n (h.keyLen n)) : ℝ) := by
  have hf : Finset.univ.filter (fun w : Ω₁ n (h.keyLen n) => 1 < fiberCard (gE1 F h n) w) =
      (Finset.univ.filter (fun w₀ : Ω₀ n (h.keyLen n) => 1 < fiberCard (fP F h n) w₀)) ×ˢ
        (Finset.univ : Finset (Fin n → Bool)) := by
    ext w
    simp [fiberCard_gE1]
  rw [hf, Finset.card_product, Finset.card_univ, Fintype.card_prod]
  push_cast
  have hpos : (0 : ℝ) < (Fintype.card (Fin n → Bool) : ℝ) := by positivity
  exact mul_div_mul_right _ _ hpos.ne'

def seedEquiv (n k r u : ℕ) :
    Seed64 n k r u ≃ (Fin k → Ω₁ n r) × (Fin u → Bool) where
  toFun s := (fun j => ((s.X j, s.I j, s.R j), s.Y j), s.U)
  invFun p := ⟨fun j => (p.1 j).1.1, fun j => (p.1 j).1.2.1, fun j => (p.1 j).1.2.2, p.2, fun j => (p.1 j).2⟩
  left_inv s := by cases s; rfl
  right_inv p := by rcases p with ⟨w, U⟩; ext j <;> rfl

lemma mem_map_symm {A B : Type*} (e : A ≃ B) (S : Finset B) (x : A) :
    x ∈ S.map e.symm.toEmbedding ↔ e x ∈ S := by
  rw [Finset.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro hx; exact ⟨e x, hx, by simp⟩

lemma fiberCard_outE64 (F : FunEns) (h hp : HashFamily) (n k m : ℕ)
    (p : Seed64 n k (h.keyLen n) (hp.keyLen n) × (Fin m → Bool)) :
    fiberCard (fun z : Seed64 n k (h.keyLen n) (hp.keyLen n) × (Fin m → Bool) =>
      outE64 F h hp n k m z.1 z.2) p =
    ∏ j : Fin k, fiberCard (gE1 F h n)
      ((seedEquiv n k (h.keyLen n) (hp.keyLen n) p.1).1 j) := by
  let r := h.keyLen n
  let u := hp.keyLen n
  let e := (seedEquiv n k r u).prodCongr (Equiv.refl (Fin m → Bool))
  let S := (Fintype.piFinset (fun j => fiber (gE1 F h n) ((seedEquiv n k r u p.1).1 j)) ×ˢ
    ({p.1.U} : Finset (Fin u → Bool))) ×ˢ ({p.2} : Finset (Fin m → Bool))
  have hmap : fiber (fun z : Seed64 n k r u × (Fin m → Bool) => outE64 F h hp n k m z.1 z.2) p =
      S.map e.symm.toEmbedding := by
    ext ⟨s', w'⟩
    rw [mem_map_symm, mem_fiber]
    change outE64 F h hp n k m s' w' = outE64 F h hp n k m p.1 p.2 ↔
      ((fun j => ((s'.X j, s'.I j, s'.R j), s'.Y j), s'.U), w') ∈ S
    simp only [S, u, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_singleton,
      mem_fiber, outE64, Out64, Prod.mk.injEq, List.ofFn_inj, funext_iff, forall_and,
      gE1, fP, seedEquiv, Equiv.coe_fn_mk]
    tauto
  have hcard := congrArg Finset.card hmap
  rw [Finset.card_map] at hcard
  dsimp [S] at hcard
  rw [Finset.card_product, Finset.card_product, Finset.card_singleton, Finset.card_singleton,
    mul_one, mul_one, Fintype.card_piFinset] at hcard
  exact hcard

lemma prod_fiberCard_gD1_le_outD64 (F : FunEns) (h hp : HashFamily) (n k : ℕ)
    (s : Seed64 n k (h.keyLen n) (hp.keyLen n)) :
    ∏ j : Fin k, fiberCard (gD1 F h n)
      ((seedEquiv n k (h.keyLen n) (hp.keyLen n) s).1 j) ≤
    fiberCard (outD64 F h hp n k) s := by
  let r := h.keyLen n
  let u := hp.keyLen n
  let e := seedEquiv n k r u
  let S := Fintype.piFinset (fun j => fiber (gD1 F h n) ((e s).1 j)) ×ˢ
    ({s.U} : Finset (Fin u → Bool))
  have hsub : S.map e.symm.toEmbedding ⊆ fiber (outD64 F h hp n k) s := by
    intro s' hs'
    rw [mem_map_symm] at hs'
    rw [mem_fiber]
    simp only [S, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_singleton,
      mem_fiber, e, seedEquiv, Equiv.coe_fn_mk] at hs'
    rcases hs' with ⟨hj, hU⟩
    have hX_Y : (fun j : Fin k => ip (List.ofFn (s'.X j)) (List.ofFn (s'.Y j))) =
        (fun j : Fin k => ip (List.ofFn (s.X j)) (List.ofFn (s.Y j))) := by
      funext j
      exact (Prod.ext_iff.mp (hj j)).1
    have hfP : (fun j : Fin k => fPrime64 F h n (s'.X j) (s'.I j) (s'.R j)) =
        (fun j : Fin k => fPrime64 F h n (s.X j) (s.I j) (s.R j)) := by
      funext j
      exact (Prod.ext_iff.mp (Prod.ext_iff.mp (hj j)).2).1
    have hY : s'.Y = s.Y := by
      funext j
      exact (Prod.ext_iff.mp (Prod.ext_iff.mp (hj j)).2).2
    have hU' : s'.U = s.U := hU
    unfold outD64
    rw [hX_Y, hfP, hU', hY]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_map] at hle
  dsimp [S] at hle
  rw [Finset.card_product, Finset.card_singleton, mul_one, Fintype.card_piFinset] at hle
  exact hle

lemma sum_seed_coord (n k r u : ℕ) (hn : 1 ≤ n) (ϕ : Ω₁ n r → ℝ) :
    (∑ s : Seed64 n k r u, ∑ j : Fin k, ϕ ((seedEquiv n k r u s).1 j)) /
      (Fintype.card (Seed64 n k r u) : ℝ) =
    (k : ℝ) * ((∑ w : Ω₁ n r, ϕ w) / (Fintype.card (Ω₁ n r) : ℝ)) := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let e := seedEquiv n k r u
  have hsum : (∑ s : Seed64 n k r u, ∑ j : Fin k, ϕ ((e s).1 j)) =
      (Fintype.card (Fin u → Bool) : ℝ) * (∑ w : Fin k → Ω₁ n r, ∑ j : Fin k, ϕ (w j)) := by
    rw [← Equiv.sum_comp e.symm]
    simp only [Equiv.apply_symm_apply]
    rw [Fintype.sum_prod_type_right]
    dsimp only
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (Seed64 n k r u) : ℝ) =
      (Fintype.card (Fin u → Bool) : ℝ) * (Fintype.card (Fin k → Ω₁ n r) : ℝ) := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_prod] at hc
    exact_mod_cast (by linarith [hc] :
      Fintype.card (Seed64 n k r u) = Fintype.card (Fin u → Bool) * Fintype.card (Fin k → Ω₁ n r))
  have hu_pos : (0 : ℝ) < (Fintype.card (Fin u → Bool) : ℝ) := by positivity
  rw [hsum, hcard, mul_div_mul_left _ _ hu_pos.ne', sum_pi_sum]

lemma entropy_diff_ge_collision (F : FunEns) (h hp : HashFamily) (n k m : ℕ) (hn : 1 ≤ n) :
    entropyE64 F h hp n k m - entropyD64 F h hp n k ≥
      (m : ℝ) - (k : ℝ) *
        (((Finset.univ.filter (fun w₀ : Ω₀ n (h.keyLen n) => 1 < fiberCard (fP F h n) w₀)).card : ℝ) /
          (Fintype.card (Ω₀ n (h.keyLen n)) : ℝ)) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let r := h.keyLen n
  let u := hp.keyLen n
  have : Nonempty (Seed64 n k r u) :=
    ⟨⟨fun _ _ => false, fun _ => ⟨0, by omega⟩, fun _ _ => false, fun _ => false, fun _ _ => false⟩⟩
  let N_S : ℝ := (Fintype.card (Seed64 n k r u) : ℝ)
  let N_Z : ℝ := (Fintype.card (Fin m → Bool) : ℝ)
  have hNS_pos : 0 < N_S := Nat.cast_pos.mpr Fintype.card_pos
  have hNZ_pos : 0 < N_Z := by dsimp [N_Z]; positivity
  have hNZ_eq : N_Z = (2 : ℝ) ^ m := by
    dsimp [N_Z]; rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; rfl
  have hlogb2 : Real.logb 2 2 = 1 := by
    unfold Real.logb; exact div_self (Real.log_pos (by norm_num)).ne'
  have hE : entropyE64 F h hp n k m =
      Real.logb 2 N_S + (m : ℝ) -
        (k : ℝ) * ((∑ w : Ω₁ n r, Real.logb 2 (fiberCard (gE1 F h n) w)) /
          (Fintype.card (Ω₁ n r) : ℝ)) := by
    unfold entropyE64
    rw [entropyOf_univ_eq]
    have hcard_prod : (Fintype.card (Seed64 n k r u × (Fin m → Bool)) : ℝ) = N_S * N_Z := by
      rw [Fintype.card_prod]; push_cast; rfl
    have hlog_prod : Real.logb 2 (Fintype.card (Seed64 n k r u × (Fin m → Bool)) : ℝ) =
        Real.logb 2 N_S + (m : ℝ) := by
      rw [hcard_prod, Real.logb_mul hNS_pos.ne' hNZ_pos.ne', hNZ_eq,
        Real.logb_pow, hlogb2, mul_one]
    have hlog_fc : ∀ p : Seed64 n k r u × (Fin m → Bool),
        Real.logb 2 (fiberCard (fun z => outE64 F h hp n k m z.1 z.2) p) =
        ∑ j : Fin k, Real.logb 2 (fiberCard (gE1 F h n) ((seedEquiv n k r u p.1).1 j)) := by
      intro p
      rw [fiberCard_outE64, Nat.cast_prod]
      unfold Real.logb
      rw [Real.log_prod (fun j _ => Nat.cast_ne_zero.mpr (fiberCard_pos _ _).ne'), Finset.sum_div]
    rw [hlog_prod]
    congr 1
    rw [Finset.sum_congr rfl (fun p _ => hlog_fc p)]
    rw [Fintype.sum_prod_type_right]
    dsimp only
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      hcard_prod, mul_comm N_S N_Z, mul_div_mul_left _ _ hNZ_pos.ne']
    exact sum_seed_coord n k r u hn (fun w => Real.logb 2 (fiberCard (gE1 F h n) w))
  have hD : entropyD64 F h hp n k ≤
      Real.logb 2 N_S -
        (k : ℝ) * ((∑ w : Ω₁ n r, Real.logb 2 (fiberCard (gD1 F h n) w)) /
          (Fintype.card (Ω₁ n r) : ℝ)) := by
    unfold entropyD64
    rw [entropyOf_univ_eq]
    change Real.logb 2 N_S - (∑ s : Seed64 n k r u, Real.logb 2 (fiberCard (outD64 F h hp n k) s)) / N_S ≤ _
    have hle_sum : (∑ s : Seed64 n k r u,
        ∑ j : Fin k, Real.logb 2 (fiberCard (gD1 F h n) ((seedEquiv n k r u s).1 j))) ≤
        ∑ s : Seed64 n k r u, Real.logb 2 (fiberCard (outD64 F h hp n k) s) := by
      refine Finset.sum_le_sum (fun s _ => ?_)
      have hprod_le := prod_fiberCard_gD1_le_outD64 F h hp n k s
      have hpos_prod : (0 : ℝ) < ((∏ j : Fin k, fiberCard (gD1 F h n) ((seedEquiv n k r u s).1 j) : ℕ) : ℝ) := by
        exact_mod_cast Finset.prod_pos (fun j _ => fiberCard_pos _ _)
      have hlog_le : Real.logb 2 ((∏ j : Fin k, fiberCard (gD1 F h n) ((seedEquiv n k r u s).1 j) : ℕ) : ℝ) ≤
          Real.logb 2 (fiberCard (outD64 F h hp n k) s : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num) hpos_prod (Nat.cast_le.mpr hprod_le)
      have hlog_eq : Real.logb 2 ((∏ j : Fin k, fiberCard (gD1 F h n) ((seedEquiv n k r u s).1 j) : ℕ) : ℝ) =
          ∑ j : Fin k, Real.logb 2 (fiberCard (gD1 F h n) ((seedEquiv n k r u s).1 j)) := by
        rw [Nat.cast_prod]
        unfold Real.logb
        rw [Real.log_prod (fun j _ => Nat.cast_ne_zero.mpr (fiberCard_pos _ _).ne'), Finset.sum_div]
      linarith
    have hdiv_le := div_le_div_of_nonneg_right hle_sum hNS_pos.le
    rw [sum_seed_coord n k r u hn (fun w => Real.logb 2 (fiberCard (gD1 F h n) w))] at hdiv_le
    linarith
  have hsplit := bool_split_fiberCard_sum_le (gE1 F h n) (b1 n r)
  have hOmega_pos : (0 : ℝ) < (Fintype.card (Ω₁ n r) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hdiv_split : (∑ w : Ω₁ n r, Real.logb 2 (fiberCard (gE1 F h n) w)) / (Fintype.card (Ω₁ n r) : ℝ) -
      (∑ w : Ω₁ n r, Real.logb 2 (fiberCard (gD1 F h n) w)) / (Fintype.card (Ω₁ n r) : ℝ) ≤
      ((Finset.univ.filter (fun w₀ : Ω₀ n r => 1 < fiberCard (fP F h n) w₀)).card : ℝ) /
        (Fintype.card (Ω₀ n r) : ℝ) := by
    rw [← sub_div, ← Finset.sum_sub_distrib, ← filter_one_lt_fiberCard_gE1]
    exact div_le_div_of_nonneg_right hsplit hOmega_pos.le
  have hk_mul := mul_le_mul_of_nonneg_left hdiv_split (Nat.cast_nonneg k)
  linarith

def Sf (F : FunEns) (n : ℕ) (x : Fin n → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x' => x' ≠ x ∧ F.f 0 n (List.ofFn x') = F.f 0 n (List.ofFn x))

lemma card_Sf_le_pow_Dtilde (F : FunEns) (n : ℕ) (x : Fin n → Bool) :
    (Sf F n x).card ≤ 2 ^ Dtilde (cube n) (F.f 0 n) (F.f 0 n (List.ofFn x)) := by
  have hx_not_mem : x ∉ Sf F n x := by simp [Sf]
  have himg : (insert x (Sf F n x)).image List.ofFn =
      (cube n).filter (fun z => F.f 0 n z = F.f 0 n (List.ofFn x)) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_insert, Sf, Finset.mem_filter,
      cube, Levin2003.cube, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x', hmem | ⟨_, hfx'⟩, rfl⟩
      · rw [hmem]; exact ⟨⟨x, rfl⟩, rfl⟩
      · exact ⟨⟨x', rfl⟩, hfx'⟩
    · rintro ⟨⟨x', rfl⟩, hfx'⟩
      by_cases hxx' : x' = x
      · rw [hxx']; exact ⟨x, Or.inl rfl, rfl⟩
      · exact ⟨x', Or.inr ⟨hxx', hfx'⟩, rfl⟩
  have hcard : (Sf F n x).card + 1 =
      ((cube n).filter (fun z => F.f 0 n z = F.f 0 n (List.ofFn x))).card := by
    rw [← himg, Finset.card_image_of_injective _ List.ofFn_injective,
      Finset.card_insert_of_notMem hx_not_mem]
  have hpow : ((cube n).filter (fun z => F.f 0 n z = F.f 0 n (List.ofFn x))).card ≤
      2 ^ Dtilde (cube n) (F.f 0 n) (F.f 0 n (List.ofFn x)) :=
    Nat.le_pow_clog (by norm_num : 1 < 2) _
  omega

lemma card_r_collision_When_ge (F : FunEns) (n : ℕ) (h : HashFamily) (hh : h.IsUniversal)
    (hin : h.inLen n = n) (hout : h.outLen n = n + Nat.clog 2 (2 * n))
    (x : Fin n → Bool) (i : Fin n)
    (hi : Dtilde (cube n) (F.f 0 n) (F.f 0 n (List.ofFn x)) ≤ i.val) :
    ((Finset.univ.filter (fun ρ : Fin (h.keyLen n) → Bool =>
      1 < fiberCard (fP F h n) (x, (i, ρ)))).card) * (2 * n) ≤
    2 ^ (h.keyLen n) := by
  let r := h.keyLen n
  let c := Nat.clog 2 (2 * n)
  let L := i.val + c
  have hL_le : L ≤ h.outLen n := by
    rw [hout]; dsimp [L, c]; have := i.isLt; omega
  have hsub : Finset.univ.filter (fun ρ : Fin r → Bool => 1 < fiberCard (fP F h n) (x, (i, ρ))) ⊆
      (Sf F n x).biUnion (fun x' => Finset.univ.filter (fun ρ : Fin r → Bool =>
        (h.eval n (List.ofFn ρ) (List.ofFn x')).take L =
          (h.eval n (List.ofFn ρ) (List.ofFn x)).take L)) := by
    intro ρ hρ
    have hρ' : 1 < (fiber (fP F h n) (x, (i, ρ))).card := (Finset.mem_filter.mp hρ).2
    obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := Finset.one_lt_card.mp hρ'
    have hex : ∃ w' ∈ fiber (fP F h n) (x, (i, ρ)), w' ≠ (x, (i, ρ)) := by
      by_cases h1 : w₁ = (x, (i, ρ))
      · subst h1; exact ⟨w₂, hw₂, hne.symm⟩
      · exact ⟨w₁, hw₁, h1⟩
    rcases hex with ⟨⟨x', i', ρ'⟩, hw', hne'⟩
    simp only [mem_fiber, fP, fPrime64, Prod.mk.injEq, List.ofFn_inj] at hw'
    rcases hw' with ⟨hfx', htake, rfl, rfl⟩
    have hxx' : x' ≠ x := by
      intro h; subst h; exact hne' rfl
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x', by simp [Sf, hxx', hfx'], htake⟩
  have h_each : ∀ x' ∈ Sf F n x,
      ((Finset.univ.filter (fun ρ : Fin r → Bool =>
        (h.eval n (List.ofFn ρ) (List.ofFn x')).take L =
          (h.eval n (List.ofFn ρ) (List.ofFn x)).take L)).card) * 2 ^ L = 2 ^ r := by
    intro x' hx'
    rcases (Finset.mem_filter.mp hx').2 with ⟨hxx', _⟩
    have himg : (Finset.univ.filter (fun ρ : Fin r → Bool =>
        (h.eval n (List.ofFn ρ) (List.ofFn x')).take L =
          (h.eval n (List.ofFn ρ) (List.ofFn x)).take L)).image List.ofFn =
      (cube r).filter (fun key =>
        (h.eval n key (List.ofFn x')).take L = (h.eval n key (List.ofFn x)).take L) := by
      ext key
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        cube, Levin2003.cube]
      constructor
      · rintro ⟨ρ, htake, rfl⟩
        exact ⟨⟨ρ, rfl⟩, htake⟩
      · rintro ⟨⟨ρ, rfl⟩, htake⟩
        exact ⟨ρ, htake, rfl⟩
    have hcard_eq : (Finset.univ.filter (fun ρ : Fin r → Bool =>
        (h.eval n (List.ofFn ρ) (List.ofFn x')).take L =
          (h.eval n (List.ofFn ρ) (List.ofFn x)).take L)).card =
      ((cube r).filter (fun key =>
        (h.eval n key (List.ofFn x')).take L = (h.eval n key (List.ofFn x)).take L)).card := by
      rw [← himg, Finset.card_image_of_injective _ List.ofFn_injective]
    rw [hcard_eq]
    have hu : List.ofFn x ∈ cube (h.inLen n) := by
      rw [hin]; exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
    have hu' : List.ofFn x' ∈ cube (h.inLen n) := by
      rw [hin]; exact Finset.mem_image_of_mem _ (Finset.mem_univ x')
    have hne_u : List.ofFn x ≠ List.ofFn x' := fun h => hxx' (List.ofFn_injective h.symm)
    exact hash_prefix_collision_card h hh n hu hu' hne_u hL_le
  have hbi : ((Finset.univ.filter (fun ρ : Fin r → Bool =>
      1 < fiberCard (fP F h n) (x, (i, ρ)))).card) * 2 ^ L ≤
      (Sf F n x).card * 2 ^ r := by
    calc ((Finset.univ.filter (fun ρ : Fin r → Bool =>
          1 < fiberCard (fP F h n) (x, (i, ρ)))).card) * 2 ^ L
      ≤ ((Sf F n x).biUnion (fun x' => Finset.univ.filter (fun ρ : Fin r → Bool =>
          (h.eval n (List.ofFn ρ) (List.ofFn x')).take L =
            (h.eval n (List.ofFn ρ) (List.ofFn x)).take L))).card * 2 ^ L := by
          gcongr
    _ ≤ (∑ x' ∈ Sf F n x, (Finset.univ.filter (fun ρ : Fin r → Bool =>
          (h.eval n (List.ofFn ρ) (List.ofFn x')).take L =
            (h.eval n (List.ofFn ρ) (List.ofFn x)).take L)).card) * 2 ^ L := by
          gcongr; exact Finset.card_biUnion_le
    _ = ∑ x' ∈ Sf F n x, ((Finset.univ.filter (fun ρ : Fin r → Bool =>
          (h.eval n (List.ofFn ρ) (List.ofFn x')).take L =
            (h.eval n (List.ofFn ρ) (List.ofFn x)).take L)).card) * 2 ^ L := Finset.sum_mul _ _ _
    _ = ∑ _x' ∈ Sf F n x, 2 ^ r := Finset.sum_congr rfl h_each
    _ = (Sf F n x).card * 2 ^ r := by rw [Finset.sum_const, smul_eq_mul]
  have hSf_le : (Sf F n x).card ≤ 2 ^ i.val :=
    (card_Sf_le_pow_Dtilde F n x).trans (Nat.pow_le_pow_right (by norm_num) hi)
  have h2n_le : 2 * n ≤ 2 ^ c := Nat.le_pow_clog (by norm_num : 1 < 2) (2 * n)
  have hmul_le : ((Finset.univ.filter (fun ρ : Fin r → Bool =>
      1 < fiberCard (fP F h n) (x, (i, ρ)))).card * (2 * n)) * 2 ^ i.val ≤
      2 ^ r * 2 ^ i.val := by
    calc ((Finset.univ.filter (fun ρ : Fin r → Bool =>
          1 < fiberCard (fP F h n) (x, (i, ρ)))).card * (2 * n)) * 2 ^ i.val
      ≤ ((Finset.univ.filter (fun ρ : Fin r → Bool =>
          1 < fiberCard (fP F h n) (x, (i, ρ)))).card * 2 ^ c) * 2 ^ i.val := by gcongr
    _ = ((Finset.univ.filter (fun ρ : Fin r → Bool =>
          1 < fiberCard (fP F h n) (x, (i, ρ)))).card) * 2 ^ L := by
          dsimp [L]; rw [pow_add]; ring
    _ ≤ (Sf F n x).card * 2 ^ r := hbi
    _ ≤ 2 ^ i.val * 2 ^ r := by gcongr
    _ = 2 ^ r * 2 ^ i.val := by ring
  exact Nat.le_of_mul_le_mul_right hmul_le (by positivity)

lemma card_S_lt_add_pow (F : FunEns) (n : ℕ) (hn : 1 ≤ n)
    (hD : ∀ x ∈ cube n, Dtilde (cube n) (F.f 0 n) (F.f 0 n x) ≤ n - 1) :
    (Finset.univ.filter (fun p : (Fin n → Bool) × Fin n =>
      p.2.val < Dtilde (cube n) (F.f 0 n) (F.f 0 n (List.ofFn p.1)))).card + 2 ^ n =
    (T64 F n).card := by
  let S_lt := Finset.univ.filter (fun p : (Fin n → Bool) × Fin n =>
    p.2.val < Dtilde (cube n) (F.f 0 n) (F.f 0 n (List.ofFn p.1)))
  let S_eq := Finset.univ.filter (fun p : (Fin n → Bool) × Fin n =>
    p.2.val = Dtilde (cube n) (F.f 0 n) (F.f 0 n (List.ofFn p.1)))
  let S_le := Finset.univ.filter (fun p : (Fin n → Bool) × Fin n =>
    p.2.val ≤ Dtilde (cube n) (F.f 0 n) (F.f 0 n (List.ofFn p.1)))
  have hpart : S_lt ∪ S_eq = S_le := by
    ext p
    simp only [S_lt, S_eq, S_le, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hdisj : Disjoint S_lt S_eq := by
    rw [Finset.disjoint_filter]
    intro p _ h1 h2; omega
  have hS_le_card : S_le.card = (T64 F n).card := by
    have himg : S_le.image (fun p : (Fin n → Bool) × Fin n => (List.ofFn p.1, p.2)) = T64 F n := by
      ext ⟨u, i⟩
      simp only [S_le, T64, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
        Finset.mem_univ, true_and, and_true, Prod.exists, Prod.mk.injEq]
      constructor
      · rintro ⟨x, i', hle, rfl, rfl⟩
        exact ⟨Finset.mem_image_of_mem _ (Finset.mem_univ x), hle⟩
      · rintro ⟨hu, hle⟩
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
        exact ⟨x, i, hle, rfl, rfl⟩
    rw [← himg, Finset.card_image_of_injective]
    intro p₁ p₂ h
    rcases Prod.ext_iff.mp h with ⟨h1, h2⟩
    exact Prod.ext (List.ofFn_injective h1) h2
  have hS_eq_card : S_eq.card = 2 ^ n := by
    have hD_lt : ∀ x : Fin n → Bool,
        Dtilde (cube n) (F.f 0 n) (F.f 0 n (List.ofFn x)) < n := by
      intro x
      have hx : List.ofFn x ∈ cube n := Finset.mem_image_of_mem _ (Finset.mem_univ x)
      have := hD (List.ofFn x) hx
      omega
    let g : (Fin n → Bool) → (Fin n → Bool) × Fin n :=
      fun x => (x, ⟨Dtilde (cube n) (F.f 0 n) (F.f 0 n (List.ofFn x)), hD_lt x⟩)
    have himg : (Finset.univ : Finset (Fin n → Bool)).image g = S_eq := by
      ext ⟨x, i⟩
      simp only [Finset.mem_image, Finset.mem_univ, true_and, S_eq, Finset.mem_filter,
        g, Prod.mk.injEq, Fin.ext_iff]
      constructor
      · rintro ⟨x', rfl, hval⟩
        exact hval.symm
      · intro hval
        exact ⟨x, rfl, hval.symm⟩
    have hinj : Function.Injective g := by
      intro x₁ x₂ h
      exact (Prod.ext_iff.mp h).1
    rw [← himg, Finset.card_image_of_injective _ hinj,
      Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [← hS_le_card, ← hS_eq_card, ← Finset.card_union_of_disjoint hdisj, hpart]

lemma collision_prob_le_p64_sub (F : FunEns) (n : ℕ) (hn : 1 ≤ n)
    (hD : ∀ x ∈ cube n, Dtilde (cube n) (F.f 0 n) (F.f 0 n x) ≤ n - 1)
    (h : HashFamily) (hh : h.IsUniversal)
    (hin : h.inLen n = n) (hout : h.outLen n = n + Nat.clog 2 (2 * n)) :
    ((Finset.univ.filter (fun w₀ : Ω₀ n (h.keyLen n) => 1 < fiberCard (fP F h n) w₀)).card : ℝ) /
      (Fintype.card (Ω₀ n (h.keyLen n)) : ℝ) ≤
    p64 F n - 1 / (2 * (n : ℝ)) := by
  let r := h.keyLen n
  let cr (p : (Fin n → Bool) × Fin n) : ℕ :=
    (Finset.univ.filter (fun ρ : Fin r → Bool => 1 < fiberCard (fP F h n) (p.1, (p.2, ρ)))).card
  have htotal : (Finset.univ.filter (fun w₀ : Ω₀ n r => 1 < fiberCard (fP F h n) w₀)).card =
      ∑ p : (Fin n → Bool) × Fin n, cr p := by
    rw [Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    dsimp [cr]
    rw [Finset.card_filter]
  let S_lt := Finset.univ.filter (fun p : (Fin n → Bool) × Fin n =>
    p.2.val < Dtilde (cube n) (F.f 0 n) (F.f 0 n (List.ofFn p.1)))
  let S_ge := Finset.univ.filter (fun p : (Fin n → Bool) × Fin n =>
    ¬ p.2.val < Dtilde (cube n) (F.f 0 n) (F.f 0 n (List.ofFn p.1)))
  have hpart : S_lt ∪ S_ge = Finset.univ := by
    ext p; simp only [S_lt, S_ge, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hdisj : Disjoint S_lt S_ge := by
    rw [Finset.disjoint_filter]
    intro p _ h1 h2; exact h2 h1
  have hcr_lt : ∀ p ∈ S_lt, cr p * (2 * n) ≤ 2 ^ r * (2 * n) := by
    intro p _
    have hle : cr p ≤ 2 ^ r := by
      have : cr p ≤ Fintype.card (Fin r → Bool) := Finset.card_le_univ _
      simpa using this
    exact Nat.mul_le_mul_right (2 * n) hle
  have hcr_ge : ∀ p ∈ S_ge, cr p * (2 * n) ≤ 2 ^ r := by
    intro p hp
    have hge : Dtilde (cube n) (F.f 0 n) (F.f 0 n (List.ofFn p.1)) ≤ p.2.val := by
      have := (Finset.mem_filter.mp hp).2; omega
    exact card_r_collision_When_ge F n h hh hin hout p.1 p.2 hge
  have hS_ge_le : S_ge.card ≤ 2 ^ n * n := by
    have : S_ge.card ≤ Fintype.card ((Fin n → Bool) × Fin n) := Finset.card_le_univ _
    simpa [Fintype.card_prod] using this
  have hnat_bound : (Finset.univ.filter (fun w₀ : Ω₀ n r => 1 < fiberCard (fP F h n) w₀)).card * (2 * n) ≤
      (S_lt.card * (2 * n) + 2 ^ n * n) * 2 ^ r := by
    rw [htotal, ← hpart, Finset.sum_union hdisj, add_mul, Finset.sum_mul, Finset.sum_mul]
    have h1 : ∑ p ∈ S_lt, cr p * (2 * n) ≤ S_lt.card * (2 ^ r * (2 * n)) := by
      calc ∑ p ∈ S_lt, cr p * (2 * n)
        ≤ ∑ _p ∈ S_lt, 2 ^ r * (2 * n) := Finset.sum_le_sum hcr_lt
      _ = S_lt.card * (2 ^ r * (2 * n)) := by rw [Finset.sum_const, smul_eq_mul]
    have h2 : ∑ p ∈ S_ge, cr p * (2 * n) ≤ (2 ^ n * n) * 2 ^ r := by
      calc ∑ p ∈ S_ge, cr p * (2 * n)
        ≤ ∑ _p ∈ S_ge, 2 ^ r := Finset.sum_le_sum hcr_ge
      _ = S_ge.card * 2 ^ r := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (2 ^ n * n) * 2 ^ r := Nat.mul_le_mul_right _ hS_ge_le
    calc ∑ x ∈ S_lt, cr x * (2 * n) + ∑ x ∈ S_ge, cr x * (2 * n)
      ≤ S_lt.card * (2 ^ r * (2 * n)) + (2 ^ n * n) * 2 ^ r := add_le_add h1 h2
    _ = (S_lt.card * (2 * n) + 2 ^ n * n) * 2 ^ r := by ring
  have hcard_Ω₀ : (Fintype.card (Ω₀ n r) : ℝ) = (2 : ℝ) ^ n * (n : ℝ) * (2 : ℝ) ^ r := by
    simp only [Ω₀, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    push_cast; ring
  have hT_eq : (S_lt.card : ℝ) + (2 : ℝ) ^ n = ((T64 F n).card : ℝ) := by
    exact_mod_cast card_S_lt_add_pow F n hn hD
  have hp64_eq : p64 F n = ((T64 F n).card : ℝ) / ((2 : ℝ) ^ n * (n : ℝ)) := by
    unfold p64
    rw [cube_card]
    push_cast; rfl
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h2n_pos : (0 : ℝ) < 2 * (n : ℝ) := by positivity
  have h2r_pos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have h2n_pow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hreal_bound : ((Finset.univ.filter (fun w₀ : Ω₀ n r => 1 < fiberCard (fP F h n) w₀)).card : ℝ) *
      (2 * (n : ℝ)) ≤ ((S_lt.card : ℝ) * (2 * (n : ℝ)) + (2 : ℝ) ^ n * (n : ℝ)) * (2 : ℝ) ^ r := by
    exact_mod_cast hnat_bound
  rw [hcard_Ω₀, hp64_eq, div_le_iff₀ (by positivity)]
  have hgoal_eq : ((((T64 F n).card : ℝ) / ((2 : ℝ) ^ n * (n : ℝ)) - 1 / (2 * (n : ℝ))) *
      ((2 : ℝ) ^ n * (n : ℝ) * (2 : ℝ) ^ r)) * (2 * (n : ℝ)) =
      ((S_lt.card : ℝ) * (2 * (n : ℝ)) + (2 : ℝ) ^ n * (n : ℝ)) * (2 : ℝ) ^ r := by
    rw [← hT_eq]
    field_simp
    ring
  nlinarith

end Lemma64Proof

open Lemma64Proof in
theorem solution (F : FunEns) (n k : ℕ) (hn : 1 ≤ n)
    (hk : 125 * n ^ 3 ≤ k)
    (hD : ∀ x ∈ cube n,
      Dtilde (cube n) (F.f 0 n) (F.f 0 n x) ≤ n - 1)
    (h hp : HashFamily) (hh : h.IsUniversal) (_hhp : hp.IsUniversal)
    (hin : h.inLen n = n)
    (hout : h.outLen n = n + Nat.clog 2 (2 * n))
    (_hpin : hp.inLen n = k)
    (_hpout : hp.outLen n = m64 F (fun _ => k) n) :
    entropyD64 F h hp n k + 10 * (n : ℝ) ^ 2 ≤
      entropyE64 F h hp n k (m64 F (fun _ => k) n) := by
  let m := m64 F (fun _ => k) n
  have hent := entropy_diff_ge_collision F h hp n k m hn
  have hcoll := collision_prob_le_p64_sub F n hn hD h hh hin hout
  have hk_coll := mul_le_mul_of_nonneg_left hcoll (Nat.cast_nonneg k)
  have hm_floor : (k : ℝ) * p64 F n - 2 * (k : ℝ) ^ ((2 : ℝ) / 3) - 1 ≤ (m : ℝ) := by
    have := Nat.lt_floor_add_one ((k : ℝ) * p64 F n - 2 * (k : ℝ) ^ ((2 : ℝ) / 3))
    change (k : ℝ) * p64 F n - 2 * (k : ℝ) ^ ((2 : ℝ) / 3) < (m : ℝ) + 1 at this
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hk_pos : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by nlinarith [ Nat.pow_pos (by omega : 0 < n) (n := 3) ]
    exact Nat.cast_pos.mpr this
  have h5n_cube : (5 * (n : ℝ)) ^ (3 : ℝ) ≤ (k : ℝ) := by
    have hnat : ((125 * n ^ 3 : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
    have heq : (5 * (n : ℝ)) ^ (3 : ℝ) = ((125 * n ^ 3 : ℕ) : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      push_cast; ring
    linarith
  have h5n_le : 5 * (n : ℝ) ≤ (k : ℝ) ^ ((1 : ℝ) / 3) := by
    have h1 := Real.rpow_le_rpow (by positivity) h5n_cube (by positivity : (0 : ℝ) ≤ 1 / 3)
    rw [← Real.rpow_mul (by positivity)] at h1
    norm_num at h1
    exact h1
  have hk_split : (k : ℝ) ^ ((1 : ℝ) / 3) * (k : ℝ) ^ ((2 : ℝ) / 3) = (k : ℝ) := by
    rw [← Real.rpow_add hk_pos]
    norm_num
  have h4nk : 4 * (n : ℝ) * (k : ℝ) ^ ((2 : ℝ) / 3) ≤ (4 / 5 : ℝ) * (k : ℝ) := by
    calc 4 * (n : ℝ) * (k : ℝ) ^ ((2 : ℝ) / 3)
      = (4 / 5 : ℝ) * ((5 * (n : ℝ)) * (k : ℝ) ^ ((2 : ℝ) / 3)) := by ring
    _ ≤ (4 / 5 : ℝ) * ((k : ℝ) ^ ((1 : ℝ) / 3) * (k : ℝ) ^ ((2 : ℝ) / 3)) := by gcongr
    _ = (4 / 5 : ℝ) * (k : ℝ) := by rw [hk_split]
  have hk125 : 125 * (n : ℝ) ^ 3 ≤ (k : ℝ) := by exact_mod_cast hk
  have hn2_ge_1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hn3_ge_n : (n : ℝ) ≤ (n : ℝ) ^ 3 := by nlinarith
  have h20n : 20 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ≤ (1 / 5 : ℝ) * (k : ℝ) := by
    calc 20 * (n : ℝ) ^ 3 + 2 * (n : ℝ)
      ≤ 20 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 3 := by gcongr
    _ ≤ 25 * (n : ℝ) ^ 3 := by nlinarith
    _ = (1 / 5 : ℝ) * (125 * (n : ℝ) ^ 3) := by ring
    _ ≤ (1 / 5 : ℝ) * (k : ℝ) := by gcongr
  have hdiv : 2 * (k : ℝ) ^ ((2 : ℝ) / 3) + 10 * (n : ℝ) ^ 2 + 1 ≤ (k : ℝ) / (2 * (n : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    calc (2 * (k : ℝ) ^ ((2 : ℝ) / 3) + 10 * (n : ℝ) ^ 2 + 1) * (2 * (n : ℝ))
      = 4 * (n : ℝ) * (k : ℝ) ^ ((2 : ℝ) / 3) + (20 * (n : ℝ) ^ 3 + 2 * (n : ℝ)) := by ring
    _ ≤ (4 / 5 : ℝ) * (k : ℝ) + (1 / 5 : ℝ) * (k : ℝ) := add_le_add h4nk h20n
    _ = (k : ℝ) := by ring
  have hkp : (k : ℝ) * (p64 F n - 1 / (2 * (n : ℝ))) =
      (k : ℝ) * p64 F n - (k : ℝ) / (2 * (n : ℝ)) := by ring
  linarith
