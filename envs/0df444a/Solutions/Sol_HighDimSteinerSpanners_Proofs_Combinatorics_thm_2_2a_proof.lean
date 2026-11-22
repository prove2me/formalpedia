-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.Combinatorics.thm_2_2a_proof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:37.212734+00:00
-- url     : https://prove2.me/submissions/2941dd01-f2f8-40bb-835f-53f1b5c123e7

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Glue
public import Definitions.Def_LeanPool_SteinerSpanners_Combinatorics
section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.Combinatorics
private lemma pinFiber_card_le {α β : Type*} [DecidableEq α]
    {a : α} {b : β} {L : Finset α} {K : ℕ} (h : L.card < K) :
    ((insert a L) ×ˢ ({b} : Finset β)).card ≤ K := by
  rw [Finset.card_product, Finset.card_singleton, mul_one]
  exact (Finset.card_insert_le _ _).trans (by omega)
end HighDimSteinerSpanners.Proofs.Combinatorics
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Combinatorics
namespace HighDimSteinerSpanners.Proofs.Combinatorics
theorem _root_.solution :
    ∀ (C₁ rStar N q K : ℕ), 2 ≤ C₁ → 1 ≤ rStar → 2 ≤ N → 2 ≤ q → 1 ≤ K →
      ∀ (X : Finset (Fin N → Fin q)) (G_hat : SimpleGraph ↥X)
        (L : ↥X → ↥X → Finset ↥X),
        (∀ a b : ↥X, G_hat.Adj a b →
          0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar) →
        (∀ x y : ↥X, hammingDist x.val y.val = rStar →
          ∃ q_walk : G_hat.Walk x y,
            q_walk.IsPath ∧ ∀ z ∈ q_walk.support, hammingDist x.val z.val ≤ C₁ * rStar) →
        ListSizeCond C₁ rStar K X L →
        OverlapCond C₁ rStar K X →
        ListHitCond C₁ rStar X L →
        (exactDistPairs X rStar).card ≤ 2 * K ^ 2 * Nat.card G_hat.edgeSet := by
  classical
  intro C₁ rStar N q K _ hrStar _ _ _ X G_hat L hG_adj hG_path hListSize hOverlap hListHit
  let : Fintype G_hat.Dart := Fintype.ofFinite _
  let : Fintype G_hat.edgeSet := Fintype.ofFinite _
  have h_dart_card : (Finset.univ : Finset G_hat.Dart).card = 2 * Nat.card G_hat.edgeSet := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    have h := G_hat.dart_card_eq_twice_card_edges
    simpa only [SimpleGraph.edgeFinset, Set.toFinset_card,
      ← Nat.card_eq_fintype_card] using h
  let dartPinFiber : G_hat.Dart → Finset (↥X × ↥X) :=
    fun d => (insert d.toProd.1 (L d.toProd.1 d.toProd.2)) ×ˢ ({d.toProd.2} : Finset ↥X)
  let P_pin : Finset (↥X × ↥X) :=
    ((Finset.univ : Finset G_hat.Dart).biUnion dartPinFiber).filter
      (fun p => 0 < hammingDist p.1.val p.2.val ∧ hammingDist p.1.val p.2.val ≤ C₁ * rStar)
  have h_dart_fiber_le : ∀ d : G_hat.Dart, (dartPinFiber d).card ≤ K := by
    intro d
    obtain ⟨hab_pos, hab_dist⟩ := hG_adj d.toProd.1 d.toProd.2 d.adj
    exact pinFiber_card_le (hListSize _ _ hab_pos hab_dist)
  have h_Ppin_card : P_pin.card ≤ 2 * K * Nat.card G_hat.edgeSet := by
    have h1 : P_pin.card ≤ ((Finset.univ : Finset G_hat.Dart).biUnion dartPinFiber).card :=
      Finset.card_filter_le _ _
    have h2 : ((Finset.univ : Finset G_hat.Dart).biUnion dartPinFiber).card ≤
        ∑ d ∈ (Finset.univ : Finset G_hat.Dart), (dartPinFiber d).card :=
      Finset.card_biUnion_le
    have h3 : ∑ d ∈ (Finset.univ : Finset G_hat.Dart), (dartPinFiber d).card ≤
        (Finset.univ : Finset G_hat.Dart).card * K := by
      simpa [smul_eq_mul] using
        Finset.sum_le_card_nsmul (Finset.univ : Finset G_hat.Dart)
          (fun d => (dartPinFiber d).card) K (fun d _ => h_dart_fiber_le d)
    calc
      P_pin.card ≤ (Finset.univ : Finset G_hat.Dart).card * K :=
        le_trans h1 (le_trans h2 h3)
      _ = (2 * Nat.card G_hat.edgeSet) * K := by rw [h_dart_card]
      _ = 2 * K * Nat.card G_hat.edgeSet := by ring
  let CherrySet : ↥X → ↥X → Finset ↥X :=
    fun x w₀ => Finset.univ.filter (fun y : ↥X =>
      y ≠ x ∧ y ≠ w₀ ∧
      hammingDist x.val y.val = rStar ∧
      (rStar : ℝ) / 4 < ((disagreeSet x.val w₀.val ∩ disagreeSet x.val y.val).card : ℝ))
  let CherryFiber : ↥X × ↥X → Finset (↥X × ↥X) :=
    fun p => ({p.1} : Finset ↥X) ×ˢ insert p.2 (CherrySet p.1 p.2)
  have h_cherry_fiber_le : ∀ p ∈ P_pin, (CherryFiber p).card ≤ K := by
    intro p hp
    simp only [P_pin, Finset.mem_filter] at hp
    have h_ch_lt : (CherrySet p.1 p.2).card < K :=
      hOverlap p.1 p.2 hp.2.1 hp.2.2
    have h := pinFiber_card_le (a := p.2) (b := p.1) h_ch_lt
    simpa only [CherryFiber, Finset.card_product, Finset.card_singleton, one_mul, mul_one]
      using h
  have h_cover_card :
      (P_pin.biUnion CherryFiber).card ≤ 2 * K ^ 2 * Nat.card G_hat.edgeSet := by
    have h1 : (P_pin.biUnion CherryFiber).card ≤ ∑ p ∈ P_pin, (CherryFiber p).card :=
      Finset.card_biUnion_le
    have h2 : ∑ p ∈ P_pin, (CherryFiber p).card ≤ P_pin.card * K := by
      simpa [smul_eq_mul] using
        Finset.sum_le_card_nsmul P_pin (fun p => (CherryFiber p).card) K h_cherry_fiber_le
    calc
      (P_pin.biUnion CherryFiber).card ≤ P_pin.card * K := le_trans h1 h2
      _ ≤ (2 * K * Nat.card G_hat.edgeSet) * K :=
        Nat.mul_le_mul_right K h_Ppin_card
      _ = 2 * K ^ 2 * Nat.card G_hat.edgeSet := by ring
  let E_sub : Finset (↥X × ↥X) :=
    Finset.univ.filter (fun xy : ↥X × ↥X => hammingDist xy.1.val xy.2.val = rStar)
  have h_sub : E_sub ⊆ P_pin.biUnion CherryFiber := by
    rintro ⟨x, y⟩ hxy
    simp only [E_sub, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
    have hxy_ne : x ≠ y := by
      intro h_eq
      subst h_eq
      rw [hammingDist_self] at hxy
      omega
    obtain ⟨q_walk, hq_path, hq_ball⟩ := hG_path x y hxy
    let m : ℕ := q_walk.length
    have hm_pos : 1 ≤ m := by
      by_contra hm0
      have hm_eq : q_walk.length = 0 := by omega
      exact hxy_ne (SimpleGraph.Walk.eq_of_length_eq_zero hm_eq)
    let u : ℕ → ↥X := fun k => q_walk.getVert k
    have hu0 : u 0 = x := q_walk.getVert_zero
    have hum : u m = y := q_walk.getVert_length
    have hu_inj : Set.InjOn u {k : ℕ | k ≤ m} := hq_path.getVert_injOn
    have hu_eq : ∀ a b : ℕ, a ≤ m → b ≤ m → u a = u b → a = b :=
      fun a b ha hb hab => hu_inj ha hb hab
    have hu_ball : ∀ k : ℕ, hammingDist x.val (u k).val ≤ C₁ * rStar :=
      fun k => hq_ball (u k) (q_walk.getVert_mem_support k)
    have hu_adj : ∀ k : ℕ, k < m → G_hat.Adj (u k) (u (k + 1)) :=
      fun k hk => q_walk.adj_getVert_succ hk
    let I : Finset ℕ :=
      (Finset.Icc 1 m).filter (fun s => x ∈ insert (u (s - 1)) (L (u (s - 1)) (u s)))
    have h1_mem : 1 ∈ I := by
      simp only [I, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨le_rfl, hm_pos⟩, ?_⟩
      change x ∈ insert (u 0) (L (u 0) (u 1))
      rw [hu0]
      exact Finset.mem_insert_self _ _
    have hI_ne : I.Nonempty := ⟨1, h1_mem⟩
    let s₀ : ℕ := I.max' hI_ne
    let w₀ : ↥X := u s₀
    have hs₀_mem : s₀ ∈ I := Finset.max'_mem I hI_ne
    simp only [I, Finset.mem_filter, Finset.mem_Icc] at hs₀_mem
    obtain ⟨⟨hs₀_ge, hs₀_le⟩, hs₀_pin⟩ := hs₀_mem
    have hadj₀ : G_hat.Adj (u (s₀ - 1)) w₀ := by
      have h_lt : s₀ - 1 < m := by omega
      have h_succ : s₀ - 1 + 1 = s₀ := by omega
      have h_a := hu_adj (s₀ - 1) h_lt
      rwa [h_succ] at h_a
    have hx_ne_w₀ : x ≠ w₀ := by
      intro h_eq
      have h0s : u 0 = u s₀ := by rw [hu0]; exact h_eq
      have : 0 = s₀ := hu_eq 0 s₀ (by omega) hs₀_le h0s
      omega
    have hxw₀_pos : 0 < hammingDist x.val w₀.val :=
      hammingDist_pos.mpr (fun h_eq => hx_ne_w₀ (Subtype.ext h_eq))
    have hp_mem : (x, w₀) ∈ P_pin := by
      simp only [P_pin, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
      refine ⟨⟨⟨(u (s₀ - 1), w₀), hadj₀⟩, ?_⟩, hxw₀_pos, hu_ball s₀⟩
      exact Finset.mem_product.mpr ⟨hs₀_pin, Finset.mem_singleton_self w₀⟩
    simp only [Finset.mem_biUnion]
    refine ⟨(x, w₀), hp_mem, ?_⟩
    simp only [CherryFiber, Finset.mem_product, Finset.mem_singleton, true_and]
    rcases eq_or_lt_of_le hs₀_le with hs₀_eq | hs₀_lt
    · have hw₀_eq_y : w₀ = y := by
        dsimp [w₀]
        rw [hs₀_eq, hum]
      rw [hw₀_eq_y]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      simp only [CherrySet, Finset.mem_filter, Finset.mem_univ, true_and]
      have hy_ne_w₀ : y ≠ w₀ := by
        intro h_eq
        have hms : u m = u s₀ := by rw [hum]; exact h_eq
        have : m = s₀ := hu_eq m s₀ le_rfl hs₀_le hms
        omega
      refine ⟨hxy_ne.symm, hy_ne_w₀, hxy, ?_⟩
      by_contra h_not_lt
      have h_inter_le :
          ((disagreeSet x.val w₀.val ∩ disagreeSet x.val y.val).card : ℝ) ≤ (rStar : ℝ) / 4 :=
        not_lt.mp h_not_lt
      let ℓ : ℕ := m - s₀
      have hℓ : 1 ≤ ℓ := by omega
      let w : Fin (ℓ + 1) → ↥X := fun t => u (s₀ + t.1)
      have hw_ball : ∀ t : Fin (ℓ + 1), w t ≠ x ∧ hammingDist x.val (w t).val ≤ C₁ * rStar := by
        intro t
        refine ⟨?_, hu_ball (s₀ + t.1)⟩
        intro h_eq
        have h_u : u (s₀ + t.1) = u 0 := by rw [hu0]; exact h_eq
        have h_le : s₀ + t.1 ≤ m := by have := t.2; omega
        have : s₀ + t.1 = 0 := hu_eq (s₀ + t.1) 0 h_le (by omega) h_u
        omega
      have hw_step : ∀ s : Fin ℓ,
          0 < hammingDist (w s.castSucc).val (w s.succ).val ∧
          hammingDist (w s.castSucc).val (w s.succ).val ≤ C₁ * rStar := by
        intro s
        have hs_lt : s₀ + s.1 < m := by have := s.2; omega
        have h_adj_s : G_hat.Adj (w s.castSucc) (w s.succ) := by
          dsimp [w]
          rw [← Nat.add_assoc]
          exact hu_adj (s₀ + s.1) hs_lt
        exact hG_adj _ _ h_adj_s
      have hw_last_eq : w (Fin.last ℓ) = y := by
        dsimp [w]
        have h_add : s₀ + ℓ = m := by omega
        rw [h_add, hum]
      have hw_zero_eq : w 0 = w₀ := rfl
      have hw_last_dist : hammingDist x.val (w (Fin.last ℓ)).val = rStar := by
        rw [hw_last_eq]
        exact hxy
      have hw_inter :
          ((disagreeSet x.val (w 0).val ∩ disagreeSet x.val (w (Fin.last ℓ)).val).card : ℝ) ≤
            (rStar : ℝ) / 4 := by
        rw [hw_zero_eq, hw_last_eq]
        exact h_inter_le
      obtain ⟨s, hs_cand⟩ := hListHit x ℓ hℓ w hw_ball hw_step hw_last_dist hw_inter
      let s' : ℕ := s₀ + s.1 + 1
      have hs'_mem : s' ∈ I := by
        simp only [I, Finset.mem_filter, Finset.mem_Icc]
        have hs'_bounds : 1 ≤ s' ∧ s' ≤ m := by have := s.2; omega
        refine ⟨hs'_bounds, ?_⟩
        apply Finset.mem_insert_of_mem
        have h1 : u (s' - 1) = w s.castSucc := rfl
        have h2 : u s' = w s.succ := by
          dsimp [w, s']
          rw [Nat.add_assoc]
        rw [h1, h2]
        exact hs_cand
      have hs'_le : s' ≤ s₀ := Finset.le_max' I s' hs'_mem
      omega
  have h_img : exactDistPairs X rStar ⊆ E_sub.image (fun xy => (xy.1.val, xy.2.val)) := by
    rintro ⟨xv, yv⟩ hxy
    simp only [exactDistPairs, Finset.mem_filter, Finset.mem_product] at hxy
    obtain ⟨⟨hx, hy⟩, hdist⟩ := hxy
    exact Finset.mem_image.mpr
      ⟨(⟨xv, hx⟩, ⟨yv, hy⟩), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩, rfl⟩
  calc
    (exactDistPairs X rStar).card
      ≤ (E_sub.image (fun xy => (xy.1.val, xy.2.val))).card := Finset.card_le_card h_img
    _ ≤ E_sub.card := Finset.card_image_le
    _ ≤ (P_pin.biUnion CherryFiber).card := Finset.card_le_card h_sub
    _ ≤ 2 * K ^ 2 * Nat.card G_hat.edgeSet := h_cover_card
end HighDimSteinerSpanners.Proofs.Combinatorics
