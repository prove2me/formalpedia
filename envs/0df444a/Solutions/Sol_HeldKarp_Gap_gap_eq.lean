-- Prove2me | solution 1 for HeldKarp.Gap.gap_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:08:40.480843+00:00
-- url     : https://prove2.me/submissions/2b5b8810-0bfe-4266-b03b-e94ffcdd03a2

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Ascent_oneTreeBound
import Definitions.Def_HeldKarp_Gap_GapFunction

open Classical
open HeldKarp.Ascent
open HeldKarp.Gap

theorem g69g_lift_eq {n : ℕ} (π : Fin n → ℝ) (e : Sym2 (Fin n)) (he : ¬ e.IsDiag) :
    Sym2.lift ⟨fun i j => π i + π j, fun i j => add_comm (π i) (π j)⟩ e =
      ∑ v, if v ∈ e then π v else 0 := by
  induction e using Sym2.ind with
  | h a b =>
    rw [Sym2.mk_isDiag_iff] at he
    rw [Sym2.lift_mk]
    have : ∀ v : Fin n, (if v ∈ s(a, b) then π v else 0) =
        (if a = v then π v else 0) + (if b = v then π v else 0) := by
      intro v
      by_cases ha : v = a
      · subst ha; simp [Ne.symm he, he]
      · by_cases hb : v = b
        · subst hb; simp [ha, Ne.symm ha]
        · simp [Sym2.mem_iff, ha, hb, Ne.symm ha, Ne.symm hb]
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem g69g_weight_shift {n : ℕ} (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ)
    (G : SimpleGraph (Fin n)) :
    weight (shift c π) G = weight c G + ∑ v, π v * (G.degree v : ℝ) := by
  unfold weight shift
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_congr rfl (fun e he => g69g_lift_eq π e
    (G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he)))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  rw [← SimpleGraph.incidenceFinset_eq_filter, SimpleGraph.card_incidenceFinset_eq_degree]

theorem g69g_sInf_shift {ι : Type*} [Finite ι] (P : ι → Prop) (g : ι → ℝ) (a : ℝ)
    (hne : ∃ i, P i) :
    sInf {t | ∃ i, P i ∧ t = g i + a} = sInf {t | ∃ i, P i ∧ t = g i} + a := by
  have hb1 : BddBelow {t | ∃ i, P i ∧ t = g i} :=
    ((Set.finite_range g).subset (by rintro t ⟨i, -, rfl⟩; exact Set.mem_range_self i)).bddBelow
  have hb2 : BddBelow {t | ∃ i, P i ∧ t = g i + a} :=
    ((Set.finite_range (fun i => g i + a)).subset
      (by rintro t ⟨i, -, rfl⟩; exact Set.mem_range_self i)).bddBelow
  obtain ⟨i0, hi0⟩ := hne
  apply le_antisymm
  · have : sInf {t | ∃ i, P i ∧ t = g i + a} - a ≤ sInf {t | ∃ i, P i ∧ t = g i} := by
      apply le_csInf (⟨g i0, i0, hi0, rfl⟩ : Set.Nonempty {t | ∃ i, P i ∧ t = g i})
      rintro t ⟨i, hi, rfl⟩
      have := csInf_le hb2 ⟨i, hi, rfl⟩
      linarith
    linarith
  · apply le_csInf (⟨g i0 + a, i0, hi0, rfl⟩ : Set.Nonempty {t | ∃ i, P i ∧ t = g i + a})
    rintro t ⟨i, hi, rfl⟩
    have := csInf_le hb1 ⟨i, hi, rfl⟩
    linarith

theorem g69g_tour_exists {n : ℕ} (hn : 3 ≤ n) : ∃ H : SimpleGraph (Fin n), IsTour H := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  refine ⟨SimpleGraph.cycleGraph (k + 3), SimpleGraph.cycleGraph_connected, fun v => ?_⟩
  convert SimpleGraph.cycleGraph_degree_three_le (v := v)

theorem g69g_oneTree_exists {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    ∃ G : SimpleGraph (Fin n), IsOneTree G := by
  set W : Set (Fin n) := {v : Fin n | v ≠ 0}
  have h1 : (⟨1, by omega⟩ : Fin n) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this
  have h2 : (⟨2, by omega⟩ : Fin n) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp at this
  have : Nonempty W := ⟨⟨⟨1, by omega⟩, h1⟩⟩
  obtain ⟨T, -, hT⟩ := (SimpleGraph.connected_top (V := W)).exists_isTree_le
  let G : SimpleGraph (Fin n) := SimpleGraph.fromRel (fun u v : Fin n =>
    (∃ (hu : u ≠ 0) (hv : v ≠ 0), T.Adj ⟨u, hu⟩ ⟨v, hv⟩) ∨
      (u = 0 ∧ (v = ⟨1, by omega⟩ ∨ v = ⟨2, by omega⟩)))
  refine ⟨G, ?_, ?_⟩
  · have : G.induce W = T := by
      ext x y
      simp only [SimpleGraph.comap_adj, SimpleGraph.induce, G, SimpleGraph.fromRel_adj]
      obtain ⟨x, hx⟩ := x
      obtain ⟨y, hy⟩ := y
      have hx' : x ≠ 0 := hx
      have hy' : y ≠ 0 := hy
      simp only [Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨-, (⟨_, _, h⟩ | ⟨h, -⟩) | (⟨_, _, h⟩ | ⟨h, -⟩)⟩
        · exact h
        · exact absurd h hx'
        · exact h.symm
        · exact absurd h hy'
      · intro h
        refine ⟨fun e => T.ne_of_adj h (Subtype.ext e), Or.inl (Or.inl ⟨hx', hy', h⟩)⟩
    rw [this]; exact hT
  · rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have : G.neighborFinset 0 = {⟨1, by omega⟩, ⟨2, by omega⟩} := by
      ext v
      rw [SimpleGraph.mem_neighborFinset]
      simp only [G, SimpleGraph.fromRel_adj, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, (⟨h, _, _⟩ | ⟨-, h⟩) | (⟨_, h, _⟩ | ⟨-, h⟩)⟩
        · exact absurd rfl h
        · exact h
        · exact absurd rfl h
        · rcases h with h | h
          · exact absurd h.symm h1
          · exact absurd h.symm h2
      · intro h
        refine ⟨?_, Or.inl (Or.inr ⟨by trivial, h⟩)⟩
        rcases h with h | h <;> (subst h; first | exact h1.symm | exact h2.symm)
    rw [← Finset.card_pair h12]; congr 1; convert this

theorem solution {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ) :
    gap c π = tourMin c + 2 * ∑ i, π i -
        sInf {t : ℝ | ∃ G : SimpleGraph (Fin n), IsOneTree G ∧
          t = weight c G + ∑ i, π i * (G.degree i : ℝ)} ∧
      gap c π = tourMin c - oneTreeBound c π := by
  have hT : tourMin (shift c π) = tourMin c + 2 * ∑ i, π i := by
    unfold tourMin
    rw [← g69g_sInf_shift (fun H => IsTour H) (weight c) _ (g69g_tour_exists hn)]
    congr 1; ext t
    constructor
    · rintro ⟨H, hH, rfl⟩
      refine ⟨H, hH, ?_⟩
      rw [g69g_weight_shift, Finset.mul_sum]
      congr 1; apply Finset.sum_congr rfl; intro v _; rw [hH.2 v]; push_cast; ring
    · rintro ⟨H, hH, rfl⟩
      refine ⟨H, hH, ?_⟩
      rw [g69g_weight_shift, Finset.mul_sum]
      congr 1; apply Finset.sum_congr rfl; intro v _; rw [hH.2 v]; push_cast; ring
  have hO : oneTreeMin (shift c π) = sInf {t : ℝ | ∃ G : SimpleGraph (Fin n), IsOneTree G ∧
          t = weight c G + ∑ i, π i * (G.degree i : ℝ)} := by
    unfold oneTreeMin
    simp_rw [g69g_weight_shift]
  have hB : oneTreeBound c π = sInf {t : ℝ | ∃ G : SimpleGraph (Fin n), IsOneTree G ∧
          t = weight c G + ∑ i, π i * (G.degree i : ℝ)} + (-(2 * ∑ i, π i)) := by
    unfold oneTreeBound
    rw [← g69g_sInf_shift (fun G => IsOneTree G)
      (fun G => weight c G + ∑ i, π i * (G.degree i : ℝ)) _ (g69g_oneTree_exists hn)]
    congr 1; ext t
    have e : ∀ G : SimpleGraph (Fin n), lagrWeight c π G =
        weight c G + ∑ i, π i * (G.degree i : ℝ) + -(2 * ∑ i, π i) := by
      intro G; unfold lagrWeight degExcess
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, add_assoc, ← Finset.sum_add_distrib]
      congr 1; apply Finset.sum_congr rfl; intro i _; ring
    simp_rw [e]
  unfold gap
  refine ⟨by rw [hT, hO], by rw [hT, hO, hB]; ring⟩
