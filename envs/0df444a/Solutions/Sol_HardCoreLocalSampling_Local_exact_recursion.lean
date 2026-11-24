-- Prove2me | solution 1 for HardCoreLocalSampling.Local.exact_recursion
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:58:58.01221+00:00
-- url     : https://prove2.me/submissions/3e38404a-08ad-4804-b8e4-5f9d8ea6e43b

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Deletion

namespace HCLSExactRecursionAux
open Finset HardCoreLocalSampling.Local

section
variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- The hard-core weight of `I` in the induced graph `G - D`. -/
noncomputable def wt (G : SimpleGraph V) (lam : ℝ) (D I : Finset V) : ℝ :=
  if ExpanderBIS.HardCore.IsIndep G I ∧ ∀ x ∈ I, x ∉ D then lam ^ I.card else 0

/-- The partition function `Z(G - D)`. -/
noncomputable def Z (G : SimpleGraph V) (lam : ℝ) (D : Finset V) : ℝ :=
  ∑ I : Finset V, wt G lam D I

theorem compatible_deletion (D I : Finset V) :
    Compatible (deletionPinning D) I ↔ ∀ x ∈ I, x ∉ D := by
  constructor
  · intro h x hx hxD
    exact (h x).2 (by simp [deletionPinning, hxD]) hx
  · intro h x
    refine ⟨fun hx => ?_, fun hx hxI => h x hxI ?_⟩
    · simp only [deletionPinning] at hx
      split_ifs at hx
    · simp only [deletionPinning] at hx
      by_contra hxD
      rw [if_neg hxD] at hx
      cases hx

theorem weight_eq (G : SimpleGraph V) (lam : ℝ) (D I : Finset V) :
    conditionalWeight G lam (deletionPinning D) I = wt G lam D I := by
  unfold conditionalWeight wt
  by_cases h : ExpanderBIS.HardCore.IsIndep G I ∧ ∀ x ∈ I, x ∉ D
  · rw [if_pos h, if_pos ⟨h.1, (compatible_deletion D I).2 h.2⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, (compatible_deletion D I).1 h'.2⟩)]

theorem odds_eq (G : SimpleGraph V) (lam : ℝ) (D : Finset V) (v : V) :
    deletionOdds G lam D v =
      (∑ I : Finset V, if v ∈ I then wt G lam D I else 0) /
        (∑ I : Finset V, if v ∉ I then wt G lam D I else 0) := by
  unfold deletionOdds
  simp only [weight_eq]
  try (congr 1 <;> exact Finset.sum_congr rfl fun I _ => by split_ifs <;> rfl)

theorem wt_nonneg (G : SimpleGraph V) (lam : ℝ) (hlam : 0 < lam) (D I : Finset V) :
    0 ≤ wt G lam D I := by
  unfold wt; split_ifs
  · positivity
  · exact le_rfl

theorem Z_pos (G : SimpleGraph V) (lam : ℝ) (hlam : 0 < lam) (D : Finset V) :
    0 < Z G lam D := by
  have h0 : wt G lam D ∅ = 1 := by
    unfold wt
    rw [if_pos ⟨fun u hu => by simp at hu, fun x hx => by simp at hx⟩]
    simp
  unfold Z
  calc (0 : ℝ) < wt G lam D ∅ := by rw [h0]; exact one_pos
    _ ≤ ∑ I : Finset V, wt G lam D I :=
      Finset.single_le_sum (fun I _ => wt_nonneg G lam hlam D I) (Finset.mem_univ _)

theorem split_sum (G : SimpleGraph V) (lam : ℝ) (D : Finset V) (u : V) :
    (∑ I : Finset V, if u ∈ I then wt G lam D I else 0) +
      (∑ I : Finset V, if u ∉ I then wt G lam D I else 0) = Z G lam D := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases h : u ∈ I
  · rw [if_pos h, if_neg (not_not.2 h), add_zero]
  · rw [if_neg h, if_pos h, zero_add]

theorem den_eq (G : SimpleGraph V) (lam : ℝ) (D : Finset V) (u : V) :
    (∑ I : Finset V, if u ∉ I then wt G lam D I else 0) = Z G lam (insert u D) := by
  unfold Z
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases hu : u ∈ I
  · rw [if_neg (not_not.2 hu)]
    unfold wt
    rw [if_neg]
    rintro ⟨-, h⟩
    exact h u hu (Finset.mem_insert_self u D)
  · rw [if_pos hu]
    have hc : (ExpanderBIS.HardCore.IsIndep G I ∧ ∀ x ∈ I, x ∉ D) ↔
        (ExpanderBIS.HardCore.IsIndep G I ∧ ∀ x ∈ I, x ∉ insert u D) := by
      constructor
      · rintro ⟨a, b⟩
        refine ⟨a, fun x hx hx' => ?_⟩
        rcases Finset.mem_insert.1 hx' with rfl | hx'
        · exact hu hx
        · exact b x hx hx'
      · rintro ⟨a, b⟩
        exact ⟨a, fun x hx hx' => b x hx (Finset.mem_insert_of_mem hx')⟩
    unfold wt
    by_cases h : ExpanderBIS.HardCore.IsIndep G I ∧ ∀ x ∈ I, x ∉ D
    · rw [if_pos h, if_pos (hc.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]

theorem key (G : SimpleGraph V) (lam : ℝ) (D N J : Finset V) (v : V) (hv : v ∉ D)
    (hN : ∀ u, u ∉ D → (u ∈ N ↔ G.Adj v u)) (hvJ : v ∉ J) :
    wt G lam D (insert v J) = lam * wt G lam (D ∪ insert v N) J := by
  have hc : (ExpanderBIS.HardCore.IsIndep G (insert v J) ∧ ∀ x ∈ insert v J, x ∉ D) ↔
      (ExpanderBIS.HardCore.IsIndep G J ∧ ∀ x ∈ J, x ∉ D ∪ insert v N) := by
    constructor
    · rintro ⟨hind, hD⟩
      refine ⟨fun a ha b hb => hind a (Finset.mem_insert_of_mem ha) b
        (Finset.mem_insert_of_mem hb), fun x hx hx' => ?_⟩
      rcases Finset.mem_union.1 hx' with hxD | hx'
      · exact hD x (Finset.mem_insert_of_mem hx) hxD
      · rcases Finset.mem_insert.1 hx' with rfl | hxN
        · exact hvJ hx
        · have hxD : x ∉ D := hD x (Finset.mem_insert_of_mem hx)
          exact hind v (Finset.mem_insert_self v J) x (Finset.mem_insert_of_mem hx)
            ((hN x hxD).1 hxN)
    · rintro ⟨hind, hD'⟩
      refine ⟨?_, fun x hx => ?_⟩
      · intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with ha | ha <;> rcases Finset.mem_insert.1 hb with hb | hb
        · rw [ha, hb] at hab; exact G.irrefl hab
        · rw [ha] at hab
          have hbD : b ∉ D := fun h => hD' b hb (Finset.mem_union_left _ h)
          exact hD' b hb (Finset.mem_union_right _ (Finset.mem_insert_of_mem ((hN b hbD).2 hab)))
        · rw [hb] at hab
          have haD : a ∉ D := fun h => hD' a ha (Finset.mem_union_left _ h)
          exact hD' a ha (Finset.mem_union_right _
            (Finset.mem_insert_of_mem ((hN a haD).2 hab.symm)))
        · exact hind a ha b hb hab
      · rcases Finset.mem_insert.1 hx with hx | hx
        · subst hx; exact hv
        · exact fun h => hD' x hx (Finset.mem_union_left _ h)
  unfold wt
  by_cases h : ExpanderBIS.HardCore.IsIndep G (insert v J) ∧ ∀ x ∈ insert v J, x ∉ D
  · rw [if_pos h, if_pos (hc.1 h), Finset.card_insert_of_notMem hvJ, pow_succ]; ring
  · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]; ring

theorem num_eq (G : SimpleGraph V) (lam : ℝ) (D N : Finset V) (v : V) (hv : v ∉ D)
    (hN : ∀ u, u ∉ D → (u ∈ N ↔ G.Adj v u)) :
    (∑ I : Finset V, if v ∈ I then wt G lam D I else 0) = lam * Z G lam (D ∪ insert v N) := by
  rw [Z, Finset.mul_sum]
  have hmem : ∀ I : Finset V, (if v ∈ I then wt G lam D I else 0) ≠ 0 → v ∈ I := by
    intro I h; by_contra hI; exact h (if_neg hI)
  apply Finset.sum_bij_ne_zero (fun I _ _ => I.erase v)
  · intros; exact Finset.mem_univ _
  · intro I₁ _ h₁ I₂ _ h₂ he
    rw [← Finset.insert_erase (hmem I₁ h₁), ← Finset.insert_erase (hmem I₂ h₂), he]
  · intro J _ hJ
    have hvJ : v ∉ J := by
      intro h; apply hJ
      unfold wt
      rw [if_neg, mul_zero]
      rintro ⟨-, h'⟩
      exact h' v h (Finset.mem_union_right _ (Finset.mem_insert_self v N))
    refine ⟨insert v J, Finset.mem_univ _, ?_, Finset.erase_insert hvJ⟩
    rw [if_pos (Finset.mem_insert_self v J), key G lam D N J v hv hN hvJ]
    exact hJ
  · intro I _ hI
    have hv1 := hmem I hI
    rw [if_pos hv1, ← key G lam D N (I.erase v) v hv hN (Finset.notMem_erase v I),
      Finset.insert_erase hv1]

theorem telescope (f : ℕ → ℝ) (hf : ∀ k, f k ≠ 0) (n : ℕ) :
    ∏ k ∈ Finset.range n, f (k + 1) / f k = f n / f 0 := by
  induction n with
  | zero => simp [hf 0]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    field_simp [hf n]

end

end HCLSExactRecursionAux

open HardCoreLocalSampling.Local HCLSExactRecursionAux

theorem solution {V : Type*} [Fintype V] [LinearOrder V] {Delta : ℕ}
    (G : SimpleGraph V) (lam : ℚ)
    (hDelta : 3 ≤ Delta) (hlam : 0 < lam) (hunique : lam < criticalFugacity Delta)
    (hdegree : MaxDegreeLE G Delta) (D : Finset V) (v : V) (hv : v ∉ D) :
    deletionOdds G (lam : ℝ) D v =
      (lam : ℝ) * ∏ i : Fin (orderedNeighbors G D v).length,
        (1 + deletionOdds G (lam : ℝ) (childDeleted G D v i)
          ((orderedNeighbors G D v)[i.val]))⁻¹ ∧
    ∀ i : Fin (orderedNeighbors G D v).length,
      residualDegree G (childDeleted G D v i) ((orderedNeighbors G D v)[i.val]) ≤
        Delta - 1 := by
  classical
  have hlamR : (0 : ℝ) < lam := by exact_mod_cast hlam
  have hmemL : ∀ u, u ∈ orderedNeighbors G D v ↔ G.Adj v u ∧ u ∉ D := by
    intro u
    unfold orderedNeighbors
    simp [Finset.mem_sort, SimpleGraph.mem_neighborFinset]
  set L := orderedNeighbors G D v with hL
  let Dn : ℕ → Finset V := fun k => D ∪ insert v ((L.take k).toFinset)
  have hchild : ∀ i : Fin L.length, childDeleted G D v i = Dn i.val := by
    intro i
    simp only [childDeleted, Dn, hL]
    try (ext x; simp)
  have hZ : ∀ k, Z G (lam : ℝ) (Dn k) ≠ 0 := fun k => (Z_pos G _ hlamR _).ne'
  have hstep : ∀ i : Fin L.length,
      (1 + deletionOdds G (lam : ℝ) (childDeleted G D v i) L[i.val])⁻¹ =
        Z G (lam : ℝ) (Dn (i.val + 1)) / Z G (lam : ℝ) (Dn i.val) := by
    intro i
    rw [hchild, odds_eq]
    have hins : insert L[i.val] (Dn i.val) = Dn (i.val + 1) := by
      have ht : L.take (i.val + 1) = L.take i.val ++ [L[i.val]] :=
        List.take_succ_eq_append_getElem i.isLt
      ext x
      simp only [Dn]
      rw [ht]
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_append,
        List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]
      tauto
    have hden := den_eq G (lam : ℝ) (Dn i.val) L[i.val]
    rw [hins] at hden
    have hsplit := split_sum G (lam : ℝ) (Dn i.val) L[i.val]
    rw [hden] at hsplit ⊢
    have h1 : 1 + (∑ I : Finset V, if L[i.val] ∈ I then wt G (lam : ℝ) (Dn i.val) I else 0) /
        Z G (lam : ℝ) (Dn (i.val + 1)) =
        Z G (lam : ℝ) (Dn i.val) / Z G (lam : ℝ) (Dn (i.val + 1)) := by
      rw [← hsplit]
      field_simp [hZ (i.val + 1)]
      ring
    rw [h1, inv_div]
  refine ⟨?_, fun i => ?_⟩
  · have hN : ∀ u, u ∉ D → (u ∈ L.toFinset ↔ G.Adj v u) := by
      intro u hu
      rw [List.mem_toFinset, hL, hmemL]
      exact ⟨fun h => h.1, fun h => ⟨h, hu⟩⟩
    rw [odds_eq, num_eq G _ D L.toFinset v hv hN, den_eq]
    rw [Finset.prod_congr rfl (fun i _ => hstep i)]
    rw [Fin.prod_univ_eq_prod_range (fun k => Z G (lam : ℝ) (Dn (k + 1)) / Z G (lam : ℝ) (Dn k))
      L.length]
    rw [telescope _ hZ]
    have e1 : Dn L.length = D ∪ insert v L.toFinset := by
      simp only [Dn, List.take_length]
    have e0 : Dn 0 = insert v D := by
      ext x; simp [Dn] <;> tauto
    rw [e1, e0, mul_div_assoc]
  · have hu : G.Adj v L[i.val] ∧ L[i.val] ∉ D := (hmemL _).1 (List.getElem_mem _)
    have hd := hdegree L[i.val]
    unfold residualDegree at hd ⊢
    simp only [Finset.sdiff_empty] at hd
    have hvN : v ∈ G.neighborFinset L[i.val] :=
      (SimpleGraph.mem_neighborFinset _ _ _).2 hu.1.symm
    have hvC : v ∈ childDeleted G D v i := by
      rw [hchild]; simp [Dn]
    have key : (G.neighborFinset L[i.val] \ childDeleted G D v i).card ≤ Delta - 1 := by
      have h1 : G.neighborFinset L[i.val] \ childDeleted G D v i ⊆
          (G.neighborFinset L[i.val]).erase v := by
        intro x hx
        rw [Finset.mem_sdiff] at hx
        rw [Finset.mem_erase]
        exact ⟨fun h => hx.2 (h ▸ hvC), hx.1⟩
      have h2 := Finset.card_le_card h1
      rw [Finset.card_erase_of_mem hvN] at h2
      omega
    convert key
