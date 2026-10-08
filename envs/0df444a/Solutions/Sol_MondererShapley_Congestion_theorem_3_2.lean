-- Prove2me | solution 1 for MondererShapley.Congestion.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:08:22.116997+00:00
-- url     : https://prove2.me/submissions/1e13b989-6435-4647-ac0e-43582d673411

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_MondererShapley_ClosedPath_IsPotentialGame
import Definitions.Def_MondererShapley_Congestion_IsIsomorphic
import Definitions.Def_MondererShapley_Congestion_congestionPayoff

open CongestionPoA.AsymSum MondererShapley.Congestion

universe u v
private theorem represent {ι : Type u} [Fintype ι] [DecidableEq ι]
    {Y : ι → Type v} [∀ i, Fintype (Y i)]
    (u : ι → (∀ i, Y i) → ℝ) (hu : MondererShapley.ClosedPath.IsPotentialGame u) :
    ∃ (E : Type (max u v)) (_ : Fintype E) (_ : DecidableEq E)
      (G : CongestionGame ι E),
      (∀ i, ∀ A ∈ G.strategies i, A.Nonempty) ∧ IsIsomorphic u (congestionPayoff G) := by
  classical
  let E := (∀ i, Y i) ⊕ ((ι × (∀ i, Y i)) ⊕ (Σ i, Y i))
  let S : ∀ i, Y i → Finset E := fun i a => Finset.univ.filter (fun e =>
    match e with
    | Sum.inl m => a = m i
    | Sum.inr (Sum.inl (k, m)) => if i = k then True else a ≠ m i
    | Sum.inr (Sum.inr ⟨k, z⟩) => (⟨i, a⟩ : Σ i, Y i) = ⟨k, z⟩)
  have hS (i) : Function.Injective (S i) := by
    intro a b hab
    have ha : Sum.inr (Sum.inr (⟨i, a⟩ : Σ i, Y i)) ∈ S i a := by simp [S]
    rw [hab] at ha
    exact (by simpa [S] using ha : b = a).symm
  have hne (i) (a : Y i) : (S i a).Nonempty := by
    exact ⟨Sum.inr (Sum.inr ⟨i, a⟩), by simp [S]⟩
  obtain ⟨P, hP⟩ := hu
  let L : E → ℕ → ℝ := fun e r => match e with
    | Sum.inl m => if r = Fintype.card ι then P m else 0
    | Sum.inr (Sum.inl (k, m)) => if r = 1 then u k m - P m else 0
    | Sum.inr (Sum.inr _) => 0
  by_cases hn : Nonempty (∀ i, Y i)
  · let base : ∀ i, Y i := Classical.choice hn
    let L' : E → ℕ → ℝ := fun e r => match e with
      | Sum.inl m => if r = Fintype.card ι then P m else 0
      | Sum.inr (Sum.inl (k, m)) => if r = 1 ∧ m k = base k then u k m - P m else 0
      | Sum.inr (Sum.inr _) => 0
    let G : CongestionGame ι E := ⟨fun i => Finset.univ.image (S i), L'⟩
    let g : ∀ i, Y i ≃ ↥(G.strategies i) := fun i =>
      Equiv.ofBijective (fun a => (⟨S i a, by simp [G]⟩ : ↥(G.strategies i))) (by
        constructor
        · intro a b h; exact hS i (congrArg Subtype.val h)
        · rintro ⟨s, hs⟩
          obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hs
          exact ⟨a, Subtype.ext ha⟩)
    refine ⟨E, inferInstance, inferInstance, G, ?_, g, ?_⟩
    · intro i s hs
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs
      exact hne i a
    · intro i y
      have hload (e : E) : load (fun k => S k (y k)) e =
          (Finset.univ.filter (fun k => e ∈ S k (y k))).card := rfl
      have hall (m : ∀ i, Y i) : load (fun k => S k (y k)) (Sum.inl m) = Fintype.card ι ↔ m = y := by
        simp only [load, S, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← Finset.card_univ, Finset.card_filter_eq_iff]
        simp only [Finset.mem_univ, forall_const, Fintype.card]
        constructor
        · intro h; funext k; exact (h k).symm
        · rintro rfl; simp
      have hone (k : ι) (m : ∀ i, Y i) :
          load (fun j => S j (y j)) (Sum.inr (Sum.inl (k,m))) = 1 ↔ ∀ j, j ≠ k → y j = m j := by
        have hmem : k ∈ Finset.univ.filter (fun j => Sum.inr (Sum.inl (k,m)) ∈ S j (y j)) := by simp [S]
        rw [load, Finset.card_eq_one]
        constructor
        · rintro ⟨a, ha⟩
          have hak : a = k := (by simpa [ha] using hmem : k = a).symm
          subst a
          intro j hj
          by_contra h
          have : j ∈ ({k} : Finset ι) := ha ▸ (by simp [S, hj, h])
          exact hj (Finset.mem_singleton.mp this)
        · intro h
          refine ⟨k, ?_⟩
          ext j
          by_cases hj : j = k
          · subst j; simp [S]
          · simp [S, hj, h j hj]
      change u i y = ∑ e ∈ S i (y i), L' e (load (fun k => S k (y k)) e)
      rw [Finset.sum_filter]
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
      have hp : (∑ m : ∀ i, Y i, if Sum.inl m ∈ S i (y i) then
          L' (Sum.inl m) (load (fun k => S k (y k)) (Sum.inl m)) else 0) = P y := by
        rw [Finset.sum_eq_single y]
        · simp only [L', hall, ite_true]
          simp [S]
        · intro m hm hmy
          simp [L', hall, hmy]
        · simp
      have hq : (∑ k : ι, ∑ m : ∀ i, Y i, if Sum.inr (Sum.inl (k,m)) ∈ S i (y i) then
          L' (Sum.inr (Sum.inl (k,m))) (load (fun j => S j (y j)) (Sum.inr (Sum.inl (k,m)))) else 0) =
          u i y - P y := by
        rw [Finset.sum_eq_single i]
        · let z := Function.update y i (base i)
          have hz : ∀ j, j ≠ i → y j = z j := by intro j hj; simp [z, hj]
          have hz' : z i = base i := by simp [z]
          have he : (∑ m : ∀ j, Y j, if Sum.inr (Sum.inl (i,m)) ∈ S i (y i) then
              L' (Sum.inr (Sum.inl (i,m))) (load (fun j => S j (y j)) (Sum.inr (Sum.inl (i,m)))) else 0) = u i z - P z := by
            rw [Finset.sum_eq_single z]
            · have hh : load (fun j => S j (y j)) (Sum.inr (Sum.inl (i,z))) = 1 := (hone i z).mpr hz
              simp only [L', hh, hz', and_self, ite_true]
              simp [S]
            · intro m hm hmz
              have hnot : ¬ ((∀ j, j ≠ i → y j = m j) ∧ m i = base i) := by
                rintro ⟨ha,hb⟩
                apply hmz
                funext j
                by_cases hj : j = i
                · subst j; exact hb.trans hz'.symm
                · exact (ha j hj).symm.trans (hz j hj)
              simp only [L', hone, hnot, ite_false]
              simp
            · simp
          rw [he]
          have hh := hP i y (base i) (y i)
          simp only [Function.update_eq_self] at hh
          change u i z - u i y = P z - P y at hh
          linarith
        · intro k hk hki
          apply Finset.sum_eq_zero
          intro m hm
          by_cases h : ∀ j, j ≠ k → y j = m j
          · simp [S, L', Ne.symm hki, h i (Ne.symm hki)]
          · simp [L', hone, h]
        · simp
      have hm : (∑ e : Σ i, Y i, if Sum.inr (Sum.inr e) ∈ S i (y i) then
          L' (Sum.inr (Sum.inr e)) (load (fun k => S k (y k)) (Sum.inr (Sum.inr e))) else 0) = 0 := by
        simp [L']
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq hm ⊢
      rw [hp, hq, hm]
      ring
  · let G : CongestionGame ι E := ⟨fun i => Finset.univ.image (S i), fun _ _ => 0⟩
    let g : ∀ i, Y i ≃ ↥(G.strategies i) := fun i =>
      Equiv.ofBijective (fun a => (⟨S i a, by simp [G]⟩ : ↥(G.strategies i))) (by
        constructor
        · intro a b h; exact hS i (congrArg Subtype.val h)
        · rintro ⟨s, hs⟩
          obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hs
          exact ⟨a, Subtype.ext ha⟩)
    refine ⟨E, inferInstance, inferInstance, G, ?_, g, ?_⟩
    · intro i s hs
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs
      exact hne i a
    · intro i y; exact False.elim (hn ⟨y⟩)

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*} [∀ i, Fintype (Y i)]
    (u : ι → (∀ i, Y i) → ℝ) (hu : MondererShapley.ClosedPath.IsPotentialGame u) :
    ∃ (m : ℕ) (G : CongestionGame ι (Fin m)),
      (∀ i, ∀ A ∈ G.strategies i, A.Nonempty) ∧ IsIsomorphic u (congestionPayoff G) := by
  classical
  obtain ⟨E, hE, dE, G, hne, g, hg⟩ := represent u hu
  letI := hE
  letI := dE
  let e := Fintype.equivFin E
  let f := fun s : Finset E => s.map e.toEmbedding
  have hf : Function.Injective f := Finset.map_injective e.toEmbedding
  let H : CongestionGame ι (Fin (Fintype.card E)) :=
    ⟨fun i => (G.strategies i).image f, fun j r => G.latency (e.symm j) r⟩
  let h : ∀ i, ↥(G.strategies i) ≃ ↥(H.strategies i) := fun i =>
    Equiv.ofBijective (fun s => (⟨f s.val, Finset.mem_image.mpr ⟨s.val,s.property,rfl⟩⟩ : ↥(H.strategies i))) (by
      constructor
      · intro s t hh; exact Subtype.ext (hf (congrArg Subtype.val hh))
      · rintro ⟨t, ht⟩
        obtain ⟨s, hs, he⟩ := Finset.mem_image.mp ht
        exact ⟨⟨s,hs⟩, Subtype.ext he⟩)
  refine ⟨Fintype.card E, H, ?_, (fun i => (g i).trans (h i)), ?_⟩
  · intro i s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.map_nonempty.mpr (hne i t ht)
  · intro i y
    rw [hg]
    change (∑ j ∈ (g i (y i)).val, G.latency j (load (fun k => (g k (y k)).val) j)) =
      ∑ j ∈ f (g i (y i)).val, G.latency (e.symm j) (load (fun k => f (g k (y k)).val) j)
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
    congr 1
    unfold load
    congr 1
    ext k
    simp [f]

#print axioms solution
