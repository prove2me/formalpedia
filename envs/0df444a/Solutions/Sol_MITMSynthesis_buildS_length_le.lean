-- Prove2me | solution 1 for MITMSynthesis.buildS_length_le
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-11T12:22:42.238688+00:00
-- url     : https://prove2.me/submissions/b613d939-9949-4109-a2fc-138ac190685c

import Mathlib.Data.Set.Card
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_MITMSynthesis_depthOneSet
import Definitions.Def_MITMSynthesis_S
import Definitions.Def_MITMSynthesis_mitmFactor

open MITMSynthesis

private theorem extend_one_value {α M : Type} [Mul M] (W : M) (c : List α) (vs : List (α × M)) :
    (extendOneC W c vs).val = vs.map (fun av => (av.2 * W, av.1 :: c)) := by
  induction vs with
  | nil => rfl
  | cons av vs ih =>
    change (av.2 * W, av.1 :: c) :: (extendOneC W c vs).val = _
    rw [ih, List.map_cons]

private theorem extend_value {α M : Type} [Mul M] (vs : List (α × M))
    (prev : List (M × List α)) :
    (extendC vs prev).val = prev.flatMap (fun wc => vs.map (fun av => (av.2 * wc.1, av.1 :: wc.2))) := by
  induction prev with
  | nil => rfl
  | cons wc prev ih =>
    simp only [extendC, List.flatMap_cons]
    change (extendOneC wc.1 wc.2 vs).val ++ (extendC vs prev).val = _
    rw [extend_one_value, ih]

private theorem extend_length {α M : Type} [Mul M] (vs : List (α × M))
    (prev : List (M × List α)) :
    (extendC vs prev).val.length = prev.length * vs.length := by
  rw [extend_value]
  induction prev with
  | nil => simp
  | cons wc prev ih => simp only [List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons, Nat.succ_mul]; omega

private theorem build_length {α M : Type} [Monoid M] (vs : List (α × M)) (i : ℕ) :
    (buildS vs i).val.length = vs.length ^ i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change (extendC vs (buildS vs i).val).val.length = _
    rw [extend_length, ih, pow_succ]

private theorem enumerate_product {α M : Type} [Monoid M] (vs : List (α × M))
    (L : List M) (hL : ∀ v ∈ L, ∃ a, (a,v) ∈ vs) :
    ∃ c, (L.prod,c) ∈ (buildS vs L.length).val := by
  induction L with
  | nil => exact ⟨[], by change (1,[]) ∈ [(1,[])]; simp⟩
  | cons v L ih =>
    obtain ⟨a, ha⟩ := hL v (by simp)
    obtain ⟨c,hc⟩ := ih (fun w hw => hL w (List.mem_cons_of_mem v hw))
    refine ⟨a :: c, ?_⟩
    change (v * L.prod, a :: c) ∈ (extendC vs (buildS vs L.length).val).val
    rw [extend_value]
    apply List.mem_flatMap.mpr
    refine ⟨(L.prod,c),hc,?_⟩
    exact List.mem_map.mpr ⟨(a,v),ha,rfl⟩

theorem solution {n : ℕ} {G : Set Gate}
    (vs : List (List (Placement n) × Matrix (Q n) (Q n) ℂ)) (hvs : IsLayerEnumeration G vs)
    (i : ℕ) :
    (buildS vs i).val.length ≤ (depthOneSet n G).ncard ^ i ∧
      (S (depthOneSet n G) i).ncard ≤ (depthOneSet n G).ncard ^ i := by
  classical
  have hKeys : depthOneSet n G = ((vs.map Prod.snd).toFinset : Set (Matrix (Q n) (Q n) ℂ)) := by
    ext M
    constructor
    · intro hM
      obtain ⟨p,hp,hpM⟩ := hvs.2.2 M hM
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p,hp,hpM⟩)
    · intro hM
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hM)
      exact ⟨p.1,(hvs.1 p hp).1,(hvs.1 p hp).2⟩
  have hCard : (depthOneSet n G).ncard = vs.length := by
    rw [hKeys, Set.ncard_coe_finset, List.toFinset_card_of_nodup hvs.2.1, List.length_map]
  have hCover : S (depthOneSet n G) i ⊆
      (((buildS vs i).val.map Prod.fst).toFinset : Set (Matrix (Q n) (Q n) ℂ)) := by
    rintro M ⟨L,hLen,hL,rfl⟩
    have hEnum : ∀ v ∈ L, ∃ a, (a,v) ∈ vs := by
      intro v hv
      obtain ⟨p,hp,hpv⟩ := hvs.2.2 v (hL v hv)
      rcases p with ⟨a,w⟩
      dsimp at hpv
      subst w
      exact ⟨a,hp⟩
    obtain ⟨c,hc⟩ := enumerate_product vs L hEnum
    rw [hLen] at hc
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(L.prod,c),hc,rfl⟩)
  constructor
  · rw [build_length,hCard]
  · calc
      _ ≤ (((buildS vs i).val.map Prod.fst).toFinset : Set (Matrix (Q n) (Q n) ℂ)).ncard :=
        Set.ncard_le_ncard hCover (Finset.finite_toSet _)
      _ = ((buildS vs i).val.map Prod.fst).toFinset.card := Set.ncard_coe_finset _
      _ ≤ ((buildS vs i).val.map Prod.fst).length := List.toFinset_card_le _
      _ = (depthOneSet n G).ncard ^ i := by rw [List.length_map,build_length,hCard]

#print axioms solution
