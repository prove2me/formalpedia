-- Prove2me | solution 1 for MetricMSO.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:59:01.017749+00:00
-- url     : https://prove2.me/submissions/905a11a4-5cff-4e8b-9471-52838ebe34a2

import Mathlib
import Definitions.Def_MetricMSO_cbl
import Definitions.Def_MetricMSO_Admissible
import Definitions.Def_MetricMSO_signedSum
import Theorems.Thm_MetricMSO_lemma_3_3

open MetricMSO

namespace Aux34

open Classical

lemma cycle_length_le_card {V : Type} [Fintype V] {G : SimpleGraph V} {v : V}
    {c : G.Walk v v} (hc : c.IsCycle) : c.length ≤ Fintype.card V := by
  have hnodup : c.support.tail.Nodup := hc.support_nodup
  have hlen : c.support.tail.length ≤ Fintype.card V := hnodup.length_le_card
  have hsup : c.support.tail.length = c.length := by
    rw [List.length_tail, SimpleGraph.Walk.length_support]
    omega
  omega

lemma shortCycleSpan_cbl {V : Type} [Fintype V] (G : SimpleGraph V) :
    shortCycleSpan G (cbl G) = cycleSpace G := by
  unfold cbl
  apply Nat.sInf_mem (s := {L | shortCycleSpan G L = cycleSpace G})
  refine ⟨Fintype.card V, le_antisymm ?_ ?_⟩
  · apply Submodule.span_mono
    rintro f ⟨v, c, hc, _, rfl⟩
    exact ⟨v, c, hc, rfl⟩
  · apply Submodule.span_mono
    rintro f ⟨v, c, hc, rfl⟩
    exact ⟨v, c, hc, cycle_length_le_card hc, rfl⟩

lemma exists_short_cycleBasis {V : Type} [Fintype V] (G : SimpleGraph V) :
    ∃ (k : ℕ) (B : Fin k → CycleOf G),
      IsCycleBasis B ∧ ∀ i, (B i).walk.length ≤ cbl G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Set (Sym2 V → ZMod 2) :=
    {f | ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length ≤ cbl G ∧ f = cycleVec c}
  have hspan_S : Submodule.span (ZMod 2) S = cycleSpace G := shortCycleSpan_cbl G
  obtain ⟨I, hI_sub, hS_le, hI_lin⟩ := exists_linearIndependent (ZMod 2) S
  have hspan_I : Submodule.span (ZMod 2) I = cycleSpace G := hS_le.trans hspan_S
  let eI : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let B : Fin (Fintype.card I) → CycleOf G := fun i =>
    let hmem : (eI i : Sym2 V → ZMod 2) ∈ S := hI_sub (eI i).2
    let vc := Classical.choose hmem
    let c := Classical.choose (Classical.choose_spec hmem)
    let hc := (Classical.choose_spec (Classical.choose_spec hmem)).1
    ⟨vc, c, hc⟩
  have hB_vec : ∀ i, cycleVec (B i).walk = (eI i : Sym2 V → ZMod 2) := by
    intro i
    let hmem : (eI i : Sym2 V → ZMod 2) ∈ S := hI_sub (eI i).2
    exact (Classical.choose_spec (Classical.choose_spec hmem)).2.2.symm
  have hB_len : ∀ i, (B i).walk.length ≤ cbl G := by
    intro i
    let hmem : (eI i : Sym2 V → ZMod 2) ∈ S := hI_sub (eI i).2
    exact (Classical.choose_spec (Classical.choose_spec hmem)).2.1
  refine ⟨Fintype.card I, B, ⟨?_, ?_⟩, hB_len⟩
  · have heq : (fun i => cycleVec (B i).walk) = (((↑) : I → Sym2 V → ZMod 2) ∘ eI) := by
      ext i e; exact congr_fun (hB_vec i) e
    rw [heq]
    exact hI_lin.comp eI eI.injective
  · have hrange : Set.range (fun i => cycleVec (B i).walk) = I := by
      ext f
      simp only [Set.mem_range, hB_vec]
      constructor
      · rintro ⟨i, rfl⟩; exact (eI i).2
      · intro hf; exact ⟨eI.symm ⟨f, hf⟩, by simp⟩
    rw [hrange, hspan_I]

lemma zmod_ne_of_ge_three {M : ℕ} (hM : 3 ≤ M) :
    (1 : ZMod M) ≠ -1 ∧ (1 : ZMod M) ≠ 0 ∧ (-1 : ZMod M) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h2 : ((2 : ℕ) : ZMod M) = 0 := by
      calc ((2 : ℕ) : ZMod M) = (1 : ZMod M) - (-1 : ZMod M) := by norm_num
        _ = 0 := by rw [← h, sub_self]
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by decide) h2
    omega
  · intro h
    have h1 : ((1 : ℕ) : ZMod M) = 0 := by simpa using h
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := Nat.le_of_dvd (by decide) h1
    omega
  · intro h
    have h1 : ((1 : ℕ) : ZMod M) = 0 := by
      calc ((1 : ℕ) : ZMod M) = -(-1 : ZMod M) := by ring
        _ = 0 := by rw [h, neg_zero]
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := Nat.le_of_dvd (by decide) h1
    omega

noncomputable def incVal {M : ℕ} (x : ZMod M) : ℤ :=
  if x = 1 then 1 else if x = -1 then -1 else 0

lemma incVal_spec {M : ℕ} (hM : 3 ≤ M) {x : ZMod M} (hx : x = -1 ∨ x = 0 ∨ x = 1) :
    incVal x ∈ ({-1, 0, 1} : Set ℤ) ∧
      (incVal x : ZMod M) = x ∧
      |incVal x| ≤ 1 ∧
      incVal (-x) = -incVal x := by
  obtain ⟨h1m1, h10, hm10⟩ := zmod_ne_of_ge_three hM
  rcases hx with rfl | rfl | rfl
  · have hneg1 : -(-1 : ZMod M) = 1 := by ring
    simp [incVal, h1m1.symm, hneg1]
  · simp [incVal, h10.symm, hm10.symm]
  · simp [incVal, h1m1.symm]

lemma signedSum_mod_and_abs {V : Type} {G : SimpleGraph V} {M : ℕ}
    {O : V → V → Prop} (hO : IsRefOrientation G O)
    (c : V → ZMod M) (δ : Sym2 V → ℤ)
    (hδ_mod : ∀ u v, O u v → (δ s(u, v) : ZMod M) = c v - c u)
    (hδ_abs : ∀ e ∈ G.edgeSet, |δ e| ≤ 1) :
    ∀ {x y : V} (W : G.Walk x y),
      (signedSum O δ W : ZMod M) = c y - c x ∧ |signedSum O δ W| ≤ W.length
  | _, _, .nil => by simp [signedSum]
  | x, y, @SimpleGraph.Walk.cons _ _ _ w _ hadj p => by
    obtain ⟨ih_mod, ih_abs⟩ := signedSum_mod_and_abs hO c δ hδ_mod hδ_abs p
    have he : s(x, w) ∈ G.edgeSet := hadj
    have habs_step : |if O x w then δ s(x, w) else -δ s(x, w)| ≤ 1 := by
      by_cases hxw : O x w
      · rw [if_pos hxw]; exact hδ_abs s(x, w) he
      · rw [if_neg hxw, abs_neg]; exact hδ_abs s(x, w) he
    refine ⟨?_, ?_⟩
    · rw [signedSum, Int.cast_add, ih_mod]
      by_cases hxw : O x w
      · rw [if_pos hxw, hδ_mod x w hxw]; ring
      · have hwx : O w x := by
          have := hO.2 w x hadj.symm
          tauto
        rw [if_neg hxw, Int.cast_neg, Sym2.eq_swap, hδ_mod w x hwx]; ring
    · rw [signedSum, SimpleGraph.Walk.length_cons]
      push_cast
      calc |(if O x w then δ s(x, w) else -δ s(x, w)) + signedSum O δ p|
          ≤ |if O x w then δ s(x, w) else -δ s(x, w)| + |signedSum O δ p| := abs_add_le _ _
        _ ≤ 1 + (p.length : ℤ) := add_le_add habs_step ih_abs
        _ = (p.length : ℤ) + 1 := add_comm _ _

lemma walk_mod_eq {V : Type} {G : SimpleGraph V} {M : ℕ}
    (lam : V → ℤ) (c : V → ZMod M)
    (hdiff : ∀ u v, G.Adj u v → ((lam v - lam u : ℤ) : ZMod M) = c v - c u) :
    ∀ {x y : V} (_ : G.Walk x y), (lam y : ZMod M) - (lam x : ZMod M) = c y - c x
  | _, _, .nil => by simp
  | x, y, @SimpleGraph.Walk.cons _ _ _ w _ hadj p => by
    have ih := walk_mod_eq lam c hdiff p
    have hstep := hdiff x w hadj
    push_cast at hstep
    linear_combination ih + hstep

end Aux34

theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) (M : ℕ) (hM : 3 ≤ M)
    (hcbl : cbl G < M) (c : V → ZMod M) (hc : Admissible G c) :
    ∃ lam : V → ℤ, (∀ v, ((lam v : ℤ) : ZMod M) = c v) ∧
      ∀ u v, G.Adj u v → lam v - lam u ∈ ({-1, 0, 1} : Set ℤ) ∧
        ((lam v - lam u : ℤ) : ZMod M) = c v - c u := by
  classical
  have : NeZero M := ⟨by omega⟩
  let enc : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let O : V → V → Prop := fun u v => G.Adj u v ∧ enc u < enc v
  have hO : IsRefOrientation G O := by
    refine ⟨fun _ _ h => h.1, fun u v hadj => ?_⟩
    have hne : enc u ≠ enc v := enc.injective.ne (G.ne_of_adj hadj)
    simp only [O, hadj, hadj.symm, true_and]
    omega
  let δ : Sym2 V → ℤ := fun e =>
    if h : ∃ u v, e = s(u, v) ∧ O u v then
      let u := Classical.choose h
      let v := Classical.choose (Classical.choose_spec h)
      Aux34.incVal (c v - c u)
    else 0
  have hδ_at : ∀ u v, O u v → δ s(u, v) = Aux34.incVal (c v - c u) := by
    intro u v houv
    have hex : ∃ u' v', s(u, v) = s(u', v') ∧ O u' v' := ⟨u, v, rfl, houv⟩
    dsimp only [δ]
    rw [dif_pos hex]
    let u' := Classical.choose hex
    let v' := Classical.choose (Classical.choose_spec hex)
    have hspec : s(u, v) = s(u', v') ∧ O u' v' :=
      Classical.choose_spec (Classical.choose_spec hex)
    obtain ⟨heq, hou'v'⟩ := hspec
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · change Aux34.incVal (c v' - c u') = Aux34.incVal (c v - c u)
      rw [← hu, ← hv]
    · exfalso
      rw [← hu, ← hv] at hou'v'
      exact ((hO.2 u v (hO.1 u v houv)).mp houv) hou'v'
  have hδ_mod : ∀ u v, O u v → (δ s(u, v) : ZMod M) = c v - c u := by
    intro u v houv
    rw [hδ_at u v houv]
    exact (Aux34.incVal_spec hM (hc u v houv.1)).2.1
  have hδ_abs : ∀ e ∈ G.edgeSet, |δ e| ≤ 1 := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have hadj : G.Adj u v := he
      by_cases houv : O u v
      · rw [hδ_at u v houv]
        exact (Aux34.incVal_spec hM (hc u v hadj)).2.2.1
      · have hovu : O v u := by
          have := hO.2 u v hadj
          tauto
        rw [Sym2.eq_swap, hδ_at v u hovu]
        exact (Aux34.incVal_spec hM (hc v u hadj.symm)).2.2.1
  obtain ⟨k, B, hB, hB_len⟩ := Aux34.exists_short_cycleBasis G
  have h0 : ∀ i, signedSum O δ (B i).walk = 0 := by
    intro i
    obtain ⟨hmod, habs⟩ := Aux34.signedSum_mod_and_abs hO c δ hδ_mod hδ_abs (B i).walk
    rw [sub_self] at hmod
    have hdvd : (M : ℤ) ∣ signedSum O δ (B i).walk :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp hmod
    have hlt : |signedSum O δ (B i).walk| < M := by
      have hlen := hB_len i
      omega
    rw [abs_lt] at hlt
    obtain ⟨q, hq⟩ := hdvd
    rw [hq] at hlt ⊢
    rcases lt_trichotomy q 0 with hq_neg | rfl | hq_pos
    · exfalso; nlinarith
    · simp
    · exfalso; nlinarith
  obtain ⟨⟨lam₀, hlam₀⟩, _⟩ := MetricMSO.lemma_3_3 G O hO δ B hB h0
  have hlam₀_adj : ∀ u v, G.Adj u v → lam₀ v - lam₀ u = Aux34.incVal (c v - c u) := by
    intro u v hadj
    by_cases houv : O u v
    · rw [hlam₀ u v houv, hδ_at u v houv]
    · have hovu : O v u := by
        have := hO.2 u v hadj
        tauto
      have h1 := hlam₀ v u hovu
      rw [hδ_at v u hovu] at h1
      have hneg : Aux34.incVal (c u - c v) = -Aux34.incVal (c v - c u) := by
        have hsub : c u - c v = -(c v - c u) := by ring
        rw [hsub]
        exact (Aux34.incVal_spec hM (hc u v hadj)).2.2.2
      omega
  let comp : V → Finset V := fun v => Finset.univ.filter (G.Reachable v)
  have hcomp_ne : ∀ v, (comp v).Nonempty := fun v =>
    ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, SimpleGraph.Reachable.refl v⟩⟩
  let pick : (S : Finset V) → S.Nonempty → V := fun S h => Classical.choose h
  let rep : V → V := fun v => pick (comp v) (hcomp_ne v)
  have hrep_eq : ∀ u v, G.Reachable u v → rep u = rep v := by
    intro u v hruv
    have hceq : comp u = comp v := by
      ext w
      simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun huw => hruv.symm.trans huw, fun hvw => hruv.trans hvw⟩
    dsimp only [rep]
    congr 1
  have hrep_reach : ∀ v, G.Reachable v (rep v) := by
    intro v
    have hmem : rep v ∈ comp v := Classical.choose_spec (hcomp_ne v)
    exact (Finset.mem_filter.mp hmem).2
  let lam : V → ℤ := fun v => lam₀ v + ((ZMod.val (c (rep v)) : ℤ) - lam₀ (rep v))
  have hlam_diff : ∀ u v, G.Adj u v → lam v - lam u = Aux34.incVal (c v - c u) := by
    intro u v hadj
    have hr : rep u = rep v := hrep_eq u v hadj.reachable
    dsimp only [lam]
    rw [hr]
    linarith [hlam₀_adj u v hadj]
  have hdiff_props : ∀ u v, G.Adj u v →
      lam v - lam u ∈ ({-1, 0, 1} : Set ℤ) ∧ ((lam v - lam u : ℤ) : ZMod M) = c v - c u := by
    intro u v hadj
    rw [hlam_diff u v hadj]
    have hspec := Aux34.incVal_spec hM (hc u v hadj)
    exact ⟨hspec.1, hspec.2.1⟩
  refine ⟨lam, ?_, hdiff_props⟩
  intro v
  obtain ⟨w_rv⟩ := (hrep_reach v).symm
  have hwalk := Aux34.walk_mod_eq lam c (fun x y hxy => (hdiff_props x y hxy).2) w_rv
  have hrep_idem : rep (rep v) = rep v := hrep_eq (rep v) v (hrep_reach v).symm
  have hlam_rep : (lam (rep v) : ZMod M) = c (rep v) := by
    dsimp only [lam]
    rw [hrep_idem]
    have : lam₀ (rep v) + ((ZMod.val (c (rep v)) : ℤ) - lam₀ (rep v)) =
        (ZMod.val (c (rep v)) : ℤ) := by ring
    rw [this, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [hlam_rep] at hwalk
  linear_combination hwalk
