-- Prove2me | solution 1 for OAI.BufferedIsing.pairTable_contractedPinned
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:40:57.857599+00:00
-- url     : https://prove2.me/submissions/efdcf84d-b6c0-4739-9b03-d40e925a285e

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/PinnedMarginal.lean:L71-L102
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.pairTable_contractedPinned. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Theorems.Thm_OAI_BufferedIsing_constrainedSum_delete_variables

-- ---- from OAI.Probability.Ising.PinnedMarginal ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma respects_terminals_iff {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (σ : KeptVertex F → Bool) :
    Respects (comparisonSetoid G I J F ∅) σ ↔
      (∀ x y, x.val ∈ I → y.val ∈ I → σ x = σ y) ∧
        (∀ x y, x.val ∈ J → y.val ∈ J → σ x = σ y) := by
  constructor
  · intro H
    exact ⟨fun x y hx hy => H x y (Relation.EqvGen.rel _ _ (Or.inl ⟨hx, hy⟩)),
      fun x y hx hy => H x y (Relation.EqvGen.rel _ _ (Or.inr (Or.inl ⟨hx, hy⟩)))⟩
  · rintro ⟨hI, hJ⟩ x y hxy
    induction hxy with
    | rel x y h =>
      rcases h with h | h | ⟨e, he, _⟩
      · exact hI x y h.1 h.2
      · exact hJ x y h.1 h.2
      · exact (Finset.notMem_empty e he).elim
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

lemma contracted_prescription_iff {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J)
    (τ : Spins n) (σ : KeptVertex F → Bool) (s t : Bool) :
    (σ i = s ∧ σ j = t ∧ Respects (comparisonSetoid G I J F ∅) σ) ↔
      AgreesOn I (pinExtension F τ σ) (fun _ => s) ∧
        AgreesOn J (pinExtension F τ σ) (fun _ => t) := by
  constructor
  · rintro ⟨his, hjt, hresp⟩
    obtain ⟨hI, hJ⟩ := (respects_terminals_iff G I J F σ).mp hresp
    constructor
    · intro v hv
      have hvF : v ∉ F := fun hvF => Finset.disjoint_left.mp hIF hv hvF
      exact (pinExtension_apply F τ σ ⟨v, hvF⟩).trans ((hI _ i hv hi).trans his)
    · intro v hv
      have hvF : v ∉ F := fun hvF => Finset.disjoint_left.mp hJF hv hvF
      exact (pinExtension_apply F τ σ ⟨v, hvF⟩).trans ((hJ _ j hv hj).trans hjt)
  · rintro ⟨hI, hJ⟩
    have hI' : ∀ v : KeptVertex F, v.val ∈ I → σ v = s := by
      intro v hv
      simpa only [pinExtension_apply] using hI v.val hv
    have hJ' : ∀ v : KeptVertex F, v.val ∈ J → σ v = t := by
      intro v hv
      simpa only [pinExtension_apply] using hJ v.val hv
    refine ⟨hI' i hi, hJ' j hj, (respects_terminals_iff G I J F σ).mpr ?_⟩
    exact ⟨fun x y hx hy => (hI' x hx).trans (hI' y hy).symm,
      fun x y hx hy => (hJ' x hx).trans (hJ' y hy).symm⟩

/-- Identifying each terminal set separately is *exactly* restriction to its
constant configurations; no new model comparison enters this identity. -/
lemma pairTable_contractedPinned {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIF : Disjoint I F) (hJF : Disjoint J F)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J)
    (τ : Spins n) (s t : Bool) :
    pairTable (contractedPinnedWeight G h I J F τ) i j s t =
      jointWeight G h I J F τ (fun _ => s) (fun _ => t) := by
  classical
  have hdel := constrainedSum_delete_variables G h F τ
    (fun ρ => AgreesOn I ρ (fun _ => s) ∧ AgreesOn J ρ (fun _ => t))
  have hswap : jointWeight G h I J F τ (fun _ => s) (fun _ => t) =
      constrainedSum G h (fun ρ => AgreesOn F ρ τ ∧
        (AgreesOn I ρ (fun _ => s) ∧ AgreesOn J ρ (fun _ => t))) := by
    unfold jointWeight constrainedSum
    apply Finset.sum_congr rfl
    intro ρ _
    congr 1
    exact propext and_rotate.symm
  rw [hswap, hdel]
  unfold pairTable
  apply Finset.sum_congr rfl
  intro σ _
  unfold contractedPinnedWeight
  have H := contracted_prescription_iff G I J F hIF hJF i j hi hj τ σ s t
  by_cases hc : σ i = s ∧ σ j = t
  · rw [ite_eq_left hc]
    by_cases hr : Respects (comparisonSetoid G I J F ∅) σ
    · rw [ite_eq_left hr, ite_eq_left (H.mp ⟨hc.1, hc.2, hr⟩)]
    · rw [ite_eq_right hr, ite_eq_right (fun hp => hr (H.mpr hp).2.2)]
  · rw [ite_eq_right hc, ite_eq_right (fun hp => hc ⟨(H.mpr hp).1, (H.mpr hp).2.1⟩)]

end BufferedIsing

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem solution {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIF : Disjoint I F) (hJF : Disjoint J F)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J)
    (τ : Spins n) (s t : Bool) :
    pairTable (contractedPinnedWeight G h I J F τ) i j s t =
      jointWeight G h I J F τ (fun _ => s) (fun _ => t) := by
  first
    | exact OAI.BufferedIsing.pairTable_contractedPinned G h I J F hIF hJF i j hi hj τ s t
    | exact OAI.BufferedIsing.pairTable_contractedPinned
    | (apply OAI.BufferedIsing.pairTable_contractedPinned <;> assumption)
    | (intros; apply OAI.BufferedIsing.pairTable_contractedPinned <;> assumption)
