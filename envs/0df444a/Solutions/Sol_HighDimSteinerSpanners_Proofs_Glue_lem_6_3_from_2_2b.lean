-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.Glue.lem_6_3_from_2_2b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:19.230438+00:00
-- url     : https://prove2.me/submissions/9b8ded0b-26d1-44fa-a203-fee25464b4d0

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
public import Definitions.Def_LeanPool_SteinerSpanners_Glue

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Glue
namespace HighDimSteinerSpanners.Proofs.Glue
theorem _root_.solution
    (h22b : ∀ (C₁ rStar N ℓ : ℕ), 2 ≤ C₁ → 1 ≤ rStar → 1 ≤ N → 1 ≤ ℓ →
      ∀ (F : Fin (ℓ + 1) → Finset (Fin N)),
        (∀ i : Fin (ℓ + 1), (F i).card ≤ C₁ * rStar) →
        ((F 0 ∩ F (Fin.last ℓ)).card : ℝ) ≤ (rStar : ℝ) / 4 →
        ∃ (s : Fin ℓ) (k : ℕ), k ≤ 8 * C₁ ∧
          ∃ (t : Fin k → Fin (ℓ + 1)) (A : Fin k → Finset (Fin N)) (I_k : Finset (Fin N)),
            Pairwise (fun i j => Disjoint (A i) (A j)) ∧
            (∀ r : Fin k, Disjoint (A r) I_k) ∧
            Finset.univ.biUnion A ∪ I_k = F s.castSucc ∩ F s.succ ∧
            (I_k.card : ℝ) ≤ (rStar : ℝ) / 2 ∧
            ∀ r : Fin k,
              let I_rem := (Finset.univ.filter (fun j : Fin k => r < j)).biUnion A ∪ I_k
              Disjoint (A r) (F (t r)) ∧
              I_rem ⊆ F (t r) ∧
              ((A r).card : ℝ) - (rStar : ℝ) / 4 ≤
                ((((F s.castSucc ∪ F s.succ) ∩ F (t r)) \ (A r ∪ I_rem)).card : ℝ)) :
    ∀ (N q C₁ rStar : ℕ), 2 ≤ N → 2 ≤ q → 3 ≤ C₁ → 1 ≤ rStar →
      ∀ (R : Fin N → Fin N → Fin q → Fin q → Prop),
        Symmetric2CSP R →
        ∀ (X : Finset (Fin N → Fin q)),
          X ⊆ satisfyingSet R →
          let η₀ : ℝ := 1 / 80
          (∀ x ∈ X, ∀ u ∈ X, ∀ z ∈ satisfyingSet R,
            hammingDist x u ≤ C₁ * rStar →
            hammingDist x z ≤ C₁ * rStar →
            ((threeWayDisagree x u z).card : ℝ) ≤ η₀ * (rStar : ℝ)) →
          let L_X : ↥X → ↥X → Finset ↥X := fun a b =>
            if 0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar then
              Finset.univ.filter (fun x : ↥X => x.val ∈ bicliqueWitnessList R C₁ rStar a.val b.val)
            else ∅
          ListHitCond C₁ rStar X L_X := by
  intro N q C₁ rStar hN hq hC₁ hrStar R hSym X hXsat η₀ hD3 L_X x ℓ hℓ w hw_ball hw_step hw_end
      hw_ov
  have hdis_card : ∀ a b : Fin N → Fin q, (disagreeSet a b).card = hammingDist a b := by
    intro a b; rfl
  let F : Fin (ℓ + 1) → Finset (Fin N) := fun i => disagreeSet x.val (w i).val
  obtain ⟨s, k, hk_max, t, A, I_k, hA_pw, hA_Ik, hA_part, hIk_card, h_step⟩ :=
    h22b C₁ rStar N ℓ (by omega) hrStar (by omega) hℓ F
      (fun i => by rw [hdis_card]; exact (hw_ball i).2) hw_ov
  refine ⟨s, ?_⟩
  let a := w s.castSucc
  let b := w s.succ
  have hab_step := hw_step s
  dsimp only [L_X]
  rw [if_pos hab_step, Finset.mem_filter]
  refine ⟨Finset.mem_univ x, ?_⟩
  simp only [bicliqueWitnessList, Finset.mem_filter]
  refine ⟨hXsat x.prop, (hw_ball s.castSucc).1.symm ∘ Subtype.ext,
    (hw_ball s.succ).1.symm ∘ Subtype.ext,
    (hw_ball s.castSucc).2, (hw_ball s.succ).2, ?_⟩
  let I_rem : Fin k → Finset (Fin N) :=
    fun r => (Finset.univ.filter (fun j : Fin k => r < j)).biUnion A ∪ I_k
  let B_fut : Fin k → Finset (Fin N) :=
    fun r => I_rem r \ threeWayDisagree x.val a.val (w (t r)).val
  let B_out : Fin k → Finset (Fin N) :=
    fun r =>
      (((F s.castSucc ∪ F s.succ) ∩ F (t r)) \ (A r ∪ I_rem r)) \
        (threeWayDisagree x.val a.val (w (t r)).val ∪
         threeWayDisagree x.val b.val (w (t r)).val)
  refine ⟨k, hk_max, A, B_fut, B_out, I_k, hA_pw, hA_Ik, hA_part, hIk_card, ?_⟩
  intro r
  obtain ⟨hA_disj, hI_sub, h_out_lb⟩ := h_step r
  have ha3 : ((threeWayDisagree x.val a.val (w (t r)).val).card : ℝ) ≤ η₀ * (rStar : ℝ) :=
    hD3 x.val x.prop a.val a.prop (w (t r)).val (hXsat (w (t r)).prop)
      (hw_ball s.castSucc).2 (hw_ball (t r)).2
  have hb3 : ((threeWayDisagree x.val b.val (w (t r)).val).card : ℝ) ≤ η₀ * (rStar : ℝ) :=
    hD3 x.val x.prop b.val b.prop (w (t r)).val (hXsat (w (t r)).prop)
      (hw_ball s.succ).2 (hw_ball (t r)).2
  refine ⟨Finset.sdiff_subset,
    Finset.sdiff_subset.trans (Finset.sdiff_subset_sdiff Finset.inter_subset_left
        (Finset.Subset.refl _)),
    ?_, ?_, ?_⟩
  · intro u huA v hvB
    have hu_not : u ∉ F (t r) := Finset.disjoint_left.mp hA_disj huA
    have hwu : (w (t r)).val u = x.val u := by
      simp only [F, disagreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu_not
      push Not at hu_not
      exact hu_not.symm
    have hsat_w := hXsat (w (t r)).prop
    simp only [satisfyingSet, Finset.mem_filter, Finset.mem_univ, true_and] at hsat_w
    have hv_Ft_act : v ∈ F (t r) ∧ (w (t r)).val v = activeColor x.val a.val b.val v := by
      rcases Finset.mem_union.mp hvB with hv_fut | hv_out
      · obtain ⟨hv_rem, hv_notD3a⟩ := Finset.mem_sdiff.mp hv_fut
        have hv_Ft : v ∈ F (t r) := hI_sub hv_rem
        have hv_I : v ∈ F s.castSucc ∩ F s.succ := by
          rw [← hA_part]
          rcases Finset.mem_union.mp hv_rem with hv_bi | hv_Ik
          · obtain ⟨j, _, hvAj⟩ := Finset.mem_biUnion.mp hv_bi
            exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hvAj⟩)
          · exact Finset.mem_union_right _ hv_Ik
        have hav : a.val v ≠ x.val v := by
          have h1 := (Finset.mem_inter.mp hv_I).1
          simp only [F, disagreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1
          exact h1.symm
        have hwv_ne : x.val v ≠ (w (t r)).val v := by
          simpa [F, disagreeSet] using hv_Ft
        refine ⟨hv_Ft, ?_⟩
        dsimp [activeColor]
        rw [if_pos hav]
        simp only [threeWayDisagree, Finset.mem_filter, Finset.mem_univ, true_and] at hv_notD3a
        by_contra hne
        exact hv_notD3a ⟨hav.symm, hwv_ne, Ne.symm hne⟩
      · obtain ⟨hv_sdiff, hv_notD3⟩ := Finset.mem_sdiff.mp hv_out
        obtain ⟨hv_W, hv_Ft⟩ := Finset.mem_inter.mp (Finset.mem_sdiff.mp hv_sdiff).1
        simp only [Finset.mem_union, not_or] at hv_notD3
        have hwv_ne : x.val v ≠ (w (t r)).val v := by
          simpa [F, disagreeSet] using hv_Ft
        refine ⟨hv_Ft, ?_⟩
        dsimp [activeColor]
        by_cases hav : a.val v ≠ x.val v
        · rw [if_pos hav]
          have hnot3 := hv_notD3.1
          simp only [threeWayDisagree, Finset.mem_filter, Finset.mem_univ, true_and] at hnot3
          by_contra hne
          exact hnot3 ⟨Ne.symm hav, hwv_ne, Ne.symm hne⟩
        · rw [if_neg hav]
          push Not at hav
          simp only [F, disagreeSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
            true_and] at hv_W
          have hbv : x.val v ≠ b.val v := by
            rcases hv_W with h1 | h2
            · exact absurd hav.symm h1
            · exact h2
          have hnot3 := hv_notD3.2
          simp only [threeWayDisagree, Finset.mem_filter, Finset.mem_univ, true_and] at hnot3
          by_contra hne
          exact hnot3 ⟨hbv, hwv_ne, Ne.symm hne⟩
    have huv_ne : u ≠ v := by
      intro heq; subst heq; exact hu_not hv_Ft_act.1
    rw [← hwu, ← hv_Ft_act.2]
    rcases lt_trichotomy u v with hlt | rfl | hgt
    · exact hsat_w u v hlt
    · exact absurd rfl huv_ne
    · exact (hSym v u _ _).mp (hsat_w v u hgt)
  · have hsub : I_rem r \ B_fut r ⊆ threeWayDisagree x.val a.val (w (t r)).val := by
      intro v hv
      obtain ⟨hv1, hv2⟩ := Finset.mem_sdiff.mp hv
      by_contra hnot
      exact hv2 (Finset.mem_sdiff.mpr ⟨hv1, hnot⟩)
    have hcard : ((I_rem r \ B_fut r).card : ℝ) ≤
        ((threeWayDisagree x.val a.val (w (t r)).val).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    dsimp [η₀] at ha3
    linarith
  · let S_out := ((F s.castSucc ∪ F s.succ) ∩ F (t r)) \ (A r ∪ I_rem r)
    let D3ab := threeWayDisagree x.val a.val (w (t r)).val ∪
        threeWayDisagree x.val b.val (w (t r)).val
    have hsub : S_out ⊆ B_out r ∪ D3ab := by
      intro v hv
      by_cases hvD : v ∈ D3ab
      · exact Finset.mem_union_right _ hvD
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv, hvD⟩)
    have hcard1 : (S_out.card : ℝ) ≤ ((B_out r).card : ℝ) + (D3ab.card : ℝ) := by
      have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      exact_mod_cast h
    have hcard2 : (D3ab.card : ℝ) ≤
        ((threeWayDisagree x.val a.val (w (t r)).val).card : ℝ) +
        ((threeWayDisagree x.val b.val (w (t r)).val).card : ℝ) := by
      exact_mod_cast Finset.card_union_le _ _
    change ((A r).card : ℝ) - (rStar : ℝ) / 4 ≤ (S_out.card : ℝ) at h_out_lb
    dsimp [η₀] at ha3 hb3
    linarith
end HighDimSteinerSpanners.Proofs.Glue
