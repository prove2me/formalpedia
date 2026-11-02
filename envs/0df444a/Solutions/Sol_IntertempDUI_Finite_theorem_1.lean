-- Prove2me | solution 1 for IntertempDUI.Finite.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T16:15:48.447252+00:00
-- url     : https://prove2.me/submissions/9070a2d4-9768-4852-bd08-07d2e7a4c033
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_IntertempDUI_Finite_DUI
import Theorems.Thm_IntertempDUI_Finite_lemma_A1_R_imp_Rstar
import Theorems.Thm_IntertempDUI_Finite_lemma_B2_dui_to_content
import Theorems.Thm_IntertempDUI_Finite_lemma_B2_content_to_dui
import Theorems.Thm_IntertempDUI_Finite_theorem_B2_b

open IntertempDUI.Finite

namespace IDUIThm1Red

/-- The Lebesgue–Stieltjes mass of the initial interval ⌊0,t⌉ is ρ(t) - ρ(0). -/
lemma measure_bracket_zero (T : ℝ) (ρ : StieltjesFunction ℝ) (hc : Continuous (ρ : ℝ → ℝ))
    (t : ℝ) (h0 : 0 ≤ t) (ht : t ≤ T) :
    (ρ.measure (Subtype.val '' bracket T 0 t)).toReal = ρ t - ρ 0 := by
  have hlim : ∀ x, Function.leftLim (ρ : ℝ → ℝ) x = ρ x := fun x =>
    (ρ.mono.continuousWithinAt_Iio_iff_leftLim_eq).1 (hc.continuousAt.continuousWithinAt)
  have hsub1 : Set.Ico 0 t ⊆ Subtype.val '' bracket T 0 t := by
    intro x hx
    refine ⟨⟨x, hx.1, le_trans hx.2.le ht⟩, ?_, rfl⟩
    simp only [bracket, Set.mem_ofPred_eq]
    refine ⟨?_, Or.inl hx.2⟩
    rcases lt_or_eq_of_le hx.1 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨trivial, h.symm⟩
  have hsub2 : Subtype.val '' bracket T 0 t ⊆ Set.Icc 0 t := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [bracket, Set.mem_ofPred_eq] at hy
    refine ⟨y.2.1, ?_⟩
    rcases hy.2 with h | h
    · exact h.le
    · rw [h.2, h.1]
  have e1 : ρ.measure (Set.Ico 0 t) = ENNReal.ofReal (ρ t - ρ 0) := by
    rw [StieltjesFunction.measure_Ico, hlim, hlim]
  have e2 : ρ.measure (Set.Icc 0 t) = ENNReal.ofReal (ρ t - ρ 0) := by
    rw [StieltjesFunction.measure_Icc, hlim]
  have hm : ρ.measure (Subtype.val '' bracket T 0 t) = ENNReal.ofReal (ρ t - ρ 0) :=
    le_antisymm (e2 ▸ MeasureTheory.measure_mono hsub2) (e1 ▸ MeasureTheory.measure_mono hsub1)
  rw [hm, ENNReal.toReal_ofReal]
  linarith [ρ.mono h0]

end IDUIThm1Red

open IDUIThm1Red in
theorem solution {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref)
    (hR : Richness A pref) (hM : MinEqn A pref) :
    ((ISep A pref ∧ LSep A pref ∧ StEq A pref ∧ CondC pref ∧
      Dom A pref ∧ CIP A pref ∧ TC A pref ∧ Eph A pref) ↔
      ∃ (ρ : StieltjesFunction ℝ) (u : X → ℝ), IsDUIRep (le_of_lt hT) A pref ρ u) ∧
    (∀ ρ u ρ' u', IsDUIRep (le_of_lt hT) A pref ρ u →
      IsDUIRep (le_of_lt hT) A pref ρ' u' →
      Set.EqOn (ρ : ℝ → ℝ) (ρ' : ℝ → ℝ) (Set.Icc 0 T) ∧
      ∃ a b : ℝ, 0 < a ∧ ∀ x : X, u' x = a * u x + b) := by
  have hRs : RichnessStar A pref := lemma_A1_R_imp_Rstar T hT A hconst pref hstd hR
  obtain ⟨hB, hU⟩ := theorem_B2_b T hT A hconst pref hstd hRs hM
  refine ⟨⟨fun hax => ?_, fun ⟨ρ, u, hρ⟩ => ?_⟩, fun ρ u ρ' u' h1 h2 => ?_⟩
  · obtain ⟨u, μ, hcu, hfs, hna⟩ := hB.1 hax
    obtain ⟨ρ, hρ, -⟩ := lemma_B2_content_to_dui T hT A hconst pref hstd u μ hcu hfs hna
    exact ⟨ρ, u, hρ⟩
  · obtain ⟨hcu, hfs, hna⟩ := lemma_B2_dui_to_content T hT A hconst pref hstd hM ρ u hρ
    exact hB.2 ⟨u, _, hcu, hfs, hna⟩
  · obtain ⟨hcu1, hfs1, hna1⟩ := lemma_B2_dui_to_content T hT A hconst pref hstd hM ρ u h1
    obtain ⟨hcu2, hfs2, hna2⟩ := lemma_B2_dui_to_content T hT A hconst pref hstd hM ρ' u' h2
    obtain ⟨hμ, hab⟩ := hU u _ u' _ hcu1 hcu2 hfs1 hfs2 hna1 hna2
    refine ⟨?_, hab⟩
    intro t ht
    rcases lt_or_eq_of_le ht.1 with htpos | ht0
    · have hspan : IsTimeSpan (bracket T 0 t) := by
        refine ⟨1, fun _ => 0, fun _ => t, fun _ => ⟨le_refl _, htpos, ht.2⟩, ?_, ?_⟩
        · intro i j hij; exact absurd hij (by omega)
        · ext x; simp only [Set.mem_iUnion]; exact ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩
      have e := hμ _ hspan
      rw [measure_bracket_zero T ρ h1.2.1 t ht.1 ht.2, measure_bracket_zero T ρ' h2.2.1 t ht.1 ht.2,
        h1.2.2.2.1, h2.2.2.2.1] at e
      linarith
    · rw [← ht0, h1.2.2.2.1, h2.2.2.2.1]
