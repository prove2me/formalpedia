-- Prove2me | solution 1 for MitigateSupplyRisk.DualSourcing.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T12:23:58.607496+00:00
-- url     : https://prove2.me/submissions/4ee46e26-182d-42de-95b7-bd9265345e90

import Mathlib
import Definitions.Def_MitigateSupplyRisk_DualSourcing_Model
import Definitions.Def_MitigateSupplyRisk_DualSourcing_Regions

open MeasureTheory ProbabilityTheory
open MitigateSupplyRisk.DualSourcing
set_option autoImplicit false

namespace SupplyRegions

lemma quantile_antitone (M : Model) (i : Fin 2) (s s' u : ℝ)
    (hGK : ∀ i a, M.G i (M.K i) a = 1) (hu : u ≤ 1) (hss' : s ≤ s') :
    M.Ginv i s' u ≤ M.Ginv i s u := by
  unfold Model.Ginv
  apply le_csInf
  · exact ⟨M.K i, (M.K_pos i).le, by simpa only [hGK] using hu⟩
  · intro t ht
    apply csInf_le
    · exact ⟨0, fun t ht => ht.1⟩
    · exact ⟨ht.1, ht.2.trans (M.ν_mono i s s' hss' t)⟩

lemma hedge_normal_form (M : Model) (a : Fin 2 → ℝ) (x : ℝ) :
    max (M.qstarTotal a x - x) 0 =
      max (min (M.K 0 + M.K 1 - x)
        (min (M.A1 a) (min (M.A2 a)
          (M.A1 a + M.A2 a - (M.K 0 + M.K 1 - x))))) 0 := by
  unfold Model.qstarTotal
  simp only [min_def, max_def]
  split_ifs <;> linarith

end SupplyRegions

theorem solution (M : Model)
    (hη : ∀ i, M.η i = 0)
    (hφpos : ∀ i, 0 < M.phi i) (hφlt : ∀ i, M.phi i < 1)
    (hGK : ∀ i a, M.G i (M.K i) a = 1)
    (hord : M.phi 1 ≤ M.phi 0)
    (i : Fin 2) (a : Fin 2 → ℝ) (s s' : ℝ) (hss' : s ≤ s') :
    M.hedgeRegion (Function.update a i s') ⊆ M.hedgeRegion (Function.update a i s) ∧
    (∀ x : ℝ, 0 ≤ x →
      max (M.qstarTotal (Function.update a i s') x - x) 0 ≤
        max (M.qstarTotal (Function.update a i s) x - x) 0) ∧
    (i = 0 → M.singleRegion (Function.update a i s) ⊆ M.singleRegion (Function.update a i s')) ∧
    (i = 1 → M.singleRegion (Function.update a i s') ⊆ M.singleRegion (Function.update a i s)) := by
  have ha : Function.update a i s ≤ Function.update a i s' := by
    intro j
    by_cases h : j = i
    · subst j
      simpa using hss'
    · simp only [Function.update_of_ne h]
      exact le_rfl
  have hA1 : M.A1 (Function.update a i s') ≤ M.A1 (Function.update a i s) := by
    exact SupplyRegions.quantile_antitone M 0 _ _ _ hGK (hφlt 1).le (ha 0)
  have hA2 : M.A2 (Function.update a i s') ≤ M.A2 (Function.update a i s) := by
    exact SupplyRegions.quantile_antitone M 1 _ _ _ hGK (hφlt 0).le (ha 1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    change _ < x ∧ x ≤ _ at hx ⊢
    exact ⟨by linarith [hx.1], hx.2⟩
  · intro x hx
    rw [SupplyRegions.hedge_normal_form, SupplyRegions.hedge_normal_form]
    exact max_le_max (min_le_min le_rfl (min_le_min hA1
      (min_le_min hA2 (sub_le_sub_right (add_le_add hA1 hA2) _)))) le_rfl
  · intro hi
    subst i
    have hratio : M.phi 1 / M.phi 0 ≤ 1 := by
      apply (div_le_iff₀ (hφpos 0)).2
      simpa using hord
    have hB : M.B (Function.update a 0 s') ≤ M.B (Function.update a 0 s) := by
      simpa [Model.B, hGK] using
        (SupplyRegions.quantile_antitone M 0 s s' (M.phi 1 / M.phi 0) hGK hratio hss')
    intro x hx
    change 0 ≤ x ∧ x ≤ _ at hx ⊢
    exact ⟨hx.1, by linarith [hx.2]⟩
  · intro hi
    subst i
    have hB : M.B (Function.update a 1 s') = M.B (Function.update a 1 s) := by
      simp [Model.B, hGK]
    unfold Model.singleRegion
    rw [hB]

