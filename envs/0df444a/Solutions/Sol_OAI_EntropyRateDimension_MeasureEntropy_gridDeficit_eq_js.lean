-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.gridDeficit_eq_js
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:25:56.845174+00:00
-- url     : https://prove2.me/submissions/48e2a804-a7f8-4068-b8b4-006fc854322c

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory
theorem h44_massfair (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (u : ℝ) (j : ℤ) :
    mass (fairShift μ s) (label s u) j =
      (mass μ (label s u) j+mass μ (label s u) (j-1))/2 := by
  have hm : ∀ k : ℤ, MeasurableSet {x | label s u x = k} :=
    fun k => label_measurable s u (measurableSet_singleton k)
  unfold mass fairShift
  rw [Measure.real_def, Measure.coe_finsetSum, Finset.sum_apply, Fin.sum_univ_two]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply (by fun_prop) (hm j), Measure.map_apply (by fun_prop) (hm j)]
  have e0 : (fun x => x + (((0 : Fin 2) : ℕ) : ℝ) * s) ⁻¹' {x | label s u x = j} =
      {x | label s u x = j} := by
    ext x; simp
  have e1 : (fun x => x + (((1 : Fin 2) : ℕ) : ℝ) * s) ⁻¹' {x | label s u x = j} =
      {x | label s u x = j - 1} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, label, Fin.val_one, Nat.cast_one, one_mul]
    rw [show (x + s) / s + u = x / s + u + 1 by field_simp; ring, Int.floor_add_one]
    omega
  simp only [Fin.val_zero, Fin.val_one] at e0 e1 ⊢
  rw [e0, e1, ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
  simp only [Measure.real_def]
  ring

theorem h44_mapwZ (p : FiniteDistribution ℤ) (f : ℤ → ℤ) (b : ℤ) :
    (p.map f).weight b = ∑ a ∈ p.support, if f a = b then p.weight a else 0 := by
  unfold FiniteDistribution.map FiniteEntropy.mass
  dsimp only
  rw [Finset.sum_filter]
  congr 1
  ext a
  congr

theorem h44_entinjZ (p : FiniteDistribution ℤ)
    (f : ℤ → ℤ) (hf : Function.Injective f) : (p.map f).entropy=p.entropy := by
  unfold FiniteDistribution.entropy
  rw [← hf.tsum_eq]
  · congr 1
    ext a
    rw [h44_mapwZ]
    congr 1
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      rw [if_neg (fun h => hb (hf h))]
    · intro ha
      rw [if_pos rfl]
      exact p.vanish a ha
  · intro b hb
    by_contra hr
    apply hb
    show Real.negMulLog ((p.map f).weight b) = 0
    rw [h44_mapwZ, Finset.sum_eq_zero (fun a _ => if_neg (fun h => hr ⟨a, h⟩))]
    exact Real.negMulLog_zero

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    gridDeficit μ s u=(gridLaw μ hμ hs u).js ((gridLaw μ hμ hs u).translate 1) := by
  set p := gridLaw μ hμ hs u with hpdef
  have hw : ∀ j, p.weight j = mass μ (label s u) j := fun j => rfl
  have ht : ∀ j, (p.translate 1).weight j = mass μ (label s u) (j - 1) := by
    intro j
    unfold FiniteDistribution.translate
    rw [h44_mapwZ, Finset.sum_eq_single (j - 1)]
    · rw [if_pos (by ring), hw]
    · intro b _ hb
      rw [if_neg (fun h => hb (by omega))]
    · intro hn
      rw [if_pos (by ring)]
      exact p.vanish _ hn
  have hent : (p.translate 1).entropy = p.entropy :=
    h44_entinjZ p _ (fun a b h => by simpa using h)
  have hmix : (p.mix (p.translate 1)).entropy = grid (fairShift μ s) s u := by
    unfold FiniteDistribution.entropy grid MeasureEntropy.entropy
    congr 1
    ext j
    rw [h44_massfair μ hs u j]
    congr 1
    show (p.weight j + (p.translate 1).weight j) / 2 = _
    rw [hw, ht]
  have hp : p.entropy = grid μ s u := rfl
  unfold gridDeficit FiniteDistribution.js
  rw [hmix, hent, hp]
  ring

