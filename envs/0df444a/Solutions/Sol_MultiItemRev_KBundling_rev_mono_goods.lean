-- Prove2me | solution 1 for MultiItemRev.KBundling.rev_mono_goods
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:21:13.135161+00:00
-- url     : https://prove2.me/submissions/f5a80fa1-d2a7-439e-90e5-b20ac625dbe4

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace KBRevMonoAux
open MultiItemRev.Decomp

/-- Restriction of `x : Fin (k+d) → ℝ≥0` to the first `k` goods. -/
def restr (k d : ℕ) (x : Fin (k + d) → ℝ≥0) : Fin k → ℝ≥0 := fun i => x (Fin.castAdd d i)

lemma measurable_restr (k d : ℕ) : Measurable (restr k d) := by
  unfold restr; fun_prop

lemma map_restr (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (k d : ℕ) :
    (Measure.pi (fun _ : Fin (k + d) => ν)).map (restr k d) =
      Measure.pi (fun _ : Fin k => ν) := by
  have h1 := (measurePreserving_piCongrLeft (fun _ : Fin (k + d) => ν)
    (finSumFinEquiv (m := k) (n := d))).map_eq
  have h2 := (measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : Fin k ⊕ Fin d => ℝ≥0) (fun _ => ν)).map_eq
  rw [← h1, ← h2, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _),
    Measure.map_map (measurable_restr k d) (by fun_prop)]
  have : (restr k d ∘ (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin (k + d) => ℝ≥0)
      (finSumFinEquiv (m := k) (n := d))) ∘
      ⇑(MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin d => ℝ≥0)).symm)) = Prod.fst := by
    funext p i
    simp only [Function.comp_apply, restr]
    rw [← finSumFinEquiv_apply_left, MeasurableEquiv.piCongrLeft_apply_apply]
    rfl
  rw [this, Measure.map_fst_prod]
  simp

lemma rev_mono_aux (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (k d : ℕ) :
    Rev (Measure.pi (fun _ : Fin k => ν)) ≤ Rev (Measure.pi (fun _ : Fin (k + d) => ν)) := by
  unfold Rev
  refine iSup₂_le fun M hM => ?_
  obtain ⟨hF, hIC, hIR, hm⟩ := hM
  let M' : Mechanism (Fin (k + d)) :=
    ⟨fun x => Fin.append (M.q (restr k d x)) (fun _ => 0), fun x => M.s (restr k d x)⟩
  have hsum : ∀ (x' x : Fin (k + d) → ℝ≥0),
      ∑ j, M'.q x' j * (x j : ℝ) = ∑ i, M.q (restr k d x') i * (restr k d x i : ℝ) := by
    intro x' x
    rw [Fin.sum_univ_add]
    simp [M', restr]
  have hM' : IsAdmissible M' := by
    refine ⟨fun x j => ?_, fun x x' => ?_, fun x => ?_, hm.comp (measurable_restr k d)⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa [M'] using hF (restr k d x) i
      · simp [M']
    · have := hIC (restr k d x) (restr k d x')
      unfold buyerPayoff at *
      rw [hsum, hsum]
      exact this
    · have := hIR (restr k d x)
      unfold buyerPayoff at *
      rw [hsum]
      exact this
  have hrev : expRevenue (Measure.pi (fun _ : Fin k => ν)) M =
      expRevenue (Measure.pi (fun _ : Fin (k + d) => ν)) M' := by
    unfold expRevenue
    rw [← map_restr ν k d,
      lintegral_map (f := fun x => ENNReal.ofReal (M.s x))
        (ENNReal.measurable_ofReal.comp hm) (measurable_restr k d),
      lintegral_map (f := fun x => ENNReal.ofReal (-M.s x))
        (ENNReal.measurable_ofReal.comp hm.neg) (measurable_restr k d)]
  rw [hrev]
  exact le_iSup₂ (f := fun (M : Mechanism (Fin (k + d))) (_ : IsAdmissible M) =>
    (expRevenue (Measure.pi (fun _ : Fin (k + d) => ν)) M).toENNReal) M' hM'

/-- For one good, the payment of an IC mechanism is nondecreasing in the value. -/
lemma pay_mono (M : Mechanism Unit) (hIC : IsIC M) (a b : ℝ≥0) (hab : a ≤ b) :
    M.s (fun _ => a) ≤ M.s (fun _ => b) := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  have h1 := hIC (fun _ => a) (fun _ => b)
  have h2 := hIC (fun _ => b) (fun _ => a)
  simp only [buyerPayoff, Finset.univ_unique, Finset.sum_singleton] at h1 h2
  have ha : (0 : ℝ) ≤ a := a.2
  have hab' : (a : ℝ) < b := h
  nlinarith

/-- One-good revenue is monotone under a pointwise coupling. -/
lemma rev1_mono_coupling {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) (f g : Ω → ℝ≥0)
    (hf : Measurable f) (hg : Measurable g) (hfg : ∀ ω, f ω ≤ g ω) :
    Rev1 (ρ.map f) ≤ Rev1 (ρ.map g) := by
  unfold Rev1 Rev
  refine iSup₂_le fun M hM => ?_
  refine le_trans ?_ (le_iSup₂ (f := fun (M : Mechanism Unit) (_ : IsAdmissible M) =>
    (expRevenue (oneGood (ρ.map g)) M).toENNReal) M hM)
  apply EReal.toENNReal_le_toENNReal
  have hm := hM.2.2.2
  have hc : Measurable (fun (t : ℝ≥0) (_ : Unit) => t) := by fun_prop
  unfold expRevenue oneGood
  rw [Measure.map_map hc hf, Measure.map_map hc hg,
    lintegral_map (f := fun x => ENNReal.ofReal (M.s x))
      (ENNReal.measurable_ofReal.comp hm) (hc.comp hf),
    lintegral_map (f := fun x => ENNReal.ofReal (-M.s x))
      (ENNReal.measurable_ofReal.comp hm.neg) (hc.comp hf),
    lintegral_map (f := fun x => ENNReal.ofReal (M.s x))
      (ENNReal.measurable_ofReal.comp hm) (hc.comp hg),
    lintegral_map (f := fun x => ENNReal.ofReal (-M.s x))
      (ENNReal.measurable_ofReal.comp hm.neg) (hc.comp hg)]
  have hmono : ∀ ω, M.s (fun _ => f ω) ≤ M.s (fun _ => g ω) :=
    fun ω => pay_mono M hM.2.1 _ _ (hfg ω)
  apply EReal.sub_le_sub
  · exact_mod_cast lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hmono ω)
  · exact_mod_cast lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (by have := hmono ω; simp only [Function.comp_apply]; linarith)

lemma brev_mono_aux (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (k d : ℕ) :
    BRev (Measure.pi (fun _ : Fin k => ν)) ≤ BRev (Measure.pi (fun _ : Fin (k + d) => ν)) := by
  unfold BRev
  rw [← map_restr ν k d, Measure.map_map (by fun_prop) (measurable_restr k d)]
  refine rev1_mono_coupling _ _ _ (by unfold restr; fun_prop) (by fun_prop) fun x => ?_
  simp only [Function.comp_apply, restr]
  rw [Fin.sum_univ_add]
  exact le_self_add

end KBRevMonoAux

open KBRevMonoAux in
theorem solution (k k' : ℕ) (hk : k ≤ k')
    (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    MultiItemRev.Decomp.Rev (Measure.pi (fun _ : Fin k => ν)) ≤ MultiItemRev.Decomp.Rev (Measure.pi (fun _ : Fin k' => ν)) ∧
      MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin k => ν)) ≤ MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin k' => ν)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact ⟨rev_mono_aux ν k d, brev_mono_aux ν k d⟩
