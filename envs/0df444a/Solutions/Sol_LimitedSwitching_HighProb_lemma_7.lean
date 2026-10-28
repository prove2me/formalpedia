-- Prove2me | solution 1 for LimitedSwitching.HighProb.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-28T13:16:28.902986+00:00
-- url     : https://prove2.me/submissions/6aacdea0-1621-4ca9-bd74-4000d3d60478

import Mathlib
import Definitions.Def_LimitedSwitching_HighProb_Setting
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace Queelius.FPLStability
open LimitedSwitching.HighProb
lemma argmin_le {n : ℕ} [NeZero n] (v : Fin n → ℝ) (j : Fin n) :
    v (argminFin v) ≤ v j := by
  have hm := Finset.min'_mem (Finset.univ.filter (fun i => v i = Finset.univ.inf' Finset.univ_nonempty v)) (by
    obtain ⟨i, _, h⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty v
    exact ⟨i, by simp [h]⟩)
  change argminFin v ∈ _ at hm
  rw [Finset.mem_filter] at hm
  rw [hm.2]
  exact Finset.inf'_le _ (Finset.mem_univ j)
lemma argmin_index {n : ℕ} [NeZero n] (v : Fin n → ℝ) (i : Fin n)
    (hi : v i = Finset.univ.inf' Finset.univ_nonempty v) : argminFin v ≤ i := by
  exact Finset.min'_le _ i (by simp [hi])
lemma argmin_eq_iff {n : ℕ} [NeZero n] (v : Fin n → ℝ) (i : Fin n) :
    argminFin v = i ↔ (∀ j, v i ≤ v j) ∧ (∀ j, j < i → v i < v j) := by
  constructor
  · intro he
    refine ⟨fun j => he ▸ argmin_le v j, ?_⟩
    intro j hj
    have hle := he ▸ argmin_le v j
    apply lt_of_le_of_ne hle
    intro h
    have hv : v j = Finset.univ.inf' Finset.univ_nonempty v := by
      have hm := Finset.min'_mem (Finset.univ.filter (fun k => v k = Finset.univ.inf' Finset.univ_nonempty v)) (by
        obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty v
        exact ⟨k, by simp [hk]⟩)
      change argminFin v ∈ _ at hm
      exact h.symm.trans (he ▸ (Finset.mem_filter.mp hm).2)
    have hh := argmin_index v j hv
    omega
  · rintro ⟨h, hs⟩
    have he : v i = Finset.univ.inf' Finset.univ_nonempty v := le_antisymm
      (Finset.le_inf' Finset.univ_nonempty v (fun j _ => h j)) (Finset.inf'_le _ (Finset.mem_univ i))
    have hi := argmin_index v i he
    by_contra hn
    have hh := hs (argminFin v) (lt_of_le_of_ne hi hn)
    have hg := argmin_le v i
    linarith
lemma measurable_argmin {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} [NeZero n]
    (v : Ω → Fin n → ℝ) (hv : ∀ i, Measurable (fun ω => v ω i)) :
    Measurable (fun ω => argminFin (v ω)) := by
  classical
  have hsingle (i : Fin n) : MeasurableSet {ω | argminFin (v ω) = i} := by
    have he : {ω | argminFin (v ω) = i} =
        {ω | ∀ j, v ω i ≤ v ω j} ∩ {ω | ∀ j, j < i → v ω i < v ω j} := by
      ext ω
      exact argmin_eq_iff (v ω) i
    rw [he]
    have h1 : MeasurableSet (⋂ j, {ω | v ω i ≤ v ω j}) := MeasurableSet.iInter (fun j => measurableSet_le (hv i) (hv j))
    have h2 : MeasurableSet (⋂ j, {ω | j < i → v ω i < v ω j}) := by
      apply MeasurableSet.iInter
      intro j
      by_cases hj : j < i
      · simpa only [hj, true_implies] using measurableSet_lt (hv i) (hv j)
      · simp only [hj, false_implies, setOf_true]
        exact MeasurableSet.univ
    convert h1.inter h2 using 1 <;> ext ω <;> simp

  intro S hS
  have he : (fun ω => argminFin (v ω)) ⁻¹' S = ⋃ i ∈ S, {ω | argminFin (v ω) = i} := by
    ext ω
    simp
  rw [he]
  exact MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ => hsingle i))
lemma exponential_shift (ε : ℝ) (hε : 0 ≤ ε) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f (x+ε) ∂expMeasure 1) ≤ ENNReal.ofReal (Real.exp ε) * ∫⁻ x, f x ∂expMeasure 1 := by
  have hd : Measurable (exponentialPDF 1) := (measurable_exponentialPDFReal 1).ennreal_ofReal
  change (∫⁻ x, f (x+ε) ∂volume.withDensity (exponentialPDF 1)) ≤
    ENNReal.ofReal (Real.exp ε) * ∫⁻ x, f x ∂volume.withDensity (exponentialPDF 1)
  rw [lintegral_withDensity_eq_lintegral_mul _ hd ((show Measurable (fun x : ℝ => f (x+ε)) from hf.comp (measurable_id.add_const ε))),
    lintegral_withDensity_eq_lintegral_mul _ hd hf]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp ε) * (exponentialPDF 1 (x+ε)*f (x+ε)) := by
      apply lintegral_mono
      intro x
      change exponentialPDF 1 x * f (x+ε) ≤ _
      by_cases hx : 0 ≤ x
      · have hdens : exponentialPDF 1 x = ENNReal.ofReal (Real.exp ε) * exponentialPDF 1 (x+ε) := by
          rw [exponentialPDF_of_nonneg hx,exponentialPDF_of_nonneg (by linarith),
            ← ENNReal.ofReal_mul (by positivity)]
          simp only [one_mul]
          rw [← Real.exp_add]
          congr 1
          congr 1
          ring
        rw [hdens,mul_assoc]
      · rw [exponentialPDF_of_neg (lt_of_not_ge hx),zero_mul]
        exact bot_le
    _ = ENNReal.ofReal (Real.exp ε) * ∫⁻ x, exponentialPDF 1 x*f x := by
      rw [lintegral_const_mul _ (show Measurable (fun x : ℝ => exponentialPDF 1 (x+ε)*f (x+ε)) from (hd.comp (measurable_id.add_const ε)).mul (hf.comp (measurable_id.add_const ε))),
        lintegral_add_right_eq_self (fun x => exponentialPDF 1 x*f x) ε]
lemma pi_shift {n : ℕ} (i : Fin (n+1)) (ε : ℝ) (hε : 0 ≤ ε)
    (f : (Fin (n+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ R, f (Function.update R i (R i+ε)) ∂expLaw (n+1)) ≤
      ENNReal.ofReal (Real.exp ε) * ∫⁻ R, f R ∂expLaw (n+1) := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => expMeasure 1) i).symm
  have hF : Measurable (fun z : ℝ × (Fin n → ℝ) => f (e.symm z)) := hf.comp e.symm.measurable
  have he (z : ℝ × (Fin n → ℝ)) : Function.update (e.symm z) i (e.symm z i+ε) = e.symm (z.1+ε,z.2) := by
    change Function.update (@Fin.insertNth n (fun _ => ℝ) i z.1 z.2) i ((@Fin.insertNth n (fun _ => ℝ) i z.1 z.2) i+ε) = @Fin.insertNth n (fun _ => ℝ) i (z.1+ε) z.2
    simp
  have hu : Measurable (fun R : Fin (n+1) → ℝ => f (Function.update R i (R i+ε))) := by
    apply hf.comp
    exact measurable_pi_iff.mpr (fun j => by
      by_cases h : j=i
      · subst j; simpa only [Function.update_self] using (show Measurable (fun R : Fin (n+1) → ℝ => R i) from measurable_pi_apply i).add_const ε
      · simpa only [Function.update_of_ne h] using measurable_pi_apply j)
  change (∫⁻ R, f (Function.update R i (R i+ε)) ∂Measure.pi (fun _ => expMeasure 1)) ≤
    ENNReal.ofReal (Real.exp ε) * ∫⁻ R, f R ∂Measure.pi (fun _ => expMeasure 1)
  rw [← hp.lintegral_comp hu,← hp.lintegral_comp hf]
  change (∫⁻ z : ℝ × (Fin n → ℝ), f (Function.update (e.symm z) i (e.symm z i+ε)) ∂(expMeasure 1).prod (Measure.pi (fun _ : Fin n => expMeasure 1))) ≤ _
  simp_rw [he]
  change (∫⁻ z : ℝ × (Fin n → ℝ), f (e.symm (z.1+ε,z.2)) ∂(expMeasure 1).prod (Measure.pi (fun _ : Fin n => expMeasure 1))) ≤
    ENNReal.ofReal (Real.exp ε) * ∫⁻ z : ℝ × (Fin n → ℝ), f (e.symm z) ∂(expMeasure 1).prod (Measure.pi (fun _ : Fin n => expMeasure 1))
  have hG : Measurable (fun z : ℝ × (Fin n → ℝ) => f (e.symm (z.1+ε,z.2))) := hF.comp ((measurable_fst.add_const ε).prodMk measurable_snd)
  rw [lintegral_prod_symm _ hG.aemeasurable,lintegral_prod_symm _ hF.aemeasurable]
  calc
    _ ≤ ∫⁻ y : Fin n → ℝ, ENNReal.ofReal (Real.exp ε) * ∫⁻ x, f (e.symm (x,y)) ∂expMeasure 1
        ∂Measure.pi (fun _ => expMeasure 1) := by
      apply lintegral_mono
      intro y
      exact exponential_shift ε hε (fun x => f (e.symm (x,y))) (hF.comp (measurable_id.prodMk measurable_const))
    _ = _ := by
      rw [lintegral_const_mul _ hF.lintegral_prod_left]
lemma boost_stable {n : ℕ} [NeZero n] (ε : ℝ) (hε : 0 < ε)
    (L l R : Fin n → ℝ) (hl : ∀ i, l i ∈ Icc (0:ℝ) 1) (i : Fin n)
    (hi : argminFin (fun j => -R j/ε+L j) = i) :
    argminFin (fun j => -(Function.update R i (R i+ε) j)/ε+L j) = i ∧
    argminFin (fun j => -(Function.update R i (R i+ε) j)/ε+L j+l j) = i := by
  classical
  have hs := (argmin_eq_iff _ i).mp hi
  have hdiv : -(R i+ε)/ε = -R i/ε-1 := by field_simp; ring
  constructor <;> apply (argmin_eq_iff _ i).mpr <;> constructor
  · intro j
    by_cases hj : j=i
    · simp [hj]
    · simp only [Function.update_self,Function.update_of_ne hj,hdiv]
      have := hs.1 j
      linarith
  · intro j hj
    have hne : j≠i := ne_of_lt hj
    simp only [Function.update_self,Function.update_of_ne hne,hdiv]
    have := hs.1 j
    linarith
  · intro j
    by_cases hj : j=i
    · simp [hj]
    · simp only [Function.update_self,Function.update_of_ne hj,hdiv]
      have := hs.1 j
      have := (hl i).2
      have := (hl j).1
      linarith
  · intro j hj
    have hne : j≠i := ne_of_lt hj
    simp only [Function.update_self,Function.update_of_ne hne,hdiv]
    have := hs.2 j hj
    have := (hl i).2
    have := (hl j).1
    linarith
lemma one_step {n : ℕ} [NeZero n] (ε : ℝ) (hε : 0 < ε)
    (L l : Fin n → ℝ) (hl : ∀ i, l i ∈ Icc (0:ℝ) 1) :
    (∫⁻ R, (if argminFin (fun j => -R j/ε+L j) ≠ argminFin (fun j => -R j/ε+L j+l j)
      then 1 else 0 : ℝ≥0∞) ∂expLaw n) ≤ ENNReal.ofReal ε := by
  classical
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    let A := fun R : Fin (n+1) → ℝ => argminFin (fun j => -R j/ε+L j)
    let B := fun R : Fin (n+1) → ℝ => argminFin (fun j => -R j/ε+L j+l j)
    have hA : Measurable A := measurable_argmin _ (fun i => ((show Measurable (fun R : Fin (n+1) → ℝ => R i) from measurable_pi_apply i).neg.div_const ε).add_const (L i))
    have hB : Measurable B := measurable_argmin _ (fun i => (((show Measurable (fun R : Fin (n+1) → ℝ => R i) from measurable_pi_apply i).neg.div_const ε).add_const (L i)).add_const (l i))
    let E := ENNReal.ofReal (Real.exp ε)
    let C := fun i (R : Fin (n+1) → ℝ) => if A R=i ∧ B R=i then (1:ℝ≥0∞) else 0
    let G := fun R => if A R=B R then (1:ℝ≥0∞) else 0
    let D := fun R => if A R≠B R then (1:ℝ≥0∞) else 0
    have hmC (i : Fin (n+1)) : Measurable (C i) :=
      Measurable.ite ((measurableSet_eq_fun hA measurable_const).inter (measurableSet_eq_fun hB measurable_const)) measurable_const measurable_const
    have hmA (i : Fin (n+1)) : Measurable (fun R => if A R=i then (1:ℝ≥0∞) else 0) :=
      Measurable.ite (measurableSet_eq_fun hA measurable_const) measurable_const measurable_const
    have hmG : Measurable G := Measurable.ite (measurableSet_eq_fun hA hB) measurable_const measurable_const
    have hmD : Measurable D := Measurable.ite (measurableSet_eq_fun hA hB).compl measurable_const measurable_const
    have hCi (i : Fin (n+1)) :
        (∫⁻ R, (if A R=i then (1:ℝ≥0∞) else 0) ∂expLaw (n+1)) ≤ E * ∫⁻ R, C i R ∂expLaw (n+1) := by
      calc
        _ ≤ ∫⁻ R, C i (Function.update R i (R i+ε)) ∂expLaw (n+1) := by
          apply lintegral_mono
          intro R
          by_cases hi : A R=i
          · have hh := boost_stable ε hε L l R hl i hi
            simp only [C,A,B,hi,hh.1,hh.2,and_self,if_true,le_refl]
          · simp [hi]
        _ ≤ _ := pi_shift i ε hε.le (C i) (hmC i)
    have hsumA (R : Fin (n+1) → ℝ) : ∑ i : Fin (n+1), (if A R=i then (1:ℝ≥0∞) else 0) = 1 := by simp
    have hsumC (R : Fin (n+1) → ℝ) : ∑ i : Fin (n+1), C i R = G R := by
      by_cases h : A R=B R
      · simp [C,G,← h]
      · have hz (i : Fin (n+1)) : ¬(A R=i ∧ B R=i) := by rintro ⟨ha,hb⟩; exact h (ha.trans hb.symm)
        simp [C,G,h,hz]
    have hs : 1 ≤ E * ∫⁻ R, G R ∂expLaw (n+1) := by
      calc
        _ = ∫⁻ R, ∑ i : Fin (n+1), (if A R=i then (1:ℝ≥0∞) else 0) ∂expLaw (n+1) := by simp_rw [hsumA]; simp
        _ = ∑ i : Fin (n+1), ∫⁻ R, (if A R=i then (1:ℝ≥0∞) else 0) ∂expLaw (n+1) := lintegral_finset_sum _ (fun i _ => hmA i)
        _ ≤ ∑ i : Fin (n+1), E * ∫⁻ R, C i R ∂expLaw (n+1) := Finset.sum_le_sum (fun i _ => hCi i)
        _ = E * ∫⁻ R, G R ∂expLaw (n+1) := by
          rw [← Finset.mul_sum,← lintegral_finset_sum _ (fun i _ => hmC i)]
          simp_rw [hsumC]
    have hGle : (∫⁻ R, G R ∂expLaw (n+1)) ≤ 1 := by
      calc
        _ ≤ ∫⁻ _R : Fin (n+1) → ℝ, (1:ℝ≥0∞) ∂expLaw (n+1) := lintegral_mono (fun R => by simp [G]; split_ifs <;> simp)
        _ = _ := by simp
    have hDle : (∫⁻ R, D R ∂expLaw (n+1)) ≤ 1 := by
      calc
        _ ≤ ∫⁻ _R : Fin (n+1) → ℝ, (1:ℝ≥0∞) ∂expLaw (n+1) := lintegral_mono (fun R => by simp [D]; split_ifs <;> simp)
        _ = _ := by simp
    have hGn := ne_top_of_le_ne_top ENNReal.one_ne_top hGle
    have hDn := ne_top_of_le_ne_top ENNReal.one_ne_top hDle
    have htotal : (∫⁻ R, G R ∂expLaw (n+1)) + (∫⁻ R, D R ∂expLaw (n+1)) = 1 := by
      rw [← lintegral_add_left hmG]
      have hh (R) : G R+D R=1 := by by_cases h : A R=B R <;> simp [G,D,h]
      simp_rw [hh]
      simp
    have hsr : 1 ≤ Real.exp ε * (∫⁻ R, G R ∂expLaw (n+1)).toReal := by
      have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGn) hs
      simpa [E,ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos ε).le] using hh
    have htr : (∫⁻ R, G R ∂expLaw (n+1)).toReal + (∫⁻ R, D R ∂expLaw (n+1)).toReal = 1 := by
      simpa [ENNReal.toReal_add hGn hDn] using congrArg ENNReal.toReal htotal
    have hlow : Real.exp (-ε) ≤ (∫⁻ R, G R ∂expLaw (n+1)).toReal := by
      rw [Real.exp_neg,inv_eq_one_div,div_le_iff₀ (Real.exp_pos ε)]
      simpa [mul_comm] using hsr
    have hnum := Real.add_one_le_exp (-ε)
    have hb : (∫⁻ R, D R ∂expLaw (n+1)).toReal ≤ ε := by linarith
    change (∫⁻ R, D R ∂expLaw (n+1)) ≤ ENNReal.ofReal ε
    exact (ENNReal.toReal_le_toReal hDn ENNReal.ofReal_ne_top).mp (by simpa [ENNReal.toReal_ofReal hε.le] using hb)
lemma measurable_play {n : ℕ} [NeZero n] (ε : ℝ) (ℓ : ℕ → Fin n → ℝ) (t : ℕ) :
    Measurable (fun R => play (fplStar ε) R ℓ t) := by
  apply measurable_argmin _
  intro i
  exact ((show Measurable (fun R : Fin n → ℝ => R i) from measurable_pi_apply i).neg.div_const ε).add_const _
lemma play_add_loss {n : ℕ} [NeZero n] (ε : ℝ) (ℓ : ℕ → Fin n → ℝ) (R : Fin n → ℝ)
    (t : ℕ) (ht : 1 ≤ t) :
    play (fplStar ε) R ℓ (t+1) =
      argminFin (fun j => -R j/ε+(∑ s : Fin (t-1), ℓ (s.val+1) j)+ℓ t j) := by
  unfold play fplStar
  simp only [Nat.add_sub_cancel,Fin.sum_univ_eq_sum_range]
  congr 1
  funext j
  change -R j/ε+(∑ s : Fin t, ℓ (s.val+1) j) = -R j/ε+(∑ s : Fin (t-1), ℓ (s.val+1) j)+ℓ t j
  rw [Fin.sum_univ_eq_sum_range (fun s => ℓ (s+1) j) t,Fin.sum_univ_eq_sum_range (fun s => ℓ (s+1) j) (t-1)]
  have he : (∑ s ∈ Finset.range t, ℓ (s+1) j) = (∑ s ∈ Finset.range (t-1), ℓ (s+1) j)+ℓ t j := by
    nth_rw 1 [show t=(t-1)+1 by omega]
    rw [Finset.sum_range_succ]
    congr 1
    congr 1
    omega
  rw [he]
  ring
lemma switch_step {n : ℕ} [NeZero n] (ε : ℝ) (hε : 0 < ε)
    (ℓ : ℕ → Fin n → ℝ) (hℓ : IsLossSeq ℓ) (t : ℕ) (ht : 2 ≤ t) :
    (∫⁻ R, (if play (fplStar ε) R ℓ t ≠ play (fplStar ε) R ℓ (t-1)
      then 1 else 0 : ℝ≥0∞) ∂expLaw n) ≤ ENNReal.ofReal ε := by
  have h := one_step ε hε (fun j => ∑ s : Fin (t-1-1), ℓ (s.val+1) j) (ℓ (t-1)) (hℓ (t-1) (by omega))
  have he (R : Fin n → ℝ) := play_add_loss ε ℓ R (t-1) (by omega)
  simp only [show t-1+1=t by omega] at he
  simp_rw [he]
  simpa only [play,fplStar,ne_comm] using h
lemma expected_switches {n : ℕ} [NeZero n] (ε : ℝ) (hε : 0 < ε)
    (ℓ : ℕ → Fin n → ℝ) (hℓ : IsLossSeq ℓ) (τ : ℕ) :
    (∫⁻ R, (switches τ (play (fplStar ε) R ℓ) : ℝ≥0∞) ∂expLaw n) ≤ ENNReal.ofReal (ε*τ) := by
  classical
  have he (R : Fin n → ℝ) : (switches τ (play (fplStar ε) R ℓ) : ℝ≥0∞) =
      ∑ t ∈ Finset.Icc 2 τ, (if play (fplStar ε) R ℓ t ≠ play (fplStar ε) R ℓ (t-1) then 1 else 0 : ℝ≥0∞) := by
    simp only [switches,Finset.card_eq_sum_ones,Nat.cast_sum,Nat.cast_one,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    split_ifs <;> simp
  simp_rw [he]
  have hm (t : ℕ) : Measurable (fun R : Fin n → ℝ => (if play (fplStar ε) R ℓ t ≠ play (fplStar ε) R ℓ (t-1) then 1 else 0 : ℝ≥0∞)) :=
    Measurable.ite (measurableSet_eq_fun (measurable_play ε ℓ t) (measurable_play ε ℓ (t-1))).compl measurable_const measurable_const
  rw [lintegral_finset_sum _ (fun t _ => hm t)]
  calc
    _ ≤ ∑ t ∈ Finset.Icc 2 τ, ENNReal.ofReal ε := Finset.sum_le_sum (fun t ht => switch_step ε hε ℓ hℓ t (Finset.mem_Icc.mp ht).1)
    _ = ENNReal.ofReal (ε*((Finset.Icc 2 τ).card:ℝ)) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [mul_comm,← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul hε.le]
    _ ≤ ENNReal.ofReal (ε*τ) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ hε.le
      exact_mod_cast (show (Finset.Icc 2 τ).card ≤ τ by simp)
lemma bound_weaken {n : ℕ} [NeZero n] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (τ : ℕ) :
    ε*τ ≤ (ε*τ+2*Real.log n)/(1-ε) := by
  have hn : (1:ℝ) ≤ n := by exact_mod_cast NeZero.one_le
  have hlog := Real.log_nonneg hn
  apply (le_div_iff₀ (by linarith : 0 < 1-ε)).mpr
  have hp : 0 ≤ ε*(τ:ℝ) := by positivity
  nlinarith
lemma zero_loss_switches {n : ℕ} [NeZero n] (ε : ℝ) (R : Fin n → ℝ) (τ : ℕ) :
    switches τ (play (fplStar ε) R (fun _ _ => 0)) = 0 := by
  simp [play,fplStar,switches]
lemma zero_shift (f : ℝ → ℝ≥0∞) :
    (∫⁻ x, f (x+0) ∂expMeasure 1) = ∫⁻ x, f x ∂expMeasure 1 := by simp
end Queelius.FPLStability
open LimitedSwitching.HighProb in
theorem solution {n : ℕ} [NeZero n] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (τ : ℕ)
    (ℓ : ℕ → Fin n → ℝ) (hℓ : IsLossSeq ℓ) :
    ∫⁻ R, (switches τ (play (fplStar ε) R ℓ) : ℝ≥0∞) ∂expLaw n ≤
      ENNReal.ofReal ((ε*τ+2*Real.log n)/(1-ε)) :=
  (Queelius.FPLStability.expected_switches ε hε ℓ hℓ τ).trans
    (ENNReal.ofReal_le_ofReal (Queelius.FPLStability.bound_weaken ε hε hε1 τ))
