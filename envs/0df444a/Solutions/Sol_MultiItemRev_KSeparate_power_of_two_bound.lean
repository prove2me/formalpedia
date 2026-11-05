-- Prove2me | solution 1 for MultiItemRev.KSeparate.power_of_two_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:19:14.585823+00:00
-- url     : https://prove2.me/submissions/33b678c3-c08e-4468-a167-4d645af32e2c

import Mathlib
import Definitions.Def_MultiItemRev_KSeparate_Model
import Theorems.Thm_MultiItemRev_KSeparate_theorem_7
import Theorems.Thm_MultiItemRev_KSeparate_theorem_A

open MeasureTheory
open scoped NNReal ENNReal

namespace KSepPow2Aux
open MultiItemRev.Decomp

/-- Relabeling the goods does not increase the optimal revenue. -/
lemma rev_map_reindex_le {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    (μ : Measure (ι → ℝ≥0)) :
    Rev (μ.map (MeasurableEquiv.piCongrLeft (fun _ : ι' => ℝ≥0) e)) ≤ Rev μ := by
  unfold Rev
  refine iSup₂_le fun M' hM' => ?_
  set g := MeasurableEquiv.piCongrLeft (fun _ : ι' => ℝ≥0) e with hg
  let M : Mechanism ι := ⟨fun x i => M'.q (g x) (e i), fun x => M'.s (g x)⟩
  have hsum : ∀ (x' x : ι → ℝ≥0),
      ∑ i, M.q x' i * (x i : ℝ) = ∑ i', M'.q (g x') i' * (g x i' : ℝ) := by
    intro x' x
    exact Fintype.sum_equiv e _ _ (fun i => by
      simp [M, g, MeasurableEquiv.piCongrLeft_apply_apply])
  obtain ⟨hF, hIC, hIR, hm⟩ := hM'
  have hM : IsAdmissible M := by
    refine ⟨fun x i => hF (g x) (e i), fun x x' => ?_, fun x => ?_, hm.comp g.measurable⟩
    · have := hIC (g x) (g x')
      unfold buyerPayoff at *
      rw [hsum, hsum]
      exact this
    · have := hIR (g x)
      unfold buyerPayoff at *
      rw [hsum]
      exact this
  have hrev : expRevenue (μ.map g) M' = expRevenue μ M := by
    unfold expRevenue
    rw [lintegral_map (f := fun x => ENNReal.ofReal (M'.s x))
        (ENNReal.measurable_ofReal.comp hm) g.measurable,
      lintegral_map (f := fun x => ENNReal.ofReal (-M'.s x))
        (ENNReal.measurable_ofReal.comp hm.neg) g.measurable]
  rw [hrev]
  exact le_iSup₂ (f := fun (M : Mechanism ι) (_ : IsAdmissible M) =>
    (expRevenue μ M).toENNReal) M hM

/-- Splitting a product of laws along `ι₁ ⊕ ι₂ ≃ ι` into two independent blocks. -/
lemma rev_pi_le_joint {ι₁ ι₂ ι : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι]
    (e : ι₁ ⊕ ι₂ ≃ ι) (ν : ι → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)] :
    Rev (Measure.pi ν) ≤
      Rev (jointLaw (Measure.pi (fun i => ν (e (Sum.inl i))))
        (Measure.pi (fun j => ν (e (Sum.inr j))))) := by
  have h1 := (measurePreserving_piCongrLeft (α := fun _ : ι => ℝ≥0) ν e).map_eq
  have h2 := (measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : ι₁ ⊕ ι₂ => ℝ≥0) (fun s => ν (e s))).map_eq
  have hJ : jointLaw (Measure.pi (fun i => ν (e (Sum.inl i))))
      (Measure.pi (fun j => ν (e (Sum.inr j)))) = Measure.pi (fun s => ν (e s)) := h2
  rw [hJ, ← h1]
  exact rev_map_reindex_le _ _

lemma pi_unit_eq_oneGood (ρ : Unit → Measure ℝ≥0) [∀ u, IsProbabilityMeasure (ρ u)] :
    Measure.pi ρ = oneGood (ρ ()) := by
  have hρ : ρ = fun _ => ρ () := funext fun u => rfl
  have h := (measurePreserving_funUnique (ρ ()) Unit).symm.map_eq
  rw [hρ, ← h, oneGood]
  rfl

lemma map_eval_pi {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ≥0)
    [∀ i, IsProbabilityMeasure (ν i)] (i : ι) :
    (Measure.pi ν).map (fun x => x i) = ν i := by
  classical
  have := Measure.pi_map_eval (μ := ν) i
  simp only [measure_univ, Finset.prod_const_one, one_smul] at this
  exact this

lemma srev_pi {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ≥0)
    [∀ i, IsProbabilityMeasure (ν i)] :
    SRev (Measure.pi ν) = ∑ i, Rev1 (ν i) := by
  unfold SRev
  simp only [map_eval_pi]

lemma sum_split {ι₁ ι₂ ι : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι]
    (e : ι₁ ⊕ ι₂ ≃ ι) (f : ι → ℝ≥0∞) :
    ∑ i, f i = ∑ i, f (e (Sum.inl i)) + ∑ j, f (e (Sum.inr j)) := by
  rw [← Fintype.sum_sum_type (fun s => f (e s))]
  exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm

lemma logb_two_pow (m : ℕ) : Real.logb 2 ((2 ^ m : ℕ) : ℝ) = (m : ℝ) := by
  push_cast
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

end KSepPow2Aux

open KSepPow2Aux MultiItemRev.Decomp in
theorem solution (c : ℝ) (hcpos : 0 < c)
    (hc : ∀ (k : ℕ), 2 ≤ k →
      ∀ (ν : Fin k → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)],
        ENNReal.ofReal (c / Real.log (k : ℝ)) *
          MultiItemRev.Decomp.BRev (Measure.pi ν) ≤ MultiItemRev.Decomp.SRev (Measure.pi ν))
    (m : ℕ) (hm : 1 ≤ m)
    (ν : Fin (2 ^ m) → Measure ℝ≥0)
    [∀ i, IsProbabilityMeasure (ν i)] :
    MultiItemRev.Decomp.Rev (Measure.pi ν) ≤
      ENNReal.ofReal
          (1 / min c (1 / 2 : ℝ) *
            (Real.logb 2 ((2 ^ m : ℕ) : ℝ)) ^ 2) *
        (∑ i, MultiItemRev.Decomp.Rev1 (ν i)) := by
  set A : ℝ := 1 / min c (1 / 2 : ℝ) with hA
  have hmin : 0 < min c (1 / 2 : ℝ) := lt_min hcpos (by norm_num)
  have hA2 : 2 ≤ A := by
    rw [hA, le_div_iff₀ hmin]
    nlinarith [min_le_right c (1 / 2 : ℝ)]
  have hAc : 1 / c ≤ A := by
    rw [hA]
    exact one_div_le_one_div_of_le hmin (min_le_left _ _)
  rw [logb_two_pow]
  -- the BRev bound from Proposition 13 (ii)
  have hB : ∀ n : ℕ, 1 ≤ n → ∀ (ρ : Fin (2 ^ n) → Measure ℝ≥0)
      [∀ i, IsProbabilityMeasure (ρ i)],
      BRev (Measure.pi ρ) ≤ ENNReal.ofReal (A * n) * ∑ i, Rev1 (ρ i) := by
    intro n hn ρ _
    have hk : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h := hc (2 ^ n) hk ρ
    rw [srev_pi] at h
    have hL : Real.log (((2 ^ n : ℕ) : ℝ)) = n * Real.log 2 := by
      push_cast; rw [Real.log_pow]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2' : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    set L := Real.log (((2 ^ n : ℕ) : ℝ)) with hLdef
    have hLpos : 0 < L := by rw [hL]; positivity
    have hone : ENNReal.ofReal (L / c) * ENNReal.ofReal (c / L) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity),
        show L / c * (c / L) = 1 by field_simp, ENNReal.ofReal_one]
    calc BRev (Measure.pi ρ) = ENNReal.ofReal (L / c) * (ENNReal.ofReal (c / L) *
          BRev (Measure.pi ρ)) := by rw [← mul_assoc, hone, one_mul]
      _ ≤ ENNReal.ofReal (L / c) * ∑ i, Rev1 (ρ i) := by gcongr
      _ ≤ ENNReal.ofReal (A * n) * ∑ i, Rev1 (ρ i) := by
        gcongr
        rw [hL, div_eq_mul_one_div, mul_comm]
        calc 1 / c * (n * Real.log 2) ≤ A * (n * 1) := by gcongr
          _ = A * n := by ring
  -- induction on m
  induction m, hm using Nat.le_induction with
  | base =>
    have e : Unit ⊕ Unit ≃ Fin (2 ^ 1) :=
      Fintype.equivOfCardEq (by simp)
    have h1 := rev_pi_le_joint e ν
    simp only [pi_unit_eq_oneGood] at h1
    have h2 := MultiItemRev.KSeparate.theorem_A (ν (e (Sum.inl ()))) (ν (e (Sum.inr ())))
    have hs := sum_split e (fun i => Rev1 (ν i))
    simp only [Fintype.univ_unit, Finset.sum_singleton] at hs
    rw [hs]
    calc Rev (Measure.pi ν) ≤ 2 * (Rev1 (ν (e (Sum.inl ()))) + Rev1 (ν (e (Sum.inr ())))) :=
          h1.trans h2
      _ ≤ ENNReal.ofReal (A * ((1 : ℕ) : ℝ) ^ 2) *
          (Rev1 (ν (e (Sum.inl ()))) + Rev1 (ν (e (Sum.inr ())))) := by
        gcongr
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
        apply ENNReal.ofReal_le_ofReal
        simpa using hA2
  | succ n hn ih =>
    have e : Fin (2 ^ n) ⊕ Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) :=
      Fintype.equivOfCardEq (by simp [pow_succ]; ring)
    have : Nonempty (Fin (2 ^ n)) := ⟨⟨0, by positivity⟩⟩
    set νY : Fin (2 ^ n) → Measure ℝ≥0 := fun i => ν (e (Sum.inl i)) with hνY
    set νZ : Fin (2 ^ n) → Measure ℝ≥0 := fun i => ν (e (Sum.inr i)) with hνZ
    have h1 := rev_pi_le_joint e ν
    have h7 := (MultiItemRev.KSeparate.theorem_7 (Measure.pi νY) (Measure.pi νZ)).1
    have hY := ih νY
    have hZ := ih νZ
    have hBY := hB n hn νY
    have hBZ := hB n hn νZ
    have hs := sum_split e (fun i => Rev1 (ν i))
    rw [hs]
    set SY := ∑ i, Rev1 (νY i)
    set SZ := ∑ i, Rev1 (νZ i)
    have hnn : (0 : ℝ) ≤ n := by positivity
    have hA0 : 0 ≤ A := by linarith
    calc Rev (Measure.pi ν) ≤ Rev (Measure.pi νY) + Rev (Measure.pi νZ) +
          BRev (Measure.pi νY) + BRev (Measure.pi νZ) := h1.trans h7
      _ ≤ ENNReal.ofReal (A * (n : ℝ) ^ 2) * SY + ENNReal.ofReal (A * (n : ℝ) ^ 2) * SZ +
          ENNReal.ofReal (A * n) * SY + ENNReal.ofReal (A * n) * SZ := by gcongr
      _ = ENNReal.ofReal (A * (n : ℝ) ^ 2 + A * n) * (SY + SZ) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        ring
      _ ≤ ENNReal.ofReal (A * ((n + 1 : ℕ) : ℝ) ^ 2) * (SY + SZ) := by
        gcongr
        push_cast
        nlinarith
