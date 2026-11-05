-- Prove2me | solution 1 for MultiItemRev.MultiBuyer.subdomain_ds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:54:47.229289+00:00
-- url     : https://prove2.me/submissions/0848e881-fb74-4989-b4e7-56f4bb2f3b04

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model

open MeasureTheory
open scoped NNReal ENNReal

open MultiItemRev.MultiBuyer in
theorem solution {n : ℕ} (hn : 1 ≤ n) {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : Measure (Fin n → ι → ℝ≥0)) [IsProbabilityMeasure μ] (M : MechanismN n ι)
    (hM : IsAdmissibleDS M) (A : Set (Fin n → ι → ℝ≥0)) (hA : MeasurableSet A)
    (hDefined : (∫⁻ x in A, ENNReal.ofReal (sellerRevenue M x) ∂μ) ≠ ⊤ ∨
      (∫⁻ x in A, ENNReal.ofReal (-sellerRevenue M x) ∂μ) ≠ ⊤) :
    ((∫⁻ x in A, ENNReal.ofReal (sellerRevenue M x) ∂μ : ℝ≥0∞) : EReal) -
        ((∫⁻ x in A, ENNReal.ofReal (-sellerRevenue M x) ∂μ : ℝ≥0∞) : EReal) ≤
      (RevDS (lawOnN μ A) : EReal) ∧
    RevDS (lawOnN μ A) ≤ RevDS μ := by
  classical
  have subLe : ∀ (a : EReal) (b : ℝ≥0∞), a - (b : EReal) ≤ a := by
    intro a b
    have := EReal.sub_le_sub (le_refl a) (EReal.coe_ennreal_nonneg b)
    rwa [sub_zero] at this
  -- `s^j(0, x^{-j}) ≤ 0` (IR at a zero report)
  have hzero_le : ∀ M : MechanismN n ι, IsAdmissibleDS M →
      ∀ x j, M.s (Function.update x j 0) j ≤ 0 := by
    intro M hM x j
    have h := hM.2.2.1 (Function.update x j 0) j
    simp [payoffN] at h
    linarith
  -- `s^j(x) ≥ s^j(0, x^{-j})` (IC of type `0` against reporting `x^j`)
  have hge_zero : ∀ M : MechanismN n ι, IsAdmissibleDS M →
      ∀ x j, M.s (Function.update x j 0) j ≤ M.s x j := by
    intro M hM x j
    have h := hM.2.1 (Function.update x j 0) j (x j)
    simp only [Function.update_idem, Function.update_eq_self, payoffN,
      Function.update_self, Pi.zero_apply, NNReal.coe_zero, mul_zero,
      Finset.sum_const_zero, zero_sub] at h
    linarith
  -- NPT normalization
  have hnorm : ∀ M : MechanismN n ι, IsAdmissibleDS M → ∃ M' : MechanismN n ι,
      IsAdmissibleDS M' ∧ (∀ x, sellerRevenue M x ≤ sellerRevenue M' x) ∧
      (∀ x, 0 ≤ sellerRevenue M' x) ∧ sellerRevenue M' 0 = 0 := by
    intro M hM
    let M' : MechanismN n ι :=
      { q := M.q
        s := fun x j => M.s x j - M.s (Function.update x j 0) j }
    have hpay' : ∀ x j, payoffN M' x j = payoffN M x j + M.s (Function.update x j 0) j := by
      intro x j; simp only [payoffN, M']; ring
    refine ⟨M', ⟨hM.1, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro x j x'
      have h := hM.2.1 x j x'
      rw [hpay']
      simp only [M', Function.update_idem] at h ⊢
      linarith
    · intro x j
      rw [hpay']
      have h := hM.2.1 x j 0
      have hq : 0 ≤ ∑ i, M.q (Function.update x j 0) j i * (x j i : ℝ) :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hM.1.1 _ j i).1 (x j i).2
      linarith
    · intro j
      exact (hM.2.2.2 j).sub ((hM.2.2.2 j).comp measurable_update_left)
    · intro x
      simp only [sellerRevenue, M']
      exact Finset.sum_le_sum fun j _ => by linarith [hzero_le M hM x j]
    · intro x
      simp only [sellerRevenue, M']
      exact Finset.sum_nonneg fun j _ => by linarith [hge_zero M hM x j]
    · simp only [sellerRevenue, M']
      apply Finset.sum_eq_zero
      intro j _
      have : Function.update (0 : Fin n → ι → ℝ≥0) j 0 = 0 := by
        rw [Function.update_eq_self_iff]; rfl
      rw [this, sub_self]
  -- revenue of a nonnegative-revenue admissible mechanism
  have hrevNN : ∀ (ν : Measure (Fin n → ι → ℝ≥0)) (M' : MechanismN n ι),
      (∀ x, 0 ≤ sellerRevenue M' x) →
      (expRevenueN ν M').toENNReal = ∫⁻ x, ENNReal.ofReal (sellerRevenue M' x) ∂ν := by
    intro ν M' h0
    have : ∫⁻ x, ENNReal.ofReal (-sellerRevenue M' x) ∂ν = 0 := by
      have : (fun x => ENNReal.ofReal (-sellerRevenue M' x)) = fun _ => 0 := by
        funext x; exact ENNReal.ofReal_of_nonpos (by linarith [h0 x])
      rw [this, lintegral_zero]
    rw [expRevenueN, this]
    simp only [EReal.coe_ennreal_zero, sub_zero, EReal.toENNReal_coe]
  have hrevLe : ∀ (ν : Measure (Fin n → ι → ℝ≥0)) (M M' : MechanismN n ι),
      (∀ x, sellerRevenue M x ≤ sellerRevenue M' x) →
      (expRevenueN ν M).toENNReal ≤ ∫⁻ x, ENNReal.ofReal (sellerRevenue M' x) ∂ν := by
    intro ν M M' hle
    rw [← EReal.toENNReal_coe (x := ∫⁻ x, ENNReal.ofReal (sellerRevenue M' x) ∂ν)]
    apply EReal.toENNReal_le_toENNReal
    unfold expRevenueN
    calc ((∫⁻ x, ENNReal.ofReal (sellerRevenue M x) ∂ν : ℝ≥0∞) : EReal) -
          ((∫⁻ x, ENNReal.ofReal (-sellerRevenue M x) ∂ν : ℝ≥0∞) : EReal)
        ≤ ((∫⁻ x, ENNReal.ofReal (sellerRevenue M x) ∂ν : ℝ≥0∞) : EReal) :=
          subLe _ _
      _ ≤ _ := by
          exact_mod_cast lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hle x)
  have hSm : ∀ M' : MechanismN n ι, IsAdmissibleDS M' →
      Measurable (fun x => ENNReal.ofReal (sellerRevenue M' x)) := fun M' h =>
    (Finset.measurable_sum _ fun j _ => h.2.2.2 j).ennreal_ofReal
  have hind : Measurable (A.indicator (id : (Fin n → ι → ℝ≥0) → (Fin n → ι → ℝ≥0))) :=
    measurable_id.indicator hA
  -- the revenue of a mechanism on `X 1_A`
  have hlaw : ∀ M' : MechanismN n ι, IsAdmissibleDS M' →
      ∫⁻ x, ENNReal.ofReal (sellerRevenue M' x) ∂(lawOnN μ A) =
        ∫⁻ x, ENNReal.ofReal (sellerRevenue M' (A.indicator id x)) ∂μ := by
    intro M' h
    rw [lawOnN, lintegral_map (hSm M' h) hind]
  have hAeq : ∀ M' : MechanismN n ι,
      ∫⁻ x in A, ENNReal.ofReal (sellerRevenue M' (A.indicator id x)) ∂μ =
        ∫⁻ x in A, ENNReal.ofReal (sellerRevenue M' x) ∂μ := by
    intro M'
    refine setLIntegral_congr_fun hA fun x hx => ?_
    rw [Set.indicator_of_mem hx, id]
  constructor
  · obtain ⟨M', hM', hle, h0, -⟩ := hnorm M hM
    have h1 : ∫⁻ x in A, ENNReal.ofReal (sellerRevenue M x) ∂μ ≤ RevDS (lawOnN μ A) := by
      calc ∫⁻ x in A, ENNReal.ofReal (sellerRevenue M x) ∂μ
          ≤ ∫⁻ x in A, ENNReal.ofReal (sellerRevenue M' x) ∂μ :=
            lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hle x)
        _ = ∫⁻ x in A, ENNReal.ofReal (sellerRevenue M' (A.indicator id x)) ∂μ := (hAeq M').symm
        _ ≤ ∫⁻ x, ENNReal.ofReal (sellerRevenue M' (A.indicator id x)) ∂μ :=
            setLIntegral_le_lintegral _ _
        _ = (expRevenueN (lawOnN μ A) M').toENNReal := by rw [hrevNN _ M' h0, hlaw M' hM']
        _ ≤ RevDS (lawOnN μ A) :=
            le_iSup₂ (f := fun (M : MechanismN n ι) (_ : IsAdmissibleDS M) =>
              (expRevenueN (lawOnN μ A) M).toENNReal) M' hM'
    calc _ ≤ ((∫⁻ x in A, ENNReal.ofReal (sellerRevenue M x) ∂μ : ℝ≥0∞) : EReal) :=
          subLe _ _
      _ ≤ _ := by exact_mod_cast h1
  · refine iSup₂_le fun M hM => ?_
    obtain ⟨M', hM', hle, h0, hz⟩ := hnorm M hM
    calc (expRevenueN (lawOnN μ A) M).toENNReal
        ≤ ∫⁻ x, ENNReal.ofReal (sellerRevenue M' x) ∂(lawOnN μ A) := hrevLe _ M M' hle
      _ = ∫⁻ x, ENNReal.ofReal (sellerRevenue M' (A.indicator id x)) ∂μ := hlaw M' hM'
      _ = ∫⁻ x in A, ENNReal.ofReal (sellerRevenue M' (A.indicator id x)) ∂μ +
          ∫⁻ x in Aᶜ, ENNReal.ofReal (sellerRevenue M' (A.indicator id x)) ∂μ :=
            (lintegral_add_compl _ hA).symm
      _ = ∫⁻ x in A, ENNReal.ofReal (sellerRevenue M' x) ∂μ := by
            rw [hAeq M']
            have : ∫⁻ x in Aᶜ, ENNReal.ofReal (sellerRevenue M' (A.indicator id x)) ∂μ = 0 := by
              rw [setLIntegral_congr_fun hA.compl (g := fun _ => 0) fun x hx => by
                simp only
                rw [Set.indicator_of_notMem hx, hz, ENNReal.ofReal_zero]]
              exact lintegral_zero
            rw [this, add_zero]
      _ ≤ ∫⁻ x, ENNReal.ofReal (sellerRevenue M' x) ∂μ := setLIntegral_le_lintegral _ _
      _ = (expRevenueN μ M').toENNReal := (hrevNN _ M' h0).symm
      _ ≤ RevDS μ := le_iSup₂ (f := fun (M : MechanismN n ι) (_ : IsAdmissibleDS M) =>
              (expRevenueN μ M).toENNReal) M' hM'
