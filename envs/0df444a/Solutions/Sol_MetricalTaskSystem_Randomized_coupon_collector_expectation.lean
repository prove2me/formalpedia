-- Prove2me | solution 1 for MetricalTaskSystem.Randomized.coupon_collector_expectation
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T10:25:02.259761+00:00
-- url     : https://prove2.me/submissions/2931bed1-b13b-46a9-b008-dafc6652510d

import Definitions.Def_MetricalTaskSystem_Randomized_Model
import Definitions.Def_MetricalTaskSystem_Randomized_TaskDistribution

open MetricalTaskSystem.Randomized
open MeasureTheory Filter
open scoped ENNReal

private lemma integral_uniformStateSeq_fin {S : Type} [Fintype S] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (j : ℕ) (g : (Fin j → S) → ℝ) :
    ∫ ω, g (fun i : Fin j => ω i) ∂(uniformStateSeq S) =
      ((Fintype.card S : ℝ)⁻¹ ^ j) * ∑ v : (Fin j → S), g v := by
  let μ₀ : Measure S := (PMF.uniformOfFintype S).toMeasure
  let I : Finset ℕ := Finset.range j
  let equivRange : (I → S) ≃ (Fin j → S) :=
    { toFun := fun y i => y ⟨i.val, Finset.mem_range.mpr i.isLt⟩
      invFun := fun v k => v ⟨k.val, Finset.mem_range.mp k.2⟩
      left_inv := fun y => by ext k; rfl
      right_inv := fun v => by ext i; rfl }
  have hcongr : (fun ω : ℕ → S => g (fun i : Fin j => ω i)) =
      (fun ω : ℕ → S => g (equivRange (I.restrict ω))) := rfl
  rw [hcongr]
  change (∫ ω : ℕ → S, (fun y : I → S => g (equivRange y)) (I.restrict ω)
    ∂Measure.infinitePi (fun _ : ℕ => μ₀)) = _
  have hmeas : AEStronglyMeasurable (fun y : I → S => g (equivRange y))
      (Measure.pi (fun _ : I => μ₀)) :=
    (Measurable.of_discrete (f := fun y : I → S => g (equivRange y))).aestronglyMeasurable
  rw [integral_restrict_infinitePi (fun _ : ℕ => μ₀) hmeas]
  rw [integral_fintype (Integrable.of_finite)]
  have hreal_singleton : ∀ y : I → S,
      (Measure.pi (fun _ : I => μ₀)).real {y} = ((Fintype.card S : ℝ)⁻¹) ^ j := by
    intro y
    unfold Measure.real
    have hsing : ({y} : Set (I → S)) = Set.univ.pi (fun i : I => {y i}) :=
      (Set.univ_pi_singleton y).symm
    rw [hsing, Measure.pi_pi]
    have hμ₀ : ∀ i : I, μ₀ {y i} = (Fintype.card S : ℝ≥0∞)⁻¹ := by
      intro i
      dsimp [μ₀]
      rw [PMF.toMeasure_apply_singleton _ (y i) (measurableSet_singleton (y i)),
          PMF.uniformOfFintype_apply]
    simp_rw [hμ₀]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, Finset.card_range,
        ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp_rw [smul_eq_mul, hreal_singleton, ← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp equivRange g

private lemma lintegral_ofReal_uniformStateSeq_fin {S : Type} [Fintype S] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (j : ℕ) (g : (Fin j → S) → ℝ) (hg0 : ∀ v, 0 ≤ g v) (hg1 : ∀ v, g v ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (g (fun i : Fin j => ω i)) ∂(uniformStateSeq S) =
      ENNReal.ofReal (((Fintype.card S : ℝ)⁻¹ ^ j) * ∑ v : (Fin j → S), g v) := by
  have _ : IsProbabilityMeasure (uniformStateSeq S) := by
    unfold uniformStateSeq
    infer_instance
  let proj : (ℕ → S) → (Fin j → S) := fun ω i => ω i
  have hmeas_proj : Measurable proj :=
    measurable_pi_lambda _ (fun i : Fin j => measurable_pi_apply i.val)
  have hmeas_g : Measurable (fun ω : ℕ → S => g (proj ω)) :=
    (Measurable.of_discrete (f := g)).comp hmeas_proj
  have hint : Integrable (fun ω : ℕ → S => g (proj ω)) (uniformStateSeq S) :=
    Integrable.of_bound hmeas_g.aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (hg0 (proj ω))]
        exact hg1 (proj ω))
  rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun ω => hg0 (proj ω)),
      integral_uniformStateSeq_fin j g]

open Classical in
private noncomputable def notAllSeen {S : Type} (k : ℕ) (ω : ℕ → S) : ENNReal :=
  if ∀ s : S, ∃ i < k, ω i = s then 0 else 1

open Classical in
private lemma collectTime_eq_tsum {S : Type} (ω : ℕ → S) :
    collectTime ω = ∑' k : ℕ, notAllSeen k ω := by
  let P (k : ℕ) : Prop := ∀ s : S, ∃ i < k, ω i = s
  have hP_mono : ∀ {k₁ k₂ : ℕ}, k₁ ≤ k₂ → P k₁ → P k₂ := by
    intro k₁ k₂ hle hk₁ s
    obtain ⟨i, hi, hω⟩ := hk₁ s
    exact ⟨i, lt_of_lt_of_le hi hle, hω⟩
  unfold notAllSeen
  change collectTime ω = ∑' k : ℕ, (if P k then (0 : ENNReal) else 1)
  by_cases hex : ∃ k : ℕ, P k
  · let m : ℕ := Nat.find hex
    have hm_spec : P m := Nat.find_spec hex
    have hm_min : ∀ k : ℕ, P k → m ≤ k := fun k hk => Nat.find_min' hex hk
    have hct : collectTime ω = (m : ENNReal) := by
      unfold collectTime
      refine le_antisymm ?_ ?_
      · exact iInf₂_le m hm_spec
      · refine le_iInf₂ fun k hk => ?_
        exact Nat.cast_le.mpr (hm_min k hk)
    rw [hct, tsum_eq_sum (s := Finset.range m)]
    · have hsum : (∑ k ∈ Finset.range m, (if P k then (0 : ENNReal) else 1)) =
          ∑ _k ∈ Finset.range m, (1 : ENNReal) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hnot : ¬ P k := Nat.find_min hex (Finset.mem_range.mp hk)
        rw [if_neg hnot]
      rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    · intro k hk
      have hge : m ≤ k := not_lt.mp ( mt Finset.mem_range.mpr hk )
      rw [if_pos (hP_mono hge hm_spec)]
  · have hno : ∀ k : ℕ, ¬ P k := fun k hk => hex ⟨k, hk⟩
    have hct : collectTime ω = ⊤ := by
      unfold collectTime
      simp [P] at hno
      simp [hno]
    simp_rw [if_neg (hno _)]
    rw [hct, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]

open Classical in
private noncomputable def seenVec {S : Type} {k : ℕ} (v : Fin k → S) : Finset S :=
  Finset.univ.image v

open Classical in
private noncomputable def leVec {S : Type} (r : ℕ) {k : ℕ} (v : Fin k → S) : ℝ :=
  if (seenVec v).card ≤ r then 1 else 0

open Classical in
private noncomputable def eqVec {S : Type} (r : ℕ) {k : ℕ} (v : Fin k → S) : ℝ :=
  if (seenVec v).card = r then 1 else 0

private def snocFun {S : Type} {k : ℕ} (v : Fin k → S) (x : S) (i : Fin (k + 1)) : S :=
  if h : i.val < k then v ⟨i.val, h⟩ else x

private def snocEquiv {S : Type} (k : ℕ) : (Fin k → S) × S ≃ (Fin (k + 1) → S) where
  toFun p := snocFun p.1 p.2
  invFun w := (fun i => w i.castSucc, w (Fin.last k))
  left_inv := by
    rintro ⟨v, x⟩
    ext i
    · simp [snocFun, i.isLt]
    · simp [snocFun, Fin.last]
  right_inv := by
    intro w
    ext i
    dsimp [snocFun]
    split_ifs with h
    · rfl
    · have hi : i = Fin.last k := Fin.ext (by dsimp [Fin.last]; omega)
      rw [hi]

open Classical in
private lemma seenVec_snocFun {S : Type} {k : ℕ} (v : Fin k → S) (x : S) :
    seenVec (snocFun v x) = insert x (seenVec v) := by
  ext s
  simp only [seenVec, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨i, rfl⟩
    dsimp [snocFun]
    split_ifs with h
    · exact Or.inr ⟨⟨i.val, h⟩, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨j, rfl⟩)
    · refine ⟨Fin.last k, ?_⟩
      simp [snocFun, Fin.last]
    · refine ⟨j.castSucc, ?_⟩
      simp [snocFun, j.isLt]

open Classical in
private lemma leVec_sub_snocFun {S : Type} {k : ℕ} (r : ℕ) (v : Fin k → S) (x : S) :
    leVec r v - leVec r (snocFun v x) =
      eqVec r v * (if x ∉ seenVec v then (1 : ℝ) else 0) := by
  unfold leVec eqVec
  rw [seenVec_snocFun]
  by_cases hx : x ∈ seenVec v
  · rw [Finset.insert_eq_of_mem hx, if_neg (not_not.mpr hx), mul_zero, sub_self]
  · rw [Finset.card_insert_of_notMem hx, if_pos hx, mul_one]
    by_cases hle : (seenVec v).card ≤ r
    · by_cases heq : (seenVec v).card = r
      · have hnot : ¬ ((seenVec v).card + 1 ≤ r) := by omega
        rw [if_pos hle, if_neg hnot, if_pos heq, sub_zero]
      · have hle' : (seenVec v).card + 1 ≤ r := by omega
        rw [if_pos hle, if_pos hle', if_neg heq, sub_self]
    · have hnot : ¬ ((seenVec v).card + 1 ≤ r) := by omega
      have hne : (seenVec v).card ≠ r := by omega
      rw [if_neg hle, if_neg hnot, if_neg hne, sub_self]

open Classical in
private lemma sum_notMem_finset {S : Type} [Fintype S] (A : Finset S) :
    (∑ x : S, (if x ∉ A then (1 : ℝ) else 0)) = (Fintype.card S : ℝ) - (A.card : ℝ) := by
  have h1 : ∀ x : S, (if x ∉ A then (1 : ℝ) else 0) = 1 - (if x ∈ A then (1 : ℝ) else 0) := by
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  simp_rw [h1]
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_const, Finset.card_univ]

open Classical in
private noncomputable def probLe (S : Type) [Fintype S] (k r : ℕ) : ℝ :=
  ((Fintype.card S : ℝ)⁻¹ ^ k) * ∑ v : (Fin k → S), leVec r v

open Classical in
private noncomputable def probEq (S : Type) [Fintype S] (k r : ℕ) : ℝ :=
  ((Fintype.card S : ℝ)⁻¹ ^ k) * ∑ v : (Fin k → S), eqVec r v

open Classical in
private lemma probLe_sub_succ {S : Type} [Fintype S] [Nonempty S] (k r : ℕ) :
    probLe S k r - probLe S (k + 1) r =
      (((Fintype.card S : ℝ) - (r : ℝ)) / (Fintype.card S : ℝ)) * probEq S k r := by
  let n : ℝ := (Fintype.card S : ℝ)
  have hn_pos : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hn_ne : n ≠ 0 := ne_of_gt hn_pos
  have hsum_w : (∑ w : (Fin (k + 1) → S), leVec r w) =
      ∑ v : (Fin k → S), ∑ x : S, leVec r (snocFun v x) := by
    rw [← Equiv.sum_comp (snocEquiv k) (leVec r), Fintype.sum_prod_type]
    rfl
  have hstep_v : ∀ v : (Fin k → S),
      n * leVec r v - ∑ x : S, leVec r (snocFun v x) = (n - (r : ℝ)) * eqVec r v := by
    intro v
    have hconst : n * leVec r v = ∑ _x : S, leVec r v := by
      simp [n, Finset.sum_const, Finset.card_univ]
    rw [hconst, ← Finset.sum_sub_distrib]
    simp_rw [leVec_sub_snocFun, ← Finset.mul_sum, sum_notMem_finset]
    unfold eqVec
    split_ifs with heq
    · rw [heq]; ring
    · ring
  have hsum_all :
      n * (∑ v : (Fin k → S), leVec r v) - (∑ w : (Fin (k + 1) → S), leVec r w) =
        (n - (r : ℝ)) * (∑ v : (Fin k → S), eqVec r v) := by
    rw [hsum_w, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => hstep_v v
  unfold probLe probEq
  change (n⁻¹ ^ k) * (∑ v : (Fin k → S), leVec r v) -
      (n⁻¹ ^ (k + 1)) * (∑ w : (Fin (k + 1) → S), leVec r w) =
    ((n - (r : ℝ)) / n) * ((n⁻¹ ^ k) * (∑ v : (Fin k → S), eqVec r v))
  have hpow : n⁻¹ ^ (k + 1) = (n⁻¹ ^ k) * n⁻¹ := pow_succ n⁻¹ k
  rw [hpow]
  calc (n⁻¹ ^ k) * (∑ v : (Fin k → S), leVec r v) -
        ((n⁻¹ ^ k) * n⁻¹) * (∑ w : (Fin (k + 1) → S), leVec r w)
      = ((n⁻¹ ^ k) * n⁻¹) *
          (n * (∑ v : (Fin k → S), leVec r v) - (∑ w : (Fin (k + 1) → S), leVec r w)) := by
        have h_inv : n⁻¹ * n = 1 := inv_mul_cancel₀ hn_ne
        linear_combination -(n⁻¹ ^ k) * (∑ v : (Fin k → S), leVec r v) * h_inv
    _ = ((n⁻¹ ^ k) * n⁻¹) * ((n - (r : ℝ)) * (∑ v : (Fin k → S), eqVec r v)) := by
        rw [hsum_all]
    _ = ((n - (r : ℝ)) / n) * ((n⁻¹ ^ k) * (∑ v : (Fin k → S), eqVec r v)) := by
        ring

open Classical in
private lemma sum_probEq_range {S : Type} [Fintype S] [Nonempty S] (K r : ℕ)
    (hr : r < Fintype.card S) :
    ∑ k ∈ Finset.range K, probEq S k r =
      ((Fintype.card S : ℝ) / ((Fintype.card S : ℝ) - (r : ℝ))) * (1 - probLe S K r) := by
  let n : ℝ := (Fintype.card S : ℝ)
  have hr_real : (r : ℝ) < n := Nat.cast_lt.mpr hr
  have hdiff_ne : n - (r : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hr_real)
  have hn_ne : n ≠ 0 := ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  have htel : ∑ k ∈ Finset.range K, (probLe S k r - probLe S (k + 1) r) =
      probLe S 0 r - probLe S K r :=
    Finset.sum_range_sub' (fun k => probLe S k r) K
  simp_rw [probLe_sub_succ, ← Finset.mul_sum] at htel
  have h0 : probLe S 0 r = 1 := by
    unfold probLe leVec seenVec
    simp
  rw [h0] at htel
  change ∑ k ∈ Finset.range K, probEq S k r = (n / (n - (r : ℝ))) * (1 - probLe S K r)
  calc ∑ k ∈ Finset.range K, probEq S k r
      = (n / (n - (r : ℝ))) *
          (((n - (r : ℝ)) / n) * ∑ k ∈ Finset.range K, probEq S k r) := by
        field_simp
    _ = (n / (n - (r : ℝ))) * (1 - probLe S K r) := by
        rw [htel]

open Classical in
private lemma probLe_bounds {S : Type} [Fintype S] [Nonempty S] (K r : ℕ)
    (hr : r < Fintype.card S) :
    0 ≤ probLe S K r ∧
      probLe S K r ≤
        (Fintype.card S : ℝ) * (((Fintype.card S : ℝ) - 1) / (Fintype.card S : ℝ)) ^ K := by
  let n : ℝ := (Fintype.card S : ℝ)
  have hn_pos : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨?_, ?_⟩
  · unfold probLe leVec
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun v _ => ?_)
    split_ifs <;> norm_num
  · have hle_v : ∀ v : (Fin K → S),
        leVec r v ≤ ∑ s : S, ∏ i : Fin K, (if v i ≠ s then (1 : ℝ) else 0) := by
      intro v
      have hterm_nonneg : ∀ s : S,
          0 ≤ ∏ i : Fin K, (if v i ≠ s then (1 : ℝ) else 0) := by
        intro s
        refine Finset.prod_nonneg fun i _ => ?_
        split_ifs <;> norm_num
      unfold leVec
      split_ifs with hcard
      · have hne_univ : seenVec v ≠ Finset.univ := by
          intro heq
          have hc : (seenVec v).card = Fintype.card S := by rw [heq, Finset.card_univ]
          omega
        have hex_not : ∃ s : S, s ∉ seenVec v := by
          by_contra hall
          push Not at hall
          exact hne_univ (Finset.eq_univ_iff_forall.mpr hall)
        obtain ⟨s₀, hs₀⟩ := hex_not
        have hprod_one : (∏ i : Fin K, (if v i ≠ s₀ then (1 : ℝ) else 0)) = 1 := by
          refine Finset.prod_eq_one fun i _ => ?_
          have hne : v i ≠ s₀ := by
            intro heq
            apply hs₀
            simp only [seenVec, Finset.mem_image, Finset.mem_univ, true_and]
            exact ⟨i, heq⟩
          rw [if_pos hne]
        have hle_single := Finset.single_le_sum (fun s _ => hterm_nonneg s) (Finset.mem_univ s₀)
        rw [hprod_one] at hle_single
        exact hle_single
      · exact Finset.sum_nonneg fun s _ => hterm_nonneg s
    have hsum_s : ∀ s : S,
        (∑ v : (Fin K → S), ∏ i : Fin K, (if v i ≠ s then (1 : ℝ) else 0)) =
          (n - 1) ^ K := by
      intro s
      rw [← Fintype.prod_sum (fun (_ : Fin K) (x : S) => if x ≠ s then (1 : ℝ) else 0)]
      have h_inner : (∑ x : S, (if x ≠ s then (1 : ℝ) else 0)) = n - 1 := by
        have hsing : ({s} : Finset S).card = 1 := Finset.card_singleton s
        have h := sum_notMem_finset ({s} : Finset S)
        simp only [Finset.mem_singleton, hsing, Nat.cast_one] at h
        exact h
      rw [Finset.prod_const, h_inner, Finset.card_univ, Fintype.card_fin]
    unfold probLe
    change (n⁻¹ ^ K) * (∑ v : (Fin K → S), leVec r v) ≤ n * ((n - 1) / n) ^ K
    calc (n⁻¹ ^ K) * (∑ v : (Fin K → S), leVec r v)
        ≤ (n⁻¹ ^ K) * ∑ v : (Fin K → S),
            ∑ s : S, ∏ i : Fin K, (if v i ≠ s then (1 : ℝ) else 0) := by
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => hle_v v) (by positivity)
      _ = (n⁻¹ ^ K) * ∑ s : S,
            ∑ v : (Fin K → S), ∏ i : Fin K, (if v i ≠ s then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
      _ = (n⁻¹ ^ K) * ∑ _s : S, (n - 1) ^ K := by
          simp_rw [hsum_s]
      _ = (n⁻¹ ^ K) * (n * (n - 1) ^ K) := by
          simp [n, Finset.sum_const, Finset.card_univ]
      _ = n * ((n - 1) / n) ^ K := by
          rw [div_eq_mul_inv, mul_pow, mul_comm ((n - 1) ^ K), ← mul_assoc,
              mul_comm (n⁻¹ ^ K) n, mul_assoc]

open Classical in
private lemma tendsto_probLe_zero {S : Type} [Fintype S] [Nonempty S] (r : ℕ)
    (hr : r < Fintype.card S) :
    Tendsto (fun K => probLe S K r) atTop (nhds 0) := by
  let n : ℝ := (Fintype.card S : ℝ)
  have hn_pos : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hn_ge_one : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr Fintype.card_pos
  have h_ratio_nonneg : 0 ≤ (n - 1) / n := div_nonneg (by linarith) (le_of_lt hn_pos)
  have h_ratio_lt_one : (n - 1) / n < 1 := (div_lt_iff₀ hn_pos).mpr (by linarith)
  have h_pow : Tendsto (fun K : ℕ => ((n - 1) / n) ^ K) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h_ratio_nonneg h_ratio_lt_one
  have h_upper : Tendsto (fun K : ℕ => n * ((n - 1) / n) ^ K) atTop (nhds 0) := by
    simpa [mul_zero] using h_pow.const_mul n
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_upper
    (fun K => (probLe_bounds K r hr).1) (fun K => (probLe_bounds K r hr).2)

open Classical in
private lemma sum_eqVec_range {S : Type} [Fintype S] {k : ℕ} (v : Fin k → S) :
    ∑ r ∈ Finset.range (Fintype.card S), eqVec r v =
      if (seenVec v).card < Fintype.card S then 1 else 0 := by
  unfold eqVec
  by_cases hlt : (seenVec v).card < Fintype.card S
  · rw [if_pos hlt]
    have hmem : (seenVec v).card ∈ Finset.range (Fintype.card S) := Finset.mem_range.mpr hlt
    rw [Finset.sum_ite_eq (Finset.range (Fintype.card S)) (seenVec v).card (fun _ => (1 : ℝ)),
        if_pos hmem]
  · rw [if_neg hlt]
    refine Finset.sum_eq_zero fun r hr => ?_
    have hr_lt : r < Fintype.card S := Finset.mem_range.mp hr
    have hne : (seenVec v).card ≠ r := by omega
    rw [if_neg hne]

open Classical in
private lemma card_seenVec_lt_iff {S : Type} [Fintype S] {k : ℕ} (ω : ℕ → S) :
    (seenVec (fun i : Fin k => ω i)).card < Fintype.card S ↔
      ¬ (∀ s : S, ∃ i < k, ω i = s) := by
  have hall_iff : (∀ s : S, ∃ i < k, ω i = s) ↔
      seenVec (fun i : Fin k => ω i) = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    refine forall_congr' fun s => ?_
    simp only [seenVec, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.isLt, rfl⟩
  rw [hall_iff, ← Finset.card_eq_iff_eq_univ]
  have hle : (seenVec (fun i : Fin k => ω i)).card ≤ Fintype.card S :=
    Finset.card_le_univ _
  omega

private lemma sum_div_sub_eq_mul_harmonic (n : ℕ) :
    ∑ r ∈ Finset.range n, (n : ℝ) / ((n : ℝ) - (r : ℝ)) =
      (n : ℝ) * (harmonic n : ℝ) := by
  have hreflect := Finset.sum_range_reflect (fun m : ℕ => (n : ℝ) / ((m + 1 : ℕ) : ℝ)) n
  have hcongr : ∑ r ∈ Finset.range n, (n : ℝ) / ((n : ℝ) - (r : ℝ)) =
      ∑ r ∈ Finset.range n, (n : ℝ) / ((n - 1 - r + 1 : ℕ) : ℝ) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr_lt : r < n := Finset.mem_range.mp hr
    have hnat : n - 1 - r + 1 = n - r := by omega
    rw [hnat, Nat.cast_sub (le_of_lt hr_lt)]
  rw [hcongr, hreflect]
  unfold harmonic
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

theorem solution {S : Type} [Fintype S] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S] :
    ∫⁻ ω, collectTime ω ∂(uniformStateSeq S) =
      ENNReal.ofReal ((Fintype.card S : ℝ) * (harmonic (Fintype.card S) : ℝ)) := by
  classical
  let n : ℕ := Fintype.card S
  simp_rw [collectTime_eq_tsum]
  have hmeas_term : ∀ k : ℕ, Measurable (notAllSeen (S := S) k) := by
    intro k
    let g : (Fin k → S) → ENNReal := fun v =>
      if (seenVec v).card < n then 1 else 0
    have hcongr : notAllSeen (S := S) k = fun ω : ℕ → S => g (fun i : Fin k => ω i) := by
      ext ω
      dsimp [notAllSeen, g, n]
      by_cases h : ∀ s : S, ∃ i < k, ω i = s
      · have hnot : ¬ ((seenVec (fun i : Fin k => ω i)).card < Fintype.card S) :=
          mt (card_seenVec_lt_iff ω).mp (not_not.mpr h)
        rw [if_pos h, if_neg hnot]
      · have hlt : (seenVec (fun i : Fin k => ω i)).card < Fintype.card S :=
          (card_seenVec_lt_iff ω).mpr h
        rw [if_neg h, if_pos hlt]
    rw [hcongr]
    exact (Measurable.of_discrete (f := g)).comp
      (measurable_pi_lambda _ (fun i : Fin k => measurable_pi_apply i.val))
  rw [lintegral_tsum (fun k => (hmeas_term k).aemeasurable)]
  let a (k : ℕ) : ℝ := ∑ r ∈ Finset.range n, probEq S k r
  have ha_nonneg : ∀ k : ℕ, 0 ≤ a k := by
    intro k
    refine Finset.sum_nonneg fun r _ => ?_
    unfold probEq eqVec
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun v _ => ?_)
    split_ifs <;> norm_num
  have hterm_eq : ∀ k : ℕ,
      (∫⁻ ω, notAllSeen k ω ∂(uniformStateSeq S)) = ENNReal.ofReal (a k) := by
    intro k
    let g : (Fin k → S) → ℝ := fun v => if (seenVec v).card < n then 1 else 0
    have hcongr : notAllSeen (S := S) k =
        fun ω : ℕ → S => ENNReal.ofReal (g (fun i : Fin k => ω i)) := by
      ext ω
      dsimp [notAllSeen, g, n]
      by_cases h : ∀ s : S, ∃ i < k, ω i = s
      · have hnot : ¬ ((seenVec (fun i : Fin k => ω i)).card < Fintype.card S) :=
          mt (card_seenVec_lt_iff ω).mp (not_not.mpr h)
        rw [if_pos h, if_neg hnot, ENNReal.ofReal_zero]
      · have hlt : (seenVec (fun i : Fin k => ω i)).card < Fintype.card S :=
          (card_seenVec_lt_iff ω).mpr h
        rw [if_neg h, if_pos hlt, ENNReal.ofReal_one]
    simp_rw [hcongr]
    rw [lintegral_ofReal_uniformStateSeq_fin k g
          (fun v => by dsimp [g]; split_ifs <;> norm_num)
          (fun v => by dsimp [g]; split_ifs <;> norm_num)]
    congr 1
    dsimp [a, probEq, g, n]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun v _ => (sum_eqVec_range v).symm
  simp_rw [hterm_eq]
  have h_tendsto : Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, a k) atTop
      (nhds (∑ r ∈ Finset.range n, (n : ℝ) / ((n : ℝ) - (r : ℝ)))) := by
    have hswap : ∀ K : ℕ,
        ∑ k ∈ Finset.range K, a k =
          ∑ r ∈ Finset.range n, ∑ k ∈ Finset.range K, probEq S k r := by
      intro K
      dsimp [a]
      exact Finset.sum_comm
    simp_rw [hswap]
    refine tendsto_finsetSum (Finset.range n) fun r hr => ?_
    have hr_lt : r < Fintype.card S := Finset.mem_range.mp hr
    simp_rw [sum_probEq_range _ r hr_lt]
    have h1 : Tendsto (fun K : ℕ => 1 - probLe S K r) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_probLe_zero r hr_lt)
    simpa [sub_zero, mul_one, n] using
      h1.const_mul ((Fintype.card S : ℝ) / ((Fintype.card S : ℝ) - (r : ℝ)))
  have h_hasSum : HasSum a (∑ r ∈ Finset.range n, (n : ℝ) / ((n : ℝ) - (r : ℝ))) :=
    (hasSum_iff_tendsto_nat_of_nonneg ha_nonneg _).mpr h_tendsto
  rw [← ENNReal.ofReal_tsum_of_nonneg ha_nonneg h_hasSum.summable,
      h_hasSum.tsum_eq, sum_div_sub_eq_mul_harmonic n]
