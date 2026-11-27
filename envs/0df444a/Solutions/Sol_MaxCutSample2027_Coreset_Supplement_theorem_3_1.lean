-- Prove2me | solution 1 for MaxCutSample2027.Coreset.Supplement.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:41:01.323062+00:00
-- url     : https://prove2.me/submissions/4b5c97f1-1a94-4815-a160-1ac88fbb393e

import Theorems.Thm_MaxCutSample2027_Coreset_lemma_2_4
import Theorems.Thm_MaxCutSample2027_Coreset_Supplement_lemma_3_4
import Theorems.Thm_MaxCutSample2027_Coreset_equation_2_14
import Definitions.Def_MaxCutSample2027_Coreset_Supplement_recovery
open scoped BigOperators
noncomputable section

set_option autoImplicit false

open MaxCutSample2027
open MaxCutSample2027.Coreset
open MaxCutSample2027.Coreset.Supplement

open scoped BigOperators

private def push_mass {V I : Type*} [DecidableEq V] (x : I → V) (w : I → ℝ)
    (S : Finset I) (v : V) : ℝ := ∑ i ∈ S.filter (fun i => x i = v), w i

private theorem sum_push_mass {V I : Type*} [Fintype V] [DecidableEq V] (x : I → V) (w : I → ℝ)
    (S : Finset I) (f : V → ℝ) :
    ∑ v, push_mass x w S v * f v = ∑ i ∈ S, w i * f (x i) := by
  unfold push_mass
  simp only [Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.univ) (g := x)
    (fun _ _ => Finset.mem_univ _) (fun i => w i * f (x i))]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

private theorem cut_push_mass {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (x : I → V) (w : I → ℝ) (L : V → V → ℝ) (S : Finset I) :
    bilinear L (push_mass x w S) (push_mass x w Sᶜ) =
      cutValue (fun i j => w i * L (x i) (x j) * w j) S := by
  unfold bilinear cutValue
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [sum_push_mass]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp_rw [mul_comm (L (x i) _) (push_mass x w Sᶜ _)]
  rw [sum_push_mass]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

open scoped Pointwise

private theorem box_eq_Icc {V : Type*} (q : V → ℝ) : Z q = Set.Icc 0 q := by
  ext a
  exact forall_and

private theorem box_compact {V : Type*} (q : V → ℝ) : IsCompact (Z q) := by
  rw [box_eq_Icc]
  exact isCompact_Icc

private theorem box_nonempty {V : Type*} {q : V → ℝ} (hq : ∀ v, 0 ≤ q v) : (Z q).Nonempty :=
  ⟨0, fun v => ⟨le_rfl, hq v⟩⟩

private theorem empirical_sum {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (x : Fin k → V) (f : V → ℝ) : ∑ v, empirical x v * f v = (∑ i, f (x i)) / (k : ℝ) := by
  calc
    _ = (∑ v, ((Finset.univ.filter (fun i => x i = v)).card : ℝ) * f v) / (k : ℝ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun v _ => by simp only [empirical]; ring
    _ = _ := by
      congr 1
      rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.univ) (g := x) (fun _ _ => Finset.mem_univ _) (fun i => f (x i))]
      apply Finset.sum_congr rfl
      intro v _
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]

private theorem empirical_probability {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (hk : 1 ≤ k) (x : Fin k → V) : IsProbabilityVector (empirical x) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  refine ⟨fun v => div_nonneg (Nat.cast_nonneg _) hk'.le, ?_⟩
  simpa [hk'.ne'] using empirical_sum x (fun _ => 1)

private theorem sample_le {V : Type*} [Fintype V] {k : ℕ} {p : V → ℝ}
    (hp : ∀ v, 0 ≤ p v) (f g : (Fin k → V) → ℝ) (h : ∀ x, f x ≤ g x) :
    sampleAverage p k f ≤ sampleAverage p k g := by
  unfold sampleAverage
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x)
    (Finset.prod_nonneg fun i _ => hp (x i))

private theorem sample_smul {V : Type*} [Fintype V] {k : ℕ} (p : V → ℝ)
    (a : ℝ) (f : (Fin k → V) → ℝ) : sampleAverage p k (fun x => a * f x) = a * sampleAverage p k f := by
  unfold sampleAverage
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring
private def boolCuts (V : Type*) [Fintype V] [DecidableEq V] : (V → Bool) ≃ Finset V where
  toFun σ := Finset.univ.filter fun v => σ v = true
  invFun S v := decide (v ∈ S)
  left_inv σ := by funext v; cases h : σ v <;> simp [h]
  right_inv S := by ext v; simp

private def lawBit {V : Type*} (t : V → ℝ) (v : V) (b : Bool) : ℝ := if b then t v else 1 - t v

private theorem roundingWeight_product {V : Type*} [Fintype V] [DecidableEq V]
    (p b : V → ℝ) (σ : V → Bool) : roundingWeight p b (boolCuts V σ) =
      ∏ v, lawBit (fun v => b v / p v) v (σ v) := by
  unfold roundingWeight lawBit
  rw [Finset.prod_ite]
  have h₁ : Finset.univ.filter (fun v : V => σ v = true) = boolCuts V σ := rfl
  have h₂ : Finset.univ.filter (fun v : V => ¬σ v = true) = (boolCuts V σ)ᶜ := by
    ext v
    simp [boolCuts]
  rw [h₁, h₂]

private theorem rounding_total {V : Type*} [Fintype V] [DecidableEq V] (p b : V → ℝ) :
    (∑ S : Finset V, roundingWeight p b S) = 1 := by
  rw [← Fintype.sum_equiv (boolCuts V) (fun σ => roundingWeight p b (boolCuts V σ))
    (roundingWeight p b) (fun _ => rfl)]
  simp only [roundingWeight_product]
  rw [← Fintype.prod_sum]
  have h (v : V) : ∑ s : Bool, lawBit (fun v => b v / p v) v s = 1 := by
    simp [Fintype.sum_bool, lawBit]
  simp only [h, Finset.prod_const_one]

private theorem rounding_cross {V : Type*} [Fintype V] [DecidableEq V] (p b : V → ℝ)
    (u v : V) (huv : u ≠ v) :
    (∑ S : Finset V, roundingWeight p b S * (if u ∈ S ∧ v ∉ S then 1 else 0)) =
      (b u / p u) * (1 - b v / p v) := by
  classical
  let t (x : V) := b x / p x
  let h (i : V) (s : Bool) : ℝ :=
    if i = u then (if s then t i else 0) else if i = v then (if s then 0 else 1 - t i) else lawBit t i s
  have product_event (σ : V → Bool) :
      roundingWeight p b (boolCuts V σ) * (if u ∈ boolCuts V σ ∧ v ∉ boolCuts V σ then 1 else 0) =
        ∏ i, h i (σ i) := by
    rw [roundingWeight_product]
    have mem (i : V) : i ∈ boolCuts V σ ↔ σ i = true := by simp [boolCuts]
    simp only [mem]
    by_cases hu : σ u = true
    · by_cases hv : σ v = true
      · rw [if_neg (fun h => h.2 hv), mul_zero]
        have hz : h v (σ v) = 0 := by simp [h, hv, Ne.symm huv]
        exact (Finset.prod_eq_zero (Finset.mem_univ v) hz).symm
      · rw [if_pos ⟨hu, hv⟩, mul_one]
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : i = u
        · subst i; simp [h, hu, lawBit, t]
        · by_cases hi' : i = v
          · subst i; simp [h, Ne.symm huv, hv, lawBit, t]
          · simp [h, hi, hi', lawBit, t]
    · rw [if_neg (fun h => hu h.1), mul_zero]
      have hz : h u (σ u) = 0 := by simp [h, hu]
      exact (Finset.prod_eq_zero (Finset.mem_univ u) hz).symm
  calc
    _ = ∑ σ : V → Bool, roundingWeight p b (boolCuts V σ) *
        (if u ∈ boolCuts V σ ∧ v ∉ boolCuts V σ then 1 else 0) :=
      (Fintype.sum_equiv (boolCuts V) _ _ fun _ => rfl).symm
    _ = ∑ σ : V → Bool, ∏ i, h i (σ i) := Finset.sum_congr rfl fun σ _ => product_event σ
    _ = ∏ i, ∑ j : Bool, h i j := (Fintype.prod_sum h).symm
    _ = _ := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ v), Finset.prod_eq_single u]
      · simp [h, huv, Ne.symm huv, Fintype.sum_bool, t]
      · intro i hi hiu
        simp [h, hiu, (Finset.mem_erase.mp hi).1, Fintype.sum_bool, lawBit]
      · simp [huv]

private theorem rounded_loss_exact {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p b : V → ℝ) (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p) :
    roundedLoss A p b = maxCut A / (Fintype.card V : ℝ) ^ 2 - bilinear (K A p) b (p - b) := by
  classical
  let N : ℝ := Fintype.card V
  have hN : 0 < N := by
    change 0 < (Fintype.card V : ℝ)
    exact_mod_cast Fintype.card_pos (α := V)
  have all_edges (S : Finset V) : cutValue A S =
      ∑ u, ∑ v, if u ∈ S ∧ v ∉ S then A u v else 0 := by
    unfold cutValue
    have inner (u : V) : (∑ v, if u ∈ S ∧ v ∉ S then A u v else 0) =
        if u ∈ S then ∑ v ∈ Sᶜ, A u v else 0 := by
      by_cases hu : u ∈ S
      · simp only [hu, true_and, if_true, ← Finset.sum_filter]
        have h : Finset.univ.filter (fun v => v ∉ S) = Sᶜ := by ext v; simp
        rw [h]
      · simp [hu]
    simp only [inner, ← Finset.sum_filter]
    simp
  have grouping : (∑ S : Finset V, roundingWeight p b S * cutValue A S) =
      ∑ u, ∑ v, A u v * ((b u / p u) * (1 - b v / p v)) := by
    simp only [all_edges, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : u = v
    · subst v; simp [hA.2.1]
    · rw [← rounding_cross p b u v h, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      split_ifs <;> ring
  unfold roundedLoss
  change (∑ S, roundingWeight p b S * ((maxCut A - cutValue A S) / N ^ 2)) = _
  have distribute : (∑ S, roundingWeight p b S * ((maxCut A - cutValue A S) / N ^ 2)) =
      (maxCut A - ∑ S, roundingWeight p b S * cutValue A S) / N ^ 2 := by
    simp only [← mul_div_assoc, ← Finset.sum_div, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, rounding_total, one_mul]
  rw [distribute, grouping, sub_div]
  congr 1
  unfold bilinear
  simp only [Finset.sum_div, Pi.sub_apply]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  change A u v * (b u / p u * (1 - b v / p v)) / N ^ 2 =
    b u * (A u v / (N ^ 2 * p u * p v)) * (p v - b v)
  field_simp [hN.ne', (hp.1 u).ne', (hp.1 v).ne']

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k)
    : (∀ x : Fin k → V, ∃ (S : Finset (Fin k)) (b : V → ℝ),
        AdmissibleRecovery A p x S b) ∧
      (∀ (S : (Fin k → V) → Finset (Fin k)) (b : (Fin k → V) → V → ℝ),
        (∀ x, AdmissibleRecovery A p x (S x) (b x)) →
        sampleAverage p k (fun x => roundedLoss A p (b x)) ≤
          120 * H A p / Real.sqrt (k : ℝ)) ∧
      (∀ x : Fin k → V,
        (queryEntries x).card ≤ Fintype.card V * k ∧
        ∀ (A' : V → V → ℝ), IsWeightMatrix A' →
          (∀ i v, A' (x i) v = A (x i) v) →
          ∀ (S : Finset (Fin k)) (b : V → ℝ),
            (AdmissibleRecovery A p x S b ↔ AdmissibleRecovery A' p x S b)) := by
  classical
  let N : ℝ := Fintype.card V
  have hN : 0 < N := by
    change 0 < (Fintype.card V : ℝ)
    exact_mod_cast Fintype.card_pos (α := V)
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hN2 : 0 < N ^ 2 := by positivity
  let L := K A p
  have fraction (x : Fin k → V) (S : Finset (Fin k)) :
      inducedFraction x S = push_mass x (fun _ => 1 / (k : ℝ)) S := by
    funext v
    simp only [inducedFraction, push_mass, Finset.sum_const, nsmul_eq_mul, mul_one_div]
  have split_mass (x : Fin k → V) (S : Finset (Fin k)) :
      empirical x - inducedFraction x S = inducedFraction x Sᶜ := by
    funext v
    change empirical x v - inducedFraction x S v = inducedFraction x Sᶜ v
    apply sub_eq_of_eq_add
    simp only [empirical, inducedFraction, ← add_div, ← Nat.cast_add]
    have dis : Disjoint Sᶜ S := by
      rw [Finset.disjoint_left]
      exact fun i hi hs => (Finset.mem_compl.mp hi) hs
    rw [← Finset.card_union_of_disjoint (dis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      ← Finset.filter_union, Finset.union_comm Sᶜ S, Finset.union_compl]
  have feasible (x : Fin k → V) (S : Finset (Fin k)) : inducedFraction x S ∈ Z (empirical x) := by
    intro v
    have h₁ : 0 ≤ inducedFraction x S v := div_nonneg (Nat.cast_nonneg _) hk'.le
    have h₂ : 0 ≤ inducedFraction x Sᶜ v := div_nonneg (Nat.cast_nonneg _) hk'.le
    have h₃ : empirical x v - inducedFraction x S v = inducedFraction x Sᶜ v := congrFun (split_mass x S) v
    exact ⟨h₁, by linarith⟩
  have sample_value (x : Fin k → V) (S : Finset (Fin k)) :
      bilinear L (inducedFraction x S) (empirical x - inducedFraction x S) = cutValue (Ahat A p x) S / N ^ 2 := by
    rw [split_mass, fraction, fraction, cut_push_mass]
    unfold cutValue
    simp only [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change (1 / (k : ℝ)) * (A (x i) (x j) / (N ^ 2 * p (x i) * p (x j))) * (1 / (k : ℝ)) =
      (A (x i) (x j) / ((k : ℝ) ^ 2 * p (x i) * p (x j))) / N ^ 2
    field_simp [hN.ne', hk'.ne', (hp.1 (x i)).ne', (hp.1 (x j)).ne']
  have attained (x : Fin k → V) (S : Finset (Fin k)) (hS : cutValue (Ahat A p x) S = maxCut (Ahat A p x)) :
      bilinear L (inducedFraction x S) (empirical x - inducedFraction x S) = FK L (empirical x) := by
    rw [sample_value, hS, (lemma_2_4 A p hA hp k hk x).2]
  refine ⟨?_, ?_, ?_⟩
  · intro x
    obtain ⟨S, _, hS⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty : (Finset.univ : Finset (Finset (Fin k))).Nonempty)
      (cutValue (Ahat A p x))
    have hcont : Continuous (fun b => recoveryError L x (inducedFraction x S) b) := by
      unfold recoveryError matVec
      fun_prop
    obtain ⟨b, hb, hbmin⟩ := (box_compact p).exists_isMinOn
      (box_nonempty (fun v => (hp.1 v).le)) hcont.continuousOn
    exact ⟨S, b, hS.symm, hb, fun c hc => hbmin hc⟩
  · intro S b hadm
    have bound (x : Fin k → V) : roundedLoss A p (b x) ≤ 10 * DeltaK L p (empirical x) := by
      obtain ⟨hx, hb, hmin⟩ := hadm x
      have recovery := lemma_3_4 A p hA hp k hk x (inducedFraction x (S x)) (feasible x (S x))
        (attained x (S x) hx) (b x) hb hmin
      rw [rounded_loss_exact A p (b x) hA hp, ← (lemma_2_4 A p hA hp k hk x).1]
      linarith
    calc
      _ ≤ sampleAverage p k (fun x => 10 * DeltaK L p (empirical x)) := sample_le (fun v => (hp.1 v).le) _ _ bound
      _ = 10 * sampleAverage p k (fun x => DeltaK L p (empirical x)) := sample_smul _ _ _
      _ ≤ 10 * (12 * H A p / Real.sqrt (k : ℝ)) := mul_le_mul_of_nonneg_left (equation_2_14 A p hA hp k hk) (by norm_num)
      _ = _ := by ring
  · intro x
    constructor
    · unfold queryEntries
      calc
        _ ≤ ∑ _i : Fin k, Fintype.card V := by
          refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => ?_)
          exact Finset.card_image_le.trans_eq (Finset.card_univ)
        _ = _ := by simp [mul_comm]
    · intro A' _ hrow S b
      have hat : Ahat A p x = Ahat A' p x := by
        funext i j
        simp only [Ahat, hrow i (x j)]
      have error (c : V → ℝ) : recoveryError (K A p) x (inducedFraction x S) c =
          recoveryError (K A' p) x (inducedFraction x S) c := by
        unfold recoveryError matVec K
        simp only [hrow]
      unfold AdmissibleRecovery
      simp only [hat, error]
