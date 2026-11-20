-- Prove2me | solution 1 for LinearChoresCLS.lemma_7_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T20:54:00.693295+00:00
-- url     : https://prove2.me/submissions/3114bc44-58aa-4662-8321-3c6cd68d05ae

import Mathlib
import Definitions.Def_LinearChoresCLS_CompletedMarket

open Finset NetworkEquilibriumCLS.LinearNash LinearChoresCLS

namespace CEAux

variable {N M : Type*} [Fintype N] [Fintype M] [DecidableEq M]

/-- Strict positivity of a market's data. -/
structure Pos (F : ChoresMarket N M) : Prop where
  d : ∀ a j, 0 < F.disutil a j
  B : ∀ a, 0 < F.earn a
  S : ∀ j, 0 < F.supply j

lemma used_exists {F : ChoresMarket N M} (hF : Pos F) {p : M → ℝ} {z : N → M → ℝ}
    (hCE : F.IsCE p z) (j : M) : ∃ a, 0 < z a j := by
  by_contra h
  push Not at h
  have h1 : ∑ a, z a j ≤ 0 := Finset.sum_nonpos (fun a _ => h a)
  rw [hCE.2.2.2 j] at h1
  exact absurd (hF.S j) (not_lt.mpr h1)

lemma earn_eq {F : ChoresMarket N M} (hF : Pos F) {p : M → ℝ} {z : N → M → ℝ}
    (hCE : F.IsCE p z) (a : N) : ∑ j, p j * z a j = F.earn a := by
  obtain ⟨hp, hz, hd, -⟩ := hCE
  obtain ⟨hy0, hyB, hymin⟩ := hd a
  by_contra hne
  have hgt : F.earn a < ∑ j, p j * z a j := lt_of_le_of_ne hyB (Ne.symm hne)
  set T := ∑ j, p j * z a j with hTdef
  have hT : 0 < T := lt_trans (hF.B a) hgt
  set c := F.earn a / T with hcdef
  have hc0 : 0 < c := div_pos (hF.B a) hT
  have hc1 : c < 1 := (div_lt_one hT).mpr hgt
  have hfeas : F.earn a ≤ ∑ j, p j * (c * z a j) := by
    have : ∑ j, p j * (c * z a j) = c * T := by
      rw [hTdef, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [this, hcdef, div_mul_cancel₀ _ hT.ne']
  have hmin := hymin (fun j => c * z a j) (fun j => mul_nonneg hc0.le (hy0 j)) hfeas
  have hscale : ∑ j, F.disutil a j * (c * z a j) = c * ∑ j, F.disutil a j * z a j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hscale] at hmin
  obtain ⟨j, hj⟩ : ∃ j, 0 < z a j := by
    by_contra h
    push Not at h
    have : T ≤ 0 := Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hp j) (h j))
    linarith
  have hD : 0 < ∑ j, F.disutil a j * z a j := by
    have h1 : F.disutil a j * z a j ≤ ∑ j, F.disutil a j * z a j :=
      Finset.single_le_sum (f := fun j => F.disutil a j * z a j)
        (fun i _ => mul_nonneg (hF.d a i).le (hy0 i)) (Finset.mem_univ j)
    have h2 : 0 < F.disutil a j * z a j := mul_pos (hF.d a j) hj
    linarith
  nlinarith

lemma price_pos {F : ChoresMarket N M} (hF : Pos F) {p : M → ℝ} {z : N → M → ℝ}
    (hCE : F.IsCE p z) (j : M) : 0 < p j := by
  obtain ⟨a, ha⟩ := used_exists hF hCE j
  obtain ⟨hp, hz, hd, -⟩ := hCE
  by_contra h
  have hp0 : p j = 0 := le_antisymm (not_lt.mp h) (hp j)
  obtain ⟨hy0, hyB, hymin⟩ := hd a
  let y' : M → ℝ := fun i => z a i - if i = j then z a j else 0
  have hy'0 : ∀ i, 0 ≤ y' i := by
    intro i
    simp only [y']
    split_ifs with hi
    · subst hi; simp
    · simpa using hy0 i
  have hsum : ∀ g : M → ℝ, ∑ i, g i * y' i = ∑ i, g i * z a i - g j * z a j := by
    intro g
    simp only [y', mul_sub, Finset.sum_sub_distrib]
    congr 1
    simp [mul_ite]
  have hfeas : F.earn a ≤ ∑ i, p i * y' i := by
    rw [hsum, hp0, zero_mul, sub_zero]; exact hyB
  have hmin := hymin y' hy'0 hfeas
  rw [hsum] at hmin
  have := mul_pos (hF.d a j) ha
  linarith

lemma optimal {F : ChoresMarket N M} (hF : Pos F) {p : M → ℝ} {z : N → M → ℝ}
    (hCE : F.IsCE p z) {a : N} {ℓ : M} (hℓ : 0 < z a ℓ) (j : M) :
    p j / F.disutil a j ≤ p ℓ / F.disutil a ℓ := by
  have hpj := price_pos hF hCE j
  have hpl := price_pos hF hCE ℓ
  have hdj := hF.d a j
  have hdl := hF.d a ℓ
  obtain ⟨hp, hz, hd, -⟩ := hCE
  obtain ⟨hy0, hyB, hymin⟩ := hd a
  by_contra hlt
  push Not at hlt
  have hjl : j ≠ ℓ := by rintro rfl; exact lt_irrefl _ hlt
  set e := z a ℓ with he
  set e' := e * p ℓ / p j with he'
  have he'0 : 0 ≤ e' := by positivity
  let y' : M → ℝ := fun i => z a i - (if i = ℓ then e else 0) + (if i = j then e' else 0)
  have hy'0 : ∀ i, 0 ≤ y' i := by
    intro i
    simp only [y']
    by_cases h1 : i = ℓ
    · subst h1; simp [hjl.symm, he]
    · by_cases h2 : i = j
      · subst h2; simp [h1]; linarith [hy0 i]
      · simp [h1, h2]; exact hy0 i
  have hsum : ∀ g : M → ℝ, ∑ i, g i * y' i = ∑ i, g i * z a i - g ℓ * e + g j * e' := by
    intro g
    simp only [y', mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    congr 1
    · congr 1
      simp [mul_ite]
    · simp [mul_ite]
  have hfeas : F.earn a ≤ ∑ i, p i * y' i := by
    rw [hsum]
    have : p j * e' = p ℓ * e := by rw [he']; field_simp
    linarith
  have hmin := hymin y' hy'0 hfeas
  rw [hsum] at hmin
  -- d_ℓ e ≤ d_j e'
  have h1 : F.disutil a ℓ * e ≤ F.disutil a j * e' := by linarith
  rw [he'] at h1
  have he0 : 0 < e := hℓ
  -- d_ℓ ≤ d_j p_ℓ / p_j  ⇒  p_j / d_j ≤ p_ℓ / d_ℓ
  have h2 : F.disutil a ℓ * p j ≤ F.disutil a j * p ℓ := by
    have h3 : F.disutil a ℓ * e * p j ≤ F.disutil a j * (e * p ℓ / p j) * p j :=
      mul_le_mul_of_nonneg_right h1 hpj.le
    rw [show F.disutil a j * (e * p ℓ / p j) * p j = F.disutil a j * p ℓ * e by
      field_simp] at h3
    nlinarith
  have : p j / F.disutil a j ≤ p ℓ / F.disutil a ℓ := by
    rw [div_le_div_iff₀ hdj hdl]; linarith
  linarith

lemma balance {F : ChoresMarket N M} (hF : Pos F) {p : M → ℝ} {z : N → M → ℝ}
    (hCE : F.IsCE p z) : ∑ j, F.supply j * p j = ∑ a, F.earn a := by
  have h1 : ∀ j, F.supply j * p j = ∑ a, p j * z a j := by
    intro j
    rw [← hCE.2.2.2 j, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact earn_eq hF hCE a

end CEAux

namespace ChoresMkt
open CEAux

variable {n : ℕ}

lemma t_facts (P : Quadratic n) (ε : ℚ) : 0 < tParam P ε ∧ tParam P ε ≤ 1 / 256 := by
  have hL : 8 ≤ chainLength P ε := by
    unfold chainLength
    split_ifs with h
    · exact (Nat.find_spec h).1
    · exact le_refl _
  refine ⟨by unfold tParam; positivity, ?_⟩
  unfold tParam
  calc ((1 : ℝ) / 2) ^ chainLength P ε ≤ (1 / 2) ^ 8 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hL
    _ = 1 / 256 := by norm_num

/-- The coefficient size `S = ∑|A| + ∑|c|`. -/
noncomputable def csize (P : Quadratic n) : ℝ :=
  ∑ i, ∑ j, |(P.Q i j : ℝ)| + ∑ i, |(P.c i : ℝ)|

lemma csize_nonneg (P : Quadratic n) : 0 ≤ csize P := by unfold csize; positivity

lemma lam_eq (P : Quadratic n) : lam P = 1 / (2 * ((n : ℝ) + 1) * (1 + csize P)) := by
  simp only [lam, csize]; ring_nf

lemma lam_nonneg (P : Quadratic n) : 0 ≤ lam P := by
  rw [lam_eq]; have := csize_nonneg P; positivity

lemma lam_small (P : Quadratic n) {z : ℝ} (hz : |z| ≤ csize P) :
    |lam P * z| ≤ 1 / (2 * ((n : ℝ) + 1)) := by
  have hS0 := csize_nonneg P
  rw [abs_mul, lam_eq, abs_of_nonneg (by positivity)]
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : |z| * (2 * ((n : ℝ) + 1)) ≤ (1 + csize P) * (2 * ((n : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith

lemma entry_le (P : Quadratic n) (i k : Fin n) : |(P.Q i k : ℝ)| ≤ csize P := by
  have h1 : |(P.Q i k : ℝ)| ≤ ∑ k, |(P.Q i k : ℝ)| :=
    Finset.single_le_sum (f := fun k => |(P.Q i k : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ k)
  have h2 : ∑ k, |(P.Q i k : ℝ)| ≤ ∑ i, ∑ k, |(P.Q i k : ℝ)| :=
    Finset.single_le_sum (f := fun i => ∑ k, |(P.Q i k : ℝ)|) (fun _ _ => by positivity)
      (Finset.mem_univ i)
  have h3 : 0 ≤ ∑ i, |(P.c i : ℝ)| := by positivity
  unfold csize; linarith

lemma row_le (P : Quadratic n) (i : Fin n) : |∑ k, (P.Q i k : ℝ)| ≤ csize P := by
  have h2 : ∑ k, |(P.Q i k : ℝ)| ≤ ∑ i, ∑ k, |(P.Q i k : ℝ)| :=
    Finset.single_le_sum (f := fun i => ∑ k, |(P.Q i k : ℝ)|) (fun _ _ => by positivity)
      (Finset.mem_univ i)
  have h3 : 0 ≤ ∑ i, |(P.c i : ℝ)| := by positivity
  have := Finset.abs_sum_le_sum_abs (fun k => (P.Q i k : ℝ)) Finset.univ
  unfold csize; linarith

lemma cExt_le (P : Quadratic n) (j : Fin (n + 1)) : |cExt P j| ≤ csize P := by
  have h0 : 0 ≤ ∑ i, ∑ j, |(P.Q i j : ℝ)| := by positivity
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [cExt, Fin.cons_zero, abs_neg]
    have := Finset.abs_sum_le_sum_abs (fun i => (P.c i : ℝ)) Finset.univ
    unfold csize; linarith
  · simp only [cExt, Fin.cons_succ]
    have : |(P.c i : ℝ)| ≤ ∑ i, |(P.c i : ℝ)| :=
      Finset.single_le_sum (f := fun i => |(P.c i : ℝ)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ i)
    unfold csize; linarith

lemma cExt_sum (P : Quadratic n) : ∑ j, cExt P j = 0 := by
  rw [Fin.sum_univ_succ]
  simp [cExt]

lemma w_bounds (P : Quadratic n) (π : Pair n) :
    1 / (2 * ((n : ℝ) + 1)) ≤ pairWeight P π ∧ pairWeight P π ≤ 3 / (2 * ((n : ℝ) + 1)) := by
  have key : ∀ z : ℝ, |z| ≤ csize P →
      (1 / (2 * ((n : ℝ) + 1)) ≤ 1 / ((n : ℝ) + 1) - lam P * z ∧
        1 / ((n : ℝ) + 1) - lam P * z ≤ 3 / (2 * ((n : ℝ) + 1))) ∧
      (1 / (2 * ((n : ℝ) + 1)) ≤ 1 / ((n : ℝ) + 1) + lam P * z ∧
        1 / ((n : ℝ) + 1) + lam P * z ≤ 3 / (2 * ((n : ℝ) + 1))) := by
    intro z hz
    have h := abs_le.mp (lam_small P hz)
    have e : (1 : ℝ) / ((n : ℝ) + 1) = 2 * (1 / (2 * ((n : ℝ) + 1))) := by
      field_simp
    have e3 : (3 : ℝ) / (2 * ((n : ℝ) + 1)) = 3 * (1 / (2 * ((n : ℝ) + 1))) := by ring
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hj' : π.1.2 ≠ 0 := by
    intro h
    have := π.2
    rw [h] at this
    exact absurd this (Fin.not_lt_zero _)
  unfold pairWeight wgt
  split_ifs with h1
  · exact (key _ (row_le P _)).1
  · exact (key _ (entry_le P _ _)).2

lemma w_pos (P : Quadratic n) (π : Pair n) : 0 < pairWeight P π :=
  lt_of_lt_of_le (by positivity) (w_bounds P π).1

lemma card_incident_le (j : Fin (n + 1)) : (incident (n := n) j).card ≤ n + 1 := by
  classical
  let other : Pair n → Fin (n + 1) := fun π => if π.1.1 = j then π.1.2 else π.1.1
  have hinj : Set.InjOn other (incident (n := n) j : Set (Pair n)) := by
    intro π hπ π' hπ' h
    simp only [incident, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hπ hπ'
    have h1 := π.2
    have h2 := π'.2
    apply Subtype.ext
    simp only [other] at h
    rcases hπ with e1 | e1 <;> rcases hπ' with e2 | e2
    · rw [if_pos e1, if_pos e2] at h; exact Prod.ext (e1.trans e2.symm) h
    · have ne2 : π'.1.1 ≠ j := by rw [← e2]; exact ne_of_lt h2
      rw [if_pos e1, if_neg ne2] at h
      exfalso
      rw [Fin.lt_def] at h1 h2
      have := congrArg Fin.val h; have := congrArg Fin.val e1; have := congrArg Fin.val e2
      omega
    · have ne1 : π.1.1 ≠ j := by rw [← e1]; exact ne_of_lt h1
      rw [if_neg ne1, if_pos e2] at h
      exfalso
      rw [Fin.lt_def] at h1 h2
      have := congrArg Fin.val h; have := congrArg Fin.val e1; have := congrArg Fin.val e2
      omega
    · have ne1 : π.1.1 ≠ j := by rw [← e1]; exact ne_of_lt h1
      have ne2 : π'.1.1 ≠ j := by rw [← e2]; exact ne_of_lt h2
      rw [if_neg ne1, if_neg ne2] at h
      exact Prod.ext h (e1.trans e2.symm)
  calc (incident (n := n) j).card = ((incident (n := n) j).image other).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (Fin (n + 1))).card := Finset.card_le_univ _
    _ = n + 1 := by simp

lemma incident_w_le (P : Quadratic n) (j : Fin (n + 1)) :
    ∑ π ∈ incident j, pairWeight P π ≤ 3 / 2 := by
  have h := Finset.sum_le_card_nsmul (incident j) (fun π => pairWeight P π)
    (3 / (2 * ((n : ℝ) + 1))) (fun π _ => (w_bounds P π).2)
  rw [nsmul_eq_mul] at h
  have hc : ((incident (n := n) j).card : ℝ) ≤ n + 1 := by exact_mod_cast card_incident_le j
  have : ((incident (n := n) j).card : ℝ) * (3 / (2 * ((n : ℝ) + 1))) ≤ 3 / 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith

lemma sum_incident (f : Pair n → ℝ) : ∑ j, ∑ π ∈ incident j, f π = 2 * ∑ π, f π := by
  classical
  simp only [incident, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π _
  rw [← Finset.sum_filter]
  have : (Finset.univ.filter (fun j => π.1.1 = j ∨ π.1.2 = j)) = {π.1.1, π.1.2} := by
    ext j; simp [eq_comm]
  rw [this, Finset.sum_pair (ne_of_lt π.2)]
  ring

variable (P : Quadratic n) (t : ℝ) (L : ℕ)

lemma earn_inl (j : Fin (n + 1)) : (chainMarket P t L).earn (Sum.inl j) =
    1 - 3 / 2 * ∑ k : Fin L, ∑ π ∈ incident j, gadgetEarn P t π k.val - alpha P t / t * cExt P j :=
  rfl

lemma earn_inr (π : Pair n) (k : Fin L) (r : Fin 3) :
    (chainMarket P t L).earn (Sum.inr (π, k, r)) = gadgetEarn P t π k.val := rfl

lemma supply_inl (j : Fin (n + 1)) : (chainMarket P t L).supply (Sum.inl j) =
    1 - ∑ k : Fin L, ∑ π ∈ incident j, gadgetSupply P t π k.val := rfl

lemma supply_inr (π : Pair n) (k : Fin L) (s : Bool) :
    (chainMarket P t L).supply (Sum.inr (π, k, s)) = gadgetSupply P t π k.val := rfl

lemma sum_incident_layers (g : Pair n → ℕ → ℝ) :
    ∑ j : Fin (n + 1), ∑ k : Fin L, ∑ π ∈ incident j, g π k.val =
      2 * ∑ π, ∑ k : Fin L, g π k.val := by
  rw [Finset.sum_comm]
  simp_rw [sum_incident (fun π => g π _)]
  rw [← Finset.mul_sum, Finset.sum_comm]

lemma total_earn (ht : t ≠ 0) : ∑ a, (chainMarket P t L).earn a = n + 1 := by
  have hg : ∑ b : Pair n × Fin L × Fin 3, (chainMarket P t L).earn (Sum.inr b) =
      3 * ∑ π, ∑ k : Fin L, gadgetEarn P t π k.val := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro π _
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    simp only [earn_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hb : ∑ j, (chainMarket P t L).earn (Sum.inl j) =
      ((n : ℝ) + 1) - 3 / 2 * (2 * ∑ π, ∑ k : Fin L, gadgetEarn P t π k.val) := by
    simp only [earn_inl]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      cExt_sum, sum_incident_layers L (fun π k => gadgetEarn P t π k)]
    simp
  rw [Fintype.sum_sum_type, hb, hg]
  ring

lemma total_supply : ∑ ℓ, (chainMarket P t L).supply ℓ = n + 1 := by
  have hg : ∑ b : Pair n × Fin L × Bool, (chainMarket P t L).supply (Sum.inr b) =
      2 * ∑ π, ∑ k : Fin L, gadgetSupply P t π k.val := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro π _
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    simp only [supply_inr, Fintype.sum_bool]
    ring
  have hb : ∑ j, (chainMarket P t L).supply (Sum.inl j) =
      ((n : ℝ) + 1) - 2 * ∑ π, ∑ k : Fin L, gadgetSupply P t π k.val := by
    simp only [supply_inl]
    rw [Finset.sum_sub_distrib, sum_incident_layers L (fun π k => gadgetSupply P t π k)]
    simp
  rw [Fintype.sum_sum_type, hb, hg]
  ring


lemma q_bounds {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 256) (k : ℕ) :
    1 ≤ qPar t k ∧ qPar t k ≤ 1 + t / 4 := by
  unfold qPar
  have hr0 : 0 ≤ 1 / 2 - 4 * t := by linarith
  have hr1 : 1 / 2 - 4 * t ≤ 1 := by linarith
  have h0 : 0 ≤ (1 / 2 - 4 * t) ^ k := pow_nonneg hr0 k
  have h1 : (1 / 2 - 4 * t) ^ k ≤ 1 := pow_le_one₀ hr0 hr1
  constructor <;> nlinarith

lemma geom_le_two {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 256) :
    ∑ k : Fin L, (1 / 2 - 4 * t) ^ k.val ≤ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (1 / 2 - 4 * t) ^ k) L]
  have hr0 : 0 ≤ 1 / 2 - 4 * t := by linarith
  calc ∑ k ∈ Finset.range L, (1 / 2 - 4 * t) ^ k ≤ ∑ k ∈ Finset.range L, (1 / 2 : ℝ) ^ k :=
        Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ hr0 (by linarith) k)
    _ ≤ 2 := by
        rw [geom_sum_eq (by norm_num)]
        have : 0 ≤ (1 / 2 : ℝ) ^ L := by positivity
        rw [div_le_iff_of_neg (by norm_num)]
        linarith

lemma incident_earn_le {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 256) (j : Fin (n + 1)) :
    0 ≤ ∑ k : Fin L, ∑ π ∈ incident j, gadgetEarn P t π k.val ∧
      ∑ k : Fin L, ∑ π ∈ incident j, gadgetEarn P t π k.val ≤ 3 * t := by
  have e : ∑ k : Fin L, ∑ π ∈ incident j, gadgetEarn P t π k.val =
      (∑ π ∈ incident j, pairWeight P π) * (t * ∑ k : Fin L, (1 / 2 - 4 * t) ^ k.val) := by
    simp only [gadgetEarn]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro π _
    ring
  rw [e]
  have hw0 : 0 ≤ ∑ π ∈ incident j, pairWeight P π :=
    Finset.sum_nonneg (fun π _ => (w_pos P π).le)
  have hw := incident_w_le P j
  have hg := geom_le_two L ht ht'
  have hg0 : 0 ≤ ∑ k : Fin L, (1 / 2 - 4 * t) ^ k.val :=
    Finset.sum_nonneg (fun k _ => pow_nonneg (by linarith) _)
  constructor
  · positivity
  · have h1 : t * ∑ k : Fin L, (1 / 2 - 4 * t) ^ k.val ≤ 2 * t := by nlinarith
    have h2 : 0 ≤ t * ∑ k : Fin L, (1 / 2 - 4 * t) ^ k.val := by positivity
    nlinarith

lemma earn_pos {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 256) (a : Agent n L) :
    0 < (chainMarket P t L).earn a := by
  rcases a with j | ⟨π, k, r⟩
  · rw [earn_inl]
    have hX := incident_earn_le P L ht ht' j
    have hα : alpha P t / t * cExt P j = t * (lam P * cExt P j) := by
      unfold alpha; field_simp
    have hc := abs_le.mp (lam_small P (cExt_le P j))
    have hn : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num); have : (0 : ℝ) ≤ n := by positivity
      linarith
    rw [hα]
    nlinarith
  · rw [earn_inr]
    unfold gadgetEarn
    have := w_pos P π
    have : 0 < 1 / 2 - 4 * t := by linarith
    positivity

lemma supply_inl_ge {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 256) (j : Fin (n + 1)) :
    1 - 3 * t ≤ (chainMarket P t L).supply (Sum.inl j) := by
  rw [supply_inl]
  have hX := incident_earn_le P L ht ht' j
  have e : ∑ k : Fin L, ∑ π ∈ incident j, gadgetSupply P t π k.val =
      (1 - 4 * t) * ∑ k : Fin L, ∑ π ∈ incident j, gadgetEarn P t π k.val := by
    simp only [gadgetSupply, Finset.mul_sum]
  rw [e]
  nlinarith

lemma supply_pos {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 256) (ℓ : Chore n L) :
    0 < (chainMarket P t L).supply ℓ := by
  rcases ℓ with j | ⟨π, k, s⟩
  · have := supply_inl_ge P L ht ht' j; linarith
  · rw [supply_inr]
    unfold gadgetSupply gadgetEarn
    have := w_pos P π
    have : 0 < 1 / 2 - 4 * t := by linarith
    have : 0 < 1 - 4 * t := by linarith
    positivity

lemma dis_inl_inl (i j : Fin (n + 1)) : (chainMarket P t L).disutil (Sum.inl i) (Sum.inl j) =
    if j = 0 ∨ j = i then 1 else 1 + t := rfl

lemma dis_inl_inr (i : Fin (n + 1)) (c : Pair n × Fin L × Bool) :
    (chainMarket P t L).disutil (Sum.inl i) (Sum.inr c) = (1 + t) ^ 2 := rfl

lemma dis_inr (π : Pair n) (k : Fin L) (r : Fin 3) (ℓ : Chore n L) :
    (chainMarket P t L).disutil (Sum.inr (π, k, r)) ℓ =
      if r = 0 then
        (if ℓ = firstIn π k ∨ ℓ = secondIn π k then qPar t k.val
          else if ℓ = Sum.inr (π, k, true) then 1 else (1 + t) ^ 2)
      else if r = 1 then
        (if ℓ = firstIn π k then 1 / qPar t k.val
          else if ℓ = Sum.inr (π, k, false) then 1 else (1 + t) ^ 2)
      else
        (if ℓ = secondIn π k then 1 / qPar t k.val
          else if ℓ = Sum.inr (π, k, false) then 1 else (1 + t) ^ 2) := rfl

lemma dis_range {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 256) (a : Agent n L) (ℓ : Chore n L) :
    (1 + t)⁻¹ ≤ (chainMarket P t L).disutil a ℓ ∧ (chainMarket P t L).disutil a ℓ ≤ (1 + t) ^ 2 := by
  have h1 : (1 + t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have h2 : (1 : ℝ) ≤ (1 + t) ^ 2 := by nlinarith
  have h3 : 1 + t ≤ (1 + t) ^ 2 := by nlinarith
  have hq : ∀ k, (1 + t)⁻¹ ≤ qPar t k ∧ qPar t k ≤ (1 + t) ^ 2 := by
    intro k
    have := q_bounds ht ht' k
    constructor <;> nlinarith
  have hq' : ∀ k, (1 + t)⁻¹ ≤ 1 / qPar t k ∧ 1 / qPar t k ≤ (1 + t) ^ 2 := by
    intro k
    have hb := q_bounds ht ht' k
    constructor
    · rw [one_div]
      exact inv_anti₀ (by linarith) (by linarith)
    · have : 1 / qPar t k ≤ 1 := by rw [div_le_one (by linarith)]; exact hb.1
      linarith
  rcases a with i | ⟨π, k, r⟩
  · rcases ℓ with j | c
    · rw [dis_inl_inl]
      split_ifs
      · exact ⟨h1, h2⟩
      · exact ⟨by linarith, h3⟩
    · rw [dis_inl_inr]
      exact ⟨by linarith, le_refl _⟩
  · rw [dis_inr]
    split_ifs
    all_goals first
      | exact hq _ | exact hq' _ | exact ⟨h1, h2⟩ | exact ⟨by linarith, le_refl _⟩

lemma dis_pos {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 256) (a : Agent n L) (ℓ : Chore n L) :
    0 < (chainMarket P t L).disutil a ℓ :=
  lt_of_lt_of_le (by positivity) (dis_range P L ht ht' a ℓ).1

lemma pos_market {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 256) : Pos (chainMarket P t L) :=
  ⟨dis_pos P L ht ht', earn_pos P L ht ht', supply_pos P L ht ht'⟩

lemma dis_undesignated (a : Agent n L) (ℓ : Chore n L) (h : ¬ Designated a ℓ) :
    (chainMarket P t L).disutil a ℓ = (1 + t) ^ 2 := by
  rcases a with i | ⟨π, k, r⟩
  · rcases ℓ with j | c
    · exact absurd ⟨j, rfl⟩ h
    · rfl
  · rw [dis_inr]
    simp only [Designated] at h
    fin_cases r <;> simp_all


lemma firstIn_eq_inr {π π' : Pair n} {k k' : Fin L} {σ : Bool}
    (h : (Sum.inr (π, k, σ) : Chore n L) = firstIn π' k') :
    π' = π ∧ k'.val = k.val + 1 ∧ σ = true := by
  unfold firstIn at h
  split_ifs at h with hk
  simp only [Sum.inr.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.symm, ?_, h3⟩
  have := congrArg Fin.val h2
  simp at this
  omega

lemma secondIn_eq_inr {π π' : Pair n} {k k' : Fin L} {σ : Bool}
    (h : (Sum.inr (π, k, σ) : Chore n L) = secondIn π' k') :
    π' = π ∧ k'.val = k.val + 1 ∧ σ = false := by
  unfold secondIn at h
  split_ifs at h with hk
  simp only [Sum.inr.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.symm, ?_, h3⟩
  have := congrArg Fin.val h2
  simp at this
  omega

lemma firstIn_eq_inl {π : Pair n} {k : Fin L} {j : Fin (n + 1)}
    (h : (Sum.inl j : Chore n L) = firstIn π k) : π.1.1 = j := by
  unfold firstIn at h
  split_ifs at h with hk
  · simp only [Sum.inl.injEq] at h; exact h.symm

lemma secondIn_eq_inl {π : Pair n} {k : Fin L} {j : Fin (n + 1)}
    (h : (Sum.inl j : Chore n L) = secondIn π k) : π.1.2 = j := by
  unfold secondIn at h
  split_ifs at h with hk
  · simp only [Sum.inl.injEq] at h; exact h.symm

/-- Outside users of an output are next-layer agents. -/
lemma outside_designated {π π' : Pair n} {k k' : Fin L} {σ : Bool} {r : Fin 3}
    (hD : Designated (Sum.inr (π', k', r) : Agent n L) (Sum.inr (π, k, σ)))
    (hout : ¬ (π' = π ∧ k' = k)) :
    π' = π ∧ k'.val = k.val + 1 ∧ (r = 0 ∨ r = (if σ then 1 else 2)) := by
  simp only [Designated] at hD
  rcases hD with ⟨hr, h | h | h⟩ | ⟨hr, h | h⟩ | ⟨hr, h | h⟩
  · obtain ⟨a1, a2, -⟩ := firstIn_eq_inr L h; exact ⟨a1, a2, Or.inl hr⟩
  · obtain ⟨a1, a2, -⟩ := secondIn_eq_inr L h; exact ⟨a1, a2, Or.inl hr⟩
  · simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    exact absurd ⟨h.1.symm, h.2.1.symm⟩ hout
  · obtain ⟨a1, a2, a3⟩ := firstIn_eq_inr L h; exact ⟨a1, a2, Or.inr (by simp [a3, hr])⟩
  · simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    exact absurd ⟨h.1.symm, h.2.1.symm⟩ hout
  · obtain ⟨a1, a2, a3⟩ := secondIn_eq_inr L h; exact ⟨a1, a2, Or.inr (by simp [a3, hr])⟩
  · simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    exact absurd ⟨h.1.symm, h.2.1.symm⟩ hout

lemma designated_basic {π : Pair n} {k : Fin L} {r : Fin 3} {j : Fin (n + 1)}
    (hD : Designated (Sum.inr (π, k, r) : Agent n L) (Sum.inl j)) : π ∈ incident j := by
  simp only [incident, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [Designated] at hD
  rcases hD with ⟨-, h | h | h⟩ | ⟨-, h | h⟩ | ⟨-, h | h⟩
  · exact Or.inl (firstIn_eq_inl L h)
  · exact Or.inr (secondIn_eq_inl L h)
  · exact absurd h (by simp)
  · exact Or.inl (firstIn_eq_inl L h)
  · exact absurd h (by simp)
  · exact Or.inr (secondIn_eq_inl L h)
  · exact absurd h (by simp)

theorem core73 {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 256)
    (p : Chore n L → ℝ) (z : Agent n L → Chore n L → ℝ)
    (hCE : (chainMarket P t L).IsCE p z) :
    (∀ ℓ, ((1 + t) ^ 3)⁻¹ ≤ p ℓ ∧ p ℓ ≤ (1 + t) ^ 3) ∧
    (∀ (π : Pair n) (k : Fin L) (σ : Bool),
      gadgetSupply P t π k.val * p (Sum.inr (π, k, σ)) < gadgetEarn P t π k.val ∧
      (p (Sum.inr (π, k, σ)) < pmax p →
        ∑ a ∈ outUsers z π k σ, (chainMarket P t L).earn a <
          gadgetSupply P t π k.val * p (Sum.inr (π, k, σ)))) ∧
    (∀ i : Fin n, p (Sum.inl 0) ≤ p (Sum.inl i.succ) ∧
      p (Sum.inl i.succ) ≤ (1 + t) * p (Sum.inl 0)) := by
  classical
  set F := chainMarket P t L with hFdef
  have hF : Pos F := pos_market P L ht ht'
  have hp : ∀ ℓ, 0 < p ℓ := price_pos hF hCE
  -- extremal prices
  obtain ⟨ℓmax, -, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty p
  obtain ⟨ℓmin, -, hmin⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty p
  have hle_max : ∀ ℓ, p ℓ ≤ pmax p := fun ℓ => Finset.le_sup' p (Finset.mem_univ ℓ)
  have hge_min : ∀ ℓ, pmin p ≤ p ℓ := fun ℓ => Finset.inf'_le p (Finset.mem_univ ℓ)
  have hpmax : pmax p = p ℓmax := hmax
  have hpmin : pmin p = p ℓmin := hmin
  -- payment balance
  have hbal := balance hF hCE
  rw [total_earn P t L ht.ne'] at hbal
  have hS := total_supply P t L
  obtain ⟨ℓ1, hℓ1⟩ : ∃ ℓ, 1 ≤ p ℓ := by
    by_contra h
    push Not at h
    have : ∑ ℓ, F.supply ℓ * p ℓ < ∑ ℓ, F.supply ℓ :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun ℓ _ => by
        have := hF.S ℓ; have := h ℓ; nlinarith)
    linarith
  obtain ⟨ℓ2, hℓ2⟩ : ∃ ℓ, p ℓ ≤ 1 := by
    by_contra h
    push Not at h
    have : ∑ ℓ, F.supply ℓ < ∑ ℓ, F.supply ℓ * p ℓ :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun ℓ _ => by
        have := hF.S ℓ; have := h ℓ; nlinarith)
    linarith
  -- ratio bound
  have hratio : pmax p ≤ (1 + t) ^ 3 * pmin p := by
    obtain ⟨a, ha⟩ := used_exists hF hCE ℓmin
    have hopt := optimal hF hCE ha ℓmax
    have hd1 := dis_range P L ht ht' a ℓmax
    have hd2 := dis_range P L ht ht' a ℓmin
    have hdp1 := dis_pos P L ht ht' a ℓmax
    have hdp2 := dis_pos P L ht ht' a ℓmin
    rw [div_le_div_iff₀ hdp1 hdp2] at hopt
    have hdm : 1 ≤ F.disutil a ℓmin * (1 + t) := by
      have := hd2.1
      rw [inv_le_iff_one_le_mul₀ (by linarith)] at this
      linarith
    rw [hpmax, hpmin]
    have hpl := hp ℓmax
    have hps := hp ℓmin
    calc p ℓmax ≤ p ℓmax * (F.disutil a ℓmin * (1 + t)) := by nlinarith
      _ = (p ℓmax * F.disutil a ℓmin) * (1 + t) := by ring
      _ ≤ (p ℓmin * F.disutil a ℓmax) * (1 + t) := by gcongr
      _ ≤ (p ℓmin * (1 + t) ^ 2) * (1 + t) := by gcongr; exact hd1.2
      _ = (1 + t) ^ 3 * p ℓmin := by ring
  have h13 : 0 < (1 + t) ^ 3 := by positivity
  have item1 : ∀ ℓ, ((1 + t) ^ 3)⁻¹ ≤ p ℓ ∧ p ℓ ≤ (1 + t) ^ 3 := by
    intro ℓ
    have a1 := hle_max ℓ
    have a2 := hge_min ℓ
    have a3 := hle_max ℓ1
    have a4 := hge_min ℓ2
    constructor
    · rw [inv_le_iff_one_le_mul₀ h13]
      nlinarith
    · nlinarith
  have hinv3 : ∀ ℓ, 1 - 3 * t ≤ p ℓ := by
    intro ℓ
    have h := (item1 ℓ).1
    have : 1 - 3 * t ≤ ((1 + t) ^ 3)⁻¹ := by
      rw [le_inv_comm₀ (by nlinarith) h13]
      rw [inv_eq_one_div, le_div_iff₀ (by nlinarith)]
      nlinarith [sq_nonneg t, pow_pos ht 3, pow_pos ht 4]
    linarith
  -- Lemma 7.2
  have h72 : ∀ a ℓ, 0 < z a ℓ → p ℓ < pmax p → Designated a ℓ := by
    intro a ℓ hz hlt
    by_contra hnd
    have hd := dis_undesignated P t L a ℓ hnd
    have hopt := optimal hF hCE hz ℓmax
    rw [hd] at hopt
    have hdm := (dis_range P L ht ht' a ℓmax).2
    have hdp := dis_pos P L ht ht' a ℓmax
    have hpm := hp ℓmax
    have h1 : p ℓmax / (1 + t) ^ 2 ≤ p ℓmax / F.disutil a ℓmax :=
      div_le_div_of_nonneg_left hpm.le hdp hdm
    have h2 : p ℓmax ≤ p ℓ := by
      have := h1.trans hopt
      rwa [div_le_div_iff_of_pos_right (by positivity)] at this
    rw [hpmax] at hlt
    linarith
  -- earnings are bounded by the total earning requirement
  have hearn_le : ∀ a ℓ, p ℓ * z a ℓ ≤ F.earn a := by
    intro a ℓ
    rw [← earn_eq hF hCE a]
    exact Finset.single_le_sum (f := fun ℓ => p ℓ * z a ℓ)
      (fun ℓ' _ => mul_nonneg (hp ℓ').le (hCE.2.1 a ℓ')) (Finset.mem_univ ℓ)
  refine ⟨item1, ?_, ?_⟩
  · -- Item 2
    intro π k σ
    have hB : 0 < gadgetEarn P t π k.val := by
      have := earn_pos P L ht ht' (Sum.inr (π, k, 0)); rwa [earn_inr] at this
    have hSdef : gadgetSupply P t π k.val = (1 - 4 * t) * gadgetEarn P t π k.val := rfl
    have hpo := item1 (Sum.inr (π, k, σ))
    have hpl := hinv3 (Sum.inr (π, k, σ))
    constructor
    · rw [hSdef]
      have h3 : (1 + t) ^ 3 < 1 + 4 * t := by nlinarith [sq_nonneg t]
      have h4 : 0 < 1 - 4 * t := by linarith
      have : (1 - 4 * t) * p (Sum.inr (π, k, σ)) < 1 := by nlinarith
      nlinarith
    · intro hlt
      have hmem : ∀ a ∈ outUsers z π k σ, ∃ k1 : Fin L, k1.val = k.val + 1 ∧
          (a = Sum.inr (π, k1, 0) ∨ a = Sum.inr (π, k1, if σ then 1 else 2)) := by
        intro a ha
        simp only [outUsers, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        have hD := h72 a _ ha.2 hlt
        rcases a with i | ⟨π', k', r⟩
        · simp [Designated] at hD
        · have hout : ¬ (π' = π ∧ k' = k) := by
            rintro ⟨rfl, rfl⟩; exact ha.1 r rfl
          obtain ⟨e1, e2, e3⟩ := outside_designated L hD hout
          subst e1
          refine ⟨k', e2, ?_⟩
          rcases e3 with e3 | e3 <;> subst e3 <;> simp
      have hSpos : 0 < gadgetSupply P t π k.val * p (Sum.inr (π, k, σ)) := by
        rw [hSdef]; have : 0 < 1 - 4 * t := by linarith
        have := hp (Sum.inr (π, k, σ)); positivity
      by_cases hk : k.val + 1 < L
      · set k1 : Fin L := ⟨k.val + 1, hk⟩
        set T : Finset (Agent n L) := {Sum.inr (π, k1, 0), Sum.inr (π, k1, if σ then 1 else 2)}
        have hsub : outUsers z π k σ ⊆ T := by
          intro a ha
          obtain ⟨k2, hk2, h⟩ := hmem a ha
          have : k2 = k1 := Fin.ext hk2
          subst this
          rcases h with h | h <;> simp [T, h]
        have h1 : ∑ a ∈ outUsers z π k σ, F.earn a ≤ ∑ a ∈ T, F.earn a :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => (hF.B a).le)
        have h2 : ∑ a ∈ T, F.earn a ≤ T.card • gadgetEarn P t π (k.val + 1) := by
          apply Finset.sum_le_card_nsmul
          intro a ha
          simp only [T, Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha with rfl | rfl <;> simp [F, earn_inr, k1]
        have h3 : T.card ≤ 2 := Finset.card_le_two
        have h4 : gadgetEarn P t π (k.val + 1) = (1 / 2 - 4 * t) * gadgetEarn P t π k.val := by
          simp only [gadgetEarn, pow_succ]; ring
        rw [nsmul_eq_mul] at h2
        have h5 : (T.card : ℝ) ≤ 2 := by exact_mod_cast h3
        have hgE : 0 ≤ gadgetEarn P t π (k.val + 1) := by
          rw [h4]; have : 0 < 1 / 2 - 4 * t := by linarith
          positivity
        have h6 : ∑ a ∈ outUsers z π k σ, F.earn a ≤ (1 - 8 * t) * gadgetEarn P t π k.val := by
          calc ∑ a ∈ outUsers z π k σ, F.earn a ≤ (T.card : ℝ) * gadgetEarn P t π (k.val + 1) :=
                h1.trans h2
            _ ≤ 2 * gadgetEarn P t π (k.val + 1) := by gcongr
            _ = (1 - 8 * t) * gadgetEarn P t π k.val := by rw [h4]; ring
        rw [hSdef]
        have h7 : (1 - 8 * t) * gadgetEarn P t π k.val <
            (1 - 4 * t) * gadgetEarn P t π k.val * p (Sum.inr (π, k, σ)) := by
          have : (1 - 8 * t) < (1 - 4 * t) * (1 - 3 * t) := by nlinarith
          have h8 : (1 - 4 * t) * (1 - 3 * t) ≤ (1 - 4 * t) * p (Sum.inr (π, k, σ)) :=
            mul_le_mul_of_nonneg_left hpl (by linarith)
          nlinarith
        linarith
      · have hempty : outUsers z π k σ = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro a ha
          obtain ⟨k2, hk2, -⟩ := hmem a ha
          have := k2.isLt
          omega
        rw [hempty, Finset.sum_empty]
        exact hSpos
  · -- Item 3
    have hU : ∀ ℓ : Fin (n + 1), p (Sum.inl ℓ) < pmax p → ∃ b, 0 < z (Sum.inl b) (Sum.inl ℓ) := by
      intro ℓ hlt
      by_contra h
      push Not at h
      have hz0 : ∀ b, z (Sum.inl b) (Sum.inl ℓ) = 0 := fun b => le_antisymm (h b) (hCE.2.1 _ _)
      have hclear := hCE.2.2.2 (Sum.inl ℓ)
      rw [Fintype.sum_sum_type] at hclear
      simp only [hz0, Finset.sum_const_zero, zero_add] at hclear
      -- earnings from ℓ
      have hE : F.supply (Sum.inl ℓ) * p (Sum.inl ℓ) =
          ∑ g : Pair n × Fin L × Fin 3, p (Sum.inl ℓ) * z (Sum.inr g) (Sum.inl ℓ) := by
        rw [← hclear, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro g _; ring
      have hterm : ∀ g : Pair n × Fin L × Fin 3, p (Sum.inl ℓ) * z (Sum.inr g) (Sum.inl ℓ) ≤
          if g.1 ∈ incident ℓ then gadgetEarn P t g.1 g.2.1.val else 0 := by
        rintro ⟨π, k, r⟩
        by_cases hz : 0 < z (Sum.inr (π, k, r)) (Sum.inl ℓ)
        · have hD := h72 _ _ hz hlt
          have hinc := designated_basic L hD
          rw [if_pos hinc]
          have := hearn_le (Sum.inr (π, k, r)) (Sum.inl ℓ)
          rwa [earn_inr] at this
        · have : z (Sum.inr (π, k, r)) (Sum.inl ℓ) = 0 :=
            le_antisymm (not_lt.mp hz) (hCE.2.1 _ _)
          rw [this, mul_zero]
          split_ifs
          · exact (hF.B (Sum.inr (π, k, 0))).le
          · exact le_refl _
      have hsum : ∑ g : Pair n × Fin L × Fin 3,
          (if g.1 ∈ incident ℓ then gadgetEarn P t g.1 g.2.1.val else 0) =
          3 * ∑ k : Fin L, ∑ π ∈ incident ℓ, gadgetEarn P t π k.val := by
        rw [Fintype.sum_prod_type]
        simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        rw [Finset.sum_comm, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _
        simp only [Nat.cast_ofNat]
        rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]
      have hX := (incident_earn_le P L ht ht' ℓ).2
      have hle : F.supply (Sum.inl ℓ) * p (Sum.inl ℓ) ≤ 9 * t := by
        rw [hE]
        calc ∑ g : Pair n × Fin L × Fin 3, p (Sum.inl ℓ) * z (Sum.inr g) (Sum.inl ℓ)
            ≤ ∑ g : Pair n × Fin L × Fin 3,
                (if g.1 ∈ incident ℓ then gadgetEarn P t g.1 g.2.1.val else 0) :=
              Finset.sum_le_sum (fun g _ => hterm g)
          _ = 3 * ∑ k : Fin L, ∑ π ∈ incident ℓ, gadgetEarn P t π k.val := hsum
          _ ≤ 3 * (3 * t) := by gcongr
          _ = 9 * t := by ring
      have hSl := supply_inl_ge P L ht ht' ℓ
      have hpl := hinv3 (Sum.inl ℓ)
      have : (1 - 3 * t) * (1 - 3 * t) ≤ F.supply (Sum.inl ℓ) * p (Sum.inl ℓ) :=
        mul_le_mul hSl hpl (by linarith) (hF.S _).le
      have key : ∀ u : ℝ, 0 < u → u ≤ 1 / 256 → 9 * u < (1 - 3 * u) * (1 - 3 * u) := by
        intro u h1 h2; nlinarith
      linarith [key t ht ht']
    intro i
    constructor
    · by_cases hlt : p (Sum.inl i.succ) < pmax p
      · obtain ⟨b, hb⟩ := hU i.succ hlt
        have hopt := optimal hF hCE hb (Sum.inl 0)
        have hd0 : F.disutil (Sum.inl b) (Sum.inl 0) = 1 := by
          simp [F, dis_inl_inl]
        have hdj : 1 ≤ F.disutil (Sum.inl b) (Sum.inl i.succ) := by
          simp only [F, dis_inl_inl]; split_ifs <;> linarith
        rw [hd0, div_one] at hopt
        have : p (Sum.inl i.succ) / F.disutil (Sum.inl b) (Sum.inl i.succ) ≤ p (Sum.inl i.succ) :=
          div_le_self (hp _).le hdj
        linarith
      · push Not at hlt
        have := hle_max (Sum.inl 0)
        linarith
    · by_cases hlt : p (Sum.inl 0) < pmax p
      · obtain ⟨b, hb⟩ := hU 0 hlt
        have hopt := optimal hF hCE hb (Sum.inl i.succ)
        have hd0 : F.disutil (Sum.inl b) (Sum.inl 0) = 1 := by
          simp [F, dis_inl_inl]
        have hdj : F.disutil (Sum.inl b) (Sum.inl i.succ) ≤ 1 + t := by
          simp only [F, dis_inl_inl]; split_ifs <;> linarith
        have hdpos := dis_pos P L ht ht' (Sum.inl b) (Sum.inl i.succ)
        rw [hd0, div_one, div_le_iff₀ hdpos] at hopt
        have h2 := mul_le_mul_of_nonneg_left hdj (hp (Sum.inl 0)).le
        linarith
      · push Not at hlt
        have h1 := hle_max (Sum.inl i.succ)
        have h2 : 0 ≤ t * p (Sum.inl 0) := mul_nonneg ht.le (hp _).le
        linarith


/-! ## Lemma 7.4 -/

lemma inr_ne_firstIn (π : Pair n) (k : Fin L) (σ : Bool) :
    (Sum.inr (π, k, σ) : Chore n L) ≠ firstIn π k := by
  intro h
  have := (firstIn_eq_inr L h).2.1
  omega

lemma inr_ne_secondIn (π : Pair n) (k : Fin L) (σ : Bool) :
    (Sum.inr (π, k, σ) : Chore n L) ≠ secondIn π k := by
  intro h
  have := (secondIn_eq_inr L h).2.1
  omega

lemma firstIn_zero (π : Pair n) (k : Fin L) (hk : k.val = 0) :
    firstIn π k = (Sum.inl π.1.1 : Chore n L) := by
  unfold firstIn; rw [dif_pos hk]

lemma secondIn_zero (π : Pair n) (k : Fin L) (hk : k.val = 0) :
    secondIn π k = (Sum.inl π.1.2 : Chore n L) := by
  unfold secondIn; rw [dif_pos hk]

lemma firstIn_succ (π : Pair n) (k : Fin L) (hk : k.val ≠ 0) :
    firstIn π k = (Sum.inr (π, ⟨k.val - 1, by omega⟩, true) : Chore n L) := by
  unfold firstIn; rw [dif_neg hk]

lemma secondIn_succ (π : Pair n) (k : Fin L) (hk : k.val ≠ 0) :
    secondIn π k = (Sum.inr (π, ⟨k.val - 1, by omega⟩, false) : Chore n L) := by
  unfold secondIn; rw [dif_neg hk]

lemma q_succ_lt {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 256) (k : ℕ) : qPar t (k + 1) < qPar t k := by
  unfold qPar
  have hr0 : 0 < 1 / 2 - 4 * t := by linarith
  have h1 : (1 / 2 - 4 * t) ^ (k + 1) < (1 / 2 - 4 * t) ^ k := by
    rw [pow_succ]
    have := pow_pos hr0 k
    nlinarith
  nlinarith

lemma q_le_q0 {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 256) (k : ℕ) : qPar t k ≤ qPar t 0 := by
  induction k with
  | zero => exact le_refl _
  | succ k ih => exact le_trans (q_succ_lt ht ht' k).le ih

lemma one_lt_q {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 256) (k : ℕ) : 1 < qPar t k := by
  unfold qPar
  have hr0 : 0 < 1 / 2 - 4 * t := by linarith
  have := pow_pos hr0 k
  have : 0 < t / 4 * (1 / 2 - 4 * t) ^ k := by positivity
  linarith

theorem core74 {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 256)
    (p : Chore n L → ℝ) (z : Agent n L → Chore n L → ℝ)
    (hCE : (chainMarket P t L).IsCE p z) :
    pmax p ≤ (1 + t) * qPar t 0 * p (Sum.inl 0) ∧
      p (Sum.inl 0) / qPar t 0 ≤ pmin p ∧
      ∀ a ℓ, 0 < z a ℓ → Designated a ℓ := by
  classical
  set F := chainMarket P t L with hFdef
  have hF : Pos F := pos_market P L ht ht'
  have hp : ∀ ℓ, 0 < p ℓ := price_pos hF hCE
  obtain ⟨item1, item2, item3⟩ := core73 P L ht ht' p z hCE
  obtain ⟨ℓmax, -, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty p
  obtain ⟨ℓmin, -, hmin⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty p
  have hle_max : ∀ ℓ, p ℓ ≤ pmax p := fun ℓ => Finset.le_sup' p (Finset.mem_univ ℓ)
  have hge_min : ∀ ℓ, pmin p ≤ p ℓ := fun ℓ => Finset.inf'_le p (Finset.mem_univ ℓ)
  have hpmax : pmax p = p ℓmax := hmax
  have hpmin : pmin p = p ℓmin := hmin
  have hq0 : 1 < qPar t 0 := one_lt_q ht ht' 0
  have hp0 := hp (Sum.inl 0)
  -- Lemma 7.2 (first part)
  have h72 : ∀ a ℓ, 0 < z a ℓ → p ℓ < pmax p → Designated a ℓ := by
    intro a ℓ hz hlt
    by_contra hnd
    have hd := dis_undesignated P t L a ℓ hnd
    have hopt := optimal hF hCE hz ℓmax
    rw [hd] at hopt
    have hdm := (dis_range P L ht ht' a ℓmax).2
    have hdp := dis_pos P L ht ht' a ℓmax
    have h1 : p ℓmax / (1 + t) ^ 2 ≤ p ℓmax / F.disutil a ℓmax :=
      div_le_div_of_nonneg_left (hp ℓmax).le hdp hdm
    have h2 : p ℓmax ≤ p ℓ := by
      have := h1.trans hopt
      rwa [div_le_div_iff_of_pos_right (by positivity)] at this
    rw [hpmax] at hlt
    linarith
  have hearn_le : ∀ a ℓ, p ℓ * z a ℓ ≤ F.earn a := by
    intro a ℓ
    rw [← earn_eq hF hCE a]
    exact Finset.single_le_sum (f := fun ℓ => p ℓ * z a ℓ)
      (fun ℓ' _ => mul_nonneg (hp ℓ').le (hCE.2.1 a ℓ')) (Finset.mem_univ ℓ)
  -- basic prices are at least p₀
  have hbasic : ∀ j : Fin (n + 1), p (Sum.inl 0) ≤ p (Sum.inl j) ∧
      p (Sum.inl j) ≤ (1 + t) * p (Sum.inl 0) := by
    intro j
    refine Fin.cases ⟨le_refl _, by nlinarith⟩ (fun i => item3 i) j
  -- (O1)
  have O1 : ∀ (π : Pair n) (k : Fin L) (r : Fin 3) (σ : Bool),
      F.disutil (Sum.inr (π, k, r)) (Sum.inr (π, k, σ)) = 1 →
      ∃ ℓ, ℓ ≠ Sum.inr (π, k, σ) ∧ 0 < z (Sum.inr (π, k, r)) ℓ ∧
        p (Sum.inr (π, k, σ)) ≤ p ℓ / F.disutil (Sum.inr (π, k, r)) ℓ := by
    intro π k r σ hd1
    set a : Agent n L := Sum.inr (π, k, r)
    set out : Chore n L := Sum.inr (π, k, σ)
    have hSB := (item2 π k σ).1
    have hzS : z a out ≤ F.supply out := by
      rw [← hCE.2.2.2 out]
      exact Finset.single_le_sum (f := fun a' => z a' out) (fun a' _ => hCE.2.1 a' out)
        (Finset.mem_univ a)
    have hSo : F.supply out = gadgetSupply P t π k.val := supply_inr P t L π k σ
    have hEa : F.earn a = gadgetEarn P t π k.val := earn_inr P t L π k r
    have hlt : p out * z a out < F.earn a := by
      rw [hEa]
      calc p out * z a out ≤ p out * F.supply out := mul_le_mul_of_nonneg_left hzS (hp out).le
        _ = gadgetSupply P t π k.val * p out := by rw [hSo]; ring
        _ < gadgetEarn P t π k.val := hSB
    obtain ⟨ℓ, hℓne, hℓ⟩ : ∃ ℓ, ℓ ≠ out ∧ 0 < z a ℓ := by
      by_contra h
      push Not at h
      have hsplit := Finset.add_sum_erase Finset.univ (fun ℓ => p ℓ * z a ℓ) (Finset.mem_univ out)
      have hrest : ∑ ℓ ∈ Finset.univ.erase out, p ℓ * z a ℓ = 0 := by
        apply Finset.sum_eq_zero
        intro ℓ hℓ
        have := h ℓ (Finset.ne_of_mem_erase hℓ)
        have h0 : z a ℓ = 0 := le_antisymm this (hCE.2.1 a ℓ)
        rw [h0, mul_zero]
      rw [hrest, add_zero, earn_eq hF hCE a] at hsplit
      linarith
    refine ⟨ℓ, hℓne, hℓ, ?_⟩
    have hopt := optimal hF hCE hℓ out
    rwa [hd1, div_one] at hopt
  -- (O2)
  have O2 : ∀ (π : Pair n) (k : Fin L) (σ : Bool), p (Sum.inr (π, k, σ)) < pmax p →
      ∃ r : Fin 3, 0 < z (Sum.inr (π, k, r)) (Sum.inr (π, k, σ)) ∧
        ((σ = true ∧ r = 0) ∨ (σ = false ∧ (r = 1 ∨ r = 2))) := by
    intro π k σ hlt
    obtain ⟨r, hr⟩ : ∃ r : Fin 3, 0 < z (Sum.inr (π, k, r)) (Sum.inr (π, k, σ)) := by
      by_contra h
      push Not at h
      have hlow := (item2 π k σ).2 hlt
      have hterm : ∀ a, p (Sum.inr (π, k, σ)) * z a (Sum.inr (π, k, σ)) ≤
          if a ∈ outUsers z π k σ then F.earn a else 0 := by
        intro a
        by_cases hin : a ∈ outUsers z π k σ
        · rw [if_pos hin]; exact hearn_le a _
        · rw [if_neg hin]
          have hz0 : z a (Sum.inr (π, k, σ)) = 0 := by
            apply le_antisymm _ (hCE.2.1 a _)
            by_contra hpos
            push Not at hpos
            apply hin
            simp only [outUsers, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨?_, hpos⟩
            rintro r rfl
            exact absurd hpos (not_lt.mpr (h r))
          rw [hz0, mul_zero]
      have hsum : F.supply (Sum.inr (π, k, σ)) * p (Sum.inr (π, k, σ)) ≤ ∑ a ∈ outUsers z π k σ, F.earn a := by
        rw [← hCE.2.2.2 (Sum.inr (π, k, σ)), Finset.sum_mul]
        calc ∑ a, z a (Sum.inr (π, k, σ)) * p (Sum.inr (π, k, σ)) ≤ ∑ a, (if a ∈ outUsers z π k σ then F.earn a else 0) :=
              Finset.sum_le_sum (fun a _ => by rw [mul_comm]; exact hterm a)
          _ = ∑ a ∈ outUsers z π k σ, F.earn a := by rw [Finset.sum_ite_mem, Finset.univ_inter]
      have hSo : F.supply (Sum.inr (π, k, σ)) = gadgetSupply P t π k.val := supply_inr P t L π k σ
      rw [hSo] at hsum
      linarith
    refine ⟨r, hr, ?_⟩
    have hD := h72 _ _ hr hlt
    simp only [Designated] at hD
    rcases hD with ⟨hr0, h | h | h⟩ | ⟨hr1, h | h⟩ | ⟨hr2, h | h⟩
    · exact absurd h (inr_ne_firstIn L π k σ)
    · exact absurd h (inr_ne_secondIn L π k σ)
    · first
        | exact Or.inl ⟨h, hr0⟩
        | (simp only [Sum.inr.injEq, Prod.mk.injEq] at h; exact Or.inl ⟨h.2.2, hr0⟩)
    · exact absurd h (inr_ne_firstIn L π k σ)
    · first
        | exact Or.inr ⟨h, Or.inl hr1⟩
        | (simp only [Sum.inr.injEq, Prod.mk.injEq] at h; exact Or.inr ⟨h.2.2, Or.inl hr1⟩)
    · exact absurd h (inr_ne_secondIn L π k σ)
    · first
        | exact Or.inr ⟨h, Or.inr hr2⟩
        | (simp only [Sum.inr.injEq, Prod.mk.injEq] at h; exact Or.inr ⟨h.2.2, Or.inr hr2⟩)
  -- disutility values in a gadget
  have d0plus : ∀ (π : Pair n) (k : Fin L),
      F.disutil (Sum.inr (π, k, 0)) (Sum.inr (π, k, true)) = 1 := by
    intro π k
    rw [hFdef, dis_inr, if_pos rfl,
      if_neg (not_or.mpr ⟨inr_ne_firstIn L π k true, inr_ne_secondIn L π k true⟩), if_pos rfl]
  have d1minus : ∀ (π : Pair n) (k : Fin L),
      F.disutil (Sum.inr (π, k, 1)) (Sum.inr (π, k, false)) = 1 := by
    intro π k
    rw [hFdef, dis_inr, if_neg (by decide : (1 : Fin 3) ≠ 0), if_pos rfl,
      if_neg (inr_ne_firstIn L π k false), if_pos rfl]
  have d2minus : ∀ (π : Pair n) (k : Fin L),
      F.disutil (Sum.inr (π, k, 2)) (Sum.inr (π, k, false)) = 1 := by
    intro π k
    rw [hFdef, dis_inr, if_neg (by decide : (2 : Fin 3) ≠ 0), if_neg (by decide : (2 : Fin 3) ≠ 1),
      if_neg (inr_ne_secondIn L π k false), if_pos rfl]
  have d0ge : ∀ (π : Pair n) (k : Fin L) (ℓ : Chore n L), ℓ ≠ Sum.inr (π, k, true) →
      qPar t k.val ≤ F.disutil (Sum.inr (π, k, 0)) ℓ := by
    intro π k ℓ hℓ
    rw [hFdef, dis_inr, if_pos rfl]
    have hq := q_bounds ht ht' k.val
    have h1 : qPar t k.val ≤ (1 + t) ^ 2 := by nlinarith
    split_ifs <;> first | exact le_refl _ | exact h1 | (exfalso; exact hℓ ‹_›)
  have d1first : ∀ (π : Pair n) (k : Fin L),
      F.disutil (Sum.inr (π, k, 1)) (firstIn π k) = 1 / qPar t k.val := by
    intro π k
    rw [hFdef, dis_inr, if_neg (by decide : (1 : Fin 3) ≠ 0), if_pos rfl, if_pos rfl]
  have d2second : ∀ (π : Pair n) (k : Fin L),
      F.disutil (Sum.inr (π, k, 2)) (secondIn π k) = 1 / qPar t k.val := by
    intro π k
    rw [hFdef, dis_inr, if_neg (by decide : (2 : Fin 3) ≠ 0), if_neg (by decide : (2 : Fin 3) ≠ 1),
      if_pos rfl]
  have d0first : ∀ (π : Pair n) (k : Fin L),
      F.disutil (Sum.inr (π, k, 0)) (firstIn π k) = qPar t k.val := by
    intro π k
    rw [hFdef, dis_inr, if_pos rfl, if_pos (Or.inl rfl)]
  have d0second : ∀ (π : Pair n) (k : Fin L),
      F.disutil (Sum.inr (π, k, 0)) (secondIn π k) = qPar t k.val := by
    intro π k
    rw [hFdef, dis_inr, if_pos rfl, if_pos (Or.inr rfl)]
  have d1other : ∀ (π : Pair n) (k : Fin L) (ℓ : Chore n L), ℓ ≠ Sum.inr (π, k, false) →
      ℓ ≠ firstIn π k → F.disutil (Sum.inr (π, k, 1)) ℓ = (1 + t) ^ 2 := by
    intro π k ℓ h1 h2
    rw [hFdef, dis_inr, if_neg (by decide : (1 : Fin 3) ≠ 0), if_pos rfl, if_neg h2, if_neg h1]
  -- (7.7)
  have h77 : ∀ (π : Pair n) (k : Fin L), p (Sum.inr (π, k, true)) * qPar t k.val ≤ pmax p := by
    intro π k
    obtain ⟨ℓ, hℓne, hℓz, hℓ⟩ := O1 π k 0 true (d0plus π k)
    have hd := d0ge π k ℓ hℓne
    have hq := one_lt_q ht ht' k.val
    have hdpos := dis_pos P L ht ht' (Sum.inr (π, k, 0)) ℓ
    rw [le_div_iff₀ hdpos] at hℓ
    have h1 : p (Sum.inr (π, k, true)) * qPar t k.val ≤
        p (Sum.inr (π, k, true)) * F.disutil (Sum.inr (π, k, 0)) ℓ :=
      mul_le_mul_of_nonneg_left hd (hp _).le
    linarith [hle_max ℓ]
  have hpm_pos : 0 < pmax p := lt_of_lt_of_le (hp ℓmax) (hle_max ℓmax)
  have hpmin_pos : 0 < pmin p := by rw [hpmin]; exact hp ℓmin
  -- upper bound
  have upper : pmax p ≤ (1 + t) * qPar t 0 * p (Sum.inl 0) := by
    rcases hℓ : ℓmax with j | ⟨π, k, σ⟩
    · rw [hpmax, hℓ]
      have := (hbasic j).2
      have : (1 + t) * p (Sum.inl 0) ≤ (1 + t) * qPar t 0 * p (Sum.inl 0) := by
        have : 0 ≤ (1 + t) * p (Sum.inl 0) := by positivity
        nlinarith
      linarith
    · have hpe : p (Sum.inr (π, k, σ)) = pmax p := by rw [hpmax, hℓ]
      cases σ with
      | true =>
        exfalso
        have := h77 π k
        have hq := one_lt_q ht ht' k.val
        rw [hpe] at this
        nlinarith
      | false =>
        obtain ⟨ℓ, hℓne, hℓz, hℓ⟩ := O1 π k 1 false (d1minus π k)
        rw [hpe] at hℓ
        by_cases hfi : ℓ = firstIn π k
        · subst hfi
          rw [d1first, div_div_eq_mul_div, div_one] at hℓ
          by_cases hk0 : k.val = 0
          · rw [firstIn_zero L π k hk0] at hℓ
            have hb := (hbasic π.1.1).2
            have hqk : qPar t k.val = qPar t 0 := by rw [hk0]
            rw [hqk] at hℓ
            have : p (Sum.inl π.1.1) * qPar t 0 ≤ (1 + t) * p (Sum.inl 0) * qPar t 0 :=
              mul_le_mul_of_nonneg_right hb (by linarith)
            linarith
          · exfalso
            rw [firstIn_succ L π k hk0] at hℓ
            have h7 := h77 π ⟨k.val - 1, by omega⟩
            simp only at h7
            have hqlt : qPar t k.val < qPar t (k.val - 1) := by
              have := q_succ_lt ht ht' (k.val - 1)
              rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)] at this
            have hq1 := one_lt_q ht ht' k.val
            have hpu := hp (Sum.inr (π, ⟨k.val - 1, by omega⟩, true))
            nlinarith
        · exfalso
          rw [d1other π k ℓ hℓne hfi] at hℓ
          have h1 := hle_max ℓ
          have h2 : p ℓ / (1 + t) ^ 2 < pmax p := by
            rw [div_lt_iff₀ (by positivity)]
            have h3 : (1 : ℝ) < (1 + t) ^ 2 := by nlinarith
            have h4 : pmax p < pmax p * (1 + t) ^ 2 := lt_mul_of_one_lt_right hpm_pos h3
            linarith
          linarith
  -- lower bound
  have lower : p (Sum.inl 0) / qPar t 0 ≤ pmin p := by
    by_contra hlt
    push Not at hlt
    have hq0' : p (Sum.inl 0) / qPar t 0 < p (Sum.inl 0) :=
      div_lt_self hp0 hq0
    rcases hℓ : ℓmin with j | ⟨π, k, σ⟩
    · rw [hpmin, hℓ] at hlt
      have := (hbasic j).1
      linarith
    · have hpe : p (Sum.inr (π, k, σ)) = pmin p := by rw [hpmin, hℓ]
      have hltmax : p (Sum.inr (π, k, σ)) < pmax p := by
        rw [hpe]; have := hle_max (Sum.inl 0); linarith
      obtain ⟨r, hrz, hrσ⟩ := O2 π k σ hltmax
      have hqk := one_lt_q ht ht' k.val
      rcases hrσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
      · -- a^max uses its plus output at the minimum price
        have hopt := optimal hF hCE hrz (secondIn π k)
        rw [d0second, d0plus, div_one, hpe, div_le_iff₀ (by linarith)] at hopt
        have hqle := q_le_q0 ht ht' k.val
        -- the second input costs less than p₀
        have hin_lt : p (secondIn π k) < p (Sum.inl 0) := by
          have : pmin p * qPar t k.val < p (Sum.inl 0) := by
            have h1 : pmin p * qPar t k.val ≤ pmin p * qPar t 0 :=
              mul_le_mul_of_nonneg_left hqle hpmin_pos.le
            have h2 : pmin p * qPar t 0 < p (Sum.inl 0) := by
              rwa [lt_div_iff₀ (by linarith)] at hlt
            linarith
          linarith
        by_cases hk0 : k.val = 0
        · rw [secondIn_zero L π k hk0] at hin_lt
          have := (hbasic π.1.2).1
          linarith
        · rw [secondIn_succ L π k hk0] at hin_lt hopt
          set k' : Fin L := ⟨k.val - 1, by omega⟩
          have hlt2 : p (Sum.inr (π, k', false)) < pmax p := by
            have := hle_max (Sum.inl 0); linarith
          obtain ⟨r', hr'z, hr'σ⟩ := O2 π k' false hlt2
          have hqlt : qPar t k.val < qPar t k'.val := by
            have := q_succ_lt ht ht' (k.val - 1)
            rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)] at this
          rcases hr'σ with ⟨h, -⟩ | ⟨-, rfl | rfl⟩
          · exact absurd h (by simp)
          · have hopt2 := optimal hF hCE hr'z (firstIn π k')
            rw [d1first, d1minus, div_one, div_div_eq_mul_div, div_one] at hopt2
            have := hge_min (firstIn π k')
            nlinarith
          · have hopt2 := optimal hF hCE hr'z (secondIn π k')
            rw [d2second, d2minus, div_one, div_div_eq_mul_div, div_one] at hopt2
            have := hge_min (secondIn π k')
            nlinarith
      · have hopt := optimal hF hCE hrz (firstIn π k)
        rw [d1first, d1minus, div_one, div_div_eq_mul_div, div_one, hpe] at hopt
        have := hge_min (firstIn π k)
        nlinarith
      · have hopt := optimal hF hCE hrz (secondIn π k)
        rw [d2second, d2minus, div_one, div_div_eq_mul_div, div_one, hpe] at hopt
        have := hge_min (secondIn π k)
        nlinarith
  refine ⟨upper, lower, ?_⟩
  -- no undesignated choices
  intro a ℓ hz
  by_contra hnd
  have hℓmax : p ℓ = pmax p := by
    by_contra hne
    exact hnd (h72 a ℓ hz (lt_of_le_of_ne (hle_max ℓ) hne))
  have hd := dis_undesignated P t L a ℓ hnd
  -- a designated chore with disutility one
  obtain ⟨s, hs⟩ : ∃ s, F.disutil a s = 1 := by
    rcases a with i | ⟨π, k, r⟩
    · exact ⟨Sum.inl 0, by rw [hFdef, dis_inl_inl]; simp⟩
    · fin_cases r
      · exact ⟨_, d0plus π k⟩
      · exact ⟨_, d1minus π k⟩
      · exact ⟨_, d2minus π k⟩
  have hopt := optimal hF hCE hz s
  rw [hs, div_one, hd, hℓmax] at hopt
  have h1 := hge_min s
  have hq0sq : qPar t 0 * qPar t 0 < 1 + t := by
    have := q_bounds ht ht' 0
    nlinarith
  -- pmax ≤ (1+t) q₀² pmin < (1+t)² pmin ≤ pmax
  have h2 : pmax p ≤ (1 + t) * (qPar t 0 * qPar t 0) * pmin p := by
    have h3 : p (Sum.inl 0) ≤ qPar t 0 * pmin p := by
      rwa [div_le_iff₀ (by linarith), mul_comm] at lower
    have : (1 + t) * qPar t 0 * p (Sum.inl 0) ≤ (1 + t) * qPar t 0 * (qPar t 0 * pmin p) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    nlinarith
  have h4 : (1 + t) ^ 2 * pmin p ≤ pmax p := by
    rw [le_div_iff₀ (by positivity)] at hopt
    nlinarith
  have h5 : (1 + t) * (qPar t 0 * qPar t 0) * pmin p < (1 + t) ^ 2 * pmin p := by
    have : (1 + t) * (qPar t 0 * qPar t 0) < (1 + t) ^ 2 := by nlinarith
    nlinarith
  linarith

end ChoresMkt

open ChoresMkt in
theorem solution {n : ℕ} (hn : 0 < n) (P : Quadratic n) (ε : ℚ) (hε : 0 < ε)
    (p : Chore n (chainLength P ε) → ℝ) (z : Agent n (chainLength P ε) → Chore n (chainLength P ε) → ℝ)
    (hCE : (completedMarket P ε).IsCE p z) :
    pmax p ≤ (1 + tParam P ε) * qPar (tParam P ε) 0 * p (Sum.inl 0) ∧
      p (Sum.inl 0) / qPar (tParam P ε) 0 ≤ pmin p ∧
      ∀ a ℓ, 0 < z a ℓ → Designated a ℓ := by
  obtain ⟨ht, ht'⟩ := t_facts P ε
  exact core74 P (chainLength P ε) ht ht' p z hCE
