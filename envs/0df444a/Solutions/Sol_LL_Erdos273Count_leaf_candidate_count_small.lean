-- Prove2me | solution 1 for LL_Erdos273Count.leaf_candidate_count_small
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T00:07:21.729323+00:00
-- url     : https://prove2.me/submissions/8e6ee9ce-a943-4df0-8f80-c5633ccf1f4b

import Mathlib

namespace LL_Erdos273Count_Work

def erdos3List : List Nat := [3, 5, 7]

def erdos10List : List Nat := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

def erdos40List : List Nat :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
   73, 79, 83, 89, 97, 101, 103, 109, 131, 163, 173, 179, 181, 191, 199,
   229, 233, 239, 307, 547, 557]

def passList (v : Nat) : List Nat → Bool
  | [] => true
  | q :: qs =>
    Bool.and (Bool.or (Nat.beq v q) (!(Nat.beq (Nat.mod v q) 0))) (passList v qs)

def candPred3 (m : Nat) : Bool :=
  Bool.and (Nat.ble 2 m) (passList (Nat.add (Nat.mul 2 m) 1) erdos3List)

def candPred10 (m : Nat) : Bool :=
  Bool.and (Nat.ble 2 m) (passList (Nat.add (Nat.mul 2 m) 1) erdos10List)

def candPred40 (m : Nat) : Bool :=
  Bool.and (Nat.ble 2 m) (passList (Nat.add (Nat.mul 2 m) 1) erdos40List)

def sumOverPow (f : Nat → Nat) (p : Nat) : Nat → Nat → Nat
  | 0, m => f m
  | e + 1, m => Nat.add (f m) (sumOverPow f p e (Nat.mul m p))

def countFactors (pred : Nat → Bool) : List (Nat × Nat) → Nat → Nat
  | [], m => if pred m then 1 else 0
  | (p, e) :: fs, m => sumOverPow (countFactors pred fs) p e m

def checkHit (facs : List (Nat × Nat)) : Bool :=
  Bool.or (Nat.ble (countFactors candPred3 facs 1) 99)
    (Bool.or (Nat.ble (countFactors candPred10 facs 1) 99)
      (Nat.ble (countFactors candPred40 facs 1) 99))

def primes193 : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
   73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
   157, 163, 167, 173, 179, 181, 191, 193]

def maxTauGo (p B : Nat) : Nat → Nat → Nat → Nat
  | 0, _, mult => mult
  | fuel + 1, pk, mult =>
    if Nat.ble pk B then maxTauGo p B fuel (Nat.mul pk p) (Nat.mul mult 2) else mult

def loopPow (step : Nat → Nat → List (Nat × Nat) → Bool) (p baseTau : Nat)
    (baseFacs : List (Nat × Nat)) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | fuel + 1, e, pe =>
    if Nat.ble (Nat.add pe 1) 982800 then
      Bool.and (step pe (Nat.mul baseTau (Nat.add e 1)) ((p, e) :: baseFacs))
        (loopPow step p baseTau baseFacs fuel (Nat.add e 1) (Nat.mul pe p))
    else true

def walkTree : List Nat → Nat → Nat → List (Nat × Nat) → Bool
  | [], curr, curTau, facs =>
    if Bool.and (Nat.ble 491400 curr) (Nat.ble 100 curTau) then checkHit facs else true
  | p :: ps, curr, curTau, facs =>
    if Nat.ble 982800 (Nat.mul curr p) then
      if Bool.and (Nat.ble 491400 curr) (Nat.ble 100 curTau) then checkHit facs else true
    else
      let B := Nat.div 982799 curr
      if Nat.ble (Nat.add (Nat.mul curTau (maxTauGo p B 20 p 1)) 1) 100 then true
      else
        Bool.and (walkTree ps curr curTau facs)
          (loopPow (walkTree ps) p curTau facs 20 1 (Nat.mul curr p))

def countSqrtDivs (u : Nat) : Nat → Nat
  | 0 => 0
  | d + 1 =>
    let d1 := Nat.add d 1
    let c := if Bool.and (Nat.ble (Nat.mul d1 d1) u) (Nat.beq (Nat.mod u d1) 0) then 1 else 0
    Nat.add c (countSqrtDivs u d)

def checkSmallUInner (b : Nat) : Nat → Bool
  | 0 => true
  | j + 1 =>
    let u := Nat.add (Nat.mul 100 b) (Nat.add j 1)
    Bool.and (if Nat.ble u 4988 then Nat.ble (countSqrtDivs u 70) 24 else true)
      (checkSmallUInner b j)

def checkSmallUOuter : Nat → Bool
  | 0 => true
  | b + 1 => Bool.and (checkSmallUInner b 100) (checkSmallUOuter b)

-- Certified finite kernel checks
lemma erdos3_ge_2 : ∀ q ∈ erdos3List, 2 ≤ q := by decide +kernel
lemma erdos10_ge_2 : ∀ q ∈ erdos10List, 2 ≤ q := by decide +kernel
lemma erdos40_ge_2 : ∀ q ∈ erdos40List, 2 ≤ q := by decide +kernel
lemma primes193_prime : ∀ p ∈ primes193, p.Prime := by decide +kernel
lemma primes193_sorted : primes193.Pairwise (· < ·) := by decide +kernel
lemma mem_primes193_of_le : ∀ q ∈ Finset.range 197, q.Prime → q ∈ primes193 := by decide +kernel
lemma small_tau_25 : ∀ u ∈ Finset.Icc 1 25, u.divisors.card ≤ 8 := by decide +kernel
lemma small_u_cert : checkSmallUOuter 50 = true := by decide +kernel
lemma erdos_tree_cert : walkTree primes193 1 1 [] = true := by decide +kernel

-- Helper lemmas for divisor expansion
def expandPow (f : Nat → List Nat) (p : Nat) : Nat → Nat → List Nat
  | 0, m => f m
  | e + 1, m => f m ++ expandPow f p e (Nat.mul m p)

def expandFacs : List (Nat × Nat) → Nat → List Nat
  | [], m => [m]
  | (p, e) :: fs, m => expandPow (expandFacs fs) p e m

lemma sumOverPow_eq_countP (pred : ℕ → Bool) (fs : List (ℕ × ℕ))
    (ih : ∀ m, countFactors pred fs m = (expandFacs fs m).countP pred) (p : ℕ) :
    ∀ e m, sumOverPow (countFactors pred fs) p e m =
      (expandPow (expandFacs fs) p e m).countP pred
  | 0, m => by simp [sumOverPow, expandPow, ih]
  | e + 1, m => by
    simp only [sumOverPow, expandPow, List.countP_append]
    rw [ih m, sumOverPow_eq_countP pred fs ih p e (Nat.mul m p)]
    rfl

lemma countFactors_eq_countP (pred : ℕ → Bool) :
    ∀ fs m, countFactors pred fs m = (expandFacs fs m).countP pred
  | [], m => by simp [countFactors, expandFacs]
  | (p, e) :: fs, m => by
    simp only [countFactors, expandFacs]
    exact sumOverPow_eq_countP pred fs (countFactors_eq_countP pred fs) p e m

lemma mem_expandPow_of_pow {f : ℕ → List ℕ} {curr : ℕ}
    (hf : ∀ m d, d ∣ curr → m * d ∈ f m) (p : ℕ) :
    ∀ e j m d₁, j ≤ e → d₁ ∣ curr → m * (d₁ * p ^ j) ∈ expandPow f p e m
  | e, 0, m, d₁, _, hd₁ => by
    cases e with
    | zero => simpa [expandPow] using hf m d₁ hd₁
    | succ e' =>
      simp only [expandPow, pow_zero, mul_one]
      exact List.mem_append_left _ (hf m d₁ hd₁)
  | 0, j + 1, _, _, hj, _ => by omega
  | e + 1, j + 1, m, d₁, hj, hd₁ => by
    simp only [expandPow]
    apply List.mem_append_right
    have hj' : j ≤ e := by omega
    have hmem := mem_expandPow_of_pow hf p e j (Nat.mul m p) d₁ hj' hd₁
    have heq : Nat.mul m p * (d₁ * p ^ j) = m * (d₁ * p ^ (j + 1)) := by
      change (m * p) * (d₁ * p ^ j) = m * (d₁ * p ^ (j + 1))
      rw [pow_succ]
      ring
    rwa [heq] at hmem

lemma mem_expandFacs_step {fs : List (ℕ × ℕ)} {curr : ℕ}
    (hfs : ∀ m d, d ∣ curr → m * d ∈ expandFacs fs m) {p e : ℕ} (hp : p.Prime) :
    ∀ m d, d ∣ curr * p ^ e → m * d ∈ expandFacs ((p, e) :: fs) m := by
  intro m d hd
  rcases Nat.dvd_mul.mp hd with ⟨d₁, d₂, hd₁, hd₂, rfl⟩
  rcases (Nat.dvd_prime_pow hp).mp hd₂ with ⟨j, hje, rfl⟩
  exact mem_expandPow_of_pow hfs p e j m d₁ hje hd₁

lemma prime_passList {v : ℕ} (hv : v.Prime) :
    ∀ qs : List ℕ, (∀ q ∈ qs, 2 ≤ q) → passList v qs = true
  | [], _ => rfl
  | q :: qs, hqs => by
    have hq2 : 2 ≤ q := hqs q List.mem_cons_self
    have hfirst : Bool.or (Nat.beq v q) (!(Nat.beq (Nat.mod v q) 0)) = true := by
      by_cases hveq : v = q
      · simp [hveq]
      · have hndvd : ¬ (q ∣ v) := by
          intro hd
          rcases hv.eq_one_or_self_of_dvd q hd with rfl | rfl <;> omega
        have hmod : Nat.mod v q ≠ 0 := fun hm => hndvd (Nat.dvd_of_mod_eq_zero hm)
        have hbeq : Nat.beq (Nat.mod v q) 0 = false :=
          Bool.eq_false_iff.mpr (fun h => hmod (Nat.beq_eq.mp h))
        simp [hbeq]
    simp only [passList, hfirst, Bool.true_and]
    exact prime_passList hv qs (fun r hr => hqs r (List.mem_cons_of_mem _ hr))

def candFinset (N : ℕ) : Finset ℕ :=
  N.divisors.filter (fun m => 2 ≤ m ∧ (2 * m + 1).Prime)

lemma card_candFinset_le_countFactors {N : ℕ} {facs : List (ℕ × ℕ)}
    (hfacs : ∀ m d, d ∣ N → m * d ∈ expandFacs facs m)
    {pred : ℕ → Bool}
    (hpred : ∀ m, 2 ≤ m → (2 * m + 1).Prime → pred m = true) :
    (candFinset N).card ≤ countFactors pred facs 1 := by
  rw [countFactors_eq_countP, List.countP_eq_length_filter]
  set L := (expandFacs facs 1).filter pred
  have hsub : candFinset N ⊆ L.toFinset := by
    intro m hm
    simp only [candFinset, Finset.mem_filter, Nat.mem_divisors] at hm
    rcases hm with ⟨⟨hdvd, _⟩, hm2, hp⟩
    rw [List.mem_toFinset, List.mem_filter]
    refine ⟨?_, hpred m hm2 hp⟩
    simpa using hfacs 1 m hdvd
  exact le_trans (Finset.card_le_card hsub) (List.toFinset_card_le L)

lemma card_candFinset_lt_of_checkHit {N : ℕ} {facs : List (ℕ × ℕ)}
    (hfacs : ∀ m d, d ∣ N → m * d ∈ expandFacs facs m)
    (hchk : checkHit facs = true) :
    (candFinset N).card < 100 := by
  simp only [checkHit, Bool.or_eq_true, Nat.ble_eq] at hchk
  rcases hchk with h3 | h10 | h40
  · have hle : (candFinset N).card ≤ countFactors candPred3 facs 1 := by
      refine card_candFinset_le_countFactors hfacs fun m hm2 hp => ?_
      simp only [candPred3, Bool.and_eq_true, Nat.ble_eq]
      exact ⟨hm2, prime_passList hp erdos3List erdos3_ge_2⟩
    omega
  · have hle : (candFinset N).card ≤ countFactors candPred10 facs 1 := by
      refine card_candFinset_le_countFactors hfacs fun m hm2 hp => ?_
      simp only [candPred10, Bool.and_eq_true, Nat.ble_eq]
      exact ⟨hm2, prime_passList hp erdos10List erdos10_ge_2⟩
    omega
  · have hle : (candFinset N).card ≤ countFactors candPred40 facs 1 := by
      refine card_candFinset_le_countFactors hfacs fun m hm2 hp => ?_
      simp only [candPred40, Bool.and_eq_true, Nat.ble_eq]
      exact ⟨hm2, prime_passList hp erdos40List erdos40_ge_2⟩
    omega

-- Multiplicative upper bound on divisor count for pruning
lemma card_divisors_mul_le {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  rw [← Finset.card_product]
  let f : ℕ → ℕ × ℕ := fun d => (Nat.gcd d a, d / Nat.gcd d a)
  refine Finset.card_le_card_of_injOn f (fun d hd => ?_) (fun d₁ _ d₂ _ heq => ?_)
  · rw [Finset.mem_coe, Nat.mem_divisors] at hd
    rcases hd with ⟨hdvd, _⟩
    set g := Nat.gcd d a
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right d ha
    have hga : g ∣ a := Nat.gcd_dvd_right d a
    have hgd : g ∣ d := Nat.gcd_dvd_left d a
    rw [Finset.mem_coe]
    refine Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hga, ha.ne'⟩,
      Nat.mem_divisors.mpr ⟨?_, hb.ne'⟩⟩
    have hcop : Nat.Coprime (d / g) (a / g) := Nat.coprime_div_gcd_div_gcd hg_pos
    have hmul_eq : g * (d / g) = d := Nat.mul_div_cancel' hgd
    have ha_eq : g * (a / g) = a := Nat.mul_div_cancel' hga
    have hdvd' : g * (d / g) ∣ g * ((a / g) * b) := by
      rw [hmul_eq, ← mul_assoc, ha_eq]
      exact hdvd
    have hdvd'' : d / g ∣ (a / g) * b := (Nat.mul_dvd_mul_iff_left hg_pos).mp hdvd'
    exact hcop.dvd_of_dvd_mul_left hdvd''
  · dsimp [f] at heq
    injection heq with hg hq
    have h1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left d₁ a)
    have h2 := Nat.mul_div_cancel' (Nat.gcd_dvd_left d₂ a)
    rw [hq, hg] at h1
    omega

lemma exists_pow_and_divisors_le {p : ℕ} :
    ∀ R : ℕ, 0 < R → (∀ q, q.Prime → q ∣ R → p ≤ q) →
      ∃ k : ℕ, p ^ k ≤ R ∧ R.divisors.card ≤ 2 ^ k := by
  intro R
  induction R using Nat.strong_induction_on with
  | h R ih =>
    intro hR_pos hprimes
    by_cases hR1 : R = 1
    · subst hR1
      exact ⟨0, by simp, by simp⟩
    · set q := R.minFac
      have hqp : q.Prime := Nat.minFac_prime hR1
      have hqdvd : q ∣ R := Nat.minFac_dvd R
      have hpq : p ≤ q := hprimes q hqp hqdvd
      set R' := R / q
      have hR_eq : q * R' = R := Nat.mul_div_cancel' hqdvd
      have hR'_pos : 0 < R' := Nat.div_pos (Nat.le_of_dvd hR_pos hqdvd) hqp.pos
      have hR'_lt : R' < R := Nat.div_lt_self hR_pos hqp.one_lt
      have hR'_primes : ∀ r, r.Prime → r ∣ R' → p ≤ r :=
        fun r hr hrd => hprimes r hr (dvd_trans hrd ⟨q, hR_eq.symm.trans (mul_comm _ _)⟩)
      obtain ⟨k', hpk', htau'⟩ := ih R' hR'_lt hR'_pos hR'_primes
      refine ⟨k' + 1, ?_, ?_⟩
      · calc
          p ^ (k' + 1) = p * p ^ k' := by rw [pow_succ']
          _ ≤ q * R' := Nat.mul_le_mul hpq hpk'
          _ = R := hR_eq
      · have hq_card : q.divisors.card = 2 := by
          rw [hqp.divisors, Finset.card_pair hqp.one_lt.ne]
        calc
          R.divisors.card = (q * R').divisors.card := by rw [hR_eq]
          _ ≤ q.divisors.card * R'.divisors.card := card_divisors_mul_le hqp.pos hR'_pos
          _ = 2 * R'.divisors.card := by rw [hq_card]
          _ ≤ 2 * 2 ^ k' := Nat.mul_le_mul_left 2 htau'
          _ = 2 ^ (k' + 1) := by rw [pow_succ']

lemma le_maxTauGo_self (p B : ℕ) : ∀ fuel pk mult, mult ≤ maxTauGo p B fuel pk mult
  | 0, _, mult => le_rfl
  | fuel + 1, pk, mult => by
    simp only [maxTauGo]
    split_ifs
    · exact le_trans (show mult ≤ Nat.mul mult 2 by change mult ≤ mult * 2; omega)
        (le_maxTauGo_self p B fuel (Nat.mul pk p) (Nat.mul mult 2))
    · exact le_rfl

lemma pow_le_maxTauGo (p B : ℕ) :
    ∀ fuel j pk mult, j ≤ fuel → (∀ i < j, pk * p ^ i ≤ B) →
      mult * 2 ^ j ≤ maxTauGo p B fuel pk mult
  | fuel, 0, pk, mult, _, _ => by
    simpa using le_maxTauGo_self p B fuel pk mult
  | 0, j + 1, _, _, hj, _ => by omega
  | fuel + 1, j + 1, pk, mult, hj, hle => by
    simp only [maxTauGo]
    have h0 : pk ≤ B := by simpa using hle 0 (by omega)
    have hble : Nat.ble pk B = true := Nat.ble_eq.mpr h0
    simp only [hble, ↓reduceIte]
    have ih := pow_le_maxTauGo p B fuel j (Nat.mul pk p) (Nat.mul mult 2) (by omega) ?_
    · calc
        mult * 2 ^ (j + 1) = (Nat.mul mult 2) * 2 ^ j := by
          change mult * 2 ^ (j + 1) = (mult * 2) * 2 ^ j
          rw [pow_succ']
          ring
        _ ≤ maxTauGo p B fuel (Nat.mul pk p) (Nat.mul mult 2) := ih
    · intro i hi
      have hi1 := hle (i + 1) (by omega)
      calc
        Nat.mul pk p * p ^ i = pk * p ^ (i + 1) := by
          change (pk * p) * p ^ i = pk * p ^ (i + 1)
          rw [pow_succ']
          ring
        _ ≤ B := hi1

lemma card_divisors_le_maxTauGo {R p B : ℕ} (hR : 0 < R) (hRB : R ≤ B) (hB : B ≤ 982799)
    (hp2 : 2 ≤ p) (hprimes : ∀ q, q.Prime → q ∣ R → p ≤ q) :
    R.divisors.card ≤ maxTauGo p B 20 p 1 := by
  obtain ⟨k, hpk, htau⟩ := exists_pow_and_divisors_le R hR hprimes
  have hk20 : k ≤ 20 := by
    by_contra hgt
    have hk21 : 20 ≤ k := by omega
    have h2_20 : 2 ^ 20 ≤ p ^ k := le_trans (Nat.pow_le_pow_left hp2 20)
      (Nat.pow_le_pow_right (by omega) hk21)
    have : 2 ^ 20 ≤ 982799 := le_trans h2_20 (le_trans hpk (le_trans hRB hB))
    norm_num at this
  refine le_trans htau ?_
  simpa using pow_le_maxTauGo p B 20 k p 1 hk20 (fun i hi => by
    calc
      p * p ^ i = p ^ (i + 1) := by rw [pow_succ']
      _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ B := le_trans hpk hRB)

lemma extract_prime_pow {n q : ℕ} (hn : 0 < n) (hq : q.Prime) :
    ∃ e u : ℕ, n = q ^ e * u ∧ 0 < u ∧ ¬ (q ∣ u) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hdvd : q ∣ n
    · set m := n / q
      have hqm : q * m = n := Nat.mul_div_cancel' hdvd
      have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hn hdvd) hq.pos
      have hm_lt : m < n := Nat.div_lt_self hn hq.one_lt
      obtain ⟨e', u, hm_eq, hu_pos, hndvd⟩ := ih m hm_lt hm_pos
      refine ⟨e' + 1, u, ?_, hu_pos, hndvd⟩
      rw [pow_succ', mul_assoc, ← hm_eq, hqm]
    · exact ⟨0, n, by simp, hn, hdvd⟩

lemma loopPow_extract (step : ℕ → ℕ → List (ℕ × ℕ) → Bool) {p : ℕ} (hp_pos : 0 < p)
    (baseTau : ℕ) (baseFacs : List (ℕ × ℕ)) :
    ∀ fuel e0 pe0 j, j < fuel → pe0 * p ^ j < 982800 →
      loopPow step p baseTau baseFacs fuel e0 pe0 = true →
      step (pe0 * p ^ j) (baseTau * (e0 + j + 1)) ((p, e0 + j) :: baseFacs) = true
  | 0, _, _, _, hj, _, _ => by omega
  | fuel + 1, e0, pe0, 0, _, hlt, hloop => by
    simp only [loopPow] at hloop
    have hble : Nat.ble (Nat.add pe0 1) 982800 = true := by
      rw [Nat.ble_eq]
      change pe0 + 1 ≤ 982800
      simpa using hlt
    simp only [hble, ↓reduceIte, Bool.and_eq_true] at hloop
    simpa using hloop.1
  | fuel + 1, e0, pe0, j + 1, hj, hlt, hloop => by
    simp only [loopPow] at hloop
    have hp_pow : 1 ≤ p ^ (j + 1) := Nat.one_le_pow _ _ hp_pos
    have hpe0_lt : pe0 < 982800 := by nlinarith
    have hble : Nat.ble (Nat.add pe0 1) 982800 = true := by
      rw [Nat.ble_eq]
      change pe0 + 1 ≤ 982800
      omega
    simp only [hble, ↓reduceIte, Bool.and_eq_true] at hloop
    have hlt' : Nat.mul pe0 p * p ^ j < 982800 := by
      calc
        Nat.mul pe0 p * p ^ j = pe0 * p ^ (j + 1) := by
          change (pe0 * p) * p ^ j = pe0 * p ^ (j + 1)
          rw [pow_succ']
          ring
        _ < 982800 := hlt
    have ih := loopPow_extract step hp_pos baseTau baseFacs fuel (Nat.add e0 1) (Nat.mul pe0 p) j
      (by omega) hlt' hloop.2
    have h1 : Nat.mul pe0 p * p ^ j = pe0 * p ^ (j + 1) := by
      change (pe0 * p) * p ^ j = pe0 * p ^ (j + 1)
      rw [pow_succ']
      ring
    have h2 : Nat.add e0 1 + j = e0 + (j + 1) := by
      change (e0 + 1) + j = e0 + (j + 1)
      omega
    rwa [h1, h2] at ih

lemma walkTree_sound :
    ∀ (ps : List ℕ), ps.Pairwise (· < ·) → (∀ p ∈ ps, p.Prime) →
      ∀ (curr curTau : ℕ) (facs : List (ℕ × ℕ)) (R : ℕ),
        walkTree ps curr curTau facs = true →
        0 < curr → 0 < R → Nat.Coprime curr R →
        491400 ≤ curr * R → curr * R < 982800 →
        100 ≤ (curr * R).divisors.card →
        curTau = curr.divisors.card →
        (∀ m d, d ∣ curr → m * d ∈ expandFacs facs m) →
        (∀ q, q.Prime → q ∣ R → q ∈ ps) →
        (candFinset (curr * R)).card < 100
  | [], _, _, curr, curTau, facs, R, hw, _, _, _, hlo, _, htau, hcurTau, hfacs, hRp => by
    have hR1 : R = 1 := by
      by_contra hne
      obtain ⟨q, hqp, hqd⟩ := Nat.exists_prime_and_dvd hne
      simpa using hRp q hqp hqd
    subst hR1
    simp only [mul_one] at hlo htau ⊢
    simp only [walkTree] at hw
    have hcond : Bool.and (Nat.ble 491400 curr) (Nat.ble 100 curTau) = true := by
      simp [Bool.and_eq_true, Nat.ble_eq, hlo, hcurTau, htau]
    simp only [hcond, ↓reduceIte] at hw
    exact card_candFinset_lt_of_checkHit hfacs hw
  | p :: ps, hpair, hps_prime, curr, curTau, facs, R, hw, hcurr, hR, hcop, hlo, hhi, htau,
      hcurTau, hfacs, hRp => by
    rw [List.pairwise_cons] at hpair
    rcases hpair with ⟨hp_lt_ps, hps_pair⟩
    have hp_prime : p.Prime := hps_prime p List.mem_cons_self
    have hps_prime' : ∀ q ∈ ps, q.Prime := fun q hq => hps_prime q (List.mem_cons_of_mem _ hq)
    have hR_min : ∀ q, q.Prime → q ∣ R → p ≤ q := by
      intro q hqp hqd
      rcases List.mem_cons.mp (hRp q hqp hqd) with rfl | hmem
      · exact le_rfl
      · exact (hp_lt_ps q hmem).le
    simp only [walkTree] at hw
    by_cases hbig : Nat.ble 982800 (Nat.mul curr p) = true
    · simp only [hbig, ↓reduceIte] at hw
      have hbig' : 982800 ≤ curr * p := Nat.ble_eq.mp hbig
      have hR1 : R = 1 := by
        by_contra hne
        obtain ⟨q, hqp, hqd⟩ := Nat.exists_prime_and_dvd hne
        have hpq : p ≤ q := hR_min q hqp hqd
        have hqR : q ≤ R := Nat.le_of_dvd hR hqd
        have : curr * p ≤ curr * R := Nat.mul_le_mul_left curr (le_trans hpq hqR)
        omega
      subst hR1
      simp only [mul_one] at hlo htau ⊢
      have hcond : Bool.and (Nat.ble 491400 curr) (Nat.ble 100 curTau) = true := by
        simp [Bool.and_eq_true, Nat.ble_eq, hlo, hcurTau, htau]
      simp only [hcond, ↓reduceIte] at hw
      exact card_candFinset_lt_of_checkHit hfacs hw
    · have hbig_f : Nat.ble 982800 (Nat.mul curr p) = false :=
        Bool.eq_false_iff.mpr hbig
      simp only [hbig_f, Bool.false_eq_true, ↓reduceIte] at hw
      set B := Nat.div 982799 curr
      by_cases hprune : Nat.ble (Nat.add (Nat.mul curTau (maxTauGo p B 20 p 1)) 1) 100 = true
      · exfalso
        have hprune' : curTau * maxTauGo p B 20 p 1 + 1 ≤ 100 := Nat.ble_eq.mp hprune
        have hRB : R ≤ B := by
          change R ≤ 982799 / curr
          exact (Nat.le_div_iff_mul_le hcurr).mpr (by rw [mul_comm]; omega)
        have hB_le : B ≤ 982799 := Nat.div_le_self 982799 curr
        have hR_tau : R.divisors.card ≤ maxTauGo p B 20 p 1 :=
          card_divisors_le_maxTauGo hR hRB hB_le hp_prime.two_le hR_min
        have htot_tau : (curr * R).divisors.card = curTau * R.divisors.card := by
          rw [hcop.card_divisors_mul, hcurTau]
        have : (curr * R).divisors.card ≤ curTau * maxTauGo p B 20 p 1 := by
          rw [htot_tau]
          exact Nat.mul_le_mul_left curTau hR_tau
        omega
      · have hprune_f :
            Nat.ble (Nat.add (Nat.mul curTau (maxTauGo p B 20 p 1)) 1) 100 = false :=
          Bool.eq_false_iff.mpr hprune
        simp only [hprune_f, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hw
        rcases hw with ⟨hw0, hw_pow⟩
        obtain ⟨e, R', hR_eq, hR'_pos, hndvd_p⟩ := extract_prime_pow hR hp_prime
        have hR'_primes : ∀ q, q.Prime → q ∣ R' → q ∈ ps := by
          intro q hqp hqd
          have hqR : q ∣ R := by
            rw [hR_eq]
            exact dvd_mul_of_dvd_right hqd _
          rcases List.mem_cons.mp (hRp q hqp hqR) with rfl | hmem
          · exact False.elim (hndvd_p hqd)
          · exact hmem
        cases e with
        | zero =>
          simp only [pow_zero, one_mul] at hR_eq
          rw [← hR_eq] at hR'_pos hR'_primes
          exact walkTree_sound ps hps_pair hps_prime' curr curTau facs R hw0 hcurr hR
            hcop hlo hhi htau hcurTau hfacs hR'_primes
        | succ j =>
          have hcop_curr_pe : Nat.Coprime curr (p ^ (j + 1)) := by
            have hdvd_pe : p ^ (j + 1) ∣ R := ⟨R', hR_eq⟩
            exact hcop.coprime_dvd_right hdvd_pe
          have hcop_curr_R' : Nat.Coprime curr R' := by
            have hdvd_R' : R' ∣ R := ⟨p ^ (j + 1), by rw [hR_eq, mul_comm]⟩
            exact hcop.coprime_dvd_right hdvd_R'
          have hcop_pe_R' : Nat.Coprime (p ^ (j + 1)) R' :=
            (hp_prime.coprime_iff_not_dvd.mpr hndvd_p).pow_left (j + 1)
          set curr' := curr * p ^ (j + 1)
          have hcurr'_R' : curr' * R' = curr * R := by
            dsimp [curr']
            rw [mul_assoc, ← hR_eq]
          have hcurr'_lt : curr' < 982800 := by
            have : curr' ≤ curr * R := by
              rw [← hcurr'_R']
              exact Nat.le_mul_of_pos_right _ hR'_pos
            omega
          have hj_lt20 : j < 20 := by
            by_contra hge
            have hj20 : 20 ≤ j + 1 := by omega
            have h2_20 : 2 ^ 20 ≤ p ^ (j + 1) := le_trans (Nat.pow_le_pow_left hp_prime.two_le 20)
              (Nat.pow_le_pow_right hp_prime.pos hj20)
            have : p ^ (j + 1) ≤ curr' := Nat.le_mul_of_pos_left _ hcurr
            have : 2 ^ 20 < 982800 := lt_of_le_of_lt (le_trans h2_20 this) hcurr'_lt
            norm_num at this
          have hpe_eq : Nat.mul curr p * p ^ j = curr' := by
            dsimp [curr']
            change (curr * p) * p ^ j = curr * p ^ (j + 1)
            rw [pow_succ']
            ring
          have hw_step := loopPow_extract (walkTree ps) hp_prime.pos curTau facs 20 1
            (Nat.mul curr p) j hj_lt20 (by rwa [hpe_eq]) hw_pow
          rw [hpe_eq, show 1 + j = j + 1 by omega] at hw_step
          have hcurTau' : curTau * (j + 1 + 1) = curr'.divisors.card := by
            dsimp [curr']
            rw [hcop_curr_pe.card_divisors_mul, hcurTau, Nat.divisors_prime_pow hp_prime,
              Finset.card_map, Finset.card_range]
          have hfacs' : ∀ m d, d ∣ curr' → m * d ∈ expandFacs ((p, j + 1) :: facs) m :=
            mem_expandFacs_step hfacs hp_prime
          have hcurr'_pos : 0 < curr' := Nat.mul_pos hcurr (pow_pos hp_prime.pos _)
          rw [← hcurr'_R'] at hlo hhi htau ⊢
          exact walkTree_sound ps hps_pair hps_prime' curr' (curTau * (j + 1 + 1))
            ((p, j + 1) :: facs) R' hw_step hcurr'_pos hR'_pos
            (Nat.Coprime.mul_left hcop_curr_R' hcop_pe_R')
            hlo hhi htau hcurTau' hfacs' hR'_primes

-- Small u <= 4988 divisor bound via countSqrtDivs
lemma countSqrtDivs_eq_card (u : ℕ) :
    ∀ k : ℕ, countSqrtDivs u k =
      ((Finset.Icc 1 k).filter (fun d => d * d ≤ u ∧ u % d = 0)).card
  | 0 => by simp [countSqrtDivs]
  | k + 1 => by
    simp only [countSqrtDivs]
    have hIcc : Finset.Icc 1 (k + 1) = Insert.insert (k + 1) (Finset.Icc 1 k) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : k + 1 ∉ Finset.Icc 1 k := by simp
    rw [hIcc, Finset.filter_insert, countSqrtDivs_eq_card u k]
    have hcond_iff :
        Bool.and (Nat.ble (Nat.mul (Nat.add k 1) (Nat.add k 1)) u)
          (Nat.beq (Nat.mod u (Nat.add k 1)) 0) = true ↔
        (k + 1) * (k + 1) ≤ u ∧ u % (k + 1) = 0 := by
      change Bool.and (Nat.ble ((k + 1) * (k + 1)) u) (Nat.beq (u % (k + 1)) 0) = true ↔
        (k + 1) * (k + 1) ≤ u ∧ u % (k + 1) = 0
      simp [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq]
    by_cases hc : (k + 1) * (k + 1) ≤ u ∧ u % (k + 1) = 0
    · have htrue : Bool.and (Nat.ble (Nat.mul (Nat.add k 1) (Nat.add k 1)) u)
          (Nat.beq (Nat.mod u (Nat.add k 1)) 0) = true := hcond_iff.mpr hc
      rw [if_pos hc, Finset.card_insert_of_notMem (by simp [hnot])]
      simp only [htrue, ↓reduceIte]
      change 1 + _ = _ + 1
      omega
    · have hfalse : Bool.and (Nat.ble (Nat.mul (Nat.add k 1) (Nat.add k 1)) u)
          (Nat.beq (Nat.mod u (Nat.add k 1)) 0) = false :=
        Bool.eq_false_iff.mpr (fun ht => hc (hcond_iff.mp ht))
      rw [if_neg hc]
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
      change 0 + _ = _
      omega

lemma checkSmallUInner_sound (b : ℕ) :
    ∀ k j : ℕ, j < k → checkSmallUInner b k = true →
      100 * b + (j + 1) ≤ 4988 → countSqrtDivs (100 * b + (j + 1)) 70 ≤ 24
  | 0, _, hj, _, _ => by omega
  | k + 1, j, hj, hchk, hle => by
    simp only [checkSmallUInner, Bool.and_eq_true] at hchk
    by_cases hjk : j = k
    · subst hjk
      have hble : Nat.ble (Nat.add (Nat.mul 100 b) (Nat.add j 1)) 4988 = true := by
        rw [Nat.ble_eq]
        exact hle
      have h1 := hchk.1
      simp only [hble, ↓reduceIte, Nat.ble_eq] at h1
      exact h1
    · exact checkSmallUInner_sound b k j (by omega) hchk.2 hle

lemma checkSmallUOuter_sound :
    ∀ K b : ℕ, b < K → checkSmallUOuter K = true → checkSmallUInner b 100 = true
  | 0, _, hb, _ => by omega
  | K + 1, b, hb, hchk => by
    simp only [checkSmallUOuter, Bool.and_eq_true] at hchk
    by_cases hbK : b = K
    · subst hbK; exact hchk.1
    · exact checkSmallUOuter_sound K b (by omega) hchk.2

lemma card_divisors_le_48_of_le_4988 {u : ℕ} (hu1 : 1 ≤ u) (hu2 : u ≤ 4988) :
    u.divisors.card ≤ 48 := by
  have hsplit : u.divisors.card =
      (u.divisors.filter (fun d => d * d ≤ u)).card +
        (u.divisors.filter (fun d => ¬ d * d ≤ u)).card :=
    (Finset.card_filter_add_card_filter_not (fun d => d * d ≤ u)).symm
  have hhi_le : (u.divisors.filter (fun d => ¬ d * d ≤ u)).card ≤
      (u.divisors.filter (fun d => d * d ≤ u)).card := by
    refine Finset.card_le_card_of_injOn (fun d => u / d) (fun d hd => ?_)
      (fun d₁ hd₁ d₂ hd₂ heq => ?_)
    · rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd
      dsimp only
      rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors]
      rcases hd with ⟨⟨hdvd, hu0⟩, hgt⟩
      have hd_eq : d * (u / d) = u := Nat.mul_div_cancel' hdvd
      refine ⟨⟨⟨d, by linarith [mul_comm d (u / d)]⟩, hu0⟩, ?_⟩
      have hlt : u / d < d := by nlinarith
      nlinarith
    · rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd₁ hd₂
      have h1 : u / (u / d₁) = d₁ := Nat.div_div_self hd₁.1.1 (by omega)
      have h2 : u / (u / d₂) = d₂ := Nat.div_div_self hd₂.1.1 (by omega)
      dsimp only at heq
      rw [← h1, ← h2, heq]
  have hsub70 : u.divisors.filter (fun d => d * d ≤ u) ⊆
      (Finset.Icc 1 70).filter (fun d => d * d ≤ u ∧ u % d = 0) := by
    intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc] at hd ⊢
    rcases hd with ⟨⟨hdvd, _⟩, hsq⟩
    have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hd70 : d ≤ 70 := by nlinarith
    exact ⟨⟨hd_pos, hd70⟩, hsq, Nat.mod_eq_zero_of_dvd hdvd⟩
  have hsqrt_le : (u.divisors.filter (fun d => d * d ≤ u)).card ≤ countSqrtDivs u 70 := by
    rw [countSqrtDivs_eq_card]
    exact Finset.card_le_card hsub70
  set b := (u - 1) / 100
  set j := (u - 1) % 100
  have hb50 : b < 50 := by omega
  have hj100 : j < 100 := Nat.mod_lt _ (by norm_num)
  have hu_decomp : 100 * b + (j + 1) = u := by
    have := Nat.div_add_mod (u - 1) 100
    omega
  have hinner := checkSmallUOuter_sound 50 b hb50 small_u_cert
  have h24 := checkSmallUInner_sound b 100 j hj100 hinner (by omega)
  rw [hu_decomp] at h24
  omega

lemma exists_top_multiple {M : ℕ} (h1 : 1 ≤ M) (h2 : M < 982800) :
    ∃ MStar : ℕ, M ∣ MStar ∧ 491400 ≤ MStar ∧ MStar < 982800 := by
  by_cases htop : 491400 ≤ M
  · exact ⟨M, dvd_rfl, htop, h2⟩
  · have hlt : 982800 - 2 * M < 982800 - M := by omega
    obtain ⟨MStar, hdvd, hlo, hhi⟩ := exists_top_multiple (M := 2 * M) (by omega) (by omega)
    exact ⟨MStar, dvd_trans ⟨2, by ring⟩ hdvd, hlo, hhi⟩
termination_by 982800 - M

lemma top_multiple_cand_lt_100 {MStar : ℕ} (hlo : 491400 ≤ MStar) (hhi : MStar < 982800) :
    (candFinset MStar).card < 100 := by
  have hM_pos : 0 < MStar := by omega
  by_cases htau : MStar.divisors.card < 100
  · exact lt_of_le_of_lt (Finset.card_filter_le _ _) htau
  · have htau' : 100 ≤ MStar.divisors.card := Nat.le_of_not_lt htau
    by_cases hlarge : ∃ q : ℕ, q.Prime ∧ q ∣ MStar ∧ 197 ≤ q
    · exfalso
      rcases hlarge with ⟨q, hqp, hqdvd, hq197⟩
      obtain ⟨e, u, hM_eq, hu_pos, hndvd⟩ := extract_prime_pow hM_pos hqp
      have he1 : 1 ≤ e := by
        by_contra he0
        have : e = 0 := by omega
        subst this
        simp only [pow_zero, one_mul] at hM_eq
        subst hM_eq
        exact hndvd hqdvd
      have hcop : Nat.Coprime (q ^ e) u :=
        (hqp.coprime_iff_not_dvd.mpr hndvd).pow_left e
      have hcard_eq : MStar.divisors.card = (e + 1) * u.divisors.card := by
        rw [hM_eq, hcop.card_divisors_mul, Nat.divisors_prime_pow hqp, Finset.card_map,
          Finset.card_range]
      by_cases he2 : 2 ≤ e
      · have he3 : e ≤ 3 := by
          by_contra he4
          have h4 : 4 ≤ e := by omega
          have hq4 : 197 ^ 4 ≤ q ^ e := le_trans (Nat.pow_le_pow_left hq197 4)
            (Nat.pow_le_pow_right (by omega) h4)
          have : q ^ e ≤ MStar := by
            rw [hM_eq]
            exact Nat.le_mul_of_pos_right _ hu_pos
          have : 197 ^ 4 < 982800 := lt_of_le_of_lt (le_trans hq4 this) hhi
          norm_num at this
        have hu25 : u ≤ 25 := by
          have hq2 : 197 ^ 2 ≤ q ^ e := le_trans (Nat.pow_le_pow_left hq197 2)
            (Nat.pow_le_pow_right (by omega) he2)
          have : 197 ^ 2 * u ≤ MStar := by
            rw [hM_eq]
            exact Nat.mul_le_mul_right u hq2
          omega
        have hu_tau : u.divisors.card ≤ 8 :=
          small_tau_25 u (Finset.mem_Icc.mpr ⟨hu_pos, hu25⟩)
        have : MStar.divisors.card ≤ 4 * 8 := by
          rw [hcard_eq]
          exact Nat.mul_le_mul (by omega) hu_tau
        omega
      · have he_eq1 : e = 1 := by omega
        subst he_eq1
        simp only [pow_one] at hM_eq
        have hu4988 : u ≤ 4988 := by
          have : 197 * u ≤ MStar := by
            rw [hM_eq]
            exact Nat.mul_le_mul_right u hq197
          omega
        have hu_tau : u.divisors.card ≤ 48 := card_divisors_le_48_of_le_4988 hu_pos hu4988
        omega
    · have hsmooth : ∀ q, q.Prime → q ∣ MStar → q ∈ primes193 := by
        intro q hqp hqd
        have hlt197 : q < 197 := lt_of_not_ge fun hge => hlarge ⟨q, hqp, hqd, hge⟩
        exact mem_primes193_of_le q (Finset.mem_range.mpr hlt197) hqp
      have hRes := walkTree_sound primes193 primes193_sorted primes193_prime 1 1 [] MStar
        erdos_tree_cert (by norm_num) hM_pos (Nat.coprime_one_left _)
        (by simpa using hlo) (by simpa using hhi) (by simpa using htau')
        (by simp) (fun m d hd => by
          have hd1 : d = 1 := Nat.eq_one_of_dvd_one hd
          subst hd1
          simp [expandFacs])
        hsmooth
      simpa using hRes

end LL_Erdos273Count_Work

theorem solution (L : ℕ) (hL0 : 0 < L) (hL : L < 1965600) (T : Finset ℕ)
    (hdvd : ∀ d ∈ T, d ∣ L) (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) :
    T.card < 100 := by
  open LL_Erdos273Count_Work in
  have hd_even : ∀ d ∈ T, 2 ∣ d ∧ 4 ≤ d ∧ (d + 1).Prime := by
    intro d hd
    obtain ⟨p, hp, hp5, rfl⟩ := hform d hd
    have hodd : Odd p := hp.odd_of_ne_two (by omega)
    rcases hodd with ⟨m, rfl⟩
    refine ⟨⟨m, by omega⟩, by omega, ?_⟩
    have : 2 * m + 1 - 1 + 1 = 2 * m + 1 := by omega
    rwa [this]
  by_cases hL_even : 2 ∣ L
  · rcases hL_even with ⟨M, rfl⟩
    have hM1 : 1 ≤ M := by omega
    have hM_lt : M < 982800 := by omega
    obtain ⟨MStar, hM_dvd, hMStar_lo, hMStar_hi⟩ := exists_top_multiple hM1 hM_lt
    have hcard_le : T.card ≤ (candFinset MStar).card := by
      refine Finset.card_le_card_of_injOn (fun d => d / 2) (fun d hd => ?_)
        (fun d₁ hd₁ d₂ hd₂ heq => ?_)
      · rw [Finset.mem_coe] at hd ⊢
        rcases hd_even d hd with ⟨⟨m, rfl⟩, hd4, hp⟩
        have hm_dvd_M : m ∣ M := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp (hdvd _ hd)
        have hm_dvd_MStar : m ∣ MStar := dvd_trans hm_dvd_M hM_dvd
        dsimp only
        have hdiv : 2 * m / 2 = m := by omega
        rw [hdiv]
        exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hm_dvd_MStar, by omega⟩, by omega, hp⟩
      · rw [Finset.mem_coe] at hd₁ hd₂
        rcases (hd_even d₁ hd₁).1 with ⟨m₁, rfl⟩
        rcases (hd_even d₂ hd₂).1 with ⟨m₂, rfl⟩
        dsimp only at heq
        omega
    exact lt_of_le_of_lt hcard_le (top_multiple_cand_lt_100 hMStar_lo hMStar_hi)
  · have hTe : T = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun d hd => ?_
      exact hL_even (dvd_trans (hd_even d hd).1 (hdvd d hd))
    simp [hTe]
