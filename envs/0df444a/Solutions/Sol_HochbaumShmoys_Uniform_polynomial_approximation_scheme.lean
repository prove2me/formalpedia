-- Prove2me | solution 1 for HochbaumShmoys.Uniform.polynomial_approximation_scheme
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T10:45:15.49427+00:00
-- url     : https://prove2.me/submissions/5bf77cb5-8df8-428c-a4c8-ef031854e8fc

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_Packing
import Definitions.Def_HochbaumShmoys_Uniform_BinarySearch
import Definitions.Def_HochbaumShmoys_Uniform_AllPack
import Theorems.Thm_HochbaumShmoys_Uniform_all_pack_relaxed_decision
import Theorems.Thm_HochbaumShmoys_Uniform_corollary_2

namespace X4HSG

open HochbaumShmoys.Uniform Finset

variable {m n : ℕ}

lemma mt_eq (p : Fin n → ℝ) (s : Fin m → ℝ) (σ : Fin n → Fin m) (i : Fin m) :
    machineTime p s σ i = binLoad p σ i / s i := by
  unfold machineTime binLoad; rw [Finset.sum_div]

lemma bdd (p : Fin n → ℝ) (s : Fin m → ℝ) (σ : Fin n → Fin m) :
    BddAbove (Set.range (machineTime p s σ)) := (Set.finite_range _).bddAbove

lemma mk_le (hm : 0 < m) (p : Fin n → ℝ) (s : Fin m → ℝ) (σ : Fin n → Fin m) (T : ℝ)
    (h : ∀ i, machineTime p s σ i ≤ T) : makespan p s σ ≤ T := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact ciSup_le h

lemma le_mk (p : Fin n → ℝ) (s : Fin m → ℝ) (σ : Fin n → Fin m) (i : Fin m) :
    machineTime p s σ i ≤ makespan p s σ := le_ciSup (bdd p s σ) i

lemma smax_ge (s : Fin m → ℝ) (i : Fin m) : s i ≤ ⨆ i, s i :=
  le_ciSup (Set.finite_range _).bddAbove i

lemma total (p : Fin n → ℝ) (σ : Fin n → Fin m) : ∑ j, p j = ∑ i, binLoad p σ i := by
  unfold binLoad
  rw [← Finset.sum_fiberwise_of_maps_to (g := σ) (t := univ) (fun _ _ => mem_univ _)]

/-- lower bound: L0 ≤ makespan of every schedule -/
lemma L0_le (hm : 0 < m) (p : Fin n → ℝ) (s : Fin m → ℝ) (hs : ∀ i, 0 < s i)
    (hp : ∀ j, 0 < p j) (τ : Fin n → Fin m) : initialLower p s ≤ makespan p s τ := by
  have hS : 0 < ⨆ i, s i := lt_of_lt_of_le (hs ⟨0, hm⟩) (smax_ge s _)
  set M := makespan p s τ
  have hb : ∀ i, binLoad p τ i ≤ M * (⨆ i, s i) := by
    intro i
    have h1 := le_mk p s τ i
    have h0 : 0 ≤ M := le_trans (by rw [mt_eq]; exact div_nonneg (sum_nonneg fun j _ => (hp j).le) (hs i).le) h1
    rw [mt_eq, div_le_iff₀ (hs i)] at h1
    calc binLoad p τ i ≤ M * s i := h1
      _ ≤ M * (⨆ i, s i) := mul_le_mul_of_nonneg_left (smax_ge s i) h0
  unfold initialLower
  rw [div_le_iff₀ (mul_pos (by exact_mod_cast hm) hS), total p τ]
  calc ∑ i, binLoad p τ i ≤ ∑ _i : Fin m, M * (⨆ i, s i) := sum_le_sum fun i _ => hb i
    _ = M * ((m : ℝ) * ⨆ i, s i) := by simp; ring

lemma fastest_mk (hm : 0 < m) (p : Fin n → ℝ) (s : Fin m → ℝ) (hs : ∀ i, 0 < s i)
    (hp : ∀ j, 0 < p j) :
    makespan p s (fun _ => fastestMachine s hm) ≤ initialUpper p s := by
  have hf := Classical.choose_spec
    (Finset.exists_max_image Finset.univ s ⟨⟨0, hm⟩, Finset.mem_univ _⟩)
  have heq : s (fastestMachine s hm) = ⨆ i, s i :=
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    le_antisymm (smax_ge s _) (ciSup_le fun i => hf.2 i (mem_univ _))
  apply mk_le hm; intro i
  rw [mt_eq]; unfold binLoad initialUpper
  by_cases hi : fastestMachine s hm = i
  · subst hi; simp [heq]
  · have : univ.filter (fun _ : Fin n => fastestMachine s hm = i) = ∅ := by simp [hi]
    rw [this, sum_empty, zero_div]
    exact div_nonneg (sum_nonneg fun j _ => (hp j).le) ((hs ⟨0, hm⟩).le.trans (smax_ge s _))

structure Inv (p : Fin n → ℝ) (s : Fin m → ℝ) (η : ℝ) (k : ℕ) (st : SearchState m n) : Prop where
  low : initialLower p s ≤ st.lower
  opt : ∀ τ, st.lower ≤ makespan p s τ
  gap : st.upper - st.lower = (initialUpper p s - initialLower p s) / 2 ^ k
  sch : makespan p s st.schedule ≤ (1 + η) * st.upper

lemma U0_ge (p : Fin n → ℝ) (s : Fin m → ℝ) (hp : ∀ j, 0 < p j) (hm : 0 < m)
    (hs : ∀ i, 0 < s i) : initialLower p s ≤ initialUpper p s := by
  have hS : 0 < ⨆ i, s i := lt_of_lt_of_le (hs ⟨0, hm⟩) (smax_ge s _)
  unfold initialLower initialUpper
  apply div_le_div_of_nonneg_left (sum_nonneg fun j _ => (hp j).le) hS
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

lemma inv_step (hm : 0 < m) (p : Fin n → ℝ) (s : Fin m → ℝ) (hs : ∀ i, 0 < s i)
    (hp : ∀ j, 0 < p j) (hn : 0 < n) (η : ℝ)
    (D : (Fin n → ℝ) → (Fin m → ℝ) → Option (Fin n → Fin m))
    (hD : IsRelaxedDecisionProcedure η D) (k : ℕ) (st : SearchState m n)
    (h : Inv p s η k st) : Inv p s η (k + 1) (searchStep D p s st) := by
  have hS : 0 < ⨆ i, s i := lt_of_lt_of_le (hs ⟨0, hm⟩) (smax_ge s _)
  have hL0 : 0 < initialLower p s := by
    unfold initialLower
    exact div_pos (sum_pos (fun j _ => hp j) ⟨⟨0, hn⟩, mem_univ _⟩)
      (mul_pos (by exact_mod_cast hm) hS)
  have hgap0 : 0 ≤ st.upper - st.lower := by
    rw [h.gap]; exact div_nonneg (by linarith [U0_ge p s hp hm hs]) (by positivity)
  set T := (st.lower + st.upper) / 2 with hT
  have hTpos : 0 < T := by linarith [h.low]
  have hb : ∀ i, 0 < T * s i := fun i => mul_pos hTpos (hs i)
  have hDD := hD p (fun i => T * s i) hp hb
  unfold searchStep
  rcases hσ : D p (fun i => T * s i) with _ | σ
  · simp only
    refine ⟨by simp; linarith [h.low], ?_, ?_, by simpa using h.sch⟩
    · intro τ
      have hnf := hDD.2 hσ τ
      unfold IsTrulyFeasible at hnf; push Not at hnf
      obtain ⟨i, hi⟩ := hnf
      show T ≤ _
      have h2 : T < binLoad p τ i / s i := by rw [lt_div_iff₀ (hs i)]; exact hi
      linarith [le_mk p s τ i, mt_eq p s τ i]
    · simp only; rw [pow_succ, ← div_div, ← h.gap]; ring
  · simp only
    refine ⟨h.low, h.opt, ?_, ?_⟩
    · simp only; rw [pow_succ, ← div_div, ← h.gap]; ring
    · apply mk_le hm; intro i
      have := hDD.1 σ hσ i
      rw [mt_eq, div_le_iff₀ (hs i)]
      calc binLoad p σ i ≤ (1 + η) * (T * s i) := this
        _ = (1 + η) * T * s i := by ring

lemma pow_ge (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) :
    3 * m / ε ≤ (2 : ℝ) ^ iterationCount m ε := by
  have hx : Real.logb 2 m + Real.logb 2 (3 / ε) = Real.logb 2 (3 * m / ε) := by
    rw [← Real.logb_mul (by positivity) (by positivity)]; congr 1; ring
  have hk := Nat.le_ceil (Real.logb 2 m + Real.logb 2 (3 / ε))
  unfold iterationCount
  rw [hx] at hk ⊢
  calc 3 * m / ε = (2 : ℝ) ^ Real.logb 2 (3 * m / ε) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
    _ ≤ (2 : ℝ) ^ ((⌈Real.logb 2 (3 * m / ε)⌉₊ : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hk
    _ = _ := Real.rpow_natCast _ _

theorem bs (η ε : ℝ) (hη : 0 ≤ η) (hε : 0 < ε) (hηε : (1 + η) * (1 + ε / 3) ≤ 1 + ε)
    (hm : 0 < m) (s : Fin m → ℝ) (p : Fin n → ℝ) (hs : ∀ i, 0 < s i) (hp : ∀ j, 0 < p j)
    (D : (Fin n → ℝ) → (Fin m → ℝ) → Option (Fin n → Fin m))
    (hD : IsRelaxedDecisionProcedure η D) (τ : Fin n → Fin m) :
    makespan p s (binarySearch D p s hm (iterationCount m ε)) ≤ (1 + ε) * makespan p s τ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : ∀ σ : Fin 0 → Fin m, makespan p s σ = 0 := by
      intro σ; unfold makespan machineTime; simp
    rw [h0, h0]; simp
  set K := iterationCount m ε
  have hinv : ∀ k, Inv p s η k ((searchStep D p s)^[k]
      ⟨initialLower p s, initialUpper p s, fun _ => fastestMachine s hm⟩) := by
    intro k; induction k with
    | zero =>
      refine ⟨le_rfl, fun τ => L0_le hm p s hs hp τ, by simp, ?_⟩
      show makespan p s (fun _ => fastestMachine s hm) ≤ (1 + η) * initialUpper p s
      have := fastest_mk hm p s hs hp
      have h0 : 0 ≤ initialUpper p s := by
        unfold initialUpper
        exact div_nonneg (sum_nonneg fun j _ => (hp j).le)
          ((hs ⟨0, hm⟩).le.trans (smax_ge s _))
      nlinarith
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact inv_step hm p s hs hp hn η D hD k _ ih
  have I := hinv K
  set st := (searchStep D p s)^[K]
      ⟨initialLower p s, initialUpper p s, fun _ => fastestMachine s hm⟩
  have hbs : binarySearch D p s hm K = st.schedule := rfl
  rw [hbs]
  set M := makespan p s τ
  have hLM := I.opt τ
  have hL0M := L0_le hm p s hs hp τ
  have hL0 : 0 ≤ initialLower p s := by
    unfold initialLower
    exact div_nonneg (sum_nonneg fun j _ => (hp j).le)
      (mul_nonneg (by positivity) ((hs ⟨0, hm⟩).le.trans (smax_ge s _)))
  have hU : initialUpper p s = m * initialLower p s := by
    unfold initialUpper initialLower
    have hS : 0 < ⨆ i, s i := lt_of_lt_of_le (hs ⟨0, hm⟩) (smax_ge s _)
    have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  have hpow := pow_ge m hm ε hε
  have h2 : (0 : ℝ) < 2 ^ K := by positivity
  have hgap : st.upper - st.lower ≤ ε / 3 * M := by
    rw [I.gap, hU, div_le_iff₀ h2]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : 3 * m ≤ 2 ^ K * ε := (div_le_iff₀ hε).1 hpow
    have hM0 : 0 ≤ M := hL0.trans hL0M
    nlinarith [mul_le_mul_of_nonneg_left this hL0, mul_le_mul_of_nonneg_left hL0M h2.le]
  have hM0 : 0 ≤ M := hL0.trans hL0M
  calc makespan p s st.schedule ≤ (1 + η) * st.upper := I.sch
    _ ≤ (1 + η) * ((1 + ε / 3) * M) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    _ = ((1 + η) * (1 + ε / 3)) * M := by ring
    _ ≤ (1 + ε) * M := mul_le_mul_of_nonneg_right hηε hM0

end X4HSG

open HochbaumShmoys.Uniform in
theorem solution :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 2 ≤ N ∧ ∃ C d : ℕ,
      ∀ (m n : ℕ) (hm : 0 < m) (s : Fin m → ℝ) (p : Fin n → ℝ),
        (∀ i, 0 < s i) → (∀ j, 0 < p j) →
        (∀ D : (Fin n → ℝ) → (Fin m → ℝ) → Option (Fin n → Fin m),
          IsAllPackResolution N D → ∀ τ : Fin n → Fin m,
            makespan p s (binarySearch D p s hm (iterationCount m ε)) ≤
              (1 + ε) * makespan p s τ) ∧
        (∀ T : ℝ, 0 < T → ∀ ord : Fin m ≃ Fin m, Antitone (fun t => T * s (ord t)) →
          arcCount N (normalizedBins (fun i => T * s i) ord)
              (normalizedPieces p (fun i => T * s i)) ≤ C * m * (n + 1) ^ d) := by
  intro ε hε
  obtain ⟨C0, hC0⟩ := corollary_2
  set N := ⌈(9 + 3 * ε) / (2 * ε)⌉₊ + 2 with hNdef
  have hN : 2 ≤ N := by omega
  have hNr : (9 + 3 * ε) / (2 * ε) + 2 ≤ (N : ℝ) := by
    rw [hNdef]; push_cast; linarith [Nat.le_ceil ((9 + 3 * ε) / (2 * ε))]
  have hNpos : (0 : ℝ) < N := by linarith [div_pos (by linarith : (0:ℝ) < 9 + 3 * ε) (by linarith : (0:ℝ) < 2 * ε)]
  refine ⟨N, hN, C0 * 2 * N ^ (2 * (2 * N ^ 2 + 3)), 2 * N ^ 2 + 3, ?_⟩
  intro m n hm s p hs hp
  constructor
  · intro D hD τ
    have hR := all_pack_relaxed_decision N hN m n D hD
    have hη0 : 0 ≤ 2 * (N : ℝ)⁻¹ + ((N : ℝ)⁻¹) ^ 2 := by positivity
    apply X4HSG.bs _ ε hη0 hε _ hm s p hs hp D hR τ
    -- (1+η)(1+ε/3) ≤ 1+ε
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hinv : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
    have hη : 2 * (N : ℝ)⁻¹ + ((N : ℝ)⁻¹) ^ 2 ≤ 3 * (N : ℝ)⁻¹ := by
      have := (N : ℝ)⁻¹; nlinarith [inv_nonneg.2 hNpos.le]
    have key : (3 + ε) * (N : ℝ)⁻¹ ≤ 2 * ε / 3 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hNpos]
      have h1 : (9 + 3 * ε) / (2 * ε) * (2 * ε) = 9 + 3 * ε := by field_simp
      nlinarith
    nlinarith
  · intro T hT ord hanti
    set b : Fin m → ℝ := fun i => T * s i
    have hbpos : ∀ i, 0 < b i := fun i => mul_pos hT (hs i)
    have hmax : ∀ i, b i ≤ b (ord ⟨0, hm⟩) := by
      intro i
      have := hanti (show (⟨0, hm⟩ : Fin m) ≤ ord.symm i from Fin.le_def.2 (Nat.zero_le _))
      simpa [b] using this
    have hL : largestBin b = b (ord ⟨0, hm⟩) := by
      unfold largestBin
      haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      exact le_antisymm (ciSup_le hmax) (le_ciSup (Set.finite_range _).bddAbove _)
    have hLpos : 0 < largestBin b := hL ▸ hbpos _
    have h := hC0 N hN m n hm (normalizedBins b ord) (normalizedPieces p b)
      (by
        intro x y hxy
        unfold normalizedBins
        exact div_le_div_of_nonneg_right (hanti hxy) hLpos.le)
      (by unfold normalizedBins; rw [hL]; exact div_self (hbpos _).ne')
      (fun t => div_pos (hbpos _) hLpos)
    refine h.trans (le_of_eq ?_)
    rw [mul_pow, ← pow_mul]; ring
