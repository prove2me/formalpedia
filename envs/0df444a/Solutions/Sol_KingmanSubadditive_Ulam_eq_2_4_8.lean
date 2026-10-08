-- Prove2me | solution 1 for KingmanSubadditive.Ulam.eq_2_4_8
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:28:12.199996+00:00
-- url     : https://prove2.me/submissions/8b031d68-01aa-4e8e-8e65-7acc3cdeb88c

import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations

open Filter Topology
open scoped BigOperators

namespace KingmanSubadditive.Ulam

lemma isAscendingOn_subset {n : ℕ} (σ : Equiv.Perm (Fin n)) {s t : Finset (Fin n)}
    (h : IsAscendingOn σ s) (hts : t ⊆ s) : IsAscendingOn σ t :=
  fun i hi j hj hij => h i (hts hi) j (hts hj) hij

lemma exists_ascending_card_eq_lis {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∃ s : Finset (Fin n), IsAscendingOn σ s ∧ s.card = lis σ := by
  classical
  have hne : ((Finset.univ : Finset (Finset (Fin n))).filter (fun s => IsAscendingOn σ s)).Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i hi => absurd hi (Finset.notMem_empty _)⟩⟩
  obtain ⟨s, hs, hcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  refine ⟨s, (Finset.mem_filter.1 hs).2, ?_⟩
  unfold lis; exact hcard.symm

theorem num_ascending_ge_choose_core {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) (_hk : k ≤ lis σ) :
    (lis σ).choose k ≤ numAscending k σ := by
  classical
  obtain ⟨s, hs, hcard⟩ := exists_ascending_card_eq_lis σ
  unfold numAscending
  rw [← hcard, ← Finset.card_powersetCard]
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_powersetCard] at ht
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  exact ⟨⟨Finset.subset_univ _, ht.2⟩, isAscendingOn_subset σ hs ht.1⟩


open Finset Classical

variable {n : ℕ}

/-- permutations fixing the complement of `s` pointwise -/
def fixSet (s : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter (fun ρ => ∀ a, a ∉ s → ρ a = a)

/-- permutations ascending on `s` -/
def ascSet (s : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter (fun σ => IsAscendingOn σ s)

lemma card_fixSet (s : Finset (Fin n)) : (fixSet s).card = (s.card).factorial := by
  classical
  have h1 : (fixSet s).card = Fintype.card {f : Equiv.Perm (Fin n) // ∀ a, ¬ a ∈ s → f a = a} := by
    rw [Fintype.card_subtype]
    unfold fixSet
    congr 1
  rw [h1, ← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ∈ s)),
    Fintype.card_perm, Fintype.card_coe]

/-- a permutation fixing `sᶜ` maps `s` into `s` -/
lemma fix_maps (s : Finset (Fin n)) (g : Equiv.Perm (Fin n)) (hg : ∀ a, a ∉ s → g a = a)
    {a : Fin n} (ha : a ∈ s) : g a ∈ s := by
  by_contra h
  have := hg _ h
  have h2 : g (g a) = g a := this
  have := g.injective h2
  rw [this] at h
  exact h ha

/-- a permutation fixing `sᶜ` and increasing on `s` is the identity -/
lemma fix_of_mono (s : Finset (Fin n)) (g : Equiv.Perm (Fin n)) (hg : ∀ a, a ∉ s → g a = a)
    (hmono : ∀ i ∈ s, ∀ j ∈ s, i < j → g i < g j) : g = 1 := by
  have hc : s.card = s.card := rfl
  have hu := Finset.orderEmbOfFin_unique hc (f := fun x => g (s.orderEmbOfFin hc x))
    (fun x => fix_maps s g hg (Finset.orderEmbOfFin_mem s hc x))
    (fun x y hxy => hmono _ (Finset.orderEmbOfFin_mem s hc x) _ (Finset.orderEmbOfFin_mem s hc y)
      ((s.orderEmbOfFin hc).strictMono hxy))
  refine Equiv.ext fun a => ?_
  simp only [Equiv.Perm.coe_one, id_eq]
  by_cases ha : a ∈ s
  · have : a ∈ Set.range (s.orderEmbOfFin hc) := by rw [Finset.range_orderEmbOfFin]; exact ha
    obtain ⟨x, rfl⟩ := this
    exact congrFun hu x
  · exact hg a ha

lemma asc_iff (s : Finset (Fin n)) (τ : Equiv.Perm (Fin n)) (hτ : IsAscendingOn τ s)
    {i j : Fin n} (hi : i ∈ s) (hj : j ∈ s) (h : τ i < τ j) : i < j := by
  rcases lt_trichotomy i j with h1 | h1 | h1
  · exact h1
  · subst h1; exact absurd h (lt_irrefl _)
  · exact absurd (hτ j hj i hi h1) (not_lt.2 h.le)

lemma card_ascSet_mul (s : Finset (Fin n)) :
    (ascSet s).card * (s.card).factorial = n.factorial := by
  classical
  have hn : n.factorial = (univ : Finset (Equiv.Perm (Fin n))).card := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← card_fixSet, ← Finset.card_product, hn]
  refine Finset.card_bij (fun p _ => p.1 * p.2) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · rintro ⟨τ, ρ⟩ hp ⟨τ', ρ'⟩ hp' heq
    simp only [Finset.mem_product, ascSet, fixSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp hp'
    simp only at heq
    -- g = τ'⁻¹ * τ = ρ' * ρ⁻¹
    have hg1 : τ'⁻¹ * τ = ρ' * ρ⁻¹ := by
      calc τ'⁻¹ * τ = τ'⁻¹ * (τ * ρ) * ρ⁻¹ := by group
        _ = τ'⁻¹ * (τ' * ρ') * ρ⁻¹ := by rw [heq]
        _ = ρ' * ρ⁻¹ := by group
    have hfix : ∀ a, a ∉ s → (τ'⁻¹ * τ) a = a := by
      intro a ha
      rw [hg1, Equiv.Perm.mul_apply]
      have h1 : ρ⁻¹ a = a := by
        have := hp.2 a ha
        exact (Equiv.Perm.inv_eq_iff_eq.2 this.symm)
      rw [h1]; exact hp'.2 a ha
    have hmono : ∀ i ∈ s, ∀ j ∈ s, i < j → (τ'⁻¹ * τ) i < (τ'⁻¹ * τ) j := by
      intro i hi j hj hij
      have h1 := hp.1 i hi j hj hij
      apply asc_iff s τ' hp'.1 (fix_maps s _ hfix hi) (fix_maps s _ hfix hj)
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
      exact h1
    have hid := fix_of_mono s _ hfix hmono
    have hττ : τ = τ' := by
      have := congrArg (fun g => τ' * g) hid
      simpa using this
    subst hττ
    have hρ : ρ = ρ' := by
      have := congrArg (fun g => τ⁻¹ * g) heq
      simpa using this
    subst hρ; rfl
  · intro σ _
    -- sorting: build τ
    set V := s.image σ with hV
    have hVc : V.card = s.card := Finset.card_image_of_injective _ σ.injective
    have hsc : s.card = s.card := rfl
    let e := s.orderIsoOfFin hsc
    let f := V.orderEmbOfFin hVc
    let τf : Fin n → Fin n := fun i => if hi : i ∈ s then f (e.symm ⟨i, hi⟩) else σ i
    have hτf_mem : ∀ i (hi : i ∈ s), τf i ∈ V := by
      intro i hi; simp only [τf, dif_pos hi]; exact Finset.orderEmbOfFin_mem _ _ _
    have hτf_not : ∀ i, i ∉ s → τf i ∉ V := by
      intro i hi hmem
      simp only [τf, dif_neg hi] at hmem
      rw [hV, Finset.mem_image] at hmem
      obtain ⟨a, ha, hai⟩ := hmem
      have := σ.injective hai
      rw [this] at ha; exact hi ha
    have hinj : Function.Injective τf := by
      intro i j hij
      by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
      · simp only [τf, dif_pos hi, dif_pos hj] at hij
        have := e.symm.injective (f.injective hij)
        exact congrArg Subtype.val this
      · exact absurd (hij ▸ hτf_mem i hi) (hτf_not j hj)
      · exact absurd (hij ▸ hτf_mem j hj) (hτf_not i hi)
      · simp only [τf, dif_neg hi, dif_neg hj] at hij
        exact σ.injective hij
    let τ : Equiv.Perm (Fin n) := Equiv.ofBijective τf (Finite.injective_iff_bijective.1 hinj)
    have hτ : ∀ i, τ i = τf i := fun i => rfl
    refine ⟨⟨τ, τ⁻¹ * σ⟩, ?_, ?_⟩
    · simp only [Finset.mem_product, ascSet, fixSet, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor
      · intro i hi j hj hij
        rw [hτ, hτ]
        simp only [τf, dif_pos hi, dif_pos hj]
        apply f.strictMono
        apply e.symm.strictMono
        exact hij
      · intro a ha
        rw [Equiv.Perm.mul_apply]
        apply Equiv.Perm.inv_eq_iff_eq.2
        rw [hτ]; simp only [τf, dif_neg ha]
    · simp only; group

lemma card_ascSet_real (s : Finset (Fin n)) :
    ((ascSet s).card : ℝ) = (n.factorial : ℝ) / ((s.card).factorial : ℝ) := by
  rw [eq_div_iff (by positivity)]
  exact_mod_cast card_ascSet_mul s

theorem expected_num_ascending_core (n k : ℕ) (_hk : 0 < k) :
    (∑ σ : Equiv.Perm (Fin n), (numAscending k σ : ℝ)) / (Nat.factorial n : ℝ) =
      (n.choose k : ℝ) / (Nat.factorial k : ℝ) := by
  classical
  have h1 : ∀ σ : Equiv.Perm (Fin n), (numAscending k σ : ℝ) =
      ∑ s ∈ (univ : Finset (Fin n)).powersetCard k, (if IsAscendingOn σ s then (1 : ℝ) else 0) := by
    intro σ
    unfold numAscending
    rw [Finset.card_filter]; push_cast; rfl
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ s ∈ (univ : Finset (Fin n)).powersetCard k,
      (∑ σ : Equiv.Perm (Fin n), (if IsAscendingOn σ s then (1 : ℝ) else 0)) =
        (n.factorial : ℝ) / (k.factorial : ℝ) := by
    intro s hs
    rw [Finset.mem_powersetCard] at hs
    rw [← hs.2, ← card_ascSet_real]
    unfold ascSet
    rw [Finset.card_filter]; push_cast; rfl
  rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp


theorem eq_2_4_7_core (n k r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r) :
    unifProb n (fun σ => r ≤ lis σ) ≤
      (n.choose k : ℝ) / ((Nat.factorial k : ℝ) * (r.choose k : ℝ)) := by
  have hE := expected_num_ascending_core n k hk
  have hrk : (0 : ℝ) < r.choose k := by exact_mod_cast Nat.choose_pos hkr
  have hn : (0 : ℝ) < n.factorial := by positivity
  have hkf : (0 : ℝ) < k.factorial := by positivity
  have hsum : ∑ σ : Equiv.Perm (Fin n), (numAscending k σ : ℝ) =
      (n.factorial : ℝ) * ((n.choose k : ℝ) / (k.factorial : ℝ)) := by
    rw [← hE]; field_simp
  have hgoal : ∀ F : Finset (Equiv.Perm (Fin n)), (∀ σ ∈ F, r ≤ lis σ) →
      (F.card : ℝ) / (n.factorial : ℝ) ≤
        (n.choose k : ℝ) / ((Nat.factorial k : ℝ) * (r.choose k : ℝ)) := by
    intro F hF
    have hkey : (r.choose k : ℝ) * (F.card : ℝ) ≤
        ∑ σ : Equiv.Perm (Fin n), (numAscending k σ : ℝ) := by
      calc (r.choose k : ℝ) * (F.card : ℝ) = ∑ σ ∈ F, (r.choose k : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ σ ∈ F, (numAscending k σ : ℝ) := by
            apply Finset.sum_le_sum
            intro σ hσ
            have hσ' := hF σ hσ
            have h1 : r.choose k ≤ (lis σ).choose k := Nat.choose_le_choose k hσ'
            have h2 := num_ascending_ge_choose_core σ k (le_trans hkr hσ')
            exact_mod_cast le_trans h1 h2
        _ ≤ ∑ σ : Equiv.Perm (Fin n), (numAscending k σ : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            intro i _ _; positivity
    rw [hsum] at hkey
    rw [div_le_div_iff₀ hn (by positivity)]
    have : (F.card : ℝ) * (k.factorial * r.choose k) = k.factorial * (r.choose k * F.card) := by
      ring
    rw [this]
    calc (k.factorial : ℝ) * (r.choose k * F.card)
        ≤ k.factorial * ((n.factorial : ℝ) * ((n.choose k : ℝ) / (k.factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left hkey hkf.le
      _ = (n.choose k : ℝ) * n.factorial := by field_simp
  unfold unifProb
  apply hgoal
  intro σ hσ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  exact hσ


open Real

/-- Stirling upper bound: `log m! ≤ 1 + log m / 2 + m log m - m` for `m ≥ 1`. -/
lemma log_factorial_upper {m : ℕ} (hm : 1 ≤ m) :
    Real.log (m.factorial : ℝ) ≤ 1 + Real.log m / 2 + m * Real.log m - m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hanti := Stirling.stirlingSeq'_antitone (Nat.zero_le (m - 1))
  simp only [Function.comp, Nat.succ_eq_add_one, zero_add, Nat.sub_add_cancel hm,
    Stirling.stirlingSeq_one] at hanti
  have hpos : 0 < Stirling.stirlingSeq m := by
    have := Stirling.stirlingSeq'_pos (m - 1)
    rwa [Nat.sub_add_cancel hm] at this
  have hlog := Real.log_le_log hpos hanti
  rw [Stirling.log_stirlingSeq_formula, Real.log_div (Real.exp_pos _).ne' (by positivity),
    Real.log_exp, Real.log_sqrt zero_le_two, Real.log_mul two_ne_zero hm'.ne',
    Real.log_div hm'.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  linarith

/-- lower bound `m log m - m ≤ log m!` -/
lemma log_factorial_lower (m : ℕ) :
    m * Real.log m - m ≤ Real.log (m.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (x := (m : ℝ)) (Nat.cast_nonneg m) m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hf : (0 : ℝ) < m.factorial := by positivity
  have := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div (by positivity) hf.ne', Real.log_pow] at this
  linarith

/-- the bound `C(n,k) / (k! C(r,k)) ≤ n^k (r-k)! / (k! r!)` -/
lemma bound_step1 (n k r : ℕ) (hkr : k ≤ r) :
    (n.choose k : ℝ) / ((k.factorial : ℝ) * (r.choose k : ℝ)) ≤
      (n : ℝ) ^ k * ((r - k).factorial : ℝ) / ((k.factorial : ℝ) * (r.factorial : ℝ)) := by
  have hC : (r.choose k : ℝ) * k.factorial * (r - k).factorial = r.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkr
  have hk : (0 : ℝ) < k.factorial := by positivity
  have hr : (0 : ℝ) < r.factorial := by positivity
  have hrk : (0 : ℝ) < (r - k).factorial := by positivity
  have hCpos : (0 : ℝ) < r.choose k := by exact_mod_cast Nat.choose_pos hkr
  have h1 : (n.choose k : ℝ) ≤ (n : ℝ) ^ k / k.factorial := by
    have := Nat.choose_le_pow_div (α := ℝ) k n
    exact_mod_cast this
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc (n.choose k : ℝ) * (k.factorial * r.factorial)
      ≤ (n : ℝ) ^ k / k.factorial * (k.factorial * r.factorial) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (n : ℝ) ^ k * r.factorial := by field_simp
    _ = (n : ℝ) ^ k * ((r.choose k : ℝ) * k.factorial * (r - k).factorial) := by rw [hC]
    _ = (n : ℝ) ^ k * (r - k).factorial * (k.factorial * r.choose k) := by ring

/-- the key real inequality: `log` of the bound in terms of the exponent -/
lemma log_bound (n k r : ℕ) (s : ℝ) (hs : 0 < s) (hn : (n : ℝ) = s ^ 2)
    (hk : 1 ≤ k) (hkr : k < r) (hkn : k ≤ n) :
    Real.log ((n.choose k : ℝ) / ((k.factorial : ℝ) * (r.choose k : ℝ))) ≤
      s * stirlingExponent ((k : ℝ) / s) ((r : ℝ) / s) + 1 + Real.log ((r : ℝ) - k) / 2 := by
  have hK : (0 : ℝ) < k := by exact_mod_cast hk
  have hR : (0 : ℝ) < r := by
    have : 0 < r := by omega
    exact_mod_cast this
  have hM : (0 : ℝ) < (r : ℝ) - k := by
    have : (k : ℝ) < r := by exact_mod_cast hkr
    linarith
  have hMnat : ((r - k : ℕ) : ℝ) = (r : ℝ) - k := by
    rw [Nat.cast_sub hkr.le]
  have hm1 : 1 ≤ r - k := by omega
  have hCpos : (0 : ℝ) < r.choose k := by exact_mod_cast Nat.choose_pos hkr.le
  have hnpos : (0 : ℝ) < n := by rw [hn]; positivity
  have hkf : (0 : ℝ) < k.factorial := by positivity
  have hrf : (0 : ℝ) < r.factorial := by positivity
  have hmf : (0 : ℝ) < (r - k).factorial := by positivity
  have hB : (0 : ℝ) < (n.choose k : ℝ) / ((k.factorial : ℝ) * (r.choose k : ℝ)) := by
    have : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
    positivity
  have h1 := Real.log_le_log hB (bound_step1 n k r hkr.le)
  have hD : Real.log ((n : ℝ) ^ k * ((r - k).factorial : ℝ) / ((k.factorial : ℝ) * (r.factorial : ℝ)))
      = k * Real.log n + Real.log ((r - k).factorial : ℝ) - Real.log (k.factorial : ℝ)
        - Real.log (r.factorial : ℝ) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hmf.ne',
      Real.log_mul hkf.ne' hrf.ne', Real.log_pow]
    ring
  rw [hD] at h1
  have hF1 := log_factorial_upper hm1
  rw [hMnat] at hF1
  have hF2 := log_factorial_lower k
  have hF3 := log_factorial_lower r
  have hlogn : Real.log (n : ℝ) = 2 * Real.log s := by
    rw [hn, Real.log_pow]; push_cast; ring
  have hG : s * stirlingExponent ((k : ℝ) / s) ((r : ℝ) / s) =
      2 * k + ((r : ℝ) - k) * Real.log ((r : ℝ) - k) - k * Real.log k - r * Real.log r +
        2 * k * Real.log s := by
    simp only [stirlingExponent]
    rw [show (r : ℝ) / s - k / s = ((r : ℝ) - k) / s by ring, Real.log_div hM.ne' hs.ne',
      Real.log_div hK.ne' hs.ne', Real.log_div hR.ne' hs.ne']
    field_simp
    ring
  rw [hG]
  rw [hlogn] at h1
  linarith


lemma unifProb_nonneg (n : ℕ) (A : Equiv.Perm (Fin n) → Prop) : 0 ≤ unifProb n A := by
  unfold unifProb; positivity

lemma unifProb_mono (n : ℕ) (A B : Equiv.Perm (Fin n) → Prop) (h : ∀ σ, A σ → B σ) :
    unifProb n A ≤ unifProb n B := by
  unfold unifProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (Finset.monotone_filter_right _ (fun σ _ => h σ))

lemma continuous_stirlingExponent : Continuous (fun p : ℝ × ℝ => stirlingExponent p.1 p.2) := by
  simp only [stirlingExponent]
  have h1 : Continuous (fun p : ℝ × ℝ => (p.2 - p.1) * Real.log (p.2 - p.1)) :=
    Real.continuous_mul_log.comp (continuous_snd.sub continuous_fst)
  have h2 : Continuous (fun p : ℝ × ℝ => p.1 * Real.log p.1) :=
    Real.continuous_mul_log.comp continuous_fst
  have h3 : Continuous (fun p : ℝ × ℝ => p.2 * Real.log p.2) :=
    Real.continuous_mul_log.comp continuous_snd
  exact (((continuous_const.mul continuous_fst).add h1).sub h2).sub h3

lemma tendsto_sqrt_nat : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_floor_div (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ => (⌊c * Real.sqrt n⌋₊ : ℝ) / Real.sqrt n) atTop (𝓝 c) := by
  have hs := tendsto_sqrt_nat
  have hlow : Tendsto (fun n : ℕ => c - (Real.sqrt n)⁻¹) atTop (𝓝 c) := by
    have := tendsto_const_nhds (x := c) |>.sub (tendsto_inv_atTop_zero.comp hs)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hs.eventually_gt_atTop 0] with n hn
    have h1 := Nat.lt_floor_add_one (c * Real.sqrt n)
    rw [le_div_iff₀ hn]
    have : (c - (Real.sqrt n)⁻¹) * Real.sqrt n = c * Real.sqrt n - 1 := by field_simp
    rw [this]; linarith
  · filter_upwards [hs.eventually_gt_atTop 0] with n hn
    rw [div_le_iff₀ hn]
    exact Nat.floor_le (by positivity)

lemma tendsto_dom (b E : ℝ) (hE : E < 0) :
    Tendsto (fun n : ℕ => Real.exp (Real.sqrt n * (E / 2 +
      Real.log (Real.sqrt n) / (2 * Real.sqrt n)) + (1 + Real.log b / 2))) atTop (𝓝 0) := by
  have hs := tendsto_sqrt_nat
  have hlog : Tendsto (fun n : ℕ => Real.log (Real.sqrt n) / (2 * Real.sqrt n)) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 2 0 1 two_ne_zero).comp hs
    refine this.congr (fun n => ?_)
    simp only [Function.comp, pow_one, add_zero]
  have hinner : Tendsto (fun n : ℕ => E / 2 +
      Real.log (Real.sqrt n) / (2 * Real.sqrt n)) atTop (𝓝 (E / 2)) := by
    have := tendsto_const_nhds (x := E / 2) |>.add hlog
    simpa using this
  have hprod : Tendsto (fun n : ℕ => Real.sqrt n * (E / 2 +
      Real.log (Real.sqrt n) / (2 * Real.sqrt n))) atTop atBot :=
    Tendsto.atTop_mul_neg (by linarith) hs hinner
  have hsum : Tendsto (fun n : ℕ => Real.sqrt n * (E / 2 +
      Real.log (Real.sqrt n) / (2 * Real.sqrt n)) + (1 + Real.log b / 2)) atTop atBot :=
    hprod.atBot_add tendsto_const_nhds
  exact Real.tendsto_exp_atBot.comp hsum

/-- the pointwise bound for good `n` -/
lemma pointwise_bound (α b : ℝ) (hα : 0 < α) (hαb : α < b) (n : ℕ) (s : ℝ) (hs_def : s = Real.sqrt n)
    (hsn : α + 1 / α + 2 / (b - α) ≤ s)
    (hGn : stirlingExponent ((⌊α * s⌋₊ : ℝ) / s) ((⌊b * s⌋₊ : ℝ) / s) < stirlingExponent α b / 2) :
    unifProb n (fun σ => b * s ≤ (lis σ : ℝ)) ≤
      Real.exp (s * (stirlingExponent α b / 2 + Real.log s / (2 * s)) + (1 + Real.log b / 2)) := by
  have hb : 0 < b := by linarith
  have hba : 0 < b - α := by linarith
  have hC : 0 < α + 1 / α + 2 / (b - α) := by positivity
  have hs0 : 0 < s := lt_of_lt_of_le hC hsn
  have hn : (n : ℝ) = s ^ 2 := by rw [hs_def, Real.sq_sqrt (Nat.cast_nonneg n)]
  have h1α : 1 / α ≤ s := by
    have : 0 ≤ 2 / (b - α) := by positivity
    linarith
  have h2 : 2 / (b - α) ≤ s := by
    have : 0 ≤ 1 / α := by positivity
    linarith
  have hαs : α ≤ s := by
    have : 0 ≤ 1 / α := by positivity
    have : 0 ≤ 2 / (b - α) := by positivity
    linarith
  obtain ⟨k, hk_def⟩ : ∃ k : ℕ, k = ⌊α * s⌋₊ := ⟨_, rfl⟩
  obtain ⟨r, hr_def⟩ : ∃ r : ℕ, r = ⌊b * s⌋₊ := ⟨_, rfl⟩
  rw [← hk_def, ← hr_def] at hGn
  have hk1 : 1 ≤ k := by
    rw [hk_def]
    apply Nat.le_floor
    rw [Nat.cast_one, ← div_le_iff₀' hα]
    exact h1α
  have hkle : (k : ℝ) ≤ α * s := by rw [hk_def]; exact Nat.floor_le (by positivity)
  have hrgt : b * s < (r : ℝ) + 1 := by rw [hr_def]; exact Nat.lt_floor_add_one _
  have hrle : (r : ℝ) ≤ b * s := by rw [hr_def]; exact Nat.floor_le (by positivity)
  have hkr : k < r := by
    have h2' : 2 ≤ (b - α) * s := by
      rw [div_le_iff₀ hba] at h2; linarith
    have : (k : ℝ) + 1 < r := by nlinarith
    have : k + 1 < r := by exact_mod_cast this
    omega
  have hkn : k ≤ n := by
    have : (k : ℝ) ≤ n := by
      rw [hn]
      calc (k : ℝ) ≤ α * s := hkle
        _ ≤ s * s := by nlinarith
        _ = s ^ 2 := by ring
    exact_mod_cast this
  have step1 : unifProb n (fun σ => b * s ≤ (lis σ : ℝ)) ≤
      unifProb n (fun σ => r ≤ lis σ) := by
    apply unifProb_mono
    intro σ hσ
    rw [hr_def]
    exact Nat.floor_le_of_le hσ
  have step2 := eq_2_4_7_core n k r hk1 hkr.le
  have hB : (0 : ℝ) < (n.choose k : ℝ) / ((k.factorial : ℝ) * (r.choose k : ℝ)) := by
    have : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
    have : (0 : ℝ) < r.choose k := by exact_mod_cast Nat.choose_pos hkr.le
    positivity
  have step3 := log_bound n k r s hs0 hn hk1 hkr hkn
  have hM : (0 : ℝ) < (r : ℝ) - k := by
    have : (k : ℝ) < r := by exact_mod_cast hkr
    linarith
  have hMle : Real.log ((r : ℝ) - k) ≤ Real.log (b * s) := by
    apply Real.log_le_log hM
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have step4 : s * stirlingExponent ((k : ℝ) / s) ((r : ℝ) / s) + 1 + Real.log ((r : ℝ) - k) / 2 ≤
      s * (stirlingExponent α b / 2 + Real.log s / (2 * s)) + (1 + Real.log b / 2) := by
    have e1 : s * (stirlingExponent α b / 2 + Real.log s / (2 * s)) + (1 + Real.log b / 2) =
        s * (stirlingExponent α b / 2) + 1 + Real.log (b * s) / 2 := by
      rw [Real.log_mul hb.ne' hs0.ne']
      field_simp
      ring
    rw [e1]
    have := mul_le_mul_of_nonneg_left hGn.le hs0.le
    linarith
  calc unifProb n (fun σ => b * s ≤ (lis σ : ℝ))
      ≤ unifProb n (fun σ => r ≤ lis σ) := step1
    _ ≤ (n.choose k : ℝ) / ((k.factorial : ℝ) * (r.choose k : ℝ)) := step2
    _ = Real.exp (Real.log ((n.choose k : ℝ) / ((k.factorial : ℝ) * (r.choose k : ℝ)))) :=
        (Real.exp_log hB).symm
    _ ≤ Real.exp (s * (stirlingExponent α b / 2 + Real.log s / (2 * s)) + (1 + Real.log b / 2)) :=
        Real.exp_le_exp.2 (le_trans step3 step4)

theorem eq_2_4_8_core (α b : ℝ) (hα : 0 < α) (hαb : α < b) (h : stirlingExponent α b < 0) :
    Tendsto (fun n : ℕ => unifProb n (fun σ => b * Real.sqrt n ≤ (lis σ : ℝ))) atTop (𝓝 0) := by
  have hb : 0 < b := by linarith
  have hs := tendsto_sqrt_nat
  have hκ := tendsto_floor_div α hα.le
  have hρ := tendsto_floor_div b hb.le
  have hG := (continuous_stirlingExponent.tendsto (α, b)).comp (hκ.prodMk_nhds hρ)
  have hEv := hG.eventually
    (gt_mem_nhds (by linarith : stirlingExponent α b < stirlingExponent α b / 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (tendsto_dom b _ h)
    (Eventually.of_forall fun n => unifProb_nonneg _ _) ?_
  filter_upwards [hEv, hs.eventually_ge_atTop (α + 1 / α + 2 / (b - α))] with n hGn hsn
  exact pointwise_bound α b hα hαb n (Real.sqrt n) rfl hsn hGn

end KingmanSubadditive.Ulam

open KingmanSubadditive.Ulam


theorem solution (α b : ℝ) (hα : 0 < α) (hαb : α < b) (h : stirlingExponent α b < 0) :
    Tendsto (fun n : ℕ => unifProb n (fun σ => b * Real.sqrt n ≤ (lis σ : ℝ))) atTop (𝓝 0) := by
  exact eq_2_4_8_core α b hα hαb h
