-- Prove2me | solution 1 for LeiBR.Async.lemma_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T11:05:32.271529+00:00
-- url     : https://prove2.me/submissions/46b88f97-1051-4c47-ac7f-3640c98e3b86
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Model
import Definitions.Def_LeiBR_Async_Algorithm
import Theorems.Thm_LeiBR_Async_eq_C2
import Theorems.Thm_LeiBR_Async_eq_C3
import Theorems.Thm_LeiBR_Async_normInf_Gamma_lt_one

open MeasureTheory

open LeiBR.Async in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ mΩ) {N : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i))
    (f : Fin N → LeiBR.Sync.Profile n → ℝ) (hA1 : Assumption1ab X f) (μ : ℝ) (hμ : 0 < μ)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : LeiBR.Sync.IsProxBR X f μ xhat) (xs : LeiBR.Sync.Profile n)
    (hNE : LeiBR.Sync.IsNashEq X f xs) (hA5 : Assumption5 X f) (I : ℕ → Finset (Fin N))
    (τ : Fin N → Fin N → ℕ → ℕ) (B1 B2 : ℕ) (hA4 : Assumption4 I τ B1 B2)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (α : Fin N → ℕ → ℝ) (x : ℕ → Ω → LeiBR.Sync.Profile n)
    (halg : IsAlgorithm3 P F X xhat I τ α x) (hα : ∀ i k, α i k = η ^ updCount I i k)
    (C : ℝ) (hC : ∀ i, ∫ ω, ‖x 0 ω i - xs i‖ ∂P ≤ C)
    (ρ c : ℝ) (hρ : ρ = rhoAsync (normInf (LeiBR.Sync.Gamma X f μ)) η B1 B2)
    (hc : c = ρ ^ (1 / (B1 : ℝ))) :
    (∀ k i, ∫ ω, ‖x k ω i - xs i‖ ∂P ≤ (C + k) * ρ ^ (k / B1)) ∧
      ∀ q D : ℝ, c < q → 1 / (Real.exp 1 * Real.log (q / c)) ≤ D →
        ∀ k i, ∫ ω, ‖x k ω i - xs i‖ ∂P ≤ ρ ^ (-((B1 : ℝ) - 1) / B1) * (C + D) * q ^ k := by
  classical
  have ha0 : 0 ≤ normInf (LeiBR.Sync.Gamma X f μ) := by unfold normInf; exact NNReal.coe_nonneg _
  have ha1 : normInf (LeiBR.Sync.Gamma X f μ) < 1 := normInf_Gamma_lt_one X f μ hμ hA5
  have hmax0 : 0 < max (normInf (LeiBR.Sync.Gamma X f μ)) η := lt_of_lt_of_le hη0 (le_max_right _ _)
  have hmax1 : max (normInf (LeiBR.Sync.Gamma X f μ)) η < 1 := max_lt ha1 hη1
  have hρ0 : 0 < ρ := by rw [hρ]; unfold rhoAsync; exact Real.rpow_pos_of_pos hmax0 _
  have hρ1 : ρ < 1 := by
    rw [hρ]; unfold rhoAsync; exact Real.rpow_lt_one hmax0.le hmax1 (by positivity)
  have hρn : ρ ^ (nZero B1 B2 + 1) = max (normInf (LeiBR.Sync.Gamma X f μ)) η := by
    rw [hρ]; unfold rhoAsync
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmax0.le]
    have : (1 / ((nZero B1 B2 : ℝ) + 1)) * ((nZero B1 B2 + 1 : ℕ) : ℝ) = 1 := by
      push_cast; field_simp
    rw [this, Real.rpow_one]
  have haρ : normInf (LeiBR.Sync.Gamma X f μ) ≤ ρ ^ (nZero B1 B2 + 1) := hρn ▸ le_max_left _ _
  have hηρ : η ≤ ρ := by
    have : ρ ^ (nZero B1 B2 + 1) ≤ ρ ^ 1 := pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
    rw [hρn, pow_one] at this
    exact (le_max_right _ _).trans this
  have hB1 := hA4.B1_pos
  -- each window of length `B₁` contains an update
  have hcount : ∀ i m, m ≤ ((Finset.range (m * B1)).filter (fun l => i ∈ I l)).card := by
    intro i m
    induction m with
    | zero => simp
    | succ m ih =>
      obtain ⟨l, hl1, hl2, hl3⟩ := hA4.window i (m * B1)
      have hmul : (m + 1) * B1 = m * B1 + B1 := Nat.succ_mul m B1
      have hsub : insert l ((Finset.range (m * B1)).filter (fun l => i ∈ I l)) ⊆
          (Finset.range ((m + 1) * B1)).filter (fun l => i ∈ I l) := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range] at hy ⊢
        rcases hy with rfl | ⟨hy1, hy2⟩
        · exact ⟨by omega, hl3⟩
        · exact ⟨by omega, hy2⟩
      have hnot : l ∉ (Finset.range (m * B1)).filter (fun l => i ∈ I l) := by
        simp only [Finset.mem_filter, Finset.mem_range, not_and]; intro h; omega
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot] at this
      omega
  have hβ : ∀ i k p, p * B1 ≤ k → i ∈ I k → p + 1 ≤ updCount I i k := by
    intro i k p hp hik
    unfold updCount
    have hsub : insert k ((Finset.range (p * B1)).filter (fun l => i ∈ I l)) ⊆
        (Finset.range (k + 1)).filter (fun l => i ∈ I l) := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range] at hy ⊢
      rcases hy with rfl | ⟨hy1, hy2⟩
      · exact ⟨by omega, hik⟩
      · exact ⟨by omega, hy2⟩
    have hnot : k ∉ (Finset.range (p * B1)).filter (fun l => i ∈ I l) := by
      simp only [Finset.mem_filter, Finset.mem_range, not_and]; intro h; omega
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot] at this
    have := hcount i p
    omega
  have hα0 : ∀ i k, 0 ≤ α i k := fun i k => by rw [hα]; exact (pow_pos hη0 _).le
  have hC2 := eq_C2 P F X f hA1 μ hμ xhat hxhat xs hNE I τ α hα0 x halg
  have hidle : ∀ i l k, (∀ t, l ≤ t → t < k → i ∉ I t) → l ≤ k → ∀ ω, x k ω i = x l ω i := by
    intro i l k h hlk ω
    induction k, hlk using Nat.le_induction with
    | base => rfl
    | succ k hlk ih =>
      rw [halg.idle k i (h k hlk (by omega)) ω, ih (fun t h1 h2 => h t h1 (by omega))]
  have hCnn : ∀ i : Fin N, 0 ≤ C := fun i =>
    (integral_nonneg fun ω => norm_nonneg _).trans (hC i)
  -- (41)
  have h41 : ∀ kbar, ∀ k ≤ kbar, ∀ j, ∫ ω, ‖x k ω j - xs j‖ ∂P ≤ (C + k) * ρ ^ (k / B1) := by
    intro kbar
    induction kbar with
    | zero => intro k hk j; rw [Nat.le_zero.mp hk]; simpa using hC j
    | succ kbar ih =>
      intro k hk j
      rcases Nat.lt_or_eq_of_le hk with hk | rfl
      · exact ih k (by omega) j
      · have hC0 := hCnn j
        have hpk : kbar / B1 * B1 ≤ kbar := Nat.div_mul_le_self kbar B1
        have hkp : kbar < (kbar / B1 + 1) * B1 := by
          have h1 := Nat.div_add_mod kbar B1
          have h2 := Nat.mod_lt kbar hB1
          rw [Nat.succ_mul]; rw [Nat.mul_comm] at h1; omega
        have hexp : (kbar + 1) / B1 ≤ kbar / B1 + 1 := by
          calc (kbar + 1) / B1 ≤ (kbar + B1) / B1 := Nat.div_le_div_right (by omega)
            _ = kbar / B1 + 1 := Nat.add_div_right kbar hB1
        have hC3 := eq_C3 P x xs I τ B1 B2 hA4 halg.delay_le_k C ρ hρ0 hρ1 kbar ih
        by_cases hex : ∃ t, kbar / B1 * B1 ≤ t ∧ t ≤ kbar ∧ j ∈ I t
        · let S := (Finset.Icc (kbar / B1 * B1) kbar).filter (fun t => j ∈ I t)
          have hS : S.Nonempty := by
            obtain ⟨t, h1, h2, h3⟩ := hex
            exact ⟨t, by simp only [S, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨h1, h2⟩, h3⟩⟩
          have hki := S.max'_mem hS
          have hkimax : ∀ t ∈ S, t ≤ S.max' hS := fun t ht => S.le_max' t ht
          set ki := S.max' hS with hkidef
          simp only [S, Finset.mem_filter, Finset.mem_Icc] at hki
          obtain ⟨⟨hki1, hki2⟩, hki3⟩ := hki
          have heq : ∀ ω, x (kbar + 1) ω j = x (ki + 1) ω j := by
            refine hidle j (ki + 1) (kbar + 1) (fun t h1 h2 hjt => ?_) (by omega)
            have := hkimax t (by
              simp only [S, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, by omega⟩, hjt⟩)
            omega
          have hαle : α j ki ≤ ρ ^ (kbar / B1 + 1) := by
            rw [hα]
            calc η ^ updCount I j ki ≤ η ^ (kbar / B1 + 1) :=
                  pow_le_pow_of_le_one hη0.le hη1.le (hβ j ki _ hki1 hki3)
              _ ≤ ρ ^ (kbar / B1 + 1) := pow_le_pow_left₀ hη0.le hηρ _
          have hap : normInf (LeiBR.Sync.Gamma X f μ) * ρ ^ (kbar / B1 - nZero B1 B2) ≤
              ρ ^ (kbar / B1 + 1) := by
            calc normInf (LeiBR.Sync.Gamma X f μ) * ρ ^ (kbar / B1 - nZero B1 B2)
                ≤ ρ ^ (nZero B1 B2 + 1) * ρ ^ (kbar / B1 - nZero B1 B2) :=
                  mul_le_mul_of_nonneg_right haρ (pow_pos hρ0 _).le
              _ ≤ ρ ^ (kbar / B1 + 1) := by
                  rw [← pow_add]; exact pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
          have hki_le : (ki : ℝ) ≤ kbar := by exact_mod_cast hki2
          have hpow : ρ ^ (kbar / B1 + 1) ≤ ρ ^ ((kbar + 1) / B1) :=
            pow_le_pow_of_le_one hρ0.le hρ1.le hexp
          have hint : ∫ ω, ‖x (kbar + 1) ω j - xs j‖ ∂P = ∫ ω, ‖x (ki + 1) ω j - xs j‖ ∂P := by
            congr 1; funext ω; rw [heq ω]
          rw [hint]
          calc ∫ ω, ‖x (ki + 1) ω j - xs j‖ ∂P
              ≤ α j ki + normInf (LeiBR.Sync.Gamma X f μ) *
                  ⨆ j', ∫ ω, ‖x (ki - τ j j' ki) ω j' - xs j'‖ ∂P := hC2 ki j hki3
            _ ≤ ρ ^ (kbar / B1 + 1) + normInf (LeiBR.Sync.Gamma X f μ) *
                  ((C + ki) * ρ ^ (kbar / B1 - nZero B1 B2)) :=
                add_le_add hαle (mul_le_mul_of_nonneg_left (hC3 ki hki1 hki2 j hki3) ha0)
            _ = ρ ^ (kbar / B1 + 1) + (C + ki) *
                  (normInf (LeiBR.Sync.Gamma X f μ) * ρ ^ (kbar / B1 - nZero B1 B2)) := by ring
            _ ≤ ρ ^ (kbar / B1 + 1) + (C + ki) * ρ ^ (kbar / B1 + 1) :=
                add_le_add le_rfl (mul_le_mul_of_nonneg_left hap (add_nonneg hC0 (Nat.cast_nonneg _)))
            _ ≤ (C + ((kbar + 1 : ℕ) : ℝ)) * ρ ^ (kbar / B1 + 1) := by
                push_cast
                have : 0 ≤ ρ ^ (kbar / B1 + 1) := (pow_pos hρ0 _).le
                nlinarith
            _ ≤ (C + ((kbar + 1 : ℕ) : ℝ)) * ρ ^ ((kbar + 1) / B1) :=
                mul_le_mul_of_nonneg_left hpow (add_nonneg hC0 (Nat.cast_nonneg _))
        · push Not at hex
          obtain ⟨t, ht1, ht2, ht3⟩ := hA4.window j (kbar / B1 * B1)
          have htk : kbar < t := by
            by_contra hcon; exact hex t ht1 (by omega) ht3
          have hdiv : (kbar + 1) / B1 = kbar / B1 := by
            apply Nat.div_eq_of_lt_le
            · omega
            · rw [Nat.succ_mul]; omega
          have hnot : j ∉ I kbar := hex kbar hpk le_rfl
          have hint : ∫ ω, ‖x (kbar + 1) ω j - xs j‖ ∂P = ∫ ω, ‖x kbar ω j - xs j‖ ∂P := by
            congr 1; funext ω; rw [halg.idle kbar j hnot ω]
          rw [hint, hdiv]
          refine (ih kbar le_rfl j).trans ?_
          have : 0 ≤ ρ ^ (kbar / B1) := (pow_pos hρ0 _).le
          push_cast
          nlinarith
  refine ⟨fun k i => h41 k k le_rfl i, ?_⟩
  -- (42)
  intro q D hcq hD k i
  have hC0 := hCnn i
  have hB1r : (0 : ℝ) < B1 := by exact_mod_cast hB1
  have hcpos : 0 < c := by rw [hc]; exact Real.rpow_pos_of_pos hρ0 _
  -- ρ^{⌊k/B₁⌋} ≤ ρ^{-(B₁-1)/B₁} c^k
  have hfl : ρ ^ (k / B1) ≤ ρ ^ (-((B1 : ℝ) - 1) / B1) * c ^ k := by
    have h1 := Nat.div_add_mod k B1
    have h2 := Nat.mod_lt k hB1
    have hkle : (k : ℝ) ≤ B1 * ((k / B1 : ℕ) : ℝ) + B1 - 1 := by
      have : k + 1 ≤ B1 * (k / B1) + B1 := by omega
      have : ((k + 1 : ℕ) : ℝ) ≤ ((B1 * (k / B1) + B1 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    have hexp : ((k : ℝ) - (B1 - 1)) / B1 ≤ ((k / B1 : ℕ) : ℝ) := by
      rw [div_le_iff₀ hB1r]; linarith
    calc ρ ^ (k / B1) = ρ ^ (((k / B1 : ℕ) : ℝ)) := (Real.rpow_natCast _ _).symm
      _ ≤ ρ ^ (((k : ℝ) - (B1 - 1)) / B1) :=
          Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1.le hexp
      _ = ρ ^ (-((B1 : ℝ) - 1) / B1) * c ^ k := by
          have : ((k : ℝ) - (B1 - 1)) / B1 = -((B1 : ℝ) - 1) / B1 + (1 / (B1 : ℝ)) * k := by
            field_simp; ring
          rw [this, Real.rpow_add hρ0, Real.rpow_mul hρ0.le, Real.rpow_natCast, hc]
  -- Lemma 2 (in the form `k c^k ≤ D q^k`, valid for every `q > c`)
  have hL : 0 < Real.log (q / c) := Real.log_pos ((one_lt_div hcpos).mpr hcq)
  have hck : (k : ℝ) * c ^ k ≤ D * q ^ k := by
    have hqc : 0 < q / c := div_pos (hcpos.trans hcq) hcpos
    have hu : Real.exp (k * Real.log (q / c)) = (q / c) ^ k := by
      rw [← Real.log_pow, Real.exp_log (pow_pos hqc k)]
    have h := Real.add_one_le_exp (k * Real.log (q / c) - 1)
    rw [Real.exp_sub, hu, sub_add_cancel, div_pow] at h
    have h3 : k * Real.log (q / c) * Real.exp 1 ≤ q ^ k / c ^ k := by
      have h' : (q ^ k / c ^ k) / Real.exp 1 = q ^ k / c ^ k * (Real.exp 1)⁻¹ := by ring
      rw [h'] at h
      have he := Real.exp_pos 1
      calc k * Real.log (q / c) * Real.exp 1 ≤ q ^ k / c ^ k * (Real.exp 1)⁻¹ * Real.exp 1 :=
            mul_le_mul_of_nonneg_right h he.le
        _ = q ^ k / c ^ k := by field_simp
    have key : (k : ℝ) * c ^ k * (Real.exp 1 * Real.log (q / c)) ≤ q ^ k := by
      calc (k : ℝ) * c ^ k * (Real.exp 1 * Real.log (q / c))
          = (k * Real.log (q / c) * Real.exp 1) * c ^ k := by ring
        _ ≤ (q ^ k / c ^ k) * c ^ k := mul_le_mul_of_nonneg_right h3 (pow_pos hcpos k).le
        _ = q ^ k := div_mul_cancel₀ _ (pow_pos hcpos k).ne'
    have hpos : 0 < Real.exp 1 * Real.log (q / c) := mul_pos (Real.exp_pos 1) hL
    calc (k : ℝ) * c ^ k ≤ q ^ k / (Real.exp 1 * Real.log (q / c)) := by
          rw [le_div_iff₀ hpos]; exact key
      _ = 1 / (Real.exp 1 * Real.log (q / c)) * q ^ k := by ring
      _ ≤ D * q ^ k := mul_le_mul_of_nonneg_right hD (pow_pos (hcpos.trans hcq) k).le
  have hckq : c ^ k ≤ q ^ k := pow_le_pow_left₀ hcpos.le hcq.le k
  have hr : 0 ≤ ρ ^ (-((B1 : ℝ) - 1) / B1) := (Real.rpow_pos_of_pos hρ0 _).le
  calc ∫ ω, ‖x k ω i - xs i‖ ∂P ≤ (C + k) * ρ ^ (k / B1) := h41 k k le_rfl i
    _ ≤ (C + k) * (ρ ^ (-((B1 : ℝ) - 1) / B1) * c ^ k) :=
        mul_le_mul_of_nonneg_left hfl (add_nonneg hC0 (Nat.cast_nonneg k))
    _ = ρ ^ (-((B1 : ℝ) - 1) / B1) * (C * c ^ k + k * c ^ k) := by ring
    _ ≤ ρ ^ (-((B1 : ℝ) - 1) / B1) * (C * q ^ k + D * q ^ k) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hckq hC0) hck) hr
    _ = ρ ^ (-((B1 : ℝ) - 1) / B1) * (C + D) * q ^ k := by ring
