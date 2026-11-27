-- Prove2me | solution 1 for LLMThroughput.TokenBudget.Supplement.theorem_10
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:18:46.737788+00:00
-- url     : https://prove2.me/submissions/650ac60d-86bd-4863-92dd-bf7f98775af7

import Mathlib
import Definitions.Def_LLMThroughput_TokenBudget_Supplement_NecessaryCondition9

open LLMThroughput
open LLMThroughput.TokenBudget
open LLMThroughput.TokenBudget.Supplement

/-- Theorem 10, correcting the omitted idle origin using Figure 13 and
Appendix E. This characterizes the necessary relaxation, not stability. -/
theorem solution (a c : ℝ) (b0 bmax kmax : ℕ)
    (ha : 0 < a) (hc : 0 ≤ c) (hb0 : 0 < b0) (hbmax : 0 < bmax)
    (hkmax : 0 < kmax) (hdiv : b0 ∣ bmax) (hk : kmax ≤ b0)
    (lambdaP lambdaD : ℝ) (hP : 0 ≤ lambdaP) (hD : 0 ≤ lambdaD) :
    NecessaryCondition9 a c b0 bmax kmax lambdaP lambdaD ↔
      (lambdaP, lambdaD) ∈ convexHull ℝ
        ({(0, 0),
          ((bmax : ℝ) / batchTime a c (b0 : ℝ) (bmax : ℝ), 0),
          (((bmax : ℝ) - (kmax : ℝ) + 1) /
              batchTime a c (b0 : ℝ) (bmax : ℝ),
            ((kmax : ℝ) - 1) / batchTime a c (b0 : ℝ) (bmax : ℝ)),
          (((b0 : ℝ) - (kmax : ℝ) + 1) /
              batchTime a c (b0 : ℝ) (b0 : ℝ),
            ((kmax : ℝ) - 1) / batchTime a c (b0 : ℝ) (b0 : ℝ)),
          (0, (kmax : ℝ) / batchTime a c (b0 : ℝ) (kmax : ℝ))} : Set (ℝ × ℝ)) := by
            classical
            obtain ⟨m, hm⟩ := hdiv
            have hm1 : 1 ≤ m := by
              rcases Nat.eq_zero_or_pos m with h | h
              · subst h; simp at hm; omega
              · exact h
            have hb0R : (0 : ℝ) < b0 := by exact_mod_cast hb0
            have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
            have hk1R : (1 : ℝ) ≤ kmax := by exact_mod_cast hkmax
            have hkR : (kmax : ℝ) ≤ b0 := by exact_mod_cast hk
            have hbR : (bmax : ℝ) = b0 * m := by rw [hm]; push_cast; ring
            have hb0bmax : b0 ≤ bmax := by rw [hm]; exact Nat.le_mul_of_pos_right _ hm1
            have hT : batchTime a c (b0 : ℝ) (bmax : ℝ) = c + a * m := by
              unfold batchTime
              have : (bmax : ℝ) / b0 = ((m : ℤ) : ℝ) := by
                rw [hbR]; push_cast; field_simp
              rw [this, Int.ceil_intCast]; push_cast; rfl
            have ht : batchTime a c (b0 : ℝ) (b0 : ℝ) = c + a := by
              unfold batchTime
              rw [div_self hb0R.ne']; simp
            have htk : batchTime a c (b0 : ℝ) (kmax : ℝ) = c + a := by
              unfold batchTime
              have : ⌈(kmax : ℝ) / b0⌉ = 1 := by
                rw [Int.ceil_eq_iff]
                constructor
                · have : 0 < (kmax : ℝ) / b0 := by positivity
                  simpa using this
                · rw [div_le_iff₀ hb0R]; simpa using hkR
              rw [this]; simp
            have hTpos : 0 < c + a * m := by
              have : 0 < a * (m : ℝ) := by positivity
              linarith
            have htpos : 0 < c + a := by linarith
            have htT : c + a ≤ c + a * m := by
              have := mul_le_mul_of_nonneg_left hm1R ha.le
              linarith
            have hnot : (0, kmax) ∉ mixedBatches bmax kmax := by
              intro h
              simp [mixedBatches] at h
            have hmem : ∀ s : ℕ × ℕ, s ∈ mixedBatches bmax kmax ↔ (s.2 < kmax ∧ s.1 + s.2 ≤ bmax) := by
              intro s
              unfold mixedBatches
              rw [Finset.mem_filter]
              constructor
              · rintro ⟨h1, h2⟩
                have h1' := Finset.mem_product.mp h1
                simp only [Finset.mem_range] at h1'
                exact ⟨h1'.2, h2⟩
              · rintro ⟨h1, h2⟩
                refine ⟨Finset.mem_product.mpr ?_, h2⟩
                simp only [Finset.mem_range]
                exact ⟨by omega, h1⟩
            rw [hT, ht, htk]
            obtain ⟨r, hr⟩ : ∃ r : ℕ × ℕ → ℝ × ℝ, ∀ s, r s =
              ((s.1 : ℝ) / batchTime a c (b0 : ℝ) ((s.1 : ℝ) + (s.2 : ℝ)),
               (s.2 : ℝ) / batchTime a c (b0 : ℝ) ((s.1 : ℝ) + (s.2 : ℝ))) := ⟨_, fun _ => rfl⟩
            have hrk : r (0, kmax) = (0, (kmax : ℝ) / (c + a)) := by
              simp [hr, htk]
            -- the region as a set
            have hNC : ∀ x y : ℝ, NecessaryCondition9 a c b0 bmax kmax x y ↔
                ∃ u : ℕ × ℕ → ℝ, (∀ s ∈ allocationBatches bmax kmax, 0 ≤ u s) ∧
                  (∑ s ∈ allocationBatches bmax kmax, u s) ≤ 1 ∧
                  x ≤ ∑ s ∈ allocationBatches bmax kmax, (r s).1 * u s ∧
                  y ≤ ∑ s ∈ allocationBatches bmax kmax, (r s).2 * u s := by
              intro x y
              unfold NecessaryCondition9
              have e1 : ∀ u : ℕ × ℕ → ℝ, ∑ s ∈ allocationBatches bmax kmax, (r s).1 * u s =
                  ∑ s ∈ mixedBatches bmax kmax,
                    (s.1 : ℝ) / batchTime a c (b0 : ℝ) ((s.1 : ℝ) + (s.2 : ℝ)) * u s := by
                intro u
                unfold allocationBatches
                rw [Finset.sum_insert hnot, hrk]
                simp [hr]
              have e2 : ∀ u : ℕ × ℕ → ℝ, ∑ s ∈ allocationBatches bmax kmax, (r s).2 * u s =
                  (∑ s ∈ mixedBatches bmax kmax,
                    (s.2 : ℝ) / batchTime a c (b0 : ℝ) ((s.1 : ℝ) + (s.2 : ℝ)) * u s) +
                  (kmax : ℝ) / batchTime a c (b0 : ℝ) (kmax : ℝ) * u (0, kmax) := by
                intro u
                unfold allocationBatches
                rw [Finset.sum_insert hnot, hrk, htk, add_comm]
                simp [hr]
              simp only [e1, e2]
            obtain ⟨S, hS⟩ : ∃ S : Set (ℝ × ℝ), S = convexHull ℝ
              ({(0, 0), ((bmax : ℝ) / (c + a * m), 0),
                (((bmax : ℝ) - (kmax : ℝ) + 1) / (c + a * m), ((kmax : ℝ) - 1) / (c + a * m)),
                (((b0 : ℝ) - (kmax : ℝ) + 1) / (c + a), ((kmax : ℝ) - 1) / (c + a)),
                (0, (kmax : ℝ) / (c + a))} : Set (ℝ × ℝ)) := ⟨_, rfl⟩
            rw [← hS]
            have hconv : Convex ℝ S := hS ▸ convex_convexHull ℝ _
            have hP0 : ((0 : ℝ), (0 : ℝ)) ∈ S := hS ▸ subset_convexHull ℝ _ (by simp)
            have hP1 : ((bmax : ℝ) / (c + a * m), (0 : ℝ)) ∈ S := hS ▸ subset_convexHull ℝ _ (by simp)
            have hP2 : (((bmax : ℝ) - (kmax : ℝ) + 1) / (c + a * m), ((kmax : ℝ) - 1) / (c + a * m)) ∈ S :=
              hS ▸ subset_convexHull ℝ _ (by simp)
            have hP3 : (((b0 : ℝ) - (kmax : ℝ) + 1) / (c + a), ((kmax : ℝ) - 1) / (c + a)) ∈ S :=
              hS ▸ subset_convexHull ℝ _ (by simp)
            have hP4 : ((0 : ℝ), (kmax : ℝ) / (c + a)) ∈ S := hS ▸ subset_convexHull ℝ _ (by simp)
            constructor
            · intro h
              obtain ⟨u, hu0, hu1, hx, hy⟩ := (hNC _ _).mp h
              -- bounds on S
              have hbound : ∀ p ∈ S, p.1 ≤ (bmax : ℝ) / (c + a * m) ∧ p.2 ≤ (kmax : ℝ) / (c + a) := by
                have hc1 : Convex ℝ {p : ℝ × ℝ | p.1 ≤ (bmax : ℝ) / (c + a * m) ∧
                    p.2 ≤ (kmax : ℝ) / (c + a)} := by
                  intro p hp q hq α β hα hβ hαβ
                  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
                    smul_eq_mul] at *
                  have hβ' : β = 1 - α := by linarith
                  constructor
                  · calc α * p.1 + β * q.1 ≤ α * ((bmax : ℝ) / (c + a * m)) + β * ((bmax : ℝ) / (c + a * m)) :=
                        add_le_add (mul_le_mul_of_nonneg_left hp.1 hα) (mul_le_mul_of_nonneg_left hq.1 hβ)
                      _ = _ := by rw [← add_mul, hαβ, one_mul]
                  · calc α * p.2 + β * q.2 ≤ α * ((kmax : ℝ) / (c + a)) + β * ((kmax : ℝ) / (c + a)) :=
                        add_le_add (mul_le_mul_of_nonneg_left hp.2 hα) (mul_le_mul_of_nonneg_left hq.2 hβ)
                      _ = _ := by rw [← add_mul, hαβ, one_mul]
                have hsub : S ⊆ {p : ℝ × ℝ | p.1 ≤ (bmax : ℝ) / (c + a * m) ∧
                    p.2 ≤ (kmax : ℝ) / (c + a)} := by
                  rw [hS]
                  apply convexHull_min _ hc1
                  intro p hp
                  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
                  have hbp : 0 ≤ (bmax : ℝ) / (c + a * m) := by positivity
                  have hkp : 0 ≤ (kmax : ℝ) / (c + a) := by positivity
                  rcases hp with rfl | rfl | rfl | rfl | rfl
                  · exact ⟨hbp, hkp⟩
                  · exact ⟨le_refl _, hkp⟩
                  · refine ⟨?_, ?_⟩
                    · exact div_le_div_of_nonneg_right (by linarith) hTpos.le
                    · exact div_le_div₀ (by linarith) (by linarith) htpos htT
                  · refine ⟨?_, ?_⟩
                    · show ((b0 : ℝ) - (kmax : ℝ) + 1) / (c + a) ≤ (bmax : ℝ) / (c + a * m)
                      rw [div_le_div_iff₀ htpos hTpos, hbR]
                      have h1 : ((b0 : ℝ) - kmax + 1) * (c + a * m) ≤ b0 * (c + a * m) :=
                        mul_le_mul_of_nonneg_right (by linarith) hTpos.le
                      have h2 : 0 ≤ (b0 : ℝ) * c * (m - 1) :=
                        mul_nonneg (mul_nonneg hb0R.le hc) (by linarith)
                      linarith
                    · exact div_le_div_of_nonneg_right (by linarith) htpos.le
                  · exact ⟨hbp, le_refl _⟩
                exact fun p hp => hsub hp
              -- horizontal and vertical axis
              have hseg : ∀ (p q : ℝ × ℝ), p ∈ S → q ∈ S → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
                  ((1 - θ) * p.1 + θ * q.1, (1 - θ) * p.2 + θ * q.2) ∈ S := by
                intro p q hp hq θ h0 h1
                have := hconv hp hq (a := 1 - θ) (b := θ) (by linarith) h0 (by ring)
                exact this
              have hbmaxR : (0 : ℝ) < bmax := by exact_mod_cast hbmax
              have hXpos : 0 < (bmax : ℝ) / (c + a * m) := by positivity
              have hYpos : 0 < (kmax : ℝ) / (c + a) := by positivity
              have hxax : ∀ x : ℝ, 0 ≤ x → x ≤ (bmax : ℝ) / (c + a * m) → (x, (0 : ℝ)) ∈ S := by
                intro x h0 h1
                have := hseg _ _ hP0 hP1 (x / ((bmax : ℝ) / (c + a * m))) (by positivity)
                  ((div_le_one hXpos).mpr h1)
                simp only [mul_zero, zero_add, add_zero] at this
                rwa [div_mul_cancel₀ _ hXpos.ne'] at this
              have hyax : ∀ y : ℝ, 0 ≤ y → y ≤ (kmax : ℝ) / (c + a) → ((0 : ℝ), y) ∈ S := by
                intro x h0 h1
                have := hseg _ _ hP0 hP4 (x / ((kmax : ℝ) / (c + a))) (by positivity)
                  ((div_le_one hYpos).mpr h1)
                simp only [mul_zero, zero_add, add_zero] at this
                rwa [div_mul_cancel₀ _ hYpos.ne'] at this
              have hdown : ∀ x y x' y' : ℝ, (x, y) ∈ S → 0 ≤ x' → x' ≤ x → 0 ≤ y' → y' ≤ y →
                  (x', y') ∈ S := by
                intro x y x' y' hxy h0 h1 h2 h3
                obtain ⟨hbx, hby⟩ := hbound _ hxy
                simp only at hbx hby
                have hx0 : 0 ≤ x := h0.trans h1
                have hy0 : 0 ≤ y := h2.trans h3
                have hxy' : (x', y) ∈ S := by
                  rcases hx0.eq_or_lt with hxe | hxlt
                  · have : x' = 0 := by linarith
                    rw [this]; exact hyax y hy0 hby
                  · have := hseg _ _ (hyax y hy0 hby) hxy (x' / x) (by positivity)
                      ((div_le_one hxlt).mpr h1)
                    simp only [mul_zero, zero_add] at this
                    rw [div_mul_cancel₀ _ hxlt.ne'] at this
                    convert this using 2
                    ring
                rcases hy0.eq_or_lt with hye | hylt
                · have : y' = 0 := by linarith
                  rw [this]; exact hxax x' h0 (h1.trans hbx)
                · have := hseg _ _ (hxax x' h0 (h1.trans hbx)) hxy' (y' / y) (by positivity)
                    ((div_le_one hylt).mpr h3)
                  simp only [mul_zero, zero_add] at this
                  rw [div_mul_cancel₀ _ hylt.ne'] at this
                  convert this using 2
                  ring
              -- Q_n
              have hQ : ∀ n : ℝ, 1 ≤ n → n ≤ m →
                  (((b0 : ℝ) * n - kmax + 1) / (c + a * n), ((kmax : ℝ) - 1) / (c + a * n)) ∈ S := by
                intro n hn1 hnm
                have hnpos : 0 < c + a * n := by
                  have := mul_pos ha (by linarith : 0 < n)
                  linarith
                rcases hm1R.eq_or_lt with hme | hmlt
                · have : n = 1 := by linarith
                  rw [this, mul_one, mul_one]; exact hP3
                · have hd : 0 < (m : ℝ) - 1 := by linarith
                  have hθ0 : 0 ≤ (n - 1) / ((m : ℝ) - 1) * (c + a * m) / (c + a * n) := by
                    have : 0 ≤ n - 1 := by linarith
                    positivity
                  have key : 1 - (n - 1) / ((m : ℝ) - 1) * (c + a * m) / (c + a * n) =
                      ((m : ℝ) - n) / (m - 1) * (c + a) / (c + a * n) := by
                    field_simp
                    ring
                  have hθ1 : (n - 1) / ((m : ℝ) - 1) * (c + a * m) / (c + a * n) ≤ 1 := by
                    have h1 : 0 ≤ (m : ℝ) - n := by linarith
                    have h2 : 0 ≤ ((m : ℝ) - n) / (m - 1) * (c + a) / (c + a * n) := by positivity
                    linarith
                  have := hseg _ _ hP3 hP2 _ hθ0 hθ1
                  rw [key] at this
                  simp only at this
                  rw [hbR] at this
                  convert this using 2
                  · field_simp
                    ring
                  · field_simp
                    ring
              -- each rate point in S
              have hrS : ∀ s ∈ allocationBatches bmax kmax, r s ∈ S := by
                intro s hs
                unfold allocationBatches at hs
                rw [Finset.mem_insert] at hs
                rcases hs with rfl | hs
                · rw [hrk]; exact hP4
                · obtain ⟨p, d⟩ := s
                  obtain ⟨hd, hpd⟩ := (hmem _).mp hs
                  simp only at hd hpd
                  rcases Nat.eq_zero_or_pos (p + d) with h0 | hpos
                  · have hp0 : p = 0 := by omega
                    have hd0 : d = 0 := by omega
                    subst hp0; subst hd0
                    simpa [hr] using hP0
                  · have hposR : (0 : ℝ) < (p : ℝ) + d := by exact_mod_cast hpos
                    have hpdR : (p : ℝ) + d ≤ bmax := by exact_mod_cast hpd
                    have hdk : (d : ℝ) ≤ kmax - 1 := by
                      have : (d : ℝ) + 1 ≤ kmax := by exact_mod_cast hd
                      linarith
                    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
                    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
                    obtain ⟨n, hn⟩ : ∃ n : ℝ, n = ((⌈((p : ℝ) + d) / b0⌉ : ℤ) : ℝ) := ⟨_, rfl⟩
                    have hn1 : 1 ≤ n := by
                      have : 0 < ⌈((p : ℝ) + d) / b0⌉ := Int.ceil_pos.mpr (by positivity)
                      rw [hn]; exact_mod_cast this
                    have hnm : n ≤ m := by
                      have : ⌈((p : ℝ) + d) / b0⌉ ≤ (m : ℤ) := by
                        rw [Int.ceil_le, div_le_iff₀ hb0R]
                        push_cast
                        linarith
                      rw [hn]; exact_mod_cast this
                    have hpn : (p : ℝ) + d ≤ b0 * n := by
                      have := Int.le_ceil (((p : ℝ) + d) / b0)
                      rw [← hn, div_le_iff₀ hb0R] at this
                      linarith
                    have hnpos : 0 < c + a * n := by
                      have := mul_pos ha (by linarith : 0 < n)
                      linarith
                    have hrs : r (p, d) = ((p : ℝ) / (c + a * n), (d : ℝ) / (c + a * n)) := by
                      simp only [hr, batchTime, hn]
                    rw [hrs]
                    -- (b0 n, 0)/τ ∈ S
                    have hA : ((b0 : ℝ) * n / (c + a * n), (0 : ℝ)) ∈ S := by
                      apply hxax
                      · positivity
                      · rw [div_le_div_iff₀ hnpos hTpos, hbR]
                        have : 0 ≤ (b0 : ℝ) * c * (m - n) :=
                          mul_nonneg (mul_nonneg hb0R.le hc) (by linarith)
                        linarith
                    have hB : (((b0 : ℝ) * n - d) / (c + a * n), (d : ℝ) / (c + a * n)) ∈ S := by
                      rcases hd0.eq_or_lt with hde | hdlt
                      · rw [← hde, sub_zero, zero_div]; exact hA
                      · have hkk : 0 < (kmax : ℝ) - 1 := by linarith
                        have := hseg _ _ hA (hQ n hn1 hnm) ((d : ℝ) / (kmax - 1)) (by positivity)
                          ((div_le_one hkk).mpr hdk)
                        simp only at this
                        convert this using 2
                        · field_simp
                          ring
                        · field_simp
                          ring
                    exact hdown _ _ _ _ hB (by positivity)
                      (div_le_div_of_nonneg_right (by linarith) hnpos.le) (by positivity) le_rfl
              have hz : ((0 : ℕ), (0 : ℕ)) ∈ allocationBatches bmax kmax := by
                unfold allocationBatches
                exact Finset.mem_insert_of_mem ((hmem _).mpr ⟨hkmax, by simp⟩)
              have hr0 : r (0, 0) = 0 := by simp [hr]
              have hsum : (∑ s ∈ allocationBatches bmax kmax, (r s).1 * u s,
                  ∑ s ∈ allocationBatches bmax kmax, (r s).2 * u s) ∈ S := by
                obtain ⟨U, hU⟩ : ∃ U, U = ∑ s ∈ allocationBatches bmax kmax, u s := ⟨_, rfl⟩
                have := hconv.sum_mem (t := allocationBatches bmax kmax)
                  (w := fun s => u s + if s = (0, 0) then 1 - U else 0) (z := r) ?_ ?_ hrS
                · convert this using 1
                  simp only [add_smul, Finset.sum_add_distrib, ite_smul, zero_smul]
                  rw [Finset.sum_ite_eq' _ _ _, if_pos hz, hr0, smul_zero, add_zero]
                  ext
                  · simp [Prod.fst_sum, mul_comm]
                  · simp [Prod.snd_sum, mul_comm]
                · intro s hs
                  have := hu0 s hs
                  show 0 ≤ u s + if s = (0, 0) then 1 - U else 0
                  split_ifs <;> linarith
                · rw [Finset.sum_add_distrib, Finset.sum_ite_eq' _ _ _, if_pos hz, ← hU]
                  ring
              exact hdown _ _ _ _ hsum hP hx hD hy
            · intro h
              have hC : Convex ℝ {p : ℝ × ℝ | NecessaryCondition9 a c b0 bmax kmax p.1 p.2} := by
                intro p hp q hq α β hα hβ hαβ
                simp only [Set.mem_ofPred_eq, hNC] at hp hq ⊢
                obtain ⟨u, hu0, hu1, hux, huy⟩ := hp
                obtain ⟨v, hv0, hv1, hvx, hvy⟩ := hq
                have hcomb : ∀ f : ℕ × ℕ → ℝ, ∑ s ∈ allocationBatches bmax kmax, f s * (α * u s + β * v s) =
                    α * ∑ s ∈ allocationBatches bmax kmax, f s * u s +
                    β * ∑ s ∈ allocationBatches bmax kmax, f s * v s := by
                  intro f
                  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                  exact Finset.sum_congr rfl fun s _ => by ring
                refine ⟨fun s => α * u s + β * v s, ?_, ?_, ?_, ?_⟩
                · intro s hs
                  exact add_nonneg (mul_nonneg hα (hu0 s hs)) (mul_nonneg hβ (hv0 s hs))
                · show ∑ s ∈ allocationBatches bmax kmax, (α * u s + β * v s) ≤ 1
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
                  have h1 := mul_le_mul_of_nonneg_left hu1 hα
                  have h2 := mul_le_mul_of_nonneg_left hv1 hβ
                  linarith
                · simp only [hcomb, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
                  exact add_le_add (mul_le_mul_of_nonneg_left hux hα) (mul_le_mul_of_nonneg_left hvx hβ)
                · simp only [hcomb, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
                  exact add_le_add (mul_le_mul_of_nonneg_left huy hα) (mul_le_mul_of_nonneg_left hvy hβ)
              have hpt : ∀ s ∈ allocationBatches bmax kmax,
                  NecessaryCondition9 a c b0 bmax kmax (r s).1 (r s).2 := by
                intro s hs
                rw [hNC]
                refine ⟨fun x => if x = s then 1 else 0, ?_, ?_, ?_, ?_⟩
                · intro x _
                  show (0 : ℝ) ≤ if x = s then 1 else 0
                  split_ifs <;> norm_num
                · rw [Finset.sum_ite_eq' _ _ _, if_pos hs]
                · simp only [mul_ite, mul_one, mul_zero]
                  rw [Finset.sum_ite_eq' _ _ _, if_pos hs]
                · simp only [mul_ite, mul_one, mul_zero]
                  rw [Finset.sum_ite_eq' _ _ _, if_pos hs]
              have hmix : ∀ s : ℕ × ℕ, s.2 < kmax → s.1 + s.2 ≤ bmax →
                  NecessaryCondition9 a c b0 bmax kmax (r s).1 (r s).2 := by
                intro s h1 h2
                exact hpt s (Finset.mem_insert_of_mem ((hmem s).mpr ⟨h1, h2⟩))
              have hk1 : ((kmax - 1 : ℕ) : ℝ) = kmax - 1 := by
                rw [Nat.cast_sub hkmax]; simp
              have hsub : S ⊆ {p : ℝ × ℝ | NecessaryCondition9 a c b0 bmax kmax p.1 p.2} := by
                rw [hS]
                apply convexHull_min _ hC
                intro p hp
                simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
                simp only [Set.mem_ofPred_eq]
                rcases hp with rfl | rfl | rfl | rfl | rfl
                · have := hmix (0, 0) hkmax (by simp)
                  simpa [hr] using this
                · have := hmix (bmax, 0) hkmax (by simp)
                  simpa [hr, hT] using this
                · have := hmix (bmax - (kmax - 1), kmax - 1) (by simp only; omega) (by simp only; omega)
                  have e : ((bmax - (kmax - 1) : ℕ) : ℝ) = bmax - kmax + 1 := by
                    rw [Nat.cast_sub (by omega), hk1]; ring
                  simp only [hr, e, hk1] at this
                  rw [show (bmax : ℝ) - kmax + 1 + (kmax - 1) = bmax by ring, hT] at this
                  exact this
                · have := hmix (b0 - (kmax - 1), kmax - 1) (by simp only; omega) (by simp only; omega)
                  have e : ((b0 - (kmax - 1) : ℕ) : ℝ) = b0 - kmax + 1 := by
                    rw [Nat.cast_sub (by omega), hk1]; ring
                  simp only [hr, e, hk1] at this
                  rw [show (b0 : ℝ) - kmax + 1 + (kmax - 1) = b0 by ring, ht] at this
                  exact this
                · have := hpt (0, kmax) (Finset.mem_insert_self _ _)
                  rw [hrk] at this
                  exact this
              exact hsub h
