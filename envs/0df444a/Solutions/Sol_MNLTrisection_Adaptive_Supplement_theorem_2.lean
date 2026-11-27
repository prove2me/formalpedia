-- Prove2me | solution 1 for MNLTrisection.Adaptive.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:18:30.490936+00:00
-- url     : https://prove2.me/submissions/a872e23e-d35b-441a-ac22-ebf2a4b7987d

import Mathlib
import Definitions.Def_MNLTrisection_Adaptive_Supplement_Baseline

open MNLTrisection
open MNLTrisection.Adaptive
open MNLTrisection.Adaptive.Supplement

/-- Theorem 2, PDF p.10 (corrected horizon T ≥ 2). C is absolute,
chosen before dimensions, horizons and all model parameters. -/
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (N T : ℕ), 2 ≤ T →
      ∀ (v r : Fin N → ℝ), (∀ i, 0 ≤ v i) → (∀ i, r i ∈ Set.Icc 0 1) →
        MNLBandit.UCB.regret v r Finset.univ ⟨∅, Finset.mem_univ _⟩
          (baselinePolicy r T) T ≤ C * Real.sqrt ((T : ℝ) * Real.log T) := by
            have hoeff : ∀ (N : ℕ) (p X : Option (Fin N) → ℝ) (F l : ℝ), (∀ c, 0 ≤ p c) → (∑ c, p c = 1) →
                (∀ c, X c ∈ Set.Icc (0:ℝ) 1) → (∑ c, p c * X c = F) →
                ∑ c, p c * Real.exp (l * (X c - F)) ≤ Real.exp (l ^ 2 / 8) := by
              intro N p X F l hp hp1 hX hF
              let _ : MeasurableSpace (Option (Fin N)) := ⊤
              let μ : MeasureTheory.Measure (Option (Fin N)) :=
                ∑ c, ENNReal.ofReal (p c) • MeasureTheory.Measure.dirac c
              have hint : ∀ f : Option (Fin N) → ℝ, ∫ c, f c ∂μ = ∑ c, p c * f c := by
                intro f
                rw [MeasureTheory.integral_finsetSum_measure]
                · refine Finset.sum_congr rfl (fun c _ => ?_)
                  rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac]
                  simp [ENNReal.toReal_ofReal (hp c)]
                · intro c _
                  exact (MeasureTheory.integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
              have _ : MeasureTheory.IsProbabilityMeasure μ := by
                constructor
                simp only [μ, MeasureTheory.Measure.coe_finsetSum, Finset.sum_apply,
                  MeasureTheory.Measure.smul_apply, MeasureTheory.measure_univ, smul_eq_mul, mul_one]
                rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => hp c), hp1, ENNReal.ofReal_one]
              have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := X) (a := 0) (b := 1)
                (measurable_from_top).aemeasurable (Filter.Eventually.of_forall hX)
              have h2 := h.mgf_le l
              rw [ProbabilityTheory.mgf, hint, hint, hF] at h2
              refine h2.trans (le_of_eq ?_)
              congr 1
              simp
              ring
            have choiceFacts : ∀ (N : ℕ) (v r : Fin N → ℝ), (∀ i, 0 ≤ v i) → ∀ S : Finset (Fin N),
                (∀ c, 0 ≤ MNLBandit.UCB.choiceProb v S c) ∧ (∑ c, MNLBandit.UCB.choiceProb v S c = 1) ∧
                (∑ c, MNLBandit.UCB.choiceProb v S c * choiceRev r c = rev v r S) := by
              intro N v r hv S
              have hs : 0 ≤ ∑ j ∈ S, v j := Finset.sum_nonneg (fun i _ => hv i)
              have hs1 : (1 + ∑ j ∈ S, v j) ≠ 0 := by positivity
              refine ⟨?_, ?_, ?_⟩
              · intro c
                cases c with
                | none => simp only [MNLBandit.UCB.choiceProb]; positivity
                | some i =>
                  simp only [MNLBandit.UCB.choiceProb]
                  split_ifs
                  · exact div_nonneg (hv i) (by positivity)
                  · exact le_rfl
              · rw [Fintype.sum_option]
                simp only [MNLBandit.UCB.choiceProb]
                rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_div,
                  ← add_div, div_self hs1]
              · rw [Fintype.sum_option]
                simp only [MNLBandit.UCB.choiceProb, choiceRev, mul_zero, zero_add, ite_mul, zero_mul]
                rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
                unfold rev ChoiceCDLP.MNL.mnlObjective
                rw [Finset.sum_div, add_comm (∑ j ∈ S, v j) 1]
                exact Finset.sum_congr rfl (fun i _ => by ring)

            have revFacts : ∀ (N : ℕ) (v r : Fin N → ℝ), (∀ i, 0 ≤ v i) → (∀ i, r i ∈ Set.Icc (0:ℝ) 1) →
                (∀ S, 0 ≤ rev v r S) ∧ (∀ S, rev v r S ≤ optRev v r) ∧ optRev v r ≤ 1 ∧
                (∀ θ, θ ≤ optRev v r → θ ≤ F v r θ) := by
              intro N v r hv hr
              have hpos : ∀ S : Finset (Fin N), 0 < ∑ j ∈ S, v j + 1 := fun S => by
                have : 0 ≤ ∑ j ∈ S, v j := Finset.sum_nonneg (fun i _ => hv i)
                linarith
              refine ⟨?_, ?_, ?_, ?_⟩
              · intro S
                exact div_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hr i).1 (hv i))) (hpos S).le
              · intro S
                exact Finset.le_sup' (fun S => ChoiceCDLP.MNL.mnlObjective v r 1 S) (Finset.mem_univ S)
              · refine Finset.sup'_le (⟨∅, Finset.mem_univ _⟩ : (Finset.univ : Finset (Finset (Fin N))).Nonempty) _ (fun S _ => ?_)
                unfold ChoiceCDLP.MNL.mnlObjective
                rw [div_le_one (hpos S)]
                have : ∑ j ∈ S, r j * v j ≤ ∑ j ∈ S, v j := Finset.sum_le_sum (fun i _ => by
                  nlinarith [(hr i).2, hv i])
                linarith
              · intro θ hθ
                obtain ⟨S, -, hS⟩ := Finset.exists_mem_eq_sup' (⟨∅, Finset.mem_univ _⟩ : (Finset.univ : Finset (Finset (Fin N))).Nonempty)
                  (fun S => ChoiceCDLP.MNL.mnlObjective v r 1 S)
                have hS' : optRev v r = ChoiceCDLP.MNL.mnlObjective v r 1 S := hS
                rw [hS'] at hθ
                unfold ChoiceCDLP.MNL.mnlObjective at hθ
                rw [le_div_iff₀ (hpos S)] at hθ
                unfold F rev ChoiceCDLP.MNL.mnlObjective
                rw [le_div_iff₀ (hpos _)]
                have h1 : ∑ j ∈ S, (r j - θ) * v j ≤ ∑ j ∈ levelSet r θ, (r j - θ) * v j := by
                  unfold levelSet
                  rw [Finset.sum_filter]
                  calc ∑ j ∈ S, (r j - θ) * v j ≤ ∑ j ∈ S, (if θ ≤ r j then (r j - θ) * v j else 0) := by
                        refine Finset.sum_le_sum (fun i _ => ?_)
                        split_ifs with h
                        · exact le_rfl
                        · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hv i)
                    _ ≤ _ := by
                        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => ?_)
                        split_ifs with h
                        · exact mul_nonneg (by linarith) (hv i)
                        · exact le_rfl
                have h2 : ∀ S : Finset (Fin N), ∑ j ∈ S, (r j - θ) * v j = ∑ j ∈ S, r j * v j - θ * ∑ j ∈ S, v j := by
                  intro S
                  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
                  exact Finset.sum_congr rfl (fun i _ => by ring)
                rw [h2, h2] at h1
                linarith
            have expect : ∀ (N : ℕ) (v r : Fin N → ℝ), (∀ i, 0 ≤ v i) → ∀ (T : ℕ) (W : List (Option (Fin N)) → ℝ),
                (∀ l : List (Option (Fin N)), l.length < T → 
                  ∑ c, MNLBandit.UCB.choiceProb v (offerOf r (l.foldl (baselineStep r T) initState)) c * W (l ++ [c]) ≤ W l) →
                ∑ h : MNLBandit.UCB.History N T, MNLBandit.UCB.histProb v (baselinePolicy r T) h * W (List.ofFn h) ≤ W [] := by
              intro N v r hv T W hW
              have hnn : ∀ (M : ℕ) (h : MNLBandit.UCB.History N M), 0 ≤ MNLBandit.UCB.histProb v (baselinePolicy r T) h := by
                intro M h
                exact Finset.prod_nonneg (fun t _ => (choiceFacts N v r hv _).1 _)
              have key : ∀ M, M ≤ T → ∑ h : MNLBandit.UCB.History N M, MNLBandit.UCB.histProb v (baselinePolicy r T) h * W (List.ofFn h) ≤ W [] := by
                intro M
                induction M with
                | zero =>
                  intro _
                  simp [MNLBandit.UCB.histProb]
                | succ M ih =>
                  intro hM
                  refine le_trans ?_ (ih (by omega))
                  have hprob : ∀ (p : Fin M → Option (Fin N)) (c : Option (Fin N)),
                      MNLBandit.UCB.histProb v (baselinePolicy r T) (Fin.snoc p c : Fin (M+1) → Option (Fin N)) =
                      MNLBandit.UCB.histProb v (baselinePolicy r T) p *
                        MNLBandit.UCB.choiceProb v (offerOf r ((List.ofFn p).foldl (baselineStep r T) initState)) c := by
                    intro p c
                    unfold MNLBandit.UCB.histProb
                    rw [Fin.prod_univ_castSucc]
                    congr 1
                    · refine Finset.prod_congr rfl (fun t _ => ?_)
                      have : MNLBandit.UCB.offered (baselinePolicy r T) (Fin.snoc p c : Fin (M+1) → Option (Fin N)) t.castSucc
                          = MNLBandit.UCB.offered (baselinePolicy r T) p t := by
                        unfold MNLBandit.UCB.offered
                        have : MNLBandit.UCB.histPrefix (Fin.snoc p c : Fin (M+1) → Option (Fin N)) t.castSucc
                            = MNLBandit.UCB.histPrefix p t := by
                          funext u
                          unfold MNLBandit.UCB.histPrefix
                          have : Fin.castLE (t.castSucc).isLt.le u = Fin.castSucc (Fin.castLE t.isLt.le u) := rfl
                          rw [this, Fin.snoc_castSucc]
                        rw [this]
                        rfl
                      rw [this, Fin.snoc_castSucc]
                    · rw [Fin.snoc_last]
                      have : MNLBandit.UCB.histPrefix (Fin.snoc p c : Fin (M+1) → Option (Fin N)) (Fin.last M) = p := by
                        funext u
                        unfold MNLBandit.UCB.histPrefix
                        have : Fin.castLE (Fin.last M).isLt.le u = Fin.castSucc u := rfl
                        rw [this, Fin.snoc_castSucc]
                      unfold MNLBandit.UCB.offered
                      rw [this]
                      rfl
                  have hlist : ∀ (p : Fin M → Option (Fin N)) (c : Option (Fin N)),
                      List.ofFn (Fin.snoc p c : Fin (M+1) → Option (Fin N)) = List.ofFn p ++ [c] := by
                    intro p c
                    rw [List.ofFn_succ']
                    simp
                  have hsum : ∑ h : MNLBandit.UCB.History N (M+1), MNLBandit.UCB.histProb v (baselinePolicy r T) h * W (List.ofFn h)
                      = ∑ p : MNLBandit.UCB.History N M, ∑ c : Option (Fin N), MNLBandit.UCB.histProb v (baselinePolicy r T) (Fin.snoc p c : Fin (M+1) → Option (Fin N)) * W (List.ofFn (Fin.snoc p c : Fin (M+1) → Option (Fin N))) := by
                    rw [Finset.sum_comm, ← Fintype.sum_prod_type']
                    exact (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (M+1) => Option (Fin N))) _ _ (fun x => rfl)).symm
                  rw [hsum]
                  refine Finset.sum_le_sum (fun p _ => ?_)
                  have := hW (List.ofFn p) (by simp; omega)
                  calc _ = MNLBandit.UCB.histProb v (baselinePolicy r T) p * ∑ c, MNLBandit.UCB.choiceProb v (offerOf r ((List.ofFn p).foldl (baselineStep r T) initState)) c * W (List.ofFn p ++ [c]) := by
                        rw [Finset.mul_sum]
                        refine Finset.sum_congr rfl (fun c _ => ?_)
                        rw [hprob, hlist]; ring
                    _ ≤ _ := mul_le_mul_of_nonneg_left this (hnn _ _)
              exact key T le_rfl
            have logT : ∀ T : ℕ, 2 ≤ T → (0.69:ℝ) < Real.log (T:ℝ) ∧ Real.log (T:ℝ) ≤ T := by
              intro T hT
              have h2 : (2:ℝ) ≤ T := by exact_mod_cast hT
              refine ⟨?_, ?_⟩
              · have := Real.log_two_gt_d9
                have h3 := Real.log_le_log (by norm_num) h2
                linarith
              · have := Real.log_le_sub_one_of_pos (show (0:ℝ) < T by linarith)
                linarith

            have innerFacts : ∀ T : ℕ, 2 ≤ T → ∀ l : ℝ, 0 < l → l ≤ 1 →
                ((baselineInnerLen T (l/3) : ℕ) : ℝ) * l ^ 2 ≤ 288 * Real.log (T:ℝ) ∧
                144 * Real.log (T:ℝ) ≤ ((baselineInnerLen T (l/3) : ℕ) : ℝ) * l ^ 2 ∧ 0 < baselineInnerLen T (l/3) := by
              intro T hT l hl hl1
              obtain ⟨hL, -⟩ := logT T hT
              unfold baselineInnerLen
              set z := (l/3)⁻¹ ^ 2 * Real.log (T:ℝ) with hz
              have hzl : z * l ^ 2 = 9 * Real.log (T:ℝ) := by
                rw [hz]; field_simp; norm_num
              have hl2 : l ^ 2 ≤ 1 := by nlinarith
              have hz1 : 1 ≤ z := by
                have : 0 < l ^ 2 := by positivity
                by_contra hc
                push Not at hc
                have h5 := mul_lt_mul_of_pos_right hc this
                linarith only [h5, hzl, hl2, hL]
              have h1 := Nat.le_ceil z
              have h2 := Nat.ceil_lt_add_one (show (0:ℝ) ≤ z by linarith)
              have hl0 : 0 < l ^ 2 := by positivity
              refine ⟨?_, ?_, ?_⟩
              · push_cast
                have h5 := mul_le_mul_of_nonneg_right (show (⌈z⌉₊:ℝ) ≤ 2 * z by linarith only [h2, hz1]) hl0.le
                linarith only [h5, hzl]
              · push_cast
                have h5 := mul_le_mul_of_nonneg_right h1 hl0.le
                linarith only [h5, hzl]
              · have : 0 < ⌈z⌉₊ := Nat.ceil_pos.mpr (by linarith)
                omega

            have radFacts : ∀ T : ℕ, ∀ m : ℕ, baselineRadius T m = Real.sqrt (Real.log (T:ℝ) / m) := by
              intro T m
              unfold baselineRadius
              rw [Real.log_pow]
              congr 1
              push_cast
              by_cases h : (m:ℝ) = 0
              · simp [h]
              · field_simp

            have epochArith : ∀ T : ℕ, 2 ≤ T → ∀ l : ℝ, 0 < l → l ≤ 1 → ∀ R g : ℝ, ∀ k m : ℕ,
                k + 1 = baselineInnerLen T (l/3) → m ≤ k + 1 → g ≤ l →
                R ≤ 1400 * Real.log (T:ℝ) / l + l * (k + m) + 6 * Real.sqrt (m * Real.log (T:ℝ)) →
                R + g ≤ 1400 * Real.log (T:ℝ) / (2 / 3 * l) := by
              intro T hT l hl hl1 R g k m hk hm hg hR
              obtain ⟨hL, -⟩ := logT T hT
              obtain ⟨h1, h2, h3⟩ := innerFacts T hT l hl hl1
              rw [← hk] at h1 h2
              push_cast at h1 h2
              set L := Real.log (T:ℝ) with hLd
              have hmr : (m:ℝ) ≤ k + 1 := by exact_mod_cast hm
              have hs : Real.sqrt (m * L) ≤ 17 * L / l := by
                rw [Real.sqrt_le_left (by positivity)]
                rw [div_pow, le_div_iff₀ (by positivity)]
                have : (m:ℝ) * l ^ 2 ≤ 288 * L := by
                  exact (mul_le_mul_of_nonneg_right hmr (by positivity)).trans h1
                have h5 := mul_le_mul_of_nonneg_right this (show (0:ℝ) ≤ L by linarith only [hL])
                have h6 : 0 ≤ L * L := mul_self_nonneg L
                linarith only [h5, h6]
              have hs2 : l * (k + m) + l ≤ 576 * L / l := by
                rw [le_div_iff₀ hl]
                have h5 := mul_le_mul_of_nonneg_right hmr (sq_nonneg l)
                linarith only [h5, h1]
              have e1 : 1400 * L / (2 / 3 * l) = 1400 * L / l + 700 * L / l := by
                field_simp; ring
              have e2 : 700 * L / l = 576 * L / l + 6 * (17 * L / l) + 22 * L / l := by
                field_simp; ring
              have e3 : 0 ≤ 22 * L / l := by positivity
              rw [e1, e2]
              linarith only [hR, hg, hs, hs2, e3]

            have finalArith : ∀ T : ℕ, 2 ≤ T → ∀ l : ℝ, 0 < l → l ≤ 1 → ∀ R : ℝ, ∀ k m : ℕ,
                k < baselineInnerLen T (l/3) → m ≤ k + 1 → k ≤ T → Real.log (T:ℝ) ≤ T * l ^ 2 →
                R ≤ 1400 * Real.log (T:ℝ) / l + l * (k + m) + 6 * Real.sqrt (m * Real.log (T:ℝ)) →
                R ≤ 1500 * Real.sqrt (T * Real.log (T:ℝ)) := by
              intro T hT l hl hl1 R k m hk hm hkT hl7 hR
              obtain ⟨hL, hLT⟩ := logT T hT
              obtain ⟨h1, h2, h3⟩ := innerFacts T hT l hl hl1
              set L := Real.log (T:ℝ) with hLd
              have h2T : (2:ℝ) ≤ T := by exact_mod_cast hT
              have hmr : (m:ℝ) ≤ k + 1 := by exact_mod_cast hm
              have hkr : (k:ℝ) ≤ T := by exact_mod_cast hkT
              have hkn : (k:ℝ) ≤ baselineInnerLen T (l/3) := by exact_mod_cast hk.le
              have hl2 : 0 < l ^ 2 := by positivity
              have hk2 : (k:ℝ) * l ^ 2 ≤ 288 * L := (mul_le_mul_of_nonneg_right hkn hl2.le).trans h1
              have hTL : 0 ≤ (T:ℝ) * L := by positivity
              have a1 : L / l ≤ Real.sqrt (T * L) := by
                apply Real.le_sqrt_of_sq_le
                rw [div_pow, div_le_iff₀ hl2]
                have := mul_le_mul_of_nonneg_left hl7 (show (0:ℝ) ≤ L by linarith only [hL])
                calc L ^ 2 = L * L := by ring
                  _ ≤ L * (T * l ^ 2) := this
                  _ = T * L * l ^ 2 := by ring
              have a2 : l * k ≤ 17 * Real.sqrt (T * L) := by
                have : l * k / 17 ≤ Real.sqrt (T * L) := by
                  apply Real.le_sqrt_of_sq_le
                  have : (l * k) ^ 2 ≤ 288 * L * T := by
                    have hk0 : (0:ℝ) ≤ k := by positivity
                    calc (l * k)^2 = (k * l^2) * k := by ring
                      _ ≤ (288 * L) * k := mul_le_mul_of_nonneg_right hk2 hk0
                      _ ≤ 288 * L * T := mul_le_mul_of_nonneg_left hkr (by positivity)
                  rw [div_pow]
                  linarith only [this, hTL]
                linarith only [this]
              have a3 : Real.sqrt (m * L) ≤ 2 * Real.sqrt (T * L) := by
                have : Real.sqrt (m * L) / 2 ≤ Real.sqrt (T * L) := by
                  apply Real.le_sqrt_of_sq_le
                  rw [div_pow, Real.sq_sqrt (by positivity)]
                  have hm4 : (m:ℝ) ≤ 4 * T := by linarith only [hmr, hkr, h2T]
                  have := mul_le_mul_of_nonneg_right hm4 (show (0:ℝ) ≤ L by linarith only [hL])
                  linarith only [this]
                linarith only [this]
              have a4 : l ≤ 2 * Real.sqrt (T * L) := by
                have : l / 2 ≤ Real.sqrt (T * L) := by
                  apply Real.le_sqrt_of_sq_le
                  rw [div_pow]
                  have e1 : l ^ 2 ≤ 1 := pow_le_one₀ hl.le hl1
                  have e2 := mul_le_mul_of_nonneg_right h2T (show (0:ℝ) ≤ L by linarith only [hL])
                  linarith only [e1, e2, hL]
                linarith only [this]
              have a5 : 1400 * L / l = 1400 * (L / l) := by ring
              have a6 : l * m ≤ l * k + l := by
                have := mul_le_mul_of_nonneg_left hmr hl.le
                linarith only [this]
              rw [a5] at hR
              have : l * ((k:ℝ) + m) = l * k + l * m := by ring
              linarith only [this, hR, a1, a2, a3, a4, a6, Real.sqrt_nonneg ((T:ℝ) * L)]

            have sqrtInc : ∀ L : ℝ, 0.69 < L → ∀ k : ℕ, ∀ g l : ℝ, 0 ≤ l → g ≤ 1 → 
                (1 ≤ k → g ≤ max l (2 * Real.sqrt (L / k))) →
                g ≤ l + 6 * (Real.sqrt ((k+1 : ℕ) * L) - Real.sqrt (k * L)) := by
              intro L hL k g l hl hg h
              rcases Nat.eq_zero_or_pos k with h0 | h0
              · subst h0
                have : (1:ℝ)/6 ≤ Real.sqrt L := Real.le_sqrt_of_sq_le (by norm_num; linarith)
                simp
                linarith
              · have hk : (1:ℝ) ≤ k := by exact_mod_cast h0
                have hmono : Real.sqrt (k * L) ≤ Real.sqrt ((k+1 : ℕ) * L) := by
                  apply Real.sqrt_le_sqrt; push_cast; nlinarith
                rcases le_max_iff.mp (h h0) with h1 | h1
                · linarith
                · have key : Real.sqrt (L / k) ≤ 3 * (Real.sqrt ((k+1 : ℕ) * L) - Real.sqrt (k * L)) := by
                    push_cast
                    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_div' _ (by positivity)]
                    have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
                    have hsk : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr (by linarith)
                    have e1 : Real.sqrt (k:ℝ) ^ 2 = k := Real.sq_sqrt (by linarith)
                    have e2 : Real.sqrt ((k:ℝ)+1) ^ 2 = k+1 := Real.sq_sqrt (by linarith)
                    have h3 : Real.sqrt ((k:ℝ)+1) ≤ 2 * Real.sqrt (k:ℝ) := by
                      rw [Real.sqrt_le_left (by positivity)]
                      rw [mul_pow, e1]; linarith
                    have h4 : 1 / Real.sqrt (k:ℝ) ≤ 3 * (Real.sqrt ((k:ℝ)+1) - Real.sqrt (k:ℝ)) := by
                      rw [div_le_iff₀ hsk]
                      have h5 : Real.sqrt (k:ℝ) ≤ Real.sqrt ((k:ℝ)+1) := Real.sqrt_le_sqrt (by linarith)
                      have h6 := mul_le_mul_of_nonneg_right h3 hsk.le
                      have h7 : (Real.sqrt ((k:ℝ)+1) - Real.sqrt (k:ℝ)) * (Real.sqrt ((k:ℝ)+1) + Real.sqrt (k:ℝ)) = 1 := by
                        have : (Real.sqrt ((k:ℝ)+1) - Real.sqrt (k:ℝ)) * (Real.sqrt ((k:ℝ)+1) + Real.sqrt (k:ℝ)) = Real.sqrt ((k:ℝ)+1)^2 - Real.sqrt (k:ℝ)^2 := by ring
                        rw [this, e1, e2]; ring
                      have h8 := mul_le_mul_of_nonneg_left (show Real.sqrt ((k:ℝ)+1) + Real.sqrt (k:ℝ) ≤ 3 * Real.sqrt (k:ℝ) by linarith only [h3]) (sub_nonneg.mpr h5)
                      linarith only [h7, h8]
                    have : Real.sqrt L / Real.sqrt (k:ℝ) = Real.sqrt L * (1 / Real.sqrt (k:ℝ)) := by ring
                    rw [this]
                    have := mul_le_mul_of_nonneg_left h4 hsL
                    linarith only [this]
                  linarith only [h1, key, hl]
            have detStep : ∀ (N : ℕ) (r : Fin N → ℝ) (T : ℕ), 2 ≤ T → ∀ (Fn : ℝ → ℝ) (Rs : ℝ), 
                (∀ θ, 0 ≤ Fn θ) → (∀ θ, Fn θ ≤ Rs) → Rs ≤ 1 → (∀ θ, θ ≤ Rs → θ ≤ Fn θ) →
                ∀ Inv : AlgState → ℝ → ℕ → Prop, 
                (∀ s R n, Inv s R n ↔ (s.b - s.a = (2/3:ℝ)^s.tau ∧ s.a ≤ Rs ∧ Rs ≤ s.b ∧ s.lo ≤ Fn s.y ∧ Fn s.y ≤ s.up ∧
                  (s.lo ≤ s.y → s.y ≤ s.up → 1 ≤ s.k + s.explored.toNat → 
                    s.up - s.lo ≤ 2 * baselineRadius T (s.k + s.explored.toNat)) ∧
                  s.k < baselineInnerLen T (s.y - s.x) ∧ s.k ≤ n ∧ Real.log (T:ℝ) ≤ T * (s.b - s.a)^2 ∧
                  R ≤ 1400 * Real.log (T:ℝ) / (s.b - s.a) + (s.b - s.a) * (s.k + (s.k + s.explored.toNat : ℕ))
                    + 6 * Real.sqrt ((s.k + s.explored.toNat : ℕ) * Real.log (T:ℝ)))) →
                ∀ (s : AlgState) (R : ℝ) (n : ℕ) (c : Option (Fin N)), n + 1 ≤ T → Inv s R n →
                  (s.exploreNow → |(s.rho + choiceRev r c) / ((s.k + 1 : ℕ) : ℝ) - Fn s.y| ≤ baselineRadius T (s.k+1)) →
                  (∀ g : ℝ, (s.exploreNow → g = Rs - Fn s.y) → (¬ s.exploreNow → g = Rs - Fn s.a) →
                  Inv (baselineStep r T s c) (R + g) (n+1)) := by
              intro N r T hT Fn Rs hF0 hFR hR1 hFge Inv hInv s R n c hn hs hgood g hg1 hg2
              obtain ⟨hL, hLT⟩ := logT T hT
              rw [hInv] at hs
              obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ := hs
              have hl0 : 0 < s.b - s.a := by rw [i1]; positivity
              have hl1 : s.b - s.a ≤ 1 := by rw [i1]; exact pow_le_one₀ (by norm_num) (by norm_num)
              have hyx : s.y - s.x = (s.b - s.a) / 3 := by unfold AlgState.x AlgState.y; ring
              have hya : s.y = s.a + 2 * (s.b - s.a) / 3 := by unfold AlgState.y; ring
              have hxa : s.x = s.a + (s.b - s.a) / 3 := by unfold AlgState.x; ring
              rw [hyx] at i7
              by_cases he : s.exploreNow
              · -- explore
                have hstep : baselineStep r T s c = (⟨s.tau, s.a, s.b, s.k, s.rho + choiceRev r c,
                    (s.rho + choiceRev r c) / ((s.k + 1 : ℕ) : ℝ) - baselineRadius T (s.k+1),
                    (s.rho + choiceRev r c) / ((s.k + 1 : ℕ) : ℝ) + baselineRadius T (s.k+1), true⟩ : AlgState) := by
                  unfold baselineStep
                  rw [if_pos he]
                rw [hstep, hInv]
                have hG := abs_le.mp (hgood he)
                obtain ⟨he1, he2, he3⟩ := he
                have hge := hg1 ⟨he1, he2, he3⟩
                simp only [he1, Bool.toNat_false, add_zero] at i6 i10
                have hgb : g ≤ (s.b - s.a) + 6 * (Real.sqrt ((s.k+1 : ℕ) * Real.log (T:ℝ)) - Real.sqrt (s.k * Real.log (T:ℝ))) := by
                  refine sqrtInc _ hL s.k g _ hl0.le ?_ ?_
                  · have := hF0 s.y; linarith only [this, hge, hR1]
                  · intro hk
                    rw [← radFacts T s.k]
                    have := i6 he2 he3 hk
                    by_cases hyR : s.y ≤ Rs
                    · refine le_trans ?_ (le_max_left _ _)
                      have := hFge _ hyR
                      linarith only [this, hge, hya, hl0, i3]
                    · refine le_trans ?_ (le_max_right _ _)
                      linarith only [this, hge, he3, i4, not_le.mp hyR]
                refine ⟨i1, i2, i3, ?_, ?_, ?_, ?_, ?_, i9, ?_⟩
                · show _ - _ ≤ Fn s.y
                  linarith only [hG.2]
                · show Fn s.y ≤ _
                  linarith only [hG.1]
                · intro _ _ _
                  simp only [Bool.toNat_true]
                  exact le_of_eq (by ring)
                · show s.k < baselineInnerLen T (s.y - s.x)
                  rw [hyx]; exact i7
                · show s.k ≤ n + 1
                  omega
                · simp only [Bool.toNat_true]
                  have hc1 : (((s.k+1 : ℕ)) : ℝ) = (s.k:ℝ) + 1 := Nat.cast_add_one _
                  have hexp1 : (s.b - s.a) * ((s.k:ℝ) + ((s.k+1 : ℕ) : ℝ)) = (s.b - s.a) * ((s.k:ℝ) + (s.k:ℝ)) + (s.b - s.a) := by
                    rw [hc1]; ring
                  linarith only [i10, hgb, hexp1]
              · have hge := hg2 he
                have hgl : g ≤ s.b - s.a := by
                  have := hFge _ i2
                  linarith only [this, hge, i3]
                have hm : s.k + s.explored.toNat ≤ s.k + 1 := by
                  have := Bool.toNat_le s.explored
                  omega
                by_cases hroll : baselineInnerLen T (s.y - s.x) ≤ s.k + 1
                · rw [hyx] at hroll
                  have hkn : s.k + 1 = baselineInnerLen T ((s.b - s.a)/3) := by omega
                  have hstep : baselineStep r T s c = (if s.up < s.y then epochStart (s.tau + 1) s.a s.y
                     else epochStart (s.tau + 1) s.x s.b) := by
                    unfold baselineStep
                    rw [if_neg he, hyx, if_pos hroll]
                  have hR' := epochArith T hT _ hl0 hl1 R g s.k _ hkn hm hgl i10
                  obtain ⟨q1, q2, q3⟩ := innerFacts T hT _ hl0 hl1
                  have hlT : Real.log (T:ℝ) ≤ T * (2/3*(s.b - s.a))^2 := by
                    have : ((baselineInnerLen T ((s.b - s.a)/3) : ℕ) : ℝ) ≤ T := by
                      rw [← hkn]; exact_mod_cast (by omega : s.k + 1 ≤ T)
                    have hp : 0 < (s.b - s.a)^2 := by positivity
                    have h3 : 144 * Real.log (T:ℝ) ≤ T * (s.b - s.a)^2 := le_trans q2 (mul_le_mul_of_nonneg_right this hp.le)
                    have h4 : (T:ℝ) * (2/3*(s.b - s.a))^2 = 4/9 * (T * (s.b - s.a)^2) := by ring
                    linarith only [h3, h4, hL]
                  have hgen : ∀ a b : ℝ, b - a = 2/3 * (s.b - s.a) → a ≤ Rs → Rs ≤ b → Inv (epochStart (s.tau + 1) a b) (R + g) (n+1) := by
                    intro a b hab ha hb
                    rw [hInv]
                    unfold epochStart
                    simp only [AlgState.x, AlgState.y, Bool.toNat_false]
                    have e1 : (1/3 * a + 2/3 * b) - (2/3*a + 1/3 * b) = (2/3 * (s.b - s.a))/3 := by rw [← hab]; ring
                    rw [e1, hab]
                    refine ⟨?_, ha, hb, hF0 _, (hFR _).trans hR1, ?_, ?_, ?_, hlT, ?_⟩
                    · rw [i1]; ring
                    · intro _ _ h; omega
                    · exact (innerFacts T hT _ (by positivity) (by linarith only [hl0, hl1])).2.2
                    · omega
                    · simpa using hR'
                  rw [hstep]
                  split_ifs with hup
                  · refine hgen _ _ ?_ i2 ?_
                    · rw [hya]; ring
                    · by_contra hc
                      push Not at hc
                      have := hFge s.y hc.le
                      linarith only [this, hup, i5]
                  · refine hgen _ _ ?_ ?_ i3
                    · rw [hxa]; ring
                    · by_contra hc
                      push Not at hc hup
                      have hFy := hFR s.y
                      have hlo : s.lo ≤ s.y := by linarith only [i4, hFy, hc, hxa, hya, hl0]
                      have hexp : s.explored = true := by
                        by_contra hne
                        exact he ⟨by simpa using hne, hlo, hup⟩
                      have h6 := i6 hlo hup (by rw [hexp]; simp)
                      rw [hexp, Bool.toNat_true, hkn, radFacts] at h6
                      have h7 : Real.sqrt (Real.log (T:ℝ) / (baselineInnerLen T ((s.b - s.a)/3) : ℕ)) ≤ (s.b - s.a) / 12 := by
                        have hnpos : (0:ℝ) < (baselineInnerLen T ((s.b - s.a)/3) : ℕ) := by exact_mod_cast q3
                        rw [Real.sqrt_le_left (by positivity), div_le_iff₀ hnpos]
                        have h8 : ((s.b - s.a)/12)^2 * (baselineInnerLen T ((s.b - s.a)/3) : ℕ) = ((baselineInnerLen T ((s.b - s.a)/3) : ℕ) * (s.b - s.a)^2) / 144 := by ring
                        linarith only [q2, h8]
                      linarith only [h6, h7, hup, i4, hFy, hc, hxa, hya, hl0]
                · have hstep : baselineStep r T s c = { s with k := s.k + 1, explored := false } := by
                    unfold baselineStep
                    rw [if_neg he, if_neg hroll]
                  rw [hstep, hInv]
                  refine ⟨i1, i2, i3, i4, i5, ?_, ?_, ?_, i9, ?_⟩
                  · intro h1 h2 h3
                    have h1' : s.lo ≤ s.y := h1
                    have h2' : s.y ≤ s.up := h2
                    have hexp : s.explored = true := by
                      by_contra hne
                      exact he ⟨by simpa using hne, h1', h2'⟩
                    have h6 := i6 h1' h2' (by rw [hexp]; simp)
                    rw [hexp] at h6
                    simpa using h6
                  · show s.k + 1 < baselineInnerLen T (s.y - s.x)
                    omega
                  · show s.k + 1 ≤ n + 1
                    omega
                  · simp only [Bool.toNat_false, add_zero]
                    have hmr : ((s.k + s.explored.toNat : ℕ) : ℝ) ≤ ((s.k + 1 : ℕ) : ℝ) := by exact_mod_cast hm
                    have hsq : Real.sqrt (((s.k + s.explored.toNat : ℕ) : ℝ) * Real.log (T:ℝ)) ≤ Real.sqrt (((s.k + 1 : ℕ) : ℝ) * Real.log (T:ℝ)) := by
                      apply Real.sqrt_le_sqrt
                      exact mul_le_mul_of_nonneg_right hmr (by linarith only [hL])
                    have : (s.b - s.a) * (((s.k:ℕ):ℝ) + ((s.k + s.explored.toNat : ℕ) : ℝ)) + (s.b - s.a) ≤ (s.b - s.a) * (((s.k+1:ℕ):ℝ) + ((s.k + 1 : ℕ) : ℝ)) := by
                      have : ((s.k+1:ℕ):ℝ) = (s.k:ℝ) + 1 := by push_cast; ring
                      rw [this] at hmr ⊢
                      have hm2 := mul_le_mul_of_nonneg_left hmr hl0.le
                      linarith only [hm2]
                    linarith only [this, hsq, i10, hgl]
            have potStep : ∀ (N : ℕ) (v r : Fin N → ℝ), (∀ i, 0 ≤ v i) → (∀ i, r i ∈ Set.Icc (0:ℝ) 1) → ∀ (T : ℕ), 2 ≤ T → 
                ∀ E : ℕ → ℝ → ℕ → ℝ, (∀ j x m, E j x m = Real.exp (4 * Real.sqrt (Real.log (T:ℝ) / j) * x - m * (2 * (Real.log (T:ℝ) / j)))) →
                ∀ Sg : ℝ → ℕ → ℝ, (∀ x m, Sg x m = ∑ j ∈ Finset.Ioc m T, (E j x m + E j (-x) m)) →
                ∀ V : AlgState → ℝ, (∀ s, V s = ((4 * Real.log (T:ℝ) - s.tau) * (2 * T) + 
                    (if s.lo ≤ s.y ∧ s.y ≤ s.up then Sg (s.rho - (s.k + s.explored.toNat : ℕ) * F v r s.y) (s.k + s.explored.toNat) else 0)) / (T:ℝ)^2) →
                ∀ G : AlgState → Option (Fin N) → Prop, (∀ s c, G s c ↔ 
                  (s.exploreNow → |(s.rho + choiceRev r c) / ((s.k + 1 : ℕ) : ℝ) - F v r s.y| ≤ baselineRadius T (s.k+1))) →
                ∀ s : AlgState, (s.tau : ℝ) ≤ 4 * Real.log (T:ℝ) → s.k + 1 ≤ T → 
                 ∀ U : Option (Fin N) → ℝ, (∀ c, G s c → U c ≤ V (baselineStep r T s c)) → (∀ c, ¬ G s c → U c ≤ 1) →
                  ∑ c, MNLBandit.UCB.choiceProb v (offerOf r s) c * U c ≤ V s := by
              intro N v r hv hr T hT E hE Sg hSg V hV G hG s htau hkT U hU1 hU2
              obtain ⟨hL, hLT⟩ := logT T hT
              have hTpos : (0:ℝ) < T := by exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.two_pos hT)
              have hT2 : (0:ℝ) < (T:ℝ)^2 := by positivity
              set L := Real.log (T:ℝ) with hLd
              obtain ⟨hp0, hp1, hp2⟩ := choiceFacts N v r hv (offerOf r s)
              have hEpos : ∀ j x m, 0 < E j x m := fun j x m => by rw [hE]; exact Real.exp_pos _
              have hSgnn : ∀ x m, 0 ≤ Sg x m := fun x m => by
                rw [hSg]
                exact Finset.sum_nonneg (fun j _ => (add_pos (hEpos _ _ _) (hEpos _ _ _)).le)
              by_cases he : s.exploreNow
              · have hstep : ∀ c, baselineStep r T s c = (⟨s.tau, s.a, s.b, s.k, s.rho + choiceRev r c,
                    (s.rho + choiceRev r c) / ((s.k + 1 : ℕ) : ℝ) - baselineRadius T (s.k+1),
                    (s.rho + choiceRev r c) / ((s.k + 1 : ℕ) : ℝ) + baselineRadius T (s.k+1), true⟩ : AlgState) := by
                  intro c
                  unfold baselineStep
                  rw [if_pos he]
                have hoff : offerOf r s = levelSet r s.y := by
                  unfold offerOf
                  rw [if_pos he]
                obtain ⟨he1, he2, he3⟩ := id he
                set f := F v r s.y with hf
                rw [hoff] at hp2
                have hp2' : ∑ c, MNLBandit.UCB.choiceProb v (offerOf r s) c * choiceRev r c = f := by
                  rw [hoff]; exact hp2
                set A := (4 * L - s.tau) * (2 * T) with hA
                have hA0 : 0 ≤ A := mul_nonneg (by linarith only [htau]) (by positivity)
                set x := s.rho - (s.k:ℝ) * f with hx
                have hVs : V s = (A + Sg x s.k) / (T:ℝ)^2 := by
                  rw [hV, if_pos ⟨he2, he3⟩, he1]
                  simp [hx, hA, hf]
                set Z : Option (Fin N) → ℝ := fun c => ∑ j ∈ Finset.Ioc s.k T, 
                  (E j (x + (choiceRev r c - f)) (s.k+1) + E j (-(x + (choiceRev r c - f))) (s.k+1)) with hZ
                have hxc : ∀ c, s.rho + choiceRev r c - ((s.k + 1 : ℕ) : ℝ) * f = x + (choiceRev r c - f) := by
                  intro c; rw [hx]; push_cast; ring
                have hSZ : ∀ c, Sg (x + (choiceRev r c - f)) (s.k+1) ≤ Z c := by
                  intro c
                  rw [hSg]
                  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => (add_pos (hEpos _ _ _) (hEpos _ _ _)).le)
                  exact Finset.Ioc_subset_Ioc_left (by omega)
                have hUb : ∀ c, U c ≤ (A + Z c) / (T:ℝ)^2 := by
                  intro c
                  by_cases hc : G s c
                  · refine (hU1 c hc).trans ?_
                    rw [hstep, hV]
                    apply div_le_div_of_nonneg_right _ hT2.le
                    refine add_le_add le_rfl ?_
                    split_ifs
                    · simp only [Bool.toNat_true]
                      show Sg (s.rho + choiceRev r c - ((s.k + 1 : ℕ) : ℝ) * f) (s.k+1) ≤ Z c
                      rw [hxc]
                      exact hSZ c
                    · exact (hSgnn _ _).trans (hSZ c)
                  · refine (hU2 c hc).trans ?_
                    rw [one_le_div hT2]
                    have hbad : baselineRadius T (s.k+1) < |(s.rho + choiceRev r c) / ((s.k + 1 : ℕ) : ℝ) - f| := by
                      by_contra hcon
                      exact hc ((hG s c).mpr (fun _ => not_lt.mp hcon))
                    rw [radFacts] at hbad
                    set q := Real.sqrt (L / ((s.k+1 : ℕ):ℝ)) with hq
                    have hj : (0:ℝ) < ((s.k+1 : ℕ):ℝ) := by positivity
                    have hq2 : q ^ 2 = L / ((s.k+1 : ℕ):ℝ) := Real.sq_sqrt (by positivity)
                    have hq2' : ((s.k+1 : ℕ):ℝ) * q ^ 2 = L := by rw [hq2]; field_simp
                    have hq0 : 0 ≤ q := Real.sqrt_nonneg _
                    have hxeq : x + (choiceRev r c - f) = ((s.k+1 : ℕ):ℝ) * ((s.rho + choiceRev r c) / ((s.k + 1 : ℕ) : ℝ) - f) := by
                      rw [← hxc]; field_simp
                    have hT2e : (T:ℝ)^2 = Real.exp (2 * L) := by
                      rw [two_mul, Real.exp_add, Real.exp_log hTpos]; ring
                    have hbig : ∀ u : ℝ, ((s.k+1 : ℕ):ℝ) * q ≤ u → (T:ℝ)^2 ≤ E (s.k+1) u (s.k+1) := by
                      intro u hu
                      rw [hE, hT2e, ← hq, ← hq2]
                      apply Real.exp_le_exp.mpr
                      have : q * (((s.k+1 : ℕ):ℝ) * q) ≤ q * u := mul_le_mul_of_nonneg_left hu hq0
                      have h9 : ((s.k+1 : ℕ):ℝ) * (2 * q^2) = 2 * L := by rw [← hq2']; ring
                      rw [h9]
                      linarith only [this, hq2']
                    have hmem : s.k + 1 ∈ Finset.Ioc s.k T := Finset.mem_Ioc.mpr ⟨by omega, hkT⟩
                    have hterm : E (s.k+1) (x + (choiceRev r c - f)) (s.k+1) + E (s.k+1) (-(x + (choiceRev r c - f))) (s.k+1) ≤ Z c :=
                      Finset.single_le_sum (f := fun j => E j (x + (choiceRev r c - f)) (s.k+1) + E j (-(x + (choiceRev r c - f))) (s.k+1))
                        (fun j _ => (add_pos (hEpos _ _ _) (hEpos _ _ _)).le) hmem
                    have e1 := hEpos (s.k+1) (x + (choiceRev r c - f)) (s.k+1)
                    have e2 := hEpos (s.k+1) (-(x + (choiceRev r c - f))) (s.k+1)
                    rcases lt_abs.mp hbad with hb | hb
                    · have := hbig (x + (choiceRev r c - f)) (by rw [hxeq]; exact mul_le_mul_of_nonneg_left hb.le hj.le)
                      linarith only [this, hterm, hA0, e1, e2]
                    · have := hbig (-(x + (choiceRev r c - f))) (by 
                        rw [hxeq, ← mul_neg]; exact mul_le_mul_of_nonneg_left hb.le hj.le)
                      linarith only [this, hterm, hA0, e1, e2]
                have hX : ∀ c, choiceRev r c ∈ Set.Icc (0:ℝ) 1 := by
                  intro c
                  cases c with
                  | none => simp [choiceRev]
                  | some i => exact hr i
                have hone : ∀ (j : ℕ) (σ : ℝ), σ ^ 2 = 1 → ∑ c, MNLBandit.UCB.choiceProb v (offerOf r s) c * E j (σ * (x + (choiceRev r c - f))) (s.k+1) ≤ E j (σ * x) s.k := by
                  intro j σ hσ
                  have hh := hoeff N _ _ f (σ * (4 * Real.sqrt (L / j))) hp0 hp1 hX hp2'
                  have hsq : (σ * (4 * Real.sqrt (L / j))) ^ 2 / 8 = 2 * (L / j) := by
                    rw [mul_pow, mul_pow, hσ, Real.sq_sqrt (by positivity)]; ring
                  rw [hsq] at hh
                  have hfac : ∀ c, E j (σ * (x + (choiceRev r c - f))) (s.k+1) = 
                      E j (σ * x) s.k * Real.exp (-(2 * (L / j))) * Real.exp (σ * (4 * Real.sqrt (L / j)) * (choiceRev r c - f)) := by
                    intro c
                    rw [hE, hE, ← Real.exp_add, ← Real.exp_add]
                    congr 1
                    push_cast
                    ring
                  calc _ = E j (σ * x) s.k * Real.exp (-(2 * (L / j))) * ∑ c, MNLBandit.UCB.choiceProb v (offerOf r s) c * Real.exp (σ * (4 * Real.sqrt (L / j)) * (choiceRev r c - f)) := by
                        rw [Finset.mul_sum]
                        refine Finset.sum_congr rfl (fun c _ => ?_)
                        rw [hfac]; ring
                    _ ≤ E j (σ * x) s.k * Real.exp (-(2 * (L / j))) * Real.exp (2 * (L / j)) :=
                        mul_le_mul_of_nonneg_left hh (mul_pos (hEpos _ _ _) (Real.exp_pos _)).le
                    _ = E j (σ * x) s.k := by
                        rw [mul_assoc, ← Real.exp_add]; simp
                have hZsum : ∑ c, MNLBandit.UCB.choiceProb v (offerOf r s) c * Z c ≤ Sg x s.k := by
                  rw [hSg]
                  simp only [hZ, Finset.mul_sum]
                  rw [Finset.sum_comm]
                  refine Finset.sum_le_sum (fun j _ => ?_)
                  have h1 := hone j 1 (by norm_num)
                  have h2 := hone j (-1) (by norm_num)
                  simp only [one_mul, neg_one_mul] at h1 h2
                  rw [Finset.sum_congr rfl (fun c _ => mul_add _ _ _), Finset.sum_add_distrib]
                  linarith only [h1, h2]
                calc ∑ c, MNLBandit.UCB.choiceProb v (offerOf r s) c * U c 
                    ≤ ∑ c, MNLBandit.UCB.choiceProb v (offerOf r s) c * ((A + Z c) / (T:ℝ)^2) :=
                      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (hUb c) (hp0 c))
                  _ = (A * ∑ c, MNLBandit.UCB.choiceProb v (offerOf r s) c + ∑ c, MNLBandit.UCB.choiceProb v (offerOf r s) c * Z c) / (T:ℝ)^2 := by
                      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
                      exact Finset.sum_congr rfl (fun c _ => by ring)
                  _ ≤ (A + Sg x s.k) / (T:ℝ)^2 := by
                      rw [hp1, mul_one]
                      exact div_le_div_of_nonneg_right (by linarith only [hZsum]) hT2.le
                  _ = V s := hVs.symm
              · have hGall : ∀ c, G s c := fun c => (hG s c).mpr (fun h => absurd h he)
                have hVle : ∀ c, V (baselineStep r T s c) ≤ V s := by
                  intro c
                  by_cases hroll : baselineInnerLen T (s.y - s.x) ≤ s.k + 1
                  · have hgen : ∀ a b : ℝ, V (epochStart (s.tau + 1) a b) ≤ V s := by
                      intro a b
                      rw [hV, hV]
                      apply div_le_div_of_nonneg_right _ hT2.le
                      have hS0 : Sg 0 0 = 2 * T := by
                        rw [hSg]
                        have : ∀ j ∈ Finset.Ioc 0 T, E j 0 0 + E j (-0) 0 = 2 := by
                          intro j _
                          rw [hE, hE]; norm_num
                        rw [Finset.sum_congr rfl this]
                        simp; ring
                      have h1 : (if (epochStart (s.tau+1) a b).lo ≤ (epochStart (s.tau+1) a b).y ∧ (epochStart (s.tau+1) a b).y ≤ (epochStart (s.tau+1) a b).up then 
                          Sg ((epochStart (s.tau+1) a b).rho - ((epochStart (s.tau+1) a b).k + (epochStart (s.tau+1) a b).explored.toNat : ℕ) * F v r (epochStart (s.tau+1) a b).y) ((epochStart (s.tau+1) a b).k + (epochStart (s.tau+1) a b).explored.toNat) else 0) ≤ 2 * T := by
                        split_ifs
                        · simp only [epochStart, Bool.toNat_false]
                          simp [hS0]
                        · positivity
                      have h2 : (0:ℝ) ≤ (if s.lo ≤ s.y ∧ s.y ≤ s.up then Sg (s.rho - (s.k + s.explored.toNat : ℕ) * F v r s.y) (s.k + s.explored.toNat) else 0) := by
                        split_ifs
                        · exact hSgnn _ _
                        · exact le_rfl
                      have h3 : (((epochStart (s.tau+1) a b).tau : ℕ) : ℝ) = s.tau + 1 := by
                        simp [epochStart]
                      rw [h3]
                      linarith only [h1, h2]
                    have hstep : baselineStep r T s c = (if s.up < s.y then epochStart (s.tau + 1) s.a s.y
                     else epochStart (s.tau + 1) s.x s.b) := by
                      unfold baselineStep
                      rw [if_neg he, if_pos hroll]
                    rw [hstep]
                    split_ifs
                    · exact hgen _ _
                    · exact hgen _ _
                  · have hstep : baselineStep r T s c = { s with k := s.k + 1, explored := false } := by
                      unfold baselineStep
                      rw [if_neg he, if_neg hroll]
                    rw [hstep, hV, hV]
                    apply div_le_div_of_nonneg_right _ hT2.le
                    refine add_le_add le_rfl ?_
                    show (if s.lo ≤ s.y ∧ s.y ≤ s.up then Sg (s.rho - ((s.k + 1) + false.toNat : ℕ) * F v r s.y) ((s.k + 1) + false.toNat) else 0) ≤ _
                    by_cases hact : s.lo ≤ s.y ∧ s.y ≤ s.up
                    · have hexp : s.explored = true := by
                        by_contra hne
                        exact he ⟨by simpa using hne, hact.1, hact.2⟩
                      rw [if_pos hact, if_pos hact, hexp]
                      simp
                    · rw [if_neg hact, if_neg hact]
                calc ∑ c, MNLBandit.UCB.choiceProb v (offerOf r s) c * U c 
                    ≤ ∑ c, MNLBandit.UCB.choiceProb v (offerOf r s) c * V s :=
                      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left ((hU1 c (hGall c)).trans (hVle c)) (hp0 c))
                  _ = V s := by rw [← Finset.sum_mul, hp1, one_mul]
            refine ⟨1520, by norm_num, ?_⟩
            intro N T hT v r hv hr
            obtain ⟨hL, hLT⟩ := logT T hT
            have hTpos : (0:ℝ) < T := by exact_mod_cast (by omega : 0 < T)
            have hT2r : (2:ℝ) ≤ T := by exact_mod_cast hT
            have hT2 : (0:ℝ) < (T:ℝ)^2 := by positivity
            obtain ⟨hrev0, hrevle, hopt1, hFge⟩ := revFacts N v r hv hr
            obtain ⟨E, hE⟩ : ∃ E : ℕ → ℝ → ℕ → ℝ, (∀ j x m, E j x m = Real.exp (4 * Real.sqrt (Real.log (T:ℝ) / j) * x - m * (2 * (Real.log (T:ℝ) / j)))) := ⟨_, fun _ _ _ => rfl⟩
            obtain ⟨Sg, hSg⟩ : ∃ Sg : ℝ → ℕ → ℝ, (∀ x m, Sg x m = ∑ j ∈ Finset.Ioc m T, (E j x m + E j (-x) m)) := ⟨_, fun _ _ => rfl⟩
            obtain ⟨V, hV⟩ : ∃ V : AlgState → ℝ, (∀ s, V s = ((4 * Real.log (T:ℝ) - s.tau) * (2 * T) + 
                  (if s.lo ≤ s.y ∧ s.y ≤ s.up then Sg (s.rho - (s.k + s.explored.toNat : ℕ) * F v r s.y) (s.k + s.explored.toNat) else 0)) / (T:ℝ)^2) := ⟨_, fun _ => rfl⟩
            obtain ⟨G, hG⟩ : ∃ G : AlgState → Option (Fin N) → Prop, (∀ s c, G s c ↔ 
                (s.exploreNow → |(s.rho + choiceRev r c) / ((s.k + 1 : ℕ) : ℝ) - F v r s.y| ≤ baselineRadius T (s.k+1))) := ⟨_, fun _ _ => Iff.rfl⟩
            obtain ⟨Rs, hRs⟩ : ∃ Rs : ℝ, Rs = optRev v r := ⟨_, rfl⟩
            rw [← hRs] at hopt1
            obtain ⟨Inv, hInv⟩ : ∃ Inv : AlgState → ℝ → ℕ → Prop, 
              (∀ s R n, Inv s R n ↔ (s.b - s.a = (2/3:ℝ)^s.tau ∧ s.a ≤ Rs ∧ Rs ≤ s.b ∧ s.lo ≤ F v r s.y ∧ F v r s.y ≤ s.up ∧
                (s.lo ≤ s.y → s.y ≤ s.up → 1 ≤ s.k + s.explored.toNat → 
                  s.up - s.lo ≤ 2 * baselineRadius T (s.k + s.explored.toNat)) ∧
                s.k < baselineInnerLen T (s.y - s.x) ∧ s.k ≤ n ∧ Real.log (T:ℝ) ≤ T * (s.b - s.a)^2 ∧
                R ≤ 1400 * Real.log (T:ℝ) / (s.b - s.a) + (s.b - s.a) * (s.k + (s.k + s.explored.toNat : ℕ))
                  + 6 * Real.sqrt ((s.k + s.explored.toNat : ℕ) * Real.log (T:ℝ)))) := ⟨_, fun _ _ _ => Iff.rfl⟩
            have hdet := detStep N r T hT (F v r) Rs (fun θ => hrev0 _) (fun θ => by rw [hRs]; exact hrevle _) hopt1
              (fun θ hθ => hFge θ (by rw [← hRs]; exact hθ)) Inv hInv
            have hpot := potStep N v r hv hr T hT E hE Sg hSg V hV G hG
            obtain ⟨st, hst⟩ : ∃ st : List (Option (Fin N)) → AlgState, ∀ l, st l = l.foldl (baselineStep r T) initState := ⟨_, fun _ => rfl⟩
            have hst0 : st [] = initState := by rw [hst]; rfl
            have hst1 : ∀ l c, st (l ++ [c]) = baselineStep r T (st l) c := by
              intro l c; rw [hst, hst, List.foldl_append]; rfl
            obtain ⟨g, hg⟩ : ∃ g : AlgState → ℝ, ∀ s, g s = Rs - rev v r (offerOf r s) := ⟨_, fun _ => rfl⟩
            have hg1 : ∀ s : AlgState, s.exploreNow → g s = Rs - F v r s.y := by
              intro s hs; rw [hg]; unfold offerOf; rw [if_pos hs]; rfl
            have hg2 : ∀ s : AlgState, ¬ s.exploreNow → g s = Rs - F v r s.a := by
              intro s hs; rw [hg]; unfold offerOf; rw [if_neg hs]; rfl
            obtain ⟨Q, hQ⟩ : ∃ Q : List (Option (Fin N)) → Prop, ∀ l, Q l ↔ ∀ l' c, l' ++ [c] <+: l → G (st l') c := ⟨_, fun _ => Iff.rfl⟩
            have hQ0 : Q [] := by
              rw [hQ]; intro l' c h
              simp at h
            have hQ1 : ∀ l c, Q (l ++ [c]) ↔ Q l ∧ G (st l) c := by
              intro l c
              constructor
              · intro h
                rw [hQ] at h
                refine ⟨?_, h l c (List.prefix_refl _)⟩
                rw [hQ]
                exact fun l' c' h' => h l' c' (h'.trans (List.prefix_append _ _))
              · rintro ⟨h1, h2⟩
                rw [hQ] at h1 ⊢
                intro l' c' h'
                rcases List.prefix_concat_iff.mp h' with h3 | h3
                · obtain ⟨h4, h5⟩ := List.append_inj' h3 rfl
                  simp at h5
                  rw [h4, h5]; exact h2
                · exact h1 l' c' h3
            obtain ⟨Rg, hRg⟩ : ∃ Rg : List (Option (Fin N)) → ℝ, ∀ l, Rg l = ∑ i ∈ Finset.range l.length, g (st (l.take i)) := ⟨_, fun _ => rfl⟩
            have hRg0 : Rg [] = 0 := by rw [hRg]; simp
            have hRg1 : ∀ l c, Rg (l ++ [c]) = Rg l + g (st l) := by
              intro l c
              rw [hRg, hRg, List.length_append, List.length_singleton, Finset.sum_range_succ]
              congr 1
              · refine Finset.sum_congr rfl (fun i hi => ?_)
                rw [List.take_append_of_le_length (Finset.mem_range.mp hi).le]
              · rw [List.take_left']; rfl
            have hinv0 : Inv initState 0 0 := by
              rw [hInv]
              unfold initState epochStart
              simp only [AlgState.x, AlgState.y, Bool.toNat_false]
              refine ⟨by norm_num, by rw [hRs]; exact (hrev0 ∅).trans (hrevle ∅), hopt1, hrev0 _, ?_, ?_, ?_, le_rfl, by norm_num; exact hLT, ?_⟩
              · exact (hrevle _).trans (by rw [← hRs]; exact hopt1)
              · intro _ _ h; omega
              · have := (innerFacts T hT 1 (by norm_num) le_rfl).2.2
                norm_num at this ⊢
                exact this
              · norm_num
                linarith
            have hinv : ∀ l : List (Option (Fin N)), l.length ≤ T → Q l → Inv (st l) (Rg l) l.length := by
              intro l
              induction l using List.reverseRecOn with
              | nil => intro _ _; rw [hst0, hRg0]; exact hinv0
              | append_singleton l c ih =>
                intro hlen hq
                rw [List.length_append, List.length_singleton] at hlen ⊢
                obtain ⟨q1, q2⟩ := (hQ1 l c).mp hq
                rw [hst1, hRg1]
                exact hdet (st l) (Rg l) l.length c hlen (ih (by omega) q1) ((hG _ _).mp q2) (g (st l)) (hg1 _) (hg2 _)
            have htau : ∀ l : List (Option (Fin N)), l.length ≤ T → Q l → ((st l).tau : ℝ) ≤ 4 * Real.log (T:ℝ) := by
              intro l hlen hq
              have h := (hInv _ _ _).mp (hinv l hlen hq)
              obtain ⟨i1, -, -, -, -, -, -, -, i9, -⟩ := h
              rw [i1] at i9
              set t := (st l).tau with ht
              have h1 : Real.exp ((t:ℝ)/2) ≤ (9/4:ℝ)^t := by
                have : Real.exp (1/2:ℝ) ≤ 9/4 := by
                  have h1 := Real.exp_one_lt_d9
                  have h2 : Real.exp (1/2:ℝ) ^ 2 = Real.exp 1 := by
                    rw [← Real.exp_nat_mul]; norm_num
                  have h3 := Real.exp_pos (1/2:ℝ)
                  nlinarith only [h1, h2, h3]
                calc Real.exp ((t:ℝ)/2) = Real.exp (1/2:ℝ) ^ t := by
                      rw [← Real.exp_nat_mul]; congr 1; ring
                  _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le this t
              have h2 : (9/4:ℝ)^t * ((2/3:ℝ)^t)^2 = 1 := by
                rw [← pow_mul, mul_comm t 2, pow_mul, ← mul_pow]; norm_num
              have h4 : (0:ℝ) < (9/4:ℝ)^t := by positivity
              have h3 : (9/4:ℝ)^t * Real.log (T:ℝ) ≤ T := by
                calc (9/4:ℝ)^t * Real.log (T:ℝ) ≤ (9/4:ℝ)^t * (T * ((2/3:ℝ)^t)^2) := mul_le_mul_of_nonneg_left i9 h4.le
                  _ = T * ((9/4:ℝ)^t * ((2/3:ℝ)^t)^2) := by ring
                  _ = T := by rw [h2, mul_one]
              have h5 : Real.exp ((t:ℝ)/2) ≤ Real.exp (2 * Real.log (T:ℝ)) := by
                have : Real.exp (2 * Real.log (T:ℝ)) = (T:ℝ)^2 := by
                  rw [two_mul, Real.exp_add, Real.exp_log hTpos]; ring
                rw [this]
                have h6 := mul_le_mul_of_nonneg_left hL.le h4.le
                have h7 : 2 * (T:ℝ) ≤ T^2 := by rw [pow_two]; exact mul_le_mul_of_nonneg_right hT2r hTpos.le
                linarith only [h1, h3, h6, h7, h4]
              have := Real.exp_le_exp.mp h5
              linarith only [this]
            have hSgnn : ∀ x m, 0 ≤ Sg x m := fun x m => by
              rw [hSg]
              refine Finset.sum_nonneg (fun j _ => ?_)
              rw [hE, hE]
              positivity
            have hVnn : ∀ l : List (Option (Fin N)), l.length ≤ T → Q l → 0 ≤ V (st l) := by
              intro l hlen hq
              rw [hV]
              refine div_nonneg (add_nonneg (mul_nonneg ?_ (by positivity)) ?_) hT2.le
              · linarith only [htau l hlen hq]
              · split_ifs
                · exact hSgnn _ _
                · exact le_rfl
            classical
            obtain ⟨W, hW⟩ : ∃ W : List (Option (Fin N)) → ℝ, ∀ l, W l = if Q l then V (st l) else 1 := ⟨_, fun _ => rfl⟩
            have hWexp := expect N v r hv T W (by
              intro l hl
              rw [← hst]
              by_cases hq : Q l
              · rw [hW l, if_pos hq]
                have hi := (hInv _ _ _).mp (hinv l hl.le hq)
                refine hpot (st l) (htau l hl.le hq) ?_ (fun c => W (l ++ [c])) ?_ ?_
                · have := hi.2.2.2.2.2.2.2.1
                  omega
                · intro c hc
                  show W (l ++ [c]) ≤ _
                  rw [hW, if_pos ((hQ1 l c).mpr ⟨hq, hc⟩), hst1]
                · intro c hc
                  show W (l ++ [c]) ≤ _
                  rw [hW, if_neg (fun h => hc ((hQ1 l c).mp h).2)]
              · rw [hW l, if_neg hq]
                have : ∀ c, W (l ++ [c]) = 1 := by
                  intro c
                  rw [hW, if_neg (fun h => hq ((hQ1 l c).mp h).1)]
                simp only [this, mul_one]
                exact (choiceFacts N v r hv _).2.1.le)
            have hone1 := expect N v r hv T (fun _ => 1) (by
              intro l hl
              simp only [mul_one]
              exact (choiceFacts N v r hv _).2.1.le)
            have hone2 := expect N v r hv T (fun _ => -1) (by
              intro l hl
              rw [← Finset.sum_mul, (choiceFacts N v r hv _).2.1]; norm_num)
            simp only [mul_one, mul_neg, Finset.sum_neg_distrib] at hone1 hone2
            have hone : ∑ h : MNLBandit.UCB.History N T, MNLBandit.UCB.histProb v (baselinePolicy r T) h = 1 := by linarith only [hone1, hone2]
            have hnn : ∀ (h : MNLBandit.UCB.History N T), 0 ≤ MNLBandit.UCB.histProb v (baselinePolicy r T) h := by
              intro h
              exact Finset.prod_nonneg (fun t _ => (choiceFacts N v r hv _).1 _)
            have hW0 : W [] ≤ 11 * Real.log (T:ℝ) / T := by
              rw [hW, if_pos hQ0, hst0, hV]
              have hS0 : Sg 0 0 = 2 * T := by
                rw [hSg]
                have : ∀ j ∈ Finset.Ioc 0 T, E j 0 0 + E j (-0) 0 = 2 := by
                  intro j _
                  rw [hE, hE]; norm_num
                rw [Finset.sum_congr rfl this]
                simp; ring
              have h1 : (if initState.lo ≤ initState.y ∧ initState.y ≤ initState.up then Sg (initState.rho - (initState.k + initState.explored.toNat : ℕ) * F v r initState.y) (initState.k + initState.explored.toNat) else 0) ≤ 2 * T := by
                split_ifs
                · simp [initState, epochStart, hS0]
                · positivity
              have h2 : ((initState.tau : ℕ) : ℝ) = 0 := by simp [initState, epochStart]
              rw [h2, div_le_div_iff₀ hT2 hTpos]
              have h3 : (4 * Real.log (T:ℝ) - 0) * (2 * T) + (if initState.lo ≤ initState.y ∧ initState.y ≤ initState.up then Sg (initState.rho - (initState.k + initState.explored.toNat : ℕ) * F v r initState.y) (initState.k + initState.explored.toNat) else 0) ≤ 11 * Real.log (T:ℝ) * T := by
                have := mul_le_mul_of_nonneg_right hL.le hTpos.le
                linarith only [h1, this, hTpos]
              calc _ ≤ 11 * Real.log (T:ℝ) * T * T := mul_le_mul_of_nonneg_right h3 hTpos.le
                _ = _ := by ring
            have hD0 : 0 ≤ Real.sqrt (T * Real.log (T:ℝ)) := Real.sqrt_nonneg _
            have hpath : ∀ h : MNLBandit.UCB.History N T, Rg (List.ofFn h) ≤ 1500 * Real.sqrt (T * Real.log (T:ℝ)) + T * W (List.ofFn h) := by
              intro h
              have hlen : (List.ofFn h).length = T := List.length_ofFn
              by_cases hq : Q (List.ofFn h)
              · have hi := (hInv _ _ _).mp (hinv _ hlen.le hq)
                have hVn := hVnn _ hlen.le hq
                rw [hW, if_pos hq]
                obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ := hi
                rw [hlen] at i8
                set s := st (List.ofFn h) with hs
                have hl0 : 0 < s.b - s.a := by rw [i1]; positivity
                have hl1 : s.b - s.a ≤ 1 := by rw [i1]; exact pow_le_one₀ (by norm_num) (by norm_num)
                have hyx : s.y - s.x = (s.b - s.a) / 3 := by unfold AlgState.x AlgState.y; ring
                rw [hyx] at i7
                have hm : s.k + s.explored.toNat ≤ s.k + 1 := by
                  have := Bool.toNat_le s.explored
                  omega
                have := finalArith T hT _ hl0 hl1 _ s.k _ i7 hm i8 i9 i10
                have h2 : 0 ≤ (T:ℝ) * V s := mul_nonneg hTpos.le hVn
                linarith only [this, h2]
              · rw [hW, if_neg hq, hRg, hlen]
                have : ∑ i ∈ Finset.range T, g (st ((List.ofFn h).take i)) ≤ ∑ i ∈ Finset.range T, (1:ℝ) := by
                  refine Finset.sum_le_sum (fun i _ => ?_)
                  rw [hg]
                  have := hrev0 (offerOf r (st ((List.ofFn h).take i)))
                  linarith only [this, hopt1]
                simp at this
                linarith only [this, hD0]
            have hreg : MNLBandit.UCB.regret v r Finset.univ ⟨∅, Finset.mem_univ _⟩ (baselinePolicy r T) T = 
                ∑ h : MNLBandit.UCB.History N T, MNLBandit.UCB.histProb v (baselinePolicy r T) h * Rg (List.ofFn h) := by
              unfold MNLBandit.UCB.regret MNLBandit.UCB.expectedRevenue
              have e1 : (T:ℝ) * MNLBandit.UCB.optRevenue v r Finset.univ ⟨∅, Finset.mem_univ _⟩ = 
                  ∑ h : MNLBandit.UCB.History N T, MNLBandit.UCB.histProb v (baselinePolicy r T) h * (T * Rs) := by
                rw [← Finset.sum_mul, hone, one_mul, hRs]; rfl
              rw [e1, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl (fun h _ => ?_)
              rw [← mul_sub]
              congr 1
              rw [hRg, List.length_ofFn, Finset.sum_range]
              have e2 : (T:ℝ) * Rs = ∑ t : Fin T, Rs := by simp
              rw [e2, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl (fun t _ => ?_)
              rw [hg]
              congr 1
              show _ = ChoiceCDLP.MNL.mnlObjective v r 1 _
              congr 1
              unfold MNLBandit.UCB.offered baselinePolicy baselineStateAt
              rw [← hst]
              congr 2
              apply List.ext_getElem
              · simp [t.isLt.le]
              · intro i h1 h2
                simp [MNLBandit.UCB.histPrefix]
            rw [hreg]
            have hlogs : Real.log (T:ℝ) ≤ Real.sqrt (T * Real.log (T:ℝ)) := by
              apply Real.le_sqrt_of_sq_le
              rw [pow_two]
              exact mul_le_mul_of_nonneg_right hLT (by linarith only [hL])
            calc ∑ h : MNLBandit.UCB.History N T, MNLBandit.UCB.histProb v (baselinePolicy r T) h * Rg (List.ofFn h)
                ≤ ∑ h : MNLBandit.UCB.History N T, MNLBandit.UCB.histProb v (baselinePolicy r T) h * (1500 * Real.sqrt (T * Real.log (T:ℝ)) + T * W (List.ofFn h)) :=
                  Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left (hpath h) (hnn h))
              _ = 1500 * Real.sqrt (T * Real.log (T:ℝ)) * (∑ h : MNLBandit.UCB.History N T, MNLBandit.UCB.histProb v (baselinePolicy r T) h) + T * ∑ h : MNLBandit.UCB.History N T, MNLBandit.UCB.histProb v (baselinePolicy r T) h * W (List.ofFn h) := by
                  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                  exact Finset.sum_congr rfl (fun h _ => by ring)
              _ ≤ 1500 * Real.sqrt (T * Real.log (T:ℝ)) + T * (11 * Real.log (T:ℝ) / T) := by
                  rw [hone, mul_one]
                  have := mul_le_mul_of_nonneg_left (hWexp.trans hW0) hTpos.le
                  linarith only [this]
              _ = 1500 * Real.sqrt (T * Real.log (T:ℝ)) + 11 * Real.log (T:ℝ) := by
                  field_simp
              _ ≤ 1520 * Real.sqrt (T * Real.log (T:ℝ)) := by linarith only [hlogs, hD0]
