-- Prove2me | solution 1 for MLRPCake.EnvyFree.Supplement.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:08:00.866258+00:00
-- url     : https://prove2.me/submissions/c6f7bf09-eb9a-4dc3-b559-b71429a78773

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_Divisions

open MLRPCake
open MLRPCake.EnvyFree
open MLRPCake.EnvyFree.Supplement

/-- Lemma 5, p. 15: under MLRP (agents in MLRP order), (1) every cake division is weakly
dominated, agent by agent, by some allocation (contiguous pieces, any assignment order), and
(2) for every Pareto optimal allocation there is an allocation giving every agent the same value
whose pieces are assigned left to right in the MLRP order. -/
theorem solution {n : ℕ} (f : Fin n → ℝ → ℝ) (hn : 1 ≤ n) (hf : IsInstance f) (hm : IsMLRP f) :
    (∀ D : Fin n → Set ℝ, IsCakeDivision D →
      ∃ (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)), IsAllocation (n := n) x ∧
        ∀ i, bundleVal f i (D i) ≤ pieceVal f x σ i) ∧
    (∀ (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)), IsAllocation (n := n) x →
      ParetoOptimal f (pieceVal f x σ) →
      ∃ x' : ℕ → ℝ, IsAllocation (n := n) x' ∧
        ∀ i : Fin n, val f i (x' i.val) (x' (i.val + 1)) = pieceVal f x σ i) := by
          classical
          have hdens : ∀ i : Fin n, dens f (i : ℕ) = f i := by
            intro i; funext t; simp [dens]
          have hdI : ∀ l, IntervalIntegrable (dens f l) MeasureTheory.volume 0 1 := by
            intro l; unfold dens; split_ifs with h
            · exact (hf ⟨l, h⟩).2.2.1
            · exact intervalIntegrable_const
          have hdIab : ∀ l (a b : ℝ), 0 ≤ a → a ≤ b → b ≤ 1 →
              IntervalIntegrable (dens f l) MeasureTheory.volume a b := by
            intro l a b ha hab hb
            exact (hdI l).mono_set (by
              rw [Set.uIcc_of_le hab, Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc ha hb)
          have hnn : ∀ l (t : ℝ), 0 ≤ t → t ≤ 1 → 0 ≤ dens f l t := by
            intro l t h0 h1; unfold dens; split_ifs with h
            · exact (hf ⟨l, h⟩).1 t ⟨h0, h1⟩
            · exact le_rfl
          have hpos : ∀ l, l < n → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 < dens f l t := by
            intro l hl t h0 h1; simp only [dens, dif_pos hl]; exact hm.1 ⟨l, hl⟩ t ⟨h0, h1⟩
          have hratio : ∀ k i, k ≤ i → i < n → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 →
              dens f i s * dens f k t ≤ dens f i t * dens f k s := by
            intro k i hki
            induction i, hki using Nat.le_induction with
            | base => intro _ s t _ _ _; exact le_of_eq (by ring)
            | succ i hki ih =>
              intro hi s t hs hst ht
              have h1 := ih (by omega) s t hs hst ht
              have h2 := hm.2 ⟨i, by omega⟩ ⟨i+1, hi⟩ rfl s t hs hst ht
              have pis := hpos i (by omega) s hs (by linarith)
              have pit := hpos i (by omega) t (by linarith) ht
              have pks := hpos k (by omega) s hs (by linarith)
              have pkt := hpos k (by omega) t (by linarith) ht
              have pjs := hpos (i+1) hi s hs (by linarith)
              have pjt := hpos (i+1) hi t (by linarith) ht
              have h2' : dens f (i+1) s * dens f i t ≤ dens f (i+1) t * dens f i s := by
                have : dens f (i+1) s / dens f i s ≤ dens f (i+1) t / dens f i t := by
                  rw [show dens f (i+1) = f ⟨i+1, hi⟩ from hdens ⟨i+1, hi⟩,
                    show dens f i = f ⟨i, by omega⟩ from hdens ⟨i, by omega⟩]
                  exact h2
                rw [div_le_div_iff₀ pis pit] at this; linarith
              have key : (dens f (i+1) s * dens f k t) * (dens f i s * dens f i t) ≤
                  (dens f (i+1) t * dens f k s) * (dens f i s * dens f i t) := by
                calc (dens f (i+1) s * dens f k t) * (dens f i s * dens f i t)
                    = (dens f (i+1) s * dens f i t) * (dens f i s * dens f k t) := by ring
                  _ ≤ (dens f (i+1) t * dens f i s) * (dens f i t * dens f k s) :=
                      mul_le_mul h2' h1 (by positivity) (by positivity)
                  _ = (dens f (i+1) t * dens f k s) * (dens f i s * dens f i t) := by ring
              exact le_of_mul_le_mul_right key (by positivity)
          have hA : ∀ k, k < n → ∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ w : ℕ → ℝ → ℝ, (∀ j t, 0 ≤ w j t) →
              (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc a 1)), ∑ j ∈ Finset.Ico k n, w j t ≤ 1) →
              (∀ j l, IntervalIntegrable (fun t => w j t * dens f l t) MeasureTheory.volume a 1) →
              ∫ t in a..1, w k t * dens f k t ≤ ∫ t in a..1, dens f k t := by
            intro k hk a ha0 ha1 w hw0 hw1 hwI
            apply intervalIntegral.integral_mono_ae_restrict ha1 (hwI k k) (hdIab k a 1 ha0 ha1 le_rfl)
            filter_upwards [hw1, MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht hta
            have h1 : w k t ≤ 1 := le_trans (Finset.single_le_sum (fun j _ => hw0 j t)
              (Finset.mem_Ico.mpr ⟨le_rfl, hk⟩)) ht
            have h2 := hnn k t (by linarith [hta.1]) hta.2
            nlinarith
          have core : ∀ m k, k + 1 + m = n → ∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ w : ℕ → ℝ → ℝ,
              (∀ j t, 0 ≤ w j t) →
              (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc a 1)), ∑ j ∈ Finset.Ico k n, w j t ≤ 1) →
              (∀ j l, IntervalIntegrable (fun t => w j t * dens f l t) MeasureTheory.volume a 1) →
              ∃ x : ℕ → ℝ, x k = a ∧ (∀ j, k ≤ j → j < n → x j ≤ x (j+1)) ∧ x n = 1 ∧
                ∀ j, k ≤ j → j < n → ∫ t in a..1, w j t * dens f j t ≤ val f j (x j) (x (j+1)) := by
            intro m
            induction m with
            | zero =>
              intro k hk a ha0 ha1 w hw0 hw1 hwI
              refine ⟨fun j => if j = k then a else 1, by simp, ?_, ?_, ?_⟩
              · intro j hj1 hj2
                have hjk : j = k := by omega
                show (if j = k then a else 1) ≤ (if j + 1 = k then a else 1)
                rw [if_pos hjk, if_neg (by omega)]; exact ha1
              · show (if n = k then a else 1) = 1
                rw [if_neg (by omega)]
              · intro j hj1 hj2
                have hjk : j = k := by omega
                show _ ≤ val f j (if j = k then a else 1) (if j + 1 = k then a else 1)
                rw [if_pos hjk, if_neg (by omega)]
                subst hjk
                exact hA _ (by omega) a ha0 ha1 w hw0 hw1 hwI
            | succ m ih =>
              intro k hk a ha0 ha1 w hw0 hw1 hwI
              have hkn : k + 1 < n := by omega
              have hk' : k < n := by omega
              have hA0 : 0 ≤ ∫ t in a..1, w k t * dens f k t :=
                intervalIntegral.integral_nonneg ha1
                  (fun t ht => mul_nonneg (hw0 k t) (hnn k t (by linarith [ht.1]) ht.2))
              have hA1 := hA k hk' a ha0 ha1 w hw0 hw1 hwI
              have hcont : ContinuousOn (fun c => ∫ t in a..c, dens f k t) (Set.Icc a 1) := by
                have := intervalIntegral.continuousOn_primitive_interval' (μ := MeasureTheory.volume)
                  (hdIab k a 1 ha0 ha1 le_rfl) Set.left_mem_uIcc
                rwa [Set.uIcc_of_le ha1] at this
              obtain ⟨c, hc, hcA⟩ := intermediate_value_Icc ha1 hcont
                ⟨by simp only [intervalIntegral.integral_same]; exact hA0, hA1⟩
              simp only at hcA
              have hac := hc.1
              have hc1 := hc.2
              have hc0 : 0 ≤ c := le_trans ha0 hac
              have hI : ∀ j l, IntervalIntegrable (fun t => w j t * dens f l t) MeasureTheory.volume a c :=
                fun j l => (hwI j l).mono_set (by
                  rw [Set.uIcc_of_le hac, Set.uIcc_of_le ha1]; exact Set.Icc_subset_Icc le_rfl hc1)
              have hI' : ∀ j l, IntervalIntegrable (fun t => w j t * dens f l t) MeasureTheory.volume c 1 :=
                fun j l => (hwI j l).mono_set (by
                  rw [Set.uIcc_of_le hc1, Set.uIcc_of_le ha1]; exact Set.Icc_subset_Icc hac le_rfl)
              have hsplit : ∀ j l, ∫ t in a..1, w j t * dens f l t =
                  (∫ t in a..c, w j t * dens f l t) + ∫ t in c..1, w j t * dens f l t := fun j l =>
                (intervalIntegral.integral_add_adjacent_intervals (hI j l) (hI' j l)).symm
              obtain ⟨G, hG⟩ : ∃ G, G = ∫ t in c..1, w k t * dens f k t := ⟨_, rfl⟩
              obtain ⟨L, hL⟩ : ∃ L : ℕ → ℝ, ∀ j, L j = ∫ t in a..c, w j t * dens f k t :=
                ⟨_, fun _ => rfl⟩
              have hG0 : 0 ≤ G := by
                rw [hG]
                exact intervalIntegral.integral_nonneg hc1
                  (fun t ht => mul_nonneg (hw0 k t) (hnn k t (by linarith [ht.1]) ht.2))
              have hL0 : ∀ j, 0 ≤ L j := fun j => by
                rw [hL j]
                exact intervalIntegral.integral_nonneg hac
                  (fun t ht => mul_nonneg (hw0 j t) (hnn k t (by linarith [ht.1]) (by linarith [ht.2])))
              have hLG : ∑ j ∈ Finset.Ico (k+1) n, L j ≤ G := by
                have e1 : ∑ j ∈ Finset.Ico (k+1) n, L j =
                    ∫ t in a..c, ∑ j ∈ Finset.Ico (k+1) n, w j t * dens f k t := by
                  rw [intervalIntegral.integral_finsetSum (fun j _ => hI j k)]
                  exact Finset.sum_congr rfl (fun j _ => hL j)
                have e2 : G = ∫ t in a..c, (dens f k t - w k t * dens f k t) := by
                  rw [intervalIntegral.integral_sub (hdIab k a c ha0 hac hc1) (hI k k), hcA, hsplit k k, hG]
                  ring
                rw [e1, e2]
                apply intervalIntegral.integral_mono_ae_restrict hac
                · have := IntervalIntegrable.sum (Finset.Ico (k+1) n) (fun j _ => hI j k)
                  have e : (∑ i ∈ Finset.Ico (k+1) n, fun t => w i t * dens f k t) =
                      fun u => ∑ j ∈ Finset.Ico (k+1) n, w j u * dens f k u := by
                    funext u; simp [Finset.sum_apply]
                  rw [e] at this; exact this
                · exact (hdIab k a c ha0 hac hc1).sub (hI k k)
                · have hw1' := MeasureTheory.ae_restrict_of_ae_restrict_of_subset
                    (Set.Icc_subset_Icc_right hc1) hw1
                  filter_upwards [hw1', MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht hta
                  rw [Finset.sum_eq_sum_Ico_succ_bot hk'] at ht
                  have hd := hnn k t (by linarith [hta.1]) (by linarith [hta.2])
                  rw [← Finset.sum_mul]
                  nlinarith
              have hw0' : ∀ j t, 0 ≤ (fun j t => w j t + L j / G * w k t) j t := fun j t =>
                add_nonneg (hw0 j t) (mul_nonneg (div_nonneg (hL0 j) hG0) (hw0 k t))
              have hw1' : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc c 1)),
                  ∑ j ∈ Finset.Ico (k+1) n, (fun j t => w j t + L j / G * w k t) j t ≤ 1 := by
                filter_upwards [MeasureTheory.ae_restrict_of_ae_restrict_of_subset
                  (Set.Icc_subset_Icc_left hac) hw1] with t ht
                rw [Finset.sum_eq_sum_Ico_succ_bot hk'] at ht
                rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div]
                have hq : (∑ j ∈ Finset.Ico (k+1) n, L j) / G ≤ 1 := div_le_one_of_le₀ hLG hG0
                have := hw0 k t
                nlinarith
              have hwI' : ∀ j l, IntervalIntegrable
                  (fun t => (fun j t => w j t + L j / G * w k t) j t * dens f l t)
                  MeasureTheory.volume c 1 := by
                intro j l
                have e : (fun t => (fun j t => w j t + L j / G * w k t) j t * dens f l t) =
                    fun t => w j t * dens f l t + (L j / G) * (w k t * dens f l t) := by
                  funext t; ring
                rw [e]; exact (hI' j l).add ((hI' k l).const_mul _)
              obtain ⟨x, hx0, hxm, hx1, hxv⟩ := ih (k+1) (by omega) c hc0 hc1 _ hw0' hw1' hwI'
              refine ⟨fun j => if j = k then a else x j, by simp, ?_, ?_, ?_⟩
              · intro j hj1 hj2
                show (if j = k then a else x j) ≤ (if j + 1 = k then a else x (j+1))
                rw [if_neg (show j + 1 ≠ k by omega)]
                by_cases hjk : j = k
                · rw [if_pos hjk, show j + 1 = k + 1 by omega, hx0]; exact hac
                · rw [if_neg hjk]; exact hxm j (by omega) hj2
              · show (if n = k then a else x n) = 1
                rw [if_neg (by omega)]; exact hx1
              · intro j hj1 hj2
                show _ ≤ val f j (if j = k then a else x j) (if j + 1 = k then a else x (j+1))
                rw [if_neg (show j + 1 ≠ k by omega)]
                by_cases hjk : j = k
                · rw [if_pos hjk]; subst hjk; rw [hx0]; exact hcA.symm.le
                · rw [if_neg hjk]
                  have hj : k + 1 ≤ j := by omega
                  have hv := hxv j hj hj2
                  refine le_trans ?_ hv
                  show ∫ t in a..1, w j t * dens f j t ≤ ∫ t in c..1, (w j t + L j / G * w k t) * dens f j t
                  have hkc := hpos k hk' c hc0 hc1
                  obtain ⟨q, hq⟩ : ∃ q, q = dens f j c / dens f k c := ⟨_, rfl⟩
                  have i1 : ∫ t in a..c, w j t * dens f j t ≤ q * L j := by
                    rw [hL j, ← intervalIntegral.integral_const_mul]
                    apply intervalIntegral.integral_mono_on hac (hI j j) ((hI j k).const_mul q)
                    intro t ht
                    have hr := hratio k j (by omega) hj2 t c (by linarith [ht.1]) ht.2 hc1
                    have hq' : dens f j t ≤ q * dens f k t := by
                      rw [hq, div_mul_eq_mul_div, le_div_iff₀ hkc]; linarith
                    have := hw0 j t
                    nlinarith
                  have i2 : q * G ≤ ∫ t in c..1, w k t * dens f j t := by
                    rw [hG, ← intervalIntegral.integral_const_mul]
                    apply intervalIntegral.integral_mono_on hc1 ((hI' k k).const_mul q) (hI' k j)
                    intro t ht
                    have hr := hratio k j (by omega) hj2 c t hc0 ht.1 ht.2
                    have hq' : q * dens f k t ≤ dens f j t := by
                      rw [hq, div_mul_eq_mul_div, div_le_iff₀ hkc]; linarith
                    have := hw0 k t
                    nlinarith
                  have e3 : ∫ t in c..1, (w j t + L j / G * w k t) * dens f j t =
                      (∫ t in c..1, w j t * dens f j t) + L j / G * ∫ t in c..1, w k t * dens f j t := by
                    rw [← intervalIntegral.integral_const_mul,
                      ← intervalIntegral.integral_add (hI' j j) ((hI' k j).const_mul _)]
                    congr 1; funext t; ring
                  have e4 : L j / G * G = L j := by
                    rcases eq_or_lt_of_le hG0 with h | h
                    · rw [← h, mul_zero]
                      have := Finset.single_le_sum (f := L) (fun i _ => hL0 i)
                        (Finset.mem_Ico.mpr ⟨hj, hj2⟩)
                      linarith [hL0 j]
                    · field_simp
                  have hrq : 0 ≤ L j / G := div_nonneg (hL0 j) hG0
                  rw [hsplit j j, e3]
                  have h5 : L j / G * (q * G) ≤ L j / G * ∫ t in c..1, w k t * dens f j t :=
                    mul_le_mul_of_nonneg_left i2 hrq
                  have e5 : L j / G * (q * G) = q * L j := by rw [mul_left_comm, e4]
                  linarith
          have hmeas : ∀ S : Set ℝ, IsFiniteIntervalUnion S → MeasurableSet S := by
            rintro S ⟨m, a, b, -, rfl⟩
            exact MeasurableSet.iUnion (fun k => measurableSet_Icc)
          have hmain : ∀ D : Fin n → Set ℝ, IsCakeDivision D →
              ∃ x : ℕ → ℝ, IsAllocation (n := n) x ∧
                ∀ i : Fin n, bundleVal f i (D i) ≤ val f i (x i) (x (i.val+1)) := by
            intro D hD
            let Dn : ℕ → Set ℝ := fun j => if h : j < n then D ⟨j, h⟩ else ∅
            have hDn : ∀ j, MeasurableSet (Dn j) := by
              intro j; simp only [Dn]; split_ifs with h
              · exact hmeas _ (hD.1 _)
              · exact MeasurableSet.empty
            let w : ℕ → ℝ → ℝ := fun j => (Dn j).indicator 1
            have hw0 : ∀ j t, 0 ≤ w j t := fun j t => Set.indicator_nonneg (fun _ _ => zero_le_one) t
            have hwI : ∀ j l, IntervalIntegrable (fun t => w j t * dens f l t) MeasureTheory.volume 0 1 := by
              intro j l
              have e : (fun t => w j t * dens f l t) = (Dn j).indicator (dens f l) := by
                funext t; simp only [w, Set.indicator_apply]; split_ifs <;> simp
              rw [e, intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
              exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (hdI l)).indicator (hDn j)
            have hw1 : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)),
                ∑ j ∈ Finset.Ico 0 n, w j t ≤ 1 := by
              have hN : MeasureTheory.volume (⋃ i : Fin n, ⋃ j : Fin n, ⋃ (_ : i ≠ j), D i ∩ D j) = 0 := by
                simp only [MeasureTheory.measure_iUnion_null_iff]
                intro i j hij; exact hD.2.1 i j hij
              apply MeasureTheory.ae_restrict_of_ae
              filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hN] with t ht
              simp only [Set.mem_iUnion, not_exists] at ht
              by_cases hex : ∃ j ∈ Finset.Ico 0 n, t ∈ Dn j
              · obtain ⟨j0, hj0, htj0⟩ := hex
                rw [Finset.sum_eq_single_of_mem j0 hj0]
                · simp only [w, Set.indicator_apply]; split_ifs <;> norm_num
                · intro b hb hne
                  simp only [w, Set.indicator_apply_eq_zero]
                  intro htb; exfalso
                  have hb' : b < n := (Finset.mem_Ico.mp hb).2
                  have hj0' : j0 < n := (Finset.mem_Ico.mp hj0).2
                  simp only [Dn, dif_pos hb', dif_pos hj0'] at htb htj0
                  exact ht ⟨b, hb'⟩ ⟨j0, hj0'⟩ (fun h => hne (congrArg Fin.val h)) ⟨htb, htj0⟩
              · push_neg at hex
                rw [Finset.sum_eq_zero]
                · norm_num
                intro j hj; simp only [w, Set.indicator_of_notMem (hex j hj)]
            obtain ⟨x, hx0, hxm, hx1, hxv⟩ :=
              core (n - 1) 0 (by omega) 0 le_rfl zero_le_one w hw0 hw1 hwI
            refine ⟨x, ⟨hx0, fun k hk => hxm k (Nat.zero_le _) hk, hx1⟩, ?_⟩
            intro i
            refine le_trans (le_of_eq ?_) (hxv i (Nat.zero_le _) i.isLt)
            have e : (fun t => w i t * dens f i t) = (D i).indicator (f i) := by
              funext t; simp only [w, Dn, dif_pos i.isLt, hdens i, Set.indicator_apply]
              split_ifs <;> simp
            rw [e, intervalIntegral.integral_of_le zero_le_one, ← MeasureTheory.integral_Icc_eq_integral_Ioc,
              MeasureTheory.setIntegral_indicator (hmeas _ (hD.1 i))]
            have hsub : D i ⊆ Set.Icc 0 1 := by rw [← hD.2.2]; exact Set.subset_iUnion D i
            rw [Set.inter_eq_right.mpr hsub]; rfl
          have hmono : ∀ y : ℕ → ℝ, IsAllocation (n := n) y → ∀ j l, j ≤ l → l ≤ n → y j ≤ y l := by
            intro y hy j l hjl
            induction l, hjl using Nat.le_induction with
            | base => intro _; exact le_rfl
            | succ l hjl ih => intro hl; exact le_trans (ih (by omega)) (hy.2.1 l (by omega))
          have hbv : ∀ (i : Fin n) (a b : ℝ), a ≤ b → bundleVal f i (Set.Icc a b) = val f i a b := by
            intro i a b hab
            simp only [bundleVal, val, hdens i]
            rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]
          have hdiv : ∀ (y : ℕ → ℝ) (τ : Equiv.Perm (Fin n)), IsAllocation (n := n) y →
              IsCakeDivision (fun i => Set.Icc (y (τ i)) (y ((τ i : ℕ) + 1))) := by
            intro y τ hy
            refine ⟨?_, ?_, ?_⟩
            · intro i
              refine ⟨1, fun _ => y (τ i), fun _ => y ((τ i : ℕ) + 1), fun _ => ⟨?_, ?_⟩, ?_⟩
              · rw [← hy.1]; exact hmono y hy 0 _ (Nat.zero_le _) (τ i).isLt.le
              · rw [← hy.2.2]; exact hmono y hy _ n (τ i).isLt (le_refl _)
              · ext t; simp
            · intro i j hij
              have hne : (τ i : ℕ) ≠ (τ j : ℕ) := fun h => hij (τ.injective (Fin.ext h))
              rw [Set.Icc_inter_Icc, Real.volume_Icc, ENNReal.ofReal_eq_zero]
              rcases Nat.lt_or_gt_of_ne hne with h | h
              · have := hmono y hy ((τ i : ℕ) + 1) (τ j) h (τ j).isLt.le
                have h1 : min (y ((τ i : ℕ) + 1)) (y ((τ j : ℕ) + 1)) ≤ y ((τ i : ℕ) + 1) :=
                  min_le_left _ _
                have h2 : y (τ j) ≤ max (y (τ i)) (y (τ j)) := le_max_right _ _
                linarith
              · have := hmono y hy ((τ j : ℕ) + 1) (τ i) h (τ i).isLt.le
                have h1 : min (y ((τ i : ℕ) + 1)) (y ((τ j : ℕ) + 1)) ≤ y ((τ j : ℕ) + 1) :=
                  min_le_right _ _
                have h2 : y (τ i) ≤ max (y (τ i)) (y (τ j)) := le_max_left _ _
                linarith
            · apply Set.Subset.antisymm
              · intro t ht
                simp only [Set.mem_iUnion] at ht
                obtain ⟨i, hi1, hi2⟩ := ht
                refine ⟨le_trans ?_ hi1, le_trans hi2 ?_⟩
                · rw [← hy.1]; exact hmono y hy 0 _ (Nat.zero_le _) (τ i).isLt.le
                · rw [← hy.2.2]; exact hmono y hy _ n (τ i).isLt (le_refl _)
              · intro t ht
                have hfind : ∀ l, l ≤ n → t ≤ y l → ∃ p, p < n ∧ y p ≤ t ∧ t ≤ y (p+1) := by
                  intro l
                  induction l with
                  | zero =>
                    intro _ h0
                    refine ⟨0, by omega, by rw [hy.1]; exact ht.1, ?_⟩
                    have := hmono y hy 0 1 (by omega) hn
                    linarith
                  | succ l ihl =>
                    intro hl h
                    by_cases h' : t ≤ y l
                    · exact ihl (by omega) h'
                    · exact ⟨l, by omega, by linarith, h⟩
                obtain ⟨p, hp, hp1, hp2⟩ := hfind n le_rfl (by rw [hy.2.2]; exact ht.2)
                simp only [Set.mem_iUnion]
                refine ⟨τ.symm ⟨p, hp⟩, ?_⟩
                simp only [Equiv.apply_symm_apply]
                exact ⟨hp1, hp2⟩
          refine ⟨?_, ?_⟩
          · intro D hD
            obtain ⟨x, hx, hxv⟩ := hmain D hD
            exact ⟨x, 1, hx, fun i => hxv i⟩
          · intro x σ hx hPO
            obtain ⟨x', hx', hxv⟩ := hmain _ (hdiv x σ hx)
            have hge : ∀ i : Fin n, pieceVal f x σ i ≤ val f i (x' i) (x' (i.val + 1)) := by
              intro i
              have := hxv i
              rwa [hbv i _ _ (hx.2.1 _ (σ i).isLt)] at this
            refine ⟨x', hx', fun i => ?_⟩
            by_contra hne
            apply hPO
            refine ⟨fun i => Set.Icc (x' i) (x' (i.val + 1)), ?_, ?_, i, ?_⟩
            · exact hdiv x' 1 hx'
            · intro j
              show _ ≤ bundleVal f j (Set.Icc (x' j) (x' (j.val + 1)))
              rw [hbv j _ _ (hx'.2.1 _ j.isLt)]
              exact hge j
            · show _ < bundleVal f i (Set.Icc (x' i) (x' (i.val + 1)))
              rw [hbv i _ _ (hx'.2.1 _ i.isLt)]
              exact lt_of_le_of_ne (hge i) (fun h => hne h.symm)
