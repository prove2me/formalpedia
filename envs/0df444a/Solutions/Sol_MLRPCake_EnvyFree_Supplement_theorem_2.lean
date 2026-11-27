-- Prove2me | solution 1 for MLRPCake.EnvyFree.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:08:12.056824+00:00
-- url     : https://prove2.me/submissions/dccc07e3-e8e8-4342-91a4-cce11adcd9e3

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_Divisions

open MLRPCake
open MLRPCake.EnvyFree
open MLRPCake.EnvyFree.Supplement

/-- Theorem 2, p. 9: under MLRP every envy-free allocation (contiguous pieces, any assignment
order) is Pareto optimal over the set of all cake divisions. -/
theorem solution {n : ℕ} (f : Fin n → ℝ → ℝ) (hn : 1 ≤ n) (hf : IsInstance f) (hm : IsMLRP f)
    (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)) (hx : IsAllocation (n := n) x)
    (hef : IsEnvyFree f x σ) :
    ParetoOptimal f (pieceVal f x σ) := by
      classical
      have hdens : ∀ j (hj : j < n), dens f j = f ⟨j, hj⟩ := by
        intro j hj; unfold dens; rw [dif_pos hj]
      have hdensF : ∀ i : Fin n, dens f (i : ℕ) = f i := by
        intro i; rw [hdens i i.isLt]
      have xmono : ∀ d a, a + d ≤ n → x a ≤ x (a + d) := by
        intro d; induction d with
        | zero => intro a _; simp
        | succ d ih =>
          intro a h
          have h1 := ih a (by omega)
          have h2 := hx.2.1 (a + d) (by omega)
          rw [← add_assoc]; linarith
      have xle : ∀ a b, a ≤ b → b ≤ n → x a ≤ x b := by
        intro a b hab hb
        have := xmono (b - a) a (by omega)
        rwa [Nat.add_sub_cancel' hab] at this
      have x01 : ∀ k ≤ n, 0 ≤ x k ∧ x k ≤ 1 := by
        intro k hk
        have h0 := xle 0 k (by omega) hk
        have h1 := xle k n hk le_rfl
        rw [hx.1] at h0; rw [hx.2.2] at h1
        exact ⟨h0, h1⟩
      have pos : ∀ j < n, ∀ t ∈ Set.Icc (0:ℝ) 1, 0 < dens f j t := by
        intro j hj t ht
        rw [hdens j hj]; exact hm.1 _ t ht
      have mlrp : ∀ m, m + 1 < n → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 →
          dens f (m+1) s / dens f m s ≤ dens f (m+1) t / dens f m t := by
        intro m hm1 s t h0 hst h1
        rw [hdens m (by omega), hdens (m+1) hm1]
        exact hm.2 ⟨m, by omega⟩ ⟨m+1, hm1⟩ rfl s t h0 hst h1
      set lam : ℕ → ℝ := fun j => ∏ m ∈ Finset.range j, dens f m (x (m+1)) / dens f (m+1) (x (m+1))
        with hlam
      have lam_succ : ∀ m, lam (m+1) = lam m * (dens f m (x (m+1)) / dens f (m+1) (x (m+1))) := by
        intro m; simp only [hlam]; rw [Finset.prod_range_succ]
      have lampos : ∀ j < n, 0 < lam j := by
        intro j hj
        simp only [hlam]
        apply Finset.prod_pos
        intro m hmj
        rw [Finset.mem_range] at hmj
        have hx1 := x01 (m+1) (by omega)
        exact div_pos (pos m (by omega) _ ⟨hx1.1, hx1.2⟩) (pos (m+1) (by omega) _ ⟨hx1.1, hx1.2⟩)
      set F : ℕ → ℝ → ℝ := fun j t => lam j * dens f j t with hF
      have stepdown : ∀ m, m + 1 < n → ∀ t, 0 ≤ t → t ≤ x (m+1) → F (m+1) t ≤ F m t := by
        intro m hm1 t h0 ht
        have hx1 := x01 (m+1) (by omega)
        have ht1 : t ≤ 1 := le_trans ht hx1.2
        have hr := mlrp m hm1 t (x (m+1)) h0 ht hx1.2
        have pa := pos m (by omega) _ ⟨hx1.1, hx1.2⟩
        have pb := pos (m+1) hm1 _ ⟨hx1.1, hx1.2⟩
        have pt := pos m (by omega) t ⟨h0, ht1⟩
        rw [div_le_div_iff₀ pt pa] at hr
        simp only [hF]; rw [lam_succ]
        have hl := lampos m (by omega)
        rw [mul_assoc, mul_le_mul_iff_of_pos_left hl, div_mul_eq_mul_div, div_le_iff₀ pb]
        nlinarith
      have stepup : ∀ m, m + 1 < n → ∀ t, x (m+1) ≤ t → t ≤ 1 → F m t ≤ F (m+1) t := by
        intro m hm1 t ht h1
        have hx1 := x01 (m+1) (by omega)
        have h0 : 0 ≤ t := le_trans hx1.1 ht
        have hr := mlrp m hm1 (x (m+1)) t hx1.1 ht h1
        have pa := pos m (by omega) _ ⟨hx1.1, hx1.2⟩
        have pb := pos (m+1) hm1 _ ⟨hx1.1, hx1.2⟩
        have pt := pos m (by omega) t ⟨h0, h1⟩
        rw [div_le_div_iff₀ pa pt] at hr
        simp only [hF]; rw [lam_succ]
        have hl := lampos m (by omega)
        rw [mul_assoc, mul_le_mul_iff_of_pos_left hl, div_mul_eq_mul_div, le_div_iff₀ pb]
        nlinarith
      have peak : ∀ k < n, ∀ t ∈ Set.Icc (x k) (x (k+1)), ∀ j < n, F j t ≤ F k t := by
        intro k hk t ht j hj
        have hxk := x01 k (by omega)
        have hxk1 := x01 (k+1) (by omega)
        have t0 : 0 ≤ t := le_trans hxk.1 ht.1
        have t1 : t ≤ 1 := le_trans ht.2 hxk1.2
        have up : ∀ d, k + d < n → F (k + d) t ≤ F k t := by
          intro d; induction d with
          | zero => intro _; simp
          | succ d ih =>
            intro hd
            have h1 := ih (by omega)
            have h2 := stepdown (k + d) (by omega) t t0
              (le_trans ht.2 (xle (k+1) (k+d+1) (by omega) (by omega)))
            rw [← add_assoc]; linarith
        have down : ∀ d j, j + d = k → F j t ≤ F k t := by
          intro d; induction d with
          | zero => intro j hj; simp at hj; rw [hj]
          | succ d ih =>
            intro j hjd
            have h1 := ih (j+1) (by omega)
            have h2 := stepup j (by omega) t (le_trans (xle (j+1) k (by omega) (by omega)) ht.1) t1
            linarith
        rcases le_total k j with h | h
        · have := up (j - k) (by omega)
          rwa [Nat.add_sub_cancel' h] at this
        · exact down (k - j) j (by omega)
      have hne : (Finset.range n).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
      set g : ℝ → ℝ := (Finset.range n).sup' hne F with hg
      have g_apply : ∀ t, g t = (Finset.range n).sup' hne (fun j => F j t) := by
        intro t; simp only [hg]; rw [Finset.sup'_apply]
      have g_ge : ∀ i < n, ∀ t, F i t ≤ g t := by
        intro i hi t; rw [g_apply]
        exact Finset.le_sup' (fun j => F j t) (Finset.mem_range.mpr hi)
      have g_eq : ∀ k < n, ∀ t ∈ Set.Icc (x k) (x (k+1)), g t = F k t := by
        intro k hk t ht
        apply le_antisymm
        · rw [g_apply]
          apply Finset.sup'_le
          intro j hj
          exact peak k hk t ht j (Finset.mem_range.mp hj)
        · exact g_ge k hk t
      have Fint : ∀ j < n, MeasureTheory.IntegrableOn (F j) (Set.Icc (0:ℝ) 1) := by
        intro j hj
        have h := (hf ⟨j, hj⟩).2.2.1
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)] at h
        rw [← hdens j hj] at h
        exact h.const_mul (lam j)
      have gint : MeasureTheory.IntegrableOn g (Set.Icc (0:ℝ) 1) := by
        simp only [hg]
        apply Finset.sup'_induction hne F (p := fun h => MeasureTheory.IntegrableOn h (Set.Icc (0:ℝ) 1) MeasureTheory.volume)
        · intro a ha b hb; exact MeasureTheory.Integrable.sup ha hb
        · intro j hj; exact Fint j (Finset.mem_range.mp hj)
      rintro ⟨D, hD, hDge, k, hk⟩
      have Dsub : ∀ i, D i ⊆ Set.Icc (0:ℝ) 1 := by
        intro i; rw [← hD.2.2]; exact Set.subset_iUnion D i
      have Dmeas : ∀ i, MeasurableSet (D i) := by
        intro i
        obtain ⟨m, a, b, _, hS⟩ := hD.1 i
        rw [hS]; exact MeasurableSet.iUnion (fun k => measurableSet_Icc)
      have S1 : ∀ i : Fin n, lam i * bundleVal f i (D i) ≤ ∫ t in D i, g t := by
        intro i
        unfold bundleVal
        rw [← MeasureTheory.integral_const_mul]
        apply MeasureTheory.setIntegral_mono_on
        · have := (Fint i i.isLt).mono_set (Dsub i)
          simp only [hF, hdensF] at this
          exact this
        · exact gint.mono_set (Dsub i)
        · exact Dmeas i
        · intro t _
          have := g_ge i i.isLt t
          simp only [hF, hdensF] at this
          exact this
      have S2 : ∑ i : Fin n, ∫ t in D i, g t = ∫ t in Set.Icc (0:ℝ) 1, g t := by
        rw [← hD.2.2, MeasureTheory.integral_iUnion_ae, tsum_fintype]
        · intro i; exact (Dmeas i).nullMeasurableSet
        · intro i j hij; exact hD.2.1 i j hij
        · rw [hD.2.2]; exact gint
      have S3 : ∫ t in Set.Icc (0:ℝ) 1, g t
          = ∑ k ∈ Finset.range n, lam k * val f k (x k) (x (k+1)) := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
        rw [← hx.1, ← hx.2.2, ← intervalIntegral.sum_integral_adjacent_intervals]
        · apply Finset.sum_congr rfl
          intro k hk
          have hk' := Finset.mem_range.mp hk
          unfold val
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le (hx.2.1 k hk')] at ht
          exact g_eq k hk' t ht
        · intro k hk
          apply MeasureTheory.IntegrableOn.intervalIntegrable
          apply gint.mono_set
          rw [Set.uIcc_of_le (hx.2.1 k hk)]
          exact Set.Icc_subset_Icc (x01 k (by omega)).1 (x01 (k+1) (by omega)).2
      have S4 : ∑ k ∈ Finset.range n, lam k * val f k (x k) (x (k+1))
          = ∑ i : Fin n, lam i * val f i (x i) (x ((i:ℕ)+1)) :=
        (Fin.sum_univ_eq_sum_range (fun k => lam k * val f k (x k) (x (k+1))) n).symm
      have S5 : ∑ i : Fin n, lam i * val f i (x i) (x ((i:ℕ)+1)) ≤ ∑ i : Fin n, lam i * pieceVal f x σ i := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (lampos i i.isLt).le
        have := hef i (σ.symm i)
        simp only [Equiv.apply_symm_apply] at this
        exact this
      have S6 : ∑ i : Fin n, lam i * pieceVal f x σ i < ∑ i : Fin n, lam i * bundleVal f i (D i) := by
        apply Finset.sum_lt_sum
        · intro i _; exact mul_le_mul_of_nonneg_left (hDge i) (lampos i i.isLt).le
        · exact ⟨k, Finset.mem_univ _, mul_lt_mul_of_pos_left hk (lampos k k.isLt)⟩
      have S7 : ∑ i : Fin n, lam i * bundleVal f i (D i) ≤ ∑ i : Fin n, ∫ t in D i, g t :=
        Finset.sum_le_sum (fun i _ => S1 i)
      linarith
