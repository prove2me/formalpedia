-- Prove2me | solution 1 for LovaszSchrijver.NPlus.valid_FRAC_of_bipartite_support
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:39:57.70875+00:00
-- url     : https://prove2.me/submissions/e119afa1-c543-450f-bad9-fc46ac1175fe

import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_StableSet



namespace LovaszSchrijver.NPlus

open MeasureTheory Set

theorem vfb_intL (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ∫ θ in Ioc (0:ℝ) 1, (Iio x).indicator (1 : ℝ → ℝ) θ = x := by
  rw [integral_indicator_one measurableSet_Iio]
  rw [measureReal_restrict_apply measurableSet_Iio]
  have : Iio x ∩ Ioc (0:ℝ) 1 = Ioo 0 x := by
    ext t; simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]; constructor
    · intro h; exact ⟨h.2.1, h.1⟩
    · intro h; exact ⟨h.2, h.1, by linarith [h.2]⟩
  rw [this, Real.volume_real_Ioo_of_le h0]; ring

theorem vfb_intR (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ∫ θ in Ioc (0:ℝ) 1, (Ioi (1 - x)).indicator (1 : ℝ → ℝ) θ = x := by
  rw [integral_indicator_one measurableSet_Ioi]
  rw [measureReal_restrict_apply measurableSet_Ioi]
  have : Ioi (1 - x) ∩ Ioc (0:ℝ) 1 = Ioc (1 - x) 1 := by
    ext t; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]; constructor
    · intro h; exact ⟨h.1, h.2.2⟩
    · intro h; exact ⟨h.1, by linarith [h.1], h.2⟩
  rw [this, Real.volume_real_Ioc_of_le (by linarith)]; ring

theorem vfb_integ (s : Set ℝ) (hs : MeasurableSet s) (a : ℝ) :
    IntegrableOn (fun θ => a * s.indicator (1 : ℝ → ℝ) θ) (Ioc 0 1) := by
  apply Integrable.const_mul
  apply IntegrableOn.indicator _ hs
  exact integrableOn_const (by simp)

theorem vfb_core {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w) (a : V → ℝ) (b : ℝ)
    (hvalid : Valid (STAB G) a b) (hbip : (G.induce {i | a i ≠ 0}).Colorable 2) :
    Valid (FRAC G) a b := by
  classical
  intro x hx
  obtain ⟨hx0, hxe⟩ := hx
  have hx1 : ∀ i, x i ≤ 1 := by
    intro i
    obtain ⟨j, hj⟩ := hG i
    linarith [hxe i j hj, hx0 j]
  obtain ⟨c⟩ := hbip
  let L : V → Prop := fun i => ∃ h : a i ≠ 0, c ⟨i, h⟩ = 0
  let I : ℝ → Finset V := fun θ => Finset.univ.filter
    (fun i => 0 < a i ∧ ((L i ∧ θ < x i) ∨ (¬ L i ∧ 1 - x i < θ)))
  -- each level set is stable
  have hstab : ∀ θ, ∑ i, a i * chi (I θ) i ≤ b := by
    intro θ
    apply hvalid
    apply subset_convexHull
    refine ⟨I θ, ?_, rfl⟩
    intro i hi j hj hij hadj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_setOf_eq, I] at hi hj
    have hai : a i ≠ 0 := ne_of_gt hi.1
    have haj : a j ≠ 0 := ne_of_gt hj.1
    have hcv : c ⟨i, hai⟩ ≠ c ⟨j, haj⟩ := c.valid (by simpa using hadj)
    rcases hi.2 with ⟨hLi, hθi⟩ | ⟨hLi, hθi⟩ <;> rcases hj.2 with ⟨hLj, hθj⟩ | ⟨hLj, hθj⟩
    · obtain ⟨_, h1⟩ := hLi; obtain ⟨_, h2⟩ := hLj
      exact hcv (h1.trans h2.symm)
    · linarith [hxe i j hadj]
    · linarith [hxe i j hadj]
    · have h1 : c ⟨i, hai⟩ ≠ 0 := fun h => hLi ⟨hai, h⟩
      have h2 : c ⟨j, haj⟩ ≠ 0 := fun h => hLj ⟨haj, h⟩
      apply hcv
      revert h1 h2
      generalize c ⟨i, hai⟩ = p; generalize c ⟨j, haj⟩ = q
      intro h1 h2; fin_cases p <;> fin_cases q <;> simp_all
  -- rewrite each summand as an indicator
  let g : V → ℝ → ℝ := fun i θ => if 0 < a i then
      (if L i then a i * (Iio (x i)).indicator (1 : ℝ → ℝ) θ
        else a i * (Ioi (1 - x i)).indicator (1 : ℝ → ℝ) θ) else 0
  have hg : ∀ i θ, a i * chi (I θ) i = g i θ := by
    intro i θ
    simp only [g, chi, I, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases ha : 0 < a i
    · by_cases hL : L i
      · by_cases ht : θ < x i
        · simp [ha, hL, ht, indicator_of_mem (show θ ∈ Iio (x i) from ht)]
        · simp [ha, hL, ht, indicator_of_notMem (show θ ∉ Iio (x i) from ht)]
      · by_cases ht : 1 - x i < θ
        · simp [ha, hL, ht, indicator_of_mem (show θ ∈ Ioi (1 - x i) from ht)]
        · simp [ha, hL, ht, indicator_of_notMem (show θ ∉ Ioi (1 - x i) from ht)]
    · simp [ha]
  have hgint : ∀ i, IntegrableOn (g i) (Ioc 0 1) := by
    intro i
    simp only [g]
    split_ifs
    · exact vfb_integ _ measurableSet_Iio _
    · exact vfb_integ _ measurableSet_Ioi _
    · exact integrableOn_const (by simp)
  have hgval : ∀ i, ∫ θ in Ioc (0:ℝ) 1, g i θ = if 0 < a i then a i * x i else 0 := by
    intro i
    simp only [g]
    split_ifs
    · rw [integral_const_mul, vfb_intL _ (hx0 i) (hx1 i)]
    · rw [integral_const_mul, vfb_intR _ (hx0 i) (hx1 i)]
    · simp
  have hmono : ∫ θ in Ioc (0:ℝ) 1, (∑ i, g i θ) ≤ ∫ θ in Ioc (0:ℝ) 1, b := by
    apply setIntegral_mono
    · exact integrable_finset_sum _ (fun i _ => hgint i)
    · exact integrableOn_const (by simp)
    · intro θ
      have := hstab θ
      simp only [hg] at this
      exact this
  rw [integral_finset_sum _ (fun i _ => hgint i)] at hmono
  simp only [hgval, setIntegral_const] at hmono
  have hvol : (volume (Ioc (0:ℝ) 1)).toReal = 1 := by simp
  have : volume.real (Ioc (0:ℝ) 1) = 1 := by simp
  rw [this, one_smul] at hmono
  calc ∑ i, a i * x i ≤ ∑ i, (if 0 < a i then a i * x i else 0) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with h
        · exact le_rfl
        · push_neg at h; exact mul_nonpos_of_nonpos_of_nonneg h (hx0 i)
    _ ≤ b := hmono

end LovaszSchrijver.NPlus

open LovaszSchrijver.NPlus


theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w) (a : V → ℝ) (b : ℝ)
    (hvalid : Valid (STAB G) a b) (hbip : (G.induce {i | a i ≠ 0}).Colorable 2) :
    Valid (FRAC G) a b := by
  exact vfb_core G hG a b hvalid hbip
