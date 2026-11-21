-- Prove2me | solution 1 for MomentSearch.rakhmanov_quantile_product_representation
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T23:58:15.975165+00:00
-- url     : https://prove2.me/submissions/2377a134-fb5f-44ad-8aa2-a77999ecea8e

import Mathlib
import Theorems.Thm_MomentSearch_rakhmanov_triangle_contour_identity
import Theorems.Thm_MomentSearch_rakhmanov_triangle_side_bounds

open Set

theorem solution (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    let V : ℝ → ℝ := fun z => ∫ t in (-1 : ℝ)..1, Real.log (1 / |z-t|) * ρ t
    ∃ S : Polynomial ℝ, ∃ C : ℝ → ℝ, S.natDegree ≤ N-k ∧
      ContinuousOn C (Set.Icc (-1 : ℝ) 1) ∧
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, 0 < C z ∧
        S.eval z = C z * Real.exp (-V z) * f z) ∧
      ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1, C u ≤ 12 * C v := by 
  intro r ρ f V
  let s : ℂ := ⟨1/2, -Real.sqrt 3 / 2⟩
  let Z : ℝ → ℂ := fun t => (r : ℂ) * (1 - s * t)
  let B : ℝ → ℂ := fun t => 2 * Complex.I * (N : ℂ) * r * s *
      ∫ v in (0 : ℝ)..t, Complex.arctan ((N : ℂ) / k *
        (((r : ℂ)^2 - (Z v)^2) ^ (1/2 : ℂ)))
  let η : ℝ → ℝ := fun x => (∫ t in (0 : ℝ)..2,
      Complex.log (1 + Complex.exp (-(B t))) * (-(r : ℂ) * s) / ((x : ℂ) - Z t)).im / Real.pi
  let D := 2 / (9 * Real.exp 1) + 4 / (3 * Real.pi * Real.sqrt 3)
  obtain ⟨S,H,hdeg,hcont,hrep,hsym⟩ :=
    MomentSearch.rakhmanov_triangle_contour_identity N k hk hkN
  change ∀ z ∈ Icc (-1 : ℝ) 1, z ≠ r → z ≠ -r →
    H z = (if |z| < r then Real.log 2 else 0) + η z + η (-z) at hsym
  have side : ∀ z ∈ Icc (-1 : ℝ) 1,
      (z < r → -(2/3) * Real.log 2 - D ≤ η z ∧ η z ≤ D) ∧
      (r < z → -D ≤ η z ∧ η z ≤ (1/3) * Real.log 2 + D) :=
    MomentSearch.rakhmanov_triangle_side_bounds N k hk hkN
  let good := Ioo (-1 : ℝ) 1 ∩ ({r,-r} : Set ℝ)ᶜ
  let J := Icc (-(2/3)*Real.log 2-2*D) (Real.log 2+2*D)
  have sub : good ⊆ Icc (-1 : ℝ) 1 := fun _ h => ⟨h.1.1.le,h.1.2.le⟩
  have hb : MapsTo H good J := by
    intro x hx
    have hx' := sub hx
    have hn : -x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx'.2],by linarith [hx'.1]⟩
    have hne : x ≠ r ∧ x ≠ -r := by simpa [Set.mem_insert_iff, not_or] using hx.2
    have hp : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    change _ ≤ H x ∧ H x ≤ _
    rw [hsym x hx' hne.1 hne.2]
    by_cases hi : |x| < r
    · rw [if_pos hi]
      obtain ⟨l,u⟩ := (side x hx').1 (abs_lt.mp hi).2
      obtain ⟨l',u'⟩ := (side (-x) hn).1 (by linarith [(abs_lt.mp hi).1])
      constructor <;> linarith
    · rw [if_neg hi]
      by_cases h : x < r
      · have hh : r < -x := by
          by_contra! hh
          exact hi (abs_lt.mpr ⟨by grind,h⟩)
        obtain ⟨l,u⟩ := (side x hx').1 h
        obtain ⟨l',u'⟩ := (side (-x) hn).2 hh
        constructor <;> linarith
      · have hh : r < x := lt_of_le_of_ne (le_of_not_gt h) hne.1.symm
        obtain ⟨l,u⟩ := (side x hx').2 hh
        obtain ⟨l',u'⟩ := (side (-x) hn).1 (by linarith)
        constructor <;> linarith
  have dense : Icc (-1 : ℝ) 1 ⊆ closure good := by
    have hd := (Set.toFinite ({r,-r} : Set ℝ)).countable.dense_compl ℝ
    rw [← closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    exact closure_minimal (hd.open_subset_closure_inter isOpen_Ioo) isClosed_closure
  have allBounds (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) : H x ∈ J := by
    have h := ((hcont x hx).mono sub).mem_closure (dense hx) hb
    simpa only [show closure J = J from isClosed_Icc.closure_eq] using h
  have hD : D ≤ 33/100 := by
    have he : (27/10 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hs : (173/100 : ℝ) < Real.sqrt 3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    have hb₁ : 2 / (9 * Real.exp 1) ≤ 2 / (9 * (27/10 : ℝ)) := by gcongr
    have hb₂ : 4 / (3 * Real.pi * Real.sqrt 3) ≤ 4 / (3 * (314/100 : ℝ) * (173/100)) := by
      gcongr
      linarith [Real.pi_gt_d2]
    dsimp [D]; linarith
  have h12 : Real.log 12 = Real.log 3 + 2 * Real.log 2 := by
    rw [show (12 : ℝ) = 3*2^2 by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  refine ⟨S,fun z => Real.exp (H z),hdeg,Real.continuous_exp.comp_continuousOn hcont,
    fun z hz => ⟨Real.exp_pos _,hrep z hz⟩,?_⟩
  intro u hu v hv
  have hl := (allBounds v hv).1
  have hh := (allBounds u hu).2
  have hlog : H u ≤ Real.log 12 + H v := by
    rw [h12]
    linarith [Real.log_three_gt_d9,Real.log_two_gt_d9]
  simpa only [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<12)] using Real.exp_le_exp.mpr hlog
