-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiShiftedPathClock
-- status  : ACCEPTED   (disprove)
-- author  : @pageman
-- created : 2026-11-23T17:29:40.12459+00:00
-- url     : https://prove2.me/submissions/25fc77e5-b2d4-491e-8b78-a28306312f4f

import Definitions.Def_Kyprianou_Ch01_LampertiInverse

open MeasureTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal

set_option autoImplicit false

noncomputable def spike (s : ℝ≥0) : ℤ :=
  if (s : ℝ) < 1 then 1 else if (s : ℝ) = 1 then -1 else 5

noncomputable def tailPath (s : ℝ≥0) : ℤ :=
  if s = 0 then -1 else 5

universe u

noncomputable def pathX {Ω : Type u} : ℝ≥0 → Ω → ℤ := fun s _ => spike s

noncomputable def pathY {Ω : Type u} : ℝ≥0 → Ω → ℤ := fun s _ => tailPath s

noncomputable abbrev rho (z : ℤ) : ℝ≥0∞ := (ENNReal.ofReal (z : ℝ))⁻¹

lemma rho_one : rho 1 = 1 := by
  simp [rho]

lemma rho_five : rho 5 = (ENNReal.ofReal 5)⁻¹ := by
  simp [rho]

lemma rho_spike_of_mem_Ioc_zero_one {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    rho (spike (Real.toNNReal s)) = 1 := by
  have hlt : (Real.toNNReal s : ℝ) < 1 := by
    rw [Real.coe_toNNReal s hs0.le]
    exact hs1
  unfold spike
  rw [if_pos hlt]
  simp [ENNReal.ofReal_one]

lemma rho_spike_of_gt_one {s : ℝ} (hs : 1 < s) :
    rho (spike (Real.toNNReal s)) = (ENNReal.ofReal 5)⁻¹ := by
  have hscoe : (Real.toNNReal s : ℝ) = s :=
    Real.coe_toNNReal s (le_trans (by norm_num : (0 : ℝ) ≤ 1) hs.le)
  have hnot : ¬ (Real.toNNReal s : ℝ) < 1 := by
    rw [hscoe]
    linarith
  have hne : (Real.toNNReal s : ℝ) ≠ 1 := by
    rw [hscoe]
    linarith
  unfold spike
  rw [if_neg hnot, if_neg hne]
  simp

lemma rho_tail_of_pos {s : ℝ} (hs : 0 < s) :
    rho (tailPath (Real.toNNReal s)) = (ENNReal.ofReal 5)⁻¹ := by
  have hscoe : (Real.toNNReal s : ℝ) = s := Real.coe_toNNReal s hs.le
  have hne : Real.toNNReal s ≠ 0 := by
    intro h
    have : (Real.toNNReal s : ℝ) = 0 := by simpa using congrArg (fun z : ℝ≥0 => (z : ℝ)) h
    rw [hscoe] at this
    exact hs.ne' this
  unfold tailPath
  rw [if_neg hne]
  simp

lemma ae_rho_spike_eq_one (τ : ℝ≥0) (hτ : (τ : ℝ) ≤ 1) :
    ∀ᵐ s ∂volume, s ∈ Ioc (0 : ℝ) (τ : ℝ) → rho (spike (Real.toNNReal s)) = 1 := by
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_singleton (1 : ℝ))
  intro s hs
  rw [mem_setOf_eq, _root_.not_imp] at hs
  rcases hs with ⟨hsI, hbad⟩
  rcases hsI with ⟨hs0, hsτ⟩
  by_cases hlt : s < 1
  · exact False.elim (hbad (rho_spike_of_mem_Ioc_zero_one hs0 hlt))
  · have hs1 : s = 1 := le_antisymm (hsτ.trans hτ) (le_of_not_gt hlt)
    simpa [hs1] using (mem_singleton_iff).mpr hs1

lemma occX_le_one {Ω : Type u} (ω : Ω) (τ : ℝ≥0) (hτ : (τ : ℝ) ≤ 1) :
    reciprocalOccupation pathX τ ω = ENNReal.ofReal (τ : ℝ) := by
  simp only [reciprocalOccupation, pathX]
  rw [setLIntegral_congr_fun_ae measurableSet_Ioc (ae_rho_spike_eq_one τ hτ)]
  rw [setLIntegral_const]
  simp [rho_one, one_mul, Real.volume_Ioc]

lemma Ioc_zero_split (τ : ℝ) (hτ : 1 < τ) :
    Ioc (0 : ℝ) τ = Ioc 0 1 ∪ Ioc 1 τ := by
  ext s
  simp only [mem_union, mem_Ioc]
  constructor
  · rintro ⟨hs0, hsτ⟩
    by_cases hs1 : s ≤ 1
    · exact Or.inl ⟨hs0, hs1⟩
    · exact Or.inr ⟨lt_of_not_ge hs1, hsτ⟩
  · rintro (⟨hs0, hs1⟩ | ⟨hs1, hsτ⟩)
    · exact ⟨hs0, le_trans hs1 (le_of_lt hτ)⟩
    · exact ⟨lt_trans (by norm_num) hs1, hsτ⟩

lemma Ioc_zero_one_disjoint_right (τ : ℝ) :
    Disjoint (Ioc (0 : ℝ) 1) (Ioc 1 τ) := by
  rw [Set.disjoint_left]
  intro s hs1 hs2
  exact (lt_irrefl s) (lt_of_le_of_lt hs1.2 hs2.1)

lemma occX_gt_one {Ω : Type u} (ω : Ω) (τ : ℝ≥0) (hτ : 1 < (τ : ℝ)) :
    reciprocalOccupation pathX τ ω =
      ENNReal.ofReal (1 + ((τ : ℝ) - 1) / 5) := by
  simp only [reciprocalOccupation, pathX]
  have hsplit := Ioc_zero_split (τ : ℝ) hτ
  rw [hsplit]
  rw [lintegral_union measurableSet_Ioc (Ioc_zero_one_disjoint_right (τ : ℝ))]
  have hleft :
      ∫⁻ s in Ioc (0 : ℝ) 1, rho (spike (Real.toNNReal s)) ∂volume = ENNReal.ofReal 1 := by
    have hae := ae_rho_spike_eq_one (1 : ℝ≥0) le_rfl
    simp only [NNReal.coe_one] at hae
    rw [setLIntegral_congr_fun_ae measurableSet_Ioc hae]
    rw [setLIntegral_const]
    simp [rho_one, one_mul, Real.volume_Ioc]
  have hrightEq : ∀ s, s ∈ Ioc (1 : ℝ) (τ : ℝ) →
      rho (spike (Real.toNNReal s)) = (ENNReal.ofReal 5)⁻¹ := by
    intro s hs
    exact rho_spike_of_gt_one hs.1
  have hright :
      ∫⁻ s in Ioc (1 : ℝ) (τ : ℝ), rho (spike (Real.toNNReal s)) ∂volume =
        (ENNReal.ofReal 5)⁻¹ * ENNReal.ofReal ((τ : ℝ) - 1) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc hrightEq, setLIntegral_const, Real.volume_Ioc]
  rw [hleft, hright]
  have hmul :
      (ENNReal.ofReal 5)⁻¹ * ENNReal.ofReal ((τ : ℝ) - 1) =
        ENNReal.ofReal (((τ : ℝ) - 1) / 5) := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact (ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 5)).symm
  rw [hmul, ← ENNReal.ofReal_add (by norm_num) (div_nonneg (sub_nonneg.mpr hτ.le) (by norm_num))]

lemma occY_pos {Ω : Type u} (ω : Ω) (σ : ℝ≥0) (hσ : 0 < σ) :
    reciprocalOccupation pathY σ ω = ENNReal.ofReal ((σ : ℝ) / 5) := by
  simp only [reciprocalOccupation, pathY]
  have hfun : ∀ s, s ∈ Ioc (0 : ℝ) (σ : ℝ) →
      rho (tailPath (Real.toNNReal s)) = (ENNReal.ofReal 5)⁻¹ := by
    intro s hs
    exact rho_tail_of_pos hs.1
  rw [setLIntegral_congr_fun measurableSet_Ioc hfun, setLIntegral_const, Real.volume_Ioc]
  simp only [sub_zero, mul_comm]
  rw [← div_eq_mul_inv]
  exact (ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 5)).symm

lemma two_lt_occX_iff {Ω : Type u} (ω : Ω) (τ : ℝ≥0) :
    ((2 : ℝ≥0) : ℝ≥0∞) < reciprocalOccupation pathX τ ω ↔ 6 < (τ : ℝ) := by
  by_cases hτ : (τ : ℝ) ≤ 1
  · rw [occX_le_one ω τ hτ]
    constructor
    · intro h
      have : (2 : ℝ) < (τ : ℝ) :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).1
          (by simpa [ENNReal.ofReal_ofNat] using h)
      linarith
    · intro h
      linarith
  · have hgt : 1 < (τ : ℝ) := lt_of_not_ge hτ
    rw [occX_gt_one ω τ hgt]
    have hpos : 0 < 1 + ((τ : ℝ) - 1) / 5 := by positivity
    rw [show ((2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    rw [ENNReal.ofReal_lt_ofReal_iff hpos]
    constructor
    · intro h
      linarith
    · intro h
      linarith

lemma one_lt_occY_iff {Ω : Type u} (ω : Ω) (σ : ℝ≥0) :
    ((1 : ℝ≥0) : ℝ≥0∞) < reciprocalOccupation pathY σ ω ↔ 5 < (σ : ℝ) := by
  by_cases hσ : (σ : ℝ) = 0
  · have hzero : σ = 0 := by
      apply NNReal.coe_injective
      simpa using hσ
    subst hzero
    have hzeroVol : volume (Ioc (0 : ℝ) 0) = 0 := by simp [Real.volume_Ioc]
    simp only [reciprocalOccupation, pathY, NNReal.coe_zero]
    rw [setLIntegral_measure_zero _ _ hzeroVol]
    norm_num
  · have hpos : (0 : ℝ) < σ := lt_of_le_of_ne (NNReal.coe_nonneg σ) (Ne.symm hσ)
    have hσpos : 0 < σ := by
      exact NNReal.coe_pos.mp hpos
    rw [occY_pos ω σ hσpos]
    rw [show ((1 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < (σ : ℝ) / 5)]
    constructor
    · intro h
      linarith
    · intro h
      linarith

lemma negSetX {Ω : Type u} (ω : Ω) : {t : ℝ≥0 | 0 < t ∧ pathX t ω < 0} = {(1 : ℝ≥0)} := by
  ext t
  simp only [mem_setOf_eq, mem_singleton_iff, pathX]
  constructor
  · rintro ⟨ht, hneg⟩
    by_cases hlt : (t : ℝ) < 1
    · simp [spike, hlt] at hneg
    · by_cases heq : (t : ℝ) = 1
      · exact Subtype.ext heq
      · simp [spike, hlt, heq] at hneg
  · intro ht
    subst ht
    refine ⟨by norm_num, ?_⟩
    simp [spike]

lemma negSetY {Ω : Type u} (ω : Ω) : {t : ℝ≥0 | 0 < t ∧ pathY t ω < 0} = ∅ := by
  ext t
  simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨ht, hneg⟩
  have hne : t ≠ 0 := ne_of_gt ht
  simp [pathY, tailPath, hne] at hneg

lemma passageX {Ω : Type u} (ω : Ω) : firstNegativePassage pathX ω = (1 : ℝ≥0) := by
  have hex : ∃ t : ℝ≥0, 0 < t ∧ pathX t ω < 0 := ⟨1, by norm_num, by simp [pathX, spike]⟩
  simp only [firstNegativePassage]
  rw [if_pos hex, negSetX ω]
  simp [sInf_singleton]

lemma passageY {Ω : Type u} (ω : Ω) : firstNegativePassage pathY ω = (⊤ : WithTop ℝ≥0) := by
  simp only [firstNegativePassage]
  rw [if_neg]
  intro hex
  rcases hex with ⟨t, ht⟩
  have : t ∈ {t : ℝ≥0 | 0 < t ∧ pathY t ω < 0} := ht
  rw [negSetY ω] at this
  exact this.elim

lemma inverseX {Ω : Type u} (ω : Ω) : inverseReciprocalOccupation pathX (2 : ℝ≥0) ω = (6 : ℝ≥0) := by
  have hex : ∃ s : ℝ≥0, ((2 : ℝ≥0) : ℝ≥0∞) < reciprocalOccupation pathX s ω := by
    refine ⟨7, ?_⟩
    rw [two_lt_occX_iff ω]
    norm_num
  simp only [inverseReciprocalOccupation]
  rw [if_pos hex]
  have hset : {s : ℝ≥0 | ((2 : ℝ≥0) : ℝ≥0∞) < reciprocalOccupation pathX s ω} =
      Ioi (6 : ℝ≥0) := by
    ext s
    simp only [mem_setOf_eq, mem_Ioi, two_lt_occX_iff ω]
    exact (NNReal.coe_lt_coe : ((6 : ℝ≥0) : ℝ) < (s : ℝ) ↔ (6 : ℝ≥0) < s)
  rw [hset, csInf_Ioi]

lemma inverseY {Ω : Type u} (ω : Ω) : inverseReciprocalOccupation pathY (1 : ℝ≥0) ω = (5 : ℝ≥0) := by
  have hex : ∃ s : ℝ≥0, ((1 : ℝ≥0) : ℝ≥0∞) < reciprocalOccupation pathY s ω := by
    refine ⟨6, ?_⟩
    rw [one_lt_occY_iff ω]
    norm_num
  simp only [inverseReciprocalOccupation]
  rw [if_pos hex]
  have hset : {s : ℝ≥0 | ((1 : ℝ≥0) : ℝ≥0∞) < reciprocalOccupation pathY s ω} =
      Ioi (5 : ℝ≥0) := by
    ext s
    simp only [mem_setOf_eq, mem_Ioi, one_lt_occY_iff ω]
    exact (NNReal.coe_lt_coe : ((5 : ℝ≥0) : ℝ) < (s : ℝ) ↔ (5 : ℝ≥0) < s)
  rw [hset, csInf_Ioi]

theorem solution :
    ¬ (∀ {Ω : Type} (X Y : ℝ≥0 → Ω → ℤ) (ω : Ω)
        (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
        (A : ℝ) (hA : 0 ≤ A)
        (hFirst : A ≤ (y : ℝ) * (t : ℝ))
        (hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A → X s ω = (y : ℤ))
        (hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
          X u ω = Y (Real.toNNReal ((u : ℝ) - A)) ω),
        (compoundPoissonToBranching X t ω).toNat =
          (compoundPoissonToBranching Y
            (Real.toNNReal ((t : ℝ) - A / (y : ℝ))) ω).toNat) := by
  intro h
  let X : ℝ≥0 → Unit → ℤ := pathX
  let Y : ℝ≥0 → Unit → ℤ := pathY
  let ω : Unit := ()
  have hprefix : ∀ s : ℝ≥0, (s : ℝ) < 1 → X s ω = (1 : ℤ) := by
    intro s hs
    simp [X, pathX, spike, hs]
  have hshift : ∀ v : ℝ≥0, (1 : ℝ) ≤ (v : ℝ) →
      X v ω = Y (Real.toNNReal ((v : ℝ) - 1)) ω := by
    intro v hv
    by_cases hv1 : (v : ℝ) = 1
    · have hzero : Real.toNNReal ((v : ℝ) - 1) = 0 := by
        simp [hv1]
      simp [X, Y, pathX, pathY, spike, tailPath, hv1, hzero]
    · have hgt : (1 : ℝ) < v := lt_of_le_of_ne hv (fun h => hv1 h.symm)
      have hpos : Real.toNNReal ((v : ℝ) - 1) ≠ 0 := by
        intro h0
        have : (Real.toNNReal ((v : ℝ) - 1) : ℝ) = 0 := by simpa using congrArg (fun z : ℝ≥0 => (z : ℝ)) h0
        rw [Real.coe_toNNReal _ (by linarith)] at this
        linarith
      have hnot : ¬ (v : ℝ) < 1 := not_lt.mpr hv
      have hne : (v : ℝ) ≠ 1 := hv1
      simp [X, Y, pathX, pathY, spike, tailPath, hnot, hne, hpos]
  have hclaim :=
    h X Y ω 1 (by norm_num) (2 : ℝ≥0) (1 : ℝ) (by norm_num) (by norm_num)
      hprefix hshift
  have hres : Real.toNNReal (↑(2 : ℝ≥0) - 1 / ↑(1 : ℕ)) = 1 := by norm_num
  have hL : compoundPoissonToBranching X (2 : ℝ≥0) ω = -1 := by
    simp only [compoundPoissonToBranching, X, inverseX ω, passageX ω]
    have hmin : min ((6 : ℝ≥0) : WithTop ℝ≥0) ((1 : ℝ≥0) : WithTop ℝ≥0) =
        ((1 : ℝ≥0) : WithTop ℝ≥0) := by
      simpa using (min_eq_right (show ((1 : ℝ≥0) : WithTop ℝ≥0) ≤ (6 : ℝ≥0) by simp))
    simp [hmin, pathX, spike]
  have hR : compoundPoissonToBranching Y (1 : ℝ≥0) ω = 5 := by
    simp only [compoundPoissonToBranching, Y, inverseY ω, passageY ω]
    have hmin : min ((5 : ℝ≥0) : WithTop ℝ≥0) (⊤ : WithTop ℝ≥0) =
        ((5 : ℝ≥0) : WithTop ℝ≥0) := by
      simp
    simp [hmin, pathY, tailPath]
  rw [hres] at hclaim
  rw [hL, hR] at hclaim
  rw [show (-1 : ℤ) = Int.negSucc 0 by rfl] at hclaim
  simp at hclaim
