-- Prove2me | solution 1 for IsodiamVar.Simplex.theorem_1_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T20:48:45.20824+00:00
-- url     : https://prove2.me/submissions/8dc21231-784b-4cdc-9eda-b62e26d61de1

import Mathlib
import Definitions.Def_IsodiamVar_Simplex_Defs

open MeasureTheory

namespace IsodiamSolT17
open IsodiamVar.Simplex

lemma integral_sum_dirac {n : ℕ} {ι G : Type*} [Fintype ι] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (c : ι → ENNReal) (hc : ∀ i, c i ≠ ⊤) (p : ι → E n) (f : E n → G) :
    ∫ x, f x ∂(∑ i, c i • Measure.dirac (p i)) = ∑ i, (c i).toReal • f (p i) := by
  rw [integral_finsetSum_measure (fun i _ => (integrable_dirac enorm_lt_top).smul_measure (hc i))]
  simp [integral_smul_measure, integral_dirac]

/-- Finite minimax via separation in `ℝ^ι`. -/
lemma finite_minimax {n : ℕ} {ι : Type*} [Fintype ι] (x : ι → E n) (V : E n → ℝ)
    (hVconv : ConvexOn ℝ Set.univ V) (t : ℝ) (h : ∀ z, ∃ i, t < V (x i - z)) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∀ z, t ≤ ∑ i, w i * V (x i - z) := by
  classical
  set S : Set (ι → ℝ) := {y | ∃ z, ∀ i, V (x i - z) ≤ y i} with hS
  set O : Set (ι → ℝ) := {y | ∀ i, y i < t} with hO
  have hSconv : Convex ℝ S := by
    rintro y ⟨z1, h1⟩ y' ⟨z2, h2⟩ a b ha hb hab
    refine ⟨a • z1 + b • z2, fun i => ?_⟩
    have e : x i - (a • z1 + b • z2) = a • (x i - z1) + b • (x i - z2) := by
      have hx : x i = a • x i + b • x i := by rw [← add_smul, hab, one_smul]
      conv_lhs => rw [hx]
      rw [smul_sub, smul_sub]; abel
    rw [e]
    calc V (a • (x i - z1) + b • (x i - z2)) ≤ a • V (x i - z1) + b • V (x i - z2) :=
          hVconv.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
      _ ≤ a * y i + b * y' i := by
          simp only [smul_eq_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left (h1 i) ha) (mul_le_mul_of_nonneg_left (h2 i) hb)
      _ = (a • y + b • y') i := by simp
  have hOconv : Convex ℝ O := by
    intro y hy y' hy' a b ha hb hab i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hyi := hy i; have hyi' := hy' i
    have e : a * t + b * t = t := by rw [← add_mul, hab, one_mul]
    rcases ha.eq_or_lt with ha0 | ha0
    · subst ha0; simp at hab; subst hab; simpa using hy' i
    · have h1 : a * y i < a * t := mul_lt_mul_of_pos_left hyi ha0
      have h2 : b * y' i ≤ b * t := mul_le_mul_of_nonneg_left hyi'.le hb
      linarith
  have hOopen : IsOpen O := by
    have : O = ⋂ i, {y : ι → ℝ | y i < t} := by ext y; simp [hO]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const
  have hdisj : Disjoint O S := by
    rw [Set.disjoint_left]
    rintro y hyO ⟨z, hz⟩
    obtain ⟨i, hi⟩ := h z
    have := hyO i; have := hz i; linarith
  obtain ⟨f, u, hfO, hfS⟩ := geometric_hahn_banach_open hOconv hOopen hSconv hdisj
  set c : ι → ℝ := fun i => f (fun j => if i = j then 1 else 0) with hc
  have hf : ∀ y, f y = ∑ i, c i * y i := by
    intro y
    rw [show f y = (f : (ι → ℝ) →ₗ[ℝ] ℝ) y from rfl, LinearMap.pi_apply_eq_sum_univ]
    congr 1; ext i; simp [hc, smul_eq_mul, mul_comm]
  -- a point of S
  set b0 : E n → ι → ℝ := fun z i => V (x i - z) with hb0
  have hb0S : ∀ z, b0 z ∈ S := fun z => ⟨z, fun i => le_rfl⟩
  have hcnn : ∀ j, 0 ≤ c j := by
    intro j
    by_contra hcj
    push_neg at hcj
    set M := (f (b0 0) - u + 1) / (-c j) with hM
    have hMpos : 0 < M := by
      have := hfS _ (hb0S 0); apply div_pos (by linarith) (by linarith)
    have hmem : b0 0 + M • (fun k => if j = k then (1 : ℝ) else 0) ∈ S := by
      refine ⟨0, fun i => ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hb0]
      have : 0 ≤ M * (if j = i then (1 : ℝ) else 0) := by
        split_ifs <;> simp [hMpos.le]
      linarith
    have h1 := hfS _ hmem
    rw [map_add, map_smul, smul_eq_mul] at h1
    have h2 : M * f (fun k => if j = k then (1 : ℝ) else 0) = -(f (b0 0) - u + 1) := by
      change M * c j = _
      have hne : c j ≠ 0 := hcj.ne
      rw [hM]; field_simp
    linarith
  have hsum : ∀ y, f y = ∑ i, c i * y i := hf
  set C := ∑ i, c i with hC
  have hCt : t * C ≤ u := by
    by_contra hlt
    push_neg at hlt
    have hCpos : 0 < C := by
      by_contra hC0; push_neg at hC0
      have : t * C ≤ 0 * C := by
        rcases (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hcnn i).eq_or_lt with h0 | h0
        · rw [hC, ← h0]; simp
        · linarith
      -- C ≤ 0 and C ≥ 0 so C = 0, then f = 0
      have hC0' : C = 0 := le_antisymm hC0 (Finset.sum_nonneg fun i _ => hcnn i)
      have hc0 : ∀ i, c i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hcnn i)).mp hC0' i (Finset.mem_univ i)
      have := hfS _ (hb0S 0)
      rw [hf] at this; simp [hc0] at this
      have := hfO (fun _ => t - 1) (fun i => by simp)
      rw [hf] at this; simp [hc0] at this
      linarith
    set ε := (t * C - u) / C with hε
    have hεpos : 0 < ε := div_pos (by linarith) hCpos
    have := hfO (fun _ => t - ε) (fun i => by simp; linarith)
    rw [hf] at this
    have e : ∑ i, c i * (t - ε) = (t - ε) * C := by rw [hC, Finset.mul_sum]; congr 1; ext i; ring
    rw [e] at this
    have : (t - ε) * C = u := by rw [hε]; field_simp; ring
    linarith
  have hCpos : 0 < C := by
    by_contra hC0; push_neg at hC0
    have hC0' : C = 0 := le_antisymm hC0 (Finset.sum_nonneg fun i _ => hcnn i)
    have hc0 : ∀ i, c i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hcnn i)).mp hC0' i (Finset.mem_univ i)
    have := hfS _ (hb0S 0)
    rw [hf] at this; simp [hc0] at this
    have := hfO (fun _ => t - 1) (fun i => by simp)
    rw [hf] at this; simp [hc0] at this
    linarith
  refine ⟨fun i => c i / C, fun i => div_nonneg (hcnn i) hCpos.le, ?_, fun z => ?_⟩
  · rw [← Finset.sum_div, ← hC, div_self hCpos.ne']
  · have h1 := hfS _ (hb0S z)
    rw [hf] at h1
    have e : ∑ i, c i / C * V (x i - z) = (∑ i, c i * b0 z i) / C := by
      rw [Finset.sum_div]; congr 1; ext i; simp [hb0]; ring
    rw [e, le_div_iff₀ hCpos]
    linarith

end IsodiamSolT17

open IsodiamVar.Simplex IsodiamSolT17 in
theorem solution {n : ℕ} (K : Set (E n)) (hK : IsCompact K) (hKne : K.Nonempty)
    (V : E n → ℝ) (hV0 : ∀ x, 0 ≤ V x) (hVconv : ConvexOn ℝ Set.univ V)
    (hVcoer : Coercive V) (lam : ℝ)
    (hlam : IsLeast {t : ℝ | 0 ≤ t ∧ ∃ z : E n, ∀ x ∈ K, V (x + z) ≤ t} lam) :
    IsLUB {s : ℝ | ∃ μ : Measure (E n), InP K μ ∧ s = varV V μ} lam ∧
      ∀ μ : Measure (E n), InP K μ →
        (varV V μ = lam ↔
          ∃ zs : E n, IsMinOn (fun z => ∫ x, V (x - z) ∂μ) Set.univ zs ∧
            μ.support ⊆ {x | V (x - zs) = lam}) := by
  classical
  have hVc : Continuous V := continuousOn_univ.mp (hVconv.continuousOn isOpen_univ)
  obtain ⟨hlam0, z0, hz0⟩ := hlam.1
  -- integrability for measures carried by K
  have hint : ∀ μ : Measure (E n), InP K μ → ∀ z, Integrable (fun x => V (x - z)) μ := by
    intro μ hμ z
    have := hμ.1
    have hcont : Continuous (fun x => V (x - z)) := hVc.comp (continuous_id.sub continuous_const)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine Integrable.mono' (integrable_const C) hcont.aestronglyMeasurable ?_
    filter_upwards [ae_iff.mpr hμ.2] with x hx using hC x hx
  have hbdd : ∀ μ : Measure (E n), BddBelow (Set.range fun z => ∫ x, V (x - z) ∂μ) :=
    fun μ => ⟨0, by rintro _ ⟨z, rfl⟩; exact integral_nonneg fun x => hV0 _⟩
  have hvarle : ∀ μ : Measure (E n), ∀ z, varV V μ ≤ ∫ x, V (x - z) ∂μ :=
    fun μ z => ciInf_le (hbdd μ) z
  have hvarnn : ∀ μ : Measure (E n), 0 ≤ varV V μ := by
    intro μ
    by_cases hne : Nonempty (E n)
    · exact le_ciInf fun z => integral_nonneg fun x => hV0 _
    · exact absurd ⟨0⟩ hne
  -- value at the λ-center
  have hcenter : ∀ μ : Measure (E n), InP K μ → ∫ x, V (x - -z0) ∂μ ≤ lam := by
    intro μ hμ
    have := hμ.1
    have : ∫ x, V (x - -z0) ∂μ ≤ ∫ _x, lam ∂μ := by
      apply integral_mono_ae (hint μ hμ _) (integrable_const _)
      filter_upwards [ae_iff.mpr hμ.2] with x hx
      rw [sub_neg_eq_add]; exact hz0 x hx
    simpa using this
  -- lower bound: for every `0 ≤ t < lam`, some measure has variance at least `t`
  have hlower : ∀ t, 0 ≤ t → t < lam → ∃ μ : Measure (E n), InP K μ ∧ t ≤ varV V μ := by
    intro t ht0 htl
    have h0 : ∀ z, ∃ x ∈ K, t < V (x - z) := by
      intro z
      by_contra hcon
      push_neg at hcon
      have : lam ≤ t := hlam.2 ⟨ht0, -z, fun x hx => by rw [← sub_eq_add_neg]; exact hcon x hx⟩
      linarith
    obtain ⟨x0, hx0⟩ := hKne
    set s : Set (E n) := {z | V (x0 - z) ≤ t} with hs
    have hscpt : IsCompact s := by
      have : s = (fun y => x0 - y) '' {y | V y ≤ t} := by
        ext z; simp only [hs, Set.mem_setOf_eq, Set.mem_image]
        constructor
        · intro hz; exact ⟨x0 - z, hz, by abel⟩
        · rintro ⟨y, hy, rfl⟩; simpa using hy
      rw [this]
      exact (hVcoer t ht0).image (continuous_const.sub continuous_id)
    set T : K → Set (E n) := fun x => {z | V (x.1 - z) ≤ t} with hT
    have hTc : ∀ x, IsClosed (T x) := fun x =>
      isClosed_le (hVc.comp (continuous_const.sub continuous_id)) continuous_const
    have hst : s ∩ ⋂ x, T x = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ hall
      obtain ⟨x, hx, hxt⟩ := h0 z
      have := hall ⟨x, hx⟩
      simp only [hT, Set.mem_setOf_eq] at this
      linarith
    obtain ⟨u, hu⟩ := hscpt.elim_finite_subfamily_closed T hTc hst
    -- finite family of points
    set pts : Option u → E n := fun o => match o with
      | none => x0
      | some i => i.1.1 with hpts
    have hptsK : ∀ o, pts o ∈ K := by
      rintro (_ | i)
      · exact hx0
      · exact i.1.2
    have hfam : ∀ z, ∃ o, t < V (pts o - z) := by
      intro z
      by_contra hcon
      push_neg at hcon
      have : z ∈ s ∩ ⋂ i ∈ u, T i := by
        refine ⟨hcon none, ?_⟩
        simp only [Set.mem_iInter]
        intro i hi
        exact hcon (some ⟨i, hi⟩)
      rw [hu] at this; exact this
    obtain ⟨w, hwnn, hw1, hwt⟩ := finite_minimax pts V hVconv t hfam
    set μ : Measure (E n) := ∑ o, ENNReal.ofReal (w o) • Measure.dirac (pts o) with hμ
    have hμK : InP K μ := by
      refine ⟨⟨?_⟩, ?_⟩
      · rw [hμ, Measure.coe_finsetSum, Finset.sum_apply]
        simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ => hwnn o), hw1, ENNReal.ofReal_one]
      · rw [hμ, Measure.coe_finsetSum, Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro o _
        rw [Measure.smul_apply, Measure.dirac_apply' _ hK.isClosed.measurableSet.compl,
          Set.indicator_of_notMem (by simpa using hptsK o)]
        simp
    refine ⟨μ, hμK, le_ciInf fun z => ?_⟩
    rw [hμ, integral_sum_dirac _ (fun o => ENNReal.ofReal_ne_top) pts (fun x => V (x - z))]
    simp only [ENNReal.toReal_ofReal (hwnn _), smul_eq_mul]
    exact hwt z
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨μ, hμ, rfl⟩
    exact (hvarle μ _).trans (hcenter μ hμ)
  · intro b hb
    by_contra hlt
    push_neg at hlt
    obtain ⟨x0, hx0⟩ := hKne
    by_cases hb0 : b < 0
    · have hμK : InP K (Measure.dirac x0) := ⟨inferInstance, by
        rw [Measure.dirac_apply' _ hK.isClosed.measurableSet.compl,
          Set.indicator_of_notMem (by simpa using hx0)]⟩
      have := hb ⟨_, hμK, rfl⟩
      have := hvarnn (Measure.dirac x0)
      linarith
    · push_neg at hb0
      obtain ⟨μ, hμ, ht⟩ := hlower ((b + lam) / 2) (by linarith) (by linarith)
      have := hb ⟨_, hμ, rfl⟩
      linarith
  · intro μ hμ
    have := hμ.1
    constructor
    · intro heq
      refine ⟨-z0, ?_, ?_⟩
      · intro z _
        simp only [Set.mem_setOf_eq]
        have h1 := hvarle μ (-z0)
        have h2 := hcenter μ hμ
        have h3 := hvarle μ z
        linarith
      · have hFc : ∫ x, V (x - -z0) ∂μ = lam :=
          le_antisymm (hcenter μ hμ) (heq ▸ hvarle μ (-z0))
        have hnn : 0 ≤ᵐ[μ] fun x => lam - V (x - -z0) := by
          filter_upwards [ae_iff.mpr hμ.2] with x hx
          simp only [Pi.zero_apply, sub_neg_eq_add]
          linarith [hz0 x hx]
        have hi : Integrable (fun x => lam - V (x - -z0)) μ :=
          (integrable_const _).sub (hint μ hμ _)
        have h0 : ∫ x, (lam - V (x - -z0)) ∂μ = 0 := by
          rw [integral_sub (integrable_const _) (hint μ hμ _), hFc]; simp
        have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hi).mp h0
        apply Measure.support_subset_of_isClosed
        · exact isClosed_eq (hVc.comp (continuous_id.sub continuous_const)) continuous_const
        · filter_upwards [hae] with x hx
          simp only [Pi.zero_apply] at hx
          show V (x - -z0) = lam
          linarith
    · rintro ⟨zs, hmin, hsupp⟩
      have hvar : varV V μ = ∫ x, V (x - zs) ∂μ :=
        le_antisymm (hvarle μ zs) (le_ciInf fun z => hmin (Set.mem_univ z))
      rw [hvar]
      have : ∫ x, V (x - zs) ∂μ = ∫ _x, lam ∂μ := by
        apply integral_congr_ae
        filter_upwards [Measure.support_mem_ae] with x hx
        exact hsupp hx
      rw [this]; simp
