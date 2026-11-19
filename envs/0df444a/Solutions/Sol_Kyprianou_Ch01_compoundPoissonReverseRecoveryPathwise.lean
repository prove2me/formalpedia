-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonReverseRecoveryPathwise
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:25:36.79962+00:00
-- url     : https://prove2.me/submissions/b7032775-901e-4a00-ac1f-2e1882d581ae

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Order.WithBot
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open Kyprianou.Ch01 MeasureTheory Set Filter
set_option autoImplicit false

theorem solution
    {Ω : Type*} (X : NNReal → Ω → ℤ) (ω : Ω)
    (hcadlag : ∀ t : NNReal,
      Tendsto (fun s : NNReal => X s ω)
        (nhdsWithin t (Set.Ici t)) (nhds (X t ω)))
    (hlocalint : ∀ t : NNReal,
      IntervalIntegrable
        (fun s : ℝ =>
          if 0 < X (Real.toNNReal s) ω then
            1 / (X (Real.toNNReal s) ω : ℝ)
          else 0)
        volume 0 (t : ℝ)) :
    ∀ t : NNReal,
      (∀ s : NNReal, s ≤ t → 0 < X s ω) →
        compoundPoissonToBranching X
          (Real.toNNReal (reciprocalOccupation X t ω).toReal) ω = X t ω := by
  intro t hpos
  set f : ℝ → ENNReal := fun s => (ENNReal.ofReal (X (Real.toNNReal s) ω : ℝ))⁻¹ with hf
  set I : NNReal → ENNReal := fun s => reciprocalOccupation X s ω with hI
  have hIdef : ∀ s : NNReal, I s = ∫⁻ x in Ioc (0 : ℝ) (s : ℝ), f x := fun s => rfl
  -- finiteness of I t
  have hfin : I t ≠ ⊤ := by
    rw [hIdef]
    set g : ℝ → ℝ := fun s => if 0 < X (Real.toNNReal s) ω then
        1 / (X (Real.toNNReal s) ω : ℝ) else 0 with hg
    have hint : IntegrableOn g (Ioc (0 : ℝ) (t : ℝ)) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le t.2).mp (hlocalint t)
    have heq : ∀ x ∈ Ioc (0 : ℝ) (t : ℝ), f x = ‖g x‖ₑ := by
      intro x hx
      have hxt : Real.toNNReal x ≤ t := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hx.1.le]; exact hx.2
      have hX := hpos _ hxt
      have hXr : (0 : ℝ) < (X (Real.toNNReal x) ω : ℝ) := by exact_mod_cast hX
      simp only [hf, hg, if_pos hX]
      rw [one_div, Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr hXr),
        ENNReal.ofReal_inv_of_pos hXr]
    rw [setLIntegral_congr_fun measurableSet_Ioc heq]
    exact (hint.2).ne
  -- integer right-continuity
  obtain ⟨v, hv, hIco⟩ := (mem_nhdsGE_iff_exists_Ico_subset).mp
    (hcadlag t (isOpen_discrete {X t ω} |>.mem_nhds rfl))
  have hconst : ∀ s : NNReal, t ≤ s → s < v → X s ω = X t ω := fun s h1 h2 => hIco ⟨h1, h2⟩
  have hXt : (0 : ℝ) < (X t ω : ℝ) := by exact_mod_cast hpos t le_rfl
  have hstrict : ∀ s : NNReal, t < s → I t < I s := by
    intro s hts
    obtain ⟨s1, hs1, hs1v⟩ := exists_between (lt_min hts (show t < v from hv))
    have hsplit : I s = I t + ∫⁻ x in Ioc (t : ℝ) (s : ℝ), f x := by
      rw [hIdef, hIdef, ← Ioc_union_Ioc_eq_Ioc t.2 (by exact_mod_cast hts.le),
        lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]
      rfl
    have hlow : (ENNReal.ofReal (X t ω : ℝ))⁻¹ * ENNReal.ofReal ((s1 : ℝ) - t) ≤
        ∫⁻ x in Ioc (t : ℝ) (s : ℝ), f x := by
      have hsub : Ioc (t : ℝ) (s1 : ℝ) ⊆ Ioc (t : ℝ) (s : ℝ) :=
        Ioc_subset_Ioc_right (by exact_mod_cast (hs1v.le.trans (min_le_left _ _)))
      refine le_trans ?_ (lintegral_mono_set hsub)
      have hc : ∀ x ∈ Ioc (t : ℝ) (s1 : ℝ), f x = (ENNReal.ofReal (X t ω : ℝ))⁻¹ := by
        intro x hx
        have hx0 : (0 : ℝ) ≤ x := le_trans t.2 hx.1.le
        have h1 : t ≤ Real.toNNReal x := by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hx0]; exact hx.1.le
        have h2 : Real.toNNReal x < v := by
          have : Real.toNNReal x ≤ s1 := by
            rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hx0]; exact hx.2
          exact lt_of_le_of_lt this (lt_of_lt_of_le hs1v (min_le_right _ _))
        simp only [hf, hconst _ h1 h2]
      rw [setLIntegral_congr_fun measurableSet_Ioc hc, setLIntegral_const, Real.volume_Ioc]
    have hposint : 0 < (ENNReal.ofReal (X t ω : ℝ))⁻¹ * ENNReal.ofReal ((s1 : ℝ) - t) := by
      apply ENNReal.mul_pos
      · exact ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
      · have : (t : ℝ) < s1 := by exact_mod_cast hs1
        exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    rw [hsplit]
    exact ENNReal.lt_add_right hfin (lt_of_lt_of_le hposint hlow).ne'
  have hmono : ∀ s : NNReal, s ≤ t → I s ≤ I t := by
    intro s hs
    rw [hIdef, hIdef]
    exact lintegral_mono_set (Ioc_subset_Ioc_right (by exact_mod_cast hs))
  have hu : (((Real.toNNReal (reciprocalOccupation X t ω).toReal) : NNReal) : ENNReal) = I t := by
    show ENNReal.ofReal (I t).toReal = I t
    exact ENNReal.ofReal_toReal hfin
  have hset : {s : NNReal | (((Real.toNNReal (reciprocalOccupation X t ω).toReal) : NNReal) : ENNReal) <
      reciprocalOccupation X s ω} = Ioi t := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_Ioi, hu]
    constructor
    · intro h
      by_contra hc
      exact absurd (hmono s (not_lt.mp hc)) (not_le.mpr h)
    · exact hstrict s
  have hinv : inverseReciprocalOccupation X (Real.toNNReal (reciprocalOccupation X t ω).toReal) ω =
      ((t : NNReal) : WithTop NNReal) := by
    unfold inverseReciprocalOccupation
    have hex : ∃ s : NNReal, (((Real.toNNReal (reciprocalOccupation X t ω).toReal) : NNReal) : ENNReal) <
        reciprocalOccupation X s ω := ⟨t + 1, by rw [hu]; exact hstrict _ (by simp)⟩
    simp only [hex, if_true]
    rw [hset, csInf_Ioi]
  have hfnp : ((t : NNReal) : WithTop NNReal) ≤ firstNegativePassage X ω := by
    unfold firstNegativePassage
    split_ifs with h
    · obtain ⟨u, hu'⟩ := h
      apply WithTop.coe_le_coe.mpr
      apply le_csInf ⟨u, hu'⟩
      rintro s ⟨-, hs⟩
      by_contra hlt0
      have hlt := not_le.mp hlt0
      exact absurd (hpos s hlt.le) (not_lt.mpr hs.le)
    · exact le_top
  unfold compoundPoissonToBranching
  rw [hinv, min_eq_left hfnp]
