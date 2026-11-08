-- Prove2me | solution 1 for ImpactCopula.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:56:21.28214+00:00
-- url     : https://prove2.me/submissions/5785120d-fa9a-4c2c-b77b-66d12c8036d4

import Mathlib
import Definitions.Def_actuarial_coIsCopula
import Definitions.Def_ImpactCopula_diniRightUpper
import Definitions.Def_ImpactCopula_diniLeftUpper

open Filter Topology

namespace Aux_ImpactCopula_l1

lemma limsup_mono_of {f g : ℝ → ℝ} (s : Set ℝ) (hs : s ∈ 𝓝[>] (0 : ℝ))
    (hfg : ∀ h ∈ s, f h ≤ g h) (hf0 : ∀ h ∈ s, 0 ≤ f h) (hg1 : ∀ h ∈ s, g h ≤ 1) :
    Filter.limsup f (𝓝[>] 0) ≤ Filter.limsup g (𝓝[>] 0) := by
  apply Filter.limsup_le_limsup
  · exact Filter.eventually_of_mem hs (fun h hh => hfg h hh)
  · exact IsBoundedUnder.isCoboundedUnder_le
      (isBoundedUnder_of_eventually_ge (Filter.eventually_of_mem hs (fun h hh => hf0 h hh)))
  · exact isBoundedUnder_of_eventually_le (Filter.eventually_of_mem hs (fun h hh => hg1 h hh))

end Aux_ImpactCopula_l1

open ActuarialValuation ImpactCopula Aux_ImpactCopula_l1 in
theorem solution (C : ℝ → ℝ → ℝ) (hC : ActuarialValuation.coIsCopula C) (u : ℝ)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    MonotoneOn (fun v => diniRightUpper C u v) (Set.Icc 0 1) ∧
      MonotoneOn (fun v => diniLeftUpper C u v) (Set.Icc 0 1) := by
  obtain ⟨hbd, hrect⟩ := hC
  obtain ⟨hu0, hu1⟩ := hu
  constructor
  · intro v hv v' hv' hvv'
    simp only [diniRightUpper]
    have hs : Set.Ioo (0 : ℝ) (1 - u) ∈ 𝓝[>] (0 : ℝ) :=
      Ioo_mem_nhdsGT (by linarith)
    apply limsup_mono_of (Set.Ioo (0 : ℝ) (1 - u)) hs
    · intro h hh
      obtain ⟨h0, h1⟩ := hh
      have := hrect u (u + h) v v' hu0.le (by linarith) (by linarith) hv.1 hvv' hv'.2
      unfold coRectangle at this
      rw [div_le_div_iff_of_pos_right h0]
      linarith
    · intro h hh
      obtain ⟨h0, h1⟩ := hh
      have := hrect u (u + h) 0 v hu0.le (by linarith) (by linarith) le_rfl hv.1 hv.2
      unfold coRectangle at this
      have e1 := (hbd (u + h) (by linarith) (by linarith)).1
      have e2 := (hbd u hu0.le hu1.le).1
      apply div_nonneg _ h0.le
      linarith
    · intro h hh
      obtain ⟨h0, h1⟩ := hh
      have := hrect u (u + h) v' 1 hu0.le (by linarith) (by linarith) hv'.1 hv'.2 le_rfl
      unfold coRectangle at this
      have e1 := (hbd (u + h) (by linarith) (by linarith)).2.2.1
      have e2 := (hbd u hu0.le hu1.le).2.2.1
      rw [div_le_one h0]
      linarith
  · intro v hv v' hv' hvv'
    simp only [diniLeftUpper]
    have hs : Set.Ioo (0 : ℝ) u ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hu0
    apply limsup_mono_of (Set.Ioo (0 : ℝ) u) hs
    · intro h hh
      obtain ⟨h0, h1⟩ := hh
      have := hrect (u - h) u v v' (by linarith) (by linarith) hu1.le hv.1 hvv' hv'.2
      unfold coRectangle at this
      rw [div_le_div_iff_of_pos_right h0]
      linarith
    · intro h hh
      obtain ⟨h0, h1⟩ := hh
      have := hrect (u - h) u 0 v (by linarith) (by linarith) hu1.le le_rfl hv.1 hv.2
      unfold coRectangle at this
      have e1 := (hbd (u - h) (by linarith) (by linarith)).1
      have e2 := (hbd u hu0.le hu1.le).1
      apply div_nonneg _ h0.le
      linarith
    · intro h hh
      obtain ⟨h0, h1⟩ := hh
      have := hrect (u - h) u v' 1 (by linarith) (by linarith) hu1.le hv'.1 hv'.2 le_rfl
      unfold coRectangle at this
      have e1 := (hbd (u - h) (by linarith) (by linarith)).2.2.1
      have e2 := (hbd u hu0.le hu1.le).2.2.1
      rw [div_le_one h0]
      linarith
