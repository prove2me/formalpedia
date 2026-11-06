-- Prove2me | solution 1 for OAI.FourierBridge.exists_complex_smooth_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:30:34.914785+00:00
-- url     : https://prove2.me/submissions/bb73f161-9583-4332-8217-122f8da8dc2a

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open scoped ContDiff Manifold
open OAI.FourierBridge
namespace OAI.FourierBridge
theorem _root_.solution (T : ℝ) (hT : 0 ≤ T) :
    ∃ V : ℝ → ℂ,
      HasCompactSupport V ∧
      ContDiff ℝ ∞ V ∧
      (∀ s, |s| ≤ T → V s = 1) ∧
      tsupport V ⊆ Set.Icc (-(T + 1)) (T + 1) ∧
      V 0 = 1 := by
  let U : Set ℝ := Set.Ioo (-(T + 1)) (T + 1)
  let K : Set ℝ := Set.Icc (-T) T
  have hU : IsOpen U := isOpen_Ioo
  have hK : IsClosed K := isClosed_Icc
  have hKU : K ⊆ U := by
    intro s hs
    rcases hs with ⟨hleft, hright⟩
    constructor <;> linarith
  obtain ⟨f, hf, _, hsupport, hone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (I := 𝓘(ℝ)) (n := ⊤) hU hK hKU
  let V : ℝ → ℂ := fun s => (f s : ℂ)
  have hf' : ContDiff ℝ ∞ f := by simpa only [contMDiff_iff_contDiff] using hf
  have hVs : ContDiff ℝ ∞ V := Complex.ofRealCLM.contDiff.comp hf'
  have hVsupport : Function.support V = Function.support f := by
    ext s
    simp [V, Function.mem_support]
  have hVsupportI : Function.support V ⊆
      Set.Icc (-(T + 1)) (T + 1) := by
    intro s hs
    rw [hVsupport, hsupport] at hs
    exact ⟨hs.1.le, hs.2.le⟩
  have hVtsupportI : tsupport V ⊆
      Set.Icc (-(T + 1)) (T + 1) :=
    closure_minimal hVsupportI isClosed_Icc
  have hVc : HasCompactSupport V :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hVsupportI
  have hone' : ∀ s, |s| ≤ T → V s = 1 := by
    intro s hs
    have hsK : s ∈ K := by simpa [K, abs_le] using hs
    have hfs : f s = 1 := (hone s).mp hsK
    simp [V, hfs]
  exact ⟨V, hVc, hVs, hone', hVtsupportI,
    hone' 0 (by simpa using hT)⟩
end OAI.FourierBridge
