-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SDPadic.exists_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:26:42.56097+00:00
-- url     : https://prove2.me/submissions/a0640730-d48c-4e23-b7d3-87abeac555bf

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_IndicatorInSchrodingerSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_SDPadic_trunc
import Theorems.Thm_GlobalTheory_JR_AbsInv_exists_selfDual
import Theorems.Thm_GlobalTheory_JR_AbsInv_fourB_fourB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU Filter Topology
namespace GlobalTheory.CompanionTheory.SDPadic
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (χ : V → V → ℂ) (L : ℤ → AddSubgroup V) (D : ℤ → AddSubgroup V), (∀ x x' y, χ (x + x') y = χ x y * χ x' y) → (∀ x y, χ x y = χ y x) → (∀ x y, ‖χ x y‖ = 1) → Continuous (fun p : V × V => χ p.1 p.2) → (∀ n, IsOpen (L n : Set V) ∧ IsCompact (L n : Set V) ∧ IsOpen (D n : Set V) ∧ IsCompact (D n : Set V)) → Antitone L → (∀ U ∈ nhds (0 : V), ∃ n, (L n : Set V) ⊆ U) → (∀ x, ∃ n, x ∈ L n) → (∀ x, ∃ n, x ∈ D n) → (∀ n y, y ∈ D n ↔ ∀ x ∈ L n, χ x y = 1) → (∀ n x, x ∈ L n ↔ ∀ y ∈ D n, χ x y = 1) → ∃ μ : Measure V, SelfDual μ χ := by
  intro V _ _ _ _ _ _ _ _ χ L D ha hs hn hB hLD hanti hsm _ hDall hD hL
  classical
  obtain ⟨μ, hμ, hinv⟩ := GlobalTheory.JR.AbsInv.exists_selfDual χ hB hs ha (fun U hU => by
    obtain ⟨n, hn⟩ := hsm U hU
    exact ⟨L n, D n, hn, (hLD n).1, (hLD n).2.1, (hLD n).2.2.1, (hLD n).2.2.2, hD n, hL n⟩)
  have hone : ∀ n, μ.real (L n) * μ.real (D n) = 1 := by
    intro n
    set f : V → ℂ := (L n : Set V).indicator (fun _ => 1) with hf
    have hcl : IsClopen (L n : Set V) := ⟨(hLD n).2.1.isClosed, (hLD n).1⟩
    have hfc : Continuous f := hcl.continuous_indicator continuous_const
    have hfs : HasCompactSupport f :=
      HasCompactSupport.intro (hLD n).2.1 fun x hx => by simp [hf, Set.indicator_of_notMem hx]
    have hfi : ∀ x, ∀ m ∈ L n, f (x + m) = f x := by
      intro x m hm
      by_cases hx : x ∈ L n
      · simp [hf, hx, (L n).add_mem hx hm]
      · have : x + m ∉ L n := fun h => hx (by simpa using (L n).sub_mem h hm)
        simp [hf, hx, this]
    have hfl : IsLocallyConstant f := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      have : (fun y => y - x) ⁻¹' (L n : Set V) ∈ 𝓝 x :=
        ((hLD n).1.preimage (by fun_prop)).mem_nhds (by simp)
      filter_upwards [this] with y hy
      have := hfi x _ hy
      simpa using this
    have e1 := GlobalTheory.JR.AbsInv.fourB_fourB μ χ hB hs ha (L n) (D n) (hLD n).1 (hLD n).2.2.1 (hLD n).2.2.2
      (hD n) (hL n) f hfc hfs hfi 0
    rw [hinv f ⟨hfl, hfs⟩ 0] at e1
    have e3 : f (-0) = 1 := by simp [hf]
    rw [e3, mul_one] at e1
    exact_mod_cast e1.symm
  refine ⟨μ, hμ, fun Φ hΦ hΦc hint z => ?_⟩
  have hmono : Monotone (fun n => (D n : Set V)) := by
    intro m n hmn y hy
    exact (hD n y).2 fun x hx => (hD m y).1 hy x (hanti hmn hx)
  have hU : (⋃ n, (D n : Set V)) = Set.univ := by
    ext x; simpa using hDall x
  have hg : Integrable (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y z) μ := by
    refine hint.mul_bdd (c := 1) ?_ (Eventually.of_forall fun y => (hn y z).le)
    exact (hB.comp (f := fun y : V => (y, z)) (by fun_prop)).aestronglyMeasurable
  have t1 := tendsto_setIntegral_of_monotone (μ := μ) (fun n => (hLD n).2.2.1.measurableSet) hmono
    (f := fun y => (∫ x, Φ x * χ x y ∂μ) * χ y z) (by rw [hU]; exact hg.integrableOn)
  rw [hU, Measure.restrict_univ] at t1
  refine tendsto_nhds_unique t1 ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hc : Continuous fun u : V => Φ (u - z) := hΦ.comp (by fun_prop)
  have hnh : {u : V | ‖Φ (u - z) - Φ (-z)‖ < ε / 2} ∈ 𝓝 (0 : V) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hε)
  obtain ⟨n0, hn0⟩ := hsm _ hnh
  refine ⟨n0, fun n hnn => ?_⟩
  rw [GlobalTheory.CompanionTheory.SDPadic.trunc μ χ hB hs ha (L n) (D n) (hLD n).1 (hLD n).2.2.1 (hLD n).2.2.2 (hL n) Φ hΦ hΦc z,
    dist_eq_norm]
  have hfin : μ (L n) < ⊤ := (hLD n).2.1.measure_lt_top
  have e : ∫ u in (L n : Set V), (μ.real (D n) : ℂ) * Φ (u - z) ∂μ - Φ (-z)
      = ∫ u in (L n : Set V), (μ.real (D n) : ℂ) * (Φ (u - z) - Φ (-z)) ∂μ := by
    simp_rw [mul_sub]
    rw [integral_sub ((by fun_prop : Continuous fun u : V => (μ.real (D n) : ℂ) * Φ (u - z)).continuousOn.integrableOn_compact
        (hLD n).2.1)
      (continuous_const.continuousOn.integrableOn_compact (hLD n).2.1), setIntegral_const,
      Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hone n]
    simp
  rw [e]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := (L n : Set V)) (C := μ.real (D n) * (ε / 2))
    (f := fun u => (μ.real (D n) : ℂ) * (Φ (u - z) - Φ (-z))) hfin (fun u hu => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg]
      exact mul_le_mul_of_nonneg_left (le_of_lt (hn0 (hanti hnn hu))) measureReal_nonneg)
  refine lt_of_le_of_lt hb ?_
  have := hone n
  calc μ.real (D n) * (ε / 2) * μ.real (L n) = (μ.real (L n) * μ.real (D n)) * (ε / 2) := by ring
    _ < ε := by rw [this]; linarith
end GlobalTheory.CompanionTheory.SDPadic
