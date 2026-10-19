-- Prove2me | solution 1 for OAI.KervaireScalarPhase.tendsto_smoothPhase_cut
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:46:57.761927+00:00
-- url     : https://prove2.me/submissions/7960b2d6-5dc2-47a5-bf26-40fae6d9527e

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/ScalarPhase.lean:L151-L188
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireScalarPhase.tendsto_smoothPhase_cut. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Theorems.Thm_OAI_KervaireScalarPhase_phase_eq_arg_one_sub

-- ---- from OAI.GroupTheory.Kervaire.ScalarPhase ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireScalarPhase

theorem re_one_sub_pos {z : ℂ} (hz : ‖z‖ = 1) (hz' : z ≠ 1) :
    0 < (1-z).re := by
  have hn : z.re ^ 2 + z.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, hz, pow_two] using Complex.normSq_eq_norm_sq z
  have hl : z.re ≤ 1 := (Complex.re_le_norm z).trans_eq hz
  have hne : z.re ≠ 1 := by
    intro h
    have hi : z.im = 0 := by nlinarith [sq_nonneg z.im]
    exact hz' (Complex.ext h hi)
  simpa using sub_pos.mpr (lt_of_le_of_ne hl hne)

/-- The tangential limit agrees with the discontinuous phase, also at one. -/
theorem tendsto_smoothPhase_cut {z : ℂ} (hz : ‖z‖ = 1) :
    Tendsto (fun ε : ℝ => smoothPhase (cutApproach ε) z)
      (𝓝[>] 0) (𝓝 (phase z)) := by
  have hc : Continuous cutApproach := by unfold cutApproach; fun_prop
  have hca : Tendsto cutApproach (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa [cutApproach] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  by_cases hz' : z = 1
  · subst z
    have ha : Tendsto (fun ε : ℝ => (ε : ℂ) - Complex.I)
        (𝓝[>] 0) (𝓝 (-Complex.I)) := by
      have hcont : Continuous (fun ε : ℝ => (ε : ℂ) - Complex.I) := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hs : -Complex.I ∈ Complex.slitPlane := by
      simp [Complex.mem_slitPlane_iff]
    have ht := (Complex.continuousAt_arg hs).tendsto.comp ha
    have he : (fun ε : ℝ => (1 - cutApproach ε).arg) =ᶠ[𝓝[>] 0]
        (fun ε => ((ε : ℂ) - Complex.I).arg) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [show 1 - cutApproach ε = (ε : ℂ) * ((ε : ℂ) - Complex.I) by
        unfold cutApproach; push_cast; ring]
      exact Complex.arg_real_mul _ hε
    have ht' := ht.congr' he.symm
    have heq : (1/2 : ℝ) + (-Complex.I).arg / Real.pi = 0 := by
      rw [Complex.arg_neg_I]
      field_simp
      norm_num
    have htt := (ht'.div_const Real.pi).const_add (1/2 : ℝ)
    rw [heq] at htt
    simpa [smoothPhase] using htt
  · have hs : 1-z ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (re_one_sub_pos hz hz'))
    have hm : Tendsto (fun ε : ℝ => cutApproach ε * z) (𝓝[>] 0) (𝓝 z) := by
      simpa using hca.mul_const z
    have ht := (Complex.continuousAt_arg hs).tendsto.comp
      (tendsto_const_nhds.sub hm)
    simpa [smoothPhase, phase_eq_arg_one_sub hz hz'] using
      (ht.div_const Real.pi).const_add (1/2 : ℝ)

end KervaireScalarPhase

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireScalarPhase
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.KervaireScalarPhase.tendsto_smoothPhase_cut := @_root_.OAI.KervaireScalarPhase.tendsto_smoothPhase_cut
