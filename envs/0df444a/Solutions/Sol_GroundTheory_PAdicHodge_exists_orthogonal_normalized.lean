-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_orthogonal_normalized
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:50:08.547704+00:00
-- url     : https://prove2.me/submissions/b8501732-7528-41b3-acd2-5f2e1814c148

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_OrthoBasis
import Definitions.Def_GroundTheory_PAdicHodge_UntiltIndep
import Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_mem_Ioc
import Theorems.Thm_GroundTheory_PAdicHodge_exists_orthogonal_of_linearIndependent
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ι : Type*} [Fintype ι] {v : ι → C♭}
    (hv : LinearIndependent K♭ v) {t r : ℝ} (ht : t < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ w : ι → C♭, LinearIndependent K♭ w ∧ (∀ i, w i ∈ Submodule.span K♭ (Set.range v)) ∧
      (∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖) ∧
      ∀ i, ‖w i‖ ≤ 1 ∧ r < ‖w i‖ := by
  obtain ⟨w', hli, hspan, horth⟩ := exists_orthogonal_of_linearIndependent hv ht
  have hw'0 : ∀ i, 0 < ‖w' i‖ := fun i => norm_pos_iff.2 (hli.ne_zero i)
  have hE : ∀ i, ∃ e : K♭, r / ‖w' i‖ < ‖e‖ ∧ ‖e‖ ≤ 1 / ‖w' i‖ := fun i =>
    exists_norm_mem_Ioc p (div_pos hr0 (hw'0 i)) (div_lt_div_of_pos_right hr1 (hw'0 i))
  choose e he1 he2 using hE
  have he0 : ∀ i, e i ≠ 0 := fun i => norm_pos_iff.1 ((div_pos hr0 (hw'0 i)).trans (he1 i))
  have hsmul : ∀ c : ι → K♭, ∑ j, c j • (e j • w' j) = ∑ j, (c j * e j) • w' j := fun c => by
    simp only [mul_smul]
  refine ⟨fun i => e i • w' i, ?_, fun i => Submodule.smul_mem _ _ (hspan i), ?_, fun i => ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [hsmul] at hg
    have := (Fintype.linearIndependent_iff.1 hli) _ hg i
    exact (mul_eq_zero.1 this).resolve_right (he0 i)
  · intro c i
    rw [hsmul, ← mul_smul]
    exact horth (fun j => c j * e j) i
  · rw [norm_smul]
    constructor
    · calc ‖e i‖ * ‖w' i‖ ≤ 1 / ‖w' i‖ * ‖w' i‖ := by gcongr; exact he2 i
        _ = 1 := one_div_mul_cancel (hw'0 i).ne'
    · calc r = r / ‖w' i‖ * ‖w' i‖ := (div_mul_cancel₀ r (hw'0 i).ne').symm
        _ < ‖e i‖ * ‖w' i‖ := mul_lt_mul_of_pos_right (he1 i) (hw'0 i)
end GroundTheory.PAdicHodge
