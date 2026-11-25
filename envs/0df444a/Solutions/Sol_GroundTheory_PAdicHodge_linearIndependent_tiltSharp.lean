-- Prove2me | solution 1 for GroundTheory.PAdicHodge.linearIndependent_tiltSharp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:57:15.446479+00:00
-- url     : https://prove2.me/submissions/42c0e1c2-e130-4bf3-9515-65054368b268

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_OrthoBasis
import Definitions.Def_GroundTheory_PAdicHodge_UntiltIndep
import Theorems.Thm_GroundTheory_PAdicHodge_mul_norm_le_norm_sum_smul_tiltSharp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {ι : Type*} [Fintype ι] {w : ι → C♭} {t r ρ : ℝ}
    (hw : ∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖)
    (hw1 : ∀ i, ‖w i‖ ≤ 1) (hwr : ∀ i, r < ‖w i‖) (ht : 0 < t) (hr : 0 < r) (hρ : 0 < ρ)
    (hρ1 : ρ < 1) (hp : ‖(p : K)‖ ≤ t * r * ρ) :
    LinearIndependent K (fun i => tiltSharp C p (w i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := mul_norm_le_norm_sum_smul_tiltSharp (C := C) hw hw1 hwr ht hr.le hρ hρ1 hp g i
  rw [hg, norm_zero] at h
  have hpos : 0 < t * r * ρ := by positivity
  have : ‖g i‖ ≤ 0 := by nlinarith [norm_nonneg (g i)]
  exact norm_le_zero_iff.1 this
end GroundTheory.PAdicHodge
