-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_tiltSharp_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:59:56.250643+00:00
-- url     : https://prove2.me/submissions/9a58c571-f923-4e8d-943d-1ff8644ade4d

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_OrthoBasis
import Definitions.Def_GroundTheory_PAdicHodge_UntiltIndep
import Theorems.Thm_GroundTheory_PAdicHodge_exists_lt_mul_mul_lt_one
import Theorems.Thm_GroundTheory_PAdicHodge_mul_norm_le_norm_sum_smul_tiltSharp
import Theorems.Thm_GroundTheory_PAdicHodge_exists_orthogonal_normalized

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
theorem _root_.solution {ι : Type*} [Fintype ι] {v : ι → C♭}
    (hv : LinearIndependent K♭ v) :
    ∃ (w : ι → C♭) (t r ρ : ℝ), 0 < t ∧ t < 1 ∧ 0 < r ∧ r < 1 ∧ 0 < ρ ∧ ρ < 1 ∧
      ‖(p : K)‖ ≤ t * r * ρ ∧ LinearIndependent K♭ w ∧
      (∀ i, w i ∈ Submodule.span K♭ (Set.range v)) ∧
      (∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖) ∧
      (∀ i, ‖w i‖ ≤ 1 ∧ r < ‖w i‖) ∧
      ∀ (l : ι → K) (i : ι), t * r * ρ * ‖l i‖ ≤ ‖∑ j, l j • tiltSharp C p (w j)‖ := by
  obtain ⟨s, hs0, hs1, hs⟩ := exists_lt_mul_mul_lt_one (norm_nonneg (p : K))
    (IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p))
  obtain ⟨w, hli, hspan, horth, hnorm⟩ := exists_orthogonal_normalized (K := K) (C := C) hv hs1 hs0 hs1
  exact ⟨w, s, s, s, hs0, hs1, hs0, hs1, hs0, hs1, hs.le, hli, hspan, horth, hnorm,
    mul_norm_le_norm_sum_smul_tiltSharp horth (fun i => (hnorm i).1) (fun i => (hnorm i).2)
      hs0 hs0.le hs0 hs1 hs.le⟩
end GroundTheory.PAdicHodge
