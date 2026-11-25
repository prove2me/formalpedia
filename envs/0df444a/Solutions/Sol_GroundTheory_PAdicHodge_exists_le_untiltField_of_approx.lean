-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_le_untiltField_of_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:12:14.134046+00:00
-- url     : https://prove2.me/submissions/1df48349-48f5-4b0a-96be-5cdce8b4fb95

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltField
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgClosed
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApprox
import Theorems.Thm_GroundTheory_PAdicHodge_perfectField_of_isPerfectoidField
import Theorems.Thm_GroundTheory_PAdicHodge_exists_mem_untiltField_of_approx

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
open Polynomial
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution [IsAlgClosed C] [IsAlgClosed C♭]
    (hfin : ∀ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N →
      FiniteDimensional K (untiltField K C p N))
    (happrox : ∀ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N →
      ∀ y ∈ untiltField K C p N, ‖y‖ ≤ 1 →
        ∃ a ∈ integerTilt K C p N, ‖y - ((PreTilt.untilt a : normInteger C) : C)‖ ≤ ‖(p : K)‖)
    (L : IntermediateField K C) [FiniteDimensional K L] :
    ∃ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N ∧ L ≤ untiltField K C p N := by
  have : PerfectField K := perfectField_of_isPerfectoidField K p
  obtain ⟨γ, hγ⟩ := Field.exists_primitive_element K L
  have hγi : IsIntegral K (γ : C) := (IsIntegral.of_finite K γ).map (IsScalarTower.toAlgHom K L C)
  obtain ⟨N, hN, hmem⟩ := exists_mem_untiltField_of_approx hfin happrox hγi
  refine ⟨N, hN, ?_⟩
  have hL : L = IntermediateField.adjoin K {(γ : C)} := by
    rw [← IntermediateField.lift_adjoin_simple, hγ, IntermediateField.lift_top]
  rw [hL, IntermediateField.adjoin_simple_le_iff]
  exact hmem
end GroundTheory.PAdicHodge
