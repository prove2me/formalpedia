-- Prove2me | solution 1 for GroundTheory.PAdicHodge.natDegree_monicOfCoeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:40.998237+00:00
-- url     : https://prove2.me/submissions/9d990d99-933b-43c1-84cf-08373f0309bd

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
import Theorems.Thm_GroundTheory_PAdicHodge_monic_monicOfCoeffs
import Theorems.Thm_GroundTheory_PAdicHodge_coeff_monicOfCoeffs

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
variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField C p]
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution (e : ℕ) (a : ℕ → 𝒪C♭) : (monicOfCoeffs e a).natDegree = e := by
  have hm := monic_monicOfCoeffs e a
  refine le_antisymm (natDegree_le_iff_coeff_eq_zero.2 fun m hm' => ?_) ?_
  · rw [coeff_monicOfCoeffs, if_neg (by
      have : e < m := by exact_mod_cast hm'
      omega), if_neg (by
      have : e < m := by exact_mod_cast hm'
      omega)]
  · refine le_natDegree_of_ne_zero ?_
    rw [coeff_monicOfCoeffs, if_pos rfl]
    exact one_ne_zero
end GroundTheory.PAdicHodge
