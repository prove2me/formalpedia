-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_le_untiltField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:22:35.266526+00:00
-- url     : https://prove2.me/submissions/01ff1780-56a3-4c68-a5d7-e5a461d28c10

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltField
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgClosed
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApprox
import Theorems.Thm_GroundTheory_PAdicHodge_exists_le_untiltField_of_approx
import Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_sub_untilt_le


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
theorem _root_.solution [IsAlgClosed C] (L : IntermediateField K C) [FiniteDimensional K L] :
    ∃ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N ∧ L ≤ untiltField K C p N :=
  exists_le_untiltField_of_approx (fun N hN => by have := hN; infer_instance)
    (fun N hN _ hy hy1 => by have := hN; exact exists_norm_sub_untilt_le N hy hy1) L
end GroundTheory.PAdicHodge
