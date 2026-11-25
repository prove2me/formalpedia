-- Prove2me | solution 1 for GroundTheory.PAdicHodge.untiltPreTiltAut_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:36:29.781186+00:00
-- url     : https://prove2.me/submissions/e67ad08c-169f-4f11-a1ce-23c5280deb1a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr
import Theorems.Thm_GroundTheory_PAdicHodge_ringHom_iterate_frobeniusEquiv_symm
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mk_untilt_iterate
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_preTilt_ext
import Theorems.Thm_GroundTheory_PAdicHodge_untiltAut_untilt


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
theorem _root_.solution (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (h : untiltAut N σ = 1)
    (b : PreTilt (normInteger (untiltField K C p N)) p) : untiltPreTiltAut N σ b = b := by
  have hu : ∀ b : PreTilt (normInteger (untiltField K C p N)) p,
      PreTilt.untilt (untiltPreTiltAut N σ b) = PreTilt.untilt b := by
    intro b
    have := untiltAut_untilt N σ b
    rw [h, AlgEquiv.one_apply] at this
    exact Subtype.ext this.symm
  refine IsPerfectoidField.preTilt_ext p fun n => ?_
  rw [← IsPerfectoidField.mk_untilt_iterate, ← IsPerfectoidField.mk_untilt_iterate,
    ← ringHom_iterate_frobeniusEquiv_symm, hu]
end GroundTheory.PAdicHodge
