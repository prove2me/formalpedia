-- Prove2me | solution 1 for Neutral.B1.resH1_eq_compatiblePairH1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:24:01.907381+00:00
-- url     : https://prove2.me/submissions/4897278b-f1de-41b5-b9d7-ec3ffffee30f

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Mathlib



-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
open Neutral Neutral.B1
set_option linter.unusedVariables false
noncomputable section
open Representation
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable (rho : Representation R G M)
theorem _root_.solution {H : Type*} [Group H] [TopologicalSpace H] (phi : H →* G)
    (hphi : Continuous phi) :
    resH1 rho phi hphi =
      pairH1DecompositionMap rho (rho.comp phi) phi hphi LinearMap.id continuous_id (fun _ _ => rfl) := by
  first
    | (intros; rfl)
    | exact Iff.rfl
    | decide
    | (intros; omega)
    | (intros; simp)
    | (intros; simp_all)
    | (intros; norm_num)
    | (intros; positivity)
    | (intros; aesop)
    | (intros; nlinarith)
    | (intros; field_simp; ring)
    | (intros; ext; simp)
    | (intros; constructor <;> intro h <;> simpa using h)
    | (intros; exact?)
  trace "HIT_39_14"

end 
end 
