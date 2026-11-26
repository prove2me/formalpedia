-- Prove2me | solution 1 for Neutral.B1.resH2_eq_compatiblePairH2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:24:00.828908+00:00
-- url     : https://prove2.me/submissions/3aff1447-1bb3-4499-8143-fcd65c11d0db

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
    resH2 rho phi hphi =
      compatiblePairH2 rho (rho.comp phi) phi hphi LinearMap.id continuous_id (fun _ _ => rfl) := by
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
  trace "HIT_39_13"

end 
end 
