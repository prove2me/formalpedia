-- Prove2me | solution 1 for Neutral.B1.mapH2_eq_compatiblePairH2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:23:58.206345+00:00
-- url     : https://prove2.me/submissions/36cb050d-df78-4e8b-b5bf-72f7b6c862a9

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
variable {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho' : Representation R G M') (u : M →ₗ[R] M') (hu : Continuous u)
  (hequiv : ∀ g m, u (rho g m) = rho' g (u m))
theorem _root_.solution :
    mapH2 rho rho' u hu hequiv =
      compatiblePairH2 rho rho' (MonoidHom.id G) continuous_id u hu hequiv := by
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
  trace "HIT_39_9"

end 
end 
