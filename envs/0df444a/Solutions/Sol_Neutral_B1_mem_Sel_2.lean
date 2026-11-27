-- Prove2me | solution 2 for Neutral.B1.mem_Sel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:49:52.408006+00:00
-- url     : https://prove2.me/submissions/f7cdbc0d-17a5-4c7e-9075-f78d21d443ab

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality

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
noncomputable section
open Representation
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable (rho : Representation R G M)
variable {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  (phi : ∀ i, D i →* G) (hphi : ∀ i, Continuous (phi i))
namespace Neutral.B1
theorem _root_.solution (L : LocCond rho phi) (x : H1 rho) :
    x ∈ Sel rho phi hphi L ↔ ∀ i, resH1 rho (phi i) (hphi i) x ∈ L i := by
  simp [Sel, Submodule.mem_iInf]
end Neutral.B1
