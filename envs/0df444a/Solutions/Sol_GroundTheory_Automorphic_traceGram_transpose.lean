-- Prove2me | solution 1 for GroundTheory.Automorphic.traceGram_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:52.019797+00:00
-- url     : https://prove2.me/submissions/d23fdb7a-2e1c-47eb-a9cb-f25c9cd9d928

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Places
import Theorems.Thm_GroundTheory_Automorphic_hermTrace_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct NumberField NumberField.InfinitePlace
variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R]
variable {H b}
omit [NumberField K] [Fintype κ]
namespace GroundTheory.Automorphic
theorem _root_.solution (hH : IsHermitianFor (conjHom K E) H) :
    (traceGram H b)ᵀ = traceGram H b := by
  ext a c
  exact hermTrace_comm hH _ _
end GroundTheory.Automorphic
