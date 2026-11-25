-- Prove2me | solution 1 for GroundTheory.Automorphic.hermTrace_eq_sum_traceGram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:28:35.95004+00:00
-- url     : https://prove2.me/submissions/3323a15d-f75c-4702-822a-f311340e8b0b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Places
import Theorems.Thm_GroundTheory_Automorphic_hermTrace_eq_sum


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
omit [NumberField K]
namespace GroundTheory.Automorphic
theorem _root_.solution (x y : ι → R ⊗[K] E) :
    hermTrace K H R x y = ∑ a : ι × κ, ∑ c : ι × κ, vecCoords R b x a * vecCoords R b y c *
      algebraMap K R (traceGram H b a c) :=
  hermTrace_eq_sum H b x y
end GroundTheory.Automorphic
