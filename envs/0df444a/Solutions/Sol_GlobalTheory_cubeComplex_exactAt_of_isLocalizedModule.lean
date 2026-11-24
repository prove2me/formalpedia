-- Prove2me | solution 1 for GlobalTheory.cubeComplex_exactAt_of_isLocalizedModule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:34:02.792476+00:00
-- url     : https://prove2.me/submissions/523cc90c-ec2f-4d0e-9169-7d78e6a6250e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v u
open GlobalTheory
variable {ι : Type} {R : Type u} [CommRing R]
namespace GlobalTheory
theorem _root_.solution [LinearOrder ι] [Finite ι]
    (A : Cube.{v} ι R) (f : ι → R)
    {M : Type*} [AddCommGroup M] [Module R M] (g : ∀ s, M →ₗ[R] A.obj s)
    (hg : ∀ s, IsLocalizedModule.Away (∏ i ∈ s, f i) (g s))
    (hres : ∀ {s t : Finset ι} (h : s ⊆ t) (m : M), Cube.res A h (g s m) = g t m)
    (hf : Ideal.span (Set.range f) = ⊤) (p : ℕ) : (cubeComplex A).ExactAt p :=
  cubeComplex_exactAt_of_isLocalizedModule_res A f
    (Cube.isLocalizedModule_res_insert A f g hg hres) hf p
end GlobalTheory
