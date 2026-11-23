-- Prove2me | solution 1 for GlobalTheory.LocalQuad.Approx.abv_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:19.578357+00:00
-- url     : https://prove2.me/submissions/6e46722a-c87a-403b-b374-36d9f7ce858b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsForallAbvSubLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad GlobalTheory.LocalQuad.Approx
variable {F : Type} [Field F] [NumberField F]
open NumberField IsDedekindDomain
open scoped Matrix WithZero
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.LocalQuad.Approx
namespace _root_.GlobalTheory.LocalQuad.Approx
theorem _root_.solution (T : Finset (HeightOneSpectrum (𝓞 F))) (v : T) (x : F) :
    _root_.GlobalTheory.LocalQuad.Approx.abv T (Sum.inl v) x = ‖algebraMap F (v.1.adicCompletion F) x‖ :=
  (FinitePlace.norm_embedding v.1 x).symm
end _root_.GlobalTheory.LocalQuad.Approx
end GlobalTheory.LocalQuad.Approx
