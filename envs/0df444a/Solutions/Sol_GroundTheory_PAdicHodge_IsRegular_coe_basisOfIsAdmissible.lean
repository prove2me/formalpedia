-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsRegular.coe_basisOfIsAdmissible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:52.044462+00:00
-- url     : https://prove2.me/submissions/76c3fb6c-8c1a-429b-9fcd-779b98113b84

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open TensorProduct Module
open GroundTheory.PAdicHodge.IsRegular
variable {G F B : Type*} [Group G] [Field F] [CommRing B] [IsDomain B] [Algebra F B]
  [MulSemiringAction G B] [SMulCommClass G F B] (h : IsRegular G F B)
include h
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
namespace GroundTheory.PAdicHodge.IsRegular
theorem _root_.solution [FiniteDimensional F V] (hadm : IsAdmissible B ρ)
    {ι : Type*} [Fintype ι] (b : Basis ι (invariantRing G F B) (DB B ρ)) :
    ⇑(h.basisOfIsAdmissible ρ hadm b) = fun i => (b i : B ⊗[F] V) :=
  Basis.coe_mk _ _
end GroundTheory.PAdicHodge.IsRegular
