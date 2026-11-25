-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.cMat_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:47:34.862115+00:00
-- url     : https://prove2.me/submissions/0885cb7a-563b-44ba-a08a-9cc57cdc8830

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalMinuscule

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
open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra
open ValuativeRel (valuation)
open scoped ValuativeRel
open GroundTheory.Automorphic.Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
local notation "π" => (GLnLocal.uniformizer F : F)
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution {S : Finset (Fin n)} (c : Pairs S → 𝓀[F]) (i j : Fin n) : cMat S c i j ∈ 𝒪[F] := by
  unfold cMat
  split_ifs
  · exact (residueLift F _).2
  · exact (𝒪[F]).zero_mem
end GroundTheory.Automorphic.Spherical
