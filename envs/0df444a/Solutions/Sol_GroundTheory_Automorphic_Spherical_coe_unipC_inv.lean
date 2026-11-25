-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.coe_unipC_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:35:43.409304+00:00
-- url     : https://prove2.me/submissions/cecc41a4-dc16-4e09-b39c-8f3b31a6859b

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
theorem _root_.solution (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) :
    (((unipC S c)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 - cMat S c := rfl
end GroundTheory.Automorphic.Spherical
