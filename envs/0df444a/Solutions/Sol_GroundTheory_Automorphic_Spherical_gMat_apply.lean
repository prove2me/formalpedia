-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.gMat_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:29.556721+00:00
-- url     : https://prove2.me/submissions/e4719b53-c43a-460a-a272-412f41c22857

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalMinuscule
import Theorems.Thm_GroundTheory_Automorphic_Spherical_coe_unipC
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_coe_torusPow


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
theorem _root_.solution (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) (i j : Fin n) :
    (gMat S c : GL (Fin n) F) i j = ((1 : Matrix (Fin n) (Fin n) F) i j + cMat S c i j) *
      π ^ lamS S j := by
  change ((unipC S c : GL (Fin n) F) * (torusPow F n (lamS S) : GL (Fin n) F) :
    Matrix (Fin n) (Fin n) F) i j = _
  rw [coe_torusPow, mul_diagonal, coe_unipC, Matrix.add_apply]
end GroundTheory.Automorphic.Spherical
