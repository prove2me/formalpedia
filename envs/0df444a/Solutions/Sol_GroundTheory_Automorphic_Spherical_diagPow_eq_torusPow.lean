-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.diagPow_eq_torusPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:15.998342+00:00
-- url     : https://prove2.me/submissions/0e8d6874-c4b1-4d32-b81d-f231e69e5843

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
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
open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra ValuativeRel
open scoped ValuativeRel
open GroundTheory.Automorphic.Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution (μ : Fin n → ℤ) : Cartan.diagPow F n μ = torusPow F n μ :=
  Units.ext (by rw [Cartan.coe_diagPow, coe_torusPow])
end GroundTheory.Automorphic.Spherical
