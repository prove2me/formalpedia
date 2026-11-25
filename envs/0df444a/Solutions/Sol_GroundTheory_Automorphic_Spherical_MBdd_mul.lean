-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.MBdd.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:34:54.371651+00:00
-- url     : https://prove2.me/submissions/98f005ea-9e1a-4d60-906a-a8160d0b3f90

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalMinuscule
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_mul_apply
import Theorems.Thm_GroundTheory_Automorphic_Spherical_Bdd_mul
import Theorems.Thm_GroundTheory_Automorphic_Spherical_bdd_sum


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
namespace MBdd
theorem _root_.solution {s t : ℤ} {A B : Matrix (Fin n) (Fin n) F} (hA : MBdd F s A) (hB : MBdd F t B) :
    MBdd F (s + t) (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact bdd_sum _ fun l _ => (hA i l).mul (hB l j)
end MBdd
end GroundTheory.Automorphic.Spherical
