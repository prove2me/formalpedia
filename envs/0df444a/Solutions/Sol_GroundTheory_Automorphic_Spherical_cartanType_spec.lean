-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.cartanType_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:38:42.997357+00:00
-- url     : https://prove2.me/submissions/85c59d26-f28c-4845-9a83-edc46877cb72

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
import Theorems.Thm_GroundTheory_Automorphic_Cartan_existsUnique_mem_doubleCoset


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
theorem _root_.solution (g : GL (Fin n) F) :
    Cartan.IsDominant (cartanType F n g) ∧
      g ∈ DoubleCoset.doubleCoset (Cartan.diagPow F n (cartanType F n g))
        (integralGL F n : Set (GL (Fin n) F)) (integralGL F n) :=
  (Cartan.existsUnique_mem_doubleCoset F n g).exists.choose_spec
end GroundTheory.Automorphic.Spherical
