-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.cartanType_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:59:02.827943+00:00
-- url     : https://prove2.me/submissions/3d569f70-6f5c-4f85-ad3b-0d4ec2aad495

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
import Theorems.Thm_GroundTheory_Automorphic_Spherical_cartanType_spec
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
theorem _root_.solution {g : GL (Fin n) F} {μ : Fin n → ℤ} (hμ : Cartan.IsDominant μ)
    (hg : g ∈ DoubleCoset.doubleCoset (Cartan.diagPow F n μ)
      (integralGL F n : Set (GL (Fin n) F)) (integralGL F n)) :
    cartanType F n g = μ :=
  (Cartan.existsUnique_mem_doubleCoset F n g).unique (cartanType_spec g) ⟨hμ, hg⟩
end GroundTheory.Automorphic.Spherical
