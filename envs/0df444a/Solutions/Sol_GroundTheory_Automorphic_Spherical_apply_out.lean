-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.apply_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:29:25.966526+00:00
-- url     : https://prove2.me/submissions/093d89b3-0810-4c0f-ba3f-71c0b339284c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular

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
variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F) :
    (h : HeckeAlgebra μ) (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL F n).out =
      (h : HeckeAlgebra μ) g := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F n) g
  rw [hk, (HeckeAlgebraLevel.val_mem _ _ h k k.2 g).2]
end GroundTheory.Automorphic.Spherical
