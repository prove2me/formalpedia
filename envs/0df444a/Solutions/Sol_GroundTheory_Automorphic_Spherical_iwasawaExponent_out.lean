-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.iwasawaExponent_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:49.513721+00:00
-- url     : https://prove2.me/submissions/7ebf9f13-bc9f-4d3b-94e7-f541a55dddfd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_iwasawaExponent_mul_of_mem_integralGL


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
theorem _root_.solution (g : GL (Fin n) F) :
    iwasawaExponent F n (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL F n).out =
      iwasawaExponent F n g := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F n) g
  rw [hk, iwasawaExponent_mul_of_mem_integralGL F n g k.2]
end GroundTheory.Automorphic.Spherical
