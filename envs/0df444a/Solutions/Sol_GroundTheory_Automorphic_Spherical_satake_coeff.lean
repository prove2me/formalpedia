-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.satake_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:32:43.326591+00:00
-- url     : https://prove2.me/submissions/eacf09cf-273e-4d59-b1e7-b38cb12c0566

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
theorem _root_.solution (h : SphericalHecke μ (F := F) (n := n)) (l : Fin n → ℤ) :
    (satake μ h).coeff l = (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) *
      ∑ x ∈ cosetSupport h,
        if iwasawaExponent F n x.out = l then (h : HeckeAlgebra μ) x.out else 0 := by
  classical
  rw [satake, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, AddMonoidAlgebra.coeff_sum,
    Finsupp.finset_sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
end GroundTheory.Automorphic.Spherical
