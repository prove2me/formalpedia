-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.apply_eq_apply_cartanType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:53:53.839207+00:00
-- url     : https://prove2.me/submissions/4b5b3396-ee30-4631-8de2-d99bee57a5f8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
import Theorems.Thm_GroundTheory_Automorphic_Spherical_cartanType_spec

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
    (h : HeckeAlgebra μ) g = (h : HeckeAlgebra μ) (Cartan.diagPow F n (cartanType F n g)) := by
  obtain ⟨k₁, hk₁, k₂, hk₂, hg⟩ := (Cartan.mem_doubleCoset_diagPow F n).1 (cartanType_spec g).2
  conv_lhs => rw [hg]
  rw [(HeckeAlgebraLevel.val_mem _ _ h k₂ hk₂ _).2, HeckeAlgebraLevel.apply_mul_left _ _ h hk₁]
end GroundTheory.Automorphic.Spherical
