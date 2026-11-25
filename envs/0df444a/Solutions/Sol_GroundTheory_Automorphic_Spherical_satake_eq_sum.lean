-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.satake_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:29:09.279743+00:00
-- url     : https://prove2.me/submissions/fe4a478c-a1ec-47c8-aff0-9ff0ba0d81b5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalPrincipal
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake

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
open MeasureTheory Matrix GLnLocal Iwasawa Parabolic HeckeAlgebra AddMonoidAlgebra
open scoped ValuativeRel
open GroundTheory.Automorphic.Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution (h : SphericalHecke μ (F := F) (n := n))
    (S : Finset (GL (Fin n) F ⧸ integralGL F n)) (hS : ∀ x ∉ S, (h : HeckeAlgebra μ) x.out = 0) :
    satake μ h = (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) •
      ∑ x ∈ S, single (iwasawaExponent F n x.out) ((h : HeckeAlgebra μ) x.out) := by
  classical
  rw [satake]
  congr 1
  rw [Finset.sum_subset (Finset.subset_union_left (s₂ := S)) fun x _ hx => by
      rw [apply_out_eq_zero hx, AddMonoidAlgebra.single_zero]]
  exact (Finset.sum_subset (Finset.subset_union_right (s₁ := cosetSupport h)) fun x _ hx => by
      rw [hS x hx, AddMonoidAlgebra.single_zero]).symm
end GroundTheory.Automorphic.Spherical
