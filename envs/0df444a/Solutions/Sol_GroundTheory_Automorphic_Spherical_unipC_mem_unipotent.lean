-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.unipC_mem_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:38:18.821529+00:00
-- url     : https://prove2.me/submissions/5ca14aa1-f57d-4236-b098-4fe9216d04ec

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalMinuscule

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
theorem _root_.solution (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) :
    unipC S c ∈ unipotent F n := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : j < i := hij
    change (1 + cMat S c) i j = 0
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij'),
      cMat_apply_of_not c (fun h => absurd h.2.2 (not_lt.2 (le_of_lt hij'))), add_zero]
  · change (1 + cMat S c) i i = 1
    rw [Matrix.add_apply, Matrix.one_apply_eq, cMat_apply_of_not c (fun h => lt_irrefl _ h.2.2),
      add_zero]
end GroundTheory.Automorphic.Spherical
