-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.gMat_inv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:02:08.406123+00:00
-- url     : https://prove2.me/submissions/eae30a1e-0b7f-4b58-aee3-9dfe4dc99f8d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalMinuscule
import Theorems.Thm_GroundTheory_Automorphic_Spherical_coe_unipC_inv
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_coe_torusPow
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_torusPow_neg


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
theorem _root_.solution (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) (i j : Fin n) :
    ((gMat S c)⁻¹ : GL (Fin n) F) i j = π ^ (-lamS S i) *
      ((1 : Matrix (Fin n) (Fin n) F) i j - cMat S c i j) := by
  change (((torusPow F n (lamS S))⁻¹ : GL (Fin n) F) * ((unipC S c)⁻¹ : GL (Fin n) F) :
    Matrix (Fin n) (Fin n) F) i j = _
  rw [← torusPow_neg, coe_torusPow, diagonal_mul, coe_unipC_inv, Matrix.sub_apply]
  rfl
end GroundTheory.Automorphic.Spherical
