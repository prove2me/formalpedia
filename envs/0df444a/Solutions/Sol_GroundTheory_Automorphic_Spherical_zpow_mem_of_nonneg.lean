-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.zpow_mem_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:43:36.111389+00:00
-- url     : https://prove2.me/submissions/8b808e6f-8e59-4c4b-a4a1-2edd5ac3f152

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
theorem _root_.solution {t : ℤ} (ht : 0 ≤ t) : π ^ t ∈ 𝒪[F] := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ht
  rw [zpow_natCast]
  exact Subring.pow_mem _ (GLnLocal.uniformizer F).2 m
end GroundTheory.Automorphic.Spherical
