-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.nonneg_of_zpow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:10.176093+00:00
-- url     : https://prove2.me/submissions/d9bdc705-4431-436f-94ef-c1687d79f017

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients

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
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {π : Representation ℂ (GL (Fin n) F) V}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {z : ℤ} (h : (uniformizer F : F) ^ z ∈ 𝒪[F]) : 0 ≤ z := by
  have h1 := (Valuation.mem_integer_iff _ _).1 h
  rw [map_zpow₀] at h1
  exact (zpow_le_one_iff_right_of_lt_one₀
    (zero_lt_iff.2 (valuation_uniformizer_ne_zero F)) (valuation_uniformizer_lt_one F)).1 h1
end GroundTheory.Automorphic.Parabolic
