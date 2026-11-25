-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.normChar_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:34:30.638383+00:00
-- url     : https://prove2.me/submissions/21357bf0-15b1-4fb9-9b40-dd55ffe59cad

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingPositivity
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_scalarDet_mem_center

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Function Topology ComplexConjugate
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {ω : GL (Fin n) F → ℂ}
variable (hωπ : HasCentralChar π ω) {v : V} (hv : v ≠ 0)
include hωπ hv
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {k : GL (Fin n) F} (hk : π (scalarDet k) v = v) : normChar ω k = 1 := by
  have h1 : ω (scalarDet k) • v = (1 : ℂ) • v := by
    rw [one_smul, ← hωπ _ (scalarDet_mem_center k), hk]
  unfold normChar
  rw [smul_left_injective ℂ hv h1, norm_one, Real.one_rpow]
end GroundTheory.Automorphic.Parabolic
