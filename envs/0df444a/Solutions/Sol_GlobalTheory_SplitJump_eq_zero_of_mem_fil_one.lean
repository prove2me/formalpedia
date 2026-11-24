-- Prove2me | solution 1 for GlobalTheory.SplitJump.eq_zero_of_mem_fil_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:52:51.844777+00:00
-- url     : https://prove2.me/submissions/766bad1f-29a2-4e0f-b32c-ca4a9d45b29f

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PeriodDataComparison

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory GlobalTheory.SplitJump
open Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
open Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
namespace GlobalTheory.SplitJump
namespace _root_.GlobalTheory.SplitJump
theorem _root_.solution (k : K) (hk : algebraMap K BdR k ∈ PD.Fil 1) :
    k = 0 := by
  by_contra hne
  have h1 : (1 : BdR) ∈ PD.Fil 1 := by
    have := (PD.Fil 1).smul_mem k⁻¹ hk
    rwa [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hne, map_one] at this
  have := PD.Fil_mul 1 1 _ _ PD.mem_filtration_one h1
  rw [mul_one] at this
  exact PD.not_mem_filtration_two (by simpa using this)
end _root_.GlobalTheory.SplitJump
end GlobalTheory.SplitJump
