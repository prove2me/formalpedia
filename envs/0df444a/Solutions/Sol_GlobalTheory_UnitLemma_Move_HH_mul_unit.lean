-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Move.HH_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:32:38.727049+00:00
-- url     : https://prove2.me/submissions/64c9322a-a5a6-445f-ba14-3593fae90ad4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFixedBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SignedInvolutionStableLatticeSumMulFixedUnit
import Theorems.Thm_GlobalTheory_UnitLemma_Move_mulLat_inv
import Theorems.Thm_GlobalTheory_UnitLemma_Move_mulLat_mem_Lin
import Theorems.Thm_GlobalTheory_UnitLemma_Move_sgnLat_mulLat
import Theorems.Thm_GlobalTheory_UnitLemma_Move_term_mulLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Move
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.UnitLemma.Move
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (ι : Type) (π : ι → B.A) (I I' : Finset ι) (u s y : B.A),
    B.LieReg → B.Plus y → HH B π I I' (y * u) s = K.eta (Algebra.norm K.E y) * HH B π I I' u (y * s) := by
  intro K B ι π I I' u s y hB hy
  obtain ⟨⟨yu, rfl⟩, hσ⟩ := hy
  have hσ' : B.σ ((yu⁻¹ : B.Aˣ) : B.A) = ((yu⁻¹ : B.Aˣ) : B.A) := by
    have h1 : B.σ ((yu⁻¹ : B.Aˣ) : B.A) * (yu : B.A) = 1 := by
      conv_lhs => rw [← hσ]
      rw [← map_mul, Units.inv_mul, map_one]
    calc B.σ ((yu⁻¹ : B.Aˣ) : B.A) = B.σ ((yu⁻¹ : B.Aˣ) : B.A) * (yu : B.A) * ((yu⁻¹ : B.Aˣ) : B.A) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  unfold HH
  rw [mul_finsum_mem]
  symm
  refine finsum_mem_eq_of_bijOn (fun M => mulLat K.O (yu : B.A) M) ?_ ?_
  · refine Set.InvOn.bijOn (f' := fun M => mulLat K.O ((yu⁻¹ : B.Aˣ) : B.A) M) ⟨fun M _ => ?_, fun M _ => ?_⟩
      (fun M hM => mulLat_mem_Lin B yu hσ M hM) (fun M hM => ?_)
    · exact mulLat_inv B M yu
    · have := mulLat_inv B M yu⁻¹
      rwa [inv_inv] at this
    · have := mulLat_mem_Lin B yu⁻¹ hσ' M hM
      exact this
  · intro M hM
    rw [sgnLat_mulLat B hB.2 M hM.1 hM.2.2 yu, term_mulLat]
    ring
end GlobalTheory.UnitLemma.Move
