-- Prove2me | solution 1 for GlobalTheory.ResidueCharacterDense.smallIdeal_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:39:25.546928+00:00
-- url     : https://prove2.me/submissions/0288cba4-8826-4465-ab03-b2d1ccccced8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Theorems.Thm_GlobalTheory_ResidueCharacterDense_mem_smallIdeal
import Theorems.Thm_GlobalTheory_ResidueCharacterDense_smallIdeal_isPrime
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense
variable {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [NumberField F]
  (p : HeightOneSpectrum (𝓞 F)) {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [T2Space K] [CharZero K] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K] [ContinuousSMul ℚ_[l] K]
  (ι : F →+* K) (U : Set K)
omit [CharZero K]
namespace GlobalTheory.ResidueCharacterDense
theorem _root_.solution (hU : ∀ x, ι x ∈ U ↔ p.valuation F x < 1)
    (hpow : ∀ z ∈ U, Tendsto (fun n : ℕ => z ^ n) atTop (𝓝 0))
    (τ : K →ₐ[ℚ_[l]] PadicAlgCl l) :
    p.asIdeal = smallIdeal ((τ : K →+* PadicAlgCl l).comp ι) := by
  have h1 : Continuous τ := τ.toLinearMap.continuous_of_finiteDimensional
  apply p.isMaximal.eq_of_le (smallIdeal_isPrime _).ne_top
  intro x hx
  rw [mem_smallIdeal]
  have h2 := hpow _ ((hU x).mpr ((p.valuation_lt_one_iff_mem x).mpr hx))
  have h3 := (h1.tendsto 0).comp h2
  rw [map_zero] at h3
  rw [← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  refine h3.congr fun n => ?_
  simp
end GlobalTheory.ResidueCharacterDense
