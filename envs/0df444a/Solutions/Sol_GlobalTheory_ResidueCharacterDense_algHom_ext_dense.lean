-- Prove2me | solution 1 for GlobalTheory.ResidueCharacterDense.algHom_ext_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:30:50.544942+00:00
-- url     : https://prove2.me/submissions/bfa4579b-69f7-4287-b149-279e3469c1ed

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense
variable {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [NumberField F]
  (p : HeightOneSpectrum (𝓞 F)) {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [T2Space K] [CharZero K] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K] [ContinuousSMul ℚ_[l] K]
  (ι : F →+* K) (U : Set K)
omit [NumberField F] [CharZero K]
namespace GlobalTheory.ResidueCharacterDense
theorem _root_.solution (hd : DenseRange ι) (τ τ' : K →ₐ[ℚ_[l]] PadicAlgCl l)
    (h : ∀ x, τ (ι x) = τ' (ι x)) : τ = τ' := by
  have h1 : Continuous τ := τ.toLinearMap.continuous_of_finiteDimensional
  have h2 : Continuous τ' := τ'.toLinearMap.continuous_of_finiteDimensional
  exact DFunLike.coe_injective (hd.equalizer h1 h2 (funext h))
end GlobalTheory.ResidueCharacterDense
