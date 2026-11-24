-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.exists_of_mem_locOrder_of_locConj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:58:46.462779+00:00
-- url     : https://prove2.me/submissions/a372cb89-ceca-4c36-8251-1987dfdc4780

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_algebraMap_locAlg_injective
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_of_locConj_eq
import Theorems.Thm_GlobalTheory_SelfDualGenus_isIntegral_of_mem_locOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
open scoped Matrix TensorProduct nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalLattice
noncomputable section
open GlobalTheory GlobalTheory.SelfDualGenus
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
namespace GlobalTheory.SelfDualGenus
theorem _root_.solution {z : LocAlg v} (hz : z ∈ locOrder v)
    (hc : locConj v z = z) :
    ∃ a : v.adicCompletionIntegers (maximalRealSubfield E), algebraMap _ (LocAlg v) a = z := by
  obtain ⟨a, rfl⟩ := exists_of_locConj_eq v hc
  have hi : IsIntegral (v.adicCompletionIntegers (maximalRealSubfield E)) a :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom (v.adicCompletionIntegers (maximalRealSubfield E))
      (v.adicCompletion (maximalRealSubfield E)) (LocAlg v)) (algebraMap_locAlg_injective v)).1
      (isIntegral_of_mem_locOrder v hz)
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact ⟨b, rfl⟩
end GlobalTheory.SelfDualGenus
