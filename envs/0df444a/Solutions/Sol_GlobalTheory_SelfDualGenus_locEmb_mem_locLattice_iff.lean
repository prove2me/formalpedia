-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.locEmb_mem_locLattice_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:41:17.520914+00:00
-- url     : https://prove2.me/submissions/a83655ef-22df-400d-8269-911c0e4c42f8

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_locEmb_mem_locOrder_iff
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_frame
import Theorems.Thm_GlobalTheory_SelfDualGenus_mem_locLattice_iff_of_frame

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
variable {L : Submodule (𝓞 E) (Fin r → E)}
namespace GlobalTheory.SelfDualGenus
theorem _root_.solution (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (x : Fin r → E) :
    (fun i => locEmb v (x i)) ∈ locLattice v L ↔
      ∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L := by
  obtain ⟨g, hg⟩ := exists_frame v hL
  rw [mem_locLattice_iff_of_frame v hg, hg]
  refine forall_congr' fun i => ?_
  rw [← locEmb_mem_locOrder_iff, RingHom.map_mulVec]
  rfl
end GlobalTheory.SelfDualGenus
