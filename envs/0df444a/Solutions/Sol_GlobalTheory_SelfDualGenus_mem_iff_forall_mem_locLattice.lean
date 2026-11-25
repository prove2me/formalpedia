-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.mem_iff_forall_mem_locLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:12:14.718458+00:00
-- url     : https://prove2.me/submissions/be1f7a31-293c-430a-ba86-389deb13dcc9

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_locEmb_mem_locLattice_iff
import Theorems.Thm_GlobalTheory_LocalLattice_mem_iff_forall_mem_localize_ringOfIntegers


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
namespace GlobalTheory.SelfDualGenus
theorem _root_.solution {L : Submodule (𝓞 E) (Fin r → E)}
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (x : Fin r → E) :
    x ∈ L ↔ ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (fun i => locEmb v (x i)) ∈ locLattice v L := by
  refine ⟨fun hx v => Submodule.subset_span ⟨x, hx, rfl⟩, fun h => ?_⟩
  refine (mem_iff_forall_mem_localize_ringOfIntegers L x).2 fun w => ?_
  obtain ⟨s, hs, h⟩ := (locEmb_mem_locLattice_iff (w.under (𝓞 (maximalRealSubfield E))) hL x).1 (h _)
  exact (mem_localize_iff w L x).2 ⟨_, hs, h⟩
end GlobalTheory.SelfDualGenus
