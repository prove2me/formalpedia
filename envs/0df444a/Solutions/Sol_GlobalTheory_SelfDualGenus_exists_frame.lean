-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:30:43.299607+00:00
-- url     : https://prove2.me/submissions/0e3b9b27-dd92-4fa6-8b59-0f5ebc14200a

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_mem_span_semiLoc_iff

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
theorem _root_.solution {L : Submodule (𝓞 E) (Fin r → E)} (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) :
    ∃ g : GL (Fin r) E, ∀ x, (∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L) ↔
      ∀ i, (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x) i ∈ semiLoc v := by
  haveI : Submodule.IsLattice E (Submodule.span (semiLoc v) (L : Set (Fin r → E))) := by
    constructor
    · obtain ⟨s, rfl⟩ := hL.1
      exact ⟨s, (Submodule.span_span_of_tower (𝓞 E) _ _).symm⟩
    · rw [Submodule.span_span_of_tower, hL.2]
  obtain ⟨g, hg⟩ := exists_eq_frameLattice (Submodule.span (semiLoc v) (L : Set (Fin r → E)))
  refine ⟨g, fun x => ?_⟩
  rw [← mem_span_semiLoc_iff, hg, mem_frameLattice_iff_inv]
  exact forall_congr' fun i =>
    Submodule.mem_one.trans ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
end GlobalTheory.SelfDualGenus
