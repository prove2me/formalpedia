-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.mem_locLattice_of_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:54:46.832645+00:00
-- url     : https://prove2.me/submissions/d5a32604-9293-46b4-9276-96ad0f777daf

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_isUnit_algebraMap_iff
import Theorems.Thm_GlobalTheory_SelfDualGenus_locEmb_algebraMap

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
theorem _root_.solution {s : 𝓞 (maximalRealSubfield E)} (hs : s ∉ v.asIdeal) {x : Fin r → E}
    (hx : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L) : (fun i => locEmb v (x i)) ∈ locLattice v L := by
  obtain ⟨t, ht⟩ := ((isUnit_algebraMap_iff v s).2 hs).exists_left_inv
  have h1 : (fun i => locEmb v (x i)) =
      t • fun i => locEmb v ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x) i) := by
    funext i
    change _ = t • locEmb v ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * x i)
    rw [map_mul, locEmb_algebraMap, Algebra.smul_def, ← mul_assoc, ← map_mul, ht, map_one, one_mul]
  rw [h1]
  exact Submodule.smul_mem _ t (Submodule.subset_span ⟨_, hx, rfl⟩)
end GlobalTheory.SelfDualGenus
