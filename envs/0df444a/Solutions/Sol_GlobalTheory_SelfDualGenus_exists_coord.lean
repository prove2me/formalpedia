-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.exists_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:14:08.712804+00:00
-- url     : https://prove2.me/submissions/762da002-4ed5-4b57-93d3-161d3b80b179

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_Published_exists_basis_one_imaginary


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
theorem _root_.solution {θ : E} (h0 : θ ≠ 0) (hθ : cc θ = -θ) (z : LocAlg v) :
    ∃ p q : v.adicCompletion (maximalRealSubfield E),
      z = algebraMap _ (LocAlg v) p + algebraMap _ (LocAlg v) q * locEmb v θ := by
  obtain ⟨b, hb0, hb1⟩ := Published.exists_basis_one_imaginary h0 hθ
  let B := Algebra.TensorProduct.basis (v.adicCompletion (maximalRealSubfield E)) b
  refine ⟨B.repr z 0, B.repr z 1, ?_⟩
  conv_lhs => rw [← B.sum_repr z, Fin.sum_univ_two]
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.basis_apply, hb0, hb1, ← Algebra.TensorProduct.one_def, mul_one]
  rfl
end GlobalTheory.SelfDualGenus
