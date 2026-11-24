-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimGood.change_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:29:32.123669+00:00
-- url     : https://prove2.me/submissions/4e9bce65-271c-4a74-910f-91cd9779d7da

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodInt_eventually_le_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodInt_repr_inclR
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodInt_valued_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimGood
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.PrimGood
theorem _root_.solution {d d' : ℕ} (b : Module.Basis (Fin d) F E) (b' : Module.Basis (Fin d') F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ x : Fv F v ⊗[F] E,
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr x k ∈ v.adicCompletionIntegers F) →
      ∀ k, (Algebra.TensorProduct.basis (Fv F v) b').repr x k ∈ v.adicCompletionIntegers F := by
  have h : ∀ j k, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      v.valuation F (b'.repr (b j) k) ≤ 1 := fun j k => GoodInt.eventually_le_one _
  filter_upwards [Filter.eventually_all.2 fun j => Filter.eventually_all.2 (h j)] with v hv x hx k
  have key : (Algebra.TensorProduct.basis (Fv F v) b').repr x k =
      ∑ j, (Algebra.TensorProduct.basis (Fv F v) b).repr x j *
        (Algebra.TensorProduct.basis (Fv F v) b').repr
          ((Algebra.TensorProduct.basis (Fv F v) b) j) k := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr x]
    simp [map_sum, Finsupp.finset_sum_apply]
  rw [key]
  refine sum_mem fun j _ => mul_mem (hx j) ?_
  have e : (Algebra.TensorProduct.basis (Fv F v) b) j = inclR (Fv F v) (b j) := by
    simp [inclR, Algebra.TensorProduct.basis_apply]
  rw [e, GoodInt.repr_inclR, HeightOneSpectrum.mem_adicCompletionIntegers,
    GoodInt.valued_algebraMap]
  exact hv j k
end GlobalTheory.CompanionTheory.SW.PrimGood
