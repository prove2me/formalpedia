-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatFix.eventually_mul_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:34:44.095086+00:00
-- url     : https://prove2.me/submissions/ac399e49-a4c1-4493-9f08-faedc1e4c7a5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjections
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EventuallyActMemLatVIff
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatFix_repr_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatFix_eventually_integral
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open PositivityTheory.Rg.Mass HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatFix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.LatFix
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ x y : Fv F v ⊗[F] E,
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr x k ∈ v.adicCompletionIntegers F) →
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) →
      ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (x * y) k ∈
        v.adicCompletionIntegers F := by
  classical
  have h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ i j k : Fin d,
      algebraMap F (Fv F v) (b.repr (b i * b j) k) ∈ v.adicCompletionIntegers F := by
    simp only [Filter.eventually_all]
    exact fun i j k => eventually_integral _
  filter_upwards [h] with v hv x y hx hy k
  rw [repr_mul]
  exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (mul_mem (hx i) (hy j)) (hv i j k)
end GlobalTheory.CompanionTheory.SW.LatFix
