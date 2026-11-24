-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.trace_form_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:17:05.262291+00:00
-- url     : https://prove2.me/submissions/e37a2468-1e57-4700-83a3-ee45e5d8f60d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EtaleAwayQuotientEqLocalization
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceFormGram_trace_entry
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceFormGram_trGram_isSymm
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceFormGram_trGram_det_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ B : Matrix (Fin M × Fin d) (Fin M × Fin d) F, B.IsSymm ∧ B.det ≠ 0 ∧ ∀ (R : Type) [CommRing R] [Algebra F R] (x y : Fin M → R ⊗[F] E), Algebra.trace R (R ⊗[F] E) (hR R σ J x y) = (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ (B.map (algebraMap F R) *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (y p.1) p.2) := by
  intro F E _ _ _ _ _ σ h M J hJ d b
  haveI : FiniteDimensional F E := Module.Basis.finiteDimensional_of_finite b
  refine ⟨TraceFormGram.trGram σ J b, TraceFormGram.trGram_isSymm h hJ b, TraceFormGram.trGram_det_ne_zero h hJ b, ?_⟩
  intro R _ _ x y
  have hh : hR R σ J x y = ∑ i, ∑ j, sigR R σ (x i) * ((1 : R) ⊗ₜ[F] J i j) * y j := rfl
  rw [hh]
  simp only [map_sum, TraceFormGram.trace_entry σ b R]
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Matrix.map_apply, TraceFormGram.trGram,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
end GlobalTheory.CompanionTheory.SW
