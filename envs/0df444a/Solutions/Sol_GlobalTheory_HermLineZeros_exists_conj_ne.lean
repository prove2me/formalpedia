-- Prove2me | solution 1 for GlobalTheory.HermLineZeros.exists_conj_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:15:55.367868+00:00
-- url     : https://prove2.me/submissions/fc26aa76-e487-407f-9bfc-d9f44b946c93

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HermitianFormFiniteZerosOnLineCmExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.HermLineZeros
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
namespace GlobalTheory.HermLineZeros
namespace _root_.GlobalTheory.HermLineZeros
theorem _root_.solution (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) : ∃ d, σ d ≠ d := by
  by_contra! hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx := h.2.2.2 τ x
    rw [hσ x] at hx
    simpa [ComplexEmbedding.conjugate_coe_eq] using hx.symm
  have hcx := (h.2.1).isComplex (InfinitePlace.mk τ)
  rw [InfinitePlace.isComplex_mk_iff] at hcx
  exact hcx hreal
end _root_.GlobalTheory.HermLineZeros
end GlobalTheory.HermLineZeros
