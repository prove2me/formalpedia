-- Prove2me | solution 1 for GlobalTheory.AdLat.Model.integral_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:47.120415+00:00
-- url     : https://prove2.me/submissions/2c02ecf3-f8c4-41a0-b978-c6b499ed97b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Model
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.AdLat.Model
namespace _root_.GlobalTheory.AdLat.Model
theorem _root_.solution (x : F) :
    (∀ v, algebraMap F (FiniteAdeleRing (𝓞 F) F) x v ∈ v.adicCompletionIntegers F) ↔
      x ∈ (algebraMap (𝓞 F) F).range := by
  constructor
  · intro h
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have hv := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp (h v)
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hv
  · rintro ⟨r, rfl⟩ v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have hv := HeightOneSpectrum.valuation_le_one (K := F) v r
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at hv
    exact hv
end _root_.GlobalTheory.AdLat.Model
end GlobalTheory.AdLat.Model
