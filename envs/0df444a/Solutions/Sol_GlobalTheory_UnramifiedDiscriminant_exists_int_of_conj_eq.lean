-- Prove2me | solution 1 for GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:08:29.175069+00:00
-- url     : https://prove2.me/submissions/ecc9dee3-d0f0-4fd9-95de-1debc389ab66

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqIdOfIsUnramifiedAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace GlobalTheory.UnramifiedDiscriminant
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
private lemma isCMExt_conj_ne_id (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  obtain ⟨-, hE, -, hτ⟩ := h
  intro hσ
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  have hc := hE.isComplex (InfinitePlace.mk τ)
  rw [InfinitePlace.isComplex_mk_iff] at hc
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  have hx := hτ τ x
  rw [hσ, AlgHom.id_apply] at hx
  exact hx.symm
open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
private lemma isCMExt_mem_range_of_conj_fixed (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {x : E} (hx : σ x = x) :
    x ∈ Set.range (algebraMap F E) := by
  have hprime : (Module.finrank F E).Prime := by rw [h.2.2.1]; exact Nat.prime_two
  haveI := Subalgebra.isSimpleOrder_of_finrank_prime F E hprime
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h0 | h1
  · have hmem : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
    rw [h0] at hmem
    exact Algebra.mem_bot.mp hmem
  · exfalso
    apply isCMExt_conj_ne_id h
    ext y
    have hmem : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := h1 ▸ Algebra.mem_top
    exact hmem
end GlobalTheory.UnramifiedDiscriminant
end

set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.UnramifiedDiscriminant
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
namespace GlobalTheory.UnramifiedDiscriminant
namespace _root_.GlobalTheory.UnramifiedDiscriminant
theorem _root_.solution (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (a : 𝓞 E) (ha : σ a = a) :
    ∃ t : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) t = a := by
  obtain ⟨f, hf⟩ := isCMExt_mem_range_of_conj_fixed h ha
  have hint : IsIntegral ℤ f := by
    rw [← isIntegral_algebraMap_iff (algebraMap F E).injective, hf]
    exact RingOfIntegers.isIntegral_coe a
  refine ⟨⟨f, hint⟩, ?_⟩
  ext
  exact hf
end _root_.GlobalTheory.UnramifiedDiscriminant
end GlobalTheory.UnramifiedDiscriminant
