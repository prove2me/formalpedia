-- Prove2me | solution 1 for GlobalTheory.UnramifiedDiscriminant.exists_discr_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:19:12.359438+00:00
-- url     : https://prove2.me/submissions/0ea4c5a3-4ced-4d3e-8d4c-6da714f50161

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqIdOfIsUnramifiedAt
import Theorems.Thm_GlobalTheory_UnramifiedDiscriminant_exists_int_of_conj_eq
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
open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
private lemma isCMExt_conj_conj (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hτ⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hτ, hτ, star_star]
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
theorem _root_.solution (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace F E v) :
    ∃ (w : E) (t n : 𝓞 F), w + σ w = algebraMap F E (t : F) ∧ w * σ w = algebraMap F E (n : F) ∧
      t ^ 2 - 4 * n ∉ v.asIdeal := by
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨P, -, hPp, hPv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E))
    (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  have hPne : P ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hPv, Ideal.comap_bot_of_injective _ hinj]
  haveI : P.LiesOver v.asIdeal := ⟨hPv.symm⟩
  haveI : Algebra.IsUnramifiedAt (𝓞 F) P := hv ⟨P, hPp, hPne⟩ ⟨hPv.symm⟩
  let σ' : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Function.Involutive.bijective (isCMExt_conj_conj h))
  haveI : IsGalois F E := by
    refine IsGalois.of_fixedField_eq_bot F E (eq_bot_iff.mpr fun x hx => ?_)
    exact IntermediateField.mem_bot.mpr (isCMExt_mem_range_of_conj_fixed h
      ((IntermediateField.mem_fixedField_iff _ _).mp hx σ' (Subgroup.mem_top _)))
  have hcard : Nat.card (P.inertia (E ≃ₐ[F] E)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn v.asIdeal P,
      Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P (E ≃ₐ[F] E)]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, σ' • x - x ∉ P := by
    by_contra hcon
    push_neg at hcon
    have hmem : σ' ∈ P.inertia (E ≃ₐ[F] E) := hcon
    haveI := (Nat.card_eq_one_iff_unique.mp hcard).1
    have h1 : σ' = 1 := congrArg Subtype.val (Subsingleton.elim (⟨σ', hmem⟩ : P.inertia _) 1)
    apply isCMExt_conj_ne_id h
    ext z
    exact DFunLike.congr_fun h1 z
  set y : 𝓞 E := σ' • x
  have hy : (y : E) = σ x := rfl
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h (x + y) (by
    show σ ((x : E) + σ x) = (x : E) + σ x
    rw [map_add, isCMExt_conj_conj h, add_comm])
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h (x * y) (by
    show σ ((x : E) * σ x) = (x : E) * σ x
    rw [map_mul, isCMExt_conj_conj h, mul_comm])
  refine ⟨x, t, n, ?_, ?_, ?_⟩
  · rw [← hy]
    exact (congrArg (fun z : 𝓞 E => (z : E)) ht).symm
  · rw [← hy]
    exact (congrArg (fun z : 𝓞 E => (z : E)) hn).symm
  · intro hmem
    have hP : algebraMap (𝓞 F) (𝓞 E) (t ^ 2 - 4 * n) ∈ P := by
      rw [← hPv] at hmem
      exact Ideal.mem_comap.mp hmem
    have heq : algebraMap (𝓞 F) (𝓞 E) (t ^ 2 - 4 * n) = (y - x) ^ 2 := by
      rw [map_sub, map_pow, map_mul, ht, hn, map_ofNat]
      ring
    rw [heq] at hP
    exact hx (hPp.mem_of_pow_mem 2 hP)
end _root_.GlobalTheory.UnramifiedDiscriminant
end GlobalTheory.UnramifiedDiscriminant
