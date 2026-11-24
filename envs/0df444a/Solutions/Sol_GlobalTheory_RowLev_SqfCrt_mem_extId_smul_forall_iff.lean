-- Prove2me | solution 1 for GlobalTheory.RowLev.SqfCrt.mem_extId_smul_forall_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:47:01.343001+00:00
-- url     : https://prove2.me/submissions/baf3b929-c5ec-4199-8b09-ec797dcdb639

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsProdLeOfIsRadical
import Theorems.Thm_GlobalTheory_RowLev_SqfCrt_mem_prod_smul_of_coprime
import Theorems.Thm_GlobalTheory_RowLev_SqfCrt_exists_prod_le_of_isRadical
import Theorems.Thm_GlobalTheory_RowLev_SqfCrt_extId_eq_image
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
namespace GlobalTheory.RowLev.SqfCrt
private theorem isCoprime_map_of_ne {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S]
    (f : R →+* S) {u v : HeightOneSpectrum R} (huv : u ≠ v) :
    IsCoprime (u.asIdeal.map f) (v.asIdeal.map f) := by
  have hmax : u.asIdeal ⊔ v.asIdeal = ⊤ :=
    u.isMaximal.coprime_of_ne v.isMaximal fun e => huv (HeightOneSpectrum.ext e)
  rw [Ideal.isCoprime_iff_sup_eq, ← Ideal.map_sup, hmax, Ideal.map_top]
private theorem prod_map_le_map_of_prod_le {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (T : Finset (HeightOneSpectrum R)) {𝔞 : Ideal R} (hle : ∏ u ∈ T, u.asIdeal ≤ 𝔞) :
    ∏ u ∈ T, u.asIdeal.map f ≤ 𝔞.map f := by
  have hprod : ∀ T' : Finset (HeightOneSpectrum R),
      ∏ u ∈ T', u.asIdeal.map f = (∏ u ∈ T', u.asIdeal).map f := by
    intro T'
    induction T' using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.prod_empty, Ideal.one_eq_top, Ideal.one_eq_top, Ideal.map_top]
    | @insert a T' haT ih => rw [Finset.prod_insert haT, Finset.prod_insert haT, Ideal.map_mul, ih]
  rw [hprod]
  exact Ideal.map_mono hle
private theorem mem_map_smul_of_forall_mem_map_smul {R S M : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S]
    [AddCommGroup M] [Module S M] (f : R →+* S) (N : Submodule S M) {𝔞 : Ideal R} (h0 : 𝔞 ≠ ⊥)
    (hr : 𝔞.IsRadical) {y : M} (hy : y ∈ N)
    (h : ∀ u : HeightOneSpectrum R, 𝔞 ≤ u.asIdeal → y ∈ u.asIdeal.map f • N) : y ∈ 𝔞.map f • N := by
  obtain ⟨T, hT, hle⟩ := exists_prod_le_of_isRadical h0 hr
  have hmem : y ∈ (∏ u ∈ T, u.asIdeal.map f) • N :=
    mem_prod_smul_of_coprime (ι := HeightOneSpectrum R) N (fun u => u.asIdeal.map f)
      (fun _ _ huv => isCoprime_map_of_ne f huv) hy T fun u hu => h u (hT u hu)
  exact Submodule.smul_mono_left (prod_map_le_map_of_prod_le f T hle) hmem
end GlobalTheory.RowLev.SqfCrt
end

set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev GlobalTheory.RowLev.SqfCrt
namespace GlobalTheory.RowLev.SqfCrt
theorem _root_.solution : ∀ (I : AutInst) (m : ℕ), 1 ≤ m → (Ideal.span {(m : 𝓞 I.E)}).IsRadical →
    ∀ y ∈ I.Lf, (∀ u : HeightOneSpectrum (𝓞 I.E), (m : 𝓞 I.E) ∈ u.asIdeal → y ∈ extId I u.asIdeal • I.Lf) ↔
      ∃ z ∈ I.Lf, y = (m : (I.E ⊗[I.F] Af I.F)) • z := by
  intro I m hm hrad y hy
  constructor
  · intro h
    have h0 : Ideal.span {(m : 𝓞 I.E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (by omega)
    have key : y ∈ (Ideal.span {(m : 𝓞 I.E)}).map (Inhab.psi I.F I.E) • I.Lf :=
      mem_map_smul_of_forall_mem_map_smul (Inhab.psi I.F I.E) I.Lf h0 hrad hy fun u hu => by
        rw [← extId_eq_image I]
        exact h u (hu (Ideal.mem_span_singleton_self _))
    rw [Ideal.map_span, Set.image_singleton, map_natCast, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at key
    obtain ⟨z, hz, hzy⟩ := key
    refine ⟨z, hz, ?_⟩
    rw [← hzy, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  · rintro ⟨z, hz, rfl⟩ u hu
    have hm' : (m : IntAf I.F I.E) ∈ extId I u.asIdeal := by
      rw [extId_eq_image, ← map_natCast (Inhab.psi I.F I.E)]
      exact Ideal.mem_map_of_mem _ hu
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (IntAf I.F I.E)]
    exact Submodule.smul_mem_smul hm' hz
end GlobalTheory.RowLev.SqfCrt
