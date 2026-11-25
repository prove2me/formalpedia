-- Prove2me | solution 1 for GlobalTheory.NormOneSplit.mem_span_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:33.369184+00:00
-- url     : https://prove2.me/submissions/93936e0f-e263-4f01-ac1e-17f3aa6351de

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsForallHomEq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
namespace GlobalTheory.NormOneSplit
open NumberField Module Matrix in
open scoped ENNReal in
private theorem exists_ringHom_zmod_ker_eq {E : Type} [Field E] [NumberField E] {T : ℕ}
    (hT : T.Prime) (P : Ideal (𝓞 E)) (hP : P.IsMaximal) (hN : Ideal.absNorm P = T) :
    ∃ φ : 𝓞 E →+* ZMod T, RingHom.ker φ = P := by
  letI := Ideal.Quotient.field P
  have hcard : Nat.card (𝓞 E ⧸ P) = T := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hN]
  haveI : Finite (𝓞 E ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hT.ne_zero)
  letI := Fintype.ofFinite (𝓞 E ⧸ P)
  let e := ZMod.ringEquivOfPrime (𝓞 E ⧸ P) hT (by rw [Fintype.card_eq_nat_card, hcard])
  refine ⟨(e.symm : (𝓞 E ⧸ P) →+* ZMod T).comp (Ideal.Quotient.mk P), ?_⟩
  ext x
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
end GlobalTheory.NormOneSplit
end

set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory GlobalTheory.NormOneSplit
open NumberField Module Matrix
open scoped ENNReal
namespace GlobalTheory.NormOneSplit
namespace _root_.GlobalTheory.NormOneSplit
theorem _root_.solution {E : Type} [Field E] [NumberField E] {T : ℕ}
    (hT : T.Prime)
    (hs : ∀ P : Ideal (𝓞 E), P.IsMaximal → ((T : 𝓞 E) ∈ P) →
      Ideal.absNorm P = T ∧ (T : 𝓞 E) ∉ P ^ 2) (x : 𝓞 E) :
    x ∈ Ideal.span {(T : 𝓞 E)} ↔ ∀ φ : 𝓞 E →+* ZMod T, φ x = 0 := by
  constructor
  · intro hx φ
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    simp
  · intro h
    set I := Ideal.span {(T : 𝓞 E)} with hI
    have hT0 : (T : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne_zero
    have hTI : (T : 𝓞 E) ∈ I := Ideal.mem_span_singleton_self _
    obtain ⟨K, hK⟩ : I.radical ∣ I := Ideal.dvd_iff_le.mpr Ideal.le_radical
    have hKtop : K = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hKM⟩ := Ideal.exists_le_maximal K hne
      have hIM : I ≤ M := by
        rw [hK]; exact le_trans (Ideal.mul_le.mpr fun a _ b hb => K.mul_mem_left a hb) hKM
      have hrad : I.radical ≤ M := (Ideal.IsPrime.radical_le_iff hM.isPrime).2 hIM
      have hle : I ≤ M ^ 2 := by
        rw [hK, pow_two]; exact Ideal.mul_mono hrad hKM
      exact (hs M hM (hIM hTI)).2 (hle hTI)
    rw [hKtop, Ideal.mul_top] at hK
    rw [hK, Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hIP, hP⟩
    have hPbot : P ≠ ⊥ := fun hb => hT0 (by simpa [hb] using hIP hTI)
    have hPmax := hP.isMaximal hPbot
    obtain ⟨φ, hφ⟩ := exists_ringHom_zmod_ker_eq hT P hPmax (hs P hPmax (hIP hTI)).1
    rw [← hφ, RingHom.mem_ker]
    exact h φ
end _root_.GlobalTheory.NormOneSplit
end GlobalTheory.NormOneSplit
