-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.DenSum.fibre_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:15:24.881113+00:00
-- url     : https://prove2.me/submissions/62c8da40-37c1-4445-a3e3-ef66d001246d

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CountableIdealSummableAbsNormRpow
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DenominatorPowerSummable
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_DenSum_mem_dI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.DenSum
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.DenSum
theorem _root_.solution (N : ℕ) (hN : 0 < N) (s : Set F)
    (hs : ∀ b ∈ s, ∀ b' ∈ s, (∃ r : 𝓞 F, b - b' = (N : F) * (r : F)) → b = b')
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    Finite {b : s // dI (b : F) = I} ∧
      Nat.card {b : s // dI (b : F) = I} ≤ N ^ Module.finrank ℤ (𝓞 F) * Ideal.absNorm I := by
  classical
  obtain ⟨a, ha_def⟩ : ∃ a : ℕ, a = Ideal.absNorm I := ⟨_, rfl⟩
  have ha0 : a ≠ 0 := by rw [ha_def, Ne, Ideal.absNorm_eq_zero_iff]; exact hI
  have haI : (a : 𝓞 F) ∈ I := by rw [ha_def]; exact Ideal.absNorm_mem I
  obtain ⟨C, hC⟩ : I ∣ Ideal.span {(a : 𝓞 F)} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem I).mpr haI)
  have hspan_ne : Ideal.span {(a : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast ha0
  have hC0 : C ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hC
    exact hspan_ne hC
  have hex : ∀ b : {b : s // dI (b : F) = I}, ∃ t : 𝓞 F, (t : F) = (a : F) * ((b : s) : F) := by
    rintro ⟨b, hb⟩
    have hm : (a : 𝓞 F) ∈ dI (b : F) := by rw [hb]; exact haI
    obtain ⟨t, ht⟩ := mem_dI.mp hm
    exact ⟨t, by rw [ht]; push_cast; rfl⟩
  choose t ht using hex
  have htC : ∀ b, t b ∈ C := by
    intro b
    have hle : Ideal.span {t b} * I ≤ I * C := by
      rw [← hC, Ideal.span_singleton_mul_le_iff]
      intro z hz
      have hz' : z ∈ dI ((b : s) : F) := by rw [b.2]; exact hz
      obtain ⟨u, hu⟩ := mem_dI.mp hz'
      rw [Ideal.mem_span_singleton']
      refine ⟨u, ?_⟩
      apply IsFractionRing.injective (𝓞 F) F
      have hu' : algebraMap (𝓞 F) F u = algebraMap (𝓞 F) F z * ((b : s) : F) := hu
      have ht' : algebraMap (𝓞 F) F (t b) = (a : F) * ((b : s) : F) := ht b
      rw [map_mul, map_mul, map_natCast, hu', ht']
      ring
    have hdvd : I * C ∣ I * Ideal.span {t b} := by
      rw [mul_comm I (Ideal.span _)]
      exact Ideal.dvd_iff_le.mpr hle
    have h2 := (mul_dvd_mul_iff_left hI).mp hdvd
    exact (Ideal.span_singleton_le_iff_mem C).mp (Ideal.dvd_iff_le.mp h2)
  let H : AddSubgroup (𝓞 F) := (Ideal.span {((a * N : ℕ) : 𝓞 F)}).toAddSubgroup
  let K : AddSubgroup (𝓞 F) := C.toAddSubgroup
  have haC : (a : 𝓞 F) ∈ C := by
    have h1 : (a : 𝓞 F) ∈ I * C := by rw [← hC]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_left : C * I ≤ C) (by rwa [mul_comm] at h1)
  have hHK : H ≤ K := by
    intro x hx
    have hle : Ideal.span {((a * N : ℕ) : 𝓞 F)} ≤ C := by
      rw [Ideal.span_singleton_le_iff_mem]
      push_cast
      exact C.mul_mem_right _ haC
    exact hle hx
  let Φ : {b : s // dI (b : F) = I} → K ⧸ H.addSubgroupOf K := fun b => QuotientAddGroup.mk ⟨t b, htC b⟩
  have hΦ : Function.Injective Φ := by
    intro b b' hbb
    have hmem := QuotientAddGroup.eq.mp hbb
    rw [AddSubgroup.mem_addSubgroupOf] at hmem
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
    have hr' : r * ((a * N : ℕ) : 𝓞 F) = -t b + t b' := by simpa using hr
    have h1 := congrArg (algebraMap (𝓞 F) F) hr'
    have htb : algebraMap (𝓞 F) F (t b) = (a : F) * ((b.1 : s) : F) := ht b
    have htb' : algebraMap (𝓞 F) F (t b') = (a : F) * ((b'.1 : s) : F) := ht b'
    simp only [map_mul, map_add, map_neg, map_natCast, Nat.cast_mul, htb, htb'] at h1
    have hrF : algebraMap (𝓞 F) F r = (r : F) := rfl
    rw [hrF] at h1
    have ha' : (a : F) ≠ 0 := by exact_mod_cast ha0
    have key : ((b'.1 : s) : F) - ((b.1 : s) : F) = (N : F) * (r : F) := by
      apply mul_left_cancel₀ ha'
      linear_combination -h1
    have := hs _ b'.1.2 _ b.1.2 ⟨r, key⟩
    exact Subtype.ext (Subtype.ext this.symm)
  have hnormNat : ∀ m : ℕ, Ideal.absNorm (Ideal.span {(m : 𝓞 F)}) = m ^ Module.finrank ℤ (𝓞 F) := by
    intro m
    rw [Ideal.absNorm_span_singleton]
    have hm : (m : 𝓞 F) = algebraMap ℤ (𝓞 F) (m : ℤ) := by simp
    rw [hm, Algebra.norm_algebraMap]
    simp [Int.natAbs_pow]
  have hrel : H.relIndex K = N ^ Module.finrank ℤ (𝓞 F) * a := by
    have h1 := AddSubgroup.relIndex_mul_index hHK
    have hKi : K.index = Ideal.absNorm C := by rw [Ideal.absNorm_apply]; rfl
    have hHi : H.index = (a * N) ^ Module.finrank ℤ (𝓞 F) := by
      have h3 : H.index = Ideal.absNorm (Ideal.span {((a * N : ℕ) : 𝓞 F)}) := by rw [Ideal.absNorm_apply]; rfl
      rw [h3, hnormNat]
    have hmul : Ideal.absNorm (Ideal.span {(a : 𝓞 F)}) = a * Ideal.absNorm C := by rw [hC, map_mul, ha_def]
    have hC0' : Ideal.absNorm C ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    rw [hKi, hHi] at h1
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hC0')
    rw [h1, mul_pow, ← hnormNat a, hmul]
    ring
  haveI hfinQ : Finite (K ⧸ H.addSubgroupOf K) := Nat.finite_of_card_ne_zero (by
    show H.relIndex K ≠ 0
    rw [hrel]
    exact Nat.mul_ne_zero (pow_ne_zero _ hN.ne') ha0)
  refine ⟨Finite.of_injective Φ hΦ, ?_⟩
  calc Nat.card {b : s // dI (b : F) = I} ≤ Nat.card (K ⧸ H.addSubgroupOf K) := Nat.card_le_card_of_injective Φ hΦ
    _ = N ^ Module.finrank ℤ (𝓞 F) * Ideal.absNorm I := by
      show H.relIndex K = _
      rw [hrel, ha_def]
end GlobalTheory.CompanionTheory.SW.DenSum
