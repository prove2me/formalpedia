-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SchurChar.apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:11:05.843913+00:00
-- url     : https://prove2.me/submissions/61cf2871-8dfc-4a5c-9bf2-504b1703a60a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AdelicProofs_SchurTranslationsCharacters
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SchurChar_comm_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SchurChar_comm_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SchurChar_comm_sub_const
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SchurChar_char_locConst

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SchurChar
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
  {χ : V → V → ℂ} {μ : Measure V}
namespace GlobalTheory.CompanionTheory.SW.SchurChar
theorem _root_.solution (h : NADual V χ μ) {T : (V → ℂ) → (V → ℂ)}
    (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsmul : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ)
    (hchar : ∀ y φ, SB φ → T (fun u => χ u y * φ u) = fun u => χ u y * T φ u)
    {φ : V → ℂ} (hφ : SB φ) {x : V} (hx : φ x = 0) : T φ x = 0 := by
  have hcomm : ∀ y, Comm T (fun u => χ u y) := fun y => ⟨char_locConst h y, fun φ hφ => hchar y φ hφ⟩
  obtain ⟨hTG, -, -, -, -, -, hsmall, -, -, hsymm, hnorm, hχadd, hperp⟩ := h
  haveI := hTG
  have hS : IsCompact (tsupport φ) := hφ.2
  have hxS : x ∉ tsupport φ := by
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [hφ.1.eventually_eq x] with u hu
    simp [hu, hx]
  have hnb : {w : V | x + w ∈ (tsupport φ)ᶜ} ∈ 𝓝 (0 : V) := by
    have hc : ContinuousAt (fun w : V => x + w) 0 := by fun_prop
    apply hc.preimage_mem_nhds
    simpa using (isClosed_tsupport φ).isOpen_compl.mem_nhds hxS
  obtain ⟨L, hLc, hLo, hLU⟩ := hsmall _ hnb
  obtain ⟨-, -, hpp, -⟩ := hperp L hLc hLo
  have key : ∃ m, Comm T m ∧ m x ≠ 0 ∧ ∀ u ∈ tsupport φ, m u = 0 := by
    refine hS.induction_on (p := fun A => ∃ m, Comm T m ∧ m x ≠ 0 ∧ ∀ u ∈ A, m u = 0) ?_ ?_ ?_ ?_
    · exact ⟨fun _ => 1, comm_one T, one_ne_zero, by simp⟩
    · rintro A B hAB ⟨m, hm, hmx, hm0⟩
      exact ⟨m, hm, hmx, fun u hu => hm0 u (hAB hu)⟩
    · rintro A B ⟨m, hm, hmx, hm0⟩ ⟨m', hm', hmx', hm0'⟩
      refine ⟨_, comm_mul hm hm', mul_ne_zero hmx hmx', ?_⟩
      rintro u (hu | hu)
      · simp [hm0 u hu]
      · simp [hm0' u hu]
    · intro s hs
      have hsL : s - x ∉ (L : Set V) := by
        intro hmem
        have := hLU hmem
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, add_sub_cancel] at this
        exact this hs
      have hz : ∃ z ∈ perp χ L, χ z (s - x) ≠ 1 := by
        by_contra hcon
        push_neg at hcon
        exact hsL (hpp fun z hz => hcon z hz)
      obtain ⟨z, hzL, hzne⟩ := hz
      have hzne' : χ (s - x) z ≠ 1 := by rwa [hsymm]
      have hxz : χ x z ≠ 0 := by
        intro h0; have := hnorm x z; rw [h0] at this; simp at this
      have hopen : {u : V | u - s ∈ (L : Set V)} ∈ 𝓝 s := by
        have hc : ContinuousAt (fun u : V => u - s) s := by fun_prop
        apply hc.preimage_mem_nhds
        simpa using hLo.mem_nhds L.zero_mem
      refine ⟨{u : V | u - s ∈ (L : Set V)}, mem_nhdsWithin_of_mem_nhds hopen,
        fun u => χ u z - χ s z, comm_sub_const hadd hsmul (hcomm z) _, ?_, ?_⟩
      · intro hzero
        apply hzne'
        have e : χ s z = χ (s - x) z * χ x z := by
          rw [← hχadd]; simp
        have e2 : χ x z = χ (s - x) z * χ x z := by
          rw [← e]; exact sub_eq_zero.mp hzero
        exact (mul_eq_right₀ hxz).mp e2.symm
      · intro u hu
        have h1 : χ (u - s) z = 1 := hzL _ hu
        have e : χ u z = χ (u - s) z * χ s z := by
          rw [← hχadd]; simp
        show χ u z - χ s z = 0
        rw [e, h1, one_mul, sub_self]
  obtain ⟨m, hm, hmx, hm0⟩ := key
  have e : (fun u => m u * φ u) = (0 : ℂ) • φ := by
    funext u
    by_cases hu : u ∈ tsupport φ
    · simp [hm0 u hu]
    · simp [image_eq_zero_of_notMem_tsupport hu]
  have h2 := hm.2 φ hφ
  rw [e, hsmul 0 φ hφ] at h2
  have h3 := congrFun h2 x
  simp only [Pi.smul_apply, Pi.zero_apply, zero_smul, smul_eq_mul, zero_mul] at h3
  exact (mul_eq_zero.mp h3.symm).resolve_left hmx
end GlobalTheory.CompanionTheory.SW.SchurChar
