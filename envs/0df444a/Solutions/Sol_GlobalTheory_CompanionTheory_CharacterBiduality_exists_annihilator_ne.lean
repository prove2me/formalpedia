-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:38:10.620815+00:00
-- url     : https://prove2.me/submissions/c4a73e20-549e-4bc6-8bdd-6b29a44dd8b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCharacterSeparatingLattice
import Theorems.Thm_GlobalTheory_CompanionTheory_CharacterBiduality_indicator_mem_SB
import Theorems.Thm_GlobalTheory_CompanionTheory_CharacterBiduality_fourier_sub_translate_eq_zero
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_inversion_pi
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isCompact_box
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isOpen_box
import Theorems.Thm_GlobalTheory_SplitWeil_exists_hasConductor_of_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CharacterBiduality
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.CharacterBiduality
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) →
    IsOpen (A : Set (Fin n → k)) → ∀ x : Fin n → k, x ∉ A →
    ∃ η : Fin n → k, (∀ a ∈ A, ψ (η ⬝ᵥ a) = 1) ∧ ψ (η ⬝ᵥ x) ≠ 1 := by
  intro k _ _ _ _ ψ hψ h1 n A hAc hAo x hxA
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := secondCountable k
  haveI := t2Space k
  let μ : Measure (Fin n → k) := Measure.addHaar
  set g : (Fin n → k) → ℂ := (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) with hgdef
  have hg : g ∈ SB (Fin n → k) := indicator_mem_SB A hAc hAo
  have hgx : (fun z => g (z + x)) ∈ SB (Fin n → k) :=
    ⟨hg.1.comp_continuous (continuous_id.add continuous_const),
      hg.2.comp_homeomorph (Homeomorph.addRight x)⟩
  have hf : (fun z => g z - g (z + x)) ∈ SB (Fin n → k) := (SB (Fin n → k)).sub_mem hg hgx
  obtain ⟨s, hs⟩ := fourier_inversion_pi μ hc hf
  have hz : ∀ y : Fin n → k, ∫ z, (g z - g (z + x)) * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 :=
    fourier_sub_translate_eq_zero ψ hψ μ A hAc hAo x hcon
  simp only [hz, integral_zero] at hs
  have hpos : ∀ r : kˣ, 0 < μ.real (box (Fin n) r) := fun r => by
    have h1 : (0 : Fin n → k) ∈ box (Fin n) r := fun i _ => by simp [cball]
    have h2 : 0 < μ (box (Fin n) r) := (isOpen_box r).measure_pos μ ⟨0, h1⟩
    exact ENNReal.toReal_pos h2.ne' (isCompact_box r).measure_lt_top.ne
  have hne : ((μ.real (box (Fin n) s) * μ.real (box (Fin n) (c * s⁻¹)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos (hpos s) (hpos _)).ne'
  have h0 : g 0 - g (0 + x) = 0 := (mul_eq_zero.mp hs.symm).resolve_left hne
  have hg0 : g 0 = 1 := Set.indicator_of_mem (SetLike.mem_coe.2 A.zero_mem) _
  have hgx0 : g (0 + x) = 0 := by
    rw [zero_add]
    exact Set.indicator_of_notMem (fun h => hxA h) _
  rw [hg0, hgx0] at h0
  simp at h0
end GlobalTheory.CompanionTheory.CharacterBiduality
