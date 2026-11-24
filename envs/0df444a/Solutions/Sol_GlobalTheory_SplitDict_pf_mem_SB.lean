-- Prove2me | solution 1 for GlobalTheory.SplitDict.pf_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:26:07.496958+00:00
-- url     : https://prove2.me/submissions/4fe649e1-a92d-4629-9341-18238a767f1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd
import Theorems.Thm_GlobalTheory_SplitDict_exists_box_invariant_snd
import Theorems.Thm_GlobalTheory_SplitDict_slice_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_eq_zero_pi
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isCompact_box
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
open scoped Topology
noncomputable section
namespace GlobalTheory.SplitDict
section Partial
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {T : Type} [TopologicalSpace T] [T2Space T]
variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k]
private theorem exists_isOpen_nhd_eq_of_mem_SB {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) (t₀ : T) :
    ∃ V : Set T, IsOpen V ∧ t₀ ∈ V ∧ ∀ t ∈ V, ∀ x, f (t, x) = f (t₀, x) := by
  obtain ⟨hlc, hcs⟩ := hf
  have hW : IsOpen {p : T × (n → k) | f p - f (t₀, p.2) = 0} :=
    (hlc.sub (hlc.comp_continuous (by fun_prop))).isOpen_fiber 0
  obtain ⟨U, V, hU, -, ht₀U, hLV, hUV⟩ := generalized_tube_lemma (isCompact_singleton (x := t₀))
    (hcs.isCompact.image continuous_snd) hW (by
      rintro ⟨t, x⟩ ⟨ht, -⟩
      simp only [Set.mem_singleton_iff] at ht
      simp [ht])
  refine ⟨U, hU, ht₀U rfl, fun t ht x => ?_⟩
  by_cases hx : x ∈ Prod.snd '' tsupport f
  · have hm : (t, x) ∈ {p : T × (n → k) | f p - f (t₀, p.2) = 0} := hUV ⟨ht, hLV hx⟩
    exact sub_eq_zero.mp hm
  · have h1 : (t, x) ∉ tsupport f := fun h => hx ⟨_, h, rfl⟩
    have h2 : (t₀, x) ∉ tsupport f := fun h => hx ⟨_, h, rfl⟩
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]
end Partial
section Matrices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
end Matrices
section Homeos
variable (k : Type) [TopologicalSpace k] (ρ v τ w W : Type)
end Homeos
section Main
variable {k : Type} [Field k]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable (ψ : AddChar k Circle) (m : Measure k) [m.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (s₁ s₂ : ℤˣ)
variable {ρ v τ w W : Type} [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]
  [Fintype τ] [DecidableEq τ] [Fintype w] [DecidableEq w] [Fintype W] [DecidableEq W]
end Main
end GlobalTheory.SplitDict
end
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitDict
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {T : Type} [TopologicalSpace T] [T2Space T]
variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitDict
theorem _root_.solution (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c)
    {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) : pf ψ μ f ∈ SB (T × (n → k)) := by
  obtain ⟨s, hs⟩ := exists_box_invariant_snd hf
  have hslice : ∀ t, (fun y => ∫ x, f (t, x) * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∈ SB (n → k) :=
    fun t => fourier_mem_SB μ h (slice_mem_SB hf t)
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    rintro ⟨t₀, y₀⟩
    obtain ⟨V, hV, ht₀, hVf⟩ := exists_isOpen_nhd_eq_of_mem_SB hf t₀
    obtain ⟨O, hO, hy₀, hOf⟩ := (IsLocallyConstant.iff_exists_open _).mp (hslice t₀).1 y₀
    refine ⟨V ×ˢ O, hV.prod hO, ⟨ht₀, hy₀⟩, ?_⟩
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    have e1 : pf ψ μ f (t, y) = pf ψ μ f (t₀, y) := by
      simp only [pf]
      congr 1
      funext x
      rw [hVf t ht x]
    rw [e1]
    exact hOf y hy
  · haveI := t2Space k
    refine HasCompactSupport.intro
      ((hf.2.isCompact.image continuous_fst).prod (isCompact_box (c * s⁻¹))) ?_
    rintro ⟨t, y⟩ hty
    rw [Set.mem_prod, not_and_or] at hty
    rcases hty with ht | hy
    · have h0 : ∀ x, f (t, x) = 0 := fun x =>
        image_eq_zero_of_notMem_tsupport fun hx => ht ⟨_, hx, rfl⟩
      simp [pf, h0]
    · show ∫ x, f (t, x) * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = 0
      exact fourier_eq_zero_pi μ h (f := fun x => f (t, x)) (fun u hu x => hs u hu (t, x)) hy
end GlobalTheory.SplitDict
