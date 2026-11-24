-- Prove2me | solution 1 for GlobalTheory.Cyc.AlmostTrace.sum_mem_Kinf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:06:51.571913+00:00
-- url     : https://prove2.me/submissions/9021488e-abea-426c-8d3b-b36fccb16ad6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.AlmostTrace
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.AlmostTrace
theorem _root_.solution (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l))
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) {b : Om l} (hb : b ∈ L) :
    ∑ s ∈ S, s b ∈ Kinf K := by
  classical
  rw [← InfiniteGalois.fixedField_fixingSubgroup (Kinf K), IntermediateField.mem_fixedField_iff]
  intro h hh
  have hex : ∀ s ∈ S, ∃ t, t ∈ S ∧ t⁻¹ * (h * s) ∈ L.fixingSubgroup := fun s hs =>
    (hrep (h * s) (mul_mem hh (hS s hs))).exists
  choose! φ hφS hφF using hex
  rw [map_sum]
  refine Finset.sum_nbij φ hφS ?_ ?_ ?_
  · intro s₁ hs₁ s₂ hs₂ he
    have h₁ := hφF s₁ hs₁
    have h₂ := hφF s₂ hs₂
    rw [he] at h₁
    have hm : s₁⁻¹ * s₂ ∈ L.fixingSubgroup := by
      have := mul_mem (inv_mem h₁) h₂
      rwa [show ((φ s₂)⁻¹ * (h * s₁))⁻¹ * ((φ s₂)⁻¹ * (h * s₂)) = s₁⁻¹ * s₂ by group] at this
    exact (hrep s₂ (hS s₂ hs₂)).unique ⟨hs₁, hm⟩ ⟨hs₂, by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro t ht
    obtain ⟨s, ⟨hs, hsm⟩, -⟩ := hrep (h⁻¹ * t) (mul_mem (inv_mem hh) (hS t ht))
    refine ⟨s, Finset.mem_coe.2 hs, ?_⟩
    have hm : t⁻¹ * (h * s) ∈ L.fixingSubgroup := by
      have := inv_mem hsm
      rwa [show (s⁻¹ * (h⁻¹ * t))⁻¹ = t⁻¹ * (h * s) by group] at this
    exact (hrep (h * s) (mul_mem hh (hS s hs))).unique ⟨hφS s hs, hφF s hs⟩ ⟨ht, hm⟩
  · intro s hs
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hφF s hs) b hb
    have key : (φ s) (((φ s)⁻¹ * (h * s)) b) = h (s b) := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel_left, AlgEquiv.mul_apply]
    rw [hfix] at key
    exact key.symm
end GlobalTheory.Cyc.AlmostTrace
