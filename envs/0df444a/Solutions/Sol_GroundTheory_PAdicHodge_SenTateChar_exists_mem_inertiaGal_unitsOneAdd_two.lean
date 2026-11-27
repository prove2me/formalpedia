-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SenTateChar.exists_mem_inertiaGal_unitsOneAdd_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:51:42.609252+00:00
-- url     : https://prove2.me/submissions/8121e1cc-e672-49db-a437-10c1dc9c5e90

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharUnits
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharClosure
import Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_isOpen_unitsOneAdd
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField
variable {p : ℕ} [hp : Fact p.Prime]
open GroundTheory.PAdicHodge.SenTateChar
open SenTateChar
namespace GroundTheory.PAdicHodge.SenTateChar
theorem _root_.solution (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ) (hη : Continuous η)
    (hinf : (η '' (inertiaGal K : Set Gal(PadicAlgCl p/K))).Infinite) :
    ∃ τ ∈ inertiaGal K, η τ ∈ unitsOneAdd p 2 ∧ η τ ≠ 1 := by
  by_contra hne
  push Not at hne
  apply hinf
  set U : Subgroup Gal(PadicAlgCl p/K) := (unitsOneAdd p 2).comap η
  have hU : IsOpen (U : Set Gal(PadicAlgCl p/K)) := (isOpen_unitsOneAdd 2).preimage hη
  have hfin : Finite (Gal(PadicAlgCl p/K) ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  classical

  let f : Gal(PadicAlgCl p/K) ⧸ U → ℤ_[p]ˣ := fun c =>
    if h : ∃ τ ∈ inertiaGal K, (τ : Gal(PadicAlgCl p/K) ⧸ U) = c then η h.choose else 1
  refine (Set.finite_range f).subset ?_
  rintro _ ⟨τ, hτ, rfl⟩
  refine ⟨(τ : Gal(PadicAlgCl p/K) ⧸ U), ?_⟩
  have h : ∃ τ' ∈ inertiaGal K, (τ' : Gal(PadicAlgCl p/K) ⧸ U) = τ := ⟨τ, hτ, rfl⟩
  simp only [f, dif_pos h]
  obtain ⟨hτ', hτ'U⟩ := h.choose_spec
  have hq : (h.choose)⁻¹ * τ ∈ U := QuotientGroup.eq.1 hτ'U
  have hI : (h.choose)⁻¹ * τ ∈ inertiaGal K := mul_mem (inv_mem hτ') hτ
  have h1 : η ((h.choose)⁻¹ * τ) = 1 := hne _ hI hq
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1
end GroundTheory.PAdicHodge.SenTateChar
