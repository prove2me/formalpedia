-- Prove2me | solution 1 for GroundTheory.LocalField.indFun_theta_mem_spanA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:32:30.540453+00:00
-- url     : https://prove2.me/submissions/d76b8076-b89b-44aa-9fa4-14e7f7456cb7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
import Theorems.Thm_GroundTheory_LocalField_isElementaryAt_elemSub
import Theorems.Thm_GroundTheory_LocalField_quotient_mul_comm
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_apply_mem_adjoin
import Theorems.Thm_GroundTheory_LocalField_IsElementaryAt_mono
import Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_isCharacter
import Theorems.Thm_GroundTheory_LocalField_eq_sum_irrChars_of_isClassFun
import Theorems.Thm_GroundTheory_LocalField_indFun_mem_spanZ
import Theorems.Thm_GroundTheory_LocalField_mem_irrChars
import Theorems.Thm_GroundTheory_LocalField_smul_mem_spanA


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G]
variable [Fintype G] (p : ℕ) [hp : Fact p.Prime] (x : G)
variable {p x}
variable {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
  (hmono : ∀ K : Subgroup G, IsElementaryAt p K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
omit hp
include hζ hmono
namespace GroundTheory.LocalField
theorem _root_.solution (hx : (orderOf x).Coprime p) :
    indFun (elemSub p x).subtype (theta p x) ∈ spanA (G := G) (IsElementaryAt p) ζ := by
  set H := elemSub p x
  set Q := H ⧸ sylowCentIn p x
  set xb : Q := (xIn p x : Q)
  set δ : Q → ℂ := fun q ↦ if q = xb then (Nat.card Q : ℂ) else 0
  have hδ : IsClassFun δ := by
    intro g h
    simp only [δ]
    rw [quotient_mul_comm h g, mul_inv_cancel_right]
  have hN : (Nat.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcoef : ∀ ψ : Q → ℂ, charInner Q δ ψ = ψ xb⁻¹ := by
    intro ψ
    rw [charInner_apply]
    simp only [δ, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), ← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  have htheta : theta p x = δ ∘ QuotientGroup.mk' (sylowCentIn p x) := rfl
  rw [htheta, eq_sum_irrChars_of_isClassFun hδ]
  have hcomp : (∑ ψ ∈ irrChars Q, charInner Q δ ψ • ψ) ∘ QuotientGroup.mk' (sylowCentIn p x) =
      ∑ ψ ∈ irrChars Q, charInner Q δ ψ • (ψ ∘ QuotientGroup.mk' (sylowCentIn p x)) := by
    funext h
    simp [Finset.sum_apply]
  rw [hcomp, map_sum]
  refine Submodule.sum_mem _ fun ψ hψ ↦ ?_
  rw [map_smul, hcoef]
  have hψc := (mem_irrChars.mp hψ).isCharacter
  refine smul_mem_spanA ?_ (indFun_mem_spanZ (fun K L hK hLK ↦ hK.mono hLK) hmono
    (isElementaryAt_elemSub hx) (hψc.comp _))
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  refine hψc.apply_mem_adjoin _ hζ ?_
  rw [orderOf_inv]
  refine (orderOf_map_dvd (QuotientGroup.mk' (sylowCentIn p x)) (xIn p x)).trans ?_
  rw [xIn, Subgroup.orderOf_mk]
  exact orderOf_dvd_natCard x
end GroundTheory.LocalField
