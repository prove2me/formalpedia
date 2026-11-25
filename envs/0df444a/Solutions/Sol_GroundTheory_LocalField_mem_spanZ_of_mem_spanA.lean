-- Prove2me | solution 1 for GroundTheory.LocalField.mem_spanZ_of_mem_spanA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:24.843219+00:00
-- url     : https://prove2.me/submissions/b3023943-b56d-474c-9651-633044e8a719

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Theorems.Thm_GroundTheory_LocalField_isClassFun_of_mem_spanZ
import Theorems.Thm_GroundTheory_LocalField_isClassFun_of_mem_spanA
import Theorems.Thm_GroundTheory_LocalField_exists_int_charInner_of_mem_spanZ
import Theorems.Thm_GroundTheory_LocalField_eq_of_isClassFun_of_charInner
import Theorems.Thm_GroundTheory_LocalField_exists_retraction_adjoin
import Theorems.Thm_GroundTheory_LocalField_mem_irrChars


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
variable {G : Type*} [Group G] [Fintype G]
variable {E : Subgroup G → Prop}
namespace GroundTheory.LocalField
theorem _root_.solution {ζ : ℂ} (hζ : IsIntegral ℤ ζ) {f : G → ℂ} (hf : f ∈ spanA E ζ)
    (hint : ∀ ψ ∈ irrChars G, ∃ k : ℤ, charInner G f ψ = k) : f ∈ spanZ E := by
  obtain ⟨π, hπ⟩ := exists_retraction_adjoin hζ
  obtain ⟨n, c, x, hx⟩ := (Submodule.mem_span_set').mp hf
  have hS : ∀ i, ∃ a : Algebra.adjoin ℤ ({ζ} : Set ℂ), ∃ g ∈ spanZ E,
      (x i : G → ℂ) = (a : ℂ) • g := fun i ↦ by
    obtain ⟨a, ha, g, hg, h⟩ := (x i).2
    exact ⟨⟨a, ha⟩, g, hg, h⟩
  choose a g hg hxag using hS
  set f' : G → ℂ := ∑ i, (c i * π (a i)) • g i with hf'def
  have hf' : f' ∈ spanZ E := Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (hg i)
  have hfeq : f = ∑ i, c i • ((a i : ℂ) • g i) := by
    rw [← hx]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hxag i]
  suffices f = f' by rw [this]; exact hf'
  apply eq_of_isClassFun_of_charInner (isClassFun_of_mem_spanA hf) (isClassFun_of_mem_spanZ hf')
  intro ψ hψ
  obtain ⟨k, hk⟩ := hint ψ hψ
  have hn : ∀ i, ∃ m : ℤ, charInner G (g i) ψ = m := fun i ↦
    exists_int_charInner_of_mem_spanZ (hg i) (mem_irrChars.mp hψ)
  choose m hm using hn
  have h1 : charInner G f ψ = ∑ i, ((c i * m i : ℤ) : ℂ) * (a i : ℂ) := by
    rw [hfeq, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Int.cast_smul_eq_zsmul ℂ, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hm i,
      smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  have hA : (∑ i, (c i * m i) • a i) = k • (1 : Algebra.adjoin ℤ ({ζ} : Set ℂ)) := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, zsmul_eq_mul, mul_one]
    push_cast
    rw [← hk, h1]
    push_cast
    rfl
  have hπA := congrArg π hA
  rw [map_sum, map_zsmul, hπ, smul_eq_mul, mul_one] at hπA
  simp only [map_zsmul, smul_eq_mul] at hπA
  rw [hk, hf'def, map_sum, LinearMap.sum_apply]
  rw [← hπA]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Int.cast_smul_eq_zsmul ℂ, map_smul, LinearMap.smul_apply, hm i, smul_eq_mul]
  push_cast
  ring
end GroundTheory.LocalField
