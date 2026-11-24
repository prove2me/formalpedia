-- Prove2me | solution 1 for GlobalTheory.CuspGL.exists_int_retraction_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:25:07.712859+00:00
-- url     : https://prove2.me/submissions/86c2a16b-3e39-408e-ae16-edcdeef1b211

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIntRelationOfIsIntegralRelation
import Theorems.Thm_GlobalTheory_CuspGL_exists_int_eq_of_isIntegral_of_mul_eq_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution :
    ∀ (ι : Type) [Fintype ι] (r : ι → ℂ), (∀ i, IsIntegral ℤ (r i)) →
      ∃ c : ι → ℤ, ∀ (m : ι → ℤ) (d : ℤ), ∑ i, r i * (m i : ℂ) = d → ∑ i, c i * m i = d := by
  intro ι _ r hr
  classical
  let f : (ι → ℤ) →ₗ[ℤ] ℂ := Fintype.linearCombination ℤ r
  have hf : ∀ m, f m = ∑ i, r i * (m i : ℂ) := by
    intro m
    simp [f, Fintype.linearCombination_apply, mul_comm]
  have hfi : ∀ m, IsIntegral ℤ (f m) := by
    intro m
    rw [hf]
    refine IsIntegral.sum _ fun i _ => (hr i).mul ?_
    exact isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := m i)
  let K : Submodule ℤ (ι → ℤ) := (LinearMap.range (Algebra.linearMap ℤ ℂ)).comap f
  have hK : ∀ m, m ∈ K ↔ ∃ j : ℤ, (j : ℂ) = f m := by
    intro m
    simp [K]
  have : Module.IsTorsionFree ℤ ((ι → ℤ) ⧸ K) := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro n x hx
    by_cases hn : n = 0
    · exact Or.inl hn
    right
    obtain ⟨m, rfl⟩ := K.mkQ_surjective x
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hK] at hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hK]
    obtain ⟨k, hk⟩ := hx
    refine exists_int_eq_of_isIntegral_of_mul_eq_int (hfi m) hn (k := k) ?_
    rw [hk, map_smul, zsmul_eq_mul]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property K.mkQ (LinearMap.id) K.mkQ_surjective
  let p : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) := LinearMap.id - s ∘ₗ K.mkQ
  have hp : ∀ m, p m ∈ K := by
    intro m
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have := LinearMap.congr_fun hs (K.mkQ m)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [p, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub, this,
      sub_self]
  have hp' : ∀ m ∈ K, p m = m := by
    intro m hm
    have : K.mkQ m = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hm
    simp only [p, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, this, map_zero,
      sub_zero]
  choose c hc using fun i : ι => (hK _).mp (hp (Pi.single i 1))
  refine ⟨c, fun m d h => ?_⟩
  have hm : m ∈ K := (hK m).mpr ⟨d, by rw [hf, h]⟩
  have hdec : m = ∑ i, m i • (Pi.single i 1 : ι → ℤ) := by
    ext j
    simp [Pi.single_apply]
  have key : ((∑ i, c i * m i : ℤ) : ℂ) = f (p m) := by
    conv_rhs => rw [hdec]
    rw [map_sum, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, ← hc, zsmul_eq_mul, mul_comm]
  rw [hp' m hm, hf, h] at key
  exact_mod_cast key
end GlobalTheory.CuspGL
