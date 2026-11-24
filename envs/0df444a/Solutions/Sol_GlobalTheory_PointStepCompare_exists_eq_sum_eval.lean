-- Prove2me | solution 1 for GlobalTheory.PointStepCompare.exists_eq_sum_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:27:14.122503+00:00
-- url     : https://prove2.me/submissions/eb52fd9d-bfb6-4c7d-9c84-23b5cef21f57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumPosOfTensorPos
import Theorems.Thm_GlobalTheory_PointStepCompare_evalOn_tensorCoord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PointStepCompare
open NumberField Matrix
open scoped MatrixOrder
namespace GlobalTheory.PointStepCompare
theorem _root_.solution : ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (S : Submodule ℝ (Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)), (∀ γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ, (∀ a b c d : Y, (∀ β ∈ S, β a b = β c d) → γ a b = γ c d) → γ ∈ S) → ∀ l : S →ₗ[ℝ] ℝ, (∀ β : S, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) → ∃ (m : ℕ) (x x' : Fin m → Y), ∀ β : S, l β = ∑ i, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) (x' i) := by
  intro Y _ _ _ S hS l hl
  classical
  let b := Module.Free.chooseBasis ℤ Y
  let A : Submodule ℤ (_ × _ → ℤ) := ⨅ β : S, LinearMap.ker (evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ))
  have hA : ∀ n, n ∈ A ↔ ∀ β : S, evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) n = 0 := fun n => by
    simp [A, Submodule.mem_iInf]
  have : NoZeroSMulDivisors ℤ ((_ × _ → ℤ) ⧸ A) := by
    refine ⟨fun {k q} h => ?_⟩
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_cases hk : k = 0
    · exact Or.inl hk
    right
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hA] at h
    rw [Submodule.Quotient.mk_eq_zero, hA]
    intro β
    have h1 := h β
    rw [map_zsmul, zsmul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left (by exact_mod_cast hk)
  have : Module.Free ℤ ((_ × _ → ℤ) ⧸ A) := Module.free_of_finite_type_torsion_free'
  let eb := Module.Free.chooseBasis ℤ ((_ × _ → ℤ) ⧸ A)
  let γ : Module.Free.ChooseBasisIndex ℤ ((_ × _ → ℤ) ⧸ A) → Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ := fun k =>
    (tensorCoord b).compr₂ ((Int.castAddHom ℝ).toIntLinearMap ∘ₗ eb.coord k ∘ₗ A.mkQ)
  have hγ : ∀ k x y, γ k x y = (eb.repr (Submodule.Quotient.mk (tensorCoord b x y)) k : ℤ) :=
    fun _ _ _ => rfl
  have hγS : ∀ k, γ k ∈ S := fun k => hS _ fun x y x' y' h => by
    have e : Submodule.Quotient.mk (p := A) (tensorCoord b x y) =
        Submodule.Quotient.mk (tensorCoord b x' y') := (Submodule.Quotient.eq A).2 ((hA _).2 fun β => by
      rw [map_sub, evalOn_tensorCoord, evalOn_tensorCoord, h β β.2, sub_self])
    rw [hγ, hγ, e]
  choose z hz using fun k => hl ⟨γ k, hγS k⟩ fun x y => ⟨_, hγ k x y⟩
  obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective A (∑ k, z k • eb k)
  let e := (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ Y × Module.Free.ChooseBasisIndex ℤ Y)).symm
  refine ⟨_, fun t => n (e t) • b (e t).1, fun t => b (e t).2, fun β => ?_⟩
  have hR : ∑ t, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (n (e t) • b (e t).1) (b (e t).2) =
      evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) n := by
    rw [e.sum_comp (fun p => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (n p • b p.1) (b p.2))]
    simp [evalOn, zsmul_eq_mul]
  rw [hR]
  let ψ := A.liftQ (evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)) (iInf_le _ β)
  have hψ : ∀ m, ψ (Submodule.Quotient.mk m) = evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) m := fun m =>
    Submodule.liftQ_apply _ _ _
  have hβ : β = ∑ k, ψ (eb k) • (⟨γ k, hγS k⟩ : S) := by
    apply Subtype.ext
    apply LinearMap.ext₂
    intro x y
    rw [Submodule.coe_sum, LinearMap.sum_apply, LinearMap.sum_apply]
    simp only [Submodule.coe_smul, LinearMap.smul_apply, hγ, smul_eq_mul]
    rw [← evalOn_tensorCoord b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) x y, ← hψ]
    conv_lhs => rw [← eb.sum_repr (Submodule.Quotient.mk (tensorCoord b x y))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  rw [congrArg l hβ, map_sum, ← hψ, hn, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, hz, smul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
end GlobalTheory.PointStepCompare
