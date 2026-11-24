-- Prove2me | solution 1 for GlobalTheory.SplitLift.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:10:49.465891+00:00
-- url     : https://prove2.me/submissions/0851e5a4-244f-4b42-86b1-b393ee97d644

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnitaryStabilizerLiftOfSplitIdempotent
import Theorems.Thm_GlobalTheory_SplitLift_exists_gen
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.SplitLift
open Formalism.UG
variable {A : Type} [CommRing A] {n : ℕ}
namespace GlobalTheory.SplitLift
theorem _root_.solution (S : Subring A) (Λ : Submodule S (Fin n → A)) {k : Type} [Field k]
    (r : S →+* k) (c : Λ →ₛₗ[r] (Fin n → k)) (ε : S) (hfg : Λ.FG)
    (hsp : Submodule.span A (Λ : Set (Fin n → A)) = ⊤)
    (hε : ε * ε = ε) (hrε : r ε = 1)
    (hr : Function.Surjective r) (hloc : ∀ z : S, r z ≠ 0 → ∃ t : S, z * t * ε = ε)
    (hc : Function.Surjective c)
    (hker : ∀ y : Λ, c y = 0 → (y : Fin n → A) ∈ RingHom.ker r • Λ) :
    ∃ B B' : Matrix (Fin n) (Fin n) A, B * B' = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) ∧
      B' * B = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) ∧ (ε : A) • B = B ∧ (ε : A) • B' = B' ∧
      (∀ y : Λ, ∃ a : Fin n → S, B' *ᵥ (y : Fin n → A) = (fun i => (a i : A)) ∧
        c y = fun i => r (a i)) ∧
      ∀ a : Fin n → S, ∃ y : Λ, B *ᵥ (fun i => (a i : A)) = y ∧ c y = fun i => r (a i) := by
  obtain ⟨μ, h1, h2, h3⟩ := exists_gen S Λ r c ε hfg hε hrε hr hloc hc hker
  have hεA : (ε : A) * ε = ε := by exact_mod_cast congrArg Subtype.val hε
  let B : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => (μ j : Fin n → A) i
  have hB : ∀ a : Fin n → S, B *ᵥ (fun i => (a i : A)) = ((∑ i, a i • μ i : Λ) : Fin n → A) := by
    intro a
    ext i
    rw [Submodule.coe_sum]
    simp [B, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm, Subring.smul_def]
  have hεB : (ε : A) • B = B := by
    ext i j
    have := congrFun (congrArg Subtype.val (h2 j)) i
    simpa [B, Subring.smul_def] using this
  have hall : ∀ v : Fin n → A, ∃ w, B *ᵥ w = (ε : A) • v := by
    intro v
    have hv : v ∈ Submodule.span A (Λ : Set (Fin n → A)) := hsp ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha⟩ := h3 ⟨y, hy⟩
      exact ⟨_, by rw [hB a, ← ha]; rfl⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨w, hw⟩ := hy
      exact ⟨u + w, by rw [Matrix.mulVec_add, hu, hw, smul_add]⟩
    | smul a x _ hx =>
      obtain ⟨u, hu⟩ := hx
      exact ⟨a • u, by rw [Matrix.mulVec_smul, hu, smul_comm]⟩
  choose w hw using hall
  let C : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => w (Pi.single j 1) i
  have hBC : B * C = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) := by
    ext i j
    have := congrFun (hw (Pi.single j 1)) i
    simpa [C, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.one_apply, Pi.single_apply] using this
  let B' : Matrix (Fin n) (Fin n) A := (ε : A) • C
  have hεB' : (ε : A) • B' = B' := by simp only [B', smul_smul, hεA]
  have hBB' : B * B' = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) := by
    simp only [B', Matrix.mul_smul, hBC, smul_smul, hεA]
  have hz : (1 - (ε : A)) • B = 0 := by rw [sub_smul, one_smul, hεB, sub_self]
  have hz' : (1 - (ε : A)) • B' = 0 := by rw [sub_smul, one_smul, hεB', sub_self]
  have hsq : (1 - (ε : A)) * (1 - ε) = 1 - ε := by linear_combination hεA
  have hB'B : B' * B = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) := by
    have e1 : (B + (1 - (ε : A)) • (1 : Matrix (Fin n) (Fin n) A)) *
        (B' + (1 - (ε : A)) • (1 : Matrix (Fin n) (Fin n) A)) = 1 := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_one, hz, hz', hBB', smul_add, smul_smul, hsq]
      simp [sub_smul]
    have e2 := mul_eq_one_comm.1 e1
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_one, hz, hz', smul_add, smul_smul, hsq] at e2
    simp only [sub_smul, one_smul, add_zero, zero_add] at e2
    linear_combination (norm := abel_nf) e2
  refine ⟨B, B', hBB', hB'B, hεB, hεB', ?_, fun a => ⟨_, hB a, h1 a⟩⟩
  intro y
  obtain ⟨a, ha⟩ := h3 y
  refine ⟨fun i => ε * a i, ?_, ?_⟩
  · have e : (ε : A) • (y : Fin n → A) = B *ᵥ (fun i => (a i : A)) := by
      rw [hB a, ← ha]; rfl
    rw [← hεB', Matrix.smul_mulVec, ← Matrix.mulVec_smul, e, Matrix.mulVec_mulVec, hB'B,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i; simp
  · have := h1 a
    rw [← ha, map_smulₛₗ, hrε, one_smul] at this
    simp [this, hrε]
end GlobalTheory.SplitLift
