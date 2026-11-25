-- Prove2me | solution 1 for GlobalTheory.xClasses_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:03:46.111791+00:00
-- url     : https://prove2.me/submissions/201b9e54-a097-4da5-af62-46d2c7b735ee

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_XClassesDenom
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
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] [NumberField K] (A : Ideal (𝓞 K)) {r : ℕ}
    (Y : Matrix (Fin r) (Fin (r + 1)) (𝓞 K)) (f : Fin r → Fin (r + 1))
    (S : Matrix (Fin r) (Fin r) K)
    (hx : ∀ a b, ∀ α ∈ A, ∃ o : 𝓞 K,
      (o : K) = (α : K) * (S * Y.map (algebraMap (𝓞 K) K)) a b) (i j : Fin r) :
    ∀ α ∈ Ideal.span {(Y.submatrix id f).det} * A, ∃ o : 𝓞 K, (o : K) = (α : K) * S i j := by
  classical
  intro α hα
  obtain ⟨β, hβ, rfl⟩ := Ideal.mem_span_singleton_mul.mp hα
  set φ := algebraMap (𝓞 K) K with hφ
  set B := Y.submatrix id f with hB
  have hM : B.map φ * (B.map φ).adjugate = (φ B.det) • (1 : Matrix (Fin r) (Fin r) K) := by
    rw [Matrix.mul_adjugate, RingHom.map_det]; rfl
  have e1 : ∀ k, (S * Y.map φ) i (f k) = (S * B.map φ) i k := by
    intro k; simp [Matrix.mul_apply, B]
  have e2 : ∀ k, φ (B.adjugate k j) = (B.map φ).adjugate k j := by
    intro k; exact congrFun (congrFun (RingHom.map_adjugate φ B) k) j
  have hkey : ∑ k, (S * Y.map φ) i (f k) * φ (B.adjugate k j) = φ B.det * S i j := by
    simp_rw [e1, e2]
    rw [← Matrix.mul_apply, Matrix.mul_assoc, hM]
    simp [Matrix.mul_apply, Matrix.one_apply, mul_comm]
  choose g hg using fun k => hx i (f k) β hβ
  refine ⟨∑ k, g k * B.adjugate k j, ?_⟩
  have hc : ∀ u : 𝓞 K, (u : K) = φ u := fun u => rfl
  simp only [hc, map_sum, map_mul] at hg ⊢
  simp_rw [hg]
  rw [mul_comm (φ B.det) (φ β), mul_assoc, ← hkey, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring
end GlobalTheory
