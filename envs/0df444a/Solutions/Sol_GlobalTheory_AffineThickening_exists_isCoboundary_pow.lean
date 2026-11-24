-- Prove2me | solution 1 for GlobalTheory.AffineThickening.exists_isCoboundary_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:04.131278+00:00
-- url     : https://prove2.me/submissions/99365033-ddf5-4940-8567-8f35370d09bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Theorems.Thm_GlobalTheory_AffineThickening_rs_rs
import Theorems.Thm_GlobalTheory_AffineThickening_exists_pow_mul_eq_zero
import Theorems.Thm_GlobalTheory_AffineThickening_exists_eq_pow_mul
import Theorems.Thm_GlobalTheory_AffineThickening_app_rs
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_res
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_pow
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_sub_zero
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_mul_zero
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_zero_iff
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_preimage_basicOpen
import Theorems.Thm_GlobalTheory_AffineThickening_exists_lifts
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_basicOpen_eq
import Theorems.Thm_GlobalTheory_AffineThickening_isAffineOpen_inf
import Theorems.Thm_GlobalTheory_AffineThickening_exists_forall_of_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory GlobalTheory.AffineThickening
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y)
variable {i}
variable [IsClosedImmersion i] [Surjective i]
  (hK : ∀ U : Y.Opens, IsAffineOpen U → ∀ a b : Γ(Y, U), Lifts i U a 0 → Lifts i U b 0 → a * b = 0)
  {ι : Type*} {f : ι → Γ(Z, ⊤)} {U : ι → Y.Opens} (hU : ∀ j, IsAffineOpen (U j))
  (hD : ∀ j, i ⁻¹ᵁ U j = Z.basicOpen (f j))
  {s : Γ(Z, ⊤)} {σ : ∀ j, Γ(Y, U j)} (hσ : ∀ j, Lifts i (U j) (σ j) s)
include hK hU hD hσ
namespace GlobalTheory.AffineThickening
theorem _root_.solution [Finite ι] (m : ι) : ∃ n : ℕ, IsCoboundary i σ (f m ^ n) := by
  choose g hg using fun j ↦ exists_lifts (i := i) (hU j) (f m)
  have hc : ∀ j k, Lifts i (U j ⊓ U k) (rs inf_le_left (σ j) - rs inf_le_right (σ k)) 0 :=
    fun j k ↦ ((hσ j).res _).sub_zero ((hσ k).res _)
  obtain ⟨N, hN⟩ := exists_forall_of_mono (fun j n ↦ ∃ y : Γ(Y, U j), Lifts i (U j) y 0 ∧
      rs (inf_le_left : U j ⊓ U m ≤ U j) y =
        rs inf_le_left (g j) ^ n * (rs inf_le_left (σ j) - rs inf_le_right (σ m)))
    (by
      rintro j n ⟨y, hy, e⟩
      exact ⟨g j * y, hy.mul_zero _, by rw [map_mul, e]; ring⟩)
    (by
      intro j
      obtain ⟨n, y, e⟩ := exists_eq_pow_mul (hU j) (inf_le_left : U j ⊓ U m ≤ U j) (g j)
        (rs inf_le_left (σ j) - rs inf_le_right (σ m)) ((hg j).basicOpen_eq (hD m))
      have h0 := (hc j m).mul_zero (rs inf_le_left (g j) ^ n)
      rw [← e, Lifts.zero_iff, app_rs] at h0
      obtain ⟨n', e'⟩ := exists_pow_mul_eq_zero ((hU j).preimage i) _ ((i.app (U j)).hom (g j)) _
        (by rw [(hg j).basicOpen_eq (hD m), Scheme.preimage_basicOpen]) h0
      refine ⟨n' + n, g j ^ n' * y, ?_, by rw [map_mul, map_pow, e]; ring⟩
      rw [Lifts.zero_iff, map_mul, map_pow, e'])
  choose t ht e using hN
  obtain ⟨M, hM⟩ := exists_forall_of_mono (fun (p : ι × ι) n ↦
      rs (inf_le_left : U p.1 ⊓ U p.2 ≤ U p.1) (g p.1) ^ n *
        (rs inf_le_left (t p.1) - rs inf_le_right (t p.2) - rs inf_le_left (g p.1) ^ N *
          (rs inf_le_left (σ p.1) - rs inf_le_right (σ p.2))) = 0)
    (by
      intro p n h
      rw [pow_succ', mul_assoc, h, mul_zero])
    (by
      rintro ⟨j, k⟩
      have hjk := isAffineOpen_inf (hU j) (hD k)
      refine exists_pow_mul_eq_zero hjk (inf_le_left : U j ⊓ U k ⊓ U m ≤ _) _ _
        (((hg j).res inf_le_left).basicOpen_eq (hD m)) ?_
      have hj : U j ⊓ U k ⊓ U m ≤ U j ⊓ U m := inf_le_inf_right _ inf_le_left
      have hk : U j ⊓ U k ⊓ U m ≤ U k ⊓ U m := inf_le_inf_right _ inf_le_right
      have ej := congrArg (rs hj) (e j)
      have ek := congrArg (rs hk) (e k)
      have h0 := hK _ (isAffineOpen_inf hjk (hD m)) _ _
        ((((hg j).res (hj.trans inf_le_left)).pow N).sub_zero
          (((hg k).res (hk.trans inf_le_left)).pow N)) ((hc k m).res hk)
      simp only [map_mul, map_sub, map_pow, rs_rs] at ej ek h0 ⊢
      linear_combination ej - ek + h0)
  refine ⟨M + N, fun j ↦ g j ^ (M + N), fun j ↦ g j ^ M * t j, fun j ↦ (hg j).pow _,
    fun j ↦ (ht j).mul_zero _, fun j k ↦ ?_⟩
  have h0 := hK _ (isAffineOpen_inf (hU j) (hD k)) _ _
    ((((hg j).res inf_le_left).pow M).sub_zero (((hg k).res inf_le_right).pow M))
    ((ht k).res inf_le_right)
  have h1 := hM (j, k)
  simp only [map_mul, map_pow] at h1 ⊢
  linear_combination h1 + h0
end GlobalTheory.AffineThickening
