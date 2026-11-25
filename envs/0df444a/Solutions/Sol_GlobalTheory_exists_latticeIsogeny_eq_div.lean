-- Prove2me | solution 1 for GlobalTheory.exists_latticeIsogeny_eq_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:33.275051+00:00
-- url     : https://prove2.me/submissions/4d1eceaa-2830-472f-8f13-8004ad566bd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNumeratorOfInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsMulEqPolynomialWeierstrassP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddMonoidHomEqZeroOfEventually
import Theorems.Thm_GlobalTheory_latticeIsogeny_latticePoint
import Theorems.Thm_GlobalTheory_card_ker_latticeIsogeny
import Theorems.Thm_GlobalTheory_derivWeierstrassP_mul_eq
import Theorems.Thm_GlobalTheory_exists_weierstrassP_mul_eq_div
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticePointEquiv_mk


attribute [local simp] GlobalTheory.latticeIsogeny_latticePoint

set_option autoImplicit false
open Filter PeriodPair Polynomial WeierstrassCurve UpperHalfPlane
open scoped Topology
noncomputable section
open GlobalTheory
variable {L L' : PeriodPair} {α : ℂ}
namespace GlobalTheory
theorem _root_.solution (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice)
    (k : Subfield ℂ) (h₂ : L.g₂ ∈ k) (h₃ : L.g₃ ∈ k) (hαk : α ∈ k)
    (hk : ∀ t ∉ L.lattice, α * t ∈ L'.lattice → ℘[L] t ∈ k) :
    ∃ A D : ℂ[X], (∀ i, A.coeff i ∈ k) ∧ (∀ i, D.coeff i ∈ k) ∧ D.Monic ∧
      A.leadingCoeff = (α ^ 2)⁻¹ ∧ IsCoprime A D ∧
      A.natDegree = Nat.card (latticeIsogeny α hα).ker ∧ D.natDegree + 1 = A.natDegree ∧
      ∀ (x y : ℂ) (h : (latticeCurve L).toAffine.Nonsingular x y),
        (D.eval x = 0 → latticeIsogeny α hα (.some x y h) = 0) ∧
        (D.eval x ≠ 0 → ∃ h', latticeIsogeny α hα (.some x y h) = .some (A.eval x / D.eval x)
          (α⁻¹ * ((derivative A * D - A * derivative D).eval x / D.eval x ^ 2) * y) h') := by
  obtain ⟨A, D, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ :=
    exists_weierstrassP_mul_eq_div hα0 hα k h₂ h₃ hαk hk
  refine ⟨A, D, c1, c2, c3, c4, c5, by rw [c6, card_ker_latticeIsogeny hα0], c7, fun x y h ↦ ?_⟩
  obtain ⟨z, hz⟩ := latticePoint_surjective L (.some x y h)
  have hzL : z ∉ L.lattice := fun h' ↦
    Affine.Point.some_ne_zero _ (hz.symm.trans (latticePoint_of_mem L h'))
  rw [← hz, latticeIsogeny_latticePoint]
  rw [latticePoint_of_notMem L hzL, Affine.Point.some.injEq] at hz
  obtain ⟨rfl, rfl⟩ := hz
  refine ⟨fun h0 ↦ latticePoint_of_mem L' ((c8 z hzL).mp h0), fun h0 ↦ ?_⟩
  have hz' := (c8 z hzL).not.mp h0
  have e : α⁻¹ * ((derivative A * D - A * derivative D).eval (℘[L] z) / D.eval (℘[L] z) ^ 2) *
      (℘'[L] z / 2) = ℘'[L'] (α * z) / 2 := by
    rw [mul_assoc, ← mul_div_assoc, ← derivWeierstrassP_mul_eq hα c9 hz' h0]
    field_simp
  rw [e, ← c9 z hz']
  exact ⟨_, latticePoint_of_notMem L' hz'⟩
end GlobalTheory
