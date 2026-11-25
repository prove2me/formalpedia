-- Prove2me | solution 1 for GlobalTheory.weierstrass_uniformisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:50:43.488801+00:00
-- url     : https://prove2.me/submissions/ea293a45-50c4-4664-91f0-03b35b076935

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNumeratorOfInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsMulEqPolynomialWeierstrassP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddMonoidHomEqZeroOfEventually
import Theorems.Thm_GlobalTheory_latticeIsogeny_latticePoint
import Theorems.Thm_GlobalTheory_exists_eq_latticeIsogeny
import Theorems.Thm_GlobalTheory_exists_mul_eq_polynomial_weierstrassP
import Theorems.Thm_GlobalTheory_exists_variableChange_eq_latticeCurve
import Theorems.Thm_GlobalTheory_exists_weierstrassP_mul_eq_div
import Theorems.Thm_GlobalTheory_latticeCurve_j
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
theorem _root_.solution :
    (∀ L : PeriodPair, (latticeCurve L).IsElliptic) ∧
    (∀ L : PeriodPair, ∃ e : (ℂ ⧸ L.lattice.toAddSubgroup) ≃+ (latticeCurve L).toAffine.Point,
      ∀ z ∉ L.lattice, ∃ h, e (z : ℂ ⧸ L.lattice.toAddSubgroup) =
        .some (℘[L] z) (℘'[L] z / 2) h) ∧
    (∀ L : PeriodPair, (∃ (a : ℂ) (τ : ℍ), a ≠ 0 ∧
        ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) ∧
      ∀ (a : ℂ) (τ : ℍ), a ≠ 0 → (∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) →
        (latticeCurve L).j = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) ∧
    (∀ (L L' : PeriodPair) (α : ℂ), α ≠ 0 → (∀ l ∈ L.lattice, α * l ∈ L'.lattice) →
      ∃ A D : ℂ[X],
        (∀ i, A.coeff i ∈ Subfield.closure
          ({L.g₂, L.g₃, α} ∪ ℘[L] '' {t | t ∉ L.lattice ∧ α * t ∈ L'.lattice})) ∧
        (∀ i, D.coeff i ∈ Subfield.closure
          ({L.g₂, L.g₃, α} ∪ ℘[L] '' {t | t ∉ L.lattice ∧ α * t ∈ L'.lattice})) ∧
        D.Monic ∧ A.leadingCoeff = (α ^ 2)⁻¹ ∧ IsCoprime A D ∧
        A.natDegree = (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex
          L'.lattice.toAddSubgroup ∧
        D.natDegree + 1 = A.natDegree ∧
        (∀ z ∉ L.lattice, D.eval (℘[L] z) = 0 ↔ α * z ∈ L'.lattice) ∧
        ∀ z, α * z ∉ L'.lattice → ℘[L'] (α * z) = A.eval (℘[L] z) / D.eval (℘[L] z)) ∧
    (∀ (L : PeriodPair) (f : ℂ → ℂ), Meromorphic f → (∀ z, ∀ l ∈ L.lattice, f (z + l) = f z) →
      (∀ z, f (-z) = f z) →
      ∃ A D : ℂ[X], D.Monic ∧ ∀ z ∉ L.lattice, f z * D.eval (℘[L] z) = A.eval (℘[L] z)) ∧
    (∀ (W : WeierstrassCurve ℂ) [W.IsElliptic],
      ∃ (L : PeriodPair) (C : VariableChange ℂ), C • W = latticeCurve L) ∧
    (∀ (L L' : PeriodPair)
      (φ : (latticeCurve L).toAffine.Point →+ (latticeCurve L').toAffine.Point) (A B D : ℂ[X]),
      D ≠ 0 → (∀ x y h, D.eval x ≠ 0 →
        ∃ y' h', φ (.some x y h) = .some ((A.eval x + B.eval x * y) / D.eval x) y' h') →
      ∃ α : ℂ, α ≠ 0 ∧ (∀ l ∈ L.lattice, α * l ∈ L'.lattice) ∧
        ∀ z, φ (latticePoint L z) = latticePoint L' (α * z)) :=
  ⟨latticeCurve_isElliptic,
    fun L ↦ ⟨latticePointEquiv L, fun _ hz ↦ ⟨_, latticePoint_of_notMem L hz⟩⟩,
    fun L ↦ ⟨exists_lattice_eq_mul_tau L, fun _ _ ha h ↦ latticeCurve_j ha h⟩,
    fun _ _ _ hα0 hα ↦ exists_weierstrassP_mul_eq_div hα0 hα _
      (Subfield.subset_closure (by simp)) (Subfield.subset_closure (by simp))
      (Subfield.subset_closure (by simp))
      fun t ht ht' ↦ Subfield.subset_closure (.inr ⟨t, ⟨ht, ht'⟩, rfl⟩),
    fun L _ hf hp hev ↦ exists_mul_eq_polynomial_weierstrassP L hf hp hev,
    fun W _ ↦ exists_variableChange_eq_latticeCurve W,
    fun _ _ φ A B D hD hφ ↦ by
      obtain ⟨α, hα, h0, rfl⟩ := exists_eq_latticeIsogeny φ A B D hD hφ
      exact ⟨α, h0, hα, latticeIsogeny_latticePoint hα⟩⟩
end GlobalTheory
