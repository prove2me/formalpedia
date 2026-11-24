-- Prove2me | solution 1 for GlobalTheory.PerMove.hermC_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:42.853141+00:00
-- url     : https://prove2.me/submissions/bf8a5f47-9f39-4a81-8f99-bce620cf5f95

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Theorems.Thm_GlobalTheory_PerMove_map_cc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.PerMove
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma hermC_eq_dotProduct' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ star w) := by
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma hermC_mulVec_mulVec' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ) (u w : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (P *ᵥ u) (P *ᵥ w) = u ⬝ᵥ ((Pᵀ * G.map τ * P.map (starRingEnd ℂ)) *ᵥ star w) := by
  have hstar : star (P *ᵥ w) = P.map (starRingEnd ℂ) *ᵥ star w := by
    ext i; simp [Matrix.mulVec, dotProduct]
  rw [hermC_eq_dotProduct', hstar, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
end GlobalTheory.PerMove
namespace GlobalTheory
end GlobalTheory
end

set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PerMove
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField Matrix
open scoped nonZeroDivisors
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.PerMove
namespace _root_.GlobalTheory.PerMove
theorem _root_.solution (τ : E →+* ℂ) (G γ : Matrix (Fin r) (Fin r) E)
    (hγ : ∀ u v, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (γ *ᵥ u) (γ *ᵥ v) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G u v) (u w : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (γ.map τ *ᵥ u) (γ.map τ *ᵥ w) = _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u w := by
  have hM : γᵀ * G * γ.map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc = G := by
    ext a b
    have h := hγ (Pi.single a 1) (Pi.single b 1)
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.herm, Matrix.mulVec_single_one] at h
    simp [Pi.single_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc] at h
    simp [Matrix.mul_apply, Finset.sum_mul, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc]
    rw [Finset.sum_comm]
    convert h using 3 <;> ring_nf
  have hconj : (γ.map τ).map (starRingEnd ℂ) = (γ.map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc).map τ := by
    ext i j
    simp [_root_.GlobalTheory.PerMove.map_cc]
  rw [hermC_mulVec_mulVec', hconj, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hM,
    hermC_eq_dotProduct']
end _root_.GlobalTheory.PerMove
end GlobalTheory.PerMove
