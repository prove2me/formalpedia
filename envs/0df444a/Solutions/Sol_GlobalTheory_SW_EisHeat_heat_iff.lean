-- Prove2me | solution 1 for GlobalTheory.SW.EisHeat.heat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:03:23.067288+00:00
-- url     : https://prove2.me/submissions/de5c432d-0be8-4e32-aa16-af40aac09ef8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisensteinSeriesOfSchwartzIsHolomorphic
import Theorems.Thm_GlobalTheory_SW_EisHeat_deriv_line
import Theorems.Thm_GlobalTheory_SW_EisHeat_deriv_two
import Theorems.Thm_GlobalTheory_SW_EisHeat_isOpen_dom
import Theorems.Thm_GlobalTheory_PosSemidefShiftByScalar_main
import Theorems.Thm_GlobalTheory_SW_TransComp_key
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisHeat
variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
open Classical
namespace GlobalTheory.SW.EisHeat
theorem _root_.solution {D : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ}
    (hD : DifferentiableOn ℂ (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => D p.1 p.2.1 p.2.2)
      {p | (p.1 : CM Ψ N N) ∈ Hn Ψ N}) :
    IsHeat Ψ D ↔ ∀ Z z z', (Z : CM Ψ N N) ∈ Hn Ψ N → ∀ (τ : Ψ) (a b : Fin N),
      2 * Real.pi * I * fderiv ℂ (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => D p.1 p.2.1 p.2.2)
        (Z, z, z') (dir Ψ τ a b, 0, 0) =
      ∑ k, fderiv ℂ (fderiv ℂ (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => D p.1 p.2.1 p.2.2))
        (Z, z, z') (0, dir Ψ τ k a, 0) (0, 0, dir Ψ τ k b) := by
  have key : ∀ {m : ℕ} (x : CF Ψ m N) (τ : Ψ) (k : Fin m) (a : Fin N) (s : ℂ),
      x + s • dir Ψ τ k a =
        (fun σ => Matrix.of (x σ) + if σ = τ then Matrix.single k a s else 0 : CM Ψ m N) := by
    intro m x τ k a s
    funext σ i j
    change x σ i j + s * (if σ = τ ∧ k = i ∧ a = j then 1 else 0) =
      x σ i j + (if σ = τ then Matrix.single k a s else 0 : Matrix (Fin m) (Fin N) ℂ) i j
    by_cases h : σ = τ
    · simp [h, Matrix.single]
    · simp [h]
  have main : ∀ (Z : CF Ψ N N) (z z' : CF Ψ n N), (Z : CM Ψ N N) ∈ Hn Ψ N →
      ∀ (τ : Ψ) (a b : Fin N),
      (2 * Real.pi * I * fderiv ℂ (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => D p.1 p.2.1 p.2.2)
        (Z, z, z') (dir Ψ τ a b, 0, 0) =
      ∑ k, fderiv ℂ (fderiv ℂ (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => D p.1 p.2.1 p.2.2))
        (Z, z, z') (0, dir Ψ τ k a, 0) (0, 0, dir Ψ τ k b)) ↔
      2 * Real.pi * I * deriv (fun s : ℂ =>
        D (fun σ => Matrix.of (Z σ) + if σ = τ then Matrix.single a b s else 0) z z') 0 =
      ∑ k, deriv (fun s : ℂ => deriv (fun t : ℂ =>
        D Z (fun σ => Matrix.of (z σ) + if σ = τ then Matrix.single k a s else 0)
          (fun σ => Matrix.of (z' σ) + if σ = τ then Matrix.single k b t else 0)) 0) 0 := by
    intro Z z z' hZ τ a b
    have hp : ((Z, z, z') : CF Ψ N N × CF Ψ n N × CF Ψ n N) ∈
      {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N} := hZ
    rw [← (deriv_line (hD.differentiableAt ((isOpen_dom Ψ).mem_nhds hp)) _).deriv]
    simp only [← deriv_two (isOpen_dom Ψ) hD hp]
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero]
    simp only [key]
  exact ⟨fun h Z z z' hZ τ a b => (main Z z z' hZ τ a b).2 (h.2 Z hZ z z' τ a b),
    fun h => ⟨hD, fun Z hZ z z' τ a b => (main Z z z' hZ τ a b).1 (h Z z z' hZ τ a b)⟩⟩
end GlobalTheory.SW.EisHeat
