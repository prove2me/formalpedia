-- Prove2me | solution 1 for GlobalTheory.SW.ExpSum.heat_dir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:11:35.963619+00:00
-- url     : https://prove2.me/submissions/7e70abae-78cf-4e93-af8e-fb4a6a75a451

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH
import Theorems.Thm_GlobalTheory_SW_ExpSum_hasSum_deriv
import Theorems.Thm_GlobalTheory_SW_ExpSum_hasSum_deriv_deriv
import Theorems.Thm_GlobalTheory_SW_ExpSum_isOpen_dom
import Theorems.Thm_P2M_GlobalTheory_SW_ExpSum_form_dir__6e51053e4c16
import Theorems.Thm_P2M_GlobalTheory_SW_ExpSum_form_dir__8ff127926bb4
import Theorems.Thm_P2M_GlobalTheory_SW_ExpSum_form_dir__9c9d997b7777
import Theorems.Thm_P2M_GlobalTheory_SW_ExpSum_line__191ffd3dba45
import Theorems.Thm_P2M_GlobalTheory_SW_ExpSum_line__4a86a48c988e
import Theorems.Thm_P2M_GlobalTheory_SW_ExpSum_line__e28282a1a7ca

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ExpSum
variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
namespace GlobalTheory.SW.ExpSum
theorem _root_.solution (φ : Matrix (Fin n) (Fin N) E → ℂ)
    (hs : ∀ p ∈ {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N},
      Summable fun x => ‖φ x * cexp (form Ψ x p)‖)
    (Z : CF Ψ N N) (hZ : (Z : CM Ψ N N) ∈ Hn Ψ N) (z z' : CF Ψ n N) (τ : Ψ) (a b : Fin N) :
    2 * π * I * deriv (fun s : ℂ => ∑' x, φ x * cexp (form Ψ x (Z + s • dir Ψ τ a b, z, z'))) 0 =
      ∑ k, deriv (fun s : ℂ => deriv (fun t : ℂ => ∑' x, φ x *
        cexp (form Ψ x (Z, z + s • dir Ψ τ k a, z' + t • dir Ψ τ k b))) 0) 0 := by
  have h1 := (hasSum_deriv (isOpen_dom Ψ) φ (form Ψ) hs (p := (Z, z, z')) hZ
    (dir Ψ τ a b, 0, 0)).mul_left (2 * π * I)
  have h2 := hasSum_sum (s := Finset.univ) fun k _ =>
    hasSum_deriv_deriv (isOpen_dom Ψ) φ (form Ψ) hs (p := (Z, z, z'))
      (0, dir Ψ τ k a, 0) (0, 0, dir Ψ τ k b) (fun s => by rw [line₂]; exact hZ)
  have e : (fun x => 2 * π * I * (φ x * form Ψ x (dir Ψ τ a b, 0, 0) * cexp (form Ψ x (Z, z, z')))) =
      fun x => ∑ k, φ x * form Ψ x (0, 0, dir Ψ τ k b) * form Ψ x (0, dir Ψ τ k a, 0) *
        cexp (form Ψ x (Z, z, z')) := by
    funext x
    simp only [form_dir₁, form_dir₂, form_dir₃, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e] at h1
  have h3 := h1.unique h2
  simp only [line₁, line₂, line₃] at h3
  exact h3
end GlobalTheory.SW.ExpSum
