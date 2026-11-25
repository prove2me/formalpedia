-- Prove2me | solution 1 for GlobalTheory.Ex.SymLift.wQ_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:49:02.545983+00:00
-- url     : https://prove2.me/submissions/5db05faa-15d5-496e-99ba-38f6c8ed6099

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactor
import Theorems.Thm_GlobalTheory_Ex_SymLift_tk_mul_left
import Theorems.Thm_GlobalTheory_Ex_SymLift_tk_one_left
import Theorems.Thm_GlobalTheory_Ex_SymLift_wQ_iff
import Theorems.Thm_GlobalTheory_Ex_NumD_QT_pow_b
import Theorems.Thm_GlobalTheory_Ex_WpPairing_tk_mul_left
import Theorems.Thm_GlobalTheory_T_degenerationWeilPairing_properties
import Theorems.Thm_GlobalTheory_T_mulq_dbl_cubN_relations


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.SymLift
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.SymLift
theorem _root_.solution {k : ℕ} (hk : Odd k) (p : N.QT k) : N.wQ p⁻¹ * N.σ p.1.2.b ^ k = N.wQ p := by
  obtain ⟨a₁, a₂⟩ := (wQ_iff N hk p _).1 rfl
  rw [← eq_div_iff_mul_eq', eq_comm, wQ_iff N hk]
  have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
  have e : (p⁻¹).1.2.b = p.1.2.b⁻¹ := rfl
  constructor
  · have t₁ := tk_mul_left N p p⁻¹ p⁻¹
    have t₂ := tk_mul_left N p p⁻¹ p
    have w₁ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p⁻¹ p).1
    have w₂ := (GlobalTheory.T.degenerationWeilPairing_properties O N k 1 1 p).1
    have s := N.σ_inv p.1.2.b
    rw [mul_inv_cancel] at t₁ t₂ w₁
    rw [mul_one, left_eq_mul] at w₂
    rw [w₂] at w₁
    rw [tk_one_left, e] at t₁ t₂
    rw [N.cub.s01 p.1.2.b p.1.2.b p.1.2.b⁻¹, N.cub.s12 p.1.2.b p.1.2.b p.1.2.b⁻¹] at t₂
    rw [e]
    have a₁ := E a₁; have t₁ := E t₁; have t₂ := E t₂; have w₁ := E w₁; have s := E s
    apply Additive.ofMul.injective
    simp only [NumD.wp, dbl, inv_inv, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a₁ t₁ t₂ w₁ s ⊢
    linear_combination (norm := module) a₁ + t₁ - t₂ + w₁ - k • s
  · have m := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB k 0 p.1.2.b 1).2.2.2
    have s := N.even p.1.1.toAdd
    rw [← N.QT_pow_b p] at s
    change _ = N.ψ (-p.1.1.toAdd) * mulq N.θ N.σ k p.1.2.b⁻¹
    have a₂ := E a₂; have m := E m; have s := E s
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at a₂ m s ⊢
    linear_combination (norm := module) a₂ - m - s
end GlobalTheory.Ex.SymLift
