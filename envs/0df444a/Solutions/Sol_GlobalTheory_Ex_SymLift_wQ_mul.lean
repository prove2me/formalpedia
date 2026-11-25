-- Prove2me | solution 1 for GlobalTheory.Ex.SymLift.wQ_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:51:44.574224+00:00
-- url     : https://prove2.me/submissions/80349a0f-f0e5-4104-9498-5f4c157a2572

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactor
import Theorems.Thm_GlobalTheory_Ex_SymLift_tk_pow
import Theorems.Thm_GlobalTheory_Ex_SymLift_tk_mul_left
import Theorems.Thm_GlobalTheory_Ex_SymLift_wQ_iff
import Theorems.Thm_GlobalTheory_Ex_SymLift_dbl_mul
import Theorems.Thm_GlobalTheory_Ex_NumB_dbl_mul
import Theorems.Thm_GlobalTheory_Ex_WpPairing_tk_mul_left
import Theorems.Thm_GlobalTheory_T_degenerationWeilPairing_properties
import Theorems.Thm_GlobalTheory_T_mulq_dbl_cubN_relations
import Theorems.Thm_P2M_GlobalTheory_Ex_NumD___add_84e84f39bbbc


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
theorem _root_.solution {k : ℕ} (hk : Odd k) (p p' : N.QT k) :
    N.wQ p * N.wQ p' * N.tk p p' = N.wp p p' ^ ((k + 1) / 2) * N.wQ (p * p') := by
  obtain ⟨a₁, a₂⟩ := (wQ_iff N hk p _).1 rfl
  obtain ⟨b₁, b₂⟩ := (wQ_iff N hk p' _).1 rfl
  rw [← div_eq_iff_eq_mul', wQ_iff N hk]
  have k₁ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p' p).2.2.2.1
  have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
  constructor
  · have t₁ := tk_mul_left N p p' (p * p')
    have t₂ := tk_mul_left N p p' p
    have t₃ := tk_mul_left N p p' p'
    have w₂ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p' p).1
    have w₃ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p' p').1
    have d := dbl_mul N p.1.2.b p'.1.2.b
    have e : (p * p').1.2.b = p.1.2.b * p'.1.2.b := rfl
    rw [e] at t₁ ⊢
    obtain ⟨j, rfl⟩ := hk
    have : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    rw [this]
    have a₁ := E a₁; have b₁ := E b₁; have k₁ := E k₁; have t₁ := E t₁; have t₂ := E t₂; have t₃ := E t₃
    have w₂ := E w₂; have w₃ := E w₃; have d := E d
    apply Additive.ofMul.injective
    simp only [NumD.wp, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a₁ b₁ k₁ t₁ t₂ t₃ w₂ w₃ d ⊢
    linear_combination (norm := module) a₁ + b₁ - k₁ - t₁ - t₂ - t₃ + w₂ + w₃ + (2 * j + 1) • d
  · have t := tk_pow N p p'
    have m := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB k 0 p.1.2.b p'.1.2.b).2.1
    have s := N.ψ_add p.1.1.toAdd p'.1.1.toAdd
    change _ = N.ψ (p.1.1.toAdd + p'.1.1.toAdd) * mulq N.θ N.σ k (p.1.2.b * p'.1.2.b)
    have a₂ := E a₂; have b₂ := E b₂; have k₁ := E k₁; have t := E t; have m := E m; have s := E s
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a₂ b₂ k₁ t m s ⊢
    linear_combination (norm := module) a₂ + b₂ - ((k + 1) / 2) • k₁ + t - m - s
end GlobalTheory.Ex.SymLift
