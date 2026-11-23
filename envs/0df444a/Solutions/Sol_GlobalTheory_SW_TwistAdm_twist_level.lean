-- Prove2me | solution 1 for GlobalTheory.SW.TwistAdm.twist_level
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:00.263456+00:00
-- url     : https://prove2.me/submissions/b32abe8e-fb59-4eb8-9f60-e5d701b287f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Theorems.Thm_GlobalTheory_SW_TwistAdm_nat_smul_mem
import Theorems.Thm_GlobalTheory_SW_TwistAdm_single_mem_std
import Theorems.Thm_GlobalTheory_SW_TwistAdm_col_eq
import Theorems.Thm_GlobalTheory_SW_TwistAdm_colsIn_mulVec
import Theorems.Thm_GlobalTheory_SW_TwistAdm_exists_mult
import Theorems.Thm_GlobalTheory_SW_TwistAdm_twist_eq
import Theorems.Thm_GlobalTheory_SW_Base_nat_smul_mem


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
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable [IsCMField E]
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable [IsCMField E]
namespace GlobalTheory.SW.TwistAdm
namespace _root_.GlobalTheory.SW.TwistAdm
theorem _root_.solution {M R : ℕ}
    {φ : _root_.GlobalTheory.SW.Fam E n N} {𝔛 : _root_.GlobalTheory.SW.Lt E N}
    (hφ : _root_.GlobalTheory.SW.admitted M R φ)
    (hA : _root_.GlobalTheory.SW.Agree (R * M) 𝔛 (_root_.GlobalTheory.SW.stdL E N))
    (a : Matrix (Fin N) (Fin N) E) (c : ℕ)
    (h1 : ∀ v ∈ _root_.GlobalTheory.SW.stdL E N, ∃ ξ ∈ 𝔛, a *ᵥ ξ = (c : E) • v)
    (h2 : ∀ ξ ∈ 𝔛, (c : E) • (a *ᵥ ξ) ∈ _root_.GlobalTheory.SW.stdL E N)
    {Λ : _root_.GlobalTheory.SW.Lt E n} (hΛ : Λ ∈ _root_.GlobalTheory.SW.Vset E n M) :
    _root_.GlobalTheory.SW.LevelL Λ (R * c) (fun x : Matrix (Fin n) (Fin N) E =>
      _root_.GlobalTheory.SW.twist R 𝔛 φ Λ
        (HMul.hMul (self := Matrix.instHMulOfFintypeOfMulOfAddCommMonoid) x a)) := by
  obtain ⟨-, hR⟩ := hφ.pos
  have hex := _root_.GlobalTheory.SW.TwistAdm.exists_mult hR hA
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · have hx' : _root_.GlobalTheory.SW.twist R 𝔛 φ Λ (x * a) ≠ 0 := hx
    rw [_root_.GlobalTheory.SW.TwistAdm.twist_eq φ hex] at hx'
    have hcond : ∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ Λ := by
      by_contra hc
      exact hx' (if_neg hc)
    intro b
    obtain ⟨ξ, hξ, hξa⟩ := h1 _ (_root_.GlobalTheory.SW.TwistAdm.single_mem_std b)
    have hmem := hcond ξ hξ
    rw [← Matrix.mulVec_mulVec, hξa, Matrix.mulVec_smul, smul_smul] at hmem
    rw [_root_.GlobalTheory.SW.TwistAdm.col_eq, Matrix.smul_mulVec, Nat.cast_mul]
    exact hmem
  · show _root_.GlobalTheory.SW.twist R 𝔛 φ Λ ((x + ((R * c : ℕ) : E) • y) * a) =
      _root_.GlobalTheory.SW.twist R 𝔛 φ Λ (x * a)
    have hmv : ∀ ξ, ((x + ((R * c : ℕ) : E) • y) * a) *ᵥ ξ =
        (x * a) *ᵥ ξ + (R : E) • (y *ᵥ ((c : E) • (a *ᵥ ξ))) := by
      intro ξ
      rw [Matrix.add_mul, Matrix.add_mulVec, Matrix.smul_mul, Matrix.smul_mulVec]
      simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_smul, smul_smul, Nat.cast_mul]
    have hiff : (∀ ξ ∈ 𝔛, (R : E) • (((x + ((R * c : ℕ) : E) • y) * a) *ᵥ ξ) ∈ Λ) ↔
        ∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ Λ := by
      refine forall₂_congr fun ξ hξ => ?_
      rw [hmv, smul_add]
      exact Λ.add_mem_iff_left (_root_.GlobalTheory.SW.TwistAdm.nat_smul_mem Λ R
        (_root_.GlobalTheory.SW.TwistAdm.nat_smul_mem Λ R
          (_root_.GlobalTheory.SW.TwistAdm.colsIn_mulVec hy (h2 ξ hξ))))
    rw [_root_.GlobalTheory.SW.TwistAdm.twist_eq φ hex, _root_.GlobalTheory.SW.TwistAdm.twist_eq φ hex]
    by_cases hc : ∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ Λ
    · rw [if_pos (hiff.mpr hc), if_pos hc]
      have hs := hex.choose_spec.2
      have hcols : _root_.GlobalTheory.SW.ColsIn Λ ((hex.choose : E) • (y * ((c : E) • a))) := by
        intro b
        have hb := h2 _ (hs _ (_root_.GlobalTheory.SW.TwistAdm.single_mem_std b))
        have hmem := _root_.GlobalTheory.SW.TwistAdm.colsIn_mulVec hy hb
        have e : ((hex.choose : E) • (y * ((c : E) • a)))ᵀ b =
            y *ᵥ ((c : E) • (a *ᵥ ((hex.choose : E) • Pi.single b 1))) := by
          rw [_root_.GlobalTheory.SW.TwistAdm.col_eq, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
            Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
            Matrix.mulVec_smul, smul_comm]
        rw [e]
        exact hmem
      have key : (hex.choose : E) • ((x + ((R * c : ℕ) : E) • y) * a) =
          (hex.choose : E) • (x * a) + (R : E) • ((hex.choose : E) • (y * ((c : E) • a))) := by
        rw [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul]
        push_cast
        module
      rw [key]
      exact hφ.per Λ hΛ _ _ hcols
    · rw [if_neg (mt hiff.mp hc), if_neg hc]
end _root_.GlobalTheory.SW.TwistAdm
end GlobalTheory.SW.TwistAdm
