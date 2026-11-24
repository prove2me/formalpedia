-- Prove2me | solution 1 for GlobalTheory.SW.TwistMove.admissibleLatticeFamily_moved_by_rational_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:29:34.145703+00:00
-- url     : https://prove2.me/submissions/9c73c047-f420-4e95-8488-7bfe203ee776

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalMatrixMoveAdmissibleUniformLevel
import Theorems.Thm_GlobalTheory_SW_Base_mem_of_coprime
import Theorems.Thm_GlobalTheory_SW_TwistAdm_colsIn_mulVec
import Theorems.Thm_GlobalTheory_SW_TwistAdm_cols_of_cond
import Theorems.Thm_GlobalTheory_SW_TwistAdm_exists_mult
import Theorems.Thm_GlobalTheory_SW_TwistAdm_mem_of_coprime
import Theorems.Thm_GlobalTheory_SW_TwistAdm_twist_adm
import Theorems.Thm_GlobalTheory_SW_TwistAdm_twist_eq
import Theorems.Thm_GlobalTheory_SW_TwistAdm_twist_level


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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistMove
open GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable [IsCMField E]
namespace GlobalTheory.SW.TwistMove
theorem _root_.solution {M R : ℕ} {φ : Fam E n N} {𝔛 : Lt E N} (hφ : admitted M R φ)
    (hA : Agree (R * M) 𝔛 (stdL E N)) (a : Matrix (Fin N) (Fin N) E) {c : ℕ} (hc0 : 0 < c)
    (h1 : ∀ v ∈ stdL E N, ∃ ξ ∈ 𝔛, a *ᵥ ξ = (c : E) • v)
    (h2 : ∀ ξ ∈ 𝔛, (c : E) • (a *ᵥ ξ) ∈ stdL E N) :
    admitted M (R * c) (fun Λ (x : Matrix (Fin n) (Fin N) E) => twist R 𝔛 φ Λ
      (HMul.hMul (self := Matrix.instHMulOfFintypeOfMulOfAddCommMonoid) x a)) := by
  have hex := exists_mult hφ.pos.2 hA
  refine ⟨⟨hφ.pos.1, Nat.mul_pos hφ.pos.2 hc0⟩, ?_,
    fun Λ hΛ => (twist_level hφ hA a c h1 h2 hΛ).1,
    fun Λ hΛ => (twist_level hφ hA a c h1 h2 hΛ).2, ?_⟩
  · intro h hh Λ hΛ Λ' hΛ' hm x
    obtain ⟨R', hR'⟩ := twist_adm hφ hA
    have := hR'.equiv h hh Λ hΛ Λ' hΛ' hm (x * a)
    rwa [← Matrix.mul_assoc] at this
  · intro Λ hΛ Λ' hΛ' ⟨u, hu, hc, h3, h4⟩ x hx hx'
    have hct : u.Coprime (c * c) := by
      have : u.Coprime c := hc.coprime_dvd_right ⟨R * M, by ring⟩
      exact this.mul_right this
    have key : ∀ A B : Lt E n, (∀ v ∈ A, (u : E) • v ∈ B) → ColsIn B (((R * c : ℕ) : E) • x) →
        (∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ A) → ∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ B := by
      intro A B hAB hB h ξ hξ
      refine mem_of_coprime B hct (hAB _ (h ξ hξ)) ?_
      have := colsIn_mulVec hB (h2 ξ hξ)
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, Matrix.mulVec_mulVec] at this
      rw [smul_smul]
      convert this using 2
      push_cast; ring
    simp only [twist_eq φ hex]
    by_cases h : ∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ Λ
    · have h' := key Λ Λ' h3 hx' h
      rw [if_pos h, if_pos h']
      exact hφ.loc Λ hΛ Λ' hΛ' ⟨u, hu, hc.coprime_dvd_right ⟨c, by ring⟩, h3, h4⟩ _
        (cols_of_cond hex.choose_spec.2 h) (cols_of_cond hex.choose_spec.2 h')
    · rw [if_neg h, if_neg (fun h' => h (key Λ' Λ h4 hx h'))]
end GlobalTheory.SW.TwistMove
