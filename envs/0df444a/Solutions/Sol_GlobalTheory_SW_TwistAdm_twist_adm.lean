-- Prove2me | solution 1 for GlobalTheory.SW.TwistAdm.twist_adm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:55.686848+00:00
-- url     : https://prove2.me/submissions/855e2b76-5da8-42ae-ae74-230d61018d25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Theorems.Thm_GlobalTheory_SW_TwistAdm_colsIn_mulVec
import Theorems.Thm_GlobalTheory_SW_TwistAdm_mem_of_coprime
import Theorems.Thm_GlobalTheory_SW_TwistAdm_cols_of_cond
import Theorems.Thm_GlobalTheory_SW_TwistAdm_exists_mult
import Theorems.Thm_GlobalTheory_SW_TwistAdm_twist_eq
import Theorems.Thm_GlobalTheory_SW_TwistAdm_twist_level
import Theorems.Thm_GlobalTheory_SW_Base_mem_of_coprime


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
    (hA : _root_.GlobalTheory.SW.Agree (R * M) 𝔛 (_root_.GlobalTheory.SW.stdL E N)) :
    ∃ R', _root_.GlobalTheory.SW.admitted M R' (_root_.GlobalTheory.SW.twist R 𝔛 φ) := by
  obtain ⟨hM, hR⟩ := hφ.pos
  obtain ⟨t, ht0, htcop, hXstd, hstdX⟩ := id hA
  have hex := _root_.GlobalTheory.SW.TwistAdm.exists_mult hR hA
  have hlev : ∀ Λ ∈ _root_.GlobalTheory.SW.Vset E n M,
      _root_.GlobalTheory.SW.LevelL Λ (R * t) (_root_.GlobalTheory.SW.twist R 𝔛 φ Λ) := by
    intro Λ hΛ
    have := _root_.GlobalTheory.SW.TwistAdm.twist_level hφ hA (1 : Matrix (Fin N) (Fin N) E) t
      (fun v hv => ⟨(t : E) • v, hstdX v hv, by rw [Matrix.one_mulVec]⟩)
      (fun ξ hξ => by rw [Matrix.one_mulVec]; exact hXstd ξ hξ) hΛ
    simpa only [Matrix.mul_one] using this
  refine ⟨R * t, ⟨⟨hM, Nat.mul_pos hR ht0⟩, ?_, fun Λ hΛ => (hlev Λ hΛ).1,
    fun Λ hΛ => (hlev Λ hΛ).2, ?_⟩⟩
  · intro h hh Λ hΛ Λ' hΛ' hcar x
    have hcar' : ∀ v, v ∈ Λ ↔ h *ᵥ v ∈ Λ' := hcar
    have hiff : (∀ ξ ∈ 𝔛, (R : E) • ((h * x) *ᵥ ξ) ∈ Λ') ↔ ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ := by
      refine forall₂_congr fun ξ _ => ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← hcar']
    rw [_root_.GlobalTheory.SW.TwistAdm.twist_eq φ hex, _root_.GlobalTheory.SW.TwistAdm.twist_eq φ hex]
    by_cases hc : ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ
    · rw [if_pos (hiff.mpr hc), if_pos hc, ← Matrix.mul_smul]
      exact hφ.equiv h hh Λ hΛ Λ' hΛ' hcar _
    · rw [if_neg (mt hiff.mp hc), if_neg hc]
  · intro Λ hΛ Λ' hΛ' hagr x hx hx'
    obtain ⟨u, hu0, hucop, hΛΛ', hΛ'Λ⟩ := id hagr
    have hut1 : u.Coprime t := Nat.Coprime.coprime_dvd_right ((dvd_mul_left t R).mul_right M) hucop
    have hut : u.Coprime (t * t) := Nat.Coprime.mul_right hut1 hut1
    have transfer : ∀ {A B : _root_.GlobalTheory.SW.Lt E n},
        _root_.GlobalTheory.SW.ColsIn B (((R * t : ℕ) : E) • x) → (∀ v ∈ A, (u : E) • v ∈ B) →
        ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ A → (R : E) • (x *ᵥ ξ) ∈ B := by
      intro A B hB hAB ξ hξ hmem
      refine _root_.GlobalTheory.SW.TwistAdm.mem_of_coprime B hut (hAB _ hmem) ?_
      have hB' := _root_.GlobalTheory.SW.TwistAdm.colsIn_mulVec hB (hXstd ξ hξ)
      have e : ((t * t : ℕ) : E) • (R : E) • (x *ᵥ ξ) = (((R * t : ℕ) : E) • x) *ᵥ ((t : E) • ξ) := by
        simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
        congr 1
        push_cast
        ring
      rw [e]
      exact hB'
    have hiff : (∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ) ↔ ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ' :=
      ⟨fun hc ξ hξ => transfer hx' hΛΛ' ξ hξ (hc ξ hξ),
        fun hc ξ hξ => transfer hx hΛ'Λ ξ hξ (hc ξ hξ)⟩
    rw [_root_.GlobalTheory.SW.TwistAdm.twist_eq φ hex, _root_.GlobalTheory.SW.TwistAdm.twist_eq φ hex]
    by_cases hc : ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ
    · rw [if_pos hc, if_pos (hiff.mp hc)]
      have hagrRM : _root_.GlobalTheory.SW.Agree (R * M) Λ Λ' :=
        ⟨u, hu0, Nat.Coprime.coprime_dvd_right
          (Nat.mul_dvd_mul (dvd_mul_right R t) dvd_rfl) hucop, hΛΛ', hΛ'Λ⟩
      exact hφ.loc Λ hΛ Λ' hΛ' hagrRM _
        (_root_.GlobalTheory.SW.TwistAdm.cols_of_cond hex.choose_spec.2 hc)
        (_root_.GlobalTheory.SW.TwistAdm.cols_of_cond hex.choose_spec.2 (hiff.mp hc))
    · rw [if_neg hc, if_neg (mt hiff.mpr hc)]
end _root_.GlobalTheory.SW.TwistAdm
end GlobalTheory.SW.TwistAdm
