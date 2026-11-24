-- Prove2me | solution 1 for GlobalTheory.SW.twist_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:01.16147+00:00
-- url     : https://prove2.me/submissions/f4ce329e-4ece-46f6-9eaa-e58f9a2b0565

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Theorems.Thm_GlobalTheory_SW_TwistAdm_colsIn_mulVec
import Theorems.Thm_GlobalTheory_SW_TwistAdm_relIndex_ne_zero
import Theorems.Thm_GlobalTheory_SW_TwistAdm_std_fg
import Theorems.Thm_GlobalTheory_SW_TwistAdm_cols_of_cond
import Theorems.Thm_GlobalTheory_SW_TwistAdm_twist_eq
import Theorems.Thm_GlobalTheory_SW_TwistAdm_twist_val
import Theorems.Thm_GlobalTheory_SW_TwistAdm_twist_level
import Theorems.Thm_GlobalTheory_SW_TwistAdm_twist_adm
import Theorems.Thm_GlobalTheory_SW_Base_gidx_stdL
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_IsFrame_relIndex_ne_zero


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
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical
namespace _root_.GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E]
    [NumberField E] [IsCMField E] (n N M R : ℕ) (φ : _root_.GlobalTheory.SW.Fam E n N)
    (𝔛 : _root_.GlobalTheory.SW.Lt E N), _root_.GlobalTheory.SW.admitted M R φ → 𝔛.FG →
    _root_.GlobalTheory.SW.Agree (R * M) 𝔛 (_root_.GlobalTheory.SW.stdL E N) →
    (∀ Λ ∈ _root_.GlobalTheory.SW.Vset E n M, ∀ x (s : ℕ), s ≡ 1 [MOD R ^ 2] →
      (∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ) → _root_.GlobalTheory.SW.ColsIn Λ ((R : E) • ((s : E) • x)) →
      _root_.GlobalTheory.SW.twist R 𝔛 φ Λ x = φ Λ ((s : E) • x)) ∧
    (∀ Λ ∈ _root_.GlobalTheory.SW.Vset E n M,
      _root_.GlobalTheory.SW.twist R (_root_.GlobalTheory.SW.stdL E N) φ Λ = φ Λ) ∧
    _root_.GlobalTheory.SW.gidx (_root_.GlobalTheory.SW.stdL E N) = 1 ∧
    0 < _root_.GlobalTheory.SW.gidx 𝔛 ∧
    (∃ R', _root_.GlobalTheory.SW.admitted M R' (_root_.GlobalTheory.SW.twist R 𝔛 φ)) ∧
    ∀ (a : Matrix (Fin N) (Fin N) E) (c : ℕ), 0 < c → a.det ≠ 0 →
      (∀ v ∈ _root_.GlobalTheory.SW.stdL E N, ∃ ξ ∈ 𝔛, a *ᵥ ξ = (c : E) • v) →
      (∀ ξ ∈ 𝔛, (c : E) • (a *ᵥ ξ) ∈ _root_.GlobalTheory.SW.stdL E N) →
      ∀ Λ ∈ _root_.GlobalTheory.SW.Vset E n M,
        _root_.GlobalTheory.SW.LevelL Λ (R * c) (fun x => _root_.GlobalTheory.SW.twist R 𝔛 φ Λ (x * a)) := by
  intro E _ _ _ n N M R φ 𝔛 hφ hfg hA
  refine ⟨fun Λ hΛ x s hs h hx => _root_.GlobalTheory.SW.TwistAdm.twist_val hφ hA hΛ x s hs h hx,
    fun Λ hΛ => ?_, _root_.GlobalTheory.SW.Base.gidx_stdL, ?_,
    _root_.GlobalTheory.SW.TwistAdm.twist_adm hφ hA,
    fun a c _ _ h1 h2 Λ hΛ => _root_.GlobalTheory.SW.TwistAdm.twist_level hφ hA a c h1 h2 hΛ⟩
  · have hstd1 : ∀ v ∈ _root_.GlobalTheory.SW.stdL E N,
        ((1 : ℕ) : E) • v ∈ _root_.GlobalTheory.SW.stdL E N := fun v hv => by
      rwa [Nat.cast_one, one_smul]
    have hAstd : _root_.GlobalTheory.SW.Agree (R * M) (_root_.GlobalTheory.SW.stdL E N)
        (_root_.GlobalTheory.SW.stdL E N) :=
      ⟨1, one_pos, Nat.coprime_one_left _, hstd1, hstd1⟩
    funext x
    by_cases hc : ∀ ξ ∈ _root_.GlobalTheory.SW.stdL E N, (R : E) • (x *ᵥ ξ) ∈ Λ
    · have hcols := _root_.GlobalTheory.SW.TwistAdm.cols_of_cond hstd1 hc
      rw [_root_.GlobalTheory.SW.TwistAdm.twist_val hφ hAstd hΛ x 1 (Nat.ModEq.refl 1) hc hcols,
        Nat.cast_one, one_smul]
    · have hex : ∃ s : ℕ, s ≡ 1 [MOD R ^ 2] ∧ ∀ v ∈ _root_.GlobalTheory.SW.stdL E N,
          (s : E) • v ∈ _root_.GlobalTheory.SW.stdL E N := ⟨1, Nat.ModEq.refl 1, hstd1⟩
      rw [_root_.GlobalTheory.SW.TwistAdm.twist_eq φ hex, if_neg hc]
      by_contra hne
      exact hc fun ξ hξ => by
        rw [← Matrix.smul_mulVec]
        exact _root_.GlobalTheory.SW.TwistAdm.colsIn_mulVec (hφ.supp Λ hΛ x (Ne.symm hne)) hξ
  · obtain ⟨t, ht0, -, hXstd, hstdX⟩ := id hA
    unfold _root_.GlobalTheory.SW.gidx
    have h1 := _root_.GlobalTheory.SW.TwistAdm.relIndex_ne_zero (_root_.GlobalTheory.SW.stdL E N) 𝔛
      hfg ht0 hXstd
    have h2 := _root_.GlobalTheory.SW.TwistAdm.relIndex_ne_zero 𝔛 _ _root_.GlobalTheory.SW.TwistAdm.std_fg
      ht0 hstdX
    exact div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h1)) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h2))
end _root_.GlobalTheory.SW
