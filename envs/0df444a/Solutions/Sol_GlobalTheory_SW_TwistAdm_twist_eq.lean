-- Prove2me | solution 1 for GlobalTheory.SW.TwistAdm.twist_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:49.220196+00:00
-- url     : https://prove2.me/submissions/4be01c04-f4e6-4cf2-ab93-89441918ded5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible

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
omit [IsCMField E]
namespace GlobalTheory.SW.TwistAdm
namespace _root_.GlobalTheory.SW.TwistAdm
theorem _root_.solution {R : ℕ} {𝔛 : _root_.GlobalTheory.SW.Lt E N}
    (φ : _root_.GlobalTheory.SW.Fam E n N)
    (hex : ∃ s : ℕ, s ≡ 1 [MOD R ^ 2] ∧ ∀ v ∈ _root_.GlobalTheory.SW.stdL E N, (s : E) • v ∈ 𝔛)
    (Λ : _root_.GlobalTheory.SW.Lt E n)
    (x : Matrix (Fin n) (Fin N) E) : _root_.GlobalTheory.SW.twist R 𝔛 φ Λ x =
      if ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ then φ Λ ((hex.choose : E) • x) else 0 := by
  by_cases h : ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ
  · rw [if_pos h]
    simp only [_root_.GlobalTheory.SW.twist]
    rw [dif_pos ⟨h, hex⟩]
  · rw [if_neg h]
    simp only [_root_.GlobalTheory.SW.twist]
    rw [dif_neg (fun h' => h h'.1)]
end _root_.GlobalTheory.SW.TwistAdm
end GlobalTheory.SW.TwistAdm
