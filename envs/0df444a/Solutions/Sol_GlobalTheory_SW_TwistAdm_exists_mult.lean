-- Prove2me | solution 1 for GlobalTheory.SW.TwistAdm.exists_mult
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:15.43611+00:00
-- url     : https://prove2.me/submissions/654c0097-51b8-4ed1-a3cc-a959dcdca7c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Theorems.Thm_GlobalTheory_SW_TwistAdm_nat_smul_mem
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
omit [IsCMField E]
namespace GlobalTheory.SW.TwistAdm
namespace _root_.GlobalTheory.SW.TwistAdm
theorem _root_.solution {M R : ℕ} (hR : 0 < R)
    {𝔛 : _root_.GlobalTheory.SW.Lt E N}
    (h : _root_.GlobalTheory.SW.Agree (R * M) 𝔛 (_root_.GlobalTheory.SW.stdL E N)) :
    ∃ s : ℕ, s ≡ 1 [MOD R ^ 2] ∧ ∀ v ∈ _root_.GlobalTheory.SW.stdL E N, (s : E) • v ∈ 𝔛 := by
  obtain ⟨s, -, hcop, -, hstd⟩ := h
  have hc : s.Coprime (R ^ 2) :=
    Nat.Coprime.pow_right 2 (Nat.Coprime.coprime_dvd_right (dvd_mul_right R M) hcop)
  rcases Nat.lt_or_ge 1 (R ^ 2) with hlt | hle
  · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc hlt
    refine ⟨s * m, ?_, fun v hv => ?_⟩
    · show s * m % R ^ 2 = 1 % R ^ 2
      rw [hm, Nat.mod_eq_of_lt hlt]
    · have := _root_.GlobalTheory.SW.TwistAdm.nat_smul_mem 𝔛 m (hstd v hv)
      rwa [smul_smul, ← Nat.cast_mul, Nat.mul_comm] at this
  · have hR1 : R ^ 2 = 1 :=
      le_antisymm hle (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hR.ne'))
    exact ⟨s, by rw [hR1]; exact Nat.modEq_one, hstd⟩
end _root_.GlobalTheory.SW.TwistAdm
end GlobalTheory.SW.TwistAdm
