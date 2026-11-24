-- Prove2me | solution 1 for GlobalTheory.HermModel.rank_integral_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:47:45.137523+00:00
-- url     : https://prove2.me/submissions/374c7069-d8a3-4ce8-92ba-4cb09fbde176

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Theorems.Thm_GlobalTheory_HermModel_finrank_eq_of_injective_of_span
import Theorems.Thm_GlobalTheory_HermModel_eq_zero_of_trace_mul_integer
import Theorems.Thm_GlobalTheory_HermModel_herm_sub_left
import Theorems.Thm_GlobalTheory_HermModel_herm_smul_left
import Theorems.Thm_GlobalTheory_HermModel_herm_add_right
import Theorems.Thm_GlobalTheory_HermModel_herm_smul_right
import Theorems.Thm_GlobalTheory_HermModel_herm_zero_right
import Theorems.Thm_GlobalTheory_HermModel_eq_zero_of_herm_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermModel
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField Matrix
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.HermModel
namespace _root_.GlobalTheory.HermModel
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (_hξ : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ξ = -ξ)
    (h : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧
      (∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
      ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y))) :
    r = D.p + D.q ∧ (LinearMap.range φ).FG ∧
      (∀ x y, IsIntegral ℤ ((NumberField.discr E : E) * (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y)))) ∧
      ∀ v : Fin r → E, (∀ y, ∃ n : ℤ, Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm v (φ y)) = n) ↔
        v ∈ LinearMap.range φ := by
  classical
  obtain ⟨hinj, hspan, -, hdet, hEF⟩ := h
  have hsmul : ∀ (c : 𝓞 E) (x : D.La), φ (c • x) = (c : E) • φ x := fun c x => by
    rw [map_smul]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hr := _root_.GlobalTheory.HermModel.finrank_eq_of_injective_of_span (R := 𝓞 E) (K := E) φ hinj hspan
    rw [Module.finrank_fin_fun] at hr
    rw [← hr, D.rank]
  · haveI := D.fin
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map φ
  · intro x y
    have hmem : ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y) ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨c, rfl⟩ := Submodule.mem_one.mp ha
      refine ⟨D.EF (c • x) y, ?_⟩
      rw [eq_intCast, hEF, hsmul, _root_.GlobalTheory.HermModel.herm_smul_left, Algebra.traceForm_apply]
      change _ = Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y) * (c : E))
      congr 1
      ring
    have hb : ∀ i, IsIntegral ℤ (NumberField.integralBasis E i) := fun i => by
      rw [NumberField.integralBasis_apply]
      exact RingOfIntegers.isIntegral_coe _
    have hint := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ) (L := E) (B := 𝓞 E) 1 hb
      (Submodule.one_le.mp le_rfl) hmem
    rw [← NumberField.coe_discr] at hint
    convert hint using 1
    rw [Algebra.smul_def, mul_one]
    simp
  · intro v
    constructor
    · intro hv
      by_cases hξ0 : ξ = 0
      · have hsub : ∀ x : D.La, x = 0 := fun x => D.unimod.1 <| by
          refine LinearMap.ext fun y => ?_
          have := hEF x y
          rw [hξ0, zero_mul, map_zero] at this
          simp [map_zero, Int.cast_eq_zero.mp this]
        have hbot : Submodule.span E (Set.range φ) ≤ ⊥ := by
          rw [Submodule.span_le]
          rintro _ ⟨x, rfl⟩
          rw [hsub x, map_zero]
          exact Submodule.zero_mem _
        have hv0 : v = 0 := by
          have : v ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
          simpa using hbot this
        rw [hv0]
        exact Submodule.zero_mem _
      · choose n hn using hv
        let ℓ : D.La →+ ℤ := AddMonoidHom.mk' n fun y y' => by
          apply Int.cast_injective (α := ℚ)
          rw [Int.cast_add, ← hn, ← hn, ← hn, map_add, _root_.GlobalTheory.HermModel.herm_add_right, mul_add,
            map_add]
        obtain ⟨x, hx⟩ := D.unimod.2 ℓ.toIntLinearMap
        have htr : ∀ y, Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (v - φ x) (φ y)) = 0 := by
          intro y
          have h1 : (D.EF x y : ℚ) = n y := by
            rw [hx]
            rfl
          rw [_root_.GlobalTheory.HermModel.herm_sub_left, mul_sub, map_sub, hn, ← hEF, h1, sub_self]
        have hzero : ∀ y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (v - φ x) (φ y) = 0 := by
          intro y
          have : ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (v - φ x) (φ y) = 0 := by
            refine _root_.GlobalTheory.HermModel.eq_zero_of_trace_mul_integer fun a => ?_
            have hc : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ((H.bar.symm a : 𝓞 E) : E) = (a : E) := by
              unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
              rw [← H.bar_eq, RingEquiv.apply_symm_apply]
            have := htr (H.bar.symm a • y)
            rw [hsmul, _root_.GlobalTheory.HermModel.herm_smul_right, hc, ← mul_assoc] at this
            exact this
          exact (mul_eq_zero.mp this).resolve_left hξ0
        have hall : ∀ u, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (v - φ x) u = 0 := by
          intro u
          have hu : u ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
          induction hu using Submodule.span_induction with
          | mem w hw =>
            obtain ⟨y, rfl⟩ := hw
            exact hzero y
          | zero => exact _root_.GlobalTheory.HermModel.herm_zero_right _ _
          | add w w' _ _ hw hw' => rw [_root_.GlobalTheory.HermModel.herm_add_right, hw, hw', add_zero]
          | smul c w _ hw => rw [_root_.GlobalTheory.HermModel.herm_smul_right, hw, zero_mul]
        have hw := _root_.GlobalTheory.HermModel.eq_zero_of_herm_eq_zero hdet hall
        exact ⟨x, (sub_eq_zero.mp hw).symm⟩
    · rintro ⟨x, rfl⟩ y
      exact ⟨D.EF x y, (hEF x y).symm⟩
end _root_.GlobalTheory.HermModel
end GlobalTheory.HermModel
