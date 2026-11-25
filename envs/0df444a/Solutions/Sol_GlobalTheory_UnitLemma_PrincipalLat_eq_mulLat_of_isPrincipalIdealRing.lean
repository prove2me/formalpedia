-- Prove2me | solution 1 for GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_of_isPrincipalIdealRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:33:27.551737+00:00
-- url     : https://prove2.me/submissions/4fcaf3fb-33ba-4816-a0fc-0d0c1bb534e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Theorems.Thm_GlobalTheory_UnitLemma_PrincipalLat_exists_mul_le_integral
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PrincipalLat
variable {O E A : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
  [CommRing A] [Algebra E A] [Algebra O A] [IsScalarTower O E A] [Module.Finite E A]
namespace GlobalTheory.UnitLemma.PrincipalLat
theorem _root_.solution [IsPrincipalIdealRing (integralClosure O A)]
    (J : Submodule O A) (hJ : IsLat O E J) (hst : ∀ a ∈ integralClosure O A, ∀ y ∈ J, a * y ∈ J) :
    ∃ a : Aˣ, J = mulLat O (a : A) (Subalgebra.toSubmodule (integralClosure O A)) := by
  classical
  obtain ⟨c, hc0, hc⟩ := exists_mul_le_integral E J hJ.1
  set Λ := integralClosure O A

  have hcu : IsUnit (algebraMap O A c) := by
    rw [IsScalarTower.algebraMap_apply O E A]
    refine (IsUnit.mk0 _ ?_).map _
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc0))
  set C := algebraMap O A c
  let I : Ideal Λ :=
    { carrier := {l | ∃ z ∈ J, (l : A) = C * z}
      add_mem' := by
        rintro a b ⟨x, hx, hax⟩ ⟨y, hy, hby⟩
        exact ⟨x + y, J.add_mem hx hy, by rw [Subalgebra.coe_add, hax, hby, mul_add]⟩
      zero_mem' := ⟨0, J.zero_mem, by simp⟩
      smul_mem' := by
        rintro a b ⟨x, hx, hbx⟩
        refine ⟨(a : A) * x, hst _ a.2 _ hx, ?_⟩
        rw [smul_eq_mul, Subalgebra.coe_mul, hbx]; ring }
  obtain ⟨b, hb⟩ := (IsPrincipalIdealRing.principal I).principal
  have hmemI : ∀ l : Λ, l ∈ I ↔ ∃ m : Λ, m * b = l := by
    intro l; rw [hb]; exact Ideal.mem_span_singleton'
  have key : ∀ z, z ∈ J ↔ ∃ l ∈ Λ, C * z = b * l := by
    intro z; constructor
    · intro hz
      obtain ⟨m, hm⟩ := (hmemI ⟨C * z, hc z hz⟩).1 ⟨z, hz, rfl⟩
      have h2 := congrArg Subtype.val hm
      simp only [Subalgebra.coe_mul] at h2
      exact ⟨m, m.2, by rw [← h2, mul_comm]⟩
    · rintro ⟨l, hl, hzl⟩
      obtain ⟨z0, hz0, hbz0⟩ : b ∈ I := by rw [hb]; exact Ideal.mem_span_singleton_self b
      have : C * z = C * (l * z0) := by rw [hzl, hbz0]; ring
      rw [hcu.mul_left_cancel this]
      exact hst l hl z0 hz0

  have hbu : IsUnit (b : A) := by
    have hle : (J : Set A) ⊆ LinearMap.range (LinearMap.mulLeft E (b : A)) := by
      intro z hz
      obtain ⟨l, _, hzl⟩ := (key z).1 hz
      refine ⟨hcu.unit⁻¹ * l, ?_⟩
      simp only [LinearMap.mulLeft_apply]
      calc (b : A) * (↑hcu.unit⁻¹ * l) = ↑hcu.unit⁻¹ * (b * l) := by ring
        _ = z := by rw [← hzl, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    have h1 : (1 : A) ∈ LinearMap.range (LinearMap.mulLeft E (b : A)) := by
      have := Submodule.span_le.2 hle
      rw [hJ.2] at this
      exact this Submodule.mem_top
    obtain ⟨w, hw⟩ := h1
    exact isUnit_iff_exists_inv.2 ⟨w, by simpa using hw⟩
  refine ⟨hcu.unit⁻¹ * hbu.unit, ?_⟩
  ext z
  rw [key z]
  simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply, Subalgebra.mem_toSubmodule,
    Units.val_mul, IsUnit.unit_spec]
  constructor
  · rintro ⟨l, hl, hzl⟩
    refine ⟨l, hl, ?_⟩
    rw [mul_assoc, ← hzl, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · rintro ⟨l, hl, hzl⟩
    refine ⟨l, hl, ?_⟩
    rw [← hzl, ← mul_assoc, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
end GlobalTheory.UnitLemma.PrincipalLat
