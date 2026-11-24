-- Prove2me | solution 1 for GlobalTheory.ThetaTranslSpan.mem_of_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:32:17.188973+00:00
-- url     : https://prove2.me/submissions/e4f773fd-02cf-4868-a34e-86b0d73fa30a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependentThetaPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslSpan
namespace GlobalTheory.ThetaTranslSpan
theorem _root_.solution {V : Type} [AddCommGroup V] (Λ Λ₁ : AddSubgroup V) (hle : Λ₁ ≤ Λ)
    [Finite (Λ ⧸ Λ₁.addSubgroupOf Λ)] (j : V → V → ℂ) (hj0 : ∀ a ∈ Λ, ∀ z, j a z ≠ 0)
    (hj : ∀ a ∈ Λ, ∀ b ∈ Λ, ∀ z, j (a + b) z = j a (z + b) * j b z)
    (D S : Submodule ℂ (V → ℂ)) (F : V → ℂ)
    (hD : ∀ a ∈ Λ, (fun z => (j a z)⁻¹ * F (z + a)) ∈ D)
    (hF : ∀ a ∈ Λ₁, ∀ z, F (z + a) = j a z * F z)
    (hS : ∀ ψ : AddChar Λ ℂ, (∀ a, ‖ψ a‖ = 1) → (∀ a : Λ, (a : V) ∈ Λ₁ → ψ a = 1) → ∀ G ∈ D,
      (∀ (a : Λ) z, G (z + a) = ψ a * j a z * G z) → G ∈ S) : F ∈ S := by
  classical
  set Q := Λ ⧸ Λ₁.addSubgroupOf Λ
  haveI : Fintype Q := Fintype.ofFinite Q
  let T₀ : Λ → V → ℂ := fun a z => (j a z)⁻¹ * F (z + a)
  have hT₀ : ∀ a b : Λ, (QuotientAddGroup.leftRel (Λ₁.addSubgroupOf Λ)) a b → T₀ a = T₀ b := by
    intro a b hab
    rw [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf] at hab
    obtain ⟨c, rfl⟩ : ∃ c : Λ, b = c + a := ⟨-a + b, by abel⟩
    have hc : (c : V) ∈ Λ₁ := by simpa using hab
    ext z
    simp only [T₀, AddSubgroup.coe_add]
    rw [hj c c.2 a a.2, show z + (c + a) = (z + a) + c by abel, hF c hc]
    have := hj0 c c.2 (z + a)
    have := hj0 a a.2 z
    field_simp
  let T : Q → V → ℂ := Quotient.lift T₀ hT₀
  have hTD : ∀ q, T q ∈ D := fun q => QuotientAddGroup.induction_on q fun a => hD a a.2
  have hT : ∀ (q : Q) (a : Λ) z, T q (z + a) = j a z * T (q + (a : Q)) z := by
    intro q a z
    induction q using QuotientAddGroup.induction_on with
    | H b =>
      change T₀ b (z + a) = j a z * T₀ (b + a) z
      simp only [T₀, AddSubgroup.coe_add]
      rw [hj b b.2 a a.2, show z + (b + a) = (z + a) + b by abel]
      have := hj0 b b.2 (z + a)
      have := hj0 a a.2 z
      field_simp
  have hT0 : T 0 = F := by
    change T₀ 0 = F
    ext z
    have h := hj 0 Λ.zero_mem 0 Λ.zero_mem z
    rw [add_zero, add_zero] at h
    have h1 : j 0 z = 1 := by
      have := hj0 0 Λ.zero_mem z
      exact (mul_eq_left₀ this).1 h.symm
    simp [T₀, h1]
  have hmem : ∀ ψ : AddChar Q ℂ, ∑ q, ψ (-q) • T q ∈ S := by
    intro ψ
    refine hS (ψ.compAddMonoidHom (QuotientAddGroup.mk' _)) (fun a => ?_) (fun a ha => ?_) _
      (D.sum_mem fun q _ => D.smul_mem _ (hTD q)) (fun a z => ?_)
    · simp [AddChar.norm_apply]
    · have : (a : Q) = 0 := (QuotientAddGroup.eq_zero_iff _).2 ha
      change ψ (a : Q) = 1
      rw [this, AddChar.map_zero_eq_one]
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hT, Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.addRight (a : Q)) _ _ fun q => ?_
      have : ψ (-q) = ψ (a : Q) * ψ (-(q + (a : Q))) := by
        rw [← AddChar.map_add_eq_mul]; congr 1; abel
      change _ = ψ (a : Q) * j a z * (ψ (-(q + (a : Q))) * T (q + (a : Q)) z)
      rw [this]
      ring
  have hsum : ∑ ψ : AddChar Q ℂ, ∑ q, ψ (-q) • T q = (Fintype.card Q : ℂ) • F := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, AddChar.sum_apply_eq_ite, neg_eq_zero]
    rw [Finset.sum_eq_single 0 (fun q _ hq => by simp [hq]) (by simp)]
    simp [hT0]
  have h := S.sum_mem (t := Finset.univ) fun ψ _ => hmem ψ
  rw [hsum] at h
  exact (S.smul_mem_iff (by simp)).1 h
end GlobalTheory.ThetaTranslSpan
