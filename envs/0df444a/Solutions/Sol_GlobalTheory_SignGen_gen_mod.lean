-- Prove2me | solution 1 for GlobalTheory.SignGen.gen_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:48:12.124558+00:00
-- url     : https://prove2.me/submissions/46d310fd-0e97-4be4-8cfe-d78bee0572c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsImaginaryGeneratorCmType
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.SignGen
namespace GlobalTheory.SignGen
theorem _root_.solution (R E : Type) [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
    (hinj : Function.Injective (algebraMap R E)) (M : Submodule R E) (hM : IsUnit M) (c : R) (hc : c ≠ 0) :
    ∃ ξ₀ ∈ M, M ≤ Submodule.span R {ξ₀} ⊔ Ideal.span {c} • M := by
  classical
  obtain ⟨N, hN⟩ := hM.exists_right_inv
  have h1 : (1 : E) ∈ (1 : Submodule R E) := Submodule.one_le.1 le_rfl
  have hN0 : ∃ ν ∈ N, ν ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hb : N = ⊥ := eq_bot_iff.2 (fun x hx => (Submodule.mem_bot R).2 (hcon x hx))
    rw [hb, Submodule.mul_bot] at hN
    rw [← hN, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  have hM0 : ∃ η ∈ M, η ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hb : M = ⊥ := eq_bot_iff.2 (fun x hx => (Submodule.mem_bot R).2 (hcon x hx))
    rw [hb, Submodule.bot_mul] at hN
    rw [← hN, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  obtain ⟨ν, hνN, hν0⟩ := hN0
  have hMsub : ∀ η ∈ M, ∃ a : R, η = a • ν⁻¹ := by
    intro η hη
    have hm : η * ν ∈ (1 : Submodule R E) := hN ▸ Submodule.mul_mem_mul hη hνN
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 hm
    exact ⟨a, by rw [Algebra.smul_def, ha]; field_simp⟩
  let f : R →ₗ[R] E := LinearMap.toSpanSingleton R E ν⁻¹
  have hf : ∀ a, f a = a • ν⁻¹ := fun _ => rfl
  let J : Ideal R := Submodule.comap f M
  have hmapJ : Submodule.map f J = M := by
    apply le_antisymm (Submodule.map_comap_le f M)
    intro η hη
    obtain ⟨a, rfl⟩ := hMsub η hη
    exact ⟨a, by simpa [J, Submodule.mem_comap, hf] using hη, rfl⟩
  have hJ0 : Ideal.span {c} * J ≠ 0 := by
    obtain ⟨η, hη, hη0⟩ := hM0
    obtain ⟨a, rfl⟩ := hMsub η hη
    have haJ : a ∈ J := by simpa [J, Submodule.mem_comap, hf] using hη
    have ha0 : a ≠ 0 := by rintro rfl; simp at hη0
    intro h0
    have hmem : c * a ∈ Ideal.span {c} * J := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self c) haJ
    rw [h0, Submodule.zero_eq_bot, Submodule.mem_bot] at hmem
    exact mul_ne_zero hc ha0 hmem
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_sup_span_eq (I := Ideal.span {c} * J) (J := J) Ideal.mul_le_right hJ0
  have hrJ : r ∈ J := hr ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self r)
  refine ⟨f r, hrJ, ?_⟩
  have hmap := congrArg (Submodule.map f) hr
  rw [hmapJ, Submodule.map_sup, ← Ideal.smul_eq_mul, Submodule.map_smul'', hmapJ] at hmap
  rw [Ideal.span, Submodule.map_span, Set.image_singleton] at hmap
  calc M = _ := hmap.symm
    _ ≤ _ := by rw [sup_comm]
end GlobalTheory.SignGen
