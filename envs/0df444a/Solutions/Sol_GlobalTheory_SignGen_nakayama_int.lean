-- Prove2me | solution 1 for GlobalTheory.SignGen.nakayama_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:48:12.987795+00:00
-- url     : https://prove2.me/submissions/f465a1f8-d560-48c8-a531-21a55fffc24d

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
theorem _root_.solution (R E : Type) [CommRing R] [Field E] [Algebra R E] [Module.Finite ℤ R]
    (M : Submodule R E) (hM : M.FG) (l : ℕ) (ξ : E)
    (h : M ≤ Submodule.span R {ξ} ⊔ Ideal.span {(l : R)} • M) :
    ∀ η ∈ M, ∃ n : ℕ, n.Coprime l ∧ ∃ a : R, (n : E) * η = algebraMap R E a * ξ := by
  classical
  have hfg : (M.restrictScalars ℤ).FG := hM.restrictScalars
  have hle : M.restrictScalars ℤ ≤
      (Submodule.span R {ξ}).restrictScalars ℤ ⊔ Ideal.span {(l : ℤ)} • M.restrictScalars ℤ := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (h hx)
    rw [Submodule.ideal_span_singleton_smul] at hz
    obtain ⟨m, hm, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
    refine Submodule.add_mem_sup hy ?_
    have : (l : R) • m = (l : ℤ) • m := by
      rw [Algebra.smul_def, zsmul_eq_mul]; simp
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hm
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hfg le_rfl hle
  intro η hη
  have hrη : r • η ∈ (Submodule.span R {ξ}).restrictScalars ℤ :=
    hr (Submodule.smul_mem_pointwise_smul η r _ hη)
  rw [Submodule.restrictScalars_mem, Submodule.mem_span_singleton] at hrη
  obtain ⟨a, ha⟩ := hrη
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.1 hr1
  refine ⟨r.natAbs, ?_, ?_⟩
  · have hc : IsCoprime r (l : ℤ) := ⟨1, -k, by linarith⟩
    have := Int.isCoprime_iff_gcd_eq_one.1 hc
    simpa [Int.gcd, Nat.Coprime] using this
  · rw [zsmul_eq_mul] at ha
    rw [Algebra.smul_def] at ha
    rcases Int.natAbs_eq r with hr' | hr'
    · refine ⟨a, ?_⟩
      have e : ((r.natAbs : ℤ) : E) = (r : E) := by rw [← hr']
      rw [← Int.cast_natCast, e, ha]
    · refine ⟨-a, ?_⟩
      have e0 : (r.natAbs : ℤ) = -r := by omega
      have e : ((r.natAbs : ℤ) : E) = -(r : E) := by rw [e0, Int.cast_neg]
      rw [← Int.cast_natCast, e, map_neg, neg_mul, neg_mul, ha]
end GlobalTheory.SignGen
