-- Prove2me | solution 1 for GlobalTheory.CMFormBound.eig_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:03:57.99864+00:00
-- url     : https://prove2.me/submissions/a8b10f2f-f0ce-4b3d-bdd5-681b5e5ca73d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodGaloisIntegral
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
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CMFormBound
namespace GlobalTheory.CMFormBound
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥)
    {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {H : Type} [AddCommGroup H] [Module O H]
    (ρ : orderC c →+* Module.End O H) (ρE : E →+* Module.End K (K ⊗[O] H))
    (hρE : ∀ a : orderC c, ρE a = (ρ a).baseChange K) (σ : E →+* K) (v : K ⊗[O] H) (hv : v ∈ eigK ρ σ)
    (a : E) : ρE a v = σ a • v := by
  have hS : ∀ b ∈ orderC c, ρE b v = σ b • v := by
    intro b hb
    have := Module.End.mem_eigenspace_iff.1 (Submodule.mem_iInf _ |>.1 hv ⟨b, hb⟩)
    rw [show b = ((⟨b, hb⟩ : orderC c) : E) from rfl, hρE]
    exact this
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  set N := algebraMap (OF E) (𝓞 E) n with hN
  have hmem : ∀ z : 𝓞 E, algebraMap (𝓞 E) E (N * z) ∈ orderC c := fun z =>
    Subring.subset_closure (Or.inr ⟨N * z, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hn), rfl⟩)
  have hy0 : algebraMap (𝓞 E) E y ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero hy
  have hN0 : algebraMap (𝓞 E) E N ≠ 0 := by
    rw [hN, ← IsScalarTower.algebraMap_apply]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (OF E) E)).2 hn0
  set b := algebraMap (𝓞 E) E (N * y)
  have hb0 : b ≠ 0 := by simp only [b, map_mul]; exact mul_ne_zero hN0 hy0
  have hab : a * b = algebraMap (𝓞 E) E (N * x) := by
    simp only [b, map_mul, ← hxy]
    field_simp
  have h1 := hS b (hmem y)
  have h2 := hS (a * b) (hab ▸ hmem x)
  have h3 : ρE b⁻¹ v = (σ b)⁻¹ • v := by
    have h4 : v = σ b • ρE b⁻¹ v := by
      rw [← map_smul, ← h1, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel₀ hb0, map_one, Module.End.one_apply]
    have hσb : σ b ≠ 0 := (map_ne_zero σ).2 hb0
    conv_rhs => rw [h4, smul_smul, inv_mul_cancel₀ hσb, one_smul]
  have h5 : ρE a = ρE b⁻¹ * ρE (a * b) := by
    rw [← map_mul]; congr 1; field_simp
  rw [h5, Module.End.mul_apply, h2, map_smul, h3, smul_smul, map_mul, mul_assoc,
    mul_inv_cancel₀ ((map_ne_zero σ).2 hb0), mul_one]
end GlobalTheory.CMFormBound
