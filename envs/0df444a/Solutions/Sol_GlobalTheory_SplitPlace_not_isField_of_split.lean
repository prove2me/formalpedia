-- Prove2me | solution 1 for GlobalTheory.SplitPlace.not_isField_of_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:36:18.845148+00:00
-- url     : https://prove2.me/submissions/cea0216a-56b5-4fd3-a114-41439c6f0445

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NotIsFieldAdicCompletionTensorOfSplit
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_SelfDualGenus_isAdicComplete_adicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_isUnit_algebraMap_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


section
open scoped TensorProduct
open NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.SplitPlace
open scoped TensorProduct in
open NumberField IsDedekindDomain Polynomial in
private lemma isMaximal_and_algebraMap_mem_iff_of_mem_primesOver (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : Ideal (𝓞 E))
    (h : P ∈ v.asIdeal.primesOver (𝓞 E)) :
    P.IsMaximal ∧ ∀ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a ∈ P ↔ a ∈ v.asIdeal := by
  obtain ⟨hp, ho⟩ := h
  haveI := hp; haveI := ho; haveI := v.isMaximal
  refine ⟨Ideal.IsMaximal.of_liesOver_isMaximal P v.asIdeal, fun a => ?_⟩
  rw [Ideal.over_def P v.asIdeal, Ideal.under_def, Ideal.mem_comap]
open scoped TensorProduct in
open NumberField IsDedekindDomain Polynomial in
private lemma exists_root_quadratic_of_isUnit_of_mem_maximalIdeal (R : Type) [CommRing R]
    [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (b c : R)
    (hb : IsUnit b) (hc : c ∈ IsLocalRing.maximalIdeal R) : ∃ β : R, β ^ 2 + b * β + c = 0 := by
  have hmon : (X ^ 2 + C b * X + C c : R[X]).Monic := by monicity!
  obtain ⟨β, hβ, -⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal R)
    (X ^ 2 + C b * X + C c) hmon 0 (by simpa using hc) (by simpa using hb.map _)
  exact ⟨β, by simpa using hβ⟩
end GlobalTheory.SplitPlace
end

set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain Polynomial
open GlobalTheory GlobalTheory.SplitPlace
open scoped TensorProduct
open NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.SplitPlace
namespace _root_.GlobalTheory.SplitPlace
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F),
    (v.asIdeal.primesOver (𝓞 E)).ncard = 2 → ¬ IsField (v.adicCompletion F ⊗[F] E) := by
  intro F E _ _ _ _ _ hrank v hsplit hfield
  obtain ⟨P, Q, hPQ, hset⟩ := Set.ncard_eq_two.mp hsplit
  obtain ⟨hPmax, hPmem⟩ := isMaximal_and_algebraMap_mem_iff_of_mem_primesOver F E v P
    (by rw [hset]; exact Set.mem_insert _ _)
  obtain ⟨hQmax, hQmem⟩ := isMaximal_and_algebraMap_mem_iff_of_mem_primesOver F E v Q
    (by rw [hset]; exact Set.mem_insert_of_mem _ rfl)
  obtain ⟨α, hαP, hαQ⟩ := SetLike.not_le_iff_exists.mp
    (fun h => hPQ (hPmax.eq_of_le hQmax.ne_top h))
  have hαF : (α : E) ∉ (algebraMap F E).range := by
    rintro ⟨a, ha⟩
    have hint : IsIntegral ℤ a := by
      have h1 : IsIntegral ℤ (algebraMap F E a) := ha ▸ RingOfIntegers.isIntegral_coe α
      exact (isIntegral_algHom_iff ((Algebra.ofId F E).restrictScalars ℤ)
        (algebraMap F E).injective).mp h1
    have hα : algebraMap (𝓞 F) (𝓞 E) ⟨a, hint⟩ = α := RingOfIntegers.ext (by rw [← ha]; rfl)
    have hav : (⟨a, hint⟩ : 𝓞 F) ∈ v.asIdeal := (hPmem _).mp (hα ▸ hαP)
    exact hαQ (hα ▸ (hQmem _).mpr hav)
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ hrank
  have hint : IsIntegral (𝓞 F) α := Algebra.IsIntegral.isIntegral α
  have hdeg : (minpoly (𝓞 F) α).natDegree = 2 := by
    have hE : minpoly (𝓞 F) (α : E) = minpoly (𝓞 F) α :=
      minpoly.algHom_eq (IsScalarTower.toAlgHom (𝓞 F) (𝓞 E) E) Subtype.val_injective α
    have hF : minpoly F (α : E) = (minpoly (𝓞 F) α).map (algebraMap (𝓞 F) F) := by
      rw [← hE]
      exact minpoly.isIntegrallyClosed_eq_field_fractions' F (hint.map (IsScalarTower.toAlgHom (𝓞 F) (𝓞 E) E))
    have hle : (minpoly F (α : E)).natDegree ≤ 2 := hrank ▸ minpoly.natDegree_le (α : E)
    have hne1 : (minpoly F (α : E)).natDegree ≠ 1 := fun h => hαF (minpoly.natDegree_eq_one_iff.mp h)
    have hpos : 0 < (minpoly F (α : E)).natDegree :=
      minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral _)
    rw [hF, (minpoly.monic hint).natDegree_map] at hle hne1 hpos
    omega
  set b := (minpoly (𝓞 F) α).coeff 1 with hb
  set c := (minpoly (𝓞 F) α).coeff 0 with hc
  have hα2 : α ^ 2 + algebraMap (𝓞 F) (𝓞 E) b * α + algebraMap (𝓞 F) (𝓞 E) c = 0 := by
    have h := minpoly.aeval (𝓞 F) α
    have h2 : (minpoly (𝓞 F) α).coeff 2 = 1 := by
      rw [← hdeg]; exact (minpoly.monic hint).coeff_natDegree
    rw [aeval_eq_sum_range, hdeg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      h2] at h
    simp only [Algebra.smul_def, map_one, one_mul, pow_zero, pow_one, mul_one] at h
    linear_combination h
  have hcv : c ∈ v.asIdeal := by
    rw [← hPmem]
    have hce : algebraMap (𝓞 F) (𝓞 E) c = -(α ^ 2 + algebraMap (𝓞 F) (𝓞 E) b * α) := by
      linear_combination hα2
    rw [hce]
    exact P.neg_mem (P.add_mem (P.pow_mem_of_mem hαP 2 two_pos) (P.mul_mem_left _ hαP))
  have hbv : b ∉ v.asIdeal := by
    intro hbv
    have hsq : α ^ 2 = -(algebraMap (𝓞 F) (𝓞 E) b * α + algebraMap (𝓞 F) (𝓞 E) c) := by
      linear_combination hα2
    have hmem : α ^ 2 ∈ Q := by
      rw [hsq]
      exact Q.neg_mem (Q.add_mem (Q.mul_mem_right _ ((hQmem b).mpr hbv)) ((hQmem c).mpr hcv))
    exact hαQ (hQmax.isPrime.mem_of_pow_mem 2 hmem)
  haveI := _root_.GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  obtain ⟨β, hβ⟩ := exists_root_quadratic_of_isUnit_of_mem_maximalIdeal
    (v.adicCompletionIntegers F) (algebraMap (𝓞 F) _ b) (algebraMap (𝓞 F) _ c)
    ((_root_.GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v b).mpr hbv)
    (by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, _root_.GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff]
      exact not_not.mpr hcv)
  have hβF : (β : v.adicCompletion F) ^ 2 + algebraMap F (v.adicCompletion F) (b : F) * β
      + algebraMap F (v.adicCompletion F) (c : F) = 0 := by
    have h := congrArg (v.adicCompletionIntegers F).subtype hβ
    rw [map_add, map_add, map_mul, map_pow, map_zero] at h
    exact h
  have hαE : (α : E) ^ 2 + algebraMap F E (b : F) * α + algebraMap F E (c : F) = 0 := by
    have h := congrArg (algebraMap (𝓞 E) E) hα2
    rw [map_add, map_add, map_mul, map_pow, map_zero] at h
    exact h
  set x : v.adicCompletion F ⊗[F] E :=
    Algebra.TensorProduct.includeLeft (S := F) (B := E) (β : v.adicCompletion F) with hx
  set y : v.adicCompletion F ⊗[F] E :=
    Algebra.TensorProduct.includeRight (A := v.adicCompletion F) (α : E) with hy
  have hxeq : x ^ 2 + algebraMap F _ (b : F) * x + algebraMap F _ (c : F) = 0 := by
    have h := congrArg (Algebra.TensorProduct.includeLeft (R := F) (S := F) (B := E)) hβF
    rw [map_add, map_add, map_mul, map_pow, AlgHom.commutes, AlgHom.commutes, map_zero] at h
    exact h
  have hyeq : y ^ 2 + algebraMap F _ (b : F) * y + algebraMap F _ (c : F) = 0 := by
    have h := congrArg (Algebra.TensorProduct.includeRight (R := F) (A := v.adicCompletion F)) hαE
    rw [map_add, map_add, map_mul, map_pow, AlgHom.commutes, AlgHom.commutes, map_zero] at h
    exact h
  have hprod : (x - y) * (x + y + algebraMap F _ (b : F)) = 0 := by
    linear_combination hxeq - hyeq
  haveI := hfield.isDomain
  obtain ⟨z, hz⟩ : ∃ z : v.adicCompletion F,
      y = Algebra.TensorProduct.includeLeft (S := F) (B := E) z := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact ⟨β, (sub_eq_zero.mp h).symm⟩
    · refine ⟨-(β : v.adicCompletion F) - algebraMap F _ (b : F), ?_⟩
      rw [map_sub, map_neg, AlgHom.commutes, ← hx]
      linear_combination h
  obtain ⟨ℓ, hℓ1, hℓα⟩ : ∃ ℓ : E →ₗ[F] F, ℓ 1 = 0 ∧ ℓ α = 1 := by
    have hnot : (α : E) ∉ Submodule.span F {(1 : E)} := by
      rw [Submodule.mem_span_singleton]
      rintro ⟨a, ha⟩
      exact hαF ⟨a, by rw [Algebra.algebraMap_eq_smul_one]; exact ha⟩
    obtain ⟨ℓ, hℓ, hℓα⟩ :=
      LinearMap.exists_extend_of_notMem (0 : Submodule.span F {(1 : E)} →ₗ[F] F) hnot 1
    refine ⟨ℓ, ?_, hℓα⟩
    have h := LinearMap.congr_fun hℓ ⟨1, Submodule.mem_span_singleton_self 1⟩
    simpa using h
  have key := congrArg ((TensorProduct.rid F (v.adicCompletion F)).toLinearMap ∘ₗ
    LinearMap.lTensor (v.adicCompletion F) ℓ) hz
  simp [hy, hℓ1, hℓα, Algebra.TensorProduct.includeLeft_apply] at key
end _root_.GlobalTheory.SplitPlace
end GlobalTheory.SplitPlace
