-- Prove2me | solution 1 for NumberField.exists_isIntegral_discr_mul_and_sum_algEquiv_apply_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/359d1b24-0a20-56ad-8635-7141783c7343

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_isIntegral_discr_mul_and_sum_algEquiv_apply_mul_eq

set_option autoImplicit false

open NumberField in
theorem solution
    (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] :
    ∃ (n : ℕ) (a b : Fin n → K),
      (∀ j, IsIntegral ℤ (a j)) ∧ (∀ j, IsIntegral ℤ ((NumberField.discr K : K) * b j)) ∧
      (∀ γ : K ≃ₐ[ℚ] K, ∑ j, γ (a j) * γ (b j) = 1) ∧
      ∀ γ δ : K ≃ₐ[ℚ] K, γ ≠ δ → ∑ j, γ (a j) * δ (b j) = 0 := by
  classical
  set ι := Module.Free.ChooseBasisIndex ℤ (𝓞 K) with hι
  set B : Module.Basis ι ℚ K := integralBasis K with hB
  have hnd : (Algebra.traceForm ℚ K).Nondegenerate := traceForm_nondegenerate ℚ K
  set Bd : Module.Basis ι ℚ K := (Algebra.traceForm ℚ K).dualBasis hnd B with hBd
  have hBint : ∀ i, IsIntegral ℤ (B i) := fun i => by
    rw [hB, integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _

  have hpair : ∀ i j, Algebra.trace ℚ K (Bd i * B j) = if j = i then 1 else 0 := fun i j =>
    LinearMap.BilinForm.apply_dualBasis_left hnd B i j

  have hdual : ∀ i, Bd i ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K) := by
    intro i
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨y, rfl⟩ := Submodule.mem_one.mp ha
    have hy : (algebraMap (𝓞 K) K y) ∈ Submodule.span ℤ (Set.range (integralBasis K)) :=
      (mem_span_integralBasis K).mpr ⟨y, rfl⟩
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨j, rfl⟩
      rw [Algebra.traceForm_apply, ← hB, hpair]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
    · rw [map_zero]; exact ⟨0, by simp⟩
    · rintro x z _ _ ⟨u, hu⟩ ⟨v, hv⟩
      exact ⟨u + v, by rw [map_add, map_add, hu, hv]⟩
    · rintro n x _ ⟨u, hu⟩
      exact ⟨n • u, by rw [map_zsmul, map_zsmul, hu]⟩
  have hdint : ∀ i, IsIntegral ℤ ((discr K : K) * Bd i) := by
    intro i
    have h := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K)
      (I := (1 : Submodule (𝓞 K) K)) (b := B) hBint (a := (1 : K)) (x := Bd i)
      (Submodule.mem_one.mpr ⟨1, map_one _⟩) (hdual i)
    rw [smul_mul_assoc, one_mul, hB, ← coe_discr, Algebra.smul_def, eq_ratCast,
      Rat.cast_intCast] at h
    exact h

  have hexp : ∀ (δ : K ≃ₐ[ℚ] K) (x : K),
      δ x = ∑ γ : K ≃ₐ[ℚ] K, (∑ i, γ (B i) * δ (Bd i)) * γ x := by
    intro δ x
    have hx : x = ∑ i, (Algebra.trace ℚ K (x * B i)) • Bd i := by
      conv_lhs => rw [← Bd.sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hBd, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
    conv_lhs => rw [hx]
    rw [map_sum]
    have h1 : ∀ i, δ ((Algebra.trace ℚ K (x * B i)) • Bd i) =
        ∑ γ : K ≃ₐ[ℚ] K, γ (B i) * δ (Bd i) * γ x := by
      intro i
      rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, trace_eq_sum_automorphisms, Finset.sum_mul]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [map_mul]; ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.sum_mul]
  have hli : LinearIndependent K (fun γ : K ≃ₐ[ℚ] K => (γ : K → K)) := by
    have h := linearIndependent_monoidHom K K
    have hinj : Function.Injective (fun γ : K ≃ₐ[ℚ] K => (γ : K →* K)) := by
      intro γ γ' hγ
      apply AlgEquiv.ext
      intro x
      exact DFunLike.congr_fun hγ x
    exact h.comp _ hinj
  have hcoef : ∀ γ δ : K ≃ₐ[ℚ] K, ∑ i, γ (B i) * δ (Bd i) = if γ = δ then 1 else 0 := by
    intro γ δ
    have hrel : ∑ γ' : K ≃ₐ[ℚ] K,
        ((∑ i, γ' (B i) * δ (Bd i)) - if γ' = δ then 1 else 0) • ((γ' : K ≃ₐ[ℚ] K) : K → K) = 0 := by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul,
        Finset.sum_sub_distrib]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← hexp δ x, sub_self]
    have h0 := (linearIndependent_iff'.mp hli) Finset.univ _ hrel γ (Finset.mem_univ γ)
    exact sub_eq_zero.mp h0

  obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := ⟨Fintype.equivFin ι⟩
  refine ⟨Fintype.card ι, fun j => B (e.symm j), fun j => Bd (e.symm j),
    fun j => hBint _, fun j => hdint _, fun γ => ?_, fun γ δ hγδ => ?_⟩
  · rw [Equiv.sum_comp e.symm (fun i => γ (B i) * γ (Bd i)), hcoef, if_pos rfl]
  · rw [Equiv.sum_comp e.symm (fun i => γ (B i) * δ (Bd i)), hcoef, if_neg hγδ]

end S_NumberField_exists_isIntegral_discr_mul_and_sum_algEquiv_apply_mul_eq
end P2MW
export P2MW.S_NumberField_exists_isIntegral_discr_mul_and_sum_algEquiv_apply_mul_eq (solution)
