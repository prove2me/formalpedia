-- Prove2me | solution 1 for NeronModelInfra.le_sq_of_linearIndependent_tmul_D_of_forall_indexOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/860e6b73-710c-587d-b5ca-6eb4fb9cca9a

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_le_sq_of_linearIndependent_tmul_D_of_forall_indexOne

set_option autoImplicit false

open TensorProduct KaehlerDifferential NeronModelInfra

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {C A : Type u} [CommRing C] [CommRing A] [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
    (hsurj : Function.Surjective (algebraMap C A))
    {n : ℕ} (z : Fin n → C)
    (hIJ : RingHom.ker (algebraMap C A) ≤ Ideal.span (insert (algebraMap R C π) (Set.range z)))
    (hlin : LinearIndependent (C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z)))
      fun j : Fin n => (1 : C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z))) ⊗ₜ[C]
        D R A (algebraMap C A (z j)))
    (hN : ∀ g : C,
      (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R R'']
        [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
        ∀ c : C →ₐ[R] R'', RingHom.ker (algebraMap C A) ≤ RingHom.ker c.toRingHom →
          Ideal.span (insert (algebraMap R C π) (Set.range z)) ≤ (IsLocalRing.maximalIdeal R'').comap c →
          g ∈ (IsLocalRing.maximalIdeal R'').comap c) →
      g ∈ Ideal.span (insert (algebraMap R C π) (Set.range z))) :
    RingHom.ker (algebraMap C A) ≤ Ideal.span (insert (algebraMap R C π) (Set.range z)) ^ 2 := by
  classical
  set π' : C := algebraMap R C π with hπ'
  set J : Ideal C := Ideal.span (insert π' (Set.range z)) with hJ
  have hπJ : π' ∈ J := Ideal.subset_span (Set.mem_insert _ _)
  have hzJ : ∀ j, z j ∈ J := fun j => Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩)
  intro f hf

  have hfJ : f ∈ J := hIJ hf
  rw [hJ, Ideal.mem_span_insert] at hfJ
  obtain ⟨g, h, hh, hfgh⟩ := hfJ
  obtain ⟨gj, hgj⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hh
  let φ := algebraMap C A
  have hφf : φ f = 0 := hf

  let ι : Ω[A⁄R] →ₗ[C] (C ⧸ J) ⊗[C] Ω[A⁄R] := TensorProduct.mk C (C ⧸ J) Ω[A⁄R] 1
  have hιsmul : ∀ (c : C) (ω : Ω[A⁄R]), ι (φ c • ω) = (Ideal.Quotient.mk J c) • ι ω := by
    intro c ω
    rw [algebraMap_smul, map_smul]
    show c • ((1 : C ⧸ J) ⊗ₜ[C] ω) = (Ideal.Quotient.mk J c) • ((1 : C ⧸ J) ⊗ₜ[C] ω)
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul, mul_one]
    rfl
  have hιJ : ∀ (c : C), c ∈ J → ∀ ω : Ω[A⁄R], ι (φ c • ω) = 0 := by
    intro c hc ω
    rw [hιsmul, Ideal.Quotient.eq_zero_iff_mem.mpr hc, zero_smul]
  have hDπ : D R A (φ π') = 0 := by
    show D R A (algebraMap C A (algebraMap R C π)) = 0
    rw [← IsScalarTower.algebraMap_apply R C A π, Derivation.map_algebraMap]
  have hDf : D R A (φ f) = φ π' • D R A (φ g) +
      ∑ j, (φ (gj j) • D R A (φ (z j)) + φ (z j) • D R A (φ (gj j))) := by
    rw [hfgh, ← hgj, map_add, map_mul, map_sum, map_add, Derivation.leibniz, hDπ, smul_zero, zero_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, Derivation.leibniz]
  have hsum : ∑ j, (Ideal.Quotient.mk J (gj j)) • ι (D R A (φ (z j))) = 0 := by
    have h0 : ι (D R A (φ f)) = 0 := by rw [hφf, map_zero, map_zero]
    rw [hDf, map_add, hιJ π' hπJ, zero_add, map_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_add, hιJ (z j) (hzJ j), add_zero, hιsmul]
  have hgjJ : ∀ j, gj j ∈ J := by
    intro j
    have := Fintype.linearIndependent_iff.mp hlin (fun j => Ideal.Quotient.mk J (gj j)) hsum j
    exact Ideal.Quotient.eq_zero_iff_mem.mp this

  have hhJ2 : h ∈ J ^ 2 := by
    rw [← hgj, pow_two]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_mul (hgjJ j) (hzJ j)

  have hgJ : g ∈ J := by
    refine hN g fun R'' _ _ _ _ _ hR'' c hker hspec => ?_
    have hm : IsLocalRing.maximalIdeal R'' = Ideal.span {algebraMap R R'' π} := by
      rw [← hR''.map_maximalIdeal, hπ, Ideal.map_span, Set.image_singleton]
    have hπ''ne : algebraMap R R'' π ≠ 0 := by
      intro h0
      have : IsLocalRing.maximalIdeal R'' = ⊥ := by rw [hm, h0, Ideal.span_singleton_eq_bot]
      exact IsDiscreteValuationRing.not_isField R'' (IsLocalRing.isField_iff_maximalIdeal_eq.mpr this)

    have hcf : c f = 0 := by
      have : f ∈ RingHom.ker c.toRingHom := hker hf
      exact this
    have hch : c h ∈ IsLocalRing.maximalIdeal R'' ^ 2 := by
      have h1 : J ^ 2 ≤ ((IsLocalRing.maximalIdeal R'').comap c) ^ 2 := Ideal.pow_right_mono hspec 2
      have h2 := (h1.trans (Ideal.le_comap_pow _ 2)) hhJ2
      exact h2
    have hcπ : c π' = algebraMap R R'' π := by rw [hπ']; exact c.commutes π
    rw [Ideal.mem_comap]

    have hrel : algebraMap R R'' π * c g = - c h := by
      have := congrArg c hfgh
      rw [hcf, map_add, map_mul, hcπ] at this
      linear_combination -this
    rw [hm, pow_two, Ideal.span_singleton_mul_span_singleton] at hch
    rw [hm, Ideal.mem_span_singleton]
    have : algebraMap R R'' π * algebraMap R R'' π ∣ algebraMap R R'' π * c g := by
      rw [hrel]; exact (Ideal.mem_span_singleton.mp hch).neg_right
    exact (mul_dvd_mul_iff_left hπ''ne).mp this

  rw [hfgh, pow_two]
  exact Ideal.add_mem _ (Ideal.mul_mem_mul hgJ hπJ) (pow_two J ▸ hhJ2)

end S_NeronModelInfra_le_sq_of_linearIndependent_tmul_D_of_forall_indexOne
end P2MW
export P2MW.S_NeronModelInfra_le_sq_of_linearIndependent_tmul_D_of_forall_indexOne (solution)
