-- Prove2me | solution 1 for Ideal.exists_map_localization_eq_span_of_flat_of_residueField_mvPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/fbd6881e-67a7-5927-8214-18b25cf779eb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_map_localization_eq_span_of_flat_of_residueField_mvPolynomial

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

universe u

section Purity

variable {R : Type*} [CommRing R] {P : Type*} [CommRing P] [Algebra R P]

noncomputable def smulMapDLC2 (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] : I ⊗[R] M →ₗ[R] M :=
  (TensorProduct.lid R M).toLinearMap ∘ₗ (I.subtype.rTensor M)

@[scoped simp] theorem smulMapDLC2_tmul (I : Ideal R) {M : Type*} [AddCommGroup M] [Module R M] (i : I) (m : M) :
    smulMapDLC2 I M (i ⊗ₜ[R] m) = (i : R) • m := by
  simp [smulMapDLC2]

theorem smulMapDLC2_naturality (I : Ideal R) {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] (f : M →ₗ[R] M') (τ : I ⊗[R] M) :
    f (smulMapDLC2 I M τ) = smulMapDLC2 I M' (f.lTensor I τ) := by
  induction τ using TensorProduct.induction_on with
  | zero => simp
  | tmul i m => simp
  | add x y hx hy => simp [hx, hy]

theorem smulMapDLC2_injective_of_flat (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] [Module.Flat R M] :
    Function.Injective (smulMapDLC2 I M) :=
  (TensorProduct.lid R M).injective.comp (Module.Flat.iff_rTensor_injective'.1 inferInstance I)

namespace Ideal p2m_export "Ideal" "map_le_iff_le_comap Quotient.eq_zero_iff_mem Quotient.mkₐ map_span primeCompl span mul_mem_mul map_eq_top_or_isMaximal_of_surjective IsMaximal Quotient.mk mul_mem_left map mk_ker mem_sup_left unit_mul_mem_iff_mem FG ext isMaximal_comap_of_isIntegral_of_isMaximal mem_map_of_mem span_le mem_sup_right ResidueField comap_map_of_surjective mem_comap mul_mono_left map_mono comap_top comap mem_map_iff_of_surjective Quotient.mk_surjective" end Ideal
p2m_open_scoped "Ideal" in

theorem Ideal.mem_map_mul_of_flat_quotient_DLC2 (I : Ideal R) (J : Ideal P) [Module.Flat R (P ⧸ J)] {x : P}
    (hxJ : x ∈ J) (hxI : x ∈ I.map (algebraMap R P)) : x ∈ I.map (algebraMap R P) * J := by
  classical

  have hrange : ∀ y ∈ I.map (algebraMap R P), ∃ τ : I ⊗[R] P, smulMapDLC2 I P τ = y := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => ∃ τ : I ⊗[R] P, smulMapDLC2 I P τ = y) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩ ⊗ₜ[R] 1, by simp [Algebra.smul_def]⟩
    · exact ⟨0, map_zero _⟩
    · rintro _ _ _ _ ⟨τ₁, rfl⟩ ⟨τ₂, rfl⟩
      exact ⟨τ₁ + τ₂, map_add _ _ _⟩
    · rintro a _ hmem ⟨τ, rfl⟩
      clear hmem
      induction τ using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | tmul i p => exact ⟨i ⊗ₜ[R] (a * p), by simp [smul_eq_mul, Algebra.smul_def, mul_left_comm]⟩
      | add x y hx hy =>
        obtain ⟨τ₁, h₁⟩ := hx
        obtain ⟨τ₂, h₂⟩ := hy
        exact ⟨τ₁ + τ₂, by rw [map_add, map_add, smul_add, h₁, h₂]⟩
  obtain ⟨τ, rfl⟩ := hrange x hxI

  let ι : J.restrictScalars R →ₗ[R] P := (J.restrictScalars R).subtype
  let q : P →ₗ[R] P ⧸ J := (Ideal.Quotient.mkₐ R J).toLinearMap
  have hιq : Function.Exact ι q := by
    intro y
    constructor
    · intro hy
      exact ⟨⟨y, (Ideal.Quotient.eq_zero_iff_mem).1 hy⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact (Ideal.Quotient.eq_zero_iff_mem).2 z.2
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hex := lTensor_exact I hιq hq

  have h0 : (q.lTensor I) τ = 0 := by
    apply smulMapDLC2_injective_of_flat I (P ⧸ J)
    rw [← smulMapDLC2_naturality, map_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 hxJ
  obtain ⟨σ, hσ⟩ := (hex τ).1 h0
  rw [← hσ, ← smulMapDLC2_naturality]
  clear hσ

  induction σ using TensorProduct.induction_on with
  | zero => simp
  | tmul i j =>
    rw [smulMapDLC2_tmul, map_smul]
    change (i : R) • (j : P) ∈ _
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ i.2) j.2
  | add x y hx hy =>
    rw [map_add, map_add]
    exact Ideal.add_mem _ hx hy

end Purity

p2m_open_scoped "Ideal" in
theorem Ideal.map_maximalIdeal_le_of_finite_quotient_DLC2 {R : Type*} [CommRing R] [IsLocalRing R]
    {P : Type*} [CommRing P] [Algebra R P] (J : Ideal P) [Module.Finite R (P ⧸ J)]
    (𝔫 : Ideal P) [h𝔫 : 𝔫.IsMaximal] (h : J ≤ 𝔫) :
    (IsLocalRing.maximalIdeal R).map (algebraMap R P) ≤ 𝔫 := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  have hcomap : (𝔫.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = 𝔫 := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.2 h
  have hmax : (𝔫.map (Ideal.Quotient.mk J)).IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj h𝔫 with htop | hm
    · exfalso
      apply h𝔫.ne_top
      rw [← hcomap, htop, Ideal.comap_top]
    · exact hm
  have h2 := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (𝔫.map (Ideal.Quotient.mk J))
  have h3 : (𝔫.map (Ideal.Quotient.mk J)).comap (algebraMap R (P ⧸ J)) = 𝔫.comap (algebraMap R P) := by
    ext r
    rw [Ideal.mem_comap, Ideal.mem_comap,
      show algebraMap R (P ⧸ J) r = Ideal.Quotient.mk J (algebraMap R P r) from rfl,
      ← Ideal.mem_comap (f := Ideal.Quotient.mk J), hcomap]
  rw [h3] at h2
  rw [Ideal.map_le_iff_le_comap, ← IsLocalRing.eq_maximalIdeal h2]

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (N : ℕ) (J : Ideal (MvPolynomial (Fin N) R))
    [Module.Finite R (MvPolynomial (Fin N) R ⧸ J)] [Module.Flat R (MvPolynomial (Fin N) R ⧸ J)]
    (hfib : ∀ (𝔫 : Ideal (MvPolynomial (Fin N) (IsLocalRing.ResidueField R))) [𝔫.IsMaximal],
      Ideal.map (MvPolynomial.map (IsLocalRing.residue R)) J ≤ 𝔫 →
      ∃ g : Fin N → MvPolynomial (Fin N) (IsLocalRing.ResidueField R),
        (∀ i, g i ∈ Ideal.map (MvPolynomial.map (IsLocalRing.residue R)) J) ∧
        Ideal.map (algebraMap _ (Localization.AtPrime 𝔫)) (Ideal.map (MvPolynomial.map (IsLocalRing.residue R)) J) =
          Ideal.span (Set.range fun i => algebraMap _ (Localization.AtPrime 𝔫) (g i)))
    (𝔫 : Ideal (MvPolynomial (Fin N) R)) [𝔫.IsMaximal] (h𝔫 : J ≤ 𝔫) :
    ∃ g : Fin N → MvPolynomial (Fin N) R, (∀ i, g i ∈ J) ∧
      Ideal.map (algebraMap (MvPolynomial (Fin N) R) (Localization.AtPrime 𝔫)) J =
        Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin N) R) (Localization.AtPrime 𝔫) (g i)) := by
  classical

  let κ := IsLocalRing.ResidueField R
  let π : MvPolynomial (Fin N) R →+* MvPolynomial (Fin N) κ := MvPolynomial.map (IsLocalRing.residue R)
  have hπs : Function.Surjective π := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hkerπ : RingHom.ker π = (IsLocalRing.maximalIdeal R).map (algebraMap R (MvPolynomial (Fin N) R)) := by
    rw [MvPolynomial.ker_map, IsLocalRing.ker_residue, MvPolynomial.algebraMap_eq]

  have h𝔪𝔫 : (IsLocalRing.maximalIdeal R).map (algebraMap R (MvPolynomial (Fin N) R)) ≤ 𝔫 :=
    Ideal.map_maximalIdeal_le_of_finite_quotient_DLC2 J 𝔫 h𝔫
  have hker𝔫 : RingHom.ker π ≤ 𝔫 := hkerπ ▸ h𝔪𝔫

  have hcomap𝔫 : (𝔫.map π).comap π = 𝔫 := by
    rw [Ideal.comap_map_of_surjective _ hπs, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.2 hker𝔫
  haveI h𝔫bar : (𝔫.map π).IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hπs ‹𝔫.IsMaximal› with htop | hm
    · exfalso
      apply ‹𝔫.IsMaximal›.ne_top
      rw [← hcomap𝔫, htop, Ideal.comap_top]
    · exact hm
  have hJ𝔫bar : J.map π ≤ 𝔫.map π := Ideal.map_mono h𝔫

  obtain ⟨gbar, hgbarJ, hgbar⟩ := hfib (𝔫.map π) hJ𝔫bar
  choose g hgJ hg using fun i => (Ideal.mem_map_iff_of_surjective π hπs).1 (hgbarJ i)
  refine ⟨g, hgJ, ?_⟩
  have hgbar' : (⇑π ∘ g) = gbar := funext fun i => hg i

  set S := Localization.AtPrime 𝔫 with hS
  set M : Ideal S := J.map (algebraMap (MvPolynomial (Fin N) R) S) with hM
  set N' : Ideal S := Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin N) R) S (g i)) with hN'
  have hN'eq : N' = (Ideal.span (Set.range g)).map (algebraMap (MvPolynomial (Fin N) R) S) := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  have hN'M : N' ≤ M := by
    rw [hN'eq]
    exact Ideal.map_mono (Ideal.span_le.2 (Set.range_subset_iff.2 hgJ))
  refine le_antisymm ?_ hN'M

  have hMfg : M.FG := IsNoetherian.noetherian M
  refine Submodule.le_of_le_smul_of_le_jacobson_bot hMfg (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_

  rw [hM, Ideal.map_le_iff_le_comap]
  intro x hxJ
  rw [Ideal.mem_comap]

  have hx1 : algebraMap _ (Localization.AtPrime (𝔫.map π)) (π x) ∈
      (Ideal.span (Set.range gbar)).map (algebraMap _ (Localization.AtPrime (𝔫.map π))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    change _ ∈ Ideal.span (Set.range fun i => algebraMap _ (Localization.AtPrime (𝔫.map π)) (gbar i))
    rw [← hgbar]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hxJ)
  obtain ⟨⟨y, s⟩, hys⟩ := (IsLocalization.mem_map_algebraMap_iff (𝔫.map π).primeCompl _).1 hx1
  rw [← map_mul] at hys
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (𝔫.map π).primeCompl _).1 hys

  have hcy : (c : MvPolynomial (Fin N) κ) * y ∈ (Ideal.span (Set.range g)).map π := by
    rw [Ideal.map_span, ← Set.range_comp, hgbar']
    exact Ideal.mul_mem_left _ _ y.2
  obtain ⟨y₀, hy₀, hy₀'⟩ := (Ideal.mem_map_iff_of_surjective π hπs).1 hcy
  obtain ⟨w, hw⟩ := hπs ((c : MvPolynomial (Fin N) κ) * s)
  have hw𝔫 : w ∉ 𝔫 := by
    intro hw'
    have h1 : π w ∈ 𝔫.map π := Ideal.mem_map_of_mem π hw'
    rw [hw] at h1
    exact ((𝔫.map π).primeCompl.mul_mem c.2 s.2) h1
  have hz : w * x - y₀ ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R (MvPolynomial (Fin N) R)) * J := by
    refine Ideal.mem_map_mul_of_flat_quotient_DLC2 _ J ?_ ?_
    · exact J.sub_mem (J.mul_mem_left w hxJ) (Ideal.span_le.2 (Set.range_subset_iff.2 hgJ) hy₀)
    · rw [← hkerπ, RingHom.mem_ker, map_sub, map_mul, hw, hy₀', sub_eq_zero, ← hc]
      ring

  have hunit : IsUnit (algebraMap (MvPolynomial (Fin N) R) S w) := IsLocalization.map_units S (⟨w, hw𝔫⟩ : 𝔫.primeCompl)
  rw [← Ideal.unit_mul_mem_iff_mem _ hunit, ← map_mul,
    show w * x = y₀ + (w * x - y₀) by ring, map_add]
  refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
  · rw [hN'eq]
    exact Ideal.mem_map_of_mem _ hy₀
  · have h2 : ((IsLocalRing.maximalIdeal R).map (algebraMap R (MvPolynomial (Fin N) R)) * J).map
        (algebraMap (MvPolynomial (Fin N) R) S) ≤ IsLocalRing.maximalIdeal S • M := by
      rw [Ideal.map_mul, Ideal.smul_eq_mul]
      refine Ideal.mul_mono_left ?_
      have hmax := Localization.AtPrime.map_eq_maximalIdeal (I := 𝔫)
      exact (Ideal.map_mono h𝔪𝔫).trans hmax.le
    exact h2 (Ideal.mem_map_of_mem _ hz)

end S_Ideal_exists_map_localization_eq_span_of_flat_of_residueField_mvPolynomial
end P2MW
export P2MW.S_Ideal_exists_map_localization_eq_span_of_flat_of_residueField_mvPolynomial (solution)
