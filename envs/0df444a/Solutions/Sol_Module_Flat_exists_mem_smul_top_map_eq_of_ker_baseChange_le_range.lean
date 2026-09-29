-- Prove2me | solution 1 for Module.Flat.exists_mem_smul_top_map_eq_of_ker_baseChange_le_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6f7c12ba-3b81-5fa2-a8aa-0a59710634dc

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Flat_exists_mem_smul_top_map_eq_of_ker_baseChange_le_range

set_option autoImplicit false

universe u

namespace AlgLiftSol

open TensorProduct

theorem mem_smul_top_of_sum_smul_eq_zero {R : Type*} [CommRing R] (𝔪 : Ideal R) {n : ℕ} (x : Fin n → R)
    (hx : ∀ r : Fin n → R, ∑ b, r b * x b = 0 → ∀ b, r b ∈ 𝔪)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Flat R M]
    (z : Fin n → M) (hz : ∑ b, x b • z b = 0) (b : Fin n) : z b ∈ 𝔪 • (⊤ : Submodule R M) := by
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hz
  rw [hy b]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
  refine hx (fun i => a i j) ?_ b
  rw [← ha j]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem one_tmul_eq_zero_of_mem {R : Type*} [CommRing R] (k : Type*) [CommRing k] [Algebra R k]
    {M : Type*} [AddCommGroup M] [Module R M] (z : M)
    (hz : z ∈ RingHom.ker (algebraMap R k) • (⊤ : Submodule R M)) : (1 : k) ⊗ₜ[R] z = 0 := by
  refine Submodule.smul_induction_on hz (fun μ hμ w _ => ?_) (fun u v hu hv => ?_)
  · rw [tmul_smul, smul_tmul', Algebra.smul_def, RingHom.mem_ker.mp hμ, zero_mul, zero_tmul]
  · rw [tmul_add, hu, hv, add_zero]

theorem smul_eq_zero_of_one_tmul_eq_zero {R : Type*} [CommRing R] (k : Type*) [CommRing k] [Algebra R k]
    (hk : Function.Surjective (algebraMap R k)) (x : R) (hx : ∀ m ∈ RingHom.ker (algebraMap R k), m * x = 0)
    {M : Type*} [AddCommGroup M] [Module R M] (u : M) (hu : (1 : k) ⊗ₜ[R] u = 0) : x • u = 0 := by

  let L : R →ₗ[R] M →ₗ[R] M := (LinearMap.lsmul R M).comp (LinearMap.mulRight R x)
  have hL : ∀ r v, L r v = (r * x) • v := fun r v => rfl
  have hker : (RingHom.ker (algebraMap R k)).restrictScalars R ≤ LinearMap.ker L := by
    intro m hm
    rw [LinearMap.mem_ker]
    ext v
    rw [hL, hx m hm, zero_smul, LinearMap.zero_apply]
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R k) hk
  let L' : k →ₗ[R] M →ₗ[R] M :=
    ((RingHom.ker (algebraMap R k)).liftQ L hker) ∘ₗ e.symm.toLinearEquiv.toLinearMap
  have h1 : L' 1 u = x • u := by
    show ((RingHom.ker (algebraMap R k)).liftQ L hker) (e.symm 1) u = x • u
    rw [map_one]
    show L 1 u = x • u
    rw [hL, one_mul]
  have h2 := congrArg (TensorProduct.lift L') hu
  rw [TensorProduct.lift.tmul, map_zero, h1] at h2
  exact h2

theorem exists_indep_repr {R : Type*} [CommRing R] (𝔪 : Ideal R) [h𝔪 : 𝔪.IsMaximal] (I : Ideal R)
    (hI : I * 𝔪 = ⊥) {M : Type*} [AddCommGroup M] [Module R M] (c : M)
    (hc : c ∈ I • (⊤ : Submodule R M)) :
    ∃ (n : ℕ) (x : Fin n → R), (∀ b, x b ∈ I) ∧
      (∀ r : Fin n → R, ∑ b, r b * x b = 0 → ∀ b, r b ∈ 𝔪) ∧ ∃ m : Fin n → M, c = ∑ b, x b • m b := by
  classical

  have hc' : c ∈ I • Submodule.span R (Set.range (id : M → M)) := by
    rwa [Set.range_id, Submodule.span_univ]
  obtain ⟨a, ha, hsum⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum I id c).mp hc'

  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hT : Module.IsTorsionBySet R (↥I) (𝔪 : Set R) := by
    rintro z ⟨μ, hμ⟩
    apply Subtype.ext
    show μ * (z : R) = 0
    have h : (z : R) * μ ∈ I * 𝔪 := Ideal.mul_mem_mul z.2 hμ
    rw [hI, Ideal.mem_bot] at h
    rw [mul_comm, h]
  letI instK : Module (R ⧸ 𝔪) ↥I := hT.module
  have hmk : ∀ (r : R) (z : ↥I), (Ideal.Quotient.mk 𝔪 r) • z = r • z := fun r z => rfl

  let y : ↥a.support → ↥I := fun u => ⟨a u, ha u⟩
  let W : Submodule (R ⧸ 𝔪) ↥I := Submodule.span (R ⧸ 𝔪) (Set.range y)
  haveI : Module.Finite (R ⧸ 𝔪) ↥W := Module.Finite.span_of_finite (R ⧸ 𝔪) (Set.finite_range y)
  let bW := Module.finBasis (R ⧸ 𝔪) ↥W
  have hcoe : ∀ q : Fin (Module.finrank (R ⧸ 𝔪) ↥W) → R,
      (((∑ b, Ideal.Quotient.mk 𝔪 (q b) • bW b : ↥W) : ↥I) : R) = ∑ b, q b * (((bW b : ↥W) : ↥I) : R) := by
    intro q
    rw [Submodule.coe_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Submodule.coe_smul, hmk]
    rfl
  refine ⟨Module.finrank (R ⧸ 𝔪) ↥W, fun b => (((bW b : ↥W) : ↥I) : R), fun b => ((bW b : ↥W) : ↥I).2, ?_, ?_⟩
  ·
    intro r hr b
    have h0 : ∑ b, Ideal.Quotient.mk 𝔪 (r b) • bW b = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      rw [hcoe r, hr]
      rfl
    exact Ideal.Quotient.eq_zero_iff_mem.mp (Fintype.linearIndependent_iff.mp bW.linearIndependent _ h0 b)
  ·
    have hyW : ∀ u : ↥a.support, y u ∈ W := fun u => Submodule.subset_span ⟨u, rfl⟩
    have hrep : ∀ u : ↥a.support, ∃ q : Fin (Module.finrank (R ⧸ 𝔪) ↥W) → R,
        (a u : R) = ∑ b, q b * (((bW b : ↥W) : ↥I) : R) := by
      intro u
      choose q hq using fun b => Ideal.Quotient.mk_surjective (bW.repr ⟨y u, hyW u⟩ b)
      refine ⟨q, ?_⟩
      have h1 : ∑ b, Ideal.Quotient.mk 𝔪 (q b) • bW b = ⟨y u, hyW u⟩ := by
        rw [← bW.sum_repr ⟨y u, hyW u⟩]
        exact Finset.sum_congr rfl fun b _ => by rw [hq]
      have h2 := congrArg (fun w : ↥W => ((w : ↥I) : R)) h1
      simp only at h2
      rw [hcoe q] at h2
      exact h2.symm
    choose r hr using hrep
    refine ⟨fun b => ∑ u : ↥a.support, r u b • (u : M), ?_⟩
    rw [← hsum]
    calc (a.sum fun i c => c • id i) = ∑ u : ↥a.support, a u • (u : M) := by
          rw [Finsupp.sum, ← Finset.sum_coe_sort]; rfl
      _ = ∑ u : ↥a.support, ∑ b, (((bW b : ↥W) : ↥I) : R) • (r u b • (u : M)) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [hr u, Finset.sum_smul]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [mul_comm, mul_smul]
      _ = ∑ b, (((bW b : ↥W) : ↥I) : R) • ∑ u : ↥a.support, r u b • (u : M) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.smul_sum]

end AlgLiftSol

open AlgLiftSol in
theorem solution
    {R : Type u} [CommRing R] (k : Type u) [Field k] [Algebra R k] (hk : Function.Surjective (algebraMap R k))
    (I : Ideal R) (hI : I * RingHom.ker (algebraMap R k) = ⊥)
    {C₀ C₁ C₂ : Type u} [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂]
    [Module.Flat R C₁] [Module.Flat R C₂]
    (d₀ : C₀ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] C₂)
    (hex : LinearMap.ker (d₁.baseChange k) ≤ LinearMap.range (d₀.baseChange k))
    (c : C₁) (hc : c ∈ I • (⊤ : Submodule R C₁)) (hdc : d₁ c = 0) :
    ∃ b ∈ I • (⊤ : Submodule R C₀), d₀ b = c := by
  classical
  haveI : (RingHom.ker (algebraMap R k)).IsMaximal := RingHom.ker_isMaximal_of_surjective (algebraMap R k) hk

  obtain ⟨n, x, hxI, hind, m, rfl⟩ := exists_indep_repr (RingHom.ker (algebraMap R k)) I hI c hc

  have hz : ∀ b, d₁ (m b) ∈ RingHom.ker (algebraMap R k) • (⊤ : Submodule R C₂) :=
    mem_smul_top_of_sum_smul_eq_zero (RingHom.ker (algebraMap R k)) x hind (fun b => d₁ (m b))
      (by rw [← hdc, map_sum]; exact (Finset.sum_congr rfl fun b _ => by rw [map_smul]).symm)

  have h2 : ∀ b, ∃ bb : C₀, (1 : k) ⊗ₜ[R] (d₀ bb) = (1 : k) ⊗ₜ[R] (m b) := by
    intro b
    have hmem : (1 : k) ⊗ₜ[R] m b ∈ LinearMap.ker (d₁.baseChange k) := by
      rw [LinearMap.mem_ker, LinearMap.baseChange_tmul, one_tmul_eq_zero_of_mem k _ (hz b)]
    obtain ⟨t, ht⟩ := hex hmem
    obtain ⟨bb, rfl⟩ := TensorProduct.mk_surjective (R := R) (M := C₀) (S := k) hk t
    exact ⟨bb, by rw [← ht]; exact (LinearMap.baseChange_tmul _ _ _).symm⟩
  choose bb hbb using h2

  refine ⟨∑ b, x b • bb b, Submodule.sum_mem _ fun b _ => Submodule.smul_mem_smul (hxI b) Submodule.mem_top, ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul]
  have h3 : (1 : k) ⊗ₜ[R] (d₀ (bb b) - m b) = 0 := by rw [TensorProduct.tmul_sub, hbb, sub_self]
  have hx : ∀ μ ∈ RingHom.ker (algebraMap R k), μ * x b = 0 := fun μ hμ => by
    have h : x b * μ ∈ I * RingHom.ker (algebraMap R k) := Ideal.mul_mem_mul (hxI b) hμ
    rw [hI, Ideal.mem_bot] at h
    rw [mul_comm, h]
  have h4 := smul_eq_zero_of_one_tmul_eq_zero k hk (x b) hx _ h3
  rwa [smul_sub, sub_eq_zero] at h4

end S_Module_Flat_exists_mem_smul_top_map_eq_of_ker_baseChange_le_range
end P2MW
export P2MW.S_Module_Flat_exists_mem_smul_top_map_eq_of_ker_baseChange_le_range (solution)
