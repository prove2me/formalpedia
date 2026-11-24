-- Prove2me | solution 1 for GlobalTheory.CNorm.kummer_basic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:22:56.466372+00:00
-- url     : https://prove2.me/submissions/9d659205-4e68-45d3-bc39-74afde7c971a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_KummerGalois
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CyclicKummerNormFixedHilbert90
import Theorems.Thm_GlobalTheory_CNorm_kummer_galois
import Theorems.Thm_GlobalTheory_CNorm_mem_kNorm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
open NumberField IsDedekindDomain Polynomial
open scoped WithZero TensorProduct
namespace GlobalTheory.CNorm
namespace _root_.GlobalTheory.CNorm
theorem _root_.solution : ∀ (p : ℕ) (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), _root_.GlobalTheory.CNorm.IsKum p ζ δ θ σ → FiniteDimensional F E ∧ Module.finrank F E = p ∧ (∀ y : E, σ^[p] y = y) ∧ (∀ y : E, σ y = y → ∃ a : F, y = algebraMap F E a) ∧ (∀ y : E, ∏ i ∈ Finset.range p, σ^[i] y = 1 → ∃ z : E, z ≠ 0 ∧ y = σ z / z) ∧ (∀ (u : F) (y : E), y ^ p = algebraMap F E u → ∃ (k : ℕ) (r : F), u = δ ^ k * r ^ p) ∧ ∀ x : Fˣ, x ∈ _root_.GlobalTheory.CNorm.kNorm p (RingHom.id F) δ ↔ ∃ y : E, ∏ i ∈ Finset.range p, σ^[i] y = algebraMap F E (x : F) := by
  intro p F E _ _ _ _ ζ δ θ σ h
  obtain ⟨hfd, hrank, hgal, hord, hgen, ⟨e⟩, -⟩ :=
    _root_.GlobalTheory.CNorm.kummer_galois p F E ζ δ θ σ h
  have hp := h.prime
  classical
  have hprod : ∀ y : E, algebraMap F E (Algebra.norm F y) = ∏ i ∈ Finset.range p, σ^[i] y := by
    intro y
    rw [Algebra.norm_eq_prod_automorphisms]
    have huniv : (Finset.univ : Finset Gal(E/F)) = (Finset.range p).image (σ ^ ·) := by
      ext τ
      simp only [Finset.mem_univ, true_iff]
      rw [← hord]
      exact mem_zpowers_iff_mem_range_orderOf.1 (hgen τ)
    rw [huniv, Finset.prod_image]
    · exact Finset.prod_congr rfl fun i _ => by rw [AlgEquiv.coe_pow]
    · intro i hi j hj hij
      exact pow_injOn_Iio_orderOf (by rw [hord]; simpa using hi) (by rw [hord]; simpa using hj) hij
  have hfix : ∀ y : E, σ y = y → ∃ a : F, y = algebraMap F E a := by
    intro y hy
    have hmem : y ∈ (⊥ : IntermediateField F E) := by
      rw [IsGalois.mem_bot_iff_fixed]
      intro τ
      have hσ : σ ∈ MulAction.stabilizer Gal(E/F) y := MulAction.mem_stabilizer_iff.2 hy
      exact MulAction.mem_stabilizer_iff.1 ((Subgroup.zpowers_le.2 hσ) (hgen τ))
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 hmem
    exact ⟨a, ha.symm⟩
  refine ⟨hfd, hrank, ?_, hfix, ?_, ?_, ?_⟩
  · intro y
    rw [← AlgEquiv.coe_pow, ← hord, pow_orderOf_eq_one]
    rfl
  · intro y hy
    haveI : IsCyclic Gal(E/F) := ⟨⟨σ, fun τ => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen τ)
      exact ⟨k, hk⟩⟩⟩
    have hn : Algebra.norm F y = 1 :=
      (algebraMap F E).injective (by rw [hprod, hy, map_one])
    obtain ⟨z, hz⟩ := groupCohomology.exists_div_of_norm_eq_one hgen hn
    refine ⟨(z : E)⁻¹, inv_ne_zero z.ne_zero, ?_⟩
    rw [map_inv₀, inv_div_inv, hz]
  · intro u y hy
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hζ := h.root.map_of_injective (algebraMap F E).injective
    by_cases hy0 : y = 0
    · refine ⟨1, 0, ?_⟩
      subst hy0
      rw [zero_pow hp.ne_zero] at hy
      have hu : u = 0 := (algebraMap F E).injective (by rw [← hy, map_zero])
      simp [hu, hp.ne_zero]
    · have hσy : (σ y / y) ^ p = 1 := by
        rw [div_pow, ← map_pow, hy, AlgEquiv.commutes, ← hy]
        exact div_self (pow_ne_zero _ hy0)
      obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one hσy
      have hσy' : σ y = algebraMap F E ζ ^ j * y := by
        rw [hj]; field_simp
      have hδ : δ ≠ 0 := by
        intro hδ
        exact h.nonpow 0 (by rw [hδ, zero_pow hp.ne_zero])
      have hθ : θ ≠ 0 := by
        intro hθ
        have := h.pow
        rw [hθ, zero_pow hp.ne_zero, eq_comm, map_eq_zero] at this
        exact hδ this
      have hζ0 : algebraMap F E ζ ≠ 0 := hζ.ne_zero hp.ne_zero
      have hw : σ (y / θ ^ j) = y / θ ^ j := by
        rw [map_div₀, map_pow, h.conj, hσy', mul_pow]
        field_simp
      obtain ⟨a, ha⟩ := hfix _ hw
      have hy' : y = algebraMap F E a * θ ^ j := by
        rw [← ha]; field_simp
      refine ⟨j, a, (algebraMap F E).injective ?_⟩
      rw [← hy, hy', mul_pow, ← pow_mul, mul_comm j p, pow_mul, h.pow]
      simp only [map_mul, map_pow]
      ring
  · intro x
    rw [_root_.GlobalTheory.CNorm.mem_kNorm]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨e.symm w, ?_⟩
      rw [← hprod, Algebra.norm_eq_of_algEquiv, hw]
      rfl
    · rintro ⟨y, hy⟩
      have hn : Algebra.norm F y = x := (algebraMap F E).injective (by rw [hprod, hy])
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [Algebra.norm_zero] at hn
        exact x.ne_zero hn.symm
      refine ⟨Units.map (e : E →* AdjoinRoot (X ^ p - C δ)) (Units.mk0 y hy0), ?_⟩
      simp only [Units.coe_map, Units.val_mk0, MonoidHom.coe_coe, RingHom.id_apply]
      rw [Algebra.norm_eq_of_algEquiv, hn]
end _root_.GlobalTheory.CNorm
end GlobalTheory.CNorm
