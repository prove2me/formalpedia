-- Prove2me | solution 1 for IntermediateField.exists_etale_padicInt_integers_of_inertia_le_fixingSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/25fb8327-52f4-5650-b5b5-0c9f96eaea2a

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_PadicAlgCl_fixingSubgroup_adjoin_rootsOfUnity_coprime
import Theorems.Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_exists_etale_padicInt_integers_of_inertia_le_fixingSubgroup

set_option autoImplicit false

namespace E5ResShape
open Polynomial
section c12

open Polynomial IntermediateField

variable (p : ℕ) [hp : Fact p.Prime]
variable {L : Type} [Field L] [Algebra ℚ_[p] L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]

theorem isTorsionFree_padicInt_of_algebra (S : Type) [CommRing S] [IsDomain S] [Algebra ℚ_[p] S]
    [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] ℚ_[p] S] : Module.IsTorsionFree ℤ_[p] S := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r s hrs => ?_
  rw [Algebra.smul_def, mul_eq_zero] at hrs
  refine hrs.imp (fun h => ?_) id
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] S] at h
  have h' : algebraMap ℤ_[p] ℚ_[p] r = 0 := by
    by_contra hne
    exact (map_ne_zero_of_mem_nonZeroDivisors (algebraMap ℚ_[p] S)
      (FaithfulSMul.algebraMap_injective ℚ_[p] S) (mem_nonZeroDivisors_of_ne_zero hne)) h
  exact (map_eq_zero_iff _ (IsFractionRing.injective ℤ_[p] ℚ_[p])).mp h'

theorem separable_X_pow_sub_one_of_isUnit {R : Type} [CommRing R] {m : ℕ} (hm0 : 0 < m)
    (hu : IsUnit (m : R)) : ((X : R[X]) ^ m - C 1).Separable := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨u, hu⟩ := hu
  have hC : C ((u⁻¹ : Rˣ) : R) * C ((k + 1 : ℕ) : R) = 1 := by
    rw [← C_mul, ← hu, Units.inv_mul, C_1]
  refine ⟨-1, C ((u⁻¹ : Rˣ) : R) * X, ?_⟩
  rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow, Nat.add_sub_cancel, C_1]
  linear_combination (X : R[X]) ^ (k + 1) * hC

section generic

variable {E : Type} [Field E] [Algebra ℚ_[p] E] [Algebra ℤ_[p] E] [IsScalarTower ℤ_[p] ℚ_[p] E]
variable {m : ℕ} {ξ : E}

omit [Algebra ℚ_[p] E] [IsScalarTower ℤ_[p] ℚ_[p] E] in
theorem aeval_X_pow_sub_one (hξ : ξ ^ m = 1) : aeval ξ ((X : ℤ_[p][X]) ^ m - C 1) = 0 := by
  simp [hξ]

omit [Algebra ℚ_[p] E] [IsScalarTower ℤ_[p] ℚ_[p] E] in
theorem isIntegral_of_pow_eq_one (hξ : ξ ^ m = 1) (hm0 : 0 < m) : IsIntegral ℤ_[p] ξ :=
  ⟨(X : ℤ_[p][X]) ^ m - C 1, monic_X_pow_sub_C _ hm0.ne', by
    simpa [aeval_def] using aeval_X_pow_sub_one p hξ⟩

theorem minpoly_dvd (hξ : ξ ^ m = 1) (hm0 : 0 < m) : minpoly ℤ_[p] ξ ∣ (X : ℤ_[p][X]) ^ m - C 1 :=
  haveI := isTorsionFree_padicInt_of_algebra p E
  minpoly.isIntegrallyClosed_dvd (isIntegral_of_pow_eq_one p hξ hm0) (aeval_X_pow_sub_one p hξ)

theorem isUnit_natCast_padicInt {m : ℕ} (hm : ¬ p ∣ m) : IsUnit (m : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  have h1 : ‖((m : ℤ) : ℤ_[p])‖ ≤ 1 := PadicInt.norm_le_one _
  have h2 : ¬ ‖((m : ℤ) : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd]
    exact_mod_cast hm
  have : ‖((m : ℤ) : ℤ_[p])‖ = 1 := le_antisymm h1 (not_lt.mp h2)
  simpa using this

end generic

section cyclo

variable {m : ℕ} {ζ : L}

local notation "γ" => AdjoinSimple.gen ℚ_[p] ζ

omit [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
theorem gen_pow_eq_one (hζ : ζ ^ m = 1) : (γ) ^ m = 1 := by
  apply Subtype.ext
  simp [hζ]

theorem isIntegral_gen (hζ : ζ ^ m = 1) (hm0 : 0 < m) : IsIntegral ℤ_[p] (γ) :=
  isIntegral_of_pow_eq_one p (gen_pow_eq_one p hζ) hm0

omit [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
theorem isIntegral_gen_field (hζ : ζ ^ m = 1) (hm0 : 0 < m) : IsIntegral ℚ_[p] ζ :=
  ⟨(X : ℚ_[p][X]) ^ m - C 1, monic_X_pow_sub_C _ hm0.ne', by simp [hζ]⟩

theorem exists_unit_discr (hζ : ζ ^ m = 1) (hm0 : 0 < m) (hm : ¬ p ∣ m) :
    ∃ u : ℤ_[p]ˣ, Algebra.discr ℚ_[p] (adjoin.powerBasis (isIntegral_gen_field p hζ hm0)).basis
      = algebraMap ℤ_[p] ℚ_[p] u := by
  haveI : FiniteDimensional ℚ_[p] ℚ_[p]⟮ζ⟯ := adjoin.finiteDimensional (isIntegral_gen_field p hζ hm0)
  haveI := isTorsionFree_padicInt_of_algebra p ℚ_[p]⟮ζ⟯
  set B := adjoin.powerBasis (isIntegral_gen_field p hζ hm0) with hB
  have hgen : B.gen = γ := by simp [hB]
  have hint : IsIntegral ℤ_[p] (γ) := isIntegral_gen p hζ hm0

  set F : ℤ_[p][X] := minpoly ℤ_[p] (γ) with hF
  obtain ⟨H, hH⟩ := minpoly_dvd p (gen_pow_eq_one p hζ) hm0

  have hder : aeval (γ) (derivative ((X : ℤ_[p][X]) ^ m - C 1)) =
      aeval (γ) (derivative F) * aeval (γ) H := by
    rw [hH, derivative_mul, map_add, map_mul, map_mul, minpoly.aeval, zero_mul, add_zero]
  have hlhs : aeval (γ) (derivative ((X : ℤ_[p][X]) ^ m - C 1)) =
      algebraMap ℚ_[p] ℚ_[p]⟮ζ⟯ (m : ℚ_[p]) * (γ) ^ (m - 1) := by
    simp [derivative_X_pow]

  have hF' : IsIntegral ℤ_[p] (aeval (γ) (derivative F)) :=
    .of_mem_of_fg _ hint.fg_adjoin_singleton _ (aeval_mem_adjoin_singleton _ _)
  have hHint : IsIntegral ℤ_[p] (aeval (γ) H) :=
    .of_mem_of_fg _ hint.fg_adjoin_singleton _ (aeval_mem_adjoin_singleton _ _)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_norm (R := ℤ_[p]) ℚ_[p] hF')
  obtain ⟨nH, hnH⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_norm (R := ℤ_[p]) ℚ_[p] hHint)
  obtain ⟨u₀, hu₀⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_norm (R := ℤ_[p]) ℚ_[p] hint)

  have hu₀m : u₀ ^ m = 1 := by
    apply IsFractionRing.injective ℤ_[p] ℚ_[p]
    rw [map_pow, hu₀, ← map_pow, gen_pow_eq_one p hζ, map_one, map_one]
  have hu₀unit : IsUnit u₀ := IsUnit.of_pow_eq_one hu₀m hm0.ne'

  have hnorm : n * nH = (m : ℤ_[p]) ^ Module.finrank ℚ_[p] ℚ_[p]⟮ζ⟯ * u₀ ^ (m - 1) := by
    apply IsFractionRing.injective ℤ_[p] ℚ_[p]
    have := congrArg (Algebra.norm ℚ_[p]) hder
    rw [hlhs, map_mul, map_mul, map_pow, Algebra.norm_algebraMap] at this
    rw [map_mul, hn, hnH, ← this, map_mul, map_pow, map_pow, hu₀, map_natCast]
  have hnunit : IsUnit n := by
    have : IsUnit (n * nH) := by
      rw [hnorm]
      exact ((isUnit_natCast_padicInt p hm).pow _).mul (hu₀unit.pow _)
    exact isUnit_of_mul_isUnit_left this

  set d := Module.finrank ℚ_[p] ℚ_[p]⟮ζ⟯ with hd
  have hdiscr : Algebra.discr ℚ_[p] B.basis =
      algebraMap ℤ_[p] ℚ_[p] ((-1) ^ (d * (d - 1) / 2) * n) := by
    rw [Algebra.discr_powerBasis_eq_norm, map_mul, map_pow, map_neg, map_one, hn, hgen,
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hint, derivative_map,
      aeval_map_algebraMap]
  have hunit : IsUnit ((-1 : ℤ_[p]) ^ (d * (d - 1) / 2) * n) := (isUnit_one.neg.pow _).mul hnunit
  exact ⟨hunit.unit, by rw [hdiscr, IsUnit.unit_spec]⟩

theorem mem_adjoin_of_isIntegral (hζ : ζ ^ m = 1) (hm0 : 0 < m) (hm : ¬ p ∣ m) {z : ℚ_[p]⟮ζ⟯}
    (hz : IsIntegral ℤ_[p] z) : z ∈ Algebra.adjoin ℤ_[p] ({γ} : Set ℚ_[p]⟮ζ⟯) := by
  haveI : FiniteDimensional ℚ_[p] ℚ_[p]⟮ζ⟯ := adjoin.finiteDimensional (isIntegral_gen_field p hζ hm0)
  obtain ⟨u, hu⟩ := exists_unit_discr p hζ hm0 hm
  set B := adjoin.powerBasis (isIntegral_gen_field p hζ hm0) with hB
  have hgen : B.gen = γ := by simp [hB]
  have hint : IsIntegral ℤ_[p] B.gen := hgen ▸ isIntegral_gen p hζ hm0
  have h := Algebra.discr_mul_isIntegral_mem_adjoin (R := ℤ_[p]) (K := ℚ_[p]) hint hz
  rw [hgen, hu, algebraMap_smul ℚ_[p] (u : ℤ_[p]) z] at h
  have h3 := (Algebra.adjoin ℤ_[p] ({γ} : Set ℚ_[p]⟮ζ⟯)).smul_mem h ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
  rwa [smul_smul, Units.inv_mul, one_smul] at h3

theorem mem_adjoin_of_isIntegral_of_mem (hζ : ζ ^ m = 1) (hm0 : 0 < m) (hm : ¬ p ∣ m) {z : L}
    (hz : IsIntegral ℤ_[p] z) (hzE : z ∈ ℚ_[p]⟮ζ⟯) : z ∈ Algebra.adjoin ℤ_[p] ({ζ} : Set L) := by
  let ι : ℚ_[p]⟮ζ⟯ →ₐ[ℤ_[p]] L := (IntermediateField.val ℚ_[p]⟮ζ⟯).restrictScalars ℤ_[p]
  have hι : Function.Injective ι := Subtype.val_injective
  have hz' : IsIntegral ℤ_[p] (⟨z, hzE⟩ : ℚ_[p]⟮ζ⟯) := (isIntegral_algHom_iff ι hι).mp hz
  have hmem := mem_adjoin_of_isIntegral p hζ hm0 hm hz'
  have himage : ι (⟨z, hzE⟩ : ℚ_[p]⟮ζ⟯) ∈ (Algebra.adjoin ℤ_[p] ({γ} : Set ℚ_[p]⟮ζ⟯)).map ι :=
    Subalgebra.mem_map.mpr ⟨_, hmem, rfl⟩
  rwa [AlgHom.map_adjoin, Set.image_singleton] at himage

end cyclo

end c12

theorem isStandardEtale_adjoin_singleton {R S : Type} [CommRing R] [CommRing S] [IsDomain R]
    [IsIntegrallyClosed R] [IsDomain S] [Algebra R S] [Module.IsTorsionFree R S] {x : S}
    (hx : IsIntegral R x) (hsep : (minpoly R x).Separable) :
    Algebra.IsStandardEtale R ↥(Algebra.adjoin R ({x} : Set S)) := by
  classical

  obtain ⟨a, b, hab⟩ := hsep
  let P : StandardEtalePair R :=
    { f := minpoly R x
      monic_f := minpoly.monic hx
      g := 1
      cond := ⟨b, a, 0, by rw [pow_zero]; linear_combination hab⟩ }
  set B : Subalgebra R S := Algebra.adjoin R ({x} : Set S) with hBdef
  let xB : ↥B := ⟨x, Algebra.self_mem_adjoin_singleton R x⟩
  have hmap : P.HasMap xB := by
    refine ⟨Subtype.ext ?_, ?_⟩
    · rw [← Subalgebra.aeval_coe, ZeroMemClass.coe_zero]
      exact minpoly.aeval R x
    · show IsUnit (aeval xB (1 : R[X]))
      rw [map_one]; exact isUnit_one

  let φ : P.Ring →ₐ[R] ↥B := P.lift xB hmap
  have hPX : aeval P.X (minpoly R x) = 0 := StandardEtalePair.hasMap_X.1
  let ψ₀ : AdjoinRoot (minpoly R x) →ₐ[R] P.Ring :=
    AdjoinRoot.liftAlgHom (minpoly R x) (Algebra.ofId R P.Ring) P.X (by
      have h : (↑(Algebra.ofId R P.Ring) : R →+* P.Ring) = algebraMap R P.Ring := rfl
      rw [h, ← aeval_def]
      exact hPX)
  let e : AdjoinRoot (minpoly R x) ≃ₐ[R] ↥B := minpoly.equivAdjoin hx
  let ψ : ↥B →ₐ[R] P.Ring := ψ₀.comp (e.symm : ↥B →ₐ[R] AdjoinRoot (minpoly R x))
  have he_root : e (AdjoinRoot.root (minpoly R x)) = xB := by
    apply Subtype.ext
    show ((minpoly.equivAdjoin hx : AdjoinRoot (minpoly R x) →ₐ[R] ↥B) (AdjoinRoot.root _) : S) = x
    rw [minpoly.equivAdjoin_toAlgHom]
    simp [AdjoinRoot.Minpoly.toAdjoin]
  have hψφ : ψ.comp φ = AlgHom.id R P.Ring := by
    apply StandardEtalePair.hom_ext
    rw [AlgHom.comp_apply, AlgHom.id_apply, StandardEtalePair.lift_X]
    show ψ₀ (e.symm xB) = P.X
    rw [← he_root, AlgEquiv.symm_apply_apply, AdjoinRoot.liftAlgHom_root]
  have hinj : Function.Injective φ := fun u v huv => by
    have := congrArg ψ huv
    rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, hψφ, AlgHom.id_apply, AlgHom.id_apply] at this
  have hsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [hBdef, Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨q, rfl⟩ := hy
    refine ⟨aeval P.X q, Subtype.ext ?_⟩
    rw [← Polynomial.aeval_algHom_apply, StandardEtalePair.lift_X, ← Subalgebra.aeval_coe]
    rfl
  exact ⟨⟨⟨P, xB, hmap, ⟨hinj, hsurj⟩⟩⟩⟩

theorem etale_adjoin_singleton {R S : Type} [CommRing R] [CommRing S] [IsDomain R]
    [IsIntegrallyClosed R] [IsDomain S] [Algebra R S] [Module.IsTorsionFree R S] {x : S}
    (hx : IsIntegral R x) (hsep : (minpoly R x).Separable) :
    Algebra.Etale R ↥(Algebra.adjoin R ({x} : Set S)) :=
  haveI := isStandardEtale_adjoin_singleton hx hsep
  inferInstance

end E5ResShape

namespace E5ResShape

open Polynomial IntermediateField

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => AlgebraicClosure ℚ_[p]
local notation "Γ" => (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])

theorem exists_le_adjoin_rootOfUnity (K : IntermediateField ℚ_[p] Ω) (hK : FiniteDimensional ℚ_[p] K)
    (hKur : (padicIntegers p).inertiaSubgroupIn ℚ_[p] ≤ K.fixingSubgroup) :
    ∃ (m : ℕ) (ζ : Ω), 0 < m ∧ ¬ p ∣ m ∧ IsPrimitiveRoot ζ m ∧ K ≤ ℚ_[p]⟮ζ⟯ := by
  classical

  set S : Set Ω := {ζ : Ω | ∃ N : ℕ, ¬ p ∣ N ∧ ζ ^ N = 1} with hS
  have hKE : K ≤ IntermediateField.adjoin ℚ_[p] S := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ_[p] S),
      IntermediateField.le_iff_le, PadicAlgCl.fixingSubgroup_adjoin_rootsOfUnity_coprime p]
    exact hKur

  haveI := hK
  obtain ⟨s, hs⟩ := Module.finite_def.mp hK
  have hT : ∀ k : ↥K, ∃ T : Finset Ω, ↑T ⊆ S ∧ (k : Ω) ∈ IntermediateField.adjoin ℚ_[p] (↑T : Set Ω) :=
    fun k => IntermediateField.exists_finset_of_mem_adjoin (hKE k.2)
  choose T hTS hTmem using hT
  set T₀ : Finset Ω := s.biUnion T with hT₀
  have hT₀S : (↑T₀ : Set Ω) ⊆ S := by
    intro t ht
    obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp ht)
    exact hTS k hk
  have hKT₀ : K ≤ IntermediateField.adjoin ℚ_[p] (↑T₀ : Set Ω) := by
    intro k hk
    have hk' : (⟨k, hk⟩ : ↥K) ∈ Submodule.span ℚ_[p] (↑s : Set ↥K) := by rw [hs]; exact Submodule.mem_top

    have himg : k ∈ Submodule.span ℚ_[p] ((K.val : ↥K →ₗ[ℚ_[p]] Ω) '' (↑s : Set ↥K)) := by
      rw [← Submodule.map_span]
      exact ⟨⟨k, hk⟩, hk', rfl⟩
    have hle : Submodule.span ℚ_[p] ((K.val : ↥K →ₗ[ℚ_[p]] Ω) '' (↑s : Set ↥K)) ≤
        Subalgebra.toSubmodule (IntermediateField.adjoin ℚ_[p] (↑T₀ : Set Ω)).toSubalgebra := by
      rw [Submodule.span_le]
      rintro _ ⟨k', hk's, rfl⟩
      exact IntermediateField.adjoin.mono _ _ _ (by
        intro t ht; exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨k', hk's, ht⟩)) (hTmem k')
    exact hle himg

  have hN : ∀ t : Ω, t ∈ T₀ → ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ t ^ N = 1 := by
    intro t ht
    obtain ⟨N, hpN, htN⟩ := hT₀S (Finset.mem_coe.mpr ht)
    rcases Nat.eq_zero_or_pos N with rfl | hN0
    · exact absurd (dvd_zero p) hpN
    · exact ⟨N, hN0, hpN, htN⟩
  choose N hN0 hNp hNpow using hN
  let N' : Ω → ℕ := fun t => if h : t ∈ T₀ then N t h else 1
  set m : ℕ := ∏ t ∈ T₀, N' t with hm_def
  have hm0 : 0 < m := Finset.prod_pos fun t ht => by
    simp only [N', dif_pos ht]
    exact hN0 t ht
  have hpm : ¬ p ∣ m := fun h => by
    obtain ⟨t, ht, hdt⟩ := ((Fact.out : p.Prime).prime.dvd_finsetProd_iff N').mp h
    simp only [N', dif_pos ht] at hdt
    exact hNp t ht hdt
  have htm : ∀ t ∈ T₀, t ^ m = 1 := fun t ht => by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem N' ht
    rw [hm_def, hc, pow_mul]
    simp only [N', dif_pos ht]
    rw [hNpow t ht, one_pow]
  haveI : NeZero m := ⟨hm0.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  refine ⟨m, ζ, hm0, hpm, hζ, hKT₀.trans ?_⟩
  rw [IntermediateField.adjoin_le_iff]
  intro t ht
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one (htm t (Finset.mem_coe.mp ht))
  exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ) i

theorem apply_eq_of_mem_adjoin_simple {ζ : Ω} (hζ : IsIntegral ℚ_[p] ζ) (σ : Γ) (hσ : σ ζ = ζ)
    {x : Ω} (hx : x ∈ ℚ_[p]⟮ζ⟯) : σ x = x := by
  have hx' : x ∈ (ℚ_[p]⟮ζ⟯).toSubalgebra := hx
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζ.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hx'
  obtain ⟨q, rfl⟩ := hx'
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← Polynomial.aeval_algHom_apply]
  show aeval ((σ : Ω →ₐ[ℚ_[p]] Ω) ζ) q = aeval ζ q
  rw [AlgEquiv.coe_algHom, hσ]

end E5ResShape

open E5ResShape in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) (hK : FiniteDimensional ℚ_[p] K)
    (hKur : (padicIntegers p).inertiaSubgroupIn ℚ_[p] ≤ K.fixingSubgroup) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra ℤ_[p] B) (_ : Module.Finite ℤ_[p] B)
      (_ : Module.Free ℤ_[p] B) (_ : Algebra.Etale ℤ_[p] B)
      (_ : Algebra B (AlgebraicClosure ℚ_[p])) (_ : IsScalarTower ℤ_[p] B (AlgebraicClosure ℚ_[p])),
      (∀ σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]),
        (∀ b : B, σ (algebraMap B (AlgebraicClosure ℚ_[p]) b) = algebraMap B (AlgebraicClosure ℚ_[p]) b) →
          σ ∈ K.fixingSubgroup) ∧
      (∀ x : AlgebraicClosure ℚ_[p], x ∈ K → (padicIntegers p).valuation x = 1 →
        ∃ b : B, IsUnit b ∧ algebraMap B (AlgebraicClosure ℚ_[p]) b = x) := by
  classical
  obtain ⟨m, ζ, hm0, hpm, hζ, hKζ⟩ := exists_le_adjoin_rootOfUnity p K hK hKur
  have hζm : ζ ^ m = 1 := hζ.pow_eq_one
  haveI : Module.IsTorsionFree ℤ_[p] (AlgebraicClosure ℚ_[p]) :=
    isTorsionFree_padicInt_of_algebra p (AlgebraicClosure ℚ_[p])
  have hint : IsIntegral ℤ_[p] ζ := isIntegral_of_pow_eq_one p hζm hm0
  have hintQ : IsIntegral ℚ_[p] ζ := isIntegral_gen_field p hζm hm0

  set B : Subalgebra ℤ_[p] (AlgebraicClosure ℚ_[p]) := Algebra.adjoin ℤ_[p] ({ζ} : Set (AlgebraicClosure ℚ_[p]))
    with hBdef
  let pb : PowerBasis ℤ_[p] ↥B := Algebra.adjoin.powerBasis' hint
  have hsep : (minpoly ℤ_[p] ζ).Separable :=
    (separable_X_pow_sub_one_of_isUnit hm0 (isUnit_natCast_padicInt p hpm)).of_dvd (minpoly_dvd p hζm hm0)
  haveI hfin : Module.Finite ℤ_[p] ↥B := Module.Finite.of_basis pb.basis
  haveI hfree : Module.Free ℤ_[p] ↥B := Module.Free.of_basis pb.basis
  haveI het : Algebra.Etale ℤ_[p] ↥B := etale_adjoin_singleton hint hsep
  refine ⟨↥B, inferInstance, inferInstance, inferInstance, hfin, hfree, het, inferInstance, inferInstance,
    fun σ hσ => ?_, fun x hxK hvx => ?_⟩
  ·
    have hσζ : σ ζ = ζ := hσ ⟨ζ, Algebra.self_mem_adjoin_singleton ℤ_[p] ζ⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro k hk
    exact apply_eq_of_mem_adjoin_simple p hintQ σ hσζ (hKζ hk)
  ·
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hvx
      exact zero_ne_one hvx
    have key : ∀ y : AlgebraicClosure ℚ_[p], y ∈ K → (padicIntegers p).valuation y = 1 → y ∈ B := by
      intro y hyK hvy
      have hy1 : y ∈ padicIntegers p := ((padicIntegers p).valuation_le_one_iff y).mp hvy.le
      have hnorm : ‖(y : PadicAlgCl p)‖ ≤ 1 := by
        have h := (mem_padicIntegers_iff p).mp hy1
        exact_mod_cast h
      have hyint : IsIntegral ℤ_[p] y := (PadicAlgCl.isIntegral_padicInt_iff_norm_le_one p y).mpr hnorm
      exact mem_adjoin_of_isIntegral_of_mem p hζm hm0 hpm hyint (hKζ hyK)
    have hxB : x ∈ B := key x hxK hvx
    have hxiB : x⁻¹ ∈ B := key x⁻¹ (inv_mem hxK) (by rw [map_inv₀, hvx, inv_one])
    refine ⟨⟨x, hxB⟩, IsUnit.of_mul_eq_one ⟨x⁻¹, hxiB⟩ (Subtype.ext ?_), rfl⟩
    show x * x⁻¹ = 1
    exact mul_inv_cancel₀ hx0

end S_IntermediateField_exists_etale_padicInt_integers_of_inertia_le_fixingSubgroup
end P2MW
export P2MW.S_IntermediateField_exists_etale_padicInt_integers_of_inertia_le_fixingSubgroup (solution)
