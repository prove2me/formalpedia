-- Prove2me | solution 1 for ModularCurve.NodeLocalized.isDiscreteValuationRing_coeffSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/d0a0e152-5f75-5993-a04c-35813cc76553

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring

set_option autoImplicit false
open ModularCurve ModularCurve.NodeLocalized
open scoped NumberField

namespace AnnulusUnif

noncomputable scoped instance instNumberFieldIntermediateField (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] : NumberField ↥K :=
  { to_charZero := inferInstance, to_finiteDimensional := inferInstance }

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

noncomputable def V : ValuationSubring ↥K := A.comap (algebraMap ↥K (AlgebraicClosure ℚ))

theorem mem_V {x : ↥K} : x ∈ V A K ↔ (x : AlgebraicClosure ℚ) ∈ A := ValuationSubring.mem_comap

section Integers

variable [FiniteDimensional ℚ K]

theorem coe_ringOfIntegers_mem (x : 𝓞 ↥K) : ((x : ↥K)) ∈ V A K := by
  obtain ⟨p, hpm, hpx⟩ := NumberField.RingOfIntegers.isIntegral_coe x
  have hv := Valuation.integer.integers (V A K).valuation
  have hint' : IsIntegral ↥((V A K).valuation.integer) (x : ↥K) := by
    refine ⟨p.map (Int.castRingHom _), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap ↥((V A K).valuation.integer) ↥K).comp
      (Int.castRingHom _)) (algebraMap ℤ ↥K)]
    exact hpx
  have hmem := Valuation.Integers.mem_of_integral hv hint'
  rwa [ValuationSubring.integer_valuation] at hmem

noncomputable def φ : 𝓞 ↥K →+* ↥(V A K) where
  toFun x := ⟨(x : ↥K), coe_ringOfIntegers_mem A K x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[scoped simp] theorem coe_φ (x : 𝓞 ↥K) : ((φ A K x : ↥(V A K)) : ↥K) = (x : ↥K) := rfl

noncomputable def 𝔭 : Ideal (𝓞 ↥K) := (IsLocalRing.maximalIdeal ↥(V A K)).comap (φ A K)

scoped instance 𝔭_isPrime : (𝔭 A K).IsPrime := Ideal.IsPrime.comap _

theorem mem_𝔭_iff (x : 𝓞 ↥K) : x ∈ 𝔭 A K ↔ ¬ IsUnit (φ A K x) := by
  show φ A K x ∈ IsLocalRing.maximalIdeal _ ↔ _
  exact IsLocalRing.mem_maximalIdeal _

theorem zero_notMem_primeCompl : (0 : 𝓞 ↥K) ∉ (𝔭 A K).primeCompl := fun h => h (zero_mem _)

noncomputable def D : Subalgebra (𝓞 ↥K) ↥K :=
  Localization.subalgebra.ofField ↥K (𝔭 A K).primeCompl
    (le_nonZeroDivisors_of_noZeroDivisors (zero_notMem_primeCompl A K))

scoped instance D_isLocalization : IsLocalization (𝔭 A K).primeCompl ↥(D A K) :=
  Localization.subalgebra.isLocalization_ofField ↥K (𝔭 A K).primeCompl _

theorem mem_D_iff (x : ↥K) : x ∈ D A K ↔ ∃ (a s : 𝓞 ↥K) (_ : s ∈ (𝔭 A K).primeCompl),
    x = algebraMap (𝓞 ↥K) ↥K a * (algebraMap (𝓞 ↥K) ↥K s)⁻¹ := Iff.rfl

end Integers

section Prime

variable {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q] (red : A →+* k)
  (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)

include hker in
theorem natCast_mem_maximalIdeal : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A :=
  (hker _).mp (by rw [map_natCast, CharP.cast_eq_zero])

variable [FiniteDimensional ℚ K]

theorem isUnit_V_of_isUnit_A (x : ↥(V A K))
    (hx : IsUnit (⟨((x : ↥K) : AlgebraicClosure ℚ), (mem_V A K).mp x.2⟩ : A)) : IsUnit x := by
  have hx0 : ((x : ↥K) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    apply not_isUnit_zero (M₀ := A)
    have : (⟨((x : ↥K) : AlgebraicClosure ℚ), (mem_V A K).mp x.2⟩ : A) = 0 := Subtype.ext h0
    rwa [this] at hx
  have hxK0 : (x : ↥K) ≠ 0 := fun h => hx0 (by rw [h]; rfl)
  obtain ⟨g, hg⟩ := hx.exists_right_inv
  have hg' : ((x : ↥K) : AlgebraicClosure ℚ) * (g : AlgebraicClosure ℚ) = 1 := by
    have := congrArg Subtype.val hg
    simpa using this
  have hginv : (g : AlgebraicClosure ℚ) = (((x : ↥K))⁻¹ : ↥K) := by
    rw [show ((((x : ↥K))⁻¹ : ↥K) : AlgebraicClosure ℚ) = (((x : ↥K) : AlgebraicClosure ℚ))⁻¹ from by push_cast; rfl]
    exact (eq_inv_of_mul_eq_one_right hg')
  have hmem : ((x : ↥K))⁻¹ ∈ V A K := by
    rw [mem_V, ← hginv]; exact g.2
  exact isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext (mul_inv_cancel₀ hxK0)⟩

theorem isUnit_A_of_isUnit_V (x : ↥(V A K)) (hx : IsUnit x) :
    IsUnit (⟨((x : ↥K) : AlgebraicClosure ℚ), (mem_V A K).mp x.2⟩ : A) := by
  obtain ⟨g, hg⟩ := hx.exists_right_inv
  have hg' : (x : ↥K) * (g : ↥K) = 1 := by
    have := congrArg Subtype.val hg; simpa using this
  have hg'' : ((x : ↥K) : AlgebraicClosure ℚ) * ((g : ↥K) : AlgebraicClosure ℚ) = 1 := by
    have := congrArg (fun t : ↥K => (t : AlgebraicClosure ℚ)) hg'; simpa using this
  exact isUnit_iff_exists_inv.mpr ⟨⟨((g : ↥K) : AlgebraicClosure ℚ), (mem_V A K).mp g.2⟩, Subtype.ext hg''⟩

include hker in
theorem not_isUnit_natCast_V : ¬ IsUnit ((q : ℕ) : ↥(V A K)) := by
  intro hu
  have := isUnit_A_of_isUnit_V A K _ hu
  have hq : (⟨(((q : ℕ) : ↥(V A K)) : ↥K) , (mem_V A K).mp ((q : ℕ) : ↥(V A K)).2⟩ : A) = ((q : ℕ) : A) := by
    apply Subtype.ext; push_cast; rfl
  rw [hq] at this
  exact (IsLocalRing.mem_maximalIdeal _).mp (natCast_mem_maximalIdeal A red hker) this

include hker in
theorem natCast_mem_𝔭 : ((q : ℕ) : 𝓞 ↥K) ∈ 𝔭 A K := by
  rw [mem_𝔭_iff, map_natCast]
  exact not_isUnit_natCast_V A K red hker

theorem 𝔭_ne_bot (hq𝔭 : ((q : ℕ) : 𝓞 ↥K) ∈ 𝔭 A K) : 𝔭 A K ≠ ⊥ := by
  intro h
  rw [h, Ideal.mem_bot] at hq𝔭
  exact (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime q).ne_zero) hq𝔭

theorem D_isDVR (hq𝔭 : ((q : ℕ) : 𝓞 ↥K) ∈ 𝔭 A K) : IsDiscreteValuationRing ↥(D A K) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 ↥K) (𝔭_ne_bot A K hq𝔭) ↥(D A K)

scoped instance D_isFractionRing : IsFractionRing ↥(D A K) ↥K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (𝔭 A K).primeCompl ↥(D A K) ↥K

theorem mem_V_of_mem_D (x : ↥K) (hx : x ∈ D A K) : x ∈ V A K := by
  obtain ⟨a, s, hs, rfl⟩ := (mem_D_iff A K x).mp hx
  refine mul_mem (coe_ringOfIntegers_mem A K a) ?_
  have hsu : IsUnit (φ A K s) := by
    by_contra h
    exact hs ((mem_𝔭_iff A K s).mpr h)
  obtain ⟨g, hg⟩ := hsu.exists_right_inv
  have hs0 : (s : ↥K) ≠ 0 := by
    intro h0
    have : φ A K s = 0 := Subtype.ext h0
    rw [this, zero_mul] at hg
    exact zero_ne_one hg
  have hg' : (s : ↥K) * (g : ↥K) = 1 := by
    have := congrArg Subtype.val hg; simpa using this
  have : (g : ↥K) = ((algebraMap (𝓞 ↥K) ↥K) s)⁻¹ := eq_inv_of_mul_eq_one_right hg'
  rw [← this]; exact g.2

end Prime

section VleD

variable {q : ℕ} [Fact q.Prime] [FiniteDimensional ℚ K]

theorem inv_uniformizer_mem (hq𝔭 : ((q : ℕ) : 𝓞 ↥K) ∈ 𝔭 A K) (x : ↥K) (hxV : x ∈ V A K) (hxD : x ∉ D A K) :
    ∃ π : ↥(D A K), Irreducible π ∧ ((π : ↥K))⁻¹ ∈ V A K := by
  haveI := D_isDVR A K hq𝔭
  have hx0 : x ≠ 0 := fun h => hxD (h ▸ zero_mem _)

  have hxinv : x⁻¹ ∈ D A K := by
    rcases ValuationRing.isInteger_or_isInteger ↥(D A K) x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact absurd (hy ▸ y.2) hxD
    · rw [← hy]; exact y.2
  set y : ↥(D A K) := ⟨x⁻¹, hxinv⟩ with hydef
  have hy0 : y ≠ 0 := fun h => (inv_ne_zero hx0) (congrArg Subtype.val h)
  have hynu : ¬ IsUnit y := by
    intro hu
    obtain ⟨y', hy'⟩ := hu.exists_right_inv
    apply hxD
    have h1 : x⁻¹ * (y' : ↥K) = 1 := by
      have := congrArg Subtype.val hy'; simpa using this
    have : (y' : ↥K) = x := by
      have := eq_inv_of_mul_eq_one_right h1
      rw [this, inv_inv]
    rw [← this]; exact y'.2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(D A K)
  obtain ⟨n, u, hyu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπ
  have hn : n ≠ 0 := by
    rintro rfl
    apply hynu
    rw [hyu, pow_zero, mul_one]
    exact Units.isUnit u
  refine ⟨π, hπ, ?_⟩

  have hyK : (x⁻¹ : ↥K) = ((u : ↥(D A K)) : ↥K) * ((π : ↥K)) ^ n := by
    have := congrArg Subtype.val hyu
    simpa using this
  have hπ0 : ((π : ↥K)) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have key : ((π : ↥K))⁻¹ = x * ((u : ↥(D A K)) : ↥K) * ((π : ↥K)) ^ (n - 1) := by
    have h2 : x * ((u : ↥(D A K)) : ↥K) * ((π : ↥K)) ^ (n - 1) * (π : ↥K) = 1 := by
      rw [mul_assoc _ _ (π : ↥K), ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn), mul_assoc, ← hyK,
        mul_inv_cancel₀ hx0]
    exact (eq_inv_of_mul_eq_one_left h2).symm
  rw [key]
  exact mul_mem (mul_mem hxV (mem_V_of_mem_D A K _ (u : ↥(D A K)).2)) (pow_mem (mem_V_of_mem_D A K _ π.2) _)

theorem mem_D_of_mem_V (hq𝔭 : ((q : ℕ) : 𝓞 ↥K) ∈ 𝔭 A K) (hqV : ¬ IsUnit ((q : ℕ) : ↥(V A K)))
    (x : ↥K) (hxV : x ∈ V A K) : x ∈ D A K := by
  haveI := D_isDVR A K hq𝔭
  by_contra hxD
  obtain ⟨π, hπ, hπinv⟩ := inv_uniformizer_mem A K hq𝔭 x hxV hxD

  have hqD0 : ((q : ℕ) : ↥(D A K)) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime q).ne_zero
  obtain ⟨m, w, hqw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hqD0 hπ
  have hqK : ((q : ℕ) : ↥K) = ((w : ↥(D A K)) : ↥K) * ((π : ↥K)) ^ m := by
    have := congrArg Subtype.val hqw
    simpa using this
  have hqinv : (((q : ℕ) : ↥K))⁻¹ ∈ V A K := by
    rw [hqK, mul_inv, ← inv_pow]
    refine mul_mem ?_ (pow_mem hπinv _)
    have hmemD : ((((w⁻¹ : (↥(D A K))ˣ) : ↥(D A K)) : ↥K)) ∈ D A K := (((w⁻¹ : (↥(D A K))ˣ) : ↥(D A K))).2
    have hprod : (((w : ↥(D A K)) : ↥K)) * (((w⁻¹ : (↥(D A K))ˣ) : ↥(D A K)) : ↥K) = 1 := by
      have h := w.mul_inv
      have := congrArg (fun t : ↥(D A K) => (t : ↥K)) h
      simp only [Subalgebra.coe_mul, Subalgebra.coe_one] at this
      exact this
    have hwinv : (((w : ↥(D A K)) : ↥K))⁻¹ = (((w⁻¹ : (↥(D A K))ˣ) : ↥(D A K)) : ↥K) :=
      (eq_inv_of_mul_eq_one_right hprod).symm
    rw [hwinv]
    exact mem_V_of_mem_D A K _ hmemD
  apply hqV
  have hq0 : ((q : ℕ) : ↥K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime q).ne_zero
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hqinv⟩, Subtype.ext ?_⟩
  show ((((q : ℕ) : ↥(V A K)) : ↥K)) * (((q : ℕ) : ↥K))⁻¹ = 1
  push_cast
  exact mul_inv_cancel₀ hq0

end VleD

section Transport

variable {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q] (red : A →+* k)
  (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) [FiniteDimensional ℚ K]

noncomputable def DtoV : ↥(D A K) →+* ↥(V A K) where
  toFun y := ⟨(y : ↥K), mem_V_of_mem_D A K _ y.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def ψ (hq𝔭 : ((q : ℕ) : 𝓞 ↥K) ∈ 𝔭 A K) (hqV : ¬ IsUnit ((q : ℕ) : ↥(V A K))) :
    ↥(D A K) ≃+* ↥(coeffSubring A K) where
  toFun y := ⟨((y : ↥K) : AlgebraicClosure ℚ), ⟨(mem_V A K).mp (mem_V_of_mem_D A K _ y.2), (y : ↥K).2⟩⟩
  invFun d := ⟨⟨(d : AlgebraicClosure ℚ), d.2.2⟩,
    mem_D_of_mem_V A K hq𝔭 hqV _ ((mem_V A K).mpr (by exact d.2.1))⟩
  left_inv y := rfl
  right_inv d := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem ψ_apply_coe (hq𝔭 : ((q : ℕ) : 𝓞 ↥K) ∈ 𝔭 A K) (hqV : ¬ IsUnit ((q : ℕ) : ↥(V A K))) (y : ↥(D A K)) :
    ((ψ A K hq𝔭 hqV y : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) = ((y : ↥K) : AlgebraicClosure ℚ) := rfl

theorem isUnit_coeffSubring_iff (d : ↥(coeffSubring A K)) :
    IsUnit d ↔ IsUnit (⟨(d : AlgebraicClosure ℚ), d.2.1⟩ : A) := by
  constructor
  · intro h
    exact h.map (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring))
  · intro h
    have hd0 : (d : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      apply not_isUnit_zero (M₀ := A)
      have : (⟨(d : AlgebraicClosure ℚ), d.2.1⟩ : A) = 0 := Subtype.ext h0
      rwa [this] at h
    obtain ⟨g, hg⟩ := h.exists_right_inv
    have hg' : (d : AlgebraicClosure ℚ) * (g : AlgebraicClosure ℚ) = 1 := by
      have := congrArg Subtype.val hg; simpa using this
    have hginv : (g : AlgebraicClosure ℚ) = (d : AlgebraicClosure ℚ)⁻¹ := eq_inv_of_mul_eq_one_right hg'
    have hgK : (g : AlgebraicClosure ℚ) ∈ K := by
      rw [hginv]; exact inv_mem d.2.2
    exact isUnit_iff_exists_inv.mpr ⟨⟨(g : AlgebraicClosure ℚ), ⟨g.2, hgK⟩⟩, Subtype.ext hg'⟩

include hker in
theorem redRestrict_eq_zero_iff_not_isUnit (d : ↥(coeffSubring A K)) :
    redRestrict red K d = 0 ↔ ¬ IsUnit d := by
  rw [isUnit_coeffSubring_iff]
  show red ⟨(d : AlgebraicClosure ℚ), d.2.1⟩ = 0 ↔ _
  exact (hker _).trans ⟨fun h => (IsLocalRing.mem_maximalIdeal _).mp h, fun h => (IsLocalRing.mem_maximalIdeal _).mpr h⟩

theorem isUnit_V_of_isUnit_D (y : ↥(D A K)) (hy : IsUnit y) : IsUnit (DtoV A K y) := hy.map _

include hker in

theorem main : ∃ ϖ : ↥(coeffSubring A K),
    (∀ d : ↥(coeffSubring A K), redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') ∧
    ∃ (eK : ℕ) (ε : ↥(coeffSubring A K)), 1 ≤ eK ∧ IsUnit ε ∧
      ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε := by
  have hq𝔭 := natCast_mem_𝔭 A K red hker
  have hqV := not_isUnit_natCast_V A K red hker
  haveI := D_isDVR A K hq𝔭
  let e := ψ A K hq𝔭 hqV
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(D A K)
  have hmax : IsLocalRing.maximalIdeal ↥(D A K) = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  refine ⟨e π, fun d => ?_, ?_⟩
  ·
    rw [redRestrict_eq_zero_iff_not_isUnit A K red hker d]
    have hunit : IsUnit d ↔ IsUnit (e.symm d) :=
      ⟨fun h => by simpa using h.map e.symm, fun h => by simpa using h.map e⟩
    have h3 : ¬ IsUnit (e.symm d) ↔ e.symm d ∈ IsLocalRing.maximalIdeal ↥(D A K) :=
      (IsLocalRing.mem_maximalIdeal _).symm
    rw [hunit, h3, hmax, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨e t, ?_⟩
      have := congrArg e ht
      simpa using this
    · rintro ⟨d', hd'⟩
      refine ⟨e.symm d', ?_⟩
      have := congrArg e.symm hd'
      simpa using this
  ·
    have hqD0 : ((q : ℕ) : ↥(D A K)) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime q).ne_zero
    obtain ⟨m, w, hqw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hqD0 hπ
    have hm : m ≠ 0 := by
      rintro rfl
      apply hqV
      rw [pow_zero, mul_one] at hqw
      have h1 : IsUnit ((q : ℕ) : ↥(D A K)) := by rw [hqw]; exact Units.isUnit w
      have h2 := isUnit_V_of_isUnit_D A K _ h1
      rwa [map_natCast] at h2
    refine ⟨m, e (w : ↥(D A K)), Nat.pos_of_ne_zero hm, (Units.isUnit w).map e, ?_⟩
    have := congrArg e hqw
    rw [map_natCast, map_mul, map_pow] at this
    rw [this, mul_comm]

end Transport

end AnnulusUnif
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring.AnnulusUnif"

namespace AnnulusUnif

section DVR

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q] (red : A →+* k)
  (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) [FiniteDimensional ℚ K]

theorem isDVR_coeffSubring (hq𝔭 : ((q : ℕ) : 𝓞 ↥K) ∈ 𝔭 A K) (hqV : ¬ IsUnit ((q : ℕ) : ↥(V A K))) :
    IsDiscreteValuationRing ↥(coeffSubring A K) := by
  haveI := D_isDVR A K hq𝔭
  let e : ↥(D A K) ≃+* ↥(coeffSubring A K) := ψ A K hq𝔭 hqV
  haveI : IsNoetherianRing ↥(coeffSubring A K) := isNoetherianRing_of_ringEquiv ↥(D A K) e
  haveI : IsLocalRing ↥(coeffSubring A K) :=
    IsLocalRing.of_surjective' (e : ↥(D A K) →+* ↥(coeffSubring A K)) e.surjective
  have hnf : ¬ IsField ↥(coeffSubring A K) := fun hF =>
    IsDiscreteValuationRing.not_isField ↥(D A K) (MulEquiv.isField hF e.toMulEquiv)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(D A K)
  have hmaxD : IsLocalRing.maximalIdeal ↥(D A K) = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hcomap : (IsLocalRing.maximalIdeal ↥(coeffSubring A K)).comap (e : ↥(D A K) →+* ↥(coeffSubring A K)) =
      IsLocalRing.maximalIdeal ↥(D A K) := by
    have hm := Ideal.comap_isMaximal_of_surjective (e : ↥(D A K) →+* ↥(coeffSubring A K)) e.surjective
      (K := IsLocalRing.maximalIdeal ↥(coeffSubring A K))
    exact IsLocalRing.eq_maximalIdeal hm
  have hmax : IsLocalRing.maximalIdeal ↥(coeffSubring A K) = Ideal.span {e π} := by
    rw [← Ideal.map_comap_of_surjective (e : ↥(D A K) →+* ↥(coeffSubring A K)) e.surjective
      (IsLocalRing.maximalIdeal _), hcomap, hmaxD, Ideal.map_span, Set.image_singleton]
    rfl
  have hP : (IsLocalRing.maximalIdeal ↥(coeffSubring A K)).IsPrincipal := ⟨⟨e π, hmax⟩⟩
  exact ((IsDiscreteValuationRing.TFAE ↥(coeffSubring A K) hnf).out 0 4).mpr hP

end DVR
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring.AnnulusUnif"

end AnnulusUnif
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring.AnnulusUnif"

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    IsDiscreteValuationRing ↥(coeffSubring A K) :=
  AnnulusUnif.isDVR_coeffSubring A K (AnnulusUnif.natCast_mem_𝔭 A K red hker) (AnnulusUnif.not_isUnit_natCast_V A K red hker)

end S_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring (solution)
