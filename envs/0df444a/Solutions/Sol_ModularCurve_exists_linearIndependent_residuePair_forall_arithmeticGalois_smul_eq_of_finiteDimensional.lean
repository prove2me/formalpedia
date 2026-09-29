-- Prove2me | solution 1 for ModularCurve.exists_linearIndependent_residuePair_forall_arithmeticGalois_smul_eq_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/590f49f7-0252-5e41-ae1e-04be1cc70200

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_geomAut
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_linearIndependent_residuePair_forall_arithmeticGalois_smul_eq_of_finiteDimensional

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve IsLocalRing ModularCurve

set_option autoImplicit false
open Matrix

namespace S12EL
namespace Cart

section Field
variable {k : Type*} [Field k] {ι : Type*} {n : ℕ}

def colAt (f : Fin n → ι → k) (i : ι) : Fin n → k := fun j => f j i

theorem span_range_colAt_eq_top (f : Fin n → ι → k) (hf : LinearIndependent k f) :
    Submodule.span k (Set.range (colAt f)) = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)

  set c : Fin n → k := fun j => φ (Pi.single j 1) with hc
  have hφ : ∀ v : Fin n → k, φ v = ∑ j, v j * c j := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ φ v]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul]
    congr 2
    ext i
    simp [Pi.single_apply, eq_comm]

  have hsum : ∑ j, c j • f j = 0 := by
    ext i
    have hi : φ (colAt f i) = 0 := hle (Submodule.subset_span ⟨i, rfl⟩)
    rw [hφ] at hi
    simpa [colAt, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hi
  have hc0 : ∀ j, c j = 0 := Fintype.linearIndependent_iff.mp hf c hsum
  apply hφ0
  apply LinearMap.pi_ext'
  intro j
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single, LinearMap.zero_comp,
    LinearMap.zero_apply]
  have := hc0 j
  simp only [hc] at this
  simpa using this

theorem exists_submatrix_det_ne_zero_of_linearIndependent (f : Fin n → ι → k) (hf : LinearIndependent k f) :
    ∃ s : Fin n → ι, Function.Injective s ∧ (Matrix.of fun l j => f j (s l)).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' k (colAt f)
  rw [span_range_colAt_eq_top f hf] at hspan

  let b : Module.Basis κ k (Fin n → k) := Module.Basis.mk hli (by rw [hspan])
  let e : Fin n ≃ κ := (b.indexEquiv (Pi.basisFun k (Fin n))).symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩

  have hrows : LinearIndependent k (Matrix.of fun l j => f j ((a ∘ e) l)).row := by
    have h2 : LinearIndependent k (colAt f ∘ a ∘ e) := (hli.comp e e.injective)
    convert h2 using 1
    all_goals try rfl
  have hU : IsUnit (Matrix.of fun l j => f j ((a ∘ e) l)) := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hU).ne_zero

end Field

section LocalRing
variable {A : Type*} [CommRing A] [IsLocalRing A] {ι : Type*} {n : ℕ}

theorem exists_submatrix_isUnit_det_of_linearIndependent_residue (b : Fin n → ι → A)
    (hb : LinearIndependent (IsLocalRing.ResidueField A) (fun j i => IsLocalRing.residue A (b j i))) :
    ∃ s : Fin n → ι, Function.Injective s ∧ IsUnit (Matrix.of fun l j => b j (s l)).det := by
  obtain ⟨s, hs, hdet⟩ := exists_submatrix_det_ne_zero_of_linearIndependent _ hb
  refine ⟨s, hs, ?_⟩
  have hmap : IsLocalRing.residue A (Matrix.of fun l j => b j (s l)).det
      = (Matrix.of fun l j => IsLocalRing.residue A (b j (s l))).det := by
    rw [RingHom.map_det]; rfl
  have hne : IsLocalRing.residue A (Matrix.of fun l j => b j (s l)).det ≠ 0 := hmap ▸ hdet
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne

end LocalRing

end S12EL.Cart

set_option autoImplicit false

namespace S12EL
namespace D3

theorem linearIndependent_map_of_linearIndependent {k' k : Type*} [Field k'] [Field k] (σ : k' →+* k)
    {ι : Type*} {n : ℕ} (f : Fin n → ι → k') (hf : LinearIndependent k' f) :
    LinearIndependent k (fun j => fun i => σ (f j i)) := by
  classical
  obtain ⟨s, hs, hdet⟩ := S12EL.Cart.exists_submatrix_det_ne_zero_of_linearIndependent f hf

  set M : Matrix (Fin n) (Fin n) k' := Matrix.of fun l j => f j (s l) with hM
  have hdet' : (M.map σ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero σ).mpr hdet

  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hcol : (M.map σ) *ᵥ c = 0 := by
    ext l
    have := congrFun hc (s l)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [Matrix.mulVec, Pi.zero_apply]
    simp only [dotProduct, Matrix.map_apply, hM, Matrix.of_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have := Matrix.eq_zero_of_mulVec_eq_zero hdet' hcol
  exact congrFun this j

end S12EL.D3

open IsLocalRing

namespace S12EL
namespace Cartesian

variable {A₀ : Type*} [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
variable {ι : Type*}

theorem exists_basis_residue_linearIndependent (M : Submodule A₀ (ι → A₀))
    (hsat : ∀ (a : A₀) (v : ι → A₀), a ≠ 0 → a • v ∈ M → v ∈ M)
    (hfin : ∃ s : Finset ι, ∀ v ∈ M, (∀ i ∈ s, v i = 0) → v = 0) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) A₀ M),
      LinearIndependent (ResidueField A₀)
        (fun j => fun i => residue A₀ (((b j : M) : ι → A₀) i)) := by
  classical
  obtain ⟨s, hs⟩ := hfin

  let res : (ι → A₀) →ₗ[A₀] (s → A₀) := LinearMap.pi fun i : s => LinearMap.proj (i : ι)
  have hres_inj : ∀ v ∈ M, res v = 0 → v = 0 := by
    intro v hv h0
    refine hs v hv fun i hi => ?_
    have := congrFun h0 ⟨i, hi⟩
    simpa [res] using this
  let resM : M →ₗ[A₀] (s → A₀) := res.comp M.subtype
  have hresM : Function.Injective resM := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    exact Subtype.ext (hres_inj _ x.2 hx)
  haveI : Module.Finite A₀ M := Module.Finite.of_injective resM hresM
  haveI : NoZeroSMulDivisors A₀ M := by
    refine ⟨fun {c x} h => ?_⟩
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      have : c • (x : ι → A₀) = 0 := by simpa using congrArg Subtype.val h
      ext i
      have := congrFun this i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_eq_zero] at this
      simpa using this.resolve_left hc
  haveI : Module.Free A₀ M := Module.free_of_finite_type_torsion_free'
  set n := Module.finrank A₀ M
  let b : Module.Basis (Fin n) A₀ M := Module.finBasis A₀ M
  refine ⟨n, b, ?_⟩

  rw [Fintype.linearIndependent_iff]
  intro cbar hrel
  choose c hc using fun j => Ideal.Quotient.mk_surjective (I := maximalIdeal A₀) (cbar j)
  set v : M := ∑ j, c j • b j with hvdef
  have hvi : ∀ i, ((v : M) : ι → A₀) i = ∑ j, c j * ((b j : M) : ι → A₀) i := by
    intro i
    simp [hvdef, Submodule.coe_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hv𝔪 : ∀ i, ((v : M) : ι → A₀) i ∈ maximalIdeal A₀ := by
    intro i
    have hi := congrFun hrel i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    rw [← Ideal.Quotient.eq_zero_iff_mem, hvi i, map_sum]
    simp only [map_mul, hc]
    exact hi

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A₀
  have hmax : maximalIdeal A₀ = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖ
  have hdiv : ∀ i, ∃ w : A₀, w * ϖ = ((v : M) : ι → A₀) i := fun i =>
    Ideal.mem_span_singleton'.mp (hmax ▸ hv𝔪 i)
  choose w hw using hdiv
  have hvw : ((v : M) : ι → A₀) = ϖ • (fun i => w i) := by
    ext i; simp [← hw i, mul_comm]
  have hwM : (fun i => w i) ∈ M := hsat ϖ _ hϖ.ne_zero (hvw ▸ v.2)
  have hvw' : v = ϖ • (⟨_, hwM⟩ : M) := Subtype.ext hvw

  have h1 : b.equivFun v = c := by
    rw [← b.equivFun.apply_symm_apply c, Module.Basis.equivFun_symm_apply]
  intro j
  have hcj : c j = ϖ * b.equivFun (⟨_, hwM⟩ : M) j := by
    rw [← congrFun h1 j, hvw', map_smul, Pi.smul_apply, smul_eq_mul]
  have hc𝔪 : c j ∈ maximalIdeal A₀ := by
    rw [hcj, hmax]
    exact Ideal.mem_span_singleton'.mpr ⟨_, mul_comm _ _⟩
  rw [← hc j]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hc𝔪

end S12EL.Cartesian

namespace S12EL
namespace D3
open IsLocalRing

section Main
variable {K : Type*} [Field K] [CharZero K] (A : ValuationSubring K)
variable {ι E : Type*} [AddCommGroup E] [Module K E]

omit [CharZero K] in

theorem linearIndependent_of_map_injective {K₁ : Type*} [Field K₁] (φ : K₁ →+* K) {n : ℕ}
    (B : Fin n → ι → K₁) (h : LinearIndependent K (fun j => fun i => φ (B j i))) :
    LinearIndependent K₁ B := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro c hc j
  have := h (fun j => φ (c j)) (by
    ext i
    have hi := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
    rw [← map_zero φ, ← hi, map_sum]
    simp only [map_mul]) j
  exact (map_eq_zero φ).mp this

omit [CharZero K] in

theorem mem_of_isIntegral_int {x : K} (hx : IsIntegral ℤ x) : x ∈ A := by

  rw [← A.valuation_le_one_iff]
  obtain ⟨p, hp, hpx⟩ := hx
  by_contra hlt
  push Not at hlt

  have hv1 : 1 < A.valuation x := hlt
  have key : A.valuation (x ^ p.natDegree) = A.valuation (-(∑ i ∈ Finset.range p.natDegree, (p.coeff i : K) * x ^ i)) := by
    congr 1
    have := hpx
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ] at this
    simp only [eq_intCast] at this
    rw [hp.coeff_natDegree, Int.cast_one, one_mul] at this
    linear_combination this
  rw [Valuation.map_neg, Valuation.map_pow] at key
  have hlt2 : A.valuation (∑ i ∈ Finset.range p.natDegree, (p.coeff i : K) * x ^ i) < A.valuation x ^ p.natDegree := by
    apply Valuation.map_sum_lt
    · exact pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hv1))
    · intro i hi
      rw [Finset.mem_range] at hi
      rw [Valuation.map_mul, Valuation.map_pow]
      have hci : A.valuation (p.coeff i : K) ≤ 1 := by
        rw [A.valuation_le_one_iff]; exact intCast_mem A (p.coeff i)
      calc A.valuation (p.coeff i : K) * A.valuation x ^ i ≤ 1 * A.valuation x ^ i := by gcongr
        _ = A.valuation x ^ i := one_mul _
        _ < A.valuation x ^ p.natDegree := pow_lt_pow_right₀ hv1 hi
  rw [key] at hlt2
  exact lt_irrefl _ hlt2

set_option maxHeartbeats 6400000 in

theorem exists_linearIndependent_residue_of_integral
    (e : E →ₗ[K] (ι → K)) (he : Function.Injective e)
    {n : ℕ} (b : Fin n → E) (hb : LinearIndependent K b)
    (hint : ∀ j i, e (b j) i ∈ A)
    (K₁ : IntermediateField ℚ K) [FiniteDimensional ℚ K₁] (hK₁ : ∀ j i, e (b j) i ∈ K₁) :
    ∃ G : Fin n → E, (∀ l, G l ∈ Submodule.span K (Set.range b)) ∧
      ∃ hG : ∀ l i, e (G l) i ∈ A, (∀ l i, e (G l) i ∈ K₁) ∧
        LinearIndependent (ResidueField A) (fun l => fun i => residue A ⟨e (G l) i, hG l i⟩) := by
  classical
  haveI : NumberField K₁ := NumberField.mk

  set B : Fin n → ι → K₁ := fun j i => ⟨e (b j) i, hK₁ j i⟩ with hBdef
  have hBK : LinearIndependent K (fun j => fun i => ((B j i : K₁) : K)) := by
    have : (fun j => fun i => ((B j i : K₁) : K)) = fun j => e (b j) := by
      funext j i; rfl
    rw [this]
    exact (hb.map' e (LinearMap.ker_eq_bot.mpr he))
  have hB : LinearIndependent K₁ B := linearIndependent_of_map_injective (algebraMap K₁ K) B hBK

  by_cases hcase : ∀ x : K₁, (x : K) ∈ A
  ·
    let toA : K₁ →+* A := (algebraMap K₁ K).codRestrict A.toSubring hcase
    let σ : K₁ →+* ResidueField A := (residue A).comp toA
    refine ⟨b, fun l => Submodule.subset_span ⟨l, rfl⟩, hint, hK₁, ?_⟩
    have := linearIndependent_map_of_linearIndependent σ B hB
    convert this using 2 with l
    all_goals try rfl
  ·
    push Not at hcase
    obtain ⟨x₀, hx₀⟩ := hcase
    let O := NumberField.RingOfIntegers K₁
    let g : O →+* K := (algebraMap K₁ K).comp (algebraMap O K₁)
    have hg_apply : ∀ r : O, g r = ((r : K₁) : K) := fun r => rfl
    have hgA : ∀ r : O, g r ∈ A := fun r =>
      mem_of_isIntegral_int A ((NumberField.RingOfIntegers.isIntegral_coe r).algebraMap)
    let gA : O →+* A := g.codRestrict A hgA
    have hgA_val : ∀ r : O, ((gA r : A) : K) = g r := fun r => rfl
    let 𝔭 : Ideal O := (maximalIdeal A).comap gA
    haveI h𝔭prime : 𝔭.IsPrime := Ideal.comap_isPrime gA (maximalIdeal A)
    have hmem𝔭 : ∀ r : O, r ∈ 𝔭 ↔ (gA r) ∈ maximalIdeal A := fun r => Ideal.mem_comap

    have hunitA : ∀ r : O, r ∉ 𝔭 → IsUnit (gA r) := by
      intro r hr
      by_contra hnu
      exact hr ((hmem𝔭 r).mpr ((mem_maximalIdeal _).mpr hnu))

    have h𝔭ne : 𝔭 ≠ ⊥ := by
      intro hbot
      apply hx₀
      obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := O) x₀
      have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
      have hsn : s ∉ 𝔭 := by rw [hbot]; exact fun h => hs0 ((Submodule.mem_bot O).mp h)
      obtain ⟨u, hu⟩ := hunitA s hsn
      have hx : (x₀ : K) = g r * (g s)⁻¹ := by
        rw [← hrs, div_eq_mul_inv]
        push_cast
        rfl
      rw [hx]
      refine A.mul_mem _ _ (hgA r) ?_
      have hmul : (g s) * (((u⁻¹ : Aˣ) : A) : K) = 1 := by
        rw [← hgA_val, ← hu]
        have h1 : ((u : A) : K) * (((u⁻¹ : Aˣ) : A) : K) = (((u * u⁻¹ : Aˣ) : A) : K) := by
          push_cast; rfl
        rw [h1, mul_inv_cancel u]
        rfl
      rw [← eq_inv_of_mul_eq_one_right hmul]
      exact SetLike.coe_mem _

    let A₀ := Localization.AtPrime 𝔭
    haveI : IsDiscreteValuationRing A₀ :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O h𝔭ne A₀

    have hunitK : ∀ y : 𝔭.primeCompl, IsUnit (algebraMap O K₁ y) := by
      intro y
      apply IsUnit.mk0
      intro h0
      have : (y : O) = 0 := (map_eq_zero_iff _ (IsFractionRing.injective O K₁)).mp h0
      exact y.2 (this ▸ 𝔭.zero_mem)
    have hunitA' : ∀ y : 𝔭.primeCompl, IsUnit (gA y) := fun y => hunitA y y.2
    let ψK : A₀ →+* K₁ := IsLocalization.lift (M := 𝔭.primeCompl) hunitK
    let ψA : A₀ →+* A := IsLocalization.lift (M := 𝔭.primeCompl) hunitA'
    have hψK_alg : ∀ r : O, ψK (algebraMap O A₀ r) = algebraMap O K₁ r := fun r => IsLocalization.lift_eq hunitK r
    have hψA_alg : ∀ r : O, ψA (algebraMap O A₀ r) = gA r := fun r => IsLocalization.lift_eq hunitA' r
    have hcompat : ∀ a : A₀, ((ψK a : K₁) : K) = ((ψA a : A) : K) := by
      intro a
      have h1 : ((algebraMap K₁ K).comp ψK) = (A.subtype.comp ψA) := by
        apply IsLocalization.ringHom_ext 𝔭.primeCompl
        ext r
        simp only [RingHom.comp_apply, hψK_alg, hψA_alg]
        rfl
      exact congrArg (fun f : A₀ →+* K => f a) h1

    have hlocal : ∀ a : A₀, a ∈ maximalIdeal A₀ → ψA a ∈ maximalIdeal A := by
      intro a ha
      obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl a
      have hr : r ∈ 𝔭 := by
        by_contra hr
        have hu : IsUnit (IsLocalization.mk' A₀ r s) :=
          (IsLocalization.AtPrime.isUnit_mk'_iff A₀ 𝔭 r s).mpr hr
        exact (mem_maximalIdeal _).mp ha hu
      rw [IsLocalization.lift_mk']
      exact Ideal.mul_mem_right _ _ ((hmem𝔭 r).mp hr)
    haveI : IsLocalHom ψA := by
      refine ⟨fun a ha => ?_⟩
      by_contra hna
      have : ψA a ∈ maximalIdeal A := hlocal a ((mem_maximalIdeal _).mpr hna)
      exact (mem_maximalIdeal _).mp this ha
    let σ₀ : ResidueField A₀ →+* ResidueField A := ResidueField.map ψA

    letI : Algebra A₀ K₁ := ψK.toAlgebra
    haveI : IsScalarTower O A₀ K₁ := IsScalarTower.of_algebraMap_eq (fun r => (hψK_alg r).symm)
    haveI : IsFractionRing A₀ K₁ :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl A₀ K₁
    have hψK_inj : Function.Injective ψK := IsFractionRing.injective A₀ K₁

    have hlift : ∀ x : K₁, (x : K) ∈ A → ∃ a : A₀, ψK a = x := by
      intro x hxA
      by_cases hx0 : x = 0
      · exact ⟨0, by rw [map_zero, hx0]⟩
      rcases ValuationRing.isInteger_or_isInteger A₀ x with ⟨a, ha⟩ | ⟨a, ha⟩
      · exact ⟨a, ha⟩
      ·
        by_cases hau : IsUnit a
        · obtain ⟨u, rfl⟩ := hau
          refine ⟨(u⁻¹ : A₀ˣ), ?_⟩
          have : (algebraMap A₀ K₁) u * x = 1 := by
            rw [ha, inv_mul_cancel₀ hx0]
          calc ψK ↑u⁻¹ = (algebraMap A₀ K₁) ↑u⁻¹ * ((algebraMap A₀ K₁) u * x) := by rw [this, mul_one]; rfl
            _ = x := by rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
        · exfalso
          have hmax : ψA a ∈ maximalIdeal A := hlocal a ((mem_maximalIdeal _).mpr hau)
          have hinvK : ((x : K₁) : K)⁻¹ = ((ψA a : A) : K) := by
            rw [← hcompat]
            change ((x : K₁) : K)⁻¹ = ((algebraMap A₀ K₁ a : K₁) : K)
            rw [ha]
            exact (map_inv₀ (algebraMap K₁ K) x).symm
          have hxK0 : ((x : K₁) : K) ≠ 0 := by
            intro h0
            exact hx0 ((map_eq_zero_iff _ (algebraMap K₁ K).injective).mp h0)

          have hone : (⟨(x : K), hxA⟩ : A) * ψA a = 1 := by
            apply Subtype.ext
            change ((x : K₁) : K) * ((ψA a : A) : K) = 1
            rw [← hinvK, mul_inv_cancel₀ hxK0]
          have : (1 : A) ∈ maximalIdeal A := hone ▸ Ideal.mul_mem_left _ _ hmax
          exact (maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)

    have hBint0 : ∀ j i, ∃ a : A₀, ψK a = B j i := fun j i => hlift (B j i) (hint j i)
    choose Bint hBint using hBint0

    let Φ : (ι → A₀) →ₗ[A₀] (ι → K₁) := (Algebra.linearMap A₀ K₁).compLeft ι
    have hΦ : ∀ (v : ι → A₀) i, Φ v i = ψK (v i) := fun v i => rfl
    have hΦinj : Function.Injective Φ := by
      intro v w h; funext i
      exact hψK_inj (by rw [← hΦ, ← hΦ, h])
    let S : Submodule K₁ (ι → K₁) := Submodule.span K₁ (Set.range B)
    let M : Submodule A₀ (ι → A₀) := (S.restrictScalars A₀).comap Φ
    have hM : ∀ v, v ∈ M ↔ Φ v ∈ S := fun v => Iff.rfl
    have hΦBint : ∀ j, Φ (Bint j) = B j := fun j => funext fun i => by rw [hΦ, hBint]
    have hBintM : ∀ j, Bint j ∈ M := by
      intro j; rw [hM, hΦBint]; exact Submodule.subset_span ⟨j, rfl⟩

    have hsat : ∀ (a : A₀) (v : ι → A₀), a ≠ 0 → a • v ∈ M → v ∈ M := by
      intro a v ha hav
      rw [hM] at hav ⊢
      have hΦs : Φ (a • v) = (ψK a) • Φ v := by
        funext i
        rw [Pi.smul_apply, hΦ, hΦ, Pi.smul_apply, smul_eq_mul, map_mul, smul_eq_mul]
      rw [hΦs] at hav
      have ha' : ψK a ≠ 0 := (map_ne_zero_iff _ hψK_inj).mpr ha
      have := S.smul_mem (ψK a)⁻¹ hav
      rwa [inv_smul_smul₀ ha'] at this

    obtain ⟨s, hsinj, hsdet⟩ := S12EL.Cart.exists_submatrix_det_ne_zero_of_linearIndependent B hB
    have hfin : ∃ t : Finset ι, ∀ v ∈ M, (∀ i ∈ t, v i = 0) → v = 0 := by
      refine ⟨Finset.univ.image s, fun v hv hv0 => ?_⟩
      rw [hM] at hv
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K₁).mp hv
      have hcz : c = 0 := by
        have hmv : (Matrix.of fun l j => B j (s l)) *ᵥ c = 0 := by
          funext l
          have hl := congrFun hc (s l)
          rw [hΦ, hv0 (s l) (Finset.mem_image_of_mem _ (Finset.mem_univ _)), map_zero] at hl
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hl
          rw [Matrix.mulVec, Pi.zero_apply]
          simp only [dotProduct, Matrix.of_apply]
          rw [show (∑ x, B x (s l) * c x) = ∑ j, c j * B j (s l) from
            Finset.sum_congr rfl fun j _ => mul_comm (B j (s l)) (c j)]
          exact hl
        exact Matrix.eq_zero_of_mulVec_eq_zero hsdet hmv
      have hΦv : Φ v = 0 := by rw [← hc, hcz]; simp
      exact hΦinj (by rw [hΦv, map_zero])

    obtain ⟨n', m, hm⟩ := S12EL.Cartesian.exists_basis_residue_linearIndependent M hsat hfin
    haveI : Module.Finite A₀ M := Module.Finite.of_basis m
    haveI : Module.Finite K₁ S := Module.Finite.span_of_finite K₁ (Set.finite_range B)

    have hfinM : Module.finrank A₀ M = n' := by
      rw [Module.finrank_eq_card_basis m, Fintype.card_fin]
    have hfinS : Module.finrank K₁ S = n := by
      rw [finrank_span_eq_card hB, Fintype.card_fin]
    have hn_le : n ≤ n' := by
      have hli : LinearIndependent A₀ (fun j => (⟨Bint j, hBintM j⟩ : M)) := by
        rw [Fintype.linearIndependent_iff]
        intro a ha j
        have h0 : ∑ j, a j • Bint j = 0 := by
          simpa using congrArg Subtype.val ha
        have h1 : ∑ j, ψK (a j) • B j = 0 := by
          have := congrArg Φ h0
          rw [map_sum, map_zero] at this
          rw [← this]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul, hΦBint, ← algebraMap_smul K₁ (a j) (B j)]
          rfl
        have := (Fintype.linearIndependent_iff.mp hB) (fun j => ψK (a j)) h1 j
        exact hψK_inj (by rw [this, map_zero])
      have := hli.fintype_card_le_finrank
      rw [Fintype.card_fin, hfinM] at this
      exact this
    have hn'_le : n' ≤ n := by
      let w : Fin n' → S := fun l => ⟨Φ ((m l : M) : ι → A₀), (hM _).mp (m l).2⟩
      have hli' : LinearIndependent K₁ (fun l => Φ ((m l : M) : ι → A₀)) := by
        rw [Fintype.linearIndependent_iff]
        intro c hc' l

        obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A₀) c
        choose a ha using hd
        have hsum : ∑ l, a l • ((m l : M) : ι → A₀) = 0 := by
          apply hΦinj
          rw [map_zero]
          calc Φ (∑ l, a l • ((m l : M) : ι → A₀))
              = ∑ l, (algebraMap A₀ K₁ (a l)) • Φ ((m l : M) : ι → A₀) := by
                rw [map_sum]
                refine Finset.sum_congr rfl fun l _ => ?_
                rw [map_smul, algebraMap_smul]
            _ = ∑ l, ((d : A₀) • c l) • Φ ((m l : M) : ι → A₀) := by
                refine Finset.sum_congr rfl fun l _ => ?_
                rw [ha l]
            _ = (d : A₀) • ∑ l, c l • Φ ((m l : M) : ι → A₀) := by
                rw [Finset.smul_sum]
                refine Finset.sum_congr rfl fun l _ => ?_
                rw [smul_assoc]
            _ = 0 := by rw [hc', smul_zero]
        have hsum' : ∑ l, a l • m l = 0 := by
          apply M.injective_subtype
          rw [map_sum, map_zero]
          rw [← hsum]
          rfl
        have hal : a l = 0 := (Fintype.linearIndependent_iff.mp m.linearIndependent) a hsum' l
        have hdc : (d : A₀) • c l = 0 := by
          rw [← ha l, hal, map_zero]
        rw [Algebra.smul_def, mul_eq_zero] at hdc
        rcases hdc with hd0 | hcl
        · exact absurd ((map_eq_zero_iff _ hψK_inj).mp hd0) (nonZeroDivisors.ne_zero d.2)
        · exact hcl
      have hli : LinearIndependent K₁ w := LinearIndependent.of_comp S.subtype hli'
      have := hli.fintype_card_le_finrank
      rw [Fintype.card_fin, hfinS] at this
      exact this
    have hn' : n' = n := le_antisymm hn'_le hn_le

    let m' : Module.Basis (Fin n) A₀ M := m.reindex (finCongr hn')
    have hm'eq : ∀ l, m' l = m ((finCongr hn').symm l) := fun l => Module.Basis.reindex_apply _ _ _
    have hm' : LinearIndependent (ResidueField A₀)
        (fun l => fun i => residue A₀ (((m' l : M) : ι → A₀) i)) := by
      have heq : (fun l => fun i => residue A₀ (((m' l : M) : ι → A₀) i)) =
          (fun l => fun i => residue A₀ (((m l : M) : ι → A₀) i)) ∘ (finCongr hn').symm := by
        funext l; simp only [Function.comp_apply, hm'eq]
      rw [heq]
      exact hm.comp _ (finCongr hn').symm.injective

    have hcoord : ∀ l, ∃ c : Fin n → K₁, ∑ j, c j • B j = Φ ((m' l : M) : ι → A₀) := fun l =>
      (Submodule.mem_span_range_iff_exists_fun K₁).mp ((hM _).mp (m' l).2)
    choose c hc using hcoord
    set G : Fin n → E := fun l => ∑ j, ((c l j : K₁) : K) • b j with hGdef
    have heG : ∀ l i, e (G l) i = ((ψA (((m' l : M) : ι → A₀) i) : A) : K) := by
      intro l i
      rw [← hcompat, ← hΦ, ← hc l, hGdef]
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rfl
    have hG : ∀ l i, e (G l) i ∈ A := fun l i => by rw [heG]; exact SetLike.coe_mem _
    refine ⟨G, fun l => ?_, hG, fun l i => ?_, ?_⟩
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [heG, ← hcompat]
      exact SetLike.coe_mem _
    · have hred : ∀ l i, residue A ⟨e (G l) i, hG l i⟩ = σ₀ (residue A₀ (((m' l : M) : ι → A₀) i)) := by
        intro l i
        have h1 : (⟨e (G l) i, hG l i⟩ : A) = ψA (((m' l : M) : ι → A₀) i) := Subtype.ext (heG l i)
        rw [h1]
        rfl
      have := linearIndependent_map_of_linearIndependent σ₀ _ hm'
      convert this using 2 with l
      funext i
      exact hred l i

end Main
end S12EL.D3

open HahnSeries

namespace S12EL
namespace LScoeff

variable {K : Type*} [Field K] (S : Subring K)

def CoeffIn (x : LaurentSeries K) : Prop := ∀ n : ℤ, x.coeff n ∈ S

theorem coeffIn_zero : CoeffIn S (0 : LaurentSeries K) := fun n => by simp [S.zero_mem]
theorem coeffIn_one : CoeffIn S (1 : LaurentSeries K) := by
  intro n
  rw [HahnSeries.coeff_one]
  split_ifs <;> simp [S.one_mem, S.zero_mem]
theorem coeffIn_add {x y : LaurentSeries K} (hx : CoeffIn S x) (hy : CoeffIn S y) : CoeffIn S (x + y) :=
  fun n => by rw [HahnSeries.coeff_add]; exact S.add_mem (hx n) (hy n)
theorem coeffIn_neg {x : LaurentSeries K} (hx : CoeffIn S x) : CoeffIn S (-x) :=
  fun n => by rw [HahnSeries.coeff_neg]; exact S.neg_mem (hx n)
theorem coeffIn_mul {x y : LaurentSeries K} (hx : CoeffIn S x) (hy : CoeffIn S y) : CoeffIn S (x * y) := by
  intro n
  rw [HahnSeries.coeff_mul]
  exact S.sum_mem fun ij _ => S.mul_mem (hx _) (hy _)
theorem coeffIn_single (n : ℤ) {r : K} (hr : r ∈ S) : CoeffIn S (single n r) := by
  intro m
  rw [HahnSeries.coeff_single]
  split_ifs <;> simp [hr, S.zero_mem]
theorem coeffIn_ofPowerSeries {p : PowerSeries K} (hp : ∀ n, PowerSeries.coeff n p ∈ S) :
    CoeffIn S (ofPowerSeries ℤ K p) := by
  intro n
  rw [PowerSeries.coeff_coe]
  split_ifs
  · exact S.zero_mem
  · exact hp _

theorem coeffIn_inv {x : LaurentSeries K} (hx : CoeffIn S x)
    (hlead : ∃ s ∈ S, s * x.leadingCoeff = 1) : CoeffIn S x⁻¹ := by
  obtain ⟨s, hs, hsx⟩ := hlead
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hsx

  set p : PowerSeries K := x.powerSeriesPart with hp
  have hpc : ∀ n, PowerSeries.coeff n p ∈ S := fun n => by
    rw [hp, LaurentSeries.powerSeriesPart_coeff]; exact hx _
  let pS : PowerSeries S := PowerSeries.mk fun n => ⟨PowerSeries.coeff n p, hpc n⟩
  have hmap : PowerSeries.map S.subtype pS = p := by
    ext n; simp [pS]
  have hconst : IsUnit (PowerSeries.constantCoeff pS) := by
    have h0 : ((PowerSeries.constantCoeff pS : S) : K) = x.leadingCoeff := by
      show (PowerSeries.coeff 0 p) = x.leadingCoeff
      rw [hp, LaurentSeries.powerSeriesPart_coeff, HahnSeries.leadingCoeff_eq]
      simp
    refine IsUnit.of_mul_eq_one (⟨s, hs⟩ : S) ?_
    apply Subtype.ext
    show ((PowerSeries.constantCoeff pS : S) : K) * s = 1
    rw [h0, mul_comm, hsx]
  have hunit : IsUnit pS := (PowerSeries.isUnit_iff_constantCoeff).mpr hconst
  obtain ⟨u, hu⟩ := hunit

  set qK : PowerSeries K := PowerSeries.map S.subtype (↑u⁻¹ : PowerSeries S) with hqK
  have hqc : ∀ n, PowerSeries.coeff n qK ∈ S := fun n => by
    rw [hqK, PowerSeries.coeff_map]; exact Subtype.mem _
  have hpq : p * qK = 1 := by
    rw [← hmap, hqK, ← map_mul, ← hu, Units.mul_inv, map_one]

  set y : LaurentSeries K := ofPowerSeries ℤ K qK * single (-x.order) 1 with hy
  have hxy : x * y = 1 := by
    have hx' : single x.order (1 : K) * ofPowerSeries ℤ K p = x := by
      rw [hp, LaurentSeries.ofPowerSeries_powerSeriesPart, ← mul_assoc, HahnSeries.single_mul_single,
        add_neg_cancel, mul_one, HahnSeries.single_zero_one, one_mul]
    rw [← hx', hy, mul_assoc, ← mul_assoc (ofPowerSeries ℤ K p) (ofPowerSeries ℤ K qK), ← map_mul, hpq,
      (ofPowerSeries ℤ K).map_one, one_mul, HahnSeries.single_mul_single, add_neg_cancel, mul_one,
      HahnSeries.single_zero_one]
  have hinv : x⁻¹ = y := inv_eq_of_mul_eq_one_right hxy
  rw [hinv, hy]
  exact coeffIn_mul S (coeffIn_ofPowerSeries S hqc) (coeffIn_single S _ S.one_mem)

end S12EL.LScoeff

namespace S12EL
namespace Glue
open ModularCurve

theorem exists_finiteDimensional_coeff_mem {L : Type*} [Field L] [Algebra ℚ L]
    (halg : ∀ c : L, IsAlgebraic ℚ c)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) {x : LaurentSeries L}
    (hx : x ∈ laurentBaseChange L F₀) :
    ∃ K₁ : IntermediateField ℚ L, FiniteDimensional ℚ K₁ ∧ ∀ k : ℤ, x.coeff k ∈ K₁ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
    rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
    ·
      refine ⟨IntermediateField.adjoin ℚ {c}, ?_, fun k => ?_⟩
      · exact IntermediateField.adjoin.finiteDimensional (halg c).isIntegral
      · rw [algebraMap_laurentSeries_eq_single]
        rw [HahnSeries.coeff_single]
        split_ifs
        · exact IntermediateField.mem_adjoin_simple_self ℚ c
        · exact zero_mem _
    ·
      refine ⟨⊥, inferInstance, fun k => ?_⟩
      rw [coeffEmb_coeff]
      exact (⊥ : IntermediateField ℚ L).algebraMap_mem (z.coeff k)
  | one => exact ⟨⊥, inferInstance, fun k => by
      rw [HahnSeries.coeff_one]; split_ifs <;> simp [one_mem, zero_mem]⟩
  | add y z _ _ hy hz =>
    obtain ⟨K₁, hK₁, h₁⟩ := hy
    obtain ⟨K₂, hK₂, h₂⟩ := hz
    haveI := hK₁; haveI := hK₂
    exact ⟨K₁ ⊔ K₂, inferInstance, fun k => by
      rw [HahnSeries.coeff_add]
      exact add_mem ((le_sup_left : K₁ ≤ K₁ ⊔ K₂) (h₁ k)) ((le_sup_right : K₂ ≤ K₁ ⊔ K₂) (h₂ k))⟩
  | neg y _ hy =>
    obtain ⟨K₁, hK₁, h₁⟩ := hy
    exact ⟨K₁, hK₁, fun k => by rw [HahnSeries.coeff_neg]; exact neg_mem (h₁ k)⟩
  | inv y _ hy =>
    obtain ⟨K₁, hK₁, h₁⟩ := hy
    refine ⟨K₁, hK₁, ?_⟩
    by_cases hy0 : y = 0
    · intro k; rw [hy0, _root_.inv_zero, HahnSeries.coeff_zero]; exact zero_mem _
    · have hlc : y.leadingCoeff ∈ K₁ := by
        rw [HahnSeries.leadingCoeff_of_ne_zero hy0]
        exact h₁ _
      have hlc0 : y.leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr hy0
      exact S12EL.LScoeff.coeffIn_inv K₁.toSubring h₁ ⟨y.leadingCoeff⁻¹,
        by simpa using inv_mem hlc, inv_mul_cancel₀ hlc0⟩
  | mul y z _ _ hy hz =>
    obtain ⟨K₁, hK₁, h₁⟩ := hy
    obtain ⟨K₂, hK₂, h₂⟩ := hz
    haveI := hK₁; haveI := hK₂
    refine ⟨K₁ ⊔ K₂, inferInstance, ?_⟩
    have h₁' : ∀ k, y.coeff k ∈ (K₁ ⊔ K₂).toSubring := fun k => (le_sup_left : K₁ ≤ K₁ ⊔ K₂) (h₁ k)
    have h₂' : ∀ k, z.coeff k ∈ (K₁ ⊔ K₂).toSubring := fun k => (le_sup_right : K₂ ≤ K₁ ⊔ K₂) (h₂ k)
    exact S12EL.LScoeff.coeffIn_mul (K₁ ⊔ K₂).toSubring h₁' h₂'

end S12EL.Glue

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace S12EL
namespace Glue
open ModularCurve IsLocalRing

noncomputable def pairCoeff {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K)) (w : F ≃ₐ[K] F) :
    F →ₗ[K] (ℤ ⊕ ℤ → K) where
  toFun f := Sum.elim (fun k => (f : LaurentSeries K).coeff k) (fun k => ((w f : F) : LaurentSeries K).coeff k)
  map_add' f g := by
    funext i; rcases i with k | k
    · simp [HahnSeries.coeff_add]
    · simp [map_add, HahnSeries.coeff_add]
  map_smul' c f := by
    funext i; rcases i with k | k
    · simp only [Sum.elim_inl, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
      rw [IntermediateField.coe_smul, Algebra.smul_def, algebraMap_laurentSeries_eq_single,
        HahnSeries.coeff_single_zero_mul]
    · simp only [Sum.elim_inr, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_smul]
      rw [IntermediateField.coe_smul, Algebra.smul_def, algebraMap_laurentSeries_eq_single,
        HahnSeries.coeff_single_zero_mul]

theorem pairCoeff_inl {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K)) (w : F ≃ₐ[K] F)
    (f : F) (k : ℤ) : pairCoeff F w f (Sum.inl k) = (f : LaurentSeries K).coeff k := rfl

theorem pairCoeff_inr {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K)) (w : F ≃ₐ[K] F)
    (f : F) (k : ℤ) : pairCoeff F w f (Sum.inr k) = ((w f : F) : LaurentSeries K).coeff k := rfl

theorem pairCoeff_injective {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K))
    (w : F ≃ₐ[K] F) : Function.Injective (pairCoeff F w) := by
  intro f g h
  apply Subtype.ext
  ext k
  exact congrFun h (Sum.inl k)

theorem exists_coeffMap_eq {K : Type*} [Field K] (A : ValuationSubring K) (x : LaurentSeries K)
    (hx : ∀ k : ℤ, x.coeff k ∈ A) : ∃ y : LaurentSeries A, coeffMap A.subtype y = x := by
  refine ⟨⟨fun k => ⟨x.coeff k, hx k⟩, ?_⟩, ?_⟩
  · have : (Function.support fun k => (⟨x.coeff k, hx k⟩ : A)) = Function.support x.coeff := by
      ext k
      simp only [Function.mem_support, ne_eq]
      rw [not_iff_not]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [this]
    exact x.isPWO_support
  · ext k
    rfl

theorem coeffMap_coeff' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : LaurentSeries R) (k : ℤ) :
    (coeffMap f x).coeff k = f (x.coeff k) := rfl

end S12EL.Glue

namespace S12EL
namespace Glue
open ModularCurve IsLocalRing AlgebraicCurve

def fixS {L : Type*} [Field L] [Algebra ℚ L] (S : Set (L ≃ₐ[ℚ] L)) : IntermediateField ℚ L where
  carrier := {x | ∀ σ ∈ S, σ x = x}
  mul_mem' := fun {a b} ha hb σ hσ => by rw [map_mul, ha σ hσ, hb σ hσ]
  one_mem' := fun σ _ => map_one σ
  add_mem' := fun {a b} ha hb σ hσ => by rw [map_add, ha σ hσ, hb σ hσ]
  zero_mem' := fun σ _ => map_zero σ
  algebraMap_mem' := fun r σ _ => σ.commutes r
  inv_mem' := fun a ha σ hσ => by rw [map_inv₀, ha σ hσ]

theorem mem_fixS_iff {L : Type*} [Field L] [Algebra ℚ L] (S : Set (L ≃ₐ[ℚ] L)) (x : L) :
    x ∈ fixS S ↔ ∀ σ ∈ S, σ x = x := Iff.rfl

theorem exists_int_mul_inv_mem (A : ValuationSubring (AlgebraicClosure ℚ)) {c : AlgebraicClosure ℚ} (hc : c ≠ 0) :
    ∃ N : ℤ, N ≠ 0 ∧ (N : AlgebraicClosure ℚ) * c⁻¹ ∈ A := by
  haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have h1 : IsAlgebraic ℚ c⁻¹ := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic c⁻¹
  have h2 : IsAlgebraic ℤ c⁻¹ := IsAlgebraic.restrictScalars ℤ h1
  obtain ⟨N, hN0, hint⟩ := h2.exists_integral_multiple
  refine ⟨N, hN0, ?_⟩
  have := S12EL.D3.mem_of_isIntegral_int A hint
  first
    | (rw [Algebra.smul_def, eq_intCast] at this; exact this)
    | (rw [zsmul_eq_mul] at this; exact this)

end S12EL.Glue

namespace S12EL
namespace Glue
open ModularCurve IsLocalRing AlgebraicCurve

set_option maxHeartbeats 6400000 in

theorem solutionCore
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (Fb : IntermediateField (ResidueField A) (LaurentSeries (ResidueField A)))
    (w : laurentBaseChange (AlgebraicClosure ℚ) F₀ ≃ₐ[AlgebraicClosure ℚ] laurentBaseChange (AlgebraicClosure ℚ) F₀)
    (R₁ R₂ : RegularProlongation A (laurentBaseChange (AlgebraicClosure ℚ) F₀) Fb)
    (h₁ : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ laurentBaseChange (AlgebraicClosure ℚ) F₀),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : laurentBaseChange (AlgebraicClosure ℚ) F₀) ∈ R₁.integers,
        ((R₁.residue ⟨_, h⟩ : Fb) : LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y)
    (h₂ : ∀ f : laurentBaseChange (AlgebraicClosure ℚ) F₀, f ∈ R₂.integers ↔ w f ∈ R₁.integers)
    (h₂' : ∀ (f : laurentBaseChange (AlgebraicClosure ℚ) F₀) (h : f ∈ R₂.integers),
      R₂.residue ⟨f, h⟩ = R₁.residue ⟨w f, (h₂ f).mp h⟩)
    (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (V : Submodule (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    [FiniteDimensional (AlgebraicClosure ℚ) V]
    (hint : ∃ b : Fin (Module.finrank (AlgebraicClosure ℚ) V) → laurentBaseChange (AlgebraicClosure ℚ) F₀,
      (∀ i, b i ∈ V) ∧ LinearIndependent (AlgebraicClosure ℚ) b ∧
      (∀ i, (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((b i : laurentBaseChange (AlgebraicClosure ℚ) F₀) :
                LaurentSeries (AlgebraicClosure ℚ))) ∧
           (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((w (b i) :
                laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)))) ∧
      ∀ i, ∀ σ ∈ S, arithmeticGalois F₀ σ • b i = b i ∧ arithmeticGalois F₀ σ • w (b i) = w (b i)) :
    ∃ (G : Fin (Module.finrank (AlgebraicClosure ℚ) V) → laurentBaseChange (AlgebraicClosure ℚ) F₀)
      (hG₁ : ∀ i, G i ∈ R₁.integers) (hG₂ : ∀ i, G i ∈ R₂.integers),
      (∀ i, G i ∈ V) ∧
      LinearIndependent (ResidueField A)
        (fun i => (R₁.residue ⟨G i, hG₁ i⟩, R₂.residue ⟨G i, hG₂ i⟩)) ∧
      ∀ i, ∀ σ ∈ S, arithmeticGalois F₀ σ • G i = G i := by
  classical
  have halg : ∀ c : AlgebraicClosure ℚ, IsAlgebraic ℚ c := by
    intro c
    convert (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic c
    all_goals first | rfl | exact Subsingleton.elim _ _
  obtain ⟨b, hbV, hbli, hbint, hbfix⟩ := hint

  have hresc : ∀ i, ∃ s : ℤ, s ≠ 0 ∧ (∀ k, (((s : ℤ) : AlgebraicClosure ℚ) • ((b i : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ))).coeff k ∈ A) ∧
      (∀ k, (((s : ℤ) : AlgebraicClosure ℚ) • ((w (b i) : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ))).coeff k ∈ A) := by
    intro i
    obtain ⟨⟨c, y, hc, hy⟩, ⟨c', y', hc', hy'⟩⟩ := hbint i
    have hint1 : ∀ k, c * ((b i : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A := fun k => by
      have := congrArg (fun z => HahnSeries.coeff z k) hy
      simp only [coeffMap_coeff, HahnSeries.coeff_smul, smul_eq_mul] at this
      rw [← this]; exact SetLike.coe_mem _
    have hint2 : ∀ k, c' * ((w (b i) : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A := fun k => by
      have := congrArg (fun z => HahnSeries.coeff z k) hy'
      simp only [coeffMap_coeff, HahnSeries.coeff_smul, smul_eq_mul] at this
      rw [← this]; exact SetLike.coe_mem _
    obtain ⟨N, hN, hNA⟩ := exists_int_mul_inv_mem A hc
    obtain ⟨N', hN', hN'A⟩ := exists_int_mul_inv_mem A hc'
    refine ⟨N * N', mul_ne_zero hN hN', fun k => ?_, fun k => ?_⟩
    · rw [HahnSeries.coeff_smul, smul_eq_mul]
      have e1 : ((N * N' : ℤ) : AlgebraicClosure ℚ) * ((b i : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)).coeff k
          = (N' : AlgebraicClosure ℚ) * (((N : AlgebraicClosure ℚ) * c⁻¹) *
              (c * ((b i : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)).coeff k)) := by
        push_cast
        field_simp
      rw [e1]
      exact A.mul_mem _ _ (intCast_mem A N') (A.mul_mem _ _ hNA (hint1 k))
    · rw [HahnSeries.coeff_smul, smul_eq_mul]
      have e1 : ((N * N' : ℤ) : AlgebraicClosure ℚ) * ((w (b i) : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)).coeff k
          = (N : AlgebraicClosure ℚ) * (((N' : AlgebraicClosure ℚ) * c'⁻¹) *
              (c' * ((w (b i) : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)).coeff k)) := by
        push_cast
        field_simp
      rw [e1]
      exact A.mul_mem _ _ (intCast_mem A N) (A.mul_mem _ _ hN'A (hint2 k))
  choose s hs0 hs1 hs2 using hresc
  have hs0' : ∀ i, ((s i : ℤ) : AlgebraicClosure ℚ) ≠ 0 := fun i => Int.cast_ne_zero.mpr (hs0 i)
  set b' : Fin (Module.finrank (AlgebraicClosure ℚ) V) → laurentBaseChange (AlgebraicClosure ℚ) F₀ := fun i => ((s i : ℤ) : AlgebraicClosure ℚ) • b i with hb'def
  have hb'V : ∀ i, b' i ∈ V := fun i => V.smul_mem _ (hbV i)
  have hb'li : LinearIndependent (AlgebraicClosure ℚ) b' := by

    have : b' = fun i => (Units.mk0 ((s i : ℤ) : AlgebraicClosure ℚ) (hs0' i) : (AlgebraicClosure ℚ)ˣ) • b i := by
      funext i; rfl
    rw [this]
    exact hbli.units_smul _

  let e : laurentBaseChange (AlgebraicClosure ℚ) F₀ →ₗ[AlgebraicClosure ℚ] (ℤ ⊕ ℤ → AlgebraicClosure ℚ) := pairCoeff (laurentBaseChange (AlgebraicClosure ℚ) F₀) w
  have he : Function.Injective e := pairCoeff_injective (laurentBaseChange (AlgebraicClosure ℚ) F₀) w
  have hcoef_b' : ∀ j k, ((b' j : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)).coeff k
      = ((s j : ℤ) : AlgebraicClosure ℚ) * ((b j : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)).coeff k := by
    intro j k
    rw [hb'def]
    simp only
    rw [IntermediateField.coe_smul, Algebra.smul_def, algebraMap_laurentSeries_eq_single,
      HahnSeries.coeff_single_zero_mul]
  have hcoef_wb' : ∀ j k, ((w (b' j) : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)).coeff k
      = ((s j : ℤ) : AlgebraicClosure ℚ) * ((w (b j) : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)).coeff k := by
    intro j k
    rw [hb'def]
    simp only
    rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, IntermediateField.coe_mul]
    have hw : ((algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀) ((s j : ℤ) : AlgebraicClosure ℚ) :
        laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)) =
        HahnSeries.single 0 ((s j : ℤ) : AlgebraicClosure ℚ) := by
      rw [← algebraMap_laurentSeries_eq_single]; rfl
    rw [hw, HahnSeries.coeff_single_zero_mul]
  have hint' : ∀ j i, e (b' j) i ∈ A := by
    intro j i
    rcases i with k | k
    · rw [pairCoeff_inl, hcoef_b']
      have := hs1 j k
      rwa [HahnSeries.coeff_smul, smul_eq_mul] at this
    · rw [pairCoeff_inr, hcoef_wb']
      have := hs2 j k
      rwa [HahnSeries.coeff_smul, smul_eq_mul] at this

  have hfix' : ∀ j i, e (b' j) i ∈ fixS S := by
    intro j i σ hσ
    obtain ⟨hb1, hb2⟩ := hbfix j σ hσ
    have hc1 : ∀ k, σ (((b j : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)).coeff k)
        = ((b j : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)).coeff k := fun k => by
      have := congrArg (fun z : laurentBaseChange (AlgebraicClosure ℚ) F₀ => (z : LaurentSeries (AlgebraicClosure ℚ)).coeff k) hb1
      simp only [coe_arithmeticGalois_smul, coeffMap_coeff] at this
      exact this
    have hc2 : ∀ k, σ (((w (b j) : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)).coeff k)
        = ((w (b j) : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)).coeff k := fun k => by
      have := congrArg (fun z : laurentBaseChange (AlgebraicClosure ℚ) F₀ => (z : LaurentSeries (AlgebraicClosure ℚ)).coeff k) hb2
      simp only [coe_arithmeticGalois_smul, coeffMap_coeff] at this
      exact this
    rcases i with k | k
    · rw [pairCoeff_inl, hcoef_b', map_mul, map_intCast, hc1]
    · rw [pairCoeff_inr, hcoef_wb', map_mul, map_intCast, hc2]

  have hK₁ : ∃ K₁ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K₁ ∧ K₁ ≤ fixS S ∧
      ∀ j i, e (b' j) i ∈ K₁ := by
    have hcoef : ∀ j, ∃ K₁ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K₁ ∧ ∀ i, e (b' j) i ∈ K₁ := by
      intro j
      obtain ⟨L₁, hL₁, hc₁⟩ := exists_finiteDimensional_coeff_mem halg F₀ (b' j).2
      obtain ⟨L₂, hL₂, hc₂⟩ := exists_finiteDimensional_coeff_mem halg F₀ (w (b' j)).2
      haveI := hL₁; haveI := hL₂
      refine ⟨L₁ ⊔ L₂, inferInstance, fun i => ?_⟩
      rcases i with k | k
      · exact (le_sup_left : L₁ ≤ L₁ ⊔ L₂) (hc₁ k)
      · exact (le_sup_right : L₂ ≤ L₁ ⊔ L₂) (hc₂ k)
    choose L hLfd hL using hcoef
    haveI : ∀ j, FiniteDimensional ℚ (L j) := hLfd
    haveI hsupfd : FiniteDimensional ℚ (⨆ j, L j : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
      IntermediateField.finiteDimensional_iSup_of_finite
    refine ⟨(⨆ j, L j) ⊓ fixS S, ?_, inf_le_right, fun j i => ?_⟩
    · have hle : (⨆ j, L j) ⊓ fixS S ≤ ⨆ j, L j := inf_le_left
      exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
        (IntermediateField.inclusion_injective hle)
    · exact ⟨(le_iSup L j) (hL j i), hfix' j i⟩
  obtain ⟨K₁, hK₁fd, hK₁fix, hK₁mem⟩ := hK₁
  haveI := hK₁fd

  obtain ⟨G, hGspan, hGint, hGK₁, hGli⟩ :=
    S12EL.D3.exists_linearIndependent_residue_of_integral A e he b' hb'li hint' K₁ hK₁mem

  have hGfix : ∀ i, ∀ σ ∈ S, arithmeticGalois F₀ σ • G i = G i := by
    intro i σ hσ
    apply Subtype.ext
    rw [coe_arithmeticGalois_smul]
    ext k
    rw [coeffMap_coeff]
    have hk : ((G i : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)).coeff k = e (G i) (Sum.inl k) :=
      (pairCoeff_inl (laurentBaseChange (AlgebraicClosure ℚ) F₀) w (G i) k).symm
    rw [hk]
    exact hK₁fix (hGK₁ i (Sum.inl k)) σ hσ

  have hGV : ∀ i, G i ∈ V := fun i =>
    (Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hb'V j)) (hGspan i)
  have hy : ∀ i, ∃ y : LaurentSeries A, coeffMap A.subtype y = ((G i : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun i => exists_coeffMap_eq A _ (fun k => hGint i (Sum.inl k))
  have hy' : ∀ i, ∃ y : LaurentSeries A, coeffMap A.subtype y = ((w (G i) : laurentBaseChange (AlgebraicClosure ℚ) F₀) : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun i => exists_coeffMap_eq A _ (fun k => hGint i (Sum.inr k))
  choose y hy using hy
  choose y' hy' using hy'
  have hyF : ∀ i, coeffMap A.subtype (y i) ∈ laurentBaseChange (AlgebraicClosure ℚ) F₀ := fun i => by
    rw [hy i]; exact (G i).2
  have hy'F : ∀ i, coeffMap A.subtype (y' i) ∈ laurentBaseChange (AlgebraicClosure ℚ) F₀ := fun i => by
    rw [hy' i]; exact (w (G i)).2
  have hGeq : ∀ i, (⟨coeffMap A.subtype (y i), hyF i⟩ : laurentBaseChange (AlgebraicClosure ℚ) F₀) = G i :=
    fun i => Subtype.ext (hy i)
  have hwGeq : ∀ i, (⟨coeffMap A.subtype (y' i), hy'F i⟩ : laurentBaseChange (AlgebraicClosure ℚ) F₀) = w (G i) :=
    fun i => Subtype.ext (hy' i)
  have hR₁ : ∀ i, ∃ h : G i ∈ R₁.integers, ((R₁.residue ⟨G i, h⟩ : Fb) : LaurentSeries (ResidueField A)) = coeffMap (residue A) (y i) := by
    intro i
    obtain ⟨h, hres⟩ := h₁ (y i) (hyF i)
    have h' : G i ∈ R₁.integers := hGeq i ▸ h
    refine ⟨h', ?_⟩
    have : (⟨G i, h'⟩ : R₁.integers) = ⟨_, h⟩ := Subtype.ext (hGeq i).symm
    rw [this]; exact hres
  have hwR₁ : ∀ i, ∃ h : w (G i) ∈ R₁.integers, ((R₁.residue ⟨w (G i), h⟩ : Fb) : LaurentSeries (ResidueField A)) = coeffMap (residue A) (y' i) := by
    intro i
    obtain ⟨h, hres⟩ := h₁ (y' i) (hy'F i)
    have h' : w (G i) ∈ R₁.integers := hwGeq i ▸ h
    refine ⟨h', ?_⟩
    have : (⟨w (G i), h'⟩ : R₁.integers) = ⟨_, h⟩ := Subtype.ext (hwGeq i).symm
    rw [this]; exact hres
  choose hG₁ hres₁ using hR₁
  choose hwG₁ hres₂' using hwR₁
  have hG₂ : ∀ i, G i ∈ R₂.integers := fun i => (h₂ _).mpr (hwG₁ i)
  have hres₂ : ∀ i, ((R₂.residue ⟨G i, hG₂ i⟩ : Fb) : LaurentSeries (ResidueField A)) = coeffMap (residue A) (y' i) := by
    intro i; rw [h₂' (G i) (hG₂ i)]; exact hres₂' i
  refine ⟨G, hG₁, hG₂, hGV, ?_, hGfix⟩

  let T : (Fb × Fb) →ₗ[ResidueField A] (ℤ ⊕ ℤ → ResidueField A) :=
    { toFun := fun p => Sum.elim (fun k => ((p.1 : Fb) : LaurentSeries (ResidueField A)).coeff k)
        (fun k => ((p.2 : Fb) : LaurentSeries (ResidueField A)).coeff k)
      map_add' := fun p p' => by
        funext i; rcases i with k | k
        · simp only [Sum.elim_inl, Prod.fst_add, IntermediateField.coe_add, HahnSeries.coeff_add, Pi.add_apply]
        · simp only [Sum.elim_inr, Prod.snd_add, IntermediateField.coe_add, HahnSeries.coeff_add, Pi.add_apply]
      map_smul' := fun c p => by
        funext i; rcases i with k | k
        · simp only [Sum.elim_inl, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
          rw [IntermediateField.coe_smul, Algebra.smul_def, algebraMap_laurentSeries_eq_single,
            HahnSeries.coeff_single_zero_mul]
        · simp only [Sum.elim_inr, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
          rw [IntermediateField.coe_smul, Algebra.smul_def, algebraMap_laurentSeries_eq_single,
            HahnSeries.coeff_single_zero_mul] }
  apply LinearIndependent.of_comp T
  convert hGli using 2 with l
  funext i
  rcases i with k | k
  · change (((R₁.residue ⟨G l, hG₁ l⟩ : Fb) : LaurentSeries (ResidueField A))).coeff k = residue A ⟨e (G l) (Sum.inl k), hGint l (Sum.inl k)⟩
    rw [hres₁ l, coeffMap_coeff]
    congr 1
    apply Subtype.ext
    change ((y l).coeff k : AlgebraicClosure ℚ) = ((G l : laurentBaseChange (AlgebraicClosure ℚ) F₀) :
      LaurentSeries (AlgebraicClosure ℚ)).coeff k
    rw [← hy l, coeffMap_coeff]
    rfl
  · change (((R₂.residue ⟨G l, hG₂ l⟩ : Fb) : LaurentSeries (ResidueField A))).coeff k = residue A ⟨e (G l) (Sum.inr k), hGint l (Sum.inr k)⟩
    rw [hres₂ l, coeffMap_coeff]
    congr 1
    apply Subtype.ext
    change ((y' l).coeff k : AlgebraicClosure ℚ) = ((w (G l) : laurentBaseChange (AlgebraicClosure ℚ) F₀) :
      LaurentSeries (AlgebraicClosure ℚ)).coeff k
    rw [← hy' l, coeffMap_coeff]
    rfl

end S12EL.Glue

open AlgebraicCurve IsLocalRing ModularCurve in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (R₁ R₂ : RegularProlongation A (modularFunctionFieldBar (1 * q))
      (modularFunctionFieldFullC (ResidueField A) 1))
    (h₁ : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (1 * q)),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (1 * q)) ∈ R₁.integers,
        ((R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
            LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y)
    (h₂ : ∀ f : modularFunctionFieldBar (1 * q),
      f ∈ R₂.integers ↔ frickeInvolutionBar (1 * q) f ∈ R₁.integers)
    (h₂' : ∀ (f : modularFunctionFieldBar (1 * q)) (h : f ∈ R₂.integers),
      R₂.residue ⟨f, h⟩ = R₁.residue ⟨frickeInvolutionBar (1 * q) f, (h₂ f).mp h⟩)
    (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (V : Submodule (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    [FiniteDimensional (AlgebraicClosure ℚ) V]
    (hint : ∃ b : Fin (Module.finrank (AlgebraicClosure ℚ) V) → modularFunctionFieldBar (1 * q),
      (∀ i, b i ∈ V) ∧ LinearIndependent (AlgebraicClosure ℚ) b ∧
      (∀ i, (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((b i : modularFunctionFieldBar (1 * q)) :
                LaurentSeries (AlgebraicClosure ℚ))) ∧
           (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((frickeInvolutionBar (1 * q) (b i) :
                modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)))) ∧
      ∀ i, ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • b i = b i) :
    ∃ (G : Fin (Module.finrank (AlgebraicClosure ℚ) V) → modularFunctionFieldBar (1 * q))
      (hG₁ : ∀ i, G i ∈ R₁.integers) (hG₂ : ∀ i, G i ∈ R₂.integers),
      (∀ i, G i ∈ V) ∧
      LinearIndependent (ResidueField A)
        (fun i => (R₁.residue ⟨G i, hG₁ i⟩, R₂.residue ⟨G i, hG₂ i⟩)) ∧
      ∀ i, ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • G i = G i := by
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact (Fact.out : q.Prime).ne_zero⟩
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  obtain ⟨b, hbV, hbli, hbint, hbfix⟩ := hint
  refine S12EL.Glue.solutionCore A (modularFunctionFieldFull (1 * q))
    (modularFunctionFieldFullC (ResidueField A) 1) (frickeInvolutionBar (1 * q)) R₁ R₂ h₁ h₂ h₂' S V
    ⟨b, hbV, hbli, hbint, fun i σ hσ => ⟨hbfix i σ hσ, ?_⟩⟩
  rw [frickeInvolutionBar_def, arithmeticGalois_smul_geomAut, hbfix i σ hσ]

end S_ModularCurve_exists_linearIndependent_residuePair_forall_arithmeticGalois_smul_eq_of_finiteDimensional
end P2MW
export P2MW.S_ModularCurve_exists_linearIndependent_residuePair_forall_arithmeticGalois_smul_eq_of_finiteDimensional (solution)
