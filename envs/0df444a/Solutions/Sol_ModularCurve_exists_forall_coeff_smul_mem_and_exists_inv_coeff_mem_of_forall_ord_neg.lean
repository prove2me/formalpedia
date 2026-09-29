-- Prove2me | solution 1 for ModularCurve.exists_forall_coeff_smul_mem_and_exists_inv_coeff_mem_of_forall_ord_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/61849d07-58bd-50ad-a98a-34b4b660c45a

import Mathlib
import Definitions.Def_ModularCurve_PlaceSpecialization
import Theorems.Thm_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_and_exists_inv_coeff_mem_of_forall_ord_neg
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

set_option autoImplicit false
open Matrix

namespace FltWs24
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
    convert h2 using 1 <;> first | rfl | (funext l; rfl) | skip
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

end FltWs24.Cart

set_option autoImplicit false

namespace FltWs24
namespace D3

theorem linearIndependent_map_of_linearIndependent {k' k : Type*} [Field k'] [Field k] (σ : k' →+* k)
    {ι : Type*} {n : ℕ} (f : Fin n → ι → k') (hf : LinearIndependent k' f) :
    LinearIndependent k (fun j => fun i => σ (f j i)) := by
  classical
  obtain ⟨s, hs, hdet⟩ := FltWs24.Cart.exists_submatrix_det_ne_zero_of_linearIndependent f hf

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

end FltWs24.D3

open IsLocalRing

namespace FltWs24
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

end FltWs24.Cartesian

namespace FltWs24
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
      ∃ hG : ∀ l i, e (G l) i ∈ A,
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
    refine ⟨b, fun l => Submodule.subset_span ⟨l, rfl⟩, hint, ?_⟩
    have := linearIndependent_map_of_linearIndependent σ B hB
    convert this using 2 with l <;> first | rfl | (funext i; rfl) | skip
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

    obtain ⟨s, hsinj, hsdet⟩ := FltWs24.Cart.exists_submatrix_det_ne_zero_of_linearIndependent B hB
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

    obtain ⟨n', m, hm⟩ := FltWs24.Cartesian.exists_basis_residue_linearIndependent M hsat hfin
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
    refine ⟨G, fun l => ?_, hG, ?_⟩
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
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
end FltWs24.D3

open HahnSeries

namespace FltWs24
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

end FltWs24.LScoeff

namespace FltWs24
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
      exact FltWs24.LScoeff.coeffIn_inv K₁.toSubring h₁ ⟨y.leadingCoeff⁻¹,
        by simpa using inv_mem hlc, inv_mul_cancel₀ hlc0⟩
  | mul y z _ _ hy hz =>
    obtain ⟨K₁, hK₁, h₁⟩ := hy
    obtain ⟨K₂, hK₂, h₂⟩ := hz
    haveI := hK₁; haveI := hK₂
    refine ⟨K₁ ⊔ K₂, inferInstance, ?_⟩
    have h₁' : ∀ k, y.coeff k ∈ (K₁ ⊔ K₂).toSubring := fun k => (le_sup_left : K₁ ≤ K₁ ⊔ K₂) (h₁ k)
    have h₂' : ∀ k, z.coeff k ∈ (K₁ ⊔ K₂).toSubring := fun k => (le_sup_right : K₂ ≤ K₁ ⊔ K₂) (h₂ k)
    exact FltWs24.LScoeff.coeffIn_mul (K₁ ⊔ K₂).toSubring h₁' h₂'

end FltWs24.Glue

namespace FltWs24
namespace Prim
open IsLocalRing FltWs24.D3

set_option maxHeartbeats 6400000 in

theorem exists_primitive_smul {K : Type*} [Field K] [CharZero K] (A : ValuationSubring K)
    (x : LaurentSeries K) (hx : x ≠ 0)
    (hint : ∀ k : ℤ, x.coeff k ∈ A)
    (K₁ : IntermediateField ℚ K) [FiniteDimensional ℚ K₁] (hK₁ : ∀ k : ℤ, x.coeff k ∈ K₁) :
    ∃ d : K, d ≠ 0 ∧ (∀ k : ℤ, (d • x).coeff k ∈ A) ∧ ∃ n : ℤ, (d • x).coeff n ≠ 0 ∧ ((d • x).coeff n)⁻¹ ∈ A := by
  classical
  haveI : NumberField K₁ := NumberField.mk

  obtain ⟨n₀, hn₀⟩ : ∃ n, x.coeff n ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (HahnSeries.ext (funext h))
  by_cases hcase : ∀ y : K₁, (y : K) ∈ A
  ·
    refine ⟨1, one_ne_zero, fun k => by rw [one_smul]; exact hint k, n₀, by rwa [one_smul], ?_⟩
    rw [one_smul]
    have : (x.coeff n₀)⁻¹ = (((⟨x.coeff n₀, hK₁ n₀⟩ : K₁)⁻¹ : K₁) : K) := by push_cast; rfl
    rw [this]
    exact hcase _
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

    have hcoefK₁ : ∀ k, ((⟨x.coeff k, hK₁ k⟩ : K₁) : K) ∈ A := fun k => hint k
    choose c hc using fun k => hlift ⟨x.coeff k, hK₁ k⟩ (hcoefK₁ k)
    have hcK : ∀ k, ((ψK (c k) : K₁) : K) = x.coeff k := fun k => by rw [hc]
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A₀

    have hc0 : c n₀ ≠ 0 := by
      intro h
      apply hn₀
      rw [← hcK n₀, h, map_zero]
      rfl
    have hex : ∃ m : ℕ, ∃ k : ℤ, ¬ ϖ ^ (m + 1) ∣ c k := by
      obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
      refine ⟨m, n₀, fun hdvd => ?_⟩
      rw [hu, pow_succ] at hdvd

      have : ϖ ∣ (u : A₀) := by
        have h1 : ϖ ^ m * ϖ ∣ ϖ ^ m * (u : A₀) := by rwa [mul_comm (u : A₀)] at hdvd
        exact (mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)).mp h1
      exact hϖ.not_isUnit (isUnit_of_dvd_unit this u.isUnit)
    let m := Nat.find hex
    obtain ⟨k₀, hk₀⟩ : ∃ k, ¬ ϖ ^ (m + 1) ∣ c k := Nat.find_spec hex
    have hall : ∀ k, ϖ ^ m ∣ c k := by
      intro k
      by_cases hm : m = 0
      · rw [hm, pow_zero]; exact one_dvd _
      · obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm
        have hlt : m' < m := by omega
        have := Nat.find_min hex hlt
        push Not at this
        rw [hm']
        exact this k
    choose b hb using hall

    have hmaxϖ : maximalIdeal A₀ = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖ
    have hbu : IsUnit (b k₀) := by
      by_contra hnu
      apply hk₀
      have hmem : b k₀ ∈ maximalIdeal A₀ := (mem_maximalIdeal _).mpr hnu
      rw [hmaxϖ, Ideal.mem_span_singleton] at hmem
      obtain ⟨b', hb'⟩ := hmem
      refine ⟨b', ?_⟩
      rw [hb k₀, hb', pow_succ, mul_assoc]

    have hϖm0 : ψK (ϖ ^ m) ≠ 0 := (map_ne_zero_iff _ hψK_inj).mpr (pow_ne_zero _ hϖ.ne_zero)
    refine ⟨(((ψK (ϖ ^ m)) : K₁) : K)⁻¹, ?_, ?_, k₀, ?_, ?_⟩
    · exact inv_ne_zero (by exact_mod_cast hϖm0)
    · intro k
      rw [HahnSeries.coeff_smul, smul_eq_mul, ← hcK k, hb k, map_mul]
      push_cast
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hϖm0), one_mul, hcompat]
      exact SetLike.coe_mem _
    · obtain ⟨u, hu⟩ := hbu
      rw [HahnSeries.coeff_smul, smul_eq_mul, ← hcK k₀, hb k₀, map_mul]
      push_cast
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hϖm0), one_mul, ← hu]
      have hu0 : ψK (u : A₀) ≠ 0 := (map_ne_zero_iff _ hψK_inj).mpr u.ne_zero
      exact_mod_cast hu0
    · obtain ⟨u, hu⟩ := hbu
      rw [HahnSeries.coeff_smul, smul_eq_mul, ← hcK k₀, hb k₀, map_mul]
      push_cast
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hϖm0), one_mul, ← hu]
      have : (((ψK (u : A₀)) : K₁) : K)⁻¹ = ((ψK ((u⁻¹ : A₀ˣ) : A₀) : K₁) : K) := by
        symm
        apply eq_inv_of_mul_eq_one_right
        have h1 : ((ψK (u : A₀) : K₁) : K) * ((ψK ((u⁻¹ : A₀ˣ) : A₀) : K₁) : K) =
            ((ψK ((u : A₀) * ((u⁻¹ : A₀ˣ) : A₀)) : K₁) : K) := by
          rw [map_mul]; push_cast; rfl
        rw [h1, Units.mul_inv, map_one]
        rfl
      rw [this, hcompat]
      exact SetLike.coe_mem _

end FltWs24.Prim

open AlgebraicCurve ModularCurve IsLocalRing in
theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]
    (f : modularFunctionFieldBar N) (hf : f ≠ 0)
    (hpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), W.ord f < 0 →
      ∃ a : A, 0 < W.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧
      (∀ k : ℤ, (c • (f : LaurentSeries (AlgebraicClosure ℚ))).coeff k ∈ A) ∧
      ∃ n : ℤ, (c • (f : LaurentSeries (AlgebraicClosure ℚ))).coeff n ≠ 0 ∧
        ((c • (f : LaurentSeries (AlgebraicClosure ℚ))).coeff n)⁻¹ ∈ A := by
  classical
  obtain ⟨c, hc, hcint⟩ := ModularCurve.exists_forall_coeff_smul_mem_of_forall_ord_neg A N f hf hpole
  have halg : ∀ z : AlgebraicClosure ℚ, IsAlgebraic ℚ z := by
    intro z; convert (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z <;> first | rfl | exact Subsingleton.elim _ _
  obtain ⟨K₁, hK₁fd, hK₁⟩ :=
    FltWs24.Glue.exists_finiteDimensional_coeff_mem halg (modularFunctionFieldFull N) f.2
  haveI := hK₁fd
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {c}) :=
    IntermediateField.adjoin.finiteDimensional (halg c).isIntegral
  have hx0 : c • (f : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
    refine smul_ne_zero hc ?_
    intro h
    exact hf (by exact_mod_cast h)
  obtain ⟨d, hd, hdint, n, hn0, hn⟩ := FltWs24.Prim.exists_primitive_smul A _ hx0 hcint
    (K₁ ⊔ IntermediateField.adjoin ℚ {c}) (fun k => by
      rw [HahnSeries.coeff_smul, smul_eq_mul]
      exact mul_mem ((le_sup_right : IntermediateField.adjoin ℚ {c} ≤ _)
        (IntermediateField.mem_adjoin_simple_self ℚ c)) ((le_sup_left : K₁ ≤ _) (hK₁ k)))
  refine ⟨d * c, mul_ne_zero hd hc, fun k => ?_, n, ?_, ?_⟩
  · rw [mul_smul]; exact hdint k
  · rw [mul_smul]; exact hn0
  · rw [mul_smul]; exact hn

end S_ModularCurve_exists_forall_coeff_smul_mem_and_exists_inv_coeff_mem_of_forall_ord_neg
end P2MW
export P2MW.S_ModularCurve_exists_forall_coeff_smul_mem_and_exists_inv_coeff_mem_of_forall_ord_neg (solution)
