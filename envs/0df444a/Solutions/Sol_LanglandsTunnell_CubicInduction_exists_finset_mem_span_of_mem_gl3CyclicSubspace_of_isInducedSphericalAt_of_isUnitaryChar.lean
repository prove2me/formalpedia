-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_finset_mem_span_of_mem_gl3CyclicSubspace_of_isInducedSphericalAt_of_isUnitaryChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/87baccb3-db4e-5a53-b16a-dafc065c4f38

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_coefficientFn_principalSeries3_of_isCosetEigenfunction_of_norm_eq_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_finset_coefficientFn_mem_span_of_isOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_mem_span_of_mem_gl3CyclicSubspace_of_isInducedSphericalAt_of_isUnitaryChar
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.Converse

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.addCharLevel RankinSelberg.primeFibre RankinSelberg.inducedFactor RankinSelberg.inducedEulerPoly RankinSelberg.inducedE1 RankinSelberg.inducedE2 RankinSelberg.inducedE3 CubicInduction.exists_eq_coefficientFn_principalSeries3_of_isCosetEigenfunction_of_norm_eq_one CubicInduction.exists_finset_coefficientFn_mem_span_of_isOpen"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3CyclicSubspace gl3CyclicSubspace_zero inducedCoeff localMaximalCompact3 LocalGL3 centralGen IsInducedSphericalAt principalSeries3 rightTranslate_mem_principalSeries3 coefficientFn exists_eq_coefficientFn_principalSeries3_of_isCosetEigenfunction_of_norm_eq_one exists_finset_coefficientFn_mem_span_of_isOpen"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem ringHom_ringOfIntegers_rat_ext {A : Type} [Ring A] (f g : 𝓞 ℚ →+* A) : f = g := by
  have h : f.comp Rat.ringOfIntegersEquiv.symm.toRingHom = g.comp Rat.ringOfIntegersEquiv.symm.toRingHom :=
    Subsingleton.elim _ _
  ext x
  have hx : Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv x) = x := Rat.ringOfIntegersEquiv.symm_apply_apply x
  have hfx : f (Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv x)) =
      g (Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv x)) :=
    RingHom.congr_fun h (Rat.ringOfIntegersEquiv x)
  rwa [hx] at hfx

private theorem finite_ringOfIntegers_of_algebra (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] :
    Module.Finite (𝓞 ℚ) (𝓞 K) :=
  Module.Finite.of_restrictScalars_finite ℤ (𝓞 ℚ) (𝓞 K)

private theorem algebraMap_ringOfIntegers_rat_injective (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] : Function.Injective (algebraMap (𝓞 ℚ) (𝓞 K)) := by
  have h : algebraMap (𝓞 ℚ) (𝓞 K) = (Int.castRingHom (𝓞 K)).comp Rat.ringOfIntegersEquiv.toRingHom :=
    ringHom_ringOfIntegers_rat_ext _ _
  rw [h]
  exact (RingHom.injective_int (Int.castRingHom (𝓞 K))).comp Rat.ringOfIntegersEquiv.injective

private theorem isTorsionFree_ringOfIntegers_of_algebra (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] : Module.IsTorsionFree (𝓞 ℚ) (𝓞 K) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap_ringOfIntegers_rat_injective K)

private theorem isScalarTower_ringOfIntegers_of_algebra (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] : IsScalarTower (𝓞 ℚ) (𝓞 K) K :=
  IsScalarTower.of_algebraMap_eq fun x => by
    have h : algebraMap (𝓞 ℚ) K = (algebraMap (𝓞 K) K).comp (algebraMap (𝓞 ℚ) (𝓞 K)) :=
      ringHom_ringOfIntegers_rat_ext _ _
    exact RingHom.congr_fun h x

private theorem liesOver_of_mem_primeFibre {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] {v : HeightOneSpectrum (𝓞 ℚ)} {𝔓 : HeightOneSpectrum (𝓞 K)}
    (h : 𝔓 ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K v) : 𝔓.asIdeal.LiesOver v.asIdeal := by
  have h' : v.asIdeal = 𝔓.asIdeal.under (𝓞 ℚ) := (congrArg HeightOneSpectrum.asIdeal h).symm
  exact ⟨h'⟩

private theorem one_le_inertiaDeg_of_mem_primeFibre {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] {v : HeightOneSpectrum (𝓞 ℚ)} {𝔓 : HeightOneSpectrum (𝓞 K)}
    (h : 𝔓 ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K v) :
    1 ≤ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
  have hv : 𝔓.under (𝓞 ℚ) = v := h
  rw [hv]
  haveI := finite_ringOfIntegers_of_algebra K
  haveI := liesOver_of_mem_primeFibre h
  exact Ideal.inertiaDeg'_pos v.asIdeal 𝔓.asIdeal

private theorem asIdeal_mem_primesOverFinset_of_mem_primeFibre {K : Type} [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] {v : HeightOneSpectrum (𝓞 ℚ)}
    {𝔓 : HeightOneSpectrum (𝓞 K)} (h : 𝔓 ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K v) :
    𝔓.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K) := by
  haveI := isTorsionFree_ringOfIntegers_of_algebra K
  rw [IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot]
  exact ⟨𝔓.isPrime, liesOver_of_mem_primeFibre h⟩

private theorem primeFibre_finite_of_algebra (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (v : HeightOneSpectrum (𝓞 ℚ)) :
    (LanglandsTunnell.RankinSelberg.primeFibre ℚ K v).Finite := by
  refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal) ?_ HeightOneSpectrum.asIdeal_injective.injOn
  refine (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K)).finite_toSet.subset ?_
  rintro _ ⟨𝔓, h𝔓, rfl⟩
  exact asIdeal_mem_primesOverFinset_of_mem_primeFibre h𝔓

private theorem sum_inertiaDeg_primeFibre_le_three (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (hdeg : Module.finrank ℚ K = 3) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∑ 𝔓 ∈ (primeFibre_finite_of_algebra K v).toFinset, (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal ≤ 3 := by
  haveI := finite_ringOfIntegers_of_algebra K
  haveI := isScalarTower_ringOfIntegers_of_algebra K
  have hsum := Ideal.sum_ramification_inertia (S := 𝓞 K) (p := v.asIdeal) ℚ K v.ne_bot
  rw [hdeg] at hsum
  rw [← hsum]
  calc
    ∑ 𝔓 ∈ (primeFibre_finite_of_algebra K v).toFinset, (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal
        = ∑ 𝔓 ∈ (primeFibre_finite_of_algebra K v).toFinset, v.asIdeal.inertiaDeg' 𝔓.asIdeal := by
          refine Finset.sum_congr rfl fun 𝔓 h𝔓 => ?_
          have hmem : 𝔓 ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K v :=
            (Set.Finite.mem_toFinset (primeFibre_finite_of_algebra K v)).mp h𝔓
          have hv : 𝔓.under (𝓞 ℚ) = v := hmem
          rw [hv]
    _ ≤ ∑ 𝔓 ∈ (primeFibre_finite_of_algebra K v).toFinset,
          v.asIdeal.ramificationIdx' 𝔓.asIdeal * v.asIdeal.inertiaDeg' 𝔓.asIdeal := by
          refine Finset.sum_le_sum fun 𝔓 h𝔓 => ?_
          have hmem := asIdeal_mem_primesOverFinset_of_mem_primeFibre
            ((Set.Finite.mem_toFinset (primeFibre_finite_of_algebra K v)).mp h𝔓)
          have he : v.asIdeal.ramificationIdx' 𝔓.asIdeal ≠ 0 :=
            Ideal.Factors.ramificationIdx_ne_zero v.asIdeal ⟨𝔓.asIdeal, hmem⟩
          exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero he)
    _ = ∑ P ∈ (primeFibre_finite_of_algebra K v).toFinset.image HeightOneSpectrum.asIdeal,
          v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P := by
          rw [Finset.sum_image fun a _ b _ hab => HeightOneSpectrum.asIdeal_injective hab]
    _ ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K),
          v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P := by
          refine Finset.sum_le_sum_of_subset fun P hP => ?_
          obtain ⟨𝔓, h𝔓, rfl⟩ := Finset.mem_image.mp hP
          exact asIdeal_mem_primesOverFinset_of_mem_primeFibre
            ((Set.Finite.mem_toFinset (primeFibre_finite_of_algebra K v)).mp h𝔓)

private theorem inducedEulerPoly_eq_prod_primeFibre (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (c : HeightOneSpectrum (𝓞 K) → ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    LanglandsTunnell.RankinSelberg.inducedEulerPoly ℚ c v =
      ∏ 𝔓 ∈ (primeFibre_finite_of_algebra K v).toFinset, LanglandsTunnell.RankinSelberg.inducedFactor ℚ c 𝔓 :=
  finprod_mem_eq_finite_toFinset_prod _ _

private theorem natDegree_inducedEulerPoly_le_three (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (hdeg : Module.finrank ℚ K = 3) (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) : (LanglandsTunnell.RankinSelberg.inducedEulerPoly ℚ c v).natDegree ≤ 3 := by
  rw [inducedEulerPoly_eq_prod_primeFibre]
  refine (Polynomial.natDegree_prod_le _ _).trans ((Finset.sum_le_sum fun 𝔓 _ => ?_).trans
    (sum_inertiaDeg_primeFibre_le_three K hdeg v))
  unfold LanglandsTunnell.RankinSelberg.inducedFactor
  refine (Polynomial.natDegree_sub_le _ _).trans ?_
  rw [Polynomial.natDegree_C, Nat.zero_max]
  exact Polynomial.natDegree_C_mul_X_pow_le _ _

private theorem coeff_zero_inducedEulerPoly_eq_one (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (c : HeightOneSpectrum (𝓞 K) → ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (LanglandsTunnell.RankinSelberg.inducedEulerPoly ℚ c v).coeff 0 = 1 := by
  rw [inducedEulerPoly_eq_prod_primeFibre, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  refine Finset.prod_eq_one fun 𝔓 h𝔓 => ?_
  have hf := one_le_inertiaDeg_of_mem_primeFibre ((Set.Finite.mem_toFinset (primeFibre_finite_of_algebra K v)).mp h𝔓)
  have hf0 : (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal ≠ 0 := by omega
  simp only [LanglandsTunnell.RankinSelberg.inducedFactor, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, zero_pow hf0, mul_zero, sub_zero]

private theorem norm_eq_one_of_eval_inducedEulerPoly_eq_zero (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ 𝔓, c 𝔓 = 0 ∨ ‖c 𝔓‖ = 1) (v : HeightOneSpectrum (𝓞 ℚ)) (z : ℂ)
    (hz : (LanglandsTunnell.RankinSelberg.inducedEulerPoly ℚ c v).eval z = 0) : ‖z‖ = 1 := by
  rw [inducedEulerPoly_eq_prod_primeFibre, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hz
  obtain ⟨𝔓, h𝔓, hz⟩ := hz
  have hf := one_le_inertiaDeg_of_mem_primeFibre ((Set.Finite.mem_toFinset (primeFibre_finite_of_algebra K v)).mp h𝔓)
  simp only [LanglandsTunnell.RankinSelberg.inducedFactor, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero] at hz
  rcases hc 𝔓 with h0 | h1
  · rw [h0, zero_mul] at hz
    exact absurd hz one_ne_zero
  · have hn := congrArg (fun w : ℂ => ‖w‖) hz
    simp only [norm_one, norm_mul, norm_pow, h1, one_mul] at hn
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) (by omega)).mp hn.symm

private theorem inducedCoeff_eq_zero_or_norm_eq_one (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 K) K μ)
    (𝔓 : HeightOneSpectrum (𝓞 K)) : inducedCoeff K μ 𝔓 = 0 ∨ ‖inducedCoeff K μ 𝔓‖ = 1 := by
  unfold inducedCoeff
  split_ifs
  · exact Or.inr (hμ _)
  · exact Or.inl rfl

private theorem exists_unitRoots_of_cubic (P : Polynomial ℂ) (h0 : P.coeff 0 = 1) (hdeg : P.natDegree ≤ 3)
    (h3 : P.coeff 3 ≠ 0) (hroots : ∀ z : ℂ, P.eval z = 0 → ‖z‖ = 1) :
    ∃ α : Fin 3 → ℂ, (∀ i, ‖α i‖ = 1) ∧ -P.coeff 1 = α 0 + α 1 + α 2 ∧
      P.coeff 2 = α 0 * α 1 + α 0 * α 2 + α 1 * α 2 ∧ -P.coeff 3 = α 0 * α 1 * α 2 := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, P.coeff 3 = c := ⟨_, rfl⟩
  have hnat : P.natDegree = 3 := le_antisymm hdeg (Polynomial.le_natDegree_of_ne_zero h3)
  have hlc : P.leadingCoeff = c := by rw [← Polynomial.coeff_natDegree, hnat, hc]
  have hcard : Multiset.card P.roots = 3 := by rw [IsAlgClosed.card_roots_eq_natDegree, hnat]
  obtain ⟨x, y, z, hxyz⟩ := Multiset.card_eq_three.mp hcard
  have hx : ‖x‖ = 1 := hroots x (Polynomial.isRoot_of_mem_roots (by rw [hxyz]; simp))
  have hy : ‖y‖ = 1 := hroots y (Polynomial.isRoot_of_mem_roots (by rw [hxyz]; simp))
  have hz : ‖z‖ = 1 := hroots z (Polynomial.isRoot_of_mem_roots (by rw [hxyz]; simp))
  have h := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := P) (by rw [hcard, hnat])
  rw [hlc, hxyz] at h
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton] at h
  have hQ : (Polynomial.X - Polynomial.C x) * ((Polynomial.X - Polynomial.C y) * (Polynomial.X - Polynomial.C z)) =
      Polynomial.X ^ 3 - Polynomial.C (x + y + z) * Polynomial.X ^ 2 +
        Polynomial.C (x * y + x * z + y * z) * Polynomial.X - Polynomial.C (x * y * z) := by
    simp only [map_add, map_mul]
    ring
  rw [hQ] at h
  have hc0 : -(c * (x * y * z)) = 1 := by
    simpa [Polynomial.coeff_X, Polynomial.coeff_C, h0] using congrArg (fun q : Polynomial ℂ => q.coeff 0) h
  have hc1 : c * (x * y + x * z + y * z) = P.coeff 1 := by
    simpa [Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_mul_X_pow'] using
      congrArg (fun q : Polynomial ℂ => q.coeff 1) h
  have hc2 : -(c * (x + y + z)) = P.coeff 2 := by
    have h2 := congrArg (fun q : Polynomial ℂ => q.coeff 2) h
    simp [Polynomial.coeff_C, Polynomial.coeff_mul_X_pow'] at h2
    linear_combination h2
  have hx' : x⁻¹ = -(c * (y * z)) := inv_eq_of_mul_eq_one_right (by linear_combination hc0)
  have hy' : y⁻¹ = -(c * (x * z)) := inv_eq_of_mul_eq_one_right (by linear_combination hc0)
  have hz' : z⁻¹ = -(c * (x * y)) := inv_eq_of_mul_eq_one_right (by linear_combination hc0)
  refine ⟨![x⁻¹, y⁻¹, z⁻¹], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [hx, hy, hz]
  · show -P.coeff 1 = x⁻¹ + y⁻¹ + z⁻¹
    rw [← hc1, hx', hy', hz']
    ring
  · show P.coeff 2 = x⁻¹ * y⁻¹ + x⁻¹ * z⁻¹ + y⁻¹ * z⁻¹
    rw [← hc2, hx', hy', hz']
    linear_combination (c * (x + y + z)) * hc0
  · show -P.coeff 3 = x⁻¹ * y⁻¹ * z⁻¹
    rw [hc, hx', hy', hz']
    linear_combination (c * (1 - c * (x * y * z))) * hc0

end LanglandsTunnell.CubicInduction

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_mem_span_of_mem_gl3CyclicSubspace_of_isInducedSphericalAt_of_isUnitaryChar.LanglandsTunnell.CubicInduction"

section Coeff
variable {v : HeightOneSpectrum (𝓞 ℚ)} {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}

private noncomputable def coeffL (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) : ↥(principalSeries3 v χ) →ₗ[ℂ] (LocalGL3 v → ℂ) where
  toFun f := coefficientFn Λ f
  map_add' f g := by
    funext x
    show Λ _ = Λ _ + Λ _
    rw [← map_add]
    congr 1
  map_smul' c f := by
    funext x
    show Λ _ = c * Λ _
    rw [← smul_eq_mul, ← map_smul]
    congr 1

private theorem coeffL_apply (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ)) :
    coeffL Λ f = coefficientFn Λ f := rfl

private theorem gl3AmbientRightTranslate_coefficientFn (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ))
    (h : LocalGL3 v) :
    gl3AmbientRightTranslate (R := ℂ) h (coefficientFn Λ f) =
      coefficientFn Λ ⟨gl3AmbientRightTranslate (R := ℂ) h f, rightTranslate_mem_principalSeries3 f.2 h⟩ := by
  funext g
  show Λ _ = Λ _
  congr 1
  apply Subtype.ext
  funext x
  show (f : LocalGL3 v → ℂ) (x * (g * h)) = (f : LocalGL3 v → ℂ) (x * g * h)
  rw [mul_assoc]

private theorem gl3CyclicSubspace_coefficientFn_le (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ)) :
    gl3CyclicSubspace (coefficientFn Λ f) ≤ LinearMap.range (coeffL Λ) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨h, rfl⟩
  show gl3AmbientRightTranslate (R := ℂ) h (coefficientFn Λ f) ∈ LinearMap.range (coeffL Λ)
  rw [gl3AmbientRightTranslate_coefficientFn]
  exact ⟨_, rfl⟩

end Coeff

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_mem_span_of_mem_gl3CyclicSubspace_of_isInducedSphericalAt_of_isUnitaryChar.LanglandsTunnell.CubicInduction in
theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 K) K μ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ)
    (hsph : IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψ : IsGL3PsiWhittakerFn ψv W)
    (hlev : LanglandsTunnell.TateLocal.addCharLevel ψv = 0) (hne : ψv ≠ 1) :
    ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)) := by
  obtain ⟨hU, hT₁, hT₂, hZ⟩ := hsph
  intro Uv hUv
  by_cases h3 : LanglandsTunnell.RankinSelberg.inducedE3 ℚ (inducedCoeff K μ) v = 0
  ·
    have hW : W = 0 := by
      funext g
      have h := hZ ((centralGen v)⁻¹ * g)
      rw [mul_inv_cancel_left, h3, zero_mul] at h
      exact h
    refine ⟨∅, fun F hF _ => ?_⟩
    subst hW
    rw [gl3CyclicSubspace_zero] at hF
    rw [(Submodule.mem_bot ℂ).mp hF]
    exact Submodule.zero_mem _
  · have hc3 : (LanglandsTunnell.RankinSelberg.inducedEulerPoly ℚ (inducedCoeff K μ) v).coeff 3 ≠ 0 := by
      intro h
      apply h3
      unfold LanglandsTunnell.RankinSelberg.inducedE3
      rw [h, neg_zero]
    obtain ⟨α, hα, h1, h2, h3'⟩ := exists_unitRoots_of_cubic _
      (coeff_zero_inducedEulerPoly_eq_one K (inducedCoeff K μ) v)
      (natDegree_inducedEulerPoly_le_three K hdeg (inducedCoeff K μ) v) hc3
      (norm_eq_one_of_eval_inducedEulerPoly_eq_zero K (inducedCoeff K μ)
        (inducedCoeff_eq_zero_or_norm_eq_one K μ hμ) v)
    unfold LanglandsTunnell.RankinSelberg.inducedE1 at hT₁
    unfold LanglandsTunnell.RankinSelberg.inducedE2 at hT₂
    unfold LanglandsTunnell.RankinSelberg.inducedE3 at hZ
    rw [h1] at hT₁
    rw [h2] at hT₂
    simp only [h3'] at hZ

    obtain ⟨χ, -, -, -, Λ, -, f, rfl⟩ :=
      LanglandsTunnell.CubicInduction.exists_eq_coefficientFn_principalSeries3_of_isCosetEigenfunction_of_norm_eq_one
        v ψv α hα W hU hT₁ hT₂ hZ hψ hlev hne

    obtain ⟨B, hB⟩ := LanglandsTunnell.CubicInduction.exists_finset_coefficientFn_mem_span_of_isOpen v χ Λ Uv hUv
    refine ⟨B, fun F hF hFk => ?_⟩
    obtain ⟨f', hf'⟩ := gl3CyclicSubspace_coefficientFn_le Λ f hF
    rw [coeffL_apply] at hf'
    subst hf'
    exact hB f' hFk

end S_LanglandsTunnell_CubicInduction_exists_finset_mem_span_of_mem_gl3CyclicSubspace_of_isInducedSphericalAt_of_isUnitaryChar
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_mem_span_of_mem_gl3CyclicSubspace_of_isInducedSphericalAt_of_isUnitaryChar (solution)
