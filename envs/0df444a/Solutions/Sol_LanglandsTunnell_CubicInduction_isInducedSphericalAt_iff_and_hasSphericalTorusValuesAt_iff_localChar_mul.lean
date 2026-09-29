-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/41c778af-3273-5c55-8db9-784c7b784724

import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul
set_option Elab.async false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.RankinSelberg

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell namespace CubicInduction p2m_export "LanglandsTunnell.CubicInduction" "sphericalTorusValue coe_diagUnits2 twoRowPointLocal HasSphericalTorusValuesAt LocalGL3 varpi heckeGen1 heckeGen2 centralGen cNormQ cosetSum IsCosetEigenfunction IsRightInvariant IsInducedSphericalAt coe_diagUnitGL2 diagHom_apply ratPrimeAt ratPrimeUnit iotaTorusLocal embedMat2 coe_iotaGL localMaximalCompact3" end LanglandsTunnell.CubicInduction
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.sphericalTorusValue_scale (a e₁ e₂ e₃ : ℂ) (n : ℕ) :
    sphericalTorusValue (a * e₁) (a ^ 2 * e₂) (a ^ 3 * e₃) n = a ^ n * sphericalTorusValue e₁ e₂ e₃ n := by
  have key : ∀ m : ℕ,
      sphericalTorusValue (a * e₁) (a ^ 2 * e₂) (a ^ 3 * e₃) m = a ^ m * sphericalTorusValue e₁ e₂ e₃ m ∧
        sphericalTorusValue (a * e₁) (a ^ 2 * e₂) (a ^ 3 * e₃) (m + 1) =
            a ^ (m + 1) * sphericalTorusValue e₁ e₂ e₃ (m + 1) ∧
          sphericalTorusValue (a * e₁) (a ^ 2 * e₂) (a ^ 3 * e₃) (m + 2) =
            a ^ (m + 2) * sphericalTorusValue e₁ e₂ e₃ (m + 2) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_, ?_⟩
      · simp only [sphericalTorusValue, pow_zero, one_mul]
      · simp only [Nat.zero_add, sphericalTorusValue, pow_one]
      · simp only [Nat.zero_add, sphericalTorusValue]
        ring
    | succ m ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      refine ⟨h1, h2, ?_⟩
      show sphericalTorusValue (a * e₁) (a ^ 2 * e₂) (a ^ 3 * e₃) (m + 3) =
        a ^ (m + 3) * sphericalTorusValue e₁ e₂ e₃ (m + 3)
      simp only [sphericalTorusValue]
      rw [h2, h1, h0]
      ring
  exact (key n).1

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.sphericalTorusValue_oneRow_scale (q a e₁ e₂ e₃ : ℂ) (n : ℕ) :
    q ^ n * sphericalTorusValue (a * e₁) (a ^ 2 * e₂) (a ^ 3 * e₃) n =
      a ^ n * (q ^ n * sphericalTorusValue e₁ e₂ e₃ n) := by
  rw [sphericalTorusValue_scale]
  ring

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.sphericalTorusValue_twoRow_scale (q a e₁ e₂ e₃ : ℂ)
    (k₁ k₂ : ℕ) :
    q ^ k₁ *
        (sphericalTorusValue (a * e₁) (a ^ 2 * e₂) (a ^ 3 * e₃) k₁ *
            sphericalTorusValue (a * e₁) (a ^ 2 * e₂) (a ^ 3 * e₃) (k₂ + 1) -
          sphericalTorusValue (a * e₁) (a ^ 2 * e₂) (a ^ 3 * e₃) (k₁ + 1) *
            sphericalTorusValue (a * e₁) (a ^ 2 * e₂) (a ^ 3 * e₃) k₂) =
      a ^ (k₁ + k₂ + 1) *
        (q ^ k₁ *
          (sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
            sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ k₂)) := by
  simp only [sphericalTorusValue_scale]
  ring

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.monoidHom_apply_eq_of_mem_doubleCoset {G : Type*} [Group G]
    {U : Subgroup G} (θ : G →* ℂˣ) (hU : ∀ u ∈ U, θ u = 1) {g x : G}
    (hx : x ∈ HeckePair.doubleCoset U g) : θ x = θ g := by
  obtain ⟨u, hu, w, hw, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  rw [map_mul, map_mul, hU u hu, hU w hw, one_mul, mul_one]

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.isRightInvariant_iff_unitMul {G : Type*} [Group G]
    (U : Subgroup G) (θ : G →* ℂˣ) (hU : ∀ u ∈ U, θ u = 1) (W W' : G → ℂ)
    (hW' : ∀ g, W' g = (θ g : ℂ) * W g) : IsRightInvariant U W ↔ IsRightInvariant U W' := by
  constructor
  · intro h g u hu
    rw [hW', hW', map_mul, hU u hu, mul_one, h g u hu]
  · intro h g u hu
    have h' := h g u hu
    rw [hW', hW', map_mul, hU u hu, mul_one] at h'
    exact mul_left_cancel₀ (θ g).ne_zero h'

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.isCosetEigenfunction_unitMul {G : Type*} [Group G]
    (U : Subgroup G) (gen : G) (θ : G →* ℂˣ) (hU : ∀ u ∈ U, θ u = 1) (W W' : G → ℂ)
    (hW' : ∀ g, W' g = (θ g : ℂ) * W g) (lam : ℂ) (h : IsCosetEigenfunction U gen W lam) :
    IsCosetEigenfunction U gen W' ((θ gen : ℂ) * lam) := by
  intro ι _ reps hreps g
  have hsum : cosetSum reps W' g = (θ g : ℂ) * (θ gen : ℂ) * cosetSum reps W g := by
    simp only [cosetSum, hW', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, monoidHom_apply_eq_of_mem_doubleCoset θ hU (hreps.mem_doubleCoset i), Units.val_mul]
  rw [hsum, h ι reps hreps g, hW' g]
  ring

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.isCosetEigenfunction_iff_unitMul {G : Type*} [Group G]
    (U : Subgroup G) (gen : G) (θ : G →* ℂˣ) (hU : ∀ u ∈ U, θ u = 1) (W W' : G → ℂ)
    (hW' : ∀ g, W' g = (θ g : ℂ) * W g) (lam : ℂ) :
    IsCosetEigenfunction U gen W lam ↔ IsCosetEigenfunction U gen W' ((θ gen : ℂ) * lam) := by
  refine ⟨isCosetEigenfunction_unitMul U gen θ hU W W' hW' lam, fun h => ?_⟩
  have hU' : ∀ u ∈ U, θ⁻¹ u = 1 := fun u hu => by
    rw [MonoidHom.inv_apply, hU u hu, inv_one]
  have hW : ∀ g, W g = (θ⁻¹ g : ℂ) * W' g := fun g => by
    rw [hW' g, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_mul_cancel_left₀ (θ g).ne_zero]
  have key := isCosetEigenfunction_unitMul U gen θ⁻¹ hU' W' W hW ((θ gen : ℂ) * lam) h
  rwa [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_mul_cancel_left₀ (θ gen).ne_zero] at key

private theorem inducedFactor_eq_comp_of_mem_primeFibre
    (K : Type) [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (v : HeightOneSpectrum (𝓞 ℚ)) (a : ℂ) (c c' : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ w ∈ primeFibre ℚ K v, c' w = a ^ (v.asIdeal.inertiaDeg' w.asIdeal) * c w)
    (w : HeightOneSpectrum (𝓞 K)) (hw : w ∈ primeFibre ℚ K v) :
    inducedFactor ℚ c' w = (inducedFactor ℚ c w).comp (Polynomial.C a * Polynomial.X) := by
  have hv : w.under (𝓞 ℚ) = v := hw
  simp only [inducedFactor, hv, hc w hw, Polynomial.sub_comp, Polynomial.C_comp, Polynomial.C_mul_comp,
    Polynomial.pow_comp, Polynomial.X_comp, mul_pow, ← Polynomial.C_pow, Polynomial.C_mul]
  ring

private theorem comp_finprod_mem_of_injective {ι : Type} (S : Set ι) (f : ι → Polynomial ℂ) (q : Polynomial ℂ)
    (hq : Function.Injective fun p : Polynomial ℂ => p.comp q) :
    (∏ᶠ i ∈ S, f i).comp q = ∏ᶠ i ∈ S, (f i).comp q := by
  have hinj : Function.Injective (Polynomial.compRingHom q).toMonoidHom := fun p p' h => hq (by simpa using h)
  have h1 := MonoidHom.map_finprod_of_injective (Polynomial.compRingHom q).toMonoidHom hinj
    (fun i => ∏ᶠ (_ : i ∈ S), f i)
  have h2 : ∀ i, (Polynomial.compRingHom q).toMonoidHom (∏ᶠ (_ : i ∈ S), f i) =
      ∏ᶠ (_ : i ∈ S), (Polynomial.compRingHom q).toMonoidHom (f i) :=
    fun i => MonoidHom.map_finprod_Prop _ _
  simp only [h2] at h1
  simpa using h1

private theorem inducedEulerPoly_eq_comp
    (K : Type) [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (v : HeightOneSpectrum (𝓞 ℚ)) (a : ℂ) (ha : a ≠ 0) (c c' : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ w ∈ primeFibre ℚ K v, c' w = a ^ (v.asIdeal.inertiaDeg' w.asIdeal) * c w) :
    inducedEulerPoly ℚ c' v = (inducedEulerPoly ℚ c v).comp (Polynomial.C a * Polynomial.X) := by
  have hinj : Function.Injective fun p : Polynomial ℂ => p.comp (Polynomial.C a * Polynomial.X) := by
    intro p p' h
    ext n
    have hn := congrArg (fun r : Polynomial ℂ => r.coeff n) h
    simp only [Polynomial.comp_C_mul_X_coeff] at hn
    exact mul_right_cancel₀ (pow_ne_zero n ha) hn
  unfold inducedEulerPoly
  rw [comp_finprod_mem_of_injective (primeFibre ℚ K v) (inducedFactor ℚ c) _ hinj]
  exact finprod_mem_congr rfl fun w hw => inducedFactor_eq_comp_of_mem_primeFibre K v a c c' hc w hw

private theorem inducedE1_eq_mul
    (K : Type) [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (c c' : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ w ∈ primeFibre ℚ K v,
      c' w = (χ (uniformizerIdele ℚ v) : ℂ) ^ (v.asIdeal.inertiaDeg' w.asIdeal) * c w) :
    inducedE1 ℚ c' v = (χ (uniformizerIdele ℚ v) : ℂ) * inducedE1 ℚ c v := by
  unfold inducedE1
  rw [inducedEulerPoly_eq_comp K v (χ (uniformizerIdele ℚ v) : ℂ) (Units.ne_zero _) c c' hc,
    Polynomial.comp_C_mul_X_coeff]
  ring

private theorem inducedE2_eq_pow_mul
    (K : Type) [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (c c' : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ w ∈ primeFibre ℚ K v,
      c' w = (χ (uniformizerIdele ℚ v) : ℂ) ^ (v.asIdeal.inertiaDeg' w.asIdeal) * c w) :
    inducedE2 ℚ c' v = (χ (uniformizerIdele ℚ v) : ℂ) ^ 2 * inducedE2 ℚ c v := by
  unfold inducedE2
  rw [inducedEulerPoly_eq_comp K v (χ (uniformizerIdele ℚ v) : ℂ) (Units.ne_zero _) c c' hc,
    Polynomial.comp_C_mul_X_coeff]
  ring

private theorem inducedE3_eq_pow_mul
    (K : Type) [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (c c' : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ w ∈ primeFibre ℚ K v,
      c' w = (χ (uniformizerIdele ℚ v) : ℂ) ^ (v.asIdeal.inertiaDeg' w.asIdeal) * c w) :
    inducedE3 ℚ c' v = (χ (uniformizerIdele ℚ v) : ℂ) ^ 3 * inducedE3 ℚ c v := by
  unfold inducedE3
  rw [inducedEulerPoly_eq_comp K v (χ (uniformizerIdele ℚ v) : ℂ) (Units.ne_zero _) c c' hc,
    Polynomial.comp_C_mul_X_coeff]
  ring

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.valued_det_le_one (v : HeightOneSpectrum (𝓞 ℚ))
    (N : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (h : ∀ i j, Valued.v (N i j) ≤ 1) :
    Valued.v N.det ≤ 1 := by
  let M : Matrix (Fin 3) (Fin 3) (v.adicCompletionIntegers ℚ) := fun i j =>
    ⟨N i j, by rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]; exact h i j⟩
  have hM : (v.adicCompletionIntegers ℚ).subtype.mapMatrix M = N := by
    ext i j
    rfl
  have hdet : N.det = (v.adicCompletionIntegers ℚ).subtype M.det := by
    rw [RingHom.map_det, hM]
  have hmem := M.det.2
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hmem
  rw [hdet]
  exact hmem

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private noncomputable def LanglandsTunnell.CubicInduction.twistHom (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) : LocalGL3 v →* ℂˣ :=
  (localChar χ v).comp Matrix.GeneralLinearGroup.det

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.twistHom_eq_one_of_mem (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hχ : IsUnramifiedCharAt χ v) :
    ∀ u ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, twistHom χ v u = 1 := by
  intro u hu
  obtain ⟨h1, h2⟩ := hu
  show localChar χ v (Matrix.GeneralLinearGroup.det u) = 1
  apply hχ
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      Matrix.GeneralLinearGroup.val_det_apply]
    exact valued_det_le_one v _ h1
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← map_inv,
      Matrix.GeneralLinearGroup.val_det_apply]
    exact valued_det_le_one v _ h2

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.det_heckeGen1 (v : HeightOneSpectrum (𝓞 ℚ)) :
    Matrix.GeneralLinearGroup.det (heckeGen1 v) = NumberField.AdelicLevel.uniformizerUnit ℚ v := by
  ext : 1
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det (Matrix.diagonal ![varpi v, 1, 1]) = _
  simp [Matrix.det_diagonal, Fin.prod_univ_three]

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.det_heckeGen2 (v : HeightOneSpectrum (𝓞 ℚ)) :
    Matrix.GeneralLinearGroup.det (heckeGen2 v) = NumberField.AdelicLevel.uniformizerUnit ℚ v ^ 2 := by
  ext : 1
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det (Matrix.diagonal ![varpi v, varpi v, 1]) = _
  simp [Matrix.det_diagonal, Fin.prod_univ_three]
  ring

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.det_centralGen (v : HeightOneSpectrum (𝓞 ℚ)) :
    Matrix.GeneralLinearGroup.det (centralGen v) = NumberField.AdelicLevel.uniformizerUnit ℚ v ^ 3 := by
  ext : 1
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det (Matrix.diagonal ![varpi v, varpi v, varpi v]) = _
  simp [Matrix.det_diagonal, Fin.prod_univ_three]
  ring

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.det_iotaTorusLocal (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Matrix.GeneralLinearGroup.det (iotaTorusLocal v n) = ratPrimeUnit v ^ n := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, iotaTorusLocal, diagHom_apply, coe_iotaGL, coe_diagUnitGL2]
  simp [embedMat2, Matrix.det_fin_three]

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.det_twoRowPointLocal (v : HeightOneSpectrum (𝓞 ℚ))
    (k₁ k₂ : ℕ) :
    Matrix.GeneralLinearGroup.det (twoRowPointLocal v k₁ k₂) = ratPrimeUnit v ^ k₁ * ratPrimeUnit v ^ k₂ := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, twoRowPointLocal, coe_iotaGL, coe_diagUnits2]
  simp [embedMat2, Matrix.det_fin_three]

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.valued_ratPrimeAt (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (ratPrimeAt v) = WithZero.exp (-1 : ℤ) := by
  have hN : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hN0 : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdvd : v.asIdeal ^ 1 ∣ Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ)} := by
    rw [pow_one, Ideal.dvd_span_singleton]
    exact Ideal.absNorm_mem v.asIdeal
  have hndvd : ¬ v.asIdeal ^ 2 ∣ Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ)} := by
    intro h
    have h1 := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd h)
    rw [map_pow, Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 ℚ)), Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one, Int.natAbs_natCast] at h1
    have h2 := Nat.le_of_dvd (by omega) h1
    nlinarith
  have hmult : multiplicity v.asIdeal (Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ)}) = 1 :=
    multiplicity_eq_of_dvd_of_not_dvd hdvd hndvd
  have h1 : Valued.v (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ)) =
      v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ)) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) (v := v)
      (r := ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ))
  have h2 : v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ)) =
      v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) :=
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := ℚ) (v := v)
      (r := ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ))
  rw [ratPrimeAt, ← map_natCast (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ)), h1, h2,
    v.intValuation_eq_exp_neg_multiplicity hN0, hmult]
  simp

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.localChar_ratPrimeUnit (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hχ : IsUnramifiedCharAt χ v) :
    localChar χ v (ratPrimeUnit v) = localChar χ v (NumberField.AdelicLevel.uniformizerUnit ℚ v) := by
  set t : (v.adicCompletion ℚ)ˣ := (NumberField.AdelicLevel.uniformizerUnit ℚ v)⁻¹ * ratPrimeUnit v with ht
  have hval : Valued.v (t : v.adicCompletion ℚ) = 1 := by
    rw [ht, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀,
      NumberField.AdelicLevel.valued_uniformizerUnit, ratPrimeUnit, Units.val_mk0, valued_ratPrimeAt]
    exact inv_mul_cancel₀ WithZero.exp_ne_zero
  have h1 : (t : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hval]
  have h2 : ((t⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀,
      hval, inv_one]
  have hkey : localChar χ v t = 1 := hχ t h1 h2
  have hsplit : ratPrimeUnit v = NumberField.AdelicLevel.uniformizerUnit ℚ v * t := by
    rw [ht, mul_inv_cancel_left]
  rw [hsplit, map_mul, hkey, mul_one]

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.localChar_uniformizerUnit (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    localChar χ v (NumberField.AdelicLevel.uniformizerUnit ℚ v) = χ (uniformizerIdele ℚ v) :=
  rfl

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in
private theorem LanglandsTunnell.CubicInduction.twistHom_heckeGen1 (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    (twistHom χ v (heckeGen1 v) : ℂ) = (χ (uniformizerIdele ℚ v) : ℂ) := by
  show (localChar χ v (Matrix.GeneralLinearGroup.det (heckeGen1 v)) : ℂ) = _
  rw [det_heckeGen1, localChar_uniformizerUnit]

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in
private theorem LanglandsTunnell.CubicInduction.twistHom_heckeGen2 (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    (twistHom χ v (heckeGen2 v) : ℂ) = (χ (uniformizerIdele ℚ v) : ℂ) ^ 2 := by
  show (localChar χ v (Matrix.GeneralLinearGroup.det (heckeGen2 v)) : ℂ) = _
  rw [det_heckeGen2, map_pow, localChar_uniformizerUnit, Units.val_pow_eq_pow_val]

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in
private theorem LanglandsTunnell.CubicInduction.twistHom_centralGen (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    (twistHom χ v (centralGen v) : ℂ) = (χ (uniformizerIdele ℚ v) : ℂ) ^ 3 := by
  show (localChar χ v (Matrix.GeneralLinearGroup.det (centralGen v)) : ℂ) = _
  rw [det_centralGen, map_pow, localChar_uniformizerUnit, Units.val_pow_eq_pow_val]

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in
private theorem LanglandsTunnell.CubicInduction.twistHom_iotaTorusLocal (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hχ : IsUnramifiedCharAt χ v) (n : ℕ) :
    (twistHom χ v (iotaTorusLocal v n) : ℂ) = (χ (uniformizerIdele ℚ v) : ℂ) ^ n := by
  show (localChar χ v (Matrix.GeneralLinearGroup.det (iotaTorusLocal v n)) : ℂ) = _
  rw [det_iotaTorusLocal, map_pow, localChar_ratPrimeUnit χ v hχ, localChar_uniformizerUnit,
    Units.val_pow_eq_pow_val]

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in
private theorem LanglandsTunnell.CubicInduction.twistHom_twoRowPointLocal (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hχ : IsUnramifiedCharAt χ v) (k₁ k₂ : ℕ) :
    (twistHom χ v (twoRowPointLocal v k₁ k₂) : ℂ) = (χ (uniformizerIdele ℚ v) : ℂ) ^ (k₁ + k₂) := by
  show (localChar χ v (Matrix.GeneralLinearGroup.det (twoRowPointLocal v k₁ k₂)) : ℂ) = _
  rw [det_twoRowPointLocal, map_mul, map_pow, map_pow, localChar_ratPrimeUnit χ v hχ, localChar_uniformizerUnit,
    Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_add]

theorem solution
    (K : Type) [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (hχ : IsUnramifiedCharAt χ v)
    (c c' : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ w ∈ primeFibre ℚ K v,
      c' w = (χ (uniformizerIdele ℚ v) : ℂ) ^ (v.asIdeal.inertiaDeg' w.asIdeal) * c w)
    (W : LocalGL3 v → ℂ) :
    (IsInducedSphericalAt c v (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ↔
      IsInducedSphericalAt c' v (localMaximalCompact3 (𝓞 ℚ) ℚ v)
        (fun g => (localChar χ v (Matrix.GeneralLinearGroup.det g) : ℂ) * W g)) ∧
    (HasSphericalTorusValuesAt c v W ↔
      HasSphericalTorusValuesAt c' v (fun g => (localChar χ v (Matrix.GeneralLinearGroup.det g) : ℂ) * W g)) := by
  set W' : LocalGL3 v → ℂ := fun g => (localChar χ v (Matrix.GeneralLinearGroup.det g) : ℂ) * W g
  have hW' : ∀ g, W' g = (twistHom χ v g : ℂ) * W g := fun _ => rfl
  have hU : ∀ u ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, twistHom χ v u = 1 := twistHom_eq_one_of_mem χ v hχ
  have hη : (χ (uniformizerIdele ℚ v) : ℂ) ≠ 0 := Units.ne_zero _
  refine ⟨?_, ?_⟩
  · have e1 : cNormQ v * ((χ (uniformizerIdele ℚ v) : ℂ) * inducedE1 ℚ c v) =
        (twistHom χ v (heckeGen1 v) : ℂ) * (cNormQ v * inducedE1 ℚ c v) := by
      rw [twistHom_heckeGen1, mul_left_comm]
    have e2 : cNormQ v * ((χ (uniformizerIdele ℚ v) : ℂ) ^ 2 * inducedE2 ℚ c v) =
        (twistHom χ v (heckeGen2 v) : ℂ) * (cNormQ v * inducedE2 ℚ c v) := by
      rw [twistHom_heckeGen2, mul_left_comm]
    have hcent : ∀ g : LocalGL3 v, (twistHom χ v (centralGen v * g) : ℂ) =
        (χ (uniformizerIdele ℚ v) : ℂ) ^ 3 * (twistHom χ v g : ℂ) := by
      intro g
      rw [map_mul, Units.val_mul, twistHom_centralGen]
    unfold IsInducedSphericalAt
    rw [inducedE1_eq_mul K χ v c c' hc, inducedE2_eq_pow_mul K χ v c c' hc, inducedE3_eq_pow_mul K χ v c c' hc,
      e1, e2]
    refine and_congr (isRightInvariant_iff_unitMul _ (twistHom χ v) hU W W' hW') (and_congr
      (isCosetEigenfunction_iff_unitMul _ _ (twistHom χ v) hU W W' hW' _) (and_congr
        (isCosetEigenfunction_iff_unitMul _ _ (twistHom χ v) hU W W' hW' _) ?_))
    constructor
    · intro h g
      simp only [hW']
      rw [hcent, h g]
      ring
    · intro h g
      have hg : (twistHom χ v (centralGen v * g) : ℂ) * W (centralGen v * g) =
          (χ (uniformizerIdele ℚ v) : ℂ) ^ 3 * inducedE3 ℚ c v * ((twistHom χ v g : ℂ) * W g) := h g
      rw [hcent] at hg
      have hne : (χ (uniformizerIdele ℚ v) : ℂ) ^ 3 * (twistHom χ v g : ℂ) ≠ 0 :=
        mul_ne_zero (pow_ne_zero 3 hη) (Units.ne_zero _)
      refine mul_left_cancel₀ hne ?_
      rw [hg]
      ring
  · unfold HasSphericalTorusValuesAt
    rw [inducedE1_eq_mul K χ v c c' hc, inducedE2_eq_pow_mul K χ v c c' hc, inducedE3_eq_pow_mul K χ v c c' hc]
    simp only [sphericalTorusValue_oneRow_scale, sphericalTorusValue_twoRow_scale, hW']
    refine and_congr (forall_congr' fun n => ?_)
      (forall_congr' fun k₁ => forall_congr' fun k₂ => imp_congr_right fun _ => ?_)
    · rw [twistHom_iotaTorusLocal χ v hχ n]
      exact (mul_right_inj' (pow_ne_zero n hη)).symm
    · rw [twistHom_twoRowPointLocal χ v hχ, ← add_assoc]
      exact (mul_right_inj' (pow_ne_zero _ hη)).symm
#print axioms solution

end S_LanglandsTunnell_CubicInduction_isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul (solution)
