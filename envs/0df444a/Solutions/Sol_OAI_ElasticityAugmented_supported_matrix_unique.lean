-- Prove2me | solution 1 for OAI.ElasticityAugmented.supported_matrix_unique
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:06:57.862013+00:00
-- url     : https://prove2.me/submissions/6bc6ec39-3849-4d45-9b97-5ad910f487d4

import Mathlib
import Definitions.Def_OAIQ6El004
import Definitions.Def_OAIQ6El005

section
-- module Solutions.OAIQ6_Elast.Elasticity_Planar
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open MeasureTheory Complex

lemma d_Z (v : ℂ) (f : Test) : d v (Z f) = v • f + Z (d v f) := by
  apply Subtype.ext
  funext z
  change fderiv ℝ (fun z => z * f z) z v = v * f z + z * ((d v f : ℂ → ℂ) z)
  have h := congrArg (fun L : ℂ →L[ℝ] ℂ => L v)
    ((hasFDerivAt_id z).mul ((smooth f).differentiable (by simp) z).hasFDerivAt).fderiv
  simpa [d_apply, add_comm, mul_comm, Pi.mul_def] using h

lemma deriv_conj (f : Test) (z v : ℂ) :
    fderiv ℝ (fun z => star (f z)) z v = star (fderiv ℝ (f : ℂ → ℂ) z v) := by
  have h := (Complex.conjCLE.hasFDerivAt.comp z
    ((smooth f).differentiable (by simp) z).hasFDerivAt).fderiv
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) h

lemma d_Zbar (v : ℂ) (f : Test) : d v (Zbar f) = (star v) • f + Zbar (d v f) := by
  apply Subtype.ext
  funext z
  change fderiv ℝ (fun z => star z * f z) z v = star v * f z + star z * ((d v f : ℂ → ℂ) z)
  have h := congrArg (fun L : ℂ →L[ℝ] ℂ => L v)
    ((Complex.conjCLE.hasFDerivAt (x := z)).mul
      ((smooth f).differentiable (by simp) z).hasFDerivAt).fderiv
  simpa [d_apply, Complex.star_def, add_comm, mul_comm, Pi.mul_def] using h

lemma d_d (v w : ℂ) (f : Test) (z : ℂ) :
    (d v (d w f) : ℂ → ℂ) z = fderiv ℝ (fderiv ℝ (f : ℂ → ℂ)) z v w := by
  have hd : Differentiable ℝ (fderiv ℝ (f : ℂ → ℂ)) :=
    ((smooth f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ (f : ℂ → ℂ) y w) z v = _
  rw [fderiv_clm_apply (hd z) (differentiableAt_const w)]
  simp

lemma d_comm (v w : ℂ) (f : Test) : d v (d w f) = d w (d v f) := by
  apply Subtype.ext
  funext z
  rw [d_d, d_d]
  exact (smooth f).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) _ _

lemma integrable_pair (f g : Test) : Integrable (fun z : ℂ => star (f z)*g z) := by
  exact ((Complex.conjCLE.continuous.comp (smooth f).continuous).mul (smooth g).continuous).integrable_of_hasCompactSupport (compact g).mul_left

lemma pair_add_right (f g h : Test) : pair f (g+h) = pair f g + pair f h := by
  simpa only [pair, Submodule.coe_add, Pi.add_apply, mul_add] using
    integral_add (integrable_pair f g) (integrable_pair f h)

lemma pair_add_left (f g h : Test) : pair (f+g) h = pair f h + pair g h := by
  simpa only [pair, Submodule.coe_add, Pi.add_apply, star_add, add_mul] using
    integral_add (integrable_pair f h) (integrable_pair g h)

lemma pair_sub_right (f g h : Test) : pair f (g-h) = pair f g - pair f h := by
  simpa only [pair, Submodule.coe_sub, Pi.sub_apply, mul_sub] using
    integral_sub (integrable_pair f g) (integrable_pair f h)

lemma pair_sub_left (f g h : Test) : pair (f-g) h = pair f h - pair g h := by
  simpa only [pair, Submodule.coe_sub, Pi.sub_apply, star_sub, sub_mul] using
    integral_sub (integrable_pair f h) (integrable_pair g h)

lemma pair_smul_right (f g : Test) (a : ℂ) : pair f (a • g) = a * pair f g := by
  simp only [pair, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc, mul_comm (star (f _)) a, mul_assoc]
  exact integral_const_mul a _

lemma pair_smul_left (f g : Test) (a : ℂ) : pair (a • f) g = star a * pair f g := by
  simp only [pair, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, star_mul, mul_comm (star (f _)), mul_assoc]
  exact integral_const_mul (star a) _

/-- Coordinate derivatives are skew adjoint on the actual test space. -/
lemma pair_d (f g : Test) (v : ℂ) : pair f (d v g) = -pair (d v f) g := by
  have h1 : Integrable (fun z : ℂ => fderiv ℝ (fun z => star (f z)) z v * g z) := by
    simpa only [deriv_conj, d_apply] using integrable_pair (d v f) g
  have h2 : Integrable (fun z : ℂ => star (f z)*fderiv ℝ (g : ℂ → ℂ) z v) :=
    integrable_pair f (d v g)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 (integrable_pair f g)
    (fun z _ => Complex.conjCLE.differentiableAt.comp z ((smooth f).differentiable (by simp) z))
    (fun z _ => (smooth g).differentiable (by simp) z)
    |>.trans (by simp only [pair, deriv_conj, d_apply])

lemma pair_Z (f g : Test) : pair f (Z g) = pair (Zbar f) g := by
  apply integral_congr_ae
  filter_upwards [] with z
  simp [mul_comm, mul_left_comm, mul_assoc]

lemma pair_Zbar (f g : Test) : pair f (Zbar g) = pair (Z f) g := by
  apply integral_congr_ae
  filter_upwards [] with z
  simp [mul_comm, mul_left_comm]

lemma pair_B (f g : Test) (t : ℝ) : pair f (B t g) = pair (C t f) g := by
  simp only [B, C, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, pair_add_right, pair_sub_right, pair_smul_right,
    pair_add_left, pair_sub_left, pair_smul_left, pair_d, pair_Z,
    ← neg_one_smul ℂ (d 1 f), pair_smul_left, map_neg, map_one,
    Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  ring

lemma pair_C (f g : Test) (t : ℝ) : pair f (C t g) = pair (B t f) g := by
  simp only [B, C, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, pair_add_right, pair_sub_right, pair_smul_right,
    pair_add_left, pair_sub_left, pair_smul_left, pair_d, pair_Zbar,
    ← neg_one_smul ℂ (d 1 g), pair_smul_right, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  ring

lemma Z_Zbar (f : Test) : Z (Zbar f) = Zbar (Z f) := by
  apply Subtype.ext
  funext z
  change z * (star z * f z) = star z * (z * f z)
  ring

/-- Positive commutator of the two Gaussian-conjugated planar operators. -/
lemma commutator (t : ℝ) (f : Test) :
    C t (B t f) - B t (C t f) = (4 * (t : ℂ)) • f := by
  simp only [B, C, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, map_add, map_sub, map_smul, map_neg, d_Z, d_Zbar,
    star_one, Complex.star_def, Complex.conj_I]
  rw [d_comm I 1 f, Z_Zbar f]
  trans (2 * (t : ℂ) - 2 * (t : ℂ) * I ^ 2) • f
  · module
  · congr 1
    rw [Complex.I_sq]
    ring

lemma energy_identity (t : ℝ) (f : Test) :
    pair (B t f) (B t f) - pair (C t f) (C t f) =
      (4 * (t : ℂ)) * pair f f := by
  calc
    _ = pair f (C t (B t f) - B t (C t f)) := by
      rw [pair_sub_right, pair_C f (B t f) t, pair_B f (C t f) t]
    _ = _ := by rw [commutator, pair_smul_right]

lemma mass_integral (f : Test) : mass f = ∫ z : ℂ, Complex.normSq (f z) := by
  have h := integral_re (integrable_pair f f)
  simpa only [mass, pair, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    RCLike.re_to_complex, Complex.ofReal_re] using h.symm

lemma integrable_normSq (f : Test) : Integrable (fun z : ℂ => Complex.normSq (f z)) := by
  have h := (integrable_pair f f).re
  simpa only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    RCLike.re_to_complex, Complex.ofReal_re] using h

lemma mass_nonneg (f : Test) : 0 ≤ mass f := by
  rw [mass_integral]
  exact integral_nonneg fun _ => Complex.normSq_nonneg _

lemma mass_eq_zero (f : Test) (h : mass f = 0) : f = 0 := by
  rw [mass_integral] at h
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun z : ℂ => Complex.normSq_nonneg (f z)) (integrable_normSq f)).mp h
  have hf : (f : ℂ → ℂ) =ᵐ[volume] 0 := by
    filter_upwards [hae] with z hz
    exact Complex.normSq_eq_zero.mp hz
  apply Subtype.ext
  exact ((smooth f).continuous.ae_eq_iff_eq volume continuous_zero).mp hf

/-- An actual weighted support estimate, independent of any frame existence. -/
theorem gaussian_coercivity (t : ℝ) (f : Test) :
    4 * t * mass f ≤ mass (B t f) := by
  have h := congrArg Complex.re (energy_identity t f)
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero, zero_mul, add_zero] at h
  change mass (B t f) - mass (C t f) = 4 * t * mass f at h
  linarith [mass_nonneg (C t f)]

lemma gaussian_ne_zero (t : ℝ) (z : ℂ) : gaussian t z ≠ 0 := Complex.exp_ne_zero _

lemma fderiv_gaussian (t : ℝ) (z v : ℂ) :
    fderiv ℝ (gaussian t) z v =
      gaussian t z * ((t : ℂ) / 2) * (v * star z + z * star v) := by
  have hd := (((hasFDerivAt_id z).mul (Complex.conjCLE.hasFDerivAt (x := z))).const_mul
    ((t : ℂ) / 2)).cexp
  have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hd.fderiv
  change fderiv ℝ (gaussian t) z v = _ at he
  rw [he]
  simp only [smul_apply, add_apply,
    smul_eq_mul, Complex.conjCLE_apply]
  change gaussian t z * ((t : ℂ) / 2 * (z * star v + star z * v)) = _
  ring

lemma d_W (t : ℝ) (v : ℂ) (f : Test) (z : ℂ) :
    (d v (W t f) : ℂ → ℂ) z = gaussian t z *
      (((t : ℂ) / 2) * (v * star z + z * star v) * f z + (d v f : ℂ → ℂ) z) := by
  have hd := ((smooth_gaussian t).differentiable (by simp) z).hasFDerivAt.mul
    ((smooth f).differentiable (by simp) z).hasFDerivAt
  have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hd.fderiv
  change fderiv ℝ (fun z => gaussian t z * f z) z v = _
  simp only [Pi.mul_def] at he
  rw [he]
  simp only [add_apply, smul_apply,
    smul_eq_mul, fderiv_gaussian, d_apply]
  ring

/-- Exact Gaussian conjugation of twice the planar Cauchy--Riemann operator. -/
lemma gaussian_conjugation (t : ℝ) (f : Test) :
    B t (W t f) = W t (d 1 f + I • d I f) := by
  apply Subtype.ext
  funext z
  change (d 1 (W t f) : ℂ → ℂ) z + I * (d I (W t f) : ℂ → ℂ) z -
      (t : ℂ) * (z * (gaussian t z * f z)) =
    gaussian t z * ((d 1 f : ℂ → ℂ) z + I * (d I f : ℂ → ℂ) z)
  rw [d_W, d_W]
  simp only [star_one, Complex.star_def, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

open scoped BigOperators

lemma normSq_sum_mul {n : Type*} [Fintype n] (a u : n → ℂ) :
    Complex.normSq (∑ j, a j * u j) ≤
      (∑ j, Complex.normSq (a j)) * ∑ j, Complex.normSq (u j) := by
  simp only [Complex.normSq_eq_norm_sq]
  have h := norm_sum_le Finset.univ (fun j => a j * u j)
  simp only [norm_mul] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j‖) (fun j => ‖u j‖))

lemma mass_bound {n : Type*} [Fintype n] (f : Test) (u : n → Test) (K : ℝ)
    (h : ∀ z : ℂ, Complex.normSq (f z) ≤ K * ∑ j, Complex.normSq (u j z)) :
    mass f ≤ K * ∑ j, mass (u j) := by
  simp only [mass_integral]
  have hi : Integrable (fun z : ℂ => ∑ j, Complex.normSq (u j z)) :=
    integrable_finsetSum _ (fun j _ => integrable_normSq (u j))
  calc
    _ ≤ ∫ z : ℂ, K * ∑ j, Complex.normSq (u j z) :=
      integral_mono (integrable_normSq f) (hi.const_mul K) h
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => integrable_normSq (u j))]

/-- Compact-kernel uniqueness with a coefficient bound only where a column is
nonzero. This is a genuine analytic theorem, not an assumed continuation rule. -/
theorem compact_kernel_of_bound {n : Type*} [Fintype n]
    (a : n → n → ℂ → ℂ) (u : n → Test) (K : ℝ)
    (hb : ∀ z : ℂ, (∃ j, u j z ≠ 0) → ∀ i,
      (∑ j, Complex.normSq (a i j z)) ≤ K)
    (heq : ∀ i (z : ℂ),
      (d 1 (u i) + I • d I (u i) : Test) z = ∑ j, a i j z * u j z) :
    ∀ i, u i = 0 := by
  classical
  let t : ℝ := (Fintype.card n : ℝ) * K + 1
  let w : n → Test := fun i => W t (u i)
  have hBw (i : n) (z : ℂ) :
      (B t (w i) : Test) z = ∑ j, a i j z * w j z := by
    dsimp [w]
    rw [gaussian_conjugation, W_apply, heq]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hpoint (i : n) (z : ℂ) :
      Complex.normSq ((B t (w i) : Test) z) ≤ K * ∑ j, Complex.normSq (w j z) := by
    rw [hBw]
    by_cases hu : ∃ j, u j z ≠ 0
    · exact (normSq_sum_mul (fun j => a i j z) (fun j => w j z)).trans
        (mul_le_mul_of_nonneg_right (hb z hu i)
          (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _))
    · have hw : ∀ j, w j z = 0 := by
        intro j
        have h := not_exists.mp hu j
        simp only [not_not] at h
        simp [w, h]
      simp [hw]
  have hi (i : n) : mass (B t (w i)) ≤ K * ∑ j, mass (w j) :=
    mass_bound _ w K (hpoint i)
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    (gaussian_coercivity t (w i)).trans (hi i))
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have hn : 0 ≤ ∑ i, mass (w i) := Finset.sum_nonneg fun i _ => mass_nonneg _
  have hz : ∑ i, mass (w i) = 0 := by
    by_contra hne
    have hp : 0 < ∑ i, mass (w i) := lt_of_le_of_ne hn (Ne.symm hne)
    have htK : (Fintype.card n : ℝ) * K ≥ 0 := by
      by_cases hnon : ∃ j z, u j z ≠ 0
      · obtain ⟨j, z, hj⟩ := hnon
        have hk : 0 ≤ K := (Finset.sum_nonneg
          (fun k (_ : k ∈ Finset.univ) => Complex.normSq_nonneg (a j k z))).trans
            (hb z ⟨j, hj⟩ j)
        exact mul_nonneg (Nat.cast_nonneg _) hk
      · have hw : ∀ j, w j = 0 := by
          intro j
          apply Subtype.ext
          funext z
          have hj : u j z = 0 := by simpa using not_exists.mp (not_exists.mp hnon j) z
          simp [w, hj]
        have hm : ∑ i, mass (w i) = 0 := by simp [hw, mass, pair]
        exact False.elim (hne hm)
    dsimp [t] at h
    nlinarith
  have hz' : ∀ i, mass (w i) = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mass_nonneg (w j))).mp hz i
      (Finset.mem_univ _)
  intro i
  have hw := mass_eq_zero (w i) (hz' i)
  apply Subtype.ext
  funext z
  have hval := congrArg (fun f : Test => f z) hw
  change gaussian t z * u i z = 0 at hval
  exact (mul_eq_zero.mp hval).resolve_left (gaussian_ne_zero t z)

/-- A smooth compactly supported solution of a planar matrix Cauchy--Riemann
system with continuous coefficients is zero. No smallness is imposed. -/
theorem compact_kernel {n : Type*} [Fintype n]
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, Continuous (a i j))
    (u : n → Test)
    (heq : ∀ i (z : ℂ),
      (d 1 (u i) + I • d I (u i) : Test) z = ∑ j, a i j z * u j z) :
    ∀ i, u i = 0 := by
  classical
  let S : Set ℂ := ⋃ i, tsupport (u i : ℂ → ℂ)
  have hc : IsCompact S := isCompact_iUnion fun i => compact (u i)
  let F : ℂ → ℝ := fun z => ∑ i, ∑ j, Complex.normSq (a i j z)
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  obtain ⟨K, hK⟩ := hc.exists_bound_of_continuousOn hF.continuousOn
  apply compact_kernel_of_bound a u K ?_ heq
  intro z hz i
  have hmem : z ∈ S := by
    obtain ⟨j, hj⟩ := hz
    exact Set.mem_iUnion.mpr ⟨j, subset_tsupport _ hj⟩
  calc
    (∑ j, Complex.normSq (a i j z)) ≤ F z := by
      dsimp [F]
      exact Finset.single_le_sum (f := fun k => ∑ j, Complex.normSq (a k j z))
        (fun k _ => Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _))
        (Finset.mem_univ i)
    _ ≤ ‖F z‖ := le_abs_self _
    _ ≤ K := hK z hmem

end ElasticityPlanar

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transport
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open MeasureTheory Set Topology
open scoped BigOperators ComplexConjugate
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : Type*} [Fintype n]

lemma planeMap_smooth (J : ℂ →L[ℝ] E) (x : E) :
    ContDiff ℝ (⊤ : ℕ∞) (planeMap J x) := contDiff_const.add J.contDiff
lemma planeMap_closedEmbedding (J : ℂ →L[ℝ] E) (hJ : Function.Injective J) (x : E) :
    IsClosedEmbedding (planeMap J x) := by
  exact (Homeomorph.addLeft x).isClosedEmbedding.comp
    (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hJ))
lemma plane_compact (J : ℂ →L[ℝ] E) (hJ : Function.Injective J) (x : E)
    {f : E → ℂ} (hf : HasCompactSupport f) : HasCompactSupport (f ∘ planeMap J x) := by
  apply HasCompactSupport.intro ((planeMap_closedEmbedding J hJ x).isCompact_preimage hf)
  intro z hz
  exact image_eq_zero_of_notMem_tsupport (f := f) (x := planeMap J x z) hz
lemma plane_deriv (J : ℂ →L[ℝ] E) (x : E) {f : E → ℂ}
    (hf : Differentiable ℝ f) (z v : ℂ) :
    fderiv ℝ (f ∘ planeMap J x) z v=fderiv ℝ f (planeMap J x z) (J v) := by
  have hp : HasFDerivAt (planeMap J x) J z := by
    change HasFDerivAt (fun t : ℂ => x+J t) J z
    simpa only [Pi.add_def,zero_add] using (hasFDerivAt_const x z).add J.hasFDerivAt
  exact congrArg (fun T : ℂ →L[ℝ] ℂ => T v) ((hf _).hasFDerivAt.comp z hp).fderiv

/-- Compact kernel uniqueness in ambient physical space, by restriction to
all affine characteristic planes. The plane embedding is actual and injective. -/
theorem spatial_compact_kernel (J : ℂ →L[ℝ] E) (hJ : Function.Injective J)
    (a : n → n → E → ℂ) (ha : ∀ i j, Continuous (a i j))
    (u : n → E → ℂ) (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i))
    (hc : ∀ i, HasCompactSupport (u i))
    (he : ∀ i x, fderiv ℝ (u i) x (J 1)+Complex.I*fderiv ℝ (u i) x (J Complex.I)=
      ∑ j, a i j x*u j x) : ∀ i x, u i x=0 := by
  intro i x
  let v : n → Test := fun i => ⟨u i ∘ planeMap J x,
    (hu i).comp (planeMap_smooth J x),plane_compact J hJ x (hc i)⟩
  have hv := compact_kernel (fun i j => a i j ∘ planeMap J x)
    (fun i j => (ha i j).comp (planeMap_smooth J x).continuous) v (fun j z => ?_)
  · have hh := congrArg (fun f : Test => f 0) (hv i)
    change u i (x+J 0)=0 at hh
    simpa only [map_zero,add_zero] using hh
  · change fderiv ℝ (u j ∘ planeMap J x) z 1+
      Complex.I*fderiv ℝ (u j ∘ planeMap J x) z Complex.I=_
    rw [plane_deriv J x ((hu j).differentiable (by simp)),
      plane_deriv J x ((hu j).differentiable (by simp))]
    exact he j (planeMap J x z)
end ElasticityPlanar
namespace ElasticityParameter
open Set
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {k n : Type*} [Fintype k] [Fintype n]

lemma characteristicPlane_one (e : k → E) (θ : k → ℂ) :
    characteristicPlane e θ 1=∑ r, (θ r).re • e r := by simp [characteristicPlane]
lemma characteristicPlane_I (e : k → E) (θ : k → ℂ) :
    characteristicPlane e θ Complex.I=∑ r, (θ r).im • e r := by simp [characteristicPlane]
lemma characteristicPlane_principal (e : k → E) (θ : k → ℂ) (L : E →L[ℝ] ℂ) :
    L (characteristicPlane e θ 1)+Complex.I*L (characteristicPlane e θ Complex.I)=
      ∑ r, θ r*L (e r) := by
  rw [characteristicPlane_one,characteristicPlane_I]
  simp only [map_sum,map_smul,Complex.real_smul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = ((θ r).re+(θ r).im*Complex.I)*L (e r) := by ring
    _ = θ r*L (e r) := by rw [Complex.re_add_im]

end ElasticityParameter
namespace ElasticityParameter
open scoped BigOperators InnerProductSpace

lemma real_complex_plane_injective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (ha : a≠0) (hb : b≠0) (hab : inner ℝ a b=0) :
    Function.Injective (Complex.reCLM.smulRight a+Complex.imCLM.smulRight b : ℂ →L[ℝ] E) := by
  let J : ℂ →L[ℝ] E := Complex.reCLM.smulRight a+Complex.imCLM.smulRight b
  suffices hn : ∀ z : ℂ, J z=0 → z=0 by
    intro z w h
    apply sub_eq_zero.mp
    apply hn
    rw [map_sub,h,sub_self]
  intro z hz
  have ha0 : inner ℝ a a≠0 := by
    intro h
    exact ha (inner_self_eq_zero.mp h)
  have hb0 : inner ℝ b b≠0 := by
    intro h
    exact hb (inner_self_eq_zero.mp h)
  have hba : inner ℝ b a=0 := by rwa [real_inner_comm]
  have hr := congrArg (fun v : E => inner ℝ a v) hz
  have hi := congrArg (fun v : E => inner ℝ b v) hz
  change inner ℝ a (z.re • a+z.im • b)=inner ℝ a 0 at hr
  change inner ℝ b (z.re • a+z.im • b)=inner ℝ b 0 at hi
  simp only [inner_add_right,inner_smul_right,hab,hba,mul_zero,zero_add,add_zero,inner_zero_right] at hr hi
  apply Complex.ext
  · exact (mul_eq_zero.mp hr).resolve_right ha0
  · exact (mul_eq_zero.mp hi).resolve_right hb0

lemma basis_sum_apply (v : Fin 3 → ℝ) (i : Fin 3) :
    (∑ r, v r • basis r : X) i=v i := by
  simp [basis,Pi.single_apply]

lemma null_re_im (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0) :
    (∑ i, (θ i).re*(θ i).re)=(∑ i, (θ i).im*(θ i).im) ∧
      (∑ i, (θ i).re*(θ i).im)=0 := by
  have hr := congrArg Complex.re hθ
  have hi := congrArg Complex.im hθ
  simp only [Complex.re_sum,Complex.mul_re,Complex.zero_re,Finset.sum_sub_distrib] at hr
  simp only [Complex.im_sum,Complex.mul_im,Complex.zero_im,Finset.sum_add_distrib] at hi
  have he : (∑ i, (θ i).im*(θ i).re)=(∑ i, (θ i).re*(θ i).im) :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [he] at hi
  constructor
  · exact sub_eq_zero.mp hr
  · linarith

lemma null_plane_injective (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0) (hne : θ≠0) :
    Function.Injective (characteristicPlane basis θ) := by
  obtain ⟨hre,him⟩ := null_re_im θ hθ
  let a : X := ∑ i, (θ i).re • basis i
  let b : X := ∑ i, (θ i).im • basis i
  have hai (i : Fin 3) : a i=(θ i).re := basis_sum_apply _ i
  have hbi (i : Fin 3) : b i=(θ i).im := basis_sum_apply _ i
  have haa : inner ℝ a a=∑ i, (θ i).re*(θ i).re := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hai]
  have hbb : inner ℝ b b=∑ i, (θ i).im*(θ i).im := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hbi]
  have hab : inner ℝ a b=0 := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hai,hbi]
    simpa only [mul_comm] using him
  have he : inner ℝ a a=inner ℝ b b := by rw [haa,hbb,hre]
  have hboth : ¬ (a=0 ∧ b=0) := by
    rintro ⟨ha,hb⟩
    apply hne
    funext i
    apply Complex.ext
    · simpa only [ha,PiLp.zero_apply,Pi.zero_apply,Complex.zero_re] using (hai i).symm
    · simpa only [hb,PiLp.zero_apply,Pi.zero_apply,Complex.zero_im] using (hbi i).symm
  have ha : a≠0 := by
    intro hz
    apply hboth
    refine ⟨hz,(@inner_self_eq_zero ℝ X _ _ _).mp ?_⟩
    rw [← he,hz,inner_zero_left]
  have hb : b≠0 := by
    intro hz
    apply ha
    apply (@inner_self_eq_zero ℝ X _ _ _).mp
    rw [he,hz,inner_zero_left]
  exact real_complex_plane_injective a b ha hb hab
end ElasticityParameter
namespace ElasticityAugmented
open scoped BigOperators

lemma thetaDerivation_apply (θ : Fin 3 → ℂ) (f : Smooth) :
    thetaDerivation θ f=direction (A := Smooth) coord θ f := by
  simp [thetaDerivation,direction,Fin.sum_univ_three]
end ElasticityAugmented

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_CommonFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators
namespace ElasticityAugmented
lemma smooth_sum_eval {ι : Type*} [Fintype ι] (f : ι → Smooth) (x : X) :
    ((∑ i,f i : Smooth) : X → ℂ) x=∑ i,(f i : X → ℂ) x := by
  exact map_sum ((Pi.evalRingHom (fun _ : X => ℂ) x).comp Smooth.val.toRingHom) f Finset.univ
end ElasticityAugmented

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Conic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators
namespace ElasticityParameter
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma commutator_flatten {R : Type*} [CommRing R]
    (M₂ M₁ G : n → n → R) (i j : n) :
    (∑ k, (M₂ i k*G k j-G i k*M₁ k j))=
      ∑ q : n × n, ((if q.2=j then M₂ i q.1 else 0)-
        (if q.1=i then M₁ q.2 j else 0))*G q.1 q.2 := by
  rw [Fintype.sum_prod_type]
  simp only [sub_mul,Finset.sum_sub_distrib,ite_mul,zero_mul]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [mul_comm]

end ElasticityParameter

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma matrixD_eval (θ : Fin 3 → ℂ) (G : Matrix n n Smooth) (x : X) (i j : n) :
    matrixEval x (matrixD θ G) i j=∑ r,θ r*fderiv ℝ (G i j : X → ℂ) x (ElasticityParameter.basis r) := by
  simp only [matrixEval_apply,matrixD,thetaDerivation_apply,direction,smooth_sum_eval,
    Subalgebra.coe_smul,Pi.smul_apply,smul_eq_mul]
  rfl

/-- The supported comparison is unique using the actual characteristic-plane
compact kernel theorem, not invertibility of the transferred frame. -/
theorem supported_matrix_unique_oai (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (M₀ M₁ G H : Matrix n n Smooth)
    (heG : matrixD θ G=M₁*G-G*M₀) (heH : matrixD θ H=M₁*H-H*M₀)
    (hc : ∀ i j,HasCompactSupport ((G i j-H i j : Smooth) : X → ℂ)) : G=H := by
  let a : (n × n) → (n × n) → X → ℂ := fun p q x =>
    (if q.2=p.2 then (M₁ p.1 q.1 : X → ℂ) x else 0)-
      (if q.1=p.1 then (M₀ q.2 p.2 : X → ℂ) x else 0)
  have ha (p q : n × n) : Continuous (a p q) := by
    have h1 : Continuous (fun x : X => if q.2=p.2 then (M₁ p.1 q.1 : X → ℂ) x else 0) := by
      split_ifs
      · exact (show ContDiff ℝ (⊤ : ℕ∞) (M₁ p.1 q.1 : X → ℂ) from (M₁ p.1 q.1).property).continuous
      · exact continuous_const
    have h0 : Continuous (fun x : X => if q.1=p.1 then (M₀ q.2 p.2 : X → ℂ) x else 0) := by
      split_ifs
      · exact (show ContDiff ℝ (⊤ : ℕ∞) (M₀ q.2 p.2 : X → ℂ) from (M₀ q.2 p.2).property).continuous
      · exact continuous_const
    exact h1.sub h0
  have he : matrixD θ (G-H)=M₁*(G-H)-(G-H)*M₀ := by
    have hd : matrixD θ (G-H)=matrixD θ G-matrixD θ H := by funext i j; exact map_sub _ _ _
    rw [hd,heG,heH]
    simp only [mul_sub,sub_mul]
    abel
  have hz := ElasticityPlanar.spatial_compact_kernel
    (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ)
    (ElasticityParameter.null_plane_injective θ hθ hne) a ha
    (fun p : n × n => ((G p.1 p.2-H p.1 p.2 : Smooth) : X → ℂ))
    (fun p => (G p.1 p.2-H p.1 p.2 : Smooth).property) (fun p => hc p.1 p.2)
    (fun p x => ?_)
  · ext i j x
    exact sub_eq_zero.mp (hz (i,j) x)
  · rw [ElasticityParameter.characteristicPlane_principal]
    have hh := congrArg (fun A : Matrix n n Smooth => matrixEval x A p.1 p.2) he
    rw [matrixD_eval] at hh
    simp only [map_sub,map_mul,Matrix.sub_apply,Matrix.mul_apply,← Finset.sum_sub_distrib] at hh
    exact hh.trans (ElasticityParameter.commutator_flatten (matrixEval x M₁) (matrixEval x M₀)
      (matrixEval x (G-H)) p.1 p.2)
end ElasticityAugmented

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElasticityAugmented.supported_matrix_unique_oai.{u_1} := @OAI.ElasticityAugmented.supported_matrix_unique_oai.{u_1}
