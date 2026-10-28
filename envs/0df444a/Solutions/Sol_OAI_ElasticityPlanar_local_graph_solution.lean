-- Prove2me | solution 1 for OAI.ElasticityPlanar.local_graph_solution
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:22:00.735892+00:00
-- url     : https://prove2.me/submissions/f3581a53-7772-40a0-9079-87b6c33cc459

import Mathlib
import Definitions.Def_OAIQ6El005

section
-- module Solutions.OAIQ6_Elast.Elasticity_Planar
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions _root_.OAI.ElasticityPlanar.graphComplete
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

/-- An actual weighted support estimate, independent of any frame existence. -/
theorem gaussian_coercivity (t : ℝ) (f : Test) :
    4 * t * mass f ≤ mass (B t f) := by
  have h := congrArg Complex.re (energy_identity t f)
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero, zero_mul, add_zero] at h
  change mass (B t f) - mass (C t f) = 4 * t * mass f at h
  linarith [mass_nonneg (C t f)]

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

end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory Complex Set
open scoped BigOperators

lemma normSq_add_le (z w : ℂ) :
    normSq (z+w) ≤ 2*normSq z+2*normSq w := by
  simp only [normSq_eq_norm_sq]
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le z w) 2
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

lemma mass_mul_bound (f g : Test) (K : ℝ)
    (hb : ∀ z, normSq (f z) ≤ K*normSq (g z)) : mass f ≤ K*mass g := by
  simpa using (mass_bound (n := Unit) f (fun _ => g) K (by simpa using hb))

/-- Quantitative Gaussian absorption for a system with no smallness of coefficients. -/
theorem weighted_inhomogeneous_bound {n : Type*} [Fintype n]
    (a : n → n → ℂ → ℂ) (u v : n → Test) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ z, (∃ j, u j z ≠ 0) → ∀ i, (∑ j, normSq (a i j z)) ≤ K)
    (heq : ∀ i z, (d 1 (u i)+I • d I (u i) : Test) z =
      v i z+∑ j, a i j z*u j z) :
    let t := (Fintype.card n : ℝ)*K+1
    (∑ i, mass (W t (u i))) ≤ ∑ i, mass (W t (v i)) := by
  classical
  dsimp only
  let t : ℝ := (Fintype.card n : ℝ)*K+1
  let w : n → Test := fun i => W t (u i)
  let f : n → Test := fun i => W t (v i)
  have hi (i : n) : mass (B t (w i)) ≤
      2*mass (f i)+2*K*∑ j, mass (w j) := by
    have hp (z : ℂ) : normSq ((B t (w i) : Test) z) ≤
        2*normSq (f i z)+2*K*∑ j, normSq (w j z) := by
      have he : (B t (w i) : Test) z=f i z+∑ j, a i j z*w j z := by
        dsimp [w,f]
        rw [gaussian_conjugation,W_apply,heq,mul_add,Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [he]
      apply (normSq_add_le _ _).trans
      have hm : normSq (∑ j, a i j z*w j z) ≤ K*∑ j, normSq (w j z) := by
        by_cases hu : ∃ j, u j z ≠ 0
        · exact (normSq_sum_mul (fun j => a i j z) (fun j => w j z)).trans
            (mul_le_mul_of_nonneg_right (hb z hu i)
              (Finset.sum_nonneg fun j _ => normSq_nonneg _))
        · have hw : ∀ j, w j z=0 := by
            intro j
            have hj : u j z=0 := by simpa using not_exists.mp hu j
            simp [w,hj]
          simp [hw]
      linarith
    rw [mass_integral,mass_integral]
    simp only [mass_integral]
    calc
      _ ≤ ∫ z : ℂ, (2*normSq (f i z)+2*K*∑ j, normSq (w j z)) :=
        integral_mono (integrable_normSq _) (((integrable_normSq _).const_mul 2).add
          ((integrable_finsetSum _ (fun j _ => integrable_normSq (w j))).const_mul _)) hp
      _ = _ := by
        rw [integral_add ((integrable_normSq _).const_mul 2)
          ((integrable_finsetSum _ (fun j _ => integrable_normSq (w j))).const_mul _),
          integral_const_mul,integral_const_mul,
          integral_finsetSum _ (fun j _ => integrable_normSq (w j))]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    (gaussian_coercivity t (w i)).trans (hi i))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul] at hs
  have hn : 0 ≤ (Fintype.card n : ℝ)*K := mul_nonneg (Nat.cast_nonneg _) hK
  have hw : 0 ≤ ∑ i, mass (w i) := Finset.sum_nonneg fun i _ => mass_nonneg _
  change (∑ i, mass (w i)) ≤ ∑ i, mass (f i)
  dsimp [t] at hs
  nlinarith [mul_nonneg hn hw]


lemma gaussian_inv (t : ℝ) (z : ℂ) : gaussian (-t) z*gaussian t z=1 := by
  rw [gaussian,gaussian,← Complex.exp_add]
  have h : (((-t : ℝ) : ℂ)/2)*(z*star z)+((t : ℂ)/2)*(z*star z)=0 := by
    push_cast
    ring
  rw [h,Complex.exp_zero]

lemma supported_weight_bound {S : Set ℂ} (hS : IsCompact S) (t : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ f : Test, tsupport (f : ℂ → ℂ) ⊆ S →
      mass (W t f) ≤ C*mass f := by
  have hc : Continuous (fun z => normSq (gaussian t z)) :=
    continuous_normSq.comp (smooth_gaussian t).continuous
  obtain ⟨K,hK⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max K 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro f hf
  apply mass_mul_bound
  intro z
  rw [W_apply,normSq_mul]
  by_cases hz : f z=0
  · simp [hz]
  · apply mul_le_mul_of_nonneg_right _ (normSq_nonneg _)
    exact (le_abs_self (normSq (gaussian t z))).trans
      ((hK z (hf (subset_tsupport _ hz))).trans (le_max_left _ _))

lemma supported_weight_equivalence {S : Set ℂ} (hS : IsCompact S) (t : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ f : Test, tsupport (f : ℂ → ℂ) ⊆ S →
      mass f ≤ C*mass (W t f) ∧ mass (W t f) ≤ C*mass f := by
  obtain ⟨C₁,hC₁,h₁⟩ := supported_weight_bound hS t
  obtain ⟨C₂,hC₂,h₂⟩ := supported_weight_bound hS (-t)
  refine ⟨max C₁ C₂,lt_of_lt_of_le hC₁ (le_max_left _ _),?_⟩
  intro f hf
  have hw : tsupport (W t f : ℂ → ℂ) ⊆ S :=
    (tsupport_mul_subset_right (f := gaussian t) (g := (f : ℂ → ℂ))).trans hf
  have he : W (-t) (W t f)=f := by
    apply Subtype.ext
    funext z
    change gaussian (-t) z*(gaussian t z*f z)=f z
    rw [← mul_assoc,gaussian_inv,one_mul]
  constructor
  · have hh := h₂ (W t f) hw
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (mass_nonneg _))
  · exact (h₁ f hf).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (mass_nonneg _))

lemma matrix_bound_on_compact {n : Type*} [Fintype n] {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, Continuous (a i j)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ S, ∀ i, (∑ j, normSq (a i j z)) ≤ K := by
  classical
  let F : ℂ → ℝ := fun z => ∑ i, ∑ j, normSq (a i j z)
  have hF : Continuous F := by dsimp [F]; fun_prop
  obtain ⟨K,hK⟩ := hS.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max K 0,le_max_right _ _,?_⟩
  intro z hz i
  calc
    _ ≤ F z := Finset.single_le_sum (fun k _ => Finset.sum_nonneg
      (fun j _ => normSq_nonneg _)) (Finset.mem_univ i)
    _ ≤ ‖F z‖ := le_abs_self _
    _ ≤ K := hK z hz
    _ ≤ max K 0 := le_max_left _ _

/-- A true unweighted supported L2 estimate, uniform over all test columns on a
fixed compact set, for an arbitrary continuous matrix coefficient. -/
theorem supported_inhomogeneous_L2 {n : Type*} [Fintype n]
    {S : Set ℂ} (hS : IsCompact S) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, Continuous (a i j)) :
    ∃ C : ℝ, 0<C ∧ ∀ u v : n → Test,
      (∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) →
      (∀ i, tsupport (v i : ℂ → ℂ) ⊆ S) →
      (∀ i z, (d 1 (u i)+I • d I (u i) : Test) z=v i z+∑ j, a i j z*u j z) →
      (∑ i, mass (u i)) ≤ C*∑ i, mass (v i) := by
  classical
  obtain ⟨K,hK,hb⟩ := matrix_bound_on_compact hS a ha
  let t : ℝ := (Fintype.card n : ℝ)*K+1
  obtain ⟨C,hC,hW⟩ := supported_weight_equivalence hS t
  refine ⟨C*C,mul_pos hC hC,?_⟩
  intro u v hu hv heq
  have hbound : ∀ z, (∃ j, u j z ≠ 0) → ∀ i, (∑ j, normSq (a i j z)) ≤ K := by
    intro z hz
    obtain ⟨j,hj⟩ := hz
    exact hb z (hu j (subset_tsupport _ hj))
  have hw := weighted_inhomogeneous_bound a u v K hK hbound heq
  change (∑ i, mass (W t (u i))) ≤ ∑ i, mass (W t (v i)) at hw
  calc
    _ ≤ ∑ i, C*mass (W t (u i)) := Finset.sum_le_sum fun i _ => (hW _ (hu i)).1
    _ = C*∑ i, mass (W t (u i)) := (Finset.mul_sum ..).symm
    _ ≤ C*∑ i, mass (W t (v i)) := mul_le_mul_of_nonneg_left hw hC.le
    _ ≤ C*(C*∑ i, mass (v i)) := mul_le_mul_of_nonneg_left (by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => (hW _ (hv i)).2) hC.le
    _ = _ := by ring

end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory Complex Set
open scoped SchwartzMap ENNReal BigOperators

lemma inner_L2 (f g : Test) : inner ℂ (L2 f) (L2 g)=pair f g := by
  simpa only [L2,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,SchwartzMap.toLpCLM_apply,
    RCLike.inner_apply',RCLike.star_def,toSchwartz_apply,pair] using
    SchwartzMap.inner_toL2_toL2_eq (toSchwartz f) (toSchwartz g) volume
lemma norm_L2_sq (f : Test) : ‖L2 f‖^2=mass f := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ),inner_L2]
  rfl

variable {n : Type*}
variable [Fintype n]
lemma norm_embed_sq (u : n → Test) : ‖embed u‖^2=∑ i, mass (u i) := by
  rw [PiLp.norm_eq_of_L2,Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact Finset.sum_congr rfl (fun i _ => norm_L2_sq (u i))

lemma transport_supported {S : Set ℂ} (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) (u : n → Test)
    (hu : ∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) :
    ∀ i, tsupport (transport a ha u i : ℂ → ℂ) ⊆ S := by
  intro i
  apply (tsupport_add _ _).trans
  apply Set.union_subset
  · apply (tsupport_add _ _).trans
    apply Set.union_subset
    · exact (tsupport_fderiv_apply_subset ℝ _).trans (hu i)
    · exact (tsupport_smul_subset_right (fun _ : ℂ => (I : ℂ)) (d I (u i) : ℂ → ℂ)).trans ((tsupport_fderiv_apply_subset ℝ I).trans (hu i))
  · have hsum (s : Finset n) : tsupport ((∑ j ∈ s, mulSmooth (a i j) (ha i j) (u j) : Test) : ℂ → ℂ) ⊆ S := by
      classical
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty,Submodule.coe_zero,tsupport_zero,Set.empty_subset]
      | @insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact (tsupport_add _ _).trans (Set.union_subset ((tsupport_mul_subset_right).trans (hu j)) ih)
    exact hsum Finset.univ

/-- A true L2 lower bound for the actual transport operator. -/
theorem supported_transport_estimate {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) :
    ∃ C : ℝ, 0<C ∧ ∀ u : n → Test, (∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) →
      ‖embed u‖ ≤ C*‖embed (transport a ha u)‖ := by
  obtain ⟨C,hC,hest⟩ := supported_inhomogeneous_L2 hS (fun i j z => -(a i j z)) (fun i j => (ha i j).continuous.neg)
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,fun u hu => ?_⟩
  have heq : ∀ i z, (d 1 (u i)+I • d I (u i) : Test) z =
      transport a ha u i z+∑ j, -(a i j z)*u j z := by
    intro i z
    change _ = (d 1 (u i)+I • d I (u i) : Test) z+(∑ j, mulSmooth (a i j) (ha i j) (u j) : Test) z+_
    simp only [Submodule.coe_sum,Finset.sum_apply,mulSmooth,LinearMap.coe_mk,AddHom.coe_mk,
      Finset.sum_neg_distrib,neg_mul]
    ring
  have h := hest u (transport a ha u) hu (transport_supported a ha u hu) heq
  rw [← norm_embed_sq,← norm_embed_sq] at h
  have hs := Real.sq_sqrt hC.le
  have hp : 0 ≤ Real.sqrt C*‖embed (transport a ha u)‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (embed u)]
end ElasticityPlanar

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Parameters
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators Manifold
namespace ElasticityRegularity
variable {P E F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
lemma complex_clm_apply_smooth {f : P → E →L[ℂ] F} {g : P → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => f p (g p)) :=
  ((ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ).contDiff.comp hf).clm_apply hg
omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
lemma complex_clm_comp_smooth {f : P → F →L[ℂ] G} {g : P → E →L[ℂ] F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => (f p).comp (g p)) := by
  let C := ContinuousLinearMap.compL ℂ E F G
  exact complex_clm_apply_smooth ((C.restrictScalars ℝ).contDiff.comp hf) hg
end ElasticityRegularity

end

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Supported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/- The exact extension proofs are reused from their canonical original module. -/

namespace ElasticityGraph
open Set
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
/-- Orthogonal projection supplies a genuine bounded left inverse of a
coercive Hilbert operator on all of the target space. -/
theorem exists_coercive_left_inverse (A : E →L[ℂ] F) (C : ℝ) (hC : 0≤C)
    (hA : ∀ x, ‖x‖≤C*‖A x‖) :
    ∃ R : F →L[ℂ] E, R.comp A=ContinuousLinearMap.id ℂ E := by
  have hal : AntilipschitzWith ⟨C,hC⟩ A := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    change dist x y≤C*dist (A x) (A y)
    simpa only [dist_eq_norm,← map_sub] using hA (x-y)
  have hclosed : IsClosed (Set.range A) := hal.isClosed_range A.uniformContinuous
  let e : E ≃L[ℂ] A.range := A.equivRange hal.injective hclosed
  let : CompleteSpace A.range := hclosed.completeSpace_coe
  let R : F →L[ℂ] E := e.symm.toContinuousLinearMap.comp A.range.orthogonalProjectionOnto
  refine ⟨R,?_⟩
  ext x
  change e.symm (A.range.orthogonalProjectionOnto (A x))=x
  have hx : A.range.orthogonalProjectionOnto (A x)=e x :=
    A.range.orthogonalProjectionOnto_mem_subspace_eq_self (e x)
  rw [hx,ContinuousLinearEquiv.symm_apply_apply]
end ElasticityGraph
namespace ElasticityGraph
open Set
open ElasticityRegularity
variable {E F P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

  [NormedAddCommGroup P] [NormedSpace ℝ P]
local instance instNormedSpaceReal_solutions_ra7502e_1 : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
attribute [local instance] OAI.ElasticityGraph.instNormedSpaceReal_solutions_1
/-- A smooth local left inverse, with no surjectivity hypothesis. -/
theorem local_smooth_left_inverse (A : P → E →L[ℂ] F)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (p₀ : P) (C : ℝ) (hC : 0≤C)
    (hbound : ∀ x, ‖x‖≤C*‖A p₀ x‖) :
    ∃ (U : Set P) (R : P → F →L[ℂ] E), IsOpen U ∧ p₀∈U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) R U ∧ ∀ p∈U, (R p).comp (A p)=ContinuousLinearMap.id ℂ E := by
  obtain ⟨R₀,hR₀⟩ := exists_coercive_left_inverse (A p₀) C hC hbound
  let B : P → E →L[ℂ] E := fun p => R₀.comp (A p-A p₀)
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := complex_clm_comp_smooth contDiff_const (hA.sub contDiff_const)
  let U : Set P := {p | ‖B p‖<1}
  have hopen : IsOpen U := isOpen_lt hB.continuous.norm continuous_const
  have hmem : p₀∈U := by simp only [U,B,mem_ofPred_eq,sub_self,ContinuousLinearMap.comp_zero,norm_zero,zero_lt_one]
  let R : P → F →L[ℂ] E := fun p => (Ring.inverse (1+B p)).comp R₀
  have hu (p : P) (hp : p∈U) : IsUnit (1+B p) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one
      (by simpa only [norm_neg] using (show ‖B p‖<1 from hp) : ‖-(B p)‖<1)
  have hi (p : P) (hp : p∈U) : ContDiffAt ℝ (⊤ : ℕ∞) (fun q => Ring.inverse (1+B q)) p := by
    obtain ⟨v,hv⟩ := hu p hp
    have hInv : ContDiffAt ℝ (⊤ : ℕ∞) Ring.inverse (1+B p) := by
      rw [← hv]
      exact contDiffAt_ringInverse ℝ v
    exact hInv.comp p (contDiffAt_const.add hB.contDiffAt)
  have hR : ContDiffOn ℝ (⊤ : ℕ∞) R U := by
    intro p hp
    let L : (E →L[ℂ] E) →L[ℂ] (F →L[ℂ] E) := (ContinuousLinearMap.compL ℂ F E E).flip R₀
    exact ((L.restrictScalars ℝ).contDiff.contDiffAt.comp p (hi p hp)).contDiffWithinAt
  refine ⟨U,R,hopen,hmem,hR,fun p hp => ?_⟩
  have hRA : R₀.comp (A p)=1+B p := by
    dsimp [B]
    rw [ContinuousLinearMap.comp_sub,hR₀]
    change R₀.comp (A p)=ContinuousLinearMap.id ℂ E+(R₀.comp (A p)-ContinuousLinearMap.id ℂ E)
    abel
  change (Ring.inverse (1+B p)).comp (R₀.comp (A p))=1
  rw [hRA]
  exact Ring.inverse_mul_cancel _ (hu p hp)

/-- Smooth dependence and existence at all parameters follow from existence
on a dense set, using the actual local Hilbert left inverse. -/
theorem local_smooth_solution_of_dense (A : P → E →L[ℂ] F)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (f : P → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {D : Set P} (hD : Dense D) (hex : ∀ p∈D, ∃ u, A p u=f p)
    (p₀ : P) (C : ℝ) (hC : 0≤C) (hbound : ∀ x, ‖x‖≤C*‖A p₀ x‖) :
    ∃ (U : Set P) (u : P → E), IsOpen U ∧ p₀∈U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) u U ∧ ∀ p∈U, A p (u p)=f p := by
  obtain ⟨U,R,hU,hp,hR,he⟩ := local_smooth_left_inverse A hA p₀ C hC hbound
  let u : P → E := fun p => R p (f p)
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) u U :=
    (((ContinuousLinearMap.restrictScalarsL ℂ F E ℝ ℝ).contDiff.comp_contDiffOn hR).clm_apply hf.contDiffOn)
  have hr : ContinuousOn (fun p => A p (u p)) U :=
    (((ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ).contDiff.comp hA).contDiffOn.clm_apply hu).continuousOn
  have hdense : EqOn (fun p => A p (u p)) f (U∩D) := by
    intro p hp
    obtain ⟨v,hv⟩ := hex p hp.2
    have hl := congrArg (fun L : E →L[ℂ] E => L v) (he p hp.1)
    change R p (A p v)=v at hl
    dsimp [u]
    rw [← hv,hl]
  exact ⟨U,u,hU,hp,hu,hdense.of_subset_closure hr hf.continuous.continuousOn
    inter_subset_left (hD.open_subset_closure_inter hU)⟩
end ElasticityGraph
namespace ElasticityPlanar
open Set MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators

section
variable {n : Type*} [Fintype n]

/-- The positive-commutator coercivity survives the actual graph closure. -/
theorem closed_graph_estimate {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) :
    ∃ C : ℝ, 0<C ∧ ∀ u : closedGraph S a ha,
      ‖u‖≤C*‖graphSecond S a ha u‖ := by
  obtain ⟨C,hC,hest⟩ := supported_transport_estimate hS a ha
  have hcl : ∀ u : closedGraph S a ha, ‖graphFirst S a ha u‖≤C*‖graphSecond S a ha u‖ := by
    intro u
    have hclosed : IsClosed {v : GraphSpace n | ‖v.fst‖≤C*‖v.snd‖} :=
      isClosed_le (WithLp.fstL 2 ℂ (Hilbert n) (Hilbert n)).continuous.norm
        (continuous_const.mul (WithLp.sndL 2 ℂ (Hilbert n) (Hilbert n)).continuous.norm)
    have hincl : (testGraph S a ha).range ≤
        {v : GraphSpace n | ‖v.fst‖≤C*‖v.snd‖} := by
      rintro v ⟨w,rfl⟩
      exact hest w w.property
    exact closure_minimal hincl hclosed u.property
  refine ⟨C+1,by linarith,fun u => ?_⟩
  have h := hcl u
  have hn := WithLp.prod_norm_sq_eq_of_L2 (u : GraphSpace n)
  change ‖u‖^2=‖graphFirst S a ha u‖^2+‖graphSecond S a ha u‖^2 at hn
  have hp : 0≤C*‖graphSecond S a ha u‖ := mul_nonneg hC.le (norm_nonneg _)
  have hsq := sq_le_sq₀ (norm_nonneg (graphFirst S a ha u)) hp |>.mpr h
  have hx := norm_nonneg u
  have hy := norm_nonneg (graphSecond S a ha u)
  nlinarith [sq_nonneg (C*‖graphSecond S a ha u‖),mul_nonneg hC.le (sq_nonneg ‖graphSecond S a ha u‖)]
end
open ElasticityRegularity
end ElasticityPlanar
namespace ElasticityPlanar
open Set MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [FiniteDimensional ℝ P] in
lemma local_graph_solution_oai {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (A : P → closedGraph S a ha →L[ℂ] Hilbert n)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (p₀ : P) (hA₀ : A p₀=graphSecond S a ha)
    (f : P → Hilbert n) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {D : Set P} (hD : Dense D) (hex : ∀ p∈D, ∃ u : closedGraph S a ha, A p u=f p) :
    ∃ (U : Set P) (u : P → closedGraph S a ha), IsOpen U ∧ p₀∈U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) u U ∧ ∀ p∈U, A p (u p)=f p := by
  obtain ⟨C,hC,hbound⟩ := closed_graph_estimate hS a ha
  exact ElasticityGraph.local_smooth_solution_of_dense (E := closedGraph S a ha) (F := Hilbert n) A hA f hf hD hex p₀ C hC.le
    (fun x => by rw [hA₀]; exact hbound x)

end ElasticityPlanar

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ElasticityPlanar.local_graph_solution_oai.{u_1, u_2} := @OAI.ElasticityPlanar.local_graph_solution_oai.{u_1, u_2}
