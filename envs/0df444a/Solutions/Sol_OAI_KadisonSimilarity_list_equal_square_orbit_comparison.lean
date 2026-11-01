-- Prove2me | solution 1 for OAI.KadisonSimilarity.list_equal_square_orbit_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T14:45:59.11186+00:00
-- url     : https://prove2.me/submissions/3f916aea-9418-4519-8020-dc761c2ead4f

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A030

section
-- module Solutions.OAIQ075_KS.Compat
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
open scoped ComplexOrder in
/-- A norm-one functional on a C⋆-algebra with `φ 1 = 1` is monotone; stands in for d13f23b's
`ContinuousLinearMap.monotone_iff_opNorm_eq_map_one` (Kadison similarity, oaiq-075). -/
theorem monotone_of_opNorm_eq_one_of_apply_one {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Nontrivial A] (φ : A →L[ℂ] ℂ) (hn : ‖φ‖ = 1) (h1 : φ 1 = 1) :
    Monotone φ := by
  have hle : ∀ z : A, ‖φ z‖ ≤ ‖z‖ := fun z => by
    simpa [hn] using φ.le_opNorm z
  -- selfadjoint elements have real values
  have him : ∀ h : A, IsSelfAdjoint h → (φ h).im = 0 := by
    intro h hh
    by_contra hy
    set y := (φ h).im with hy_def
    set x := (φ h).re with hx_def
    set C : ℝ := x ^ 2 + y ^ 2 - ‖h‖ ^ 2 with hC
    have hD : 0 < |C| + 1 := by positivity
    set t : ℝ := -y / (|C| + 1) with ht
    set z : A := (1 : A) + ((t : ℂ) * Complex.I) • h with hz
    have hzz : star z * z = (1 : A) + ((t ^ 2 : ℝ) : ℂ) • (h * h) := by
      have hs : star ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by
        simp [Complex.conj_ofReal]
      have ht2 : ((t ^ 2 : ℝ) : ℂ) = -(((t : ℂ) * Complex.I) * ((t : ℂ) * Complex.I)) := by
        push_cast; ring_nf; simp [Complex.I_sq]
      rw [ht2]
      simp only [hz, star_add, star_one, star_smul, hh.star_eq, hs, add_mul, mul_add, one_mul, mul_one,
        smul_mul_assoc, mul_smul_comm, smul_smul, neg_smul, smul_neg, neg_mul, smul_add]
      module
    have hnz : ‖z‖ ^ 2 ≤ 1 + t ^ 2 * ‖h‖ ^ 2 := by
      have h0 : ‖z‖ * ‖z‖ = ‖star z * z‖ := (CStarRing.norm_star_mul_self).symm
      rw [sq, h0, hzz]
      calc ‖(1 : A) + ((t ^ 2 : ℝ) : ℂ) • (h * h)‖ ≤ ‖(1 : A)‖ + ‖((t ^ 2 : ℝ) : ℂ) • (h * h)‖ := norm_add_le _ _
        _ ≤ 1 + t ^ 2 * (‖h‖ * ‖h‖) := by
          rw [norm_one, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
          gcongr
          exact norm_mul_le _ _
        _ = 1 + t ^ 2 * ‖h‖ ^ 2 := by ring
    have hphiz : φ z = (1 - t * y : ℝ) + (t * x : ℝ) * Complex.I := by
      have hh' : φ h = (x : ℂ) + (y : ℂ) * Complex.I := (Complex.re_add_im (φ h)).symm
      rw [hz, map_add, map_smul, h1, smul_eq_mul, hh']
      apply Complex.ext <;> simp <;> ring
    have hphin : ‖φ z‖ ^ 2 = (1 - t * y) ^ 2 + (t * x) ^ 2 := by
      rw [hphiz, Complex.sq_norm, Complex.normSq_apply]
      simp; ring
    have hineq : (1 - t * y) ^ 2 + (t * x) ^ 2 ≤ 1 + t ^ 2 * ‖h‖ ^ 2 := by
      rw [← hphin]
      exact (pow_le_pow_left₀ (norm_nonneg _) (hle z) 2).trans hnz
    have hkey : y ^ 2 * (C + 2 * (|C| + 1)) ≤ 0 := by
      have e1 : t * (|C| + 1) = -y := by rw [ht]; field_simp
      have : t ^ 2 * C - 2 * t * y ≤ 0 := by rw [hC]; nlinarith [hineq]
      have h3 : (t * (|C| + 1)) ^ 2 * C - 2 * (t * (|C| + 1)) * y * (|C| + 1) ≤ 0 := by
        have := mul_nonneg (le_of_lt (pow_pos hD 2)) (neg_nonneg.mpr this)
        nlinarith [this]
      rw [e1] at h3
      nlinarith [h3]
    have hCpos : 0 < C + 2 * (|C| + 1) := by
      have := neg_abs_le C
      linarith
    have hy2 : y ^ 2 ≤ 0 := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_pos hcon hCpos]
    exact hy (by nlinarith [sq_nonneg y])
  -- nonnegative elements have nonnegative values
  have hpos : ∀ c : A, 0 ≤ c → 0 ≤ φ c := by
    intro c hc
    have hsa : IsSelfAdjoint c := IsSelfAdjoint.of_nonneg hc
    have hre := him c hsa
    set r : ℝ := ‖c‖ with hr
    have hcr : c ≤ algebraMap ℝ A r := hsa.le_algebraMap_norm_self
    have hnn : 0 ≤ algebraMap ℝ A r - c := sub_nonneg.mpr hcr
    have hle2 : algebraMap ℝ A r - c ≤ algebraMap ℝ A r := sub_le_self _ hc
    have hnorm : ‖algebraMap ℝ A r - c‖ ≤ r := by
      refine (CStarAlgebra.norm_le_norm_of_nonneg_of_le hnn hle2).trans ?_
      rw [Algebra.algebraMap_eq_smul_one, norm_smul, norm_one, mul_one, Real.norm_eq_abs, hr]
      exact le_of_eq (abs_of_nonneg (norm_nonneg _))
    have hphi : φ (algebraMap ℝ A r - c) = (r : ℂ) - φ c := by
      rw [map_sub, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul, h1]
      simp
    have hb := (hle _).trans hnorm
    rw [hphi] at hb
    have hx : φ c = ((φ c).re : ℂ) := by
      apply Complex.ext <;> simp [hre]
    rw [hx] at hb
    have : ‖(r : ℂ) - ((φ c).re : ℂ)‖ = |r - (φ c).re| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [this] at hb
    have := (abs_le.mp hb).2
    rw [Complex.nonneg_iff]
    exact ⟨by linarith, by simp [hre]⟩
  intro a b hab
  have := hpos (b - a) (sub_nonneg.mpr hab)
  rw [map_sub] at this
  exact sub_nonneg.mp this
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_DicksonAdjoint
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The adjoint homomorphism and the exact row-to-column transfer. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every pointwise operator bound is preserved by the sharp operation. -/
theorem sharpHom_bound (π : BoundedUnitalHom A H) {C : ℝ}
    (hπ : ∀ a, ‖π.1 a‖ ≤ C * ‖a‖) (a : A) :
    ‖(sharpHom π).1 a‖ ≤ C * ‖a‖ := by
  simpa only [sharpHom_apply, norm_star] using hπ (star a)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_RegularizedPolarFactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contractive approximate polar factors inside the original C-star algebra.
These avoid any bidual extension in the row-bound argument. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem positiveShiftReciprocal_continuous (h : A) (hh : 0 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun t : ℝ => (t + ε)⁻¹) (spectrum ℝ h) := by
  apply ContinuousOn.inv₀ (by fun_prop)
  intro t ht
  exact ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hh ht) hε)

omit [PartialOrder A] [StarOrderedRing A] in
theorem positiveShiftReciprocal_selfAdjoint (h : A) (ε : ℝ) :
    IsSelfAdjoint (positiveShiftReciprocal h ε) := cfc_predicate _ h

omit [PartialOrder A] [StarOrderedRing A] in
theorem positiveShiftReciprocal_commute (h : A) (ε : ℝ) :
    Commute (positiveShiftReciprocal h ε) h := (Commute.refl h).cfc_real _

theorem positiveShiftReciprocal_inverse (h : A) (hh : 0 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    (h + ε • (1 : A)) * positiveShiftReciprocal h ε = 1 := by
  have hc := positiveShiftReciprocal_continuous h hh hε
  have hid : cfc (fun t : ℝ => t + ε) h = h + ε • (1 : A) := by
    rw [cfc_add h (fun t : ℝ => t) (fun _ => ε) continuousOn_id continuousOn_const,
      cfc_id' ℝ h hh.isSelfAdjoint, cfc_const ε h hh.isSelfAdjoint]
    simp only [Algebra.algebraMap_eq_smul_one]
  rw [positiveShiftReciprocal, ← hid, ← cfc_mul _ _ h (by fun_prop) hc]
  calc
    cfc (fun t : ℝ => (t + ε) * (t + ε)⁻¹) h = cfc (fun _ : ℝ => 1) h := by
      apply cfc_congr
      intro t ht
      exact mul_inv_cancel₀ (ne_of_gt
        (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hh ht) hε))
    _ = 1 := cfc_const_one ℝ h hh.isSelfAdjoint

theorem positiveShiftReciprocal_mul_norm_le (h : A) (hh : 0 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    ‖h * positiveShiftReciprocal h ε‖ ≤ 1 := by
  have hc := positiveShiftReciprocal_continuous h hh hε
  change ‖h * cfc (fun t : ℝ => (t + ε)⁻¹) h‖ ≤ 1
  conv_lhs => arg 1; arg 1; rw [← cfc_id' ℝ h hh.isSelfAdjoint]
  rw [← cfc_mul (fun t : ℝ => t) (fun t : ℝ => (t + ε)⁻¹) h continuousOn_id hc]
  apply norm_cfc_le zero_le_one
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg hh ht
  have hp : 0 < t + ε := add_pos_of_nonneg_of_pos ht0 hε
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 (inv_nonneg.mpr hp.le))]
  change t / (t + ε) ≤ 1
  exact (div_le_one hp).mpr (by linarith)

/-- The regularized polar factor is contractive without leaving the algebra. -/
theorem norm_positiveShiftReciprocal_mul_le (x h : A) (hh : 0 ≤ h)
    (hsq : x * star x = h * h) {ε : ℝ} (hε : 0 < ε) :
    ‖positiveShiftReciprocal h ε * x‖ ≤ 1 := by
  let r := positiveShiftReciprocal h ε
  have hr : star r = r := (positiveShiftReciprocal_selfAdjoint h ε).star_eq
  have hc : r * h = h * r := (positiveShiftReciprocal_commute h ε).eq
  have he : (r * x) * star (r * x) = (h * r) * (h * r) := by
    rw [star_mul, hr]
    calc
      (r * x) * (star x * r) = r * (x * star x) * r := by noncomm_ring
      _ = r * (h * h) * r := by rw [hsq]
      _ = (r * h) * (h * r) := by noncomm_ring
      _ = (h * r) * (h * r) := by rw [hc]
  have hsa : IsSelfAdjoint (h * r) :=
    (hh.isSelfAdjoint.commute_iff (positiveShiftReciprocal_selfAdjoint h ε)).mp
      (positiveShiftReciprocal_commute h ε).symm
  have heq : ‖r * x‖ ^ 2 = ‖h * r‖ ^ 2 := by
    rw [sq, ← CStarRing.norm_self_mul_star, he, hsa.norm_mul_self]
  have hn := positiveShiftReciprocal_mul_norm_le h hh hε
  nlinarith [norm_nonneg (r * x), norm_nonneg (h * r)]

/-- The error in the polar factorization has norm at most the regularizer. -/
theorem regularizedPolar_error (x h : A) (hh : 0 ≤ h)
    (hsq : x * star x = h * h) {ε : ℝ} (hε : 0 < ε) :
    ‖x - h * (positiveShiftReciprocal h ε * x)‖ ≤ ε := by
  let v := positiveShiftReciprocal h ε * x
  have hi := congrArg (fun z : A => z * x) (positiveShiftReciprocal_inverse h hh hε)
  have he : x - h * v = ε • v := by
    change (h + ε • (1 : A)) * positiveShiftReciprocal h ε * x = 1 * x at hi
    simp only [add_mul, smul_mul_assoc, one_mul, mul_assoc] at hi
    change h * v + ε • v = x at hi
    rw [← hi]
    abel
  change ‖x - h * v‖ ≤ ε
  rw [he, norm_smul, Real.norm_of_nonneg hε.le]
  exact (mul_le_mul_of_nonneg_left
    (norm_positiveShiftReciprocal_mul_le x h hh hsq hε) hε.le).trans_eq (mul_one ε)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_HomPolarBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.boundedHomOrbit_apply _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.listOrbitSum_append _root_.OAI.KadisonSimilarity.listOrbitSum_nil _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.sharpVectorMap_apply _root_.OAI.KadisonSimilarity.similarityRepresentation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polar estimate for a bounded homomorphism, proved with approximate
polar factors in the source algebra. -/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Approximate polar factorization transfers to an adjoint-vector estimate. -/
theorem hom_adjoint_polar_bound (π : BoundedUnitalHom A H) {M : ℝ} (hM : 0 ≤ M)
    (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖) (x h : A) (hh : 0 ≤ h)
    (hsq : x * star x = h * h) (ξ : H) :
    ‖(π.1 x).adjoint ξ‖ ≤ M * ‖(π.1 h).adjoint ξ‖ := by
  have happrox (ε : ℝ) (hε : 0 < ε) :
      ‖(π.1 x).adjoint ξ‖ ≤ M * ‖(π.1 h).adjoint ξ‖ + (M * ‖ξ‖) * ε := by
    let v := positiveShiftReciprocal h ε * x
    let e := x - h * v
    have hv : ‖π.1 v‖ ≤ M :=
      (hπ v).trans ((mul_le_mul_of_nonneg_left
        (norm_positiveShiftReciprocal_mul_le x h hh hsq hε) hM).trans_eq (mul_one M))
    have he : ‖π.1 e‖ ≤ M * ε :=
      (hπ e).trans (mul_le_mul_of_nonneg_left (regularizedPolar_error x h hh hsq hε) hM)
    have hx : x = h * v + e := by dsimp [e]; abel
    have hid : (π.1 x).adjoint ξ =
        (π.1 v).adjoint ((π.1 h).adjoint ξ) + (π.1 e).adjoint ξ := by
      conv_lhs => rw [hx, map_add, map_mul]
      simp only [← star_eq_adjoint, star_add, star_mul, add_apply, mul_apply_eq_comp]
    rw [hid]
    calc
      _ ≤ ‖(π.1 v).adjoint ((π.1 h).adjoint ξ)‖ + ‖(π.1 e).adjoint ξ‖ := norm_add_le _ _
      _ ≤ ‖π.1 v‖ * ‖(π.1 h).adjoint ξ‖ + ‖π.1 e‖ * ‖ξ‖ := by
        exact add_le_add
          (by simpa only [adjoint.norm_map] using
            (π.1 v).adjoint.le_opNorm ((π.1 h).adjoint ξ))
          (by simpa only [adjoint.norm_map] using (π.1 e).adjoint.le_opNorm ξ)
      _ ≤ M * ‖(π.1 h).adjoint ξ‖ + (M * ε) * ‖ξ‖ := by gcongr
      _ = _ := by ring
  apply le_of_forall_pos_le_add
  intro δ hδ
  let C := M * ‖ξ‖
  have hC : 0 ≤ C := mul_nonneg hM (norm_nonneg ξ)
  have hden : 0 < C + 1 := by positivity
  have heps : 0 < δ / (C + 1) := div_pos hδ hden
  refine (happrox (δ / (C + 1)) heps).trans ?_
  apply add_le_add (le_refl _)
  change C * (δ / (C + 1)) ≤ δ
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hden).mpr
  nlinarith

/-- The positive square root of `xx*` is enough; a polar partial isometry
or an extension of the homomorphism to a bidual is unnecessary. -/
theorem hom_adjoint_sqrt_bound (π : BoundedUnitalHom A H) {M : ℝ} (hM : 0 ≤ M)
    (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖) (x : A) (ξ : H) :
    ‖(π.1 x).adjoint ξ‖ ≤ M * ‖(π.1 (CFC.sqrt (x * star x))).adjoint ξ‖ := by
  exact hom_adjoint_polar_bound π hM hπ x _ (CFC.sqrt_nonneg _)
    (CFC.sqrt_mul_sqrt_self _ (mul_star_self_nonneg x)).symm ξ

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_NormAttainingGrothendieck
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm-attaining case of the little Grothendieck inequality.
The unitary paths and their quadratic estimates are constructed explicitly. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- At a norm-attaining unit, the supporting vector functional is a state. -/
theorem exists_normAttainingState (T : A →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (h1 : ‖T 1‖ = 1) :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ ∀ a, f a = inner ℂ (T 1) (T a) := by
  let φ : A →L[ℂ] ℂ := (innerSL ℂ (T 1)).comp T
  have hφ1 : φ 1 = 1 := by
    change inner ℂ (T 1) (T 1) = 1
    rw [inner_self_eq_norm_sq_to_K, h1]
    norm_num
  have hnle : ‖φ‖ ≤ 1 := by
    calc
      _ ≤ ‖innerSL ℂ (T 1)‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖T‖ := by rw [innerSL_apply_norm, h1, one_mul]
      _ ≤ 1 := hT
  have hn : ‖φ‖ = 1 := by
    apply le_antisymm hnle
    simpa only [hφ1, norm_one, mul_one] using φ.le_opNorm (1 : A)
  have hm : Monotone φ := OAI.monotone_of_opNorm_eq_one_of_apply_one φ hn hφ1
  let f : A →ₚ[ℂ] ℂ := { φ.toLinearMap with monotone' := hm }
  exact ⟨f, hφ1, fun _ => rfl⟩

/-- The two conjugate unitary paths give a quadratic contraction estimate. -/
theorem contraction_sqrt_complement (T : A →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (a : A) (ha : IsSelfAdjoint a) (hna : ‖a‖ ≤ 1) :
    ‖T a‖ ^ 2 + ‖T (CFC.sqrt (1 - a ^ 2))‖ ^ 2 ≤ 1 := by
  let r := CFC.sqrt (1 - a ^ 2)
  have hu : a + Complex.I • r ∈ unitary A :=
    ha.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary a hna
  have hv : a - Complex.I • r ∈ unitary A := by
    have hstar := Unitary.star_mem hu
    have hr : star r = r := (CFC.sqrt_nonneg (1 - a ^ 2)).star_eq
    simpa only [star_add, star_smul, ha.star_eq, Complex.star_def, map_add,
      Complex.conj_I, hr, neg_smul,
      ← sub_eq_add_neg] using hstar
  have hplus : ‖T (a + Complex.I • r)‖ ≤ 1 := by
    exact (T.le_opNorm _).trans (by rw [CStarRing.norm_of_mem_unitary hu, mul_one]; exact hT)
  have hminus : ‖T (a - Complex.I • r)‖ ≤ 1 := by
    exact (T.le_opNorm _).trans (by rw [CStarRing.norm_of_mem_unitary hv, mul_one]; exact hT)
  have hpar := parallelogram_law_with_norm ℂ (T a) (Complex.I • T r)
  have hi : ‖Complex.I • T r‖ = ‖T r‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  rw [hi] at hpar
  have hp : ‖T a + Complex.I • T r‖ ≤ 1 := by simpa only [map_add, map_smul] using hplus
  have hm : ‖T a - Complex.I • T r‖ ≤ 1 := by simpa only [map_sub, map_smul] using hminus
  have hp2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  have hm2 := pow_le_pow_left₀ (norm_nonneg _) hm 2
  change ‖T a‖ ^ 2 + ‖T r‖ ^ 2 ≤ 1
  nlinarith

/-- A scalar square-root expansion with a uniform quadratic remainder. -/
theorem sqrt_complement_remainder (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    |1 - Real.sqrt (1 - s) - s / 2| ≤ s ^ 2 := by
  have hr : 0 ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
  have hr2 : Real.sqrt (1 - s) ^ 2 = 1 - s := Real.sq_sqrt (by linarith)
  have hr1 : Real.sqrt (1 - s) ≤ 1 := by nlinarith
  have hd : 0 ≤ 1 - Real.sqrt (1 - s) := by linarith
  have hdle : 1 - Real.sqrt (1 - s) ≤ s := by
    nlinarith
  have he : 1 - Real.sqrt (1 - s) - s / 2 = (1 - Real.sqrt (1 - s)) ^ 2 / 2 := by
    nlinarith
  rw [he, abs_of_nonneg (by positivity)]
  have hsq := pow_le_pow_left₀ hd hdle 2
  nlinarith [sq_nonneg s]

omit [PartialOrder A] [StarOrderedRing A] in
theorem norm_cfcSqrtRemainder_le (a : A) (hna : ‖a‖ ≤ 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) : ‖cfcSqrtRemainder a t‖ ≤ t ^ 4 := by
  apply norm_cfc_le (by positivity)
  intro x hx
  have hxabs : |x| ≤ 1 := (spectrum.norm_le_norm_of_mem hx).trans hna
  have hx2 : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).mpr hxabs
  have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith
  have hprod : (t * x) ^ 2 ≤ t ^ 2 := by
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hx2 (sq_nonneg t)]
  have hsmall : (t * x) ^ 2 ≤ 1 / 2 := by linarith
  have he := sqrt_complement_remainder ((t * x) ^ 2) (sq_nonneg _) hsmall
  rw [Real.norm_eq_abs]
  exact he.trans (by nlinarith [sq_nonneg ((t * x) ^ 2), sq_nonneg (t ^ 2)])

omit [Nontrivial A] in
/-- Interpret the scalar remainder as the actual square-root error. -/
theorem cfcSqrtRemainder_eq (a : A) (ha : IsSelfAdjoint a) (t : ℝ)
    (hpos : 0 ≤ 1 - (t • a) ^ 2) :
    cfcSqrtRemainder a t =
      1 - CFC.sqrt (1 - (t • a) ^ 2) - (t ^ 2 / 2) • a ^ 2 := by
  have hpoly : cfc (fun x : ℝ => 1 - (t * x) ^ 2) a = 1 - (t • a) ^ 2 := by
    rw [cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => (t * x) ^ 2) a,
      cfc_const_one ℝ a ha,
      cfc_pow (fun x : ℝ => t * x) 2 a (by fun_prop) ha, cfc_const_mul_id t a ha]
  have hroot : cfc (fun x : ℝ => Real.sqrt (1 - (t * x) ^ 2)) a =
      CFC.sqrt (1 - (t • a) ^ 2) := by
    rw [cfc_comp' Real.sqrt (fun x : ℝ => 1 - (t * x) ^ 2) a,
      hpoly, CFC.sqrt_eq_real_sqrt _ hpos, cfcₙ_eq_cfc]
  have hquad : cfc (fun x : ℝ => (t * x) ^ 2 / 2) a = (t ^ 2 / 2) • a ^ 2 := by
    have he : (fun x : ℝ => (t * x) ^ 2 / 2) = (fun x : ℝ => (t ^ 2 / 2) * x ^ 2) := by
      funext x
      ring
    rw [he, cfc_const_mul (t ^ 2 / 2) (fun x : ℝ => x ^ 2) a (by fun_prop),
      cfc_pow_id a 2 ha]
  unfold cfcSqrtRemainder
  rw [cfc_sub (fun x : ℝ => 1 - Real.sqrt (1 - (t * x) ^ 2))
    (fun x : ℝ => (t * x) ^ 2 / 2) a,
    cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => Real.sqrt (1 - (t * x) ^ 2)) a,
    cfc_const_one ℝ a ha, hroot, hquad]

/-- A fourth-order error disappears after dividing the quadratic term. -/
theorem le_of_scaled_quadratic_approximations {x y : ℝ}
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → t ^ 2 * x ≤ t ^ 2 * y + 2 * t ^ 4) :
    x ≤ y := by
  by_contra hxy
  have hgap : 0 < x - y := by linarith
  let t := min (1 / 2 : ℝ) (Real.sqrt (x - y) / 2)
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have hthalf : t ≤ 1 / 2 := min_le_left _ _
  have htsqrt : t ≤ Real.sqrt (x - y) / 2 := min_le_right _ _
  have hsqrt := Real.sq_sqrt hgap.le
  have hsmall : 2 * t ^ 2 < x - y := by
    have hsq := pow_le_pow_left₀ ht.le htsqrt 2
    nlinarith
  have hprod : 0 < t ^ 2 * (x - y - 2 * t ^ 2) :=
    mul_pos (sq_pos_of_pos ht) (by linarith)
  have hbound := h t ht hthalf
  nlinarith

/-- The unitary-path estimate recovers the square bound on self-adjoint contractions. -/
theorem normAttaining_selfAdjoint_contraction (T : A →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (h1 : ‖T 1‖ = 1) (a : A) (ha : IsSelfAdjoint a) (hna : ‖a‖ ≤ 1) :
    ‖T a‖ ^ 2 ≤ (inner ℂ (T 1) (T (a ^ 2))).re := by
  apply le_of_scaled_quadratic_approximations
  intro t ht ht1
  have hta : ‖t • a‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith [norm_nonneg a]
  have hsa : IsSelfAdjoint (t • a) := (IsSelfAdjoint.all t).smul ha
  have hpos : 0 ≤ 1 - (t • a) ^ 2 := by
    rw [sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg ((t • a) ^ 2),
      sq, hsa.norm_mul_self, sq_le_one_iff₀ (norm_nonneg _)]
    exact hta
  have hpath := contraction_sqrt_complement T hT (t • a) hsa hta
  have hrem : ‖T (cfcSqrtRemainder a t)‖ ≤ t ^ 4 :=
    (T.le_opNorm _).trans <| (mul_le_of_le_one_left (norm_nonneg _) hT).trans
      (norm_cfcSqrtRemainder_le a hna ht.le ht1)
  have hinner : (inner ℂ (T 1) (T (cfcSqrtRemainder a t))).re ≤ t ^ 4 := by
    exact (re_inner_le_norm (𝕜 := ℂ) (T 1) (T (cfcSqrtRemainder a t))).trans (by simpa only [h1, one_mul] using hrem)
  have hpair := norm_sub_sq (𝕜 := ℂ) (T 1) (T (CFC.sqrt (1 - (t • a) ^ 2)))
  have hnonneg := sq_nonneg ‖T 1 - T (CFC.sqrt (1 - (t • a) ^ 2))‖
  have hsmul (c : ℝ) (v : H) :
      inner ℂ (T 1) (c • v) = (c : ℂ) * inner ℂ (T 1) v := by
    rw [← Complex.coe_smul c v, inner_smul_right]
  rw [cfcSqrtRemainder_eq a ha t hpos, map_sub, map_sub,
    ContinuousLinearMap.map_smul_of_tower, inner_sub_right, inner_sub_right, hsmul,
    inner_self_eq_norm_sq_to_K] at hinner
  simp only [ContinuousLinearMap.map_smul_of_tower, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
    mul_pow] at hpath
  simp only [Complex.sub_re, Complex.ofReal_re, h1,
    Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at hinner
  norm_num at hinner
  rw [h1] at hpair
  change ‖T 1 - T (CFC.sqrt (1 - (t • a) ^ 2))‖ ^ 2 =
    1 ^ 2 - 2 * (inner ℂ (T 1) (T (CFC.sqrt (1 - (t • a) ^ 2)))).re +
    ‖T (CFC.sqrt (1 - (t • a) ^ 2))‖ ^ 2 at hpair
  nlinarith only [hpath, hinner, hpair, hnonneg]

/-- Homogeneity removes the contraction restriction. -/
theorem normAttaining_selfAdjoint (T : A →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (h1 : ‖T 1‖ = 1) (a : A) (ha : IsSelfAdjoint a) :
    ‖T a‖ ^ 2 ≤ (inner ℂ (T 1) (T (a ^ 2))).re := by
  by_cases hz : a = 0
  · simp [hz]
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr hz
  have hna : ‖‖a‖⁻¹ • a‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  have h := normAttaining_selfAdjoint_contraction T hT h1 (‖a‖⁻¹ • a)
    ((IsSelfAdjoint.all _).smul ha) hna
  have hsmul (c : ℝ) (v : H) :
      inner ℂ (T 1) (c • v) = (c : ℂ) * inner ℂ (T 1) v := by
    rw [← Complex.coe_smul c v, inner_smul_right]
  simp only [ContinuousLinearMap.map_smul_of_tower, smul_pow, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hn.le), mul_pow, hsmul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  exact (mul_le_mul_iff_of_pos_left (sq_pos_of_pos (inv_pos.mpr hn))).mp h

/-- Haagerup's norm-attaining inequality, obtained from the real and imaginary parts. -/
theorem normAttaining_grothendieck (T : A →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (h1 : ‖T 1‖ = 1) :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧
      ∀ a, ‖T a‖ ^ 2 ≤ (f (star a * a)).re + (f (a * star a)).re := by
  obtain ⟨f, hf1, hf⟩ := exists_normAttainingState T hT h1
  refine ⟨f, hf1, fun a => ?_⟩
  let b : A := realPart a
  let c : A := imaginaryPart a
  have hb := normAttaining_selfAdjoint T hT h1 b selfAdjoint.isSelfAdjoint
  have hc := normAttaining_selfAdjoint T hT h1 c selfAdjoint.isSelfAdjoint
  rw [← hf (b ^ 2)] at hb
  rw [← hf (c ^ 2)] at hc
  have hdec : b + Complex.I • c = a := realPart_add_I_smul_imaginaryPart a
  have htdec : T b + Complex.I • T c = T a := by rw [← map_smul, ← map_add, hdec]
  have hpar := parallelogram_law_with_norm ℂ (T b) (Complex.I • T c)
  rw [norm_smul, Complex.norm_I, one_mul, htdec] at hpar
  have hsum : (f (star a * a)).re + (f (a * star a)).re =
      2 * ((f (b ^ 2)).re + (f (c ^ 2)).re) := by
    rw [← Complex.add_re, ← map_add, star_mul_self_add_self_mul_star]
    simp only [two_smul, two_mul, map_add, Complex.add_re, b, c, pow_two]
  rw [hsum]
  nlinarith [sq_nonneg ‖T b - Complex.I • T c‖]

/-- Transport the norm-attaining inequality from the identity to a unitary. -/
theorem unitaryNormAttaining_grothendieck (T : A →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (u : unitary A) (hu : ‖T (u : A)‖ = 1) :
    ∃ f g : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ g 1 = 1 ∧
      ∀ a, ‖T a‖ ^ 2 ≤ (f (star a * a)).re + (g (a * star a)).re := by
  let S := T.comp (ContinuousLinearMap.mul ℂ A (u : A))
  have hS : ‖S‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    calc
      ‖S a‖ ≤ ‖T‖ * ‖(u : A) * a‖ := T.le_opNorm _
      _ ≤ ‖(u : A) * a‖ := mul_le_of_le_one_left (norm_nonneg _) hT
      _ ≤ ‖(u : A)‖ * ‖a‖ := norm_mul_le _ _
      _ = 1 * ‖a‖ := by rw [CStarRing.norm_coe_unitary]
  have hS1 : ‖S 1‖ = 1 := by simpa [S] using hu
  obtain ⟨f, hf1, hf⟩ := normAttaining_grothendieck S hS hS1
  let gL : A →ₗ[ℂ] ℂ := f.toLinearMap.comp
    ((LinearMap.mulRight ℂ (u : A)).comp (LinearMap.mulLeft ℂ (star (u : A))))
  let g : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ gL
    (fun a ha => f.map_nonneg (star_left_conjugate_nonneg ha (u : A)))
  have hg (a : A) : g a = f (star (u : A) * a * (u : A)) := rfl
  refine ⟨f, g, hf1, ?_, fun a => ?_⟩
  · rw [hg, mul_one, Unitary.star_mul_self_of_mem u.prop, hf1]
  · have h := hf (star (u : A) * a)
    have hval : S (star (u : A) * a) = T a := by
      change T ((u : A) * (star (u : A) * a)) = T a
      rw [← mul_assoc, Unitary.mul_star_self_of_mem u.prop, one_mul]
    have hs : star (star (u : A) * a) * (star (u : A) * a) = star a * a := by
      rw [star_mul, star_star, mul_assoc, ← mul_assoc (u : A),
        Unitary.mul_star_self_of_mem u.prop, one_mul]
    have ht : (star (u : A) * a) * star (star (u : A) * a) =
        star (u : A) * (a * star a) * (u : A) := by
      rw [star_mul, star_star]
      simp only [mul_assoc]
    simpa only [hval, hs, ht, hg] using h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_GrothendieckUltrapower
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.constantHilbertInclusion_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.quotientGNSVector_mk _root_.OAI.KadisonSimilarity.tracialUltrapowerGNSInclusion_mk _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded families turn approximate unitary norm attainment into exact
attainment. The source is the ordinary bounded product C-star algebra; only
the Hilbert target needs an ultraproduct. -/

noncomputable section
namespace KadisonSimilarity
open NuclearUltrapower Filter
open scoped ENNReal Topology ComplexOrder

variable {B H : Type*} [CStarAlgebra B] [Nontrivial B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem grothendieckFamilyMap_norm_le (ω : Ultrafilter ℕ) (T : B →L[ℂ] H) :
    ‖grothendieckFamilyMap ω T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro X
  simp only [grothendieckFamilyMap_apply, UniformSpace.Completion.norm_coe]
  apply le_of_tendsto (UltraPreHilbert.norm_tendsto ω _)
  exact Eventually.of_forall fun i => (T.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero X i) (norm_nonneg T))

theorem grothendieckFamilyMap_norm_tendsto (ω : Ultrafilter ℕ) (T : B →L[ℂ] H)
    (X : lp (fun _ : ℕ => B) ∞) :
    Tendsto (fun i => ‖T (X i)‖) (ω : Filter ℕ) (𝓝 ‖grothendieckFamilyMap ω T X‖) := by
  simpa only [grothendieckFamilyMap_apply, UniformSpace.Completion.norm_coe,
    grothendieckFamilyLinear_apply] using
      UltraPreHilbert.norm_tendsto ω (grothendieckFamilyLinear ω T X)

@[simp] theorem grothendieckFamilyMap_constant_norm (ω : Ultrafilter ℕ)
    (T : B →L[ℂ] H) (b : B) :
    ‖grothendieckFamilyMap ω T (grothendieckConstant b)‖ = ‖T b‖ :=
  tendsto_nhds_unique (grothendieckFamilyMap_norm_tendsto ω T (grothendieckConstant b))
    tendsto_const_nhds

local instance instNontrivialSubtypePreLpNatMemAddSubgroupLpTopENNReal_solutions : Nontrivial (lp (fun _ : ℕ => B) ∞) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have he := congrArg (fun X : lp (fun _ : ℕ => B) ∞ => X 0) h
  exact zero_ne_one he

section Positive
variable [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
/-- The norm of a unitary family is attained at the limiting map. -/
theorem grothendieckFamily_attains (T : B →L[ℂ] H) (u : ℕ → unitary B)
    (hu : Tendsto (fun n => ‖T (u n : B)‖) atTop (𝓝 1)) :
    ‖grothendieckFamilyMap (Ultrafilter.of atTop) T
      (grothendieckUnitaryFamily u : lp (fun _ : ℕ => B) ∞)‖ = 1 :=
  tendsto_nhds_unique
    (grothendieckFamilyMap_norm_tendsto (Ultrafilter.of atTop) T (grothendieckUnitaryFamily u))
    (hu.mono_left (Ultrafilter.of_le _))

attribute [local instance] OAI.KadisonSimilarity.instCStarAlgebraSubtypePreLpNatMemAddSubgroupLpTopENNReal_solutions
attribute [local instance] OAI.KadisonSimilarity.instPartialOrderSubtypePreLpNatMemAddSubgroupLpTopENNReal_solutions
attribute [local instance] OAI.KadisonSimilarity.instStarOrderedRingSubtypePreLpNatMemAddSubgroupLpTopENNReal_solutions
omit [PartialOrder B] [StarOrderedRing B] in
/-- Apply the proved norm-attaining theorem inside the bounded product. -/
theorem grothendieckFamily_states (T : B →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (u : ℕ → unitary B)
    (hu : Tendsto (fun n => ‖T (u n : B)‖) atTop (𝓝 1)) :
    ∃ f g : lp (fun _ : ℕ => B) ∞ →ₚ[ℂ] ℂ, f 1 = 1 ∧ g 1 = 1 ∧
      ∀ X, ‖grothendieckFamilyMap (Ultrafilter.of atTop) T X‖ ^ 2 ≤
        (f (star X * X)).re + (g (X * star X)).re := by
  have hS : ‖grothendieckFamilyMap (Ultrafilter.of atTop) T‖ ≤ 1 :=
    (grothendieckFamilyMap_norm_le (Ultrafilter.of atTop) T).trans hT
  have hunit := grothendieckFamily_attains T u hu
  exact unitaryNormAttaining_grothendieck
    (A := lp (fun _ : ℕ => B) ∞)
    (H := HilbertUltraproduct (fun _ : ℕ => H) (Ultrafilter.of atTop))
    (grothendieckFamilyMap (Ultrafilter.of atTop) T) hS
    (grothendieckUnitaryFamily u) hunit

/-- Approximate norm attainment at unitaries suffices for the exact two-state inequality. -/
theorem approximateUnitary_grothendieck (T : B →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (u : ℕ → unitary B)
    (hu : Tendsto (fun n => ‖T (u n : B)‖) atTop (𝓝 1)) :
    ∃ f g : B →ₚ[ℂ] ℂ, f 1 = 1 ∧ g 1 = 1 ∧
      ∀ b, ‖T b‖ ^ 2 ≤ (f (star b * b)).re + (g (b * star b)).re := by
  obtain ⟨f, g, hf, hg, hfg⟩ := grothendieckFamily_states T hT u hu
  refine ⟨grothendieckRestrict f, grothendieckRestrict g, ?_, ?_, fun b => ?_⟩
  · change f (grothendieckConstant 1) = 1
    exact (congrArg f (map_one grothendieckConstant)).trans hf
  · change g (grothendieckConstant 1) = 1
    exact (congrArg g (map_one grothendieckConstant)).trans hg
  · have h := hfg (grothendieckConstant b)
    rw [grothendieckFamilyMap_constant_norm] at h
    change ‖T b‖ ^ 2 ≤ (f (grothendieckConstant (star b * b))).re +
      (g (grothendieckConstant (b * star b))).re
    simpa only [map_mul, map_star] using h

end Positive

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_GrothendieckMatrix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.HochschildMatrixDilation.diag_pow _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.representedDoubleMatrix_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A four-by-four matrix corner supplies unitary norm-attaining tests for
an arbitrary bounded linear map without an additional convexity theorem. -/

noncomputable section
namespace KadisonSimilarity
open HochschildMatrixDilation Filter
open scoped ComplexOrder Topology

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [Nontrivial A] in
theorem grothendieckMatrixMap_norm_le (T : A →L[ℂ] H) :
    ‖grothendieckMatrixMap T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro X
  change ‖T (X 0 1 0 1)‖ ≤ ‖T‖ * ‖X‖
  exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    ((CStarMatrix.norm_entry_le_norm (M := X 0 1) (i := 0) (j := 1)).trans
      (CStarMatrix.norm_entry_le_norm (M := X) (i := 0) (j := 1))) (norm_nonneg T))

omit [Nontrivial A] in
/-- A norm-one map has norm-attaining unitary tests in its matrix extension. -/
theorem grothendieckMatrixMap_approximateUnitary (T : A →L[ℂ] H) (hT : ‖T‖ = 1) :
    ∃ u : ℕ → unitary (Mat (Mat A)),
      Tendsto (fun n => ‖grothendieckMatrixMap T (u n : Mat (Mat A))‖) atTop (𝓝 1) := by
  have hx : ∀ n : ℕ, ∃ a : A, ‖a‖ < 1 ∧ 1 - 1 / ((n : ℝ) + 1) < ‖T a‖ := by
    intro n
    apply T.exists_lt_apply_of_lt_opNorm
    rw [hT]
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose a ha hTa using hx
  let u n := contractionSymmetryUnitary (a n) (ha n).le
  refine ⟨u, ?_⟩
  have heval (n : ℕ) : grothendieckMatrixMap T (u n : Mat (Mat A)) = T (a n) := by
    rw [grothendieckMatrixMap_apply, contractionSymmetryUnitary_entry]
  simp only [heval]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 1) from by
      simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    tendsto_const_nhds (fun n => (hTa n).le)
  intro n
  exact (T.le_opNorm _).trans (by rw [hT, one_mul]; exact (ha n).le)

theorem grothendieckCorner00_one_norm : ‖grothendieckCorner00 (1 : A)‖ ≤ 1 := by
  exact (norm_diag_le _ _).trans (max_le ((norm_diag_le _ _).trans (by simp)) (by simp))

theorem grothendieckCorner11_one_norm : ‖grothendieckCorner11 (1 : A)‖ ≤ 1 := by
  exact (norm_diag_le _ _).trans (max_le (by simp) ((norm_diag_le _ _).trans (by simp)))

lemma grothendieckState11_mass (f : Mat (Mat A) →ₚ[ℂ] ℂ) (hf : f 1 = 1) :
    (grothendieckState11 f 1).re ≤ 1 := by
  exact (Complex.re_le_norm _).trans <| (f.norm_apply_le_of_nonneg _
    (grothendieckCorner11_nonneg zero_le_one)).trans (by
      rw [hf, norm_one, one_mul]
      exact grothendieckCorner11_one_norm)

lemma grothendieckState00_mass (f : Mat (Mat A) →ₚ[ℂ] ℂ) (hf : f 1 = 1) :
    (grothendieckState00 f 1).re ≤ 1 := by
  exact (Complex.re_le_norm _).trans <| (f.norm_apply_le_of_nonneg _
    (grothendieckCorner00_nonneg zero_le_one)).trans (by
      rw [hf, norm_one, one_mul]
      exact grothendieckCorner00_one_norm)

/-- The two-state little Grothendieck inequality for a norm-one map. -/
theorem normOne_grothendieck (T : A →L[ℂ] H) (hT : ‖T‖ = 1) :
    ∃ f g : A →ₚ[ℂ] ℂ, (f 1).re ≤ 1 ∧ (g 1).re ≤ 1 ∧
      ∀ a, ‖T a‖ ^ 2 ≤ (f (star a * a)).re + (g (a * star a)).re := by
  obtain ⟨u, hu⟩ := grothendieckMatrixMap_approximateUnitary T hT
  obtain ⟨f, g, hf, hg, hfg⟩ := approximateUnitary_grothendieck
    (grothendieckMatrixMap T) ((grothendieckMatrixMap_norm_le T).trans hT.le) u hu
  refine ⟨grothendieckState11 f, grothendieckState00 g,
    grothendieckState11_mass f hf, grothendieckState00_mass g hg, fun a => ?_⟩
  simpa only [grothendieckMatrixMap_apply, grothendieckOffDiagonal_entry,
    grothendieckOffDiagonal_star_mul, grothendieckOffDiagonal_mul_star,
    grothendieckState11_apply, grothendieckState00_apply] using hfg (grothendieckOffDiagonal a)

/-- Homogeneity gives the published inequality with its exact operator-norm factor. -/
theorem littleGrothendieck_nontrivial : LittleGrothendieckInput A H := by
  intro T
  by_cases hT : T = 0
  · subst T
    exact ⟨0, 0, by simp, by simp, by simp⟩
  have hnorm : 0 < ‖T‖ := norm_pos_iff.mpr hT
  let S : A →L[ℂ] H := ‖T‖⁻¹ • T
  have hS : ‖S‖ = 1 := by
    change ‖‖T‖⁻¹ • T‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnorm.le), inv_mul_cancel₀ hnorm.ne']
  obtain ⟨f, g, hf, hg, hfg⟩ := normOne_grothendieck S hS
  refine ⟨f, g, hf, hg, fun a => ?_⟩
  have h := hfg a
  change ‖‖T‖⁻¹ • T a‖ ^ 2 ≤ _ at h
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnorm.le), mul_pow] at h
  have hc : 0 < ‖T‖ ^ 2 := sq_pos_of_pos hnorm
  have hmul := mul_le_mul_of_nonneg_left h hc.le
  simpa only [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hnorm.ne', one_pow, one_mul] using hmul

/-- Haagerup's two-state bound, including the zero algebra. -/
theorem littleGrothendieck_proved {D E : Type*} [CStarAlgebra D] [PartialOrder D]
    [StarOrderedRing D] [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    LittleGrothendieckInput D E := by
  cases subsingleton_or_nontrivial D with
  | inl h =>
    let := h
    intro T
    refine ⟨0, 0, by simp, by simp, fun a => ?_⟩
    have ha : a = 0 := Subsingleton.elim _ _
    simp [ha]
  | inr h =>
    let := h
    exact littleGrothendieck_nontrivial

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_BoundedHomRow
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row bounds for arbitrary bounded homomorphisms in terms of their operator norms. -/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
theorem norm_sharpVectorMap_le_general (π : BoundedUnitalHom A H)
    {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖) (ξ : H) : ‖sharpVectorMap π ξ‖ ≤ M * ‖ξ‖ := by
  apply opNorm_le_bound _ (by positivity)
  intro a
  change ‖(sharpHom π).1 a ξ‖ ≤ _
  calc
    _ ≤ ‖(sharpHom π).1 a‖ * ‖ξ‖ := le_opNorm _ _
    _ ≤ (M * ‖a‖) * ‖ξ‖ := mul_le_mul_of_nonneg_right
      (sharpHom_bound π hπ a) (norm_nonneg ξ)
    _ = (M * ‖ξ‖) * ‖a‖ := by ring

/-- The polar estimate converts the two-sided square bound into the single
row square, with a bound depending only on the norm of the homomorphism. -/
theorem boundedHom_vector_states (lg : LittleGrothendieckInput A H)
    (π : BoundedUnitalHom A H) {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖) (ξ : H) :
    ∃ f g : A →ₚ[ℂ] ℂ, (f 1).re ≤ 1 ∧ (g 1).re ≤ 1 ∧
      ∀ a, ‖(π.1 a).adjoint ξ‖ ^ 2 ≤
        M ^ 4 * ‖ξ‖ ^ 2 * ((f (a * star a)).re + (g (a * star a)).re) := by
  obtain ⟨f, g, hf, hg, hfg⟩ := lg (sharpVectorMap π ξ)
  refine ⟨f, g, hf, hg, ?_⟩
  intro a
  let h := CFC.sqrt (a * star a)
  have hh : 0 ≤ h := CFC.sqrt_nonneg _
  have hsq : h * h = a * star a := CFC.sqrt_mul_sqrt_self _ (mul_star_self_nonneg a)
  have hp := hom_adjoint_sqrt_bound π hM hπ a ξ
  change ‖(π.1 a).adjoint ξ‖ ≤ M * ‖(π.1 h).adjoint ξ‖ at hp
  have hl := hfg h
  simp only [sharpVectorMap_apply, hh.star_eq, hsq] at hl
  have hpos : 0 ≤ (f (a * star a)).re + (g (a * star a)).re :=
    add_nonneg (f.map_nonneg (mul_star_self_nonneg a)).1
      (g.map_nonneg (mul_star_self_nonneg a)).1
  calc
    _ ≤ (M * ‖(π.1 h).adjoint ξ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
    _ = M ^ 2 * ‖(π.1 h).adjoint ξ‖ ^ 2 := by ring
    _ ≤ M ^ 2 * (‖sharpVectorMap π ξ‖ ^ 2 *
        ((f (a * star a)).re + (g (a * star a)).re)) := mul_le_mul_of_nonneg_left hl (sq_nonneg M)
    _ ≤ M ^ 2 * ((M * ‖ξ‖) ^ 2 * ((f (a * star a)).re + (g (a * star a)).re)) := by
      gcongr
      exact norm_sharpVectorMap_le_general π hM hπ ξ
    _ = _ := by ring


end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_OrbitSquareNormalization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedHomOrbit_apply _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.listOrbitSum_append _root_.OAI.KadisonSimilarity.listOrbitSum_nil _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.matrixLeftArray_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.representedDoubleMatrix_apply _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.similarityRepresentation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Upper and lower orbit estimates for a finite family whose sum of
positive squares is one. This is the normalization step in the cyclic
similarity argument. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem normalized_adjoint_orbit_sum_le (π : BoundedUnitalHom A H)
    {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖)
    {n : ℕ} (a : Fin n → A) (ha : ∑ i, star (a i) * a i = 1) (ξ : H) :
    ∑ i, ‖(π.1 (star (a i))).adjoint ξ‖ ^ 2 ≤ 2 * M ^ 4 * ‖ξ‖ ^ 2 := by
  obtain ⟨f, g, hf, hg, hfg⟩ := boundedHom_vector_states
    littleGrothendieck_proved π hM hπ ξ
  have hf' : (∑ i, (f (star (a i) * a i)).re) ≤ 1 := by
    rw [← Complex.re_sum, ← map_sum, ha]
    exact hf
  have hg' : (∑ i, (g (star (a i) * a i)).re) ≤ 1 := by
    rw [← Complex.re_sum, ← map_sum, ha]
    exact hg
  calc
    _ ≤ ∑ i, M ^ 4 * ‖ξ‖ ^ 2 *
        ((f (star (a i) * a i)).re + (g (star (a i) * a i)).re) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [star_star] using hfg (star (a i))
    _ = M ^ 4 * ‖ξ‖ ^ 2 *
        ((∑ i, (f (star (a i) * a i)).re) + ∑ i, (g (star (a i) * a i)).re) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ M ^ 4 * ‖ξ‖ ^ 2 * (1 + 1) :=
      mul_le_mul_of_nonneg_left (add_le_add hf' hg') (by positivity)
    _ = _ := by ring

theorem normalized_orbit_sum_le (π : BoundedUnitalHom A H)
    {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖)
    {n : ℕ} (a : Fin n → A) (ha : ∑ i, star (a i) * a i = 1) (ξ : H) :
    ∑ i, ‖π.1 (a i) ξ‖ ^ 2 ≤ 2 * M ^ 4 * ‖ξ‖ ^ 2 := by
  have h := normalized_adjoint_orbit_sum_le (sharpHom π) hM (sharpHom_bound π hπ) a ha ξ
  simpa only [sharpHom_apply, ← ContinuousLinearMap.star_eq_adjoint, star_star] using h

theorem norm_sq_le_normalized_orbit_sum (π : BoundedUnitalHom A H)
    {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖)
    {n : ℕ} (a : Fin n → A) (ha : ∑ i, star (a i) * a i = 1) (ξ : H) :
    ‖ξ‖ ^ 2 ≤ (2 * M ^ 4) * ∑ i, ‖π.1 (a i) ξ‖ ^ 2 := by
  let U : HilbertCopies H n := WithLp.toLp 2 (fun i => (π.1 (star (a i))).adjoint ξ)
  let V : HilbertCopies H n := WithLp.toLp 2 (fun i => π.1 (a i) ξ)
  have hidentity : ∑ i, π.1 (star (a i)) (π.1 (a i) ξ) = ξ := by
    have h := congrArg (fun b : A => π.1 b ξ) ha
    simpa only [map_sum, map_mul, map_one, sum_apply, mul_apply_eq_comp, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply] using h
  have hinner : inner ℂ U V = (‖ξ‖ ^ 2 : ℝ) := by
    simp only [PiLp.inner_apply, U, V,
      ContinuousLinearMap.adjoint_inner_left, ← inner_sum, hidentity,
      inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    rfl
  have hnorm : ‖ξ‖ ^ 2 ≤ ‖U‖ * ‖V‖ := by
    simpa only [hinner, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] using
      norm_inner_le_norm (𝕜 := ℂ) U V
  have hu : ‖U‖ ^ 2 ≤ 2 * M ^ 4 * ‖ξ‖ ^ 2 := by
    simpa only [PiLp.norm_sq_eq_of_L2, U, WithLp.ofLp_toLp] using
      normalized_adjoint_orbit_sum_le π hM hπ a ha ξ
  have hv : ‖V‖ ^ 2 = ∑ i, ‖π.1 (a i) ξ‖ ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2, V]
  have hs := pow_le_pow_left₀ (sq_nonneg ‖ξ‖) hnorm 2
  rw [mul_pow] at hs
  have hs' := mul_le_mul_of_nonneg_right hu (sq_nonneg ‖V‖)
  rw [hv] at hs hs'
  by_cases hz : ξ = 0
  · simp [hz]
  · have hp : 0 < ‖ξ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
    nlinarith

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FiniteOrbitComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.boundedHomOrbit_apply _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.similarityRepresentation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite equal-square families have uniformly comparable orbit norms.
The regularization stays inside the original C*-algebra. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_positive_shift_sqrt_unit (x : A) (hx : 0 ≤ x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Aˣ, 0 ≤ (S : A) ∧ (S : A) * (S : A) = x + ε • (1 : A) := by
  let Q : Aˣ := {
    val := x + ε • (1 : A)
    inv := positiveShiftReciprocal x ε
    val_inv := positiveShiftReciprocal_inverse x hx hε
    inv_val := by
      have hc : Commute (positiveShiftReciprocal x ε) (x + ε • (1 : A)) :=
        (positiveShiftReciprocal_commute x ε).add_right ((Commute.one_right _).smul_right ε)
      rw [hc.eq]
      exact positiveShiftReciprocal_inverse x hx hε }
  have hQ : 0 ≤ (Q : A) := add_nonneg hx (smul_nonneg hε.le zero_le_one)
  obtain ⟨S, hS⟩ := (CFC.isUnit_sqrt_iff _ hQ).mpr Q.isUnit
  refine ⟨S, ?_, ?_⟩
  · rw [hS]; exact CFC.sqrt_nonneg _
  · rw [hS, CFC.sqrt_mul_sqrt_self _ hQ]

theorem unit_normalized_square_sum (S : Aˣ) (hS : 0 ≤ (S : A))
    {n : ℕ} (a : Fin n → A) (ha : ∑ i, star (a i) * a i = (S : A) * (S : A)) :
    ∑ i, star (a i * (↑S⁻¹ : A)) * (a i * (↑S⁻¹ : A)) = 1 := by
  have hstar : star S = S := Units.ext hS.star_eq
  have hi : star (↑S⁻¹ : A) = (↑S⁻¹ : A) := by
    rw [← Units.coe_star, star_inv, hstar]
  simp only [star_mul, hi]
  calc
    _ = (↑S⁻¹ : A) * (∑ i, star (a i) * a i) * (↑S⁻¹ : A) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      noncomm_ring
    _ = 1 := by rw [ha]; simp

theorem finite_equal_square_orbit_comparison (π : BoundedUnitalHom A H)
    {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖)
    {n m : ℕ} (a : Fin n → A) (b : Fin m → A)
    (hab : ∑ i, star (a i) * a i = ∑ j, star (b j) * b j) (ξ : H) :
    ∑ i, ‖π.1 (a i) ξ‖ ^ 2 ≤ (2 * M ^ 4) ^ 2 * ∑ j, ‖π.1 (b j) ξ‖ ^ 2 := by
  let K := (2 * M ^ 4) ^ 2
  let s := ‖ξ‖ ^ 2
  have hK : 0 ≤ K := sq_nonneg _
  have hs : 0 ≤ s := sq_nonneg _
  have regularized (ε : ℝ) (hε : 0 < ε) :
      ε * s + ∑ i, ‖π.1 (a i) ξ‖ ^ 2 ≤
        K * (ε * s + ∑ j, ‖π.1 (b j) ξ‖ ^ 2) := by
    let x := ∑ j, star (b j) * b j
    have hx : 0 ≤ x := Finset.sum_nonneg fun j _ => star_mul_self_nonneg (b j)
    obtain ⟨S, hS, hSq⟩ := exists_positive_shift_sqrt_unit x hx hε
    let e : A := Real.sqrt ε • 1
    have he : star e * e = ε • (1 : A) := by
      dsimp [e]
      rw [star_smul, star_trivial, star_one, smul_mul_assoc, mul_smul_comm,
        one_mul, smul_smul, Real.mul_self_sqrt hε.le]
    let a' : Fin (n + 1) → A := Fin.cons e a
    let b' : Fin (m + 1) → A := Fin.cons e b
    have ha' : ∑ i, star (a' i) * a' i = (S : A) * (S : A) := by
      rw [Fin.sum_univ_succ]
      simp only [a', Fin.cons_zero, Fin.cons_succ, he]
      rw [hab, hSq]; dsimp [x]; abel
    have hb' : ∑ i, star (b' i) * b' i = (S : A) * (S : A) := by
      rw [Fin.sum_univ_succ]
      simp only [b', Fin.cons_zero, Fin.cons_succ, he]
      rw [hSq]; dsimp [x]; abel
    let η := π.1 (S : A) ξ
    have hu := normalized_orbit_sum_le π hM hπ
      (fun i => a' i * (↑S⁻¹ : A)) (unit_normalized_square_sum S hS a' ha') η
    have hl := norm_sq_le_normalized_orbit_sum π hM hπ
      (fun i => b' i * (↑S⁻¹ : A)) (unit_normalized_square_sum S hS b' hb') η
    have hrecover (c : A) : π.1 (c * (↑S⁻¹ : A)) η = π.1 c ξ := by
      dsimp [η]
      calc
        _ = (π.1 (c * (↑S⁻¹ : A)) * π.1 (S : A)) ξ := rfl
        _ = π.1 ((c * (↑S⁻¹ : A)) * (S : A)) ξ := by simp only [map_mul]
        _ = π.1 c ξ := by simp [mul_assoc]
    simp only [hrecover] at hu hl
    have hcomp := hu.trans (mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 * M ^ 4))
    have henorm : ‖π.1 e ξ‖ ^ 2 = ε * s := by
      dsimp [e, s]
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, map_one, smul_apply,
        ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg ε),
        mul_pow, Real.sq_sqrt hε.le]
    simp only [Fin.sum_univ_succ, a', b', Fin.cons_zero, Fin.cons_succ] at hcomp
    rw [henorm] at hcomp
    simpa only [K, pow_two, mul_assoc] using hcomp
  apply le_of_forall_pos_le_add
  intro δ hδ
  let d := (K + 1) * (s + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  let ε := δ / d
  have hε : 0 < ε := div_pos hδ hd
  have heq : ε * d = δ := div_mul_cancel₀ δ hd.ne'
  have hsmall : K * (ε * s) ≤ δ := by
    calc
      _ = ε * (K * s) := by ring
      _ ≤ ε * d := mul_le_mul_of_nonneg_left (by dsimp [d]; nlinarith) hε.le
      _ = δ := heq
  have h := regularized ε hε
  nlinarith [mul_nonneg hε.le hs]

theorem listSquareSum_eq_sum_get (L : List A) :
    (listSquareSum L : A) = ∑ i : Fin L.length, star (L.get i) * L.get i := by
  unfold listSquareSum
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  exact map_sum (selfAdjoint A).subtype _ _

omit [PartialOrder A] [StarOrderedRing A] [CompleteSpace H] in
theorem listOrbitSum_eq_sum_get (π : BoundedUnitalHom A H) (ξ : H) (L : List A) :
    listOrbitSum π ξ L = ∑ i : Fin L.length, ‖π.1 (L.get i) ξ‖ ^ 2 := by
  rw [listOrbitSum, ← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

theorem list_equal_square_orbit_comparison_oai (π : BoundedUnitalHom A H)
    {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖)
    (a b : List A) (hab : listSquareSum a = listSquareSum b) (ξ : H) :
    listOrbitSum π ξ a ≤ (2 * M ^ 4) ^ 2 * listOrbitSum π ξ b := by
  rw [listOrbitSum_eq_sum_get, listOrbitSum_eq_sum_get]
  apply finite_equal_square_orbit_comparison π hM hπ a.get b.get
  rw [← listSquareSum_eq_sum_get, ← listSquareSum_eq_sum_get, hab]

end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonSimilarity.list_equal_square_orbit_comparison_oai.{u_1, u_2} := @OAI.KadisonSimilarity.list_equal_square_orbit_comparison_oai.{u_1, u_2}
