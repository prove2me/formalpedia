-- Prove2me | solution 1 for OAI.PermanentBorder.CI.good_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:19:54.752154+00:00
-- url     : https://prove2.me/submissions/3aa8152f-89b5-4193-a4ab-04798d6492fb

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/SliceCertificates.lean:L259-L273
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.CI.good_card. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
import Theorems.Thm_OAI_PermanentBorder_CI_good_iff_bad
import Theorems.Thm_OAI_PermanentBorder_CI_normalized_count_constant
import Theorems.Thm_OAI_PermanentBorder_CI_powers_good
import Theorems.Thm_OAI_PermanentBorder_SliceParameters_macaulay_surjective_iff
import Theorems.Thm_OAI_PermanentBorder_SliceParameters_macaulay_surjective_zero
import Theorems.Thm_OAI_PermanentBorder_SliceParameters_monomial_mem_of_variable_powers

-- ---- from OAI.Algebra.Determinantal.RegularSections ----
namespace OAI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
section Algebra
variable {R ι : Type*} [CommRing R] [Fintype ι]

lemma linear_homogeneous (l : Option ι → R) : (linear l).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _
  simpa using (isHomogeneous_C (Option ι) (l j)).mul (isHomogeneous_X R j)

lemma det_homogeneous {σ n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n (MvPolynomial σ R)) (e : n → ℕ)
    (hA : ∀ i j, (A i j).IsHomogeneous (e i)) : A.det.IsHomogeneous (∑ i, e i) := by
  classical
  rw [Matrix.det_apply]
  apply IsHomogeneous.sum
  intro p _
  have hp : (∏ i, A (p i) i).IsHomogeneous (∑ i, e (p i)) :=
    IsHomogeneous.prod _ _ _ (fun i _ => hA _ _)
  rw [Equiv.sum_comp] at hp
  change (p.sign : ℤ) • (∏ i, A (p i) i) ∈
    (homogeneousSubmodule σ R (∑ i, e i)).restrictScalars ℤ
  exact Submodule.smul_mem _ _ hp

lemma square_det_homogeneous (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R)
    (e : ι → ℕ) (hH : ∀ i, (H i).IsHomogeneous (e i)) :
    (square H l).det.IsHomogeneous (∑ i, (e i - 1)) := by
  classical
  have h := det_homogeneous (square H l) (Option.elim' 0 (fun i => e i - 1)) (by
    intro i j
    cases i with
    | none => exact isHomogeneous_C _ _
    | some i => exact (hH i).pderiv)
  simpa using h

lemma bad_homogeneous (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R)
    (e : ι → ℕ) (hH : ∀ i, (H i).IsHomogeneous (e i)) (i : Option ι) :
    (bad H l i).IsHomogeneous (degrees e i) := by
  cases i with
  | none => exact (linear_homogeneous l).mul (square_det_homogeneous H l e hH)
  | some i => exact hH i

end Algebra
section Good
variable {K ι : Type*} [Field K] [Fintype ι]

end Good
end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma powers_homogeneous (e : ι → ℕ) (i : ι) : (powers e i).IsHomogeneous (e i) := by
  simpa [powers] using ((isHomogeneous_X ℂ (some i)).pow (e i)).sub
    ((isHomogeneous_X ℂ (none : Option ι)).pow (e i))

lemma card_power_roots (n : ℕ) (hn : 0 < n) : Nat.card {z : ℂ // z^n=1} = n := by
  let : NeZero n := ⟨ne_of_gt hn⟩
  let e := (rootsOfUnityEquivNthRoots ℂ n).trans
    (Equiv.subtypeEquivRight (fun _ => Polynomial.mem_nthRoots hn))
  rw [← Nat.card_congr e]
  exact Complex.card_rootsOfUnity n

lemma powers_card (e : ι → ℕ) (he : ∀ i, 0 < e i) :
    Nat.card (Roots (powers e) coordinate) = ∏ i, e i := by
  rw [Nat.card_congr (powersRootsEquiv e), Nat.card_pi]
  exact Finset.prod_congr rfl (fun i _ => card_power_roots (e i) (he i))

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial
section
variable {σ : Type*} [Fintype σ]

lemma contDiff_eval (p : MvPolynomial σ ℂ) :
    ContDiff ℂ 1 (fun x : σ → ℂ => MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℂ 1 (fun _ : σ → ℂ => a))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp => simpa only [map_mul, eval_X] using hp.mul (contDiff_apply ℂ ℂ i)

end
end PermanentBorder.CI

namespace PermanentBorder.Polar
open Topology Filter
open scoped Topology

end PermanentBorder.Polar
namespace PermanentBorder.Polar
open Topology Filter
open scoped Topology

end PermanentBorder.Polar

namespace PermanentBorder.Polar
open Topology Set

end PermanentBorder.Polar

end OAI

-- ---- from OAI.Algebra.Determinantal.SmoothSlices ----
namespace OAI

namespace PermanentBorder.SliceParameters

open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.CI
open MvPolynomial Topology
open scoped Topology Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma variable_power_certificate {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] [Finite σ] (I : Ideal (MvPolynomial σ K))
    (hz : ∀ y ∈ zeroLocus L I, y = 0) (j : σ) :
    ∃ n : ℕ, (X j : MvPolynomial σ K)^n ∈ I := by
  have hx : (X j : MvPolynomial σ K) ∈ vanishingIdeal K (zeroLocus L I) := by
    intro y hy
    rw [hz y hy]
    simp
  rw [vanishingIdeal_zeroLocus_eq_radical] at hx
  exact hx

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma intWeight_degree {σ : Type*} (s : σ →₀ ℕ) :
    Finsupp.weight (fun _ : σ => (1 : ℤ)) s = (s.degree : ℤ) := by
  simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]

lemma homogeneous_intWeight {K σ : Type*} [CommSemiring K]
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) :
    f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d := by
  intro s hs
  rw [intWeight_degree]
  have h : s.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf hs
  rw [h]

lemma intWeight_homogeneous {K σ : Type*} [CommSemiring K]
    {f : MvPolynomial σ K} {d : ℕ}
    (hf : f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d) :
    f.IsHomogeneous d := by
  intro s hs
  change Finsupp.weight (fun _ : σ => (1 : ℕ)) s = d
  rw [← Finsupp.degree_eq_weight_one]
  exact_mod_cast (intWeight_degree s ▸ hf hs)

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

section Matrix
variable {K σ ι : Type*} [CommRing K] [Finite σ] [Fintype ι]

omit [Finite σ] [Fintype ι] in
lemma macaulayMatrix_map {L : Type*} [CommRing L] (φ : K →+* L)
    (e : ι → ℤ) (F : ι → MvPolynomial σ K) (D : ℤ) :
    macaulayMatrix e (fun i => map φ (F i)) D = (macaulayMatrix e F D).map φ := by
  classical
  ext s t
  change (map φ (F t.1) * monomial t.2.val 1).coeff s.val =
    φ ((F t.1 * monomial t.2.val 1).coeff s.val)
  rw [← coeff_map, map_mul, map_monomial, φ.map_one]

end Matrix

section Surjectivity
variable {K σ ι : Type*} [Field K] [Finite σ] [Fintype ι]

end Surjectivity
end PermanentBorder.SliceParameters

end OAI

-- ---- from OAI.Algebra.Determinantal.SliceCertificates ----
namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma homogeneous_piece_certificate_all {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] [Fintype σ] (I : Ideal (MvPolynomial σ K))
    (hz : ∀ y ∈ zeroLocus L I, y = 0) :
    ∃ N : ℕ, ∀ D ≥ N, ∀ f : MvPolynomial σ K, f.IsHomogeneous D → f ∈ I := by
  classical
  choose M hM using variable_power_certificate I hz
  refine ⟨(∑ j, M j)+1, ?_⟩
  intro D hD f hf
  rw [← f.support_sum_monomial_coeff]
  apply I.sum_mem
  intro s hs
  apply monomial_mem_of_variable_powers I M hM
  have hd : s.degree = D := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (mem_support_iff.mp hs)
  omega

end PermanentBorder.SliceParameters
namespace PermanentBorder.CI
open MvPolynomial PermanentBorder.SliceParameters
open scoped Classical
variable {ι : Type*} [Fintype ι]

lemma good_certificate_all (H : ι → MvPolynomial (Option ι) ℂ) (l : Option ι → ℂ)
    (e : ι → ℕ) (hh : ∀ i, (H i).IsHomogeneous (e i)) (hg : Good H l) :
    ∃ N : ℕ, ∀ D ≥ N, Function.Surjective
      (macaulayMatrix (fun i => (degrees e i : ℤ)) (bad H l) D).mulVec := by
  have hz : ∀ y ∈ zeroLocus ℂ (Ideal.span (Set.range (bad H l))), y = 0 := by
    intro y hy
    apply (good_iff_bad H l).mp hg y
    intro i
    exact hy _ Ideal.mem_span_range_self
  obtain ⟨N,hN⟩ := homogeneous_piece_certificate_all (Ideal.span (Set.range (bad H l))) hz
  refine ⟨N, fun D hD => ?_⟩
  apply (macaulay_surjective_iff _ _
    (fun i => homogeneous_intWeight (bad_homogeneous H l e hh i)) D).mpr
  intro f hf
  exact hN D hD f (intWeight_homogeneous hf)

lemma good_of_certificate (H : ι → MvPolynomial (Option ι) ℂ) (l : Option ι → ℂ)
    (e : ι → ℕ) (hh : ∀ i, (H i).IsHomogeneous (e i)) (D : ℕ)
    (hM : Function.Surjective (macaulayMatrix (fun i => (degrees e i : ℤ)) (bad H l) D).mulVec) :
    Good H l := by
  apply (good_iff_bad H l).mpr
  exact macaulay_surjective_zero (bad H l) (degrees e) (bad_homogeneous H l e hh) D hM

end PermanentBorder.CI

namespace PermanentBorder.CI
open Polynomial Matrix
open scoped Classical

lemma matrix_right_inverse {K α β : Type*} [Field K] [Fintype α] [Fintype β]
    (A : Matrix α β K) (hA : Function.Surjective A.mulVec) :
    ∃ B : Matrix β α K, A * B = 1 := by
  choose b hb using fun i : α => hA (Pi.single i 1)
  refine ⟨fun j i => b i j, ?_⟩
  ext i j
  change (A.mulVec (b j)) i = (1 : Matrix α α K) i j
  rw [hb]
  simp [Matrix.one_apply, Pi.single_apply]

lemma rank_curve {K α β : Type*} [Field K] [Fintype α] [Fintype β]
    (A : Matrix α β K[X])
    (h0 : Function.Surjective (A.map (evalRingHom (0 : K))).mulVec)
    (h1 : Function.Surjective (A.map (evalRingHom (1 : K))).mulVec) :
    ∃ q : K[X], q.eval 0 = 1 ∧ q.eval 1 = 1 ∧
      ∀ t : K, q.eval t ≠ 0 → Function.Surjective (A.map (evalRingHom t)).mulVec := by
  obtain ⟨b0,hb0⟩ := matrix_right_inverse _ h0
  obtain ⟨b1,hb1⟩ := matrix_right_inverse _ h1
  let B : Matrix β α K[X] := fun i j => C (b0 i j) + X * (C (b1 i j) - C (b0 i j))
  have hB0 : B.map (evalRingHom (0 : K)) = b0 := by
    ext i j
    change (C (b0 i j) + X * (C (b1 i j) - C (b0 i j))).eval _ = _
    simp
  have hB1 : B.map (evalRingHom (1 : K)) = b1 := by
    ext i j
    change (C (b0 i j) + X * (C (b1 i j) - C (b0 i j))).eval _ = _
    simp
  refine ⟨(A*B).det, ?_, ?_, ?_⟩
  · rw [show ((A*B).det).eval 0 = ((A*B).map (evalRingHom (0 : K))).det from
      (evalRingHom (0 : K)).map_det (A*B)]
    rw [Matrix.map_mul, hB0, hb0, Matrix.det_one]
  · rw [show ((A*B).det).eval 1 = ((A*B).map (evalRingHom (1 : K))).det from
      (evalRingHom (1 : K)).map_det (A*B)]
    rw [Matrix.map_mul, hB1, hb1, Matrix.det_one]
  · intro t ht
    have hu : IsUnit ((A*B).map (evalRingHom t)) := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      apply isUnit_iff_ne_zero.mpr
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact ht
    have hs := Matrix.mulVec_surjective_iff_isUnit.mpr hu
    intro v
    obtain ⟨x,hx⟩ := hs v
    refine ⟨(B.map (evalRingHom t)).mulVec x, ?_⟩
    rw [Matrix.mulVec_mulVec]
    simpa only [Matrix.map_mul] using hx

lemma polynomial_nonzero_preconnected (q : ℂ[X]) (hq : q ≠ 0) :
    IsPreconnected {t : ℂ | q.eval t ≠ 0} := by
  have hs : {t : ℂ | q.eval t = 0}.Finite := q.finite_setOfPred_isRoot hq
  have hdim : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  exact (hs.countable.isPathConnected_compl_of_one_lt_rank hdim).isConnected.isPreconnected

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial PermanentBorder.SliceParameters
open scoped Classical
variable {ι : Type*} [Fintype ι]

lemma map_linear {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (l : Option ι → R) : map φ (linear l) = linear (fun j => φ (l j)) := by
  simp [linear]

omit [Fintype ι] in
lemma map_square {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R) :
    (square H l).map (map φ) = square (fun i => map φ (H i)) (fun j => φ (l j)) := by
  ext i j
  cases i <;> simp [square, pderiv_map]

lemma map_bad {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R) (i : Option ι) :
    map φ (bad H l i) = bad (fun i => map φ (H i)) (fun j => φ (l j)) i := by
  cases i with
  | none => simp only [bad, Option.elim'_none, map_mul, RingHom.map_det, RingHom.mapMatrix_apply, map_linear, map_square]
  | some i => rfl

omit [Fintype ι] in
lemma Hline_map (H0 H1 : ι → MvPolynomial (Option ι) ℂ) (t : ℂ) (i : ι) :
    map (Polynomial.evalRingHom t) (Hline H0 H1 i) = Htime H0 H1 t i := by
  have hh : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℂ := by
    ext x; simp
  simp [Hline, Htime, map_map, hh, MvPolynomial.map_id]
omit [Fintype ι] in
lemma lline_eval (l0 l1 : Option ι → ℂ) (t : ℂ) (j : Option ι) :
    (lline l0 l1 j).eval t = ltime l0 l1 t j := by simp [lline, ltime]

omit [Fintype ι] in
lemma Htime_homogeneous (H0 H1 : ι → MvPolynomial (Option ι) ℂ) (e : ι → ℕ)
    (h0 : ∀ i, (H0 i).IsHomogeneous (e i)) (h1 : ∀ i, (H1 i).IsHomogeneous (e i))
    (t : ℂ) (i : ι) : (Htime H0 H1 t i).IsHomogeneous (e i) := by
  apply (h0 i).add
  simpa using (isHomogeneous_C (Option ι) t).mul ((h1 i).sub (h0 i))

lemma good_curve (H0 H1 : ι → MvPolynomial (Option ι) ℂ) (l0 l1 : Option ι → ℂ)
    (e : ι → ℕ) (h0 : ∀ i, (H0 i).IsHomogeneous (e i))
    (h1 : ∀ i, (H1 i).IsHomogeneous (e i)) (hg0 : Good H0 l0) (hg1 : Good H1 l1) :
    ∃ q : Polynomial ℂ, q.eval 0 = 1 ∧ q.eval 1 = 1 ∧
      ∀ t, q.eval t ≠ 0 → Good (Htime H0 H1 t) (ltime l0 l1 t) := by
  obtain ⟨N0,hN0⟩ := good_certificate_all H0 l0 e h0 hg0
  obtain ⟨N1,hN1⟩ := good_certificate_all H1 l1 e h1 hg1
  let D := max N0 N1
  let A := macaulayMatrix (fun i => (degrees e i : ℤ)) (bad (Hline H0 H1) (lline l0 l1)) D
  have hA (t : ℂ) : A.map (Polynomial.evalRingHom t) =
      macaulayMatrix (fun i => (degrees e i : ℤ)) (bad (Htime H0 H1 t) (ltime l0 l1 t)) D := by
    rw [← macaulayMatrix_map]
    congr 1
    funext i
    rw [map_bad]
    congr 2
    · exact funext (Hline_map H0 H1 t)
    · exact funext (lline_eval l0 l1 t)
  have ha0 : Function.Surjective (A.map (Polynomial.evalRingHom (0 : ℂ))).mulVec := by
    rw [hA]; simp only [Htime_zero, ltime_zero]
    exact hN0 D (le_max_left _ _)
  have ha1 : Function.Surjective (A.map (Polynomial.evalRingHom (1 : ℂ))).mulVec := by
    rw [hA]; simp only [Htime_one, ltime_one]
    exact hN1 D (le_max_right _ _)
  obtain ⟨q,hq0,hq1,hq⟩ := rank_curve A ha0 ha1
  refine ⟨q,hq0,hq1,fun t ht => ?_⟩
  apply good_of_certificate _ _ e (Htime_homogeneous H0 H1 e h0 h1 t) D
  rw [← hA]
  exact hq t ht

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial
open scoped Classical
variable {ι : Type*} [Fintype ι]

lemma linear_ltime (l0 l1 : Option ι → ℂ) (t : ℂ) :
    linear (ltime l0 l1 t) = linear l0 + C t * (linear l1 - linear l0) := by
  simp only [linear, ltime, map_add, map_mul, map_sub, add_mul, mul_sub, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [mul_assoc]

lemma normalized_time (H0 H1 : ι → MvPolynomial (Option ι) ℂ)
    (l0 l1 : Option ι → ℂ) (t : ℂ) (i : Option ι) :
    normalized (Htime H0 H1 t) (ltime l0 l1 t) i =
      normalized H0 l0 i + C t * (normalized H1 l1 i - normalized H0 l0 i) := by
  cases i with
  | none => simp only [normalized, Option.elim'_none, linear_ltime]; ring
  | some i => rfl

lemma contDiff_normalized_time (H0 H1 : ι → MvPolynomial (Option ι) ℂ)
    (l0 l1 : Option ι → ℂ) :
    ContDiff ℂ 1 (fun z : ℂ × (Option ι → ℂ) =>
      fun i => eval z.2 (normalized (Htime H0 H1 z.1) (ltime l0 l1 z.1) i)) := by
  apply contDiff_pi.mpr
  intro i
  simp only [normalized_time, map_add, map_mul, map_sub, eval_C]
  exact ((contDiff_eval (normalized H0 l0 i)).comp contDiff_snd).add
    (contDiff_fst.mul (((contDiff_eval (normalized H1 l1 i)).comp contDiff_snd).sub
      ((contDiff_eval (normalized H0 l0 i)).comp contDiff_snd)))

theorem good_card (H : ι → MvPolynomial (Option ι) ℂ) (l : Option ι → ℂ)
    (e : ι → ℕ) (he : ∀ i, 0 < e i) (hh : ∀ i, (H i).IsHomogeneous (e i))
    (hg : Good H l) : Nat.card (Roots H l) = ∏ i, e i := by
  obtain ⟨q,hq0,hq1,hq⟩ := good_curve H (powers e) l coordinate e hh
    (powers_homogeneous e) hg (powers_good e he)
  have hqn : q ≠ 0 := by intro hz; simp [hz] at hq0
  let s : Set ℂ := {t | q.eval t ≠ 0}
  let : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp
    (polynomial_nonzero_preconnected q hqn)
  let a : s := ⟨0,by simp [s,hq0]⟩
  let b : s := ⟨1,by simp [s,hq1]⟩
  have hc := normalized_count_constant (Htime H (powers e)) (ltime l coordinate) e
    (Htime_homogeneous H (powers e) e hh (powers_homogeneous e))
    (contDiff_normalized_time H (powers e) l coordinate) s hq a b
  simpa only [a,b,Htime_zero,Htime_one,ltime_zero,ltime_one,powers_card e he] using hc

end PermanentBorder.CI

namespace PermanentBorder.Polar
open MvPolynomial
open scoped TensorProduct

variable {K R L : Type*} [CommRing K] [CommRing R] [CommRing L]
  [Algebra K R] [Algebra K L] [Algebra R L] [IsScalarTower K R L]

section Generic
universe u v
variable (K : Type u) [Field K] [CharZero K] (ι : Type v)

end Generic

section ChainRule
variable {K L σ : Type*} [CommRing K] [CommRing L] [Algebra K L] [Fintype σ]

end ChainRule
end PermanentBorder.Polar

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.CI
open MvPolynomial
open scoped Classical


theorem solution : type_of% @_root_.OAI.PermanentBorder.CI.good_card := @_root_.OAI.PermanentBorder.CI.good_card
