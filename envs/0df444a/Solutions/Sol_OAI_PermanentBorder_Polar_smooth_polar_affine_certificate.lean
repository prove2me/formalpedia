-- Prove2me | solution 1 for OAI.PermanentBorder.Polar.smooth_polar_affine_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:36:04.558977+00:00
-- url     : https://prove2.me/submissions/2c076a16-a74a-4bc4-bda8-ff5e1aa319cf

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/Model.lean:L59-L111
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Polar.smooth_polar_affine_certificate. The node keeps its source
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
import Definitions.Def_OAI_Algebra_Determinantal_GenericPolars
import Definitions.Def_OAI_Algebra_Determinantal_RankTransfer
import Definitions.Def_OAI_Algebra_Determinantal_Model
import Theorems.Thm_OAI_PermanentBorder_CI_good_card
import Theorems.Thm_OAI_PermanentBorder_CI_good_derivative_invertible
import Theorems.Thm_OAI_PermanentBorder_Polar_exists_normalizer_equiv
import Theorems.Thm_OAI_PermanentBorder_Polar_generic_no_infinity
import Theorems.Thm_OAI_PermanentBorder_Polar_generic_square_isUnit
import Theorems.Thm_OAI_PermanentBorder_SliceParameters_homogeneous_piece_certificate
import Theorems.Thm_OAI_PermanentBorder_SliceParameters_macaulay_surjective_iff
import Theorems.Thm_OAI_PermanentBorder_SliceParameters_macaulay_surjective_zero
import Theorems.Thm_OAI_PermanentBorder_SliceParameters_polynomial_rank_specialize

-- ---- from OAI.Algebra.Determinantal.RegularSections ----
namespace OAI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
section Algebra
variable {R ι : Type*} [CommRing R] [Fintype ι]

end Algebra
section Good
variable {K ι : Type*} [Field K] [Fintype ι]

end Good
end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
variable {ι : Type*} [Fintype ι]

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

lemma normalized_eval_zero_iff (H : ι → MvPolynomial (Option ι) ℂ) (l y : Option ι → ℂ) :
    (fun i => eval y (normalized H l i)) = 0 ↔
      (∀ i, eval y (H i) = 0) ∧ eval y (linear l) = 1 := by
  constructor
  · intro h
    constructor
    · intro i; exact congrFun h (some i)
    · have hh := congrFun h none
      simpa [normalized, sub_eq_zero] using hh
  · rintro ⟨hH,hl⟩
    funext i
    cases i <;> simp [normalized, hH, hl]

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

-- ---- from OAI.Algebra.Determinantal.GenericPolars ----
namespace OAI
namespace PermanentBorder.Polar
open MvPolynomial

section Parametric
variable {K L σ τ : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype σ] [Fintype τ]

end Parametric
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Square
variable {K L τ : Type*} [Field K] [Field L] [Algebra K L] [Fintype τ]
end Square

section GenericSquare
variable {K τ : Type*} [Field K] [CharZero K] [Fintype τ] [DecidableEq τ]
local notation "P" => (Option τ × PolarVars τ)
local notation "E" => GenericField K P

end GenericSquare
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Polynomials
variable {R σ τ : Type*} [CommRing R] [Fintype σ] [Fintype τ]

omit [Fintype τ] in
lemma polarPolynomial_homogeneous (w : τ → σ → R) {f : MvPolynomial σ R} {r : ℕ}
    (hf : f.IsHomogeneous r) (i : τ) : (polarPolynomial w f i).IsHomogeneous (r-1) := by
  apply IsHomogeneous.sum
  intro j _
  simpa using (isHomogeneous_C σ (w i j)).mul hf.pderiv

omit [Fintype τ] in
lemma linearPolynomial_homogeneous (l : σ → R) : (linearPolynomial l).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _
  simpa using (isHomogeneous_C σ (l j)).mul (isHomogeneous_X R j)

omit [Fintype σ] in
lemma det_row_homogeneous {n : Type*} [Fintype n] [DecidableEq n]
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

lemma squarePolynomial_homogeneous [DecidableEq τ] (w : τ → PolarVars τ → R) (l : PolarVars τ → R)
    {f : MvPolynomial (PolarVars τ) R} {r : ℕ} (hf : f.IsHomogeneous r) :
    (squarePolynomial w l f).det.IsHomogeneous (∑ i, squareDegrees τ r i) := by
  classical
  apply det_row_homogeneous
  intro i j
  rcases i with _ | (_ | i)
  · exact hf.pderiv
  · exact isHomogeneous_C _ _
  · exact (polarPolynomial_homogeneous w hf i).pderiv

lemma badPolarSystem_homogeneous (w : τ → PolarVars τ → R) (l : PolarVars τ → R)
    {f : MvPolynomial (PolarVars τ) R} {r : ℕ} (hf : f.IsHomogeneous r) (i : PolarVars τ) :
    (badPolarSystem w l f i).IsHomogeneous (badPolarDegrees τ r i) := by
  classical
  rcases i with _ | (_ | i)
  · exact hf
  · exact (linearPolynomial_homogeneous l).mul (squarePolynomial_homogeneous w l hf)
  · exact polarPolynomial_homogeneous w hf i

end Polynomials

section Evaluation
variable {K L σ τ : Type*} [Field K] [Field L] [Algebra K L] [Fintype σ] [Fintype τ]

omit [Fintype τ] in
lemma eval_polarPolynomial (w : τ → σ → L) (f : MvPolynomial σ K)
    (y : σ → L) (i : τ) :
    eval y (polarPolynomial w (map (algebraMap K L) f) i) = polarValue w f y i := by
  simp [polarPolynomial, polarValue, pderiv_map, eval_map, aeval_def]

lemma eval_linearPolynomial (l : σ → L) (y : σ → L) :
    eval y (linearPolynomial l) = ∑ j, l j * y j := by
  simp [linearPolynomial]

lemma eval_squarePolynomial (w : τ → PolarVars τ → L) (l : PolarVars τ → L)
    (f : MvPolynomial (PolarVars τ) K) (y : PolarVars τ → L) :
    (squarePolynomial w l (map (algebraMap K L) f)).map (eval y) = squareJacobian w l f y := by
  classical
  ext i j
  rcases i with _ | (_ | i)
  · simp [squarePolynomial, squareJacobian, pderiv_map, eval_map, aeval_def]
  · simp [squarePolynomial, squareJacobian]
  · simp [squarePolynomial, squareJacobian, polarPolynomial, polarGradient, pderiv_map,
      eval_map, aeval_def]

end Evaluation
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Map
variable {R S σ τ : Type*} [CommRing R] [CommRing S] [Fintype σ] [Fintype τ]

omit [Fintype τ] in
lemma map_polarPolynomial (φ : R →+* S) (w : τ → σ → R) (f : MvPolynomial σ R) (i : τ) :
    map φ (polarPolynomial w f i) = polarPolynomial (fun i j => φ (w i j)) (map φ f) i := by
  simp [polarPolynomial, pderiv_map]

lemma map_linearPolynomial (φ : R →+* S) (l : σ → R) :
    map φ (linearPolynomial l) = linearPolynomial (fun j => φ (l j)) := by
  simp [linearPolynomial]

lemma map_squarePolynomial (φ : R →+* S) (w : τ → PolarVars τ → R)
    (l : PolarVars τ → R) (f : MvPolynomial (PolarVars τ) R) :
    (squarePolynomial w l f).map (map φ) =
      squarePolynomial (fun i j => φ (w i j)) (fun j => φ (l j)) (map φ f) := by
  classical
  funext i j
  rcases i with _ | (_ | i)
  · simp [squarePolynomial, pderiv_map]
  · simp [squarePolynomial]
  · simp only [Matrix.map_apply, squarePolynomial, ← pderiv_map, map_polarPolynomial]

lemma map_badPolarSystem (φ : R →+* S) (w : τ → PolarVars τ → R)
    (l : PolarVars τ → R) (f : MvPolynomial (PolarVars τ) R) (i : PolarVars τ) :
    map φ (badPolarSystem w l f i) =
      badPolarSystem (fun i j => φ (w i j)) (fun j => φ (l j)) (map φ f) i := by
  classical
  rcases i with _ | (_ | i)
  · rfl
  · simp only [badPolarSystem, map_mul, map_linearPolynomial, RingHom.map_det,
      RingHom.mapMatrix_apply, map_squarePolynomial]
  · exact map_polarPolynomial φ w f i

end Map
end PermanentBorder.Polar

end OAI

-- ---- from OAI.Algebra.Determinantal.RankTransfer ----
namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.Polar
open MvPolynomial Matrix PermanentBorder.SliceParameters

lemma smooth_extension {K L σ : Type*} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]
    [Fintype σ] (f : MvPolynomial σ K)
    (hs : ∀ y : σ → K, eval y f = 0 → (∀ j, eval y (pderiv j f) = 0) → y = 0)
    (y : σ → L) (hf : aeval y f = 0) (hd : ∀ j, aeval y (pderiv j f) = 0) : y = 0 := by
  classical
  let F : Option σ → MvPolynomial σ K := fun i => match i with
    | none => f
    | some j => pderiv j f
  let I := Ideal.span (Set.range F)
  have hz : ∀ x ∈ zeroLocus K I, x = 0 := by
    intro x hx
    apply hs x
    · exact hx _ (Ideal.subset_span ⟨none,rfl⟩)
    · intro j
      exact hx _ (Ideal.subset_span ⟨some j,rfl⟩)
  have hy : y ∈ zeroLocus L I := by
    rw [zeroLocus_span]
    rintro _ ⟨i,rfl⟩
    cases i with
    | none => exact hf
    | some j => exact hd j
  ext j
  obtain ⟨n,hn⟩ := variable_power_certificate I hz j
  have hpow : y j ^ n = 0 := by simpa using hy _ hn
  by_contra h
  exact pow_ne_zero n h hpow

section Generic
variable {K τ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Fintype τ]
local notation "P" => (Option τ × PolarVars τ)
local notation "E" => GenericField K P

lemma generic_bad_zero (f : MvPolynomial (PolarVars τ) K) {r : ℕ}
    (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → K, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0)
    (y : PolarVars τ → E)
    (hy : ∀ i, eval y (badPolarSystem genericDirections genericLinear (map (algebraMap K E) f) i) = 0) :
    y = 0 := by
  classical
  by_contra hyn
  have hf : aeval y f = 0 := by simpa [badPolarSystem, eval_map, aeval_def] using hy none
  have hp : ∀ i, polarValue genericDirections f y i = 0 := by
    intro i
    simpa only [badPolarSystem, eval_polarPolynomial] using hy (some (some i))
  have hg : ∃ j, aeval y (pderiv j f) ≠ 0 := by
    by_contra h
    exact hyn (smooth_extension f hs y hf (by simpa only [not_exists, not_not] using h))
  have hn : ∑ j, genericLinear j * y j ≠ 0 := fun h =>
    hyn (generic_no_infinity f hh y hf hp hg h)
  have hu := generic_square_isUnit f hh y hf hp hyn hg
  have hj : (squareJacobian genericDirections genericLinear f y).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have hb := hy (some none)
  simp only [badPolarSystem, map_mul, eval_linearPolynomial, RingHom.map_det,
    RingHom.mapMatrix_apply, eval_squarePolynomial] at hb
  exact (mul_ne_zero hn hj) hb

omit [CharZero K] [IsAlgClosed K] in
lemma universalBadPolar_specialize {L : Type*} [Field L] [Algebra K L]
    (f : MvPolynomial (PolarVars τ) K) (w : P → L) (i : PolarVars τ) :
    map (eval₂Hom (algebraMap K L) w) (universalBadPolar f i) =
      badPolarSystem (fun i j => w (some i,j)) (fun j => w (none,j))
        (map (algebraMap K L) f) i := by
  rw [universalBadPolar, map_badPolarSystem, MvPolynomial.map_map]
  have hc : (eval₂Hom (algebraMap K L) w).comp C = algebraMap K L := by ext; simp
  rw [hc]
  simp only [MvPolynomial.eval₂Hom_X']

theorem exists_good_polar_certificate (f : MvPolynomial (PolarVars τ) K) {r : ℕ}
    (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → K, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ∃ w : τ → PolarVars τ → K, ∃ l : PolarVars τ → K, ∃ D : ℕ,
      Function.Surjective (macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ))
        (badPolarSystem w l f) D).mulVec := by
  classical
  let F := badPolarSystem (genericDirections (K := K) (τ := τ)) genericLinear
    (map (algebraMap K E) f)
  have hhom (i : PolarVars τ) : (F i).IsHomogeneous (badPolarDegrees τ r i) :=
    badPolarSystem_homogeneous _ _ (hh.map _) i
  have hz : ∀ y ∈ zeroLocus E (Ideal.span (Set.range F)), y = 0 := by
    intro y hy
    apply generic_bad_zero f hh hs y
    intro i
    exact hy _ Ideal.mem_span_range_self
  obtain ⟨D,hD⟩ := homogeneous_piece_certificate (Ideal.span (Set.range F)) hz
  have hM : Function.Surjective
      (macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ)) F D).mulVec := by
    apply (macaulay_surjective_iff _ _ (fun i => homogeneous_intWeight (hhom i)) D).mpr
    intro p hp
    exact hD p (intWeight_homogeneous hp)
  let M := macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ)) (universalBadPolar f) D
  have hMa : Function.Surjective (M.map (eval₂Hom (algebraMap K E) (genericParameter K P))).mulVec := by
    have he : M.map (eval₂Hom (algebraMap K E) (genericParameter K P)) =
        macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ)) F D := by
      rw [← macaulayMatrix_map]
      apply congrArg (fun Q => macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ)) Q D)
      funext i
      exact universalBadPolar_specialize f (genericParameter K P) i
    rwa [he]
  obtain ⟨a,ha⟩ := polynomial_rank_specialize M (genericParameter K P) hMa
  refine ⟨fun i j => a (some i,j), fun j => a (none,j), D, ?_⟩
  have he : M.map (eval₂Hom (RingHom.id K) a) =
      macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ))
        (badPolarSystem (fun i j => a (some i,j)) (fun j => a (none,j)) f) D := by
    rw [← macaulayMatrix_map]
    apply congrArg (fun Q => macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ)) Q D)
    funext i
    simpa only [Algebra.algebraMap_self, MvPolynomial.map_id] using universalBadPolar_specialize f a i
  rwa [he] at ha

end Generic
end PermanentBorder.Polar

namespace PermanentBorder.Polar
open MvPolynomial Matrix PermanentBorder.SliceParameters
open scoped Classical
variable {τ : Type*} [Fintype τ]

lemma hypersurfacePolars_homogeneous (w : τ → PolarVars τ → ℂ)
    {f : MvPolynomial (PolarVars τ) ℂ} {r : ℕ} (hh : f.IsHomogeneous r) (i : Option τ) :
    (hypersurfacePolars w f i).IsHomogeneous (hypersurfaceDegrees r i) := by
  cases i with
  | none => exact hh
  | some i => exact polarPolynomial_homogeneous w hh i

lemma hypersurfacePolars_square (w : τ → PolarVars τ → ℂ) (l : PolarVars τ → ℂ)
    (f : MvPolynomial (PolarVars τ) ℂ) :
    CI.square (hypersurfacePolars w f) l =
      (squarePolynomial w l f).submatrix swapFirstRows id := by
  ext i j
  rcases i with _ | (_ | i) <;>
    simp [CI.square, hypersurfacePolars, squarePolynomial, Matrix.submatrix, swapFirstRows]

lemma determinant_permutation_ne_zero {n : Type*} [Fintype n]
    (d₁ d₂ : DecidableEq n) (A B : Matrix n n ℂ) (e : Equiv.Perm n)
    (he : B = A.submatrix e id) (ha : @Matrix.det n d₁ _ ℂ _ A ≠ 0) :
    @Matrix.det n d₂ _ ℂ _ B ≠ 0 := by
  subst B
  cases Subsingleton.elim d₁ d₂
  rw [Matrix.det_permute]
  exact mul_ne_zero (by exact_mod_cast (Equiv.Perm.sign e).ne_zero) ha

lemma polar_certificate_good (w : τ → PolarVars τ → ℂ) (l : PolarVars τ → ℂ)
    (f : MvPolynomial (PolarVars τ) ℂ) {r : ℕ} (hh : f.IsHomogeneous r) (D : ℕ)
    (hM : Function.Surjective (macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ))
      (badPolarSystem w l f) D).mulVec) : CI.Good (hypersurfacePolars w f) l := by
  classical
  have hz := macaulay_surjective_zero (badPolarSystem w l f) (badPolarDegrees τ r)
    (badPolarSystem_homogeneous w l hh) D hM
  intro y hn hy
  have hp : eval y (linearPolynomial l) * ((squarePolynomial w l f).map (eval y)).det ≠ 0 := by
    intro he
    apply hn (hz y ?_)
    rintro (_ | (_ | i))
    · exact hy none
    · simpa only [badPolarSystem, map_mul, RingHom.map_det, RingHom.mapMatrix_apply] using he
    · exact hy (some i)
  refine ⟨(mul_ne_zero_iff.mp hp).1, ?_⟩
  have he : (CI.square (hypersurfacePolars w f) l).map (eval y) =
      ((squarePolynomial w l f).map (eval y)).submatrix swapFirstRows id := by
    rw [hypersurfacePolars_square]
    rfl
  exact determinant_permutation_ne_zero _ _ _ _ swapFirstRows he (mul_ne_zero_iff.mp hp).2

theorem smooth_polar_count (f : MvPolynomial (PolarVars τ) ℂ) {r : ℕ} (hr : 2 ≤ r)
    (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ∃ w : τ → PolarVars τ → ℂ, ∃ l : PolarVars τ → ℂ,
      CI.Good (hypersurfacePolars w f) l ∧
      Nat.card (CI.Roots (hypersurfacePolars w f) l) = r * (r-1) ^ Fintype.card τ := by
  obtain ⟨w,l,D,hD⟩ := exists_good_polar_certificate f hh hs
  have hg := polar_certificate_good w l f hh D hD
  refine ⟨w,l,hg,?_⟩
  have hc := CI.good_card (hypersurfacePolars w f) l (hypersurfaceDegrees r)
    (by rintro (_ | i) <;> simp only [hypersurfaceDegrees,Option.elim'_none,Option.elim'_some] <;> omega)
    (hypersurfacePolars_homogeneous w hh) hg
  simpa [hypersurfaceDegrees] using hc

end PermanentBorder.Polar

namespace PermanentBorder.Polar
open scoped Classical
variable {ι : Type*} [Fintype ι]

lemma affineNormChart_hasFDerivAt
    (e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ)) (z : ι → ℂ) :
    HasFDerivAt (affineNormChart e)
      (e.symm.toContinuousLinearMap.comp optionInsert) z := by
  have h : HasFDerivAt (fun z : ι → ℂ => Option.elim' 1 z) optionInsert z := by
    apply hasFDerivAt_pi.mpr
    rintro (_ | i)
    · exact hasFDerivAt_const _ _
    · exact (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).hasFDerivAt
  exact e.symm.hasFDerivAt.comp z h

omit [Fintype ι] in
lemma exists_chart_preimage
    (e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ)) {y : Option ι → ℂ}
    (hy : e y none = 1) : ∃ z, affineNormChart e z = y := by
  refine ⟨fun i => e y (some i), ?_⟩
  apply e.injective
  rw [affineNormChart, e.apply_symm_apply]
  funext i
  cases i <;> simp [hy]

end PermanentBorder.Polar

end OAI

-- ---- from OAI.Algebra.Determinantal.Model ----
namespace OAI

namespace PermanentBorder.Polar
open scoped Classical
variable {ι : Type*} [Fintype ι]

lemma isInvertible_of_injective (D : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (hD : Function.Injective D) : D.IsInvertible := by
  have hs : Function.Surjective D := (LinearMap.injective_iff_surjective).mp hD
  let e := LinearEquiv.ofBijective D.toLinearMap ⟨hD,hs⟩
  exact ⟨e.toContinuousLinearEquiv, rfl⟩

lemma normalizer_simple_restrict
    (e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ))
    (F : (Option ι → ℂ) → (Option ι → ℂ))
    (hfirst : ∀ y, F y none = e y none - 1) (z : ι → ℂ)
    (hF : DifferentiableAt ℂ F (affineNormChart e z))
    (hs : (fderiv ℂ F (affineNormChart e z)).IsInvertible) :
    (fderiv ℂ (fun z i => F (affineNormChart e z) (some i)) z).IsInvertible := by
  let D := (fderiv ℂ F (affineNormChart e z)).comp
    (e.symm.toContinuousLinearMap.comp optionInsert)
  have hfull : HasFDerivAt (fun z => F (affineNormChart e z)) D z :=
    hF.hasFDerivAt.comp z (affineNormChart_hasFDerivAt e z)
  let E : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
    ContinuousLinearMap.pi (fun i => (ContinuousLinearMap.proj (some i)).comp D)
  have hred : HasFDerivAt (fun z i => F (affineNormChart e z) (some i)) E z :=
    hasFDerivAt_pi.mpr (fun i => (ContinuousLinearMap.proj (some i) : (Option ι → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp z hfull)
  have hzero : (fun z => F (affineNormChart e z) none) = fun _ => (0 : ℂ) := by
    funext z
    rw [hfirst, affineNormChart, e.apply_symm_apply]
    simp
  have hnone : (ContinuousLinearMap.proj none).comp D = 0 := by
    have hd := (ContinuousLinearMap.proj none : (Option ι → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp z hfull
    change HasFDerivAt (fun z => F (affineNormChart e z) none) _ z at hd
    rw [hzero] at hd
    exact hd.unique (hasFDerivAt_const _ _)
  rw [hred.fderiv]
  apply isInvertible_of_injective
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hd : D v = 0 := by
    funext i
    cases i with
    | none => exact congrArg (fun T : (ι → ℂ) →L[ℂ] ℂ => T v) hnone
    | some i => exact congrFun hv i
  have he : e.symm (optionInsert v) = 0 := hs.injective (hd.trans (map_zero _).symm)
  have hi : optionInsert v = 0 := e.symm.injective (he.trans (map_zero _).symm)
  exact funext (fun i => congrFun hi (some i))

end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial
open scoped Classical
variable {τ : Type*} [Fintype τ]

theorem smooth_polar_affine_certificate (f : MvPolynomial (PolarVars τ) ℂ)
    {r : ℕ} (hr : 2 ≤ r) (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ∃ w : τ → PolarVars τ → ℂ,
    ∃ e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ),
    ∃ x : Fin (r * (r-1)^Fintype.card τ) → Option τ → ℂ,
      Function.Injective x ∧
      ∀ i, (fun j => eval (affineNormChart e (x i)) (hypersurfacePolars w f j)) = 0 ∧
        (fderiv ℂ (fun z j => eval (affineNormChart e z)
          (hypersurfacePolars w f j)) (x i)).IsInvertible := by
  classical
  obtain ⟨w,l,hg,hcard⟩ := smooth_polar_count f hr hh hs
  let R := CI.Roots (hypersurfacePolars w f) l
  have hpos : 0 < Nat.card R := by
    rw [show Nat.card R = _ from hcard]
    exact Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  have : Finite R := (Nat.card_pos_iff.mp hpos).2
  let : Fintype R := Fintype.ofFinite R
  have hcard' : Fintype.card R = r * (r-1)^Fintype.card τ := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  let q : Fin (r * (r-1)^Fintype.card τ) ≃ R := (Fintype.equivFinOfCardEq hcard').symm
  have hl : l ≠ 0 := by
    intro hz
    obtain ⟨y⟩ := (Nat.card_pos_iff.mp hpos).1
    have hy := y.property.2
    simp [CI.eval_linear, hz] at hy
  obtain ⟨e,he⟩ := exists_normalizer_equiv l hl
  have hy (i : Fin (r * (r-1)^Fintype.card τ)) : e (q i).val none = 1 := by
    rw [he, ← CI.eval_linear]
    exact (q i).property.2
  choose x hx using fun i => exists_chart_preimage e (hy i)
  refine ⟨w,e,x,?_,?_⟩
  · intro i j hij
    apply q.injective
    apply Subtype.ext
    rw [← hx i, ← hx j, hij]
  · intro i
    have hz : (fun j => eval (q i).val (CI.normalized (hypersurfacePolars w f) l j)) = 0 :=
      (CI.normalized_eval_zero_iff _ _ _).mpr (q i).property
    constructor
    · rw [hx i]
      exact funext (q i).property.1
    · have hfirst (y : PolarVars τ → ℂ) :
          eval y (CI.normalized (hypersurfacePolars w f) l none) = e y none - 1 := by
        change eval y (CI.linear l - 1) = _
        rw [map_sub, map_one, CI.eval_linear, he]
      apply normalizer_simple_restrict e
        (fun y j => eval y (CI.normalized (hypersurfacePolars w f) l j)) hfirst (x i)
      · exact ((contDiff_pi.mpr (fun j => CI.contDiff_eval
          (CI.normalized (hypersurfacePolars w f) l j))).differentiable (by decide)) _
      · rw [hx i]
        exact CI.good_derivative_invertible _ _ _ hg hz

end PermanentBorder.Polar

namespace PermanentBorder

open Filter
open scoped Topology

end PermanentBorder

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

section FixedCoefficientSpace
variable {σ τ : Type*} [Fintype σ]

end FixedCoefficientSpace

section DeterminantDegree
variable {σ : Type*} [Fintype σ]

end DeterminantDegree

section AffineSubstitution
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

end AffineSubstitution
end PermanentBorder

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

section ScalarNormalization
variable {σ : Type*} [Fintype σ]

end ScalarNormalization
end PermanentBorder

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.Polar
open MvPolynomial
open scoped Classical


theorem solution : type_of% @_root_.OAI.PermanentBorder.Polar.smooth_polar_affine_certificate := @_root_.OAI.PermanentBorder.Polar.smooth_polar_affine_certificate
