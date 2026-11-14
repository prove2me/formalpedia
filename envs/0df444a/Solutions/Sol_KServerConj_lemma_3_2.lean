-- Prove2me | solution 1 for KServerConj.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T03:50:19.008871+00:00
-- url     : https://prove2.me/submissions/a7278493-4a64-4e90-8374-dec3f5f42467

import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Definitions.Def_KServerConj_minorVal
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.Algebra.BigOperators.WithTop

set_option autoImplicit false

open scoped BigOperators

theorem det_mul_det_updateCol
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A B : Matrix ι ι R) (j : ι) (v : ι → R) :
    A.det * (B.updateCol j v).det =
      ∑ i, (A.updateCol i v).det *
        (B.updateCol j (fun r => A r i)).det := by
  have h : A.det • v =
      ∑ i, (A.updateCol i v).det • (fun r => A r i) := by
    rw [← Matrix.mulVec_cramer A v]
    ext r
    simp only [Matrix.mulVec, dotProduct, Matrix.cramer_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have h' := congrArg (fun w : ι → R => B.cramer w j) h
  simp only [map_smul, map_sum] at h'
  simpa only [map_smul, map_sum, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.cramer_apply] using h'

open scoped BigOperators

namespace DetValuationMilestone

def prependColumn {n : ℕ} {R : Type*} (v : Fin (n + 1) → R)
    (W : Matrix (Fin (n + 1)) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun r j => Fin.cases (v r) (fun j => W r j) j

theorem updateCol_prepend {n : ℕ} {R : Type*}
    (v w : Fin (n + 1) → R) (W : Matrix (Fin (n + 1)) (Fin n) R) :
    (prependColumn v W).updateCol 0 w = prependColumn w W := by
  ext r j
  cases j using Fin.cases <;> simp [prependColumn, Matrix.updateCol]

theorem det_prepend_single {n : ℕ} {R : Type*} [CommRing R]
    (W : Matrix (Fin (n + 1)) (Fin n) R) :
    (prependColumn (Pi.single 0 1) W).det = (W.submatrix Fin.succ id).det := by
  rw [Matrix.det_succ_column_zero]
  simp [prependColumn, Matrix.submatrix, Pi.single_apply, mul_ite, ite_mul]

theorem det_mul_det_prepend {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (v : Fin (n + 1) → R) (W : Matrix (Fin (n + 1)) (Fin n) R) :
    A.det * (prependColumn v W).det =
      ∑ i, (A.updateCol i v).det * (prependColumn (fun r => A r i) W).det := by
  simpa only [updateCol_prepend] using det_mul_det_updateCol A (prependColumn v W) 0 v

theorem det_prepend_smul {n : ℕ} {R : Type*} [CommRing R]
    (c : R) (v : Fin (n + 1) → R) (W : Matrix (Fin (n + 1)) (Fin n) R) :
    (prependColumn (c • v) W).det = c * (prependColumn v W).det := by
  simpa only [updateCol_prepend] using Matrix.det_updateCol_smul (prependColumn v W) 0 c v

theorem prepend_submatrix {n : ℕ} {R ι : Type*}
    (H : Matrix (Fin (n + 1)) ι R) (x : ι) (y : Fin n → ι) :
    prependColumn (fun r => H r x) (H.submatrix id y) =
      H.submatrix id (Fin.cases x y) := by
  ext r j
  cases j using Fin.cases <;> rfl

theorem projected_minor_identity {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (y : Fin n → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i))) :
    A.det * (H.submatrix Fin.succ y).det =
      ∑ i, (A.updateCol i (Pi.single 0 1)).det * c i *
        (prependColumn (fun r => H r (x i)) (H.submatrix id y)).det := by
  simpa only [det_prepend_single, Matrix.submatrix_submatrix, Function.comp_id,
    Function.id_comp, hcol, det_prepend_smul, mul_assoc] using
      det_mul_det_prepend A (Pi.single 0 1) (H.submatrix id y)


theorem exists_nonzero_projected_minor {n : ℕ} {R ι : Type*} [CommRing R]
    (H : Matrix (Fin (n + 1)) ι R) (x : Fin (n + 1) → ι)
    (hdet : (H.submatrix id x).det ≠ 0) :
    ∃ y : Fin n → ι, (H.submatrix Fin.succ y).det ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hdet
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  simp only [Matrix.submatrix_submatrix, Function.id_comp, h, mul_zero]

theorem nonzero_unscaled_minor {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i)))
    (hdet : A.det ≠ 0) : (H.submatrix id x).det ≠ 0 := by
  have hA : A = Matrix.of (fun r i => c i * (H.submatrix id x) r i) :=
    funext fun r => funext fun i => congrFun (hcol i) r
  rw [hA, Matrix.det_mul_row c (H.submatrix id x)] at hdet
  exact right_ne_zero_of_mul hdet

theorem det_eq_sum_scaled_cramer {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i))) :
    A.det = ∑ i, (A.updateCol i (Pi.single 0 1)).det * c i * H 0 (x i) := by
  have hentry : ∀ r i, A r i = c i * H r (x i) :=
    fun r i => congrFun (hcol i) r
  simpa [Matrix.mulVec, dotProduct, Matrix.cramer_apply, hentry,
    mul_comm, mul_left_comm, mul_assoc] using
      (congrFun (Matrix.mulVec_cramer A (Pi.single 0 1)) 0).symm

theorem exists_nonzero_scaled_cramer {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i)))
    (hdet : A.det ≠ 0) :
    ∃ i, (A.updateCol i (Pi.single 0 1)).det * c i ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hdet (by
    simpa only [h, zero_mul, Finset.sum_const_zero] using det_eq_sum_scaled_cramer A H x c hcol)


end DetValuationMilestone

open scoped BigOperators

/-!
Abstract valuation arithmetic for the division-free projected-minor identity.

The valuation laws are explicit hypotheses. In particular, this file does not
construct the coefficient field or assume a k-server growth theorem. Values of
zero terms stay in `WithTop ℝ` throughout; subtraction occurs only between the
finite real numbers extracted from nonzero witnesses.
-/

namespace DetValuationMilestone

/-- A uniform lower bound on finitely many terms bounds the valuation of their sum,
including the empty sum and cancellations. -/
theorem valuation_sum_lower_bound
    {R ι : Type*} [AddCommMonoid R]
    (ν : R → WithTop ℝ)
    (hzero : ν 0 = ⊤)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (s : Finset ι) (f : ι → R) (c : WithTop ℝ)
    (hf : ∀ i ∈ s, c ≤ ν (f i)) :
    c ≤ ν (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hzero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (le_min (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))).trans (hadd _ _)

/-- The arithmetic consequence of `D * P = ∑ i, a i * M i`. The explicitly real
value `δ` permits cancellation even when `P` or summands vanish. -/
theorem valuation_lower_bound_of_minor_identity
    {R ι : Type*} [Semiring R] [Fintype ι]
    (ν : R → WithTop ℝ)
    (hzero : ν 0 = ⊤)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (D P : R) (a M : ι → R) (δ α μ : ℝ)
    (hD : ν D = (δ : WithTop ℝ))
    (hid : D * P = ∑ i, a i * M i)
    (ha : ∀ i, (α : WithTop ℝ) ≤ ν (a i))
    (hM : ∀ i, (μ : WithTop ℝ) ≤ ν (M i)) :
    ((α + μ - δ : ℝ) : WithTop ℝ) ≤ ν P := by
  have hsum : ((α + μ : ℝ) : WithTop ℝ) ≤ ν (∑ i, a i * M i) := by
    apply valuation_sum_lower_bound ν hzero hadd
    intro i _
    simpa only [WithTop.coe_add, hmul] using add_le_add (ha i) (hM i)
  rw [← hid, hmul, hD] at hsum
  apply WithTop.le_of_add_le_add_left (x := (δ : WithTop ℝ)) (by simp)
  simpa only [← WithTop.coe_add,
    show δ + (α + μ - δ) = α + μ by linarith] using hsum

/-- Evaluate the pointwise estimate at an attained finite projected-minor minimum.
The lower bounds on coefficients and full minors may in particular be their minima. -/
theorem minValue_growth_of_minor_identities
    {R ι κ : Type*} [Semiring R] [Fintype ι]
    (ν : R → WithTop ℝ)
    (hzero : ν 0 = ⊤)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (D : R) (a : ι → R) (P : κ → R) (M : ι → κ → R)
    (δ α μ μhat : ℝ)
    (hD : ν D = (δ : WithTop ℝ))
    (hid : ∀ y, D * P y = ∑ i, a i * M i y)
    (ha : ∀ i, (α : WithTop ℝ) ≤ ν (a i))
    (hM : ∀ i y, (μ : WithTop ℝ) ≤ ν (M i y))
    (hmin : ∃ y, ν (P y) = (μhat : WithTop ℝ)) :
    α - δ ≤ μhat - μ := by
  obtain ⟨y, hy⟩ := hmin
  have h := valuation_lower_bound_of_minor_identity ν hzero hmul hadd
    D (P y) a (fun i => M i y) δ α μ hD (hid y) ha (fun i => hM i y)
  rw [hy, WithTop.coe_le_coe] at h
  linarith

/-- A finite family containing a nonzero element has a real minimum valuation;
the minimum is attained at a nonzero element. -/
theorem exists_real_minimum_of_nonzero
    {R ι : Type*} [Zero R] [Fintype ι]
    (ν : R → WithTop ℝ)
    (htop : ∀ x, ν x = ⊤ ↔ x = 0)
    (f : ι → R) (hnonzero : ∃ i, f i ≠ 0) :
    ∃ μ : ℝ,
      (Finset.univ.inf fun i => ν (f i)) = (μ : WithTop ℝ) ∧
      (∀ i, (μ : WithTop ℝ) ≤ ν (f i)) ∧
      (∃ i, ν (f i) = (μ : WithTop ℝ) ∧ f i ≠ 0) := by
  classical
  obtain ⟨i, hi⟩ := hnonzero
  have hfinite : (Finset.univ.inf fun i => ν (f i)) ≠ ⊤ := by
    exact ne_of_lt ((Finset.inf_le (Finset.mem_univ i)).trans_lt
      (lt_top_iff_ne_top.mpr fun h => hi ((htop _).mp h)))
  obtain ⟨μ, hμ⟩ := WithTop.ne_top_iff_exists.mp hfinite
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf (Finset.univ : Finset ι)
    ⟨i, Finset.mem_univ i⟩ (fun j => ν (f j))
  exact ⟨μ, hμ.symm, fun j => hμ.trans_le (Finset.inf_le (Finset.mem_univ j)),
    j, hj.symm.trans hμ.symm, fun hz => hfinite (hj.trans ((htop _).mpr hz))⟩

/-- Canonical finite minima satisfy the growth estimate. Nonzero witnesses make
all four real quantities finite. A determinant in the identity may be zero or an
actual member of the full-minor family, covering repeated-column determinants. -/
theorem canonical_minValue_growth
    {R ι κ η : Type*} [Semiring R] [Fintype ι] [Fintype κ] [Fintype η]
    (ν : R → WithTop ℝ)
    (htop : ∀ x, ν x = ⊤ ↔ x = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (D : R) (a : ι → R) (P : κ → R) (F : η → R) (M : ι → κ → R)
    (hD : D ≠ 0)
    (ha_nonzero : ∃ i, a i ≠ 0)
    (hP_nonzero : ∃ y, P y ≠ 0)
    (hF_nonzero : ∃ z, F z ≠ 0)
    (hid : ∀ y, D * P y = ∑ i, a i * M i y)
    (hM : ∀ i y, M i y = 0 ∨ ∃ z, M i y = F z) :
    ∃ δ α μ μhat : ℝ,
      ν D = (δ : WithTop ℝ) ∧
      (Finset.univ.inf fun i => ν (a i)) = (α : WithTop ℝ) ∧
      (Finset.univ.inf fun z => ν (F z)) = (μ : WithTop ℝ) ∧
      (Finset.univ.inf fun y => ν (P y)) = (μhat : WithTop ℝ) ∧
      α - δ ≤ μhat - μ := by
  obtain ⟨δ, hδ⟩ := WithTop.ne_top_iff_exists.mp (fun h => hD ((htop _).mp h))
  obtain ⟨α, hα, ha, _⟩ := exists_real_minimum_of_nonzero ν htop a ha_nonzero
  obtain ⟨μ, hμ, hF, _⟩ := exists_real_minimum_of_nonzero ν htop F hF_nonzero
  obtain ⟨μhat, hμhat, _, y, hy, _⟩ :=
    exists_real_minimum_of_nonzero ν htop P hP_nonzero
  exact ⟨δ, α, μ, μhat, hδ.symm, hα, hμ, hμhat,
    minValue_growth_of_minor_identities ν ((htop 0).mpr rfl) hmul hadd
      D a P M δ α μ μhat hδ.symm hid ha
      (fun i y => (hM i y).elim
        (fun hz => by simp [hz, (htop 0).mpr rfl])
        (fun ⟨z, hz⟩ => by simpa only [hz] using hF z))
      ⟨y, hy⟩⟩

end DetValuationMilestone

open scoped BigOperators

namespace DetValuationMilestone

/-- The projected-minor growth inequality with canonical finite real minima.
All nonzero-minor witnesses follow from the single assumption `A.det ≠ 0`.
The full-minor family is indexed by arbitrary tuples; repeated columns have
zero determinant and hence valuation `⊤`.
-/
theorem canonical_projected_minValue_growth
    {n : ℕ} {R ι : Type*} [CommRing R] [Fintype ι]
    (ν : R → WithTop ℝ)
    (htop : ∀ x, ν x = ⊤ ↔ x = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i)))
    (hdet : A.det ≠ 0) :
    ∃ δ α μ μhat : ℝ,
      ν A.det = (δ : WithTop ℝ) ∧
      (Finset.univ.inf fun i => ν ((A.updateCol i (Pi.single 0 1)).det * c i)) =
        (α : WithTop ℝ) ∧
      (Finset.univ.inf fun z : Fin (n + 1) → ι => ν (H.submatrix id z).det) =
        (μ : WithTop ℝ) ∧
      (Finset.univ.inf fun y : Fin n → ι => ν (H.submatrix Fin.succ y).det) =
        (μhat : WithTop ℝ) ∧
      α - δ ≤ μhat - μ := by
  exact canonical_minValue_growth ν htop hmul hadd A.det
    (fun i => (A.updateCol i (Pi.single 0 1)).det * c i)
    (fun y : Fin n → ι => (H.submatrix Fin.succ y).det)
    (fun z : Fin (n + 1) → ι => (H.submatrix id z).det)
    (fun i y => (prependColumn (fun r => H r (x i)) (H.submatrix id y)).det)
    hdet (exists_nonzero_scaled_cramer A H x c hcol hdet)
    (exists_nonzero_projected_minor H x (nonzero_unscaled_minor A H x c hcol hdet))
    ⟨x, nonzero_unscaled_minor A H x c hcol hdet⟩
    (fun y => projected_minor_identity A H x y c hcol)
    (fun i y => Or.inr ⟨Fin.cases (x i) y,
      congrArg Matrix.det (prepend_submatrix H (x i) y)⟩)

end DetValuationMilestone

open scoped BigOperators

namespace DetValuationMilestone

noncomputable def tupleMinorVal
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (G : Matrix I J R) : WithTop ℝ := by
  classical
  exact Finset.univ.inf fun e : I → J => ν (G.submatrix id e).det

noncomputable def embeddingMinorVal
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (G : Matrix I J R) : WithTop ℝ := by
  classical
  exact Finset.univ.inf fun e : I ↪ J => ν (G.submatrix id e).det

theorem det_submatrix_eq_zero_of_not_injective
    {I J R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (G : Matrix I J R) (x : I → J) (hx : ¬ Function.Injective x) :
    (G.submatrix id x).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hx
  exact Matrix.det_zero_of_column_eq hne (fun r => congrArg (fun j => G r j) hij)

theorem embeddingMinorVal_le_tuple
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤)
    (G : Matrix I J R) (x : I → J) :
    embeddingMinorVal ν G ≤ ν (G.submatrix id x).det := by
  classical
  exact (Classical.em (Function.Injective x)).elim
    (fun hx => Finset.inf_le (f := fun e : I ↪ J => ν (G.submatrix id e).det)
      (Finset.mem_univ (⟨x, hx⟩ : I ↪ J)))
    (fun hx => by
      simpa only [det_submatrix_eq_zero_of_not_injective G x hx, hzero] using
        (le_top : embeddingMinorVal ν G ≤ ⊤))

theorem tupleMinorVal_eq_embeddingMinorVal
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (G : Matrix I J R) :
    tupleMinorVal ν G = embeddingMinorVal ν G := by
  classical
  exact le_antisymm
    (Finset.le_inf fun e _ => Finset.inf_le
      (f := fun x : I → J => ν (G.submatrix id x).det) (Finset.mem_univ (e : I → J)))
    (Finset.le_inf fun x _ => embeddingMinorVal_le_tuple ν hzero G x)


theorem add_finset_inf {ι : Type*} (a : WithTop ℝ) (s : Finset ι)
    (f : ι → WithTop ℝ) :
    a + s.inf f = s.inf (fun i => a + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.inf_insert, ← ih, min_add_add_left]

theorem tupleMinorVal_mul
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (A : Matrix I I R) (G : Matrix I J R) :
    tupleMinorVal ν (A * G) = ν A.det + tupleMinorVal ν G := by
  have hval : ∀ x : I → J, ν ((A * G).submatrix id x).det =
      ν A.det + ν (G.submatrix id x).det := fun x =>
    (congrArg ν (Matrix.det_mul A (G.submatrix id x))).trans (hmul _ _)
  simpa only [tupleMinorVal, hval] using
    (add_finset_inf (ν A.det) (Finset.univ : Finset (I → J))
      (fun x => ν (G.submatrix id x).det)).symm

theorem embeddingMinorVal_mul
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (A : Matrix I I R) (G : Matrix I J R) :
    embeddingMinorVal ν (A * G) = ν A.det + embeddingMinorVal ν G := by
  simpa only [tupleMinorVal_eq_embeddingMinorVal ν hzero] using tupleMinorVal_mul ν hmul A G


end DetValuationMilestone

namespace KServerConj

theorem minorVal_eq_embeddingMinorVal
    {F I J : Type*} [Field F] [Fintype I] [hI : DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) :
    minorVal G = DetValuationMilestone.embeddingMinorVal (HahnSeries.addVal ℝ F) G := by
  classical
  cases Subsingleton.elim hI (Classical.decEq I)
  unfold minorVal DetValuationMilestone.embeddingMinorVal
  rfl

theorem minorVal_mul
    {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I I (HahnSeries ℝ F)) (G : Matrix I J (HahnSeries ℝ F)) :
    minorVal (A * G) = HahnSeries.addVal ℝ F A.det + minorVal G := by
  simpa only [minorVal_eq_embeddingMinorVal] using
    DetValuationMilestone.embeddingMinorVal_mul (HahnSeries.addVal ℝ F)
      (AddValuation.map_zero _) (fun x y => AddValuation.map_mul _ x y) A G

end KServerConj

open scoped BigOperators

/-!
Minimum valuations of maximal minors under column combinations.

The determinant expansion includes every column tuple, including repeated
columns; there is no injectivity filter. Nonnegative coefficient valuations
then give monotonicity by the non-Archimedean sum inequality. Minimum values
remain in `WithTop ℝ`, so no spanning or finite-minimum hypotheses are required.
The final theorem is the column-combination rule of paper Lemma 3.2(2).
-/

namespace DetValuationMilestone

/-- Determinant multilinearity for a rectangular product, before eliminating
the tuples with repeated columns. -/
theorem det_mul_rectangular_expansion
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (G : Matrix I J R) (C : Matrix J I R) :
    (G * C).det =
      ∑ f : I → J, (∏ i, C (f i) i) * (G.submatrix id f).det := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
    Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  simp only [Finset.prod_mul_distrib, Matrix.submatrix_apply, id_eq,
    mul_comm, mul_assoc]

/-- Products of elements with nonnegative valuation have nonnegative valuation,
including the empty product. -/
theorem valuation_prod_nonneg
    {R I : Type*} [CommMonoid R]
    (ν : R → WithTop ℝ) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (s : Finset I) (f : I → R)
    (hf : ∀ i ∈ s, (0 : WithTop ℝ) ≤ ν (f i)) :
    (0 : WithTop ℝ) ≤ ν (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hone]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, hmul]
    exact add_nonneg (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Any lower bound on all maximal tuple minors survives a square column
combination with coefficients of nonnegative valuation. The lower bound may be top. -/
theorem valuation_det_mul_lower_bound
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (C : Matrix J I R) (μ : WithTop ℝ)
    (hG : ∀ f : I → J, μ ≤ ν (G.submatrix id f).det)
    (hC : ∀ j i, (0 : WithTop ℝ) ≤ ν (C j i)) :
    μ ≤ ν (G * C).det := by
  rw [det_mul_rectangular_expansion]
  apply valuation_sum_lower_bound ν hzero hadd
  intro f _
  have hcoeff : (0 : WithTop ℝ) ≤ ν (∏ i, C (f i) i) :=
    valuation_prod_nonneg ν hone hmul Finset.univ (fun i => C (f i) i)
      (fun i _ => hC (f i) i)
  simpa only [hmul, zero_add] using add_le_add hcoeff (hG f)

/-- Column combinations cannot decrease the minimum tuple-minor valuation. -/
theorem tupleMinorVal_mono_of_nonneg_coeff
    {I J K R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (C : Matrix J K R)
    (hC : ∀ j k, (0 : WithTop ℝ) ≤ ν (C j k)) :
    tupleMinorVal ν G ≤ tupleMinorVal ν (G * C) := by
  classical
  refine Finset.le_inf (fun e _ => ?_)
  change tupleMinorVal ν G ≤ ν (G * (C.submatrix id e)).det
  exact valuation_det_mul_lower_bound ν hzero hone hmul hadd G (C.submatrix id e)
    (tupleMinorVal ν G)
    (fun f => Finset.inf_le (f := fun x : I → J => ν (G.submatrix id x).det)
      (Finset.mem_univ f))
    (fun j i => hC j (e i))

/-- The same monotonicity statement for the published injection-indexed minimum. -/
theorem embeddingMinorVal_mono_of_nonneg_coeff
    {I J K R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (C : Matrix J K R)
    (hC : ∀ j k, (0 : WithTop ℝ) ≤ ν (C j k)) :
    embeddingMinorVal ν G ≤ embeddingMinorVal ν (G * C) := by
  simpa only [tupleMinorVal_eq_embeddingMinorVal ν hzero] using
    tupleMinorVal_mono_of_nonneg_coeff ν hzero hone hmul hadd G C hC

/-- An explicit coefficient matrix is unnecessary: choose the witnessing
combination for each target column. No rank hypothesis is needed. -/
theorem embeddingMinorVal_mono_of_column_combinations
    {I J K R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (F : Matrix I K R)
    (hF : ∀ k, ∃ c : J → R,
      (∀ j, (0 : WithTop ℝ) ≤ ν (c j)) ∧ ∀ i, F i k = ∑ j, G i j * c j) :
    embeddingMinorVal ν G ≤ embeddingMinorVal ν F := by
  classical
  let C : Matrix J K R := Matrix.of fun j k => (hF k).choose j
  have hGC : G * C = F :=
    Matrix.ext (fun i k => by
      simpa only [Matrix.mul_apply, C, Matrix.of_apply] using ((hF k).choose_spec.2 i).symm)
  simpa only [hGC] using
    embeddingMinorVal_mono_of_nonneg_coeff ν hzero hone hmul hadd G C
      (fun j k => (hF k).choose_spec.1 j)

end DetValuationMilestone

open scoped BigOperators

/-!
Nonnegative valuations of determinants and minimum maximal minors.

The nonnegative elements form a subring. A matrix with entries in this subring
has its determinant in the subring, and mapping that determinant to the ambient
ring gives the desired valuation bound. Rank and finite-minimum assumptions are
unnecessary; a zero determinant or a non-spanning family has value top.
-/

namespace DetValuationMilestone

/-- A matrix whose entries all have nonnegative valuation has determinant of
nonnegative valuation, by computing the determinant in the nonnegative subring. -/
theorem valuation_det_nonneg
    {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hneg : ∀ x, ν (-x) = ν x)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (A : Matrix I I R) (hA : ∀ i j, (0 : WithTop ℝ) ≤ ν (A i j)) :
    (0 : WithTop ℝ) ≤ ν A.det := by
  let S : Subring R :=
    { carrier := {x | (0 : WithTop ℝ) ≤ ν x}
      zero_mem' := (show (0 : WithTop ℝ) ≤ ν 0 from
        hzero.symm ▸ (le_top : (0 : WithTop ℝ) ≤ ⊤))
      one_mem' := (show (0 : WithTop ℝ) ≤ ν 1 from
        hone.symm ▸ (le_rfl : (0 : WithTop ℝ) ≤ 0))
      add_mem' := fun hx hy => (le_min hx hy).trans (hadd _ _)
      neg_mem' := fun {x} hx => (show (0 : WithTop ℝ) ≤ ν (-x) from (hneg x).symm ▸ hx)
      mul_mem' := fun {x y} hx hy => (show (0 : WithTop ℝ) ≤ ν (x * y) from
        (hmul x y).symm ▸ add_nonneg hx hy) }
  let B : Matrix I I S := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have hmatrix : S.subtype.mapMatrix B = A := Matrix.ext (fun _ _ => rfl)
  have hmap : (↑(B.det) : R) = A.det :=
    (RingHom.map_det S.subtype B).trans (congrArg Matrix.det hmatrix)
  exact hmap ▸ (show (0 : WithTop ℝ) ≤ ν (↑(B.det) : R) from (B.det).property)

/-- The minimum over all maximal tuple minors is nonnegative. -/
theorem zero_le_tupleMinorVal_of_entries
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hneg : ∀ x, ν (-x) = ν x)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (hG : ∀ i j, (0 : WithTop ℝ) ≤ ν (G i j)) :
    (0 : WithTop ℝ) ≤ tupleMinorVal ν G := by
  classical
  exact Finset.le_inf (fun e _ => valuation_det_nonneg ν hzero hone hneg hmul hadd
    (G.submatrix id e) (fun i j => hG i (e j)))

/-- The published injection-indexed minimum is nonnegative as well. -/
theorem zero_le_embeddingMinorVal_of_entries
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hneg : ∀ x, ν (-x) = ν x)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (hG : ∀ i j, (0 : WithTop ℝ) ≤ ν (G i j)) :
    (0 : WithTop ℝ) ≤ embeddingMinorVal ν G := by
  simpa only [tupleMinorVal_eq_embeddingMinorVal ν hzero] using
    zero_le_tupleMinorVal_of_entries ν hzero hone hneg hmul hadd G hG

end DetValuationMilestone

open scoped BigOperators

/-!
Pure determinant algebra for the lifted work-function request update.

All identities hold over a commutative ring. The fresh row is arbitrary: no
special value at the request, coefficient independence, or valuation premise is
used. Column tuples may repeat labels. Determinant-one normalization preserves
every old column determinant exactly.
-/

namespace KServerAlgebra

/-- Expanding a replaced row by transposed Cramer's rule. -/
theorem det_updateRow_eq_sum_updateCol
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (j : ι) (δ : ι → R) :
    (M.updateRow j δ).det =
      ∑ i, δ i * (M.updateCol i (Pi.single j 1)).det := by
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.adjugate_apply,
    Matrix.updateRow_transpose, Matrix.det_transpose]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- Replacing a selected column is the same as replacing its tuple label. -/
theorem updateCol_column_family
    {ι M R : Type*} [DecidableEq ι]
    (q : M → ι → R) (X : ι → M) (i : ι) (r : M) :
    (Matrix.of fun a b => q (X b) a).updateCol i (q r) =
      Matrix.of (fun a b => q (Function.update X i r b) a) := by
  ext a b
  by_cases h : b = i <;> simp [Matrix.updateCol, Function.update, h]

/-- If the request column is a standard basis vector, row replacement expands
over tuples with one label replaced by the request. -/
theorem det_updateRow_column_family
    {ι M R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (q : M → ι → R) (X : ι → M) (r : M) (j : ι) (δ : ι → R)
    (hr : q r = Pi.single j 1) :
    ((Matrix.of fun a b => q (X b) a).updateRow j δ).det =
      ∑ i, δ i * (Matrix.of fun a b => q (Function.update X i r b) a).det := by
  simpa only [← hr, updateCol_column_family] using
    det_updateRow_eq_sum_updateCol (Matrix.of fun a b => q (X b) a) j δ

/-- The `Fin.cons` form of the published row replacement is matrix row replacement. -/
theorem rowReplace_column_matrix
    {n : ℕ} {M R : Type*}
    (q : M → Fin (n + 1) → R) (δ : M → R) (X : Fin (n + 1) → M) :
    (Matrix.of fun a b => Fin.cons (δ (X b)) (Fin.tail (q (X b))) a) =
      (Matrix.of fun a b => q (X b) a).updateRow 0 (fun b => δ (X b)) := by
  ext a b
  cases a using Fin.cases <;> simp [Matrix.updateRow, Function.update, Fin.tail]

/-- The exact lifted work-function determinant recurrence, before applying valuation. -/
theorem det_rowReplace_column_family
    {n : ℕ} {M R : Type*} [CommRing R]
    (q : M → Fin (n + 1) → R) (δ : M → R) (X : Fin (n + 1) → M)
    (r : M) (hr : q r = Pi.single 0 1) :
    (Matrix.of fun a b => Fin.cons (δ (X b)) (Fin.tail (q (X b))) a).det =
      ∑ i, δ (X i) * (Matrix.of fun a b => q (Function.update X i r b) a).det := by
  rw [rowReplace_column_matrix]
  exact det_updateRow_column_family q X r 0 (fun i => δ (X i)) hr

/-- Applying a matrix to each column is left matrix multiplication. -/
theorem mulVec_column_matrix
    {ι M R : Type*} [Fintype ι] [CommRing R]
    (B : Matrix ι ι R) (q : M → ι → R) (X : ι → M) :
    (Matrix.of fun a b => B.mulVec (q (X b)) a) =
      B * (Matrix.of fun a b => q (X b) a) := by
  rfl

/-- A determinant-one change of basis preserves all column determinants, allowing
freshness to be tracked at determinant level rather than entrywise. -/
theorem det_normalized_column_family
    {ι M R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (B : Matrix ι ι R) (hB : B.det = 1) (q : M → ι → R) (X : ι → M) :
    (Matrix.of fun a b => B.mulVec (q (X b)) a).det =
      (Matrix.of fun a b => q (X b) a).det := by
  rw [mulVec_column_matrix, Matrix.det_mul, hB, one_mul]

end KServerAlgebra

open scoped BigOperators

/-!
Binary block-diagonal additivity for finite minor values.

Choose a minimum-valued basis in each block. Inverse basis normalization gives
entries of nonnegative valuation by Cramer's rule. The normalized direct sum has
nonnegative minor values; undoing the row transformation gives the lower bound.
The direct sum of the two chosen bases gives the matching upper bound.
-/

namespace DetValuationMilestone

/-- A finite real infimum over a finite family is attained, even if the index
type was not initially known to be inhabited. -/
theorem exists_finite_inf_minimizer
    {X : Type*} [Fintype X] (f : X → WithTop ℝ) (μ : ℝ)
    (h : (Finset.univ.inf f) = (μ : WithTop ℝ)) :
    ∃ x, f x = (μ : WithTop ℝ) := by
  classical
  obtain ⟨i, _, hi⟩ := (Finset.inf_le_iff (show (μ : WithTop ℝ) < ⊤ by simp)).mp h.le
  exact ⟨i, le_antisymm hi (h.symm.trans_le (Finset.inf_le (Finset.mem_univ i)))⟩

/-- Relative to a minimum-valued basis, all column coordinates have nonnegative
valuation. Only the finite determinant valuation is cancelled. -/
theorem minimum_basis_coordinate_nonneg
    {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Field K]
    (ν : K → WithTop ℝ) (hzero : ν 0 = ⊤)
    (hmul : ∀ a b, ν (a * b) = ν a + ν b)
    (G : Matrix I J K) (x : I → J) (μ : ℝ)
    (hmin : tupleMinorVal ν G = (μ : WithTop ℝ))
    (hx : ν (G.submatrix id x).det = (μ : WithTop ℝ)) :
    ∀ i j, (0 : WithTop ℝ) ≤ ν (((G.submatrix id x)⁻¹ * G) i j) := by
  let A : Matrix I I K := G.submatrix id x
  have hval : ν A.det = (μ : WithTop ℝ) := hx
  have hAne : A.det ≠ 0 := fun hz =>
    (show (μ : WithTop ℝ) ≠ ⊤ by simp)
      ((hval.symm.trans (congrArg ν hz)).trans hzero)
  intro i j
  have hcr := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer A (G.col j)
    (isUnit_iff_ne_zero.mpr hAne)) i
  have hcoord : A.det * ((A⁻¹ * G) i j) = (A.updateCol i (G.col j)).det := by
    simpa only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Matrix.col_apply] using hcr
  have hmodified : (A.updateCol i (G.col j)).det =
      (G.submatrix id (Function.update x i j)).det := by
    exact congrArg Matrix.det (Matrix.ext (fun a b => by
      by_cases hb : b = i <;>
        simp [A, Matrix.updateCol, Matrix.submatrix, Function.update, hb]))
  have hfull : (μ : WithTop ℝ) ≤ ν (G.submatrix id (Function.update x i j)).det :=
    hmin.symm.trans_le (Finset.inf_le (f := fun y : I → J => ν (G.submatrix id y).det)
      (Finset.mem_univ (Function.update x i j)))
  rw [← hmodified, ← hcoord, hmul, hval] at hfull
  exact WithTop.le_of_add_le_add_left (x := (μ : WithTop ℝ)) (by simp)
    (by simpa only [add_zero] using hfull)

/-- The determinant of an inverse matrix has opposite finite valuation. -/
theorem valuation_det_inverse_of_finite
    {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (ν : R → WithTop ℝ) (hone : ν 1 = 0)
    (hmul : ∀ a b, ν (a * b) = ν a + ν b)
    (A : Matrix I I R) (hA : IsUnit A.det) (μ : ℝ)
    (hval : ν A.det = (μ : WithTop ℝ)) :
    ν A⁻¹.det = ((-μ : ℝ) : WithTop ℝ) := by
  have hprod : ν A⁻¹.det + (μ : WithTop ℝ) = 0 := by
    simpa only [hmul, hval, hone] using congrArg ν (Matrix.det_nonsing_inv_mul_det A hA)
  exact (add_left_inj_of_ne_top (a := (μ : WithTop ℝ)) (by simp)).mp
    (by simpa only [← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero] using hprod)

/-- Selecting the direct sum of two column tuples commutes with block formation. -/
theorem submatrix_fromBlocks_sum_map
    {I₁ I₂ J₁ J₂ R : Type*} [Zero R]
    (G₁ : Matrix I₁ J₁ R) (G₂ : Matrix I₂ J₂ R)
    (x₁ : I₁ → J₁) (x₂ : I₂ → J₂) :
    (Matrix.fromBlocks G₁ 0 0 G₂).submatrix id (Sum.map x₁ x₂) =
      Matrix.fromBlocks (G₁.submatrix id x₁) 0 0 (G₂.submatrix id x₂) := by
  ext i j
  cases i <;> cases j <;> rfl

/-- The block rule of paper Lemma 3.2(3) for two finite real minor minima.
No separate rank or nonzero-determinant assumptions are needed. -/
theorem tupleMinorVal_fromBlocks_of_finite
    {I₁ I₂ J₁ J₂ R : Type*}
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    [Fintype J₁] [Fintype J₂] [Field R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hneg : ∀ a, ν (-a) = ν a)
    (hmul : ∀ a b, ν (a * b) = ν a + ν b)
    (hadd : ∀ a b, min (ν a) (ν b) ≤ ν (a + b))
    (G₁ : Matrix I₁ J₁ R) (G₂ : Matrix I₂ J₂ R) (μ₁ μ₂ : ℝ)
    (hmin₁ : tupleMinorVal ν G₁ = (μ₁ : WithTop ℝ))
    (hmin₂ : tupleMinorVal ν G₂ = (μ₂ : WithTop ℝ)) :
    tupleMinorVal ν (Matrix.fromBlocks G₁ 0 0 G₂) = ((μ₁ + μ₂ : ℝ) : WithTop ℝ) := by
  obtain ⟨x₁, hx₁⟩ := exists_finite_inf_minimizer
    (fun x : I₁ → J₁ => ν (G₁.submatrix id x).det) μ₁ hmin₁
  obtain ⟨x₂, hx₂⟩ := exists_finite_inf_minimizer
    (fun x : I₂ → J₂ => ν (G₂.submatrix id x).det) μ₂ hmin₂
  let A₁ : Matrix I₁ I₁ R := G₁.submatrix id x₁
  let A₂ : Matrix I₂ I₂ R := G₂.submatrix id x₂
  let S : Matrix (I₁ ⊕ I₂) (J₁ ⊕ J₂) R := Matrix.fromBlocks G₁ 0 0 G₂
  let B : Matrix (I₁ ⊕ I₂) (I₁ ⊕ I₂) R := Matrix.fromBlocks A₁⁻¹ 0 0 A₂⁻¹
  let H : Matrix (I₁ ⊕ I₂) (J₁ ⊕ J₂) R :=
    Matrix.fromBlocks (A₁⁻¹ * G₁) 0 0 (A₂⁻¹ * G₂)
  have hproduct : B * S = H := by
    simp only [B, S, H, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      zero_add, add_zero]
  have hn₁ := minimum_basis_coordinate_nonneg ν hzero hmul G₁ x₁ μ₁ hmin₁ hx₁
  have hn₂ := minimum_basis_coordinate_nonneg ν hzero hmul G₂ x₂ μ₂ hmin₂ hx₂
  have hH : ∀ (i : I₁ ⊕ I₂) (j : J₁ ⊕ J₂), (0 : WithTop ℝ) ≤ ν (H i j) := fun
    | Sum.inl i, Sum.inl j => hn₁ i j
    | Sum.inl i, Sum.inr j => by simp [H, hzero]
    | Sum.inr i, Sum.inl j => by simp [H, hzero]
    | Sum.inr i, Sum.inr j => hn₂ i j
  have hHmin := zero_le_tupleMinorVal_of_entries ν hzero hone hneg hmul hadd H hH
  have hrow : tupleMinorVal ν H = ν B.det + tupleMinorVal ν S :=
    (congrArg (tupleMinorVal ν) hproduct).symm.trans (tupleMinorVal_mul ν hmul B S)
  have hunit₁ : IsUnit A₁.det := isUnit_iff_ne_zero.mpr (fun hz =>
    (show (μ₁ : WithTop ℝ) ≠ ⊤ by simp)
      ((hx₁.symm.trans (congrArg ν hz)).trans hzero))
  have hunit₂ : IsUnit A₂.det := isUnit_iff_ne_zero.mpr (fun hz =>
    (show (μ₂ : WithTop ℝ) ≠ ⊤ by simp)
      ((hx₂.symm.trans (congrArg ν hz)).trans hzero))
  have hinv₁ := valuation_det_inverse_of_finite ν hone hmul A₁ hunit₁ μ₁ hx₁
  have hinv₂ := valuation_det_inverse_of_finite ν hone hmul A₂ hunit₂ μ₂ hx₂
  have hBval : ν B.det = ((-μ₁ + -μ₂ : ℝ) : WithTop ℝ) := by
    simp only [B, Matrix.det_fromBlocks_zero₂₁, hmul, hinv₁, hinv₂, ← WithTop.coe_add]
  have hscaled : (0 : WithTop ℝ) ≤ ((-μ₁ + -μ₂ : ℝ) : WithTop ℝ) + tupleMinorVal ν S := by
    simpa only [hrow, hBval] using hHmin
  have hlower : ((μ₁ + μ₂ : ℝ) : WithTop ℝ) ≤ tupleMinorVal ν S :=
    WithTop.le_of_add_le_add_left (x := ((-μ₁ + -μ₂ : ℝ) : WithTop ℝ)) (by simp)
      (by simpa only [← WithTop.coe_add,
        show (-μ₁ + -μ₂) + (μ₁ + μ₂) = 0 by linarith only,
        WithTop.coe_zero] using hscaled)
  have hselected : tupleMinorVal ν S ≤ ν (S.submatrix id (Sum.map x₁ x₂)).det :=
    Finset.inf_le (f := fun x : (I₁ ⊕ I₂) → (J₁ ⊕ J₂) => ν (S.submatrix id x).det)
      (Finset.mem_univ (Sum.map x₁ x₂))
  have hupper : tupleMinorVal ν S ≤ ((μ₁ + μ₂ : ℝ) : WithTop ℝ) := by
    simpa only [S, submatrix_fromBlocks_sum_map, Matrix.det_fromBlocks_zero₂₁,
      hmul, hx₁, hx₂, ← WithTop.coe_add] using hselected
  exact le_antisymm hupper hlower

end DetValuationMilestone

namespace KServerConj

theorem tupleMinorVal_one_punit {F : Type*} [Field F] :
    DetValuationMilestone.tupleMinorVal (HahnSeries.addVal ℝ F)
      (1 : Matrix PUnit PUnit (HahnSeries ℝ F)) = (0 : WithTop ℝ) := by
  classical
  simp [DetValuationMilestone.tupleMinorVal, Matrix.det_unique, Matrix.submatrix_apply,
    AddValuation.map_one]

theorem minorVal_one_punit {F : Type*} [Field F] :
    minorVal (1 : Matrix PUnit PUnit (HahnSeries ℝ F)) = (0 : WithTop ℝ) := by
  simpa only [DetValuationMilestone.tupleMinorVal_eq_embeddingMinorVal
    (HahnSeries.addVal ℝ F) (AddValuation.map_zero _), ← minorVal_eq_embeddingMinorVal] using
      (tupleMinorVal_one_punit (F := F))

set_option maxHeartbeats 1000000 in
theorem minorVal_fromBlocks_of_finite {F I₁ I₂ J₁ J₂ : Type*} [Field F]
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    [Fintype J₁] [Fintype J₂]
    (G₁ : Matrix I₁ J₁ (HahnSeries ℝ F)) (G₂ : Matrix I₂ J₂ (HahnSeries ℝ F))
    (a b : ℝ) (h₁ : minorVal G₁ = (a : WithTop ℝ)) (h₂ : minorVal G₂ = (b : WithTop ℝ)) :
    minorVal (Matrix.fromBlocks G₁ 0 0 G₂) = ((a + b : ℝ) : WithTop ℝ) := by
  simpa only [DetValuationMilestone.tupleMinorVal_eq_embeddingMinorVal
    (HahnSeries.addVal ℝ F) (AddValuation.map_zero _), ← minorVal_eq_embeddingMinorVal] using
      DetValuationMilestone.tupleMinorVal_fromBlocks_of_finite (R := HahnSeries ℝ F)
        (HahnSeries.addVal ℝ F) (AddValuation.map_zero (HahnSeries.addVal ℝ F))
        (AddValuation.map_one (HahnSeries.addVal ℝ F))
        (fun x => AddValuation.map_neg (HahnSeries.addVal ℝ F) x)
        (fun x y => AddValuation.map_mul (HahnSeries.addVal ℝ F) x y)
        (fun x y => AddValuation.map_add (HahnSeries.addVal ℝ F) x y) G₁ G₂ a b
        (by
          simpa only [DetValuationMilestone.tupleMinorVal_eq_embeddingMinorVal
            (HahnSeries.addVal ℝ F) (AddValuation.map_zero _), ← minorVal_eq_embeddingMinorVal] using h₁)
        (by
          simpa only [DetValuationMilestone.tupleMinorVal_eq_embeddingMinorVal
            (HahnSeries.addVal ℝ F) (AddValuation.map_zero _), ← minorVal_eq_embeddingMinorVal] using h₂)

end KServerConj

open scoped BigOperators

namespace KServerConj

theorem minorVal_mono_of_column_combinations {F I J K : Type*} [Field F]
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype K]
    (G : Matrix I J (HahnSeries ℝ F)) (A : Matrix I K (HahnSeries ℝ F))
    (hA : ∀ k, ∃ c : J → HahnSeries ℝ F,
      (∀ j, (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (c j)) ∧
      ∀ i, A i k = ∑ j, G i j * c j) :
    minorVal G ≤ minorVal A := by
  simpa only [minorVal_eq_embeddingMinorVal] using
    DetValuationMilestone.embeddingMinorVal_mono_of_column_combinations
      (HahnSeries.addVal ℝ F) (AddValuation.map_zero _) (AddValuation.map_one _)
      (fun a b => AddValuation.map_mul _ a b) (fun a b => AddValuation.map_add _ a b)
      G A hA

end KServerConj

namespace KServerConj

theorem minorVal_le_tuple {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (x : I → J) :
    minorVal G ≤ HahnSeries.addVal ℝ F (G.submatrix id x).det := by
  simpa only [minorVal_eq_embeddingMinorVal] using
    DetValuationMilestone.embeddingMinorVal_le_tuple (HahnSeries.addVal ℝ F)
      (AddValuation.map_zero _) G x

theorem exists_minorVal_minimizer {F I J : Type*}
    [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (a : ℝ)
    (ha : minorVal G = (a : WithTop ℝ)) :
    ∃ x : I ↪ J, HahnSeries.addVal ℝ F (G.submatrix id x).det = (a : WithTop ℝ) := by
  classical
  have hh : DetValuationMilestone.embeddingMinorVal (HahnSeries.addVal ℝ F) G =
      (a : WithTop ℝ) := (minorVal_eq_embeddingMinorVal G).symm.trans ha
  unfold DetValuationMilestone.embeddingMinorVal at hh
  obtain ⟨x, _, hx⟩ := (Finset.inf_le_iff (show (a : WithTop ℝ) < ⊤ by simp)).mp hh.le
  exact ⟨x, le_antisymm hx (hh.symm.trans_le (Finset.inf_le (Finset.mem_univ x)))⟩


end KServerConj

open scoped BigOperators

namespace KServerConj

theorem exists_rightInverse_of_nonzero_minor
    {K I J : Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J K) (x : I → J) (hx : (G.submatrix id x).det ≠ 0) :
    ∃ C : Matrix J I K, G * C = 1 := by
  classical
  refine ⟨(1 : Matrix J J K).submatrix id x * (G.submatrix id x)⁻¹, ?_⟩
  rw [← Matrix.mul_assoc]
  have hm : G * (1 : Matrix J J K).submatrix id x = G.submatrix id x := by
    simpa only [Equiv.coe_refl, Equiv.refl_symm, Function.id_comp] using
      Matrix.mul_submatrix_one (Equiv.refl J) x G
  exact (congrArg (fun B : Matrix I I K => B * (G.submatrix id x)⁻¹) hm).trans
    (Matrix.mul_nonsing_inv (G.submatrix id x) (isUnit_iff_ne_zero.mpr hx))


theorem exists_nonzero_minor_of_rightInverse
    {K I J : Type*} [CommRing K] [Nontrivial K]
    [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J K) (C : Matrix J I K) (hC : G * C = 1) :
    ∃ x : I → J, (G.submatrix id x).det ≠ 0 := by
  classical
  by_contra h
  simp only [not_exists, not_not] at h
  simpa only [DetValuationMilestone.det_mul_rectangular_expansion, h, mul_zero,
    Finset.sum_const_zero, Matrix.det_one, zero_ne_one] using congrArg Matrix.det hC


theorem rightInverse_fromBlocks_left
    {K I₁ I₂ J₁ J₂ : Type*} [CommRing K]
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    [Fintype J₁] [Fintype J₂]
    (G₁ : Matrix I₁ J₁ K) (G₂ : Matrix I₂ J₂ K)
    (C : Matrix (J₁ ⊕ J₂) (I₁ ⊕ I₂) K)
    (hC : Matrix.fromBlocks G₁ 0 0 G₂ * C = 1) :
    G₁ * C.submatrix Sum.inl Sum.inl = 1 := by
  funext i j
  simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.submatrix,
    Matrix.one_apply] using
    congrFun (congrFun hC (Sum.inl i)) (Sum.inl j)


theorem rightInverse_fromBlocks_right
    {K I₁ I₂ J₁ J₂ : Type*} [CommRing K]
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    [Fintype J₁] [Fintype J₂]
    (G₁ : Matrix I₁ J₁ K) (G₂ : Matrix I₂ J₂ K)
    (C : Matrix (J₁ ⊕ J₂) (I₁ ⊕ I₂) K)
    (hC : Matrix.fromBlocks G₁ 0 0 G₂ * C = 1) :
    G₂ * C.submatrix Sum.inr Sum.inr = 1 := by
  exact funext fun i => funext fun j => by
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.submatrix,
      Matrix.one_apply] using congrFun (congrFun hC (Sum.inr i)) (Sum.inr j)


theorem minorVal_ne_top_of_nonzero_minor
    {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (x : I → J)
    (hx : (G.submatrix id x).det ≠ 0) : minorVal G ≠ ⊤ := by
  exact fun h => hx <| HahnSeries.orderTop_eq_top.mp <|
    top_le_iff.mp <| h ▸ minorVal_le_tuple G x


theorem minorVal_fromBlocks_eq_top_of_left
    {F I₁ I₂ J₁ J₂ : Type*} [Field F]
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    [Fintype J₁] [Fintype J₂]
    (G₁ : Matrix I₁ J₁ (HahnSeries ℝ F)) (G₂ : Matrix I₂ J₂ (HahnSeries ℝ F))
    (h₁ : minorVal G₁ = ⊤) :
    minorVal (Matrix.fromBlocks G₁ 0 0 G₂) = ⊤ := by
  classical
  have hz : ∀ x : (I₁ ⊕ I₂) → (J₁ ⊕ J₂),
      ((Matrix.fromBlocks G₁ 0 0 G₂).submatrix id x).det = 0 :=
    fun x => Classical.byContradiction fun hx =>
      (exists_rightInverse_of_nonzero_minor (Matrix.fromBlocks G₁ 0 0 G₂) x hx).elim
        fun C hC =>
          (exists_nonzero_minor_of_rightInverse G₁ (C.submatrix Sum.inl Sum.inl)
            (rightInverse_fromBlocks_left G₁ G₂ C hC)).elim fun y hy =>
              (minorVal_ne_top_of_nonzero_minor G₁ y hy) h₁
  simp [minorVal_eq_embeddingMinorVal, DetValuationMilestone.embeddingMinorVal,
    hz, AddValuation.map_zero]


theorem minorVal_eq_top_of_all_tuple_minors_zero
    {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F))
    (hz : ∀ x : I → J, (G.submatrix id x).det = 0) : minorVal G = ⊤ := by
  classical
  simp [minorVal_eq_embeddingMinorVal, DetValuationMilestone.embeddingMinorVal,
    hz, AddValuation.map_zero]


theorem minorVal_fromBlocks_eq_top_of_right
    {F I₁ I₂ J₁ J₂ : Type*} [Field F]
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    [Fintype J₁] [Fintype J₂]
    (G₁ : Matrix I₁ J₁ (HahnSeries ℝ F)) (G₂ : Matrix I₂ J₂ (HahnSeries ℝ F))
    (h₂ : minorVal G₂ = ⊤) :
    minorVal (Matrix.fromBlocks G₁ 0 0 G₂) = ⊤ := by
  exact minorVal_eq_top_of_all_tuple_minors_zero (Matrix.fromBlocks G₁ 0 0 G₂)
    fun x => Classical.byContradiction fun hx =>
      (exists_rightInverse_of_nonzero_minor (Matrix.fromBlocks G₁ 0 0 G₂) x hx).elim
        fun C hC =>
          (exists_nonzero_minor_of_rightInverse G₂ (C.submatrix Sum.inr Sum.inr)
            (rightInverse_fromBlocks_right G₁ G₂ C hC)).elim fun y hy =>
              (minorVal_ne_top_of_nonzero_minor G₂ y hy) h₂


theorem minorVal_fromBlocks
    {F I₁ I₂ J₁ J₂ : Type*} [Field F]
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    [Fintype J₁] [Fintype J₂]
    (G₁ : Matrix I₁ J₁ (HahnSeries ℝ F)) (G₂ : Matrix I₂ J₂ (HahnSeries ℝ F)) :
    minorVal (Matrix.fromBlocks G₁ 0 0 G₂) = minorVal G₁ + minorVal G₂ := by
  exact (Classical.em (minorVal G₁ = ⊤)).elim
    (fun h₁ => by simpa [h₁] using minorVal_fromBlocks_eq_top_of_left G₁ G₂ h₁)
    (fun h₁ => (Classical.em (minorVal G₂ = ⊤)).elim
      (fun h₂ => by simpa [h₂] using minorVal_fromBlocks_eq_top_of_right G₁ G₂ h₂)
      (fun h₂ => (WithTop.ne_top_iff_exists.mp h₁).elim fun a ha =>
        (WithTop.ne_top_iff_exists.mp h₂).elim fun b hb => by
          simpa only [← ha, ← hb, WithTop.coe_add] using
            minorVal_fromBlocks_of_finite G₁ G₂ a b ha.symm hb.symm))


end KServerConj

open scoped BigOperators

namespace KServerConj

theorem det_blockDiagonal'_general {K β : Type*} [CommRing K]
    [Fintype β] [DecidableEq β] {I : β → Type*}
    [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)]
    (G : ∀ b, Matrix (I b) (I b) K) :
    (Matrix.blockDiagonal' G).det = ∏ b, (G b).det := by
  classical
  let : LinearOrder β := LinearOrder.lift' (Fintype.equivFin β) (Equiv.injective _)
  have ht : (Matrix.blockDiagonal' G).BlockTriangular
      (Sigma.fst : (Σ b, I b) → β) :=
    fun _ _ h => Matrix.blockDiagonal'_apply_ne G _ _ (ne_of_lt h).symm
  rw [ht.det_fintype]
  refine Finset.prod_congr rfl (fun b _ => ?_)
  refine (Matrix.det_reindex_self (Equiv.sigmaSubtype (β := I) b)
    ((Matrix.blockDiagonal' G).toSquareBlock Sigma.fst b)).symm.trans
      (congrArg Matrix.det (Matrix.ext (fun i j => ?_)))
  simp [Matrix.toSquareBlock_def, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.sigmaSubtype]


end KServerConj

open scoped BigOperators

namespace KServerConj

theorem rightInverse_blockDiagonal'_block
    {K β : Type*} [CommRing K] [Fintype β] [DecidableEq β]
    {I J : β → Type*} [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)]
    [∀ b, Fintype (J b)]
    (G : ∀ b, Matrix (I b) (J b) K)
    (C : Matrix (Σ b, J b) (Σ b, I b) K)
    (hC : Matrix.blockDiagonal' G * C = 1) (b : β) :
    G b * C.submatrix (Sigma.mk b) (Sigma.mk b) = 1 := by
  exact Matrix.ext fun i j => by
    simpa [Matrix.mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma,
      Matrix.blockDiagonal'_apply, dite_mul, Finset.sum_dite_irrel, Fintype.sum_dite_eq,
      Matrix.submatrix_apply, Matrix.one_apply] using
        congrFun (congrFun hC ⟨b, i⟩) ⟨b, j⟩


theorem submatrix_blockDiagonal'_sigmaMap
    {K β : Type*} [Zero K] [DecidableEq β] {I J L : β → Type*}
    (G : ∀ b, Matrix (I b) (J b) K) (x : ∀ b, L b → J b) :
    (Matrix.blockDiagonal' G).submatrix id
        (fun p : Σ b, L b => (⟨p.1, x p.1 p.2⟩ : Σ b, J b)) =
      Matrix.blockDiagonal' (fun b => (G b).submatrix id (x b)) := by
  exact Matrix.ext fun ⟨b, i⟩ ⟨c, j⟩ => by
    by_cases h : b = c
    · subst c
      simp [Matrix.submatrix_apply]
    · simp [Matrix.submatrix_apply, Matrix.blockDiagonal'_apply, h]


end KServerConj

open scoped BigOperators

namespace KServerConj

theorem addVal_finset_prod {F β : Type*} [Field F]
    (s : Finset β) (f : β → HahnSeries ℝ F) :
    HahnSeries.addVal ℝ F (∏ b ∈ s, f b) = ∑ b ∈ s, HahnSeries.addVal ℝ F (f b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddValuation.map_one]
  | @insert b s hb ih =>
    simp only [Finset.prod_insert hb, Finset.sum_insert hb, AddValuation.map_mul, ih]


end KServerConj

namespace KServerConj

theorem minorVal_nonneg_of_entries
    {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F))
    (hG : ∀ i j, (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (G i j)) :
    (0 : WithTop ℝ) ≤ minorVal G := by
  simpa only [minorVal_eq_embeddingMinorVal] using
    DetValuationMilestone.zero_le_embeddingMinorVal_of_entries
      (HahnSeries.addVal ℝ F) (AddValuation.map_zero _) (AddValuation.map_one _)
      (fun a => AddValuation.map_neg _ a) (fun a b => AddValuation.map_mul _ a b)
      (fun a b => AddValuation.map_add _ a b) G hG


theorem minimal_basis_coordinates_nonneg
    {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (x : I → J) (μ : ℝ)
    (hμ : minorVal G = (μ : WithTop ℝ))
    (hx : HahnSeries.addVal ℝ F (G.submatrix id x).det = (μ : WithTop ℝ)) :
    ∀ i j, (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (((G.submatrix id x)⁻¹ * G) i j) := by
  exact DetValuationMilestone.minimum_basis_coordinate_nonneg
    (HahnSeries.addVal ℝ F) (AddValuation.map_zero _)
    (fun a b => AddValuation.map_mul _ a b) G x μ
    (by simpa only [(DetValuationMilestone.tupleMinorVal_eq_embeddingMinorVal
        (HahnSeries.addVal ℝ F) (AddValuation.map_zero _)),
      ← minorVal_eq_embeddingMinorVal] using hμ) hx


theorem addVal_det_inverse_of_real_minor
    {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (x : I → J) (μ : ℝ)
    (hx : HahnSeries.addVal ℝ F (G.submatrix id x).det = (μ : WithTop ℝ)) :
    HahnSeries.addVal ℝ F (G.submatrix id x)⁻¹.det = ((-μ : ℝ) : WithTop ℝ) := by
  exact DetValuationMilestone.valuation_det_inverse_of_finite
    (HahnSeries.addVal ℝ F) (AddValuation.map_one _)
    (fun a b => AddValuation.map_mul _ a b) (G.submatrix id x)
    (isUnit_iff_ne_zero.mpr (fun hz => (show (μ : WithTop ℝ) ≠ ⊤ by simp)
      ((hx.symm.trans (congrArg (HahnSeries.addVal ℝ F) hz)).trans (AddValuation.map_zero _)))) μ hx


end KServerConj

open scoped BigOperators

namespace KServerConj

theorem minorVal_blockDiagonal'_eq_top_of_block
    {F β : Type*} [Field F] [Fintype β] [DecidableEq β]
    {I J : β → Type*} [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)]
    [∀ b, Fintype (J b)]
    (G : ∀ b, Matrix (I b) (J b) (HahnSeries ℝ F)) (b : β)
    (hb : minorVal (G b) = ⊤) : minorVal (Matrix.blockDiagonal' G) = ⊤ := by
  exact minorVal_eq_top_of_all_tuple_minors_zero (Matrix.blockDiagonal' G)
    fun x => Classical.byContradiction fun hx =>
      (exists_rightInverse_of_nonzero_minor (Matrix.blockDiagonal' G) x hx).elim fun C hC =>
        (exists_nonzero_minor_of_rightInverse (G b) (C.submatrix (Sigma.mk b) (Sigma.mk b))
          (rightInverse_blockDiagonal'_block G C hC b)).elim fun y hy =>
            (minorVal_ne_top_of_nonzero_minor (G b) y hy) hb


theorem minorVal_blockDiagonal'_of_finite
    {F β : Type*} [Field F] [Fintype β] [DecidableEq β]
    {I J : β → Type*} [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)]
    [∀ b, Fintype (J b)]
    (G : ∀ b, Matrix (I b) (J b) (HahnSeries ℝ F)) (μ : β → ℝ)
    (hμ : ∀ b, minorVal (G b) = (μ b : WithTop ℝ)) :
    minorVal (Matrix.blockDiagonal' G) = ((∑ b, μ b : ℝ) : WithTop ℝ) := by
  classical
  obtain ⟨x, hx⟩ := Classical.axiom_of_choice
    (fun b => exists_minorVal_minimizer (G b) (μ b) (hμ b))
  let A : ∀ b, Matrix (I b) (I b) (HahnSeries ℝ F) :=
    fun b => (G b).submatrix id (x b)
  let B : Matrix (Σ b, I b) (Σ b, I b) (HahnSeries ℝ F) :=
    Matrix.blockDiagonal' (fun b => (A b)⁻¹)
  have hnorm : B * Matrix.blockDiagonal' G =
      Matrix.blockDiagonal' (fun b => (A b)⁻¹ * G b) :=
    (Matrix.blockDiagonal'_mul (fun b => (A b)⁻¹) G).symm
  have hc (b : β) : ∀ i j, (0 : WithTop ℝ) ≤
      HahnSeries.addVal ℝ F (((A b)⁻¹ * G b) i j) :=
    minimal_basis_coordinates_nonneg (G b) (x b) (μ b) (hμ b) (hx b)
  have hi (b : β) : HahnSeries.addVal ℝ F (A b)⁻¹.det = ((-μ b : ℝ) : WithTop ℝ) :=
    addVal_det_inverse_of_real_minor (G b) (x b) (μ b) (hx b)
  have hBval : HahnSeries.addVal ℝ F B.det = ((-∑ b, μ b : ℝ) : WithTop ℝ) := by
    simp only [B, det_blockDiagonal'_general, addVal_finset_prod, hi,
      ← WithTop.coe_sum, Finset.sum_neg_distrib]
  have hH : ∀ p q, (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F
      (Matrix.blockDiagonal' (fun b => (A b)⁻¹ * G b) p q) :=
    fun ⟨b, i⟩ ⟨c, j⟩ => (Classical.em (b = c)).elim
      (fun h => by subst c; simpa only [Matrix.blockDiagonal'_apply_eq] using hc b i j)
      (fun h => by simp only [Matrix.blockDiagonal'_apply_ne _ _ _ h,
        AddValuation.map_zero, le_top])
  have hlower : ((∑ b, μ b : ℝ) : WithTop ℝ) ≤ minorVal (Matrix.blockDiagonal' G) :=
    WithTop.le_of_add_le_add_left (x := ((-∑ b, μ b : ℝ) : WithTop ℝ)) (by simp)
      (by simpa only [← hnorm, minorVal_mul, hBval, ← WithTop.coe_add,
        neg_add_cancel, WithTop.coe_zero] using
          minorVal_nonneg_of_entries (Matrix.blockDiagonal' (fun b => (A b)⁻¹ * G b)) hH)
  have hsel : (Matrix.blockDiagonal' G).submatrix id
      (fun p : Σ b, I b => (⟨p.1, x p.1 p.2⟩ : Σ b, J b)) = Matrix.blockDiagonal' A :=
    submatrix_blockDiagonal'_sigmaMap G (fun b => (x b : I b → J b))
  have hupper : minorVal (Matrix.blockDiagonal' G) ≤ ((∑ b, μ b : ℝ) : WithTop ℝ) := by
    simpa only [hsel, det_blockDiagonal'_general, addVal_finset_prod, A, hx,
      ← WithTop.coe_sum] using
        minorVal_le_tuple (Matrix.blockDiagonal' G)
          (fun p : Σ b, I b => (⟨p.1, x p.1 p.2⟩ : Σ b, J b))
  exact le_antisymm hupper hlower


theorem minorVal_blockDiagonal'
    {F β : Type*} [Field F] [Fintype β] [DecidableEq β]
    {I J : β → Type*} [∀ b, Fintype (I b)] [∀ b, Fintype (J b)]
    (G : ∀ b, Matrix (I b) (J b) (HahnSeries ℝ F)) :
    minorVal (Matrix.blockDiagonal' G) = ∑ b, minorVal (G b) := by
  classical
  exact (Classical.em (∀ b, minorVal (G b) ≠ ⊤)).elim
    (fun h => (Classical.axiom_of_choice
      (fun b => WithTop.ne_top_iff_exists.mp (h b))).elim fun μ hμ => by
        simpa only [← hμ, WithTop.coe_sum] using
          minorVal_blockDiagonal'_of_finite G μ (fun b => (hμ b).symm))
    (fun h => (not_forall.mp h).elim fun b hb =>
      (minorVal_blockDiagonal'_eq_top_of_block G b (not_not.mp hb)).trans
        (show (∑ c, minorVal (G c)) = ⊤ from
          WithTop.sum_eq_top.mpr ⟨b, Finset.mem_univ _, not_not.mp hb⟩).symm)


end KServerConj

open scoped BigOperators

open KServerConj

theorem solution {F : Type*} [Field F] {R ι κ : Type*} [Fintype R] [DecidableEq R] [Fintype ι]
    [Fintype κ] {β : Type*} [Fintype β] [DecidableEq β] {Rb ιb : β → Type*}
    [∀ j, Fintype (Rb j)] [∀ j, Fintype (ιb j)] :
    (∀ (A : Matrix R R (HahnSeries ℝ F)) (G : Matrix R ι (HahnSeries ℝ F)), A.det ≠ 0 →
      minorVal (A * G) = HahnSeries.addVal ℝ F A.det + minorVal G) ∧
    (∀ (Fm : Matrix R κ (HahnSeries ℝ F)) (G : Matrix R ι (HahnSeries ℝ F)),
      (∀ c : κ, ∃ coeffs : ι → HahnSeries ℝ F, (∀ j, 0 ≤ HahnSeries.addVal ℝ F (coeffs j)) ∧
        ∀ i, Fm i c = ∑ j, coeffs j * G i j) →
      minorVal G ≤ minorVal Fm) ∧
    (∀ Gs : ∀ j : β, Matrix (Rb j) (ιb j) (HahnSeries ℝ F),
      minorVal (Matrix.blockDiagonal' Gs) = ∑ j, minorVal (Gs j)) := by
  exact ⟨fun A G _ => minorVal_mul A G,
    fun Fm G h => minorVal_mono_of_column_combinations G Fm (fun c =>
      (h c).elim fun coeff hcoeff =>
        ⟨coeff, hcoeff.1, fun i => (hcoeff.2 i).trans
          (Finset.sum_congr rfl (fun j _ => mul_comm _ _))⟩),
    fun Gs => minorVal_blockDiagonal' Gs⟩

#print axioms solution
