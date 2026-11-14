-- Prove2me | solution 1 for KServerConj.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T02:25:46.86657+00:00
-- url     : https://prove2.me/submissions/3606e6cc-011d-464f-8601-9d78bfadd2ce

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Definitions.Def_KServerConj_Psi
import Definitions.Def_KServerConj_Hmat
set_option autoImplicit false

section PaperFile004
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
end PaperFile004

section PaperFile005
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
end PaperFile005

section PaperFile006
open scoped BigOperators

namespace DetValuationMilestone

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
end PaperFile006

section PaperFile007
open scoped BigOperators

namespace DetValuationMilestone

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
end PaperFile007

section PaperFile008
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
end PaperFile008

section PaperFile009
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
end PaperFile009

section PaperFile010
open scoped BigOperators

namespace KServerConj

noncomputable def quadraticMatrix {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F) :
    Matrix (Sym2 (Fin k)) (Sym2 M) (HahnSeries ℝ F) :=
  fun p c => Sym2.lift ⟨fun x y =>
    HahnSeries.single (-dist x y) (1 : F) * symProd (q x) (q y) p,
    fun x y => by
      dsimp only
      rw [dist_comm, symProd_comm]⟩ c

theorem Qmat_eq_quadraticMatrix {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → K k M) : Qmat q = quadraticMatrix q := rfl

noncomputable def weightedColumns {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F) (r : M) :
    Matrix (Fin k) M (HahnSeries ℝ F) :=
  fun i x => HahnSeries.single (-dist r x) (1 : F) * q x i

noncomputable def negPairDist {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (x : Fin k → M) : Sym2 (Fin k) → ℝ :=
  Sym2.lift ⟨fun i j => -dist (x i) (x j),
    fun i j => congrArg Neg.neg (dist_comm (x i) (x j))⟩

theorem quadraticMatrix_submatrix {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) :
    (quadraticMatrix q).submatrix id (Sym2.map x) =
      Matrix.of (fun r c => HahnSeries.single (negPairDist x c) (1 : F) *
        sym2Mat (Matrix.of (fun i j => q (x j) i)) r c) := by
  funext r c
  induction c using Sym2.ind with
  | _ i j => rfl

end KServerConj
end PaperFile010

section PaperFile011
open scoped BigOperators

namespace KServerConj

@[simp] theorem symProd_apply {R : Type*} [CommRing R] {k : ℕ}
    (a b : Fin k → R) (i j : Fin k) :
    symProd a b s(i, j) =
      if i = j then a i * b i else a i * b j + a j * b i := by
  rfl

theorem symProd_add_left {R : Type*} [CommRing R] {k : ℕ}
    (a b c : Fin k → R) : symProd (a + b) c = symProd a c + symProd b c := by
  funext p
  induction p using Sym2.ind with
  | _ i j =>
    simp only [Pi.add_apply, symProd_apply]
    split_ifs <;> ring

theorem symProd_smul_left {R : Type*} [CommRing R] {k : ℕ}
    (c : R) (a b : Fin k → R) : symProd (c • a) b = c • symProd a b := by
  funext p
  induction p using Sym2.ind with
  | _ i j =>
    simp only [Pi.smul_apply, symProd_apply, smul_eq_mul]
    split_ifs <;> ring

theorem symProd_add_right {R : Type*} [CommRing R] {k : ℕ}
    (a b c : Fin k → R) : symProd a (b + c) = symProd a b + symProd a c := by
  simpa only [symProd_comm] using symProd_add_left b c a

theorem symProd_smul_right {R : Type*} [CommRing R] {k : ℕ}
    (c : R) (a b : Fin k → R) : symProd a (c • b) = c • symProd a b := by
  simpa only [symProd_comm] using symProd_smul_left c b a

def symProdBilin {R : Type*} [CommRing R] {k : ℕ} :
    (Fin k → R) →ₗ[R] (Fin k → R) →ₗ[R] (Sym2 (Fin k) → R) where
  toFun a :=
    { toFun := symProd a
      map_add' := symProd_add_right a
      map_smul' c b := symProd_smul_right c a b }
  map_add' a b := LinearMap.ext fun c => symProd_add_left a b c
  map_smul' c a := LinearMap.ext fun b => symProd_smul_left c a b

@[simp] theorem symProd_single_single {R : Type*} [CommRing R] {k : ℕ}
    (i j : Fin k) :
    symProd (Pi.single i (1 : R)) (Pi.single j (1 : R)) = Pi.single s(i, j) 1 := by
  funext p
  induction p using Sym2.ind with
  | _ l m =>
    by_cases hlm : l = m <;> by_cases hli : l = i <;> by_cases hlj : l = j <;>
      by_cases hmi : m = i <;> by_cases hmj : m = j <;>
      simp_all [symProd_apply, Pi.single_apply]

@[simp] theorem sym2Mat_col {R : Type*} [CommRing R] {k : ℕ}
    (A : Matrix (Fin k) (Fin k) R) (i j : Fin k) :
    (sym2Mat A).col s(i, j) = symProd (A.col i) (A.col j) := rfl

theorem sym2Mat_mulVec_symProd {R : Type*} [CommRing R] {k : ℕ}
    (A : Matrix (Fin k) (Fin k) R) (a b : Fin k → R) :
    (sym2Mat A).mulVec (symProd a b) = symProd (A.mulVec a) (A.mulVec b) := by
  have h : (symProdBilin (R := R) (k := k)).compr₂ (sym2Mat A).mulVecLin =
      (symProdBilin (R := R) (k := k)).compl₁₂ A.mulVecLin A.mulVecLin := by
    apply (Pi.basisFun R (Fin k)).ext
    intro i
    apply (Pi.basisFun R (Fin k)).ext
    intro j
    simp only [Pi.basisFun_apply, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
    simp [symProdBilin, symProd_single_single]
  exact congrArg (fun f => f a b) h

@[simp] theorem sym2Mat_one {R : Type*} [CommRing R] (k : ℕ) :
    sym2Mat (1 : Matrix (Fin k) (Fin k) R) = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro c
  induction c using Sym2.ind with
  | _ i j =>
    simpa only [symProd_single_single, Matrix.one_mulVec] using
      sym2Mat_mulVec_symProd (1 : Matrix (Fin k) (Fin k) R)
        (Pi.single i 1) (Pi.single j 1)

theorem sym2Mat_mul {R : Type*} [CommRing R] {k : ℕ}
    (A B : Matrix (Fin k) (Fin k) R) :
    sym2Mat (A * B) = sym2Mat A * sym2Mat B := by
  apply Matrix.ext_of_mulVec_single
  intro c
  induction c using Sym2.ind with
  | _ i j =>
    simp only [← symProd_single_single, ← Matrix.mulVec_mulVec, sym2Mat_mulVec_symProd]

end KServerConj
end PaperFile011

section PaperFile012
namespace KServerConj

def sym2FinSuccEmbed (n : ℕ) :
    Fin (n + 1) ⊕ Sym2 (Fin n) → Sym2 (Fin (n + 1))
  | Sum.inl i => s(0, i)
  | Sum.inr p => p.map Fin.succ

theorem sym2FinSucc_top_ne_bottom (n : ℕ) (i : Fin (n + 1)) (p : Sym2 (Fin n)) :
    s((0 : Fin (n + 1)), i) ≠ p.map Fin.succ := by
  induction p using Sym2.ind with
  | _ a b =>
    simp [(Fin.succ_ne_zero a).symm, (Fin.succ_ne_zero b).symm]

theorem sym2FinSuccEmbed_injective (n : ℕ) : Function.Injective (sym2FinSuccEmbed n) := by
  intro x y h
  rcases x with i | p <;> rcases y with j | q
  · exact congrArg Sum.inl ((Sym2.eq_iff.mp h).elim And.right (fun h => h.2.trans h.1))
  · exact False.elim (sym2FinSucc_top_ne_bottom n i q h)
  · exact False.elim (sym2FinSucc_top_ne_bottom n j p h.symm)
  · exact congrArg Sum.inr (Sym2.map.injective (Fin.succ_injective n) h)

theorem sym2FinSuccEmbed_surjective (n : ℕ) : Function.Surjective (sym2FinSuccEmbed n) := by
  intro p
  induction p using Sym2.ind with
  | _ i j =>
    cases i using Fin.cases with
    | zero => exact ⟨Sum.inl j, rfl⟩
    | succ i =>
      cases j using Fin.cases with
      | zero => exact ⟨Sum.inl i.succ, Sym2.eq_swap⟩
      | succ j => exact ⟨Sum.inr s(i, j), rfl⟩

noncomputable def sym2FinSuccEquiv (n : ℕ) :
    Sym2 (Fin (n + 1)) ≃ Fin (n + 1) ⊕ Sym2 (Fin n) :=
  (Equiv.ofBijective (sym2FinSuccEmbed n)
    ⟨sym2FinSuccEmbed_injective n, sym2FinSuccEmbed_surjective n⟩).symm

@[simp] theorem sym2FinSuccEquiv_symm_inl (n : ℕ) (i : Fin (n + 1)) :
    (sym2FinSuccEquiv n).symm (Sum.inl i) = s(0, i) := rfl

@[simp] theorem sym2FinSuccEquiv_symm_inr (n : ℕ) (p : Sym2 (Fin n)) :
    (sym2FinSuccEquiv n).symm (Sum.inr p) = p.map Fin.succ := rfl

@[simp] theorem sym2FinSuccEquiv_mk_zero (n : ℕ) (i : Fin (n + 1)) :
    sym2FinSuccEquiv n s(0, i) = Sum.inl i := by
  simpa only [sym2FinSuccEquiv_symm_inl] using
    (sym2FinSuccEquiv n).apply_symm_apply (Sum.inl i)

@[simp] theorem sym2FinSuccEquiv_map_succ (n : ℕ) (p : Sym2 (Fin n)) :
    sym2FinSuccEquiv n (p.map Fin.succ) = Sum.inr p := by
  simpa only [sym2FinSuccEquiv_symm_inr] using
    (sym2FinSuccEquiv n).apply_symm_apply (Sum.inr p)

theorem symProd_split_top {R : Type*} [CommRing R] {n : ℕ}
    (a b : Fin (n + 1) → R) (i : Fin (n + 1)) :
    symProd a b ((sym2FinSuccEquiv n).symm (Sum.inl i)) =
      if i = 0 then a 0 * b 0 else a 0 * b i + a i * b 0 := by
  simp [symProd_apply, eq_comm]

@[simp] theorem symProd_split_top_zero {R : Type*} [CommRing R] {n : ℕ}
    (a b : Fin (n + 1) → R) :
    symProd a b ((sym2FinSuccEquiv n).symm (Sum.inl 0)) = a 0 * b 0 := by
  simp [symProd_apply]

theorem symProd_split_top_succ {R : Type*} [CommRing R] {n : ℕ}
    (a b : Fin (n + 1) → R) (i : Fin n) :
    symProd a b ((sym2FinSuccEquiv n).symm (Sum.inl i.succ)) =
      a 0 * b i.succ + a i.succ * b 0 := by
  simp [symProd_apply, (Fin.succ_ne_zero i).symm]

theorem symProd_split_bottom {R : Type*} [CommRing R] {n : ℕ}
    (a b : Fin (n + 1) → R) (p : Sym2 (Fin n)) :
    symProd a b ((sym2FinSuccEquiv n).symm (Sum.inr p)) =
      symProd (fun i => a i.succ) (fun i => b i.succ) p := by
  induction p using Sym2.ind with
  | _ i j =>
    simp only [sym2FinSuccEquiv_symm_inr, Sym2.map_mk, symProd_apply,
      (Fin.succ_injective n).eq_iff]

theorem symProd_e0_split_top {R : Type*} [CommRing R] {n : ℕ}
    (h : Fin (n + 1) → R) (i : Fin (n + 1)) :
    symProd (Pi.single 0 1) h ((sym2FinSuccEquiv n).symm (Sum.inl i)) = h i := by
  by_cases hi : i = 0 <;> simp [hi, eq_comm]

theorem symProd_e0_split_bottom {R : Type*} [CommRing R] {n : ℕ}
    (h : Fin (n + 1) → R) (p : Sym2 (Fin n)) :
    symProd (Pi.single 0 1) h ((sym2FinSuccEquiv n).symm (Sum.inr p)) = 0 := by
  induction p using Sym2.ind with
  | _ i j =>
    simp [symProd_apply]

theorem symProd_e0_split {R : Type*} [CommRing R] {n : ℕ} (h : Fin (n + 1) → R) :
    (fun p : Fin (n + 1) ⊕ Sym2 (Fin n) =>
      symProd (Pi.single 0 1) h ((sym2FinSuccEquiv n).symm p)) =
      Sum.elim h (fun _ => 0) := by
  exact funext (Sum.rec (symProd_e0_split_top h) (symProd_e0_split_bottom h))

end KServerConj
end PaperFile012

section PaperFile013
namespace KServerConj

@[simp] theorem quadraticMatrix_apply_pair {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F)
    (p : Sym2 (Fin k)) (x y : M) :
    quadraticMatrix q p s(x, y) =
      HahnSeries.single (-dist x y) (1 : F) * symProd (q x) (q y) p := rfl

theorem quadraticMatrix_request_column {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M)
    (hqr : q r = Pi.single 0 1) (x : M) :
    (quadraticMatrix q).col s(r, x) =
      symProd (Pi.single 0 1) (fun i => weightedColumns q r i x) := by
  funext p
  change HahnSeries.single (-dist r x) (1 : F) * symProd (q r) (q x) p =
    symProd (Pi.single 0 1) (HahnSeries.single (-dist r x) (1 : F) • q x) p
  rw [hqr, symProd_smul_right]
  rfl

theorem quadraticMatrix_request_top {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M)
    (hqr : q r = Pi.single 0 1) (x : M) (i : Fin (n + 1)) :
    quadraticMatrix q ((sym2FinSuccEquiv n).symm (Sum.inl i)) s(r, x) =
      weightedColumns q r i x := by
  exact (congrFun (quadraticMatrix_request_column q r hqr x)
    ((sym2FinSuccEquiv n).symm (Sum.inl i))).trans
      (symProd_e0_split_top (fun i => weightedColumns q r i x) i)

theorem quadraticMatrix_request_bottom {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M)
    (hqr : q r = Pi.single 0 1) (x : M) (p : Sym2 (Fin n)) :
    quadraticMatrix q ((sym2FinSuccEquiv n).symm (Sum.inr p)) s(r, x) = 0 := by
  exact (congrFun (quadraticMatrix_request_column q r hqr x)
    ((sym2FinSuccEquiv n).symm (Sum.inr p))).trans
      (symProd_e0_split_bottom (fun i => weightedColumns q r i x) p)

theorem quadraticMatrix_split_bottom {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin (n + 1) → HahnSeries ℝ F)
    (p : Sym2 (Fin n)) (c : Sym2 M) :
    quadraticMatrix q ((sym2FinSuccEquiv n).symm (Sum.inr p)) c =
      quadraticMatrix (fun x (i : Fin n) => q x i.succ) p c := by
  induction c using Sym2.ind with
  | _ x y =>
    exact congrArg (fun z => HahnSeries.single (-dist x y) (1 : F) * z)
      (symProd_split_bottom (q x) (q y) p)

theorem quadraticMatrix_exists_old_minor {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M)
    (hqr : q r = Pi.single 0 1) (x : Fin (n + 1) → M)
    (y : Sym2 (Fin n) → Sym2 M) :
    ∃ c : Sym2 (Fin (n + 1)) → Sym2 M,
      ((quadraticMatrix q).submatrix id c).det =
        ((weightedColumns q r).submatrix id x).det *
          ((quadraticMatrix (fun m (i : Fin n) => q m i.succ)).submatrix id y).det := by
  let e := sym2FinSuccEquiv n
  let c : Sym2 (Fin (n + 1)) → Sym2 M :=
    fun p => Sum.elim (fun i => s(r, x i)) y (e p)
  let A := (weightedColumns q r).submatrix id x
  let D := (quadraticMatrix (fun m (i : Fin n) => q m i.succ)).submatrix id y
  let B : Matrix (Fin (n + 1)) (Sym2 (Fin n)) (HahnSeries ℝ F) :=
    fun i j => quadraticMatrix q (e.symm (Sum.inl i)) (y j)
  have hblock : Matrix.reindex e e ((quadraticMatrix q).submatrix id c) =
      Matrix.fromBlocks A B 0 D := by
    funext u v
    rcases u with i | p <;> rcases v with j | t
    · change quadraticMatrix q (e.symm (Sum.inl i)) (c (e.symm (Sum.inl j))) =
        weightedColumns q r i (x j)
      simpa only [c, e, Equiv.apply_symm_apply, Sum.elim_inl] using
        quadraticMatrix_request_top q r hqr (x j) i
    · change quadraticMatrix q (e.symm (Sum.inl i)) (c (e.symm (Sum.inr t))) =
        quadraticMatrix q (e.symm (Sum.inl i)) (y t)
      simp only [c, e, Equiv.apply_symm_apply, Sum.elim_inr]
    · change quadraticMatrix q (e.symm (Sum.inr p)) (c (e.symm (Sum.inl j))) = 0
      simpa only [c, e, Equiv.apply_symm_apply, Sum.elim_inl] using
        quadraticMatrix_request_bottom q r hqr (x j) p
    · change quadraticMatrix q (e.symm (Sum.inr p)) (c (e.symm (Sum.inr t))) =
        quadraticMatrix (fun m (i : Fin n) => q m i.succ) p (y t)
      simpa only [c, e, Equiv.apply_symm_apply, Sum.elim_inr] using
        quadraticMatrix_split_bottom q p (y t)
  exact ⟨c, (Matrix.det_reindex_self e ((quadraticMatrix q).submatrix id c)).symm.trans
    ((congrArg Matrix.det hblock).trans (Matrix.det_fromBlocks_zero₂₁ A B D))⟩

end KServerConj
end PaperFile013

section PaperFile014
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
end PaperFile014

section PaperFile015
namespace KServerConj

theorem quadraticMatrix_old_bound_finite {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M)
    (hqr : q r = Pi.single 0 1) (a b : ℝ)
    (ha : minorVal (weightedColumns q r) = (a : WithTop ℝ))
    (hb : minorVal (quadraticMatrix (fun m (i : Fin n) => q m i.succ)) = (b : WithTop ℝ)) :
    minorVal (quadraticMatrix q) ≤ ((a + b : ℝ) : WithTop ℝ) := by
  obtain ⟨x, hx⟩ := exists_minorVal_minimizer (weightedColumns q r) a ha
  obtain ⟨y, hy⟩ := exists_minorVal_minimizer
    (quadraticMatrix (fun m (i : Fin n) => q m i.succ)) b hb
  obtain ⟨c, hc⟩ := quadraticMatrix_exists_old_minor q r hqr x y
  have hval : HahnSeries.addVal ℝ F ((quadraticMatrix q).submatrix id c).det =
      ((a + b : ℝ) : WithTop ℝ) := by
    simpa only [AddValuation.map_mul, hx, hy, WithTop.coe_add] using
      congrArg (HahnSeries.addVal ℝ F) hc
  exact (minorVal_le_tuple (quadraticMatrix q) c).trans_eq hval

theorem quadraticMatrix_old_bound {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M)
    (hqr : q r = Pi.single 0 1) :
    minorVal (quadraticMatrix q) ≤
      minorVal (quadraticMatrix (fun m (i : Fin n) => q m i.succ)) +
        minorVal (weightedColumns q r) := by
  by_cases hH : minorVal (weightedColumns q r) = ⊤
  · simp [hH]
  by_cases hT : minorVal (quadraticMatrix (fun m (i : Fin n) => q m i.succ)) = ⊤
  · simp [hT]
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hH
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hT
  simpa only [← ha, ← hb, WithTop.coe_add, add_comm] using
    quadraticMatrix_old_bound_finite q r hqr a b ha.symm hb.symm

end KServerConj
end PaperFile015

open KServerConj

theorem solution {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M] {m : ℕ}
    (hm : 1 ≤ m) (q : M → Fin (m + 1) → K (m + 1) M) (r : M) (hr : q r = Pi.single 0 1) :
    Psi q ≤ minorVal (Qhat q) + minorVal (Hmat q r) := by
  change minorVal (quadraticMatrix q) ≤
    minorVal (quadraticMatrix (fun x (i : Fin m) => q x i.succ)) +
      minorVal (weightedColumns q r)
  exact quadraticMatrix_old_bound q r hr

#print axioms solution
