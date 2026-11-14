-- Prove2me | solution 1 for KServerConj.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T03:16:13.333022+00:00
-- url     : https://prove2.me/submissions/71a3c04c-54ab-4564-ae31-cc3ebffcf596

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Definitions.Def_KServerConj_Psi
import Definitions.Def_KServerConj_Hmat
import Definitions.Def_KServerConj_rowReplace
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
open scoped BigOperators

namespace KServerConj

noncomputable def finSuccThreeBlockEquiv (m : ℕ) : Fin (m + 1) ≃ PUnit ⊕ Fin m :=
  (finSuccEquiv m).trans ((Equiv.optionEquivSumPUnit (Fin m)).trans (Equiv.sumComm _ _))

noncomputable def quadraticThreeBlockEquiv (m : ℕ) :
    Sym2 (Fin (m + 1)) ≃ PUnit ⊕ (Fin m ⊕ Sym2 (Fin m)) :=
  (sym2FinSuccEquiv m).trans
    ((Equiv.sumCongr (finSuccThreeBlockEquiv m) (Equiv.refl _)).trans (Equiv.sumAssoc _ _ _))

@[simp] theorem quadraticThreeBlockEquiv_symm_first (m : ℕ) (u : PUnit) :
    (quadraticThreeBlockEquiv m).symm (Sum.inl u) = s(0, 0) := by
  simp [quadraticThreeBlockEquiv, finSuccThreeBlockEquiv]

@[simp] theorem quadraticThreeBlockEquiv_symm_middle (m : ℕ) (i : Fin m) :
    (quadraticThreeBlockEquiv m).symm (Sum.inr (Sum.inl i)) = s(0, i.succ) := by
  simp [quadraticThreeBlockEquiv, finSuccThreeBlockEquiv]

@[simp] theorem quadraticThreeBlockEquiv_symm_last (m : ℕ) (p : Sym2 (Fin m)) :
    (quadraticThreeBlockEquiv m).symm (Sum.inr (Sum.inr p)) = p.map Fin.succ := by
  simp [quadraticThreeBlockEquiv]

noncomputable def quadraticNewReference {F : Type*} [Field F] {m : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin (m + 1) → HahnSeries ℝ F) (r : M) :
    Matrix (PUnit ⊕ (Fin m ⊕ Sym2 (Fin m))) (PUnit ⊕ (M ⊕ Sym2 M)) (HahnSeries ℝ F) :=
  Matrix.fromBlocks 1 0 0
    (Matrix.fromBlocks ((weightedColumns q r).submatrix Fin.succ id) 0 0
      (quadraticMatrix (fun y => Fin.tail (q y))))

noncomputable def quadraticNewCoefficients {F : Type*} [Field F] {M : Type*}
    [PseudoMetricSpace M] [DecidableEq M] (r : M) (δ : M → HahnSeries ℝ F) (x y : M) :
    PUnit ⊕ (M ⊕ Sym2 M) → HahnSeries ℝ F :=
  Sum.elim (fun _ => HahnSeries.single (-dist x y) (1 : F) * δ x * δ y)
    (Sum.elim (fun z =>
      (Pi.single y (HahnSeries.single (dist r y - dist x y) (1 : F) * δ x) :
        M → HahnSeries ℝ F) z +
      (Pi.single x (HahnSeries.single (dist r x - dist x y) (1 : F) * δ y) :
        M → HahnSeries ℝ F) z)
      (Pi.single s(x, y) 1 : Sym2 M → HahnSeries ℝ F))

theorem single_neg_mul_sub {F : Type*} [Field F] (a b : ℝ) :
    (HahnSeries.single (-a) (1 : F) : HahnSeries ℝ F) *
        HahnSeries.single (a - b) 1 = HahnSeries.single (-b) 1 := by
  simp [HahnSeries.single_mul_single, sub_eq_add_neg, ← add_assoc]

theorem weightedColumns_mul_shift {F : Type*} [Field F] {m : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin m → HahnSeries ℝ F) (r y : M)
    (i : Fin m) (b : ℝ) (a : HahnSeries ℝ F) :
    weightedColumns q r i y * (HahnSeries.single (dist r y - b) (1 : F) * a) =
      HahnSeries.single (-b) (1 : F) * a * q y i := by
  calc
    _ = (HahnSeries.single (-dist r y) (1 : F) *
        HahnSeries.single (dist r y - b) (1 : F)) * a * q y i := by
      dsimp only [weightedColumns]
      ring
    _ = _ := by rw [single_neg_mul_sub]

theorem quadraticNewColumn_expansion {F : Type*} [Field F] {m : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin (m + 1) → HahnSeries ℝ F) (r : M) (δ : M → HahnSeries ℝ F)
    (x y : M) (i : PUnit ⊕ (Fin m ⊕ Sym2 (Fin m))) :
    quadraticMatrix (fun z => Fin.cons (δ z) (Fin.tail (q z)))
        ((quadraticThreeBlockEquiv m).symm i) s(x, y) =
      ∑ j, quadraticNewReference q r i j * quadraticNewCoefficients r δ x y j := by
  rcases i with u | (i | p)
  · simp [quadraticNewReference, quadraticNewCoefficients, mul_assoc]
  · simp [quadraticNewReference, quadraticNewCoefficients, symProd_apply, Fin.tail,
      Pi.single_apply, mul_ite, mul_add, Finset.sum_add_distrib, weightedColumns_mul_shift]
    simp only [(Fin.succ_ne_zero i).symm, if_false, mul_assoc, mul_comm, mul_left_comm]
  · induction p using Sym2.ind with
    | _ i j =>
      simp [quadraticNewReference, quadraticNewCoefficients, quadraticMatrix, symProd,
        Pi.single_apply, mul_ite, Fin.tail]

end KServerConj
end PaperFile014

section PaperFile015
namespace KServerConj

theorem addVal_single_one {F : Type*} [Field F] (a : ℝ) :
    HahnSeries.addVal ℝ F (HahnSeries.single a (1 : F)) = (a : WithTop ℝ) := by
  exact HahnSeries.orderTop_single one_ne_zero

theorem quadraticNew_unit_nonneg {F : Type*} [Field F] {M : Type*} [PseudoMetricSpace M]
    (r : M) (δ : M → HahnSeries ℝ F)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ)) (x y : M) :
    (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F
      (HahnSeries.single (-dist x y) (1 : F) * δ x * δ y) := by
  rw [AddValuation.map_mul, AddValuation.map_mul, addVal_single_one, hδ, hδ,
    ← WithTop.coe_add, ← WithTop.coe_add]
  exact WithTop.coe_le_coe.mpr (by
    linarith [show dist x y ≤ dist r x + dist r y by
      simpa only [dist_comm x r] using dist_triangle x r y])

theorem quadraticNew_middle_nonneg {F : Type*} [Field F] {M : Type*} [PseudoMetricSpace M]
    (r : M) (δ : M → HahnSeries ℝ F)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ)) (x y : M) :
    (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F
      (HahnSeries.single (dist r y - dist x y) (1 : F) * δ x) := by
  rw [AddValuation.map_mul, addVal_single_one, hδ, ← WithTop.coe_add]
  exact WithTop.coe_le_coe.mpr (by
    linarith [show dist x y ≤ dist r x + dist r y by
      simpa only [dist_comm x r] using dist_triangle x r y])

theorem addVal_pi_single_nonneg {F J : Type*} [Field F] [DecidableEq J]
    (j z : J) (a : HahnSeries ℝ F) (ha : (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F a) :
    (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F ((Pi.single j a : J → HahnSeries ℝ F) z) := by
  rw [Pi.single_apply]
  split_ifs
  · exact ha
  · simpa only [AddValuation.map_zero] using (le_top : (0 : WithTop ℝ) ≤ ⊤)

theorem quadraticNewCoefficients_nonneg {F : Type*} [Field F] {M : Type*}
    [PseudoMetricSpace M] [DecidableEq M] (r : M) (δ : M → HahnSeries ℝ F)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ)) (x y : M)
    (j : PUnit ⊕ (M ⊕ Sym2 M)) :
    (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (quadraticNewCoefficients r δ x y j) := by
  rcases j with u | (z | p)
  · exact quadraticNew_unit_nonneg r δ hδ x y
  · exact (le_min
      (addVal_pi_single_nonneg y z _ (quadraticNew_middle_nonneg r δ hδ x y))
      (addVal_pi_single_nonneg x z _ (by
        simpa only [dist_comm y x] using quadraticNew_middle_nonneg r δ hδ y x))).trans
      (AddValuation.map_add _ _ _)
  · exact addVal_pi_single_nonneg s(x, y) p 1 (by simp [AddValuation.map_one])

end KServerConj
end PaperFile015

section PaperFile016
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
end PaperFile016

section PaperFile017
namespace KServerConj

theorem det_row_equiv_tuple {R I I' J : Type*} [CommRing R]
    [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
    (G : Matrix I J R) (e : I' ≃ I) (x : I → J) :
    ((G.submatrix e id).submatrix id (x ∘ e)).det = (G.submatrix id x).det := by
  simpa only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] using
    Matrix.det_submatrix_equiv_self e (G.submatrix id x)

theorem minorVal_row_equiv_le {F I I' J : Type*} [Field F]
    [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (e : I' ≃ I) :
    minorVal (G.submatrix e id) ≤ minorVal G := by
  rw [minorVal_eq_embeddingMinorVal G]
  exact Finset.le_inf (fun x _ => (minorVal_le_tuple (G.submatrix e id) (x ∘ e)).trans_eq
    (congrArg (HahnSeries.addVal ℝ F) (det_row_equiv_tuple G e x)))

theorem minorVal_row_equiv {F I I' J : Type*} [Field F]
    [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (e : I' ≃ I) :
    minorVal (G.submatrix e id) = minorVal G := by
  refine le_antisymm (minorVal_row_equiv_le G e) ?_
  simpa only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Function.comp_id,
    Matrix.submatrix_id_id] using minorVal_row_equiv_le (G.submatrix e id) e.symm

end KServerConj
end PaperFile017

section PaperFile018
open scoped BigOperators

namespace DetValuationMilestone

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
end PaperFile018

section PaperFile019
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
end PaperFile019

section PaperFile020
open scoped BigOperators

namespace KServerConj

theorem quadraticNewReference_le_updated_minorVal {F : Type*} [Field F]
    {m : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (m + 1) → HahnSeries ℝ F) (r : M) (δ : M → HahnSeries ℝ F)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ)) :
    minorVal (quadraticNewReference q r) ≤
      minorVal (quadraticMatrix (fun y => Fin.cons (δ y) (Fin.tail (q y)))) := by
  classical
  exact (minorVal_mono_of_column_combinations (quadraticNewReference q r)
    ((quadraticMatrix (fun y => Fin.cons (δ y) (Fin.tail (q y)))).submatrix
      (quadraticThreeBlockEquiv m).symm id) (by
        intro c
        induction c using Sym2.ind with
        | _ x y =>
          exact ⟨quadraticNewCoefficients r δ x y,
            quadraticNewCoefficients_nonneg r δ hδ x y,
            quadraticNewColumn_expansion q r δ x y⟩)).trans_eq
      (minorVal_row_equiv (quadraticMatrix (fun y => Fin.cons (δ y) (Fin.tail (q y))))
        (quadraticThreeBlockEquiv m).symm)

end KServerConj
end PaperFile020

section PaperFile021
open scoped BigOperators

namespace KServerConj

noncomputable def quadraticCoeffSingle {F : Type*} [Field F] {M : Type*}
    [DecidableEq M] (p : Sym2 M) (a : HahnSeries ℝ F) : Sym2 M → HahnSeries ℝ F :=
  Pi.single p a

noncomputable def quadraticOldTailCoefficients {F : Type*} [Field F] {M : Type*}
    [PseudoMetricSpace M] [DecidableEq M] (r : M) (δ : M → HahnSeries ℝ F)
    (x y : M) : Sym2 M → HahnSeries ℝ F :=
  quadraticCoeffSingle s(x, y) 1 -
    quadraticCoeffSingle s(r, y) ((δ r)⁻¹ * HahnSeries.single (dist r y - dist x y) 1 * δ x) -
    quadraticCoeffSingle s(r, x) ((δ r)⁻¹ * HahnSeries.single (dist r x - dist x y) 1 * δ y) +
    quadraticCoeffSingle s(r, r) ((δ r)⁻¹ * (δ r)⁻¹ * HahnSeries.single (-dist x y) 1 * δ x * δ y)

theorem quadraticOldTailCoefficients_comm {F : Type*} [Field F] {M : Type*}
    [PseudoMetricSpace M] [DecidableEq M] (r : M) (δ : M → HahnSeries ℝ F) (x y : M) :
    quadraticOldTailCoefficients r δ x y = quadraticOldTailCoefficients r δ y x := by
  funext p
  have hxy : (s(x, y) : Sym2 M) = s(y, x) := Sym2.eq_swap
  simp only [quadraticOldTailCoefficients, hxy, dist_comm x y, Pi.add_apply, Pi.sub_apply]
  congr 1
  · ring
  · congr 1
    ring

noncomputable def quadraticOldCoefficients {F : Type*} [Field F] {M : Type*}
    [PseudoMetricSpace M] [DecidableEq M] (r : M) (δ : M → HahnSeries ℝ F) :
    PUnit ⊕ (M ⊕ Sym2 M) → Sym2 M → HahnSeries ℝ F :=
  Sum.elim (fun _ => quadraticCoeffSingle s(r, r) ((δ r)⁻¹ * (δ r)⁻¹))
    (Sum.elim (fun x =>
      quadraticCoeffSingle s(r, x) (δ r)⁻¹ -
        quadraticCoeffSingle s(r, r) ((δ r)⁻¹ * (δ r)⁻¹ * HahnSeries.single (-dist r x) 1 * δ x))
      (Sym2.lift ⟨quadraticOldTailCoefficients r δ, quadraticOldTailCoefficients_comm r δ⟩))

theorem quadraticOldCoefficients_nonneg {F : Type*} [Field F] {M : Type*}
    [PseudoMetricSpace M] [DecidableEq M] (r : M) (δ : M → HahnSeries ℝ F)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ))
    (j : PUnit ⊕ (M ⊕ Sym2 M)) (z : Sym2 M) :
    (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (quadraticOldCoefficients r δ j z) := by
  have hinv : HahnSeries.addVal ℝ F (δ r)⁻¹ = 0 := by
    simp only [AddValuation.map_inv, hδ, dist_self, WithTop.coe_zero, neg_zero]
  have hradial (x : M) :
      HahnSeries.addVal ℝ F (HahnSeries.single (-dist r x) 1 * δ x) = 0 := by
    simp only [AddValuation.map_mul, addVal_single_one, hδ, ← WithTop.coe_add,
      neg_add_cancel, WithTop.coe_zero]
  have hunit (f : HahnSeries ℝ F) (hf : (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F f) :
      (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F ((δ r)⁻¹ * f) := by
    simpa only [AddValuation.map_mul, hinv, zero_add] using hf
  have hadd {a b : HahnSeries ℝ F}
      (ha : (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F a)
      (hb : (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F b) :
      (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (a + b) :=
    (le_min ha hb).trans (AddValuation.map_add _ _ _)
  have hsub {a b : HahnSeries ℝ F}
      (ha : (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F a)
      (hb : (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F b) :
      (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (a - b) := by
    simpa only [sub_eq_add_neg, AddValuation.map_neg] using
      hadd ha (show (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (-b) by
        simpa only [AddValuation.map_neg] using hb)
  rcases j with u | (x | p)
  · simp only [quadraticOldCoefficients, Sum.elim_inl, quadraticCoeffSingle]
    exact addVal_pi_single_nonneg _ _ _ (hunit _ hinv.ge)
  · simp only [quadraticOldCoefficients, Sum.elim_inr, Sum.elim_inl,
      Pi.sub_apply, quadraticCoeffSingle]
    apply hsub
    · exact addVal_pi_single_nonneg _ _ _ hinv.ge
    · apply addVal_pi_single_nonneg
      simpa only [mul_assoc] using hunit _ (hunit _ (hradial x).ge)
  · induction p using Sym2.ind with
    | _ x y =>
      simp only [quadraticOldCoefficients, Sum.elim_inr, Sym2.lift_mk,
        quadraticOldTailCoefficients, Pi.add_apply, Pi.sub_apply, quadraticCoeffSingle]
      apply hadd
      · apply hsub
        · apply hsub
          · exact addVal_pi_single_nonneg _ _ _ (by simp only [AddValuation.map_one, le_refl])
          · apply addVal_pi_single_nonneg
            simpa only [mul_assoc] using hunit _ (quadraticNew_middle_nonneg r δ hδ x y)
        · apply addVal_pi_single_nonneg
          simpa only [mul_assoc, dist_comm y x] using
            hunit _ (quadraticNew_middle_nonneg r δ hδ y x)
      · apply addVal_pi_single_nonneg
        simpa only [mul_assoc] using hunit _ (hunit _ (quadraticNew_unit_nonneg r δ hδ x y))

theorem quadraticOldColumn_expansion {F : Type*} [Field F] {m : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin (m + 1) → HahnSeries ℝ F) (r : M) (δ : M → HahnSeries ℝ F)
    (hr : q r = Pi.single 0 1) (hc : δ r ≠ 0)
    (j : PUnit ⊕ (M ⊕ Sym2 M)) (i : PUnit ⊕ (Fin m ⊕ Sym2 (Fin m))) :
    quadraticNewReference q r i j =
      ∑ c, quadraticMatrix (fun x => Fin.cons (δ x) (Fin.tail (q x)))
          ((quadraticThreeBlockEquiv m).symm i) c * quadraticOldCoefficients r δ j c := by
  classical
  rcases j with u | (x | p)
  · rcases i with v | (i | p)
    · simp [quadraticNewReference, quadraticOldCoefficients, quadraticCoeffSingle,
        quadraticMatrix, symProd, Pi.single_apply, mul_ite]
      field_simp [hc]
    · simp [quadraticNewReference, quadraticOldCoefficients, quadraticCoeffSingle,
        quadraticMatrix, symProd, Fin.tail, hr, Pi.single_apply, mul_ite,
        (Fin.succ_ne_zero i).symm]
    · induction p using Sym2.ind with
      | _ a b =>
        simp [quadraticNewReference, quadraticOldCoefficients, quadraticCoeffSingle,
          quadraticMatrix, symProd, Fin.tail, hr, Pi.single_apply, mul_ite]
  · rcases i with v | (i | p)
    · simp [quadraticNewReference, quadraticOldCoefficients, quadraticCoeffSingle,
        quadraticMatrix, symProd, Pi.single_apply, mul_ite,
        mul_sub, Finset.sum_sub_distrib]
      field_simp [hc]
      ring
    · simp [quadraticNewReference, quadraticOldCoefficients, quadraticCoeffSingle,
        quadraticMatrix, symProd, Fin.tail, hr, Pi.single_apply, mul_ite,
        mul_sub, Finset.sum_sub_distrib, weightedColumns, (Fin.succ_ne_zero i).symm]
      field_simp [hc]
    · induction p using Sym2.ind with
      | _ a b =>
        simp [quadraticNewReference, quadraticOldCoefficients, quadraticCoeffSingle,
          quadraticMatrix, symProd, Fin.tail, hr, Pi.single_apply, mul_ite,
          mul_sub, Finset.sum_sub_distrib]
  · induction p using Sym2.ind with
    | _ x y =>
      rcases i with v | (i | p)
      · simp [quadraticNewReference, quadraticOldCoefficients, quadraticOldTailCoefficients,
          quadraticCoeffSingle, quadraticMatrix, symProd, Pi.single_apply,
          mul_ite, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
        field_simp [hc]
        simp only [mul_assoc, single_neg_mul_sub]
        ring
      · simp [quadraticNewReference, quadraticOldCoefficients, quadraticOldTailCoefficients,
          quadraticCoeffSingle, quadraticMatrix, symProd, Fin.tail, hr, Pi.single_apply,
          mul_ite, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          (Fin.succ_ne_zero i).symm]
        field_simp [hc]
        simp only [mul_assoc, single_neg_mul_sub]
        ring
      · induction p using Sym2.ind with
        | _ a b =>
          simp [quadraticNewReference, quadraticOldCoefficients, quadraticOldTailCoefficients,
            quadraticCoeffSingle, quadraticMatrix, symProd, Fin.tail, hr, Pi.single_apply,
            mul_ite, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem updated_minorVal_le_quadraticNewReference {F : Type*} [Field F]
    {m : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (m + 1) → HahnSeries ℝ F) (r : M) (δ : M → HahnSeries ℝ F)
    (hr : q r = Pi.single 0 1)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ)) :
    minorVal (quadraticMatrix (fun x => Fin.cons (δ x) (Fin.tail (q x)))) ≤
      minorVal (quadraticNewReference q r) := by
  classical
  have hc : δ r ≠ 0 := HahnSeries.orderTop_ne_top.mp
    (ne_of_eq_of_ne (hδ r) WithTop.coe_ne_top)
  calc
    _ = minorVal ((quadraticMatrix (fun x => Fin.cons (δ x) (Fin.tail (q x)))).submatrix
        (quadraticThreeBlockEquiv m).symm id) :=
      (minorVal_row_equiv _ (quadraticThreeBlockEquiv m).symm).symm
    _ ≤ _ := minorVal_mono_of_column_combinations _ _ (by
      intro j
      exact ⟨quadraticOldCoefficients r δ j, quadraticOldCoefficients_nonneg r δ hδ j,
        fun i => quadraticOldColumn_expansion q r δ hr hc j i⟩)

theorem quadratic_new_potential_eq_reference {F : Type*} [Field F]
    {m : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (m + 1) → HahnSeries ℝ F) (r : M) (δ : M → HahnSeries ℝ F)
    (hr : q r = Pi.single 0 1)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ)) :
    minorVal (quadraticMatrix (fun x => Fin.cons (δ x) (Fin.tail (q x)))) =
      minorVal (quadraticNewReference q r) := by
  exact le_antisymm (updated_minorVal_le_quadraticNewReference q r δ hr hδ)
    (quadraticNewReference_le_updated_minorVal q r δ hδ)

end KServerConj
end PaperFile021

section PaperFile022
open scoped BigOperators

namespace DetValuationMilestone

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
end PaperFile022

section PaperFile023
open scoped BigOperators

namespace KServerAlgebra

theorem det_updateRow_eq_sum_updateCol
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (j : ι) (δ : ι → R) :
    (M.updateRow j δ).det =
      ∑ i, δ i * (M.updateCol i (Pi.single j 1)).det := by
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.adjugate_apply,
    Matrix.updateRow_transpose, Matrix.det_transpose]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem updateCol_column_family
    {ι M R : Type*} [DecidableEq ι]
    (q : M → ι → R) (X : ι → M) (i : ι) (r : M) :
    (Matrix.of fun a b => q (X b) a).updateCol i (q r) =
      Matrix.of (fun a b => q (Function.update X i r b) a) := by
  ext a b
  by_cases h : b = i <;> simp [Matrix.updateCol, Function.update, h]

theorem det_updateRow_column_family
    {ι M R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (q : M → ι → R) (X : ι → M) (r : M) (j : ι) (δ : ι → R)
    (hr : q r = Pi.single j 1) :
    ((Matrix.of fun a b => q (X b) a).updateRow j δ).det =
      ∑ i, δ i * (Matrix.of fun a b => q (Function.update X i r b) a).det := by
  simpa only [← hr, updateCol_column_family] using
    det_updateRow_eq_sum_updateCol (Matrix.of fun a b => q (X b) a) j δ

theorem rowReplace_column_matrix
    {n : ℕ} {M R : Type*}
    (q : M → Fin (n + 1) → R) (δ : M → R) (X : Fin (n + 1) → M) :
    (Matrix.of fun a b => Fin.cons (δ (X b)) (Fin.tail (q (X b))) a) =
      (Matrix.of fun a b => q (X b) a).updateRow 0 (fun b => δ (X b)) := by
  ext a b
  cases a using Fin.cases <;> simp [Matrix.updateRow, Function.update, Fin.tail]

theorem det_rowReplace_column_family
    {n : ℕ} {M R : Type*} [CommRing R]
    (q : M → Fin (n + 1) → R) (δ : M → R) (X : Fin (n + 1) → M)
    (r : M) (hr : q r = Pi.single 0 1) :
    (Matrix.of fun a b => Fin.cons (δ (X b)) (Fin.tail (q (X b))) a).det =
      ∑ i, δ (X i) * (Matrix.of fun a b => q (Function.update X i r b) a).det := by
  rw [rowReplace_column_matrix]
  exact det_updateRow_column_family q X r 0 (fun i => δ (X i)) hr

theorem mulVec_column_matrix
    {ι M R : Type*} [Fintype ι] [CommRing R]
    (B : Matrix ι ι R) (q : M → ι → R) (X : ι → M) :
    (Matrix.of fun a b => B.mulVec (q (X b)) a) =
      B * (Matrix.of fun a b => q (X b) a) := by
  rfl

theorem det_normalized_column_family
    {ι M R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (B : Matrix ι ι R) (hB : B.det = 1) (q : M → ι → R) (X : ι → M) :
    (Matrix.of fun a b => B.mulVec (q (X b)) a).det =
      (Matrix.of fun a b => q (X b) a).det := by
  rw [mulVec_column_matrix, Matrix.det_mul, hB, one_mul]

end KServerAlgebra
end PaperFile023

section PaperFile024
open scoped BigOperators

namespace DetValuationMilestone

theorem exists_finite_inf_minimizer
    {X : Type*} [Fintype X] (f : X → WithTop ℝ) (μ : ℝ)
    (h : (Finset.univ.inf f) = (μ : WithTop ℝ)) :
    ∃ x, f x = (μ : WithTop ℝ) := by
  classical
  obtain ⟨i, _, hi⟩ := (Finset.inf_le_iff (show (μ : WithTop ℝ) < ⊤ by simp)).mp h.le
  exact ⟨i, le_antisymm hi (h.symm.trans_le (Finset.inf_le (Finset.mem_univ i)))⟩

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

theorem submatrix_fromBlocks_sum_map
    {I₁ I₂ J₁ J₂ R : Type*} [Zero R]
    (G₁ : Matrix I₁ J₁ R) (G₂ : Matrix I₂ J₂ R)
    (x₁ : I₁ → J₁) (x₂ : I₂ → J₂) :
    (Matrix.fromBlocks G₁ 0 0 G₂).submatrix id (Sum.map x₁ x₂) =
      Matrix.fromBlocks (G₁.submatrix id x₁) 0 0 (G₂.submatrix id x₂) := by
  ext i j
  cases i <;> cases j <;> rfl

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
end PaperFile024

section PaperFile025
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
end PaperFile025

section PaperFile026
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
end PaperFile026

open KServerConj

theorem solution {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M] {m : ℕ}
    (hm : 1 ≤ m) (q : M → Fin (m + 1) → K (m + 1) M) (r : M)
    (hr : q r = Pi.single 0 1) (δ : M → K (m + 1) M)
    (hδ : ∀ x, nu (δ x) = ((dist r x : ℝ) : WithTop ℝ)) :
    Psi (rowReplace q δ) = minorVal (Qhat q) + minorVal (Hhat q r) := by
  change minorVal (quadraticMatrix (fun x => Fin.cons (δ x) (Fin.tail (q x)))) =
    minorVal (quadraticMatrix (fun x => Fin.tail (q x))) +
      minorVal ((weightedColumns q r).submatrix Fin.succ id)
  rw [quadratic_new_potential_eq_reference.{_, _, 0} q r δ hr hδ]
  simp only [quadraticNewReference, minorVal_fromBlocks, minorVal_one_punit, zero_add, add_comm]

#print axioms solution
