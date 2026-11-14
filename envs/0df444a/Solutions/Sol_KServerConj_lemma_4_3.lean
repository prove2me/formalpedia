-- Prove2me | solution 1 for KServerConj.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T03:38:06.806002+00:00
-- url     : https://prove2.me/submissions/bcd9d2be-fa9d-4319-b8db-c781fb382aad

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Definitions.Def_KServerConj_extCost
import Definitions.Def_KServerConj_colDet
import Definitions.Def_KServerConj_minorVal
import Definitions.Def_KServerConj_Hmat
import Definitions.Def_KServerConj_Psi
import Definitions.Def_KServerConj_rowReplace
import Theorems.Thm_KServerConj_eq_2
set_option autoImplicit false

section PaperFile004
open scoped BigOperators

theorem paper43_det_mul_det_updateCol
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

def paper43_prependColumn {n : ℕ} {R : Type*} (v : Fin (n + 1) → R)
    (W : Matrix (Fin (n + 1)) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun r j => Fin.cases (v r) (fun j => W r j) j

theorem paper43_updateCol_prepend {n : ℕ} {R : Type*}
    (v w : Fin (n + 1) → R) (W : Matrix (Fin (n + 1)) (Fin n) R) :
    (paper43_prependColumn v W).updateCol 0 w = paper43_prependColumn w W := by
  ext r j
  cases j using Fin.cases <;> simp [paper43_prependColumn, Matrix.updateCol]

theorem paper43_det_prepend_single {n : ℕ} {R : Type*} [CommRing R]
    (W : Matrix (Fin (n + 1)) (Fin n) R) :
    (paper43_prependColumn (Pi.single 0 1) W).det = (W.submatrix Fin.succ id).det := by
  rw [Matrix.det_succ_column_zero]
  simp [paper43_prependColumn, Matrix.submatrix, Pi.single_apply, mul_ite, ite_mul]

theorem paper43_det_mul_det_prepend {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (v : Fin (n + 1) → R) (W : Matrix (Fin (n + 1)) (Fin n) R) :
    A.det * (paper43_prependColumn v W).det =
      ∑ i, (A.updateCol i v).det * (paper43_prependColumn (fun r => A r i) W).det := by
  simpa only [paper43_updateCol_prepend] using paper43_det_mul_det_updateCol A (paper43_prependColumn v W) 0 v

theorem paper43_det_prepend_smul {n : ℕ} {R : Type*} [CommRing R]
    (c : R) (v : Fin (n + 1) → R) (W : Matrix (Fin (n + 1)) (Fin n) R) :
    (paper43_prependColumn (c • v) W).det = c * (paper43_prependColumn v W).det := by
  simpa only [paper43_updateCol_prepend] using Matrix.det_updateCol_smul (paper43_prependColumn v W) 0 c v

theorem paper43_prepend_submatrix {n : ℕ} {R ι : Type*}
    (H : Matrix (Fin (n + 1)) ι R) (x : ι) (y : Fin n → ι) :
    paper43_prependColumn (fun r => H r x) (H.submatrix id y) =
      H.submatrix id (Fin.cases x y) := by
  ext r j
  cases j using Fin.cases <;> rfl

theorem paper43_projected_minor_identity {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (y : Fin n → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i))) :
    A.det * (H.submatrix Fin.succ y).det =
      ∑ i, (A.updateCol i (Pi.single 0 1)).det * c i *
        (paper43_prependColumn (fun r => H r (x i)) (H.submatrix id y)).det := by
  simpa only [paper43_det_prepend_single, Matrix.submatrix_submatrix, Function.comp_id,
    Function.id_comp, hcol, paper43_det_prepend_smul, mul_assoc] using
      paper43_det_mul_det_prepend A (Pi.single 0 1) (H.submatrix id y)

theorem paper43_exists_nonzero_projected_minor {n : ℕ} {R ι : Type*} [CommRing R]
    (H : Matrix (Fin (n + 1)) ι R) (x : Fin (n + 1) → ι)
    (hdet : (H.submatrix id x).det ≠ 0) :
    ∃ y : Fin n → ι, (H.submatrix Fin.succ y).det ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hdet
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  simp only [Matrix.submatrix_submatrix, Function.id_comp, h, mul_zero]

theorem paper43_nonzero_unscaled_minor {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i)))
    (hdet : A.det ≠ 0) : (H.submatrix id x).det ≠ 0 := by
  have hA : A = Matrix.of (fun r i => c i * (H.submatrix id x) r i) :=
    funext fun r => funext fun i => congrFun (hcol i) r
  rw [hA, Matrix.det_mul_row c (H.submatrix id x)] at hdet
  exact right_ne_zero_of_mul hdet

theorem paper43_det_eq_sum_scaled_cramer {n : ℕ} {R ι : Type*} [CommRing R]
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

theorem paper43_exists_nonzero_scaled_cramer {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i)))
    (hdet : A.det ≠ 0) :
    ∃ i, (A.updateCol i (Pi.single 0 1)).det * c i ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hdet (by
    simpa only [h, zero_mul, Finset.sum_const_zero] using paper43_det_eq_sum_scaled_cramer A H x c hcol)

end DetValuationMilestone
end PaperFile005

section PaperFile006
open scoped BigOperators

namespace DetValuationMilestone

theorem paper43_valuation_sum_lower_bound
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

theorem paper43_valuation_lower_bound_of_minor_identity
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
    apply paper43_valuation_sum_lower_bound ν hzero hadd
    intro i _
    simpa only [WithTop.coe_add, hmul] using add_le_add (ha i) (hM i)
  rw [← hid, hmul, hD] at hsum
  apply WithTop.le_of_add_le_add_left (x := (δ : WithTop ℝ)) (by simp)
  simpa only [← WithTop.coe_add,
    show δ + (α + μ - δ) = α + μ by linarith] using hsum

theorem paper43_minValue_growth_of_minor_identities
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
  have h := paper43_valuation_lower_bound_of_minor_identity ν hzero hmul hadd
    D (P y) a (fun i => M i y) δ α μ hD (hid y) ha (fun i => hM i y)
  rw [hy, WithTop.coe_le_coe] at h
  linarith

theorem paper43_exists_real_minimum_of_nonzero
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

theorem paper43_canonical_minValue_growth
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
  obtain ⟨α, hα, ha, _⟩ := paper43_exists_real_minimum_of_nonzero ν htop a ha_nonzero
  obtain ⟨μ, hμ, hF, _⟩ := paper43_exists_real_minimum_of_nonzero ν htop F hF_nonzero
  obtain ⟨μhat, hμhat, _, y, hy, _⟩ :=
    paper43_exists_real_minimum_of_nonzero ν htop P hP_nonzero
  exact ⟨δ, α, μ, μhat, hδ.symm, hα, hμ, hμhat,
    paper43_minValue_growth_of_minor_identities ν ((htop 0).mpr rfl) hmul hadd
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

theorem paper43_canonical_projected_minValue_growth
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
  exact paper43_canonical_minValue_growth ν htop hmul hadd A.det
    (fun i => (A.updateCol i (Pi.single 0 1)).det * c i)
    (fun y : Fin n → ι => (H.submatrix Fin.succ y).det)
    (fun z : Fin (n + 1) → ι => (H.submatrix id z).det)
    (fun i y => (paper43_prependColumn (fun r => H r (x i)) (H.submatrix id y)).det)
    hdet (paper43_exists_nonzero_scaled_cramer A H x c hcol hdet)
    (paper43_exists_nonzero_projected_minor H x (paper43_nonzero_unscaled_minor A H x c hcol hdet))
    ⟨x, paper43_nonzero_unscaled_minor A H x c hcol hdet⟩
    (fun y => paper43_projected_minor_identity A H x y c hcol)
    (fun i y => Or.inr ⟨Fin.cases (x i) y,
      congrArg Matrix.det (paper43_prepend_submatrix H (x i) y)⟩)

end DetValuationMilestone
end PaperFile007

section PaperFile008
open scoped BigOperators

namespace DetValuationMilestone

noncomputable def paper43_tupleMinorVal
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (G : Matrix I J R) : WithTop ℝ := by
  classical
  exact Finset.univ.inf fun e : I → J => ν (G.submatrix id e).det

noncomputable def paper43_embeddingMinorVal
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (G : Matrix I J R) : WithTop ℝ := by
  classical
  exact Finset.univ.inf fun e : I ↪ J => ν (G.submatrix id e).det

theorem paper43_det_submatrix_eq_zero_of_not_injective
    {I J R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (G : Matrix I J R) (x : I → J) (hx : ¬ Function.Injective x) :
    (G.submatrix id x).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hx
  exact Matrix.det_zero_of_column_eq hne (fun r => congrArg (fun j => G r j) hij)

theorem paper43_embeddingMinorVal_le_tuple
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤)
    (G : Matrix I J R) (x : I → J) :
    paper43_embeddingMinorVal ν G ≤ ν (G.submatrix id x).det := by
  classical
  exact (Classical.em (Function.Injective x)).elim
    (fun hx => Finset.inf_le (f := fun e : I ↪ J => ν (G.submatrix id e).det)
      (Finset.mem_univ (⟨x, hx⟩ : I ↪ J)))
    (fun hx => by
      simpa only [paper43_det_submatrix_eq_zero_of_not_injective G x hx, hzero] using
        (le_top : paper43_embeddingMinorVal ν G ≤ ⊤))

theorem paper43_tupleMinorVal_eq_embeddingMinorVal
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (G : Matrix I J R) :
    paper43_tupleMinorVal ν G = paper43_embeddingMinorVal ν G := by
  classical
  exact le_antisymm
    (Finset.le_inf fun e _ => Finset.inf_le
      (f := fun x : I → J => ν (G.submatrix id x).det) (Finset.mem_univ (e : I → J)))
    (Finset.le_inf fun x _ => paper43_embeddingMinorVal_le_tuple ν hzero G x)

theorem paper43_add_finset_inf {ι : Type*} (a : WithTop ℝ) (s : Finset ι)
    (f : ι → WithTop ℝ) :
    a + s.inf f = s.inf (fun i => a + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.inf_insert, ← ih, min_add_add_left]

theorem paper43_tupleMinorVal_mul
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (A : Matrix I I R) (G : Matrix I J R) :
    paper43_tupleMinorVal ν (A * G) = ν A.det + paper43_tupleMinorVal ν G := by
  have hval : ∀ x : I → J, ν ((A * G).submatrix id x).det =
      ν A.det + ν (G.submatrix id x).det := fun x =>
    (congrArg ν (Matrix.det_mul A (G.submatrix id x))).trans (hmul _ _)
  simpa only [paper43_tupleMinorVal, hval] using
    (paper43_add_finset_inf (ν A.det) (Finset.univ : Finset (I → J))
      (fun x => ν (G.submatrix id x).det)).symm

theorem paper43_embeddingMinorVal_mul
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (A : Matrix I I R) (G : Matrix I J R) :
    paper43_embeddingMinorVal ν (A * G) = ν A.det + paper43_embeddingMinorVal ν G := by
  simpa only [paper43_tupleMinorVal_eq_embeddingMinorVal ν hzero] using paper43_tupleMinorVal_mul ν hmul A G

end DetValuationMilestone
end PaperFile008

section PaperFile009
namespace KServerConj

theorem paper43_minorVal_eq_embeddingMinorVal
    {F I J : Type*} [Field F] [Fintype I] [hI : DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) :
    minorVal G = DetValuationMilestone.paper43_embeddingMinorVal (HahnSeries.addVal ℝ F) G := by
  classical
  cases Subsingleton.elim hI (Classical.decEq I)
  unfold minorVal DetValuationMilestone.paper43_embeddingMinorVal
  rfl

theorem paper43_minorVal_mul
    {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I I (HahnSeries ℝ F)) (G : Matrix I J (HahnSeries ℝ F)) :
    minorVal (A * G) = HahnSeries.addVal ℝ F A.det + minorVal G := by
  simpa only [paper43_minorVal_eq_embeddingMinorVal] using
    DetValuationMilestone.paper43_embeddingMinorVal_mul (HahnSeries.addVal ℝ F)
      (AddValuation.map_zero _) (fun x y => AddValuation.map_mul _ x y) A G

end KServerConj
end PaperFile009

section PaperFile010
open scoped BigOperators

namespace KServerConj

noncomputable def paper43_quadraticMatrix {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F) :
    Matrix (Sym2 (Fin k)) (Sym2 M) (HahnSeries ℝ F) :=
  fun p c => Sym2.lift ⟨fun x y =>
    HahnSeries.single (-dist x y) (1 : F) * symProd (q x) (q y) p,
    fun x y => by
      dsimp only
      rw [dist_comm, symProd_comm]⟩ c

theorem paper43_Qmat_eq_quadraticMatrix {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → K k M) : Qmat q = paper43_quadraticMatrix q := rfl

noncomputable def paper43_weightedColumns {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F) (r : M) :
    Matrix (Fin k) M (HahnSeries ℝ F) :=
  fun i x => HahnSeries.single (-dist r x) (1 : F) * q x i

noncomputable def paper43_negPairDist {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (x : Fin k → M) : Sym2 (Fin k) → ℝ :=
  Sym2.lift ⟨fun i j => -dist (x i) (x j),
    fun i j => congrArg Neg.neg (dist_comm (x i) (x j))⟩

theorem paper43_quadraticMatrix_submatrix {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) :
    (paper43_quadraticMatrix q).submatrix id (Sym2.map x) =
      Matrix.of (fun r c => HahnSeries.single (paper43_negPairDist x c) (1 : F) *
        sym2Mat (Matrix.of (fun i j => q (x j) i)) r c) := by
  funext r c
  induction c using Sym2.ind with
  | _ i j => rfl

end KServerConj
end PaperFile010

section PaperFile013
namespace KServerConj

variable {k : ℕ} {M : Type*}

@[simp] theorem paper43_nu_zero : nu (0 : K k M) = ⊤ := by
  exact AddValuation.map_zero _

@[simp] theorem paper43_nu_one : nu (1 : K k M) = 0 := by
  exact AddValuation.map_one _

@[simp] theorem paper43_nu_eq_top_iff (f : K k M) : nu f = ⊤ ↔ f = 0 := by
  exact HahnSeries.orderTop_eq_top

theorem paper43_nu_mul (f g : K k M) : nu (f * g) = nu f + nu g := by
  exact AddValuation.map_mul _ f g

theorem paper43_nu_add (f g : K k M) : min (nu f) (nu g) ≤ nu (f + g) := by
  exact AddValuation.map_add _ f g

@[simp] theorem paper43_nu_zp (a : ℝ) : nu (zp a : K k M) = (a : WithTop ℝ) := by
  exact HahnSeries.orderTop_single one_ne_zero

theorem paper43_varF_ne_zero (v : Var k M) : varF v ≠ 0 := by
  exact (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Var k M) ℚ) (F k M))).mpr
    (MvPolynomial.X_ne_zero v)

@[simp] theorem paper43_nu_coef (v : Var k M) : nu (coef v) = 0 := by
  simpa only [nu, HahnSeries.addVal_apply, coef, HahnSeries.C_apply, WithTop.coe_zero] using
    (HahnSeries.orderTop_single (a := (0 : ℝ)) (paper43_varF_ne_zero v))

theorem paper43_nu_C {c : F k M} (hc : c ≠ 0) : nu (HahnSeries.C c : K k M) = 0 := by
  simpa only [nu, HahnSeries.addVal_apply, HahnSeries.C_apply, WithTop.coe_zero] using
    (HahnSeries.orderTop_single (a := (0 : ℝ)) hc)

theorem paper43_coef_ne_zero (v : Var k M) : coef v ≠ 0 := by
  exact HahnSeries.single_ne_zero (paper43_varF_ne_zero v)

theorem paper43_zp_ne_zero (a : ℝ) : (zp a : K k M) ≠ 0 := by
  exact HahnSeries.single_ne_zero one_ne_zero

@[simp] theorem paper43_zp_zero : (zp 0 : K k M) = 1 := by
  exact HahnSeries.single_zero_one

theorem paper43_zp_add (a b : ℝ) : (zp (a + b) : K k M) = zp a * zp b := by
  simpa only [one_mul] using
    (HahnSeries.single_mul_single (a := a) (b := b) (r := (1 : F k M)) (s := 1)).symm

@[simp] theorem paper43_nu_neg (f : K k M) : nu (-f) = nu f := by
  exact AddValuation.map_neg _ _

@[simp] theorem paper43_nu_inv (f : K k M) : nu f⁻¹ = -(nu f) := by
  exact AddValuation.map_inv _

theorem paper43_nu_sum_ge {ι : Type*} [Fintype ι] (f : ι → K k M) (b : WithTop ℝ)
    (hf : ∀ i, b ≤ nu (f i)) : b ≤ nu (∑ i, f i) := by
  exact AddValuation.map_le_sum _ (fun i _ => hf i)

theorem paper43_nu_fresh_term (v : Var k M) (a : ℝ) (f : K k M) :
    nu (coef v * zp a * f) = (a : WithTop ℝ) + nu f := by
  simp only [paper43_nu_mul, paper43_nu_coef, paper43_nu_zp, zero_add]

theorem paper43_zp_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (zp (∑ i ∈ s, a i) : K k M) = ∏ i ∈ s, zp (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, paper43_zp_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, paper43_zp_add, ih]

end KServerConj
end PaperFile013

section PaperFile014
open scoped BigOperators

namespace KServerConj

variable {k : ℕ} {M : Type*}

theorem paper43_varF_algebraicIndependent : AlgebraicIndependent ℚ (@varF k M) := by
  exact (MvPolynomial.algebraicIndependent_X (Var k M) ℚ).map'
    (f := IsScalarTower.toAlgHom ℚ (MvPolynomial (Var k M) ℚ) (F k M))
    (IsFractionRing.injective (MvPolynomial (Var k M) ℚ) (F k M))

theorem paper43_varF_algebraicIndependent_over_complement (S : Set (Var k M)) :
    AlgebraicIndependent (IntermediateField.adjoin ℚ ((@varF k M) '' Sᶜ))
      (fun i : S => varF (i : Var k M)) := by
  exact IntermediateField.algebraicIndependent_adjoin_iff.mpr
    ((AlgebraicIndependent.iff_adjoin_image_compl S).mp paper43_varF_algebraicIndependent).2

theorem paper43_fresh_vars_linearIndependent {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) :
    LinearIndependent
      (IntermediateField.adjoin ℚ ((@varF k M) '' (Set.range v)ᶜ))
      (fun i => varF (v i)) := by
  exact (paper43_varF_algebraicIndependent_over_complement (Set.range v)).linearIndependent.comp
    (fun i => ⟨v i, Set.mem_range_self i⟩)
    (fun _ _ h => hv (congrArg Subtype.val h))

theorem paper43_complement_closure_le_adjoin (S : Set (Var k M)) :
    Subfield.closure ((@varF k M) '' Sᶜ) ≤
      (IntermediateField.adjoin ℚ ((@varF k M) '' Sᶜ)).toSubfield := by
  exact Subfield.closure_le.mpr (IntermediateField.subset_adjoin ℚ _)

theorem paper43_fresh_vars_sum_ne_zero {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) (b : Fin N → F k M)
    (hb : ∀ i, b i ∈ Subfield.closure ((@varF k M) '' (Set.range v)ᶜ))
    (hne : ∃ i, b i ≠ 0) :
    ∑ i, varF (v i) * b i ≠ 0 := by
  intro hz
  let c : Fin N → IntermediateField.adjoin ℚ ((@varF k M) '' (Set.range v)ᶜ) :=
    fun i => ⟨b i, paper43_complement_closure_le_adjoin (Set.range v) (hb i)⟩
  have hsum : ∑ i, c i • varF (v i) = 0 := by
    simpa only [c, IntermediateField.smul_def, Subtype.coe_mk, smul_eq_mul, mul_comm] using hz
  have hczero := Fintype.linearIndependent_iff.mp (paper43_fresh_vars_linearIndependent v hv) c hsum
  exact hne.elim (fun i hi => hi (congrArg Subtype.val (hczero i)))

end KServerConj
end PaperFile014

section PaperFile015
open scoped BigOperators

namespace KServerConj

variable {k : ℕ} {M : Type*}

theorem paper43_coeff_fresh_term (v : Var k M) (a b : ℝ) (f : K k M) :
    (coef v * zp a * f).coeff b = varF v * f.coeff (b - a) := by
  simp only [mul_assoc, coef, HahnSeries.C_apply, zp, HahnSeries.coeff_single_mul,
    one_mul, sub_zero]

theorem paper43_fresh_sum_coeff_ne_zero {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) (f : Fin N → K k M)
    (hf : ∀ i, FreeOf (Set.range v) (f i)) (a : Fin N → ℝ) (b : ℝ)
    (hne : ∃ i, (f i).coeff (b - a i) ≠ 0) :
    (∑ i, coef (v i) * zp (a i) * f i).coeff b ≠ 0 := by
  simpa only [HahnSeries.coeff_sum, paper43_coeff_fresh_term] using
    paper43_fresh_vars_sum_ne_zero v hv (fun i => (f i).coeff (b - a i))
      (fun i => hf i (b - a i)) hne

theorem paper43_nu_fresh_sum_le_of_ne {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) (f : Fin N → K k M)
    (hf : ∀ i, FreeOf (Set.range v) (f i)) (a : Fin N → ℝ)
    (j : Fin N) (hj : f j ≠ 0) :
    nu (∑ i, coef (v i) * zp (a i) * f i) ≤ (a j : WithTop ℝ) + nu (f j) := by
  have hcoeff := paper43_fresh_sum_coeff_ne_zero v hv f hf a (a j + (f j).order)
    ⟨j, by simpa only [add_sub_cancel_left] using (HahnSeries.coeff_order_eq_zero.not.mpr hj)⟩
  simpa only [nu, HahnSeries.addVal_apply_of_ne hj, ← WithTop.coe_add] using
    (HahnSeries.addVal_le_of_coeff_ne_zero hcoeff)

theorem paper43_fresh_coefficients_no_cancellation {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) (f : Fin N → K k M)
    (hf : ∀ i, FreeOf (Set.range v) (f i)) (a : Fin N → ℝ) :
    nu (∑ i, coef (v i) * zp (a i) * f i) =
      Finset.univ.inf (fun i => (a i : WithTop ℝ) + nu (f i)) := by
  apply le_antisymm
  · refine Finset.le_inf ?_
    intro j _
    exact (eq_or_ne (f j) 0).elim
      (fun hj => by simp only [hj, paper43_nu_zero, WithTop.add_top, le_top])
      (paper43_nu_fresh_sum_le_of_ne v hv f hf a j)
  · exact paper43_nu_sum_ge _ _ (fun i => by
      simpa only [paper43_nu_fresh_term] using
        (Finset.inf_le (f := fun i => (a i : WithTop ℝ) + nu (f i)) (Finset.mem_univ i)))

end KServerConj
end PaperFile015

section PaperFile016
namespace KServerConj

noncomputable def paper43_hahnCoeffMap {F E : Type*} [Field F] [Field E] (g : F →+* E) :
    HahnSeries ℝ F →+* HahnSeries ℝ E where
  toFun f := f.map g
  map_zero' := HahnSeries.map_zero g.toZeroHom
  map_one' := by
    simpa only [map_one] using (HahnSeries.map_C (Γ := ℝ) (1 : F) g)
  map_add' _ _ := HahnSeries.map_add g.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul g.toNonUnitalRingHom

@[simp] theorem paper43_hahnCoeffMap_coeff {F E : Type*} [Field F] [Field E]
    (g : F →+* E) (f : HahnSeries ℝ F) (a : ℝ) :
    (paper43_hahnCoeffMap g f).coeff a = g (f.coeff a) := rfl

noncomputable def paper43_restrictCoeffs {F : Type*} [Field F] (S : Subfield F) (f : HahnSeries ℝ F)
    (hf : ∀ a, f.coeff a ∈ S) : HahnSeries ℝ S where
  coeff a := ⟨f.coeff a, hf a⟩
  isPWO_support' := f.isPWO_support.mono fun _ ha hz => ha (Subtype.ext hz)

@[simp] theorem paper43_restrictCoeffs_map {F : Type*} [Field F] (S : Subfield F)
    (f : HahnSeries ℝ F) (hf : ∀ a, f.coeff a ∈ S) :
    paper43_hahnCoeffMap S.subtype (paper43_restrictCoeffs S f hf) = f := by
  exact HahnSeries.coeff_injective rfl

theorem paper43_coeff_inv_mem_subfield {F : Type*} [Field F] (S : Subfield F)
    (f : HahnSeries ℝ F) (hf : ∀ a, f.coeff a ∈ S) :
    ∀ a, (f⁻¹).coeff a ∈ S := by
  have hmap : paper43_hahnCoeffMap S.subtype (paper43_restrictCoeffs S f hf)⁻¹ = f⁻¹ := by
    rw [map_inv₀, paper43_restrictCoeffs_map]
  exact fun a => (congrArg (fun g : HahnSeries ℝ F => g.coeff a) hmap) ▸
    (((paper43_restrictCoeffs S f hf)⁻¹).coeff a).property

end KServerConj
end PaperFile016

section PaperFile017
namespace KServerConj

variable {k : ℕ} {M : Type*}

theorem paper43_freeOf_zero (S : Set (Var k M)) : FreeOf S (0 : K k M) := by
  exact fun _ => Subfield.zero_mem _

theorem paper43_freeOf_single (S : Set (Var k M)) (a : ℝ) (c : F k M)
    (hc : c ∈ Subfield.closure ((fun v => varF v) '' Sᶜ)) :
    FreeOf S (HahnSeries.single a c) := by
  intro b
  rw [HahnSeries.coeff_single]
  exact ite_mem.mpr ⟨fun _ => hc, fun _ => Subfield.zero_mem _⟩

theorem paper43_freeOf_zp (S : Set (Var k M)) (a : ℝ) : FreeOf S (zp a : K k M) := by
  exact paper43_freeOf_single S a 1 (Subfield.one_mem _)

theorem paper43_freeOf_one (S : Set (Var k M)) : FreeOf S (1 : K k M) := by
  exact paper43_freeOf_single S 0 1 (Subfield.one_mem _)

theorem paper43_freeOf_coef (S : Set (Var k M)) (v : Var k M) (hv : v ∉ S) :
    FreeOf S (coef v) := by
  exact paper43_freeOf_single S 0 (varF v) (Subfield.subset_closure ⟨v, hv, rfl⟩)

theorem paper43_freeOf_add {S : Set (Var k M)} {f g : K k M} (hf : FreeOf S f) (hg : FreeOf S g) :
    FreeOf S (f + g) := by
  simpa only [FreeOf, HahnSeries.coeff_add] using
    fun a => Subfield.add_mem _ (hf a) (hg a)

theorem paper43_freeOf_neg {S : Set (Var k M)} {f : K k M} (hf : FreeOf S f) :
    FreeOf S (-f) := by
  simpa only [FreeOf, HahnSeries.coeff_neg] using
    fun a => Subfield.neg_mem _ (hf a)

theorem paper43_freeOf_mul {S : Set (Var k M)} {f g : K k M} (hf : FreeOf S f) (hg : FreeOf S g) :
    FreeOf S (f * g) := by
  intro a
  rw [HahnSeries.coeff_mul]
  exact Subfield.sum_mem _ fun ij _ => Subfield.mul_mem _ (hf ij.1) (hg ij.2)

theorem paper43_freeOf_inv {S : Set (Var k M)} {f : K k M} (hf : FreeOf S f) :
    FreeOf S f⁻¹ := by
  exact paper43_coeff_inv_mem_subfield _ f hf

noncomputable def paper43_freeOfSubfield (S : Set (Var k M)) : Subfield (K k M) where
  carrier := FreeOf S
  zero_mem' := paper43_freeOf_zero S
  one_mem' := paper43_freeOf_one S
  add_mem' := paper43_freeOf_add
  mul_mem' := paper43_freeOf_mul
  neg_mem' := paper43_freeOf_neg
  inv_mem' := fun _ hf => paper43_freeOf_inv hf

theorem paper43_freeOf_div {S : Set (Var k M)} {f g : K k M} (hf : FreeOf S f) (hg : FreeOf S g) :
    FreeOf S (f / g) := by
  exact (paper43_freeOfSubfield S).div_mem hf hg

theorem paper43_freeOf_sum {S : Set (Var k M)} {ι : Type*} (s : Finset ι) (f : ι → K k M)
    (hf : ∀ i ∈ s, FreeOf S (f i)) : FreeOf S (∑ i ∈ s, f i) := by
  exact (paper43_freeOfSubfield S).sum_mem hf

theorem paper43_freeOf_prod {S : Set (Var k M)} {ι : Type*} (s : Finset ι) (f : ι → K k M)
    (hf : ∀ i ∈ s, FreeOf S (f i)) : FreeOf S (∏ i ∈ s, f i) := by
  exact (paper43_freeOfSubfield S).prod_mem hf

theorem paper43_freeOf_mono {S T : Set (Var k M)} {f : K k M} (hST : S ⊆ T)
    (hf : FreeOf T f) : FreeOf S f := by
  exact fun a => Subfield.closure_mono (Set.image_mono (Set.compl_subset_compl.mpr hST)) (hf a)

end KServerConj
end PaperFile017

section PaperFile018
namespace KServerConj

theorem paper43_colDet_eq_zero_of_not_injective {k : ℕ} {M : Type*}
    (q : M → Fin k → K k M) (x : Fin k → M) (hx : ¬ Function.Injective x) :
    colDet q x = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hx
  exact Matrix.det_zero_of_column_eq hne (fun a => congrArg (fun y => q y a) hij)

theorem paper43_update_injective_of_not_mem_range {ι M : Type*} [DecidableEq ι]
    (x : ι → M) (hx : Function.Injective x) (r : M) (hr : r ∉ Set.range x) (i : ι) :
    Function.Injective (Function.update x i r) := by
  intro a b hab
  by_cases ha : a = i
  · have hb : b = i := Classical.byContradiction fun hb => hr
      ⟨b, by simpa only [Function.update_apply, ha, hb, if_true, if_false] using hab.symm⟩
    exact ha.trans hb.symm
  · have hb : b ≠ i := fun hb => hr
      ⟨a, by simpa only [Function.update_apply, ha, hb, if_true, if_false] using hab⟩
    exact hx (by simpa only [Function.update_apply, ha, hb, if_false] using hab)

end KServerConj
end PaperFile018

section PaperFile019
open scoped BigOperators

namespace KServerAlgebra

theorem paper43_det_updateRow_eq_sum_updateCol
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (j : ι) (δ : ι → R) :
    (M.updateRow j δ).det =
      ∑ i, δ i * (M.updateCol i (Pi.single j 1)).det := by
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.adjugate_apply,
    Matrix.updateRow_transpose, Matrix.det_transpose]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem paper43_updateCol_column_family
    {ι M R : Type*} [DecidableEq ι]
    (q : M → ι → R) (X : ι → M) (i : ι) (r : M) :
    (Matrix.of fun a b => q (X b) a).updateCol i (q r) =
      Matrix.of (fun a b => q (Function.update X i r b) a) := by
  ext a b
  by_cases h : b = i <;> simp [Matrix.updateCol, Function.update, h]

theorem paper43_det_updateRow_column_family
    {ι M R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (q : M → ι → R) (X : ι → M) (r : M) (j : ι) (δ : ι → R)
    (hr : q r = Pi.single j 1) :
    ((Matrix.of fun a b => q (X b) a).updateRow j δ).det =
      ∑ i, δ i * (Matrix.of fun a b => q (Function.update X i r b) a).det := by
  simpa only [← hr, paper43_updateCol_column_family] using
    paper43_det_updateRow_eq_sum_updateCol (Matrix.of fun a b => q (X b) a) j δ

theorem paper43_rowReplace_column_matrix
    {n : ℕ} {M R : Type*}
    (q : M → Fin (n + 1) → R) (δ : M → R) (X : Fin (n + 1) → M) :
    (Matrix.of fun a b => Fin.cons (δ (X b)) (Fin.tail (q (X b))) a) =
      (Matrix.of fun a b => q (X b) a).updateRow 0 (fun b => δ (X b)) := by
  ext a b
  cases a using Fin.cases <;> simp [Matrix.updateRow, Function.update, Fin.tail]

theorem paper43_det_rowReplace_column_family
    {n : ℕ} {M R : Type*} [CommRing R]
    (q : M → Fin (n + 1) → R) (δ : M → R) (X : Fin (n + 1) → M)
    (r : M) (hr : q r = Pi.single 0 1) :
    (Matrix.of fun a b => Fin.cons (δ (X b)) (Fin.tail (q (X b))) a).det =
      ∑ i, δ (X i) * (Matrix.of fun a b => q (Function.update X i r b) a).det := by
  rw [paper43_rowReplace_column_matrix]
  exact paper43_det_updateRow_column_family q X r 0 (fun i => δ (X i)) hr

theorem paper43_mulVec_column_matrix
    {ι M R : Type*} [Fintype ι] [CommRing R]
    (B : Matrix ι ι R) (q : M → ι → R) (X : ι → M) :
    (Matrix.of fun a b => B.mulVec (q (X b)) a) =
      B * (Matrix.of fun a b => q (X b) a) := by
  rfl

theorem paper43_det_normalized_column_family
    {ι M R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (B : Matrix ι ι R) (hB : B.det = 1) (q : M → ι → R) (X : ι → M) :
    (Matrix.of fun a b => B.mulVec (q (X b)) a).det =
      (Matrix.of fun a b => q (X b) a).det := by
  rw [paper43_mulVec_column_matrix, Matrix.det_mul, hB, one_mul]

end KServerAlgebra
end PaperFile019

section PaperFile020
open scoped BigOperators

namespace KServerConj

theorem paper43_colDet_rowReplace_eq_sum {n : ℕ} {M : Type*}
    (q : M → Fin (n + 1) → K (n + 1) M) (δ : M → K (n + 1) M)
    (x : Fin (n + 1) → M) (r : M) (hr : q r = Pi.single 0 1) :
    colDet (rowReplace q δ) x =
      ∑ i, δ (x i) * colDet q (Function.update x i r) := by
  exact KServerAlgebra.paper43_det_rowReplace_column_family q δ x r hr

theorem paper43_fresh_rowReplace_valuation_eq_inf {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (hr : q r = Pi.single 0 1)
    (hfree : ∀ x : Fin (n + 1) → M,
      FreeOf (Set.range fun y : M => (Sum.inr (t, y) : Var (n + 1) M)) (colDet q x))
    (x : Fin (n + 1) → M) (hx : Function.Injective x) :
    nu (colDet (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) =
      Finset.univ.inf (fun i => (dist r (x i) : WithTop ℝ) +
        nu (colDet q (Function.update x i r))) := by
  have hv : Function.Injective (fun i : Fin (n + 1) => (Sum.inr (t, x i) : Var (n + 1) M)) :=
    fun _ _ h => hx (congrArg (fun p : ℕ × M => p.2) (Sum.inr.inj h))
  have hsubset :
      Set.range (fun i : Fin (n + 1) => (Sum.inr (t, x i) : Var (n + 1) M)) ⊆
        Set.range (fun y : M => (Sum.inr (t, y) : Var (n + 1) M)) :=
    fun _ ⟨i, hi⟩ => ⟨x i, hi⟩
  exact (congrArg nu (paper43_colDet_rowReplace_eq_sum q
    (fun y => coef (Sum.inr (t, y)) * zp (dist r y)) x r hr)).trans
    (paper43_fresh_coefficients_no_cancellation
      (fun i => (Sum.inr (t, x i) : Var (n + 1) M)) hv
      (fun i => colDet q (Function.update x i r))
      (fun i => paper43_freeOf_mono hsubset (hfree (Function.update x i r)))
      (fun i => dist r (x i)))

theorem paper43_exists_injective_update_le {ι M : Type*} [DecidableEq ι] [PseudoMetricSpace M]
    (x : ι → M) (hx : Function.Injective x) (r : M)
    (w : (ι → M) → ℝ) (b : ℝ)
    (hge : ∃ i, w (Function.update x i r) + dist r (x i) ≤ b) (hmono : w x ≤ b) :
    ∃ i, Function.Injective (Function.update x i r) ∧
      w (Function.update x i r) + dist r (x i) ≤ b := by
  by_cases hrange : r ∈ Set.range x
  · exact hrange.elim (fun j hj =>
      let hu : Function.update x j r = x := Function.update_eq_self_iff.mpr hj.symm
      ⟨j, hu.symm ▸ hx, by simpa only [hu, hj, dist_self, add_zero] using hmono⟩)
  · exact hge.elim (fun i hi =>
      ⟨i, paper43_update_injective_of_not_mem_range x hx r hrange i, hi⟩)

theorem paper43_determinant_cost_inf_eq {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M)
    (w : (Fin (n + 1) → M) → ℝ) (b : ℝ)
    (hrep : ∀ y : Fin (n + 1) → M, Function.Injective y →
      nu (colDet q y) = (w y : WithTop ℝ))
    (x : Fin (n + 1) → M) (hx : Function.Injective x)
    (hle : ∀ i, b ≤ w (Function.update x i r) + dist r (x i))
    (hge : ∃ i, w (Function.update x i r) + dist r (x i) ≤ b)
    (hmono : w x ≤ b) :
    Finset.univ.inf (fun i => (dist r (x i) : WithTop ℝ) +
      nu (colDet q (Function.update x i r))) = (b : WithTop ℝ) := by
  apply le_antisymm
  · obtain ⟨i, hi, hcost⟩ := paper43_exists_injective_update_le x hx r w b hge hmono
    exact (Finset.inf_le
      (f := fun i => (dist r (x i) : WithTop ℝ) + nu (colDet q (Function.update x i r)))
      (Finset.mem_univ i)).trans (by
        simpa only [hrep _ hi, ← WithTop.coe_add, add_comm] using
          (WithTop.coe_le_coe.mpr hcost))
  · refine Finset.le_inf ?_
    intro i _
    exact (em (Function.Injective (Function.update x i r))).elim
      (fun hi => by
        simpa only [hrep _ hi, ← WithTop.coe_add, add_comm] using
          (WithTop.coe_le_coe.mpr (hle i)))
      (fun hi => by
        simp only [paper43_colDet_eq_zero_of_not_injective q _ hi, paper43_nu_zero, WithTop.add_top, le_top])

theorem paper43_request_representation_step {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (w w' : (Fin (n + 1) → M) → ℝ) (hr : q r = Pi.single 0 1)
    (hrep : ∀ y : Fin (n + 1) → M, Function.Injective y →
      nu (colDet q y) = (w y : WithTop ℝ))
    (hfree : ∀ y : Fin (n + 1) → M,
      FreeOf (Set.range fun z : M => (Sum.inr (t, z) : Var (n + 1) M)) (colDet q y))
    (hrec_le : ∀ y : Fin (n + 1) → M, Function.Injective y → ∀ i,
      w' y ≤ w (Function.update y i r) + dist r (y i))
    (hrec_ge : ∀ y : Fin (n + 1) → M, Function.Injective y →
      ∃ i, w (Function.update y i r) + dist r (y i) ≤ w' y)
    (hmono : ∀ y : Fin (n + 1) → M, Function.Injective y → w y ≤ w' y)
    (x : Fin (n + 1) → M) (hx : Function.Injective x) :
    nu (colDet (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) =
      (w' x : WithTop ℝ) := by
  exact (paper43_fresh_rowReplace_valuation_eq_inf q r t hr hfree x hx).trans
    (paper43_determinant_cost_inf_eq q r w (w' x) hrep x hx
      (hrec_le x hx) (hrec_ge x hx) (hmono x hx))

theorem paper43_rowReplace_det_freeOf {n : ℕ} {M : Type*} (S : Set (Var (n + 1) M))
    (q : M → Fin (n + 1) → K (n + 1) M) (δ : M → K (n + 1) M)
    (r : M) (hr : q r = Pi.single 0 1)
    (hfree : ∀ y : Fin (n + 1) → M, FreeOf S (colDet q y))
    (hδ : ∀ y : M, FreeOf S (δ y)) (x : Fin (n + 1) → M) :
    FreeOf S (colDet (rowReplace q δ) x) := by
  exact (paper43_colDet_rowReplace_eq_sum q δ x r hr).symm ▸
    paper43_freeOf_sum Finset.univ (fun i => δ (x i) * colDet q (Function.update x i r))
      (fun i _ => paper43_freeOf_mul (hδ (x i)) (hfree (Function.update x i r)))

theorem paper43_fresh_rowReplace_det_freeOf {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (S : Set (Var (n + 1) M)) (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (hr : q r = Pi.single 0 1)
    (hfree : ∀ y : Fin (n + 1) → M, FreeOf S (colDet q y))
    (hS : ∀ y : M, Sum.inr (t, y) ∉ S) (x : Fin (n + 1) → M) :
    FreeOf S (colDet (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) := by
  exact paper43_rowReplace_det_freeOf S q _ r hr hfree
    (fun y => paper43_freeOf_mul (paper43_freeOf_coef S (Sum.inr (t, y)) (hS y)) (paper43_freeOf_zp S (dist r y))) x

theorem paper43_colDet_normalize_eq {k : ℕ} {M : Type*}
    (B : Matrix (Fin k) (Fin k) (K k M)) (hB : B.det = 1)
    (q : M → Fin k → K k M) (x : Fin k → M) :
    colDet (fun y => B.mulVec (q y)) x = colDet q x := by
  exact KServerAlgebra.paper43_det_normalized_column_family B hB q x

theorem paper43_normalized_request_representation_step {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (K (n + 1) M)) (hB : B.det = 1)
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (w w' : (Fin (n + 1) → M) → ℝ) (hr : B.mulVec (q r) = Pi.single 0 1)
    (hrep : ∀ y : Fin (n + 1) → M, Function.Injective y →
      nu (colDet q y) = (w y : WithTop ℝ))
    (hfree : ∀ y : Fin (n + 1) → M,
      FreeOf (Set.range fun z : M => (Sum.inr (t, z) : Var (n + 1) M)) (colDet q y))
    (hrec_le : ∀ y : Fin (n + 1) → M, Function.Injective y → ∀ i,
      w' y ≤ w (Function.update y i r) + dist r (y i))
    (hrec_ge : ∀ y : Fin (n + 1) → M, Function.Injective y →
      ∃ i, w (Function.update y i r) + dist r (y i) ≤ w' y)
    (hmono : ∀ y : Fin (n + 1) → M, Function.Injective y → w y ≤ w' y)
    (x : Fin (n + 1) → M) (hx : Function.Injective x) :
    nu (colDet (rowReplace (fun y => B.mulVec (q y))
      (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) = (w' x : WithTop ℝ) := by
  exact paper43_request_representation_step (fun y => B.mulVec (q y)) r t w w' hr
    (fun y hy => (congrArg nu (paper43_colDet_normalize_eq B hB q y)).trans (hrep y hy))
    (fun y => (paper43_colDet_normalize_eq B hB q y).symm ▸ hfree y)
    hrec_le hrec_ge hmono x hx

theorem paper43_normalized_fresh_rowReplace_det_freeOf {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (S : Set (Var (n + 1) M))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (K (n + 1) M)) (hB : B.det = 1)
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (hr : B.mulVec (q r) = Pi.single 0 1)
    (hfree : ∀ y : Fin (n + 1) → M, FreeOf S (colDet q y))
    (hS : ∀ y : M, Sum.inr (t, y) ∉ S) (x : Fin (n + 1) → M) :
    FreeOf S (colDet (rowReplace (fun y => B.mulVec (q y))
      (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) := by
  exact paper43_fresh_rowReplace_det_freeOf S (fun y => B.mulVec (q y)) r t hr
    (fun y => (paper43_colDet_normalize_eq B hB q y).symm ▸ hfree y) hS x

end KServerConj
end PaperFile020

section PaperFile021
open scoped BigOperators

namespace KServerConj

theorem paper43_weightedColumns_rescale {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F) (r y : M) :
    HahnSeries.single (dist r y) (1 : F) • (fun i => paper43_weightedColumns q r i y) = q y := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, paper43_weightedColumns, ← mul_assoc,
    HahnSeries.single_mul_single, add_neg_cancel, one_mul, HahnSeries.single_zero_one]

theorem paper43_tupleMinorVal_eq_minorVal {F I J : Type*} [Field F]
    [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) :
    DetValuationMilestone.paper43_tupleMinorVal (HahnSeries.addVal ℝ F) G = minorVal G := by
  exact (DetValuationMilestone.paper43_tupleMinorVal_eq_embeddingMinorVal
    (HahnSeries.addVal ℝ F) (AddValuation.map_zero _) G).trans
      (paper43_minorVal_eq_embeddingMinorVal G).symm

theorem paper43_projected_weighted_growth_of_cramer_min
    {F : Type*} [Field F] {n : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M) (x : Fin (n + 1) → M)
    (δ β : ℝ)
    (hδ : HahnSeries.addVal ℝ F (Matrix.of fun i j => q (x j) i).det = (δ : WithTop ℝ))
    (hβ : (Finset.univ.inf fun i => HahnSeries.addVal ℝ F
      (((Matrix.of fun a b => q (x b) a).updateCol i (Pi.single 0 1)).det *
        HahnSeries.single (dist r (x i)) (1 : F))) = (β : WithTop ℝ)) :
    ∃ a b : ℝ,
      minorVal (paper43_weightedColumns q r) = (a : WithTop ℝ) ∧
      minorVal ((paper43_weightedColumns q r).submatrix Fin.succ id) = (b : WithTop ℝ) ∧
      β - δ ≤ b - a := by
  have hdet : (Matrix.of fun i j => q (x j) i).det ≠ 0 :=
    HahnSeries.orderTop_ne_top.mp (ne_of_eq_of_ne hδ WithTop.coe_ne_top)
  obtain ⟨δ', α', a, b, hδ', hα', ha, hb, hgrow⟩ :=
    DetValuationMilestone.paper43_canonical_projected_minValue_growth
      (HahnSeries.addVal ℝ F) (fun _ => HahnSeries.orderTop_eq_top)
      (fun f g => AddValuation.map_mul _ f g)
      (fun f g => AddValuation.map_add _ f g)
      (Matrix.of fun i j => q (x j) i) (paper43_weightedColumns q r) x
      (fun i => HahnSeries.single (dist r (x i)) (1 : F))
      (fun i => (paper43_weightedColumns_rescale q r (x i)).symm) hdet
  exact ⟨a, b,
    (paper43_tupleMinorVal_eq_minorVal (paper43_weightedColumns q r)).symm.trans ha,
    (paper43_tupleMinorVal_eq_minorVal ((paper43_weightedColumns q r).submatrix Fin.succ id)).symm.trans hb,
    by simpa only [WithTop.coe_inj.mp (hδ'.symm.trans hδ),
      WithTop.coe_inj.mp (hα'.symm.trans hβ)] using hgrow⟩

theorem paper43_fresh_rowReplace_valuation_eq_cramerMin {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (hr : q r = Pi.single 0 1)
    (hfree : ∀ x : Fin (n + 1) → M,
      FreeOf (Set.range fun y : M => (Sum.inr (t, y) : Var (n + 1) M)) (colDet q x))
    (x : Fin (n + 1) → M) (hx : Function.Injective x) :
    nu (colDet (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) =
      Finset.univ.inf (fun i => nu
        (((Matrix.of fun a b => q (x b) a).updateCol i (Pi.single 0 1)).det *
          zp (dist r (x i)))) := by
  exact (paper43_fresh_rowReplace_valuation_eq_inf q r t hr hfree x hx).trans
    (Finset.inf_congr rfl fun i _ => by
      simp only [← hr, KServerAlgebra.paper43_updateCol_column_family, paper43_nu_mul, paper43_nu_zp, colDet,
        add_comm])

theorem paper43_request_projected_minor_growth {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (hr : q r = Pi.single 0 1)
    (hfree : ∀ y : Fin (n + 1) → M,
      FreeOf (Set.range fun z : M => (Sum.inr (t, z) : Var (n + 1) M)) (colDet q y))
    (x : Fin (n + 1) → M) (hx : Function.Injective x) (δ β : ℝ)
    (hδ : nu (colDet q x) = (δ : WithTop ℝ))
    (hβ : nu (colDet (rowReplace q
      (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) = (β : WithTop ℝ)) :
    ∃ a b : ℝ,
      minorVal (paper43_weightedColumns q r) = (a : WithTop ℝ) ∧
      minorVal ((paper43_weightedColumns q r).submatrix Fin.succ id) = (b : WithTop ℝ) ∧
      β - δ ≤ b - a := by
  exact paper43_projected_weighted_growth_of_cramer_min q r x δ β hδ
    ((paper43_fresh_rowReplace_valuation_eq_cramerMin q r t hr hfree x hx).symm.trans hβ)

end KServerConj
end PaperFile021

section PaperFile022
namespace KServerConj

theorem paper43_minorVal_le_tuple {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (x : I → J) :
    minorVal G ≤ HahnSeries.addVal ℝ F (G.submatrix id x).det := by
  simpa only [paper43_minorVal_eq_embeddingMinorVal] using
    DetValuationMilestone.paper43_embeddingMinorVal_le_tuple (HahnSeries.addVal ℝ F)
      (AddValuation.map_zero _) G x

theorem paper43_exists_minorVal_minimizer {F I J : Type*}
    [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (a : ℝ)
    (ha : minorVal G = (a : WithTop ℝ)) :
    ∃ x : I ↪ J, HahnSeries.addVal ℝ F (G.submatrix id x).det = (a : WithTop ℝ) := by
  classical
  have hh : DetValuationMilestone.paper43_embeddingMinorVal (HahnSeries.addVal ℝ F) G =
      (a : WithTop ℝ) := (paper43_minorVal_eq_embeddingMinorVal G).symm.trans ha
  unfold DetValuationMilestone.paper43_embeddingMinorVal at hh
  obtain ⟨x, _, hx⟩ := (Finset.inf_le_iff (show (a : WithTop ℝ) < ⊤ by simp)).mp hh.le
  exact ⟨x, le_antisymm hx (hh.symm.trans_le (Finset.inf_le (Finset.mem_univ x)))⟩

end KServerConj
end PaperFile022

section PaperFile023
open scoped BigOperators

namespace KServerConj

theorem paper43_det_updateCol_e0 {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (j : Fin (n + 1)) :
    (A.updateCol j (Pi.single 0 1)).det =
      (-1 : R) ^ j.val * (A.submatrix Fin.succ j.succAbove).det := by
  rw [Matrix.det_succ_column _ j]
  simp [Matrix.updateCol, Function.update, Pi.single_apply, mul_ite, ite_mul,
    Matrix.submatrix, Fin.succAbove_ne]

theorem paper43_scaled_cramer_factor {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A H : Matrix ι ι R) (c : ι → R) (v : ι → R)
    (hcol : ∀ a j, A a j = c j * H a j) (i : ι) :
    (A.updateCol i v).det * c i = (∏ j, c j) * (H.updateCol i v).det := by
  calc
    _ = (A.updateCol i (c i • v)).det := by
      simpa only [mul_comm] using (Matrix.det_updateCol_smul A i (c i) v).symm
    _ = (Matrix.of (fun a j => c j * (H.updateCol i v) a j)).det := by
      apply congrArg Matrix.det
      ext a j
      by_cases hj : j = i <;>
        simp [Matrix.updateCol, Function.update, hj, hcol, Pi.smul_apply, smul_eq_mul]
    _ = _ := Matrix.det_mul_row c (H.updateCol i v)

theorem paper43_projected_minor_le_cramer {F : Type*} [Field F] {n : ℕ} {M : Type*} [Fintype M]
    (H : Matrix (Fin (n + 1)) M (HahnSeries ℝ F)) (x : Fin (n + 1) → M)
    (j : Fin (n + 1)) :
    minorVal (H.submatrix Fin.succ id) ≤
      HahnSeries.addVal ℝ F ((H.submatrix id x).updateCol j (Pi.single 0 1)).det := by
  rw [paper43_det_updateCol_e0]
  simp only [AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_neg,
    AddValuation.map_one, nsmul_zero, zero_add]
  simpa only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] using
    paper43_minorVal_le_tuple (H.submatrix Fin.succ id) (x ∘ j.succAbove)

theorem paper43_weighted_cramer_ge_projected {n : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (x : Fin (n + 1) → M)
    (b : ℝ)
    (hb : minorVal ((paper43_weightedColumns q r).submatrix Fin.succ id) = (b : WithTop ℝ))
    (i : Fin (n + 1)) :
    (((∑ j, dist r (x j)) + b : ℝ) : WithTop ℝ) ≤
      nu (((Matrix.of fun a j => q (x j) a).updateCol i (Pi.single 0 1)).det *
        zp (dist r (x i))) := by
  have hcol (a j : Fin (n + 1)) : q (x j) a =
      (zp (dist r (x j)) : K (n + 1) M) * paper43_weightedColumns q r a (x j) := by
    exact (congrFun (paper43_weightedColumns_rescale q r (x j)) a).symm
  have hfac := paper43_scaled_cramer_factor (Matrix.of fun a j => q (x j) a)
    ((paper43_weightedColumns q r).submatrix id x) (fun j => (zp (dist r (x j)) : K (n + 1) M))
    (Pi.single 0 1) hcol i
  rw [hfac, paper43_nu_mul, ← paper43_zp_sum Finset.univ (fun j => dist r (x j)), paper43_nu_zp, WithTop.coe_add]
  exact add_le_add le_rfl (hb.symm.trans_le (paper43_projected_minor_le_cramer (paper43_weightedColumns q r) x i))

theorem paper43_weighted_det_valuation {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (x : Fin (n + 1) → M)
    (a : ℝ)
    (ha : nu ((paper43_weightedColumns q r).submatrix id x).det = (a : WithTop ℝ)) :
    nu (colDet q x) = (((∑ j, dist r (x j)) + a : ℝ) : WithTop ℝ) := by
  have hA : (Matrix.of fun i j => q (x j) i) =
      Matrix.of (fun i j => (zp (dist r (x j)) : K (n + 1) M) *
        ((paper43_weightedColumns q r).submatrix id x) i j) := by
    apply Matrix.ext
    intro i j
    exact (congrFun (paper43_weightedColumns_rescale q r (x j)) i).symm
  change nu (Matrix.of (fun i j => q (x j) i)).det = _
  rw [hA, Matrix.det_mul_row, paper43_nu_mul, ← paper43_zp_sum Finset.univ (fun j => dist r (x j)),
    paper43_nu_zp, ha, ← WithTop.coe_add]

end KServerConj
end PaperFile023

section PaperFile024
namespace KServerConj

theorem paper43_exists_injective_enumeration {M : Type*} [DecidableEq M] {k : ℕ}
    (X : Finset M) (hX : X.card = k) :
    ∃ x : Fin k → M, Function.Injective x ∧ Finset.univ.image x = X := by
  classical
  let e : X ≃ Fin k := X.equivFinOfCardEq hX
  let x : Fin k → M := fun i => (e.symm i).val
  have hx : Function.Injective x := fun i j h => e.symm.injective (Subtype.ext h)
  refine ⟨x, hx, ?_⟩
  apply Finset.ext
  intro a
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact (e.symm i).property
  · intro ha
    refine ⟨e ⟨a, ha⟩, ?_⟩
    exact congrArg Subtype.val (e.symm_apply_apply ⟨a, ha⟩)

end KServerConj
end PaperFile024

section PaperFile025
open scoped BigOperators

namespace KServerConj

theorem paper43_projected_minor_growth_bound {M : Type*} [PseudoMetricSpace M]
    [Fintype M] [DecidableEq M] {m : ℕ}
    (q : M → Fin (m + 1) → K (m + 1) M) (r : M)
    (s : Fin (m + 1) → M) (hs : Function.Injective s) (w w' : Finset M → ℝ)
    (hrep : ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet q x) = (w (Finset.univ.image x) : WithTop ℝ))
    (hcost : ∀ x : Fin (m + 1) → M, Function.Injective x →
      (Finset.univ.inf fun i => nu
        (((Matrix.of fun a b => q (x b) a).updateCol i (Pi.single 0 1)).det *
          zp (dist r (x i)))) = (w' (Finset.univ.image x) : WithTop ℝ)) :
    ∃ a b : ℝ, minorVal (paper43_weightedColumns q r) = (a : WithTop ℝ) ∧
      minorVal ((paper43_weightedColumns q r).submatrix Fin.succ id) = (b : WithTop ℝ) ∧
      ∀ x : Fin (m + 1) → M, Function.Injective x →
        w' (Finset.univ.image x) - w (Finset.univ.image x) ≤ b - a := by
  obtain ⟨a, b, ha, hb, _⟩ := paper43_projected_weighted_growth_of_cramer_min q r s
    (w (Finset.univ.image s)) (w' (Finset.univ.image s)) (hrep s hs) (hcost s hs)
  refine ⟨a, b, ha, hb, ?_⟩
  intro x hx
  obtain ⟨a', b', ha', hb', hg⟩ := paper43_projected_weighted_growth_of_cramer_min q r x
    (w (Finset.univ.image x)) (w' (Finset.univ.image x)) (hrep x hx) (hcost x hx)
  have hea : a' = a := WithTop.coe_inj.mp (ha'.symm.trans ha)
  have heb : b' = b := WithTop.coe_inj.mp (hb'.symm.trans hb)
  simpa only [hea, heb] using hg

theorem paper43_projected_minor_growth_attained {M : Type*} [PseudoMetricSpace M]
    [Fintype M] [DecidableEq M] {m : ℕ}
    (q : M → Fin (m + 1) → K (m + 1) M) (r : M) (w w' : Finset M → ℝ)
    (hrep : ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet q x) = (w (Finset.univ.image x) : WithTop ℝ))
    (hcost : ∀ x : Fin (m + 1) → M, Function.Injective x →
      (Finset.univ.inf fun i => nu
        (((Matrix.of fun a b => q (x b) a).updateCol i (Pi.single 0 1)).det *
          zp (dist r (x i)))) = (w' (Finset.univ.image x) : WithTop ℝ))
    (a b : ℝ) (ha : minorVal (paper43_weightedColumns q r) = (a : WithTop ℝ))
    (hb : minorVal ((paper43_weightedColumns q r).submatrix Fin.succ id) = (b : WithTop ℝ)) :
    ∃ x : Fin (m + 1) → M, Function.Injective x ∧
      b - a ≤ w' (Finset.univ.image x) - w (Finset.univ.image x) := by
  obtain ⟨x, hxmin⟩ := paper43_exists_minorVal_minimizer (paper43_weightedColumns q r) a ha
  have hnew : (((∑ j, dist r (x j)) + b : ℝ) : WithTop ℝ) ≤
      (w' (Finset.univ.image x) : WithTop ℝ) := by
    rw [← hcost x x.injective]
    exact Finset.le_inf (fun i _ => paper43_weighted_cramer_ge_projected q r x b hb i)
  have hold : w (Finset.univ.image x) = (∑ j, dist r (x j)) + a :=
    WithTop.coe_inj.mp ((hrep x x.injective).symm.trans
      (paper43_weighted_det_valuation q r x a hxmin))
  refine ⟨x, x.injective, ?_⟩
  have hnew_real := WithTop.coe_le_coe.mp hnew
  linarith only [hold, hnew_real]

theorem paper43_projected_extendedCost_eq {M : Type*} [PseudoMetricSpace M]
    [Fintype M] [DecidableEq M] {m : ℕ}
    (q : M → Fin (m + 1) → K (m + 1) M) (r : M)
    (s : Fin (m + 1) → M) (hs : Function.Injective s) (w w' : Finset M → ℝ)
    (hrep : ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet q x) = (w (Finset.univ.image x) : WithTop ℝ))
    (hcost : ∀ x : Fin (m + 1) → M, Function.Injective x →
      (Finset.univ.inf fun i => nu
        (((Matrix.of fun a b => q (x b) a).updateCol i (Pi.single 0 1)).det *
          zp (dist r (x i)))) = (w' (Finset.univ.image x) : WithTop ℝ)) :
    ∃ a b : ℝ, minorVal (paper43_weightedColumns q r) = (a : WithTop ℝ) ∧
      minorVal ((paper43_weightedColumns q r).submatrix Fin.succ id) = (b : WithTop ℝ) ∧
      (⨆ X : {X : Finset M // X.card = m + 1}, w' X.val - w X.val) = b - a := by
  classical
  have hS : (Finset.univ.image s).card = m + 1 := by
    rw [Finset.card_image_of_injective _ hs]
    simp
  letI : Nonempty {X : Finset M // X.card = m + 1} := ⟨⟨Finset.univ.image s, hS⟩⟩
  obtain ⟨a, b, ha, hb, hupper⟩ := paper43_projected_minor_growth_bound q r s hs w w' hrep hcost
  refine ⟨a, b, ha, hb, le_antisymm ?_ ?_⟩
  · apply ciSup_le
    intro X
    obtain ⟨x, hx, himage⟩ := paper43_exists_injective_enumeration X.val X.property
    simpa only [himage] using hupper x hx
  · obtain ⟨x, hx, hgrow⟩ := paper43_projected_minor_growth_attained q r w w' hrep hcost a b ha hb
    have hX : (Finset.univ.image x).card = m + 1 := by
      rw [Finset.card_image_of_injective _ hx]
      simp
    exact hgrow.trans (le_ciSup (Finite.bddAbove_range
      (fun X : {X : Finset M // X.card = m + 1} => w' X.val - w X.val))
      ⟨Finset.univ.image x, hX⟩)

end KServerConj
end PaperFile025

section PaperFile026
namespace KServerConj

theorem paper43_image_update_injective {k : ℕ} {M : Type*} [DecidableEq M]
    (x : Fin k → M) (hx : Function.Injective x) (i : Fin k) (r : M) :
    Finset.univ.image (Function.update x i r) =
      insert r ((Finset.univ.image x).erase (x i)) := by
  classical
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_erase]
  constructor
  · rintro ⟨j, rfl⟩
    by_cases hji : j = i
    · subst j
      exact Or.inl (Function.update_self _ _ _)
    · rw [Function.update_of_ne hji]
      exact Or.inr ⟨fun h => hji (hx h), j, rfl⟩
  · rintro (rfl | ⟨ha, j, hj⟩)
    · exact ⟨i, Function.update_self _ _ _⟩
    · have hji : j ≠ i := fun h => ha (by simpa only [h] using hj.symm)
      exact ⟨j, by rw [Function.update_of_ne hji]; exact hj⟩

theorem paper43_update_injective_iff_admissible {k : ℕ} {M : Type*} [DecidableEq M]
    (x : Fin k → M) (hx : Function.Injective x) (i : Fin k) (r : M) :
    Function.Injective (Function.update x i r) ↔
      r ∉ Finset.univ.image x ∨ x i = r := by
  classical
  constructor
  · intro hu
    by_cases hr : r ∈ Finset.univ.image x
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hr
      by_cases hji : j = i
      · exact Or.inr (hji ▸ hj)
      · have heq : Function.update x i r j = Function.update x i r i := by
          rw [Function.update_of_ne hji, Function.update_self, hj]
        exact False.elim (hji (hu heq))
    · exact Or.inl hr
  · rintro (hr | hr)
    · exact paper43_update_injective_of_not_mem_range x hx r
        (fun ⟨j, hj⟩ => hr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)) i
    · exact (Function.update_eq_self_iff.mpr hr.symm : Function.update x i r = x).symm ▸ hx

end KServerConj
end PaperFile026

section PaperFile038
open scoped BigOperators

namespace KServerConj

theorem paper43_determinant_cost_inf_eq_admissible {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M)
    (w : (Fin (n + 1) → M) → ℝ) (b : ℝ)
    (hrep : ∀ y : Fin (n + 1) → M, Function.Injective y →
      nu (colDet q y) = (w y : WithTop ℝ))
    (x : Fin (n + 1) → M) (hx : Function.Injective x)
    (hle : ∀ i, Function.Injective (Function.update x i r) →
      b ≤ w (Function.update x i r) + dist r (x i))
    (hge : ∃ i, Function.Injective (Function.update x i r) ∧
      w (Function.update x i r) + dist r (x i) ≤ b) :
    Finset.univ.inf (fun i => (dist r (x i) : WithTop ℝ) +
      nu (colDet q (Function.update x i r))) = (b : WithTop ℝ) := by
  classical
  apply le_antisymm
  · obtain ⟨i, hi, hcost⟩ := hge
    exact (Finset.inf_le
      (f := fun i => (dist r (x i) : WithTop ℝ) + nu (colDet q (Function.update x i r)))
      (Finset.mem_univ i)).trans (by
        simpa only [hrep _ hi, ← WithTop.coe_add, add_comm] using
          (WithTop.coe_le_coe.mpr hcost))
  · refine Finset.le_inf ?_
    intro i _
    by_cases hi : Function.Injective (Function.update x i r)
    · simpa only [hrep _ hi, ← WithTop.coe_add, add_comm] using
        (WithTop.coe_le_coe.mpr (hle i hi))
    · simp only [paper43_colDet_eq_zero_of_not_injective q _ hi, paper43_nu_zero, WithTop.add_top, le_top]

theorem paper43_fresh_request_representation_admissible {M : Type*} [PseudoMetricSpace M]
    [Fintype M] [DecidableEq M] {m : ℕ}
    (hm : 1 ≤ m) (s : Fin (m + 1) → M) (hs : Function.Injective s) (r : ℕ → M) (t : ℕ)
    (ht : 1 ≤ t) (q : M → Fin (m + 1) → K (m + 1) M)
    (hrep : ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet q x) = (workFn (m + 1) (Finset.univ.image s) r (t - 1)
        (Finset.univ.image x) : WithTop ℝ))
    (hfree : ∀ x : Fin (m + 1) → M,
      FreeOf (Set.range fun y : M => (Sum.inr (t, y) : Var (m + 1) M)) (colDet q x))
    (hr : q (r t) = Pi.single 0 1) :
    ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet (rowReplace q (freshRow r t)) x) =
        (workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x) : WithTop ℝ) := by
  classical
  intro x hx
  have hS : (Finset.univ.image s).card = m + 1 := by
    rw [Finset.card_image_of_injective _ hs]
    simp
  have hX : (Finset.univ.image x).card = m + 1 := by
    rw [Finset.card_image_of_injective _ hx]
    simp
  have hrec := (eq_2 (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
    (Finset.univ.image s) hS r).2 t ht (Finset.univ.image x) hX
  have hle (i : Fin (m + 1)) (hi : Function.Injective (Function.update x i (r t))) :
      workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x) ≤
        workFn (m + 1) (Finset.univ.image s) r (t - 1)
          (Finset.univ.image (Function.update x i (r t))) + dist (r t) (x i) := by
    rw [paper43_image_update_injective x hx i (r t)]
    exact hrec.1 (x i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      ((paper43_update_injective_iff_admissible x hx i (r t)).mp hi)
  have hge : ∃ i : Fin (m + 1), Function.Injective (Function.update x i (r t)) ∧
      workFn (m + 1) (Finset.univ.image s) r (t - 1)
        (Finset.univ.image (Function.update x i (r t))) + dist (r t) (x i) ≤
          workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x) := by
    obtain ⟨a, ha, hvalid, heq⟩ := hrec.2
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨i, (paper43_update_injective_iff_admissible x hx i (r t)).mpr hvalid, ?_⟩
    rw [paper43_image_update_injective x hx i (r t)]
    exact heq.ge
  have hcost := paper43_determinant_cost_inf_eq_admissible q (r t)
    (fun y => workFn (m + 1) (Finset.univ.image s) r (t - 1) (Finset.univ.image y))
    (workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x)) hrep x hx hle hge
  change nu (colDet (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist (r t) y))) x) = _
  exact (paper43_fresh_rowReplace_valuation_eq_inf q (r t) t hr hfree x hx).trans hcost

end KServerConj
end PaperFile038

section PaperFile039
open scoped BigOperators

namespace KServerConj

theorem paper43_request_cramer_min_eq_workFn {M : Type*} [PseudoMetricSpace M]
    [Fintype M] [DecidableEq M] {m : ℕ}
    (s : Fin (m + 1) → M) (hs : Function.Injective s) (r : ℕ → M) (t : ℕ)
    (ht : 1 ≤ t) (q : M → Fin (m + 1) → K (m + 1) M)
    (hrep : ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet q x) = (workFn (m + 1) (Finset.univ.image s) r (t - 1)
        (Finset.univ.image x) : WithTop ℝ))
    (hr : q (r t) = Pi.single 0 1) (x : Fin (m + 1) → M) (hx : Function.Injective x) :
    (Finset.univ.inf fun i => nu
      (((Matrix.of fun a b => q (x b) a).updateCol i (Pi.single 0 1)).det *
        zp (dist (r t) (x i)))) =
      (workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x) : WithTop ℝ) := by
  classical
  have hS : (Finset.univ.image s).card = m + 1 := by
    rw [Finset.card_image_of_injective _ hs]
    simp
  have hX : (Finset.univ.image x).card = m + 1 := by
    rw [Finset.card_image_of_injective _ hx]
    simp
  have hrec := (eq_2 (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
    (Finset.univ.image s) hS r).2 t ht (Finset.univ.image x) hX
  have hle (i : Fin (m + 1)) (hi : Function.Injective (Function.update x i (r t))) :
      workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x) ≤
        workFn (m + 1) (Finset.univ.image s) r (t - 1)
          (Finset.univ.image (Function.update x i (r t))) + dist (r t) (x i) := by
    rw [paper43_image_update_injective x hx i (r t)]
    exact hrec.1 (x i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      ((paper43_update_injective_iff_admissible x hx i (r t)).mp hi)
  have hge : ∃ i : Fin (m + 1), Function.Injective (Function.update x i (r t)) ∧
      workFn (m + 1) (Finset.univ.image s) r (t - 1)
        (Finset.univ.image (Function.update x i (r t))) + dist (r t) (x i) ≤
          workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x) := by
    obtain ⟨a, ha, hvalid, heq⟩ := hrec.2
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨i, (paper43_update_injective_iff_admissible x hx i (r t)).mpr hvalid, ?_⟩
    rw [paper43_image_update_injective x hx i (r t)]
    exact heq.ge
  have hcost := paper43_determinant_cost_inf_eq_admissible q (r t)
    (fun y => workFn (m + 1) (Finset.univ.image s) r (t - 1) (Finset.univ.image y))
    (workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x)) hrep x hx hle hge
  refine (Finset.inf_congr rfl (fun i _ => ?_)).trans hcost
  simp only [← hr, KServerAlgebra.paper43_updateCol_column_family, paper43_nu_mul, paper43_nu_zp, colDet, add_comm]

end KServerConj
end PaperFile039

open KServerConj

theorem solution {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M] {m : ℕ}
    (hm : 1 ≤ m) (s : Fin (m + 1) → M) (hs : Function.Injective s) (r : ℕ → M) (t : ℕ)
    (ht : 1 ≤ t) (q : M → Fin (m + 1) → K (m + 1) M)
    (hrep : ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet q x) = ((workFn (m + 1) (Finset.univ.image s) r (t - 1) (Finset.univ.image x) : ℝ) :
        WithTop ℝ))
    (hr : q (r t) = Pi.single 0 1) :
    ∃ a b : ℝ, minorVal (Hmat q (r t)) = (a : WithTop ℝ) ∧ minorVal (Hhat q (r t)) = (b : WithTop ℝ) ∧
      extCost (m + 1) (Finset.univ.image s) r t = b - a := by
  change ∃ a b : ℝ, minorVal (paper43_weightedColumns q (r t)) = (a : WithTop ℝ) ∧
    minorVal ((paper43_weightedColumns q (r t)).submatrix Fin.succ id) = (b : WithTop ℝ) ∧
      (⨆ X : {X : Finset M // X.card = m + 1},
        workFn (m + 1) (Finset.univ.image s) r t X.val -
          workFn (m + 1) (Finset.univ.image s) r (t - 1) X.val) = b - a
  exact paper43_projected_extendedCost_eq q (r t) s hs
    (fun X => workFn (m + 1) (Finset.univ.image s) r (t - 1) X)
    (fun X => workFn (m + 1) (Finset.univ.image s) r t X) hrep
    (fun x hx => paper43_request_cramer_min_eq_workFn s hs r t ht q hrep hr x hx)

#print axioms solution
