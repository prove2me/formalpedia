-- Prove2me | solution 1 for KServerConj.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T03:29:32.893205+00:00
-- url     : https://prove2.me/submissions/8d7c421c-a989-4f77-84ff-6f631859d6bb

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Definitions.Def_KServerConj_workFn
import Definitions.Def_KServerConj_cl
import Definitions.Def_KServerConj_Psi
import Definitions.Def_KServerConj_IsRun
import Theorems.Thm_KServerConj_theorem_2_4
set_option autoImplicit false

section PaperFile004
open scoped BigOperators

theorem paper51_det_mul_det_updateCol
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

def paper51_prependColumn {n : ℕ} {R : Type*} (v : Fin (n + 1) → R)
    (W : Matrix (Fin (n + 1)) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun r j => Fin.cases (v r) (fun j => W r j) j

theorem paper51_updateCol_prepend {n : ℕ} {R : Type*}
    (v w : Fin (n + 1) → R) (W : Matrix (Fin (n + 1)) (Fin n) R) :
    (paper51_prependColumn v W).updateCol 0 w = paper51_prependColumn w W := by
  ext r j
  cases j using Fin.cases <;> simp [paper51_prependColumn, Matrix.updateCol]

theorem paper51_det_prepend_single {n : ℕ} {R : Type*} [CommRing R]
    (W : Matrix (Fin (n + 1)) (Fin n) R) :
    (paper51_prependColumn (Pi.single 0 1) W).det = (W.submatrix Fin.succ id).det := by
  rw [Matrix.det_succ_column_zero]
  simp [paper51_prependColumn, Matrix.submatrix, Pi.single_apply, mul_ite, ite_mul]

theorem paper51_det_mul_det_prepend {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (v : Fin (n + 1) → R) (W : Matrix (Fin (n + 1)) (Fin n) R) :
    A.det * (paper51_prependColumn v W).det =
      ∑ i, (A.updateCol i v).det * (paper51_prependColumn (fun r => A r i) W).det := by
  simpa only [paper51_updateCol_prepend] using paper51_det_mul_det_updateCol A (paper51_prependColumn v W) 0 v

theorem paper51_det_prepend_smul {n : ℕ} {R : Type*} [CommRing R]
    (c : R) (v : Fin (n + 1) → R) (W : Matrix (Fin (n + 1)) (Fin n) R) :
    (paper51_prependColumn (c • v) W).det = c * (paper51_prependColumn v W).det := by
  simpa only [paper51_updateCol_prepend] using Matrix.det_updateCol_smul (paper51_prependColumn v W) 0 c v

theorem paper51_prepend_submatrix {n : ℕ} {R ι : Type*}
    (H : Matrix (Fin (n + 1)) ι R) (x : ι) (y : Fin n → ι) :
    paper51_prependColumn (fun r => H r x) (H.submatrix id y) =
      H.submatrix id (Fin.cases x y) := by
  ext r j
  cases j using Fin.cases <;> rfl

theorem paper51_projected_minor_identity {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (y : Fin n → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i))) :
    A.det * (H.submatrix Fin.succ y).det =
      ∑ i, (A.updateCol i (Pi.single 0 1)).det * c i *
        (paper51_prependColumn (fun r => H r (x i)) (H.submatrix id y)).det := by
  simpa only [paper51_det_prepend_single, Matrix.submatrix_submatrix, Function.comp_id,
    Function.id_comp, hcol, paper51_det_prepend_smul, mul_assoc] using
      paper51_det_mul_det_prepend A (Pi.single 0 1) (H.submatrix id y)

theorem paper51_exists_nonzero_projected_minor {n : ℕ} {R ι : Type*} [CommRing R]
    (H : Matrix (Fin (n + 1)) ι R) (x : Fin (n + 1) → ι)
    (hdet : (H.submatrix id x).det ≠ 0) :
    ∃ y : Fin n → ι, (H.submatrix Fin.succ y).det ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hdet
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  simp only [Matrix.submatrix_submatrix, Function.id_comp, h, mul_zero]

theorem paper51_nonzero_unscaled_minor {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i)))
    (hdet : A.det ≠ 0) : (H.submatrix id x).det ≠ 0 := by
  have hA : A = Matrix.of (fun r i => c i * (H.submatrix id x) r i) :=
    funext fun r => funext fun i => congrFun (hcol i) r
  rw [hA, Matrix.det_mul_row c (H.submatrix id x)] at hdet
  exact right_ne_zero_of_mul hdet

theorem paper51_det_eq_sum_scaled_cramer {n : ℕ} {R ι : Type*} [CommRing R]
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

theorem paper51_exists_nonzero_scaled_cramer {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i)))
    (hdet : A.det ≠ 0) :
    ∃ i, (A.updateCol i (Pi.single 0 1)).det * c i ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hdet (by
    simpa only [h, zero_mul, Finset.sum_const_zero] using paper51_det_eq_sum_scaled_cramer A H x c hcol)

end DetValuationMilestone
end PaperFile005

section PaperFile006
open scoped BigOperators

namespace DetValuationMilestone

theorem paper51_valuation_sum_lower_bound
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

theorem paper51_valuation_lower_bound_of_minor_identity
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
    apply paper51_valuation_sum_lower_bound ν hzero hadd
    intro i _
    simpa only [WithTop.coe_add, hmul] using add_le_add (ha i) (hM i)
  rw [← hid, hmul, hD] at hsum
  apply WithTop.le_of_add_le_add_left (x := (δ : WithTop ℝ)) (by simp)
  simpa only [← WithTop.coe_add,
    show δ + (α + μ - δ) = α + μ by linarith] using hsum

theorem paper51_minValue_growth_of_minor_identities
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
  have h := paper51_valuation_lower_bound_of_minor_identity ν hzero hmul hadd
    D (P y) a (fun i => M i y) δ α μ hD (hid y) ha (fun i => hM i y)
  rw [hy, WithTop.coe_le_coe] at h
  linarith

theorem paper51_exists_real_minimum_of_nonzero
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

theorem paper51_canonical_minValue_growth
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
  obtain ⟨α, hα, ha, _⟩ := paper51_exists_real_minimum_of_nonzero ν htop a ha_nonzero
  obtain ⟨μ, hμ, hF, _⟩ := paper51_exists_real_minimum_of_nonzero ν htop F hF_nonzero
  obtain ⟨μhat, hμhat, _, y, hy, _⟩ :=
    paper51_exists_real_minimum_of_nonzero ν htop P hP_nonzero
  exact ⟨δ, α, μ, μhat, hδ.symm, hα, hμ, hμhat,
    paper51_minValue_growth_of_minor_identities ν ((htop 0).mpr rfl) hmul hadd
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

theorem paper51_canonical_projected_minValue_growth
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
  exact paper51_canonical_minValue_growth ν htop hmul hadd A.det
    (fun i => (A.updateCol i (Pi.single 0 1)).det * c i)
    (fun y : Fin n → ι => (H.submatrix Fin.succ y).det)
    (fun z : Fin (n + 1) → ι => (H.submatrix id z).det)
    (fun i y => (paper51_prependColumn (fun r => H r (x i)) (H.submatrix id y)).det)
    hdet (paper51_exists_nonzero_scaled_cramer A H x c hcol hdet)
    (paper51_exists_nonzero_projected_minor H x (paper51_nonzero_unscaled_minor A H x c hcol hdet))
    ⟨x, paper51_nonzero_unscaled_minor A H x c hcol hdet⟩
    (fun y => paper51_projected_minor_identity A H x y c hcol)
    (fun i y => Or.inr ⟨Fin.cases (x i) y,
      congrArg Matrix.det (paper51_prepend_submatrix H (x i) y)⟩)

end DetValuationMilestone
end PaperFile007

section PaperFile008
open scoped BigOperators

namespace DetValuationMilestone

noncomputable def paper51_tupleMinorVal
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (G : Matrix I J R) : WithTop ℝ := by
  classical
  exact Finset.univ.inf fun e : I → J => ν (G.submatrix id e).det

noncomputable def paper51_embeddingMinorVal
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (G : Matrix I J R) : WithTop ℝ := by
  classical
  exact Finset.univ.inf fun e : I ↪ J => ν (G.submatrix id e).det

theorem paper51_det_submatrix_eq_zero_of_not_injective
    {I J R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (G : Matrix I J R) (x : I → J) (hx : ¬ Function.Injective x) :
    (G.submatrix id x).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hx
  exact Matrix.det_zero_of_column_eq hne (fun r => congrArg (fun j => G r j) hij)

theorem paper51_embeddingMinorVal_le_tuple
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤)
    (G : Matrix I J R) (x : I → J) :
    paper51_embeddingMinorVal ν G ≤ ν (G.submatrix id x).det := by
  classical
  exact (Classical.em (Function.Injective x)).elim
    (fun hx => Finset.inf_le (f := fun e : I ↪ J => ν (G.submatrix id e).det)
      (Finset.mem_univ (⟨x, hx⟩ : I ↪ J)))
    (fun hx => by
      simpa only [paper51_det_submatrix_eq_zero_of_not_injective G x hx, hzero] using
        (le_top : paper51_embeddingMinorVal ν G ≤ ⊤))

theorem paper51_tupleMinorVal_eq_embeddingMinorVal
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (G : Matrix I J R) :
    paper51_tupleMinorVal ν G = paper51_embeddingMinorVal ν G := by
  classical
  exact le_antisymm
    (Finset.le_inf fun e _ => Finset.inf_le
      (f := fun x : I → J => ν (G.submatrix id x).det) (Finset.mem_univ (e : I → J)))
    (Finset.le_inf fun x _ => paper51_embeddingMinorVal_le_tuple ν hzero G x)

theorem paper51_add_finset_inf {ι : Type*} (a : WithTop ℝ) (s : Finset ι)
    (f : ι → WithTop ℝ) :
    a + s.inf f = s.inf (fun i => a + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.inf_insert, ← ih, min_add_add_left]

theorem paper51_tupleMinorVal_mul
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (A : Matrix I I R) (G : Matrix I J R) :
    paper51_tupleMinorVal ν (A * G) = ν A.det + paper51_tupleMinorVal ν G := by
  have hval : ∀ x : I → J, ν ((A * G).submatrix id x).det =
      ν A.det + ν (G.submatrix id x).det := fun x =>
    (congrArg ν (Matrix.det_mul A (G.submatrix id x))).trans (hmul _ _)
  simpa only [paper51_tupleMinorVal, hval] using
    (paper51_add_finset_inf (ν A.det) (Finset.univ : Finset (I → J))
      (fun x => ν (G.submatrix id x).det)).symm

theorem paper51_embeddingMinorVal_mul
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (A : Matrix I I R) (G : Matrix I J R) :
    paper51_embeddingMinorVal ν (A * G) = ν A.det + paper51_embeddingMinorVal ν G := by
  simpa only [paper51_tupleMinorVal_eq_embeddingMinorVal ν hzero] using paper51_tupleMinorVal_mul ν hmul A G

end DetValuationMilestone
end PaperFile008

section PaperFile009
namespace KServerConj

theorem paper51_minorVal_eq_embeddingMinorVal
    {F I J : Type*} [Field F] [Fintype I] [hI : DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) :
    minorVal G = DetValuationMilestone.paper51_embeddingMinorVal (HahnSeries.addVal ℝ F) G := by
  classical
  cases Subsingleton.elim hI (Classical.decEq I)
  unfold minorVal DetValuationMilestone.paper51_embeddingMinorVal
  rfl

theorem paper51_minorVal_mul
    {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I I (HahnSeries ℝ F)) (G : Matrix I J (HahnSeries ℝ F)) :
    minorVal (A * G) = HahnSeries.addVal ℝ F A.det + minorVal G := by
  simpa only [paper51_minorVal_eq_embeddingMinorVal] using
    DetValuationMilestone.paper51_embeddingMinorVal_mul (HahnSeries.addVal ℝ F)
      (AddValuation.map_zero _) (fun x y => AddValuation.map_mul _ x y) A G

end KServerConj
end PaperFile009

section PaperFile010
open scoped BigOperators

namespace KServerConj

noncomputable def paper51_quadraticMatrix {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F) :
    Matrix (Sym2 (Fin k)) (Sym2 M) (HahnSeries ℝ F) :=
  fun p c => Sym2.lift ⟨fun x y =>
    HahnSeries.single (-dist x y) (1 : F) * symProd (q x) (q y) p,
    fun x y => by
      dsimp only
      rw [dist_comm, symProd_comm]⟩ c

theorem paper51_Qmat_eq_quadraticMatrix {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → K k M) : Qmat q = paper51_quadraticMatrix q := rfl

noncomputable def paper51_weightedColumns {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F) (r : M) :
    Matrix (Fin k) M (HahnSeries ℝ F) :=
  fun i x => HahnSeries.single (-dist r x) (1 : F) * q x i

noncomputable def paper51_negPairDist {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (x : Fin k → M) : Sym2 (Fin k) → ℝ :=
  Sym2.lift ⟨fun i j => -dist (x i) (x j),
    fun i j => congrArg Neg.neg (dist_comm (x i) (x j))⟩

theorem paper51_quadraticMatrix_submatrix {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) :
    (paper51_quadraticMatrix q).submatrix id (Sym2.map x) =
      Matrix.of (fun r c => HahnSeries.single (paper51_negPairDist x c) (1 : F) *
        sym2Mat (Matrix.of (fun i j => q (x j) i)) r c) := by
  funext r c
  induction c using Sym2.ind with
  | _ i j => rfl

end KServerConj
end PaperFile010

section PaperFile011
namespace KServerConj

variable {k : ℕ} {M : Type*}

@[simp] theorem paper51_nu_zero : nu (0 : K k M) = ⊤ := by
  exact AddValuation.map_zero _

@[simp] theorem paper51_nu_one : nu (1 : K k M) = 0 := by
  exact AddValuation.map_one _

@[simp] theorem paper51_nu_eq_top_iff (f : K k M) : nu f = ⊤ ↔ f = 0 := by
  exact HahnSeries.orderTop_eq_top

theorem paper51_nu_mul (f g : K k M) : nu (f * g) = nu f + nu g := by
  exact AddValuation.map_mul _ f g

theorem paper51_nu_add (f g : K k M) : min (nu f) (nu g) ≤ nu (f + g) := by
  exact AddValuation.map_add _ f g

@[simp] theorem paper51_nu_zp (a : ℝ) : nu (zp a : K k M) = (a : WithTop ℝ) := by
  exact HahnSeries.orderTop_single one_ne_zero

theorem paper51_varF_ne_zero (v : Var k M) : varF v ≠ 0 := by
  exact (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Var k M) ℚ) (F k M))).mpr
    (MvPolynomial.X_ne_zero v)

@[simp] theorem paper51_nu_coef (v : Var k M) : nu (coef v) = 0 := by
  simpa only [nu, HahnSeries.addVal_apply, coef, HahnSeries.C_apply, WithTop.coe_zero] using
    (HahnSeries.orderTop_single (a := (0 : ℝ)) (paper51_varF_ne_zero v))

theorem paper51_nu_C {c : F k M} (hc : c ≠ 0) : nu (HahnSeries.C c : K k M) = 0 := by
  simpa only [nu, HahnSeries.addVal_apply, HahnSeries.C_apply, WithTop.coe_zero] using
    (HahnSeries.orderTop_single (a := (0 : ℝ)) hc)

theorem paper51_coef_ne_zero (v : Var k M) : coef v ≠ 0 := by
  exact HahnSeries.single_ne_zero (paper51_varF_ne_zero v)

theorem paper51_zp_ne_zero (a : ℝ) : (zp a : K k M) ≠ 0 := by
  exact HahnSeries.single_ne_zero one_ne_zero

@[simp] theorem paper51_zp_zero : (zp 0 : K k M) = 1 := by
  exact HahnSeries.single_zero_one

theorem paper51_zp_add (a b : ℝ) : (zp (a + b) : K k M) = zp a * zp b := by
  simpa only [one_mul] using
    (HahnSeries.single_mul_single (a := a) (b := b) (r := (1 : F k M)) (s := 1)).symm

@[simp] theorem paper51_nu_neg (f : K k M) : nu (-f) = nu f := by
  exact AddValuation.map_neg _ _

@[simp] theorem paper51_nu_inv (f : K k M) : nu f⁻¹ = -(nu f) := by
  exact AddValuation.map_inv _

theorem paper51_nu_sum_ge {ι : Type*} [Fintype ι] (f : ι → K k M) (b : WithTop ℝ)
    (hf : ∀ i, b ≤ nu (f i)) : b ≤ nu (∑ i, f i) := by
  exact AddValuation.map_le_sum _ (fun i _ => hf i)

theorem paper51_nu_fresh_term (v : Var k M) (a : ℝ) (f : K k M) :
    nu (coef v * zp a * f) = (a : WithTop ℝ) + nu f := by
  simp only [paper51_nu_mul, paper51_nu_coef, paper51_nu_zp, zero_add]

theorem paper51_zp_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (zp (∑ i ∈ s, a i) : K k M) = ∏ i ∈ s, zp (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, paper51_zp_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, paper51_zp_add, ih]

end KServerConj
end PaperFile011

section PaperFile012
open scoped BigOperators

namespace KServerConj

variable {k : ℕ} {M : Type*}

theorem paper51_varF_algebraicIndependent : AlgebraicIndependent ℚ (@varF k M) := by
  exact (MvPolynomial.algebraicIndependent_X (Var k M) ℚ).map'
    (f := IsScalarTower.toAlgHom ℚ (MvPolynomial (Var k M) ℚ) (F k M))
    (IsFractionRing.injective (MvPolynomial (Var k M) ℚ) (F k M))

theorem paper51_varF_algebraicIndependent_over_complement (S : Set (Var k M)) :
    AlgebraicIndependent (IntermediateField.adjoin ℚ ((@varF k M) '' Sᶜ))
      (fun i : S => varF (i : Var k M)) := by
  exact IntermediateField.algebraicIndependent_adjoin_iff.mpr
    ((AlgebraicIndependent.iff_adjoin_image_compl S).mp paper51_varF_algebraicIndependent).2

theorem paper51_fresh_vars_linearIndependent {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) :
    LinearIndependent
      (IntermediateField.adjoin ℚ ((@varF k M) '' (Set.range v)ᶜ))
      (fun i => varF (v i)) := by
  exact (paper51_varF_algebraicIndependent_over_complement (Set.range v)).linearIndependent.comp
    (fun i => ⟨v i, Set.mem_range_self i⟩)
    (fun _ _ h => hv (congrArg Subtype.val h))

theorem paper51_complement_closure_le_adjoin (S : Set (Var k M)) :
    Subfield.closure ((@varF k M) '' Sᶜ) ≤
      (IntermediateField.adjoin ℚ ((@varF k M) '' Sᶜ)).toSubfield := by
  exact Subfield.closure_le.mpr (IntermediateField.subset_adjoin ℚ _)

theorem paper51_fresh_vars_sum_ne_zero {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) (b : Fin N → F k M)
    (hb : ∀ i, b i ∈ Subfield.closure ((@varF k M) '' (Set.range v)ᶜ))
    (hne : ∃ i, b i ≠ 0) :
    ∑ i, varF (v i) * b i ≠ 0 := by
  intro hz
  let c : Fin N → IntermediateField.adjoin ℚ ((@varF k M) '' (Set.range v)ᶜ) :=
    fun i => ⟨b i, paper51_complement_closure_le_adjoin (Set.range v) (hb i)⟩
  have hsum : ∑ i, c i • varF (v i) = 0 := by
    simpa only [c, IntermediateField.smul_def, Subtype.coe_mk, smul_eq_mul, mul_comm] using hz
  have hczero := Fintype.linearIndependent_iff.mp (paper51_fresh_vars_linearIndependent v hv) c hsum
  exact hne.elim (fun i hi => hi (congrArg Subtype.val (hczero i)))

end KServerConj
end PaperFile012

section PaperFile014
namespace KServerConj

theorem paper51_nu_det_C {k : ℕ} {M ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (F k M)) (hA : A.det ≠ 0) :
    nu (((HahnSeries.C : F k M →+* K k M).mapMatrix A).det) = 0 := by
  exact (congrArg nu ((HahnSeries.C : F k M →+* K k M).map_det A).symm).trans (paper51_nu_C hA)

end KServerConj
end PaperFile014

section PaperFile015
namespace KServerConj

noncomputable def paper51_hahnCoeffMap {F E : Type*} [Field F] [Field E] (g : F →+* E) :
    HahnSeries ℝ F →+* HahnSeries ℝ E where
  toFun f := f.map g
  map_zero' := HahnSeries.map_zero g.toZeroHom
  map_one' := by
    simpa only [map_one] using (HahnSeries.map_C (Γ := ℝ) (1 : F) g)
  map_add' _ _ := HahnSeries.map_add g.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul g.toNonUnitalRingHom

@[simp] theorem paper51_hahnCoeffMap_coeff {F E : Type*} [Field F] [Field E]
    (g : F →+* E) (f : HahnSeries ℝ F) (a : ℝ) :
    (paper51_hahnCoeffMap g f).coeff a = g (f.coeff a) := rfl

noncomputable def paper51_restrictCoeffs {F : Type*} [Field F] (S : Subfield F) (f : HahnSeries ℝ F)
    (hf : ∀ a, f.coeff a ∈ S) : HahnSeries ℝ S where
  coeff a := ⟨f.coeff a, hf a⟩
  isPWO_support' := f.isPWO_support.mono fun _ ha hz => ha (Subtype.ext hz)

@[simp] theorem paper51_restrictCoeffs_map {F : Type*} [Field F] (S : Subfield F)
    (f : HahnSeries ℝ F) (hf : ∀ a, f.coeff a ∈ S) :
    paper51_hahnCoeffMap S.subtype (paper51_restrictCoeffs S f hf) = f := by
  exact HahnSeries.coeff_injective rfl

theorem paper51_coeff_inv_mem_subfield {F : Type*} [Field F] (S : Subfield F)
    (f : HahnSeries ℝ F) (hf : ∀ a, f.coeff a ∈ S) :
    ∀ a, (f⁻¹).coeff a ∈ S := by
  have hmap : paper51_hahnCoeffMap S.subtype (paper51_restrictCoeffs S f hf)⁻¹ = f⁻¹ := by
    rw [map_inv₀, paper51_restrictCoeffs_map]
  exact fun a => (congrArg (fun g : HahnSeries ℝ F => g.coeff a) hmap) ▸
    (((paper51_restrictCoeffs S f hf)⁻¹).coeff a).property

end KServerConj
end PaperFile015

section PaperFile016
namespace KServerConj

variable {k : ℕ} {M : Type*}

theorem paper51_freeOf_zero (S : Set (Var k M)) : FreeOf S (0 : K k M) := by
  exact fun _ => Subfield.zero_mem _

theorem paper51_freeOf_single (S : Set (Var k M)) (a : ℝ) (c : F k M)
    (hc : c ∈ Subfield.closure ((fun v => varF v) '' Sᶜ)) :
    FreeOf S (HahnSeries.single a c) := by
  intro b
  rw [HahnSeries.coeff_single]
  exact ite_mem.mpr ⟨fun _ => hc, fun _ => Subfield.zero_mem _⟩

theorem paper51_freeOf_zp (S : Set (Var k M)) (a : ℝ) : FreeOf S (zp a : K k M) := by
  exact paper51_freeOf_single S a 1 (Subfield.one_mem _)

theorem paper51_freeOf_one (S : Set (Var k M)) : FreeOf S (1 : K k M) := by
  exact paper51_freeOf_single S 0 1 (Subfield.one_mem _)

theorem paper51_freeOf_coef (S : Set (Var k M)) (v : Var k M) (hv : v ∉ S) :
    FreeOf S (coef v) := by
  exact paper51_freeOf_single S 0 (varF v) (Subfield.subset_closure ⟨v, hv, rfl⟩)

theorem paper51_freeOf_add {S : Set (Var k M)} {f g : K k M} (hf : FreeOf S f) (hg : FreeOf S g) :
    FreeOf S (f + g) := by
  simpa only [FreeOf, HahnSeries.coeff_add] using
    fun a => Subfield.add_mem _ (hf a) (hg a)

theorem paper51_freeOf_neg {S : Set (Var k M)} {f : K k M} (hf : FreeOf S f) :
    FreeOf S (-f) := by
  simpa only [FreeOf, HahnSeries.coeff_neg] using
    fun a => Subfield.neg_mem _ (hf a)

theorem paper51_freeOf_mul {S : Set (Var k M)} {f g : K k M} (hf : FreeOf S f) (hg : FreeOf S g) :
    FreeOf S (f * g) := by
  intro a
  rw [HahnSeries.coeff_mul]
  exact Subfield.sum_mem _ fun ij _ => Subfield.mul_mem _ (hf ij.1) (hg ij.2)

theorem paper51_freeOf_inv {S : Set (Var k M)} {f : K k M} (hf : FreeOf S f) :
    FreeOf S f⁻¹ := by
  exact paper51_coeff_inv_mem_subfield _ f hf

noncomputable def paper51_freeOfSubfield (S : Set (Var k M)) : Subfield (K k M) where
  carrier := FreeOf S
  zero_mem' := paper51_freeOf_zero S
  one_mem' := paper51_freeOf_one S
  add_mem' := paper51_freeOf_add
  mul_mem' := paper51_freeOf_mul
  neg_mem' := paper51_freeOf_neg
  inv_mem' := fun _ hf => paper51_freeOf_inv hf

theorem paper51_freeOf_div {S : Set (Var k M)} {f g : K k M} (hf : FreeOf S f) (hg : FreeOf S g) :
    FreeOf S (f / g) := by
  exact (paper51_freeOfSubfield S).div_mem hf hg

theorem paper51_freeOf_sum {S : Set (Var k M)} {ι : Type*} (s : Finset ι) (f : ι → K k M)
    (hf : ∀ i ∈ s, FreeOf S (f i)) : FreeOf S (∑ i ∈ s, f i) := by
  exact (paper51_freeOfSubfield S).sum_mem hf

theorem paper51_freeOf_prod {S : Set (Var k M)} {ι : Type*} (s : Finset ι) (f : ι → K k M)
    (hf : ∀ i ∈ s, FreeOf S (f i)) : FreeOf S (∏ i ∈ s, f i) := by
  exact (paper51_freeOfSubfield S).prod_mem hf

theorem paper51_freeOf_mono {S T : Set (Var k M)} {f : K k M} (hST : S ⊆ T)
    (hf : FreeOf T f) : FreeOf S f := by
  exact fun a => Subfield.closure_mono (Set.image_mono (Set.compl_subset_compl.mpr hST)) (hf a)

end KServerConj
end PaperFile016

section PaperFile017
namespace KServerConj

theorem paper51_freeOf_det {k : ℕ} {M ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Set (Var k M)} (A : Matrix ι ι (K k M)) (hA : ∀ i j, FreeOf S (A i j)) :
    FreeOf S A.det := by
  let B : Matrix ι ι (paper51_freeOfSubfield S) := fun i j => ⟨A i j, hA i j⟩
  exact ((paper51_freeOfSubfield S).subtype.map_det B) ▸ B.det.property

end KServerConj
end PaperFile017

section PaperFile018
open scoped BigOperators

namespace KServerConj

variable {k : ℕ} {M : Type*}

theorem paper51_gamma_det_ne_zero (x : Fin k → M) (hx : Function.Injective x) :
    (Matrix.of fun i j : Fin k => varF (Sum.inl (i, x j))).det ≠ 0 := by
  let ρ : Fin k × Fin k → Var k M := fun ij => Sum.inl (ij.1, x ij.2)
  have hρ : Function.Injective ρ := fun a b h =>
    let h' : (a.1, x a.2) = (b.1, x b.2) := Sum.inl.inj h
    Prod.ext (congrArg (fun z : Fin k × M => z.1) h')
      (hx (congrArg (fun z : Fin k × M => z.2) h'))
  have hAI := (@paper51_varF_algebraicIndependent k M).comp ρ hρ
  have hne := (map_ne_zero_iff (MvPolynomial.aeval ((@varF k M) ∘ ρ))
    (algebraicIndependent_iff_injective_aeval.mp hAI)).mpr
      (Matrix.det_mvPolynomialX_ne_zero (m := Fin k) (R := ℚ))
  simpa [AlgHom.map_det, Matrix.mvPolynomialX, Matrix.map, ρ] using hne

theorem paper51_nu_gamma_det (x : Fin k → M) (hx : Function.Injective x) :
    nu ((Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j))).det) = 0 := by
  exact paper51_nu_det_C (Matrix.of fun i j : Fin k => varF (Sum.inl (i, x j)))
    (paper51_gamma_det_ne_zero x hx)

theorem paper51_weighted_gamma_det_valuation (w : M → ℝ) (x : Fin k → M)
    (hx : Function.Injective x) :
    nu ((Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j)) * zp (w (x j))).det) =
      ((∑ j, w (x j) : ℝ) : WithTop ℝ) := by
  have hfactor :
      (Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j)) * zp (w (x j))).det =
        (∏ j, (zp (w (x j)) : K k M)) *
          (Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j))).det := by
    simpa only [Matrix.of_apply, mul_comm] using
      Matrix.det_mul_row (fun j => (zp (w (x j)) : K k M))
        (Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j)))
  rw [hfactor, ← paper51_zp_sum Finset.univ (fun j => w (x j)), paper51_nu_mul, paper51_nu_zp,
    paper51_nu_gamma_det x hx, add_zero]

theorem paper51_initCols_colDet_valuation_of_uniform_dist [PseudoMetricSpace M]
    (s : Fin k → M) (w : M → ℝ) (hd : ∀ i y, dist (s i) y = w y)
    (x : Fin k → M) (hx : Function.Injective x) :
    nu (colDet (initCols s) x) = ((∑ j, w (x j) : ℝ) : WithTop ℝ) := by
  simpa only [colDet, initCols, hd] using paper51_weighted_gamma_det_valuation w x hx

theorem paper51_initCols_coalesced_valuation [PseudoMetricSpace M]
    (p : M) (x : Fin k → M) (hx : Function.Injective x) :
    nu (colDet (initCols (fun _ : Fin k => p)) x) =
      ((∑ j, dist p (x j) : ℝ) : WithTop ℝ) := by
  exact paper51_initCols_colDet_valuation_of_uniform_dist (fun _ => p) (dist p) (fun _ _ => rfl) x hx

theorem paper51_initCols_freeOf [PseudoMetricSpace M] (S : Set (Var k M))
    (hS : ∀ (i : Fin k) (y : M), Sum.inl (i, y) ∉ S)
    (s : Fin k → M) (y : M) (i : Fin k) : FreeOf S (initCols s y i) := by
  exact paper51_freeOf_mul (paper51_freeOf_coef S (Sum.inl (i, y)) (hS i y))
    (paper51_freeOf_zp S (dist (s i) y))

theorem paper51_colDet_freeOf (S : Set (Var k M)) (q : M → Fin k → K k M)
    (x : Fin k → M) (hq : ∀ i j, FreeOf S (q (x j) i)) : FreeOf S (colDet q x) := by
  exact paper51_freeOf_det (Matrix.of fun i j => q (x j) i) hq

theorem paper51_initCols_colDet_freeOf [PseudoMetricSpace M] (S : Set (Var k M))
    (hS : ∀ (i : Fin k) (y : M), Sum.inl (i, y) ∉ S)
    (s : Fin k → M) (x : Fin k → M) : FreeOf S (colDet (initCols s) x) := by
  exact paper51_colDet_freeOf S (initCols s) x (fun i j => paper51_initCols_freeOf S hS s (x j) i)

end KServerConj
end PaperFile018

section PaperFile019
open scoped BigOperators

namespace KServerConj

@[simp] theorem paper51_symProd_apply {R : Type*} [CommRing R] {k : ℕ}
    (a b : Fin k → R) (i j : Fin k) :
    symProd a b s(i, j) =
      if i = j then a i * b i else a i * b j + a j * b i := by
  rfl

theorem paper51_symProd_add_left {R : Type*} [CommRing R] {k : ℕ}
    (a b c : Fin k → R) : symProd (a + b) c = symProd a c + symProd b c := by
  funext p
  induction p using Sym2.ind with
  | _ i j =>
    simp only [Pi.add_apply, paper51_symProd_apply]
    split_ifs <;> ring

theorem paper51_symProd_smul_left {R : Type*} [CommRing R] {k : ℕ}
    (c : R) (a b : Fin k → R) : symProd (c • a) b = c • symProd a b := by
  funext p
  induction p using Sym2.ind with
  | _ i j =>
    simp only [Pi.smul_apply, paper51_symProd_apply, smul_eq_mul]
    split_ifs <;> ring

theorem paper51_symProd_add_right {R : Type*} [CommRing R] {k : ℕ}
    (a b c : Fin k → R) : symProd a (b + c) = symProd a b + symProd a c := by
  simpa only [symProd_comm] using paper51_symProd_add_left b c a

theorem paper51_symProd_smul_right {R : Type*} [CommRing R] {k : ℕ}
    (c : R) (a b : Fin k → R) : symProd a (c • b) = c • symProd a b := by
  simpa only [symProd_comm] using paper51_symProd_smul_left c b a

def paper51_symProdBilin {R : Type*} [CommRing R] {k : ℕ} :
    (Fin k → R) →ₗ[R] (Fin k → R) →ₗ[R] (Sym2 (Fin k) → R) where
  toFun a :=
    { toFun := symProd a
      map_add' := paper51_symProd_add_right a
      map_smul' c b := paper51_symProd_smul_right c a b }
  map_add' a b := LinearMap.ext fun c => paper51_symProd_add_left a b c
  map_smul' c a := LinearMap.ext fun b => paper51_symProd_smul_left c a b

@[simp] theorem paper51_symProd_single_single {R : Type*} [CommRing R] {k : ℕ}
    (i j : Fin k) :
    symProd (Pi.single i (1 : R)) (Pi.single j (1 : R)) = Pi.single s(i, j) 1 := by
  funext p
  induction p using Sym2.ind with
  | _ l m =>
    by_cases hlm : l = m <;> by_cases hli : l = i <;> by_cases hlj : l = j <;>
      by_cases hmi : m = i <;> by_cases hmj : m = j <;>
      simp_all [paper51_symProd_apply, Pi.single_apply]

@[simp] theorem paper51_sym2Mat_col {R : Type*} [CommRing R] {k : ℕ}
    (A : Matrix (Fin k) (Fin k) R) (i j : Fin k) :
    (sym2Mat A).col s(i, j) = symProd (A.col i) (A.col j) := rfl

theorem paper51_sym2Mat_mulVec_symProd {R : Type*} [CommRing R] {k : ℕ}
    (A : Matrix (Fin k) (Fin k) R) (a b : Fin k → R) :
    (sym2Mat A).mulVec (symProd a b) = symProd (A.mulVec a) (A.mulVec b) := by
  have h : (paper51_symProdBilin (R := R) (k := k)).compr₂ (sym2Mat A).mulVecLin =
      (paper51_symProdBilin (R := R) (k := k)).compl₁₂ A.mulVecLin A.mulVecLin := by
    apply (Pi.basisFun R (Fin k)).ext
    intro i
    apply (Pi.basisFun R (Fin k)).ext
    intro j
    simp only [Pi.basisFun_apply, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
    simp [paper51_symProdBilin, paper51_symProd_single_single]
  exact congrArg (fun f => f a b) h

@[simp] theorem paper51_sym2Mat_one {R : Type*} [CommRing R] (k : ℕ) :
    sym2Mat (1 : Matrix (Fin k) (Fin k) R) = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro c
  induction c using Sym2.ind with
  | _ i j =>
    simpa only [paper51_symProd_single_single, Matrix.one_mulVec] using
      paper51_sym2Mat_mulVec_symProd (1 : Matrix (Fin k) (Fin k) R)
        (Pi.single i 1) (Pi.single j 1)

theorem paper51_sym2Mat_mul {R : Type*} [CommRing R] {k : ℕ}
    (A B : Matrix (Fin k) (Fin k) R) :
    sym2Mat (A * B) = sym2Mat A * sym2Mat B := by
  apply Matrix.ext_of_mulVec_single
  intro c
  induction c using Sym2.ind with
  | _ i j =>
    simp only [← paper51_symProd_single_single, ← Matrix.mulVec_mulVec, paper51_sym2Mat_mulVec_symProd]

end KServerConj
end PaperFile019

section PaperFile020
open scoped BigOperators

namespace KServerConj

theorem paper51_det_eq_one_of_weight {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (A : Matrix ι ι R) (weight : ι → ℕ)
    (h : ∀ i j, weight j ≤ weight i → A i j = (1 : Matrix ι ι R) i j) :
    A.det = 1 := by
  have ht : A.BlockTriangular weight := by
    intro i j hij
    rw [h i j hij.le]
    exact Matrix.one_apply_ne (fun he => (ne_of_lt hij) (congrArg weight he).symm)
  have hb (n : ℕ) : A.toSquareBlock weight n = 1 := by
    ext i j
    change A i.val j.val = (1 : Matrix { a // weight a = n } { a // weight a = n } R) i j
    simpa [Matrix.one_apply, Subtype.ext_iff] using
      h i.val j.val (le_of_eq (j.property.trans i.property.symm))
  simpa [hb] using ht.det

def paper51_symCount {ι : Type*} [DecidableEq ι] (a : ι) : Sym2 ι → ℕ :=
  Sym2.lift ⟨fun i j => (if i = a then 1 else 0) + (if j = a then 1 else 0), by
    intro i j
    exact Nat.add_comm _ _⟩

@[simp] theorem paper51_symCount_mk {ι : Type*} [DecidableEq ι] (a i j : ι) :
    paper51_symCount a s(i, j) = (if i = a then 1 else 0) + (if j = a then 1 else 0) := rfl

theorem paper51_transvection_col {R : Type*} [CommRing R] {k : ℕ}
    (i j l : Fin k) (c : R) :
    (Matrix.transvection i j c).col l =
      Pi.single l 1 + if l = j then c • Pi.single i 1 else 0 := by
  ext r
  by_cases hl : l = j <;> by_cases hr : r = i <;>
    simp_all [Matrix.transvection, Matrix.col, Matrix.single, Matrix.one_apply,
      Pi.single_apply, eq_comm]

theorem paper51_sym2Mat_transvection_weight {R : Type*} [CommRing R] {k : ℕ}
    (i j : Fin k) (c : R) (hij : i ≠ j) (p q : Sym2 (Fin k))
    (hw : paper51_symCount j q ≤ paper51_symCount j p) :
    sym2Mat (Matrix.transvection i j c) p q = (1 : Matrix _ _ R) p q := by
  have hz (z : Sym2 (Fin k)) (hzp : paper51_symCount j z < paper51_symCount j p) :
      (Pi.single z (1 : R) : Sym2 (Fin k) → R) p = 0 :=
    Pi.single_eq_of_ne (M := fun _ : Sym2 (Fin k) => R)
      (fun he => hzp.ne (congrArg (paper51_symCount j) he).symm) (1 : R)
  induction q using Sym2.ind with
  | _ x y =>
    change symProd ((Matrix.transvection i j c).col x)
      ((Matrix.transvection i j c).col y) p = _
    by_cases hx : x = j <;> by_cases hy : y = j
    · have h0 := hz s(i, i) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      have h1 := hz s(i, j) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      simp only [paper51_transvection_col, hx, hy, ite_true, paper51_symProd_add_left,
        paper51_symProd_add_right, paper51_symProd_smul_left, paper51_symProd_smul_right, paper51_symProd_single_single,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        show s(j, i) = s(i, j) from Sym2.eq_swap, h0, h1, mul_zero, add_zero]
      simp [hx, hy, Matrix.one_apply, Pi.single_apply]
    · have h0 := hz s(i, y) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      simp only [paper51_transvection_col, hx, hy, ite_true, ite_false, add_zero,
        paper51_symProd_add_left, paper51_symProd_smul_left, paper51_symProd_single_single,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
      simp [hx, Matrix.one_apply, Pi.single_apply]
    · have h0 := hz s(x, i) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      simp only [paper51_transvection_col, hx, hy, ite_true, ite_false, add_zero,
        paper51_symProd_add_right, paper51_symProd_smul_right, paper51_symProd_single_single,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
      simp [hy, Matrix.one_apply, Pi.single_apply]
    · simp [paper51_transvection_col, hx, hy, paper51_symProd_single_single, Matrix.one_apply, Pi.single_apply]

theorem paper51_det_sym2Mat_transvection {R : Type*} [CommRing R] {k : ℕ}
    (i j : Fin k) (c : R) (hij : i ≠ j) :
    (sym2Mat (Matrix.transvection i j c)).det = 1 := by
  exact paper51_det_eq_one_of_weight _ (paper51_symCount j) (paper51_sym2Mat_transvection_weight i j c hij)

theorem paper51_sym2_mk_left_injective {ι : Type*} (i : ι) :
    Function.Injective (fun j : ι => s(i, j)) :=
  fun _ _ h => (Sym2.eq_iff.mp h).elim And.right (fun h => h.2.trans h.1)

theorem paper51_symCount_eq_zero_of_not_mem_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (p : Sym2 ι)
    (hp : p ∉ Finset.univ.image (fun j : ι => s(i, j))) : paper51_symCount i p = 0 := by
  induction p using Sym2.ind with
  | _ x y =>
    have hx : x ≠ i := fun h => hp (Finset.mem_image.mpr
      ⟨y, Finset.mem_univ _, congrArg (fun a => s(a, y)) h.symm⟩)
    have hy : y ≠ i := fun h => hp (Finset.mem_image.mpr
      ⟨x, Finset.mem_univ _, (Sym2.eq_swap : s(i, x) = s(x, i)).trans
        (congrArg (fun a => s(x, a)) h.symm)⟩)
    simp [paper51_symCount_mk, hx, hy]

theorem paper51_sum_symCount {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    ∑ p : Sym2 ι, paper51_symCount i p = Fintype.card ι + 1 := by
  have hs : (∑ p ∈ Finset.univ.image (fun j : ι => s(i, j)), paper51_symCount i p) =
      ∑ p : Sym2 ι, paper51_symCount i p :=
    Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => paper51_symCount_eq_zero_of_not_mem_image i p hp)
  rw [← hs, Finset.sum_image (paper51_sym2_mk_left_injective i).injOn]
  simp [paper51_symCount_mk, Finset.sum_add_distrib]

def paper51_symPairMul {ι R : Type*} [CommMonoid R] (d : ι → R) : Sym2 ι → R :=
  Sym2.lift ⟨fun i j => d i * d j, fun i j => mul_comm (d i) (d j)⟩

@[simp] theorem paper51_symPairMul_mk {ι R : Type*} [CommMonoid R]
    (d : ι → R) (i j : ι) : paper51_symPairMul d s(i, j) = d i * d j := rfl

theorem paper51_symPairMul_eq_prod {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid R]
    (d : ι → R) (p : Sym2 ι) :
    paper51_symPairMul d p = ∏ i : ι, d i ^ paper51_symCount i p := by
  induction p using Sym2.ind with
  | _ x y =>
    simp only [paper51_symPairMul_mk, paper51_symCount_mk, pow_add, Finset.prod_mul_distrib]
    simp only [Finset.prod_pow_boole, Finset.mem_univ, ite_true]

theorem paper51_prod_symPairMul {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid R]
    (d : ι → R) :
    (∏ p : Sym2 ι, paper51_symPairMul d p) = (∏ i : ι, d i) ^ (Fintype.card ι + 1) := by
  simp_rw [paper51_symPairMul_eq_prod]
  rw [Finset.prod_comm]
  simp_rw [Finset.prod_pow_eq_pow_sum, paper51_sum_symCount]
  exact Finset.prod_pow _ _ _

theorem paper51_sym2Mat_diagonal {R : Type*} [CommRing R] {k : ℕ} (d : Fin k → R) :
    sym2Mat (Matrix.diagonal d) = Matrix.diagonal (paper51_symPairMul d) := by
  have hs (i : Fin k) (a : R) :
      (Pi.single i a : Fin k → R) = a • Pi.single i 1 := by
    simpa only [smul_eq_mul, mul_one] using Pi.single_smul' i a (1 : R)
  apply Matrix.ext_of_mulVec_single
  intro c
  induction c using Sym2.ind with
  | _ i j =>
    simp only [Matrix.mulVec_single_one, paper51_sym2Mat_col, Matrix.col_diagonal, paper51_symPairMul_mk]
    rw [hs i (d i), hs j (d j), paper51_symProd_smul_left, paper51_symProd_smul_right,
      paper51_symProd_single_single, smul_smul]
    simp only [← Pi.single_smul', smul_eq_mul, mul_one]

theorem paper51_det_sym2Mat_diagonal {R : Type*} [CommRing R] {k : ℕ} (d : Fin k → R) :
    (sym2Mat (Matrix.diagonal d)).det = (Matrix.diagonal d).det ^ (k + 1) := by
  simp only [paper51_sym2Mat_diagonal, Matrix.det_diagonal, paper51_prod_symPairMul, Fintype.card_fin]

theorem paper51_det_sym2Mat {K : Type*} [Field K] {k : ℕ} (A : Matrix (Fin k) (Fin k) K) :
    (sym2Mat A).det = A.det ^ (k + 1) := by
  apply Matrix.diagonal_transvection_induction
    (fun M : Matrix (Fin k) (Fin k) K => (sym2Mat M).det = M.det ^ (k + 1)) A
  · exact fun d _ => paper51_det_sym2Mat_diagonal d
  · intro t
    simpa [Matrix.TransvectionStruct.toMatrix, t.hij] using
      paper51_det_sym2Mat_transvection t.i t.j t.c t.hij
  · intro M N hM hN
    rw [paper51_sym2Mat_mul, Matrix.det_mul, hM, hN, Matrix.det_mul, mul_pow]

end KServerConj
end PaperFile020

section PaperFile021
open scoped BigOperators

namespace DetValuationMilestone

theorem paper51_det_mul_rectangular_expansion
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (G : Matrix I J R) (C : Matrix J I R) :
    (G * C).det =
      ∑ f : I → J, (∏ i, C (f i) i) * (G.submatrix id f).det := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
    Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  simp only [Finset.prod_mul_distrib, Matrix.submatrix_apply, id_eq,
    mul_comm, mul_assoc]

theorem paper51_valuation_prod_nonneg
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

theorem paper51_valuation_det_mul_lower_bound
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (C : Matrix J I R) (μ : WithTop ℝ)
    (hG : ∀ f : I → J, μ ≤ ν (G.submatrix id f).det)
    (hC : ∀ j i, (0 : WithTop ℝ) ≤ ν (C j i)) :
    μ ≤ ν (G * C).det := by
  rw [paper51_det_mul_rectangular_expansion]
  apply paper51_valuation_sum_lower_bound ν hzero hadd
  intro f _
  have hcoeff : (0 : WithTop ℝ) ≤ ν (∏ i, C (f i) i) :=
    paper51_valuation_prod_nonneg ν hone hmul Finset.univ (fun i => C (f i) i)
      (fun i _ => hC (f i) i)
  simpa only [hmul, zero_add] using add_le_add hcoeff (hG f)

theorem paper51_tupleMinorVal_mono_of_nonneg_coeff
    {I J K R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (C : Matrix J K R)
    (hC : ∀ j k, (0 : WithTop ℝ) ≤ ν (C j k)) :
    paper51_tupleMinorVal ν G ≤ paper51_tupleMinorVal ν (G * C) := by
  classical
  refine Finset.le_inf (fun e _ => ?_)
  change paper51_tupleMinorVal ν G ≤ ν (G * (C.submatrix id e)).det
  exact paper51_valuation_det_mul_lower_bound ν hzero hone hmul hadd G (C.submatrix id e)
    (paper51_tupleMinorVal ν G)
    (fun f => Finset.inf_le (f := fun x : I → J => ν (G.submatrix id x).det)
      (Finset.mem_univ f))
    (fun j i => hC j (e i))

theorem paper51_embeddingMinorVal_mono_of_nonneg_coeff
    {I J K R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (C : Matrix J K R)
    (hC : ∀ j k, (0 : WithTop ℝ) ≤ ν (C j k)) :
    paper51_embeddingMinorVal ν G ≤ paper51_embeddingMinorVal ν (G * C) := by
  simpa only [paper51_tupleMinorVal_eq_embeddingMinorVal ν hzero] using
    paper51_tupleMinorVal_mono_of_nonneg_coeff ν hzero hone hmul hadd G C hC

theorem paper51_embeddingMinorVal_mono_of_column_combinations
    {I J K R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (F : Matrix I K R)
    (hF : ∀ k, ∃ c : J → R,
      (∀ j, (0 : WithTop ℝ) ≤ ν (c j)) ∧ ∀ i, F i k = ∑ j, G i j * c j) :
    paper51_embeddingMinorVal ν G ≤ paper51_embeddingMinorVal ν F := by
  classical
  let C : Matrix J K R := Matrix.of fun j k => (hF k).choose j
  have hGC : G * C = F :=
    Matrix.ext (fun i k => by
      simpa only [Matrix.mul_apply, C, Matrix.of_apply] using ((hF k).choose_spec.2 i).symm)
  simpa only [hGC] using
    paper51_embeddingMinorVal_mono_of_nonneg_coeff ν hzero hone hmul hadd G C
      (fun j k => (hF k).choose_spec.1 j)

end DetValuationMilestone
end PaperFile021

section PaperFile022
open scoped BigOperators

namespace DetValuationMilestone

theorem paper51_valuation_det_nonneg
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

theorem paper51_zero_le_tupleMinorVal_of_entries
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hneg : ∀ x, ν (-x) = ν x)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (hG : ∀ i j, (0 : WithTop ℝ) ≤ ν (G i j)) :
    (0 : WithTop ℝ) ≤ paper51_tupleMinorVal ν G := by
  classical
  exact Finset.le_inf (fun e _ => paper51_valuation_det_nonneg ν hzero hone hneg hmul hadd
    (G.submatrix id e) (fun i j => hG i (e j)))

theorem paper51_zero_le_embeddingMinorVal_of_entries
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hneg : ∀ x, ν (-x) = ν x)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (hG : ∀ i j, (0 : WithTop ℝ) ≤ ν (G i j)) :
    (0 : WithTop ℝ) ≤ paper51_embeddingMinorVal ν G := by
  simpa only [paper51_tupleMinorVal_eq_embeddingMinorVal ν hzero] using
    paper51_zero_le_tupleMinorVal_of_entries ν hzero hone hneg hmul hadd G hG

end DetValuationMilestone
end PaperFile022

section PaperFile023
namespace KServerConj

theorem paper51_minorVal_le_tuple {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (x : I → J) :
    minorVal G ≤ HahnSeries.addVal ℝ F (G.submatrix id x).det := by
  simpa only [paper51_minorVal_eq_embeddingMinorVal] using
    DetValuationMilestone.paper51_embeddingMinorVal_le_tuple (HahnSeries.addVal ℝ F)
      (AddValuation.map_zero _) G x

theorem paper51_exists_minorVal_minimizer {F I J : Type*}
    [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (a : ℝ)
    (ha : minorVal G = (a : WithTop ℝ)) :
    ∃ x : I ↪ J, HahnSeries.addVal ℝ F (G.submatrix id x).det = (a : WithTop ℝ) := by
  classical
  have hh : DetValuationMilestone.paper51_embeddingMinorVal (HahnSeries.addVal ℝ F) G =
      (a : WithTop ℝ) := (paper51_minorVal_eq_embeddingMinorVal G).symm.trans ha
  unfold DetValuationMilestone.paper51_embeddingMinorVal at hh
  obtain ⟨x, _, hx⟩ := (Finset.inf_le_iff (show (a : WithTop ℝ) < ⊤ by simp)).mp hh.le
  exact ⟨x, le_antisymm hx (hh.symm.trans_le (Finset.inf_le (Finset.mem_univ x)))⟩

end KServerConj
end PaperFile023

section PaperFile024
open scoped BigOperators

namespace KServerConj

theorem paper51_single_add_one {F : Type*} [Field F] (a b : ℝ) :
    (HahnSeries.single (a + b) (1 : F) : HahnSeries ℝ F) =
      HahnSeries.single a (1 : F) * HahnSeries.single b (1 : F) := by
  simpa only [one_mul] using
    (HahnSeries.single_mul_single (a := a) (b := b) (r := (1 : F)) (s := 1)).symm

theorem paper51_single_sum_one {F ι : Type*} [Field F] (s : Finset ι) (a : ι → ℝ) :
    (HahnSeries.single (∑ i ∈ s, a i) (1 : F) : HahnSeries ℝ F) =
      ∏ i ∈ s, HahnSeries.single (a i) (1 : F) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, HahnSeries.single_zero_one]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, paper51_single_add_one, ih]

theorem paper51_quadraticMatrix_selected_det {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) :
    ((paper51_quadraticMatrix q).submatrix id (Sym2.map x)).det =
      HahnSeries.single (∑ c, paper51_negPairDist x c) (1 : F) *
        (Matrix.of (fun i j => q (x j) i)).det ^ (k + 1) := by
  rw [paper51_quadraticMatrix_submatrix]
  rw [Matrix.det_mul_row (fun c => HahnSeries.single (paper51_negPairDist x c) (1 : F))
    (sym2Mat (Matrix.of (fun i j => q (x j) i)))]
  rw [paper51_det_sym2Mat, ← paper51_single_sum_one]

theorem paper51_quadraticMatrix_selected_valuation {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) (δ : ℝ)
    (hD : HahnSeries.addVal ℝ F (Matrix.of (fun i j => q (x j) i)).det =
      (δ : WithTop ℝ)) :
    HahnSeries.addVal ℝ F ((paper51_quadraticMatrix q).submatrix id (Sym2.map x)).det =
      ((∑ c, paper51_negPairDist x c) + ((k : ℝ) + 1) * δ : ℝ) := by
  rw [paper51_quadraticMatrix_selected_det, AddValuation.map_mul, AddValuation.map_pow, hD]
  rw [show HahnSeries.addVal ℝ F
      (HahnSeries.single (∑ c, paper51_negPairDist x c) (1 : F)) =
      (((∑ c, paper51_negPairDist x c) : ℝ) : WithTop ℝ) from HahnSeries.orderTop_single one_ne_zero]
  simp only [← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]

theorem paper51_negPairDist_nonpos {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (x : Fin k → M) (c : Sym2 (Fin k)) : paper51_negPairDist x c ≤ 0 := by
  induction c using Sym2.ind with
  | _ i j => exact neg_nonpos.mpr dist_nonneg

theorem paper51_minorVal_quadratic_le {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) (δ : ℝ)
    (hD : HahnSeries.addVal ℝ F (Matrix.of (fun i j => q (x j) i)).det =
      (δ : WithTop ℝ)) :
    minorVal (paper51_quadraticMatrix q) ≤ ((((k : ℝ) + 1) * δ : ℝ) : WithTop ℝ) := by
  exact (paper51_minorVal_le_tuple (paper51_quadraticMatrix q) (Sym2.map x)).trans
    ((paper51_quadraticMatrix_selected_valuation q x δ hD).le.trans
      (WithTop.coe_le_coe.mpr (add_le_of_nonpos_left
        (Finset.sum_nonpos fun c _ => paper51_negPairDist_nonpos x c))))

end KServerConj
end PaperFile024

section PaperFile025
namespace KServerConj

def paper51_sym2FinSuccEmbed (n : ℕ) :
    Fin (n + 1) ⊕ Sym2 (Fin n) → Sym2 (Fin (n + 1))
  | Sum.inl i => s(0, i)
  | Sum.inr p => p.map Fin.succ

theorem paper51_sym2FinSucc_top_ne_bottom (n : ℕ) (i : Fin (n + 1)) (p : Sym2 (Fin n)) :
    s((0 : Fin (n + 1)), i) ≠ p.map Fin.succ := by
  induction p using Sym2.ind with
  | _ a b =>
    simp [(Fin.succ_ne_zero a).symm, (Fin.succ_ne_zero b).symm]

theorem paper51_sym2FinSuccEmbed_injective (n : ℕ) : Function.Injective (paper51_sym2FinSuccEmbed n) := by
  intro x y h
  rcases x with i | p <;> rcases y with j | q
  · exact congrArg Sum.inl ((Sym2.eq_iff.mp h).elim And.right (fun h => h.2.trans h.1))
  · exact False.elim (paper51_sym2FinSucc_top_ne_bottom n i q h)
  · exact False.elim (paper51_sym2FinSucc_top_ne_bottom n j p h.symm)
  · exact congrArg Sum.inr (Sym2.map.injective (Fin.succ_injective n) h)

theorem paper51_sym2FinSuccEmbed_surjective (n : ℕ) : Function.Surjective (paper51_sym2FinSuccEmbed n) := by
  intro p
  induction p using Sym2.ind with
  | _ i j =>
    cases i using Fin.cases with
    | zero => exact ⟨Sum.inl j, rfl⟩
    | succ i =>
      cases j using Fin.cases with
      | zero => exact ⟨Sum.inl i.succ, Sym2.eq_swap⟩
      | succ j => exact ⟨Sum.inr s(i, j), rfl⟩

noncomputable def paper51_sym2FinSuccEquiv (n : ℕ) :
    Sym2 (Fin (n + 1)) ≃ Fin (n + 1) ⊕ Sym2 (Fin n) :=
  (Equiv.ofBijective (paper51_sym2FinSuccEmbed n)
    ⟨paper51_sym2FinSuccEmbed_injective n, paper51_sym2FinSuccEmbed_surjective n⟩).symm

@[simp] theorem paper51_sym2FinSuccEquiv_symm_inl (n : ℕ) (i : Fin (n + 1)) :
    (paper51_sym2FinSuccEquiv n).symm (Sum.inl i) = s(0, i) := rfl

@[simp] theorem paper51_sym2FinSuccEquiv_symm_inr (n : ℕ) (p : Sym2 (Fin n)) :
    (paper51_sym2FinSuccEquiv n).symm (Sum.inr p) = p.map Fin.succ := rfl

@[simp] theorem paper51_sym2FinSuccEquiv_mk_zero (n : ℕ) (i : Fin (n + 1)) :
    paper51_sym2FinSuccEquiv n s(0, i) = Sum.inl i := by
  simpa only [paper51_sym2FinSuccEquiv_symm_inl] using
    (paper51_sym2FinSuccEquiv n).apply_symm_apply (Sum.inl i)

@[simp] theorem paper51_sym2FinSuccEquiv_map_succ (n : ℕ) (p : Sym2 (Fin n)) :
    paper51_sym2FinSuccEquiv n (p.map Fin.succ) = Sum.inr p := by
  simpa only [paper51_sym2FinSuccEquiv_symm_inr] using
    (paper51_sym2FinSuccEquiv n).apply_symm_apply (Sum.inr p)

theorem paper51_symProd_split_top {R : Type*} [CommRing R] {n : ℕ}
    (a b : Fin (n + 1) → R) (i : Fin (n + 1)) :
    symProd a b ((paper51_sym2FinSuccEquiv n).symm (Sum.inl i)) =
      if i = 0 then a 0 * b 0 else a 0 * b i + a i * b 0 := by
  simp [paper51_symProd_apply, eq_comm]

@[simp] theorem paper51_symProd_split_top_zero {R : Type*} [CommRing R] {n : ℕ}
    (a b : Fin (n + 1) → R) :
    symProd a b ((paper51_sym2FinSuccEquiv n).symm (Sum.inl 0)) = a 0 * b 0 := by
  simp [paper51_symProd_apply]

theorem paper51_symProd_split_top_succ {R : Type*} [CommRing R] {n : ℕ}
    (a b : Fin (n + 1) → R) (i : Fin n) :
    symProd a b ((paper51_sym2FinSuccEquiv n).symm (Sum.inl i.succ)) =
      a 0 * b i.succ + a i.succ * b 0 := by
  simp [paper51_symProd_apply, (Fin.succ_ne_zero i).symm]

theorem paper51_symProd_split_bottom {R : Type*} [CommRing R] {n : ℕ}
    (a b : Fin (n + 1) → R) (p : Sym2 (Fin n)) :
    symProd a b ((paper51_sym2FinSuccEquiv n).symm (Sum.inr p)) =
      symProd (fun i => a i.succ) (fun i => b i.succ) p := by
  induction p using Sym2.ind with
  | _ i j =>
    simp only [paper51_sym2FinSuccEquiv_symm_inr, Sym2.map_mk, paper51_symProd_apply,
      (Fin.succ_injective n).eq_iff]

theorem paper51_symProd_e0_split_top {R : Type*} [CommRing R] {n : ℕ}
    (h : Fin (n + 1) → R) (i : Fin (n + 1)) :
    symProd (Pi.single 0 1) h ((paper51_sym2FinSuccEquiv n).symm (Sum.inl i)) = h i := by
  by_cases hi : i = 0 <;> simp [hi, eq_comm]

theorem paper51_symProd_e0_split_bottom {R : Type*} [CommRing R] {n : ℕ}
    (h : Fin (n + 1) → R) (p : Sym2 (Fin n)) :
    symProd (Pi.single 0 1) h ((paper51_sym2FinSuccEquiv n).symm (Sum.inr p)) = 0 := by
  induction p using Sym2.ind with
  | _ i j =>
    simp [paper51_symProd_apply]

theorem paper51_symProd_e0_split {R : Type*} [CommRing R] {n : ℕ} (h : Fin (n + 1) → R) :
    (fun p : Fin (n + 1) ⊕ Sym2 (Fin n) =>
      symProd (Pi.single 0 1) h ((paper51_sym2FinSuccEquiv n).symm p)) =
      Sum.elim h (fun _ => 0) := by
  exact funext (Sum.rec (paper51_symProd_e0_split_top h) (paper51_symProd_e0_split_bottom h))

end KServerConj
end PaperFile025

section PaperFile027
open scoped BigOperators

namespace KServerConj

theorem paper51_negPairDist_map_succ {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (x : Fin (k + 1) → M) (p : Sym2 (Fin k)) :
    paper51_negPairDist x (p.map Fin.succ) = paper51_negPairDist (fun i => x i.succ) p := by
  induction p using Sym2.ind with
  | _ i j => rfl

theorem paper51_twice_sum_negPairDist {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (x : Fin k → M) :
    2 * (∑ p, paper51_negPairDist x p) = -(∑ i, ∑ j, dist (x i) (x j)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : (∑ p, paper51_negPairDist x p) =
        (∑ i : Fin (k + 1), -dist (x 0) (x i)) +
          ∑ p, paper51_negPairDist (fun i : Fin k => x i.succ) p := by
      calc
        _ = ∑ p : Fin (k + 1) ⊕ Sym2 (Fin k),
            paper51_negPairDist x ((paper51_sym2FinSuccEquiv k).symm p) :=
          Fintype.sum_equiv (paper51_sym2FinSuccEquiv k) _ _ (fun p => by simp)
        _ = _ := by
          simp only [Fintype.sum_sum_type, paper51_sym2FinSuccEquiv_symm_inl,
            paper51_sym2FinSuccEquiv_symm_inr, paper51_negPairDist_map_succ]
          rfl
    have hfull : (∑ i, ∑ j, dist (x i) (x j)) =
        2 * (∑ i : Fin k, dist (x 0) (x i.succ)) +
          ∑ i : Fin k, ∑ j : Fin k, dist (x i.succ) (x j.succ) := by
      simp only [Fin.sum_univ_succ, dist_self, zero_add, Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun i _ => dist_comm (x i.succ) (x 0))]
      ring
    simp only [Fin.sum_univ_succ, dist_self, zero_add,
      Finset.sum_neg_distrib] at hsplit
    have htail := ih (fun i => x i.succ)
    linarith only [hsplit, hfull, htail]

theorem paper51_sum_offDiag_dist {M : Type*} [PseudoMetricSpace M] (X : Finset M) :
    (∑ p ∈ X.offDiag, dist p.1 p.2) = ∑ i ∈ X, ∑ j ∈ X, dist i j := by
  classical
  calc
    _ = ∑ p ∈ X ×ˢ X, dist p.1 p.2 := by
      apply Finset.sum_subset
      · intro p hp
        exact Finset.mem_product.mpr
          ⟨(Finset.mem_offDiag.mp hp).1, (Finset.mem_offDiag.mp hp).2.1⟩
      · intro p hp hn
        have heq : p.1 = p.2 := by
          by_contra h
          exact hn (Finset.mem_offDiag.mpr
            ⟨(Finset.mem_product.mp hp).1, (Finset.mem_product.mp hp).2, h⟩)
        simp only [heq, dist_self]
    _ = _ := Finset.sum_product X X (fun p => dist p.1 p.2)

theorem paper51_sum_negPairDist_eq_neg_cl {k : ℕ} {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (x : Fin k → M) (hx : Function.Injective x) :
    (∑ p, paper51_negPairDist x p) = -cl (Finset.univ.image x) := by
  classical
  unfold cl
  rw [paper51_sum_offDiag_dist]
  simp only [Finset.sum_image (fun i _ j _ h => hx h)]
  have h := paper51_twice_sum_negPairDist x
  linarith only [h]

theorem paper51_minorVal_quadratic_le_clique {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) (hx : Function.Injective x)
    (δ : ℝ) (hD : HahnSeries.addVal ℝ F (Matrix.of (fun i j => q (x j) i)).det =
      (δ : WithTop ℝ)) :
    minorVal (paper51_quadraticMatrix q) ≤
      ((((k : ℝ) + 1) * δ - cl (Finset.univ.image x) : ℝ) : WithTop ℝ) := by
  have h := paper51_quadraticMatrix_selected_valuation q x δ hD
  rw [paper51_sum_negPairDist_eq_neg_cl x hx] at h
  simpa only [sub_eq_add_neg, add_comm] using
    (paper51_minorVal_le_tuple (paper51_quadraticMatrix q) (Sym2.map x)).trans_eq h

end KServerConj
end PaperFile027

section PaperFile028
namespace KServerConj

theorem paper51_exists_injective_enumeration {M : Type*} [DecidableEq M] {k : ℕ}
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
end PaperFile028

section PaperFile029
namespace KServerConj

theorem paper51_terminal_bound_of_representation {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin k → K k M) (w : Finset M → ℝ)
    (hrep : ∀ x : Fin k → M, Function.Injective x →
      nu (colDet q x) = (w (Finset.univ.image x) : WithTop ℝ))
    (X : Finset M) (hX : X.card = k) :
    Psi q ≤ ((((k : ℝ) + 1) * w X - cl X : ℝ) : WithTop ℝ) := by
  obtain ⟨x, hx, himage⟩ := paper51_exists_injective_enumeration X hX
  change minorVal (paper51_quadraticMatrix q) ≤ _
  simpa only [himage] using
    paper51_minorVal_quadratic_le_clique q x hx (w (Finset.univ.image x)) (hrep x hx)

end KServerConj
end PaperFile029

open KServerConj

theorem solution {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M] {m : ℕ}
    (hm : 1 ≤ m) (s : Fin (m + 1) → M) (hs : Function.Injective s) (r : ℕ → M) (T : ℕ)
    (q qn : ℕ → M → Fin (m + 1) → K (m + 1) M) (hrun : IsRun s r T q qn) :
    ∀ t, t ≤ T → ∀ X : Finset M, X.card = m + 1 →
      Psi (q t) ≤
        ((((m + 2 : ℕ) : ℝ) * workFn (m + 1) (Finset.univ.image s) r t X - cl X : ℝ) : WithTop ℝ) := by
  intro t ht X hX
  have h := paper51_terminal_bound_of_representation (q t)
    (fun Y => workFn (m + 1) (Finset.univ.image s) r t Y)
    (fun x hx => (theorem_2_4 hm s hs r T).2 q qn hrun t ht x hx) X hX
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc,
    one_add_one_eq_two] using h

#print axioms solution
