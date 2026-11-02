-- Prove2me | solution 2 for Grunbaum2003.neighborly_cubical_realization
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:20:20.771162+00:00
-- url     : https://prove2.me/submissions/ba53db7d-4f83-47df-b16d-4ee9252d94c4

import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FunProp
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.Separation.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Convex.Exposed
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Tactic.Linarith
import Mathlib.Data.Set.Image
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Algebra.ContinuousAffineEquiv
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_Grunbaum2003_IsDPolytope
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.Order.LeftRight
import Definitions.Def_Grunbaum2003_standardCube
import Mathlib.Tactic.Ring
import Definitions.Def_Grunbaum2003_PolytopeFace
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Definitions.Def_Grunbaum2003_IsCubicalDPolytope
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Definitions.Def_Grunbaum2003_SkeletonFace

-- Local ingredient: PositiveDependenceOpen

set_option autoImplicit false
open scoped BigOperators Topology Matrix

namespace Grunbaum2003

                                                                           
                                                                            
                                                                            
                                                                      
theorem positive_dependence_persists {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (a₀ : ι → Fin m → ℝ) (weight : ι → ℝ)
    (hWeight : ∀ i, 0 < weight i)
    (hSum : (∑ i, weight i • a₀ i) = 0)
    (u : Fin m ↪ ι)
    (hDet : Matrix.det (fun k j : Fin m => a₀ (u j) k) ≠ 0) :
    ∀ᶠ a in 𝓝 a₀, ∃ w : ι → ℝ,
      (∀ i, 0 < w i) ∧ (∑ i, w i • a i) = 0 ∧
        Matrix.det (fun k j : Fin m => a (u j) k) ≠ 0 := by
  classical
  let A : (ι → Fin m → ℝ) → Matrix (Fin m) (Fin m) ℝ := fun a k j => a (u j) k
  let rhs : (ι → Fin m → ℝ) → (Fin m → ℝ) := fun a => -∑ i, weight i • a i
  let c : (ι → Fin m → ℝ) → (Fin m → ℝ) := fun a => (A a)⁻¹ *ᵥ rhs a
  let w : (ι → Fin m → ℝ) → ι → ℝ :=
    fun a i => weight i + ∑ j : Fin m, if u j = i then c a j else 0
  have hA : Continuous A := by unfold A; fun_prop
  have hRhs : Continuous rhs := by unfold rhs; fun_prop
  have hInv : ContinuousAt (fun a => (A a)⁻¹) a₀ := by
    apply (continuousAt_matrix_inv (A a₀) ?_).comp hA.continuousAt
    have hRealInv : (Ring.inverse : ℝ → ℝ) = Inv.inv :=
      funext (fun x => Ring.inverse_eq_inv x)
    rw [hRealInv]
    exact continuousAt_inv₀ hDet
  have hc : ContinuousAt c a₀ := by
    unfold c
    fun_prop
  have hcZero : c a₀ = 0 := by
    simp only [c, rhs, hSum, neg_zero, Matrix.mulVec_zero]
  have hwZero (i : ι) : w a₀ i = weight i := by
    simp only [w, hcZero, Pi.zero_apply, ite_self, Finset.sum_const_zero, add_zero]
  have hw : ∀ i : ι, ContinuousAt (fun a => w a i) a₀ := by
    intro i
    unfold w
    apply continuousAt_const.add
    apply tendsto_finsetSum Finset.univ
    intro j _
    by_cases hj : u j = i
    · simp only [if_pos hj]
      exact (continuous_apply j).continuousAt.comp hc
    · simp only [if_neg hj]
      exact continuousAt_const
  have hPos : ∀ᶠ a in 𝓝 a₀, ∀ i, 0 < w a i := by
    apply Filter.eventually_all.mpr
    intro i
    have hi : (0 : ℝ) < w a₀ i := by rw [hwZero]; exact hWeight i
    exact (hw i).tendsto.eventually (Ioi_mem_nhds hi)
  have hMinor : ∀ᶠ a in 𝓝 a₀, (A a).det ≠ 0 :=
    hA.matrix_det.continuousAt.eventually_ne hDet
  filter_upwards [hPos, hMinor] with a hPosA hMinorA
  refine ⟨w a, hPosA, ?_, hMinorA⟩
  have hcEq : A a *ᵥ c a = rhs a := by
    change A a *ᵥ ((A a)⁻¹ *ᵥ rhs a) = rhs a
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hMinorA),
      Matrix.one_mulVec]
  have hVec : (∑ j : Fin m, c a j • a (u j)) = rhs a := by
    ext k
    have h := congrFun hcEq k
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
      dotProduct, A, mul_comm] using h
  have hCorrection :
      (∑ i, (∑ j : Fin m, if u j = i then c a j else 0) • a i) =
        ∑ j : Fin m, c a j • a (u j) := by
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp only [ite_smul, zero_smul]
    simp [eq_comm]
  calc
    (∑ i, w a i • a i) =
        (∑ i, weight i • a i) +
          (∑ i, (∑ j : Fin m, if u j = i then c a j else 0) • a i) := by
      simp only [w, add_smul, Finset.sum_add_distrib]
    _ = (∑ i, weight i • a i) + rhs a := by rw [hCorrection, hVec]
    _ = 0 := add_neg_cancel _

end Grunbaum2003


-- Local ingredient: PositiveSpanningNeighborhood

set_option autoImplicit false
open scoped BigOperators Topology
open Module

namespace Grunbaum2003

                                                                            
theorem exists_regular_minor_of_span_eq_top {ι : Type*} [Fintype ι] {m : ℕ}
    (a : ι → Fin m → ℝ)
    (hSpan : Submodule.span ℝ (Set.range a) = ⊤) :
    ∃ u : Fin m ↪ ι,
      Matrix.det (fun k j : Fin m => a (u j) k) ≠ 0 := by
  classical
  obtain ⟨κ, v, hv, hSp, hLI⟩ := exists_linearIndependent' ℝ a
  let : Fintype κ := Fintype.ofInjective v hv
  have hTop : Submodule.span ℝ (Set.range (a ∘ v)) = ⊤ := hSp.trans hSpan
  let b : Basis κ ℝ (Fin m → ℝ) := Basis.mk hLI hTop.ge
  have hCard : Fintype.card κ = m := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fin_fun]
  let e : Fin m ≃ κ := Fintype.equivOfCardEq (by simp only [Fintype.card_fin, hCard])
  let u : Fin m ↪ ι := ⟨v ∘ e, hv.comp e.injective⟩
  have hCols : LinearIndependent ℝ (fun j : Fin m => a (u j)) :=
    hLI.comp e e.injective
  let M : Matrix (Fin m) (Fin m) ℝ := fun k j => a (u j) k
  have hUnit : IsUnit M :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hCols
  exact ⟨u, isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det M).mp hUnit)⟩

private theorem span_eq_top_of_regular_minor {ι : Type*} {m : ℕ}
    (a : ι → Fin m → ℝ) (u : Fin m ↪ ι)
    (hDet : Matrix.det (fun k j : Fin m => a (u j) k) ≠ 0) :
    Submodule.span ℝ (Set.range a) = ⊤ := by
  have hLI : LinearIndependent ℝ (fun j : Fin m => a (u j)) :=
    Matrix.linearIndependent_cols_of_det_ne_zero hDet
  have hSp : Submodule.span ℝ (Set.range (fun j : Fin m => a (u j))) = ⊤ :=
    hLI.span_eq_top_of_card_eq_finrank' (by simp)
  apply top_unique
  rw [← hSp]
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨u j, rfl⟩

                                                                           
                                                                     
theorem isOpen_positive_spanning_configurations {ι : Type*} [Fintype ι] {m : ℕ} :
    IsOpen {a : ι → Fin m → ℝ |
      (∃ weight : ι → ℝ, (∀ i, 0 < weight i) ∧ (∑ i, weight i • a i) = 0) ∧
        Submodule.span ℝ (Set.range a) = ⊤} := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  rintro a₀ ⟨⟨weight, hWeight, hSum⟩, hSpan⟩
  obtain ⟨u, hDet⟩ := exists_regular_minor_of_span_eq_top a₀ hSpan
  filter_upwards [positive_dependence_persists a₀ weight hWeight hSum u hDet]
    with a ha
  obtain ⟨w, hw, hSumW, hDetW⟩ := ha
  exact ⟨⟨w, hw, hSumW⟩, span_eq_top_of_regular_minor a u hDetW⟩

                                                                          
                                          
theorem exists_positive_spanning_neighborhood {ι : Type*} [Fintype ι] {m : ℕ}
    (a₀ : ι → Fin m → ℝ)
    (hPos : ∃ weight : ι → ℝ,
      (∀ i, 0 < weight i) ∧ (∑ i, weight i • a₀ i) = 0)
    (hSpan : Submodule.span ℝ (Set.range a₀) = ⊤) :
    ∃ U : Set (ι → Fin m → ℝ), IsOpen U ∧ a₀ ∈ U ∧
      ∀ a ∈ U,
        (∃ weight : ι → ℝ, (∀ i, 0 < weight i) ∧ (∑ i, weight i • a i) = 0) ∧
          Submodule.span ℝ (Set.range a) = ⊤ := by
  exact ⟨_, isOpen_positive_spanning_configurations, ⟨hPos, hSpan⟩, fun _ h => h⟩

end Grunbaum2003


-- Local ingredient: ShiftedGaleLimit

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

private theorem sum_subtype_eq_sum_ite {ι V : Type*} [Fintype ι]
    [AddCommMonoid V] (p : ι → Prop) [DecidablePred p] (f : ι → V) :
    (∑ i : {i // p i}, f i.val) = ∑ i, if p i then f i else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter p) (fun i => by simp) f,
    Finset.sum_filter]

                                                                             
                                                                         
                                                                           
theorem shift_zero_complement_positive_spanning {N m : ℕ}
    (G : Fin N → Fin m → ℝ) (J : Finset (Fin (N + 1)))
    (hPos : ∃ weight : {i : Fin N // i.succ ∉ J} → ℝ,
      (∀ i, 0 < weight i) ∧ (∑ i, weight i • G i.val) = 0)
    (hSpan : Submodule.span ℝ (Set.range (fun i : {i : Fin N // i.succ ∉ J} =>
      G i.val)) = ⊤) :
    (∃ weight : {i : Fin (N + 1) // i ∉ J} → ℝ,
      (∀ i, 0 < weight i) ∧
        (∑ i, weight i • Fin.cons (α := fun _ : Fin (N + 1) => Fin m → ℝ) 0 G i.val) = 0) ∧
      Submodule.span ℝ (Set.range (fun i : {i : Fin (N + 1) // i ∉ J} =>
        Fin.cons (α := fun _ : Fin (N + 1) => Fin m → ℝ) 0 G i.val)) = ⊤ := by
  classical
  obtain ⟨w, hw, hSum⟩ := hPos
  let w' : Fin N → ℝ := fun i => if hi : i.succ ∉ J then w ⟨i, hi⟩ else 0
  let W : Fin (N + 1) → ℝ := Fin.cons (α := fun _ : Fin (N + 1) => ℝ) 1 w'
  have hExtended : (∑ i : Fin N, w' i • G i) = 0 := by
    calc
      (∑ i : Fin N, w' i • G i) =
          ∑ i : Fin N, if i.succ ∉ J then w' i • G i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i.succ ∉ J <;> simp [w', hi]
      _ = ∑ i : {i : Fin N // i.succ ∉ J}, w' i.val • G i.val :=
        (sum_subtype_eq_sum_ite (fun i : Fin N => i.succ ∉ J) _).symm
      _ = 0 := by
        convert hSum using 1
        apply Finset.sum_congr rfl
        intro i _
        simp only [w', dif_pos i.property]
  refine ⟨⟨fun i => W i.val, ?_, ?_⟩, ?_⟩
  · rintro ⟨i, hi⟩
    cases i using Fin.cases with
    | zero => norm_num [W]
    | succ i =>
      simpa only [W, Fin.cons_succ, w', dif_pos hi] using hw ⟨i, hi⟩
  · rw [sum_subtype_eq_sum_ite (fun i : Fin (N + 1) => i ∉ J)
      (fun i => W i • Fin.cons (α := fun _ : Fin (N + 1) => Fin m → ℝ) 0 G i), Fin.sum_univ_succ]
    simp only [W, Fin.cons_zero, smul_zero, ite_self, zero_add, Fin.cons_succ]
    calc
      (∑ i : Fin N, if i.succ ∉ J then w' i • G i else 0) =
          ∑ i : Fin N, w' i • G i := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i.succ ∉ J <;> simp [w', hi]
      _ = 0 := hExtended
  · apply top_unique
    rw [← hSpan]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i.val.succ, i.property⟩, rfl⟩

                                                                            
                                                
theorem shifted_normalized_basis_row {N m : ℕ} (hm : m ≤ N)
    (G : Fin N → Fin m → ℝ)
    (hG : ∀ i j : Fin m, G (Fin.castLE hm i) j = if i = j then 1 else 0)
    (i j : Fin m) :
    Fin.cons (α := fun _ : Fin (N + 1) => Fin m → ℝ) 0 G (Fin.castLE hm i).succ j =
      if i = j then 1 else 0 := by
  simpa only [Fin.cons_succ] using hG i j

                                                                          
                                                                     
theorem shifted_normalized_triangular_rows_at_zero {N m : ℕ} (hm : m ≤ N)
    (G : Fin N → Fin m → ℝ)
    (hG : ∀ i j : Fin m, G (Fin.castLE hm i) j = if i = j then 1 else 0)
    (σ : Fin (N + 1) → Bool) (i : Fin (N + 1)) (j : Fin m) :
    (if j.val < i.val then Fin.cons (α := fun _ : Fin (N + 1) => Fin m → ℝ) 0 G i j
      else if j.val = i.val then (if σ i then (0 : ℝ) else -0) else 0) =
        Fin.cons (α := fun _ : Fin (N + 1) => Fin m → ℝ) 0 G i j := by
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    by_cases hj : j.val < i.succ.val
    · simp only [if_pos hj]
    · have hij : i.val < j.val := by simp only [Fin.val_succ] at hj; omega
      have him : i.val < m := lt_trans hij j.isLt
      let k : Fin m := ⟨i.val, him⟩
      have hCast : Fin.castLE hm k = i := Fin.ext rfl
      have hne : k ≠ j := by intro h; have := congrArg Fin.val h; change i.val = j.val at this; omega
      have hZero : G i j = 0 := by rw [← hCast, hG k j, if_neg hne]
      simp [hZero]

end Grunbaum2003


-- Local ingredient: AffineDetDensity

set_option autoImplicit false

namespace Grunbaum2003

open Polynomial
open scoped Matrix.Norms.Elementwise

                                                                
private theorem eval_det_affine_pencil {m : ℕ}
    (M N : Matrix (Fin m) (Fin m) ℝ) (t : ℝ) :
    Polynomial.eval t
        (Matrix.det (fun i j => Polynomial.C (M i j) +
          Polynomial.X * Polynomial.C (N i j - M i j))) =
      Matrix.det (AffineMap.lineMap M N t) := by
  let K : Matrix (Fin m) (Fin m) (Polynomial ℝ) := fun i j =>
    Polynomial.C (M i j) + Polynomial.X * Polynomial.C (N i j - M i j)
  change (Polynomial.evalRingHom t) K.det = _
  rw [(Polynomial.evalRingHom t).map_det K]
  apply congrArg Matrix.det
  ext i j
  change Polynomial.eval t (Polynomial.C (M i j) +
    Polynomial.X * Polynomial.C (N i j - M i j)) =
      t * (N i j - M i j) + M i j
  simp [add_comm]

                                                                           
                             
theorem affine_det_regular_locus_dense {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ}
    (A : E →ᵃ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (hReg : ∃ q, Matrix.det (A q) ≠ 0) :
    Dense {x | Matrix.det (A x) ≠ 0} := by
  classical
  obtain ⟨q, hq⟩ := hReg
  intro y
  let P : ℝ[X] := Matrix.det (fun i j => Polynomial.C (A y i j) +
    Polynomial.X * Polynomial.C (A q i j - A y i j))
  have hEval (t : ℝ) : P.eval t = Matrix.det (A (AffineMap.lineMap y q t)) := by
    rw [A.apply_lineMap]
    exact eval_det_affine_pencil (A y) (A q) t
  have hAtOne : P.eval 1 ≠ 0 := by
    rw [hEval, AffineMap.lineMap_apply_one]
    exact hq
  have hP : P ≠ 0 := by
    intro h
    apply hAtOne
    simp only [h, Polynomial.eval_zero]
  have hFinite : Set.Finite {t : ℝ | P.eval t = 0} :=
    Polynomial.finite_setOfPred_isRoot hP
  have hDense : Dense {t : ℝ | P.eval t ≠ 0} := by
    simpa only [Set.sdiff_eq, Set.univ_inter, Set.compl_ofPred] using
      (dense_univ : Dense (Set.univ : Set ℝ)).sdiff_finite hFinite
  have hy : AffineMap.lineMap y q (0 : ℝ) ∈ closure {x | Matrix.det (A x) ≠ 0} :=
    map_mem_closure (AffineMap.lineMap_continuous (p := y) (q := q))
    (hDense 0) (by
      intro t ht
      change Matrix.det (A (AffineMap.lineMap y q t)) ≠ 0
      rw [← hEval]
      exact ht)
  simpa only [AffineMap.lineMap_apply_zero] using hy

                                                                                 
theorem isOpen_affine_det_regular_locus {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ}
    (A : E →ᵃ[ℝ] Matrix (Fin m) (Fin m) ℝ) :
    IsOpen {x | Matrix.det (A x) ≠ 0} := by
  have hA : Continuous (A : E → Matrix (Fin m) (Fin m) ℝ) :=
    AffineMap.continuous_of_finiteDimensional
      (𝕜 := ℝ) (E := E) (F := Matrix (Fin m) (Fin m) ℝ)
      (PE := E) (PF := Matrix (Fin m) (Fin m) ℝ) A
  have hDet : Continuous (fun x => Matrix.det (A x)) := hA.matrix_det
  exact isOpen_ne_fun hDet continuous_const

                                                                             
                                                                 
theorem finite_affine_det_regular_locus_dense {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ}
    (S : Finset ι)
    (A : ι → E →ᵃ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (hReg : ∀ i ∈ S, ∃ q, Matrix.det (A i q) ≠ 0) :
    Dense {x | ∀ i ∈ S, Matrix.det (A i x) ≠ 0} := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hdi := affine_det_regular_locus_dense (A i) (hReg i (Finset.mem_insert_self _ _))
    have hdS := ih (fun j hj => hReg j (Finset.mem_insert_of_mem hj))
    have hd := hdi.inter_of_isOpen_left hdS (isOpen_affine_det_regular_locus (A i))
    simpa only [Set.ofPred_and, Finset.forall_mem_insert] using hd

                                                                           
                                        
theorem exists_mem_open_finite_affine_det_regular_locus {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ}
    (S : Finset ι)
    (A : ι → E →ᵃ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (hReg : ∀ i ∈ S, ∃ q, Matrix.det (A i q) ≠ 0)
    (U : Set E) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∀ i ∈ S, Matrix.det (A i x) ≠ 0 :=
  (finite_affine_det_regular_locus_dense S A hReg).inter_open_nonempty U hU hne

end Grunbaum2003


-- Local ingredient: TriangularMinorWitness

set_option autoImplicit false

namespace Grunbaum2003

                                                                       
theorem strictMono_fin_val_le {m n : ℕ} (u : Fin m → Fin n)
    (hu : StrictMono u) (i : Fin m) : i.val ≤ (u i).val := by
  have hAux : ∀ k : ℕ, ∀ j : Fin m, j.val = k → k ≤ (u j).val := by
    intro k
    induction k with
    | zero => intro j _; exact Nat.zero_le _
    | succ k ih =>
      intro j hj
      let l : Fin m := ⟨k, by omega⟩
      have hlj : l < j := by change k < j.val; omega
      have hLower : k ≤ (u l).val := ih l rfl
      have hStrict : (u l).val < (u j).val := hu hlj
      omega
  exact hAux i.val i rfl

                                                                          
                                                                             
                                                                         
                                                                              
theorem exists_regular_triangular_minor {m n : ℕ}
    (u : Fin m → Fin n) (hu : StrictMono u)
    (diag : Fin n → ℝ) (hDiag : ∀ i, diag i ≠ 0) :
    ∃ B : Matrix (Fin n) (Fin m) ℝ,
      Matrix.det (fun i j : Fin m =>
        if j.val < (u i).val then B (u i) j
        else if j.val = (u i).val then diag (u i) else 0) ≠ 0 := by
  classical
  let B : Matrix (Fin n) (Fin m) ℝ := fun i j => if i = u j then 1 else 0
  let M : Matrix (Fin m) (Fin m) ℝ := fun i j =>
    if j.val < (u i).val then B (u i) j
    else if j.val = (u i).val then diag (u i) else 0
  have hUpper : M.IsUpperTriangular := by
    intro i j hij
    have hji : j.val < (u i).val :=
      lt_of_lt_of_le hij (strictMono_fin_val_le u hu i)
    have hne : u i ≠ u j := fun h => (ne_of_gt hij) (hu.injective h)
    change (if j.val < (u i).val then (if u i = u j then 1 else 0)
      else if j.val = (u i).val then diag (u i) else 0) = 0
    rw [if_pos hji, if_neg hne]
  have hNonzero (i : Fin m) : M i i ≠ 0 := by
    by_cases hi : i.val < (u i).val
    · change (if i.val < (u i).val then (if u i = u i then 1 else 0)
        else if i.val = (u i).val then diag (u i) else 0) ≠ 0
      rw [if_pos hi, if_pos rfl]
      exact one_ne_zero
    · have hEq : i.val = (u i).val :=
        le_antisymm (strictMono_fin_val_le u hu i) (Nat.le_of_not_gt hi)
      change (if i.val < (u i).val then B (u i) i
        else if i.val = (u i).val then diag (u i) else 0) ≠ 0
      rw [if_neg hi, if_pos hEq]
      exact hDiag (u i)
  refine ⟨B, ?_⟩
  change M.det ≠ 0
  rw [Matrix.det_of_isUpperTriangular hUpper]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hNonzero i)

end Grunbaum2003


-- Local ingredient: TriangularGeneric

set_option autoImplicit false

open scoped Matrix.Norms.Elementwise

namespace Grunbaum2003

                                                                            
                                         
private def triangularMinorAffine {n m : ℕ} (u : Fin m → Fin n)
    (diag : Fin n → ℝ) :
    Matrix (Fin n) (Fin m) ℝ →ᵃ[ℝ] Matrix (Fin m) (Fin m) ℝ where
  toFun B := fun i j =>
    if j.val < (u i).val then B (u i) j
    else if j.val = (u i).val then diag (u i) else 0
  linear :=
    { toFun B := fun i j => if j.val < (u i).val then B (u i) j else 0
      map_add' B C := by
        ext i j
        change (if j.val < (u i).val then B (u i) j + C (u i) j else 0) =
          (if j.val < (u i).val then B (u i) j else 0) +
            (if j.val < (u i).val then C (u i) j else 0)
        by_cases h : j.val < (u i).val <;> simp [h]
      map_smul' c B := by
        ext i j
        change (if j.val < (u i).val then c * B (u i) j else 0) =
          c * (if j.val < (u i).val then B (u i) j else 0)
        by_cases h : j.val < (u i).val <;> simp [h] }
  map_vadd' B V := by
    ext i j
    change (if j.val < (u i).val then V (u i) j + B (u i) j
      else if j.val = (u i).val then diag (u i) else 0) =
        (if j.val < (u i).val then V (u i) j else 0) +
          (if j.val < (u i).val then B (u i) j
            else if j.val = (u i).val then diag (u i) else 0)
    by_cases h : j.val < (u i).val <;> simp [h]

                                                                           
                                                                         
theorem triangular_discarded_minors_dense {n m : ℕ}
    (ε : Fin n → ℝ) (hε : ∀ i, ε i ≠ 0) :
    Dense {B : Matrix (Fin n) (Fin m) ℝ |
      ∀ u : Fin m → Fin n, StrictMono u → ∀ σ : Fin n → Bool,
        Matrix.det (fun i j : Fin m =>
          if j.val < (u i).val then B (u i) j
          else if j.val = (u i).val then
            (if σ (u i) then ε (u i) else -ε (u i)) else 0) ≠ 0} := by
  classical
  let I := {u : Fin m → Fin n // StrictMono u} × (Fin n → Bool)
  let A : I → Matrix (Fin n) (Fin m) ℝ →ᵃ[ℝ] Matrix (Fin m) (Fin m) ℝ :=
    fun i => triangularMinorAffine i.1.1 (fun j => if i.2 j then ε j else -ε j)
  have hReg : ∀ i ∈ (Finset.univ : Finset I), ∃ B, Matrix.det (A i B) ≠ 0 := by
    rintro ⟨⟨u, hu⟩, σ⟩ _
    have hDiag (i : Fin n) : (if σ i then ε i else -ε i) ≠ 0 := by
      split
      · exact hε i
      · exact neg_ne_zero.mpr (hε i)
    exact exists_regular_triangular_minor u hu
      (fun i => if σ i then ε i else -ε i) hDiag
  have hDense := finite_affine_det_regular_locus_dense (Finset.univ : Finset I) A hReg
  apply hDense.mono
  intro B hB u hu σ
  exact hB (⟨u, hu⟩, σ) (Finset.mem_univ _)

                                                                            
                                                      
theorem exists_generic_triangular_discarded_normals {n m : ℕ}
    (ε : Fin n → ℝ) (hε : ∀ i, ε i ≠ 0)
    (U : Set (Matrix (Fin n) (Fin m) ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ B ∈ U,
      ∀ u : Fin m → Fin n, StrictMono u → ∀ σ : Fin n → Bool,
        Matrix.det (fun i j : Fin m =>
          if j.val < (u i).val then B (u i) j
          else if j.val = (u i).val then
            (if σ (u i) then ε (u i) else -ε (u i)) else 0) ≠ 0 :=
  (triangular_discarded_minors_dense ε hε).inter_open_nonempty U hU hne

end Grunbaum2003


-- Local ingredient: PositiveTriangularNeighborhood

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.Elementwise

namespace Grunbaum2003

private def signedTriangularRows {n m : ℕ}
    (z : Matrix (Fin n) (Fin m) ℝ × ℝ) (σ : Fin n → Bool) : Fin n → Fin m → ℝ :=
  fun i j => if j.val < i.val then z.1 i j
    else if j.val = i.val then (if σ i then z.2 else -z.2) else 0

                                                                         
                                                                              
theorem exists_joint_positive_spanning_triangular_neighborhood {N m r : ℕ}
    (hm : m ≤ N) (G : Fin N → Fin m → ℝ)
    (hBasis : ∀ i j : Fin m, G (Fin.castLE hm i) j = if i = j then 1 else 0)
    (hG : ∀ J : Finset (Fin N), J.card ≤ r →
      (∃ weight : {i : Fin N // i ∉ J} → ℝ,
        (∀ i, 0 < weight i) ∧ (∑ i, weight i • G i.val) = 0) ∧
        Submodule.span ℝ (Set.range (fun i : {i : Fin N // i ∉ J} => G i.val)) = ⊤) :
    ∃ W : Set (Matrix (Fin (N + 1)) (Fin m) ℝ × ℝ),
      IsOpen W ∧ (Fin.cons (α := fun _ : Fin (N + 1) => Fin m → ℝ) 0 G, 0) ∈ W ∧
      ∀ B δ, (B, δ) ∈ W →
        ∀ J : Finset (Fin (N + 1)), J.card ≤ r → ∀ σ : Fin (N + 1) → Bool,
          (∃ weight : {i : Fin (N + 1) // i ∉ J} → ℝ,
            (∀ i, 0 < weight i) ∧
              (∑ i, weight i • (fun j : Fin m =>
                if j.val < i.val.val then B i.val j
                else if j.val = i.val.val then
                  (if σ i.val then δ else -δ) else 0)) = 0) ∧
          Submodule.span ℝ (Set.range (fun i : {i : Fin (N + 1) // i ∉ J} =>
            fun j : Fin m => if j.val < i.val.val then B i.val j
              else if j.val = i.val.val then
                (if σ i.val then δ else -δ) else 0)) = ⊤ := by
  classical
  have hShift (J : Finset (Fin (N + 1))) (hJ : J.card ≤ r) :
      (∃ weight : {i : Fin (N + 1) // i ∉ J} → ℝ,
        (∀ i, 0 < weight i) ∧
          (∑ i, weight i • Fin.cons (α := fun _ : Fin (N + 1) => Fin m → ℝ) 0 G i.val) = 0) ∧
        Submodule.span ℝ (Set.range (fun i : {i : Fin (N + 1) // i ∉ J} =>
          Fin.cons (α := fun _ : Fin (N + 1) => Fin m → ℝ) 0 G i.val)) = ⊤ := by
    let Jg : Finset (Fin N) := Finset.univ.filter (fun i => i.succ ∈ J)
    have hCard : Jg.card ≤ J.card :=
      Finset.card_le_card_of_injOn Fin.succ
        (fun i hi => (Finset.mem_filter.mp hi).2)
        (fun _ _ _ _ hij => Fin.succ_inj.mp hij)
    obtain ⟨hPos, hSpan⟩ := hG Jg (hCard.trans hJ)
    have hJg (i : Fin N) : i ∉ Jg ↔ i.succ ∉ J := by simp [Jg]
    let e : {i : Fin N // i.succ ∉ J} ≃ {i : Fin N // i ∉ Jg} :=
      Equiv.subtypeEquivRight (fun i => (hJg i).symm)
    obtain ⟨w, hw, hSum⟩ := hPos
    apply shift_zero_complement_positive_spanning G J
    · refine ⟨fun i => w (e i), fun i => hw (e i), ?_⟩
      exact (e.sum_comp (fun i => w i • G i.val)).trans hSum
    · have hRange :
          Set.range (fun i : {i : Fin N // i.succ ∉ J} => G i.val) =
            Set.range (fun i : {i : Fin N // i ∉ Jg} => G i.val) := by
        ext x
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨e i, rfl⟩
        · rintro ⟨i, rfl⟩
          exact ⟨e.symm i, rfl⟩
      rw [hRange]
      exact hSpan
  let I := {J : Finset (Fin (N + 1)) // J.card ≤ r} × (Fin (N + 1) → Bool)
  let W : Set (Matrix (Fin (N + 1)) (Fin m) ℝ × ℝ) := ⋂ c : I,
    (fun z => fun i : {i : Fin (N + 1) // i ∉ c.1.val} =>
      signedTriangularRows z c.2 i.val) ⁻¹'
      {a : {i : Fin (N + 1) // i ∉ c.1.val} → Fin m → ℝ |
        (∃ weight : {i : Fin (N + 1) // i ∉ c.1.val} → ℝ,
          (∀ i, 0 < weight i) ∧ (∑ i, weight i • a i) = 0) ∧
          Submodule.span ℝ (Set.range a) = ⊤}
  have hOpen : IsOpen W := by
    apply isOpen_iInter_of_finite
    intro c
    apply isOpen_positive_spanning_configurations.preimage
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    unfold signedTriangularRows
    split_ifs <;> fun_prop
  have hZeroRows (σ : Fin (N + 1) → Bool) (i : Fin (N + 1)) :
      signedTriangularRows (Fin.cons (α := fun _ : Fin (N + 1) => Fin m → ℝ) 0 G, 0) σ i =
        Fin.cons (α := fun _ : Fin (N + 1) => Fin m → ℝ) 0 G i := by
    funext j
    exact shifted_normalized_triangular_rows_at_zero hm G hBasis σ i j
  have hMem : (Fin.cons (α := fun _ : Fin (N + 1) => Fin m → ℝ) 0 G, 0) ∈ W := by
    apply Set.mem_iInter.mpr
    intro c
    change
      (∃ weight : {i : Fin (N + 1) // i ∉ c.1.val} → ℝ,
        (∀ i, 0 < weight i) ∧
          (∑ i, weight i • signedTriangularRows
            (Fin.cons (α := fun _ : Fin (N + 1) => Fin m → ℝ) 0 G, 0) c.2 i.val) = 0) ∧
        Submodule.span ℝ (Set.range (fun i : {i : Fin (N + 1) // i ∉ c.1.val} =>
          signedTriangularRows (Fin.cons (α := fun _ : Fin (N + 1) => Fin m → ℝ) 0 G, 0) c.2 i.val)) = ⊤
    simpa only [hZeroRows] using hShift c.1.val c.1.property
  refine ⟨W, hOpen, hMem, ?_⟩
  intro B δ hBW J hJ σ
  exact Set.mem_iInter.mp hBW (⟨J, hJ⟩, σ)

end Grunbaum2003


-- Local ingredient: PositiveGenericCoefficients

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.Elementwise

namespace Grunbaum2003

private theorem exists_pos_right_mem_open {E : Type*} [TopologicalSpace E]
    (W : Set (E × ℝ)) (hW : IsOpen W) (x : E) (hx : (x, 0) ∈ W) :
    ∃ δ : ℝ, 0 < δ ∧ (x, δ) ∈ W := by
  have hV : IsOpen ((fun δ : ℝ => (x, δ)) ⁻¹' W) :=
    hW.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨ε, hε, hBall⟩ := Metric.isOpen_iff.mp hV 0 hx
  refine ⟨ε / 2, half_pos hε, hBall ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
  exact half_lt_self hε

                                                                              
                                                                            
                                                                             
theorem exists_positive_generic_triangular_coefficients_of_normalized_family
    {N m r : ℕ} (hm : m ≤ N) (G : Fin N → Fin m → ℝ)
    (hBasis : ∀ i j : Fin m, G (Fin.castLE hm i) j = if i = j then 1 else 0)
    (hG : ∀ J : Finset (Fin N), J.card ≤ r →
      (∃ weight : {i : Fin N // i ∉ J} → ℝ,
        (∀ i, 0 < weight i) ∧ (∑ i, weight i • G i.val) = 0) ∧
        Submodule.span ℝ (Set.range (fun i : {i : Fin N // i ∉ J} => G i.val)) = ⊤) :
    ∃ B : Matrix (Fin (N + 1)) (Fin m) ℝ, ∃ δ : ℝ, 0 < δ ∧
      (∀ J : Finset (Fin (N + 1)), J.card ≤ r → ∀ σ : Fin (N + 1) → Bool,
        (∃ weight : {i : Fin (N + 1) // i ∉ J} → ℝ,
          (∀ i, 0 < weight i) ∧
            (∑ i, weight i • (fun j : Fin m =>
              if j.val < i.val.val then B i.val j
              else if j.val = i.val.val then
                (if σ i.val then δ else -δ) else 0)) = 0) ∧
        Submodule.span ℝ (Set.range (fun i : {i : Fin (N + 1) // i ∉ J} =>
          fun j : Fin m => if j.val < i.val.val then B i.val j
            else if j.val = i.val.val then
              (if σ i.val then δ else -δ) else 0)) = ⊤) ∧
      (∀ u : Fin m → Fin (N + 1), StrictMono u → ∀ σ : Fin (N + 1) → Bool,
        Matrix.det (fun i j : Fin m =>
          if j.val < (u i).val then B (u i) j
          else if j.val = (u i).val then
            (if σ (u i) then δ else -δ) else 0) ≠ 0) := by
  classical
  obtain ⟨W, hW, hZero, hPos⟩ :=
    exists_joint_positive_spanning_triangular_neighborhood hm G hBasis hG
  let B₀ : Matrix (Fin (N + 1)) (Fin m) ℝ :=
    Fin.cons (α := fun _ : Fin (N + 1) => Fin m → ℝ) 0 G
  obtain ⟨δ, hδ, hδW⟩ := exists_pos_right_mem_open W hW B₀ hZero
  let U : Set (Matrix (Fin (N + 1)) (Fin m) ℝ) := {B | (B, δ) ∈ W}
  have hU : IsOpen U := hW.preimage (continuous_id.prodMk continuous_const)
  have hUne : U.Nonempty := ⟨B₀, hδW⟩
  obtain ⟨B, hBU, hMinor⟩ := exists_generic_triangular_discarded_normals
    (fun _ : Fin (N + 1) => δ) (fun _ => ne_of_gt hδ) U hU hUne
  exact ⟨B, δ, hδ, hPos B δ hBU, hMinor⟩

end Grunbaum2003


-- Local ingredient: LagrangeGale

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003
open Polynomial

                                                                          
                                                                           
theorem lagrange_sum_eq_zero_of_degree_lt {N : ℕ}
    (t : Fin N → ℝ) (ht : Function.Injective t) (p : ℝ[X])
    (hp : p.degree < ((N - 1 : ℕ) : WithBot ℕ)) :
    ∑ i : Fin N, p.eval (t i) /
      ∏ j ∈ Finset.univ.erase i, (t i - t j) = 0 := by
  classical
  have hN : ((N - 1 : ℕ) : WithBot ℕ) ≤ (N : WithBot ℕ) := by
    exact_mod_cast Nat.sub_le N 1
  have hBound : p.degree < (Finset.univ : Finset (Fin N)).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using lt_of_lt_of_le hp hN
  have h := Lagrange.coeff_eq_sum (s := Finset.univ) ht.injOn hBound
  rw [Finset.card_univ, Fintype.card_fin, Polynomial.coeff_eq_zero_of_degree_lt hp] at h
  exact h.symm

                                                                          
                                                                                
theorem lagrange_weighted_moment_eq_zero {N : ℕ}
    (t : Fin N → ℝ) (ht : Function.Injective t) (p : ℝ[X]) (k : ℕ)
    (hp : p.natDegree + k < N - 1) :
    ∑ i : Fin N, p.eval (t i) *
      ((t i) ^ k / ∏ j ∈ Finset.univ.erase i, (t i - t j)) = 0 := by
  have hNat : (p * X ^ k).natDegree < N - 1 := by
    apply lt_of_le_of_lt (Polynomial.natDegree_mul_le (p := p) (q := X ^ k)) ?_
    simpa only [Polynomial.natDegree_X_pow] using hp
  have hDeg : (p * X ^ k).degree < ((N - 1 : ℕ) : WithBot ℕ) := by
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hNat)
  have h := lagrange_sum_eq_zero_of_degree_lt t ht (p * X ^ k) hDeg
  simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    mul_div_assoc] using h

                                                              
theorem lagrange_denominator_ne_zero {N : ℕ}
    (t : Fin N → ℝ) (ht : Function.Injective t) (i : Fin N) :
    (∏ j ∈ Finset.univ.erase i, (t i - t j)) ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro heq
  exact (Finset.mem_erase.mp hj).1 (ht heq).symm

                                                                               
                                                       
theorem lagrange_gale_rows_linearIndependent {N m : ℕ}
    (t : Fin N → ℝ) (ht : Function.Injective t)
    (u : Fin m → Fin N) (hu : Function.Injective u) :
    LinearIndependent ℝ (fun i : Fin m => fun j : Fin m =>
      (t (u i)) ^ j.val / ∏ k ∈ Finset.univ.erase (u i), (t (u i) - t k)) := by
  classical
  let den : Fin N → ℝ := fun i => ∏ k ∈ Finset.univ.erase i, (t i - t k)
  have hden : ∀ i, den i ≠ 0 := lagrange_denominator_ne_zero t ht
  let w : Fin m → ℝˣ := fun i => Units.mk0 ((den (u i))⁻¹) (inv_ne_zero (hden (u i)))
  have hV : LinearIndependent ℝ (fun i => Matrix.vandermonde (t ∘ u) i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero
      (Matrix.det_vandermonde_ne_zero_iff.mpr (ht.comp hu))
  have hRows : (fun i : Fin m => fun j : Fin m =>
      (t (u i)) ^ j.val / den (u i)) = w • (fun i => Matrix.vandermonde (t ∘ u) i) := by
    funext i j
    change (t (u i)) ^ j.val / den (u i) = (den (u i))⁻¹ * (t (u i)) ^ j.val
    rw [div_eq_mul_inv, mul_comm]
  change LinearIndependent ℝ (fun i : Fin m => fun j : Fin m =>
    (t (u i)) ^ j.val / den (u i))
  rw [hRows]
  exact hV.units_smul w

end Grunbaum2003


-- Local ingredient: MomentPolynomial

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

                                                                          
theorem moment_squared_polynomial_data {n : ℕ} (t : Fin n → ℝ)
    (ht : Function.Injective t) (J : Finset (Fin n)) :
    let p : Polynomial ℝ := ∏ j ∈ J, (Polynomial.X - Polynomial.C (t j)) ^ 2
    p.natDegree ≤ 2 * J.card ∧
      (∀ z : ℝ, p.eval z = ∏ j ∈ J, (z - t j) ^ 2) ∧
      (∀ j : Fin n, p.eval (t j) = 0 ↔ j ∈ J) ∧
      (∀ z : ℝ, 0 ≤ p.eval z) ∧
      (∀ j : Fin n, j ∉ J → 0 < p.eval (t j)) ∧
      (J = ∅ → p = 1) := by
  classical
  let p : Polynomial ℝ := ∏ j ∈ J, (Polynomial.X - Polynomial.C (t j)) ^ 2
  have hDegree : p.natDegree ≤ 2 * J.card := by
    calc
      p.natDegree ≤ ∑ j ∈ J, ((Polynomial.X - Polynomial.C (t j)) ^ 2).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ = 2 * J.card := by
        simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, one_mul,
          Finset.sum_const, smul_eq_mul, mul_comm]
  have hEval (z : ℝ) : p.eval z = ∏ j ∈ J, (z - t j) ^ 2 := by
    simp only [p, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
  have hZero (j : Fin n) : p.eval (t j) = 0 ↔ j ∈ J := by
    rw [hEval, Finset.prod_eq_zero_iff]
    constructor
    · rintro ⟨k, hk, hjk⟩
      have htk : t j = t k := sub_eq_zero.mp (sq_eq_zero_iff.mp hjk)
      exact (ht htk).symm ▸ hk
    · intro hj
      exact ⟨j, hj, by simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)]⟩
  have hNonneg (z : ℝ) : 0 ≤ p.eval z := by
    rw [hEval]
    exact Finset.prod_nonneg (fun j _ => sq_nonneg (z - t j))
  refine ⟨hDegree, hEval, hZero, hNonneg, ?_, ?_⟩
  · intro j hj
    exact lt_of_le_of_ne (hNonneg (t j)) (Ne.symm (fun h => hj ((hZero j).mp h)))
  · intro hEmpty
    simp only [hEmpty, Finset.prod_empty]

                                                                                    
                                                                                   
                                                                                                  
theorem moment_vandermonde_positive_coefficients {n q : ℕ}
    (t : Fin n → ℝ) (ht : Function.Injective t)
    (J : Finset (Fin n)) (hJ : 2 * J.card < q) :
    ∃ c : Fin q → ℝ,
      (∀ j : Fin n, (∑ r : Fin q, c r * (t j) ^ r.val) = ∏ k ∈ J, (t j - t k) ^ 2) ∧
      (∀ j : Fin n, (∑ r : Fin q, c r * (t j) ^ r.val) = 0 ↔ j ∈ J) ∧
      (∀ j : Fin n, j ∉ J → 0 < ∑ r : Fin q, c r * (t j) ^ r.val) ∧
      (J = ∅ → ∀ r : Fin q, c r = if r.val = 0 then 1 else 0) := by
  classical
  let p : Polynomial ℝ := ∏ j ∈ J, (Polynomial.X - Polynomial.C (t j)) ^ 2
  obtain ⟨hDegree, hEval, hZero, _, hPos, hEmpty⟩ := moment_squared_polynomial_data t ht J
  let c : Fin q → ℝ := fun r => p.coeff r.val
  have hSum (j : Fin n) : (∑ r : Fin q, c r * (t j) ^ r.val) = p.eval (t j) := by
    change (∑ r : Fin q, p.coeff r.val * (t j) ^ r.val) = _
    rw [Fin.sum_univ_eq_sum_range (fun r => p.coeff r * (t j) ^ r) q]
    exact (Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hDegree hJ) (t j)).symm
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hSum j]
    exact hEval (t j)
  · intro j
    rw [hSum j]
    exact hZero j
  · intro j hj
    rw [hSum j]
    exact hPos j hj
  · intro hJEmpty r
    change p.coeff r.val = _
    have hpOne : p = 1 := hEmpty hJEmpty
    rw [hpOne]
    simp only [Polynomial.coeff_one]

end Grunbaum2003


-- Local ingredient: GalePositive

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

                                                                            
                                                                            
theorem lagrange_gale_positive_relation {N m : ℕ}
    (t : Fin N → ℝ) (ht : Function.Injective t)
    (J : Finset (Fin N)) (hJ : 2 * J.card + m < N) :
    ∃ weight : Fin N → ℝ,
      (∀ i, weight i = 0 ↔ i ∈ J) ∧
      (∀ i, i ∉ J → 0 < weight i) ∧
      (∀ k : Fin m, ∑ i : Fin N, weight i *
        ((t i) ^ k.val / ∏ j ∈ Finset.univ.erase i, (t i - t j)) = 0) := by
  classical
  let p : Polynomial ℝ := ∏ j ∈ J, (Polynomial.X - Polynomial.C (t j)) ^ 2
  obtain ⟨hDegree, _, hZero, _, hPos, _⟩ := moment_squared_polynomial_data t ht J
  refine ⟨fun i => p.eval (t i), hZero, hPos, ?_⟩
  intro k
  apply lagrange_weighted_moment_eq_zero t ht p k.val
  have hk := k.isLt
  change p.natDegree ≤ 2 * J.card at hDegree
  omega

                                                                           
                              
theorem lagrange_gale_square_span {N m : ℕ}
    (t : Fin N → ℝ) (ht : Function.Injective t)
    (u : Fin m → Fin N) (hu : Function.Injective u) :
    Submodule.span ℝ (Set.range (fun i : Fin m => fun j : Fin m =>
      (t (u i)) ^ j.val / ∏ k ∈ Finset.univ.erase (u i), (t (u i) - t k))) = ⊤ := by
  apply (lagrange_gale_rows_linearIndependent t ht u hu).span_eq_top_of_card_eq_finrank'
  simp only [Fintype.card_fin, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one]

end Grunbaum2003


-- Local ingredient: GaleConfiguration

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

                                                                    
                                          
theorem lagrange_gale_complement_span {N m : ℕ}
    (t : Fin N → ℝ) (ht : Function.Injective t)
    (J : Finset (Fin N)) (hJ : J.card + m ≤ N) :
    Submodule.span ℝ (Set.range (fun i : {i : Fin N // i ∉ J} =>
      fun j : Fin m => (t i.val) ^ j.val /
        ∏ k ∈ Finset.univ.erase i.val, (t i.val - t k))) = ⊤ := by
  classical
  have hCard : Fintype.card {i : Fin N // i ∉ J} = N - J.card := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_fin, Fintype.card_coe]
  have hBound : Fintype.card (Fin m) ≤ Fintype.card {i : Fin N // i ∉ J} := by
    rw [Fintype.card_fin, hCard]
    omega
  obtain ⟨u⟩ := Function.Embedding.nonempty_of_card_le hBound
  have hU : Function.Injective (fun i => (u i).val) :=
    Subtype.val_injective.comp u.injective
  apply top_unique
  rw [← lagrange_gale_square_span t ht (fun i => (u i).val) hU]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨u i, rfl⟩

                                                                              
                                                                              
                                                                           
theorem lagrange_gale_complement_positive_spanning {N m : ℕ}
    (t : Fin N → ℝ) (ht : Function.Injective t)
    (J : Finset (Fin N)) (hJ : 2 * J.card + m < N) :
    (∃ weight : {i : Fin N // i ∉ J} → ℝ,
      (∀ i, 0 < weight i) ∧
      (∑ i : {i : Fin N // i ∉ J}, weight i •
        (fun j : Fin m => (t i.val) ^ j.val /
          ∏ k ∈ Finset.univ.erase i.val, (t i.val - t k))) = 0) ∧
    Submodule.span ℝ (Set.range (fun i : {i : Fin N // i ∉ J} =>
      fun j : Fin m => (t i.val) ^ j.val /
        ∏ k ∈ Finset.univ.erase i.val, (t i.val - t k))) = ⊤ := by
  classical
  obtain ⟨weight, hZero, hPos, hSum⟩ := lagrange_gale_positive_relation t ht J hJ
  refine ⟨⟨fun i => weight i.val, fun i => hPos i.val i.property, ?_⟩,
    lagrange_gale_complement_span t ht J (by omega)⟩
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i => i ∉ J))
    (fun i => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (fun i => weight i *
      ((t i) ^ k.val / ∏ j ∈ Finset.univ.erase i, (t i - t j))),
    Finset.sum_filter]
  have hEq : (∑ i : Fin N, if i ∉ J then
      weight i * ((t i) ^ k.val / ∏ j ∈ Finset.univ.erase i, (t i - t j)) else 0) =
      ∑ i : Fin N, weight i *
        ((t i) ^ k.val / ∏ j ∈ Finset.univ.erase i, (t i - t j)) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ J
    · rw [if_neg (not_not.mpr hi), (hZero i).mpr hi, zero_mul]
    · rw [if_pos hi]
  exact hEq.trans (hSum k)

end Grunbaum2003


-- Local ingredient: GaleNormalized

set_option autoImplicit false
open scoped BigOperators
open Module

namespace Grunbaum2003

                                                                             
                                                                         
                                                                             
theorem exists_normalized_lagrange_gale {N m : ℕ} (hm : m ≤ N)
    (t : Fin N → ℝ) (ht : Function.Injective t) :
    ∃ T : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ),
      (∀ i j : Fin m,
        T (fun k : Fin m => (t (Fin.castLE hm i)) ^ k.val /
          ∏ l ∈ Finset.univ.erase (Fin.castLE hm i),
            (t (Fin.castLE hm i) - t l)) j = if i = j then 1 else 0) ∧
      ∀ J : Finset (Fin N), 2 * J.card + m < N →
        (∃ weight : {i : Fin N // i ∉ J} → ℝ,
          (∀ i, 0 < weight i) ∧
          (∑ i : {i : Fin N // i ∉ J}, weight i •
            T (fun j : Fin m => (t i.val) ^ j.val /
              ∏ k ∈ Finset.univ.erase i.val, (t i.val - t k))) = 0) ∧
        Submodule.span ℝ (Set.range (fun i : {i : Fin N // i ∉ J} =>
          T (fun j : Fin m => (t i.val) ^ j.val /
            ∏ k ∈ Finset.univ.erase i.val, (t i.val - t k)))) = ⊤ := by
  classical
  let v : Fin N → (Fin m → ℝ) := fun i j =>
    (t i) ^ j.val / ∏ k ∈ Finset.univ.erase i, (t i - t k)
  have hu : Function.Injective (Fin.castLE hm : Fin m → Fin N) := Fin.castLE_injective hm
  have hLI : LinearIndependent ℝ (fun i => v (Fin.castLE hm i)) :=
    lagrange_gale_rows_linearIndependent t ht _ hu
  have hSpan : Submodule.span ℝ (Set.range (fun i => v (Fin.castLE hm i))) = ⊤ :=
    lagrange_gale_square_span t ht _ hu
  let b : Basis (Fin m) ℝ (Fin m → ℝ) := Basis.mk hLI hSpan.ge
  have hb (i : Fin m) : b i = v (Fin.castLE hm i) := by
    exact congrFun (Basis.coe_mk hLI hSpan.ge) i
  let T : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) := b.equivFun
  refine ⟨T, ?_, ?_⟩
  · intro i j
    change b.equivFun (v (Fin.castLE hm i)) j = _
    rw [← hb i]
    exact b.equivFun_self i j
  · intro J hJ
    obtain ⟨⟨weight, hPos, hSum⟩, hSp⟩ :=
      lagrange_gale_complement_positive_spanning t ht J hJ
    refine ⟨⟨weight, hPos, ?_⟩, ?_⟩
    · simpa only [map_sum, map_smul, map_zero] using congrArg T hSum
    · have h := congrArg (Submodule.map T.toLinearMap) hSp
      rw [Submodule.map_span, Submodule.map_top,
        LinearMap.range_eq_top.mpr T.surjective] at h
      simpa only [← Set.range_comp', LinearEquiv.coe_toLinearMap,
        LinearEquiv.coe_coe] using h

end Grunbaum2003


-- Local ingredient: ActualGaleCoefficients

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.Elementwise

namespace Grunbaum2003

                                                                         
                                                                            
                                                                      
                                                       
theorem exists_neighborly_triangular_coefficients {n d : ℕ}
    (hd : 2 ≤ d) (hdn : d < n) :
    ∃ B : Matrix (Fin n) (Fin (n - d)) ℝ, ∃ δ : ℝ, 0 < δ ∧
      (∀ J : Finset (Fin n), J.card ≤ d / 2 - 1 → ∀ σ : Fin n → Bool,
        (∃ weight : {i : Fin n // i ∉ J} → ℝ,
          (∀ i, 0 < weight i) ∧
            (∑ i, weight i • (fun j : Fin (n - d) =>
              if j.val < i.val.val then B i.val j
              else if j.val = i.val.val then
                (if σ i.val then δ else -δ) else 0)) = 0) ∧
        Submodule.span ℝ (Set.range (fun i : {i : Fin n // i ∉ J} =>
          fun j : Fin (n - d) => if j.val < i.val.val then B i.val j
            else if j.val = i.val.val then
              (if σ i.val then δ else -δ) else 0)) = ⊤) ∧
      (∀ u : Fin (n - d) → Fin n, StrictMono u → ∀ σ : Fin n → Bool,
        Matrix.det (fun i j : Fin (n - d) =>
          if j.val < (u i).val then B (u i) j
          else if j.val = (u i).val then
            (if σ (u i) then δ else -δ) else 0) ≠ 0) := by
  classical
  cases n with
  | zero => omega
  | succ N =>
    let m : ℕ := N + 1 - d
    let r : ℕ := d / 2 - 1
    have hm : m ≤ N := by dsimp only [m]; omega
    let t : Fin N → ℝ := fun i => (i.val : ℝ)
    have ht : Function.Injective t := by
      intro i j hij
      apply Fin.ext
      exact Nat.cast_injective hij
    obtain ⟨T, hBasis, hComplement⟩ := exists_normalized_lagrange_gale hm t ht
    let G : Fin N → Fin m → ℝ := fun i =>
      T (fun j : Fin m => (t i) ^ j.val /
        ∏ k ∈ Finset.univ.erase i, (t i - t k))
    have hBasisG : ∀ i j : Fin m,
        G (Fin.castLE hm i) j = if i = j then 1 else 0 := hBasis
    have hG : ∀ J : Finset (Fin N), J.card ≤ r →
        (∃ weight : {i : Fin N // i ∉ J} → ℝ,
          (∀ i, 0 < weight i) ∧ (∑ i, weight i • G i.val) = 0) ∧
          Submodule.span ℝ (Set.range (fun i : {i : Fin N // i ∉ J} => G i.val)) = ⊤ := by
      intro J hJ
      apply hComplement J
      dsimp only [m, r] at *
      omega
    exact exists_positive_generic_triangular_coefficients_of_normalized_family
      hm G hBasisG hG

end Grunbaum2003


-- Local ingredient: DeformedIntervalFaces

set_option autoImplicit false

namespace Grunbaum2003

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

                                                                         
                                                      
theorem affine_maximizers_isExposed (P : Set E) (a : E →ᵃ[ℝ] ℝ) :
    IsExposed ℝ P {x | x ∈ P ∧ ∀ y ∈ P, a y ≤ a x} := by
  intro _
  refine ⟨a.linear.toContinuousLinearMap, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, fun y hy => ?_⟩
    have h := hmax y hy
    have hax : a x = a.linear x + a 0 := congrFun a.decomp x
    have hay : a y = a.linear y + a 0 := congrFun a.decomp y
    change a.linear y ≤ a.linear x
    linarith
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, fun y hy => ?_⟩
    have h : a.linear y ≤ a.linear x := hmax y hy
    have hax : a x = a.linear x + a 0 := congrFun a.decomp x
    have hay : a y = a.linear y + a 0 := congrFun a.decomp y
    linarith

                                                                           
                                                              
theorem maximizers_eq_graph_of_fiber_maximum
    (P : Set E) (C : Set (E × ℝ)) (g : E →ᵃ[ℝ] ℝ)
    (L : StrongDual ℝ (E × ℝ))
    (hBase : ∀ z ∈ C, z.1 ∈ P)
    (hGraph : ∀ x ∈ P, (x, g x) ∈ C)
    (hLe : ∀ z ∈ C, L z ≤ L (z.1, g z.1))
    (hEq : ∀ z ∈ C, L z = L (z.1, g z.1) → z.2 = g z.1) :
    let A := {x | x ∈ P ∧ ∀ y ∈ P, L (y, g y) ≤ L (x, g x)}
    IsExposed ℝ P A ∧
      {z | z ∈ C ∧ ∀ w ∈ C, L w ≤ L z} =
        {z | z.1 ∈ A ∧ z.2 = g z.1} := by
  classical
  let a : E →ᵃ[ℝ] ℝ :=
    L.toLinearMap.toAffineMap.comp ((AffineMap.id ℝ E).prod g)
  refine ⟨affine_maximizers_isExposed P a, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hmax⟩
    have hLG : L z = L (z.1, g z.1) :=
      le_antisymm (hLe z hz) (hmax _ (hGraph z.1 (hBase z hz)))
    refine ⟨⟨hBase z hz, fun y hy => ?_⟩, hEq z hz hLG⟩
    rw [← hLG]
    exact hmax _ (hGraph y hy)
  · rintro ⟨⟨hz, hmax⟩, hHeight⟩
    have hzEq : z = (z.1, g z.1) := Prod.ext rfl hHeight
    refine ⟨hzEq ▸ hGraph z.1 hz, ?_⟩
    intro w hw
    calc
      L w ≤ L (w.1, g w.1) := hLe w hw
      _ ≤ L (z.1, g z.1) := hmax w.1 (hBase w hw)
      _ = L z := congrArg L hzEq.symm

omit [FiniteDimensional ℝ E] in
                                                                      
                        
theorem product_functional_apply (L : StrongDual ℝ (E × ℝ)) (x : E) (t : ℝ) :
    L (x, t) = L (x, 0) + t * L (0, 1) := by
  have hPair : (x, t) = (x, 0) + t • (0, 1) := by ext <;> simp
  rw [hPair, map_add, map_smul, smul_eq_mul]

                                                                     
                                                              
theorem deformed_interval_upper_face (P : Set E) (f : E →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P, 0 ≤ f x) (L : StrongDual ℝ (E × ℝ))
    (hL : 0 < L (0, 1)) :
    let C := {z : E × ℝ | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1}
    ∃ A : Set E, IsExposed ℝ P A ∧
      {z | z ∈ C ∧ ∀ w ∈ C, L w ≤ L z} =
        {z | z.1 ∈ A ∧ z.2 = f z.1} := by
  refine ⟨_, maximizers_eq_graph_of_fiber_maximum P _ f L
    (fun _ hz => hz.1) (fun x hx => ⟨hx, by linarith [hf x hx], le_rfl⟩) ?_ ?_⟩
  · intro z hz
    rw [product_functional_apply L z.1 z.2, product_functional_apply L z.1 (f z.1)]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hz.2.2 hL.le)
  · intro z _ heq
    rw [product_functional_apply L z.1 z.2, product_functional_apply L z.1 (f z.1)] at heq
    exact (mul_left_inj' hL.ne').mp (add_left_cancel heq)

                                                                    
theorem deformed_interval_lower_face (P : Set E) (f : E →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P, 0 ≤ f x) (L : StrongDual ℝ (E × ℝ))
    (hL : L (0, 1) < 0) :
    let C := {z : E × ℝ | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1}
    ∃ A : Set E, IsExposed ℝ P A ∧
      {z | z ∈ C ∧ ∀ w ∈ C, L w ≤ L z} =
        {z | z.1 ∈ A ∧ z.2 = -f z.1} := by
  refine ⟨_, maximizers_eq_graph_of_fiber_maximum P _ (-f) L
    (fun _ hz => hz.1) (fun x hx => ⟨hx, le_rfl, by
      change -f x ≤ f x
      linarith [hf x hx]⟩) ?_ ?_⟩
  · intro z hz
    rw [product_functional_apply L z.1 z.2, product_functional_apply L z.1 ((-f) z.1)]
    exact add_le_add le_rfl (mul_le_mul_of_nonpos_right hz.2.1 hL.le)
  · intro z _ heq
    rw [product_functional_apply L z.1 z.2, product_functional_apply L z.1 ((-f) z.1)] at heq
    exact (mul_left_inj' hL.ne).mp (add_left_cancel heq)

                                                                             
theorem deformed_interval_free_face (P : Set E) (f : E →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P, 0 ≤ f x) (L : StrongDual ℝ (E × ℝ))
    (hL : L (0, 1) = 0) :
    let C := {z : E × ℝ | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1}
    ∃ A : Set E, IsExposed ℝ P A ∧
      {z | z ∈ C ∧ ∀ w ∈ C, L w ≤ L z} =
        {z | z.1 ∈ A ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1} := by
  let a : E →ᵃ[ℝ] ℝ :=
    L.toLinearMap.toAffineMap.comp ((AffineMap.id ℝ E).prod (AffineMap.const ℝ E 0))
  refine ⟨{x | x ∈ P ∧ ∀ y ∈ P, L (y, 0) ≤ L (x, 0)},
    affine_maximizers_isExposed P a, ?_⟩
  have hApply (x : E) (t : ℝ) : L (x, t) = L (x, 0) := by
    rw [product_functional_apply, hL, mul_zero, add_zero]
  ext z
  constructor
  · rintro ⟨hz, hmax⟩
    refine ⟨⟨hz.1, fun y hy => ?_⟩, hz.2⟩
    have h := hmax (y, 0) ⟨hy, by linarith [hf y hy], hf y hy⟩
    rwa [hApply z.1 z.2] at h
  · rintro ⟨⟨hz, hmax⟩, hBounds⟩
    refine ⟨⟨hz, hBounds⟩, fun w hw => ?_⟩
    rw [hApply w.1 w.2, hApply z.1 z.2]
    exact hmax w.1 hw.1

end Grunbaum2003


-- Local ingredient: DeformedIntervalConverse

set_option autoImplicit false

namespace Grunbaum2003

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

                                                                            
                                                                             
theorem isExposed_graph_of_affine_fiber_bound
    (P : Set E) (C : Set (E × ℝ)) (g : E →ᵃ[ℝ] ℝ)
    (hBase : ∀ z ∈ C, z.1 ∈ P)
    (hGraph : ∀ x ∈ P, (x, g x) ∈ C)
    (s : ℝ) (hs : s ≠ 0)
    (hBound : ∀ z ∈ C, s * z.2 ≤ s * g z.1)
    (F : Set E) (hF : IsExposed ℝ P F) :
    IsExposed ℝ C {z : E × ℝ | z.1 ∈ F ∧ z.2 = g z.1} := by
  intro hNonempty
  obtain ⟨z₀, hz₀⟩ := hNonempty
  obtain ⟨l, hl⟩ := hF ⟨z₀.1, hz₀.1⟩
  let fstL := ContinuousLinearMap.fst ℝ E ℝ
  let sndL := ContinuousLinearMap.snd ℝ E ℝ
  let L : StrongDual ℝ (E × ℝ) :=
    l.comp fstL + s • (sndL - g.linear.toContinuousLinearMap.comp fstL)
  have hApply (x : E) (t : ℝ) : L (x, t) = l x + s * (t - g.linear x) := rfl
  have hGraphApply (x : E) : L (x, g x) = l x + s * g 0 := by
    rw [hApply]
    have hg : g x = g.linear x + g 0 := congrFun g.decomp x
    rw [hg, add_sub_cancel_left]
  have hLe (z : E × ℝ) (hz : z ∈ C) : L z ≤ L (z.1, g z.1) := by
    rw [hApply, hApply]
    have h := hBound z hz
    simp only [mul_sub]
    linarith
  have hEq (z : E × ℝ) (_ : z ∈ C)
      (h : L z = L (z.1, g z.1)) : z.2 = g z.1 := by
    rw [hApply, hApply] at h
    have hHeight := mul_left_cancel₀ hs (add_left_cancel h)
    linarith
  obtain ⟨_, hMax⟩ :=
    maximizers_eq_graph_of_fiber_maximum P C g L hBase hGraph hLe hEq
  simp_rw [hGraphApply, add_le_add_iff_right] at hMax
  rw [← hl] at hMax
  exact ⟨L, hMax.symm⟩

omit [FiniteDimensional ℝ E] in
                                                                           
                                
theorem isExposed_full_fibers (P : Set E) (C : Set (E × ℝ))
    (hBase : ∀ z ∈ C, z.1 ∈ P)
    (hCover : ∀ x ∈ P, ∃ t : ℝ, (x, t) ∈ C)
    (F : Set E) (hF : IsExposed ℝ P F) :
    IsExposed ℝ C {z : E × ℝ | z ∈ C ∧ z.1 ∈ F} := by
  intro hNonempty
  obtain ⟨z₀, hz₀⟩ := hNonempty
  obtain ⟨l, hl⟩ := hF ⟨z₀.1, hz₀.2⟩
  refine ⟨l.comp (ContinuousLinearMap.fst ℝ E ℝ), ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hFz⟩
    rw [hl] at hFz
    exact ⟨hz, fun w hw => hFz.2 w.1 (hBase w hw)⟩
  · rintro ⟨hz, hmax⟩
    refine ⟨hz, ?_⟩
    rw [hl]
    refine ⟨hBase z hz, fun x hx => ?_⟩
    obtain ⟨t, ht⟩ := hCover x hx
    exact hmax (x, t) ht

                                                                         
                                                                           
theorem deformed_interval_faces_of_base (P : Set E) (f : E →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P, 0 ≤ f x) (F : Set E) (hF : IsExposed ℝ P F) :
    let C := {z : E × ℝ | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1}
    IsExposed ℝ C {z | z.1 ∈ F ∧ z.2 = f z.1} ∧
      IsExposed ℝ C {z | z.1 ∈ F ∧ z.2 = -f z.1} ∧
      IsExposed ℝ C {z | z.1 ∈ F ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1} := by
  let C : Set (E × ℝ) := {z | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1}
  have hBase : ∀ z ∈ C, z.1 ∈ P := fun _ hz => hz.1
  have hUpper : ∀ x ∈ P, (x, f x) ∈ C := by
    intro x hx
    exact ⟨hx, by linarith [hf x hx], le_rfl⟩
  have hLower : ∀ x ∈ P, (x, (-f) x) ∈ C := by
    intro x hx
    exact ⟨hx, le_rfl, by change -f x ≤ f x; linarith [hf x hx]⟩
  refine ⟨isExposed_graph_of_affine_fiber_bound P C f hBase hUpper 1 one_ne_zero
    (fun z hz => by simpa only [one_mul] using hz.2.2) F hF, ?_, ?_⟩
  · exact isExposed_graph_of_affine_fiber_bound P C (-f) hBase hLower (-1)
      (neg_ne_zero.mpr one_ne_zero)
      (fun z hz => by change (-1) * z.2 ≤ (-1) * (-f z.1); linarith [hz.2.1]) F hF
  · have h := isExposed_full_fibers P C hBase
      (fun x hx => ⟨f x, hUpper x hx⟩) F hF
    convert h using 1
    ext z
    constructor
    · rintro ⟨hz, h₁, h₂⟩
      exact ⟨⟨hF.subset hz, h₁, h₂⟩, hz⟩
    · rintro ⟨⟨_, h₁, h₂⟩, hz⟩
      exact ⟨hz, h₁, h₂⟩

                                                                           
                                                  
theorem deformed_interval_face_classification (P : Set E) (f : E →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P, 0 ≤ f x) (S : Set (E × ℝ))
    (hS : IsExposed ℝ {z : E × ℝ | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1} S) :
    ∃ F : Set E, IsExposed ℝ P F ∧
      (S = {z | z.1 ∈ F ∧ z.2 = f z.1} ∨
       S = {z | z.1 ∈ F ∧ z.2 = -f z.1} ∨
       S = {z | z.1 ∈ F ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1}) := by
  obtain rfl | hNonempty := S.eq_empty_or_nonempty
  · refine ⟨∅, isExposed_empty, Or.inl ?_⟩
    ext z
    simp only [Set.mem_empty_iff_false, Set.mem_ofPred_eq, false_and]
  obtain ⟨L, rfl⟩ := hS hNonempty
  rcases lt_trichotomy 0 (L (0, 1)) with hL | hL | hL
  · obtain ⟨F, hF, hEq⟩ := deformed_interval_upper_face P f hf L hL
    exact ⟨F, hF, Or.inl hEq⟩
  · obtain ⟨F, hF, hEq⟩ := deformed_interval_free_face P f hf L hL.symm
    exact ⟨F, hF, Or.inr (Or.inr hEq)⟩
  · obtain ⟨F, hF, hEq⟩ := deformed_interval_lower_face P f hf L hL
    exact ⟨F, hF, Or.inr (Or.inl hEq)⟩

end Grunbaum2003


-- Local ingredient: FiberNormalization

set_option autoImplicit false

namespace Grunbaum2003

variable {E : Type*}

                                                                       
theorem normalize_fiber_upper_image (P F : Set E) (f : E → ℝ)
    (hf : ∀ x ∈ P, 0 < f x) (hFP : F ⊆ P) :
    (fun z : E × ℝ => (z.1, z.2 / f z.1)) ''
        {z : E × ℝ | z.1 ∈ F ∧ z.2 = f z.1} =
      {z : E × ℝ | z.1 ∈ F ∧ z.2 = 1} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, ⟨hz, hHeight⟩, rfl⟩
    refine ⟨hz, ?_⟩
    change z.2 / f z.1 = 1
    rw [hHeight, div_self (hf z.1 (hFP hz)).ne']
  · rintro ⟨x, t⟩ ⟨hx, ht⟩
    refine ⟨(x, f x), ⟨hx, rfl⟩, ?_⟩
    apply Prod.ext
    · rfl
    · change f x / f x = t
      rw [div_self (hf x (hFP hx)).ne']
      exact ht.symm

                                                                        
theorem normalize_fiber_lower_image (P F : Set E) (f : E → ℝ)
    (hf : ∀ x ∈ P, 0 < f x) (hFP : F ⊆ P) :
    (fun z : E × ℝ => (z.1, z.2 / f z.1)) ''
        {z : E × ℝ | z.1 ∈ F ∧ z.2 = -f z.1} =
      {z : E × ℝ | z.1 ∈ F ∧ z.2 = -1} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, ⟨hz, hHeight⟩, rfl⟩
    refine ⟨hz, ?_⟩
    change z.2 / f z.1 = -1
    rw [hHeight, neg_div, div_self (hf z.1 (hFP hz)).ne']
  · rintro ⟨x, t⟩ ⟨hx, ht⟩
    refine ⟨(x, -f x), ⟨hx, rfl⟩, ?_⟩
    apply Prod.ext
    · rfl
    · change -f x / f x = t
      rw [neg_div, div_self (hf x (hFP hx)).ne']
      exact ht.symm

                                                                    
                                                         
theorem normalize_fiber_interval_image (P F : Set E) (f : E → ℝ)
    (hf : ∀ x ∈ P, 0 < f x) (hFP : F ⊆ P) :
    (fun z : E × ℝ => (z.1, z.2 / f z.1)) ''
        {z : E × ℝ | z.1 ∈ F ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1} =
      {z : E × ℝ | z.1 ∈ F ∧ -1 ≤ z.2 ∧ z.2 ≤ 1} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, ⟨hz, hLo, hUp⟩, rfl⟩
    have hfx := hf z.1 (hFP hz)
    refine ⟨hz, (le_div_iff₀ hfx).mpr ?_, (div_le_iff₀ hfx).mpr ?_⟩
    · simpa only [neg_one_mul] using hLo
    · simpa only [one_mul] using hUp
  · rintro ⟨x, t⟩ ⟨hx, hLo, hUp⟩
    have hfx := hf x (hFP hx)
    refine ⟨(x, t * f x), ⟨hx, ?_, ?_⟩, ?_⟩
    · simpa only [neg_one_mul] using mul_le_mul_of_nonneg_right hLo hfx.le
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right hUp hfx.le
    · apply Prod.ext
      · rfl
      · exact mul_div_cancel_right₀ t hfx.ne'

                                                                       
theorem normalize_fiber_inverse_left (P : Set E) (f : E → ℝ)
    (hf : ∀ x ∈ P, 0 < f x) (z : E × ℝ) (hz : z.1 ∈ P) :
    (fun w : E × ℝ => (w.1, w.2 * f w.1))
      ((fun w : E × ℝ => (w.1, w.2 / f w.1)) z) = z := by
  apply Prod.ext
  · rfl
  · exact div_mul_cancel₀ z.2 (hf z.1 hz).ne'

                                                                      
theorem normalize_fiber_inverse_right (P : Set E) (f : E → ℝ)
    (hf : ∀ x ∈ P, 0 < f x) (z : E × ℝ) (hz : z.1 ∈ P) :
    (fun w : E × ℝ => (w.1, w.2 / f w.1))
      ((fun w : E × ℝ => (w.1, w.2 * f w.1)) z) = z := by
  apply Prod.ext
  · rfl
  · exact mul_div_cancel_right₀ z.2 (hf z.1 hz).ne'

end Grunbaum2003


-- Local ingredient: FaceImageOrder

set_option autoImplicit false

namespace Grunbaum2003

variable {E F : Type*} [AddCommGroup E] [TopologicalSpace E] [Module ℝ E]
  [AddCommGroup F] [TopologicalSpace F] [Module ℝ F]

                                                                       
                                                                        
                                                                          
                                                                           
theorem exposedFaces_orderIso_of_inverse_images
    (P : Set E) (Q : Set F) (f : E → F) (g : F → E)
    (hGF : ∀ x ∈ P, g (f x) = x)
    (hFG : ∀ y ∈ Q, f (g y) = y)
    (hFaces : ∀ S : Set E, IsExposed ℝ P S → IsExposed ℝ Q (f '' S))
    (hBack : ∀ T : Set F, IsExposed ℝ Q T → IsExposed ℝ P (g '' T)) :
    ∃ Φ : {S : Set E // IsExposed ℝ P S} ≃o
        {T : Set F // IsExposed ℝ Q T},
      ∀ S, (Φ S).val = f '' S.val := by
  classical
  have hInj : Set.InjOn f P := by
    intro x hx y hy hxy
    calc
      x = g (f x) := (hGF x hx).symm
      _ = g (f y) := congrArg g hxy
      _ = y := hGF y hy
  have hReflect {S T : Set E} (hS : IsExposed ℝ P S) (hT : IsExposed ℝ P T)
      (h : f '' S ⊆ f '' T) : S ⊆ T := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := h ⟨x, hx, rfl⟩
    exact (hInj (hT.subset hy) (hS.subset hx) hyx) ▸ hy
  let e : {S : Set E // IsExposed ℝ P S} ↪o
      {T : Set F // IsExposed ℝ Q T} := {
    toFun := fun S => ⟨f '' S.val, hFaces S.val S.property⟩
    inj' := by
      intro S T h
      have hEq : f '' S.val = f '' T.val := congrArg Subtype.val h
      apply Subtype.ext
      exact Set.Subset.antisymm (hReflect S.property T.property hEq.le)
        (hReflect T.property S.property hEq.ge)
    map_rel_iff' := by
      intro S T
      change f '' S.val ⊆ f '' T.val ↔ S.val ⊆ T.val
      constructor
      · exact hReflect S.property T.property
      · exact Set.image_mono }
  have he : Function.Surjective e := by
    intro T
    refine ⟨⟨g '' T.val, hBack T.val T.property⟩, ?_⟩
    apply Subtype.ext
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa only [hFG y (T.property.subset hy)] using hy
    · intro y hy
      exact ⟨g y, ⟨y, hy, rfl⟩, hFG y (T.property.subset hy)⟩
  exact ⟨OrderIso.ofSurjective e he, fun _ => rfl⟩

end Grunbaum2003


-- Local ingredient: AffineTransport

set_option autoImplicit false

namespace Grunbaum2003

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

                                                                                       
theorem isExposed_image_continuousAffineEquiv (f : E ≃ᴬ[ℝ] F)
    {P S : Set E} (hS : IsExposed ℝ P S) : IsExposed ℝ (f '' P) (f '' S) := by
  intro hne
  have hSne : S.Nonempty := by
    obtain ⟨y, x, hx, rfl⟩ := hne
    exact ⟨x, hx⟩
  obtain ⟨l, hl⟩ := hS hSne
  let m : F →L[ℝ] ℝ := l.comp f.symm.toContinuousAffineMap.contLinear
  have hm : ∀ x : E, m (f x) = l x - l (f.symm 0) := by
    intro x
    have hf := f.symm.toContinuousAffineMap.contLinear_map_vsub (f x) (0 : F)
    change f.symm.toContinuousAffineMap.contLinear (f x - 0) = f.symm (f x) - f.symm 0 at hf
    have hf' : f.symm.toContinuousAffineMap.contLinear (f x) = x - f.symm 0 := by
      simpa only [sub_zero, f.symm_apply_apply] using hf
    change l (f.symm.toContinuousAffineMap.contLinear (f x)) = _
    rw [hf', map_sub]
  refine ⟨m, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ P ∧ ∀ z ∈ P, l z ≤ l x := by
      simpa only [hl, Set.mem_ofPred_eq] using hx
    refine ⟨⟨x, hx'.1, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [hm, hm]
    exact sub_le_sub_right (hx'.2 z hz) _
  · rintro ⟨⟨x, hx, rfl⟩, hmax⟩
    refine ⟨x, ?_, rfl⟩
    rw [hl]
    refine ⟨hx, ?_⟩
    intro z hz
    have ht := hmax (f z) ⟨z, hz, rfl⟩
    rw [hm, hm] at ht
    exact (sub_le_sub_iff_right _).mp ht

theorem isExposed_image_continuousAffineEquiv_iff (f : E ≃ᴬ[ℝ] F) (P S : Set E) :
    IsExposed ℝ (f '' P) (f '' S) ↔ IsExposed ℝ P S := by
  constructor
  · intro h
    have h' := isExposed_image_continuousAffineEquiv f.symm h
    have hP : f.symm '' (f '' P) = P := f.toEquiv.symm_image_image P
    have hS' : f.symm '' (f '' S) = S := f.toEquiv.symm_image_image S
    rw [hP, hS'] at h'
    exact h'
  · exact isExposed_image_continuousAffineEquiv f

theorem isExposed_image_affineEquiv [FiniteDimensional ℝ E] (f : E ≃ᵃ[ℝ] F)
    {P S : Set E} (hS : IsExposed ℝ P S) : IsExposed ℝ (f '' P) (f '' S) := by
  exact isExposed_image_continuousAffineEquiv (AffineEquiv.toContinuousAffineEquiv f) hS

end Grunbaum2003


-- Local ingredient: AffineEmbedding

set_option autoImplicit false

namespace Grunbaum2003

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

                                                                               
                                                                                
theorem isExposed_image_affineMap_of_injective [FiniteDimensional ℝ F]
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    {P S : Set E} (hS : IsExposed ℝ P S) : IsExposed ℝ (f '' P) (f '' S) := by
  intro hne
  have hSne : S.Nonempty := by
    obtain ⟨y, x, hx, rfl⟩ := hne
    exact ⟨x, hx⟩
  obtain ⟨l, hl⟩ := hS hSne
  have hlin : Function.Injective f.linear := f.linear_injective_iff.mpr hf
  obtain ⟨u, hu⟩ := f.linear.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hlin)
  have hu_apply : ∀ x : E, u (f.linear x) = x := by
    intro x
    exact congrArg (fun L : E →ₗ[ℝ] E => L x) hu
  let m : F →L[ℝ] ℝ := l.comp u.toContinuousLinearMap
  have hm : ∀ x : E, m (f x) = l x + l (u (f 0)) := by
    intro x
    have hfx : f x = f.linear x + f 0 := by
      simpa only [vadd_eq_add, add_zero] using f.map_vadd (0 : E) x
    change l (u (f x)) = _
    rw [hfx, map_add, hu_apply, map_add]
  refine ⟨m, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ P ∧ ∀ z ∈ P, l z ≤ l x := by
      simpa only [hl, Set.mem_ofPred_eq] using hx
    refine ⟨⟨x, hx'.1, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [hm, hm]
    exact add_le_add (hx'.2 z hz) le_rfl
  · rintro ⟨⟨x, hx, rfl⟩, hmax⟩
    refine ⟨x, ?_, rfl⟩
    rw [hl]
    refine ⟨hx, ?_⟩
    intro z hz
    have ht := hmax (f z) ⟨z, hz, rfl⟩
    rw [hm, hm] at ht
    exact (add_le_add_iff_right _).mp ht

                                                                             
                                                     
theorem isExposed_preimage_affineMap_of_injective [FiniteDimensional ℝ E]
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    {P : Set E} {T : Set F} (hT : IsExposed ℝ (f '' P) T) :
    IsExposed ℝ P (f ⁻¹' T) := by
  intro hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨l, hl⟩ := hT ⟨f x, hx⟩
  let m : E →L[ℝ] ℝ := l.comp f.linear.toContinuousLinearMap
  have hm : ∀ x : E, m x = l (f x) - l (f 0) := by
    intro x
    have hv := f.linearMap_vsub x (0 : E)
    change f.linear (x - 0) = f x - f 0 at hv
    have hv' : f.linear x = f x - f 0 := by simpa only [sub_zero] using hv
    change l (f.linear x) = _
    rw [hv', map_sub]
  refine ⟨m, ?_⟩
  ext y
  constructor
  · intro hy
    change f y ∈ T at hy
    have hy' : f y ∈ f '' P ∧ ∀ z ∈ f '' P, l z ≤ l (f y) := by
      simpa only [hl, Set.mem_ofPred_eq] using hy
    refine ⟨hf.mem_set_image.mp hy'.1, ?_⟩
    intro z hz
    rw [hm, hm]
    exact sub_le_sub_right (hy'.2 (f z) ⟨z, hz, rfl⟩) _
  · rintro ⟨hy, hmax⟩
    change f y ∈ T
    rw [hl]
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have ht := hmax z hz
    rw [hm, hm] at ht
    exact (sub_le_sub_iff_right _).mp ht

theorem isExposed_image_affineMap_iff [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) (P S : Set E) :
    IsExposed ℝ (f '' P) (f '' S) ↔ IsExposed ℝ P S := by
  constructor
  · intro h
    have h' := isExposed_preimage_affineMap_of_injective f hf h
    rw [Set.preimage_image_eq S hf] at h'
    exact h'
  · exact isExposed_image_affineMap_of_injective f hf

end Grunbaum2003


-- Local ingredient: ProjectionFaceOrder

set_option autoImplicit false

namespace Grunbaum2003

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

                                                                               
                                              
theorem exposedFaces_orderIso_affineImage
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) (P : Set E) :
    ∃ Φ : {S : Set E // IsExposed ℝ P S} ≃o
        {T : Set F // IsExposed ℝ (f '' P) T},
      ∀ S, (Φ S).val = f '' S.val := by
  classical
  let e : {S : Set E // IsExposed ℝ P S} ↪o
      {T : Set F // IsExposed ℝ (f '' P) T} := {
    toFun := fun S => ⟨f '' S.val, isExposed_image_affineMap_of_injective f hf S.property⟩
    inj' := by
      intro S T h
      exact Subtype.ext (hf.image_injective (congrArg Subtype.val h))
    map_rel_iff' := by
      intro S T
      change f '' S.val ⊆ f '' T.val ↔ S.val ⊆ T.val
      constructor
      · intro h x hx
        exact hf.mem_set_image.mp (h ⟨x, hx, rfl⟩)
      · rintro h _ ⟨x, hx, rfl⟩
        exact ⟨x, h hx, rfl⟩ }
  have he : Function.Surjective e := by
    intro T
    refine ⟨⟨f ⁻¹' T.val, isExposed_preimage_affineMap_of_injective f hf T.property⟩, ?_⟩
    apply Subtype.ext
    apply Set.image_preimage_eq_of_subset
    intro x hx
    obtain ⟨y, _, hy⟩ := T.property.subset hx
    exact ⟨y, hy⟩
  exact ⟨OrderIso.ofSurjective e he, fun _ => rfl⟩

                                                                              
                                                                           
                                                                   
theorem exposedFaces_orderIso_projection_on_submodule
    (π : E →L[ℝ] F) (P : Set E) (x₀ : E) (U : Submodule ℝ E)
    (hP : ∀ x ∈ P, x - x₀ ∈ U)
    (hKer : ∀ z ∈ U, π z = 0 → z = 0) :
    Nonempty ({S : Set E // IsExposed ℝ P S} ≃o
      {T : Set F // IsExposed ℝ (π '' P) T}) := by
  classical
  let f : U →ᵃ[ℝ] E := U.subtype.toAffineMap + AffineMap.const ℝ U x₀
  let g : U →ᵃ[ℝ] F := π.toLinearMap.toAffineMap.comp f
  let Q : Set U := f ⁻¹' P
  have hfApply (u : U) : f u = (u : E) + x₀ := rfl
  have hgApply (u : U) : g u = π ((u : E) + x₀) := rfl
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    exact add_right_cancel (show (u : E) + x₀ = (v : E) + x₀ from huv)
  have hg : Function.Injective g := by
    intro u v huv
    have hEq : π (u : E) = π (v : E) := by
      have h : π ((u : E) + x₀) = π ((v : E) + x₀) := huv
      rw [map_add, map_add] at h
      exact add_right_cancel h
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hKer ((u : E) - (v : E)) (U.sub_mem u.property v.property)
    rw [map_sub, hEq, sub_self]
  have hfQ : f '' Q = P := by
    apply Set.Subset.antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact hu
    · intro x hx
      let u : U := ⟨x - x₀, hP x hx⟩
      have hu : f u = x := by rw [hfApply]; exact sub_add_cancel x x₀
      exact ⟨u, by change f u ∈ P; rwa [hu], hu⟩
  have hgQ : g '' Q = π '' P := by
    change (π ∘ f) '' Q = π '' P
    calc
      (π ∘ f) '' Q = π '' (f '' Q) := (Set.image_image π f Q).symm
      _ = π '' P := congrArg (fun S => π '' S) hfQ
  obtain ⟨e, _⟩ := exposedFaces_orderIso_affineImage f hf Q
  obtain ⟨e', _⟩ := exposedFaces_orderIso_affineImage g hg Q
  rw [hfQ] at e
  rw [hgQ] at e'
  exact ⟨e.symm.trans e'⟩

end Grunbaum2003


-- Local ingredient: FaceBijection

set_option autoImplicit false

namespace Grunbaum2003

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

                                                                          
                                                                            
                                                                       
structure ExposedFaceBijection (P : Set E) (Q : Set F) where
  toFun : E → F
  invFun : F → E
  map_mem : ∀ x ∈ P, toFun x ∈ Q
  inv_mem : ∀ y ∈ Q, invFun y ∈ P
  left_inv : ∀ x ∈ P, invFun (toFun x) = x
  right_inv : ∀ y ∈ Q, toFun (invFun y) = y
  map_face : ∀ S : Set E, IsExposed ℝ P S → IsExposed ℝ Q (toFun '' S)
  inv_face : ∀ T : Set F, IsExposed ℝ Q T → IsExposed ℝ P (invFun '' T)

namespace ExposedFaceBijection

def refl (P : Set E) : ExposedFaceBijection P P where
  toFun := id
  invFun := id
  map_mem := fun _ hx => hx
  inv_mem := fun _ hx => hx
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl
  map_face := fun _ h => by simpa only [Set.image_id] using h
  inv_face := fun _ h => by simpa only [Set.image_id] using h

def symm {P : Set E} {Q : Set F} (e : ExposedFaceBijection P Q) :
    ExposedFaceBijection Q P where
  toFun := e.invFun
  invFun := e.toFun
  map_mem := e.inv_mem
  inv_mem := e.map_mem
  left_inv := e.right_inv
  right_inv := e.left_inv
  map_face := e.inv_face
  inv_face := e.map_face

                                                                           
def congr {P P' : Set E} {Q Q' : Set F} (e : ExposedFaceBijection P Q)
    (hP : P = P') (hQ : Q = Q') : ExposedFaceBijection P' Q' where
  toFun := e.toFun
  invFun := e.invFun
  map_mem := by
    intro x hx
    rw [← hP] at hx
    rw [← hQ]
    exact e.map_mem x hx
  inv_mem := by
    intro y hy
    rw [← hQ] at hy
    rw [← hP]
    exact e.inv_mem y hy
  left_inv := by
    intro x hx
    rw [← hP] at hx
    exact e.left_inv x hx
  right_inv := by
    intro y hy
    rw [← hQ] at hy
    exact e.right_inv y hy
  map_face := by
    intro S hS
    rw [← hP] at hS
    rw [← hQ]
    exact e.map_face S hS
  inv_face := by
    intro T hT
    rw [← hQ] at hT
    rw [← hP]
    exact e.inv_face T hT

def trans {P : Set E} {Q : Set F} {R : Set G}
    (e : ExposedFaceBijection P Q) (e' : ExposedFaceBijection Q R) :
    ExposedFaceBijection P R where
  toFun := e'.toFun ∘ e.toFun
  invFun := e.invFun ∘ e'.invFun
  map_mem := fun x hx => e'.map_mem (e.toFun x) (e.map_mem x hx)
  inv_mem := fun y hy => e.inv_mem (e'.invFun y) (e'.inv_mem y hy)
  left_inv := by
    intro x hx
    change e.invFun (e'.invFun (e'.toFun (e.toFun x))) = x
    rw [e'.left_inv (e.toFun x) (e.map_mem x hx), e.left_inv x hx]
  right_inv := by
    intro y hy
    change e'.toFun (e.toFun (e.invFun (e'.invFun y))) = y
    rw [e.right_inv (e'.invFun y) (e'.inv_mem y hy), e'.right_inv y hy]
  map_face := by
    intro S hS
    simpa only [Set.image_image, Function.comp_def] using
      e'.map_face (e.toFun '' S) (e.map_face S hS)
  inv_face := by
    intro T hT
    simpa only [Set.image_image, Function.comp_def] using
      e.inv_face (e'.invFun '' T) (e'.inv_face T hT)

                                                                     
                                                                                
noncomputable def ofLinearEquiv [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : E ≃ₗ[ℝ] F) (P : Set E) : ExposedFaceBijection P (e '' P) where
  toFun := e
  invFun := e.symm
  map_mem := fun x hx => ⟨x, hx, rfl⟩
  inv_mem := by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [LinearEquiv.symm_apply_apply] using hx
  left_inv := fun x _ => e.symm_apply_apply x
  right_inv := fun y _ => e.apply_symm_apply y
  map_face := fun S hS => isExposed_image_affineMap_of_injective e.toAffineMap e.injective hS
  inv_face := by
    intro T hT
    have h := isExposed_image_affineMap_of_injective e.symm.toAffineMap e.symm.injective hT
    simp only [LinearMap.coe_toAffineMap, LinearEquiv.coe_coe] at h
    have hP : e.symm '' (e '' P) = P := by
      apply Set.Subset.antisymm
      · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        simpa only [LinearEquiv.symm_apply_apply] using hx
      · intro x hx
        exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
    rwa [hP] at h

theorem exists_orderIso {P : Set E} {Q : Set F} (e : ExposedFaceBijection P Q) :
    ∃ Φ : {S : Set E // IsExposed ℝ P S} ≃o
        {T : Set F // IsExposed ℝ Q T},
      ∀ S, (Φ S).val = e.toFun '' S.val :=
  exposedFaces_orderIso_of_inverse_images P Q e.toFun e.invFun
    e.left_inv e.right_inv e.map_face e.inv_face

end ExposedFaceBijection
end Grunbaum2003


-- Local ingredient: DeformedIntervalOrder

set_option autoImplicit false

namespace Grunbaum2003

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

                                                                        
                                                                           
                                                                            
noncomputable def deformedIntervalFaceBijection (P : Set E)
    (f : E →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P, 0 < f x) :
    ExposedFaceBijection
      {z : E × ℝ | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1}
      {z : E × ℝ | z.1 ∈ P ∧ -1 ≤ z.2 ∧ z.2 ≤ 1} := by
  classical
  let C : Set (E × ℝ) := {z | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1}
  let Q : Set (E × ℝ) := {z | z.1 ∈ P ∧ -1 ≤ z.2 ∧ z.2 ≤ 1}
  let φ : (E × ℝ) → (E × ℝ) := fun z => (z.1, z.2 / f z.1)
  let ψ : (E × ℝ) → (E × ℝ) := fun z => (z.1, z.2 * f z.1)
  have hGF : ∀ z ∈ C, ψ (φ z) = z :=
    fun z hz => normalize_fiber_inverse_left P f hf z hz.1
  have hFG : ∀ z ∈ Q, φ (ψ z) = z :=
    fun z hz => normalize_fiber_inverse_right P f hf z hz.1
  have hInvImage {S : Set (E × ℝ)} (hS : S ⊆ C) : ψ '' (φ '' S) = S := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [hGF z (hS hz)] using hz
    · intro z hz
      exact ⟨φ z, ⟨z, hz, rfl⟩, hGF z (hS hz)⟩
  have hFixed (F : Set E) (hF : IsExposed ℝ P F) :
      IsExposed ℝ Q {z : E × ℝ | z.1 ∈ F ∧ z.2 = 1} ∧
      IsExposed ℝ Q {z : E × ℝ | z.1 ∈ F ∧ z.2 = -1} ∧
      IsExposed ℝ Q {z : E × ℝ | z.1 ∈ F ∧ -1 ≤ z.2 ∧ z.2 ≤ 1} :=
    deformed_interval_faces_of_base P (AffineMap.const ℝ E 1)
      (fun _ _ => zero_le_one) F hF
  have hFaces : ∀ S : Set (E × ℝ), IsExposed ℝ C S → IsExposed ℝ Q (φ '' S) := by
    intro S hS
    obtain ⟨F, hF, hCases⟩ := deformed_interval_face_classification P f
      (fun x hx => (hf x hx).le) S hS
    change IsExposed ℝ Q ((fun z : E × ℝ => (z.1, z.2 / f z.1)) '' S)
    rcases hCases with hUp | hLo | hFree
    · rw [hUp, normalize_fiber_upper_image P F f hf hF.subset]
      exact (hFixed F hF).1
    · rw [hLo, normalize_fiber_lower_image P F f hf hF.subset]
      exact (hFixed F hF).2.1
    · rw [hFree, normalize_fiber_interval_image P F f hf hF.subset]
      exact (hFixed F hF).2.2
  have hBack : ∀ T : Set (E × ℝ), IsExposed ℝ Q T → IsExposed ℝ C (ψ '' T) := by
    intro T hT
    obtain ⟨F, hF, hCases⟩ := deformed_interval_face_classification P
      (AffineMap.const ℝ E 1) (fun _ _ => zero_le_one) T hT
    change (T = {z : E × ℝ | z.1 ∈ F ∧ z.2 = 1} ∨
      T = {z : E × ℝ | z.1 ∈ F ∧ z.2 = -1} ∨
      T = {z : E × ℝ | z.1 ∈ F ∧ -1 ≤ z.2 ∧ z.2 ≤ 1}) at hCases
    have hOfImage {S : Set (E × ℝ)} (hS : IsExposed ℝ C S)
        (hImage : φ '' S = T) : IsExposed ℝ C (ψ '' T) := by
      rw [← hImage, hInvImage hS.subset]
      exact hS
    have hSource := deformed_interval_faces_of_base P f (fun x hx => (hf x hx).le) F hF
    rcases hCases with hUp | hLo | hFree
    · apply hOfImage hSource.1
      change (fun z : E × ℝ => (z.1, z.2 / f z.1)) ''
        {z : E × ℝ | z.1 ∈ F ∧ z.2 = f z.1} = T
      rw [normalize_fiber_upper_image P F f hf hF.subset]
      exact hUp.symm
    · apply hOfImage hSource.2.1
      change (fun z : E × ℝ => (z.1, z.2 / f z.1)) ''
        {z : E × ℝ | z.1 ∈ F ∧ z.2 = -f z.1} = T
      rw [normalize_fiber_lower_image P F f hf hF.subset]
      exact hLo.symm
    · apply hOfImage hSource.2.2
      change (fun z : E × ℝ => (z.1, z.2 / f z.1)) ''
        {z : E × ℝ | z.1 ∈ F ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1} = T
      rw [normalize_fiber_interval_image P F f hf hF.subset]
      exact hFree.symm
  have hImage : φ '' C = Q := normalize_fiber_interval_image P P f hf Set.Subset.rfl
  exact {
    toFun := φ
    invFun := ψ
    map_mem := by
      intro z hz
      change φ z ∈ Q
      rw [← hImage]
      exact ⟨z, hz, rfl⟩
    inv_mem := by
      intro z hz
      change z ∈ Q at hz
      change ψ z ∈ C
      rw [← hImage] at hz
      obtain ⟨x, hx, hxz⟩ := hz
      rw [← hxz, hGF x hx]
      exact hx
    left_inv := hGF
    right_inv := hFG
    map_face := hFaces
    inv_face := hBack }

                                                                          
                                                                        
                                                              
theorem deformed_interval_faces_orderIso_product (P : Set E)
    (f : E →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P, 0 < f x) :
    let C := {z : E × ℝ | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1}
    let Q := {z : E × ℝ | z.1 ∈ P ∧ -1 ≤ z.2 ∧ z.2 ≤ 1}
    ∃ Φ : {S : Set (E × ℝ) // IsExposed ℝ C S} ≃o
        {T : Set (E × ℝ) // IsExposed ℝ Q T},
      ∀ S, (Φ S).val = (fun z : E × ℝ => (z.1, z.2 / f z.1)) '' S.val := by
  exact (deformedIntervalFaceBijection P f hf).exists_orderIso

end Grunbaum2003


-- Local ingredient: IntervalProductBijection

set_option autoImplicit false

namespace Grunbaum2003

                                                                     
theorem product_map_fibers_image {E F : Type*} (f : E → F)
    (S : Set E) (I : Set ℝ) :
    (fun z : E × ℝ => (f z.1, z.2)) '' {z | z.1 ∈ S ∧ z.2 ∈ I} =
      {z : F × ℝ | z.1 ∈ f '' S ∧ z.2 ∈ I} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, ⟨hz, ht⟩, rfl⟩
    exact ⟨⟨z.1, hz, rfl⟩, ht⟩
  · rintro ⟨y, t⟩ ⟨⟨x, hx, hxy⟩, ht⟩
    exact ⟨(x, t), ⟨hx, ht⟩, Prod.ext hxy rfl⟩

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

                                                                         
                                                                
theorem isExposed_interval_product_image
    (P : Set E) (Q : Set F) (f : E → F)
    (hMap : ∀ A : Set E, IsExposed ℝ P A → IsExposed ℝ Q (f '' A))
    (S : Set (E × ℝ))
    (hS : IsExposed ℝ {z : E × ℝ | z.1 ∈ P ∧ -1 ≤ z.2 ∧ z.2 ≤ 1} S) :
    IsExposed ℝ {z : F × ℝ | z.1 ∈ Q ∧ -1 ≤ z.2 ∧ z.2 ≤ 1}
      ((fun z : E × ℝ => (f z.1, z.2)) '' S) := by
  obtain ⟨A, hA, hCases⟩ := deformed_interval_face_classification P
    (AffineMap.const ℝ E 1) (fun _ _ => zero_le_one) S hS
  change (S = {z : E × ℝ | z.1 ∈ A ∧ z.2 = 1} ∨
    S = {z : E × ℝ | z.1 ∈ A ∧ z.2 = -1} ∨
    S = {z : E × ℝ | z.1 ∈ A ∧ -1 ≤ z.2 ∧ z.2 ≤ 1}) at hCases
  have hTarget := deformed_interval_faces_of_base Q (AffineMap.const ℝ F 1)
    (fun _ _ => zero_le_one) (f '' A) (hMap A hA)
  have hGraph (c : ℝ) :
      (fun z : E × ℝ => (f z.1, z.2)) '' {z | z.1 ∈ A ∧ z.2 = c} =
        {z : F × ℝ | z.1 ∈ f '' A ∧ z.2 = c} := by
    simpa only [Set.mem_singleton_iff] using product_map_fibers_image f A {c}
  have hFree :
      (fun z : E × ℝ => (f z.1, z.2)) ''
          {z | z.1 ∈ A ∧ -1 ≤ z.2 ∧ z.2 ≤ 1} =
        {z : F × ℝ | z.1 ∈ f '' A ∧ -1 ≤ z.2 ∧ z.2 ≤ 1} := by
    exact product_map_fibers_image f A (Set.Icc (-1) 1)
  rcases hCases with hUp | hLo | hAll
  · rw [hUp, hGraph]
    exact hTarget.1
  · rw [hLo, hGraph]
    exact hTarget.2.1
  · rw [hAll, hFree]
    exact hTarget.2.2

                                                                         
                                                                                  
noncomputable def ExposedFaceBijection.prodInterval
    {P : Set E} {Q : Set F} (e : ExposedFaceBijection P Q) :
    ExposedFaceBijection
      {z : E × ℝ | z.1 ∈ P ∧ -1 ≤ z.2 ∧ z.2 ≤ 1}
      {z : F × ℝ | z.1 ∈ Q ∧ -1 ≤ z.2 ∧ z.2 ≤ 1} where
  toFun := fun z => (e.toFun z.1, z.2)
  invFun := fun z => (e.invFun z.1, z.2)
  map_mem := fun z hz => ⟨e.map_mem z.1 hz.1, hz.2⟩
  inv_mem := fun z hz => ⟨e.inv_mem z.1 hz.1, hz.2⟩
  left_inv := fun z hz => Prod.ext (e.left_inv z.1 hz.1) rfl
  right_inv := fun z hz => Prod.ext (e.right_inv z.1 hz.1) rfl
  map_face := isExposed_interval_product_image P Q e.toFun e.map_face
  inv_face := isExposed_interval_product_image Q P e.invFun e.inv_face

end Grunbaum2003


-- Local ingredient: SnocCoordinates

set_option autoImplicit false

namespace Grunbaum2003

                                                                           
def snocLinearEquiv (n : ℕ) :
    ((Fin n → ℝ) × ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun := fun z => Fin.snoc z.1 z.2
  invFun := fun x => (Fin.init x, x (Fin.last n))
  left_inv := by
    intro z
    apply Prod.ext <;> simp only [Fin.init_snoc, Fin.snoc_last]
  right_inv := Fin.snoc_init_self
  map_add' := by
    intro x y
    ext i
    cases i using Fin.lastCases <;> simp
  map_smul' := by
    intro a x
    ext i
    cases i using Fin.lastCases <;> simp

theorem snocLinearEquiv_apply (n : ℕ) (z : (Fin n → ℝ) × ℝ) :
    snocLinearEquiv n z = Fin.snoc z.1 z.2 := rfl

                                                                           
theorem snocLinearEquiv_image_centered_cube (n : ℕ) :
    snocLinearEquiv n ''
        {z : (Fin n → ℝ) × ℝ |
          (∀ i, -1 ≤ z.1 i ∧ z.1 i ≤ 1) ∧ -1 ≤ z.2 ∧ z.2 ≤ 1} =
      {x : Fin (n + 1) → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, ⟨hz, hLast⟩, rfl⟩ i
    cases i using Fin.lastCases with
    | last => simpa only [snocLinearEquiv_apply, Fin.snoc_last] using hLast
    | cast i => simpa only [snocLinearEquiv_apply, Fin.snoc_castSucc] using hz i
  · intro x hx
    refine ⟨(Fin.init x, x (Fin.last n)), ⟨fun i => hx i.castSucc, hx (Fin.last n)⟩, ?_⟩
    exact Fin.snoc_init_self x

end Grunbaum2003


-- Local ingredient: NativeCubeStep

set_option autoImplicit false

namespace Grunbaum2003

                                                                       
                                                                           
noncomputable def nativeDeformedCubeBijection {n : ℕ} (P : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P, 0 < f x)
    (e : ExposedFaceBijection P {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1}) :
    ExposedFaceBijection
      (snocLinearEquiv n ''
        {z : (Fin n → ℝ) × ℝ | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1})
      {x : Fin (n + 1) → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1} := by
  let C : Set ((Fin n → ℝ) × ℝ) :=
    {z | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1}
  let source := ExposedFaceBijection.ofLinearEquiv (snocLinearEquiv n) C
  let target := (ExposedFaceBijection.ofLinearEquiv (snocLinearEquiv n)
    {z : (Fin n → ℝ) × ℝ |
      (∀ i, -1 ≤ z.1 i ∧ z.1 i ≤ 1) ∧ -1 ≤ z.2 ∧ z.2 ≤ 1}).congr
        rfl (snocLinearEquiv_image_centered_cube n)
  exact source.symm.trans
    ((deformedIntervalFaceBijection P f hf).trans (e.prodInterval.trans target))

                                                                          
                                                                 
theorem nativeDeformedCubeBijection_toFun {n : ℕ} (P : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P, 0 < f x)
    (e : ExposedFaceBijection P {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1})
    (x : Fin (n + 1) → ℝ) :
    (nativeDeformedCubeBijection P f hf e).toFun x =
      Fin.snoc (e.toFun (Fin.init x)) (x (Fin.last n) / f (Fin.init x)) := rfl

end Grunbaum2003


-- Local ingredient: DeformedIntervalHull

set_option autoImplicit false

namespace Grunbaum2003

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

                                                                              
                                              
theorem convex_deformed_interval {P : Set E} (hP : Convex ℝ P)
    (f : E →ᵃ[ℝ] ℝ) :
    Convex ℝ {z : E × ℝ | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1} := by
  let fstA : (E × ℝ) →ᵃ[ℝ] E := (LinearMap.fst ℝ E ℝ).toAffineMap
  let sndA : (E × ℝ) →ᵃ[ℝ] ℝ := (LinearMap.snd ℝ E ℝ).toAffineMap
  let lo : (E × ℝ) →ᵃ[ℝ] ℝ := sndA + f.comp fstA
  let up : (E × ℝ) →ᵃ[ℝ] ℝ := sndA - f.comp fstA
  have hSet : {z : E × ℝ | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1} =
      fstA ⁻¹' P ∩ (lo ⁻¹' Set.Ici 0 ∩ up ⁻¹' Set.Iic 0) := by
    ext z
    change (z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1) ↔
      (z.1 ∈ P ∧ 0 ≤ z.2 + f z.1 ∧ z.2 - f z.1 ≤ 0)
    constructor <;> rintro ⟨hz, h₁, h₂⟩ <;> exact ⟨hz, by linarith, by linarith⟩
  rw [hSet]
  exact (hP.affine_preimage fstA).inter
    (((convex_Ici (0 : ℝ)).affine_preimage lo).inter
      ((convex_Iic (0 : ℝ)).affine_preimage up))

                                                                            
                                                                         
                                 
theorem deformed_interval_convexHull (V : Set E) (f : E →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ convexHull ℝ V, 0 ≤ f x) :
    {z : E × ℝ | z.1 ∈ convexHull ℝ V ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1} =
      convexHull ℝ (((AffineMap.id ℝ E).prod f) '' V ∪
        ((AffineMap.id ℝ E).prod (-f)) '' V) := by
  let P : Set E := convexHull ℝ V
  let C : Set (E × ℝ) := {z | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1}
  let upper : E →ᵃ[ℝ] (E × ℝ) := (AffineMap.id ℝ E).prod f
  let lower : E →ᵃ[ℝ] (E × ℝ) := (AffineMap.id ℝ E).prod (-f)
  let W : Set (E × ℝ) := upper '' V ∪ lower '' V
  have hGraphUpper : ∀ x ∈ P, upper x ∈ C := by
    intro x hx
    exact ⟨hx, by change -f x ≤ f x; linarith [hf x hx], le_rfl⟩
  have hGraphLower : ∀ x ∈ P, lower x ∈ C := by
    intro x hx
    exact ⟨hx, le_rfl, by change -f x ≤ f x; linarith [hf x hx]⟩
  have hW : W ⊆ C := by
    rintro _ (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact hGraphUpper x (subset_convexHull ℝ V hx)
    · exact hGraphLower x (subset_convexHull ℝ V hx)
  have hHull : convexHull ℝ W ⊆ C :=
    convexHull_min hW (convex_deformed_interval (convex_convexHull ℝ V) f)
  have hUpper : upper '' P ⊆ convexHull ℝ W := by
    change upper '' convexHull ℝ V ⊆ _
    rw [upper.image_convexHull]
    exact convexHull_mono Set.subset_union_left
  have hLower : lower '' P ⊆ convexHull ℝ W := by
    change lower '' convexHull ℝ V ⊆ _
    rw [lower.image_convexHull]
    exact convexHull_mono Set.subset_union_right
  apply Set.Subset.antisymm
  · intro z hz
    have hLo : (z.1, -f z.1) ∈ convexHull ℝ W := hLower ⟨z.1, hz.1, rfl⟩
    have hUp : (z.1, f z.1) ∈ convexHull ℝ W := hUpper ⟨z.1, hz.1, rfl⟩
    apply (convex_convexHull ℝ W).segment_subset hLo hUp
    rw [← Prod.image_mk_segment_right (𝕜 := ℝ) (x := z.1)
      (y₁ := -f z.1) (y₂ := f z.1)]
    exact ⟨z.2, Icc_subset_segment hz.2, rfl⟩
  · exact hHull

                                                                               
theorem deformed_interval_finite_generators (V : Set E) (hV : V.Finite)
    (f : E →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ convexHull ℝ V, 0 ≤ f x) :
    ∃ W : Set (E × ℝ), W.Finite ∧
      {z : E × ℝ | z.1 ∈ convexHull ℝ V ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1} =
        convexHull ℝ W := by
  exact ⟨_, (hV.image _).union (hV.image _), deformed_interval_convexHull V f hf⟩

end Grunbaum2003


-- Local ingredient: DeformedIntervalSpan

set_option autoImplicit false

namespace Grunbaum2003

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

                                                                            
                                                         
theorem deformed_interval_interior_nonempty (P : Set E) (hP : Convex ℝ P)
    (hSpan : affineSpan ℝ P = ⊤) (f : E →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P, 0 < f x) :
    (interior {z : E × ℝ | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1}).Nonempty := by
  obtain ⟨x₀, hx₀⟩ := hP.interior_nonempty_iff_affineSpan_eq_top.mpr hSpan
  have hf₀ := hf x₀ (interior_subset hx₀)
  have hfc : Continuous f := f.continuous_of_finiteDimensional
  let O : Set (E × ℝ) :=
    {z | z.1 ∈ interior P ∧ -f z.1 < z.2 ∧ z.2 < f z.1}
  have hOpen : IsOpen O :=
    (isOpen_interior.preimage continuous_fst).inter
      ((isOpen_lt (hfc.comp continuous_fst).neg continuous_snd).inter
        (isOpen_lt continuous_snd (hfc.comp continuous_fst)))
  refine ⟨(x₀, 0), mem_interior.mpr ⟨O, ?_, hOpen, ?_⟩⟩
  · intro z hz
    exact ⟨interior_subset hz.1, hz.2.1.le, hz.2.2.le⟩
  · exact ⟨hx₀, by linarith, hf₀⟩

                                                                           
                                     
theorem deformed_interval_affineSpan_eq_top (P : Set E) (hP : Convex ℝ P)
    (hSpan : affineSpan ℝ P = ⊤) (f : E →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P, 0 < f x) :
    affineSpan ℝ {z : E × ℝ | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1} = ⊤ := by
  apply affineSpan_eq_top_of_nonempty_interior
  exact (deformed_interval_interior_nonempty P hP hSpan f hf).mono
    (interior_mono (subset_convexHull ℝ _))

end Grunbaum2003


-- Local ingredient: DeformedIntervalPolytope

set_option autoImplicit false

namespace Grunbaum2003

                                                                        
                                                                                
theorem isDPolytope_deformed_interval {n : ℕ} (P : Set (Fin n → ℝ))
    (hP : IsDPolytope P) (f : (Fin n → ℝ) →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P, 0 < f x) :
    IsDPolytope (snocLinearEquiv n ''
      {z : (Fin n → ℝ) × ℝ | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1}) := by
  classical
  obtain ⟨⟨V, hV, hVne, hHull⟩, hSpan⟩ := hP
  let C : Set ((Fin n → ℝ) × ℝ) := {z | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1}
  let upper : (Fin n → ℝ) →ᵃ[ℝ] ((Fin n → ℝ) × ℝ) := (AffineMap.id ℝ _).prod f
  let lower : (Fin n → ℝ) →ᵃ[ℝ] ((Fin n → ℝ) × ℝ) := (AffineMap.id ℝ _).prod (-f)
  let W : Set ((Fin n → ℝ) × ℝ) := upper '' V ∪ lower '' V
  have hW : W.Finite := (hV.image upper).union (hV.image lower)
  have hWne : W.Nonempty := (hVne.image upper).mono Set.subset_union_left
  have hC : C = convexHull ℝ W := by
    change {z : (Fin n → ℝ) × ℝ | z.1 ∈ P ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1} = _
    rw [hHull]
    exact deformed_interval_convexHull V f (fun x hx => (hf x (hHull ▸ hx)).le)
  let e := snocLinearEquiv n
  have hImage : e '' C = convexHull ℝ (e '' W) := by
    rw [hC]
    simpa only [LinearEquiv.coe_coe] using e.toLinearMap.image_convexHull W
  have hCSpan : affineSpan ℝ C = ⊤ :=
    deformed_interval_affineSpan_eq_top P (hHull ▸ convex_convexHull ℝ V) hSpan f hf
  have hImageSpan : affineSpan ℝ (e '' C) = ⊤ := by
    simpa only [LinearMap.coe_toAffineMap, LinearEquiv.coe_coe] using
      e.toAffineMap.span_eq_top_of_surjective e.surjective hCSpan
  exact ⟨⟨e '' W, hW.image e, hWne.image e, hImage⟩, hImageSpan⟩

end Grunbaum2003


-- Local ingredient: PositiveAffineWidth

set_option autoImplicit false

namespace Grunbaum2003

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

                                                                           
                                                                       
                                                                          
theorem exists_positive_affine_width (V : Set E) (hV : V.Finite)
    (l : E →ₗ[ℝ] ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ b : ℝ, ∃ f : E →ᵃ[ℝ] ℝ,
      (∀ x, f x = (b - l x) / ε) ∧
        ∀ x ∈ convexHull ℝ V, 0 < f x := by
  obtain ⟨M, hM⟩ := (hV.image l).bddAbove
  have hBound : ∀ x ∈ convexHull ℝ V, l x ≤ M :=
    convexHull_min (fun x hx => hM ⟨x, hx, rfl⟩)
      ((convex_Iic M).linear_preimage l)
  let f : E →ᵃ[ℝ] ℝ := ε⁻¹ • (AffineMap.const ℝ E (M + 1) - l.toAffineMap)
  have hApply (x : E) : f x = (M + 1 - l x) / ε := by
    change ε⁻¹ * (M + 1 - l x) = (M + 1 - l x) / ε
    rw [div_eq_mul_inv, mul_comm]
  refine ⟨M + 1, f, hApply, ?_⟩
  intro x hx
  rw [hApply]
  exact div_pos (by linarith [hBound x hx]) hε

end Grunbaum2003


-- Local ingredient: TriangularConstraints

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem abs_mul_le_iff_affine_interval (a t ε : ℝ) (hε : 0 < ε) :
    |ε * t| ≤ a ↔ -(a / ε) ≤ t ∧ t ≤ a / ε := by
  rw [abs_le]
  constructor
  · rintro ⟨hLo, hUp⟩
    constructor
    · rw [← neg_div]
      exact (div_le_iff₀ hε).mpr (by simpa only [mul_comm] using hLo)
    · exact (le_div_iff₀ hε).mpr (by simpa only [mul_comm] using hUp)
  · rintro ⟨hLo, hUp⟩
    rw [← neg_div] at hLo
    exact ⟨by simpa only [mul_comm] using (div_le_iff₀ hε).mp hLo,
      by simpa only [mul_comm] using (le_div_iff₀ hε).mp hUp⟩

theorem lower_triangular_sum_castSucc {n : ℕ}
    (B : Fin (n + 1) → Fin (n + 1) → ℝ) (x : Fin (n + 1) → ℝ) (i : Fin n) :
    (∑ j : Fin (n + 1), if j < i.castSucc then B i.castSucc j * x j else 0) =
      ∑ j : Fin n, if j < i then B i.castSucc j.castSucc * x j.castSucc else 0 := by
  have hLast : ¬ Fin.last n < i.castSucc := by
    intro h
    have hi := i.isLt
    change n < i.val at h
    omega
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.castSucc_lt_castSucc_iff, if_neg hLast, add_zero]

theorem lower_triangular_sum_last {n : ℕ}
    (B : Fin (n + 1) → Fin (n + 1) → ℝ) (x : Fin (n + 1) → ℝ) :
    (∑ j : Fin (n + 1), if j < Fin.last n then B (Fin.last n) j * x j else 0) =
      ∑ j : Fin n, B (Fin.last n) j.castSucc * x j.castSucc := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.castSucc_lt_last, if_true, lt_self_iff_false, if_false, add_zero]

                                                                        
                                                        
theorem triangular_constraints_snoc_iff {n : ℕ}
    (B : Fin (n + 1) → Fin (n + 1) → ℝ)
    (ε : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (bLast : ℝ)
    (hε : 0 < ε (Fin.last n)) (f : (Fin n → ℝ) → ℝ)
    (hf : ∀ y, f y = (bLast - ∑ j : Fin n, B (Fin.last n) j.castSucc * y j) /
      ε (Fin.last n)) (x : Fin (n + 1) → ℝ) :
    (∀ i : Fin (n + 1), |ε i * x i| ≤ (Fin.snoc b bLast : Fin (n + 1) → ℝ) i -
      ∑ j : Fin (n + 1), if j < i then B i j * x j else 0) ↔
    (∀ i : Fin n, |ε i.castSucc * x i.castSucc| ≤ b i -
      ∑ j : Fin n, if j < i then B i.castSucc j.castSucc * x j.castSucc else 0) ∧
      -f (Fin.init x) ≤ x (Fin.last n) ∧ x (Fin.last n) ≤ f (Fin.init x) := by
  rw [Fin.forall_iff_castSucc]
  simp_rw [Fin.snoc_last, Fin.snoc_castSucc, lower_triangular_sum_last,
    lower_triangular_sum_castSucc]
  rw [abs_mul_le_iff_affine_interval _ _ _ hε, hf]
  exact and_comm

end Grunbaum2003


-- Local ingredient: TriangularCube

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

                                                                         
                                                                              
                                                                              
                                                                        
theorem exists_triangular_cube (n : ℕ) :
    ∀ (B : Fin n → Fin n → ℝ) (ε : Fin n → ℝ), (∀ i, 0 < ε i) →
    ∃ b : Fin n → ℝ,
      let P : Set (Fin n → ℝ) :=
        {x | ∀ i, |ε i * x i| ≤ b i - ∑ j : Fin n, if j < i then B i j * x j else 0}
      IsDPolytope P ∧
        ∃ e : ExposedFaceBijection P {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1},
          ∀ x ∈ P, ∀ i,
            0 < b i - (∑ j : Fin n, if j < i then B i j * x j else 0) ∧
            e.toFun x i = ε i * x i /
              (b i - ∑ j : Fin n, if j < i then B i j * x j else 0) := by
  induction n with
  | zero =>
    intro B ε _
    let b : Fin 0 → ℝ := fun i => Fin.elim0 i
    let P : Set (Fin 0 → ℝ) :=
      {x | ∀ i, |ε i * x i| ≤ b i - ∑ j : Fin 0, if j < i then B i j * x j else 0}
    have hPUniv : P = Set.univ := Set.eq_univ_of_forall (fun _ i => Fin.elim0 i)
    have hBoxUniv : {x : Fin 0 → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1} = Set.univ :=
      Set.eq_univ_of_forall (fun _ i => Fin.elim0 i)
    have hP : IsDPolytope P := by
      constructor
      · refine ⟨{0}, Set.finite_singleton _, Set.singleton_nonempty _, ?_⟩
        rw [hPUniv, convexHull_singleton]
        ext x
        simp only [Set.mem_univ, Set.mem_singleton_iff, true_iff]
        exact Subsingleton.elim x 0
      · rw [hPUniv, AffineSubspace.span_univ]
    refine ⟨b, hP, (ExposedFaceBijection.refl P).congr rfl
      (hPUniv.trans hBoxUniv.symm), ?_⟩
    intro x hx i
    exact Fin.elim0 i
  | succ n ih =>
    intro B ε hε
    let B₀ : Fin n → Fin n → ℝ := fun i j => B i.castSucc j.castSucc
    let ε₀ : Fin n → ℝ := fun i => ε i.castSucc
    obtain ⟨b₀, hP₀, e₀, hCoordinates₀⟩ := ih B₀ ε₀ (fun i => hε i.castSucc)
    let P₀ : Set (Fin n → ℝ) :=
      {x | ∀ i, |ε₀ i * x i| ≤ b₀ i - ∑ j : Fin n, if j < i then B₀ i j * x j else 0}
    obtain ⟨V, hV, _, hHull⟩ := hP₀.1
    let l : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
      ∑ j : Fin n, B (Fin.last n) j.castSucc • (LinearMap.proj j)
    have hl (y : Fin n → ℝ) : l y = ∑ j : Fin n, B (Fin.last n) j.castSucc * y j := by
      simp only [l, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
    obtain ⟨bLast, f, hf, hPositive⟩ := exists_positive_affine_width V hV l
      (ε (Fin.last n)) (hε (Fin.last n))
    have hfP : ∀ y ∈ P₀, 0 < f y := by
      intro y hy
      apply hPositive y
      rwa [← hHull]
    have hfFormula (y : Fin n → ℝ) :
        f y = (bLast - ∑ j : Fin n, B (Fin.last n) j.castSucc * y j) / ε (Fin.last n) := by
      rw [hf, hl]
    let b : Fin (n + 1) → ℝ := Fin.snoc b₀ bLast
    let P : Set (Fin (n + 1) → ℝ) :=
      {x | ∀ i, |ε i * x i| ≤ b i - ∑ j : Fin (n + 1), if j < i then B i j * x j else 0}
    let C : Set ((Fin n → ℝ) × ℝ) :=
      {z | z.1 ∈ P₀ ∧ -f z.1 ≤ z.2 ∧ z.2 ≤ f z.1}
    have hSplit (x : Fin (n + 1) → ℝ) : x ∈ P ↔
        Fin.init x ∈ P₀ ∧ -f (Fin.init x) ≤ x (Fin.last n) ∧
          x (Fin.last n) ≤ f (Fin.init x) :=
      triangular_constraints_snoc_iff B ε b₀ bLast (hε (Fin.last n)) f hfFormula x
    have hImage : P = snocLinearEquiv n '' C := by
      apply Set.Subset.antisymm
      · intro x hx
        exact ⟨(Fin.init x, x (Fin.last n)), (hSplit x).mp hx, Fin.snoc_init_self x⟩
      · rintro _ ⟨z, hz, rfl⟩
        apply (hSplit (snocLinearEquiv n z)).mpr
        simpa only [C, Set.mem_ofPred_eq, snocLinearEquiv_apply,
          Fin.init_snoc, Fin.snoc_last] using hz
    have hP : IsDPolytope P := by
      rw [hImage]
      exact isDPolytope_deformed_interval P₀ hP₀ f hfP
    let e := (nativeDeformedCubeBijection P₀ f hfP e₀).congr hImage.symm rfl
    refine ⟨b, hP, e, ?_⟩
    intro x hx i
    have hx₀ : Fin.init x ∈ P₀ := ((hSplit x).mp hx).1
    cases i using Fin.lastCases with
    | cast i =>
      obtain ⟨hPos, hEq⟩ := hCoordinates₀ (Fin.init x) hx₀ i
      constructor
      · simpa only [b, B₀, ε₀, Fin.init, Fin.snoc_castSucc,
          lower_triangular_sum_castSucc] using hPos
      · change (nativeDeformedCubeBijection P₀ f hfP e₀).toFun x i.castSucc = _
        rw [nativeDeformedCubeBijection_toFun, Fin.snoc_castSucc]
        simpa only [b, B₀, ε₀, Fin.init, Fin.snoc_castSucc,
          lower_triangular_sum_castSucc] using hEq
    | last =>
      have hPos : 0 < bLast - ∑ j : Fin n, B (Fin.last n) j.castSucc * x j.castSucc := by
        have h := hfP (Fin.init x) hx₀
        rw [hfFormula] at h
        exact (div_pos_iff_of_pos_right (hε (Fin.last n))).mp h
      constructor
      · simpa only [b, Fin.snoc_last, lower_triangular_sum_last] using hPos
      · change (nativeDeformedCubeBijection P₀ f hfP e₀).toFun x (Fin.last n) = _
        rw [nativeDeformedCubeBijection_toFun, Fin.snoc_last, hfFormula]
        simp only [b, Fin.snoc_last, lower_triangular_sum_last]
        rw [div_div_eq_mul_div, mul_comm]
        rfl

end Grunbaum2003


-- Local ingredient: NeighborlyCubeData

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

                                                                             
theorem extend_discarded_coefficients_at {n m : ℕ} (hm : m ≤ n)
    (B : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) (j : Fin m) :
    (fun r k : Fin n => if h : k.val < m then B r ⟨k.val, h⟩ else 0)
      i (Fin.castLE hm j) = B i j := by
  simp only [Fin.coe_castLE, j.isLt, dite_true]

                                                                         
                                                                          
                                                                             
theorem exists_neighborly_cube_data {n d : ℕ} (hd : 2 ≤ d) (hdn : d < n) :
    ∃ B : Matrix (Fin n) (Fin (n - d)) ℝ, ∃ δ : ℝ, ∃ b : Fin n → ℝ,
      0 < δ ∧
      let fullB : Fin n → Fin n → ℝ :=
        fun i j => if h : j.val < n - d then B i ⟨j.val, h⟩ else 0
      let P : Set (Fin n → ℝ) := {x | ∀ i, |δ * x i| ≤ b i -
        ∑ j : Fin n, if j < i then fullB i j * x j else 0}
      IsDPolytope P ∧
      (∃ e : ExposedFaceBijection P {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1},
        ∀ x ∈ P, ∀ i,
          0 < b i - (∑ j : Fin n, if j < i then fullB i j * x j else 0) ∧
          e.toFun x i = δ * x i /
            (b i - ∑ j : Fin n, if j < i then fullB i j * x j else 0)) ∧
      (∀ J : Finset (Fin n), J.card ≤ d / 2 - 1 → ∀ σ : Fin n → Bool,
        (∃ weight : {i : Fin n // i ∉ J} → ℝ,
          (∀ i, 0 < weight i) ∧ (∑ i, weight i • (fun j : Fin (n - d) =>
            if j.val < i.val.val then B i.val j else if j.val = i.val.val then
              (if σ i.val then δ else -δ) else 0)) = 0) ∧
        Submodule.span ℝ (Set.range (fun i : {i : Fin n // i ∉ J} =>
          fun j : Fin (n - d) => if j.val < i.val.val then B i.val j
            else if j.val = i.val.val then (if σ i.val then δ else -δ) else 0)) = ⊤) ∧
      (∀ u : Fin (n - d) → Fin n, StrictMono u → ∀ σ : Fin n → Bool,
        Matrix.det (fun i j : Fin (n - d) =>
          if j.val < (u i).val then B (u i) j else if j.val = (u i).val then
            (if σ (u i) then δ else -δ) else 0) ≠ 0) := by
  obtain ⟨B, δ, hδ, hPositive, hGeneric⟩ := exists_neighborly_triangular_coefficients hd hdn
  let fullB : Fin n → Fin n → ℝ :=
    fun i j => if h : j.val < n - d then B i ⟨j.val, h⟩ else 0
  obtain ⟨b, hP, e, hCoordinates⟩ := exists_triangular_cube n fullB (fun _ => δ) (fun _ => hδ)
  exact ⟨B, δ, b, hδ, hP, ⟨e, hCoordinates⟩, hPositive, hGeneric⟩

end Grunbaum2003


-- Local ingredient: NeighborlyCubeDataCast

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

                                                                          
                                                                           
                                                    
theorem exists_neighborly_cube_data_sub_eq {n d m : ℕ}
    (hd : 2 ≤ d) (hdn : d < n) (hmd : n - d = m) :
    ∃ B : Matrix (Fin n) (Fin (m)) ℝ, ∃ δ : ℝ, ∃ b : Fin n → ℝ,
      0 < δ ∧
      let fullB : Fin n → Fin n → ℝ :=
        fun i j => if h : j.val < m then B i ⟨j.val, h⟩ else 0
      let P : Set (Fin n → ℝ) := {x | ∀ i, |δ * x i| ≤ b i -
        ∑ j : Fin n, if j < i then fullB i j * x j else 0}
      IsDPolytope P ∧
      (∃ e : ExposedFaceBijection P {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1},
        ∀ x ∈ P, ∀ i,
          0 < b i - (∑ j : Fin n, if j < i then fullB i j * x j else 0) ∧
          e.toFun x i = δ * x i /
            (b i - ∑ j : Fin n, if j < i then fullB i j * x j else 0)) ∧
      (∀ J : Finset (Fin n), J.card ≤ d / 2 - 1 → ∀ σ : Fin n → Bool,
        (∃ weight : {i : Fin n // i ∉ J} → ℝ,
          (∀ i, 0 < weight i) ∧ (∑ i, weight i • (fun j : Fin (m) =>
            if j.val < i.val.val then B i.val j else if j.val = i.val.val then
              (if σ i.val then δ else -δ) else 0)) = 0) ∧
        Submodule.span ℝ (Set.range (fun i : {i : Fin n // i ∉ J} =>
          fun j : Fin (m) => if j.val < i.val.val then B i.val j
            else if j.val = i.val.val then (if σ i.val then δ else -δ) else 0)) = ⊤) ∧
      (∀ u : Fin (m) → Fin n, StrictMono u → ∀ σ : Fin n → Bool,
        Matrix.det (fun i j : Fin (m) =>
          if j.val < (u i).val then B (u i) j else if j.val = (u i).val then
            (if σ (u i) then δ else -δ) else 0) ≠ 0) := by
  subst m
  exact exists_neighborly_cube_data hd hdn

end Grunbaum2003


-- Local ingredient: CoordinateSplit

set_option autoImplicit false

namespace Grunbaum2003

noncomputable section

                                                                           
def retainedCoordinateProjection (m d : ℕ) :
    (Fin (m + d) → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Fin.natAdd m i))

@[simp] theorem retainedCoordinateProjection_apply (m d : ℕ)
    (x : Fin (m + d) → ℝ) (i : Fin d) :
    retainedCoordinateProjection m d x i = x (Fin.natAdd m i) := rfl

                                                                          
                                                                       
def discardedCoordinateEmbed (m d : ℕ) :
    (Fin m → ℝ) →L[ℝ] (Fin (m + d) → ℝ) where
  toLinearMap :=
    { toFun z := Fin.append z (0 : Fin d → ℝ)
      map_add' z w := by
        ext i
        cases i using Fin.addCases <;> simp
      map_smul' c z := by
        ext i
        cases i using Fin.addCases <;> simp }
  cont := by
    apply continuous_pi
    intro i
    change Continuous (fun z : Fin m → ℝ => Fin.append z (0 : Fin d → ℝ) i)
    cases i using Fin.addCases
    · rename_i j
      simpa only [Fin.append_left] using
        (continuous_apply j : Continuous (fun z : Fin m → ℝ => z j))
    · simpa only [Fin.append_right, Pi.zero_apply] using
        (continuous_const : Continuous (fun _ : Fin m → ℝ => (0 : ℝ)))

@[simp] theorem discardedCoordinateEmbed_apply_left (m d : ℕ)
    (z : Fin m → ℝ) (i : Fin m) :
    discardedCoordinateEmbed m d z (Fin.castAdd d i) = z i :=
  Fin.append_left _ _ _

@[simp] theorem discardedCoordinateEmbed_apply_right (m d : ℕ)
    (z : Fin m → ℝ) (i : Fin d) :
    discardedCoordinateEmbed m d z (Fin.natAdd m i) = 0 :=
  Fin.append_right _ _ _

                                                                         
                                                                       
theorem coordinate_split_identity (m d : ℕ) (x : Fin (m + d) → ℝ) :
    Fin.append (fun i : Fin m => x (Fin.castAdd d i))
      (retainedCoordinateProjection m d x) = x :=
  Fin.append_castAdd_natAdd

theorem discardedCoordinateEmbed_injective (m d : ℕ) :
    Function.Injective (discardedCoordinateEmbed m d) := by
  intro z w h
  funext i
  simpa only [discardedCoordinateEmbed_apply_left] using
    congrFun h (Fin.castAdd d i)

                                                                        
                                             
theorem retainedCoordinateProjection_eq_zero_iff (m d : ℕ)
    (x : Fin (m + d) → ℝ) :
    retainedCoordinateProjection m d x = 0 ↔
      ∃ z : Fin m → ℝ, discardedCoordinateEmbed m d z = x := by
  constructor
  · intro h
    let z : Fin m → ℝ := fun i => x (Fin.castAdd d i)
    refine ⟨z, ?_⟩
    ext i
    cases i using Fin.addCases
    · simp only [discardedCoordinateEmbed_apply_left, z]
    · rename_i j
      rw [discardedCoordinateEmbed_apply_right]
      exact (congrFun h j).symm
  · rintro ⟨z, rfl⟩
    ext i
    exact discardedCoordinateEmbed_apply_right m d z i

theorem retainedCoordinateProjection_surjective (m d : ℕ) :
    Function.Surjective (retainedCoordinateProjection m d) := by
  intro y
  refine ⟨Fin.append (0 : Fin m → ℝ) y, ?_⟩
  ext i
  exact Fin.append_right _ _ _

theorem ker_retainedCoordinateProjection_eq_range_discardedCoordinateEmbed (m d : ℕ) :
    LinearMap.ker (retainedCoordinateProjection m d).toLinearMap =
      LinearMap.range (discardedCoordinateEmbed m d).toLinearMap := by
  ext x
  exact retainedCoordinateProjection_eq_zero_iff m d x

end
end Grunbaum2003


-- Local ingredient: NormalMatching

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

                                                                   
                                                              
theorem full_triangular_dot_eq_source_normal {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) (σ : Fin n → Bool)
    (i : Fin n) (x : Fin n → ℝ) :
    (∑ j : Fin n,
      (if j.val < i.val then C i j else if j.val = i.val then
        (if σ i then δ else -δ) else 0) * x j) =
      (∑ j : Fin n, if j < i then C i j * x j else 0) +
        (if σ i then δ else -δ) * x i := by
  classical
  have hTerm (j : Fin n) :
      (if j.val < i.val then C i j else if j.val = i.val then
        (if σ i then δ else -δ) else 0) * x j =
      (if j.val < i.val then C i j * x j else 0) +
        (if j.val = i.val then (if σ i then δ else -δ) * x j else 0) := by
    by_cases hlt : j.val < i.val
    · simp [hlt, ne_of_lt hlt]
    · simp [hlt, ite_mul]
  simp_rw [hTerm]
  rw [Finset.sum_add_distrib]
  simp only [← Fin.ext_iff]
  simp

private theorem full_triangular_dot_embed_eq_prefix {m d : ℕ}
    (C : Matrix (Fin (m + d)) (Fin (m + d)) ℝ)
    (δ : ℝ) (σ : Fin (m + d) → Bool) (i : Fin (m + d)) (z : Fin m → ℝ) :
    (∑ j : Fin (m + d),
      (if j.val < i.val then C i j else if j.val = i.val then
        (if σ i then δ else -δ) else 0) * discardedCoordinateEmbed m d z j) =
      ∑ j : Fin m,
        (if j.val < i.val then C i (Fin.castAdd d j) else if j.val = i.val then
          (if σ i then δ else -δ) else 0) * z j := by
  rw [Fin.sum_univ_add]
  simp only [discardedCoordinateEmbed_apply_left, discardedCoordinateEmbed_apply_right,
    Fin.val_castAdd, mul_zero, Finset.sum_const_zero, add_zero]

                                                                             
                                                                         
                                                                     
theorem actual_signed_normal_on_discarded_embed {m d : ℕ}
    (B : Matrix (Fin (m + d)) (Fin m) ℝ) (δ : ℝ)
    (σ : Fin (m + d) → Bool) (i : Fin (m + d)) (z : Fin m → ℝ) :
    let fullB : Matrix (Fin (m + d)) (Fin (m + d)) ℝ :=
      fun r j => if h : j.val < m then B r ⟨j.val, h⟩ else 0
    (∑ j : Fin (m + d), if j < i then
      fullB i j * discardedCoordinateEmbed m d z j else 0) +
        (if σ i then δ else -δ) * discardedCoordinateEmbed m d z i =
      ∑ j : Fin m,
        (if j.val < i.val then B i j else if j.val = i.val then
          (if σ i then δ else -δ) else 0) * z j := by
  classical
  let C : Matrix (Fin (m + d)) (Fin (m + d)) ℝ :=
    fun r j => if h : j.val < m then B r ⟨j.val, h⟩ else 0
  change (∑ j : Fin (m + d), if j < i then
    C i j * discardedCoordinateEmbed m d z j else 0) +
      (if σ i then δ else -δ) * discardedCoordinateEmbed m d z i = _
  rw [← full_triangular_dot_eq_source_normal C δ σ i (discardedCoordinateEmbed m d z),
    full_triangular_dot_embed_eq_prefix C δ σ i z]
  apply Finset.sum_congr rfl
  intro j _
  have hC : C i (Fin.castAdd d j) = B i j := by
    simp only [C, Fin.val_castAdd, j.isLt, dite_true]
  rw [hC]

end Grunbaum2003


-- Local ingredient: DiscardedRows

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

                                                                         
                                                                      
theorem discarded_rows_common_kernel_eq_zero {n m : ℕ}
    (R : Matrix (Fin n) (Fin m) ℝ)
    (hGeneric : ∀ u : Fin m → Fin n, StrictMono u →
      Matrix.det (fun i j : Fin m => R (u i) j) ≠ 0)
    (I : Finset (Fin n)) (hI : m ≤ I.card)
    (z : Fin m → ℝ) (hZero : ∀ i ∈ I, ∑ j : Fin m, R i j * z j = 0) :
    z = 0 := by
  classical
  obtain ⟨S, hSI, hSm⟩ := Finset.exists_subset_card_eq hI
  let u : Fin m ↪o Fin n := S.orderEmbOfFin hSm
  let M : Matrix (Fin m) (Fin m) ℝ := fun i j => R (u i) j
  have hDet : M.det ≠ 0 := hGeneric u u.strictMono
  have hUnit : IsUnit M :=
    (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hDet)
  have hMz : M.mulVec z = 0 := by
    ext i
    change (∑ j : Fin m, R (u i) j * z j) = 0
    exact hZero (u i) (hSI (S.orderEmbOfFin_mem hSm i))
  apply (Matrix.mulVec_injective_iff_isUnit.mpr hUnit)
  simpa only [Matrix.mulVec_zero] using hMz

                                                                          
                                                                          
                                                                
theorem exists_discarded_vector_releasing_rows {n m : ℕ} (hm : m ≤ n)
    (R : Matrix (Fin n) (Fin m) ℝ)
    (hGeneric : ∀ u : Fin m → Fin n, StrictMono u →
      Matrix.det (fun i j : Fin m => R (u i) j) ≠ 0)
    (I : Finset (Fin n)) (hI : I.card ≤ m) :
    ∃ z : Fin m → ℝ, ∀ i ∈ I, ∑ j : Fin m, R i j * z j = -1 := by
  classical
  have hCard : m ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hm
  obtain ⟨S, hIS, _, hSm⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ I) hI hCard
  let u : Fin m ↪o Fin n := S.orderEmbOfFin hSm
  let M : Matrix (Fin m) (Fin m) ℝ := fun i j => R (u i) j
  have hDet : M.det ≠ 0 := hGeneric u u.strictMono
  have hUnit : IsUnit M :=
    (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hDet)
  obtain ⟨z, hz⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hUnit)
    (fun _ : Fin m => (-1 : ℝ))
  refine ⟨z, ?_⟩
  intro i hi
  obtain ⟨j, hji⟩ : ∃ j : Fin m, u j = i := by
    change i ∈ Set.range (S.orderEmbOfFin hSm)
    rw [Finset.range_orderEmbOfFin]
    exact hIS hi
  rw [← hji]
  exact congrFun hz j

end Grunbaum2003


-- Local ingredient: ActualProjectionKernel

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

private def sourceNormalLinearMap {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) (σ : Fin n → Bool) (i : Fin n) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  ∑ j : Fin n,
    (if j.val < i.val then C i j else if j.val = i.val then
      (if σ i then δ else -δ) else 0) • LinearMap.proj j

private theorem sourceNormalLinearMap_apply {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) (σ : Fin n → Bool)
    (i : Fin n) (x : Fin n → ℝ) :
    sourceNormalLinearMap C δ σ i x =
      (∑ j : Fin n, if j < i then C i j * x j else 0) +
        (if σ i then δ else -δ) * x i := by
  rw [← full_triangular_dot_eq_source_normal C δ σ i x]
  simp only [sourceNormalLinearMap, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]

                                                                       
                                                                          
                                                                         
theorem actual_projection_active_kernel_eq_zero {m d : ℕ}
    (B : Matrix (Fin (m + d)) (Fin m) ℝ) (δ : ℝ)
    (hGeneric : ∀ u : Fin m → Fin (m + d), StrictMono u →
      ∀ τ : Fin (m + d) → Bool,
        Matrix.det (fun i j : Fin m =>
          if j.val < (u i).val then B (u i) j else if j.val = (u i).val then
            (if τ (u i) then δ else -δ) else 0) ≠ 0)
    (I : Finset (Fin (m + d))) (hI : m ≤ I.card) (σ : Fin (m + d) → Bool)
    (v : Fin (m + d) → ℝ) (hProj : retainedCoordinateProjection m d v = 0)
    (hNormal :
      let fullB : Matrix (Fin (m + d)) (Fin (m + d)) ℝ :=
        fun r j => if h : j.val < m then B r ⟨j.val, h⟩ else 0
      ∀ i ∈ I, (∑ j : Fin (m + d), if j < i then fullB i j * v j else 0) +
        (if σ i then δ else -δ) * v i = 0) :
    v = 0 := by
  classical
  let C : Matrix (Fin (m + d)) (Fin (m + d)) ℝ :=
    fun r j => if h : j.val < m then B r ⟨j.val, h⟩ else 0
  change ∀ i ∈ I, (∑ j : Fin (m + d), if j < i then C i j * v j else 0) +
    (if σ i then δ else -δ) * v i = 0 at hNormal
  obtain ⟨z, hz⟩ := (retainedCoordinateProjection_eq_zero_iff m d v).mp hProj
  let R : Matrix (Fin (m + d)) (Fin m) ℝ := fun i j =>
    if j.val < i.val then B i j else if j.val = i.val then
      (if σ i then δ else -δ) else 0
  have hGenericR : ∀ u : Fin m → Fin (m + d), StrictMono u →
      Matrix.det (fun i j : Fin m => R (u i) j) ≠ 0 :=
    fun u hu => hGeneric u hu σ
  have hRows : ∀ i ∈ I, ∑ j : Fin m, R i j * z j = 0 := by
    intro i hi
    have hN := hNormal i hi
    rw [← hz] at hN
    exact (actual_signed_normal_on_discarded_embed B δ σ i z).symm.trans hN
  have hz₀ := discarded_rows_common_kernel_eq_zero R hGenericR I hI z hRows
  calc
    v = discardedCoordinateEmbed m d z := hz.symm
    _ = 0 := by rw [hz₀, map_zero]

                                                                            
                                                                      
theorem actual_projection_injective_on_active_equalities {m d : ℕ}
    (B : Matrix (Fin (m + d)) (Fin m) ℝ) (δ : ℝ)
    (hGeneric : ∀ u : Fin m → Fin (m + d), StrictMono u →
      ∀ τ : Fin (m + d) → Bool,
        Matrix.det (fun i j : Fin m =>
          if j.val < (u i).val then B (u i) j else if j.val = (u i).val then
            (if τ (u i) then δ else -δ) else 0) ≠ 0)
    (I : Finset (Fin (m + d))) (hI : m ≤ I.card) (σ : Fin (m + d) → Bool)
    (b : Fin (m + d) → ℝ) :
    let fullB : Matrix (Fin (m + d)) (Fin (m + d)) ℝ :=
      fun r j => if h : j.val < m then B r ⟨j.val, h⟩ else 0
    Set.InjOn (retainedCoordinateProjection m d)
      {x | ∀ i ∈ I, (∑ j : Fin (m + d), if j < i then fullB i j * x j else 0) +
        (if σ i then δ else -δ) * x i = b i} := by
  classical
  let C : Matrix (Fin (m + d)) (Fin (m + d)) ℝ :=
    fun r j => if h : j.val < m then B r ⟨j.val, h⟩ else 0
  change Set.InjOn (retainedCoordinateProjection m d)
    {x | ∀ i ∈ I, (∑ j : Fin (m + d), if j < i then C i j * x j else 0) +
      (if σ i then δ else -δ) * x i = b i}
  intro x hx y hy hxy
  have hProj : retainedCoordinateProjection m d (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hNormal : ∀ i ∈ I,
      (∑ j : Fin (m + d), if j < i then C i j * (x - y) j else 0) +
        (if σ i then δ else -δ) * (x - y) i = 0 := by
    intro i hi
    have h := (sourceNormalLinearMap C δ σ i).map_sub x y
    simpa only [sourceNormalLinearMap_apply, hx i hi, hy i hi, sub_self] using h
  exact sub_eq_zero.mp
    (actual_projection_active_kernel_eq_zero B δ hGeneric I hI σ (x - y) hProj hNormal)

                                                                         
                                                                     
theorem actual_projection_injective_on_common_active_kernel {m d : ℕ}
    (B : Matrix (Fin (m + d)) (Fin m) ℝ) (δ : ℝ)
    (hGeneric : ∀ u : Fin m → Fin (m + d), StrictMono u →
      ∀ τ : Fin (m + d) → Bool,
        Matrix.det (fun i j : Fin m =>
          if j.val < (u i).val then B (u i) j else if j.val = (u i).val then
            (if τ (u i) then δ else -δ) else 0) ≠ 0)
    (I : Finset (Fin (m + d))) (hI : m ≤ I.card) (σ : Fin (m + d) → Bool) :
    let fullB : Matrix (Fin (m + d)) (Fin (m + d)) ℝ :=
      fun r j => if h : j.val < m then B r ⟨j.val, h⟩ else 0
    Set.InjOn (retainedCoordinateProjection m d)
      {v | ∀ i ∈ I, (∑ j : Fin (m + d), if j < i then fullB i j * v j else 0) +
        (if σ i then δ else -δ) * v i = 0} :=
  actual_projection_injective_on_active_equalities B δ hGeneric I hI σ (fun _ => 0)

                                                                           
                                                                             
                             
theorem exists_actual_discarded_release_direction {m d : ℕ}
    (B : Matrix (Fin (m + d)) (Fin m) ℝ) (δ : ℝ)
    (hGeneric : ∀ u : Fin m → Fin (m + d), StrictMono u →
      ∀ τ : Fin (m + d) → Bool,
        Matrix.det (fun i j : Fin m =>
          if j.val < (u i).val then B (u i) j else if j.val = (u i).val then
            (if τ (u i) then δ else -δ) else 0) ≠ 0)
    (I : Finset (Fin (m + d))) (hI : I.card ≤ m) (σ : Fin (m + d) → Bool) :
    let fullB : Matrix (Fin (m + d)) (Fin (m + d)) ℝ :=
      fun r j => if h : j.val < m then B r ⟨j.val, h⟩ else 0
    ∃ v : Fin (m + d) → ℝ, retainedCoordinateProjection m d v = 0 ∧
      ∀ i ∈ I, (∑ j : Fin (m + d), if j < i then fullB i j * v j else 0) +
        (if σ i then δ else -δ) * v i = -1 := by
  classical
  let R : Matrix (Fin (m + d)) (Fin m) ℝ := fun i j =>
    if j.val < i.val then B i j else if j.val = i.val then
      (if σ i then δ else -δ) else 0
  have hGenericR : ∀ u : Fin m → Fin (m + d), StrictMono u →
      Matrix.det (fun i j : Fin m => R (u i) j) ≠ 0 :=
    fun u hu => hGeneric u hu σ
  obtain ⟨z, hz⟩ := exists_discarded_vector_releasing_rows (Nat.le_add_right m d)
    R hGenericR I hI
  refine ⟨discardedCoordinateEmbed m d z, ?_, ?_⟩
  · exact (retainedCoordinateProjection_eq_zero_iff m d _).mpr ⟨z, rfl⟩
  · intro i hi
    exact (actual_signed_normal_on_discarded_embed B δ σ i z).trans (hz i hi)

end Grunbaum2003


-- Local ingredient: CubeWeightedMax

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

                                                                        
                                                                          
                                                                         
theorem centered_cube_weighted_maximizers {n : ℕ} (c : Fin n → ℝ) :
    {x : Fin n → ℝ | (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧
      ∀ y : Fin n → ℝ, (∀ i, -1 ≤ y i ∧ y i ≤ 1) →
        (∑ i, c i * y i) ≤ ∑ i, c i * x i} =
    {x : Fin n → ℝ | (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧
      ∀ i, c i ≠ 0 → x i = if 0 < c i then 1 else -1} := by
  classical
  let M : ℝ := ∑ i, |c i|
  let v : Fin n → ℝ := fun i => if 0 ≤ c i then 1 else -1
  have hv : ∀ i, -1 ≤ v i ∧ v i ≤ 1 := by
    intro i
    dsimp only [v]
    split_ifs <;> constructor <;> norm_num
  have hAtMax : (∑ i, c i * v i) = M := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ c i
    · simp only [v, if_pos hi, mul_one, abs_of_nonneg hi]
    · have hneg : c i < 0 := lt_of_not_ge hi
      simp only [v, if_neg hi, mul_neg, mul_one, abs_of_neg hneg]
  have hTerm (x : Fin n → ℝ) (hx : ∀ i, -1 ≤ x i ∧ x i ≤ 1) (i : Fin n) :
      c i * x i ≤ |c i| := by
    calc
      c i * x i ≤ |c i * x i| := le_abs_self _
      _ = |c i| * |x i| := abs_mul _ _
      _ ≤ |c i| * 1 := mul_le_mul_of_nonneg_left (abs_le.mpr (hx i)) (abs_nonneg _)
      _ = |c i| := mul_one _
  have hBound (x : Fin n → ℝ) (hx : ∀ i, -1 ≤ x i ∧ x i ≤ 1) :
      (∑ i, c i * x i) ≤ M := Finset.sum_le_sum (fun i _ => hTerm x hx i)
  ext x
  constructor
  · rintro ⟨hx, hMax⟩
    have hEq : (∑ i, c i * x i) = M :=
      le_antisymm (hBound x hx) (hAtMax ▸ hMax v hv)
    have hGap : (∑ i, (|c i| - c i * x i)) = 0 := by
      rw [Finset.sum_sub_distrib, hEq]
      exact sub_self M
    have hEach := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => sub_nonneg.mpr (hTerm x hx i))).mp hGap
    refine ⟨hx, fun i hci => ?_⟩
    have hProduct : c i * x i = |c i| := (sub_eq_zero.mp (hEach i (Finset.mem_univ i))).symm
    by_cases hi : 0 < c i
    · rw [if_pos hi]
      apply mul_left_cancel₀ hci
      simpa only [abs_of_pos hi, mul_one] using hProduct
    · have hneg : c i < 0 := lt_of_le_of_ne (le_of_not_gt hi) hci
      rw [if_neg hi]
      apply mul_left_cancel₀ hci
      simpa only [abs_of_neg hneg, mul_neg, mul_one] using hProduct
  · rintro ⟨hx, hFixed⟩
    have hEq : (∑ i, c i * x i) = M := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hci : c i = 0
      · simp only [hci, zero_mul, abs_zero]
      · rw [hFixed i hci]
        by_cases hi : 0 < c i
        · simp only [if_pos hi, mul_one, abs_of_pos hi]
        · have hneg : c i < 0 := lt_of_le_of_ne (le_of_not_gt hi) hci
          simp only [if_neg hi, mul_neg, mul_one, abs_of_neg hneg]
    refine ⟨hx, fun y hy => ?_⟩
    rw [hEq]
    exact hBound y hy

end Grunbaum2003


-- Local ingredient: CenteredCubeFaces

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem coordinate_functional_eq_sum {n : ℕ}
    (L : StrongDual ℝ (Fin n → ℝ)) (x : Fin n → ℝ) :
    L x = ∑ i : Fin n, L (Pi.single i 1) * x i := by
  classical
  have hExpansion : (∑ i : Fin n, x i • Pi.single i (1 : ℝ)) = x := by
    ext j
    simp [Pi.single_apply]
  calc
    L x = L (∑ i : Fin n, x i • Pi.single i (1 : ℝ)) := congrArg L hExpansion.symm
    _ = ∑ i : Fin n, x i * L (Pi.single i 1) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = ∑ i : Fin n, L (Pi.single i 1) * x i :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

                                                                               
theorem centered_cube_face_classification {n : ℕ} (S : Set (Fin n → ℝ))
    (hS : IsExposed ℝ {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1} S)
    (hNonempty : S.Nonempty) :
    ∃ I : Finset (Fin n), ∃ σ : Fin n → Bool,
      S = {x : Fin n → ℝ | (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧
        ∀ i ∈ I, x i = if σ i then 1 else -1} := by
  classical
  obtain ⟨L, hL⟩ := hS hNonempty
  let c : Fin n → ℝ := fun i => L (Pi.single i 1)
  let I : Finset (Fin n) := Finset.univ.filter (fun i => c i ≠ 0)
  let σ : Fin n → Bool := fun i => decide (0 < c i)
  refine ⟨I, σ, ?_⟩
  have hEq : S = {x : Fin n → ℝ | (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧
      ∀ i, c i ≠ 0 → x i = if 0 < c i then 1 else -1} := by
    rw [hL]
    trans {x : Fin n → ℝ | (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧
      ∀ y : Fin n → ℝ, (∀ i, -1 ≤ y i ∧ y i ≤ 1) →
        (∑ i, c i * y i) ≤ ∑ i, c i * x i}
    · ext x
      apply and_congr_right
      intro _
      apply forall_congr'
      intro y
      apply imp_congr_right
      intro _
      rw [coordinate_functional_eq_sum L y, coordinate_functional_eq_sum L x]
    · exact centered_cube_weighted_maximizers c
  rw [hEq]
  ext x
  simp only [I, σ, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ,
    true_and, decide_eq_true_eq]

                                                                              
theorem isExposed_centered_cube_coordinate_face {n : ℕ}
    (I : Finset (Fin n)) (σ : Fin n → Bool) :
    IsExposed ℝ {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1}
      {x : Fin n → ℝ | (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧
        ∀ i ∈ I, x i = if σ i then 1 else -1} := by
  classical
  let c : Fin n → ℝ := fun i => if i ∈ I then (if σ i then 1 else -1) else 0
  let L : StrongDual ℝ (Fin n → ℝ) :=
    ∑ i : Fin n, c i • (ContinuousLinearMap.proj i)
  have hApply (x : Fin n → ℝ) : L x = ∑ i, c i * x i := by
    simp only [L, sum_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hActive (i : Fin n) : c i ≠ 0 ↔ i ∈ I := by
    by_cases hi : i ∈ I <;> cases hσ : σ i <;> simp [c, hi, hσ]
  have hSign (i : Fin n) (hi : i ∈ I) :
      (if 0 < c i then (1 : ℝ) else -1) = if σ i then 1 else -1 := by
    cases hσ : σ i <;> simp [c, hi, hσ]
  intro _
  refine ⟨L, ?_⟩
  have hMax := centered_cube_weighted_maximizers c
  have hPattern :
      {x : Fin n → ℝ | (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧
        ∀ i, c i ≠ 0 → x i = if 0 < c i then 1 else -1} =
      {x : Fin n → ℝ | (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧
        ∀ i ∈ I, x i = if σ i then 1 else -1} := by
    ext x
    constructor
    · rintro ⟨hx, hFix⟩
      refine ⟨hx, fun i hi => ?_⟩
      rw [← hSign i hi]
      exact hFix i ((hActive i).mpr hi)
    · rintro ⟨hx, hFix⟩
      refine ⟨hx, fun i hi => ?_⟩
      have hiI := (hActive i).mp hi
      rw [hSign i hiI]
      exact hFix i hiI
  apply Eq.symm
  simp_rw [hApply]
  exact hMax.trans hPattern

                                                                        
                                                                            
theorem centered_cube_coordinate_face_anchor {n : ℕ}
    (I : Finset (Fin n)) (σ : Fin n → Bool) :
    let x₀ : Fin n → ℝ := fun i => if i ∈ I then (if σ i then 1 else -1) else 0
    (∀ i, -1 ≤ x₀ i ∧ x₀ i ≤ 1) ∧
      (∀ i ∈ I, x₀ i = if σ i then 1 else -1) ∧
      ∀ i ∉ I, x₀ i = 0 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ I <;> cases hσ : σ i <;> simp [hi, hσ]
  · intro i hi
    simp only [if_pos hi]
  · intro i hi
    simp only [if_neg hi]

end Grunbaum2003


-- Local ingredient: TriangularCubeFaces

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem normalized_coordinate_eq_endpoint_iff (l b δ t : ℝ) (σ : Bool)
    (hWidth : 0 < b - l) :
    δ * t / (b - l) = (if σ then 1 else -1) ↔
      l + (if σ then δ else -δ) * t = b := by
  cases σ with
  | false =>
    change δ * t / (b - l) = -1 ↔ l + (-δ) * t = b
    rw [div_eq_iff hWidth.ne']
    simp only [neg_one_mul, neg_mul]
    constructor <;> intro h <;> linarith
  | true =>
    change δ * t / (b - l) = 1 ↔ l + δ * t = b
    rw [div_eq_iff hWidth.ne', one_mul]
    constructor <;> intro h <;> linarith

                                                                        
                                                                              
theorem triangular_cube_face_classification {n : ℕ}
    (B : Fin n → Fin n → ℝ) (δ : ℝ) (b : Fin n → ℝ) (P : Set (Fin n → ℝ))
    (e : ExposedFaceBijection P {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1})
    (hCoordinates : ∀ x ∈ P, ∀ i,
      0 < b i - (∑ j : Fin n, if j < i then B i j * x j else 0) ∧
      e.toFun x i = δ * x i / (b i - ∑ j : Fin n, if j < i then B i j * x j else 0))
    (S : Set (Fin n → ℝ)) (hS : IsExposed ℝ P S) (hSne : S.Nonempty) :
    ∃ I : Finset (Fin n), ∃ σ : Fin n → Bool,
      S = {x | x ∈ P ∧ ∀ i ∈ I,
        (∑ j : Fin n, if j < i then B i j * x j else 0) +
          (if σ i then δ else -δ) * x i = b i} := by
  classical
  obtain ⟨I, σ, hImage⟩ := centered_cube_face_classification (e.toFun '' S)
    (e.map_face S hS) (hSne.image e.toFun)
  refine ⟨I, σ, ?_⟩
  ext x
  constructor
  · intro hx
    have hxP := hS.subset hx
    have hxImage : e.toFun x ∈ e.toFun '' S := ⟨x, hx, rfl⟩
    rw [hImage] at hxImage
    refine ⟨hxP, fun i hi => ?_⟩
    have hEnd := hxImage.2 i hi
    rw [(hCoordinates x hxP i).2] at hEnd
    exact (normalized_coordinate_eq_endpoint_iff _ _ δ (x i) (σ i)
      (hCoordinates x hxP i).1).mp hEnd
  · rintro ⟨hxP, hActive⟩
    have hxImage : e.toFun x ∈ e.toFun '' S := by
      rw [hImage]
      refine ⟨e.map_mem x hxP, fun i hi => ?_⟩
      rw [(hCoordinates x hxP i).2]
      exact (normalized_coordinate_eq_endpoint_iff _ _ δ (x i) (σ i)
        (hCoordinates x hxP i).1).mpr (hActive i hi)
    obtain ⟨y, hy, hyx⟩ := hxImage
    have hyP := hS.subset hy
    have hyx' : y = x := by
      calc
        y = e.invFun (e.toFun y) := (e.left_inv y hyP).symm
        _ = e.invFun (e.toFun x) := congrArg e.invFun hyx
        _ = x := e.left_inv x hxP
    exact hyx' ▸ hy

                                                                          
                                                                            
                                                                               
theorem triangular_cube_face_strict_anchor {n : ℕ}
    (B : Fin n → Fin n → ℝ) (δ : ℝ) (b : Fin n → ℝ) (P : Set (Fin n → ℝ))
    (e : ExposedFaceBijection P {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1})
    (hCoordinates : ∀ x ∈ P, ∀ i,
      0 < b i - (∑ j : Fin n, if j < i then B i j * x j else 0) ∧
      e.toFun x i = δ * x i / (b i - ∑ j : Fin n, if j < i then B i j * x j else 0))
    (I : Finset (Fin n)) (σ : Fin n → Bool) :
    ∃ x₀ ∈ P,
      (∀ i ∈ I, (∑ j : Fin n, if j < i then B i j * x₀ j else 0) +
        (if σ i then δ else -δ) * x₀ i = b i) ∧
      (∀ i ∉ I,
        (∑ j : Fin n, if j < i then B i j * x₀ j else 0) + δ * x₀ i < b i ∧
        (∑ j : Fin n, if j < i then B i j * x₀ j else 0) - δ * x₀ i < b i) ∧
      ∀ i ∈ I, (∑ j : Fin n, if j < i then B i j * x₀ j else 0) -
        (if σ i then δ else -δ) * x₀ i < b i := by
  classical
  let v : Fin n → ℝ := fun i => if i ∈ I then (if σ i then 1 else -1) else 0
  obtain ⟨hBox, hFixed, hFree⟩ := centered_cube_coordinate_face_anchor I σ
  let x₀ := e.invFun v
  have hxP : x₀ ∈ P := e.inv_mem v hBox
  have hxMap : e.toFun x₀ = v := e.right_inv v hBox
  have hActive : ∀ i ∈ I,
      (∑ j : Fin n, if j < i then B i j * x₀ j else 0) +
        (if σ i then δ else -δ) * x₀ i = b i := by
    intro i hi
    apply (normalized_coordinate_eq_endpoint_iff _ _ δ (x₀ i) (σ i)
      (hCoordinates x₀ hxP i).1).mp
    rw [← (hCoordinates x₀ hxP i).2, hxMap]
    exact hFixed i hi
  refine ⟨x₀, hxP, hActive, ?_, ?_⟩
  · intro i hi
    have hZero : δ * x₀ i / (b i - ∑ j : Fin n, if j < i then B i j * x₀ j else 0) = 0 := by
      rw [← (hCoordinates x₀ hxP i).2, hxMap]
      exact hFree i hi
    have hMul : δ * x₀ i = 0 := by
      simpa only [zero_mul] using
        (div_eq_iff (hCoordinates x₀ hxP i).1.ne').mp hZero
    have hWidth := (hCoordinates x₀ hxP i).1
    constructor <;> rw [hMul] <;> linarith
  · intro i hi
    have hA := hActive i hi
    have hWidth := (hCoordinates x₀ hxP i).1
    linarith

end Grunbaum2003


-- Local ingredient: TriangularHalfspaces

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

noncomputable def triangularSignedNormal {n : ℕ}
    (B : Fin n → Fin n → ℝ) (δ : ℝ) (i : Fin n) (s : Bool) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ j : Fin n,
    (if j < i then B i j else if j = i then (if s then δ else -δ) else 0) * x j
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => mul_left_comm _ c (x j))

theorem triangularSignedNormal_apply {n : ℕ} (B : Fin n → Fin n → ℝ)
    (δ : ℝ) (i : Fin n) (s : Bool) (x : Fin n → ℝ) :
    triangularSignedNormal B δ i s x =
      (∑ j : Fin n, if j < i then B i j * x j else 0) +
        (if s then δ else -δ) * x i := by
  classical
  have hsplit (j : Fin n) :
      (if j < i then B i j else if j = i then (if s then δ else -δ) else 0) * x j =
      (if j < i then B i j * x j else 0) +
        (if j = i then (if s then δ else -δ) * x j else 0) := by
    by_cases hlt : j < i
    · simp only [if_pos hlt, if_neg (ne_of_lt hlt), add_zero]
    · by_cases heq : j = i
      · subst j
        simp only [lt_irrefl, ↓reduceIte, zero_add]
      · simp only [if_neg hlt, if_neg heq, zero_mul, add_zero]
  change (∑ j : Fin n, _) = _
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib]
  simp

theorem triangular_absolute_constraints_eq_halfspaces {n : ℕ}
    (B : Fin n → Fin n → ℝ) (δ : ℝ) (b : Fin n → ℝ) :
    {x : Fin n → ℝ | ∀ i, |δ * x i| ≤ b i -
      ∑ j : Fin n, if j < i then B i j * x j else 0} =
    {x : Fin n → ℝ | ∀ p : Fin n × Bool,
      triangularSignedNormal B δ p.1 p.2 x ≤ b p.1} := by
  ext x
  constructor
  · intro hx p
    have h := abs_le.mp (hx p.1)
    rw [triangularSignedNormal_apply]
    cases p.2 <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_mul] <;> linarith
  · intro hx i
    have hp := hx (i, true)
    have hm := hx (i, false)
    simp only [triangularSignedNormal_apply, Bool.false_eq_true, ↓reduceIte,
      neg_mul] at hp hm
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem triangularSignedNormal_direction_zero {n : ℕ}
    (B : Fin n → Fin n → ℝ) (δ : ℝ) (b : Fin n → ℝ)
    (P : Set (Fin n → ℝ)) (I : Finset (Fin n)) (σ : Fin n → Bool)
    (z : Fin n → ℝ)
    (hz : z ∈ (affineSpan ℝ {x | x ∈ P ∧ ∀ i ∈ I,
      (∑ j : Fin n, if j < i then B i j * x j else 0) +
        (if σ i then δ else -δ) * x i = b i}).direction) :
    ∀ i ∈ I, triangularSignedNormal B δ i (σ i) z = 0 := by
  intro i hi
  let a := triangularSignedNormal B δ i (σ i)
  have hCarrier : {x | x ∈ P ∧ ∀ j ∈ I,
      (∑ k : Fin n, if k < j then B j k * x k else 0) +
        (if σ j then δ else -δ) * x j = b j} ⊆
      {x | a x = b i} := by
    intro x hx
    change triangularSignedNormal B δ i (σ i) x = b i
    rw [triangularSignedNormal_apply]
    exact hx.2 i hi
  have hSpan : (affineSpan ℝ {x | x ∈ P ∧ ∀ j ∈ I,
      (∑ k : Fin n, if k < j then B j k * x k else 0) +
        (if σ j then δ else -δ) * x j = b j}).direction ≤ a.ker := by
    rw [direction_affineSpan, vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, y, hy, rfl⟩
    change a (x - y) = 0
    rw [map_sub, hCarrier hx, hCarrier hy, sub_self]
  exact hSpan hz

end Grunbaum2003


-- Local ingredient: TriangularFaceAnchor

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem mem_triangular_active_pairs {n : ℕ} (I : Finset (Fin n)) (σ : Fin n → Bool)
    (i : Fin n) (s : Bool) :
    (i, s) ∈ I.image (fun j => (j, σ j)) ↔ i ∈ I ∧ s = σ i := by
  classical
  constructor
  · intro h
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
    have hji : j = i := congrArg Prod.fst heq
    have hjs : σ j = s := congrArg Prod.snd heq
    subst j
    exact ⟨hj, hjs.symm⟩
  · rintro ⟨hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

                                                                      
                                                
theorem triangular_cube_halfspace_strict_anchor {n : ℕ}
    (B : Fin n → Fin n → ℝ) (δ : ℝ) (b : Fin n → ℝ) (P : Set (Fin n → ℝ))
    (e : ExposedFaceBijection P {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1})
    (hCoordinates : ∀ x ∈ P, ∀ i,
      0 < b i - (∑ j : Fin n, if j < i then B i j * x j else 0) ∧
      e.toFun x i = δ * x i / (b i - ∑ j : Fin n, if j < i then B i j * x j else 0))
    (I : Finset (Fin n)) (σ : Fin n → Bool) :
    ∃ x₀ ∈ P,
      (∀ i ∈ I, triangularSignedNormal B δ i (σ i) x₀ = b i) ∧
      ∀ p : Fin n × Bool, p ∉ I.image (fun j => (j, σ j)) →
        triangularSignedNormal B δ p.1 p.2 x₀ < b p.1 := by
  classical
  obtain ⟨x₀, hxP, hActive, hFree, hOpposite⟩ :=
    triangular_cube_face_strict_anchor B δ b P e hCoordinates I σ
  refine ⟨x₀, hxP, ?_, ?_⟩
  · intro i hi
    rw [triangularSignedNormal_apply]
    exact hActive i hi
  · rintro ⟨i, s⟩ hp
    rw [triangularSignedNormal_apply]
    by_cases hi : i ∈ I
    · have hs : s ≠ σ i := by
        intro hs
        exact hp ((mem_triangular_active_pairs I σ i s).mpr ⟨hi, hs⟩)
      have hCoeff : (if s then δ else -δ) = -(if σ i then δ else -δ) := by
        cases s <;> cases hσ : σ i
        · exact False.elim (hs hσ.symm)
        · rfl
        · exact (neg_neg δ).symm
        · exact False.elim (hs hσ.symm)
      rw [hCoeff, neg_mul, ← sub_eq_add_neg]
      exact hOpposite i hi
    · cases s with
      | false =>
          simpa only [Bool.false_eq_true, ↓reduceIte, neg_mul, sub_eq_add_neg]
            using (hFree i hi).2
      | true => simpa only [↓reduceIte] using (hFree i hi).1

end Grunbaum2003


-- Local ingredient: FiniteLinearStep

set_option autoImplicit false
open scoped Topology

namespace Grunbaum2003

                                                                         
                                                               
theorem exists_positive_step_preserving_inactive_strict {ι E : Type*}
    [Fintype ι] [AddCommGroup E] [Module ℝ E]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (I : Finset ι) (x₀ u : E)
    (hStrict : ∀ i, i ∉ I → a i x₀ < b i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, i ∉ I → a i (x₀ + t • u) < b i := by
  classical
  have hEvent : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ i, i ∉ I → a i (x₀ + t • u) < b i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i ∈ I
    · exact Filter.Eventually.of_forall (fun _ h => (h hi).elim)
    · have hCont : ContinuousAt (fun t : ℝ => a i x₀ + t * a i u) 0 := by fun_prop
      have hZero : a i x₀ + (0 : ℝ) * a i u < b i := by
        simpa only [zero_mul, add_zero] using hStrict i hi
      have hLt := hCont.tendsto.eventually (Iio_mem_nhds hZero)
      filter_upwards [hLt] with t ht
      intro _
      simpa only [map_add, map_smul, smul_eq_mul] using ht
  exact hEvent.exists_gt

                                                                          
                                                    
theorem exists_positive_step_releasing_active {ι E : Type*}
    [Fintype ι] [AddCommGroup E] [Module ℝ E]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (I : Finset ι) (x₀ u : E)
    (hActive : ∀ i ∈ I, a i x₀ = b i)
    (hStrict : ∀ i, i ∉ I → a i x₀ < b i)
    (hRelease : ∀ i ∈ I, a i u < 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, a i (x₀ + t • u) < b i := by
  classical
  obtain ⟨t, ht, hStep⟩ :=
    exists_positive_step_preserving_inactive_strict a b I x₀ u hStrict
  refine ⟨t, ht, ?_⟩
  intro i
  by_cases hi : i ∈ I
  · have hNeg : t * a i u < 0 := mul_neg_of_pos_of_neg ht (hRelease i hi)
    calc
      a i (x₀ + t • u) = b i + t * a i u := by
        rw [map_add, map_smul, hActive i hi, smul_eq_mul]
      _ < b i + 0 := by simpa only [add_comm] using add_lt_add_left hNeg (b i)
      _ = b i := add_zero _
  · exact hStep i hi

end Grunbaum2003


-- Local ingredient: StrictFeasibleProjection

set_option autoImplicit false

namespace Grunbaum2003

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

                                                                           
                                                                            
                                                                                
theorem exposed_image_face_eq_full_of_strict_feasible_point
    {ι : Type*} [Fintype ι] (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (P : Set E) (hP : P = {x | ∀ i, a i x ≤ b i})
    (π : E →L[ℝ] F) (hπ : Function.Surjective π)
    (G : Set F) (hG : IsExposed ℝ (π '' P) G)
    (x₀ : E) (hStrict : ∀ i, a i x₀ < b i) (hxG : π x₀ ∈ G) :
    G = π '' P := by
  classical
  obtain ⟨L, hL⟩ := hG ⟨π x₀, hxG⟩
  have hMax : ∀ y ∈ P, L (π y) ≤ L (π x₀) := by
    have hx : π x₀ ∈ {z ∈ π '' P | ∀ w ∈ π '' P, L w ≤ L z} := hL ▸ hxG
    intro y hy
    exact hx.2 (π y) ⟨y, hy, rfl⟩
  have hZero : L = 0 := by
    by_contra hne
    have hPos : ∃ v : F, 0 < L v := by
      by_contra hNoPos
      have hNonpos (v : F) : L v ≤ 0 := le_of_not_gt (fun h => hNoPos ⟨v, h⟩)
      apply hne
      ext v
      change L v = 0
      have h₁ := hNonpos v
      have h₂ := hNonpos (-v)
      rw [map_neg] at h₂
      linarith
    obtain ⟨v, hv⟩ := hPos
    obtain ⟨u, hu⟩ := hπ v
    obtain ⟨t, ht, hStep⟩ := exists_positive_step_preserving_inactive_strict
      a b ∅ x₀ u (fun i _ => hStrict i)
    have hy : x₀ + t • u ∈ P := by
      rw [hP]
      exact fun i => (hStep i (by simp)).le
    have hBound := hMax (x₀ + t • u) hy
    have hApply : L (π (x₀ + t • u)) = L (π x₀) + t * L v := by
      rw [map_add, map_smul, map_add, map_smul, hu, smul_eq_mul]
    rw [hApply] at hBound
    have hPositive := mul_pos ht hv
    linarith
  rw [hL, hZero]
  exact Set.Subset.antisymm (fun _ hx => hx.1)
    (fun _ hx => ⟨hx, fun _ _ => le_rfl⟩)

end Grunbaum2003


-- Local ingredient: ProjectionFaceRelease

set_option autoImplicit false

namespace Grunbaum2003

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

                                                                          
                                                                           
theorem exposed_image_face_eq_full_of_releasing_kernel_direction
    {ι : Type*} [Fintype ι] (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (P : Set E) (hP : P = {x | ∀ i, a i x ≤ b i})
    (π : E →L[ℝ] F) (hπ : Function.Surjective π)
    (G : Set F) (hG : IsExposed ℝ (π '' P) G)
    (I : Finset ι) (x₀ u : E)
    (hActive : ∀ i ∈ I, a i x₀ = b i)
    (hStrict : ∀ i, i ∉ I → a i x₀ < b i)
    (hKernel : π u = 0) (hRelease : ∀ i ∈ I, a i u < 0)
    (hxG : π x₀ ∈ G) : G = π '' P := by
  obtain ⟨t, _, hAllStrict⟩ := exists_positive_step_releasing_active
    a b I x₀ u hActive hStrict hRelease
  apply exposed_image_face_eq_full_of_strict_feasible_point
    a b P hP π hπ G hG (x₀ + t • u) hAllStrict
  simpa only [map_add, map_smul, hKernel, smul_zero, add_zero] using hxG

end Grunbaum2003


-- Local ingredient: CanonicalCubes

set_option autoImplicit false

namespace Grunbaum2003

theorem isDPolytope_centered_cube (n : ℕ) :
    IsDPolytope {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1} := by
  induction n with
  | zero =>
    have hUniv : {x : Fin 0 → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1} = Set.univ :=
      Set.eq_univ_of_forall (fun _ i => Fin.elim0 i)
    constructor
    · refine ⟨{0}, Set.finite_singleton _, Set.singleton_nonempty _, ?_⟩
      rw [hUniv, convexHull_singleton]
      ext x
      simp only [Set.mem_univ, Set.mem_singleton_iff, true_iff]
      exact Subsingleton.elim x 0
    · rw [hUniv, AffineSubspace.span_univ]
  | succ n ih =>
    have h := isDPolytope_deformed_interval _ ih (AffineMap.const ℝ _ 1)
      (fun _ _ => zero_lt_one)
    change IsDPolytope (snocLinearEquiv n ''
      {z : (Fin n → ℝ) × ℝ |
        (∀ i, -1 ≤ z.1 i ∧ z.1 i ≤ 1) ∧ -1 ≤ z.2 ∧ z.2 ≤ 1}) at h
    rwa [snocLinearEquiv_image_centered_cube] at h

theorem isDPolytope_image_affineEquiv {n m : ℕ}
    (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin m → ℝ))
    (P : Set (Fin n → ℝ)) (hP : IsDPolytope P) : IsDPolytope (e '' P) := by
  obtain ⟨⟨V, hV, hVne, hHull⟩, hSpan⟩ := hP
  constructor
  · refine ⟨e '' V, hV.image e, hVne.image e, ?_⟩
    rw [hHull]
    exact e.toAffineMap.image_convexHull V
  · exact e.toAffineMap.span_eq_top_of_surjective e.surjective hSpan

                                                                     
                                  
noncomputable def centeredToUnitCube (n : ℕ) :
    (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ) :=
  (LinearEquiv.smulOfNeZero ℝ (Fin n → ℝ) (1 / 2) (by norm_num)).toAffineEquiv.trans
    (AffineEquiv.constVAdd ℝ (Fin n → ℝ) (fun _ => 1 / 2))

theorem centeredToUnitCube_apply (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    centeredToUnitCube n x i = (x i + 1) / 2 := by
  change (1 / 2 : ℝ) + (1 / 2) * x i = (x i + 1) / 2
  ring

theorem centeredToUnitCube_image (n : ℕ) :
    centeredToUnitCube n '' {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1} =
      standardCube n := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩ i
    rw [centeredToUnitCube_apply]
    constructor <;> linarith [hx i]
  · intro y hy
    refine ⟨fun i => 2 * y i - 1, ?_, ?_⟩
    · intro i
      constructor <;> linarith [hy i]
    · ext i
      rw [centeredToUnitCube_apply]
      ring

theorem isDPolytope_standardCube (n : ℕ) : IsDPolytope (standardCube n) := by
  rw [← centeredToUnitCube_image]
  exact isDPolytope_image_affineEquiv (centeredToUnitCube n) _ (isDPolytope_centered_cube n)

end Grunbaum2003


-- Local ingredient: CubeFaceModel

set_option autoImplicit false

namespace Grunbaum2003

                                                                        
                                                                         
                                                                         
theorem centered_cube_coordinate_face_orderIso {n : ℕ}
    (I : Finset (Fin n)) (σ : Fin n → Bool) :
    Nonempty (PolytopeFace
      {x : Fin n → ℝ | (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧
        ∀ i ∈ I, x i = if σ i then 1 else -1} ≃o
      PolytopeFace (standardCube (n - I.card))) := by
  classical
  let U := {i : Fin n // i ∉ I}
  let k := Fintype.card U
  let F : Set (Fin n → ℝ) := {x | (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧
    ∀ i ∈ I, x i = if σ i then 1 else -1}
  let anchor : Fin n → ℝ := fun i => if i ∈ I then (if σ i then 1 else -1) else 0
  let L : (U → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i => if hi : i ∈ I then 0 else LinearMap.proj (⟨i, hi⟩ : U))
  let f : (U → ℝ) →ᵃ[ℝ] (Fin n → ℝ) :=
    L.toAffineMap + AffineMap.const ℝ (U → ℝ) anchor
  have hApply (y : U → ℝ) (i : Fin n) :
      f y i = if hi : i ∈ I then (if σ i then 1 else -1) else y ⟨i, hi⟩ := by
    by_cases hi : i ∈ I <;> simp [f, L, anchor, hi]
  have hInj : Function.Injective f := by
    intro y z hyz
    funext i
    have h := congrFun hyz i.val
    simpa only [hApply, dif_neg i.property] using h
  have hImage : f '' {y : U → ℝ | ∀ i, -1 ≤ y i ∧ y i ≤ 1} = F := by
    apply Set.Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨fun i => ?_, fun i hi => ?_⟩
      · rw [hApply]
        by_cases hi : i ∈ I
        · rw [dif_pos hi]
          cases σ i <;> simp
        · rw [dif_neg hi]
          exact hy ⟨i, hi⟩
      · rw [hApply, dif_pos hi]
    · intro x hx
      let y : U → ℝ := fun i => x i.val
      refine ⟨y, fun i => hx.1 i.val, ?_⟩
      funext i
      rw [hApply]
      by_cases hi : i ∈ I
      · rw [dif_pos hi]
        exact (hx.2 i hi).symm
      · rw [dif_neg hi]
  let r : (U → ℝ) ≃ₗ[ℝ] (Fin k → ℝ) :=
    LinearEquiv.piCongrLeft' ℝ (fun _ : U => ℝ) (Fintype.equivFin U)
  have hRImage : r.symm '' {y : Fin k → ℝ | ∀ i, -1 ≤ y i ∧ y i ≤ 1} =
      {y : U → ℝ | ∀ i, -1 ≤ y i ∧ y i ≤ 1} := by
    apply Set.Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩ i
      simpa [r, LinearEquiv.piCongrLeft'] using hy ((Fintype.equivFin U) i)
    · intro y hy
      refine ⟨r y, ?_, r.symm_apply_apply y⟩
      intro i
      change -1 ≤ y ((Fintype.equivFin U).symm i) ∧
        y ((Fintype.equivFin U).symm i) ≤ 1
      exact hy _
  let f' : (Fin k → ℝ) →ᵃ[ℝ] (Fin n → ℝ) := f.comp r.symm.toAffineMap
  have hf' : Function.Injective f' := hInj.comp r.symm.injective
  have hfImage : f' '' {y : Fin k → ℝ | ∀ i, -1 ≤ y i ∧ y i ≤ 1} = F := by
    change (f ∘ r.symm) '' _ = F
    calc
      (f ∘ r.symm) '' {y : Fin k → ℝ | ∀ i, -1 ≤ y i ∧ y i ≤ 1} =
          f '' (r.symm '' {y : Fin k → ℝ | ∀ i, -1 ≤ y i ∧ y i ≤ 1}) :=
        (Set.image_image f r.symm _).symm
      _ = F := by rw [hRImage]; exact hImage
  obtain ⟨e, _⟩ := exposedFaces_orderIso_affineImage f' hf'
    {y : Fin k → ℝ | ∀ i, -1 ≤ y i ∧ y i ≤ 1}
  rw [hfImage] at e
  obtain ⟨eUnit, _⟩ := exposedFaces_orderIso_affineImage (centeredToUnitCube k).toAffineMap
    (centeredToUnitCube k).injective {y : Fin k → ℝ | ∀ i, -1 ≤ y i ∧ y i ≤ 1}
  have hUnit : (centeredToUnitCube k).toAffineMap ''
      {y : Fin k → ℝ | ∀ i, -1 ≤ y i ∧ y i ≤ 1} = standardCube k := by
    simpa only [AffineEquiv.coe_coe] using centeredToUnitCube_image k
  rw [hUnit] at eUnit
  have hResult : Nonempty (PolytopeFace F ≃o PolytopeFace (standardCube k)) :=
    ⟨e.symm.trans eUnit⟩
  have hCard : Fintype.card U = n - I.card := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_fin, Fintype.card_coe]
  change Nonempty (PolytopeFace F ≃o PolytopeFace (standardCube (n - I.card)))
  have hk : k = n - I.card := hCard
  rwa [hk] at hResult

end Grunbaum2003


-- Local ingredient: ExposedTransAccepted

                                                                                                   

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

                                                                           
lemma extremePoints_eq_exposedSingletons {d : ℕ} (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} := by
  classical
  rcases hP.1 with ⟨V0, hV0_fin, _, hP_eq⟩
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_setOf_eq]
    have hx_in_P : x ∈ P := extremePoints_subset hx
    have hx_ext : IsExtreme ℝ P {x} := isExtreme_singleton.mpr hx
    have hx_not_in : x ∉ convexHull ℝ (V0 \ {x}) := by
      intro hx_in
      have h_sub : convexHull ℝ (V0 \ {x}) ⊆ P := by
        rw [hP_eq]
        exact convexHull_mono Set.diff_subset
      have hx_ext' : IsExtreme ℝ (convexHull ℝ (V0 \ {x})) {x} :=
        hx_ext.mono h_sub (Set.singleton_subset_iff.mpr hx_in)
      have hx_ep : x ∈ (convexHull ℝ (V0 \ {x})).extremePoints ℝ :=
        isExtreme_singleton.mp hx_ext'
      have hx_diff : x ∈ V0 \ {x} := extremePoints_convexHull_subset hx_ep
      exact hx_diff.2 rfl
    have hC_conv : Convex ℝ (convexHull ℝ (V0 \ {x})) := convex_convexHull ℝ _
    have hC_closed : IsClosed (convexHull ℝ (V0 \ {x})) :=
      ((hV0_fin.diff).isCompact_convexHull ℝ).isClosed
    obtain ⟨l, u, hlu, hux⟩ := geometric_hahn_banach_closed_point hC_conv hC_closed hx_not_in
    intro _
    refine ⟨l, ?_⟩
    apply Set.Subset.antisymm
    · rintro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      refine ⟨hx_in_P, ?_⟩
      have h_le : P ⊆ {z : Fin d → ℝ | l z ≤ l x} := by
        rw [hP_eq]
        refine convexHull_min ?_ ?_
        · intro s hs
          change l s ≤ l x
          by_cases hsx : s = x
          · rw [hsx]
          · have hs_diff : s ∈ V0 \ {x} := ⟨hs, hsx⟩
            exact le_of_lt ((hlu s (subset_convexHull ℝ _ hs_diff)).trans hux)
        · intro z1 hz1 z2 hz2 a b ha hb hab
          change l z1 ≤ l x at hz1
          change l z2 ≤ l x at hz2
          change l (a • z1 + b • z2) ≤ l x
          rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
          have hb_eq : b = 1 - a := by linarith
          subst hb_eq
          nlinarith
      intro z hz
      exact h_le hz
    · rintro y ⟨hyP, hymax⟩
      rw [Set.mem_singleton_iff]
      have hly : l x ≤ l y := hymax x hx_in_P
      rw [hP_eq] at hyP
      let Vfin := hV0_fin.toFinset
      have hVfin : (Vfin : Set (Fin d → ℝ)) = V0 := hV0_fin.coe_toFinset
      rw [← hVfin] at hyP
      obtain ⟨w, hw0, hw1, rfl⟩ := Finset.mem_convexHull'.mp hyP
      have h_sum_nonneg : ∀ s ∈ Vfin, 0 ≤ w s * (l x - l s) := by
        intro s hs
        refine mul_nonneg (hw0 s hs) ?_
        by_cases hsx : s = x
        · subst hsx; linarith
        · have hs_diff : s ∈ V0 \ {x} := ⟨hV0_fin.mem_toFinset.mp hs, hsx⟩
          have hls := hlu s (subset_convexHull ℝ _ hs_diff)
          linarith
      have h_sum_le : ∑ s ∈ Vfin, w s * (l x - l s) ≤ 0 := by
        have h_eq : ∑ s ∈ Vfin, w s * (l x - l s) = l x - l (∑ s ∈ Vfin, w s • s) := by
          rw [map_sum]
          simp_rw [map_smul, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
            hw1, one_mul]
        linarith
      have h_all_zero : ∀ s ∈ Vfin, w s * (l x - l s) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg h_sum_nonneg).mp
          (le_antisymm h_sum_le (Finset.sum_nonneg h_sum_nonneg))
      have hw_zero_of_ne : ∀ s ∈ Vfin, s ≠ x → w s = 0 := by
        intro s hs hsx
        have hs_diff : s ∈ V0 \ {x} := ⟨hV0_fin.mem_toFinset.mp hs, hsx⟩
        have hls := (hlu s (subset_convexHull ℝ _ hs_diff)).trans hux
        have h_z := h_all_zero s hs
        rcases mul_eq_zero.mp h_z with hw_z | hl_z
        · exact hw_z
        · linarith
      calc ∑ s ∈ Vfin, w s • s
          = ∑ s ∈ Vfin, w s • x := by
            refine Finset.sum_congr rfl (fun s hs => ?_)
            by_cases hsx : s = x
            · subst hsx; rfl
            · simp [hw_zero_of_ne s hs hsx]
        _ = (∑ s ∈ Vfin, w s) • x := (Finset.sum_smul).symm
        _ = x := by rw [hw1, one_smul]
  · intro x hx
    exact exposedPoints_subset_extremePoints (mem_exposedPoints_iff_exposed_singleton.mpr hx)

                                                                                          
                                                                                          
                                                               
theorem polytope_face_eq_convexHull_exposed_vertices (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ F : PolytopeFace P,
        F.val = convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}) := by
  rcases hP.1 with ⟨V0, hV0_fin, _, hP_eq⟩
  have hExtEq : P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} :=
    extremePoints_eq_exposedSingletons P hP
  have hVertFin : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite := by
    rw [← hExtEq, hP_eq]
    exact hV0_fin.subset extremePoints_convexHull_subset
  refine ⟨hVertFin, ?_⟩
  intro F
  have hP_comp : IsCompact P := hP_eq ▸ hV0_fin.isCompact_convexHull ℝ
  have hP_conv : Convex ℝ P := hP_eq ▸ convex_convexHull ℝ V0
  have hF_comp : IsCompact F.val := F.property.isCompact hP_comp
  have hF_conv : Convex ℝ F.val := F.property.convex hP_conv
  have hF_ext : F.val.extremePoints ℝ = F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} := by
    rw [F.property.isExtreme.extremePoints_eq, ← hExtEq]
  have h_km := closure_convexHull_extremePoints hF_comp hF_conv
  rw [hF_ext] at h_km
  have h_closed : IsClosed (convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) :=
    ((hVertFin.subset Set.inter_subset_right).isCompact_convexHull ℝ).isClosed
  rw [h_closed.closure_eq] at h_km
  exact h_km.symm

end Grunbaum2003

                                        

set_option autoImplicit false

namespace Grunbaum2003

                                                                                            
                                                                                  
theorem isExposed_trans_polytope (d : ℕ) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (F G : Set (Fin d → ℝ)) (hF : IsExposed ℝ P F) (hG : IsExposed ℝ F G) :
    IsExposed ℝ P G := by
  classical
  by_cases hEmpty : G = ∅
  · rw [hEmpty]
    exact isExposed_empty
  obtain ⟨z, hzG⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
  have hzF : z ∈ F := hG.subset hzG
  have hzP : z ∈ P := hF.subset hzF
  obtain ⟨l, hFl⟩ := hF ⟨z, hzF⟩
  obtain ⟨m, hGm⟩ := hG ⟨z, hzG⟩
  have hlMax : ∀ x ∈ P, l x ≤ l z := by
    have hz := hzF
    rw [hFl] at hz
    exact hz.2
  have hmMax : ∀ x ∈ F, m x ≤ m z := by
    have hz := hzG
    rw [hGm] at hz
    exact hz.2
  have hFlevel (x : Fin d → ℝ) (hxP : x ∈ P) : x ∈ F ↔ l x = l z := by
    constructor
    · intro hxF
      rw [hFl] at hxF
      exact le_antisymm (hlMax x hxP) (hxF.2 z hzP)
    · intro hxEq
      rw [hFl]
      exact ⟨hxP, fun y hy => by rw [hxEq]; exact hlMax y hy⟩
  have hGlevel (x : Fin d → ℝ) (hxF : x ∈ F) : x ∈ G ↔ m x = m z := by
    constructor
    · intro hxG
      rw [hGm] at hxG
      exact le_antisymm (hmMax x hxF) (hxG.2 z hzF)
    · intro hxEq
      rw [hGm]
      exact ⟨hxF, fun y hy => by rw [hxEq]; exact hmMax y hy⟩
  let V := {x : Fin d → ℝ | IsExposed ℝ P {x}}
  obtain ⟨hVfin, hFaces⟩ := polytope_face_eq_convexHull_exposed_vertices d P hP
  have hVP : V ⊆ P := fun x hx => (mem_exposedPoints_iff_exposed_singleton.mpr hx).1
  have hPgen : P = convexHull ℝ V := by
    have h := hFaces ⟨P, IsExposed.refl P⟩
    change P = convexHull ℝ (P ∩ V) at h
    rwa [Set.inter_eq_right.mpr hVP] at h
  have hPconv : Convex ℝ P := hPgen ▸ convex_convexHull ℝ V
  let r : (Fin d → ℝ) → ℝ := fun w => (m w - m z) / (l z - l w)
  obtain ⟨M, hM⟩ := ((hVfin.image r).insert 0).bddAbove
  let C : ℝ := M + 1
  let n : StrongDual ℝ (Fin d → ℝ) := C • l + m
  have hStrict (w : Fin d → ℝ) (hwV : w ∈ V) (hwF : w ∉ F) : n w < n z := by
    have hwP : w ∈ P := hVP hwV
    have hlw : l w < l z := lt_of_le_of_ne (hlMax w hwP) (fun h => hwF ((hFlevel w hwP).mpr h))
    have hDen : 0 < l z - l w := sub_pos.mpr hlw
    have hRatio : r w < C := lt_of_le_of_lt (hM (Set.mem_insert_of_mem 0 ⟨w, hwV, rfl⟩)) (by dsimp [C]; linarith)
    have hNum : m w - m z < C * (l z - l w) := (div_lt_iff₀ hDen).mp hRatio
    change C * l w + m w < C * l z + m z
    nlinarith [hNum]
  have hGen (w : Fin d → ℝ) (hwV : w ∈ V) : n w ≤ n z := by
    by_cases hwF : w ∈ F
    · change C * l w + m w ≤ C * l z + m z
      rw [(hFlevel w (hVP hwV)).mp hwF]
      exact add_le_add le_rfl (hmMax w hwF)
    · exact (hStrict w hwV hwF).le
  have hnMax : ∀ x ∈ P, n x ≤ n z := by
    rw [hPgen]
    apply convexHull_min hGen
    intro x hx y hy a b ha hb hab
    change n (a • x + b • y) ≤ n z
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    calc
      a * n x + b * n y ≤ a * n z + b * n z :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
      _ = n z := by rw [← add_mul, hab, one_mul]
  let K := {x ∈ P | n x = n z}
  have hK : IsExposed ℝ P K := by
    intro _
    refine ⟨n, ?_⟩
    ext x
    constructor
    · rintro ⟨hxP, hxEq⟩
      exact ⟨hxP, fun y hy => (hnMax y hy).trans_eq hxEq.symm⟩
    · rintro ⟨hxP, hxMax⟩
      exact ⟨hxP, le_antisymm (hnMax x hxP) (hxMax z hzP)⟩
  have hKsubG : K ⊆ G := by
    have hHullK := hFaces ⟨K, hK⟩
    change K = convexHull ℝ (K ∩ V) at hHullK
    rw [hHullK]
    apply convexHull_min ?_ (hG.convex (hF.convex hPconv))
    rintro w ⟨hwK, hwV⟩
    have hwF : w ∈ F := by
      by_contra hnF
      exact (hStrict w hwV hnF).ne hwK.2
    apply (hGlevel w hwF).mpr
    have hEq : C * l w + m w = C * l z + m z := hwK.2
    rw [(hFlevel w hwK.1).mp hwF] at hEq
    linarith
  have hGsubK : G ⊆ K := by
    intro x hxG
    have hxF : x ∈ F := hG.subset hxG
    have hxP : x ∈ P := hF.subset hxF
    refine ⟨hxP, ?_⟩
    change C * l x + m x = C * l z + m z
    rw [(hFlevel x hxP).mp hxF, (hGlevel x hxF).mp hxG]
  have hKG : K = G := Set.Subset.antisymm hKsubG hGsubK
  rwa [hKG] at hK

end Grunbaum2003


-- Local ingredient: FaceBijectionRestrict

set_option autoImplicit false

namespace Grunbaum2003

                                                                           
                                                                                 
noncomputable def ExposedFaceBijection.restrict {n m : ℕ}
    {P : Set (Fin n → ℝ)} {Q : Set (Fin m → ℝ)}
    (e : ExposedFaceBijection P Q) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (S : Set (Fin n → ℝ)) (hS : IsExposed ℝ P S) :
    ExposedFaceBijection S (e.toFun '' S) where
  toFun := e.toFun
  invFun := e.invFun
  map_mem := fun x hx => ⟨x, hx, rfl⟩
  inv_mem := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hy
    rw [← hxy, e.left_inv x (hS.subset hx)]
    exact hx
  left_inv := fun x hx => e.left_inv x (hS.subset hx)
  right_inv := fun y hy => e.right_inv y ((e.map_face S hS).subset hy)
  map_face := by
    intro T hT
    have hTP := isExposed_trans_polytope n P hP S T hS hT
    exact (e.map_face T hTP).mono (e.map_face S hS).subset (Set.image_mono hT.subset)
  inv_face := by
    intro T hT
    have hTQ := isExposed_trans_polytope m Q hQ (e.toFun '' S) T (e.map_face S hS) hT
    have hInv := e.inv_face T hTQ
    have hSub : e.invFun '' T ⊆ S := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := hT.subset hy
      rw [← hxy, e.left_inv x (hS.subset hx)]
      exact hx
    exact hInv.mono hS.subset hSub

end Grunbaum2003


-- Local ingredient: TriangularFaceModels

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

                                                                         
                                                           
theorem triangular_cube_active_face_image {n : ℕ}
    (B : Fin n → Fin n → ℝ) (δ : ℝ) (b : Fin n → ℝ) (P : Set (Fin n → ℝ))
    (e : ExposedFaceBijection P {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1})
    (hCoordinates : ∀ x ∈ P, ∀ i,
      0 < b i - (∑ j : Fin n, if j < i then B i j * x j else 0) ∧
      e.toFun x i = δ * x i / (b i - ∑ j : Fin n, if j < i then B i j * x j else 0))
    (I : Finset (Fin n)) (σ : Fin n → Bool) :
    e.toFun '' {x | x ∈ P ∧ ∀ i ∈ I,
      (∑ j : Fin n, if j < i then B i j * x j else 0) +
        (if σ i then δ else -δ) * x i = b i} =
      {y | (∀ i, -1 ≤ y i ∧ y i ≤ 1) ∧ ∀ i ∈ I, y i = if σ i then 1 else -1} := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxP, hx⟩, rfl⟩
    refine ⟨e.map_mem x hxP, fun i hi => ?_⟩
    rw [(hCoordinates x hxP i).2]
    exact (normalized_coordinate_eq_endpoint_iff _ _ δ (x i) (σ i)
      (hCoordinates x hxP i).1).mpr (hx i hi)
  · rintro ⟨hyQ, hy⟩
    have hxP := e.inv_mem y hyQ
    refine ⟨e.invFun y, ⟨hxP, fun i hi => ?_⟩, e.right_inv y hyQ⟩
    apply (normalized_coordinate_eq_endpoint_iff _ _ δ (e.invFun y i) (σ i)
      (hCoordinates _ hxP i).1).mp
    rw [← (hCoordinates _ hxP i).2, e.right_inv y hyQ]
    exact hy i hi

                                                                         
                                                                    
theorem triangular_cube_active_face_model {n : ℕ}
    (B : Fin n → Fin n → ℝ) (δ : ℝ) (b : Fin n → ℝ) (P : Set (Fin n → ℝ))
    (hP : IsDPolytope P)
    (e : ExposedFaceBijection P {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1})
    (hCoordinates : ∀ x ∈ P, ∀ i,
      0 < b i - (∑ j : Fin n, if j < i then B i j * x j else 0) ∧
      e.toFun x i = δ * x i / (b i - ∑ j : Fin n, if j < i then B i j * x j else 0))
    (I : Finset (Fin n)) (σ : Fin n → Bool)
    (hF : IsExposed ℝ P {x | x ∈ P ∧ ∀ i ∈ I,
      (∑ j : Fin n, if j < i then B i j * x j else 0) +
        (if σ i then δ else -δ) * x i = b i}) :
    Nonempty (PolytopeFace {x | x ∈ P ∧ ∀ i ∈ I,
      (∑ j : Fin n, if j < i then B i j * x j else 0) +
        (if σ i then δ else -δ) * x i = b i} ≃o
      PolytopeFace (standardCube (n - I.card))) := by
  obtain ⟨eFace, _⟩ :=
    (e.restrict hP (isDPolytope_centered_cube n) _ hF).exists_orderIso
  rw [triangular_cube_active_face_image B δ b P e hCoordinates I σ] at eFace
  obtain ⟨eCube⟩ := centered_cube_coordinate_face_orderIso I σ
  exact ⟨eFace.trans eCube⟩

                                                                            
                                                                           
                                                                        
theorem triangular_cube_all_face_models {n : ℕ}
    (B : Fin n → Fin n → ℝ) (δ : ℝ) (b : Fin n → ℝ) (P : Set (Fin n → ℝ))
    (hP : IsDPolytope P)
    (e : ExposedFaceBijection P {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1})
    (hCoordinates : ∀ x ∈ P, ∀ i,
      0 < b i - (∑ j : Fin n, if j < i then B i j * x j else 0) ∧
      e.toFun x i = δ * x i / (b i - ∑ j : Fin n, if j < i then B i j * x j else 0))
    (S : Set (Fin n → ℝ)) (hS : IsExposed ℝ P S) (hSne : S.Nonempty) :
    ∃ I : Finset (Fin n), ∃ σ : Fin n → Bool,
      S = {x | x ∈ P ∧ ∀ i ∈ I,
        (∑ j : Fin n, if j < i then B i j * x j else 0) +
          (if σ i then δ else -δ) * x i = b i} ∧
      Nonempty (PolytopeFace S ≃o PolytopeFace (standardCube (n - I.card))) := by
  obtain ⟨I, σ, hSSet⟩ := triangular_cube_face_classification B δ b P e hCoordinates S hS hSne
  refine ⟨I, σ, hSSet, ?_⟩
  rw [hSSet]
  exact triangular_cube_active_face_model B δ b P hP e hCoordinates I σ (hSSet ▸ hS)

end Grunbaum2003


-- Local ingredient: ActiveFaceSpan

set_option autoImplicit false

namespace Grunbaum2003

                                                                            
                                                                              
                                                                            
theorem vectorSpan_halfspace_face_eq_active_kernels {ι E : Type*}
    [Fintype ι] [AddCommGroup E] [Module ℝ E]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (I : Finset ι) (x₀ : E)
    (hActive : ∀ i ∈ I, a i x₀ = b i)
    (hStrict : ∀ i, i ∉ I → a i x₀ < b i) :
    vectorSpan ℝ {x : E | (∀ i, a i x ≤ b i) ∧ ∀ i ∈ I, a i x = b i} =
      ⨅ i ∈ I, (a i).ker := by
  classical
  let F : Set E := {x | (∀ i, a i x ≤ b i) ∧ ∀ i ∈ I, a i x = b i}
  have hx₀ : x₀ ∈ F := by
    refine ⟨?_, hActive⟩
    intro i
    by_cases hi : i ∈ I
    · exact (hActive i hi).le
    · exact (hStrict i hi).le
  change vectorSpan ℝ F = _
  apply le_antisymm
  · refine le_iInf (fun i => le_iInf (fun hi => ?_))
    rw [vectorSpan_eq_span_vsub_set_right ℝ hx₀]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    change a i (x -ᵥ x₀) = 0
    rw [vsub_eq_sub, map_sub, hx.2 i hi, hActive i hi, sub_self]
  · intro u hu
    have hKernel : ∀ i ∈ I, a i u = 0 := by
      simpa only [Submodule.mem_iInf, LinearMap.mem_ker] using hu
    obtain ⟨t, ht, hStep⟩ :=
      exists_positive_step_preserving_inactive_strict a b I x₀ u hStrict
    have hPoint : x₀ + t • u ∈ F := by
      refine ⟨?_, ?_⟩
      · intro i
        by_cases hi : i ∈ I
        · simp only [map_add, map_smul, hKernel i hi, smul_zero, add_zero,
            hActive i hi, le_refl]
        · exact (hStep i hi).le
      · intro i hi
        simp only [map_add, map_smul, hKernel i hi, smul_zero, add_zero, hActive i hi]
    have hScaled : t • u ∈ vectorSpan ℝ F := by
      have h := vsub_mem_vectorSpan ℝ hPoint hx₀
      simpa only [vsub_eq_sub, add_sub_cancel_left] using h
    exact ((vectorSpan ℝ F).smul_mem_iff (ne_of_gt ht)).mp hScaled

end Grunbaum2003


-- Local ingredient: RegularMinorRank

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

                                                                          
                                                         
theorem mulVec_surjective_of_regular_column_minor {n k : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (u : Fin k → Fin n)
    (hDet : Matrix.det (fun i j : Fin k => A i (u j)) ≠ 0) :
    Function.Surjective A.mulVec := by
  classical
  let M : Matrix (Fin k) (Fin k) ℝ := fun i j => A i (u j)
  let C : Matrix (Fin n) (Fin k) ℝ := fun i j => if i = u j then 1 else 0
  have hAC : A * C = M := by
    ext i j
    change (∑ l : Fin n, A i l * (if l = u j then 1 else 0)) = A i (u j)
    simp [mul_ite]
  have hRight : A * (C * M⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, hAC]
    exact Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hDet)
  exact Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨C * M⁻¹, hRight⟩

                                                                         
                                                       
theorem surjective_and_finrank_ker_of_regular_column_minor {n k : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (u : Fin k → Fin n)
    (hDet : Matrix.det (fun i j : Fin k => A i (u j)) ≠ 0) :
    Function.Surjective (Matrix.toLin' A) ∧
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A)) = n - k := by
  have hSurj : Function.Surjective (Matrix.toLin' A) :=
    mulVec_surjective_of_regular_column_minor A u hDet
  have hRange : LinearMap.range (Matrix.toLin' A) = ⊤ :=
    LinearMap.range_eq_top.mpr hSurj
  have hRangeDim : Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) = k := by
    have h := congrArg
      (fun S : Submodule ℝ (Fin k → ℝ) => Module.finrank ℝ S) hRange
    simpa only [finrank_top, Module.finrank_fin_fun] using h
  have hRank := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
  rw [hRangeDim] at hRank
  simp only [Module.finrank_fin_fun] at hRank
  exact ⟨hSurj, by omega⟩

end Grunbaum2003


-- Local ingredient: FullTriangularRank

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

                                                                           
                                                                          
                                                                               
theorem full_triangular_normal_minor_regular {n k : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) (hδ : δ ≠ 0)
    (u : Fin k → Fin n) (hu : StrictMono u) (σ : Fin n → Bool) :
    Matrix.det (fun i j : Fin k =>
      if (u j).val < (u i).val then B (u i) (u j)
      else if (u j).val = (u i).val then
        (if σ (u i) then δ else -δ) else 0) ≠ 0 := by
  classical
  let M : Matrix (Fin k) (Fin k) ℝ := fun i j =>
    if (u j).val < (u i).val then B (u i) (u j)
    else if (u j).val = (u i).val then
      (if σ (u i) then δ else -δ) else 0
  have hLower : M.IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    have hlt : (u i).val < (u j).val := hu hij
    change (if (u j).val < (u i).val then B (u i) (u j)
      else if (u j).val = (u i).val then
        (if σ (u i) then δ else -δ) else 0) = 0
    rw [if_neg (not_lt_of_ge hlt.le), if_neg (ne_of_gt hlt)]
  have hDiag (i : Fin k) : M i i ≠ 0 := by
    dsimp only [M]
    rw [if_neg (lt_irrefl _), if_pos rfl]
    split
    · exact hδ
    · exact neg_ne_zero.mpr hδ
  change M.det ≠ 0
  rw [Matrix.det_of_isLowerTriangular M hLower]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hDiag i)

                                                                        
                                                  
theorem full_triangular_active_map_surjective_and_finrank_ker {n k : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) (hδ : δ ≠ 0)
    (u : Fin k → Fin n) (hu : StrictMono u) (σ : Fin n → Bool) :
    let A : Matrix (Fin k) (Fin n) ℝ := fun i j =>
      if j.val < (u i).val then B (u i) j
      else if j.val = (u i).val then
        (if σ (u i) then δ else -δ) else 0
    Function.Surjective (Matrix.toLin' A) ∧
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A)) = n - k := by
  dsimp only
  apply surjective_and_finrank_ker_of_regular_column_minor _ u
  exact full_triangular_normal_minor_regular B δ hδ u hu σ

end Grunbaum2003


-- Local ingredient: SourceFaceRank

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace Grunbaum2003

private def sourceTriangularNormal {n : ℕ} (B : Fin n → Fin n → ℝ) (δ : ℝ)
    (i : Fin n) (s : Bool) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ j : Fin n,
    (if j < i then B i j else if j = i then (if s then δ else -δ) else 0) * x j
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => mul_left_comm _ c (x j))

private theorem sourceTriangularNormal_apply {n : ℕ} (B : Fin n → Fin n → ℝ)
    (δ : ℝ) (i : Fin n) (s : Bool) (x : Fin n → ℝ) :
    sourceTriangularNormal B δ i s x =
      (∑ j : Fin n, if j < i then B i j * x j else 0) +
        (if s then δ else -δ) * x i := by
  classical
  have hsplit (j : Fin n) :
      (if j < i then B i j else if j = i then (if s then δ else -δ) else 0) * x j =
        (if j < i then B i j * x j else 0) +
          (if j = i then (if s then δ else -δ) * x j else 0) := by
    by_cases hlt : j < i
    · have hne : j ≠ i := ne_of_lt hlt
      simp only [if_pos hlt, if_neg hne, add_zero]
    · by_cases heq : j = i
      · subst j
        simp only [lt_irrefl, ↓reduceIte, zero_add]
      · simp only [if_neg hlt, if_neg heq, zero_mul, add_zero]
  change (∑ j : Fin n, _) = _
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib]
  simp

private def sourceActivePairs {n : ℕ} (I : Finset (Fin n)) (σ : Fin n → Bool) :
    Finset (Fin n × Bool) := I.image (fun i => (i, σ i))

private theorem mem_sourceActivePairs {n : ℕ} (I : Finset (Fin n)) (σ : Fin n → Bool)
    (i : Fin n) (s : Bool) : (i, s) ∈ sourceActivePairs I σ ↔ i ∈ I ∧ s = σ i := by
  classical
  constructor
  · intro h
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
    have hji : j = i := congrArg Prod.fst heq
    have hjs : σ j = s := congrArg Prod.snd heq
    subst j
    exact ⟨hj, hjs.symm⟩
  · rintro ⟨hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

private theorem opposite_bool_coefficient (δ : ℝ) (s t : Bool) (h : s ≠ t) :
    (if s then δ else -δ) = -(if t then δ else -δ) := by
  cases s <;> cases t
  · exact False.elim (h rfl)
  · rfl
  · exact (neg_neg δ).symm
  · exact False.elim (h rfl)

                                                                           
                                                                           
                                                                
theorem triangular_source_coordinate_face_finrank {n : ℕ}
    (B : Fin n → Fin n → ℝ) (δ : ℝ) (hδ : δ ≠ 0) (b : Fin n → ℝ)
    (P : Set (Fin n → ℝ))
    (hP : P = {x : Fin n → ℝ | ∀ i,
      |δ * x i| ≤ b i - ∑ j : Fin n, if j < i then B i j * x j else 0})
    (e : ExposedFaceBijection P {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1})
    (hCoordinates : ∀ x ∈ P, ∀ i,
      0 < b i - (∑ j : Fin n, if j < i then B i j * x j else 0) ∧
      e.toFun x i = δ * x i / (b i - ∑ j : Fin n, if j < i then B i j * x j else 0))
    (I : Finset (Fin n)) (σ : Fin n → Bool) :
    Module.finrank ℝ (affineSpan ℝ {x : Fin n → ℝ | x ∈ P ∧ ∀ i ∈ I,
      (∑ j : Fin n, if j < i then B i j * x j else 0) +
        (if σ i then δ else -δ) * x i = b i}).direction = n - I.card := by
  classical
  let a : (Fin n × Bool) → (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    fun p => sourceTriangularNormal B δ p.1 p.2
  let β : Fin n × Bool → ℝ := fun p => b p.1
  let J := sourceActivePairs I σ
  let F : Set (Fin n → ℝ) := {x | x ∈ P ∧ ∀ i ∈ I,
    (∑ j : Fin n, if j < i then B i j * x j else 0) +
      (if σ i then δ else -δ) * x i = b i}
  obtain ⟨x₀, hx₀, hActive, hFree, hOpposite⟩ :=
    triangular_cube_face_strict_anchor B δ b P e hCoordinates I σ
  have hPall : P = {x : Fin n → ℝ | ∀ p : Fin n × Bool, a p x ≤ β p} := by
    ext x
    rw [hP]
    change (∀ i, |δ * x i| ≤ b i - ∑ j : Fin n, if j < i then B i j * x j else 0) ↔ _
    constructor
    · intro h p
      obtain ⟨hm, hp⟩ := abs_le.mp (h p.1)
      rw [show a p x = _ from sourceTriangularNormal_apply B δ p.1 p.2 x]
      cases p.2 <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_mul]
      all_goals dsimp only [β]; linarith only [hm, hp]
    · intro h i
      have hm := h (i, false)
      have hp := h (i, true)
      simp only [a, β, sourceTriangularNormal_apply, Bool.false_eq_true, ↓reduceIte,
        Prod.fst, Prod.snd, neg_mul] at hm hp
      apply abs_le.mpr
      constructor <;> linarith only [hm, hp]
  have hJA : ∀ p ∈ J, a p x₀ = β p := by
    rintro ⟨i, s⟩ hp
    obtain ⟨hi, hs⟩ := (mem_sourceActivePairs I σ i s).mp hp
    simpa only [a, β, sourceTriangularNormal_apply, Prod.fst, Prod.snd, hs]
      using hActive i hi
  have hJS : ∀ p, p ∉ J → a p x₀ < β p := by
    rintro ⟨i, s⟩ hp
    change sourceTriangularNormal B δ i s x₀ < b i
    rw [sourceTriangularNormal_apply]
    by_cases hi : i ∈ I
    · have hs : s ≠ σ i := by
        intro hs
        exact hp ((mem_sourceActivePairs I σ i s).mpr ⟨hi, hs⟩)
      rw [opposite_bool_coefficient δ s (σ i) hs, neg_mul, ← sub_eq_add_neg]
      exact hOpposite i hi
    · cases s with
      | false =>
          simpa only [Bool.false_eq_true, ↓reduceIte, neg_mul, sub_eq_add_neg] using (hFree i hi).2
      | true => simpa only [↓reduceIte] using (hFree i hi).1
  have hF : F = {x : Fin n → ℝ | (∀ p, a p x ≤ β p) ∧ ∀ p ∈ J, a p x = β p} := by
    ext x
    constructor
    · rintro ⟨hx, hfix⟩
      have hxall : ∀ p, a p x ≤ β p := by rwa [hPall] at hx
      refine ⟨hxall, ?_⟩
      rintro ⟨i, s⟩ hp
      obtain ⟨hi, hs⟩ := (mem_sourceActivePairs I σ i s).mp hp
      simpa only [a, β, Prod.fst, Prod.snd, sourceTriangularNormal_apply, hs] using hfix i hi
    · rintro ⟨hx, hfix⟩
      refine ⟨?_, ?_⟩
      · rwa [hPall]
      · intro i hi
        have h := hfix (i, σ i) ((mem_sourceActivePairs I σ i (σ i)).mpr ⟨hi, rfl⟩)
        simpa only [a, β, Prod.fst, Prod.snd, sourceTriangularNormal_apply] using h
  have hSpan : vectorSpan ℝ F = ⨅ p ∈ J, (a p).ker := by
    rw [hF]
    exact vectorSpan_halfspace_face_eq_active_kernels a β J x₀ hJA hJS
  let u : Fin I.card ↪o Fin n := I.orderEmbOfFin rfl
  let A : Matrix (Fin I.card) (Fin n) ℝ := fun i j =>
    if j.val < (u i).val then B (u i) j
    else if j.val = (u i).val then (if σ (u i) then δ else -δ) else 0
  have hMap (x : Fin n → ℝ) (r : Fin I.card) :
      (Matrix.toLin' A x) r = a (u r, σ (u r)) x := by
    change (∑ j : Fin n,
      (if j.val < (u r).val then B (u r) j else if j.val = (u r).val then
        (if σ (u r) then δ else -δ) else 0) * x j) =
      ∑ j : Fin n,
        (if j < u r then B (u r) j else if j = u r then
          (if σ (u r) then δ else -δ) else 0) * x j
    simp only [Fin.lt_def, Fin.val_inj]
  have hKer : (⨅ p ∈ J, (a p).ker) = LinearMap.ker (Matrix.toLin' A) := by
    ext x
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    constructor
    · intro h
      funext r
      rw [hMap]
      exact h (u r, σ (u r)) ((mem_sourceActivePairs I σ (u r) (σ (u r))).mpr
        ⟨I.orderEmbOfFin_mem rfl r, rfl⟩)
    · intro h p hp
      obtain ⟨hi, hs⟩ := (mem_sourceActivePairs I σ p.1 p.2).mp hp
      have hiRange : p.1 ∈ Set.range u := by
        rw [show Set.range u = (I : Set (Fin n)) from I.range_orderEmbOfFin rfl]
        exact hi
      obtain ⟨r, hr⟩ := hiRange
      have hh := congrFun h r
      rw [hMap] at hh
      simpa only [hr, ← hs, Prod.mk.eta, Pi.zero_apply] using hh
  have hRank : Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A)) = n - I.card :=
    (full_triangular_active_map_surjective_and_finrank_ker B δ hδ u u.strictMono σ).2
  change Module.finrank ℝ (affineSpan ℝ F).direction = _
  rw [direction_affineSpan, hSpan, hKer]
  exact hRank

end Grunbaum2003

end

-- Local ingredient: ProjectedDirectionRank

set_option autoImplicit false

namespace Grunbaum2003

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

                                                                         
                                                                            
theorem finrank_direction_affineSpan_image_of_kernel_injective
    (f : E →ᵃ[ℝ] F) (S : Set E)
    (hKer : ∀ z ∈ (affineSpan ℝ S).direction, f.linear z = 0 → z = 0) :
    Module.finrank ℝ (affineSpan ℝ (f '' S)).direction =
      Module.finrank ℝ (affineSpan ℝ S).direction := by
  let D := (affineSpan ℝ S).direction
  have hInj : Function.Injective (f.linear.domRestrict D) := by
    intro u v huv
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hKer ((u : E) - (v : E)) (D.sub_mem u.property v.property)
    rw [map_sub]
    exact sub_eq_zero.mpr huv
  have hRank := LinearMap.finrank_range_of_inj hInj
  rw [LinearMap.range_domRestrict] at hRank
  have hDirection : (affineSpan ℝ (f '' S)).direction = D.map f.linear := by
    simpa only [D, direction_affineSpan] using (f.map_vectorSpan (s := S)).symm
  rw [hDirection]
  exact hRank

end Grunbaum2003


-- Local ingredient: ProjectionFaceCarrier

set_option autoImplicit false

namespace Grunbaum2003

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

                                                                      
                                                         
theorem exposedFaces_orderIso_projection_on_direction
    (π : E →L[ℝ] F) (S : Set E) (hSne : S.Nonempty)
    (hKer : ∀ z ∈ (affineSpan ℝ S).direction, π z = 0 → z = 0) :
    Nonempty ({T : Set E // IsExposed ℝ S T} ≃o
      {T : Set F // IsExposed ℝ (π '' S) T}) := by
  obtain ⟨x₀, hx₀⟩ := hSne
  apply exposedFaces_orderIso_projection_on_submodule π S x₀
    (affineSpan ℝ S).direction ?_ hKer
  intro x hx
  exact AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hx) (mem_affineSpan ℝ hx₀)

end Grunbaum2003


-- Local ingredient: ProjectedCubeFaces

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

                                                                           
                                                                          
                                                                          
                                                       
theorem projected_triangular_cube_face_model {n d : ℕ}
    (B : Fin n → Fin n → ℝ) (δ : ℝ) (hδ : δ ≠ 0) (b : Fin n → ℝ)
    (P : Set (Fin n → ℝ)) (hD : IsDPolytope P)
    (hP : P = {x : Fin n → ℝ | ∀ i,
      |δ * x i| ≤ b i - ∑ j : Fin n, if j < i then B i j * x j else 0})
    (e : ExposedFaceBijection P {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1})
    (hCoordinates : ∀ x ∈ P, ∀ i,
      0 < b i - (∑ j : Fin n, if j < i then B i j * x j else 0) ∧
      e.toFun x i = δ * x i / (b i - ∑ j : Fin n, if j < i then B i j * x j else 0))
    (π : (Fin n → ℝ) →L[ℝ] (Fin d → ℝ))
    (S : Set (Fin n → ℝ)) (hS : IsExposed ℝ P S) (hSne : S.Nonempty)
    (hKer : ∀ z ∈ (affineSpan ℝ S).direction, π z = 0 → z = 0) :
    ∃ I : Finset (Fin n), ∃ σ : Fin n → Bool,
      S = {x | x ∈ P ∧ ∀ i ∈ I,
        (∑ j : Fin n, if j < i then B i j * x j else 0) +
          (if σ i then δ else -δ) * x i = b i} ∧
      Module.finrank ℝ (affineSpan ℝ (π '' S)).direction = n - I.card ∧
      Nonempty (PolytopeFace (π '' S) ≃o PolytopeFace (standardCube (n - I.card))) := by
  obtain ⟨I, σ, hSSet, ⟨eCube⟩⟩ :=
    triangular_cube_all_face_models B δ b P hD e hCoordinates S hS hSne
  have hSourceDim : Module.finrank ℝ (affineSpan ℝ S).direction = n - I.card := by
    rw [hSSet]
    exact triangular_source_coordinate_face_finrank B δ hδ b P hP e hCoordinates I σ
  have hImageDim : Module.finrank ℝ (affineSpan ℝ (π '' S)).direction = n - I.card := by
    calc
      _ = Module.finrank ℝ (affineSpan ℝ S).direction :=
        finrank_direction_affineSpan_image_of_kernel_injective
          π.toLinearMap.toAffineMap S hKer
      _ = n - I.card := hSourceDim
  obtain ⟨eProjection⟩ := exposedFaces_orderIso_projection_on_direction π S hSne hKer
  exact ⟨I, σ, hSSet, hImageDim, ⟨eProjection.symm.trans eCube⟩⟩

end Grunbaum2003


-- Local ingredient: ProjectionPolytopes

set_option autoImplicit false

namespace Grunbaum2003

                                                                         
                                                                      
theorem isDPolytope_image_surjective_affineMap {n d : ℕ}
    (f : (Fin n → ℝ) →ᵃ[ℝ] (Fin d → ℝ)) (hf : Function.Surjective f)
    (P : Set (Fin n → ℝ)) (hP : IsDPolytope P) : IsDPolytope (f '' P) := by
  obtain ⟨⟨V, hV, hVne, hHull⟩, hSpan⟩ := hP
  constructor
  · refine ⟨f '' V, hV.image f, hVne.image f, ?_⟩
    rw [hHull]
    exact f.image_convexHull V
  · exact f.span_eq_top_of_surjective hf hSpan

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

                                                                           
                                                                               
theorem isExposed_source_face_of_projection
    (π : E →L[ℝ] F) (P : Set E) (G : Set F)
    (hG : IsExposed ℝ (π '' P) G) :
    IsExposed ℝ P {x | x ∈ P ∧ π x ∈ G} := by
  intro hNe
  obtain ⟨x₀, hxP, hxG⟩ := hNe
  obtain ⟨L, hL⟩ := hG ⟨π x₀, hxG⟩
  refine ⟨L.comp π, ?_⟩
  ext x
  constructor
  · rintro ⟨hxP, hxG⟩
    rw [hL] at hxG
    exact ⟨hxP, fun y hy => hxG.2 (π y) ⟨y, hy, rfl⟩⟩
  · rintro ⟨hxP, hMax⟩
    refine ⟨hxP, ?_⟩
    rw [hL]
    refine ⟨⟨x, hxP, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hMax y hy

theorem projection_image_source_face
    (π : E →L[ℝ] F) (P : Set E) (G : Set F)
    (hG : IsExposed ℝ (π '' P) G) :
    π '' {x | x ∈ P ∧ π x ∈ G} = G := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hG.subset hy
    exact ⟨x, ⟨hx, hy⟩, rfl⟩

end Grunbaum2003


-- Local ingredient: ProjectionTheory

                                               
set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

                                                                           
                                                                          
                                                                                
theorem active_card_gt_of_proper_projected_face {m d : ℕ}
    (B : Matrix (Fin (m + d)) (Fin m) ℝ) (δ : ℝ)
    (hGeneric : ∀ u : Fin m → Fin (m + d), StrictMono u →
      ∀ τ : Fin (m + d) → Bool,
        Matrix.det (fun i j : Fin m =>
          if j.val < (u i).val then B (u i) j else if j.val = (u i).val then
            (if τ (u i) then δ else -δ) else 0) ≠ 0)
    (C : Fin (m + d) → Fin (m + d) → ℝ)
    (hC : C = fun r j => if h : j.val < m then B r ⟨j.val, h⟩ else 0)
    (b : Fin (m + d) → ℝ) (P : Set (Fin (m + d) → ℝ))
    (hP : P = {x | ∀ i, |δ * x i| ≤ b i -
      ∑ j : Fin (m + d), if j < i then C i j * x j else 0})
    (e : ExposedFaceBijection P
      {x : Fin (m + d) → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1})
    (hCoordinates : ∀ x ∈ P, ∀ i,
      0 < b i - (∑ j : Fin (m + d), if j < i then C i j * x j else 0) ∧
      e.toFun x i = δ * x i / (b i - ∑ j : Fin (m + d), if j < i then C i j * x j else 0))
    (I : Finset (Fin (m + d))) (σ : Fin (m + d) → Bool)
    (G : Set (Fin d → ℝ))
    (hG : IsExposed ℝ (retainedCoordinateProjection m d '' P) G)
    (hProper : G ≠ retainedCoordinateProjection m d '' P)
    (hContain : retainedCoordinateProjection m d ''
      {x | x ∈ P ∧ ∀ i ∈ I,
        (∑ j : Fin (m + d), if j < i then C i j * x j else 0) +
          (if σ i then δ else -δ) * x i = b i} ⊆ G) :
    m < I.card := by
  classical
  by_contra hNot
  have hI : I.card ≤ m := Nat.le_of_not_gt hNot
  obtain ⟨v, hvKernel, hvRelease⟩ :=
    exists_actual_discarded_release_direction B δ hGeneric I hI σ
  obtain ⟨x₀, hxP, hActive, hStrict⟩ :=
    triangular_cube_halfspace_strict_anchor C δ b P e hCoordinates I σ
  let a : (Fin (m + d) × Bool) → (Fin (m + d) → ℝ) →ₗ[ℝ] ℝ :=
    fun p => triangularSignedNormal C δ p.1 p.2
  let β : Fin (m + d) × Bool → ℝ := fun p => b p.1
  let J := I.image (fun i => (i, σ i))
  have hPall : P = {x | ∀ p, a p x ≤ β p} :=
    hP.trans (triangular_absolute_constraints_eq_halfspaces C δ b)
  have hJA : ∀ p ∈ J, a p x₀ = β p := by
    rintro ⟨i, s⟩ hp
    obtain ⟨hi, hs⟩ := (mem_triangular_active_pairs I σ i s).mp hp
    simpa only [a, β, hs] using hActive i hi
  have hJS : ∀ p, p ∉ J → a p x₀ < β p := hStrict
  have hJR : ∀ p ∈ J, a p v < 0 := by
    rintro ⟨i, s⟩ hp
    obtain ⟨hi, hs⟩ := (mem_triangular_active_pairs I σ i s).mp hp
    change triangularSignedNormal C δ i s v < 0
    rw [hs, triangularSignedNormal_apply, hC]
    rw [hvRelease i hi]
    norm_num
  have hxG : retainedCoordinateProjection m d x₀ ∈ G := by
    apply hContain
    refine ⟨x₀, ⟨hxP, ?_⟩, rfl⟩
    intro i hi
    simpa only [triangularSignedNormal_apply] using hActive i hi
  apply hProper
  exact exposed_image_face_eq_full_of_releasing_kernel_direction a β P hPall
    (retainedCoordinateProjection m d) (retainedCoordinateProjection_surjective m d)
    G hG J x₀ v hJA hJS hvKernel hJR hxG

                                                                         
                                                                          
                                                                            
theorem actual_triangular_face_direction_kernel_eq_zero {m d : ℕ}
    (B : Matrix (Fin (m + d)) (Fin m) ℝ) (δ : ℝ)
    (hGeneric : ∀ u : Fin m → Fin (m + d), StrictMono u →
      ∀ τ : Fin (m + d) → Bool,
        Matrix.det (fun i j : Fin m =>
          if j.val < (u i).val then B (u i) j else if j.val = (u i).val then
            (if τ (u i) then δ else -δ) else 0) ≠ 0)
    (C : Fin (m + d) → Fin (m + d) → ℝ)
    (hC : C = fun r j => if h : j.val < m then B r ⟨j.val, h⟩ else 0)
    (b : Fin (m + d) → ℝ) (P : Set (Fin (m + d) → ℝ))
    (I : Finset (Fin (m + d))) (hI : m ≤ I.card) (σ : Fin (m + d) → Bool)
    (z : Fin (m + d) → ℝ)
    (hz : z ∈ (affineSpan ℝ {x | x ∈ P ∧ ∀ i ∈ I,
      (∑ j : Fin (m + d), if j < i then C i j * x j else 0) +
        (if σ i then δ else -δ) * x i = b i}).direction)
    (hProj : retainedCoordinateProjection m d z = 0) : z = 0 := by
  apply actual_projection_active_kernel_eq_zero B δ hGeneric I hI σ z hProj
  dsimp only
  intro i hi
  have h := triangularSignedNormal_direction_zero C δ b P I σ z hz i hi
  rw [triangularSignedNormal_apply, hC] at h
  exact h

end Grunbaum2003



                                           
set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

section

variable {m d : ℕ}
variable (B : Matrix (Fin (m + d)) (Fin m) ℝ) (δ : ℝ) (hδ : δ ≠ 0)
variable (hGeneric : ∀ u : Fin m → Fin (m + d), StrictMono u →
  ∀ τ : Fin (m + d) → Bool,
    Matrix.det (fun i j : Fin m =>
      if j.val < (u i).val then B (u i) j else if j.val = (u i).val then
        (if τ (u i) then δ else -δ) else 0) ≠ 0)
variable (C : Fin (m + d) → Fin (m + d) → ℝ)
variable (hC : C = fun r j => if h : j.val < m then B r ⟨j.val, h⟩ else 0)
variable (b : Fin (m + d) → ℝ) (P : Set (Fin (m + d) → ℝ))
variable (hP : P = {x | ∀ i, |δ * x i| ≤ b i -
  ∑ j : Fin (m + d), if j < i then C i j * x j else 0})
variable (hD : IsDPolytope P)
variable (e : ExposedFaceBijection P
  {x : Fin (m + d) → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1})
variable (hCoordinates : ∀ x ∈ P, ∀ i,
  0 < b i - (∑ j : Fin (m + d), if j < i then C i j * x j else 0) ∧
  e.toFun x i = δ * x i / (b i - ∑ j : Fin (m + d), if j < i then C i j * x j else 0))

include B δ hδ hGeneric C hC b P hP hD e hCoordinates

                                                                        
                                             
theorem proper_projected_source_face_kernel
    (G : Set (Fin d → ℝ))
    (hG : IsExposed ℝ (retainedCoordinateProjection m d '' P) G)
    (hGne : G.Nonempty) (hProper : G ≠ retainedCoordinateProjection m d '' P) :
    ∀ z ∈ (affineSpan ℝ {x | x ∈ P ∧ retainedCoordinateProjection m d x ∈ G}).direction,
      retainedCoordinateProjection m d z = 0 → z = 0 := by
  let π := retainedCoordinateProjection m d
  let S : Set (Fin (m + d) → ℝ) := {x | x ∈ P ∧ π x ∈ G}
  have hS : IsExposed ℝ P S := isExposed_source_face_of_projection π P G hG
  have hSne : S.Nonempty := by
    obtain ⟨y, hy⟩ := hGne
    obtain ⟨x, hx, rfl⟩ := hG.subset hy
    exact ⟨x, hx, hy⟩
  have hImage : π '' S = G := projection_image_source_face π P G hG
  obtain ⟨I, σ, hSSet⟩ :=
    triangular_cube_face_classification C δ b P e hCoordinates S hS hSne
  have hContain : π '' {x | x ∈ P ∧ ∀ i ∈ I,
      (∑ j : Fin (m + d), if j < i then C i j * x j else 0) +
        (if σ i then δ else -δ) * x i = b i} ⊆ G := by
    rw [← hSSet, hImage]
  have hI : m < I.card := active_card_gt_of_proper_projected_face
    B δ hGeneric C hC b P hP e hCoordinates I σ G hG hProper hContain
  intro z hz hProj
  apply actual_triangular_face_direction_kernel_eq_zero
    B δ hGeneric C hC b P I hI.le σ z ?_ hProj
  rwa [← hSSet]

                                                                        
                                                                        
                                                   
theorem proper_projected_cube_face_model
    (G : Set (Fin d → ℝ))
    (hG : IsExposed ℝ (retainedCoordinateProjection m d '' P) G)
    (hGne : G.Nonempty) (hProper : G ≠ retainedCoordinateProjection m d '' P) :
    ∃ k : ℕ, Module.finrank ℝ (affineSpan ℝ G).direction = k ∧
      Nonempty (PolytopeFace G ≃o PolytopeFace (standardCube k)) := by
  let π := retainedCoordinateProjection m d
  let S : Set (Fin (m + d) → ℝ) := {x | x ∈ P ∧ π x ∈ G}
  have hS : IsExposed ℝ P S := isExposed_source_face_of_projection π P G hG
  have hSne : S.Nonempty := by
    obtain ⟨y, hy⟩ := hGne
    obtain ⟨x, hx, rfl⟩ := hG.subset hy
    exact ⟨x, hx, hy⟩
  have hImage : π '' S = G := projection_image_source_face π P G hG
  have hKer := proper_projected_source_face_kernel
    B δ hδ hGeneric C hC b P hP hD e hCoordinates G hG hGne hProper
  obtain ⟨J, τ, _, hRank, hModel⟩ := projected_triangular_cube_face_model
    C δ hδ b P hD hP e hCoordinates π S hS hSne hKer
  rw [hImage] at hRank hModel
  exact ⟨m + d - J.card, hRank, hModel⟩

theorem proper_projected_source_face_finrank
    (G : Set (Fin d → ℝ))
    (hG : IsExposed ℝ (retainedCoordinateProjection m d '' P) G)
    (hGne : G.Nonempty) (hProper : G ≠ retainedCoordinateProjection m d '' P) :
    Module.finrank ℝ (affineSpan ℝ
      {x | x ∈ P ∧ retainedCoordinateProjection m d x ∈ G}).direction =
      Module.finrank ℝ (affineSpan ℝ G).direction := by
  let π := retainedCoordinateProjection m d
  let S : Set (Fin (m + d) → ℝ) := {x | x ∈ P ∧ π x ∈ G}
  have hKer := proper_projected_source_face_kernel
    B δ hδ hGeneric C hC b P hP hD e hCoordinates G hG hGne hProper
  have hRank := finrank_direction_affineSpan_image_of_kernel_injective
    π.toLinearMap.toAffineMap S hKer
  change Module.finrank ℝ (affineSpan ℝ (π '' S)).direction =
    Module.finrank ℝ (affineSpan ℝ S).direction at hRank
  have hImage : π '' S = G := projection_image_source_face π P G hG
  rw [hImage] at hRank
  exact hRank.symm

                                                                           
                                                                     
theorem small_projected_face_source_preimage_small
    (r : ℕ) (hr : r < d) (G : Set (Fin d → ℝ))
    (hG : IsExposed ℝ (retainedCoordinateProjection m d '' P) G)
    (hSmall : G = ∅ ∨ Module.finrank ℝ (affineSpan ℝ G).direction ≤ r) :
    {x | x ∈ P ∧ retainedCoordinateProjection m d x ∈ G} = ∅ ∨
      Module.finrank ℝ (affineSpan ℝ
        {x | x ∈ P ∧ retainedCoordinateProjection m d x ∈ G}).direction ≤ r := by
  by_cases hEmpty : G = ∅
  · left
    ext x
    simp only [hEmpty, Set.mem_ofPred_eq, Set.mem_empty_iff_false, and_false]
  · have hGne : G.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
    have hLe : Module.finrank ℝ (affineSpan ℝ G).direction ≤ r :=
      hSmall.resolve_left hEmpty
    have hImageD : IsDPolytope (retainedCoordinateProjection m d '' P) :=
      isDPolytope_image_surjective_affineMap
        (retainedCoordinateProjection m d).toLinearMap.toAffineMap
        (retainedCoordinateProjection_surjective m d) P hD
    have hProper : G ≠ retainedCoordinateProjection m d '' P := by
      intro hFull
      have hDim : Module.finrank ℝ (affineSpan ℝ G).direction = d := by
        rw [hFull, hImageD.2, AffineSubspace.direction_top]
        simp only [finrank_top, Module.finrank_fin_fun]
      omega
    right
    rw [proper_projected_source_face_finrank
      B δ hδ hGeneric C hC b P hP hD e hCoordinates G hG hGne hProper]
    exact hLe

                                                                       
                                                                          
                                                                         
theorem isCubicalDPolytope_triangular_projection :
    IsCubicalDPolytope (retainedCoordinateProjection m d '' P) := by
  let π := retainedCoordinateProjection m d
  have hImageD : IsDPolytope (π '' P) :=
    isDPolytope_image_surjective_affineMap π.toLinearMap.toAffineMap
      (retainedCoordinateProjection_surjective m d) P hD
  refine ⟨hImageD, ?_⟩
  intro G hGne hG hFacet
  have hProper : G ≠ π '' P := by
    intro hFull
    have hDim : Module.finrank ℝ (affineSpan ℝ G).direction = d := by
      rw [hFull, hImageD.2, AffineSubspace.direction_top]
      simp only [finrank_top, Module.finrank_fin_fun]
    omega
  obtain ⟨k, hDim, ⟨eCube⟩⟩ := proper_projected_cube_face_model
    B δ hδ hGeneric C hC b P hP hD e hCoordinates G hG hGne hProper
  have hk : k = d - 1 := by omega
  rw [hk] at eCube
  exact ⟨eCube⟩

end
end Grunbaum2003


-- Local ingredient: ProjectionFaces

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

                                                                             
                                                                            
theorem dual_factors_through_projection {n d : ℕ}
    (π : (Fin n → ℝ) →L[ℝ] (Fin d → ℝ)) (hπ : Function.Surjective π)
    (L : StrongDual ℝ (Fin n → ℝ))
    (hKer : ∀ z, π z = 0 → L z = 0) :
    ∃ c : StrongDual ℝ (Fin d → ℝ), ∀ x, c (π x) = L x := by
  classical
  obtain ⟨g, hg⟩ := π.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hπ)
  have hgπ (y : Fin d → ℝ) : π (g y) = y := LinearMap.congr_fun hg y
  let c : StrongDual ℝ (Fin d → ℝ) := (L.toLinearMap.comp g).toContinuousLinearMap
  refine ⟨c, ?_⟩
  intro x
  change L (g (π x)) = L x
  have hz : π (x - g (π x)) = 0 := by rw [map_sub, hgπ, sub_self]
  have hL := hKer (x - g (π x)) hz
  rw [map_sub, sub_eq_zero] at hL
  exact hL.symm

                                                                            
                                                                           
                                                                        
                                                                            
theorem active_face_projects_of_positive_sum {n d : ℕ} {ι : Type*}
    (P : Set (Fin n → ℝ))
    (π : (Fin n → ℝ) →L[ℝ] (Fin d → ℝ))
    (I : Finset ι) (a : ι → StrongDual ℝ (Fin n → ℝ)) (b weight : ι → ℝ)
    (hWeight : ∀ i ∈ I, 0 < weight i)
    (hBound : ∀ i ∈ I, ∀ x ∈ P, a i x ≤ b i)
    (c : StrongDual ℝ (Fin d → ℝ))
    (hFactor : ∀ x, ∑ i ∈ I, weight i * a i x = c (π x)) :
    let F := {x | x ∈ P ∧ ∀ i ∈ I, a i x = b i}
    IsExposed ℝ P F ∧ IsExposed ℝ (π '' P) (π '' F) ∧
      ∀ x ∈ P, π x ∈ π '' F ↔ x ∈ F := by
  classical
  let F := {x | x ∈ P ∧ ∀ i ∈ I, a i x = b i}
  let β := ∑ i ∈ I, weight i * b i
  have hGap (x : Fin n → ℝ) :
      (∑ i ∈ I, weight i * (b i - a i x)) = β - c (π x) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hFactor x]
  have hNonneg (x : Fin n → ℝ) (hx : x ∈ P) (i : ι) (hi : i ∈ I) :
      0 ≤ weight i * (b i - a i x) := mul_nonneg (hWeight i hi).le (sub_nonneg.mpr (hBound i hi x hx))
  have hLe (x : Fin n → ℝ) (hx : x ∈ P) : c (π x) ≤ β := by
    apply sub_nonneg.mp
    rw [← hGap x]
    exact Finset.sum_nonneg (hNonneg x hx)
  have hEq (x : Fin n → ℝ) (hx : x ∈ P) : c (π x) = β ↔ x ∈ F := by
    constructor
    · intro heq
      refine ⟨hx, ?_⟩
      have hZero : (∑ i ∈ I, weight i * (b i - a i x)) = 0 := by rw [hGap x, heq, sub_self]
      have hEach := (Finset.sum_eq_zero_iff_of_nonneg (hNonneg x hx)).mp hZero
      intro i hi
      have hDiff : b i - a i x = 0 := (mul_eq_zero.mp (hEach i hi)).resolve_left (hWeight i hi).ne'
      exact (sub_eq_zero.mp hDiff).symm
    · intro hxF
      rw [← hFactor x]
      exact Finset.sum_congr rfl (fun i hi => congrArg (fun z : ℝ => weight i * z) (hxF.2 i hi))
  have hSource : IsExposed ℝ P F := by
    intro hF
    obtain ⟨x₀, hx₀⟩ := hF
    refine ⟨c.comp π, ?_⟩
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro y hy
      change c (π y) ≤ c (π x)
      rw [(hEq x hx.1).mpr hx]
      exact hLe y hy
    · rintro ⟨hx, hmax⟩
      apply (hEq x hx).mp
      apply le_antisymm (hLe x hx)
      have h := hmax x₀ hx₀.1
      change c (π x₀) ≤ c (π x) at h
      rw [(hEq x₀ hx₀.1).mpr hx₀] at h
      exact h
  refine ⟨hSource, ?_, ?_⟩
  · intro hImage
    obtain ⟨_, ⟨x₀, hx₀, rfl⟩⟩ := hImage
    refine ⟨c, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      rw [(hEq x hx.1).mpr hx]
      exact hLe z hz
    · rintro ⟨⟨x, hx, hxy⟩, hmax⟩
      refine ⟨x, (hEq x hx).mp ?_, hxy⟩
      apply le_antisymm (hLe x hx)
      have h := hmax (π x₀) ⟨x₀, hx₀.1, rfl⟩
      rw [(hEq x₀ hx₀.1).mpr hx₀] at h
      rwa [hxy]
  · intro x hx
    constructor
    · rintro ⟨z, hz, hzx⟩
      apply (hEq x hx).mp
      rw [← hzx]
      exact (hEq z hz.1).mpr hz
    · intro hxF
      exact ⟨x, hxF, rfl⟩

                                                                       
                                                  
theorem projection_injOn_active_face {n d : ℕ} {ι : Type*}
    (P : Set (Fin n → ℝ))
    (π : (Fin n → ℝ) →L[ℝ] (Fin d → ℝ))
    (I : Finset ι) (a : ι → StrongDual ℝ (Fin n → ℝ)) (b : ι → ℝ)
    (hRank : ∀ z, π z = 0 → (∀ i ∈ I, a i z = 0) → z = 0) :
    Set.InjOn π {x | x ∈ P ∧ ∀ i ∈ I, a i x = b i} := by
  intro x hx y hy hxy
  apply sub_eq_zero.mp
  apply hRank (x - y)
  · rw [map_sub, hxy, sub_self]
  · intro i hi
    rw [map_sub, hx.2 i hi, hy.2 i hi, sub_self]

end Grunbaum2003


-- Local ingredient: PositiveFaceProjection

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

private noncomputable def positiveSourceDual {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) (σ : Fin n → Bool) (i : Fin n) :
    StrongDual ℝ (Fin n → ℝ) :=
  ∑ j : Fin n,
    (if j.val < i.val then C i j else if j.val = i.val then
      (if σ i then δ else -δ) else 0) • ContinuousLinearMap.proj j

private theorem positiveSourceDual_apply {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) (σ : Fin n → Bool)
    (i : Fin n) (x : Fin n → ℝ) :
    positiveSourceDual C δ σ i x =
      (∑ j : Fin n, if j < i then C i j * x j else 0) +
        (if σ i then δ else -δ) * x i := by
  rw [← full_triangular_dot_eq_source_normal C δ σ i x]
  simp only [positiveSourceDual, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

                                                                           
                                                                     
                                                                          
                                                                           
                                                               
theorem actual_face_projects_of_positive_discarded_sum {m d : ℕ}
    (B : Matrix (Fin (m + d)) (Fin m) ℝ) (δ : ℝ)
    (b : Fin (m + d) → ℝ) (J : Finset (Fin (m + d)))
    (σ : Fin (m + d) → Bool)
    (weight : {i : Fin (m + d) // i ∉ J} → ℝ)
    (hWeight : ∀ i, 0 < weight i)
    (hRows :
      (∑ i : {i : Fin (m + d) // i ∉ J}, weight i •
        (fun j : Fin m => if j.val < i.val.val then B i.val j
          else if j.val = i.val.val then (if σ i.val then δ else -δ) else 0)) = 0) :
    let fullB : Matrix (Fin (m + d)) (Fin (m + d)) ℝ :=
      fun r j => if h : j.val < m then B r ⟨j.val, h⟩ else 0
    let P := {x : Fin (m + d) → ℝ | ∀ i,
      |δ * x i| ≤ b i - ∑ j : Fin (m + d), if j < i then fullB i j * x j else 0}
    let F := {x | x ∈ P ∧ ∀ i, i ∉ J →
      (∑ j : Fin (m + d), if j < i then fullB i j * x j else 0) +
        (if σ i then δ else -δ) * x i = b i}
    IsExposed ℝ P F ∧
      IsExposed ℝ (retainedCoordinateProjection m d '' P)
        (retainedCoordinateProjection m d '' F) ∧
      ∀ x ∈ P, retainedCoordinateProjection m d x ∈
        retainedCoordinateProjection m d '' F ↔ x ∈ F := by
  classical
  let C : Matrix (Fin (m + d)) (Fin (m + d)) ℝ :=
    fun r j => if h : j.val < m then B r ⟨j.val, h⟩ else 0
  let P := {x : Fin (m + d) → ℝ | ∀ i,
    |δ * x i| ≤ b i - ∑ j : Fin (m + d), if j < i then C i j * x j else 0}
  let F := {x | x ∈ P ∧ ∀ i, i ∉ J →
    (∑ j : Fin (m + d), if j < i then C i j * x j else 0) +
      (if σ i then δ else -δ) * x i = b i}
  change IsExposed ℝ P F ∧
    IsExposed ℝ (retainedCoordinateProjection m d '' P)
      (retainedCoordinateProjection m d '' F) ∧
    ∀ x ∈ P, retainedCoordinateProjection m d x ∈
      retainedCoordinateProjection m d '' F ↔ x ∈ F
  let R : Matrix (Fin (m + d)) (Fin m) ℝ := fun i j =>
    if j.val < i.val then B i j else if j.val = i.val then
      (if σ i then δ else -δ) else 0
  let a : {i : Fin (m + d) // i ∉ J} → StrongDual ℝ (Fin (m + d) → ℝ) :=
    fun i => positiveSourceDual C δ σ i.val
  let L : StrongDual ℝ (Fin (m + d) → ℝ) :=
    ∑ i : {i : Fin (m + d) // i ∉ J}, weight i • a i
  have hL (x : Fin (m + d) → ℝ) :
      L x = ∑ i : {i : Fin (m + d) // i ∉ J}, weight i * a i x := by
    simp only [L, sum_apply, smul_apply, smul_eq_mul]
  have haEmbed (i : {i : Fin (m + d) // i ∉ J}) (z : Fin m → ℝ) :
      a i (discardedCoordinateEmbed m d z) = ∑ j : Fin m, R i.val j * z j := by
    rw [positiveSourceDual_apply]
    exact actual_signed_normal_on_discarded_embed B δ σ i.val z
  have hCoord (j : Fin m) :
      (∑ i : {i : Fin (m + d) // i ∉ J}, weight i * R i.val j) = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      using congrFun hRows j
  have hKer (v : Fin (m + d) → ℝ)
      (hv : retainedCoordinateProjection m d v = 0) : L v = 0 := by
    obtain ⟨z, hz⟩ := (retainedCoordinateProjection_eq_zero_iff m d v).mp hv
    calc
      L v = ∑ i : {i : Fin (m + d) // i ∉ J},
          weight i * a i (discardedCoordinateEmbed m d z) := by rw [← hz, hL]
      _ = ∑ i : {i : Fin (m + d) // i ∉ J},
          weight i * ∑ j : Fin m, R i.val j * z j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [haEmbed]
      _ = ∑ j : Fin m,
          (∑ i : {i : Fin (m + d) // i ∉ J}, weight i * R i.val j) * z j := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        exact (mul_assoc (weight i) (R i.val j) (z j)).symm
      _ = 0 := by simp only [hCoord, zero_mul, Finset.sum_const_zero]
  obtain ⟨c, hc⟩ := dual_factors_through_projection (retainedCoordinateProjection m d)
    (retainedCoordinateProjection_surjective m d) L hKer
  have hBound : ∀ i : {i : Fin (m + d) // i ∉ J},
      ∀ x ∈ P, a i x ≤ b i.val := by
    intro i x hx
    have hAbs := abs_le.mp (hx i.val)
    rw [positiveSourceDual_apply]
    cases σ i.val <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_mul] <;>
      linarith [hAbs.1, hAbs.2]
  have hFactor (x : Fin (m + d) → ℝ) :
      (∑ i ∈ (Finset.univ : Finset {i : Fin (m + d) // i ∉ J}),
        weight i * a i x) = c (retainedCoordinateProjection m d x) := by
    exact (hL x).symm.trans (hc x).symm
  have hPres := active_face_projects_of_positive_sum P (retainedCoordinateProjection m d)
    Finset.univ a (fun i => b i.val) weight (fun i _ => hWeight i)
    (fun i _ => hBound i) c hFactor
  have hF : {x | x ∈ P ∧ ∀ i ∈ (Finset.univ : Finset {i : Fin (m + d) // i ∉ J}),
      a i x = b i.val} = F := by
    ext x
    constructor
    · rintro ⟨hx, hEq⟩
      refine ⟨hx, ?_⟩
      intro i hi
      exact (positiveSourceDual_apply C δ σ i x).symm.trans
        (hEq ⟨i, hi⟩ (Finset.mem_univ _))
    · rintro ⟨hx, hEq⟩
      refine ⟨hx, ?_⟩
      intro i _
      exact (positiveSourceDual_apply C δ σ i.val x).trans (hEq i.val i.property)
  simpa only [hF] using hPres

end Grunbaum2003


-- Local ingredient: LowSkeletonProjection

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

                                                                        
                                                                          
                                                                          
theorem small_source_faces_strictly_project {m d : ℕ}
    (B : Matrix (Fin (m + d)) (Fin m) ℝ) (δ : ℝ) (hδ : δ ≠ 0)
    (r : ℕ) (hr : r < d)
    (hPositive : ∀ J : Finset (Fin (m + d)), J.card ≤ r →
      ∀ σ : Fin (m + d) → Bool,
        ∃ weight : {i : Fin (m + d) // i ∉ J} → ℝ,
          (∀ i, 0 < weight i) ∧
          (∑ i : {i : Fin (m + d) // i ∉ J}, weight i •
            (fun j : Fin m => if j.val < i.val.val then B i.val j
              else if j.val = i.val.val then (if σ i.val then δ else -δ) else 0)) = 0)
    (hGeneric : ∀ u : Fin m → Fin (m + d), StrictMono u →
      ∀ τ : Fin (m + d) → Bool,
        Matrix.det (fun i j : Fin m =>
          if j.val < (u i).val then B (u i) j else if j.val = (u i).val then
            (if τ (u i) then δ else -δ) else 0) ≠ 0)
    (C : Fin (m + d) → Fin (m + d) → ℝ)
    (hC : C = fun a j => if h : j.val < m then B a ⟨j.val, h⟩ else 0)
    (b : Fin (m + d) → ℝ) (P : Set (Fin (m + d) → ℝ))
    (hP : P = {x | ∀ i, |δ * x i| ≤ b i -
      ∑ j : Fin (m + d), if j < i then C i j * x j else 0})
    (e : ExposedFaceBijection P
      {x : Fin (m + d) → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1})
    (hCoordinates : ∀ x ∈ P, ∀ i,
      0 < b i - (∑ j : Fin (m + d), if j < i then C i j * x j else 0) ∧
      e.toFun x i = δ * x i / (b i - ∑ j : Fin (m + d), if j < i then C i j * x j else 0))
    (S : Set (Fin (m + d) → ℝ)) (hS : IsExposed ℝ P S)
    (hSmall : S = ∅ ∨ Module.finrank ℝ (affineSpan ℝ S).direction ≤ r) :
    IsExposed ℝ (retainedCoordinateProjection m d '' P)
      (retainedCoordinateProjection m d '' S) ∧
    Module.finrank ℝ (affineSpan ℝ (retainedCoordinateProjection m d '' S)).direction =
      Module.finrank ℝ (affineSpan ℝ S).direction ∧
    ∀ x ∈ P, retainedCoordinateProjection m d x ∈
      retainedCoordinateProjection m d '' S ↔ x ∈ S := by
  classical
  by_cases hEmpty : S = ∅
  · subst S
    refine ⟨?_, ?_, ?_⟩
    · rw [Set.image_empty]
      exact isExposed_empty
    · rw [Set.image_empty, direction_affineSpan, direction_affineSpan,
        vectorSpan_empty, vectorSpan_empty, finrank_bot, finrank_bot]
    · simp
  · have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
    have hLe : Module.finrank ℝ (affineSpan ℝ S).direction ≤ r :=
      hSmall.resolve_left hEmpty
    subst C
    subst P
    let C : Fin (m + d) → Fin (m + d) → ℝ :=
      fun a j => if h : j.val < m then B a ⟨j.val, h⟩ else 0
    let P : Set (Fin (m + d) → ℝ) := {x | ∀ i, |δ * x i| ≤ b i -
      ∑ j : Fin (m + d), if j < i then C i j * x j else 0}
    let π := retainedCoordinateProjection m d
    obtain ⟨I, σ, hSSet⟩ := triangular_cube_face_classification
      C δ b P e hCoordinates S hS hSne
    have hSourceDim : Module.finrank ℝ (affineSpan ℝ S).direction = m + d - I.card := by
      rw [hSSet]
      exact triangular_source_coordinate_face_finrank C δ hδ b P rfl e hCoordinates I σ
    let J := Iᶜ
    have hJCard : J.card = m + d - I.card := by
      simp only [J, Finset.card_compl, Fintype.card_fin]
    have hJSmall : J.card ≤ r := by rw [hJCard, ← hSourceDim]; exact hLe
    obtain ⟨weight, hWeight, hRows⟩ := hPositive J hJSmall σ
    have hPres := actual_face_projects_of_positive_discarded_sum B δ b J σ weight hWeight hRows
    let F : Set (Fin (m + d) → ℝ) := {x | x ∈ P ∧ ∀ i, i ∉ J →
        (∑ j : Fin (m + d), if j < i then C i j * x j else 0) +
          (if σ i then δ else -δ) * x i = b i}
    have hPres0 : IsExposed ℝ P F ∧ IsExposed ℝ (π '' P) (π '' F) ∧
        ∀ x ∈ P, π x ∈ π '' F ↔ x ∈ F := hPres
    have hF : F = S := by
      change {x | x ∈ P ∧ ∀ i, i ∉ J →
        (∑ j : Fin (m + d), if j < i then C i j * x j else 0) +
          (if σ i then δ else -δ) * x i = b i} = S
      rw [hSSet]
      ext x
      simp only [J, Finset.mem_compl, not_not]
    have hPres' : IsExposed ℝ P S ∧ IsExposed ℝ (π '' P) (π '' S) ∧
        ∀ x ∈ P, π x ∈ π '' S ↔ x ∈ S := by
      simpa only [hF] using hPres0
    have hICard : I.card ≤ m + d := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ I)
    have hI : m ≤ I.card := by omega
    have hKer : ∀ z ∈ (affineSpan ℝ S).direction, π z = 0 → z = 0 := by
      intro z hz hProj
      apply actual_triangular_face_direction_kernel_eq_zero
        B δ hGeneric C rfl b P I hI σ z ?_ hProj
      rwa [← hSSet]
    have hRank := finrank_direction_affineSpan_image_of_kernel_injective
      π.toLinearMap.toAffineMap S hKer
    exact ⟨hPres'.2.1, hRank, hPres'.2.2⟩

end Grunbaum2003


-- Local ingredient: ProjectionSkeletonOrder

set_option autoImplicit false

namespace Grunbaum2003

                                                                         
                                                                             
                                                                             
theorem skeleton_orderIso_of_strict_face_projection {n d : ℕ}
    (P : Set (Fin n → ℝ)) (π : (Fin n → ℝ) →L[ℝ] (Fin d → ℝ)) (r : ℕ)
    (hForward : ∀ S : Set (Fin n → ℝ), IsExposed ℝ P S →
      (S = ∅ ∨ Module.finrank ℝ (affineSpan ℝ S).direction ≤ r) →
      IsExposed ℝ (π '' P) (π '' S) ∧
      Module.finrank ℝ (affineSpan ℝ (π '' S)).direction =
        Module.finrank ℝ (affineSpan ℝ S).direction ∧
      ∀ x ∈ P, π x ∈ π '' S ↔ x ∈ S)
    (hBack : ∀ G : Set (Fin d → ℝ), IsExposed ℝ (π '' P) G →
      (G = ∅ ∨ Module.finrank ℝ (affineSpan ℝ G).direction ≤ r) →
      {x | x ∈ P ∧ π x ∈ G} = ∅ ∨
        Module.finrank ℝ (affineSpan ℝ {x | x ∈ P ∧ π x ∈ G}).direction ≤ r) :
    Nonempty (SkeletonFace P r ≃o SkeletonFace (π '' P) r) := by
  have hReflect (S T : SkeletonFace P r)
      (h : π '' S.val.val ⊆ π '' T.val.val) : S.val.val ⊆ T.val.val := by
    intro x hx
    exact ((hForward T.val.val T.val.property T.property).2.2 x
      (S.val.property.subset hx)).mp (h ⟨x, hx, rfl⟩)
  let e : SkeletonFace P r ↪o SkeletonFace (π '' P) r := {
    toFun := fun S =>
      ⟨⟨π '' S.val.val, (hForward S.val.val S.val.property S.property).1⟩, by
        rcases S.property with hEmpty | hSmall
        · left
          change π '' S.val.val = ∅
          rw [hEmpty, Set.image_empty]
        · right
          change Module.finrank ℝ (affineSpan ℝ (π '' S.val.val)).direction ≤ r
          rw [(hForward S.val.val S.val.property S.property).2.1]
          exact hSmall⟩
    inj' := by
      intro S T h
      have hEq : π '' S.val.val = π '' T.val.val :=
        congrArg (fun A : SkeletonFace (π '' P) r => A.val.val) h
      apply Subtype.ext
      apply Subtype.ext
      exact Set.Subset.antisymm (hReflect S T hEq.le) (hReflect T S hEq.ge)
    map_rel_iff' := by
      intro S T
      change π '' S.val.val ⊆ π '' T.val.val ↔ S.val.val ⊆ T.val.val
      exact ⟨hReflect S T, Set.image_mono⟩ }
  have hSurj : Function.Surjective e := by
    intro G
    let S : Set (Fin n → ℝ) := {x | x ∈ P ∧ π x ∈ G.val.val}
    refine ⟨⟨⟨S, isExposed_source_face_of_projection π P G.val.val G.val.property⟩,
      hBack G.val.val G.val.property G.property⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact projection_image_source_face π P G.val.val G.val.property
  exact ⟨OrderIso.ofSurjective e hSurj⟩

end Grunbaum2003


-- Local ingredient: SkeletonTransport

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003.RankSkeletonTransport

private theorem sign_endpoint_iff (s : Bool) (t : ℝ) :
    (if s then (1 : ℝ) else -1) * t = 1 ↔ t = if s then 1 else -1 := by
  cases s with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
      constructor <;> intro h <;> linarith only [h]
  | true => simp only [↓reduceIte, one_mul]

                                                                       
                                                           
theorem centered_coordinate_face_finrank {n : ℕ} (I : Finset (Fin n)) (σ : Fin n → Bool) :
    Module.finrank ℝ (affineSpan ℝ {x : Fin n → ℝ |
      (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧ ∀ i ∈ I, x i = if σ i then 1 else -1}).direction =
      n - I.card := by
  let P : Set (Fin n → ℝ) := {x | ∀ i, -1 ≤ x i ∧ x i ≤ 1}
  have hP : P = {x : Fin n → ℝ | ∀ i,
      |(1 : ℝ) * x i| ≤ (1 : ℝ) - ∑ j : Fin n, if j < i then (0 : ℝ) * x j else 0} := by
    ext x
    simp only [P, one_mul, zero_mul, ite_self, Finset.sum_const_zero, sub_zero, abs_le]
  have hCoordinates : ∀ x ∈ P, ∀ i,
      0 < (1 : ℝ) - (∑ j : Fin n, if j < i then (0 : ℝ) * x j else 0) ∧
      (ExposedFaceBijection.refl P).toFun x i =
        (1 : ℝ) * x i / ((1 : ℝ) - ∑ j : Fin n, if j < i then (0 : ℝ) * x j else 0) := by
    intro x _ i
    change 0 < (1 : ℝ) - (∑ j : Fin n, if j < i then (0 : ℝ) * x j else 0) ∧
      x i = (1 : ℝ) * x i / ((1 : ℝ) - ∑ j : Fin n, if j < i then (0 : ℝ) * x j else 0)
    simp only [zero_mul, ite_self, Finset.sum_const_zero, sub_zero, one_mul, div_one,
      zero_lt_one, and_self]
  have h := triangular_source_coordinate_face_finrank (fun _ _ => (0 : ℝ)) 1
    one_ne_zero (fun _ => (1 : ℝ)) P hP (ExposedFaceBijection.refl P) hCoordinates I σ
  change Module.finrank ℝ (affineSpan ℝ {x : Fin n → ℝ | x ∈ P ∧ ∀ i ∈ I,
    (∑ j : Fin n, if j < i then (0 : ℝ) * x j else 0) +
      (if σ i then (1 : ℝ) else -1) * x i = 1}).direction = n - I.card at h
  have hFace : {x : Fin n → ℝ | x ∈ P ∧ ∀ i ∈ I,
      (∑ j : Fin n, if j < i then (0 : ℝ) * x j else 0) +
        (if σ i then (1 : ℝ) else -1) * x i = 1} =
      {x : Fin n → ℝ | (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧
        ∀ i ∈ I, x i = if σ i then 1 else -1} := by
    ext x
    change ((∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧ ∀ i ∈ I,
      (∑ j : Fin n, if j < i then (0 : ℝ) * x j else 0) +
        (if σ i then (1 : ℝ) else -1) * x i = 1) ↔ _
    simp only [Set.mem_ofPred_eq, zero_mul, ite_self, Finset.sum_const_zero,
      zero_add, sign_endpoint_iff]
  rw [hFace] at h
  exact h

end Grunbaum2003.RankSkeletonTransport


set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003.RankSkeletonTransport

                                                                      
theorem active_face_image {n : ℕ}
    (B : Fin n → Fin n → ℝ) (δ : ℝ) (b : Fin n → ℝ) (P : Set (Fin n → ℝ))
    (e : ExposedFaceBijection P {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1})
    (hCoordinates : ∀ x ∈ P, ∀ i,
      0 < b i - (∑ j : Fin n, if j < i then B i j * x j else 0) ∧
      e.toFun x i = δ * x i / (b i - ∑ j : Fin n, if j < i then B i j * x j else 0))
    (I : Finset (Fin n)) (σ : Fin n → Bool) :
    e.toFun '' {x | x ∈ P ∧ ∀ i ∈ I,
      (∑ j : Fin n, if j < i then B i j * x j else 0) +
        (if σ i then δ else -δ) * x i = b i} =
      {y | (∀ i, -1 ≤ y i ∧ y i ≤ 1) ∧ ∀ i ∈ I, y i = if σ i then 1 else -1} := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxP, hx⟩, rfl⟩
    refine ⟨e.map_mem x hxP, fun i hi => ?_⟩
    rw [(hCoordinates x hxP i).2]
    exact (normalized_coordinate_eq_endpoint_iff _ _ δ (x i) (σ i)
      (hCoordinates x hxP i).1).mpr (hx i hi)
  · rintro ⟨hyQ, hy⟩
    have hxP := e.inv_mem y hyQ
    refine ⟨e.invFun y, ⟨hxP, fun i hi => ?_⟩, e.right_inv y hyQ⟩
    apply (normalized_coordinate_eq_endpoint_iff _ _ δ (e.invFun y i) (σ i)
      (hCoordinates _ hxP i).1).mp
    rw [← (hCoordinates _ hxP i).2, e.right_inv y hyQ]
    exact hy i hi

                                                                           
                                                                             
                                                          
theorem normalizer_preserves_face_finrank {n : ℕ}
    (B : Fin n → Fin n → ℝ) (δ : ℝ) (hδ : δ ≠ 0) (b : Fin n → ℝ)
    (P : Set (Fin n → ℝ))
    (hP : P = {x : Fin n → ℝ | ∀ i,
      |δ * x i| ≤ b i - ∑ j : Fin n, if j < i then B i j * x j else 0})
    (e : ExposedFaceBijection P {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1})
    (hCoordinates : ∀ x ∈ P, ∀ i,
      0 < b i - (∑ j : Fin n, if j < i then B i j * x j else 0) ∧
      e.toFun x i = δ * x i / (b i - ∑ j : Fin n, if j < i then B i j * x j else 0))
    (S : Set (Fin n → ℝ)) (hS : IsExposed ℝ P S) :
    Module.finrank ℝ (affineSpan ℝ (e.toFun '' S)).direction =
      Module.finrank ℝ (affineSpan ℝ S).direction := by
  classical
  by_cases hSne : S.Nonempty
  · obtain ⟨I, σ, hSSet⟩ :=
      triangular_cube_face_classification B δ b P e hCoordinates S hS hSne
    have hSource := triangular_source_coordinate_face_finrank B δ hδ b P hP e hCoordinates I σ
    have hCenter := centered_coordinate_face_finrank I σ
    calc
      _ = n - I.card := by
        rw [hSSet, active_face_image B δ b P e hCoordinates I σ]
        exact hCenter
      _ = _ := by rw [hSSet]; exact hSource.symm
  · have hEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
    rw [hEmpty, Set.image_empty]

end Grunbaum2003.RankSkeletonTransport


set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace Grunbaum2003.RankSkeletonTransport

private def affineEquivFaceBijection {n m : ℕ}
    (f : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin m → ℝ)) (P : Set (Fin n → ℝ)) :
    ExposedFaceBijection P (f '' P) where
  toFun := f
  invFun := f.symm
  map_mem := fun x hx => ⟨x, hx, rfl⟩
  inv_mem := by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [AffineEquiv.symm_apply_apply] using hx
  left_inv := fun x _ => f.symm_apply_apply x
  right_inv := fun y _ => f.apply_symm_apply y
  map_face := fun S hS => isExposed_image_affineMap_of_injective f.toAffineMap f.injective hS
  inv_face := by
    intro T hT
    have h := isExposed_image_affineMap_of_injective f.symm.toAffineMap f.symm.injective hT
    change IsExposed ℝ (f.symm '' (f '' P)) (f.symm '' T) at h
    have hBack : f.symm '' (f '' P) = P := by
      apply Set.Subset.antisymm
      · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        simpa only [AffineEquiv.symm_apply_apply] using hx
      · intro x hx
        exact ⟨f x, ⟨x, hx, rfl⟩, f.symm_apply_apply x⟩
    rwa [hBack] at h

private theorem affineEquiv_preserves_direction_finrank {n m : ℕ}
    (f : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin m → ℝ)) (S : Set (Fin n → ℝ)) :
    Module.finrank ℝ (affineSpan ℝ (f '' S)).direction =
      Module.finrank ℝ (affineSpan ℝ S).direction := by
  apply finrank_direction_affineSpan_image_of_kernel_injective f.toAffineMap S
  intro z _ hz
  apply f.linear.injective
  simpa only [AffineEquiv.linear_toAffineMap, AffineEquiv.coe_linear,
    LinearEquiv.coe_coe, map_zero] using hz

                                                                       
                                                                             
                                                                               
theorem source_cube_rank_preserving_face_and_skeleton_isos {n : ℕ}
    (B : Fin n → Fin n → ℝ) (δ : ℝ) (hδ : δ ≠ 0) (b : Fin n → ℝ)
    (P : Set (Fin n → ℝ))
    (hP : P = {x : Fin n → ℝ | ∀ i,
      |δ * x i| ≤ b i - ∑ j : Fin n, if j < i then B i j * x j else 0})
    (e : ExposedFaceBijection P {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1})
    (hCoordinates : ∀ x ∈ P, ∀ i,
      0 < b i - (∑ j : Fin n, if j < i then B i j * x j else 0) ∧
      e.toFun x i = δ * x i / (b i - ∑ j : Fin n, if j < i then B i j * x j else 0)) :
    ∃ Φ : PolytopeFace P ≃o PolytopeFace (standardCube n),
      (∀ F, (Φ F).val = (fun x => centeredToUnitCube n (e.toFun x)) '' F.val) ∧
      (∀ F, Module.finrank ℝ (affineSpan ℝ (Φ F).val).direction =
        Module.finrank ℝ (affineSpan ℝ F.val).direction) ∧
      ∀ r : ℕ, ∃ φ : SkeletonFace P r ≃o SkeletonFace (standardCube n) r,
        ∀ F, (φ F).val = Φ F.val := by
  let C : Set (Fin n → ℝ) := {x | ∀ i, -1 ≤ x i ∧ x i ≤ 1}
  let f := centeredToUnitCube n
  let eUnit : ExposedFaceBijection C (standardCube n) :=
    (affineEquivFaceBijection f C).congr rfl (centeredToUnitCube_image n)
  let eFull : ExposedFaceBijection P (standardCube n) := e.trans eUnit
  obtain ⟨Φ, hΦ⟩ := eFull.exists_orderIso
  have hImage (S : Set (Fin n → ℝ)) :
      eFull.toFun '' S = f '' (e.toFun '' S) := by
    change (fun x => f (e.toFun x)) '' S = _
    rw [Set.image_image]
  have hRanks (F : PolytopeFace P) :
      Module.finrank ℝ (affineSpan ℝ (Φ F).val).direction =
        Module.finrank ℝ (affineSpan ℝ F.val).direction := by
    rw [hΦ F, hImage]
    exact (affineEquiv_preserves_direction_finrank f (e.toFun '' F.val)).trans
      (normalizer_preserves_face_finrank B δ hδ b P hP e hCoordinates F.val F.property)
  refine ⟨Φ, ?_, hRanks, ?_⟩
  · intro F
    exact hΦ F
  · intro r
    have hEmpty (F : PolytopeFace P) : (Φ F).val = ∅ ↔ F.val = ∅ := by
      rw [hΦ F, Set.image_eq_empty]
    have hPred (F : PolytopeFace P) :
        (F.val = ∅ ∨ Module.finrank ℝ (affineSpan ℝ F.val).direction ≤ r) ↔
          ((Φ F).val = ∅ ∨ Module.finrank ℝ (affineSpan ℝ (Φ F).val).direction ≤ r) := by
      rw [hEmpty F, hRanks F]
    let φ : SkeletonFace P r ≃o SkeletonFace (standardCube n) r := {
      toEquiv := Equiv.subtypeEquiv Φ.toEquiv hPred
      map_rel_iff' := by
        intro F G
        change Φ F.val ≤ Φ G.val ↔ F.val ≤ G.val
        exact Φ.le_iff_le }
    exact ⟨φ, fun _ => rfl⟩

theorem source_cube_skeleton_orderIso {n : ℕ}
    (B : Fin n → Fin n → ℝ) (δ : ℝ) (hδ : δ ≠ 0) (b : Fin n → ℝ)
    (P : Set (Fin n → ℝ))
    (hP : P = {x : Fin n → ℝ | ∀ i,
      |δ * x i| ≤ b i - ∑ j : Fin n, if j < i then B i j * x j else 0})
    (e : ExposedFaceBijection P {x : Fin n → ℝ | ∀ i, -1 ≤ x i ∧ x i ≤ 1})
    (hCoordinates : ∀ x ∈ P, ∀ i,
      0 < b i - (∑ j : Fin n, if j < i then B i j * x j else 0) ∧
      e.toFun x i = δ * x i / (b i - ∑ j : Fin n, if j < i then B i j * x j else 0))
    (r : ℕ) : Nonempty (SkeletonFace P r ≃o SkeletonFace (standardCube n) r) := by
  obtain ⟨Φ, _, _, hSkeleton⟩ :=
    source_cube_rank_preserving_face_and_skeleton_isos B δ hδ b P hP e hCoordinates
  obtain ⟨φ, _⟩ := hSkeleton r
  exact ⟨φ⟩

end Grunbaum2003.RankSkeletonTransport

end

-- Local ingredient: NeighborlyRealization

set_option autoImplicit false
open scoped BigOperators
open Grunbaum2003

                                                                           
                                                                            
                                                                            
                    
theorem solution (n d : ℕ) (hd : 2 ≤ d) (hnd : d < n) :
    ∃ P : Set (Fin d → ℝ), IsCubicalDPolytope P ∧
      Nonempty (SkeletonFace P (d / 2 - 1) ≃o
        SkeletonFace (standardCube n) (d / 2 - 1)) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + d :=
    ⟨n - d, (Nat.sub_add_cancel hnd.le).symm⟩
  have hData := exists_neighborly_cube_data_sub_eq (n := m + d) (m := m)
    hd hnd (Nat.add_sub_cancel m d)
  obtain ⟨B, δ, b, hδ, hRest⟩ := hData
  obtain ⟨hD, ⟨e, hCoordinates⟩, hPositive, hGeneric⟩ := hRest
  let C : Fin (m + d) → Fin (m + d) → ℝ :=
    fun a j => if h : j.val < m then B a ⟨j.val, h⟩ else 0
  let P : Set (Fin (m + d) → ℝ) := {x | ∀ i, |δ * x i| ≤ b i -
    ∑ j : Fin (m + d), if j < i then C i j * x j else 0}
  let π := retainedCoordinateProjection m d
  let r := d / 2 - 1
  have hr : r < d := by dsimp only [r]; omega
  have hCubical : IsCubicalDPolytope (π '' P) :=
    isCubicalDPolytope_triangular_projection
      B δ hδ.ne' hGeneric C rfl b P rfl hD e hCoordinates
  have hForward : ∀ S : Set (Fin (m + d) → ℝ), IsExposed ℝ P S →
      (S = ∅ ∨ Module.finrank ℝ (affineSpan ℝ S).direction ≤ r) →
      IsExposed ℝ (π '' P) (π '' S) ∧
      Module.finrank ℝ (affineSpan ℝ (π '' S)).direction =
        Module.finrank ℝ (affineSpan ℝ S).direction ∧
      ∀ x ∈ P, π x ∈ π '' S ↔ x ∈ S := by
    intro S hS hSmall
    exact small_source_faces_strictly_project B δ hδ.ne' r hr
      (fun J hJ σ => (hPositive J hJ σ).1) hGeneric C rfl b P rfl e hCoordinates S hS hSmall
  have hBack : ∀ G : Set (Fin d → ℝ), IsExposed ℝ (π '' P) G →
      (G = ∅ ∨ Module.finrank ℝ (affineSpan ℝ G).direction ≤ r) →
      {x | x ∈ P ∧ π x ∈ G} = ∅ ∨
        Module.finrank ℝ (affineSpan ℝ {x | x ∈ P ∧ π x ∈ G}).direction ≤ r := by
    intro G hG hSmall
    exact small_projected_face_source_preimage_small
      B δ hδ.ne' hGeneric C rfl b P rfl hD e hCoordinates r hr G hG hSmall
  obtain ⟨eProjection⟩ := skeleton_orderIso_of_strict_face_projection P π r hForward hBack
  obtain ⟨eCube⟩ := RankSkeletonTransport.source_cube_skeleton_orderIso
    C δ hδ.ne' b P rfl e hCoordinates r
  exact ⟨π '' P, hCubical, ⟨eProjection.symm.trans eCube⟩⟩

