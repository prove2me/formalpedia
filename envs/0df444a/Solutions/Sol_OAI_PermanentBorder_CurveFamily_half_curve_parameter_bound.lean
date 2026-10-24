-- Prove2me | solution 1 for OAI.PermanentBorder.CurveFamily.half_curve_parameter_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T19:57:15.079931+00:00
-- url     : https://prove2.me/submissions/ac67aa07-3f52-4cee-a631-a1510c0750c1

import Mathlib
import Definitions.Def_OAIQWPB000

section
-- module Solutions.OAIQW_PermanentBorder.Multigraded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial

variable {K σ G : Type*} [Field K] [AddCommGroup G]
variable (w : σ → G)

lemma project_mul {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (g : MvPolynomial σ K) (d : G) :
    weightedHomogeneousComponent w d (a * g) =
      a * weightedHomogeneousComponent w (d-e) g := by
  classical
  ext z
  simp only [coeff_weightedHomogeneousComponent, coeff_mul]
  have hi : (if Finsupp.weight w z = d then
      ∑ xy ∈ Finset.HasAntidiagonal.antidiagonal z, a.coeff xy.1 * g.coeff xy.2 else 0) =
      ∑ xy ∈ Finset.HasAntidiagonal.antidiagonal z,
        if Finsupp.weight w z = d then a.coeff xy.1 * g.coeff xy.2 else 0 := by
    rw [Finset.sum_ite_irrel]
    simp
  rw [hi]
  apply Finset.sum_congr rfl
  rintro ⟨x,y⟩ hxy
  have hsum : x+y=z := Finset.HasAntidiagonal.mem_antidiagonal.mp hxy
  by_cases hx : a.coeff x = 0
  · simp [hx]
  · have hwe : Finsupp.weight w x = e := ha hx
    have hcond : Finsupp.weight w z = d ↔ Finsupp.weight w y = d-e := by
      rw [← hsum, map_add, hwe]
      rw [eq_sub_iff_add_eq, add_comm]
    simp only [hcond]
    split_ifs <;> simp

end PermanentBorder.Multigraded

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.SmoothSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma intWeight_homogeneous {K σ : Type*} [CommSemiring K]
    {f : MvPolynomial σ K} {d : ℕ}
    (hf : f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d) :
    f.IsHomogeneous d := by
  intro s hs
  change Finsupp.weight (fun _ : σ => (1 : ℕ)) s = d
  rw [← Finsupp.degree_eq_weight_one]
  exact_mod_cast (intWeight_degree s ▸ hf hs)

end PermanentBorder.SliceParameters

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.HomogeneousPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.SliceParameters

universe u
open MvPolynomial

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

open scoped IntermediateField.algebraAdjoinAdjoin in
lemma field_adjoin_trdeg_le {κ : Type*} [Fintype κ] (x : κ → L) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) ≤
      (Fintype.card κ : Cardinal) := by
  let A := Algebra.adjoin K (Set.range x)
  let y : κ → A := fun i => ⟨x i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  have htop : Algebra.adjoin K (Set.range y) = ⊤ := by
    apply Subalgebra.map_injective (show Function.Injective A.val from Subtype.val_injective)
    rw [AlgHom.map_adjoin, Algebra.map_top, A.range_val, ← Set.range_comp]
    rfl
  let : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range y)) A := by
    constructor
    intro a
    have ha : a ∈ Algebra.adjoin K (Set.range y) := by rw [htop]; trivial
    exact isAlgebraic_algebraMap (R := Algebra.adjoin K (Set.range y)) ⟨a, ha⟩
  have hA : Algebra.trdeg K A ≤ (Fintype.card κ : Cardinal) := by
    calc
      Algebra.trdeg K A ≤ Cardinal.mk (Set.range y) :=
        Algebra.IsAlgebraic.trdeg_le_cardinalMk K (Set.range y)
      _ ≤ Fintype.card κ := by
        simpa using (Cardinal.mk_range_le_lift (f := y))
  rw [← trdeg_add_eq K A, trdeg_eq_zero (R := A), add_zero]
  exact hA

lemma add_parameters {κ : Type*} [Fintype κ] (F : IntermediateField K L)
    (n : ℕ) (hF : Algebra.trdeg K F ≤ (n : Cardinal)) (z : κ → L) :
    ∃ E : IntermediateField K L,
      F ≤ E ∧ (∀ i, z i ∈ E) ∧
      Algebra.trdeg K E ≤ (n + Fintype.card κ : ℕ) := by
  let E := IntermediateField.adjoin F (Set.range z)
  let : FaithfulSMul F E := (faithfulSMul_iff_algebraMap_injective F E).mpr
    (algebraMap F E).injective
  let : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨E.restrictScalars K, ?_, ?_, ?_⟩
  · intro x hx
    exact E.algebraMap_mem ⟨x, hx⟩
  · intro i
    exact IntermediateField.subset_adjoin F _ (Set.mem_range_self i)
  · change Algebra.trdeg K E ≤ _
    rw [← trdeg_add_eq K F]
    exact (add_le_add hF (field_adjoin_trdeg_le (K := F) z)).trans_eq (by simp)

end PermanentBorder.SliceParameters

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Transcendence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.ParameterBounds
open Algebra MvPolynomial
universe u
variable {K A : Type u} [Field K] [CommRing A] [IsDomain A] [Algebra K A]

theorem trdeg_lt_of_relation {n : ℕ} (x : Fin n → A)
    [Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) A]
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) (hx : aeval x p = 0) :
    Algebra.trdeg K A < (n : Cardinal) := by
  by_contra! ht
  have ht' : Cardinal.lift.{u} (Cardinal.mk (Fin n)) ≤
      Cardinal.lift.{0} (Algebra.trdeg K A) := by simpa using ht
  have hi := (Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite K x ht').1
  apply hp
  exact hi (by simpa using hx)

theorem adjoin_trdeg_lt_of_relation {n : ℕ} (x : Fin n → A)
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) (hx : aeval x p = 0) :
    Algebra.trdeg K (Algebra.adjoin K (Set.range x)) < (n : Cardinal) := by
  let B := Algebra.adjoin K (Set.range x)
  let y : Fin n → B := fun i => ⟨x i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  have htop : Algebra.adjoin K (Set.range y) = ⊤ := by
    apply Subalgebra.map_injective (show Function.Injective B.val from Subtype.val_injective)
    rw [AlgHom.map_adjoin, Algebra.map_top, B.range_val, ← Set.range_comp]
    rfl
  let : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range y)) B := by
    constructor
    intro b
    have hb : b ∈ Algebra.adjoin K (Set.range y) := by rw [htop]; trivial
    exact isAlgebraic_algebraMap (R := Algebra.adjoin K (Set.range y)) ⟨b, hb⟩
  apply trdeg_lt_of_relation y p hp
  apply (show Function.Injective B.val from Subtype.val_injective)
  rw [map_zero, MvPolynomial.comp_aeval_apply]
  exact hx

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem field_adjoin_trdeg_lt_of_relation {L : Type u} [Field L] [Algebra K L]
    {n : ℕ} (x : Fin n → L) (p : MvPolynomial (Fin n) K) (hp : p ≠ 0)
    (hx : aeval x p = 0) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) < (n : Cardinal) := by
  rw [← trdeg_add_eq K (Algebra.adjoin K (Set.range x)),
    trdeg_eq_zero (R := Algebra.adjoin K (Set.range x)), add_zero]
  exact adjoin_trdeg_lt_of_relation x p hp hx

end PermanentBorder.ParameterBounds

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Centralizers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CentralizerDimension

open Matrix MvPolynomial

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem eval_coordinateMatrix (A : Matrix ι ι K) (B : centralizer A) :
    (coordinateMatrix A).map (eval (fun b => (centralizerBasis A).repr B b)) = B.val := by
  classical
  ext i j
  have h := congrArg (fun W : centralizer A => W.val i j)
    ((centralizerBasis A).sum_repr B)
  simp only [coordinateMatrix, Matrix.map_apply, map_sum, map_mul, eval_C, eval_X]
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, mul_comm] using h

theorem eval_determinantPolynomial (A : Matrix ι ι K) (B : centralizer A) :
    eval (fun b => (centralizerBasis A).repr B b) (determinantPolynomial A) =
      B.val.det := by
  rw [determinantPolynomial, RingHom.map_det]
  change ((coordinateMatrix A).map (eval (fun b => (centralizerBasis A).repr B b))).det = _
  rw [eval_coordinateMatrix]

theorem determinantPolynomial_ne_zero (A : Matrix ι ι K) :
    determinantPolynomial A ≠ 0 := by
  intro h
  have he := eval_determinantPolynomial A (centralizerOne A)
  simp [h, centralizerOne] at he

end PermanentBorder.CentralizerDimension

namespace PermanentBorder.CoordinateGauge
open Module Submodule
variable {K ι : Type*} [Field K] [Fintype ι]

theorem exists_coordinate_gauge (S : Submodule K (ι → K)) :
    ∃ a : Fin (Module.finrank K S) → ι, Function.Injective a ∧
      Function.Bijective (fun x : S => fun j => x.val (a j)) := by
  classical
  let q (i : ι) : Module.Dual K S := (LinearMap.proj i).comp S.subtype
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K q
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let r : S →ₗ[K] (κ → K) := LinearMap.pi fun j => q (a j)
  have hri : Function.Injective r := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro x hx
    have hz : ∀ j, q (a j) x = 0 := congrFun (show r x = 0 from hx)
    have hs : ∀ g ∈ Submodule.span K (Set.range (q ∘ a)), g x = 0 := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem z hz' => obtain ⟨j, rfl⟩ := hz'; exact hz j
      | zero => rfl
      | add y z _ _ hy hz => simp only [LinearMap.add_apply, hy, hz, add_zero]
      | smul c y _ hy => simp only [LinearMap.smul_apply, hy, smul_zero]
    have hcoord (i : ι) : q i x = 0 := by
      apply hs
      rw [hspan]
      exact Submodule.subset_span (Set.mem_range_self i)
    change x = 0
    apply Subtype.ext
    funext i
    exact hcoord i
  have hc : Fintype.card κ = Module.finrank K S := by
    apply Nat.le_antisymm
    · simpa only [Subspace.dual_finrank_eq] using hli.fintype_card_le_finrank
    · simpa only [Module.finrank_fintype_fun_eq_card] using
        (LinearMap.finrank_le_finrank_of_injective hri)
  have hrs : Function.Surjective r :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa only [Module.finrank_fintype_fun_eq_card] using hc.symm)).mp hri
  let e := Fintype.equivFinOfCardEq hc
  refine ⟨a ∘ e.symm, ha.comp e.symm.injective, ?_, ?_⟩
  · intro x y h
    apply hri
    funext j
    have he := congrFun h (e j)
    change x.val (a j) = y.val (a j)
    simpa only [Function.comp_apply, e.symm_apply_apply] using he
  · intro v
    obtain ⟨x, hx⟩ := hrs (v ∘ e)
    refine ⟨x, ?_⟩
    funext j
    have he := congrFun hx (e.symm j)
    simpa only [r, LinearMap.pi_apply, q, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.proj_apply, Function.comp_apply, e.apply_symm_apply] using he

end PermanentBorder.CoordinateGauge

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.CoordinateFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CoordinateNormalization
open Matrix MvPolynomial CoordinateGauge
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L] [Infinite K]
  [Fintype ι] [DecidableEq ι]

theorem exists_base_eval_ne_zero {κ : Type*} (p : MvPolynomial κ L) (hp : p ≠ 0) :
    ∃ x : κ → K, MvPolynomial.eval (algebraMap K L ∘ x) p ≠ 0 := by
  classical
  by_contra! h
  apply hp
  apply MvPolynomial.funext_set (fun _ => Set.range (algebraMap K L))
    (fun _ => Set.infinite_range_of_injective (algebraMap K L).injective)
  intro x hx
  choose y hy using fun i => hx i (Set.mem_univ i)
  have he : algebraMap K L ∘ y = x := funext hy
  simp only [← he, h, map_zero]

theorem eval_basisDeterminant {κ : Type*} [Fintype κ]
    (S : Submodule L ((ι × ι) → L)) (b : Module.Basis κ L S) (v : S) :
    MvPolynomial.eval (fun a => b.repr v a) (basisDeterminant S b) =
      Matrix.det (Function.curry v.val) := by
  classical
  unfold basisDeterminant
  rw [RingHom.map_det]
  congr 1
  ext i j
  change MvPolynomial.eval (fun a => b.repr v a)
    (∑ a, C ((b a).val (i,j)) * X a) = v.val (i,j)
  simp only [map_sum, map_mul, eval_C, eval_X]
  have h := congrArg (fun z : S => z.val (i,j)) (b.sum_repr v)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_comm] using h

theorem exists_invertible_coordinate_gauge
    (S : Submodule L ((ι × ι) → L))
    (hS : ∃ v : S, Matrix.det (Function.curry v.val) ≠ 0) :
    ∃ (a : Fin (Module.finrank L S) → ι × ι) (v : S),
      Function.Injective a ∧ Matrix.det (Function.curry v.val) ≠ 0 ∧
      ∀ j, ∃ c : K, v.val (a j) = algebraMap K L c := by
  classical
  obtain ⟨a, hai, hab⟩ := exists_coordinate_gauge S
  let r : S →ₗ[L] (Fin (Module.finrank L S) → L) :=
    LinearMap.pi fun j => (LinearMap.proj (a j)).comp S.subtype
  let e : S ≃ₗ[L] (Fin (Module.finrank L S) → L) := LinearEquiv.ofBijective r hab
  let b := Module.Basis.ofEquivFun e
  have hp : basisDeterminant S b ≠ 0 := by
    obtain ⟨v, hv⟩ := hS
    intro h
    apply hv
    rw [← eval_basisDeterminant S b v, h, map_zero]
  obtain ⟨x, hx⟩ := exists_base_eval_ne_zero (K := K) (basisDeterminant S b) hp
  let v := e.symm (algebraMap K L ∘ x)
  have hre : (fun j => b.repr v j) = algebraMap K L ∘ x := by
    funext j
    simp only [b, Module.Basis.ofEquivFun_repr_apply, v, LinearEquiv.apply_symm_apply]
  refine ⟨a, v, hai, ?_, ?_⟩
  · rwa [← hre, eval_basisDeterminant] at hx
  · intro j
    refine ⟨x j, ?_⟩
    have h := congrFun (e.apply_symm_apply (algebraMap K L ∘ x)) j
    exact h

end PermanentBorder.CoordinateNormalization

namespace PermanentBorder.OrbitNormalization
open Matrix CentralizerDimension CentralizerBaseChange CoordinateNormalization
variable {L ι : Type*} [Field L] [Fintype ι] [DecidableEq ι]

variable {K : Type*} [Field K] [Algebra K L] [Infinite K]

theorem exists_normalized_intertwiner (A : Matrix ι ι L) (C : Matrix ι ι K)
    (P : (Matrix ι ι L)ˣ)
    (hP : A * (P : Matrix ι ι L) = (P : Matrix ι ι L) * C.map (algebraMap K L)) :
    ∃ (a : Fin (Module.finrank K (centralizer C)) → ι × ι)
      (Q : (Matrix ι ι L)ˣ),
      Function.Injective a ∧
      A * (Q : Matrix ι ι L) = (Q : Matrix ι ι L) * C.map (algebraMap K L) ∧
      ∀ j, ∃ c : K, (Q : Matrix ι ι L) (a j).1 (a j).2 = algebraMap K L c := by
  classical
  let S := intertwinerSpace A (C.map (algebraMap K L))
  have hd : Module.finrank L S = Module.finrank K (centralizer C) :=
    (intertwinerEquivCentralizer A _ P hP).finrank_eq.symm.trans
      (finrank_centralizer_map C)
  have hS : ∃ v : S, Matrix.det (Function.curry v.val) ≠ 0 := by
    refine ⟨⟨Function.uncurry (P : Matrix ι ι L), hP⟩, ?_⟩
    exact (Matrix.isUnits_det_units P).ne_zero
  obtain ⟨a, v, hai, hv, hvK⟩ := exists_invertible_coordinate_gauge (K := K) S hS
  obtain ⟨Q, hQ⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hv)
  let e := finCongr hd
  refine ⟨a ∘ e.symm, Q, hai.comp e.symm.injective, ?_, ?_⟩
  · rw [hQ]
    exact v.property
  · intro j
    obtain ⟨c, hc⟩ := hvK (e.symm j)
    exact ⟨c, by simpa only [hQ, Function.comp_apply, Function.curry] using hc⟩

end PermanentBorder.OrbitNormalization

namespace PermanentBorder.CentralizerParameters
open Matrix MvPolynomial CentralizerDimension CentralizerBaseChange
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype ι] [DecidableEq ι]

theorem entry_expansion (C : Matrix ι ι K)
    (B : centralizer (C.map (algebraMap K L))) (i j : ι) :
    B.val i j = ∑ a, coefficients C B a * algebraMap K L ((centralizerBasis C a).val i j) := by
  have h := congrArg (fun D : centralizer (C.map (algebraMap K L)) => D.val i j)
    ((centralizerBasisMap C (centralizerBasis C)).sum_repr B)
  simpa only [coefficients, Submodule.coe_sum, Submodule.coe_smul, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, centralizerBasisMap_apply,
    mapCentralizer, Matrix.map_apply] using h.symm

theorem eval_determinant (C : Matrix ι ι K)
    (B : centralizer (C.map (algebraMap K L))) :
    MvPolynomial.aeval (coefficients C B) (determinantPolynomial C) = B.val.det := by
  rw [determinantPolynomial, AlgHom.map_det]
  congr 1
  ext i j
  change MvPolynomial.aeval (coefficients C B)
    (∑ a, MvPolynomial.C ((centralizerBasis C a).val i j) * X a) = B.val i j
  simp only [map_sum, map_mul, aeval_C, aeval_X]
  rw [entry_expansion C B i j]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem determinant_relation (C : Matrix ι ι K)
    (B : centralizer (C.map (algebraMap K L))) (hB : B.val.det = 0) :
    determinantPolynomial C ≠ 0 ∧
      MvPolynomial.aeval (coefficients C B) (determinantPolynomial C) = 0 :=
  ⟨determinantPolynomial_ne_zero C, (eval_determinant C B).trans hB⟩

end PermanentBorder.CentralizerParameters

namespace PermanentBorder.MatrixSubfield
open Matrix
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem mul_mem (F : IntermediateField K L) (A B : Matrix ι ι L)
    (hA : ∀ i j, A i j ∈ F) (hB : ∀ i j, B i j ∈ F) :
    ∀ i j, (A * B) i j ∈ F := by
  intro i j
  exact F.sum_mem fun k _ => F.mul_mem (hA i k) (hB k j)

theorem unit_inv_mem (F : IntermediateField K L) (P : (Matrix ι ι L)ˣ)
    (hP : ∀ i j, (P : Matrix ι ι L) i j ∈ F) :
    ∀ i j, (↑P⁻¹ : Matrix ι ι L) i j ∈ F := by
  let A : Matrix ι ι F := fun i j => ⟨(P : Matrix ι ι L) i j, hP i j⟩
  have hA : A.map (algebraMap F L) = (P : Matrix ι ι L) := rfl
  have hd : A.det ≠ 0 := by
    intro h
    have he : algebraMap F L A.det = (P : Matrix ι ι L).det :=
      (algebraMap F L).map_det A
    rw [h, map_zero] at he
    exact (Matrix.isUnits_det_units P).ne_zero he.symm
  have hi := congrArg (fun M : Matrix ι ι F => M.map (algebraMap F L))
    (Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hd))
  simp only [Matrix.map_mul, hA, Matrix.map_one _ (map_zero _) (map_one _)] at hi
  have he : A⁻¹.map (algebraMap F L) = (↑P⁻¹ : Matrix ι ι L) := by
    calc
      _ = (A⁻¹.map (algebraMap F L) * (P : Matrix ι ι L)) * (↑P⁻¹ : Matrix ι ι L) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [hi, one_mul]
  intro i j
  rw [← he]
  exact ((A⁻¹) i j).property

end PermanentBorder.MatrixSubfield

namespace PermanentBorder.ParameterBounds
open Algebra MvPolynomial
universe u
variable {K A : Type u} [Field K] [CommRing A] [IsDomain A] [Algebra K A]

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem field_adjoin_trdeg_lt_of_relation_fintype {L : Type u} [Field L] [Algebra K L]
    {κ : Type*} [Fintype κ] (x : κ → L) (p : MvPolynomial κ K) (hp : p ≠ 0)
    (hx : aeval x p = 0) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) < (Fintype.card κ : Cardinal) := by
  classical
  let e := Fintype.equivFin κ
  let y := x ∘ e.symm
  have hy : Set.range y = Set.range x := e.symm.surjective.range_comp x
  rw [← hy]
  apply field_adjoin_trdeg_lt_of_relation y (MvPolynomial.rename e p)
  · exact fun h => hp ((MvPolynomial.rename_injective e e.injective) (by simpa using h))
  · simpa only [MvPolynomial.aeval_rename, y, Function.comp_assoc,
      Equiv.symm_comp_self, Function.comp_id] using hx

end PermanentBorder.ParameterBounds

namespace PermanentBorder.CommutingPairs
open Matrix CentralizerDimension CentralizerParameters OrbitNormalization
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Infinite K]

theorem normalized_pair_field_bound {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) L) (C : Matrix (Fin n) (Fin n) K)
    (P : (Matrix (Fin n) (Fin n) L)ˣ)
    (hP : A * (P : Matrix (Fin n) (Fin n) L) =
      (P : Matrix (Fin n) (Fin n) L) * C.map (algebraMap K L))
    (hAB : A * B = B * A) (hB : B.det = 0) :
    ∃ F : IntermediateField K L,
      Algebra.trdeg K F < (n * n : ℕ) ∧
      (∀ i j, A i j ∈ F) ∧ (∀ i j, B i j ∈ F) := by
  classical
  obtain ⟨a, Q, hai, hQ, hQa⟩ := exists_normalized_intertwiner A C P hP
  let j := Module.finrank K (centralizer C)
  let C' := C.map (algebraMap K L)
  have hC' : C' = (↑Q⁻¹ : Matrix (Fin n) (Fin n) L) * A * (Q : Matrix (Fin n) (Fin n) L) := by
    calc
      _ = (↑Q⁻¹ : Matrix (Fin n) (Fin n) L) * ((Q : Matrix (Fin n) (Fin n) L) * C') := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [← hQ, mul_assoc]
  let B' : centralizer C' := ⟨(↑Q⁻¹ : Matrix (Fin n) (Fin n) L) * B * (Q : Matrix (Fin n) (Fin n) L), by
    change C' * _ = _ * C'
    rw [hC']
    simp only [mul_assoc]
    simp only [← mul_assoc (Q : Matrix (Fin n) (Fin n) L), Units.mul_inv, one_mul]
    simp only [← mul_assoc]
    rw [mul_assoc (↑Q⁻¹ : Matrix (Fin n) (Fin n) L) A B, hAB, ← mul_assoc]⟩
  let κ := {p : Fin n × Fin n // p ∉ Set.range a} ⊕ Fin j
  let x : κ → L := Sum.elim
    (fun p => (Q : Matrix (Fin n) (Fin n) L) p.val.1 p.val.2)
    (coefficients C B')
  let F := IntermediateField.adjoin K (Set.range x)
  have hx (i : κ) : x i ∈ F := IntermediateField.subset_adjoin K _ (Set.mem_range_self i)
  have ha_card : Fintype.card {p : Fin n × Fin n // p ∈ Set.range a} = j := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr (Equiv.ofInjective a hai)).symm
  have hj : j ≤ n * n := by
    simpa only [Fintype.card_fin, Fintype.card_prod] using Fintype.card_le_of_injective a hai
  have hκ : Fintype.card κ = n * n := by
    simp only [κ, Fintype.card_sum, Fintype.card_subtype_compl, ha_card,
      Fintype.card_prod, Fintype.card_fin]
    exact Nat.sub_add_cancel hj
  have hB' : B'.val.det = 0 := (Matrix.det_units_conj' Q B).trans hB
  obtain ⟨hp, hxp⟩ := determinant_relation C B' hB'
  have hFp : Algebra.trdeg K F < (Fintype.card κ : Cardinal) := by
    apply ParameterBounds.field_adjoin_trdeg_lt_of_relation_fintype x
      (MvPolynomial.rename (Sum.inr : Fin j → κ) (determinantPolynomial C))
    · exact fun h => hp ((MvPolynomial.rename_injective _ Sum.inr_injective) (by simpa using h))
    · simpa only [MvPolynomial.aeval_rename, Function.comp_def, x, Sum.elim_inr] using hxp
  have hQF : ∀ i j, (Q : Matrix (Fin n) (Fin n) L) i j ∈ F := by
    intro i j
    by_cases h : (i,j) ∈ Set.range a
    · obtain ⟨b, hb⟩ := h
      obtain ⟨c, hc⟩ := hQa b
      rw [hb] at hc
      rw [hc]
      exact F.algebraMap_mem c
    · exact hx (Sum.inl ⟨(i,j), h⟩)
  have hQiF := MatrixSubfield.unit_inv_mem F Q hQF
  have hCF : ∀ i j, C' i j ∈ F := fun i j => F.algebraMap_mem (C i j)
  have hBF : ∀ i j, B'.val i j ∈ F := by
    intro i j
    rw [entry_expansion C B' i j]
    exact F.sum_mem fun b _ => F.mul_mem (hx (Sum.inr b)) (F.algebraMap_mem _)
  have hAeq : A = (Q : Matrix (Fin n) (Fin n) L) * C' * (↑Q⁻¹ : Matrix (Fin n) (Fin n) L) := by
    rw [← hQ, mul_assoc, Units.mul_inv, mul_one]
  have hBeq : B = (Q : Matrix (Fin n) (Fin n) L) * B'.val * (↑Q⁻¹ : Matrix (Fin n) (Fin n) L) := by
    change B = (Q : Matrix (Fin n) (Fin n) L) *
      ((↑Q⁻¹ : Matrix (Fin n) (Fin n) L) * B * (Q : Matrix (Fin n) (Fin n) L)) *
      (↑Q⁻¹ : Matrix (Fin n) (Fin n) L)
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
  refine ⟨F, ?_, ?_, ?_⟩
  · simpa only [hκ] using hFp
  · rw [hAeq]
    exact MatrixSubfield.mul_mem F _ _ (MatrixSubfield.mul_mem F _ _ hQF hCF) hQiF
  · rw [hBeq]
    exact MatrixSubfield.mul_mem F _ _ (MatrixSubfield.mul_mem F _ _ hQF hBF) hQiF

end PermanentBorder.CommutingPairs

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Nilpotents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.NilpotentOrbits
open scoped DirectSum
open Submodule Module Polynomial Ideal Submodule.IsPrincipal Submodule.Quotient

section Decomposition
variable {R M : Type*} [CommRing R] [IsPrincipalIdealRing R] [IsDomain R]
  [AddCommGroup M] [Module R M]

/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin

The following decomposition theorem is adapted from Mathlib.Algebra.Module.PID.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Algebra/Module/PID.lean

This code has been modified.
-/

theorem decomposition_of_generators {p : R} (hp : Irreducible p)
    (hM : Module.IsTorsion' M (Submonoid.powers p))
    (d : ℕ) (s : Fin d → M) (hs : Submodule.span R (Set.range s) = ⊤) :
    ∃ k : Fin d → ℕ, Nonempty (M ≃ₗ[R] ⨁ i : Fin d, R ⧸ R ∙ p ^ k i) := by
  classical
  induction d generalizing M with
  | zero =>
    use finZeroElim
    rw [Set.range_eq_empty, Submodule.span_empty] at hs
    have : Unique M :=
      ⟨⟨0⟩, fun x => by dsimp; rw [← Submodule.mem_bot R, hs]; exact Submodule.mem_top⟩
    exact ⟨0⟩
  | succ d IH =>
    have : ∀ x : M, Decidable (x = 0) := fun _ => by classical infer_instance
    obtain ⟨j, hj⟩ := exists_isTorsionBy hM d.succ d.succ_ne_zero s hs
    let s' : Fin d → M ⧸ R ∙ s j := Submodule.Quotient.mk ∘ s ∘ j.succAbove

    have := IH ?_ s' ?_
    · obtain ⟨k, ⟨f⟩⟩ := this
      clear IH
      have : ∀ i : Fin d,
          ∃ x : M, p ^ k i • x = 0 ∧ f (Submodule.Quotient.mk x) = DirectSum.lof R _ _ i 1 := by
        intro i
        let fi := f.symm.toLinearMap.comp (DirectSum.lof _ _ _ i)
        obtain ⟨x, h0, h1⟩ := exists_smul_eq_zero_and_mk_eq hp hM hj fi; refine ⟨x, h0, ?_⟩; rw [h1]
        simp only [fi, LinearMap.coe_comp, f.symm.coe_toLinearMap, f.apply_symm_apply,
          Function.comp_apply]
      refine ⟨?_, ⟨?_⟩⟩
      · exact fun a => (fun i => (Option.rec (pOrder hM (s j)) k i : ℕ)) (finSuccEquiv d a)
      · refine
          (lequivProdOfRightSplitExact
            (g := f.toLinearMap.comp <| mkQ _)
            (f := (DirectSum.toModule _ _ _ fun i => (liftQSpanSingleton (p ^ k i)
                (LinearMap.toSpanSingleton _ _ _)
                (show (LinearMap.toSpanSingleton R M (this i).choose) (p ^ k i) = 0 from
                  (this i).choose_spec.left) : R ⧸ _ →ₗ[R] _)))
              (R ∙ s j).injective_subtype ?_ ?_).symm ≪≫ₗ
          (((quotTorsionOfEquivSpanSingleton R M (s j)).symm ≪≫ₗ
            (quotEquivOfEq (torsionOf R M (s j)) _
              (Ideal.torsionOf_eq_span_pow_pOrder hp hM (s j)))).prodCongr (.refl _ _)) ≪≫ₗ
          (@DirectSum.lequivProdDirectSum R _ _
            (fun i => R ⧸ R ∙ p ^ @Option.rec _ (fun _ => ℕ) (pOrder hM <| s j) k i) _ _).symm ≪≫ₗ
          (DirectSum.lequivCongrLeft R (finSuccEquiv d).symm)
        · rw [range_subtype, LinearEquiv.ker_comp, ker_mkQ]
        · rw [LinearMap.comp_assoc]
          ext i : 3
          simp only [LinearMap.coe_comp, Function.comp_apply, mkQ_apply]
          rw [LinearEquiv.coe_toLinearMap, LinearMap.id_apply, DirectSum.toModule_lof,
            liftQSpanSingleton_apply, LinearMap.toSpanSingleton_apply_one, Ideal.Quotient.mk_eq_mk,
            map_one (Ideal.Quotient.mk _), (this i).choose_spec.right]
    · exact (mk_surjective _).forall.mpr fun x =>
        ⟨(@hM x).choose, by rw [← Quotient.mk_smul, (@hM x).choose_spec, Quotient.mk_zero]⟩
    · have hs' := congr_arg (Submodule.map <| mkQ <| R ∙ s j) hs
      rw [Submodule.map_span, Submodule.map_top, range_mkQ] at hs'
      simp only [s']; rw [← Function.comp_assoc, Set.range_comp (_ ∘ s), Fin.range_succAbove]
      rw [← Set.range_comp, ← Set.insert_image_compl_eq_range _ j, Function.comp_apply,
        mkQ_apply, (Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self _),
        Submodule.span_insert_zero] at hs'
      exact hs'

end Decomposition

section Nilpotent
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem torsion_of_nilpotent (f : Module.End K V) (hf : IsNilpotent f) :
    Module.IsTorsion' (Module.AEval' f) (Submonoid.powers (X : K[X])) := by
  obtain ⟨e, he⟩ := hf
  intro x
  refine ⟨⟨X ^ e, ⟨e, rfl⟩⟩, ?_⟩
  change (X ^ e : K[X]) • x = 0
  obtain ⟨v, rfl⟩ := (Module.AEval'.of f).surjective x
  rw [Module.AEval'.X_pow_smul_of, he, zero_smul, map_zero]

theorem nilpotent_decomposition {n : ℕ} (b : Module.Basis (Fin n) K V)
    (f : Module.End K V) (hf : IsNilpotent f) :
    ∃ e : Fin n → ℕ,
      Nonempty (Module.AEval' f ≃ₗ[K[X]] ⨁ i : Fin n, Block (K := K) (e i)) := by
  let b' := b.map (Module.AEval'.of f)
  exact decomposition_of_generators Polynomial.irreducible_X
    (torsion_of_nilpotent f hf) n b'
    (Submodule.span_eq_top_of_span_eq_top K K[X] _ b'.span_eq)

theorem unit_conjugacy_of_intertwiner (f g : Module.End K V)
    (L : V ≃ₗ[K] V) (hL : ∀ v, L (f v) = g (L v)) :
    ∃ U : (Module.End K V)ˣ, g = (U : Module.End K V) * f * (↑U⁻¹ : Module.End K V) := by
  let U := (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm L
  have hu : (U : Module.End K V) = L.toLinearMap := rfl
  have h : (U : Module.End K V) * f = g * (U : Module.End K V) := by
    ext v
    exact hL v
  refine ⟨U, ?_⟩
  rw [h, mul_assoc, Units.mul_inv, mul_one]

end Nilpotent

end PermanentBorder.NilpotentOrbits

namespace PermanentBorder.NilpotentBlocks
open Polynomial Module
open scoped DirectSum
variable {K : Type*} [Field K]

theorem X_smul_blockBasis (e : ℕ) (i : Fin e) :
    (X : K[X]) • blockBasis (K := K) e i =
      if h : i.val + 1 < e then blockBasis e ⟨i.val + 1, h⟩ else 0 := by
  rw [blockBasis_apply]
  change Ideal.Quotient.mk _ ((X : K[X]) * X ^ i.val) = _
  rw [← pow_succ']
  split_ifs with h
  · exact (blockBasis_apply e ⟨i.val + 1, h⟩).symm
  · have he : i.val + 1 = e := by omega
    rw [he]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton _)

@[simp] theorem action_sumBasis {n : ℕ} (e : Fin n → ℕ)
    (i : Fin n) (j : Fin (e i)) :
    action (K := K) e (sumBasis e ⟨i,j⟩) =
      if h : j.val + 1 < e i then sumBasis e ⟨i,⟨j.val + 1,h⟩⟩ else 0 := by
  classical
  rw [sumBasis_apply]
  change (X : K[X]) • DirectSum.lof K (Fin n) (fun i => Block (K := K) (e i)) i (blockBasis (e i) j) = _
  have hmap := (DirectSum.lof K[X] (Fin n) (fun i => Block (K := K) (e i)) i).map_smul
    (X : K[X]) (blockBasis (e i) j)
  change DirectSum.lof K (Fin n) (fun i => Block (K := K) (e i)) i ((X : K[X]) • blockBasis (e i) j) =
    (X : K[X]) • DirectSum.lof K (Fin n) (fun i => Block (K := K) (e i)) i
      (blockBasis (e i) j) at hmap
  rw [← hmap, X_smul_blockBasis]
  split_ifs with h
  · exact (sumBasis_apply e i ⟨j.val + 1,h⟩).symm
  · exact map_zero _

theorem toMatrix_action {n : ℕ} (e : Fin n → ℕ) :
    LinearMap.toMatrix (sumBasis (K := K) e) (sumBasis e) (action e) = shiftMatrix e := by
  classical
  ext ⟨a,i⟩ ⟨b,j⟩
  simp only [LinearMap.toMatrix_apply, action_sumBasis]
  split_ifs with h
  · simp only [Basis.repr_self, Finsupp.single_apply]
    by_cases hab : a = b
    · subst b
      simp [shiftMatrix, Fin.ext_iff, eq_comm]
    · have hba : b ≠ a := Ne.symm hab
      simp [shiftMatrix, hab, hba]
  · simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    simp only [shiftMatrix]
    split_ifs with hab
    · obtain ⟨rfl, hij⟩ := hab
      omega
    · rfl

end PermanentBorder.NilpotentBlocks

namespace PermanentBorder.NilpotentBlocks
open Polynomial Module
open scoped DirectSum
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem toMatrix_of_intertwiner {W ι : Type*} [AddCommGroup W] [Module K W]
    [Fintype ι] [DecidableEq ι] (b : Basis ι K W) (f : Module.End K V)
    (g : Module.End K W) (L : V ≃ₗ[K] W) (hL : ∀ v, L (f v) = g (L v)) :
    LinearMap.toMatrix (b.map L.symm) (b.map L.symm) f = LinearMap.toMatrix b b g := by
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  congr 1
  apply LinearMap.ext
  intro x
  change L (f (L.symm x)) = g x
  rw [hL, L.apply_symm_apply]

theorem shift_basis_of_equiv {n : ℕ} (e : Fin n → ℕ) (f : Module.End K V)
    (L : V ≃ₗ[K] ⨁ i : Fin n, Block (K := K) (e i))
    (hL : ∀ v, L (f v) = action e (L v)) :
    ∃ b : Basis (Σ i : Fin n, Fin (e i)) K V,
      LinearMap.toMatrix b b f = shiftMatrix e := by
  classical
  refine ⟨(sumBasis e).map L.symm, ?_⟩
  have ht := toMatrix_of_intertwiner (K := K) (V := V)
    (W := ⨁ i : Fin n, Block (K := K) (e i)) (ι := Σ i : Fin n, Fin (e i))
    (sumBasis (K := K) e) f (action (K := K) e) L hL
  exact ht.trans (toMatrix_action (K := K) e)

theorem exists_shift_basis {n : ℕ} (b₀ : Basis (Fin n) K V)
    (f : Module.End K V) (hf : IsNilpotent f) :
    ∃ e : Fin n → ℕ, (∑ i, e i) = n ∧
      ∃ b : Basis (Σ i : Fin n, Fin (e i)) K V,
        LinearMap.toMatrix b b f = shiftMatrix e := by
  classical
  obtain ⟨e, ⟨E⟩⟩ := NilpotentOrbits.nilpotent_decomposition b₀ f hf
  let L : V ≃ₗ[K] ⨁ i : Fin n, Block (K := K) (e i) :=
    (Module.AEval'.of f).trans (E.restrictScalars K)
  have hL (v : V) : L (f v) = action e (L v) := by
    change E (Module.AEval'.of f (f v)) = (X : K[X]) • E (Module.AEval'.of f v)
    rw [← Module.AEval'.X_smul_of, E.map_smul]
  obtain ⟨b, hb⟩ := shift_basis_of_equiv e f L hL
  refine ⟨e, ?_, b, hb⟩
  have hc := (Module.finrank_eq_card_basis b).symm.trans
    (Module.finrank_eq_card_basis b₀)
  simpa only [Fintype.card_sigma, Fintype.card_fin] using hc

end PermanentBorder.NilpotentBlocks

namespace PermanentBorder.NilpotentBlocks
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_shape_basis {n : ℕ} (b₀ : Basis (Fin n) K V)
    (f : Module.End K V) (hf : IsNilpotent f) :
    ∃ e : Fin n → ℕ, ∃ he : (∑ i, e i) = n,
      ∃ b : Basis (Fin n) K V, LinearMap.toMatrix b b f = shapeMatrix e he := by
  classical
  obtain ⟨e, he, b, hb⟩ := exists_shift_basis b₀ f hf
  refine ⟨e, he, b.reindex (indexEquiv e he), ?_⟩
  ext i j
  simpa only [LinearMap.toMatrix_apply, Basis.reindex_apply, Basis.repr_reindex_apply,
    shapeMatrix, Matrix.reindex_apply, Matrix.submatrix_apply] using
      congrArg (fun M => M ((indexEquiv e he).symm i) ((indexEquiv e he).symm j)) hb

theorem matrix_conjugacy_of_basis {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (b : Basis (Fin n) K (Fin n → K)) :
    ∃ U : (Matrix (Fin n) (Fin n) K)ˣ,
      LinearMap.toMatrix b b (Matrix.toLinAlgEquiv' A) =
        (U : Matrix (Fin n) (Fin n) K) * A * (↑U⁻¹ : Matrix (Fin n) (Fin n) K) := by
  classical
  let E : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K) := Matrix.toLinAlgEquiv'
  let B := LinearMap.toMatrix b b (E A)
  have hL (v : Fin n → K) : b.equivFun (E A v) = E B (b.equivFun v) := by
    change b.repr (E A v) = B.mulVec (b.repr v)
    exact (LinearMap.toMatrix_mulVec_repr b b (E A) v).symm
  obtain ⟨U, hU⟩ := NilpotentOrbits.unit_conjugacy_of_intertwiner (E A) (E B) b.equivFun hL
  let W := Units.map E.symm.toRingHom.toMonoidHom U
  refine ⟨W, ?_⟩
  change B = E.symm (U : Module.End K (Fin n → K)) * A *
    E.symm (↑U⁻¹ : Module.End K (Fin n → K))
  have h := congrArg E.symm hU
  simpa only [map_mul, E.symm_apply_apply] using h

theorem canonical_nilpotent_form (K : Type*) [Field K] {L : Type*} [Field L]
    (φ : K →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) L) (hA : IsNilpotent A) :
    ∃ e : Fin n → ℕ, ∃ he : (∑ i, e i) = n,
      ∃ U : (Matrix (Fin n) (Fin n) L)ˣ,
        (shapeMatrix (K := K) e he).map φ =
          (U : Matrix (Fin n) (Fin n) L) * A * (↑U⁻¹ : Matrix (Fin n) (Fin n) L) := by
  obtain ⟨e, he, b, hb⟩ := exists_shape_basis (Pi.basisFun L (Fin n))
    (Matrix.toLinAlgEquiv' A) (hA.map Matrix.toLinAlgEquiv')
  obtain ⟨U, hU⟩ := matrix_conjugacy_of_basis A b
  exact ⟨e, he, U, by rw [shapeMatrix_map, ← hb]; exact hU⟩

end PermanentBorder.NilpotentBlocks

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.PunctualCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CommutingPairs
open Matrix CentralizerDimension CentralizerParameters OrbitNormalization
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Infinite K]

theorem nilpotent_pair_field_bound {n : ℕ} (hn : 0 < n)
    (A B : Matrix (Fin n) (Fin n) L) (hA : IsNilpotent A) (hB : IsNilpotent B)
    (hAB : A * B = B * A) :
    ∃ F : IntermediateField K L,
      Algebra.trdeg K F ≤ (n * n - 1 : ℕ) ∧
      (∀ i j, A i j ∈ F) ∧ (∀ i j, B i j ∈ F) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hBd : B.det = 0 := by
    obtain ⟨r, hr⟩ := hB
    have hd : B.det ^ r = 0 := by rw [← Matrix.det_pow, hr, Matrix.det_zero]
    by_contra h
    exact pow_ne_zero r h hd
  obtain ⟨e, he, U, hU⟩ := NilpotentBlocks.canonical_nilpotent_form K (algebraMap K L) A hA
  have hP : A * (↑U⁻¹ : Matrix (Fin n) (Fin n) L) =
      (↑U⁻¹ : Matrix (Fin n) (Fin n) L) *
        (NilpotentBlocks.shapeMatrix (K := K) e he).map (algebraMap K L) := by
    rw [hU, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨F, hF, hAF, hBF⟩ := normalized_pair_field_bound A B
    (NilpotentBlocks.shapeMatrix e he) U⁻¹ hP hAB hBd
  refine ⟨F, ?_, hAF, hBF⟩
  have hpos : 0 < n * n := Nat.mul_pos hn hn
  have hc : n * n = (n * n - 1) + 1 := by omega
  rw [hc, Nat.cast_add, Nat.cast_one] at hF
  exact Cardinal.lt_natCast_add_one_iff.mp hF

end PermanentBorder.CommutingPairs

namespace PermanentBorder.FieldParameters
open Algebra MvPolynomial
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

theorem adjoin_trdeg_le {n : ℕ} (x : Fin n → L) :
    Algebra.trdeg K (Algebra.adjoin K (Set.range x)) ≤ (n : Cardinal) := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  have h := trdeg_le_of_surjective (MvPolynomial.aeval (R := K) x).rangeRestrict
    (AlgHom.rangeRestrict_surjective (MvPolynomial.aeval (R := K) x))
  simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin, Cardinal.lift_natCast] using h

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem field_adjoin_trdeg_le {n : ℕ} (x : Fin n → L) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) ≤ (n : Cardinal) := by
  rw [← trdeg_add_eq K (Algebra.adjoin K (Set.range x)),
    trdeg_eq_zero (R := Algebra.adjoin K (Set.range x)), add_zero]
  exact adjoin_trdeg_le x

theorem extend_field {p n : ℕ} (F : IntermediateField K L)
    (hF : Algebra.trdeg K F ≤ (p : Cardinal)) (x : Fin n → L) :
    ∃ E : IntermediateField K L,
      F ≤ E ∧ Algebra.trdeg K E ≤ (p + n : ℕ) ∧ (∀ i, x i ∈ E) := by
  let T := IntermediateField.adjoin F (Set.range x)
  let E := T.restrictScalars K
  have : FaithfulSMul F T := (faithfulSMul_iff_algebraMap_injective F T).mpr
    (algebraMap F T).injective
  have : FaithfulSMul K F := (faithfulSMul_iff_algebraMap_injective K F).mpr
    (algebraMap K F).injective
  have hFE : F ≤ E := by
    intro y hy
    exact T.algebraMap_mem ⟨y, hy⟩
  have hx : ∀ i, x i ∈ E := fun i => IntermediateField.subset_adjoin F _ (Set.mem_range_self i)
  refine ⟨E, hFE, ?_, hx⟩
  calc
    Algebra.trdeg K E = Algebra.trdeg K F + Algebra.trdeg F T := (trdeg_add_eq K F (A := T)).symm
    _ ≤ (p : Cardinal) + n := add_le_add hF (field_adjoin_trdeg_le (K := F) x)
    _ = (p + n : ℕ) := by simp only [Nat.cast_add]

end PermanentBorder.FieldParameters

namespace PermanentBorder.GenericMatrix
open Matrix MvPolynomial
universe u
variable (L : Type u) [Field L] (n : ℕ)

theorem relative_trdeg : Algebra.trdeg L (FunctionField L n) = (n * n : ℕ) := by
  have : Algebra.IsAlgebraic (CoordinateRing L n) (FunctionField L n) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (CoordinateRing L n))
  have : FaithfulSMul (CoordinateRing L n) (FunctionField L n) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (IsFractionRing.injective (CoordinateRing L n) (FunctionField L n))
  rw [← trdeg_add_eq L (CoordinateRing L n), trdeg_eq_zero (R := CoordinateRing L n), add_zero]
  simp only [CoordinateRing, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_prod,
    Cardinal.mk_fin, Cardinal.lift_mul, Cardinal.lift_natCast, Nat.cast_mul]

theorem field_eq_top_of_mem (K : Type u) [Field K] [Algebra K L]
    (E : IntermediateField K (FunctionField L n))
    (hc : ∀ x : L, algebraMap L (FunctionField L n) x ∈ E)
    (hx : ∀ i j, genericMatrix L n i j ∈ E) : E = ⊤ := by
  have hp : ∀ p : CoordinateRing L n,
      algebraMap (CoordinateRing L n) (FunctionField L n) p ∈ E := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C x =>
      change algebraMap (CoordinateRing L n) (FunctionField L n)
        (algebraMap L (CoordinateRing L n) x) ∈ E
      rw [← IsScalarTower.algebraMap_apply]
      exact hc x
    | add p q hp hq =>
      rw [map_add]
      exact E.add_mem hp hq
    | mul_X p ij hp =>
      rw [map_mul]
      exact E.mul_mem hp (hx ij.1 ij.2)
  apply eq_top_iff.mpr
  intro z _
  obtain ⟨p, q, _, hz⟩ := IsFractionRing.div_surjective (CoordinateRing L n) z
  rw [← hz]
  exact E.div_mem (hp p) (hp q)

end PermanentBorder.GenericMatrix

namespace PermanentBorder.CyclicFrames
open Matrix
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype ι] [DecidableEq ι]

theorem recover_frame (r s : ι → ℕ) (A B A' B' Q : Matrix ι ι L)
    (v v' : ι → L) (hb : MonomialBasis r s A B v)
    (hA : A' * Q = Q * A) (hB : B' * Q = Q * B) (hv : v' = Q.mulVec v) :
    ∀ i j, Q i j = ((A' ^ r j * B' ^ s j).mulVec v') i := by
  intro i j
  have hpa : Q * A ^ r j = A' ^ r j * Q := (SemiconjBy.pow_right hA.symm _)
  have hpb : Q * B ^ s j = B' ^ s j * Q := (SemiconjBy.pow_right hB.symm _)
  have hm : (A' ^ r j * B' ^ s j) * Q = Q * (A ^ r j * B ^ s j) := by
    rw [mul_assoc, ← hpb, ← mul_assoc, ← hpa, mul_assoc]
  rw [hv, Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, hb j,
    Matrix.mulVec_single]
  simp

theorem pow_mem (F : IntermediateField K L) (A : Matrix ι ι L)
    (hA : ∀ i j, A i j ∈ F) (r : ℕ) : ∀ i j, (A ^ r) i j ∈ F := by
  induction r with
  | zero =>
    intro i j
    simp only [pow_zero, Matrix.one_apply]
    split <;> simp
  | succ r hr =>
    rw [pow_succ]
    exact MatrixSubfield.mul_mem F _ _ hr hA

omit [DecidableEq ι] in
theorem mulVec_mem (F : IntermediateField K L) (A : Matrix ι ι L) (v : ι → L)
    (hA : ∀ i j, A i j ∈ F) (hv : ∀ i, v i ∈ F) : ∀ i, A.mulVec v i ∈ F := by
  intro i
  exact F.sum_mem fun j _ => F.mul_mem (hA i j) (hv j)

theorem frame_mem (F : IntermediateField K L) (r s : ι → ℕ)
    (A B A' B' Q : Matrix ι ι L) (v v' : ι → L)
    (hb : MonomialBasis r s A B v)
    (hA : A' * Q = Q * A) (hB : B' * Q = Q * B) (hv : v' = Q.mulVec v)
    (hAF : ∀ i j, A' i j ∈ F) (hBF : ∀ i j, B' i j ∈ F) (hvF : ∀ i, v' i ∈ F) :
    ∀ i j, Q i j ∈ F := by
  intro i j
  rw [recover_frame r s A B A' B' Q v v' hb hA hB hv i j]
  exact mulVec_mem F _ _ (MatrixSubfield.mul_mem F _ _
    (pow_mem F A' hAF (r j)) (pow_mem F B' hBF (s j))) hvF i

theorem original_mem (F : IntermediateField K L)
    (A B A' B' : Matrix ι ι L) (Q : (Matrix ι ι L)ˣ) (v v' : ι → L)
    (hA : A' * (Q : Matrix ι ι L) = (Q : Matrix ι ι L) * A)
    (hB : B' * (Q : Matrix ι ι L) = (Q : Matrix ι ι L) * B)
    (hv : v' = (Q : Matrix ι ι L).mulVec v)
    (hQF : ∀ i j, (Q : Matrix ι ι L) i j ∈ F)
    (hAF : ∀ i j, A' i j ∈ F) (hBF : ∀ i j, B' i j ∈ F) (hvF : ∀ i, v' i ∈ F) :
    (∀ i j, A i j ∈ F) ∧ (∀ i j, B i j ∈ F) ∧ (∀ i, v i ∈ F) := by
  have hQiF := MatrixSubfield.unit_inv_mem F Q hQF
  have he (M M' : Matrix ι ι L) (hM : M' * (Q : Matrix ι ι L) = (Q : Matrix ι ι L) * M) :
      M = (↑Q⁻¹ : Matrix ι ι L) * (M' * (Q : Matrix ι ι L)) := by
    rw [hM, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [he A A' hA]
    exact MatrixSubfield.mul_mem F _ _ hQiF (MatrixSubfield.mul_mem F _ _ hAF hQF)
  · rw [he B B' hB]
    exact MatrixSubfield.mul_mem F _ _ hQiF (MatrixSubfield.mul_mem F _ _ hBF hQF)
  · have hev : v = (↑Q⁻¹ : Matrix ι ι L).mulVec v' := by
      rw [hv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [hev]
    exact mulVec_mem F _ _ hQiF hvF

end PermanentBorder.CyclicFrames

namespace PermanentBorder.CyclicFrames
open Matrix
variable {K L ι : Type*} [Field K] [Field L] [Fintype ι] [DecidableEq ι]

theorem conjugation_intertwines (Q : (Matrix ι ι L)ˣ) (A : Matrix ι ι L) :
    conjugation Q A * (Q : Matrix ι ι L) = (Q : Matrix ι ι L) * A := by
  change ((Q : Matrix ι ι L) * A * (↑Q⁻¹ : Matrix ι ι L)) *
    (Q : Matrix ι ι L) = (Q : Matrix ι ι L) * A
  rw [mul_assoc, Units.inv_mul, mul_one]

end PermanentBorder.CyclicFrames
namespace PermanentBorder.PunctualCharts
open Matrix Algebra CyclicFrames
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Infinite K]

theorem generated_chart_field_bound {n : ℕ} (hn : 0 < n)
    (r s : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) L) (v : Fin n → L)
    (hA : IsNilpotent A) (hB : IsNilpotent B) (hAB : A * B = B * A)
    (hb : MonomialBasis r s A B v)
    (hgen : IntermediateField.adjoin K (tripleEntries A B v) = ⊤) :
    Algebra.trdeg K L ≤ (n - 1 : ℕ) := by
  classical
  let T := GenericMatrix.FunctionField L n
  let f := algebraMap L T
  let Q := GenericMatrix.genericUnit L n
  let A₀ : Matrix (Fin n) (Fin n) T := A.map f
  let B₀ : Matrix (Fin n) (Fin n) T := B.map f
  let v₀ : Fin n → T := f ∘ v
  let A' := conjugation Q A₀
  let B' := conjugation Q B₀
  let v' := (Q : Matrix (Fin n) (Fin n) T).mulVec v₀
  have hA' : IsNilpotent A' := (hA.map f.mapMatrix).map (conjugation Q)
  have hB' : IsNilpotent B' := (hB.map f.mapMatrix).map (conjugation Q)
  have hAB' : A' * B' = B' * A' := by
    exact ((Commute.map (show Commute A B from hAB) f.mapMatrix).map (conjugation Q)).eq
  obtain ⟨F, hF, hAF, hBF⟩ := CommutingPairs.nilpotent_pair_field_bound (K := K) hn A' B'
    hA' hB' hAB'
  obtain ⟨E, hFE, hE, hvE⟩ := FieldParameters.extend_field F hF v'
  have hAE : ∀ i j, A' i j ∈ E := fun i j => hFE (hAF i j)
  have hBE : ∀ i j, B' i j ∈ E := fun i j => hFE (hBF i j)
  have hb₀ : MonomialBasis r s A₀ B₀ v₀ := hb.map f
  have hAQ := conjugation_intertwines Q A₀
  have hBQ := conjugation_intertwines Q B₀
  have hQE : ∀ i j, (Q : Matrix (Fin n) (Fin n) T) i j ∈ E :=
    frame_mem E r s A₀ B₀ A' B' Q v₀ v' hb₀ hAQ hBQ rfl hAE hBE hvE
  obtain ⟨hA₀E, hB₀E, hv₀E⟩ := original_mem E A₀ B₀ A' B' Q v₀ v' hAQ hBQ
    rfl hQE hAE hBE hvE
  have hc : ∀ x : L, algebraMap L T x ∈ E := by
    have hle : IntermediateField.adjoin K (tripleEntries A B v) ≤
        IntermediateField.comap (IsScalarTower.toAlgHom K L T) E := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro x ((⟨⟨i,j⟩, rfl⟩ | ⟨⟨i,j⟩, rfl⟩) | ⟨i, rfl⟩)
      · exact hA₀E i j
      · exact hB₀E i j
      · exact hv₀E i
    rw [hgen] at hle
    exact fun x => hle (IntermediateField.mem_top)
  have htop : E = ⊤ := GenericMatrix.field_eq_top_of_mem L n K E hc (by
    simpa only [Q, GenericMatrix.genericUnit_val] using hQE)
  have hT : Algebra.trdeg K T ≤ (n * n - 1 + n : ℕ) := by
    rw [htop, (IntermediateField.topEquiv (F := K) (E := T)).trdeg_eq] at hE
    exact hE
  have : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).mpr
    (algebraMap K L).injective
  have : FaithfulSMul L T := (faithfulSMul_iff_algebraMap_injective L T).mpr
    (algebraMap L T).injective
  rw [← trdeg_add_eq K L, GenericMatrix.relative_trdeg] at hT
  have heq : n * n - 1 + n = (n - 1) + n * n := by
    have hp : 0 < n * n := Nat.mul_pos hn hn
    omega
  rw [heq, Nat.cast_add] at hT
  exact (Cardinal.add_le_add_iff_of_lt_aleph0 (Cardinal.natCast_lt_aleph0)).mp hT

end PermanentBorder.PunctualCharts

namespace PermanentBorder.PunctualCharts
open Matrix Algebra CyclicFrames
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Infinite K]

theorem chart_field_bound {n : ℕ} (hn : 0 < n)
    (r s : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) L) (v : Fin n → L)
    (hA : IsNilpotent A) (hB : IsNilpotent B) (hAB : A * B = B * A)
    (hb : MonomialBasis r s A B v) :
    ∃ F : IntermediateField K L,
      Algebra.trdeg K F ≤ (n - 1 : ℕ) ∧
      (∀ i j, A i j ∈ F) ∧ (∀ i j, B i j ∈ F) ∧ (∀ i, v i ∈ F) := by
  classical
  let F := IntermediateField.adjoin K (tripleEntries A B v)
  have hAF : ∀ i j, A i j ∈ F := fun i j => IntermediateField.subset_adjoin K _
    (Or.inl (Or.inl (Set.mem_range_self (i,j))))
  have hBF : ∀ i j, B i j ∈ F := fun i j => IntermediateField.subset_adjoin K _
    (Or.inl (Or.inr (Set.mem_range_self (i,j))))
  have hvF : ∀ i, v i ∈ F := fun i => IntermediateField.subset_adjoin K _
    (Or.inr (Set.mem_range_self i))
  let A₀ : Matrix (Fin n) (Fin n) F := fun i j => ⟨A i j, hAF i j⟩
  let B₀ : Matrix (Fin n) (Fin n) F := fun i j => ⟨B i j, hBF i j⟩
  let v₀ : Fin n → F := fun i => ⟨v i, hvF i⟩
  let f := (algebraMap F L).mapMatrix (m := Fin n)
  have hf : Function.Injective f := by
    intro P Q h
    ext i j
    exact congrFun (congrFun h i) j
  have hfA : f A₀ = A := rfl
  have hfB : f B₀ = B := rfl
  have hA₀ : IsNilpotent A₀ := by
    obtain ⟨d, hd⟩ := hA
    refine ⟨d, hf ?_⟩
    rw [map_pow, hfA, map_zero, hd]
  have hB₀ : IsNilpotent B₀ := by
    obtain ⟨d, hd⟩ := hB
    refine ⟨d, hf ?_⟩
    rw [map_pow, hfB, map_zero, hd]
  have hAB₀ : A₀ * B₀ = B₀ * A₀ := by
    apply hf
    rw [map_mul, map_mul, hfA, hfB, hAB]
  have hb₀ : MonomialBasis r s A₀ B₀ v₀ := by
    intro i
    ext j
    have he := congrFun (hb i) j
    have hh := (algebraMap F L).map_mulVec (A₀ ^ r i * B₀ ^ s i) v₀ j
    have hp : (A₀ ^ r i * B₀ ^ s i).map (algebraMap F L) = A ^ r i * B ^ s i := by
      change f (A₀ ^ r i * B₀ ^ s i) = _
      rw [map_mul, map_pow, map_pow, hfA, hfB]
    rw [hp] at hh
    change algebraMap F L ((A₀ ^ r i * B₀ ^ s i).mulVec v₀ j) = _
    rw [hh]
    change ((A ^ r i * B ^ s i).mulVec v) j = _
    rw [he]
    by_cases hij : j = i
    · subst j
      simp
    · simp [hij]
  have hgen : IntermediateField.adjoin K (tripleEntries A₀ B₀ v₀) = ⊤ := by
    apply IntermediateField.map_injective F.val
    rw [IntermediateField.adjoin_map]
    have him : F.val '' tripleEntries A₀ B₀ v₀ = tripleEntries A B v := by
      simp only [tripleEntries, Set.image_union, ← Set.range_comp]
      rfl
    rw [him]
    change F = (⊤ : IntermediateField K F).map F.val
    ext x
    constructor
    · intro hx
      exact ⟨⟨x,hx⟩, IntermediateField.mem_top, rfl⟩
    · rintro ⟨x, _, rfl⟩
      exact x.property
  exact ⟨F, generated_chart_field_bound hn r s A₀ B₀ v₀ hA₀ hB₀ hAB₀ hb₀ hgen,
    hAF, hBF, hvF⟩

end PermanentBorder.PunctualCharts

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.CurveParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.CurveParameters
open Matrix Algebra MvPolynomial CyclicFrames
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Infinite K]

omit [Infinite K] in

theorem support_field_bound (p : MvPolynomial (Fin 2) K) (hp : p ≠ 0)
    (x : Fin 2 → L) (hx : aeval x p = 0) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) ≤ (1 : Cardinal) := by
  have h := ParameterBounds.field_adjoin_trdeg_lt_of_relation x p hp hx
  apply Cardinal.lt_natCast_add_one_iff.mp
  convert h using 1
  norm_num

theorem extend_by_chart {p₀ n : ℕ} (F : IntermediateField K L)
    (hF : Algebra.trdeg K F ≤ (p₀ : Cardinal))
    (p : MvPolynomial (Fin 2) K) (hp : p ≠ 0)
    (x : Fin 2 → L) (hx : aeval x p = 0) (hn : 0 < n)
    (r s : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) L) (v : Fin n → L)
    (hA : IsNilpotent A) (hB : IsNilpotent B) (hAB : A * B = B * A)
    (hb : MonomialBasis r s A B v) :
    ∃ E : IntermediateField K L,
      F ≤ E ∧ Algebra.trdeg K E ≤ (p₀+n : ℕ) ∧
      (∀ i, x i ∈ E) ∧ (∀ i j, A i j ∈ E) ∧
      (∀ i j, B i j ∈ E) ∧ (∀ i, v i ∈ E) := by
  have : Infinite F := Infinite.of_injective (algebraMap K F) (algebraMap K F).injective
  let pF := MvPolynomial.map (algebraMap K F) p
  have hpF : pF ≠ 0 := by
    exact fun h => hp ((MvPolynomial.map_injective _ (algebraMap K F).injective)
      (by simpa only [map_zero] using h))
  have hxF : aeval (R := F) x pF = 0 := by
    change eval₂ (algebraMap F L) x (MvPolynomial.map (algebraMap K F) p) = 0
    rw [MvPolynomial.eval₂_map, ← IsScalarTower.algebraMap_eq K F L]
    exact hx
  let T := IntermediateField.adjoin F (Set.range x)
  have : IsScalarTower K T L := IsScalarTower.of_algebraMap_eq' (by ext z; rfl)
  have : Infinite T := Infinite.of_injective (algebraMap K T) (algebraMap K T).injective
  have hT : Algebra.trdeg F T ≤ (1 : Cardinal) := support_field_bound pF hpF x hxF
  obtain ⟨U,hU,hAU,hBU,hvU⟩ := PunctualCharts.chart_field_bound (K := T)
    hn r s A B v hA hB hAB hb
  have : FaithfulSMul T U := (faithfulSMul_iff_algebraMap_injective T U).mpr
    (algebraMap T U).injective
  let E := U.restrictScalars K
  have : FaithfulSMul K F := (faithfulSMul_iff_algebraMap_injective K F).mpr
    (algebraMap K F).injective
  have : FaithfulSMul F T := (faithfulSMul_iff_algebraMap_injective F T).mpr
    (algebraMap F T).injective
  have : FaithfulSMul K T := (faithfulSMul_iff_algebraMap_injective K T).mpr
    (algebraMap K T).injective
  have hFE : F ≤ E := by
    intro z hz
    exact U.algebraMap_mem (algebraMap F T ⟨z,hz⟩)
  have hxE : ∀ i, x i ∈ E := fun i =>
    U.algebraMap_mem ⟨x i, IntermediateField.subset_adjoin F _ (Set.mem_range_self i)⟩
  refine ⟨E,hFE,?_,hxE,hAU,hBU,hvU⟩
  calc
    Algebra.trdeg K E = Algebra.trdeg K T + Algebra.trdeg T U :=
      (trdeg_add_eq K T (A := U)).symm
    _ = (Algebra.trdeg K F + Algebra.trdeg F T) + Algebra.trdeg T U := by
      rw [trdeg_add_eq K F (A := T)]
    _ ≤ ((p₀ : Cardinal) + 1) + (n-1 : ℕ) := add_le_add (add_le_add hF hT) hU
    _ = (p₀+n : ℕ) := by
      rw [add_assoc, ← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_of_le hn, ← Nat.cast_add]

end PermanentBorder.CurveParameters
namespace PermanentBorder.CurveParameters
open Matrix Algebra MvPolynomial CyclicFrames
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

namespace LocalChart
variable {p : MvPolynomial (Fin 2) K}

theorem InField.mono {D : LocalChart (L := L) p} {F E : IntermediateField K L}
    (h : D.InField F) (hFE : F ≤ E) : D.InField E :=
  ⟨fun i => hFE (h.1 i),fun i j => hFE (h.2.1 i j),
    fun i j => hFE (h.2.2.1 i j),fun i => hFE (h.2.2.2 i)⟩

theorem extend [Infinite K] (D : LocalChart (L := L) p) (hp : p ≠ 0)
    {b : ℕ} (F : IntermediateField K L) (hF : Algebra.trdeg K F ≤ (b : Cardinal)) :
    ∃ E : IntermediateField K L,
      F ≤ E ∧ Algebra.trdeg K E ≤ (b + D.length : ℕ) ∧ D.InField E :=
  extend_by_chart F hF p hp D.support D.on_curve D.positive D.r D.s D.A D.B D.v
    D.nilA D.nilB D.commutes D.basis_eq

end LocalChart

theorem extend_by_finite_family [Infinite K] {κ : Type*}
    {p : MvPolynomial (Fin 2) K} (hp : p ≠ 0)
    (D : κ → LocalChart (L := L) p) (t : Finset κ)
    {b : ℕ} (F : IntermediateField K L) (hF : Algebra.trdeg K F ≤ (b : Cardinal)) :
    ∃ E : IntermediateField K L,
      F ≤ E ∧ Algebra.trdeg K E ≤ (b + ∑ i ∈ t, (D i).length : ℕ) ∧
      ∀ i ∈ t, (D i).InField E := by
  classical
  induction t using Finset.induction_on generalizing b F with
  | empty =>
    exact ⟨F,le_rfl,by simpa using hF,by simp⟩
  | @insert i t hi ih =>
    obtain ⟨T,hFT,hT,hDT⟩ := (D i).extend hp F hF
    obtain ⟨E,hTE,hE,hDE⟩ := ih T hT
    refine ⟨E,hFT.trans hTE,?_,?_⟩
    · simpa only [Finset.sum_insert hi, Nat.add_assoc] using hE
    · intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjt
      · subst j
        exact hDT.mono hTE
      · exact hDE j hjt

end PermanentBorder.CurveParameters

namespace PermanentBorder.FiniteAlgebras
open Module
variable (L R : Type*) [Field L] [CommRing R] [Algebra L R] [Module.Finite L R]

include L in

theorem artinian : IsArtinianRing R := isArtinian_of_tower L inferInstance

end PermanentBorder.FiniteAlgebras

namespace PermanentBorder.FinitePlaneFrames
open MvPolynomial Module Matrix
variable {L S : Type*} [Field L] [CommRing S] [Algebra L S]

theorem action_on_unit {n : ℕ} (b : Basis (Fin n) L S) (x : S) :
    (representation b x).mulVec (unitVector b) = b.equivFun x := by
  change ((LinearMap.toMatrix b b) (Algebra.lmul L S x)).mulVec
    (fun i => b.repr 1 i) = _
  rw [LinearMap.toMatrix_mulVec_repr]
  simp only [Module.Basis.equivFun_apply]
  change (fun i => b.repr (x * 1) i) = _
  rw [mul_one]

theorem exists_monomial_basis [Module.Finite L S]
    (q : MvPolynomial (Fin 2) L →ₐ[L] S) (hq : Function.Surjective q) :
    ∃ (b : Basis (Fin (finrank L S)) L S) (r s : Fin (finrank L S) → ℕ),
      ∀ i, b i = q (X 0 ^ r i * X 1 ^ s i) := by
  classical
  let μ := q.toLinearMap ∘ (MvPolynomial.basisMonomials (Fin 2) L)
  have hsp : Submodule.span L (Set.range μ) = ⊤ := by
    rw [show Set.range μ = q.toLinearMap '' Set.range (MvPolynomial.basisMonomials (Fin 2) L) from
      Set.range_comp _ _]
    rw [← Submodule.map_span, (MvPolynomial.basisMonomials (Fin 2) L).span_eq,
      Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hq
  have hdim : finrank L (Submodule.span L (Set.range μ)) = finrank L S := by
    rw [hsp, finrank_top]
  obtain ⟨f,hmem,hspan,hind⟩ : ∃ f : Fin (finrank L S) → S,
      (∀ i, f i ∈ Set.range μ) ∧ Submodule.span L (Set.range f) = ⊤ ∧
        LinearIndependent L f := by
    have he := Submodule.exists_fun_fin_finrank_span_eq L (Set.range μ)
    rw [hdim] at he
    simpa only [hsp] using he
  choose e he using hmem
  let b := Basis.mk hind (le_of_eq hspan.symm)
  refine ⟨b,fun i => e i 0,fun i => e i 1,?_⟩
  intro i
  rw [show b i = f i from Basis.mk_apply hind (le_of_eq hspan.symm) i, ← he i]
  change q (monomial (e i) 1) = _
  congr 1
  rw [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_two]
  · simp

end PermanentBorder.FinitePlaneFrames
namespace PermanentBorder.FiniteAlgebras
open Module MvPolynomial Matrix FinitePlaneFrames
variable (L R : Type*) [Field L] [CommRing R] [Algebra L R]
  [Module.Finite L R] [IsAlgClosed L]

theorem shiftedLocalHom_surjective (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (hq : Function.Surjective q) (m : MaximalSpectrum R) (e : ℕ) :
    Function.Surjective (shiftedLocalHom L R q m e) :=
  Ideal.Quotient.mk_surjective.comp (hq.comp
    (PlaneTranslations.equivalence (-supportPoint L R q m)).surjective)

theorem local_monomial_chart (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (hq : Function.Surjective q) (m : MaximalSpectrum R) (e : ℕ) :
    ∃ (b : Basis (Fin (finrank L (R ⧸ m.asIdeal ^ e))) L (R ⧸ m.asIdeal ^ e))
      (r s : Fin (finrank L (R ⧸ m.asIdeal ^ e)) → ℕ),
      CyclicFrames.MonomialBasis r s
        (representation b (shiftedLocalHom L R q m e (X 0)))
        (representation b (shiftedLocalHom L R q m e (X 1))) (unitVector b) := by
  obtain ⟨b,r,s,hb⟩ := FinitePlaneFrames.exists_monomial_basis
    (shiftedLocalHom L R q m e) (shiftedLocalHom_surjective L R q hq m e)
  refine ⟨b,r,s,?_⟩
  intro i
  have h : (representation b (shiftedLocalHom L R q m e (X 0))) ^ r i *
      (representation b (shiftedLocalHom L R q m e (X 1))) ^ s i =
      representation b (shiftedLocalHom L R q m e (X 0 ^ r i * X 1 ^ s i)) := by
    simp only [map_mul, map_pow]
  rw [h, action_on_unit, ← hb i]
  ext j
  simpa only [Pi.single_apply, eq_comm] using b.equivFun_self i j

end PermanentBorder.FiniteAlgebras
namespace PermanentBorder.FiniteAlgebras
open Module
variable (L R : Type*) [Field L] [CommRing R] [Algebra L R] [Module.Finite L R]

theorem exists_canonical_local_power_decomposition :
    ∃ e : ℕ, 0 < e ∧ ∃ E : R ≃ₐ[L] ∀ m : MaximalSpectrum R, R ⧸ m.asIdeal ^ e,
      ∀ x m, E x m = Ideal.Quotient.mk (m.asIdeal ^ e) x := by
  have : IsArtinianRing R := artinian L R
  obtain ⟨e,he⟩ := IsArtinianRing.isNilpotent_nilradical (R := R)
  have he' : nilradical R ^ (e+1) = ⊥ := by rw [pow_succ, he]; simp
  let E := ((AlgEquiv.quotientBot R R).symm.trans
    ((Ideal.quotientEquivAlgOfEq R he'.symm).trans
      (IsArtinianRing.quotNilradicalPowEquivPi R (e+1)))).restrictScalars L
  exact ⟨e+1, Nat.zero_lt_succ e, E, fun _ _ => rfl⟩

end PermanentBorder.FiniteAlgebras
namespace PermanentBorder.BasisFieldRecovery
open Module Matrix
variable {K L S ι κ : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup S] [Module L S] [Fintype ι] [Fintype κ]

omit [Fintype ι] in

theorem repr_mem (F : IntermediateField K L) (b : Basis ι L S) (c : Basis κ L S)
    (hbc : ∀ i j, c.repr (b j) i ∈ F) (x : S) (hx : ∀ i, c.repr x i ∈ F) :
    ∀ j, b.repr x j ∈ F := by
  classical
  let e := b.indexEquiv c
  let b' := b.reindex e
  let P : (Matrix κ κ L)ˣ :=
    ⟨c.toMatrix b', b'.toMatrix c,
      c.toMatrix_mul_toMatrix_flip b', b'.toMatrix_mul_toMatrix_flip c⟩
  have hP : ∀ i j, (P : Matrix κ κ L) i j ∈ F := by
    intro i j
    simpa only [P, Units.val_mk, b', Basis.toMatrix_apply, Basis.reindex_apply] using hbc i (e.symm j)
  have hI := MatrixSubfield.unit_inv_mem F P hP
  have hb'x : ∀ j, b'.repr x j ∈ F := by
    intro j
    rw [← c.toMatrix_mulVec_repr b' x]
    exact F.sum_mem fun i _ => F.mul_mem (hI j i) (hx i)
  intro j
  have h := hb'x (e j)
  simpa only [b', Basis.repr_reindex, Finsupp.equivMapDomain_apply,
    Equiv.symm_apply_apply, Finsupp.mapDomain_apply e.injective] using h

end PermanentBorder.BasisFieldRecovery

namespace PermanentBorder.MatrixSubfield
open Matrix
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype ι] [DecidableEq ι]

theorem pow_mem (F : IntermediateField K L) (A : Matrix ι ι L)
    (hA : ∀ i j, A i j ∈ F) (r : ℕ) : ∀ i j, (A ^ r) i j ∈ F := by
  induction r with
  | zero => intro i j; simp only [pow_zero, one_apply]; split <;> simp
  | succ r ih => simpa only [pow_succ] using mul_mem F (A^r) A ih hA

omit [DecidableEq ι] in
theorem mulVec_mem (F : IntermediateField K L) (A : Matrix ι ι L) (v : ι → L)
    (hA : ∀ i j, A i j ∈ F) (hv : ∀ i, v i ∈ F) :
    ∀ i, (A.mulVec v) i ∈ F := by
  intro i
  exact F.sum_mem fun j _ => F.mul_mem (hA i j) (hv j)

end PermanentBorder.MatrixSubfield

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.QuotientFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.FinitePlaneFrames
open Module Matrix MvPolynomial
variable {K L S : Type*} [Field K] [Field L] [Algebra K L]
  [CommRing S] [Algebra L S]

theorem monomial_coordinates_mem {n : ℕ} (F : IntermediateField K L)
    (q : MvPolynomial (Fin 2) L →ₐ[L] S) (b : Basis (Fin n) L S)
    (hA : ∀ i j, representation b (q (X 0)) i j ∈ F)
    (hB : ∀ i j, representation b (q (X 1)) i j ∈ F)
    (hv : ∀ i, unitVector b i ∈ F) (r s : ℕ) :
    ∀ i, b.repr (q (X 0 ^ r * X 1 ^ s)) i ∈ F := by
  have h := MatrixSubfield.mulVec_mem F
    ((representation b (q (X 0))) ^ r * (representation b (q (X 1))) ^ s)
    (unitVector b)
    (MatrixSubfield.mul_mem F _ _ (MatrixSubfield.pow_mem F _ hA r)
      (MatrixSubfield.pow_mem F _ hB s)) hv
  have he : (representation b (q (X 0))) ^ r * (representation b (q (X 1))) ^ s =
      representation b (q (X 0 ^ r * X 1 ^ s)) := by simp only [map_mul,map_pow]
  simpa only [he, action_on_unit, Basis.equivFun_apply] using h

theorem unshifted_representation_mem {n : ℕ} (F : IntermediateField K L)
    (b : Basis (Fin n) L S) (x : S) (a : L) (ha : a ∈ F)
    (h : ∀ i j, representation b (x - algebraMap L S a) i j ∈ F) :
    ∀ i j, representation b x i j ∈ F := by
  have he : representation b x = representation b (x - algebraMap L S a) +
      algebraMap L (Matrix (Fin n) (Fin n) L) a := by
    rw [map_sub, AlgHom.commutes, sub_add_cancel]
  intro i j
  rw [he, Matrix.add_apply]
  refine F.add_mem (h i j) ?_
  change (Matrix.scalar (Fin n) a) i j ∈ F
  by_cases hij : i = j
  · subst j; simpa using ha
  · simp [Matrix.scalar, Matrix.diagonal, hij]

end PermanentBorder.FinitePlaneFrames
namespace PermanentBorder.FiniteAlgebras
open Module MvPolynomial Matrix FinitePlaneFrames CurveParameters
universe u
variable {K L : Type u} {R : Type u} [Field K] [Field L] [Algebra K L]
  [CommRing R] [Algebra L R] [Module.Finite L R] [IsAlgClosed L]

theorem local_monomial_coordinates_mem (F : IntermediateField K L)
    (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (p : MvPolynomial (Fin 2) K) (hpq : q (p.map (algebraMap K L)) = 0)
    (m : MaximalSpectrum R) (e : ℕ) (he : 0 < e)
    (b : Basis (Fin (finrank L (R ⧸ m.asIdeal ^ e))) L (R ⧸ m.asIdeal ^ e))
    (r s : Fin (finrank L (R ⧸ m.asIdeal ^ e)) → ℕ)
    (hb : CyclicFrames.MonomialBasis r s
      (representation b (shiftedLocalHom L R q m e (X 0)))
      (representation b (shiftedLocalHom L R q m e (X 1))) (unitVector b))
    (hF : (localChart q p hpq m e he b r s hb).InField F) (r' s' : ℕ) :
    ∀ i, b.repr (localHom L R q m e (X 0 ^ r' * X 1 ^ s')) i ∈ F := by
  apply monomial_coordinates_mem F (localHom L R q m e) b _ _ hF.2.2.2 r' s'
  · apply unshifted_representation_mem F b _ (supportPoint L R q m 0) (hF.1 0)
    have h : ∀ i j, representation b (shiftedLocalHom L R q m e (X 0)) i j ∈ F := hF.2.1
    simpa only [shiftedLocalHom_X] using h
  · apply unshifted_representation_mem F b _ (supportPoint L R q m 1) (hF.1 1)
    have h : ∀ i j, representation b (shiftedLocalHom L R q m e (X 1)) i j ∈ F := hF.2.2.1
    simpa only [shiftedLocalHom_X] using h

end PermanentBorder.FiniteAlgebras
namespace PermanentBorder.CurveQuotientParameters
open Module Matrix MvPolynomial FiniteAlgebras FinitePlaneFrames CurveParameters
universe u
variable {K L R : Type u} [Field K] [Field L] [Algebra K L]
  [Infinite K] [IsAlgClosed L] [CommRing R] [Algebra L R] [Module.Finite L R]

theorem chart_field_bound (p : MvPolynomial (Fin 2) K) (hp : p ≠ 0)
    (q : MvPolynomial (Fin 2) L →ₐ[L] R) (hq : Function.Surjective q)
    (hpq : q (p.map (algebraMap K L)) = 0)
    {n : ℕ} (b₀ : Basis (Fin n) L R) (r₀ s₀ : Fin n → ℕ)
    (hb₀ : ∀ i, b₀ i = q (X 0 ^ r₀ i * X 1 ^ s₀ i)) :
    ∃ F : IntermediateField K L,
      Algebra.trdeg K F ≤ (finrank L R : Cardinal) ∧
      (∀ i j, representation b₀ (q (X 0)) i j ∈ F) ∧
      (∀ i j, representation b₀ (q (X 1)) i j ∈ F) ∧
      (∀ i, unitVector b₀ i ∈ F) := by
  classical
  have : IsArtinianRing R := artinian L R
  let _ : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  obtain ⟨e, he, E, hE⟩ := exists_canonical_local_power_decomposition L R
  choose b r s hb using fun m => local_monomial_chart L R q hq m e
  let D : MaximalSpectrum R → LocalChart (L := L) p := fun m =>
    localChart q p hpq m e he (b m) (r m) (s m) (hb m)
  have hbot : Algebra.trdeg K (⊥ : IntermediateField K L) ≤ (0 : Cardinal) := by
    rw [trdeg_eq_zero]
  obtain ⟨F, _, hF, hDF⟩ := extend_by_finite_family hp D Finset.univ
    (⊥ : IntermediateField K L) hbot
  have hdF : ∀ m, (D m).InField F := fun m => hDF m (Finset.mem_univ m)
  have hlen : finrank L R = ∑ m : MaximalSpectrum R, finrank L (R ⧸ m.asIdeal ^ e) := by
    rw [E.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  have hdeg : Algebra.trdeg K F ≤ (finrank L R : Cardinal) := by
    rw [hlen]
    simpa only [D, localChart, Nat.zero_add] using hF
  let w : R ≃ₗ[L] ((m : MaximalSpectrum R) × Fin (finrank L (R ⧸ m.asIdeal ^ e))) → L :=
    E.toLinearEquiv.trans ((LinearEquiv.piCongrRight fun m => (b m).equivFun).trans
      (LinearEquiv.piCurry L (fun (m : MaximalSpectrum R) (_ : Fin (finrank L (R ⧸ m.asIdeal ^ e))) => L)).symm)
  let c := Basis.ofEquivFun w
  have hmon (a d : ℕ) : ∀ i, c.repr (q (X 0 ^ a * X 1 ^ d)) i ∈ F := by
    intro i
    change (b i.1).repr (E (q (X 0 ^ a * X 1 ^ d)) i.1) i.2 ∈ F
    rw [hE]
    exact local_monomial_coordinates_mem F q p hpq i.1 e he
      (b i.1) (r i.1) (s i.1) (hb i.1) (hdF i.1) a d i.2
  have hbc : ∀ i j, c.repr (b₀ j) i ∈ F := by
    intro i j
    rw [hb₀]
    exact hmon (r₀ j) (s₀ j) i
  have hmon₀ (a d : ℕ) : ∀ i, b₀.repr (q (X 0 ^ a * X 1 ^ d)) i ∈ F :=
    BasisFieldRecovery.repr_mem F b₀ c hbc _ (hmon a d)
  refine ⟨F,hdeg,?_,?_,?_⟩
  · intro i j
    rw [show representation b₀ (q (X 0)) i j = b₀.repr (q (X 0) * b₀ j) i from
      LinearMap.toMatrixAlgEquiv_apply b₀ (Algebra.lmul L R (q (X 0))) i j]
    have h : q (X 0) * b₀ j = q (X 0 ^ (r₀ j + 1) * X 1 ^ s₀ j) := by
      rw [hb₀, ← map_mul]
      congr 1
      ring
    rw [h]
    exact hmon₀ (r₀ j+1) (s₀ j) i
  · intro i j
    rw [show representation b₀ (q (X 1)) i j = b₀.repr (q (X 1) * b₀ j) i from
      LinearMap.toMatrixAlgEquiv_apply b₀ (Algebra.lmul L R (q (X 1))) i j]
    have h : q (X 1) * b₀ j = q (X 0 ^ r₀ j * X 1 ^ (s₀ j+1)) := by
      rw [hb₀, ← map_mul]
      congr 1
      ring
    rw [h]
    exact hmon₀ (r₀ j) (s₀ j+1) i
  · intro i
    simpa only [pow_zero, one_mul, map_one, unitVector, Basis.equivFun_apply] using hmon₀ 0 0 i

end PermanentBorder.CurveQuotientParameters

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.PlaneHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K : Type*} [Field K]

lemma finrank_piece (d : ℤ) : Module.finrank K (H (K := K) d) = (d+1).toNat := by
  rw [(pieceCoordinates d).finrank_eq, Module.finrank_pi]
  by_cases hd : 0 ≤ d
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hd
    rw [Fintype.card_congr (degreeIndexEquiv n), Fintype.card_fin]
    omega
  · have : IsEmpty (DegreeIndex (Fin 2) d) := ⟨fun s => by
      have hs : (0 : ℤ) ≤ s.val.degree := by positivity
      exact hd (s.property ▸ hs)⟩
    have hc : Fintype.card (DegreeIndex (Fin 2) d) = 0 := Fintype.card_eq_zero
    rw [hc]
    omega

end PermanentBorder.PlaneHilbert

namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K : Type*} [Field K]

lemma varMul_injective (i : Fin 2) (n : ℕ) :
    Function.Injective (varMul (K := K) i n) := by
  intro p q h
  apply Subtype.ext
  exact mul_left_cancel₀ (X_ne_zero i) (congrArg Subtype.val h)

lemma piece_degreeOf_le {n : ℕ} (p : H (K := K) (n : ℤ)) (i : Fin 2) :
    p.val.degreeOf i ≤ n :=
  (degreeOf_le_totalDegree _ _).trans (intWeight_homogeneous p.property).totalDegree_le

theorem exists_varMul_outside {n : ℕ} (W : Submodule K (H (K := K) (n : ℤ)))
    (hW : W ≠ ⊥) :
    ∃ p ∈ W, varMul 0 n p ∉ W.map (varMul 1 n) := by
  classical
  obtain ⟨p,hp,hp0⟩ := W.ne_bot_iff.mp hW
  have hpv : p.val ≠ 0 := fun h => hp0 (Subtype.ext h)
  let P : ℕ → Prop := fun j => ∃ v ∈ W, v.val ≠ 0 ∧ v.val.degreeOf 0 = j
  have he : P (p.val.degreeOf 0) := ⟨p,hp,hpv,rfl⟩
  have hb := piece_degreeOf_le p 0
  obtain ⟨q,hq,hq0,hqm⟩ := Nat.findGreatest_spec hb he
  refine ⟨q,hq,?_⟩
  rintro ⟨z,hz,heq⟩
  have hz0 : z.val ≠ 0 := by
    intro h
    have hh := congrArg Subtype.val heq
    change X 1 * z.val = X 0 * q.val at hh
    rw [h,mul_zero] at hh
    exact (mul_ne_zero (X_ne_zero 0) hq0) hh.symm
  have hzm : z.val.degreeOf 0 ≤ Nat.findGreatest P n :=
    Nat.le_findGreatest (piece_degreeOf_le z 0) ⟨z,hz,hz0,rfl⟩
  have hh := congrArg (fun v : H (K := K) ((n+1 : ℕ) : ℤ) => v.val.degreeOf 0) heq
  change (X 1 * z.val).degreeOf 0 = (X 0 * q.val).degreeOf 0 at hh
  rw [mul_comm (X 1), degreeOf_mul_X_of_ne _ (by decide : (0 : Fin 2) ≠ 1),
    mul_comm (X 0), (degreeOf_mul_X_eq_degreeOf_add_one_iff 0 q.val).mpr hq0] at hh
  omega

lemma finrank_varMul_sup {n : ℕ} (W : Submodule K (H (K := K) (n : ℤ)))
    (hW : W ≠ ⊥) :
    Module.finrank K W + 1 ≤
      Module.finrank K ↥(W.map (varMul 0 n) ⊔ W.map (varMul 1 n)) := by
  obtain ⟨p,hp,hnot⟩ := exists_varMul_outside W hW
  have hlt : W.map (varMul 1 n) < W.map (varMul 0 n) ⊔ W.map (varMul 1 n) := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro heq
    apply hnot
    rw [heq]
    exact Submodule.mem_sup_left (Submodule.mem_map_of_mem hp)
  have hf := Submodule.finrank_strictMono hlt
  dsimp only at hf
  rw [← (Submodule.equivMapOfInjective (varMul 1 n) (varMul_injective 1 n) W).finrank_eq] at hf
  omega

end PermanentBorder.PlaneHilbert
namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K : Type*} [Field K]

lemma homogeneous_factor_right {a b : Plane (K := K)} {e t : ℤ}
    (ha : a.IsWeightedHomogeneous weight e) (h0 : a ≠ 0)
    (hab : (a*b).IsWeightedHomogeneous weight t) :
    b.IsWeightedHomogeneous weight (t-e) := by
  have hh := weightedHomogeneousComponent_eq_self hab
  rw [project_mul weight ha] at hh
  have hb : weightedHomogeneousComponent weight (t-e) b = b := mul_left_cancel₀ h0 hh
  rw [← hb]
  exact weightedHomogeneousComponent_mem weight b (t-e)

lemma mulPiece_injective {a : Plane (K := K)} {e : ℤ}
    (ha : a.IsWeightedHomogeneous weight e) (ha0 : a ≠ 0) (t : ℤ) :
    Function.Injective (mulPiece weight ha t) := by
  intro p q h
  apply Subtype.ext
  exact mul_left_cancel₀ ha0 (congrArg Subtype.val h)

lemma finrank_multiplicationRange {a : Plane (K := K)} {e : ℤ}
    (ha : a.IsWeightedHomogeneous weight e) (ha0 : a ≠ 0) (t : ℤ) :
    Module.finrank K (multiplicationRange ha t) = (t-e+1).toNat := by
  rw [LinearMap.finrank_range_of_inj (mulPiece_injective ha ha0 t), finrank_piece]

lemma multiplicationRange_inf {a b : Plane (K := K)} {e f : ℤ}
    (ha : a.IsWeightedHomogeneous weight e) (hb : b.IsWeightedHomogeneous weight f)
    (hb0 : b ≠ 0) (hab : IsRelPrime a b) (t : ℤ) :
    multiplicationRange ha t ⊓ multiplicationRange hb t =
      multiplicationRange (ha.mul hb) t := by
  ext p
  constructor
  · rintro ⟨⟨u,hu⟩,⟨v,hv⟩⟩
    have huv : a*u.val = b*v.val := congrArg Subtype.val (hu.trans hv.symm)
    have hd : b ∣ u.val := hab.symm.dvd_of_dvd_mul_left ⟨v,huv⟩
    obtain ⟨w,hw⟩ := hd
    have hbw : (b*w).IsWeightedHomogeneous weight (t-e) := hw ▸ u.property
    have hwh := homogeneous_factor_right hb hb0 hbw
    have hh : (t-e)-f = t-(e+f) := by ring
    rw [hh] at hwh
    refine ⟨⟨w,hwh⟩,?_⟩
    apply Subtype.ext
    change (a*b)*w = p.val
    rw [mul_assoc, ← hw]
    exact congrArg Subtype.val hu
  · rintro ⟨w,hw⟩
    have hbw : (b*w.val).IsWeightedHomogeneous weight (t-e) := by
      convert hb.mul w.property using 1; ring
    have haw : (a*w.val).IsWeightedHomogeneous weight (t-f) := by
      convert ha.mul w.property using 1; ring
    constructor
    · refine ⟨⟨b*w.val,hbw⟩,?_⟩
      apply Subtype.ext
      change a*(b*w.val) = p.val
      rw [← mul_assoc]
      exact congrArg Subtype.val hw
    · refine ⟨⟨a*w.val,haw⟩,?_⟩
      apply Subtype.ext
      change b*(a*w.val) = p.val
      rw [← mul_assoc, mul_comm b a]
      exact congrArg Subtype.val hw

end PermanentBorder.PlaneHilbert

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.FilteredPlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

lemma mem_filtered_succ (q : Plane (K := K) →ₐ[K] R) (n : ℕ) (z : R) :
    z ∈ filtered q (n+1) ↔ ∃ p : Plane (K := K), p.totalDegree ≤ n ∧ q p = z := by
  simp only [filtered,Submodule.mem_map,mem_restrictTotalDegree,AlgHom.toLinearMap_apply]

lemma filtered_mono (q : Plane (K := K) →ₐ[K] R) : Monotone (filtered q) := by
  apply monotone_nat_of_le_succ
  intro n
  cases n with
  | zero => exact bot_le
  | succ n =>
    intro z hz
    obtain ⟨p,hp,rfl⟩ := (mem_filtered_succ q n z).mp hz
    exact (mem_filtered_succ q (n+1) _).mpr ⟨p,by omega,rfl⟩

lemma homogeneous_mem_filtered (q : Plane (K := K) →ₐ[K] R) {n : ℕ}
    (p : H (K := K) (n : ℤ)) : q p.val ∈ filtered q (n+1) := by
  exact (mem_filtered_succ q n _).mpr
    ⟨p.val,(intWeight_homogeneous p.property).totalDegree_le,rfl⟩

lemma mul_X_filtered (q : Plane (K := K) →ₐ[K] R) (i : Fin 2) {n : ℕ}
    {z : R} (hz : z ∈ filtered q n) : q (X i) * z ∈ filtered q (n+1) := by
  cases n with
  | zero =>
    have hz0 : z = 0 := hz
    simp [hz0]
  | succ n =>
    obtain ⟨p,hp,rfl⟩ := (mem_filtered_succ q n z).mp hz
    apply (mem_filtered_succ q (n+1) _).mpr
    refine ⟨X i*p,?_,map_mul _ _ _⟩
    have hx : (X i : Plane (K := K)).totalDegree = 1 := totalDegree_X i
    exact (totalDegree_mul _ _).trans (by rw [hx]; omega)

lemma sub_topComponent_degree {p : Plane (K := K)} {n : ℕ}
    (hp : p.totalDegree ≤ n+1) : (p-(topComponent (n+1) p).val).totalDegree ≤ n := by
  classical
  apply Finset.sup_le
  intro s hs
  have hc : (p-(topComponent (n+1) p).val).coeff s ≠ 0 := mem_support_iff.mp hs
  change s.degree ≤ n
  by_contra! hn
  apply hc
  change (p-homogeneousComponent (n+1) p).coeff s = 0
  rw [coeff_sub,coeff_homogeneousComponent]
  by_cases he : s.degree = n+1
  · simp [he]
  · have hlt : p.totalDegree < s.degree := by omega
    simp [he,coeff_eq_zero_of_totalDegree_lt hlt]

lemma sub_topComponent_mem_filtered (q : Plane (K := K) →ₐ[K] R)
    {p : Plane (K := K)} {n : ℕ} (hp : p.totalDegree ≤ n) :
    q p - q (topComponent n p).val ∈ filtered q n := by
  cases n with
  | zero =>
    have he : p = (topComponent 0 p).val := by
      change p = homogeneousComponent 0 p
      rw [homogeneousComponent_zero]
      exact (totalDegree_eq_zero_iff_eq_C).mp (Nat.eq_zero_of_le_zero hp)
    rw [← he, sub_self]
    exact (filtered q 0).zero_mem
  | succ n =>
    exact (mem_filtered_succ q n _).mpr
      ⟨p-(topComponent (n+1) p).val,sub_topComponent_degree hp,map_sub _ _ _⟩

lemma mem_leadingRelations (q : Plane (K := K) →ₐ[K] R) (n : ℕ)
    (p : H (K := K) (n : ℤ)) : p ∈ leadingRelations q n ↔ q p.val ∈ filtered q n := by
  simp only [leadingRelations,LinearMap.mem_ker,leadingMap,LinearMap.comp_apply,
    Submodule.subtype_apply,AlgHom.toLinearMap_apply,Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]

lemma varMul_leadingRelations (q : Plane (K := K) →ₐ[K] R) (i : Fin 2) (n : ℕ) :
    (leadingRelations q n).map (varMul i n) ≤ leadingRelations q (n+1) := by
  rintro _ ⟨p,hp,rfl⟩
  change p ∈ leadingRelations q n at hp
  rw [mem_leadingRelations] at hp ⊢
  change q (X i*p.val) ∈ _
  rw [map_mul]
  exact mul_X_filtered q i hp

lemma leadingMap_range (q : Plane (K := K) →ₐ[K] R) (n : ℕ) :
    LinearMap.range (leadingMap q n) = (filtered q (n+1)).map (filtered q n).mkQ := by
  ext z
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨q p.val,homogeneous_mem_filtered q p,rfl⟩
  · rintro ⟨r,hr,rfl⟩
    obtain ⟨p,hp,rfl⟩ := (mem_filtered_succ q n r).mp hr
    refine ⟨topComponent n p,?_⟩
    change Submodule.Quotient.mk (q (topComponent n p).val) = Submodule.Quotient.mk (q p)
    apply (Submodule.Quotient.eq _).mpr
    simpa only [neg_sub] using (filtered q n).neg_mem (sub_topComponent_mem_filtered q hp)

lemma filteredH_add_rank (q : Plane (K := K) →ₐ[K] R) (n : ℕ) :
    filteredH q n + Module.finrank K (filtered q n) = Module.finrank K (filtered q (n+1)) := by
  let f := (filtered q n).mkQ.domRestrict (filtered q (n+1))
  have hr : LinearMap.range f = LinearMap.range (leadingMap q n) := by
    rw [leadingMap_range,LinearMap.range_domRestrict]
  have hk : LinearMap.ker f = (filtered q n).comap (filtered q (n+1)).subtype := by
    simp only [f,LinearMap.domRestrict,LinearMap.ker_comp,Submodule.ker_mkQ]
  have hh := f.finrank_range_add_finrank_ker
  rw [hr,hk,(Submodule.comapSubtypeEquivOfLe (filtered_mono q (Nat.le_succ n))).finrank_eq] at hh
  unfold filteredH
  rw [(leadingMap q n).quotKerEquivRange.finrank_eq]
  exact hh

end PermanentBorder.PlaneHilbert
namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K : Type*} [Field K]
variable (W : (n : ℕ) → Submodule K (H (K := K) (n : ℤ)))

lemma quotientH_add_rank (n : ℕ) : quotientH W n + Module.finrank K (W n) = n+1 := by
  rw [quotientH, Submodule.finrank_quotient_add_finrank, finrank_piece]
  omega
lemma quotientH_le (n : ℕ) : quotientH W n ≤ n+1 := by
  have := quotientH_add_rank W n
  omega
variable (hW : ∀ (i : Fin 2) (n : ℕ), (W n).map (varMul i n) ≤ W (n+1))
include hW in
lemma quotientH_succ_le_of_deficit {n : ℕ}
    (hn : quotientH W n < n+1) : quotientH W (n+1) ≤ quotientH W n := by
  have h0 : W n ≠ ⊥ := by
    intro h
    have hh := quotientH_add_rank W n
    rw [h, finrank_bot] at hh
    omega
  have hh := finrank_varMul_sup (W n) h0
  have hl : Module.finrank K ↥((W n).map (varMul 0 n) ⊔ (W n).map (varMul 1 n)) ≤
      Module.finrank K (W (n+1)) := Submodule.finrank_mono (sup_le (hW 0 n) (hW 1 n))
  have h1 := quotientH_add_rank W n
  have h2 := quotientH_add_rank W (n+1)
  omega
include hW in
lemma quotientH_le_of_deficit {n m : ℕ}
    (hn : quotientH W n < n+1) (hnm : n ≤ m) : quotientH W m ≤ quotientH W n := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hnm ih =>
    exact (quotientH_succ_le_of_deficit W hW (by omega : quotientH W m < m+1)).trans ih

include hW in
lemma quotientH_normalized {n m : ℕ} (hnm : n ≤ m) :
    (n+1) * quotientH W m ≤ (m+1) * quotientH W n := by
  rcases (quotientH_le W n).eq_or_lt with he|hl
  · rw [he]
    have := quotientH_le W m
    nlinarith
  · have hh := quotientH_le_of_deficit W hW hl hnm
    nlinarith

theorem quotientH_coprime_bound
    {a b : Plane (K := K)} {e f : ℤ}
    (ha : a.IsWeightedHomogeneous weight e) (hb : b.IsWeightedHomogeneous weight f)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : IsRelPrime a b) (n : ℕ)
    (haW : multiplicationRange ha (n : ℤ) ≤ W n)
    (hbW : multiplicationRange hb (n : ℤ) ≤ W n) :
    quotientH W n + ((n : ℤ)-e+1).toNat + ((n : ℤ)-f+1).toNat ≤
      n+1 + ((n : ℤ)-(e+f)+1).toNat := by
  have hh := Submodule.finrank_sup_add_finrank_inf_eq
    (multiplicationRange ha (n : ℤ)) (multiplicationRange hb (n : ℤ))
  rw [multiplicationRange_inf ha hb hb0 hab,
    finrank_multiplicationRange ha ha0, finrank_multiplicationRange hb hb0,
    finrank_multiplicationRange (ha.mul hb) (mul_ne_zero ha0 hb0)] at hh
  have hl : Module.finrank K ↥(multiplicationRange ha (n : ℤ) ⊔
      multiplicationRange hb (n : ℤ)) ≤ Module.finrank K (W n) :=
    Submodule.finrank_mono (sup_le haW hbW)
  have heq := quotientH_add_rank W n
  omega

end PermanentBorder.PlaneHilbert
namespace PermanentBorder.PlaneHilbert
open Finset
variable (h : ℕ → ℕ)
lemma hSum_succ (n : ℕ) : hSum h (n+1) = hSum h n + h n := sum_range_succ _ _

lemma hSum_double_le
    (hnorm : ∀ n m, n ≤ m → (n+1)*h m ≤ (m+1)*h n) (n : ℕ) :
    hSum h (2*n) ≤ 4*hSum h n := by
  induction n with
  | zero => simp [hSum]
  | succ n ih =>
    have h1 := hnorm n (2*n) (by omega)
    have h2 := hnorm n (2*n+1) (by omega)
    have hh : h (2*n) + h (2*n+1) ≤ 4*h n := by nlinarith
    rw [show 2*(n+1) = (2*n+1)+1 by omega, hSum_succ, hSum_succ, hSum_succ]
    omega

lemma hSum_half_length (B : ℕ)
    (hle : ∀ n, h n ≤ n+1)
    (hdec : ∀ n m, h n < n+1 → n ≤ m → h m ≤ h n)
    (htail : ∀ n, B ≤ n → h n ≤ 2*B-n) :
    hSum h (2*B) ≤ 2*hSum h B := by
  have hp : ∀ i ∈ range B, h (B+i) ≤ h (B-1-i) := by
    intro i hi
    have hiB := mem_range.mp hi
    rcases (hle (B-1-i)).eq_or_lt with he|hl
    · rw [he]
      have ht := htail (B+i) (by omega)
      omega
    · exact hdec (B-1-i) (B+i) hl (by omega)
  have hs := sum_le_sum hp
  rw [sum_range_reflect] at hs
  have he : hSum h (2*B) = hSum h B + ∑ i ∈ range B, h (B+i) := by
    rw [show 2*B = B+B by omega, hSum, sum_range_add]
    rfl
  rw [he]
  dsimp only [hSum] at *
  omega

end PermanentBorder.PlaneHilbert
namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

lemma mul_filtered_by_homogeneous (q : Plane (K := K) →ₐ[K] R) {n m : ℕ}
    {z : R} (hz : z ∈ filtered q n) (p : H (K := K) (m : ℤ)) :
    z * q p.val ∈ filtered q (n+m) := by
  cases n with
  | zero =>
    have hz0 : z = 0 := hz
    simp [hz0]
  | succ n =>
    obtain ⟨a,ha,rfl⟩ := (mem_filtered_succ q n z).mp hz
    rw [show n+1+m = (n+m)+1 by omega]
    apply (mem_filtered_succ q (n+m) _).mpr
    refine ⟨a*p.val,?_,map_mul _ _ _⟩
    exact (totalDegree_mul _ _).trans
      (Nat.add_le_add ha (intWeight_homogeneous p.property).totalDegree_le)

lemma multiplicationRange_le_leading (q : Plane (K := K) →ₐ[K] R)
    {a : Plane (K := K)} {e : ℕ} (ha : a.IsWeightedHomogeneous weight (e : ℤ))
    (hqa : q a ∈ filtered q e) (n : ℕ) :
    multiplicationRange ha (n : ℤ) ≤ leadingRelations q n := by
  rintro _ ⟨p,rfl⟩
  rw [mem_leadingRelations]
  change q (a*p.val) ∈ _
  rw [map_mul]
  by_cases hen : e ≤ n
  · let p' : H (K := K) ((n-e : ℕ) : ℤ) := ⟨p.val, by
      have hh : (n : ℤ)-e = ((n-e : ℕ) : ℤ) := by omega
      exact hh ▸ p.property⟩
    have hh := mul_filtered_by_homogeneous q hqa p'
    simpa only [Nat.add_sub_of_le hen] using hh
  · have hr : Module.finrank K (H (K := K) ((n : ℤ)-e)) = 0 := by
      rw [finrank_piece]; omega
    obtain ⟨c,hc,hcp⟩ := Module.finrank_eq_zero_iff.mp hr p
    have hp0 : p = 0 := (smul_eq_zero.mp hcp).resolve_left hc
    rw [hp0]
    simp

lemma filtered_rank_eq_hSum (q : Plane (K := K) →ₐ[K] R) (n : ℕ) :
    Module.finrank K (filtered q n) = hSum (filteredH q) n := by
  induction n with
  | zero =>
    change Module.finrank K (⊥ : Submodule K R) = 0
    exact finrank_bot K R
  | succ n ih =>
    rw [hSum_succ,← ih]
    have := filteredH_add_rank q n
    omega

lemma filtered_eq_top_of_tail (q : Plane (K := K) →ₐ[K] R)
    (hq : Function.Surjective q) (N : ℕ)
    (hz : ∀ n, N ≤ n → filteredH q n = 0) : filtered q N = ⊤ := by
  have he : ∀ n, N ≤ n → filtered q n = filtered q N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      have hh := filteredH_add_rank q n
      rw [hz n hn,zero_add] at hh
      exact (Submodule.eq_of_le_of_finrank_eq (filtered_mono q (Nat.le_succ n)) hh).symm.trans ih
  apply top_unique
  intro z _
  obtain ⟨p,rfl⟩ := hq z
  have hm : q p ∈ filtered q (max N (p.totalDegree+1)) :=
    filtered_mono q (le_max_right ..)
      ((mem_filtered_succ q p.totalDegree (q p)).mpr ⟨p,le_rfl,rfl⟩)
  rwa [he _ (le_max_left ..)] at hm

theorem finite_interpolation_half (q : Plane (K := K) →ₐ[K] R)
    (hq : Function.Surjective q) {a b : Plane (K := K)} {e f B : ℕ}
    (ha : a.IsWeightedHomogeneous weight (e : ℤ))
    (hb : b.IsWeightedHomogeneous weight (f : ℤ))
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : IsRelPrime a b)
    (hqa : q a ∈ filtered q e) (hqb : q b ∈ filtered q f)
    (he : e ≤ B+1) (hf : f ≤ B+1) (hef : e+f ≤ 2*B+1) :
    filtered q (2*B) = ⊤ ∧ Module.finrank K R ≤ 2*Module.finrank K (filtered q B) := by
  have ht : ∀ n, B ≤ n → filteredH q n ≤ 2*B-n := by
    intro n hn
    have hh := quotientH_coprime_bound (leadingRelations q) ha hb ha0 hb0 hab n
      (multiplicationRange_le_leading q ha hqa n)
      (multiplicationRange_le_leading q hb hqb n)
    change filteredH q n + _ + _ ≤ _ at hh
    omega
  have htop := filtered_eq_top_of_tail q hq (2*B) (by
    intro n hn
    have hh := ht n (by omega)
    omega)
  refine ⟨htop,?_⟩
  have hh := hSum_half_length (filteredH q) B
    (quotientH_le (leadingRelations q))
    (fun n m hn hnm => quotientH_le_of_deficit (leadingRelations q)
      (varMul_leadingRelations q) hn hnm) ht
  rw [← filtered_rank_eq_hSum, ← filtered_rank_eq_hSum, htop,finrank_top] at hh
  exact hh

lemma filtered_rank_double_le (q : Plane (K := K) →ₐ[K] R) (n : ℕ) :
    Module.finrank K (filtered q (2*n)) ≤ 4*Module.finrank K (filtered q n) := by
  rw [filtered_rank_eq_hSum, filtered_rank_eq_hSum]
  exact hSum_double_le (filteredH q)
    (fun n m hnm => quotientH_normalized (leadingRelations q)
      (varMul_leadingRelations q) hnm) n

end PermanentBorder.PlaneHilbert

namespace PermanentBorder.LowPlane
open MvPolynomial
variable {K : Type*} [Field K]

lemma card_index (B : ℕ) : Fintype.card (Index B) = (B+1).choose 2 := by
  rw [Fintype.card_congr (indexEquiv B),Fintype.card_subtype]
  simpa only [Fintype.card_fin] using Fintype.card_product_filter_lt (α := Fin (B+1))

lemma expansion {B : ℕ} (p : MvPolynomial (Fin 2) K)
    (hp : ∀ s ∈ p.support, s.degree < B) :
    p = ∑ s : Index B, p.coeff s.val • monomial s.val (1 : K) := by
  classical
  ext t
  rw [coeff_sum]
  by_cases ht : t.degree < B
  · rw [Finset.sum_eq_single (⟨t,ht⟩ : Index B)]
    · simp
    · intro s _ hs
      have he : s.val ≠ t := fun h => hs (Subtype.ext h)
      simp [coeff_monomial,he]
    · simp
  · have hz : p.coeff t=0 := by
      by_contra hn
      exact ht (hp t (mem_support_iff.mpr hn))
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro s _
    have he : s.val ≠ t := fun he => ht (he ▸ s.property)
    simp [coeff_monomial,he]

lemma remainder_expansion {B : ℕ} (p t : MvPolynomial (Fin 2) K)
    (hp : ∀ s, B ≤ s.degree → p.coeff s = t.coeff s) :
    p = t + ∑ s : Index B, (p-t).coeff s.val • monomial s.val (1 : K) := by
  have h := expansion (p-t) (by
    intro s hs
    have hc := mem_support_iff.mp hs
    rw [coeff_sub,sub_ne_zero] at hc
    exact lt_of_not_ge (fun hh => hc (hp s hh)))
  rw [← h]
  abel

end PermanentBorder.LowPlane

namespace PermanentBorder.LinearParameters
open Module
variable {K L S ι κ : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup S] [Module L S] [Fintype ι] [Fintype κ]

lemma independent_coefficients_mem (F : IntermediateField K L) (c : Basis κ L S)
    (v : ι → S) (hv : LinearIndependent L v) (x : ι → L)
    (hvc : ∀ i j, c.repr (v i) j ∈ F)
    (hx : ∀ j, c.repr (∑ i, x i • v i) j ∈ F) : ∀ i, x i ∈ F := by
  classical
  have ht : (⊤ : Submodule L S) ≤ Submodule.span L (Set.range v ∪ Set.range c) := by
    rw [← c.span_eq]
    exact Submodule.span_mono Set.subset_union_right
  let hs : Set.range v ⊆ Set.range v ∪ Set.range c := Set.subset_union_left
  let b := Basis.extendLe hv.linearIndepOn_id hs ht
  let j : ι → hv.linearIndepOn_id.extend hs :=
    fun i => ⟨v i,hv.linearIndepOn_id.subset_extend hs ⟨i,rfl⟩⟩
  have hj : Function.Injective j := by
    intro i i' he
    exact hv.injective (congrArg Subtype.val he)
  have hb : ∀ i, b (j i) = v i := fun i => Basis.extendLe_apply_self ..
  have hbc : ∀ i t, c.repr (b t) i ∈ F := by
    intro i t
    have hh := Basis.extendLe_subset hv.linearIndepOn_id hs ht
      (Set.mem_range_self t)
    rcases hh with ⟨a,ha⟩|⟨a,ha⟩
    · rw [← ha]; exact hvc a i
    · rw [← ha,c.repr_self]
      by_cases h : a=i <;> simp [h]
  have hh := BasisFieldRecovery.repr_mem F b c hbc _ hx
  intro i
  have he : b.repr (∑ a, x a • v a) (j i) = x i := by
    simp only [← hb,map_sum,map_smul,Basis.repr_self,Finsupp.finsetSum_apply,
      Finsupp.smul_apply,smul_eq_mul,Finsupp.single_apply]
    simp only [hj.eq_iff]
    simp
  rw [← he]
  exact hh (j i)

end PermanentBorder.LinearParameters

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.HalfPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.LinearParameters
open Module
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {S ι κ : Type*} [AddCommGroup S] [Module L S] [Fintype ι] [Fintype κ]

theorem add_constrained_parameters (F : IntermediateField K L) (n : ℕ)
    (hF : Algebra.trdeg K F ≤ (n : Cardinal)) (c : Basis κ L S)
    (v : ι → S) (x : ι → L) (hvc : ∀ i j, c.repr (v i) j ∈ F)
    (hx : ∀ j, c.repr (∑ i, x i • v i) j ∈ F) :
    ∃ E : IntermediateField K L, F ≤ E ∧ (∀ i, x i ∈ E) ∧
      Algebra.trdeg K E ≤
        (n + (Fintype.card ι - finrank L (Submodule.span L (Set.range v))) : ℕ) := by
  classical
  let : Module.Finite L S := Module.Finite.of_basis c
  let r := finrank L (Submodule.span L (Set.range v))
  obtain ⟨w,hw,_,hwi⟩ := Submodule.exists_fun_fin_finrank_span_eq L (Set.range v)
  choose j hj using hw
  have hji : Function.Injective j := by
    intro a b h
    apply hwi.injective
    rw [← hj a,← hj b,h]
  let e := Equiv.ofInjective j hji
  let t := (Set.range j)ᶜ
  have ht : Fintype.card t = Fintype.card ι - r := by
    rw [Fintype.card_compl_set,← Fintype.card_congr e]
    simp only [Fintype.card_fin,r]
  obtain ⟨E,hFE,hxE,hE⟩ := SliceParameters.add_parameters F n hF (fun i : t => x i)
  have hsum : (∑ a, x (j a) • v (j a)) =
      (∑ i, x i • v i) - ∑ i : t, x i • v i := by
    have he := Equiv.sum_comp e (fun a : Set.range j => x a • v a)
    change (∑ a, x (j a) • v (j a)) = _ at he
    rw [he]
    apply eq_sub_of_add_eq
    convert Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ Set.range j)
      (fun i => x i • v i) using 1
    congr 3
    exact Subsingleton.elim _ _
  have hpi : LinearIndependent L (fun a => v (j a)) := by
    simpa only [hj] using hwi
  have hpE : ∀ a, x (j a) ∈ E := independent_coefficients_mem E c
      (fun a => v (j a)) hpi (fun a => x (j a))
      (fun a k => hFE (hvc (j a) k)) (by
        intro k
        rw [hsum,map_sub]
        apply E.sub_mem (hFE (hx k))
        simp only [map_sum,Finsupp.finsetSum_apply,map_smul,Finsupp.smul_apply,smul_eq_mul]
        exact E.sum_mem (fun i _ => E.mul_mem (hxE i) (hFE (hvc i k))))
  refine ⟨E,hFE,?_,?_⟩
  · intro i
    by_cases hi : i ∈ Set.range j
    · obtain ⟨a,rfl⟩ := hi
      exact hpE a
    · exact hxE ⟨i,hi⟩
  · simpa only [ht] using hE

end PermanentBorder.LinearParameters
namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert
universe u
variable {K L R : Type u} [Field K] [Field L] [Algebra K L]
  [CommRing R] [Algebra L R]

lemma inField_lift (F : IntermediateField K L) {p : MvPolynomial (Fin 2) L}
    (hp : InField F p) : ∃ p₀ : MvPolynomial (Fin 2) F, p₀.map F.val.toRingHom = p := by
  apply mem_range_map_iff_coeffs_subset.mpr
  intro c hc
  obtain ⟨s,_,rfl⟩ := mem_coeffs_iff.mp hc
  exact ⟨⟨_,hp s⟩,rfl⟩

lemma inField_of_high {F : IntermediateField K L} {p : MvPolynomial (Fin 2) L}
    {B : ℕ} (hp : ∀ s, B ≤ s.degree → p.coeff s ∈ F)
    (hlow : ∀ s : Index B, p.coeff s.val ∈ F) : InField F p := by
  intro s
  by_cases hs : s.degree < B
  · exact hlow ⟨s,hs⟩
  · exact hp s (by omega)

lemma span_low (q : MvPolynomial (Fin 2) L →ₐ[L] R) (B : ℕ) :
    Submodule.span L (Set.range (fun s : Index B => q (monomial s.val (1 : L)))) = filtered q B := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨s,rfl⟩
    cases B with
    | zero => exact False.elim (Nat.not_lt_zero _ s.property)
    | succ B =>
      apply (mem_filtered_succ q B _).mpr
      refine ⟨_,(totalDegree_monomial_le _ _).trans ?_,rfl⟩
      change s.val.degree ≤ B
      have h:=s.property
      omega
  · cases B with
    | zero => exact bot_le
    | succ B =>
      intro z hz
      obtain ⟨p,hp,rfl⟩ := (mem_filtered_succ q B z).mp hz
      rw [LowPlane.expansion (B := B+1) p (by
        intro s hs
        have hc : s.degree ≤ p.totalDegree := le_totalDegree hs
        omega),map_sum]
      apply Submodule.sum_mem
      intro s _
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self s))

lemma repr_polynomial_mem {ι : Type*} [Fintype ι] (F : IntermediateField K L)
    (q : MvPolynomial (Fin 2) L →ₐ[L] R) (c : Basis ι L R)
    (hmon : ∀ s i, c.repr (q (monomial s (1 : L))) i ∈ F)
    (p : MvPolynomial (Fin 2) L) (hp : InField F p) :
    ∀ i, c.repr (q p) i ∈ F := by
  classical
  intro i
  rw [p.as_sum]
  simp only [map_sum,Finsupp.finsetSum_apply]
  apply F.sum_mem
  intro s _
  have he : monomial s (p.coeff s) = p.coeff s • monomial s (1 : L) := by rw [smul_monomial,smul_eq_mul,mul_one]
  rw [he,map_smul,map_smul,Finsupp.smul_apply,smul_eq_mul]
  exact F.mul_mem (hp s) (hmon s i)

theorem add_vanishing_polynomial {ι : Type*} [Fintype ι]
    (F : IntermediateField K L) (n B : ℕ) (hF : Algebra.trdeg K F ≤ (n : Cardinal))
    (q : MvPolynomial (Fin 2) L →ₐ[L] R) (c : Basis ι L R)
    (hmon : ∀ s i, c.repr (q (monomial s (1 : L))) i ∈ F)
    (p t : MvPolynomial (Fin 2) L) (ht : InField F t)
    (hhigh : ∀ s, B ≤ s.degree → p.coeff s = t.coeff s) (hpq : q p = 0) :
    ∃ E : IntermediateField K L, F ≤ E ∧ InField E p ∧
      Algebra.trdeg K E ≤ (n + (Fintype.card (Index B) - finrank L (filtered q B)) : ℕ) := by
  classical
  have he := remainder_expansion p t hhigh
  have hsum : ∑ s : Index B, (p-t).coeff s.val • q (monomial s.val 1) = -q t := by
    have hh := congrArg q he
    rw [hpq,map_add,map_sum] at hh
    simp only [map_smul] at hh
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hh.symm)
  obtain ⟨E,hFE,hxE,hE⟩ := LinearParameters.add_constrained_parameters F n hF c
    (fun s : Index B => q (monomial s.val 1)) (fun s => (p-t).coeff s.val)
    (fun s i => hmon s.val i) (by
      intro i
      rw [hsum,map_neg]
      exact F.neg_mem (repr_polynomial_mem F q c hmon t ht i))
  refine ⟨E,hFE,?_,?_⟩
  · intro s
    by_cases hs : s.degree < B
    · have hh := hxE ⟨s,hs⟩
      rw [coeff_sub] at hh
      have ht' := hFE (ht s)
      simpa only [sub_add_cancel] using E.add_mem hh ht'
    · rw [hhigh s (by omega)]
      exact hFE (ht s)
  · rwa [span_low] at hE

end PermanentBorder.CurveFamily

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert
universe u
variable {K L R : Type u} [Field K] [Field L] [Algebra K L]
  [CommRing R] [Algebra L R]

lemma adjoin_polynomial (F : IntermediateField K L) (n B : ℕ)
    (hF : Algebra.trdeg K F ≤ (n : Cardinal)) (p : MvPolynomial (Fin 2) L)
    (hhigh : ∀ s, B ≤ s.degree → p.coeff s ∈ F) :
    ∃ E : IntermediateField K L, F ≤ E ∧ InField E p ∧
      Algebra.trdeg K E ≤ (n + Fintype.card (Index B) : ℕ) := by
  obtain ⟨E,hFE,hc,hE⟩ := SliceParameters.add_parameters F n hF
    (fun s : Index B => p.coeff s.val)
  exact ⟨E,hFE,inField_of_high (fun s hs => hFE (hhigh s hs)) hc,hE⟩

lemma monomial_plane (s : Fin 2 →₀ ℕ) :
    (monomial s 1 : MvPolynomial (Fin 2) L) = X 0 ^ s 0 * X 1 ^ s 1 := by
  rw [monomial_eq,C_1,one_mul,Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fin.prod_univ_two]

theorem extend_by_quotient [Infinite K] [IsAlgClosed L] [Module.Finite L R]
    (F : IntermediateField K L) (n : ℕ) (hF : Algebra.trdeg K F ≤ (n : Cardinal))
    (p : MvPolynomial (Fin 2) L) (hp : p ≠ 0) (hpF : InField F p)
    (q : MvPolynomial (Fin 2) L →ₐ[L] R) (hq : Function.Surjective q) (hpq : q p = 0)
    (c : Basis (Fin (finrank L R)) L R) (a b : Fin (finrank L R) → ℕ)
    (hc : ∀ i, c i=q (X 0 ^ a i * X 1 ^ b i)) :
    ∃ E : IntermediateField K L, F ≤ E ∧
      (∀ s i, c.repr (q (monomial s (1 : L))) i ∈ E) ∧
      Algebra.trdeg K E ≤ (n + finrank L R : ℕ) := by
  obtain ⟨p₀,hp₀⟩ := inField_lift F hpF
  have hp0 : p₀ ≠ 0 := by intro hz; apply hp; rw [← hp₀,hz,map_zero]
  let : Infinite F := Infinite.of_injective (algebraMap K F) (algebraMap K F).injective
  obtain ⟨E,hE,hA,hB,hv⟩ := CurveQuotientParameters.chart_field_bound p₀ hp0 q hq
    (by change q (p₀.map F.val.toRingHom)=0; rw [hp₀,hpq]) c a b hc
  let : FaithfulSMul F E := (faithfulSMul_iff_algebraMap_injective F E).mpr
    (algebraMap F E).injective
  let : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨E.restrictScalars K,?_,?_,?_⟩
  · intro x hx
    exact E.algebraMap_mem ⟨x,hx⟩
  · intro s i
    rw [monomial_plane]
    exact FinitePlaneFrames.monomial_coordinates_mem E q c hA hB hv (s 0) (s 1) i
  · change Algebra.trdeg K E ≤ _
    rw [← trdeg_add_eq K F]
    exact (add_le_add hF hE).trans_eq (by simp)

end PermanentBorder.CurveFamily

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert
universe u
variable {K L R : Type u} [Field K] [Field L] [Algebra K L]
  [CommRing R] [Algebra L R]

lemma filtered_rank_le (q : MvPolynomial (Fin 2) L →ₐ[L] R) (B : ℕ) :
    finrank L (filtered q B) ≤ Fintype.card (Index B) := by
  rw [← span_low]
  exact finrank_range_le_card _

lemma inField_map (F : IntermediateField K L) (p : MvPolynomial (Fin 2) K) :
    InField F (p.map (algebraMap K L)) := by
  intro s
  rw [coeff_map]
  exact F.algebraMap_mem _

lemma inField_mono {F E : IntermediateField K L} (hFE : F ≤ E)
    {p : MvPolynomial (Fin 2) L} (hp : InField F p) : InField E p := fun s => hFE (hp s)

theorem add_vanishing_family {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : IntermediateField K L) (n : ℕ) (hF : Algebra.trdeg K F ≤ (n : Cardinal))
    (q : MvPolynomial (Fin 2) L →ₐ[L] R) (c : Basis ι L R)
    (hmon : ∀ s i, c.repr (q (monomial s (1 : L))) i ∈ F)
    (B : κ → ℕ) (p : κ → MvPolynomial (Fin 2) L) (t : κ → MvPolynomial (Fin 2) K)
    (hhigh : ∀ i s, B i ≤ s.degree → (p i).coeff s = algebraMap K L ((t i).coeff s))
    (hpq : ∀ i, q (p i) = 0) (U : Finset κ) :
    ∃ E : IntermediateField K L, F ≤ E ∧ (∀ i ∈ U, InField E (p i)) ∧
      Algebra.trdeg K E ≤ (n + ∑ i ∈ U, (Fintype.card (Index (B i)) - finrank L (filtered q (B i))) : ℕ) := by
  classical
  induction U using Finset.induction_on with
  | empty => exact ⟨F,le_rfl,by simp,by simpa using hF⟩
  | @insert i U hi ih =>
    obtain ⟨E,hFE,hpE,hE⟩ := ih
    obtain ⟨D,hED,hpD,hD⟩ := add_vanishing_polynomial E _ (B i) hE q c
      (fun s j => hFE (hmon s j)) (p i) ((t i).map (algebraMap K L)) (inField_map E _)
      (by intro s hs; rw [coeff_map]; exact hhigh i s hs) (hpq i)
    refine ⟨D,hFE.trans hED,?_,?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact hpD
      · exact inField_mono hED (hpE j hj)
    · simpa only [Finset.sum_insert hi,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hD

theorem four_polynomial_bound [Infinite K] [IsAlgClosed L] [Module.Finite L R]
    (q : MvPolynomial (Fin 2) L →ₐ[L] R) (hq : Function.Surjective q)
    (B₀ : ℕ) (B : Fin 3 → ℕ)
    (p₀ : MvPolynomial (Fin 2) L) (p : Fin 3 → MvPolynomial (Fin 2) L)
    (t₀ : MvPolynomial (Fin 2) K) (t : Fin 3 → MvPolynomial (Fin 2) K)
    (hp₀ : p₀ ≠ 0) (h₀ : ∀ s, B₀ ≤ s.degree → p₀.coeff s=algebraMap K L (t₀.coeff s))
    (h : ∀ i s, B i ≤ s.degree → (p i).coeff s=algebraMap K L ((t i).coeff s))
    (hq₀ : q p₀=0) (hqp : ∀ i, q (p i)=0)
    (hrank : ∀ i, finrank L R ≤ 2*finrank L (filtered q (B i))) :
    ∃ (E : IntermediateField K L) (n : ℕ), InField E p₀ ∧ (∀ i, InField E (p i)) ∧
      Algebra.trdeg K E ≤ (n : Cardinal) ∧
      2*n + finrank L R ≤ 2*(Fintype.card (Index B₀) + ∑ i, Fintype.card (Index (B i))) := by
  classical
  have hbot : Algebra.trdeg K (⊥ : IntermediateField K L) ≤ (0 : Cardinal) := by rw [trdeg_eq_zero]
  obtain ⟨F,_,hpF,hF⟩ := adjoin_polynomial (⊥ : IntermediateField K L) 0 B₀ hbot p₀
    (by intro s hs; rw [h₀ s hs]; exact IntermediateField.algebraMap_mem _ _)
  obtain ⟨c,a,b,hc⟩ := FinitePlaneFrames.exists_monomial_basis q hq
  obtain ⟨D,hFD,hmon,hD⟩ := extend_by_quotient F _ hF p₀ hp₀ hpF q hq hq₀ c a b hc
  obtain ⟨E,hDE,hpE,hE⟩ := add_vanishing_family D _ hD q c hmon B p t h hqp Finset.univ
  refine ⟨E,_,inField_mono (hFD.trans hDE) hpF,(fun i => hpE i (Finset.mem_univ i)),hE,?_⟩
  let N := fun i => Fintype.card (Index (B i))
  let r := fun i => finrank L (filtered q (B i))
  have hle (i) : r i ≤ N i := filtered_rank_le q (B i)
  have he : ∑ i, (N i-r i) + ∑ i, r i = ∑ i, N i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.sub_add_cancel (hle i)
  have hh : 3*finrank L R ≤ 2*∑ i, r i := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrank i)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,← Finset.mul_sum] using hs
  change 2*(0+Fintype.card (Index B₀)+finrank L R+∑ i, (N i-r i))+finrank L R ≤ 2*(Fintype.card (Index B₀)+∑ i, N i)
  omega

end PermanentBorder.CurveFamily

namespace PermanentBorder.FrobeniusPlane
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [CharP L 2]

lemma derivation_square {M : Type*} [AddCommGroup M] [Module K M]
    [Module L M] [IsScalarTower K L M] (D : Derivation K L M) (a : L) :
    D (a^2) = 0 := by
  rw [D.leibniz_pow,← Nat.cast_smul_eq_nsmul L]
  simp only [CharP.cast_eq_zero L 2,zero_smul]

omit [CharP L 2] in
lemma derivation_zero_of_field_generators {M : Type*} [AddCommGroup M] [Module K M]
    [Module L M] [IsScalarTower K L M] (D : Derivation K L M)
    (s : Set L) (hs : IntermediateField.adjoin K s = ⊤) (hD : ∀ x ∈ s, D x = 0) : D = 0 := by
  let F : IntermediateField K L :=
    { carrier := {x | D x = 0}
      zero_mem' := map_zero D
      one_mem' := D.map_one_eq_zero
      add_mem' := by
        intro x y hx hy
        change D x = 0 at hx
        change D y = 0 at hy
        change D (x+y) = 0
        rw [map_add,hx,hy,add_zero]
      mul_mem' := by
        intro x y hx hy
        change D x = 0 at hx
        change D y = 0 at hy
        change D (x*y) = 0
        rw [D.leibniz,hx,hy,smul_zero,smul_zero,add_zero]
      inv_mem' := by
        intro x hx
        change D x = 0 at hx
        change D x⁻¹ = 0
        rw [D.leibniz_inv,hx,smul_zero]
      algebraMap_mem' := fun r => D.map_algebraMap r }
  have hF : IntermediateField.adjoin K s ≤ F := IntermediateField.adjoin_le_iff.mpr hD
  rw [hs] at hF
  ext x
  exact hF (show x ∈ (⊤ : IntermediateField K L) from trivial)

theorem finite_of_square_coordinate_equations (x : Fin 2 → L)
    (hgen : IntermediateField.adjoin K (Set.range x) = ⊤)
    (b c d : L) (hd : d ≠ 0)
    (hb : b^2+x 1*d^2=0) (hc : c^2+x 0*d^2=0) : Module.Finite K L := by
  classical
  let D := KaehlerDifferential.D K L
  have hx (i : Fin 2) : D (x i) = 0 := by
    have h (v a : L) (he : a^2+v*d^2=0) : D v = 0 := by
      have hh := congrArg D he
      simp only [map_add,D.leibniz,derivation_square,smul_zero,zero_add,map_zero] at hh
      exact (smul_eq_zero.mp hh).resolve_left (pow_ne_zero 2 hd)
    fin_cases i
    · exact h _ _ hc
    · exact h _ _ hb
  have hD : D = 0 := derivation_zero_of_field_generators D _ hgen (by
    rintro _ ⟨i,rfl⟩; exact hx i)
  have hbot : (⊤ : Submodule L (KaehlerDifferential K L)) ≤ ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation,Submodule.span_le]
    rintro _ ⟨a,rfl⟩
    change D a = 0
    rw [hD]; rfl
  let : Algebra.FormallyUnramified K L := ⟨(subsingleton_iff_forall_eq 0).mpr (fun a => hbot trivial)⟩
  let : Algebra.EssFiniteType K L := IntermediateField.fg_top_iff.mp
    ⟨Finset.univ.image x,by simpa using hgen⟩
  exact Algebra.FormallyUnramified.finite_of_free K L
end PermanentBorder.FrobeniusPlane
namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [CharP L 2]

theorem node_coordinates_algebraic (x : Fin 2 → L)
    (b c d : MvPolynomial (Fin 2) K) (hd : aeval x d ≠ 0)
    (hb : (aeval x b)^2+x 1*(aeval x d)^2=0)
    (hc : (aeval x c)^2+x 0*(aeval x d)^2=0) : ∀ i, IsAlgebraic K (x i) := by
  let E := IntermediateField.adjoin K (Set.range x)
  let y : Fin 2 → E := fun i => ⟨x i,IntermediateField.subset_adjoin K _ (Set.mem_range_self i)⟩
  have hgen : IntermediateField.adjoin K (Set.range y) = ⊤ := by
    apply IntermediateField.map_injective E.val
    rw [IntermediateField.adjoin_map,← Set.range_comp,← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val]
    rfl
  let : CharP E 2 := (algebraMap E L).charP (algebraMap E L).injective 2
  have he (p : MvPolynomial (Fin 2) K) : E.val.toRingHom (aeval y p) = aeval x p := by
    change E.val (aeval y p) = _
    rw [← AlgHom.comp_apply]
    congr 1
    ext i
    simp [y]
  have hy (i) : E.val.toRingHom (y i) = x i := rfl
  let : Module.Finite K E := finite_of_square_coordinate_equations y hgen
    (aeval y b) (aeval y c) (aeval y d) (by intro hz; apply hd; rw [← he d,hz,map_zero])
    (by apply E.val.injective; simpa only [map_add,map_mul,map_pow,AlgHom.coe_toRingHom,he,hy,map_zero] using hb)
    (by apply E.val.injective; simpa only [map_add,map_mul,map_pow,AlgHom.coe_toRingHom,he,hy,map_zero] using hc)
  intro i
  exact (IsAlgebraic.of_finite K (y i)).algHom E.val

end PermanentBorder.FrobeniusPlane

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.SingularValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert
universe u
variable {K L R : Type u} [Field K] [Field L] [Algebra K L]
  [CommRing R] [Algebra L R]

theorem add_evaluated_polynomial {ι : Type*} [Fintype ι]
    (F : IntermediateField K L) (n B : ℕ) (hF : Algebra.trdeg K F ≤ (n : Cardinal))
    (q : MvPolynomial (Fin 2) L →ₐ[L] R) (c : Basis ι L R)
    (hmon : ∀ s i, c.repr (q (monomial s (1 : L))) i ∈ F)
    (p t : MvPolynomial (Fin 2) L) (ht : InField F t)
    (hhigh : ∀ s, B ≤ s.degree → p.coeff s = t.coeff s)
    (hpq : ∀ i, c.repr (q p) i ∈ F) :
    ∃ E : IntermediateField K L, F ≤ E ∧ InField E p ∧
      Algebra.trdeg K E ≤ (n + (Fintype.card (Index B) - finrank L (filtered q B)) : ℕ) := by
  classical
  have he := remainder_expansion p t hhigh
  have hsum : ∑ s : Index B, (p-t).coeff s.val • q (monomial s.val 1) = q p-q t := by
    have hh := congrArg q he
    rw [map_add,map_sum] at hh
    simp only [map_smul] at hh
    exact eq_sub_of_add_eq (by simpa only [add_comm] using hh.symm)
  obtain ⟨E,hFE,hxE,hE⟩ := LinearParameters.add_constrained_parameters F n hF c
    (fun s : Index B => q (monomial s.val 1)) (fun s => (p-t).coeff s.val)
    (fun s i => hmon s.val i) (by
      intro i
      rw [hsum,map_sub]
      exact F.sub_mem (hpq i) (repr_polynomial_mem F q c hmon t ht i))
  refine ⟨E,hFE,?_,?_⟩
  · intro s
    by_cases hs : s.degree < B
    · have hh := hxE ⟨s,hs⟩
      rw [coeff_sub] at hh
      simpa only [sub_add_cancel] using E.add_mem hh (hFE (ht s))
    · rw [hhigh s (by omega)]
      exact hFE (ht s)
  · rwa [span_low] at hE

lemma evaluated_mem (F : IntermediateField K L) {p : MvPolynomial (Fin 2) L}
    (hp : InField F p) {x : Fin 2 → L} (hx : ∀ i, x i ∈ F) : eval x p ∈ F :=
  eval_mem (fun s _ => hp s) hx

lemma add_algebraic_closure (F : IntermediateField K L) (n : ℕ)
    (hF : Algebra.trdeg K F ≤ (n : Cardinal)) :
    let E := (algebraicClosure F L).restrictScalars K
    F ≤ E ∧ Algebra.trdeg K E ≤ (n : Cardinal) := by
  let E := algebraicClosure F L
  let : FaithfulSMul F E := (faithfulSMul_iff_algebraMap_injective F E).mpr
    (algebraMap F E).injective
  let : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨fun x hx => E.algebraMap_mem ⟨x,hx⟩,?_⟩
  change Algebra.trdeg K E ≤ _
  rw [← trdeg_add_eq K F,trdeg_eq_zero (R := F),add_zero]
  exact hF

lemma node_values_mem [CharP L 2] (F : IntermediateField K L)
    (a b c d : MvPolynomial (Fin 2) L) (hbF : InField F b) (hcF : InField F c)
    (hdF : InField F d) (x : Fin 2 → L) (hd : eval x d ≠ 0)
    (hb : (eval x b)^2+x 1*(eval x d)^2=0)
    (hc : (eval x c)^2+x 0*(eval x d)^2=0)
    (ha : (eval x a)^2+x 0*(eval x b)^2+x 1*(eval x c)^2+x 0*x 1*(eval x d)^2=0) :
    (∀ i, x i ∈ algebraicClosure F L) ∧ eval x a ∈ algebraicClosure F L := by
  obtain ⟨b₀,hb₀⟩ := inField_lift F hbF
  obtain ⟨c₀,hc₀⟩ := inField_lift F hcF
  obtain ⟨d₀,hd₀⟩ := inField_lift F hdF
  have he (p : MvPolynomial (Fin 2) F) : aeval x p = eval x (p.map F.val.toRingHom) := by
    rw [eval_map]
    rfl
  have hx := FrobeniusPlane.node_coordinates_algebraic x b₀ c₀ d₀
    (by simpa only [he,hd₀] using hd) (by simpa only [he,hb₀,hd₀] using hb)
    (by simpa only [he,hc₀,hd₀] using hc)
  have hx' : ∀ i, x i ∈ algebraicClosure F L := fun i => mem_algebraicClosure_iff.mpr (hx i)
  refine ⟨hx',mem_algebraicClosure_iff.mpr ?_⟩
  apply IsAlgebraic.of_pow (n := 2) (by omega)
  apply mem_algebraicClosure_iff.mp
  have hFE : F ≤ (algebraicClosure F L).restrictScalars K := fun z hz =>
    (algebraicClosure F L).algebraMap_mem ⟨z,hz⟩
  have hb' := evaluated_mem ((algebraicClosure F L).restrictScalars K) (inField_mono hFE hbF) hx'
  have hc' := evaluated_mem ((algebraicClosure F L).restrictScalars K) (inField_mono hFE hcF) hx'
  have hd' := evaluated_mem ((algebraicClosure F L).restrictScalars K) (inField_mono hFE hdF) hx'
  have heq : (eval x a)^2 = -(x 0*(eval x b)^2+x 1*(eval x c)^2+x 0*x 1*(eval x d)^2) := by
    linear_combination ha
  rw [heq]
  exact neg_mem (add_mem (add_mem (mul_mem (hx' 0) (pow_mem hb' 2))
    (mul_mem (hx' 1) (pow_mem hc' 2))) (mul_mem (mul_mem (hx' 0) (hx' 1)) (pow_mem hd' 2)))

end PermanentBorder.CurveFamily

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

theorem adjoin_polynomial_family {κ : Type*} [Fintype κ]
    (F : IntermediateField K L) (n : ℕ) (hF : Algebra.trdeg K F ≤ (n : Cardinal))
    (B : κ → ℕ) (p : κ → MvPolynomial (Fin 2) L) (t : κ → MvPolynomial (Fin 2) K)
    (hhigh : ∀ i s, B i ≤ s.degree → (p i).coeff s=algebraMap K L ((t i).coeff s))
    (U : Finset κ) :
    ∃ E : IntermediateField K L, F ≤ E ∧ (∀ i ∈ U, InField E (p i)) ∧
      Algebra.trdeg K E ≤ (n+∑ i ∈ U, Fintype.card (Index (B i)) : ℕ) := by
  classical
  induction U using Finset.induction_on with
  | empty => exact ⟨F,le_rfl,by simp,by simpa using hF⟩
  | @insert i U hi ih =>
    obtain ⟨D,hFD,hpD,hD⟩ := ih
    obtain ⟨E,hDE,hpE,hE⟩ := adjoin_polynomial D _ (B i) hD (p i) (by
      intro s hs; rw [hhigh i s hs]; exact D.algebraMap_mem ((t i).coeff s))
    refine ⟨E,hFD.trans hDE,?_,?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact hpE
      · exact inField_mono hDE (hpD j hj)
    · simpa only [Finset.sum_insert hi,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hE

lemma pointEvaluation_apply {ι : Type*} (x : ι → Fin 2 → L)
    (p : MvPolynomial (Fin 2) L) (i : ι) : pointEvaluation x p i = eval (x i) p := by
  simp [pointEvaluation,aeval_def]

theorem node_parameter_bound [CharP L 2] {ι : Type u} [Fintype ι]
    (x : ι → Fin 2 → L) (a b c d : MvPolynomial (Fin 2) L)
    (B₀ : ℕ) (B : Fin 3 → ℕ) (t₀ : MvPolynomial (Fin 2) K)
    (t : Fin 3 → MvPolynomial (Fin 2) K)
    (h₀ : ∀ s, B₀ ≤ s.degree → a.coeff s=algebraMap K L (t₀.coeff s))
    (h : ∀ i s, B i ≤ s.degree → (![b,c,d] i).coeff s=algebraMap K L ((t i).coeff s))
    (hd : ∀ i, eval (x i) d ≠ 0)
    (hb : ∀ i, (eval (x i) b)^2+x i 1*(eval (x i) d)^2=0)
    (hc : ∀ i, (eval (x i) c)^2+x i 0*(eval (x i) d)^2=0)
    (ha : ∀ i, (eval (x i) a)^2+x i 0*(eval (x i) b)^2+
      x i 1*(eval (x i) c)^2+x i 0*x i 1*(eval (x i) d)^2=0) :
    ∃ (E : IntermediateField K L) (n : ℕ), InField E a ∧ InField E b ∧ InField E c ∧
      InField E d ∧ Algebra.trdeg K E ≤ (n : Cardinal) ∧
      n+finrank L (filtered (pointEvaluation x) B₀) ≤
        Fintype.card (Index B₀)+∑ i, Fintype.card (Index (B i)) := by
  classical
  have hbot : Algebra.trdeg K (⊥ : IntermediateField K L) ≤ (0 : Cardinal) := by rw [trdeg_eq_zero]
  obtain ⟨F,_,hpF,hF⟩ := adjoin_polynomial_family (⊥ : IntermediateField K L) 0 hbot
    B ![b,c,d] t h Finset.univ
  simp only [Finset.mem_univ,forall_const,zero_add] at hpF hF
  let D := (algebraicClosure F L).restrictScalars K
  obtain ⟨hFD,hD⟩ := add_algebraic_closure F _ hF
  have hn := fun i => node_values_mem F a b c d (hpF 0) (hpF 1) (hpF 2)
    (x i) (hd i) (hb i) (hc i) (ha i)
  obtain ⟨E,hDE,hpE,hE⟩ := add_evaluated_polynomial D _ B₀ hD (pointEvaluation x)
    (Pi.basisFun L ι) (by
      intro s i
      rw [Pi.basisFun_repr,pointEvaluation_apply]
      apply evaluated_mem D _ (hn i).1
      intro j
      rw [coeff_monomial]
      split_ifs <;> simp)
    a (t₀.map (algebraMap K L)) (inField_map D _) (by
      intro s hs; rw [coeff_map]; exact h₀ s hs)
    (by intro i; rw [Pi.basisFun_repr,pointEvaluation_apply]; exact (hn i).2)
  refine ⟨E,_,hpE,inField_mono (hFD.trans hDE) (hpF 0),
    inField_mono (hFD.trans hDE) (hpF 1),inField_mono (hFD.trans hDE) (hpF 2),hE,?_⟩
  have hr := filtered_rank_le (pointEvaluation x) B₀
  omega

end PermanentBorder.CurveFamily

namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
variable {K : Type*} [Field K] [CharP K 2]

lemma squareForm_add (a b c d a' b' c' d' : Plane K) :
    squareForm (a+a') (b+b') (c+c') (d+d') =
      squareForm a b c d + squareForm a' b' c' d' := by
  have htwo : (2 : Plane K) = 0 := CharP.cast_eq_zero _ 2
  simp only [squareForm, add_sq, htwo, zero_mul, add_zero]
  ring

omit [CharP K 2] in
lemma squareForm_mul_zero (a b c d : Plane K) :
    squareForm a b c d * X 0 = squareForm (X 0*b) a (X 0*d) c := by
  unfold squareForm
  ring

omit [CharP K 2] in
lemma squareForm_mul_one (a b c d : Plane K) :
    squareForm a b c d * X 1 = squareForm (X 1*c) (X 1*d) a b := by
  unfold squareForm
  ring

theorem exists_squareForm [PerfectRing K 2] (f : Plane K) :
    ∃ a b c d : Plane K, f = squareForm a b c d := by
  induction f using MvPolynomial.induction_on with
  | C a =>
      refine ⟨C ((frobeniusEquiv K 2).symm a),0,0,0,?_⟩
      simp only [squareForm, zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero]
      rw [← map_pow, frobeniusEquiv_symm_pow_p]
  | add f g hf hg =>
      obtain ⟨a,b,c,d,rfl⟩ := hf
      obtain ⟨a',b',c',d',rfl⟩ := hg
      exact ⟨a+a',b+b',c+c',d+d',(squareForm_add ..).symm⟩
  | mul_X f i hf =>
      obtain ⟨a,b,c,d,rfl⟩ := hf
      fin_cases i
      · exact ⟨X 0*b,a,X 0*d,c,squareForm_mul_zero ..⟩
      · exact ⟨X 1*c,X 1*d,a,b,squareForm_mul_one ..⟩

lemma squareForm_partial_zero (a b c d : Plane K) :
    pderiv 0 (squareForm a b c d) = b^2 + X 1*d^2 := by
  have htwo : (2 : Plane K) = 0 := CharP.cast_eq_zero _ 2
  simp [squareForm, htwo, mul_comm]

lemma squareForm_partial_one (a b c d : Plane K) :
    pderiv 1 (squareForm a b c d) = c^2 + X 0*d^2 := by
  have htwo : (2 : Plane K) = 0 := CharP.cast_eq_zero _ 2
  simp [squareForm, htwo, mul_comm]

lemma squareForm_mixed (a b c d : Plane K) :
    pderiv 1 (pderiv 0 (squareForm a b c d)) = d^2 := by
  rw [squareForm_partial_zero]
  have htwo : (2 : Plane K) = 0 := CharP.cast_eq_zero _ 2
  simp [htwo]

end PermanentBorder.FrobeniusPlane

namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
variable {K : Type*} [Field K] [CharP K 2]

lemma squareForm_eq_zero_iff (a b c d : Plane K) :
    squareForm a b c d = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro hf
    have hd : d = 0 := by
      have hh := congrArg (fun f : Plane K => pderiv 1 (pderiv 0 f)) hf
      rw [squareForm_mixed] at hh
      simpa using hh
    have hb : b = 0 := by
      have hh := congrArg (pderiv (0 : Fin 2)) hf
      rw [squareForm_partial_zero, hd] at hh
      simpa using hh
    have hc : c = 0 := by
      have hh := congrArg (pderiv (1 : Fin 2)) hf
      rw [squareForm_partial_one, hd] at hh
      simpa using hh
    have ha : a = 0 := by simpa [squareForm, hb, hc, hd] using hf
    exact ⟨ha,hb,hc,hd⟩
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    simp [squareForm]

lemma squareForm_injective {a b c d a' b' c' d' : Plane K}
    (h : squareForm a b c d = squareForm a' b' c' d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have hz : squareForm (a+a') (b+b') (c+c') (d+d') = 0 := by
    rw [squareForm_add,h]
    simpa using (CharTwo.add_self_eq_zero (squareForm a' b' c' d'))
  rcases (squareForm_eq_zero_iff ..).mp hz with ⟨ha,hb,hc,hd⟩
  exact ⟨CharTwo.add_eq_zero.mp ha, CharTwo.add_eq_zero.mp hb,
    CharTwo.add_eq_zero.mp hc, CharTwo.add_eq_zero.mp hd⟩

end PermanentBorder.FrobeniusPlane

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.DegreeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
lemma partial_degree {f : Plane K} {n : ℕ} (hf : f.totalDegree ≤ n+1) (i : Fin 2) :
    (pderiv i f).totalDegree ≤ n := by
  classical
  apply Finset.sup_le
  intro m hm
  have hc := mem_support_iff.mp hm
  rw [coeff_pderiv] at hc
  have hp : f.coeff (m+Finsupp.single i 1) ≠ 0 := (mul_ne_zero_iff.mp hc).1
  have hd := le_totalDegree (mem_support_iff.mpr hp)
  change (m+Finsupp.single i 1).degree ≤ f.totalDegree at hd
  simp only [map_add,Finsupp.degree_single] at hd
  change m.degree ≤ n
  omega

omit [CharP K 2] in
lemma square_degree (p : Plane K) : (p^2).totalDegree = 2*p.totalDegree := by
  by_cases hp : p=0
  · simp [hp]
  · rw [pow_two,totalDegree_mul_of_isDomain hp hp]
    omega

lemma squareForm_degree_bounds {a b c d : Plane K} {n : ℕ}
    (h : (squareForm a b c d).totalDegree ≤ n+2) :
    2*a.totalDegree ≤ n+2 ∧ 2*b.totalDegree ≤ n+1 ∧
      2*c.totalDegree ≤ n+1 ∧ 2*d.totalDegree ≤ n := by
  have hx := partial_degree h 0
  have hy := partial_degree h 1
  rw [squareForm_partial_zero] at hx
  rw [squareForm_partial_one] at hy
  have hd := partial_degree (partial_degree h 0) 1
  rw [squareForm_mixed,square_degree] at hd
  have hxd : (X (0 : Fin 2)*d^2).totalDegree ≤ n+1 := by
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_X,square_degree]; omega)
  have hyd : (X (1 : Fin 2)*d^2).totalDegree ≤ n+1 := by
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_X,square_degree]; omega)
  have hb : 2*b.totalDegree ≤ n+1 := by
    rw [← square_degree]
    have he : b^2=(b^2+X 1*d^2)-X 1*d^2 := by ring
    rw [he]
    exact (totalDegree_sub _ _).trans (max_le hx hyd)
  have hc : 2*c.totalDegree ≤ n+1 := by
    rw [← square_degree]
    have he : c^2=(c^2+X 0*d^2)-X 0*d^2 := by ring
    rw [he]
    exact (totalDegree_sub _ _).trans (max_le hy hxd)
  have ha : 2*a.totalDegree ≤ n+2 := by
    rw [← square_degree]
    have he : a^2=squareForm a b c d-X 0*b^2-X 1*c^2-X 0*X 1*d^2 := by
      unfold squareForm; ring
    rw [he]
    apply (totalDegree_sub _ _).trans
    apply max_le
    · apply (totalDegree_sub _ _).trans
      apply max_le
      · apply (totalDegree_sub _ _).trans
        exact max_le h ((totalDegree_mul _ _).trans (by rw [totalDegree_X,square_degree]; omega))
      · exact (totalDegree_mul _ _).trans (by rw [totalDegree_X,square_degree]; omega)
    · have he' : X (0 : Fin 2)*X 1*d^2=X 0*(X 1*d^2) := mul_assoc ..
      rw [he']
      exact (totalDegree_mul _ _).trans (by rw [totalDegree_X]; omega)
  exact ⟨ha,hb,hc,hd⟩

omit [CharP K 2] in
lemma squareForm_degree_le {a b c d : Plane K} {n : ℕ}
    (ha : 2*a.totalDegree ≤ n) (hb : 1+2*b.totalDegree ≤ n)
    (hc : 1+2*c.totalDegree ≤ n) (hd : 2+2*d.totalDegree ≤ n) :
    (squareForm a b c d).totalDegree ≤ n := by
  unfold squareForm
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · apply (totalDegree_add _ _).trans
      exact max_le (by simpa only [square_degree] using ha)
        ((totalDegree_mul _ _).trans (by simpa only [totalDegree_X,square_degree] using hb))
    · exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_X,square_degree] using hc)
  · have h := (totalDegree_mul (X (0 : Fin 2) : Plane K) (X 1))
    exact (totalDegree_mul _ _).trans (by simp only [totalDegree_X,square_degree] at *; omega)

omit [CharP K 2] in
lemma subtract_top_degree {p : Plane K} {n : ℕ} (hp : p.totalDegree ≤ n+1) :
    (p-homogeneousComponent (n+1) p).totalDegree ≤ n := by
  classical
  apply Finset.sup_le
  intro m hm
  have hc := mem_support_iff.mp hm
  rw [coeff_sub,coeff_homogeneousComponent] at hc
  change m.degree ≤ n
  by_contra! hn
  by_cases he : m.degree=n+1
  · exact hc (by simp [he])
  · have hz : p.coeff m=0 := coeff_eq_zero_of_totalDegree_lt (by change p.totalDegree < m.degree; omega)
    exact hc (by simp [he,hz])

lemma squareForm_top_even {a b c d : Plane K} {r : ℕ} (hr : 2 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r) :
    homogeneousComponent (2*r) (squareForm a b c d) =
      squareForm (homogeneousComponent r a) 0 0 (homogeneousComponent (r-1) d) := by
  let A := homogeneousComponent r a
  let D := homogeneousComponent (r-1) d
  have hdeg := squareForm_degree_bounds (n := 2*r-2) (by omega :
    (squareForm a b c d).totalDegree ≤ (2*r-2)+2)
  have ha : 2*(a-A).totalDegree ≤ 2*r-1 := by
    have hh : (a-homogeneousComponent ((r-1)+1) a).totalDegree ≤ r-1 :=
      subtract_top_degree (by omega)
    have he : r-1+1=r := by omega
    rw [he] at hh
    change (a-A).totalDegree ≤ r-1 at hh
    omega
  have hd : 2+2*(d-D).totalDegree ≤ 2*r-1 := by
    have hh : (d-homogeneousComponent ((r-2)+1) d).totalDegree ≤ r-2 :=
      subtract_top_degree (by omega)
    have he : r-2+1=r-1 := by omega
    rw [he] at hh
    change (d-D).totalDegree ≤ r-2 at hh
    omega
  have hlow := squareForm_degree_le ha (by omega : 1+2*b.totalDegree ≤ 2*r-1)
    (by omega : 1+2*c.totalDegree ≤ 2*r-1) hd
  have hz : homogeneousComponent (2*r) (squareForm (a-A) b c (d-D))=0 :=
    homogeneousComponent_eq_zero _ _ (by omega)
  have htop : (squareForm A 0 0 D).IsHomogeneous (2*r) := by
    simp only [squareForm,zero_pow (by omega : 2 ≠ 0),mul_zero,add_zero]
    apply IsHomogeneous.add
    · convert (homogeneousComponent_isHomogeneous r a).pow 2 using 1; omega
    · convert ((isHomogeneous_X K (0 : Fin 2)).mul (isHomogeneous_X K 1)).mul
        ((homogeneousComponent_isHomogeneous (r-1) d).pow 2) using 1; omega
  have he : squareForm a b c d = squareForm A 0 0 D + squareForm (a-A) b c (d-D) := by
    rw [← squareForm_add]
    simp only [add_sub_cancel,zero_add]
  rw [he,map_add,homogeneousComponent_eq_self htop,hz,add_zero]

lemma squareForm_top_odd {a b c d : Plane K} {r : ℕ} (hr : 1 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r+1) :
    homogeneousComponent (2*r+1) (squareForm a b c d) =
      squareForm 0 (homogeneousComponent r b) (homogeneousComponent r c) 0 := by
  let B := homogeneousComponent r b
  let C' := homogeneousComponent r c
  have hdeg := squareForm_degree_bounds (n := 2*r-1) (by omega :
    (squareForm a b c d).totalDegree ≤ (2*r-1)+2)
  have hb : 1+2*(b-B).totalDegree ≤ 2*r := by
    have hh : (b-homogeneousComponent ((r-1)+1) b).totalDegree ≤ r-1 :=
      subtract_top_degree (by omega)
    have he : r-1+1=r := by omega
    rw [he] at hh
    change (b-B).totalDegree ≤ r-1 at hh
    omega
  have hc : 1+2*(c-C').totalDegree ≤ 2*r := by
    have hh : (c-homogeneousComponent ((r-1)+1) c).totalDegree ≤ r-1 :=
      subtract_top_degree (by omega)
    have he : r-1+1=r := by omega
    rw [he] at hh
    change (c-C').totalDegree ≤ r-1 at hh
    omega
  have hlow := squareForm_degree_le (by omega : 2*a.totalDegree ≤ 2*r) hb hc
    (by omega : 2+2*d.totalDegree ≤ 2*r)
  have hz : homogeneousComponent (2*r+1) (squareForm a (b-B) (c-C') d)=0 :=
    homogeneousComponent_eq_zero _ _ (by omega)
  have htop : (squareForm 0 B C' 0).IsHomogeneous (2*r+1) := by
    simp only [squareForm,zero_pow (by omega : 2 ≠ 0),mul_zero,add_zero,zero_add]
    apply IsHomogeneous.add
    · convert (isHomogeneous_X K (0 : Fin 2)).mul
        ((homogeneousComponent_isHomogeneous r b).pow 2) using 1; omega
    · convert (isHomogeneous_X K (1 : Fin 2)).mul
        ((homogeneousComponent_isHomogeneous r c).pow 2) using 1; omega
  have he : squareForm a b c d = squareForm 0 B C' 0 + squareForm a (b-B) (c-C') d := by
    rw [← squareForm_add]
    simp only [add_sub_cancel,zero_add]
  rw [he,map_add,homogeneousComponent_eq_self htop,hz,add_zero]

end PermanentBorder.FrobeniusPlane
namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
lemma homogeneous_not_unit {p : Plane K} {n : ℕ} (hp : p.IsHomogeneous n)
    (hn : 0 < n) : ¬ IsUnit p := by
  intro hu
  have hz := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
  have he := hp.totalDegree hu.ne_zero
  omega

omit [CharP K 2] in
lemma squarefree_even_pair {a d : Plane K}
    (h : Squarefree (squareForm a 0 0 d)) : IsRelPrime a d := by
  intro g hga hgd
  apply h g
  simp only [squareForm,zero_pow (by omega : 2 ≠ 0),mul_zero,add_zero]
  apply dvd_add
  · simpa only [pow_two] using mul_dvd_mul hga hga
  · exact dvd_mul_of_dvd_right (by simpa only [pow_two] using mul_dvd_mul hgd hgd) _

omit [CharP K 2] in
lemma squarefree_odd_pair {b c : Plane K}
    (h : Squarefree (squareForm 0 b c 0)) : IsRelPrime b c := by
  intro g hgb hgc
  apply h g
  simp only [squareForm,zero_pow (by omega : 2 ≠ 0),mul_zero,add_zero,zero_add]
  exact dvd_add (dvd_mul_of_dvd_right (by simpa only [pow_two] using mul_dvd_mul hgb hgb) _)
    (dvd_mul_of_dvd_right (by simpa only [pow_two] using mul_dvd_mul hgc hgc) _)

lemma squarefree_even_leading {a b c d : Plane K} {r : ℕ} (hr : 2 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r)
    (hs : Squarefree (homogeneousComponent (2*r) (squareForm a b c d))) :
    homogeneousComponent r a ≠ 0 ∧ homogeneousComponent (r-1) d ≠ 0 ∧
      IsRelPrime (homogeneousComponent r a) (homogeneousComponent (r-1) d) := by
  rw [squareForm_top_even hr hf] at hs
  have hp := squarefree_even_pair hs
  have ha := homogeneous_not_unit (homogeneousComponent_isHomogeneous r a) (by omega : 0 < r)
  have hd := homogeneous_not_unit (homogeneousComponent_isHomogeneous (r-1) d) (by omega : 0 < r-1)
  refine ⟨?_,?_,hp⟩
  · intro hz
    apply hd
    exact hp (by rw [hz]; exact dvd_zero _) dvd_rfl
  · intro hz
    apply ha
    exact hp dvd_rfl (by rw [hz]; exact dvd_zero _)

lemma squarefree_odd_leading {a b c d : Plane K} {r : ℕ} (hr : 1 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r+1)
    (hs : Squarefree (homogeneousComponent (2*r+1) (squareForm a b c d))) :
    homogeneousComponent r b ≠ 0 ∧ homogeneousComponent r c ≠ 0 ∧
      IsRelPrime (homogeneousComponent r b) (homogeneousComponent r c) := by
  rw [squareForm_top_odd hr hf] at hs
  have hp := squarefree_odd_pair hs
  have hb := homogeneous_not_unit (homogeneousComponent_isHomogeneous r b) (by omega : 0 < r)
  have hc := homogeneous_not_unit (homogeneousComponent_isHomogeneous r c) (by omega : 0 < r)
  refine ⟨?_,?_,hp⟩
  · intro hz
    exact hc (hp (by rw [hz]; exact dvd_zero _) dvd_rfl)
  · intro hz
    exact hb (hp dvd_rfl (by rw [hz]; exact dvd_zero _))

end PermanentBorder.FrobeniusPlane

namespace PermanentBorder.PlaneHilbert
open MvPolynomial
variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

lemma leading_vanishing_mem (q : Plane (K := K) →ₐ[K] R) {p : Plane (K := K)} {e : ℕ}
    (hp : p.totalDegree ≤ e) (hq : q p=0) : q (homogeneousComponent e p) ∈ filtered q e := by
  have hh := sub_topComponent_mem_filtered q hp
  change q p-q (homogeneousComponent e p) ∈ filtered q e at hh
  rw [hq,zero_sub] at hh
  exact (Submodule.neg_mem_iff _).mp hh

theorem finite_of_leading_pair (q : Plane (K := K) →ₐ[K] R) (hq : Function.Surjective q)
    {p t : Plane (K := K)} {e f B : ℕ} (hp : p.totalDegree ≤ e) (ht : t.totalDegree ≤ f)
    (hqp : q p=0) (hqt : q t=0) (hp0 : homogeneousComponent e p ≠ 0)
    (ht0 : homogeneousComponent f t ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e p) (homogeneousComponent f t))
    (he : e ≤ B+1) (hf : f ≤ B+1) (hef : e+f ≤ 2*B+1) :
    Module.Finite K R ∧ Module.finrank K R ≤ 2*Module.finrank K (filtered q B) := by
  have hh := finite_interpolation_half q hq
    (SliceParameters.homogeneous_intWeight (homogeneousComponent_isHomogeneous e p))
    (SliceParameters.homogeneous_intWeight (homogeneousComponent_isHomogeneous f t))
    hp0 ht0 hcop (leading_vanishing_mem q hp hqp) (leading_vanishing_mem q ht hqt) he hf hef
  refine ⟨?_,hh.2⟩
  apply Module.Finite.of_surjective (filtered q (2*B)).subtype
  intro z
  exact ⟨⟨z,by rw [hh.1]; trivial⟩,rfl⟩

end PermanentBorder.PlaneHilbert

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert FrobeniusPlane
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [CharP L 2]

omit [CharP L 2] in
lemma halfIdeal_mem (a b c d : Plane L) :
    a ∈ halfIdeal a b c d ∧ b ∈ halfIdeal a b c d ∧ c ∈ halfIdeal a b c d ∧ d ∈ halfIdeal a b c d := by
  exact ⟨Ideal.subset_span (by simp),Ideal.subset_span (by simp),
    Ideal.subset_span (by simp),Ideal.subset_span (by simp)⟩

lemma halfIdeal_even_finite {a b c d : Plane L} {r : ℕ} (hr : 2 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r)
    (hs : Squarefree (homogeneousComponent (2*r) (squareForm a b c d))) :
    let q := Ideal.Quotient.mkₐ L (halfIdeal a b c d)
    Module.Finite L (Plane L ⧸ halfIdeal a b c d) ∧
      finrank L (Plane L ⧸ halfIdeal a b c d) ≤ 2*finrank L (filtered q r) := by
  let q := Ideal.Quotient.mkₐ L (halfIdeal a b c d)
  have hm := halfIdeal_mem a b c d
  have hdeg := squareForm_degree_bounds (n := 2*r-2) (by simpa [show 2*r-2+2=2*r by omega] using hf)
  obtain ⟨ha0,hd0,hcop⟩ := squarefree_even_leading hr hf hs
  exact finite_of_leading_pair q Ideal.Quotient.mk_surjective
    (show a.totalDegree ≤ r by omega) (show d.totalDegree ≤ r-1 by omega)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hm.1) (Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.2.2)
    ha0 hd0 hcop (by omega) (by omega) (by omega)

lemma halfIdeal_odd_finite {a b c d : Plane L} {r : ℕ} (hr : 1 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r+1)
    (hs : Squarefree (homogeneousComponent (2*r+1) (squareForm a b c d))) :
    let q := Ideal.Quotient.mkₐ L (halfIdeal a b c d)
    Module.Finite L (Plane L ⧸ halfIdeal a b c d) ∧
      finrank L (Plane L ⧸ halfIdeal a b c d) ≤ 2*finrank L (filtered q r) := by
  let q := Ideal.Quotient.mkₐ L (halfIdeal a b c d)
  have hm := halfIdeal_mem a b c d
  have hdeg := squareForm_degree_bounds (n := 2*r-1) (by simpa [show 2*r-1+2=2*r+1 by omega] using hf)
  obtain ⟨hb0,hc0,hcop⟩ := squarefree_odd_leading hr hf hs
  exact finite_of_leading_pair q Ideal.Quotient.mk_surjective
    (show b.totalDegree ≤ r by omega) (show c.totalDegree ≤ r by omega)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.1) (Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.2.1)
    hb0 hc0 hcop (by omega) (by omega) (by omega)

end PermanentBorder.CurveFamily

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.WildParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert FrobeniusPlane
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [CharP L 2]

lemma twice_choose_two (n : ℕ) : 2*((n+1).choose 2)=n*(n+1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.choose_succ_succ]
    simp only [Nat.choose_one_right]
    nlinarith

lemma even_count (r : ℕ) :
    2*(Fintype.card (Index (r-1)) + ∑ _ : Fin 3, Fintype.card (Index r)) = (2*r)*(2*r+1) := by
  simp only [LowPlane.card_index,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  cases r with
  | zero => norm_num
  | succ s =>
    simp only [Nat.add_sub_cancel]
    have h1 := twice_choose_two s
    have h2 := twice_choose_two (s+1)
    nlinarith

lemma odd_count (r : ℕ) :
    2*(Fintype.card (Index r) + ∑ i : Fin 3, Fintype.card (Index (![r+1,r,r] i))) =
      (2*r+1)*(2*r+2) := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.isValue,
    Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero,LowPlane.card_index]
  have h1 := twice_choose_two r
  have h2 := twice_choose_two (r+1)
  nlinarith

theorem wild_parameter_bound_even [Infinite K] [IsAlgClosed L]
    {a b c d : Plane L} {r : ℕ} (hr : 2 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r)
    (hs : Squarefree (homogeneousComponent (2*r) (squareForm a b c d)))
    (t : Fin 4 → Plane K)
    (h : ∀ i s, (![r,r,r,r-1] i) ≤ s.degree →
      (![a,b,c,d] i).coeff s=algebraMap K L ((t i).coeff s)) :
    ∃ (E : IntermediateField K L) (n : ℕ), InField E a ∧ InField E b ∧ InField E c ∧
      InField E d ∧ Algebra.trdeg K E ≤ (n : Cardinal) ∧
      2*n+finrank L (Plane L ⧸ halfIdeal a b c d) ≤ (2*r)*(2*r+1) := by
  classical
  let q := Ideal.Quotient.mkₐ L (halfIdeal a b c d)
  obtain ⟨hfinite,hrank⟩ := halfIdeal_even_finite hr hf hs
  let := hfinite
  have hm := halfIdeal_mem a b c d
  have hd0 : d ≠ 0 := by
    intro hz
    have hh := (squarefree_even_leading hr hf hs).2.1
    exact hh (by rw [hz,map_zero])
  obtain ⟨E,n,hdE,hpE,hE,hn⟩ := four_polynomial_bound q Ideal.Quotient.mk_surjective
    (r-1) (fun _ => r) d ![a,b,c] (t 3) ![t 0,t 1,t 2] hd0
    (h 3) (by
      intro i
      fin_cases i
      · exact h 0
      · exact h 1
      · exact h 2)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.2.2)
    (by intro i; fin_cases i
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hm.1
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.1
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.2.1)
    (fun _ => hrank)
  exact ⟨E,n,hpE 0,hpE 1,hpE 2,hdE,hE,(hn.trans_eq (even_count r))⟩

theorem wild_parameter_bound_odd [Infinite K] [IsAlgClosed L]
    {a b c d : Plane L} {r : ℕ} (hr : 1 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r+1)
    (hs : Squarefree (homogeneousComponent (2*r+1) (squareForm a b c d)))
    (t : Fin 4 → Plane K)
    (h : ∀ i s, (![r+1,r,r,r] i) ≤ s.degree →
      (![a,b,c,d] i).coeff s=algebraMap K L ((t i).coeff s)) :
    ∃ (E : IntermediateField K L) (n : ℕ), InField E a ∧ InField E b ∧ InField E c ∧
      InField E d ∧ Algebra.trdeg K E ≤ (n : Cardinal) ∧
      2*n+finrank L (Plane L ⧸ halfIdeal a b c d) ≤ (2*r+1)*(2*r+2) := by
  classical
  let q := Ideal.Quotient.mkₐ L (halfIdeal a b c d)
  obtain ⟨hfinite,hrank⟩ := halfIdeal_odd_finite hr hf hs
  let := hfinite
  have hm := halfIdeal_mem a b c d
  have hb0 : b ≠ 0 := by
    intro hz
    have hh := (squarefree_odd_leading hr hf hs).1
    exact hh (by rw [hz,map_zero])
  obtain ⟨E,n,hbE,hpE,hE,hn⟩ := four_polynomial_bound q Ideal.Quotient.mk_surjective
    r ![r+1,r,r] b ![a,c,d] (t 1) ![t 0,t 2,t 3] hb0 (h 1)
    (by intro i; fin_cases i
        exact h 0
        exact h 2
        exact h 3)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.1)
    (by intro i; fin_cases i
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hm.1
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.2.1
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.2.2)
    (by intro i
        apply hrank.trans
        apply Nat.mul_le_mul_left 2
        apply Submodule.finrank_mono
        apply filtered_mono
        fin_cases i <;> simp)
  exact ⟨E,n,hpE 0,hbE,hpE 1,hpE 2,hE,(hn.trans_eq (odd_count r))⟩

end PermanentBorder.CurveFamily
namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert
variable {L : Type*} [Field L]

lemma pointEvaluation_surjective {ι : Type*} [Fintype ι]
    (x : ι → Fin 2 → L) (hx : Function.Injective x) :
    Function.Surjective (pointEvaluation x) := by
  classical
  have hp : ∀ i j : ι, i ≠ j → ∃ p : MvPolynomial (Fin 2) L,
      eval (x i) p = 1 ∧ eval (x j) p = 0 := by
    intro i j hij
    have hne : ∃ k, x i k ≠ x j k := by
      by_contra! h
      exact hij (hx (funext h))
    obtain ⟨k,hk⟩ := hne
    refine ⟨C (x i k-x j k)⁻¹*(X k-C (x j k)),?_,?_⟩
    · simp only [map_mul,map_sub,eval_C,eval_X]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr hk)
    · simp
  choose p hp using hp
  let P (i : ι) := ∏ j : {j // j ≠ i}, p i j.val (Ne.symm j.property)
  have he (i j : ι) : eval (x j) (P i) = if i=j then 1 else 0 := by
    dsimp [P]
    rw [map_prod]
    split_ifs with hij
    · subst j
      exact Finset.prod_eq_one fun z _ => (hp i z.val (Ne.symm z.property)).1
    · exact Finset.prod_eq_zero (Finset.mem_univ ⟨j,Ne.symm hij⟩)
        (hp i j hij).2
  intro y
  refine ⟨∑ i, C (y i)*P i,?_⟩
  ext j
  simp only [pointEvaluation_apply,map_sum,map_mul,eval_C,he]
  simp

lemma partial_leading (p : MvPolynomial (Fin 2) L) (n : ℕ) (i : Fin 2) :
    homogeneousComponent n (pderiv i p) = pderiv i (homogeneousComponent (n+1) p) := by
  ext s
  simp only [coeff_homogeneousComponent,coeff_pderiv]
  have he : (s+Finsupp.single i 1).degree = s.degree+1 := by
    simp only [map_add,Finsupp.degree_single]
  rw [he]
  split_ifs <;> simp_all

theorem distinct_critical_point_count {ι : Type*} [Fintype ι]
    (x : ι → Fin 2 → L) (hx : Function.Injective x)
    (f : MvPolynomial (Fin 2) L) (k R : ℕ) (hk : 1 ≤ k) (hR : k-1 ≤ 2*R)
    (hf : f.totalDegree ≤ k)
    (hlead : homogeneousComponent k f ≠ 0)
    (hpartial : pderiv 1 (homogeneousComponent k f) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent k f) (pderiv 1 (homogeneousComponent k f)))
    (hzero : ∀ i, eval (x i) f=0) (hderiv : ∀ i, eval (x i) (pderiv 1 f)=0) :
    Fintype.card ι ≤ 8*finrank L (filtered (pointEvaluation x) R) := by
  let q := pointEvaluation x
  have he : homogeneousComponent (k-1) (pderiv 1 f)=pderiv 1 (homogeneousComponent k f) := by
    simpa only [Nat.sub_add_cancel hk] using partial_leading f (k-1) 1
  have hdeg : (pderiv 1 f).totalDegree ≤ k-1 :=
    FrobeniusPlane.partial_degree (by rwa [Nat.sub_add_cancel hk]) 1
  have hh := finite_of_leading_pair q (pointEvaluation_surjective x hx) hf hdeg
    (by ext i; exact hzero i) (by ext i; exact hderiv i) hlead
    (by rwa [he]) (by rwa [he]) (B := k-1) (by omega) (by omega) (by omega)
  have hrank : finrank L (filtered q (k-1)) ≤ finrank L (filtered q (2*R)) :=
    Submodule.finrank_mono (filtered_mono q hR)
  have hd := filtered_rank_double_le q R
  change Fintype.card ι ≤ 8*finrank L (filtered q R)
  simpa only [Module.finrank_pi,finrank_self,Finset.sum_const,Finset.card_univ,
    smul_eq_mul,mul_one] using (hh.2.trans (by omega))

end PermanentBorder.CurveFamily
namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
variable {K L : Type*} [Field K] [Field L] [CharP K 2] [CharP L 2] [Algebra K L]

omit [CharP K 2] [CharP L 2] in
lemma squareForm_map (a b c d : Plane K) :
    (squareForm a b c d).map (algebraMap K L) =
      squareForm (a.map (algebraMap K L)) (b.map (algebraMap K L))
        (c.map (algebraMap K L)) (d.map (algebraMap K L)) := by
  simp [squareForm]

omit [CharP K 2] [CharP L 2] in
lemma high_coeff_of_top {p : Plane L} {t : Plane K} {n : ℕ}
    (hp : p.totalDegree ≤ n) (ht : t.IsHomogeneous n)
    (he : homogeneousComponent n p = t.map (algebraMap K L)) :
    ∀ s, n ≤ s.degree → p.coeff s=algebraMap K L (t.coeff s) := by
  intro s hs
  by_cases hsn : s.degree=n
  · have hh := congrArg (fun polynomial : Plane L => polynomial.coeff s) he
    simpa only [coeff_homogeneousComponent,hsn,ite_true,coeff_map] using hh
  · have hz : p.coeff s=0 := coeff_eq_zero_of_totalDegree_lt (by change _ < s.degree; omega)
    rw [hz,ht.coeff_eq_zero (by exact fun h => hsn h),map_zero]

omit [CharP K 2] [CharP L 2] in
lemma high_coeff_zero {p : Plane L} {n : ℕ} (h : p.totalDegree < n) :
    ∀ s, n ≤ s.degree → p.coeff s=algebraMap K L ((0 : Plane K).coeff s) := by
  intro s hs
  rw [MvPolynomial.coeff_zero,map_zero]
  exact coeff_eq_zero_of_totalDegree_lt (by change _ < s.degree; omega)

theorem fixed_half_forms_even [PerfectRing K 2]
    {a b c d : Plane L} {r : ℕ} (hr : 2 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r)
    (H : Plane K) (hH : H.IsHomogeneous (2*r))
    (he : homogeneousComponent (2*r) (squareForm a b c d)=H.map (algebraMap K L)) :
    ∃ t : Fin 4 → Plane K, ∀ i s, (![r,r,r,r-1] i) ≤ s.degree →
      (![a,b,c,d] i).coeff s=algebraMap K L ((t i).coeff s) := by
  obtain ⟨A,B,C,D,hrep⟩ := exists_squareForm H
  have hHdeg : (squareForm A B C D).totalDegree ≤ 2*r := by
    rw [← hrep]
    exact hH.totalDegree_le
  have htop := squareForm_top_even hr hHdeg
  rw [← hrep,homogeneousComponent_of_mem hH,ite_eq_left rfl] at htop
  rw [squareForm_top_even hr hf,htop,squareForm_map] at he
  simp only [map_zero] at he
  obtain ⟨ha,_,_,hd⟩ := squareForm_injective he
  have hdeg := squareForm_degree_bounds (n := 2*r-2)
    (by simpa only [show 2*r-2+2=2*r by omega] using hf)
  refine ⟨![homogeneousComponent r A,0,0,homogeneousComponent (r-1) D],?_⟩
  intro i
  fin_cases i <;> dsimp
  · exact high_coeff_of_top (by omega) (homogeneousComponent_isHomogeneous r A) ha
  · exact high_coeff_zero (by omega)
  · exact high_coeff_zero (by omega)
  · exact high_coeff_of_top (by omega) (homogeneousComponent_isHomogeneous (r-1) D) hd

theorem fixed_half_forms_odd [PerfectRing K 2]
    {a b c d : Plane L} {r : ℕ} (hr : 1 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r+1)
    (H : Plane K) (hH : H.IsHomogeneous (2*r+1))
    (he : homogeneousComponent (2*r+1) (squareForm a b c d)=H.map (algebraMap K L)) :
    ∃ t : Fin 4 → Plane K, ∀ i s, (![r+1,r,r,r] i) ≤ s.degree →
      (![a,b,c,d] i).coeff s=algebraMap K L ((t i).coeff s) := by
  obtain ⟨A,B,C,D,hrep⟩ := exists_squareForm H
  have hHdeg : (squareForm A B C D).totalDegree ≤ 2*r+1 := by
    rw [← hrep]
    exact hH.totalDegree_le
  have htop := squareForm_top_odd hr hHdeg
  rw [← hrep,homogeneousComponent_of_mem hH,ite_eq_left rfl] at htop
  rw [squareForm_top_odd hr hf,htop,squareForm_map] at he
  simp only [map_zero] at he
  obtain ⟨_,hb,hc,_⟩ := squareForm_injective he
  have hdeg := squareForm_degree_bounds (n := 2*r-1)
    (by simpa only [show 2*r-1+2=2*r+1 by omega] using hf)
  refine ⟨![0,homogeneousComponent r B,homogeneousComponent r C,0],?_⟩
  intro i
  fin_cases i <;> dsimp
  · exact high_coeff_zero (by omega)
  · exact high_coeff_of_top (by omega) (homogeneousComponent_isHomogeneous r B) hb
  · exact high_coeff_of_top (by omega) (homogeneousComponent_isHomogeneous r C) hc
  · exact high_coeff_zero (by omega)

end PermanentBorder.FrobeniusPlane

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.ConductorDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.CurveFamily
open MvPolynomial Module FrobeniusPlane
open scoped Classical
variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
lemma singular_zero_iff (f : Plane K) (x : Fin 2 → K) :
    x ∈ zeroLocus K (singularIdeal f) ↔
      eval x f=0 ∧ eval x (pderiv 0 f)=0 ∧ eval x (pderiv 1 f)=0 := by
  change singularIdeal f ≤ RingHom.ker (aeval x) ↔ _
  rw [singularIdeal,Ideal.span_le]
  simp only [Set.insert_subset_iff,Set.singleton_subset_iff]
  rfl

end PermanentBorder.CurveFamily

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert FrobeniusPlane
open scoped Classical
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

lemma inField_squareForm (E : IntermediateField K L) {a b c d : Plane L}
    (ha : InField E a) (hb : InField E b) (hc : InField E c) (hd : InField E d) :
    InField E (squareForm a b c d) := by
  obtain ⟨a₀,rfl⟩ := inField_lift E ha
  obtain ⟨b₀,rfl⟩ := inField_lift E hb
  obtain ⟨c₀,rfl⟩ := inField_lift E hc
  obtain ⟨d₀,rfl⟩ := inField_lift E hd
  intro s
  have he : squareForm (MvPolynomial.map E.val.toRingHom a₀) (MvPolynomial.map E.val.toRingHom b₀)
      (MvPolynomial.map E.val.toRingHom c₀) (MvPolynomial.map E.val.toRingHom d₀) =
      (squareForm a₀ b₀ c₀ d₀).map E.val.toRingHom := by simp [squareForm]
  rw [he,coeff_map]
  exact ((squareForm a₀ b₀ c₀ d₀).coeff s).property

variable [CharP L 2]

theorem ordinary_parameter_bound {a b c d : Plane L} {k R : ℕ}
    (hk : 1 ≤ k) (hR : k-1 ≤ 2*R)
    (hf : (squareForm a b c d).totalDegree ≤ k)
    (hlead : homogeneousComponent k (squareForm a b c d) ≠ 0)
    (hpartial : pderiv 1 (homogeneousComponent k (squareForm a b c d)) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent k (squareForm a b c d))
      (pderiv 1 (homogeneousComponent k (squareForm a b c d))))
    (B : Fin 3 → ℕ) (t : Fin 4 → Plane K)
    (h₀ : ∀ s, R ≤ s.degree → a.coeff s=algebraMap K L ((t 0).coeff s))
    (h : ∀ i s, B i ≤ s.degree → (![b,c,d] i).coeff s=algebraMap K L ((t i.succ).coeff s))
    [Fintype (zeroLocus L (singularIdeal (squareForm a b c d)))] :
    ∃ (E : IntermediateField K L) (n : ℕ), InField E (squareForm a b c d) ∧
      Algebra.trdeg K E ≤ (n : Cardinal) ∧
      8*n+Fintype.card {x : zeroLocus L (singularIdeal (squareForm a b c d)) // eval x.val d≠0} ≤
        8*(Fintype.card (Index R)+∑ i, Fintype.card (Index (B i))) := by
  let ι := {x : zeroLocus L (singularIdeal (squareForm a b c d)) // eval x.val d≠0}
  let x : ι → Fin 2 → L := fun z => z.val.val
  have hx : Function.Injective x := by
    intro z w hzw
    exact Subtype.ext (Subtype.ext hzw)
  have hsing (i : ι) := (singular_zero_iff _ _).mp i.val.property
  obtain ⟨E,n,ha,hb,hc,hd,hE,hn⟩ := node_parameter_bound x a b c d R B (t 0)
    (fun i => t i.succ) h₀ h (fun i => i.property)
    (fun i => by simpa only [squareForm_partial_zero,map_add,map_mul,map_pow,eval_X] using (hsing i).2.1)
    (fun i => by simpa only [squareForm_partial_one,map_add,map_mul,map_pow,eval_X] using (hsing i).2.2)
    (fun i => by simpa only [squareForm,map_add,map_mul,map_pow,eval_X] using (hsing i).1)
  have hcount := distinct_critical_point_count x hx (squareForm a b c d) k R hk hR hf hlead
    hpartial hcop (fun i => (hsing i).1) (fun i => (hsing i).2.2)
  refine ⟨E,n,inField_squareForm E ha hb hc hd,hE,?_⟩
  have hecard : Fintype.card {z : zeroLocus L (singularIdeal (squareForm a b c d)) // eval z.val d≠0} =
      Fintype.card ι := Fintype.card_congr (Equiv.refl _)
  rw [hecard]
  calc
    _ ≤ 8*n+8*finrank L (filtered (pointEvaluation x) R) := Nat.add_le_add_left hcount _
    _ = 8*(n+finrank L (filtered (pointEvaluation x) R)) := by omega
    _ ≤ _ := Nat.mul_le_mul_left 8 hn

end PermanentBorder.CurveFamily

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert FrobeniusPlane
open scoped Classical
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [CharP L 2]

lemma ordinary_even_count (r : ℕ) :
    2*(Fintype.card (Index r)+∑ i : Fin 3, Fintype.card (Index (![r,r,r-1] i))) =
      (2*r)*(2*r+1) := by
  have h := even_count r
  simp only [LowPlane.card_index,Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.isValue,
    Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero] at h ⊢
  omega

lemma ordinary_odd_count (r : ℕ) :
    2*(Fintype.card (Index (r+1))+∑ _i : Fin 3, Fintype.card (Index (r))) =
      (2*r+1)*(2*r+2) := by
  have h := odd_count r
  simp only [LowPlane.card_index,Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.isValue,
    Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero] at h ⊢
  omega

variable [CharP K 2] [PerfectRing K 2] [Infinite K] [IsAlgClosed L]

theorem half_curve_parameter_bound_oai {a b c d : Plane L} {k : ℕ}
    (hk : 4 ≤ k) (hf : (squareForm a b c d).totalDegree ≤ k)
    (hs : Squarefree (homogeneousComponent k (squareForm a b c d)))
    (hlead : homogeneousComponent k (squareForm a b c d) ≠ 0)
    (hpartial : pderiv 1 (homogeneousComponent k (squareForm a b c d)) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent k (squareForm a b c d))
      (pderiv 1 (homogeneousComponent k (squareForm a b c d))))
    (H : Plane K) (hH : H.IsHomogeneous k)
    (he : homogeneousComponent k (squareForm a b c d)=H.map (algebraMap K L))
    [Fintype (zeroLocus L (singularIdeal (squareForm a b c d)))] :
    ∃ (E : IntermediateField K L) (n : ℕ), InField E (squareForm a b c d) ∧
      Algebra.trdeg K E ≤ (n : Cardinal) ∧
      18*n+5*finrank L (Plane L ⧸ halfIdeal a b c d) +
        Fintype.card {x : zeroLocus L (singularIdeal (squareForm a b c d)) // eval x.val d≠0} ≤
          9*(k*(k+1)) := by
  have hrep : ∃ r, k=2*r ∨ k=2*r+1 := ⟨k/2,by omega⟩
  obtain ⟨r,h|h⟩ := hrep
  · subst k
    obtain ⟨t,ht⟩ := fixed_half_forms_even (by omega) hf H hH he
    obtain ⟨E,nw,ha,hb,hc,hd,hE,hw⟩ := wild_parameter_bound_even (by omega) hf hs t ht
    obtain ⟨F,nn,hfF,hF,hn⟩ := ordinary_parameter_bound (R := r) (by omega) (by omega) hf hlead hpartial hcop
      ![r,r,r-1] t (ht 0) (by intro _i; fin_cases _i; exact ht 1; exact ht 2; exact ht 3)
    have hcount := ordinary_even_count r
    by_cases hmin : nw≤nn
    · exact ⟨E,nw,inField_squareForm E ha hb hc hd,hE,by omega⟩
    · exact ⟨F,nn,hfF,hF,by omega⟩
  · subst k
    obtain ⟨t,ht⟩ := fixed_half_forms_odd (by omega) hf H hH he
    obtain ⟨E,nw,ha,hb,hc,hd,hE,hw⟩ := wild_parameter_bound_odd (by omega) hf hs t ht
    obtain ⟨F,nn,hfF,hF,hn⟩ := ordinary_parameter_bound (R := r+1) (by omega) (by omega) hf hlead hpartial hcop
      (fun _ : Fin 3 => r) t (ht 0) (by intro _i; fin_cases _i; exact ht 1; exact ht 2; exact ht 3)
    have hcount := ordinary_odd_count r
    by_cases hmin : nw≤nn
    · exact ⟨E,nw,inField_squareForm E ha hb hc hd,hE,by
        have hsimp : 2*r+1+1=2*r+2 := by omega
        rw [hsimp]
        omega⟩
    · exact ⟨F,nn,hfF,hF,by
        have hsimp : 2*r+1+1=2*r+2 := by omega
        rw [hsimp]
        omega⟩

end PermanentBorder.CurveFamily

end OAI
end

theorem solution.{u} : type_of% @OAI.PermanentBorder.CurveFamily.half_curve_parameter_bound_oai.{u} := @OAI.PermanentBorder.CurveFamily.half_curve_parameter_bound_oai.{u}
