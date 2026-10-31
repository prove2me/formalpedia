-- Prove2me | solution 1 for OAI.AffineBernstein.affineEpigraph_angular_literal_drift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:46:56.658551+00:00
-- url     : https://prove2.me/submissions/7b8c460a-47a2-4145-9274-f34eacff6dfa

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_invariant_tube_positive
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_tube_angular_smooth

section
-- module Solutions.OAIQ22_AB.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_PiolaAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exchanging two independently replaced rows reverses the determinant. -/
theorem det_updateRow_pair_swap (A : Matrix ι ι ℝ) {i l : ι} (hil : i ≠ l)
    (v w : ι → ℝ) :
    ((A.updateRow i v).updateRow l w).det =
      -((A.updateRow i w).updateRow l v).det := by
  have hm : ((A.updateRow i w).updateRow l v) ∘ Equiv.swap i l =
      (A.updateRow i v).updateRow l w := by
    funext k j
    change ((A.updateRow i w).updateRow l v) (Equiv.swap i l k) j = _
    by_cases hki : k = i
    · subst k
      simp [hil]
    by_cases hkl : k = l
    · subst k
      simp [hil]
    · simp [Equiv.swap_apply_of_ne_of_ne hki hkl, hki, hkl]
  have hs := (Matrix.detRowAlternating : (ι → ℝ) [⋀^ι]→ₗ[ℝ] ℝ).map_swap
    (fun k => ((A.updateRow i w).updateRow l v) k) hil
  rw [show (fun k => ((A.updateRow i w).updateRow l v) k) ∘ Equiv.swap i l =
      (fun k => ((A.updateRow i v).updateRow l w) k) from hm] at hs
  exact hs

/-- Expand one determinant row in the coordinate vectors. -/
theorem det_updateRow_sum (A : Matrix ι ι ℝ) (l : ι) (v : ι → ℝ) :
    (A.updateRow l v).det = ∑ m, v m * (A.updateRow l (Pi.single m 1)).det := by
  have hv : v = ∑ m, v m • Pi.single m (1 : ℝ) := by
    ext k
    simp [Pi.single_apply, Finset.sum_apply]
  calc
    (A.updateRow l v).det =
        ∑ m, (A.updateRow l (v m • Pi.single m 1)).det := by
      conv_lhs => rw [hv]
      exact (Matrix.detRowAlternating : (ι → ℝ) [⋀^ι]→ₗ[ℝ] ℝ).map_update_sum
        Finset.univ l (fun m => v m • Pi.single m (1 : ℝ)) (fun k => A k)
    _ = _ := Finset.sum_congr rfl fun m _ => Matrix.det_updateRow_smul A l (v m) _

/-- Symmetric coefficients contract to zero with an alternating pair of rows. -/
theorem sum_two_rows_eq_zero (A : Matrix ι ι ℝ) {i l : ι} (hil : i ≠ l)
    (T : ι → ι → ℝ) (hT : ∀ j m, T j m = T m j) :
    (∑ j, ∑ m, T j m *
      ((A.updateRow i (Pi.single j 1)).updateRow l (Pi.single m 1)).det) = 0 := by
  let S := ∑ j, ∑ m, T j m *
      ((A.updateRow i (Pi.single j 1)).updateRow l (Pi.single m 1)).det
  have hs : S = -S := by
    dsimp [S]
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro m hm
    rw [hT m j]
    exact (congrArg (fun r : ℝ => T j m * r)
      (det_updateRow_pair_swap A hil (Pi.single m 1) (Pi.single j 1))).trans
      (mul_neg _ _)
  change S = 0
  linarith

/-- The algebraic cancellation underlying the Piola identity. -/
theorem piola_cancel (A : Matrix ι ι ℝ) (i : ι) (T : ι → ι → ι → ℝ)
    (hT : ∀ l j m, T l j m = T l m j) :
    (∑ j, ∑ l, ((A.updateRow i (Pi.single j 1)).updateRow l
      (if l = i then 0 else T l j)).det) = 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro l hl
  by_cases hli : l = i
  · subst l
    apply Finset.sum_eq_zero
    intro j hj
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro m
    simp
  · simp only [ite_eq_right hli]
    calc
      _ = ∑ j, ∑ m, T l j m *
          ((A.updateRow i (Pi.single j 1)).updateRow l (Pi.single m 1)).det :=
        Finset.sum_congr rfl fun j _ => det_updateRow_sum _ l _
      _ = 0 := sum_two_rows_eq_zero A (Ne.symm hli) (T l) (hT l)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_PositiveDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
theorem contDiffAt_gradient {H : E → ℝ} {e : E} (hh : ContDiffAt ℝ ∞ H e) :
    ContDiffAt ℝ ∞ (gradient H) e :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp
    e (hh.fderiv_right (by simp))

end

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AngularCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Orthogonal tangential projection when `e` is a unit vector. -/

omit [CompleteSpace E] in
theorem tangentProjection_eq {e v : E} (hv : inner ℝ e v = 0) :
    tangentProjection e v = v := by simp [tangentProjection, hv]

theorem hasFDerivAt_tangentProjection (e v : E) :
    HasFDerivAt (fun x => tangentProjection x v)
      (-(inner ℝ e v • ContinuousLinearMap.id ℝ E +
        (InnerProductSpace.toDual ℝ E v).smulRight e)) e := by
  have hd := (hasFDerivAt_const v e).sub
    ((InnerProductSpace.toDual ℝ E v).hasFDerivAt.smul (hasFDerivAt_id e))
  convert hd using 1
  · ext x; simp [tangentProjection, real_inner_comm]
  · simp [real_inner_comm]

/- The covariant derivative of an ambient two-tensor restricted to the sphere.
The arguments `u,v,w` are tangent at the unit point of evaluation. The projected
constant extensions of `v,w` have zero covariant derivative there. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CofactorCodazzi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_adjugate_entries (M : E → Matrix ι ι ℝ) (x : E)
    (hM : ∀ l m, DifferentiableAt ℝ (fun y => M y l m) x) (i j : ι) (v : E) :
    fderiv ℝ (fun y => (M y).adjugate j i) x v =
      ∑ l, (((M x).updateRow i (Pi.single j 1)).updateRow l
        (if l = i then 0 else fun m => fderiv ℝ (fun y => M y l m) x v)).det := by
  let N : E → (ι → ι → ℝ) := fun y =>
    Function.update (fun l m => M y l m) i (Pi.single j 1)
  let D : E →L[ℝ] (ι → ι → ℝ) := ContinuousLinearMap.pi fun l =>
    if l = i then 0 else ContinuousLinearMap.pi fun m => fderiv ℝ (fun y => M y l m) x
  have hD : HasFDerivAt N D x := by
    dsimp [N, D]
    apply hasFDerivAt_pi.mpr
    intro l
    by_cases hli : l = i
    · subst l
      simp only [Function.update_self, ite_true]
      exact hasFDerivAt_const (Pi.single j 1) x
    · simp only [Function.update_of_ne hli, ite_eq_right hli]
      exact hasFDerivAt_pi.mpr (fun m => (hM l m).hasFDerivAt)
  have hAdj : (fun y => (M y).adjugate j i) = continuousDetRows ∘ N := by
    funext y
    rw [Matrix.adjugate_apply]
    rfl
  have hc := (continuousDetRows.hasFDerivAt (N x)).comp x hD
  rw [hAdj, hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hli : l = i
  · subst l
    simp only [D, ContinuousLinearMap.pi_apply, ite_true, zero_apply]
    rfl
  · simp only [D, ContinuousLinearMap.pi_apply, ite_eq_right hli]
    rfl

/- Cofactor divergence vanishes for every differentiable Codazzi matrix field,
including size one and the empty angular block. No invertibility is required. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AngularCofactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem third_derivative_swap_last {H : E → ℝ} {e : E}
    (hh : ContDiffAt ℝ ∞ H e) (u v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ H)) e u v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ H)) e u w v := by
  have hd := ((hh.fderiv_right (m := ∞) (by simp)).fderiv_right
    (m := ∞) (by simp)).differentiableAt (by simp)
  have he : (fun y => fderiv ℝ (fderiv ℝ H) y v w) =ᶠ[𝓝 e]
      (fun y => fderiv ℝ (fderiv ℝ H) y w v) := by
    filter_upwards [(hh.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually
      (by simp)] with q hq
    exact (hq.isSymmSndFDerivAt (by norm_num)).eq v w
  have hdv := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v e)).clm_apply
    (hasFDerivAt_const w e)
  have hdw := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const w e)).clm_apply
    (hasFDerivAt_const v e)
  have heq := (hdv.congr_of_eventuallyEq he.symm).unique hdw
  have hev := congrArg (fun L : E →L[ℝ] ℝ => L u) heq
  simpa using hev

/- Radius matrix in projected constant tangent frames. At a unit `e` and an
orthonormal tangent frame this is exactly `∇²_S h + h Id`; its first derivatives
are the round covariant derivatives in a normal frame. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeChartConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
lemma tube_dimension_equiv {n : ℕ}
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (L : (S × E) ≃L[ℝ] (Space n × ℝ)) : Nonempty (Fin n ≃ ι ⊕ κ) := by
  let : FiniteDimensional ℝ S := Module.Finite.of_basis bS
  let : FiniteDimensional ℝ E := Module.Finite.of_basis bE.toBasis
  have hdim := L.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod,Module.finrank_prod,Module.finrank_eq_card_basis bS,
    Module.finrank_eq_card_basis bE.toBasis] at hdim
  simp only [Fintype.card_sum,Fintype.card_unit,Module.finrank_self,
    finrank_euclideanSpace,Fintype.card_fin] at hdim
  apply Fintype.card_eq.mp
  simp only [Fintype.card_fin,Fintype.card_sum]
  omega

/- An actual flat-normal coordinate injection with a continuous linear left
inverse. These chart data are produced from the frames, not postulated. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeWeightAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/- Literal invariant tube measure coefficient with respect to `ds dω`. -/

lemma tubeMeasureCoefficient_pos {n : ℕ} {h B Q : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hQ : 0 < Q) :
    0 < tubeMeasureCoefficient n h B Q :=
  mul_pos (Real.rpow_pos_of_pos hh _) (Real.sqrt_pos.2 (mul_pos hB hQ))

lemma tubeMeasureCoefficient_angular {n : ℕ} {h B Q : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hQ : 0 < Q) :
    tubeMeasureCoefficient n h B Q*h/Q =
      Real.exp (2*Real.log h + (((n : ℝ)+2)/2)*
        ((Real.log B-Real.log Q)/((n : ℝ)+2)-Real.log h)) := by
  have hN : (n : ℝ)+2 ≠ 0 := by positivity
  have hl : 0 < tubeMeasureCoefficient n h B Q*h/Q :=
    div_pos (mul_pos (tubeMeasureCoefficient_pos hh hB hQ) hh) hQ
  rw [← Real.exp_log hl]
  congr 1
  rw [Real.log_div (mul_ne_zero (tubeMeasureCoefficient_pos hh hB hQ).ne' hh.ne') hQ.ne',
    Real.log_mul (tubeMeasureCoefficient_pos hh hB hQ).ne' hh.ne']
  unfold tubeMeasureCoefficient
  rw [Real.log_mul (Real.rpow_pos_of_pos hh _).ne' (Real.sqrt_pos.2 (mul_pos hB hQ)).ne',
    Real.log_rpow hh,Real.log_sqrt (mul_pos hB hQ).le,Real.log_mul hB.ne' hQ.ne']
  field_simp
  ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualTubeWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- The manuscript's invariant density `μ₀` on base times unit normals. -/

omit [DecidableEq ι] [DecidableEq κ] in
lemma tube_dimension_eq {n : ℕ} (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (L : (S × E) ≃L[ℝ] (Space n × ℝ)) : n = Fintype.card ι+Fintype.card κ := by
  obtain ⟨j⟩ := tube_dimension_equiv bS bE L
  simpa only [Fintype.card_fin,Fintype.card_sum] using Fintype.card_congr j

lemma invariantTubeF_unit {n : ℕ} (H : S × E → ℝ) (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hn : n = Fintype.card ι+Fintype.card κ) {q : S × E} (he : ‖q.2‖ = 1) :
    invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2)) q =
      (Real.log (tubeBaseMatrix H q bS).det-Real.log (tubeAngularDensity H q bE))/((n : ℝ)+2)-
        Real.log (H q) := by
  simp only [invariantTubeF,real_inner_self_eq_norm_sq,he,one_pow,Real.log_one,add_zero,hn,Nat.cast_add]
  ring

lemma tubeMeasureDensity_angular {n : ℕ} {H : S × E → ℝ} (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hn : n = Fintype.card ι+Fintype.card κ) {q : S × E} (he : ‖q.2‖ = 1)
    (hh : 0 < H q) (hB : 0 < (tubeBaseMatrix H q bS).det) (hQ : 0 < tubeAngularDensity H q bE) :
    tubeMeasureDensity n H bS bE q*H q/tubeAngularDensity H q bE =
      Real.exp (2*Real.log (H q)+(((n : ℝ)+2)/2)*
        invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2)) q) := by
  rw [invariantTubeF_unit H bS bE hn he]
  exact tubeMeasureCoefficient_angular hh hB hQ

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricVariationAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma contDiff_adjugate_entry (i j : ι) :
    ContDiff ℝ ∞ (fun A : ι → ι → ℝ => Matrix.adjugate (Matrix.of A) i j) := by
  simp only [Matrix.adjugate_apply]
  change ContDiff ℝ ∞ (continuousDetRows ∘ fun A : ι → ι → ℝ =>
    fun l m => Matrix.updateRow (Matrix.of A) j (Pi.single i 1) l m)
  apply (continuousDetRows (ι := ι)).contDiff.comp
  apply contDiff_pi.mpr
  intro l
  by_cases hl : l = j
  · subst l
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne hl, Matrix.of_apply]
    fun_prop

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NewtonPiola
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma fderiv_piMatrix_entry (A V : ι → ι → ℝ) (l m : ι) :
    fderiv ℝ (fun B : ι → ι → ℝ => Matrix.of B l m) A V = V l m := by
  change fderiv ℝ (fun B : ι → ι → ℝ => B l m) A V = V l m
  rw [fderiv_apply (by fun_prop), fderiv_apply (by fun_prop)]
  simp

lemma adjugate_linear_piola (A : ι → ι → ℝ) (V : ι → ι → ι → ℝ)
    (hV : ∀ l j m, V j l m = V m l j) (i : ι) :
    (∑ j, fderiv ℝ (fun B : ι → ι → ℝ => (Matrix.of B).adjugate j i) A (V j)) = 0 := by
  have hh (j : ι) := fderiv_adjugate_entries (fun B : ι → ι → ℝ => Matrix.of B) A
    (fun l m => by change DifferentiableAt ℝ (fun B : ι → ι → ℝ => B l m) A; fun_prop) i j (V j)
  simp only [fderiv_piMatrix_entry] at hh
  simp_rw [hh]
  exact piola_cancel (Matrix.of A) i (fun l j m => V j l m) hV

lemma piMatrix_shift_hasDerivAt (A : ι → ι → ℝ) :
    HasDerivAt (fun t : ℝ => fun l m => A l m + t * (1 : Matrix ι ι ℝ) l m)
      (fun l m => (1 : Matrix ι ι ℝ) l m) 0 := by
  apply hasDerivAt_pi.mpr
  intro l
  apply hasDerivAt_pi.mpr
  intro m
  simpa only [one_mul, id_eq] using ((hasDerivAt_id (0 : ℝ)).mul_const
    ((1 : Matrix ι ι ℝ) l m)).const_add (A l m)

/- The linearized Piola cancellation is the divergence identity for the
penultimate Newton tensor. -/
lemma newton_linear_piola (A : ι → ι → ℝ) (V : ι → ι → ι → ℝ)
    (hV : ∀ l j m, V j l m = V m l j) (i : ι) :
    (∑ j, fderiv ℝ (fderiv ℝ (fun B : ι → ι → ℝ => (Matrix.of B).adjugate j i)) A
      (V j) (fun l m => (1 : Matrix ι ι ℝ) l m)) = 0 := by
  let I : ι → ι → ℝ := fun l m => (1 : Matrix ι ι ℝ) l m
  have hz : (fun t : ℝ => ∑ j, fderiv ℝ
      (fun B : ι → ι → ℝ => (Matrix.of B).adjugate j i)
      (fun l m => A l m + t * I l m) (V j)) = fun _ => 0 := by
    funext t
    exact adjugate_linear_piola _ V hV i
  have hdj (j : ι) : HasDerivAt (fun t : ℝ => fderiv ℝ
      (fun B : ι → ι → ℝ => (Matrix.of B).adjugate j i)
      (fun l m => A l m + t * I l m) (V j))
      (fderiv ℝ (fderiv ℝ (fun B : ι → ι → ℝ => (Matrix.of B).adjugate j i)) A I (V j)) 0 := by
    let G : (ι → ι → ℝ) → ℝ := fun B => (Matrix.of B).adjugate j i
    have hs : ContDiff ℝ ∞ G := contDiff_adjugate_entry j i
    have hh : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) A) A :=
      ((hs.fderiv_right (m := ∞) (by simp)).differentiable (by simp) A).hasFDerivAt
    have hh' : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) A)
        (fun l m => A l m + (0 : ℝ) * I l m) := by
      simpa only [zero_mul, add_zero] using hh
    have hc : HasDerivAt (fun t : ℝ => fderiv ℝ G (fun l m => A l m + t * I l m))
        (fderiv ℝ (fderiv ℝ G) A I) 0 :=
      hh'.comp_hasDerivAt 0 (piMatrix_shift_hasDerivAt A)
    have hk : HasDerivAt (fun t : ℝ => fderiv ℝ G (fun l m => A l m + t * I l m) (V j))
        (fderiv ℝ (fderiv ℝ G) A I (V j) + fderiv ℝ G A 0) 0 := by
      convert hc.clm_apply (hasDerivAt_const (0 : ℝ) (V j)) using 1
      all_goals try with_reducible_and_instances rfl
      simp only [zero_mul, add_zero]
    simpa only [map_zero, add_zero] using hk
  have hd := (HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => hdj j)).deriv
  rw [hz, deriv_const] at hd
  rw [hd]
  apply Finset.sum_congr rfl
  intro j _
  exact ((contDiff_adjugate_entry j i).contDiffAt.isSymmSndFDerivAt
    (by simp)).eq (V j) I

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NewtonTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- The penultimate Newton tensor, defined polynomially, not using an inverse. -/

theorem contDiff_newtonTensor_entry (i j : ι) :
    ContDiff ℝ ∞ (fun A : ι → ι → ℝ => newtonTensor (Matrix.of A) i j) := by
  exact ((contDiff_adjugate_entry i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem newtonTensor_eq_deriv (A : Matrix ι ι ℝ) (i j : ι) :
    newtonTensor A i j = deriv (fun t : ℝ => (A + t • 1).adjugate i j) 0 := by
  have hd : HasDerivAt (fun t : ℝ => fun l m => (A + t • 1) l m)
      (fun l m => (1 : Matrix ι ι ℝ) l m) 0 := by
    apply hasDerivAt_pi.mpr
    intro l
    apply hasDerivAt_pi.mpr
    intro m
    change HasDerivAt (fun t : ℝ => A l m + t * (1 : Matrix ι ι ℝ) l m)
      ((1 : Matrix ι ι ℝ) l m) 0
    simpa only [one_mul, id_eq] using ((hasDerivAt_id (0 : ℝ)).mul_const
      ((1 : Matrix ι ι ℝ) l m)).const_add (A l m)
  have hA : HasFDerivAt (fun B : ι → ι → ℝ => Matrix.adjugate (Matrix.of B) i j)
      (fderiv ℝ (fun B : ι → ι → ℝ => Matrix.adjugate (Matrix.of B) i j) (fun l m => A l m))
      (fun l m => (A + (0 : ℝ) • 1) l m) := by
    simpa using ((contDiff_adjugate_entry i j).differentiable (by simp) (fun l m => A l m)).hasFDerivAt
  have hh := hA.comp_hasDerivAt 0 hd
  have hη (C : Matrix ι ι ℝ) : Matrix.of (fun l m => C l m) = C := by
    ext l m
    rfl
  simpa only [newtonTensor, Function.comp_def, hη] using hh.deriv.symm

theorem newtonTensor_isSymm {A : Matrix ι ι ℝ} (hA : A.IsSymm) :
    (newtonTensor A).IsSymm := by
  have he (t : ℝ) : (A + t • (1 : Matrix ι ι ℝ)).adjugate.IsSymm :=
    (hA.add (Matrix.isSymm_one.smul t)).adjugate
  ext i j
  simp only [Matrix.transpose_apply, newtonTensor_eq_deriv]
  congr 1
  funext t
  exact congrFun (congrFun (he t) i) j

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NewtonField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_newtonTensor_entry (A V : ι → ι → ℝ) (i j : ι) :
    fderiv ℝ (fun B : ι → ι → ℝ => newtonTensor (Matrix.of B) i j) A V =
      fderiv ℝ (fderiv ℝ (fun B : ι → ι → ℝ => (Matrix.of B).adjugate i j)) A V
        (fun l m => (1 : Matrix ι ι ℝ) l m) := by
  let G : (ι → ι → ℝ) → ℝ := fun B => (Matrix.of B).adjugate i j
  let I : ι → ι → ℝ := fun l m => (1 : Matrix ι ι ℝ) l m
  have hd : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) A) A :=
    (((contDiff_adjugate_entry i j).fderiv_right (m := ∞) (by simp)).differentiable
      (by simp) A).hasFDerivAt
  have hh := hd.clm_apply (hasFDerivAt_const I A)
  have he : (fun B : ι → ι → ℝ => newtonTensor (Matrix.of B) i j) =
      fun B => fderiv ℝ G B I := rfl
  rw [he, hh.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, map_zero, zero_add]
  rfl

/- Newton divergence for a genuine differentiable Codazzi field in constant
coordinates. Its sole tensor hypothesis is the third derivative symmetry. -/
theorem newtonTensor_divergence_of_codazzi (M : E → Matrix ι ι ℝ) (x : E) (e : ι → E)
    (hM : ∀ l m, DifferentiableAt ℝ (fun y => M y l m) x)
    (hCodazzi : ∀ l j m, fderiv ℝ (fun y => M y l m) x (e j) =
      fderiv ℝ (fun y => M y l j) x (e m)) (i : ι) :
    (∑ j, fderiv ℝ (fun y => newtonTensor (M y) j i) x (e j)) = 0 := by
  let B : E → ι → ι → ℝ := fun y l m => M y l m
  have hdB : DifferentiableAt ℝ B x := differentiableAt_pi.mpr fun l =>
    differentiableAt_pi.mpr (hM l)
  have he (j : ι) : fderiv ℝ (fun y => newtonTensor (M y) j i) x (e j) =
      fderiv ℝ (fderiv ℝ (fun A : ι → ι → ℝ => (Matrix.of A).adjugate j i)) (B x)
        (fun l m => fderiv ℝ (fun y => M y l m) x (e j))
        (fun l m => (1 : Matrix ι ι ℝ) l m) := by
    have hη (y : E) : Matrix.of (B y) = M y := by ext l m; rfl
    have hc := ((contDiff_newtonTensor_entry j i).differentiable (by simp) (B x)).hasFDerivAt.comp x
      hdB.hasFDerivAt
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L (e j)) hc.fderiv
    simp only [Function.comp_def, hη, ContinuousLinearMap.comp_apply] at hh
    let D : E →L[ℝ] (ι → ι → ℝ) := ContinuousLinearMap.pi fun l =>
      ContinuousLinearMap.pi fun m => fderiv ℝ (fun y => M y l m) x
    have hBD : HasFDerivAt B D x := hasFDerivAt_pi.mpr fun l =>
      hasFDerivAt_pi.mpr fun m => (hM l m).hasFDerivAt
    rw [hh, fderiv_newtonTensor_entry, hBD.fderiv]
    rfl
  simp_rw [he]
  apply newton_linear_piola (B x) (fun j l m => fderiv ℝ (fun y => M y l m) x (e j))
  intro l j m
  exact hCodazzi l j m

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SmoothParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section SmoothParameter
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/- A twice differentiated eigenvector equation, still valid at a singular
matrix and in dimension one. -/
theorem second_deriv_smul_id {g : ℝ → F} (hg : ContDiff ℝ ∞ g) :
    deriv (deriv (fun t : ℝ => t • g t)) 0 = 2 • deriv g 0 := by
  have hdg (t : ℝ) : HasDerivAt g (deriv g t) t :=
    (hg.differentiable (by simp) t).hasDerivAt
  have he : deriv (fun t : ℝ => t • g t) = fun t => g t + t • deriv g t := by
    funext t
    simpa only [one_smul, id_eq, Pi.smul_def', add_comm] using ((hasDerivAt_id t).smul (hdg t)).deriv
  rw [he]
  have hddg : DifferentiableAt ℝ (deriv g) 0 :=
    ((hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).differentiable_deriv_two) 0
  have hh := (hdg 0).add ((hasDerivAt_id (0 : ℝ)).smul hddg.hasDerivAt)
  simpa only [zero_smul, one_smul, add_zero, two_smul, Pi.add_def, Pi.smul_def', id_eq, zero_add] using hh.deriv

end SmoothParameter

open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma contDiff_adjugate_shift (A : Matrix ι ι ℝ) (i j : ι) :
    ContDiff ℝ ∞ (fun t : ℝ => (A + t • 1).adjugate i j) := by
  apply (contDiff_adjugate_entry i j).comp
  change ContDiff ℝ ∞ (fun t : ℝ => fun l m => (A + t • 1) l m)
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

lemma contDiff_det_shift (A : Matrix ι ι ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => (A + t • 1).det) := by
  change ContDiff ℝ ∞ (continuousDetRows ∘ fun t : ℝ => fun l m => (A + t • 1) l m)
  apply (continuousDetRows (ι := ι)).contDiff.comp
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

/- A radial null vector of the Hessian is an eigenvector of its Newton
polynomial. No nonsingularity, division by a determinant, or limiting inverse
is used. -/
theorem newtonTensor_radial {A : Matrix ι ι ℝ} {v : ι → ℝ}
    (hv : A *ᵥ v = 0) : ∃ c : ℝ, newtonTensor A *ᵥ v = c • v := by
  let f : ℝ → ℝ := fun t => (A + t • 1).det
  have hf : ContDiff ℝ ∞ f := contDiff_det_shift A
  have hdf : Differentiable ℝ (deriv f) :=
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).differentiable_deriv_two
  refine ⟨deriv (deriv f) 0 / 2, ?_⟩
  ext i
  let g : ℝ → ℝ := fun t => ((A + t • 1).adjugate *ᵥ v) i
  have hg : ContDiff ℝ ∞ g := by
    change ContDiff ℝ ∞ (fun t : ℝ => ∑ j, (A + t • 1).adjugate i j * v j)
    exact ContDiff.sum (fun j _ => (contDiff_adjugate_shift A i j).mul contDiff_const)
  have he : (fun t : ℝ => t • g t) = fun t => f t * v i := by
    funext t
    have hB : (A + t • (1 : Matrix ι ι ℝ)) *ᵥ v = t • v := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv, zero_add]
    have hb := congrFun (show t • ((A + t • (1 : Matrix ι ι ℝ)).adjugate *ᵥ v) =
        f t • v by
      rw [← Matrix.mulVec_smul, ← hB, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
        Matrix.smul_mulVec, Matrix.one_mulVec]) i
    exact hb
  have hsecond : deriv (deriv (fun t => f t * v i)) 0 = deriv (deriv f) 0 * v i := by
    have hh : deriv (fun t => f t * v i) = fun t => deriv f t * v i := by
      funext t
      exact ((hf.differentiable (by simp) t).hasDerivAt.mul_const (v i)).deriv
    rw [hh]
    exact ((hdf 0).hasDerivAt.mul_const (v i)).deriv
  have he2 := congrArg (fun k : ℝ → ℝ => deriv (deriv k) 0) he
  rw [second_deriv_smul_id hg, hsecond] at he2
  have hg' : deriv g 0 = (newtonTensor A *ᵥ v) i := by
    have hh : HasDerivAt g (∑ j, newtonTensor A i j * v j) 0 := by
      apply HasDerivAt.fun_sum
      intro j _
      rw [newtonTensor_eq_deriv]
      exact ((contDiff_adjugate_shift A i j).differentiable (by simp) 0).hasDerivAt.mul_const (v j)
    exact hh.deriv
  rw [hg'] at he2
  simp only [two_smul, smul_eq_mul, Pi.smul_apply] at he2 ⊢
  linarith

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SphereTensorCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma fderiv_bilinear_field {T : E → E →L[ℝ] E →L[ℝ] ℝ} {u v : E → E} {x : E}
    (hT : DifferentiableAt ℝ T x) (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (z : E) :
    fderiv ℝ (fun q => T q (u q) (v q)) x z =
      fderiv ℝ T x z (u x) (v x) + T x (fderiv ℝ u x z) (v x) +
        T x (u x) (fderiv ℝ v x z) := by
  rw [((hT.hasFDerivAt.clm_apply hu.hasFDerivAt).clm_apply hv.hasFDerivAt).fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  ring

/- Derivatives of the radial eigenspace remain radial in the radial direction.
The polynomial identity avoids differentiating an arbitrarily chosen eigenvalue. -/
lemma radial_tensor_derivative {T : E → E →L[ℝ] E →L[ℝ] ℝ} {e v : E}
    (hT : DifferentiableAt ℝ T e) (he : inner ℝ e e = 1) (hv : inner ℝ e v = 0)
    (hr : ∀ᶠ q in 𝓝 e, T q q v * inner ℝ q q = T q q q * inner ℝ q v) :
    fderiv ℝ T e e e v = 0 := by
  have hv0 : T e e v = 0 := by
    have hh := hr.self_of_nhds
    simpa only [he, hv, mul_one, mul_zero] using hh
  have h1 : DifferentiableAt ℝ (fun q => T q q v) e :=
    (hT.clm_apply differentiableAt_id).clm_apply (differentiableAt_const v)
  have h2 : DifferentiableAt ℝ (fun q => T q q q) e :=
    (hT.clm_apply differentiableAt_id).clm_apply differentiableAt_id
  have hn : DifferentiableAt ℝ (fun q : E => inner ℝ q q) e :=
    differentiableAt_id.inner ℝ differentiableAt_id
  have hvd : DifferentiableAt ℝ (fun q : E => inner ℝ q v) e :=
    differentiableAt_id.inner ℝ (differentiableAt_const v)
  have heq : (fun q => T q q v * inner ℝ q q) =ᶠ[𝓝 e]
      (fun q => T q q q * inner ℝ q v) := hr
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L e) heq.fderiv_eq
  have hd1 := (h1.hasFDerivAt.mul hn.hasFDerivAt).fderiv
  have hd2 := (h2.hasFDerivAt.mul hvd.hasFDerivAt).fderiv
  simp only [Pi.mul_def] at hd1 hd2
  rw [hd1, hd2] at hh
  simp only [add_apply, smul_apply, smul_eq_mul, he, hv, hv0, zero_mul,
    add_zero, zero_add] at hh
  have hvd' : fderiv ℝ (fun q : E => inner ℝ q v) e e = 0 := by
    have hG : (fun q : E => inner ℝ q v) = InnerProductSpace.toDual ℝ E v := by
      ext q; simp [real_inner_comm]
    rw [hG, (InnerProductSpace.toDual ℝ E v).fderiv]
    simpa only [InnerProductSpace.toDual_apply_apply, real_inner_comm] using hv
  rw [hvd', mul_zero] at hh
  have hdf := fderiv_bilinear_field hT differentiableAt_id (differentiableAt_const v) e
  simp only [id_eq, fderiv_id, ContinuousLinearMap.id_apply, fderiv_const_apply, zero_apply,
    hv0, map_zero, add_zero] at hdf
  rw [hdf] at hh
  simpa only [one_mul] using hh

lemma roundTensorDerivative_eq_of_radial {T : E → E →L[ℝ] E →L[ℝ] ℝ} {e : E}
    (hT : DifferentiableAt ℝ T e) (u v w : E)
    (hv : inner ℝ e v = 0) (hw : inner ℝ e w = 0)
    (hrv : T e v e = 0) (hrw : T e e w = 0) :
    roundTensorDerivative T e u v w = fderiv ℝ T e u v w := by
  unfold roundTensorDerivative
  rw [fderiv_bilinear_field hT (hasFDerivAt_tangentProjection e v).differentiableAt
    (hasFDerivAt_tangentProjection e w).differentiableAt,
    (hasFDerivAt_tangentProjection e v).fderiv,
    (hasFDerivAt_tangentProjection e w).fderiv]
  simp only [tangentProjection_eq hv, tangentProjection_eq hw,
    neg_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    InnerProductSpace.toDual_apply_apply,
    hv, hw, zero_smul, zero_add, map_neg, map_smul, smul_eq_mul,
    hrv, hrw, mul_zero, neg_zero, add_zero]

variable {ι : Type*} [Fintype ι]

omit [CompleteSpace E] in
lemma trace_projected_bilinear (b : OrthonormalBasis ι ℝ E)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (e : E) (he : inner ℝ e e = 1) :
    (∑ i, A (tangentProjection e (b i)) (tangentProjection e (b i))) =
      (∑ i, A (b i) (b i)) - A e e := by
  simp only [tangentProjection, map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib, mul_sub]
  have hone : (∑ i, inner ℝ e (b i) • b i) = e := by
    simpa only [real_inner_comm e] using b.sum_repr' e
  have h1 : (∑ i, inner ℝ e (b i) * A (b i) e) = A e e := by
    have hh := congrArg (fun z => A z e) hone
    simpa only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul] using hh
  have h2 : (∑ i, inner ℝ e (b i) * A e (b i)) = A e e := by
    have hh := congrArg (A e) hone
    simpa only [map_sum, map_smul, smul_eq_mul] using hh
  have h3 : (∑ i, inner ℝ e (b i) * (inner ℝ e (b i) * A e e)) = A e e := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    have hh : (∑ i, inner ℝ e (b i) * inner ℝ e (b i)) = 1 := by
      simpa only [real_inner_comm e] using (b.sum_inner_mul_inner e e).trans he
    rw [hh, one_mul]
  rw [h1, h2, h3]
  ring

/- Tangential divergence of the restricted Newton tensor. Both normal
corrections vanish by genuine radial invariance, not as an IBP assumption. -/
theorem projected_tensor_divergence (b : OrthonormalBasis ι ℝ E)
    {T : E → E →L[ℝ] E →L[ℝ] ℝ} {e v : E}
    (hT : DifferentiableAt ℝ T e) (he : inner ℝ e e = 1) (hv : inner ℝ e v = 0)
    (hs : ∀ u w, T e u w = T e w u)
    (hr : ∀ᶠ q in 𝓝 e, ∀ w, T q q w * inner ℝ q q = T q q q * inner ℝ q w)
    (hdiv : ∀ w, (∑ i, fderiv ℝ T e (b i) (b i) w) = 0) :
    (∑ i, roundTensorDerivative T e (tangentProjection e (b i))
      (tangentProjection e (b i)) v) = 0 := by
  have hrv : T e e v = 0 := by
    have hh := hr.self_of_nhds v
    simpa only [he, hv, mul_one, mul_zero] using hh
  have hp (i : ι) : inner ℝ e (tangentProjection e (b i)) = 0 := by
    simp only [tangentProjection, inner_sub_right, real_inner_smul_right, he, mul_one, sub_self]
  have hrp (i : ι) : T e (tangentProjection e (b i)) e = 0 := by
    rw [hs]
    have hh := hr.self_of_nhds (tangentProjection e (b i))
    simpa only [he, hp, mul_one, mul_zero] using hh
  simp_rw [roundTensorDerivative_eq_of_radial hT _ _ _ (hp _) hv (hrp _) hrv]
  let A : E →L[ℝ] E →L[ℝ] ℝ := (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) ℝ
    (ContinuousLinearMap.apply ℝ ℝ v)).comp (fderiv ℝ T e)
  have htrace : (∑ i, fderiv ℝ T e (tangentProjection e (b i))
      (tangentProjection e (b i)) v) =
      (∑ i, fderiv ℝ T e (b i) (b i) v) - fderiv ℝ T e e e v := by
    exact trace_projected_bilinear b A e he
  rw [htrace, hdiv, radial_tensor_derivative hT he hv (hr.mono fun q hq => hq v), sub_zero]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_BilinearNewton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open scoped Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma bilinearOfMatrix_apply (b : OrthonormalBasis ι ℝ E) (A : Matrix ι ι ℝ) (v w : E) :
    bilinearOfMatrix b A v w = ∑ i, ∑ j, A i j * inner ℝ (b i) v * inner ℝ (b j) w := by
  simp only [bilinearOfMatrix, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    InnerProductSpace.toDual_apply_apply, smul_eq_mul, mul_assoc]

lemma bilinearOfMatrix_basis (b : OrthonormalBasis ι ℝ E) (A : Matrix ι ι ℝ) (i j : ι) :
    bilinearOfMatrix b A (b i) (b j) = A i j := by
  rw [bilinearOfMatrix_apply]
  simp [orthonormal_iff_ite.mp b.orthonormal]

omit [DecidableEq ι] in
lemma bilinearOfMatrix_symm (b : OrthonormalBasis ι ℝ E) {A : Matrix ι ι ℝ}
    (hA : A.IsSymm) (v w : E) : bilinearOfMatrix b A v w = bilinearOfMatrix b A w v := by
  have hs (i j : ι) : A i j = A j i := congrFun (congrFun hA j) i
  simp only [bilinearOfMatrix_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hs]
  ring

omit [DecidableEq ι] in
lemma bilinearOfMatrix_radial (b : OrthonormalBasis ι ℝ E) {A : Matrix ι ι ℝ}
    (hA : A.IsSymm) {e : E} {c : ℝ}
    (he : A *ᵥ (fun i => inner ℝ (b i) e) = c • (fun i => inner ℝ (b i) e)) (v : E) :
    bilinearOfMatrix b A e v = c * inner ℝ e v := by
  have hs (i j : ι) : A i j = A j i := congrFun (congrFun hA j) i
  rw [bilinearOfMatrix_apply, Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  have hm (j : ι) : (∑ i, A i j * inner ℝ (b i) e) = c * inner ℝ (b j) e := by
    simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hs] using congrFun he j
  simp_rw [hm, mul_assoc]
  rw [← Finset.mul_sum]
  have hinner : (∑ j, inner ℝ (b j) e * inner ℝ (b j) v) = inner ℝ e v := by
    simpa only [real_inner_comm e] using b.sum_inner_mul_inner e v
  rw [hinner]

omit [DecidableEq ι] in
lemma contDiffAt_bilinearOfMatrix (b : OrthonormalBasis ι ℝ E)
    {M : E → Matrix ι ι ℝ} {x : E} (hM : ∀ i j, ContDiffAt ℝ ∞ (fun q => M q i j) x) :
    ContDiffAt ℝ ∞ (fun q => bilinearOfMatrix b (M q)) x := by
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    @NormedSpace.toIsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) _ _ _
  unfold bilinearOfMatrix
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => (hM i j).smul contDiffAt_const

lemma fderiv_bilinearOfMatrix_basis (b : OrthonormalBasis ι ℝ E)
    {M : E → Matrix ι ι ℝ} {x : E}
    (hM : DifferentiableAt ℝ (fun q => bilinearOfMatrix b (M q)) x) (i j : ι) (v : E) :
    fderiv ℝ (fun q => bilinearOfMatrix b (M q)) x v (b i) (b j) =
      fderiv ℝ (fun q => M q i j) x v := by
  have he : (fun q => bilinearOfMatrix b (M q) (b i) (b j)) = fun q => M q i j := by
    funext q; exact bilinearOfMatrix_basis b (M q) i j
  have hh := fderiv_bilinear_field hM (differentiableAt_const (b i))
    (differentiableAt_const (b j)) v
  rw [he] at hh
  simpa only [fderiv_const_apply, zero_apply, map_zero, zero_apply, add_zero] using hh.symm

lemma bilinearOfMatrix_field_divergence (b : OrthonormalBasis ι ℝ E)
    {M : E → Matrix ι ι ℝ} {x : E}
    (hM : DifferentiableAt ℝ (fun q => bilinearOfMatrix b (M q)) x)
    (hd : ∀ j, (∑ i, fderiv ℝ (fun q => M q i j) x (b i)) = 0) (v : E) :
    (∑ i, fderiv ℝ (fun q => bilinearOfMatrix b (M q)) x (b i) (b i) v) = 0 := by
  have hv (i : ι) : fderiv ℝ (fun q => bilinearOfMatrix b (M q)) x (b i) (b i) v =
      ∑ j, inner ℝ (b j) v * fderiv ℝ (fun q => M q i j) x (b i) := by
    conv_lhs => rw [← b.sum_repr' v]
    simp only [map_sum, map_smul, smul_eq_mul, fderiv_bilinearOfMatrix_basis b hM]
  simp_rw [hv]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hd, mul_zero]
  exact Finset.sum_const_zero

/- Full ambient Hessian in a constant orthonormal basis. -/

omit [CompleteSpace E] [DecidableEq ι] in
lemma contDiffAt_basisHessian (b : OrthonormalBasis ι ℝ E) {H : E → ℝ} {x : E}
    (hH : ContDiffAt ℝ ∞ H x) (i j : ι) : ContDiffAt ℝ ∞ (fun q => basisHessian b H q i j) x :=
  (((hH.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply
    contDiffAt_const).clm_apply contDiffAt_const

omit [CompleteSpace E] [DecidableEq ι] in
lemma basisHessian_isSymm (b : OrthonormalBasis ι ℝ E) {H : E → ℝ} {x : E}
    (hH : ContDiffAt ℝ ∞ H x) : (basisHessian b H x).IsSymm := by
  ext i j
  exact (hH.isSymmSndFDerivAt (by simp)).eq _ _

omit [CompleteSpace E] [DecidableEq ι] in
lemma fderiv_basisHessian (b : OrthonormalBasis ι ℝ E) {H : E → ℝ} {x : E}
    (hH : ContDiffAt ℝ ∞ H x) (i j : ι) (v : E) :
    fderiv ℝ (fun q => basisHessian b H q i j) x v =
      fderiv ℝ (fderiv ℝ (fderiv ℝ H)) x v (b i) (b j) := by
  have hh := fderiv_bilinear_field
    (((hH.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    (differentiableAt_const (b i)) (differentiableAt_const (b j)) v
  simpa only [fderiv_const_apply, zero_apply, map_zero, add_zero, basisHessian] using hh

omit [CompleteSpace E] [DecidableEq ι] in
lemma basisHessian_codazzi (b : OrthonormalBasis ι ℝ E) {H : E → ℝ} {x : E}
    (hH : ContDiffAt ℝ ∞ H x) (l j m : ι) :
    fderiv ℝ (fun q => basisHessian b H q l m) x (b j) =
      fderiv ℝ (fun q => basisHessian b H q l j) x (b m) := by
  rw [fderiv_basisHessian b hH, fderiv_basisHessian b hH]
  have hs := (hH.fderiv_right (m := ∞) (by simp)).isSymmSndFDerivAt
    (by simp)
  calc
    _ = fderiv ℝ (fderiv ℝ (fderiv ℝ H)) x (b l) (b j) (b m) :=
      congrArg (fun L : E →L[ℝ] ℝ => L (b m)) (hs.eq (b j) (b l))
    _ = fderiv ℝ (fderiv ℝ (fderiv ℝ H)) x (b l) (b m) (b j) :=
      third_derivative_swap_last hH _ _ _
    _ = _ := congrArg (fun L : E →L[ℝ] ℝ => L (b j)) (hs.eq (b l) (b m))

/- Global polynomial tensor whose tangential restriction is the angular cofactor. -/

lemma contDiffAt_supportNewtonTensor (b : OrthonormalBasis ι ℝ E) {H : E → ℝ} {x : E}
    (hH : ContDiffAt ℝ ∞ H x) : ContDiffAt ℝ ∞ (supportNewtonTensor b H) x := by
  apply contDiffAt_bilinearOfMatrix b
  intro i j
  have hM : ContDiffAt ℝ ∞ (fun q => fun l m => basisHessian b H q l m) x :=
    contDiffAt_pi.mpr fun l => contDiffAt_pi.mpr fun m => contDiffAt_basisHessian b hH l m
  exact (contDiff_newtonTensor_entry i j).contDiffAt.comp x hM

lemma supportNewtonTensor_isSymm (b : OrthonormalBasis ι ℝ E) {H : E → ℝ} {x : E}
    (hH : ContDiffAt ℝ ∞ H x) (u v : E) :
    supportNewtonTensor b H x u v = supportNewtonTensor b H x v u :=
  bilinearOfMatrix_symm b (newtonTensor_isSymm (basisHessian_isSymm b hH)) u v

lemma supportNewtonTensor_flat_divergence (b : OrthonormalBasis ι ℝ E) {H : E → ℝ} {x : E}
    (hH : ContDiffAt ℝ ∞ H x) (v : E) :
    (∑ i, fderiv ℝ (supportNewtonTensor b H) x (b i) (b i) v) = 0 := by
  apply bilinearOfMatrix_field_divergence b
    ((contDiffAt_supportNewtonTensor b hH).differentiableAt (by simp))
  intro j
  apply newtonTensor_divergence_of_codazzi (basisHessian b H) x b
  · intro l m
    exact (contDiffAt_basisHessian b hH l m).differentiableAt (by simp)
  · exact basisHessian_codazzi b hH

lemma supportNewtonTensor_radial (b : OrthonormalBasis ι ℝ E) {H : E → ℝ} {x : E}
    (hH : ContDiffAt ℝ ∞ H x)
    (hr : ∀ v, fderiv ℝ (fderiv ℝ H) x v x = 0) :
    ∃ c : ℝ, ∀ v, supportNewtonTensor b H x x v = c * inner ℝ x v := by
  have hv : basisHessian b H x *ᵥ (fun i => inner ℝ (b i) x) = 0 := by
    ext i
    change (∑ j, basisHessian b H x i j * inner ℝ (b j) x) = 0
    have hh := congrArg (fderiv ℝ (fderiv ℝ H) x (b i)) (b.sum_repr' x)
    simp only [map_sum, map_smul, smul_eq_mul] at hh
    simpa only [basisHessian, mul_comm, hr] using hh
  obtain ⟨c, hc⟩ := newtonTensor_radial hv
  exact ⟨c, fun v => bilinearOfMatrix_radial b
    (newtonTensor_isSymm (basisHessian_isSymm b hH)) hc v⟩

/- The genuinely differentiated angular divergence identity for a smooth
one-homogeneous support extension. Its only analytic input is the actual
radial Hessian identity; flat Piola and both normal cancellations are proved. -/
theorem supportNewtonTensor_round_divergence (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) {H : E → ℝ} (hH : ContDiffOn ℝ ∞ H U)
    (hr : ∀ q ∈ U, ∀ v, fderiv ℝ (fderiv ℝ H) q v q = 0)
    {e v : E} (heU : e ∈ U) (he : inner ℝ e e = 1) (hv : inner ℝ e v = 0) :
    (∑ i, roundTensorDerivative (supportNewtonTensor b H) e
      (tangentProjection e (b i)) (tangentProjection e (b i)) v) = 0 := by
  have hHe := hH.contDiffAt (hU.mem_nhds heU)
  apply projected_tensor_divergence b
    ((contDiffAt_supportNewtonTensor b hHe).differentiableAt (by simp)) he hv
    (supportNewtonTensor_isSymm b hHe)
  · filter_upwards [hU.mem_nhds heU] with q hq
    obtain ⟨c, hc⟩ := supportNewtonTensor_radial b
      (hH.contDiffAt (hU.mem_nhds hq)) (hr q hq)
    intro w
    rw [hc, hc]
    ring
  · exact supportNewtonTensor_flat_divergence b hHe

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SphereIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open scoped Pointwise
open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- The action of a genuine orthogonal coordinate change on the unit sphere. -/

variable [FiniteDimensional ℝ E]

section
variable [MeasurableSpace E] [BorelSpace E]

/- The round measure, defined by ordinary Euclidean polar coordinates, is
orthogonally invariant in every dimension, including the two-point sphere. -/
theorem sphereIsometry_measurePreserving (A : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereIsometry A) volume.toSphere volume.toSphere := by
  refine ⟨(sphereIsometry A).continuous.measurable, ?_⟩
  apply Measure.ext
  intro T hT
  rw [Measure.map_apply (sphereIsometry A).continuous.measurable hT,
    Measure.toSphere_apply' _ ((sphereIsometry A).continuous.measurable hT),
    Measure.toSphere_apply' _ hT]
  congr 1
  have hset : Ioo (0 : ℝ) 1 • (Subtype.val '' ((sphereIsometry A) ⁻¹' T)) =
      A ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' T)) := by
    ext y
    constructor
    · rintro ⟨r, hr, z, ⟨q,hq,rfl⟩, rfl⟩
      exact ⟨r, hr, A q, ⟨sphereIsometry A q, hq, rfl⟩, by simp⟩
    · rintro ⟨r, hr, z, ⟨q,hq,rfl⟩, hy⟩
      refine ⟨r, hr, A.symm q, ⟨(sphereIsometry A).symm q, ?_, rfl⟩, ?_⟩
      · simpa only [mem_preimage, Homeomorph.apply_symm_apply] using hq
      · apply A.injective
        simpa only [map_smul, A.apply_symm_apply] using hy
  rw [hset]
  change volume (A.toHomeomorph ⁻¹' _) = _
  rw [← A.toHomeomorph.measurableEmbedding.map_apply]
  change Measure.map A volume _ = _
  rw [A.measurePreserving.map_eq]

 theorem integral_sphere_isometry (A : E ≃ₗᵢ[ℝ] E)
    (f : sphere (0 : E) 1 → ℝ) :
    (∫ e, f (sphereIsometry A e) ∂volume.toSphere) = ∫ e, f e ∂volume.toSphere :=
  (sphereIsometry_measurePreserving A).integral_comp (sphereIsometry A).measurableEmbedding f

end

/- The infinitesimal generator of rotation in the oriented `u,v` plane. -/

theorem planeRotation_apply {u v : E} (hu : inner ℝ u u = 1)
    (hv : inner ℝ v v = 1) (huv : inner ℝ u v = 0) (t : ℝ) (x : E) :
    planeRotation hu hv huv t x = planeRotationMap u v t x := rfl

theorem planeRotation_zero (u v x : E) : planeRotationMap u v 0 x = x := by
  simp [planeRotationMap]

theorem planeRotation_hasDerivAt (u v x : E) (t : ℝ) :
    HasDerivAt (fun r => planeRotationMap u v r x)
      ((-Real.sin t) • planeProjection u v x + Real.cos t • rotationGenerator u v x) t := by
  have hh := ((hasDerivAt_const t x).add
    (((Real.hasDerivAt_cos t).sub_const 1).smul_const (planeProjection u v x))).add
      ((Real.hasDerivAt_sin t).smul_const (rotationGenerator u v x))
  convert hh using 1
  · funext r; rfl
  · simp

theorem planeRotation_mem_sphere {u v : E} (hu : inner ℝ u u = 1)
    (hv : inner ℝ v v = 1) (huv : inner ℝ u v = 0)
    (t : ℝ) (e : sphere (0 : E) 1) :
    planeRotationMap u v t e ∈ sphere (0 : E) 1 := by
  have h := (planeRotation hu hv huv t).norm_map (e : E)
  rw [planeRotation_apply] at h
  rw [mem_sphere, dist_zero_right, h]
  exact mem_sphere_zero_iff_norm.mp e.property

theorem planeRotation_sphere_continuous (u v : E) :
    Continuous (fun p : ℝ × sphere (0 : E) 1 => planeRotationMap u v p.1 p.2) := by
  simp only [planeRotationMap, add_apply, smul_apply, ContinuousLinearMap.id_apply]
  fun_prop

/- Differentiation under a finite measure on a compact parameter space.
The uniform bound is proved, rather than supplied as an analytic assumption. -/
theorem hasDerivAt_integral_compact {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [MeasurableSpace α] [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {F D : ℝ → α → ℝ}
    (hF : Continuous (fun p : ℝ × α => F p.1 p.2))
    (hD : Continuous (fun p : ℝ × α => D p.1 p.2))
    (hd : ∀ t a, HasDerivAt (fun r => F r a) (D t a) t) :
    HasDerivAt (fun t => ∫ a, F t a ∂μ) (∫ a, D 0 a ∂μ) 0 := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod (isCompact_univ (X := α))).exists_bound_of_continuousOn
    (f := fun p : ℝ × α => D p.1 p.2) hD.continuousOn
  have hFc (t : ℝ) : Continuous (F t) := hF.comp (continuous_const.prodMk continuous_id)
  have hDc (t : ℝ) : Continuous (D t) := hD.comp (continuous_const.prodMk continuous_id)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (μ := μ) (x₀ := (0 : ℝ))
    (s := Icc (-1 : ℝ) 1) (bound := fun _ => C)
    (Icc_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall (fun t => (hFc t).aestronglyMeasurable))
    ((hFc 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hDc 0).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e t ht => hC (t,e) ⟨ht, mem_univ e⟩))
    (integrable_const C) (Filter.Eventually.of_forall (fun e t _ => hd t e))).2

variable [MeasurableSpace E] [BorelSpace E]

/- Infinitesimal orthogonal invariance of the actual round measure. This is
proved by differentiating the genuine rotation, with a compact-sphere bound. -/
theorem integral_sphere_rotation_deriv {u v : E} (hu : inner ℝ u u = 1)
    (hv : inner ℝ v v = 1) (huv : inner ℝ u v = 0)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    (∫ e : sphere (0 : E) 1, fderiv ℝ f e (rotationGenerator u v e)
      ∂volume.toSphere) = 0 := by
  let F : ℝ → sphere (0 : E) 1 → ℝ := fun t e => f (planeRotationMap u v t e)
  let D : ℝ → sphere (0 : E) 1 → ℝ := fun t e =>
    fderiv ℝ f (planeRotationMap u v t e)
      ((-Real.sin t) • planeProjection u v e + Real.cos t • rotationGenerator u v e)
  have hR := planeRotation_mem_sphere hu hv huv
  have hRc := planeRotation_sphere_continuous u v
  have hFc : Continuous (fun p : ℝ × sphere (0 : E) 1 => F p.1 p.2) :=
    hf.continuousOn.comp_continuous hRc (fun p => hSU (hR p.1 p.2))
  have hDc : Continuous (fun p : ℝ × sphere (0 : E) 1 => D p.1 p.2) := by
    have hfd : Continuous (fun p : ℝ × sphere (0 : E) 1 =>
        fderiv ℝ f (planeRotationMap u v p.1 p.2)) := by
      apply continuous_iff_continuousAt.mpr
      intro p
      exact ((hf.contDiffAt (hU.mem_nhds (hSU (hR p.1 p.2)))).continuousAt_fderiv (by simp)).comp
        (f := fun q : ℝ × sphere (0 : E) 1 => planeRotationMap u v q.1 q.2)
        hRc.continuousAt
    apply hfd.clm_apply
    change Continuous (fun p : ℝ × sphere (0 : E) 1 =>
      (-Real.sin p.1) • planeProjection u v (p.2 : E) +
      Real.cos p.1 • rotationGenerator u v (p.2 : E))
    exact ((Real.continuous_sin.comp continuous_fst).neg.smul
      ((planeProjection u v).continuous.comp (continuous_subtype_val.comp continuous_snd))).add
      ((Real.continuous_cos.comp continuous_fst).smul
      ((rotationGenerator u v).continuous.comp (continuous_subtype_val.comp continuous_snd)))
  have hdiff (t : ℝ) (e : sphere (0 : E) 1) : HasDerivAt (fun r => F r e) (D t e) t :=
    ((hf.contDiffAt (hU.mem_nhds (hSU (hR t e)))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
      t (planeRotation_hasDerivAt u v e t)
  have hdint := hasDerivAt_integral_compact (μ := volume.toSphere) hFc hDc hdiff
  have hconst : (fun t => ∫ e, F t e ∂volume.toSphere) =
      (fun _ : ℝ => ∫ e : sphere (0 : E) 1, f e ∂volume.toSphere) := by
    funext t
    exact integral_sphere_isometry (planeRotation hu hv huv t) (fun e => f e)
  have hzero := hdint
  rw [hconst] at hzero
  have hz := hzero.unique (hasDerivAt_const (0 : ℝ) _)
  simpa only [D, planeRotation_zero, Real.sin_zero, neg_zero, zero_smul,
    Real.cos_zero, one_smul, zero_add] using hz

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SphereAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Ambient expression for the round divergence of the restriction to the unit sphere. -/

theorem rotationGenerator_apply (u v e : E) :
    rotationGenerator u v e = inner ℝ u e • v - inner ℝ v e • u := rfl

theorem sum_rotation_pair_first (b : OrthonormalBasis ι ℝ E) (e w : E) :
    (∑ i, ∑ j, inner ℝ (b i) (rotationGenerator (b i) (b j) e) * inner ℝ (b j) w) =
      (1 - (Fintype.card ι : ℝ)) * inner ℝ e w := by
  have hb (i j : ι) : inner ℝ (b i) (b j) = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp b.orthonormal i j
  simp only [rotationGenerator_apply, inner_sub_right, real_inner_smul_right, hb,
    sub_mul, Finset.sum_sub_distrib]
  have hew : (∑ i, inner ℝ (b i) e * inner ℝ (b i) w) = inner ℝ e w := by
    simpa only [real_inner_comm e] using b.sum_inner_mul_inner e w
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.sum_const, nsmul_eq_mul]
  rw [hew, Finset.card_univ]
  ring

omit [DecidableEq ι] in
theorem sum_rotation_pair_second (b : OrthonormalBasis ι ℝ E)
    (e : E) (he : inner ℝ e e = 1) (M : E →L[ℝ] E) :
    (∑ i, ∑ j, inner ℝ (b i) e * inner ℝ (b j) (M (rotationGenerator (b i) (b j) e))) =
      (∑ j, inner ℝ (b j) (M (b j))) - inner ℝ e (M e) := by
  simp only [rotationGenerator_apply, map_sub, map_smul, inner_sub_right,
    real_inner_smul_right, mul_sub, Finset.sum_sub_distrib]
  have hnorm : (∑ i, inner ℝ (b i) e * inner ℝ (b i) e) = 1 := by
    rw [← he]; simpa only [real_inner_comm e] using b.sum_inner_mul_inner e e
  have hdiag : (∑ i, ∑ j, inner ℝ (b i) e *
      (inner ℝ (b i) e * inner ℝ (b j) (M (b j)))) = ∑ j, inner ℝ (b j) (M (b j)) := by
    simp_rw [← mul_assoc, ← Finset.mul_sum]
    rw [← Finset.sum_mul, hnorm, one_mul]
  have hcross : (∑ i, ∑ j, inner ℝ (b i) e *
      (inner ℝ (b j) e * inner ℝ (b j) (M (b i)))) = inner ℝ e (M e) := by
    simp_rw [← Finset.mul_sum]
    have hinner (i : ι) : (∑ j, inner ℝ (b j) e * inner ℝ (b j) (M (b i))) =
        inner ℝ e (M (b i)) := by
      simpa only [real_inner_comm e] using b.sum_inner_mul_inner e (M (b i))
    simp_rw [hinner, ← real_inner_smul_right, ← map_smul]
    rw [← inner_sum, ← map_sum, b.sum_repr']
  rw [hdiag, hcross]

omit [FiniteDimensional ℝ E] [DecidableEq ι] in
theorem roundDivergence_trace (b : OrthonormalBasis ι ℝ E) (W : E → E) (e : E) :
    roundDivergence b W e =
      (∑ i, inner ℝ (b i) (fderiv ℝ W e (b i))) - inner ℝ e (fderiv ℝ W e e) := by
  simp only [roundDivergence, map_sub, map_smul, inner_sub_right,
    real_inner_smul_right, Finset.sum_sub_distrib]
  rw [b.sum_inner_mul_inner]

/- Contraction of the rotation derivatives is divergence minus the normal correction. -/
theorem sum_rotation_pair (b : OrthonormalBasis ι ℝ E) (e : E)
    (he : inner ℝ e e = 1) (w : E) (M : E →L[ℝ] E) :
    (∑ i, ∑ j, (inner ℝ (b i) (rotationGenerator (b i) (b j) e) * inner ℝ (b j) w +
      inner ℝ (b i) e * inner ℝ (b j) (M (rotationGenerator (b i) (b j) e)))) =
      (∑ j, inner ℝ (b j) (M (b j))) - inner ℝ e (M e) +
        (1 - (Fintype.card ι : ℝ)) * inner ℝ e w := by
  simp only [Finset.sum_add_distrib]
  rw [sum_rotation_pair_first, sum_rotation_pair_second b e he M]
  ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TensorFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι]

lemma tangentProjectionCLM_apply (e v : E) : tangentProjectionCLM e v = tangentProjection e v := rfl

omit [CompleteSpace E] in
lemma inner_tangentProjection_unit {e : E} (he : inner ℝ e e = 1) (v : E) :
    inner ℝ e (tangentProjection e v) = 0 := by
  simp only [tangentProjection, inner_sub_right, real_inner_smul_right, he, mul_one, sub_self]

omit [CompleteSpace E] in
lemma tangentProjection_self_unit {e : E} (he : inner ℝ e e = 1) :
    tangentProjection e e = 0 := by simp only [tangentProjection, he, one_smul, sub_self]

omit [CompleteSpace E] in
lemma contDiffAt_projected_field {G : E → E} {e : E} (hG : ContDiffAt ℝ ∞ G e) :
    ContDiffAt ℝ ∞ (fun q => tangentProjection q (G q)) e :=
  hG.sub ((contDiffAt_id.inner ℝ hG).smul contDiffAt_id)

omit [CompleteSpace E] in
lemma fderiv_projected_field {G : E → E} {e : E} (hG : DifferentiableAt ℝ G e) (u : E) :
    fderiv ℝ (fun q => tangentProjection q (G q)) e u =
      tangentProjection e (fderiv ℝ G e u) - inner ℝ u (G e) • e - inner ℝ e (G e) • u := by
  have hd := (hG.hasFDerivAt.sub (((hasFDerivAt_id e).inner ℝ hG.hasFDerivAt).smul
    (hasFDerivAt_id e))).fderiv
  simp only [Pi.sub_def, Pi.smul_def', id_eq] at hd
  change fderiv ℝ (fun q => G q - inner ℝ q (G q) • q) e u = _
  rw [hd]
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    tangentProjection, fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply, add_smul]
  abel

/- The flux of the angular tensor acting on the projected vector field.
Written in a fixed ambient basis, so no unspecified moving-frame derivatives appear. -/

omit [CompleteSpace E] in
lemma contDiffAt_tensorFlux (b : OrthonormalBasis ι ℝ E)
    {T : E → E →L[ℝ] E →L[ℝ] ℝ} {G : E → E} {e : E}
    (hT : ContDiffAt ℝ ∞ T e) (hG : ContDiffAt ℝ ∞ G e) :
    ContDiffAt ℝ ∞ (tensorFlux b T G) e := by
  apply ContDiffAt.sum
  intro i _
  exact ((hT.clm_apply (contDiffAt_projected_field contDiffAt_const)).clm_apply
    (contDiffAt_projected_field hG)).smul contDiffAt_const

lemma tensorFlux_tangent (b : OrthonormalBasis ι ℝ E)
    (T : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E) {e : E} (he : inner ℝ e e = 1) :
    inner ℝ e (tensorFlux b T G e) = 0 := by
  simp only [tensorFlux, inner_sum, real_inner_smul_right]
  have hb : (∑ i, inner ℝ e (b i) • tangentProjection e (b i)) = 0 := by
    have hh := congrArg (tangentProjectionCLM e) (b.sum_repr' e)
    simp only [map_sum, map_smul, tangentProjectionCLM_apply, tangentProjection_self_unit he] at hh
    simpa only [real_inner_comm e] using hh
  have hh := congrArg (fun v => T e v (tangentProjection e (G e))) hb
  simpa only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, map_zero, zero_apply,
    mul_comm] using hh

lemma fderiv_tensorFlux_scalar (b : OrthonormalBasis ι ℝ E)
    (T : E → E →L[ℝ] E →L[ℝ] ℝ) (g f : E → ℝ) (e : E) :
    fderiv ℝ f e (tensorFlux b T (gradient g) e) =
      T e (tangentProjection e (gradient f e)) (tangentProjection e (gradient g e)) := by
  simp only [tensorFlux, map_sum, map_smul, smul_eq_mul]
  have hh := congrArg (fun v => T e (tangentProjectionCLM e v)
    (tangentProjection e (gradient g e))) (b.sum_repr' (gradient f e))
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
    tangentProjectionCLM_apply] at hh
  simpa only [real_inner_comm (gradient f e), inner_gradient_left, mul_comm] using hh

omit [CompleteSpace E] in
lemma fderiv_basis_combination (b : OrthonormalBasis ι ℝ E) {F : ι → E → ℝ}
    {e : E} (hF : ∀ i, DifferentiableAt ℝ (F i) e) (v : E) :
    fderiv ℝ (fun q => ∑ i, F i q • b i) e v = ∑ i, fderiv ℝ (F i) e v • b i := by
  have hd : HasFDerivAt (fun q => ∑ i, F i q • b i)
      (∑ i, (fderiv ℝ (F i) e).smulRight (b i)) e := by
    apply HasFDerivAt.fun_sum
    intro i _
    exact (hF i).hasFDerivAt.smul_const (b i)
  rw [hd.fderiv]
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply]

variable [DecidableEq ι]

omit [CompleteSpace E] in
lemma roundDivergence_basis_combination (b : OrthonormalBasis ι ℝ E) {F : ι → E → ℝ}
    {e : E} (hF : ∀ i, DifferentiableAt ℝ (F i) e) :
    roundDivergence b (fun q => ∑ i, F i q • b i) e =
      ∑ i, fderiv ℝ (F i) e (tangentProjection e (b i)) := by
  simp only [roundDivergence, tangentProjection, fderiv_basis_combination b hF,
    inner_sum, real_inner_smul_right, orthonormal_iff_ite.mp b.orthonormal,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/- Intrinsic round Hessian contraction, formed from ambient derivatives and
orthogonal projection. It is independent of the extension off the sphere. -/

lemma roundDivergence_tensorFlux (b : OrthonormalBasis ι ℝ E)
    {T : E → E →L[ℝ] E →L[ℝ] ℝ} {G : E → E} {e : E}
    (hT : DifferentiableAt ℝ T e) (hG : DifferentiableAt ℝ G e)
    (he : inner ℝ e e = 1)
    (hr : ∀ v, inner ℝ e v = 0 → T e e v = 0 ∧ T e v e = 0)
    (hdiv : ∀ v, inner ℝ e v = 0 → (∑ i,
      roundTensorDerivative T e (tangentProjection e (b i)) (tangentProjection e (b i)) v) = 0) :
    roundDivergence b (tensorFlux b T G) e =
      ∑ i, T e (tangentProjection e (b i))
        (tangentProjection e (fderiv ℝ G e (tangentProjection e (b i))) -
          inner ℝ e (G e) • tangentProjection e (b i)) := by
  let p : ι → E := fun i => tangentProjection e (b i)
  let v : E := tangentProjection e (G e)
  have hp (i : ι) : inner ℝ e (p i) = 0 := inner_tangentProjection_unit he _
  have hv : inner ℝ e v = 0 := inner_tangentProjection_unit he _
  have hP : DifferentiableAt ℝ (fun q => tangentProjection q (G q)) e :=
    hG.sub ((differentiableAt_id.inner ℝ hG).smul differentiableAt_id)
  unfold tensorFlux
  rw [roundDivergence_basis_combination b (fun i =>
    (hT.clm_apply (hasFDerivAt_tangentProjection e (b i)).differentiableAt).clm_apply hP)]
  have hi (i : ι) :
      fderiv ℝ (fun q => T q (tangentProjection q (b i)) (tangentProjection q (G q))) e (p i) =
        roundTensorDerivative T e (p i) (p i) v - inner ℝ e (b i) * T e (p i) v +
          T e (p i) (tangentProjection e (fderiv ℝ G e (p i)) - inner ℝ e (G e) • p i) := by
    rw [fderiv_bilinear_field hT (hasFDerivAt_tangentProjection e (b i)).differentiableAt hP,
      (hasFDerivAt_tangentProjection e (b i)).fderiv, fderiv_projected_field hG,
      roundTensorDerivative_eq_of_radial hT _ _ _ (hp i) hv (hr _ (hp i)).2 (hr _ hv).1]
    simp only [neg_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, InnerProductSpace.toDual_apply_apply,
      map_neg, map_add, map_sub, map_smul, smul_eq_mul]
    dsimp only [p, v] at *
    simp only [(hr _ hv).1, (hr _ (hp i)).2, mul_zero, sub_zero, add_zero]
    ring
  change (∑ i, fderiv ℝ (fun q => T q (tangentProjection q (b i))
    (tangentProjection q (G q))) e (p i)) = _
  simp_rw [hi, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hdiv v hv]
  have hz : (∑ i, inner ℝ e (b i) * T e (p i) v) = 0 := by
    have hb := congrArg (tangentProjectionCLM e) (b.sum_repr' e)
    simp only [map_sum, map_smul, tangentProjectionCLM_apply, tangentProjection_self_unit he] at hb
    have hb' : (∑ i, inner ℝ e (b i) • p i) = 0 := by
      simpa only [real_inner_comm e] using hb
    have hh := congrArg (fun z => T e z v) hb'
    simpa only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, map_zero, zero_apply] using hh
  rw [hz, sub_self, zero_add]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SphereDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [MeasurableSpace E] [BorelSpace E] in
theorem fderiv_rotationPair {W : E → E} {e : E} (hW : DifferentiableAt ℝ W e)
    (u v z : E) :
    fderiv ℝ (fun q => inner ℝ u q * inner ℝ v (W q)) e z =
      inner ℝ u z * inner ℝ v (W e) + inner ℝ u e * inner ℝ v (fderiv ℝ W e z) := by
  have h1 := (InnerProductSpace.toDual ℝ E u).hasFDerivAt (x := e)
  have h2 := (InnerProductSpace.toDual ℝ E v).hasFDerivAt.comp e hW.hasFDerivAt
  have hd := (h1.mul h2).fderiv
  simp only [Pi.mul_def, Function.comp_def, InnerProductSpace.toDual_apply_apply] at hd
  rw [hd]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem rotationPair_smooth {U : Set E} {W : E → E} (hW : ContDiffOn ℝ ∞ W U)
    (u v : E) : ContDiffOn ℝ ∞ (fun q => inner ℝ u q * inner ℝ v (W q)) U :=
  (contDiffOn_const.inner ℝ contDiffOn_id).mul (contDiffOn_const.inner ℝ hW)

theorem sphere_directional_integrable {U : Set E} (hU : IsOpen U)
    (hSU : sphere (0 : E) 1 ⊆ U) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (M : E →L[ℝ] E) :
    Integrable (fun e : sphere (0 : E) 1 => fderiv ℝ f e (M e)) volume.toSphere := by
  have hd : ContinuousOn (fderiv ℝ f) U :=
    (hf.fderiv_of_isOpen hU (m := ∞) (by simp)).continuousOn
  have hc : Continuous (fun e : sphere (0 : E) 1 => fderiv ℝ f e) :=
    hd.comp_continuous continuous_subtype_val (fun e => hSU e.property)
  exact (hc.clm_apply (M.continuous.comp continuous_subtype_val)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integral_sphere_rotation_basis (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) (i j : ι) :
    (∫ e : sphere (0 : E) 1, fderiv ℝ f e (rotationGenerator (b i) (b j) e)
      ∂volume.toSphere) = 0 := by
  by_cases hij : i = j
  · subst j
    simp [rotationGenerator]
  · exact integral_sphere_rotation_deriv
      (by simp)
      (by simp)
      (b.inner_eq_zero hij) hU hSU hf

/- No angular boundary term: the round divergence of an actual smooth tangent
vector field integrates to zero, including the two-point and empty spheres. -/
theorem integral_roundDivergence (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {W : E → E} (hW : ContDiffOn ℝ ∞ W U)
    (ht : ∀ e ∈ sphere (0 : E) 1, inner ℝ e (W e) = 0) :
    (∫ e : sphere (0 : E) 1, roundDivergence b W e ∂volume.toSphere) = 0 := by
  let Q : ι → ι → E → ℝ := fun i j q => inner ℝ (b i) q * inner ℝ (b j) (W q)
  have hsmooth (i j : ι) : ContDiffOn ℝ ∞ (Q i j) U := rotationPair_smooth hW _ _
  have hpoint (e : sphere (0 : E) 1) :
      (∑ i, ∑ j, fderiv ℝ (Q i j) e (rotationGenerator (b i) (b j) e)) =
        roundDivergence b W e := by
    have hd : DifferentiableAt ℝ W (e : E) :=
      (hW.contDiffAt (hU.mem_nhds (hSU e.property))).differentiableAt (by simp)
    simp only [Q, fderiv_rotationPair hd]
    rw [sum_rotation_pair b (e : E)]
    · rw [ht e e.property, mul_zero, add_zero, roundDivergence_trace]
    · rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp e.property]
      norm_num
  have hi (i j : ι) : Integrable (fun e : sphere (0 : E) 1 =>
      fderiv ℝ (Q i j) e (rotationGenerator (b i) (b j) e)) volume.toSphere :=
    sphere_directional_integrable hU hSU (hsmooth i j) _
  calc
    (∫ e : sphere (0 : E) 1, roundDivergence b W e ∂volume.toSphere) =
        ∫ e : sphere (0 : E) 1, ∑ i, ∑ j,
          fderiv ℝ (Q i j) e (rotationGenerator (b i) (b j) e) ∂volume.toSphere := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun e => (hpoint e).symm)
    _ = ∑ i, ∑ j, ∫ e : sphere (0 : E) 1,
          fderiv ℝ (Q i j) e (rotationGenerator (b i) (b j) e) ∂volume.toSphere := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j _ => hi i j)
    _ = 0 := by
      simp only [integral_sphere_rotation_basis b hU hSU (hsmooth _ _), Finset.sum_const_zero]

/- Product rule for the actual round divergence, with no coordinate frame
extension assumed. The only cancellation is actual tangency on the sphere. -/
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DecidableEq ι] in
theorem roundDivergence_smul (b : OrthonormalBasis ι ℝ E)
    {f : E → ℝ} {W : E → E} {e : E}
    (hf : DifferentiableAt ℝ f e) (hW : DifferentiableAt ℝ W e)
    (ht : inner ℝ e (W e) = 0) :
    roundDivergence b (fun q => f q • W q) e =
      fderiv ℝ f e (W e) + f e * roundDivergence b W e := by
  have hd := (hf.hasFDerivAt.smul hW.hasFDerivAt).fderiv
  simp only [Pi.smul_def'] at hd
  rw [roundDivergence_trace, hd, roundDivergence_trace]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, inner_add_right, real_inner_smul_right,
    ht, mul_zero, add_zero, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hw : (∑ i, fderiv ℝ f e (b i) * inner ℝ (b i) (W e)) = fderiv ℝ f e (W e) := by
    conv_rhs => rw [← b.sum_repr' (W e)]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hw]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem sphere_fderiv_continuous {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    Continuous (fun e : sphere (0 : E) 1 => fderiv ℝ f e) :=
  (hf.fderiv_of_isOpen hU (m := ∞) (by simp)).continuousOn.comp_continuous
    continuous_subtype_val (fun e => hSU e.property)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DecidableEq ι] in
theorem sphere_roundDivergence_continuous (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {W : E → E} (hW : ContDiffOn ℝ ∞ W U) :
    Continuous (fun e : sphere (0 : E) 1 => roundDivergence b W e) := by
  have hd := sphere_fderiv_continuous hU hSU hW
  unfold roundDivergence
  apply continuous_finsetSum
  intro i _
  exact continuous_const.inner (hd.clm_apply
    (continuous_const.sub ((continuous_subtype_val.inner continuous_const).smul continuous_subtype_val)))

/- One genuine spherical integration by parts; all integrability follows from
smoothness near the compact sphere. -/
theorem integral_sphere_by_parts (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {f : E → ℝ} {W : E → E} (hf : ContDiffOn ℝ ∞ f U) (hW : ContDiffOn ℝ ∞ W U)
    (ht : ∀ e ∈ sphere (0 : E) 1, inner ℝ e (W e) = 0) :
    (∫ e : sphere (0 : E) 1, f e * roundDivergence b W e ∂volume.toSphere) =
      -(∫ e : sphere (0 : E) 1, fderiv ℝ f e (W e) ∂volume.toSphere) := by
  have hfc : Continuous (fun e : sphere (0 : E) 1 => f e) :=
    hf.continuousOn.comp_continuous continuous_subtype_val (fun e => hSU e.property)
  have hWc : Continuous (fun e : sphere (0 : E) 1 => W e) :=
    hW.continuousOn.comp_continuous continuous_subtype_val (fun e => hSU e.property)
  have hi1 : Integrable (fun e : sphere (0 : E) 1 => fderiv ℝ f e (W e)) volume.toSphere :=
    ((sphere_fderiv_continuous hU hSU hf).clm_apply hWc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun e : sphere (0 : E) 1 => f e * roundDivergence b W e) volume.toSphere :=
    (hfc.mul (sphere_roundDivergence_continuous b hU hSU hW)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hz := integral_roundDivergence b hU hSU (hf.smul hW) (fun e he => by
    simp only [Pi.smul_apply', real_inner_smul_right, ht e he, mul_zero])
  simp only [Pi.smul_def'] at hz
  have hh : (∫ e : sphere (0 : E) 1, roundDivergence b (fun q => f q • W q) e ∂volume.toSphere) =
      (∫ e : sphere (0 : E) 1, fderiv ℝ f e (W e) ∂volume.toSphere) +
      (∫ e : sphere (0 : E) 1, f e * roundDivergence b W e ∂volume.toSphere) := by
    rw [← integral_add hi1 hi2]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro e
    exact roundDivergence_smul b
      ((hf.contDiffAt (hU.mem_nhds (hSU e.property))).differentiableAt (by simp))
      ((hW.contDiffAt (hU.mem_nhds (hSU e.property))).differentiableAt (by simp)) (ht e e.property)
  linarith

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TensorIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Weighted spherical tensor integration by parts, for the literal round measure.
All smoothness and integrability statements are derived on a neighborhood of the
compact sphere. -/
theorem integral_roundHessianContraction (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {T : E → E →L[ℝ] E →L[ℝ] ℝ} (hT : ContDiffOn ℝ ∞ T U)
    (hr : ∀ e ∈ sphere (0 : E) 1, ∀ v, inner ℝ e v = 0 → T e e v = 0 ∧ T e v e = 0)
    (hdiv : ∀ e ∈ sphere (0 : E) 1, ∀ v, inner ℝ e v = 0 → (∑ i,
      roundTensorDerivative T e (tangentProjection e (b i)) (tangentProjection e (b i)) v) = 0)
    {f g : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    (∫ e : sphere (0 : E) 1, f e * roundHessianContraction b T g e ∂volume.toSphere) =
      -(∫ e : sphere (0 : E) 1, T e (tangentProjection e (gradient f e))
        (tangentProjection e (gradient g e)) ∂volume.toSphere) := by
  have hG : ContDiffOn ℝ ∞ (gradient g) U := by
    intro e he
    exact (contDiffAt_gradient (hg.contDiffAt (hU.mem_nhds he))).contDiffWithinAt
  have hW : ContDiffOn ℝ ∞ (tensorFlux b T (gradient g)) U := by
    intro e he
    exact (contDiffAt_tensorFlux b (hT.contDiffAt (hU.mem_nhds he))
      (hG.contDiffAt (hU.mem_nhds he))).contDiffWithinAt
  have he1 (e : sphere (0 : E) 1) : inner ℝ (e : E) e = 1 := by
    rw [real_inner_self_eq_norm_sq, (mem_sphere_zero_iff_norm.mp e.property)]
    norm_num
  have hpoint (e : sphere (0 : E) 1) :
      roundDivergence b (tensorFlux b T (gradient g)) e = roundHessianContraction b T g e :=
    roundDivergence_tensorFlux b
      ((hT.contDiffAt (hU.mem_nhds (hSU e.property))).differentiableAt (by simp))
      ((hG.contDiffAt (hU.mem_nhds (hSU e.property))).differentiableAt (by simp))
      (he1 e) (hr e e.property) (hdiv e e.property)
  calc
    _ = ∫ e : sphere (0 : E) 1, f e *
        roundDivergence b (tensorFlux b T (gradient g)) e ∂volume.toSphere := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun e => by
        dsimp only
        rw [hpoint e]
    _ = -(∫ e : sphere (0 : E) 1, fderiv ℝ f e
        (tensorFlux b T (gradient g) e) ∂volume.toSphere) :=
      integral_sphere_by_parts b hU hSU hf hW (fun e he =>
        tensorFlux_tangent b T (gradient g) (by
          rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp he]; norm_num))
    _ = _ := by simp_rw [fderiv_tensorFlux_scalar]

/- The exact twofold angular IBP needed by the tube Euler equation. -/
theorem integral_supportNewtonTensor_by_parts (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {H : E → ℝ} (hH : ContDiffOn ℝ ∞ H U)
    (hr : ∀ q ∈ U, ∀ v, fderiv ℝ (fderiv ℝ H) q v q = 0)
    {f g : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    (∫ e : sphere (0 : E) 1, f e *
      roundHessianContraction b (supportNewtonTensor b H) g e ∂volume.toSphere) =
      -(∫ e : sphere (0 : E) 1, supportNewtonTensor b H e
        (tangentProjection e (gradient f e)) (tangentProjection e (gradient g e)) ∂volume.toSphere) := by
  apply integral_roundHessianContraction b hU hSU
  · intro e he
    exact (contDiffAt_supportNewtonTensor b (hH.contDiffAt (hU.mem_nhds he))).contDiffWithinAt
  · intro e he v hv
    obtain ⟨c, hc⟩ := supportNewtonTensor_radial b
      (hH.contDiffAt (hU.mem_nhds (hSU he))) (hr e (hSU he))
    constructor
    · rw [hc, hv, mul_zero]
    · rw [supportNewtonTensor_isSymm b (hH.contDiffAt (hU.mem_nhds (hSU he))), hc, hv, mul_zero]
  · intro e he v hv
    apply supportNewtonTensor_round_divergence b hU hH hr (hSU he) _ hv
    rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp he]
    norm_num
  · exact hf
  · exact hg

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualTubeMetricPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [MeasurableSpace E] [BorelSpace E] in
lemma gradient_exp_linear_combination {P F : E → ℝ} {e : E}
    (hP : DifferentiableAt ℝ P e) (hF : DifferentiableAt ℝ F e) (a c : ℝ) :
    gradient (fun y => Real.exp (a*P y+c*F y)) e =
      Real.exp (a*P e+c*F e) • (a • gradient P e+c • gradient F e) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have hh : HasFDerivAt (fun y => Real.exp (a*P y+c*F y))
      (Real.exp (a*P e+c*F e) • (a • fderiv ℝ P e+c • fderiv ℝ F e)) e :=
    ((hP.hasFDerivAt.const_mul a).add (hF.hasFDerivAt.const_mul c)).exp
  rw [hh.fderiv]
  simp [inner_add_left,real_inner_smul_left,inner_gradient_left,mul_left_comm]

theorem integral_supportNewtonTensor_exp_weight (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {H P F : E → ℝ} (hH : ContDiffOn ℝ ∞ H U)
    (hr : ∀ q ∈ U, ∀ v, fderiv ℝ (fderiv ℝ H) q v q = 0)
    (hP : ContDiffOn ℝ ∞ P U) (hF : ContDiffOn ℝ ∞ F U) (a c : ℝ) :
    (∫ e : sphere (0 : E) 1, Real.exp (a*P e+c*F e) *
      roundHessianContraction b (supportNewtonTensor b H) F e ∂volume.toSphere) =
      -(∫ e : sphere (0 : E) 1, Real.exp (a*P e+c*F e) *
        (a * supportNewtonTensor b H e (tangentProjection e (gradient P e))
            (tangentProjection e (gradient F e)) +
         c * supportNewtonTensor b H e (tangentProjection e (gradient F e))
            (tangentProjection e (gradient F e))) ∂volume.toSphere) := by
  rw [integral_supportNewtonTensor_by_parts b hU hSU hH hr
    (((contDiffOn_const.mul hP).add (contDiffOn_const.mul hF)).exp) hF]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro e
  dsimp only
  rw [gradient_exp_linear_combination
    ((hP.contDiffAt (hU.mem_nhds (hSU e.property))).differentiableAt (by simp))
    ((hF.contDiffAt (hU.mem_nhds (hSU e.property))).differentiableAt (by simp))]
  change supportNewtonTensor b H e
    (tangentProjectionCLM (e : E) (Real.exp (a*P e+c*F e) • (a • gradient P e+c • gradient F e))) _ = _
  simp only [map_smul,map_add,smul_apply,add_apply,smul_eq_mul,tangentProjectionCLM_apply]

omit [MeasurableSpace E] [BorelSpace E] in
lemma sphere_tangent_gradient_continuous {U : Set E} (hU : IsOpen U)
    (hSU : sphere (0:E) 1 ⊆ U) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) :
    Continuous (fun e : sphere (0:E) 1 => tangentProjection (e : E) (gradient F (e : E))) := by
  have hgc : Continuous (fun e : sphere (0:E) 1 => gradient F (e : E)) := by
    refine ContinuousOn.comp_continuous (g := gradient F) ?_ continuous_subtype_val (fun e => hSU e.property)
    intro e he
    exact (contDiffAt_gradient (hF.contDiffAt (hU.mem_nhds he))).continuousAt.continuousWithinAt
  exact hgc.sub ((continuous_subtype_val.inner hgc).smul continuous_subtype_val)

omit [MeasurableSpace E] [BorelSpace E] in
lemma sphere_supportNewtonTensor_continuous (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0:E) 1 ⊆ U)
    {H : E → ℝ} (hH : ContDiffOn ℝ ∞ H U) :
    Continuous (fun e : sphere (0:E) 1 => supportNewtonTensor b H e) := by
  refine ContinuousOn.comp_continuous (g := supportNewtonTensor b H) ?_ continuous_subtype_val (fun e => hSU e.property)
  intro e he
  exact (contDiffAt_supportNewtonTensor b (hH.contDiffAt (hU.mem_nhds he))).continuousAt.continuousWithinAt

/- The angular drift coefficient after integration is exactly `1-c`.
At `c=(n+2)/2` this is `-n/2`, as in tubes.tex. -/
theorem integral_supportNewtonTensor_weighted_drift (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {H P F : E → ℝ} (hH : ContDiffOn ℝ ∞ H U)
    (hr : ∀ q ∈ U, ∀ v, fderiv ℝ (fderiv ℝ H) q v q = 0)
    (hP : ContDiffOn ℝ ∞ P U) (hF : ContDiffOn ℝ ∞ F U) (a c : ℝ) :
    (∫ e : sphere (0 : E) 1, Real.exp (a*P e+c*F e) *
      roundHessianContraction b (supportNewtonTensor b H) F e ∂volume.toSphere) +
    a*(∫ e : sphere (0 : E) 1, Real.exp (a*P e+c*F e) *
      supportNewtonTensor b H e (tangentProjection e (gradient P e))
        (tangentProjection e (gradient F e)) ∂volume.toSphere) +
    (∫ e : sphere (0 : E) 1, Real.exp (a*P e+c*F e) *
      supportNewtonTensor b H e (tangentProjection e (gradient F e))
        (tangentProjection e (gradient F e)) ∂volume.toSphere) =
    (1-c)*(∫ e : sphere (0 : E) 1, Real.exp (a*P e+c*F e) *
      supportNewtonTensor b H e (tangentProjection e (gradient F e))
        (tangentProjection e (gradient F e)) ∂volume.toSphere) := by
  have hpc := hP.continuousOn.comp_continuous continuous_subtype_val (fun e => hSU e.property)
  have hfc := hF.continuousOn.comp_continuous continuous_subtype_val (fun e => hSU e.property)
  have hwc : Continuous (fun e : sphere (0:E) 1 => Real.exp (a*P e+c*F e)) :=
    Real.continuous_exp.comp ((continuous_const.mul hpc).add (continuous_const.mul hfc))
  have htc := sphere_supportNewtonTensor_continuous b hU hSU hH
  have hdpc := sphere_tangent_gradient_continuous hU hSU hP
  have hdfc := sphere_tangent_gradient_continuous hU hSU hF
  have hi1 := (hwc.mul ((htc.clm_apply hdpc).clm_apply hdfc)).integrable_of_hasCompactSupport (μ := volume.toSphere)
    (HasCompactSupport.of_compactSpace _)
  have hi2 := (hwc.mul ((htc.clm_apply hdfc).clm_apply hdfc)).integrable_of_hasCompactSupport (μ := volume.toSphere)
    (HasCompactSupport.of_compactSpace _)
  simp only [Pi.mul_def] at hi1 hi2
  rw [integral_supportNewtonTensor_exp_weight b hU hSU hH hr hP hF a c]
  have hsplit : (∫ e : sphere (0:E) 1, Real.exp (a*P e+c*F e) *
      (a * supportNewtonTensor b H e (tangentProjection e (gradient P e)) (tangentProjection e (gradient F e)) +
       c * supportNewtonTensor b H e (tangentProjection e (gradient F e)) (tangentProjection e (gradient F e))) ∂volume.toSphere) =
      a*(∫ e : sphere (0:E) 1, Real.exp (a*P e+c*F e) * supportNewtonTensor b H e
        (tangentProjection e (gradient P e)) (tangentProjection e (gradient F e)) ∂volume.toSphere) +
      c*(∫ e : sphere (0:E) 1, Real.exp (a*P e+c*F e) * supportNewtonTensor b H e
        (tangentProjection e (gradient F e)) (tangentProjection e (gradient F e)) ∂volume.toSphere) := by
    rw [← integral_const_mul,← integral_const_mul,← integral_add (hi1.const_mul a) (hi2.const_mul c)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun _ => by ring
  rw [hsplit]
  ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualWeightedAngular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem affineEpigraph_angular_f_weighted_drift {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun q => Real.log (H q)
    let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
    let N := supportNewtonTensor bE (fun e => H (s,e))
    let dP := fun e => tangentProjection e (gradient (fun y => P (s,y)) e)
    let dF := fun e => tangentProjection e (gradient (fun y => F (s,y)) e)
    let W := fun e => Real.exp (2*P (s,e)+(((n : ℝ)+2)/2)*F (s,e))
    (∫ e : sphere (0:E) 1, W e*roundHessianContraction bE N (fun y => F (s,y)) e ∂volume.toSphere) +
    2*(∫ e : sphere (0:E) 1, W e*N e (dP e) (dF e) ∂volume.toSphere) +
    (∫ e : sphere (0:E) 1, W e*N e (dF e) (dF e) ∂volume.toSphere) =
    (-(n : ℝ)/2)*(∫ e : sphere (0:E) 1, W e*N e (dF e) (dF e) ∂volume.toSphere) := by
  dsimp only
  have hsmooth := affineEpigraph_tube_angular_smooth hΩ hcv hu hp a L hD hK hzero hs bS bE
    (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
  have hU : IsOpen {e : E | e ≠ 0} := isClosed_singleton.isOpen_compl
  have hSU : sphere (0:E) 1 ⊆ {e : E | e ≠ 0} := by
    intro e he
    have hen : ‖e‖ = 1 := mem_sphere_zero_iff_norm.1 he
    intro hz
    simp [hz] at hen
  have hh := integral_supportNewtonTensor_weighted_drift bE hU hSU
    hsmooth.1 hsmooth.2.2.2 hsmooth.2.1 hsmooth.2.2.1 2 (((n : ℝ)+2)/2)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualWeightedAngularFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- The actual angular weighted drift integrates to exactly `-n/2` times
its nonnegative angular energy. No angular PDE or integration formula is assumed. -/
theorem affineEpigraph_angular_literal_drift_oai {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun q => Real.log (H q)
    let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
    let N := supportNewtonTensor bE (fun e => H (s,e))
    let dP := fun e => tangentProjection e (gradient (fun y => P (s,y)) e)
    let dF := fun e => tangentProjection e (gradient (fun y => F (s,y)) e)
    let W := fun e => tubeMeasureDensity n H bS bE (s,e)*H (s,e)/tubeAngularDensity H (s,e) bE
    (∫ e : sphere (0:E) 1, W e*roundHessianContraction bE N (fun y => F (s,y)) e ∂volume.toSphere) +
    2*(∫ e : sphere (0:E) 1, W e*N e (dP e) (dF e) ∂volume.toSphere) +
    (∫ e : sphere (0:E) 1, W e*N e (dF e) (dF e) ∂volume.toSphere) =
    (-(n : ℝ)/2)*(∫ e : sphere (0:E) 1, W e*N e (dF e) (dF e) ∂volume.toSphere) := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  have hw (e : sphere (0:E) 1) :
      Real.exp (2*Real.log (H (s,e))+(((n : ℝ)+2)/2)*invariantTubeF H bS bE
        (1/((Fintype.card ι : ℝ)+Fintype.card κ+2)) (s,e)) =
      tubeMeasureDensity n H bS bE (s,e)*H (s,e)/tubeAngularDensity H (s,e) bE := by
    have he : ‖(e:E)‖ = 1 := mem_sphere_zero_iff_norm.1 e.property
    have hen : (e:E) ≠ 0 := by intro hz; simp [hz] at he
    have hpos := affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hs hen bS bE
    exact (tubeMeasureDensity_angular bS bE (tube_dimension_eq bS bE L) he
      hpos.2.2 hpos.1.det_pos hpos.2.1).symm
  have hh := affineEpigraph_angular_f_weighted_drift hΩ hcv hu hp a L hD hK hzero hs bS bE
  dsimp only at hh
  dsimp only [H] at hw
  simpa only [hw] using hh

end AffineBernstein
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.AffineBernstein.affineEpigraph_angular_literal_drift_oai.{u_1, u_2, u_3, u_4} := @OAI.AffineBernstein.affineEpigraph_angular_literal_drift_oai.{u_1, u_2, u_3, u_4}
