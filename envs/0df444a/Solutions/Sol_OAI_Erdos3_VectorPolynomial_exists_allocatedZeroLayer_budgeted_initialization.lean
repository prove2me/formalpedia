-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_budgeted_initialization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T01:55:52.28005+00:00
-- url     : https://prove2.me/submissions/547eda73-83f1-40c4-96c1-37e7ca5f5a35

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1342
import Definitions.Def_OAIErdos3B1348

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformSelectedCoefficientProductLaw
namespace OAI

section

namespace Erdos3

open scoped ENNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem baseArrayJoin_injective {K I X : Type*} (tail : K × I → X) :
    Function.Injective (baseArrayJoin tail) := by
  intro b c he
  funext i
  exact congrFun he (none,i)

theorem independentProductPMF_base_split {K I X : Type*} [Fintype K] [Fintype I]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : Option K × I → PMF X) :
    independentProductPMF p =
      (independentProductPMF (fun k : K × I => p (some k.1,k.2))).bind
        (fun tail => (independentProductPMF (fun i => p (none,i))).map (baseArrayJoin tail)) := by
  ext z
  let tail := fun k : K × I => z (some k.1,k.2)
  let base := fun i : I => z (none,i)
  have hz : baseArrayJoin tail base = z := baseArrayJoin_eta z
  rw [← hz, PMF.bind_apply, tsum_eq_single tail]
  · rw [pmf_map_injective_at _ _ (baseArrayJoin_injective tail)]
    simp only [independentProductPMF_apply, Fintype.prod_prod_type, Fintype.prod_option, baseArrayJoin]
    exact mul_comm _ _
  · intro other hother
    have hr : baseArrayJoin tail base ∉ Set.range (baseArrayJoin other) := by
      rintro ⟨b, he⟩
      apply hother
      funext k
      exact congrFun he (some k.1,k.2)
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

theorem independentProductPMF_base_cap {K I X Y : Type*} [Fintype K] [Fintype I]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : Option K × I → PMF X) (f : (Option K × I → X) → Y)
    (hf : ∀ tail, Function.Injective (fun base => f (baseArrayJoin tail base)))
    (C : I → ℝ) (hC : ∀ i, 0 ≤ C i) (hp : ∀ i x, (p (none,i) x).toReal ≤ C i) (y : Y) :
    ((independentProductPMF p).map f y).toReal ≤ ∏ i, C i := by
  rw [independentProductPMF_base_split, PMF.map_bind]
  simp_rw [PMF.map_comp]
  apply pmf_bind_injective_toReal_cap _ _ _ hf (Finset.prod_nonneg (fun i _ => hC i))
  intro base
  rw [independentProductPMF_toReal]
  exact Finset.prod_le_prod (fun i _ => ENNReal.toReal_nonneg) (fun i _ => hp i (base i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem shiftedSmoothProductPMF_base_cap {K I Y : Type*} [Fintype K] [Fintype I]
    (a S : Option K × I → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (f : (Option K × I → ℤ) → Y)
    (hf : ∀ tail, Function.Injective (fun base => f (baseArrayJoin tail base)))
    (hbase : ∀ i, 8*(probabilityProfileLipschitz : ℝ) ≤ S (none,i)) (y : Y) :
    ((shiftedSmoothProductPMF a S hS hZ).map f y).toReal ≤ ∏ i, 2 / S (none,i) := by
  rw [shiftedSmoothProductPMF_eq_independent]
  apply independentProductPMF_base_cap _ f hf (fun i => 2 / S (none,i))
    (fun i => div_nonneg (by norm_num) (hS (none,i)).le)
  intro i k
  exact shiftedSmoothCoefficientPMF_le (a (none,i)) (hbase i) k

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSymbolicShearWeightedDegree
namespace OAI

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ τ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem parameterSubstitution_slot_homogeneous
    (f : σ → MvPolynomial τ ℝ) (i : Fin d) (v : σ ⊕ Fin i.val) :
    (parameterSubstitution f i v).IsWeightedHomogeneous
      (patchSlotWeight w i) (patchSlotWeight w i v) := by
  cases v with
  | inl a =>
    apply aeval_isWeightedHomogeneous (fun _ : τ => 0) (patchSlotWeight w i)
    · intro b
      exact isWeightedHomogeneous_X ℝ _ (Sum.inl b)
    · intro α _
      simp [Finsupp.weight_apply, Finsupp.sum, patchSlotWeight]
  | inr j => exact isWeightedHomogeneous_X ℝ _ (Sum.inr j)

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

end Erdos3.PolynomialSlots

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ}

namespace PolynomialSlots

variable {w : Fin d → ℕ}

end PolynomialSlots

namespace PolynomialPatch

variable {s : ℕ}

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ τ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem reparam_topPart_center (A : PolynomialSlots σ d w)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (i : Fin d) :
    (A.reparam f hf).topPart.center i =
      aeval (parameterSubstitution f i) (A.topPart.center i) := by
  exact (aeval_weightedHomogeneousComponent (patchSlotWeight w i)
    (patchSlotWeight w i) (parameterSubstitution f i)
    (parameterSubstitution_slot_homogeneous f i) (w i) (A.center i)).symm

theorem reparam_topPart_specializeCenter (A : PolynomialSlots σ d w)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (i : Fin d) :
    (A.reparam f hf).topPart.specializeCenter 0 i =
      A.topPart.specializeCenter 0 i := by
  unfold specializeCenter
  rw [A.reparam_topPart_center f hf, MvPolynomial.comp_aeval_apply]
  let q : σ → MvPolynomial (Fin i.val) ℝ := fun a =>
    aeval (Sum.elim (fun _ : τ => 0) X) (parameterSubstitution f i (Sum.inl a))
  have hinput :
      (fun a => aeval (Sum.elim (fun j : τ => C ((0 : τ → ℝ) j)) X)
        (parameterSubstitution f i a)) = Sum.elim q X := by
    funext a
    cases a <;> simp [q, parameterSubstitution]
  rw [hinput]
  exact A.topPart_aeval_independent i q (fun a => C ((0 : σ → ℝ) a)) X

theorem reparam_topResidualEquiv (A : PolynomialSlots σ d w)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) :
    (A.reparam f hf).topResidualEquiv = A.topResidualEquiv := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  change (A.reparam f hf).topResidualEquiv (X i) = A.topResidualEquiv (X i)
  rw [topResidualEquiv_X, topResidualEquiv_X,
    A.reparam_topPart_specializeCenter f hf]

theorem reparam_specialized_residualHom (A : PolynomialSlots σ d w)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (t : τ → ℝ) :
    (patchParameterSpecialization t).comp (A.reparam f hf).residualHom =
      (patchParameterSpecialization (fun a => aeval t (f a))).comp A.residualHom := by
  apply MvPolynomial.algHom_ext
  intro i
  apply MvPolynomial.funext
  intro x
  simp only [AlgHom.comp_apply, ← MvPolynomial.aeval_eq_eval]
  rw [patchParameterSpecialization_eval, patchParameterSpecialization_eval,
    residualHom_X, residualHom_X, residualCoordinate_eval, residualCoordinate_eval,
    reparam_slots]

theorem reparam_loweringAt (A : PolynomialSlots σ d w)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (t : τ → ℝ) :
    (A.reparam f hf).loweringAt t = A.loweringAt (fun a => aeval t (f a)) := by
  have hc := (A.reparam f hf).loweringAt_comp_top t
  rw [A.reparam_topResidualEquiv f hf, A.reparam_specialized_residualHom f hf,
    ← A.loweringAt_comp_top] at hc
  apply Subtype.ext
  apply AlgEquiv.coe_toAlgHom_injective
  apply AlgHom.ext
  intro P
  have h := congrArg (fun F : MvPolynomial (Fin d) ℝ →ₐ[ℝ] MvPolynomial (Fin d) ℝ =>
    F (A.topResidualEquiv.symm P)) hc
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using h

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

end Erdos3.PolynomialSlots

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R] [Algebra ℚ R]
variable {w₀ w₁ : σ → ℕ} {v₀ : τ → ℕ}

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} {d : ℕ} (w : Fin d → ℕ)
variable [Fintype (PolynomialShearIndex w)]
variable (c : PolynomialShearIndex w → MvPolynomial σ ℝ)

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
variable {σ : Type*} {d : ℕ} (p : σ → ℕ) (w : Fin d → ℕ)
variable [Fintype (PolynomialShearIndex w)]
variable (c : PolynomialShearIndex w → MvPolynomial σ ℝ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

namespace ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q : ℕ}

end ResidueBoxSlice

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q r : ℕ}

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {X : Type*} {N : X → ℕ} {q : ℕ}

end ResidueBoxSlice

theorem relativePatchBoxScore_pullback {X : Type*} [Fintype X] [DecidableEq X]
    {s d q : ℕ} {N : X → ℕ} (S : ResidueBoxSlice N q)
    (f : (X → ℤ) → ℝ) (a : ℝ) (A : PolynomialPatch X s d) :
    relativePatchBoxScore S.length (S.integerPullback f) a A =
      relativePatchSliceScore S f a A := by
  classical
  symm
  unfold relativePatchSliceScore relativePatchBoxScore
  apply Finset.expect_bij (fun t _ i => ((t i).val : ℤ))
  · intro t _
    exact (mem_integerBox S.length _).mpr (fun i =>
      ⟨Int.natCast_nonneg _, by exact_mod_cast (t i).isLt⟩)
  · intro t _
    simp only [ResidueBoxSlice.integerPullback, ResidueBoxSlice.integerAffine_finPoint,
      Int.cast_natCast]
  · intro t _ u _ h
    funext i
    apply Fin.ext
    exact_mod_cast congrFun h i
  · intro x hx
    have hx' := (mem_integerBox S.length x).mp hx
    refine ⟨fun i => ⟨(x i).toNat, by have := hx' i; omega⟩, by simp only [Finset.mem_univ], ?_⟩
    funext i
    exact Int.toNat_of_nonneg (hx' i).1

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeFullSliceLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical
namespace ResidueBoxSlice
variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q s d : ℕ}

omit [Fintype X] [DecidableEq X] in
theorem fullSliceReinsertPatch_point_value (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch X s d) (hq : 0 < q) (u : ∀ i, Fin (S.length i)) :
    (S.fullSliceReinsertPatch Q).value (fun i => ((S.point u i).val : ℝ)) =
      Q.value (fun i => ((u i).val : ℝ)) := by
  rw [fullSliceReinsertPatch, PolynomialPatch.reparam_value]
  congr 1
  funext i
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [fullSliceInverseParameters, map_smul, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    point, Nat.cast_add, Nat.cast_mul, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]
  field_simp
  ring

theorem fullSliceLaw_score (S : ResidueBoxSlice N q) (hlen : ∀ i, 0 < S.length i)
    (hq : 0 < q) (Q : PolynomialPatch X s d) (f : (X → ℤ) → ℝ) (target : ℝ) :
    (S.fullSliceLaw hlen).mean (fun x => (f x.val-target) *
      (S.fullSliceReinsertPatch Q).value (fun i => (x.val i : ℝ))) =
      relativePatchSliceScore S f target Q := by
  rw [fullSliceLaw_mean]
  unfold relativePatchSliceScore
  congr 1
  · ext u
    simp
  · funext u
    change (f _-target) * (S.fullSliceReinsertPatch Q).value (fun i => ((S.point u i).val : ℝ)) = _
    rw [fullSliceReinsertPatch_point_value S Q hq]
    rfl
end ResidueBoxSlice

theorem RelativePatchSliceConclusion.exists_full_law
    {X : Type*} [Fintype X] [DecidableEq X] {s rankBound : ℕ} {N : X → ℕ}
    {f : (X → ℤ) → ℝ} {target cost : ℝ} (hN : ∀ i, 0 < N i)
    (h : RelativePatchSliceConclusion s N f target rankBound cost) :
    ∃ (d : ℕ) (Q : PolynomialPatch X s d) (law : FiniteProbabilityWeights (integerBox N)),
      d ≤ rankBound ∧ relativePatchComplexity Q ≤ cost ∧ (Q.kernel.lip : ℝ) ≤ Real.exp cost ∧
      Real.exp (-cost) ≤ law.mean (fun x => (f x.val-target) * Q.value (fun i => (x.val i : ℝ))) ∧
      ∃ q, 0 < q ∧ ∃ (S : ResidueBoxSlice N q) (hlen : ∀ i, 0 < S.length i),
        (∀ i, Real.exp (-cost) * (N i : ℝ) ≤ (S.length i : ℝ)) ∧ law = S.fullSliceLaw hlen := by
  obtain ⟨q,hq,S,d,Q,hlength,hd,hcost,hscore⟩ := h
  have hlen : ∀ i, 0 < S.length i := by
    intro i
    exact_mod_cast (mul_pos (Real.exp_pos (-cost)) (Nat.cast_pos.mpr (hN i))).trans_le (hlength i)
  have hlog : Real.log (1+(Q.kernel.lip : ℝ)) ≤ cost := by
    have := Nat.cast_nonneg (α := ℝ) d
    dsimp only [relativePatchComplexity] at hcost
    linarith
  have hlip : (Q.kernel.lip : ℝ) ≤ Real.exp cost := by
    have he := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (by positivity : 0 < 1+(Q.kernel.lip : ℝ))] at he
    linarith
  refine ⟨d,S.fullSliceReinsertPatch Q,S.fullSliceLaw hlen,hd,hcost,hlip,?_,q,hq,S,hlen,hlength,rfl⟩
  rwa [S.fullSliceLaw_score hlen hq Q f target]
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalBaseInjection
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem residueLatticeArray_baseArrayJoin {K I : Type*}
    (residue : Option K × I → ℤ) (modulus : I → ℕ) (tail : K × I → ℤ) (base : I → ℤ) :
    residueLatticeArray residue modulus (baseArrayJoin tail base) =
      baseArrayJoin (fun k => residue (some k.1,k.2) + (modulus k.2 : ℤ)*tail k)
        (fun i => residue (none,i) + (modulus i : ℤ)*base i) := by
  funext z
  rcases z with ⟨k,i⟩
  cases k <;> rfl

theorem physicalAffineSite_residue_base_injective {K I : Type*} [Fintype K]
    (root : K → ℤ) (residue : Option K × I → ℤ)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i) (tail : K × I → ℤ) :
    Function.Injective (fun base =>
      physicalAffineSite root (residueLatticeArray residue modulus (baseArrayJoin tail base))) := by
  intro b c he
  funext i
  have h := congrFun he i
  simp only [residueLatticeArray_baseArrayJoin, physicalAffineSite_baseArrayJoin_apply] at h
  have hb : residue (none,i) + (modulus i : ℤ)*b i =
      residue (none,i) + (modulus i : ℤ)*c i := by exact_mod_cast add_right_cancel h
  exact mul_left_cancel₀ (by exact_mod_cast (hmodulus i).ne' : (modulus i : ℤ) ≠ 0)
    (add_left_cancel hb)

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResiduePhysicalCap
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem residueSmoothPMF_physical_cap {K I : Type*} [Fintype K] [Fintype I]
    (root : K → ℤ) (residue : Option K × I → ℤ)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus) (residueProfileWidth modulus W))
    (hbase : ∀ i, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W (none,i))
    (y : I → ℝ) :
    ((residueSmoothPMF residue modulus hmodulus W hW hZ).map (physicalAffineSite root) y).toReal ≤
      ∏ i, 2*(modulus i : ℝ)/W (none,i) := by
  rw [residueSmoothPMF, PMF.map_comp, residueSmoothIndexPMF]
  have h := shiftedSmoothProductPMF_base_cap (residueProfileCenter residue modulus)
    (residueProfileWidth modulus W) (residueProfileWidth_pos modulus W hmodulus hW) hZ
    (physicalAffineSite root ∘ residueLatticeArray residue modulus)
    (physicalAffineSite_residue_base_injective root residue modulus hmodulus) hbase y
  simpa only [residueProfileWidth, div_div_eq_mul_div] using h

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedPhysicalReferenceCap
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

variable {K I : Type*} [Fintype K] [Fintype I]
variable (root : K → ℤ) (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
variable (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
variable (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
variable (hc : ∀ r : T, 0 < shiftedSmoothProductMass
  (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus) (residueProfileWidth modulus W))
variable (hbase : ∀ i, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W (none,i))

include hmodulus hT hc hbase in
theorem selectedResidueSmoothPMF_physical_cap (y : I → ℝ) :
    ((selectedResidueSmoothPMF modulus T W hW hZ).map (physicalAffineSite root) y).toReal ≤
      ∏ i, 2*(modulus i : ℝ)/W (none,i) := by
  obtain ⟨_, h⟩ := selectedResidueSmoothPMF_bound_of_cells (ε := ∏ i, 2*(modulus i : ℝ)/W (none,i))
    modulus hmodulus T hT W hW hc
    (fun z => if physicalAffineSite root z = y then (1 : ℂ) else 0)
    (by
      intro r
      exact (pmf_point_indicator_norm _ (physicalAffineSite root) y).trans_le
        (residueSmoothPMF_physical_cap root (columnResidueRepresentative modulus r.val)
          modulus hmodulus W hW (hc r) hbase y))
  exact (pmf_point_indicator_norm _ (physicalAffineSite root) y).symm.trans_le h

end Erdos3.BooleanCubeKernel

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators

namespace BooleanCubeKernel

theorem exists_selectedResidue_physical_cap {K I : Type*} [Fintype K] [Fintype I]
    (root : K → ℤ) (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z) :
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z,
      ∀ y, ((selectedResidueSmoothPMF modulus T W hW hZ).map (physicalAffineSite root) y).toReal ≤
        ∏ i, 2*(modulus i : ℝ)/W (none,i) := by
  have hc (r : T) : 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus) (residueProfileWidth modulus W) :=
    shiftedSmoothProductMass_pos_of_scales _ _ hscale
  have hZ := selectedResidueSmoothWeight_mass_pos modulus T hT W hW (fun r => by
    rw [← residueSmoothWeight_mass _ modulus hmodulus W hW]
    exact hc r)
  exact ⟨hZ, selectedResidueSmoothPMF_physical_cap root modulus hmodulus T hT W hW hZ hc
    (fun i => hscale (none,i))⟩

end BooleanCubeKernel

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace BooleanCubeKernel

end BooleanCubeKernel

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxCoordinateEquiv
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*}

variable [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem coordinateReindexedFunction_expect (e : X ≃ Y) (N : X → ℕ)
    (f : (X → ℤ) → ℝ) :
    (𝔼 y ∈ integerBox (coordinateReindexedSides e N), coordinateReindexedFunction e f y) =
      𝔼 x ∈ integerBox N, f x := by
  apply Finset.expect_bij (fun y _ x => y (e x))
  · intro y hy
    exact (coordinateReindexedSides_mem_integerBox e N y).mp hy
  · intro y _
    rfl
  · intro y _ z _ he
    funext j
    simpa only [e.apply_symm_apply] using congrFun he (e.symm j)
  · intro x hx
    refine ⟨fun j => x (e.symm j), ?_, ?_⟩
    · apply (coordinateReindexedSides_mem_integerBox e N _).mpr
      simpa only [e.symm_apply_apply] using hx
    · funext i
      simp only [e.symm_apply_apply]

end Erdos3

end

section

namespace Erdos3

variable {X Y : Type*}

variable [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBoxSliceCoordinateDisintegration
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {U : Type*} {N : U → ℕ} {q : ℕ}

variable [Fintype U] [DecidableEq U]

end Erdos3.ResidueBoxSlice

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I]

namespace ResidueBoxSlice

variable {N : I → ℕ} {q : ℕ}

end ResidueBoxSlice
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} {P N : I → ℕ} {q : ℕ}

namespace ResidueBoxSlice

variable [Fintype I] [DecidableEq I]

end ResidueBoxSlice

variable [Fintype I] [DecidableEq I]

namespace ResidueBoxSlice

omit [Fintype I] [DecidableEq I] in
theorem enlargeBox_length_lower (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) {c extra : ℝ}
    (hlength : ∀ i, Real.exp (-c) * (P i : ℝ) ≤ (S.length i : ℝ))
    (hside : ∀ i, Real.exp (-extra) * (N i : ℝ) ≤ (P i : ℝ)) (i : I) :
    Real.exp (-(c + extra)) * (N i : ℝ) ≤ ((S.enlargeBox N hPN).length i : ℝ) := by
  calc
    Real.exp (-(c + extra)) * (N i : ℝ) =
        Real.exp (-c) * (Real.exp (-extra) * (N i : ℝ)) := by
          rw [neg_add, Real.exp_add, mul_assoc]
    _ ≤ Real.exp (-c) * (P i : ℝ) :=
      mul_le_mul_of_nonneg_left (hside i) (Real.exp_pos _).le
    _ ≤ ((S.enlargeBox N hPN).length i : ℝ) := hlength i

end ResidueBoxSlice

omit [DecidableEq I] in

theorem RelativePatchSliceConclusion.enlargeBox {s rankBound : ℕ}
    {f : (I → ℤ) → ℝ} {target c extra : ℝ}
    (h : RelativePatchSliceConclusion s P f target rankBound c)
    (hPN : ∀ i, P i ≤ N i)
    (hside : ∀ i, Real.exp (-extra) * (N i : ℝ) ≤ (P i : ℝ))
    (hextra : 0 ≤ extra) :
    RelativePatchSliceConclusion s N f target rankBound (c + extra) := by
  obtain ⟨q, hq, S, d, Q, hlength, hd, hcost, hscore⟩ := h
  refine ⟨q, hq, S.enlargeBox N hPN, d, Q,
    S.enlargeBox_length_lower hPN hlength hside, hd, ?_, ?_⟩
  · exact hcost.trans (le_add_of_nonneg_right hextra)
  · exact (Real.exp_le_exp.mpr (neg_le_neg (le_add_of_nonneg_right hextra))).trans hscore

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {U : Type*} [Fintype U] [DecidableEq U] {N : U → ℕ} {q : ℕ}

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I V : Type*} {N : I → ℕ} {q : ℕ}

variable [Fintype I] [DecidableEq I]

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {K : Type*} (oldKeep keep : K → Prop)

variable {oldKeep keep} {N : K → ℕ} {q oldq : ℕ}

attribute [local irreducible] integerProgressionSupport

variable [Fintype K]

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {N : I → ℕ} {q : ℕ}

end Erdos3.ResidueBoxSlice

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RelativePatchFiniteCoordinateReduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace PolynomialPatch

variable {X Y : Type*} {s d : ℕ}

theorem coordinateEquiv_value (A : PolynomialPatch X s d) (e : X ≃ Y) (y : Y → ℝ) :
    (A.coordinateEquiv e).value y = A.value (fun i => y (e i)) := by
  rw [coordinateEquiv, reparam_value]
  simp only [MvPolynomial.aeval_X]

end PolynomialPatch

theorem relativePatchBoxScore_coordinateEquiv
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {s d : ℕ} (e : X ≃ Y) (N : X → ℕ) (f : (X → ℤ) → ℝ)
    (target : ℝ) (A : PolynomialPatch X s d) :
    relativePatchBoxScore (coordinateReindexedSides e N) (coordinateReindexedFunction e f)
      target (A.coordinateEquiv e) = relativePatchBoxScore N f target A := by
  unfold relativePatchBoxScore
  simp only [PolynomialPatch.coordinateEquiv_value]
  exact coordinateReindexedFunction_expect e N
    (fun x => (f x - target) * A.value (fun i => (x i : ℝ)))

namespace ResidueBoxSlice

variable {X Y : Type*} {N : X → ℕ} {q : ℕ}

theorem coordinateReturn_score [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {s d : ℕ} (e : X ≃ Y) (S : ResidueBoxSlice (coordinateReindexedSides e N) q)
    (f : (X → ℤ) → ℝ) (target : ℝ) (A : PolynomialPatch Y s d) :
    relativePatchSliceScore (S.coordinateReturn e) f target (A.coordinateEquiv e.symm) =
      relativePatchSliceScore S (coordinateReindexedFunction e f) target A := by
  rw [← relativePatchBoxScore_pullback, ← relativePatchBoxScore_pullback]
  have h := relativePatchBoxScore_coordinateEquiv e.symm S.length
    (S.integerPullback (coordinateReindexedFunction e f)) target A
  convert h using 1
  congr 1
  funext x
  simp only [coordinateReindexedFunction, integerPullback, integerAffine,
    coordinateReturn, Equiv.symm_apply_apply]
  rfl

end ResidueBoxSlice

theorem RelativePatchSliceConclusion.coordinateReturn
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {s rankBound : ℕ} {N : X → ℕ} {f : (X → ℤ) → ℝ} {target cost : ℝ}
    (e : X ≃ Y)
    (h : RelativePatchSliceConclusion s (coordinateReindexedSides e N)
      (coordinateReindexedFunction e f) target rankBound cost) :
    RelativePatchSliceConclusion s N f target rankBound cost := by
  obtain ⟨q, hq, S, d, A, hlength, hd, hcomplexity, hscore⟩ := h
  refine ⟨q, hq, S.coordinateReturn e, d, A.coordinateEquiv e.symm, ?_,
    hd, hcomplexity, ?_⟩
  · intro i
    simpa only [coordinateReindexedSides, ResidueBoxSlice.coordinateReturn,
      Equiv.symm_apply_apply] using hlength (e i)
  · rwa [ResidueBoxSlice.coordinateReturn_score]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ProductiveAbsoluteCRTPatches
namespace OAI

section

namespace Erdos3

namespace IntegerVectorAPFree

variable {I J : Type*} {k : ℕ}

theorem mono {A B : Set (I → ℤ)} (hA : IntegerVectorAPFree A k) (hBA : B ⊆ A) :
    IntegerVectorAPFree B k := by
  intro a d hd
  obtain ⟨i, hi⟩ := hA a d hd
  exact ⟨i, fun h => hi (hBA h)⟩

end IntegerVectorAPFree

namespace BooleanCubeKernel

theorem joint_sample_progression_free {K X : Type*} [Fintype K]
    {A : Set (X → ℤ)} {k : ℕ} (hA : IntegerVectorAPFree A k) (hk : 2 ≤ k)
    (z : (X → ℤ) × (Option K × X → ℤ)) (domain : Set (K → ℤ))
    (hinj : Set.InjOn (fun x => jointIntegerPhysicalSite x z) domain) :
    IntegerVectorAPFree (domain ∩ (fun x => jointIntegerPhysicalSite x z) ⁻¹' A) k := by
  classical
  let L : (K → ℤ) →+ (X → ℤ) :=
    (Matrix.of (fun i j => z.2 (some j,i))).mulVecLin.toAddMonoidHom
  let b : X → ℤ := fun i => z.1 i + z.2 (none,i)
  have he (x : K → ℤ) : jointIntegerPhysicalSite x z = b + L x := by
    funext i
    change z.1 i + (z.2 (none,i) + ∑ j, x j * z.2 (some j,i)) =
      (z.1 i + z.2 (none,i)) + ∑ j, z.2 (some j,i) * x j
    rw [← add_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h := hA.affine_preimage hk L b domain (by simpa only [he] using hinj)
  simpa only [he] using h

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

namespace IntegerVectorAPFree

end IntegerVectorAPFree

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedZeroLayerLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)

variable (N : X → ℕ) (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

theorem allocatedCenteredJointDensityMass_zero_layers
    (hbase : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty)
    (hwidth : ∀ z, 0 < allocatedExternalCandidateWidths B U b S N τ ξ z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells
      (allocatedExternalCandidateWidths B U b S N τ ξ) z) :
    selectedJointDensityMass (trimmedIntegerBox N (spatialTrimMargin τ N)) stride cells
      (allocatedExternalCandidateWidths B U b S N τ ξ)
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center) = 1 := by
  rw [← selectedJointReference_densityMass _ hbase _ _ _ hwidth hZ]
  simp only [allocatedCenteredJointDensity_zero_layers, FiniteProbabilityWeights.mean_const]

theorem allocatedExternalCandidateSampler_zero_layers
    (hN : ∀ x, 0 < N x) (hτ : 0 < τ) (hξ : 0 < ξ)
    (hstride : ∀ x, 0 < stride x)
    (hbase : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells
      (allocatedExternalCandidateWidths B U b S N τ ξ) z) :
    AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center := by
  refine ⟨hN, hτ, hξ, hstride, hbase, hZ, ?_⟩
  rw [allocatedCenteredJointDensityMass_zero_layers B U b S hb o hR hσ poly hm
    center N τ ξ stride cells hbase
    (narrowTrimmedSpatialWidths_pos (allocatedExternalCandidateRootBudget_nonneg B U b S)
      hτ hξ N hN) hZ]
  norm_num

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem selectedJointReference_trimmed_complex_compare {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hwidth : ∀ i, physicalSiteWidth root W i ≤ (R i : ℝ))
    (f : (I → ℤ) → ℂ) (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1) :
    ‖(selectedJointReference (trimmedIntegerBox N R) (trimmedIntegerBox_nonempty N R hR)
      modulus T W hW hZ).complexMean
        (fun z => f (jointIntegerPhysicalSite root (z.1.val, z.2.val))) -
      𝔼 x ∈ integerBox N, f x‖ ≤ 2 * ∑ i, 2 * (R i : ℝ) / N i := by
  rw [selectedJointReference, FiniteProbabilityWeights.complexMean_prod]
  have he (a : I → ℤ) := selectedResidueFiniteLaw_complexMean modulus T W hW hZ
    (fun z => f (a + integerPhysicalSite root z))
  simp only [jointIntegerPhysicalSite, he]
  rw [FiniteProbabilityWeights.uniformFinset_complexMean (trimmedIntegerBox N R)
    (trimmedIntegerBox_nonempty N R hR) (fun a =>
      ∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ) *
        f (a + integerPhysicalSite root z))]
  exact selectedResidue_trimmed_reference_compare root N R hR modulus T W hW hZ hwidth f hf

theorem selectedJointReference_trimmed_compare {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hwidth : ∀ i, physicalSiteWidth root W i ≤ (R i : ℝ))
    (f : (I → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, |f x| ≤ 1) :
    |(selectedJointReference (trimmedIntegerBox N R) (trimmedIntegerBox_nonempty N R hR)
      modulus T W hW hZ).mean
        (fun z => f (jointIntegerPhysicalSite root (z.1.val, z.2.val))) -
      𝔼 x ∈ integerBox N, f x| ≤ 2 * ∑ i, 2 * (R i : ℝ) / N i := by
  have h := selectedJointReference_trimmed_complex_compare root N R hR modulus T W hW hZ
    hwidth (fun x => (f x : ℂ)) (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hf)
  have hr := (Complex.abs_re_le_norm _).trans h
  simpa only [Complex.sub_re, FiniteProbabilityWeights.complexMean_re,
    Complex.ofReal_re, Finset.expect, Complex.smul_re, Complex.re_sum] using hr

theorem selectedJointReference_noninjectivity_le {K I S : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (A : Finset (I → ℤ)) (hA : A.Nonempty)
    (site : S → K → ℤ) (hsite : Function.Injective site) (i : I)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {L : ℝ} (hL : 0 < L) (hwidth : ∀ k, L ≤ W (some k, i)) :
    (selectedJointReference A hA modulus T W hW hZ).mean
      (fun z => noninjectivityIndicator
        (fun s => jointIntegerPhysicalSite (site s) (z.1.val, z.2.val))) ≤
      (Fintype.card S : ℝ)^2 * (2 * (modulus i : ℝ) / L) := by
  apply FiniteProbabilityWeights.noninjectivity_le _ _ (by positivity)
  intro s t hst
  rw [selectedJointReference_collision]
  exact selectedResidue_distinct_collision_le (site s) (site t) (fun h => hst (hsite h)) i
    modulus hmodulus T hT W hW hZ hscale hL hwidth

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators Classical

attribute [local irreducible] selectedJointReference selectedResidueFiniteLaw

theorem productive_finite_samples {Ω S Y : Type*}
    [Fintype Ω] [Fintype S] [Nonempty S]
    (law : FiniteProbabilityWeights Ω) (image : Ω → S → Y)
    (f : Y → ℝ) {a σ : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ)
    (hf : ∀ y, f y ≤ 1)
    (hmarginal : ∀ r, a + 7 * σ / 8 ≤ law.mean (fun z => f (image z r)))
    (hcollision : law.mean (fun z => noninjectivityIndicator (image z)) ≤ σ / 16) :
    ∃ productive : Finset Ω, σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective (image z)) ∧
      ∀ z ∈ productive, a + σ / 2 ≤ 𝔼 r : S, f (image z r) := by
  let score := fun z => 𝔼 r : S, (f (image z r) - a)
  let bad := Finset.univ.filter (fun z => ¬Function.Injective (image z))
  have hscore (z) : score z ≤ 1 := by
    dsimp only [score]
    apply Finset.expect_le Finset.univ_nonempty
    intro r _
    linarith [hf (image z r)]
  have hbad : law.mass bad ≤ σ / 16 := by
    have he : law.mass bad = law.mean (fun z => noninjectivityIndicator (image z)) := by
      rw [← law.mean_indicator]
      congr 1
      funext z
      by_cases hz : Function.Injective (image z) <;> simp [bad, hz, noninjectivityIndicator]
    rw [he]
    exact hcollision
  have hmeanScore : 7 * σ / 8 ≤ law.mean score := by
    have he := law.mean_comm (FiniteProbabilityWeights.uniform S)
      (fun z r => f (image z r) - a)
    simp only [FiniteProbabilityWeights.uniform_mean] at he
    change law.mean score = _ at he
    rw [he]
    apply Finset.le_expect Finset.univ_nonempty
    intro r _
    rw [law.mean_sub, law.mean_const]
    linarith [hmarginal r]
  let productive := Finset.univ.filter (fun z => z ∉ bad ∧ σ / 2 ≤ score z)
  refine ⟨productive, ?_, ?_, ?_⟩
  · have h := law.productive_mass_lower_bound score bad (a := σ / 2)
      (by positivity) hscore
    change _ ≤ law.mass productive at h
    linarith
  · intro z hz
    have h := (Finset.mem_filter.mp hz).2.1
    simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using h
  · intro z hz
    have h := (Finset.mem_filter.mp hz).2.2
    simp only [score, Finset.expect_sub_distrib, Fintype.expect_const] at h
    linarith

namespace BooleanCubeKernel

theorem exists_unconditioned_productive_family
    {K X S : Type*} [Fintype K] [Fintype X] [DecidableEq X]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (N R : X → ℕ) (hR : ∀ i, 2 * R i < N i)
    (site : S → K → ℤ) (hsite : Function.Injective site) (i : X)
    (modulus : X → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (T : Finset (ColumnResiduePattern (Option K) X modulus)) (hT : T.Nonempty)
    (W : Option K × X → ℝ) (hW : ∀ z, 0 < W z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {L a σ : ℝ} (hL : 0 < L) (hwidth : ∀ k, L ≤ W (some k,i))
    (hfit : ∀ r j, physicalSiteWidth (site r) W j ≤ (R j : ℝ))
    (ha : 0 ≤ a) (hσ : 0 < σ)
    (hboundary : 2 * (∑ j, 2 * (R j : ℝ) / N j) ≤ σ / 8)
    (hcollision : (Fintype.card S : ℝ)^2 * (2 * (modulus i : ℝ) / L) ≤ σ / 16)
    (f : (X → ℤ) → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hmean : a + σ ≤ 𝔼 x ∈ integerBox N, f x) :
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z,
    let law := selectedJointReference (trimmedIntegerBox N R)
      (trimmedIntegerBox_nonempty N R hR) modulus T W hW hZ
    ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
      σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective
        (fun r => jointIntegerPhysicalSite (site r) (z.1.val,z.2.val))) ∧
      (∀ z ∈ productive, a + σ / 2 ≤
        𝔼 r : S, f (jointIntegerPhysicalSite (site r) (z.1.val,z.2.val))) ∧
      ∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1, ∀ r,
        jointIntegerPhysicalSite (site r) (z.1.val,z.2.val) ∈ integerBox N := by
  obtain ⟨hZ, _⟩ := exists_selectedResidue_physical_cap (0 : K → ℤ)
    modulus hmodulus T hT W hW hscale
  refine ⟨hZ, ?_⟩
  intro law
  let image := fun (z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) r =>
    jointIntegerPhysicalSite (site r) (z.1.val,z.2.val)
  have hmarginal (r : S) : a + 7 * σ / 8 ≤ law.mean (fun z => f (image z r)) := by
    have h := selectedJointReference_trimmed_compare (site r) N R hR modulus T W hW hZ
      (hfit r) f (fun x _ => abs_le.mpr ⟨by linarith [(hf x).1], (hf x).2⟩)
    have hlo := (abs_le.mp h).1
    change -_ ≤ law.mean (fun z => f (image z r)) - _ at hlo
    linarith
  have hbad := selectedJointReference_noninjectivity_le (trimmedIntegerBox N R)
    (trimmedIntegerBox_nonempty N R hR) site hsite i modulus hmodulus T hT W hW hZ
    hscale hL hwidth
  obtain ⟨productive, hmass, hinj, hlocal⟩ := productive_finite_samples law image f ha hσ
    (fun x => (hf x).2) hmarginal (hbad.trans hcollision)
  refine ⟨productive, hmass, hinj, hlocal, ?_⟩
  intro z r
  exact jointIntegerPhysicalSite_mem_box (site r) N R (fun j => (hR j).le) W (hfit r) z

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem residueBoxIntegerPoint_sum_abs_le {K : Type*} [Fintype K]
    (P : K → ℕ) [∀ k, NeZero (P k)] (u : ∀ k, ZMod (P k)) :
    (∑ k, |(residueBoxIntegerPoint P u k : ℝ)|) ≤ unconditionedResidueSiteBound P := by
  apply Finset.sum_le_sum
  intro k _
  change |((u k).val : ℝ)| ≤ (P k : ℝ)
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (ZMod.val_lt (u k)).le

theorem unconditionedCollisionWidth_pos {K : Type*} [Fintype K] [DecidableEq K]
    (P : K → ℕ) [∀ k, NeZero (P k)] {σ : ℝ} (hσ : 0 < σ) :
    0 < unconditionedCollisionWidth P σ := by
  have hc : 0 < (Fintype.card (∀ k, ZMod (P k)) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := ∀ k, ZMod (P k))
  unfold unconditionedCollisionWidth
  positivity

theorem unconditionedCollisionWidth_collision {K : Type*} [Fintype K] [DecidableEq K]
    (P : K → ℕ) [∀ k, NeZero (P k)] {σ : ℝ} (hσ : 0 < σ) :
    (Fintype.card (∀ k, ZMod (P k)) : ℝ) ^ 2 * (2 / unconditionedCollisionWidth P σ) = σ / 16 := by
  have hc : (Fintype.card (∀ k, ZMod (P k)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := ∀ k, ZMod (P k))
  unfold unconditionedCollisionWidth
  field_simp
  ring

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type*} {I J : Fin 0 → Type*} {n : Fin 0 → ℕ}
    (B : LayerSamplerAxis I n → Type*)

variable [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ}

variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedExternalCandidateSides_zero_layers_fun :
    allocatedExternalCandidateSides B U b S =
      fun _ : LayerSamplerVariables G I n B => S.value :=
  funext (allocatedExternalCandidateSides_zero_layers B U b S)

theorem allocatedExternalCandidateRootBudget_zero_layers :
    allocatedExternalCandidateRootBudget B U b S =
      (Fintype.card G : ℝ) * S.value := by
  unfold allocatedExternalCandidateRootBudget
  rw [zeroLayerVariables_card]

theorem allocatedExternalCandidateWidths_zero_layers
    (N : X → ℕ) (τ ξ : ℝ) :
    allocatedExternalCandidateWidths B U b S N τ ξ =
      trimmedSpatialWidths (K := LayerSamplerVariables G I n B)
        ((Fintype.card G : ℝ) * S.value) τ N := by
  funext z
  rw [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_zero_layers]
  rcases z with ⟨_ | k, x⟩
  · rfl
  · cases k with
    | inl g => rfl
    | inr a => exact Fin.elim0 a.1.1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I J : Fin m → Type*} {n : Fin m → ℕ}
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (Fin (n j))]
    (B : LayerSamplerAxis I n → Type*)

variable [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}

variable (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {G X : Type*} [Fintype G]
    {I J : Fin 0 → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

open Module Submodule

end Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRecoveredPreparedFreeze
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G V : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

include hσ1 hC hchart

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module Submodule VectorPolynomial
open scoped BigOperators TensorProduct

variable {X G : Type} [Fintype G] {s D E m : ℕ}
variable {A : PolynomialPatch X s (D + E)}
variable (L : RankPreparationFamily X (Fin D) m)
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (L j).space)ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (L j).space))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B (fun j => (L j).space) b R σ)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped Classical

variable {G X : Type*} {I E J : Fin 0 → Type*} {n : Fin 0 → ℕ}
variable (B : LayerSamplerAxis I n → Type*)

variable [Fintype G]
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

omit [∀ j, Fintype (J j)] in
theorem allocatedZeroLayerCenterLift_spec
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => allocatedZeroLayerCenterLift U s.1))) := by
  exact Subsingleton.elim _ _

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin 0 → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem allocatedZeroLayer_recovered_sample
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :
    AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      c a v sample (allocatedZeroLayerFramedRead (E := E) B a v) := by
  refine ⟨rfl, Subsingleton.elim _ _, ?_, ?_, ?_⟩
  · intro j
    exact Fin.elim0 j
  · intro d
    exact Fin.elim0 d.1.1
  · intro j
    exact Fin.elim0 j

theorem allocatedZeroLayer_recovered
    (a : X → ℤ) (v : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      (allocatedZeroLayerCenterLift U) a v (allocatedZeroLayerSample B)
      (allocatedZeroLayerFramedRead (E := E) B a v) :=
  allocatedZeroLayer_recovered_sample B U b hb o S hR hσ poly hm _ _ _ _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m s D E : ℕ} {X G : Type} [Fintype X] [Fintype G]
variable (L : RankPreparationFamily X (Fin D) m)
variable {I Deck : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (Deck j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchPositivePowerInduction
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem integerBox_real_expect_eq_residue {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) [∀ i, NeZero (N i)] (f : (X → ℤ) → ℝ) :
    (𝔼 x ∈ integerBox N, f x) = 𝔼 u, f (residueBoxIntegerPoint N u) := by
  symm
  apply Finset.expect_bij (fun u _ => residueBoxIntegerPoint N u)
  · intro u _
    exact (mem_integerBox N _).mpr (fun i =>
      ⟨Int.natCast_nonneg _, by
        change ((u i).val : ℤ) < N i
        exact_mod_cast (u i).val_lt⟩)
  · intro u _
    rfl
  · intro u _ v _ h
    funext i
    apply ZMod.val_injective
    have hi := congrFun h i
    dsimp only [residueBoxIntegerPoint] at hi
    exact_mod_cast hi
  · intro x hx
    have hx' := (mem_integerBox N x).mp hx
    refine ⟨fun i => (x i : ZMod (N i)), Finset.mem_univ _, ?_⟩
    funext i
    dsimp only [residueBoxIntegerPoint]
    rw [ZMod.val_intCast, Int.emod_eq_of_lt (hx' i).1 (hx' i).2]

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial
open scoped BigOperators TensorProduct Classical

namespace ResidueBoxSlice

end ResidueBoxSlice

namespace PolynomialPatch.LowestLayerModel

variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {s D E j R : ℕ} {A : PolynomialPatch X s (D + E)}

end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

variable {K X : Type*} [Fintype K] [Fintype X] [DecidableEq K] [DecidableEq X]

theorem unconditionedAbsoluteSample_input
    (s : ℕ) (N : X → ℕ) (P : K → ℕ) [∀ i, NeZero (P i)]
    (z : (X → ℤ) × (Option K × X → ℤ)) (f : (X → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hinj : Function.Injective (fun u : ∀ i, ZMod (P i) =>
      jointIntegerPhysicalSite (residueBoxIntegerPoint P u) z))
    (hinside : ∀ u : ∀ i, ZMod (P i),
      jointIntegerPhysicalSite (residueBoxIntegerPoint P u) z ∈ integerBox N)
    {a : ℝ}
    (hmean : a ≤ 𝔼 u, f (jointIntegerPhysicalSite (residueBoxIntegerPoint P u) z)) :
    (∀ x ∈ integerBox P, f (jointIntegerPhysicalSite x z) ∈ Set.Icc (0 : ℝ) 1) ∧
      IntegerVectorAPFree
        {x | x ∈ integerBox P ∧ f (jointIntegerPhysicalSite x z) ≠ 0} (s + 2) ∧
      a ≤ 𝔼 x ∈ integerBox P, f (jointIntegerPhysicalSite x z) := by
  have hrep (x : K → ℤ) (hx : x ∈ integerBox P) :
      residueBoxIntegerPoint P (fun i => (x i : ZMod (P i))) = x := by
    funext i
    have hxi := (mem_integerBox P x).mp hx i
    dsimp only [residueBoxIntegerPoint]
    rw [ZMod.val_intCast, Int.emod_eq_of_lt hxi.1 hxi.2]
  have hinside' (x : K → ℤ) (hx : x ∈ integerBox P) :
      jointIntegerPhysicalSite x z ∈ integerBox N := by
    simpa only [hrep x hx] using hinside (fun i => (x i : ZMod (P i)))
  have hinj' : Set.InjOn (fun x => jointIntegerPhysicalSite x z)
      (↑(integerBox P) : Set (K → ℤ)) := by
    intro x hx y hy he
    have hres : (fun i => (x i : ZMod (P i))) = (fun i => (y i : ZMod (P i))) :=
      hinj (by simpa only [hrep x hx, hrep y hy] using he)
    calc
      x = residueBoxIntegerPoint P (fun i => (x i : ZMod (P i))) := (hrep x hx).symm
      _ = residueBoxIntegerPoint P (fun i => (y i : ZMod (P i))) :=
        congrArg (residueBoxIntegerPoint P) hres
      _ = y := hrep y hy
  refine ⟨fun x hx => hf _ (hinside' x hx), ?_, ?_⟩
  · apply (joint_sample_progression_free hfree (by omega) z
      (↑(integerBox P) : Set (K → ℤ)) hinj').mono
    intro x hx
    exact ⟨hx.1, hinside' x hx.1, hx.2⟩
  · rw [integerBox_real_expect_eq_residue]
    exact hmean

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3
open VectorPolynomial
open scoped BigOperators TensorProduct

namespace PolynomialPatch.LowestLayerModel

end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators

variable {K X : Type*} [Fintype K]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct Classical

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial Module
open scoped BigOperators TensorProduct Classical

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial Module
open scoped BigOperators TensorProduct Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.UnconditionedRootBudgetAbsoluteFamily
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

namespace BooleanCubeKernel

theorem exists_unconditioned_rootBudget_productive_family_equiv
    {K J X : Type*} [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]
    [Fintype X] [DecidableEq X]
    (P : J → ℕ) [∀ k, NeZero (P k)] (e : K ≃ J)
    (B : ℝ) (hBP : unconditionedResidueSiteBound P ≤ B) (i : X)
    {a σ : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (N : X → ℕ)
    (hN : ∀ j, unconditionedSpatialWidthCutoff B
      (unconditionedSpatialTrimFraction (Fintype.card X) σ) (unconditionedCollisionWidth P σ) ≤ (N j : ℝ))
    (f : (X → ℤ) → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hmean : a + σ ≤ 𝔼 x ∈ integerBox N, f x) :
    let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
    let W := trimmedSpatialWidths (K := K) B τ N
    let R := spatialTrimMargin τ N
    ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
    let law := selectedJointReference (trimmedIntegerBox N R)
      (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
    ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
      σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective (fun u : ∀ k, ZMod (P k) =>
        jointIntegerPhysicalSite (fun k => residueBoxIntegerPoint P u (e k)) (z.1.val,z.2.val))) ∧
      (∀ z ∈ productive, a + σ / 2 ≤ 𝔼 u : ∀ k, ZMod (P k),
        f (jointIntegerPhysicalSite (fun k => residueBoxIntegerPoint P u (e k)) (z.1.val,z.2.val))) ∧
      ∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1, ∀ u : ∀ k, ZMod (P k),
        jointIntegerPhysicalSite (fun k => residueBoxIntegerPoint P u (e k)) (z.1.val,z.2.val) ∈ integerBox N := by
  let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
  let W := trimmedSpatialWidths (K := K) B τ N
  let R := spatialTrimMargin τ N
  have hB : 0 ≤ B :=
    (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _) :
      0 ≤ unconditionedResidueSiteBound P).trans hBP
  obtain ⟨_, _, hW, hscale, hwidth, hR, hboundary⟩ :=
    unconditionedSpatialWidthBudget (K := K) hB hσ hσ1 N hN
  have hτ : 0 < τ := (unconditionedSpatialTrimFraction_bounds (Fintype.card X) hσ hσ1).1
  have hsite : Function.Injective (fun (u : ∀ j, ZMod (P j)) (k : K) =>
      residueBoxIntegerPoint P u (e k)) := by
    intro u v he
    funext j
    apply ZMod.val_injective
    have hj := congrFun he (e.symm j)
    simp only [Equiv.apply_symm_apply] at hj
    change ((u j).val : ℤ) = ((v j).val : ℤ) at hj
    exact_mod_cast hj
  have hroot (u : ∀ j, ZMod (P j)) :
      (∑ k : K, |(residueBoxIntegerPoint P u (e k) : ℝ)|) ≤ B := by
    rw [e.sum_comp (fun j => |(residueBoxIntegerPoint P u j : ℝ)|)]
    exact (residueBoxIntegerPoint_sum_abs_le P u).trans hBP
  have hfit (u : ∀ j, ZMod (P j)) (j : X) :
      physicalSiteWidth (fun k => residueBoxIntegerPoint P u (e k)) W j ≤ (R j : ℝ) :=
    spatialTrimMargin_fits hB hτ.le (fun k => residueBoxIntegerPoint P u (e k))
      (hroot u) N j
  obtain ⟨hZ, productive, hmass, hinj, hlocal, hinside⟩ :=
    exists_unconditioned_productive_family N R hR (fun u k => residueBoxIntegerPoint P u (e k)) hsite i
      (fun _ : X => 1) (fun _ => by decide) {0} (Finset.singleton_nonempty _) W hW hscale
      (unconditionedCollisionWidth_pos P hσ) (fun k => hwidth (some k, i)) hfit ha hσ hboundary
      (by simpa only [Nat.cast_one, mul_one] using (unconditionedCollisionWidth_collision P hσ).le)
      f hf hmean
  exact ⟨hW, hR, hZ, productive, hmass, hinj, hlocal, hinside⟩

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace BooleanCubeKernel

theorem jointIntegerPhysicalSite_comp_equiv
    {K J X : Type*} [Fintype K] [Fintype J]
    (e : K ≃ J) (x : J → ℤ)
    (z : (X → ℤ) × (Option K × X → ℤ)) :
    jointIntegerPhysicalSite (fun k => x (e k)) z =
      jointIntegerPhysicalSite x
        (z.1, fun w => z.2 (Option.map e.symm w.1, w.2)) := by
  funext i
  simp only [jointIntegerPhysicalSite, integerPhysicalSite, Pi.add_apply,
    Option.map_none, Option.map_some]
  congr 2
  apply Fintype.sum_equiv e
  intro k
  simp only [Equiv.symm_apply_apply]

theorem exists_unconditioned_rootBudget_absolute_family_equiv
    (s n₀ : ℕ) {K X : Type*} [Fintype K] [DecidableEq K]
    [Fintype X] [DecidableEq X]
    (P : Fin n₀ → ℕ) [∀ k, NeZero (P k)]
    (e : K ≃ Fin n₀) (B : ℝ) (hBP : unconditionedResidueSiteBound P ≤ B) (i : X)
    {p a Λ σ : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (d₀ : ℕ) (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hprime : ∀ k, (P k).Prime) (hdistinct : Function.Injective P)
    (hcomparable : ∀ k j, P k ≤ 2 ^ (n₀ + 1) * P j)
    (hcutoff : ∀ k, Real.exp p ≤ (P k : ℝ))
    (N : X → ℕ)
    (hN : ∀ j, unconditionedSpatialWidthCutoff B
      (unconditionedSpatialTrimFraction (Fintype.card X) σ) (unconditionedCollisionWidth P σ) ≤ (N j : ℝ))
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hmean : a + σ ≤ 𝔼 x ∈ integerBox N, f x) :
    let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
    let W := trimmedSpatialWidths (K := K) B τ N
    let R := spatialTrimMargin τ N
    ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
    let law := selectedJointReference (trimmedIntegerBox N R)
      (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
    ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
      σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective (fun u : ∀ k, ZMod (P k) =>
        jointIntegerPhysicalSite (fun k => residueBoxIntegerPoint P u (e k)) (z.1.val,z.2.val))) ∧
      (∀ z ∈ productive,
        RelativePatchSliceConclusion s P
          (fun x => f (jointIntegerPhysicalSite (fun k => x (e k)) (z.1.val,z.2.val))) Λ d₀ p) ∧
      ∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1,
        ∀ u : ∀ k, ZMod (P k),
        jointIntegerPhysicalSite (fun k => residueBoxIntegerPoint P u (e k)) (z.1.val,z.2.val) ∈ integerBox N := by
  let f₀ := fun x => if x ∈ integerBox N then f x else 0
  have hf₀ : ∀ x, f₀ x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    by_cases hx : x ∈ integerBox N
    · simpa only [f₀, if_pos hx] using hf x hx
    · simp only [f₀, if_neg hx, Set.mem_Icc, le_refl, zero_le_one, and_self]
  have hmean₀ : a + σ ≤ 𝔼 x ∈ integerBox N, f₀ x := by
    have he : (𝔼 x ∈ integerBox N, f₀ x) = 𝔼 x ∈ integerBox N, f x :=
      Finset.expect_congr rfl (fun x hx => if_pos hx)
    rwa [he]
  obtain ⟨hW, hR, hZ, productive, hmass, hinj, hlocal, hinside⟩ :=
    exists_unconditioned_rootBudget_productive_family_equiv P e B hBP i ha hσ hσ1 N hN f₀ hf₀ hmean₀
  refine ⟨hW, hR, hZ, productive, hmass, hinj, ?_, hinside⟩
  intro z hz
  have hlocal' : a ≤ 𝔼 u : ∀ k, ZMod (P k),
      f (jointIntegerPhysicalSite (fun k => residueBoxIntegerPoint P u (e k)) (z.1.val,z.2.val)) := by
    have h := hlocal z hz
    simp only [f₀, if_pos (hinside z _)] at h
    linarith
  let zP : (X → ℤ) × (Option (Fin n₀) × X → ℤ) :=
    (z.1.val, fun w => z.2.val (Option.map e.symm w.1, w.2))
  have hphysical (x : Fin n₀ → ℤ) :
      jointIntegerPhysicalSite (fun k => x (e k)) (z.1.val,z.2.val) =
        jointIntegerPhysicalSite x zP :=
    jointIntegerPhysicalSite_comp_equiv e x (z.1.val,z.2.val)
  obtain ⟨hbound, hAP, hmean⟩ := unconditionedAbsoluteSample_input
    s N P zP f hf hfree
      (by simpa only [hphysical] using hinj z hz)
      (by simpa only [hphysical] using hinside z)
      (by simpa only [hphysical] using hlocal')
  simpa only [hphysical] using habsolute P hprime hdistinct hcomparable hcutoff
    (fun x => f (jointIntegerPhysicalSite x zP)) hbound hAP hmean

end BooleanCubeKernel
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedPatchShearFiberCandidateScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal TensorProduct

namespace PolynomialPatch

variable {X Y : Type*} {s d : ℕ} (P : PolynomialPatch X s d)
  [Fintype (PolynomialShearIndex P.weight)]

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {I : Type*} [Fintype I] [DecidableEq I]
  {keep : I → Prop} [DecidablePred keep] {N : I → ℕ} {q : ℕ}

end ResidueBoxSlice

namespace PolynomialSlots

variable {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ} {w : Fin d → ℕ}

omit [Fintype I] [DecidableEq I] in
theorem coordinateFiberForm_loweringAt_integer (A : PolynomialSlots I d w)
    (keep : I → Prop) [DecidablePred keep] (fixed : {i // ¬keep i} → ℤ)
    (u : {i // keep i} → ℤ) :
    (A.coordinateFiberForm keep fixed).loweringAt (fun i => (u i : ℝ)) =
      A.loweringAt (fun i => ((finiteSplitPoint keep u fixed i : ℤ) : ℝ)) := by
  rw [coordinateFiberForm, reparam_loweringAt]
  congr 1
  funext i
  by_cases hi : keep i <;> simp [coordinateFiberParameters, finiteSplitPoint, hi]

end PolynomialSlots

namespace PolynomialPatch

variable {X I : Type*} [Fintype I] [DecidableEq I] {s d : ℕ}
    (P : PolynomialPatch X s d)

theorem fiberSliceLaw_shear_score_eq_fullSliceLaw
    (A : PolynomialSlots I d P.weight) (keep : I → Prop) [DecidablePred keep]
    {N : I → ℕ} {q : ℕ}
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (hlen : ∀ i, 0 < S.length i) (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ))
    (f : (I → ℤ) → ℝ) (lam : ℝ) :
    (S.fiberSliceLaw hlen fixed hfixed).mean (fun u => (f u.val - lam) *
      (P.form.shearTransformedSlots P.weight_mono
        (A.loweringAt (fun i => (u.val i : ℝ)))).patchValue P.kernel) =
      (S.fullSliceLaw hlen).mean (fun u => (f (finiteSplitPoint keep u.val fixed) - lam) *
        (P.form.shearTransformedSlots P.weight_mono
          ((A.coordinateFiberForm keep fixed).loweringAt
            (fun i => (u.val i : ℝ)))).patchValue P.kernel) := by
  rw [S.fiberSliceLaw_mean hlen fixed hfixed, S.fullSliceLaw_mean hlen]
  simp only [PolynomialSlots.coordinateFiberForm_loweringAt_integer]
  rfl

end PolynomialPatch

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionedArbitraryFixedPatchFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem exists_relative_finite_returned_slice_normalization (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {Ω J : Type*}
      [Fintype Ω] [Nonempty Ω] [Fintype J] [DecidableEq J]
      (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω),
      0 < outer.mass productive →
      ∀ (P : J → ℕ), (∀ i, 0 < P i) →
      ∀ (p : ℝ), 0 ≤ p → ∀ (Λ : ℝ), Λ ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (d₀ : ℕ) (f : Ω → (J → ℤ) → ℝ),
      (∀ h x, x ∈ integerBox P → f h x ∈ Set.Icc (0 : ℝ) 1) →
      (∀ h ∈ productive, RelativePatchSliceConclusion s P (f h) Λ d₀ p) →
      let q := p + (Fintype.card J : ℝ) + 2
      let D := min d₀ ⌊p⌋₊
      ∃ (localLaw : Ω → FiniteProbabilityWeights (integerBox P))
        (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots J d w) (localForm : Ω → PolynomialSlots J d w)
        (retained : Finset Ω),
        d ≤ D ∧ d ≤ d₀ ∧ (∀ i, 1 ≤ w i) ∧ (∀ i, w i ≤ s) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((q + 2) ^ E) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ (q + 2) ^ E) ∧
        retained ⊆ productive ∧
        (outer.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ outer.mass retained ∧
        (∀ h ∈ retained, ∃ r, 0 < r ∧ ∃ (S : ResidueBoxSlice P r)
          (hlen : ∀ i, 0 < S.length i),
          (∀ i, Real.exp (-p) * (P i : ℝ) ≤ (S.length i : ℝ)) ∧
            localLaw h = S.fullSliceLaw hlen) ∧
        ∀ h ∈ retained, Real.exp (-((q + 2) ^ E)) ≤ (localLaw h).mean
          (fun x => (f h x.val - Λ) * (B.shearTransformedSlots hw
            ((localForm h).loweringAt (fun i => (x.val i : ℝ)))).patchValue Ψ) := by
  obtain ⟨E, hE, hfixed⟩ := exists_varying_rank_fixed_patch_function s
  refine ⟨E, hE, ?_⟩
  intro Ω J _ _ _ _ outer productive hmass P hP p hp Λ hΛ d₀ f hf hreturn
  let q := p + (Fintype.card J : ℝ) + 2
  let D := min d₀ ⌊p⌋₊
  have hne : productive.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hmass
    linarith)
  obtain ⟨h₀, hh₀⟩ := hne
  obtain ⟨ddefault, Qdefault, lawdefault, hddefault, _, hlipdefault, _, _⟩ :=
    (hreturn h₀ hh₀).tighten_rank.exists_full_law hP
  have hall (h : Ω) : ∃ (d : ℕ) (Q : PolynomialPatch J s d)
      (localLaw : FiniteProbabilityWeights (integerBox P)),
      d ≤ D ∧ (Q.kernel.lip : ℝ) ≤ Real.exp p ∧
      (h ∈ productive → Real.exp (-p) ≤ localLaw.mean
        (fun x => (f h x.val - Λ) * Q.value (fun i => (x.val i : ℝ)))) ∧
      (h ∈ productive → ∃ r, 0 < r ∧ ∃ (S : ResidueBoxSlice P r)
        (hlen : ∀ i, 0 < S.length i),
        (∀ i, Real.exp (-p) * (P i : ℝ) ≤ (S.length i : ℝ)) ∧
          localLaw = S.fullSliceLaw hlen) := by
    by_cases hh : h ∈ productive
    · obtain ⟨d, Q, localLaw, hd, _, hlip, hscore, hslice⟩ :=
        (hreturn h hh).tighten_rank.exists_full_law hP
      exact ⟨d, Q, localLaw, hd, hlip, fun _ => hscore, fun _ => hslice⟩
    · exact ⟨ddefault, Qdefault, lawdefault, hddefault, hlipdefault,
        fun hmem => (hh hmem).elim, fun hmem => (hh hmem).elim⟩
  choose d patch localLaw hd hlip hpositive hslice using hall
  have hpq : p ≤ q := by
    dsimp only [q]
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card J)]
  have hq : 0 ≤ q := hp.trans hpq
  have hD : (D : ℝ) ≤ q :=
    (Nat.cast_le.mpr (Nat.min_le_right d₀ ⌊p⌋₊)).trans ((Nat.floor_le hp).trans hpq)
  have hJ : (Fintype.card J : ℝ) ≤ q := by dsimp only [q]; linarith
  have hLip (h) : ((patch h).kernel.lip : ℝ) ≤ Real.exp q :=
    (hlip h).trans (Real.exp_le_exp.mpr hpq)
  let point := fun (_ : Ω) (x : integerBox P) => x.val
  let score := fun h (x : integerBox P) => f h x.val - Λ
  have hscore (h) (x : integerBox P) : |score h x| ≤ 1 := by
    dsimp only [score]
    obtain ⟨hf0, hf1⟩ := hf h x.val x.property
    exact abs_le.mpr ⟨by linarith [hΛ.2], by linarith [hΛ.1]⟩
  have hpositive' (h) (hh : h ∈ productive) : Real.exp (-q) ≤ (localLaw h).mean
      (fun x => score h x * (patch h).value (fun i => (point h x i : ℝ))) :=
    (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (hpositive h hh)
  obtain ⟨d', w, hw, Ψ, B, localForm, retained, hd', hpos, hws, hΨ, hB,
      hsub, hmass', hlocal⟩ :=
    hfixed outer productive d patch D q hd hmass hq hD hJ hLip
      localLaw point score hscore hpositive'
  exact ⟨localLaw, d', w, hw, Ψ, B, localForm, retained, hd',
    hd'.trans (Nat.min_le_left _ _), hpos, hws, hΨ, hB, hsub, hmass',
    fun h hh => hslice h (hsub hh), hlocal⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedReturnedPatchSource

variable {keep : LayerSamplerVariables G I n B → Prop} {centerLift : ∀ j, U j}
    {z : A.Path} (source : AllocatedReturnedPatchSource (E := E) (A := A) keep centerLift z)

end AllocatedReturnedPatchSource

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

theorem exists_allocatedNormalizedShearProblem_of_returned_fiber_laws
    {V : Type*} {s d : ℕ} (keep : LayerSamplerVariables G I n B → Prop)
    (centerLift : ∀ j, U j)
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    (productive : Finset A.Path) {massThreshold cost scoreThreshold : ℝ}
    (hmass : massThreshold ≤ A.law.mass productive)
    (hsupported : ∀ z : productive, 0 < A.law.weight z.val)
    (sample : productive → CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : productive → AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ z : productive,
      AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
        centerLift z.val.1.val z.val.2.val (sample z) (read z))
    (hshort : ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (patch : PolynomialPatch V s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    (localForm : productive → PolynomialSlots (LayerSamplerVariables G I n B) d patch.weight)
    (law : productive → FiniteProbabilityWeights A.Site)
    (hslice : ∀ z, RelativeReturnedFiberLaw keep A.sides cost (law z))
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    (hscore : ∀ z, scoreThreshold ≤ (law z).mean
      (fun u => (f (A.physical z.val u) - lam) *
        (patch.form.shearTransformedSlots patch.weight_mono
          ((localForm z).loweringAt (fun i => (u.val i : ℝ)))).patchValue patch.kernel)) :
    ∃ P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - lam : ℝ) : ℂ)) cost massThreshold scoreThreshold,
      P.productive = productive ∧ P.centerLift = centerLift ∧
        ∀ z, (P.chart z).keep = keep := by
  have hcert := hslice
  unfold RelativeReturnedFiberLaw at hcert
  choose fixed hfixed q hq slice hlen hlength hlaw using hcert
  let source : ∀ z : productive,
      AllocatedReturnedPatchSource (E := E) (A := A) keep centerLift z.val := fun z =>
    ⟨hsupported z, sample z, read z, hread z, fixed z, hfixed z⟩
  let keptForm := fun z => (localForm z).coordinateFiberForm keep (fixed z)
  have hkeptScore (z : productive) : scoreThreshold ≤
      ((slice z).fullSliceLaw (hlen z)).mean (fun u =>
        (f ((source z).physical u.val) - lam) *
          (patch.form.shearTransformedSlots patch.weight_mono
            ((keptForm z).loweringAt (fun i => (u.val i : ℝ)))).patchValue patch.kernel) := by
    have hs := hscore z
    rw [hlaw z] at hs
    dsimp only [AllocatedExternalCandidateSampler.physical] at hs
    rw [patch.fiberSliceLaw_shear_score_eq_fullSliceLaw (localForm z) keep
      (slice z) (hlen z) (fixed z) (hfixed z)
      (fun u => f (jointIntegerPhysicalSite u (z.val.1.val, z.val.2.val))) lam] at hs
    have hdec :
        (fun a b : {i // keep i} => Classical.propDecidable (a = b)) =
        (fun a b => @Subtype.instDecidableEq _ keep
          (inferInstance : DecidableEq (LayerSamplerVariables G I n B)) a b) :=
      Subsingleton.elim _ _
    rw [← hdec] at hs
    simpa only [keptForm, AllocatedReturnedPatchSource.physical, source] using hs
  let P := allocatedNormalizedShearProblem keep centerLift hcenter productive hmass
    source hshort patch keptForm q hq slice hlen hlength f lam hkeptScore
  exact ⟨P, rfl, rfl, fun _ => rfl⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin 0 → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

theorem exists_allocatedZeroLayerNormalizedShearProblem
    {V : Type*} {s d : ℕ} (keep : LayerSamplerVariables G I n B → Prop)
    (productive : Finset A.Path) {massThreshold cost scoreThreshold : ℝ}
    (hmass : massThreshold ≤ A.law.mass productive)
    (hshort : ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (patch : PolynomialPatch V s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    (localForm : A.Path → PolynomialSlots (LayerSamplerVariables G I n B) d patch.weight)
    (law : A.Path → FiniteProbabilityWeights A.Site)
    (hslice : ∀ z ∈ productive, RelativeReturnedFiberLaw keep A.sides cost (law z))
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    (hscore : ∀ z ∈ productive, scoreThreshold ≤ (law z).mean
      (fun u => (f (A.physical z u) - lam) *
        (patch.form.shearTransformedSlots patch.weight_mono
          ((localForm z).loweringAt (fun i => (u.val i : ℝ)))).patchValue patch.kernel)) :
    ∃ P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - lam : ℝ) : ℂ)) cost massThreshold scoreThreshold,
      P.productive ⊆ productive ∧ A.law.mass P.productive = A.law.mass productive ∧
        P.centerLift = allocatedZeroLayerCenterLift U ∧
        ∀ z, (P.chart z).keep = keep := by
  let supported := productive.filter (fun z => 0 < A.law.weight z)
  have hsub : supported ⊆ productive := Finset.filter_subset _ _
  have hsame : A.law.mass supported = A.law.mass productive := by
    unfold FiniteProbabilityWeights.mass
    dsimp only [supported]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : 0 < A.law.weight z
    · rw [if_pos hz]
    · rw [if_neg hz]
      exact (le_antisymm (le_of_not_gt hz) (A.law.nonneg z)).symm
  obtain ⟨P, hP, hcenter, hkeep⟩ :=
    exists_allocatedNormalizedShearProblem_of_returned_fiber_laws
      (E := E) (A := A) keep (allocatedZeroLayerCenterLift U)
      (allocatedZeroLayerCenterLift_spec B U center) supported
      (hmass.trans_eq hsame.symm)
      (fun z => (Finset.mem_filter.mp z.property).2)
      (fun _ => allocatedZeroLayerSample B)
      (fun z => allocatedZeroLayerFramedRead (E := E) B z.val.1.val z.val.2.val)
      (fun z => allocatedZeroLayer_recovered B U b hb o S hR hσ poly hm
        z.val.1.val z.val.2.val)
      hshort patch (fun z => localForm z.val) (fun z => law z.val)
      (fun z => hslice z.val (hsub z.property)) f lam
      (fun z => hscore z.val (hsub z.property))
  exact ⟨P, hP ▸ hsub, hP ▸ hsame, hcenter, hkeep⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedCommonSideSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem unconditionedResidueSiteBound_le_commonSide
    {K J : Type*} [Fintype K] [Fintype J]
    (P : J → ℕ) (e : K ≃ J) (S : ℕ) (hP : ∀ j, P j ≤ S) :
    unconditionedResidueSiteBound P ≤ (Fintype.card K : ℝ) * S := by
  calc
    unconditionedResidueSiteBound P ≤ ∑ _j : J, (S : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      exact_mod_cast hP j
    _ = (Fintype.card K : ℝ) * S := by
      simp [Fintype.card_congr e]

theorem integerBox_commonSide_sum_abs_le
    {K : Type*} [Fintype K] [DecidableEq K]
    (S : ℕ) (x : K → ℤ) (hx : x ∈ integerBox (fun _ : K => S)) :
    (∑ k, |(x k : ℝ)|) ≤ (Fintype.card K : ℝ) * S := by
  calc
    (∑ k, |(x k : ℝ)|) ≤ ∑ _k : K, (S : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      have hk := (mem_integerBox (fun _ : K => S) x).mp hx k
      rw [abs_of_nonneg (by exact_mod_cast hk.1 : (0 : ℝ) ≤ x k)]
      exact_mod_cast hk.2.le
    _ = (Fintype.card K : ℝ) * S := by simp

namespace BooleanCubeKernel

theorem unconditionedCommonSide_site_mem
    {K X : Type*} [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq X]
    (S : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) (N : X → ℕ)
    (hR : ∀ i, 2 * spatialTrimMargin τ N i < N i)
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0
        (trimmedSpatialWidths (K := K) ((Fintype.card K : ℝ) * S) τ N) 1)
    (x : K → ℤ) (hx : x ∈ integerBox (fun _ : K => S)) :
    jointIntegerPhysicalSite x (z.1.val, z.2.val) ∈ integerBox N := by
  apply jointIntegerPhysicalSite_mem_box x N (spatialTrimMargin τ N)
    (fun i => (hR i).le)
    (trimmedSpatialWidths (K := K) ((Fintype.card K : ℝ) * S) τ N) _ z
  intro i
  exact spatialTrimMargin_fits (by positivity) hτ x
    (integerBox_commonSide_sum_abs_le S x hx) N i

end BooleanCubeKernel
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalCandidateAllKeptSliceLaw
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I : Type*} {N : I → ℕ} {q : ℕ}

variable [Fintype I] [DecidableEq I]

theorem keepTrueSlice_fiberSliceLaw_mean (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 0 < S.length i) (fixed : {_i : I // ¬True} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ))
    (f : integerBox N → ℝ) :
    (S.fullSliceLaw hlen).mean f =
      (S.keepTrueSlice.fiberSliceLaw (fun i => hlen i.val) fixed hfixed).mean f := by
  refine (S.fullSliceLaw_mean hlen f).trans
    (Eq.trans ?_ (S.keepTrueSlice.fiberSliceLaw_mean
      (fun i => hlen i.val) fixed hfixed f).symm)
  apply Fintype.expect_equiv S.keepTrueParameterEquiv
  intro u
  rfl

theorem keepTrueSlice_fiberSliceLaw (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 0 < S.length i) (fixed : {_i : I // ¬True} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ)) :
    S.fullSliceLaw hlen =
      S.keepTrueSlice.fiberSliceLaw (fun i => hlen i.val) fixed hfixed := by
  have ext_weight {p p' : FiniteProbabilityWeights (integerBox N)}
      (h : p.weight = p'.weight) : p = p' := by
    cases p
    cases p'
    cases h
    rfl
  apply ext_weight
  funext x
  have hm := S.keepTrueSlice_fiberSliceLaw_mean hlen fixed hfixed
    (fun y => if y = x then 1 else 0)
  simpa [FiniteProbabilityWeights.mean] using hm

theorem fullSliceLaw_returnedFiberLaw (S : ResidueBoxSlice N q)
    (hq : 0 < q) (hlen : ∀ i, 0 < S.length i) {cost : ℝ}
    (hlength : ∀ i, Real.exp (-cost) * (N i : ℝ) ≤ (S.length i : ℝ)) :
    RelativeReturnedFiberLaw (fun _ : I => True) N cost (S.fullSliceLaw hlen) := by
  let fixed : {_i : I // ¬True} → ℤ := fun i => False.elim (i.property trivial)
  have hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ) :=
    fun i => False.elim (i.property trivial)
  exact ⟨fixed, hfixed, q, hq, S.keepTrueSlice, (fun i => hlen i.val),
    (fun i => hlength i.val), S.keepTrueSlice_fiberSliceLaw hlen fixed hfixed⟩

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]
    {keep : I → Prop} [dkeep : DecidablePred keep] {N : I → ℕ} {q : ℕ}

end Erdos3.ResidueBoxSlice

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace AllocatedExternalCandidateProblem.Conclusion

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedZeroLayerCommonSideInitializationUniform
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical NNReal

theorem exists_unconditioned_commonSide_fixed_patch_family (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ (n₀ : ℕ) {K X : Type*}
      [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq X]
      (P : Fin n₀ → ℕ) [∀ k, NeZero (P k)] (e : K ≃ Fin n₀)
    (S : ℕ), 0 < S → ∀ (_i : X) {p a Λ σ extra : ℝ},
      0 ≤ p → 0 ≤ a → Λ ∈ Set.Icc (0 : ℝ) 1 → 0 < σ → σ ≤ 1 →
      0 ≤ extra → (∀ j, P j ≤ S) →
      (∀ j, (S : ℝ) ≤ Real.exp extra * (P j : ℝ)) →
      ∀ (d₀ : ℕ), RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
      (∀ j, (P j).Prime) → Function.Injective P →
      (∀ j k, P j ≤ 2 ^ (n₀ + 1) * P k) →
      (∀ j, Real.exp p ≤ (P j : ℝ)) →
      ∀ (N : X → ℕ),
        (∀ j, unconditionedSpatialWidthCutoff ((Fintype.card K : ℝ) * S)
          (unconditionedSpatialTrimFraction (Fintype.card X) σ)
          (unconditionedCollisionWidth P σ) ≤ (N j : ℝ)) →
      ∀ (f : (X → ℤ) → ℝ), (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
        IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
        a + σ ≤ (𝔼 x ∈ integerBox N, f x) →
      let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
      let W := trimmedSpatialWidths (K := K) ((Fintype.card K : ℝ) * S) τ N
      let R := spatialTrimMargin τ N
      let q := p + extra + (Fintype.card K : ℝ) + 2
      let D := min d₀ ⌊p + extra⌋₊
      ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
        (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
      let law := selectedJointReference (trimmedIntegerBox N R)
        (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
      ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
        σ / 4 ≤ law.mass productive ∧
        (∀ z ∈ productive, Function.Injective (fun u : ∀ j, ZMod (P j) =>
          jointIntegerPhysicalSite (fun k => residueBoxIntegerPoint P u (e k))
            (z.1.val,z.2.val))) ∧
        (∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1,
          ∀ x ∈ integerBox (fun _ : K => S),
          jointIntegerPhysicalSite x (z.1.val,z.2.val) ∈ integerBox N) ∧
      ∃ (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots K d w)
        (localForm : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
          PolynomialSlots K d w)
        (localLaw : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
          FiniteProbabilityWeights (integerBox (fun _ : K => S)))
        (retained : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1)),
        d ≤ d₀ ∧ d ≤ D ∧ (∀ j, 1 ≤ w j) ∧ (∀ j, w j ≤ s) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((q + 2) ^ E) ∧
        (∀ j, realPolynomialMass (B.center j) ≤ (q + 2) ^ E) ∧
        retained ⊆ productive ∧
        (law.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        ((σ / 4) / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        (∀ z ∈ retained, ∃ r, 0 < r ∧
          ∃ (slice : ResidueBoxSlice (fun _ : K => S) r)
            (hlen : ∀ j, 0 < slice.length j),
            (∀ j, Real.exp (-(p + extra)) * (S : ℝ) ≤ (slice.length j : ℝ)) ∧
            localLaw z = slice.fullSliceLaw hlen) ∧
        ∀ z ∈ retained, Real.exp (-((q + 2) ^ E)) ≤ (localLaw z).mean
          (fun x => (f (jointIntegerPhysicalSite x.val (z.1.val,z.2.val)) - Λ) *
            (B.shearTransformedSlots hw
              ((localForm z).loweringAt (fun j => (x.val j : ℝ)))).patchValue Ψ) := by
  obtain ⟨E, hE, hfixed⟩ := exists_relative_finite_returned_slice_normalization s
  refine ⟨E, hE, ?_⟩
  intro n₀ K X _ _ _ _ P _ e S hS i p a Λ σ extra hp ha hΛ hσ hσ1 hextra
    hPS hratio d₀ habsolute hprime hdistinct hcomparable hcutoff N hN f hf hfree hmean
  let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
  let W := trimmedSpatialWidths (K := K) ((Fintype.card K : ℝ) * S) τ N
  let R := spatialTrimMargin τ N
  let q := p + extra + (Fintype.card K : ℝ) + 2
  let D := min d₀ ⌊p + extra⌋₊
  have hBP : unconditionedResidueSiteBound P ≤ (Fintype.card K : ℝ) * S := by
    exact unconditionedResidueSiteBound_le_commonSide P e S hPS
  obtain ⟨hW, hR, hZ, productive, hmass, hinj, hreturn, _⟩ :=
    exists_unconditioned_rootBudget_absolute_family_equiv s n₀ P e
      ((Fintype.card K : ℝ) * S) hBP i ha hσ hσ1 d₀ habsolute
      hprime hdistinct hcomparable hcutoff N hN f hf hfree hmean
  let law := selectedJointReference (trimmedIntegerBox N R)
    (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
  have hprod : 0 < law.mass productive := (div_pos hσ (by norm_num)).trans_le hmass
  have hnonempty : productive.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hprod
  obtain ⟨z₀, _⟩ := hnonempty
  let : Nonempty (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) := ⟨z₀⟩
  have hτ : 0 ≤ τ :=
    (unconditionedSpatialTrimFraction_bounds (Fintype.card X) hσ hσ1).1.le
  have hinside (z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1)
      (x : K → ℤ) (hx : x ∈ integerBox (fun _ : K => S)) :
      jointIntegerPhysicalSite x (z.1.val,z.2.val) ∈ integerBox N := by
    exact unconditionedCommonSide_site_mem S hτ N hR z x hx
  have hbound (z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1)
      (x : K → ℤ) (hx : x ∈ integerBox (fun _ : K => S)) :
      f (jointIntegerPhysicalSite x (z.1.val,z.2.val)) ∈ Set.Icc (0 : ℝ) 1 :=
    hf _ (hinside z x hx)
  have hreturned (z) (hz : z ∈ productive) :
      RelativePatchSliceConclusion s (fun _ : K => S)
        (fun x => f (jointIntegerPhysicalSite x (z.1.val,z.2.val))) Λ d₀ (p + extra) := by
    have hprimeReturn : RelativePatchSliceConclusion s
        (coordinateReindexedSides e (fun k => P (e k)))
        (coordinateReindexedFunction e
          (fun x => f (jointIntegerPhysicalSite x (z.1.val,z.2.val)))) Λ d₀ p := by
      have he : coordinateReindexedSides e (fun k => P (e k)) = P := by
        funext j
        exact congrArg P (e.apply_symm_apply j)
      rw [he]
      exact hreturn z hz
    apply (hprimeReturn.coordinateReturn e).enlargeBox (fun k => hPS (e k))
      (fun k => ?_) hextra
    calc
      Real.exp (-extra) * (S : ℝ) ≤
          Real.exp (-extra) * (Real.exp extra * (P (e k) : ℝ)) :=
        mul_le_mul_of_nonneg_left (hratio (e k)) (Real.exp_nonneg _)
      _ = (P (e k) : ℝ) := by rw [← mul_assoc, ← Real.exp_add]; simp
  obtain ⟨localLaw, d, w, hw, Ψ, B, localForm, retained, hd, hd₀, hpos, hws, hΨ, hB,
      hsub, hretained, hcertificate, hlocal⟩ :=
    hfixed law productive hprod (fun _ : K => S) (fun _ => hS) (p + extra)
      (add_nonneg hp hextra) Λ hΛ d₀
      (fun z x => f (jointIntegerPhysicalSite x (z.1.val,z.2.val))) hbound hreturned
  refine ⟨hW, hR, hZ, productive, hmass, hinj, hinside, d, w, hw, Ψ, B,
    localForm, localLaw, retained, hd₀, hd, hpos, hws, hΨ, hB, hsub,
    hretained, ?_, hcertificate, hlocal⟩
  have hle := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hmass
      (by positivity : (0 : ℝ) ≤ ((D + 1) * (s + 1) ^ D : ℕ)))
    (Real.exp_nonneg (-((q + 2) ^ E)))
  exact hle.trans hretained

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ}
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

theorem exists_allocatedZeroLayer_commonSide_initialization_uniform (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ}
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))],
    ∀ (S : LayerSamplerScale (G := G) B U b R σ)
      (n₀ : ℕ) (_eG : G ≃ Fin n₀)
      (P : Fin n₀ → ℕ) [∀ j, NeZero (P j)] (_i : X)
      {p a Λ surplus extra : ℝ},
      0 ≤ p → 0 ≤ a → Λ ∈ Set.Icc (0 : ℝ) 1 →
      0 < surplus → surplus ≤ 1 → 0 ≤ extra →
      (∀ j, P j ≤ S.value) →
      (∀ j, (S.value : ℝ) ≤ Real.exp extra * (P j : ℝ)) →
      ∀ (d₀ : ℕ), RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
      (∀ j, (P j).Prime) → Function.Injective P →
      (∀ j k, P j ≤ 2 ^ (n₀ + 1) * P k) →
      (∀ j, Real.exp p ≤ (P j : ℝ)) →
      ∀ (N : X → ℕ),
      (∀ x, unconditionedSpatialWidthCutoff
        ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value)
        (unconditionedSpatialTrimFraction (Fintype.card X) surplus)
        (unconditionedCollisionWidth P surplus) ≤ (N x : ℝ)) →
      ∀ (f : (X → ℤ) → ℝ),
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
      a + surplus ≤ (𝔼 x ∈ integerBox N, f x) →
      let τ := unconditionedSpatialTrimFraction (Fintype.card X) surplus
      let q := p + extra + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2
      let D := min d₀ ⌊p + extra⌋₊
      let mass := ((surplus / 4) / ((D + 1) * (s + 1) ^ D : ℕ)) *
        Real.exp (-((q + 2) ^ C))
      ∃ (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
          N poly hm τ 1 (fun _ => 1) {0} 0)
        (d : ℕ) (patch : PolynomialPatch (LayerSamplerVariables G I n B) s d),
        d ≤ d₀ ∧ d ≤ D ∧
        (patch.kernel.lip : ℝ) ≤ Real.exp ((q + 2) ^ C) ∧
        (∀ j, realPolynomialMass (patch.form.center j) ≤ (q + 2) ^ C) ∧
        letI := polynomialShearIndexFintype patch.weight patch.weight_pos
        ∃ Q : AllocatedExternalCandidateProblem (E := E) A
          (polynomialShearNilmanifold patch.weight s patch.weight_le)
          (RationalTorus.trivialFiltration s) 0 1
          (fun _ y => (patch.shearObservable y : ℂ))
          (fun x => ((f x - Λ : ℝ) : ℂ))
          (p + extra) mass (Real.exp (-((q + 2) ^ C))),
          Q.centerLift = allocatedZeroLayerCenterLift U ∧
          ∀ z, (Q.chart z).keep = fun _ => True := by
  obtain ⟨C, hC, hsource⟩ := exists_unconditioned_commonSide_fixed_patch_family s
  refine ⟨C, hC, ?_⟩
  intro G X _ _ I E J _ _ n B _ U b R σ hb o hR hσ poly hm _
    S n₀ eG P _ i p a Λ surplus extra hp ha hΛ hsurplus hsurplus1 hextra
    hPS hratio d₀ habsolute hprime hdistinct hcomparable hcutoff N hN f hf hfree hmean
    τ q D mass
  let e := (zeroLayerVariablesEquiv B).trans eG
  have hfamily := hsource n₀ P e S.value S.positive i hp ha hΛ hsurplus hsurplus1
    hextra hPS hratio d₀ habsolute hprime hdistinct hcomparable hcutoff N hN f hf hfree hmean
  obtain ⟨hW, hproper, hZ, productive, _hmass, _hinjective, _hinside,
    d, w, hw, Ψ, form, localForm, localLaw, retained, hd₀, hdD, hpos, hws,
    hΨ, hform, _hsub, _hmassRelative, hretained, hslice, hscore⟩ := hfamily
  let patch : PolynomialPatch (LayerSamplerVariables G I n B) s d := ⟨w, hpos, hws, hw, form, Ψ⟩
  have hslice0 : ∀ z ∈ retained, RelativeReturnedFiberLaw (fun _ : (LayerSamplerVariables G I n B) => True)
      (fun _ : (LayerSamplerVariables G I n B) => S.value) (p + extra) (localLaw z) := by
    intro z hz
    obtain ⟨r, hr, slice, hlen, hdense, hlawSlice⟩ := hslice z hz
    rw [hlawSlice]
    exact slice.fullSliceLaw_returnedFiberLaw hr hlen hdense
  let data : UniformScalarCommonBoxSource s d₀ D N τ (fun _ : (LayerSamplerVariables G I n B) => S.value)
      (trimmedSpatialWidths (K := (LayerSamplerVariables G I n B)) ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value) τ N)
      f Λ (p + extra) ((q + 2) ^ C) mass :=
    ⟨hW, hproper, hZ, d, patch, hd₀, hdD, hΨ, hform, localForm, localLaw,
      retained, hretained, hslice0, hscore⟩
  have hwidth : allocatedExternalCandidateWidths B U b S N τ 1 =
      trimmedSpatialWidths (K := (LayerSamplerVariables G I n B)) ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value) τ N := by
    rw [allocatedExternalCandidateWidths_zero_layers, zeroLayerVariables_card]
  have actualData : UniformScalarCommonBoxSource s d₀ D N τ
      (allocatedExternalCandidateSides B U b S)
      (allocatedExternalCandidateWidths B U b S N τ 1)
      f Λ (p + extra) ((q + 2) ^ C) mass := by
    rw [allocatedExternalCandidateSides_zero_layers_fun, hwidth]
    exact data
  have hNpos (x : X) : 0 < N x := by have hx := actualData.proper x; omega
  have hτ : 0 < τ :=
    (unconditionedSpatialTrimFraction_bounds (Fintype.card X) hsurplus hsurplus1).1
  let A := allocatedExternalCandidateSampler_zero_layers B U b S hb o hR hσ poly hm
    0 N τ 1 (fun _ => 1) {0} hNpos hτ (by norm_num) (fun _ => by norm_num)
    (trimmedIntegerBox_nonempty N _ actualData.proper) actualData.smooth_pos
  let := polynomialShearIndexFintype actualData.patch.weight actualData.patch.weight_pos
  have hlaw : A.law = selectedJointReference
      (trimmedIntegerBox N (spatialTrimMargin τ N))
      (trimmedIntegerBox_nonempty N _ actualData.proper) (fun _ : X => 1) {0}
      (allocatedExternalCandidateWidths B U b S N τ 1)
      actualData.width_pos actualData.smooth_pos :=
    A.law_zero_layers
  have hmassA : mass ≤ A.law.mass actualData.retained := by
    rw [hlaw]
    exact actualData.mass_le
  have hsliceA := actualData.slice
  have hdec : (fun _ : (LayerSamplerVariables G I n B) => instDecidableTrue) =
      (fun _ : (LayerSamplerVariables G I n B) => Classical.propDecidable True) := Subsingleton.elim _ _
  rw [hdec] at hsliceA
  obtain ⟨Q, _, _, hcenter, hkeep⟩ :=
    exists_allocatedZeroLayerNormalizedShearProblem (E := E) A (fun _ => True) actualData.retained
      hmassA (fun j => (j.property trivial).elim) actualData.patch actualData.localForm
      actualData.localLaw hsliceA f Λ actualData.score
  exact ⟨A, actualData.rank, actualData.patch, actualData.rank_le,
    actualData.rank_le_early, actualData.lip_le, actualData.center_le, Q, hcenter, hkeep⟩

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedZeroLayerInitializationMassLoss
namespace OAI

section

namespace Erdos3

theorem allocatedZeroLayerInitialization_denominator_bound (s D : ℕ) {r : ℝ}
    (hD : (D : ℝ) ≤ r) :
    4 * (((D + 1) * (s + 1) ^ D : ℕ) : ℝ) ≤
      Real.exp (r + 5 + r * (s + 1)) := by
  have hs : (s + 1 : ℝ) ≤ Real.exp (s + 1) :=
    (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num)).trans
      (Real.add_one_le_exp (s + 1))
  have hpow : ((s + 1 : ℕ) : ℝ) ^ D ≤ Real.exp (r * (s + 1)) := by
    calc
      _ ≤ (Real.exp (s + 1)) ^ D :=
        pow_le_pow_left₀ (by positivity)
          (by simpa only [Nat.cast_add, Nat.cast_one] using hs) D
      _ = Real.exp ((D : ℝ) * (s + 1)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hD (by positivity))
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by
    linarith [Real.add_one_le_exp (4 : ℝ)]
  have hdim : (D + 1 : ℝ) ≤ Real.exp (r + 1) := by
    linarith [Real.add_one_le_exp (r + 1)]
  calc
    _ = (4 * (D + 1 : ℝ)) * ((s + 1 : ℕ) : ℝ) ^ D := by push_cast; ring
    _ ≤ (Real.exp 4 * Real.exp (r + 1)) * Real.exp (r * (s + 1)) :=
      mul_le_mul (mul_le_mul hfour hdim (by positivity) (Real.exp_nonneg _))
        hpow (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem allocatedZeroLayerInitialization_mass_loss (s D : ℕ) (p r L : ℝ)
    (hD : (D : ℝ) ≤ r) :
    Real.exp (-(L + p + r + 5 + r * (s + 1))) ≤
      ((Real.exp (-p) / 4) / (((D + 1) * (s + 1) ^ D : ℕ) : ℝ)) *
        Real.exp (-L) := by
  let denominator : ℝ := (((D + 1) * (s + 1) ^ D : ℕ) : ℝ)
  have hd0 : 0 < denominator := by dsimp only [denominator]; positivity
  have hden : 4 * denominator ≤ Real.exp (r + 5 + r * (s + 1)) :=
    allocatedZeroLayerInitialization_denominator_bound s D hD
  change Real.exp (-(L + p + r + 5 + r * (s + 1))) ≤
    (Real.exp (-p) / 4 / denominator) * Real.exp (-L)
  rw [div_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 4 * denominator)]
  calc
    _ ≤ Real.exp (-(L + p + r + 5 + r * (s + 1))) *
        Real.exp (r + 5 + r * (s + 1)) :=
      mul_le_mul_of_nonneg_left hden (Real.exp_nonneg _)
    _ = Real.exp (-p) * Real.exp (-L) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CanonicalZeroLayerBudgetedInitialization
namespace OAI

section

namespace Erdos3

theorem exists_allocatedZeroLayerInitialization_power_budget
    (s n₀ Cinit : ℕ) (extra : ℝ) (hextra : 0 ≤ extra) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (p : ℝ), 2 ≤ p →
      let q := p + extra + (n₀ : ℝ) + 2
      let b := (p + 2) ^ C
      p + extra ≤ b ∧ (q + 2) ^ Cinit ≤ b ∧
      Real.exp (-b) ≤ Real.exp (-((q + 2) ^ Cinit)) ∧
      ∀ D : ℕ, D ≤ ⌊p + extra⌋₊ →
        (D : ℝ) ≤ b ∧
        Real.exp (-b) ≤
          ((Real.exp (-p) / 4) / (((D + 1) * (s + 1) ^ D : ℕ) : ℝ)) *
            Real.exp (-((q + 2) ^ Cinit)) := by
  let E : ℕ := ⌈extra⌉₊
  let rankPoly : Polynomial ℕ := Polynomial.X + Polynomial.C E
  let depth : Polynomial ℕ := (Polynomial.X + Polynomial.C (E + n₀ + 4)) ^ Cinit
  let massLog : Polynomial ℕ :=
    depth + Polynomial.X + rankPoly + 5 + rankPoly * Polynomial.C (s + 1)
  obtain ⟨C, hC, hbudget⟩ :=
    exists_natPolynomial_fixed_power_budget (rankPoly + depth + massLog)
  refine ⟨C, hC, ?_⟩
  intro p hp q b
  let r : ℝ := p + E
  let L : ℝ := (p + E + n₀ + 4) ^ Cinit
  let T : ℝ := L + p + r + 5 + r * (s + 1)
  have hp0 : 0 ≤ p := by linarith
  have hE : extra ≤ (E : ℝ) := Nat.le_ceil extra
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  have hT0 : 0 ≤ T := by dsimp only [T]; positivity
  have hbudget' : r + L + T ≤ b := by
    simpa [rankPoly, depth, massLog, Polynomial.eval₂_pow, r, L, T, b,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc] using hbudget p hp0
  have hrb : r ≤ b := by linarith
  have hLb : L ≤ b := by linarith
  have hTb : T ≤ b := by linarith
  have hcost : p + extra ≤ r := by dsimp only [r]; linarith
  have hnorm : (q + 2) ^ Cinit ≤ L := by
    apply pow_le_pow_left₀
      (by dsimp only [q]; positivity)
      (by dsimp only [q]; linarith)
  have hnormalization : (q + 2) ^ Cinit ≤ b := hnorm.trans hLb
  refine ⟨hcost.trans hrb, hnormalization,
    Real.exp_le_exp.mpr (neg_le_neg hnormalization), ?_⟩
  intro D hD
  have hDr : (D : ℝ) ≤ p + extra :=
    (Nat.cast_le.mpr hD).trans (Nat.floor_le (add_nonneg hp0 hextra))
  refine ⟨hDr.trans (hcost.trans hrb), ?_⟩
  have hmassLog : (q + 2) ^ Cinit + p + (p + extra) + 5 +
      (p + extra) * (s + 1) ≤ T := by
    have hmul := mul_le_mul_of_nonneg_right hcost (show (0 : ℝ) ≤ s + 1 by positivity)
    dsimp only [T]
    linarith
  exact (Real.exp_le_exp.mpr (neg_le_neg (hmassLog.trans hTb))).trans
    (allocatedZeroLayerInitialization_mass_loss s D p (p + extra)
      ((q + 2) ^ Cinit) hDr)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem unconditionedCommonSideExtra_nonneg (n : ℕ) :
    0 ≤ unconditionedCommonSideExtra n := by
  apply Real.log_nonneg
  exact_mod_cast (by omega : 1 ≤ 1 + n * 2 ^ (n + 1))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

theorem exists_allocatedZeroLayer_budgeted_initialization_oai (s n₀ : ℕ) :
    ∃ Cshape Cinput : ℕ, 2 ≤ Cshape ∧ Cshape ≤ Cinput ∧
    ∀ {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ}
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))],
    ∀ (S : LayerSamplerScale (G := G) B U b R σ)
      (_eG : G ≃ Fin n₀)
      (P : Fin n₀ → ℕ) [∀ j, NeZero (P j)] (_i : X)
      {p a Λ : ℝ},
      2 ≤ p → 0 ≤ a → Λ ∈ Set.Icc (0 : ℝ) 1 →
      (∀ j, P j ≤ S.value) →
      (∀ j, (S.value : ℝ) ≤ Real.exp (unconditionedCommonSideExtra n₀) * (P j : ℝ)) →
      ∀ (d₀ : ℕ), RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
      (∀ j, (P j).Prime) → Function.Injective P →
      (∀ j k, P j ≤ 2 ^ (n₀ + 1) * P k) →
      (∀ j, Real.exp p ≤ (P j : ℝ)) →
      ∀ (N : X → ℕ),
      (∀ x, unconditionedSpatialWidthCutoff
        ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value)
        (unconditionedSpatialTrimFraction (Fintype.card X) (Real.exp (-p)))
        (unconditionedCollisionWidth P (Real.exp (-p))) ≤ (N x : ℝ)) →
      ∀ (f : (X → ℤ) → ℝ),
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
      a + (Real.exp (-p)) ≤ (𝔼 x ∈ integerBox N, f x) →
      let τ := unconditionedSpatialTrimFraction (Fintype.card X) (Real.exp (-p))
      let shape := (p + 2) ^ Cshape
      let input := (p + 2) ^ Cinput
      ∃ (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
          N poly hm τ 1 (fun _ => 1) {0} 0)
        (d : ℕ) (patch : PolynomialPatch (LayerSamplerVariables G I n B) s d),
        d ≤ d₀ ∧ (d : ℝ) ≤ shape ∧
        (patch.kernel.lip : ℝ) ≤ Real.exp shape ∧
        (∀ j, realPolynomialMass (patch.form.center j) ≤ shape) ∧
        letI := polynomialShearIndexFintype patch.weight patch.weight_pos
        ∀ [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
          [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
          [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
          [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)],
        ∃ M : ℝ≥0, patch.ExternalObservableRegularity M input ∧
        ∃ Q : AllocatedExternalCandidateProblem (E := E) A
          (polynomialShearNilmanifold patch.weight s patch.weight_le)
          (RationalTorus.trivialFiltration s) 0 1
          (fun _ y => (patch.shearObservable y : ℂ))
          (fun x => ((f x - Λ : ℝ) : ℂ))
          input (Real.exp (-input)) (Real.exp (-input)),
          Q.centerLift = allocatedZeroLayerCenterLift U ∧
          ∀ z, (Q.chart z).keep = fun _ => True := by
  obtain ⟨Cinit, _, hinit⟩ := exists_allocatedZeroLayer_commonSide_initialization_uniform s
  obtain ⟨Cshape, hCshape, hbudget⟩ := exists_allocatedZeroLayerInitialization_power_budget
    s n₀ Cinit (unconditionedCommonSideExtra n₀) (unconditionedCommonSideExtra_nonneg n₀)
  obtain ⟨Cobs, hCobs, hobs⟩ := exists_polynomialPatch_external_observable_budget s
  let Cinput := (Cshape + 1) * Cobs
  have hshapeInput : Cshape ≤ Cinput := by
    dsimp only [Cinput]
    exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (by omega))
  refine ⟨Cshape, Cinput, hCshape, hshapeInput, ?_⟩
  intro G X _ _ I E J _ _ n B _ U b R σ hb o hR hσ poly hm _ S eG P _ i
    p a Λ hp ha hΛ hPS hratio d₀ habsolute hprime hdistinct hcomparable hcutoff
    N hN f hf hfree hmean τ shape input
  have hp0 : 0 ≤ p := by linarith
  have hsurplus1 : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hvars : Fintype.card (LayerSamplerVariables G I n B) = n₀ := by
    rw [zeroLayerVariables_card]
    exact (Fintype.card_congr eG).trans (Fintype.card_fin n₀)
  have hsource := hinit (E := E) B U b hb o hR hσ poly hm S n₀ eG P i hp0 ha hΛ
    (Real.exp_pos _) hsurplus1 (unconditionedCommonSideExtra_nonneg n₀)
    hPS hratio d₀ habsolute hprime hdistinct hcomparable hcutoff N hN f hf hfree hmean
  dsimp only at hsource
  rw [hvars] at hsource
  obtain ⟨A, d, patch, hd, hdD, hLip, hcenter, hproblem⟩ := hsource
  let : Fintype (PolynomialShearIndex patch.weight) := polynomialShearIndexFintype patch.weight patch.weight_pos
  obtain ⟨Pinit, hcenterLift, hkeep⟩ := hproblem
  have hb := hbudget p hp
  dsimp only at hb
  have hdFloor : d ≤ ⌊p + unconditionedCommonSideExtra n₀⌋₊ := hdD.trans (Nat.min_le_right _ _)
  have hrank : (d : ℝ) ≤ shape := (hb.2.2.2 d hdFloor).1
  have hshape0 : 0 ≤ shape := pow_nonneg (by linarith) _
  have hshape1 : 1 ≤ shape := one_le_pow₀ (by linarith : 1 ≤ p + 2)
  have hshapeLe : shape ≤ input := pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) hshapeInput
  have hshift : shape + 2 ≤ (p + 2) ^ (Cshape + 1) := by
    rw [pow_succ']
    change shape + 2 ≤ (p + 2) * shape
    nlinarith
  have hobsLe : (shape + 2) ^ Cobs ≤ input := by
    calc
      _ ≤ ((p + 2) ^ (Cshape + 1)) ^ Cobs := pow_le_pow_left₀ (by positivity) hshift _
      _ = input := by dsimp only [input, Cinput]; rw [pow_mul]
  have hLipShape : (patch.kernel.lip : ℝ) ≤ Real.exp shape :=
    hLip.trans (Real.exp_le_exp.mpr hb.2.1)
  have hcenterShape : ∀ j, realPolynomialMass (patch.form.center j) ≤ shape :=
    fun j => (hcenter j).trans hb.2.1
  refine ⟨A, d, patch, hd, hrank, hLipShape, hcenterShape, ?_⟩
  intro _ _ _ _
  have hregularity := PolynomialPatch.ExternalObservableRegularity.mono patch
    (hobs patch shape hshape0 hrank hcenterShape hLipShape) hobsLe
  let D := min d₀ ⌊p + unconditionedCommonSideExtra n₀⌋₊
  have hmass := (hb.2.2.2 D (Nat.min_le_right _ _)).2
  have he : Real.exp (-input) ≤ Real.exp (-shape) := Real.exp_le_exp.mpr (neg_le_neg hshapeLe)
  let ref := Pinit.budgetRefinement (hb.1.trans hshapeLe) (he.trans hmass) (he.trans hb.2.2.1)
  refine ⟨⟨shape, hshape0⟩, hregularity, ref.problem, ?_, ?_⟩
  · exact hcenterLift
  · exact hkeep

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

namespace CanonicalEmptyLayerGeometry

end CanonicalEmptyLayerGeometry


end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_budgeted_initialization_oai := @OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_budgeted_initialization_oai
