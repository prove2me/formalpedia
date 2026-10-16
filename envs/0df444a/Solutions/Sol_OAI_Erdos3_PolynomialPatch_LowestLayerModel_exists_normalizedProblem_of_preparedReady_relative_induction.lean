-- Prove2me | solution 1 for OAI.Erdos3.PolynomialPatch.LowestLayerModel.exists_normalizedProblem_of_preparedReady_relative_induction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T01:57:25.067845+00:00
-- url     : https://prove2.me/submissions/ab2f3ace-dbcc-4952-aeac-52d61e45eaa1

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1331
import Definitions.Def_OAIErdos3B1348
import Definitions.Def_OAIErdos3B1351
import Theorems.Thm_OAI_Erdos3_PolynomialPatch_LowestLayerModel_exists_relative_child_of_allocated_padded_recovery

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

theorem recursive_discount_target_mem_Icc {discount Λ : ℝ}
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1) (hΛ : Λ ∈ Set.Icc (0 : ℝ) 1)
    (stage : ℕ) : (1 - discount) ^ (stage + 1) * Λ ∈ Set.Icc (0 : ℝ) 1 := by
  have hbase : 0 ≤ 1 - discount := sub_nonneg.mpr hdiscount.2
  have hbase1 : 1 - discount ≤ 1 := by linarith only [hdiscount.1]
  have hpow : (1 - discount) ^ (stage + 1) ≤ 1 := pow_le_one₀ hbase hbase1
  exact ⟨mul_nonneg (pow_nonneg hbase _) hΛ.1,
    (mul_le_mul hpow hΛ.2 hΛ.1 zero_le_one).trans_eq (one_mul 1)⟩

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeFinalPower
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure C) (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))

include hweight

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem RelativeReturnedFiberLaw.mono {X : Type*} [Fintype X] [DecidableEq X]
    {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {cost cost' : ℝ}
    {law : FiniteProbabilityWeights (integerBox N)}
    (h : RelativeReturnedFiberLaw keep N cost law) (hcost : cost ≤ cost') :
    RelativeReturnedFiberLaw keep N cost' law := by
  obtain ⟨fixed, hfixed, q, hq, S, hlen, hlength, hlaw⟩ := h
  refine ⟨fixed, hfixed, q, hq, S, hlen, ?_, hlaw⟩
  intro i
  exact (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg hcost)) (Nat.cast_nonneg _)).trans (hlength i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
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
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (A : AllocatedExternalCandidateSamplerFamily B U b S hb o hR hσ N poly hm τ ξ stride cells)

namespace AllocatedExternalCandidateSamplerFamily

variable [MeasurableSpace A.Path] [MeasurableSingletonClass A.Path]

end AllocatedExternalCandidateSamplerFamily

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedProductivePathPullback
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {nX : ℕ} {N : Fin nX → ℕ}
    {widths : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ}
    {bases : Finset (Fin nX → ℤ)} {test : (Fin nX → ℝ) → ℝ} {gain : ℝ}
    {z : bases × rectangularWeightIndices 0 widths 1}

namespace AllocatedPathProductivity

variable (hproductive : AllocatedPathProductivity B U b S N widths bases test gain z)

include hproductive

theorem physical_injOn :
    Set.InjOn (fun q => jointIntegerPhysicalSite q (z.1.val, z.2.val))
      (↑(integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)))) := by
  intro u hu v hv huv
  exact congrArg Subtype.val (hproductive.1 (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩) huv)

theorem pullback_mem_Icc {f : (Fin nX → ℤ) → ℝ}
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ q ∈ integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)),
      f (jointIntegerPhysicalSite q (z.1.val, z.2.val)) ∈ Set.Icc (0 : ℝ) 1 := by
  intro q hq
  exact hf _ (hproductive.2.2 ⟨q, hq⟩)

theorem pullback_apFree {f : (Fin nX → ℤ) → ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k) :
    IntegerVectorAPFree
      {q | q ∈ integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)) ∧
        f (jointIntegerPhysicalSite q (z.1.val, z.2.val)) ≠ 0} k := by
  apply (joint_sample_progression_free hfree hk (z.1.val, z.2.val)
    (↑(integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S))))
    hproductive.physical_injOn).mono
  intro q hq
  exact ⟨hq.1, hproductive.2.2 ⟨q, hq.1⟩, hq.2⟩

end AllocatedPathProductivity
end Erdos3.VectorPolynomial

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

theorem exists_allocatedFixedCenterNormalizedShearProblem
    (s : ℕ) (keep : LayerSamplerVariables G I n B → Prop)
    (centerLift : ∀ j, U j)
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    (productive : Finset A.Path) (hmass : 0 < A.law.mass productive)
    (hsupported : ∀ z : productive, 0 < A.law.weight z.val)
    (sample : productive → CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : productive → AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ z : productive,
      AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
        centerLift z.val.1.val z.val.2.val (sample z) (read z))
    (p cost : ℝ) (hp : 0 ≤ p) (hpcost : p ≤ cost)
    (hshort : ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (rankBound : ℕ) (f : (X → ℤ) → ℝ) (target : ℝ)
    (htarget : target ∈ Set.Icc (0 : ℝ) 1)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) (hξ1 : ξ ≤ 1)
    (hreturned : ∀ z ∈ productive, ∃ (fixed : {i // ¬keep i} → ℤ),
      (∀ i, 0 ≤ fixed i ∧ fixed i < (A.sides i.val : ℤ)) ∧
      RelativePatchSliceConclusion s (fun i : {i // keep i} => A.sides i.val)
        (fun u => f (jointIntegerPhysicalSite (finiteSplitPoint keep u fixed)
          (z.1.val, z.2.val))) target rankBound p) :
    let normalizationPower := (exists_relative_finite_returned_fiber_normalization.{0,0} s).choose
    let q := p + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2
    let D := min rankBound ⌊p⌋₊
    let normalizedBudget := (q + 2) ^ normalizationPower
    let retainedMass := (A.law.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
      Real.exp (-normalizedBudget)
    ∃ (d : ℕ) (patch : PolynomialPatch (LayerSamplerVariables G I n B) s d),
      d ≤ D ∧ d ≤ rankBound ∧
      (patch.kernel.lip : ℝ) ≤ Real.exp normalizedBudget ∧
      (∀ i, realPolynomialMass (patch.form.center i) ≤ normalizedBudget) ∧
      let := polynomialShearIndexFintype patch.weight (fun i => patch.weight_pos i)
      ∃ P : AllocatedExternalCandidateProblem (E := E) A
        (polynomialShearNilmanifold patch.weight s patch.weight_le)
        (RationalTorus.trivialFiltration s) 0 1
        (fun _ y => (patch.shearObservable y : ℂ))
        (fun x => ((f x - target : ℝ) : ℂ)) cost retainedMass (Real.exp (-normalizedBudget)),
        P.productive ⊆ productive ∧ P.centerLift = centerLift ∧
          ∀ z, (P.chart z).keep = keep := by
  intro normalizationPower q D normalizedBudget retainedMass
  have hne : productive.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hmass
    linarith)
  let : Nonempty A.Path := hne.to_subtype.map Subtype.val
  let pathInput := fun (z : A.Path) (u : LayerSamplerVariables G I n B → ℤ) =>
    f (jointIntegerPhysicalSite u (z.1.val, z.2.val))
  have hinput : ∀ z u, u ∈ integerBox A.sides → pathInput z u ∈ Set.Icc (0 : ℝ) 1 := by
    intro z u hu
    exact hf _ (A.physical_mem_integerBox hξ1 z ⟨u, hu⟩)
  obtain ⟨localLaw, d, w, hw, Ψ, slots, localForm, retained,
      hd, hdrank, hwpos, hwle, hLip, hslots, hsub, hretained, hslice, hscore⟩ :=
    (exists_relative_finite_returned_fiber_normalization.{0,0} s).choose_spec.2
      A.law productive hmass A.sides keep A.sides_pos p hp target htarget rankBound
      pathInput hinput hreturned
  let patch : PolynomialPatch (LayerSamplerVariables G I n B) s d :=
    ⟨w, hwpos, hwle, hw, slots, Ψ⟩
  let := polynomialShearIndexFintype patch.weight (fun i => patch.weight_pos i)
  obtain ⟨P, hP, hcenterP, hkeep⟩ :=
    exists_allocatedNormalizedShearProblem_of_returned_fiber_laws
      (E := E) (A := A) keep centerLift hcenter retained hretained
      (fun z => hsupported ⟨z.val, hsub z.property⟩)
      (fun z => sample ⟨z.val, hsub z.property⟩)
      (fun z => read ⟨z.val, hsub z.property⟩)
      (fun z => hread ⟨z.val, hsub z.property⟩)
      hshort patch (fun z => localForm z.val) (fun z => localLaw z.val)
      (fun z => (hslice z.val z.property).mono hpcost) f target
      (fun z => hscore z.val z.property)
  exact ⟨d, patch, hd, hdrank, hLip, hslots, P, hP ▸ hsub, hcenterP, hkeep⟩

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedProductiveRelativeScore
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

theorem relativePatchSourceTest_expect_physical
    {X Ω : Type*} [Fintype X] [Fintype Ω] {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ) (A : PolynomialPatch X s d)
    (physical : Ω → X → ℤ) (hphysical : ∀ u, physical u ∈ integerBox N) :
    (𝔼 u, relativePatchSourceTest N f a A (fun x => (physical u x : ℝ))) =
      𝔼 u, (f (physical u) - a) * A.value (fun x => (physical u x : ℝ)) := by
  apply Finset.expect_congr rfl
  intro u _
  rw [relativePatchSourceTest_integer, relativeBoxInput_eq N f (hphysical u)]

variable {m nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {N : Fin nX → ℕ}
    {widths : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ}
    {bases : Finset (Fin nX → ℤ)}
    {f : (Fin nX → ℤ) → ℝ} {a gain : ℝ}
    {s d : ℕ} {A : PolynomialPatch (Fin nX) s d}
    {z : bases × rectangularWeightIndices 0 widths 1}

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

namespace AllocatedPathProductivity

theorem relativePatch_child_score
    (hprod : AllocatedPathProductivity B U b S N widths bases
      (relativePatchSourceTest N f a A) gain z) :
    gain / 2 ≤ 𝔼 u : integerBox sides,
      (f (jointIntegerPhysicalSite u.val (z.1.val, z.2.val)) - a) *
        A.value (fun x => (jointIntegerPhysicalSite u.val (z.1.val, z.2.val) x : ℝ)) := by
  have hscore : gain / 2 ≤ 𝔼 u : integerBox sides,
      relativePatchSourceTest N f a A
        (fun x => (jointIntegerPhysicalSite u.val (z.1.val, z.2.val) x : ℝ)) := hprod.2.1
  exact hscore.trans_eq (relativePatchSourceTest_expect_physical N f a A
    (fun u : integerBox sides => jointIntegerPhysicalSite u.val (z.1.val, z.2.val))
    (fun u => by simpa only [mem_integerBox] using hprod.2.2 u))

end AllocatedPathProductivity
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProductivePaddedRelativeInitialization
namespace OAI

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m q s D E : ℕ} {X G : Type} [Fintype X] [Fintype G] [Nonempty G]
variable (L : RankPreparationFamily X (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (Deck j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)


end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m q s D E nX : ℕ} {G : Type} [Fintype G] [Nonempty G]
variable (L : RankPreparationFamily (Fin nX) (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (Deck j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)


attribute [local irreducible] integerBox

end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m q s D E nX : ℕ} {G : Type} [Fintype G] [Nonempty G]
variable (L : RankPreparationFamily (Fin nX) (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (Deck j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
local notation "Vars" => LayerSamplerVariables G I n B

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

attribute [local irreducible] RankPreparationFamily.pad integerBox

include hmq in
omit [∀ j, Fintype (Deck j)] in
theorem exists_relative_child_of_productive_padded_recovery
    {A : PolynomialPatch (Fin nX) s (D + E)} (F : A.LowestLayerModel m)
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (c : ∀ j, U j) (N : (Fin nX) → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n))
          (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := Vars) I n)
    (read : AllocatedActualCoefficientIndex G (Fin nX) I Deck n B → ℤ)
    (hread : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
      (fun j => (L.pad q j).poly) hm c z.1.val z.2.val sample read)
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain)
    (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    {p Pearly : ℝ} (hp0 : 0 ≤ p)
    (hDlog : (D : ℝ) ≤ Real.exp p) (hqlog : (q : ℝ) ≤ Real.exp p)
    (hLlog : (A.kernel.lip : ℝ) ≤ Real.exp p)
    (hNlog : ∀ j, (Fintype.card (L.pad q j).Coord : ℝ) ≤ Real.exp p)
    (hClog : ∀ j, C j ≤ Real.exp p) (hgainlog : Real.exp (-p) ≤ gain)
    (hδearly : δ ≤ Real.exp (-(3 * p + 130)))
    (hPearly : 6 * p + 35 ≤ Pearly)
    (hearly : ∀ C' : Fin q → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {n₀ stage d₀ : ℕ} {discount : ℝ} {cutoff cost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount cutoff cost)
    {pchild a Λ : ℝ} (hp2 : 2 ≤ p) (hpchild : p+2 ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card Vars : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (hDpos : 0 < D) (hrest : ∀ i : Fin E, m < A.weight (i.natAdd D))
    (hA : relativePatchComplexity A ≤ pchild)
    (hstage : relativePatchDistinctWeights A ≤ stage+1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s+2))
    (hproductive : AllocatedPathProductivity B U b S N
      (narrowTrimmedSpatialWidths (G := G)
        (J := PrincipalTupleIndex B (layerSamplerDegree I n))
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N)
      (trimmedIntegerBox N (spatialTrimMargin τ N))
      (relativePatchSourceTest N f a A) gain z) :
    ∃ fixed : {k : Vars // ¬H ≤ sides k} → ℤ,
      (∀ k, 0 ≤ fixed k ∧ fixed k < sides k) ∧
      RelativePatchSliceConclusion s
        (fun k : {k : Vars // H ≤ sides k} => sides k)
        (fun x => f (jointIntegerPhysicalSite
          (finiteSplitPoint (fun k : Vars => H ≤ sides k) x fixed) (z.1.val,z.2.val)))
        ((1-discount) ^ (stage+1) * Λ) (d₀+s*E) (cost pchild) := by
  refine F.exists_relative_child_of_allocated_padded_recovery
    (X := Fin nX) (G := G) (m := m) (q := q) (s := s) (D := D) (E := E)
    (A := A) (I := I) (Deck := Deck) (n := n) (R := R) (σ := σ) L hmq B U b hb o S hR hσ
    ip hip c₀ err hprepare hm hp hσ1 C hC hchart c N hN hτ hτhalf hξ1 hsize
    ⟨⟨z.1.val, by
      simpa only [trimmedIntegerBox, Finset.mem_image, mem_integerBox] using z.1.property⟩, z.2⟩
    sample read hread hδ hgain hgain1
    (fun x hx i => herr x (by simpa only [mem_integerBox] using hx) i) hp0 hDlog hqlog hLlog hNlog hClog
    hgainlog hδearly hPearly hearly ih hp2 hpchild ha haΛ hΛ habsolute hDim
    H hH hHcut hDpos hrest hA hstage
    (fun u => f (jointIntegerPhysicalSite u (z.1.val,z.2.val))) ?_ ?_ ?_
  · exact hproductive.pullback_mem_Icc (I := I) (n := n) (B := B)
      (J := fun j => (L.pad q j).Coord) (U := U) (b := b) (S := S) hf
  · exact hproductive.pullback_apFree (I := I) (n := n) (B := B)
      (J := fun j => (L.pad q j).Coord) (U := U) (b := b) (S := S)
      (by omega : 2 ≤ s + 2) hfree
  · exact hproductive.relativePatch_child_score (I := I) (n := n) (B := B)
      (J := fun j => (L.pad q j).Coord) (U := U) (b := b) (S := S)

end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators TensorProduct Classical

variable {m q s D E nX : ℕ} {G : Type} [Fintype G] [Nonempty G]
variable (L : RankPreparationFamily (Fin nX) (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
local notation "Vars" => LayerSamplerVariables G I n B

attribute [local irreducible] integerBox

include hmq in

theorem returned_fibers_of_productive_padded_relative_induction
    {oldPatch : PolynomialPatch (Fin nX) s (D + E)} (F : oldPatch.LowestLayerModel m)
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (N : Fin nX → ℕ) {τ ξ : ℝ} (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (stride : Fin nX → ℕ)
    (cells : Finset (ColumnResiduePattern (Option Vars) (Fin nX) stride))
    (center : CoefficientTorus (K := Vars) U)
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N
      (fun j => (L.pad q j).poly) hm τ ξ stride cells center)
    (centerLift : ∀ j, U j)
    (productive : Finset A.Path)
    (sample : productive → CoefficientSamplerArrays (K := Vars) I n)
    (read : productive → AllocatedActualCoefficientIndex G (Fin nX) I Deck n B → ℤ)
    (hread : ∀ z : productive,
      AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
        (fun j => (L.pad q j).poly) hm centerLift z.val.1.val z.val.2.val (sample z) (read z))
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain) (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    {p Pearly : ℝ} (hp0 : 0 ≤ p)
    (hDlog : (D : ℝ) ≤ Real.exp p) (hqlog : (q : ℝ) ≤ Real.exp p)
    (hLlog : (oldPatch.kernel.lip : ℝ) ≤ Real.exp p)
    (hNlog : ∀ j, (Fintype.card (L.pad q j).Coord : ℝ) ≤ Real.exp p)
    (hClog : ∀ j, C j ≤ Real.exp p) (hgainlog : Real.exp (-p) ≤ gain)
    (hδearly : δ ≤ Real.exp (-(3 * p + 130)))
    (hPearly : 6 * p + 35 ≤ Pearly)
    (hearly : ∀ C' : Fin q → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {n₀ stage d₀ : ℕ} {discount : ℝ} {cutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount cutoff childCost)
    {pchild a Λ : ℝ} (hp2 : 2 ≤ p) (hpchild : p + 2 ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card Vars : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (hDpos : 0 < D) (hrest : ∀ i : Fin E, m < oldPatch.weight (i.natAdd D))
    (hA : relativePatchComplexity oldPatch ≤ pchild)
    (hstage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hproductive : ∀ z : productive,
      AllocatedPathProductivity B U b S N A.widths A.bases
        (relativePatchSourceTest N f a oldPatch) gain z.val)
 :
    ∀ z ∈ productive, ∃ (fixed : {k : Vars // ¬H ≤ A.sides k} → ℤ),
      (∀ k, 0 ≤ fixed k ∧ fixed k < (A.sides k.val : ℤ)) ∧
      RelativePatchSliceConclusion s (fun k : {k : Vars // H ≤ A.sides k} => A.sides k.val)
        (fun u => f (jointIntegerPhysicalSite
          (finiteSplitPoint (fun k : Vars => H ≤ A.sides k) u fixed) (z.1.val,z.2.val)))
        ((1 - discount) ^ (stage + 1) * Λ) (d₀ + s * E) (childCost pchild) := by
  intro z hz
  let z' : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n))
          (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1 :=
    ⟨⟨z.1.val, by
      simpa only [trimmedIntegerBox, Finset.mem_image, mem_integerBox] using z.1.property⟩,
      ⟨z.2.val, by
      simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq]
        using z.2.property⟩⟩
  have hprod : AllocatedPathProductivity B U b S N
      (narrowTrimmedSpatialWidths (G := G)
        (J := PrincipalTupleIndex B (layerSamplerDegree I n))
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N)
      (trimmedIntegerBox N (spatialTrimMargin τ N))
      (relativePatchSourceTest N f a oldPatch) gain z' := by
    exact hproductive ⟨z,hz⟩
  exact F.exists_relative_child_of_productive_padded_recovery
    (m := m) (q := q) (s := s) (D := D) (E := E) (G := G)
    (I := I) (Deck := Deck) (n := n) (R := R) (σ := σ) (A := oldPatch)
    (τ := τ) (ξ := ξ) (δ := δ) (gain := gain) (p := p) (Pearly := Pearly)
    (n₀ := n₀) (stage := stage) (d₀ := d₀) (discount := discount)
    (cutoff := cutoff) (cost := childCost) (pchild := pchild) (a := a) (Λ := Λ)
    L hmq B U b hb o S hR hσ
    ip hip c₀ err hprepare hm hp hσ1 C hC hchart centerLift N A.size_pos A.trim_pos
    hτhalf hξ1 hsize
    z' (sample ⟨z,hz⟩) (read ⟨z,hz⟩) (hread ⟨z,hz⟩)
    hδ hgain hgain1 herr hp0 hDlog hqlog hLlog hNlog hClog hgainlog hδearly hPearly hearly
    ih hp2 hpchild ha haΛ hΛ habsolute hDim H hH hHcut hDpos hrest hA hstage
    f hf hfree hprod

end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators TensorProduct Classical

variable {m q s D E nX : ℕ} {G : Type} [Fintype G] [Nonempty G]
variable (L : RankPreparationFamily (Fin nX) (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (L.pad q j).Coord) (euclideanSubspace (U j)))]
local notation "Vars" => LayerSamplerVariables G I n B

include hmq in

theorem exists_normalizedProblem_of_productive_padded_relative_induction
    {oldPatch : PolynomialPatch (Fin nX) s (D + E)} (F : oldPatch.LowestLayerModel m)
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (N : Fin nX → ℕ) {τ ξ : ℝ} (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (stride : Fin nX → ℕ)
    (cells : Finset (ColumnResiduePattern (Option Vars) (Fin nX) stride))
    (center : CoefficientTorus (K := Vars) U)
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N
      (fun j => (L.pad q j).poly) hm τ ξ stride cells center)
    (centerLift : ∀ j, U j)
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    (productive : Finset A.Path) (hmass : 0 < A.law.mass productive)
    (hsupported : ∀ z : productive, 0 < A.law.weight z.val)
    (sample : productive → CoefficientSamplerArrays (K := Vars) I n)
    (read : productive → AllocatedActualCoefficientIndex G (Fin nX) I Deck n B → ℤ)
    (hread : ∀ z : productive,
      AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
        (fun j => (L.pad q j).poly) hm centerLift z.val.1.val z.val.2.val (sample z) (read z))
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain) (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    {p Pearly : ℝ} (hp0 : 0 ≤ p)
    (hDlog : (D : ℝ) ≤ Real.exp p) (hqlog : (q : ℝ) ≤ Real.exp p)
    (hLlog : (oldPatch.kernel.lip : ℝ) ≤ Real.exp p)
    (hNlog : ∀ j, (Fintype.card (L.pad q j).Coord : ℝ) ≤ Real.exp p)
    (hClog : ∀ j, C j ≤ Real.exp p) (hgainlog : Real.exp (-p) ≤ gain)
    (hδearly : δ ≤ Real.exp (-(3 * p + 130)))
    (hPearly : 6 * p + 35 ≤ Pearly)
    (hearly : ∀ C' : Fin q → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {n₀ stage d₀ : ℕ} {discount : ℝ} {cutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount cutoff childCost)
    {pchild a Λ : ℝ} (hp2 : 2 ≤ p) (hpchild : p + 2 ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card Vars : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (hDpos : 0 < D) (hrest : ∀ i : Fin E, m < oldPatch.weight (i.natAdd D))
    (hA : relativePatchComplexity oldPatch ≤ pchild)
    (hstage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hproductive : ∀ z : productive,
      AllocatedPathProductivity B U b S N A.widths A.bases
        (relativePatchSourceTest N f a oldPatch) gain z.val)
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hchildCost : 0 ≤ childCost pchild) (initialCost : ℝ)
    (hCost : childCost pchild ≤ initialCost) (hHcost : (H : ℝ) ≤ Real.exp initialCost) :
    let normalizationPower := (exists_relative_finite_returned_fiber_normalization.{0,0} s).choose
    let Qnorm := childCost pchild + (Fintype.card Vars : ℝ) + 2
    let Dnorm := min (d₀ + s * E) ⌊childCost pchild⌋₊
    let normalizedBudget := (Qnorm + 2) ^ normalizationPower
    let retainedMass := (A.law.mass productive / ((Dnorm + 1) * (s + 1) ^ Dnorm : ℕ)) *
      Real.exp (-normalizedBudget)
    ∃ (d : ℕ) (patch : PolynomialPatch Vars s d),
      d ≤ Dnorm ∧ d ≤ d₀ + s * E ∧
      (patch.kernel.lip : ℝ) ≤ Real.exp normalizedBudget ∧
      (∀ i, realPolynomialMass (patch.form.center i) ≤ normalizedBudget) ∧
      let := polynomialShearIndexFintype patch.weight (fun i => patch.weight_pos i)
      ∃ P : AllocatedExternalCandidateProblem (E := Deck) A
        (polynomialShearNilmanifold patch.weight s patch.weight_le)
        (RationalTorus.trivialFiltration s) 0 1
        (fun _ y => (patch.shearObservable y : ℂ))
        (fun x => ((f x - (1 - discount) ^ (stage + 1) * Λ : ℝ) : ℂ))
        initialCost retainedMass (Real.exp (-normalizedBudget)),
        P.productive ⊆ productive ∧ P.centerLift = centerLift ∧
          ∀ z, (P.chart z).keep = fun k => H ≤ A.sides k := by
  classical
  have htarget := recursive_discount_target_mem_Icc hdiscount
    ⟨(Real.exp_pos (-p)).le.trans (ha.trans haΛ), hΛ⟩ stage
  have hreturned := F.returned_fibers_of_productive_padded_relative_induction
    (I := I) (Deck := Deck) (n := n) L hmq B U b hb o S hR hσ ip hip c₀ err hprepare hm hp hσ1 C hC hchart
    N hτhalf hξ1 hsize stride cells center A centerLift productive
    sample read hread hδ hgain hgain1 herr hp0 hDlog hqlog hLlog hNlog hClog hgainlog
    hδearly hPearly hearly ih hp2 hpchild ha haΛ hΛ habsolute hDim H hH hHcut hDpos
    hrest hA hstage f hf hfree hproductive
  have hdec : (fun k : Vars => H.decLe (A.sides k)) =
      (fun k : Vars => Classical.propDecidable (H ≤ A.sides k)) := Subsingleton.elim _ _
  rw [hdec] at hreturned
  exact exists_allocatedFixedCenterNormalizedShearProblem (A := A) (E := Deck)
    s (fun k => H ≤ A.sides k) centerLift hcenter productive hmass hsupported
    sample read hread (childCost pchild) initialCost hchildCost hCost
    (fun i => (Nat.cast_le.mpr (Nat.le_of_lt (Nat.lt_of_not_ge i.property))).trans hHcost)
    (d₀ + s * E) f ((1 - discount) ^ (stage + 1) * Λ) htarget (fun x hx => hf x (by simpa only [mem_integerBox] using hx)) hξ1 hreturned

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedReadyPaddedRelativeInitialization
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators TensorProduct Classical

variable {m q s D E nX Mslot : ℕ}
variable (L : RankPreparationFamily (Fin nX) (Fin D) m) (hmq : m ≤ q)
variable {Deck : Fin q → Type} [∀ j, Fintype (Deck j)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin ((preparedSamplerTransverse (L.pad q)) j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous (L.pad q)) j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot)))) (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))) U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (L.pad q j).Coord) (euclideanSubspace (U j)))]

variable (bW : ∀ j, Basis (Deck j) ℤ
  (latticeSection (standardEuclideanLattice (L.pad q j).Coord) (euclideanSubspace (U j))))
variable [MeasurableSpace (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))) (PreparedSamplerContinuous (L.pad q)) (preparedSamplerTransverse (L.pad q)) (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))))) U)]
variable (μ : Measure (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))) (PreparedSamplerContinuous (L.pad q)) (preparedSamplerTransverse (L.pad q)) (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))))) U))

include hmq in

theorem exists_normalizedProblem_of_preparedReady_relative_induction_oai
    {oldPatch : PolynomialPatch (Fin nX) s (D + E)} (F : oldPatch.LowestLayerModel m)
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (N : Fin nX → ℕ) {τ ξ : ℝ} (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (stride : Fin nX → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))) (PreparedSamplerContinuous (L.pad q)) (preparedSamplerTransverse (L.pad q)) (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))))) (Fin nX) stride))
    (Acandidate : AllocatedExternalCandidateSamplerFamily (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))) U b S hb o hR hσ N
      (fun j => (L.pad q j).poly) hm τ ξ stride cells)
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain) (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    {p Pearly : ℝ} (hp0 : 0 ≤ p)
    (hDlog : (D : ℝ) ≤ Real.exp p) (hqlog : (q : ℝ) ≤ Real.exp p)
    (hLlog : (oldPatch.kernel.lip : ℝ) ≤ Real.exp p)
    (hNlog : ∀ j, (Fintype.card (L.pad q j).Coord : ℝ) ≤ Real.exp p)
    (hClog : ∀ j, C j ≤ Real.exp p) (hgainlog : Real.exp (-p) ≤ gain)
    (hδearly : δ ≤ Real.exp (-(3 * p + 130)))
    (hPearly : 6 * p + 35 ≤ Pearly)
    (hearly : ∀ C' : Fin q → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card ((PreparedSamplerContinuous (L.pad q)) j) : ℝ) + 1) * R j ≤ 1 / 4)
    {n₀ stage d₀ : ℕ} {discount : ℝ} {cutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount cutoff childCost)
    {pchild a Λ : ℝ} (hp2 : 2 ≤ p) (hpchild : p + 2 ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))) (PreparedSamplerContinuous (L.pad q)) (preparedSamplerTransverse (L.pad q)) (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot)))) : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (hDpos : 0 < D) (hrest : ∀ i : Fin E, m < oldPatch.weight (i.natAdd D))
    (hA : relativePatchComplexity oldPatch ≤ pchild)
    (hstage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hchildCost : 0 ≤ childCost pchild) (initialCost : ℝ)
    (hCost : childCost pchild ≤ initialCost) (hHcost : (H : ℝ) ≤ Real.exp initialCost)
    (gainLog : ℝ) (Qgood : ℕ) (eReady : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))))
    (Ready : CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))) (PreparedSamplerContinuous (L.pad q)) (preparedSamplerTransverse (L.pad q)) (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))))) U → Prop)
    (hready : PreparedCenteredProductiveGoodCenterReadyConclusion
      (m := q) (nX := nX) (M := Mslot) (L.pad q) U b S bW hb o hR hσ μ
      (fun j => (L.pad q j).poly) hm stride
      (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))) U b S N τ ξ) (Acandidate 0).bases
      gainLog gain Qgood eReady Acandidate.law N (relativePatchSourceTest N f a oldPatch) Ready) :
    PreparedCenteredProductiveGoodCenterEnhancedConclusion
      (m := q) (nX := nX) (M := Mslot) (L.pad q) U b S bW hb o hR hσ μ
      (fun j => (L.pad q j).poly) hm stride
      (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))) U b S N τ ξ) (Acandidate 0).bases
      gainLog gain Qgood eReady Acandidate.law N (relativePatchSourceTest N f a oldPatch) Ready
      (fun center centerLift productive =>
        AllocatedNormalizedCandidateConclusion (E := Deck) (A := Acandidate center)
          s (fun k => H ≤ (Acandidate center).sides k) centerLift productive
          (childCost pchild) initialCost (d₀ + s * E) f ((1 - discount) ^ (stage + 1) * Λ)) := by
  classical
  let : Nonempty (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))) := ⟨enlargedPreparedCommonCanonicalSelection q
    (modularInitialBlockCount q (nX + q * Mslot)) 0 (Nat.zero_le q) 0⟩
  unfold PreparedCenteredProductiveGoodCenterReadyConclusion at hready
  unfold PreparedCenteredProductiveGoodCenterEnhancedConclusion
  obtain ⟨c, hc, hcenter, sample, read, hglobal, hfinite⟩ := hready
  refine ⟨c, hc, hcenter, sample, read, hglobal, ?_⟩
  intro primes hprime
  let : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
  intro depth hdepth
  obtain ⟨center, productive, hReady, hmass, hF⟩ := hfinite primes hprime depth hdepth
  refine ⟨center, productive, hReady, hmass, hF, ?_⟩
  have hmasspos : 0 < (Acandidate center).law.mass productive :=
    lt_trans (div_pos hgain (by norm_num)) hmass
  have hdecG : instDecidableEqFin
      ((q + 1) * (q + 3) + (q + 1) * modularInitialBlockCount q (nX + q * Mslot)) =
      (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  have hinit := F.exists_normalizedProblem_of_productive_padded_relative_induction
    (m := m) (q := q) (s := s) (D := D) (E := E) (nX := nX) (Deck := Deck)
    (R := R) (σ := σ) (τ := τ) (ξ := ξ) (δ := δ) (gain := gain)
    (p := p) (Pearly := Pearly) (n₀ := n₀) (stage := stage) (d₀ := d₀)
    (discount := discount) (cutoff := cutoff) (childCost := childCost)
    (pchild := pchild) (a := a) (Λ := Λ)
    L hmq (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))) U b hb o S hR hσ ip hip c₀ err hprepare hm hp hσ1 C hC hchart
    N hτhalf hξ1 hsize stride cells center (Acandidate center)
    (c center) (hcenter center) productive hmasspos
    (fun z => (hF z.val z.property).1)
    (fun z => sample center z.val.1.val z.val.2.val)
    (fun z => allocatedJointFrameRead z.val.1.val (read center z.val.1.val z.val.2.val))
    (fun z => (hF z.val z.property).2.2.2.1)
    hδ hgain hgain1 herr hp0 hDlog hqlog hLlog hNlog hClog hgainlog hδearly hPearly hearly
    ih hp2 hpchild ha haΛ hΛ habsolute hDim H hH hHcut hDpos hrest hA hstage f hf hfree
    (fun z => by
      have hz := (hF z.val z.property).2.1
      rw [hdecG] at hz
      exact hz) hdiscount hchildCost initialCost hCost hHcost
  exact hinit

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.PolynomialPatch.LowestLayerModel.exists_normalizedProblem_of_preparedReady_relative_induction_oai := @OAI.Erdos3.PolynomialPatch.LowestLayerModel.exists_normalizedProblem_of_preparedReady_relative_induction_oai
