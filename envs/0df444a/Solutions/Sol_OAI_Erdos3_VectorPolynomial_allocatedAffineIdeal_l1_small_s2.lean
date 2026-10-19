-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_l1_small_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:00:42.319911+00:00
-- url     : https://prove2.me/submissions/4161bd14-a3a0-4013-8bd0-24017a861dc1

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B213
import Definitions.Def_OAIE3v2B217
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineIdeal_l1_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineL1_primitive_bounds_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineSourceReferenceError_small_separated_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

theorem residueLatticeImage_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (residueLatticeImage L m).toAddSubgroup.index = L.toAddSubgroup.index := by
  have hk : (integerResidueMap I m).toAddMonoidHom.ker ≤ L.toAddSubgroup := by
    change (LinearMap.ker (integerResidueMap I m)).toAddSubgroup ≤ L.toAddSubgroup
    rw [integerResidueMap_ker]
    exact hperiod
  have h := L.toAddSubgroup.index_map_eq (integerResidueMap_surjective I m) hk
  change (L.toAddSubgroup.map (integerResidueMap I m).toAddMonoidHom).index = _
  exact h

theorem residueLatticeImage_card_mul_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    Nat.card (residueLatticeImage L m) * L.toAddSubgroup.index = m ^ Fintype.card I := by
  classical
  have h := (residueLatticeImage L m).toAddSubgroup.card_mul_index
  rw [residueLatticeImage_index L m hperiod] at h
  change Nat.card (residueLatticeImage L m) * L.toAddSubgroup.index = Nat.card (I → ZMod m) at h
  have heq : Nat.card (I → ZMod m) = m ^ Fintype.card I := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  exact h.trans heq

end Erdos3

end

section

namespace Erdos3

theorem residueLatticeImage_index_le {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    L.toAddSubgroup.index ≤ m ^ Fintype.card I := by
  have h := residueLatticeImage_card_mul_index L m hperiod
  have hpos := Nat.card_pos (α := residueLatticeImage L m)
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI


namespace Erdos3

theorem hasBoundedScalarPeriod_index_le {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (B : ℕ) (h : HasBoundedScalarPeriod L B) :
    L.toAddSubgroup.index ≤ B ^ Fintype.card I := by
  obtain ⟨a, ha, haB, hperiod⟩ := h
  let : NeZero a := ⟨ha.ne'⟩
  exact (residueLatticeImage_index_le L a hperiod).trans (Nat.pow_le_pow_left haB _)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI


namespace Erdos3

open scoped Matrix

theorem integerMatrix_fromCols_range {I J N : Type*} [Fintype J] [Fintype N]
    (B : Matrix I J ℤ) (C : Matrix I N ℤ) :
    (Matrix.fromCols B C).mulVecLin.range = B.mulVecLin.range ⊔ C.mulVecLin.range := by
  ext v
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨B *ᵥ (fun j => x (.inl j)), ⟨_, rfl⟩,
      C *ᵥ (fun n => x (.inr n)), ⟨_, rfl⟩, ?_⟩
    exact (Matrix.fromCols_mulVec B C x).symm.trans hx
  · rintro ⟨b, ⟨x, rfl⟩, c, ⟨y, rfl⟩, h⟩
    refine ⟨Sum.elim x y, ?_⟩
    change Matrix.fromCols B C *ᵥ Sum.elim x y = v
    rw [Matrix.fromCols_mulVec_sumElim]
    exact h

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScaleIndependence
namespace OAI


namespace Erdos3

theorem scalarKernelJet_extended_period {I J O N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype O] [Fintype N]
    {L B : ℕ} {κ : ℝ} (selection : I → J) (x : J → IntegerScalarCubeBox I L)
    (hx : GoodScalarKernelTuple selection κ B x) (h : ℕ) (rows : O → Finset I)
    (hr : Function.Injective rows) (hrows : ∀ o, (rows o).card ≤ h) (C : Matrix O N ℤ) :
    HasBoundedScalarPeriod (Matrix.fromCols (scalarKernelIntegerJet x h rows) C).mulVecLin.range (B ^ h) := by
  obtain ⟨a, ha, haB, hp⟩ := hx.2
  refine ⟨a ^ h, pow_pos ha h, Nat.pow_le_pow_left haB h, ?_⟩
  rw [integerMatrix_fromCols_range, Nat.cast_pow]
  exact (boundedDegreeIntegerJetMatrix_period _ _ (a : ℤ) hp h rows hr hrows).trans le_sup_left

theorem scalarKernelJet_extended_index {I J O N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype O] [Fintype N]
    {L B : ℕ} {κ : ℝ} (selection : I → J) (x : J → IntegerScalarCubeBox I L)
    (hx : GoodScalarKernelTuple selection κ B x) (h : ℕ) (rows : O → Finset I)
    (hr : Function.Injective rows) (hrows : ∀ o, (rows o).card ≤ h) (C : Matrix O N ℤ) :
    (Matrix.fromCols (scalarKernelIntegerJet x h rows) C).mulVecLin.range.toAddSubgroup.index ≤
      (B ^ h) ^ Fintype.card O :=
  hasBoundedScalarPeriod_index_le _ _ (scalarKernelJet_extended_period selection x hx h rows hr hrows C)


end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowReindex
namespace OAI


namespace Erdos3

theorem coefficientImageMultiplier_nonneg {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (v : I → ℤ) : 0 ≤ coefficientImageMultiplier A v := by
  classical
  unfold coefficientImageMultiplier
  split <;> positivity

theorem coefficientImageMultiplier_le_index {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (v : I → ℤ) :
    coefficientImageMultiplier A v ≤ (A.mulVecLin.range.toAddSubgroup.index : ℝ) := by
  classical
  unfold coefficientImageMultiplier
  split <;> simp


open MeasureTheory
open scoped BigOperators NNReal

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarCubeProductRiemannBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem scalarCubeGridBoundaryConstant_pos (I : Type*) [Fintype I] :
    0 < scalarCubeGridBoundaryConstant I := by
  unfold scalarCubeGridBoundaryConstant
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_finset]
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveShortLogBounds
namespace OAI

section

namespace Erdos3

theorem coefficientReplacementError_small {D L target supportLog amplitude ε : ℝ}
    (hD : 0 ≤ D) (hL : 0 ≤ L) (htarget : 0 ≤ target)
    (hSupport : supportLog ≤ L) (ha0 : 0 ≤ amplitude) (ha : amplitude ≤ Real.exp L)
    (output axes : ℕ) (ho : (output : ℝ) ≤ D) (hn : (axes : ℝ) ≤ D)
    (hε0 : 0 ≤ ε)
    (hε : ε ≤ Real.exp (-(target + coefficientReplacementErrorLog D L))) :
    (2 * Real.exp supportLog + 1) ^ output *
      (axes * ε * (1 + amplitude + ε) ^ axes) ≤ Real.exp (-target) := by
  let Q := coefficientReplacementErrorLog D L
  have hQ : 0 ≤ Q := by dsimp [Q, coefficientReplacementErrorLog]; positivity
  have he1 : ε ≤ 1 := hε.trans (Real.exp_le_one_iff.mpr (by change -(target + Q) ≤ 0; linarith))
  have heL : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr hL
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hbase : 2 * Real.exp supportLog + 1 ≤ Real.exp (L + 3) := by
    calc
      _ ≤ 3 * Real.exp L := by linarith [Real.exp_le_exp.mpr hSupport]
      _ ≤ Real.exp L * Real.exp 3 := by nlinarith [Real.exp_pos L]
      _ = _ := (Real.exp_add _ _).symm
  have hbase' : 1 + amplitude + ε ≤ Real.exp (L + 3) := by
    calc
      _ ≤ 3 * Real.exp L := by linarith only [ha, he1, heL]
      _ ≤ Real.exp L * Real.exp 3 := by nlinarith [Real.exp_pos L]
      _ = _ := (Real.exp_add _ _).symm
  have ho' := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ 2 * Real.exp supportLog + 1)
    hbase (by positivity : 0 ≤ L + 3) output ho
  have hn' := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ 1 + amplitude + ε)
    hbase' (by positivity : 0 ≤ L + 3) axes hn
  have haxes : (axes : ℝ) ≤ Real.exp D := hn.trans (by linarith [Real.add_one_le_exp D])
  have hcost : D * (L + 3) + D + D * (L + 3) ≤ Q := by
    dsimp [Q, coefficientReplacementErrorLog]
    nlinarith [mul_nonneg hD hL]
  have hcoeff : (2 * Real.exp supportLog + 1) ^ output * axes * (1 + amplitude + ε) ^ axes ≤ Real.exp Q := by
    calc
      _ ≤ Real.exp (D * (L + 3)) * Real.exp D * Real.exp (D * (L + 3)) := by gcongr
      _ ≤ _ := by rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr hcost
  calc
    _ = ((2 * Real.exp supportLog + 1) ^ output * axes * (1 + amplitude + ε) ^ axes) * ε := by ring
    _ ≤ Real.exp Q * Real.exp (-(target + Q)) :=
      (mul_le_mul_of_nonneg_right hcoeff hε0).trans (mul_le_mul_of_nonneg_left hε (Real.exp_pos _).le)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelReplacement
namespace OAI

section

namespace Erdos3

theorem layerKernelIndexBound_row {m B : ℕ} {α O : Type*} [Fintype α] [Fintype O]
    (hB : 0 < B) (hq : Fintype.card α ≤ m+1) (rows : O → Finset α)
    (hinj : Function.Injective rows) (j : Fin m) :
    (B^(j.val+1))^Fintype.card O ≤ layerKernelIndexBound m B := by
  have hc : Fintype.card O ≤ 2^(m+1) := by
    have hr : Fintype.card O ≤ 2^Fintype.card α := by
      simpa only [Fintype.card_finset] using Fintype.card_le_of_injective rows hinj
    exact hr.trans (Nat.pow_le_pow_right (by decide : 0 < 2) hq)
  rw [← pow_mul]
  exact Nat.pow_le_pow_right hB (Nat.mul_le_mul (Nat.succ_le_of_lt j.isLt) hc)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)

theorem allocatedIntegerKernelMask_bound {M : ℕ} {κ : ℝ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection κ M x)
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val + 1)
    (j : Fin m) (modulus : ℕ)
    (residue : Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (z : O j → ℤ) :
    0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus residue z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus residue z ≤ layerKernelIndexBound m M := by
  unfold allocatedIntegerKernelMask coefficientResidueMultiplier
  refine ⟨coefficientImageMultiplier_nonneg _ _, (coefficientImageMultiplier_le_index _ _).trans ?_⟩
  have hi := scalarKernelJet_extended_index selection x hx (j.val + 1) (rows j)
    (hinj j) (hrows j) (liftResidueMatrix residue)
  exact_mod_cast hi.trans (layerKernelIndexBound_row hM hq (rows j) (hinj j) j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.MixedGridBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem selectedOutput_card_split {I J : Type*} [Fintype I] [Fintype J] (s : J ↪ I) :
    Fintype.card (UnselectedColumn s)+Fintype.card J = Fintype.card I := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (selectedFreeFirstEquiv s)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedIdealRefinedPointwise
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α O D)

include h

theorem AllocatedComparisonDimensions.active_outputs
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P] :
    (Fintype.card (Σ a : {a // ¬P a}, O a.val.1) : ℝ) ≤ D := by
  let emb : (Σ a : {a // ¬P a}, O a.val.1) ↪ (Σ a : LayerSamplerAxis I n, O a.1) :=
    Function.Embedding.sigmaMap (Function.Embedding.subtype (fun a => ¬P a))
      (fun a => Function.Embedding.refl (O a.val.1))
  have hc := Fintype.card_le_of_embedding emb
  exact (Nat.cast_le.mpr hc).trans h.outputs

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineRecenteredSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable [∀ j, Nonempty (rowSets j)]
local notation "selectedRows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
variable (x : G → IntegerScalarCubeBox α S.value)
variable (s : ∀ j : Fin m, ↥(rowSets j) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (Subtype.val : rowSets j → Finset α)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := ↥(rowSets j))
  S.positive x (j.val + 1) (Subtype.val : rowSets j → Finset α) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U basis S)
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "ξ" => Measure.pi (fun j => Measure.pi (fun _ : rowSets j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S
local notation "cover" => quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
omit [∀ j, Nonempty (rowSets j)] in
theorem allocatedAffineIdeal_l1_small_s2_oai
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S) →
  EuclideanJetLayers U selectedRows → ℝ)
    (hgm : ∀ y, Measurable (g y)) (hg0 : ∀ y z, 0 ≤ g y z)
    (hgi : ∀ y, Integrable (g y) ξ)
    (hglaw : ∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
  (euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows) = realDensityMeasure ξ (g y))
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hρ : 0 < ρ grid) (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j) (hH : ∀ j : Tuple, 2 ≤ H j)
    (hδ : 0 < δ)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hm : 0 < modulus)
    (hsize : ∀ j : Tuple, (Fintype.card α + 1) * modulus ≤ H j)
    (hsmall : ∀ j : Tuple, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j : Tuple, (step j : ℝ) / L j ≤ ε)
    (selection : α ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hq : Fintype.card α ≤ m + 1)
    (hrowDegree : ∀ j (a : rowSets j), a.val.card ≤ j.val + 1)
    {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α jetRows P e) ≤ S.value)
    (hperiod : ∀ j : Fin m, integerScalarLattice (selectedRows j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    {D target Pk Prho : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B α selectedRows D)
    (hPk : 0 ≤ Pk) (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho) (hρlog : (ρ grid : ℝ)⁻¹ ≤ Real.exp Prho)
    (htarget : 0 ≤ target)
    (hη0 : 0 ≤ η)
    (hcoefsmall : εcoef ≤ Real.exp (-(target + 1 + coefficientReplacementErrorLog D (allocatedAffineL1Log m D P Prho Pk))))
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4)))
    (hratiosmall : (∑ j : Tuple, (modulus : ℝ) / H j) ≤
      Real.exp (-(target + 1 + affineReferenceCoefficientLog D (allocatedAffineL1Log m D P Prho Pk) + 4)))
    (hεsmall : ε ≤ Real.exp (-(target + 1 + affineReferenceCoefficientLog D (allocatedAffineL1Log m D P Prho Pk) + 4)))
    (hmeshsmall : mesh ≤ Real.exp (-(target + 1 + affineReferenceCoefficientLog D (allocatedAffineL1Log m D P Prho Pk) + 4))) :
    let center := principalProgressionSliceCenter (α := α) activeB activeDegree L c
    let width := principalProgressionSliceWidth (α := α) activeB activeDegree L H step
    let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬grid a}, selectedRows a.val.1) => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) (ρ grid) center width)
    let _outputResidue := fun (u : GridTuples) j => integerResidueMatrix
      (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    (∫ y, ‖((wholeLaw).mean (fun v => g v y) : ℂ) -
      ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows
        hb o bW d (principalAxisJoin grid u v₀) modulus ideal y) : ℂ)‖ ∂ξ) ≤
      Real.exp (-target) := by
  intro center width ideal outputResidue
  let Lb := allocatedAffineL1Log m D P Prho Pk
  have hD := hdimensions.nonneg
  have haxes := hdimensions.axes
  have houtputs := hdimensions.outputs
  have hlongoutputs := hdimensions.active_outputs B grid
  have hsplit := selectedOutput_card_split (allocatedLongIntegerSelect B U basis S (O := selectedRows))
  have hunselected : (Fintype.card (UnselectedColumn
      (allocatedLongIntegerSelect B U basis S (O := selectedRows))) : ℝ) ≤ D := by
    apply (Nat.cast_le.mpr (Nat.le_add_right _ _)).trans
    rw [hsplit]
    exact hlongoutputs
  have hinteger : (Fintype.card {o : (Σ a : {a // ¬grid a}, selectedRows a.val.1) //
      allocatedLongIntegerCoordinate B U basis S (O := selectedRows) o} : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hlongoutputs
  obtain ⟨hLb, hPL, hdensity, hsupport, hamp, hideal, hKi, hindexL, hboundary⟩ :=
    allocatedAffineL1_primitive_bounds_s2 B hdimensions hP hPrho hPk hMkPk grid R
      (fun j => (hR j).le) hRi (ρ grid) hρlog
  have hboundary0 : 0 ≤ scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) :=
    div_nonneg (scalarCubeGridBoundaryConstant_pos α).le (scalarCubeDomain_volumeReal_pos α).le
  let Cmask : ℝ := layerKernelIndexBound m Mk
  have hCmask : 1 ≤ Cmask := by
    dsimp only [Cmask, layerKernelIndexBound]
    exact_mod_cast (Nat.one_le_pow _ _ hMk)
  have hmask (u : GridTuples) (j : Fin m) (z : selectedRows j → ℤ) :=
    allocatedIntegerKernelMask_bound B U basis S x rows hMk selection hgood hq
      (fun _ => Subtype.val_injective) hrowDegree j modulus (outputResidue u j) z
  have hmaskL : Cmask ≤ Real.exp Lb :=
    (layerKernelIndexBound_le_exp m hMkPk).trans (Real.exp_le_exp.mpr hindexL)
  have hearlyMask : Cmask ^ Fintype.card (LayerSamplerAxis I n) ≤
      Real.exp (D * ((m * 2 ^ (m + 1) : ℕ) * Pk)) :=
    pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _) (layerKernelIndexBound_le_exp m hMkPk)
      (mul_nonneg (Nat.cast_nonneg _) hPk) _ haxes
  have hc := allocatedAffineIdeal_l1_s2 B U basis hR hσ S rowSets x s hA hMk hi
    hP hMkP hRP hRi hσi hcount Q hb o bW d H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell ν μ
    g hgm hg0 hgi hglaw ρ t htone hs hρ hρ1 hσsmall hstep hH hδ hdense hm hsize hsmall
    hε hmesh selection hgood hq he hεcoef hεe hlarge hperiod v₀ hv₀ hmesh0 hmesh1 hscaleMesh
    hCmask hmask T hT hsource C hC hchart hbudget
  have hactive : (Fintype.card {a // ¬grid a} : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le (fun a => ¬grid a))).trans haxes
  have hreplace := coefficientReplacementError_small hD hLb (by linarith : 0 ≤ target + 1)
    hsupport (mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)) hamp
    (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1))
    (Fintype.card {a // ¬grid a}) houtputs hactive hεcoef.le hcoefsmall
  have href := allocatedAffineSourceReferenceError_small_separated_s2 B U basis S α selectedRows (ρ grid) P
    (fun _ => modulus) H hearlyMask hD hLb hPL hdensity hsupport hideal hKi (zero_le_one.trans hCmask)
    hmaskL hboundary0 hboundary haxes hlongoutputs hunselected hinteger hη0 hε hmesh0
    hηsmall hratiosmall hεsmall hmeshsmall
  calc
    _ ≤ _ := hc
    _ ≤ Real.exp (-(target + 1)) + Real.exp (-(target + 1)) := add_le_add hreplace href
    _ ≤ Real.exp (-target) := by
      have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      calc
        _ = 2 * Real.exp (-(target + 1)) := by ring
        _ ≤ Real.exp 1 * Real.exp (-(target + 1)) :=
          mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uJ, uQ, u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_l1_small_s2_oai.{uJ, uQ, u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_l1_small_s2_oai.{uJ, uQ, u_1, u_2, u_3, u_4}
