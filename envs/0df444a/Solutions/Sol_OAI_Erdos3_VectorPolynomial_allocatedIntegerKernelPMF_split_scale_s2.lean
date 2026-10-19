-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelPMF_split_scale_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:58:21.746998+00:00
-- url     : https://prove2.me/submissions/d2f765de-2d88-4b31-a188-17bc2092bc8b

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B217

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothProfileReindexing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_map_equiv_apply {X Y : Type*} (p : PMF X) (e : X ≃ Y) (y : Y) :
    (p.map e) y = p (e.symm y) := by
  classical
  rw [PMF.map_apply, tsum_eq_single (e.symm y)]
  · simp
  · intro z hz
    have he : y ≠ e z := by
      intro he
      apply hz
      apply e.injective
      simpa only [e.apply_symm_apply] using he.symm
    simp only [ite_eq_right_iff]
    exact fun h => (he h).elim

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedProductCoordinateLaw
namespace OAI


namespace Erdos3

open scoped Matrix

theorem coefficientPMF_apply {J : Type*} [Fintype J]
    (f : (J → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hZ : 0 < coefficientWeightSum f S)
    (z : J → ℤ) :
    (coefficientPMF f hf S hS hsupport hZ z).toReal = coefficientWeight f S z / coefficientWeightSum f S :=
  realWeightPMF_apply _ _ _ _ z

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientReindex
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {I J O : Type*} [Fintype I] [Fintype J]

theorem coefficientPMF_affine_reindex (e : I ≃ J) (c w S : J → ℝ)
    (hw : ∀ j, 0 < w j) (hS : ∀ j, 0 < S j) {R : ℝ} (hR : 0 ≤ R)
    (hcw : ∀ j, |c j|+w j ≤ R) (hZ : 0 < coefficientWeightSum (affineProductProfile c w) S) :
    (coefficientPMF (affineProductProfile (c ∘ e) (w ∘ e))
      (affineProductProfile_nonneg _ _ (fun i => hw (e i))) (S ∘ e) (fun i => hS (e i))
      (affineProductProfile_zero_outside _ _ (fun i => hw (e i)) hR (fun i => hcw (e i)))
      (by rw [affineCoefficientWeightSum_reindex]; exact hZ)).map (fun z => z ∘ e.symm) =
    coefficientPMF (affineProductProfile c w) (affineProductProfile_nonneg c w hw) S hS
      (affineProductProfile_zero_outside c w hw hR hcw) hZ := by
  let E : (I → ℤ) ≃ (J → ℤ) := Equiv.arrowCongr e (Equiv.refl ℤ)
  change (coefficientPMF _ _ _ _ _ _).map E = _
  ext z
  rw [pmf_map_equiv_apply]
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  change ((coefficientPMF _ _ _ _ _ _) (z ∘ e)).toReal = _
  rw [coefficientPMF_apply, coefficientPMF_apply,
    affineCoefficientWeight_reindex, affineCoefficientWeightSum_reindex]

theorem coefficientImagePMF_affine_reindex (A : Matrix O J ℤ) (e : I ≃ J) (c w S : J → ℝ)
    (hw : ∀ j, 0 < w j) (hS : ∀ j, 0 < S j) {R : ℝ} (hR : 0 ≤ R)
    (hcw : ∀ j, |c j|+w j ≤ R) (hZ : 0 < coefficientWeightSum (affineProductProfile c w) S) :
    coefficientImagePMF (A.submatrix id e) (affineProductProfile (c ∘ e) (w ∘ e))
      (affineProductProfile_nonneg _ _ (fun i => hw (e i))) (S ∘ e) (fun i => hS (e i))
      (affineProductProfile_zero_outside _ _ (fun i => hw (e i)) hR (fun i => hcw (e i)))
      (by rw [affineCoefficientWeightSum_reindex]; exact hZ) =
    coefficientImagePMF A (affineProductProfile c w) (affineProductProfile_nonneg c w hw) S hS
      (affineProductProfile_zero_outside c w hw hR hcw) hZ := by
  unfold coefficientImagePMF
  rw [← coefficientPMF_affine_reindex e c w S hw hS hR hcw hZ, PMF.map_comp]
  congr 1
  funext z
  exact Matrix.submatrix_mulVec_equiv A z id e

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

theorem monomialScale_kernelExponent {G X : Type*} {h : ℕ} (T : G ⊕ X → ℝ)
    (d : BoundedIntegerExponent G h) :
    monomialScale T (kernelExponentEmbedding G X h d).val =
      monomialScale (fun g => T (.inl g)) d.val :=
  Finsupp.prod_embDomain

theorem kernelExponent_eval_monomial {G X : Type*} {h : ℕ} (x : G ⊕ X → ℤ)
    (d : BoundedIntegerExponent G h) :
    MvPolynomial.eval x (MvPolynomial.monomial (kernelExponentEmbedding G X h d).val 1) =
      MvPolynomial.eval (fun g => x (.inl g)) (MvPolynomial.monomial d.val 1) := by
  change MvPolynomial.eval x (MvPolynomial.monomial (d.val.embDomain Function.Embedding.inl) 1) = _
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_embDomain]
  rfl

theorem integerMappedCubeTuple_kernel {G X Z Y α : Type*}
    (input : G ⊕ X → Option α → Z ⊕ Y) (z : Z → ℤ) (y : Y → ℤ)
    {L : ℕ} (x : G → IntegerScalarCubeBox α L)
    (hfixed : ∀ g a, Sum.elim z y (input (.inl g) a) = (x g a : ℤ)) (t : Finset α) :
    (fun g => integerMappedCubeTuple input z y t (.inl g)) =
      integerAffineCube (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) t := by
  funext g
  simp only [integerMappedCubeTuple, integerAffineCube, hfixed, scalarCubeDifferenceMatrix, sampledColumnMatrix]

theorem integerMappedJetMatrix_kernel {G X Z Y α O : Type*} [Fintype G] [DecidableEq α]
    (h : ℕ) (input : G ⊕ X → Option α → Z ⊕ Y) (z : Z → ℤ) (y : Y → ℤ)
    {L : ℕ} (x : G → IntegerScalarCubeBox α L)
    (hfixed : ∀ g a, Sum.elim z y (input (.inl g) a) = (x g a : ℤ)) (rows : O → Finset α) :
    (integerMappedJetMatrix (fun d : BoundedCoefficientExponent (G ⊕ X) h => d.val)
      input z rows y).submatrix id (kernelExponentEmbedding G X h) = scalarKernelIntegerJet x h rows := by
  ext o d
  change booleanCoefficient (fun t => MvPolynomial.eval (integerMappedCubeTuple input z y t)
      (MvPolynomial.monomial (kernelExponentEmbedding G X h d).val 1)) (rows o) =
    booleanCoefficient (fun t => MvPolynomial.eval
      (integerAffineCube (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) t)
      (MvPolynomial.monomial d.val 1)) (rows o)
  apply congrArg (fun f : Finset α → ℤ => booleanCoefficient f (rows o))
  funext t
  rw [kernelExponent_eval_monomial, integerMappedCubeTuple_kernel input z y x hfixed t]

theorem integerMappedJetMatrix_kernel_split {G X Z Y α O : Type*} [Fintype G] [DecidableEq α]
    (h : ℕ) (input : G ⊕ X → Option α → Z ⊕ Y) (z : Z → ℤ) (y : Y → ℤ)
    {L : ℕ} (x : G → IntegerScalarCubeBox α L)
    (hfixed : ∀ g a, Sum.elim z y (input (.inl g) a) = (x g a : ℤ)) (rows : O → Finset α) :
    (integerMappedJetMatrix (fun d : BoundedCoefficientExponent (G ⊕ X) h => d.val)
      input z rows y).submatrix id (kernelCoefficientEquiv G X h) =
      Matrix.fromCols (scalarKernelIntegerJet x h rows)
        (integerMappedJetMatrix (fun d : NonkernelCoefficient G X h => d.val.val) input z rows y) := by
  ext o d
  cases d with
  | inl d => exact congrFun (congrFun (integerMappedJetMatrix_kernel h input z y x hfixed rows) o) d
  | inr d => rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedKernelCoefficientScale (j : Fin m) (i : Fin (n j))
    (d : BoundedIntegerExponent G (j.val+1)) :
    allocatedIntegerProfileScales B U basis S j i (allocatedKernelCoefficientEquiv B j (.inl d)) =
      kernelJetCoefficientScale G (j.val+1) S.value (basisAxisScale (basis j) i) d := by
  change (basisAxisScale (basis j) i : ℝ) /
      monomialScale (layerSamplerBox B U basis S)
        (kernelExponentEmbedding G (PrincipalTupleIndex B (layerSamplerDegree I n)) (j.val+1) d).val = _
  rw [monomialScale_kernelExponent]
  rfl

theorem allocatedKernelCoefficientScales_split (j : Fin m) (i : Fin (n j)) :
    allocatedIntegerProfileScales B U basis S j i ∘ allocatedKernelCoefficientEquiv B j =
      Sum.elim (kernelJetCoefficientScale G (j.val+1) S.value (basisAxisScale (basis j) i))
        (fun d => (basisAxisScale (basis j) i : ℝ) /
          monomialScale (layerSamplerBox B U basis S) (allocatedNonkernelExponent B j d)) := by
  funext d
  cases d with
  | inl d => exact allocatedKernelCoefficientScale B U basis S j i d
  | inr d => rfl

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

theorem allocatedKernelJet_split {α O : Type*} [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (u : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) grid → ℤ)
    (v : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℤ)
    (rows : O → Finset α) :
    (integerMappedJetMatrix (fun d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) => d.val)
      (partitionedPrincipalInput grid (fun g a => (g, a)))
      (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v).submatrix id reindex =
      Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) rows)
        (integerMappedJetMatrix (allocatedNonkernelExponent B j)
          (partitionedPrincipalInput grid (fun g a => (g, a)))
          (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v) :=
  integerMappedJetMatrix_kernel_split (j.val+1) _ _ _ x (fun _ _ => rfl) rows

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedIntegerKernelComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedInteger" => Sum.elim
  (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ)) (principalTupleIntegers u)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "scales" => allocatedIntegerProfileScales B U basis S j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

theorem allocatedIntegerKernelPMF_reindexed :
    allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i hσ1 henormous =
      coefficientImagePMF
        (Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) (rows j))
          (integerMappedJetMatrix (allocatedNonkernelExponent B j) input fixedInteger (rows j)
            (principalTupleIntegers v)))
        (affineProductProfile (centers ∘ reindex) (widths ∘ reindex))
        (affineProductProfile_nonneg _ _ (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)))
        (scales ∘ reindex) (fun d => allocatedIntegerProfileScales_pos B U basis S j i (reindex d))
        (affineProductProfile_zero_outside _ _
          (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)) (hR j).le
          (fun d => allocatedKernelProfile_bound B hR hσ j i hσ1 (reindex d)))
        (allocatedKernelProfile_sum_pos B U basis hR hσ S j i hσ1 henormous) := by
  have he := coefficientImagePMF_affine_reindex (allocatedPartitionedJetMatrix B U basis S x u v rows j)
    reindex centers widths scales (allocatedIntegerProfileWidths_pos B hR hσ j i)
    (allocatedIntegerProfileScales_pos B U basis S j i) (hR j).le
    (allocatedKernelProfile_bound B hR hσ j i hσ1)
    (allocatedEnormous_profile_sum_pos B U basis hR hσ S j i hσ1 henormous)
  change coefficientImagePMF ((integerMappedJetMatrix _ _ _ _ _).submatrix id reindex) _ _ _ _ _ _ = _ at he
  rw [allocatedKernelJet_split B U basis S j x (principalTupleIntegers u) (principalTupleIntegers v) (rows j)] at he
  exact he.symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem coefficientImagePMF_congr_scale {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (f : (J → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x)
    {S T : J → ℝ} (hST : S = T) (hS : ∀ j, 0 < S j) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0)
    (hZS : 0 < coefficientWeightSum f S) (hZT : 0 < coefficientWeightSum f T) :
    coefficientImagePMF A f hf S hS hsupport hZS = coefficientImagePMF A f hf T hT hsupport hZT := by
  subst T
  rfl

end Erdos3

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α) (j : Fin m)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable (i : Fin (n j)) (s : O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id s).det ≠ 0)
variable (hσ1 : σ j ≤ 1) (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "height" => (basisAxisScale (basis j) i : ℝ)
local notation "heightPos" => Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) height
local notation "nonkernelScale" => fun d => height / monomialScale (layerSamplerBox B U basis S)
  (allocatedNonkernelExponent B j d)
local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedIntegerKernelPMF_split_scale_s2_oai
    (hZ : 0 < coefficientWeightSum (affineProductProfile (centers ∘ reindex) (widths ∘ reindex))
      (Sum.elim kernelScale nonkernelScale))
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i hσ1 henormous =
      coefficientImagePMF
        (Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) (rows j))
          (allocatedNonkernelJetMatrix B U basis S x u rows j v))
        (affineProductProfile (centers ∘ reindex) (widths ∘ reindex))
        (affineProductProfile_nonneg _ _ (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)))
        (Sum.elim kernelScale nonkernelScale)
        (Sum.rec (kernelJetCoefficientScale_pos G (j.val+1) (Nat.cast_pos.mpr S.positive) heightPos)
          (fun _d => div_pos heightPos (monomialScale_pos _
            (fun k => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S k)) _)))
        (affineProductProfile_zero_outside _ _
          (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)) (hR j).le
          (fun d => allocatedKernelProfile_bound B hR hσ j i hσ1 (reindex d))) hZ := by
  apply (allocatedIntegerKernelPMF_reindexed B U basis hR hσ S x u v rows j i hσ1 henormous).trans
  exact coefficientImagePMF_congr_scale _ _ _ (allocatedKernelCoefficientScales_split B U basis S j i) _ _ _ _ _

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelPMF_split_scale_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelPMF_split_scale_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
