-- Prove2me | solution 1 for OAI.ElementaryPositivity.RawShuffle.clearedSeparationB_cell
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:22.833966+00:00
-- url     : https://prove2.me/submissions/07b2e35a-ce50-41a4-997b-9546fdb98476

import Mathlib
import Definitions.Def_OAIQ368Chrom036
import Definitions.Def_OAIQ368Chrom037
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_cellTransfer_normalized

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentMapNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
variable {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
lemma mapRing_square (f : A →+* B) (g : C →+* D) (p : A →+* C) (q : B →+* D)
    (h : ∀ x,q (f x)=g (p x)) (x : LaurentSeries A) :
    mapRing q (mapRing f x)=mapRing g (mapRing p x) := by
  apply HahnSeries.ext
  funext k
  exact h (x.coeff k)
lemma mapUnit_square (f : A →+* B) (g : C →+* D) (p : A →+* C) (q : B →+* D)
    (h : ∀ x,q (f x)=g (p x)) (x : (LaurentSeries A)ˣ) :
    Units.map (mapRing q).toMonoidHom (Units.map (mapRing f).toMonoidHom x)=
      Units.map (mapRing g).toMonoidHom (Units.map (mapRing p).toMonoidHom x) := by
  apply Units.ext
  exact mapRing_square f g p q h x.val
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentScalarNaturality
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
lemma mapRing_rat_smul (f : R →ₐ[ℚ] S) (r : ℚ) (x : LaurentSeries R) :
    mapRing f.toRingHom (r • x)=r • mapRing f.toRingHom x := by
  apply HahnSeries.ext
  funext k
  simp only [mapRing_coeff,HahnSeries.coeff_smul]
  exact f.toLinearMap.map_smul r (x.coeff k)
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GridQuotient
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TensorColumns
open scoped TensorProduct
variable {K A B C D : Type*} [CommRing K]
  [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra K A] [Algebra K B] [Algebra K C] [Algebra K D]

lemma first_tmul (a : A) (b : B) :
    first (C:=C) (D:=D) (a⊗ₜ[K]b)=(a⊗ₜ[K]1)⊗ₜ[K](b⊗ₜ[K]1) := rfl
lemma second_tmul (c : C) (d : D) :
    second (A:=A) (B:=B) (c⊗ₜ[K]d)=(1⊗ₜ[K]c)⊗ₜ[K](1⊗ₜ[K]d) := rfl

end ElementaryPositivity.TensorColumns

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorColumnSeriesFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SeparationInfinity
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.unitalNatS
noncomputable local instance unitalNatSA_r9a1cfb_1 (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.unitalNatB
noncomputable local instance unitalNatBA_r9a1cfb_1 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d⊗[ℚ]B a μ e) := inferInstance
lemma unitalRestrictionRelativeB_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (f : S (d+e)) :
    unitalRestrictionRelativeB a c η hc hs (quotientAlg a (slope c η) (d+e) f)=
    Polynomial.map (quotientTensor a (slope c η) d e).toRingHom
      (relativeTaylor d e (restrictTensor (firstCut d e) f)) := by
  rw [relativeTaylor_quotient]
  rfl

lemma unitalSeparationSeries_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (f : S (d+e)) :
    unitalSeparationSeries a c η hc hs (quotientAlg a (slope c η) (d+e) f)=
    mapRing (quotientTensor a (slope c η) d e).toRingHom (tensorSeparationSeries a d e f) := by
  rw [tensorSeparationSeries,mapRing_mul_polynomial]
  dsimp only [unitalSeparationSeries,LinearMap.comp_apply,AlgHom.toLinearMap_apply]
  rw [unitalRestrictionRelativeB_mk]
  rfl

end ElementaryPositivity.RawShuffle.SeparationInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ClearedSeparationB
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
open SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma mapRing_ratio_val {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (u v : (LaurentSeries R)ˣ) :
    mapRing f (u*v⁻¹).val=
      (Units.map (mapRing f).toMonoidHom u*(Units.map (mapRing f).toMonoidHom v)⁻¹).val := by
  rw [Units.val_mul,map_mul]
  rfl

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.clearBTensorS
noncomputable local instance clearBTensorSA_r9a1cfb_1 (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.clearBTensorB
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.clearBTensorBA
lemma clearedSeparationB_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (x : S d⊗[ℚ]S e) :
    clearedSeparationB a μ d e (quotientTensor a μ d e x)=
    mapRing (quotientTensor a μ d e).toRingHom
      ((inverseKernelUnit a d e*(inverseKernelUnit (fun _ _ : I=>0) d e)⁻¹).val *
        polynomial (relativeTaylor d e x)) := by
  rw [mapRing_mul_polynomial,mapRing_ratio_val,relativeTaylor_quotient]
  rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorColumnNaturality
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TensorColumns
open scoped TensorProduct
variable {K A B C D A' B' C' D' : Type*} [Field K]
  [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [CommRing A'] [CommRing B'] [CommRing C'] [CommRing D']
  [Algebra K A] [Algebra K B] [Algebra K C] [Algebra K D]
  [Algebra K A'] [Algebra K B'] [Algebra K C'] [Algebra K D']

lemma map_first (f : A →ₐ[K] A') (g : B →ₐ[K] B') (h : C →ₐ[K] C') (k : D →ₐ[K] D')
    (x : A⊗[K]B) :
    Algebra.TensorProduct.map (Algebra.TensorProduct.map f h) (Algebra.TensorProduct.map g k)
      (first x)=first (Algebra.TensorProduct.map f g x) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a b => simp only [first_tmul,Algebra.TensorProduct.map_tmul,map_one]

lemma map_second (f : A →ₐ[K] A') (g : B →ₐ[K] B') (h : C →ₐ[K] C') (k : D →ₐ[K] D')
    (x : C⊗[K]D) :
    Algebra.TensorProduct.map (Algebra.TensorProduct.map f h) (Algebra.TensorProduct.map g k)
      (second x)=second (Algebra.TensorProduct.map h k x) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul c d => simp only [second_tmul,Algebra.TensorProduct.map_tmul,map_one]

lemma map_middle (f : A →ₐ[K] A') (g : B →ₐ[K] B') (h : C →ₐ[K] C') (k : D →ₐ[K] D')
    (x : C⊗[K]B) :
    Algebra.TensorProduct.map (Algebra.TensorProduct.map f h) (Algebra.TensorProduct.map g k)
      (ElementaryPositivity.LinearDetection.middleEmbedding x)=
    ElementaryPositivity.LinearDetection.middleEmbedding (Algebra.TensorProduct.map h g x) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul c b =>
    change Algebra.TensorProduct.map (Algebra.TensorProduct.map f h) (Algebra.TensorProduct.map g k)
      ((1⊗ₜ[K]c)⊗ₜ[K](b⊗ₜ[K]1))=(1⊗ₜ[K]h c)⊗ₜ[K](g b⊗ₜ[K]1)
    simp only [Algebra.TensorProduct.map_tmul,map_one]

end ElementaryPositivity.TensorColumns

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.LinearDetection
open ElementaryPositivity.SlopeArithmetic
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing
attribute [local instance] cellSepTensorSemiring cellSepTensorNonAssoc cellSepFourSemiring cellSepFourNonAssoc cellSepFourModule
attribute [local instance] braidFourTensor braidFourTensorAlg braidFourRing braidFourAlg
attribute [local instance] braidFourTensorN braidFourTensorM braidFourN braidFourM

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.quotientFourSemiring
noncomputable local instance quotientFourNonAssoc_r9a1cfb_1 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d₁ e₁ d₂ e₂ : I → ℕ) :
    NonAssocSemiring ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂)) :=
  (braidFourRing a μ d₁ e₁ d₂ e₂).toNonAssocSemiring
lemma fourQuotient_firstColumn (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (x : S d₁⊗[ℚ]S d₂) :
    fourQuotient a μ d₁ e₁ d₂ e₂ (firstColumnAlg d₁ e₁ d₂ e₂ x)=
    firstColumnBAlg a μ d₁ e₁ d₂ e₂ (quotientTensor a μ d₁ d₂ x) :=
  ElementaryPositivity.TensorColumns.map_first
    (quotientAlg a μ d₁) (quotientAlg a μ d₂) (quotientAlg a μ e₁) (quotientAlg a μ e₂) x

lemma fourQuotient_secondColumn (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (x : S e₁⊗[ℚ]S e₂) :
    fourQuotient a μ d₁ e₁ d₂ e₂ (secondColumnAlg d₁ e₁ d₂ e₂ x)=
    secondColumnBAlg a μ d₁ e₁ d₂ e₂ (quotientTensor a μ e₁ e₂ x) :=
  ElementaryPositivity.TensorColumns.map_second
    (quotientAlg a μ d₁) (quotientAlg a μ d₂) (quotientAlg a μ e₁) (quotientAlg a μ e₂) x

lemma fourQuotient_crossingColumn (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (x : S e₁⊗[ℚ]S d₂) :
    fourQuotient a μ d₁ e₁ d₂ e₂ (crossingColumnAlg d₁ e₁ d₂ e₂ x)=
    crossingColumnBAlg a μ d₁ e₁ d₂ e₂ (quotientTensor a μ e₁ d₂ x) :=
  ElementaryPositivity.TensorColumns.map_middle
    (quotientAlg a μ d₁) (quotientAlg a μ d₂) (quotientAlg a μ e₁) (quotientAlg a μ e₂) x

lemma fourSeriesQuotient_firstColumn (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (F : LaurentSeries (S d₁⊗[ℚ]S d₂)) :
    mapRing (fourQuotient a μ d₁ e₁ d₂ e₂).toRingHom
      (mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom F)=
    mapRing (firstColumnBAlg a μ d₁ e₁ d₂ e₂).toRingHom
      (mapRing (quotientTensor a μ d₁ d₂).toRingHom F) := by
  apply HahnSeries.ext
  funext j
  exact fourQuotient_firstColumn a μ d₁ e₁ d₂ e₂ (F.coeff j)

lemma fourSeriesQuotient_secondColumn (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (F : LaurentSeries (S e₁⊗[ℚ]S e₂)) :
    mapRing (fourQuotient a μ d₁ e₁ d₂ e₂).toRingHom
      (mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom F)=
    mapRing (secondColumnBAlg a μ d₁ e₁ d₂ e₂).toRingHom
      (mapRing (quotientTensor a μ e₁ e₂).toRingHom F) := by
  apply HahnSeries.ext
  funext j
  exact fourQuotient_secondColumn a μ d₁ e₁ d₂ e₂ (F.coeff j)

lemma fourSeriesQuotient_crossingUnit (a b : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Units.map (mapRing (fourQuotient a μ d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
      (mappedInverseKernel b e₁ d₂ (crossingColumnAlg d₁ e₁ d₂ e₂))=
    Units.map (mapRing (crossingColumnBAlg a μ d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
      (mixedInverseKernelUnit a b μ e₁ d₂) :=
  mapUnit_square (crossingColumnAlg d₁ e₁ d₂ e₂).toRingHom
    (crossingColumnBAlg a μ d₁ e₁ d₂ e₂).toRingHom
    (quotientTensor a μ e₁ d₂).toRingHom (fourQuotient a μ d₁ e₁ d₂ e₂).toRingHom
    (fourQuotient_crossingColumn a μ d₁ e₁ d₂ e₂) (inverseKernelUnit b e₁ d₂)

lemma unit_map_ratio_square {R S T : Type*} [Ring R] [Ring S] [Ring T]
    (f : R →+* T) (g : S →+* T) (x y : Rˣ) (x' y' : Sˣ)
    (hx : Units.map f.toMonoidHom x=Units.map g.toMonoidHom x')
    (hy : Units.map f.toMonoidHom y=Units.map g.toMonoidHom y') :
    f (x*y⁻¹).val=g (x'*y'⁻¹).val := by
  have h : Units.map f.toMonoidHom (x*y⁻¹)=Units.map g.toMonoidHom (x'*y'⁻¹) := by
    rw [map_mul,map_inv,map_mul,map_inv,hx,hy]
  exact congrArg Units.val h

lemma fourSeriesQuotient_crossingRatio (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    mapRing (fourQuotient a μ d₁ e₁ d₂ e₂).toRingHom
      (mappedInverseKernel a e₁ d₂ (crossingColumnAlg d₁ e₁ d₂ e₂) *
        (mappedInverseKernel (fun i j=>a j i) e₁ d₂ (crossingColumnAlg d₁ e₁ d₂ e₂))⁻¹).val=
    mapRing (crossingColumnBAlg a μ d₁ e₁ d₂ e₂).toRingHom (braidingRatioUnit a μ e₁ d₂).val := by
  exact unit_map_ratio_square
    (mapRing (fourQuotient a μ d₁ e₁ d₂ e₂).toRingHom)
    (mapRing (crossingColumnBAlg a μ d₁ e₁ d₂ e₂).toRingHom) _ _ _ _
    (fourSeriesQuotient_crossingUnit a a μ d₁ e₁ d₂ e₂)
    (fourSeriesQuotient_crossingUnit a (fun i j=>a j i) μ d₁ e₁ d₂ e₂)

lemma fourInputSeriesB_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (hd : d₁=0 ∨ d₂=0 ∨ slope c η d₁=slope c η d₂)
    (he : e₁=0 ∨ e₂=0 ∨ slope c η e₁=slope c η e₂)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    mapRing (fourQuotient a (slope c η) d₁ e₁ d₂ e₂).toRingHom
      (fourInputSeries a d₁ e₁ d₂ e₂ f g)=
    fourInputSeriesB a c η hc d₁ e₁ d₂ e₂ hd he
      (quotientAlg a (slope c η) (d₁+d₂) f) (quotientAlg a (slope c η) (e₁+e₂) g) := by
  rewrite [fourInputSeries,map_mul,map_mul,
    fourSeriesQuotient_firstColumn a (slope c η) d₁ e₁ d₂ e₂ (tensorSeparationSeries a d₁ d₂ f),
    fourSeriesQuotient_secondColumn a (slope c η) d₁ e₁ d₂ e₂ (tensorSeparationSeries a e₁ e₂ g),
    fourSeriesQuotient_crossingRatio a (slope c η) d₁ e₁ d₂ e₂,
    fourInputSeriesB,unitalSeparationSeries_mk a c η hc d₁ d₂ hd f,
    unitalSeparationSeries_mk a c η hc e₁ e₂ he g]
  dsimp only [ElementaryPositivity.TensorColumns.seriesProduct,firstColumnBAlg,secondColumnBAlg]
  exact mul_comm _ _

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TwoTargetFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing
attribute [local instance] cellSepTensorSemiring cellSepTensorNonAssoc cellSepFourSemiring cellSepFourNonAssoc cellSepFourModule
attribute [local instance] braidFourTensor braidFourTensorAlg braidFourRing braidFourAlg
attribute [local instance] braidFourTensorN braidFourTensorM braidFourN braidFourM

lemma quotient_twoTargetSeries (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (h₁ : d₁=0 ∨ e₁=0 ∨ slope c η d₁=slope c η e₁)
    (h₂ : d₂=0 ∨ e₂=0 ∨ slope c η d₂=slope c η e₂)
    (F : LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂))) :
    mapRing (quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂)).toRingHom
      (mapLinear (twoTargetTransfer a d₁ e₁ d₂ e₂) F)=
    mapLinear (twoTargetTransferB a c η hc d₁ e₁ d₂ e₂ h₁ h₂)
      (mapRing (fourQuotient a (slope c η) d₁ e₁ d₂ e₂).toRingHom F) := by
  apply HahnSeries.ext
  funext j
  exact quotient_twoTargetTransfer_unit a c η hc d₁ e₁ d₂ e₂ h₁ h₂ (F.coeff j)

lemma clearedSeparationB_cell_oai (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (hd : d₁=0 ∨ d₂=0 ∨ slope c η d₁=slope c η d₂)
    (he : e₁=0 ∨ e₂=0 ∨ slope c η e₁=slope c η e₂)
    (h₁ : d₁=0 ∨ e₁=0 ∨ slope c η d₁=slope c η e₁)
    (h₂ : d₂=0 ∨ e₂=0 ∨ slope c η d₂=slope c η e₂)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    clearedSeparationB a (slope c η) (d₁+e₁) (d₂+e₂)
      (quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂)
        (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)))=
    ((-1 : ℚ)^eulerForm a d₂ e₁) •
      mapLinear (twoTargetTransferB a c η hc d₁ e₁ d₂ e₂ h₁ h₂)
        (fourInputSeriesB a c η hc d₁ e₁ d₂ e₂ hd he
          (quotientAlg a (slope c η) (d₁+d₂) f) (quotientAlg a (slope c η) (e₁+e₂) g)) := by
  rw [clearedSeparationB_mk,cellTransfer_normalized,mapRing_rat_smul,
    quotient_twoTargetSeries a c η hc d₁ e₁ d₂ e₂ h₁ h₂,
    fourInputSeriesB_mk a c η hc d₁ e₁ d₂ e₂ hd he]

end ElementaryPositivity.RawShuffle

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElementaryPositivity.RawShuffle.clearedSeparationB_cell_oai.{u_1} := @OAI.ElementaryPositivity.RawShuffle.clearedSeparationB_cell_oai.{u_1}
