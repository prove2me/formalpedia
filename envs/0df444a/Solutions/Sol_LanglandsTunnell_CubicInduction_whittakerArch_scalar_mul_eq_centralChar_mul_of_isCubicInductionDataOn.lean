-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.whittakerArch_scalar_mul_eq_centralChar_mul_of_isCubicInductionDataOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/26b13b2c-6938-56d5-a48b-8e5634a7ee79

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_whittakerArch_scalar_mul_eq_centralChar_mul_of_isCubicInductionDataOn

set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open LanglandsTunnell.CubicLambda LanglandsTunnell.TateLocal UnramifiedWhittaker
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace CENTARCH

open Matrix

noncomputable def archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) :=
  Matrix.of fun i j => ((g i j, (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)

theorem mapMatrix_arch_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = g := by
  ext i j
  simp [archMat3, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, NumberField.AdelicLevel.adeleArch_apply]

theorem mapMatrix_fin_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = 1 := by
  ext i j
  simp [archMat3, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, NumberField.AdelicLevel.adeleFin_apply]

theorem archMat3_one : archMat3 1 = 1 :=
  LanglandsTunnell.CubicInduction.matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ (by rw [mapMatrix_arch_archMat3, map_one])
    (by rw [mapMatrix_fin_archMat3, map_one])

theorem archMat3_mul (g h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    archMat3 (g * h) = archMat3 g * archMat3 h :=
  LanglandsTunnell.CubicInduction.matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ
    (by rw [map_mul, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3])
    (by rw [map_mul, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mul_one])

noncomputable def archEmbed3 : GL (Fin 3) (InfiniteAdeleRing ℚ) →* AdelicGL 3 (𝓞 ℚ) ℚ where
  toFun g :=
    { val := archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
      inv := archMat3 ((g⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
      val_inv := by rw [← archMat3_mul, Units.mul_inv, archMat3_one]
      inv_val := by rw [← archMat3_mul, Units.inv_mul, archMat3_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact archMat3_one)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact archMat3_mul _ _)

theorem archComponent3_archEmbed3 (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archComponent3 (𝓞 ℚ) ℚ (archEmbed3 g) = g := by
  apply Units.ext
  change RingHom.mapMatrix (NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ)
      (archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))) = (g : Matrix (Fin 3) (Fin 3) _)
  exact mapMatrix_arch_archMat3 _

theorem componentAt3_archEmbed3 (w : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ w (archEmbed3 g) = 1 := by
  apply Units.ext
  change RingHom.mapMatrix ((NumberField.AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp
      (NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
      (archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))) = _
  rw [RingHom.mapMatrix_apply, RingHom.coe_comp, ← Matrix.map_map, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, mapMatrix_fin_archMat3, map_one, Units.val_one]

theorem coe_centralScalarGL {A : Type*} [CommRing A] (u : Aˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      Matrix.scalar (Fin 3) (u : A) := rfl

theorem mapMatrix_scalar {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (r : A) :
    f.mapMatrix (Matrix.scalar (Fin 3) r) = Matrix.scalar (Fin 3) (f r) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, h]

theorem archComponent3_centralScalarGL (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (z : (InfiniteAdeleRing ℚ)ˣ) :
    archComponent3 (𝓞 ℚ) ℚ (centralScalarGL 3 (𝓞 ℚ) ℚ (E z)) = Matrix.GeneralLinearGroup.scalar (Fin 3) z := by
  have h := (hE z).1
  have hz : ((E z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = (z : InfiniteAdeleRing ℚ) := by
    rw [← M4aHerbrand.coe_infPart_apply, h]
  apply Units.ext
  change RingHom.mapMatrix (NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ)
      ((Matrix.GeneralLinearGroup.scalar (Fin 3) (E z) : GL (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 3) (Fin 3) _) =
    ((Matrix.GeneralLinearGroup.scalar (Fin 3) z : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) _)
  rw [coe_centralScalarGL, coe_centralScalarGL, mapMatrix_scalar, NumberField.AdelicLevel.adeleArch_apply, hz]

theorem componentAt3_centralScalarGL (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (z : (InfiniteAdeleRing ℚ)ˣ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ w (centralScalarGL 3 (𝓞 ℚ) ℚ (E z)) = 1 := by
  have h := (hE z).2
  have hz : ((E z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := by
    have := congrArg (fun x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ => (x : FiniteAdeleRing (𝓞 ℚ) ℚ)) h
    have h__ := this
    try simp [RatIdele.finPart] at h__
    try simp [RatIdele.finPart]
    exact h__
  apply Units.ext
  change RingHom.mapMatrix ((NumberField.AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp
      (NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
      ((Matrix.GeneralLinearGroup.scalar (Fin 3) (E z) : GL (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 3) (Fin 3) _) =
    ((1 : GL (Fin 3) (w.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) _)
  rw [coe_centralScalarGL, mapMatrix_scalar, RingHom.comp_apply, NumberField.AdelicLevel.adeleFin_apply, hz, map_one,
    Units.val_one]
  ext i j
  simp [Matrix.scalar_apply, Matrix.one_apply]

theorem centralScalarGL_mul_comm (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    g * centralScalarGL 3 (𝓞 ℚ) ℚ z = centralScalarGL 3 (𝓞 ℚ) ℚ z * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have hc : ((centralScalarGL 3 (𝓞 ℚ) ℚ z : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      Matrix.scalar (Fin 3) (z : AdeleRing (𝓞 ℚ) ℚ) := rfl
  have hs : Matrix.scalar (Fin 3) (z : AdeleRing (𝓞 ℚ) ℚ) = (z : AdeleRing (𝓞 ℚ) ℚ) • (1 : Matrix (Fin 3) (Fin 3) _) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.scalar_apply]
    · simp [Matrix.scalar_apply, h, Matrix.one_apply_ne h]
  rw [hc, hs, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]

end CENTARCH

open CENTARCH in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (pins : CarrierPins ℚ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ (S : Set (HeightOneSpectrum (𝓞 ℚ))) X)
    (h1 : ∀ v ∈ S, X.whittakerLoc v 1 = 1)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    X.whittakerArch (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) =
      ((X.centralChar (E z) : ℂˣ) : ℂ) * X.whittakerArch g := by
  classical

  have hcenW : ∀ (z₀ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (G : AdelicGL 3 (𝓞 ℚ) ℚ),
      X.whittaker (centralScalarGL 3 (𝓞 ℚ) ℚ z₀ * G) = ((X.centralChar z₀ : ℂˣ) : ℂ) * X.whittaker G := by
    intro z₀ G
    rw [hX.whittaker_eq, hX.whittaker_eq]
    unfold whittaker3
    have hcomm : ∀ x y t : AdeleRing (𝓞 ℚ) ℚ,
        X.form (upperUnipotent3 x y t * (centralScalarGL 3 (𝓞 ℚ) ℚ z₀ * G)) =
          ((X.centralChar z₀ : ℂˣ) : ℂ) * X.form (upperUnipotent3 x y t * G) := by
      intro x y t
      rw [← mul_assoc, centralScalarGL_mul_comm, mul_assoc, hX.central]
    simp_rw [hcomm, mul_assoc]
    simp_rw [MeasureTheory.integral_const_mul]

  have hT : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ (S : Set (HeightOneSpectrum (𝓞 ℚ))) → v ∈ S :=
    fun v hv => Finset.mem_coe.mp hv
  have hG : ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v (archEmbed3 g) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
    intro v _; rw [componentAt3_archEmbed3]; exact Subgroup.one_mem _
  have hG' : ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v (centralScalarGL 3 (𝓞 ℚ) ℚ (E z) * archEmbed3 g) ∈
      localMaximalCompact3 (𝓞 ℚ) ℚ v := by
    intro v _
    rw [map_mul, componentAt3_archEmbed3, componentAt3_centralScalarGL E hE, mul_one]
    exact Subgroup.one_mem _
  have hprod : ∏ v ∈ S, X.whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v (archEmbed3 g)) = 1 :=
    Finset.prod_eq_one fun v hv => by rw [componentAt3_archEmbed3]; exact h1 v hv
  have hprod' : ∏ v ∈ S,
      X.whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v (centralScalarGL 3 (𝓞 ℚ) ℚ (E z) * archEmbed3 g)) = 1 :=
    Finset.prod_eq_one fun v hv => by
      rw [map_mul, componentAt3_archEmbed3, componentAt3_centralScalarGL E hE, mul_one]; exact h1 v hv
  have h1' := hX.factorizable (archEmbed3 g) S hT hG
  have h2' := hX.factorizable (centralScalarGL 3 (𝓞 ℚ) ℚ (E z) * archEmbed3 g) S hT hG'
  rw [hprod, mul_one, archComponent3_archEmbed3] at h1'
  rw [hprod', mul_one, map_mul, archComponent3_archEmbed3, archComponent3_centralScalarGL E hE] at h2'
  rw [← h2', hcenW, h1']

end S_LanglandsTunnell_CubicInduction_whittakerArch_scalar_mul_eq_centralChar_mul_of_isCubicInductionDataOn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_whittakerArch_scalar_mul_eq_centralChar_mul_of_isCubicInductionDataOn (solution)
