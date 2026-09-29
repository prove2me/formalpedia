-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_mul_eq_unipotent_mul_diagonal_mul_compact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/abdcd472-2b5c-5d2c-a31b-3184c4f8beb7

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_Growth
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_componentAt3_mul_mem_localMaximalCompact3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_orthogonal_real
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_compact
p2m_attr_erase "instance" "NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LanglandsTunnell.RankinSelberg.mem_primeFibre HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul"

set_option autoImplicit false

p2m_open "Matrix NumberField NumberField.AdelicLevel IsDedekindDomain LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_compact.LanglandsTunnell.CubicInduction"

noncomputable section

namespace SiegelArchEmbed

variable (F : Type) [Field F]

open scoped Classical in
private def archPiMat3 (v₀ : InfinitePlace F) (g : Matrix (Fin 3) (Fin 3) v₀.Completion) :
    Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing F) :=
  Matrix.of fun i j =>
    (Function.update ((1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing F)) i j) v₀ (g i j) : InfiniteAdeleRing F)

private theorem matrix_eq_of_forall_archEval {M N : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing F)}
    (h : ∀ w : InfinitePlace F, (archEval F w).mapMatrix M = (archEval F w).mapMatrix N) : M = N := by
  refine Matrix.ext fun i j => funext fun w => ?_
  have hw := congrFun (congrFun (h w) i) j
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, archEval_apply] using hw

open scoped Classical in
private theorem archEval_mapMatrix_archPiMat3_self (v₀ : InfinitePlace F) (g : Matrix (Fin 3) (Fin 3) v₀.Completion) :
    (archEval F v₀).mapMatrix (archPiMat3 F v₀ g) = g := by
  ext i j
  simp [archPiMat3, archEval_apply]

open scoped Classical in
private theorem archEval_mapMatrix_archPiMat3_of_ne (v₀ : InfinitePlace F) (g : Matrix (Fin 3) (Fin 3) v₀.Completion)
    {w : InfinitePlace F} (hw : w ≠ v₀) : (archEval F w).mapMatrix (archPiMat3 F v₀ g) = 1 := by
  ext i j
  simp only [archPiMat3, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, archEval_apply,
    Function.update_of_ne hw]
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    rfl
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij]
    rfl

private theorem archPiMat3_one (v₀ : InfinitePlace F) : archPiMat3 F v₀ 1 = 1 :=
  matrix_eq_of_forall_archEval F fun w => by
    by_cases hw : w = v₀
    · subst hw
      rw [archEval_mapMatrix_archPiMat3_self, map_one]
    · rw [archEval_mapMatrix_archPiMat3_of_ne F _ _ hw, map_one]

private theorem archPiMat3_mul (v₀ : InfinitePlace F) (g h : Matrix (Fin 3) (Fin 3) v₀.Completion) :
    archPiMat3 F v₀ (g * h) = archPiMat3 F v₀ g * archPiMat3 F v₀ h :=
  matrix_eq_of_forall_archEval F fun w => by
    by_cases hw : w = v₀
    · subst hw
      rw [map_mul, archEval_mapMatrix_archPiMat3_self, archEval_mapMatrix_archPiMat3_self,
        archEval_mapMatrix_archPiMat3_self]
    · rw [map_mul, archEval_mapMatrix_archPiMat3_of_ne F _ _ hw, archEval_mapMatrix_archPiMat3_of_ne F _ _ hw,
        archEval_mapMatrix_archPiMat3_of_ne F _ _ hw, mul_one]

variable [NumberField F]

private def infMat3 (M : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing F)) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j =>
    ((M i j, (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F)

private theorem matrix_eq_of_arch_fin {M N : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 F) F)}
    (h₁ : (adeleArch (𝓞 F) F).mapMatrix M = (adeleArch (𝓞 F) F).mapMatrix N)
    (h₂ : (adeleFin (𝓞 F) F).mapMatrix M = (adeleFin (𝓞 F) F).mapMatrix N) : M = N := by
  ext i j
  have hw₁ := congrFun (congrFun h₁ i) j
  have hw₂ := congrFun (congrFun h₂ i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply, adeleFin_apply] at hw₁ hw₂
  exact Prod.ext hw₁ hw₂

private theorem adeleArch_mapMatrix_infMat3 (M : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing F)) :
    (adeleArch (𝓞 F) F).mapMatrix (infMat3 F M) = M := by
  ext i j
  simp [infMat3, adeleArch_apply]

private theorem adeleFin_mapMatrix_infMat3 (M : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing F)) :
    (adeleFin (𝓞 F) F).mapMatrix (infMat3 F M) = 1 := by
  ext i j
  simp [infMat3, adeleFin_apply]

private theorem infMat3_one : infMat3 F 1 = 1 :=
  matrix_eq_of_arch_fin F (by rw [adeleArch_mapMatrix_infMat3, map_one])
    (by rw [adeleFin_mapMatrix_infMat3, map_one])

private theorem infMat3_mul (M N : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing F)) :
    infMat3 F (M * N) = infMat3 F M * infMat3 F N :=
  matrix_eq_of_arch_fin F
    (by rw [map_mul, adeleArch_mapMatrix_infMat3, adeleArch_mapMatrix_infMat3, adeleArch_mapMatrix_infMat3])
    (by rw [map_mul, adeleFin_mapMatrix_infMat3, adeleFin_mapMatrix_infMat3, adeleFin_mapMatrix_infMat3, mul_one])

private def archEmbed3 (v₀ : InfinitePlace F) : GL (Fin 3) v₀.Completion →* AdelicGL 3 (𝓞 F) F where
  toFun g :=
    { val := infMat3 F (archPiMat3 F v₀ g)
      inv := infMat3 F (archPiMat3 F v₀ ((g⁻¹ : GL (Fin 3) v₀.Completion) : Matrix _ _ _))
      val_inv := by rw [← infMat3_mul, ← archPiMat3_mul, Units.mul_inv, archPiMat3_one, infMat3_one]
      inv_val := by rw [← infMat3_mul, ← archPiMat3_mul, Units.inv_mul, archPiMat3_one, infMat3_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; rw [archPiMat3_one, infMat3_one])
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; rw [archPiMat3_mul, infMat3_mul])

private theorem coe_archEmbed3 (v₀ : InfinitePlace F) (g : GL (Fin 3) v₀.Completion) :
    (archEmbed3 F v₀ g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 F) F)) = infMat3 F (archPiMat3 F v₀ g) := rfl

variable {F}

private theorem
    componentAt3_archEmbed3 (v₀ : InfinitePlace F) (p : HeightOneSpectrum (𝓞 F)) (g : GL (Fin 3) v₀.Completion) :
    componentAt3 (𝓞 F) F p (archEmbed3 F v₀ g) = 1 :=
  Units.ext (by
    show (finAdeleEval (𝓞 F) F p).mapMatrix ((adeleFin (𝓞 F) F).mapMatrix (infMat3 F (archPiMat3 F v₀ g))) = 1
    rw [adeleFin_mapMatrix_infMat3, map_one])

private theorem archPlaceComponent3_archEmbed3_self (v₀ : InfinitePlace F) (g : GL (Fin 3) v₀.Completion) :
    archPlaceComponent3 F v₀ (archEmbed3 F v₀ g) = g :=
  Units.ext (by
    show (archEval F v₀).mapMatrix ((adeleArch (𝓞 F) F).mapMatrix (infMat3 F (archPiMat3 F v₀ g))) = g
    rw [adeleArch_mapMatrix_infMat3, archEval_mapMatrix_archPiMat3_self])

private theorem archPlaceComponent3_archEmbed3_of_ne (v₀ : InfinitePlace F) (g : GL (Fin 3) v₀.Completion)
    {w : InfinitePlace F} (hw : w ≠ v₀) : archPlaceComponent3 F w (archEmbed3 F v₀ g) = 1 :=
  Units.ext (by
    show (archEval F w).mapMatrix ((adeleArch (𝓞 F) F).mapMatrix (infMat3 F (archPiMat3 F v₀ g))) = 1
    rw [adeleArch_mapMatrix_infMat3, archEval_mapMatrix_archPiMat3_of_ne F _ _ hw])

private theorem archPlaceComponent3_archEmbed3_mul (w : InfinitePlace F) (s : GL (Fin 3) w.Completion)
    (g : AdelicGL 3 (𝓞 F) F) :
    archPlaceComponent3 F w (archEmbed3 F w s * g) = s * archPlaceComponent3 F w g := by
  rw [map_mul, archPlaceComponent3_archEmbed3_self]

private theorem componentAt3_archEmbed3_mul (v₀ : InfinitePlace F) (p : HeightOneSpectrum (𝓞 F))
    (s : GL (Fin 3) v₀.Completion) (g : AdelicGL 3 (𝓞 F) F) :
    componentAt3 (𝓞 F) F p (archEmbed3 F v₀ s * g) = componentAt3 (𝓞 F) F p g := by
  rw [map_mul, componentAt3_archEmbed3, one_mul]

private theorem componentAt3_globalPointsGL (p : HeightOneSpectrum (𝓞 F)) (γ : GL (Fin 3) F) :
    componentAt3 (𝓞 F) F p (globalPointsGL 3 (𝓞 F) F γ) =
      Matrix.GeneralLinearGroup.map (algebraMap F (p.adicCompletion F)) γ :=
  Units.ext (by ext i j; rfl)

private theorem
    componentAt3_globalPointsGL_mul (p : HeightOneSpectrum (𝓞 F)) (γ : GL (Fin 3) F) (g : AdelicGL 3 (𝓞 F) F) :
    componentAt3 (𝓞 F) F p (globalPointsGL 3 (𝓞 F) F γ * g) =
      Matrix.GeneralLinearGroup.map (algebraMap F (p.adicCompletion F)) γ * componentAt3 (𝓞 F) F p g := by
  rw [map_mul, componentAt3_globalPointsGL]

private theorem archPlaceComponent3_globalPointsGL (w : InfinitePlace F) (γ : GL (Fin 3) F) :
    archPlaceComponent3 F w (globalPointsGL 3 (𝓞 F) F γ) =
      Matrix.GeneralLinearGroup.map (algebraMap F w.Completion) γ :=
  Units.ext (by ext i j; rfl)

private theorem
    archPlaceComponent3_globalPointsGL_mul (w : InfinitePlace F) (γ : GL (Fin 3) F) (g : AdelicGL 3 (𝓞 F) F) :
    archPlaceComponent3 F w (globalPointsGL 3 (𝓞 F) F γ * g) =
      Matrix.GeneralLinearGroup.map (algebraMap F w.Completion) γ * archPlaceComponent3 F w g := by
  rw [map_mul, archPlaceComponent3_globalPointsGL]

open scoped Classical in
private theorem continuous_infMat3_archPiMat3 (v₀ : InfinitePlace F) :
    Continuous fun M : Matrix (Fin 3) (Fin 3) v₀.Completion => infMat3 F (archPiMat3 F v₀ M) := by
  refine continuous_matrix fun i j => ?_
  simp only [infMat3, archPiMat3, Matrix.of_apply]
  refine Continuous.prodMk ?_ continuous_const
  refine continuous_pi fun w => ?_
  by_cases hw : w = v₀
  · subst hw
    simp only [Function.update_self]
    exact continuous_id.matrix_elem i j
  · simp only [Function.update_of_ne hw]
    exact continuous_const

private theorem continuous_archEmbed3 (v₀ : InfinitePlace F) : Continuous (archEmbed3 F v₀) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_infMat3_archPiMat3 v₀).comp Units.continuous_val
  · exact (continuous_infMat3_archPiMat3 v₀).comp Units.continuous_coe_inv

section Rat

private theorem finiteAdele_ext {x y : FiniteAdeleRing (𝓞 ℚ) ℚ}
    (h : ∀ p : HeightOneSpectrum (𝓞 ℚ), finAdeleEval (𝓞 ℚ) ℚ p x = finAdeleEval (𝓞 ℚ) ℚ p y) : x = y := by
  ext p
  simpa only [finAdeleEval_apply] using h p

private theorem adeleFin_mapMatrix_eq_one_of_forall_componentAt3 {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p g = 1) :
    (adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = 1 := by
  refine Matrix.ext fun i j => ?_
  refine finiteAdele_ext fun p => ?_
  have hp0 := congrArg Units.val (hg p)
  have hp : (finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix
      ((adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) = 1 := hp0
  have hp' := congrFun (congrFun hp i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hp'
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [hp']
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]

private theorem archEmbed3_archPlaceComponent3_of_forall_componentAt3 (w : InfinitePlace ℚ) {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p g = 1) :
    archEmbed3 ℚ w (archPlaceComponent3 ℚ w g) = g := by
  refine Units.ext ?_
  rw [coe_archEmbed3]
  refine matrix_eq_of_arch_fin ℚ ?_ ?_
  · rw [adeleArch_mapMatrix_infMat3]
    refine matrix_eq_of_forall_archEval ℚ fun w' => ?_
    rw [Subsingleton.elim w' w, archEval_mapMatrix_archPiMat3_self]
    rfl
  · rw [adeleFin_mapMatrix_infMat3, adeleFin_mapMatrix_eq_one_of_forall_componentAt3 hg]

end Rat

end SiegelArchEmbed

end

set_option autoImplicit false

open Matrix NumberField

noncomputable section

namespace SiegelRealTransport

private def RealReduction : Prop :=
  ∃ c C : ℝ, 0 < c ∧ ∀ M : GL (Fin 3) ℝ,
    ∃ (γ : GL (Fin 3) ℤ) (n t k : GL (Fin 3) ℝ),
      Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) γ * M = n * t * k ∧
      (∀ i j : Fin 3,
        (n : Matrix (Fin 3) (Fin 3) ℝ) i i = 1 ∧ (j < i → (n : Matrix (Fin 3) (Fin 3) ℝ) i j = 0) ∧
        ‖(n : Matrix (Fin 3) (Fin 3) ℝ) i j‖ ≤ C) ∧
      (∀ i j : Fin 3, i ≠ j → (t : Matrix (Fin 3) (Fin 3) ℝ) i j = 0) ∧
      (∀ i : Fin 3, 0 < (t : Matrix (Fin 3) (Fin 3) ℝ) i i) ∧
      c ≤ (t : Matrix (Fin 3) (Fin 3) ℝ) 0 0 / (t : Matrix (Fin 3) (Fin 3) ℝ) 1 1 ∧
      c ≤ (t : Matrix (Fin 3) (Fin 3) ℝ) 1 1 / (t : Matrix (Fin 3) (Fin 3) ℝ) 2 2 ∧
      (k : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (k : Matrix (Fin 3) (Fin 3) ℝ) = 1

section Functor

variable {A B : Type*} [CommRing A] [CommRing B]

private theorem coe_map (f : A →+* B) (g : GL (Fin 3) A) (i j : Fin 3) :
    (Matrix.GeneralLinearGroup.map f g : Matrix (Fin 3) (Fin 3) B) i j = f ((g : Matrix (Fin 3) (Fin 3) A) i j) :=
  rfl

private theorem map_symm_map (e : A ≃+* B) (g : GL (Fin 3) A) :
    Matrix.GeneralLinearGroup.map (e.symm : B →+* A) (Matrix.GeneralLinearGroup.map (e : A →+* B) g) = g :=
  Units.ext (by ext i j; simp)

private theorem map_symm_map_intCast (e : A ≃+* B) (γ : GL (Fin 3) ℤ) :
    Matrix.GeneralLinearGroup.map (e.symm : B →+* A) (Matrix.GeneralLinearGroup.map (Int.castRingHom B) γ) =
      Matrix.GeneralLinearGroup.map (Int.castRingHom A) γ :=
  Units.ext (by ext i j; simp)

private theorem transpose_mul_map_eq_one (f : A →+* B) {k : Matrix (Fin 3) (Fin 3) A} (hk : kᵀ * k = 1) :
    (k.map f)ᵀ * k.map f = 1 := by
  rw [← Matrix.transpose_map, ← Matrix.map_mul, hk, Matrix.map_one f (map_zero f) (map_one f)]

private theorem map_intCast_eq_map_algebraMap {L : Type*} [Field L] [Algebra ℚ L] (γ : GL (Fin 3) ℤ) :
    Matrix.GeneralLinearGroup.map (Int.castRingHom L) γ =
      Matrix.GeneralLinearGroup.map (algebraMap ℚ L) (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) γ) :=
  Units.ext (by ext i j; simp)

end Functor

section RealPlace

variable {K : Type*} [Field K]

private theorem norm_symm_ringEquivRealOfIsReal {w : InfinitePlace K} (hw : w.IsReal) (x : ℝ) :
    ‖(InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _)
    ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm x)
  rw [← h]
  congr 1
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal hw).apply_symm_apply x

private theorem exists_reduced_of_isReal (hRB : RealReduction) :
    ∃ c C : ℝ, 0 < c ∧ ∀ (w : InfinitePlace K) (_hw : w.IsReal) (M : GL (Fin 3) w.Completion),
      ∃ (γ : GL (Fin 3) ℤ) (n t k : GL (Fin 3) w.Completion),
        Matrix.GeneralLinearGroup.map (Int.castRingHom w.Completion) γ * M = n * t * k ∧
        (∀ i j : Fin 3,
          (n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
          (j < i → (n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
          ‖(n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
        (∀ i j : Fin 3, i ≠ j → (t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
        c ≤ ‖(t : Matrix (Fin 3) (Fin 3) w.Completion) 0 0‖ / ‖(t : Matrix (Fin 3) (Fin 3) w.Completion) 1 1‖ ∧
        c ≤ ‖(t : Matrix (Fin 3) (Fin 3) w.Completion) 1 1‖ / ‖(t : Matrix (Fin 3) (Fin 3) w.Completion) 2 2‖ ∧
        (k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ * (k : Matrix (Fin 3) (Fin 3) w.Completion) = 1 := by
  obtain ⟨c, C, hc, hred⟩ := hRB
  refine ⟨c, C, hc, fun w hw M => ?_⟩
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw with he
  obtain ⟨γ, n, t, k, hprod, hn, htd, htpos, hr1, hr2, hk⟩ := hred (Matrix.GeneralLinearGroup.map (e : _ →+* ℝ) M)
  have hnorm : ∀ x : ℝ, ‖e.symm x‖ = ‖x‖ := norm_symm_ringEquivRealOfIsReal hw
  have hnorm' : ∀ x : ℝ, ‖(e.symm : ℝ →+* w.Completion) x‖ = ‖x‖ := hnorm
  refine ⟨γ,
    Matrix.GeneralLinearGroup.map (e.symm : ℝ →+* w.Completion) n,
    Matrix.GeneralLinearGroup.map (e.symm : ℝ →+* w.Completion) t,
    Matrix.GeneralLinearGroup.map (e.symm : ℝ →+* w.Completion) k, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h := congrArg (Matrix.GeneralLinearGroup.map (e.symm : ℝ →+* w.Completion)) hprod
    rwa [map_mul, map_mul, map_mul, map_symm_map, map_symm_map_intCast] at h
  · intro i j
    obtain ⟨h1, h0, hC⟩ := hn i j
    refine ⟨?_, fun hji => ?_, ?_⟩
    · rw [coe_map, h1, map_one]
    · rw [coe_map, h0 hji, map_zero]
    · rw [coe_map, hnorm']
      exact hC
  · intro i j hij
    rw [coe_map, htd i j hij, map_zero]
  · rw [coe_map, coe_map, hnorm', hnorm', Real.norm_of_nonneg (htpos 0).le, Real.norm_of_nonneg (htpos 1).le]
    exact hr1
  · rw [coe_map, coe_map, hnorm', hnorm', Real.norm_of_nonneg (htpos 1).le, Real.norm_of_nonneg (htpos 2).le]
    exact hr2
  · exact transpose_mul_map_eq_one (e.symm : ℝ →+* w.Completion) hk

end RealPlace

private theorem isReal_of_rat (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

private theorem exists_reduced_rat (hRB : RealReduction) :
    ∃ c C : ℝ, 0 < c ∧ ∀ (w : InfinitePlace ℚ) (M : GL (Fin 3) w.Completion),
      ∃ (γ : GL (Fin 3) ℤ) (n t k : GL (Fin 3) w.Completion),
        Matrix.GeneralLinearGroup.map (Int.castRingHom w.Completion) γ * M = n * t * k ∧
        (∀ i j : Fin 3,
          (n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
          (j < i → (n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
          ‖(n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
        (∀ i j : Fin 3, i ≠ j → (t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
        c ≤ ‖(t : Matrix (Fin 3) (Fin 3) w.Completion) 0 0‖ / ‖(t : Matrix (Fin 3) (Fin 3) w.Completion) 1 1‖ ∧
        c ≤ ‖(t : Matrix (Fin 3) (Fin 3) w.Completion) 1 1‖ / ‖(t : Matrix (Fin 3) (Fin 3) w.Completion) 2 2‖ ∧
        (k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ * (k : Matrix (Fin 3) (Fin 3) w.Completion) = 1 := by
  obtain ⟨c, C, hc, h⟩ := exists_reduced_of_isReal (K := ℚ) hRB
  exact ⟨c, C, hc, fun w M => h w (isReal_of_rat w) M⟩

end SiegelRealTransport

end

set_option autoImplicit false

open Matrix

noncomputable section

namespace SiegelGram

variable {L : Type*} [Field L]

private theorem eq_diagonal_of_offDiag_eq_zero (M : Matrix (Fin 3) (Fin 3) L) (hM : ∀ i j : Fin 3, i ≠ j → M i j = 0) :
    M = Matrix.diagonal (fun i => M i i) := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ h, hM i j h]

end SiegelGram

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.exists_forall_componentAt3_mul_mem_localMaximalCompact3 CubicInduction.exists_mul_eq_unipotent_mul_diagonal_mul_orthogonal_real"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂ archPlaceComponent3 AdelicGL globalPointsGL localMaximalCompact3 mem_localMaximalCompact3_iff componentAt3 exists_forall_componentAt3_mul_mem_localMaximalCompact3 exists_mul_eq_unipotent_mul_diagonal_mul_orthogonal_real"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable {L : Type*} [NormedField L]

private theorem lastRowEucl_of_coe_eq_diagonal (t : GL (Fin 3) L) (d : Fin 3 → L)
    (ht : (t : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal d) :
    lastRowEucl t = ‖d 2‖ := by
  simp only [lastRowEucl, ht, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ (show (2 : Fin 3) ≠ 0 by decide),
    Matrix.diagonal_apply_ne _ (show (2 : Fin 3) ≠ 1 by decide), norm_zero]
  rw [show (0 : ℝ) ^ 2 + 0 ^ 2 + ‖d 2‖ ^ 2 = ‖d 2‖ ^ 2 by ring]
  exact Real.sqrt_sq (norm_nonneg _)

private theorem minorEucl_of_coe_eq_diagonal (t : GL (Fin 3) L) (d : Fin 3 → L)
    (ht : (t : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal d) :
    minorEucl t = ‖d 1 * d 2‖ := by
  simp only [minorEucl, bottomMinor, ht, Matrix.diagonal_apply]
  simp only [show ((1 : Fin 3) = 0) = False by decide, show ((1 : Fin 3) = 2) = False by decide,
    show ((2 : Fin 3) = 0) = False by decide, show ((2 : Fin 3) = 1) = False by decide, if_false, if_true,
    mul_zero, zero_mul, sub_zero, norm_zero]
  rw [show (0 : ℝ) ^ 2 + 0 ^ 2 + ‖d 1 * d 2‖ ^ 2 = ‖d 1 * d 2‖ ^ 2 by ring]
  exact Real.sqrt_sq (norm_nonneg _)

private theorem detSize_of_coe_eq_diagonal (t : GL (Fin 3) L) (d : Fin 3 → L)
    (ht : (t : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal d) :
    detSize t = ‖d 0 * d 1 * d 2‖ := by
  simp only [detSize, ht, Matrix.det_diagonal, Fin.prod_univ_three]

private theorem rootSizes_of_coe_eq_diagonal (t : GL (Fin 3) L) (d : Fin 3 → L)
    (ht : (t : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal d) (h1 : d 1 ≠ 0) (h2 : d 2 ≠ 0) :
    detSize t * lastRowEucl t / minorEucl t ^ 2 = ‖d 0‖ / ‖d 1‖ ∧
      minorEucl t / lastRowEucl t ^ 2 = ‖d 1‖ / ‖d 2‖ := by
  rw [detSize_of_coe_eq_diagonal t d ht, lastRowEucl_of_coe_eq_diagonal t d ht, minorEucl_of_coe_eq_diagonal t d ht]
  have n1 : ‖d 1‖ ≠ 0 := norm_ne_zero_iff.mpr h1
  have n2 : ‖d 2‖ ≠ 0 := norm_ne_zero_iff.mpr h2
  simp only [norm_mul]
  constructor
  · field_simp
  · field_simp

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_compact.LanglandsTunnell.CubicInduction"

noncomputable section

namespace SiegelCoveringThree

private def FiniteCovering : Prop :=
  ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ γ : GL (Fin 3) ℚ, ∀ p : HeightOneSpectrum (𝓞 ℚ),
    componentAt3 (𝓞 ℚ) ℚ p (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p

private def IntegralInCompact : Prop :=
  ∀ (γ : GL (Fin 3) ℤ) (p : HeightOneSpectrum (𝓞 ℚ)),
    componentAt3 (𝓞 ℚ) ℚ p (globalPointsGL 3 (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) γ)) ∈
      localMaximalCompact3 (𝓞 ℚ) ℚ p

private theorem diag_ne_zero {L : Type*} [Field L] (t : GL (Fin 3) L)
    (htd : ∀ i j : Fin 3, i ≠ j → (t : Matrix (Fin 3) (Fin 3) L) i j = 0) (i : Fin 3) :
    (t : Matrix (Fin 3) (Fin 3) L) i i ≠ 0 := by
  have hdiag := SiegelGram.eq_diagonal_of_offDiag_eq_zero (t : Matrix (Fin 3) (Fin 3) L) htd
  have hdet : (t : Matrix (Fin 3) (Fin 3) L).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det t).ne_zero
  rw [hdiag, Matrix.det_diagonal] at hdet
  exact (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ i)

private theorem covering (hRA : FiniteCovering) (hRB : SiegelRealTransport.RealReduction) (hB4 : IntegralInCompact) :
    ∃ c C : ℝ, 0 < c ∧ ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ∃ (γ : GL (Fin 3) ℚ) (n t k : AdelicGL 3 (𝓞 ℚ) ℚ),
        globalPointsGL 3 (𝓞 ℚ) ℚ γ * g = n * t * k ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
        ∀ w : InfinitePlace ℚ,
          (∀ i j : Fin 3,
            (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
            (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
          (∀ i j : Fin 3, i ≠ j →
            (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
          c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
          (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
              (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1 := by
  obtain ⟨c, C, hc, hred⟩ := SiegelRealTransport.exists_reduced_rat hRB
  refine ⟨c, C, hc, fun g => ?_⟩

  obtain ⟨γA, hγA⟩ := hRA g
  set g₁ : AdelicGL 3 (𝓞 ℚ) ℚ := globalPointsGL 3 (𝓞 ℚ) ℚ γA * g

  obtain ⟨γz, n, t, k, hprod, hn, htd, hr1, hr2, hk⟩ :=
    hred Rat.infinitePlace (archPlaceComponent3 ℚ Rat.infinitePlace g₁)
  set γQ : GL (Fin 3) ℚ := Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) γz with hγQ
  set nE : AdelicGL 3 (𝓞 ℚ) ℚ := SiegelArchEmbed.archEmbed3 ℚ Rat.infinitePlace n with hnE
  set tE : AdelicGL 3 (𝓞 ℚ) ℚ := SiegelArchEmbed.archEmbed3 ℚ Rat.infinitePlace t with htE
  set kA : AdelicGL 3 (𝓞 ℚ) ℚ := (nE * tE)⁻¹ * (globalPointsGL 3 (𝓞 ℚ) ℚ (γQ * γA) * g) with hkA
  have hsplit : globalPointsGL 3 (𝓞 ℚ) ℚ (γQ * γA) * g = globalPointsGL 3 (𝓞 ℚ) ℚ γQ * g₁ := by
    rw [map_mul, mul_assoc]
  have hnw : archPlaceComponent3 ℚ Rat.infinitePlace nE = n :=
    SiegelArchEmbed.archPlaceComponent3_archEmbed3_self Rat.infinitePlace n
  have htw : archPlaceComponent3 ℚ Rat.infinitePlace tE = t :=
    SiegelArchEmbed.archPlaceComponent3_archEmbed3_self Rat.infinitePlace t
  have hntw : archPlaceComponent3 ℚ Rat.infinitePlace (nE * tE) = n * t := by
    rw [map_mul, hnw, htw]
  have hntp : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p (nE * tE) = 1 := fun p => by
    rw [map_mul, hnE, htE, SiegelArchEmbed.componentAt3_archEmbed3, SiegelArchEmbed.componentAt3_archEmbed3,
      mul_one]

  have harchk : archPlaceComponent3 ℚ Rat.infinitePlace kA = k := by
    rw [hkA, hsplit, map_mul, map_inv, hntw, SiegelArchEmbed.archPlaceComponent3_globalPointsGL_mul, hγQ,
      ← SiegelRealTransport.map_intCast_eq_map_algebraMap, hprod, inv_mul_cancel_left]
  refine ⟨γQ * γA, nE, tE, kA, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hkA, mul_inv_cancel_left]
  · intro p
    rw [hnE]
    exact SiegelArchEmbed.componentAt3_archEmbed3 Rat.infinitePlace p n
  · intro p
    rw [htE]
    exact SiegelArchEmbed.componentAt3_archEmbed3 Rat.infinitePlace p t
  · intro p
    rw [hkA, hsplit, map_mul, map_inv, hntp p, inv_one, one_mul, map_mul]
    exact Subgroup.mul_mem _ (hB4 γz p) (hγA p)
  · intro w
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    have hd1 := diag_ne_zero t htd 1
    have hd2 := diag_ne_zero t htd 2

    have hdiag := SiegelGram.eq_diagonal_of_offDiag_eq_zero _ htd
    have hroots := rootSizes_of_coe_eq_diagonal t _ hdiag hd1 hd2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hnw]
      exact hn
    · rw [htw]
      exact htd
    · unfold archRoot₁
      rw [htw, hroots.1]
      exact hr1
    · unfold archRoot₂
      rw [htw, hroots.2]
      exact hr2
    · rw [harchk]
      exact hk

end SiegelCoveringThree

end

namespace RationalIntegralPoints

p2m_open "IsDedekindDomain NumberField Matrix LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_compact.LanglandsTunnell.CubicInduction"

private theorem componentAt3_globalPointsGL_apply (v : HeightOneSpectrum (𝓞 ℚ)) (γ : GL (Fin 3) ℚ) (i j : Fin 3) :
    (componentAt3 (𝓞 ℚ) ℚ v (globalPointsGL 3 (𝓞 ℚ) ℚ γ) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j =
      FinitePlace.embedding v ((γ : Matrix (Fin 3) (Fin 3) ℚ) i j) :=
  rfl

private theorem valued_intCast_le_one (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℤ) :
    Valued.v (FinitePlace.embedding v (n : ℚ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
  rw [FinitePlace.embedding_apply, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ) by rw [map_intCast]]
  exact v.valuation_le_one _

private theorem componentAt3_globalPointsGL_map_intCast_mem (γ : GL (Fin 3) ℤ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ v (globalPointsGL 3 (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) γ)) ∈
      localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [componentAt3_globalPointsGL_apply, Matrix.GeneralLinearGroup.map_apply]
    exact valued_intCast_le_one v _
  · rw [← map_inv (componentAt3 (𝓞 ℚ) ℚ v), ← map_inv (globalPointsGL 3 (𝓞 ℚ) ℚ),
      ← map_inv (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ)), componentAt3_globalPointsGL_apply,
      Matrix.GeneralLinearGroup.map_apply]
    exact valued_intCast_le_one v _

end RationalIntegralPoints

open Matrix IsDedekindDomain NumberField

theorem solution :
    ∃ c C : ℝ, 0 < c ∧ ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ∃ (γ : GL (Fin 3) ℚ) (n t k : AdelicGL 3 (𝓞 ℚ) ℚ),
        globalPointsGL 3 (𝓞 ℚ) ℚ γ * g = n * t * k ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
        ∀ w : InfinitePlace ℚ,
          (∀ i j : Fin 3,
            (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
            (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
          (∀ i j : Fin 3, i ≠ j →
            (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
          c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
          (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
              (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1 :=
  SiegelCoveringThree.covering
    LanglandsTunnell.CubicInduction.exists_forall_componentAt3_mul_mem_localMaximalCompact3
    LanglandsTunnell.CubicInduction.exists_mul_eq_unipotent_mul_diagonal_mul_orthogonal_real
    RationalIntegralPoints.componentAt3_globalPointsGL_map_intCast_mem

end S_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_compact
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_compact (solution)
