-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.localPackage_psiLocal_inv_comp_mul_diagonal_of_localPackage_psiLocal_of_gauge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/9d70bac9-888a-5c26-bfec-20cbc1d046f9

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalWhittakerDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_localPackage_psiLocal_inv_comp_mul_diagonal_of_localPackage_psiLocal_of_gauge

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

noncomputable section

namespace SFδ

variable (v : HeightOneSpectrum (𝓞 ℚ))
local notation "Kv" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "M3" => (Matrix (Fin 3) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "G3" => (LocalGL3 v)

def d : LocalGL3 v :=
  iotaGL (Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : (v.adicCompletion ℚ)ˣ) * diagOne (-1 : (v.adicCompletion ℚ)ˣ))

theorem coe_d : ((d v : G3) : M3) = !![1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  simp only [d, coe_iotaGL, Units.val_mul, embedMat2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagOne, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.diagonal]

theorem d_mul_d : d v * d v = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_d, Units.val_one, Matrix.mul_fin_three]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

theorem d_inv : (d v)⁻¹ = d v := inv_eq_of_mul_eq_one_right (d_mul_d v)

theorem coe_scalar (t : (v.adicCompletion ℚ)ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 3) t : G3) : M3) = !![(t : Kv), 0, 0; 0, (t : Kv), 0; 0, 0, (t : Kv)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal]

theorem coe_transposeInv3 (g : G3) : ((transposeInv3 g : G3) : M3) = (((g⁻¹ : G3) : M3)).transpose := rfl

theorem coe_iota_diagUnit (a : (v.adicCompletion ℚ)ˣ) :
    ((iotaGL (diagUnitGL2 a) : G3) : M3) = !![(a : Kv), 0, 0; 0, 1, 0; 0, 0, 1] := by
  rw [coe_iotaGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, diagUnitGL2]

theorem d_upper (x y z : Kv) : d v * upperUnipotent3 x y z * d v = upperUnipotent3 (-x) (-y) z := by
  apply Units.ext
  simp only [Units.val_mul, coe_d, upperUnipotent3_coe, Matrix.mul_fin_three]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem d_iota (a : (v.adicCompletion ℚ)ˣ) : d v * iotaGL (diagUnitGL2 a) = iotaGL (diagUnitGL2 a) * d v := by
  apply Units.ext
  simp only [Units.val_mul, coe_d, coe_iota_diagUnit, Matrix.mul_fin_three]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem d_conj_iota_mul (a : (v.adicCompletion ℚ)ˣ) (g : G3) :
    d v * (iotaGL (diagUnitGL2 a) * g) * d v = iotaGL (diagUnitGL2 a) * (d v * g * d v) := by
  have h := d_iota v a
  calc d v * (iotaGL (diagUnitGL2 a) * g) * d v = (d v * iotaGL (diagUnitGL2 a)) * g * d v := by
        simp only [mul_assoc]
    _ = (iotaGL (diagUnitGL2 a) * d v) * g * d v := by rw [h]
    _ = iotaGL (diagUnitGL2 a) * (d v * g * d v) := by simp only [mul_assoc]

theorem scalar_comm (t : (v.adicCompletion ℚ)ˣ) (g : G3) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) t * g = g * Matrix.GeneralLinearGroup.scalar (Fin 3) t := by
  apply Units.ext
  simp only [Units.val_mul]
  have : ((Matrix.GeneralLinearGroup.scalar (Fin 3) t : G3) : M3) = (t : Kv) • (1 : M3) := by
    rw [coe_scalar]; ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [this, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

theorem d_longWeyl : d v * longWeyl3 = longWeyl3 * d v := by
  apply Units.ext
  simp only [Units.val_mul, coe_d, longWeyl3_coe, Matrix.mul_fin_three]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem transposeInv3_mul (g h : G3) : transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  apply Units.ext
  rw [Units.val_mul, coe_transposeInv3, coe_transposeInv3, coe_transposeInv3, mul_inv_rev, Units.val_mul,
    Matrix.transpose_mul]

theorem transposeInv3_d : transposeInv3 (d v) = d v := by
  apply Units.ext
  rw [coe_transposeInv3, d_inv, coe_d]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem transposeInv3_scalar (t : (v.adicCompletion ℚ)ˣ) :
    transposeInv3 (Matrix.GeneralLinearGroup.scalar (Fin 3) t) = Matrix.GeneralLinearGroup.scalar (Fin 3) t⁻¹ := by
  apply Units.ext
  rw [coe_transposeInv3, ← map_inv, coe_scalar]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

theorem d_key (a : (v.adicCompletion ℚ)ˣ) (x : Kv) :
    d v * iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * weylPrime3 * d v =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (-1 : (v.adicCompletion ℚ)ˣ) *
        iotaGL (diagUnitGL2 ((-1 : (v.adicCompletion ℚ)ˣ) * a)) * lowerUnipotent21 x * weylPrime3 := by
  apply Units.ext
  simp only [Units.val_mul, coe_d, coe_iota_diagUnit, lowerUnipotent21_coe, weylPrime3_coe, coe_scalar,
    Matrix.mul_fin_three, Units.val_neg, Units.val_one, Units.val_mul]
  ext i j; fin_cases i <;> fin_cases j <;> simp

private def _root_.SFδ.conj (W : G3 → ℂ) : G3 → ℂ := fun g => W (d v * g * d v)

p2m_export "SFδ" "conj"
theorem conj_apply (W : G3 → ℂ) (g : G3) : conj v W g = W (d v * g * d v) := rfl

theorem dual_conj (W : G3 → ℂ) : dualWhittakerFn3 (conj v W) = conj v (dualWhittakerFn3 W) := by
  funext h
  simp only [dualWhittakerFn3_apply, conj_apply, transposeInv3_mul, transposeInv3_d, ← mul_assoc, d_longWeyl]

theorem dual_scalar (W : G3 → ℂ) (ω : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : G3), W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W h)
    (t : (v.adicCompletion ℚ)ˣ) (h : G3) :
    dualWhittakerFn3 W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t⁻¹ : ℂˣ) : ℂ) * dualWhittakerFn3 W h := by
  simp only [dualWhittakerFn3_apply, transposeInv3_mul, transposeInv3_scalar, ← mul_assoc]
  rw [← scalar_comm, mul_assoc, hω]

theorem dual_conj_integrand (W : G3 → ℂ) (ω : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : G3), W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W h)
    (a : (v.adicCompletion ℚ)ˣ) (x : Kv) (g : G3) :
    dualWhittakerFn3 (conj v W) (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 g)) =
      ((ω (-1 : (v.adicCompletion ℚ)ˣ)⁻¹ : ℂˣ) : ℂ) *
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 ((-1 : (v.adicCompletion ℚ)ˣ) * a)) * lowerUnipotent21 x *
          (weylPrime3 * transposeInv3 (d v * g * d v))) := by
  rw [dual_conj, conj_apply]
  have : d v * (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 g)) * d v =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (-1 : (v.adicCompletion ℚ)ˣ) *
        (iotaGL (diagUnitGL2 ((-1 : (v.adicCompletion ℚ)ˣ) * a)) * lowerUnipotent21 x *
          (weylPrime3 * transposeInv3 (d v * g * d v))) := by
    rw [transposeInv3_mul, transposeInv3_mul, transposeInv3_d]
    have hk := d_key v a x
    calc d v * (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 g)) * d v
        = (d v * iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * weylPrime3 * d v) *
            (d v * transposeInv3 g * d v) := by
          simp only [mul_assoc, ← mul_assoc (d v) (d v), d_mul_d, one_mul]
      _ = _ := by rw [hk]; simp only [mul_assoc]
  rw [this, dual_scalar v W ω hω]

section Zeta

variable [MeasurableSpace (v.adicCompletion ℚ)] [BorelSpace (v.adicCompletion ℚ)]

scoped instance secondCountable_units : SecondCountableTopology (HeightOneSpectrum.adicCompletion ℚ v)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

theorem borelSpace_units : BorelSpace (HeightOneSpectrum.adicCompletion ℚ v)ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace (HeightOneSpectrum.adicCompletion ℚ v)ˣ) =
      TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := Kv)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace Kv) = borel (HeightOneSpectrum.adicCompletion ℚ v)ˣ
  rw [BorelSpace.measurable_eq (α := Kv), ← borel_comap, ← hind]

theorem localZeta30_conj (μ : Measure (v.adicCompletion ℚ)ˣ) (W : G3 → ℂ) (s : ℂ) (g : G3) :
    localZeta30 v μ (conj v W) 1 s g = localZeta30 v μ W 1 s (d v * g * d v) := by
  unfold localZeta30
  simp_rw [conj_apply, d_conj_iota_mul]

theorem isLocalZeta30ConvergentAbove_conj (μ : Measure (v.adicCompletion ℚ)ˣ) (W : G3 → ℂ) (g : G3) (σ : ℝ)
    (h : IsLocalZeta30ConvergentAbove v μ W 1 (d v * g * d v) σ) :
    IsLocalZeta30ConvergentAbove v μ (conj v W) 1 g σ := by
  intro s hs
  have := h s hs
  refine (integrable_congr (Filter.Eventually.of_forall fun a => ?_)).mp this
  simp only [conj_apply, d_conj_iota_mul]

variable (μ : Measure (v.adicCompletion ℚ)ˣ) [μ.IsMulLeftInvariant] (ν : Measure (v.adicCompletion ℚ))

theorem measurableMul_units : MeasurableMul (HeightOneSpectrum.adicCompletion ℚ v)ˣ := by
  haveI := borelSpace_units v
  infer_instance

theorem localZetaDual31_conj [SFinite μ] [SFinite ν] (W : G3 → ℂ) (ω : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : G3), W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W h)
    (s : ℂ) (g : G3) :
    localZetaDual31 v μ ν (conj v W) 1 s g =
      ((ω (-1 : (v.adicCompletion ℚ)ˣ)⁻¹ : ℂˣ) : ℂ) * localZetaDual31 v μ ν W 1 s (d v * g * d v) := by
  haveI := measurableMul_units v
  unfold localZetaDual31 localZeta31
  simp_rw [dual_conj_integrand v W ω hω]
  rw [← integral_mul_left_eq_self _ (-1 : (v.adicCompletion ℚ)ˣ), ← integral_const_mul]
  congr 1
  funext a
  have h1 : (-1 : (v.adicCompletion ℚ)ˣ) * ((-1 : (v.adicCompletion ℚ)ˣ) * a) = a := by
    rw [← mul_assoc, neg_mul_neg, one_mul, one_mul]
  have hmod : (modulus (((-1 : (v.adicCompletion ℚ)ˣ) * a : (v.adicCompletion ℚ)ˣ) : Kv) : ℝ) =
      (modulus ((a : (v.adicCompletion ℚ)ˣ) : Kv) : ℝ) := by
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v,
      LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v, Units.val_mul, Units.val_neg, Units.val_one,
      neg_one_mul, nnnorm_neg]
  rw [h1, hmod, integral_const_mul]
  simp only [MonoidHom.inv_apply, MonoidHom.one_apply, inv_one]
  ring

theorem isLocalZeta31ConvergentAbove_conj [SFinite μ] [SFinite ν] (W : G3 → ℂ) (ω : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : G3), W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W h)
    (g : G3) (σ : ℝ)
    (h : IsLocalZeta31ConvergentAbove v μ ν (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 (d v * g * d v)) σ) :
    IsLocalZeta31ConvergentAbove v μ ν (dualWhittakerFn3 (conj v W)) 1 (weylPrime3 * transposeInv3 g) σ := by
  haveI := measurableMul_units v
  intro s hs
  have hint := h s hs
  have hT : MeasurePreserving (fun p : (v.adicCompletion ℚ)ˣ × Kv => ((-1 : (v.adicCompletion ℚ)ˣ) * p.1, p.2))
      (μ.prod ν) (μ.prod ν) :=
    (measurePreserving_mul_left μ (-1 : (v.adicCompletion ℚ)ˣ)).prod (MeasurePreserving.id ν)
  have h2 := (hT.integrable_comp hint.aestronglyMeasurable).mpr hint
  refine ((h2.const_mul ((ω (-1 : (v.adicCompletion ℚ)ˣ)⁻¹ : ℂˣ) : ℂ)).congr ?_)
  refine Filter.Eventually.of_forall fun p => ?_
  simp only [Function.comp_apply, dual_conj_integrand v W ω hω, MonoidHom.one_apply, inv_one]
  have hmod : (modulus (((-1 : (v.adicCompletion ℚ)ˣ) * p.1 : (v.adicCompletion ℚ)ˣ) : Kv) : ℝ) =
      (modulus ((p.1 : (v.adicCompletion ℚ)ˣ) : Kv) : ℝ) := by
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v,
      LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v, Units.val_mul, Units.val_neg, Units.val_one,
      neg_one_mul, nnnorm_neg]
  rw [hmod]
  ring

end Zeta

theorem conj_conj (F : G3 → ℂ) : conj v (conj v F) = F := by
  funext g
  simp only [conj_apply]
  congr 1
  calc d v * (d v * g * d v) * d v = (d v * d v) * g * (d v * d v) := by simp only [mul_assoc]
    _ = g := by rw [d_mul_d, one_mul, mul_one]

theorem conj_injective : Function.Injective (conj v) := fun F G h => by
  have := congrArg (conj v) h
  rwa [conj_conj, conj_conj] at this

def conjₗ : (G3 → ℂ) →ₗ[ℂ] (G3 → ℂ) where
  toFun := conj v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem conjₗ_apply (F : G3 → ℂ) : conjₗ v F = conj v F := rfl

theorem conj_translate (h : G3) (F : G3 → ℂ) :
    conj v (gl3AmbientRightTranslate (R := ℂ) h F) = gl3AmbientRightTranslate (R := ℂ) (d v * h * d v) (conj v F) := by
  funext g
  simp only [conj_apply, gl3AmbientRightTranslate_apply]
  congr 1
  calc d v * g * d v * h = d v * g * d v * h * (d v * d v) := by rw [d_mul_d, mul_one]
    _ = d v * (g * (d v * h * d v)) * d v := by simp only [mul_assoc]

theorem map_conj_cyclic (F : G3 → ℂ) : (gl3CyclicSubspace F).map (conjₗ v) = gl3CyclicSubspace (conj v F) := by
  unfold gl3CyclicSubspace
  rw [Submodule.map_span]
  congr 1
  ext G
  simp only [Set.mem_image, Set.mem_range, conjₗ_apply]
  constructor
  · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
    exact ⟨d v * h * d v, (conj_translate v h F).symm⟩
  · rintro ⟨h, rfl⟩
    refine ⟨gl3AmbientRightTranslate (R := ℂ) (d v * h * d v) F, ⟨d v * h * d v, rfl⟩, ?_⟩
    rw [conj_translate]
    have hh : d v * (d v * h * d v) * d v = h := by
      calc d v * (d v * h * d v) * d v = (d v * d v) * h * (d v * d v) := by simp only [mul_assoc]
        _ = h := by rw [d_mul_d, one_mul, mul_one]
    rw [hh]

theorem conj_mem_cyclic {F G : G3 → ℂ} (hG : G ∈ gl3CyclicSubspace F) : conj v G ∈ gl3CyclicSubspace (conj v F) := by
  rw [← map_conj_cyclic]
  exact ⟨G, hG, rfl⟩

theorem mem_cyclic_of_conj {F G : G3 → ℂ} (hG : conj v G ∈ gl3CyclicSubspace (conj v F)) : G ∈ gl3CyclicSubspace F := by
  have := conj_mem_cyclic v hG
  rwa [conj_conj, conj_conj] at this

def conjRes (F : G3 → ℂ) : gl3CyclicSubspace F →ₗ[ℂ] gl3CyclicSubspace (conj v F) :=
  (conjₗ v).restrict fun G hG => conj_mem_cyclic v hG

theorem conjRes_apply_coe (F : G3 → ℂ) (f : gl3CyclicSubspace F) : ((conjRes v F f : gl3CyclicSubspace (conj v F)) : G3 → ℂ) = conj v f := rfl

theorem conjRes_surjective (F : G3 → ℂ) : Function.Surjective (conjRes v F) := by
  intro f
  refine ⟨⟨conj v f, mem_cyclic_of_conj v (by rw [conj_conj]; exact f.2)⟩, ?_⟩
  apply Subtype.ext
  simp [conjRes_apply_coe, conj_conj]

theorem conjRes_rep (F : G3 → ℂ) (h : G3) (f : gl3CyclicSubspace F) :
    conjRes v F (gl3CyclicRep F h f) = gl3CyclicRep (conj v F) (d v * h * d v) (conjRes v F f) := by
  apply Subtype.ext
  show conj v (fun g => (f : G3 → ℂ) (g * h)) = fun g => conj v f (g * (d v * h * d v))
  exact conj_translate v h f

theorem hasWhittakerMultOne_conj (ψ : AddChar Kv ℂ) (W : G3 → ℂ) (hmult : HasWhittakerMultOne ψ W) :
    HasWhittakerMultOne ψ⁻¹ (conj v W) := by
  unfold HasWhittakerMultOne GL3WhittakerUniquenessStatement at hmult ⊢

  let Φ : gl3WhittakerFunctionalSpace (gl3CyclicRep (conj v W)) ψ⁻¹ →ₗ[ℂ]
      gl3WhittakerFunctionalSpace (gl3CyclicRep W) ψ :=
    { toFun := fun L => ⟨(L : gl3CyclicSubspace (conj v W) →ₗ[ℂ] ℂ) ∘ₗ conjRes v W, by
        intro x y z w
        show (L : gl3CyclicSubspace (conj v W) →ₗ[ℂ] ℂ) (conjRes v W (gl3CyclicRep W (upperUnipotent3 x y z) w)) =
          ψ (x + y) * (L : gl3CyclicSubspace (conj v W) →ₗ[ℂ] ℂ) (conjRes v W w)
        rw [conjRes_rep, d_upper, L.2 (-x) (-y) z, AddChar.inv_apply]
        congr 2; ring⟩
      map_add' := fun L₁ L₂ => by
        apply Subtype.ext
        show ((L₁ + L₂ : gl3WhittakerFunctionalSpace (gl3CyclicRep (conj v W)) ψ⁻¹) :
            gl3CyclicSubspace (conj v W) →ₗ[ℂ] ℂ) ∘ₗ conjRes v W =
          (L₁ : gl3CyclicSubspace (conj v W) →ₗ[ℂ] ℂ) ∘ₗ conjRes v W +
            (L₂ : gl3CyclicSubspace (conj v W) →ₗ[ℂ] ℂ) ∘ₗ conjRes v W
        rw [Submodule.coe_add, LinearMap.add_comp]
      map_smul' := fun c L => by
        apply Subtype.ext
        show ((c • L : gl3WhittakerFunctionalSpace (gl3CyclicRep (conj v W)) ψ⁻¹) :
            gl3CyclicSubspace (conj v W) →ₗ[ℂ] ℂ) ∘ₗ conjRes v W =
          c • ((L : gl3CyclicSubspace (conj v W) →ₗ[ℂ] ℂ) ∘ₗ conjRes v W)
        rw [Submodule.coe_smul, LinearMap.smul_comp] }
  have hΦ : Function.Injective Φ := by
    intro L₁ L₂ h
    apply Subtype.ext
    apply LinearMap.ext
    intro f
    obtain ⟨f', rfl⟩ := conjRes_surjective v W f
    have := congrArg (fun (M : gl3WhittakerFunctionalSpace (gl3CyclicRep W) ψ) => (M : gl3CyclicSubspace W →ₗ[ℂ] ℂ) f') h
    exact this
  exact (LinearMap.rank_le_of_injective Φ hΦ).trans hmult

theorem coe_d_diag : ((d v : G3) : M3) = Matrix.diagonal ![1, -1, 1] := by
  rw [coe_d]; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem conj_entry (k : G3) (i j : Fin 3) :
    ((d v * k * d v : G3) : M3) i j = ![1, -1, 1] i * (k : M3) i j * ![1, -1, 1] j := by
  rw [Units.val_mul, Units.val_mul, coe_d_diag, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem v_conj_entry (k : G3) (i j : Fin 3) :
    Valued.v (((d v * k * d v : G3) : M3) i j) = Valued.v ((k : M3) i j) := by
  rw [conj_entry]
  fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg]

theorem conj_inv (k : G3) : (d v * k * d v)⁻¹ = d v * k⁻¹ * d v := by
  rw [mul_inv_rev, mul_inv_rev, d_inv, mul_assoc]

theorem conj_mem_localMaximalCompact3 {k : G3} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    d v * k * d v ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  obtain ⟨h1, h2⟩ := hk
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [v_conj_entry]; exact h1 i j
  · rw [conj_inv, v_conj_entry]; exact h2 i j

theorem conj_mem_congruenceK1 (c : ℕ) {k : G3} (hk : k ∈ congruenceK1 (𝓞 ℚ) ℚ v c) :
    d v * k * d v ∈ congruenceK1 (𝓞 ℚ) ℚ v c := by
  rw [mem_congruenceK1_iff] at hk ⊢
  obtain ⟨h0, h1, h2, h3⟩ := hk
  refine ⟨conj_mem_localMaximalCompact3 v h0, ?_, ?_, ?_⟩
  · rw [v_conj_entry]; exact h1
  · rw [v_conj_entry]; exact h2
  · rw [conj_entry]; simpa using h3

theorem d_mem_congruenceK1 (c : ℕ) : d v ∈ congruenceK1 (𝓞 ℚ) ℚ v c := by
  rw [mem_congruenceK1_iff]
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, ?_, ?_, ?_⟩
  · rw [coe_d]; fin_cases i <;> fin_cases j <;> simp
  · rw [d_inv, coe_d]; fin_cases i <;> fin_cases j <;> simp
  · rw [coe_d]; simp
  · rw [coe_d]; simp
  · rw [coe_d]; simp

theorem coe_iota_diagUnits2 (a b : (v.adicCompletion ℚ)ˣ) :
    ((iotaGL (diagUnits2 a b) : G3) : M3) = !![(a : Kv), 0, 0; 0, (b : Kv), 0; 0, 0, 1] := by
  rw [coe_iotaGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, diagUnits2]

theorem d_twoRow (k₁ k₂ : ℕ) : d v * twoRowPointLocal v k₁ k₂ = twoRowPointLocal v k₁ k₂ * d v := by
  unfold twoRowPointLocal
  apply Units.ext
  simp only [Units.val_mul, coe_d, coe_iota_diagUnits2, Matrix.mul_fin_three]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem d_iotaTorus (n : ℕ) : d v * iotaTorusLocal v n = iotaTorusLocal v n * d v := by
  unfold iotaTorusLocal
  rw [diagHom_apply]
  exact d_iota v _

theorem lastRowSup_conj (h : G3) : lastRowSup (d v * h * d v) = lastRowSup h := by
  unfold lastRowSup
  simp only [conj_entry]
  simp

theorem bottomMinor_conj (h : G3) (j j' : Fin 3) :
    ‖bottomMinor (d v * h * d v) j j'‖ = ‖bottomMinor h j j'‖ := by
  unfold bottomMinor
  simp only [conj_entry]
  fin_cases j <;> fin_cases j' <;> simp
  all_goals (rw [← norm_neg]; congr 1; ring)

theorem minorSup_conj (h : G3) : minorSup (d v * h * d v) = minorSup h := by
  unfold minorSup
  rw [bottomMinor_conj, bottomMinor_conj, bottomMinor_conj]

theorem detSize_conj (h : G3) : detSize (d v * h * d v) = detSize h := by
  unfold detSize
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, coe_d]
  have : (!![(1 : Kv), 0, 0; 0, -1, 0; 0, 0, 1] : M3).det = -1 := by
    rw [Matrix.det_fin_three]; simp
  rw [this]; simp

end SFδ
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localPackage_psiLocal_inv_comp_mul_diagonal_of_localPackage_psiLocal_of_gauge.SFδ"

open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.CubicInduction

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ : ψv = NumberField.StandardAddChar.psiLocal ℚ v)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) (h1 : W 1 = 1)
    (hmult : HasWhittakerMultOne ψv W)
    (hirr : ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2) * (LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2)) ^ t))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hωu : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (E Ed : Polynomial ℂ) (ε : ℂ) (hε : ε ≠ 0) (ℓ : ℕ)
    (h31 : ∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g =
            (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s))) :
    ∃ (W₀ : LocalGL3 v → ℂ) (d : LocalGL3 v),
      IsLocalWhittakerDatum v (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W₀ ∧
      (∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
        W₀ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W₀ h) ∧
      (∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B) → W₀ h = 0) ∧
      (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B →
        ‖W₀ h‖ ≤ C / ((LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2) * (LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2)) ^ t)) ∧
      (∃ ε₀ : ℂ, ε₀ ≠ 0 ∧ ε₀ ^ 2 = ε ^ 2 ∧
      (∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W₀ 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W₀ 1 s g =
            (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W₀) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W₀ 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε₀ * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)))) ∧
      (∀ F ∈ gl3CyclicSubspace W₀, (fun g : LocalGL3 v => F (d * g * d⁻¹)) ∈ gl3CyclicSubspace W) ∧
      (∀ n : ℕ, d * iotaTorusLocal v n = iotaTorusLocal v n * d) ∧
      (∀ k₁ k₂ : ℕ, d * twoRowPointLocal v k₁ k₂ = twoRowPointLocal v k₁ k₂ * d) ∧
      (∀ c : ℕ, ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v c, d * k * d⁻¹ ∈ congruenceK1 (𝓞 ℚ) ℚ v c) ∧
      (∀ g : LocalGL3 v, W₀ g = W (d * g * d⁻¹)) ∧
      d = iotaGL (Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : (v.adicCompletion ℚ)ˣ) * diagOne (-1 : (v.adicCompletion ℚ)ˣ)) ∧
      (∀ c : ℕ, d ∈ congruenceK1 (𝓞 ℚ) ℚ v c) ∧
      (∀ F ∈ gl3CyclicSubspace W, (fun g : LocalGL3 v => F (d⁻¹ * g * d)) ∈ gl3CyclicSubspace W₀) := by
  classical
  subst hψ
  letI mK : MeasurableSpace (v.adicCompletion ℚ) := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := SFδ.borelSpace_units v
  haveI hadd : (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
    show (((Ideal.absNorm v.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2)) •
      Measure.addHaarMeasure (integersPositiveCompacts ℚ v)).IsAddHaarMeasure
    refine Measure.IsAddHaarMeasure.nnreal_smul _ ?_
    apply ne_of_gt
    apply NNReal.rpow_pos
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero h0
  haveI hHaar := LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ v (selfDualHaarAt ℚ v)
  set μ : Measure (v.adicCompletion ℚ)ˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)) with hμ
  set ν : Measure (v.adicCompletion ℚ) := selfDualHaarAt ℚ v with hν

  refine ⟨SFδ.conj v W, SFδ.d v, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  ·
    refine ⟨?_, ?_, SFδ.hasWhittakerMultOne_conj v _ W hmult, ?_, ?_, ?_⟩
    · intro x y z g
      show W (SFδ.d v * (upperUnipotent3 x y z * g) * SFδ.d v) = _ * W (SFδ.d v * g * SFδ.d v)
      have : SFδ.d v * (upperUnipotent3 x y z * g) * SFδ.d v =
          (SFδ.d v * upperUnipotent3 x y z * SFδ.d v) * (SFδ.d v * g * SFδ.d v) := by
        calc SFδ.d v * (upperUnipotent3 x y z * g) * SFδ.d v
            = SFδ.d v * upperUnipotent3 x y z * (SFδ.d v * SFδ.d v) * g * SFδ.d v := by rw [SFδ.d_mul_d]; simp only [mul_one, mul_assoc]
          _ = _ := by simp only [mul_assoc]
      rw [this, SFδ.d_upper, hW, AddChar.inv_apply]
      congr 2; ring
    · show W (SFδ.d v * 1 * SFδ.d v) = 1
      rw [mul_one, SFδ.d_mul_d, h1]
    · intro F hF hF0
      have hcF : SFδ.conj v F ∈ gl3CyclicSubspace W := by
        have := SFδ.conj_mem_cyclic v hF
        rwa [SFδ.conj_conj] at this
      have hcF0 : SFδ.conj v F ≠ 0 := fun h => hF0 (SFδ.conj_injective v (by rw [h]; rfl))
      have hW' := hirr _ hcF hcF0
      have h2 := SFδ.conj_mem_cyclic v hW'
      rwa [SFδ.conj_conj] at h2
    · obtain ⟨Uv, hUo, hUv⟩ := hsm
      refine ⟨Uv.comap (MulAut.conj (SFδ.d v)).toMonoidHom, ?_, ?_⟩
      · exact hUo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
      · intro k hk g
        have hk' : SFδ.d v * k * (SFδ.d v)⁻¹ ∈ Uv := hk
        show W (SFδ.d v * (g * k) * SFδ.d v) = W (SFδ.d v * g * SFδ.d v)
        have : SFδ.d v * (g * k) * SFδ.d v = (SFδ.d v * g * SFδ.d v) * (SFδ.d v * k * (SFδ.d v)⁻¹) := by
          rw [SFδ.d_inv]
          calc SFδ.d v * (g * k) * SFδ.d v = SFδ.d v * g * (SFδ.d v * SFδ.d v) * k * SFδ.d v := by
                rw [SFδ.d_mul_d]; simp only [mul_one, mul_assoc]
            _ = _ := by simp only [mul_assoc]
        rw [this, hUv _ hk']
    · intro Uv hUo
      set Uv' : Subgroup (LocalGL3 v) := Uv.comap (MulAut.conj (SFδ.d v)).toMonoidHom with hUv'
      have hUo' : IsOpen (Uv' : Set (LocalGL3 v)) :=
        hUo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
      obtain ⟨B, hB⟩ := hadm Uv' hUo'
      refine ⟨B.image (SFδ.conj v), fun F hF hFix => ?_⟩
      have hcF : SFδ.conj v F ∈ gl3CyclicSubspace W := by
        have := SFδ.conj_mem_cyclic v hF
        rwa [SFδ.conj_conj] at this
      have hcFix : ∀ k ∈ Uv', ∀ g : LocalGL3 v, SFδ.conj v F (g * k) = SFδ.conj v F g := by
        intro k hk g
        have hk' : SFδ.d v * k * (SFδ.d v)⁻¹ ∈ Uv := hk
        show F (SFδ.d v * (g * k) * SFδ.d v) = F (SFδ.d v * g * SFδ.d v)
        have : SFδ.d v * (g * k) * SFδ.d v = (SFδ.d v * g * SFδ.d v) * (SFδ.d v * k * (SFδ.d v)⁻¹) := by
          rw [SFδ.d_inv]
          calc SFδ.d v * (g * k) * SFδ.d v = SFδ.d v * g * (SFδ.d v * SFδ.d v) * k * SFδ.d v := by
                rw [SFδ.d_mul_d]; simp only [mul_one, mul_assoc]
            _ = _ := by simp only [mul_assoc]
        rw [this, hFix _ hk']
      have hmem := hB _ hcF hcFix
      have : F ∈ (Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))).map (SFδ.conjₗ v) :=
        ⟨SFδ.conj v F, hmem, SFδ.conj_conj v F⟩
      rw [Submodule.map_span] at this
      have e : ((SFδ.conjₗ v : (LocalGL3 v → ℂ) →ₗ[ℂ] (LocalGL3 v → ℂ)) : (LocalGL3 v → ℂ) → (LocalGL3 v → ℂ)) =
          SFδ.conj v := rfl
      rw [e] at this
      rw [Finset.coe_image]
      exact this
  ·
    intro t h
    show W (SFδ.d v * (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) * SFδ.d v) = _ * W (SFδ.d v * h * SFδ.d v)
    have : SFδ.d v * (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) * SFδ.d v =
        Matrix.GeneralLinearGroup.scalar (Fin 3) t * (SFδ.d v * h * SFδ.d v) := by
      calc SFδ.d v * (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) * SFδ.d v
          = (SFδ.d v * Matrix.GeneralLinearGroup.scalar (Fin 3) t) * h * SFδ.d v := by simp only [mul_assoc]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin 3) t * SFδ.d v) * h * SFδ.d v := by rw [SFδ.scalar_comm]
        _ = _ := by simp only [mul_assoc]
    rw [this, hω]
  ·
    obtain ⟨B, t, C, hG⟩ := hWgauge
    refine ⟨B, t, C, fun h => ?_⟩
    have := hG (SFδ.d v * h * SFδ.d v)
    rw [SFδ.lastRowSup_conj, SFδ.minorSup_conj, SFδ.detSize_conj] at this
    exact this
  ·
    refine ⟨((ωv (-1 : (v.adicCompletion ℚ)ˣ)⁻¹ : ℂˣ) : ℂ) * ε, mul_ne_zero (Units.ne_zero _) hε, ?_, ?_⟩
    · have : (((ωv (-1 : (v.adicCompletion ℚ)ˣ)⁻¹ : ℂˣ) : ℂ)) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← map_pow, inv_pow, neg_one_sq, inv_one, map_one, Units.val_one]
      rw [mul_pow, this, one_mul]
    · intro g
      obtain ⟨P, σ₀, σ₁, hrat, h30c, h30e, h31c, h31e⟩ := h31 (SFδ.d v * g * SFδ.d v)
      refine ⟨P, σ₀, σ₁, hrat, SFδ.isLocalZeta30ConvergentAbove_conj v _ W g σ₀ h30c, ?_,
        SFδ.isLocalZeta31ConvergentAbove_conj v _ _ W ωv hω g σ₁ h31c, ?_⟩
      · intro s hs
        rw [SFδ.localZeta30_conj]
        exact h30e s hs
      · intro s hs
        rw [SFδ.localZetaDual31_conj v _ _ W ωv hω, h31e s hs]
        ring
  · intro F hF
    rw [SFδ.d_inv]
    have := SFδ.conj_mem_cyclic v hF
    rwa [SFδ.conj_conj] at this
  · exact SFδ.d_iotaTorus v
  · exact SFδ.d_twoRow v
  · intro c k hk
    rw [SFδ.d_inv]
    exact SFδ.conj_mem_congruenceK1 v c hk
  · intro g
    rw [SFδ.d_inv]; rfl
  · exact SFδ.d_mem_congruenceK1 v
  · intro F hF
    rw [SFδ.d_inv]
    exact SFδ.conj_mem_cyclic v hF

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localPackage_psiLocal_inv_comp_mul_diagonal_of_localPackage_psiLocal_of_gauge.SFδ"

end S_LanglandsTunnell_CubicInduction_localPackage_psiLocal_inv_comp_mul_diagonal_of_localPackage_psiLocal_of_gauge
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_localPackage_psiLocal_inv_comp_mul_diagonal_of_localPackage_psiLocal_of_gauge (solution)
