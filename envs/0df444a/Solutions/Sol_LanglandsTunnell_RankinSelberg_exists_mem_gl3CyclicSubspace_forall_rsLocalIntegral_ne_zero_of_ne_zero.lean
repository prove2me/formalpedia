-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_ne_zero_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/60ed2540-4e4c-51c7-b7c4-effd3808c0b6

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_HaarQuotient
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_sum_translate_eq_const_of_apply_one_ne_zero
import Theorems.Thm_HaarQuotient_exists_forall_integral_withDensity_density_eq_smul_of_isHaarMeasure
import Theorems.Thm_HaarQuotient_exists_forall_integrable_comp_mul_right_iff_and_integral_eq_smul
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_ne_zero_of_ne_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction

open scoped NNReal

noncomputable section

namespace LTJpss1Sided

abbrev unip (v : HeightOneSpectrum (𝓞 ℚ)) : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)) :=
  (unipotentGL2Hom (R := v.adicCompletion ℚ)).range

theorem coe_unip_eq (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((unip v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))) =
      {g : GL (Fin 2) (v.adicCompletion ℚ) |
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0 = 1 ∧
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 = 0 ∧
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 = 1} := by
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    simp [unipotentGL2Hom, unipotentGL2_coe]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1), Units.ext ?_⟩
    change ((unipotentGL2 ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) : GL (Fin 2) (v.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    rw [unipotentGL2_coe]
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

theorem isClosed_unip (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsClosed ((unip v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))) := by
  rw [coe_unip_eq]
  have hc : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j := fun i j =>
    (Units.continuous_val).matrix_elem i j
  exact ((isClosed_singleton.preimage (hc 0 0)).inter
    ((isClosed_singleton.preimage (hc 1 0)).inter (isClosed_singleton.preimage (hc 1 1))))

theorem unip_comm (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (unip v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)))) :
    a * b = b * a := by
  obtain ⟨x, hx⟩ := a.2
  obtain ⟨y, hy⟩ := b.2
  refine Subtype.ext ?_
  change (a : GL (Fin 2) (v.adicCompletion ℚ)) * b = b * a
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

theorem unipotent_eq_unipotentGL2 (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    UnramifiedWhittaker.unipotent x = (unipotentGL2 x : GL (Fin 2) (v.adicCompletion ℚ)) := by
  refine Units.ext ?_
  rw [unipotentGL2_coe]
  simp [UnramifiedWhittaker.unipotent]

theorem det_unipotentGL2 (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x : GL (Fin 2) (v.adicCompletion ℚ)) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

scoped instance instSecondCountableMat (v : HeightOneSpectrum (𝓞 ℚ)) :
    SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → v.adicCompletion ℚ))

scoped instance instSecondCountableMatOp (v : HeightOneSpectrum (𝓞 ℚ)) :
    SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem secondCountableTopology_localGL (v : HeightOneSpectrum (𝓞 ℚ)) :
    SecondCountableTopology (GL (Fin 2) (v.adicCompletion ℚ)) :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem isMulRightInvariant_of_comm {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]
    (μ' : Measure H) [μ'.IsMulLeftInvariant] (hcomm : ∀ a b : H, a * b = b * a) : μ'.IsMulRightInvariant :=
  ⟨fun g => by
    have : (fun h : H => h * g) = fun h => g * h := funext fun h => hcomm h g
    rw [this]
    exact map_mul_left_eq_self μ' g⟩

theorem law_of_mem_gl3CyclicSubspace {A : Type*} [CommRing A] {ψ : AddChar A ℂ} {W₀ W : GL (Fin 3) A → ℂ}
    (h₀ : IsGL3PsiWhittakerFn ψ W₀) (hW : W ∈ gl3CyclicSubspace W₀) : IsGL3PsiWhittakerFn ψ W := by
  have hmem : W₀ ∈ gl3PsiWhittakerFnSpace A ℂ ψ := (mem_gl3PsiWhittakerFnSpace_iff ψ W₀).mpr h₀
  have hle : gl3CyclicSubspace W₀ ≤ gl3PsiWhittakerFnSpace A ℂ ψ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    exact rightTranslate_mem_gl3PsiWhittakerFnSpace ψ h hmem
  exact (mem_gl3PsiWhittakerFnSpace_iff ψ W).mp (hle hW)

def dmod (v : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 2) (v.adicCompletion ℚ)) : ℝ :=
  (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ)

theorem dmod_nonneg (v : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 2) (v.adicCompletion ℚ)) : 0 ≤ dmod v g :=
  NNReal.coe_nonneg _

theorem dmod_pos (v : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 2) (v.adicCompletion ℚ)) : 0 < dmod v g := by
  unfold dmod
  exact_mod_cast modulus_pos (Units.ne_zero _)

theorem dmod_mul (v : HeightOneSpectrum (𝓞 ℚ)) (g h : GL (Fin 2) (v.adicCompletion ℚ)) :
    dmod v (g * h) = dmod v g * dmod v h := by
  unfold dmod
  rw [map_mul, Units.val_mul, modulus_mul, NNReal.coe_mul]

theorem dmod_eq_norm (v : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 2) (v.adicCompletion ℚ)) :
    dmod v g = ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ := by
  unfold dmod
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, coe_nnnorm, Matrix.GeneralLinearGroup.val_det_apply]

def phiP (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (w : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (s : ℂ)
    (g : GL (Fin 2) (v.adicCompletion ℚ)) : ℂ :=
  (W (iotaGL g) * w g) * ((dmod v g : ℝ) : ℂ) ^ (s - 1 / 2)

theorem rsLocalIntegral_eq_integral_phiP (v : HeightOneSpectrum (𝓞 ℚ)) [MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ))]
    (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) (μN : Measure ↥(unip v)) (s : ℂ) (W : LocalGL3 v → ℂ)
    (w : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) :
    RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
        (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
          (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
        s (fun g => W (iotaGL g)) w =
      ∫ g, phiP v W w s g ∂(μ₂.withDensity (HaarQuotient.density (unip v) μN)) := rfl

theorem phiP_unipotent_mul (v : HeightOneSpectrum (𝓞 ℚ)) {W : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W)
    {w : GL (Fin 2) (v.adicCompletion ℚ) → ℂ}
    (hw : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      w (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * w g)
    (s : ℂ) :
    ∀ (x : ↥(unip v)) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      phiP v W w s ((x : GL (Fin 2) (v.adicCompletion ℚ)) * g) = phiP v W w s g := by
  rintro ⟨_, ⟨z, rfl⟩⟩ g
  have hx : (unipotentGL2Hom z : GL (Fin 2) (v.adicCompletion ℚ)) = unipotentGL2 z.toAdd := rfl
  show phiP v W w s (unipotentGL2Hom z * g) = phiP v W w s g
  unfold phiP dmod
  rw [hx, map_mul, iotaGL_unipotentGL2, hW, map_mul, det_unipotentGL2, one_mul, ← unipotent_eq_unipotentGL2, hw,
    AddChar.inv_apply, add_zero]
  congr 1
  calc (NumberField.StandardAddChar.psiLocal ℚ v) (-z.toAdd) * W (iotaGL g) *
        ((NumberField.StandardAddChar.psiLocal ℚ v) z.toAdd * w g)
      = ((NumberField.StandardAddChar.psiLocal ℚ v) (-z.toAdd) * (NumberField.StandardAddChar.psiLocal ℚ v) z.toAdd) *
          (W (iotaGL g) * w g) := by ring
    _ = W (iotaGL g) * w g := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]

theorem phiP_translate (v : HeightOneSpectrum (𝓞 ℚ)) (W' : LocalGL3 v → ℂ) (w : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (g₀ : GL (Fin 2) (v.adicCompletion ℚ)) (s : ℂ) (g : GL (Fin 2) (v.adicCompletion ℚ)) :
    phiP v (fun y : LocalGL3 v => W' (y * (iotaGL g₀)⁻¹)) w s (g * g₀) =
      ((dmod v g₀ : ℝ) : ℂ) ^ (s - 1 / 2) * phiP v W' (fun h => w (h * g₀)) s g := by
  unfold phiP
  simp only [map_mul, mul_inv_cancel_right]
  rw [dmod_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (dmod_nonneg v g) (dmod_nonneg v g₀) (s - 1 / 2)]
  ring

theorem continuous_iotaGL (v : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous fun g : GL (Fin 2) (v.adicCompletion ℚ) => (iotaGL g : LocalGL3 v) := by
  rw [Units.continuous_iff]
  have hc : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j := fun i j =>
    (Units.continuous_val).matrix_elem i j
  have hci : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
      ((g⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j := fun i j =>
    (Units.continuous_coe_inv).matrix_elem i j
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [Function.comp_apply, coe_iotaGL, embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
        Matrix.cons_val_fin_one] <;>
      first | exact continuous_const | exact hc _ _
  · have h : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
        ((((iotaGL g : LocalGL3 v)⁻¹ : LocalGL3 v)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
          embedMat2 ((g⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :=
      fun g => by rw [← map_inv, coe_iotaGL]
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact continuous_const | exact hci _ _

theorem continuous_of_rightInvariant {H : Type*} [Group H] [TopologicalSpace H] [ContinuousMul H]
    {α : Type*} [TopologicalSpace α]
    {f : H → α} {U : Subgroup H} (hU : IsOpen (U : Set H)) (hf : ∀ k ∈ U, ∀ g : H, f (g * k) = f g) :
    Continuous f := by
  refine (IsLocallyConstant.iff_exists_open f).mpr (fun x => ?_) |>.continuous
  refine ⟨(fun h => x⁻¹ * h) ⁻¹' (U : Set H), hU.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro y hy
    have := hf (x⁻¹ * y) hy x
    rwa [mul_inv_cancel_left] at this

theorem continuous_dmod (v : HeightOneSpectrum (𝓞 ℚ)) : Continuous (dmod v) := by
  have : dmod v = fun g : GL (Fin 2) (v.adicCompletion ℚ) => ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ :=
    funext (dmod_eq_norm v)
  rw [this]
  exact continuous_norm.comp (Units.continuous_val.matrix_det)

theorem measurable_phiP (v : HeightOneSpectrum (𝓞 ℚ)) [MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ))]
    [BorelSpace (GL (Fin 2) (v.adicCompletion ℚ))] {W : LocalGL3 v → ℂ} (hW : Continuous W)
    {w : GL (Fin 2) (v.adicCompletion ℚ) → ℂ} (hw : Continuous w) (s : ℂ) :
    Measurable (phiP v W w s) := by
  have h1 : Continuous fun g : GL (Fin 2) (v.adicCompletion ℚ) => W (iotaGL g) := hW.comp (continuous_iotaGL v)
  have h3 : Continuous fun g : GL (Fin 2) (v.adicCompletion ℚ) => ((dmod v g : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_dmod v)
  exact ((h1.mul hw).measurable).mul (h3.measurable.pow_const _)

theorem continuous_sum_translate (v : HeightOneSpectrum (𝓞 ℚ)) {W₀ : LocalGL3 v → ℂ} (hW₀ : Continuous W₀)
    {n : ℕ} (c : Fin n → ℂ) (kk : Fin n → LocalGL3 v) (x : LocalGL3 v) :
    Continuous fun y : LocalGL3 v => ∑ i, c i * W₀ (y * x * kk i) := by
  refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
  exact hW₀.comp ((continuous_id.mul continuous_const).mul continuous_const)

theorem integrable_of_integral_ne_zero {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℂ}
    (h : ∫ a, f a ∂ν ≠ 0) : Integrable f ν := by
  by_contra hf
  exact h (integral_undef hf)

theorem main
    (p : HeightOneSpectrum (𝓞 ℚ))
    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (hW₃ne : W₃base ≠ 0)
    (hW₃irr : ∀ W ∈ gl3CyclicSubspace W₃base, W ≠ 0 → W₃base ∈ gl3CyclicSubspace W)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (hwsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hwne : w ≠ 0) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∃ W₃ ∈ gl3CyclicSubspace W₃base,
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∃ (C : ℂ) (a : ℝ), C ≠ 0 ∧ 0 < a ∧ ∀ s : ℂ,
        Integrable
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (W₃ (iotaGL g) * w g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) :
                  p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
            s (fun g => W₃ (iotaGL g)) w = C * ((a : ℝ) : ℂ) ^ (s - 1 / 2) := by
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  haveI : LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ)) := locallyCompactSpace_localGL ℚ p
  haveI : SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ)) := secondCountableTopology_localGL p
  have hclosed := isClosed_unip p
  haveI : LocallyCompactSpace ↥(unip p) := hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace

  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hwne
  simp only [Pi.zero_apply] at hg₀
  set w' : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun g => w (g * g₀) with hw'def
  have hw'1 : w' 1 ≠ 0 := by simpa only [hw'def, one_mul] using hg₀
  have hw'law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w' (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w' g := by
    intro x g
    simp only [hw'def, mul_assoc]
    exact hwlaw x (g * g₀)
  obtain ⟨U, hUo, hwU⟩ := hwsm
  have hw'U : ∃ U₂ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (U₂ : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
        ∀ k ∈ U₂, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g := by
    have hcont : Continuous fun h : GL (Fin 2) (p.adicCompletion ℚ) => g₀⁻¹ * h * g₀ :=
      (continuous_const.mul continuous_id).mul continuous_const
    refine ⟨U.comap (MulAut.conj g₀⁻¹).toMonoidHom, ?_, ?_⟩
    · have hset : ((Subgroup.comap (MulAut.conj g₀⁻¹).toMonoidHom U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
              Set (GL (Fin 2) (p.adicCompletion ℚ))) =
          (fun h : GL (Fin 2) (p.adicCompletion ℚ) => g₀⁻¹ * h * g₀) ⁻¹' (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
        ext h
        simp
      rw [hset]
      exact hUo.preimage hcont
    · intro k' hk' g
      have hk'' : g₀⁻¹ * k' * g₀ ∈ U := by
        simpa [MulAut.conj_apply] using hk'
      show w (g * k' * g₀) = w (g * g₀)
      have e := hwU _ hk'' (g * g₀)
      rw [show g * g₀ * (g₀⁻¹ * k' * g₀) = g * k' * g₀ by group] at e
      exact e

  let μ₀ : Measure (GL (Fin 2) (p.adicCompletion ℚ)) := AutomorphicForm.localHaar ℚ p
  haveI hμ₀ : μ₀.IsHaarMeasure := AutomorphicForm.isHaarMeasure_localHaar ℚ p
  let μN₀ : Measure ↥(unip p) := Measure.haar
  haveI hμN₀ : μN₀.IsHaarMeasure := inferInstance
  obtain ⟨n, c, kk, Cst, hCst, hpair⟩ :=
    LanglandsTunnell.CubicInduction.exists_rsLocalIntegral_sum_translate_eq_const_of_apply_one_ne_zero p
      (NumberField.StandardAddChar.psiLocal ℚ p) (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p) W₃base hW₃law hW₃sm
      hW₃irr hW₃ne w' hw'law hw'U hw'1 μ₀ μN₀

  set W' : LocalGL3 p → ℂ := fun y => ∑ i, c i * W₃base (y * kk i) with hW'def
  set W₃ : LocalGL3 p → ℂ := fun y => W' (y * (iotaGL g₀)⁻¹) with hW₃def
  have hW'mem : W' ∈ gl3CyclicSubspace W₃base := by
    have e : W' = ∑ i, c i • (fun g : LocalGL3 p => W₃base (g * kk i)) := by
      ext g
      simp [hW'def, Finset.sum_apply, smul_eq_mul]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (c i) (Submodule.subset_span ⟨kk i, rfl⟩)
  have hW₃mem : W₃ ∈ gl3CyclicSubspace W₃base :=
    gl3AmbientRightTranslate_mem_gl3CyclicSubspace W₃base (iotaGL g₀)⁻¹ hW'mem
  have hW'law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W' :=
    law_of_mem_gl3CyclicSubspace hW₃law hW'mem
  have hW₃law' : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃ :=
    law_of_mem_gl3CyclicSubspace hW₃law hW₃mem

  obtain ⟨Uv, hUvo, hWUv⟩ := hW₃sm
  have hW₀c : Continuous W₃base := continuous_of_rightInvariant hUvo hWUv
  have hwc : Continuous w := continuous_of_rightInvariant hUo hwU
  have hW₃c : Continuous W₃ := by
    have : W₃ = fun y : LocalGL3 p => ∑ i, c i * W₃base (y * (iotaGL g₀)⁻¹ * kk i) := by
      funext y
      simp [hW₃def, hW'def]
    rw [this]
    exact continuous_sum_translate p hW₀c c kk _
  refine ⟨W₃, hW₃mem, ?_⟩
  intro μ₂ _ μN₂ _

  haveI : μN₂.IsMulRightInvariant := isMulRightInvariant_of_comm μN₂ (unip_comm p)
  haveI : μN₀.IsMulRightInvariant := isMulRightInvariant_of_comm μN₀ (unip_comm p)
  obtain ⟨cH, hcH0, hcH⟩ :=
    HaarQuotient.exists_forall_integral_withDensity_density_eq_smul_of_isHaarMeasure (E := ℂ)
      (unip p) hclosed μ₀ μ₂ μN₀ μN₂
  have hcH' : ((cH : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (NNReal.coe_ne_zero.2 hcH0)

  have hval' : ∀ s : ℂ,
      ∫ g, phiP p W' w' s g ∂(μ₂.withDensity (HaarQuotient.density (unip p) μN₂)) = ((cH : ℝ) : ℂ) * Cst := by
    intro s
    have h := hcH (phiP p W' w' s) (phiP_unipotent_mul p hW'law hw'law s)
    rw [Complex.real_smul] at h
    rw [h]
    congr 1
    exact (hpair s).2
  have hint' : ∀ s : ℂ, Integrable (phiP p W' w' s) (μ₂.withDensity (HaarQuotient.density (unip p) μN₂)) := by
    intro s
    refine integrable_of_integral_ne_zero ?_
    rw [hval' s]
    exact mul_ne_zero hcH' hCst

  obtain ⟨cR, hcR0, hcR⟩ :=
    HaarQuotient.exists_forall_integrable_comp_mul_right_iff_and_integral_eq_smul (E := ℂ)
      μ₂ (unip p) hclosed μN₂ g₀
  have hcR' : ((cR : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (NNReal.coe_ne_zero.2 hcR0)
  refine ⟨((cR : ℝ) : ℂ)⁻¹ * (((cH : ℝ) : ℂ) * Cst), dmod p g₀,
    mul_ne_zero (inv_ne_zero hcR') (mul_ne_zero hcH' hCst), dmod_pos p g₀, ?_⟩
  intro s
  have hmeas : Measurable (phiP p W₃ w s) := measurable_phiP p hW₃c hwc s
  have hinvN : ∀ (x : ↥(unip p)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      phiP p W₃ w s ((x : GL (Fin 2) (p.adicCompletion ℚ)) * g) = phiP p W₃ w s g :=
    phiP_unipotent_mul p hW₃law' hwlaw s
  obtain ⟨hiff, hR⟩ := hcR (phiP p W₃ w s) hmeas hinvN

  have htr : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => phiP p W₃ w s (g * g₀)) =
      fun g => ((dmod p g₀ : ℝ) : ℂ) ^ (s - 1 / 2) * phiP p W' w' s g := by
    funext g
    exact phiP_translate p W' w g₀ s g
  have hintTr : Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => phiP p W₃ w s (g * g₀))
      (μ₂.withDensity (HaarQuotient.density (unip p) μN₂)) := by
    rw [htr]
    exact (hint' s).const_mul _
  have hint : Integrable (phiP p W₃ w s) (μ₂.withDensity (HaarQuotient.density (unip p) μN₂)) := hiff.mp hintTr
  refine ⟨hint, ?_⟩

  rw [rsLocalIntegral_eq_integral_phiP]
  have hR' : ((cR : ℝ) : ℂ) * ∫ g, phiP p W₃ w s g ∂(μ₂.withDensity (HaarQuotient.density (unip p) μN₂)) =
      ((dmod p g₀ : ℝ) : ℂ) ^ (s - 1 / 2) * (((cH : ℝ) : ℂ) * Cst) := by
    rw [← Complex.real_smul, ← hR, htr, integral_const_mul, hval' s]
  calc ∫ g, phiP p W₃ w s g ∂(μ₂.withDensity (HaarQuotient.density (unip p) μN₂))
      = ((cR : ℝ) : ℂ)⁻¹ * (((cR : ℝ) : ℂ) *
          ∫ g, phiP p W₃ w s g ∂(μ₂.withDensity (HaarQuotient.density (unip p) μN₂))) := by
        rw [← mul_assoc, inv_mul_cancel₀ hcR', one_mul]
    _ = ((cR : ℝ) : ℂ)⁻¹ * (((cH : ℝ) : ℂ) * Cst) * ((dmod p g₀ : ℝ) : ℂ) ^ (s - 1 / 2) := by
        rw [hR']; ring

theorem main_ne_zero
    (p : HeightOneSpectrum (𝓞 ℚ))
    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (hW₃ne : W₃base ≠ 0)
    (hW₃irr : ∀ W ∈ gl3CyclicSubspace W₃base, W ≠ 0 → W₃base ∈ gl3CyclicSubspace W)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (hwsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hwne : w ≠ 0) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∃ W₃ ∈ gl3CyclicSubspace W₃base,
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∀ s : ℂ,
        Integrable
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (W₃ (iotaGL g) * w g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) :
                  p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
            s (fun g => W₃ (iotaGL g)) w ≠ 0 := by
  obtain ⟨W₃, hW₃, h⟩ := main p W₃base hW₃law hW₃sm hW₃ne hW₃irr w hwlaw hwsm hwne
  refine ⟨W₃, hW₃, fun μ₂ _ μN₂ _ s => ?_⟩
  obtain ⟨C, a, hC, ha, hs⟩ := h μ₂ μN₂
  refine ⟨(hs s).1, ?_⟩
  rw [(hs s).2]
  refine mul_ne_zero hC fun h0 => ?_
  rw [Complex.cpow_eq_zero_iff] at h0
  exact (Complex.ofReal_ne_zero.mpr ha.ne') h0.1

theorem main_forall_exists
    (p : HeightOneSpectrum (𝓞 ℚ))
    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (hW₃ne : W₃base ≠ 0)
    (hW₃irr : ∀ W ∈ gl3CyclicSubspace W₃base, W ≠ 0 → W₃base ∈ gl3CyclicSubspace W)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (hwsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hwne : w ≠ 0) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∃ W₃ ∈ gl3CyclicSubspace W₃base,
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
            s (fun g => W₃ (iotaGL g)) w ≠ 0 := by
  obtain ⟨W₃, hW₃, h⟩ := main_ne_zero p W₃base hW₃law hW₃sm hW₃ne hW₃irr w hwlaw hwsm hwne
  refine ⟨W₃, hW₃, fun μ₂ _ μN₂ _ σ => ⟨((σ + 1 : ℝ) : ℂ), ?_, (h μ₂ μN₂ _).2⟩⟩
  rw [Complex.ofReal_re]
  linarith

end LTJpss1Sided
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_ne_zero_of_ne_zero.LTJpss1Sided"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_ne_zero_of_ne_zero.LTJpss1Sided"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (hW₃ne : W₃base ≠ 0)
    (hW₃irr : ∀ W ∈ gl3CyclicSubspace W₃base, W ≠ 0 → W₃base ∈ gl3CyclicSubspace W)

    (hW₃adm : ∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
      ∃ B : Finset (LocalGL3 p → ℂ), ∀ W ∈ gl3CyclicSubspace W₃base,
        (∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (LocalGL3 p → ℂ)))

    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (hwsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hwne : w ≠ 0) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∃ W₃ ∈ gl3CyclicSubspace W₃base, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
            s (fun g => W₃ (iotaGL g)) w ≠ 0 := by
  intro μ₂ _ μN₂ _
  obtain ⟨W₃, hW₃, h⟩ := LTJpss1Sided.main_ne_zero p W₃base hW₃law hW₃sm hW₃ne hW₃irr w hwlaw hwsm hwne
  exact ⟨W₃, hW₃, 0, fun s _ => (h μ₂ μN₂ s).2⟩

end S_LanglandsTunnell_RankinSelberg_exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_ne_zero_of_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_ne_zero_of_ne_zero (solution)
