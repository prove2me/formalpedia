-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_pos_forall_rsLocalIntegral_indicator_unipotent_mul_localLevelOne_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b83b2e3f-3134-5342-8bed-8db938275b24

import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_HaarQuotient_lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsLocalIntegral_indicator_unipotent_mul_localLevelOne_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace LOCCELLVOL

open Matrix

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "Gv" => GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)

theorem coe_range_unipotentGL2Hom :
    ((unipotentGL2Hom (R := v.adicCompletion ℚ)).range : Set Gv) =
      {g : Gv | (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0 = 1} ∩
        {g : Gv | (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 = 1} ∩
        {g : Gv | (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 = 0} := by
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [unipotentGL2Hom, unipotentGL2]
  · rintro ⟨⟨h00, h11⟩, h10⟩
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1), ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2Hom, unipotentGL2, h00, h11, h10]

theorem isClosed_range_unipotentGL2Hom :
    IsClosed ((unipotentGL2Hom (R := v.adicCompletion ℚ)).range : Set Gv) := by
  have hc : ∀ i j : Fin 2,
      Continuous fun g : Gv => (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  rw [coe_range_unipotentGL2Hom]
  exact ((isClosed_eq (hc 0 0) continuous_const).inter (isClosed_eq (hc 1 1) continuous_const)).inter
    (isClosed_eq (hc 1 0) continuous_const)

theorem unipotent_comm (a b : (unipotentGL2Hom (R := v.adicCompletion ℚ)).range) : a * b = b * a := by
  obtain ⟨x, hx⟩ := a.2
  obtain ⟨y, hy⟩ := b.2
  apply Subtype.ext
  show (a : Gv) * b = b * a
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

theorem coe_localLevelOne_top :
    ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Subgroup Gv) : Set Gv) = localIntegralSet ℚ v := by
  ext k
  rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff]
  show _ ↔ k ∈ integralUnitsSet (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))
  rw [mem_integralUnitsSet]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    have key : ∀ m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), (∀ i j, m i j ∈ v.adicCompletionIntegers ℚ) →
        AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ m := by
      intro m hm
      refine ⟨hm, ?_, ?_⟩
      · rw [NumberField.AdelicLevel.idealBound_top]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hm 1 0)
      · rw [NumberField.AdelicLevel.idealBound_top]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1
          ((v.adicCompletionIntegers ℚ).sub_mem (hm 1 1) (v.adicCompletionIntegers ℚ).one_mem)
    exact ⟨key _ h1, key _ h2⟩

theorem valued_det_eq_one_of_mem_localLevelOne {k : Gv} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    Valued.v ((Matrix.GeneralLinearGroup.det k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
  obtain ⟨h1, h2⟩ := (AdelicDock.mem_localLevelOne_iff (𝓞 ℚ) ℚ v k).1 hk
  have hle : ∀ m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), (∀ i j, m i j ∈ v.adicCompletionIntegers ℚ) →
      Valued.v m.det ≤ 1 := by
    intro m hm
    have h := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hm i j)
    rw [Matrix.det_fin_two]
    refine Valued.v.map_sub_le ?_ ?_
    · rw [map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
    · rw [map_mul]; exact mul_le_one' (h 0 1) (h 1 0)
  have hk1 := hle _ h1.integral
  have hk2 := hle _ h2.integral
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  have hprod : Valued.v (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det *
      Valued.v ((k⁻¹ : Gv) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  exact le_antisymm hk1 (by
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det *
          Valued.v ((k⁻¹ : Gv) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det := hprod.symm
      _ ≤ Valued.v (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det * 1 := mul_le_mul_right hk2 _
      _ = _ := mul_one _)

theorem det_unipotent_eq_one {n : Gv} (hn : n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range) :
    Matrix.GeneralLinearGroup.det n = 1 := by
  obtain ⟨x, rfl⟩ := hn
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  simp [unipotentGL2Hom, unipotentGL2, Matrix.det_fin_two]

theorem modulus_det_eq_one {g : Gv}
    (hg : g ∈ {x : Gv | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
      ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}) :
    ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
      v.adicCompletion ℚ) : ℝ) : ℂ) = 1 := by
  obtain ⟨n, hn, k, hk, rfl⟩ := hg
  rw [map_mul, det_unipotent_eq_one v hn, one_mul, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm,
    coe_nnnorm, NumberField.FinitePlace.norm_def, valued_det_eq_one_of_mem_localLevelOne v hk, map_one]
  simp

end LOCCELLVOL

open scoped Pointwise in
open LOCCELLVOL in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
    ∃ m : ℝ, 0 < m ∧
      (∀ s : ℂ,
        Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
          ({x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}.indicator (fun _ => (1 : ℂ)) g *
            {x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}.indicator (fun _ => (1 : ℂ)) g) *
            ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂))) ∧
      ∀ s : ℂ,
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                v.adicCompletion ℚ) : ℝ))
            s
            ({x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}.indicator (fun _ => (1 : ℂ)))
            ({x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}.indicator (fun _ => (1 : ℂ))) = m := by
  intro μ₂ _ μN₂ _
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := localGLBorel ℚ v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ v
  haveI : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := locallyCompactSpace_localGL ℚ v
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → v.adicCompletion ℚ))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin 2) (v.adicCompletion ℚ)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology

  have hN := isClosed_range_unipotentGL2Hom v
  haveI : μN₂.IsMulRightInvariant := ⟨fun g => by
    have h : (fun h : (unipotentGL2Hom (R := v.adicCompletion ℚ)).range => h * g) = fun h => g * h :=
      funext fun h => unipotent_comm v h g
    rw [h]
    exact MeasureTheory.map_mul_left_eq_self μN₂ g⟩
  have hKo : IsOpen ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
      Set (GL (Fin 2) (v.adicCompletion ℚ))) := by
    rw [coe_localLevelOne_top]; exact isOpen_localIntegralSet ℚ v
  have hKc : IsCompact ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
      Set (GL (Fin 2) (v.adicCompletion ℚ))) := by
    rw [coe_localLevelOne_top]; exact isCompact_localIntegralSet ℚ v

  have hBeq : {x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
      ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k} =
      ((unipotentGL2Hom (R := v.adicCompletion ℚ)).range : Set (GL (Fin 2) (v.adicCompletion ℚ))) *
        ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
          Set (GL (Fin 2) (v.adicCompletion ℚ))) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨n, hn, k, hk, rfl⟩; exact ⟨n, hn, k, hk, rfl⟩
    · rintro ⟨n, hn, k, hk, rfl⟩; exact ⟨n, hn, k, hk, rfl⟩
  have hBo : IsOpen {x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
      ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k} := by
    rw [hBeq]; exact hKo.mul_left
  have hBm := hBo.measurableSet

  obtain ⟨hvol, hlt⟩ := HaarQuotient.lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top μ₂
    (unipotentGL2Hom (R := v.adicCompletion ℚ)).range hN μN₂ (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) hKo hKc
  rw [← hBeq] at hvol hlt
  have hμB : (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂))
      {x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k} =
      ∫⁻ g, {x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}.indicator (fun _ => (1 : ENNReal)) g
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂)) := by
    rw [MeasureTheory.lintegral_indicator hBm, MeasureTheory.setLIntegral_const, one_mul]
  have hBtop : (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂))
      {x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k} < ⊤ := by
    rw [hμB]; exact hlt
  have hBpos : (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂))
      {x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k} ≠ 0 := by
    rw [hμB, hvol]
    refine (ENNReal.div_pos_iff.mpr ⟨?_, ?_⟩).ne'
    · exact (hKo.measure_pos μ₂ ⟨1, Subgroup.one_mem _⟩).ne'
    · exact ((hN.isClosedEmbedding_subtypeVal.isCompact_preimage hKc).measure_lt_top).ne

  have hint : ∀ s : ℂ, (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
      ({x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}.indicator (fun _ => (1 : ℂ)) g *
        {x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}.indicator (fun _ => (1 : ℂ)) g) *
        ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
            v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) =
      {x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}.indicator (fun _ => (1 : ℂ)) := by
    intro s
    funext g
    by_cases hg : g ∈ {x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}
    · rw [Set.indicator_of_mem hg, modulus_det_eq_one v hg, Complex.one_cpow, mul_one, mul_one]
    · rw [Set.indicator_of_notMem hg, zero_mul, zero_mul]
  refine ⟨((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂))
      {x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}).toReal,
    ENNReal.toReal_pos hBpos hBtop.ne, fun s => ?_, fun s => ?_⟩
  · rw [hint s, integrable_indicator_iff hBm]
    exact integrableOn_const hBtop.ne
  · unfold RSCarrier.rsLocalIntegral
    rw [hint s, MeasureTheory.integral_indicator_const _ hBm, Complex.real_smul, mul_one, measureReal_def]

end S_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsLocalIntegral_indicator_unipotent_mul_localLevelOne_eq
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsLocalIntegral_indicator_unipotent_mul_localLevelOne_eq (solution)
