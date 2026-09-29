-- Prove2me | solution 1 for NumberField.InfiniteAdeleRing.exists_lintegral_generalLinearGroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2_rowIsometry
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7c2f6e4d-46c0-5106-95dd-8e2c1c95ba16

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Theorems.Thm_NumberField_InfiniteAdeleRing_exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2
import Theorems.Thm_NumberField_InfiniteAdeleRing_exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup
import Theorems.Thm_MeasureTheory_Measure_exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer
import Theorems.Thm_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfiniteAdeleRing_exists_lintegral_generalLinearGroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2_rowIsometry
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply"
p2m_attr_erase "simp" "LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped ENNReal

attribute [local instance] AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open Topology

attribute [local instance] AutomorphicForm.glBorelOf AutomorphicForm.borelSpace_glBorelOf

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace ArchIwasawa

variable (K : Type) [Field K] [NumberField K]

abbrev G : Type := GL (Fin 2) (InfiniteAdeleRing K)

abbrev B : Subgroup (G K) := AutomorphicForm.borelSubgroup (InfiniteAdeleRing K)

abbrev Kc : Subgroup (G K) :=
  ⨅ w : InfinitePlace K, (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent K w)

@[reducible] scoped instance measB : MeasurableSpace ↥(B K) := borel _
scoped instance borelB : BorelSpace ↥(B K) := ⟨rfl⟩
@[reducible] scoped instance measKc : MeasurableSpace ↥(Kc K) := borel _
scoped instance borelKc : BorelSpace ↥(Kc K) := ⟨rfl⟩

scoped instance secondCountable_K : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology K

  have h : IsEmbedding (fun x : InfiniteAdeleRing K => ((x, (0 : FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K)) :=
    isEmbedding_prodMkLeft (0 : FiniteAdeleRing (𝓞 K) K)
  exact h.secondCountableTopology

scoped instance t2_M : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing K))
scoped instance lc_M : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing K))
scoped instance sc_M : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → InfiniteAdeleRing K))
scoped instance lc_G : LocallyCompactSpace (G K) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
scoped instance sc_G : SecondCountableTopology (G K) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem isClosed_B : IsClosed (B K : Set (G K)) := by
  have : (B K : Set (G K)) = (fun g : G K => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0) ⁻¹' {0} := by
    ext g; exact AutomorphicForm.mem_borelSubgroup_iff _
  rw [this]
  exact isClosed_singleton.preimage ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))).matrix_elem 1 0)

scoped instance lc_B : LocallyCompactSpace ↥(B K) := (isClosed_B K).locallyCompactSpace
scoped instance sc_B : SecondCountableTopology ↥(B K) := TopologicalSpace.Subtype.secondCountableTopology _
scoped instance sc_Kc : SecondCountableTopology ↥(Kc K) := TopologicalSpace.Subtype.secondCountableTopology _
scoped instance cpt_Kc : CompactSpace ↥(Kc K) := isCompact_iff_compactSpace.1 (NumberField.InfiniteAdeleRing.exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup K).2
scoped instance lc_Kc : LocallyCompactSpace ↥(Kc K) := ((NumberField.InfiniteAdeleRing.exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup K).2.isClosed).locallyCompactSpace

abbrev L : Type := ↥(B K) × ↥(Kc K)

scoped instance lc_L : LocallyCompactSpace (L K) := Prod.locallyCompactSpace _ _
scoped instance sc_L : SecondCountableTopology (L K) := inferInstance
scoped instance tg_L : IsTopologicalGroup (L K) := inferInstance

scoped instance action : MulAction (L K) (G K) where
  smul l g := (l.1 : G K) * g * ((l.2 : ↥(Kc K)) : G K)⁻¹
  one_smul g := by
    change ((1 : ↥(B K)) : G K) * g * (((1 : ↥(Kc K))) : G K)⁻¹ = g
    simp
  mul_smul l l' g := by
    change ((l * l').1 : G K) * g * (((l * l').2 : ↥(Kc K)) : G K)⁻¹ =
      (l.1 : G K) * ((l'.1 : G K) * g * ((l'.2 : ↥(Kc K)) : G K)⁻¹) * ((l.2 : ↥(Kc K)) : G K)⁻¹
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_inv_rev]
    group

theorem smul_def (l : L K) (g : G K) : l • g = (l.1 : G K) * g * ((l.2 : ↥(Kc K)) : G K)⁻¹ := rfl

scoped instance continuousSMul : ContinuousSMul (L K) (G K) := by
  refine ⟨?_⟩
  change Continuous fun p : L K × G K => (p.1.1 : G K) * p.2 * ((p.1.2 : ↥(Kc K)) : G K)⁻¹
  exact ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul continuous_snd).mul
    (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).inv

theorem exists_smul_one_eq (g : G K) : ∃ l : L K, l • (1 : G K) = g := by
  obtain ⟨b, hb, k, hk, rfl⟩ := (NumberField.InfiniteAdeleRing.exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup K).1 g
  refine ⟨(⟨b, hb⟩, ⟨k, hk⟩⁻¹), ?_⟩
  rw [smul_def]
  simp

scoped instance isPretransitive : MulAction.IsPretransitive (L K) (G K) := by
  refine ⟨fun g₁ g₂ => ?_⟩
  obtain ⟨l₁, h₁⟩ := exists_smul_one_eq K g₁
  obtain ⟨l₂, h₂⟩ := exists_smul_one_eq K g₂
  exact ⟨l₂ * l₁⁻¹, by rw [← h₁, ← h₂, mul_smul, inv_smul_smul]⟩

abbrev BK : Type := {k : ↥(Kc K) // (k : G K) ∈ B K}

scoped instance compactSpace_BK : CompactSpace (BK K) := by
  refine isCompact_iff_compactSpace.mp ?_
  exact ((isClosed_B K).preimage continuous_subtype_val).isCompact

def toStab (k : BK K) : L K := (⟨(k.1 : G K), k.2⟩, k.1)

theorem continuous_toStab : Continuous (toStab K) :=
  ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).prodMk continuous_subtype_val

theorem stabilizer_eq_range : (MulAction.stabilizer (L K) (1 : G K) : Set (L K)) = Set.range (toStab K) := by
  ext l
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, smul_def, mul_one, mul_inv_eq_one]
  constructor
  · intro h
    refine ⟨⟨l.2, ?_⟩, ?_⟩
    · rw [← h]; exact l.1.2
    · refine Prod.ext (Subtype.ext ?_) rfl
      exact h.symm
  · rintro ⟨k, rfl⟩; rfl

theorem isCompact_stabilizer : IsCompact (MulAction.stabilizer (L K) (1 : G K) : Set (L K)) := by
  rw [stabilizer_eq_range]; exact isCompact_range (continuous_toStab K)

theorem map_smul_eq (ν : Measure (G K)) [ν.IsHaarMeasure] (l : L K) :
    ν.map (fun g : G K => l • g) = ν := by
  haveI : ν.IsMulRightInvariant :=
    AutomorphicForm.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing K ν inferInstance
  have : (fun g : G K => l • g) = (fun g => (l.1 : G K) * g) ∘ (fun g => g * ((l.2 : ↥(Kc K)) : G K)⁻¹) := by
    funext g; rw [Function.comp_apply, smul_def, mul_assoc]
  rw [this, ← Measure.map_map (measurable_const_mul _) (measurable_mul_const _), map_mul_right_eq_self,
    map_mul_left_eq_self]

theorem isInvInvariant_of_compactSpace {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [μ.IsHaarMeasure] : μ.IsInvInvariant := by
  haveI : μ.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    have h := Measure.map_right_mul_eq_modularCharacterFun_smul μ g
    have huniv : (μ.map (· * g)) Set.univ = μ Set.univ := by
      rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
    have hc : Measure.modularCharacterFun g = 1 := by
      have h2 := congrArg (fun ν : Measure H => ν Set.univ) h
      simp only [huniv] at h2
      have hne : μ Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μ Set.univ_nonempty
      have htop : μ Set.univ ≠ ∞ := measure_ne_top μ _
      have : (Measure.modularCharacterFun g : ℝ≥0∞) = 1 := by
        rw [← ENNReal.mul_left_inj hne htop, one_mul]; exact h2.symm
      exact_mod_cast this
    rw [h, hc, one_smul]
  have h := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have huniv : μ.inv Set.univ = μ Set.univ := by
    rw [Measure.inv_def, Measure.map_apply measurable_inv MeasurableSet.univ, Set.preimage_univ]
  have hc : Measure.haarScalarFactor μ.inv μ = 1 := by
    have h2 := congrArg (fun ν : Measure H => ν Set.univ) h
    simp only [huniv] at h2
    have hne : μ Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μ Set.univ_nonempty
    have htop : μ Set.univ ≠ ∞ := measure_ne_top μ _
    have : (Measure.haarScalarFactor μ.inv μ : ℝ≥0∞) = 1 := by
      rw [← ENNReal.mul_left_inj hne htop, one_mul]; exact h2.symm
    exact_mod_cast this
  refine ⟨?_⟩
  rw [h, hc, one_smul]

def borelHaar : Measure ↥(B K) := Measure.haar

scoped instance isHaar_borelHaar : (borelHaar K).IsHaarMeasure := by unfold borelHaar; infer_instance

scoped instance sigmaFinite_borelHaar : SigmaFinite (borelHaar K) := by
  haveI : SigmaCompactSpace ↥(B K) := sigmaCompactSpace_of_locallyCompact_secondCountable
  infer_instance

def LHaar (κ : Measure ↥(Kc K)) : Measure (L K) := (borelHaar K).prod κ

scoped instance isHaar_LHaar (κ : Measure ↥(Kc K)) [κ.IsHaarMeasure] : (LHaar K κ).IsHaarMeasure := by
  unfold LHaar; infer_instance

end ArchIwasawa
p2m_reactivate "P2MW.S_NumberField_InfiniteAdeleRing_exists_lintegral_generalLinearGroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2_rowIsometry.ArchIwasawa"

end
p2m_reactivate "P2MW.S_NumberField_InfiniteAdeleRing_exists_lintegral_generalLinearGroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2_rowIsometry.ArchIwasawa"

set_option maxHeartbeats 6400000 in
open ArchIwasawa in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) ν)
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (lam : Measure (InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (ρ : Measure (InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    (κ : @Measure (↥(⨅ w : InfinitePlace K,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent K w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing K)))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ φ : GL (Fin 2) (InfiniteAdeleRing K) → ℝ≥0∞, Measurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] φ →
        @lintegral _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) ν φ =
          c * ∫⁻ u, ∫⁻ t, ∫⁻ x, @lintegral _ (borel _) κ (fun k =>
                φ (Matrix.GeneralLinearGroup.scalar (Fin 2) u * diagUnits2 t 1 * AutomorphicForm.unipotentGL2 x *
                  (k : GL (Fin 2) (InfiniteAdeleRing K)))) ∂lam ∂ρ ∂ρ := by
  classical
  letI mG : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
  haveI : Measure.IsHaarMeasure ν := hν
  haveI : Measure.IsHaarMeasure κ := hκ
  haveI : κ.IsInvInvariant := isInvInvariant_of_compactSpace κ
  haveI : SigmaFinite κ := inferInstance

  obtain ⟨c₁, hc₁top, hc₁⟩ :=
    MeasureTheory.Measure.exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer (LHaar K κ)
      (X := G K) (1 : G K) (isCompact_stabilizer K) ν (map_smul_eq K ν)
  have hc₁0 : c₁ ≠ 0 := by
    intro h0
    have : ν Set.univ = 0 := by rw [hc₁, h0, zero_smul]; rfl
    exact isOpen_univ.measure_ne_zero ν Set.univ_nonempty this

  obtain ⟨c₂, hc₂0, hc₂top, hc₂⟩ := NumberField.InfiniteAdeleRing.exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2 K lam ρ (borelHaar K) inferInstance
  refine ⟨c₁ * c₂, mul_ne_zero hc₁0 hc₂0, ENNReal.mul_ne_top hc₁top hc₂top, fun φ hφ => ?_⟩
  have hsm : Measurable fun l : L K => l • (1 : G K) := (continuous_id.smul continuous_const).measurable
  have hF : Measurable fun g : G K => ∫⁻ k, φ (g * (k : G K)) ∂κ := by
    refine Measurable.lintegral_prod_right ?_
    exact hφ.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).measurable
  calc ∫⁻ g, φ g ∂ν = c₁ * ∫⁻ l, φ (l • (1 : G K)) ∂(LHaar K κ) := by
        rw [hc₁, lintegral_smul_measure, lintegral_map hφ hsm, smul_eq_mul]
    _ = c₁ * ∫⁻ b, ∫⁻ k, φ ((b : G K) * ((k : G K))⁻¹) ∂κ ∂(borelHaar K) := by
        refine congrArg (fun z => c₁ * z) ?_
        rw [LHaar, lintegral_prod _ (show Measurable (fun l : L K => φ (l • (1 : G K))) from hφ.comp hsm).aemeasurable]
        refine lintegral_congr fun b => lintegral_congr fun k => ?_
        rw [smul_def, mul_one]
    _ = c₁ * ∫⁻ b, ∫⁻ k, φ ((b : G K) * (k : G K)) ∂κ ∂(borelHaar K) := by
        refine congrArg (fun z => c₁ * z) ?_
        refine lintegral_congr fun b => ?_
        have hψ : Measurable fun k : ↥(Kc K) => φ ((b : G K) * (k : G K)) :=
          hφ.comp (continuous_const.mul continuous_subtype_val).measurable
        calc ∫⁻ k, φ ((b : G K) * ((k : G K))⁻¹) ∂κ
            = ∫⁻ k, φ ((b : G K) * (k : G K)) ∂(κ.inv) := by
              rw [Measure.inv_def, lintegral_map hψ measurable_inv]
              rfl
          _ = _ := by rw [Measure.IsInvInvariant.inv_eq_self]
    _ = c₁ * (c₂ * ∫⁻ u, ∫⁻ t, ∫⁻ x, (∫⁻ k, φ (Matrix.GeneralLinearGroup.scalar (Fin 2) u * diagUnits2 t 1 *
          AutomorphicForm.unipotentGL2 x * (k : G K)) ∂κ) ∂lam ∂ρ ∂ρ) := by
        rw [hc₂ _ hF]
    _ = _ := by rw [mul_assoc]

end S_NumberField_InfiniteAdeleRing_exists_lintegral_generalLinearGroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2_rowIsometry
end P2MW
export P2MW.S_NumberField_InfiniteAdeleRing_exists_lintegral_generalLinearGroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2_rowIsometry (solution)
