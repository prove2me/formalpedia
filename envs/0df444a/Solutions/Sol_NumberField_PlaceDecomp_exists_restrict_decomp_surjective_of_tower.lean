-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_restrict_decomp_surjective_of_tower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c449e4fc-414f-5e7c-ba2f-2e3a58eb2c9b

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_NumberField_PlaceTransport_stabilizer_eq_decomp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
open CategoryTheory IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

set_option maxHeartbeats 800000

namespace T2Proof
open scoped Pointwise NumberField.PlaceTransport

variable {E K K'' : Type} [Field E] [Field K] [NumberField K] [Field K''] [NumberField K'']
    [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K''] [Normal E K]

theorem coe_smul_ringOfIntegers {F L : Type} [Field F] [Field L] [NumberField L] [Algebra F L]
    (σ : L ≃ₐ[F] L) (x : 𝓞 L) : ((σ • x : 𝓞 L) : L) = σ (x : L) := rfl

omit [NumberField K] [NumberField K''] in
theorem restrictNormalHom_inv_apply (σ : K'' ≃ₐ[E] K'') (k : K) :
    algebraMap K K'' ((AlgEquiv.restrictNormalHom K σ)⁻¹ k) = σ⁻¹ (algebraMap K K'' k) := by
  rw [← map_inv]
  exact AlgEquiv.restrictNormal_commutes σ⁻¹ K k

theorem under_smul (σ : K'' ≃ₐ[E] K'') (w'' : HeightOneSpectrum (𝓞 K'')) :
    HeightOneSpectrum.under (𝓞 K) (σ • w'') = (AlgEquiv.restrictNormalHom K σ) • HeightOneSpectrum.under (𝓞 K) w'' := by
  apply HeightOneSpectrum.ext
  ext x
  rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff]
  show algebraMap (𝓞 K) (𝓞 K'') x ∈ (σ • w'').asIdeal ↔
    algebraMap (𝓞 K) (𝓞 K'') ((AlgEquiv.restrictNormalHom K σ)⁻¹ • x) ∈ w''.asIdeal
  have key : algebraMap (𝓞 K) (𝓞 K'') ((AlgEquiv.restrictNormalHom K σ)⁻¹ • x) = σ⁻¹ • algebraMap (𝓞 K) (𝓞 K'') x := by
    apply Subtype.ext
    show algebraMap K K'' ((((AlgEquiv.restrictNormalHom K σ)⁻¹ • x : 𝓞 K)) : K) = ((σ⁻¹ • algebraMap (𝓞 K) (𝓞 K'') x : 𝓞 K'') : K'')
    rw [coe_smul_ringOfIntegers, coe_smul_ringOfIntegers, restrictNormalHom_inv_apply]
    rfl
  rw [key, ← NumberField.PlaceTransport.mem_smul_asIdeal_iff]

omit [NumberField K] [NumberField K''] [Normal E K] in

theorem restrictScalars_smul (ρ : K'' ≃ₐ[K] K'') (w'' : HeightOneSpectrum (𝓞 K'')) :
    (AlgEquiv.restrictScalars E ρ) • w'' = ρ • w'' := by
  apply HeightOneSpectrum.ext
  ext x
  rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff, NumberField.PlaceTransport.mem_smul_asIdeal_iff]
  have : ((AlgEquiv.restrictScalars E ρ)⁻¹ • x : 𝓞 K'') = ρ⁻¹ • x := rfl
  rw [this]

omit [NumberField K] [NumberField K''] [Normal E K] in

theorem smul_asIdeal_eq_pointwise (ρ : K'' ≃ₐ[K] K'') (w'' : HeightOneSpectrum (𝓞 K'')) :
    (ρ • w'').asIdeal = ρ • w''.asIdeal := by
  rw [NumberField.PlaceTransport.smul_asIdeal_eq_map, Ideal.pointwise_smul_def]
  rfl

end T2Proof

open T2Proof NumberField.PlaceDecomp in
open scoped Pointwise NumberField.PlaceTransport in
theorem solution
    (E K K'' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
    [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K''] [IsGalois E K''] [Normal E K]
    (w'' : HeightOneSpectrum (𝓞 K'')) :
    ∃ r : decomp E K'' w'' →* decomp E K (HeightOneSpectrum.under (𝓞 K) w''),
      Function.Surjective r ∧
      (∀ σ : decomp E K'' w'', ((r σ : decomp E K (HeightOneSpectrum.under (𝓞 K) w'')) : K ≃ₐ[E] K) =
        AlgEquiv.restrictNormalHom K (σ : K'' ≃ₐ[E] K'')) ∧
      (∀ σ : decomp E K'' w'', r σ = 1 ↔ ∀ x : K, (σ : K'' ≃ₐ[E] K'') (algebraMap K K'' x) = algebraMap K K'' x) ∧
      (∀ τ : decomp K K'' w'', ∃ σ : decomp E K'' w'',
        (σ : K'' ≃ₐ[E] K'') = AlgEquiv.restrictScalars E (τ : K'' ≃ₐ[K] K'') ∧ r σ = 1) ∧
      (∀ (σ : decomp E K'' w'') (x : (HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K),
        HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
            (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w'').Extension (𝓞 K'')) (r σ • x) =
          σ • HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
            (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w'').Extension (𝓞 K'')) x) := by
  classical
  haveI : Normal E K'' := inferInstance
  haveI : IsGalois K K'' := IsGalois.tower_top_of_isGalois E K K''
  have hmem : ∀ σ : decomp E K'' w'', AlgEquiv.restrictNormalHom K (σ : K'' ≃ₐ[E] K'') ∈
      decomp E K (HeightOneSpectrum.under (𝓞 K) w'') := by
    intro σ
    rw [← NumberField.PlaceTransport.stabilizer_eq_decomp E K, MulAction.mem_stabilizer_iff, ← under_smul]
    have hσ : (σ : K'' ≃ₐ[E] K'') • w'' = w'' := MulAction.mem_stabilizer_iff.1 (by
      rw [NumberField.PlaceTransport.stabilizer_eq_decomp E K'' w'']; exact σ.2)
    rw [hσ]
  let r : decomp E K'' w'' →* decomp E K (HeightOneSpectrum.under (𝓞 K) w'') :=
    { toFun := fun σ => ⟨AlgEquiv.restrictNormalHom K (σ : K'' ≃ₐ[E] K''), hmem σ⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun σ τ => Subtype.ext (map_mul _ _ _) }
  have hr : ∀ σ : decomp E K'' w'', ((r σ : decomp E K (HeightOneSpectrum.under (𝓞 K) w'')) : K ≃ₐ[E] K) =
      AlgEquiv.restrictNormalHom K (σ : K'' ≃ₐ[E] K'') := fun _ => rfl

  have hker : ∀ σ : decomp E K'' w'', r σ = 1 ↔
      ∀ x : K, (σ : K'' ≃ₐ[E] K'') (algebraMap K K'' x) = algebraMap K K'' x := by
    intro σ
    rw [Subtype.ext_iff, hr, OneMemClass.coe_one, AlgEquiv.ext_iff]
    refine forall_congr' fun x => ?_
    rw [AlgEquiv.one_apply, ← (algebraMap K K'').injective.eq_iff]
    show algebraMap K K'' ((σ : K'' ≃ₐ[E] K'').restrictNormal K x) = algebraMap K K'' x ↔ _
    rw [AlgEquiv.restrictNormal_commutes]
  refine ⟨r, ?_, hr, hker, ?_, ?_⟩
  ·
    intro τ
    obtain ⟨σ₀, hσ₀⟩ := AlgEquiv.restrictNormalHom_surjective K'' (τ : K ≃ₐ[E] K)
    have hτ : (τ : K ≃ₐ[E] K) • HeightOneSpectrum.under (𝓞 K) w'' = HeightOneSpectrum.under (𝓞 K) w'' :=
      MulAction.mem_stabilizer_iff.1 (by rw [NumberField.PlaceTransport.stabilizer_eq_decomp E K]; exact τ.2)
    have hunder : HeightOneSpectrum.under (𝓞 K) (σ₀ • w'') = HeightOneSpectrum.under (𝓞 K) w'' := by
      rw [under_smul, hσ₀, hτ]
    haveI : (σ₀ • w'').asIdeal.LiesOver (HeightOneSpectrum.under (𝓞 K) w'').asIdeal :=
      ⟨(congrArg HeightOneSpectrum.asIdeal hunder).symm⟩
    haveI : w''.asIdeal.LiesOver (HeightOneSpectrum.under (𝓞 K) w'').asIdeal := ⟨rfl⟩
    haveI : (σ₀ • w'').asIdeal.IsMaximal := (σ₀ • w'').isMaximal
    haveI : w''.asIdeal.IsMaximal := w''.isMaximal
    obtain ⟨ρ, hρ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (HeightOneSpectrum.under (𝓞 K) w'').asIdeal
      (σ₀ • w'').asIdeal w''.asIdeal (K'' ≃ₐ[K] K'')
    have hσ : ((AlgEquiv.restrictScalars E ρ) * σ₀) • w'' = w'' := by
      rw [mul_smul, restrictScalars_smul]
      apply HeightOneSpectrum.ext
      rw [smul_asIdeal_eq_pointwise, hρ]
    refine ⟨⟨(AlgEquiv.restrictScalars E ρ) * σ₀, ?_⟩, ?_⟩
    · rw [← NumberField.PlaceTransport.stabilizer_eq_decomp E K'' w'', MulAction.mem_stabilizer_iff]
      exact hσ
    · apply Subtype.ext
      rw [hr]
      show AlgEquiv.restrictNormalHom K ((AlgEquiv.restrictScalars E ρ) * σ₀) = (τ : K ≃ₐ[E] K)
      rw [map_mul, hσ₀]
      convert one_mul (τ : K ≃ₐ[E] K)
      apply AlgEquiv.ext
      intro k
      apply (algebraMap K K'').injective
      rw [show AlgEquiv.restrictNormalHom K (AlgEquiv.restrictScalars E ρ) k =
          (AlgEquiv.restrictScalars E ρ).restrictNormal K k from rfl,
        AlgEquiv.restrictNormal_commutes, AlgEquiv.one_apply]
      exact ρ.commutes k
  ·
    intro τ
    have hτ : (AlgEquiv.restrictScalars E (τ : K'' ≃ₐ[K] K'')) ∈ decomp E K'' w'' := by
      have h2 := τ.2
      change (τ : K'' ≃ₐ[K] K'') ∈ MulAction.stabilizer (K'' ≃ₐ[K] K'') _ at h2
      change AlgEquiv.restrictScalars E (τ : K'' ≃ₐ[K] K'') ∈ MulAction.stabilizer (K'' ≃ₐ[E] K'') _
      rw [MulAction.mem_stabilizer_iff] at h2 ⊢
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      conv_rhs => rw [← h2]
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      exact Iff.rfl
    refine ⟨⟨_, hτ⟩, rfl, ?_⟩
    rw [hker]
    intro x
    exact (τ : K'' ≃ₐ[K] K'').commutes x
  ·
    intro σ x
    let v := (HeightOneSpectrum.under (𝓞 K) w'').valuation K
    let ι := HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
      (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w'').Extension (𝓞 K''))
    have hf : Continuous (fun y : (HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K => ι (r σ • y)) := by
      have : (fun y : (HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K => ι (r σ • y)) =
          ι ∘ NumberField.PlaceDecomp.actRingEquiv (r σ) := by
        funext y; simp only [Function.comp_apply, NumberField.PlaceDecomp.smul_def]
      rw [this]
      exact (HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous K K'' _).comp
        (NumberField.PlaceDecomp.continuous_actRingEquiv _)
    have hg : Continuous (fun y : (HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K => σ • ι y) := by
      have : (fun y : (HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K => σ • ι y) =
          NumberField.PlaceDecomp.actRingEquiv σ ∘ ι := by
        funext y; simp only [Function.comp_apply, NumberField.PlaceDecomp.smul_def]
      rw [this]
      exact (NumberField.PlaceDecomp.continuous_actRingEquiv σ).comp
        (HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous K K'' _)
    have key := DenseRange.equalizer
      ((HeightOneSpectrum.adicCompletion.ofCompletion_surjective K (HeightOneSpectrum.under (𝓞 K) w'')).denseRange.comp
        (UniformSpace.Completion.denseRange_coe (α := WithVal v))
        (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K _)) hf hg (by
      funext k
      show ι (r σ • ((k : WithVal v) : (HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K)) =
        σ • ι ((k : WithVal v) : (HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K)
      rw [NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.actRingEquiv_coe, WithVal.congr_apply,
        HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe,
        HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe,
        NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.actRingEquiv_coe, WithVal.congr_apply]
      congr 2
      show (WithVal.equiv (HeightOneSpectrum.valuation K'' w'')).symm
          (algebraMap K K'' (((r σ : decomp E K _) : K ≃ₐ[E] K).toRingEquiv k.ofVal)) = _
      rw [hr]
      show (WithVal.equiv (HeightOneSpectrum.valuation K'' w'')).symm
          (algebraMap K K'' (((σ : K'' ≃ₐ[E] K'').restrictNormal K) k.ofVal)) = _
      rw [AlgEquiv.restrictNormal_commutes]
      rfl)
    exact congrFun key x

end S_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower (solution)
