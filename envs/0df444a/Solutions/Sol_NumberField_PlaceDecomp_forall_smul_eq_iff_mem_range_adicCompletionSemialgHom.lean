-- Prove2me | solution 1 for NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7ea374da-c7ea-51e5-910e-77d193e9f753

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Theorems.Thm_NumberField_PlaceDecomp_natCard_decomp_eq_ramificationIdx_mul_inertiaDeg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
open CategoryTheory IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

set_option maxHeartbeats 800000

namespace T1Proof

variable (K K'' : Type) [Field K] [NumberField K] [Field K''] [NumberField K''] [Algebra K K'']
  (v : HeightOneSpectrum (𝓞 K)) (W : v.Extension (𝓞 K''))

theorem smul_algebraMap_completion (σ : NumberField.PlaceDecomp.decomp K K'' W.1) (x : v.adicCompletion K) :
    σ • (algebraMap (v.adicCompletion K) (W.1.adicCompletion K'') x) =
      algebraMap (v.adicCompletion K) (W.1.adicCompletion K'') x := by
  have hι : ∀ z, algebraMap (v.adicCompletion K) (W.1.adicCompletion K'') z =
      HeightOneSpectrum.Extension.adicCompletionSemialgHom K K'' W z := fun _ => rfl
  have hf : Continuous (fun z : v.adicCompletion K => σ • algebraMap (v.adicCompletion K) (W.1.adicCompletion K'') z) := by
    have : (fun z : v.adicCompletion K => σ • algebraMap (v.adicCompletion K) (W.1.adicCompletion K'') z) =
        NumberField.PlaceDecomp.actRingEquiv σ ∘ HeightOneSpectrum.Extension.adicCompletionSemialgHom K K'' W := by
      funext z; simp only [Function.comp_apply, NumberField.PlaceDecomp.smul_def, hι]
    rw [this]
    exact (NumberField.PlaceDecomp.continuous_actRingEquiv σ).comp
      (HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous K K'' W)
  have hg : Continuous (fun z : v.adicCompletion K => algebraMap (v.adicCompletion K) (W.1.adicCompletion K'') z) := by
    simp only [hι]; exact HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous K K'' W
  have key := DenseRange.equalizer
    ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjective K v).denseRange.comp
      (UniformSpace.Completion.denseRange_coe (α := WithVal (v.valuation K)))
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v)) hf hg (by
    funext k
    show σ • algebraMap _ _ ((k : WithVal (v.valuation K)) : v.adicCompletion K) =
      algebraMap _ _ ((k : WithVal (v.valuation K)) : v.adicCompletion K)
    rw [hι, HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe, NumberField.PlaceDecomp.smul_def,
      NumberField.PlaceDecomp.actRingEquiv_coe, WithVal.congr_apply]
    congr 1
    congr 1
    show WithVal.toVal _ ((σ : K'' ≃ₐ[K] K'').toRingEquiv (algebraMap K K'' k.ofVal)) = _
    rw [AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    rfl)
  exact congrFun key x

theorem aux [IsGalois K K'']
    (hcard : Nat.card (NumberField.PlaceDecomp.decomp K K'' W.1) =
      Module.finrank (v.adicCompletion K) (W.1.adicCompletion K''))
    (y : W.1.adicCompletion K'') :
    (∀ σ : NumberField.PlaceDecomp.decomp K K'' W.1, σ • y = y) ↔
      y ∈ Set.range (HeightOneSpectrum.Extension.adicCompletionSemialgHom K K'' W) := by
  classical
  constructor
  · intro hy
    haveI := NumberField.PlaceDecomp.faithfulSMul_decomp K K'' W.1
    letI := Fintype.ofFinite (NumberField.PlaceDecomp.decomp K K'' W.1)
    let Fix : IntermediateField (v.adicCompletion K) (W.1.adicCompletion K'') :=
      Subfield.toIntermediateField (FixedPoints.subfield (NumberField.PlaceDecomp.decomp K K'' W.1) (W.1.adicCompletion K''))
        (fun x σ => smul_algebraMap_completion K K'' v W σ x)
    have h1 : Module.finrank Fix (W.1.adicCompletion K'') = Nat.card (NumberField.PlaceDecomp.decomp K K'' W.1) := by
      rw [Nat.card_eq_fintype_card]
      exact FixedPoints.finrank_eq_card (NumberField.PlaceDecomp.decomp K K'' W.1) (W.1.adicCompletion K'')
    have h2 := Module.finrank_mul_finrank (v.adicCompletion K) Fix (W.1.adicCompletion K'')
    rw [h1, ← hcard] at h2
    have hpos : 0 < Nat.card (NumberField.PlaceDecomp.decomp K K'' W.1) := Nat.card_pos
    have h3 : Module.finrank (v.adicCompletion K) Fix = 1 := by
      have := Nat.eq_of_mul_eq_mul_right hpos (h2.trans (one_mul _).symm)
      exact this
    have hbot : Fix = ⊥ := IntermediateField.finrank_eq_one_iff.1 h3
    have hyFix : y ∈ Fix := hy
    rw [hbot, IntermediateField.mem_bot] at hyFix
    exact hyFix
  · rintro ⟨x, rfl⟩
    intro σ
    exact smul_algebraMap_completion K K'' v W σ x

end T1Proof

open T1Proof NumberField.PlaceDecomp in
theorem solution
    (K K'' : Type) [Field K] [NumberField K] [Field K''] [NumberField K''] [Algebra K K''] [IsGalois K K'']
    (w'' : HeightOneSpectrum (𝓞 K'')) (y : w''.adicCompletion K'') :
    (∀ σ : decomp K K'' w'', σ • y = y) ↔
      y ∈ Set.range (HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
        (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w'').Extension (𝓞 K''))) := by
  exact aux K K'' (HeightOneSpectrum.under (𝓞 K) w'') ⟨w'', rfl⟩
    ((natCard_decomp_eq_ramificationIdx_mul_inertiaDeg K K'' w'').trans
      (HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank K K''
        (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w'').Extension (𝓞 K'')))) y

end S_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom
end P2MW
export P2MW.S_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom (solution)
