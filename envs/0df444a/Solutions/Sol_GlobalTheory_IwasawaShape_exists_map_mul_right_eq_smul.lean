-- Prove2me | solution 1 for GlobalTheory.IwasawaShape.exists_map_mul_right_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:39.260523+00:00
-- url     : https://prove2.me/submissions/466dcf4b-edae-40a0-8cec-bde09ce172c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMapMulRightEqSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.IwasawaShape
variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
namespace GlobalTheory.IwasawaShape
theorem _root_.solution (P : Subgroup G) (hP : MeasurableSet (P : Set G)) (ρ : Measure G)
    [SigmaFinite ρ] (h0 : ρ (P : Set G)ᶜ = 0) (hinv : ∀ s ∈ P, ρ.map (fun g => s * g) = ρ)
    (T : Set G) (hT : MeasurableSet T) (hT0 : ρ T ≠ 0) (hT1 : ρ T ≠ ⊤) (l : G) (hl : l ∈ P) :
    ∃ D : ENNReal, D ≠ 0 ∧ D ≠ ⊤ ∧ ρ.map (fun g => g * l) = D • ρ := by
  classical
  have e : MeasurableEmbedding (Subtype.val : P → G) := MeasurableEmbedding.subtype_coe hP
  have : MeasurableMul₂ P := ⟨e.measurable_comp_iff.1
    ((measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd))⟩
  have : MeasurableInv P := ⟨e.measurable_comp_iff.1 measurable_subtype_coe.inv⟩
  set ρ' : Measure P := ρ.comap Subtype.val with hρ'
  have hmap : ρ'.map Subtype.val = ρ := by
    rw [hρ', e.map_comap, Subtype.range_coe_subtype, Measure.restrict_eq_self_of_ae_mem]
    exact ae_iff.2 h0
  have inj : ∀ α β : Measure P, α.map Subtype.val = β.map Subtype.val → α = β := fun α β h => by
    rw [← e.comap_map α, ← e.comap_map β, h]
  have : SigmaFinite ρ' :=
    SigmaFinite.of_map ρ' measurable_subtype_coe.aemeasurable (by rw [hmap]; infer_instance)
  have : ρ'.IsMulLeftInvariant := ⟨fun s => inj _ _ (by
    rw [Measure.map_map measurable_subtype_coe (measurable_const_mul s)]
    have hc : (Subtype.val ∘ fun x : P => s * x) = (fun g : G => (s : G) * g) ∘ Subtype.val := rfl
    rw [hc, ← Measure.map_map (measurable_const_mul _) measurable_subtype_coe, hmap, hinv s s.2])⟩
  let l' : P := ⟨l, hl⟩
  set ν' : Measure P := ρ'.map (fun x => x * l') with hν'
  have : ν'.IsMulLeftInvariant := ⟨fun s => by
    rw [hν', Measure.map_map (measurable_const_mul s) (measurable_mul_const l')]
    have hc : ((fun x : P => s * x) ∘ fun x => x * l') = (fun x => x * l') ∘ (fun x => s * x) := by
      funext x; simp [Function.comp, mul_assoc]
    rw [hc, ← Measure.map_map (measurable_mul_const l') (measurable_const_mul s), map_mul_left_eq_self]⟩
  have : SigmaFinite ν' := SigmaFinite.of_map ν' (measurable_mul_const l'⁻¹).aemeasurable (by
    rw [hν', Measure.map_map (measurable_mul_const _) (measurable_mul_const _)]
    have hc : ((fun x : P => x * l'⁻¹) ∘ fun x => x * l') = id := by funext x; simp
    rw [hc, Measure.map_id]; infer_instance)
  have hρT' : ρ' (Subtype.val ⁻¹' T) = ρ T := by
    rw [hρ', e.comap_apply, Set.image_preimage_eq_inter_range]
    exact measure_inter_conull (by rw [Subtype.range_coe_subtype]; exact h0)
  have hEq := measure_eq_div_smul ν' ρ' (s := Subtype.val ⁻¹' T) (by rw [hρT']; exact hT0)
    (by rw [hρT']; exact hT1)
  set D := ν' (Subtype.val ⁻¹' T) / ρ' (Subtype.val ⁻¹' T) with hD
  have hmapD : ρ.map (fun g => g * l) = D • ρ := by
    conv_lhs => rw [← hmap]
    rw [Measure.map_map (measurable_mul_const l) measurable_subtype_coe]
    have hc : ((fun g : G => g * l) ∘ Subtype.val) = Subtype.val ∘ (fun x : P => x * l') := rfl
    rw [hc, ← Measure.map_map measurable_subtype_coe (measurable_mul_const l'), ← hν', hEq,
      Measure.map_smul, hmap]
  have huniv : (ρ.map fun g => g * l) Set.univ ≠ 0 := by
    rw [Measure.map_apply (measurable_mul_const l) MeasurableSet.univ, Set.preimage_univ]
    exact fun h => hT0 (measure_mono_null (Set.subset_univ _) h)
  have hD0 : D ≠ 0 := by
    intro h
    apply huniv
    rw [hmapD, h, zero_smul, Measure.coe_zero, Pi.zero_apply]
  have hD1 : D ≠ ⊤ := by
    intro h
    have : SigmaFinite (ρ.map fun g => g * l) :=
      SigmaFinite.of_map _ (measurable_mul_const l⁻¹).aemeasurable (by
        rw [Measure.map_map (measurable_mul_const _) (measurable_mul_const _)]
        have hc : ((fun g : G => g * l⁻¹) ∘ fun g => g * l) = id := by funext x; simp
        rw [hc, Measure.map_id]; infer_instance)
    obtain ⟨n, hn⟩ : ∃ n, (ρ.map fun g => g * l) (spanningSets (ρ.map fun g => g * l) n) ≠ 0 := by
      by_contra hne
      push Not at hne
      apply huniv
      rw [← iUnion_spanningSets (ρ.map fun g => g * l)]
      exact measure_iUnion_null hne
    have hlt := measure_spanningSets_lt_top (ρ.map fun g => g * l) n
    set Sn := spanningSets (ρ.map fun g => g * l) n
    rw [hmapD, Measure.smul_apply, smul_eq_mul, h] at hn hlt
    rcases eq_or_ne (ρ Sn) 0 with h' | h'
    · exact hn (by rw [h', mul_zero])
    · rw [ENNReal.top_mul h'] at hlt
      exact lt_irrefl _ hlt
  exact ⟨D, hD0, hD1, hmapD⟩
end GlobalTheory.IwasawaShape
