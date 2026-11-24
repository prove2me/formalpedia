-- Prove2me | solution 1 for GlobalTheory.UnfoldNormal.map_conj_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:48:21.359674+00:00
-- url     : https://prove2.me/submissions/0ad5ee06-e0ba-40c4-8cfb-f2d0e2c58ab1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMapConjNormalizingLatticeEqSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Function
open scoped Pointwise
open GlobalTheory GlobalTheory.UnfoldNormal
namespace GlobalTheory.UnfoldNormal
theorem _root_.solution (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (Γ N : Subgroup H) (hΓ : Countable Γ) (hNc : IsClosed (N : Set H))
    (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N) (hκ : κ.IsHaarMeasure)
    (h𝓝 : IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ) (hfin : κ 𝓝 ≠ ⊤)
    (γ : H) (hγ : γ ∈ Γ) :
    κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ := by
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : LocallyCompactSpace N := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : Countable (Γ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨(x : N), x.2⟩ : Γ)) ?_
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    simpa using congrArg Subtype.val hab
  set e := conjEquiv N γ (hN γ hγ) (hN γ⁻¹ (Γ.inv_mem hγ)) with he_def
  have hfun : (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = ⇑e := rfl
  rw [hfun]
  haveI : (κ.map e).IsHaarMeasure := e.isHaarMeasure_map κ
  have hsm : κ.map e = Measure.haarScalarFactor (κ.map e) κ • κ :=
    Measure.isMulLeftInvariant_eq_smul (κ.map e) κ
  set c := Measure.haarScalarFactor (κ.map e) κ

  have hqmp : Measure.QuasiMeasurePreserving e κ κ :=
    ⟨e.continuous.measurable, by rw [hsm]; exact Measure.smul_absolutelyContinuous⟩
  have hpre : IsFundamentalDomain (Γ.subgroupOf N) (e ⁻¹' 𝓝) κ := by
    refine h𝓝.preimage_of_equiv hqmp (e := fun g : Γ.subgroupOf N =>
      (⟨⟨γ⁻¹ * (g : H) * γ⁻¹⁻¹, hN γ⁻¹ (Γ.inv_mem hγ) _ (g : N).2⟩,
        by
          show γ⁻¹ * (g : H) * γ⁻¹⁻¹ ∈ Γ
          exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) g.2) (Γ.inv_mem (Γ.inv_mem hγ))⟩ : Γ.subgroupOf N)) ?_ ?_
    · constructor
      · intro a b hab
        apply Subtype.ext; apply Subtype.ext
        have := congrArg (fun x : Γ.subgroupOf N => ((x : N) : H)) hab
        simpa using this
      · intro g
        refine ⟨⟨⟨γ * (g : H) * γ⁻¹, hN γ hγ _ (g : N).2⟩, ?_⟩, ?_⟩
        · show γ * (g : H) * γ⁻¹ ∈ Γ
          exact Γ.mul_mem (Γ.mul_mem hγ g.2) (Γ.inv_mem hγ)
        · apply Subtype.ext; apply Subtype.ext; simp [mul_assoc]
    · intro g x
      apply Subtype.ext
      simp [he_def, conjEquiv, Subgroup.smul_def, mul_assoc]
  have hmeq : κ (e ⁻¹' 𝓝) = κ 𝓝 := hpre.measure_eq h𝓝
  have hmap : κ.map e 𝓝 = κ (e ⁻¹' 𝓝) := by
    have := e.toHomeomorph.toMeasurableEquiv.map_apply (μ := κ) 𝓝
    exact this
  have hne : κ 𝓝 ≠ 0 := h𝓝.measure_ne_zero (NeZero.ne κ)
  have hc : (c : ENNReal) * κ 𝓝 = 1 * κ 𝓝 := by
    have h' : (c • κ) 𝓝 = κ 𝓝 := by rw [← hsm, hmap, hmeq]
    rw [one_mul]
    conv_rhs => rw [← h']
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hc1 : (c : ENNReal) = 1 := (ENNReal.mul_left_inj hne hfin).1 hc
  have : c = 1 := by exact_mod_cast hc1
  rw [hsm, this, one_smul]
end GlobalTheory.UnfoldNormal
