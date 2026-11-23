-- Prove2me | solution 1 for GlobalTheory.exists_continuous_extension_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:33.936964+00:00
-- url     : https://prove2.me/submissions/e6492c51-bf77-48bc-bccd-de97f6278836

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsContinuousExtensionAdicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory
open NumberField IsDedekindDomain
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (E : Type) [Field E] [NumberField E] (l : ℕ)
    [Fact l.Prime] (τ : E →+* _root_.Formalism.ConjugateSelfDual.Qbar l) (v : HeightOneSpectrum (𝓞 E))
    (h : ∀ x : E, v.valuation E x < 1 ↔ ‖τ x‖ < 1) :
    ∃ j : v.adicCompletion E →+* _root_.Formalism.ConjugateSelfDual.Qbar l, Continuous j ∧
      j.comp (algebraMap E (v.adicCompletion E)) = τ := by
  unfold _root_.Formalism.ConjugateSelfDual.Qbar at τ h ⊢

  let b := Module.finBasis ℚ E
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) :=
    IntermediateField.adjoin ℚ_[l] (Set.range fun i => τ (b i))
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  have hmem : ∀ x, τ x ∈ K := by
    intro x
    rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem K _)
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)

  let g : WithVal (v.valuation E) →+* PadicAlgCl l := τ.comp (WithVal.equiv (v.valuation E)).toRingHom
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E v
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  have hπ1 : ‖τ π‖ < 1 := (h π).1 (by rw [hπ]; decide)
  have hπpos : 0 < ‖τ π‖ := norm_pos_iff.2 ((map_ne_zero τ).2 hπ0)
  have hg : Continuous g := by
    refine continuous_of_continuousAt_zero g ?_
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hπ1
    let y : WithVal (v.valuation E) := (WithVal.equiv (v.valuation E)).symm (π ^ n)
    have hy : Valued.v.restrict y ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact (map_ne_zero _).2 (pow_ne_zero n hπ0)
    rw [Filter.Eventually, Valued.mem_nhds_zero]
    refine ⟨Units.mk0 _ hy, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx ⊢
    have hz : v.valuation E (WithVal.equiv (v.valuation E) x) < v.valuation E (π ^ n) := hx
    have hπn : v.valuation E (π ^ n) ≠ 0 := by
      rw [map_pow, hπ]; exact pow_ne_zero _ (WithZero.coe_ne_zero)
    have hq : v.valuation E (WithVal.equiv (v.valuation E) x / π ^ n) < 1 := by
      rw [map_div₀]
      exact (div_lt_one₀ (zero_lt_iff.2 hπn)).2 hz
    have hτq := (h _).1 hq
    rw [map_div₀, map_pow, norm_div, norm_pow, div_lt_one (pow_pos hπpos n)] at hτq
    rw [dist_zero_right]
    exact lt_trans hτq hn
  let τ' : WithVal (v.valuation E) →+* K :=
    (τ.codRestrict K hmem).comp (WithVal.equiv (v.valuation E)).toRingHom
  have hτ' : Continuous τ' := continuous_induced_rng.2 hg
  let ext : (v.valuation E).Completion →+* K := UniformSpace.Completion.extensionHom τ' hτ'
  let φ : v.adicCompletion E →+* (v.valuation E).Completion :=
    { toFun := HeightOneSpectrum.adicCompletion.toCompletion
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφ : Continuous φ := uniformContinuous_comap.continuous
  refine ⟨(algebraMap K (PadicAlgCl l)).comp (ext.comp φ), ?_, ?_⟩
  · exact continuous_subtype_val.comp (UniformSpace.Completion.continuous_extension.comp hφ)
  · ext x
    simp only [RingHom.comp_apply, HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply]
    change ((ext ((WithVal.equiv (v.valuation E)).symm (algebraMap E E x) : (v.valuation E).Completion) : K) :
      PadicAlgCl l) = τ x
    rw [UniformSpace.Completion.extensionHom_coe]
    rfl
end _root_.GlobalTheory
end GlobalTheory
