-- Prove2me | solution 1 for GlobalTheory.LocFlat.PartialFourier.partial_fourier_inversion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:10:41.631276+00:00
-- url     : https://prove2.me/submissions/151eb526-042f-4f56-bdbd-b6edd82d7311

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialFourierInversion
import Theorems.Thm_GlobalTheory_LocFlat_PartialFourier_partial_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_inversion_pi
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isCompact_int
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_pos
import Theorems.Thm_GlobalTheory_SplitWeil_conductor_exists
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_int
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_measureReal_cball
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_pos
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.PartialFourier
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.LocFlat.PartialFourier
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (I : Type) [Fintype I], ∃ C : ℝ, 0 < C ∧ ∀ (J : Type) [Fintype J] (a : I → k), ∀ f ∈ SB ((I → k) × (J → k)), Integrable (fun l : I → k => ∫ x : (I → k) × (J → k), f x * (ψ (l ⬝ᵥ x.1) : ℂ) ∂((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν))) (Measure.pi fun _ => ν) ∧ ∫ l : I → k, (ψ (-(l ⬝ᵥ a)) : ℂ) * (∫ x : (I → k) × (J → k), f x * (ψ (l ⬝ᵥ x.1) : ℂ) ∂((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν))) ∂(Measure.pi fun _ => ν) = (C : ℂ) * ∫ y : J → k, f (a, y) ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ ψ ν hψ hne hν I _
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ hne
  have hO : 0 < ν.real (𝒪[k] : Set k) :=
    ENNReal.toReal_pos ((isOpen_int k).measure_pos ν ⟨0, zero_mem _⟩).ne' (isCompact_int k).measure_lt_top.ne
  have hpsi : ∀ u : k, (ψ (-u) : ℂ) * ψ u = 1 := by
    intro u
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
  refine ⟨(nabs k c * ν.real (𝒪[k] : Set k) ^ 2) ^ Fintype.card I, by have := nabs_pos k c; positivity,
    fun J _ a f hf => ?_⟩
  set μI : Measure (I → k) := Measure.pi fun _ => ν with hμI
  set μJ : Measure (J → k) := Measure.pi fun _ => ν with hμJ
  set g : (I → k) → ℂ := fun x₁ => ∫ y, f (x₁, y) ∂μJ with hgdef
  have hg : g ∈ SB (I → k) := partial_mem_SB ν hf
  have hF : ∀ l : I → k, ∫ x, f x * (ψ (l ⬝ᵥ x.1) : ℂ) ∂(μI.prod μJ) = ∫ x₁, g x₁ * (ψ (x₁ ⬝ᵥ l) : ℂ) ∂μI := by
    intro l
    have hfi : Integrable f (μI.prod μJ) := hf.1.continuous.integrable_of_hasCompactSupport hf.2
    have hi : Integrable (fun x => f x * (ψ (l ⬝ᵥ x.1) : ℂ)) (μI.prod μJ) :=
      hfi.mul_bdd (c := 1)
        ((continuous_subtype_val.comp (hψ.comp (continuous_const.dotProduct continuous_fst))).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun q => (Circle.norm_coe _).le)
    rw [integral_prod _ hi]
    congr 1
    funext x₁
    simp only [hgdef, ← integral_mul_const, dotProduct_comm l]
  simp only [hF]
  refine ⟨?_, ?_⟩
  · have := FourierPi.fourier_mem_SB μI hc hg
    exact this.1.continuous.integrable_of_hasCompactSupport this.2
  · set h : (I → k) → ℂ := fun x => g (x + a) with hhdef
    have hh : h ∈ SB (I → k) :=
      ⟨hg.1.comp_continuous (continuous_add_const a), hg.2.comp_homeomorph (Homeomorph.addRight a)⟩
    have htr : ∀ l : I → k, (ψ (-(l ⬝ᵥ a)) : ℂ) * ∫ x₁, g x₁ * (ψ (x₁ ⬝ᵥ l) : ℂ) ∂μI =
        ∫ x, h x * (ψ (x ⬝ᵥ l) : ℂ) ∂μI := by
      intro l
      rw [← integral_const_mul, ← integral_add_right_eq_self _ a]
      congr 1
      funext x
      have e1 : (x + a) ⬝ᵥ l = x ⬝ᵥ l + l ⬝ᵥ a := by rw [add_dotProduct, dotProduct_comm a l]
      rw [hhdef, e1, AddChar.map_add_eq_mul, Circle.coe_mul]
      linear_combination (g (x + a) * (ψ (x ⬝ᵥ l) : ℂ)) * hpsi (l ⬝ᵥ a)
    simp only [htr]
    obtain ⟨s, hs⟩ := FourierPi.fourier_inversion_pi μI hc hh
    have hb : ∀ r : kˣ, μI.real (FourierPi.box I r) = ν.real (cball r) ^ Fintype.card I := by
      intro r
      simp [hμI, Measure.real, FourierPi.box, Measure.pi_pi]
    rw [hs, hb, hb, ← mul_pow, measureReal_cball, measureReal_cball]
    have h4 : nabs k c = nabs k s * nabs k (c * s⁻¹) := by
      rw [← nabs_mul, mul_comm, inv_mul_cancel_right]
    simp only [hhdef, zero_add, hgdef, h4]
    push_cast
    ring
end GlobalTheory.LocFlat.PartialFourier
