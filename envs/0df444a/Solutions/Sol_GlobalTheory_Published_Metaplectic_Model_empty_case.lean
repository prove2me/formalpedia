-- Prove2me | solution 1 for GlobalTheory.Published.Metaplectic.Model.empty_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:09:12.152382+00:00
-- url     : https://prove2.me/submissions/e2afe458-72df-4da0-873f-a455189f4489

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HolPartShear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.Metaplectic GlobalTheory.Published.Metaplectic.Model
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.Published.Metaplectic.Model
theorem _root_.solution (ι : Type) [Fintype ι] [DecidableEq ι] [IsEmpty ι] :
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G)
      (pr : G →* symplecticGroup ι ℝ)
      (Ω : G →* (Lp ℂ 2 (volume : Measure (ι → ℝ)) →L[ℂ] Lp ℂ 2 (volume : Measure (ι → ℝ))))
      (ω : G →* (𝓢(ι → ℝ, ℂ) →L[ℂ] 𝓢(ι → ℝ, ℂ))) (φ₀ : 𝓢(ι → ℝ, ℂ)),
      Function.Surjective pr ∧ IsCoveringMap pr ∧ Nat.card pr.ker = 2 ∧
      (∀ g f, ‖Ω g f‖ = ‖f‖) ∧ (∀ f, Continuous fun g => Ω g f) ∧
      (∀ g (φ : 𝓢(ι → ℝ, ℂ)), Ω g (φ.toLp 2) = (ω g φ).toLp 2) ∧
      (Continuous fun x : G × 𝓢(ι → ℝ, ℂ) => ω x.1 x.2) ∧
      (∀ g w φ, ω g (rho w φ) = rho (act (pr g).1 w) (ω g φ)) ∧
      (∀ g, pr g = 1 → g ≠ 1 → ∀ φ, ω g φ = -φ) ∧
      (∀ x, φ₀ x = cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))) ∧
      (∀ g, (∫ x, ω g φ₀ x * conj (φ₀ x)) ^ 2 * (holPart (pr g).1).det = (∫ x, φ₀ x * conj (φ₀ x)) ^ 2) ∧
      (∀ g, (pr g).1ᵀ * (pr g).1 = 1 → ∃ c : ℂ, c ^ 2 * (holPart (pr g).1).det = 1 ∧ ω g φ₀ = c • φ₀) := by
  have hs : Subsingleton (symplecticGroup ι ℝ) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have hsq : ∀ g : ℤˣ, (((g : ℤ) : ℂ)) ^ 2 = 1 := by
    intro g; rcases Int.units_eq_one_or g with rfl | rfl <;> simp
  let φ₀ : 𝓢(ι → ℝ, ℂ) := (HasCompactSupport.of_compactSpace (fun _ : ι → ℝ => (1 : ℂ))).toSchwartzMap contDiff_const
  refine ⟨ℤˣ, inferInstance, inferInstance, inferInstance, 1, sgnRep _, sgnRep _, φ₀, fun a => ⟨1, Subsingleton.elim _ _⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨inferInstance, Set.univ, trivial, isOpen_univ, isOpen_discrete _, ?_⟩
    have : Finite ((1 : ℤˣ →* symplecticGroup ι ℝ) ⁻¹' {x}) := inferInstance
    refine ⟨Equiv.toHomeomorphOfDiscrete
      { toFun := fun g => (⟨x, trivial⟩, ⟨g.1, Subsingleton.elim _ _⟩)
        invFun := fun y => ⟨y.2.1, trivial⟩
        left_inv := fun _ => rfl
        right_inv := fun y => Prod.ext (Subtype.ext (Subsingleton.elim _ _)) rfl }, fun _ => Subsingleton.elim _ _⟩
  · simp
  · intro g f
    rcases Int.units_eq_one_or g with rfl | rfl <;> simp [sgnRep]
  · intro f; exact continuous_of_discreteTopology
  · intro g φ
    change ((g : ℤ) : ℂ) • SchwartzMap.toLpCLM ℂ ℂ 2 volume φ = SchwartzMap.toLpCLM ℂ ℂ 2 volume (((g : ℤ) : ℂ) • φ)
    rw [map_smul]
  · change Continuous fun x : ℤˣ × 𝓢(ι → ℝ, ℂ) => (((x.1 : ℤ) : ℂ)) • x.2
    exact ((continuous_of_discreteTopology (f := fun g : ℤˣ => ((g : ℤ) : ℂ))).comp continuous_fst).smul continuous_snd
  · intro g w φ
    rw [Subsingleton.elim (act _ w) w]
    simp [sgnRep]
  · intro g _ hg φ
    rcases Int.units_eq_one_or g with rfl | rfl
    · exact absurd rfl hg
    · simp [sgnRep]
  · intro x; simp [φ₀, dotProduct]
  · intro g
    rcases Int.units_eq_one_or g with rfl | rfl <;> simp [sgnRep, integral_neg]
  · intro g _
    exact ⟨_, by simp [hsq g], rfl⟩
end GlobalTheory.Published.Metaplectic.Model
