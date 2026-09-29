-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.joint_expansion_comp_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/8650ea58-172f-5532-8f13-6c05481a7fef

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_joint_expansion_comp_mul_right

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

namespace WsC
namespace H2

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction

noncomputable section

theorem whittaker3_comp_mul_right (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (k' g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ (fun x => v (x * k')) g =
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ v (g * k') := by
  simp only [whittaker3, mul_assoc]

theorem main
    (ρ : ℝ) (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ) (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (cv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hexp :
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => cv i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
        ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ v
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
          (∑ i : Fin n, ∑ j : Fin J, cv i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
        C * y₁ ^ (ρ + δ)) ∧
        (∀ i j i' j', Continuous (cv' i j i' j')) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
        ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖cv i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, cv' i j i' j' k *
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ)))
    (k' : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => (fun i j y k => cv i j y (k * k')) i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
        ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (fun g => v (g * k'))
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
          (∑ i : Fin n, ∑ j : Fin J, (fun i j y k => cv i j y (k * k')) i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
        C * y₁ ^ (ρ + δ)) ∧
        (∀ i j i' j', Continuous ((fun i j i' j' k => cv' i j i' j' (k * k')) i j i' j')) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
        ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖(fun i j y k => cv i j y (k * k')) i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, (fun i j i' j' k => cv' i j i' j' (k * k')) i j i' j' k *
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ)) := by
  obtain ⟨hcont, hexp₁, hcont', hexp₂⟩ := hexp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    have hf : Continuous (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => ((p.1, p.2 * k') : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ)) :=
      continuous_fst.prodMk (continuous_snd.mul continuous_const)
    have hmaps : Set.MapsTo (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => ((p.1, p.2 * k') : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ))
        {p | 0 < p.1} {p | 0 < p.1} := fun p hp => hp
    exact (hcont i j).comp hf.continuousOn hmaps
  · intro K hK b hb
    obtain ⟨C, hC⟩ := hexp₁ ((fun k => k * k') '' K) (hK.image (continuous_mul_const k')) b hb
    refine ⟨C, fun k hk y₂ hlo hhi y₁ hy₁ hy₁' => ?_⟩
    have h := hC (k * k') ⟨k, hk, rfl⟩ y₂ hlo hhi y₁ hy₁ hy₁'
    rw [whittaker3_comp_mul_right]
    simpa only [mul_assoc] using h
  · intro i j i' j'
    exact (hcont' i j i' j').comp (continuous_mul_const k')
  · intro K hK
    obtain ⟨C, hC⟩ := hexp₂ ((fun k => k * k') '' K) (hK.image (continuous_mul_const k'))
    exact ⟨C, fun k hk i j y₂ hy₂ hy₂' => hC (k * k') ⟨k, hk, rfl⟩ i j y₂ hy₂ hy₂'⟩

end

end WsC.H2

theorem solution
    (ρ : ℝ) (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ) (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (cv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hexp :
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => cv i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
        ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ v
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
          (∑ i : Fin n, ∑ j : Fin J, cv i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
        C * y₁ ^ (ρ + δ)) ∧
        (∀ i j i' j', Continuous (cv' i j i' j')) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
        ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖cv i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, cv' i j i' j' k *
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ)))
    (k' : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => (fun i j y k => cv i j y (k * k')) i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
        ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (fun g => v (g * k'))
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
          (∑ i : Fin n, ∑ j : Fin J, (fun i j y k => cv i j y (k * k')) i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
        C * y₁ ^ (ρ + δ)) ∧
        (∀ i j i' j', Continuous ((fun i j i' j' k => cv' i j i' j' (k * k')) i j i' j')) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
        ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖(fun i j y k => cv i j y (k * k')) i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, (fun i j i' j' k => cv' i j i' j' (k * k')) i j i' j' k *
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ)) := by
  exact WsC.H2.main ρ n J e δ v cv cv' hexp k'

end S_LanglandsTunnell_CubicInduction_joint_expansion_comp_mul_right
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_joint_expansion_comp_mul_right (solution)
