-- Prove2me | solution 1 for GlobalTheory.automorphyFactor_exp_linear_of_cube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:11.479801+00:00
-- url     : https://prove2.me/submissions/15216234-059b-48a1-8f27-845ff9cd4439

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AutomorphyFactorExpLinearOfCube
import Theorems.Thm_GlobalTheory_entire_hom_eq_cexp_fderiv
import Theorems.Thm_GlobalTheory_clm_eq_of_cexp_eq
import Theorems.Thm_GlobalTheory_prod_finset_fin_three

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z + l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∀ (fr : ι → (Fin g → ℂ) → ℂ) (κ : ℂ), ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Set.univ)) ∧ (∀ i z, z ∈ W i → z ∈ Set.univ → fr i z ≠ 0) ∧ (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Set.univ → fr i z = c i j z * fr j z)) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) → ∃ (a : Λ → ℂ) (B : Λ →+ ((Fin g → ℂ) →ₗ[ℂ] ℂ)), (∀ l, a l ≠ 0) ∧ (∀ l m : Λ, a (l + m) = a l * a m * cexp (B l m)) ∧ ∀ (l : Λ) i z, z ∈ W i → fr i z = a l * cexp (B l z) * fr i (z + l)) := by
  intro g ι W c hWo hcov _ _ _ T _ hT0 _ Λ _ _ hWp hcp hTp fr κ ⟨hfd, hf0, hfc⟩ hcube
  choose σ hσ using hcov
  have hf0' : ∀ i z, z ∈ W i → fr i z ≠ 0 := fun i z hz => hf0 i z hz (Set.mem_univ _)
  have hfa : ∀ i z, z ∈ W i → DifferentiableAt ℂ (fr i) z := fun i z hz => by
    have := hfd i
    rw [Set.inter_univ] at this
    exact this.differentiableAt ((hWo i).mem_nhds hz)
  let α : Λ → (Fin g → ℂ) → ℂ := fun l z => fr (σ z) z / fr (σ z) (z + l)
  have hα : ∀ (l : Λ) i z, z ∈ W i → α l z = fr i z / fr i (z + l) := by
    intro l i z hz
    have hzl : z + l ∈ W i := (hWp i z l l.2).2 hz
    have hzl' : z + l ∈ W (σ z) := (hWp _ z l l.2).2 (hσ z)
    have e1 := hfc (σ z) i z (hσ z) hz (Set.mem_univ _)
    have e2 := hfc (σ z) i (z + l) hzl' hzl (Set.mem_univ _)
    rw [hcp _ _ z l l.2] at e2
    have hc0 : c (σ z) i z ≠ 0 := by
      intro h
      rw [h, zero_mul] at e1
      exact hf0' _ _ (hσ z) e1
    show fr (σ z) z / fr (σ z) (z + l) = _
    rw [e1, e2, mul_div_mul_left _ _ hc0]
  have hα0 : ∀ (l : Λ) z, α l z ≠ 0 := fun l z =>
    div_ne_zero (hf0' _ _ (hσ z)) (hf0' _ _ ((hWp _ z l l.2).2 (hσ z)))
  have hαd : ∀ l : Λ, Differentiable ℂ (α l) := by
    intro l z
    have hzl' : z + l ∈ W (σ z) := (hWp _ z l l.2).2 (hσ z)
    have h1 : DifferentiableAt ℂ (fun w => fr (σ z) (w + l)) z :=
      (hfa _ _ hzl').comp z (differentiableAt_id.add_const _)
    have h2 : DifferentiableAt ℂ (fun w => fr (σ z) w / fr (σ z) (w + l)) z := by
      simp only [div_eq_mul_inv]
      exact (hfa _ _ (hσ z)).mul (h1.inv (hf0' _ _ hzl'))
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [(hWo (σ z)).mem_nhds (hσ z)] with w hw
    exact hα l _ w hw
  have hαc : ∀ (l m : Λ) z, α (l + m) z = α l z * α m (z + l) := by
    intro l m z
    have hzl' : z + l ∈ W (σ z) := (hWp _ z l l.2).2 (hσ z)
    rw [hα (l + m) _ z (hσ z), hα l _ z (hσ z), hα m _ (z + l) hzl', Submodule.coe_add,
      ← add_assoc]
    have := hf0' _ _ hzl'
    field_simp
  have hcubeα : ∀ (l : Λ) y z, α l (y + z) * α l 0 = α l y * α l z := by
    intro l y z
    let x : Fin 3 → Fin g → ℂ := ![0, y, z]
    let L : Fin 3 → Fin g → ℂ := ![l, 0, 0]
    have hL : ∀ a, L a ∈ Λ := by
      intro a
      fin_cases a
      · exact l.2
      · exact Λ.zero_mem
      · exact Λ.zero_mem
    let j : Finset (Fin 3) → ι := fun I => σ (∑ a ∈ I, x a)
    have hj : ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I) := fun I => hσ _
    have hs : ∀ I : Finset (Fin 3), ∑ a ∈ I, (x + L) a = ∑ a ∈ I, x a + ∑ a ∈ I, L a := by
      intro I
      simp only [Pi.add_apply, Finset.sum_add_distrib]
    have hj' : ∀ I : Finset (Fin 3), ∑ a ∈ I, (x + L) a ∈ W (j I) := by
      intro I
      rw [hs]
      exact (hWp _ _ _ (Λ.sum_mem fun a _ => hL a)).2 (hj I)
    have e1 := hcube j x hj
    have e2 := hcube j (x + L) hj'
    have hκ : κ ≠ 0 := by
      intro h
      rw [h, zero_mul] at e1
      exact hT0 j x hj e1
    rw [hTp j x L hL, e1] at e2
    have e3 := mul_left_cancel₀ hκ e2
    have e4 : ∏ I : Finset (Fin 3), (fr (j I) (∑ a ∈ I, x a) /
        fr (j I) (∑ a ∈ I, x a + ∑ a ∈ I, L a)) ^ ((-1 : ℤ) ^ (3 - I.card)) = 1 := by
      simp only [div_zpow, Finset.prod_div_distrib]
      simp only [hs] at e3
      rw [← e3]
      exact div_self (Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (hf0' _ _ (hj I)))
    have hz : ∀ (m : Λ) w, (m : Fin g → ℂ) = 0 → α m w = 1 := by
      intro m w hm
      show fr (σ w) w / fr (σ w) (w + m) = 1
      rw [hm, add_zero]
      exact div_self (hf0' _ _ (hσ w))
    have hl : ∀ (m : Λ) w w', (m : Fin g → ℂ) = l → w = w' → α m w = α l w' := by
      intro m w w' hm hw
      rw [Subtype.ext hm, hw]
    let F : Finset (Fin 3) → ℂ := fun I =>
      α ⟨∑ a ∈ I, L a, Λ.sum_mem fun a _ => hL a⟩ (∑ a ∈ I, x a)
    have e6 : ∏ I : Finset (Fin 3), F I ^ ((-1 : ℤ) ^ (3 - I.card)) = 1 := e4
    have f0 : F ∅ = 1 := hz _ _ (by simp)
    have f1 : F {0} = α l 0 := hl _ _ _ (by simp [L]) (by simp [x])
    have f2 : F {1} = 1 := hz _ _ (by simp [L])
    have f3 : F {2} = 1 := hz _ _ (by simp [L])
    have f4 : F {0, 1} = α l y := hl _ _ _ (by simp [L]) (by simp [x])
    have f5 : F {0, 2} = α l z := hl _ _ _ (by simp [L]) (by simp [x])
    have f6 : F {1, 2} = 1 := hz _ _ (by simp [L])
    have f7 : F {0, 1, 2} = α l (y + z) := hl _ _ _ (by simp [L]) (by simp [x])
    clear e4
    have e4 := e6
    rw [prod_finset_fin_three, f0, f1, f2, f3, f4, f5, f6, f7] at e4
    have c1 : ({0} : Finset (Fin 3)).card = 1 := rfl
    have c2 : ({0, 1} : Finset (Fin 3)).card = 2 := rfl
    have c3 : ({0, 2} : Finset (Fin 3)).card = 2 := rfl
    have c4 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := rfl
    rw [c1, c2, c3, c4] at e4
    norm_num at e4
    have := hα0 l y
    have := hα0 l z
    field_simp at e4
    linear_combination e4
  let B₀ : Λ → ((Fin g → ℂ) →L[ℂ] ℂ) := fun l => fderiv ℂ (fun z => α l z / α l 0) 0
  have hexp : ∀ (l : Λ) z, α l z = α l 0 * cexp (B₀ l z) := by
    intro l z
    have h0 := hα0 l 0
    have := entire_hom_eq_cexp_fderiv (fun z => α l z / α l 0)
      (by simp only [div_eq_mul_inv]; exact (hαd l).mul_const _)
      (div_self h0) (fun y z => by
        have := hcubeα l y z
        field_simp
        linear_combination this) z
    show _ = _ * cexp (fderiv ℂ (fun z => α l z / α l 0) 0 z)
    rw [← this]
    field_simp
  have ha : ∀ l m : Λ, α (l + m) 0 = α l 0 * α m 0 * cexp (B₀ l m) := by
    intro l m
    rw [add_comm, hαc, zero_add, hexp l m]
    ring
  have hBadd : ∀ l m : Λ, B₀ (l + m) = B₀ l + B₀ m := by
    intro l m
    apply clm_eq_of_cexp_eq
    intro z
    have e := hαc m l z
    rw [add_comm m l, hexp (l + m), hexp m, hexp l, ha, map_add, Complex.exp_add] at e
    rw [ContinuousLinearMap.add_apply, Complex.exp_add]
    have h1 : α l 0 * α m 0 * cexp (B₀ l m) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (hα0 _ _) (hα0 _ _)) (Complex.exp_ne_zero _)
    apply mul_left_cancel₀ h1
    linear_combination e
  refine ⟨fun l => α l 0, AddMonoidHom.mk' (fun l => (B₀ l).toLinearMap) ?_, fun l => hα0 l 0,
    ha, ?_⟩
  · intro l m
    rw [hBadd]; rfl
  · intro l i z hz
    have e := hexp l z
    rw [hα l i z hz, div_eq_iff (hf0' _ _ ((hWp _ z l l.2).2 hz))] at e
    exact e
end GlobalTheory
