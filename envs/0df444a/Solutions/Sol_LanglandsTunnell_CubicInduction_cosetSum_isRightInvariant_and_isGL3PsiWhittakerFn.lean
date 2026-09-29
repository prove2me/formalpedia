-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.cosetSum_isRightInvariant_and_isGL3PsiWhittakerFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/003ebb2a-305b-5653-b99a-64440058d457

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_cosetSum_isRightInvariant_and_isGL3PsiWhittakerFn

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField
open LanglandsTunnell.CubicInduction

private theorem rightInvariant_cosetSum_of_cosetSystem {G : Type*} [Group G] {U : Subgroup G} {gen : G}
    {ι : Type} [Fintype ι] {reps : ι → G} (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U gen reps) {W : G → ℂ}
    (hW : IsRightInvariant U W) : IsRightInvariant U (cosetSum reps W) := by
  intro g u hu
  have hcov : ∀ i, ∃ j, (QuotientGroup.mk (u * reps i) : G ⧸ U) = QuotientGroup.mk (reps j) := fun i =>
    hsys.covers _ (HeckePair.mul_mem_doubleCoset (hsys.mem_doubleCoset i) hu)
  choose σ hσ using hcov
  have hterm : ∀ i, W (g * u * reps i) = W (g * reps (σ i)) := by
    intro i
    have hmem : (u * reps i)⁻¹ * reps (σ i) ∈ U := QuotientGroup.eq.mp (hσ i)
    calc W (g * u * reps i) = W (g * u * reps i * ((u * reps i)⁻¹ * reps (σ i))) := (hW _ _ hmem).symm
      _ = W (g * reps (σ i)) := by congr 1; group
  have hinj : Function.Injective σ := by
    intro i j hij
    apply hsys.mk_injective
    show (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps j)
    have h₁ : (QuotientGroup.mk (u * reps i) : G ⧸ U) = QuotientGroup.mk (u * reps j) := by rw [hσ i, hσ j, hij]
    have h₂ : (u * reps i)⁻¹ * (u * reps j) = (reps i)⁻¹ * reps j := by group
    rw [QuotientGroup.eq] at h₁ ⊢
    rwa [h₂] at h₁
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hinj
  simp only [cosetSum]
  calc ∑ i, W (g * u * reps i) = ∑ i, W (g * reps (σ i)) := Finset.sum_congr rfl fun i _ => hterm i
    _ = ∑ j, W (g * reps j) := Equiv.sum_comp (Equiv.ofBijective σ hbij) fun j => W (g * reps j)

private theorem whittakerLaw_cosetSum {F : Type} [CommRing F] (ψ : AddChar F ℂ) {ι : Type} [Fintype ι]
    (reps : ι → GL (Fin 3) F) {W : GL (Fin 3) F → ℂ} (hW : IsGL3PsiWhittakerFn ψ W) :
    IsGL3PsiWhittakerFn ψ (cosetSum reps W) := by
  intro x y z g
  simp only [cosetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, hW]

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (U : Subgroup (LocalGL3 v)) (gen : LocalGL3 v)
    {ι : Type} [Fintype ι] (reps : ι → LocalGL3 v) (W : LocalGL3 v → ℂ) :
    (HeckeIntegralSeam.IsHeckeCosetSystem U gen reps → IsRightInvariant U W → IsRightInvariant U (cosetSum reps W)) ∧
    (IsGL3PsiWhittakerFn ψv W → IsGL3PsiWhittakerFn ψv (cosetSum reps W)) :=
  ⟨fun hsys hW => rightInvariant_cosetSum_of_cosetSystem hsys hW, fun hW => whittakerLaw_cosetSum ψv reps hW⟩

end S_LanglandsTunnell_CubicInduction_cosetSum_isRightInvariant_and_isGL3PsiWhittakerFn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_cosetSum_isRightInvariant_and_isGL3PsiWhittakerFn (solution)
