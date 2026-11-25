-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.UnitRep.exists_good_on_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:48:07.684442+00:00
-- url     : https://prove2.me/submissions/c798d92e-8ae7-42a7-a7a6-367ef7c1f318

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormRepresentsUnit
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitRep_hform_self_fixed
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitRep_hform_self_congr
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitRep_exists_hform_not_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitRep_comap_isMaximal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitRep_isCoprime_of_mem_not_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix HeckeCharacterZeroLocus.SiegelWeilU
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.UnitRep
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.CompanionTheory.SW.UnitRep
theorem _root_.solution [Finite (MaximalSpectrum A)] (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y)
    (h2 : IsUnit (2 : A)) (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ) (m : ℕ)
    (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (hJ : ∀ i j, σ (J j i) = J i j)
    (hdet : IsUnit J.det) (T : Finset (MaximalSpectrum A)) :
    ∃ x, ∀ p ∈ T, hform σ J x x ∉ p.asIdeal := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert q T _ ih =>
    obtain ⟨x, hx⟩ := ih
    by_cases hxq : hform σ J x x ∈ q.asIdeal
    swap
    · refine ⟨x, fun p hp => ?_⟩
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact hxq
      · exact hx p hp
    obtain ⟨y, hy⟩ := exists_hform_not_mem σ hσ h2 hδ m J hdet q.asIdeal q.isMaximal
    have hfix := hform_self_fixed σ hσ J hJ x
    have hmemc : ∀ {P : Ideal A}, hform σ J x x ∈ P → hform σ J x x ∈ P.comap σ := fun h => by
      rw [Ideal.mem_comap, hfix]; exact h
    have hnotc : ∀ {P : Ideal A}, hform σ J x x ∉ P → hform σ J x x ∉ P.comap σ := fun h h' => by
      rw [Ideal.mem_comap, hfix] at h'; exact h h'
    have hqm := q.isMaximal
    have hqc := comap_isMaximal σ hσ q.asIdeal q.isMaximal
    have hL : ∀ {Q : Ideal A}, Q.IsMaximal → hform σ J x x ∉ Q →
        IsCoprime (q.asIdeal * q.asIdeal.comap σ) Q := fun hQ hn =>
      IsCoprime.mul_left (isCoprime_of_mem_not_mem hqm hQ hxq hn)
        (isCoprime_of_mem_not_mem hqc hQ (hmemc hxq) hn)
    have hK₁ : IsCoprime (q.asIdeal * q.asIdeal.comap σ) (⨅ p ∈ T, p.asIdeal) :=
      Ideal.isCoprime_biInf fun p hp => hL p.isMaximal (hx p hp)
    have hK₂ : IsCoprime (q.asIdeal * q.asIdeal.comap σ) (⨅ p ∈ T, p.asIdeal.comap σ) :=
      Ideal.isCoprime_biInf fun p hp =>
        hL (comap_isMaximal σ hσ _ p.isMaximal) (hnotc (hx p hp))
    obtain ⟨u, hu, c, hc, huc⟩ := Ideal.isCoprime_iff_exists.1 (hK₁.mul_right hK₂)
    have hc₁ : ∀ p ∈ T, c ∈ p.asIdeal := fun p hp =>
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (Ideal.mul_le_left hc) p) hp
    have hc₂ : ∀ p ∈ T, σ c ∈ p.asIdeal := fun p hp =>
      Ideal.mem_comap.1 ((Submodule.mem_iInf _).1
        ((Submodule.mem_iInf _).1 (Ideal.mul_le_right hc) p) hp)
    have hu₁ : u ∈ q.asIdeal := Ideal.mul_le_right (I := q.asIdeal.comap σ) (by rwa [mul_comm] at hu)
    have hu₂ : σ u ∈ q.asIdeal := Ideal.mem_comap.1 (Ideal.mul_le_left (J := q.asIdeal) (by rwa [mul_comm] at hu))
    refine ⟨u • x + c • y, fun p hp => ?_⟩
    have hu' : u = 1 - c := by rw [← huc]; ring
    rcases Finset.mem_insert.1 hp with rfl | hp
    · intro hz
      refine hy ?_
      have h := hform_self_congr σ J p.asIdeal y (u • x + c • y)
        (fun i => ?_) (fun i => ?_)
      · simpa using p.asIdeal.sub_mem hz h
      · have : (u • x + c • y) i - y i = u * (x i - y i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this]
        exact p.asIdeal.mul_mem_right _ hu₁
      · have : (u • x + c • y) i - y i = u * (x i - y i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this, map_mul]
        exact p.asIdeal.mul_mem_right _ hu₂
    · intro hz
      refine hx p hp ?_
      have h := hform_self_congr σ J p.asIdeal x (u • x + c • y)
        (fun i => ?_) (fun i => ?_)
      · simpa using p.asIdeal.sub_mem hz h
      · have : (u • x + c • y) i - x i = c * (y i - x i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this]
        exact p.asIdeal.mul_mem_right _ (hc₁ p hp)
      · have : (u • x + c • y) i - x i = c * (y i - x i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this, map_mul]
        exact p.asIdeal.mul_mem_right _ (hc₂ p hp)
end GlobalTheory.CompanionTheory.SW.UnitRep
