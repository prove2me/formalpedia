-- Prove2me | solution 1 for Ideal.exists_forall_map_localization_eq_span_of_finite_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0034f01a-94e9-5c10-8719-0e0c4bd40f44

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_forall_map_localization_eq_span_of_finite_maximal

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

universe u

theorem solution
    (P : Type u) [CommRing P] [IsNoetherianRing P] (J : Ideal P)
    (hfin : {𝔫 : Ideal P | 𝔫.IsMaximal ∧ J ≤ 𝔫}.Finite) (N : ℕ)
    (hloc : ∀ (𝔫 : Ideal P) [𝔫.IsMaximal], J ≤ 𝔫 →
      ∃ g : Fin N → P, (∀ i, g i ∈ J) ∧
        Ideal.map (algebraMap P (Localization.AtPrime 𝔫)) J =
          Ideal.span (Set.range fun i => algebraMap P (Localization.AtPrime 𝔫) (g i))) :
    ∃ f : Fin N → P, (∀ i, f i ∈ J) ∧
      ∀ (𝔫 : Ideal P) [𝔫.IsMaximal], J ≤ 𝔫 →
        Ideal.map (algebraMap P (Localization.AtPrime 𝔫)) J =
          Ideal.span (Set.range fun i => algebraMap P (Localization.AtPrime 𝔫) (f i)) := by
  classical
  set T : Set (Ideal P) := {𝔫 : Ideal P | 𝔫.IsMaximal ∧ J ≤ 𝔫} with hT

  have key : ∀ 𝔫 : Ideal P, 𝔫 ∈ T → ∃ g : Fin N → P, (∀ i, g i ∈ J) ∧
      ∀ x ∈ J, ∃ s : P, s ∉ 𝔫 ∧ s * x ∈ Ideal.span (Set.range g) := by
    rintro 𝔫 ⟨hmax, hJ⟩
    haveI := hmax
    obtain ⟨g, hgJ, hg⟩ := hloc 𝔫 hJ
    refine ⟨g, hgJ, fun x hx => ?_⟩
    have h1 : algebraMap P (Localization.AtPrime 𝔫) x ∈
        (Ideal.span (Set.range g)).map (algebraMap P (Localization.AtPrime 𝔫)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      change _ ∈ Ideal.span (Set.range fun i => algebraMap P (Localization.AtPrime 𝔫) (g i))
      rw [← hg]
      exact Ideal.mem_map_of_mem _ hx
    obtain ⟨⟨y, s⟩, hys⟩ := (IsLocalization.mem_map_algebraMap_iff 𝔫.primeCompl _).1 h1
    rw [← map_mul] at hys
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists 𝔫.primeCompl _).1 hys
    refine ⟨c * s, 𝔫.primeCompl.mul_mem c.2 s.2, ?_⟩
    rw [show (c : P) * s * x = c * (x * s) by ring]
    change (c : P) * (x * ((y, s) : _ × _).2) ∈ _
    rw [hc]
    exact Ideal.mul_mem_left _ _ y.2
  choose! G hGJ hG using key

  have he : ∀ 𝔫 : Ideal P, 𝔫 ∈ T → ∃ e : P, e ∉ 𝔫 ∧ ∀ 𝔫' ∈ T, 𝔫' ≠ 𝔫 → e ∈ 𝔫' := by
    intro 𝔫 h𝔫
    have hpick : ∀ 𝔫' : Ideal P, 𝔫' ∈ hfin.toFinset.erase 𝔫 → ∃ a : P, a ∈ 𝔫' ∧ a ∉ 𝔫 := by
      intro 𝔫' h𝔫'
      obtain ⟨hne, h𝔫'F⟩ := Finset.mem_erase.1 h𝔫'
      have h𝔫'T : 𝔫' ∈ T := (Set.Finite.mem_toFinset hfin).1 h𝔫'F
      by_contra hcon
      exact hne (h𝔫'T.1.eq_of_le h𝔫.1.ne_top fun x hx => by_contra fun hx' => hcon ⟨x, hx, hx'⟩)
    choose! a ha using hpick
    refine ⟨∏ 𝔫' ∈ hfin.toFinset.erase 𝔫, a 𝔫', ?_, ?_⟩
    · refine Finset.prod_induction _ (fun x => x ∉ 𝔫) (fun x y hx hy hxy => (h𝔫.1.isPrime.mem_or_mem hxy).elim hx hy)
        (fun h1 => h𝔫.1.ne_top ((Ideal.eq_top_iff_one _).2 h1)) ?_
      intro 𝔫' h𝔫'
      exact (ha 𝔫' h𝔫').2
    · intro 𝔫' h𝔫'T hne
      have hmem : 𝔫' ∈ hfin.toFinset.erase 𝔫 :=
        Finset.mem_erase.2 ⟨hne, (Set.Finite.mem_toFinset hfin).2 h𝔫'T⟩
      rw [← Finset.mul_prod_erase _ _ hmem]
      exact Ideal.mul_mem_right _ _ (ha 𝔫' hmem).1
  choose! E hE𝔫 hE using he

  let f : Fin N → P := fun i => ∑ 𝔫 ∈ hfin.toFinset, E 𝔫 * G 𝔫 i
  have hfJ : ∀ i, f i ∈ J := fun i =>
    Ideal.sum_mem _ fun 𝔫 h𝔫 => J.mul_mem_left _ (hGJ 𝔫 ((Set.Finite.mem_toFinset hfin).1 h𝔫) i)
  refine ⟨f, hfJ, ?_⟩
  intro 𝔫 inst hJ𝔫
  have h𝔫T : 𝔫 ∈ T := ⟨inst, hJ𝔫⟩
  have h𝔫F : 𝔫 ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).2 h𝔫T
  set S := Localization.AtPrime 𝔫 with hS
  set M : Ideal S := J.map (algebraMap P S) with hM
  set N' : Ideal S := Ideal.span (Set.range fun i => algebraMap P S (f i)) with hN'
  have hN'eq : N' = (Ideal.span (Set.range f)).map (algebraMap P S) := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  have hN'M : N' ≤ M := by
    rw [hN'eq]
    exact Ideal.map_mono (Ideal.span_le.2 (Set.range_subset_iff.2 hfJ))
  refine le_antisymm ?_ hN'M
  have h𝔫S : 𝔫.map (algebraMap P S) = IsLocalRing.maximalIdeal S := Localization.AtPrime.map_eq_maximalIdeal

  set K : Ideal S := N' ⊔ IsLocalRing.maximalIdeal S • M with hK
  have hK : ∀ i, algebraMap P S (G 𝔫 i) ∈ K := by
    intro i
    have hsplit : E 𝔫 * G 𝔫 i = f i - ∑ 𝔫' ∈ hfin.toFinset.erase 𝔫, E 𝔫' * G 𝔫' i := by
      rw [eq_sub_iff_add_eq]
      exact Finset.add_sum_erase _ (fun 𝔫' => E 𝔫' * G 𝔫' i) h𝔫F
    have hrest : ∑ 𝔫' ∈ hfin.toFinset.erase 𝔫, E 𝔫' * G 𝔫' i ∈ 𝔫 * J := by
      refine Ideal.sum_mem _ fun 𝔫' h𝔫' => ?_
      obtain ⟨hne, h𝔫'F⟩ := Finset.mem_erase.1 h𝔫'
      have h𝔫'T : 𝔫' ∈ T := (Set.Finite.mem_toFinset hfin).1 h𝔫'F
      exact Ideal.mul_mem_mul (hE 𝔫' h𝔫'T 𝔫 h𝔫T hne.symm) (hGJ 𝔫' h𝔫'T i)
    have hunit : IsUnit (algebraMap P S (E 𝔫)) :=
      IsLocalization.map_units S (⟨E 𝔫, hE𝔫 𝔫 h𝔫T⟩ : 𝔫.primeCompl)
    rw [← Ideal.unit_mul_mem_iff_mem _ hunit, ← map_mul, hsplit, map_sub]
    refine K.sub_mem (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
    · exact Ideal.subset_span ⟨i, rfl⟩
    · rw [Ideal.smul_eq_mul, ← h𝔫S, hM, ← Ideal.map_mul]
      exact Ideal.mem_map_of_mem _ hrest

  have hMK : M ≤ K := by
    rw [hM, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    obtain ⟨s, hs𝔫, hsx⟩ := hG 𝔫 h𝔫T x hx
    have hunit : IsUnit (algebraMap P S s) := IsLocalization.map_units S (⟨s, hs𝔫⟩ : 𝔫.primeCompl)
    rw [← Ideal.unit_mul_mem_iff_mem _ hunit, ← map_mul]
    have hle : (Ideal.span (Set.range (G 𝔫))).map (algebraMap P S) ≤ K := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact hK i
    exact hle (Ideal.mem_map_of_mem _ hsx)

  exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian M)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥) hMK

end S_Ideal_exists_forall_map_localization_eq_span_of_finite_maximal
end P2MW
export P2MW.S_Ideal_exists_forall_map_localization_eq_span_of_finite_maximal (solution)
