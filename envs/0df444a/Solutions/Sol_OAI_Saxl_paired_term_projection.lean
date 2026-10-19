-- Prove2me | solution 1 for OAI.Saxl.paired_term_projection
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:04:21.04819+00:00
-- url     : https://prove2.me/submissions/527b4bea-ef56-4e9a-b936-7322e84b722f

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension
import Definitions.Def_OAI_RepresentationTheory_Saxl_SizedStrips
import Definitions.Def_OAI_RepresentationTheory_Saxl_HorizontalRemoval
import Definitions.Def_OAI_RepresentationTheory_Saxl_YoungRule
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_RepeatedProjection

open OAI OAI.Saxl
open scoped TensorProduct
universe uX
theorem h42_pair_key {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : Function.Injective (fun i => (t i, a i)))
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) (g h : H)
    (π : Equiv.Perm (Fin n))
    (hs : ∀ i, (a (g.val i)).val + (a (h.val i)).val = (t (π i)).val) : h = ω * g := by
  classical
  let A : Fin n → ℤ := fun j => ((a j).val : ℤ)
  let Tt : Fin n → ℤ := fun j => ((t j).val : ℤ)
  let k : Equiv.Perm (Fin n) := h.val * g.val⁻¹
  have hkH : k ∈ H := mul_mem h.2 (inv_mem g.2)
  have hk : ∀ j, Tt (k j) = Tt j := fun j => by
    show ((t (k j)).val : ℤ) = (t j).val; rw [ht ⟨k, hkH⟩ j]
  have hωt : ∀ j, Tt (ω.val j) = Tt j := fun j => by
    show ((t (ω.val j)).val : ℤ) = (t j).val; rw [ht ω j]
  have hω' : ∀ j, A j + A (ω.val j) = Tt j := fun j => by
    simp only [A, Tt]; exact_mod_cast hω j
  have hs' : ∀ j, A j + A (k j) = Tt (π (g.val⁻¹ j)) := by
    intro j
    have := hs (g.val⁻¹ j)
    have e1 : g.val (g.val⁻¹ j) = j := by simp
    have e2 : h.val (g.val⁻¹ j) = k j := rfl
    rw [e1, e2] at this
    show ((a j).val : ℤ) + (a (k j)).val = (t (π (g.val⁻¹ j))).val
    exact_mod_cast this
  have S1 : ∑ j, (A j + A (k j))^2 = ∑ j, Tt j ^ 2 := by
    simp_rw [hs']
    exact Equiv.sum_comp ((g.val⁻¹ : Equiv.Perm (Fin n)).trans π) (fun x => Tt x ^ 2)
  have S2 : ∑ j, A (k j) * Tt j = ∑ j, A j * Tt j := by
    calc ∑ j, A (k j) * Tt j = ∑ j, A (k j) * Tt (k j) :=
          Finset.sum_congr rfl (fun j _ => by rw [hk])
      _ = _ := Equiv.sum_comp k (fun x => A x * Tt x)
  have S3 : ∑ j, A (ω.val j) * Tt j = ∑ j, A j * Tt j := by
    calc ∑ j, A (ω.val j) * Tt j = ∑ j, A (ω.val j) * Tt (ω.val j) :=
          Finset.sum_congr rfl (fun j _ => by rw [hωt])
      _ = _ := Equiv.sum_comp ω.val (fun x => A x * Tt x)
  have T2 : ∑ j, Tt j ^ 2 = 2 * ∑ j, A j * Tt j := by
    have : ∀ j, Tt j ^ 2 = A j * Tt j + A (ω.val j) * Tt j := by
      intro j; rw [← add_mul, hω' j]; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, S3]; ring
  have hz : ∑ j, (A j + A (k j) - Tt j)^2 = 0 := by
    have : ∀ j, (A j + A (k j) - Tt j)^2 =
        (A j + A (k j))^2 - 2 * (A j * Tt j) - 2 * (A (k j) * Tt j) + Tt j ^ 2 := by
      intro j; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, S1, S2, T2]
    ring
  have hpt : ∀ j, A j + A (k j) = Tt j := by
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (A j + A (k j) - Tt j))).1 hz j
      (Finset.mem_univ _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  have hkω : ∀ j, k j = ω.val j := by
    intro j
    apply ha
    have e1 : A (k j) = A (ω.val j) := by linarith [hpt j, hω' j]
    have e2 : t (k j) = t (ω.val j) := by rw [ht ⟨k, hkH⟩ j, ht ω j]
    simp only [A] at e1
    exact Prod.ext e2 (Fin.ext (by exact_mod_cast e1))
  apply Subtype.ext
  have hk' : k = ω.val := Equiv.ext hkω
  rw [Subgroup.coe_mul, ← hk']
  simp [k]

theorem solution {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : Function.Injective (fun i => (t i, a i)))
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) (g h : H) :
    orbitProjection t (pairSumMap n d e (Pi.single
      (mergeWords (a ∘ g.val) (a ∘ h.val)) 1)) =
      if h = ω*g then Pi.single t 1 else 0 := by
  classical
  have hval : ∀ b, pairSumMap n d e (Pi.single (mergeWords (a ∘ g.val) (a ∘ h.val)) 1) b =
      if ∀ i, (a (g.val i)).val + (a (h.val i)).val = (b i).val then 1 else 0 := by
    intro b
    unfold pairSumMap
    rw [wordMap_single]
    simp only [mergeWords, Equiv.symm_apply_apply]
    rw [Finset.prod_boole]
    simp
  have hproj : ∀ x : WordSpace n e, ∀ b, orbitProjection t x b = if wordOrbit t b then x b else 0 := by
    intro x b
    exact coordinateProjection_apply (wordOrbit t) x b
  funext b
  rw [hproj, hval]
  by_cases hh : h = ω * g
  · rw [if_pos hh]; subst hh
    have hc : (∀ i, (a (g.val i)).val + (a ((ω*g).val i)).val = (b i).val) ↔ b = t := by
      have : ∀ i, (a (g.val i)).val + (a ((ω*g).val i)).val = (t i).val := by
        intro i; rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, hω (g.val i), ht g i]
      constructor
      · intro H'; funext i; exact Fin.ext ((H' i).symm.trans (this i))
      · rintro rfl; exact this
    rw [Pi.single_apply]
    by_cases hb : b = t
    · subst hb; rw [if_pos ⟨1, rfl⟩, if_pos (hc.2 rfl), if_pos rfl]
    · rw [if_neg (mt hc.1 hb), if_neg hb]; simp
  · rw [if_neg hh]
    simp only [Pi.zero_apply]
    split_ifs with h1 h2
    · exfalso; obtain ⟨π, hπ⟩ := h1; apply hh
      exact h42_pair_key H a t ω ht ha hω g h π (fun i => by rw [h2 i, hπ]; rfl)
    · rfl
    · rfl

