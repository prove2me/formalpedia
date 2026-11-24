-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspIff.isCuspidal_of_sum_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:04:08.434354+00:00
-- url     : https://prove2.me/submissions/9d7ded10-aac9-4a0d-8bff-bd24c4b9a213

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalOfUnipotentSumsVanish
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspIff_mem_stdRadical
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspIff_pm_conj
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspIff_eq_zero_of_sum_char

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspIff
namespace GlobalTheory.CompanionTheory.TyFin.CuspIff
theorem _root_.solution : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)),
    (∀ a, 0 < a → a < d → (open Classical in ∑ u : GL (Fin d) K,
      if (∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ)))
      then τ.character u else 0) = 0) → IsCuspidal K τ := by
  classical
  intro K _ _ _ d τ h s b hb hs v hv
  let c0 : Fin s := ⟨0, by omega⟩
  let c1 : Fin s := ⟨1, by omega⟩
  have hc : c0 ≠ c1 := by simp [c0, c1, Fin.ext_iff]
  obtain ⟨i0, hi0⟩ := hb c0
  obtain ⟨i1, hi1⟩ := hb c1
  set a := Fintype.card {i // b i = c0} with ha
  have ha0 : 0 < a := Fintype.card_pos_iff.2 ⟨⟨i0, hi0⟩⟩
  have had : a < d := by
    have := Fintype.card_subtype_lt (p := fun i => b i = c0) (x := i1) (by rw [hi1]; exact hc.symm)
    simpa using this
  have hcard : Fintype.card {i // b i = c0} = Fintype.card {i : Fin d // (i : ℕ) < a} := by
    rw [← ha]
    exact (Fintype.card_fin a).symm.trans (Fintype.card_congr
      { toFun := fun k => ⟨⟨k, by omega⟩, k.2⟩
        invFun := fun i => ⟨i.1, i.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
  let e := Fintype.equivOfCardEq hcard
  let σ : Equiv.Perm (Fin d) := e.extendSubtype
  have hσ : ∀ i, (σ i : ℕ) < a ↔ b i = c0 := by
    intro i
    by_cases hi : b i = c0
    · exact ⟨fun _ => hi, fun _ => e.extendSubtype_mem i hi⟩
    · exact ⟨fun h' => absurd h' (e.extendSubtype_not_mem i hi), fun h' => absurd h' hi⟩
  have hfix : ∀ w : τ, (∀ u ∈ stdRadical K d a, τ.ρ u w = w) → w = 0 := by
    refine eq_zero_of_sum_char τ.ρ (stdRadical K d a) ?_
    refine Eq.trans (Finset.sum_congr rfl fun u _ => ?_) (h a ha0 had)
    by_cases hu : u ∈ stdRadical K d a
    · rw [if_pos hu, if_pos (mem_stdRadical.1 hu)]; rfl
    · rw [if_neg hu, if_neg (fun h' => hu (mem_stdRadical.2 h'))]

  have hent : ∀ (x : GL (Fin d) K) (i j : Fin d),
      ((pm K σ * x * (pm K σ)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (σ i) (σ j) =
        (x : Matrix (Fin d) (Fin d) K) i j := by
    intro x i j
    rw [pm_conj]
    show (x : Matrix (Fin d) (Fin d) K) (σ.symm (σ i)) (σ.symm (σ j)) = _
    simp
  have key : ∀ x : GL (Fin d) K, pm K σ * x * (pm K σ)⁻¹ ∈ stdRadical K d a → ∀ i j,
      (x : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ (b i = c0 ∧ b j ≠ c0) := by
    intro x hx i j
    have := hx (σ i) (σ j)
    rw [hent] at this
    rcases this with h1 | ⟨h1, h2⟩
    · left; simpa [σ.injective.eq_iff] using h1
    · right
      refine ⟨(hσ i).1 h1, fun h3 => ?_⟩
      have := (hσ j).2 h3
      omega
  have hut : ∀ x : GL (Fin d) K, pm K σ * x * (pm K σ)⁻¹ ∈ stdRadical K d a →
      IsBlockUT K b (x : Matrix (Fin d) (Fin d) K) := by
    intro x hx i j hij
    rcases key x hx i j with h1 | ⟨h1, -⟩
    · have : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
      simpa [this] using h1
    · rw [h1] at hij
      exact absurd hij (by simp [c0, Fin.lt_def])
  have hun : ∀ x : GL (Fin d) K, pm K σ * x * (pm K σ)⁻¹ ∈ stdRadical K d a → x ∈ unip K b := by
    intro x hx
    refine ⟨⟨hut x hx, hut x⁻¹ ?_⟩, ?_⟩
    · have : pm K σ * x⁻¹ * (pm K σ)⁻¹ = (pm K σ * x * (pm K σ)⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem hx
    · intro i j hij
      rcases key x hx i j with h1 | ⟨h1, h2⟩
      · exact h1
      · exact absurd (hij ▸ h1) h2
  have hw := hfix (τ.ρ (pm K σ) v) (by
    intro u hu
    have hx : (pm K σ)⁻¹ * u * pm K σ ∈ unip K b := by
      apply hun
      have : pm K σ * ((pm K σ)⁻¹ * u * pm K σ) * (pm K σ)⁻¹ = u := by group
      rw [this]
      exact hu
    have hh : u * pm K σ = pm K σ * ((pm K σ)⁻¹ * u * pm K σ) := by group
    rw [← Module.End.mul_apply, ← map_mul, hh, map_mul, Module.End.mul_apply, hv _ hx])
  have h3 := congrArg (τ.ρ (pm K σ)⁻¹) hw
  simpa [← Module.End.mul_apply, ← map_mul] using h3
end GlobalTheory.CompanionTheory.TyFin.CuspIff
