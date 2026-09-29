-- Prove2me | solution 1 for HorizontalPadicL.CharacterCountingTransfer.logLowerBound_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:11:21.568862+00:00
-- url     : https://prove2.me/submissions/2365a968-0f59-4fac-bef8-92a1a159b705

import Definitions.Def_KN_PrimePowerPropagationV2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CountAux
open HorizontalPadicL

/-- Counting step: characters of `S` of conductor at most `Y` are at most `M` times the characters
of `T` of conductor at most `scale * Y`. -/
lemma count_le {S T : Set DirichletCharacterWithLevel} (F : CharacterCountingTransfer S T)
    (hS : ∀ X : ℝ, {χ | χ ∈ S ∧ (χ.2.conductor : ℝ) ≤ X}.Finite)
    (hT : ∀ X : ℝ, {χ | χ ∈ T ∧ (χ.2.conductor : ℝ) ≤ X}.Finite) (Y : ℝ) :
    characterConductorCount S Y ≤ F.multiplicity * characterConductorCount T (F.scale * Y) := by
  classical
  unfold characterConductorCount
  set A := {χ | χ ∈ S ∧ (χ.2.conductor : ℝ) ≤ Y}
  set B := {χ | χ ∈ T ∧ (χ.2.conductor : ℝ) ≤ F.scale * Y}
  have hA := hS Y
  have hB := hT (F.scale * Y)
  let f : DirichletCharacterWithLevel → DirichletCharacterWithLevel :=
    fun χ => if h : χ ∈ S then (F.map ⟨χ, h⟩).val else χ
  have hfA : ∀ χ ∈ A, ∃ h : χ ∈ S, f χ = (F.map ⟨χ, h⟩).val := fun χ hχ => ⟨hχ.1, dif_pos hχ.1⟩
  have himg : hA.toFinset.image f ⊆ hB.toFinset := by
    intro θ hθ
    rw [Finset.mem_image] at hθ
    obtain ⟨χ, hχ, rfl⟩ := hθ
    rw [Set.Finite.mem_toFinset] at hχ ⊢
    obtain ⟨h, hf⟩ := hfA χ hχ
    rw [hf]
    refine ⟨(F.map ⟨χ, h⟩).2, ?_⟩
    calc ((F.map ⟨χ, h⟩).val.2.conductor : ℝ) ≤ F.scale * (χ.2.conductor : ℝ) := F.conductor_bound _
      _ ≤ F.scale * Y := mul_le_mul_of_nonneg_left hχ.2 (by linarith [F.scale_ge_one])
  have hfib : ∀ θ ∈ hA.toFinset.image f,
      (hA.toFinset.filter (fun χ => f χ = θ)).card ≤ F.multiplicity := by
    intro θ hθ
    have hθT : θ ∈ T := by
      have := himg hθ
      rw [Set.Finite.mem_toFinset] at this
      exact this.1
    have hsub : ((hA.toFinset.filter (fun χ => f χ = θ)) : Set _) ⊆
        Subtype.val '' {ψ : S | F.map ψ = ⟨θ, hθT⟩} := by
      intro χ hχ
      simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hχ
      obtain ⟨hχA, hfχ⟩ := hχ
      obtain ⟨h, hf⟩ := hfA χ hχA
      refine ⟨⟨χ, h⟩, ?_, rfl⟩
      apply Subtype.ext
      rw [← hf, hfχ]
    have hfin : (Subtype.val '' {ψ : S | F.map ψ = ⟨θ, hθT⟩}).Finite :=
      (F.fibre_finite ⟨θ, hθT⟩).image _
    calc (hA.toFinset.filter (fun χ => f χ = θ)).card
        = Set.ncard ((hA.toFinset.filter (fun χ => f χ = θ)) : Set _) := (Set.ncard_coe_finset _).symm
      _ ≤ Set.ncard (Subtype.val '' {ψ : S | F.map ψ = ⟨θ, hθT⟩}) := Set.ncard_le_ncard hsub hfin
      _ = Set.ncard {ψ : S | F.map ψ = ⟨θ, hθT⟩} :=
          Set.ncard_image_of_injective _ Subtype.val_injective
      _ ≤ F.multiplicity := F.fibre_card _
  calc A.ncard = hA.toFinset.card := Set.ncard_eq_toFinset_card A hA
    _ ≤ F.multiplicity * (hA.toFinset.image f).card := Finset.card_le_mul_card_image _ _ hfib
    _ ≤ F.multiplicity * hB.toFinset.card := Nat.mul_le_mul_left _ (Finset.card_le_card himg)
    _ = F.multiplicity * B.ncard := by rw [Set.ncard_eq_toFinset_card B hB]

/-- Comparison of `(log (X / s))^β` with `(log X)^β` for `X ≥ max(s², 3)`. -/
lemma log_rpow_le (s X β : ℝ) (hs : 1 ≤ s) (hX2 : s ^ 2 ≤ X) (hX3 : 3 ≤ X) :
    Real.log (X / s) ^ β ≤ (1 + (1 / 2 : ℝ) ^ β) * Real.log X ^ β := by
  have hs0 : 0 < s := by linarith
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogs : 0 ≤ Real.log s := Real.log_nonneg hs
  have hlogs2 : 2 * Real.log s ≤ Real.log X := by
    have := Real.log_le_log (by positivity) hX2
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hY : Real.log (X / s) = Real.log X - Real.log s := Real.log_div hX0.ne' hs0.ne'
  have hlo : Real.log X / 2 ≤ Real.log (X / s) := by rw [hY]; linarith
  have hhi : Real.log (X / s) ≤ Real.log X := by rw [hY]; linarith
  have hlo0 : 0 < Real.log X / 2 := by linarith
  have hpos : 0 ≤ Real.log X ^ β := Real.rpow_nonneg hlogX.le _
  rcases le_or_gt 0 β with hβ | hβ
  · have := Real.rpow_le_rpow (by linarith) hhi hβ
    have h2 : 0 ≤ (1 / 2 : ℝ) ^ β * Real.log X ^ β := by positivity
    nlinarith
  · have h1 := Real.rpow_le_rpow_of_nonpos hlo0 hlo hβ.le
    have h2 : (Real.log X / 2) ^ β = (1 / 2 : ℝ) ^ β * Real.log X ^ β := by
      rw [div_eq_mul_one_div, Real.mul_rpow hlogX.le (by norm_num), mul_comm]
    nlinarith

end CountAux

open HorizontalPadicL CountAux in
theorem solution
    {S T : Set DirichletCharacterWithLevel}
    (F : CharacterCountingTransfer S T)
    (hS : ∀ X : ℝ, {χ | χ ∈ S ∧ (χ.2.conductor : ℝ) ≤ X}.Finite)
    (hT : ∀ X : ℝ, {χ | χ ∈ T ∧ (χ.2.conductor : ℝ) ≤ X}.Finite)
    (α : ℝ) (hα : 0 < α)
    (hcount : HasLogPowerLowerBound (characterConductorCount S) α) :
    HasLogPowerLowerBound (characterConductorCount T) α := by
  obtain ⟨c, X₀, hc, hX₀, hbound⟩ := hcount
  set s := F.scale
  set M := F.multiplicity
  have hs : 1 ≤ s := F.scale_ge_one
  have hs0 : 0 < s := by linarith
  have hM : (0 : ℝ) < M := by exact_mod_cast F.multiplicity_pos
  set K : ℝ := 1 + (1 / 2 : ℝ) ^ (1 - α)
  have hK : 0 < K := by positivity
  refine ⟨c / (M * s * K), max (max (s * X₀) (s ^ 2)) 3, by positivity,
    le_trans (by norm_num) (le_max_right _ _), fun X hX => ?_⟩
  have hX1 : s * X₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX2 : s ^ 2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX3 : 3 ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 < X := by linarith
  have hY : X₀ ≤ X / s := by rw [le_div_iff₀ hs0]; linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hLX : 0 < Real.log X ^ (1 - α) := Real.rpow_pos_of_pos hlogX _
  have hlogY : 0 < Real.log (X / s) := by
    have := Real.log_le_log (by positivity) hX2
    rw [Real.log_pow, Nat.cast_ofNat] at this
    rw [Real.log_div hX0.ne' hs0.ne']; linarith [Real.log_nonneg hs]
  have hLY : 0 < Real.log (X / s) ^ (1 - α) := Real.rpow_pos_of_pos hlogY _
  have hS' := hbound (X / s) hY
  have hcnt : (characterConductorCount S (X / s) : ℝ) ≤ M * characterConductorCount T X := by
    have := count_le F hS hT (X / s)
    have e : F.scale * (X / s) = X := by change s * (X / s) = X; field_simp
    rw [e] at this
    exact_mod_cast this
  have hcmp := log_rpow_le s X (1 - α) hs hX2 hX3
  -- c' X / L^β ≤ c (X/s) / (M L_Y^β) ≤ count_S(X/s) / M ≤ count_T X
  have hcmp' : Real.log (X / s) ^ (1 - α) ≤ K * Real.log X ^ (1 - α) := hcmp
  have key : c / (M * s * K) * X / Real.log X ^ (1 - α) ≤ c * (X / s) / Real.log (X / s) ^ (1 - α) / M := by
    have e1 : c / (M * s * K) * X / Real.log X ^ (1 - α) =
        (c * X / (s * M)) * (1 / (K * Real.log X ^ (1 - α))) := by
      field_simp
    have e2 : c * (X / s) / Real.log (X / s) ^ (1 - α) / M =
        (c * X / (s * M)) * (1 / Real.log (X / s) ^ (1 - α)) := by
      field_simp
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hLY hcmp') (by positivity)
  calc c / (M * s * K) * X / Real.log X ^ (1 - α)
      ≤ c * (X / s) / Real.log (X / s) ^ (1 - α) / M := key
    _ ≤ (characterConductorCount S (X / s) : ℝ) / M := div_le_div_of_nonneg_right hS' hM.le
    _ ≤ characterConductorCount T X := by rw [div_le_iff₀ hM]; linarith
