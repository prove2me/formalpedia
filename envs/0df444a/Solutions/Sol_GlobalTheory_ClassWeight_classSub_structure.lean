-- Prove2me | solution 1 for GlobalTheory.ClassWeight.classSub_structure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:32:18.921413+00:00
-- url     : https://prove2.me/submissions/4c4460fe-1896-41d3-9b70-e41729df8222

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PerfectPairingOrthogonalOfCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceFinrank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ClassSubStructure
import Theorems.Thm_GlobalTheory_ClassWeight_evalChar_add_nsmul
import Theorems.Thm_GlobalTheory_ClassWeight_exists_evalChar_ne
import Theorems.Thm_GlobalTheory_ClassWeight_exists_proj
import Theorems.Thm_GlobalTheory_HeisenbergWeightDim_comm_mul_left
import Theorems.Thm_GlobalTheory_HeisenbergWeightDim_comm_mul_right
import Theorems.Thm_GlobalTheory_HeisenbergWeightDim_units_eq_of_smul_eq
import Theorems.Thm_GlobalTheory_heisenberg_weightSpace_finrank
import Theorems.Thm_GlobalTheory_heisenberg_weightSpace_irreducible
import Theorems.Thm_GlobalTheory_perfectPairing_orthogonal_of_card
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassWeight
variable {X : Type} [AddCommGroup X] {F : Type} [Field F] {N : ℕ}
variable {E : Type} [AddCommGroup E] [Module F E] {W : X → Type} [∀ α, AddCommGroup (W α)] [∀ α, Module F (W α)]
namespace GlobalTheory.ClassWeight
theorem _root_.solution [Module.Finite ℤ X] [IsAlgClosed F] [FiniteDimensional F E] (hN : (N : F) ≠ 0)
    {A : Type} [CommGroup A] [Finite A] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E)) (hA : (Nat.card A : F) ≠ 0)
    (hd : Module.finrank F E ^ 2 = Nat.card A) (hm : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hc : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (hn : ∀ a, (∀ b, e a b = 1) → a = 1)
    (S : ∀ α, E →ₗ[F] W α) (hS : ∀ v, (∀ α, S α v = 0) → v = 0)
    (a : TorChar X F N →* A) (ha : Function.Injective a)
    (hT : ∀ τ, ∃ c : Fˣ, ∀ v α, S α (Φ (a τ) v) = ((c * evalChar F N α τ : Fˣ) : F) • S α v)
    (H : Subgroup A) (hH : ∀ h ∈ H, ∀ α v v' (c : F), S α v = c • S α v' → S α (Φ h v) = c • S α (Φ h v'))
    (hcard : Nat.card (TorChar X F N) * Nat.card H = Nat.card A) (α : X) :
    (∀ v, ∃ v' ∈ classSub S N α, ∀ mu, S (α + N • mu) v' = S (α + N • mu) v) ∧
    Module.finrank F (classSub S N α) * Nat.card (TorChar X F N) = Module.finrank F E ∧
    ∀ U : Submodule F E, U ≤ classSub S N α → (∀ h ∈ H, ∀ v ∈ U, Φ h v ∈ U) → U = ⊥ ∨ U = classSub S N α := by
  have hpos : 0 < Nat.card A := Nat.card_pos
  have : Nontrivial E := by
    apply Module.nontrivial_of_finrank_pos (R := F)
    rcases Nat.eq_zero_or_pos (Module.finrank F E) with h | h
    · rw [h] at hd
      omega
    · exact h
  have ext : ∀ v v', (∀ α, S α v = S α v') → v = v' := fun v v' h =>
    sub_eq_zero.1 (hS _ fun α => by rw [map_sub, h, sub_self])
  choose c hcT using hT
  let l₀ : TorChar X F N → (E ≃ₗ[F] E) := fun τ => (Φ (a τ)).trans (LinearEquiv.smulOfUnit (c τ)⁻¹)
  have l₀e : ∀ τ v, l₀ τ v = (((c τ)⁻¹ : Fˣ) : F) • Φ (a τ) v := fun _ _ => rfl
  have hl : ∀ τ v β, S β (l₀ τ v) = (evalChar F N β τ : F) • S β v := fun τ v β => by
    rw [l₀e, map_smul, hcT, smul_smul, ← Units.val_mul, inv_mul_cancel_left]
  let l : TorChar X F N →* (E ≃ₗ[F] E) := MonoidHom.mk' l₀ fun τ τ' => LinearEquiv.ext fun v => ext _ _ fun β => by
    rw [LinearEquiv.mul_apply, hl, hl, hl, smul_smul, map_mul, Units.val_mul]
  let i : TorChar X F N ≃* a.range := MonoidHom.ofInjective ha
  let lam : a.range →* (E ≃ₗ[F] E) := l.comp i.symm.toMonoidHom
  have hlam : ∀ t : a.range, ∃ c : Fˣ, ∀ v, lam t v = (c : F) • Φ t v := fun t => by
    obtain ⟨τ, rfl⟩ := i.surjective t
    refine ⟨(c τ)⁻¹, fun v => ?_⟩
    show l₀ (i.symm (i τ)) v = _
    rw [i.symm_apply_apply]; rfl
  let Wt : (a.range →* Fˣ) → Submodule F E := fun χ =>
    { carrier := {v | ∀ t, lam t v = (χ t : F) • v}
      add_mem' := fun {v v'} h h' t => by rw [map_add, h t, h' t, smul_add]
      zero_mem' := fun t => by rw [map_zero, smul_zero]
      smul_mem' := fun r v h t => by rw [map_smul, h t, smul_comm] }
  have hWt : ∀ χ v, v ∈ Wt χ ↔ ∀ t, lam t v = (χ t : F) • v := fun _ _ => Iff.rfl
  let χ : a.range →* Fˣ := (evalChar F N α).comp i.symm.toMonoidHom
  have hW : Wt χ = classSub S N α := Submodule.ext fun v => ⟨fun h β hβ => by
      obtain ⟨τ, hτ⟩ := exists_evalChar_ne (F := F) hN hβ
      have h₁ : l₀ (i.symm (i τ)) v = (evalChar F N α (i.symm (i τ)) : F) • v := h (i τ)
      have h₂ := congrArg (S β) h₁
      rw [i.symm_apply_apply, hl, map_smul] at h₂
      by_contra h₃
      exact hτ (Units.ext (smul_left_injective F h₃ h₂)), fun h t => ext _ _ fun β => by
      refine (hl (i.symm t) v β).trans ?_
      rw [map_smul]
      by_cases hβ : ∃ mu, β = α + N • mu
      · obtain ⟨mu, rfl⟩ := hβ
        rw [evalChar_add_nsmul]; rfl
      · rw [h β hβ, smul_zero, smul_zero]⟩
  have hci : Nat.card a.range = Nat.card (TorChar X F N) := (Nat.card_congr i.toEquiv).symm
  have hTH : ∀ t ∈ a.range, ∀ h ∈ H, e t h = 1 := by
    rintro _ ⟨τ, rfl⟩ h hh
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have h₁ : Φ (a τ) (Φ h v) = Φ h (Φ (a τ) v) := ext _ _ fun β =>
      (hcT τ _ β).trans (hH h hh β _ _ _ (hcT τ v β)).symm
    have h₂ : Φ h (Φ (a τ) v) ≠ 0 := by simpa using hv
    apply HeisenbergWeightDim.units_eq_of_smul_eq h₂
    rw [← hc, h₁, Units.val_one, one_smul]
  have hperp := (perfectPairing_orthogonal_of_card F A e (HeisenbergWeightDim.comm_mul_left hm hc)
    (HeisenbergWeightDim.comm_mul_right hm hc) hn a.range H hTH (by rw [hci, hcard])).2.1
  refine ⟨exists_proj hN S (fun h => hA (by rw [← hcard, Nat.cast_mul, h, zero_mul])) (fun τ v => l₀ τ v) hl α, ?_,
    fun U hU hst => ?_⟩
  · rw [← hW, ← hci]
    exact (heisenberg_weightSpace_finrank F A E e Φ hA hd hm hc hn a.range lam hlam Wt hWt).2 χ
  · rw [← hW] at hU ⊢
    exact heisenberg_weightSpace_irreducible F A E e Φ hA hd hm hc hn a.range lam hlam Wt hWt χ U hU
      fun h hh => hst h ((hperp h).1 fun t ht => hh ⟨t, ht⟩)
end GlobalTheory.ClassWeight
