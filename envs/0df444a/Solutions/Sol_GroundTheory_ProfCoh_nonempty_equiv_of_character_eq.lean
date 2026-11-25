-- Prove2me | solution 1 for GroundTheory.ProfCoh.nonempty_equiv_of_character_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:16.973324+00:00
-- url     : https://prove2.me/submissions/beb4a9f5-509f-4b76-bd06-c0b40f3c79e9

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLatticeCharacter
import Theorems.Thm_GroundTheory_ProfCoh_character_prod
import Theorems.Thm_GroundTheory_ProfCoh_exists_equiv_prod_of_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Module Representation
universe uk uG uU uV uW
variable {k : Type uk} {G : Type uG} [Field k] [Group G]
namespace GroundTheory.ProfCoh
theorem _root_.solution [CharZero k] [Finite G] {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (ρ : Representation k G V) (σ : Representation k G W)
    (h : ρ.character = σ.character) : Nonempty (ρ.Equiv σ) := by
  suffices H : ∀ n : ℕ, ∀ {V : Type uV} {W : Type uW} [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
      (ρ : Representation k G V) (σ : Representation k G W), finrank k V = n →
      ρ.character = σ.character → Nonempty (ρ.Equiv σ) from H _ ρ σ rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V W _ _ _ _ _ _ ρ σ hn h
  have : Fintype G := Fintype.ofFinite G
  have hG : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have : NeZero (Nat.card G : k) := ⟨hG⟩
  have : Invertible (Nat.card G : k) := invertibleOfNonzero hG
  have hdim : finrank k W = finrank k V := by
    have h1 := congrFun h 1
    rw [Representation.char_one, Representation.char_one] at h1
    exact_mod_cast h1.symm
  by_cases hV : finrank k V = 0
  · have : Subsingleton W := Module.finrank_zero_iff.1 (hdim.trans hV)
    exact ⟨Representation.Equiv.mk (LinearEquiv.ofFinrankEq V W hdim.symm) fun g =>
      LinearMap.ext fun _ => Subsingleton.elim _ _⟩

  have hex : ∃ m, ∃ Y : Subrepresentation ρ, Y ≠ ⊥ ∧ finrank k Y.toSubmodule = m := by
    refine ⟨finrank k V, ⊤, fun h0 => hV ?_, finrank_top k V⟩
    have h1 : (⊤ : Submodule k V) = ⊥ := congrArg Subrepresentation.toSubmodule h0
    rw [← finrank_top k V, h1, finrank_bot]
  classical
  obtain ⟨Y, hY0, hYm⟩ := Nat.find_spec hex
  have hmin : ∀ Y' : Subrepresentation ρ, Y' ≠ ⊥ →
      finrank k Y.toSubmodule ≤ finrank k Y'.toSubmodule := fun Y' hY' => by
    rw [hYm]
    exact Nat.find_min' hex ⟨Y', hY', rfl⟩
  have hYsub : Y.toSubmodule ≠ ⊥ := fun h0 => hY0 (Subrepresentation.toSubmodule_injective h0)

  let ι : IntertwiningMap Y.toRepresentation ρ :=
    ⟨Y.toSubmodule.subtype, fun g => LinearMap.ext fun _ => rfl⟩
  have hιinj : Function.Injective ι := Subtype.val_injective
  have hι0 : ι ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := Submodule.ne_bot_iff _ |>.1 hYsub
    intro h0
    exact hy0 (congrArg (fun φ : IntertwiningMap Y.toRepresentation ρ => φ ⟨y, hy⟩) h0)

  have hHom : finrank k (IntertwiningMap Y.toRepresentation σ) =
      finrank k (IntertwiningMap Y.toRepresentation ρ) := by
    have h1 := card_inv_mul_sum_char_mul_char_eq_finrank Y.toRepresentation ρ
    have h2 := card_inv_mul_sum_char_mul_char_eq_finrank Y.toRepresentation σ
    rw [h] at h1
    exact_mod_cast h2.symm.trans h1
  have hpos : 0 < finrank k (IntertwiningMap Y.toRepresentation σ) :=
    hHom ▸ Module.finrank_pos_iff_exists_ne_zero.2 ⟨ι, hι0⟩
  obtain ⟨f, hf0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos

  have hfinj : Function.Injective f := by
    let K : Submodule k Y.toSubmodule := LinearMap.ker f.toLinearMap
    by_cases hK : K = ⊥
    · exact LinearMap.ker_eq_bot.1 hK
    exfalso
    let K' : Subrepresentation ρ := ⟨K.map Y.toSubmodule.subtype, by
      rintro g _ ⟨y, hy, rfl⟩
      refine ⟨Y.toRepresentation g y, ?_, rfl⟩
      have h1 := LinearMap.congr_fun (f.isIntertwining' g) y
      have hy' : f.toLinearMap y = 0 := hy
      show f.toLinearMap (Y.toRepresentation g y) = 0
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
      rw [h1, hy', map_zero]⟩
    have hK'dim : finrank k K'.toSubmodule = finrank k K := Submodule.finrank_map_subtype_eq _ _
    have hKpos : finrank k K ≠ 0 := fun h0 => hK (Submodule.finrank_eq_zero.1 h0)
    have hK'0 : K' ≠ ⊥ := by
      intro h0
      have h1 : K'.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h0
      rw [h1, finrank_bot] at hK'dim
      exact hKpos hK'dim.symm
    have h1 := hmin K' hK'0
    have h2 : finrank k K = finrank k Y.toSubmodule :=
      le_antisymm (Submodule.finrank_le K) (hK'dim ▸ h1)
    have hKtop : K = ⊤ := Submodule.eq_top_of_finrank_eq h2
    exact hf0 (IntertwiningMap.ext (LinearMap.ker_eq_top.1 hKtop))

  obtain ⟨V', ⟨eV⟩⟩ := exists_equiv_prod_of_injective ι hιinj
  obtain ⟨W', ⟨eW⟩⟩ := exists_equiv_prod_of_injective f hfinj
  have hchar : V'.toRepresentation.character = W'.toRepresentation.character := by
    funext g
    have h1 := congrFun (char_iso eV) g
    have h2 := congrFun (char_iso eW) g
    have h3 := congrFun h g
    rw [character_prod] at h1 h2
    linear_combination h1 - h2 + h3
  have hYpos : 0 < finrank k Y.toSubmodule :=
    Nat.pos_of_ne_zero fun h0 => hYsub (Submodule.finrank_eq_zero.1 h0)
  have hlt : finrank k V'.toSubmodule < n := by
    have h1 := eV.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at h1
    omega
  obtain ⟨e'⟩ := ih _ hlt V'.toRepresentation W'.toRepresentation rfl hchar
  exact ⟨eV.symm.trans ((equivProdRight Y.toRepresentation e').trans eW)⟩
end GroundTheory.ProfCoh
