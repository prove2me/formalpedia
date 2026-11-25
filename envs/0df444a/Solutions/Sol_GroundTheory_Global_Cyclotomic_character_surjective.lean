-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.character_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:26:32.015689+00:00
-- url     : https://prove2.me/submissions/9a4ef77a-09e2-40b6-b284-aae5bfb9d690

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
import Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_modCharacter_eq
import Theorems.Thm_GroundTheory_Global_Cyclotomic_continuous_character_val
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_castHom_proj
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_continuous_proj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
open scoped Pointwise
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution : Function.Surjective character := by
  intro u
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  let N : ℕ → ℕ+ := fun k => ⟨(k + 1).factorial, Nat.factorial_pos _⟩
  have hdvd : ∀ {k l : ℕ}, k ≤ l → (N k : ℕ) ∣ N l := fun h =>
    Nat.factorial_dvd_factorial (Nat.succ_le_succ h)
  have hcont : ∀ n : ℕ+, Continuous fun σ : Gal(ℚ̄/ℚ) => ProfiniteInteger.proj n (character σ : ℤ̂) :=
    fun n => (ProfiniteInteger.continuous_proj n).comp continuous_character_val
  let S : ℕ → Set Gal(ℚ̄/ℚ) := fun k =>
    {σ | ProfiniteInteger.proj (N k) (character σ : ℤ̂) = ProfiniteInteger.proj (N k) (u : ℤ̂)}
  have hmono : ∀ k, S (k + 1) ⊆ S k := fun k σ hσ => by
    simp only [S, Set.mem_ofPred_eq] at hσ ⊢
    rw [← ProfiniteInteger.castHom_proj (hdvd k.le_succ) (character σ : ℤ̂), hσ,
      ProfiniteInteger.castHom_proj]
  have hne : ∀ k, (S k).Nonempty := fun k => by
    obtain ⟨σ, hσ⟩ := exists_modCharacter_eq (N k)
      (Units.map (ProfiniteInteger.proj (N k)).toMonoidHom u)
    refine ⟨σ, ?_⟩
    simp only [S, Set.mem_ofPred_eq, proj_character, hσ]
    rfl
  have hclosed : ∀ k, IsClosed (S k) := fun k => isClosed_eq (hcont (N k)) continuous_const
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hmono hne
    (hclosed 0).isCompact hclosed
  rw [Set.mem_iInter] at hσ
  refine ⟨σ, Units.ext (ProfiniteInteger.ext fun n => ?_)⟩
  have hn : (n : ℕ) ∣ N n := Nat.dvd_factorial n.pos (Nat.le_succ n)
  rw [← ProfiniteInteger.castHom_proj hn (character σ : ℤ̂), ← ProfiniteInteger.castHom_proj hn,
    show ProfiniteInteger.proj (N n) (character σ : ℤ̂) = _ from hσ n]
end GroundTheory.Global.Cyclotomic
