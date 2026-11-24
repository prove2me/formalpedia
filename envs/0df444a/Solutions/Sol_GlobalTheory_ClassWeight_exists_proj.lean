-- Prove2me | solution 1 for GlobalTheory.ClassWeight.exists_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:27:41.405955+00:00
-- url     : https://prove2.me/submissions/7b95fb03-d35c-4bee-a9ca-43d81e092946

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PerfectPairingOrthogonalOfCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceFinrank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ClassSubStructure
import Theorems.Thm_GlobalTheory_ClassWeight_evalChar_add_nsmul
import Theorems.Thm_GlobalTheory_ClassWeight_exists_evalChar_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
theorem _root_.solution [Module.Finite ℤ X] [IsAlgClosed F] (hN : (N : F) ≠ 0) (S : ∀ α, E →ₗ[F] W α)
    (hc : (Nat.card (TorChar X F N) : F) ≠ 0) (l : TorChar X F N → E → E)
    (hl : ∀ τ v β, S β (l τ v) = (evalChar F N β τ : F) • S β v) (α : X) (v : E) :
    ∃ v' ∈ classSub S N α, ∀ mu, S (α + N • mu) v' = S (α + N • mu) v := by
  have : Finite (TorChar X F N) := Nat.finite_of_card_ne_zero fun e => hc (by rw [e, Nat.cast_zero])
  have := Fintype.ofFinite (TorChar X F N)
  have key : ∀ β, S β ((Nat.card (TorChar X F N) : F)⁻¹ • ∑ τ, (((evalChar F N α τ)⁻¹ : Fˣ) : F) • l τ v) =
      ((Nat.card (TorChar X F N) : F)⁻¹ * ∑ τ, ((Units.coeHom F).comp (evalChar F N β / evalChar F N α)) τ) • S β v :=
    fun β => by
      rw [map_smul, map_sum, mul_smul, Finset.sum_smul]
      refine congrArg _ (Finset.sum_congr rfl fun τ _ => ?_)
      rw [map_smul, hl, smul_smul, ← Units.val_mul, mul_comm, ← div_eq_mul_inv]
      rfl
  refine ⟨_, fun β hβ => (key β).trans ?_, fun mu => (key _).trans ?_⟩
  · obtain ⟨τ, hτ⟩ := exists_evalChar_ne hN hβ
    rw [sum_hom_units_eq_zero _ fun e => hτ (div_eq_one.1 (Units.ext (DFunLike.congr_fun e τ))), mul_zero, zero_smul]
  · have e : ∀ τ, ((Units.coeHom F).comp (evalChar F N (α + N • mu) / evalChar F N α)) τ = 1 := fun τ =>
      congrArg Units.val (div_eq_one.2 (evalChar_add_nsmul α mu τ))
    rw [Finset.sum_congr rfl fun τ _ => e τ, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_one, inv_mul_cancel₀ hc, one_smul]
end GlobalTheory.ClassWeight
