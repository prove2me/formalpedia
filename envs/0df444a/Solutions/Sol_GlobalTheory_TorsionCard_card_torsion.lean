-- Prove2me | solution 1 for GlobalTheory.TorsionCard.card_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:48:02.749091+00:00
-- url     : https://prove2.me/submissions/8b658709-8091-4a35-8ab8-0c3ae392080b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCosetRepresentativesOfFiniteSubgroupPadicI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ChiOntoOfUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardTorsionMulFinrank
import Theorems.Thm_GlobalTheory_TorsionCard_eq_one_of_red
import Theorems.Thm_GlobalTheory_TorsionCard_exists_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory GlobalTheory.TorsionCard
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.TorsionCard
theorem _root_.solution (h2 : l ≠ 2) {Γ : Type} [Group Γ] (χ : Γ →* ℤ_[l]ˣ)
    (hχ : Function.Injective χ) (hk : ∀ x, red l x = 1 → x ∈ χ.range) :
    Nat.card {g : Γ // IsOfFinOrder g} = Nat.card ((red l).comp χ).range := by
  classical
  have hcomm : ∀ a b : Γ, a * b = b * a := fun a b => hχ (by rw [map_mul, map_mul, mul_comm])
  have hfin : ∀ g : Γ, IsOfFinOrder (χ g) ↔ IsOfFinOrder g := fun g => by
    rw [← orderOf_pos_iff, ← orderOf_pos_iff, orderOf_injective χ hχ g]
  let f : {g : Γ // IsOfFinOrder g} → ((red l).comp χ).range := fun g => ⟨red l (χ g.1), g.1, rfl⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hab' : red l (χ a) = red l (χ b) := congrArg Subtype.val hab
    have hc : Commute a b⁻¹ := hcomm a b⁻¹
    have ht : IsOfFinOrder (χ (a * b⁻¹)) := (hfin _).mpr (hc.isOfFinOrder_mul ha hb.inv)
    have h1 : red l (χ (a * b⁻¹)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_inv, hab', mul_inv_cancel]
    have h3 := eq_one_of_red h2 _ ht h1
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    exact Subtype.ext (hχ h3)
  · rintro ⟨u, g, rfl⟩
    obtain ⟨x, hx, hxu⟩ := exists_lift h2 (red l (χ g))
    have hr : red l (x⁻¹ * χ g) = 1 := by rw [map_mul, map_inv, hxu, inv_mul_cancel]
    obtain ⟨k, hk'⟩ := hk _ hr
    have hgk : χ (g * k⁻¹) = x := by
      rw [map_mul, map_inv, hk', mul_inv_rev, inv_inv, mul_inv_cancel_left]
    refine ⟨⟨g * k⁻¹, (hfin _).mp (hgk ▸ hx)⟩, Subtype.ext ?_⟩
    change red l (χ (g * k⁻¹)) = red l (χ g)
    rw [hgk, hxu]
end GlobalTheory.TorsionCard
