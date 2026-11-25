-- Prove2me | solution 1 for GlobalTheory.UnramCard.card_quot_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:28.187914+00:00
-- url     : https://prove2.me/submissions/408c6848-89cb-4d7c-ae80-3b0b0df76ceb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotEqPow
import Theorems.Thm_GlobalTheory_UnramCard_card_quot_mul
import Theorems.Thm_GlobalTheory_UnramCard_card_quot_map
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_inj
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
import Theorems.Thm_GlobalTheory_UnramVal_vE_valuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnramCard
namespace GlobalTheory.UnramCard
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ δ : L.O, IsUnit (δ : E) → 0 ≤ vE L ϖ ((δ : E) * L.cj δ) ∧ Nat.card (L.O ⧸ Ideal.span {δ}) = resQ ϖ ^ (vE L ϖ ((δ : E) * L.cj δ)).toNat := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ δ hδ
  obtain ⟨-, h2, -, -, h5, h6, -, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨-, -, v3, v4⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  obtain ⟨hcm, -, n, hn⟩ := h2 δ δ.2
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  have hE : Nontrivial E := hinj.nontrivial
  have hn0 : (n : F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hn
    exact (hδ.mul (hδ.map L.cj)).ne_zero hn
  rw [hn]
  have hv : 0 ≤ vE L ϖ (algebraMap F E (n : F)) := (v3 _ hn0).2 n.2
  refine ⟨hv, ?_⟩
  obtain ⟨u, hu⟩ := v4 _ hn0
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hv
  rw [hj, zpow_natCast] at hu
  rw [hj, Int.toNat_natCast]
  let c : L.O ≃+* L.O :=
    { toFun := fun x => ⟨L.cj x, GlobalTheory.UnramOrder.cj_mem L x.2⟩
      invFun := fun x => ⟨L.cj x, GlobalTheory.UnramOrder.cj_mem L x.2⟩
      left_inv := fun x => Subtype.ext (L.cj_cj x)
      right_inv := fun x => Subtype.ext (L.cj_cj x)
      map_mul' := fun x y => Subtype.ext (map_mul L.cj (x : E) y)
      map_add' := fun x y => Subtype.ext (map_add L.cj (x : E) y) }
  have hnz : δ ∈ nonZeroDivisors L.O := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    have hx' : (x : E) * δ = 0 := by exact_mod_cast congrArg Subtype.val hx
    exact Subtype.ext (hδ.mul_left_eq_zero.1 hx')
  have hmul := card_quot_mul hnz (c δ)
  rw [card_quot_map] at hmul
  let ι : 𝒪[F] →+* L.O :=
    ((algebraMap F E).comp (𝒪[F]).subtype).codRestrict L.O (fun x => (h5 _).2 x.2)
  have hset : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)} = {ι (ϖ ^ j)} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Subtype.ext_iff]
    rfl
  have hprod : δ * c δ = ι (ϖ ^ j) * ι u := by
    apply Subtype.ext
    change (δ : E) * L.cj δ = algebraMap F E ((ϖ : F) ^ j) * algebraMap F E ((u : 𝒪[F]) : F)
    rw [hn, ← map_mul, ← hu]
  have h7 := h6 j
  rw [hset] at h7
  rw [hprod, Ideal.span_singleton_mul_right_unit (u.isUnit.map ι), h7, two_mul, pow_add] at hmul
  exact (Nat.mul_self_inj.1 hmul).symm
end GlobalTheory.UnramCard
