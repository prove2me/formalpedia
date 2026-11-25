-- Prove2me | solution 1 for GlobalTheory.OrbitDenom.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:50:25.764902+00:00
-- url     : https://prove2.me/submissions/b548440b-cdb2-4b82-9e45-dec0b431762a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Theorems.Thm_GlobalTheory_OrbitDenom_det_mem
import Theorems.Thm_GlobalTheory_OrbitDenom_det_three
import Theorems.Thm_GlobalTheory_OrbitDenom_unit_cut
import Theorems.Thm_GlobalTheory_OrbitDenom_low_mem
import Theorems.Thm_GlobalTheory_OrbitDenom_up_mem
import Theorems.Thm_GlobalTheory_OrbitDenom_entry_symm
import Theorems.Thm_GlobalTheory_OrbitDenom_block_of
import Theorems.Thm_GlobalTheory_OrbitDenom_vE_norm_prod
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
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
open GlobalTheory GlobalTheory.OrbitDenom
namespace GlobalTheory.OrbitDenom
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u → IsUni u' → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) → IsIntM L (cT L u * S.Zh * u') → ∀ Δ : E, Δ = ∏ l : Fin (r + 2), (if S.D l ≠ 0 then S.D l else 1) → Δ ∈ L.O ∧ IsUnit Δ ∧ vE L S.ϖ (Δ * L.cj Δ) = S.vD ∧ ∀ i j, L.cj Δ * u i j ∈ L.O ∧ Δ * u' i j ∈ L.O := by
  intro F _ _ _ _ _ E _ _ _ L r k S u u' hu hu' huO hZ Δ hΔ
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  have hcj : ∀ x ∈ L.O, L.cj x ∈ L.O := fun x hx =>
    ((GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.1 x hx).1
  obtain ⟨-, -, -, hW, hun, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hW' : IsUnit S.Zh.det := hW
  have hA : ∀ a b : Fin (r + 1), a < b → cT L u a b = 0 := fun a b h => by
    rw [cT, hu.1 _ _ h, map_zero]
  have hA1 : ∀ a : Fin (r + 1), cT L u a a = 1 := fun a => by rw [cT, hu.2, map_one]
  have hB : ∀ a b : Fin (r + 1), b < a → u' a b = 0 := hu'.1
  have hDO : ∀ l, S.D l ∈ L.O := fun l => by
    unfold Frames.D lead
    rw [← det_three _ _ _ _ hA hA1 hB hu'.2]
    exact det_mem _ _ fun _ _ => hZ _ _
  set x : Fin (r + 2) → E := fun l => if S.D l ≠ 0 then S.D l else 1 with hx
  have hxO : ∀ l, x l ∈ L.O := fun l => by
    simp only [hx]; split_ifs
    · exact hDO l
    · exact L.O.one_mem
  have hxu : ∀ l, IsUnit (x l) := fun l => by
    simp only [hx]; split_ifs with h
    · exact hun l h
    · exact isUnit_one
  have h10 : vE L S.ϖ 1 = 0 := by
    simpa using vE_norm_prod L S.ϖ S.ϖ_irr x hxu ∅
  refine ⟨hΔ ▸ L.O.prod_mem fun l _ => hxO l, hΔ ▸ IsUnit.prod_iff.2 fun l _ => hxu l, ?_, ?_⟩
  · rw [hΔ, vE_norm_prod L S.ϖ S.ϖ_irr x hxu, Frames.vD]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h0 : S.D l = 0
    · simp [hx, h0, h10]
    · by_cases h1 : l = 0
      · have : S.D 0 = 1 := Matrix.det_isEmpty (n := Fin 0)
        simp [hx, h1, this, h10]
      · simp [hx, h0, h1]
  · intro i j
    obtain ⟨l', l, t, e1, e2, e3, e4, e5, e6, e7⟩ :=
      block_of S.w.blocks i (by rw [S.w.size]; exact i.2)
    rw [S.w.size] at e3
    have e3' : l' ≤ r + 1 := by omega
    have hZh : ∀ a b : Fin (r + 1), S.Zh a b = ptEntryL S.w.blocks a b * (-1) ^ (r - (b : ℕ)) :=
      fun a b => S.relevant a b
    have hc : ∀ a b : Fin (r + 1), l ≤ (a : ℕ) → (b : ℕ) < l → S.Zh a b = 0 := fun a b ha hb => by
      rw [hZh, e6 _ _ ha hb, zero_mul]
    have hc' : ∀ a b : Fin (r + 1), l' ≤ (a : ℕ) → (b : ℕ) < l' → S.Zh a b = 0 := fun a b ha hb => by
      rw [hZh, e7 _ _ ha hb, zero_mul]
    have hAO : ∀ a b : Fin (r + 1), (a : ℕ) < l → l' ≤ (b : ℕ) → cT L u a b ∈ L.O := by
      intro a b ha hb
      by_cases hab : a < b
      · rw [hA _ _ hab]; exact L.O.zero_mem
      · rw [Fin.lt_def] at hab
        exact hcj _ (huO _ _ (e4 _ _ hb (by omega) (by omega) ha))
    have g1 := low_mem L.O e3 _ _ _ hA hA1 hB hu'.2 hZ hW' hc hAO i e1 e2 j
    have g2 := up_mem L.O e3 e3' _ _ _ hA hA1 hB hu'.2 hZ hW' hc' hAO t
      (fun b => (-1) ^ (r - (b : ℕ))) (fun b => L.O.pow_mem (L.O.neg_mem L.O.one_mem) _)
      (fun b => by rw [← mul_pow]; simp)
      (fun a b hb' hb => by rw [hZh, entry_symm, e5 _ _ hb' hb, add_comm (b : ℕ) a])
      (fun a b ha' ha => by rw [hZh, e5 _ _ ha' ha]) i e1 e2 j
    let p : Fin (r + 2) := ⟨l, by omega⟩
    let p' : Fin (r + 2) := ⟨l', by omega⟩
    have hp : x p = (S.Zh.submatrix (Fin.castLE e3) (Fin.castLE e3)).det :=
      if_pos (unit_cut e3 _ hW' hc).ne_zero
    have hp' : x p' = (S.Zh.submatrix (Fin.castLE e3') (Fin.castLE e3')).det :=
      if_pos (unit_cut e3' _ hW' hc').ne_zero
    have hne : p' ≠ p := fun e => by
      have := congrArg Fin.val e
      simp only [p, p'] at this
      omega
    obtain ⟨y, hy, hΔy⟩ : ∃ y ∈ L.O, Δ = x p * (x p' * y) := by
      refine ⟨∏ m ∈ (Finset.univ.erase p).erase p', x m, L.O.prod_mem fun m _ => hxO m, ?_⟩
      rw [Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩),
        Finset.mul_prod_erase _ _ (Finset.mem_univ _), hΔ]
    rw [← hp] at g1
    rw [← hp, ← hp'] at g2
    constructor
    · have g3 := hcj _ (L.O.mul_mem (L.O.mul_mem (hxO p') hy) g1)
      rw [hΔy]
      convert g3 using 1
      simp only [cT, map_mul, L.cj_cj]
      ring
    · have g3 := L.O.mul_mem hy g2
      rw [hΔy]
      convert g3 using 1
      ring
end GlobalTheory.OrbitDenom
