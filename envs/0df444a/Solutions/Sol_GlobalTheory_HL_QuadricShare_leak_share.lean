-- Prove2me | solution 1 for GlobalTheory.HL.QuadricShare.leak_share
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:10.973926+00:00
-- url     : https://prove2.me/submissions/5493c34b-6680-4c1e-b95d-6fd465285cec

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNormOneOrthTriple
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruenceSubgroupLatticeStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ProperIdealsOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsTraceChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExpandByConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TwoGeometricSumsIndexBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormGaussSumLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLocalCharacterSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuadricCharacterLeakSharesFinite
import Theorems.Thm_GlobalTheory_HL_QuadricShare_prime_share
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_CongFin_smul_mem_of
import Theorems.Thm_GlobalTheory_HL_GaussSummand_hf_add_right
import Theorems.Thm_GlobalTheory_HL_GaussSummand_hf_smul_right
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
import Theorems.Thm_GlobalTheory_UnramOrder_proper_ideals
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.QuadricShare
open GlobalTheory.HL.GaussSummand
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
  {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.HL.QuadricShare
theorem _root_.solution (hH : IsHermND L Hm) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    (UU : Submodule L.O (Fin n → E)) (hUU : ∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O)
    (ρ : ℕ) (hρ : 4 ≤ ρ) (e : Fin ρ → Fin n → E) (W : Submodule L.O (Fin n → E)) (hW : W ≤ UU)
    (he : ∀ a, e a ∈ W)
    (hee : ∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) (a N : ℕ) (haN : a + 1 ≤ N)
    (R : Finset (Fin n → E)) (hRU : ∀ u ∈ R, u ∈ UU)
    (hR : ∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y)
    (Z : (Fin n → E) → Prop)
    (hZ : ∀ u, Z u ↔ ∃ c : 𝒪[F], hf L Hm u u = algebraMap F E ((ϖ : F) ^ a * c)) :
    ((R.filter fun u => Z u ∧ ¬ ∃ y ∈ W, hf L Hm u y = 1).card : ℝ) * (resQ ϖ : ℝ) ^ a ≤
      16 / 7 * (resQ ϖ : ℝ) ^ (1 - (ρ : ℤ)) * R.card := by
  obtain ⟨-, hcj, -, -, hint, -, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hq1 : (1 : ℝ) ≤ resQ ϖ := by exact_mod_cast (by omega : 1 ≤ resQ ϖ)
  have hp : algebraMap F E ϖ ∈ L.O := (hint _).2 ϖ.2
  have hps := prime_share L Hm hH ϖ hϖ UU hUU ρ hρ e (fun a => hW (he a)) hee a N (by omega) R hRU hR
    Z hZ
  have hI : ∀ u ∈ R, (¬ ∃ y ∈ W, hf L Hm u y = 1) → ∃ I : Ideal L.O, I ≠ ⊤ ∧
      ∀ a, ∃ x ∈ I, (x : E) = hf L Hm u (e a) := by
    intro u hu hne
    let I : Ideal L.O :=
      { carrier := {x | ∃ y ∈ W, hf L Hm u y = x}
        zero_mem' := ⟨0, W.zero_mem, by simp [hf]⟩
        add_mem' := by
          rintro x x' ⟨y, hy, e⟩ ⟨y', hy', e'⟩
          exact ⟨y + y', W.add_mem hy hy', by rw [hf_add_right, e, e']; rfl⟩
        smul_mem' := by
          rintro c x ⟨y, hy, e⟩
          refine ⟨L.cj c • y, CongFin.smul_mem_of W (hcj c c.2).1 hy, ?_⟩
          rw [hf_smul_right, L.cj_cj, e]; rfl }
    refine ⟨I, fun h => hne ((Ideal.eq_top_iff_one I).1 h), fun a => ?_⟩
    exact ⟨⟨_, hUU u (hRU u hu) _ (hW (he a))⟩, ⟨e a, he a, rfl⟩, rfl⟩
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hM : algebraMap F E ((ϖ : F) ^ M) ∈ L.O := by rw [map_pow]; exact L.O.pow_mem hp M
  have hqa : (0 : ℝ) ≤ (resQ ϖ : ℝ) ^ a := by positivity
  have hR0 : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  rcases GlobalTheory.UnramOrder.proper_ideals L ϖ hϖ with h | ⟨π, hπ, hππ, h⟩
  · have h1 := hps (algebraMap F E ϖ) 2 hp (by rw [AlgEquiv.commutes, ← map_mul, sq])
      ⟨_, hM, by rw [← map_mul, pow_succ']⟩
    have hsub : (R.filter fun u => Z u ∧ ¬ ∃ y ∈ W, hf L Hm u y = 1) ⊆
        R.filter fun u => Z u ∧ ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = algebraMap F E ϖ * c := by
      intro u hu
      obtain ⟨hu, hz, hne⟩ := Finset.mem_filter.1 hu
      obtain ⟨I, hI, hIe⟩ := hI u hu hne
      refine Finset.mem_filter.2 ⟨hu, hz, fun a => ?_⟩
      obtain ⟨x, hx, e⟩ := hIe a
      exact e ▸ h I hI x hx
    have h2 : ((R.filter fun u => Z u ∧ ¬ ∃ y ∈ W, hf L Hm u y = 1).card : ℝ) ≤ _ :=
      Nat.cast_le.2 (Finset.card_le_card hsub)
    have h3 : (resQ ϖ : ℝ) ^ (((2 : ℕ) : ℤ) - (2 : ℕ) * ρ) ≤ (resQ ϖ : ℝ) ^ (1 - (ρ : ℤ)) :=
      zpow_le_zpow_right₀ hq1 (by push_cast; omega)
    have h4 : (0 : ℝ) ≤ (resQ ϖ : ℝ) ^ (1 - (ρ : ℤ)) := by positivity
    refine (mul_le_mul_of_nonneg_right h2 hqa).trans (h1.trans ?_)
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_left h3 (by norm_num)).trans (by linarith only [h4])) hR0
  · have h1 := hps π 1 hπ (by rw [hππ, pow_one])
      ⟨L.cj π * algebraMap F E ((ϖ : F) ^ M), L.O.mul_mem (hcj π hπ).1 hM, by
        rw [← mul_assoc, hππ, ← map_mul, pow_succ']⟩
    have h1' := hps (L.cj π) 1 (hcj π hπ).1 (by rw [L.cj_cj, mul_comm, hππ, pow_one])
      ⟨π * algebraMap F E ((ϖ : F) ^ M), L.O.mul_mem hπ hM, by
        rw [← mul_assoc, mul_comm _ π, hππ, ← map_mul, pow_succ']⟩
    have hsub : (R.filter fun u => Z u ∧ ¬ ∃ y ∈ W, hf L Hm u y = 1) ⊆
        (R.filter fun u => Z u ∧ ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c) ∪
        (R.filter fun u => Z u ∧ ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = L.cj π * c) := by
      intro u hu
      obtain ⟨hu, hz, hne⟩ := Finset.mem_filter.1 hu
      obtain ⟨I, hI, hIe⟩ := hI u hu hne
      rcases h I hI with h | h
      · refine Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hu, hz, fun a => ?_⟩)
        obtain ⟨x, hx, e⟩ := hIe a
        exact e ▸ h x hx
      · refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hu, hz, fun a => ?_⟩)
        obtain ⟨x, hx, e⟩ := hIe a
        exact e ▸ h x hx
    have h2 : ((R.filter fun u => Z u ∧ ¬ ∃ y ∈ W, hf L Hm u y = 1).card : ℝ) ≤ _ :=
      Nat.cast_le.2 ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
    rw [Nat.cast_add] at h2
    have h3 := mul_le_mul_of_nonneg_right h2 hqa
    simp only [Nat.cast_one, one_mul] at h1 h1'
    rw [add_mul] at h3
    linarith
end GlobalTheory.HL.QuadricShare
