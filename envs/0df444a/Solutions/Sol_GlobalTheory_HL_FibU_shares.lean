-- Prove2me | solution 1 for GlobalTheory.HL.FibU.shares
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:31.745223+00:00
-- url     : https://prove2.me/submissions/ca5e245c-c001-4cec-a4db-a8606be6fe67

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuadricCharacterLeakSharesFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqMeanOverRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPowSmulMemOfIsLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermIntegralNearOneBound
import Theorems.Thm_GlobalTheory_HL_FibU_hf_addr
import Theorems.Thm_GlobalTheory_HL_FibU_hf_smull
import Theorems.Thm_GlobalTheory_HL_FibU_hf_smulr
import Theorems.Thm_GlobalTheory_HL_FibU_exists_pow_smul
import Theorems.Thm_GlobalTheory_HL_FibU_inZ_add
import Theorems.Thm_GlobalTheory_HL_FibU_noLeak_add
import Theorems.Thm_GlobalTheory_HL_FibU_exists_reps_refU
import Theorems.Thm_GlobalTheory_HL_FibU_cint_eq_mean
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_FrameLevel_main
import Theorems.Thm_GlobalTheory_LengthDualFunctional_main
import Theorems.Thm_GlobalTheory_LengthQuotientSpanValuation_main
import Theorems.Thm_GlobalTheory_PowSmulMem_main
import Theorems.Thm_GlobalTheory_T_hermitian_double_coset_term_basic_facts
import Theorems.Thm_GlobalTheory_T_quadric_character_leak_shares_finite
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FibU
namespace GlobalTheory.HL.FibU
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → |(cint (S.refU J Λ) (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u)).re * (S.q : ℝ) ^ S.a - 1| ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ (cint (S.refU J Λ) (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u ∧ ¬ S.NoLeak Λ u)).re * (S.q : ℝ) ^ S.a ≤ 16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ ∀ y : S.V, (∃ u ∈ S.refU J Λ, L.psi0 (S.h y u) ≠ 1) → ‖cint (S.refU J Λ) (fun u => ind (fun u => u ∈ S.refU J Λ ∧ S.InZ u) u * L.psi0 (S.h y u))‖ * (S.q : ℝ) ^ S.a ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk J d Λ hT
  have hΛ : IsSD L S.Hm Λ := (GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT).1
  have hq : (0 : ℝ) < (S.q : ℝ) ^ S.a := by
    obtain ⟨-, -, -, -, -, -, h7, -⟩ := GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr
    have : 0 < S.q := lt_of_lt_of_le two_pos h7
    positivity
  have main : ∀ N : ℕ, S.a + 1 ≤ N → 1 ≤ N → ∃ R : Finset S.V, (0 : ℝ) < R.card ∧ (∀ w ∈ R, w ∈ S.refU J Λ) ∧
      (∀ w ∈ S.refU J Λ, ∃! x, x ∈ R ∧ w - x ∈ mulP S Λ N) := by
    intro N _ _
    obtain ⟨R, h1, h2⟩ := exists_reps_refU S hΛ J N
    obtain ⟨x, ⟨hx, -⟩, -⟩ := h2 0 (zero_mem _)
    exact ⟨R, by exact_mod_cast Finset.card_pos.2 ⟨x, hx⟩, h1, h2⟩
  have hZ : ∀ N : ℕ, S.a + 1 ≤ N → ∀ w ∈ S.refU J Λ, ∀ b ∈ mulP S Λ N, S.InZ w → S.InZ (w + b) := by
    rintro N hN w hw _ ⟨y, hy, rfl⟩ h
    exact inZ_add S hΛ (by omega) hw.1 hy h
  set ε : ℝ := (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) with hε
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨R, h0, h1, h2⟩ := main (S.a.toNat + 1) (by omega) (by omega)
    have h3 := (GlobalTheory.T.quadric_character_leak_shares_finite L r k S hk J d Λ hT (S.a.toNat + 1) R S.InZ (by omega) (fun _ => Iff.rfl)
      h1 (fun u hu hu' => h2 u ⟨hu, hu'⟩)).1
    have h4 := cint_eq_mean _ _ R S.InZ (fun _ => 1) h1 h2 (hZ _ (by omega)) (fun _ _ _ => rfl)
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h4
    have h5 : (cint (S.refU J Λ) (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u)).re =
        ((R.filter S.InZ).card : ℝ) / R.card := by
      rw [show (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u) = fun u => (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u) u
        from rfl, h4, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
        Complex.ofReal_re]
    rw [h5]
    have h6 : ((R.filter S.InZ).card : ℝ) / R.card * (S.q : ℝ) ^ S.a - 1 =
        (((R.filter S.InZ).card : ℝ) - R.card / (S.q : ℝ) ^ S.a) / (R.card / (S.q : ℝ) ^ S.a) := by
      field_simp
    rw [h6, abs_div, abs_of_pos (div_pos h0 hq), div_le_iff₀ (div_pos h0 hq)]
    exact h3
  · obtain ⟨R, h0, h1, h2⟩ := main (S.a.toNat + 1) (by omega) (by omega)
    have h3 := (GlobalTheory.T.quadric_character_leak_shares_finite L r k S hk J d Λ hT (S.a.toNat + 1) R S.InZ (by omega) (fun _ => Iff.rfl)
      h1 (fun u hu hu' => h2 u ⟨hu, hu'⟩)).2.1
    have h4 := cint_eq_mean _ _ R (fun u => S.InZ u ∧ ¬ S.NoLeak Λ u) (fun _ => 1) h1 h2
      (fun w hw b hb h => ⟨hZ _ (by omega) w hw b hb h.1, fun h' => h.2 (by
        obtain ⟨y, hy, hb'⟩ := (mulP S Λ _).neg_mem hb
        have := noLeak_add S hΛ (N := S.a.toNat + 1) (by omega) hy h'
        rwa [← hb', add_neg_cancel_right] at this)⟩) (fun _ _ _ => rfl)
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h4
    have h5 : (cint (S.refU J Λ) (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u ∧ ¬ S.NoLeak Λ u)).re =
        ((R.filter fun u => S.InZ u ∧ ¬ S.NoLeak Λ u).card : ℝ) / R.card := by
      rw [show (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u ∧ ¬ S.NoLeak Λ u) =
        fun u => (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u ∧ ¬ S.NoLeak Λ u) u
        from rfl, h4, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
        Complex.ofReal_re]
      congr
    rw [h5]
    have h6 : ∀ c : ℝ, c / R.card * (S.q : ℝ) ^ S.a = c / (R.card / (S.q : ℝ) ^ S.a) := by
      intro c
      field_simp
    rw [h6, div_le_iff₀ (div_pos h0 hq)]
    refine le_trans (le_of_eq ?_) h3
    congr 2
  · rintro y ⟨u, hu, hne⟩
    obtain ⟨m, hm⟩ := exists_pow_smul L S.ϖ S.ϖ_irr Λ hΛ.1 y
    obtain ⟨R, h0, h1, h2⟩ := main (m + (S.a.toNat + 1)) (by omega) (by omega)
    have hint : ∀ z ∈ Λ, algebraMap F E ((S.ϖ : F) ^ (m + (S.a.toNat + 1))) * S.h y z ∈ L.O := by
      intro z hz
      have := L.O.mul_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (pow_mem S.ϖ.2 (S.a.toNat + 1)))
        ((hΛ.2 z).2 hz _ hm)
      rw [hf_smull] at this
      convert this using 1
      rw [pow_add, map_mul, Frames.h]
      ring
    have hg : ∀ w, ∀ b ∈ mulP S Λ (m + (S.a.toNat + 1)), L.psi0 (S.h y (w + b)) = L.psi0 (S.h y w) := by
      rintro w _ ⟨z, hz, rfl⟩
      have := (L.additive_character_dual_ring _).2 (hint z hz) 1 L.O.one_mem
      rw [mul_one] at this
      unfold Frames.h at this ⊢
      rw [hf_addr, hf_smulr, AlgEquiv.commutes, AddChar.map_add_eq_mul, this, mul_one]
    have h3 := (GlobalTheory.T.quadric_character_leak_shares_finite L r k S hk J d Λ hT (m + (S.a.toNat + 1)) R S.InZ (by omega) (fun _ => Iff.rfl)
      h1 (fun u hu hu' => h2 u ⟨hu, hu'⟩)).2.2 y (fun u hu => hint u (h1 u hu).1) (by
        obtain ⟨x, ⟨hx, hx'⟩, -⟩ := h2 u hu
        refine ⟨x, hx, ?_⟩
        rwa [← hg x _ hx', add_sub_cancel])
    have h4 := cint_eq_mean _ _ R S.InZ (fun u => L.psi0 (S.h y u)) h1 h2 (hZ _ (by omega)) hg
    have h6 : ∀ c : ℝ, c / R.card * (S.q : ℝ) ^ S.a = c / (R.card / (S.q : ℝ) ^ S.a) := by
      intro c
      field_simp
    rw [h4, norm_div, Complex.norm_natCast, h6, div_le_iff₀ (div_pos h0 hq)]
    exact h3
end GlobalTheory.HL.FibU
