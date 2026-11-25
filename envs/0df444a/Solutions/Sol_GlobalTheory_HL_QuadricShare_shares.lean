-- Prove2me | solution 1 for GlobalTheory.HL.QuadricShare.shares
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:20:22.773015+00:00
-- url     : https://prove2.me/submissions/46d32e74-ffe2-44d4-88b7-1644f575dd74

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
import Theorems.Thm_GlobalTheory_HL_QuadricShare_sum_char_eq_zero
import Theorems.Thm_GlobalTheory_HL_QuadricShare_char_share
import Theorems.Thm_GlobalTheory_HL_QuadricShare_leak_share
import Theorems.Thm_GlobalTheory_HL_QuadricShare_integral_of_reps
import Theorems.Thm_GlobalTheory_HL_QuadricShare_perp_anti
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_FrameLevel_main
import Theorems.Thm_GlobalTheory_HL_GaussSummand_hf_add_right
import Theorems.Thm_GlobalTheory_HL_GaussSummand_hf_smul_right
import Theorems.Thm_GlobalTheory_HL_OrthCompl_exists_orthonormal_perp
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem
import Theorems.Thm_GlobalTheory_HL_TermBasic_term_basic
import Theorems.Thm_GlobalTheory_LengthDualFunctional_main
import Theorems.Thm_GlobalTheory_LengthQuotientSpanValuation_main
import Theorems.Thm_GlobalTheory_PowSmulMem_main
import Theorems.Thm_GlobalTheory_T_term_exponents_nonneg_and_defect_group_bound
import Theorems.Thm_GlobalTheory_TraceChar_exists_trace_char
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.QuadricShare
open GlobalTheory.HL.GaussSummand
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
  {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.HL.QuadricShare
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (N : ℕ) (R : Finset S.V) (Z : S.V → Prop), S.a + 1 ≤ N → (∀ u, Z u ↔ ∃ c : 𝒪[F], S.h u u = algebraMap F E ((S.ϖ : F) ^ S.a * c)) → (∀ u ∈ R, u ∈ Λ ∧ u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)) → (∀ u ∈ Λ, u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J) → ∃! w, w ∈ R ∧ ∃ y ∈ Λ, u - w = algebraMap F E ((S.ϖ : F) ^ N) • y) → |((R.filter Z).card : ℝ) - R.card / (S.q : ℝ) ^ S.a| ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a) ∧ (((R.filter fun u => Z u ∧ ¬ ∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1).card : ℝ) ≤ 16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a)) ∧ ∀ y : S.V, (∀ u ∈ R, algebraMap F E ((S.ϖ : F) ^ N) * S.h y u ∈ L.O) → (∃ u ∈ R, L.psi0 (S.h y u) ≠ 1) → ‖∑ u ∈ R.filter Z, L.psi0 (S.h y u)‖ ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk J d Λ hT N R Z haN hZ hRU hR
  obtain ⟨-, hcj, -, -, hint, -, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr
  have hSD := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).1
  have hli := (GlobalTheory.FrameBasic.main L r k S).1
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).1
  rw [ha] at haN hZ ⊢
  simp only [zpow_natCast] at hZ ⊢
  have haN' : a + 1 ≤ N := by omega
  obtain ⟨e, he, hee⟩ := GlobalTheory.HL.OrthCompl.exists_orthonormal_perp L S.Hm S.herm Λ hSD _ _
    (hli.comp finSumFinEquiv.symm finSumFinEquiv.symm.injective)
  have hsp : ∀ j, S.spanTo S.f j ⊔ S.spanTo S.f' j ≤
      Submodule.span E (Set.range (Sum.elim S.f S.f' ∘ finSumFinEquiv.symm)) := by
    intro j
    rw [finSumFinEquiv.symm.surjective.range_comp]
    refine sup_le (Submodule.span_mono ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨i, -, rfl⟩; exact ⟨Sum.inl i, rfl⟩
    · rintro _ ⟨i, -, rfl⟩; exact ⟨Sum.inr i, rfl⟩
  let ρ := k + 2 * r + 1 - 2 * (r + 1 + (r + 1))
  have hρdef : ρ = k + 2 * r + 1 - 2 * (r + 1 + (r + 1)) := rfl
  have hρ : 4 ≤ ρ := by omega
  have hρ' : (k : ℤ) - 2 * r - 3 = ρ := by omega
  rw [hρ']
  let UU : Submodule L.O S.V :=
    Λ ⊓ (perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)).restrictScalars L.O
  let W : Submodule L.O S.V := Λ ⊓ S.W0.restrictScalars L.O
  have hJ : S.spanTo S.f J ⊔ S.spanTo S.f' J ≤ S.ME :=
    sup_le_sup (Submodule.span_mono (Set.image_mono fun i _ => i.2))
      (Submodule.span_mono (Set.image_mono fun i _ => i.2))
  have hW : W ≤ UU := fun x hx => ⟨hx.1, perp_anti L S.Hm hJ hx.2⟩
  have heW : ∀ i, e i ∈ W := fun i => ⟨(he i).1, perp_anti L S.Hm (hsp (r + 1)) (he i).2⟩
  have hUU : ∀ x ∈ UU, ∀ y ∈ UU, hf L S.Hm x y ∈ L.O := fun x hx y hy => (hSD.2 y).2 hy.1 x hx.1
  have hRU' : ∀ u ∈ R, u ∈ UU := hRU
  have hu : IsUnit (algebraMap F E ((S.ϖ : F) ^ N)) :=
    ((IsUnit.mk0 (S.ϖ : F) (fun h => S.ϖ_irr.ne_zero (Subtype.ext h))).pow N).map _
  have hR' : ∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((S.ϖ : F) ^ N) • y := by
    intro u hu'
    refine (existsUnique_congr fun w => and_congr_right fun hw => ?_).1 (hR u hu'.1 hu'.2)
    constructor
    · rintro ⟨y, hy, e⟩
      refine ⟨y, ⟨hy, ?_⟩, e⟩
      have h1 : algebraMap F E ((S.ϖ : F) ^ N) • y ∈
          perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J) :=
        e ▸ Submodule.sub_mem _ hu'.2 (hRU w hw).2
      exact (Submodule.smul_mem_iff_of_isUnit _ hu).1 h1
    · rintro ⟨y, hy, e⟩
      exact ⟨y, hy.1, e⟩
  have hcs := char_share L S.Hm S.herm S.ϖ S.ϖ_irr UU hUU ρ hρ e (fun i => hW (heW i)) hee a N
    (by omega) R hRU' hR' Z hZ
  have hqa : (0 : ℝ) < (S.q : ℝ) ^ a := by
    have : (0 : ℝ) < S.q := by exact_mod_cast (by omega : 0 < resQ S.ϖ)
    positivity
  refine ⟨?_, ?_, fun y hy ⟨u₀, hu₀, hne⟩ => ?_⟩
  · have h := hcs 1 (by simp) (by simp)
    simp only [AddChar.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    have h1 : ‖((R.filter Z).card : ℂ) * (resQ S.ϖ : ℂ) ^ a - R.card‖ =
        |((R.filter Z).card : ℝ) * (S.q : ℝ) ^ a - R.card| := by
      rw [← Real.norm_eq_abs, ← Complex.norm_real]
      push_cast; rfl
    rw [h1] at h
    rw [← mul_div_assoc, le_div_iff₀ hqa, ← abs_of_pos hqa, ← abs_mul, abs_of_pos hqa, sub_mul,
      div_mul_cancel₀ _ hqa.ne']
    exact h
  · have h := leak_share L S.Hm S.herm S.ϖ S.ϖ_irr UU hUU ρ hρ e W hW heW hee a N haN' R hRU' hR' Z hZ
    rw [← mul_div_assoc, le_div_iff₀ hqa]
    refine le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Finset.card_le_card ?_)) hqa.le) h
    intro u hu'
    simp only [Finset.mem_filter] at hu' ⊢
    refine ⟨hu'.1, hu'.2.1, ?_⟩
    rintro ⟨y, ⟨h1, h2⟩, h3⟩
    exact hu'.2.2 ⟨y, h1, h2, h3⟩
  · obtain ⟨ψ, hψ1, -, hψ⟩ := GlobalTheory.TraceChar.exists_trace_char L
    let φ : S.V →+ E := AddMonoidHom.mk' (fun u => hf L S.Hm y u) (hf_add_right L S.Hm y)
    let χ : AddChar S.V ℂ := L.psi0.compAddMonoidHom φ
    have hχ1 : ∀ u, ‖χ u‖ = 1 := fun u => by
      obtain ⟨c, hc⟩ := (L.cj_fix (φ u + L.cj (φ u))).1 (by rw [map_add, L.cj_cj, add_comm])
      change ‖L.psi0 (φ u)‖ = 1
      rw [hψ _ c hc.symm, hψ1]
    have hint' := integral_of_reps L S.Hm S.ϖ S.ϖ_irr Λ hSD UU inf_le_left N (by omega) R hR' y hy
    have hχ : ∀ u ∈ UU, χ (algebraMap F E ((S.ϖ : F) ^ N) • u) = 1 := fun u hu' => by
      change L.psi0 (hf L S.Hm y _) = 1
      rw [hf_smul_right, AlgEquiv.commutes]
      simpa using (L.additive_character_dual_ring _).2 (hint' u hu') 1 L.O.one_mem
    have h := hcs χ hχ1 hχ
    rw [sum_char_eq_zero UU _ R hRU' hR' χ hχ u₀ hu₀ hne, sub_zero, norm_mul, norm_pow,
      Complex.norm_natCast] at h
    rw [← mul_div_assoc, le_div_iff₀ hqa]
    exact h
end GlobalTheory.HL.QuadricShare
