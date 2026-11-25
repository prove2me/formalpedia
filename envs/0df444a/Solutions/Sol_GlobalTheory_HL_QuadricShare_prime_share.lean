-- Prove2me | solution 1 for GlobalTheory.HL.QuadricShare.prime_share
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:50.195479+00:00
-- url     : https://prove2.me/submissions/a1575c4c-5dec-4675-80ed-e41fe072ef66

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
import Theorems.Thm_GlobalTheory_HL_QuadricShare_exists_norm
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_CharCond_expand_by_conductor
import Theorems.Thm_GlobalTheory_T_hermitian_local_character_sum
import Theorems.Thm_GlobalTheory_TraceChar_exists_trace_char
import Theorems.Thm_GlobalTheory_UnramOrder_exists_norm
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
import Theorems.Thm_GlobalTheory_two_geometric_sums_index_bound
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
    (ρ : ℕ) (hρ : 4 ≤ ρ) (e : Fin ρ → Fin n → E) (he : ∀ a, e a ∈ UU)
    (hee : ∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) (a N : ℕ) (haN : a ≤ N)
    (R : Finset (Fin n → E)) (hRU : ∀ u ∈ R, u ∈ UU)
    (hR : ∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y)
    (Z : (Fin n → E) → Prop)
    (hZ : ∀ u, Z u ↔ ∃ c : 𝒪[F], hf L Hm u u = algebraMap F E ((ϖ : F) ^ a * c))
    (π : E) (j : ℕ) (hπ : π ∈ L.O) (hπj : π * L.cj π = algebraMap F E ((ϖ : F) ^ j))
    (hπN : ∃ c ∈ L.O, algebraMap F E ((ϖ : F) ^ N) = π * c) :
    ((R.filter fun u => Z u ∧ ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c).card : ℝ) * (resQ ϖ : ℝ) ^ a ≤
      8 / 7 * (resQ ϖ : ℝ) ^ ((j : ℤ) - j * ρ) * R.card := by
  obtain ⟨-, -, -, -, -, -, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨ψ, hψ1, hψ, -⟩ := GlobalTheory.TraceChar.exists_trace_char L
  obtain ⟨nrm, Q, hnrm, hQ, hdvd⟩ := exists_norm L Hm hH ϖ hϖ UU hUU
  obtain ⟨hc, hg⟩ := GlobalTheory.T.hermitian_local_character_sum L Hm hH ϖ hϖ ψ hψ1 hψ UU hUU ρ e he hee π j N hπ hπj hπN R nrm hnrm
    hRU hR
  set R' := R.filter fun u => ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c with hR'
  have hfil : (R.filter fun u => Z u ∧ ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c)
      = R'.filter (fun u => ϖ ^ a ∣ Q u) := by
    rw [hR', Finset.filter_filter]
    exact Finset.filter_congr fun u hu => by rw [hZ, hdvd a u (hRU u hu), and_comm]
  have h := GlobalTheory.HL.CharCond.expand_by_conductor ϖ hϖ ψ hψ R' Q (fun _ => 1) a
    (fun i => (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) * (resQ ϖ : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ)))
    (fun i hi hia t u₀ ht => by
      rw [Finset.sum_congr rfl fun u hu => by
        rw [hQ u (hRU u (Finset.mem_filter.1 hu).1), mul_one]]
      exact hg i (hia.trans haN) t u₀ ht)
  rw [hfil]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have h1 : ((R'.filter (fun u => ϖ ^ a ∣ Q u)).card : ℝ) * (resQ ϖ : ℝ) ^ a - R'.card ≤
      ‖((R'.filter (fun u => ϖ ^ a ∣ Q u)).card : ℂ) * (resQ ϖ : ℂ) ^ a - R'.card‖ := by
    refine (le_abs_self _).trans (le_of_eq ?_)
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    push_cast; rfl
  have h2 := (GlobalTheory.two_geometric_sums_index_bound (resQ ϖ) ρ a hq hρ).2 j
  have hq0 : (0 : ℝ) < resQ ϖ := by exact_mod_cast (by omega : 0 < resQ ϖ)
  have h3 := mul_le_mul_of_nonneg_left h2
    (by positivity : (0 : ℝ) ≤ (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)))
  rw [mul_add, mul_one, Finset.mul_sum] at h3
  have h4 : ∑ i ∈ Finset.Icc 1 a, ((resQ ϖ : ℝ) ^ i - (resQ ϖ : ℝ) ^ (i - 1)) *
      ((R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) * (resQ ϖ : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ))) =
      ∑ i ∈ Finset.Icc 1 a, (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) *
      (((resQ ϖ : ℝ) ^ i - (resQ ϖ : ℝ) ^ (i - 1)) * (resQ ϖ : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ))) :=
    Finset.sum_congr rfl fun i _ => by ring
  have h5 : 8 / 7 * (resQ ϖ : ℝ) ^ ((j : ℤ) - j * ρ) * R.card =
      (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) * (8 / 7 * (resQ ϖ : ℝ) ^ j) := by
    rw [sub_eq_add_neg, zpow_add₀ hq0.ne', zpow_natCast]; ring
  rw [h5]
  rw [h4] at h
  linarith
end GlobalTheory.HL.QuadricShare
