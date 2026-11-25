-- Prove2me | solution 1 for GlobalTheory.HL.QuadricShare.char_share
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:52:56.602419+00:00
-- url     : https://prove2.me/submissions/453a4f0a-fc17-472f-9c3c-693b0b68d887

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
import Theorems.Thm_GlobalTheory_HL_CharCond_expand_by_conductor
import Theorems.Thm_GlobalTheory_HL_GaussSum_norm_gauss_sum_le
import Theorems.Thm_GlobalTheory_HL_GaussSummand_norm_gauss_sum_le
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
    (χ : AddChar (Fin n → E) ℂ) (hχ1 : ∀ u, ‖χ u‖ = 1)
    (hχ : ∀ u ∈ UU, χ (algebraMap F E ((ϖ : F) ^ N) • u) = 1) :
    ‖(∑ u ∈ R.filter Z, χ u) * (resQ ϖ : ℂ) ^ a - ∑ u ∈ R, χ u‖ ≤
      8 / 7 * (resQ ϖ : ℝ) ^ (1 - (ρ : ℤ)) * R.card := by
  obtain ⟨-, -, -, -, -, -, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨ψ, hψ1, hψ, -⟩ := GlobalTheory.TraceChar.exists_trace_char L
  obtain ⟨nrm, Q, hnrm, hQ, hdvd⟩ := exists_norm L Hm hH ϖ hϖ UU hUU
  have hfil : R.filter Z = R.filter (fun u => ϖ ^ a ∣ Q u) :=
    Finset.filter_congr fun u hu => by rw [hZ, hdvd a u (hRU u hu)]
  have h := GlobalTheory.HL.CharCond.expand_by_conductor ϖ hϖ ψ hψ R Q χ a
    (fun i => (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(i * ρ : ℤ))) (fun i hi hia t u₀ ht => by
      rw [Finset.sum_congr rfl fun u hu => by rw [hQ u (hRU u hu)]]
      exact norm_gauss_sum_le L Hm hH ϖ hϖ ψ hψ1 hψ UU hUU ρ e he hee i N hi (hia.trans haN) t u₀ ht
        χ hχ1 hχ R nrm hnrm hRU hR)
  rw [hfil]
  refine h.trans ?_
  have h2 := (GlobalTheory.two_geometric_sums_index_bound (resQ ϖ) ρ a hq hρ).1
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _))
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring
end GlobalTheory.HL.QuadricShare
