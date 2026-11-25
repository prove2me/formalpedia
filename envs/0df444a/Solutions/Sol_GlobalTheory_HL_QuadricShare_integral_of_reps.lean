-- Prove2me | solution 1 for GlobalTheory.HL.QuadricShare.integral_of_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:53:19.199968+00:00
-- url     : https://prove2.me/submissions/564e5b8d-7553-4154-b7a9-118b098bd78f

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
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_CongFin_exists_pow_mul_mem
import Theorems.Thm_GlobalTheory_HL_CongFin_exists_pow_smul_mem
import Theorems.Thm_GlobalTheory_HL_GaussSummand_hf_add_right
import Theorems.Thm_GlobalTheory_HL_GaussSummand_hf_smul_left
import Theorems.Thm_GlobalTheory_HL_GaussSummand_hf_smul_right
import Theorems.Thm_GlobalTheory_PowSmulMem_exists_pow_smul_mem
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
theorem _root_.solution (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (Λ : Submodule L.O (Fin n → E))
    (hΛ : IsSD L Hm Λ) (UU : Submodule L.O (Fin n → E)) (hUΛ : UU ≤ Λ) (N : ℕ) (hN : 1 ≤ N)
    (R : Finset (Fin n → E))
    (hR : ∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y)
    (y : Fin n → E) (hy : ∀ u ∈ R, algebraMap F E ((ϖ : F) ^ N) * hf L Hm y u ∈ L.O) :
    ∀ u ∈ UU, algebraMap F E ((ϖ : F) ^ N) * hf L Hm y u ∈ L.O := by
  obtain ⟨-, -, -, -, hint, -, -, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hp : algebraMap F E ϖ ∈ L.O := (hint _).2 ϖ.2
  obtain ⟨M, hM⟩ := CongFin.exists_pow_smul_mem hp (CongFin.exists_pow_mul_mem L ϖ hϖ)
    (Submodule.span L.O {y}) Λ (Submodule.fg_span_singleton y) hΛ.1.2
  have hMy := hM y (Submodule.mem_span_singleton_self y)
  simp only [map_pow] at hR hy ⊢
  have hcp : L.cj (algebraMap F E ϖ ^ N) = algebraMap F E ϖ ^ N := by
    rw [map_pow, AlgEquiv.commutes]
  set p := algebraMap F E ϖ with hpdef
  have key : ∀ m : ℕ, (∀ u ∈ UU, p ^ m * (p ^ N * hf L Hm y u) ∈ L.O) →
      ∀ u ∈ UU, p ^ N * hf L Hm y u ∈ L.O := by
    intro m
    induction m with
    | zero => intro h u hu; simpa using h u hu
    | succ m ih =>
      intro h
      refine ih fun u hu => ?_
      obtain ⟨w, ⟨hw, z, hz, e⟩, -⟩ := hR u hu
      have e' : u = w + p ^ N • z := by rw [← e]; abel
      obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
      rw [e', hf_add_right, hf_smul_right, hcp]
      have := L.O.add_mem (L.O.mul_mem (L.O.pow_mem hp m) (hy w hw))
        (L.O.mul_mem (L.O.pow_mem hp K) (h z hz))
      convert this using 1
      ring
  refine key M fun u hu => ?_
  have h1 := (hΛ.2 u).2 (hUΛ hu) _ hMy
  rw [hf_smul_left] at h1
  rw [mul_left_comm]
  exact L.O.mul_mem (L.O.pow_mem hp N) h1
end GlobalTheory.HL.QuadricShare
