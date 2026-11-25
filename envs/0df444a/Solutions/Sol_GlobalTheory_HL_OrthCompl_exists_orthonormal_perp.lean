-- Prove2me | solution 1 for GlobalTheory.HL.OrthCompl.exists_orthonormal_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:59:56.426611+00:00
-- url     : https://prove2.me/submissions/7ccf0d94-87fc-4f61-82d1-d7aef604868f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNormOneOrthTriple
import Theorems.Thm_GlobalTheory_HL_OrthCompl_exists_isON_orth_family
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_add_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_smul_r
import Theorems.Thm_GlobalTheory_HL_SelfDual_orthonormal_basis_and_one_orbit
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OrthCompl
namespace GlobalTheory.HL.OrthCompl
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (y : Fin m → Fin n → E), LinearIndependent E y → ∃ u : Fin (n - 2 * m) → Fin n → E, (∀ i, u i ∈ Λ ∧ u i ∈ perp L Hm (Submodule.span E (Set.range y))) ∧ ∀ i j, hf L Hm (u i) (u j) = if i = j then 1 else 0 := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH Λ hΛ m y _
  by_cases hn : 2 * m ≤ n
  · obtain ⟨b, hb, hΛb⟩ := (GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit L Hm hH).1 Λ hΛ
    have hk : n - 2 * m + 2 * m = n := Nat.sub_add_cancel hn
    obtain ⟨u, hu, hu'⟩ := exists_isON_orth_family L hH.1 (n - 2 * m) m y Λ
      (fun i => b (Fin.cast hk i)) (fun i => hΛb ▸ Submodule.subset_span ⟨_, rfl⟩)
      (fun i j => by simpa using hb (Fin.cast hk i) (Fin.cast hk j))
    refine ⟨u, fun i => ⟨(hu i).1, fun z hz => ?_⟩, hu'⟩
    induction hz using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact (hu i).2 j
    | zero => simp [hf]
    | add a b _ _ ha hb => rw [Eichler.hf_add_r, ha, hb, add_zero]
    | smul c a _ ha => rw [Eichler.hf_smul_r, ha, mul_zero]
  · have h0 : ∀ i : Fin (n - 2 * m), False := fun i => by have := i.2; omega
    exact ⟨fun _ => 0, fun i => (h0 i).elim, fun i => (h0 i).elim⟩
end GlobalTheory.HL.OrthCompl
