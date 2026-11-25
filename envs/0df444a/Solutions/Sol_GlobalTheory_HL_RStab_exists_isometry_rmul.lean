-- Prove2me | solution 1 for GlobalTheory.HL.RStab.exists_isometry_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:56:26.70022+00:00
-- url     : https://prove2.me/submissions/58ec23ee-10d9-4e89-9071-56f333ae57eb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryNearIdentityCloseTuplesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryTupleMatrixRightMulNearIdentity
import Theorems.Thm_GlobalTheory_HL_RStab_gramT_scale
import Theorems.Thm_GlobalTheory_HL_RStab_rmul_sub
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_ContModel_gramT_rmul
import Theorems.Thm_GlobalTheory_T_exists_isometry_near_identity_close_tuples
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.RStab
namespace GlobalTheory.HL.RStab
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsUnit Γ.det → ∀ N e : ℕ, ∃ i0 : ℕ, ∀ i ≥ i0, ∀ x : Fin m → Fin n → E, (∀ a, algebraMap F E ((ϖ : F) ^ e) • x a ∈ Λ) → gramT L Hm x = Γ → ∀ A ∈ congK L ϖ m i, cT L A * Γ * A = Γ → ∃ g ∈ isomG L Hm, CongId L ϖ Λ N g ∧ ∀ a, g (x a) = rmul x A a := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λ hΛ m Γ hΓ N e
  have h0 : ((ϖ : F) ^ e) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)
  have ht : IsUnit (algebraMap F E ((ϖ : F) ^ e)) := (IsUnit.mk0 _ h0).map _
  set t := algebraMap F E ((ϖ : F) ^ e) with htdef
  have hΓ' : IsUnit ((t * t) • Γ).det := by
    rw [Matrix.det_smul]; exact ((ht.mul ht).pow _).mul hΓ
  obtain ⟨N', hN'⟩ := GlobalTheory.T.exists_isometry_near_identity_close_tuples L ϖ hϖ Hm hH Λ hΛ m _ hΓ' N
  refine ⟨N', fun i hi x hx hG A hA hAΓ => ?_⟩
  have hϖO : algebraMap F E ((ϖ : F) ^ (i - N')) ∈ L.O := by
    rw [L.O_def]
    have h1 : IsIntegral 𝒪[F] ((ϖ : F) ^ (i - N')) :=
      (isIntegral_algebraMap (R := 𝒪[F]) (A := F) (x := ϖ)).pow _
    exact h1.map (IsScalarTower.toAlgHom 𝒪[F] F E)
  obtain ⟨g, hg, hc, hgx⟩ := hN' (fun a => t • x a) (fun a => t • rmul x A a) hx
    (by rw [gramT_scale, hG]) (by rw [gramT_scale, ContModel.gramT_rmul, hG, hAΓ]) (by
      intro a
      choose c hc hc' using hA
      refine ⟨∑ j, (algebraMap F E ((ϖ : F) ^ (i - N')) * c j a) • t • x j, ?_, ?_⟩
      · refine Λ.sum_mem fun j _ => ?_
        exact Λ.smul_mem (⟨_, L.O.mul_mem hϖO (hc j a)⟩ : L.O) (hx j)
      · rw [← smul_sub, rmul_sub, Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hc', smul_smul, smul_smul, smul_smul]
        congr 1
        have : (ϖ : F) ^ i = (ϖ : F) ^ N' * (ϖ : F) ^ (i - N') := by
          rw [← pow_add]; congr 1; omega
        rw [this, map_mul]; ring)
  refine ⟨g, hg, hc, fun a => ?_⟩
  have h := hgx a
  simp only [map_smul] at h
  exact ht.smul_left_cancel.1 h
end GlobalTheory.HL.RStab
