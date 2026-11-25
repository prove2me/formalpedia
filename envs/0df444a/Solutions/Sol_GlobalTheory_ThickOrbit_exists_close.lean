-- Prove2me | solution 1 for GlobalTheory.ThickOrbit.exists_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:32:39.933943+00:00
-- url     : https://prove2.me/submissions/4c02df21-1c5d-4993-a233-9089782b820f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryNearIdentityCloseTuplesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryTupleMatrixRightMulNearIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ThickOrbitSelfDualUnramifiedLattice
import Theorems.Thm_GlobalTheory_ThickOrbit_pow_mem
import Theorems.Thm_GlobalTheory_ThickOrbit_smul_mem
import Theorems.Thm_GlobalTheory_ThickOrbit_pow_add_smul
import Theorems.Thm_GlobalTheory_ThickOrbit_isUnit_pow
import Theorems.Thm_GlobalTheory_ThickOrbit_rmul_rmul
import Theorems.Thm_GlobalTheory_ThickOrbit_rmul_one
import Theorems.Thm_GlobalTheory_ThickOrbit_rmul_add
import Theorems.Thm_GlobalTheory_ThickOrbit_rmul_smul
import Theorems.Thm_GlobalTheory_ThickOrbit_rmul_mem
import Theorems.Thm_GlobalTheory_ThickOrbit_rmul_cong
import Theorems.Thm_GlobalTheory_ThickOrbit_cT_mul
import Theorems.Thm_GlobalTheory_ThickOrbit_cT_one
import Theorems.Thm_GlobalTheory_ThickOrbit_gramT_smul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_CongGrp_cT_mul
import Theorems.Thm_GlobalTheory_CongGrp_cT_one
import Theorems.Thm_GlobalTheory_CongTrans_cT_mul
import Theorems.Thm_GlobalTheory_CongTrans_cT_one
import Theorems.Thm_GlobalTheory_HL_ContModel_gramT_rmul
import Theorems.Thm_GlobalTheory_HL_Model_hf_add_left
import Theorems.Thm_GlobalTheory_HL_Model_hf_add_right
import Theorems.Thm_GlobalTheory_HL_Model_hf_smul_left
import Theorems.Thm_GlobalTheory_HL_Model_hf_smul_right
import Theorems.Thm_GlobalTheory_HL_Model_hf_symm
import Theorems.Thm_GlobalTheory_T_congruentOneMatrices_transitive_near_hermitian
import Theorems.Thm_GlobalTheory_T_exists_isometry_near_identity_close_tuples
import Theorems.Thm_GlobalTheory_T_matrixCongruentOneModUniformizerPow_group_and_orbits
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
open GlobalTheory GlobalTheory.ThickOrbit
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.ThickOrbit
theorem _root_.solution (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {n : ℕ}
    {Hm : Matrix (Fin n) (Fin n) E} (hH : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)}
    (hΛ : IsSD L Hm Λ) {m : ℕ} {Γ : Matrix (Fin m) (Fin m) E} (hh : IsHerm L Γ) (hΓ : IsUnit Γ.det)
    (N e i : ℕ) (hi : 1 ≤ i) : ∃ M : ℕ, ∀ y u : Fin m → Fin n → E,
      (∀ a, algebraMap F E ((ϖ : F) ^ e) • y a ∈ Λ) → gramT L Hm y = Γ → (∀ a, u a ∈ Λ) →
      ∃ g ∈ isomG L Hm, CongId L ϖ Λ N g ∧ ∃ A ∈ congK L ϖ m i,
        y + algebraMap F E ((ϖ : F) ^ M) • u = rmul (fun a => g (y a)) A := by
  have hpe := isUnit_pow (E := E) hϖ e
  obtain ⟨N', hN'⟩ := GlobalTheory.T.exists_isometry_near_identity_close_tuples L ϖ hϖ Hm hH Λ hΛ m
    ((algebraMap F E ((ϖ : F) ^ e) * algebraMap F E ((ϖ : F) ^ e)) • Γ)
    (by rw [Matrix.det_smul]; exact ((hpe.mul hpe).pow _).mul hΓ) N
  have hi' : 1 ≤ N' + i := by omega
  obtain ⟨j, hj⟩ := GlobalTheory.T.congruentOneMatrices_transitive_near_hermitian L ϖ hϖ m Γ hh hΓ (N' + i) hi'
  obtain ⟨h1, hK', -⟩ := GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m (N' + i) hi'
  obtain ⟨h2, hK, -⟩ := GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i hi
  refine ⟨N' + (j + e), fun y u hy hG hu => ?_⟩
  have hint : ∀ v ∈ Λ, ∀ w ∈ Λ, hf L Hm v w ∈ L.O := fun v hv w hw => (hΛ.2 w).2 hw v hv
  let D : Matrix (Fin m) (Fin m) E := Matrix.of fun a b =>
    algebraMap F E ((ϖ : F) ^ N') * (hf L Hm (algebraMap F E ((ϖ : F) ^ e) • y b) (u a) +
      hf L Hm (u b) (algebraMap F E ((ϖ : F) ^ e) • y a)) +
      algebraMap F E ((ϖ : F) ^ (N' + N' + j + e + e)) * hf L Hm (u b) (u a)
  have hD : IsHerm L D := by
    ext a b
    simp only [cT, D, Matrix.of_apply, map_add, map_mul, AlgEquiv.commutes, ← GlobalTheory.HL.Model.hf_symm L hH.1]
    ring
  have hD' : IsIntM L D := fun a b =>
    L.O.add_mem (L.O.mul_mem (pow_mem L ϖ _) (L.O.add_mem (hint _ (hy b) _ (hu a))
      (hint _ (hu b) _ (hy a)))) (L.O.mul_mem (pow_mem L ϖ _) (hint _ (hu b) _ (hu a)))
  obtain ⟨A, hA, hA'⟩ := hj Γ ⟨1, h1, by rw [cT_one]; simp⟩ D hD hD'
  set y1 := y + algebraMap F E ((ϖ : F) ^ (N' + (j + e))) • u with hy1
  have hG1 : gramT L Hm y1 = cT L A * Γ * A := by
    rw [← hA', ← hG]
    ext a b
    simp only [gramT, hy1, D, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, GlobalTheory.HL.Model.hf_add_left, GlobalTheory.HL.Model.hf_add_right,
      GlobalTheory.HL.Model.hf_smul_left, GlobalTheory.HL.Model.hf_smul_right, AlgEquiv.commutes]
    simp only [map_pow]
    ring
  obtain ⟨-, hAu, -, hAi, -⟩ := hK' A hA
  have hG2 : gramT L Hm (rmul y1 A⁻¹) = Γ := by
    rw [GlobalTheory.HL.ContModel.gramT_rmul, hG1]
    calc _ = cT L (A * A⁻¹) * Γ * (A * A⁻¹) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = Γ := by rw [Matrix.mul_nonsing_inv _ hAu, cT_one]; simp
  obtain ⟨g, hg, hgc, hgy⟩ := hN' (algebraMap F E ((ϖ : F) ^ e) • y)
    (algebraMap F E ((ϖ : F) ^ e) • rmul y1 A⁻¹) hy (by rw [gramT_smul, hG])
    (by rw [gramT_smul, hG2]) (by
      intro a
      obtain ⟨w, hw, hw'⟩ := rmul_cong L (x := algebraMap F E ((ϖ : F) ^ e) • y) hy hAi a
      refine ⟨algebraMap F E ((ϖ : F) ^ i) • w +
        algebraMap F E ((ϖ : F) ^ (j + e + e)) • rmul u A⁻¹ a, Λ.add_mem
        (smul_mem L (pow_mem L ϖ _) hw)
        (smul_mem L (pow_mem L ϖ _) (rmul_mem L hu (hK' _ hAi).1 a)), ?_⟩
      rw [smul_add, ← pow_add_smul, ← hw', hy1, rmul_add, rmul_smul, rmul_smul]
      simp only [Pi.smul_apply, Pi.add_apply, smul_add, ← pow_add_smul]
      rw [show e + (N' + (j + e)) = N' + (j + e + e) by ring]
      abel)
  refine ⟨g, hg, hgc, A, (((hK 1 h2).2.2.2.2.2) (N' + i) (by omega) A hA).2, ?_⟩
  have h3 : (fun a => g (y a)) = rmul y1 A⁻¹ := by
    funext a
    have := hgy a
    simp only [Pi.smul_apply, map_smul] at this
    exact (hpe.smul_left_cancel).1 this
  rw [h3, rmul_rmul, Matrix.nonsing_inv_mul _ hAu, rmul_one]
end GlobalTheory.ThickOrbit
