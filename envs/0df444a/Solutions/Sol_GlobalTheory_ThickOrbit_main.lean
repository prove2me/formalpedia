-- Prove2me | solution 1 for GlobalTheory.ThickOrbit.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:36:55.437603+00:00
-- url     : https://prove2.me/submissions/38e7027c-0764-4a9d-8c92-b53b83e3bc09

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
import Theorems.Thm_GlobalTheory_ThickOrbit_relIndex_ne_zero_of_finite
import Theorems.Thm_GlobalTheory_ThickOrbit_pow_mem
import Theorems.Thm_GlobalTheory_ThickOrbit_smul_mem
import Theorems.Thm_GlobalTheory_ThickOrbit_exists_pow_le
import Theorems.Thm_GlobalTheory_ThickOrbit_finite_image
import Theorems.Thm_GlobalTheory_ThickOrbit_rmul_rmul
import Theorems.Thm_GlobalTheory_ThickOrbit_rmul_one
import Theorems.Thm_GlobalTheory_ThickOrbit_rmul_add
import Theorems.Thm_GlobalTheory_ThickOrbit_rmul_smul
import Theorems.Thm_GlobalTheory_ThickOrbit_rmul_mem
import Theorems.Thm_GlobalTheory_ThickOrbit_exists_close
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Model_hf_symm
import Theorems.Thm_GlobalTheory_T_exists_isometry_tupleMatrixRightMul_near_identity
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
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsUnit Γ.det → ∀ N e : ℕ, ∃ i0 : ℕ, 1 ≤ i0 ∧ ∀ i ≥ i0, ∀ K : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), K ≤ isomG L Hm ⊓ stabL L Λ → (∀ g ∈ isomG L Hm, CongId L ϖ Λ N g → g ∈ K) → ∀ x : Fin m → Fin n → E, (∀ a, algebraMap F E ((ϖ : F) ^ e) • x a ∈ Λ) → gramT L Hm x = Γ → IsCO (tupLat L Λs m) (thick L ϖ (torb K x) i) ∧ (∀ y ∈ torb K x, ∀ A ∈ congK L ϖ m i, cT L A * Γ * A = Γ → rmul y A ∈ torb K x) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hΛs Λ hΛ m Γ hΓ N e
  obtain ⟨i1, hi1⟩ := GlobalTheory.T.exists_isometry_tupleMatrixRightMul_near_identity L ϖ hϖ Hm hH Λ hΛ m Γ hΓ N e
  refine ⟨i1 + 1, by omega, fun i hi K hK hKN x hx hG => ?_⟩
  have horb : ∀ y ∈ torb K x, (∀ a, algebraMap F E ((ϖ : F) ^ e) • y a ∈ Λ) ∧ gramT L Hm y = Γ ∧
      ∀ g ∈ K, (fun a => g (y a)) ∈ torb K x := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨fun a => ?_, ?_, fun g' hg' => ⟨g' * g, K.mul_mem hg' hg, rfl⟩⟩
    · have h : g • Λ = Λ := (hK hg).2
      rw [← map_smul, ← h]
      exact ⟨_, hx a, rfl⟩
    · rw [← hG]
      ext a b
      exact (hK hg).1 _ _
  refine ⟨?_, fun y hy A hA hA' => ?_⟩
  swap
  · obtain ⟨h1, h2, h3⟩ := horb y hy
    obtain ⟨g, hg, hgc, hgy⟩ := hi1 i (by omega) y h1 h2 A hA hA'
    rw [← funext hgy]
    exact h3 g (hKN g hg hgc)
  have hh : IsHerm L Γ := by
    rw [← hG]
    ext a b
    exact (GlobalTheory.HL.Model.hf_symm L hH.1 _ _).symm
  obtain ⟨M, hM⟩ := exists_close L hϖ hH hΛ hh hΓ N e i (by omega)
  obtain ⟨-, hC, -⟩ := GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i (by omega)
  let B : AddSubgroup (Fin m → Fin n → E) :=
    (tupLat L Λ m).map (DistribMulAction.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ M)))
  have hB : ∀ w : Fin m → Fin n → E, (∀ a, w a ∈ Λ) → algebraMap F E ((ϖ : F) ^ M) • w ∈ B :=
    fun w hw => ⟨w, fun a _ => hw a, rfl⟩
  obtain ⟨k, hk⟩ := exists_pow_le L hϖ hΛ.1 hΛs.1
  obtain ⟨l, hl⟩ := exists_pow_le L hϖ hΛs.1 hΛ.1
  refine ⟨B, relIndex_ne_zero_of_finite _ _ (finite_image L hϖ hΛ.1 M k B hB _
      fun z hz a => hk _ (hz a trivial)),
    relIndex_ne_zero_of_finite _ _ (finite_image L hϖ hΛs.1 0 l _
      (fun w hw a _ => by simpa using hw a) _ ?_), ?_, finite_image L hϖ hΛ.1 M e B hB _ ?_⟩
  · rintro _ ⟨w, hw, rfl⟩ a
    exact hl _ (smul_mem L (pow_mem L ϖ M) (hw a trivial))
  · rintro _ ⟨y, hy, A, hA, rfl⟩ _ ⟨v, hv, rfl⟩
    obtain ⟨h1, h2, h3⟩ := horb y hy
    obtain ⟨-, hAu, -, hAi, -⟩ := hC A hA
    obtain ⟨g, hg, hgc, A', hA', h⟩ := hM y (rmul v A⁻¹) h1 h2
      (rmul_mem L (fun a => hv a trivial) (hC _ hAi).1)
    refine ⟨_, h3 g (hKN g hg hgc), A' * A, (hC _ hA').2.2.2.2.1 A hA, ?_⟩
    rw [← rmul_rmul, ← h, rmul_add, rmul_smul, rmul_rmul, Matrix.nonsing_inv_mul _ hAu, rmul_one]
    rfl
  · rintro _ ⟨y, hy, A, hA, rfl⟩ a
    have := rmul_mem L (x := algebraMap F E ((ϖ : F) ^ e) • y) (horb y hy).1 (hC A hA).1 a
    rwa [rmul_smul] at this
end GlobalTheory.ThickOrbit
