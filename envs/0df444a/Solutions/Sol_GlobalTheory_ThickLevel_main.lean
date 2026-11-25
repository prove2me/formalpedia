-- Prove2me | solution 1 for GlobalTheory.ThickLevel.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:01:44.154914+00:00
-- url     : https://prove2.me/submissions/acd7e8f8-cdc7-4e75-aa63-b4404d01fc7b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentBiUnionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMatrixCongruenceContentJacobianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalisedContentThickenedSetIndependentOfLevel
import Theorems.Thm_GlobalTheory_ThickLevel_finite_pieces
import Theorems.Thm_GlobalTheory_ThickLevel_cT_mul
import Theorems.Thm_GlobalTheory_ThickLevel_rmul_rmul
import Theorems.Thm_GlobalTheory_ThickLevel_gramT_rmul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_CongGrp_cT_mul
import Theorems.Thm_GlobalTheory_CongTrans_cT_mul
import Theorems.Thm_GlobalTheory_HL_ContModel_gramT_rmul
import Theorems.Thm_GlobalTheory_HL_HermJacobian_cT_mul
import Theorems.Thm_GlobalTheory_T_commensurableCosetUnionContent_biUnion
import Theorems.Thm_GlobalTheory_T_hermitianMatrix_congruence_content_jacobian
import Theorems.Thm_GlobalTheory_T_matrixCongruentOneModUniformizerPow_group_and_orbits
import Theorems.Thm_GlobalTheory_T_tuple_jacobian_rightMul_isometry
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
open GlobalTheory GlobalTheory.ThickLevel
namespace GlobalTheory.ThickLevel
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsHerm L Γ → IsUnit Γ.det → ∀ (Ω : Set (Fin m → Fin n → E)), (∀ y ∈ Ω, gramT L Hm y = Γ) → ∀ i i' : ℕ, 1 ≤ i → i ≤ i' → (∀ y ∈ Ω, ∀ A ∈ congK L ϖ m i, cT L A * Γ * A = Γ → rmul y A ∈ Ω) → IsCO (tupLat L Λs m) (thick L ϖ Ω i') → cont (tupLat L Λs m) (thick L ϖ Ω i) * cont (hermLat L m) (horb L ϖ Γ i') = cont (tupLat L Λs m) (thick L ϖ Ω i') * cont (hermLat L m) (horb L ϖ Γ i) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λ hΛ m Γ hΓ hΓu Ω hΩ i i' hi hii hst hco
  obtain ⟨h1, hK, hO⟩ := GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i hi
  obtain ⟨h1', hK', hO'⟩ := GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i' (hi.trans hii)
  obtain ⟨hOco, -⟩ := hO Γ hΓ hΓu
  obtain ⟨hOco', hpos⟩ := hO' Γ hΓ hΓu
  have hsub : ∀ B ∈ congK L ϖ m i', B ∈ congK L ϖ m i := fun B hB =>
    ((hK 1 h1).2.2.2.2.2 i' hii B hB).2
  have hu : ∀ A ∈ congK L ϖ m i, IsUnit A.det := fun A hA => (hK A hA).2.1
  have hmul : ∀ A ∈ congK L ϖ m i, ∀ B ∈ congK L ϖ m i, A * B ∈ congK L ϖ m i :=
    fun A hA => (hK A hA).2.2.2.2.1
  have hmul' : ∀ A ∈ congK L ϖ m i', ∀ B ∈ congK L ϖ m i', A * B ∈ congK L ϖ m i' :=
    fun A hA => (hK' A hA).2.2.2.2.1
  have hinv : ∀ A ∈ congK L ϖ m i, A⁻¹ ∈ congK L ϖ m i := fun A hA => (hK A hA).2.2.2.1
  have hinv' : ∀ A ∈ congK L ϖ m i', A⁻¹ ∈ congK L ϖ m i' := fun A hA => (hK' A hA).2.2.2.1
  have hnorm : ∀ A ∈ congK L ϖ m i, ∀ B ∈ congK L ϖ m i', A⁻¹ * B * A ∈ congK L ϖ m i' :=
    fun A hA B hB => ((hK A hA).2.2.2.2.2 i' hii B hB).1

  let act : Matrix (Fin m) (Fin m) E → Matrix (Fin m) (Fin m) E → Matrix (Fin m) (Fin m) E :=
    fun A X => cT L A * X * A
  have act_mul : ∀ A B X, act B (act A X) = act (A * B) X := by
    intro A B X
    simp only [act, cT_mul, Matrix.mul_assoc]
  let P : Matrix (Fin m) (Fin m) E → Set (Matrix (Fin m) (Fin m) E) :=
    fun a => act a '' horb L ϖ Γ i'
  have memP : ∀ a X, X ∈ P a ↔ ∃ B ∈ congK L ϖ m i', X = act (B * a) Γ := by
    intro a X
    constructor
    · rintro ⟨_, ⟨B, hB, rfl⟩, rfl⟩
      exact ⟨B, hB, act_mul B a Γ⟩
    · rintro ⟨B, hB, rfl⟩
      exact ⟨_, ⟨B, hB, rfl⟩, act_mul B a Γ⟩
  have hPle : ∀ a ∈ congK L ϖ m i, ∀ b ∈ congK L ϖ m i, ∀ X ∈ P a, X ∈ P b → P a ⊆ P b := by
    intro a ha b hb X hXa hXb Y hY
    obtain ⟨B, hB, hXB⟩ := (memP _ _).1 hXa
    obtain ⟨C, hC, hXC⟩ := (memP _ _).1 hXb
    obtain ⟨D, hD, rfl⟩ := (memP _ _).1 hY
    have hk : a⁻¹ * (B⁻¹ * D) * a ∈ congK L ϖ m i' := hnorm a ha _ (hmul' _ (hinv' B hB) D hD)
    set k := a⁻¹ * (B⁻¹ * D) * a with hkdef
    have hk2 := hnorm _ (hinv b hb) k hk
    rw [Matrix.nonsing_inv_nonsing_inv b (hu b hb)] at hk2
    refine (memP _ _).2 ⟨C * (b * k * b⁻¹), hmul' _ hC _ hk2, ?_⟩
    have e1 : D * a = B * a * k := by
      rw [hkdef]
      simp only [Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left a _ (hu a ha),
        Matrix.mul_nonsing_inv_cancel_left B _ (hu B (hsub B hB))]
    have e2 : C * (b * k * b⁻¹) * b = C * b * k := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul b (hu b hb), Matrix.mul_one]
    rw [e1, e2, ← act_mul (B * a), ← act_mul (C * b), ← hXB, ← hXC]
  let S : Set (Set (Matrix (Fin m) (Fin m) E)) := P '' congK L ϖ m i
  have hdisj : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint p q := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne
    rw [Set.disjoint_left]
    intro X hXa hXb
    exact hne (Set.Subset.antisymm (hPle a ha b hb X hXa hXb) (hPle b hb a ha X hXb hXa))
  have hS : ∀ p ∈ S, IsCO (hermLat L m) p ∧ cont (hermLat L m) p = cont (hermLat L m) (horb L ϖ Γ i') ∧
      p ⊆ horb L ϖ Γ i := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨j1, j2⟩ := (GlobalTheory.T.hermitianMatrix_congruence_content_jacobian L ϖ hϖ m a (hu a ha)).2 _ hOco'
    rw [(hK a ha).2.2.1] at j2
    refine ⟨j1, by simpa using j2, fun X hX => ?_⟩
    obtain ⟨B, hB, rfl⟩ := (memP _ _).1 hX
    exact ⟨B * a, hmul _ (hsub B hB) a ha, rfl⟩
  have hfin : S.Finite := finite_pieces _ hOco S _ hpos hS hdisj
  have hself : ∀ a, act a Γ ∈ P a := fun a => (memP _ _).2 ⟨1, h1', by rw [Matrix.one_mul]⟩
  have hU1 : (⋃ p ∈ hfin.toFinset, p) = horb L ϖ Γ i := by
    apply Set.Subset.antisymm
    · exact Set.iUnion₂_subset fun p hp => (hS p (hfin.mem_toFinset.1 hp)).2.2
    · rintro _ ⟨A, hA, rfl⟩
      exact Set.mem_iUnion₂.2 ⟨P A, hfin.mem_toFinset.2 ⟨A, hA, rfl⟩, hself A⟩
  have hc1 := (GlobalTheory.T.commensurableCosetUnionContent_biUnion (hermLat L m) hfin.toFinset (fun p => p)
    (fun p hp => (hS p (hfin.mem_toFinset.1 hp)).1)).2
    (fun p hp q hq => hdisj p (hfin.mem_toFinset.1 hp) q (hfin.mem_toFinset.1 hq))
  rw [hU1, Finset.sum_congr rfl (fun p hp => (hS p (hfin.mem_toFinset.1 hp)).2.1), Finset.sum_const,
    nsmul_eq_mul] at hc1

  have hrep : ∀ p : Set (Matrix (Fin m) (Fin m) E), ∃ a, p ∈ S → a ∈ congK L ϖ m i ∧ P a = p := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨a, ha, h⟩ := hp
      exact ⟨a, fun _ => ⟨ha, h⟩⟩
    · exact ⟨1, fun h => absurd h hp⟩
  choose r hr using hrep
  let T : Set (Matrix (Fin m) (Fin m) E) → Set (Fin m → Fin n → E) :=
    fun p => (fun x => rmul x (r p)) '' thick L ϖ Ω i'
  have hT : ∀ p ∈ S, IsCO (tupLat L Λ m) (T p) ∧
      cont (tupLat L Λ m) (T p) = cont (tupLat L Λ m) (thick L ϖ Ω i') := by
    intro p hp
    have ha := (hr p hp).1
    obtain ⟨j1, j2⟩ := (GlobalTheory.T.tuple_jacobian_rightMul_isometry L ϖ hϖ Hm hH Λ hΛ m).1 _ (hu _ ha) _ hco
    rw [(hK _ ha).2.2.1] at j2
    exact ⟨j1, by simpa using j2⟩
  have hgram : ∀ p ∈ S, ∀ x ∈ T p, gramT L Hm x ∈ p := by
    rintro p hp _ ⟨_, ⟨y, hy, B, hB, rfl⟩, rfl⟩
    have : act (B * r p) Γ ∈ P (r p) := (memP _ _).2 ⟨B, hB, rfl⟩
    rw [(hr p hp).2] at this
    simp only [rmul_rmul, gramT_rmul, hΩ y hy]
    exact this
  have hU2 : (⋃ p ∈ hfin.toFinset, T p) = thick L ϖ Ω i := by
    apply Set.Subset.antisymm
    · refine Set.iUnion₂_subset fun p hp => ?_
      rintro _ ⟨_, ⟨y, hy, B, hB, rfl⟩, rfl⟩
      exact ⟨y, hy, B * r p, hmul _ (hsub B hB) _ (hr p (hfin.mem_toFinset.1 hp)).1, rmul_rmul _ _ _⟩
    · rintro _ ⟨y, hy, A, hA, rfl⟩
      have hp : P A ∈ S := ⟨A, hA, rfl⟩
      refine Set.mem_iUnion₂.2 ⟨P A, hfin.mem_toFinset.2 hp, ?_⟩
      obtain ⟨ha, hPa⟩ := hr _ hp
      have h3 := hself A
      rw [← hPa] at h3
      obtain ⟨B, hB, h4⟩ := (memP _ _).1 h3
      have hBa := hmul _ (hsub B hB) _ ha
      have h5 : act (A * (B * r (P A))⁻¹) Γ = Γ := by
        rw [← act_mul, h4, act_mul, Matrix.mul_nonsing_inv _ (hu _ hBa)]
        have : cT L (1 : Matrix (Fin m) (Fin m) E) = 1 := by
          ext a b
          simp only [cT, Matrix.one_apply, eq_comm]
          split_ifs <;> simp
        simp only [act, this, Matrix.one_mul, Matrix.mul_one]
      refine ⟨_, ⟨_, hst y hy _ (hmul _ hA _ (hinv _ hBa)) h5, B, hB, rfl⟩, ?_⟩
      simp only [rmul_rmul]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hu _ hBa), Matrix.mul_one]
  have hc2 := (GlobalTheory.T.commensurableCosetUnionContent_biUnion (tupLat L Λ m) hfin.toFinset T
    (fun p hp => (hT p (hfin.mem_toFinset.1 hp)).1)).2
    (fun p hp q hq hne => by
      have hp' := hfin.mem_toFinset.1 hp
      have hq' := hfin.mem_toFinset.1 hq
      rw [Set.disjoint_left]
      intro x hxp hxq
      exact Set.disjoint_left.1 (hdisj p hp' q hq' hne) (hgram p hp' x hxp) (hgram q hq' x hxq))
  rw [hU2, Finset.sum_congr rfl (fun p hp => (hT p (hfin.mem_toFinset.1 hp)).2), Finset.sum_const,
    nsmul_eq_mul] at hc2
  rw [hc1, hc2]
  ring
end GlobalTheory.ThickLevel
