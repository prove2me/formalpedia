-- Prove2me | solution 1 for GlobalTheory.CongGrp.horb_isCO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:46:40.375937+00:00
-- url     : https://prove2.me/submissions/be058324-c39c-463c-b5b8-f4761b02c979

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbit
import Theorems.Thm_GlobalTheory_CongGrp_finite_image_of_factor
import Theorems.Thm_GlobalTheory_CongGrp_intM_mul
import Theorems.Thm_GlobalTheory_CongGrp_intM_smul
import Theorems.Thm_GlobalTheory_CongGrp_cT_mul
import Theorems.Thm_GlobalTheory_CongGrp_cT_cT
import Theorems.Thm_GlobalTheory_CongGrp_mem_hermLat
import Theorems.Thm_P2M_GlobalTheory_CongGrp_pow_mem__de67754d33b0
import Theorems.Thm_GlobalTheory_CongGrp_exists_pow_mul_mem
import Theorems.Thm_GlobalTheory_CongGrp_congK_int
import Theorems.Thm_GlobalTheory_CongGrp_congK_mul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_CongTrans_cT_cT
import Theorems.Thm_GlobalTheory_CongTrans_cT_mul
import Theorems.Thm_GlobalTheory_CongTrans_exists_pow_mul_mem
import Theorems.Thm_GlobalTheory_T_congruentOneMatrices_transitive_near_hermitian
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
open GlobalTheory GlobalTheory.CongGrp
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.CongGrp
theorem _root_.solution (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {m i : ℕ} (hi : 1 ≤ i)
    (Γ : Matrix (Fin m) (Fin m) E) (hΓ : IsHerm L Γ) (hdet : IsUnit Γ.det) :
    IsCO (hermLat L m) (horb L ϖ Γ i) := by
  obtain ⟨j, hj⟩ := GlobalTheory.T.congruentOneMatrices_transitive_near_hermitian L ϖ hϖ m Γ hΓ hdet i hi
  obtain ⟨-, hcj, -, -, -, hcard, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hpu : ∀ n : ℕ, IsUnit (algebraMap F E ((ϖ : F) ^ n)) := fun n =>
    (IsUnit.mk0 _ (pow_ne_zero n hϖ0)).map _
  let A : AddSubgroup (Matrix (Fin m) (Fin m) E) :=
    (hermLat L m).map (DistribMulAction.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ j)))
  have hA : ∀ X, X ∈ A ↔ ∃ D, (IsHerm L D ∧ IsIntM L D) ∧ algebraMap F E ((ϖ : F) ^ j) • D = X := by
    intro X
    simp only [A, AddSubgroup.mem_map, mem_hermLat]
    rfl
  have hfin : ∀ (c : ℕ) (S : Set (Matrix (Fin m) (Fin m) E)),
      (∀ X ∈ S, IsHerm L X ∧ IsIntM L (algebraMap F E ((ϖ : F) ^ c) • X)) →
      ((QuotientAddGroup.mk : _ → _ ⧸ A) '' S).Finite := by
    intro c S hS
    let I : Ideal L.O := Ideal.span {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ (c + j))}
    haveI : Finite (L.O ⧸ I) := by
      apply Nat.finite_of_card_ne_zero
      rw [hcard]
      exact pow_ne_zero _ (by omega)
    refine finite_image_of_factor S (fun X => fun a b : Fin m =>
      if h : algebraMap F E ((ϖ : F) ^ c) * X a b ∈ L.O then Ideal.Quotient.mk I ⟨_, h⟩ else 0) _ ?_
    intro X hX Y hY hXY
    have key : ∀ a b, ∃ d ∈ L.O, Y a b - X a b = algebraMap F E ((ϖ : F) ^ j) * d := by
      intro a b
      have h := congrFun (congrFun hXY a) b
      have h1 : algebraMap F E ((ϖ : F) ^ c) * X a b ∈ L.O := (hS X hX).2 a b
      have h2 : algebraMap F E ((ϖ : F) ^ c) * Y a b ∈ L.O := (hS Y hY).2 a b
      simp only [dif_pos h1, dif_pos h2] at h
      have h3 := Ideal.Quotient.eq.1 h.symm
      have hI : I = Ideal.span {(⟨_, pow_mem' L ϖ (c + j)⟩ : L.O)} := by
        simp only [I]
        congr 1
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Subtype.ext_iff]
      rw [hI, Ideal.mem_span_singleton'] at h3
      obtain ⟨d, hd⟩ := h3
      refine ⟨d, d.2, (hpu c).mul_left_cancel ?_⟩
      have h4 : (d : E) * algebraMap F E ((ϖ : F) ^ (c + j)) =
        algebraMap F E ((ϖ : F) ^ c) * Y a b - algebraMap F E ((ϖ : F) ^ c) * X a b :=
        congrArg Subtype.val hd
      rw [pow_add, map_mul] at h4
      linear_combination -h4
    choose D hD hDe using key
    rw [QuotientAddGroup.eq, hA]
    refine ⟨Matrix.of D, ⟨?_, hD⟩, ?_⟩
    · ext a b
      apply (hpu j).mul_left_cancel
      have h1 := congrFun (congrFun (hS X hX).1 a) b
      have h2 := congrFun (congrFun (hS Y hY).1 a) b
      have h3 := congrArg L.cj (hDe b a)
      simp only [cT, map_sub, map_mul, AlgEquiv.commutes] at h1 h2 h3
      simp only [cT, Matrix.of_apply]
      rw [← h3, h1, h2, hDe]
    · ext a b
      simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Matrix.add_apply,
        Matrix.neg_apply]
      linear_combination -hDe a b
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · have h := AddSubgroup.relIndex_ker (hermLat L m) (QuotientAddGroup.mk' A)
    rw [QuotientAddGroup.ker_mk'] at h
    rw [h]
    have : Finite ((hermLat L m).map (QuotientAddGroup.mk' A)) :=
      hfin 0 (hermLat L m) fun X hX => by simpa using (mem_hermLat L).1 hX
    exact Nat.card_pos.ne'
  · have : A ≤ hermLat L m := by
      intro X hX
      obtain ⟨D, hD, rfl⟩ := (hA X).1 hX
      refine (mem_hermLat L).2 ⟨?_, intM_smul L (pow_mem' L ϖ j) hD.2⟩
      ext a b
      have h1 := congrFun (congrFun hD.1 a) b
      simp only [cT] at h1
      simp only [cT, Matrix.smul_apply, smul_eq_mul, map_mul, AlgEquiv.commutes, h1]
    rw [AddSubgroup.relIndex_eq_one.2 this]
    exact one_ne_zero
  · intro X hX a ha
    obtain ⟨D, hD, rfl⟩ := (hA a).1 ha
    obtain ⟨B, hB, hXB⟩ := hj X hX D hD.1 hD.2
    obtain ⟨C, hC, rfl⟩ := hX
    refine ⟨C * B, congK_mul L ϖ hC hB, ?_⟩
    rw [hXB, cT_mul]
    simp only [Matrix.mul_assoc]
  · choose n hn using fun a b => exists_pow_mul_mem L ϖ hϖ (Γ a b)
    let c : ℕ := Finset.univ.sup fun ab : Fin m × Fin m => n ab.1 ab.2
    have hc : IsIntM L (algebraMap F E ((ϖ : F) ^ c) • Γ) := by
      intro a b
      have hle : n a b ≤ c :=
        Finset.le_sup (f := fun ab : Fin m × Fin m => n ab.1 ab.2) (Finset.mem_univ (a, b))
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hle
      rw [hk, pow_add, map_mul, Matrix.smul_apply, smul_eq_mul, mul_assoc]
      exact mul_mem (pow_mem' L ϖ k) (hn a b)
    refine hfin c _ ?_
    rintro _ ⟨C, hC, rfl⟩
    have hCi := congK_int L ϖ hC
    constructor
    · unfold IsHerm at hΓ ⊢
      rw [cT_mul, cT_mul, cT_cT, hΓ, Matrix.mul_assoc]
    · rw [← Matrix.smul_mul, ← Matrix.mul_smul]
      exact intM_mul L (intM_mul L (fun a b => (hcj _ (hCi b a)).1) hc) hCi
end GlobalTheory.CongGrp
