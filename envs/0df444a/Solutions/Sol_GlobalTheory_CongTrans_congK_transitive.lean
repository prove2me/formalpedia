-- Prove2me | solution 1 for GlobalTheory.CongTrans.congK_transitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:30:43.933209+00:00
-- url     : https://prove2.me/submissions/bd7df97e-aea0-44f3-8121-ad8932fdab85

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitian
import Theorems.Thm_GlobalTheory_CongTrans_int_mul
import Theorems.Thm_GlobalTheory_CongTrans_int_cT
import Theorems.Thm_GlobalTheory_CongTrans_cT_add
import Theorems.Thm_GlobalTheory_CongTrans_cT_smul
import Theorems.Thm_GlobalTheory_CongTrans_cT_mul
import Theorems.Thm_GlobalTheory_CongTrans_cT_cT
import Theorems.Thm_GlobalTheory_CongTrans_cT_one
import Theorems.Thm_GlobalTheory_CongTrans_mem_congK_iff
import Theorems.Thm_GlobalTheory_CongTrans_exists_inv
import Theorems.Thm_GlobalTheory_CongTrans_exists_solution
import Theorems.Thm_GlobalTheory_CongTrans_exists_pow_mul_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
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
open GlobalTheory.CongTrans GlobalTheory.UnramOrder
namespace GlobalTheory.CongTrans
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsHerm L Γ → IsUnit Γ.det → ∀ i : ℕ, 1 ≤ i → ∃ j : ℕ, ∀ X ∈ horb L ϖ Γ i, ∀ D : Matrix (Fin m) (Fin m) E, IsHerm L D → IsIntM L D → ∃ A ∈ congK L ϖ m i, X + algebraMap F E ((ϖ : F) ^ j) • D = cT L A * X * A := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ m Γ hΓ hdet i hi
  have hp : algebraMap F E ϖ ∈ L.O := (algebraMap_mem_iff L _).2 ϖ.2
  have hcp : ∀ n : ℕ, L.cj (algebraMap F E ϖ ^ n) = algebraMap F E ϖ ^ n := fun n => by
    rw [map_pow, AlgEquiv.commutes]
  have hΓ' : cT L Γ = Γ := hΓ
  have hinv : Γ * Γ⁻¹ = 1 := Matrix.mul_nonsing_inv Γ hdet
  have hH : cT L Γ⁻¹ = Γ⁻¹ := by
    have h := congrArg (cT L) hinv
    rw [cT_mul, hΓ', cT_one] at h
    calc cT L Γ⁻¹ = cT L Γ⁻¹ * (Γ * Γ⁻¹) := by rw [hinv, Matrix.mul_one]
      _ = Γ⁻¹ := by rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  choose k hk using fun ab : Fin m × Fin m => exists_pow_mul_mem L hϖ (Γ⁻¹ ab.1 ab.2)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, IsIntM L (algebraMap F E ϖ ^ c • Γ⁻¹) := by
    refine ⟨Finset.univ.sup k, fun a b => ?_⟩
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := k) (Finset.mem_univ (a, b)))
    rw [hd, Matrix.smul_apply, smul_eq_mul, pow_add, mul_assoc]
    exact L.O.mul_mem (L.O.pow_mem hp _) (hk (a, b))
  refine ⟨i + c, ?_⟩
  rintro X ⟨A, hA, hX⟩ D hD hDi
  obtain ⟨B, hB, hAB⟩ := exists_inv L hϖ hi hA
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  have hBA' : cT L A * cT L B = 1 := by rw [← cT_mul, hBA, cT_one]
  obtain ⟨G, hG⟩ : ∃ G, G = B * (algebraMap F E ϖ ^ c • Γ⁻¹) * cT L B := ⟨_, rfl⟩
  have hGi : IsIntM L G := hG ▸ int_mul L (int_mul L hB hc) (int_cT L hB)
  have hGh : cT L G = G := by
    rw [hG, cT_mul, cT_mul, cT_cT, cT_smul, hcp, hH, Matrix.mul_assoc]
  have hXh : cT L X = X := by
    rw [hX, cT_mul, cT_mul, cT_cT, hΓ', Matrix.mul_assoc]
  have hXG : X * G = algebraMap F E ϖ ^ c • (1 : Matrix (Fin m) (Fin m) E) := by
    calc X * G = algebraMap F E ϖ ^ c • (cT L A * (Γ * (A * B) * Γ⁻¹) * cT L B) := by
          rw [hX, hG]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [hAB, Matrix.mul_one, hinv, Matrix.mul_one, hBA']
  have hGX : G * X = algebraMap F E ϖ ^ c • (1 : Matrix (Fin m) (Fin m) E) := by
    have h := congrArg (cT L) hXG
    rwa [cT_mul, hGh, hXh, cT_smul, hcp, cT_one] at h
  obtain ⟨Z, hZ, hZD⟩ := exists_solution L hϖ hi hGh hGi hD hDi
  refine ⟨1 + algebraMap F E ϖ ^ i • (G * Z),
    (mem_congK_iff L ϖ i _).2 ⟨_, int_mul L hGi hZ, rfl⟩, ?_⟩
  have e1 : X * (G * Z) = algebraMap F E ϖ ^ c • Z := by
    rw [← Matrix.mul_assoc, hXG, Matrix.smul_mul, Matrix.one_mul]
  have e2 : cT L Z * G * X = algebraMap F E ϖ ^ c • cT L Z := by
    rw [Matrix.mul_assoc, hGX, Matrix.mul_smul, Matrix.mul_one]
  rw [cT_add, cT_smul, hcp, cT_mul, hGh, cT_one, map_pow, ← hZD]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, e1, e2, ← Matrix.mul_assoc (cT L Z) G Z]
  module
end GlobalTheory.CongTrans
