-- Prove2me | solution 1 for GlobalTheory.HL.CloseTuples.exists_isometry_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:17.844518+00:00
-- url     : https://prove2.me/submissions/c1e00cf2-e6cc-450b-b3f2-3206035b4c86

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryNearIdentityCloseTuples
import Theorems.Thm_GlobalTheory_HL_CloseTuples_mem_jac
import Theorems.Thm_GlobalTheory_HL_CloseTuples_exists_pow_denom
import Theorems.Thm_GlobalTheory_HL_CloseTuples_one_add_onto
import Theorems.Thm_GlobalTheory_HL_CloseTuples_rk_mem
import Theorems.Thm_GlobalTheory_HL_CloseTuples_rk_adj
import Theorems.Thm_GlobalTheory_HL_CloseTuples_rk_dual
import Theorems.Thm_GlobalTheory_HL_CloseTuples_exists_skew
import Theorems.Thm_GlobalTheory_HL_CloseTuples_exists_cayley
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_DualInter_smul_l
import Theorems.Thm_GlobalTheory_HL_DualInter_smul_r
import Theorems.Thm_GlobalTheory_HL_DualInter_sub_l
import Theorems.Thm_GlobalTheory_HL_DualInter_sub_r
import Theorems.Thm_GlobalTheory_HL_DualInter_sum_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_add_r
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CloseTuples
open GlobalTheory.HL.Eichler GlobalTheory.HL.DualInter
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.HL.CloseTuples
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsUnit Γ.det → ∀ N : ℕ, ∃ N' : ℕ, ∀ x y : Fin m → Fin n → E, (∀ a, x a ∈ Λ) → gramT L Hm x = Γ → gramT L Hm y = Γ → (∀ a, ∃ w ∈ Λ, y a - x a = algebraMap F E ((ϖ : F) ^ N') • w) → ∃ g ∈ isomG L Hm, CongId L ϖ Λ N g ∧ ∀ a, g (x a) = y a := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm h Λ hΛ m Γ hΓ N
  set π : E := algebraMap F E ϖ with hπ
  have hπO : π ∈ L.O := (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 ϖ.2
  have hπc : L.cj π = π := L.cj.commutes _
  have hπu : IsUnit π :=
    (IsUnit.mk0 (ϖ : F) fun e => hϖ.ne_zero (Subtype.ext e)).map _
  have hπj := mem_jac L hϖ.not_isUnit ⟨π, hπO⟩ rfl
  set hf2 : E := algebraMap F E 2⁻¹ with hhf2
  have h2 : hf2 * 2 = 1 := by
    rw [hhf2, ← map_ofNat (algebraMap F E) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  choose k hk using fun ab : Fin m × Fin m => exists_pow_denom L hϖ (hf2 * Γ⁻¹ ab.1 ab.2)
  obtain ⟨c, hc⟩ : ∃ c, ∀ ab, k ab ≤ c := ⟨Finset.univ.sup k, fun ab => Finset.le_sup (Finset.mem_univ ab)⟩
  set q : E := π ^ c with hq
  have hqO : q ∈ L.O := L.O.pow_mem hπO c
  have hqc : L.cj q = q := by rw [hq, map_pow, hπc]
  have hqΓ : ∀ a b, q * (hf2 * Γ⁻¹ a b) ∈ L.O := fun a b => by
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le' (hc (a, b))
    rw [hq, hj, pow_add, mul_assoc]
    exact L.O.mul_mem (L.O.pow_mem hπO j) (hk (a, b))
  let p : L.O := ⟨π, hπO⟩ ^ (N + 1)
  have hpe : (p : E) = π ^ (N + 1) := rfl
  have hpj : p ∈ Ideal.jacobson (⊥ : Ideal L.O) := Ideal.pow_mem_of_mem _ hπj _ (Nat.succ_pos N)
  have hpc : L.cj p = p := by rw [hpe, map_pow, hπc]
  refine ⟨N + 1 + (c + c), fun x y hx gx gy hxy => ?_⟩
  choose d hd hxy using hxy
  have hxy' : ∀ a, y a = x a + ((p : E) * (q * q)) • d a := fun a => by
    rw [← sub_eq_iff_eq_add', hxy, map_pow, pow_add, pow_add _ c c]; rfl
  have hu : IsUnit ((p : E) * (q * q)) := (hπu.pow _).mul ((hπu.pow _).mul (hπu.pow _))
  have huc : L.cj ((p : E) * (q * q)) = p * (q * q) := by simp only [map_mul, hpc, hqc]
  have hy : ∀ a, y a ∈ Λ := fun a => by
    rw [hxy']
    exact Λ.add_mem (hx a) (Λ.smul_mem ⟨_, L.O.mul_mem p.2 (L.O.mul_mem hqO hqO)⟩ (hd a))
  have gx' : ∀ a b, hf L Hm (x b) (x a) = Γ a b := fun a b => congrFun (congrFun gx a) b
  have gy' : ∀ a b, hf L Hm (y b) (y a) = Γ a b := fun a b => congrFun (congrFun gy a) b
  have hsk : ∀ a b, hf L Hm (x a + y a) (d b) = - hf L Hm (d a) (x b + y b) := fun a b => by
    refine hu.mul_left_cancel ?_
    have e : ∀ a, ((p : E) * (q * q)) • d a = y a - x a := fun a => by rw [hxy' a]; abel
    rw [mul_neg, ← smul_l L Hm _ (d a), e]
    conv_lhs => rw [← huc, ← smul_r, e]
    simp only [hf_add_l, hf_add_r, sub_l, sub_r, gx', gy']
    ring
  let t0 : Fin m → Fin n → E := fun b => ∑ a, L.cj (q * (hf2 * Γ⁻¹ b a)) • x a
  have ht0 : ∀ b, t0 b ∈ Λ := fun b => Λ.sum_mem fun a _ =>
    Λ.smul_mem ⟨_, GlobalTheory.UnramOrder.cj_mem L (hqΓ b a)⟩ (hx a)
  have hxt : ∀ a b, hf L Hm (x a + x a) (t0 b) = if a = b then q else 0 := fun a b => by
    have e : ∑ j, Γ⁻¹ b j * Γ j a = if a = b then 1 else 0 := by
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hΓ, Matrix.one_apply]
      simp only [eq_comm]
    have e' : hf L Hm (x a) (t0 b) = q * hf2 * ∑ j, Γ⁻¹ b j * Γ j a := by
      simp only [t0, sum_r, smul_r, L.cj_cj, gx', Finset.mul_sum, mul_assoc]
    rw [hf_add_l, e', e]
    split_ifs
    · linear_combination q * h2
    · ring
  obtain ⟨-, o⟩ := one_add_onto hΛ.1 p hpj (q • rk L Hm d t0) fun v hv =>
    Λ.smul_mem ⟨q, hqO⟩ (rk_mem hΛ hd ht0 hv)
  choose t ht et using fun b => o _ (ht0 b)
  have hst : ∀ a b, hf L Hm (x a + y a) (t b) = if a = b then q else 0 := fun a b => by
    rw [← hxt, ← et b, hf_add_r, LinearMap.smul_apply, smul_r, smul_r, ← rk_adj h,
      rk_dual (s := fun a => x a + x a) hxt, hxy', ← add_assoc, hf_add_l _ _ (x a + x a), smul_l,
      smul_l, hpc, hqc]
    ring
  obtain ⟨Z, hZ, hZs, hZd⟩ := exists_skew h hΛ (s := fun a => x a + y a)
    (fun a => Λ.add_mem (hx a) (hy a)) ht hd hqO hqc hst hsk
  obtain ⟨g, hg, hgΛ, hgx⟩ := exists_cayley (Hm := Hm) hΛ.1 p hpj hpc Z hZ hZs
  refine ⟨g, hg, fun v hv => ?_, fun a => hgx _ _ ?_⟩
  · obtain ⟨w, hw, e⟩ := hgΛ v hv
    refine ⟨π • w, Λ.smul_mem ⟨π, hπO⟩ hw, ?_⟩
    rw [e, hpe, map_pow, smul_smul, pow_succ]
  · rw [hZd a, smul_smul, eq_sub_iff_add_eq', ← hxy']
end GlobalTheory.HL.CloseTuples
