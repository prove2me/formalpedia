-- Prove2me | solution 1 for GlobalTheory.HL.Glue.exists_nat_between
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:32.622106+00:00
-- url     : https://prove2.me/submissions/f9d9f1ca-75ba-4b39-a314-48047d85d2c3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalLatticeBetweenScaledStandardLattices
import Theorems.Thm_P2M_GlobalTheory_HL_Glue_smul_mem_of_mem__8d07f3110088
import Theorems.Thm_GlobalTheory_HL_Glue_exists_nat_smul_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_NatSmulMem_exists_nat_smul_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Glue
variable {R : Type} [CommRing R] {O : Subring R} {n : ℕ}
namespace GlobalTheory.HL.Glue
theorem _root_.solution (Λ : Submodule O (Fin n → R)) (hfg : Λ.FG)
    (hsp : Submodule.span R (Λ : Set (Fin n → R)) = ⊤)
    (hd : ∀ y : R, ∃ m : ℕ, m ≠ 0 ∧ (m : R) * y ∈ O) :
    ∃ m : ℕ, m ≠ 0 ∧ (∀ v : Fin n → R, (∀ i, v i ∈ O) → (m : R) • v ∈ Λ) ∧
      ∀ v ∈ Λ, ∀ i, (m : R) * v i ∈ O := by
  choose md hmd0 hmd using hd
  obtain ⟨S, hS⟩ := hfg

  set m1 : ℕ := ∏ s ∈ S, ∏ i, md (s i) with hm1
  have hm10 : m1 ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => Finset.prod_ne_zero_iff.2 fun i _ => hmd0 _
  have hup : ∀ v ∈ Λ, ∀ i, (m1 : R) * v i ∈ O := by
    intro v hv
    rw [← hS] at hv
    induction hv using Submodule.span_induction with
    | mem s hs =>
      intro i
      have hdvd : md (s i) ∣ m1 :=
        (Finset.dvd_prod_of_mem (fun j => md (s j)) (Finset.mem_univ i)).trans
          (Finset.dvd_prod_of_mem (fun t : Fin n → R => ∏ j, md (t j)) hs)
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, Nat.cast_mul, mul_comm (md (s i) : R), mul_assoc]
      exact O.mul_mem (natCast_mem O k) (hmd _)
    | zero => intro i; simp
    | add x y _ _ hx hy => intro i; simpa [mul_add] using O.add_mem (hx i) (hy i)
    | smul a x _ hx =>
      intro i
      have : (m1 : R) * (a • x) i = (a : R) * ((m1 : R) * x i) := by
        simp [Subring.smul_def]; ring
      rw [this]
      exact O.mul_mem a.2 (hx i)

  have hsingle : ∀ i : Fin n, ∃ m : ℕ, m ≠ 0 ∧ (m : R) • (Pi.single i 1 : Fin n → R) ∈ Λ := fun i =>
    exists_nat_smul_mem Λ (fun y => ⟨md y, hmd0 y, hmd y⟩) (by rw [hsp]; exact Submodule.mem_top)
  choose ms hms0 hms using hsingle
  set m2 : ℕ := ∏ i, ms i with hm2
  have hm20 : m2 ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hms0 i
  have hsing2 : ∀ i, (m2 : R) • (Pi.single i 1 : Fin n → R) ∈ Λ := by
    intro i
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem ms (Finset.mem_univ i)
    rw [← hm2] at hk
    rw [hk, Nat.cast_mul, mul_comm, ← smul_smul]
    exact smul_mem_of_mem' Λ (natCast_mem O k) (hms i)
  have hlow : ∀ v : Fin n → R, (∀ i, v i ∈ O) → (m2 : R) • v ∈ Λ := by
    intro v hv
    have h : (m2 : R) • v = ∑ i, v i • ((m2 : R) • (Pi.single i 1 : Fin n → R)) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, mul_comm]
    rw [h]
    exact Λ.sum_mem fun i _ => smul_mem_of_mem' Λ (hv i) (hsing2 i)
  refine ⟨m1 * m2, mul_ne_zero hm10 hm20, fun v hv => ?_, fun v hv i => ?_⟩
  · have : ((m1 * m2 : ℕ) : R) • v = (m1 : R) • ((m2 : R) • v) := by push_cast; rw [smul_smul]
    rw [this]
    exact smul_mem_of_mem' Λ (natCast_mem O m1) (hlow v hv)
  · have : ((m1 * m2 : ℕ) : R) * v i = (m2 : R) * ((m1 : R) * v i) := by push_cast; ring
    rw [this]
    exact O.mul_mem (natCast_mem O m2) (hup v hv i)
end GlobalTheory.HL.Glue
