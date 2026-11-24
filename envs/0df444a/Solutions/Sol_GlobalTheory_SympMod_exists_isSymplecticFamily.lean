-- Prove2me | solution 1 for GlobalTheory.SympMod.exists_isSymplecticFamily
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:16:56.238531+00:00
-- url     : https://prove2.me/submissions/44b18550-a645-44d6-b742-b93f921b596d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsStdSympZmod
import Theorems.Thm_GlobalTheory_SympMod_card_torsion_zmod
import Theorems.Thm_GlobalTheory_SympMod_exists_pair_eq_one
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_right
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.SympMod
namespace GlobalTheory.SympMod
theorem _root_.solution {M : ℕ} [NeZero M] {V : Type*} [AddCommGroup V] [Module (ZMod M) V]
    {B : LinearMap.BilinForm (ZMod M) V} (hB : B.IsAlt) (g : ℕ) (N : Submodule (ZMod M) V)
    (hN : ∀ x ∈ N, (∀ y ∈ N, B x y = 0) → x = 0)
    (hc : ∀ d, d ∣ M → Nat.card {x : V // x ∈ N ∧ d • x = 0} = d ^ (2 * g)) :
    ∃ e f : Fin g → V, IsSymplecticFamily B e f (fun _ => 1) ∧ (∀ i, e i ∈ N) ∧ ∀ i, f i ∈ N := by
  induction g generalizing N with
  | zero =>
    exact ⟨Fin.elim0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, fun i => i.elim0⟩
  | succ g ih =>
  obtain ⟨e, he, f, hf, hd⟩ := exists_pair_eq_one N hN hc
  have hd' : B f e = -1 := by rw [← hB.neg_eq, hd]
  let N' : Submodule (ZMod M) V := N ⊓ (LinearMap.ker (B e) ⊓ LinearMap.ker (B f))
  have hmem : ∀ y, y ∈ N' ↔ y ∈ N ∧ B e y = 0 ∧ B f y = 0 := fun y => Iff.rfl
  have hpr : ∀ y ∈ N, y - B y f • e - B e y • f ∈ N' := fun y hy =>
    (hmem _).2 ⟨N.sub_mem (N.sub_mem hy (N.smul_mem _ he)) (N.smul_mem _ hf),
      by simp [hd, hB.self_eq_zero], by simp [← hB.neg_eq y f, hd', hB.self_eq_zero]⟩
  have hdec : ∀ y ∈ N, ∃ a b : ZMod M, ∃ y' ∈ N', y = a • e + b • f + y' := fun y hy =>
    ⟨B y f, B e y, _, hpr y hy, by abel⟩
  obtain ⟨e', f', hs, he', hf'⟩ := ih N' (by
    intro x hx hx0
    refine hN x hx.1 fun y hy => ?_
    obtain ⟨a, b, y', hy', rfl⟩ := hdec y hy
    simp [hx0 y' hy', hB.eq_iff.1 ((hmem x).1 hx).2.1, hB.eq_iff.1 ((hmem x).1 hx).2.2]) (by
    intro d hdM
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdM (NeZero.pos M)
    let F : {a : ZMod M // d • a = 0} × {a : ZMod M // d • a = 0} × {x : V // x ∈ N' ∧ d • x = 0} →
        {x : V // x ∈ N ∧ d • x = 0} := fun t =>
      ⟨t.1.1 • e + t.2.1.1 • f + t.2.2.1,
        N.add_mem (N.add_mem (N.smul_mem _ he) (N.smul_mem _ hf)) t.2.2.2.1.1, by
          rw [smul_add, smul_add, ← smul_assoc, ← smul_assoc, t.1.2, t.2.1.2, t.2.2.2.2]
          simp⟩
    have hF : Function.Bijective F := by
      constructor
      · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨y, hy, hy'⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩, ⟨z, hz, hz'⟩⟩ h
        have h : a • e + b • f + y = a' • e + b' • f + z := congrArg Subtype.val h
        obtain rfl : b = b' := by
          simpa [hd, hB.self_eq_zero, ((hmem _).1 hy).2.1, ((hmem _).1 hz).2.1] using congrArg (B e) h
        obtain rfl : a = a' := by
          simpa [hd', hB.self_eq_zero, ((hmem _).1 hy).2.2, ((hmem _).1 hz).2.2] using congrArg (B f) h
        obtain rfl : y = z := add_left_cancel h
        rfl
      · rintro ⟨x, hx, hx'⟩
        have k₁ : d • B x f = 0 := by rw [← LinearMap.smul_apply, ← map_nsmul, hx']; simp
        have k₂ : d • B e x = 0 := by rw [← map_nsmul, hx', map_zero]
        refine ⟨⟨⟨B x f, k₁⟩, ⟨B e x, k₂⟩, ⟨_, hpr x hx, ?_⟩⟩, Subtype.ext ?_⟩
        · rw [smul_sub, smul_sub, ← smul_assoc, ← smul_assoc, k₁, k₂, hx']
          simp
        · show B x f • e + B e x • f + (x - B x f • e - B e x • f) = x
          abel
    have h := Nat.card_eq_of_bijective F hF
    rw [hc d hdM, Nat.card_prod, Nat.card_prod, card_torsion_zmod hdM,
      show d ^ (2 * (g + 1)) = d * (d * d ^ (2 * g)) by ring] at h
    exact Nat.eq_of_mul_eq_mul_left hd0 (Nat.eq_of_mul_eq_mul_left hd0 h))
  refine ⟨Fin.cons e e', Fin.cons f f', ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp [hB.self_eq_zero]
    · simp [((hmem _).1 (he' _)).2.1]
    · simp [hB.eq_iff.1 ((hmem _).1 (he' _)).2.1]
    · simp [hs.left_left]
  · intro i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp [hB.self_eq_zero]
    · simp [((hmem _).1 (hf' _)).2.2]
    · simp [hB.eq_iff.1 ((hmem _).1 (hf' _)).2.2]
    · simp [hs.right_right]
  · intro i
    cases i using Fin.cases
    · simp [hd]
    · simp [hs.left_right_self]
  · intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact absurd rfl hij
    · simp [((hmem _).1 (hf' _)).2.1]
    · simp [hB.eq_iff.1 ((hmem _).1 (he' _)).2.2]
    · simpa using hs.left_right_ne _ _ fun a => hij (congrArg _ a)
  · intro i
    cases i using Fin.cases
    · exact he
    · exact (he' _).1
  · intro i
    cases i using Fin.cases
    · exact hf
    · exact (hf' _).1
end GlobalTheory.SympMod
