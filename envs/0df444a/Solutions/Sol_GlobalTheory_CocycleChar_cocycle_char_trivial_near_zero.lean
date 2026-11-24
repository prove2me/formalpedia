-- Prove2me | solution 1 for GlobalTheory.CocycleChar.cocycle_char_trivial_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:31:35.823138+00:00
-- url     : https://prove2.me/submissions/7f893263-f9f5-4625-b7f4-80174fb668fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerMore
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousCharacterCocycleTrivialNearZero
import Theorems.Thm_GlobalTheory_CocycleChar_pow_near_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CocycleChar
namespace GlobalTheory.CocycleChar
theorem _root_.solution :
    ∀ {A V : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A]
    [NonarchimedeanAddGroup A] [AddCommGroup V] [TopologicalSpace V] [T2Space V] (lam : A →+ V), Continuous lam →
    ∀ (ε : V → V → ℂ), (∃ N ∈ nhds (0 : V), ∀ x ∈ N, ∀ y ∈ N, ε x y = 1) → (∀ x, ε x 0 = 1) →
    ∀ (χ : A → ℂ), Continuous χ → (∀ a, lam a = 0 → χ a = 1) →
    (∀ a b, χ (a + b) = χ a * χ b * ε (lam a) (lam b)) → ∃ U ∈ nhds (0 : V), ∀ a, lam a ∈ U → χ a = 1 := by
  intro A V _ _ _ _ _ _ _ _ lam hlam ε ⟨N, hN, hεN⟩ hε0 χ hχ hker hmul
  have hχ0 : χ 0 = 1 := hker 0 (map_zero lam)

  have hW : lam ⁻¹' N ∩ {a : A | ‖χ a - 1‖ < 1 / 2} ∈ nhds (0 : A) := by
    refine Filter.inter_mem ?_ ?_
    · exact hlam.continuousAt.preimage_mem_nhds (by simpa using hN)
    · exact (isOpen_lt (hχ.sub continuous_const).norm continuous_const).mem_nhds (by simp [hχ0])
  obtain ⟨K₀, hK₀⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hW
  have hpow : ∀ a ∈ K₀, ∀ n : ℕ, χ (n • a) = χ a ^ n := by
    intro a ha n
    induction n with
    | zero => simp [hχ0]
    | succ n ih =>
      have h1 : n • a ∈ K₀ := K₀.toAddSubgroup.nsmul_mem ha n
      rw [succ_nsmul, hmul, ih, hεN _ (hK₀ h1).1 _ (hK₀ ha).1, pow_succ, mul_one]
  have hK₀one : ∀ a ∈ K₀, χ a = 1 := by
    intro a ha
    refine pow_near_one fun n => ?_
    rw [← hpow a ha n]
    exact (hK₀ (K₀.toAddSubgroup.nsmul_mem ha n)).2

  set S : AddSubgroup A := K₀.toAddSubgroup ⊔ lam.ker with hSdef
  have hSopen : IsOpen (S : Set A) :=
    AddSubgroup.isOpen_mono (le_sup_left : K₀.toAddSubgroup ≤ S) K₀.isOpen
  set C : Set A := (S : Set A)ᶜ
  have hCc : IsCompact C := hSopen.isClosed_compl.isCompact
  have hLc : IsClosed (lam '' C) := (hCc.image hlam).isClosed
  have h0 : (0 : V) ∉ lam '' C := by
    rintro ⟨c, hc, hc0⟩
    exact hc (le_sup_right (a := K₀.toAddSubgroup) (AddMonoidHom.mem_ker.2 hc0))
  refine ⟨(lam '' C)ᶜ, hLc.isOpen_compl.mem_nhds h0, fun a ha => ?_⟩
  have haS : a ∈ S := by
    by_contra h
    exact ha ⟨a, h, rfl⟩
  obtain ⟨k, hk, n, hn, rfl⟩ := AddSubgroup.mem_sup.1 haS
  rw [AddMonoidHom.mem_ker] at hn
  rw [hmul, hK₀one k hk, hker n hn, hn, hε0, mul_one, mul_one]
end GlobalTheory.CocycleChar
