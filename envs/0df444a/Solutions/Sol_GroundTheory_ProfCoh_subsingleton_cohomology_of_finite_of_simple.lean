-- Prove2me | solution 1 for GroundTheory.ProfCoh.subsingleton_cohomology_of_finite_of_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:20:50.437482+00:00
-- url     : https://prove2.me/submissions/dbb64cfa-0c81-4edd-93cd-03c142e1f044

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_GroundTheory_ProfCoh_subsingleton_cohomology_of_subsingleton
import Theorems.Thm_GroundTheory_ProfCoh_subsingleton_cohomology_of_sub_quot
import Theorems.Thm_GroundTheory_ProfCoh_eq_zero_of_pow_nsmul_eq_zero
import Theorems.Thm_GroundTheory_ProfCoh_cohomologyCoindCokernelIso_hom
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.cohomologyCoindCokernelIso_hom
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Limits
universe u
attribute [local instance 2000] Rep.hV2
attribute [-instance] ULift.module
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {p : ℕ} {m : ℕ}
    (h : ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A], IsSimpleOrder (Subrepresentation A.ρ) →
      (∀ a : A, p • a = 0) → Subsingleton (cohomology A m))
    (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] [Finite A]
    (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) : Subsingleton (cohomology A m) := by
  suffices H : ∀ N : ℕ, ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] [Finite A],
      (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) → Nat.card A = N → Subsingleton (cohomology A m) from
    H _ A hA rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro A _ _ hA hN
  rcases subsingleton_or_nontrivial A with hs | hnt
  · exact subsingleton_cohomology_of_subsingleton A m
  have : Nontrivial (Subrepresentation A.ρ) := ⟨⟨⊥, ⊤, fun hbt => by
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    have : a ∈ (⊤ : Subrepresentation A.ρ).toSubmodule := Submodule.mem_top
    rw [← hbt] at this
    exact ha ((Submodule.mem_bot _).1 this)⟩⟩
  by_cases hsimple : IsSimpleOrder (Subrepresentation A.ρ)
  · apply h A hsimple
    let P : Subrepresentation A.ρ :=
      { toSubmodule := LinearMap.range (p • LinearMap.id : A →ₗ[ULift.{u} ℤ] A)
        apply_mem_toSubmodule := by
          rintro g _ ⟨b, rfl⟩
          exact ⟨A.ρ g b, by simp [map_nsmul]⟩ }
    rcases hsimple.eq_bot_or_eq_top P with hP | hP
    · intro a
      have : p • a ∈ P.toSubmodule := ⟨a, by simp⟩
      rw [hP] at this
      exact (Submodule.mem_bot _).1 this
    · exfalso
      have hsurj : Function.Surjective fun a : A => p • a := by
        intro a
        have : a ∈ (⊤ : Subrepresentation A.ρ).toSubmodule := Submodule.mem_top
        rw [← hP] at this
        obtain ⟨b, hb⟩ := this
        exact ⟨b, by simpa using hb⟩
      have hinj := Finite.injective_iff_surjective.2 hsurj
      obtain ⟨a, ha⟩ := exists_ne (0 : A)
      obtain ⟨k, hk⟩ := hA a
      exact ha (eq_zero_of_pow_nsmul_eq_zero (fun x hx => hinj (hx.trans (smul_zero p).symm)) k a hk)
  · obtain ⟨W, hW0, hWT⟩ : ∃ W : Subrepresentation A.ρ, W ≠ ⊥ ∧ W ≠ ⊤ := by
      by_contra hne
      push Not at hne
      exact hsimple { toNontrivial := inferInstance,
                      eq_bot_or_eq_top := fun W => (em (W = ⊥)).imp id (hne W) }
    have hst : ∀ g, W.toSubmodule ≤ W.toSubmodule.comap (A.ρ g) :=
      fun g v hv => W.apply_mem_toSubmodule g hv
    obtain ⟨a, ha⟩ : ∃ a : A, a ∉ W.toSubmodule := by
      by_contra hc
      push Not at hc
      exact hWT (Subrepresentation.ext (Submodule.eq_top_iff'.2 hc))
    obtain ⟨w, hw, hw0⟩ : ∃ w ∈ W.toSubmodule, w ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hW0 (Subrepresentation.ext ((Submodule.eq_bot_iff _).2 hc))
    have hfinS : Finite (A.subrepresentation W.toSubmodule hst) :=
      inferInstanceAs (Finite W.toSubmodule)
    have hfinQ : Finite (A.quotient W.toSubmodule hst) :=
      Finite.of_surjective _ (Submodule.mkQ_surjective W.toSubmodule)
    have hcardS : Nat.card (A.subrepresentation W.toSubmodule hst) < N := by
      rw [← hN]
      exact Finite.card_subtype_lt ha
    have hone : 1 < Nat.card (A.subrepresentation W.toSubmodule hst) := by
      have : Nontrivial W.toSubmodule := ⟨⟨⟨w, hw⟩, 0, fun h => hw0 (congrArg Subtype.val h)⟩⟩
      exact Finite.one_lt_card_iff_nontrivial.2 this
    have hc : Nat.card A = Nat.card (A.quotient W.toSubmodule hst) *
        Nat.card (A.subrepresentation W.toSubmodule hst) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup W.toSubmodule.toAddSubgroup
    have hcardQ : Nat.card (A.quotient W.toSubmodule hst) < N := by
      rw [← hN, hc]
      exact lt_mul_of_one_lt_right Nat.card_pos hone
    apply subsingleton_cohomology_of_sub_quot A W.toSubmodule hst m
    · refine ih _ hcardS (A.subrepresentation W.toSubmodule hst) ?_ rfl
      rintro ⟨b, hb⟩
      obtain ⟨k, hk⟩ := hA b
      exact ⟨k, Subtype.ext hk⟩
    · refine ih _ hcardQ (A.quotient W.toSubmodule hst) ?_ rfl
      intro x
      obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective W.toSubmodule x
      obtain ⟨k, hk⟩ := hA b
      exact ⟨k, by rw [← map_nsmul, hk, map_zero]⟩
end GroundTheory.ProfCoh
