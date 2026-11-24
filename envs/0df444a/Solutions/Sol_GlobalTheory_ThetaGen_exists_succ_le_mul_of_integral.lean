-- Prove2me | solution 1 for GlobalTheory.ThetaGen.exists_succ_le_mul_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:11.781804+00:00
-- url     : https://prove2.me/submissions/af94879d-0ecc-47a6-911d-297654a6253d

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousOfMemSpanPow
import Theorems.Thm_GlobalTheory_ThetaGen_exists_succ_le_mul
import Theorems.Thm_GlobalTheory_ThetaGen_entire_mul_eq_zero
import Theorems.Thm_GlobalTheory_ThetaGen_differentiable_of_mem_adjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaGen
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.ThetaGen
theorem _root_.solution {ι : Type} [Finite ι] (R : ℕ → Submodule ℂ (E → ℂ))
    (h1 : (1 : E → ℂ) ∈ R 0) (hmul : ∀ a b, R a * R b ≤ R (a + b))
    (hdiff : ∀ d, ∀ f ∈ R d, Differentiable ℂ f) (θ : ι → E → ℂ) (hθ : ∀ c, θ c ∈ R 1)
    (hint : ∀ d, ∀ f ∈ R d,
      IsIntegral (Algebra.adjoin ℂ (Set.range fun (c : ι) (p : ℂ × E) => p.1 * θ c p.2))
        (fun p : ℂ × E => p.1 ^ d * f p.2) ∧
      ∃ a ∈ Algebra.adjoin ℂ (Set.range fun (c : ι) (p : ℂ × E) => p.1 * θ c p.2),
        ∃ b ∈ Algebra.adjoin ℂ (Set.range fun (c : ι) (p : ℂ × E) => p.1 * θ c p.2),
          b ≠ 0 ∧ b * (fun p : ℂ × E => p.1 ^ d * f p.2) = a)
    (hfin : ∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra ℂ A]
      [Algebra.FiniteType ℂ A] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B],
      (∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) →
        Module.Finite A B) :
    ∃ e, ∀ d, e ≤ d → R (d + 1) ≤ R 1 * R d := by
  set A := Algebra.adjoin ℂ (Set.range fun (c : ι) (p : ℂ × E) => p.1 * θ c p.2) with hA
  have hA1 : A ≤ Algebra.adjoin ℂ {F | ∃ f ∈ R 1, F = homog 1 f} := by
    apply Algebra.adjoin_mono
    rintro _ ⟨c, rfl⟩
    exact ⟨θ c, hθ c, by funext p; simp [homog]⟩
  have hAR : A ≤ gradedRing R := hA1.trans (Algebra.adjoin_mono (by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨1, f, hf, rfl⟩))
  let B : Subalgebra A (ℂ × E → ℂ) := Algebra.adjoin A {F | ∃ d, ∃ f ∈ R d, F = homog d f}
  have hB : ∀ F, F ∈ B ↔ F ∈ gradedRing R := by
    intro F
    constructor
    · intro hF
      induction hF using Algebra.adjoin_induction with
      | mem x hx => exact Algebra.subset_adjoin hx
      | algebraMap c => exact hAR c.2
      | add x y _ _ hx hy => exact add_mem hx hy
      | mul x y _ _ hx hy => exact mul_mem hx hy
    · intro hF
      induction hF using Algebra.adjoin_induction with
      | mem x hx => exact Algebra.subset_adjoin hx
      | algebraMap c => exact B.algebraMap_mem (algebraMap ℂ A c)
      | add x y _ _ hx hy => exact add_mem hx hy
      | mul x y _ _ hx hy => exact mul_mem hx hy
  have hd : ∀ F ∈ gradedRing R, Differentiable ℂ F := by
    intro F hF
    refine differentiable_of_mem_adjoin ?_ hF
    rintro _ ⟨d, f, hf, rfl⟩
    have := hdiff d f hf
    unfold homog
    fun_prop
  haveI : NoZeroDivisors A := ⟨fun {a b} hab =>
    (entire_mul_eq_zero (hd _ (hAR a.2)) (hd _ (hAR b.2)) (congrArg Subtype.val hab)).imp
      Subtype.ext Subtype.ext⟩
  haveI : NoZeroDivisors B := ⟨fun {a b} hab =>
    (entire_mul_eq_zero (hd _ ((hB _).1 a.2)) (hd _ ((hB _).1 b.2))
      (congrArg Subtype.val hab)).imp Subtype.ext Subtype.ext⟩
  haveI : IsDomain A := NoZeroDivisors.to_isDomain _
  haveI : Nontrivial B := ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
  haveI : IsDomain B := NoZeroDivisors.to_isDomain _
  haveI : Algebra.FiniteType ℂ A :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2
    fun a b hab => Subtype.ext (congrArg (Subtype.val : B → (ℂ × E → ℂ)) hab)
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.adjoin (by
    rintro _ ⟨d, f, hf, rfl⟩
    exact (hint d f hf).1)
  have hfrac : ∀ F ∈ B, ∃ a a' : A, a' ≠ 0 ∧ (a' : ℂ × E → ℂ) * F = a := by
    intro F hF
    induction hF using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨d, f, hf, rfl⟩ := hx
      obtain ⟨a, ha, b, hb, hb0, h⟩ := (hint d f hf).2
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h0 => hb0 (congrArg Subtype.val h0), h⟩
    | algebraMap c => exact ⟨c, 1, one_ne_zero, one_mul _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, a', ha, h⟩ := hx
      obtain ⟨b, b', hb, h'⟩ := hy
      refine ⟨b' * a + a' * b, a' * b', mul_ne_zero ha hb, ?_⟩
      push_cast
      rw [← h, ← h']; ring
    | mul x y _ _ hx hy =>
      obtain ⟨a, a', ha, h⟩ := hx
      obtain ⟨b, b', hb, h'⟩ := hy
      refine ⟨a * b, a' * b', mul_ne_zero ha hb, ?_⟩
      push_cast
      rw [← h, ← h']; ring
  have hF : Module.Finite A B := hfin A B fun b => by
    obtain ⟨a, a', ha, h⟩ := hfrac b b.2
    exact ⟨a, a', ha, Subtype.ext h⟩
  exact exists_succ_le_mul R h1 hmul A hA1 (Subalgebra.toSubmodule B)
    (Module.Finite.iff_fg.1 hF) hB
end GlobalTheory.ThetaGen
