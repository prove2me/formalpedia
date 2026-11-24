-- Prove2me | solution 1 for GlobalTheory.quadratic_exists_integral_generator_common_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:30:36.954535+00:00
-- url     : https://prove2.me/submissions/79e1bcdd-3409-4312-bd66-b9dbb1c3fc08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_QuadraticRingOfIntegersMulMemSpanOneGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_QuadraticExistsIntegralGeneratorCommonDenominato
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField
namespace GlobalTheory
open NumberField in
private theorem exists_integral_generator_common_denom_of_finrank_two
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h : Module.finrank F E = 2) :
    ∃ θ : 𝓞 E, (θ : E) ∉ Set.range (algebraMap F E) ∧
      ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F,
        algebraMap (𝓞 F) (𝓞 E) D * y =
          algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ Set.range (algebraMap F E) := by
    by_contra! hx
    have htop : (⊤ : IntermediateField F E) = ⊥ := by
      ext x
      simp only [IntermediateField.mem_top, true_iff]
      exact IntermediateField.mem_bot.mpr (hx x)
    have h1 := IntermediateField.finrank_eq_one_iff.mpr htop
    rw [IntermediateField.finrank_top'] at h1
    omega
  obtain ⟨n, hn, hnx⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset E)
  have hint : IsIntegral ℤ (n • x) := hnx x (Finset.mem_singleton_self x)
  obtain ⟨θ, hθx⟩ : ∃ θ : 𝓞 E, (θ : E) = (n : E) * x :=
    ⟨⟨n • x, hint⟩, by rw [← zsmul_eq_mul]; rfl⟩
  have hθ : (θ : E) ∉ Set.range (algebraMap F E) := by
    rintro ⟨a, ha⟩
    apply hx
    refine ⟨a / n, ?_⟩
    have hnE : (n : E) ≠ 0 := by exact_mod_cast hn
    rw [map_div₀, map_intCast, ha, hθx]
    field_simp
  have hli : LinearIndependent F ![(1 : E), (θ : E)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply hθ
      refine ⟨-s / t, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).mpr ht
      rw [map_div₀, map_neg]
      field_simp
      linear_combination -hst
  obtain ⟨b, hb1⟩ : ∃ b : Module.Basis (Fin 2) F E, ⇑b = ![(1 : E), (θ : E)] :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [h, Fintype.card_fin]),
      coe_basisOfLinearIndependentOfCardEqFinrank _ _⟩
  have hb : ∀ z : E, z = algebraMap F E (b.repr z 0) + algebraMap F E (b.repr z 1) * θ := by
    intro z
    conv_lhs => rw [← b.sum_repr z]
    rw [Fin.sum_univ_two, hb1]
    simp [Algebra.smul_def]
  set B := RingOfIntegers.basis E
  obtain ⟨d, hd, hdint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin 2 =>
      b.repr (B p.1 : E) p.2)
  have hmem : ∀ i k, IsIntegral ℤ (d • b.repr (B i : E) k) := fun i k =>
    hdint _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, k)))
  refine ⟨θ, hθ, (d : 𝓞 F), by exact_mod_cast hd, ?_⟩
  let M : Submodule ℤ (𝓞 E) :=
    { carrier := {z | ∃ u v : 𝓞 F, z = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ}
      add_mem' := by
        rintro _ _ ⟨u, v, rfl⟩ ⟨u', v', rfl⟩
        exact ⟨u + u', v + v', by simp only [map_add]; ring⟩
      zero_mem' := ⟨0, 0, by simp⟩
      smul_mem' := by
        rintro c _ ⟨u, v, rfl⟩
        exact ⟨c • u, c • v, by simp only [zsmul_eq_mul, map_mul, map_intCast]; ring⟩ }
  have hall : ∀ y : 𝓞 E, algebraMap (𝓞 F) (𝓞 E) (d : 𝓞 F) * y ∈ M := by
    intro y
    have hspan : y ∈ Submodule.span ℤ (Set.range B) := by rw [B.span_eq]; trivial
    induction hspan using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      refine ⟨⟨_, hmem i 0⟩, ⟨_, hmem i 1⟩, ?_⟩
      rw [RingOfIntegers.ext_iff]
      have e := hb (B i : E)
      have key : algebraMap F E (d : F) * (B i : E) =
          algebraMap F E (d • b.repr (B i : E) 0) +
            algebraMap F E (d • b.repr (B i : E) 1) * θ := by
        simp only [zsmul_eq_mul, map_mul, map_intCast]
        linear_combination (d : E) * e
      exact key
    | zero => simpa using M.zero_mem
    | add z w _ _ hz hw => rw [mul_add]; exact M.add_mem hz hw
    | smul c z _ hz => rw [mul_smul_comm]; exact M.smul_mem c hz
  intro y
  obtain ⟨u, v, huv⟩ := hall y
  exact ⟨u, v, huv⟩
end GlobalTheory
end

set_option autoImplicit false
open NumberField
open GlobalTheory
open NumberField
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      [Algebra.IsQuadraticExtension F E], ∃ θ : 𝓞 E, (θ : E) ∉ Set.range (algebraMap F E) ∧
      ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F,
        algebraMap (𝓞 F) (𝓞 E) D * y =
          algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  intro F E _ _ _ _ _ _
  exact exists_integral_generator_common_denom_of_finrank_two F E
    (Algebra.IsQuadraticExtension.finrank_eq_two F E)
end _root_.GlobalTheory
end GlobalTheory
