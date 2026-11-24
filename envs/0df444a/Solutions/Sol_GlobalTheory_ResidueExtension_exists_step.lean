-- Prove2me | solution 1 for GlobalTheory.ResidueExtension.exists_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:32:53.071687+00:00
-- url     : https://prove2.me/submissions/9fd43a13-823a-4362-ada8-52f1551255e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsCompleteDiscreteValuationRingWithResidues
import Theorems.Thm_GlobalTheory_ResidueExtension_exists_localization
import Theorems.Thm_GlobalTheory_ResidueExtension_exists_generator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory
open GlobalTheory.ResidueExtension
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]
namespace GlobalTheory.ResidueExtension
theorem _root_.solution (r : O →+* Ω) (hr : RingHom.ker r = maximalIdeal O) (a : Ω) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
      (j : O →+* B) (r' : B →+* Ω), Function.Injective j ∧ r'.comp j = r ∧
      RingHom.ker r' = maximalIdeal B ∧ a ∈ Set.range r' := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨G, hG, h0, hgen⟩ := exists_generator r hr a hπ
  have hrπ : r π = 0 := by
    rw [← RingHom.mem_ker, hr, hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self _
  have hk : RingHom.ker (AdjoinRoot.lift r a h0) = Ideal.span {AdjoinRoot.of G π} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective x
      rw [RingHom.mem_ker, AdjoinRoot.lift_mk] at hx
      obtain ⟨g, h, rfl⟩ := hgen f hx
      rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, zero_add, map_mul, AdjoinRoot.mk_C]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, AdjoinRoot.lift_of, hrπ]
  have hreg : ∀ x, AdjoinRoot.of G π * x = 0 → x = 0 := by
    intro x hx
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [← AdjoinRoot.mk_C, ← map_mul, AdjoinRoot.mk_eq_zero] at hx
    rw [AdjoinRoot.mk_eq_zero]
    rcases hG with hG | rfl
    · rw [← modByMonic_eq_zero_iff_dvd hG] at hx ⊢
      rw [← smul_eq_C_mul, smul_modByMonic] at hx
      exact (smul_eq_zero.mp hx).resolve_left hπ.ne_zero
    · rw [zero_dvd_iff] at hx ⊢
      exact (mul_eq_zero.mp hx).resolve_left (C_ne_zero.mpr hπ.ne_zero)
  obtain ⟨B, _, _, _, j, r', h1, h2, h3, h4⟩ := exists_localization (AdjoinRoot.of G)
    (AdjoinRoot.lift r a h0) hπ hk hreg
  exact ⟨B, _, ‹_›, ‹_›, j, r', h1, h2.trans (AdjoinRoot.lift_comp_of h0), h3,
    h4 ⟨_, AdjoinRoot.lift_root h0⟩⟩
end GlobalTheory.ResidueExtension
