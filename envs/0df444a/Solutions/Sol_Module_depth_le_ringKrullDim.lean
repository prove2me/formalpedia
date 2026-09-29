-- Prove2me | solution 1 for Module.depth_le_ringKrullDim
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/235e90be-c7de-5051-9f2f-cde785c64dd4

import Definitions.Def_Patching_SystemTypes
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_depth_le_ringKrullDim

set_option autoImplicit false

open IsLocalRing RingTheory

namespace Module
p2m_export "Module" "support mem_annihilator annihilator mk annihilator_eq_top_iff support_eq_empty_iff support_eq_zeroLocus length depth"
p2m_open "Module"

variable (R M : Type*) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]

private lemma depth_le_krullDim_support' [Nontrivial M] [Module.Finite R M] :
    .some (Module.depth R M) ≤ Order.krullDim (Module.support R M) := by
  have : Nonempty (Module.support R M) := by
    rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty,
      ne_eq, support_eq_empty_iff, not_subsingleton_iff_nontrivial]
  cases h : Order.krullDim (Module.support R M) with
  | bot => simpa using Order.krullDim_nonneg.trans_eq h
  | coe n =>
  cases n with
  | top => simp
  | coe n =>
  clear this
  simp only [WithBot.coe_le_coe, ge_iff_le]
  induction n using Nat.strong_induction_on generalizing M with
  | h n IH =>
    rw [depth, sSup_le_iff]
    rintro _ ⟨l, hl, hl', rfl⟩
    apply WithTop.coe_le_coe.mpr ?_
    cases l with
    | nil => simp
    | cons x l =>
    simp only [Sequence.isWeaklyRegular_cons_iff] at hl
    have : Nontrivial (QuotSMulTop x M) := by
      apply Submodule.Quotient.nontrivial_iff.2
      rw [← Submodule.ideal_span_singleton_smul, ne_comm]
      apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      refine le_trans ?_ (maximalIdeal_le_jacobson _)
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hl' _ (by simp)
    rw [Module.support_eq_zeroLocus, ← ringKrullDim_quotient] at h
    let f : (R ⧸ annihilator R M) ⧸ Ideal.span {(Ideal.Quotient.mk (annihilator R M)) x} →+*
        R ⧸ annihilator R (QuotSMulTop x M) :=
      Ideal.Quotient.lift _ (Ideal.quotientMap _ (.id R)
        (LinearMap.annihilator_le_of_surjective _ (Submodule.mkQ_surjective _)))
        (show Ideal.span _ ≤ RingHom.ker _ by
          rw [Ideal.span_le, Set.singleton_subset_iff]
          simp only [SetLike.mem_coe, RingHom.mem_ker, Ideal.quotientMap_mk, RingHom.id_apply,
            Ideal.Quotient.eq_zero_iff_mem, Module.mem_annihilator]
          intro m
          obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          exact ⟨m, trivial, rfl⟩)
    have hf : Function.Surjective f := by
      apply Ideal.Quotient.lift_surjective_of_surjective
      apply Ideal.Quotient.lift_surjective_of_surjective
      exact Ideal.Quotient.mk_surjective
    have := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (R := R ⧸ annihilator R M)
        (r := Ideal.Quotient.mk _ x) (by
      rw [← nonZeroDivisorsLeft_eq_nonZeroDivisors]
      intro z hz
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      simp only [← map_mul, Ideal.Quotient.eq_zero_iff_mem,
        Module.mem_annihilator] at hz ⊢
      intro m
      apply hl.1
      simpa [smul_comm x, mul_smul] using hz m)
    rw [h] at this
    replace this := (add_le_add (ringKrullDim_le_of_surjective f hf) le_rfl).trans this
    cases h2 : ringKrullDim (R ⧸ annihilator R (QuotSMulTop x M)) with
    | bot =>
      have : Nontrivial (R ⧸ annihilator R (QuotSMulTop x M)) := by
        rw [Ideal.Quotient.nontrivial_iff, ← Submodule.annihilator_top, ne_eq,
          Submodule.annihilator_eq_top_iff]
        exact top_ne_bot
      have := ringKrullDim_nonneg_of_nontrivial.trans_eq h2
      simp at this
    | coe m =>
    cases m with
    | top =>
      have : (⊤ : ℕ∞) ≤ (n : ℕ) := by apply WithBot.coe_le_coe.mp; (simp only [h2] at this; exact this)
      cases (ENat.coe_lt_top n).not_ge this
    | coe m =>
    rw [h2] at this
    replace this : m + 1 ≤ n := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp this)
    replace IH := IH m (Nat.lt_of_succ_le this) (QuotSMulTop x M)
      (by rwa [Module.support_eq_zeroLocus, ← ringKrullDim_quotient])
    have hlen : (l.length : ℕ∞) ≤ (m : ℕ∞) := by
      have hld : l.length ≤ Module.depth R (QuotSMulTop x M) :=
        le_sSup ⟨l, hl.2, fun r hr => hl' r (List.mem_cons_of_mem _ hr), rfl⟩
      exact hld.trans IH
    replace hlen := WithTop.coe_le_coe.mp hlen
    simp only [List.length_cons, ge_iff_le]
    omega

private lemma depth_le_dim_annihilator' [Nontrivial M] [Module.Finite R M] :
    .some (Module.depth R M) ≤ ringKrullDim (R ⧸ Module.annihilator R M) := by
  rw [ringKrullDim_quotient, ← Module.support_eq_zeroLocus]
  exact depth_le_krullDim_support' R M

end Module

theorem solution {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Nontrivial M] [Module.Finite R M] :
    .some (Module.depth R M) ≤ ringKrullDim R :=
  (Module.depth_le_dim_annihilator' R M).trans (ringKrullDim_quotient_le _)

end S_Module_depth_le_ringKrullDim
end P2MW
export P2MW.S_Module_depth_le_ringKrullDim (solution)
