-- Prove2me | solution 1 for GlobalTheory.ThetaGL.DualPair.exists_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:31:13.598933+00:00
-- url     : https://prove2.me/submissions/f18f4885-6af3-419c-ba4d-0724c08fba10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_IsParahoricVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairContragredientQuotient
import Theorems.Thm_GlobalTheory_ThetaGL_DualPair_ev_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ThetaGL.DualPair.ev_tmul

set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct
open GlobalTheory GlobalTheory.ThetaGL GlobalTheory.ThetaGL.DualPair
variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.ThetaGL.DualPair
theorem _root_.solution (π : Representation ℂ G W) (hπ : IsSmooth π) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (w : W) :
    ∃ w' ∈ fixed π K, ∀ T : W →ₗ[ℂ] V, (∀ k ∈ K, ∀ x, T (π k x) = T x) → T w = T w' := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let S : Subgroup K :=
    { carrier := {k | π (k : G) w = w}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hS : IsOpen (S : Set K) := (hπ w).preimage continuous_subtype_val
  haveI : Finite (K ⧸ S) := Subgroup.quotient_finite_of_isOpen S hS
  haveI : Fintype (K ⧸ S) := Fintype.ofFinite _
  let φ : K ⧸ S → W := fun q => Quotient.liftOn' q (fun k : K => π (k : G) w) (fun a b h => by
    have h' : a⁻¹ * b ∈ S := QuotientGroup.leftRel_apply.1 h
    have h2 : π ((a⁻¹ * b : K) : G) w = w := h'
    have h3 : π (b : G) w = π (a : G) w := by
      conv_rhs => rw [← h2]
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    exact h3.symm)
  have hφ : ∀ (k : K) (q : K ⧸ S), φ (k • q) = π (k : G) (φ q) := by
    intro k q
    induction q using QuotientGroup.induction_on with
    | H a =>
      show π ((k * a : K) : G) w = π (k : G) (π (a : G) w)
      rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  have hcard : ((Fintype.card (K ⧸ S) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨((Fintype.card (K ⧸ S) : ℕ) : ℂ)⁻¹ • ∑ q, φ q, ?_, fun T hT => ?_⟩
  · intro k
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [map_smul, map_sum]
    congr 1
    simp_rw [← hφ]
    exact Equiv.sum_comp (MulAction.toPerm k) φ
  · have h1 : ∀ q, T (φ q) = T w := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H a => exact hT _ a.2 w
    rw [map_smul, map_sum]
    simp only [h1, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]
end GlobalTheory.ThetaGL.DualPair
