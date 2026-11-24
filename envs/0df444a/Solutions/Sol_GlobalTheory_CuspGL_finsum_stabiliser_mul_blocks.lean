-- Prove2me | solution 1 for GlobalTheory.CuspGL.finsum_stabiliser_mul_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:04:07.702403+00:00
-- url     : https://prove2.me/submissions/2d53d7eb-d383-4276-b965-08e585c132c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumSubspaceStabilizerMulBlockFunctions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (W : Submodule F V) (Φ : Module.End F W → ℂ)
    (Φ' : Module.End F (V ⧸ W) → ℂ) :
    ∑ᶠ g : {g : Module.End F V // ∀ x ∈ W, g x ∈ W},
        Φ (g.1.restrict g.2) * Φ' (W.mapQ W g.1 (fun x hx => g.2 x hx)) =
      (Nat.card F : ℂ) ^ (Module.finrank F W * Module.finrank F (V ⧸ W)) *
        ((∑ᶠ a, Φ a) * ∑ᶠ b, Φ' b) := by
  classical
  obtain ⟨s, hs⟩ := W.mkQ.exists_rightInverse_of_surjective W.range_mkQ
  have hs' : ∀ y, W.mkQ (s y) = y := fun y => LinearMap.congr_fun hs y
  have hmem : ∀ x : V, (LinearMap.id - s ∘ₗ W.mkQ : V →ₗ[F] V) x ∈ W := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hs',
      sub_self]
  let p : V →ₗ[F] W := LinearMap.codRestrict W _ hmem
  have hp : ∀ x : V, (p x : V) = x - s (W.mkQ x) := fun x => rfl
  have hπ : ∀ x : W, W.mkQ (x : V) = 0 := fun x => by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact x.2
  have hpι : ∀ x : W, p (x : V) = x := fun x => Subtype.ext (by rw [hp, hπ, map_zero, sub_zero])
  have hps : ∀ y, p (s y) = 0 := fun y => Subtype.ext (by rw [hp, hs', sub_self]; rfl)
  let G : Module.End F W × Module.End F (V ⧸ W) × ((V ⧸ W) →ₗ[F] W) → Module.End F V :=
    fun t => W.subtype ∘ₗ t.1 ∘ₗ p + s ∘ₗ t.2.1 ∘ₗ W.mkQ + W.subtype ∘ₗ t.2.2 ∘ₗ W.mkQ
  have hG : ∀ t x, G t x = (t.1 (p x) : V) + s (t.2.1 (W.mkQ x)) + (t.2.2 (W.mkQ x) : V) :=
    fun t x => rfl
  have hGι : ∀ t (x : W), G t x = (t.1 x : V) := by
    intro t x
    rw [hG, hpι, hπ]; simp
  have hGW : ∀ t, ∀ x ∈ W, G t x ∈ W := by
    intro t x hx
    rw [hGι t ⟨x, hx⟩]; exact (t.1 _).2
  have h1 : ∀ t, (G t).restrict (hGW t) = t.1 := by
    intro t
    ext x
    rw [LinearMap.restrict_coe_apply, hGι]
  have h2 : ∀ t, W.mapQ W (G t) (fun x hx => hGW t x hx) = t.2.1 := by
    intro t
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.comp_apply]
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, ← Submodule.mkQ_apply, hG, map_add, map_add,
      hπ, hπ, hs', zero_add, add_zero, Submodule.mkQ_apply]
  have h3 : ∀ t, p ∘ₗ G t ∘ₗ s = t.2.2 := by
    intro t
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply]
    rw [hG, hps, hs', map_add, map_add, hps, hpι, hpι, map_zero, zero_add, zero_add]
  let e : (Module.End F W × Module.End F (V ⧸ W) × ((V ⧸ W) →ₗ[F] W)) ≃
      {g : Module.End F V // ∀ x ∈ W, g x ∈ W} :=
    { toFun := fun t => ⟨G t, hGW t⟩
      invFun := fun g => (g.1.restrict g.2, W.mapQ W g.1 (fun x hx => g.2 x hx), p ∘ₗ g.1 ∘ₗ s)
      left_inv := fun t => Prod.ext (h1 t) (Prod.ext (h2 t) (h3 t))
      right_inv := by
        intro g
        refine Subtype.ext (LinearMap.ext fun x => ?_)
        show G _ x = _
        rw [hG]
        simp only [LinearMap.restrict_coe_apply, LinearMap.comp_apply]
        have hq : W.mapQ W g.1 (fun x hx => g.2 x hx) (W.mkQ x) = W.mkQ (g.1 (s (W.mkQ x))) := by
          conv_lhs => rw [← hs' (W.mkQ x)]
          rfl
        rw [hq, hp, hp, map_sub]
        abel }
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F W) := Module.finite_of_finite F
  haveI : Finite (Module.End F (V ⧸ W)) := Module.finite_of_finite F
  haveI : Finite ((V ⧸ W) →ₗ[F] W) := Module.finite_of_finite F
  haveI := Fintype.ofFinite (Module.End F W)
  haveI := Fintype.ofFinite (Module.End F (V ⧸ W))
  haveI := Fintype.ofFinite ((V ⧸ W) →ₗ[F] W)
  have hcard : Fintype.card ((V ⧸ W) →ₗ[F] W) =
      Nat.card F ^ (Module.finrank F W * Module.finrank F (V ⧸ W)) := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := F),
      Module.finrank_linearMap, mul_comm]
  rw [← finsum_comp_equiv e]
  have : ∀ t, Φ ((e t).1.restrict (e t).2) * Φ' (W.mapQ W (e t).1 (fun x hx => (e t).2 x hx))
      = Φ t.1 * Φ' t.2.1 := by
    intro t
    show Φ ((G t).restrict (hGW t)) * Φ' (W.mapQ W (G t) (fun x hx => hGW t x hx)) = _
    rw [h1, h2]
  rw [finsum_congr this, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, Nat.cast_pow]
end GlobalTheory.CuspGL
