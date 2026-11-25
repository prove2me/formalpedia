-- Prove2me | solution 1 for GlobalTheory.SecLifts.exists_compatible_sections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:04:54.399822+00:00
-- url     : https://prove2.me/submissions/0d1c16f8-4b24-4b25-b7da-d59444cbe8a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompatibleSections
import Theorems.Thm_GlobalTheory_SecLifts_mk_mem_ker_factor
import Theorems.Thm_GlobalTheory_SecLifts_exists_closedFibre
import Theorems.Thm_GlobalTheory_T_exists_sec_lift_alt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SecLifts
namespace GlobalTheory.SecLifts
theorem _root_.solution : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e)) → (∀ e, Flat (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → FirstCohomologyVanishes (N 0) → ∀ s₀ : LB.Sec (N 0), ∃ s : ∀ e, LB.Sec (N e), s 0 = s₀ ∧ ∀ e, (∀ z (k : (N (e + 1)).ι) (k' : (N e).ι), (β e) z ∈ (N (e + 1)).U k → z ∈ (N e).U k' → gs (β e) z _ ((s (e + 1)).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e).f k')) := by
  intro V _ _ _ Y β hβ hfl N v hN h1 s₀
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hm : IsLocalRing.maximalIdeal V = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hmem : ∀ (n : ℕ) (x : V), x ∈ IsLocalRing.maximalIdeal V ^ n ↔ ϖ ^ n ∣ x := fun n x => by
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have step : ∀ e (s' : LB.Sec (N e)), ∃ s : LB.Sec (N (e + 1)),
      ∀ z (k : (N (e + 1)).ι) (k' : (N e).ι), (β e) z ∈ (N (e + 1)).U k → z ∈ (N e).U k' →
        gs (β e) z _ (s.f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ (s'.f k') := by
    intro e s'
    obtain ⟨j, hj, w, hw⟩ := exists_closedFibre V _ Y β hβ N v hN e
    refine GlobalTheory.T.exists_sec_lift_alt _ _ _ _ _ (Ideal.Quotient.mk _ (ϖ ^ (e + 1))) (Ideal.Quotient.factor_surjective _)
      (Ideal.Quotient.factor_surjective _) ?_ ?_ ?_ ?_ _ _ _ _ _ _ j (β e) (hfl (e + 1)) hj (hβ e)
      (N (e + 1)) (N 0) w (hN (e + 1)).1 (hN 0).1 hw h1 (N e) (v e) (hN e).1 (hN e).2 s'
    · refine ⟨e + 1 + 1, ?_⟩
      have hle : RingHom.ker (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (by omega) : IsLocalRing.maximalIdeal V ^ (e + 1 + 1) ≤
          IsLocalRing.maximalIdeal V ^ (0 + 1))) ≤ (IsLocalRing.maximalIdeal V).map (Ideal.Quotient.mk _) := by
        intro x hx
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [mk_mem_ker_factor, zero_add, pow_one] at hx
        exact Ideal.mem_map_of_mem _ hx
      refine le_bot_iff.1 ((Ideal.pow_right_mono hle _).trans ?_)
      rw [← Ideal.map_pow, Ideal.map_quotient_self]
    · ext x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [mk_mem_ker_factor, hmem, Ideal.mem_span_singleton]
      refine ⟨fun h => map_dvd _ h, fun ⟨y, hy⟩ => ?_⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_mul, Ideal.Quotient.eq, hmem] at hy
      have h₁ : ϖ ^ (e + 1) ∣ x - ϖ ^ (e + 1) * y := (pow_dvd_pow ϖ (Nat.le_succ _)).trans hy
      simpa using h₁.add (dvd_mul_right (ϖ ^ (e + 1)) y)
    · rw [mk_mem_ker_factor, hmem]
      exact pow_dvd_pow ϖ (by omega)
    · intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [mk_mem_ker_factor, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hmem, hmem, zero_add, pow_one, pow_succ,
        mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)]
  choose L hL using step
  exact ⟨fun e => Nat.rec (motive := fun e => LB.Sec (N e)) s₀ L e, rfl, fun e => hL e _⟩
end GlobalTheory.SecLifts
