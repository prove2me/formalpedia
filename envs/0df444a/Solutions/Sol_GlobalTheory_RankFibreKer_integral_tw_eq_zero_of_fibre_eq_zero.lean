-- Prove2me | solution 1 for GlobalTheory.RankFibreKer.integral_tw_eq_zero_of_fibre_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:51:41.843897+00:00
-- url     : https://prove2.me/submissions/d5434393-d719-4e72-9eb6-41cd647ee90c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrbitalIntegralVanishesOfFibre
import Theorems.Thm_GlobalTheory_SplitFlip_apow_ne_zero
import Theorems.Thm_GlobalTheory_SplitFlip_rank_eq_card_iff_exists_frameMatrixFirstColumnBlock


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
open GlobalTheory GlobalTheory.RankFibreKer
namespace GlobalTheory.RankFibreKer
theorem _root_.solution :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ),
    fibre ν β a b Φ = 0 → ∀ Y : Matrix (Fin a) (Fin (a + b)) k, Y.rank = a →
    ∫ g : GL (Fin a) k, Φ (g.val * Y) * tw ν (a + b) g ∂(haarVol (KO k (Fin a))) = 0 := by
  intro k _ _ _ _ _ _ ν β a b Φ hF Y hY
  obtain ⟨h, hYh⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock (k := k) finSumFinEquiv Y).1 (by rw [hY, Fintype.card_fin])
  have e := congrFun hF h
  have hC : (β (gdet h) : ℂ) * apow (gdet h) (-(a : ℂ) / 2) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
  have key : ∀ g : GL (Fin a) k, omA ν β 1 h Φ (g.val * X0 k finSumFinEquiv) * (ν (gdet g) : ℂ) *
      apow (gdet g) (((a + b : ℕ) : ℂ) / 2) = ((β (gdet h) : ℂ) * apow (gdet h) (-(a : ℂ) / 2)) *
      (Φ (g.val * Y) * tw ν (a + b) g) := by
    intro g
    have hm : g.val * Y = (((((1 : GL (Fin a) k)⁻¹).val * ((g.val * X0 k finSumFinEquiv : Matrix (Fin a) (Fin (a + b)) k))
        : Matrix (Fin a) (Fin (a + b)) k)) * (invT h).val : Matrix (Fin a) (Fin (a + b)) k) := by
      rw [inv_one, Units.val_one, Matrix.one_mul, hYh]
      exact (Matrix.mul_assoc _ _ _).symm
    rw [hm]
    simp only [omA, tw, Fintype.card_fin, map_one, inv_one, Units.val_one, apow_one]
    ring
  simp only [fibre, Pi.zero_apply, key, integral_const_mul] at e
  exact (mul_eq_zero.1 e).resolve_left hC
end GlobalTheory.RankFibreKer
