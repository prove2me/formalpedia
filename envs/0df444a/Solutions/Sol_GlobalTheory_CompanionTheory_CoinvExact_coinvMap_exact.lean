-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CoinvExact.coinvMap_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:33.966818+00:00
-- url     : https://prove2.me/submissions/f7785a48-6964-4e7d-bd02-0337c50ea378

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteLengthCoinvariantsExact
import Theorems.Thm_GlobalTheory_CompanionTheory_CoinvExact_coinvMap_mk
import Theorems.Thm_GlobalTheory_CompanionTheory_CoinvExact_twRel_le_map
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CoinvExact
namespace GlobalTheory.CompanionTheory.CoinvExact
theorem _root_.solution {Γ G W V U : Type} [Group Γ] [Group G] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {τW : Representation ℂ (Γ × G) W} {τ : Representation ℂ (Γ × G) V}
    {τU : Representation ℂ (Γ × G) U} (i : τW.IntertwiningMap τ) (f : τ.IntertwiningMap τU)
    (hf : Function.Surjective f) (hif : Function.Exact i f) (ψ : Γ →* ℂˣ) :
    Function.Exact (coinvMap i ψ) (coinvMap f ψ) := by
  intro x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  constructor
  · intro h
    have hv : f v ∈ twRel (τU.comp (MonoidHom.inl Γ G)) ψ :=
      (Submodule.Quotient.mk_eq_zero _).1 h
    obtain ⟨r, hr, hrv⟩ := twRel_le_map f hf ψ hv
    have hrv' : f r = f v := hrv
    have hz : f (v - r) = 0 := by rw [map_sub, hrv', sub_self]
    obtain ⟨w, hw⟩ := (hif (v - r)).1 hz
    refine ⟨Submodule.Quotient.mk w, ?_⟩
    rw [coinvMap_mk, hw]
    exact (Submodule.Quotient.eq _).2 (by simpa using (Submodule.neg_mem _ hr))
  · rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have h0 : f (i w) = 0 := (hif (i w)).2 ⟨w, rfl⟩
    rw [← hy, coinvMap_mk, coinvMap_mk, h0]
    rfl
end GlobalTheory.CompanionTheory.CoinvExact
