-- Prove2me | solution 1 for GlobalTheory.UnitPairNorm.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:24:31.837275+00:00
-- url     : https://prove2.me/submissions/f3508be4-5e28-40c7-8e47-ed16083ca03b

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitNorm
import Theorems.Thm_GlobalTheory_UnitPairNorm_main_ind

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitPairNorm
open Module
namespace GlobalTheory.UnitPairNorm
theorem _root_.solution : ∀ (K : GlobalTheory.UnitLemma.UQ), (∀ (u : (GlobalTheory.UnitLemma.UQ.O K)ˣ), (GlobalTheory.UnitLemma.UQ.c K : GlobalTheory.UnitLemma.UQ.E K → GlobalTheory.UnitLemma.UQ.E K) ((Algebra.algebraMap (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) : GlobalTheory.UnitLemma.UQ.O K → GlobalTheory.UnitLemma.UQ.E K) (↑u : GlobalTheory.UnitLemma.UQ.O K)) = (Algebra.algebraMap (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) : GlobalTheory.UnitLemma.UQ.O K → GlobalTheory.UnitLemma.UQ.E K) (↑u : GlobalTheory.UnitLemma.UQ.O K) → ∃ (z : (GlobalTheory.UnitLemma.UQ.O K)ˣ), (Algebra.algebraMap (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) : GlobalTheory.UnitLemma.UQ.O K → GlobalTheory.UnitLemma.UQ.E K) (↑u : GlobalTheory.UnitLemma.UQ.O K) = (Algebra.algebraMap (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) : GlobalTheory.UnitLemma.UQ.O K → GlobalTheory.UnitLemma.UQ.E K) (↑z : GlobalTheory.UnitLemma.UQ.O K) * (GlobalTheory.UnitLemma.UQ.c K : GlobalTheory.UnitLemma.UQ.E K → GlobalTheory.UnitLemma.UQ.E K) ((Algebra.algebraMap (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) : GlobalTheory.UnitLemma.UQ.O K → GlobalTheory.UnitLemma.UQ.E K) (↑z : GlobalTheory.UnitLemma.UQ.O K))) → (∃ (z : GlobalTheory.UnitLemma.UQ.O K), (Algebra.algebraMap (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) : GlobalTheory.UnitLemma.UQ.O K → GlobalTheory.UnitLemma.UQ.E K) z + (GlobalTheory.UnitLemma.UQ.c K : GlobalTheory.UnitLemma.UQ.E K → GlobalTheory.UnitLemma.UQ.E K) ((Algebra.algebraMap (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) : GlobalTheory.UnitLemma.UQ.O K → GlobalTheory.UnitLemma.UQ.E K) z) = (1 : GlobalTheory.UnitLemma.UQ.E K)) → ∀ (n : ℕ) (V : Type) [inst : AddCommGroup V] [inst_1 : Module (GlobalTheory.UnitLemma.UQ.E K) V] [inst_2 : Module (GlobalTheory.UnitLemma.UQ.O K) V] [IsScalarTower (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) V] [Module.Finite (GlobalTheory.UnitLemma.UQ.E K) V] (h : V → V → GlobalTheory.UnitLemma.UQ.E K), Module.finrank (GlobalTheory.UnitLemma.UQ.E K) V = n → (∀ (x y z : V), h (x + y) z = h x z + h y z) → (∀ (c : GlobalTheory.UnitLemma.UQ.E K) (x z : V), h (c • x) z = c * h x z) → (∀ (x y : V), h y x = (GlobalTheory.UnitLemma.UQ.c K : GlobalTheory.UnitLemma.UQ.E K → GlobalTheory.UnitLemma.UQ.E K) (h x y)) → ∀ (L : Submodule (GlobalTheory.UnitLemma.UQ.O K) V), Submodule.FG L → Submodule.span (GlobalTheory.UnitLemma.UQ.E K) (↑L : Set V) = ⊤ → (∀ (y : V), y ∈ L ↔ ∀ z ∈ L, h y z ∈ RingHom.range (Algebra.algebraMap (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K))) → ∃ (m : ℕ) (v : Fin m → V), (∀ (i j : Fin m), h (v i) (v j) = if i = j then (1 : GlobalTheory.UnitLemma.UQ.E K) else (0 : GlobalTheory.UnitLemma.UQ.E K)) ∧ Submodule.span (GlobalTheory.UnitLemma.UQ.O K) (Set.range v) = L := by
  intro K hnorm hz n V _ _ _ _ _ h hn hadd hsmul hsym L hfg hsp hdual
  exact main_ind K.c K.c_c K.c_int hnorm hz h hadd hsmul hsym n ⊤ (by rw [finrank_top]; exact hn)
    L hfg hsp (fun y _ => hdual y)
end GlobalTheory.UnitPairNorm
