-- Prove2me | solution 1 for GlobalTheory.killed_span_adjoin_finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:13:24.608271+00:00
-- url     : https://prove2.me/submissions/3b8c593e-4e71-4a3a-ac60-7336b1a1e36d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAlgebraOrbitOfAnnihilated
import Theorems.Thm_GlobalTheory_KilledFin_span_adjoin_apply_le
import Theorems.Thm_GlobalTheory_KilledFin_span_adjoin_apply_stable
import Theorems.Thm_GlobalTheory_KilledFin_commute_of_mem_adjoin
import Theorems.Thm_GlobalTheory_KilledFin_powSpan_stable_self
import Theorems.Thm_GlobalTheory_KilledFin_powSpan_stable
import Theorems.Thm_GlobalTheory_KilledFin_le_powSpan
import Theorems.Thm_GlobalTheory_KilledFin_powSpan_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open Polynomial
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Finset (Module.End ℂ V))
      (p : Module.End ℂ V → Polynomial ℂ), (∀ s ∈ T, ∀ t ∈ T, Commute s t) →
      (∀ t ∈ T, p t ≠ 0) → ∀ ψ : V, (∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0) →
      FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
        (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ∧
      Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
        (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ≤
        ∏ t ∈ T, (p t).natDegree := by
  intro V _ _ T p
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro _ _ ψ _
    have hle := GlobalTheory.KilledFin.span_adjoin_apply_le (V := V) ((∅ : Finset (Module.End ℂ V)) : Set _)
      (Submodule.span ℂ {ψ}) (by intro u hu; simp at hu) ψ (Submodule.mem_span_singleton_self ψ)
    refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
    rw [Finset.prod_empty]
    refine (Submodule.finrank_mono hle).trans ?_
    exact (finrank_span_le_card ({ψ} : Set V)).trans (by simp)
  | insert t T htT ih =>
    intro hcomm hne ψ hkillψ
    have hcommT : ∀ s ∈ T, ∀ u ∈ T, Commute s u := fun s hs u hu =>
      hcomm s (Finset.mem_insert_of_mem hs) u (Finset.mem_insert_of_mem hu)
    obtain ⟨hfd, hrk⟩ := ih hcommT (fun u hu => hne u (Finset.mem_insert_of_mem hu)) ψ
      (fun u hu => hkillψ u (Finset.mem_insert_of_mem hu))
    set N := Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
        (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V))) with hN
    have htcomm : ∀ u ∈ (T : Set (Module.End ℂ V)), Commute u t := fun u hu =>
      hcomm u (Finset.mem_insert_of_mem hu) t (Finset.mem_insert_self t T)
    have hkill : ∀ n ∈ N, aeval t (p t) n = 0 := by
      intro n hn
      induction hn using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨z, hz, rfl⟩ := hx
        have hc := GlobalTheory.KilledFin.commute_of_mem_adjoin _ t htcomm z hz (p t)
        show aeval t (p t) (z ψ) = 0
        rw [← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply,
          hkillψ t (Finset.mem_insert_self t T), map_zero]
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul c x _ hx => rw [map_smul, hx, smul_zero]
    have hq := hne t (Finset.mem_insert_self t T)
    have hK := GlobalTheory.KilledFin.powSpan_finite t (p t).natDegree N
    have hψK : ψ ∈ GlobalTheory.KilledFin.powSpan t (p t).natDegree N :=
      GlobalTheory.KilledFin.le_powSpan t (p t) hq N hkill
        (Submodule.subset_span ⟨1, Subalgebra.one_mem _, rfl⟩)
    have hle := GlobalTheory.KilledFin.span_adjoin_apply_le
      ((insert t T : Finset (Module.End ℂ V)) : Set (Module.End ℂ V))
      (GlobalTheory.KilledFin.powSpan t (p t).natDegree N) (by
        intro u hu v hv
        rw [Finset.coe_insert, Set.mem_insert_iff] at hu
        rcases hu with hut | hu
        · subst hut
          exact GlobalTheory.KilledFin.powSpan_stable_self u (p u) hq N hkill v hv
        · exact GlobalTheory.KilledFin.powSpan_stable t u _ N
            (fun n hn => GlobalTheory.KilledFin.span_adjoin_apply_stable _ ψ u
              (Algebra.subset_adjoin hu) n hn) (htcomm u hu) v hv) ψ hψK
    haveI := hK.1
    refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
    rw [Finset.prod_insert htT]
    calc _ ≤ Module.finrank ℂ (GlobalTheory.KilledFin.powSpan t (p t).natDegree N) :=
          Submodule.finrank_mono hle
      _ ≤ (p t).natDegree * Module.finrank ℂ N := hK.2
      _ ≤ _ := Nat.mul_le_mul_left _ hrk
end GlobalTheory
