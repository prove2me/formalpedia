-- Prove2me | solution 1 for GlobalTheory.TensHead.exists_adjoin_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:32:44.840046+00:00
-- url     : https://prove2.me/submissions/9be9d764-4b25-4957-9dec-8a26c1818cce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DixmierSchurOfRankLeAleph0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleTensorProductOperatorStableCountable
import Theorems.Thm_GlobalTheory_dixmier_schur_of_rank_le_aleph0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TensHead
namespace GlobalTheory.TensHead
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (A : Set (Module.End ℂ V)) (hrank : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hA : ∀ U : Submodule ℂ V, Stab A U → U = ⊥ ∨ U = ⊤) (p : Module.End ℂ V) (s : Finset V) :
    ∃ r ∈ Algebra.adjoin ℂ A, ∀ m ∈ s, p m = r m := by
  set R := Algebra.adjoin ℂ A with hR
  haveI : IsSimpleModule R V := by
    rw [isSimpleModule_iff]
    refine { eq_bot_or_eq_top := fun N => ?_ }
    have h := hA (N.restrictScalars ℂ) (fun g hg x hx =>
      N.smul_mem (⟨g, Algebra.subset_adjoin hg⟩ : R) hx)
    rcases h with h | h
    · left; exact (Submodule.restrictScalars_eq_bot_iff ℂ R V).1 h
    · right; exact (Submodule.restrictScalars_eq_top_iff ℂ R V).1 h
  have hsc : ∀ φ : Module.End R V, ∃ c : ℂ, ∀ x, φ x = c • x := by
    intro φ
    obtain ⟨c, hc⟩ := GlobalTheory.dixmier_schur_of_rank_le_aleph0 V A (fun g => g.1)
      (LinearMap.restrictScalars ℂ φ) inferInstance hrank
      (fun N hN => hA N (fun g hg x hx => hN ⟨g, hg⟩ x hx))
      (fun g => LinearMap.ext fun x =>
        φ.map_smul (⟨g.1, Algebra.subset_adjoin g.2⟩ : R) x)
    exact ⟨c, fun x => LinearMap.congr_fun hc x⟩
  let f : Module.End (Module.End R V) V :=
    { toFun := p
      map_add' := p.map_add
      map_smul' := fun φ x => by
        obtain ⟨c, hc⟩ := hsc φ
        change p (φ x) = φ (p x)
        rw [hc, hc, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density f s
  exact ⟨r.1, r.2, hr⟩
end GlobalTheory.TensHead
