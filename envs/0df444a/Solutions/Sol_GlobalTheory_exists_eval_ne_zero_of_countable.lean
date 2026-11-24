-- Prove2me | solution 1 for GlobalTheory.exists_eval_ne_zero_of_countable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:41:34.616749+00:00
-- url     : https://prove2.me/submissions/d1eeb912-fe9b-4c16-9496-4de052e2c157

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsAlgHomNeZeroOfCountable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {σ : Type} [Finite σ] (T : Set (MvPolynomial σ ℂ))
    (hT : T.Countable) (h0 : (0 : MvPolynomial σ ℂ) ∉ T) :
    ∃ c : σ → ℂ, ∀ p ∈ T, MvPolynomial.eval c p ≠ 0 := by
  classical
  have := Fintype.ofFinite σ
  have hd : Dense (⋂ p ∈ T, {c : σ → ℂ | MvPolynomial.eval c p ≠ 0}) := by
    refine dense_biInter_of_isOpen (fun p _ => ?_) hT (fun p hp => ?_)
    · exact isOpen_ne_fun (MvPolynomial.continuous_eval p) continuous_const
    · intro c
      by_contra hc
      have hev : (fun c : σ → ℂ => MvPolynomial.eval c p) =ᶠ[nhds c] 0 := by
        have h1 : (closure {c : σ → ℂ | MvPolynomial.eval c p ≠ 0})ᶜ ∈ nhds c :=
          isClosed_closure.isOpen_compl.mem_nhds hc
        filter_upwards [h1] with x hx
        by_contra hx'
        exact hx (subset_closure hx')
      have hz := (AnalyticOnNhd.eval_mvPolynomial p).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ c) hev
      have : p = 0 := MvPolynomial.funext fun x => by
        simpa using hz (Set.mem_univ x)
      exact h0 (this ▸ hp)
  obtain ⟨c, hc⟩ := hd.nonempty
  exact ⟨c, fun p hp => Set.mem_iInter₂.1 hc p hp⟩
end GlobalTheory
