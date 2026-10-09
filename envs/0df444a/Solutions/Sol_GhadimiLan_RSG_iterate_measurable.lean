-- Prove2me | solution 1 for GhadimiLan.RSG.iterate_measurable
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-08T22:58:14.679761+00:00
-- url     : https://prove2.me/submissions/74780554-cec0-48df-8fff-3cae5c8c7e77

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
open GhadimiLan.RSG
set_option autoImplicit false

/-- Measurability of the RSG iterates (Ghadimi & Lan, arXiv:1309.5549v1, proof of Theorem 2.1,
p. 7: "the search point `x_k` is a function of the history `ξ_[k−1]`"): if the oracle `G` is
Borel and the noise `ξ_k` is `ℱ_k`-measurable for every `k ≥ 1`, then along an RSG run the
iterate `x_k` is `ℱ_{k-1}`-measurable for every `k ≥ 1` (`x_1 = x1` is constant, hence
`ℱ_0`-measurable). -/
theorem solution {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n)
    (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ)
    (hξ : ∀ k : ℕ, 1 ≤ k → Measurable[ℱ k] (ξ k))
    (γ : ℕ → ℝ) (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (k : ℕ) (hk : 1 ≤ k) :
    Measurable[ℱ (k - 1)] (x k) := by
  induction k, hk using Nat.le_induction with
  | base =>
    -- `x 1` is the constant function `x1`, hence measurable for any σ-algebra, in particular `ℱ 0`.
    have h1 : x 1 = fun _ => x1 := funext hx.1
    rw [h1]
    exact measurable_const
  | succ k hk ih =>
    -- Upgrade the induction hypothesis from `ℱ (k - 1)` to `ℱ k` (filtrations are monotone).
    have hxk : Measurable[ℱ k] (x k) := ih.mono (ℱ.mono (Nat.sub_le k 1)) le_rfl
    have hξk : Measurable[ℱ k] (ξ k) := hξ k hk
    -- The pair `ω ↦ (x k ω, ξ k ω)` is `ℱ k`-measurable, so composing with the Borel oracle
    -- `Function.uncurry G` gives `ℱ k`-measurability of `ω ↦ G (x k ω) (ξ k ω)`.
    have hpair : Measurable[ℱ k] (fun ω => (x k ω, ξ k ω)) := hxk.prodMk hξk
    have hGk : Measurable[ℱ k] (fun ω => G (x k ω) (ξ k ω)) := hG.comp hpair
    -- The recursion (2.2) expresses `x (k + 1)` through `ℱ k`-measurable maps.
    have hstep : x (k + 1) = fun ω => x k ω - γ k • G (x k ω) (ξ k ω) := funext (hx.2 k hk)
    rw [Nat.add_sub_cancel, hstep]
    exact hxk.sub (hGk.const_smul (γ k))
