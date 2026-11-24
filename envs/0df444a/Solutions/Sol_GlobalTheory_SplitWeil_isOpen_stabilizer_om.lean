-- Prove2me | solution 1 for GlobalTheory.SplitWeil.isOpen_stabilizer_om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:23:29.12288+00:00
-- url     : https://prove2.me/submissions/313a3bae-52ee-4cc8-b243-d2667e5a6d8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Theorems.Thm_GlobalTheory_SplitWeil_eventually_comp_sideMul_eq
import Theorems.Thm_GlobalTheory_SplitWeil_eventually_det_trivial
import Theorems.Thm_GlobalTheory_SplitWeil_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_om_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
namespace GlobalTheory.SplitWeil
theorem _root_.solution {μ : kˣ →* ℂˣ} (hμ : IsOpen (μ.ker : Set kˣ)) {Φ : Matrix b a k → ℂ}
    (hΦ : Φ ∈ SB (Matrix b a k)) : IsOpen {gh : GL a k × GL b k | om μ gh.1 gh.2 Φ = Φ} := by
  let S : Subgroup (GL a k × GL b k) :=
    { carrier := {gh | om μ gh.1 gh.2 Φ = Φ}
      one_mem' := om_one μ Φ
      mul_mem' := fun {x y} hx hy => by
        show om μ (x.1 * y.1) (x.2 * y.2) Φ = Φ
        rw [om_mul, hy, hx]
      inv_mem' := fun {x} hx => by
        show om μ x.1⁻¹ x.2⁻¹ Φ = Φ
        conv_lhs => rw [← hx]
        rw [← om_mul, inv_mul_cancel, inv_mul_cancel, om_one] }
  refine S.isOpen_of_mem_nhds (g := 1) ?_
  have h1 := (continuous_fst.tendsto (1 : GL a k × GL b k)).eventually (eventually_det_trivial a hμ)
  have h2 := (continuous_snd.tendsto (1 : GL a k × GL b k)).eventually (eventually_det_trivial b hμ)
  filter_upwards [h1, h2, eventually_comp_sideMul_eq hΦ] with gh hg hh hs
  show om μ gh.1 gh.2 Φ = Φ
  funext x
  have := hs x
  simp only [om, hg.1, hg.2, hh.1, hh.2, Real.one_rpow, inv_one, Units.val_one, Complex.ofReal_one,
    one_mul]
  exact this
end GlobalTheory.SplitWeil
