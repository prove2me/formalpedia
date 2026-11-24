-- Prove2me | solution 1 for GlobalTheory.SplitWeil.eventually_comp_sideMul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:56:02.755288+00:00
-- url     : https://prove2.me/submissions/ddc6564f-0c5b-4c67-84b2-e51ffd23bdd1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq

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
theorem _root_.solution {Φ : Matrix b a k → ℂ} (hΦ : Φ ∈ SB (Matrix b a k)) :
    ∀ᶠ gh : GL a k × GL b k in 𝓝 1, ∀ x, Φ (sideMul gh.1 gh.2 x) = Φ x := by
  have hc : Continuous fun q : (GL a k × GL b k) × Matrix b a k => sideMul q.1.1 q.1.2 q.2 := by
    show Continuous fun q : (GL a k × GL b k) × Matrix b a k =>
      (q.1.2⁻¹ : GL b k).val * q.2 * q.1.1.val
    exact ((Units.continuous_coe_inv.comp (continuous_snd.comp continuous_fst)).matrix_mul
      continuous_snd).matrix_mul (Units.continuous_val.comp (continuous_fst.comp continuous_fst))
  have h1 : ∀ᶠ gh : GL a k × GL b k in 𝓝 1, ∀ x ∈ tsupport Φ, Φ (sideMul gh.1 gh.2 x) = Φ x := by
    refine IsCompact.eventually_forall_of_forall_eventually hΦ.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : (GL a k × GL b k) × Matrix b a k =>
        (Φ (sideMul q.1.1 q.1.2 q.2), Φ q.2) :=
      (hΦ.1.comp_continuous hc).prodMk (hΦ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (1, x)] with q hq
    simp only [Prod.mk.injEq] at hq
    rw [hq.1, hq.2]
    congr 1
    show ((1 : GL b k)⁻¹ : GL b k).val * x * (1 : GL a k).val = x
    simp
  have h2 : ∀ᶠ gh : GL a k × GL b k in 𝓝 1,
      ∀ x ∈ tsupport Φ, Φ (sideMul gh⁻¹.1 gh⁻¹.2 x) = Φ x := by
    have ht : Filter.Tendsto (fun gh : GL a k × GL b k => gh⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv (G := GL a k × GL b k)).tendsto 1
    exact ht.eventually h1
  filter_upwards [h1, h2] with gh hs hs' x
  by_cases hx : x ∈ tsupport Φ
  · exact hs x hx
  by_cases hx' : sideMul gh.1 gh.2 x ∈ tsupport Φ
  · rw [← hs' _ hx']
    congr 1
    have := (sideMul gh.1 gh.2).left_inv x
    refine Eq.trans ?_ this
    show (gh.2⁻¹⁻¹ : GL b k).val * sideMul gh.1 gh.2 x * (gh.1⁻¹ : GL a k).val = _
    rw [inv_inv]
    rfl
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
end GlobalTheory.SplitWeil
