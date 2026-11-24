-- Prove2me | solution 1 for GlobalTheory.JetConj.jetRel_divQuot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:19:54.532348+00:00
-- url     : https://prove2.me/submissions/c9eacc25-9175-4959-8cbc-cd809566fa5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SecondDerivSigmaProductAtZero
import Theorems.Thm_GlobalTheory_JetConj_IsSigmaLike_double
import Theorems.Thm_GlobalTheory_JetConj_IsSigmaLike_analyticAt_divQuot
import Theorems.Thm_GlobalTheory_JetConj_eventually_add_notMem
import Theorems.Thm_GlobalTheory_JetConj_IsSigmaLike_divQuot_rec
import Theorems.Thm_GlobalTheory_JetConj_IsSigmaLike_divQuot_ne
import Theorems.Thm_GlobalTheory_JetConj_JetRel_wr
import Theorems.Thm_GlobalTheory_JetConj_JetRel_congr
import Theorems.Thm_GlobalTheory_JetConj_JetRel_const
import Theorems.Thm_GlobalTheory_JetConj_JetRel_mul
import Theorems.Thm_GlobalTheory_JetConj_JetRel_of_mul
import Theorems.Thm_GlobalTheory_JetConj_JetRel_pow
import Theorems.Thm_GlobalTheory_JetConj_JetRel_sub
import Theorems.Thm_GlobalTheory_JetConj_jetRel_of_weierstrass_system
import Theorems.Thm_GlobalTheory_JetConj_pair_mul
import Theorems.Thm_GlobalTheory_JetConj_pair_natCast
import Theorems.Thm_GlobalTheory_analyticAt_weierstrassP_add
import Theorems.Thm_GlobalTheory_weierstrass_system_add_const


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PeriodPair
open GlobalTheory GlobalTheory.JetConj
variable {L : PeriodPair} {σ : ℂ → ℂ}
namespace GlobalTheory.JetConj
theorem _root_.solution {S : Subring (ℂ × ℂ)} (hS : IsFieldGraph S) {L L' : PeriodPair} {σ σ' : ℂ → ℂ}
    (H : IsSigmaLike L σ) (H' : IsSigmaLike L' σ') {u u' : ℂ} (hu : u ∉ L.lattice) (hu' : u' ∉ L'.lattice)
    (hg : (L.g₂, L'.g₂) ∈ S) (hp : (℘[L] u, ℘[L'] u') ∈ S) (hq : (℘'[L] u, ℘'[L'] u') ∈ S) (n : ℕ) :
    JetRel S (divQuot σ u n) (divQuot σ' u' n) := by
  have z0 : ∀ {L : PeriodPair} {u : ℂ}, u ∉ L.lattice → 0 + u ∉ L.lattice := fun h => by simpa using h
  have c0 : ∀ {L : PeriodPair} {σ : ℂ → ℂ} {u : ℂ}, IsSigmaLike L σ →
      (fun _ => (0 : ℂ)) =ᶠ[𝓝 0] divQuot σ u 0 := fun H =>
    .of_forall fun z => by simp [divQuot, (H.zero_iff 0).2 (zero_mem _)]
  have c1 : ∀ {L : PeriodPair} {σ : ℂ → ℂ} {u : ℂ}, IsSigmaLike L σ → u ∉ L.lattice →
      (fun _ => (1 : ℂ)) =ᶠ[𝓝 0] divQuot σ u 1 := fun H hu => by
    filter_upwards [eventually_add_notMem _ (z0 hu)] with w hw
    simp [divQuot, mt (H.zero_iff _).1 hw]
  have c2 : ∀ {L : PeriodPair} {σ : ℂ → ℂ} {u : ℂ}, IsSigmaLike L σ → u ∉ L.lattice →
      (fun z => 0 - ℘'[L] (z + u)) =ᶠ[𝓝 0] divQuot σ u 2 := @fun L σ u H hu => by
    filter_upwards [eventually_add_notMem _ (z0 hu)] with w hw
    rw [divQuot, show ((2 : ℕ) : ℂ) * w + (2 : ℕ) * u = (w + u) + (w + u) by push_cast; ring, H.double hw]
    have := mt (H.zero_iff _).1 hw
    field_simp
    ring
  have c3 : ∀ {L : PeriodPair} {u : ℂ}, u ∉ L.lattice →
      AnalyticAt ℂ (fun z => ℘'[L] (z + u)) 0 ∧
      (deriv (fun z => ℘[L] (z + u)) =ᶠ[𝓝 0] fun z => ℘'[L] (z + u)) ∧
      (deriv (fun z => ℘'[L] (z + u)) =ᶠ[𝓝 0] fun z => 6 * ℘[L] (z + u) * ℘[L] (z + u) - L.g₂ * (2 : ℂ)⁻¹) :=
    @fun L u hu => by
    refine ⟨(L.analyticOnNhd_derivWeierstrassP _ (z0 hu)).comp (f := (· + u)) (by fun_prop), ?_, ?_⟩
    · filter_upwards [weierstrass_system_add_const L u (z0 hu)] with w hw using hw.1.deriv
    · filter_upwards [weierstrass_system_add_const L u (z0 hu)] with w hw
      rw [hw.2.deriv]; ring
  have hq2 : JetRel S (fun z => ℘'[L] (z + u)) (fun z => ℘'[L'] (z + u')) :=
    jetRel_of_weierstrass_system (pair_mul hg (hS.2 _ _ (pair_natCast S 2)))
      (analyticAt_weierstrassP_add L u (z0 hu)) (analyticAt_weierstrassP_add L' u' (z0 hu'))
      (c3 hu).1 (c3 hu').1 (c3 hu).2.1 (c3 hu').2.1 (c3 hu).2.2 (c3 hu').2.2
      (by simpa using hp) (by simpa using hq)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => exact (JetRel.const S.zero_mem).congr (c0 H) (c0 H')
  | 1 => exact (JetRel.const S.one_mem).congr (c1 H hu) (c1 H' hu')
  | 2 => exact ((JetRel.const S.zero_mem).sub hq2).congr (c2 H hu) (c2 H' hu')
  | n + 3 =>
    have c4 : ∀ {L : PeriodPair} {σ : ℂ → ℂ} {u : ℂ}, IsSigmaLike L σ → u ∉ L.lattice →
        wr (divQuot σ u (n + 2)) =ᶠ[𝓝 0] fun z =>
          divQuot σ u (n + 3) z * (((n + 2 : ℕ) : ℂ) ^ 2 * divQuot σ u (n + 1) z) := fun H hu => by
      filter_upwards [eventually_add_notMem _ (z0 hu)] with w hw using (H.divQuot_rec hw (n + 1)).symm
    refine JetRel.of_mul hS (H.analyticAt_divQuot (z0 hu) _) (H'.analyticAt_divQuot (z0 hu') _)
      (((JetRel.const (pair_natCast S (n + 2))).pow 2).mul (ih (n + 1) (by omega))) ?_
      ((ih (n + 2) (by omega)).wr.congr (c4 H hu) (c4 H' hu'))
    intro e
    apply H.divQuot_ne hu (n := n + 1) (by omega)
    have hn : ((n + 2 : ℕ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : n + 2 ≠ 0))
    filter_upwards [e] with w hw using (mul_eq_zero.1 hw).resolve_left hn
end GlobalTheory.JetConj
