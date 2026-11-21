-- Prove2me | solution 1 for MasulloRH.approximate_prime_certificate_verifies_a_zero_height
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:08:11.104398+00:00
-- url     : https://prove2.me/submissions/a6503c39-bdb1-42b6-9da3-be1d6bcbf27b

-- New converse height certificate; the analytic-order positivity proof is due to marozols.
import Theorems.Thm_MasulloRH_approximate_prime_certificate_bounds_missing_zero_mass
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH ArithmeticFunction
open Set Filter Topology

private theorem multiplicity_pos (ρ : ZetaZerosInTraceStrip (1/2)) :
    0 < analyticOrderNatAt riemannZeta ρ.val := by
  have h1 : ρ.val ≠ 1 := fun h => by
    have hr := congrArg Complex.re h
    simp only [Complex.one_re] at hr
    linarith [ρ.prop.2.2.1]
  have hA := analyticOn_riemannZeta
  have htwo : analyticOrderAt riemannZeta 2 = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
  have hfin := hA.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1:ℂ)).isPreconnected
    (show (2:ℂ) ∈ ({1}:Set ℂ)ᶜ by norm_num) h1 (htwo ▸ ENat.zero_ne_top)
  apply Nat.pos_of_ne_zero
  unfold analyticOrderNatAt
  exact fun h => (ENat.toNat_eq_zero.mp h).elim
    ((hA _ h1).analyticOrderAt_ne_zero.mpr ρ.prop.1) hfin


theorem solution (N : ℕ) (hN : 2 ≤ N) (ε : ℝ)
    (F : Finset (ZetaZerosInTraceStrip (1/2))) (hF : ∀ z ∈ F, z.val.re = 1/2)
    (hc : Real.log 2/2 + Real.pi/4 - 37/30 +
      (∑ j ∈ Finset.range (N+1), (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ))) ≤
        (∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
          ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))) + ε) (H : ℝ)
    (hsmall : 4*(ε + ((2/3)*Real.log N+4/9)*(N:ℝ)^(-(3/2):ℝ))*(1+H^2) < 1) :
    ∀ z : ZetaZerosInTraceStrip (1/2), |z.val.im| ≤ H → z ∈ F ∧ z.val.re = 1/2 := by
  classical
  intro z hz
  suffices hm : z ∈ F from ⟨hm,hF z hm⟩
  by_contra hnot
  let w := fun u : ZetaZerosInTraceStrip (1/2) => if u ∈ F then 0 else zeroDecayWeight (1/2) u
  have hsum : Summable w := by
    have h := (weighted_zero_summability (1/2) (by norm_num)).indicator (↑F : Set _)ᶜ
    apply h.congr
    intro u
    by_cases h : u ∈ F <;> simp [w,Set.indicator_apply,h]
  have hnon (u) : 0 ≤ w u := by
    dsimp [w]; split_ifs <;> first | exact le_rfl | change 0 ≤ (_:ℝ)/(1+u.val.im^2); positivity
  have hmass := approximate_prime_certificate_bounds_missing_zero_mass N hN ε F hF hc
  have hw : w z ≤ ∑' u,w u := hsum.le_tsum z (fun u _ => hnon u)
  have hzsq : z.val.im^2 ≤ H^2 := by
    nlinarith [sq_abs z.val.im,mul_self_le_mul_self (abs_nonneg _) hz]
  have hm : (1:ℝ) ≤ analyticOrderNatAt riemannZeta z.val := by exact_mod_cast multiplicity_pos z
  have hl : 1/(1+H^2) ≤ w z := by
    rw [show w z = zeroDecayWeight (1/2) z by simp [w,hnot]]
    change _ ≤ (_:ℝ)/(1+z.val.im^2)
    exact (one_div_le_one_div_of_le (by positivity) (by linarith only [hzsq])).trans
      (div_le_div_of_nonneg_right hm (by positivity))
  exact (not_le_of_gt hsmall) ((div_le_iff₀ (by positivity : 0 < 1+H^2)).mp (hl.trans (hw.trans hmass)))
