-- Prove2me | solution 1 for MasulloRH.prime_mass_deficit_comparable_to_omitted_zero_weight
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:04:11.228901+00:00
-- url     : https://prove2.me/submissions/49bba880-7202-443a-8410-aee86af84f82

-- New two-sided comparison using the finite-set trace splitting of marozols.
import Theorems.Thm_MasulloRH_reference_real_resolvent_sandwich
import Theorems.Thm_MasulloRH_reference_resolvent_le_half_decay_weight
import Theorems.Thm_MasulloRH_regularized_reference_mass_prime_series
import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH ArithmeticFunction
open Set Filter Topology MeasureTheory Finset

private theorem line_kernel (z : ZetaZerosInTraceStrip (1/2)) (hz : z.val.re = 1/2) :
    (zeroResolventTerm (1/2) 3 z).re = (analyticOrderNatAt riemannZeta z.val:ℝ) *
      ((z.val.im^2 - 5) / (2 * (z.val.im^2 + 25/4) * (z.val.im^2+4))) := by
  unfold zeroResolventTerm
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
  congr 1
  simp only [one_div,Complex.sub_re,Complex.inv_re,Complex.normSq_apply,Complex.sub_im]
  norm_num [hz,pow_two,Complex.div_ofNat_re,Complex.div_ofNat_im]
  field_simp
  ring

theorem solution (F : Finset (ZetaZerosInTraceStrip (1/2))) (hon : ∀ z ∈ F, z.val.re = 1/2) :
    let D := Real.log 2/2 + Real.pi/4 - 37/30 +
      (∑' j : ℕ, (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ))) -
      ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
        ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))
    let T := ∑' z : ZetaZerosInTraceStrip (1/2), if z ∈ F then 0 else zeroDecayWeight (1/2) z
    T/4 ≤ D ∧ D ≤ T/2 := by
  classical
  dsimp only
  let C := Real.log 2/2 + Real.pi/4-37/30
  let A := (zetaLogDeriv 3).re - (zetaLogDeriv (5/2)+regularizedArch 3-regularizedPolar 3).re
  let f (j : ℕ) := ArithmeticFunction.vonMangoldt j / (j:ℝ)^(5/2:ℝ) -
    ArithmeticFunction.vonMangoldt j / (j:ℝ)^(3:ℝ)
  let r := zeroResolventTerm (1/2) 3
  let k (z : ZetaZerosInTraceStrip (1/2)) := (r z).re
  let w := zeroDecayWeight (1/2)
  have hw := weighted_zero_summability (1/2) (by norm_num)
  have hs : Summable r := hw.of_norm_bounded (fun z => (reference_resolvent_le_half_decay_weight z).trans (by
    have h : 0 ≤ zeroDecayWeight (1/2) z := by unfold zeroDecayWeight; positivity
    change zeroDecayWeight (1/2) z / 2 ≤ zeroDecayWeight (1/2) z
    linarith))
  have hk : Summable k := (Complex.hasSum_re hs.hasSum).summable
  have hsum : (∑' z,k z) = A := by
    dsimp only [A]
    rw [←regularized_initial_identity_full_strip (3:ℂ) (by norm_num)]
    change _ = ((_ + ∑' z,r z).re-_)
    rw [Complex.add_re,add_sub_cancel_left,Complex.re_tsum hs]
  let E : Set (ZetaZerosInTraceStrip (1/2)) := (F : Set _)ᶜ
  have hsplit : (∑ z ∈ F,k z)+(∑' z,E.indicator k z) = A := by
    rw [←_root_.tsum_subtype]
    exact (hk.sum_add_tsum_compl (s:=F)).trans hsum
  have hpt (z) : E.indicator w z / 4 ≤ E.indicator k z ∧ E.indicator k z ≤ E.indicator w z / 2 := by
    by_cases h : z ∈ E
    · simpa only [Set.indicator_of_mem h] using reference_real_resolvent_sandwich z
    · simp [Set.indicator_of_notMem h]
  have hlow := (hw.indicator E).tsum_le_tsum
    (fun z => show E.indicator w z ≤ 4*E.indicator k z by linarith [(hpt z).1]) ((hk.indicator E).mul_left (4:ℝ))
  have hupp := ((hk.indicator E).mul_left (2:ℝ)).tsum_le_tsum
    (fun z => show 2*E.indicator k z ≤ E.indicator w z by linarith [(hpt z).2]) (hw.indicator E)
  rw [tsum_mul_left] at hlow hupp
  have hrew (z) : (if z ∈ F then 0 else zeroDecayWeight (1/2) z) = E.indicator w z := by
    by_cases h : z ∈ F <;> simp [E,w,Set.indicator_apply,h]
  have hm : (∑ z ∈ F,k z) = _ := Finset.sum_congr rfl fun z hz => line_kernel z (hon z hz)
  have hpri := regularized_reference_mass_prime_series
  have hp : (∑' j,f j) = A-C := by
    rw [show (∑' j,f j) = _ from hpri.tsum_eq]
    dsimp only [A,C]
    ring
  simp_rw [hrew]
  change _ ≤ C+(∑' j,f j)-_ ∧ C+(∑' j,f j)-_ ≤ _
  rw [←hm,hp]
  constructor <;> linarith only [hlow,hupp,hsplit]
