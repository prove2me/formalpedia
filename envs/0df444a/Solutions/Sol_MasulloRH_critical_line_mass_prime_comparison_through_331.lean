-- Prove2me | solution 1 for MasulloRH.critical_line_mass_prime_comparison_through_331
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:57:56.922175+00:00
-- url     : https://prove2.me/submissions/82959871-07a2-4289-8751-acaa6a869184

-- Adapts the finite-zero witness construction by marozols (Prove2Me submission
-- 02bdcd00-bd8f-4001-a129-1bc499218bd8) to a uniform two-sided error.
import Theorems.Thm_MasulloRH_reference_resolvent_le_half_decay_weight
import Theorems.Thm_MasulloRH_certified_prime_tail_from_331
import Theorems.Thm_MasulloRH_uniform_prime_mass_certificate_at_height_99998
import Theorems.Thm_MasulloRH_certified_height_99998_reference_budget
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_regularized_reference_mass_prime_series
import Theorems.Thm_MasulloRH_zero_decay_tail_at_real_lattice
import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
import Mathlib

open Set Filter Topology MeasureTheory ArithmeticFunction Finset
open MasulloRH

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


theorem solution :
    let a := fun j : ℕ => vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ)
    let C := Real.log 2/2 + Real.pi/4 - 37/30
    ∃ F : Finset (ZetaZerosInTraceStrip (1/2)),
      (∀ z, z ∈ F ↔ |z.val.im| ≤ 199997/2) ∧ (∀ z ∈ F, z.val.re = 1/2) ∧
      let M := ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
        ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))
      |C + (∑' j, a j) - M| ≤ 7/80000 ∧
      ∀ N : ℕ, N ≤ 331 → C + (∑ j ∈ Finset.range N, a j) ≤ M := by
  classical
  dsimp only
  let n : ℕ := 49998
  let H : ℝ := 5/2+2*n
  obtain ⟨hcover,hbudget⟩ := certified_height_99998_reference_budget
  let C := Real.log 2/2 + Real.pi/4-37/30
  let A := (zetaLogDeriv 3).re - (zetaLogDeriv (5/2)+regularizedArch 3-regularizedPolar 3).re
  let f (j : ℕ) := ArithmeticFunction.vonMangoldt j / (j:ℝ)^(5/2:ℝ) -
    ArithmeticFunction.vonMangoldt j / (j:ℝ)^(3:ℝ)
  have hpos (j : ℕ) : 0 ≤ f j := by
    rcases eq_or_ne j 0 with rfl | hj
    · simp [f]
    have h1 : 1 ≤ (j:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num))
  obtain ⟨F,hFc,hon,_⟩ := uniform_prime_mass_certificate_at_height_99998
  have hF (z) : z ∈ F ↔ |z.val.im| ≤ H := by
    rw [show H = 199997/2 by norm_num [H,n]]
    exact hFc z
  refine ⟨F,hFc,hon,?_⟩
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
  have hpoint (z) : |E.indicator k z| ≤ E.indicator w z / 2 := by
    by_cases hz : z ∈ E
    · rw [Set.indicator_of_mem hz,Set.indicator_of_mem hz]
      exact (Complex.abs_re_le_norm _).trans (reference_resolvent_le_half_decay_weight z)
    · simp [Set.indicator_of_notMem hz]
  have htail := ((hk.indicator E).mul_left (2:ℝ)).tsum_le_tsum
    (fun z => show 2*E.indicator k z ≤ E.indicator w z by linarith [(abs_le.mp (hpoint z)).2]) (hw.indicator E)
  rw [tsum_mul_left] at htail
  have hweight : (∑' z,E.indicator w z) ≤ (7/40000:ℝ) := by
    have hrewrite (z : ZetaZerosInTraceStrip (1/2)) : E.indicator w z =
        if H < |z.val.im| then zeroDecayWeight (1/2) z else 0 := by
      have hz : z ∈ E ↔ H < |z.val.im| := by change (¬z∈F) ↔ _; rw [hF,not_le]
      simp only [Set.indicator_apply,hz,w]
    simp_rw [hrewrite]
    apply (zero_decay_tail_at_real_lattice n).trans
    exact hbudget.trans (by norm_num)
  have hlo := ((hk.indicator E).mul_left (-2:ℝ)).tsum_le_tsum
    (fun z => show -2*E.indicator k z ≤ E.indicator w z by linarith [(abs_le.mp (hpoint z)).1]) (hw.indicator E)
  rw [tsum_mul_left] at hlo
  have hm : (∑ z ∈ F,k z) = _ := Finset.sum_congr rfl fun z hz => line_kernel z (hon z hz)
  have hpri := regularized_reference_mass_prime_series
  have hp : (∑' j,f j) = A-C := by
    rw [show (∑' j,f j) = _ from hpri.tsum_eq]
    dsimp only [A,C]
    ring
  constructor
  · change |C+(∑' j,f j)-_| ≤ _
    rw [←hm,abs_le]
    constructor <;> linarith only [hsplit,htail,hlo,hweight,hp]
  · intro N hN
    obtain ⟨P,hP,hval⟩ := certified_prime_tail_from_331
    have hdis : Disjoint (Finset.range N) P := Finset.disjoint_left.mpr
      (fun j hj h => (Nat.not_lt_of_ge (hN.trans (hP j h).2.1)) (Finset.mem_range.mp hj))
    have hpN : (∑ j ∈ Finset.range N,f j)+(∑ j ∈ P,f j) ≤ ∑' j,f j := by
      rw [←Finset.sum_union hdis]
      exact hpri.summable.sum_le_tsum _ (fun j _ => hpos j)
    change (88412/1000000000:ℝ) ≤ ∑ j ∈ P,f j at hval
    change C + (∑ j ∈ Finset.range N,f j) ≤ _
    rw [←hm]
    linarith only [hpN,hp,hsplit,htail,hweight,hval]
