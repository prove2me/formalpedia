-- Prove2me | solution 1 for MasulloRH.off_line_mass_is_glb_of_finite_critical_line_deficits
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:24:47.229778+00:00
-- url     : https://prove2.me/submissions/3b95bb30-f037-4594-ac11-fda3955dd6c1

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

theorem solution :
    let C := Real.log 2/2 + Real.pi/4 - 37/30 +
      (∑' j : ℕ, (vonMangoldt j/(j:ℝ)^(5/2:ℝ) - vonMangoldt j/(j:ℝ)^(3:ℝ)))
    let Z := {z : ZetaZerosInTraceStrip (1/2) // z.val.re = 1/2}
    let M := fun F : Finset Z => ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val.val:ℝ) *
      ((z.val.val.im^2-5)/(2*(z.val.val.im^2+25/4)*(z.val.val.im^2+4)))
    IsGLB (Set.range (fun F => C - M F))
      (∑' z : {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2},
        (zeroResolventTerm (1/2) 3 z.val).re) := by
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
  have hpri := regularized_reference_mass_prime_series
  have hp : (∑' j,f j) = A-C := by
    rw [show (∑' j,f j) = _ from hpri.tsum_eq]
    dsimp only [A,C]
    ring
  let S : Set (ZetaZerosInTraceStrip (1/2)) := {z | z.val.re = 1/2}
  let D := ∑' z : ↥(Sᶜ), k z.val
  let l := fun z : S => k z.val
  have hl : Summable l := hk.subtype S
  have hsplit : (∑' z,l z)+D = A := (hk.tsum_subtype_add_tsum_subtype_compl S).trans hsum
  have hnn (z : S) : 0 ≤ l z := by
    have hwz : 0 ≤ zeroDecayWeight (1/2) z.val := by unfold zeroDecayWeight; positivity
    exact (by linarith : 0 ≤ zeroDecayWeight (1/2) z.val /4).trans (reference_real_resolvent_sandwich z.val).1
  let P := C + ∑' j,f j
  have hp' : P = A := by dsimp [P]; linarith
  have hglb : IsGLB (Set.range fun F : Finset S => P - ∑ z ∈ F,l z) D := by
    constructor
    · rintro _ ⟨F,rfl⟩
      have h := hl.sum_le_tsum F (fun z _ => hnn z)
      linarith only [hp',hsplit,h]
    · intro b hb
      have htt : Tendsto (fun F : Finset S => P - ∑ z ∈ F,l z) atTop (𝓝 (P-(∑' z,l z))) :=
        tendsto_const_nhds.sub hl.hasSum
      have hd : P-(∑' z,l z) = D := by linarith
      rw [hd] at htt
      exact ge_of_tendsto' htt (fun F => hb (Set.mem_range_self F))
  have heq (z : S) : l z = (analyticOrderNatAt riemannZeta z.val.val:ℝ) *
      ((z.val.val.im^2-5)/(2*(z.val.val.im^2+25/4)*(z.val.val.im^2+4))) := line_kernel z.val z.property
  simp_rw [heq] at hglb
  exact hglb
