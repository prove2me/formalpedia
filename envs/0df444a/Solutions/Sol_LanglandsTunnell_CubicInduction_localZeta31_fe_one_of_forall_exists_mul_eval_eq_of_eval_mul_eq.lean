-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.localZeta31_fe_one_of_forall_exists_mul_eval_eq_of_eval_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/425174a4-a0e0-5ca9-9e71-c189d595e487

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_localZeta31_fe_one_of_forall_exists_mul_eval_eq_of_eval_mul_eq

set_option autoImplicit false

section

open Polynomial

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove dualWhittakerFn3 weylPrime3 transposeInv3 LocalGL3"
namespace PushRegion
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Roots

private theorem exists_pos_forall_eval_ne_zero_of_norm_lt (p : ℂ[X]) (hp : p ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℂ, x ≠ 0 → ‖x‖ < δ → p.eval x ≠ 0 := by
  classical
  set T : Finset ℂ := p.roots.toFinset.filter fun r : ℂ => r ≠ 0
  have hmemT : ∀ x : ℂ, x ≠ 0 → p.eval x = 0 → x ∈ T := fun x hx hev =>
    Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 ((mem_roots hp).2 hev), hx⟩
  by_cases hne : T.Nonempty
  · obtain ⟨r₀, hr₀, hmin⟩ := T.exists_min_image (fun r : ℂ => ‖r‖) hne
    have hr₀ne : r₀ ≠ 0 := (Finset.mem_filter.1 hr₀).2
    refine ⟨‖r₀‖, norm_pos_iff.2 hr₀ne, fun x hx hxlt hev => ?_⟩
    exact absurd (hmin x (hmemT x hx hev)) (not_le.2 hxlt)
  · exact ⟨1, one_pos, fun x hx _ hev => hne ⟨x, hmemT x hx hev⟩⟩

private theorem exists_forall_eval_ne_zero_of_lt_norm (p : ℂ[X]) (hp : p ≠ 0) :
    ∃ M : ℝ, ∀ x : ℂ, M < ‖x‖ → p.eval x ≠ 0 := by
  classical
  refine ⟨∑ r ∈ p.roots.toFinset, ‖r‖, fun x hx hev => ?_⟩
  have hmem : x ∈ p.roots.toFinset := Multiset.mem_toFinset.2 ((mem_roots hp).2 hev)
  have hle : ‖x‖ ≤ ∑ r ∈ p.roots.toFinset, ‖r‖ := Finset.single_le_sum (fun r _ => norm_nonneg r) hmem
  exact absurd hle (not_le.2 hx)

end Roots

section Pushes

variable {q : ℕ}

private theorem norm_natCast_cpow_neg (hq : 0 < q) (z : ℂ) : ‖(q : ℂ) ^ (-z)‖ = (q : ℝ) ^ (-z.re) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [show (q : ℂ) = ((q : ℝ) : ℂ) from (Complex.ofReal_natCast q).symm,
    Complex.norm_cpow_eq_rpow_re_of_pos hq', Complex.neg_re]

private theorem natCast_cpow_neg_ne_zero (hq : 0 < q) (z : ℂ) : (q : ℂ) ^ (-z) ≠ 0 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Ne, ← norm_eq_zero, norm_natCast_cpow_neg hq z]
  exact (Real.rpow_pos_of_pos hq' _).ne'

private theorem exists_forall_eval_natCast_cpow_neg_ne_zero_of_re_gt (hq : 2 ≤ q) (p : ℂ[X]) (hp : p ≠ 0) :
    ∃ σ : ℝ, ∀ z : ℂ, σ < z.re → p.eval ((q : ℂ) ^ (-z)) ≠ 0 := by
  obtain ⟨δ, hδ, hδ'⟩ := exists_pos_forall_eval_ne_zero_of_norm_lt p hp
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  have hq0 : 0 < q := by omega
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  refine ⟨(k : ℝ), fun z hz => hδ' _ (natCast_cpow_neg_ne_zero hq0 z) ?_⟩
  rw [norm_natCast_cpow_neg hq0]
  calc (q : ℝ) ^ (-z.re) ≤ (q : ℝ) ^ (-(k : ℝ)) := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    _ = ((q : ℝ) ^ k)⁻¹ := by rw [Real.rpow_neg (by linarith), Real.rpow_natCast]
    _ ≤ ((2 : ℝ) ^ k)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hq2 k)
    _ = (1 / 2 : ℝ) ^ k := by rw [one_div, inv_pow]
    _ < δ := hk

private theorem exists_forall_eval_natCast_cpow_neg_ne_zero_of_one_sub_re_gt (hq : 2 ≤ q) (p : ℂ[X]) (hp : p ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < (1 - s).re → p.eval ((q : ℂ) ^ (-s)) ≠ 0 := by
  obtain ⟨M, hM⟩ := exists_forall_eval_ne_zero_of_lt_norm p hp
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt M (by norm_num : (1 : ℝ) < 2)
  have hq0 : 0 < q := by omega
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  refine ⟨(k : ℝ) + 1, fun s hs => hM _ ?_⟩
  rw [norm_natCast_cpow_neg hq0]
  have hre : (k : ℝ) ≤ -s.re := by
    rw [Complex.sub_re, Complex.one_re] at hs
    linarith
  calc M < (2 : ℝ) ^ k := hk
    _ ≤ (q : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) hq2 k
    _ = (q : ℝ) ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (q : ℝ) ^ (-s.re) := Real.rpow_le_rpow_of_exponent_le hq1 hre

end Pushes

end LanglandsTunnell.CubicInduction.PushRegion

end

section

open Polynomial

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove dualWhittakerFn3 weylPrime3 transposeInv3 LocalGL3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Monotone

variable (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
variable {mT : MeasurableSpace (v.adicCompletion ℚ)ˣ} {mA : MeasurableSpace (v.adicCompletion ℚ)}

namespace IsLocalZeta30ConvergentAbove
private theorem _root_.LanglandsTunnell.CubicInduction.IsLocalZeta30ConvergentAbove.of_le {μ : MeasureTheory.Measure (v.adicCompletion ℚ)ˣ}
    {W : LocalGL3 v → ℂ} {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {g : LocalGL3 v} {σ σ' : ℝ} :
    IsLocalZeta30ConvergentAbove v μ W χ g σ → σ ≤ σ' → IsLocalZeta30ConvergentAbove v μ W χ g σ' :=
  fun h hσ s hs => h s (lt_of_le_of_lt hσ hs)

end IsLocalZeta30ConvergentAbove
p2m_export "LanglandsTunnell.CubicInduction" "IsLocalZeta30ConvergentAbove.of_le"
namespace IsLocalZeta31ConvergentAbove
private theorem _root_.LanglandsTunnell.CubicInduction.IsLocalZeta31ConvergentAbove.of_le {μ : MeasureTheory.Measure (v.adicCompletion ℚ)ˣ}
    {ν : MeasureTheory.Measure (v.adicCompletion ℚ)} {W : LocalGL3 v → ℂ} {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    {g : LocalGL3 v} {σ σ' : ℝ} :
    IsLocalZeta31ConvergentAbove v μ ν W χ g σ → σ ≤ σ' → IsLocalZeta31ConvergentAbove v μ ν W χ g σ' :=
  fun h hσ s hs => h s (lt_of_le_of_lt hσ hs)

end IsLocalZeta31ConvergentAbove
p2m_export "LanglandsTunnell.CubicInduction" "IsLocalZeta31ConvergentAbove.of_le"
end Monotone

section Algebra

open PushRegion

private theorem exists_closed_form (q : ℕ) (E Q₁ Q₂ : ℂ[X]) (hQ₂ : Q₂ ≠ 0) (n : ℤ) :
    ∃ (Q R : ℂ[X]) (k : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
      E.eval ((q : ℂ) ^ (-s)) * Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((n : ℂ) * s) / Q₂.eval ((q : ℂ) ^ (-s)) *
          R.eval ((q : ℂ) ^ (-s)) =
        Q.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s) := by
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · refine ⟨E * Q₁ * Q₂, Q₂ * Q₂, a, mul_ne_zero hQ₂ hQ₂, fun s => ?_⟩
    simp only [eval_mul, Int.cast_natCast]
    by_cases hz : Q₂.eval ((q : ℂ) ^ (-s)) = 0
    · rw [hz]
      ring
    · field_simp
  · refine ⟨E * Q₁ * Q₂ * X ^ a, Q₂ * Q₂, 0, mul_ne_zero hQ₂ hQ₂, fun s => ?_⟩
    have hpow : (q : ℂ) ^ (((-(a : ℤ) : ℤ) : ℂ) * s) = ((q : ℂ) ^ (-s)) ^ a := by
      rw [Int.cast_neg, Int.cast_natCast, ← Complex.cpow_nat_mul]
      congr 1
      ring
    simp only [eval_mul, eval_pow, eval_X, Nat.cast_zero, zero_mul, Complex.cpow_zero, mul_one, hpow]
    by_cases hz : Q₂.eval ((q : ℂ) ^ (-s)) = 0
    · rw [hz]
      ring
    · field_simp

private theorem two_le_absNorm_asIdeal (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

private theorem exists_fun_closedForm_of_block (q : ℕ) (hq : 2 ≤ q) (Z Zd : ℂ → ℂ) (E Ed : ℂ[X]) (ε : ℂ) (ℓ : ℕ)
    (R₁ R₂ : ℂ[X]) (m : ℤ) (hR₂ : R₂ ≠ 0) (hE : E ≠ 0) (hEd : Ed ≠ 0)
    (hB : ∀ s : ℂ,
      R₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((m : ℂ) * s) * Ed.eval ((q : ℂ) ^ (-(1 - s))) =
        ε * (q : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * E.eval ((q : ℂ) ^ (-s)) * R₂.eval ((q : ℂ) ^ (-s)))
    (Q₁ Q₂ : ℂ[X]) (n : ℤ) (σ₀' σ₁' : ℝ) (hQ₂ : Q₂ ≠ 0)
    (ha : ∀ s : ℂ, σ₀' < s.re →
      Z s * Q₂.eval ((q : ℂ) ^ (-s)) = Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((n : ℂ) * s))
    (hb : ∀ s : ℂ, σ₁' < (1 - s).re →
      Zd (1 - s) * (Q₂.eval ((q : ℂ) ^ (-s)) * R₂.eval ((q : ℂ) ^ (-s))) =
        R₁.eval ((q : ℂ) ^ (-s)) * Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ (((m : ℂ) + (n : ℂ)) * s)) :
    ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ), σ₀' ≤ σ₀ ∧ σ₁' ≤ σ₁ ∧
      (∃ (Q R : ℂ[X]) (k : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
        P s * R.eval ((q : ℂ) ^ (-s)) = Q.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s)) ∧
      (∀ s : ℂ, σ₀ < s.re → Z s = (E.eval ((q : ℂ) ^ (-s)))⁻¹ * P s) ∧
      (∀ s : ℂ, σ₁ < (1 - s).re →
        Zd (1 - s) = (Ed.eval ((q : ℂ) ^ (-(1 - s))))⁻¹ * ((ε * (q : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)) := by
  have hq0 : (q : ℂ) ≠ 0 := by
    have : (0 : ℕ) < q := by omega
    exact_mod_cast this.ne'
  obtain ⟨σE, hσE⟩ := exists_forall_eval_natCast_cpow_neg_ne_zero_of_re_gt hq E hE
  obtain ⟨σQ, hσQ⟩ := exists_forall_eval_natCast_cpow_neg_ne_zero_of_re_gt hq Q₂ hQ₂
  obtain ⟨τQ, hτQ⟩ := exists_forall_eval_natCast_cpow_neg_ne_zero_of_one_sub_re_gt hq Q₂ hQ₂
  obtain ⟨τR, hτR⟩ := exists_forall_eval_natCast_cpow_neg_ne_zero_of_one_sub_re_gt hq R₂ hR₂
  obtain ⟨τE, hτE⟩ := exists_forall_eval_natCast_cpow_neg_ne_zero_of_re_gt hq Ed hEd
  refine ⟨fun s => E.eval ((q : ℂ) ^ (-s)) * Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((n : ℂ) * s) /
      Q₂.eval ((q : ℂ) ^ (-s)),
    max σ₀' (max σE σQ), max σ₁' (max τQ (max τR τE)), le_max_left _ _, le_max_left _ _,
    exists_closed_form q E Q₁ Q₂ hQ₂ n, fun s hs => ?_, fun s hs => ?_⟩
  ·
    have hs₀ : σ₀' < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hsE : σE < s.re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hs
    have hsQ : σQ < s.re := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hs
    have hEX := hσE s hsE
    have hQX := hσQ s hsQ
    have hZ : Z s = Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((n : ℂ) * s) / Q₂.eval ((q : ℂ) ^ (-s)) :=
      (eq_div_iff hQX).2 (ha s hs₀)
    rw [hZ]
    field_simp
  ·
    have hs₁ : σ₁' < (1 - s).re := lt_of_le_of_lt (le_max_left _ _) hs
    have hsQ : τQ < (1 - s).re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hs
    have hsR : τR < (1 - s).re :=
      lt_of_le_of_lt (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hs
    have hsE : τE < (1 - s).re :=
      lt_of_le_of_lt (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hs
    have hQX := hτQ s hsQ
    have hRX := hτR s hsR
    have hEdX := hτE (1 - s) hsE
    have hsplit : (q : ℂ) ^ (((m : ℂ) + (n : ℂ)) * s) = (q : ℂ) ^ ((m : ℂ) * s) * (q : ℂ) ^ ((n : ℂ) * s) := by
      rw [add_mul, Complex.cpow_add _ _ hq0]
    have hZd : Zd (1 - s) =
        R₁.eval ((q : ℂ) ^ (-s)) * Q₁.eval ((q : ℂ) ^ (-s)) *
            ((q : ℂ) ^ ((m : ℂ) * s) * (q : ℂ) ^ ((n : ℂ) * s)) /
          (Q₂.eval ((q : ℂ) ^ (-s)) * R₂.eval ((q : ℂ) ^ (-s))) :=
      (eq_div_iff (mul_ne_zero hQX hRX)).2 (by rw [hb s hs₁, hsplit])
    have hR₁ : R₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((m : ℂ) * s) =
        ε * (q : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * E.eval ((q : ℂ) ^ (-s)) * R₂.eval ((q : ℂ) ^ (-s)) /
          Ed.eval ((q : ℂ) ^ (-(1 - s))) :=
      (eq_div_iff hEdX).2 (hB s)
    have hZd' : Zd (1 - s) =
        R₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((m : ℂ) * s) *
            (Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((n : ℂ) * s)) /
          (Q₂.eval ((q : ℂ) ^ (-s)) * R₂.eval ((q : ℂ) ^ (-s))) :=
      hZd.trans (by ring)
    rw [hZd', hR₁]
    field_simp

end Algebra

end LanglandsTunnell.CubicInduction

end

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_localZeta31_fe_one_of_forall_exists_mul_eval_eq_of_eval_mul_eq.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_localZeta31_fe_one_of_forall_exists_mul_eval_eq_of_eval_mul_eq.LanglandsTunnell.CubicInduction in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (W : LocalGL3 v → ℂ)
    (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)
    (hE : E ≠ 0) (hEd : Ed ≠ 0)
    (R₁ R₂ : Polynomial ℂ) (m : ℤ)
    (hA : R₁ ≠ 0 ∧ R₂ ≠ 0 ∧
      ∀ g : LocalGL3 v,
        letI := localBorel ℚ v
        ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g *
              Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt
            ℚ v) (dualWhittakerFn3 W) 1⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W 1 (1 - s) g *
              (Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) =
            R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (((m : ℂ) + (n : ℂ)) * s)))
    (hB : ∀ s : ℂ,
      R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) *
          Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) =
        ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
          R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))
    :
    ∀ g : LocalGL3 v,
    (letI := localBorel ℚ v
     ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
      (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
        P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
      (∀ s : ℂ, σ₀ < s.re →
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g =
          (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
      ∀ s : ℂ, σ₁ < (1 - s).re →
        localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
            W 1 (1 - s) g =
          (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
            ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)) := by
  intro g
  letI := localBorel ℚ v
  obtain ⟨-, hR₂, hblock⟩ := hA
  obtain ⟨Q₁, Q₂, n, σ₀', σ₁', hQ₂, hc30, ha, hc31, hb⟩ := hblock g
  obtain ⟨P, σ₀, σ₁, h₀, h₁, hc1, hc2, hc3⟩ :=
    exists_fun_closedForm_of_block (Ideal.absNorm v.asIdeal) (two_le_absNorm_asIdeal v)
      (fun s => localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g)
      (fun t => localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        W 1 t g)
      E Ed ε ℓ R₁ R₂ m hR₂ hE hEd hB Q₁ Q₂ n σ₀' σ₁' hQ₂ ha hb
  exact ⟨P, σ₀, σ₁, hc1, IsLocalZeta30ConvergentAbove.of_le v hc30 h₀, hc2,
    by exact IsLocalZeta31ConvergentAbove.of_le v hc31 h₁, hc3⟩

end S_LanglandsTunnell_CubicInduction_localZeta31_fe_one_of_forall_exists_mul_eval_eq_of_eval_mul_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_localZeta31_fe_one_of_forall_exists_mul_eval_eq_of_eval_mul_eq (solution)
