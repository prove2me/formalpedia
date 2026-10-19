-- Prove2me | solution 1 for OAI.ContinuumTemperature.laplace_principle_eventual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:06:28.983913+00:00
-- url     : https://prove2.me/submissions/866f8ed3-3942-4816-bb3b-3dd8f45f07f5

import Mathlib
import Definitions.Def_OAIQWCT000

section
-- module Solutions.OAIQW_ContinuumTemperature.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_ContinuumTemperature.DensityLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem densityFilter_length (d : ℝ) :
    Tendsto (fun p : ℝ × ℕ => p.1) (densityFilter d) atTop := by
  have h : Tendsto (fun p : ℝ × ℕ => (p.1, (p.2 : ℝ)/p.1^3))
      (densityFilter d) (atTop ×ˢ 𝓝 d) := Filter.tendsto_comap
  simpa only [Function.comp_def] using
    (tendsto_fst : Tendsto (Prod.fst : ℝ × ℝ → ℝ) (atTop ×ˢ 𝓝 d) atTop).comp h

theorem tendsto_densityFilter_iff {α : Type u_1} {l : Filter α} {d : ℝ} {p : α → ℝ × ℕ} :
    Tendsto p l (densityFilter d) ↔
      Tendsto (fun x => (p x).1) l atTop ∧
      Tendsto (fun x => ((p x).2 : ℝ)/(p x).1^3) l (𝓝 d) := by
  rw [densityFilter, tendsto_comap_iff, tendsto_prod_iff']
  rfl

theorem floor_density_tendsto {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun L : ℝ => (L, ⌊d*L^3⌋₊)) atTop (densityFilter d) := by
  apply tendsto_densityFilter_iff.2
  exact ⟨tendsto_id, (tendsto_nat_floor_mul_div_atTop hd).comp
    (tendsto_pow_atTop (by norm_num : 3 ≠ 0))⟩

instance densityFilter_neBot (d : ℝ) [Fact (0 ≤ d)] : (densityFilter d).NeBot :=
  (floor_density_tendsto (Fact.out : 0 ≤ d)).neBot

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LaplaceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter Set

namespace ContinuumTemperature

theorem tsum_le_low_sector_add_tail {w b : ℕ → ℝ} (hw : Summable w) (hb : Summable b)
    (hb0 : ∀ n, 0 ≤ b n) {M : ℕ} {A : ℝ}
    (hlow : ∀ n, n < M → w n ≤ A) (hhigh : ∀ n, M ≤ n → w n ≤ b n) :
    ∑' n, w n ≤ (M : ℝ)*A + ∑' n, b n := by
  have hst : Summable (fun n : ℕ => w (n+M)) :=
    hw.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hbt : Summable (fun n : ℕ => b (n+M)) :=
    hb.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have ht : (∑' n : ℕ, w (n+M)) ≤ ∑' n : ℕ, b (n+M) :=
    hst.tsum_le_tsum (fun n => hhigh _ (Nat.le_add_left M n)) hbt
  have htail : (∑' n : ℕ, b (n+M)) ≤ ∑' n, b n := by
    rw [← hb.sum_add_tsum_nat_add M]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun n _ => hb0 n))
  have hsum : (∑ n ∈ Finset.range M, w n) ≤ (M : ℝ)*A := by
    calc
      (∑ n ∈ Finset.range M, w n) ≤ ∑ n ∈ Finset.range M, A :=
        Finset.sum_le_sum (fun n hn => hlow n (Finset.mem_range.mp hn))
      _ = _ := by simp
  rw [← hw.sum_add_tsum_nat_add M]
  exact add_le_add hsum (ht.trans htail)

theorem log_affine_cube_div_tendsto_zero {D C : ℝ} (hD : 0 < D) :
    Tendsto (fun L : ℝ => Real.log (D*L^3+C)/L^3) atTop (𝓝 0) := by
  have hv : Tendsto (fun L : ℝ => L^3) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hz : Tendsto (fun L : ℝ => D*L^3+C) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop C (hv.const_mul_atTop hD)
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hz
  have hi : Tendsto (fun L : ℝ => (L^3)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hv
  have hr : Tendsto (fun L : ℝ => D+C*(L^3)⁻¹) atTop (𝓝 D) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (hi.const_mul C)
  have hh := hlog.mul hr
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [hv.eventually (eventually_gt_atTop 0), hz.eventually (eventually_gt_atTop 0)] with L hL hzL
  change Real.log (D*L^3+C)/(D*L^3+C)*(D+C*(L^3)⁻¹) = _
  have hn : L ≠ 0 := by rintro rfl; simp at hL
  field_simp [hn, ne_of_gt hzL]

theorem log_tsum_div_le {w b : ℕ → ℝ} (hw : Summable w) (hb : Summable b)
    (hb0 : ∀ n, 0 ≤ b n) (hpos : 0 < ∑' n, w n) {M : ℕ} (hM : 0 < M)
    {V c : ℝ} (hV : 0 < V) (hc : 0 ≤ c)
    (hlow : ∀ n, n < M → w n ≤ Real.exp (V*c))
    (hhigh : ∀ n, M ≤ n → w n ≤ b n) :
    Real.log (∑' n, w n)/V ≤ c + Real.log ((M : ℝ)+∑' n, b n)/V := by
  have hbS : 0 ≤ ∑' n, b n := tsum_nonneg hb0
  have he : 1 ≤ Real.exp (V*c) := Real.one_le_exp (mul_nonneg hV.le hc)
  have hbound := tsum_le_low_sector_add_tail hw hb hb0 hlow hhigh
  have hbound' : ∑' n, w n ≤ ((M : ℝ)+∑' n, b n)*Real.exp (V*c) := by
    have hh := mul_le_mul_of_nonneg_left he hbS
    nlinarith only [hbound, hh]
  have hp : 0 < (M : ℝ)+∑' n, b n := by positivity
  have hlog := Real.log_le_log hpos hbound'
  rw [Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  calc
    Real.log (∑' n, w n)/V ≤ (Real.log ((M : ℝ)+∑' n, b n)+V*c)/V :=
      div_le_div_of_nonneg_right hlog hV.le
    _ = _ := by field_simp; ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LaplacePrinciple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem density_compact_eventually {K : Set ℝ} (hK : IsCompact K)
    {P : ℝ × ℕ → Prop} (hP : ∀ d ∈ K, ∀ᶠ p in densityFilter d, P p) :
    ∀ᶠ L in atTop, ∀ n : ℕ, (n : ℝ)/L^3 ∈ K → P (L,n) := by
  have hp : ∀ᶠ p in Filter.comap
      (fun p : ℝ × ℕ => (p.1, (p.2 : ℝ)/p.1^3)) (atTop ×ˢ 𝓝ˢ K), P p := by
    rw [hK.prod_nhdsSet_eq_biSup, comap_iSup]
    simp only [comap_iSup, eventually_iSup]
    exact hP
  obtain ⟨S, hS, hsub⟩ := Filter.mem_comap.mp hp
  obtain ⟨T, hT, U, hU, hTU⟩ := Filter.mem_prod_iff.mp hS
  filter_upwards [hT] with L hL
  intro n hn
  exact hsub (hTU ⟨hL, (subset_of_mem_nhdsSet hU) hn⟩)

theorem laplace_low_sector {w : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {D S ε : ℝ}
    (hw : ∀ L > 0, ∀ n, 0 < w L n) (hD : 0 < D) (hε : 0 < ε)
    (hF : ∀ d, 0 ≤ d → F d ≤ S)
    (hlim : ∀ d, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3)
      (densityFilter d) (𝓝 (F d))) :
    ∀ᶠ L in atTop, ∀ n : ℕ, n < ⌊D*L^3⌋₊+1 →
      w L n ≤ Real.exp (L^3*(S+ε)) := by
  have he : ∀ᶠ L in atTop, ∀ n : ℕ, (n : ℝ)/L^3 ∈ Icc 0 D →
      Real.log (w L n)/L^3 < S+ε := by
    apply density_compact_eventually (K := Icc 0 D)
      (P := fun p => Real.log (w p.1 p.2)/p.1^3 < S+ε) isCompact_Icc
    intro d hd
    apply (hlim d hd.1).eventually_lt_const
    linarith [hF d hd.1]
  filter_upwards [he, eventually_gt_atTop 0] with L hL hp
  intro n hn
  have hn' : (n : ℝ) ≤ D*L^3 :=
    (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hn)).trans (Nat.floor_le (by positivity))
  have hr : (n : ℝ)/L^3 ∈ Icc 0 D :=
    ⟨div_nonneg (Nat.cast_nonneg n) (pow_pos hp 3).le, (div_le_iff₀ (pow_pos hp 3)).2 hn'⟩
  apply (Real.log_le_iff_le_exp (hw L hp n)).1
  have hh := (div_lt_iff₀ (pow_pos hp 3)).1 (hL n hr)
  nlinarith only [hh]

theorem laplace_upper_eventually {w : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {b : ℕ → ℝ}
    {D S : ℝ}
    (hw : ∀ L > 0, ∀ n, 0 < w L n) (hsum : ∀ L > 0, Summable (w L))
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) (hD : 0 < D) (hS : 0 ≤ S)
    (hF : ∀ d, 0 ≤ d → F d ≤ S)
    (hlim : ∀ d, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3)
      (densityFilter d) (𝓝 (F d)))
    (htail : ∀ᶠ L in atTop, ∀ n : ℕ, D ≤ (n : ℝ)/L^3 → w L n ≤ b n) :
    ∀ q > S, ∀ᶠ L in atTop, Real.log (∑' n, w L n)/L^3 < q := by
  intro q hq
  let ε := (q-S)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hlog := log_affine_cube_div_tendsto_zero (C := 1+∑' n, b n) hD
  have he := hlog.eventually_lt_const hε
  filter_upwards [laplace_low_sector hw hD hε hF hlim, htail, he,
    eventually_gt_atTop 0] with L hlow hhigh hsmall hL
  let M : ℕ := ⌊D*L^3⌋₊+1
  have hV : 0 < L^3 := pow_pos hL 3
  have hpos : 0 < ∑' n, w L n :=
    (hw L hL 0).trans_le ((hsum L hL).le_tsum 0 (fun n _ => (hw L hL n).le))
  have hh := log_tsum_div_le (hsum L hL) hb hb0 hpos (Nat.succ_pos _ : 0 < M)
    hV (show 0 ≤ S+ε by linarith) hlow (fun n hn => hhigh n (by
      apply (le_div_iff₀ hV).2
      have hm : D*L^3 < (M : ℝ) := by simpa [M] using Nat.lt_floor_add_one (D*L^3)
      exact hm.le.trans (Nat.cast_le.mpr hn)))
  have hbS : 0 ≤ ∑' n, b n := tsum_nonneg hb0
  have hM : (M : ℝ)+∑' n, b n ≤ D*L^3+(1+∑' n, b n) := by
    have hf := Nat.floor_le (mul_nonneg hD.le hV.le)
    dsimp [M]
    push_cast
    linarith
  have hMpos : 0 < (M : ℝ)+∑' n, b n := by
    have hp : 0 < (M : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
    linarith
  have hl := div_le_div_of_nonneg_right (Real.log_le_log hMpos hM) hV.le
  dsimp [ε] at *
  linarith only [hh, hl, hsmall]

theorem laplace_principle {w : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {b : ℕ → ℝ} {D : ℝ}
    (hw : ∀ L > 0, ∀ n, 0 < w L n) (hsum : ∀ L > 0, Summable (w L))
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) (hD : 0 < D) (hF0 : F 0 = 0)
    (hbdd : BddAbove (F '' Ici 0))
    (hlim : ∀ d, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3)
      (densityFilter d) (𝓝 (F d)))
    (htail : ∀ᶠ L in atTop, ∀ n : ℕ, D ≤ (n : ℝ)/L^3 → w L n ≤ b n) :
    Tendsto (fun L => Real.log (∑' n, w L n)/L^3) atTop (𝓝 (sSup (F '' Ici 0))) := by
  have hnon : (F '' Ici 0).Nonempty := ⟨F 0, ⟨0, by simp, rfl⟩⟩
  have hF : ∀ d, 0 ≤ d → F d ≤ sSup (F '' Ici 0) :=
    fun d hd => le_csSup hbdd ⟨d, hd, rfl⟩
  have hS : 0 ≤ sSup (F '' Ici 0) := by simpa [hF0] using hF 0 le_rfl
  apply tendsto_order.2
  constructor
  · intro q hq
    obtain ⟨_, ⟨d, hd, rfl⟩, hqd⟩ := exists_lt_of_lt_csSup hnon hq
    have hdlim := (hlim d hd).comp (floor_density_tendsto hd)
    filter_upwards [hdlim.eventually_const_lt hqd, eventually_gt_atTop 0] with L hL hp
    have hh := (hsum L hp).le_tsum ⌊d*L^3⌋₊ (fun n _ => (hw L hp n).le)
    exact hL.trans_le (div_le_div_of_nonneg_right (Real.log_le_log (hw L hp _) hh)
      (pow_pos hp 3).le)
  · exact laplace_upper_eventually hw hsum hb hb0 hD hS hF hlim htail

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LaplaceEventual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter Set
namespace ContinuumTemperature

theorem laplace_principle_eventual_oai {w : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {b : ℕ → ℝ} {D : ℝ}
    (hw : ∀ L > 0, ∀ n, 0 < w L n) (hsum : ∀ᶠ L in atTop, Summable (w L))
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) (hD : 0 < D) (hF0 : F 0 = 0)
    (hbdd : BddAbove (F '' Ici 0))
    (hlim : ∀ d, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3)
      (densityFilter d) (𝓝 (F d)))
    (htail : ∀ᶠ L in atTop, ∀ n : ℕ, D ≤ (n : ℝ)/L^3 → w L n ≤ b n) :
    Tendsto (fun L => Real.log (∑' n, w L n)/L^3) atTop (𝓝 (sSup (F '' Ici 0))) := by
  classical
  let v (L : ℝ) (n : ℕ) := if Summable (w L) then w L n else (Real.exp (-1))^n
  have hvs (L : ℝ) (_ : 0 < L) : Summable (v L) := by
    by_cases hh : Summable (w L)
    · simpa only [v, ite_eq_left hh] using hh
    · simp only [v, ite_eq_right hh]
      exact summable_geometric_of_lt_one (Real.exp_pos _).le (by simp)
  have hv (L : ℝ) (hL : 0 < L) (n : ℕ) : 0 < v L n := by
    dsimp only [v]
    split_ifs
    · exact hw L hL n
    · exact pow_pos (Real.exp_pos _) n
  have hve : ∀ᶠ L in atTop, v L = w L := by
    filter_upwards [hsum] with L hL
    funext n
    exact ite_eq_left hL
  have hvl (d : ℝ) (hd : 0 ≤ d) := (hlim d hd).congr' (by
    filter_upwards [(densityFilter_length d).eventually hve] with p hp
    rw [hp] : (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3) =ᶠ[densityFilter d]
      (fun p : ℝ × ℕ => Real.log (v p.1 p.2)/p.1^3))
  have ht : ∀ᶠ L in atTop, ∀ n : ℕ, D ≤ (n : ℝ)/L^3 → v L n ≤ b n := by
    filter_upwards [hve, htail] with L he hh
    simpa only [he] using hh
  have hh := laplace_principle hv hvs hb hb0 hD hF0 hbdd hvl ht
  apply hh.congr'
  filter_upwards [hve] with L hL
  rw [hL]

end ContinuumTemperature
end

end OAI
end

theorem solution : type_of% @OAI.ContinuumTemperature.laplace_principle_eventual_oai := @OAI.ContinuumTemperature.laplace_principle_eventual_oai
