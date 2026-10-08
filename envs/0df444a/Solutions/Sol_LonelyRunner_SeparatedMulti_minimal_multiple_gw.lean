-- Prove2me | solution 1 for LonelyRunner.SeparatedMulti.minimal_multiple_gw
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T18:54:45.599728+00:00
-- url     : https://prove2.me/submissions/c7d9e974-ddbb-465a-815c-6ca25352fecc

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs
import Theorems.Thm_LonelyRunner_FailedWindow_baseline_safe_boundary

namespace LonelyRunner



theorem ndist_eq_norm (x : ℝ) : ndist x = ‖(x : UnitAddCircle)‖ :=
  UnitAddCircle.norm_eq.symm











































end LonelyRunner

namespace LonelyRunner.BadCover

theorem continuous_ndist : Continuous ndist := by
  have heq : ndist = fun x : ℝ => ‖(x : UnitAddCircle)‖ := funext ndist_eq_norm
  rw [heq]
  exact continuous_norm.comp (AddCircle.continuous_mk' (1 : ℝ))



theorem strict_of_between {x δ : ℝ} {m : ℤ}
    (hl : (m : ℝ) + δ < x) (hu : x < m + 1 - δ) : δ < ndist x := by
  change δ < |x - (round x : ℤ)|
  rcases le_or_gt (round x) m with h | h
  · have hR : ((round x : ℤ) : ℝ) ≤ m := by exact_mod_cast h
    exact lt_of_lt_of_le (by linarith) (le_abs_self _)
  · have hR : (m : ℝ) + 1 ≤ (round x : ℤ) := by exact_mod_cast h
    exact lt_of_lt_of_le (by linarith) (neg_le_abs _)















end LonelyRunner.BadCover

namespace LonelyRunner.LaminarCover

open Set





end LonelyRunner.LaminarCover

namespace LonelyRunner.Farey

theorem exists_determinant_one {r s : ℤ} (h : Int.gcd r s = 1) :
    ∃ a b : ℤ, b * r - a * s = 1 := by
  refine ⟨-Int.gcdB r s, Int.gcdA r s, ?_⟩
  have hb := Int.gcd_eq_gcd_ab r s
  rw [h] at hb
  norm_num at hb
  linear_combination -hb

















end LonelyRunner.Farey

namespace LonelyRunner.CoprimeReplacements

open Farey BadCover





























end LonelyRunner.CoprimeReplacements

namespace LonelyRunner.SingleDeletion

open BadCover









end LonelyRunner.SingleDeletion

namespace LonelyRunner.BadCover











end LonelyRunner.BadCover

namespace LonelyRunner.MatchingArithmetic





end LonelyRunner.MatchingArithmetic

namespace LonelyRunner.LargeDeletionMatching

open BadCover SingleDeletion



















end LonelyRunner.LargeDeletionMatching

namespace LonelyRunner.SeparatedBands

open BadCover

/-- Below the gcd threshold, intersecting bad bands have the same center. -/
theorem overlap_determinant {p q d c j : ℤ} {δ t : ℝ}
    (hp : 0<p) (hq : 0<q) (hdp : d∣p) (hdq : d∣q)
    (hsep : δ*((p:ℝ)+q)<d)
    (hc : |(p:ℝ)*t-c|≤δ) (hj : |(q:ℝ)*t-j|≤δ) :
    q*c-p*j=0 := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hdiv : d∣q*c-p*j := dvd_sub (dvd_mul_of_dvd_left hdq c) (dvd_mul_of_dvd_left hdp j)
  have hbound : |(q:ℝ)*c-p*j|≤δ*((p:ℝ)+q) := by
    calc
      _ = |(p:ℝ)*((q:ℝ)*t-j)-(q:ℝ)*((p:ℝ)*t-c)| := by congr 1; ring
      _ ≤ |(p:ℝ)*((q:ℝ)*t-j)|+|(q:ℝ)*((p:ℝ)*t-c)| := by
        simpa using (abs_sub_le ((p:ℝ)*((q:ℝ)*t-j)) 0 ((q:ℝ)*((p:ℝ)*t-c)))
      _ = (p:ℝ)*|((q:ℝ)*t-j)|+(q:ℝ)*|((p:ℝ)*t-c)| := by
        rw [abs_mul,abs_mul,abs_of_pos hpR,abs_of_pos hqR]
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hj hpR.le,
        mul_le_mul_of_nonneg_left hc hqR.le]
  by_contra hh
  have hge := Int.le_abs_of_dvd hh hdiv
  have hgeR : (d:ℝ)≤|(q:ℝ)*c-p*j| := by exact_mod_cast hge
  linarith

/-- The faster speed is strictly safe at either endpoint of a slower bad band. -/
theorem fast_safe_at_boundary {p q d c : ℤ} {δ t : ℝ}
    (hp : 0<p) (hpq : p<q) (hdp : d∣p) (hdq : d∣q)
    (hδ : 0<δ) (hsep : δ*((p:ℝ)+q)<d)
    (hc : |(p:ℝ)*t-c|=δ) : δ<ndist ((q:ℝ)*t) := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hpqR : (p:ℝ)<q := by exact_mod_cast hpq
  by_contra! hh
  have heq := overlap_determinant hp (lt_trans hp hpq) hdp hdq hsep hc.le hh
  have heqR : (q:ℝ)*c-p*(round ((q:ℝ)*t):ℤ)=0 := by exact_mod_cast heq
  have hid : (p:ℝ)*|(q:ℝ)*t-(round ((q:ℝ)*t):ℤ)|=(q:ℝ)*δ := by
    calc
      _ = |(p:ℝ)*((q:ℝ)*t-(round ((q:ℝ)*t):ℤ))| := by rw [abs_mul,abs_of_pos hpR]
      _ = |(q:ℝ)*((p:ℝ)*t-c)| := by congr 1; nlinarith only [heqR]
      _ = _ := by rw [abs_mul,abs_of_pos (lt_trans hpR hpqR),hc]
  change |(q:ℝ)*t-(round ((q:ℝ)*t):ℤ)|≤δ at hh
  nlinarith [mul_le_mul_of_nonneg_left hh hpR.le]

/-- The other speed is safe at a band endpoint if it is not integer at the
band's center; no speed ordering is required. -/
theorem safe_at_boundary_of_noninteger {p q d c : ℤ} {δ t : ℝ}
    (hp : 0<p) (hq : 0<q) (hdp : d∣p) (hdq : d∣q)
    (hsep : δ*((p:ℝ)+q)<d) (hc : |(p:ℝ)*t-c|≤δ)
    (hneq : ∀ j : ℤ, q*c≠p*j) : δ<ndist ((q:ℝ)*t) := by
  by_contra! hh
  exact hneq _ (sub_eq_zero.mp (overlap_determinant hp hq hdp hdq hsep hc hh))

/-- Strict safety for finitely many other speeds survives moving just beyond
the left endpoint of a bad band. -/
theorem escape_left {p δ t : ℝ} {c : ℤ} (S : Finset ℕ)
    (hp : 0<p) (hδ : δ<1/2) (hc : p*t=(c:ℝ)-δ)
    (hsafe : ∀ v∈S, δ<ndist ((v:ℝ)*t)) :
    ∃ u : ℝ, δ<ndist (p*u) ∧ ∀ v∈S, δ<ndist ((v:ℝ)*u) := by
  have hopen : IsOpen {u : ℝ | ∀ v∈S, δ<ndist ((v:ℝ)*u)} := by
    simp only [Set.ofPred_forall]
    exact isOpen_biInter_finset fun v _ =>
      isOpen_lt continuous_const (continuous_ndist.comp (continuous_const.mul continuous_id))
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen t hsafe
  let e := min (ε/2) ((1-2*δ)/(2*p))
  have he : 0<e := lt_min (by positivity) (by apply div_pos <;> linarith)
  have heε : e<ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hep : p*e≤(1-2*δ)/2 := by
    have hh := (le_div_iff₀ (show 0<2*p by linarith)).mp (min_le_right (ε/2) ((1-2*δ)/(2*p)))
    dsimp [e]
    nlinarith only [hh]
  refine ⟨t-e,?_,hball ?_⟩
  · apply strict_of_between (m := c-1)
    · push_cast
      nlinarith
    · push_cast
      nlinarith
  · rw [Metric.mem_ball,Real.dist_eq,sub_sub_cancel_left,abs_neg,abs_of_pos he]
    exact heε

end LonelyRunner.SeparatedBands

namespace LonelyRunner

open Finset



























end LonelyRunner

namespace LonelyRunner

















end LonelyRunner

namespace LonelyRunner.FailedWindow

open Farey BadCover









end LonelyRunner.FailedWindow

namespace LonelyRunner.SeparatedReplacements

open LargeDeletionMatching SeparatedBands























end LonelyRunner.SeparatedReplacements

namespace LonelyRunner.MixedReplacements

open LargeDeletionMatching SeparatedReplacements













end LonelyRunner.MixedReplacements

namespace LonelyRunner.SeparatedMulti

open SeparatedReplacements SeparatedBands SingleDeletion







set_option maxHeartbeats 1000000 in
theorem other_safe_at_boundary {n r m q b : ℕ} {a c : ℤ}
    (hn : 0 < n) (hr : 0 < r) (hm : 0 < m) (hq : 0 < q)
    (hu : a*(b:ℤ)-c*(r:ℤ)=1)
    (hsep : m*r+q < n*Nat.gcd (m*r) q)
    (hcase : m*r < q ∨ ¬ r ∣ q) :
    (1:ℝ)/n < ndist ((q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))) := by
  have hnR : (0:ℝ) < n := by positivity
  have hδ : (0:ℝ) < 1/n := by positivity
  have hmZ : (0:ℤ) < m := by exact_mod_cast hm
  let t : ℝ := (a:ℝ)/r-1/((n:ℝ)*m*r)
  have hval : ((m*r:ℕ):ℝ)*t=(m*a:ℤ)-(1:ℝ)/n := by
    have hrR : (r:ℝ) ≠ 0 := by positivity
    have hmR : (m:ℝ) ≠ 0 := by positivity
    dsimp [t]
    push_cast
    field_simp
  have hb : |((m*r:ℕ):ℝ)*t-(m*a:ℤ)|=(1:ℝ)/n := by
    rw [hval,sub_sub_cancel_left,abs_neg,abs_of_pos hδ]
  have hdp : (Nat.gcd (m*r) q:ℤ) ∣ ((m*r:ℕ):ℤ) := by
    exact_mod_cast Nat.gcd_dvd_left (m*r) q
  have hdq : (Nat.gcd (m*r) q:ℤ) ∣ (q:ℤ) := by
    exact_mod_cast Nat.gcd_dvd_right (m*r) q
  have hsepR : (1/(n:ℝ))*(((m*r:ℕ):ℝ)+q) < (Nat.gcd (m*r) q:ℤ) := by
    rw [one_div_mul_eq_div,div_lt_iff₀ hnR]
    exact_mod_cast (show m*r+q < Nat.gcd (m*r) q*n by simpa [mul_comm] using hsep)
  rcases hcase with hlt | hnot
  · exact fast_safe_at_boundary (by exact_mod_cast Nat.mul_pos hm hr)
      (by exact_mod_cast hlt) hdp hdq hδ hsepR hb
  · apply safe_at_boundary_of_noninteger (by exact_mod_cast Nat.mul_pos hm hr)
      (by exact_mod_cast hq) hdp hdq hsepR hb.le
    intro j hj
    have hz : (m:ℤ)*((q:ℤ)*a-(r:ℤ)*j)=0 := by
      push_cast at hj
      nlinarith only [hj]
    have heq := (mul_eq_zero.mp hz).resolve_left hmZ.ne'
    apply hnot
    have hd : (r:ℤ) ∣ (q:ℤ) := by
      refine ⟨(b:ℤ)*j-c*q,?_⟩
      nlinarith [congrArg (fun x : ℤ => x*q) hu]
    exact_mod_cast hd















end LonelyRunner.SeparatedMulti

namespace LonelyRunner.InteractionComponents

open Set























end LonelyRunner.InteractionComponents

namespace LonelyRunner.GWArithmetic

open SeparatedReplacements







end LonelyRunner.GWArithmetic

namespace LonelyRunner.ContactPreservation











end LonelyRunner.ContactPreservation

namespace LonelyRunner.GWContactArithmetic

open SeparatedReplacements ContactPreservation



















end LonelyRunner.GWContactArithmetic

namespace LonelyRunner.ComponentRestoration

open SeparatedMulti InteractionComponents









end LonelyRunner.ComponentRestoration

namespace LonelyRunner.GWGrowth

open SeparatedReplacements GWArithmetic

























end LonelyRunner.GWGrowth

namespace LonelyRunner.OddSmooth

open SeparatedReplacements GWGrowth















end LonelyRunner.OddSmooth

namespace LonelyRunner.SecondUnit

open SeparatedReplacements GWArithmetic OddSmooth











end LonelyRunner.SecondUnit

namespace LonelyRunner.ElementarySmooth

open SeparatedReplacements OddSmooth GWArithmetic GWGrowth SecondUnit

















end LonelyRunner.ElementarySmooth

namespace LonelyRunner.FailedFlank

open Farey BadCover LargeDeletionMatching









end LonelyRunner.FailedFlank

namespace LonelyRunner.FlankReduction

















end LonelyRunner.FlankReduction

namespace LonelyRunner.MixedNormalize

open SeparatedReplacements SecondUnit GWArithmetic



end LonelyRunner.MixedNormalize

namespace LonelyRunner.MixedArithmetic

open SeparatedReplacements GWArithmetic GWGrowth FlankReduction SecondUnit



end LonelyRunner.MixedArithmetic

namespace LonelyRunner.NearData

open LargeDeletionMatching SeparatedReplacements







end LonelyRunner.NearData

namespace LonelyRunner.MixedConverse

open LargeDeletionMatching SeparatedReplacements MixedReplacements
open GWArithmetic GWGrowth FlankReduction









end LonelyRunner.MixedConverse

namespace LonelyRunner.SmallComponentRigidity

open SeparatedMulti SeparatedReplacements InteractionComponents





































end LonelyRunner.SmallComponentRigidity

open LonelyRunner
open LonelyRunner.SeparatedMulti
open SeparatedReplacements SeparatedBands SingleDeletion

set_option maxHeartbeats 1500000 in
/-- The smallest inserted multiple of a deletion must obey its individual GW rule. -/
theorem solution {n r m : ℕ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hrR : r ∈ R) (hlarge : n ≤ 2*r) (hrn : r < n)
    (hm : 2 ≤ m) (hpW : m*r ∈ W)
    (hW : ∀ q ∈ W, n ≤ q) (hsep : Separated n W)
    (hmin : ∀ q ∈ W, r ∣ q → m*r ≤ q)
    (hno : ¬ HasStrictTime n R W) : GW n r m := by
  intro b hab hfail hcop
  have hr : 0 < r := by omega
  have hn0 : 0 < n := by omega
  have hm0 : 0 < m := by omega
  have hnR : (0:ℝ) < n := by positivity
  obtain ⟨a',c',hu'⟩ := Farey.exists_determinant_one
    (r := (r:ℤ)) (s := (b:ℤ)) (by simpa using hcop.gcd_eq_one)
  let a := -a'
  let c := -c'
  have hu : a*(b:ℤ)-c*(r:ℤ)=1 := by dsimp [a,c]; nlinarith only [hu']
  let t : ℝ := (a:ℝ)/r-1/((n:ℝ)*m*r)
  have hval : ((m*r:ℕ):ℝ)*t=(m*a:ℤ)-(1:ℝ)/n := by
    have hrR : (r:ℝ) ≠ 0 := by positivity
    have hmR : (m:ℝ) ≠ 0 := by positivity
    dsimp [t]
    push_cast
    field_simp
  have hbase (v : ℕ) (hv : 0 < v) (hvn : v < n) (hne : v ≠ r) :
      (1:ℝ)/n < ndist ((v:ℝ)*t) := by
    apply FailedWindow.baseline_safe_boundary (n := (n:ℤ)) (r := (r:ℤ))
      (m := (m:ℤ)) (b := (b:ℤ)) (a := a) (c := c)
      (by exact_mod_cast hr) (by exact_mod_cast hrn) (by exact_mod_cast hlarge) (by omega)
    · rw [← Nat.cast_sub hrn.le]; exact_mod_cast hab
    · rw [← Nat.cast_sub hrn.le]; exact_mod_cast hfail
    · exact hu
    · exact_mod_cast hv
    · exact_mod_cast hvn
    · exact_mod_cast hne
  have hother (q : ℕ) (hqW : q ∈ W) (hne : q ≠ m*r) :
      (1:ℝ)/n < ndist ((q:ℝ)*t) := by
    have hq : 0 < q := lt_of_lt_of_le hn0 (hW q hqW)
    apply other_safe_at_boundary hn0 hr hm0 hq hu (hsep _ hpW q hqW hne.symm)
    by_cases hlt : m*r < q
    · exact Or.inl hlt
    · exact Or.inr (fun hd => by have := hmin q hqW hd; omega)
  let S := ((Finset.range n).filter (fun v => 0 < v ∧ v ∉ R)) ∪ W.erase (m*r)
  have hS : ∀ v ∈ S, (1:ℝ)/n < ndist ((v:ℝ)*t) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨hvn,hv0,hvR⟩ := Finset.mem_filter.mp hv
      exact hbase v hv0 (Finset.mem_range.mp hvn) (by rintro rfl; exact hvR hrR)
    · obtain ⟨hne,hvW⟩ := Finset.mem_erase.mp hv
      exact hother v hvW hne
  have hhalf : (1:ℝ)/n < 1/2 := by
    apply (div_lt_div_iff₀ hnR (by norm_num : (0:ℝ) < 2)).mpr
    exact_mod_cast (show 1*2 < 1*n by omega)
  obtain ⟨u,hp,huS⟩ := escape_left S (by exact_mod_cast Nat.mul_pos hm0 hr)
    hhalf hval hS
  apply hno
  refine ⟨u,fun v hv => ?_⟩
  rcases hv with ⟨hv,hvn,hvR⟩ | hvW
  · exact huS v (Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hvn,hv,hvR⟩))
  · by_cases heq : v=m*r
    · simpa [heq] using hp
    · exact huS v (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨heq,hvW⟩))
