-- Prove2me | solution 1 for LonelyRunner.InteractionComponents.localize_interval
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T18:55:59.664254+00:00
-- url     : https://prove2.me/submissions/5b365a07-751b-4e3d-b965-3bf062900659

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs
import Theorems.Thm_LonelyRunner_LaminarCover_localize

namespace LonelyRunner











/-- `ndist x` is at most the distance from `x` to any integer. -/
theorem ndist_le_abs_sub (x : ℝ) (m : ℤ) : ndist x ≤ |x - m| := round_le x m



































end LonelyRunner

namespace LonelyRunner.BadCover





















end LonelyRunner.BadCover

namespace LonelyRunner.LaminarCover

open Set





end LonelyRunner.LaminarCover

namespace LonelyRunner.Farey



















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





theorem band_closed (δ : ℝ) (i : ℕ × ℤ) : IsClosed (band δ i) :=
  isClosed_le ((continuous_const.mul continuous_id).sub continuous_const).abs continuous_const

theorem same_center_subset {p q : ℕ} {c j : ℤ} {δ : ℝ}
    (hq : 0 < q) (hδ : 0 ≤ δ) (hpq : p ≤ q)
    (hcenter : (q : ℤ)*c-(p : ℤ)*j=0) :
    band δ (q,j) ⊆ band δ (p,c) := by
  intro t ht
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpR : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hcR : (q : ℝ)*c-(p : ℝ)*j=0 := by exact_mod_cast hcenter
  have hid : (q : ℝ)*|(p : ℝ)*t-c| = (p : ℝ)*|(q : ℝ)*t-j| := by
    calc
      _ = |(q:ℝ)*((p:ℝ)*t-c)| := by rw [abs_mul,abs_of_pos hqR]
      _ = |(p:ℝ)*((q:ℝ)*t-j)| := by congr 1; nlinarith only [hcR]
      _ = _ := by rw [abs_mul,abs_of_nonneg hpR]
  change |(q : ℝ)*t-j| ≤ δ at ht
  change |(p : ℝ)*t-c| ≤ δ
  have hmul := mul_le_mul_of_nonneg_left ht hpR
  have hdelta := mul_le_mul_of_nonneg_right hpqR hδ
  nlinarith only [hid,hmul,hdelta,hqR]

/-- Separated distinct speeds have strictly nested intersecting bad bands. -/
theorem bands_nested {n p q : ℕ} {c j : ℤ}
    (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) (hne : p ≠ q)
    (hsep : p+q < n*Nat.gcd p q)
    (hinter : (band (1/(n:ℝ)) (p,c) ∩ band (1/(n:ℝ)) (q,j)).Nonempty) :
    band (1/(n:ℝ)) (p,c) ⊂ band (1/(n:ℝ)) (q,j) ∨
      band (1/(n:ℝ)) (q,j) ⊂ band (1/(n:ℝ)) (p,c) := by
  have hnR : (0 : ℝ) < n := by positivity
  have hδ : (0 : ℝ) < 1/n := by positivity
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  have hdP : (Nat.gcd p q : ℤ) ∣ p := by exact_mod_cast Nat.gcd_dvd_left p q
  have hdQ : (Nat.gcd p q : ℤ) ∣ q := by exact_mod_cast Nat.gcd_dvd_right p q
  have hsepR : (1/(n:ℝ))*((p:ℝ)+q) < (Nat.gcd p q : ℤ) := by
    rw [one_div_mul_eq_div,div_lt_iff₀ hnR]
    exact_mod_cast (show p+q < Nat.gcd p q*n by simpa [mul_comm] using hsep)
  obtain ⟨t, htP, htQ⟩ := hinter
  have hcenter := SeparatedBands.overlap_determinant hpZ hqZ hdP hdQ hsepR htP htQ
  have strict_subset (p q : ℕ) (c j : ℤ) (hp : 0 < p) (hpq : p < q)
      (hcenter : (q : ℤ)*c-(p : ℤ)*j=0)
      (hsafe : ∀ t : ℝ, |(p:ℝ)*t-c|=1/(n:ℝ) →
        1/(n:ℝ)<ndist ((q:ℝ)*t)) :
      band (1/(n:ℝ)) (q,j) ⊂ band (1/(n:ℝ)) (p,c) := by
    have hsub := same_center_subset (lt_trans hp hpq) hδ.le hpq.le hcenter
    refine ⟨hsub,?_⟩
    intro hreverse
    let u : ℝ := ((c:ℝ)-1/(n:ℝ))/p
    have hu : |(p:ℝ)*u-c|=1/(n:ℝ) := by
      have hpR : (p:ℝ) ≠ 0 := by positivity
      dsimp [u]
      rw [mul_div_cancel₀ _ hpR]
      simp
    have hbad : |(q:ℝ)*u-j| ≤ 1/(n:ℝ) := hreverse hu.le
    exact (not_le_of_gt (hsafe u hu)) ((ndist_le_abs_sub _ j).trans hbad)
  rcases lt_or_gt_of_ne hne with hpq | hqp
  · right
    apply strict_subset p q c j hp hpq hcenter
    intro u hu
    exact SeparatedBands.fast_safe_at_boundary hpZ (by exact_mod_cast hpq)
      hdP hdQ hδ hsepR hu
  · left
    apply strict_subset q p j c hq hqp (by nlinarith only [hcenter])
    intro u hu
    exact SeparatedBands.fast_safe_at_boundary hqZ (by exact_mod_cast hqp)
      hdQ hdP hδ (by simpa [add_comm] using hsepR) hu



theorem mem_bandsOn {W : Finset ℕ} {δ L U : ℝ} {p : ℕ} {j : ℤ} :
    (p,j) ∈ bandsOn W δ L U ↔
      p ∈ W ∧ ⌊(p:ℝ)*L-δ⌋ ≤ j ∧ j ≤ ⌈(p:ℝ)*U+δ⌉ := by
  simp [bandsOn]

theorem band_index_mem {W : Finset ℕ} {δ L U t : ℝ} {p : ℕ} {j : ℤ}
    (hp : p ∈ W) (ht : t ∈ Icc L U) (hband : t ∈ band δ (p,j)) :
    (p,j) ∈ bandsOn W δ L U := by
  change |(p:ℝ)*t-j| ≤ δ at hband
  apply mem_bandsOn.mpr
  refine ⟨hp,?_,?_⟩
  · have hmul := mul_le_mul_of_nonneg_left ht.1 (Nat.cast_nonneg p : (0:ℝ) ≤ p)
    have hfloor := Int.floor_le ((p:ℝ)*L-δ)
    have hh := (abs_le.mp hband).2
    have hle : (⌊(p:ℝ)*L-δ⌋:ℝ) ≤ j := by linarith
    exact_mod_cast hle
  · have hmul := mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg p : (0:ℝ) ≤ p)
    have hceil := Int.le_ceil ((p:ℝ)*U+δ)
    have hh := (abs_le.mp hband).1
    have hle : (j:ℝ) ≤ ⌈(p:ℝ)*U+δ⌉ := by linarith
    exact_mod_cast hle







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
open LonelyRunner.InteractionComponents
open Set

/-- All coverage in an interval through a primitive center of a smallest
repair comes from its side of a separated cut. -/
theorem solution {n r m b : ℕ} {a c : ℤ} {W C : Finset ℕ} {L U : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hm : 0 < m)
    (hC : C ⊆ W) (hpC : m*r ∈ C) (hW : ∀ p ∈ W, 0 < p)
    (hcut : SeparatedCut n W C)
    (hmin : ∀ q ∈ W, r ∣ q → m*r ≤ q)
    (hu : a*(b:ℤ)-c*(r:ℤ)=1)
    (hcenter : (a:ℝ)/r ∈ Icc L U)
    (hcover : ∀ t ∈ Icc L U, ∃ q ∈ W, ndist ((q:ℝ)*t) ≤ 1/(n:ℝ)) :
    ∀ t ∈ Icc L U, ∃ p ∈ C, ndist ((p:ℝ)*t) ≤ 1/(n:ℝ) := by
  classical
  let T := bandsOn W (1/(n:ℝ)) L U
  let F := band (1/(n:ℝ))
  let side : ℕ × ℤ → Prop := fun i => i.1 ∈ C
  let seed : ℕ × ℤ := (m*r,(m:ℤ)*a)
  have hδ : (0:ℝ) < 1/n := by positivity
  have hseedval : ((m*r:ℕ):ℝ)*((a:ℝ)/r) = ((m:ℤ)*a:ℤ) := by
    have hrR : (r:ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hseedband : (a:ℝ)/r ∈ F seed := by
    change |((m*r:ℕ):ℝ)*((a:ℝ)/r)-((m:ℤ)*a:ℤ)| ≤ 1/(n:ℝ)
    rw [hseedval,sub_self,abs_zero]
    exact hδ.le
  have hseedT : seed ∈ T := band_index_mem (hC hpC) hcenter hseedband
  have hcross : ∀ i ∈ T, ∀ j ∈ T, side i → ¬ side j →
      (F i ∩ F j).Nonempty → F i ⊂ F j ∨ F j ⊂ F i := by
    intro i hi j hj hiC hjC hinter
    change i.1 ∈ C at hiC
    change j.1 ∉ C at hjC
    have hiW := (mem_bandsOn.mp hi).1
    have hjW := (mem_bandsOn.mp hj).1
    have hne : i.1 ≠ j.1 := by intro h; exact hjC (h ▸ hiC)
    exact bands_nested hn (hW _ hiW) (hW _ hjW) hne (hcut _ hiC _ hjW hjC) hinter
  have hsub : Icc L U ⊆ ⋃ i ∈ T, F i := by
    intro t ht
    obtain ⟨q,hq,hbad⟩ := hcover t ht
    let j : ℤ := round ((q:ℝ)*t)
    have htband : t ∈ F (q,j) := hbad
    exact Set.mem_iUnion₂.mpr ⟨(q,j),band_index_mem hq ht htband,htband⟩
  have hno : ∀ j ∈ T, ¬ side j → ¬ F seed ⊆ F j := by
    intro j hj hjC hsubset
    change j.1 ∉ C at hjC
    have hjW := (mem_bandsOn.mp hj).1
    let t : ℝ := (a:ℝ)/r-1/((n:ℝ)*m*r)
    have hcase : m*r < j.1 ∨ ¬ r ∣ j.1 := by
      by_cases hlt : m*r < j.1
      · exact Or.inl hlt
      · right
        intro hd
        have hle := hmin _ hjW hd
        have heq : m*r=j.1 := by omega
        exact hjC (heq ▸ hpC)
    have hsafe := SeparatedMulti.other_safe_at_boundary hn hr hm (hW _ hjW)
      hu (hcut _ hpC _ hjW hjC) hcase
    have htseed : t ∈ F seed := by
      have hnR : (n:ℝ) ≠ 0 := by positivity
      have hmR : (m:ℝ) ≠ 0 := by positivity
      have hrR : (r:ℝ) ≠ 0 := by positivity
      have hval : ((m*r:ℕ):ℝ)*t = ((m:ℤ)*a:ℤ)-1/(n:ℝ) := by
        dsimp [t]
        push_cast
        field_simp
      change |((m*r:ℕ):ℝ)*t-((m:ℤ)*a:ℤ)| ≤ 1/(n:ℝ)
      rw [hval,sub_sub_cancel_left,abs_neg,abs_of_pos hδ]
    exact (not_le_of_gt hsafe) ((ndist_le_abs_sub _ j.2).trans (hsubset htseed))
  have hloc := LaminarCover.localize T F side (fun i _ => band_closed _ i)
    hcross isPreconnected_Icc hsub hseedT hno hcenter hseedband
  intro t ht
  obtain ⟨i,hi,htband⟩ := Set.mem_iUnion₂.mp (hloc ht)
  exact ⟨i.1,(Finset.mem_filter.mp hi).2,(ndist_le_abs_sub _ i.2).trans htband⟩
