-- Prove2me | solution 1 for MasulloRH.critical_zero_band_of_signed_brackets
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:36:37.937556+00:00
-- url     : https://prove2.me/submissions/e66e2d27-55e6-466e-9790-0a4b4d3a9628

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_riemannZeta_conj
import Theorems.Thm_ZetaZeroLocalization_completedZeta_im_eq_zero
import Mathlib

open Set Finset
open scoped ComplexConjugate
open MasulloRH
private abbrev FullZero := ZetaZerosInTraceStrip (1/2)
private noncomputable def axis (t : ℝ) : ℂ := 1/2+(t:ℂ)*Complex.I
private noncomputable def signValue (t : ℝ) := (completedRiemannZeta (axis t)).re
private theorem axis_re (t : ℝ) : (axis t).re=1/2 := by norm_num [axis,Complex.div_re]
private theorem axis_im (t : ℝ) : (axis t).im=t := by norm_num [axis,Complex.div_im]
private theorem axis_ne_zero (t : ℝ) : axis t ≠ 0 := fun h => by have hh := congrArg Complex.re h;rw [axis_re,Complex.zero_re] at hh;norm_num at hh
private theorem axis_ne_one (t : ℝ) : axis t ≠ 1 := fun h => by have hh := congrArg Complex.re h;rw [axis_re,Complex.one_re] at hh;norm_num at hh

private theorem from_signs {a b : ℝ} (hab : a < b) (hs : signValue a * signValue b < 0) :
    ∃ z : FullZero, z.val.re = 1/2 ∧ z.val.im ∈ Set.Ioo a b := by
  have hg : Continuous signValue := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hX : Continuous axis := by unfold axis; fun_prop
    exact Complex.continuous_re.continuousAt.comp ((differentiableAt_completedZeta (axis_ne_zero x) (axis_ne_one x)).continuousAt.comp hX.continuousAt)
  have hr : 0 ∈ signValue '' Set.Ioo a b := by
    rcases mul_neg_iff.mp hs with h|h
    · exact intermediate_value_Ioo' hab.le hg.continuousOn ⟨h.2,h.1⟩
    · exact intermediate_value_Ioo hab.le hg.continuousOn ⟨h.1,h.2⟩
  obtain ⟨t,ht,ht0⟩ := hr
  have hz : completedRiemannZeta (axis t)=0 := Complex.ext ht0 (ZetaZeroLocalization.completedZeta_im_eq_zero t)
  have hz' : riemannZeta (axis t)=0 := by rw [riemannZeta_def_of_ne_zero (axis_ne_zero t),hz,zero_div]
  let z : FullZero := ⟨axis t,hz',by rw [axis_re];norm_num,by rw [axis_re];norm_num,by rw [axis_re];norm_num⟩
  exact ⟨z,axis_re t,(axis_im t) ▸ ht⟩

private noncomputable def conjZero (z : FullZero) : FullZero :=
  ⟨conj z.val, by rw [riemannZeta_conj,z.prop.1,map_zero], by simpa using z.prop.2⟩
private noncomputable def reflectZero (z : FullZero) : FullZero := by
  have hnot (j : ℕ) : z.val ≠ -j := by
    intro e; have h := congrArg Complex.re e; simp only [Complex.neg_re,Complex.natCast_re] at h
    linarith [z.prop.2.1,j.cast_nonneg (α:=ℝ)]
  have h1 : z.val ≠ 1 := fun e => by have h := congrArg Complex.re e; simp only [Complex.one_re] at h; linarith [z.prop.2.2.1]
  refine ⟨1-z.val,by rw [riemannZeta_one_sub hnot h1,z.prop.1,mul_zero],?_,?_,?_⟩
  · simp only [Complex.sub_re,Complex.one_re];linarith [z.prop.2.2.1]
  · simp only [Complex.sub_re,Complex.one_re];linarith [z.prop.2.1]
  · simp only [Complex.sub_re,Complex.one_re]; rw [show 1-z.val.re-1/2 = -(z.val.re-1/2) by ring,abs_neg];exact z.prop.2.2.2

private theorem one_missing {L H : ℝ} (Q : Finset FullZero)
    (hQ : ∀ z ∈ Q, L < z.val.im ∧ z.val.im ≤ H ∧ z.val.re=1/2)
    (hb : Set.encard {z : FullZero | L<z.val.im ∧ z.val.im≤H} ≤ ((Q.card+1:ℕ):ℕ∞))
    (z : FullZero) (hz : L < z.val.im ∧ z.val.im ≤ H) : z.val.re=1/2 := by
  classical
  by_contra hc
  let w := reflectZero (conjZero z)
  have hwre : w.val.re=1-z.val.re := by change (1-conj z.val).re=1-z.val.re;simp
  have hwim : w.val.im=z.val.im := by change (1-conj z.val).im=z.val.im;simp
  have hzw : z≠w := fun h => by have he := congrArg (fun v : FullZero => v.val.re) h;change z.val.re=w.val.re at he;rw [hwre] at he;apply hc;linarith
  have hzQ : z ∉ Q := fun h => hc (hQ z h).2.2
  have hwQ : w ∉ Q := fun h => hc (by have he := (hQ w h).2.2; rw [hwre] at he;linarith)
  let R := insert z (insert w Q)
  have hcard : R.card=Q.card+2 := by simp [R,Finset.card_insert_of_notMem,hwQ,hzQ,hzw]
  have hsub : (R:Set FullZero) ⊆ {v | L<v.val.im ∧ v.val.im≤H} := by
    intro v hv
    have hv' : v=z ∨ v=w ∨ v∈Q := by simpa [R] using hv
    rcases hv' with rfl|rfl|h
    · exact hz
    · simpa only [Set.mem_setOf_eq,hwim] using hz
    · exact ⟨(hQ v h).1,(hQ v h).2.1⟩
  have hle := (Set.encard_le_encard hsub).trans hb
  rw [Set.encard_coe_eq_coe_finsetCard,hcard] at hle
  have hnat : Q.card+2 ≤ Q.card+1 := by exact_mod_cast hle
  omega

private theorem make_witnesses (L H : ℝ) (E : Finset FullZero) (B : Finset (ℚ×ℚ))
    (hE : ∀ z ∈ E, L < z.val.im ∧ z.val.im ≤ H ∧ z.val.re=1/2)
    (hB : ∀ i ∈ B, L ≤ (i.1:ℝ) ∧ i.1 < i.2 ∧ (i.2:ℝ) ≤ H ∧ signValue i.1 * signValue i.2 < 0)
    (hD : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (Set.Ioo (i.1:ℝ) (i.2:ℝ)) (Set.Ioo (j.1:ℝ) (j.2:ℝ)))
    (hED : ∀ z ∈ E, ∀ i ∈ B, z.val.im ∉ Set.Ioo (i.1:ℝ) (i.2:ℝ)) :
    ∃ Q : Finset FullZero, Q.card=E.card+B.card ∧ ∀ z ∈ Q, L<z.val.im ∧ z.val.im≤H ∧ z.val.re=1/2 := by
  classical
  have hbr (i : B) := from_signs (a:=(i.val.1:ℝ)) (b:=(i.val.2:ℝ))
    (by exact_mod_cast (hB i.val i.prop).2.1) (hB i.val i.prop).2.2.2
  choose root hr using hbr
  have hinj : Function.Injective root := by
    intro i j he
    apply Subtype.ext
    by_contra hn
    have hd := Set.disjoint_left.mp (hD i.val i.prop j.val j.prop hn)
    exact hd (hr i).2 (he ▸ (hr j).2)
  let F := B.attach.image root
  have hc : F.card=B.card := by rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
  have hd : Disjoint E F := by
    apply Finset.disjoint_left.mpr
    intro z hz hzF
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hzF
    exact hED _ hz i.val i.prop (hr i).2
  refine ⟨E ∪ F,by rw [Finset.card_union_of_disjoint hd,hc],?_⟩
  intro z hz
  rcases Finset.mem_union.mp hz with h | h
  · exact hE z h
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
    have hs := (hr i).2
    exact ⟨(hB i.val i.prop).1.trans_lt hs.1, hs.2.le.trans (hB i.val i.prop).2.2.1,(hr i).1⟩

theorem solution (L H : ℝ)
    (E : Finset (ZetaZerosInTraceStrip (1/2))) (B : Finset (ℚ×ℚ))
    (hE : ∀ z ∈ E, L < z.val.im ∧ z.val.im ≤ H ∧ z.val.re=1/2)
    (hB : ∀ i ∈ B, L ≤ (i.1:ℝ) ∧ i.1 < i.2 ∧ (i.2:ℝ) ≤ H ∧
      (completedRiemannZeta (1/2 + (i.1:ℂ)*Complex.I)).re * (completedRiemannZeta (1/2 + (i.2:ℂ)*Complex.I)).re < 0)
    (hD : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (Set.Ioo (i.1:ℝ) (i.2:ℝ)) (Set.Ioo (j.1:ℝ) (j.2:ℝ)))
    (hED : ∀ z ∈ E, ∀ i ∈ B, z.val.im ∉ Set.Ioo (i.1:ℝ) (i.2:ℝ))
    (hcount : Set.encard {z : ZetaZerosInTraceStrip (1/2) | L<z.val.im ∧ z.val.im≤H} ≤ ((E.card+B.card+1:ℕ):ℕ∞)) :
    ∀ z : ZetaZerosInTraceStrip (1/2), L < |z.val.im| → |z.val.im| ≤ H → z.val.re=1/2 := by
  have hb : ∀ i ∈ B, L ≤ (i.1:ℝ) ∧ i.1 < i.2 ∧ (i.2:ℝ)≤H ∧ signValue i.1 * signValue i.2 < 0 := by
    simpa [signValue,axis] using hB
  obtain ⟨Q,hcard,hQ⟩ := make_witnesses L H E B hE hb hD hED
  rw [←hcard] at hcount
  intro z hlo hhi
  by_cases hpos : 0 ≤ z.val.im
  · rw [abs_of_nonneg hpos] at hlo hhi
    exact one_missing Q hQ hcount z ⟨hlo,hhi⟩
  · rw [abs_of_neg (lt_of_not_ge hpos)] at hlo hhi
    have h := one_missing Q hQ hcount (conjZero z) (by change L < (conj z.val).im ∧ (conj z.val).im ≤ H; simpa using And.intro hlo hhi)
    exact h
