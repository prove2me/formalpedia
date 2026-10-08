-- Prove2me | solution 1 for Helfgott.major_arc_integral_decomposition_explicit
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T07:27:13.588135+00:00
-- url     : https://prove2.me/submissions/c1105255-60bd-4e68-ba65-4047f6a7f460

import Definitions.Def_Helfgott_ArcCounting
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
open MeasureTheory Set Metric

namespace Helfgott

theorem circle_arc_integral (f : AddCircle (1:ℝ) → ℂ) (c ε : ℝ)
    (hε : ε ≤ (1/2:ℝ)) :
    (∫ α in ball (c : AddCircle (1:ℝ)) ε,f α ∂AddCircle.haarAddCircle) =
      ∫ t in Ioo (c-ε) (c+ε),f (t : AddCircle (1:ℝ)) := by
  have hv : (volume : Measure (AddCircle (1:ℝ))) = AddCircle.haarAddCircle := by
    simpa only [ENNReal.ofReal_one,one_smul] using AddCircle.volume_eq_smul_haarAddCircle (T:=1)
  rw [← hv,← integral_indicator measurableSet_ball]
  rw [← AddCircle.integral_preimage (1:ℝ) (c-1/2)]
  have hcoe (t : ℝ) (ht : t ∈ Ioc (c-1/2) (c-1/2+1)) :
      ((t : AddCircle (1:ℝ)) ∈ ball (c : AddCircle (1:ℝ)) ε) ↔
        t ∈ Ioo (c-ε) (c+ε) := by
    have htlo := (mem_Ioc.mp ht).1
    have hthi := (mem_Ioc.mp ht).2
    have habs : |t-c| ≤ (1:ℝ)/2 := by apply abs_le.mpr;constructor <;>linarith
    have hn : ‖((t-c:ℝ) : AddCircle (1:ℝ))‖ = |t-c| :=
      (AddCircle.norm_coe_eq_abs_iff (1:ℝ) (by norm_num)).mpr (by simpa using habs)
    simp only [mem_ball,dist_eq_norm,← AddCircle.coe_sub,hn,mem_Ioo]
    rw [abs_lt]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  have he : (∫ t in Ioc (c-1/2) (c-1/2+1),
      (ball (c : AddCircle (1:ℝ)) ε).indicator f (t : AddCircle (1:ℝ))) =
      ∫ t in Ioc (c-1/2) (c-1/2+1),
        (Ioo (c-ε) (c+ε)).indicator (fun t : ℝ => f (t : AddCircle (1:ℝ))) t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    by_cases hm : t ∈ Ioo (c-ε) (c+ε)
    · rw [Set.indicator_of_mem ((hcoe t ht).mpr hm),Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem (fun hc => hm ((hcoe t ht).mp hc)),Set.indicator_of_notMem hm]
  rw [he,setIntegral_indicator measurableSet_Ioo]
  have hs : Ioo (c-ε) (c+ε) ⊆ Ioc (c-1/2) (c-1/2+1) := by
    intro t ht
    rcases mem_Ioo.mp ht with ⟨hl,hr⟩
    exact mem_Ioc.mpr ⟨by linarith,by linarith⟩
  rw [inter_eq_right.mpr hs]

theorem circle_arc_integral_scaled (f : AddCircle (1:ℝ) → ℂ) (c ε x : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ (1/2:ℝ)) (hx : 0 < x) :
    (∫ α in ball (c : AddCircle (1:ℝ)) ε,f α ∂AddCircle.haarAddCircle) =
      x⁻¹ • (∫ β in Icc (-(x*ε)) (x*ε),f ((c+β/x : ℝ) : AddCircle (1:ℝ))) := by
  calc
    _ = ∫ t in Ioo (c-ε) (c+ε),f (t : AddCircle (1:ℝ)) := circle_arc_integral f c ε hε
    _ = ∫ u in (-ε)..ε,f ((c+u : ℝ) : AddCircle (1:ℝ)) := by
      rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by linarith : c-ε ≤ c+ε)]
      simpa only [sub_eq_add_neg] using
        (intervalIntegral.integral_comp_add_left (f:=fun t : ℝ => f (t : AddCircle (1:ℝ)))
          (a:= -ε) (b:=ε) c).symm
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by nlinarith : -(x*ε) ≤ x*ε)]
      have hs := intervalIntegral.integral_comp_div
        (f:=fun u : ℝ => f ((c+u : ℝ) : AddCircle (1:ℝ)))
        (a:= -(x*ε)) (b:=x*ε) hx.ne'
      simp only [neg_div,mul_div_cancel_left₀ ε hx.ne'] at hs
      rw [hs,smul_smul,inv_mul_cancel₀ hx.ne',one_smul]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Metric

namespace Helfgott

lemma reduced_fraction_cross_eq {a q b d : ℕ} (hq : 0 < q) (hd : 0 < d)
    (haq : Nat.Coprime a q) (hbd : Nat.Coprime b d) (he : a*d = b*q) :
    a = b ∧ q = d := by
  have hqd : q ∣ d := haq.symm.dvd_of_dvd_mul_left (by rw [he];exact dvd_mul_left q b)
  have hdq : d ∣ q := hbd.symm.dvd_of_dvd_mul_left (by rw [← he];exact dvd_mul_left d a)
  have hqdEq : q = d := Nat.dvd_antisymm hqd hdq
  have hab : a = b := Nat.eq_of_mul_eq_mul_right hd (by simpa only [hqdEq] using he)
  exact ⟨hab,hqdEq⟩

lemma reduced_fraction_circle_separation {a q b d : ℕ} (hq : 0 < q) (hd : 0 < d)
    (ha : a < q) (hb : b < d) (haq : Nat.Coprime a q) (hbd : Nat.Coprime b d)
    (hne : (a,q) ≠ (b,d)) :
    1/((q:ℝ)*(d:ℝ)) ≤ dist ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ))
      ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  let δ : ℝ := (a:ℝ)/(q:ℝ)-(b:ℝ)/(d:ℝ)
  let k : ℤ := (a:ℤ)*(d:ℤ)-(b:ℤ)*(q:ℤ)-round δ*(q:ℤ)*(d:ℤ)
  have hδlo : -1 < δ := by
    have hba : (b:ℝ)/(d:ℝ) < 1 := (div_lt_one hdR).mpr (by exact_mod_cast hb)
    have haa : 0 ≤ (a:ℝ)/(q:ℝ) := by positivity
    dsimp [δ]
    linarith
  have hδhi : δ < 1 := by
    have haa : (a:ℝ)/(q:ℝ) < 1 := (div_lt_one hqR).mpr (by exact_mod_cast ha)
    have hba : 0 ≤ (b:ℝ)/(d:ℝ) := by positivity
    dsimp [δ]
    linarith
  have hk : (k:ℝ) = (q:ℝ)*(d:ℝ)*(δ-(round δ:ℝ)) := by
    dsimp [k,δ]
    push_cast
    field_simp
  have hk0 : k ≠ 0 := by
    intro hzero
    have hzR : (k:ℝ) = 0 := by exact_mod_cast hzero
    rw [hk] at hzR
    have hδ : δ = (round δ:ℝ) := by
      have hδ0 := (mul_eq_zero.mp hzR).resolve_left (by positivity)
      exact sub_eq_zero.mp hδ0
    have hroundlo : (-1:ℤ) < round δ := by exact_mod_cast (hδ.symm ▸ hδlo)
    have hroundhi : round δ < (1:ℤ) := by exact_mod_cast (hδ.symm ▸ hδhi)
    have hround : round δ = 0 := by omega
    have hcrossR : (a:ℝ)*(d:ℝ) = (b:ℝ)*(q:ℝ) := by
      rw [hround,Int.cast_zero] at hδ
      dsimp only [δ] at hδ
      have ht := (sub_eq_zero.mp hδ)
      exact (div_eq_div_iff hqR.ne' hdR.ne').mp ht
    have hcross : a*d = b*q := by exact_mod_cast hcrossR
    rcases reduced_fraction_cross_eq hq hd haq hbd hcross with ⟨hab,hqd⟩
    exact hne (Prod.ext hab hqd)
  have hkabs : 1 ≤ |(k:ℝ)| := by
    rcases lt_or_gt_of_ne hk0 with hneg | hpos
    · have hkneg : (k:ℝ) < 0 := by exact_mod_cast hneg
      rw [abs_of_neg hkneg]
      have hh : k ≤ -1 := by omega
      have hhR : (k:ℝ) ≤ -1 := by exact_mod_cast hh
      linarith
    · have hkpos : (0:ℝ) < k := by exact_mod_cast hpos
      rw [abs_of_pos hkpos]
      exact_mod_cast (show (1:ℤ) ≤ k by omega)
  have hnorm : dist ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ))
      ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) = |δ-(round δ:ℝ)| := by
    rw [dist_eq_norm,← QuotientAddGroup.mk_sub,AddCircle.norm_eq]
    simp only [inv_one,one_mul,mul_one]
    rfl
  rw [hnorm]
  apply (div_le_iff₀ (mul_pos hqR hdR)).mpr
  rw [hk,abs_mul,abs_of_pos (mul_pos hqR hdR)] at hkabs
  simpa only [mul_comm] using hkabs

theorem major_arc_balls_disjoint {a q b d r : ℕ} {x : ℝ}
    (hq : 0 < q) (hd : 0 < d) (ha : a < q) (hb : b < d)
    (haq : Nat.Coprime a q) (hbd : Nat.Coprime b d)
    (hqr : q ≤ 2*r) (hdr : d ≤ 2*r) (hx : 32*(r:ℝ)^2 < x)
    (hne : (a,q) ≠ (b,d)) :
    Disjoint (ball ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) (8*(r:ℝ)/((q:ℝ)*x)))
      (ball ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) (8*(r:ℝ)/((d:ℝ)*x))) := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hxR : 0 < x := lt_of_le_of_lt (by positivity) hx
  have hqrR : (q:ℝ) ≤ 2*r := by exact_mod_cast hqr
  have hdrR : (d:ℝ) ≤ 2*r := by exact_mod_cast hdr
  have hsep := reduced_fraction_circle_separation hq hd ha hb haq hbd hne
  have hrad : 8*(r:ℝ)/((q:ℝ)*x)+8*(r:ℝ)/((d:ℝ)*x) < 1/((q:ℝ)*(d:ℝ)) := by
    apply (lt_div_iff₀ (mul_pos hqR hdR)).mpr
    have he : (8*(r:ℝ)/((q:ℝ)*x)+8*(r:ℝ)/((d:ℝ)*x))*((q:ℝ)*(d:ℝ)) =
        8*(r:ℝ)*((q:ℝ)+(d:ℝ))/x := by
      field_simp
      ring
    rw [he]
    apply (div_lt_one hxR).mpr
    have hsum : (q:ℝ)+(d:ℝ) ≤ 4*r := by linarith
    have hm := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 8*(r:ℝ))
    nlinarith
  apply Set.disjoint_left.mpr
  intro α hαq hαd
  have hdcenter := dist_triangle ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) α
    ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ))
  have hqdist := mem_ball.mp hαq
  have hddist := mem_ball.mp hαd
  rw [dist_comm _ α] at hdcenter
  linarith

theorem actual_major_arc_rational_unique {a q b d r : ℕ} {x : ℝ}
    (α : AddCircle (1:ℝ)) (hq : 0 < q) (hd : 0 < d)
    (ha : a < q) (hb : b < d) (haq : Nat.Coprime a q) (hbd : Nat.Coprime b d)
    (hx : 32*(r:ℝ)^2 < x)
    (hαq : (Odd q ∧ q ≤ r ∧ dist α ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) <
        8*r/(2*q*x)) ∨
      (Even q ∧ q ≤ 2*r ∧ dist α ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) < 8*r/(q*x)))
    (hαd : (Odd d ∧ d ≤ r ∧ dist α ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) <
        8*r/(2*d*x)) ∨
      (Even d ∧ d ≤ 2*r ∧ dist α ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) < 8*r/(d*x))) :
    a = b ∧ q = d := by
  have hxR : 0 < x := lt_of_le_of_lt (by positivity) hx
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hqr : q ≤ 2*r := by rcases hαq with h | h <;> omega
  have hdr : d ≤ 2*r := by rcases hαd with h | h <;> omega
  have hqball : α ∈ ball ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) (8*(r:ℝ)/((q:ℝ)*x)) := by
    apply mem_ball.mpr
    rcases hαq with h | h
    · apply h.2.2.trans_le
      have hden : (0:ℝ) < q*x := mul_pos hqR hxR
      have hnum : 0 ≤ 8*(r:ℝ) := by positivity
      apply div_le_div_of_nonneg_left hnum hden
      nlinarith
    · exact h.2.2
  have hdball : α ∈ ball ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) (8*(r:ℝ)/((d:ℝ)*x)) := by
    apply mem_ball.mpr
    rcases hαd with h | h
    · apply h.2.2.trans_le
      have hden : (0:ℝ) < d*x := mul_pos hdR hxR
      have hnum : 0 ≤ 8*(r:ℝ) := by positivity
      apply div_le_div_of_nonneg_left hnum hden
      nlinarith
    · exact h.2.2
  by_contra hh
  have hne : (a,q) ≠ (b,d) := by
    intro he
    exact hh ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩
  exact Set.disjoint_left.mp (major_arc_balls_disjoint hq hd ha hb haq hbd hqr hdr hx hne) hqball hdball

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
open MeasureTheory Set Metric Finset Function
open scoped BigOperators

namespace Helfgott

noncomputable def actualArcDenominators (r : ℕ) : Finset ℕ :=
  (Finset.Icc 1 r).filter (fun q => Odd q) ∪
    (Finset.Icc 1 (2*r)).filter (fun q => Even q)

noncomputable def actualArcIndices (r : ℕ) : Finset (Σ _ : ℕ,ℕ) :=
  (actualArcDenominators r).sigma (fun q => (range q).filter (fun a => Nat.Coprime a q))

noncomputable def actualArcRadius (r q : ℕ) (x : ℝ) : ℝ :=
  if Odd q then 4*(r:ℝ)/((q:ℝ)*x) else 8*(r:ℝ)/((q:ℝ)*x)

lemma actualArcIndices_mem (r : ℕ) (i : Σ _ : ℕ,ℕ) :
    i ∈ actualArcIndices r ↔ 0 < i.1 ∧ i.2 < i.1 ∧ Nat.Coprime i.2 i.1 ∧
      ((Odd i.1 ∧ i.1 ≤ r) ∨ (Even i.1 ∧ i.1 ≤ 2*r)) := by
  classical
  simp only [actualArcIndices,actualArcDenominators,Finset.mem_sigma,Finset.mem_union,
    Finset.mem_filter,Finset.mem_Icc,Finset.mem_range]
  constructor
  · rintro ⟨h,ha,hcop⟩
    rcases h with ⟨⟨hpos,hqr⟩,ho⟩ | ⟨⟨hpos,hqr⟩,he⟩
    · exact ⟨hpos,ha,hcop,Or.inl ⟨ho,hqr⟩⟩
    · exact ⟨hpos,ha,hcop,Or.inr ⟨he,hqr⟩⟩
  · rintro ⟨hpos,ha,hcop,h⟩
    constructor
    · rcases h with ⟨ho,hqr⟩ | ⟨he,hqr⟩
      · exact Or.inl ⟨⟨hpos,hqr⟩,ho⟩
      · exact Or.inr ⟨⟨hpos,hqr⟩,he⟩
    · exact ⟨ha,hcop⟩

lemma actualArcRadius_odd (r q : ℕ) (x : ℝ) (ho : Odd q) :
    actualArcRadius r q x = 8*r/(2*q*x) := by
  rw [actualArcRadius,if_pos ho]
  ring_nf

lemma actualArcRadius_even (r q : ℕ) (x : ℝ) (he : Even q) :
    actualArcRadius r q x = 8*r/(q*x) := by
  rw [actualArcRadius,if_neg (Nat.not_odd_iff_even.mpr he)]

lemma majorArcs_eq_indexed_balls (r : ℕ) (x : ℝ) :
    majorArcs 8 r x = ⋃ i ∈ actualArcIndices r,
      ball ((i.2:ℝ)/(i.1:ℝ) : AddCircle (1:ℝ)) (actualArcRadius r i.1 x) := by
  ext α
  constructor
  · rintro ⟨q,a,hq,ha,hcop,h⟩
    have hi : (⟨q,a⟩ : Σ _ : ℕ,ℕ) ∈ actualArcIndices r := by
      apply (actualArcIndices_mem r _).mpr
      exact ⟨hq,ha,hcop,h.elim (fun hh => Or.inl ⟨hh.1,hh.2.1⟩)
        (fun hh => Or.inr ⟨hh.1,hh.2.1⟩)⟩
    apply mem_iUnion.mpr
    refine ⟨⟨q,a⟩,mem_iUnion.mpr ⟨hi,?_⟩⟩
    apply mem_ball.mpr
    rcases h with ⟨ho,hqr,hα⟩ | ⟨he,hqr,hα⟩
    · simpa only [actualArcRadius_odd r q x ho] using hα
    · simpa only [actualArcRadius_even r q x he] using hα
  · intro hα
    rcases mem_iUnion.mp hα with ⟨i,hα⟩
    rcases mem_iUnion.mp hα with ⟨hi,hα⟩
    rcases (actualArcIndices_mem r i).mp hi with ⟨hq,ha,hcop,h⟩
    refine ⟨i.1,i.2,hq,ha,hcop,?_⟩
    have hd := mem_ball.mp hα
    rcases h with ⟨ho,hqr⟩ | ⟨he,hqr⟩
    · exact Or.inl ⟨ho,hqr,by simpa only [actualArcRadius_odd r i.1 x ho] using hd⟩
    · exact Or.inr ⟨he,hqr,by simpa only [actualArcRadius_even r i.1 x he] using hd⟩

lemma actualArcRadius_bounds (r q : ℕ) (x : ℝ) (hr : 0 < r) (hq : 0 < q)
    (hx : 32*(r:ℝ)^2 < x) :
    0 ≤ actualArcRadius r q x ∧ actualArcRadius r q x ≤ (1/2:ℝ) ∧
      actualArcRadius r q x ≤ 8*(r:ℝ)/((q:ℝ)*x) := by
  have hxR : 0 < x := lt_of_le_of_lt (by positivity) hx
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hqone : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hupper : actualArcRadius r q x ≤ 8*(r:ℝ)/((q:ℝ)*x) := by
    unfold actualArcRadius
    split_ifs <;> apply div_le_div_of_nonneg_right _ (by positivity) <;> nlinarith
  have hhalf : 8*(r:ℝ)/((q:ℝ)*x) ≤ (1/2:ℝ) := by
    apply (div_le_iff₀ (mul_pos hqR hxR)).mpr
    have hqx : x ≤ (q:ℝ)*x := by nlinarith
    have hrsq : (r:ℝ) ≤ (r:ℝ)^2 := by nlinarith
    nlinarith
  refine ⟨?_,hupper.trans hhalf,hupper⟩
  unfold actualArcRadius
  split_ifs <;> positivity

lemma actualArcBalls_pairwise (r : ℕ) (x : ℝ) (hr : 0 < r) (hx : 32*(r:ℝ)^2 < x) :
    Set.Pairwise (↑(actualArcIndices r)) (Disjoint on (fun i : Σ _ : ℕ,ℕ =>
      ball ((i.2:ℝ)/(i.1:ℝ) : AddCircle (1:ℝ)) (actualArcRadius r i.1 x))) := by
  intro i hi j hj hij
  rcases (actualArcIndices_mem r i).mp hi with ⟨hqi,hai,hcopi,hri⟩
  rcases (actualArcIndices_mem r j).mp hj with ⟨hqj,haj,hcopj,hrj⟩
  have hri' : i.1 ≤ 2*r := by rcases hri with h | h <;> omega
  have hrj' : j.1 ≤ 2*r := by rcases hrj with h | h <;> omega
  have hne : (i.2,i.1) ≠ (j.2,j.1) := by
    intro he
    have hq : i.1 = j.1 := congrArg Prod.snd he
    have ha : i.2 = j.2 := congrArg Prod.fst he
    exact hij (Sigma.ext hq (by simpa using ha))
  have hd := major_arc_balls_disjoint hqi hqj hai haj hcopi hcopj hri' hrj' hx hne
  exact hd.mono (ball_subset_ball (actualArcRadius_bounds r i.1 x hr hqi hx).2.2)
    (ball_subset_ball (actualArcRadius_bounds r j.1 x hr hqj hx).2.2)

lemma actualArcRadius_scaled (r q : ℕ) (x : ℝ) (hq : 0 < q) (hx : 0 < x) :
    x*actualArcRadius r q x =
      (if Odd q then 4*(r:ℝ)/(q:ℝ) else 8*(r:ℝ)/(q:ℝ)) := by
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold actualArcRadius
  split_ifs <;> field_simp

theorem major_arc_integral_decomposition (r : ℕ) (x : ℝ) (hr : 0 < r)
    (hx : 32*(r:ℝ)^2 < x) (f : AddCircle (1:ℝ) → ℂ)
    (hf : Integrable f AddCircle.haarAddCircle) :
    (∫ α in majorArcs 8 r x,f α ∂AddCircle.haarAddCircle) =
      x⁻¹ • (∑ q ∈ actualArcDenominators r,
        ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ∫ β in Set.Icc (-(if Odd q then 4*(r:ℝ)/(q:ℝ) else 8*(r:ℝ)/(q:ℝ)))
            (if Odd q then 4*(r:ℝ)/(q:ℝ) else 8*(r:ℝ)/(q:ℝ)),
            f (((a:ℝ)/(q:ℝ)+β/x : ℝ) : AddCircle (1:ℝ))) := by
  classical
  have hxR : 0 < x := lt_of_le_of_lt (by positivity) hx
  rw [majorArcs_eq_indexed_balls]
  rw [integral_biUnion_finset (actualArcIndices r) (fun i hi => measurableSet_ball)
    (actualArcBalls_pairwise r x hr hx) (fun i hi => hf.integrableOn)]
  have he (i : Σ _ : ℕ,ℕ) (hi : i ∈ actualArcIndices r) :
      (∫ α in ball ((i.2:ℝ)/(i.1:ℝ) : AddCircle (1:ℝ)) (actualArcRadius r i.1 x),
        f α ∂AddCircle.haarAddCircle) =
      x⁻¹ • (∫ β in Set.Icc (-(if Odd i.1 then 4*(r:ℝ)/(i.1:ℝ) else 8*(r:ℝ)/(i.1:ℝ)))
        (if Odd i.1 then 4*(r:ℝ)/(i.1:ℝ) else 8*(r:ℝ)/(i.1:ℝ)),
        f (((i.2:ℝ)/(i.1:ℝ)+β/x : ℝ) : AddCircle (1:ℝ))) := by
    have hq := ((actualArcIndices_mem r i).mp hi).1
    have hb := actualArcRadius_bounds r i.1 x hr hq hx
    simpa only [actualArcRadius_scaled r i.1 x hq hxR] using
      circle_arc_integral_scaled f ((i.2:ℝ)/(i.1:ℝ)) (actualArcRadius r i.1 x) x hb.1 hb.2.1 hxR
  rw [Finset.sum_congr rfl he,← Finset.smul_sum]
  simp only [actualArcIndices,Finset.sum_sigma]

end Helfgott
end

open MeasureTheory Set Metric Finset Function Helfgott
open scoped BigOperators

theorem solution (r : ℕ) (x : ℝ) (hr : 0 < r)
    (hx : 32*(r:ℝ)^2 < x) (f : AddCircle (1:ℝ) → ℂ)
    (hf : Integrable f AddCircle.haarAddCircle) :
    (∫ α in Helfgott.majorArcs 8 r x,f α ∂AddCircle.haarAddCircle) =
      x⁻¹ • (∑ q ∈ ((Finset.Icc 1 r).filter (fun q => Odd q) ∪
          (Finset.Icc 1 (2*r)).filter (fun q => Even q)),
        ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ∫ β in Set.Icc (-(if Odd q then 4*(r:ℝ)/(q:ℝ) else 8*(r:ℝ)/(q:ℝ)))
            (if Odd q then 4*(r:ℝ)/(q:ℝ) else 8*(r:ℝ)/(q:ℝ)),
            f (((a:ℝ)/(q:ℝ)+β/x : ℝ) : AddCircle (1:ℝ))) := by
  simpa only [Helfgott.actualArcDenominators] using
    Helfgott.major_arc_integral_decomposition r x hr hx f hf

#print axioms solution
