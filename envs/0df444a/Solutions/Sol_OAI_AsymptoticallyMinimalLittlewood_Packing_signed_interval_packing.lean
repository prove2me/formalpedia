-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.signed_interval_packing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:38:21.807374+00:00
-- url     : https://prove2.me/submissions/43f1ff98-1a21-4d8f-be27-f8e399b1553e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/IntervalPacking.lean:L307-L376
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.signed_interval_packing. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_choose_odd_lengths
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_integer_slot_matching

-- ---- from OAI.Analysis.Littlewood.Chunks ----
namespace OAI

universe uJ

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

variable {r : ℕ}
lemma prefix_add_length_le (L : Fin r → ℕ) (i : Fin r) :
    slotPrefix L i+L i ≤ periodLength L := by
  classical
  have hi : i∉Finset.Iio i := by simp
  dsimp [slotPrefix,periodLength]
  rw [add_comm,← Finset.sum_insert hi]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma prefix_separated (L : Fin r → ℕ) {i j : Fin r} (hij : i<j) :
    slotPrefix L i+L i ≤ slotPrefix L j := by
  classical
  have hi : i∉Finset.Iio i := by simp
  change (∑ k ∈ Finset.Iio i, L k)+L i ≤ ∑ k ∈ Finset.Iio j, L k
  rw [add_comm,← Finset.sum_insert hi]
  apply Finset.sum_le_sum_of_subset
  intro k hk
  rcases Finset.mem_insert.mp hk with h | h
  · subst k; simpa using hij
  · exact Finset.mem_Iio.mpr (lt_trans (Finset.mem_Iio.mp h) hij)

lemma slotLeft_bounds (L : Fin r → ℕ) (R : ℕ) {shift chunk period : ℕ}
    (hs : shift<periodLength L) (hp : period+1<R) (i : Fin r) :
    chunk*(R*periodLength L) ≤ slotLeft L R shift chunk period i ∧
    slotLeft L R shift chunk period i+L i < (chunk+1)*(R*periodLength L) := by
  have hi := prefix_add_length_le L i
  have hp' : (period+2)*periodLength L ≤ R*periodLength L :=
    Nat.mul_le_mul_right _ (by omega)
  dsimp [slotLeft]
  constructor
  · omega
  · simp only [Nat.add_mul] at hp' ⊢
    omega

lemma slots_separated_same_chunk (L : Fin r → ℕ) (R shift chunk : ℕ)
    {p q : ℕ} {i j : Fin r} (h : p<q ∨ p=q ∧ i<j) :
    slotLeft L R shift chunk p i+L i ≤ slotLeft L R shift chunk q j := by
  have hi := prefix_add_length_le L i
  dsimp [slotLeft]
  rcases h with h | ⟨rfl,h⟩
  · have hp : (p+1)*periodLength L ≤ q*periodLength L :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [Nat.add_mul,Nat.one_mul] at hp
    omega
  · have hj := prefix_separated L h
    omega

lemma slots_separated_chunks (L : Fin r → ℕ) (R : ℕ) {s t k l p q : ℕ}
    (hs : s<periodLength L) (hp : p+1<R) (hkl : k<l) (i j : Fin r) :
    slotLeft L R s k p i+L i < slotLeft L R t l q j := by
  have hleft := (slotLeft_bounds L R (chunk := k) hs hp i).2
  have hle : (k+1)*(R*periodLength L) ≤ l*(R*periodLength L) :=
    Nat.mul_le_mul_right _ (by omega)
  dsimp [slotLeft] at *
  omega

lemma periodLength_pos (d : Fin r → ℕ) (i : Fin r) : 0<periodLength (oddLengths d) := by
  have h := prefix_add_length_le (oddLengths d) i
  dsimp [oddLengths] at h
  omega

end
end Packing
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset
variable {r : ℕ}

attribute [local instance] Classical.propDecidable

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- from OAI.Analysis.Littlewood.IntervalPacking ----
namespace OAI

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble Filter Topology
attribute [local instance] Classical.propDecidable

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

lemma circleInterval_disjoint_of_lifts {a b u v : ℝ}
    (ha : |a|+u/2<1/2) (hb : |b|+v/2<1/2) (hsep : (u+v)/2< |a-b|) :
    Disjoint (circleInterval (a : UnitAddCircle) u) (circleInterval (b : UnitAddCircle) v) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨t,ht,hz⟩ ⟨s,hs,hz'⟩
  have he : ((a+t : ℝ) : UnitAddCircle)=((b+s : ℝ) : UnitAddCircle) := by
    simpa only [AddCircle.coe_add] using hz.symm.trans hz'
  have ht' : |a+t|<1/2 := by linarith [abs_add_le a t]
  have hs' : |b+s|<1/2 := by linarith [abs_add_le b s]
  have he' : a+t=b+s := (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (a := (-1/2 : ℝ)) (p := (1 : ℝ))
    (show a+t∈Set.Ico (-1/2 : ℝ) (-1/2+1) from ⟨by linarith [(abs_lt.mp ht').1],by linarith [(abs_lt.mp ht').2]⟩)
    (show b+s∈Set.Ico (-1/2 : ℝ) (-1/2+1) from ⟨by linarith [(abs_lt.mp hs').1],by linarith [(abs_lt.mp hs').2]⟩)).mp he
  have h : |a-b|≤(u+v)/2 := by
    rw [show a-b=s-t by linarith]
    have hst := abs_sub s t
    linarith
  exact (not_lt_of_ge h) hsep

lemma slots_separated {r K R : ℕ} (d : Fin r → ℕ) (ω : SlotChoices d K)
    (k l : Fin K) (p t : Fin (R-1)) (i j : Fin r)
    (hne : (k,p,i)≠(l,t,j)) :
    slotLeft (oddLengths d) R (ω k).1 k p i+oddLengths d i≤
      slotLeft (oddLengths d) R (ω l).1 l t j ∨
    slotLeft (oddLengths d) R (ω l).1 l t j+oddLengths d j≤
      slotLeft (oddLengths d) R (ω k).1 k p i := by
  have hp : (p : ℕ)+1<R := by omega
  have ht : (t : ℕ)+1<R := by omega
  rcases lt_trichotomy k l with hkl | rfl | hlk
  · exact Or.inl (slots_separated_chunks _ R (ω k).1.isLt hp hkl i j).le
  · rcases lt_trichotomy p t with hpt | rfl | htp
    · exact Or.inl (slots_separated_same_chunk _ R (ω k).1 k (i := i) (j := j) (Or.inl hpt))
    · have hij : i≠j := fun h ↦ hne (by rw [h])
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact Or.inl (slots_separated_same_chunk _ R (ω k).1 k (i := i) (j := j) (Or.inr ⟨rfl,hij⟩))
      · exact Or.inr (slots_separated_same_chunk _ R (ω k).1 k (i := j) (j := i) (Or.inr ⟨rfl,hji⟩))
    · exact Or.inr (slots_separated_same_chunk _ R (ω k).1 k (i := j) (j := i) (Or.inl htp))
  · exact Or.inr (slots_separated_chunks _ R (ω l).1.isLt ht hlk j i).le

lemma actual_centers_separated {r K R : ℕ} (d : Fin r → ℕ) (ω : SlotChoices d K)
    (k l : Fin K) (p t : Fin (R-1)) (i j : Fin r)
    (hne : (k,p,i)≠(l,t,j)) :
    ((oddLengths d i : ℝ)+oddLengths d j)/2 ≤
      |(siteCenter d R (ω k).1 k p i : ℝ)-siteCenter d R (ω l).1 l t j| := by
  obtain h | h := slots_separated d ω k l p t i j hne
  · have h' : ((slotLeft (oddLengths d) R (ω k).1 k p i : ℕ) : ℝ)+oddLengths d i≤
        slotLeft (oddLengths d) R (ω l).1 l t j := by exact_mod_cast h
    apply le_trans _ (neg_le_abs _)
    dsimp [siteCenter,oddLengths] at *
    push_cast at *
    linarith
  · have h' : ((slotLeft (oddLengths d) R (ω l).1 l t j : ℕ) : ℝ)+oddLengths d j≤
        slotLeft (oddLengths d) R (ω k).1 k p i := by exact_mod_cast h
    apply le_trans _ (le_abs_self _)
    dsimp [siteCenter,oddLengths] at *
    push_cast at *
    linarith

lemma siteCenter_margin {r K R : ℕ} (d : Fin r → ℕ) (ω : SlotChoices d K)
    (k : Fin K) (p : Fin (R-1)) (i : Fin r) :
    (oddLengths d i : ℝ)/2 < siteCenter d R (ω k).1 k p i ∧
    (siteCenter d R (ω k).1 k p i : ℝ)+(oddLengths d i : ℝ)/2 <
      K*(R*periodLength (oddLengths d)) := by
  have h := (slotLeft_bounds (oddLengths d) R (chunk := (k : ℕ)) (ω k).1.isLt
    (show (p : ℕ)+1<R by omega) i).2
  have hk : ((k : ℕ)+1)*(R*periodLength (oddLengths d))≤K*(R*periodLength (oddLengths d)) :=
    Nat.mul_le_mul_right _ (by omega)
  have hb : (slotLeft (oddLengths d) R (ω k).1 k p i : ℝ)+oddLengths d i+1≤
      K*(R*periodLength (oddLengths d)) := by
    have hh : slotLeft (oddLengths d) R (ω k).1 k p i+oddLengths d i+1≤K*(R*periodLength (oddLengths d)) := by omega
    exact_mod_cast hh
  have hz : (0 : ℝ) ≤ slotLeft (oddLengths d) R (ω k).1 k p i := Nat.cast_nonneg _
  dsimp [siteCenter,oddLengths] at *
  push_cast at *
  constructor <;> linarith

lemma signedLift_abs (e : Bool) (x : ℝ) : |signedLift e x|=|x| := by cases e <;> simp [signedLift]

lemma signedLift_separation {x y u v : ℝ} (hx : u/2<x) (hy : v/2<y)
    (e f : Bool) (h : e=f → (u+v)/2≤|x-y|) :
    (u+v)/2≤|signedLift e x-signedLift f y| := by
  cases e <;> cases f <;> simp only [signedLift,Bool.false_eq_true,↓reduceIte] at *
  · simpa only [neg_sub_neg,abs_sub_comm] using h trivial
  · have hh : (u+v)/2<x+y := by linarith
    have hl := le_abs_self (x+y)
    rw [show -x-y=-(x+y) by ring,abs_neg]
    exact hh.le.trans hl
  · have hh : (u+v)/2<x+y := by linarith
    rw [sub_neg_eq_add]
    exact hh.le.trans (le_abs_self _)
  · exact h trivial

lemma circle_slots_disjoint {r K R q : ℕ} (d : Fin r → ℕ) (ω : SlotChoices d K)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q)
    (k l : Fin K) (p t : Fin (R-1)) (i j : Fin r) (e f : Bool)
    (hne : (e,k,p,i)≠(f,l,t,j)) {u v : ℝ}
    (hu : u<(oddLengths d i : ℝ)/q) (hv : v<(oddLengths d j : ℝ)/q) :
    Disjoint (circleInterval ((signedLift e (siteCenter d R (ω k).1 k p i)/q : ℝ) : UnitAddCircle) u)
      (circleInterval ((signedLift f (siteCenter d R (ω l).1 l t j)/q : ℝ) : UnitAddCircle) v) := by
  have hq0 : (0 : ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have hq' : (2 : ℝ)*(K*(R*periodLength (oddLengths d)))<q := by exact_mod_cast hq
  have ⟨hxi,hx⟩ := siteCenter_margin d ω k p i
  have ⟨hyj,hy⟩ := siteCenter_margin d ω l t j
  have hxi0 : (0 : ℝ)<siteCenter d R (ω k).1 k p i := lt_trans (by dsimp [oddLengths]; positivity) hxi
  have hyj0 : (0 : ℝ)<siteCenter d R (ω l).1 l t j := lt_trans (by dsimp [oddLengths]; positivity) hyj
  apply circleInterval_disjoint_of_lifts
  · rw [abs_div,signedLift_abs,abs_of_pos hq0,abs_of_pos hxi0]
    have hu' := (lt_div_iff₀ hq0).mp hu
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
    have hxx : 2*(siteCenter d R (ω k).1 k p i : ℝ)+u*q<q := by linarith
    have hd : (2*(siteCenter d R (ω k).1 k p i : ℝ)+u*q)/q<1 := (div_lt_iff₀ hq0).mpr (by simpa using hxx)
    have he : (siteCenter d R (ω k).1 k p i / (q : ℝ)+u/2)*2 = (2*(siteCenter d R (ω k).1 k p i : ℝ)+u*q)/q := by field_simp
    rw [he]
    exact hd
  · rw [abs_div,signedLift_abs,abs_of_pos hq0,abs_of_pos hyj0]
    have hv' := (lt_div_iff₀ hq0).mp hv
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
    have hyy : 2*(siteCenter d R (ω l).1 l t j : ℝ)+v*q<q := by linarith
    have hd : (2*(siteCenter d R (ω l).1 l t j : ℝ)+v*q)/q<1 := (div_lt_iff₀ hq0).mpr (by simpa using hyy)
    have he : (siteCenter d R (ω l).1 l t j / (q : ℝ)+v/2)*2 = (2*(siteCenter d R (ω l).1 l t j : ℝ)+v*q)/q := by field_simp
    rw [he]
    exact hd
  · rw [← sub_div,abs_div,abs_of_pos hq0]
    apply (lt_div_iff₀ hq0).mpr
    have hu' := (lt_div_iff₀ hq0).mp hu
    have hv' := (lt_div_iff₀ hq0).mp hv
    have hsep := signedLift_separation hxi hyj e f (by
      intro hef
      apply actual_centers_separated d ω k l p t i j
      intro heq
      apply hne
      obtain ⟨rfl,rfl,rfl⟩ := Prod.mk.inj heq |>.imp_left id
      exact hef ▸ rfl)
    nlinarith only [hu',hv',hsep]

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

lemma zmod_dot_circle {q m : ℕ} [NeZero q] (a : Fin m → ℤ) (y : Fin m → ZMod q) :
    ZMod.toAddCircle (dotProduct (fun k ↦ (a k : ZMod q)) y)=
      ∑ k, (a k) • ZMod.toAddCircle (y k) := by
  simp only [dotProduct,← zsmul_eq_mul,map_sum,map_zsmul]

lemma signedSite_circle {q : ℕ} [NeZero q] (e f : Bool) (c : ℕ) :
    signedCircle e (ZMod.toAddCircle (signedSite q f c))=
      ((signedLift (e==f) c/(q : ℝ) : ℝ) : UnitAddCircle) := by
  cases e <;> cases f <;>
    simp [signedCircle,signedSite,signedLift,ZMod.toAddCircle_natCast,neg_div]

theorem signed_interval_packing {r m : ℕ} (hr : 2≤r)
    (a : Fin r → Fin m → ℤ)
    (ha : ∀ j, (fun k ↦ (a j k : ℚ))≠0)
    (hnp : ∀ j l, j≠l → ∀ c : ℚ,
      (fun k ↦ (a l k : ℚ))≠c • (fun k ↦ (a j k : ℚ)))
    (w : Fin r → ℝ) (hw : ∀ i, 0<w i) (hs : 2*∑ i, w i<1) :
    ∃ H : ℕ, 1≤H ∧ ∃ θ : Fin H → Fin m → UnitAddCircle,
      ∀ e f : Bool, ∀ i j : Fin r, ∀ h v : Fin H, (e,i,h)≠(f,j,v) →
        Disjoint (circleInterval (signedCircle e (∑ k, a i k • θ h k)) (w i/H))
          (circleInterval (signedCircle f (∑ k, a j k • θ v k)) (w j/H)) := by
  classical
  have : Nonempty (Fin r) := ⟨⟨0,by omega⟩⟩
  obtain ⟨d,hd⟩ := choose_odd_lengths w hw hs
  let L := periodLength (oddLengths d)
  have hLi (i : Fin r) : (0 : ℝ)<oddLengths d i := by dsimp [oddLengths]; positivity
  have hL : (0 : ℝ)<L := by exact_mod_cast periodLength_pos d (Classical.arbitrary (Fin r))
  have hdr (i : Fin r) : w i/(oddLengths d i : ℝ)<1/(2*L) := by
    have hdi : w i<(oddLengths d i : ℝ)/(2*L) := by
      simpa only [L,periodLength,oddLengths,Nat.cast_sum,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hd i
    rw [div_lt_div_iff₀ (hLi i) (by positivity)]
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ)<2*L)).mp hdi
    simpa only [one_mul] using hh
  obtain ⟨i₀,_,himax⟩ := Finset.exists_max_image Finset.univ (fun i ↦ w i/(oddLengths d i : ℝ)) Finset.univ_nonempty
  obtain ⟨t,htlow,hthi⟩ := exists_between (hdr i₀)
  have ht0 : 0<t := (div_pos (hw i₀) (hLi i₀)).trans htlow
  have hti (i : Fin r) : w i/(oddLengths d i : ℝ)<t := (himax i (Finset.mem_univ i)).trans_lt htlow
  obtain ⟨q,R,K,hq,hR,hK,hqslot,ω,M,hhit,hdis,hsize⟩ := integer_slot_matching hr a ha hnp d ht0 hthi
  have : NeZero q := ⟨hq.ne_zero⟩
  have hq0 : (0 : ℝ)<q := by exact_mod_cast hq.pos
  have hM0 : 0<M.card := by have hh := (mul_pos ht0 hq0).trans hsize; exact_mod_cast hh
  have hMpos : (0 : ℝ)<M.card := by exact_mod_cast hM0
  let y : Fin M.card → M := M.equivFin.symm
  have hyinj : Function.Injective y := M.equivFin.symm.injective
  have hyhit (i : Fin r) (h : Fin M.card) : ∃ k : Fin K, ∃ p : Fin (R-1),
      dotProduct (fun k ↦ (a i k : ZMod q)) (y h).val=
        signedSite q (ω k).2 (siteCenter d R (ω k).1 k p i) := hhit (y h) (y h).property i
  choose k p hcenter using hyhit
  let θ : Fin M.card → Fin m → UnitAddCircle := fun h l ↦ ZMod.toAddCircle ((y h).val l)
  have hwidth (i : Fin r) : w i/(M.card : ℝ)<(oddLengths d i : ℝ)/q := by
    have hh := (div_lt_iff₀ (hLi i)).mp (hti i)
    have hhmul := mul_lt_mul_of_pos_right hh hq0
    have hsmul := mul_lt_mul_of_pos_left hsize (hLi i)
    rw [div_lt_div_iff₀ hMpos hq0]
    nlinarith only [hhmul,hsmul]
  have hcircle (e : Bool) (i : Fin r) (h : Fin M.card) :
      signedCircle e (∑ l, a i l • θ h l)=
        ((signedLift (e==(ω (k i h)).2) (siteCenter d R (ω (k i h)).1 (k i h) (p i h) i)/q : ℝ) : UnitAddCircle) := by
    change signedCircle e (∑ l, a i l • ZMod.toAddCircle ((y h).val l))=_
    rw [← zmod_dot_circle,hcenter i h]
    exact signedSite_circle e (ω (k i h)).2 _
  refine ⟨M.card,by omega,θ,?_⟩
  intro e f i j h v hne
  rw [hcircle,hcircle]
  apply circle_slots_disjoint d ω hqslot (k i h) (k j v) (p i h) (p j v) i j
    (e==(ω (k i h)).2) (f==(ω (k j v)).2) ?_ (hwidth i) (hwidth j)
  intro heq
  obtain ⟨hef,hpair⟩ := Prod.mk.inj heq
  obtain ⟨hk,hpair⟩ := Prod.mk.inj hpair
  obtain ⟨hp,hij⟩ := Prod.mk.inj hpair
  subst j
  have hdot : dotProduct (fun l ↦ (a i l : ZMod q)) (y h).val=
      dotProduct (fun l ↦ (a i l : ZMod q)) (y v).val := by
    rw [hcenter,hcenter,hk,hp]
  have hy : (y h).val=(y v).val := by
    by_contra hy
    exact hdis (y h) (y h).property (y v) (y v).property hy i hdot
  have hv : h=v := hyinj (Subtype.ext hy)
  subst v
  have hef' : e=f := by cases e <;> cases f <;> cases (ω (k i h)).2 <;> simp_all
  exact hne (by rw [hef'])

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.signed_interval_packing := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.signed_interval_packing
