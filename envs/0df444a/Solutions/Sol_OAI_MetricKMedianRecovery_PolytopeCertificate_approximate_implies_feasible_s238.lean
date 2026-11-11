-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.PolytopeCertificate.approximate_implies_feasible_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:15:53.568406+00:00
-- url     : https://prove2.me/submissions/9fef4056-29eb-4560-89c8-54cab8ef0870

import Mathlib
import Definitions.Def_Q238K000
import Definitions.Def_Q238K004

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Region
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PolytopeCertificate
open Matrix
open scoped Topology BigOperators

variable {R V : Type*} [Fintype R] [Fintype V]

omit [Fintype R] in
lemma row_perturb (A : Matrix R V ℝ) (x u : V → ℝ) (r : R) (t : ℝ) :
    (∑ j, A r j * (x j+t*u j)) = (∑ j, A r j*x j)+t*(∑ j, A r j*u j) := by
  simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem active_kernel_zero (A : Matrix R V ℝ) (b : R → ℝ) (x : V → ℝ)
    (hx : x ∈ (region A b).extremePoints ℝ) (u : V → ℝ)
    (hu : ∀ r, (∑ j, A r j*x j)=b r → (∑ j, A r j*u j)=0) : u=0 := by
  have hn : ∀ᶠ t : ℝ in 𝓝 0, (fun j => x j+t*u j) ∈ region A b := by
    apply Filter.eventually_all.mpr
    intro r
    by_cases ha : (∑ j, A r j*x j)=b r
    · exact Filter.Eventually.of_forall (fun t => by rw [row_perturb,hu r ha,ha]; simp)
    · have hs : (∑ j, A r j*x j)<b r := lt_of_le_of_ne (hx.1 r) ha
      have hc : Continuous (fun t : ℝ => ∑ j, A r j*(x j+t*u j)) := by fun_prop
      have hh : ∀ᶠ t : ℝ in 𝓝 0, (∑ j, A r j*(x j+t*u j))<b r :=
        hc.continuousAt.eventually_lt_const (by simpa using hs)
      exact hh.mono (fun _ h => h.le)
  obtain ⟨e,he,hs⟩ := Metric.eventually_nhds_iff.mp hn
  have hp : (fun j => x j+(e/2)*u j) ∈ region A b := hs (by simpa [abs_of_pos he] using (show e/2<e by linarith))
  have hm : (fun j => x j+(-e/2)*u j) ∈ region A b := hs (by simpa [abs_of_pos he] using (show e/2<e by linarith))
  have hmid : midpoint ℝ (fun j => x j+(e/2)*u j) (fun j => x j+(-e/2)*u j) = x := by
    rw [midpoint_eq_smul_add]
    ext j
    simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul,invOf_eq_inv]
    ring
  have hseg := midpoint_mem_openSegment (𝕜 := ℝ) (fun j => x j+(e/2)*u j) (fun j => x j+(-e/2)*u j)
  rw [hmid] at hseg
  have heq := hx.2 hp hm hseg
  ext j
  have hh := congrFun heq j
  change u j=0
  have hmul : (e/2)*u j=0 := by linarith
  exact (mul_eq_zero.mp hmul).resolve_left (by positivity)

omit [Fintype R] in
lemma region_closed (A : Matrix R V ℝ) (b : R → ℝ) : IsClosed (region A b) := by
  have h : region A b = ⋂ r, {x : V → ℝ | (∑ j, A r j*x j) ≤ b r} := by
    ext x
    simp only [region,Set.mem_ofPred_eq,Set.mem_iInter]
  rw [h]
  apply isClosed_iInter
  intro r
  exact isClosed_le (by fun_prop) continuous_const

lemma gram_det_ne_zero [DecidableEq V] (C : Matrix R V ℝ)
    (hker : ∀ u : V → ℝ, C *ᵥ u=0 → u=0) : (Cᵀ*C).det≠0 := by
  classical
  have hg : ∀ u : V → ℝ, (Cᵀ*C) *ᵥ u=0 → u=0 := by
    intro u hu
    have hsum : ∑ r, (C *ᵥ u) r ^ 2 = 0 := by
      calc
        _ = u ⬝ᵥ ((Cᵀ*C) *ᵥ u) := by
          rw [←mulVec_mulVec,dotProduct_transpose_mulVec]
          simp only [dotProduct,pow_two]
        _ = 0 := by rw [hu]; simp
    have hz : ∀ r, (C *ᵥ u) r=0 := by
      intro r
      have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun r (_ : r ∈ Finset.univ) => sq_nonneg ((C *ᵥ u) r))).mp hsum r (Finset.mem_univ r)
      exact sq_eq_zero_iff.mp hh
    exact hker u (funext hz)
  have hi : Function.Injective (Cᵀ*C).mulVec := by
    intro u w huw
    have hh : (Cᵀ*C) *ᵥ (u-w)=0 := by rw [mulVec_sub,huw,sub_self]
    exact sub_eq_zero.mp (hg _ hh)
  exact isUnit_iff_ne_zero.mp ((Cᵀ*C).isUnit_iff_isUnit_det.mp (mulVec_injective_iff_isUnit.mp hi))

lemma abs_det_le [DecidableEq V] (M : Matrix V V ℤ) (H : ℤ)
    (hM : ∀ i j, |M i j| ≤ H) :
    |M.det| ≤ (Fintype.card V).factorial * H^(Fintype.card V) := by
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ s : Equiv.Perm V, |(s.sign : ℤ) * ∏ i, M (s i) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s : Equiv.Perm V, H^(Fintype.card V) := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul,Equiv.Perm.sign_abs,one_mul,Finset.abs_prod]
      calc
        _ ≤ ∏ _i : V, H := Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun index _ => hM (s index) index)
        _ = _ := by simp
    _ = _ := by simp [Fintype.card_perm]

omit [Fintype R] in
lemma int_det_cast [DecidableEq V] (M : Matrix V V ℤ) :
    ((M.det:ℤ):ℝ)=Matrix.det (fun i j => (M i j:ℝ)) := by
  exact (Int.castRingHom ℝ).map_det M

theorem integer_point_certificate [DecidableEq V] (A : Matrix R V ℤ) (b : R → ℤ)
    (H : ℤ) (hH : 0 ≤ H) (hA : ∀ r j, |A r j| ≤ H) (hb : ∀ r, |b r| ≤ H)
    (x : V → ℝ)
    (hker : ∀ u : V → ℝ, (∀ r, (∑ j, (A r j:ℝ)*x j)=(b r:ℝ) →
      (∑ j, (A r j:ℝ)*u j)=0) → u=0) :
    ∃ p : V → ℤ, ∃ q : ℤ, q≠0 ∧
      |q| ≤ (Fintype.card V).factorial * ((Fintype.card R:ℤ)*H^2)^(Fintype.card V) ∧
      (∀ j, |p j| ≤ (Fintype.card V).factorial * ((Fintype.card R:ℤ)*H^2)^(Fintype.card V)) ∧
      (fun j => (p j:ℝ)/(q:ℝ)) = x := by
  classical
  let active (r : R) : Prop := (∑ j, (A r j:ℝ)*x j)=(b r:ℝ)
  let C : Matrix R V ℤ := fun r j => if active r then A r j else 0
  let d : R → ℤ := fun r => if active r then b r else 0
  let G : Matrix V V ℤ := Cᵀ*C
  let c : V → ℤ := Cᵀ *ᵥ d
  let Cr : Matrix R V ℝ := fun r j => (C r j:ℝ)
  let Gr : Matrix V V ℝ := fun i j => (G i j:ℝ)
  have hm : Gr=Crᵀ*Cr := by
    ext i j
    change ((∑ r, C r i*C r j:ℤ):ℝ) = _
    push_cast
    rfl
  have hcx : Cr *ᵥ x = fun r => (d r:ℝ) := by
    ext r
    by_cases ha : active r
    · simpa only [Matrix.mulVec,dotProduct,Cr,C,d,ite_eq_left ha] using ha
    · simp [Matrix.mulVec,dotProduct,Cr,C,d,ha]
  have hc : (fun j => (c j:ℝ))=Crᵀ *ᵥ (fun r => (d r:ℝ)) := by
    ext j
    change ((∑ r, C r j*d r:ℤ):ℝ) = _
    push_cast
    rfl
  have hdet : Gr.det≠0 := by
    rw [hm]
    apply gram_det_ne_zero
    intro u hu
    apply hker u
    intro r hr
    have hh := congrFun hu r
    simpa only [Matrix.mulVec,dotProduct,Cr,C,ite_eq_left (show active r from hr),Pi.zero_apply] using hh
  have hgx : Gr *ᵥ x = fun j => (c j:ℝ) := by
    rw [hm,←mulVec_mulVec,hcx,←hc]
  have hq : G.det≠0 := by
    intro hh
    apply hdet
    rw [←int_det_cast,hh,Int.cast_zero]
  have hcramer : (Gr.det) • x = Gr.cramer (fun j => (c j:ℝ)) := by
    rw [cramer_eq_adjugate_mulVec,←hgx,mulVec_mulVec,adjugate_mul,smul_mulVec,one_mulVec]
  have hxrat : ∀ j, x j = ((G.updateCol j c).det:ℝ)/(G.det:ℝ) := by
    intro j
    have hh := congrFun hcramer j
    simp only [Pi.smul_apply,smul_eq_mul,cramer_apply] at hh
    have hmap : (fun i k => ((G.updateCol j c) i k:ℝ))=Gr.updateCol j (fun k => (c k:ℝ)) := by
      ext i k
      simp only [Matrix.updateCol_apply]
      split_ifs <;> rfl
    have hcast : (Gr.updateCol j (fun k => (c k:ℝ))).det = ((G.updateCol j c).det:ℝ) := by
      rw [←hmap,←int_det_cast]
    have hcastG : Gr.det=(G.det:ℝ) := (int_det_cast G).symm
    rw [hcast,hcastG] at hh
    apply (eq_div_iff (by exact_mod_cast hq)).mpr
    linarith
  have hC : ∀ r j, |C r j|≤H := by
    intro r j
    by_cases ha : active r
    · simpa only [C,ite_eq_left ha] using hA r j
    · simpa only [C,ite_eq_right ha,abs_zero] using hH
  have hd : ∀ r, |d r|≤H := by
    intro r
    by_cases ha : active r
    · simpa only [d,ite_eq_left ha] using hb r
    · simpa only [d,ite_eq_right ha,abs_zero] using hH
  have hG : ∀ i j, |G i j| ≤ (Fintype.card R:ℤ)*H^2 := by
    intro i j
    calc
      _ = |∑ r, C r i*C r j| := rfl
      _ ≤ ∑ r, |C r i*C r j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : R, H^2 := by
        apply Finset.sum_le_sum
        intro r _
        rw [abs_mul,pow_two]
        exact mul_le_mul (hC r i) (hC r j) (abs_nonneg _) hH
      _ = _ := by simp
  have hcv : ∀ j, |c j| ≤ (Fintype.card R:ℤ)*H^2 := by
    intro j
    calc
      _ = |∑ r, C r j*d r| := rfl
      _ ≤ ∑ r, |C r j*d r| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : R, H^2 := by
        apply Finset.sum_le_sum
        intro r _
        rw [abs_mul,pow_two]
        exact mul_le_mul (hC r j) (hd r) (abs_nonneg _) hH
      _ = _ := by simp
  refine ⟨fun j => (G.updateCol j c).det,G.det,hq,
    abs_det_le G _ hG,?_,?_⟩
  · intro j
    apply abs_det_le _ _
    intro i k
    by_cases he : k=j
    · simpa only [Matrix.updateCol_apply,he,ite_true, if_true] using hcv i
    · simpa only [Matrix.updateCol_apply,he,ite_false, if_false] using hG i k
  · ext j
    exact (hxrat j).symm

end MetricKMedianRecovery.PolytopeCertificate

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundedMinimizingExtreme
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PolytopeCertificate

section
open Matrix
open scoped Topology BigOperators
variable {R V : Type*} [Fintype R] [Fintype V]

omit [Fintype R] in

theorem bounded_minimizing_extreme (A : Matrix R V ℝ) (b : R → ℝ) (c : V → ℝ) (B : ℝ)
    (hn : (region A b).Nonempty)
    (hbound : ∀ x ∈ region A b, ∀ j, -B ≤ x j ∧ x j ≤ B) :
    ∃ x, x ∈ (region A b).extremePoints ℝ ∧
      ∀ y ∈ region A b, (∑ j, c j*x j) ≤ ∑ j, c j*y j := by
  let L : (V → ℝ) → ℝ := fun x => ∑ j, c j*x j
  have hL : Continuous L := by fun_prop
  have hc : IsCompact (region A b) :=
    isCompact_Icc.of_isClosed_subset (region_closed A b) (by
      intro x hx
      exact ⟨fun j => (hbound x hx j).1,fun j => (hbound x hx j).2⟩)
  obtain ⟨x0,hx0,hmin⟩ := hc.exists_isMinOn hn hL.continuousOn
  let S : Set (V → ℝ) := region A b ∩ {x | L x=L x0}
  have hS : IsCompact S := hc.inter_right (isClosed_eq hL continuous_const)
  have hSn : S.Nonempty := ⟨x0,hx0,rfl⟩
  have he : IsExtreme ℝ (region A b) S := by
    refine ⟨fun _ hx => hx.1,?_⟩
    intro x hx y hy z hz hseg
    refine ⟨hx,?_⟩
    rcases hseg with ⟨a,b,ha,hb,hab,rfl⟩
    have heq : L (a • x+b • y)=a*L x+b*L y := by
      simp only [L,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
      rw [Finset.mul_sum,Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
    have hval : a*L x+b*L y=L x0 := heq.symm.trans hz.2
    have hmx : L x0 ≤ L x := hmin hx
    have hmy : L x0 ≤ L y := hmin hy
    change L x=L x0
    apply le_antisymm ?_ hmx
    by_contra! hh
    have hpos := mul_pos ha (sub_pos.mpr hh)
    have hnon := mul_nonneg hb.le (sub_nonneg.mpr hmy)
    have hab0 : (a+b)*L x0=L x0 := by rw [hab,one_mul]
    nlinarith
  obtain ⟨x,hx⟩ := hS.extremePoints_nonempty hSn
  refine ⟨x,he.extremePoints_subset_extremePoints hx,?_⟩
  intro y hy
  change L x ≤ L y
  rw [hx.1.2]
  exact hmin hy

theorem integer_min_certificate [DecidableEq V] (A : Matrix R V ℤ) (b : R → ℤ)
    (c : V → ℝ) (B : ℝ) (H : ℤ) (hH : 0 ≤ H)
    (hA : ∀ r j, |A r j| ≤ H) (hb : ∀ r, |b r| ≤ H)
    (hn : (region (fun r j => (A r j:ℝ)) (fun r => (b r:ℝ))).Nonempty)
    (hbound : ∀ x ∈ region (fun r j => (A r j:ℝ)) (fun r => (b r:ℝ)),
      ∀ j, -B ≤ x j ∧ x j ≤ B) :
    ∃ p : V → ℤ, ∃ q : ℤ, q≠0 ∧
      |q| ≤ (Fintype.card V).factorial * ((Fintype.card R:ℤ)*H^2)^(Fintype.card V) ∧
      (∀ j, |p j| ≤ (Fintype.card V).factorial * ((Fintype.card R:ℤ)*H^2)^(Fintype.card V)) ∧
      (fun j => (p j:ℝ)/(q:ℝ)) ∈ region (fun r j => (A r j:ℝ)) (fun r => (b r:ℝ)) ∧
      ∀ y ∈ region (fun r j => (A r j:ℝ)) (fun r => (b r:ℝ)),
        (∑ j, c j*((p j:ℝ)/(q:ℝ))) ≤ ∑ j, c j*y j := by
  obtain ⟨x,hx,hm⟩ := bounded_minimizing_extreme (fun r j => (A r j:ℝ))
    (fun r => (b r:ℝ)) c B hn hbound
  obtain ⟨p,q,hq,hqb,hpb,heq⟩ := integer_point_certificate A b H hH hA hb x
    (fun u hu => active_kernel_zero _ _ x hx u hu)
  refine ⟨p,q,hq,hqb,hpb,heq.symm ▸ hx.1,?_⟩
  intro y hy
  have heqj (j : V) : (p j:ℝ)/(q:ℝ)=x j := congrFun heq j
  simpa only [heqj] using hm y hy

end

open Matrix
open scoped BigOperators
variable {R V : Type*} [Fintype R] [Fintype V] [DecidableEq V]

omit [Fintype R] in
lemma slack_region_iff (A : Matrix R V ℤ) (b : R → ℤ) (B H : ℤ) (y : Option V → ℝ) :
    y ∈ region (fun r j => (slackMatrix A r j:ℝ)) (fun r => (slackBounds b B H r:ℝ)) ↔
      (0 ≤ y none ∧ y none ≤ (H:ℝ)) ∧
      (∀ j, -(B:ℝ) ≤ y (some j) ∧ y (some j) ≤ (B:ℝ)) ∧
      (∀ r, (∑ j, (A r j:ℝ)*y (some j)) ≤ (b r:ℝ)+y none) := by
  have he (r : R) : (∑ j, (slackMatrix A (.inl r) j:ℝ)*y j) =
      -y none+∑ j, (A r j:ℝ)*y (some j) := by
    simp [Fintype.sum_option,slackMatrix]
  have hb (s : Bool) (j : Option V) :
      (∑ k, (slackMatrix A (.inr (s,j)) k:ℝ)*y k) = if s then y j else -y j := by
    cases s <;> simp [slackMatrix]
  constructor
  · intro h
    have h0 := h (.inr (false,none))
    have hH := h (.inr (true,none))
    rw [hb] at h0 hH
    refine ⟨?_,?_,?_⟩
    · simpa only [Bool.false_eq_true,Bool.true_eq,ite_false, if_false,ite_true, if_true,slackBounds,
        Int.cast_zero,neg_nonpos] using And.intro h0 hH
    · intro j
      have hl := h (.inr (false,some j))
      have hu := h (.inr (true,some j))
      simp only [hb,slackBounds,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hl hu
      exact ⟨by linarith,hu⟩
    · intro r
      have hh := h (.inl r)
      rw [he] at hh
      change -y none+(∑ j, (A r j:ℝ)*y (some j)) ≤ (b r:ℝ) at hh
      linarith
  · rintro ⟨ht,hx,ha⟩ r
    cases r with
    | inl r =>
      rw [he]
      change _ ≤ (b r:ℝ)
      linarith [ha r]
    | inr p =>
      rcases p with ⟨s,j⟩
      rw [hb]
      cases j with
      | none =>
        cases s
        · simpa only [Bool.false_eq_true,ite_false, if_false,slackBounds,Int.cast_zero,neg_nonpos] using ht.1
        · exact ht.2
      | some j =>
        cases s
        · change -y (some j) ≤ (B:ℝ)
          linarith [(hx j).1]
        · exact (hx j).2

lemma positive_fraction_gap (p q : ℤ) (Q : ℝ) (hq : q≠0)
    (hb : |(q:ℝ)| ≤ Q) (hpq : 0 < (p:ℝ)/(q:ℝ)) :
    1/Q ≤ (p:ℝ)/(q:ℝ) := by
  have hqr : (q:ℝ)≠0 := by exact_mod_cast hq
  have hq0 : 0 < |(q:ℝ)| := abs_pos.mpr hqr
  have hp : p≠0 := by
    intro he
    simp [he] at hpq
  have hp1 : (1:ℤ) ≤ |p| := by have hh := abs_pos.mpr hp; omega
  have hp1r : (1:ℝ) ≤ |(p:ℝ)| := by exact_mod_cast hp1
  calc
    _ ≤ 1/|(q:ℝ)| := one_div_le_one_div_of_le hq0 hb
    _ ≤ |(p:ℝ)|/|(q:ℝ)| := div_le_div_of_nonneg_right hp1r hq0.le
    _ = (p:ℝ)/(q:ℝ) := by rw [←abs_div,abs_of_pos hpq]

theorem approximate_implies_feasible_s238_oai (A : Matrix R V ℤ) (b : R → ℤ) (B H : ℤ)
    (hB : 0 ≤ B) (hH : 1 ≤ H) (hA : ∀ r j, |A r j|≤H) (hb : ∀ r, |b r|≤H)
    (eps : ℝ) (heps0 : 0≤eps) (hepsH : eps≤(H:ℝ))
    (heps : eps < 1 / ((Fintype.card (Option V)).factorial *
      ((Fintype.card (SlackRow R V):ℤ)*(max H B)^2)^(Fintype.card (Option V)) : ℤ))
    (x : V → ℝ) (hx : ∀ j, -(B:ℝ)≤x j ∧ x j≤(B:ℝ))
    (ha : ∀ r, (∑ j, (A r j:ℝ)*x j)≤(b r:ℝ)+eps) :
    ∃ y ∈ region (fun r j => (A r j:ℝ)) (fun r => (b r:ℝ)),
      ∀ j, -(B:ℝ)≤y j ∧ y j≤(B:ℝ) := by
  classical
  let C := slackMatrix A
  let d := slackBounds (V:=V) b B H
  let K := max H B
  have hK : 0≤K := le_trans (by omega) (le_max_left H B)
  have hKH : H≤K := le_max_left _ _
  have hKB : B≤K := le_max_right _ _
  have hC : ∀ r j, |C r j|≤K := by
    intro r j
    cases r with
    | inl r =>
      cases j with
      | none => change |-1|≤K; simp only [abs_neg,abs_one]; omega
      | some j => exact (hA r j).trans hKH
    | inr p =>
      rcases p with ⟨s,k⟩
      change |if j=k then if s then 1 else -1 else 0|≤K
      split_ifs <;> simp only [abs_one,abs_neg,abs_zero] <;> omega
  have hd : ∀ r, |d r|≤K := by
    intro r
    cases r with
    | inl r => exact (hb r).trans hKH
    | inr p =>
      rcases p with ⟨s,j⟩
      cases j with
      | none => cases s <;> simp_all [d,slackBounds,abs_of_nonneg (show 0≤H by omega)]
      | some j => simpa only [d,slackBounds,abs_of_nonneg hB] using hKB
  let c : Option V → ℝ := fun j => if j=none then 1 else 0
  have hc (y : Option V → ℝ) : (∑ j, c j*y j)=y none := by simp [c]
  have hn : (region (fun r j => (C r j:ℝ)) (fun r => (d r:ℝ))).Nonempty := by
    refine ⟨Option.elim' (H:ℝ) (fun _ => 0),(slack_region_iff A b B H _).mpr ?_⟩
    refine ⟨?_,?_,?_⟩
    · change 0≤(H:ℝ) ∧ (H:ℝ)≤(H:ℝ)
      exact ⟨by exact_mod_cast (show 0≤H by omega),le_rfl⟩
    · intro j
      simp only [Option.elim'_some]
      exact ⟨neg_nonpos.mpr (by exact_mod_cast hB),by exact_mod_cast hB⟩
    · intro r
      simp only [Option.elim'_some,Option.elim'_none,mul_zero,Finset.sum_const_zero]
      have hh := (abs_le.mp (hb r)).1
      exact_mod_cast (show 0≤b r+H by omega)
  have hbounded : ∀ y ∈ region (fun r j => (C r j:ℝ)) (fun r => (d r:ℝ)),
      ∀ j, -(K:ℝ)≤y j ∧ y j≤(K:ℝ) := by
    intro y hy j
    have hh := (slack_region_iff A b B H y).mp hy
    have hKr : 0≤(K:ℝ) := by exact_mod_cast hK
    have hKHr : (H:ℝ)≤(K:ℝ) := by exact_mod_cast hKH
    have hKBr : (B:ℝ)≤(K:ℝ) := by exact_mod_cast hKB
    cases j with
    | none => exact ⟨by linarith [hh.1.1],hh.1.2.trans hKHr⟩
    | some j => exact ⟨by linarith [(hh.2.1 j).1],(hh.2.1 j).2.trans hKBr⟩
  obtain ⟨p,q,hq,hqb,_hpb,hpq,hmin⟩ := integer_min_certificate C d c (K:ℝ) K
    hK hC hd hn hbounded
  have hh := (slack_region_iff A b B H _).mp hpq
  by_cases he : (p none:ℝ)/(q:ℝ)=0
  · refine ⟨fun j => (p (some j):ℝ)/(q:ℝ),?_,hh.2.1⟩
    intro r
    simpa only [he,add_zero] using hh.2.2 r
  · have hpqpos : 0<(p none:ℝ)/(q:ℝ) := lt_of_le_of_ne hh.1.1 (Ne.symm he)
    have hqbR : |(q:ℝ)| ≤ ((Fintype.card (Option V)).factorial *
        ((Fintype.card (SlackRow R V):ℤ)*K^2)^(Fintype.card (Option V)) : ℤ) := by
      exact_mod_cast hqb
    have hgap := positive_fraction_gap (p none) q _ hq hqbR hpqpos
    have happrox : Option.elim' eps x ∈
        region (fun r j => (C r j:ℝ)) (fun r => (d r:ℝ)) :=
      (slack_region_iff A b B H _).mpr ⟨⟨heps0,hepsH⟩,hx,ha⟩
    have hval := hmin (Option.elim' eps x) happrox
    rw [hc,hc] at hval
    change (p none:ℝ)/(q:ℝ) ≤ eps at hval
    exact (not_lt_of_ge (hgap.trans hval) heps).elim

end MetricKMedianRecovery.PolytopeCertificate

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.MetricKMedianRecovery.PolytopeCertificate.approximate_implies_feasible_s238_oai.{u_1, u_2} := @OAI.MetricKMedianRecovery.PolytopeCertificate.approximate_implies_feasible_s238_oai.{u_1, u_2}
