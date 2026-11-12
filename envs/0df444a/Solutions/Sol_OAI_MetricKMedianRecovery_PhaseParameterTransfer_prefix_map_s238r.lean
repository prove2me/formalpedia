-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.PhaseParameterTransfer.prefix_map_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:30:38.320686+00:00
-- url     : https://prove2.me/submissions/82449e20-d192-48ab-8591-0167145a92da

import Mathlib
import Definitions.Def_Q238L010

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_NearestImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LeafTransfer
variable {A X : Type*} [PseudoMetricSpace X] [DecidableEq X]

lemma nearest_images (W : Finset A) (hW : W.Nonempty) (r s : A → X) (p : X)
    (eps : ℝ) (hshrink : ∀ a ∈ W, dist p (s a) ≤ dist p (r a))
    (hloss : ∀ a ∈ W, dist p (r a) ≤ dist p (s a)+eps) :
    nearestDistance p (W.image s) ≤ nearestDistance p (W.image r) ∧
    nearestDistance p (W.image r) ≤ nearestDistance p (W.image s)+eps := by
  have hr : (W.image r).Nonempty := hW.image r
  have hs : (W.image s).Nonempty := hW.image s
  constructor
  · obtain ⟨x,hx,he⟩ := nearestDistance_attained p (W.image r) hr
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    rw [he]
    exact (nearestDistance_le_mem p (W.image s) (s a) (Finset.mem_image.mpr ⟨a,ha,rfl⟩)).trans
      (hshrink a ha)
  · obtain ⟨x,hx,he⟩ := nearestDistance_attained p (W.image s) hs
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    rw [he]
    exact (nearestDistance_le_mem p (W.image r) (r a) (Finset.mem_image.mpr ⟨a,ha,rfl⟩)).trans
      (hloss a ha)

end MetricKMedianRecovery.LeafTransfer

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_ClippedBid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace ClippingTransfer
variable {D X : Type*} [PseudoMetricSpace X]

lemma nearest_triangle (x y : X) (W : Finset X) (hW : W.Nonempty) :
    nearestDistance x W ≤ dist x y + nearestDistance y W := by
  obtain ⟨f,hf,he⟩ := nearestDistance_attained y W hW
  exact (nearestDistance_le_mem x W f hf).trans ((dist_triangle x y f).trans_eq (by rw [he]))

lemma active_transfer (loc : D → X) (t z : ℝ) (W W' : Finset X)
    (hW : W.Nonempty) (hW' : W'.Nonempty) (ht : 0 ≤ t)
    (hr : ∀ j, nearestDistance (loc j) W' ≤ nearestDistance (loc j) W)
    (j : D) (ha : activeAt loc t z W' j) : activeAt loc t z W j := by
  apply (activeAt_iff loc t z W j ht hW).mpr
  exact ((activeAt_iff loc t z W' j ht hW').mp ha).trans_le (mul_le_mul_of_nonneg_left (hr j) ht)

lemma bid_cap (loc : D → X) (t K v z : ℝ) (W : Finset X) (hW : W.Nonempty)
    (i : X) (tau : D → ℝ) (hb : admissibleBids loc t K v z W i tau)
    (j : D) (ha : activeAt loc t z W j) : tau j ≤ t*nearestDistance (loc j) W := by
  obtain ⟨f,hf,he⟩ := nearestDistance_attained (loc j) W hW
  simpa only [he] using (hb j ha).2.2.1 f hf

lemma admissible (loc : D → X) (t K v z : ℝ) (W W' : Finset X)
    (hW : W.Nonempty) (hW' : W'.Nonempty) (ht : 0 ≤ t)
    (hr : ∀ j, nearestDistance (loc j) W' ≤ nearestDistance (loc j) W)
    (i : X) (tau : D → ℝ) (hb : admissibleBids loc t K v z W i tau) :
    admissibleBids loc t K v z W' i (clippedBid loc t W' tau) := by
  intro j hj
  have ha := active_transfer loc t z W W' hW hW' ht hr j hj
  have hlo := ((activeAt_iff loc t z W' j ht hW').mp hj).le
  refine ⟨le_min (hb j ha).1 hlo,(min_le_left _ _).trans (hb j ha).2.1,?_,?_⟩
  · intro f hf
    exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_left (nearestDistance_le_mem _ _ _ hf) ht)
  · intro hfar
    unfold clippedBid
    rw [(hb j ha).2.2.2 hfar,min_eq_left hlo]

lemma effective_bounds (loc : D → X) (t K v z eps : ℝ) (W W' : Finset X)
    (hW : W.Nonempty) (hW' : W'.Nonempty) (ht : 0 ≤ t) (heps : 0 ≤ eps)
    (hr : ∀ j, nearestDistance (loc j) W' ≤ nearestDistance (loc j) W)
    (hchange : ∀ j, nearestDistance (loc j) W ≤ nearestDistance (loc j) W'+eps)
    (i : X) (tau : D → ℝ) (hb : admissibleBids loc t K v z W i tau) (j : D) :
    effectiveBid loc t z W' (clippedBid loc t W' tau) j ≤ effectiveBid loc t z W tau j ∧
    effectiveBid loc t z W tau j - t*eps ≤ effectiveBid loc t z W' (clippedBid loc t W' tau) j := by
  classical
  have hte : 0 ≤ t*eps := mul_nonneg ht heps
  have hr' := mul_le_mul_of_nonneg_left (hr j) ht
  have hc := mul_le_mul_of_nonneg_left (hchange j) ht
  by_cases hnew : activeAt loc t z W' j
  · have hold := active_transfer loc t z W W' hW hW' ht hr j hnew
    simp only [effectiveBid,ite_eq_left hnew,ite_eq_left hold,clippedBid]
    refine ⟨min_le_left _ _,le_min (by linarith only [hte]) ?_⟩
    have hcap := bid_cap loc t K v z W hW i tau hb j hold
    nlinarith only [hc,hcap]
  · have hnewcap : t*nearestDistance (loc j) W' ≤ z :=
      not_lt.mp (fun hh => hnew ((activeAt_iff loc t z W' j ht hW').mpr hh))
    by_cases hold : activeAt loc t z W j
    · simp only [effectiveBid,ite_eq_right hnew,ite_eq_left hold]
      have hcap := bid_cap loc t K v z W hW i tau hb j hold
      exact ⟨hnewcap.trans (hb j hold).1,by nlinarith only [hc,hcap]⟩
    · simp only [effectiveBid,ite_eq_right hnew,ite_eq_right hold]
      exact ⟨hr',by nlinarith only [hc]⟩

variable [Fintype D]

lemma payment_loss (loc : D → X) (t K v z eps : ℝ) (W W' : Finset X)
    (hW : W.Nonempty) (hW' : W'.Nonempty) (ht : 0 ≤ t) (heps : 0 ≤ eps)
    (hr : ∀ j, nearestDistance (loc j) W' ≤ nearestDistance (loc j) W)
    (hchange : ∀ j, nearestDistance (loc j) W ≤ nearestDistance (loc j) W'+eps)
    (i : X) (tau : D → ℝ) (hb : admissibleBids loc t K v z W i tau) :
    openingPayment loc t z W i tau ≤
      openingPayment loc t z W' i (clippedBid loc t W' tau) + (Fintype.card D:ℝ)*(t*eps) := by
  classical
  have hpoint : ∀ j, max (effectiveBid loc t z W tau j-t*dist i (loc j)) 0 ≤
      max (effectiveBid loc t z W' (clippedBid loc t W' tau) j-t*dist i (loc j)) 0+t*eps := by
    intro j
    have hh := (effective_bounds loc t K v z eps W W' hW hW' ht heps hr hchange i tau hb j).2
    apply max_le
    · have hm := le_max_left (effectiveBid loc t z W' (clippedBid loc t W' tau) j-t*dist i (loc j)) 0
      linarith
    · exact add_nonneg (le_max_right _ _) (mul_nonneg ht heps)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hpoint j)
  simpa only [openingPayment,effectiveBid,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul] using hsum

omit [Fintype D] in
lemma newly_inactive_dual (loc : D → X) (t K v z : ℝ) (W W' : Finset X)
    (hW' : W'.Nonempty) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (i i₀ : X) (tau : D → ℝ) (hb : admissibleBids loc t K v z W i tau)
    (a j : D) (hold : activeAt loc t z W j) (hnew : ¬activeAt loc t z W' j) :
    clippedBid loc t W' tau a - 2*dist i₀ (loc j)-dist i₀ (loc a) ≤ tau j-dist i₀ (loc j) := by
  have hcap : t*nearestDistance (loc j) W' ≤ z :=
    not_lt.mp (fun hh => hnew ((activeAt_iff loc t z W' j ht hW').mpr hh))
  have hnear := mul_le_mul_of_nonneg_left (nearest_triangle (loc a) (loc j) W' hW') ht
  have hdist := mul_le_mul_of_nonneg_right ht1 (dist_nonneg : 0 ≤ dist (loc a) (loc j))
  have htri := dist_triangle (loc a) i₀ (loc j)
  rw [dist_comm (loc a) i₀] at htri
  have hcl : clippedBid loc t W' tau a ≤ t*nearestDistance (loc a) W' := min_le_right _ _
  have hlo := (hb j hold).1
  nlinarith only [hcap,hnear,hdist,htri,hcl,hlo]

lemma dual_monotone (loc : D → X) (t K v z : ℝ) (W W' : Finset X)
    (hW : W.Nonempty) (hW' : W'.Nonempty) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hr : ∀ j, nearestDistance (loc j) W' ≤ nearestDistance (loc j) W)
    (i i₀ : X) (tau : D → ℝ) (hb : admissibleBids loc t K v z W i tau)
    (a : D) :
    openingDual loc t z W' i₀ (clippedBid loc t W' tau) a ≤ openingDual loc t z W i₀ tau a := by
  classical
  unfold openingDual
  apply Finset.sum_le_sum
  intro j _
  by_cases hnew : activeAt loc t z W' j
  · have hold := active_transfer loc t z W W' hW hW' ht hr j hnew
    simp only [ite_eq_left hnew,ite_eq_left hold]
    exact max_le_max (sub_le_sub_right (min_le_left _ _) _) le_rfl
  · by_cases hold : activeAt loc t z W j
    · simp only [ite_eq_right hnew,ite_eq_left hold]
      exact max_le_max (newly_inactive_dual loc t K v z W W' hW' ht ht1 i i₀ tau hb a j hold hnew) le_rfl
    · simp only [ite_eq_right hnew,ite_eq_right hold]
      exact max_le_max (sub_le_sub_right (sub_le_sub_right (min_le_left _ _) _) _) le_rfl

theorem openable_transfer (loc : D → X) (F W W' : Finset X) (t K v z lam lam' eta eps : ℝ)
    (hW : W.Nonempty) (hW' : W'.Nonempty) (ht : 0 ≤ t) (ht1 : t ≤ 1) (heps : 0 ≤ eps)
    (hr : ∀ j, nearestDistance (loc j) W' ≤ nearestDistance (loc j) W)
    (hchange : ∀ j, nearestDistance (loc j) W ≤ nearestDistance (loc j) W'+eps)
    (hlam : lam ≤ lam') (herror : lam'-lam+(Fintype.card D:ℝ)*(t*eps) ≤ (Fintype.card D:ℝ)*eta)
    (i : X) (hop : etaOpenable loc F W t K v z lam 0 i) :
    etaOpenable loc F W' t K v z lam' eta i := by
  obtain ⟨tau,hbid,hpay,hdual⟩ := hop
  refine ⟨clippedBid loc t W' tau,admissible loc t K v z W W' hW hW' ht hr i tau hbid,?_,?_⟩
  · have hp := payment_loss loc t K v z eps W W' hW hW' ht heps hr hchange i tau hbid
    simp only [mul_zero,sub_zero] at hpay
    linarith only [hp,hpay,herror]
  · intro i₀ hi₀ a ha
    exact (dual_monotone loc t K v z W W' hW hW' ht ht1 hr i i₀ tau hbid a).trans
      ((hdual i₀ hi₀ a (active_transfer loc t z W W' hW hW' ht hr a ha)).trans hlam)

end ClippingTransfer
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_OpenableMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseParameterTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma openable_map (loc : D → X) (F W : Finset X) (r : X → X)
    (v z lam lam' eta eps : ℝ) (hv : 0 < v) (hvsmall : v < 1/6)
    (heps : 0 ≤ eps) (hprice : lam ≤ lam')
    (herror : lam'-lam+(Fintype.card D:ℝ)*((1-3*v)*eps) ≤ (Fintype.card D:ℝ)*eta)
    (hshrink : ∀ j, ∀ x ∈ W, dist (loc j) (r x) ≤ dist (loc j) x)
    (hloss : ∀ j, ∀ x ∈ W, dist (loc j) x ≤ dist (loc j) (r x)+eps)
    (i : X) (hop : etaOpenable loc F W (1-3*v) (1+v^2) v z lam 0 i) :
    etaOpenable loc F (W.image r) (1-3*v) (1+v^2) v z lam' eta i := by
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have ht1 : 1-3*v ≤ 1 := by linarith only [hv]
  by_cases hW : W.Nonempty
  · have hh (j : D) := LeafTransfer.nearest_images W hW id r (loc j) eps
      (hshrink j) (hloss j)
    simp only [Finset.image_id] at hh
    exact ClippingTransfer.openable_transfer loc F W (W.image r) (1-3*v) (1+v^2)
      v z lam lam' eta eps hW (hW.image r) ht ht1 heps
      (fun j => (hh j).1) (fun j => (hh j).2) hprice herror i hop
  · have hW0 : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst W
    simp only [Finset.image_empty]
    obtain ⟨tau,hb,hp,hd⟩ := hop
    refine ⟨tau,hb,?_,fun i hi a ha => (hd i hi a ha).trans hprice⟩
    simp only [mul_zero,sub_zero] at hp
    have hnonneg : 0 ≤ (Fintype.card D:ℝ)*((1-3*v)*eps) := by positivity
    linarith only [hp,herror,hnonneg]

omit [Fintype D] [PseudoMetricSpace X] in
lemma image_regular_union {F B : Finset X} {r : X → X}
    (hfix : ∀ i ∈ F, r i = i) : (F ∪ B).image r ⊆ F ∪ B.image r := by
  intro x hx
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  rcases Finset.mem_union.mp hi with hi | hi
  · exact Finset.mem_union_left _ ((hfix i hi).symm ▸ hi)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)

theorem prefix_map_s238r_oai (loc : D → X) (F B Q : Finset X) (H : List X) (r : X → X)
    (v z lam lam' eta eps : ℝ) (hv : 0 < v) (hvsmall : v < 1/6)
    (heps : 0 ≤ eps) (hprice : lam ≤ lam')
    (herror : lam'-lam+(Fintype.card D:ℝ)*((1-3*v)*eps) ≤ (Fintype.card D:ℝ)*eta)
    (hinj : Function.Injective r) (hfix : ∀ i ∈ F, r i = i)
    (hshrink : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) (r x) ≤ dist (loc j) x)
    (hloss : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) x ≤ dist (loc j) (r x)+eps)
    (hp : PhaseSequence.Prefix loc F B v z lam 0 Q H) :
    PhaseSequence.Prefix loc F (B.image r) v z lam' eta (Q.image r) (H.map r) := by
  induction hp with
  | nil => exact PhaseSequence.Prefix.nil _
  | @cons Q i H hi htail ih =>
    apply PhaseSequence.Prefix.cons
    · refine ⟨?_,?_⟩
      · intro hh
        obtain ⟨a,ha,har⟩ := Finset.mem_image.mp hh
        exact hi.1 ((hinj har) ▸ ha)
      · rcases hi.2 with hb | ⟨hiF,W,hQ,hW,hop⟩
        · exact Or.inl (Finset.mem_image.mpr ⟨i,hb,rfl⟩)
        · have hir := hfix i hiF
          apply Or.inr
          refine ⟨hir.symm ▸ hiF,W.image r,Finset.image_subset_image hQ,?_,?_⟩
          · exact (Finset.image_subset_image hW).trans (image_regular_union hfix)
          · rw [hir]
            exact openable_map loc F W r v z lam lam' eta eps hv hvsmall heps hprice herror
              (fun j x hx => hshrink j x (hW hx))
              (fun j x hx => hloss j x (hW hx)) i hop
    · simpa only [Finset.image_insert] using ih

end MetricKMedianRecovery.PhaseParameterTransfer

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.MetricKMedianRecovery.PhaseParameterTransfer.prefix_map_s238r_oai.{u_1, u_2} := @OAI.MetricKMedianRecovery.PhaseParameterTransfer.prefix_map_s238r_oai.{u_1, u_2}
