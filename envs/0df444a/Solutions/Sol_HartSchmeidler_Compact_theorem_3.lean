-- Prove2me | solution 1 for HartSchmeidler.Compact.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-11T06:25:37.034723+00:00
-- url     : https://prove2.me/submissions/658f6a67-3247-4ef5-b240-238b6da345d9

import Definitions.Def_HartSchmeidler_Compact_Game

-- BEGIN COMPLETE MODULE FiniteMinimax
section

open scoped BigOperators
open Set
namespace HartSchmeidler.Compact.Proof

/-- Finite mixed response criterion, with no strict inequalities. -/
theorem finite_minimax_response {I J : Type*} [Fintype I] [Nonempty I]
    [Fintype J] [Nonempty J] (A : I → J → ℝ)
    (h : ∀ y ∈ stdSimplex ℝ J, ∃ x ∈ stdSimplex ℝ I,
      0 ≤ ∑ i, ∑ j, x i * y j * A i j) :
    ∃ x ∈ stdSimplex ℝ I, ∀ j, 0 ≤ ∑ i, x i * A i j := by
  classical
  let B : (J → ℝ) → (I → ℝ) → ℝ := fun y x => ∑ i, ∑ j, x i * y j * A i j
  have hnI : (stdSimplex ℝ I).Nonempty :=
    ⟨Pi.single (Classical.choice ‹Nonempty I›) 1, single_mem_stdSimplex _ _⟩
  have hnJ : (stdSimplex ℝ J).Nonempty :=
    ⟨Pi.single (Classical.choice ‹Nonempty J›) 1, single_mem_stdSimplex _ _⟩
  have hc1 (x : I → ℝ) : Continuous (fun y => B y x) := by unfold B; fun_prop
  have hc2 (y : J → ℝ) : Continuous (B y) := by unfold B; fun_prop
  have hv (x : I → ℝ) : ConvexOn ℝ (stdSimplex ℝ J) (fun y => B y x) := by
    refine ⟨convex_stdSimplex _ _, ?_⟩
    intro y hy z hz a b ha hb hab
    apply le_of_eq
    simp only [B, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi
    all_goals apply Finset.sum_congr rfl; intros; ring
  have hw (y : J → ℝ) : ConcaveOn ℝ (stdSimplex ℝ I) (B y) := by
    refine ⟨convex_stdSimplex _ _, ?_⟩
    intro x hx z hz a b ha hb hab
    apply le_of_eq
    simp only [B, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi
    all_goals apply Finset.sum_congr rfl; intros; ring
  obtain ⟨y, hy, x, hx, hs⟩ := Sion.exists_isSaddlePointOn hnJ
    (convex_stdSimplex ℝ J) (isCompact_stdSimplex ℝ J)
    (fun x _ => (hc1 x).continuousOn.lowerSemicontinuousOn)
    (fun x _ => (hv x).quasiconvexOn)
    (convex_stdSimplex ℝ I) hnI (isCompact_stdSimplex ℝ I)
    (fun y _ => (hc2 y).continuousOn.upperSemicontinuousOn)
    (fun y _ => (hw y).quasiconcaveOn)
  obtain ⟨z, hz, hz0⟩ := h y hy
  refine ⟨x, hx, fun j => ?_⟩
  have hh := hs (Pi.single j 1) (single_mem_stdSimplex _ _) z hz
  have : 0 ≤ B (Pi.single j 1) x := hz0.trans hh
  simpa [B, Pi.single_apply, mul_ite] using this

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE FiniteMinimax

-- BEGIN COMPLETE MODULE StationaryLottery
section

open scoped BigOperators
namespace HartSchmeidler.Compact.Proof

noncomputable def flowMatrix {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → I → ℝ) (r j : I) : ℝ :=
  (if r = j then ∑ t, a r t else 0) - a r j

theorem flowMatrix_sum {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → I → ℝ) (r : I) : ∑ j, flowMatrix a r j = 0 := by
  simp [flowMatrix, Finset.sum_sub_distrib]

theorem flowMatrix_eval {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → I → ℝ) (u : I → ℝ) (r : I) :
    ∑ j, u j * flowMatrix a r j = ∑ t, a r t * (u r - u t) := by
  simp [flowMatrix, mul_sub, mul_ite, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_comm]

/-- A finite nonnegative transition array admits a lottery cancelling every test vector. -/
theorem stationary_lottery {I : Type*} [Fintype I] [Nonempty I]
    (a : I → I → ℝ) (ha : ∀ r t, 0 ≤ a r t) :
    ∃ x ∈ stdSimplex ℝ I, ∀ u : I → ℝ,
      ∑ r, x r * ∑ t, a r t * (u r - u t) = 0 := by
  classical
  obtain ⟨x, hx, hnon⟩ := finite_minimax_response (flowMatrix a) (by
    intro y hy
    obtain ⟨r, hr, hmax⟩ := Finset.exists_max_image Finset.univ y Finset.univ_nonempty
    refine ⟨Pi.single r 1, single_mem_stdSimplex _ _, ?_⟩
    simp only [mul_assoc, ← Finset.mul_sum]
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [flowMatrix_eval]
    exact Finset.sum_nonneg fun t _ => mul_nonneg (ha r t) (sub_nonneg.mpr (hmax t (by simp))))
  have hsum : ∑ j, (∑ r, x r * flowMatrix a r j) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, flowMatrix_sum, mul_zero, Finset.sum_const_zero]
  have hz (j : I) : ∑ r, x r * flowMatrix a r j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnon j)).mp hsum j (by simp)
  refine ⟨x, hx, fun u => ?_⟩
  simp_rw [← flowMatrix_eval, Finset.mul_sum]
  calc
    ∑ r, ∑ j, x r * (u j * flowMatrix a r j) =
        ∑ j, u j * ∑ r, x r * flowMatrix a r j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring
    _ = 0 := by simp [hz]

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE StationaryLottery

-- BEGIN COMPLETE MODULE ProductLottery
section

open scoped BigOperators
namespace HartSchmeidler.Compact.Proof

variable {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*}
    [∀ i, Fintype (S i)]

noncomputable def productLottery (x : ∀ i, S i → ℝ) (s : ∀ i, S i) : ℝ :=
  ∏ i, x i (s i)

theorem productLottery_simplex (x : ∀ i, S i → ℝ) (hx : ∀ i, x i ∈ stdSimplex ℝ (S i)) :
    productLottery x ∈ stdSimplex ℝ (∀ i, S i) := by
  refine ⟨fun s => Finset.prod_nonneg fun i _ => (hx i).1 (s i), ?_⟩
  change (∑ s : ∀ i, S i, ∏ i, x i (s i)) = 1
  rw [← Fintype.prod_sum]
  simp [fun i => (hx i).2]

omit [Fintype I] [∀ i, Fintype (S i)] in
theorem splitAt_update (i : I) (r t : S i) (s : ∀ j : {j // j ≠ i}, S j) :
    Function.update ((Equiv.piSplitAt i S).symm (r,s)) i t =
      (Equiv.piSplitAt i S).symm (t,s) := by
  funext j
  by_cases hj : j = i
  · subst j; simp [Equiv.piSplitAt]
  · simp [Equiv.piSplitAt, hj]

omit [∀ i, Fintype (S i)] in
theorem productLottery_split (x : ∀ i, S i → ℝ) (i : I)
    (r : S i) (s : ∀ j : {j // j ≠ i}, S j) :
    productLottery x ((Equiv.piSplitAt i S).symm (r,s)) =
      x i r * ∏ j : {j // j ≠ i}, x j (s j) := by
  unfold productLottery
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  congr 1
  · simp [Equiv.piSplitAt]
  · apply Finset.prod_congr rfl
    intro j hj
    simp [Equiv.piSplitAt, j.property]

/-- Independent stationary lotteries cancel a player's full deviation array. -/
theorem productLottery_cancel (x : ∀ i, S i → ℝ) (i : I)
    (a : S i → S i → ℝ)
    (hx : ∀ u : S i → ℝ, ∑ r, x i r * ∑ t, a r t * (u r-u t) = 0)
    (h : (∀ i, S i) → ℝ) :
    ∑ s : ∀ i, S i, productLottery x s *
      ∑ t, a (s i) t * (h s - h (Function.update s i t)) = 0 := by
  classical
  rw [← (Equiv.piSplitAt i S).symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro s hs
  have he (r : S i) : (Equiv.piSplitAt i S).symm (r,s) i = r := by simp [Equiv.piSplitAt]
  simp only [he, splitAt_update, productLottery_split]
  calc
    _ = (∏ j : {j // j ≠ i}, x j (s j)) *
        ∑ r, x i r * ∑ t, a r t *
          (h ((Equiv.piSplitAt i S).symm (r,s)) -
           h ((Equiv.piSplitAt i S).symm (t,s))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = 0 := by rw [hx]; simp

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE ProductLottery

-- BEGIN COMPLETE MODULE FiniteEquilibrium
section

open scoped BigOperators
namespace HartSchmeidler.Compact.Proof

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {S : I → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]

noncomputable def deviationPayoff (h : I → (∀ i, S i) → ℝ)
    (s : ∀ i, S i) (d : Σ i, S i × S i) : ℝ := by
  classical
  exact if s d.1 = d.2.1 then h d.1 s - h d.1 (Function.update s d.1 d.2.2) else 0

omit [Nonempty I] [∀ i, Nonempty (S i)] in
theorem deviationPayoff_sum (h : I → (∀ i, S i) → ℝ)
    (y : (Σ i, S i × S i) → ℝ) (s : ∀ i, S i) :
    ∑ d, y d * deviationPayoff h s d =
      ∑ i, ∑ t, y ⟨i,(s i,t)⟩ * (h i s-h i (Function.update s i t)) := by
  classical
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, deviationPayoff, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  simp

open Classical in
/-- Finite correlated equilibrium obtained by two finite minimax arguments. -/
theorem finite_correlated_equilibrium (h : I → (∀ i, S i) → ℝ) :
    ∃ w ∈ stdSimplex ℝ (∀ i, S i), ∀ i (r t : S i),
      0 ≤ ∑ s, if s i = r then w s * (h i s-h i (Function.update s i t)) else 0 := by
  classical
  let : Nonempty (Σ i, S i × S i) := ⟨⟨Classical.choice ‹Nonempty I›,
    Classical.choice inferInstance, Classical.choice inferInstance⟩⟩
  obtain ⟨w, hw, hwA⟩ := finite_minimax_response (deviationPayoff h) (by
    intro y hy
    have hs (i : I) := stationary_lottery (fun r t : S i => y ⟨i,(r,t)⟩)
      (fun r t => hy.1 ⟨i,(r,t)⟩)
    choose x hx hc using hs
    refine ⟨productLottery x, productLottery_simplex x hx, ?_⟩
    have heq : (∑ s : ∀ i, S i, ∑ d, productLottery x s * y d * deviationPayoff h s d) = 0 := by
      simp_rw [mul_assoc, ← Finset.mul_sum, deviationPayoff_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro i hi
      simpa only [← Finset.mul_sum] using
        productLottery_cancel x i (fun r t => y ⟨i,(r,t)⟩) (hc i) (h i)
    exact heq.ge)
  refine ⟨w, hw, fun i r t => ?_⟩
  simpa [deviationPayoff, mul_ite] using hwA ⟨i,(r,t)⟩

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE FiniteEquilibrium

-- BEGIN COMPLETE MODULE FiniteLotteryImage
section

open scoped BigOperators
namespace HartSchmeidler.Compact.Proof

/-- Push a finite lottery through an injective profile map. -/
theorem finite_lottery_image {A B : Type*} [Fintype A]
    (e : A → B) (he : Function.Injective e) (w : A → ℝ) :
    ∃ F : Finset B, ∃ v : B → ℝ,
      (∀ b, b ∈ F ↔ ∃ a, e a = b) ∧ (∀ a, v (e a) = w a) ∧
      (∀ g : B → ℝ, ∑ b ∈ F, v b * g b = ∑ a, w a * g (e a)) := by
  classical
  let F := Finset.univ.image e
  let v : B → ℝ := fun b => if h : ∃ a, e a = b then w h.choose else 0
  have hv (a : A) : v (e a) = w a := by
    dsimp [v]
    rw [dif_pos ⟨a,rfl⟩]
    congr 1
    exact he (Classical.choose_spec (show ∃ x, e x = e a from ⟨a,rfl⟩))
  refine ⟨F, v, ?_, hv, ?_⟩
  · intro b; simp [F]
  · intro g
    rw [Finset.sum_image]
    · simp only [hv]
    · exact fun a _ b _ hab => he hab

open Classical in
/-- Finite-game existence also covers a vacant set of active players. -/
theorem finite_equilibrium_all {I : Type*} [Fintype I] [DecidableEq I]
    {S : I → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (h : I → (∀ i, S i) → ℝ) :
    ∃ w ∈ stdSimplex ℝ (∀ i, S i), ∀ i (r t : S i),
      0 ≤ ∑ s, if s i = r then w s * (h i s-h i (Function.update s i t)) else 0 := by
  cases isEmpty_or_nonempty I with
  | inl he =>
    refine ⟨fun _ => 1, ?_, fun i => isEmptyElim i⟩
    constructor
    · intro s; norm_num
    · simp
  | inr hn => exact finite_correlated_equilibrium h

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE FiniteLotteryImage

-- BEGIN COMPLETE MODULE AnchoredProfiles
section

open scoped BigOperators
namespace HartSchmeidler.Compact.Proof

variable {I : Type*} [DecidableEq I] {S : I → Type*}

noncomputable def activePlayers (T : ∀ i, Finset (S i)) (hf : IsFSet T) : Finset I :=
  hf.2.toFinset

omit [DecidableEq I] in
@[simp] theorem mem_activePlayers (T : ∀ i, Finset (S i)) (hf : IsFSet T) (i : I) :
    i ∈ activePlayers T hf ↔ (T i).card ≠ 1 := by
  simp [activePlayers]

noncomputable def extendActive (anchor : Profile S) (T : ∀ i, Finset (S i)) (hf : IsFSet T)
    (s : ∀ i : activePlayers T hf, {a // a ∈ T i}) : Profile S :=
  fun i => if hi : i ∈ activePlayers T hf then (s ⟨i,hi⟩).val else anchor i

@[simp] theorem extendActive_at (anchor : Profile S) (T : ∀ i, Finset (S i)) (hf : IsFSet T)
    (s : ∀ i : activePlayers T hf, {a // a ∈ T i}) (i : activePlayers T hf) :
    extendActive anchor T hf s i = (s i).val := by
  simp [extendActive, i.property]

theorem extendActive_injective (anchor : Profile S) (T : ∀ i, Finset (S i)) (hf : IsFSet T) :
    Function.Injective (extendActive anchor T hf) := by
  intro s t hst
  funext i
  apply Subtype.ext
  simpa using congrFun hst i

theorem extendActive_mem (anchor : Profile S) (T : ∀ i, Finset (S i))
    (hf : IsAnchoredFSet anchor T) (s : ∀ i : activePlayers T hf.1, {a // a ∈ T i}) :
    ∀ i, extendActive anchor T hf.1 s i ∈ T i := by
  intro i
  dsimp [extendActive]
  split
  · rename_i hi
    exact (s ⟨i,hi⟩).property
  · exact hf.2 i

omit [DecidableEq I] in
theorem inactive_eq_anchor (anchor : Profile S) (T : ∀ i, Finset (S i))
    (hf : IsAnchoredFSet anchor T) {i : I} (hi : i ∉ activePlayers T hf.1)
    {a : S i} (ha : a ∈ T i) : a = anchor i := by
  have hc : (T i).card = 1 := by simpa using hi
  exact (Finset.card_le_one.mp hc.le) a ha (anchor i) (hf.2 i)

theorem extendActive_update (anchor : Profile S) (T : ∀ i, Finset (S i)) (hf : IsFSet T)
    (s : ∀ i : activePlayers T hf, {a // a ∈ T i}) (i : activePlayers T hf)
    (t : {a // a ∈ T i}) :
    extendActive anchor T hf (Function.update s i t) =
      Function.update (extendActive anchor T hf s) i t.val := by
  classical
  funext j
  change extendActive anchor T hf (Function.update s i t) j =
    Function.update (fun k => extendActive anchor T hf s k) i.val t.val j
  by_cases hj : j = i.val
  · subst j; simp
  · by_cases hja : j ∈ activePlayers T hf
    · rw [Function.update_of_ne hj]
      have hne : (⟨j,hja⟩ : activePlayers T hf) ≠ i := fun h => hj (congrArg Subtype.val h)
      simp [extendActive, hja, hne]
    · rw [Function.update_of_ne hj]
      simp [extendActive, hja]

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE AnchoredProfiles

-- BEGIN COMPLETE MODULE AnchoredEquilibrium
section

open scoped BigOperators
namespace HartSchmeidler.Compact.Proof

/-- Every anchored f-set carries an actual finite-support correlated lottery. -/
theorem anchored_equilibrium {I : Type*} [DecidableEq I] {S : I → Type*}
    (h : I → Profile S → ℝ) (anchor : Profile S) (T : ∀ i, Finset (S i))
    (hT : IsAnchoredFSet anchor T) :
    ∃ F w, IsFSetCE h T F w := by
  classical
  let A := activePlayers T hT.1
  let R : A → Type _ := fun i => {a // a ∈ T i}
  let instN : ∀ i : A, Nonempty (R i) := fun i =>
    let ⟨a,ha⟩ := hT.1.1 i
    ⟨⟨a,ha⟩⟩
  let e : (∀ i, R i) → Profile S := extendActive anchor T hT.1
  obtain ⟨w, hw, hce⟩ := finite_equilibrium_all (fun i : A => fun s => h i (e s))
  obtain ⟨F,v,hF,hv,hsum⟩ := finite_lottery_image e
    (extendActive_injective anchor T hT.1) w
  refine ⟨F,v,?_,?_,?_,?_⟩
  · intro s hs i
    obtain ⟨a,rfl⟩ := (hF s).mp hs
    exact extendActive_mem anchor T hT a i
  · intro s hs
    obtain ⟨a,rfl⟩ := (hF s).mp hs
    rw [hv]
    exact hw.1 a
  · simpa using (hsum (fun _ => 1)).trans (by simpa using hw.2)
  · intro i r hr t ht
    by_cases hi : i ∈ A
    · let ii : A := ⟨i,hi⟩
      let rr : R ii := ⟨r,hr⟩
      let tt : R ii := ⟨t,ht⟩
      have hc := hce ii rr tt
      have he (s : ∀ j, R j) : e (Function.update s ii tt) =
          Function.update (e s) i t := extendActive_update anchor T hT.1 s ii tt
      have hcoord (s : ∀ j, R j) : e s i = (s ii).val := extendActive_at _ _ _ s ii
      have htest := hsum (fun s => if s i = r then h i s - h i (Function.update s i t) else 0)
      rw [Finset.sum_filter]
      have hleft : (∑ s ∈ F, if s i = r then v s * (h i s-h i (Function.update s i t)) else 0) =
          ∑ s, if s ii = rr then w s * (h i (e s)-h i (e (Function.update s ii tt))) else 0 := by
        calc
          _ = ∑ s, w s * (if e s i = r then h i (e s) - h i (Function.update (e s) i t) else 0) := by
            simpa only [mul_ite, mul_zero] using htest
          _ = _ := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [hcoord, he]
            by_cases hvv : (s ii).val = r
            · have heq : s ii = rr := Subtype.ext hvv
              simp only [if_pos hvv, if_pos heq]
            · have hne : s ii ≠ rr := fun hh => hvv (congrArg Subtype.val hh)
              simp only [if_neg hvv, if_neg hne, mul_zero]
      rw [hleft]
      simpa only [ii] using hc
    · have hrt : r = t := (inactive_eq_anchor anchor T hT hi hr).trans
        (inactive_eq_anchor anchor T hT hi ht).symm
      subst t
      apply Finset.sum_nonneg
      intro s hs
      have hsr := (Finset.mem_filter.mp hs).2
      have hu : Function.update s i r = s := by rw [← hsr]; exact Function.update_eq_self i s
      simp [hu]

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE AnchoredEquilibrium

-- BEGIN COMPLETE MODULE AnchoredIndex
section

namespace HartSchmeidler.Compact.Proof
variable {I : Type*} [DecidableEq I] {S : I → Type*}

abbrev AnchoredIndex (anchor : Profile S) := {T : ∀ i, Finset (S i) // IsAnchoredFSet anchor T}

omit [DecidableEq I] in
theorem anchored_singletons (anchor : Profile S) :
    IsAnchoredFSet anchor (fun i => {anchor i}) := by
  refine ⟨⟨fun i => Finset.singleton_nonempty _, ?_⟩, fun i => Finset.mem_singleton_self _⟩
  simp

instance anchoredIndex_nonempty (anchor : Profile S) : Nonempty (AnchoredIndex anchor) :=
  ⟨⟨fun i => {anchor i}, anchored_singletons anchor⟩⟩

omit [DecidableEq I] in
theorem anchored_card_one {anchor : Profile S} {T : ∀ i, Finset (S i)}
    (hT : IsAnchoredFSet anchor T) (i : I) (hc : (T i).card = 1) : T i = {anchor i} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  exact ⟨hT.2 i, fun x hx => (Finset.card_le_one.mp hc.le) x hx (anchor i) (hT.2 i)⟩

open Classical in
omit [DecidableEq I] in
theorem anchored_union {anchor : Profile S} {T U : ∀ i, Finset (S i)}
    (hT : IsAnchoredFSet anchor T) (hU : IsAnchoredFSet anchor U) :
    IsAnchoredFSet anchor (fun i => T i ∪ U i) := by
  refine ⟨⟨fun i => (hT.1.1 i).mono Finset.subset_union_left, ?_⟩,
    fun i => Finset.mem_union_left _ (hT.2 i)⟩
  apply (hT.1.2.union hU.1.2).subset
  intro i hi
  by_contra hn
  have ht : (T i).card = 1 := by simpa using (not_or.mp hn).1
  have hu : (U i).card = 1 := by simpa using (not_or.mp hn).2
  have : (T i ∪ U i).card = 1 := by
    rw [anchored_card_one hT i ht, anchored_card_one hU i hu]
    simp
  exact hi this

noncomputable instance anchoredIndex_directed (anchor : Profile S) :
    IsDirected (AnchoredIndex anchor) (· ≤ ·) := by
  classical
  constructor
  intro T U
  exact ⟨⟨fun i => T.val i ∪ U.val i, anchored_union T.property U.property⟩,
    fun i => Finset.subset_union_left, fun i => Finset.subset_union_right⟩

noncomputable def anchoredTarget (anchor : Profile S) (i : I) (t : S i) : AnchoredIndex anchor := by
  classical
  let T : ∀ j, Finset (S j) := Function.update (fun j => {anchor j}) i {anchor i,t}
  refine ⟨T, ⟨⟨?_,?_⟩,?_⟩⟩
  · intro j
    by_cases hj : j = i
    · subst j; simp [T]
    · simp [T,hj]
  · apply (Set.finite_singleton i).subset
    intro j hj
    by_contra hji
    have hne : j ≠ i := by simpa using hji
    exact hj (by simp [T,hne])
  · intro j
    by_cases hj : j = i
    · subst j; simp [T]
    · simp [T,hj]

@[simp] theorem mem_anchoredTarget (anchor : Profile S) (i : I) (t : S i) :
    t ∈ (anchoredTarget anchor i t).val i := by
  classical
  simp [anchoredTarget]

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE AnchoredIndex

-- BEGIN COMPLETE MODULE FiniteLotteryMeasure
section

open MeasureTheory
open scoped BigOperators
namespace HartSchmeidler.Compact.Proof

variable {X : Type*} [MeasurableSpace X]

noncomputable def finiteLotteryMeasure (F : Finset X) (w : X → ℝ) : Measure X :=
  ∑ x ∈ F, ENNReal.ofReal (w x) • Measure.dirac x

theorem finiteLotteryMeasure_probability (F : Finset X) (w : X → ℝ)
    (hw : ∀ x ∈ F, 0 ≤ w x) (hs : ∑ x ∈ F, w x = 1) :
    IsProbabilityMeasure (finiteLotteryMeasure F w) := by
  constructor
  simp only [finiteLotteryMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg hw, hs]
  norm_num

theorem finiteLotteryMeasure_integrable [MeasurableSingletonClass X]
    (F : Finset X) (w g : X → ℝ) : Integrable g (finiteLotteryMeasure F w) := by
  apply integrable_finsetSum_measure.mpr
  intro x hx
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem finiteLotteryMeasure_integral [MeasurableSingletonClass X]
    (F : Finset X) (w : X → ℝ) (hw : ∀ x ∈ F, 0 ≤ w x) (g : X → ℝ) :
    (∫ x, g x ∂finiteLotteryMeasure F w) = ∑ x ∈ F, w x * g x := by
  rw [finiteLotteryMeasure, integral_finsetSum_measure (fun x hx =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw x hx)]
  rfl

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE FiniteLotteryMeasure

-- BEGIN COMPLETE MODULE FiniteWeightedGain
section

open scoped BigOperators
namespace HartSchmeidler.Compact.Proof

/-- Recommendation inequalities can be combined with any nonnegative recommendation weight. -/
theorem fset_ce_weighted {I : Type*} [DecidableEq I] {S : I → Type*}
    {h : I → Profile S → ℝ} {T : ∀ i, Finset (S i)} {F : Finset (Profile S)}
    {w : Profile S → ℝ} (hce : IsFSetCE h T F w) (i : I) {t : S i} (ht : t ∈ T i)
    (φ : S i → ℝ) (hφ : ∀ r, 0 ≤ φ r) :
    0 ≤ ∑ s ∈ F, w s * (φ (s i) * (h i s-h i (Function.update s i t))) := by
  classical
  have hn : 0 ≤ ∑ r ∈ T i, φ r *
      ∑ s ∈ F.filter (fun s => s i = r), w s * (h i s-h i (Function.update s i t)) := by
    exact Finset.sum_nonneg fun r hr => mul_nonneg (hφ r) (hce.2.2.2 i r hr t ht)
  have heq : (∑ r ∈ T i, φ r *
      ∑ s ∈ F.filter (fun s => s i = r), w s * (h i s-h i (Function.update s i t))) =
        ∑ s ∈ F, w s * (φ (s i) * (h i s-h i (Function.update s i t))) := by
    simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.sum_ite_eq, if_pos (hce.1 s hs i)]
    ring
  exact heq ▸ hn

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE FiniteWeightedGain

-- BEGIN COMPLETE MODULE ProbabilityFunctional
section

open MeasureTheory Topology
namespace HartSchmeidler.Compact.Proof

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma continuous_integrable (μ : Measure X) [IsFiniteMeasure μ] (f : C(X,ℝ)) :
    Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

noncomputable def probabilityFunctional (μ : Measure X) [IsProbabilityMeasure μ] :
    StrongDual ℝ C(X,ℝ) :=
  ({ toFun := fun f => ∫ x, f x ∂μ
     map_add' := fun f g => integral_add (continuous_integrable μ f) (continuous_integrable μ g)
     map_smul' := fun c f => integral_smul c f } : C(X,ℝ) →ₗ[ℝ] ℝ).mkContinuous 1 (by
       intro f
       simpa using norm_integral_le_of_norm_le_const (μ := μ)
         (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x)))

lemma probabilityFunctional_apply (μ : Measure X) [IsProbabilityMeasure μ] (f : C(X,ℝ)) :
    probabilityFunctional μ f = ∫ x, f x ∂μ := rfl

lemma probabilityFunctional_norm (μ : Measure X) [IsProbabilityMeasure μ] :
    ‖probabilityFunctional μ‖ ≤ 1 := by
  apply (probabilityFunctional μ).opNorm_le_bound (by norm_num)
  intro f
  simpa [probabilityFunctional_apply] using norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x))

lemma probabilityFunctional_one (μ : Measure X) [IsProbabilityMeasure μ] :
    probabilityFunctional μ 1 = 1 := by
  simp [probabilityFunctional_apply]

lemma probabilityFunctional_nonneg (μ : Measure X) [IsProbabilityMeasure μ]
    (f : C(X,ℝ)) (hf : 0 ≤ f) : 0 ≤ probabilityFunctional μ f := by
  exact integral_nonneg (fun x => hf x)

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE ProbabilityFunctional

-- BEGIN COMPLETE MODULE CompactStates
section

open MeasureTheory Filter Topology Set
namespace HartSchmeidler.Compact.Proof
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Positive unital functionals in the weak-dual unit ball. -/
def stateSet : Set (WeakDual ℝ C(X,ℝ)) :=
  (WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1) ∩
    {L | L 1 = 1 ∧ ∀ f : C(X,ℝ), 0 ≤ f → 0 ≤ L f}

lemma stateSet_compact : IsCompact (stateSet (X := X)) := by
  apply (WeakDual.isCompact_closedBall (0 : StrongDual ℝ C(X,ℝ)) 1).inter_right
  have hp : IsClosed {L : WeakDual ℝ C(X,ℝ) | ∀ f : C(X,ℝ), 0 ≤ f → 0 ≤ L f} := by
    rw [show {L : WeakDual ℝ C(X,ℝ) | ∀ f : C(X,ℝ), 0 ≤ f → 0 ≤ L f} =
      ⋂ f : C(X,ℝ), ⋂ (_ : 0 ≤ f), {L : WeakDual ℝ C(X,ℝ) | 0 ≤ L f} by ext; simp]
    exact isClosed_iInter (fun f => isClosed_iInter (fun _ =>
      isClosed_le continuous_const (WeakDual.eval_continuous f)))
  exact (isClosed_eq (WeakDual.eval_continuous 1) continuous_const).inter hp

lemma probabilityFunctional_mem_stateSet [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] :
    (probabilityFunctional μ).toWeakDual ∈ stateSet := by
  refine ⟨?_,probabilityFunctional_one μ,probabilityFunctional_nonneg μ⟩
  change dist (probabilityFunctional μ) (0 : StrongDual ℝ C(X,ℝ)) ≤ 1
  have hd := dist_eq_norm (probabilityFunctional μ) (0 : StrongDual ℝ C(X,ℝ))
  rw [hd,sub_zero]
  exact probabilityFunctional_norm μ

lemma stateSet_exists_cluster [MeasurableSpace X] [BorelSpace X]
    {D : Type*} [Preorder D] [IsDirected D (· ≤ ·)] [Nonempty D]
    (q : D → Measure X) (hq : ∀ d, IsProbabilityMeasure (q d)) :
    ∃ L ∈ stateSet (X := X), ∀ (f : C(X,ℝ)) (ε : ℝ), 0 < ε → ∀ d₀ : D,
      ∃ d, d₀ ≤ d ∧ |L f - ∫ x, f x ∂q d| < ε := by
  let F : D → WeakDual ℝ C(X,ℝ) := fun d =>
    let : IsProbabilityMeasure (q d) := hq d
    (probabilityFunctional (q d)).toWeakDual
  have hF : ∀ d, F d ∈ stateSet := fun d => by
    let : IsProbabilityMeasure (q d) := hq d
    exact probabilityFunctional_mem_stateSet (q d)
  obtain ⟨L,hL,hcluster⟩ := stateSet_compact.exists_mapClusterPt
    (f := atTop) (u := F) (by
      rw [Filter.le_principal_iff]
      change ∀ᶠ d in atTop, F d ∈ stateSet
      exact Filter.Eventually.of_forall hF)
  refine ⟨L,hL,?_⟩
  intro f ε hε d₀
  have hopen : IsOpen {A : WeakDual ℝ C(X,ℝ) | |L f - A f| < ε} :=
    isOpen_lt ((continuous_const.sub (WeakDual.eval_continuous f)).abs) continuous_const
  have hn : {A : WeakDual ℝ C(X,ℝ) | |L f - A f| < ε} ∈ 𝓝 L :=
    hopen.mem_nhds (by simpa using hε)
  obtain ⟨d,hd,hge⟩ := (hcluster.frequently hn).and_eventually (eventually_ge_atTop d₀) |>.exists
  exact ⟨d,hge,hd⟩

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE CompactStates

-- BEGIN COMPLETE MODULE StateMeasure
section

open MeasureTheory Topology CompactlySupported
namespace HartSchmeidler.Compact.Proof
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

noncomputable def statePositive (L : WeakDual ℝ C(X,ℝ)) (hL : L ∈ stateSet) :
    C_c(X,ℝ) →ₚ[ℝ] ℝ where
  toFun f := L f.toContinuousMap
  map_add' f g := by
    change L (f.toContinuousMap + g.toContinuousMap) = _
    exact map_add L _ _
  map_smul' c f := by
    change L (c • f.toContinuousMap) = c * L f.toContinuousMap
    exact map_smul L c f.toContinuousMap
  monotone' f g hfg := by
    have h := hL.2.2 (g.toContinuousMap - f.toContinuousMap) (fun x => sub_nonneg.mpr (hfg x))
    simpa only [map_sub,sub_nonneg] using h

lemma state_measure (L : WeakDual ℝ C(X,ℝ)) (hL : L ∈ stateSet) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ μ.Regular ∧
      ∀ f : C(X,ℝ), ∫ x, f x ∂μ = L f := by
  let Λ := statePositive L hL
  let μ := RealRMK.rieszMeasure Λ
  have htest : ∀ f : C(X,ℝ), ∫ x, f x ∂μ = L f := by
    intro f
    let g : C_c(X,ℝ) := ⟨f,HasCompactSupport.of_compactSpace f⟩
    exact RealRMK.integral_rieszMeasure Λ g
  have hmass : μ Set.univ = 1 := by
    have h := htest 1
    have hi : (∫ x, (1 : C(X,ℝ)) x ∂μ) = 1 := h.trans hL.2.1
    have hr : μ.real Set.univ = 1 := by simpa using hi
    exact (ENNReal.toReal_eq_one_iff _).mp hr
  exact ⟨μ,⟨hmass⟩,by infer_instance,htest⟩

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE StateMeasure

-- BEGIN COMPLETE MODULE RegularCluster
section

open MeasureTheory
namespace HartSchmeidler.Compact.Proof
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

lemma regular_probability_cluster {D : Type*} [Preorder D]
    [IsDirected D (· ≤ ·)] [Nonempty D]
    (q : D → Measure X) (hq : ∀ d, IsProbabilityMeasure (q d)) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ μ.Regular ∧
      ∀ (f : C(X,ℝ)) (ε : ℝ), 0 < ε → ∀ d₀ : D,
        ∃ d, d₀ ≤ d ∧ |(∫ x, f x ∂μ) - ∫ x, f x ∂q d| < ε := by
  obtain ⟨L,hL,hc⟩ := stateSet_exists_cluster q hq
  obtain ⟨μ,hμ,hr,ht⟩ := state_measure L hL
  refine ⟨μ,hμ,hr,?_⟩
  intro f ε hε d₀
  simpa only [ht f] using hc f ε hε d₀

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE RegularCluster

-- BEGIN COMPLETE MODULE CompactGameBasic
section

open MeasureTheory Topology Set
namespace HartSchmeidler.Compact.Proof
variable {ι : Type*} [DecidableEq ι] {S : ι → Type*}
  [∀ i, TopologicalSpace (S i)]

omit [DecidableEq ι] in
lemma profile_eval_continuous (i : ι) : Continuous (fun s : Profile S => s i) :=
  continuous_apply i

lemma profile_update_continuous (i : ι) (t : S i) :
    Continuous (fun s : Profile S => (Function.update s i t : Profile S)) := by
  change Continuous (fun s : (∀ j, S j) => Function.update s i t)
  fun_prop

lemma profile_update_joint_continuous (i : ι) :
    Continuous (fun z : S i × Profile S => (Function.update z.2 i z.1 : Profile S)) := by
  change Continuous (fun z : S i × (∀ j, S j) => Function.update z.2 i z.1)
  fun_prop

def fixedGain (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i))
    (i : ι) (t : S i) : C(Profile S,ℝ) :=
  ⟨fun s => h i s - h i (Function.update s i t),
    (hcont i).sub ((hcont i).comp (profile_update_continuous i t))⟩

@[simp] lemma fixedGain_apply (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i))
    (i : ι) (t : S i) (s : Profile S) :
    fixedGain h hcont i t s = h i s - h i (Function.update s i t) := rfl

omit [∀ i, TopologicalSpace (S i)] in
lemma special_gain_eq_indicator (h : ι → Profile S → ℝ) (i : ι) (t : S i)
    (R : Set (S i)) (s : Profile S) :
    h i s - h i (Function.update s i (specialDeviation t R (s i))) =
      (fun s : Profile S => R.indicator (fun _ => (1:ℝ)) (s i)) s *
        (h i s - h i (Function.update s i t)) := by
  classical
  by_cases hs : s i ∈ R
  · simp [specialDeviation,hs]
  · have he : (Function.update s i (s i) : Profile S) = s := Function.update_eq_self i s
    simp only [specialDeviation,if_neg hs,Set.indicator_of_notMem hs,zero_mul]
    rw [he,sub_self]

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE CompactGameBasic

-- BEGIN COMPLETE MODULE WeightedCluster
section

open MeasureTheory Topology
namespace HartSchmeidler.Compact.Proof

/-- A regular probability satisfying every continuous weighted fixed-action incentive. -/
theorem exists_weighted_equilibrium {I : Type*} [DecidableEq I] {S : I → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, Nonempty (S i)]
    (h : I → Profile S → ℝ) (hcont : ∀ i, Continuous (h i)) :
    ∃ μ : Measure (Profile S), IsProbabilityMeasure μ ∧ μ.Regular ∧
      ∀ (i : I) (t : S i) (φ : C(S i,ℝ)), 0 ≤ φ →
        0 ≤ ∫ s, φ (s i) * fixedGain h hcont i t s ∂μ := by
  classical
  let anchor : Profile S := Classical.choice inferInstance
  let D := AnchoredIndex anchor
  have hex (d : D) : ∃ F w, IsFSetCE h d.val F w :=
    anchored_equilibrium h anchor d.val d.property
  choose F w hc using hex
  let q : D → Measure (Profile S) := fun d => finiteLotteryMeasure (F d) (w d)
  have hq (d : D) : IsProbabilityMeasure (q d) :=
    finiteLotteryMeasure_probability (F d) (w d) (hc d).2.1 (hc d).2.2.1
  obtain ⟨μ,hμ,hr,hcluster⟩ := regular_probability_cluster q hq
  refine ⟨μ,hμ,hr,?_⟩
  intro i t φ hφ
  let g : C(Profile S,ℝ) :=
    ⟨fun s => φ (s i) * fixedGain h hcont i t s,
      (φ.continuous.comp (profile_eval_continuous i)).mul (fixedGain h hcont i t).continuous⟩
  change 0 ≤ ∫ s, g s ∂μ
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨d,hd,hclose⟩ := hcluster g ε hε (anchoredTarget anchor i t)
  have ht : t ∈ d.val i := hd i (mem_anchoredTarget anchor i t)
  have hnon : 0 ≤ ∫ s, g s ∂q d := by
    rw [show q d = finiteLotteryMeasure (F d) (w d) from rfl,
      finiteLotteryMeasure_integral _ _ (hc d).2.1]
    exact fset_ce_weighted (hc d) i ht φ hφ
  have hb := (abs_lt.mp hclose).1
  linarith

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE WeightedCluster

-- BEGIN COMPLETE MODULE RegularIndicator
section

open MeasureTheory Set Topology
namespace HartSchmeidler.Compact.Proof
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

lemma continuous_indicator_approx (μ : Measure X) [IsFiniteMeasure μ]
    [μ.InnerRegularCompactLTTop] {R : Set X} (hR : MeasurableSet R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : C(X,ℝ), (∀ x, φ x ∈ Icc (0:ℝ) 1) ∧
      (∫ x, |R.indicator (fun _ => (1:ℝ)) x - φ x| ∂μ) < ε := by
  have he : ENNReal.ofReal (ε/2) ≠ 0 := by positivity
  obtain ⟨K,hKR,hK,hμK⟩ := hR.exists_isCompact_sdiff_lt (measure_ne_top μ R) he
  obtain ⟨J,hJR,hJ,hμJ⟩ := hR.compl.exists_isCompact_sdiff_lt (measure_ne_top μ Rᶜ) he
  have hd : Disjoint J K := Set.disjoint_left.mpr (fun x hxJ hxK => hJR hxJ (hKR hxK))
  obtain ⟨φ,hφJ,hφK,hφ⟩ := exists_continuous_zero_one_of_isClosed hJ.isClosed hK.isClosed hd
  let B := (K ∪ J)ᶜ
  have hB : MeasurableSet B := (hK.isClosed.union hJ.isClosed).measurableSet.compl
  have hsub : B ⊆ (R \ K) ∪ (Rᶜ \ J) := by
    intro x hx
    simp only [B,mem_compl_iff,mem_union] at hx
    by_cases hr : x ∈ R
    · exact Or.inl ⟨hr,fun hk => hx (Or.inl hk)⟩
    · exact Or.inr ⟨hr,fun hj => hx (Or.inr hj)⟩
  have hμB : μ B < ENNReal.ofReal ε := calc
    μ B ≤ μ ((R \ K) ∪ (Rᶜ \ J)) := measure_mono hsub
    _ ≤ μ (R \ K) + μ (Rᶜ \ J) := measure_union_le _ _
    _ < ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := ENNReal.add_lt_add hμK hμJ
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hi : Integrable (fun x => |R.indicator (fun _ => (1:ℝ)) x - φ x|) μ :=
    ((integrable_const (1:ℝ)).indicator hR |>.sub
      (φ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace φ))).abs
  have hbound : ∀ x, |R.indicator (fun _ => (1:ℝ)) x - φ x| ≤ B.indicator (fun _ => (1:ℝ)) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      by_cases hr : x ∈ R
      · rw [Set.indicator_of_mem hr,abs_of_nonneg (by linarith [(hφ x).2])]
        linarith [(hφ x).1]
      · rw [Set.indicator_of_notMem hr,zero_sub,abs_neg,abs_of_nonneg (hφ x).1]
        exact (hφ x).2
    · rw [Set.indicator_of_notMem hx]
      have hx' : x ∈ K ∪ J := by
        by_contra hn
        exact hx hn
      rcases hx' with hk | hj
      · rw [Set.indicator_of_mem (hKR hk),hφK hk]; simp
      · rw [Set.indicator_of_notMem (hJR hj),hφJ hj]; simp
  refine ⟨φ,hφ,?_⟩
  have hb := integral_mono hi ((integrable_const (1:ℝ)).indicator hB) hbound
  have hbi : (∫ x, B.indicator (fun _ => (1:ℝ)) x ∂μ) = μ.real B :=
    integral_indicator_one hB
  rw [hbi] at hb
  exact hb.trans_lt (ENNReal.toReal_lt_of_lt_ofReal hμB)

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE RegularIndicator

-- BEGIN COMPLETE MODULE BorelWeight
section

open MeasureTheory Set
namespace HartSchmeidler.Compact.Proof
variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
  [MeasurableSpace Y] [BorelSpace Y]

lemma borel_weight_nonneg (μ : Measure X) [IsProbabilityMeasure μ]
    [μ.InnerRegularCompactLTTop] (p : C(X,Y)) (g : C(X,ℝ))
    (hpos : ∀ φ : C(Y,ℝ), 0 ≤ φ → 0 ≤ ∫ x, φ (p x) * g x ∂μ)
    {R : Set Y} (hR : MeasurableSet R) :
    Integrable (fun x => R.indicator (fun _ => (1:ℝ)) (p x) * g x) μ ∧
      0 ≤ ∫ x, R.indicator (fun _ => (1:ℝ)) (p x) * g x ∂μ := by
  classical
  let r : X → ℝ := fun x => R.indicator (fun _ => (1:ℝ)) (p x)
  have hrm : Measurable r := (measurable_const.indicator hR).comp p.continuous.measurable
  have hrb : ∀ x, ‖r x‖ ≤ 1 := by
    intro x
    by_cases hx : p x ∈ R <;> simp [r,hx]
  have hrg : Integrable (fun x => r x * g x) μ :=
    (continuous_integrable μ g).bdd_mul hrm.aestronglyMeasurable
      (Filter.Eventually.of_forall hrb)
  refine ⟨hrg,?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  let ν := μ.map p
  let : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map p.continuous.aemeasurable
  let : ν.InnerRegularCompactLTTop :=
    Measure.InnerRegularCompactLTTop.map_of_continuous p.continuous
  have hM : 0 < ‖g‖ + 1 := by positivity
  obtain ⟨φ,hφ,herr⟩ := continuous_indicator_approx ν hR (div_pos hε hM)
  have hib : Integrable (fun x => |r x - φ (p x)|) μ := by
    have hr : Integrable r μ := (integrable_const (1:ℝ)).mono' hrm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hrb x))
    exact (hr.sub (continuous_integrable μ (φ.comp p))).abs
  have herr' : (∫ x, |r x - φ (p x)| ∂μ) < ε / (‖g‖ + 1) := by
    have hm : AEStronglyMeasurable (fun y => |R.indicator (fun _ => (1:ℝ)) y - φ y|) ν :=
      (((measurable_const.indicator hR).sub φ.continuous.measurable).abs.aestronglyMeasurable)
    have he := integral_map p.continuous.aemeasurable hm
    change (∫ y, |R.indicator (fun _ => (1:ℝ)) y - φ y| ∂ν) =
      (∫ x, |r x - φ (p x)| ∂μ) at he
    rwa [← he]
  have hip : Integrable (fun x => φ (p x) * g x) μ :=
    continuous_integrable μ ((φ.comp p) * g)
  have hide : Integrable (fun x => (r x - φ (p x)) * g x) μ := by
    convert hrg.sub hip using 1
    ext x
    simp only [Pi.sub_apply]
    ring
  have hierr : Integrable (fun x => (‖g‖ + 1) * |r x - φ (p x)|) μ :=
    hib.const_mul _
  have hpoint : ∀ x, -((r x - φ (p x)) * g x) ≤
      (‖g‖ + 1) * |r x - φ (p x)| := by
    intro x
    calc
      -((r x - φ (p x)) * g x) ≤ |(r x - φ (p x)) * g x| := neg_le_abs _
      _ = |r x - φ (p x)| * |g x| := abs_mul _ _
      _ ≤ |r x - φ (p x)| * (‖g‖ + 1) :=
        mul_le_mul_of_nonneg_left ((g.norm_coe_le_norm x).trans (by linarith)) (abs_nonneg _)
      _ = _ := mul_comm _ _
  have hb := integral_mono hide.neg hierr hpoint
  change (∫ x, -((r x - φ (p x)) * g x) ∂μ) ≤ _ at hb
  rw [integral_neg,integral_const_mul] at hb
  have hid : (∫ x, (r x - φ (p x)) * g x ∂μ) =
      (∫ x, r x * g x ∂μ) - ∫ x, φ (p x) * g x ∂μ := by
    rw [← integral_sub hrg hip]
    congr 1
    ext x
    ring
  rw [hid] at hb
  have hsmall : (‖g‖ + 1) * (∫ x, |r x - φ (p x)| ∂μ) < ε :=
    by have hh := (lt_div_iff₀ hM).mp herr'; nlinarith
  have hp := hpos φ (fun y => (hφ y).1)
  linarith

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE BorelWeight

-- BEGIN COMPLETE MODULE UniformPayoffCover
section

open MeasureTheory Topology Set
namespace HartSchmeidler.Compact.Proof
variable {ι : Type*} [DecidableEq ι] {S : ι → Type*}
  [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)]
  [∀ i, Nonempty (S i)]

noncomputable def payoffSections (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i))
    (i : ι) : C(S i,C(Profile S,ℝ)) :=
  ContinuousMap.curry ⟨fun z : S i × Profile S => h i (Function.update z.2 i z.1),
    (hcont i).comp (profile_update_joint_continuous i)⟩

omit [∀ i, Nonempty (S i)] in
lemma uniform_payoff_cover (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i))
    (i : ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (a : Fin m → S i) (U : Fin m → Set (S i)),
      (∀ j, IsOpen (U j)) ∧ (∀ x, ∃ j, x ∈ U j) ∧
      ∀ j, ∀ x ∈ U j, ∀ s : Profile S,
        |h i (Function.update s i x) - h i (Function.update s i (a j))| < ε := by
  classical
  let F := payoffSections h hcont i
  let O := fun a : S i => {x | ‖F x - F a‖ < ε}
  have hO : ∀ a, IsOpen (O a) := fun a =>
    isOpen_lt ((F.continuous.sub continuous_const).norm) continuous_const
  have hcover : Set.univ ⊆ ⋃ a, O a := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x,by simpa [O] using hε⟩
  obtain ⟨A,hA⟩ := isCompact_univ.elim_finite_subcover O hO hcover
  let e : Fin A.card ≃ A := by simpa only [Fintype.card_coe] using (Fintype.equivFin A).symm
  refine ⟨A.card,fun j => (e j).val,fun j => O (e j),fun j => hO _,?_,?_⟩
  · intro x
    obtain ⟨a,ha,hxa⟩ := Set.mem_iUnion₂.mp (hA (Set.mem_univ x))
    exact ⟨e.symm ⟨a,ha⟩,by simpa using hxa⟩
  · intro j x hx s
    have hb := (F x - F (e j)).norm_coe_le_norm s
    have hlt : ‖F x - F (e j)‖ < ε := hx
    exact lt_of_le_of_lt (by simpa [F,payoffSections] using hb) hlt

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE UniformPayoffCover

-- BEGIN COMPLETE MODULE FinitePartition
section

open Set
namespace HartSchmeidler.Compact.Proof

lemma finite_measurable_partition {X : Type*} [MeasurableSpace X] {m : ℕ}
    (U : Fin m → Set X) (hU : ∀ j, MeasurableSet (U j))
    (hcover : ∀ x, ∃ j, x ∈ U j) :
    ∃ R : Fin m → Set X, (∀ j, MeasurableSet (R j)) ∧
      (∀ j, R j ⊆ U j) ∧ (∀ x, ∃! j, x ∈ R j) := by
  classical
  let R := fun j : Fin m => U j \ ⋃ k : {k : Fin m // k < j}, U k
  have hR : ∀ j, MeasurableSet (R j) := fun j =>
    (hU j).diff (MeasurableSet.iUnion (fun k => hU k))
  refine ⟨R,hR,fun j => Set.sdiff_subset,?_⟩
  intro x
  let A := Finset.univ.filter (fun j : Fin m => x ∈ U j)
  have hA : A.Nonempty := by
    obtain ⟨j,hj⟩ := hcover x
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  let j := A.min' hA
  have hjA : j ∈ A := Finset.min'_mem _ _
  have hj : x ∈ R j := by
    refine ⟨(Finset.mem_filter.mp hjA).2,?_⟩
    intro hx
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
    have hkj := Finset.min'_le A k.val (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩)
    exact (not_lt_of_ge hkj) k.property
  refine ⟨j,hj,?_⟩
  intro k hk
  by_contra hne
  rcases lt_or_gt_of_ne hne with hkj | hjk
  · exact hj.2 (Set.mem_iUnion.mpr ⟨⟨k,hkj⟩,hk.1⟩)
  · exact hk.2 (Set.mem_iUnion.mpr ⟨⟨j,hjk⟩,hj.1⟩)

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE FinitePartition

-- BEGIN COMPLETE MODULE UniformPositiveLimit
section

open MeasureTheory Filter Topology
namespace HartSchmeidler.Compact.Proof

lemma uniform_positive_limit {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) {M : ℝ}
    (hf : ∀ x, |f x| ≤ M)
    (ha : ∀ ε : ℝ, 0 < ε → ∃ g : X → ℝ, Measurable g ∧ Integrable g μ ∧
      0 ≤ (∫ x, g x ∂μ) ∧ ∀ x, |f x - g x| < ε) :
    Integrable f μ ∧ 0 ≤ ∫ x, f x ∂μ := by
  have hε : ∀ n : ℕ, 0 < (1:ℝ) / (n + 1) := fun n => by positivity
  choose g hgm hgi hgp hge using fun n : ℕ => ha (1 / ((n:ℝ) + 1)) (hε n)
  have hlim : Tendsto g atTop (𝓝 f) := by
    apply tendsto_pi_nhds.mpr
    intro x
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [Real.dist_eq,abs_sub_comm] using (hge n x).le
  have hfm : Measurable f := measurable_of_tendsto_metrizable hgm hlim
  have hi : Integrable f μ := (integrable_const M).mono' hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hf x))
  refine ⟨hi,le_of_forall_pos_le_add (fun ε hε => ?_)⟩
  obtain ⟨g,hgm,hgi,hgp,hge⟩ := ha ε hε
  have hp : ∀ x, g x ≤ f x + ε := by
    intro x
    have hh := (abs_lt.mp (hge x)).1
    linarith
  have hb := integral_mono hgi (hi.add (integrable_const ε)) hp
  have he : (∫ x, f x + ε ∂μ) = (∫ x, f x ∂μ) + ε := by
    rw [integral_add hi (integrable_const ε)]
    simp
  change (∫ x, g x ∂μ) ≤ (∫ x, f x + ε ∂μ) at hb
  rw [he] at hb
  exact hgp.trans hb

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE UniformPositiveLimit

-- BEGIN COMPLETE MODULE GeneralDeviation
section

open MeasureTheory Topology Set
namespace HartSchmeidler.Compact.Proof
variable {ι : Type*} [DecidableEq ι] {S : ι → Type*}
  [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)]
  [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]

lemma general_deviation (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i))
    (μ : Measure (Profile S)) [IsProbabilityMeasure μ]
    (hspecial : ∀ (i : ι) (t : S i) (R : Set (S i)), MeasurableSet R →
      0 ≤ ∫ s, R.indicator (fun _ => (1:ℝ)) (s i) * fixedGain h hcont i t s ∂μ)
    (i : ι) (ζ : S i → S i) (hζ : Measurable ζ) :
    Integrable (fun s => h i s - h i (Function.update s i (ζ (s i)))) μ ∧
      0 ≤ ∫ s, h i s - h i (Function.update s i (ζ (s i))) ∂μ := by
  classical
  let H : C(Profile S,ℝ) := ⟨h i,hcont i⟩
  apply uniform_positive_limit μ _ (M := 2 * ‖H‖)
  · intro s
    calc
      |h i s - h i (Function.update s i (ζ (s i)))| ≤
          |h i s| + |h i (Function.update s i (ζ (s i)))| := abs_sub _ _
      _ ≤ ‖H‖ + ‖H‖ := add_le_add (H.norm_coe_le_norm s) (H.norm_coe_le_norm _)
      _ = _ := by ring
  · intro ε hε
    obtain ⟨m,a,U,hU,hcover,hclose⟩ := uniform_payoff_cover h hcont i hε
    obtain ⟨R,hR,hRU,hpart⟩ := finite_measurable_partition U
      (fun j => (hU j).measurableSet) hcover
    let A := fun j => ζ ⁻¹' R j
    have hA : ∀ j, MeasurableSet (A j) := fun j => hζ (hR j)
    let q := fun (j : Fin m) (s : Profile S) =>
      (A j).indicator (fun _ => (1:ℝ)) (s i) * fixedGain h hcont i (a j) s
    have hqm : ∀ j, Measurable (q j) := fun j =>
      (((measurable_const.indicator (hA j)).comp
        (profile_eval_continuous i).measurable).mul (fixedGain h hcont i (a j)).continuous.measurable)
    have hqi : ∀ j, Integrable (q j) μ := by
      intro j
      have hi := (continuous_integrable μ (fixedGain h hcont i (a j))).indicator
        ((profile_eval_continuous i).measurable (hA j))
      have he : q j = ((fun s : Profile S => s i) ⁻¹' A j).indicator
          (fun s => fixedGain h hcont i (a j) s) := by
        funext s
        by_cases hs : s i ∈ A j <;> simp [q,hs]
      rw [he]
      exact hi
    have hqp : ∀ j, 0 ≤ ∫ s, q j s ∂μ := fun j => hspecial i (a j) (A j) (hA j)
    refine ⟨fun s => ∑ j, q j s, by fun_prop,
      integrable_finsetSum _ (fun j _ => hqi j),?_,?_⟩
    · rw [integral_finsetSum _ (fun j _ => hqi j)]
      exact Finset.sum_nonneg (fun j _ => hqp j)
    · intro s
      obtain ⟨j,hj,hunique⟩ := hpart (ζ (s i))
      have he : (∑ k, q k s) = fixedGain h hcont i (a j) s := by
        rw [Finset.sum_eq_single j]
        · simp [q,A,hj]
        · intro k _ hkj
          have hk : ζ (s i) ∉ R k := fun hk => hkj (hunique k hk)
          simp [q,A,hk]
        · simp
      change |(h i s - h i (Function.update s i (ζ (s i)))) - ∑ k, q k s| < ε
      rw [he]
      have hc := hclose j (ζ (s i)) (hRU j hj) s
      change |(h i s - h i (Function.update s i (ζ (s i)))) -
        (h i s - h i (Function.update s i (a j)))| < ε
      have heq : (h i s - h i (Function.update s i (ζ (s i)))) -
        (h i s - h i (Function.update s i (a j))) =
        -(h i (Function.update s i (ζ (s i))) - h i (Function.update s i (a j))) := by ring
      rw [heq,abs_neg]
      exact hc

end HartSchmeidler.Compact.Proof
end
-- END COMPLETE MODULE GeneralDeviation

-- BEGIN COMPLETE MODULE CompactCERoot
section

namespace HartSchmeidler.Compact
open MeasureTheory
open Proof

theorem theorem_3 {ι : Type*} [Nonempty ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, Nonempty (S i)] [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i)) :
    ∃ μ : Measure (Profile S), IsCorrelatedEq h μ := by
  obtain ⟨μ,hμ,hr,hw⟩ := exists_weighted_equilibrium h hcont
  let : IsProbabilityMeasure μ := hμ
  let : μ.Regular := hr
  have hs : ∀ (i : ι) (t : S i) (R : Set (S i)), MeasurableSet R →
      0 ≤ ∫ s, R.indicator (fun _ => (1:ℝ)) (s i) * fixedGain h hcont i t s ∂μ := by
    intro i t R hR
    exact (borel_weight_nonneg μ ⟨fun s => s i,profile_eval_continuous i⟩
      (fixedGain h hcont i t) (hw i t) hR).2
  exact ⟨μ,hμ,fun i ζ hζ => general_deviation h hcont μ hs i ζ hζ⟩

end HartSchmeidler.Compact

open MeasureTheory in
theorem solution {ι : Type*} [Nonempty ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, Nonempty (S i)] [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (h : ι → HartSchmeidler.Compact.Profile S → ℝ) (hcont : ∀ i, Continuous (h i)) :
    ∃ μ : Measure (HartSchmeidler.Compact.Profile S), HartSchmeidler.Compact.IsCorrelatedEq h μ :=
  HartSchmeidler.Compact.theorem_3 h hcont
end
-- END COMPLETE MODULE CompactCERoot
