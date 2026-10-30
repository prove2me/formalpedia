-- Prove2me | solution 1 for NonconvexCost.Complexity.thm_6_6_line_search_calls
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T13:20:30.489369+00:00
-- url     : https://prove2.me/submissions/a6cbaa18-97da-4278-96b4-7b405b88a1af

import Mathlib
import Definitions.Def_NonconvexCost_Complexity_Setting
import Definitions.Def_NonconvexCost_Complexity_Algorithm
open Set
open scoped RealInnerProductSpace
namespace Queelius.NonsmoothLine
open NonconvexCost.Complexity
lemma point_distance {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (δ : ℝ) (x g : X) (hg : g ≠ 0) (t : ℝ) :
    ‖lsPoint δ x g t-x‖ = |t-δ| := by
  have hn : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  simp [lsPoint,norm_smul,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg g)),hn]
lemma oracle_mem {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (G : X → X → X) (δ : ℝ) (x g : X) (hg : g ≠ 0) (t : ℝ) (ht : t ∈ Icc 0 δ) :
    G (lsPoint δ x g t) (‖g‖⁻¹ • g) ∈ goldstein G δ x := by
  apply subset_convexHull ℝ
  refine ⟨lsPoint δ x g t,‖g‖⁻¹ • g,?_,rfl⟩
  rw [point_distance δ x g hg t,abs_of_nonpos (sub_nonpos.mpr ht.2)]
  linarith [ht.1]
lemma oracle_angle {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (G : X → X → X) (δ ε : ℝ) (hε : 0 < ε) (x g : X) (hg : ε < ‖g‖)
    (t : ℝ) (ht : lsDeriv G δ ε x g t < 0) :
    ⟪G (lsPoint δ x g t) (‖g‖⁻¹ • g),g⟫ < ‖g‖^2/2 := by
  have hn : 0 < ‖g‖ := lt_trans hε hg
  unfold lsDeriv at ht
  rw [inner_smul_right] at ht
  have ha : ⟪G (lsPoint δ x g t) (‖g‖⁻¹ • g),g⟫ / ‖g‖ < ε/2 := by
    simpa only [div_eq_mul_inv,mul_comm] using sub_neg.mp ht
  have hb := (div_lt_iff₀ hn).mp ha
  nlinarith [mul_pos (sub_pos.mpr hg) hn]
end Queelius.NonsmoothLine
namespace NonconvexCost.Complexity
 theorem _root_.prior_outcome {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (x g : X)
    (hg : ε < ‖g‖) (hdec : f x - f (lsPoint δ x g 0) < δ * ε / 3) :
    (lsFun f δ ε x g δ - lsFun f δ ε x g 0) / (δ - 0) < -(ε / 6) ∧
      ∀ t ∈ Icc (0 : ℝ) δ, lsDeriv G δ ε x g t < 0 →
        G (lsPoint δ x g t) (‖g‖⁻¹ • g) ∈ goldstein G δ x ∧
          ⟪G (lsPoint δ x g t) (‖g‖⁻¹ • g), g⟫ < ‖g‖ ^ 2 / 2 := by
  constructor
  · rw [sub_zero,div_lt_iff₀ hδ]
    unfold lsFun
    simp only [lsPoint,sub_self,zero_smul,add_zero,mul_zero,zero_div,sub_zero] at *
    linarith
  · intro t ht hd
    have hn : g ≠ 0 := norm_pos_iff.mp (lt_trans hε hg)
    exact ⟨Queelius.NonsmoothLine.oracle_mem G δ x g hn t ht,
      Queelius.NonsmoothLine.oracle_angle G δ ε hε x g hg t hd⟩
end NonconvexCost.Complexity

namespace Queelius.NonsmoothReduction
open NonconvexCost.Complexity Set Classical
open scoped RealInnerProductSpace
noncomputable def reductions {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (x0 g0 : X) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range n).filter (fun j => IsReinit (run f G δ ε x0 g0 j))).card
def Pending {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (C : Set X) (δ ε : ℝ) (s : State X) : Prop :=
  ∀ r : X,s.ph=.reinit r → r ∈ C ∧ f r ≤ f s.x-δ*ε/3
lemma reductions_succ {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (x0 g0 : X) (n : ℕ) :
    reductions f G δ ε x0 g0 (n+1)=reductions f G δ ε x0 g0 n+
      (if IsReinit (run f G δ ε x0 g0 n) then 1 else 0) := by
  classical
  unfold reductions
  rw [Finset.range_add_one,Finset.filter_insert]
  by_cases h : IsReinit (run f G δ ε x0 g0 n) <;> simp [h]
lemma step_control {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (C : Set X) (f0 : ℝ)
    (hsub : ∀ x ∈ C,f x ≤ f0 → ∀ y : X,‖y‖ ≤ δ → x+y ∈ C)
    (s : State X) (hx : s.x ∈ C) (hfx : f s.x ≤ f0) (hp : Pending f C δ ε s) :
    (step f G δ ε s).x ∈ C ∧
      f (step f G δ ε s).x ≤ f s.x-(if IsReinit s then δ*ε/3 else 0) ∧
      Pending f C δ ε (step f G δ ε s) := by
  classical
  cases hph : s.ph with
  | trial =>
    have hn : ¬ IsReinit s := by simp [IsReinit,hph]
    simp only [step,hph,if_neg hn,sub_zero]
    split_ifs with hsmall hdec hneg
    · exact ⟨hx,le_rfl,hp⟩
    · refine ⟨hx,le_rfl,?_⟩
      intro r hr
      have hr' := Phase.reinit.inj hr
      rw [← hr']
      have hg : s.g ≠ 0 := norm_pos_iff.mp (hε.trans (lt_of_not_ge hsmall))
      have hd := Queelius.NonsmoothLine.point_distance δ s.x s.g hg 0
      have hdn : ‖lsPoint δ s.x s.g 0-s.x‖ ≤ δ := by simpa [abs_of_pos hδ] using hd.le
      have hm := hsub s.x hx hfx (lsPoint δ s.x s.g 0-s.x) hdn
      exact ⟨by simpa using hm,by dsimp;linarith⟩
    · exact ⟨hx,le_rfl,by simp [Pending]⟩
    · exact ⟨hx,le_rfl,by simp [Pending]⟩
  | reinit r =>
    have hi : IsReinit s := ⟨r,hph⟩
    obtain ⟨hr,hfr⟩ := hp r hph
    simp only [step,hph,if_pos hi]
    exact ⟨hr,hfr,by simp [Pending]⟩
  | bis l r =>
    have hn : ¬ IsReinit s := by simp [IsReinit,hph]
    simp only [step,hph,if_neg hn,sub_zero]
    split_ifs <;> exact ⟨hx,le_rfl,by simp [Pending]⟩
lemma run_control {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (C : Set X) (x0 g0 : X) (hx0 : x0 ∈ C)
    (hsub : ∀ x ∈ C,f x ≤ f x0 → ∀ y : X,‖y‖ ≤ δ → x+y ∈ C) (n : ℕ) :
    (run f G δ ε x0 g0 n).x ∈ C ∧
      f (run f G δ ε x0 g0 n).x+(δ*ε/3)*(reductions f G δ ε x0 g0 n : ℝ) ≤ f x0 ∧
      Pending f C δ ε (run f G δ ε x0 g0 n) := by
  classical
  induction n with
  | zero => simpa [run,reductions,Pending] using hx0
  | succ n ih =>
    have hpos : 0 ≤ δ*ε/3 := by positivity
    have hnon := mul_nonneg hpos (Nat.cast_nonneg (reductions f G δ ε x0 g0 n))
    have hfx : f (run f G δ ε x0 g0 n).x ≤ f x0 := by linarith [ih.2.1]
    obtain ⟨hx,hd,hp⟩ := step_control f G δ ε hδ hε C (f x0) hsub
      (run f G δ ε x0 g0 n) ih.1 hfx ih.2.2
    refine ⟨hx,?_,hp⟩
    rw [reductions_succ,Nat.cast_add]
    by_cases hi : IsReinit (run f G δ ε x0 g0 n)
    · simp only [if_pos hi,Nat.cast_one] at *
      change f (step f G δ ε (run f G δ ε x0 g0 n)).x+_ ≤ _
      linarith [ih.2.1]
    · simp only [if_neg hi,Nat.cast_zero,add_zero,sub_zero] at *
      change f (step f G δ ε (run f G δ ε x0 g0 n)).x+_ ≤ _
      linarith [ih.2.1]
lemma reduction_bound {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (C : Set X) (hbdd : BddBelow (f '' C)) (x0 g0 : X) (hx0 : x0 ∈ C)
    (hsub : ∀ x ∈ C,f x ≤ f x0 → ∀ y : X,‖y‖ ≤ δ → x+y ∈ C) (n : ℕ) :
    (reductions f G δ ε x0 g0 n : ℝ) ≤ 3*(f x0-sInf (f '' C))/(δ*ε) := by
  have hi := run_control f G δ ε hδ hε C x0 g0 hx0 hsub n
  have hl : sInf (f '' C) ≤ f (run f G δ ε x0 g0 n).x :=
    csInf_le hbdd ⟨_,hi.1,rfl⟩
  apply (le_div_iff₀ (mul_pos hδ hε)).mpr
  nlinarith [hi.2.1]
end Queelius.NonsmoothReduction
namespace NonconvexCost.Complexity
open Classical in
 theorem _root_.prior_reduction_count {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (C : Set X) (f : X → ℝ) (hbdd : BddBelow (f '' C))
    (G : X → X → X) (x0 : X) (hx0 : x0 ∈ C)
    (hsub : ∀ x ∈ C,f x ≤ f x0 → ∀ y : X,‖y‖ ≤ δ → x+y ∈ C) (g0 : X) (n : ℕ) :
    ((Finset.range n).filter (fun j => IsReinit (run f G δ ε x0 g0 j))).card ≤
      ⌈3*(f x0-sInf (f '' C))/(δ*ε)⌉₊ := by
  have he := Queelius.NonsmoothReduction.reduction_bound f G δ ε hδ hε C hbdd x0 g0 hx0 hsub n
  change Queelius.NonsmoothReduction.reductions f G δ ε x0 g0 n ≤ _
  have hb : (Queelius.NonsmoothReduction.reductions f G δ ε x0 g0 n : ℝ) ≤
      (⌈3*(f x0-sInf (f '' C))/(δ*ε)⌉₊ : ℝ) := he.trans (Nat.le_ceil _)
  exact_mod_cast hb
end NonconvexCost.Complexity

namespace Queelius.NonsmoothRun
open NonconvexCost.Complexity Classical
open scoped RealInnerProductSpace
lemma short_minimizes {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (g h : X) : IsShortestIn g h (short g h) := by
  let d := h-g
  let D := ‖d‖^2
  let A := ⟪g,d⟫
  let a := -A/D
  let t := max 0 (min 1 a)
  have ht0 : 0 ≤ t := le_max_left _ _
  have ht1 : t ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have he : short g h=g+t • d := by
    unfold short
    have hi : ⟪g,g-h⟫ = -A := by dsimp [A,d];rw [inner_sub_right,inner_sub_right];ring
    have hn : ‖g-h‖^2=D := by dsimp [D,d];rw [norm_sub_rev]
    rw [hi,hn]
  rw [he]
  constructor
  · have : (1-t) • g+t • h=g+t • d := by dsimp [d];module
    rw [← this]
    exact ⟨1-t,t,by linarith,ht0,by ring,rfl⟩
  · intro v hv
    obtain ⟨u,b,hu,hb,hub,rfl⟩ := hv
    have hb1 : b ≤ 1 := by linarith
    have hv : u • g+b • h=g+b • d := by dsimp [d];rw [show u=1-b by linarith];module
    rw [hv]
    have hD : 0 ≤ D := sq_nonneg _
    have hcrit : 0 ≤ (b-t)*(A+t*D) := by
      by_cases hd : D=0
      · have hz : d=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hd)
        simp [A,hz,hd]
      · have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm hd)
        have ha : a*D = -A := by dsimp [a];field_simp
        by_cases ha0 : a ≤ 0
        · have ht : t=0 := max_eq_left (le_trans (min_le_right _ _) ha0)
          rw [ht]
          simpa only [sub_zero,zero_mul,add_zero] using mul_nonneg hb (show 0 ≤ A by nlinarith [mul_nonpos_of_nonpos_of_nonneg ha0 hD])
        · by_cases ha1 : 1 ≤ a
          · have ht : t=1 := by dsimp [t];rw [min_eq_left ha1];norm_num
            rw [ht]
            apply mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hb1)
            nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hD]
          · have ht : t=a := by dsimp [t];rw [min_eq_right (le_of_not_ge ha1),max_eq_right (le_of_not_ge ha0)]
            rw [ht];nlinarith
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have hex (r : ℝ) : ‖g+r • d‖^2=‖g‖^2+2*r*A+r^2*D := by
      rw [norm_add_sq_real,inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
      dsimp [A,D];ring
    rw [hex t,hex b]
    nlinarith [mul_nonneg hD (sq_nonneg (b-t))]
lemma goldstein_norm {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (G : X → X → X) (L δ : ℝ) (hL : IsLBounded G L) (x g : X)
    (hg : g ∈ goldstein G δ x) : ‖g‖ ≤ L := by
  have hc : Convex ℝ {v : X | ‖v‖ ≤ L} := by simpa only [Metric.closedBall,dist_zero_right] using (convex_closedBall (0 : X) L)
  apply (convexHull_min ?_ hc) hg
  rintro v ⟨y,e,_,rfl⟩
  exact hL.2 y e
end Queelius.NonsmoothRun

namespace Queelius.NonsmoothRun
open NonconvexCost.Complexity Classical
def Valid {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (G : X → X → X) (δ ε : ℝ) (s : State X) : Prop :=
  s.g ∈ goldstein G δ s.x ∧ ∀ l r,s.ph=.bis l r → 0 ≤ l ∧ l ≤ r ∧ r ≤ δ ∧ ε < ‖s.g‖
lemma short_mem {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (G : X → X → X) (δ : ℝ) (x g h : X)
    (hg : g ∈ goldstein G δ x) (hh : h ∈ goldstein G δ x) :
    short g h ∈ goldstein G δ x := by
  exact (convex_convexHull ℝ _).segment_subset hg hh (short_minimizes g h).1
lemma step_valid {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (s : State X) (hs : Valid G δ ε s) : Valid G δ ε (step f G δ ε s) := by
  classical
  cases hp : s.ph with
  | trial =>
    simp only [step,hp]
    split_ifs with hsmall hdec hneg
    · exact hs
    · exact ⟨hs.1,by simp⟩
    · have hg : s.g ≠ 0 := norm_pos_iff.mp (hε.trans (lt_of_not_ge hsmall))
      exact ⟨short_mem G δ s.x s.g _ hs.1 (Queelius.NonsmoothLine.oracle_mem G δ s.x s.g hg 0 ⟨le_rfl,hδ.le⟩),by simp⟩
    · exact ⟨hs.1,by intro l r hr;cases hr;exact ⟨le_rfl,hδ.le,le_rfl,lt_of_not_ge hsmall⟩⟩
  | reinit x =>
    refine ⟨?_,by simp [step,hp]⟩
    simp only [step,hp]
    change G x 0 ∈ goldstein G δ x
    apply subset_convexHull ℝ
    exact ⟨x,0,by simp [hδ.le],rfl⟩
  | bis l r =>
    obtain ⟨hl,hlr,hr,hg⟩ := hs.2 l r hp
    have hm : (l+r)/2 ∈ Icc 0 δ := ⟨by linarith,by linarith⟩
    have hgne : s.g ≠ 0 := norm_pos_iff.mp (hε.trans hg)
    simp only [step,hp]
    split_ifs with hneg hmid
    · exact ⟨short_mem G δ s.x s.g _ hs.1 (Queelius.NonsmoothLine.oracle_mem G δ s.x s.g hgne _ hm),by simp⟩
    · exact ⟨hs.1,by intro a b hab;cases hab;exact ⟨hl,by linarith,by linarith,hg⟩⟩
    · exact ⟨hs.1,by intro a b hab;cases hab;exact ⟨by linarith,by linarith,hr,hg⟩⟩
lemma run_valid {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (x0 g0 : X) (hg0 : g0 ∈ goldstein G δ x0) (n : ℕ) :
    Valid G δ ε (run f G δ ε x0 g0 n) := by
  induction n with
  | zero => exact ⟨hg0,by simp [run]⟩
  | succ n ih => exact step_valid f G δ ε hδ hε _ ih
lemma run_norm {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε L : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hL : IsLBounded G L) (x0 g0 : X) (hg0 : g0 ∈ goldstein G δ x0) (n : ℕ) :
    ‖(run f G δ ε x0 g0 n).g‖ ≤ L :=
  goldstein_norm G L δ hL _ _ (run_valid f G δ ε hδ hε x0 g0 hg0 n).1
end Queelius.NonsmoothRun

section
open scoped RealInnerProductSpace

open NonconvexCost.Complexity in
theorem community_contraction {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (L : ℝ) (hL : 0 < L) (g g' g'' : X) (hg : ‖g‖ ≤ L) (hg' : ‖g'‖ ≤ L)
    (hinner : ⟪g', g⟫ ≤ ‖g‖ ^ 2 / 2) (hshort : IsShortestIn g g' g'') :
    ‖g''‖ ^ 2 ≤ ‖g‖ ^ 2 * (1 - ‖g‖ ^ 2 / (16 * L ^ 2)) := by
  set t : ℝ := ‖g‖ ^ 2 / (8 * L ^ 2) with ht
  have hL2 : 0 < L ^ 2 := by positivity
  have hn0 : 0 ≤ ‖g‖ := norm_nonneg _
  have hn2 : ‖g‖ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hn0 hg 2
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by positivity)]
    linarith
  have hmem : (1 - t) • g + t • g' ∈ segment ℝ g g' :=
    ⟨1 - t, t, by linarith, ht0, by ring, rfl⟩
  have hle := hshort.2 _ hmem
  have hv : (1 - t) • g + t • g' = g + t • (g' - g) := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [hv] at hle
  have hsq : ‖g''‖ ^ 2 ≤ ‖g + t • (g' - g)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hexp : ‖g + t • (g' - g)‖ ^ 2 =
      ‖g‖ ^ 2 + 2 * t * (⟪g', g⟫ - ‖g‖ ^ 2) + t ^ 2 * ‖g' - g‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm g g', Real.norm_eq_abs, abs_of_nonneg ht0]
    ring
  have hd : ‖g' - g‖ ≤ 2 * L := by
    have := norm_sub_le g' g
    linarith
  have hd2 : ‖g' - g‖ ^ 2 ≤ 4 * L ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hd 2
    nlinarith
  have h1 : 2 * t * (⟪g', g⟫ - ‖g‖ ^ 2) ≤ -(t * ‖g‖ ^ 2) := by nlinarith
  have h2 : t ^ 2 * ‖g' - g‖ ^ 2 ≤ t ^ 2 * (4 * L ^ 2) :=
    mul_le_mul_of_nonneg_left hd2 (by positivity)
  have h3 : ‖g‖ ^ 2 - t * ‖g‖ ^ 2 + t ^ 2 * (4 * L ^ 2) =
      ‖g‖ ^ 2 * (1 - ‖g‖ ^ 2 / (16 * L ^ 2)) := by
    rw [ht]
    field_simp
    ring
  linarith

end

namespace Queelius.NonsmoothRun
open NonconvexCost.Complexity Classical
lemma rho_step (r z : ℝ) (k : ℕ) (hr : 0 ≤ r) (hz : z ≤ r*(1-r))
    (hb : r*(16+(k:ℝ)) ≤ 1) : z*(16+((k+1:ℕ):ℝ)) ≤ 1 := by
  let m : ℝ := 16+k
  have hm : 16 ≤ m := by dsimp [m];have := Nat.cast_nonneg (α:=ℝ) k;linarith
  have hA : r*(1-r)*m^2 ≤ m-1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1-r*m by dsimp [m];linarith)
      (show 0 ≤ m-1-r*m by dsimp [m] at *;nlinarith)]
  have hB : r*(1-r)*(m+1)*m^2 ≤ m^2 := by nlinarith
  have hC : r*(1-r)*(m+1) ≤ 1 := le_of_mul_le_mul_right (by simpa only [one_mul] using hB) (show 0 < m^2 by nlinarith)
  have hD := mul_le_mul_of_nonneg_right hz (show 0 ≤ m+1 by linarith)
  push_cast
  dsimp [m] at *
  linarith
lemma budget_increment (a L ε : ℝ) (k : ℕ) (hε : 0 < ε) (ha : ε < a)
    (hb : (a^2/(16*L^2))*(16+(k:ℝ)) ≤ 1) (hL : 0 < L) :
    ((k+1:ℕ):ℝ) ≤ 16*L^2/ε^2 := by
  have hD : 0 < 16*L^2 := by positivity
  have hE : 0 < ε^2 := by positivity
  have hA : a^2*(16+(k:ℝ)) ≤ 16*L^2 := by
    apply (div_le_one hD).mp
    simpa only [div_mul_eq_mul_div] using hb
  have haa : ε^2 < a^2 := by nlinarith
  apply (le_div_iff₀ hE).mpr
  push_cast
  nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (sub_nonneg.mpr haa.le)]
lemma short_rho {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (L ε : ℝ) (hL : 0 < L) (hε : 0 < ε) (g h : X)
    (hg : ‖g‖ ≤ L) (hh : ‖h‖ ≤ L) (ha : ⟪h,g⟫ < ‖g‖^2/2) (k : ℕ)
    (hb : (‖g‖^2/(16*L^2))*(16+(k:ℝ)) ≤ 1) :
    (‖short g h‖^2/(16*L^2))*(16+((k+1:ℕ):ℝ)) ≤ 1 := by
  have hd : 0 < 16*L^2 := by positivity
  have hc := community_contraction L hL g h (short g h) hg hh ha.le (short_minimizes g h)
  apply rho_step _ _ k (by positivity) ?_ hb
  apply (div_le_iff₀ hd).mpr
  have he : (‖g‖^2/(16*L^2)*(1-‖g‖^2/(16*L^2)))*(16*L^2)=‖g‖^2*(1-‖g‖^2/(16*L^2)) := by field_simp
  rw [he]
  exact hc
noncomputable def localCount {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (x0 g0 : X) : ℕ → ℕ
  | 0 => 0
  | n+1 => if IsReinit (run f G δ ε x0 g0 n) then 0 else
      if StartsLineSearch f δ ε (run f G δ ε x0 g0 n) then localCount f G δ ε x0 g0 n+1
      else localCount f G δ ε x0 g0 n
noncomputable def searchCount {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (x0 g0 : X) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range n).filter (fun j => StartsLineSearch f δ ε (run f G δ ε x0 g0 j))).card
lemma searchCount_succ {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (x0 g0 : X) (n : ℕ) :
    searchCount f G δ ε x0 g0 (n+1)=searchCount f G δ ε x0 g0 n+
      (if StartsLineSearch f δ ε (run f G δ ε x0 g0 n) then 1 else 0) := by
  classical
  unfold searchCount
  rw [Finset.range_add_one,Finset.filter_insert]
  by_cases h : StartsLineSearch f δ ε (run f G δ ε x0 g0 n) <;> simp [h]
end Queelius.NonsmoothRun

namespace Queelius.NonsmoothRun
open NonconvexCost.Complexity Classical
noncomputable def nextCount {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (δ ε : ℝ) (s : State X) (k : ℕ) : ℕ :=
  if IsReinit s then 0 else if StartsLineSearch f δ ε s then k+1 else k
def Budget {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (L ε : ℝ) (s : State X) (k : ℕ) : Prop :=
  (k:ℝ) ≤ 16*L^2/ε^2 ∧
  (match s.ph with
   | .bis _ _ => 0 < k ∧ (‖s.g‖^2/(16*L^2))*(15+(k:ℝ)) ≤ 1
   | _ => (‖s.g‖^2/(16*L^2))*(16+(k:ℝ)) ≤ 1)
lemma budget_step {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε L : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hL : IsLBounded G L) (s : State X) (hs : Valid G δ ε s)
    (k : ℕ) (hk : Budget L ε s k) :
    Budget L ε (step f G δ ε s) (nextCount f δ ε s k) := by
  have hn := goldstein_norm G L δ hL s.x s.g hs.1
  have hD : 0 < 16*L^2 := by positivity [hL.1]
  cases hp : s.ph with
  | trial =>
    have hnot : ¬ IsReinit s := by simp [IsReinit,hp]
    have hkb : (‖s.g‖^2/(16*L^2))*(16+(k:ℝ)) ≤ 1 := by simpa only [Budget,hp] using hk.2
    simp only [step,hp]
    split_ifs with hsmall hdec hneg
    · have hno : ¬ StartsLineSearch f δ ε s := by simp [StartsLineSearch,hp,not_lt.mpr hsmall]
      simpa only [nextCount,if_neg hnot,if_neg hno] using hk
    · have hno : ¬ StartsLineSearch f δ ε s := by simp [StartsLineSearch,hp,not_lt.mpr hdec]
      simpa only [nextCount,if_neg hnot,if_neg hno,Budget,hp] using hk
    · have hyes : StartsLineSearch f δ ε s := ⟨hp,lt_of_not_ge hsmall,lt_of_not_ge hdec⟩
      simp only [nextCount,if_neg hnot,if_pos hyes,Budget]
      exact ⟨budget_increment _ L ε k hε (lt_of_not_ge hsmall) hkb hL.1,
        short_rho L ε hL.1 hε s.g _ hn (hL.2 _ _)
          (Queelius.NonsmoothLine.oracle_angle G δ ε hε s.x s.g (lt_of_not_ge hsmall) 0 hneg) k hkb⟩
    · have hyes : StartsLineSearch f δ ε s := ⟨hp,lt_of_not_ge hsmall,lt_of_not_ge hdec⟩
      simp only [nextCount,if_neg hnot,if_pos hyes,Budget]
      refine ⟨budget_increment _ L ε k hε (lt_of_not_ge hsmall) hkb hL.1,by omega,?_⟩
      push_cast
      nlinarith
  | reinit x =>
    have hi : IsReinit s := ⟨x,hp⟩
    simp only [nextCount,if_pos hi,step,hp,Budget,Nat.cast_zero,add_zero]
    refine ⟨by positivity,?_⟩
    have hh := pow_le_pow_left₀ (norm_nonneg (G x 0)) (hL.2 x 0) 2
    rw [div_mul_eq_mul_div]
    apply (div_le_one hD).mpr
    nlinarith
  | bis l r =>
    have hnot : ¬ IsReinit s := by simp [IsReinit,hp]
    have hno : ¬ StartsLineSearch f δ ε s := by simp [StartsLineSearch,hp]
    obtain ⟨hkp,hkb⟩ := (show 0 < k ∧ (‖s.g‖^2/(16*L^2))*(15+(k:ℝ)) ≤ 1 by simpa only [Budget,hp] using hk.2)
    have hprev : (‖s.g‖^2/(16*L^2))*(16+((k-1:ℕ):ℝ)) ≤ 1 := by
      have he : ((k-1:ℕ):ℝ)+1=k := by exact_mod_cast (Nat.sub_add_cancel hkp)
      nlinarith
    have hg := (hs.2 l r hp).2.2.2
    simp only [nextCount,if_neg hnot,if_neg hno,step,hp]
    split_ifs with hneg hmid
    · refine ⟨hk.1,?_⟩
      have hh := short_rho L ε hL.1 hε s.g _ hn (hL.2 _ _)
        (Queelius.NonsmoothLine.oracle_angle G δ ε hε s.x s.g hg _ hneg) (k-1) hprev
      simpa only [Budget,show k-1+1=k by omega] using hh
    · exact ⟨hk.1,hkp,hkb⟩
    · exact ⟨hk.1,hkp,hkb⟩
end Queelius.NonsmoothRun

namespace Queelius.NonsmoothRun
open NonconvexCost.Complexity Classical Queelius.NonsmoothReduction
lemma run_budget {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε L : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hL : IsLBounded G L) (x0 g0 : X) (hg0 : g0 ∈ goldstein G δ x0) (n : ℕ) :
    Budget L ε (run f G δ ε x0 g0 n) (localCount f G δ ε x0 g0 n) := by
  induction n with
  | zero =>
    simp only [run,localCount,Budget,Nat.cast_zero,add_zero]
    refine ⟨by positivity,?_⟩
    have hn := goldstein_norm G L δ hL x0 g0 hg0
    have hh := pow_le_pow_left₀ (norm_nonneg g0) hn 2
    rw [div_mul_eq_mul_div]
    apply (div_le_one (by positivity [hL.1] : 0 < 16*L^2)).mpr
    nlinarith
  | succ n ih =>
    exact budget_step f G δ ε L hδ hε hL _ (run_valid f G δ ε hδ hε x0 g0 hg0 n) _ ih
lemma count_accounting {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε L : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hL : IsLBounded G L) (x0 g0 : X) (hg0 : g0 ∈ goldstein G δ x0) (n : ℕ) :
    (searchCount f G δ ε x0 g0 n : ℝ) ≤
      (reductions f G δ ε x0 g0 n : ℝ)*(16*L^2/ε^2)+(localCount f G δ ε x0 g0 n : ℝ) := by
  induction n with
  | zero => simp [searchCount,reductions,localCount]
  | succ n ih =>
    have hk := (run_budget f G δ ε L hδ hε hL x0 g0 hg0 n).1
    rw [searchCount_succ,reductions_succ,localCount]
    by_cases hi : IsReinit (run f G δ ε x0 g0 n)
    · have hno : ¬ StartsLineSearch f δ ε (run f G δ ε x0 g0 n) := by
        obtain ⟨x,hx⟩ := hi
        simp [StartsLineSearch,hx]
      simp only [if_pos hi,if_neg hno,Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero]
      nlinarith
    · by_cases hyes : StartsLineSearch f δ ε (run f G δ ε x0 g0 n)
      · simp only [if_neg hi,if_pos hyes,Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero]
        linarith
      · simp only [if_neg hi,if_neg hyes,Nat.cast_add,Nat.cast_zero,add_zero]
        exact ih
lemma count_bound {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε L : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hL : IsLBounded G L) (x0 g0 : X) (hg0 : g0 ∈ goldstein G δ x0) (n : ℕ) :
    (searchCount f G δ ε x0 g0 n : ℝ) ≤
      ((reductions f G δ ε x0 g0 n : ℝ)+1)*(16*L^2/ε^2) := by
  have hs := count_accounting f G δ ε L hδ hε hL x0 g0 hg0 n
  have hk := (run_budget f G δ ε L hδ hε hL x0 g0 hg0 n).1
  nlinarith
end Queelius.NonsmoothRun
namespace NonconvexCost.Complexity
open Classical in
theorem _root_.prior_global_count {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (δ ε L : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (C : Set X) (f : X → ℝ) (hbdd : BddBelow (f '' C))
    (G : X → X → X) (hL : IsLBounded G L) (x0 : X) (hx0 : x0 ∈ C)
    (hsub : ∀ x ∈ C, f x ≤ f x0 → ∀ y : X, ‖y‖ ≤ δ → x + y ∈ C)
    (g0 : X) (hg0 : g0 ∈ goldstein G δ x0) (n : ℕ) :
    (((Finset.range n).filter (fun j => StartsLineSearch f δ ε (run f G δ ε x0 g0 j))).card : ℝ) ≤
      ((⌊3 * (f x0 - sInf (f '' C)) / (δ * ε)⌋₊ : ℝ) + 1) * (16 * L ^ 2 / ε ^ 2) := by
  have hs := Queelius.NonsmoothRun.count_bound f G δ ε L hδ hε hL x0 g0 hg0 n
  have hr := Queelius.NonsmoothReduction.reduction_bound f G δ ε hδ hε C hbdd x0 g0 hx0 hsub n
  have hnat : Queelius.NonsmoothReduction.reductions f G δ ε x0 g0 n ≤
      ⌊3*(f x0-sInf (f '' C))/(δ*ε)⌋₊ := Nat.le_floor hr
  have hreal : (Queelius.NonsmoothReduction.reductions f G δ ε x0 g0 n : ℝ) ≤
      (⌊3*(f x0-sInf (f '' C))/(δ*ε)⌋₊ : ℝ) := by exact_mod_cast hnat
  exact hs.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
end NonconvexCost.Complexity

section
open Set

theorem _root_.community_slope_drop (h s : ℝ → ℝ) (p q : ℝ) (hs : ConvexOn ℝ (Icc p q) s)
    (hhs : ConvexOn ℝ (Icc p q) (h + s)) (x y : ℝ) (hpx : p ≤ x) (hxy : x < y) (hyq : y ≤ q)
    (c a b : ℝ) (hc : HasDerivWithinAt h c (Icc x q) x) (hc0 : 0 ≤ c)
    (ha : HasDerivWithinAt s a (Icc x q) x) (hb : HasDerivWithinAt s b (Icc p y) y) :
    a - b ≤ (h y - h x) / (y - x) := by
  have hsR : ConvexOn ℝ (Icc x q) s := hs.subset (Icc_subset_Icc hpx le_rfl) (convex_Icc x q)
  have hsL : ConvexOn ℝ (Icc p y) s := hs.subset (Icc_subset_Icc le_rfl hyq) (convex_Icc p y)
  have hhsR : ConvexOn ℝ (Icc x q) (h + s) :=
    hhs.subset (Icc_subset_Icc hpx le_rfl) (convex_Icc x q)
  have hxR : x ∈ Icc x q := ⟨le_rfl, (hxy.trans_le hyq).le⟩
  have hyR : y ∈ Icc x q := ⟨hxy.le, hyq⟩
  have hxL : x ∈ Icc p y := ⟨hpx, hxy.le⟩
  have hyL : y ∈ Icc p y := ⟨hpx.trans hxy.le, le_rfl⟩
  have h1 : a ≤ slope s x y := hsR.le_slope_of_hasDerivWithinAt hxR hyR hxy ha
  have h2 : slope s x y ≤ b := hsL.slope_le_of_hasDerivWithinAt hxL hyL hxy hb
  have h3 : c + a ≤ slope (h + s) x y :=
    hhsR.le_slope_of_hasDerivWithinAt hxR hyR hxy (hc.add ha)
  have e : slope (h + s) x y = slope h x y + slope s x y := by
    simp only [slope_def_field, Pi.add_apply]; ring
  rw [← slope_def_field]
  linarith

namespace Queelius.BisectionComplexity
open NonconvexCost.Complexity Set Filter Topology
lemma midpoint_derivatives (s : ℝ → ℝ) (p m q : ℝ) (hs : ConvexOn ℝ (Icc p q) s)
    (hpm : p < m) (hmq : m < q) :
    ∃ a b : ℝ,HasDerivWithinAt s a (Icc m q) m ∧
      HasDerivWithinAt s b (Icc p m) m ∧ b ≤ a := by
  have hm : m ∈ Icc p q := ⟨hpm.le,hmq.le⟩
  have hr : MonotoneOn (slope s m) (Ioo m q) :=
    (hs.monotoneOn_slope_gt hm).mono (fun x hx => ⟨⟨hpm.le.trans hx.1.le,hx.2.le⟩,hx.1⟩)
  have hl : MonotoneOn (slope s m) (Ioo p m) :=
    (hs.monotoneOn_slope_lt hm).mono (fun x hx => ⟨⟨hx.1.le,hx.2.le.trans hmq.le⟩,hx.2⟩)
  have hbr : BddBelow ((slope s m) '' Ioo m q) := by
    refine ⟨(s m-s p)/(m-p),?_⟩
    rintro _ ⟨y,hy,rfl⟩
    simpa only [slope_def_field] using hs.slope_mono_adjacent ⟨le_rfl,hpm.le.trans hmq.le⟩
      ⟨hpm.le.trans hy.1.le,hy.2.le⟩ hpm hy.1
  have hbl : BddAbove ((slope s m) '' Ioo p m) := by
    refine ⟨(s q-s m)/(q-m),?_⟩
    rintro _ ⟨x,hx,rfl⟩
    rw [slope_comm s m x]
    simpa only [slope_def_field] using hs.slope_mono_adjacent ⟨hx.1.le,hx.2.le.trans hmq.le⟩
      ⟨hpm.le.trans hmq.le,le_rfl⟩ hx.2 hmq
  let a := sInf ((slope s m) '' Ioo m q)
  let b := sSup ((slope s m) '' Ioo p m)
  have htr := MonotoneOn.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr hmq) hr hbr
  have htl := MonotoneOn.tendsto_nhdsWithin_Ioo_left (nonempty_Ioo.mpr hpm) hl hbl
  have har : HasDerivWithinAt s a (Ioi m) m :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : m ∉ Ioi m)).mpr htr
  have hbr' : HasDerivWithinAt s b (Iio m) m :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : m ∉ Iio m)).mpr htl
  refine ⟨a,b,har.Ici_of_Ioi.mono Icc_subset_Ici_self,hbr'.Iic_of_Iio.mono Icc_subset_Iic_self,?_⟩
  apply le_csInf ((nonempty_Ioo.mpr hmq).image _)
  rintro _ ⟨y,hy,rfl⟩
  apply csSup_le ((nonempty_Ioo.mpr hpm).image _)
  rintro _ ⟨x,hx,rfl⟩
  rw [slope_comm s m x]
  simpa only [slope_def_field] using hs.slope_mono_adjacent ⟨hx.1.le,hx.2.le.trans hmq.le⟩
    ⟨hpm.le.trans hy.1.le,hy.2.le⟩ hx.2 hy.1
lemma bisect_shift (h : ℝ → ℝ) (p q : ℝ) (n : ℕ) :
    bisect h p q (n+1)=
      if 2*h ((p+q)/2) < h p+h q then bisect h p ((p+q)/2) n
      else bisect h ((p+q)/2) q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bisect,ih]
    split_ifs <;> simp_all [bisect]
lemma eval_shift_left (h : ℝ → ℝ) (p q : ℝ) (hl : 2*h ((p+q)/2) < h p+h q) (n : ℕ) :
    evalPt h p ((p+q)/2) (n+1)=evalPt h p q (n+2) := by
  simp only [evalPt,bisect_shift,if_pos hl]
lemma eval_shift_right (h : ℝ → ℝ) (p q : ℝ) (hl : ¬ 2*h ((p+q)/2) < h p+h q) (n : ℕ) :
    evalPt h ((p+q)/2) q (n+1)=evalPt h p q (n+2) := by
  simp only [evalPt,bisect_shift,if_neg hl]
lemma noStop_left (h h' : ℝ → ℝ) (p q : ℝ) (k : ℕ)
    (hr : NoStopWithin h h' p q (k+1)) (hl : 2*h ((p+q)/2) < h p+h q) :
    NoStopWithin h h' p ((p+q)/2) k := by
  intro j hj
  cases j with
  | zero => simpa [evalPt] using hr 0 (by omega)
  | succ n => rw [eval_shift_left h p q hl n];exact hr (n+2) (by omega)
lemma noStop_right (h h' : ℝ → ℝ) (p q : ℝ) (k : ℕ)
    (hr : NoStopWithin h h' p q (k+1)) (hl : ¬ 2*h ((p+q)/2) < h p+h q) :
    NoStopWithin h h' ((p+q)/2) q k := by
  intro j hj
  cases j with
  | zero => simpa [evalPt,bisect] using hr 1 (by omega)
  | succ n => rw [eval_shift_right h p q hl n];exact hr (n+2) (by omega)
end Queelius.BisectionComplexity

namespace Queelius.BisectionComplexity
open NonconvexCost.Complexity Set
lemma complexity (h h' s : ℝ → ℝ) (p q : ℝ) (hpq : p < q) (hs : ConvexOn ℝ (Icc p q) s)
    (hhs : ConvexOn ℝ (Icc p q) (h+s)) (hder : IsRightDerivOn h h' p q) (sp sq : ℝ)
    (hsp : HasDerivWithinAt s sp (Icc p q) p) (hsq : HasDerivWithinAt s sq (Icc p q) q)
    (k : ℕ) (hk : 1 ≤ k) (hrun : NoStopWithin h h' p q k) :
    (sp-sq)/k ≤ (h q-h p)/(q-p) := by
  induction k generalizing p q sp sq with
  | zero => omega
  | succ k ih =>
    have hdp := hder p ⟨le_rfl,hpq⟩
    have hnp : 0 ≤ h' p := by simpa [evalPt] using hrun 0 (by omega)
    by_cases hk0 : k=0
    · subst k
      have he := community_slope_drop h s p q hs hhs p q le_rfl hpq le_rfl
        (h' p) sp sq hdp hnp hsp hsq
      simpa using he
    have hkpos : 0 < (k:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
    have hkone : (1:ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
    let m := (p+q)/2
    have hpm : p < m := by dsimp [m];linarith
    have hmq : m < q := by dsimp [m];linarith
    obtain ⟨sr,sl,hsr,hsl,horder⟩ := midpoint_derivatives s p m q hs hpm hmq
    have hnm : 0 ≤ h' m := by simpa [evalPt,bisect,m] using hrun 1 (by omega)
    have hdm := hder m ⟨hpm.le,hmq⟩
    let A := (h q-h p)/(q-p)
    let L := (h m-h p)/(m-p)
    let R := (h q-h m)/(q-m)
    have hlen : 0 < q-p := sub_pos.mpr hpq
    have hL : L=(2*(h m-h p))/(q-p) := by
      dsimp only [L]
      rw [show m-p=(q-p)/2 by dsimp [m];ring]
      field_simp [hlen.ne']
      <;> ring
    have hR : R=(2*(h q-h m))/(q-p) := by
      dsimp only [R]
      rw [show q-m=(q-p)/2 by dsimp [m];ring]
      field_simp [hlen.ne']
      <;> ring
    have hsum : L+R=2*A := by rw [hL,hR];dsimp [A];ring
    simp only [Nat.cast_add,Nat.cast_one]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (k:ℝ)+1)).mpr
    by_cases hl : 2*h m < h p+h q
    · have hs' := hs.subset (Icc_subset_Icc le_rfl hmq.le) (convex_Icc p m)
      have hhs' := hhs.subset (Icc_subset_Icc le_rfl hmq.le) (convex_Icc p m)
      have hd' : IsRightDerivOn h h' p m := by
        intro x hx
        exact (hder x ⟨hx.1,hx.2.trans hmq⟩).mono (Icc_subset_Icc le_rfl hmq.le)
      have hi := ih p m hpm hs' hhs' hd' sp sl
        (hsp.mono (Icc_subset_Icc le_rfl hmq.le)) hsl (Nat.one_le_iff_ne_zero.mpr hk0)
        (noStop_left h h' p q k hrun hl)
      have hi' : sp-sl ≤ L*k := (div_le_iff₀ hkpos).mp hi
      have ho := community_slope_drop h s p q hs hhs m q hpm.le hmq le_rfl
        (h' m) sr sq hdm hnm hsr hsq
      have hlo : L ≤ A := by
        rw [hL]
        exact div_le_div_of_nonneg_right (by dsimp [A,m] at *;linarith) hlen.le
      have hm := mul_le_mul_of_nonneg_left hlo (sub_nonneg.mpr hkone)
      change sp-sq ≤ A*((k:ℝ)+1)
      change sr-sq ≤ R at ho
      nlinarith
    · have hs' := hs.subset (Icc_subset_Icc hpm.le le_rfl) (convex_Icc m q)
      have hhs' := hhs.subset (Icc_subset_Icc hpm.le le_rfl) (convex_Icc m q)
      have hd' : IsRightDerivOn h h' m q := by
        intro x hx
        exact hder x ⟨hpm.le.trans hx.1,hx.2⟩
      have hi := ih m q hmq hs' hhs' hd' sr sq hsr
        (hsq.mono (Icc_subset_Icc hpm.le le_rfl)) (Nat.one_le_iff_ne_zero.mpr hk0)
        (noStop_right h h' p q k hrun hl)
      have hi' : sr-sq ≤ R*k := (div_le_iff₀ hkpos).mp hi
      have ho := community_slope_drop h s p q hs hhs p m le_rfl hpm hmq.le
        (h' p) sp sl hdp hnp hsp hsl
      have hro : R ≤ A := by
        rw [hR]
        exact div_le_div_of_nonneg_right (by dsimp [A,m] at *;linarith) hlen.le
      have hm := mul_le_mul_of_nonneg_left hro (sub_nonneg.mpr hkone)
      change sp-sq ≤ A*((k:ℝ)+1)
      change sp-sl ≤ L at ho
      nlinarith
end Queelius.BisectionComplexity
namespace NonconvexCost.Complexity
 theorem _root_.prior_complexity (h h' s : ℝ → ℝ) (p q : ℝ) (hpq : p < q) (hs : ConvexOn ℝ (Set.Icc p q) s)
    (hhs : ConvexOn ℝ (Set.Icc p q) (h+s)) (hder : IsRightDerivOn h h' p q) (sp sq : ℝ)
    (hsp : HasDerivWithinAt s sp (Set.Icc p q) p) (hsq : HasDerivWithinAt s sq (Set.Icc p q) q)
    (k : ℕ) (hk : 1 ≤ k) (hrun : NoStopWithin h h' p q k) :
    (sp-sq)/k ≤ (h q-h p)/(q-p) := by
  exact Queelius.BisectionComplexity.complexity h h' s p q hpq hs hhs hder sp sq hsp hsq k hk hrun
end NonconvexCost.Complexity

namespace Queelius.BisectionTermination
open NonconvexCost.Complexity Set Filter Topology
open scoped ENNReal NNReal
lemma lipschitz_slope (s : ℝ → ℝ) (p q : ℝ) (K : ℝ≥0)
    (hl : LipschitzOnWith K s (Icc p q)) (x y : ℝ) (hx : x ∈ Icc p q) (hy : y ∈ Icc p q)
    (hxy : x ≠ y) : -(K:ℝ) ≤ slope s x y ∧ slope s x y ≤ K := by
  apply abs_le.mp
  rw [slope_def_field,abs_div]
  apply (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hxy.symm))).mpr
  simpa only [Real.dist_eq] using hl.dist_le_mul y hy x hx
lemma endpoint_derivatives (s : ℝ → ℝ) (p q : ℝ) (hpq : p < q)
    (hs : ConvexOn ℝ (Icc p q) s) (K : ℝ≥0) (hl : LipschitzOnWith K s (Icc p q)) :
    ∃ a b : ℝ,HasDerivWithinAt s a (Icc p q) p ∧ HasDerivWithinAt s b (Icc p q) q ∧
      -(K:ℝ) ≤ a ∧ b ≤ K := by
  have hp : p ∈ Icc p q := ⟨le_rfl,hpq.le⟩
  have hq : q ∈ Icc p q := ⟨hpq.le,le_rfl⟩
  have hr : MonotoneOn (slope s p) (Ioo p q) :=
    (hs.monotoneOn_slope_gt hp).mono (fun x hx => ⟨⟨hx.1.le,hx.2.le⟩,hx.1⟩)
  have hleft : MonotoneOn (slope s q) (Ioo p q) :=
    (hs.monotoneOn_slope_lt hq).mono (fun x hx => ⟨⟨hx.1.le,hx.2.le⟩,hx.2⟩)
  have hbr : BddBelow ((slope s p) '' Ioo p q) := by
    refine ⟨-(K:ℝ),?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact (lipschitz_slope s p q K hl p x hp ⟨hx.1.le,hx.2.le⟩ hx.1.ne).1
  have hbl : BddAbove ((slope s q) '' Ioo p q) := by
    refine ⟨(K:ℝ),?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact (lipschitz_slope s p q K hl q x hq ⟨hx.1.le,hx.2.le⟩ hx.2.ne').2
  let a := sInf ((slope s p) '' Ioo p q)
  let b := sSup ((slope s q) '' Ioo p q)
  have htr := MonotoneOn.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr hpq) hr hbr
  have htl := MonotoneOn.tendsto_nhdsWithin_Ioo_left (nonempty_Ioo.mpr hpq) hleft hbl
  have har : HasDerivWithinAt s a (Ioi p) p :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : p ∉ Ioi p)).mpr htr
  have hbl' : HasDerivWithinAt s b (Iio q) q :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : q ∉ Iio q)).mpr htl
  refine ⟨a,b,har.Ici_of_Ioi.mono Icc_subset_Ici_self,hbl'.Iic_of_Iio.mono Icc_subset_Iic_self,?_,?_⟩
  · apply le_csInf ((nonempty_Ioo.mpr hpq).image _)
    rintro _ ⟨x,hx,rfl⟩
    exact (lipschitz_slope s p q K hl p x hp ⟨hx.1.le,hx.2.le⟩ hx.1.ne).1
  · apply csSup_le ((nonempty_Ioo.mpr hpq).image _)
    rintro _ ⟨x,hx,rfl⟩
    exact (lipschitz_slope s p q K hl q x hq ⟨hx.1.le,hx.2.le⟩ hx.2.ne').2
lemma correction_below (h : ℝ → ℝ) (J : Set ℝ) (R : ℝ)
    (hR : (concaveDeviation h J).toReal < R) (hfinite : concaveDeviation h J ≠ ⊤) :
    ∃ s : ℝ → ℝ,∃ K : ℝ≥0,ConvexOn ℝ J s ∧ ConvexOn ℝ J (h+s) ∧
      LipschitzOnWith K s J ∧ (K:ℝ) < R := by
  have hp : 0 < R := ENNReal.toReal_nonneg.trans_lt hR
  have hi : concaveDeviation h J < ENNReal.ofReal R := by
    rw [← ENNReal.ofReal_toReal hfinite]
    exact (ENNReal.ofReal_lt_ofReal_iff hp).mpr hR
  unfold concaveDeviation at hi
  obtain ⟨s,hs⟩ := iInf_lt_iff.mp hi
  obtain ⟨K,hK⟩ := iInf_lt_iff.mp hs
  obtain ⟨hvalid,hKR⟩ := iInf_lt_iff.mp hK
  refine ⟨s,K,hvalid.1,hvalid.2.1,hvalid.2.2,?_⟩
  have hr := ENNReal.toReal_lt_toReal ENNReal.coe_ne_top ENNReal.ofReal_ne_top |>.mpr hKR
  simpa only [ENNReal.coe_toReal,ENNReal.toReal_ofReal hp.le] using hr
lemma termination (h h' : ℝ → ℝ) (p q : ℝ) (hpq : p < q) (hder : IsRightDerivOn h h' p q)
    (hM : concaveDeviation h (Icc p q) ≠ ⊤) (hσ : 0 < -((h q-h p)/(q-p))) :
    ¬ NoStopWithin h h' p q
      (1+⌊2*(concaveDeviation h (Icc p q)).toReal/(-((h q-h p)/(q-p)))⌋₊) := by
  let M := (concaveDeviation h (Icc p q)).toReal
  let σ := -((h q-h p)/(q-p))
  let k := 1+⌊2*M/σ⌋₊
  have hk : 1 ≤ k := by dsimp [k];omega
  have hkreal : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hσp : 0 < σ := hσ
  have hfloor : 2*M/σ < (k:ℝ) := by
    have hf := Nat.lt_floor_add_one (2*M/σ)
    simpa only [k,Nat.cast_add,Nat.cast_one,add_comm] using hf
  have hbudget : M < σ*(k:ℝ)/2 := by
    have hh := (div_lt_iff₀ hσp).mp hfloor
    nlinarith
  obtain ⟨s,K,hs,hhs,hl,hK⟩ := correction_below h (Icc p q) (σ*(k:ℝ)/2) hbudget hM
  obtain ⟨a,b,ha,hb,hKa,hbK⟩ := endpoint_derivatives s p q hpq hs K hl
  intro hrun
  have hc := Queelius.BisectionComplexity.complexity h h' s p q hpq hs hhs hder a b ha hb k hk hrun
  have hc' := (div_le_iff₀ hkreal).mp hc
  rw [show (h q-h p)/(q-p) = -σ by dsimp [σ];ring] at hc'
  nlinarith
end Queelius.BisectionTermination

namespace NonconvexCost.Complexity
theorem _root_.prior_termination (h h' : ℝ → ℝ) (p q : ℝ) (hpq : p < q) (hder : IsRightDerivOn h h' p q)
    (hM : concaveDeviation h (Set.Icc p q) ≠ ⊤) (hσ : 0 < -((h q-h p)/(q-p))) :
    ¬ NoStopWithin h h' p q
      (1+⌊2*(concaveDeviation h (Set.Icc p q)).toReal/(-((h q-h p)/(q-p)))⌋₊) := by
  exact Queelius.BisectionTermination.termination h h' p q hpq hder hM hσ
end NonconvexCost.Complexity

end

namespace Queelius.OracleComplexity
open NonconvexCost.Complexity Set Filter Topology
open scoped RealInnerProductSpace ENNReal
lemma right_derivative_of_increment (h : ℝ → ℝ) (t a : ℝ)
    (hi : Tendsto (fun z : ℝ => (h (t+z)-h t)/z) (𝓝[>] 0) (𝓝 a)) :
    HasDerivWithinAt h a (Ici t) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have he : Ici t\{t}=Ioi t := by
    ext z
    simp only [Set.mem_sdiff,mem_Ici,mem_singleton_iff,mem_Ioi]
    constructor
    · rintro ⟨hz,hne⟩;exact lt_of_le_of_ne hz (Ne.symm hne)
    · intro hz;exact ⟨hz.le,ne_of_gt hz⟩
  rw [he]
  have ht : Tendsto (fun z : ℝ => z-t) (𝓝[>] t) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun z : ℝ => z-t) := by fun_prop
      simpa only [sub_self] using (hc.tendsto t).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_pos.mpr (show t<z from hz)
  have hs : slope h t=(fun y : ℝ => (h y-h t)/(y-t)) := by funext y;rw [slope_def_field]
  rw [hs]
  simpa only [Function.comp_def,add_sub_cancel] using hi.comp ht
lemma deviation_add_affine_le (h : ℝ → ℝ) (J : Set ℝ) (hJ : Convex ℝ J) (a b : ℝ) :
    concaveDeviation (fun t => h t+(a*t+b)) J ≤ concaveDeviation h J := by
  have haf : ConvexOn ℝ J (fun t : ℝ => a*t+b) := by
    refine ⟨hJ,?_⟩
    intro x hx y hy u v hu hv huv
    dsimp
    have he : a*(u*x+v*y)+b=u*(a*x+b)+v*(a*y+b) := by
      calc
        _ = a*(u*x+v*y)+(u+v)*b := by rw [huv,one_mul]
        _ = _ := by ring
    exact he.le
  unfold concaveDeviation
  apply le_iInf;intro s
  apply le_iInf;intro K
  apply le_iInf;intro hs
  have hc : ConvexOn ℝ J ((fun t => h t+(a*t+b))+s) := by
    convert! hs.2.1.add haf using 1
    funext t;simp only [Pi.add_apply];ring
  exact iInf_le_of_le s (iInf_le_of_le K (iInf_le_of_le ⟨hs.1,hc,hs.2.2⟩ le_rfl))
lemma point_shift {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (δ : ℝ) (x g : X) (t u : ℝ) :
    lsPoint δ x g (t+u)=lsPoint δ x g t+u • (‖g‖⁻¹ • g) := by
  unfold lsPoint
  module
lemma lsPoint_mem {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (δ : ℝ) (hδ : 0 < δ) (C : Set X) (x g : X) (hg : g ≠ 0)
    (hball : ∀ y : X,‖y‖ ≤ δ → x+y ∈ C) (t : ℝ) (ht : t ∈ Icc 0 δ) :
    lsPoint δ x g t ∈ C := by
  have hd := Queelius.NonsmoothLine.point_distance δ x g hg t
  have hb : ‖lsPoint δ x g t-x‖ ≤ δ := by rw [hd,abs_of_nonpos (sub_nonpos.mpr ht.2)];linarith [ht.1]
  simpa using hball (lsPoint δ x g t-x) hb
lemma line_right_derivative {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (C : Set X) (hG : IsDirSubgradMapOn f G C)
    (δ ε : ℝ) (hδ : 0 < δ) (x g : X) (hg : g ≠ 0)
    (hball : ∀ y : X,‖y‖ ≤ δ → x+y ∈ C) :
    IsRightDerivOn (lsFun f δ ε x g) (lsDeriv G δ ε x g) 0 δ := by
  intro t ht
  have hx := lsPoint_mem δ hδ C x g hg hball t ⟨ht.1,ht.2.le⟩
  have hlocal : ∃ τ > 0,∀ u ∈ Icc (0:ℝ) τ,lsPoint δ x g t+u • (‖g‖⁻¹ • g) ∈ C := by
    refine ⟨δ-t,sub_pos.mpr ht.2,?_⟩
    intro u hu
    rw [← point_shift]
    exact lsPoint_mem δ hδ C x g hg hball (t+u) ⟨by linarith [ht.1,hu.1],by linarith [hu.2]⟩
  have hd := hG (lsPoint δ x g t) hx (‖g‖⁻¹ • g) hlocal
  have hc : HasDerivWithinAt (fun u => f (lsPoint δ x g u))
      ⟪G (lsPoint δ x g t) (‖g‖⁻¹ • g),‖g‖⁻¹ • g⟫ (Icc t δ) t := by
    apply (right_derivative_of_increment _ _ _ ?_).mono (fun u hu => hu.1)
    simpa only [point_shift] using hd
  have ha := ((hasDerivAt_id t).const_mul (ε/2)).hasDerivWithinAt (s := Icc t δ)
  convert! hc.sub ha using 1
  · funext u;simp only [lsFun,Pi.sub_apply,id_eq];ring
  · unfold lsDeriv;ring
end Queelius.OracleComplexity

namespace Queelius.OracleComplexity
open NonconvexCost.Complexity Set Filter Topology
open scoped RealInnerProductSpace ENNReal
lemma line_segment_identity {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (δ : ℝ) (hδ : δ ≠ 0) (x g : X) (t : ℝ) :
    lsPoint δ x g 0+(t/δ) • (x-lsPoint δ x g 0)=lsPoint δ x g t := by
  have hd : x-lsPoint δ x g 0=δ • (‖g‖⁻¹ • g) := by unfold lsPoint;module
  rw [hd,smul_smul,div_mul_cancel₀ _ hδ]
  unfold lsPoint
  module
lemma line_deviation_bound {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (C : Set X) (δ ε : ℝ) (hδ : 0 < δ) (x g : X) (hx : x ∈ C) (hg : g ≠ 0)
    (hball : ∀ y : X,‖y‖ ≤ δ → x+y ∈ C) :
    concaveDeviation (lsFun f δ ε x g) (Icc 0 δ) ≤ nonconvexityModulus f C δ := by
  have hx' := lsPoint_mem δ hδ C x g hg hball 0 ⟨le_rfl,hδ.le⟩
  have hd : ‖lsPoint δ x g 0-x‖ ≤ δ := by
    rw [Queelius.NonsmoothLine.point_distance δ x g hg 0]
    simp [abs_of_pos hδ]
  have hb : concaveDeviation (fun t => f (lsPoint δ x g 0+(t/δ) • (x-lsPoint δ x g 0))) (Icc 0 δ) ≤
      nonconvexityModulus f C δ :=
    le_iSup_of_le (lsPoint δ x g 0) (le_iSup_of_le hx' (le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le hd le_rfl))))
  have he : (fun t => f (lsPoint δ x g 0+(t/δ) • (x-lsPoint δ x g 0)))=
      (fun t => f (lsPoint δ x g t)) := by funext t;rw [line_segment_identity δ hδ.ne']
  rw [he] at hb
  have ha := deviation_add_affine_le (fun t => f (lsPoint δ x g t)) (Icc 0 δ) (convex_Icc _ _) (-ε/2) 0
  have hf : (fun t => f (lsPoint δ x g t)+(-ε/2*t+0))=lsFun f δ ε x g := by
    funext t;unfold lsFun;ring
  rw [hf] at ha
  exact ha.trans hb
lemma uniform_line_termination {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (C : Set X) (hG : IsDirSubgradMapOn f G C)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (x g : X) (hx : x ∈ C)
    (hg : ε < ‖g‖) (hball : ∀ y : X,‖y‖ ≤ δ → x+y ∈ C)
    (hdec : f x-f (lsPoint δ x g 0) < δ*ε/3)
    (hΛ : nonconvexityModulus f C δ ≠ ⊤) :
    ¬ NoStopWithin (lsFun f δ ε x g) (lsDeriv G δ ε x g) 0 δ
      (1+⌊12*(nonconvexityModulus f C δ).toReal/ε⌋₊) := by
  let h := lsFun f δ ε x g
  let σ := -((h δ-h 0)/(δ-0))
  let M := concaveDeviation h (Icc 0 δ)
  let Λ := nonconvexityModulus f C δ
  have hgne : g ≠ 0 := norm_pos_iff.mp (hε.trans hg)
  have hMle : M ≤ Λ := line_deviation_bound f C δ ε hδ x g hx hgne hball
  have hM : M ≠ ⊤ := ne_top_of_le_ne_top hΛ hMle
  have hσ : ε/6 < σ := by
    have hh := (prior_outcome f G δ ε hδ hε x g hg hdec).1
    dsimp [σ,h]
    linarith
  have hσ0 : 0 < σ := by linarith
  have hmreal : M.toReal ≤ Λ.toReal := ENNReal.toReal_mono hΛ hMle
  have hratio : 2*M.toReal/σ ≤ 12*Λ.toReal/ε := by
    apply (div_le_div_iff₀ hσ0 hε).mpr
    nlinarith [mul_nonneg (show 0 ≤ Λ.toReal from ENNReal.toReal_nonneg) (sub_nonneg.mpr hσ.le),
      mul_nonneg hε.le (sub_nonneg.mpr hmreal)]
  have hfloor : 1+⌊2*M.toReal/σ⌋₊ ≤ 1+⌊12*Λ.toReal/ε⌋₊ := Nat.add_le_add_left (Nat.floor_le_floor hratio) 1
  have ht := prior_termination h (lsDeriv G δ ε x g) 0 δ hδ
    (line_right_derivative f G C hG δ ε hδ x g hgne hball) hM hσ0
  intro hno
  apply ht
  intro j hj
  exact hno j (lt_of_lt_of_le hj hfloor)
end Queelius.OracleComplexity

namespace Queelius.OracleComplexity
open NonconvexCost.Complexity Set Classical
noncomputable def nextAge {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (s : State X) (a : ℕ) : ℕ := match s.ph with | .bis _ _ => a+1 | _ => 0
noncomputable def age {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (x0 g0 : X) : ℕ → ℕ
  | 0 => 0
  | n+1 => nextAge (run f G δ ε x0 g0 (n+1)) (age f G δ ε x0 g0 n)
def PendingState {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (s : State X) (a : ℕ) : Prop :=
  match s.ph with
  | .bis l r => 0 < a ∧ l=(bisect (lsFun f δ ε s.x s.g) 0 δ (a-1)).1 ∧
      r=(bisect (lsFun f δ ε s.x s.g) 0 δ (a-1)).2 ∧
      NoStopWithin (lsFun f δ ε s.x s.g) (lsDeriv G δ ε s.x s.g) 0 δ a ∧
      f s.x-f (lsPoint δ s.x s.g 0) < δ*ε/3
  | _ => a=0
lemma step_pending {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (s : State X) (a : ℕ)
    (ha : PendingState f G δ ε s a) :
    PendingState f G δ ε (step f G δ ε s) (nextAge (step f G δ ε s) a) := by
  cases hp : s.ph with
  | trial =>
    have ha0 : a=0 := by simpa only [PendingState,hp] using ha
    simp only [step,hp]
    split_ifs with hsmall hdec hneg
    · simpa only [nextAge,hp,PendingState] using ha0
    · rfl
    · rfl
    · simp only [nextAge,ha0,zero_add,PendingState,Nat.sub_self,bisect]
      refine ⟨by omega,True.intro,True.intro,?_,lt_of_not_ge hdec⟩
      intro j hj
      have hj0 : j=0 := by omega
      simpa only [hj0,evalPt] using le_of_not_gt hneg
  | reinit x => simp [step,hp,nextAge,PendingState]
  | bis l r =>
    obtain ⟨ha0,hl,hr,hno,hdec⟩ := (show 0 < a ∧ _ by simpa only [PendingState,hp] using ha)
    have hae : a=(a-1)+1 := by omega
    have heval : evalPt (lsFun f δ ε s.x s.g) 0 δ a=(l+r)/2 := by
      conv_lhs => rw [hae]
      simp only [evalPt,← hl,← hr]
    have hnext : bisect (lsFun f δ ε s.x s.g) 0 δ a=
        if 2*lsFun f δ ε s.x s.g ((l+r)/2)<lsFun f δ ε s.x s.g l+lsFun f δ ε s.x s.g r
        then (l,(l+r)/2) else ((l+r)/2,r) := by
      conv_lhs => rw [hae]
      simp only [bisect,← hl,← hr]
    simp only [step,hp]
    split_ifs with hneg hmid
    · rfl
    · simp only [nextAge,PendingState,Nat.add_sub_cancel,hnext,if_pos hmid]
      refine ⟨by omega,True.intro,True.intro,?_,hdec⟩
      intro j hj
      by_cases hj0 : j<a
      · exact hno j hj0
      · have hj1 : j=a := by omega
        rw [hj1,heval]
        exact le_of_not_gt hneg
    · simp only [nextAge,PendingState,Nat.add_sub_cancel,hnext,if_neg hmid]
      refine ⟨by omega,True.intro,True.intro,?_,hdec⟩
      intro j hj
      by_cases hj0 : j<a
      · exact hno j hj0
      · have hj1 : j=a := by omega
        rw [hj1,heval]
        exact le_of_not_gt hneg
lemma run_pending {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (x0 g0 : X) (n : ℕ) :
    PendingState f G δ ε (run f G δ ε x0 g0 n) (age f G δ ε x0 g0 n) := by
  induction n with
  | zero => rfl
  | succ n ih => exact step_pending f G δ ε _ _ ih
lemma run_age_bound {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (C : Set X) (hG : IsDirSubgradMapOn f G C)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (x0 g0 : X) (hx0 : x0 ∈ C)
    (hg0 : g0 ∈ goldstein G δ x0)
    (hsub : ∀ x ∈ C,f x ≤ f x0 → ∀ y : X,‖y‖ ≤ δ → x+y ∈ C)
    (hΛ : nonconvexityModulus f C δ ≠ ⊤) (n : ℕ) (l r : ℝ)
    (hp : (run f G δ ε x0 g0 n).ph=.bis l r) :
    age f G δ ε x0 g0 n < 1+⌊12*(nonconvexityModulus f C δ).toReal/ε⌋₊ := by
  have hc := Queelius.NonsmoothReduction.run_control f G δ ε hδ hε C x0 g0 hx0 hsub n
  have hv := Queelius.NonsmoothRun.run_valid f G δ ε hδ hε x0 g0 hg0 n
  have hg := (hv.2 l r hp).2.2.2
  have hfx : f (run f G δ ε x0 g0 n).x ≤ f x0 := by
    have hn : 0 ≤ (δ*ε/3)*(Queelius.NonsmoothReduction.reductions f G δ ε x0 g0 n : ℝ) := by positivity
    linarith [hc.2.1]
  obtain ⟨ha,hl,hr,hno,hdec⟩ := (show 0 < age f G δ ε x0 g0 n ∧ _ by simpa only [PendingState,hp] using run_pending f G δ ε x0 g0 n)
  have ht := uniform_line_termination f G C hG δ ε hδ hε _ _ hc.1 hg (hsub _ hc.1 hfx) hdec hΛ
  by_contra hbad
  apply ht
  intro j hj
  exact hno j (lt_of_lt_of_le hj (Nat.le_of_not_gt hbad))
end Queelius.OracleComplexity

namespace Queelius.OracleComplexity
open NonconvexCost.Complexity Queelius.NonsmoothRun Queelius.NonsmoothReduction Set Classical
lemma increment_tight (a L ε : ℝ) (k : ℕ) (hε : 0 < ε) (ha : ε < a)
    (hb : (a^2/(16*L^2))*(16+(k:ℝ)) ≤ 1) (hL : 0 < L) :
    ((k+1:ℕ):ℝ) ≤ 16*L^2/ε^2-15 := by
  have hD : 0 < 16*L^2 := by positivity
  have hE : 0 < ε^2 := by positivity
  have hA : a^2*(16+(k:ℝ)) ≤ 16*L^2 := by
    apply (div_le_one hD).mp
    simpa only [div_mul_eq_mul_div] using hb
  have haa : ε^2 < a^2 := by nlinarith
  have hh : ((k+1:ℕ):ℝ)+15 ≤ 16*L^2/ε^2 := by
    apply (le_div_iff₀ hE).mpr
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (sub_nonneg.mpr haa.le)]
  linarith
lemma local_count_tight {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε L : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hL : IsLBounded G L) (heL : ε < L) (x0 g0 : X) (hg0 : g0 ∈ goldstein G δ x0) (n : ℕ) :
    (localCount f G δ ε x0 g0 n : ℝ) ≤ 16*L^2/ε^2-15 := by
  have hcap : 0 ≤ 16*L^2/ε^2-15 := by
    have he : 0 < ε^2 := by positivity
    have hh : 16 ≤ 16*L^2/ε^2 := by apply (le_div_iff₀ he).mpr;nlinarith
    linarith
  induction n with
  | zero => simpa only [localCount,Nat.cast_zero] using hcap
  | succ n ih =>
    rw [localCount]
    split_ifs with hi hs
    · simpa only [Nat.cast_zero] using hcap
    · have hb := (run_budget f G δ ε L hδ hε hL x0 g0 hg0 n).2
      have hph := hs.1
      simp only [hph] at hb
      exact increment_tight _ L ε _ hε hs.2.1 hb hL.1
    · exact ih
lemma count_tight {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε L : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hL : IsLBounded G L) (heL : ε < L) (x0 g0 : X) (hg0 : g0 ∈ goldstein G δ x0) (n : ℕ) :
    (searchCount f G δ ε x0 g0 n : ℝ) ≤
      ((reductions f G δ ε x0 g0 n : ℝ)+1)*(16*L^2/ε^2-15) := by
  have ha (n : ℕ) : (searchCount f G δ ε x0 g0 n : ℝ) ≤
      (reductions f G δ ε x0 g0 n : ℝ)*(16*L^2/ε^2-15)+(localCount f G δ ε x0 g0 n : ℝ) := by
    induction n with
    | zero => simp [searchCount,reductions,localCount]
    | succ n ih =>
      have hk := local_count_tight f G δ ε L hδ hε hL heL x0 g0 hg0 n
      rw [searchCount_succ,reductions_succ,localCount]
      by_cases hi : IsReinit (run f G δ ε x0 g0 n)
      · have hno : ¬ StartsLineSearch f δ ε (run f G δ ε x0 g0 n) := by
          obtain ⟨x,hx⟩ := hi
          simp [StartsLineSearch,hx]
        simp only [if_pos hi,if_neg hno,Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero]
        nlinarith
      · by_cases hyes : StartsLineSearch f δ ε (run f G δ ε x0 g0 n)
        · simp only [if_neg hi,if_pos hyes,Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero]
          linarith
        · simp only [if_neg hi,if_neg hyes,Nat.cast_add,Nat.cast_zero,add_zero]
          exact ih
  have hs := ha n
  have hk := local_count_tight f G δ ε L hδ hε hL heL x0 g0 hg0 n
  nlinarith
end Queelius.OracleComplexity

namespace Queelius.OracleComplexity
open NonconvexCost.Complexity Queelius.NonsmoothRun Queelius.NonsmoothReduction Set Classical
noncomputable def reserve {X : Type*} (s : State X) (a K : ℕ) : ℝ :=
  match s.ph with | .bis _ _ => (K:ℝ)-a | _ => 0
noncomputable def pendingOne {X : Type*} (s : State X) : ℝ :=
  match s.ph with | .reinit _ => 1 | _ => 0
lemma elapsed_step {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (s : State X) (a K : ℕ) (hK : 1 ≤ K)
    (ha : PendingState f G δ ε s a) (hnd : ¬ IsDone ε s)
    (hab : ∀ l r,s.ph=.bis l r → a<K) :
    1+reserve (step f G δ ε s) (nextAge (step f G δ ε s) a) K+pendingOne s ≤
      reserve s a K+2*(if IsReinit s then (1:ℝ) else 0)+
        (if StartsLineSearch f δ ε s then (K:ℝ) else 0)+pendingOne (step f G δ ε s) := by
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast hK
  cases hp : s.ph with
  | trial =>
    have ha0 : a=0 := by simpa only [PendingState,hp] using ha
    have hi : ¬ IsReinit s := by simp [IsReinit,hp]
    have hlarge : ¬ ‖s.g‖ ≤ ε := fun h => hnd ⟨hp,h⟩
    by_cases hdec : δ*ε/3 ≤ f s.x-f (lsPoint δ s.x s.g 0)
    · have hno : ¬ StartsLineSearch f δ ε s := by simp [StartsLineSearch,hp,not_lt.mpr hdec]
      simp [step,hp,hlarge,hdec,reserve,pendingOne,nextAge,hi,hno]
    · have hyes : StartsLineSearch f δ ε s := ⟨hp,lt_of_not_ge hlarge,lt_of_not_ge hdec⟩
      simp only [step,hp,if_neg hlarge,if_neg hdec,if_neg hi,if_pos hyes]
      split_ifs with hneg
      · simpa only [reserve,pendingOne,nextAge,hp,zero_add,add_zero,mul_zero] using hKr
      · simp [reserve,pendingOne,nextAge,hp,ha0]
  | reinit x =>
    have hi : IsReinit s := ⟨x,hp⟩
    have hno : ¬ StartsLineSearch f δ ε s := by simp [StartsLineSearch,hp]
    norm_num [step,hp,reserve,pendingOne,nextAge,hi,hno]
  | bis l r =>
    have hi : ¬ IsReinit s := by simp [IsReinit,hp]
    have hno : ¬ StartsLineSearch f δ ε s := by simp [StartsLineSearch,hp]
    have habr : (a:ℝ)+1 ≤ K := by exact_mod_cast hab l r hp
    simp only [step,hp]
    split_ifs with hneg hmid
    · simp only [reserve,pendingOne,nextAge,hp,if_neg hi,if_neg hno,mul_zero,add_zero,zero_add]
      linarith
    · simp only [reserve,pendingOne,nextAge,hp,if_neg hi,if_neg hno,mul_zero,add_zero,zero_add,Nat.cast_add,Nat.cast_one]
      linarith
    · simp only [reserve,pendingOne,nextAge,hp,if_neg hi,if_neg hno,mul_zero,add_zero,zero_add,Nat.cast_add,Nat.cast_one]
      linarith
lemma elapsed_bound {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (x0 g0 : X) (K : ℕ) (hK : 1 ≤ K)
    (hages : ∀ n l r,(run f G δ ε x0 g0 n).ph=.bis l r → age f G δ ε x0 g0 n<K)
    (n : ℕ) (hnd : ∀ j<n,¬ IsDone ε (run f G δ ε x0 g0 j)) :
    (n:ℝ)+reserve (run f G δ ε x0 g0 n) (age f G δ ε x0 g0 n) K ≤
      2*(reductions f G δ ε x0 g0 n : ℝ)+(searchCount f G δ ε x0 g0 n : ℝ)*K+
        pendingOne (run f G δ ε x0 g0 n) := by
  induction n with
  | zero => simp [run,reserve,pendingOne,reductions,searchCount]
  | succ n ih =>
    have hp := ih (fun j hj => hnd j (by omega))
    have hs := elapsed_step f G δ ε (run f G δ ε x0 g0 n) (age f G δ ε x0 g0 n) K hK
      (run_pending f G δ ε x0 g0 n) (hnd n (by omega)) (hages n)
    rw [reductions_succ,searchCount_succ]
    change ((n+1:ℕ):ℝ)+reserve (step f G δ ε (run f G δ ε x0 g0 n))
      (nextAge (step f G δ ε (run f G δ ε x0 g0 n)) (age f G δ ε x0 g0 n)) K ≤ _
    by_cases hi : IsReinit (run f G δ ε x0 g0 n) <;>
      by_cases hls : StartsLineSearch f δ ε (run f G δ ε x0 g0 n) <;>
      simp only [hi,hls,if_true,if_false,Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero] at * <;>
      dsimp only [run] <;> nlinarith
end Queelius.OracleComplexity

namespace NonconvexCost.Complexity
open Queelius.OracleComplexity Queelius.NonsmoothRun Queelius.NonsmoothReduction
open Set Classical in
theorem _root_.prior_oracle_root {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (δ ε L : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (C : Set X) (hC : Convex ℝ C) (f : X → ℝ)
    (hbdd : BddBelow (f '' C)) (G : X → X → X) (hG : IsDirSubgradMapOn f G C)
    (hL : IsLBounded G L) (x0 : X) (hx0 : x0 ∈ C)
    (hsub : ∀ x ∈ C, f x ≤ f x0 → ∀ y : X, ‖y‖ ≤ δ → x + y ∈ C)
    (hΛ : nonconvexityModulus f C δ ≠ ⊤) (g0 : X) (hg0 : g0 ∈ goldstein G δ x0) :
    ∃ n : ℕ,
      (n : ℝ) ≤ ((⌊3 * (f x0 - sInf (f '' C)) / (δ * ε)⌋₊ : ℝ) + 1) * (16 * L ^ 2 / ε ^ 2) *
          (1 + ⌊12 * (nonconvexityModulus f C δ).toReal / ε⌋₊) ∧
        IsDone ε (run f G δ ε x0 g0 n) ∧
        (run f G δ ε x0 g0 n).g ∈ goldstein G δ (run f G δ ε x0 g0 n).x := by
  let K := 1+⌊12*(nonconvexityModulus f C δ).toReal/ε⌋₊
  let B := 16*L^2/ε^2
  let R : ℝ := (⌊3*(f x0-sInf (f '' C))/(δ*ε)⌋₊ : ℝ)+1
  let T := R*B*K
  have hK : 1 ≤ K := by dsimp [K];omega
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0:ℝ) ≤ K := by positivity
  have hB0 : 0 ≤ B := by dsimp [B];positivity
  have hT : 0 ≤ T := by dsimp [T,R];positivity
  by_cases hsmall : ‖g0‖ ≤ ε
  · refine ⟨0,?_,⟨rfl,hsmall⟩,hg0⟩
    simpa only [T,R,B,K,Nat.cast_add,Nat.cast_one,Nat.cast_zero] using hT
  · have heL : ε < L := (lt_of_not_ge hsmall).trans_le (goldstein_norm G L δ hL x0 g0 hg0)
    have hex : ∃ n : ℕ,(n:ℝ) ≤ T ∧ IsDone ε (run f G δ ε x0 g0 n) := by
      by_contra hnone
      let n := ⌊T⌋₊+1
      have hnd : ∀ j<n,¬ IsDone ε (run f G δ ε x0 g0 j) := by
        intro j hj hd
        apply hnone
        refine ⟨j,?_,hd⟩
        have hjn : j ≤ ⌊T⌋₊ := by dsimp [n] at hj;omega
        have hjr : (j:ℝ) ≤ (⌊T⌋₊ : ℝ) := by exact_mod_cast hjn
        exact hjr.trans (Nat.floor_le hT)
      have hages (m : ℕ) (l r : ℝ) (hp : (run f G δ ε x0 g0 m).ph=.bis l r) :
          age f G δ ε x0 g0 m<K :=
        run_age_bound f G C hG δ ε hδ hε x0 g0 hx0 hg0 hsub hΛ m l r hp
      have ht := elapsed_bound f G δ ε x0 g0 K hK hages n hnd
      have hrsv : 0 ≤ reserve (run f G δ ε x0 g0 n) (age f G δ ε x0 g0 n) K := by
        cases hp : (run f G δ ε x0 g0 n).ph with
        | trial => simp [reserve,hp]
        | reinit x => simp [reserve,hp]
        | bis l r =>
          simp only [reserve,hp]
          have hh : (age f G δ ε x0 g0 n : ℝ) ≤ K := by exact_mod_cast (hages n l r hp).le
          linarith
      have hpend : pendingOne (run f G δ ε x0 g0 n) ≤ 1 := by
        cases hp : (run f G δ ε x0 g0 n).ph <;> simp [pendingOne,hp]
      have hs := count_tight f G δ ε L hδ hε hL heL x0 g0 hg0 n
      have hsmul := mul_le_mul_of_nonneg_right hs hK0
      change (searchCount f G δ ε x0 g0 n : ℝ)*K ≤
        ((reductions f G δ ε x0 g0 n : ℝ)+1)*(B-15)*K at hsmul
      have hr := reduction_bound f G δ ε hδ hε C hbdd x0 g0 hx0 hsub n
      have hrnat : reductions f G δ ε x0 g0 n ≤ ⌊3*(f x0-sInf (f '' C))/(δ*ε)⌋₊ := Nat.le_floor hr
      have hrr : (reductions f G δ ε x0 g0 n : ℝ)+1 ≤ R := by dsimp [R];exact_mod_cast Nat.add_le_add_right hrnat 1
      have hgrowth := mul_le_mul_of_nonneg_right hrr (mul_nonneg hB0 hK0)
      have htarget : ((reductions f G δ ε x0 g0 n : ℝ)+1)*B*K ≤ T := by
        simpa only [T,mul_assoc] using hgrowth
      have hred0 : (0:ℝ) ≤ reductions f G δ ε x0 g0 n := Nat.cast_nonneg _
      have hprod := mul_nonneg hred0 (sub_nonneg.mpr hKr)
      have htime : (n:ℝ) ≤ T := by nlinarith
      have hnf : T < (n:ℝ) := by dsimp [n];simpa only [Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one T
      linarith
    obtain ⟨n,hn,hd⟩ := hex
    refine ⟨n,?_,hd,(run_valid f G δ ε hδ hε x0 g0 hg0 n).1⟩
    simpa only [T,R,B,K,Nat.cast_add,Nat.cast_one] using hn
end NonconvexCost.Complexity

namespace Queelius.OracleComplexity
open NonconvexCost.Complexity Set Filter Topology
open scoped RealInnerProductSpace ENNReal
lemma line_path_convex {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (δ : ℝ) (hδ : 0 < δ) (C : Set X) (hC : Convex ℝ C) (x g : X)
    (hx : x ∈ C) (hx' : lsPoint δ x g 0 ∈ C) :
    ∀ t ∈ Icc (0:ℝ) δ,lsPoint δ x g t ∈ C := by
  intro t ht
  rw [← line_segment_identity δ hδ.ne']
  exact hC.add_smul_sub_mem hx' hx ⟨div_nonneg ht.1 hδ.le,(div_le_one hδ).mpr ht.2⟩
lemma line_right_derivative_path {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (C : Set X) (hG : IsDirSubgradMapOn f G C)
    (δ ε : ℝ) (hδ : 0 < δ) (x g : X) (hg : g ≠ 0)
    (hpath : ∀ t ∈ Icc (0:ℝ) δ,lsPoint δ x g t ∈ C) :
    IsRightDerivOn (lsFun f δ ε x g) (lsDeriv G δ ε x g) 0 δ := by
  intro t ht
  have hx := hpath t ⟨ht.1,ht.2.le⟩
  have hlocal : ∃ τ > 0,∀ u ∈ Icc (0:ℝ) τ,lsPoint δ x g t+u • (‖g‖⁻¹ • g) ∈ C := by
    refine ⟨δ-t,sub_pos.mpr ht.2,?_⟩
    intro u hu
    rw [← point_shift]
    exact hpath (t+u) ⟨by linarith [ht.1,hu.1],by linarith [hu.2]⟩
  have hd := hG (lsPoint δ x g t) hx (‖g‖⁻¹ • g) hlocal
  have hc : HasDerivWithinAt (fun u => f (lsPoint δ x g u))
      ⟪G (lsPoint δ x g t) (‖g‖⁻¹ • g),‖g‖⁻¹ • g⟫ (Icc t δ) t := by
    apply (right_derivative_of_increment _ _ _ ?_).mono (fun u hu => hu.1)
    simpa only [point_shift] using hd
  have ha := ((hasDerivAt_id t).const_mul (ε/2)).hasDerivWithinAt (s := Icc t δ)
  convert! hc.sub ha using 1
  · funext u;simp only [lsFun,Pi.sub_apply,id_eq];ring
  · unfold lsDeriv;ring
lemma line_deviation_endpoints {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (C : Set X) (δ ε : ℝ) (hδ : 0 < δ) (x g : X) (hx : x ∈ C) (hg : g ≠ 0)
    (hx' : lsPoint δ x g 0 ∈ C) :
    concaveDeviation (lsFun f δ ε x g) (Icc 0 δ) ≤ nonconvexityModulus f C δ := by
  have hd : ‖lsPoint δ x g 0-x‖ ≤ δ := by
    rw [Queelius.NonsmoothLine.point_distance δ x g hg 0]
    simp [abs_of_pos hδ]
  have hb : concaveDeviation (fun t => f (lsPoint δ x g 0+(t/δ) • (x-lsPoint δ x g 0))) (Icc 0 δ) ≤
      nonconvexityModulus f C δ :=
    le_iSup_of_le (lsPoint δ x g 0) (le_iSup_of_le hx' (le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le hd le_rfl))))
  have he : (fun t => f (lsPoint δ x g 0+(t/δ) • (x-lsPoint δ x g 0)))=
      (fun t => f (lsPoint δ x g t)) := by funext t;rw [line_segment_identity δ hδ.ne']
  rw [he] at hb
  have ha := deviation_add_affine_le (fun t => f (lsPoint δ x g t)) (Icc 0 δ) (convex_Icc _ _) (-ε/2) 0
  have hf : (fun t => f (lsPoint δ x g t)+(-ε/2*t+0))=lsFun f δ ε x g := by
    funext t;unfold lsFun;ring
  rw [hf] at ha
  exact ha.trans hb
lemma uniform_line_endpoints {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (C : Set X) (hC : Convex ℝ C) (hG : IsDirSubgradMapOn f G C)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (x g : X) (hx : x ∈ C)
    (hg : ε < ‖g‖) (hx' : lsPoint δ x g 0 ∈ C)
    (hdec : f x-f (lsPoint δ x g 0) < δ*ε/3)
    (hΛ : nonconvexityModulus f C δ ≠ ⊤) :
    ¬ NoStopWithin (lsFun f δ ε x g) (lsDeriv G δ ε x g) 0 δ
      (1+⌊12*(nonconvexityModulus f C δ).toReal/ε⌋₊) := by
  let h := lsFun f δ ε x g
  let σ := -((h δ-h 0)/(δ-0))
  let M := concaveDeviation h (Icc 0 δ)
  let Λ := nonconvexityModulus f C δ
  have hgne : g ≠ 0 := norm_pos_iff.mp (hε.trans hg)
  have hMle : M ≤ Λ := line_deviation_endpoints f C δ ε hδ x g hx hgne hx'
  have hM : M ≠ ⊤ := ne_top_of_le_ne_top hΛ hMle
  have hσ : ε/6 < σ := by
    have hh := (prior_outcome f G δ ε hδ hε x g hg hdec).1
    dsimp [σ,h]
    linarith
  have hσ0 : 0 < σ := by linarith
  have hmreal : M.toReal ≤ Λ.toReal := ENNReal.toReal_mono hΛ hMle
  have hratio : 2*M.toReal/σ ≤ 12*Λ.toReal/ε := by
    apply (div_le_div_iff₀ hσ0 hε).mpr
    nlinarith [mul_nonneg (show 0 ≤ Λ.toReal from ENNReal.toReal_nonneg) (sub_nonneg.mpr hσ.le),
      mul_nonneg hε.le (sub_nonneg.mpr hmreal)]
  have hfloor : 1+⌊2*M.toReal/σ⌋₊ ≤ 1+⌊12*Λ.toReal/ε⌋₊ := Nat.add_le_add_left (Nat.floor_le_floor hratio) 1
  have ht := prior_termination h (lsDeriv G δ ε x g) 0 δ hδ
    (line_right_derivative_path f G C hG δ ε hδ x g hgne (line_path_convex δ hδ C hC x g hx hx')) hM hσ0
  intro hno
  apply ht
  intro j hj
  exact hno j (lt_of_lt_of_le hj hfloor)
end Queelius.OracleComplexity

open NonconvexCost.Complexity in
theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (C : Set X) (hC : Convex ℝ C) (f : X → ℝ)
    (G : X → X → X) (hG : IsDirSubgradMapOn f G C)
    (hΛ : nonconvexityModulus f C δ ≠ ⊤) (x g : X) (hx : x ∈ C)
    (hx' : lsPoint δ x g 0 ∈ C) (hg : ε < ‖g‖)
    (hdec : f x-f (lsPoint δ x g 0) < δ*ε/3) :
    IsRightDerivOn (lsFun f δ ε x g) (lsDeriv G δ ε x g) 0 δ ∧
      ¬ NoStopWithin (lsFun f δ ε x g) (lsDeriv G δ ε x g) 0 δ
        (1+⌊12*(nonconvexityModulus f C δ).toReal/ε⌋₊) := by
  have hgne : g ≠ 0 := norm_pos_iff.mp (hε.trans hg)
  exact ⟨Queelius.OracleComplexity.line_right_derivative_path f G C hG δ ε hδ x g hgne
    (Queelius.OracleComplexity.line_path_convex δ hδ C hC x g hx hx'),
    Queelius.OracleComplexity.uniform_line_endpoints f G C hC hG δ ε hδ hε x g hx hg hx' hdec hΛ⟩
