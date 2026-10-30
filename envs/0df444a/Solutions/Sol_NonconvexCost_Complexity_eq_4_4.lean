-- Prove2me | solution 1 for NonconvexCost.Complexity.eq_4_4
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T12:18:38.324584+00:00
-- url     : https://prove2.me/submissions/7eb0e62b-2a84-49bf-8fc3-a79b01f2d90b

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
theorem _root_.solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
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
