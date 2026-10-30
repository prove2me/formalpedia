-- Prove2me | solution 1 for NonconvexCost.Complexity.thm_4_3_reduction_count
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T10:00:54.748995+00:00
-- url     : https://prove2.me/submissions/f86f6584-b141-4be1-a200-1a4bf19e018d

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
 theorem _root_.solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
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
