-- Prove2me | solution 1 for InfFisher.Linear.S_eq_cone_inter_T
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T09:56:06.81669+00:00
-- url     : https://prove2.me/submissions/319f51d6-9e31-4348-80de-d8915e632c25

import Mathlib
import Definitions.Def_InfFisher_Linear_Setting
set_option autoImplicit false
set_option maxRecDepth 4096
namespace FisherResearch
noncomputable def F (d x : ℝ) := (1-d)*x^2+d*x
lemma strictF {d : ℝ} (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    StrictMonoOn (F d) (Set.Icc (0:ℝ) 1) := by
  intro a ha b hb hab
  have hab0 : 0 < a+b := by linarith [ha.1]
  have hab2 : a+b < 2 := by linarith [hb.2]
  have hp : 0 < (1-d)*(a+b)+d := by
    have h1 := mul_nonneg hd0 (show 0 ≤ 2-(a+b) by linarith)
    have h2 := mul_nonneg (sub_nonneg.mpr hd2) (le_of_lt hab0)
    by_cases h : d = 0
    · subst d; nlinarith
    · have := mul_pos (lt_of_le_of_ne hd0 (Ne.symm h)) (show 0 < 2-(a+b) by linarith)
      nlinarith
  have := mul_pos (sub_pos.mpr hab) hp
  dsimp [F]
  nlinarith
lemma existsF {d z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) :
    ∃ b ∈ Set.Icc (0:ℝ) 1, F d b = z := by
  have hc : Continuous (F d) := by unfold F; fun_prop
  have h := intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num) hc.continuousOn
  have hz' : z ∈ Set.Icc (F d 0) (F d 1) := by simpa [F] using hz
  exact h hz'
lemma coneMix {b z θ : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1)
    (ht : θ ∈ Set.Icc (0:ℝ) 1) :
    ((1-θ)*b+θ*z)^2 ≤ (1-θ)*b^2+θ*z := by
  have hzsq : 0 ≤ z-z^2 := by nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
  have h1 := mul_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) ht.1) (sq_nonneg (b-z))
  have h2 := mul_nonneg ht.1 hzsq
  nlinarith
lemma region (d e : ℝ) (he0 : 0 ≤ e) (hed : e ≤ d) (hd2 : d ≤ 2)
    (z y : ℝ) (hz : z ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hyz : y ≤ z) :
    (∃ a ∈ Set.Icc (0:ℝ) 1, z ≤ F d a ∧ F e a ≤ y) ↔
    ∃ s t : ℝ, s^2 ≤ t ∧ z=d*s+(1-d)*t ∧ y=e*s+(1-e)*t := by
  have hd0 : 0 ≤ d := le_trans he0 hed
  have he2 : e ≤ 2 := le_trans hed hd2
  obtain ⟨b,hb,hbz⟩ := existsF (d:=d) hz
  constructor
  · rintro ⟨a,ha,hza,hay⟩
    have hba : b ≤ a := by
      by_contra h
      have := strictF hd0 hd2 ha hb (lt_of_not_ge h)
      linarith
    have hby : F e b ≤ y := le_trans ((strictF he0 he2).monotoneOn hb ha hba) hay
    have hc : Continuous (fun θ : ℝ => (1-θ)*F e b+θ*z) := by fun_prop
    obtain ⟨θ,hθ,hθy⟩ := intermediate_value_Icc (show (0:ℝ)≤1 by norm_num)
      hc.continuousOn (show y ∈ Set.Icc ((1-0)*F e b+0*z) ((1-1)*F e b+1*z) by
        simpa using And.intro hby hyz)
    refine ⟨(1-θ)*b+θ*z, (1-θ)*b^2+θ*z, coneMix hz hθ, ?_, ?_⟩
    · dsimp [F] at hbz
      nlinarith [congrArg (fun x : ℝ => θ*x) hbz]
    · dsimp [F] at hθy
      nlinarith
  · rintro ⟨s,t,hst,hzst,hyst⟩
    refine ⟨b,hb,le_of_eq hbz.symm,?_⟩
    by_cases hde : d = e
    · subst e
      have : z=y := by linarith
      linarith
    have hD : 0 < d-e := sub_pos.mpr (lt_of_le_of_ne hed (Ne.symm hde))
    have hdpos : 0 < d := by linarith
    have hK : 0 ≤ d+2*(1-d)*b := by
      nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hb.2), mul_nonneg (sub_nonneg.mpr hd2) hb.1]
    by_contra h
    have hh : y-F e b < 0 := sub_neg.mpr (lt_of_not_ge h)
    have hlin : (d-e)*(t-b^2)=d*(y-F e b) := by
      dsimp [F] at *
      nlinarith [congrArg (fun x : ℝ => e*x) hzst, congrArg (fun x : ℝ => d*x) hyst,
        congrArg (fun x : ℝ => e*x) hbz]
    have hquad : (d-e)*(t-2*b*s+b^2) = (d+2*(1-d)*b)*(y-F e b) := by
      dsimp [F] at *
      nlinarith [congrArg (fun x : ℝ => (2*b)*x) (show (d-e)*(s-b)=-(1-d)*(y-((1-e)*b^2+e*b)) by
        nlinarith [congrArg (fun x : ℝ => (1-e)*x) hzst, congrArg (fun x : ℝ => (1-d)*x) hyst,
          congrArg (fun x : ℝ => (1-e)*x) hbz])]
    have hhK := mul_nonpos_of_nonneg_of_nonpos hK (le_of_lt hh)
    have hzero : s=b := by
      have hn : t-2*b*s+b^2 ≤ 0 := by nlinarith
      nlinarith [sq_nonneg (s-b)]
    subst s
    have := mul_neg_of_pos_of_neg hdpos hh
    nlinarith [mul_nonneg (le_of_lt hD) (sub_nonneg.mpr hst)]
end FisherResearch
namespace FisherResearch
lemma cone_section (c₁ d₁ c₂ d₂ : ℝ)
    (h₁ : c₁ / 2 + d₁ = 1) (h₂ : c₂ / 2 + d₂ = 1)
    (hd : d₂ ≤ d₁) (hd₁ : d₁ ≤ 2) (hd₂ : 0 ≤ d₂) :
    {q : ℝ × ℝ | ∃ a ∈ Set.Icc (0 : ℝ) 1,
      q.1 ≤ c₁ / 2 * a ^ 2 + d₁ * a ∧
      q.2 ≤ -(c₂ / 2) * a ^ 2 - d₂ * a ∧
      q.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      q.2 ∈ Set.Icc (-1 : ℝ) 0 ∧ 0 ≤ q.1 + q.2} =
    {q : ℝ × ℝ |
      q.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      q.2 ∈ Set.Icc (-1 : ℝ) 0 ∧ 0 ≤ q.1 + q.2 ∧
      ∃ s t : ℝ, s ^ 2 ≤ t ∧
        q = (d₁ * s + c₁ / 2 * t, -d₂ * s - c₂ / 2 * t)} := by
  have hc1 : c₁/2=1-d₁ := by linarith
  have hc2 : c₂/2=1-d₂ := by linarith
  ext q
  constructor
  · rintro ⟨a,ha,hza,haw,hz,hw,hzw⟩
    have hy : -q.2 ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith [hw.1,hw.2]
    have hyz : -q.2 ≤ q.1 := by linarith
    have ha' : q.1 ≤ F d₁ a ∧ F d₂ a ≤ -q.2 := by
      dsimp [F]; rw [hc1] at hza; rw [hc2] at haw; constructor <;> linarith
    obtain ⟨s,t,hst,hs,ht⟩ := (region d₁ d₂ hd₂ hd hd₁ q.1 (-q.2) hz hy hyz).mp ⟨a,ha,ha'⟩
    refine ⟨hz,hw,hzw,s,t,hst,?_⟩
    ext <;> simp only [Prod.fst,Prod.snd,hc1,hc2] <;> linarith
  · rintro ⟨hz,hw,hzw,s,t,hst,hq⟩
    have hy : -q.2 ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith [hw.1,hw.2]
    have hyz : -q.2 ≤ q.1 := by linarith
    have hs : q.1=d₁*s+(1-d₁)*t := by rw [hq]; simp [hc1]
    have ht : -q.2=d₂*s+(1-d₂)*t := by rw [hq]; simp only [Prod.snd]; rw [hc2]; ring
    obtain ⟨a,ha,hza,haw⟩ := (region d₁ d₂ hd₂ hd hd₁ q.1 (-q.2) hz hy hyz).mpr ⟨s,t,hst,hs,ht⟩
    refine ⟨a,ha,?_,?_,hz,hw,hzw⟩
    · simpa [F,hc1] using hza
    · dsimp [F] at haw; rw [hc2]; linarith
end FisherResearch


/-- Gao–Kroer, proof of Theorem 4, (A.8): the two-buyer region is a transformed parabolic cone cut by `T`. -/
theorem solution (c₁ d₁ c₂ d₂ : ℝ)
    (h₁ : c₁ / 2 + d₁ = 1) (h₂ : c₂ / 2 + d₂ = 1)
    (hd : d₂ ≤ d₁) (hd₁ : d₁ ≤ 2) (hd₂ : 0 ≤ d₂) :
    {q : ℝ × ℝ | ∃ a ∈ Set.Icc (0 : ℝ) 1,
      q.1 ≤ c₁ / 2 * a ^ 2 + d₁ * a ∧
      q.2 ≤ -(c₂ / 2) * a ^ 2 - d₂ * a ∧
      q.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      q.2 ∈ Set.Icc (-1 : ℝ) 0 ∧ 0 ≤ q.1 + q.2} =
    {q : ℝ × ℝ |
      q.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      q.2 ∈ Set.Icc (-1 : ℝ) 0 ∧ 0 ≤ q.1 + q.2 ∧
      ∃ s t : ℝ, s ^ 2 ≤ t ∧
        q = (d₁ * s + c₁ / 2 * t, -d₂ * s - c₂ / 2 * t)} := by exact FisherResearch.cone_section c₁ d₁ c₂ d₂ h₁ h₂ hd hd₁ hd₂


#print axioms solution
