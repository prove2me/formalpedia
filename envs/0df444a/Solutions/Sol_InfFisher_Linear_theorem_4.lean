-- Prove2me | solution 1 for InfFisher.Linear.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T11:22:39.593748+00:00
-- url     : https://prove2.me/submissions/e3ea3541-8606-47c5-af2c-34153f61e475

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
namespace FisherResearch
open InfFisher.Linear
lemma F_mem {d a : ℝ} (hd0 : 0 ≤ d) (hd2 : d ≤ 2) (ha : a ∈ Set.Icc (0:ℝ) 1) :
    F d a ∈ Set.Icc (0:ℝ) 1 := by
  have hm := (strictF hd0 hd2).monotoneOn
  constructor
  · simpa [F] using hm (show (0:ℝ)∈Set.Icc 0 1 by norm_num) ha ha.1
  · simpa [F] using hm ha (show (1:ℝ)∈Set.Icc 0 1 by norm_num) ha.2
lemma breakpoints_conic {n : ℕ} (hn : 2 ≤ n) (c d : ℕ → ℝ)
    (hnorm : ∀ i < n, c i / 2 + d i = 1)
    (hd : ∀ i j, i ≤ j → j < n → d j ≤ d i)
    (hd2 : d 0 ≤ 2) (hd0 : 0 ≤ d (n-1)) (u : Fin n → ℝ) :
    ((∀ i, 0 ≤ u i) ∧ ∃ a : ℕ → ℝ, a 0=0 ∧ a n=1 ∧
      (∀ k, 1 ≤ k → k < n → a k ∈ Set.Icc (0:ℝ) 1) ∧
      ∀ i : Fin n, u i ≤ c i.val/2*(a (i.val+1)^2-a i.val^2)+d i.val*(a (i.val+1)-a i.val)) ↔
      conicRep n c d u := by
  have hdlo : ∀ k < n, 0 ≤ d k := by
    intro k hk
    exact le_trans hd0 (hd k (n-1) (by omega) (by omega))
  have hdhi : ∀ k < n, d k ≤ 2 := by
    intro k hk
    exact le_trans (hd 0 k (Nat.zero_le _) hk) hd2
  have hc : ∀ k < n, c k/2=1-d k := by intro k hk; linarith [hnorm k hk]
  constructor
  · rintro ⟨hu,a,ha0,han,ha,hub⟩
    let z : ℕ → ℝ := fun k => F (d k) (a (k+1))
    let w : ℕ → ℝ := fun k => -F (d (k+1)) (a (k+1))
    refine ⟨hu,z,w,(fun k=>a (k+1)),(fun k=>a (k+1)^2),?_,?_,?_,?_⟩
    · intro i hi
      have h := hub i
      have hc0 := hc 0 (by omega)
      dsimp [z,F]; rw [hi,ha0] at h
      simpa [hc0] using h
    · intro i hi hil
      have h := hub i
      have he : i.val-1+1=i.val := by omega
      dsimp [z,w,F]; rw [he]
      rw [hc i.val i.isLt] at h
      nlinarith
    · intro i hi
      have h := hub i
      have he : i.val+1=n := by omega
      have he' : n-2+1=i.val := by omega
      dsimp [w,F]; rw [he']
      rw [he,han,hc i.val i.isLt] at h
      nlinarith
    · intro k hk
      have hk' : k<n := by omega
      have hk1 : k+1<n := by omega
      have ha' := ha (k+1) (by omega) hk1
      have hz := F_mem (hdlo k hk') (hdhi k hk') ha'
      have hw := F_mem (hdlo (k+1) hk1) (hdhi (k+1) hk1) ha'
      refine ⟨?_,by change a (k+1)^2 ≤ a (k+1)^2; exact le_rfl,hz,?_,?_⟩
      · dsimp [Gmap,z,w,F]; rw [hc k hk',hc (k+1) hk1]; ext <;> ring
      · dsimp [w]; constructor <;> linarith [hw.1,hw.2]
      · have hprod := mul_nonneg (sub_nonneg.mpr (hd k (k+1) (by omega) hk1))
          (show 0 ≤ a (k+1)-a (k+1)^2 by nlinarith [mul_nonneg ha'.1 (sub_nonneg.mpr ha'.2)])
        dsimp [z,w,F]; nlinarith
  · rintro ⟨hu,z,w,s,t,hfirst,hmid,hlast,hpair⟩
    have hex : ∀ k < n-1, ∃ b ∈ Set.Icc (0:ℝ) 1,
        z k ≤ F (d k) b ∧ F (d (k+1)) b ≤ -w k := by
      intro k hk
      obtain ⟨hg,hst,hz,hw,hzw⟩ := hpair k hk
      apply (region (d k) (d (k+1)) (hdlo _ (by omega))
        (hd k (k+1) (by omega) (by omega)) (hdhi _ (by omega)) (z k) (-w k)
        hz (by constructor <;> linarith [hw.1,hw.2]) (by linarith)).mpr
      have hg1 := congrArg Prod.fst hg
      have hg2 := congrArg Prod.snd hg
      dsimp [Gmap] at hg1 hg2
      rw [hc k (by omega)] at hg1
      rw [hc (k+1) (by omega)] at hg2
      exact ⟨s k,t k,hst,hg1.symm,by linarith⟩
    classical
    let b : ℕ → ℝ := fun k => if hk : k<n-1 then (hex k hk).choose else 0
    have hb : ∀ k < n-1, b k ∈ Set.Icc (0:ℝ) 1 ∧
        z k ≤ F (d k) (b k) ∧ F (d (k+1)) (b k) ≤ -w k := by
      intro k hk
      simpa [b,hk] using (hex k hk).choose_spec
    let a : ℕ → ℝ := fun k => if k=0 then 0 else if k=n then 1 else b (k-1)
    have ha0 : a 0=0 := by simp [a]
    have han : a n=1 := by simp [a,show n≠0 by omega]
    have ha : ∀ k, 1 ≤ k → k<n → a k=b (k-1) := by
      intro k hk hkn; simp [a,show k≠0 by omega,show k≠n by omega]
    refine ⟨hu,a,ha0,han,?_,?_⟩
    · intro k hk hkn; rw [ha k hk hkn]; exact (hb (k-1) (by omega)).1
    · intro i
      rw [hc i.val i.isLt]
      by_cases hi0 : i.val=0
      · have h := hfirst i hi0
        have hb0 := (hb 0 (by omega)).2.1
        rw [hi0,ha0,ha 1 (by omega) (by omega)]
        dsimp [F] at hb0; norm_num at *; linarith
      · by_cases hin : i.val=n-1
        · have h := hlast i hin
          have hbn := (hb (n-2) (by omega)).2.2
          have hnext : i.val+1=n := by omega
          have hprev : i.val-1=n-2 := by omega
          have hidx : n-2+1=i.val := by omega
          rw [hnext,han,ha i.val (by omega) i.isLt,hprev]
          rw [hidx] at hbn; dsimp [F] at hbn; nlinarith
        · have h := hmid i (by omega) (by omega)
          have hbcur := (hb i.val (by omega)).2.1
          have hbprev := (hb (i.val-1) (by omega)).2.2
          have he : i.val-1+1=i.val := by omega
          rw [he] at hbprev
          rw [ha (i.val+1) (by omega) (by omega),ha i.val (by omega) i.isLt]
          simp only [Nat.add_sub_cancel]
          dsimp [F] at hbcur hbprev
          nlinarith
end FisherResearch

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory
namespace FisherResearch
lemma downward_closed {α : Type*} [MeasurableSpace α] (μ : Measure α) {n : ℕ}
    (v : Fin n → α → ℝ) (u w : Fin n → ℝ)
    (hw : w ∈ InfFisher.Linear.feasUtil μ v) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ w i) :
    u ∈ InfFisher.Linear.feasUtil μ v := by
  obtain ⟨x,hx,hw⟩ := hw
  let r : Fin n → ℝ := fun i => u i / w i
  have hr (i : Fin n) : 0 ≤ r i ∧ r i ≤ 1 := by
    have hw0 : 0 ≤ w i := (hu i).1.trans (hu i).2
    constructor
    · exact div_nonneg (hu i).1 hw0
    · by_cases h : w i = 0
      · simp [r,h]
      · exact (div_le_one₀ (lt_of_le_of_ne hw0 (Ne.symm h))).mpr (hu i).2
  refine ⟨fun i θ => r i*x i θ, ⟨?_,?_⟩, ?_⟩
  · intro i
    refine ⟨(hx.1 i).1.const_mul (r i), ?_⟩
    filter_upwards [(hx.1 i).2] with θ hθ
    exact mul_nonneg (hr i).1 hθ
  · filter_upwards [hx.2, ae_all_iff.mpr (fun i => (hx.1 i).2)] with θ hsum hnonneg
    calc
      ∑ i, r i*x i θ ≤ ∑ i, x i θ := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_of_le_one_left (hnonneg i) (hr i).2
      _ ≤ 1 := hsum
  · intro i
    have hmul : r i*w i=u i := by
      by_cases h : w i=0
      · have : u i=0 := le_antisymm (by simpa [h] using (hu i).2) (hu i).1
        simp [r,h,this]
      · exact div_mul_cancel₀ _ h
    change u i = ∫ θ, v i θ * (r i * x i θ) ∂μ
    calc
      u i = r i * InfFisher.Linear.pair μ (v i) (x i) := by rw [← hw i,hmul]
      _ = ∫ θ, v i θ * (r i*x i θ) ∂μ := by
        rw [InfFisher.Linear.pair, ← integral_const_mul]
        congr 1
        funext θ
        ring

lemma chain {n : ℕ} (a : ℕ → ℝ) (ha : ∀ k<n,a k≤a (k+1))
    {i j : ℕ} (hij : i≤j) (hj : j≤n) : a i≤a j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hle ih => exact (ih (by omega)).trans (ha j (by omega))

lemma interval_allocation {n : ℕ} (a : ℕ → ℝ)
    (ha : ∀ k<n,a k≤a (k+1)) (μ : Measure ℝ) :
    InfFisher.Linear.IsAllocation μ
      (fun i : Fin n => (Set.Ioc (a i.val) (a (i.val+1))).indicator (fun _ => (1:ℝ))) := by
  classical
  let x : Fin n → ℝ → ℝ := fun i => (Set.Ioc (a i.val) (a (i.val+1))).indicator (fun _ => (1:ℝ))
  have hdis (i j : Fin n) (θ : ℝ) (hi : θ∈Set.Ioc (a i.val) (a (i.val+1)))
      (hj : θ∈Set.Ioc (a j.val) (a (j.val+1))) : i=j := by
    apply Fin.ext
    by_contra h
    rcases lt_or_gt_of_ne h with hlt|hgt
    · have := chain a ha (show i.val + 1 ≤ j.val by omega) (Nat.le_of_lt j.isLt)
      exact (not_lt_of_ge (hi.2.trans this)) hj.1
    · have := chain a ha (show j.val + 1 ≤ i.val by omega) (Nat.le_of_lt i.isLt)
      exact (not_lt_of_ge (hj.2.trans this)) hi.1
  constructor
  · intro i
    refine ⟨(memLp_top_const (1:ℝ)).indicator measurableSet_Ioc, ?_⟩
    exact Filter.Eventually.of_forall (fun θ => Set.indicator_nonneg (fun _ _ => by norm_num) θ)
  · apply Filter.Eventually.of_forall
    intro θ
    by_cases h : ∃ i : Fin n, θ∈Set.Ioc (a i.val) (a (i.val+1))
    · obtain ⟨i,hi⟩ := h
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro j hj hji
        have hnot : θ∉Set.Ioc (a j.val) (a (j.val+1)) := fun hj => hji (hdis j i θ hj hi)
        simp [hnot]
      · simp
    · have hnot (i : Fin n) : θ∉Set.Ioc (a i.val) (a (i.val+1)) := fun hi => h ⟨i,hi⟩
      simp [hnot]
lemma interval_pair (c d l h : ℝ) (hl : 0 ≤ l) (hh : h ≤ 1) (hlh : l ≤ h) :
    InfFisher.Linear.pair (volume.restrict (Set.Icc (0:ℝ) 1))
      (fun θ => c*θ+d) ((Set.Ioc l h).indicator (fun _ => (1:ℝ))) =
      c/2*(h^2-l^2)+d*(h-l) := by
  unfold InfFisher.Linear.pair
  have heq : (fun θ => (c*θ+d)*(Set.Ioc l h).indicator (fun _ => (1:ℝ)) θ) =
      (Set.Ioc l h).indicator (fun θ => c*θ+d) := by
    funext θ
    by_cases hθ : θ∈Set.Ioc l h <;> simp [hθ]
  rw [heq,integral_indicator measurableSet_Ioc]
  have hsub : Set.Ioc l h ⊆ Set.Icc (0:ℝ) 1 := fun θ hθ => ⟨hl.trans hθ.1.le,hθ.2.trans hh⟩
  rw [Measure.restrict_restrict_of_subset hsub, ← intervalIntegral.integral_of_le hlh]
  have hf : IntervalIntegrable (fun x:ℝ => c*x) volume l h :=
    (show Continuous (fun x:ℝ => c*x) by fun_prop).intervalIntegrable l h
  have hg : IntervalIntegrable (fun _:ℝ => d) volume l h := continuous_const.intervalIntegrable l h
  rw [intervalIntegral.integral_add hf hg,
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring
end FisherResearch
namespace FisherResearch
open InfFisher.Linear
lemma breakpoints_feasible {n : ℕ} (hn : 0 < n) (c d : ℕ → ℝ)
    (hnorm : ∀ i < n, c i / 2 + d i = 1)
    (hd : ∀ i j, i ≤ j → j < n → d j ≤ d i)
    (hd2 : d 0 ≤ 2) (hd0 : 0 ≤ d (n-1)) (u : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) (a : ℕ → ℝ) (ha0 : a 0=0) (han : a n=1)
    (ha : ∀ k, 1 ≤ k → k < n → a k ∈ Set.Icc (0:ℝ) 1)
    (hub : ∀ i : Fin n, u i ≤ c i.val/2*(a (i.val+1)^2-a i.val^2)+d i.val*(a (i.val+1)-a i.val)) :
    u ∈ feasUtil (volume.restrict (Set.Icc (0:ℝ) 1)) (linVal c d n) := by
  have hdlo : ∀ k < n, 0 ≤ d k := by
    intro k hk
    exact le_trans hd0 (hd k (n-1) (by omega) (by omega))
  have hdhi : ∀ k < n, d k ≤ 2 := by
    intro k hk
    exact le_trans (hd 0 k (Nat.zero_le _) hk) hd2
  have hc : ∀ k < n, c k/2=1-d k := by intro k hk; linarith [hnorm k hk]
  have hb (k : ℕ) (hk : k≤n) : a k∈Set.Icc (0:ℝ) 1 := by
    by_cases h0 : k=0
    · simp [h0,ha0]
    by_cases he : k=n
    · simp [he,han]
    exact ha k (by omega) (by omega)
  have hstep (k : ℕ) (hk : k<n) : a k ≤ a (k+1) := by
    have hui := hub ⟨k,hk⟩
    have hu0 := hu ⟨k,hk⟩
    simp only [Fin.val_mk,hc k hk] at hui
    by_contra h
    have hlt := strictF (hdlo k hk) (hdhi k hk) (hb (k+1) (by omega)) (hb k (by omega)) (lt_of_not_ge h)
    dsimp [F] at hlt
    nlinarith
  let μ := volume.restrict (Set.Icc (0:ℝ) 1)
  let x : Fin n → ℝ → ℝ := fun i => (Set.Ioc (a i.val) (a (i.val+1))).indicator (fun _ => (1:ℝ))
  let w : Fin n → ℝ := fun i => pair μ (linVal c d n i) (x i)
  have hw : w∈feasUtil μ (linVal c d n) := ⟨x,interval_allocation a hstep μ,fun _ => rfl⟩
  apply downward_closed μ (linVal c d n) u w hw
  intro i
  refine ⟨hu i,?_⟩
  have hi := interval_pair (c i.val) (d i.val) (a i.val) (a (i.val+1))
    (hb i.val (by omega)).1 (hb (i.val+1) (by omega)).2 (hstep i.val i.isLt)
  change u i ≤ pair μ (fun θ => c i.val*θ+d i.val) (x i)
  rw [hi]
  exact hub i
end FisherResearch
namespace FisherResearch
open InfFisher.Linear MeasureTheory
lemma linear_integral (c d l h : ℝ) (hlh : l ≤ h) :
    (∫ θ in Set.Icc l h, c*θ+d) = c/2*(h^2-l^2)+d*(h-l) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlh]
  have hf : IntervalIntegrable (fun x:ℝ => c*x) volume l h :=
    (show Continuous (fun x:ℝ => c*x) by fun_prop).intervalIntegrable l h
  have hg : IntervalIntegrable (fun _:ℝ => d) volume l h := continuous_const.intervalIntegrable l h
  rw [intervalIntegral.integral_add hf hg,intervalIntegral.integral_const_mul,
    integral_id,intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

lemma feasible_nonneg {n : ℕ} (hn : 0<n) (c d : ℕ → ℝ)
    (hnorm : ∀ i<n,c i/2+d i=1)
    (hd : ∀ i j,i≤j → j<n → d j≤d i)
    (hd2 : d 0≤2) (hd0 : 0≤d (n-1)) (u : Fin n → ℝ)
    (hu : u∈feasUtil (volume.restrict (Set.Icc (0:ℝ) 1)) (linVal c d n)) :
    ∀ i,0≤u i := by
  obtain ⟨x,hx,hui⟩ := hu
  intro i
  have hdlo : 0≤d i.val := hd0.trans (hd i.val (n-1) (by omega) (by omega))
  have hdhi : d i.val≤2 := (hd 0 i.val (Nat.zero_le _) i.isLt).trans hd2
  have hc : c i.val=2*(1-d i.val) := by linarith [hnorm i.val i.isLt]
  rw [hui i]
  apply integral_nonneg_of_ae
  filter_upwards [(hx.1 i).2, ae_restrict_mem measurableSet_Icc] with θ hxθ hθ
  apply mul_nonneg _ hxθ
  change 0≤c i.val*θ+d i.val
  rw [hc]
  have h1 := mul_nonneg (sub_nonneg.mpr hdhi) hθ.1
  have h2 := mul_nonneg hdlo (sub_nonneg.mpr hθ.2)
  nlinarith only [h1,h2]

lemma conic_feasible {n : ℕ} (hn : 2≤n) (c d : ℕ → ℝ)
    (hnorm : ∀ i<n,c i/2+d i=1)
    (hd : ∀ i j,i≤j → j<n → d j≤d i)
    (hd2 : d 0≤2) (hd0 : 0≤d (n-1)) (u : Fin n → ℝ)
    (hu : conicRep n c d u) :
    u∈feasUtil (volume.restrict (Set.Icc (0:ℝ) 1)) (linVal c d n) := by
  obtain ⟨hu0,a,ha0,han,ha,hub⟩ := (breakpoints_conic hn c d hnorm hd hd2 hd0 u).mpr hu
  exact breakpoints_feasible (by omega) c d hnorm hd hd2 hd0 u hu0 a ha0 han ha hub

lemma full_conic_of_interval_dominance {n : ℕ} (hn : 2≤n) (c d : ℕ → ℝ)
    (hnorm : ∀ i<n,c i/2+d i=1)
    (hd : ∀ i j,i≤j → j<n → d j≤d i)
    (hd2 : d 0≤2) (hd0 : 0≤d (n-1))
    (hdom : ∀ u∈feasUtil (volume.restrict (Set.Icc (0:ℝ) 1)) (linVal c d n),
      ∃ a : ℕ → ℝ, a 0=0 ∧ (∀ k<n,a k≤a (k+1)) ∧ a n=1 ∧
        ∀ i : Fin n,u i≤∫ θ in Set.Icc (a i.val) (a (i.val+1)), c i.val*θ+d i.val) :
    ∀ u : Fin n → ℝ,
      u∈feasUtil (volume.restrict (Set.Icc (0:ℝ) 1)) (linVal c d n) ↔ conicRep n c d u := by
  intro u
  constructor
  · intro hu
    obtain ⟨a,ha0,hstep,han,hub⟩ := hdom u hu
    apply (breakpoints_conic hn c d hnorm hd hd2 hd0 u).mp
    refine ⟨feasible_nonneg (by omega) c d hnorm hd hd2 hd0 u hu,a,ha0,han,?_,?_⟩
    · intro k hk hkn
      constructor
      · simpa [ha0] using chain a hstep (Nat.zero_le k) (Nat.le_of_lt hkn)
      · simpa [han] using chain a hstep (Nat.le_of_lt hkn) (le_refl n)
    · intro i
      simpa only [linear_integral _ _ _ _ (hstep i.val i.isLt)] using hub i
  · exact conic_feasible hn c d hnorm hd hd2 hd0 u
end FisherResearch

set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory
namespace FisherResearch
lemma welfare_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) {n : ℕ}
    (v x : Fin n → α → ℝ) (β : Fin n → ℝ) (p : α → ℝ)
    (hv : ∀ i,Integrable (v i) μ) (hx : InfFisher.Linear.IsAllocation μ x)
    (hp : Integrable p μ) (hp0 : 0 ≤ᵐ[μ] p)
    (hdom : ∀ i,(fun θ => β i*v i θ) ≤ᵐ[μ] p) :
    ∑ i,β i*InfFisher.Linear.pair μ (v i) (x i) ≤ ∫ θ,p θ ∂μ := by
  have hint (i : Fin n) : Integrable (fun θ => β i*(v i θ*x i θ)) μ :=
    ((memLp_one_iff_integrable.mpr (hv i)).integrable_mul (hx.1 i).1).const_mul (β i)
  calc
    ∑ i,β i*InfFisher.Linear.pair μ (v i) (x i) =
        ∫ θ,∑ i,β i*(v i θ*x i θ) ∂μ := by
      rw [integral_finsetSum _ (fun i _ => hint i)]
      apply Finset.sum_congr rfl
      intro i hi
      exact (integral_const_mul _ _).symm
    _ ≤ ∫ θ,p θ ∂μ := by
      apply integral_mono_ae (integrable_finsetSum _ (fun i _ => hint i)) hp
      filter_upwards [hx.2,hp0,ae_all_iff.mpr (fun i => (hx.1 i).2),ae_all_iff.mpr hdom]
        with θ hs hpθ hxθ hdθ
      calc
        ∑ i,β i*(v i θ*x i θ) = ∑ i,(β i*v i θ)*x i θ := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ ∑ i,p θ*x i θ := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_right (hdθ i) (hxθ i)
        _ = p θ*(∑ i,x i θ) := (Finset.mul_sum _ _ _).symm
        _ ≤ p θ := mul_le_of_le_one_right hpθ hs
end FisherResearch

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace FisherResearch
lemma affine_crossing (c₁ d₁ c₂ d₂ b₁ b₂ a θ : ℝ)
    (hn1 : c₁/2+d₁=1) (hn2 : c₂/2+d₂=1) (hd : d₂ ≤ d₁)
    (hb : 0 ≤ b₁) (hpos : 0<c₂*a+d₂)
    (htie : b₁*(c₁*a+d₁)=b₂*(c₂*a+d₂)) :
    (θ ≤ a → b₂*(c₂*θ+d₂) ≤ b₁*(c₁*θ+d₁)) ∧
    (a ≤ θ → b₁*(c₁*θ+d₁) ≤ b₂*(c₂*θ+d₂)) := by
  have hc1 : c₁=2*(1-d₁) := by linarith
  have hc2 : c₂=2*(1-d₂) := by linarith
  have hid : (c₂*a+d₂)*(b₁*(c₁*θ+d₁)-b₂*(c₂*θ+d₂)) =
      2*b₁*(d₁-d₂)*(a-θ) := by
    calc
      _ = b₁*((c₂*a+d₂)*(c₁*θ+d₁)-(c₁*a+d₁)*(c₂*θ+d₂)) := by
        linear_combination (c₂*θ+d₂)*htie
      _ = _ := by rw [hc1,hc2];ring
  have hk : 0 ≤ 2*b₁*(d₁-d₂) := mul_nonneg (mul_nonneg (by norm_num) hb) (sub_nonneg.mpr hd)
  constructor
  · intro h
    have := mul_nonneg hk (sub_nonneg.mpr h)
    nlinarith only [hid,this,hpos]
  · intro h
    have := mul_nonpos_of_nonneg_of_nonpos hk (sub_nonpos.mpr h)
    nlinarith only [hid,this,hpos]

lemma finite_chain {n : ℕ} (a : ℕ → ℝ) (ha : ∀ k<n,a k ≤ a (k+1))
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) : a i ≤ a j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hle ih => exact (ih (by omega)).trans (ha j (by omega))

lemma interval_winner {n : ℕ} (a c d β : ℕ → ℝ)
    (ha : ∀ k<n,a k ≤ a (k+1))
    (hnorm : ∀ k<n,c k/2+d k=1)
    (hd : ∀ k,k+1<n → d (k+1) ≤ d k)
    (hb : ∀ k<n,0 ≤ β k)
    (hpos : ∀ k,k+1<n → 0<c (k+1)*a (k+1)+d (k+1))
    (htie : ∀ k,k+1<n → β k*(c k*a (k+1)+d k)=β (k+1)*(c (k+1)*a (k+1)+d (k+1)))
    (j : ℕ) (hj : j<n) (θ : ℝ) (hθ : θ∈Set.Icc (a j) (a (j+1))) :
    ∀ i<n,β i*(c i*θ+d i) ≤ β j*(c j*θ+d j) := by
  intro i hi
  let f : ℕ → ℝ := fun k => β k*(c k*θ+d k)
  by_cases hij : i ≤ j
  · apply finite_chain (n:=j) f _ hij (le_refl j)
    intro k hk
    have hkn : k+1<n := by omega
    apply (affine_crossing (c k) (d k) (c (k+1)) (d (k+1)) (β k) (β (k+1)) (a (k+1)) θ
      (hnorm k (by omega)) (hnorm (k+1) hkn) (hd k hkn) (hb k (by omega)) (hpos k hkn) (htie k hkn)).2
    exact (finite_chain a ha (show k+1 ≤ j by omega) (Nat.le_of_lt hj)).trans hθ.1
  · have hji : j ≤ i := by omega
    have hh : ∀ m,j ≤ m → m<n → f m ≤ f j := by
      intro m hm
      induction m,hm using Nat.le_induction with
      | base => intro _;exact le_rfl
      | succ m hm ih =>
        intro hmn
        have hcross := (affine_crossing (c m) (d m) (c (m+1)) (d (m+1)) (β m) (β (m+1)) (a (m+1)) θ
          (hnorm m (by omega)) (hnorm (m+1) hmn) (hd m hmn) (hb m (by omega)) (hpos m hmn) (htie m hmn)).1
        exact (hcross (hθ.2.trans (finite_chain a ha (by omega) (by omega)))).trans (ih (by omega))
    exact hh i hji hi
lemma affine_pos (c d x : ℝ) (hn : c/2+d=1) (hd0 : 0 ≤ d) (hd2 : d ≤ 2)
    (hx : x∈Set.Ioo (0:ℝ) 1) : 0<c*x+d := by
  have hc : c=2*(1-d) := by linarith
  have h1 := mul_nonneg (sub_nonneg.mpr hd2) hx.1.le
  by_cases h : d=0
  · rw [h] at hn ⊢
    have : c=2 := by linarith
    simp only [this,mul_pos_iff_of_pos_left (show (0:ℝ)<2 by norm_num),add_zero]
    exact hx.1
  · have h2 := mul_pos (lt_of_le_of_ne hd0 (Ne.symm h)) (sub_pos.mpr hx.2)
    rw [hc]
    nlinarith only [h1,h2]

def partitionWeights (a c d : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | k+1 => partitionWeights a c d k*(c k*a (k+1)+d k)/(c (k+1)*a (k+1)+d (k+1))

lemma partition_weights {n : ℕ} (a c d : ℕ → ℝ)
    (hnorm : ∀ k<n,c k/2+d k=1) (hd : ∀ k<n,0 ≤ d k ∧ d k ≤ 2)
    (ha : ∀ k,0<k → k<n → a k∈Set.Ioo (0:ℝ) 1) :
    (∀ k<n,0<partitionWeights a c d k) ∧
    (∀ k,k+1<n → partitionWeights a c d k*(c k*a (k+1)+d k)=
      partitionWeights a c d (k+1)*(c (k+1)*a (k+1)+d (k+1))) := by
  have hpos (i k : ℕ) (hi : i<n) (hk0 : 0<k) (hkn : k<n) :
      0<c i*a k+d i := affine_pos _ _ _ (hnorm i hi) (hd i hi).1 (hd i hi).2 (ha k hk0 hkn)
  constructor
  · intro k
    induction k with
    | zero => intro _;norm_num [partitionWeights]
    | succ k ih =>
      intro hk
      exact div_pos (mul_pos (ih (by omega)) (hpos k (k+1) (by omega) (by omega) hk))
        (hpos (k+1) (k+1) hk (by omega) hk)
  · intro k hk
    simp only [partitionWeights]
    exact (div_mul_cancel₀ _ (ne_of_gt (hpos (k+1) (k+1) hk (by omega) hk))).symm
end FisherResearch

namespace FisherResearch
open MeasureTheory InfFisher.Linear
lemma interval_cover (n : ℕ) (a : ℕ → ℝ) (θ : ℝ)
    (hθ : θ∈Set.Ioc (a 0) (a n)) :
    ∃ j<n,θ∈Set.Ioc (a j) (a (j+1)) := by
  induction n with
  | zero => exact (not_lt_of_ge hθ.2 hθ.1).elim
  | succ n ih =>
    by_cases h : θ ≤ a n
    · obtain ⟨j,hj,hjθ⟩ := ih ⟨hθ.1,h⟩
      exact ⟨j,by omega,hjθ⟩
    · exact ⟨n,by omega,lt_of_not_ge h,hθ.2⟩

lemma partition_certificate {n : ℕ} (hn : 0<n) (a c d : ℕ → ℝ)
    (ha0 : a 0=0) (han : a n=1) (ha : ∀ k<n,a k ≤ a (k+1))
    (hint : ∀ k,0<k → k<n → a k∈Set.Ioo (0:ℝ) 1)
    (hnorm : ∀ k<n,c k/2+d k=1) (hd : ∀ k<n,0 ≤ d k ∧ d k ≤ 2)
    (horder : ∀ k,k+1<n → d (k+1) ≤ d k)
    (u : Fin n → ℝ)
    (hu : u∈feasUtil (volume.restrict (Set.Icc (0:ℝ) 1)) (linVal c d n)) :
    ∑ i : Fin n,partitionWeights a c d i.val*u i ≤
      ∑ i : Fin n,partitionWeights a c d i.val*
        (c i.val/2*(a (i.val+1)^2-a i.val^2)+d i.val*(a (i.val+1)-a i.val)) := by
  classical
  let μ := volume.restrict (Set.Icc (0:ℝ) 1)
  let v := linVal c d n
  let β : Fin n → ℝ := fun i => partitionWeights a c d i.val
  let y : Fin n → ℝ → ℝ := fun i => (Set.Ioc (a i.val) (a (i.val+1))).indicator (fun _ => (1:ℝ))
  let p : ℝ → ℝ := fun θ => ∑ i,β i*(v i θ*y i θ)
  have hweights := partition_weights a c d hnorm hd hint
  have hv (i : Fin n) : Integrable (v i) μ :=
    (show Continuous (fun θ:ℝ => c i.val*θ+d i.val) by fun_prop).integrableOn_Icc
  have hy := interval_allocation a ha μ
  have hpint (i : Fin n) : Integrable (fun θ => β i*(v i θ*y i θ)) μ :=
    ((memLp_one_iff_integrable.mpr (hv i)).integrable_mul (hy.1 i).1).const_mul (β i)
  have hp : Integrable p μ := integrable_finsetSum _ (fun i _ => hpint i)
  have hpos (k : ℕ) (hk : k+1<n) : 0<c (k+1)*a (k+1)+d (k+1) :=
    affine_pos _ _ _ (hnorm (k+1) hk) (hd (k+1) hk).1 (hd (k+1) hk).2 (hint (k+1) (by omega) hk)
  have hvalue (i : Fin n) (θ : ℝ) (hθ : θ∈Set.Icc (0:ℝ) 1) : 0 ≤ v i θ := by
    have hc : c i.val=2*(1-d i.val) := by linarith [hnorm i.val i.isLt]
    have h1 := mul_nonneg (sub_nonneg.mpr (hd i.val i.isLt).2) hθ.1
    have h2 := mul_nonneg (hd i.val i.isLt).1 (sub_nonneg.mpr hθ.2)
    dsimp [v,linVal]
    rw [hc]
    nlinarith only [h1,h2]
  have hwin (θ : ℝ) (hθ : θ∈Set.Ioc (0:ℝ) 1) :
      0 ≤ p θ ∧ ∀ i,β i*v i θ ≤ p θ := by
    obtain ⟨j,hj,hjθ⟩ := interval_cover n a θ (by simpa [ha0,han] using hθ)
    let j' : Fin n := ⟨j,hj⟩
    have hnot (i : Fin n) (hij : i≠j') : θ∉Set.Ioc (a i.val) (a (i.val+1)) := by
      intro hiθ
      have hne : i.val≠j := fun h => hij (Fin.ext h)
      rcases lt_or_gt_of_ne hne with hlt|hgt
      · have hm := finite_chain a ha (show i.val+1 ≤ j by omega) (Nat.le_of_lt hj)
        exact (not_lt_of_ge (hiθ.2.trans hm)) hjθ.1
      · have hm := finite_chain a ha (show j+1 ≤ i.val by omega) (Nat.le_of_lt i.isLt)
        exact (not_lt_of_ge (hjθ.2.trans hm)) hiθ.1
    have heq : p θ=β j'*v j' θ := by
      dsimp [p]
      rw [Finset.sum_eq_single j']
      · simp [y,j',hjθ]
      · intro i hi hij
        simp [y,hnot i hij]
      · simp
    rw [heq]
    constructor
    · exact mul_nonneg (hweights.1 j hj).le (hvalue j' θ ⟨hθ.1.le,hθ.2⟩)
    · intro i
      exact interval_winner a c d (partitionWeights a c d) ha hnorm horder
        (fun k hk => (hweights.1 k hk).le) hpos hweights.2 j hj θ ⟨hjθ.1.le,hjθ.2⟩ i.val i.isLt
  have hae : ∀ᵐ θ∂μ, θ∈Set.Ioc (0:ℝ) 1 := by
    have hz : ∀ᵐ θ∂μ, θ≠0 := by simp [ae_iff]
    filter_upwards [ae_restrict_mem measurableSet_Icc,hz] with θ hθ hzθ
    exact ⟨lt_of_le_of_ne hθ.1 (Ne.symm hzθ),hθ.2⟩
  have hp0 : 0 ≤ᵐ[μ] p := hae.mono (fun θ hθ => (hwin θ hθ).1)
  have hdom (i : Fin n) : (fun θ => β i*v i θ) ≤ᵐ[μ] p := hae.mono (fun θ hθ => (hwin θ hθ).2 i)
  obtain ⟨x,hx,hux⟩ := hu
  have hbound := welfare_bound μ v x β p hv hx hp hp0 hdom
  have hb (k : ℕ) (hk : k ≤ n) : a k∈Set.Icc (0:ℝ) 1 := by
    constructor
    · simpa [ha0] using finite_chain a ha (Nat.zero_le k) hk
    · simpa [han] using finite_chain a ha hk (le_refl n)
  have hprice : (∫ θ,p θ ∂μ) = ∑ i : Fin n,β i*
      (c i.val/2*(a (i.val+1)^2-a i.val^2)+d i.val*(a (i.val+1)-a i.val)) := by
    rw [show (∫ θ,p θ ∂μ) = ∑ i,∫ θ,β i*(v i θ*y i θ) ∂μ by
      exact integral_finsetSum _ (fun i _ => hpint i)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul]
    congr 1
    exact interval_pair _ _ _ _ (hb i.val (by omega)).1 (hb (i.val+1) (by omega)).2 (ha i.val i.isLt)
  rw [hprice] at hbound
  simpa only [hux] using hbound
end FisherResearch
namespace FisherResearch
open MeasureTheory InfFisher.Linear
lemma prefix_feasible {n m : ℕ} (hm : m≤n) (c d : ℕ → ℝ) (u : Fin n → ℝ)
    (hu : u∈feasUtil (volume.restrict (Set.Icc (0:ℝ) 1)) (linVal c d n)) :
    (fun i : Fin m => u (Fin.castLE hm i)) ∈
      feasUtil (volume.restrict (Set.Icc (0:ℝ) 1)) (linVal c d m) := by
  classical
  obtain ⟨x,hx,hu⟩ := hu
  refine ⟨fun i => x (Fin.castLE hm i),⟨fun i => hx.1 _,?_⟩,fun i => hu _⟩
  filter_upwards [hx.2,ae_all_iff.mpr (fun i => (hx.1 i).2)] with θ hs hx0
  apply le_trans _ hs
  rw [←Finset.sum_image (f:=fun i : Fin n => x i θ) (s:=Finset.univ) (fun i _ j _ h => Fin.castLE_injective hm h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hx0 i)

lemma greedy_step {n : ℕ} (c d u a : ℕ → ℝ) (σ : ℝ)
    (hσ0 : 0<σ) (hσ1 : σ<1)
    (hnorm : ∀ i<n,c i/2+d i=1) (hd : ∀ i<n,0≤d i ∧ d i≤2)
    (horder : ∀ i,i+1<n → d (i+1)≤d i)
    (hu : (fun i : Fin n => u i.val/σ)∈feasUtil (volume.restrict (Set.Icc (0:ℝ) 1)) (linVal c d n))
    (hupos : ∀ i<n,0<u i) (k : ℕ) (hk : k<n)
    (ha0 : a 0=0) (ha : ∀ i<k,a i≤a (i+1))
    (hint : ∀ i, 0 < i → i ≤ k → a i∈Set.Ioo (0:ℝ) 1)
    (hmatch : ∀ i<k,u i=c i/2*(a (i+1)^2-a i^2)+d i*(a (i+1)-a i)) :
    ∃ b∈Set.Ioo (a k) 1,u k=c k/2*(b^2-a k^2)+d k*(b-a k) := by
  classical
  let A : ℕ → ℝ := fun i => if i=k+1 then 1 else a i
  have hA0 : A 0=0 := by simp [A,ha0]
  have hAk : A k=a k := by simp [A]
  have hAend : A (k+1)=1 := by simp [A]
  have hak0 : 0≤a k := by
    by_cases h : k=0
    · simp [h,ha0]
    · exact (hint k (by omega) le_rfl).1.le
  have hak1 : a k<1 := by
    by_cases h : k=0
    · simp [h,ha0]
    · exact (hint k (by omega) le_rfl).2
  have hAi (i : ℕ) (hi : i≤k) : A i=a i := by simp [A,show i≠k+1 by omega]
  have hA : ∀ i<k+1,A i≤A (i+1) := by
    intro i hi
    by_cases h : i=k
    · simpa [h,hAk,hAend] using hak1.le
    · rw [hAi i (by omega),hAi (i+1) (by omega)]
      exact ha i (by omega)
  have hAiint : ∀ i, 0 < i → i < k+1 → A i∈Set.Ioo (0:ℝ) 1 := by
    intro i hi hj
    rw [hAi i (by omega)]
    exact hint i hi (by omega)
  have hnorm' : ∀ i<k+1,c i/2+d i=1 := fun i hi => hnorm i (by omega)
  have hd' : ∀ i<k+1,0≤d i ∧ d i≤2 := fun i hi => hd i (by omega)
  have hb := partition_weights A c d hnorm' hd' hAiint
  let β := partitionWeights A c d
  have hbound := partition_certificate (n:=k+1) (by omega) A c d hA0 hAend hA hAiint hnorm' hd'
    (fun i hi => horder i (by omega)) (fun i : Fin (k+1) => u i.val/σ)
    (prefix_feasible (show k+1≤n by omega) c d _ hu)
  have hscaled : (∑ i : Fin (k+1),β i.val*u i.val) ≤
      σ*(∑ i : Fin (k+1),β i.val*(c i.val/2*(A (i.val+1)^2-A i.val^2)+d i.val*(A (i.val+1)-A i.val))) := by
    have h := mul_le_mul_of_nonneg_left hbound hσ0.le
    convert h using 1 <;> try rfl
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [β]
    field_simp
  let S : ℝ := ∑ i : Fin k,β i.val*u i.val
  let R : ℝ := c k/2*(1-a k^2)+d k*(1-a k)
  have hlhs : (∑ i : Fin (k+1),β i.val*u i.val)=S+β k*u k := by
    rw [Fin.sum_univ_castSucc]
    rfl
  have hrhs : (∑ i : Fin (k+1),β i.val*(c i.val/2*(A (i.val+1)^2-A i.val^2)+d i.val*(A (i.val+1)-A i.val)))=S+β k*R := by
    rw [Fin.sum_univ_castSucc]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [Fin.val_castSucc]
      rw [hAi (i.val+1) (by omega),hAi i.val (by omega),←hmatch i.val i.isLt]
    · simp [R,hAk,hAend]
  rw [hlhs,hrhs] at hscaled
  have hS : 0≤S := Finset.sum_nonneg (fun i _ => mul_nonneg (hb.1 i.val (by omega)).le (hupos i.val (by omega)).le)
  have hβk : 0<β k := hb.1 k (by omega)
  have hRpos : 0<R := by
    by_contra hn
    have hR : R≤0 := le_of_not_gt hn
    have hm := mul_nonpos_of_nonneg_of_nonpos hβk.le hR
    have hm' := mul_nonpos_of_nonneg_of_nonpos hσ0.le hm
    have hS' := mul_le_mul_of_nonneg_right hσ1.le hS
    have hu' := mul_pos hβk (hupos k hk)
    nlinarith only [hscaled,hm',hS',hu']
  have hukR : u k<R := by
    have hgap := mul_pos (sub_pos.mpr hσ1) (mul_pos hβk hRpos)
    have hS' := mul_le_mul_of_nonneg_right hσ1.le hS
    nlinarith only [hscaled,hgap,hS',hβk]
  let f : ℝ → ℝ := fun b => c k/2*(b^2-a k^2)+d k*(b-a k)
  have hc : Continuous f := by dsimp [f];fun_prop
  have hf0 : f (a k)=0 := by simp [f]
  have hf1 : f 1=R := by simp [f,R]
  obtain ⟨b,hbmem,hbu⟩ := intermediate_value_Icc hak1.le hc.continuousOn
    (show u k∈Set.Icc (f (a k)) (f 1) by rw [hf0,hf1];exact ⟨(hupos k hk).le,hukR.le⟩)
  have hblt : a k<b := by
    by_contra h
    have he : b=a k := le_antisymm (le_of_not_gt h) hbmem.1
    rw [he,hf0] at hbu
    linarith [hupos k hk]
  have hblt1 : b<1 := by
    by_contra h
    have he : b=1 := le_antisymm hbmem.2 (le_of_not_gt h)
    rw [he,hf1] at hbu
    linarith
  exact ⟨b,⟨hblt,hblt1⟩,hbu.symm⟩
end FisherResearch
namespace FisherResearch
open MeasureTheory InfFisher.Linear
lemma greedy_cuts {n : ℕ} (c d u : ℕ → ℝ) (σ : ℝ)
    (hσ0 : 0<σ) (hσ1 : σ<1)
    (hnorm : ∀ i<n,c i/2+d i=1) (hd : ∀ i<n,0≤d i ∧ d i≤2)
    (horder : ∀ i,i+1<n → d (i+1)≤d i)
    (hu : (fun i : Fin n => u i.val/σ)∈feasUtil (volume.restrict (Set.Icc (0:ℝ) 1)) (linVal c d n))
    (hupos : ∀ i<n,0<u i) :
    ∃ a : ℕ → ℝ,a 0=0 ∧ (∀ i<n,a i≤a (i+1)) ∧
      (∀ i, 0 < i → i ≤ n → a i∈Set.Ioo (0:ℝ) 1) ∧
      ∀ i<n,u i=c i/2*(a (i+1)^2-a i^2)+d i*(a (i+1)-a i) := by
  have aux : ∀ k,k≤n → ∃ a : ℕ → ℝ,a 0=0 ∧ (∀ i<k,a i≤a (i+1)) ∧
      (∀ i, 0 < i → i ≤ k → a i∈Set.Ioo (0:ℝ) 1) ∧
      ∀ i<k,u i=c i/2*(a (i+1)^2-a i^2)+d i*(a (i+1)-a i) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨fun _ => 0,rfl,by omega,by omega,by omega⟩
    | succ k ih =>
      intro hkn
      obtain ⟨a,ha0,ha,hint,hmatch⟩ := ih (by omega)
      obtain ⟨b,hb,hbu⟩ := greedy_step c d u a σ hσ0 hσ1 hnorm hd horder hu hupos k (by omega) ha0 ha hint hmatch
      let A : ℕ → ℝ := fun i => if i=k+1 then b else a i
      have hAi (i : ℕ) (hi : i≤k) : A i=a i := by simp [A,show i≠k+1 by omega]
      have hAb : A (k+1)=b := by simp [A]
      have hak : 0≤a k := by
        by_cases hk0 : k=0
        · simp [hk0,ha0]
        · exact (hint k (by omega) le_rfl).1.le
      refine ⟨A,by simpa [hAi 0 (Nat.zero_le _)] using ha0,?_,?_,?_⟩
      · intro i hi
        by_cases hik : i=k
        · subst i
          rw [hAi k le_rfl,hAb]
          exact hb.1.le
        · rw [hAi i (by omega),hAi (i+1) (by omega)]
          exact ha i (by omega)
      · intro i hi hik
        by_cases he : i=k+1
        · subst i
          rw [hAb]
          exact ⟨hak.trans_lt hb.1,hb.2⟩
        · rw [hAi i (by omega)]
          exact hint i hi (by omega)
      · intro i hi
        by_cases hik : i=k
        · subst i
          rw [hAi k le_rfl,hAb]
          exact hbu
        · rw [hAi i (by omega),hAi (i+1) (by omega)]
          exact hmatch i (by omega)
  exact aux n le_rfl

lemma strict_feasible_interval_dominance {n : ℕ} (hn : 0<n) (c d u : ℕ → ℝ) (σ : ℝ)
    (hσ0 : 0<σ) (hσ1 : σ<1)
    (hnorm : ∀ i<n,c i/2+d i=1) (hd : ∀ i<n,0≤d i ∧ d i≤2)
    (horder : ∀ i,i+1<n → d (i+1)≤d i)
    (hu : (fun i : Fin n => u i.val/σ)∈feasUtil (volume.restrict (Set.Icc (0:ℝ) 1)) (linVal c d n))
    (hupos : ∀ i<n,0<u i) :
    ∃ a : ℕ → ℝ,a 0=0 ∧ (∀ i<n,a i≤a (i+1)) ∧ a n=1 ∧
      ∀ i<n,u i≤c i/2*(a (i+1)^2-a i^2)+d i*(a (i+1)-a i) := by
  obtain ⟨a,ha0,ha,hint,hmatch⟩ := greedy_cuts c d u σ hσ0 hσ1 hnorm hd horder hu hupos
  let A : ℕ → ℝ := fun i => if i=n then 1 else a i
  have hAi (i : ℕ) (hi : i<n) : A i=a i := by simp [A,ne_of_lt hi]
  have hAn : A n=1 := by simp [A]
  have han : a n∈Set.Ioo (0:ℝ) 1 := hint n hn le_rfl
  have hAn_ge (i : ℕ) (hi : i≤n) : a i≤A i := by
    by_cases he : i=n
    · simpa [he,hAn] using han.2.le
    · rw [hAi i (by omega)]
  refine ⟨A,by simpa [hAi 0 hn] using ha0,?_,hAn,?_⟩
  · intro i hi
    rw [hAi i hi]
    exact (ha i hi).trans (hAn_ge (i+1) (by omega))
  · intro i hi
    rw [hAi i hi,hmatch i hi]
    by_cases he : i+1=n
    · rw [he,hAn]
      have hc : c i/2=1-d i := by linarith [hnorm i hi]
      have hm := (strictF (hd i hi).1 (hd i hi).2).monotoneOn
        (show a n∈Set.Icc (0:ℝ) 1 from ⟨han.1.le,han.2.le⟩)
        (show (1:ℝ)∈Set.Icc 0 1 by norm_num) han.2.le
      dsimp [F] at hm
      rw [hc]
      nlinarith only [hm]
    · rw [hAi (i+1) (by omega)]
end FisherResearch
namespace FisherResearch
open MeasureTheory InfFisher.Linear
lemma mix_uniform_feasible {n : ℕ} (hn : 0<n) (c d : ℕ → ℝ)
    (hnorm : ∀ i<n,c i/2+d i=1) (u : Fin n → ℝ)
    (hu : u∈feasUtil (volume.restrict (Set.Icc (0:ℝ) 1)) (linVal c d n))
    (ε : ℝ) (hε0 : 0≤ε) (hε1 : ε≤1) :
    (fun i => (1-ε)*u i+ε/n)∈feasUtil (volume.restrict (Set.Icc (0:ℝ) 1)) (linVal c d n) := by
  classical
  let μ := volume.restrict (Set.Icc (0:ℝ) 1)
  have hnR : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  obtain ⟨x,hx,hux⟩ := hu
  have hv (i : Fin n) : Integrable (linVal c d n i) μ :=
    (show Continuous (fun θ:ℝ => c i.val*θ+d i.val) by fun_prop).integrableOn_Icc
  have hvx (i : Fin n) : Integrable (fun θ => linVal c d n i θ*x i θ) μ :=
    (memLp_one_iff_integrable.mpr (hv i)).integrable_mul (hx.1 i).1
  have hvone (i : Fin n) : (∫ θ,linVal c d n i θ ∂μ)=1 := by
    have h := linear_integral (c i.val) (d i.val) 0 1 (by norm_num)
    simp only [linVal,μ]
    rw [h]
    simpa using hnorm i.val i.isLt
  refine ⟨fun i θ => (1-ε)*x i θ+ε/n,⟨?_,?_⟩,?_⟩
  · intro i
    refine ⟨((hx.1 i).1.const_mul (1-ε)).add (memLp_top_const _),?_⟩
    filter_upwards [(hx.1 i).2] with θ hθ
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hε1) hθ) (div_nonneg hε0 hnR.le)
  · filter_upwards [hx.2] with θ hs
    simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hdiv : (n:ℝ)*(ε/n)=ε := by field_simp
    rw [hdiv]
    nlinarith [mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hε1)]
  · intro i
    change (1-ε)*u i+ε/n = ∫ θ,linVal c d n i θ*((1-ε)*x i θ+ε/n) ∂μ
    have he : (fun θ => linVal c d n i θ*((1-ε)*x i θ+ε/n)) =
      (fun θ => (1-ε)*(linVal c d n i θ*x i θ)+(ε/n)*linVal c d n i θ) := by funext θ;ring
    rw [he,integral_add ((hvx i).const_mul _) ((hv i).const_mul _),integral_const_mul,integral_const_mul,hvone i]
    rw [hux i]
    simp [pair,μ]
end FisherResearch
namespace FisherResearch
open MeasureTheory InfFisher.Linear Filter Topology
lemma interval_dominance {n : ℕ} (hn : 0<n) (c d : ℕ → ℝ)
    (hnorm : ∀ i<n,c i/2+d i=1)
    (hd : ∀ i j,i≤j → j<n → d j≤d i)
    (hd2 : d 0≤2) (hd0 : 0≤d (n-1)) (u : Fin n → ℝ)
    (hu : u∈feasUtil (volume.restrict (Set.Icc (0:ℝ) 1)) (linVal c d n)) :
    ∃ a : ℕ → ℝ,a 0=0 ∧ (∀ i<n,a i≤a (i+1)) ∧ a n=1 ∧
      ∀ i : Fin n,u i≤∫ θ in Set.Icc (a i.val) (a (i.val+1)),(c i.val*θ+d i.val) := by
  classical
  let U : ℕ → ℝ := fun i => if hi : i<n then u ⟨i,hi⟩ else 0
  have hUi (i : Fin n) : U i.val=u i := by simp [U]
  have hu0 := feasible_nonneg hn c d hnorm hd hd2 hd0 u hu
  have hU0 (i : ℕ) : 0≤U i := by dsimp [U];split <;> simp_all
  have hd' (i : ℕ) (hi : i<n) : 0≤d i ∧ d i≤2 :=
    ⟨hd0.trans (hd i (n-1) (by omega) (by omega)),(hd 0 i (Nat.zero_le _) hi).trans hd2⟩
  let ε : ℕ → ℝ := fun j => (1/((j:ℝ)+1))/2
  have hε (j : ℕ) : 0<ε j ∧ ε j<1 := by
    have hj : 0≤(j:ℝ) := Nat.cast_nonneg j
    have hden : 0<(j:ℝ)+1 := by positivity
    have hle : 1/((j:ℝ)+1)≤1 := (div_le_one₀ hden).mpr (by linarith)
    constructor
    · dsimp [ε];positivity
    · dsimp [ε];linarith
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).div_const 2
  let V : ℕ → ℕ → ℝ := fun j i => (1-ε j)*((1-ε j)*U i+ε j/n)
  have hVlim (i : ℕ) : Tendsto (fun j => V j i) atTop (𝓝 (U i)) := by
    have hσ := (tendsto_const_nhds (x:=(1:ℝ))).sub hεlim
    simpa [V] using hσ.mul ((hσ.mul_const (U i)).add (hεlim.div_const (n:ℝ)))
  have hex (j : ℕ) : ∃ a : ℕ → ℝ,a 0=0 ∧ (∀ i<n,a i≤a (i+1)) ∧ a n=1 ∧
      ∀ i<n,V j i≤c i/2*(a (i+1)^2-a i^2)+d i*(a (i+1)-a i) := by
    have hσ0 : 0<1-ε j := sub_pos.mpr (hε j).2
    have hσ1 : 1-ε j<1 := by linarith [(hε j).1]
    apply strict_feasible_interval_dominance hn c d (V j) (1-ε j) hσ0 hσ1 hnorm hd'
      (fun i hi => hd i (i+1) (by omega) hi)
    · have hm := mix_uniform_feasible hn c d hnorm u hu (ε j) (hε j).1.le (hε j).2.le
      convert hm using 1
      ext i
      dsimp [V]
      rw [mul_div_cancel_left₀ _ (ne_of_gt hσ0),hUi i]
    · intro i hi
      dsimp [V]
      apply mul_pos hσ0
      exact add_pos_of_nonneg_of_pos (mul_nonneg hσ0.le (hU0 i))
        (div_pos (hε j).1 (Nat.cast_pos.mpr hn))
  choose a ha0 ha han hau using hex
  let A : ℕ → ℕ → ℝ := fun j i => if i≤n then a j i else 1
  have hAi (j i : ℕ) (hi : i≤n) : A j i=a j i := by simp [A,hi]
  have hmem (j : ℕ) : A j∈Set.Icc (fun _ : ℕ => (0:ℝ)) (fun _ => (1:ℝ)) := by
    constructor <;> intro i
    · by_cases hi : i≤n
      · rw [hAi j i hi]
        simpa [ha0 j] using chain (a j) (ha j) (Nat.zero_le i) hi
      · simp [A,hi]
    · by_cases hi : i≤n
      · rw [hAi j i hi]
        simpa [han j] using chain (a j) (ha j) hi (le_refl n)
      · simp [A,hi]
  obtain ⟨b,hb,φ,hφ,hlim⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : ℕ => (0:ℝ)) (fun _ => (1:ℝ)))).tendsto_subseq hmem
  have hcoord (i : ℕ) : Tendsto (fun j => A (φ j) i) atTop (𝓝 (b i)) :=
    (tendsto_pi_nhds.mp hlim) i
  have hb0 : b 0=0 := tendsto_nhds_unique (hcoord 0)
    (by simpa [A,ha0] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0)))
  have hbn : b n=1 := tendsto_nhds_unique (hcoord n)
    (by simpa [A,han] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)))
  have hbmono (i : ℕ) (hi : i<n) : b i≤b (i+1) :=
    le_of_tendsto_of_tendsto (hcoord i) (hcoord (i+1)) (Filter.Eventually.of_forall (fun j => by
      change A (φ j) i ≤ A (φ j) (i+1)
      rw [hAi (φ j) i (by omega),hAi (φ j) (i+1) (by omega)]
      exact ha (φ j) i hi))
  refine ⟨b,hb0,hbmono,hbn,?_⟩
  intro i
  rw [linear_integral _ _ _ _ (hbmono i.val i.isLt)]
  have hleft : Tendsto (fun j => V (φ j) i.val) atTop (𝓝 (u i)) := by
    simpa only [Function.comp_def,hUi i] using (hVlim i.val).comp hφ.tendsto_atTop
  have hright : Tendsto (fun j => c i.val/2*(A (φ j) (i.val+1)^2-A (φ j) i.val^2)+d i.val*(A (φ j) (i.val+1)-A (φ j) i.val)) atTop
      (𝓝 (c i.val/2*(b (i.val+1)^2-b i.val^2)+d i.val*(b (i.val+1)-b i.val))) := by
    exact ((((hcoord (i.val+1)).pow 2).sub ((hcoord i.val).pow 2)).const_mul (c i.val/2)).add
      (((hcoord (i.val+1)).sub (hcoord i.val)).const_mul (d i.val))
  apply le_of_tendsto_of_tendsto hleft hright
  apply Filter.Eventually.of_forall
  intro j
  dsimp only
  rw [hAi (φ j) i.val (by omega),hAi (φ j) (i.val+1) (by omega)]
  exact hau (φ j) i.val i.isLt
end FisherResearch

open InfFisher.Linear MeasureTheory


open MeasureTheory

/-- Gao–Kroer, Theorem 4, pp. 15–16: the conic characterization of `U(v,[0,1])`. -/
theorem solution {n : ℕ} (hn : 2 ≤ n) (c d : ℕ → ℝ)
    (hnorm : ∀ i < n, c i / 2 + d i = 1)
    (hd : ∀ i j, i ≤ j → j < n → d j ≤ d i)
    (hd2 : d 0 ≤ 2) (hd0 : 0 ≤ d (n - 1)) :
    ∀ u : Fin n → ℝ,
      u ∈ feasUtil (volume.restrict (Set.Icc (0 : ℝ) 1)) (linVal c d n) ↔
        conicRep n c d u := by
  exact FisherResearch.full_conic_of_interval_dominance hn c d hnorm hd hd2 hd0
    (FisherResearch.interval_dominance (by omega) c d hnorm hd hd2 hd0)



#print axioms solution
