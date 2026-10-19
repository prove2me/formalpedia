-- Prove2me | solution 1 for MarketplaceLeakage.Benefits.profit_b
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-19T04:34:34.164437+00:00
-- url     : https://prove2.me/submissions/75deedd7-860a-41e4-ae4d-4ff5ec3a6f0a

import Mathlib
import Definitions.Def_MarketplaceLeakage_Baseline_Setting
import Definitions.Def_MarketplaceLeakage_Benefits_Setting

open MarketplaceLeakage.Baseline
set_option maxHeartbeats 1600000

namespace LeakBaseProof

lemma g_bounds (μ x : ℝ) : 0 ≤ G μ x ∧ G μ x ≤ 1 := by
  unfold G
  exact ⟨le_min (le_max_right _ _) (by norm_num), min_le_right _ _⟩

lemma g_small {μ x : ℝ} (hμ : 0 < μ) (hx : 0 ≤ x) (hxμ : x ≤ μ) :
    G μ x = x / μ := by
  simp only [G, max_eq_left (div_nonneg hx hμ.le),
    min_eq_left ((div_le_one hμ).2 hxμ)]

lemma g_large {μ x : ℝ} (hμ : 0 < μ) (hx : μ ≤ x) : G μ x = 1 := by
  have h : 1 ≤ x / μ := (le_div_iff₀ hμ).2 (by simpa using hx)
  exact min_eq_right (h.trans (le_max_left _ _))

lemma seller_small {v c μ f p : ℝ} (hμ : 0 < μ) (hp : p ≤ v) (hx : v - p ≤ μ) :
    μ * sProfit v c μ f p = μ * (v - c - f) + (f - (v-p)) * (v-p) := by
  rw [sProfit, g_small hμ (sub_nonneg.mpr hp) hx]
  field_simp
  <;> ring

lemma seller_large {v c μ f p : ℝ} (hμ : 0 < μ) (hx : μ ≤ v - p) :
    sProfit v c μ f p = p - c := by
  simp [sProfit, g_large hμ hx]

lemma seller_peak {v c μ f : ℝ} (hμ : 0 < μ) (hf : 0 ≤ f) :
    let pstar := if 2 * μ ≤ f then v - μ else v - f / 2
    pstar ≤ v ∧ ∀ p : ℝ, p ≤ v →
      sProfit v c μ f p ≤ sProfit v c μ f pstar ∧
      (sProfit v c μ f p = sProfit v c μ f pstar → p = pstar) := by
  dsimp
  split_ifs with hfμ
  · refine ⟨by linarith, ?_⟩
    intro p hp
    rw [seller_large hμ (by linarith : μ ≤ v - (v-μ))]
    by_cases hx : μ ≤ v-p
    · rw [seller_large hμ hx]
      exact ⟨by linarith, by intro h; linarith⟩
    · have hxp : 0 < μ - (v-p) := by linarith
      have hfp : 0 < f - μ - (v-p) := by linarith
      have hm := mul_pos hxp hfp
      have hs := seller_small (v:=v) (c:=c) (f:=f) hμ hp (by linarith : v-p ≤ μ)
      have hstrict : sProfit v c μ f p < v - μ - c := by
        nlinarith
      exact ⟨hstrict.le, by intro he; linarith⟩
  · have hfμ' : f < 2 * μ := by linarith
    refine ⟨by linarith, ?_⟩
    intro p hp
    have hstar := seller_small (v:=v) (c:=c) (f:=f) (p:=v-f/2) hμ
      (by linarith) (by linarith)
    by_cases hx : v-p ≤ μ
    · have hs := seller_small (v:=v) (c:=c) (f:=f) hμ hp hx
      have hsq := sq_nonneg (v-p-f/2)
      constructor
      · nlinarith
      · intro he
        have hz : (v-p-f/2)^2 = 0 := by nlinarith
        have : v-p-f/2 = 0 := (sq_eq_zero_iff).1 hz
        linarith
    · rw [seller_large hμ (by linarith : μ ≤ v-p)]
      have hsq : 0 < (2*μ-f)^2 := sq_pos_of_pos (by linarith)
      have hstrict : p-c < sProfit v c μ f (v-f/2) := by nlinarith
      exact ⟨hstrict.le, by intro he; linarith⟩

lemma seller_iff (v c μ : ℝ) (hμ : 0 < μ) (f : ℝ) (hf : 0 ≤ f) (pd : ℝ) :
    IsSOpt v c μ f pd ↔ pd = (if 2 * μ ≤ f then v - μ else v - f / 2) := by
  have hp := seller_peak (v:=v) (c:=c) hμ hf
  constructor
  · intro h
    apply (hp.2 pd h.1).2
    exact le_antisymm (hp.2 pd h.1).1 (h.2 _ hp.1)
  · intro h
    subst pd
    exact ⟨hp.1, fun p hp' => (hp.2 p hp').1⟩

lemma good_seller {v c μ f : ℝ} (hμ : 0 < μ) (hf : 0 ≤ f) (hfm : f < 2*μ) :
    IsSOpt v c μ f (v-f/2) := by
  apply (seller_iff v c μ hμ f hf _).2
  rw [if_neg (not_le.mpr hfm)]


end LeakBaseProof

open MarketplaceLeakage.Benefits
namespace LeakBenefitsProof
open LeakBaseProof

lemma sellerB_eq (v c μ b f pd : ℝ) : sProfitB v c μ b f pd = sProfit v c μ (f-b) pd := by
  unfold sProfitB sProfit
  ring

lemma sellerB_base (v c μ b f pd : ℝ) : IsSOptB v c μ b f pd ↔ IsSOpt v c μ (f-b) pd := by
  simp only [IsSOptB, IsSOpt, sellerB_eq]

lemma response {v c μ b f pd : ℝ} (hμ : 0 < μ) (hbf : b ≤ f) :
    IsSOptB v c μ b f pd ↔ pd = (if b+2*μ ≤ f then v-μ else v-(f-b)/2) := by
  rw [sellerB_base, seller_iff v c μ hμ (f-b) (sub_nonneg.mpr hbf) pd]
  have hiff : 2*μ ≤ f-b ↔ b+2*μ ≤ f := by constructor <;> intro h <;> linarith
  simp only [hiff]

lemma profit_formula {v c μ k b f pd : ℝ} (hμ : 0 < μ) (hbf : b ≤ f)
    (hs : IsSOptB v c μ b f pd) :
    MProfitB v μ k b f pd = if b+2*μ ≤ f then -(k*b^2/2)
      else f*(1-(f-b)/(2*μ))-k*b^2/2 := by
  rw [(response hμ hbf).1 hs]
  split_ifs with hfm
  · rw [MProfitB, g_large hμ (by linarith : μ ≤ v-(v-μ))]
    ring
  · rw [MProfitB, g_small hμ (by linarith : 0 ≤ v-(v-(f-b)/2))
      (by linarith : v-(v-(f-b)/2) ≤ μ)]
    ring

noncomputable def share (μ x : ℝ) := 1-min (x/(2*μ)) 1
noncomputable def F (μ k b t : ℝ) := b*t+2*μ*t*(1-t)-k/2*b^2
def GoodT (μ a t : ℝ) : Prop := 0 ≤ t ∧ t ≤ 1 ∧ 1-a/(2*μ) ≤ t
def MaxF (μ k a b t : ℝ) : Prop :=
  0 ≤ b ∧ GoodT μ a t ∧ ∀ b' t', 0 ≤ b' → GoodT μ a t' → F μ k b' t' ≤ F μ k b t

lemma share_small {μ x : ℝ} (hμ : 0 < μ) (hx : x ≤ 2*μ) : share μ x = 1-x/(2*μ) := by
  rw [share, min_eq_left ((div_le_one (by positivity : 0 < 2*μ)).2 hx)]

lemma share_large {μ x : ℝ} (hμ : 0 < μ) (hx : 2*μ ≤ x) : share μ x = 0 := by
  rw [share, min_eq_right ((le_div_iff₀ (by positivity : 0 < 2*μ)).2 (by simpa using hx))]
  ring

lemma share_good {μ a x : ℝ} (hμ : 0 < μ) (hx : 0 ≤ x) (hxa : x ≤ a) :
    GoodT μ a (share μ x) := by
  have hlo : 0 ≤ min (x/(2*μ)) 1 := le_min (div_nonneg hx (by positivity)) (by norm_num)
  have hhi : min (x/(2*μ)) 1 ≤ 1 := min_le_right _ _
  have hcap : min (x/(2*μ)) 1 ≤ a/(2*μ) :=
    (min_le_left _ _).trans (div_le_div_of_nonneg_right hxa (by positivity))
  unfold GoodT share
  exact ⟨by linarith, by linarith, by linarith⟩

lemma share_identity {μ x : ℝ} (hμ : 0 < μ) :
    x*share μ x = 2*μ*share μ x*(1-share μ x) := by
  by_cases hx : x ≤ 2*μ
  · rw [share_small hμ hx]
    field_simp
    <;> ring
  · rw [share_large hμ (le_of_not_ge hx)]
    ring

lemma seller_share {v c μ b f pd : ℝ} (hμ : 0 < μ) (hbf : b ≤ f)
    (hs : IsSOptB v c μ b f pd) : 1-G μ (v-pd) = share μ (f-b) := by
  rw [(response hμ hbf).1 hs]
  split_ifs with hfm
  · rw [g_large hμ (by linarith : μ ≤ v-(v-μ)), share_large hμ (by linarith)]
    ring
  · rw [g_small hμ (by linarith : 0 ≤ v-(v-(f-b)/2))
      (by linarith : v-(v-(f-b)/2) ≤ μ), share_small hμ (by linarith)]
    ring

lemma profit_F {v c μ k b f pd : ℝ} (hμ : 0 < μ) (hbf : b ≤ f)
    (hs : IsSOptB v c μ b f pd) : MProfitB v μ k b f pd = F μ k b (share μ (f-b)) := by
  rw [MProfitB, seller_share hμ hbf hs, F]
  have h := share_identity (x:=f-b) hμ
  nlinarith [h]

lemma realizes {v c μ k b t : ℝ} (hμ : 0 < μ) (hb : 0 ≤ b) (ht : GoodT μ (v-c) t) :
    Feasible v c b (b+2*μ*(1-t)) ∧
    IsSOptB v c μ b (b+2*μ*(1-t)) (v-μ*(1-t)) ∧
    share μ ((b+2*μ*(1-t))-b) = t ∧
    MProfitB v μ k b (b+2*μ*(1-t)) (v-μ*(1-t)) = F μ k b t := by
  have hx0 : 0 ≤ 2*μ*(1-t) := mul_nonneg (by positivity) (sub_nonneg.mpr ht.2.1)
  have hxm : 2*μ*(1-t) ≤ 2*μ := by nlinarith [ht.1]
  have hxa : 2*μ*(1-t) ≤ v-c := by
    have h := (le_div_iff₀ (by positivity : 0 < 2*μ)).1 (show (v-c)/(2*μ) ≥ 1-t by linarith [ht.2.2])
    nlinarith
  have hbf : b ≤ b+2*μ*(1-t) := by linarith
  have hs : IsSOptB v c μ b (b+2*μ*(1-t)) (v-μ*(1-t)) := by
    apply (response hμ hbf).2
    split_ifs with h <;> nlinarith
  have he : share μ ((b+2*μ*(1-t))-b) = t := by
    rw [share_small hμ (by linarith)]
    field_simp
    <;> ring
  exact ⟨⟨hb, hbf, by linarith⟩, hs, he, by rw [profit_F hμ hbf hs, he]⟩

lemma opt_to_max {v c μ k b f pd : ℝ} (hμ : 0 < μ) (h : IsOpt v c μ k b f pd) :
    MaxF μ k (v-c) b (share μ (f-b)) := by
  refine ⟨h.1.1, share_good hμ (sub_nonneg.mpr h.1.2.1) (by linarith [h.1.2.2]), ?_⟩
  intro b' t' hb' ht'
  have hr := realizes (v:=v) (c:=c) (k:=k) hμ hb' ht'
  have ho := h.2.2 _ _ _ hr.1 hr.2.1
  rw [hr.2.2.2, profit_F hμ h.1.2.1 h.2.1] at ho
  exact ho

lemma max_to_opt {v c μ k b f pd : ℝ} (hμ : 0 < μ)
    (hf : Feasible v c b f) (hs : IsSOptB v c μ b f pd)
    (hm : MaxF μ k (v-c) b (share μ (f-b))) : IsOpt v c μ k b f pd := by
  refine ⟨hf, hs, ?_⟩
  intro b' f' pd' hf' hs'
  rw [profit_F hμ hf.2.1 hs, profit_F hμ hf'.2.1 hs']
  exact hm.2.2 b' _ hf'.1 (share_good hμ (sub_nonneg.mpr hf'.2.1) (by linarith [hf'.2.2]))

noncomputable def U (μ k t : ℝ) := 2*μ*t-(2*μ-1/(2*k))*t^2
noncomputable def T (μ k a : ℝ) :=
  if μ ≤ 1/(2*k) then 1 else max (1-a/(2*μ)) (μ/(2*μ-1/(2*k)))

lemma F_square {μ k b t : ℝ} (hk : 0 < k) :
    F μ k b t = U μ k t-k/2*(b-t/k)^2 := by
  unfold F U
  field_simp
  <;> ring

lemma F_upper {μ k b t : ℝ} (hk : 0 < k) :
    F μ k b t ≤ U μ k t ∧ (F μ k b t = U μ k t → b = t/k) := by
  rw [F_square hk]
  have hp := mul_nonneg (by positivity : 0 ≤ k/2) (sq_nonneg (b-t/k))
  constructor
  · linarith
  · intro he
    have hz : (b-t/k)^2 = 0 := by nlinarith
    have := sq_eq_zero_iff.mp hz
    linarith

lemma F_at {μ k t : ℝ} (hk : 0 < k) : F μ k (t/k) t = U μ k t := by
  rw [F_square hk]
  ring

lemma U_scaled {μ k t : ℝ} (hk : 0 < k) :
    2*k*U μ k t = 4*k*μ*t-(4*k*μ-1)*t^2 := by
  unfold U
  field_simp
  <;> ring

lemma low_peak {μ k t : ℝ} (hk : 0 < k) (hm : μ ≤ 1/(2*k)) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    U μ k t ≤ U μ k 1 ∧ (U μ k t = U μ k 1 → t = 1) := by
  have hm' : μ*(2*k) ≤ 1 := (le_div_iff₀ (by positivity)).1 hm
  have hs := U_scaled (μ:=μ) (t:=t) hk
  have hs1 := U_scaled (μ:=μ) (t:=1) hk
  by_cases ht : t = 1
  · subst t
    exact ⟨le_rfl, fun _ => rfl⟩
  · have htt : t < 1 := lt_of_le_of_ne ht1 ht
    have hfactor : 0 < 1+t-4*k*μ*t := by
      nlinarith [mul_nonneg (by nlinarith : 0 ≤ 2-4*k*μ) ht0]
    have hp := mul_pos (sub_pos.mpr htt) hfactor
    have hstrict : U μ k t < U μ k 1 := by nlinarith
    exact ⟨hstrict.le, by intro he; linarith⟩

lemma high_constants {μ k : ℝ} (hk : 0 < k) (hm : 1/(2*k) < μ) :
    0 < 2*μ-1/(2*k) ∧ 0 < μ/(2*μ-1/(2*k)) ∧ μ/(2*μ-1/(2*k)) < 1 := by
  have hμ : 0 < μ := (by positivity : 0 < 1/(2*k)).trans hm
  have hc : 0 < 2*μ-1/(2*k) := by linarith
  exact ⟨hc, div_pos hμ hc, (div_lt_one hc).2 (by linarith)⟩

lemma T_good {μ k a : ℝ} (hμ : 0 < μ) (hk : 0 < k) (ha : 0 < a) :
    GoodT μ a (T μ k a) ∧ 0 < T μ k a := by
  have hl : 1-a/(2*μ) < 1 := by have := div_pos ha (by positivity : 0 < 2*μ); linarith
  unfold T
  split_ifs with hm
  · exact ⟨⟨by norm_num, le_rfl, hl.le⟩, by norm_num⟩
  · have hc := high_constants hk (lt_of_not_ge hm)
    have hp := hc.2.1.trans_le (le_max_right (1-a/(2*μ)) _)
    exact ⟨⟨hp.le, max_le hl.le hc.2.2.le, le_max_left _ _⟩, hp⟩

lemma U_peak {μ k a t : ℝ} (hμ : 0 < μ) (hk : 0 < k) (ha : 0 < a) (ht : GoodT μ a t) :
    U μ k t ≤ U μ k (T μ k a) ∧ (U μ k t = U μ k (T μ k a) → t = T μ k a) := by
  unfold T
  split_ifs with hm
  · exact low_peak hk hm ht.1 ht.2.1
  · have hc := (high_constants hk (lt_of_not_ge hm)).1
    let C := 2*μ-1/(2*k)
    let u := μ/C
    let l := 1-a/(2*μ)
    have hcu : C*u = μ := by dsimp [u]; field_simp [show C ≠ 0 from hc.ne']
    change U μ k t ≤ U μ k (max l u) ∧ _
    by_cases hlu : l ≤ u
    · rw [max_eq_right hlu]
      have hid : U μ k u-U μ k t = C*(t-u)^2 := by
        dsimp only [U]
        change (2*μ*u-C*u^2)-(2*μ*t-C*t^2) = C*(t-u)^2
        linear_combination -2*(u-t)*hcu
      have hp := mul_nonneg hc.le (sq_nonneg (t-u))
      constructor
      · linarith
      · intro he
        have hz : (t-u)^2 = 0 := by nlinarith
        have := sq_eq_zero_iff.mp hz
        linarith
    · rw [max_eq_left (le_of_not_ge hlu)]
      have hcl : μ < C*l := by
        rw [← hcu]
        exact mul_lt_mul_of_pos_left (lt_of_not_ge hlu) hc
      have htl : l ≤ t := ht.2.2
      have hfactor : 0 < C*(t+l)-2*μ := by
        have := mul_le_mul_of_nonneg_left htl hc.le
        linarith
      have hid : U μ k l-U μ k t = (t-l)*(C*(t+l)-2*μ) := by unfold U; dsimp [C]; ring
      have hp := mul_nonneg (sub_nonneg.mpr htl) hfactor.le
      constructor
      · linarith
      · intro he
        by_contra hne
        have hp' := mul_pos (sub_pos.mpr (lt_of_le_of_ne htl (Ne.symm hne))) hfactor
        linarith

lemma maxF_character {μ k a b t : ℝ} (hμ : 0 < μ) (hk : 0 < k) (ha : 0 < a)
    (h : MaxF μ k a b t) : t = T μ k a ∧ b = t/k := by
  have hg := T_good hμ hk ha
  have hp := h.2.2 (T μ k a/k) (T μ k a) (div_nonneg hg.2.le hk.le) hg.1
  rw [F_at hk] at hp
  have hu := F_upper (μ:=μ) (b:=b) (t:=t) hk
  have ht := U_peak hμ hk ha h.2.1
  have heU : U μ k t = U μ k (T μ k a) := le_antisymm ht.1 (hp.trans hu.1)
  exact ⟨ht.2 heU, hu.2 (le_antisymm hu.1 (heU ▸ hp))⟩

lemma maxF_exists {μ k a : ℝ} (hμ : 0 < μ) (hk : 0 < k) (ha : 0 < a) :
    MaxF μ k a (T μ k a/k) (T μ k a) := by
  have hg := T_good hμ hk ha
  refine ⟨div_nonneg hg.2.le hk.le, hg.1, ?_⟩
  intro b t hb ht
  rw [F_at hk]
  exact (F_upper (μ:=μ) (b:=b) (t:=t) hk).1.trans (U_peak hμ hk ha ht).1

lemma bar_data {v c k : ℝ} (hvc : c < v) (hk : 0 < k) :
    max (v-c) (1/(2*k)) < muBar v c k ∧
    4*k*muBar v c k*(muBar v c k-(v-c))-2*muBar v c k+(v-c) = 0 := by
  let a := v-c
  let s := Real.sqrt ((a/2)^2+1/(16*k^2))
  have ha : 0 < a := sub_pos.mpr hvc
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s^2 = (a/2)^2+1/(16*k^2) := Real.sq_sqrt (by positivity)
  have hc4 : 0 < 1/(4*k) := by positivity
  have hinv : 1/(16*k^2) = (1/(4*k))^2 := by field_simp; ring
  have hsa : a/2 < s := by
    have hpos : 0 < 1/(16*k^2) := by positivity
    nlinarith
  have hsk : 1/(4*k) < s := by rw [hinv] at hsq; nlinarith
  have hhalf : 1/(2*k) = 2*(1/(4*k)) := by ring
  have hsroot : 16*k^2*s^2 = 4*k^2*a^2+1 := by
    field_simp at hsq
    nlinarith [hsq]
  change max a (1/(2*k)) < a/2+1/(4*k)+s ∧
    4*k*(a/2+1/(4*k)+s)*(a/2+1/(4*k)+s-a)-2*(a/2+1/(4*k)+s)+a = 0
  constructor
  · apply max_lt_iff.mpr
    exact ⟨by linarith, by linarith⟩
  · field_simp
    nlinarith [hsroot]

lemma bar_factor {v c k μ : ℝ} (hvc : c < v) (hk : 0 < k) :
    4*k*μ*(μ-(v-c))-2*μ+(v-c) =
      (μ-muBar v c k)*(4*k*(μ+muBar v c k-(v-c)-1/(2*k))) := by
  have hr := (bar_data hvc hk).2
  have hi : 2*k*(1/(2*k)) = 1 := by field_simp
  linear_combination hr+2*(μ-muBar v c k)*hi

lemma bar_comparison {v c k μ : ℝ} (hvc : c < v) (hk : 0 < k)
    (hf : 0 < μ+muBar v c k-(v-c)-1/(2*k)) :
    (4*k*μ*(μ-(v-c))-2*μ+(v-c) ≤ 0 ↔ μ ≤ muBar v c k) ∧
    (0 ≤ 4*k*μ*(μ-(v-c))-2*μ+(v-c) ↔ muBar v c k ≤ μ) := by
  have hp : 0 < 4*k*(μ+muBar v c k-(v-c)-1/(2*k)) := by positivity
  rw [bar_factor hvc hk]
  constructor
  · constructor
    · intro h
      by_contra hn
      have ht := mul_pos (by linarith : 0 < μ-muBar v c k) hp
      linarith
    · intro h
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) hp.le
  · exact (mul_nonneg_iff_of_pos_right hp).trans sub_nonneg

lemma bar_facts {v c k : ℝ} (hvc : c < v) (hk : 0 < k) :
    max (v-c) (1/(2*k)) < muBar v c k ∧
    ∀ μ : ℝ, v-c < μ →
      ((1/(2*μ) ≤ k ∧ k ≤ (2*μ-(v-c))/(4*μ*(μ-(v-c)))) ↔
        (1/(2*k) ≤ μ ∧ μ ≤ muBar v c k)) ∧
      ((2*μ-(v-c))/(4*μ*(μ-(v-c))) ≤ k ↔ muBar v c k ≤ μ) := by
  have hb := (bar_data hvc hk).1
  refine ⟨hb, ?_⟩
  intro μ hm
  have hμ : 0 < μ := (sub_pos.mpr hvc).trans hm
  have hden : 0 < 4*μ*(μ-(v-c)) := by positivity
  have hcomp := bar_comparison (μ:=μ) hvc hk
    (by linarith [lt_of_le_of_lt (le_max_right (v-c) (1/(2*k))) hb])
  have hone : 1/(2*μ) ≤ k ↔ 1/(2*k) ≤ μ := by
    rw [div_le_iff₀ (by positivity : 0 < 2*μ), div_le_iff₀ (by positivity : 0 < 2*k)]
    constructor <;> intro h <;> nlinarith
  have hle : k ≤ (2*μ-(v-c))/(4*μ*(μ-(v-c))) ↔ μ ≤ muBar v c k := by
    rw [le_div_iff₀ hden, ← hcomp.1]
    constructor <;> intro h <;> nlinarith
  have hge : (2*μ-(v-c))/(4*μ*(μ-(v-c))) ≤ k ↔ muBar v c k ≤ μ := by
    rw [div_le_iff₀ hden, ← hcomp.2]
    constructor <;> intro h <;> nlinarith
  exact ⟨and_congr hone hle, hge⟩

lemma vertex_region {v c μ k : ℝ} (hvc : c < v) (hk : 0 < k) (hm : 1/(2*k) < μ) :
    1-(v-c)/(2*μ) ≤ μ/(2*μ-1/(2*k)) ↔ μ ≤ muBar v c k := by
  have hμ : 0 < μ := (by positivity : 0 < 1/(2*k)).trans hm
  have hc := (high_constants hk hm).1
  have hb := (bar_data hvc hk).1
  have hcomp := (bar_comparison (μ:=μ) hvc hk
    (by linarith [lt_of_le_of_lt (le_max_left (v-c) (1/(2*k))) hb])).1
  have hid : 4*k*μ*((2*μ-1/(2*k))*(1-(v-c)/(2*μ))-μ) =
      4*k*μ*(μ-(v-c))-2*μ+(v-c) := by field_simp <;> ring
  rw [le_div_iff₀ hc, ← hcomp]
  have hp : 0 < 4*k*μ := by positivity
  constructor <;> intro h <;> nlinarith

lemma T_cases {v c μ k : ℝ} (hvc : c < v) (hk : 0 < k) :
    T μ k (v-c) = if μ ≤ 1/(2*k) then 1 else if μ ≤ muBar v c k
      then μ/(2*μ-1/(2*k)) else 1-(v-c)/(2*μ) := by
  unfold T
  split_ifs with hm hbar
  · rfl
  · exact max_eq_right ((vertex_region hvc hk (lt_of_not_ge hm)).2 hbar)
  · exact max_eq_left (le_of_not_ge (fun h => hbar ((vertex_region hvc hk (lt_of_not_ge hm)).1 h)))

lemma middle_den_pos {μ k : ℝ} (hk : 0 < k) (hm : 1/(2*k) ≤ μ) :
    0 < μ ∧ 0 < 2*k-1/(2*μ) := by
  have hμ := (by positivity : 0 < 1/(2*k)).trans_le hm
  have hm' := (div_le_iff₀ (by positivity : 0 < 2*k)).1 hm
  have hinv : 1/(2*μ) ≤ k := (div_le_iff₀ (by positivity)).2 (by nlinarith)
  exact ⟨hμ, by linarith⟩

lemma b_formula {v c μ k : ℝ} (hvc : c < v) (hμ : 0 < μ) (hk : 0 < k) :
    T μ k (v-c)/k = if μ ≤ 1/(2*k) then 1/k else if μ ≤ muBar v c k
      then 1/(2*k-1/(2*μ)) else 1/k-(v-c)/(2*k*μ) := by
  rw [T_cases hvc hk]
  split_ifs with hm hbar
  · rfl
  · have hc := (high_constants hk (lt_of_not_ge hm)).1
    have hd := (middle_den_pos hk (le_of_lt (lt_of_not_ge hm))).2
    field_simp
    <;> ring
  · ring

lemma opt_exists {v c μ k : ℝ} (hvc : c < v) (hμ : 0 < μ) (hk : 0 < k) :
    ∃ b f pd : ℝ, IsOpt v c μ k b f pd := by
  have hg := T_good hμ hk (sub_pos.mpr hvc)
  have hr := realizes (v:=v) (c:=c) (k:=k) hμ (div_nonneg hg.2.le hk.le) hg.1
  refine ⟨T μ k (v-c)/k, _, _, max_to_opt hμ hr.1 hr.2.1 ?_⟩
  rw [hr.2.2.1]
  exact maxF_exists hμ hk (sub_pos.mpr hvc)

lemma opt_data {v c μ k b f pd : ℝ} (hvc : c < v) (hμ : 0 < μ) (hk : 0 < k)
    (h : IsOpt v c μ k b f pd) :
    b = T μ k (v-c)/k ∧ 0 < b ∧
    f = b+2*μ*(1-T μ k (v-c)) ∧ pd = v-μ*(1-T μ k (v-c)) ∧
    leakage v μ pd = 1-k*b ∧ MProfitB v μ k b f pd = U μ k (T μ k (v-c)) := by
  have he := maxF_character hμ hk (sub_pos.mpr hvc) (opt_to_max hμ h)
  have hg := T_good hμ hk (sub_pos.mpr hvc)
  have hb : b = T μ k (v-c)/k := by rw [he.2, he.1]
  have hbpos : 0 < b := by rw [hb]; exact div_pos hg.2 hk
  have hshare : 0 < share μ (f-b) := he.1 ▸ hg.2
  have hlt : f-b < 2*μ := by
    by_contra hn
    rw [share_large hμ (le_of_not_gt hn)] at hshare
    exact lt_irrefl 0 hshare
  have hx := he.1
  rw [share_small hμ hlt.le] at hx
  have hx' := (div_eq_iff (by positivity : 2*μ ≠ 0)).1
    (show (f-b)/(2*μ) = 1-T μ k (v-c) by linarith)
  have hf : f = b+2*μ*(1-T μ k (v-c)) := by nlinarith
  have hp := (response hμ h.1.2.1).1 h.2.1
  rw [if_neg (by linarith : ¬ b+2*μ ≤ f)] at hp
  have hkb : k*b = T μ k (v-c) := by rw [hb]; field_simp
  refine ⟨hb, hbpos, hf, by nlinarith, ?_, ?_⟩
  · have hs := seller_share hμ h.1.2.1 h.2.1
    rw [he.1] at hs
    unfold leakage
    linarith
  · rw [profit_F hμ h.1.2.1 h.2.1, he.1, hb, F_at hk]

lemma cost_strict {μ a k₁ k₂ b₁ t₁ b₂ t₂ : ℝ} (hμ : 0 < μ) (ha : 0 < a)
    (hk1 : 0 < k₁) (hk12 : k₁ < k₂)
    (h1 : MaxF μ k₁ a b₁ t₁) (h2 : MaxF μ k₂ a b₂ t₂) : b₂ < b₁ := by
  have hk2 : 0 < k₂ := hk1.trans hk12
  have hc1 := h1.2.2 b₂ t₂ h2.1 h2.2.1
  have hc2 := h2.2.2 b₁ t₁ h1.1 h1.2.1
  have hle : b₂ ≤ b₁ := by
    by_contra hn
    have hlt : b₁ < b₂ := lt_of_not_ge hn
    have hsq : b₁^2 < b₂^2 := by nlinarith [h1.1, h2.1]
    have hp := mul_pos (sub_pos.mpr hk12) (sub_pos.mpr hsq)
    unfold F at hc1 hc2
    nlinarith
  apply lt_of_le_of_ne hle
  intro he
  have hv : F μ k₁ b₂ t₂ = F μ k₁ b₁ t₁ := by
    rw [he] at hc1 hc2 ⊢
    unfold F at hc1 hc2 ⊢
    nlinarith
  have hhybrid : MaxF μ k₁ a b₂ t₂ :=
    ⟨h2.1, h2.2.1, fun b t hb ht => (h1.2.2 b t hb ht).trans_eq hv.symm⟩
  have e1 := maxF_character hμ hk1 ha hhybrid
  have e2 := maxF_character hμ hk2 ha h2
  have hpos : 0 < t₂ := e2.1 ▸ (T_good hμ hk2 ha).2
  have hbpos : 0 < b₂ := e2.2 ▸ div_pos hpos hk2
  have hkb1 : k₁*b₂ = t₂ := by rw [e1.2]; field_simp
  have hkb2 : k₂*b₂ = t₂ := by rw [e2.2]; field_simp
  nlinarith

lemma vertex_region_ge {v c μ k : ℝ} (hvc : c < v) (hk : 0 < k) (hm : 1/(2*k) < μ) :
    μ/(2*μ-1/(2*k)) ≤ 1-(v-c)/(2*μ) ↔ muBar v c k ≤ μ := by
  have hμ : 0 < μ := (by positivity : 0 < 1/(2*k)).trans hm
  have hc := (high_constants hk hm).1
  have hb := (bar_data hvc hk).1
  have hcomp := (bar_comparison (μ:=μ) hvc hk
    (by linarith [lt_of_le_of_lt (le_max_left (v-c) (1/(2*k))) hb])).2
  have hid : 4*k*μ*((2*μ-1/(2*k))*(1-(v-c)/(2*μ))-μ) =
      4*k*μ*(μ-(v-c))-2*μ+(v-c) := by field_simp <;> ring
  rw [div_le_iff₀ hc, ← hcomp]
  have hp : 0 < 4*k*μ := by positivity
  constructor <;> intro h <;> nlinarith

lemma T_mid {v c μ k : ℝ} (hvc : c < v) (hk : 0 < k)
    (hm : 1/(2*k) ≤ μ) (hbar : μ ≤ muBar v c k) :
    T μ k (v-c) = μ/(2*μ-1/(2*k)) := by
  by_cases hlo : μ ≤ 1/(2*k)
  · have he : μ = 1/(2*k) := le_antisymm hlo hm
    have hμ := (middle_den_pos hk hm).1
    rw [T, if_pos hlo, ← he]
    field_simp
    <;> ring
  · rw [T_cases hvc hk, if_neg hlo, if_pos hbar]

lemma T_high {v c μ k : ℝ} (hvc : c < v) (hk : 0 < k) (hbar : muBar v c k ≤ μ) :
    T μ k (v-c) = 1-(v-c)/(2*μ) := by
  have hm : 1/(2*k) < μ :=
    (lt_of_le_of_lt (le_max_right (v-c) (1/(2*k))) (bar_data hvc hk).1).trans_le hbar
  rw [T, if_neg (not_le.mpr hm), max_eq_left ((vertex_region_ge hvc hk hm).2 hbar)]

lemma opt_b_mid {v c μ k b f pd : ℝ} (hvc : c < v) (hk : 0 < k)
    (hm : 1/(2*k) ≤ μ) (hbar : μ ≤ muBar v c k) (h : IsOpt v c μ k b f pd) :
    b = 1/(2*k-1/(2*μ)) := by
  have hμ := (middle_den_pos hk hm).1
  have hd := (middle_den_pos hk hm).2
  have hc : 0 < 2*μ-1/(2*k) := by linarith
  rw [(opt_data hvc hμ hk h).1, T_mid hvc hk hm hbar]
  field_simp
  <;> ring

lemma opt_b_high {v c μ k b f pd : ℝ} (hvc : c < v) (hk : 0 < k)
    (hbar : muBar v c k ≤ μ) (h : IsOpt v c μ k b f pd) :
    b = 1/k-(v-c)/(2*k*μ) := by
  have hμ : 0 < μ := (sub_pos.mpr hvc).trans_le
    ((le_max_left (v-c) (1/(2*k))).trans ((bar_data hvc hk).1.le.trans hbar))
  rw [(opt_data hvc hμ hk h).1, T_high hvc hk hbar]
  ring

lemma mid_comparative {v c k μ₁ μ₂ b₁ f₁ p₁ b₂ f₂ p₂ : ℝ}
    (hvc : c < v) (hk : 0 < k) (hm1 : 1/(2*k) ≤ μ₁) (h12 : μ₁ < μ₂)
    (hm2 : μ₂ ≤ muBar v c k) (h1 : IsOpt v c μ₁ k b₁ f₁ p₁)
    (h2 : IsOpt v c μ₂ k b₂ f₂ p₂) :
    b₂ < b₁ ∧ leakage v μ₁ p₁ < leakage v μ₂ p₂ := by
  have hμ1 := (middle_den_pos hk hm1).1
  have hμ2 := hμ1.trans h12
  have hd1 := (middle_den_pos hk hm1).2
  have hinv : 1/(2*μ₂) < 1/(2*μ₁) :=
    div_lt_div_of_pos_left (by norm_num) (by positivity) (by linarith)
  have hb1 := opt_b_mid hvc hk hm1 (h12.le.trans hm2) h1
  have hb2 := opt_b_mid hvc hk (hm1.trans h12.le) hm2 h2
  have hbb : b₂ < b₁ := by
    rw [hb1, hb2]
    exact div_lt_div_of_pos_left (by norm_num) hd1 (by linarith)
  refine ⟨hbb, ?_⟩
  rw [(opt_data hvc hμ1 hk h1).2.2.2.2.1, (opt_data hvc hμ2 hk h2).2.2.2.2.1]
  nlinarith

lemma high_comparative {v c k μ₁ μ₂ b₁ f₁ p₁ b₂ f₂ p₂ : ℝ}
    (hvc : c < v) (hk : 0 < k) (hm1 : muBar v c k ≤ μ₁) (h12 : μ₁ < μ₂)
    (h1 : IsOpt v c μ₁ k b₁ f₁ p₁) (h2 : IsOpt v c μ₂ k b₂ f₂ p₂) :
    b₁ < b₂ ∧ leakage v μ₂ p₂ < leakage v μ₁ p₁ := by
  have hμ1 : 0 < μ₁ := (sub_pos.mpr hvc).trans_le
    ((le_max_left (v-c) (1/(2*k))).trans ((bar_data hvc hk).1.le.trans hm1))
  have hμ2 := hμ1.trans h12
  have hinv : (v-c)/(2*k*μ₂) < (v-c)/(2*k*μ₁) :=
    div_lt_div_of_pos_left (sub_pos.mpr hvc) (by positivity) (by nlinarith)
  have hbb : b₁ < b₂ := by
    rw [opt_b_high hvc hk hm1 h1, opt_b_high hvc hk (hm1.trans h12.le) h2]
    linarith
  refine ⟨hbb, ?_⟩
  rw [(opt_data hvc hμ1 hk h1).2.2.2.2.1, (opt_data hvc hμ2 hk h2).2.2.2.2.1]
  nlinarith

lemma optimum_values {v c μ k b f pd : ℝ} (hvc : c < v) (hμ : 0 < μ) (hk : 0 < k)
    (h : IsOpt v c μ k b f pd) :
    f = (if μ ≤ 1/(2*k) then b else if μ ≤ muBar v c k then μ+b/2 else v+b-c) ∧
    pd = (if μ ≤ 1/(2*k) then v else if μ ≤ muBar v c k
      then v-μ*(2*k*μ-1)/(4*k*μ-1) else (v+c)/2) ∧
    MProfitB v μ k b f pd = (if μ ≤ 1/(2*k) then 1/(2*k)
      else if μ ≤ muBar v c k then μ*k/(2*k-1/(2*μ))
      else (v-c)*(1-(v-c)/(2*μ))+1/(2*k)*(1-(v-c)/(2*μ))^2) := by
  have he := opt_data hvc hμ hk h
  by_cases hlo : μ ≤ 1/(2*k)
  · have ht : T μ k (v-c) = 1 := by rw [T, if_pos hlo]
    simp only [if_pos hlo]
    refine ⟨?_, ?_, ?_⟩
    · rw [he.2.2.1, ht]; ring
    · rw [he.2.2.2.1, ht]; ring
    · rw [he.2.2.2.2.2, ht, U]; ring
  · have hc := (high_constants hk (lt_of_not_ge hlo)).1
    have hd := (middle_den_pos hk (le_of_lt (lt_of_not_ge hlo))).2
    have hkm : 1 < μ*(2*k) := (div_lt_iff₀ (by positivity)).1 (lt_of_not_ge hlo)
    have hpden : 0 < 4*k*μ-1 := by nlinarith
    simp only [if_neg hlo]
    by_cases hbar : μ ≤ muBar v c k
    · have ht := T_mid hvc hk (le_of_lt (lt_of_not_ge hlo)) hbar
      have hbmid := opt_b_mid hvc hk (le_of_lt (lt_of_not_ge hlo)) hbar h
      have hrel := (div_eq_iff hd.ne').1 hbmid.symm
      have hrelScaled : (4*k*μ-1)*b = 2*μ := by
        have hh := congrArg (fun z : ℝ => 2*μ*z) hrel
        field_simp at hh
        nlinarith [hh]
      have hkb : T μ k (v-c) = k*b := by rw [he.1]; field_simp
      simp only [if_pos hbar]
      refine ⟨?_, ?_, ?_⟩
      · rw [he.2.2.1, hkb]
        nlinarith [hrelScaled]
      · rw [he.2.2.2.1, hkb]
        congr 1
        apply (eq_div_iff hpden.ne').2
        linear_combination (-μ*k)*hrelScaled
      · rw [he.2.2.2.2.2, ht, U]
        field_simp
        <;> ring
    · have ht := T_high hvc hk (le_of_not_ge hbar)
      simp only [if_neg hbar]
      refine ⟨?_, ?_, ?_⟩
      · rw [he.2.2.1, ht]
        field_simp
        <;> ring
      · rw [he.2.2.2.1, ht]
        field_simp
        <;> ring
      · rw [he.2.2.2.2.2, ht, U]
        field_simp
        <;> ring

noncomputable def gross (μ b x : ℝ) := (b+x)*share μ x
noncomputable def X (μ a b : ℝ) :=
  if 2*μ ≤ b then 0 else if b ≤ 2*μ-2*a then a else μ-b/2

lemma X_bounds {μ a b : ℝ} (hμ : 0 < μ) (ha : 0 < a) (hb : 0 ≤ b) :
    0 ≤ X μ a b ∧ X μ a b ≤ a ∧ X μ a b ≤ 2*μ := by
  unfold X
  split_ifs <;> exact ⟨by linarith, by linarith, by linarith⟩

lemma gross_nonneg {μ b x : ℝ} (hμ : 0 < μ) (hb : 0 ≤ b) (hx : 0 ≤ x) : 0 ≤ gross μ b x := by
  exact mul_nonneg (add_nonneg hb hx) (share_good hμ hx (le_refl x)).1

lemma gross_scaled {μ b x : ℝ} (hμ : 0 < μ) (hx : x ≤ 2*μ) :
    2*μ*gross μ b x = 2*μ*b+(2*μ-b)*x-x^2 := by
  rw [gross, share_small hμ hx]
  field_simp
  <;> ring

lemma gross_peak {μ a b x : ℝ} (hμ : 0 < μ) (ha : 0 < a) (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hxa : x ≤ a) : gross μ b x ≤ gross μ b (X μ a b) := by
  have hxs := X_bounds hμ ha hb
  have hstar := gross_scaled (b:=b) hμ hxs.2.2
  by_cases hxm : x ≤ 2*μ
  · have hval := gross_scaled (b:=b) hμ hxm
    by_cases hbm : 2*μ ≤ b
    · have he : X μ a b = 0 := by rw [X, if_pos hbm]
      rw [he] at hstar ⊢
      have hp := mul_nonneg hx (by linarith : 0 ≤ b+x-2*μ)
      nlinarith
    · by_cases hba : b ≤ 2*μ-2*a
      · have he : X μ a b = a := by rw [X, if_neg hbm, if_pos hba]
        rw [he] at hstar ⊢
        have hp := mul_nonneg (sub_nonneg.mpr hxa) (by linarith : 0 ≤ 2*μ-b-a-x)
        nlinarith
      · have he : X μ a b = μ-b/2 := by rw [X, if_neg hbm, if_neg hba]
        rw [he] at hstar ⊢
        nlinarith [sq_nonneg (x-(μ-b/2))]
  · have hz : gross μ b x = 0 := by rw [gross, share_large hμ (le_of_not_ge hxm)]; ring
    rw [hz]
    exact gross_nonneg hμ hb hxs.1

lemma gross_value {μ a b : ℝ} (hμ : 0 < μ) (ha : 0 < a) (hb : 0 ≤ b) :
    gross μ b (X μ a b) = if 2*μ ≤ b then b else if b ≤ 2*μ-2*a
      then (a+b)*(1-a/(2*μ)) else (2*μ+b)^2/(8*μ) := by
  unfold X
  split_ifs with hbm hba
  · rw [gross, share_small hμ (by linarith : (0:ℝ) ≤ 2*μ)]
    ring
  · rw [gross, share_small hμ (by linarith : a ≤ 2*μ)]
    ring
  · rw [gross, share_small hμ (by linarith : μ-b/2 ≤ 2*μ)]
    field_simp
    <;> ring

lemma profit_gross {v c μ k b f pd : ℝ} (hμ : 0 < μ) (hbf : b ≤ f)
    (hs : IsSOptB v c μ b f pd) :
    MProfitB v μ k b f pd = gross μ b (f-b)-k*b^2/2 := by
  rw [MProfitB, seller_share hμ hbf hs, gross]
  ring

lemma fixed_profit {v c μ k b : ℝ} (hvc : c < v) (hμ : 0 < μ) (hb : 0 ≤ b) :
    IsGreatest {π : ℝ | ∃ f pd : ℝ, b ≤ f ∧ f ≤ v-c+b ∧ IsSOptB v c μ b f pd ∧
      π = MProfitB v μ k b f pd}
      (if 2*μ ≤ b then b-k*b^2/2 else if b ≤ 2*μ-2*(v-c)
       then (v-c+b)*(1-(v-c)/(2*μ))-k*b^2/2 else (2*μ+b)^2/(8*μ)-k*b^2/2) := by
  let x := X μ (v-c) b
  have hx := X_bounds hμ (sub_pos.mpr hvc) hb
  have hbf : b ≤ b+x := by linarith [hx.1]
  have hs : IsSOptB v c μ b (b+x) (v-x/2) := by
    apply (response hμ hbf).2
    split_ifs with hh <;> nlinarith [hx.2.2]
  have hval : MProfitB v μ k b (b+x) (v-x/2) =
      (if 2*μ ≤ b then b-k*b^2/2 else if b ≤ 2*μ-2*(v-c)
       then (v-c+b)*(1-(v-c)/(2*μ))-k*b^2/2 else (2*μ+b)^2/(8*μ)-k*b^2/2) := by
    rw [profit_gross hμ hbf hs, show b+x-b=x by ring]
    change gross μ b (X μ (v-c) b)-k*b^2/2 = _
    rw [gross_value hμ (sub_pos.mpr hvc) hb]
    split_ifs <;> ring
  refine ⟨⟨b+x, v-x/2, hbf, by linarith [hx.2.1], hs, hval.symm⟩, ?_⟩
  rintro π ⟨f, pd, hbf', hfa', hs', rfl⟩
  rw [← hval, profit_gross hμ hbf hs, profit_gross hμ hbf' hs', show b+x-b=x by ring]
  have hp := gross_peak hμ (sub_pos.mpr hvc) hb (sub_nonneg.mpr hbf')
    (show f-b ≤ v-c by linarith)
  linarith

end LeakBenefitsProof

theorem solution (v c μ k b : ℝ) (hvc : c < v) (hμ : 0 < μ) (hb : 0 ≤ b) :
    IsGreatest
      {π : ℝ | ∃ f pd : ℝ, b ≤ f ∧ f ≤ v - c + b ∧ IsSOptB v c μ b f pd ∧
        π = MProfitB v μ k b f pd}
      (if 2 * μ ≤ b then b - k * b ^ 2 / 2
       else if b ≤ 2 * μ - 2 * (v - c) then
         (v - c + b) * (1 - (v - c) / (2 * μ)) - k * b ^ 2 / 2
       else (2 * μ + b) ^ 2 / (8 * μ) - k * b ^ 2 / 2) := by
  exact LeakBenefitsProof.fixed_profit hvc hμ hb
