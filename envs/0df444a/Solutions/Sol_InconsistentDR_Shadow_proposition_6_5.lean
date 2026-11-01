-- Prove2me | solution 1 for InconsistentDR.Shadow.proposition_6_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T23:42:39.334288+00:00
-- url     : https://prove2.me/submissions/0c04a736-78ad-43ec-8f10-ab58af05f95a

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_FRBSplitting_Weak_Setting
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Theorems.Thm_InconsistentDR_Shadow_proposition_6_2
import Theorems.Thm_InconsistentDR_Shadow_proposition_6_4
import Theorems.Thm_InconsistentDR_Shadow_corollary_5_7
import Theorems.Thm_InconsistentDR_Shadow_theorem_5_5
import Theorems.Thm_InconsistentDR_Shadow_eq_68_v_eq_vD
import Theorems.Thm_InconsistentDR_Shadow_eq_75_tendsto
import Theorems.Thm_QuasiFejerOpial_exists_weak_subsequence

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization FRBSplitting.Weak

namespace DR65Aux

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

lemma toReal_eq {e : EReal} (h1 : e ≠ ⊤) (h2 : e ≠ ⊥) : ∃ r : ℝ, e = r :=
  ⟨e.toReal, (EReal.coe_toReal h1 h2).symm⟩

lemma subgrad_mono (f : X → EReal) : IsMonotoneOp (subgrad f) := by
  intro x y a b ha hb
  obtain ⟨F, hF⟩ := toReal_eq ha.2.1 ha.1
  obtain ⟨G, hG⟩ := toReal_eq hb.2.1 hb.1
  have h1 := ha.2.2 y
  have h2 := hb.2.2 x
  rw [hF, hG] at h1 h2
  have h1' : F + ⟪y - x, a⟫_ℝ ≤ G := by exact_mod_cast h1
  have h2' : G + ⟪x - y, b⟫_ℝ ≤ F := by exact_mod_cast h2
  have e : ⟪y - x, a⟫_ℝ = -⟪x - y, a⟫_ℝ := by rw [← inner_neg_left, neg_sub]
  rw [inner_sub_right]
  linarith

lemma prox_unique (f : X → EReal) (P : X → X) (hP : IsResolvent 1 (subgrad f) P) {x y : X}
    (hy : x - y ∈ subgrad f y) : P x = y := by
  have hx := hP x
  rw [inv_one, one_smul] at hx
  have := subgrad_mono f _ _ _ _ hx hy
  have e : (x - P x) - (x - y) = -(P x - y) := by abel
  rw [e, inner_neg_right, real_inner_self_eq_norm_sq] at this
  have h0 : ‖P x - y‖ = 0 := by nlinarith [norm_nonneg (P x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

lemma subgrad_maxmono (f : X → EReal) (P : X → X) (hP : IsResolvent 1 (subgrad f) P) :
    IsMaximalMonotone (subgrad f) := by
  refine ⟨subgrad_mono f, fun A' hA' hsub => ?_⟩
  funext x
  ext u
  refine ⟨fun hu => ?_, fun hu => hsub x hu⟩
  have hp := hP (x + u)
  rw [inv_one, one_smul] at hp
  set p := P (x + u)
  have h1 := hA' _ _ _ _ hu (hsub p hp)
  have e : u - (x + u - p) = -(x - p) := by abel
  rw [e, inner_neg_right, real_inner_self_eq_norm_sq] at h1
  have h0 : ‖x - p‖ = 0 := by nlinarith [norm_nonneg (x - p)]
  have hxp : x = p := sub_eq_zero.mp (norm_eq_zero.mp h0)
  have : x + u - p = u := by rw [← hxp]; abel
  rw [this, ← hxp] at hp
  exact hp

lemma subgrad_paramono (f : X → EReal) : InconsistentDR.Shadow.IsParamonotone (subgrad f) := by
  refine ⟨subgrad_mono f, fun x y u w hu hw h0 => ?_⟩
  obtain ⟨F, hF⟩ := toReal_eq hu.2.1 hu.1
  obtain ⟨G, hG⟩ := toReal_eq hw.2.1 hw.1
  have h1 := hu.2.2 y
  have h2 := hw.2.2 x
  rw [hF, hG] at h1 h2
  have h1' : F + ⟪y - x, u⟫_ℝ ≤ G := by exact_mod_cast h1
  have h2' : G + ⟪x - y, w⟫_ℝ ≤ F := by exact_mod_cast h2
  have hc : ⟪x - y, u⟫_ℝ = ⟪x - y, w⟫_ℝ := by rw [inner_sub_right] at h0; linarith
  have e1 : ⟪y - x, u⟫_ℝ = -⟪x - y, u⟫_ℝ := by rw [← inner_neg_left, neg_sub]
  have hFG : G = F - ⟪x - y, u⟫_ℝ := by linarith
  refine ⟨⟨by rw [hF]; exact EReal.coe_ne_bot _, by rw [hF]; exact EReal.coe_ne_top _,
    fun z => ?_⟩, ⟨by rw [hG]; exact EReal.coe_ne_bot _, by rw [hG]; exact EReal.coe_ne_top _,
    fun z => ?_⟩⟩
  · have h := hw.2.2 z
    rw [hG] at h
    rw [hF, ← EReal.coe_add]
    rw [← EReal.coe_add] at h
    have e : F + ⟪z - x, w⟫_ℝ = G + ⟪z - y, w⟫_ℝ := by
      have : ⟪z - y, w⟫_ℝ = ⟪z - x, w⟫_ℝ + ⟪x - y, w⟫_ℝ := by
        rw [← inner_add_left]; congr 1; abel
      rw [this, hFG]; linarith
    rw [e]; exact h
  · have h := hu.2.2 z
    rw [hF] at h
    rw [hG, ← EReal.coe_add]
    rw [← EReal.coe_add] at h
    have e : G + ⟪z - y, u⟫_ℝ = F + ⟪z - x, u⟫_ℝ := by
      have : ⟪z - y, u⟫_ℝ = ⟪z - x, u⟫_ℝ + ⟪x - y, u⟫_ℝ := by
        rw [← inner_add_left]; congr 1; abel
      rw [this, hFG]; ring
    rw [e]; exact h

/-- Fejér monotonicity of a pair with respect to `C₁ × C₂` forces uniqueness of the weak cluster
points of the first component inside `C₁`. -/
lemma fejer_unique (P S : ℕ → X) (C1 C2 : Set X)
    (hfej : InconsistentDR.Shadow.IsFejerPair P S (C1 ×ˢ C2)) (k : X) (hk : k ∈ C2)
    (z1 z2 : X) (h1 : z1 ∈ C1) (h2 : z2 ∈ C1)
    (hc1 : IsWeakClusterPt P z1) (hc2 : IsWeakClusterPt P z2) : z1 = z2 := by
  have hconv : ∀ c ∈ C1 ×ˢ C2, ∃ L, Tendsto (fun n => ‖P n - c.1‖ ^ 2 + ‖S n - c.2‖ ^ 2)
      atTop (𝓝 L) := by
    intro c hc
    have hanti : Antitone (fun n => ‖P n - c.1‖ ^ 2 + ‖S n - c.2‖ ^ 2) :=
      antitone_nat_of_succ_le fun n => hfej c hc n
    exact ⟨_, tendsto_atTop_ciInf hanti ⟨0, by rintro _ ⟨n, rfl⟩; positivity⟩⟩
  obtain ⟨L1, hL1⟩ := hconv (z1, k) ⟨h1, hk⟩
  obtain ⟨L2, hL2⟩ := hconv (z2, k) ⟨h2, hk⟩
  have hid : ∀ n, ⟪P n, z1 - z2⟫_ℝ = ((‖z1‖ ^ 2 - ‖z2‖ ^ 2) -
      ((‖P n - z1‖ ^ 2 + ‖S n - k‖ ^ 2) - (‖P n - z2‖ ^ 2 + ‖S n - k‖ ^ 2))) / 2 := by
    intro n
    rw [norm_sub_sq_real (P n) z1, norm_sub_sq_real (P n) z2, inner_sub_right]
    ring
  have hlim : Tendsto (fun n => ⟪P n, z1 - z2⟫_ℝ) atTop
      (𝓝 (((‖z1‖ ^ 2 - ‖z2‖ ^ 2) - (L1 - L2)) / 2)) := by
    simp only [hid]
    exact ((tendsto_const_nhds.sub (hL1.sub hL2)).div_const 2)
  obtain ⟨φ1, hφ1, hw1⟩ := hc1
  obtain ⟨φ2, hφ2, hw2⟩ := hc2
  have e1 := tendsto_nhds_unique (hw1 (z1 - z2)) (hlim.comp hφ1.tendsto_atTop)
  have e2 := tendsto_nhds_unique (hw2 (z1 - z2)) (hlim.comp hφ2.tendsto_atTop)
  have h0 : ⟪z1 - z2, z1 - z2⟫_ℝ = 0 := by rw [inner_sub_left, e1, e2, sub_self]
  rw [real_inner_self_eq_norm_sq] at h0
  have : ‖z1 - z2‖ = 0 := by nlinarith [norm_nonneg (z1 - z2)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- A bounded sequence whose weak cluster points coincide converges weakly. -/
lemma weak_conv_of_unique [CompleteSpace X] (P : ℕ → X) (R : ℝ) (hR : ∀ n, ‖P n‖ ≤ R)
    (huniq : ∀ z1 z2, IsWeakClusterPt P z1 → IsWeakClusterPt P z2 → z1 = z2) :
    ∃ z, IsWeakLimit P z ∧ IsWeakClusterPt P z := by
  obtain ⟨r, hr, z, hz⟩ := QuasiFejerOpial.exists_weak_subsequence P R hR
  have hzc : IsWeakClusterPt P z := ⟨r, hr, hz⟩
  refine ⟨z, fun u => ?_, hzc⟩
  by_contra hnot
  rw [not_tendsto_iff_exists_frequently_notMem] at hnot
  obtain ⟨s, hs, hfreq⟩ := hnot
  obtain ⟨θ, hθ, hθs⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨ρ, hρ, z', hz'⟩ := QuasiFejerOpial.exists_weak_subsequence (P ∘ θ) R (fun n => hR _)
  have hz'c : IsWeakClusterPt P z' := ⟨θ ∘ ρ, hθ.comp hρ, hz'⟩
  have hzz : z' = z := huniq _ _ hz'c hzc
  subst hzz
  have := (hz' u).eventually hs
  obtain ⟨k, hk⟩ := this.exists
  exact hθs (ρ k) hk

/-- Weak sequential lower semicontinuity of a `Γ₀` function on sublevel sets. -/
lemma weak_lsc [CompleteSpace X] (f : X → EReal) (hf : GammaZero f) {ψ : ℕ → X} {z : X}
    (hψ : IsWeakLimit ψ z) {s : ℝ} (hs : ∃ᶠ k in atTop, f (ψ k) ≤ (s : EReal)) :
    f z ≤ (s : EReal) := by
  obtain ⟨θ, hθ, hθs⟩ := extraction_of_frequently_atTop hs
  set C : Set X := {w | f w ≤ (s : EReal)} with hC
  have hCcl : IsClosed C := hf.2.2.2.isClosed_preimage (s : EReal)
  have hCcv : Convex ℝ C := by
    intro a ha b hb t r ht hr htr
    have hA : ((a, s) : X × ℝ) ∈ {p : X × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} := ha
    have hB : ((b, s) : X × ℝ) ∈ {p : X × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} := hb
    have := hf.2.2.1 hA hB ht hr htr
    simp only [Set.mem_ofPred_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at this
    change f (t • a + r • b) ≤ (s : EReal)
    have e : t * s + r * s = s := by rw [← add_mul, htr, one_mul]
    rwa [e] at this
  have hCne : C.Nonempty := ⟨ψ (θ 0), hθs 0⟩
  obtain ⟨c, hcC, hc⟩ := exists_norm_eq_iInf_of_complete_convex hCne hCcl.isComplete hCcv z
  have hvi := (norm_eq_iInf_iff_real_inner_le_zero hCcv hcC).mp hc
  have h1 : ∀ k, ⟪ψ (θ k), z - c⟫_ℝ ≤ ⟪c, z - c⟫_ℝ := by
    intro k
    have := hvi _ (hθs k)
    rw [real_inner_comm, inner_sub_left] at this
    linarith
  have h2 : Tendsto (fun k => ⟪ψ (θ k), z - c⟫_ℝ) atTop (𝓝 ⟪z, z - c⟫_ℝ) :=
    (hψ (z - c)).comp hθ.tendsto_atTop
  have h3 : ⟪z, z - c⟫_ℝ ≤ ⟪c, z - c⟫_ℝ := le_of_tendsto' h2 h1
  have h4 : ‖z - c‖ ^ 2 ≤ 0 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left]; linarith
  have h5 : z = c := by
    have : ‖z - c‖ = 0 := by nlinarith [norm_nonneg (z - c)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  rw [h5]; exact hcC

/-- Along a weakly convergent sequence, `f` is eventually above any value below `f z`. -/
lemma ev_gt [CompleteSpace X] (f : X → EReal) (hf : GammaZero f) {ψ : ℕ → X} {z : X}
    (hψ : IsWeakLimit ψ z) {b : EReal} (hb : b < f z) : ∀ᶠ n in atTop, b < f (ψ n) := by
  by_cases hbot : b = ⊥
  · subst hbot
    exact Eventually.of_forall fun n => Ne.bot_lt (hf.1 _)
  have htop : b ≠ ⊤ := ne_top_of_lt hb
  obtain ⟨s, rfl⟩ : ∃ s : ℝ, b = s := ⟨b.toReal, (EReal.coe_toReal htop hbot).symm⟩
  by_contra hcon
  rw [not_eventually] at hcon
  have : ∃ᶠ n in atTop, f (ψ n) ≤ (s : EReal) := hcon.mono fun n h => not_lt.mp h
  exact absurd (weak_lsc f hf hψ this) (not_le.mpr hb)

/-- Convergence of the first value sequence from the asymptotic inequality (78). -/
lemma first_tendsto [CompleteSpace X] (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (p q : ℕ → X) (z w : X) (hp : IsWeakLimit p z) (hq : IsWeakLimit q w) (F G : ℝ)
    (hF : f z = F) (hG : g w = G) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hineq : ∀ n : ℕ, 1 ≤ n → f (p n) + g (q n) + ((e n : ℝ) : EReal) ≤ ((F + G : ℝ) : EReal)) :
    Tendsto (fun n => f (p n)) atTop (𝓝 (F : EReal)) := by
  -- finiteness for `n ≥ 1`
  have hfin : ∀ n : ℕ, 1 ≤ n → f (p n) ≠ ⊤ ∧ g (q n) ≠ ⊤ := by
    intro n hn
    have h := hineq n hn
    constructor
    · intro ht
      rw [ht, EReal.top_add_of_ne_bot (hg.1 _), EReal.top_add_of_ne_bot (EReal.coe_ne_bot _),
        top_le_iff] at h
      exact EReal.coe_ne_top _ h
    · intro ht
      rw [ht, EReal.add_top_of_ne_bot (hf.1 _), EReal.top_add_of_ne_bot (EReal.coe_ne_bot _),
        top_le_iff] at h
      exact EReal.coe_ne_top _ h
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · exact ev_gt f hf hp (hF ▸ ha)
  · by_cases htop : a = ⊤
    · subst htop
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact Ne.lt_top (hfin n hn).1
    have hbot : a ≠ ⊥ := ne_bot_of_gt ha
    obtain ⟨s, rfl⟩ : ∃ s : ℝ, a = s := ⟨a.toReal, (EReal.coe_toReal htop hbot).symm⟩
    have hsF : F < s := by exact_mod_cast ha
    set η := (s - F) / 3 with hη
    have hη0 : 0 < η := by rw [hη]; linarith
    have hgev := ev_gt g hg hq (b := ((G - η : ℝ) : EReal)) (by rw [hG]; exact_mod_cast (by linarith))
    have heev : ∀ᶠ n in atTop, -η < e n := he.eventually (lt_mem_nhds (by linarith))
    filter_upwards [eventually_ge_atTop 1, hgev, heev] with n hn hgn hen
    obtain ⟨P, hP⟩ : ∃ P : ℝ, f (p n) = P :=
      ⟨(f (p n)).toReal, (EReal.coe_toReal (hfin n hn).1 (hf.1 _)).symm⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, g (q n) = Q :=
      ⟨(g (q n)).toReal, (EReal.coe_toReal (hfin n hn).2 (hg.1 _)).symm⟩
    have h := hineq n hn
    rw [hP, hQ] at h
    rw [hQ] at hgn
    have h' : P + Q + e n ≤ F + G := by exact_mod_cast h
    have hgn' : G - η < Q := by exact_mod_cast hgn
    rw [hP]
    have : P < s := by linarith
    exact_mod_cast this


/-- Splitting a strict inequality `Y < A + B` in `EReal` through real lower bounds. -/
lemma split_lt (Y : ℝ) {A B : EReal} (hA : A ≠ ⊥) (hB : B ≠ ⊥) (h : (Y : EReal) < A + B) :
    ∃ α β : ℝ, (α : EReal) < A ∧ (β : EReal) < B ∧ Y < α + β := by
  induction A using EReal.rec with
  | bot => exact absurd rfl hA
  | top =>
    induction B using EReal.rec with
    | bot => exact absurd rfl hB
    | top => exact ⟨Y, 1, EReal.coe_lt_top _, EReal.coe_lt_top _, by linarith⟩
    | coe b => exact ⟨Y - b + 2, b - 1, EReal.coe_lt_top _, by exact_mod_cast (by linarith), by linarith⟩
  | coe a =>
    induction B using EReal.rec with
    | bot => exact absurd rfl hB
    | top => exact ⟨a - 1, Y - a + 2, by exact_mod_cast (by linarith), EReal.coe_lt_top _, by linarith⟩
    | coe b =>
      have h' : Y < a + b := by exact_mod_cast h
      refine ⟨a - (a + b - Y) / 3, b - (a + b - Y) / 3, ?_, ?_, by linarith⟩ <;>
        exact_mod_cast (by linarith)

/-- Lower semicontinuity of the sum along `(78)`. -/
lemma sum_le [CompleteSpace X] (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (p q : ℕ → X) (z w : X) (hp : IsWeakLimit p z) (hq : IsWeakLimit q w) (Y : ℝ) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (hineq : ∀ᶠ n in atTop, f (p n) + g (q n) + ((e n : ℝ) : EReal) ≤ (Y : EReal)) :
    f z + g w ≤ (Y : EReal) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨α, β, hα, hβ, hY⟩ := split_lt Y (hf.1 z) (hg.1 w) hcon
  have h1 := ev_gt f hf hp hα
  have h2 := ev_gt g hg hq hβ
  have h3 : ∀ᶠ n in atTop, -((α + β - Y) / 2) < e n := he.eventually (lt_mem_nhds (by linarith))
  obtain ⟨n, hn1, hn2, hn3, hn4⟩ := (h1.and (h2.and (h3.and hineq))).exists
  have hfin1 : f (p n) ≠ ⊤ := by
    intro ht
    rw [ht, EReal.top_add_of_ne_bot (hg.1 _), EReal.top_add_of_ne_bot (EReal.coe_ne_bot _),
      top_le_iff] at hn4
    exact EReal.coe_ne_top _ hn4
  have hfin2 : g (q n) ≠ ⊤ := by
    intro ht
    rw [ht, EReal.add_top_of_ne_bot (hf.1 _), EReal.top_add_of_ne_bot (EReal.coe_ne_bot _),
      top_le_iff] at hn4
    exact EReal.coe_ne_top _ hn4
  obtain ⟨P, hP⟩ := toReal_eq hfin1 (hf.1 _)
  obtain ⟨Q, hQ⟩ := toReal_eq hfin2 (hg.1 _)
  rw [hP, hQ, ← EReal.coe_add, ← EReal.coe_add] at hn4
  rw [hP] at hn1
  rw [hQ] at hn2
  have a1 : α < P := by exact_mod_cast hn1
  have a2 : β < Q := by exact_mod_cast hn2
  have a4 : P + Q + e n ≤ Y := by exact_mod_cast hn4
  linarith

end DR65Aux

open InconsistentDR.Shadow in
theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf) (hPg : IsResolvent 1 (subgrad g) Pg)
    (v : X) (hv : IsMinNormPt (closure (Set.range fun x => x - drT Pf Pg x)) v)
    (h12 : Standing12 (subgrad f) (subgrad g) Pf Pg)
    (hvR : (0 : X) ∈ closure (setR (subgrad f) (subgrad g)))
    (hZ : (solZ (subgrad f) (subgrad g) v).Nonempty)
    (x : X) :
    let μ : EReal := ⨅ y, f y + g (y - v)
    let p : ℕ → X := fun n => Pf ((drT Pf Pg)^[n] x)
    let q : ℕ → X := fun n => Pg (refl Pf ((drT Pf Pg)^[n] x))
    (Bornology.IsBounded (Set.range p) ∧
      ∀ z, IsWeakClusterPt p z → ∀ y, f z + g (z - v) ≤ f y + g (y - v)) ∧
    (Bornology.IsBounded (Set.range q) ∧
      ∀ w, IsWeakClusterPt q w → ∀ y, f (w + v) + g w ≤ f (y + v) + g y) ∧
    (∀ z, IsWeakClusterPt p z →
      Tendsto (fun n => f (p n)) atTop (𝓝 (f z)) ∧
      Tendsto (fun n => g (q n)) atTop (𝓝 (g (z - v))) ∧
      Tendsto (fun n => f (p n) + g (q n)) atTop (𝓝 μ)) := by
  intro μ p q
  have hmaxf := DR65Aux.subgrad_maxmono f Pf hPf
  have hmaxg := DR65Aux.subgrad_maxmono g Pg hPg
  have hvR0 : IsMinNormPt (closure (setR (subgrad f) (subgrad g))) 0 :=
    ⟨hvR, fun c _ => by simp⟩
  have hvD := eq_68_v_eq_vD f g hf hg Pf Pg hPf hPg v hv h12 hvR
  have hZ' := hZ
  obtain ⟨z0, a, ha, b, hb, hab⟩ := hZ'
  have hb' : b = v - a := by
    have : b = -(-v + a) := by rw [eq_neg_iff_add_eq_zero]; rw [add_comm]; exact hab
    rw [this]; abel
  have hPfp : Pf (z0 + a) = z0 :=
    DR65Aux.prox_unique f Pf hPf (by rw [add_sub_cancel_left]; exact ha)
  have hrefl : refl Pf (z0 + a) = z0 - a := by
    rw [InconsistentDR.Shadow.refl, hPfp]; module
  have hPgp : Pg (z0 - a) = z0 - v := by
    apply DR65Aux.prox_unique g Pg hPg
    have : z0 - a - (z0 - v) = b := by rw [hb']; abel
    rw [this]; exact hb
  have hfix : (FixSet fun y => v + drT Pf Pg y).Nonempty := by
    refine ⟨z0 + a, ?_⟩
    show v + drT Pf Pg (z0 + a) = z0 + a
    rw [InconsistentDR.Shadow.drT, hrefl, hPfp, hPgp]; abel
  have hK : -b ∈ solK (subgrad f) (subgrad g) v := by
    refine ⟨z0, ?_, ?_⟩
    · rw [hb']; simpa using ha
    · simpa using hb
  -- boundedness (Corollary 5.7)
  obtain ⟨hpb, hqb⟩ := corollary_5_7 (subgrad f) (subgrad g) hmaxf hmaxg Pf Pg hPf hPg v v 0 hv
    hvD hvR0 h12 rfl hfix x
  -- (75)
  obtain ⟨hid, hlim⟩ := eq_75_tendsto f g hf hg Pf Pg hPf hPg v hv x
  have hdiff : Tendsto (fun n => p n - q n) atTop (𝓝 v) := by
    have e : (fun n => p n - q n) = fun n => (drT Pf Pg)^[n] x - (drT Pf Pg)^[n + 1] x := by
      funext n; exact hid n
    rw [e]; exact hlim
  have hshift : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ z, IsWeakLimit (p ∘ φ) z →
      IsWeakLimit (q ∘ φ) (z - v) := by
    intro φ hφ z hz u
    have h1 := hz u
    have h2 : Tendsto (fun n => inner ℝ (p (φ n) - q (φ n)) u) atTop (𝓝 (inner ℝ v u)) :=
      ((continuous_id.inner continuous_const).tendsto v).comp (hdiff.comp hφ.tendsto_atTop)
    have h3 := h1.sub h2
    have e1 : ∀ n, inner ℝ ((p ∘ φ) n) u - inner ℝ (p (φ n) - q (φ n)) u =
        inner ℝ ((q ∘ φ) n) u := by
      intro n; simp only [Function.comp, inner_sub_left]; ring
    rw [inner_sub_left]
    simpa only [e1] using h3
  have hshift' : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ w, IsWeakLimit (q ∘ φ) w →
      IsWeakLimit (p ∘ φ) (w + v) := by
    intro φ hφ w hw u
    have h1 := hw u
    have h2 : Tendsto (fun n => inner ℝ (p (φ n) - q (φ n)) u) atTop (𝓝 (inner ℝ v u)) :=
      ((continuous_id.inner continuous_const).tendsto v).comp (hdiff.comp hφ.tendsto_atTop)
    have h3 := h1.add h2
    have e1 : ∀ n, inner ℝ ((q ∘ φ) n) u + inner ℝ (p (φ n) - q (φ n)) u =
        inner ℝ ((p ∘ φ) n) u := by
      intro n; simp only [Function.comp, inner_sub_left]; ring
    rw [inner_add_left]
    simpa only [e1] using h3
  -- (78) along subsequences
  have h78 : ∀ y, y ∈ edom f ∧ y - v ∈ edom g → ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → f (p n) + g (q n) + ((e n : ℝ) : EReal) ≤ f y + g (y - v) := by
    intro y hy
    have h64 := proposition_6_4 f g hf hg Pf Pg hPf hPg v hv h12 hvR hZ y hy x
    simp only at h64
    obtain ⟨hε, hδ, h78⟩ := h64
    exact ⟨_, by simpa using hε.add hδ, h78⟩
  -- (i): weak cluster points of `p` minimize `f + g(· - v)`
  have hmin : ∀ z, IsWeakClusterPt p z → ∀ y, f z + g (z - v) ≤ f y + g (y - v) := by
    intro z ⟨φ, hφ, hz⟩ y
    by_cases hy : y ∈ edom f ∧ y - v ∈ edom g
    · obtain ⟨Fy, hFy⟩ := DR65Aux.toReal_eq hy.1 (hf.1 y)
      obtain ⟨Gy, hGy⟩ := DR65Aux.toReal_eq hy.2 (hg.1 _)
      obtain ⟨e, he, hineq⟩ := h78 y hy
      rw [hFy, hGy, ← EReal.coe_add]
      refine DR65Aux.sum_le f g hf hg (p ∘ φ) (q ∘ φ) z (z - v) hz (hshift φ hφ z hz) (Fy + Gy)
        (e ∘ φ) (he.comp hφ.tendsto_atTop) ?_
      filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
      have := hineq (φ n) hn
      rw [hFy, hGy, ← EReal.coe_add] at this
      exact this
    · have htop : f y + g (y - v) = ⊤ := by
        rw [not_and_or] at hy
        rcases hy with h | h
        · have h' : f y = ⊤ := by simpa [edom] using h
          rw [h', EReal.top_add_of_ne_bot (hg.1 _)]
        · have h' : g (y - v) = ⊤ := by simpa [edom] using h
          rw [h', EReal.add_top_of_ne_bot (hf.1 _)]
      rw [htop]; exact le_top
  -- (ii)
  have hminq : ∀ w, IsWeakClusterPt q w → ∀ y, f (w + v) + g w ≤ f (y + v) + g y := by
    intro w ⟨φ, hφ, hw⟩ y
    have := hmin (w + v) ⟨φ, hφ, hshift' φ hφ w hw⟩ (y + v)
    simpa using this
  -- uniqueness of the weak cluster points (Theorem 5.5(ix), as in Proposition 6.6)
  have h55 := (theorem_5_5 (subgrad f) (subgrad g) hmaxf hmaxg Pf Pg hPf hPg v v 0 hv hvD hvR0
    h12 hfix x).2 (DR65Aux.subgrad_paramono f) (DR65Aux.subgrad_paramono g)
  have e0 : (fun n : ℕ => Pf ((drT Pf Pg)^[n] x) + (n : ℝ) • (0 : X)) = p := by
    funext n; simp [p]
  rw [e0] at h55
  have h62 := (proposition_6_2 f g hf hg Pf Pg hPf hPg v hv h12 hvR).2 hZ
  have hclZ : ∀ z, IsWeakClusterPt p z → z ∈ solZ (subgrad f) (subgrad g) v := by
    intro z hz
    rw [h62.2]
    exact hmin z hz
  have huniq : ∀ z1 z2, IsWeakClusterPt p z1 → IsWeakClusterPt p z2 → z1 = z2 :=
    fun z1 z2 h1 h2 =>
      DR65Aux.fejer_unique _ _ _ _ h55 (-b) hK z1 z2 (hclZ z1 h1) (hclZ z2 h2) h1 h2
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hpb
  obtain ⟨zs, hzslim, hzsc⟩ := DR65Aux.weak_conv_of_unique p R (fun n => hR _ ⟨n, rfl⟩) huniq
  refine ⟨⟨hpb, hmin⟩, ⟨hqb, hminq⟩, fun z hz => ?_⟩
  -- (iii)–(v)
  have hzeq : z = zs := huniq _ _ hz hzsc
  subst hzeq
  have hzlim := hzslim
  have hqlim : IsWeakLimit q (z - v) := by
    have := hshift id strictMono_id z hzlim
    simpa using this
  have hzmin := hmin z hz
  have hzx0 := hzmin z0
  obtain ⟨F0, hF0⟩ := DR65Aux.toReal_eq ha.2.1 ha.1
  obtain ⟨G0, hG0⟩ := DR65Aux.toReal_eq hb.2.1 hb.1
  rw [hF0, hG0, ← EReal.coe_add] at hzx0
  have hfz : f z ≠ ⊤ := by
    intro ht; rw [ht, EReal.top_add_of_ne_bot (hg.1 _), top_le_iff] at hzx0
    exact EReal.coe_ne_top _ hzx0
  have hgz : g (z - v) ≠ ⊤ := by
    intro ht; rw [ht, EReal.add_top_of_ne_bot (hf.1 _), top_le_iff] at hzx0
    exact EReal.coe_ne_top _ hzx0
  obtain ⟨F, hF⟩ := DR65Aux.toReal_eq hfz (hf.1 z)
  obtain ⟨G, hG⟩ := DR65Aux.toReal_eq hgz (hg.1 _)
  obtain ⟨e, he, hineq0⟩ := h78 z ⟨hfz, hgz⟩
  have hineq : ∀ n : ℕ, 1 ≤ n →
      f (p n) + g (q n) + ((e n : ℝ) : EReal) ≤ ((F + G : ℝ) : EReal) := by
    intro n hn
    have := hineq0 n hn
    rwa [hF, hG, ← EReal.coe_add] at this
  have hfp := DR65Aux.first_tendsto f g hf hg _ _ z (z - v) hzlim hqlim F G hF hG e he hineq
  have hgq := DR65Aux.first_tendsto g f hg hf _ _ (z - v) z hqlim hzlim G F hG hF e he
    (fun n hn => by rw [add_comm G F, add_comm (g _)]; exact hineq n hn)
  have hmu : f z + g (z - v) = μ :=
    le_antisymm (le_iInf hzmin) (iInf_le (fun y => f y + g (y - v)) z)
  refine ⟨by rw [hF]; exact hfp, by rw [hG]; exact hgq, ?_⟩
  rw [← hmu, hF, hG]
  have hc := EReal.continuousAt_add (p := ((F : EReal), (G : EReal)))
    (Or.inl (EReal.coe_ne_top F)) (Or.inl (EReal.coe_ne_bot F))
  exact hc.tendsto.comp (hfp.prodMk_nhds hgq)
