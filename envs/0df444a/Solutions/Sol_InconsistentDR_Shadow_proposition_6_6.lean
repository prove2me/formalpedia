-- Prove2me | solution 1 for InconsistentDR.Shadow.proposition_6_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T23:33:37.516855+00:00
-- url     : https://prove2.me/submissions/1cbf4049-45e4-47e8-be4d-245c81050d02

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_FRBSplitting_Weak_Setting
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Theorems.Thm_InconsistentDR_Shadow_proposition_6_2
import Theorems.Thm_InconsistentDR_Shadow_proposition_6_5
import Theorems.Thm_InconsistentDR_Shadow_theorem_5_5
import Theorems.Thm_InconsistentDR_Shadow_eq_68_v_eq_vD
import Theorems.Thm_InconsistentDR_Shadow_eq_75_tendsto
import Theorems.Thm_QuasiFejerOpial_exists_weak_subsequence

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization FRBSplitting.Weak

namespace DR66Aux

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

end DR66Aux

open InconsistentDR.Shadow in
theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf) (hPg : IsResolvent 1 (subgrad g) Pg)
    (v : X) (hv : IsMinNormPt (closure (Set.range fun x => x - drT Pf Pg x)) v)
    (h12 : Standing12 (subgrad f) (subgrad g) Pf Pg)
    (hvR : (0 : X) ∈ closure (setR (subgrad f) (subgrad g)))
    (hZ : (solZ (subgrad f) (subgrad g) v).Nonempty)
    (x : X) :
    (∃ z, IsWeakLimit (fun n => Pf ((drT Pf Pg)^[n] x)) z ∧
      ∀ y, f z + g (z - v) ≤ f y + g (y - v)) ∧
    (∃ w, IsWeakLimit (fun n => Pg (refl Pf ((drT Pf Pg)^[n] x))) w ∧
      ∀ y, f (w + v) + g w ≤ f (y + v) + g y) := by
  have hmaxf := DR66Aux.subgrad_maxmono f Pf hPf
  have hmaxg := DR66Aux.subgrad_maxmono g Pg hPg
  have hvR0 : IsMinNormPt (closure (setR (subgrad f) (subgrad g))) 0 :=
    ⟨hvR, fun c _ => by simp⟩
  have hvD := eq_68_v_eq_vD f g hf hg Pf Pg hPf hPg v hv h12 hvR
  -- a point of `Fix(v + T)` and a point of `K` from a point of `Z`
  obtain ⟨z0, a, ha, b, hb, hab⟩ := hZ
  have hb' : b = v - a := by
    have : b = -(-v + a) := by rw [eq_neg_iff_add_eq_zero]; rw [add_comm]; exact hab
    rw [this]; abel
  have hPfp : Pf (z0 + a) = z0 := DR66Aux.prox_unique f Pf hPf (by rw [add_sub_cancel_left]; exact ha)
  have hrefl : refl Pf (z0 + a) = z0 - a := by
    rw [InconsistentDR.Shadow.refl, hPfp]; module
  have hPgp : Pg (z0 - a) = z0 - v := by
    apply DR66Aux.prox_unique g Pg hPg
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
  have hZ : (solZ (subgrad f) (subgrad g) v).Nonempty := ⟨z0, a, ha, b, hb, hab⟩
  -- Theorem 5.5(ix)
  have h55 := (theorem_5_5 (subgrad f) (subgrad g) hmaxf hmaxg Pf Pg hPf hPg v v 0 hv hvD hvR0
    h12 hfix x).2 (DR66Aux.subgrad_paramono f) (DR66Aux.subgrad_paramono g)
  have e0 : (fun n : ℕ => Pf ((drT Pf Pg)^[n] x) + (n : ℝ) • (0 : X)) =
      fun n : ℕ => Pf ((drT Pf Pg)^[n] x) := by funext n; simp
  rw [e0] at h55
  -- Propositions 6.5(i) and 6.2(ii)
  have h65 := proposition_6_5 f g hf hg Pf Pg hPf hPg v hv h12 hvR hZ x
  simp only at h65
  obtain ⟨⟨hpb, hpmin⟩, -, -⟩ := h65
  have h62 := (proposition_6_2 f g hf hg Pf Pg hPf hPg v hv h12 hvR).2 hZ
  have hclZ : ∀ z, IsWeakClusterPt (fun n => Pf ((drT Pf Pg)^[n] x)) z →
      z ∈ solZ (subgrad f) (subgrad g) v := by
    intro z hz
    rw [h62.2]
    exact hpmin z hz
  have huniq : ∀ z1 z2, IsWeakClusterPt (fun n => Pf ((drT Pf Pg)^[n] x)) z1 →
      IsWeakClusterPt (fun n => Pf ((drT Pf Pg)^[n] x)) z2 → z1 = z2 := fun z1 z2 h1 h2 =>
    DR66Aux.fejer_unique _ _ _ _ h55 (-b) hK z1 z2 (hclZ z1 h1) (hclZ z2 h2) h1 h2
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hpb
  obtain ⟨z, hzlim, hzc⟩ := DR66Aux.weak_conv_of_unique _ R (fun n => hR _ ⟨n, rfl⟩) huniq
  have hzmin := hpmin z hzc
  refine ⟨⟨z, hzlim, hzmin⟩, ⟨z - v, ?_, ?_⟩⟩
  · obtain ⟨hid, hlim⟩ := eq_75_tendsto f g hf hg Pf Pg hPf hPg v hv x
    have hdiff : Tendsto (fun n => Pf ((drT Pf Pg)^[n] x) - Pg (refl Pf ((drT Pf Pg)^[n] x)))
        atTop (𝓝 v) := by
      simpa only [hid] using hlim
    intro u
    have h1 := hzlim u
    have h2 : Tendsto (fun n => inner ℝ (Pf ((drT Pf Pg)^[n] x) -
        Pg (refl Pf ((drT Pf Pg)^[n] x))) u) atTop (𝓝 (inner ℝ v u)) :=
      ((continuous_id.inner continuous_const).tendsto v).comp hdiff
    have h3 := h1.sub h2
    have e1 : ∀ n, inner ℝ (Pf ((drT Pf Pg)^[n] x)) u - inner ℝ (Pf ((drT Pf Pg)^[n] x) -
        Pg (refl Pf ((drT Pf Pg)^[n] x))) u = inner ℝ (Pg (refl Pf ((drT Pf Pg)^[n] x))) u := by
      intro n; rw [inner_sub_left]; ring
    rw [inner_sub_left]
    simpa only [e1] using h3
  · intro y
    have := hzmin (y + v)
    simpa using this
