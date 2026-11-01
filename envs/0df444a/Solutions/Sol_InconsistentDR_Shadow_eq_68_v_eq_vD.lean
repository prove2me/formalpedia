-- Prove2me | solution 1 for InconsistentDR.Shadow.eq_68_v_eq_vD
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T23:33:36.295302+00:00
-- url     : https://prove2.me/submissions/1fc241e2-50f5-4033-8704-e6550d82b069

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization
import Theorems.Thm_InconsistentDR_Shadow_proposition_3_3
import Theorems.Thm_InconsistentDR_Shadow_edom_subset_closure_dom_subgrad

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization

namespace DR68Aux

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

lemma edom_convex (f : X → EReal) (hf : GammaZero f) :
    Convex ℝ (InconsistentDR.Shadow.edom f) := by
  intro a ha b hb s t hs ht hst
  obtain ⟨Fa, hFa⟩ := toReal_eq ha (hf.1 a)
  obtain ⟨Fb, hFb⟩ := toReal_eq hb (hf.1 b)
  have hA : ((a, Fa) : X × ℝ) ∈ {p : X × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} := by simp [hFa]
  have hB : ((b, Fb) : X × ℝ) ∈ {p : X × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} := by simp [hFb]
  have := hf.2.2.1 hA hB hs ht hst
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at this
  intro htop
  change f (s • a + t • b) = ⊤ at htop
  rw [htop, top_le_iff] at this
  exact EReal.coe_ne_top _ this

end DR68Aux

open InconsistentDR.Shadow in
theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf) (hPg : IsResolvent 1 (subgrad g) Pg)
    (v : X) (hv : IsMinNormPt (closure (Set.range fun x => x - drT Pf Pg x)) v)
    (h12 : Standing12 (subgrad f) (subgrad g) Pf Pg)
    (hvR : (0 : X) ∈ closure (setR (subgrad f) (subgrad g))) :
    IsMinNormPt (closure (setD (subgrad f) (subgrad g))) v := by
  have hmaxf := DR68Aux.subgrad_maxmono f Pf hPf
  have hmaxg := DR68Aux.subgrad_maxmono g Pg hPg
  have hvR0 : IsMinNormPt (closure (setR (subgrad f) (subgrad g))) 0 :=
    ⟨hvR, fun c _ => by simp⟩
  -- `cl D = cl (dom f - dom g)` is a nonempty closed convex set
  have hsub1 : setD (subgrad f) (subgrad g) ⊆ edom f - edom g := by
    rintro _ ⟨a, ⟨u, hu⟩, b, ⟨w, hw⟩, rfl⟩
    exact ⟨a, hu.2.1, b, hw.2.1, rfl⟩
  have hsub2 : edom f - edom g ⊆ closure (setD (subgrad f) (subgrad g)) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have ha' := edom_subset_closure_dom_subgrad f hf Pf hPf ha
    have hb' := edom_subset_closure_dom_subgrad g hg Pg hPg hb
    exact map_mem_closure₂ continuous_sub ha' hb' (fun x hx y hy => ⟨x, hx, y, hy, rfl⟩)
  have hcl : closure (setD (subgrad f) (subgrad g)) = closure (edom f - edom g) := by
    apply le_antisymm (closure_mono hsub1)
    exact closure_minimal hsub2 isClosed_closure
  have hconv : Convex ℝ (closure (setD (subgrad f) (subgrad g))) := by
    rw [hcl]
    exact ((DR68Aux.edom_convex f hf).sub (DR68Aux.edom_convex g hg)).closure
  have hne : (closure (setD (subgrad f) (subgrad g))).Nonempty := by
    have h1 := hPf 0
    have h2 := hPg 0
    exact ⟨Pf 0 - Pg 0, subset_closure ⟨Pf 0, ⟨_, h1⟩, Pg 0, ⟨_, h2⟩, rfl⟩⟩
  obtain ⟨vD, hvDmem, hvDinf⟩ := exists_norm_eq_iInf_of_complete_convex hne
    isClosed_closure.isComplete hconv 0
  have hvD : IsMinNormPt (closure (setD (subgrad f) (subgrad g))) vD := by
    refine ⟨hvDmem, fun c hc => ?_⟩
    have h1 : ‖(0 : X) - vD‖ ≤ ‖(0 : X) - c‖ := by
      rw [hvDinf]
      exact ciInf_le (f := fun w : closure (setD (subgrad f) (subgrad g)) => ‖(0 : X) - w‖)
        ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩ ⟨c, hc⟩
    simpa using h1
  obtain ⟨-, hvv, -⟩ := proposition_3_3 (subgrad f) (subgrad g) hmaxf hmaxg Pf Pg hPf hPg
    v vD 0 hv hvD hvR0 h12
  rw [add_zero] at hvv
  rw [hvv]
  exact hvD
