-- Prove2me | solution 1 for InconsistentDR.Shadow.lemma_6_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T23:33:36.89078+00:00
-- url     : https://prove2.me/submissions/329fa5f1-41f4-4e03-847e-bb055a909dee

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_FRBSplitting_Weak_Setting
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization
import Theorems.Thm_InconsistentDR_Shadow_eq_68_v_eq_vD
import Theorems.Thm_InconsistentDR_Shadow_edom_subset_closure_dom_subgrad

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization FRBSplitting.Weak

namespace DR63Aux

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

/-- Variational inequality for the least-norm point of a convex set. -/
lemma minnorm_vi {C : Set X} (hC : Convex ℝ C) {v : X} (hv : InconsistentDR.Shadow.IsMinNormPt C v)
    {d : X} (hd : d ∈ C) : 0 ≤ ⟪v, d - v⟫_ℝ := by
  by_contra hneg
  push Not at hneg
  set a := ⟪v, d - v⟫_ℝ
  set b := ‖d - v‖ ^ 2
  have hb : 0 ≤ b := by positivity
  set t := min 1 (-a / (b + 1)) with ht
  have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) (by linarith))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htb : t * (b + 1) ≤ -a := by
    have : t ≤ -a / (b + 1) := min_le_right _ _
    rwa [le_div_iff₀ (by linarith)] at this
  have hmem : v + t • (d - v) ∈ C := by
    have : v + t • (d - v) = (1 - t) • v + t • d := by module
    rw [this]; exact hC hv.1 hd (by linarith) ht0.le (by ring)
  have h1 := hv.2 _ hmem
  have h2 : ‖v‖ ^ 2 ≤ ‖v + t • (d - v)‖ ^ 2 := by gcongr
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg ht0.le] at h2
  have : t * (2 * a + t * b) < 0 := by
    apply mul_neg_of_pos_of_neg ht0
    nlinarith
  nlinarith

end DR63Aux

open InconsistentDR.Shadow in
theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf) (hPg : IsResolvent 1 (subgrad g) Pg)
    (v : X) (hv : IsMinNormPt (closure (Set.range fun x => x - drT Pf Pg x)) v)
    (h12 : Standing12 (subgrad f) (subgrad g) Pf Pg)
    (hvR : (0 : X) ∈ closure (setR (subgrad f) (subgrad g)))
    (x y : X) (hy : y ∈ edom f ∧ y - v ∈ edom g) :
    ⟪y - Pf x, v⟫_ℝ ≤ 0 ∧
    f (Pf x) + ((⟪y - Pf x, v + resInv Pf x⟫_ℝ : ℝ) : EReal) ≤ f y ∧
    g (Pg (refl Pf x)) +
        ((⟪y - Pg (refl Pf x) - v, Pf x - Pg (refl Pf x) - v⟫_ℝ +
          ⟪-y + v + Pg (refl Pf x), v + resInv Pf x⟫_ℝ : ℝ) : EReal) ≤ g (y - v) := by
  have hvD := eq_68_v_eq_vD f g hf hg Pf Pg hPf hPg v hv h12 hvR
  have hsub2 : edom f - edom g ⊆ closure (setD (subgrad f) (subgrad g)) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have ha' := edom_subset_closure_dom_subgrad f hf Pf hPf ha
    have hb' := edom_subset_closure_dom_subgrad g hg Pg hPg hb
    exact map_mem_closure₂ continuous_sub ha' hb' (fun x hx y hy => ⟨x, hx, y, hy, rfl⟩)
  have hsub1 : setD (subgrad f) (subgrad g) ⊆ edom f - edom g := by
    rintro _ ⟨a, ⟨u, hu⟩, b, ⟨w, hw⟩, rfl⟩
    exact ⟨a, hu.2.1, b, hw.2.1, rfl⟩
  have hcl : closure (setD (subgrad f) (subgrad g)) = closure (edom f - edom g) := by
    apply le_antisymm (closure_mono hsub1)
    exact closure_minimal hsub2 isClosed_closure
  have hconv : Convex ℝ (closure (setD (subgrad f) (subgrad g))) := by
    rw [hcl]
    exact ((DR63Aux.edom_convex f hf).sub (DR63Aux.edom_convex g hg)).closure
  -- (70): `⟪v, a - b - v⟫ ≥ 0` on `dom f × dom g`
  have h70 : ∀ a ∈ edom f, ∀ b ∈ edom g, 0 ≤ ⟪v, a - b - v⟫_ℝ := fun a ha b hb =>
    DR63Aux.minnorm_vi hconv hvD (hsub2 ⟨a, ha, b, hb, rfl⟩)
  set p := Pf x with hp
  set q := Pg (refl Pf x) with hq
  have hs : resInv Pf x ∈ subgrad f p := by
    have := hPf x; rw [inv_one, one_smul] at this; exact this
  have ht : refl Pf x - q ∈ subgrad g q := by
    have := hPg (refl Pf x); rw [inv_one, one_smul] at this; exact this
  have hpdom : p ∈ edom f := hs.2.1
  have hqdom : q ∈ edom g := ht.2.1
  -- (71a)
  have h71a : ⟪y - p, v⟫_ℝ ≤ 0 := by
    have := h70 p hpdom (y - v) hy.2
    have e : p - (y - v) - v = -(y - p) := by abel
    rw [e, inner_neg_right, real_inner_comm] at this
    linarith
  obtain ⟨Fp, hFp⟩ := DR63Aux.toReal_eq hs.2.1 hs.1
  obtain ⟨Fy, hFy⟩ := DR63Aux.toReal_eq hy.1 (hf.1 y)
  obtain ⟨Gq, hGq⟩ := DR63Aux.toReal_eq ht.2.1 ht.1
  obtain ⟨Gy, hGy⟩ := DR63Aux.toReal_eq hy.2 (hg.1 (y - v))
  refine ⟨h71a, ?_, ?_⟩
  · have h := hs.2.2 y
    rw [hFp, hFy, ← EReal.coe_add] at h
    have h' : Fp + ⟪y - p, resInv Pf x⟫_ℝ ≤ Fy := by exact_mod_cast h
    rw [hFp, hFy, ← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    rw [inner_add_right]
    linarith
  · have h := ht.2.2 (y - v)
    rw [hGq, hGy, ← EReal.coe_add] at h
    have h' : Gq + ⟪y - v - q, refl Pf x - q⟫_ℝ ≤ Gy := by exact_mod_cast h
    have h70b := h70 y hy.1 q hqdom
    rw [hGq, hGy, ← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    have erefl : refl Pf x = (2 : ℝ) • p - x := rfl
    have eres : resInv Pf x = x - p := rfl
    rw [erefl] at h'
    rw [eres]
    have key : ⟪y - q - v, p - q - v⟫_ℝ + ⟪-y + v + q, v + (x - p)⟫_ℝ =
        ⟪y - v - q, (2 : ℝ) • p - x - q⟫_ℝ - 2 * ⟪v, y - q - v⟫_ℝ := by
      have e1 : -y + v + q = -(y - q - v) := by abel
      have e2 : y - v - q = y - q - v := by abel
      rw [e1, e2, inner_neg_left, real_inner_comm (y - q - v) v]
      have e3 : (2 : ℝ) • p - x - q = (p - q - v) + (p - x) + v := by module
      rw [e3, inner_add_right, inner_add_right, inner_add_right]
      have e4 : x - p = -(p - x) := by abel
      rw [e4, inner_neg_right]
      ring
    rw [key]
    linarith
