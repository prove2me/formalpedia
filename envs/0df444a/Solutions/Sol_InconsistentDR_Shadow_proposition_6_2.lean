-- Prove2me | solution 1 for InconsistentDR.Shadow.proposition_6_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T23:39:32.523387+00:00
-- url     : https://prove2.me/submissions/c38ccd56-b410-4a9f-ad15-d7b2c8afe410

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_FRBSplitting_Weak_Setting
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization
import Theorems.Thm_InconsistentDR_Shadow_eq_68_v_eq_vD
import Theorems.Thm_InconsistentDR_Shadow_theorem_4_3
import Theorems.Thm_InconsistentDR_Shadow_proposition_2_7

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization FRBSplitting.Weak

namespace DR62Aux

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

/-- `c + e ≤ t ↔ e ≤ t - c` for real `c, t` and `e ≠ ⊥`. -/
lemma coe_add_le_iff (c t : ℝ) {e : EReal} (he : e ≠ ⊥) :
    (c : EReal) + e ≤ t ↔ e ≤ ((t - c : ℝ) : EReal) := by
  induction e using EReal.rec with
  | bot => exact absurd rfl he
  | top => simp only [EReal.coe_add_top, top_le_iff, EReal.coe_ne_top]
  | coe r =>
    rw [← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

/-- The translate `g(· - v)` is in `Γ₀`. -/
lemma gammaZero_translate (g : X → EReal) (hg : GammaZero g) (v : X) :
    GammaZero (fun x => g (x - v)) := by
  obtain ⟨hb, ⟨x0, hx0⟩, hc, hl⟩ := hg
  refine ⟨fun x => hb _, ⟨x0 + v, by simpa using hx0⟩, ?_, ?_⟩
  · intro p hp q hq s t hs ht hst
    have hp' : ((p.1 - v, p.2) : X × ℝ) ∈ {p : X × ℝ | g p.1 ≤ ((p.2 : ℝ) : EReal)} := hp
    have hq' : ((q.1 - v, q.2) : X × ℝ) ∈ {p : X × ℝ | g p.1 ≤ ((p.2 : ℝ) : EReal)} := hq
    have := hc hp' hq' hs ht hst
    show g ((s • p + t • q).1 - v) ≤ (((s • p + t • q).2 : ℝ) : EReal)
    have e : (s • p + t • q).1 - v = s • (p.1 - v) + t • (q.1 - v) := by
      simp only [Prod.fst_add, Prod.smul_fst]
      rw [smul_sub, smul_sub]
      have : v = (s + t) • v := by rw [hst, one_smul]
      conv_lhs => rw [this]
      rw [add_smul]; abel
    rw [e]
    simpa using this
  · exact hl.comp (continuous_id.sub continuous_const)

/-- The linear perturbation `-⟪·, v⟫ + f` is in `Γ₀`. -/
lemma gammaZero_lin (f : X → EReal) (hf : GammaZero f) (v : X) :
    GammaZero (fun x => ((-⟪x, v⟫_ℝ : ℝ) : EReal) + f x) := by
  obtain ⟨hb, ⟨x0, hx0⟩, hc, hl⟩ := hf
  refine ⟨fun x => ?_, ⟨x0, ?_⟩, ?_, ?_⟩
  · show ((-⟪x, v⟫_ℝ : ℝ) : EReal) + f x ≠ ⊥
    exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, hb x⟩
  · obtain ⟨F, hF⟩ := toReal_eq hx0 (hb x0)
    show ((-⟪x0, v⟫_ℝ : ℝ) : EReal) + f x0 ≠ ⊤
    rw [hF, ← EReal.coe_add]; exact EReal.coe_ne_top _
  · intro p hp q hq s t hs ht hst
    have hp1 : f p.1 ≤ ((p.2 - -⟪p.1, v⟫_ℝ : ℝ) : EReal) := (coe_add_le_iff _ _ (hb _)).mp hp
    have hq1 : f q.1 ≤ ((q.2 - -⟪q.1, v⟫_ℝ : ℝ) : EReal) := (coe_add_le_iff _ _ (hb _)).mp hq
    have hp' : ((p.1, p.2 - -⟪p.1, v⟫_ℝ) : X × ℝ) ∈ {p : X × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} :=
      hp1
    have hq' : ((q.1, q.2 - -⟪q.1, v⟫_ℝ) : X × ℝ) ∈ {p : X × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} :=
      hq1
    have := hc hp' hq' hs ht hst
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at this
    show ((-⟪(s • p + t • q).1, v⟫_ℝ : ℝ) : EReal) + f (s • p + t • q).1 ≤
      (((s • p + t • q).2 : ℝ) : EReal)
    rw [coe_add_le_iff _ _ (hb _)]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    refine this.trans (le_of_eq ?_)
    congr 1
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  · refine LowerSemicontinuous.add' ?_ hl (fun x => ?_)
    · exact (continuous_coe_real_ereal.comp
        ((continuous_id.inner continuous_const).neg)).lowerSemicontinuous
    · apply EReal.continuousAt_add
      · left; exact EReal.coe_ne_top _
      · left; exact EReal.coe_ne_bot _

lemma subgrad_translate (g : X → EReal) (v x y : X) :
    y ∈ subgrad (fun x => g (x - v)) x ↔ y ∈ subgrad g (x - v) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun u => ?_⟩
    have := h3 (u + v)
    simp only [add_sub_cancel_right] at this
    have e : u + v - x = u - (x - v) := by abel
    rwa [e] at this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun u => ?_⟩
    have := h3 (u - v)
    have e : u - v - (x - v) = u - x := by abel
    rwa [e] at this

lemma subgrad_lin (f : X → EReal) (hf : ∀ x, f x ≠ ⊥) (v x y : X) :
    y ∈ subgrad (fun x => ((-⟪x, v⟫_ℝ : ℝ) : EReal) + f x) x ↔ y + v ∈ subgrad f x := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    beta_reduce at h1 h2 h3
    have hfx : f x ≠ ⊤ := by
      intro h; apply h2; rw [h]; simp
    obtain ⟨F, hF⟩ := toReal_eq hfx (hf x)
    refine ⟨hf x, hfx, fun u => ?_⟩
    have := h3 u
    rw [hF] at this ⊢
    induction h : f u using EReal.rec with
    | bot => exact absurd h (hf u)
    | top => exact le_top
    | coe r =>
      rw [h, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add] at this
      rw [← EReal.coe_add]
      have h' : -⟪x, v⟫_ℝ + F + ⟪u - x, y⟫_ℝ ≤ -⟪u, v⟫_ℝ + r := by exact_mod_cast this
      apply EReal.coe_le_coe_iff.mpr
      simp only [inner_add_right, inner_sub_left] at h' ⊢
      linarith
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨F, hF⟩ := toReal_eq h2 h1
    refine ⟨?_, ?_, fun u => ?_⟩ <;> beta_reduce
    · rw [hF, ← EReal.coe_add]; exact EReal.coe_ne_bot _
    · rw [hF, ← EReal.coe_add]; exact EReal.coe_ne_top _
    have := h3 u
    rw [hF] at this ⊢
    induction h : f u using EReal.rec with
    | bot => exact absurd h (hf u)
    | top => rw [EReal.coe_add_top]; exact le_top
    | coe r =>
      rw [h, ← EReal.coe_add] at this
      rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]
      have h' : F + ⟪u - x, y + v⟫_ℝ ≤ r := by exact_mod_cast this
      apply EReal.coe_le_coe_iff.mpr
      simp only [inner_add_right, inner_sub_left] at h' ⊢
      linarith

end DR62Aux

open InconsistentDR.Shadow in
theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf) (hPg : IsResolvent 1 (subgrad g) Pg)
    (v : X) (hv : IsMinNormPt (closure (Set.range fun x => x - drT Pf Pg x)) v)
    (h12 : Standing12 (subgrad f) (subgrad g) Pf Pg)
    (hvR : (0 : X) ∈ closure (setR (subgrad f) (subgrad g))) :
    solZ (subgrad f) (subgrad g) v =
        {x | ∃ a ∈ subgrad f x, ∃ b ∈ subgrad g (x - v), a + b = 0} ∧
    ((solZ (subgrad f) (subgrad g) v).Nonempty →
      solZ (subgrad f) (subgrad g) v =
          {x | ∀ y, ((-⟪x, v⟫_ℝ : ℝ) : EReal) + f x + g (x - v) ≤
            ((-⟪y, v⟫_ℝ : ℝ) : EReal) + f y + g (y - v)} ∧
        solZ (subgrad f) (subgrad g) v = {x | ∀ y, f x + g (x - v) ≤ f y + g (y - v)}) := by
  have hmaxf := DR62Aux.subgrad_maxmono f Pf hPf
  have hmaxg := DR62Aux.subgrad_maxmono g Pg hPg
  have hvR0 : IsMinNormPt (closure (setR (subgrad f) (subgrad g))) 0 :=
    ⟨hvR, fun c _ => by simp⟩
  have hvD := eq_68_v_eq_vD f g hf hg Pf Pg hPf hPg v hv h12 hvR
  have h43 := (theorem_4_3 (subgrad f) (subgrad g) hmaxf hmaxg Pf Pg hPf hPg v v 0 hv hvD hvR0
    h12).2 rfl
  have hi : solZ (subgrad f) (subgrad g) v =
      {x | ∃ a ∈ subgrad f x, ∃ b ∈ subgrad g (x - v), a + b = 0} := by
    rw [← h43]
    ext x
    simp only [Set.mem_ofPred_eq, neg_zero, zero_add]
  refine ⟨hi, fun hZ => ⟨?_, ?_⟩⟩
  · -- `Z = argmin (-⟪·, v⟫ + f + g(· - v))`
    set f' : X → EReal := fun x => ((-⟪x, v⟫_ℝ : ℝ) : EReal) + f x with hf'
    set g' : X → EReal := fun x => g (x - v) with hg'
    have hZeq : solZ (subgrad f) (subgrad g) v =
        {x | ∃ a ∈ subgrad f' x, ∃ b ∈ subgrad g' x, a + b = 0} := by
      ext x
      simp only [solZ, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨a, ha, b, hb, hab⟩
        refine ⟨a - v, ?_, b, (DR62Aux.subgrad_translate g v x b).mpr hb, ?_⟩
        · rw [DR62Aux.subgrad_lin f hf.1]; simpa using ha
        · rw [← hab]; abel
      · rintro ⟨a, ha, b, hb, hab⟩
        refine ⟨a + v, (DR62Aux.subgrad_lin f hf.1 v x a).mp ha, b,
          (DR62Aux.subgrad_translate g v x b).mp hb, ?_⟩
        rw [← hab]; abel
    have hzer : ∃ x, ∃ a ∈ subgrad f' x, ∃ b ∈ subgrad g' x, a + b = 0 := by
      obtain ⟨x, hx⟩ := hZ
      rw [hZeq] at hx
      exact ⟨x, hx⟩
    obtain ⟨h1, h2⟩ := proposition_2_7 f' g' (DR62Aux.gammaZero_lin f hf v)
      (DR62Aux.gammaZero_translate g hg v) hzer
    rw [hZeq, ← h2, ← h1]
  · -- `Z = argmin (f + g(· - v))`
    set g' : X → EReal := fun x => g (x - v) with hg'
    have hZeq : solZ (subgrad f) (subgrad g) v =
        {x | ∃ a ∈ subgrad f x, ∃ b ∈ subgrad g' x, a + b = 0} := by
      rw [hi]
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨a, ha, b, hb, hab⟩
        exact ⟨a, ha, b, (DR62Aux.subgrad_translate g v x b).mpr hb, hab⟩
      · rintro ⟨a, ha, b, hb, hab⟩
        exact ⟨a, ha, b, (DR62Aux.subgrad_translate g v x b).mp hb, hab⟩
    have hzer : ∃ x, ∃ a ∈ subgrad f x, ∃ b ∈ subgrad g' x, a + b = 0 := by
      obtain ⟨x, hx⟩ := hZ
      rw [hZeq] at hx
      exact ⟨x, hx⟩
    obtain ⟨h1, h2⟩ := proposition_2_7 f g' hf (DR62Aux.gammaZero_translate g hg v) hzer
    rw [hZeq, ← h2, ← h1]
