-- Prove2me | solution 1 for InconsistentDR.Shadow.proposition_6_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T23:36:56.426736+00:00
-- url     : https://prove2.me/submissions/e86847d9-aa84-47dd-b07c-37fb99550975

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_FRBSplitting_Weak_Setting
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization
import Theorems.Thm_InconsistentDR_Shadow_eq_68_v_eq_vD
import Theorems.Thm_InconsistentDR_Shadow_edom_subset_closure_dom_subgrad
import Theorems.Thm_InconsistentDR_Shadow_lemma_6_3
import Theorems.Thm_InconsistentDR_Shadow_corollary_5_7
import Theorems.Thm_InconsistentDR_Shadow_eq_75_tendsto

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization FRBSplitting.Weak

namespace DR64Aux


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


lemma prox_unique (f : X → EReal) (P : X → X) (hP : IsResolvent 1 (subgrad f) P) {x y : X}
    (hy : x - y ∈ subgrad f y) : P x = y := by
  have hx := hP x
  rw [inv_one, one_smul] at hx
  have := subgrad_mono f _ _ _ _ hx hy
  have e : (x - P x) - (x - y) = -(P x - y) := by abel
  rw [e, inner_neg_right, real_inner_self_eq_norm_sq] at this
  have h0 : ‖P x - y‖ = 0 := by nlinarith [norm_nonneg (P x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)


/-- Monotonicity of the subdifferential. -/
lemma subgrad_mono2 (f : X → EReal) {x y a b : X} (ha : a ∈ subgrad f x) (hb : b ∈ subgrad f y) :
    0 ≤ ⟪x - y, a - b⟫_ℝ := by
  obtain ⟨F, hF⟩ : ∃ r : ℝ, f x = r := ⟨(f x).toReal, (EReal.coe_toReal ha.2.1 ha.1).symm⟩
  obtain ⟨G, hG⟩ : ∃ r : ℝ, f y = r := ⟨(f y).toReal, (EReal.coe_toReal hb.2.1 hb.1).symm⟩
  have h1 := ha.2.2 y
  have h2 := hb.2.2 x
  rw [hF, hG] at h1
  rw [hF, hG] at h2
  have h1' : F + ⟪y - x, a⟫_ℝ ≤ G := by exact_mod_cast h1
  have h2' : G + ⟪x - y, b⟫_ℝ ≤ F := by exact_mod_cast h2
  have e : ⟪y - x, a⟫_ℝ = -⟪x - y, a⟫_ℝ := by rw [← inner_neg_left, neg_sub]
  rw [inner_sub_right]
  linarith

/-- The proximal map is firmly nonexpansive. -/
lemma prox_fne (f : X → EReal) (P : X → X) (hP : IsResolvent 1 (subgrad f) P) (x y : X) :
    ‖P x - P y‖ ^ 2 ≤ ⟪P x - P y, x - y⟫_ℝ := by
  have hx := hP x
  have hy := hP y
  rw [inv_one, one_smul] at hx hy
  have := subgrad_mono2 f hx hy
  have e : (x - P x) - (y - P y) = (x - y) - (P x - P y) := by abel
  rw [e, inner_sub_right, real_inner_self_eq_norm_sq] at this
  linarith

/-- The reflected proximal map is nonexpansive. -/
lemma refl_nonexp (f : X → EReal) (P : X → X) (hP : IsResolvent 1 (subgrad f) P) (x y : X) :
    ‖InconsistentDR.Shadow.refl P x - InconsistentDR.Shadow.refl P y‖ ≤ ‖x - y‖ := by
  have h := prox_fne f P hP x y
  have e : InconsistentDR.Shadow.refl P x - InconsistentDR.Shadow.refl P y =
      (2 : ℝ) • (P x - P y) - (x - y) := by
    simp only [InconsistentDR.Shadow.refl]; module
  have h2 : ‖InconsistentDR.Shadow.refl P x - InconsistentDR.Shadow.refl P y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [e, norm_sub_sq_real, norm_smul, real_inner_smul_left, mul_pow]
    norm_num
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- The Douglas–Rachford operator of two proximal maps is firmly nonexpansive. -/
lemma drT_fne (f g : X → EReal) (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf)
    (hPg : IsResolvent 1 (subgrad g) Pg) (x y : X) :
    ‖InconsistentDR.Shadow.drT Pf Pg x - InconsistentDR.Shadow.drT Pf Pg y‖ ^ 2 +
      ‖(x - InconsistentDR.Shadow.drT Pf Pg x) - (y - InconsistentDR.Shadow.drT Pf Pg y)‖ ^ 2
      ≤ ‖x - y‖ ^ 2 := by
  open InconsistentDR.Shadow in
  have hN : ‖refl Pg (refl Pf x) - refl Pg (refl Pf y)‖ ≤ ‖x - y‖ :=
    (refl_nonexp g Pg hPg _ _).trans (refl_nonexp f Pf hPf x y)
  open InconsistentDR.Shadow in
  have e1 : drT Pf Pg x - drT Pf Pg y =
      (1 / 2 : ℝ) • ((x - y) + (refl Pg (refl Pf x) - refl Pg (refl Pf y))) := by
    simp only [InconsistentDR.Shadow.drT, InconsistentDR.Shadow.refl]; module
  open InconsistentDR.Shadow in
  have e2 : (x - drT Pf Pg x) - (y - drT Pf Pg y) =
      (1 / 2 : ℝ) • ((x - y) - (refl Pg (refl Pf x) - refl Pg (refl Pf y))) := by
    simp only [InconsistentDR.Shadow.drT, InconsistentDR.Shadow.refl]; module
  rw [e1, e2]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hN 2
  generalize x - y = a at h2 ⊢
  generalize InconsistentDR.Shadow.refl Pg (InconsistentDR.Shadow.refl Pf x) -
    InconsistentDR.Shadow.refl Pg (InconsistentDR.Shadow.refl Pf y) = b at h2 ⊢
  rw [norm_smul, norm_smul, mul_pow, mul_pow, norm_add_sq_real, norm_sub_sq_real]
  have : ‖(1 / 2 : ℝ)‖ ^ 2 = 1 / 4 := by norm_num
  rw [this]
  nlinarith


/-- On `Fix(v + T)` the iterates move by `-v` ([13, Proposition 2.5]). -/
lemma fix_iter [CompleteSpace X] (T : X → X)
    (hfne : ∀ x y, ‖T x - T y‖ ^ 2 + ‖(x - T x) - (y - T y)‖ ^ 2 ≤ ‖x - y‖ ^ 2)
    (v : X) (hv : ∀ w, ‖v‖ ≤ ‖w - T w‖) (p : X) (hp : v + T p = p) :
    ∀ n : ℕ, T^[n] p = p - (n : ℝ) • v := by
  have step : ∀ q, v + T q = q → v + T (q - v) = q - v := by
    intro q hq
    have hTq : T q = q - v := eq_sub_of_add_eq' hq
    have h := hfne q (q - v)
    rw [hTq, sub_sub_cancel] at h
    set w := q - v - T (q - v) with hw
    have hvw := hv (q - v)
    rw [← hw] at hvw
    have h2 : ‖v‖ ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvw 2
    have h3 : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w)]
    have h5 : q - v - T (q - v) = v := (sub_eq_zero.mp (norm_eq_zero.mp h3)).symm
    calc v + T (q - v) = v + (q - v - (q - v - T (q - v))) := by abel
      _ = q - v := by rw [h5]; abel
  have key : ∀ n : ℕ, v + T (p - (n : ℝ) • v) = p - (n : ℝ) • v := by
    intro n
    induction n with
    | zero => simpa using hp
    | succ k ih =>
      have := step _ ih
      have e : p - ((k + 1 : ℕ) : ℝ) • v = p - (k : ℝ) • v - v := by push_cast; module
      rw [e]; exact this
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have := key k
    have e : T (p - (k : ℝ) • v) = p - (k : ℝ) • v - v := eq_sub_of_add_eq' this
    rw [e]; push_cast; module

lemma iter_nonexp (T : X → X) (hne : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (x y : X) :
    ∀ n : ℕ, ‖T^[n] x - T^[n] y‖ ≤ ‖x - y‖ := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (hne _ _).trans ih

lemma inner_tendsto_zero (a b : ℕ → X) (M : ℝ) (ha : ∀ n, ‖a n‖ ≤ M)
    (hb : Tendsto b atTop (𝓝 0)) : Tendsto (fun n => ⟪a n, b n⟫_ℝ) atTop (𝓝 0) := by
  have hb' : Tendsto (fun n => M * ‖b n‖) atTop (𝓝 0) := by
    have := (hb.norm).const_mul M
    simpa using this
  refine squeeze_zero_norm (fun n => ?_) hb'
  rw [Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (ha n) (norm_nonneg _))

end DR64Aux

open InconsistentDR.Shadow in
theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf) (hPg : IsResolvent 1 (subgrad g) Pg)
    (v : X) (hv : IsMinNormPt (closure (Set.range fun x => x - drT Pf Pg x)) v)
    (h12 : Standing12 (subgrad f) (subgrad g) Pf Pg)
    (hvR : (0 : X) ∈ closure (setR (subgrad f) (subgrad g)))
    (hZ : (solZ (subgrad f) (subgrad g) v).Nonempty)
    (y : X) (hy : y ∈ edom f ∧ y - v ∈ edom g) (x : X) :
    let ε : ℕ → ℝ := fun n =>
      ⟪y - Pg (refl Pf ((drT Pf Pg)^[n] x)) - v,
        Pf ((drT Pf Pg)^[n] x) - Pg (refl Pf ((drT Pf Pg)^[n] x)) - v⟫_ℝ
    let δ : ℕ → ℝ := fun n =>
      ⟪Pf ((drT Pf Pg)^[n] x) - Pg (refl Pf ((drT Pf Pg)^[n] x)) - v,
        Pf ((drT Pf Pg)^[n] x) - ((drT Pf Pg)^[n] x + (n : ℝ) • v)⟫_ℝ
    Tendsto ε atTop (𝓝 0) ∧ Tendsto δ atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n →
        f (Pf ((drT Pf Pg)^[n] x)) + g (Pg (refl Pf ((drT Pf Pg)^[n] x))) +
            ((ε n + δ n : ℝ) : EReal) ≤ f y + g (y - v) := by
  intro ε δ
  have hmaxf := DR64Aux.subgrad_maxmono f Pf hPf
  have hmaxg := DR64Aux.subgrad_maxmono g Pg hPg
  have hvR0 : IsMinNormPt (closure (setR (subgrad f) (subgrad g))) 0 :=
    ⟨hvR, fun c _ => by simp⟩
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
    exact ((DR64Aux.edom_convex f hf).sub (DR64Aux.edom_convex g hg)).closure
  -- a point of `Fix(v + T)` from a point of `Z`
  obtain ⟨z0, a, ha, b, hb, hab⟩ := hZ
  have hb' : b = v - a := by
    have : b = -(-v + a) := by rw [eq_neg_iff_add_eq_zero]; rw [add_comm]; exact hab
    rw [this]; abel
  have hPfp : Pf (z0 + a) = z0 :=
    DR64Aux.prox_unique f Pf hPf (by rw [add_sub_cancel_left]; exact ha)
  have hrefl : refl Pf (z0 + a) = z0 - a := by
    rw [InconsistentDR.Shadow.refl, hPfp]; module
  have hPgp : Pg (z0 - a) = z0 - v := by
    apply DR64Aux.prox_unique g Pg hPg
    have : z0 - a - (z0 - v) = b := by rw [hb']; abel
    rw [this]; exact hb
  have hp0 : v + drT Pf Pg (z0 + a) = z0 + a := by
    rw [InconsistentDR.Shadow.drT, hrefl, hPfp, hPgp]; abel
  have hfix : (FixSet fun y => v + drT Pf Pg y).Nonempty := ⟨z0 + a, hp0⟩
  -- boundedness of the shadows (Corollary 5.7) and of `Tⁿx + n v`
  obtain ⟨hpb, hqb⟩ := corollary_5_7 (subgrad f) (subgrad g) hmaxf hmaxg Pf Pg hPf hPg v v 0 hv
    hvD hvR0 h12 rfl hfix x
  obtain ⟨R1, hR1⟩ := isBounded_iff_forall_norm_le.mp hpb
  obtain ⟨R2, hR2⟩ := isBounded_iff_forall_norm_le.mp hqb
  have hfne := DR64Aux.drT_fne f g Pf Pg hPf hPg
  have hvmin : ∀ w, ‖v‖ ≤ ‖w - drT Pf Pg w‖ := fun w => hv.2 _ (subset_closure ⟨w, rfl⟩)
  have hit := DR64Aux.fix_iter (drT Pf Pg) hfne v hvmin _ hp0
  have hne : ∀ u w, ‖drT Pf Pg u - drT Pf Pg w‖ ≤ ‖u - w‖ := by
    intro u w
    have h := hfne u w
    have h2 : ‖drT Pf Pg u - drT Pf Pg w‖ ^ 2 ≤ ‖u - w‖ ^ 2 := by
      nlinarith [sq_nonneg ‖(u - drT Pf Pg u) - (w - drT Pf Pg w)‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  have hbT : ∀ n : ℕ, ‖(drT Pf Pg)^[n] x + (n : ℝ) • v‖ ≤ ‖z0 + a‖ + ‖x - (z0 + a)‖ := by
    intro n
    have h1 := DR64Aux.iter_nonexp (drT Pf Pg) hne x (z0 + a) n
    rw [hit n] at h1
    have e : (drT Pf Pg)^[n] x + (n : ℝ) • v =
        (z0 + a) + ((drT Pf Pg)^[n] x - (z0 + a - (n : ℝ) • v)) := by abel
    rw [e]
    exact (norm_add_le _ _).trans (by linarith)
  -- (75)
  obtain ⟨hid, hlim⟩ := eq_75_tendsto f g hf hg Pf Pg hPf hPg v hv x
  have hdiff : Tendsto (fun n => Pf ((drT Pf Pg)^[n] x) - Pg (refl Pf ((drT Pf Pg)^[n] x)) - v)
      atTop (𝓝 0) := by
    have : Tendsto (fun n => Pf ((drT Pf Pg)^[n] x) - Pg (refl Pf ((drT Pf Pg)^[n] x)))
        atTop (𝓝 v) := by simpa only [hid] using hlim
    simpa using this.sub_const v
  refine ⟨?_, ?_, ?_⟩
  · -- `εₙ → 0`
    apply DR64Aux.inner_tendsto_zero _ _ (‖y‖ + R2 + ‖v‖) (fun n => ?_) hdiff
    have := hR2 _ ⟨n, rfl⟩
    calc ‖y - Pg (refl Pf ((drT Pf Pg)^[n] x)) - v‖
        ≤ ‖y - Pg (refl Pf ((drT Pf Pg)^[n] x))‖ + ‖v‖ := norm_sub_le _ _
      _ ≤ ‖y‖ + ‖Pg (refl Pf ((drT Pf Pg)^[n] x))‖ + ‖v‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖y‖ + R2 + ‖v‖ := by linarith
  · -- `δₙ → 0`
    have := DR64Aux.inner_tendsto_zero (fun n => Pf ((drT Pf Pg)^[n] x) -
      ((drT Pf Pg)^[n] x + (n : ℝ) • v)) _ (R1 + (‖z0 + a‖ + ‖x - (z0 + a)‖)) (fun n => ?_) hdiff
    · refine this.congr (fun n => ?_)
      exact real_inner_comm _ _
    · have h1 := hR1 _ ⟨n, rfl⟩
      have h2 := hbT n
      exact (norm_sub_le _ _).trans (by linarith)
  · -- (78)
    intro n hn
    set Tx := (drT Pf Pg)^[n] x with hTx
    set p := Pf Tx with hp
    set q := Pg (refl Pf Tx) with hq
    have hs : resInv Pf Tx ∈ subgrad f p := by
      have := hPf Tx; rw [inv_one, one_smul] at this; exact this
    have ht : refl Pf Tx - q ∈ subgrad g q := by
      have := hPg (refl Pf Tx); rw [inv_one, one_smul] at this; exact this
    have h70 : 0 ≤ ⟪v, p - q - v⟫_ℝ :=
      DR64Aux.minnorm_vi hconv hvD (subset_closure ⟨p, ⟨_, hs⟩, q, ⟨_, ht⟩, rfl⟩)
    obtain ⟨-, h71b, h71c⟩ := lemma_6_3 f g hf hg Pf Pg hPf hPg v hv h12 hvR Tx y hy
    obtain ⟨Fp, hFp⟩ := DR64Aux.toReal_eq hs.2.1 hs.1
    obtain ⟨Fy, hFy⟩ := DR64Aux.toReal_eq hy.1 (hf.1 y)
    obtain ⟨Gq, hGq⟩ := DR64Aux.toReal_eq ht.2.1 ht.1
    obtain ⟨Gy, hGy⟩ := DR64Aux.toReal_eq hy.2 (hg.1 (y - v))
    rw [hFp, hFy, ← EReal.coe_add] at h71b
    rw [hGq, hGy, ← EReal.coe_add] at h71c
    have hb1 : Fp + ⟪y - p, v + resInv Pf Tx⟫_ℝ ≤ Fy := by exact_mod_cast h71b
    have hb2 : Gq + (⟪y - q - v, p - q - v⟫_ℝ + ⟪-y + v + q, v + resInv Pf Tx⟫_ℝ) ≤ Gy := by
      exact_mod_cast h71c
    rw [hFp, hGq, hFy, hGy, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    have hεn : ε n = ⟪y - q - v, p - q - v⟫_ℝ := rfl
    have hδn : δ n = ⟪p - q - v, p - (Tx + (n : ℝ) • v)⟫_ℝ := rfl
    have eres : resInv Pf Tx = Tx - p := rfl
    rw [eres] at hb1 hb2
    have key : ⟪y - p, v + (Tx - p)⟫_ℝ + ⟪-y + v + q, v + (Tx - p)⟫_ℝ =
        ⟪p - q - v, p - (Tx + (n : ℝ) • v)⟫_ℝ + ((n : ℝ) - 1) * ⟪v, p - q - v⟫_ℝ := by
      have e1 : ⟪y - p, v + (Tx - p)⟫_ℝ + ⟪-y + v + q, v + (Tx - p)⟫_ℝ =
          ⟪-(p - q - v), v + (Tx - p)⟫_ℝ := by
        rw [← inner_add_left]; congr 1; abel
      have e2 : p - (Tx + (n : ℝ) • v) = -(v + (Tx - p)) + ((1 : ℝ) - n) • v := by module
      rw [e1, e2, real_inner_comm (p - q - v) v]
      set d := p - q - v
      set r := Tx - p
      simp only [inner_add_right, inner_neg_right, inner_neg_left, real_inner_smul_right]
      ring
    have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have := mul_nonneg hn1 h70
    rw [hεn, hδn]
    linarith
