-- Prove2me | solution 2 for InconsistentDR.Shadow.theorem_6_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T23:19:40.041508+00:00
-- url     : https://prove2.me/submissions/84e5f654-9ea5-462e-967b-d9da1d9bef65

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_FRBSplitting_Weak_Setting
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization
import Theorems.Thm_InconsistentDR_Shadow_proposition_6_2
import Theorems.Thm_InconsistentDR_Shadow_proposition_6_4
import Theorems.Thm_InconsistentDR_Shadow_proposition_6_6
import Theorems.Thm_InconsistentDR_Shadow_eq_75_tendsto
import Theorems.Thm_InconsistentDR_Shadow_closure_domConj_eq_closure_ran_subgrad

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization FRBSplitting.Weak

namespace DR69bAux

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

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
    simp only [Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at this
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

end DR69bAux

open InconsistentDR.Shadow in
theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf) (hPg : IsResolvent 1 (subgrad g) Pg)
    (v : X) (hv : IsMinNormPt (closure (Set.range fun x => x - drT Pf Pg x)) v)
    (h12 : Standing12 (subgrad f) (subgrad g) Pf Pg)
    (h0 : (0 : X) ∈ domConj f + domConj g)
    (hvran : v ∈ Set.range fun x => x - drT Pf Pg x)
    (hzer : ∃ x, ∃ a ∈ subgrad f x, ∃ b ∈ subgrad g (x - v), a + b = 0)
    (x : X) :
    ∃ z : X,
      (IsWeakLimit (fun n => Pf ((drT Pf Pg)^[n] x)) z ∧
        ∀ y, f z + g (z - v) ≤ f y + g (y - v)) ∧
      (IsWeakLimit (fun n => Pg (refl Pf ((drT Pf Pg)^[n] x))) (z - v) ∧
        ∀ y, f (z - v + v) + g (z - v) ≤ f (y + v) + g y) ∧
      (Tendsto (fun n => f (Pf ((drT Pf Pg)^[n] x)) + g (Pg (refl Pf ((drT Pf Pg)^[n] x))))
          atTop (𝓝 (f z + g (z - v))) ∧
        f z + g (z - v) = ⨅ y, f y + g (y - v)) ∧
      Tendsto (fun n => f (Pf ((drT Pf Pg)^[n] x))) atTop (𝓝 (f z)) ∧
      Tendsto (fun n => g (Pg (refl Pf ((drT Pf Pg)^[n] x)))) atTop (𝓝 (g (z - v))) := by
  -- Step 1: `0 ∈ cl R`, i.e. `v_R = 0`.
  have hvR : (0 : X) ∈ closure (setR (subgrad f) (subgrad g)) := by
    obtain ⟨a, ha, b, hb, hab⟩ := h0
    have ha' : a ∈ closure (ran (subgrad f)) := by
      rw [← closure_domConj_eq_closure_ran_subgrad f hf]; exact subset_closure ha
    have hb' : b ∈ closure (ran (subgrad g)) := by
      rw [← closure_domConj_eq_closure_ran_subgrad g hg]; exact subset_closure hb
    have := map_mem_closure₂ (f := fun a b : X => a + b) (u := setR (subgrad f) (subgrad g))
      continuous_add ha' hb' (fun a ha b hb => Set.add_mem_add ha hb)
    simpa [hab] using this
  -- Step 2: `Z ≠ ∅`.
  have h62 := proposition_6_2 f g hf hg Pf Pg hPf hPg v hv h12 hvR
  have hZ : (solZ (subgrad f) (subgrad g) v).Nonempty := by
    obtain ⟨x0, a, ha, b, hb, hab⟩ := hzer
    refine ⟨x0, ?_⟩
    rw [h62.1]
    exact ⟨a, ha, b, hb, hab⟩
  -- Step 3: weak convergence of the primal shadows.
  obtain ⟨⟨z, hzlim, hzmin⟩, -⟩ := proposition_6_6 f g hf hg Pf Pg hPf hPg v hv h12 hvR hZ x
  -- Step 4: (75) gives `p n - q n → v`, hence `q n ⇀ z - v`.
  obtain ⟨hid, hlim⟩ := eq_75_tendsto f g hf hg Pf Pg hPf hPg v hv x
  have hdiff : Tendsto (fun n => Pf ((drT Pf Pg)^[n] x) - Pg (refl Pf ((drT Pf Pg)^[n] x)))
      atTop (𝓝 v) := by
    simpa only [hid] using hlim
  have hqlim : IsWeakLimit (fun n => Pg (refl Pf ((drT Pf Pg)^[n] x))) (z - v) := by
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
  -- Step 5: the optimal values are finite.
  obtain ⟨x0, a0, ha0, b0, hb0, -⟩ := hzer
  obtain ⟨F0, hF0⟩ : ∃ r : ℝ, f x0 = r := ⟨(f x0).toReal, (EReal.coe_toReal ha0.2.1 ha0.1).symm⟩
  obtain ⟨G0, hG0⟩ : ∃ r : ℝ, g (x0 - v) = r :=
    ⟨(g (x0 - v)).toReal, (EReal.coe_toReal hb0.2.1 hb0.1).symm⟩
  have hzx0 := hzmin x0
  rw [hF0, hG0, ← EReal.coe_add] at hzx0
  have hfz : f z ≠ ⊤ := by
    intro ht; rw [ht, EReal.top_add_of_ne_bot (hg.1 _), top_le_iff] at hzx0
    exact EReal.coe_ne_top _ hzx0
  have hgz : g (z - v) ≠ ⊤ := by
    intro ht; rw [ht, EReal.add_top_of_ne_bot (hf.1 _), top_le_iff] at hzx0
    exact EReal.coe_ne_top _ hzx0
  obtain ⟨F, hF⟩ : ∃ r : ℝ, f z = r := ⟨(f z).toReal, (EReal.coe_toReal hfz (hf.1 z)).symm⟩
  obtain ⟨G, hG⟩ : ∃ r : ℝ, g (z - v) = r :=
    ⟨(g (z - v)).toReal, (EReal.coe_toReal hgz (hg.1 _)).symm⟩
  -- Step 6: Proposition 6.4 with `y = z`.
  have h64 := proposition_6_4 f g hf hg Pf Pg hPf hPg v hv h12 hvR hZ z ⟨hfz, hgz⟩ x
  simp only at h64
  obtain ⟨hε, hδ, h78⟩ := h64
  set e : ℕ → ℝ := fun n =>
      ⟪z - Pg (refl Pf ((drT Pf Pg)^[n] x)) - v,
        Pf ((drT Pf Pg)^[n] x) - Pg (refl Pf ((drT Pf Pg)^[n] x)) - v⟫_ℝ +
      ⟪Pf ((drT Pf Pg)^[n] x) - Pg (refl Pf ((drT Pf Pg)^[n] x)) - v,
        Pf ((drT Pf Pg)^[n] x) - ((drT Pf Pg)^[n] x + (n : ℝ) • v)⟫_ℝ with he
  have hetend : Tendsto e atTop (𝓝 0) := by
    have := hε.add hδ
    simpa [he] using this
  have hineq : ∀ n : ℕ, 1 ≤ n →
      f (Pf ((drT Pf Pg)^[n] x)) + g (Pg (refl Pf ((drT Pf Pg)^[n] x))) + ((e n : ℝ) : EReal)
        ≤ ((F + G : ℝ) : EReal) := by
    intro n hn
    have := h78 n hn
    rw [hF, hG, ← EReal.coe_add] at this
    simpa [he] using this
  have hfp := DR69bAux.first_tendsto f g hf hg _ _ z (z - v) hzlim hqlim F G hF hG e hetend hineq
  have hgq := DR69bAux.first_tendsto g f hg hf _ _ (z - v) z hqlim hzlim G F hG hF e hetend
    (fun n hn => by rw [add_comm G F, add_comm (g _)]; exact hineq n hn)
  have hmu : f z + g (z - v) = ⨅ y, f y + g (y - v) :=
    le_antisymm (le_iInf hzmin) (iInf_le (fun y => f y + g (y - v)) z)
  have hsum : Tendsto (fun n => f (Pf ((drT Pf Pg)^[n] x)) + g (Pg (refl Pf ((drT Pf Pg)^[n] x))))
      atTop (𝓝 (f z + g (z - v))) := by
    rw [hF, hG]
    have hc := EReal.continuousAt_add (p := ((F : EReal), (G : EReal)))
      (Or.inl (EReal.coe_ne_top F)) (Or.inl (EReal.coe_ne_bot F))
    exact hc.tendsto.comp (hfp.prodMk_nhds hgq)
  refine ⟨z, ⟨hzlim, hzmin⟩, ⟨hqlim, ?_⟩, ⟨hsum, hmu⟩, ?_, ?_⟩
  · intro y
    have := hzmin (y + v)
    simpa using this
  · rw [hF]; exact hfp
  · rw [hG]; exact hgq
