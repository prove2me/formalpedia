-- Prove2me | solution 1 for JMMS.not_exists_subshift_semiconj_IETOn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T14:58:37.86164+00:00
-- url     : https://prove2.me/submissions/2ad8f48f-8829-4b92-9b53-a935199eb9a3

import Mathlib
import Definitions.Def_CantorSystems

section

open CantorSystems IntervalExchange
open Filter Topology

namespace JMMS
namespace IETPF511

lemma contMk : Continuous (fun t : ℝ => (t : UnitAddCircle)) := continuous_quotient_mk'

/-! ## A concrete interval exchange with a discontinuity

Cut the circle at `a`; with `0 < l < 1/2`, exchange `[a, a + l)` and `[a + l, a + 2l)`. -/

/-- The position of `x` in `[0, 1)`, measured from `a`. -/
noncomputable def tt (a : ℝ) (x : UnitAddCircle) : ℝ := (AddCircle.equivIco 1 a x : ℝ) - a

lemma tt_mem (a : ℝ) (x : UnitAddCircle) : 0 ≤ tt a x ∧ tt a x < 1 := by
  have h := (AddCircle.equivIco 1 a x).2
  simp only [Set.mem_Ico] at h
  constructor <;> simp only [tt] <;> linarith [h.1, h.2]

lemma coe_tt (a : ℝ) (x : UnitAddCircle) : ((a + tt a x : ℝ) : UnitAddCircle) = x := by
  simp only [tt, add_sub_cancel]
  exact AddCircle.coe_equivIco

lemma tt_coe (a r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) : tt a ((a + r : ℝ) : UnitAddCircle) = r := by
  rw [tt, AddCircle.equivIco_coe_of_mem ⟨by linarith, by linarith⟩]
  ring

lemma tt_add (a : ℝ) (x : UnitAddCircle) (d : ℝ) (h0 : 0 ≤ tt a x + d) (h1 : tt a x + d < 1) :
    tt a (x + (d : UnitAddCircle)) = tt a x + d := by
  conv_lhs => rw [← coe_tt a x, ← AddCircle.coe_add, add_assoc]
  exact tt_coe a _ h0 h1

/-- The increment. -/
noncomputable def cc (l t : ℝ) : ℝ := if t < l then l else if t < 2 * l then -l else 0

/-- The map. -/
noncomputable def gfun (a l : ℝ) (x : UnitAddCircle) : UnitAddCircle :=
  x + ((cc l (tt a x) : ℝ) : UnitAddCircle)

variable {a l : ℝ}

lemma gfun_involutive (hl : 0 < l) (hl2 : l < 1 / 2) : Function.Involutive (gfun a l) := by
  intro x
  obtain ⟨h0, h1⟩ := tt_mem a x
  by_cases c1 : tt a x < l
  · have e1 : cc l (tt a x) = l := by simp [cc, c1]
    have e2 : tt a (gfun a l x) = tt a x + l := by
      rw [gfun, e1]; exact tt_add a x l (by linarith) (by linarith)
    have e3 : cc l (tt a (gfun a l x)) = -l := by
      rw [e2]; simp only [cc]; rw [if_neg (by linarith), if_pos (by linarith)]
    rw [gfun, e3, gfun, e1, AddCircle.coe_neg]; abel
  · by_cases c2 : tt a x < 2 * l
    · have e1 : cc l (tt a x) = -l := by simp [cc, c1, c2]
      have e2 : tt a (gfun a l x) = tt a x + -l := by
        rw [gfun, e1]; exact tt_add a x (-l) (by linarith) (by linarith)
      have e3 : cc l (tt a (gfun a l x)) = l := by
        rw [e2]; simp only [cc]; rw [if_pos (by linarith)]
      rw [gfun, e3, gfun, e1, AddCircle.coe_neg]; abel
    · have e1 : cc l (tt a x) = 0 := by simp [cc, c1, c2]
      have e2 : gfun a l x = x := by rw [gfun, e1]; simp
      rw [e2, e2]

/-- Right-continuity in the strong form: `g (x + r) = g x + r` for small `r ≥ 0`. -/
lemma gfun_locTrans (hl : 0 < l) (x : UnitAddCircle) :
    ∀ᶠ r : ℝ in 𝓝[Set.Ici (0:ℝ)] (0:ℝ),
      gfun a l (x + (r : UnitAddCircle)) = gfun a l x + r := by
  obtain ⟨h0, h1⟩ := tt_mem a x
  have hcc : ∀ᶠ r : ℝ in 𝓝[Set.Ici (0:ℝ)] (0:ℝ), cc l (tt a x + r) = cc l (tt a x) := by
    by_cases c1 : tt a x < l
    · have : ∀ᶠ r : ℝ in 𝓝 (0:ℝ), r < l - tt a x := gt_mem_nhds (by linarith)
      filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with r hr hr0
      simp only [Set.mem_Ici] at hr0
      simp only [cc]; rw [if_pos (by linarith), if_pos c1]
    · by_cases c2 : tt a x < 2 * l
      · have : ∀ᶠ r : ℝ in 𝓝 (0:ℝ), r < 2 * l - tt a x := gt_mem_nhds (by linarith)
        filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with r hr hr0
        simp only [Set.mem_Ici] at hr0
        simp only [cc]; rw [if_neg (by linarith), if_pos (by linarith), if_neg c1, if_pos c2]
      · filter_upwards [self_mem_nhdsWithin] with r hr0
        simp only [Set.mem_Ici] at hr0
        simp only [cc]; rw [if_neg (by linarith), if_neg (by linarith), if_neg c1, if_neg c2]
  have h1' : ∀ᶠ r : ℝ in 𝓝 (0:ℝ), r < 1 - tt a x := gt_mem_nhds (by linarith)
  filter_upwards [hcc, nhdsWithin_le_nhds h1', self_mem_nhdsWithin] with r hr hr1 hr0
  simp only [Set.mem_Ici] at hr0
  rw [gfun, gfun, tt_add a x r (by linarith) (by linarith), hr]
  abel

lemma gfun_rc (hl : 0 < l) : IsRightContinuous (gfun a l) := by
  intro x
  have hc : ContinuousWithinAt (fun t : ℝ => gfun a l x + (t : UnitAddCircle)) (Set.Ici 0) 0 :=
    (continuous_const.add contMk).continuousWithinAt
  exact hc.congr_of_eventuallyEq (gfun_locTrans hl x) (by simp)

lemma gfun_sub_mem (x : UnitAddCircle) :
    gfun a l x - x ∈ ({(l : UnitAddCircle), ((-l : ℝ) : UnitAddCircle), 0} : Set _) := by
  simp only [gfun, add_sub_cancel_left, cc]
  split_ifs <;> simp

lemma cc_continuousAt {t : ℝ} (h1 : t ≠ l) (h2 : t ≠ 2 * l) : ContinuousAt (cc l) t := by
  rcases lt_or_gt_of_ne h1 with c1 | c1
  · have : ∀ᶠ s in 𝓝 t, cc l s = l := by
      filter_upwards [gt_mem_nhds c1] with s hs
      simp [cc, hs]
    exact continuousAt_const.congr (this.mono fun s hs => hs.symm)
  · rcases lt_or_gt_of_ne h2 with c2 | c2
    · have : ∀ᶠ s in 𝓝 t, cc l s = -l := by
        filter_upwards [lt_mem_nhds c1, gt_mem_nhds c2] with s hs hs'
        simp [cc, hs', not_lt.2 hs.le]
      exact continuousAt_const.congr (this.mono fun s hs => hs.symm)
    · have : ∀ᶠ s in 𝓝 t, cc l s = 0 := by
        filter_upwards [lt_mem_nhds c1, lt_mem_nhds c2] with s hs hs'
        simp [cc, not_lt.2 hs.le, not_lt.2 hs'.le]
      exact continuousAt_const.congr (this.mono fun s hs => hs.symm)

lemma gfun_continuousAt {x : UnitAddCircle} (h0 : x ≠ (a : UnitAddCircle))
    (h1 : x ≠ ((a + l : ℝ) : UnitAddCircle)) (h2 : x ≠ ((a + 2 * l : ℝ) : UnitAddCircle)) :
    ContinuousAt (gfun a l) x := by
  have ht : ContinuousAt (tt a) x := by
    have := AddCircle.continuousAt_equivIco (p := (1:ℝ)) a h0
    exact (continuous_subtype_val.continuousAt.comp this).sub continuousAt_const
  have e1 : tt a x ≠ l := by
    intro h; apply h1; rw [← coe_tt a x, h]
  have e2 : tt a x ≠ 2 * l := by
    intro h; apply h2; rw [← coe_tt a x, h]
  have hc : ContinuousAt (fun z => cc l (tt a z)) x := (cc_continuousAt e1 e2).comp ht
  exact continuousAt_id.add (contMk.continuousAt.comp hc)

lemma gfun_disc_finite :
    {x | ¬ ContinuousAt (gfun a l) x}.Finite := by
  refine (Set.toFinite ({(a : UnitAddCircle), ((a + l : ℝ) : UnitAddCircle),
    ((a + 2 * l : ℝ) : UnitAddCircle)} : Set _)).subset ?_
  intro x hx
  by_contra hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hn
  exact hx (gfun_continuousAt hn.1 hn.2.1 hn.2.2)

/-- The left limit at `a`: `g` is the identity just to the left of `a`. -/
lemma gfun_left (hl : 0 < l) (hl2 : l < 1 / 2) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
      gfun a l ((a - ε : ℝ) : UnitAddCircle) = ((a - ε : ℝ) : UnitAddCircle) := by
  have h' : ∀ᶠ ε : ℝ in 𝓝 (0:ℝ), ε < 1 - 2 * l := gt_mem_nhds (by linarith)
  filter_upwards [nhdsWithin_le_nhds h', self_mem_nhdsWithin] with ε hε hε0
  simp only [Set.mem_Ioi] at hε0
  have e : ((a - ε : ℝ) : UnitAddCircle) = ((a + (1 - ε) : ℝ) : UnitAddCircle) := by
    rw [show a + (1 - ε) = (a - ε) + 1 by ring, AddCircle.coe_add, AddCircle.coe_period, add_zero]
  rw [e, gfun, tt_coe a _ (by linarith) (by linarith)]
  simp only [cc]
  rw [if_neg (by linarith), if_neg (by linarith)]
  simp

lemma gfun_at (hl : 0 < l) :
    gfun a l (a : UnitAddCircle) = (a : UnitAddCircle) + (l : UnitAddCircle) := by
  have : tt a (a : UnitAddCircle) = 0 := by
    have := tt_coe a 0 le_rfl one_pos
    simpa using this
  simp [gfun, this, cc, hl]

lemma coe_ne_zero (hl : 0 < l) (hl1 : l < 1) : (l : UnitAddCircle) ≠ 0 := by
  rw [Ne, AddCircle.coe_eq_zero_of_pos_iff (1:ℝ) one_pos hl]
  rintro ⟨n, hn⟩
  simp only [nsmul_eq_mul, mul_one] at hn
  rcases Nat.lt_or_ge n 1 with h | h
  · interval_cases n; simp at hn; linarith
  · have : (1:ℝ) ≤ n := by exact_mod_cast h
    linarith

/-- The concrete permutation. -/
noncomputable def gperm (a l : ℝ) (hl : 0 < l) (hl2 : l < 1 / 2) : Equiv.Perm UnitAddCircle :=
  (gfun_involutive (a := a) hl hl2).toPerm _

lemma gperm_mem (Λ : AddSubgroup UnitAddCircle) (σ : Finset UnitAddCircle) (hl : 0 < l)
    (hl2 : l < 1 / 2) (hlΛ : (l : UnitAddCircle) ∈ Λ) (ha : (a : UnitAddCircle) ∈ σ) :
    gperm a l hl hl2 ∈ IETOn Λ σ := by
  have hinv : (gperm a l hl hl2)⁻¹ = gperm a l hl hl2 := by
    rw [Equiv.Perm.inv_def]
    exact Function.Involutive.toPerm_symm _
  refine ⟨⟨Subgroup.subset_closure ⟨gfun_rc hl, ?_, gfun_disc_finite⟩, ?_⟩, ?_⟩
  · refine (Set.toFinite ({(l : UnitAddCircle), ((-l : ℝ) : UnitAddCircle), 0} : Set _)).subset ?_
    rintro _ ⟨x, rfl⟩
    exact gfun_sub_mem x
  · intro x
    have := gfun_sub_mem (a := a) (l := l) x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    change gfun a l x - x ∈ Λ
    rcases this with h | h | h <;> rw [h]
    · exact hlΛ
    · rw [AddCircle.coe_neg]; exact Λ.neg_mem hlΛ
    · exact Λ.zero_mem
  · intro x hx
    rw [hinv]
    have hc : ContinuousAt (gfun a l) x := by
      apply gfun_continuousAt
      · rintro rfl; exact hx ⟨_, ha, by simp⟩
      · rintro rfl; exact hx ⟨_, ha, by rw [AddCircle.coe_add]; simpa using hlΛ⟩
      · rintro rfl
        refine hx ⟨_, ha, ?_⟩
        rw [AddCircle.coe_add, add_sub_cancel_left, two_mul, AddCircle.coe_add]
        exact Λ.add_mem hlΛ hlΛ
    exact ⟨hc, hc⟩

/-- An infinite subgroup of the circle contains `l` with `0 < l < 1/2`. -/
lemma exists_small (Λ : AddSubgroup UnitAddCircle) (hΛ : (Λ : Set UnitAddCircle).Infinite) :
    ∃ l : ℝ, 0 < l ∧ l < 1 / 2 ∧ (l : UnitAddCircle) ∈ Λ := by
  obtain ⟨μ, hμ, hμn⟩ :=
    (hΛ.sdiff (Set.toFinite ({0, ((1 / 2 : ℝ) : UnitAddCircle)} : Set UnitAddCircle))).nonempty
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hμn
  set m : ℝ := (AddCircle.equivIco 1 0 μ : ℝ) with hm
  have hmμ : (m : UnitAddCircle) = μ := AddCircle.coe_equivIco
  have hmI := (AddCircle.equivIco 1 0 μ).2
  rw [← hm] at hmI
  simp only [Set.mem_Ico, zero_add] at hmI
  have hm0 : m ≠ 0 := by rintro h; apply hμn.1; rw [← hmμ, h]; simp
  have hm2 : m ≠ 1 / 2 := by rintro h; apply hμn.2; rw [← hmμ, h]
  rcases lt_or_gt_of_ne hm2 with h | h
  · exact ⟨m, lt_of_le_of_ne hmI.1 (Ne.symm hm0), h, hmμ ▸ hμ⟩
  · refine ⟨1 - m, by linarith, by linarith, ?_⟩
    rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub, hmμ]
    exact Λ.neg_mem hμ

end IETPF511

theorem chk_not_exists_subshift_semiconj_IETOn
    (Λ : AddSubgroup UnitAddCircle) (hΛ : (Λ : Set UnitAddCircle).Infinite) (hfg : Λ.FG)
    (σ : Finset UnitAddCircle) (hσ : σ.Nonempty) :
    ¬ ∃ k : ℕ, ∃ S : Subshift Λ (Fin k),
      ∃ π : topologicalFullGroup Λ S ≃* IETOn Λ σ, ∃ h : S → UnitAddCircle,
        Continuous h ∧ Function.Surjective h ∧
        ∀ (g : topologicalFullGroup Λ S) (x : S),
          h ((g : S ≃ₜ S) x) = (π g : Equiv.Perm UnitAddCircle) (h x) := by
  rintro ⟨k, S, π, h, hc, hsurj, hsemi⟩
  obtain ⟨s, hs⟩ := hσ
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective s
  obtain ⟨l, hl, hl2, hlΛ⟩ := IETPF511.exists_small Λ hΛ
  set g := IETPF511.gperm a l hl hl2 with hgdef
  have hgmem : g ∈ IETOn Λ σ := IETPF511.gperm_mem Λ σ hl hl2 hlΛ hs
  set gh := π.symm ⟨g, hgmem⟩ with hgh
  have hsemi' : ∀ x : S, h ((gh : S ≃ₜ S) x) = IETPF511.gfun a l (h x) := by
    intro x
    rw [hsemi, hgh, MulEquiv.apply_symm_apply]
    rfl
  -- compactness of the subshift
  have hcpt : CompactSpace S :=
    isCompact_iff_compactSpace.1 (S.isSubshift.1.isCompact : IsCompact (S : Set (Λ → Fin k)))
  let xs : ℝ → S := fun ε => Function.surjInv hsurj ((a - ε : ℝ) : UnitAddCircle)
  have hxs : ∀ ε, h (xs ε) = ((a - ε : ℝ) : UnitAddCircle) :=
    fun ε => Function.surjInv_eq hsurj _
  let F : Filter S := Filter.map xs (𝓝[>] (0:ℝ))
  obtain ⟨x, hx⟩ := exists_clusterPt_of_compactSpace F
  have : (𝓝 x ⊓ F).NeBot := hx
  have hlim : Tendsto (fun ε : ℝ => ((a - ε : ℝ) : UnitAddCircle)) (𝓝[>] (0:ℝ))
      (𝓝 (a : UnitAddCircle)) := by
    have hc' : Continuous (fun ε : ℝ => ((a - ε : ℝ) : UnitAddCircle)) :=
      IETPF511.contMk.comp (continuous_const.sub continuous_id)
    have := hc'.tendsto (0:ℝ)
    simp only [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hF1 : Tendsto h F (𝓝 (a : UnitAddCircle)) := by
    rw [tendsto_map'_iff]
    exact hlim.congr (fun ε => (hxs ε).symm)
  have hF2 : Tendsto (fun y => h ((gh : S ≃ₜ S) y)) F (𝓝 (a : UnitAddCircle)) := by
    rw [tendsto_map'_iff]
    refine hlim.congr' ?_
    filter_upwards [IETPF511.gfun_left (a := a) hl hl2] with ε hε
    simp only [Function.comp_apply]
    rw [hsemi', hxs, hε]
  have e1 : h x = (a : UnitAddCircle) :=
    tendsto_nhds_unique (hc.continuousAt.tendsto.mono_left inf_le_left)
      (hF1.mono_left inf_le_right)
  have e2 : h ((gh : S ≃ₜ S) x) = (a : UnitAddCircle) :=
    tendsto_nhds_unique
      ((hc.comp (gh : S ≃ₜ S).continuous).continuousAt.tendsto.mono_left inf_le_left)
      (hF2.mono_left inf_le_right)
  rw [hsemi', e1, IETPF511.gfun_at hl] at e2
  exact IETPF511.coe_ne_zero hl (by linarith) (by simpa using e2)

end JMMS

end

open CantorSystems IntervalExchange
theorem solution
    (Λ : AddSubgroup UnitAddCircle) (hΛ : (Λ : Set UnitAddCircle).Infinite) (hfg : Λ.FG)
    (σ : Finset UnitAddCircle) (hσ : σ.Nonempty) :
    ¬ ∃ k : ℕ, ∃ S : Subshift Λ (Fin k),
      ∃ π : topologicalFullGroup Λ S ≃* IETOn Λ σ, ∃ h : S → UnitAddCircle,
        Continuous h ∧ Function.Surjective h ∧
        ∀ (g : topologicalFullGroup Λ S) (x : S),
          h ((g : S ≃ₜ S) x) = (π g : Equiv.Perm UnitAddCircle) (h x) :=
  JMMS.chk_not_exists_subshift_semiconj_IETOn Λ hΛ hfg σ hσ
