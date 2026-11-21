-- Prove2me | solution 2 for MasulloGRH.bounded_disk_scalar_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:21:21.888165+00:00
-- url     : https://prove2.me/submissions/19d2175f-9121-4b9d-b2f4-69501c399394

import Theorems.Thm_MasulloGRH_completeNuclearDF_bounded_nuclear_domination
import Theorems.Thm_MasulloGRH_nuclearFrechet_bounded_nuclear_domination
import Theorems.Thm_MasulloGRH_quasinuclear_comp_nuclear_expansion
import Theorems.Thm_MasulloGRH_strongDual_seminorm_of_bounded
import Theorems.Thm_MasulloGRH_strongDual_seminorm_le_polar
import Theorems.Thm_MasulloGRH_nuclear_bounded_precompact

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open MasulloGRH Topology Filter

universe u

section CNReprSection

open Set Bornology Pointwise

namespace CNRepr


/-- In a complete locally convex space the closed convex hull of a precompact set is compact. -/
theorem isCompact_closure_convexHull {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hlc : IsLocallyConvexTopology E ‹TopologicalSpace E›)
    (hcomp : ∀ f : Filter E, IsCauchyFilter f → ∃ x : E, f ≤ 𝓝 x) (S : Set E)
    (hpre : ∀ V ∈ 𝓝 (0 : E), ∃ t : Finset E, S ⊆ ⋃ x ∈ t, {y : E | y - x ∈ V}) :
    IsCompact (closure (convexHull ℝ S)) := by
  obtain ⟨ι, _, p, hp⟩ := hlc
  have hadd : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ E := hp.continuousSMul
  have hlc : LocallyConvexSpace ℝ E := hp.toLocallyConvexSpace
  have hsR : ContinuousSMul ℝ E := IsScalarTower.continuousSMul (M := ℝ) (α := E) ℂ
  let _ : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace E := by
    refine ⟨fun {f} hf => hcomp f ⟨hf.1, fun U hU => ?_⟩⟩
    have hmem : {p : E × E | p.2 - p.1 ∈ U} ∈ uniformity E := by
      rw [uniformity_eq_comap_nhds_zero E]
      exact preimage_mem_comap hU
    obtain ⟨t, ht, hts⟩ := mem_prod_same_iff.1 (hf.2 hmem)
    exact ⟨t, ht, fun x hx y hy => hts (mk_mem_prod hy hx)⟩
  have hS : TotallyBounded S := by
    rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
    intro U hU
    obtain ⟨t, ht⟩ := hpre U hU
    refine ⟨t, t.finite_toSet, fun y hy => ?_⟩
    obtain ⟨x, hx⟩ := mem_iUnion.1 (ht hy)
    obtain ⟨hxt, hyx⟩ := mem_iUnion.1 hx
    refine mem_iUnion.2 ⟨x, mem_iUnion.2 ⟨hxt, ⟨y - x, hyx, ?_⟩⟩⟩
    simp
  exact isCompact_closure_of_totallyBounded_quasiComplete (𝕜 := ℂ) hS.convexHull

/-- The balanced hull of a bounded set is bounded. -/
theorem isVonNBounded_balancedHull {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [ContinuousSMul ℂ E] {S : Set E} (hS : IsVonNBounded ℂ S) :
    IsVonNBounded ℂ (balancedHull ℂ S) := by
  intro V hV
  obtain ⟨W, ⟨hW, hWb⟩, hWV⟩ := (nhds_basis_balanced ℂ E).mem_iff.1 hV
  obtain ⟨r, hr⟩ := absorbs_iff_norm.1 (hS hW)
  refine absorbs_iff_norm.2 ⟨r, fun c hc => ?_⟩
  exact ((hWb.smul c).balancedHull_subset_of_subset (hr c hc)).trans
    (smul_set_mono hWV)


theorem completeNuclear_strongBidual_bounded_repr (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hN : IsNuclear G)
    (q : Seminorm ℂ (StrongDual ℂ G)) (hq : Continuous q) :
    ∃ D : Set G, Bornology.IsVonNBounded ℂ D ∧
      ∀ F : StrongDual ℂ (StrongDual ℂ G), (∀ f, ‖F f‖ ≤ q f) →
        ∃ y ∈ D, ∀ f : StrongDual ℂ G, F f = f y := by
  obtain ⟨⟨ι, _, p, hp⟩, hT2⟩ := hN.1
  obtain ⟨-, hcomp⟩ := hC
  have hadd : IsTopologicalAddGroup G := hp.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ G := hp.continuousSMul
  have hHLCS : IsHLCS G := ⟨⟨ι, inferInstance, p, hp⟩, hT2⟩
  -- `q` is dominated by the polar gauge of a bounded set `B`
  obtain ⟨B, C, hB, hC, hqB⟩ := strongDual_seminorm_le_polar G hHLCS q hq
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨B', hB'def⟩ : ∃ B' : Set G,
      B' = insert 0 ((fun x : G => ((C + 1 : ℝ) : ℂ) • x) '' B) := ⟨_, rfl⟩
  have hB'b : IsVonNBounded ℂ B' := by
    rw [hB'def, isVonNBounded_insert]
    have h1 := hB.image (((C + 1 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ G)
    refine h1.subset ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp⟩
  have h0B' : (0 : G) ∈ B' := by rw [hB'def]; exact mem_insert _ _
  have hB₁b : IsVonNBounded ℂ (balancedHull ℂ B') := isVonNBounded_balancedHull hB'b
  have hpre := nuclear_bounded_precompact G hN _ hB₁b
  have hDc : IsCompact (closure (convexHull ℝ (balancedHull ℂ B'))) :=
    isCompact_closure_convexHull ⟨ι, inferInstance, p, hp⟩ hcomp _ hpre
  have hsubD : ∀ (z : ℂ) (y₀ : G), ‖z‖ ≤ 1 → y₀ ∈ B' →
      z • y₀ ∈ closure (convexHull ℝ (balancedHull ℂ B')) := fun z y₀ hz hy₀ =>
    subset_closure (subset_convexHull ℝ _
      (mem_balancedHull_iff.2 ⟨z, hz, smul_mem_smul_set hy₀⟩))
  refine ⟨closure (convexHull ℝ (balancedHull ℂ B')), ?_, fun F hF => ?_⟩
  · -- a compact set is bounded
    intro V hV
    obtain ⟨W, ⟨hW, hWb⟩, hWV⟩ := (nhds_basis_balanced ℂ G).mem_iff.1 hV
    have hWo : interior W ∈ 𝓝 (0 : G) := interior_mem_nhds.2 hW
    -- cover the compact set by the open sets `n • interior W`
    have hcover : closure (convexHull ℝ (balancedHull ℂ B')) ⊆
        ⋃ n : ℕ, ((n : ℂ) + 1) • interior W := by
      intro y _
      have hlim : Tendsto (fun n : ℕ => ((n : ℂ) + 1)⁻¹ • y) atTop (𝓝 0) := by
        have h1 : Tendsto (fun k : ℕ => ((k : ℂ) + 1)⁻¹) atTop (𝓝 0) := by
          have h2 : Tendsto (fun k : ℕ => (((1 : ℝ) / ((k : ℝ) + 1) : ℝ) : ℂ)) atTop
              (𝓝 ((0 : ℝ) : ℂ)) :=
            (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
          refine (h2.congr fun k => ?_).trans_eq ?_
          · push_cast; rw [one_div]
          · simp
        simpa using h1.smul_const y
      obtain ⟨n, hn⟩ := (hlim.eventually hWo).exists
      have hc0 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      refine mem_iUnion.2 ⟨n, ⟨((n : ℂ) + 1)⁻¹ • y, hn, ?_⟩⟩
      simp only
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    have hopen : ∀ n : ℕ, IsOpen (((n : ℂ) + 1) • interior W) := fun n =>
      isOpen_interior.smul₀ (by exact_mod_cast Nat.succ_ne_zero n)
    obtain ⟨t, ht⟩ := hDc.elim_finite_subcover _ hopen hcover
    -- all the finitely many multiples sit inside one large multiple of `W`
    refine absorbs_iff_norm.2 ⟨(t.sup id : ℕ) + 1, fun c hc => ?_⟩
    have hc0 : c ≠ 0 := by
      intro h
      rw [h, norm_zero] at hc
      have : (0 : ℝ) < (t.sup id : ℕ) + 1 := by positivity
      linarith
    intro y hy
    obtain ⟨n, hn⟩ := mem_iUnion.1 (ht hy)
    obtain ⟨hnt, hyn⟩ := mem_iUnion.1 hn
    obtain ⟨w, hw, rfl⟩ := hyn
    have hnle : (n : ℝ) + 1 ≤ ‖c‖ := by
      have h1 : n ≤ t.sup id := Finset.le_sup (f := id) hnt
      have h2 : (n : ℝ) ≤ (t.sup id : ℕ) := by exact_mod_cast h1
      linarith
    refine ⟨c⁻¹ • (((n : ℂ) + 1) • w), hWV ?_, by simp only; rw [smul_inv_smul₀ hc0]⟩
    rw [smul_smul]
    refine hWb.smul_mem ?_ (interior_subset hw)
    rw [norm_mul, norm_inv]
    have h3 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [h3]
    have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc0
    rw [inv_mul_le_iff₀ hcpos]
    linarith
  · -- the representation: finite-dimensional separation plus compactness
    have hsR : ContinuousSMul ℝ G := IsScalarTower.continuousSMul (M := ℝ) (α := G) ℂ
    have hDconv : Convex ℝ (closure (convexHull ℝ (balancedHull ℂ B'))) :=
      (convex_convexHull ℝ _).closure
    -- no functional separates `F` from the compact set
    have key : ∀ (f : StrongDual ℂ G) (u : ℝ), (F f).re < u →
        (∀ y ∈ closure (convexHull ℝ (balancedHull ℂ B')), u < (f y).re) → False := by
      intro f u hFf hφD
      have hsmall : ∀ y₀ ∈ B', ‖f y₀‖ < -u := by
        intro y₀ hy₀
        by_cases h0 : f y₀ = 0
        · have h1 := hφD 0 (by simpa using hsubD 0 y₀ (by simp) hy₀)
          rw [map_zero] at h1
          rw [h0, norm_zero]
          simpa using h1
        · obtain ⟨z, hz⟩ : ∃ z : ℂ, z = -((starRingEnd ℂ) (f y₀) / (‖f y₀‖ : ℂ)) := ⟨_, rfl⟩
          have hnpos : 0 < ‖f y₀‖ := norm_pos_iff.2 h0
          have hzn : ‖z‖ ≤ 1 := by
            rw [hz, norm_neg, norm_div, RCLike.norm_conj, Complex.norm_real,
              Real.norm_of_nonneg hnpos.le, div_self hnpos.ne']
          have hzf : z * f y₀ = -(‖f y₀‖ : ℂ) := by
            rw [hz, neg_mul, div_mul_eq_mul_div, Complex.conj_mul']
            have hne : (‖f y₀‖ : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
            field_simp
          have h1 := hφD (z • y₀) (hsubD z y₀ hzn hy₀)
          rw [map_smul, smul_eq_mul, hzf] at h1
          simp only [Complex.neg_re, Complex.ofReal_re] at h1
          linarith
      have hupos : 0 < -u := by
        have := hsmall 0 h0B'
        simpa using this
      have hqf : q f ≤ (C + 1) * (-u / (C + 1)) := by
        refine (hqB f (-u / (C + 1)) (by positivity) fun x hx => ?_).trans
          (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
        have hx' : ((C + 1 : ℝ) : ℂ) • x ∈ B' := by
          rw [hB'def]; exact mem_insert_of_mem _ ⟨x, hx, rfl⟩
        have h2 := hsmall _ hx'
        rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hC1.le] at h2
        rw [le_div_iff₀ hC1, mul_comm]
        exact h2.le
      have hqf' : q f ≤ -u := by
        have : (C + 1) * (-u / (C + 1)) = -u := by field_simp
        rwa [this] at hqf
      have h3 : -(F f).re ≤ ‖F f‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm (F f))
      linarith [hF f]
    -- finitely many equations can be solved in the compact set
    have hfin : ∀ s : Finset (StrongDual ℂ G),
        ∃ y ∈ closure (convexHull ℝ (balancedHull ℂ B')), ∀ f ∈ s, f y = F f := by
      classical
      intro s
      by_contra hno
      let T : G →L[ℂ] (s → ℂ) := ContinuousLinearMap.pi fun g => g.1
      have hTapp : ∀ (y : G) (g : s), T y g = g.1 y := fun _ _ => rfl
      have hK : IsCompact (T '' closure (convexHull ℝ (balancedHull ℂ B'))) :=
        hDc.image T.continuous
      have hKc : Convex ℝ (T '' closure (convexHull ℝ (balancedHull ℂ B'))) :=
        hDconv.is_linear_image ⟨map_add T, fun c x => T.map_smul_of_tower c x⟩
      have hv : (fun g : s => F g.1) ∉ T '' closure (convexHull ℝ (balancedHull ℂ B')) := by
        rintro ⟨y, hy, hyv⟩
        refine hno ⟨y, hy, fun f hf => ?_⟩
        have := congrFun hyv ⟨f, hf⟩
        simpa [hTapp] using this
      obtain ⟨φ, u, h1, h2⟩ :=
        RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ) hKc hK.isClosed hv
      have hφw : ∀ w : s → ℂ, φ w = ∑ g : s, w g * φ (Pi.single g 1) := by
        intro w
        conv_lhs => rw [← Finset.univ_sum_single w]
        rw [map_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        have h3 : (Pi.single g (w g) : s → ℂ) = w g • Pi.single g 1 := by
          ext j
          by_cases h : j = g <;> simp [h]
        rw [h3, map_smul, smul_eq_mul]
      obtain ⟨f, hf⟩ : ∃ f : StrongDual ℂ G, f = ∑ g : s, φ (Pi.single g 1) • g.1 := ⟨_, rfl⟩
      have hFf : φ (fun g : s => F g.1) = F f := by
        rw [hφw, hf, map_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [map_smul, smul_eq_mul, mul_comm]
      have hfy : ∀ y : G, φ (T y) = f y := by
        intro y
        rw [hφw, hf, sum_apply]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [hTapp, smul_apply, smul_eq_mul, mul_comm]
      refine key f u ?_ ?_
      · rw [← hFf]
        simpa using h1
      · intro y hy
        have := h2 (T y) ⟨y, hy, rfl⟩
        rw [hfy] at this
        simpa using this
    -- compactness
    obtain ⟨y, hyD, hy⟩ := hDc.inter_iInter_nonempty
      (fun f : StrongDual ℂ G => {y : G | f y = F f})
      (fun f => isClosed_eq f.continuous continuous_const)
      (fun s => by
        obtain ⟨y, hy, h⟩ := hfin s
        exact ⟨y, hy, mem_iInter₂.2 h⟩)
    exact ⟨y, hyD, fun f => ((mem_iInter.1 hy f : f y = F f)).symm⟩

end CNRepr

end CNReprSection

namespace BDSE

/-- The seminorm `c • p` for a real `c ≥ 0`. -/
noncomputable def sc {X : Type*} [AddCommGroup X] [Module ℂ X] (c : ℝ) (hc : 0 ≤ c)
    (p : Seminorm ℂ X) : Seminorm ℂ X :=
  let c' : NNReal := ⟨c, hc⟩
  c' • p

theorem sc_apply {X : Type*} [AddCommGroup X] [Module ℂ X] (c : ℝ) (hc : 0 ≤ c)
    (p : Seminorm ℂ X) (x : X) : sc c hc p x = c * p x := rfl

/-- A positively homogeneous function bounded by `C` on the open unit ball of a seminorm `s`
is bounded by `C * s`. -/
theorem homog_bound {X : Type*} [AddCommGroup X] [Module ℂ X] (s : Seminorm ℂ X) (f : X → ℝ)
    (hf : ∀ (c : ℝ) (x : X), 0 < c → f ((c : ℂ) • x) = c * f x) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, s x < 1 → f x ≤ C) (x : X) : f x ≤ C * s x := by
  by_contra hlt
  rw [not_le] at hlt
  have hs0 : 0 ≤ s x := apply_nonneg s x
  have hdpos : 0 < f x - C * s x := by linarith
  have hC1 : 0 < C + 1 := by linarith
  have hεpos : 0 < (f x - C * s x) / (C + 1) := div_pos hdpos hC1
  set ε := (f x - C * s x) / (C + 1) with hε
  have hb : 0 < s x + ε := by linarith
  have hsx : s ((((s x + ε)⁻¹ : ℝ) : ℂ) • x) < 1 := by
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hb.le),
      inv_mul_lt_iff₀ hb]
    linarith
  have h1 := h _ hsx
  rw [hf _ _ (inv_pos.2 hb), inv_mul_le_iff₀ hb] at h1
  have h3 : C * ε < f x - C * s x := by
    have : ε * (C + 1) = f x - C * s x := by
      rw [hε]; field_simp
    nlinarith
  nlinarith

/-- A `0`-neighbourhood of a locally convex space contains the open unit ball of a continuous
seminorm. -/
theorem exists_seminorm_ball_subset {X : Type u} [AddCommGroup X] [Module ℂ X]
    [t : TopologicalSpace X] (h : IsLocallyConvexTopology X t) {U : Set X}
    (hU : U ∈ 𝓝 (0 : X)) :
    ∃ p : Seminorm ℂ X, Continuous p ∧ ∀ x, p x < 1 → x ∈ U := by
  obtain ⟨ι, _, P, hP⟩ := h
  have hadd : IsTopologicalAddGroup X := hP.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ X := hP.continuousSMul
  obtain ⟨⟨s, ρ⟩, hρ, hsub⟩ := hP.hasBasis_zero_ball.mem_iff.1 hU
  have hρ : 0 < ρ := hρ
  obtain ⟨p0, hp0⟩ : ∃ p : Seminorm ℂ X, p = s.sup P := ⟨_, rfl⟩
  have hsub : p0.ball 0 ρ ⊆ U := by rw [hp0]; exact hsub
  have hsc : Continuous p0 := by
    rw [hp0]
    exact Seminorm.continuous (r := ρ) (hP.hasBasis_zero_ball.mem_of_mem (i := (s, ρ)) hρ)
  refine ⟨sc ρ⁻¹ (inv_pos.2 hρ).le p0, ?_, ?_⟩
  · have : (fun x => sc ρ⁻¹ (inv_pos.2 hρ).le p0 x) = fun x => ρ⁻¹ * p0 x :=
      funext fun x => sc_apply _ _ _ _
    change Continuous (fun x => sc ρ⁻¹ (inv_pos.2 hρ).le p0 x)
    rw [this]
    exact continuous_const.mul hsc
  · intro x hx
    apply hsub
    rw [Seminorm.mem_ball_zero]
    rw [sc_apply, inv_mul_lt_iff₀ hρ] at hx
    simpa using hx

/-- A continuous seminorm is bounded on a von Neumann bounded set. -/
theorem seminorm_bdd_of_bounded {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (q : Seminorm ℂ X) (hqc : Continuous q) (B : Set X) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ B, q x ≤ M := by
  have hq1 : {x : X | q x < 1} ∈ 𝓝 (0 : X) :=
    (isOpen_lt hqc continuous_const).mem_nhds (by simp)
  obtain ⟨ρ, hρ⟩ := absorbs_iff_norm.1 (hB hq1)
  refine ⟨max ρ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx => ?_⟩
  have hnorm : ‖((max ρ 1 : ℝ) : ℂ)‖ = max ρ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (le_trans zero_le_one (le_max_right _ _))]
  obtain ⟨y, hy, rfl⟩ := hρ ((max ρ 1 : ℝ) : ℂ) (by rw [hnorm]; exact le_max_left _ _) hx
  have hy' : q y < 1 := hy
  change q (((max ρ 1 : ℝ) : ℂ) • y) ≤ max ρ 1
  rw [map_smul_eq_mul, hnorm]
  nlinarith [le_max_right ρ 1, apply_nonneg q y]

/-- A linear functional dominated by a continuous seminorm is continuous. -/
theorem continuous_of_le_seminorm {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] (P : Seminorm ℂ X) (hP : Continuous P) (f : X →ₗ[ℂ] ℂ)
    (hf : ∀ x, ‖f x‖ ≤ P x) : Continuous f := by
  have h0 : ContinuousAt f 0 := by
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    have h1 : ∀ᶠ x in 𝓝 (0 : X), P x < ε := by
      have h2 := hP.tendsto 0
      rw [map_zero] at h2
      exact h2.eventually (Iio_mem_nhds hε)
    filter_upwards [h1] with x hx
    rw [dist_zero_right]
    exact (hf x).trans_lt hx
  exact continuous_of_continuousAt_zero f h0



/-- In a Hausdorff locally convex space, continuous linear functionals separate points
(Hahn–Banach). -/
theorem exists_dual_ne_zero {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) {x : E} (hx : x ≠ 0) : ∃ f : StrongDual ℂ E, f x ≠ 0 := by
  obtain ⟨⟨ι, _, p, hp⟩, hT2⟩ := hE
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  have : PolynormableSpace ℂ E := hp.toPolynormableSpace
  let S : Submodule ℂ E := ℂ ∙ x
  obtain ⟨g, hg⟩ := Submodule.ClosedComplemented.of_finiteDimensional S
  have hxS : x ∈ S := Submodule.mem_span_singleton_self x
  have hne : (⟨x, hxS⟩ : S) ≠ 0 := by
    intro h
    apply hx
    simpa using congrArg Subtype.val h
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ S, φ ⟨x, hxS⟩ ≠ 0 := by
    by_contra! h
    exact hne ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
  let φc : S →L[ℂ] ℂ := LinearMap.toContinuousLinearMap φ
  refine ⟨φc.comp g, ?_⟩
  have hgx : g x = ⟨x, hxS⟩ := hg ⟨x, hxS⟩
  simpa [φc, hgx] using hφ

theorem eq_of_forall_dual_eq {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) (x y : E) (h : ∀ f : StrongDual ℂ E, f x = f y) : x = y := by
  by_contra hxy
  obtain ⟨f, hf⟩ := exists_dual_ne_zero hE (sub_ne_zero.2 hxy)
  apply hf
  rw [map_sub, h f, sub_self]

/-- For a nonnegative summable sequence `c` there are weights `ε n > 0`, `ε n → 0`, with
`∑ c n / ε n < ∞`. -/
theorem exists_null_weights (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hcs : Summable c) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧ Summable (fun n => c n / ε n) := by
  let r : ℕ → ℝ := fun n => ∑' k, c (k + n)
  have hsh : ∀ n, Summable fun k => c (k + n) := fun n => (summable_nat_add_iff n).2 hcs
  have hr0 : ∀ n, 0 ≤ r n := fun n => tsum_nonneg fun k => hc0 _
  have hrec : ∀ n, r n = c n + r (n + 1) := by
    intro n
    have h1 := (hsh n).tsum_eq_zero_add
    change r n = c n + r (n + 1)
    change (∑' k, c (k + n)) = c n + ∑' k, c (k + (n + 1))
    rw [h1, zero_add]
    congr 1
    exact tsum_congr fun k => by rw [add_assoc, add_comm 1 n]
  have hrt : Tendsto r atTop (𝓝 0) := tendsto_sum_nat_add c
  refine ⟨fun n => Real.sqrt (r n) + (1 / 2) ^ n, fun n => by positivity, ?_, ?_⟩
  · have h1 : Tendsto (fun n => Real.sqrt (r n)) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hrt
      simpa [Function.comp_def] using h
    have h2 : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using h1.add h2
  · have hterm : ∀ n, c n / (Real.sqrt (r n) + (1 / 2) ^ n) ≤
        2 * (Real.sqrt (r n) - Real.sqrt (r (n + 1))) := by
      intro n
      have hp : (0 : ℝ) < (1 / 2) ^ n := by positivity
      obtain ⟨A, hA⟩ : ∃ A, A = Real.sqrt (r n) := ⟨_, rfl⟩
      obtain ⟨B, hB⟩ : ∃ B, B = Real.sqrt (r (n + 1)) := ⟨_, rfl⟩
      have hA0 : 0 ≤ A := hA ▸ Real.sqrt_nonneg _
      have hB0 : 0 ≤ B := hB ▸ Real.sqrt_nonneg _
      have e1 : A * A = r n := by rw [hA]; exact Real.mul_self_sqrt (hr0 n)
      have e2 : B * B = r (n + 1) := by rw [hB]; exact Real.mul_self_sqrt (hr0 (n + 1))
      have hle : B ≤ A := by
        rw [hA, hB]
        exact Real.sqrt_le_sqrt (by rw [hrec n]; linarith [hc0 n])
      have hc : c n = A * A - B * B := by rw [e1, e2, hrec n]; ring
      rw [← hA, ← hB, div_le_iff₀ (by positivity), hc]
      nlinarith [mul_nonneg (sub_nonneg.2 hle) (by linarith : (0 : ℝ) ≤ A - B + 2 * (1 / 2) ^ n)]
    refine summable_of_sum_range_le (c := 2 * Real.sqrt (r 0))
      (fun n => div_nonneg (hc0 n) (by positivity)) fun N => ?_
    have h1 : ∑ i ∈ Finset.range N, c i / (Real.sqrt (r i) + (1 / 2) ^ i) ≤
        2 * (Real.sqrt (r 0) - Real.sqrt (r N)) := by
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ]
        have := hterm N
        linarith
    linarith [Real.sqrt_nonneg (r N)]

/-- The seminorm `φ ↦ ∑ aₙ |φ(wₙ)|` on the strong dual. -/
noncomputable def sumSeminorm {G : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (w : ℕ → G) (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n)
    (hs : ∀ φ : StrongDual ℂ G, Summable fun n => a n * ‖φ (w n)‖) :
    Seminorm ℂ (StrongDual ℂ G) :=
  Seminorm.of (fun φ => ∑' n, a n * ‖φ (w n)‖)
    (fun φ ψ => by
      rw [← (hs φ).tsum_add (hs ψ)]
      refine (hs (φ + ψ)).tsum_le_tsum (fun n => ?_) ((hs φ).add (hs ψ))
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (ha0 n))
    (fun c φ => by
      rw [← tsum_mul_left]
      refine tsum_congr fun n => ?_
      change a n * ‖c * φ (w n)‖ = ‖c‖ * (a n * ‖φ (w n)‖)
      rw [norm_mul]
      ring)

theorem sumSeminorm_apply {G : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (w : ℕ → G) (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n)
    (hs : ∀ φ : StrongDual ℂ G, Summable fun n => a n * ‖φ (w n)‖) (φ : StrongDual ℂ G) :
    sumSeminorm w a ha0 hs φ = ∑' n, a n * ‖φ (w n)‖ := rfl

/-- Evaluation at a point, as a linear functional on the dual. -/
noncomputable def evL {G : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] (y : G) :
    StrongDual ℂ G →ₗ[ℂ] ℂ where
  toFun f := f y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end BDSE

open BDSE in
theorem solution (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hN : IsNuclear G)
    (hclass : IsFrechet G ∨
      ((∃ B : ℕ → Set G, (∀ n, Bornology.IsVonNBounded ℂ (B n)) ∧
      ∀ S : Set G, Bornology.IsVonNBounded ℂ S → ∃ n, S ⊆ B n) ∧
       (∀ U : ℕ → Set G, (∀ n, U n ∈ nhds (0 : G) ∧ IsClosed (U n) ∧ Balanced ℂ (U n) ∧ Convex ℝ (U n)) →
      (∀ S : Set G, Bornology.IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) →
      (⋂ n, U n) ∈ nhds (0 : G))))
    (B : Set G) (hBb : Bornology.IsVonNBounded ℂ B) :
    ∃ (y : ℕ → G) (c : ℕ → ℝ) (a : ℕ → (Submodule.span ℂ B) →ₗ[ℂ] ℂ),
      Filter.Tendsto y Filter.atTop (nhds (0 : G)) ∧
      (∀ n, 0 ≤ c n) ∧ Summable c ∧
      (∀ n (x : Submodule.span ℂ B), (x : G) ∈ B → ‖a n x‖ ≤ c n) ∧
      ∀ x : Submodule.span ℂ B, HasSum (fun n => a n x • y n) (x : G) := by
  have hHL : IsHLCS G := hN.1
  obtain ⟨⟨ι, hι, Pf, hPf⟩, hT2⟩ := hN.1
  have hadd : IsTopologicalAddGroup G := hPf.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ G := hPf.continuousSMul
  -- bounded sets are nuclearly dominated (both classes)
  have hdom : ∀ S : Set G, Bornology.IsVonNBounded ℂ S →
      ∃ (y : ℕ → G) (c : ℕ → ℝ), Bornology.IsVonNBounded ℂ (Set.range y) ∧ (∀ n, 0 ≤ c n) ∧
        Summable c ∧ ∀ (f : StrongDual ℂ G), ∀ x ∈ S, ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖ := by
    intro S hS
    rcases hclass with hFr | ⟨hBf, hDF⟩
    · exact nuclearFrechet_bounded_nuclear_domination G hFr hN S hS
    · exact completeNuclearDF_bounded_nuclear_domination G hC hN hBf hDF S hS
  obtain ⟨u, a, hub, ha0, has, hBu⟩ := hdom B hBb
  obtain ⟨v, b, hvb, hb0, hbs, huv⟩ := hdom (Set.range u) hub
  -- seminorms on the strong dual
  obtain ⟨pu, hpuc, hpu⟩ := strongDual_seminorm_of_bounded G hHL (Set.range u) hub
  obtain ⟨pv, hpvc, hpv⟩ := strongDual_seminorm_of_bounded G hHL (Set.range v) hvb
  have hsu : ∀ φ : StrongDual ℂ G, Summable fun n => a n * ‖φ (u n)‖ := fun φ =>
    Summable.of_nonneg_of_le (fun n => mul_nonneg (ha0 n) (norm_nonneg _))
      (fun n => mul_le_mul_of_nonneg_left (hpu φ (u n) ⟨n, rfl⟩) (ha0 n)) (has.mul_right _)
  have hsv : ∀ φ : StrongDual ℂ G, Summable fun n => b n * ‖φ (v n)‖ := fun φ =>
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hb0 n) (norm_nonneg _))
      (fun n => mul_le_mul_of_nonneg_left (hpv φ (v n) ⟨n, rfl⟩) (hb0 n)) (hbs.mul_right _)
  let q := sumSeminorm u a ha0 hsu
  let r := sumSeminorm v b hb0 hsv
  let fu : ℕ → StrongDual ℂ (StrongDual ℂ G) := fun n =>
    ⟨evL (u n), continuous_of_le_seminorm pu hpuc (evL (u n)) fun φ => hpu φ (u n) ⟨n, rfl⟩⟩
  let gv : ℕ → StrongDual ℂ (StrongDual ℂ G) := fun n =>
    ⟨evL (v n), continuous_of_le_seminorm pv hpvc (evL (v n)) fun φ => hpv φ (v n) ⟨n, rfl⟩⟩
  obtain ⟨h, ψ, c, hc0, hcs, hh, hψ, hconv⟩ :=
    quasinuclear_comp_nuclear_expansion (StrongDual ℂ G) q r pv fu a ha0 has
      (fun n φ => huv φ (u n) ⟨n, rfl⟩) (fun φ => le_rfl)
      gv b hb0 hbs (fun n φ => hpv φ (v n) ⟨n, rfl⟩) (fun φ => le_rfl)
  -- the functionals `h n` are evaluations at the points of a bounded set
  obtain ⟨D, hDb, hD⟩ := CNRepr.completeNuclear_strongBidual_bounded_repr G hC hN pv hpvc
  choose z hzD hz using fun n => hD (h n) (hh n)
  -- completeness of `G` as a uniform space
  obtain ⟨-, hcomp⟩ := hC
  let _ : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  have : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace G := by
    refine ⟨fun {f} hf => hcomp f ⟨hf.1, fun U hU => ?_⟩⟩
    have hmem : {p : G × G | p.2 - p.1 ∈ U} ∈ uniformity G := by
      rw [uniformity_eq_comap_nhds_zero G]
      exact preimage_mem_comap hU
    obtain ⟨t, ht, hts⟩ := mem_prod_same_iff.1 (hf.2 hmem)
    exact ⟨t, ht, fun x hx y hy => hts (Set.mk_mem_prod hy hx)⟩
  -- the expansion on `B`
  have hψB : ∀ n, ∀ x ∈ B, ‖ψ n x‖ ≤ 1 := fun n x hx => (hBu (ψ n) x hx).trans (hψ n)
  have hexp : ∀ x ∈ B, HasSum (fun n => ((c n : ℂ) * ψ n x) • z n) x := by
    intro x hx
    -- summability in the complete space `G`
    have hsummT : Summable fun n => ((c n : ℂ) * ψ n x) • z n := by
      rw [summable_iff_vanishing]
      intro e he
      obtain ⟨p, hpc, hp⟩ := exists_seminorm_ball_subset ⟨ι, hι, Pf, hPf⟩ he
      obtain ⟨M, hM0, hM⟩ := seminorm_bdd_of_bounded p hpc D hDb
      obtain ⟨s, hs⟩ := hcs.vanishing (Metric.ball_mem_nhds (0 : ℝ) (inv_pos.2 hM0))
      refine ⟨s, fun t ht => hp _ ?_⟩
      have h1 := hs t ht
      rw [mem_ball_zero_iff, Real.norm_of_nonneg (Finset.sum_nonneg fun n _ => hc0 n)] at h1
      calc p (∑ n ∈ t, ((c n : ℂ) * ψ n x) • z n)
          ≤ ∑ n ∈ t, p (((c n : ℂ) * ψ n x) • z n) :=
            Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
        _ ≤ ∑ n ∈ t, c n * M := by
            refine Finset.sum_le_sum fun n _ => ?_
            rw [map_smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc0 n)]
            have h2 := hψB n x hx
            have h3 := hM (z n) (hzD n)
            have h4 := apply_nonneg p (z n)
            calc c n * ‖ψ n x‖ * p (z n) ≤ c n * 1 * M := by
                  apply mul_le_mul (mul_le_mul_of_nonneg_left h2 (hc0 n)) h3 h4
                  exact mul_nonneg (hc0 n) zero_le_one
              _ = c n * M := by ring
        _ = (∑ n ∈ t, c n) * M := by rw [Finset.sum_mul]
        _ < 1 := by
            rw [← lt_div_iff₀ hM0, one_div]
            exact h1
    -- the sum is `x`, tested against every functional
    have hval : ∑' n, ((c n : ℂ) * ψ n x) • z n = x := by
      apply eq_of_forall_dual_eq hHL
      intro φ
      have h1 := (φ.hasSum hsummT.hasSum).tendsto_sum_nat
      have h2 : Tendsto (fun N => (φ - ∑ n ∈ Finset.range N, ((c n : ℂ) * h n φ) • ψ n) x)
          atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun N => ?_) (hconv φ)
        exact hBu _ x hx
      have h3 : Tendsto (fun N => φ x - ∑ n ∈ Finset.range N, φ (((c n : ℂ) * ψ n x) • z n))
          atTop (𝓝 0) := by
        refine h2.congr fun N => ?_
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [ContinuousLinearMap.smul_apply, smul_eq_mul, hz n φ, map_smul, smul_eq_mul]
        ring
      have h4 : Tendsto (fun N => ∑ n ∈ Finset.range N, φ (((c n : ℂ) * ψ n x) • z n))
          atTop (𝓝 (φ x)) := by
        have h5 := (tendsto_const_nhds (x := φ x)).sub h3
        simpa using h5
      exact tendsto_nhds_unique h1 h4
    have hfin := hsummT.hasSum
    rw [hval] at hfin
    exact hfin
  -- extension to the span of `B` by linearity
  have hspan : ∀ x : G, x ∈ Submodule.span ℂ B →
      HasSum (fun n => ((c n : ℂ) * ψ n x) • z n) x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hexp x hx
    | zero => simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : G)) 0)
    | add x y _ _ hx hy =>
      have h1 := hx.add hy
      have e : (fun n => ((c n : ℂ) * ψ n (x + y)) • z n) =
          fun n => ((c n : ℂ) * ψ n x) • z n + ((c n : ℂ) * ψ n y) • z n := by
        funext n
        rw [map_add, mul_add, add_smul]
      rw [e]
      exact h1
    | smul k x _ hx =>
      have h1 := hx.const_smul k
      have e : (fun n => ((c n : ℂ) * ψ n (k • x)) • z n) =
          fun n => k • ((c n : ℂ) * ψ n x) • z n := by
        funext n
        rw [map_smul, smul_eq_mul, smul_smul]
        congr 1
        ring
      rw [e]
      exact h1
  -- rescaling to a null sequence
  obtain ⟨ε, hε0, hεt, hεs⟩ := exists_null_weights c hc0 hcs
  refine ⟨fun n => (ε n : ℂ) • z n, fun n => c n / ε n,
    fun n => (((c n / ε n : ℝ) : ℂ)) • ((ψ n : G →ₗ[ℂ] ℂ).comp (Submodule.span ℂ B).subtype),
    ?_, fun n => div_nonneg (hc0 n) (hε0 n).le, hεs, ?_, ?_⟩
  · have hεc : Tendsto (fun n => (ε n : ℂ)) atTop (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).comp hεt
      simpa [Function.comp_def] using this
    exact hDb.smul_tendsto_zero (Filter.Eventually.of_forall hzD) hεc
  · intro n x hx
    change ‖((c n / ε n : ℝ) : ℂ) * ψ n (x : G)‖ ≤ c n / ε n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hc0 n) (hε0 n).le)]
    have := mul_le_mul_of_nonneg_left (hψB n x hx) (div_nonneg (hc0 n) (hε0 n).le)
    rwa [mul_one] at this
  · intro x
    have h1 := hspan (x : G) x.2
    have e : (fun n => ((((c n / ε n : ℝ) : ℂ)) •
        ((ψ n : G →ₗ[ℂ] ℂ).comp (Submodule.span ℂ B).subtype)) x • ((ε n : ℂ) • z n)) =
        fun n => ((c n : ℂ) * ψ n (x : G)) • z n := by
      funext n
      change ((((c n / ε n : ℝ) : ℂ)) * ψ n (x : G)) • ((ε n : ℂ) • z n) =
        ((c n : ℂ) * ψ n (x : G)) • z n
      rw [smul_smul]
      congr 1
      have hne : (ε n : ℂ) ≠ 0 := by
        rw [Ne, Complex.ofReal_eq_zero]; exact (hε0 n).ne'
      push_cast
      field_simp
    rw [e]
    exact h1
