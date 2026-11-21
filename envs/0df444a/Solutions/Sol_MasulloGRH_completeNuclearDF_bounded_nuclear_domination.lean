-- Prove2me | solution 1 for MasulloGRH.completeNuclearDF_bounded_nuclear_domination
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:55:43.194532+00:00
-- url     : https://prove2.me/submissions/f9bf8254-44c9-4a2a-8128-4acf17840f2b

import Theorems.Thm_MasulloGRH_nuclear_dual_domination
import Theorems.Thm_MasulloGRH_pietsch_hilbertian_two_summing
import Theorems.Thm_MasulloGRH_quasinuclear_of_hilbertian_two_summing_chain
import Theorems.Thm_MasulloGRH_strongDual_isHLCS
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

namespace CNDFAux

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


/-- **Absolute summability of the strong dual.**  Let `G` be a nuclear space with a fundamental
increasing sequence `A k` of bounded sets and the (DF) property.  Every continuous seminorm `p`
on the strong dual is absolutely summing with respect to the evaluations at some `A k`. -/
theorem dual_abs_summing (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hN : IsNuclear G)
    (hDF : ∀ U : ℕ → Set G, (∀ n, U n ∈ nhds (0 : G) ∧ IsClosed (U n) ∧ Balanced ℂ (U n) ∧
      Convex ℝ (U n)) →
      (∀ S : Set G, Bornology.IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) →
      (⋂ n, U n) ∈ nhds (0 : G))
    (A : ℕ → Set G) (hAb : ∀ k, Bornology.IsVonNBounded ℂ (A k))
    (hAmono : ∀ r k, r ≤ k → A r ⊆ A k)
    (hAf : ∀ S : Set G, Bornology.IsVonNBounded ℂ S → ∃ k, S ⊆ A k)
    (p : Seminorm ℂ (StrongDual ℂ G)) (hp : Continuous p) :
    ∃ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (f : Fin n → StrongDual ℂ G) (s : ℝ), 0 ≤ s →
      (∀ y ∈ A k, ∑ i, ‖f i y‖ ≤ s) → ∑ i, p (f i) ≤ K * s := by
  have hHL : IsHLCS G := hN.1
  obtain ⟨⟨ι, hι, Pf, hPf⟩, hT2⟩ := hN.1
  have hadd : IsTopologicalAddGroup G := hPf.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ G := hPf.continuousSMul
  by_contra hcon
  push Not at hcon
  choose n f s hs0 hsA hlt using fun k : ℕ => hcon k (2 ^ k) (by positivity)
  -- normalization
  let T : ℕ → ℝ := fun k => ∑ i, p (f k i)
  have hT0 : ∀ k, 0 < T k := fun k =>
    lt_of_le_of_lt (mul_nonneg (by positivity) (hs0 k)) (hlt k)
  let g : ∀ k, Fin (n k) → StrongDual ℂ G := fun k i => (((T k)⁻¹ : ℝ) : ℂ) • f k i
  have hgapp : ∀ k i x, ‖g k i x‖ = (T k)⁻¹ * ‖f k i x‖ := by
    intro k i x
    change ‖(((T k)⁻¹ : ℝ) : ℂ) * f k i x‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (hT0 k).le)]
  have hg1 : ∀ k, ∑ i, p (g k i) = 1 := by
    intro k
    have h1 : ∀ i, p (g k i) = (T k)⁻¹ * p (f k i) := by
      intro i
      change p ((((T k)⁻¹ : ℝ) : ℂ) • f k i) = _
      rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (hT0 k).le)]
    rw [Finset.sum_congr rfl fun i _ => h1 i, ← Finset.mul_sum]
    exact inv_mul_cancel₀ (hT0 k).ne'
  have hg2 : ∀ k, ∀ y ∈ A k, ∑ i, ‖g k i y‖ ≤ (1 / 2) ^ k := by
    intro k y hy
    rw [Finset.sum_congr rfl fun i _ => hgapp k i y, ← Finset.mul_sum, inv_mul_le_iff₀ (hT0 k)]
    have h1 := hsA k y hy
    have h2 := hlt k
    have h3 : (0 : ℝ) < 2 ^ k := by positivity
    have h4 : T k * (1 / 2) ^ k = T k / 2 ^ k := by
      rw [one_div, inv_pow, div_eq_mul_inv]
    rw [h4, le_div_iff₀ h3]
    have h5 : (∑ i, ‖f k i y‖) * 2 ^ k ≤ s k * 2 ^ k := mul_le_mul_of_nonneg_right h1 h3.le
    have h6 : 2 ^ k * s k < T k := h2
    linarith
  -- the partial sums `R N x = ∑_{k<N} ∑ᵢ |g k i x|`
  let R : ℕ → G → ℝ := fun N x => ∑ k ∈ Finset.range N, ∑ i, ‖g k i x‖
  have hRc : ∀ N, Continuous (R N) := fun N =>
    continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun i _ =>
      (g k i).continuous.norm
  have hR0 : ∀ N, R N 0 = 0 := fun N => by simp [R]
  have hRsmul : ∀ N (c : ℂ) x, R N (c • x) = ‖c‖ * R N x := by
    intro N c x
    simp only [R, map_smul, smul_eq_mul, norm_mul, Finset.mul_sum]
  have hRadd : ∀ N x y, R N (x + y) ≤ R N x + R N y := by
    intro N x y
    simp only [R, map_add]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => norm_add_le _ _
  have hRnn : ∀ N x, 0 ≤ R N x := fun N x =>
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  let U : ℕ → Set G := fun N => {x | R N x ≤ 1}
  have hUprops : ∀ N, U N ∈ nhds (0 : G) ∧ IsClosed (U N) ∧ Balanced ℂ (U N) ∧
      Convex ℝ (U N) := by
    intro N
    refine ⟨?_, isClosed_le (hRc N) continuous_const, ?_, ?_⟩
    · have h1 : {x : G | R N x < 1} ∈ 𝓝 (0 : G) :=
        (isOpen_lt (hRc N) continuous_const).mem_nhds (by simp [hR0])
      exact Filter.mem_of_superset h1 fun x (hx : R N x < 1) => (le_of_lt hx : R N x ≤ 1)
    · intro c hc
      rintro _ ⟨x, hx, rfl⟩
      change R N (c • x) ≤ 1
      rw [hRsmul]
      have hx' : R N x ≤ 1 := hx
      nlinarith [hRnn N x, norm_nonneg c]
    · intro x hx y hy a b ha hb hab
      change R N (a • x + b • y) ≤ 1
      rw [← Complex.coe_smul a x, ← Complex.coe_smul b y]
      refine (hRadd N _ _).trans ?_
      rw [hRsmul, hRsmul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg ha,
        Real.norm_of_nonneg hb]
      have hx' : R N x ≤ 1 := hx
      have hy' : R N y ≤ 1 := hy
      nlinarith
  have hborn : ∀ S : Set G, Bornology.IsVonNBounded ℂ S → Absorbs ℂ (⋂ N, U N) S := by
    intro S hS
    obtain ⟨r, hSr⟩ := hAf S hS
    have hbd : ∀ (k : ℕ) (i : Fin (n k)), ∃ C : ℝ, ∀ x ∈ A r, ‖g k i x‖ ≤ C := by
      intro k i
      have h1 := (hAb r).image (g k i)
      rw [NormedSpace.isVonNBounded_iff, isBounded_iff_forall_norm_le] at h1
      obtain ⟨C, hC⟩ := h1
      exact ⟨C, fun x hx => hC _ ⟨x, hx, rfl⟩⟩
    choose C hC using hbd
    let bk : ℕ → ℝ := fun k => ∑ i, |C k i|
    have hbk0 : ∀ k, 0 ≤ bk k := fun k => Finset.sum_nonneg fun i _ => abs_nonneg _
    let Mr : ℝ := ∑ k ∈ Finset.range r, bk k
    have hMr0 : 0 ≤ Mr := Finset.sum_nonneg fun k _ => hbk0 k
    have hbound : ∀ N, ∀ x ∈ A r, R N x ≤ Mr + 2 := by
      intro N x hx
      have hterm : ∀ k, ∑ i, ‖g k i x‖ ≤ (if k < r then bk k else 0) + (1 / 2) ^ k := by
        intro k
        by_cases hkr : k < r
        · rw [if_pos hkr]
          have h1 : ∑ i, ‖g k i x‖ ≤ bk k :=
            Finset.sum_le_sum fun i _ => (hC k i x hx).trans (le_abs_self _)
          have h2 : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
          linarith
        · rw [if_neg hkr, zero_add]
          exact hg2 k x (hAmono r k (not_lt.1 hkr) hx)
      have h1 : R N x ≤ ∑ k ∈ Finset.range N, ((if k < r then bk k else 0) + (1 / 2) ^ k) :=
        Finset.sum_le_sum fun k _ => hterm k
      rw [Finset.sum_add_distrib] at h1
      have h2 : ∑ k ∈ Finset.range N, (if k < r then bk k else 0) ≤ Mr := by
        rw [← Finset.sum_filter]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hbk0 k
        intro k hk
        rw [Finset.mem_filter] at hk
        exact Finset.mem_range.2 hk.2
      have h3 : ∑ k ∈ Finset.range N, ((1 : ℝ) / 2) ^ k ≤ 2 := sum_geometric_two_le N
      linarith
    refine absorbs_iff_norm.2 ⟨Mr + 2, fun c hc x hx => ?_⟩
    have hcpos : 0 < ‖c‖ := by linarith
    have hc0 : c ≠ 0 := norm_pos_iff.1 hcpos
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc0, Set.mem_iInter]
    intro N
    change R N (c⁻¹ • x) ≤ 1
    rw [hRsmul, norm_inv, inv_mul_le_iff₀ hcpos, mul_one]
    exact (hbound N x (hSr hx)).trans hc
  have hW := hDF U hUprops hborn
  obtain ⟨qG, hqGc, hqG⟩ := exists_seminorm_ball_subset ⟨ι, hι, Pf, hPf⟩ hW
  have hRq : ∀ N x, R N x ≤ qG x := by
    intro N x
    have h1 := homog_bound qG (R N) (fun c x hc => by
      rw [hRsmul, Complex.norm_real, Real.norm_of_nonneg hc.le]) 1 zero_le_one
      (fun x hx => Set.mem_iInter.1 (hqG x hx) N) x
    simpa using h1
  have hgq : ∀ k i x, ‖g k i x‖ ≤ qG x := by
    intro k i x
    refine le_trans ?_ (hRq (k + 1) x)
    have h1 : ‖g k i x‖ ≤ ∑ j, ‖g k j x‖ :=
      Finset.single_le_sum (f := fun j => ‖g k j x‖) (fun j _ => norm_nonneg _)
        (Finset.mem_univ i)
    have h2 : ∑ j, ‖g k j x‖ ≤ R (k + 1) x :=
      Finset.single_le_sum (f := fun k => ∑ j, ‖g k j x‖)
        (fun k _ => Finset.sum_nonneg fun j _ => norm_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_self k))
    exact h1.trans h2
  -- nuclearity of `G`
  obtain ⟨pG, y, c, hpGc, hc0, hcs, hqy, hdom⟩ := nuclear_dual_domination G hN qG hqGc
  obtain ⟨S₀, C₀, hS₀, hC₀, hpol⟩ := strongDual_seminorm_le_polar G hHL p hp
  obtain ⟨M, hM0, hM⟩ := seminorm_bdd_of_bounded pG hpGc S₀ hS₀
  have hgy : ∀ k i m, ‖g k i (y m)‖ ≤ 1 := fun k i m => (hgq k i (y m)).trans (hqy m)
  have hsum : ∀ k i, Summable fun m => c m * ‖g k i (y m)‖ := fun k i =>
    Summable.of_nonneg_of_le (fun m => mul_nonneg (hc0 m) (norm_nonneg _))
      (fun m => by
        have := mul_le_mul_of_nonneg_left (hgy k i m) (hc0 m)
        rwa [mul_one] at this) hcs
  have hkey : ∀ k i, p (g k i) ≤ C₀ * (M * ∑' m, c m * ‖g k i (y m)‖) := by
    intro k i
    have hts : 0 ≤ ∑' m, c m * ‖g k i (y m)‖ :=
      tsum_nonneg fun m => mul_nonneg (hc0 m) (norm_nonneg _)
    refine hpol (g k i) _ (mul_nonneg hM0.le hts) fun x hx => ?_
    have h1 : pG (((M⁻¹ : ℝ) : ℂ) • x) ≤ 1 := by
      rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hM0.le),
        inv_mul_le_iff₀ hM0, mul_one]
      exact hM x hx
    have h2 := hdom (g k i) (hgq k i) _ h1
    rw [map_smul, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.2 hM0.le), inv_mul_le_iff₀ hM0] at h2
    exact h2
  have hN' : ∀ N : ℕ, (N : ℝ) ≤ C₀ * (M * ∑' m, c m) := by
    intro N
    have h1 : (N : ℝ) = ∑ k ∈ Finset.range N, ∑ i, p (g k i) := by
      rw [Finset.sum_congr rfl fun k _ => hg1 k]
      simp
    have h2 : ∑ k ∈ Finset.range N, ∑ i, p (g k i) ≤
        ∑ k ∈ Finset.range N, ∑ i, C₀ * (M * ∑' m, c m * ‖g k i (y m)‖) :=
      Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i _ => hkey k i
    have h3 : ∑ k ∈ Finset.range N, ∑ i, C₀ * (M * ∑' m, c m * ‖g k i (y m)‖) =
        C₀ * (M * ∑ k ∈ Finset.range N, ∑ i, ∑' m, c m * ‖g k i (y m)‖) := by
      simp only [Finset.mul_sum]
    have h4 : ∑ k ∈ Finset.range N, ∑ i, ∑' m, c m * ‖g k i (y m)‖ =
        ∑' m, c m * R N (y m) := by
      have h5 := (hasSum_sum (s := Finset.range N) fun k _ =>
        hasSum_sum (s := Finset.univ) fun i _ => (hsum k i).hasSum).tsum_eq
      rw [← h5]
      refine tsum_congr fun m => ?_
      simp only [R, Finset.mul_sum]
    have h6 : ∑' m, c m * R N (y m) ≤ ∑' m, c m := by
      have hle : ∀ m, c m * R N (y m) ≤ c m := fun m => by
        have := mul_le_mul_of_nonneg_left ((hRq N (y m)).trans (hqy m)) (hc0 m)
        rwa [mul_one] at this
      exact Summable.tsum_le_tsum hle
        (Summable.of_nonneg_of_le (fun m => mul_nonneg (hc0 m) (hRnn N (y m))) hle hcs) hcs
    rw [h1]
    refine h2.trans ?_
    rw [h3, h4]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h6 hM0.le) hC₀
  obtain ⟨N, hNgt⟩ := exists_nat_gt (C₀ * (M * ∑' m, c m))
  exact absurd (hN' N) (not_le.2 hNgt)

end CNDFAux

open CNDFAux in
theorem solution (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hN : IsNuclear G)
    (hB : ∃ B : ℕ → Set G, (∀ n, Bornology.IsVonNBounded ℂ (B n)) ∧
      ∀ S : Set G, Bornology.IsVonNBounded ℂ S → ∃ n, S ⊆ B n)
    (hDF : ∀ U : ℕ → Set G, (∀ n, U n ∈ nhds (0 : G) ∧ IsClosed (U n) ∧ Balanced ℂ (U n) ∧ Convex ℝ (U n)) →
      (∀ S : Set G, Bornology.IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) →
      (⋂ n, U n) ∈ nhds (0 : G))
    (B : Set G) (hBb : Bornology.IsVonNBounded ℂ B) :
    ∃ (y : ℕ → G) (c : ℕ → ℝ), Bornology.IsVonNBounded ℂ (Set.range y) ∧ (∀ n, 0 ≤ c n) ∧
      Summable c ∧ ∀ (f : StrongDual ℂ G), ∀ x ∈ B, ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖ := by
  have hHL : IsHLCS G := hN.1
  have hF : IsHLCS (StrongDual ℂ G) := strongDual_isHLCS G hHL
  obtain ⟨Bs, hBsb, hBsf⟩ := hB
  -- an increasing fundamental sequence of bounded sets
  let A : ℕ → Set G := fun k => ⋃ j ∈ Finset.range (k + 1), Bs j
  have hAb : ∀ k, Bornology.IsVonNBounded ℂ (A k) := by
    intro k
    induction k with
    | zero =>
      have : A 0 = Bs 0 := by simp [A]
      rw [this]
      exact hBsb 0
    | succ k ih =>
      have : A (k + 1) = Bs (k + 1) ∪ A k := by
        simp only [A]
        rw [Finset.range_add_one (n := k + 1), Finset.set_biUnion_insert]
      rw [this]
      exact (hBsb (k + 1)).union ih
  have hAmono : ∀ r k, r ≤ k → A r ⊆ A k := by
    intro r k hrk
    exact Set.biUnion_subset_biUnion_left fun j hj =>
      Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hj) (by omega))
  have hAf : ∀ S : Set G, Bornology.IsVonNBounded ℂ S → ∃ k, S ⊆ A k := by
    intro S hS
    obtain ⟨k, hk⟩ := hBsf S hS
    exact ⟨k, hk.trans (Set.subset_biUnion_of_mem (u := fun j => Bs j)
      (Finset.mem_range.2 (Nat.lt_succ_self k)))⟩
  -- absolutely summing pairs of seminorms on the strong dual
  have hpair : ∀ p : Seminorm ℂ (StrongDual ℂ G), Continuous p →
      ∃ q : Seminorm ℂ (StrongDual ℂ G), Continuous q ∧
        ∀ (n : ℕ) (x : Fin n → StrongDual ℂ G) (c : ℝ),
          (∀ Φ : StrongDual ℂ (StrongDual ℂ G), (∀ g, ‖Φ g‖ ≤ q g) → ∑ i, ‖Φ (x i)‖ ≤ c) →
          ∑ i, p (x i) ≤ c := by
    intro p hp
    obtain ⟨k, K, hK, hk⟩ := dual_abs_summing G hN hDF A hAb hAmono hAf p hp
    obtain ⟨qk, hqkc, hqk⟩ := strongDual_seminorm_of_bounded G hHL (A k) (hAb k)
    have hK1 : 0 < K + 1 := by linarith
    refine ⟨sc (K + 1) hK1.le qk, ?_, fun n x c hyp => ?_⟩
    · have : (fun g => sc (K + 1) hK1.le qk g) = fun g => (K + 1) * qk g :=
        funext fun g => sc_apply _ _ _ _
      change Continuous (fun g => sc (K + 1) hK1.le qk g)
      rw [this]
      exact continuous_const.mul hqkc
    · have hc0 : 0 ≤ c := by
        have h1 := hyp 0 (fun g => by
          rw [ContinuousLinearMap.zero_apply, norm_zero]
          exact apply_nonneg _ g)
        simpa using h1
      have h1 : ∀ y ∈ A k, ∑ i, ‖x i y‖ ≤ c / (K + 1) := by
        intro y hy
        let evl : StrongDual ℂ G →ₗ[ℂ] ℂ :=
          { toFun := fun f => f y
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        have hev : ∀ f, ‖evl f‖ ≤ qk f := fun f => hqk f y hy
        let Φ : StrongDual ℂ (StrongDual ℂ G) :=
          ⟨evl, continuous_of_le_seminorm qk hqkc evl hev⟩
        have h2 := hyp (((K + 1 : ℝ) : ℂ) • Φ) (fun g => by
          rw [ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg hK1.le, sc_apply]
          exact mul_le_mul_of_nonneg_left (hev g) hK1.le)
        rw [le_div_iff₀ hK1, Finset.sum_mul]
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) h2
        rw [ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg hK1.le, mul_comm]
        rfl
      have h2 := hk n x (c / (K + 1)) (div_nonneg hc0 hK1.le) h1
      refine h2.trans ?_
      rw [← mul_div_assoc, div_le_iff₀ hK1]
      nlinarith
  -- three Pietsch factorizations
  obtain ⟨p₀, hp₀c, hp₀⟩ := strongDual_seminorm_of_bounded G hHL B hBb
  obtain ⟨q₁, hq₁c, hq₁⟩ := hpair p₀ hp₀c
  obtain ⟨h₁, hh₁c, hp₀h₁, hh₁q₁, hpar₁, hsum₁⟩ :=
    pietsch_hilbertian_two_summing (StrongDual ℂ G) hF p₀ q₁ hp₀c hq₁c hq₁
  obtain ⟨q₂, hq₂c, hq₂⟩ := hpair q₁ hq₁c
  obtain ⟨h₂, hh₂c, hq₁h₂, hh₂q₂, hpar₂, hsum₂⟩ :=
    pietsch_hilbertian_two_summing (StrongDual ℂ G) hF q₁ q₂ hq₁c hq₂c hq₂
  obtain ⟨q₃, hq₃c, hq₃⟩ := hpair q₂ hq₂c
  obtain ⟨h₃, hh₃c, hq₂h₃, hh₃q₃, hpar₃, hsum₃⟩ :=
    pietsch_hilbertian_two_summing (StrongDual ℂ G) hF q₂ q₃ hq₂c hq₃c hq₃
  obtain ⟨φ, c, hc0, hcs, hφ, hdom⟩ :=
    quasinuclear_of_hilbertian_two_summing_chain (StrongDual ℂ G) hF h₁ h₂ h₃ hh₃c
      hpar₁ hpar₂ hpar₃
      (fun n x c hyp => hsum₁ n x c fun Φ hΦ => hyp Φ fun g => (hΦ g).trans (hq₁h₂ g))
      (fun n x c hyp => hsum₂ n x c fun Φ hΦ => hyp Φ fun g => (hΦ g).trans (hq₂h₃ g))
  -- the dominating functionals are evaluations at the points of a bounded set
  obtain ⟨D, hDb, hD⟩ := CNRepr.completeNuclear_strongBidual_bounded_repr G hC hN h₃ hh₃c
  choose y hyD hy using fun m => hD (φ m) (hφ m)
  refine ⟨y, c, hDb.subset ?_, hc0, hcs, fun f x hx => ?_⟩
  · rintro _ ⟨m, rfl⟩
    exact hyD m
  · have h1 := (hp₀ f x hx).trans ((hp₀h₁ f).trans (hdom f))
    refine h1.trans (le_of_eq ?_)
    exact tsum_congr fun m => by rw [hy m f]
