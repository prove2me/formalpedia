-- Prove2me | solution 1 for MasulloGRH.projTensor_nhds_zero_hasBasis
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:06:23.136943+00:00
-- url     : https://prove2.me/submissions/aa0b9abf-ced1-405b-80ec-15aa094f90e8

import Definitions.Def_MasulloGRH_LocallyConvex

open TensorProduct Topology Filter
open scoped ComplexOrder
set_option autoImplicit false
universe u v

namespace Sol_MasulloGRH_projTensor_nhds_zero_hasBasis

open MasulloGRH Set Pointwise

section algebraic

variable {E F : Type u} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]

/-- The convex circled hull of the elementary tensors `x ⊗ y` with `P x < r`, `Q y < s`. -/
def Gam (P : Seminorm ℂ E) (Q : Seminorm ℂ F) (r s : ℝ) : Set (E ⊗[ℂ] F) :=
  absConvexHull ℂ (image2 (fun x y => x ⊗ₜ[ℂ] y) (P.ball 0 r) (Q.ball 0 s))

variable (P : Seminorm ℂ E) (Q : Seminorm ℂ F) (r s : ℝ)

theorem balanced_Gam : Balanced ℂ (Gam P Q r s) := balanced_absConvexHull

theorem convex_Gam : Convex ℂ (Gam P Q r s) := convex_absConvexHull

theorem convex_real_Gam : Convex ℝ (Gam P Q r s) :=
  convex_RCLike_iff_convex_real.1 (convex_Gam P Q r s)

/-- An elementary tensor `x ⊗ y` with `P x < r ‖c‖`, `Q y < s ‖d‖` lies in `(c d) Γ`. -/
theorem tmul_eq_smul {x : E} {y : F} {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0)
    (hx : P x < r * ‖c‖) (hy : Q y < s * ‖d‖) :
    ∃ g ∈ Gam P Q r s, x ⊗ₜ[ℂ] y = (c * d) • g := by
  refine ⟨(c⁻¹ • x) ⊗ₜ[ℂ] (d⁻¹ • y), subset_absConvexHull ⟨c⁻¹ • x, ?_, d⁻¹ • y, ?_, rfl⟩, ?_⟩
  · rw [Seminorm.mem_ball, sub_zero, map_smul_eq_mul, norm_inv, inv_mul_lt_iff₀ (norm_pos_iff.2 hc)]
    linarith [mul_comm r ‖c‖]
  · rw [Seminorm.mem_ball, sub_zero, map_smul_eq_mul, norm_inv, inv_mul_lt_iff₀ (norm_pos_iff.2 hd)]
    linarith [mul_comm s ‖d‖]
  · rw [TensorProduct.smul_tmul_smul, smul_smul]
    have : c * d * (c⁻¹ * d⁻¹) = 1 := by field_simp
    rw [this, one_smul]

/-- Every tensor is a positive multiple of an element of `Γ`. -/
theorem exists_eq_smul (hr : 0 < r) (hs : 0 < s) (u : E ⊗[ℂ] F) :
    ∃ c : ℝ, 0 < c ∧ ∃ g ∈ Gam P Q r s, u = (c : ℂ) • g := by
  have h0 : (0 : E ⊗[ℂ] F) ∈ Gam P Q r s := by
    refine (balanced_Gam P Q r s).zero_mem ⟨(0 : E) ⊗ₜ[ℂ] (0 : F), subset_absConvexHull ?_⟩
    exact ⟨0, by simpa using hr, 0, by simpa using hs, rfl⟩
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, 0, h0, by simp⟩
  | tmul x y =>
    have ha : 0 < P x / r + 1 := by positivity
    have hb : 0 < Q y / s + 1 := by positivity
    obtain ⟨g, hg, h⟩ := tmul_eq_smul P Q r s (x := x) (y := y)
      (c := ((P x / r + 1 : ℝ) : ℂ)) (d := ((Q y / s + 1 : ℝ) : ℂ))
      (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')
      (by
        rw [Complex.norm_real, Real.norm_of_nonneg ha.le, mul_add, mul_div_cancel₀ _ hr.ne']
        linarith)
      (by
        rw [Complex.norm_real, Real.norm_of_nonneg hb.le, mul_add, mul_div_cancel₀ _ hs.ne']
        linarith)
    refine ⟨(P x / r + 1) * (Q y / s + 1), mul_pos ha hb, g, hg, ?_⟩
    rw [h]
    push_cast
    rfl
  | add u v hu hv =>
    obtain ⟨c₁, hc₁, g₁, hg₁, rfl⟩ := hu
    obtain ⟨c₂, hc₂, g₂, hg₂, rfl⟩ := hv
    have hc : 0 < c₁ + c₂ := add_pos hc₁ hc₂
    refine ⟨c₁ + c₂, hc, ((c₁ / (c₁ + c₂) : ℝ) : ℂ) • g₁ + ((c₂ / (c₁ + c₂) : ℝ) : ℂ) • g₂, ?_, ?_⟩
    · refine convex_Gam P Q r s hg₁ hg₂ ?_ ?_ ?_
      · exact Complex.zero_le_real.2 (div_pos hc₁ hc).le
      · exact Complex.zero_le_real.2 (div_pos hc₂ hc).le
      · rw [← Complex.ofReal_add, ← add_div, div_self hc.ne', Complex.ofReal_one]
    · rw [smul_add, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        mul_div_cancel₀ _ hc.ne', mul_div_cancel₀ _ hc.ne']

/-- `Γ` is absorbing. -/
theorem absorbent_Gam (hr : 0 < r) (hs : 0 < s) : Absorbent ℝ (Gam P Q r s) := by
  intro u
  obtain ⟨c, hc, g, hg, rfl⟩ := exists_eq_smul P Q r s hr hs u
  rw [absorbs_iff_norm]
  refine ⟨c, fun a ha => ?_⟩
  rw [Real.norm_eq_abs] at ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
    linarith
  rw [singleton_subset_iff]
  refine ⟨((c / a : ℝ) : ℂ) • g, ?_, ?_⟩
  · refine balanced_iff_smul_mem.1 (balanced_Gam P Q r s) ?_ hg
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hc]
    exact div_le_one_of_le₀ ha (abs_nonneg a)
  · show a • ((c / a : ℝ) : ℂ) • g = (c : ℂ) • g
    rw [← algebraMap_smul ℂ a (((c / a : ℝ) : ℂ) • g), smul_smul, Complex.coe_algebraMap,
      ← Complex.ofReal_mul, mul_div_cancel₀ _ ha0]

/-- The gauge of `Γ`, as a seminorm on `E ⊗ F`. -/
noncomputable def gam (hr : 0 < r) (hs : 0 < s) : Seminorm ℂ (E ⊗[ℂ] F) :=
  gaugeSeminorm (balanced_Gam P Q r s) (convex_real_Gam P Q r s) (absorbent_Gam P Q r s hr hs)

theorem gam_apply (hr : 0 < r) (hs : 0 < s) (u : E ⊗[ℂ] F) :
    gam P Q r s hr hs u = gauge (Gam P Q r s) u := rfl

/-- The cross estimate `γ(x ⊗ y) ≤ a b` when `P x < r a` and `Q y < s b`. -/
theorem gam_tmul_le (hr : 0 < r) (hs : 0 < s) {x : E} {y : F} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : P x < r * a) (hy : Q y < s * b) : gam P Q r s hr hs (x ⊗ₜ[ℂ] y) ≤ a * b := by
  obtain ⟨g, hg, h⟩ := tmul_eq_smul P Q r s (x := x) (y := y) (c := (a : ℂ)) (d := (b : ℂ))
    (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')
    (by rwa [Complex.norm_real, Real.norm_of_nonneg ha.le])
    (by rwa [Complex.norm_real, Real.norm_of_nonneg hb.le])
  rw [h, map_smul_eq_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg ha.le, Real.norm_of_nonneg hb.le]
  have h1 : gam P Q r s hr hs g ≤ 1 := gauge_le_one_of_mem hg
  nlinarith [mul_pos ha hb]

/-- The open unit ball of the gauge of `Γ` is contained in `Γ`. -/
theorem gam_ball_subset (hr : 0 < r) (hs : 0 < s) :
    (gam P Q r s hr hs).ball 0 1 ⊆ Gam P Q r s := by
  intro u hu
  rw [Seminorm.mem_ball, sub_zero] at hu
  exact setOfPred_gauge_lt_one_subset_self (convex_real_Gam P Q r s)
    (absorbent_Gam P Q r s hr hs).zero_mem (absorbent_Gam P Q r s hr hs) hu

/-- The topology on `E ⊗ F` defined by the single seminorm `γ`. -/
@[reducible]
noncomputable def gamTopology (P : Seminorm ℂ E) (Q : Seminorm ℂ F) (r s : ℝ) (hr : 0 < r)
    (hs : 0 < s) : TopologicalSpace (E ⊗[ℂ] F) :=
  (SeminormFamily.moduleFilterBasis (fun _ : PUnit.{u + 1} => gam P Q r s hr hs)).topology

theorem gamTopology_withSeminorms (P : Seminorm ℂ E) (Q : Seminorm ℂ F) (r s : ℝ) (hr : 0 < r)
    (hs : 0 < s) :
    @WithSeminorms ℂ (E ⊗[ℂ] F) PUnit.{u + 1} _ _ _ (fun _ => gam P Q r s hr hs)
      (gamTopology P Q r s hr hs) :=
  @WithSeminorms.mk ℂ (E ⊗[ℂ] F) PUnit.{u + 1} _ _ _ _ (gamTopology P Q r s hr hs) rfl

/-- `Γ` is a neighbourhood of `0` for the topology of its gauge. -/
theorem Gam_mem_nhds (P : Seminorm ℂ E) (Q : Seminorm ℂ F) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    Gam P Q r s ∈ @nhds (E ⊗[ℂ] F) (gamTopology P Q r s hr hs) 0 := by
  let _ : TopologicalSpace (E ⊗[ℂ] F) := gamTopology P Q r s hr hs
  have hw := gamTopology_withSeminorms P Q r s hr hs
  have hc : Continuous (gam P Q r s hr hs) := hw.continuous_seminorm PUnit.unit
  have hopen : IsOpen ((gam P Q r s hr hs).ball 0 1) := by
    have : (gam P Q r s hr hs).ball 0 1 = (gam P Q r s hr hs) ⁻¹' (Iio 1) := by
      ext u
      simp [Seminorm.mem_ball]
    rw [this]
    exact isOpen_Iio.preimage hc
  exact Filter.mem_of_superset (hopen.mem_nhds (by simp [Seminorm.mem_ball]))
    (gam_ball_subset P Q r s hr hs)

end algebraic

section topological

variable {E F : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- The canonical bilinear map is continuous into `E ⊗ F` with the topology of `γ`, provided `P`
and `Q` are continuous. -/
theorem continuous_tmul_gamTopology (P : Seminorm ℂ E) (Q : Seminorm ℂ F) (r s : ℝ) (hr : 0 < r)
    (hs : 0 < s) (hP : ∀ (x₀ : E) (ε : ℝ), 0 < ε → ∀ᶠ x in 𝓝 x₀, P (x - x₀) < ε)
    (hQ : ∀ (y₀ : F) (ε : ℝ), 0 < ε → ∀ᶠ y in 𝓝 y₀, Q (y - y₀) < ε) :
    @Continuous (E × F) (E ⊗[ℂ] F) _ (gamTopology P Q r s hr hs) (fun p => p.1 ⊗ₜ[ℂ] p.2) := by
  let _ : TopologicalSpace (E ⊗[ℂ] F) := gamTopology P Q r s hr hs
  have hw := gamTopology_withSeminorms P Q r s hr hs
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, y₀⟩
  refine (hw.tendsto_nhds _ _).2 fun _ ε hε => ?_
  have ha : 0 < P x₀ / r + 1 := by positivity
  have hb : 0 < Q y₀ / s + 1 := by positivity
  set a := P x₀ / r + 1 with ha_def
  set b := Q y₀ / s + 1 with hb_def
  have hxa : P x₀ < r * a := by
    rw [ha_def, mul_add, mul_div_cancel₀ _ hr.ne']
    linarith
  have hyb : Q y₀ < s * b := by
    rw [hb_def, mul_add, mul_div_cancel₀ _ hs.ne']
    linarith
  have hab : 0 < 1 + a + b := by positivity
  set δ := min 1 (ε / (2 * (1 + a + b))) with hδ_def
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ * (1 + a + b) ≤ ε / 2 := by
    have h2 : δ ≤ ε / (2 * (1 + a + b)) := min_le_right _ _
    calc δ * (1 + a + b) ≤ ε / (2 * (1 + a + b)) * (1 + a + b) :=
          mul_le_mul_of_nonneg_right h2 hab.le
      _ = ε / 2 := by field_simp
  filter_upwards [(hP x₀ (r * δ) (mul_pos hr hδ)).prod_nhds (hQ y₀ (s * δ) (mul_pos hs hδ))]
    with z hz
  obtain ⟨hz1, hz2⟩ := hz
  have hid : z.1 ⊗ₜ[ℂ] z.2 - x₀ ⊗ₜ[ℂ] y₀ =
      (z.1 - x₀) ⊗ₜ[ℂ] (z.2 - y₀) + x₀ ⊗ₜ[ℂ] (z.2 - y₀) + (z.1 - x₀) ⊗ₜ[ℂ] y₀ := by
    simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    abel
  show gam P Q r s hr hs (z.1 ⊗ₜ[ℂ] z.2 - x₀ ⊗ₜ[ℂ] y₀) < ε
  rw [hid]
  have e1 := gam_tmul_le P Q r s hr hs hδ hδ hz1 hz2
  have e2 := gam_tmul_le P Q r s hr hs ha hδ hxa hz2
  have e3 := gam_tmul_le P Q r s hr hs hδ hb hz1 hyb
  have e4 := map_add_le_add (gam P Q r s hr hs)
    ((z.1 - x₀) ⊗ₜ[ℂ] (z.2 - y₀) + x₀ ⊗ₜ[ℂ] (z.2 - y₀)) ((z.1 - x₀) ⊗ₜ[ℂ] y₀)
  have e5 := map_add_le_add (gam P Q r s hr hs)
    ((z.1 - x₀) ⊗ₜ[ℂ] (z.2 - y₀)) (x₀ ⊗ₜ[ℂ] (z.2 - y₀))
  have e6 : δ * δ ≤ δ * 1 := mul_le_mul_of_nonneg_left hδ1 hδ.le
  nlinarith

/-- The convex circled hull of `U ⊗ V` is a neighbourhood of `0` for the projective topology. -/
theorem absConvexHull_mem_nhds (hE : IsHLCS E) (hF : IsHLCS F) {U : Set E} {V : Set F}
    (hU : U ∈ 𝓝 (0 : E)) (hV : V ∈ 𝓝 (0 : F)) :
    absConvexHull ℂ (image2 (fun x y => x ⊗ₜ[ℂ] y) U V) ∈
      @nhds (E ⊗[ℂ] F) (projTensorTopology E F) 0 := by
  obtain ⟨ι, _, p, hp⟩ := hE.1
  obtain ⟨κ, _, q, hq⟩ := hF.1
  obtain ⟨⟨I, r⟩, hr, hIU⟩ := hp.hasBasis_zero_ball.mem_iff.1 hU
  obtain ⟨⟨J, s⟩, hs, hJV⟩ := hq.hasBasis_zero_ball.mem_iff.1 hV
  have hr : 0 < r := hr
  have hs : 0 < s := hs
  have hmem : gamTopology (I.sup p) (J.sup q) r s hr hs ∈
      {t | IsLocallyConvexTopology (E ⊗[ℂ] F) t ∧
        @Continuous (E × F) (E ⊗[ℂ] F) _ t (fun p => p.1 ⊗ₜ[ℂ] p.2)} := by
    refine ⟨⟨PUnit.{u + 1}, inferInstance, _, gamTopology_withSeminorms _ _ r s hr hs⟩, ?_⟩
    refine continuous_tmul_gamTopology _ _ r s hr hs (fun x₀ ε hε => ?_) (fun y₀ ε hε => ?_)
    · exact hp.hasBasis_ball.mem_of_mem (i := (I, ε)) hε
    · exact hq.hasBasis_ball.mem_of_mem (i := (J, ε)) hε
  have hle : projTensorTopology E F ≤ gamTopology (I.sup p) (J.sup q) r s hr hs := sInf_le hmem
  refine Filter.mem_of_superset (nhds_mono hle (Gam_mem_nhds _ _ r s hr hs)) ?_
  exact absConvexHull_mono (image2_subset hIU hJV)

/-- Every neighbourhood of `0` for a locally convex topology on `E ⊗ F` making `⊗` continuous
contains the convex circled hull of some `U ⊗ V`. -/
theorem exists_absConvexHull_subset (t : TopologicalSpace (E ⊗[ℂ] F))
    (ht : IsLocallyConvexTopology (E ⊗[ℂ] F) t)
    (hc : @Continuous (E × F) (E ⊗[ℂ] F) _ t (fun p => p.1 ⊗ₜ[ℂ] p.2))
    {W : Set (E ⊗[ℂ] F)} (hW : W ∈ @nhds (E ⊗[ℂ] F) t 0) :
    ∃ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 (0 : F),
      absConvexHull ℂ (image2 (fun x y => x ⊗ₜ[ℂ] y) U V) ⊆ W := by
  let _ : TopologicalSpace (E ⊗[ℂ] F) := t
  obtain ⟨ι, _, q, hq⟩ := ht
  obtain ⟨⟨I, r⟩, hr, hsub⟩ := hq.hasBasis_zero_ball.mem_iff.1 hW
  have hball : (I.sup q).ball 0 r ∈ 𝓝 (0 : E ⊗[ℂ] F) := hq.hasBasis_zero_ball.mem_of_mem hr
  have hpre : (fun p : E × F => p.1 ⊗ₜ[ℂ] p.2) ⁻¹' ((I.sup q).ball 0 r) ∈ 𝓝 ((0 : E), (0 : F)) := by
    refine hc.continuousAt.preimage_mem_nhds ?_
    simpa using hball
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hpre
  obtain ⟨U, hU, V, hV, hUV⟩ := hpre
  refine ⟨U, hU, V, hV, (absConvexHull_min ?_ ⟨(I.sup q).balanced_ball_zero r, ?_⟩).trans hsub⟩
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    exact hUV (Set.mk_mem_prod hx hy)
  · exact convex_RCLike_iff_convex_real.2 (Seminorm.convex_ball _ _ _)

end topological

end Sol_MasulloGRH_projTensor_nhds_zero_hasBasis

open MasulloGRH Sol_MasulloGRH_projTensor_nhds_zero_hasBasis

theorem solution (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsHLCS E) (hF : IsHLCS F) :
    (@nhds (E ⊗[ℂ] F) (projTensorTopology E F) 0).HasBasis
      (fun UV : Set E × Set F => UV.1 ∈ 𝓝 (0 : E) ∧ UV.2 ∈ 𝓝 (0 : F))
      (fun UV => absConvexHull ℂ (Set.image2 (fun x y => x ⊗ₜ[ℂ] y) UV.1 UV.2)) := by
  -- the sets `Γ(U ⊗ V)` form a filter basis
  have hB : Filter.IsBasis (fun UV : Set E × Set F => UV.1 ∈ 𝓝 (0 : E) ∧ UV.2 ∈ 𝓝 (0 : F))
      (fun UV => absConvexHull ℂ (Set.image2 (fun x y => x ⊗ₜ[ℂ] y) UV.1 UV.2)) :=
    { nonempty := ⟨(Set.univ, Set.univ), Filter.univ_mem, Filter.univ_mem⟩
      inter := by
        rintro ⟨U, V⟩ ⟨U', V'⟩ ⟨hU, hV⟩ ⟨hU', hV'⟩
        exact ⟨(U ∩ U', V ∩ V'), ⟨Filter.inter_mem hU hU', Filter.inter_mem hV hV'⟩,
          Set.subset_inter
            (absConvexHull_mono (Set.image2_subset Set.inter_subset_left Set.inter_subset_left))
            (absConvexHull_mono
              (Set.image2_subset Set.inter_subset_right Set.inter_subset_right))⟩ }
  -- the filter it generates is finer than the neighbourhood filter of `0` of every locally
  -- convex topology making `⊗` continuous, hence finer than their infimum
  have h1 : hB.filter ≤ @nhds (E ⊗[ℂ] F) (projTensorTopology E F) 0 := by
    unfold projTensorTopology
    rw [nhds_sInf]
    refine le_iInf₂ fun t ht W hW => ?_
    obtain ⟨U, hU, V, hV, hsub⟩ := exists_absConvexHull_subset t ht.1 ht.2 hW
    exact hB.mem_filter_iff.2 ⟨(U, V), ⟨hU, hV⟩, hsub⟩
  -- each `Γ(U ⊗ V)` is a neighbourhood of `0` for the projective topology
  have h2 : @nhds (E ⊗[ℂ] F) (projTensorTopology E F) 0 ≤ hB.filter := by
    intro W hW
    obtain ⟨⟨U, V⟩, ⟨hU, hV⟩, hsub⟩ := hB.mem_filter_iff.1 hW
    exact Filter.mem_of_superset (absConvexHull_mem_nhds hE hF hU hV) hsub
  rw [le_antisymm h2 h1]
  exact hB.hasBasis
