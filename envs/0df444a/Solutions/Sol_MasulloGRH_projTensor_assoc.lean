-- Prove2me | solution 1 for MasulloGRH.projTensor_assoc
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:09:39.925186+00:00
-- url     : https://prove2.me/submissions/ea3cb5ff-60bd-4e69-b646-64c0e46b5d52

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false

open MasulloGRH TensorProduct Topology

universe u

namespace ProjTensorAssocAux

/-- A polynormable topology is locally convex in the sense of the mission's definitions. -/
theorem lc_of_polynormable {X : Type u} [AddCommGroup X] [Module ℂ X] (t : TopologicalSpace X)
    (h : @PolynormableSpace ℂ X _ _ _ t) : IsLocallyConvexTopology X t := by
  letI := t
  exact ⟨{p : Seminorm ℂ X // Continuous p},
    ⟨⟨0, continuous_const⟩⟩, fun p => p.1,
    PolynormableSpace.withSeminorms ℂ X⟩

theorem polynormable_of_lc {X : Type u} [AddCommGroup X] [Module ℂ X] (t : TopologicalSpace X)
    (h : IsLocallyConvexTopology X t) : @PolynormableSpace ℂ X _ _ _ t := by
  obtain ⟨ι, _, p, hp⟩ := h
  exact hp.toPolynormableSpace

theorem addGroup_of_lc {X : Type u} [AddCommGroup X] [Module ℂ X] (t : TopologicalSpace X)
    (h : IsLocallyConvexTopology X t) : @IsTopologicalAddGroup X t _ := by
  obtain ⟨ι, _, p, hp⟩ := h
  exact hp.topologicalAddGroup

/-- The projective topology is locally convex. -/
theorem proj_lc (A B : Type u) [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] :
    IsLocallyConvexTopology (A ⊗[ℂ] B) (projTensorTopology A B) := by
  apply lc_of_polynormable
  unfold projTensorTopology
  apply PolynormableSpace.sInf
  intro t ht
  exact polynormable_of_lc t ht.1

/-- The canonical bilinear map is continuous for the projective topology. -/
theorem proj_tmul_continuous (A B : Type u) [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] :
    @Continuous (A × B) (A ⊗[ℂ] B) _ (projTensorTopology A B) (fun p => p.1 ⊗ₜ[ℂ] p.2) := by
  unfold projTensorTopology
  exact continuous_sInf_rng.2 fun t ht => ht.2

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
  let c : NNReal := ⟨ρ⁻¹, (inv_pos.2 hρ).le⟩
  have hval : ∀ x, (c • p0) x = ρ⁻¹ * p0 x := by
    intro x
    rw [Seminorm.smul_apply, NNReal.smul_def]
    rfl
  refine ⟨c • p0, ?_, ?_⟩
  · have : (fun x => (c • p0) x) = fun x => ρ⁻¹ * p0 x := funext hval
    change Continuous (fun x => (c • p0) x)
    rw [this]
    exact continuous_const.mul hsc
  · intro x hx
    apply hsub
    rw [Seminorm.mem_ball_zero]
    rw [hval, inv_mul_lt_iff₀ hρ] at hx
    simpa using hx

/-- A seminorm on `A ⊗ B` dominated on pure tensors by a product of continuous seminorms is
continuous for the projective topology. -/
theorem continuous_seminorm_proj {A B : Type u} [AddCommGroup A] [Module ℂ A]
    [TopologicalSpace A] [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]
    (N : Seminorm ℂ (A ⊗[ℂ] B)) (p : Seminorm ℂ A) (q : Seminorm ℂ B) (hp : Continuous p)
    (hq : Continuous q) (hN : ∀ a b, N (a ⊗ₜ[ℂ] b) ≤ p a * q b) :
    @Continuous _ _ (projTensorTopology A B) _ N := by
  let P : SeminormFamily ℂ (A ⊗[ℂ] B) PUnit.{u + 1} := fun _ => N
  let t : TopologicalSpace (A ⊗[ℂ] B) := P.moduleFilterBasis.topology
  have hP : @WithSeminorms ℂ (A ⊗[ℂ] B) PUnit.{u + 1} _ _ _ P t := ⟨rfl⟩
  have htLC : IsLocallyConvexTopology (A ⊗[ℂ] B) t := ⟨PUnit, ⟨⟨⟩⟩, P, hP⟩
  have htc : @Continuous (A × B) (A ⊗[ℂ] B) _ t (fun x => x.1 ⊗ₜ[ℂ] x.2) := by
    letI := t
    rw [continuous_iff_continuousAt]
    rintro ⟨a0, b0⟩
    refine (hP.tendsto_nhds _ _).2 ?_
    intro _ ε hε
    have hg : Continuous (fun x : A × B => p (x.1 - a0) * q x.2 + p a0 * q (x.2 - b0)) :=
      ((hp.comp (continuous_fst.sub continuous_const)).mul (hq.comp continuous_snd)).add
        (continuous_const.mul (hq.comp (continuous_snd.sub continuous_const)))
    have h0 : (fun x : A × B => p (x.1 - a0) * q x.2 + p a0 * q (x.2 - b0)) (a0, b0) < ε := by
      simpa using hε
    filter_upwards [hg.continuousAt.eventually (gt_mem_nhds h0)] with x hx
    refine lt_of_le_of_lt ?_ hx
    have hsplit : x.1 ⊗ₜ[ℂ] x.2 - a0 ⊗ₜ[ℂ] b0
        = (x.1 - a0) ⊗ₜ[ℂ] x.2 + a0 ⊗ₜ[ℂ] (x.2 - b0) := by
      rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub]; abel
    change N (x.1 ⊗ₜ[ℂ] x.2 - a0 ⊗ₜ[ℂ] b0) ≤ _
    rw [hsplit]
    exact (map_add_le_add N _ _).trans (add_le_add (hN _ _) (hN _ _))
  have hle : projTensorTopology A B ≤ t := sInf_le ⟨htLC, htc⟩
  have hNc : @Continuous _ _ t _ N := by
    letI := t
    exact hP.continuous_seminorm ⟨⟩
  exact continuous_le_dom hle hNc

/-- A continuous "trilinear" map into a locally convex space is bounded, through any continuous
seminorm of the target, by a product of continuous seminorms. -/
theorem trilinear_bound {A B C M : Type u} [AddCommGroup A] [Module ℂ A]
    [tA : TopologicalSpace A] [AddCommGroup B] [Module ℂ B] [tB : TopologicalSpace B]
    [AddCommGroup C] [Module ℂ C] [tC : TopologicalSpace C] [AddCommGroup M] [Module ℂ M]
    (hA : IsLocallyConvexTopology A tA) (hB : IsLocallyConvexTopology B tB)
    (hC : IsLocallyConvexTopology C tC) (t : TopologicalSpace M)
    (Φ : A ⊗[ℂ] B →ₗ[ℂ] C →ₗ[ℂ] M)
    (hΦ : @Continuous (A × B × C) M _ t (fun w => Φ (w.1 ⊗ₜ[ℂ] w.2.1) w.2.2))
    (r : Seminorm ℂ M) (hr : @Continuous _ _ t _ r) :
    ∃ (p : Seminorm ℂ A) (q : Seminorm ℂ B) (s : Seminorm ℂ C),
      Continuous p ∧ Continuous q ∧ Continuous s ∧
      ∀ a b c, r (Φ (a ⊗ₜ[ℂ] b) c) ≤ p a * q b * s c := by
  have hcomp : Continuous (fun w : A × B × C => r (Φ (w.1 ⊗ₜ[ℂ] w.2.1) w.2.2)) := by
    letI := t
    exact hr.comp hΦ
  have hmem : {w : A × B × C | r (Φ (w.1 ⊗ₜ[ℂ] w.2.1) w.2.2) < 1} ∈ 𝓝 ((0, 0, 0) : A × B × C) :=
    (isOpen_lt hcomp continuous_const).mem_nhds (by simp)
  rw [nhds_prod_eq, nhds_prod_eq] at hmem
  obtain ⟨U, hU, V', hV', hsub⟩ := Filter.mem_prod_iff.1 hmem
  obtain ⟨V, hV, W, hW, hsub'⟩ := Filter.mem_prod_iff.1 hV'
  obtain ⟨p, hpc, hp⟩ := exists_seminorm_ball_subset hA hU
  obtain ⟨q, hqc, hq⟩ := exists_seminorm_ball_subset hB hV
  obtain ⟨s, hsc, hs⟩ := exists_seminorm_ball_subset hC hW
  have hball : ∀ a b c, p a < 1 → q b < 1 → s c < 1 → r (Φ (a ⊗ₜ[ℂ] b) c) < 1 := by
    intro a b c ha hb hc
    have h1 : ((b, c) : B × C) ∈ V' := hsub' (Set.mk_mem_prod (hq b hb) (hs c hc))
    have h2 : ((a, b, c) : A × B × C) ∈ U ×ˢ V' := Set.mk_mem_prod (hp a ha) h1
    exact hsub h2
  have step1 : ∀ a b c, q b < 1 → s c < 1 → r (Φ (a ⊗ₜ[ℂ] b) c) ≤ p a := by
    intro a b c hb hc
    have := homog_bound p (fun a => r (Φ (a ⊗ₜ[ℂ] b) c)) (fun k a hk => by
      change r (Φ (((k : ℂ) • a) ⊗ₜ[ℂ] b) c) = k * r (Φ (a ⊗ₜ[ℂ] b) c)
      rw [← TensorProduct.smul_tmul', map_smul, LinearMap.smul_apply, map_smul_eq_mul,
        Complex.norm_real, Real.norm_of_nonneg hk.le]) 1 zero_le_one
      (fun a ha => (hball a b c ha hb hc).le) a
    simpa using this
  have step2 : ∀ a b c, s c < 1 → r (Φ (a ⊗ₜ[ℂ] b) c) ≤ p a * q b := by
    intro a b c hc
    exact homog_bound q (fun b => r (Φ (a ⊗ₜ[ℂ] b) c)) (fun k b hk => by
      change r (Φ (a ⊗ₜ[ℂ] ((k : ℂ) • b)) c) = k * r (Φ (a ⊗ₜ[ℂ] b) c)
      rw [TensorProduct.tmul_smul, map_smul, LinearMap.smul_apply, map_smul_eq_mul,
        Complex.norm_real, Real.norm_of_nonneg hk.le]) (p a) (apply_nonneg p a)
      (fun b hb => step1 a b c hb hc) b
  refine ⟨p, q, s, hpc, hqc, hsc, fun a b c => ?_⟩
  exact homog_bound s (fun c => r (Φ (a ⊗ₜ[ℂ] b) c)) (fun k c hk => by
    change r (Φ (a ⊗ₜ[ℂ] b) ((k : ℂ) • c)) = k * r (Φ (a ⊗ₜ[ℂ] b) c)
    rw [map_smul, map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg hk.le])
    (p a * q b) (mul_nonneg (apply_nonneg p a) (apply_nonneg q b))
    (fun c hc => step2 a b c hc) c

/-- **Currying for the projective topology.**  A bilinear map `Φ` on `(A ⊗ B) × C` with values in
a locally convex space is continuous for the projective topology on `A ⊗ B` as soon as the
trilinear map `(a, b, c) ↦ Φ (a ⊗ b) c` is continuous. -/
theorem continuous_curry {A B C M : Type u} [AddCommGroup A] [Module ℂ A]
    [tA : TopologicalSpace A] [AddCommGroup B] [Module ℂ B] [tB : TopologicalSpace B]
    [AddCommGroup C] [Module ℂ C] [tC : TopologicalSpace C] [AddCommGroup M] [Module ℂ M]
    (hA : IsLocallyConvexTopology A tA) (hB : IsLocallyConvexTopology B tB)
    (hC : IsLocallyConvexTopology C tC) (t : TopologicalSpace M)
    (ht : IsLocallyConvexTopology M t) (Φ : A ⊗[ℂ] B →ₗ[ℂ] C →ₗ[ℂ] M)
    (hΦ : @Continuous (A × B × C) M _ t (fun w => Φ (w.1 ⊗ₜ[ℂ] w.2.1) w.2.2)) :
    @Continuous ((A ⊗[ℂ] B) × C) M (@instTopologicalSpaceProd _ _ (projTensorTopology A B) tC) t
      (fun w => Φ w.1 w.2) := by
  obtain ⟨ι, _, P, hP⟩ := ht
  have hAg : IsTopologicalAddGroup A := addGroup_of_lc tA hA
  have hBg : IsTopologicalAddGroup B := addGroup_of_lc tB hB
  have hCg : IsTopologicalAddGroup C := addGroup_of_lc tC hC
  letI tπ : TopologicalSpace (A ⊗[ℂ] B) := projTensorTopology A B
  have hπg : IsTopologicalAddGroup (A ⊗[ℂ] B) := addGroup_of_lc _ (proj_lc A B)
  letI := t
  rw [continuous_iff_continuousAt]
  rintro ⟨u0, c0⟩
  refine (hP.tendsto_nhds _ _).2 ?_
  intro i ε hε
  obtain ⟨p, q, s, hpc, hqc, hsc, hbd⟩ :=
    trilinear_bound hA hB hC t Φ hΦ (P i) (hP.continuous_seminorm i)
  -- the seminorm `N u = sup_{s c < 1} P i (Φ u c)`
  let fam : {c : C // s c < 1} → Seminorm ℂ (A ⊗[ℂ] B) := fun c => (P i).comp (Φ.flip c.1)
  have hfam : ∀ (c : {c : C // s c < 1}) (u : A ⊗[ℂ] B), fam c u = P i (Φ u c.1) :=
    fun c u => rfl
  have hne : Nonempty {c : C // s c < 1} := ⟨⟨0, by simp⟩⟩
  have hbddpt : ∀ u : A ⊗[ℂ] B, ∃ K : ℝ, ∀ c : C, s c < 1 → P i (Φ u c) ≤ K := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, fun c _ => by simp⟩
    | tmul a b =>
      refine ⟨p a * q b, fun c hc => (hbd a b c).trans ?_⟩
      have h0 : 0 ≤ p a * q b := mul_nonneg (apply_nonneg p a) (apply_nonneg q b)
      nlinarith [apply_nonneg s c]
    | add v w hv hw =>
      obtain ⟨K1, h1⟩ := hv
      obtain ⟨K2, h2⟩ := hw
      refine ⟨K1 + K2, fun c hc => ?_⟩
      rw [map_add, LinearMap.add_apply]
      exact (map_add_le_add (P i) _ _).trans (add_le_add (h1 c hc) (h2 c hc))
  have hbdd : BddAbove (Set.range fam) := by
    rw [Seminorm.bddAbove_range_iff]
    intro u
    obtain ⟨K, hK⟩ := hbddpt u
    refine ⟨K, ?_⟩
    rintro _ ⟨c, rfl⟩
    exact hK c.1 c.2
  let N : Seminorm ℂ (A ⊗[ℂ] B) := ⨆ c, fam c
  have hNapp : ∀ u, N u = ⨆ c, fam c u := fun u => Seminorm.iSup_apply hbdd
  have hNge : ∀ (u : A ⊗[ℂ] B) (c : C), s c < 1 → P i (Φ u c) ≤ N u := by
    intro u c hc
    rw [hNapp]
    exact le_ciSup (f := fun c : {c : C // s c < 1} => fam c u)
      (Seminorm.bddAbove_range_iff.1 hbdd u) ⟨c, hc⟩
  have hNle : ∀ a b, N (a ⊗ₜ[ℂ] b) ≤ p a * q b := by
    intro a b
    rw [hNapp]
    refine ciSup_le fun c => ?_
    rw [hfam]
    refine (hbd a b c.1).trans ?_
    have h0 : 0 ≤ p a * q b := mul_nonneg (apply_nonneg p a) (apply_nonneg q b)
    nlinarith [apply_nonneg s c.1, c.2]
  have hNs : ∀ (u : A ⊗[ℂ] B) (c : C), P i (Φ u c) ≤ N u * s c := by
    intro u c
    exact homog_bound s (fun c => P i (Φ u c)) (fun k c hk => by
      change P i (Φ u ((k : ℂ) • c)) = k * P i (Φ u c)
      rw [map_smul, map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg hk.le])
      (N u) (apply_nonneg N u) (fun c hc => hNge u c hc) c
  have hNc : Continuous N := continuous_seminorm_proj N p q hpc hqc hNle
  have hg : Continuous (fun w : (A ⊗[ℂ] B) × C => N (w.1 - u0) * s w.2 + N u0 * s (w.2 - c0)) :=
    ((hNc.comp (continuous_fst.sub continuous_const)).mul (hsc.comp continuous_snd)).add
      (continuous_const.mul (hsc.comp (continuous_snd.sub continuous_const)))
  have h0 : (fun w : (A ⊗[ℂ] B) × C => N (w.1 - u0) * s w.2 + N u0 * s (w.2 - c0)) (u0, c0)
      < ε := by
    simpa using hε
  filter_upwards [hg.continuousAt.eventually (gt_mem_nhds h0)] with w hw
  refine lt_of_le_of_lt ?_ hw
  have hsplit : Φ w.1 w.2 - Φ u0 c0 = Φ (w.1 - u0) w.2 + Φ u0 (w.2 - c0) := by
    simp only [map_sub, LinearMap.sub_apply]; abel
  change P i (Φ w.1 w.2 - Φ u0 c0) ≤ _
  rw [hsplit]
  exact (map_add_le_add (P i) _ _).trans (add_le_add (hNs _ _) (hNs _ _))

/-- `(E ⊗_π F) ⊗_π G` carries the finest locally convex topology making the trilinear map
`(x, y, z) ↦ (x ⊗ y) ⊗ z` continuous. -/
theorem proj_left_eq (E F G : Type u) [AddCommGroup E] [Module ℂ E] [tE : TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [tF : TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [tG : TopologicalSpace G]
    (hE : IsLocallyConvexTopology E tE) (hF : IsLocallyConvexTopology F tF)
    (hG : IsLocallyConvexTopology G tG) :
    @projTensorTopology (E ⊗[ℂ] F) _ _ (projTensorTopology E F) G _ _ _ =
      sInf {t | IsLocallyConvexTopology ((E ⊗[ℂ] F) ⊗[ℂ] G) t ∧
        @Continuous (E × F × G) _ _ t (fun w => (w.1 ⊗ₜ[ℂ] w.2.1) ⊗ₜ[ℂ] w.2.2)} := by
  unfold projTensorTopology
  congr 1
  ext t
  refine and_congr_right fun hLC => ⟨fun h => ?_, fun h => ?_⟩
  · have hm : @Continuous (E × F × G) ((E ⊗[ℂ] F) × G) _
        (@instTopologicalSpaceProd _ _ (projTensorTopology E F) tG)
        (fun w => (w.1 ⊗ₜ[ℂ] w.2.1, w.2.2)) := by
      letI : TopologicalSpace (E ⊗[ℂ] F) := projTensorTopology E F
      exact ((proj_tmul_continuous E F).comp
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (continuous_snd.comp continuous_snd)
    have key := @Continuous.comp _ _ _ _ (@instTopologicalSpaceProd _ _ (projTensorTopology E F) tG) t
      _ _ h hm
    exact key
  · exact continuous_curry hE hF hG t hLC (TensorProduct.mk ℂ (E ⊗[ℂ] F) G) h

/-- `E ⊗_π (F ⊗_π G)` carries the finest locally convex topology making the trilinear map
`(x, y, z) ↦ x ⊗ (y ⊗ z)` continuous. -/
theorem proj_right_eq (E F G : Type u) [AddCommGroup E] [Module ℂ E] [tE : TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [tF : TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [tG : TopologicalSpace G]
    (hE : IsLocallyConvexTopology E tE) (hF : IsLocallyConvexTopology F tF)
    (hG : IsLocallyConvexTopology G tG) :
    @projTensorTopology E _ _ _ (F ⊗[ℂ] G) _ _ (projTensorTopology F G) =
      sInf {t | IsLocallyConvexTopology (E ⊗[ℂ] (F ⊗[ℂ] G)) t ∧
        @Continuous (E × F × G) _ _ t (fun w => w.1 ⊗ₜ[ℂ] (w.2.1 ⊗ₜ[ℂ] w.2.2))} := by
  unfold projTensorTopology
  congr 1
  ext t
  refine and_congr_right fun hLC => ⟨fun h => ?_, fun h => ?_⟩
  · have hm : @Continuous (E × F × G) (E × (F ⊗[ℂ] G)) _
        (@instTopologicalSpaceProd _ _ tE (projTensorTopology F G))
        (fun w => (w.1, w.2.1 ⊗ₜ[ℂ] w.2.2)) := by
      letI : TopologicalSpace (F ⊗[ℂ] G) := projTensorTopology F G
      exact continuous_fst.prodMk ((proj_tmul_continuous F G).comp continuous_snd)
    have key := @Continuous.comp _ _ _ _ (@instTopologicalSpaceProd _ _ tE (projTensorTopology F G)) t
      _ _ h hm
    exact key
  · have hperm : @Continuous (F × G × E) (E ⊗[ℂ] (F ⊗[ℂ] G)) _ t
        (fun w => (TensorProduct.mk ℂ E (F ⊗[ℂ] G)).flip (w.1 ⊗ₜ[ℂ] w.2.1) w.2.2) := by
      have hσ : Continuous (fun w : F × G × E => ((w.2.2, w.1, w.2.1) : E × F × G)) :=
        (continuous_snd.comp continuous_snd).prodMk
          (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
      have key := @Continuous.comp _ _ _ _ _ t _ _ h hσ
      exact key
    have hc := continuous_curry hF hG hE t hLC (TensorProduct.mk ℂ E (F ⊗[ℂ] G)).flip hperm
    letI : TopologicalSpace (F ⊗[ℂ] G) := projTensorTopology F G
    have hswap : Continuous (fun w : E × (F ⊗[ℂ] G) => ((w.2, w.1) : (F ⊗[ℂ] G) × E)) :=
      continuous_snd.prodMk continuous_fst
    have key := @Continuous.comp _ _ _ _ _ t _ _ hc hswap
    exact key

end ProjTensorAssocAux

open ProjTensorAssocAux in
theorem solution (E F G : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (hE : IsHLCS E) (hF : IsHLCS F) (hG : IsHLCS G) :
    @projTensorTopology (E ⊗[ℂ] F) _ _ (projTensorTopology E F) G _ _ _ =
      TopologicalSpace.induced (TensorProduct.assoc ℂ E F G)
        (@projTensorTopology E _ _ _ (F ⊗[ℂ] G) _ _ (projTensorTopology F G)) := by
  rw [proj_left_eq E F G hE.1 hF.1 hG.1, proj_right_eq E F G hE.1 hF.1 hG.1, induced_sInf]
  congr 1
  ext t
  constructor
  · rintro ⟨hLC, hc⟩
    refine ⟨TopologicalSpace.induced (TensorProduct.assoc ℂ E F G).symm t, ⟨?_, ?_⟩, ?_⟩
    · letI := t
      have := polynormable_of_lc t hLC
      exact lc_of_polynormable _
        (PolynormableSpace.induced
          ((TensorProduct.assoc ℂ E F G).symm : E ⊗[ℂ] (F ⊗[ℂ] G) →ₗ[ℂ] (E ⊗[ℂ] F) ⊗[ℂ] G))
    · rw [continuous_induced_rng]
      have hfun : ((TensorProduct.assoc ℂ E F G).symm ∘
          fun w : E × F × G => w.1 ⊗ₜ[ℂ] (w.2.1 ⊗ₜ[ℂ] w.2.2)) =
          fun w => (w.1 ⊗ₜ[ℂ] w.2.1) ⊗ₜ[ℂ] w.2.2 := by
        funext w; simp
      rw [hfun]
      exact hc
    · rw [induced_compose]
      have hid : ((TensorProduct.assoc ℂ E F G).symm ∘ (TensorProduct.assoc ℂ E F G)) = id := by
        funext w; simp
      rw [hid, induced_id]
  · rintro ⟨t', ⟨hLC, hc⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · letI := t'
      have := polynormable_of_lc t' hLC
      exact lc_of_polynormable _
        (PolynormableSpace.induced
          ((TensorProduct.assoc ℂ E F G) : (E ⊗[ℂ] F) ⊗[ℂ] G →ₗ[ℂ] E ⊗[ℂ] (F ⊗[ℂ] G)))
    · rw [continuous_induced_rng]
      have hfun : ((TensorProduct.assoc ℂ E F G) ∘
          fun w : E × F × G => (w.1 ⊗ₜ[ℂ] w.2.1) ⊗ₜ[ℂ] w.2.2) =
          fun w => w.1 ⊗ₜ[ℂ] (w.2.1 ⊗ₜ[ℂ] w.2.2) := by
        funext w; simp
      rw [hfun]
      exact hc
