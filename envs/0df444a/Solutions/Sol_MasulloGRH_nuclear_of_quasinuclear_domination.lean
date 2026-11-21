-- Prove2me | solution 1 for MasulloGRH.nuclear_of_quasinuclear_domination
-- status  : ACCEPTED   (prove)
-- author  : @ijawdoij123
-- created : 2026-11-20T23:32:57.288504+00:00
-- url     : https://prove2.me/submissions/11d3e86d-25df-4719-bfbd-b574a32d15e0

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_quasinuclear_comp_nuclear_expansion

set_option autoImplicit false

open MasulloGRH
open TensorProduct Topology Filter

universe u

/-! ### Locally convex generalities -/

private theorem polynormable_of_lc {X : Type u} [AddCommGroup X] [Module ℂ X]
    (t : TopologicalSpace X) (h : IsLocallyConvexTopology X t) : @PolynormableSpace ℂ X _ _ _ t := by
  obtain ⟨ι, _, p, hp⟩ := h
  exact hp.toPolynormableSpace

private theorem addGroup_of_lc {X : Type u} [AddCommGroup X] [Module ℂ X] (t : TopologicalSpace X)
    (h : IsLocallyConvexTopology X t) : @IsTopologicalAddGroup X t _ := by
  obtain ⟨ι, _, p, hp⟩ := h
  exact hp.topologicalAddGroup

private theorem lc_of_polynormable {X : Type u} [AddCommGroup X] [Module ℂ X]
    (t : TopologicalSpace X) (h : @PolynormableSpace ℂ X _ _ _ t) : IsLocallyConvexTopology X t := by
  letI := t
  exact ⟨{p : Seminorm ℂ X // Continuous p},
    ⟨⟨0, continuous_const⟩⟩, fun p => p.1,
    PolynormableSpace.withSeminorms ℂ X⟩

private theorem proj_lc (A B : Type u) [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] :
    IsLocallyConvexTopology (A ⊗[ℂ] B) (projTensorTopology A B) := by
  apply lc_of_polynormable
  unfold projTensorTopology
  apply PolynormableSpace.sInf
  intro t ht
  exact polynormable_of_lc t ht.1

private theorem proj_tmul_continuous (A B : Type u) [AddCommGroup A] [Module ℂ A]
    [TopologicalSpace A] [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] :
    @Continuous (A × B) (A ⊗[ℂ] B) _ (projTensorTopology A B) (fun p => p.1 ⊗ₜ[ℂ] p.2) := by
  unfold projTensorTopology
  exact continuous_sInf_rng.2 fun t ht => ht.2

private theorem homog_bound {X : Type*} [AddCommGroup X] [Module ℂ X] (s : Seminorm ℂ X)
    (f : X → ℝ) (hf : ∀ (c : ℝ) (x : X), 0 < c → f ((c : ℂ) • x) = c * f x) (C : ℝ) (hC : 0 ≤ C)
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

private theorem exists_seminorm_ball_subset {X : Type u} [AddCommGroup X] [Module ℂ X]
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
private theorem continuous_seminorm_proj {A B : Type u} [AddCommGroup A] [Module ℂ A]
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

/-- A `π`-continuous seminorm is dominated on pure tensors by a product of continuous
seminorms. -/
private lemma bilinear_bound {A B : Type u} [AddCommGroup A] [Module ℂ A]
    [tA : TopologicalSpace A] [AddCommGroup B] [Module ℂ B] [tB : TopologicalSpace B]
    (hA : IsLocallyConvexTopology A tA) (hB : IsLocallyConvexTopology B tB)
    (r : Seminorm ℂ (A ⊗[ℂ] B)) (hr : @Continuous _ _ (projTensorTopology A B) _ r) :
    ∃ (p : Seminorm ℂ A) (s : Seminorm ℂ B), Continuous p ∧ Continuous s ∧
      ∀ a b, r (a ⊗ₜ[ℂ] b) ≤ p a * s b := by
  have hcomp : Continuous (fun w : A × B => r (w.1 ⊗ₜ[ℂ] w.2)) := by
    letI := projTensorTopology A B
    exact hr.comp (proj_tmul_continuous A B)
  have hmem : {w : A × B | r (w.1 ⊗ₜ[ℂ] w.2) < 1} ∈ 𝓝 ((0, 0) : A × B) :=
    (isOpen_lt hcomp continuous_const).mem_nhds (by simp)
  rw [nhds_prod_eq] at hmem
  obtain ⟨U, hU, V, hV, hsub⟩ := Filter.mem_prod_iff.1 hmem
  obtain ⟨p, hpc, hp⟩ := exists_seminorm_ball_subset hA hU
  obtain ⟨s, hsc, hs⟩ := exists_seminorm_ball_subset hB hV
  have hball : ∀ a b, p a < 1 → s b < 1 → r (a ⊗ₜ[ℂ] b) < 1 := fun a b ha hb =>
    hsub (Set.mk_mem_prod (hp a ha) (hs b hb))
  have step1 : ∀ a b, s b < 1 → r (a ⊗ₜ[ℂ] b) ≤ p a := by
    intro a b hb
    have := homog_bound p (fun a => r (a ⊗ₜ[ℂ] b)) (fun k a hk => by
      change r (((k : ℂ) • a) ⊗ₜ[ℂ] b) = k * r (a ⊗ₜ[ℂ] b)
      rw [← TensorProduct.smul_tmul', map_smul_eq_mul, Complex.norm_real,
        Real.norm_of_nonneg hk.le]) 1 zero_le_one
      (fun a ha => (hball a b ha hb).le) a
    simpa using this
  refine ⟨p, s, hpc, hsc, fun a b => ?_⟩
  exact homog_bound s (fun b => r (a ⊗ₜ[ℂ] b)) (fun k b hk => by
      change r (a ⊗ₜ[ℂ] ((k : ℂ) • b)) = k * r (a ⊗ₜ[ℂ] b)
      rw [TensorProduct.tmul_smul, map_smul_eq_mul, Complex.norm_real,
        Real.norm_of_nonneg hk.le])
    (p a) (apply_nonneg p a) (fun b hb => step1 a b hb) b

/-- Functionals dominated by one continuous seminorm form an equicontinuous set. -/
private lemma equicont_of_bound {X : Type u} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] (q : Seminorm ℂ X) (hq : Continuous q) (A : Set (StrongDual ℂ X))
    (hA : ∀ a ∈ A, ∀ x, ‖a x‖ ≤ q x) : Equicontinuous (fun a : A => (a : X → ℂ)) := by
  intro x₀
  refine Metric.equicontinuousAt_iff_right.2 fun ε hε => ?_
  have h0 : q (x₀ - x₀) < ε := by simpa using hε
  filter_upwards [(hq.comp (continuous_id.sub continuous_const)).continuousAt.eventually
    (gt_mem_nhds h0)] with x hx
  rintro ⟨a, ha⟩
  rw [dist_eq_norm, ← map_sub]
  calc ‖a (x₀ - x)‖ ≤ q (x₀ - x) := hA a ha _
    _ = q (x - x₀) := by rw [← map_neg_eq_map, neg_sub]
    _ < ε := hx

/-- An equicontinuous set of functionals on a locally convex space is dominated by one
continuous seminorm. -/
private lemma bound_of_equicont {X : Type u} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (hX : IsLocallyConvexTopology X ‹_›) (A : Set (StrongDual ℂ X))
    (hA : Equicontinuous (fun a : A => (a : X → ℂ))) :
    ∃ q : Seminorm ℂ X, Continuous q ∧ ∀ a ∈ A, ∀ x, ‖a x‖ ≤ q x := by
  have hU : {x : X | ∀ a ∈ A, ‖a x‖ < 1} ∈ 𝓝 (0 : X) := by
    filter_upwards [Metric.equicontinuousAt_iff_right.1 (hA 0) 1 one_pos] with x hx a ha
    simpa [dist_eq_norm] using hx ⟨a, ha⟩
  obtain ⟨q, hq, hsub⟩ := exists_seminorm_ball_subset hX hU
  refine ⟨q, hq, fun a ha x => ?_⟩
  have := homog_bound q (fun x => ‖a x‖) (fun k x hk => by
    rw [map_smul, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk.le])
    1 zero_le_one (fun x hx => (hsub x hx a ha).le) x
  simpa using this

/-- Hahn–Banach: a continuous seminorm is attained by a functional in its polar. -/
private lemma hb_exists {Y : Type u} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [PolynormableSpace ℂ Y] (s : Seminorm ℂ Y) (hs : Continuous s) (w : Y) :
    ∃ b : StrongDual ℂ Y, (∀ z, ‖b z‖ ≤ s z) ∧ ‖b w‖ = s w := by
  have H : ∀ c : ℂ, c • w = 0 → (RingHom.id ℂ) c • ((s w : ℝ) : ℂ) = 0 := by
    intro c hc
    rcases eq_or_ne c 0 with rfl | hc0
    · simp
    · have : w = 0 := by simpa [hc0] using hc
      simp [this]
  let f := LinearPMap.mkSpanSingleton' w ((s w : ℝ) : ℂ) H
  obtain ⟨g, hg, hle⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm f.domain
    f.toFun hs (by
      rintro ⟨x, hx⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      change ‖f ⟨c • w, hx⟩‖ ≤ s (c • w)
      rw [LinearPMap.mkSpanSingleton'_apply, map_smul_eq_mul, RingHom.id_apply, smul_eq_mul,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg s w)])
  refine ⟨g, hle, ?_⟩
  have hw : w ∈ f.domain := Submodule.mem_span_singleton_self w
  have := hg ⟨w, hw⟩
  change g w = f ⟨w, hw⟩ at this
  rw [this, LinearPMap.mkSpanSingleton'_apply_self, Complex.norm_real,
    Real.norm_of_nonneg (apply_nonneg s w)]

/-! ### The injective topology -/

section eps

variable (X Y : Type u) [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]

private def eqS : Set (Set (StrongDual ℂ X × StrongDual ℂ Y)) :=
  {S | ∃ (A : Set (StrongDual ℂ X)) (B : Set (StrongDual ℂ Y)),
    Equicontinuous (fun a : A => (a : X → ℂ)) ∧ Equicontinuous (fun b : B => (b : Y → ℂ)) ∧
      S = A ×ˢ B}

private lemma eps_eq :
    epsTensorTopology X Y = TopologicalSpace.induced
      (fun u : X ⊗[ℂ] Y => UniformOnFun.ofFun (eqS X Y) (fun ab => tensorFunctional X Y ab u))
      inferInstance := rfl

private lemma tf_add (ab : StrongDual ℂ X × StrongDual ℂ Y) (u v : X ⊗[ℂ] Y) :
    tensorFunctional X Y ab (u + v) = tensorFunctional X Y ab u + tensorFunctional X Y ab v := by
  simp [tensorFunctional]

private lemma tf_zero (ab : StrongDual ℂ X × StrongDual ℂ Y) :
    tensorFunctional X Y ab 0 = 0 := by
  simp [tensorFunctional]

private lemma tf_tmul (a : StrongDual ℂ X) (b : StrongDual ℂ Y) (x : X) (y : Y) :
    tensorFunctional X Y (a, b) (x ⊗ₜ[ℂ] y) = a x * b y := by
  simp [tensorFunctional]

private lemma tf_contrL (a : StrongDual ℂ X) (ψ : StrongDual ℂ Y) (w : X ⊗[ℂ] Y) :
    tensorFunctional X Y (a, ψ) w =
      ψ (TensorProduct.lid ℂ Y (TensorProduct.map (a : X →ₗ[ℂ] ℂ) LinearMap.id w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp [tensorFunctional]
  | tmul x y => simp [tensorFunctional]
  | add x y hx hy => rw [tf_add, hx, hy]; simp

/-- The additive map `u ↦ ((a, b) ↦ (a ⊗ b)(u))` defining the injective topology. -/
private def epsJ : X ⊗[ℂ] Y →+ UniformOnFun (StrongDual ℂ X × StrongDual ℂ Y) ℂ (eqS X Y) where
  toFun u := UniformOnFun.ofFun (eqS X Y) (fun ab => tensorFunctional X Y ab u)
  map_zero' := by
    funext ab
    simp [tensorFunctional]
    rfl
  map_add' := by
    intro u v
    funext ab
    simp [tensorFunctional]
    rfl

private lemma eps_group : @IsTopologicalAddGroup _ (epsTensorTopology X Y) _ := by
  rw [eps_eq]
  exact topologicalAddGroup_induced (epsJ X Y)

private lemma equicont_union' {Z : Type*} [TopologicalSpace Z] [AddCommGroup Z] [Module ℂ Z]
    {A A' : Set (StrongDual ℂ Z)}
    (hA : Equicontinuous (fun a : A => (a : Z → ℂ)))
    (hA' : Equicontinuous (fun a : A' => (a : Z → ℂ))) :
    Equicontinuous (fun a : (A ∪ A' : Set (StrongDual ℂ Z)) => (a : Z → ℂ)) := by
  intro x₀
  refine Metric.equicontinuousAt_iff_right.2 fun ε hε => ?_
  filter_upwards [Metric.equicontinuousAt_iff_right.1 (hA x₀) ε hε,
    Metric.equicontinuousAt_iff_right.1 (hA' x₀) ε hε] with x h1 h2
  rintro ⟨a, ha | ha⟩
  · exact h1 ⟨a, ha⟩
  · exact h2 ⟨a, ha⟩

private lemma eqS_nonempty : (eqS X Y).Nonempty := by
  refine ⟨∅ ×ˢ ∅, ∅, ∅, ?_, ?_, rfl⟩
  · intro x₀; exact Metric.equicontinuousAt_iff_right.2 fun ε hε => by
      filter_upwards with x; rintro ⟨a, ha⟩; exact ha.elim
  · intro x₀; exact Metric.equicontinuousAt_iff_right.2 fun ε hε => by
      filter_upwards with x; rintro ⟨a, ha⟩; exact ha.elim

private lemma eqS_directed : DirectedOn (· ⊆ ·) (eqS X Y) := by
  rintro _ ⟨A, B, hA, hB, rfl⟩ _ ⟨A', B', hA', hB', rfl⟩
  exact ⟨(A ∪ A') ×ˢ (B ∪ B'), ⟨_, _, equicont_union' hA hA', equicont_union' hB hB', rfl⟩,
    Set.prod_mono Set.subset_union_left Set.subset_union_left,
    Set.prod_mono Set.subset_union_right Set.subset_union_right⟩

private lemma eps_nhds_zero {U : Set (X ⊗[ℂ] Y)} (hU : U ∈ @nhds _ (epsTensorTopology X Y) 0) :
    ∃ (A : Set (StrongDual ℂ X)) (B : Set (StrongDual ℂ Y)),
      Equicontinuous (fun a : A => (a : X → ℂ)) ∧ Equicontinuous (fun b : B => (b : Y → ℂ)) ∧
      ∃ r > (0 : ℝ), ∀ x, (∀ a ∈ A, ∀ b ∈ B, ‖tensorFunctional X Y (a, b) x‖ < r) → x ∈ U := by
  rw [eps_eq, nhds_induced] at hU
  obtain ⟨⟨S, r⟩, ⟨⟨A, B, hA, hB, rfl⟩, hr⟩, hsub⟩ :=
    ((UniformOnFun.hasBasis_nhds_of_basis _ _ _ _ (eqS_nonempty X Y) (eqS_directed X Y)
      Metric.uniformity_basis_dist).comap _).mem_iff.1 hU
  refine ⟨A, B, hA, hB, r, hr, fun x hx => hsub ?_⟩
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  simpa [tf_zero, dist_eq_norm] using hx a ha b hb

private lemma eps_eventually {S : Set (StrongDual ℂ X × StrongDual ℂ Y)} (hS : S ∈ eqS X Y)
    (x₀ : X ⊗[ℂ] Y) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in @nhds _ (epsTensorTopology X Y) x₀,
      ∀ i ∈ S, dist (tensorFunctional X Y i x₀) (tensorFunctional X Y i x) < ε := by
  let _ : TopologicalSpace (X ⊗[ℂ] Y) := epsTensorTopology X Y
  have hc : Continuous (fun u : X ⊗[ℂ] Y =>
      UniformOnFun.ofFun (eqS X Y) (fun ab => tensorFunctional X Y ab u)) :=
    continuous_induced_dom
  have := UniformOnFun.tendsto_iff_tendstoUniformlyOn.1 (hc.tendsto x₀) S hS
  exact Metric.tendstoUniformlyOn_iff.1 this ε hε

end eps

/-- Comparison of two additive group topologies through neighbourhoods of `0`. -/
private lemma le_of_nhds_zero {T : Type*} [AddCommGroup T] (t₁ t₂ : TopologicalSpace T)
    (h₁ : @IsTopologicalAddGroup T t₁ _) (h₂ : @IsTopologicalAddGroup T t₂ _)
    (h : ∀ U, U ∈ @nhds T t₂ 0 → U ∈ @nhds T t₁ 0) : t₁ ≤ t₂ := by
  rw [← continuous_id_iff_le]
  have := @continuous_of_continuousAt_zero T t₁ _ h₁ T (T →+ T) _ t₂
    (@IsTopologicalAddGroup.toContinuousAdd T t₂ _ h₂) _ _ (AddMonoidHom.id T) (fun U hU => h U hU)
  exact this

/-! ### `π` is finer than `ε` -/

/-- The `ε`-seminorm of a pair of equicontinuous sets is `π`-continuous. -/
private lemma eps_sup_continuous {X Y : Type u} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup X] [IsTopologicalAddGroup Y]
    (A : Set (StrongDual ℂ X)) (B : Set (StrongDual ℂ Y)) (p : Seminorm ℂ X) (s : Seminorm ℂ Y)
    (hp : Continuous p) (hs : Continuous s) (hA : ∀ a ∈ A, ∀ x, ‖a x‖ ≤ p x)
    (hB : ∀ b ∈ B, ∀ y, ‖b y‖ ≤ s y) :
    ∃ N : Seminorm ℂ (X ⊗[ℂ] Y), @Continuous _ _ (projTensorTopology X Y) _ N ∧
      ∀ a ∈ A, ∀ b ∈ B, ∀ u, ‖tensorFunctional X Y (a, b) u‖ ≤ N u := by
  let ι := {ab : StrongDual ℂ X × StrongDual ℂ Y // ab.1 ∈ A ∧ ab.2 ∈ B}
  let L : ι → X ⊗[ℂ] Y →ₗ[ℂ] ℂ := fun i =>
    (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
      TensorProduct.map (i.1.1 : X →ₗ[ℂ] ℂ) (i.1.2 : Y →ₗ[ℂ] ℂ)
  have hL : ∀ i u, L i u = tensorFunctional X Y i.1 u := fun i u => rfl
  let fam : ι → Seminorm ℂ (X ⊗[ℂ] Y) := fun i => (normSeminorm ℂ ℂ).comp (L i)
  have hfam : ∀ i u, fam i u = ‖tensorFunctional X Y i.1 u‖ := fun i u => rfl
  have htm : ∀ (i : ι) x y, ‖tensorFunctional X Y i.1 (x ⊗ₜ[ℂ] y)‖ ≤ p x * s y := by
    rintro ⟨⟨a, b⟩, ha, hb⟩ x y
    rw [tf_tmul, norm_mul]
    exact mul_le_mul (hA a ha x) (hB b hb y) (norm_nonneg _) (apply_nonneg p x)
  have hbddpt : ∀ u : X ⊗[ℂ] Y, ∃ K : ℝ, ∀ i : ι, fam i u ≤ K := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, fun i => by simp⟩
    | tmul x y => exact ⟨p x * s y, fun i => by rw [hfam]; exact htm i x y⟩
    | add v w hv hw =>
      obtain ⟨K1, h1⟩ := hv
      obtain ⟨K2, h2⟩ := hw
      exact ⟨K1 + K2, fun i => (map_add_le_add (fam i) _ _).trans (add_le_add (h1 i) (h2 i))⟩
  have hbdd : BddAbove (Set.range fam) := by
    rw [Seminorm.bddAbove_range_iff]
    intro u
    obtain ⟨K, hK⟩ := hbddpt u
    exact ⟨K, by rintro _ ⟨i, rfl⟩; exact hK i⟩
  let N : Seminorm ℂ (X ⊗[ℂ] Y) := ⨆ i, fam i
  have hNapp : ∀ u, N u = ⨆ i, fam i u := fun u => Seminorm.iSup_apply hbdd
  refine ⟨N, continuous_seminorm_proj N p s hp hs fun x y => ?_, fun a ha b hb u => ?_⟩
  · rw [hNapp]
    exact Real.iSup_le (fun i => by rw [hfam]; exact htm i x y)
      (mul_nonneg (apply_nonneg p x) (apply_nonneg s y))
  · rw [hNapp]
    exact le_ciSup (f := fun i : ι => fam i u) (Seminorm.bddAbove_range_iff.1 hbdd u)
      ⟨(a, b), ha, hb⟩

private lemma proj_le_eps (X Y : Type u) [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (hX : IsLocallyConvexTopology X ‹_›) (hY : IsLocallyConvexTopology Y ‹_›) :
    projTensorTopology X Y ≤ epsTensorTopology X Y := by
  haveI := addGroup_of_lc _ hX
  haveI := addGroup_of_lc _ hY
  refine le_of_nhds_zero _ _ (addGroup_of_lc _ (proj_lc X Y)) (eps_group X Y) fun U hU => ?_
  obtain ⟨A, B, hA, hB, ρ, hρ, hsub⟩ := eps_nhds_zero X Y hU
  obtain ⟨p, hp, hpA⟩ := bound_of_equicont hX A hA
  obtain ⟨s, hs, hsB⟩ := bound_of_equicont hY B hB
  obtain ⟨N, hN, hNb⟩ := eps_sup_continuous A B p s hp hs hpA hsB
  letI : TopologicalSpace (X ⊗[ℂ] Y) := projTensorTopology X Y
  have h0 : N 0 < ρ := by simpa using hρ
  filter_upwards [hN.continuousAt.eventually (gt_mem_nhds h0)] with u hu
  exact hsub u fun a ha b hb => (hNb a ha b hb u).trans_lt hu

/-! ### `ε` is finer than `π` under a nuclear expansion -/

/-- The key estimate: a nuclear expansion of the first factor dominates a `π`-type seminorm by an
`ε`-type quantity. -/
private lemma main_est {X Y : Type u} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y]
    (r : Seminorm ℂ (X ⊗[ℂ] Y)) (p : Seminorm ℂ X) (s : Seminorm ℂ Y) (hs : Continuous s)
    (hr : ∀ a b, r (a ⊗ₜ[ℂ] b) ≤ p a * s b)
    (h : ℕ → StrongDual ℂ X) (y : ℕ → X) (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hcs : Summable c)
    (hy : ∀ n, p (y n) ≤ 1)
    (hexp : ∀ x, Tendsto (fun N => p (x - ∑ n ∈ Finset.range N, ((c n : ℂ) * h n x) • y n))
      atTop (𝓝 0))
    (δ : ℝ) (u : X ⊗[ℂ] Y)
    (hu : ∀ n, ∀ b : StrongDual ℂ Y, (∀ z, ‖b z‖ ≤ s z) →
      ‖tensorFunctional X Y (h n, b) u‖ ≤ δ) :
    r u ≤ (∑' n, c n) * δ := by
  let P : ℕ → X →ₗ[ℂ] X := fun N =>
    ∑ n ∈ Finset.range N, (c n : ℂ) • (h n : X →ₗ[ℂ] ℂ).smulRight (y n)
  have hP : ∀ N x, P N x = ∑ n ∈ Finset.range N, ((c n : ℂ) * h n x) • y n := by
    intro N x
    simp [P, LinearMap.sum_apply, mul_smul]
  let w : ℕ → X ⊗[ℂ] Y → Y := fun n v =>
    TensorProduct.lid ℂ Y (TensorProduct.map (h n : X →ₗ[ℂ] ℂ) LinearMap.id v)
  have hmap : ∀ N (v : X ⊗[ℂ] Y), TensorProduct.map (P N) LinearMap.id v =
      ∑ n ∈ Finset.range N, (c n : ℂ) • (y n ⊗ₜ[ℂ] w n v) := by
    intro N v
    induction v using TensorProduct.induction_on with
    | zero => simp [w]
    | tmul x z =>
      rw [TensorProduct.map_tmul, hP, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp [w, mul_smul, TensorProduct.smul_tmul', TensorProduct.tmul_smul, ← TensorProduct.smul_tmul]
    | add v₁ v₂ h₁ h₂ =>
      rw [map_add, h₁, h₂, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp [w, TensorProduct.tmul_add, smul_add]
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hu 0 0 (fun z => by simp))
  have hws : ∀ n, s (w n u) ≤ δ := by
    intro n
    obtain ⟨b, hb, hbw⟩ := hb_exists s hs (w n u)
    rw [← hbw]
    have := hu n b hb
    rwa [tf_contrL] at this
  have hmain : ∀ N, r (TensorProduct.map (P N) LinearMap.id u) ≤ (∑' n, c n) * δ := by
    intro N
    rw [hmap]
    refine (Finset.le_sum_of_subadditive r (map_zero r).le (map_add_le_add r) _ _).trans ?_
    calc ∑ n ∈ Finset.range N, r ((c n : ℂ) • (y n ⊗ₜ[ℂ] w n u))
        ≤ ∑ n ∈ Finset.range N, c n * δ := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg (hc0 n)]
          refine mul_le_mul_of_nonneg_left ?_ (hc0 n)
          calc r (y n ⊗ₜ[ℂ] w n u) ≤ p (y n) * s (w n u) := hr _ _
            _ ≤ 1 * δ := mul_le_mul (hy n) (hws n) (apply_nonneg s _) zero_le_one
            _ = δ := one_mul δ
      _ = (∑ n ∈ Finset.range N, c n) * δ := by rw [Finset.sum_mul]
      _ ≤ (∑' n, c n) * δ :=
          mul_le_mul_of_nonneg_right (hcs.sum_le_tsum _ (fun n _ => hc0 n)) hδ
  have hrem : ∀ v : X ⊗[ℂ] Y,
      Tendsto (fun N => r (v - TensorProduct.map (P N) LinearMap.id v)) atTop (𝓝 0) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x z =>
      have ht : Tendsto (fun N => p (x - P N x) * s z) atTop (𝓝 0) := by
        have := (hexp x).mul_const (s z)
        simpa [hP] using this
      refine squeeze_zero (fun N => apply_nonneg r _) (fun N => ?_) ht
      rw [TensorProduct.map_tmul, LinearMap.id_apply, ← TensorProduct.sub_tmul]
      exact hr _ _
    | add v₁ v₂ h₁ h₂ =>
      refine squeeze_zero (fun N => apply_nonneg r _) (fun N => ?_) (by simpa using h₁.add h₂)
      have : v₁ + v₂ - TensorProduct.map (P N) LinearMap.id (v₁ + v₂) =
          (v₁ - TensorProduct.map (P N) LinearMap.id v₁) +
            (v₂ - TensorProduct.map (P N) LinearMap.id v₂) := by
        rw [map_add]; abel
      rw [this]
      exact map_add_le_add r _ _
  have key : ∀ N, r u - (∑' n, c n) * δ ≤ r (u - TensorProduct.map (P N) LinearMap.id u) := by
    intro N
    have h1 : r u ≤ r (TensorProduct.map (P N) LinearMap.id u) +
        r (u - TensorProduct.map (P N) LinearMap.id u) := by
      calc r u = r (TensorProduct.map (P N) LinearMap.id u +
            (u - TensorProduct.map (P N) LinearMap.id u)) := by congr 1; abel
        _ ≤ _ := map_add_le_add r _ _
    linarith [hmain N]
  have : r u - (∑' n, c n) * δ ≤ 0 := ge_of_tendsto (hrem u) (Filter.Eventually.of_forall key)
  linarith

private lemma eps_le_proj (X Y : Type u) [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (hX : IsLocallyConvexTopology X ‹_›) (hY : IsLocallyConvexTopology Y ‹_›)
    (hexp : ∀ p : Seminorm ℂ X, Continuous p →
      ∃ (q : Seminorm ℂ X) (h : ℕ → StrongDual ℂ X) (y : ℕ → X) (c : ℕ → ℝ),
        Continuous q ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖h n x‖ ≤ q x) ∧
        (∀ n, p (y n) ≤ 1) ∧
        ∀ x, Tendsto (fun N => p (x - ∑ n ∈ Finset.range N, ((c n : ℂ) * h n x) • y n))
          atTop (𝓝 0)) :
    epsTensorTopology X Y ≤ projTensorTopology X Y := by
  haveI := polynormable_of_lc _ hY
  haveI := addGroup_of_lc _ hX
  haveI := addGroup_of_lc _ hY
  refine le_of_nhds_zero _ _ (eps_group X Y) (addGroup_of_lc _ (proj_lc X Y)) fun U hU => ?_
  obtain ⟨r, hr, hrU⟩ := @exists_seminorm_ball_subset _ _ _ (projTensorTopology X Y)
    (proj_lc X Y) U hU
  obtain ⟨p, s, hp, hs, hps⟩ := bilinear_bound hX hY r hr
  obtain ⟨q, h, y, c, hq, hc0, hcs, hh, hy, hx⟩ := hexp p hp
  set C := ∑' n, c n
  have hC : 0 ≤ C := tsum_nonneg hc0
  set δ : ℝ := 1 / (2 * (C + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  let A : Set (StrongDual ℂ X) := Set.range h
  let B : Set (StrongDual ℂ Y) := {b | ∀ z, ‖b z‖ ≤ s z}
  have hS : A ×ˢ B ∈ eqS X Y :=
    ⟨A, B, equicont_of_bound q hq A (by rintro _ ⟨n, rfl⟩; exact hh n),
      equicont_of_bound s hs B (fun b hb => hb), rfl⟩
  filter_upwards [eps_eventually X Y hS 0 hδ] with u hu
  apply hrU
  have hest := main_est r p s hs hps h y c hc0 hcs hy hx δ u (fun n b hb => by
    have := hu (h n, b) ⟨⟨n, rfl⟩, hb⟩
    rw [tf_zero, dist_eq_norm, zero_sub, norm_neg] at this
    exact this.le)
  calc r u ≤ C * δ := hest
    _ < 1 := by
      rw [hδdef, mul_one_div, div_lt_one (by positivity)]
      linarith

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E)
    (hdom : ∀ p : Seminorm ℂ E, Continuous p →
      ∃ (q : Seminorm ℂ E) (f : ℕ → StrongDual ℂ E) (c : ℕ → ℝ),
        Continuous q ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖f n x‖ ≤ q x) ∧
        ∀ x, p x ≤ ∑' n, c n * ‖f n x‖) :
    IsNuclear E := by
  refine ⟨hE, fun F _ _ _ hF => le_antisymm (proj_le_eps E F hE.1 hF.1)
    (eps_le_proj E F hE.1 hF.1 fun p hp => ?_)⟩
  obtain ⟨r, f, a, hr, ha, has, hf, hpr⟩ := hdom p hp
  obtain ⟨s, g, b, hs, hb, hbs, hg, hrs⟩ := hdom r hr
  obtain ⟨h, y, c, hc0, hcs, hh, hy, hexp⟩ :=
    quasinuclear_comp_nuclear_expansion E p r s f a ha has hf hpr g b hb hbs hg hrs
  exact ⟨s, h, y, c, hs, hc0, hcs, hh, hy, hexp⟩
