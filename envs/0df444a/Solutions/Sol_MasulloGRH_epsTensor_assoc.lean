-- Prove2me | solution 1 for MasulloGRH.epsTensor_assoc
-- status  : ACCEPTED   (prove)
-- author  : @ijawdoij123
-- created : 2026-11-20T23:16:58.525643+00:00
-- url     : https://prove2.me/submissions/9aa88540-000f-4c0d-b554-0cbcd49ad7c8

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH
open TensorProduct Topology Filter

universe u

private lemma dom_le {T I J : Type*} [AddCommGroup T] {𝔖 : Set (Set I)} {𝔗 : Set (Set J)}
    (f : T → I → ℂ) (g : T → J → ℂ)
    (hf : ∀ u v i, f (u - v) i = f u i - f v i) (hg : ∀ u v j, g (u - v) j = g u j - g v j)
    (h : ∀ S' ∈ 𝔗, ∃ S ∈ 𝔖, ∀ ρ > 0, ∃ δ > 0, ∀ u,
      (∀ i ∈ S, ‖f u i‖ < δ) → ∀ j ∈ S', ‖g u j‖ < ρ) :
    TopologicalSpace.induced (fun u => UniformOnFun.ofFun 𝔖 (f u)) inferInstance ≤
    TopologicalSpace.induced (fun u => UniformOnFun.ofFun 𝔗 (g u)) inferInstance := by
  let _ : TopologicalSpace T :=
    TopologicalSpace.induced (fun u => UniformOnFun.ofFun 𝔖 (f u)) inferInstance
  rw [← continuous_iff_le_induced, continuous_iff_continuousAt]
  intro u
  have hc : Continuous (fun u => UniformOnFun.ofFun 𝔖 (f u)) := continuous_induced_dom
  have hu := UniformOnFun.tendsto_iff_tendstoUniformlyOn.1 (hc.tendsto u)
  refine UniformOnFun.tendsto_iff_tendstoUniformlyOn.2 fun S' hS' => ?_
  obtain ⟨S, hS, hd⟩ := h S' hS'
  have hS := Metric.tendstoUniformlyOn_iff.1 (hu S hS)
  refine Metric.tendstoUniformlyOn_iff.2 fun ρ hρ => ?_
  obtain ⟨δ, hδ, hdd⟩ := hd ρ hρ
  filter_upwards [hS δ hδ] with v hv j hj
  have h1 : ∀ i ∈ S, ‖f (u - v) i‖ < δ := fun i hi => by
    have := hv i hi
    rw [dist_eq_norm] at this
    simpa [hf] using this
  have := hdd (u - v) h1 j hj
  rw [dist_eq_norm]
  simpa [hg] using this

section generic

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

private lemma tf_sub (ab : StrongDual ℂ X × StrongDual ℂ Y) (u v : X ⊗[ℂ] Y) :
    tensorFunctional X Y ab (u - v) = tensorFunctional X Y ab u - tensorFunctional X Y ab v := by
  simp [tensorFunctional]

private lemma tf_add (ab : StrongDual ℂ X × StrongDual ℂ Y) (u v : X ⊗[ℂ] Y) :
    tensorFunctional X Y ab (u + v) = tensorFunctional X Y ab u + tensorFunctional X Y ab v := by
  simp [tensorFunctional]

private lemma tf_smul (ab : StrongDual ℂ X × StrongDual ℂ Y) (c : ℂ) (u : X ⊗[ℂ] Y) :
    tensorFunctional X Y ab (c • u) = c * tensorFunctional X Y ab u := by
  simp [tensorFunctional]

private lemma tf_zero (ab : StrongDual ℂ X × StrongDual ℂ Y) :
    tensorFunctional X Y ab 0 = 0 := by
  simp [tensorFunctional]

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


private lemma singleton_eqc {Z : Type u} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (a : StrongDual ℂ Z) : Equicontinuous (fun x : ({a} : Set (StrongDual ℂ Z)) => (x : Z → ℂ)) := by
  intro x₀
  refine Metric.equicontinuousAt_iff_right.2 fun ε hε => ?_
  filter_upwards [Metric.tendsto_nhds.1 (a.continuous.tendsto x₀) ε hε] with x hx
  rintro ⟨a', ha'⟩
  rw [Set.mem_singleton_iff] at ha'
  subst ha'
  rw [dist_comm]
  exact hx

private lemma tf_continuous [t : TopologicalSpace (X ⊗[ℂ] Y)] (hT : t = epsTensorTopology X Y)
    (a : StrongDual ℂ X) (b : StrongDual ℂ Y) : Continuous (tensorFunctional X Y (a, b)) := by
  subst hT
  let _ : TopologicalSpace (X ⊗[ℂ] Y) := epsTensorTopology X Y
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [eps_eventually X Y ⟨{a}, {b}, singleton_eqc a, singleton_eqc b, rfl⟩ x₀ hε]
    with x hx
  rw [dist_comm]
  exact hx (a, b) ⟨rfl, rfl⟩

private def tfCLM [t : TopologicalSpace (X ⊗[ℂ] Y)] (hT : t = epsTensorTopology X Y)
    (a : StrongDual ℂ X) (b : StrongDual ℂ Y) : StrongDual ℂ (X ⊗[ℂ] Y) :=
  ⟨(TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ TensorProduct.map (a : X →ₗ[ℂ] ℂ) (b : Y →ₗ[ℂ] ℂ),
    tf_continuous X Y hT a b⟩

private lemma tfCLM_apply [t : TopologicalSpace (X ⊗[ℂ] Y)] (hT : t = epsTensorTopology X Y)
    (a : StrongDual ℂ X) (b : StrongDual ℂ Y) (u : X ⊗[ℂ] Y) :
    tfCLM X Y hT a b u = tensorFunctional X Y (a, b) u := rfl

private lemma tfCLM_equicont [t : TopologicalSpace (X ⊗[ℂ] Y)] (hT : t = epsTensorTopology X Y)
    {A : Set (StrongDual ℂ X)} {B : Set (StrongDual ℂ Y)}
    (hA : Equicontinuous (fun a : A => (a : X → ℂ)))
    (hB : Equicontinuous (fun b : B => (b : Y → ℂ))) :
    Equicontinuous (fun φ : ((fun ab : StrongDual ℂ X × StrongDual ℂ Y => tfCLM X Y hT ab.1 ab.2) ''
      (A ×ˢ B)) => (φ : X ⊗[ℂ] Y → ℂ)) := by
  intro x₀
  refine Metric.equicontinuousAt_iff_right.2 fun ε hε => ?_
  have := eps_eventually X Y ⟨A, B, hA, hB, rfl⟩ x₀ hε
  subst hT
  filter_upwards [this] with x hx
  rintro ⟨_, ab, hab, rfl⟩
  exact hx ab hab

private lemma tf_contrR (φ : StrongDual ℂ X) (c : StrongDual ℂ Y) (w : X ⊗[ℂ] Y) :
    tensorFunctional X Y (φ, c) w =
      φ (TensorProduct.rid ℂ X (TensorProduct.map LinearMap.id (c : Y →ₗ[ℂ] ℂ) w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp [tensorFunctional]
  | tmul x y => simp [tensorFunctional, mul_comm]
  | add x y hx hy => rw [tf_add, hx, hy]; simp

private lemma tf_contrL (a : StrongDual ℂ X) (ψ : StrongDual ℂ Y) (w : X ⊗[ℂ] Y) :
    tensorFunctional X Y (a, ψ) w =
      ψ (TensorProduct.lid ℂ Y (TensorProduct.map (a : X →ₗ[ℂ] ℂ) LinearMap.id w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp [tensorFunctional]
  | tmul x y => simp [tensorFunctional]
  | add x y hx hy => rw [tf_add, hx, hy]; simp

end generic

private lemma tf_assoc (E F G : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (a : StrongDual ℂ E) (b : StrongDual ℂ F) (c : StrongDual ℂ G) (w : (E ⊗[ℂ] F) ⊗[ℂ] G) :
    tensorFunctional F G (b, c) (TensorProduct.lid ℂ (F ⊗[ℂ] G)
        (TensorProduct.map (a : E →ₗ[ℂ] ℂ) LinearMap.id (TensorProduct.assoc ℂ E F G w))) =
      tensorFunctional E F (a, b) (TensorProduct.rid ℂ (E ⊗[ℂ] F)
        (TensorProduct.map LinearMap.id (c : G →ₗ[ℂ] ℂ) w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp [tensorFunctional]
  | tmul t z =>
    induction t using TensorProduct.induction_on with
    | zero => simp [tensorFunctional]
    | tmul x y => simp [tensorFunctional]; ring
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, tf_add] at hx hy ⊢; rw [hx, hy]
  | add x y hx hy => simp only [map_add, tf_add] at hx hy ⊢; rw [hx, hy]

private lemma scale_lt {Z : Type u} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (φ : StrongDual ℂ Z) (x : Z) {ρ : ℝ} (hρ : 0 < ρ)
    (h : dist (φ 0) (φ ((ρ : ℂ)⁻¹ • x)) < 1) : ‖φ x‖ < ρ := by
  rw [map_zero, map_smul, dist_zero_left, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hρ.le] at h
  rwa [inv_mul_lt_iff₀ hρ, mul_one] at h

private lemma scale_lt' (y : ℂ) {r ρ : ℝ} (hρ : 0 < ρ) (h : ‖y‖ < r * ρ) :
    ‖(ρ : ℂ)⁻¹ * y‖ < r := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ.le, inv_mul_lt_iff₀ hρ,
    mul_comm]
  exact h

private def tripS (E F G : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] :
    Set (Set (StrongDual ℂ E × StrongDual ℂ F × StrongDual ℂ G)) :=
  {S | ∃ (A : Set (StrongDual ℂ E)) (B : Set (StrongDual ℂ F)) (C : Set (StrongDual ℂ G)),
    Equicontinuous (fun a : A => (a : E → ℂ)) ∧ Equicontinuous (fun b : B => (b : F → ℂ)) ∧
      Equicontinuous (fun c : C => (c : G → ℂ)) ∧ S = A ×ˢ B ×ˢ C}

private def f3 (E F G : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] (w : (E ⊗[ℂ] F) ⊗[ℂ] G)
    (abc : StrongDual ℂ E × StrongDual ℂ F × StrongDual ℂ G) : ℂ :=
  tensorFunctional E F (abc.1, abc.2.1)
    (TensorProduct.rid ℂ (E ⊗[ℂ] F) (TensorProduct.map LinearMap.id (abc.2.2 : G →ₗ[ℂ] ℂ) w))

theorem solution (E F G : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (hE : IsHLCS E) (hF : IsHLCS F) (hG : IsHLCS G) :
    @epsTensorTopology (E ⊗[ℂ] F) _ _ (epsTensorTopology E F) G _ _ _ =
      TopologicalSpace.induced (TensorProduct.assoc ℂ E F G)
        (@epsTensorTopology E _ _ _ (F ⊗[ℂ] G) _ _ (epsTensorTopology F G)) := by
  let tEF : TopologicalSpace (E ⊗[ℂ] F) := epsTensorTopology E F
  let tFG : TopologicalSpace (F ⊗[ℂ] G) := epsTensorTopology F G
  have hR : TopologicalSpace.induced (TensorProduct.assoc ℂ E F G)
      (epsTensorTopology E (F ⊗[ℂ] G)) = TopologicalSpace.induced
      (fun w : (E ⊗[ℂ] F) ⊗[ℂ] G => UniformOnFun.ofFun (eqS E (F ⊗[ℂ] G))
        (fun ab => tensorFunctional E (F ⊗[ℂ] G) ab (TensorProduct.assoc ℂ E F G w)))
      inferInstance := by
    rw [eps_eq, induced_compose]; rfl
  have h3 : ∀ u v i, f3 E F G (u - v) i = f3 E F G u i - f3 E F G v i := by
    intro u v i; simp [f3, tf_sub]
  have hl : ∀ (u v : (E ⊗[ℂ] F) ⊗[ℂ] G) i, tensorFunctional (E ⊗[ℂ] F) G i (u - v) =
      tensorFunctional (E ⊗[ℂ] F) G i u - tensorFunctional (E ⊗[ℂ] F) G i v :=
    fun u v i => tf_sub _ _ i u v
  have hr : ∀ (u v : (E ⊗[ℂ] F) ⊗[ℂ] G) i,
      tensorFunctional E (F ⊗[ℂ] G) i (TensorProduct.assoc ℂ E F G (u - v)) =
      tensorFunctional E (F ⊗[ℂ] G) i (TensorProduct.assoc ℂ E F G u) -
        tensorFunctional E (F ⊗[ℂ] G) i (TensorProduct.assoc ℂ E F G v) :=
    fun u v i => by rw [map_sub, tf_sub]
  rw [hR, eps_eq]
  -- left ≤ triple
  have L1 := dom_le (𝔖 := eqS (E ⊗[ℂ] F) G) (𝔗 := tripS E F G)
    (fun w ab => tensorFunctional (E ⊗[ℂ] F) G ab w) (f3 E F G) hl h3 (by
      rintro _ ⟨A, B, C, hA, hB, hC, rfl⟩
      refine ⟨_ ×ˢ C, ⟨_, C, tfCLM_equicont E F rfl hA hB, hC, rfl⟩, fun ρ hρ => ⟨ρ, hρ, ?_⟩⟩
      rintro w hw ⟨a, b, c⟩ ⟨ha, hb, hc⟩
      have := hw (tfCLM E F rfl a b, c) ⟨⟨(a, b), ⟨ha, hb⟩, rfl⟩, hc⟩
      rw [tf_contrR, tfCLM_apply] at this
      exact this)
  -- triple ≤ left
  have L2 := dom_le (𝔖 := tripS E F G) (𝔗 := eqS (E ⊗[ℂ] F) G)
    (f3 E F G) (fun w ab => tensorFunctional (E ⊗[ℂ] F) G ab w) h3 hl (by
      rintro _ ⟨A', C, hA', hC, rfl⟩
      obtain ⟨A, B, hA, hB, r, hr, hsub⟩ :=
        eps_nhds_zero E F (Metric.equicontinuousAt_iff_right.1 (hA' 0) 1 one_pos)
      refine ⟨A ×ˢ B ×ˢ C, ⟨A, B, C, hA, hB, hC, rfl⟩,
        fun ρ hρ => ⟨r * ρ, mul_pos hr hρ, ?_⟩⟩
      rintro w hw ⟨φ, c⟩ ⟨hφ, hc⟩
      show ‖tensorFunctional (E ⊗[ℂ] F) G (φ, c) w‖ < ρ
      rw [tf_contrR]
      refine scale_lt φ _ hρ (hsub _ (fun a ha b hb => ?_) ⟨φ, hφ⟩)
      rw [tf_smul]
      exact scale_lt' _ hρ (hw (a, b, c) ⟨ha, hb, hc⟩))
  -- right ≤ triple
  have R1 := dom_le (𝔖 := eqS E (F ⊗[ℂ] G)) (𝔗 := tripS E F G)
    (fun w ab => tensorFunctional E (F ⊗[ℂ] G) ab (TensorProduct.assoc ℂ E F G w)) (f3 E F G)
    hr h3 (by
      rintro _ ⟨A, B, C, hA, hB, hC, rfl⟩
      refine ⟨A ×ˢ _, ⟨A, _, hA, tfCLM_equicont F G rfl hB hC, rfl⟩, fun ρ hρ => ⟨ρ, hρ, ?_⟩⟩
      rintro w hw ⟨a, b, c⟩ ⟨ha, hb, hc⟩
      have := hw (a, tfCLM F G rfl b c) ⟨ha, ⟨(b, c), ⟨hb, hc⟩, rfl⟩⟩
      rw [tf_contrL, tfCLM_apply, tf_assoc] at this
      exact this)
  -- triple ≤ right
  have R2 := dom_le (𝔖 := tripS E F G) (𝔗 := eqS E (F ⊗[ℂ] G))
    (f3 E F G) (fun w ab => tensorFunctional E (F ⊗[ℂ] G) ab (TensorProduct.assoc ℂ E F G w))
    h3 hr (by
      rintro _ ⟨A, B', hA, hB', rfl⟩
      obtain ⟨B, C, hB, hC, r, hr, hsub⟩ :=
        eps_nhds_zero F G (Metric.equicontinuousAt_iff_right.1 (hB' 0) 1 one_pos)
      refine ⟨A ×ˢ B ×ˢ C, ⟨A, B, C, hA, hB, hC, rfl⟩,
        fun ρ hρ => ⟨r * ρ, mul_pos hr hρ, ?_⟩⟩
      rintro w hw ⟨a, ψ⟩ ⟨ha, hψ⟩
      show ‖tensorFunctional E (F ⊗[ℂ] G) (a, ψ) (TensorProduct.assoc ℂ E F G w)‖ < ρ
      rw [tf_contrL]
      refine scale_lt ψ _ hρ (hsub _ (fun b hb c hc => ?_) ⟨ψ, hψ⟩)
      rw [tf_smul, tf_assoc]
      exact scale_lt' _ hρ (hw (a, b, c) ⟨ha, hb, hc⟩))
  exact le_antisymm (L1.trans R2) (R1.trans L2)
