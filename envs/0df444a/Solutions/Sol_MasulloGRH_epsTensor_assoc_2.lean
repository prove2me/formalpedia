-- Prove2me | solution 2 for MasulloGRH.epsTensor_assoc
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:18:56.431393+00:00
-- url     : https://prove2.me/submissions/646b1bf2-1490-433c-b8bc-f1f09ea6de28

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open MasulloGRH TensorProduct Topology Filter

universe u

namespace EpsTensorAssocAux

/-- Comparison of two topologies of uniform convergence on families of sets, pulled back along
linear maps into function spaces. -/
theorem induced_uniformOnFun_le {W α₁ α₂ : Type*} [AddCommGroup W] [Module ℂ W]
    (𝔖₁ : Set (Set α₁)) (𝔖₂ : Set (Set α₂)) (φ₁ : W →ₗ[ℂ] (α₁ → ℂ)) (φ₂ : W →ₗ[ℂ] (α₂ → ℂ))
    (h : ∀ S₂ ∈ 𝔖₂, ∃ S₁ ∈ 𝔖₁, ∃ δ : ℝ, 0 < δ ∧
      ∀ w : W, (∀ x ∈ S₁, ‖φ₁ w x‖ < δ) → ∀ y ∈ S₂, ‖φ₂ w y‖ < 1) :
    TopologicalSpace.induced (fun w => UniformOnFun.ofFun 𝔖₁ (φ₁ w)) inferInstance ≤
      TopologicalSpace.induced (fun w => UniformOnFun.ofFun 𝔖₂ (φ₂ w)) inferInstance := by
  rw [← continuous_iff_le_induced]
  letI : TopologicalSpace W :=
    TopologicalSpace.induced (fun w => UniformOnFun.ofFun 𝔖₁ (φ₁ w)) inferInstance
  have hc1 : Continuous (fun w : W => UniformOnFun.ofFun 𝔖₁ (φ₁ w)) := continuous_induced_dom
  rw [continuous_iff_continuousAt]
  intro w0
  refine UniformOnFun.tendsto_iff_tendstoUniformlyOn.2 ?_
  intro S₂ hS₂
  obtain ⟨S₁, hS₁, δ, hδ, hw⟩ := h S₂ hS₂
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h1 := UniformOnFun.tendsto_iff_tendstoUniformlyOn.1 (hc1.tendsto w0) S₁ hS₁
  rw [Metric.tendstoUniformlyOn_iff] at h1
  filter_upwards [h1 (ε * δ) (mul_pos hε hδ)] with w hwS y hy
  have hwS' : ∀ x ∈ S₁, dist (φ₁ w0 x) (φ₁ w x) < ε * δ := hwS
  change dist (φ₂ w0 y) (φ₂ w y) < ε
  have hεn : ‖((ε⁻¹ : ℝ) : ℂ)‖ = ε⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hε.le)]
  have hx' : ∀ x ∈ S₁, ‖φ₁ (((ε⁻¹ : ℝ) : ℂ) • (w - w0)) x‖ < δ := by
    intro x hx
    have h2 := hwS' x hx
    rw [dist_comm, dist_eq_norm] at h2
    rw [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, norm_mul, hεn,
      inv_mul_lt_iff₀ hε]
    exact h2
  have key := hw _ hx' y hy
  rw [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, norm_mul, hεn,
    inv_mul_lt_iff₀ hε, mul_one] at key
  rw [dist_comm, dist_eq_norm]
  exact key

section defs

variable (X Y : Type u) [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]

/-- The products of equicontinuous sets of functionals. -/
def eqSets : Set (Set (StrongDual ℂ X × StrongDual ℂ Y)) :=
  {S | ∃ (A : Set (StrongDual ℂ X)) (B : Set (StrongDual ℂ Y)),
    Equicontinuous (fun a : A => (a : X → ℂ)) ∧
    Equicontinuous (fun b : B => (b : Y → ℂ)) ∧ S = A ×ˢ B}

/-- The linear map `u ↦ ((x', y') ↦ (x' ⊗ y')(u))`. -/
noncomputable def Ψ : X ⊗[ℂ] Y →ₗ[ℂ] (StrongDual ℂ X × StrongDual ℂ Y → ℂ) :=
  LinearMap.pi fun ab =>
    (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
      TensorProduct.map (ab.1 : X →ₗ[ℂ] ℂ) (ab.2 : Y →ₗ[ℂ] ℂ)

theorem eps_eq : epsTensorTopology X Y =
    TopologicalSpace.induced (fun u => UniformOnFun.ofFun (eqSets X Y) (Ψ X Y u))
      inferInstance := rfl

theorem equicontinuous_union {A₁ A₂ : Set (StrongDual ℂ X)}
    (h₁ : Equicontinuous (fun a : A₁ => ((a : StrongDual ℂ X) : X → ℂ)))
    (h₂ : Equicontinuous (fun a : A₂ => ((a : StrongDual ℂ X) : X → ℂ))) :
    Equicontinuous (fun a : (A₁ ∪ A₂ : Set (StrongDual ℂ X)) =>
      ((a : StrongDual ℂ X) : X → ℂ)) := by
  intro x0 U hU
  filter_upwards [h₁ x0 U hU, h₂ x0 U hU] with x hx1 hx2
  rintro ⟨a, ha | ha⟩
  · exact hx1 ⟨a, ha⟩
  · exact hx2 ⟨a, ha⟩

theorem eqSets_nonempty : (eqSets X Y).Nonempty :=
  ⟨∅ ×ˢ ∅, ∅, ∅, fun x0 U hU => Filter.Eventually.of_forall fun x i => i.2.elim,
    fun x0 U hU => Filter.Eventually.of_forall fun x i => i.2.elim, rfl⟩

theorem eqSets_directed : DirectedOn (· ⊆ ·) (eqSets X Y) := by
  rintro _ ⟨A₁, B₁, hA₁, hB₁, rfl⟩ _ ⟨A₂, B₂, hA₂, hB₂, rfl⟩
  exact ⟨(A₁ ∪ A₂) ×ˢ (B₁ ∪ B₂),
    ⟨_, _, equicontinuous_union X hA₁ hA₂, equicontinuous_union Y hB₁ hB₂, rfl⟩,
    Set.prod_mono Set.subset_union_left Set.subset_union_left,
    Set.prod_mono Set.subset_union_right Set.subset_union_right⟩

variable [tXY : TopologicalSpace (X ⊗[ℂ] Y)] (h : tXY = epsTensorTopology X Y)

include h in
/-- Uniform continuity estimate for the `ε`-topology on products of equicontinuous sets. -/
theorem eps_uniform (A : Set (StrongDual ℂ X)) (B : Set (StrongDual ℂ Y))
    (hA : Equicontinuous (fun a : A => (a : X → ℂ)))
    (hB : Equicontinuous (fun b : B => (b : Y → ℂ)))
    (u0 : X ⊗[ℂ] Y) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ u in 𝓝 u0, ∀ a ∈ A, ∀ b ∈ B,
      ‖tensorFunctional X Y (a, b) u - tensorFunctional X Y (a, b) u0‖ < ε := by
  subst h
  letI : TopologicalSpace (X ⊗[ℂ] Y) := epsTensorTopology X Y
  have hc : Continuous (fun u : X ⊗[ℂ] Y => UniformOnFun.ofFun (eqSets X Y) (Ψ X Y u)) :=
    continuous_induced_dom
  have h1 := UniformOnFun.tendsto_iff_tendstoUniformlyOn.1 (hc.tendsto u0) (A ×ˢ B)
    ⟨A, B, hA, hB, rfl⟩
  rw [Metric.tendstoUniformlyOn_iff] at h1
  filter_upwards [h1 ε hε] with u hu a ha b hb
  have h2 := hu (a, b) ⟨ha, hb⟩
  rw [dist_comm, dist_eq_norm] at h2
  exact h2

include h in
theorem tensorFunctional_continuous (a : StrongDual ℂ X) (b : StrongDual ℂ Y) :
    Continuous (tensorFunctional X Y (a, b)) := by
  have hA : Equicontinuous (fun a' : ({a} : Set (StrongDual ℂ X)) =>
      ((a' : StrongDual ℂ X) : X → ℂ)) :=
    equicontinuous_finite.2 fun a' => a'.1.continuous
  have hB : Equicontinuous (fun b' : ({b} : Set (StrongDual ℂ Y)) =>
      ((b' : StrongDual ℂ Y) : Y → ℂ)) :=
    equicontinuous_finite.2 fun b' => b'.1.continuous
  rw [continuous_iff_continuousAt]
  intro u0
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [eps_uniform X Y h {a} {b} hA hB u0 ε hε] with u hu
  rw [dist_eq_norm]
  exact hu a rfl b rfl

/-- `x' ⊗ y'` as a continuous linear functional on `X ⊗_ε Y`. -/
noncomputable def tf (a : StrongDual ℂ X) (b : StrongDual ℂ Y) : StrongDual ℂ (X ⊗[ℂ] Y) :=
  ⟨(TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
      TensorProduct.map (a : X →ₗ[ℂ] ℂ) (b : Y →ₗ[ℂ] ℂ),
    tensorFunctional_continuous X Y h a b⟩

theorem tf_apply (a : StrongDual ℂ X) (b : StrongDual ℂ Y) (u : X ⊗[ℂ] Y) :
    tf X Y h a b u = tensorFunctional X Y (a, b) u := rfl

/-- The functionals `x' ⊗ y'`, `x' ∈ A`, `y' ∈ B`, form an equicontinuous subset of the dual of
`X ⊗_ε Y` when `A` and `B` are equicontinuous. -/
theorem equicontinuous_tf (A : Set (StrongDual ℂ X)) (B : Set (StrongDual ℂ Y))
    (hA : Equicontinuous (fun a : A => (a : X → ℂ)))
    (hB : Equicontinuous (fun b : B => (b : Y → ℂ))) :
    Equicontinuous (fun c : {c : StrongDual ℂ (X ⊗[ℂ] Y) | ∃ a ∈ A, ∃ b ∈ B, c = tf X Y h a b} =>
      ((c : StrongDual ℂ (X ⊗[ℂ] Y)) : X ⊗[ℂ] Y → ℂ)) := by
  intro u0 U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.1 hU
  filter_upwards [eps_uniform X Y h A B hA hB u0 ε hε] with u hu
  rintro ⟨c, a, ha, b, hb, rfl⟩
  apply hεU
  rw [dist_comm, dist_eq_norm]
  exact hu a ha b hb

include h in
/-- An equicontinuous subset of the dual of `X ⊗_ε Y` is dominated by a product of
equicontinuous sets. -/
theorem exists_of_equicontinuous (C : Set (StrongDual ℂ (X ⊗[ℂ] Y)))
    (hC : Equicontinuous (fun c : C => ((c : StrongDual ℂ (X ⊗[ℂ] Y)) : X ⊗[ℂ] Y → ℂ))) :
    ∃ (A : Set (StrongDual ℂ X)) (B : Set (StrongDual ℂ Y)),
      Equicontinuous (fun a : A => (a : X → ℂ)) ∧ Equicontinuous (fun b : B => (b : Y → ℂ)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ u : X ⊗[ℂ] Y,
        (∀ a ∈ A, ∀ b ∈ B, ‖tensorFunctional X Y (a, b) u‖ < δ) → ∀ c ∈ C, ‖c u‖ < 1 := by
  subst h
  letI : TopologicalSpace (X ⊗[ℂ] Y) := epsTensorTopology X Y
  have h0 := hC 0 {p : ℂ × ℂ | dist p.1 p.2 < 1} (Metric.dist_mem_uniformity one_pos)
  have hn : @nhds _ (epsTensorTopology X Y) (0 : X ⊗[ℂ] Y) =
      Filter.comap (fun u => UniformOnFun.ofFun (eqSets X Y) (Ψ X Y u))
        (𝓝 (UniformOnFun.ofFun (eqSets X Y) (Ψ X Y 0))) := nhds_induced _ _
  rw [hn, Filter.eventually_comap] at h0
  obtain ⟨⟨S, V⟩, ⟨⟨A, B, hA, hB, hS⟩, hV⟩, hsub⟩ :=
    (UniformOnFun.hasBasis_nhds _ _ _ (UniformOnFun.ofFun (eqSets X Y) (Ψ X Y 0))
      (eqSets_nonempty X Y) (eqSets_directed X Y)).eventually_iff.1 h0
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_uniformity_dist.1 hV
  refine ⟨A, B, hA, hB, δ, hδ, fun u hu c hc => ?_⟩
  have hmem : UniformOnFun.ofFun (eqSets X Y) (Ψ X Y u) ∈
      {g | (g, UniformOnFun.ofFun (eqSets X Y) (Ψ X Y 0)) ∈ UniformOnFun.gen (eqSets X Y) S V} := by
    intro x hx
    apply hδV
    change dist (Ψ X Y u x) (Ψ X Y 0 x) < δ
    have hx' : x ∈ A ×ˢ B := hS ▸ hx
    rw [map_zero, Pi.zero_apply, dist_zero_right]
    exact hu x.1 hx'.1 x.2 hx'.2
  have h3 := hsub hmem u rfl ⟨c, hc⟩
  have h4 : dist (c 0) (c u) < 1 := h3
  rw [map_zero, dist_comm, dist_zero_right] at h4
  exact h4

end defs

section slices

variable {X Y : Type u} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]

/-- `(x' ⊗ y')(u) = y'((x' ⊗ id)(u))`. -/
theorem tensorFunctional_left (a : StrongDual ℂ X) (b : StrongDual ℂ Y) (w : X ⊗[ℂ] Y) :
    tensorFunctional X Y (a, b) w =
      b (TensorProduct.lid ℂ Y (TensorProduct.map (a : X →ₗ[ℂ] ℂ) LinearMap.id w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp [tensorFunctional]
  | tmul x y => simp [tensorFunctional]
  | add v w hv hw =>
    simp only [tensorFunctional, map_add] at hv hw ⊢
    rw [hv, hw]

/-- `(x' ⊗ y')(u) = x'((id ⊗ y')(u))`. -/
theorem tensorFunctional_right (a : StrongDual ℂ X) (b : StrongDual ℂ Y) (w : X ⊗[ℂ] Y) :
    tensorFunctional X Y (a, b) w =
      a (TensorProduct.rid ℂ X (TensorProduct.map LinearMap.id (b : Y →ₗ[ℂ] ℂ) w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp [tensorFunctional]
  | tmul x y => simp [tensorFunctional, mul_comm]
  | add v w hv hw =>
    simp only [tensorFunctional, map_add] at hv hw ⊢
    rw [hv, hw]

end slices

section threefold

variable {E F G : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]

theorem slice_right_assoc [TopologicalSpace (F ⊗[ℂ] G)] (a : StrongDual ℂ E)
    (b : StrongDual ℂ F) (d : StrongDual ℂ G) (κ : StrongDual ℂ (F ⊗[ℂ] G))
    (hκ : ∀ v, κ v = tensorFunctional F G (b, d) v) (w : (E ⊗[ℂ] F) ⊗[ℂ] G) :
    tensorFunctional E F (a, b)
        (TensorProduct.rid ℂ (E ⊗[ℂ] F) (TensorProduct.map LinearMap.id (d : G →ₗ[ℂ] ℂ) w)) =
      tensorFunctional E (F ⊗[ℂ] G) (a, κ) (TensorProduct.assoc ℂ E F G w) := by
  have H : ((TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
        TensorProduct.map (a : E →ₗ[ℂ] ℂ) (b : F →ₗ[ℂ] ℂ)) ∘ₗ
        (TensorProduct.rid ℂ (E ⊗[ℂ] F)).toLinearMap ∘ₗ
          TensorProduct.map LinearMap.id (d : G →ₗ[ℂ] ℂ) =
      ((TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
        TensorProduct.map (a : E →ₗ[ℂ] ℂ) (κ : F ⊗[ℂ] G →ₗ[ℂ] ℂ)) ∘ₗ
        (TensorProduct.assoc ℂ E F G).toLinearMap := by
    apply TensorProduct.ext_threefold
    intro x y z
    simp [hκ, tensorFunctional]
    ring
  exact LinearMap.congr_fun H w

theorem slice_left_assoc [TopologicalSpace (E ⊗[ℂ] F)] (a : StrongDual ℂ E)
    (b : StrongDual ℂ F) (d : StrongDual ℂ G) (c : StrongDual ℂ (E ⊗[ℂ] F))
    (hc : ∀ u, c u = tensorFunctional E F (a, b) u) (w : (E ⊗[ℂ] F) ⊗[ℂ] G) :
    tensorFunctional F G (b, d)
        (TensorProduct.lid ℂ (F ⊗[ℂ] G) (TensorProduct.map (a : E →ₗ[ℂ] ℂ) LinearMap.id
          (TensorProduct.assoc ℂ E F G w))) =
      tensorFunctional (E ⊗[ℂ] F) G (c, d) w := by
  have H : ((TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
        TensorProduct.map (b : F →ₗ[ℂ] ℂ) (d : G →ₗ[ℂ] ℂ)) ∘ₗ
        (TensorProduct.lid ℂ (F ⊗[ℂ] G)).toLinearMap ∘ₗ
          TensorProduct.map (a : E →ₗ[ℂ] ℂ) LinearMap.id ∘ₗ
            (TensorProduct.assoc ℂ E F G).toLinearMap =
      ((TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
        TensorProduct.map (c : E ⊗[ℂ] F →ₗ[ℂ] ℂ) (d : G →ₗ[ℂ] ℂ)) := by
    apply TensorProduct.ext_threefold
    intro x y z
    simp [hc, tensorFunctional]
    ring
  exact LinearMap.congr_fun H w

end threefold

end EpsTensorAssocAux

open EpsTensorAssocAux in
theorem solution (E F G : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (hE : IsHLCS E) (hF : IsHLCS F) (hG : IsHLCS G) :
    @epsTensorTopology (E ⊗[ℂ] F) _ _ (epsTensorTopology E F) G _ _ _ =
      TopologicalSpace.induced (TensorProduct.assoc ℂ E F G)
        (@epsTensorTopology E _ _ _ (F ⊗[ℂ] G) _ _ (epsTensorTopology F G)) := by
  letI tEF : TopologicalSpace (E ⊗[ℂ] F) := epsTensorTopology E F
  letI tFG : TopologicalSpace (F ⊗[ℂ] G) := epsTensorTopology F G
  have hL : epsTensorTopology (E ⊗[ℂ] F) G =
      TopologicalSpace.induced
        (fun w => UniformOnFun.ofFun (eqSets (E ⊗[ℂ] F) G) (Ψ (E ⊗[ℂ] F) G w)) inferInstance :=
    rfl
  have hR : TopologicalSpace.induced (TensorProduct.assoc ℂ E F G)
        (epsTensorTopology E (F ⊗[ℂ] G)) =
      TopologicalSpace.induced
        (fun w => UniformOnFun.ofFun (eqSets E (F ⊗[ℂ] G))
          ((Ψ E (F ⊗[ℂ] G) ∘ₗ (TensorProduct.assoc ℂ E F G).toLinearMap) w)) inferInstance := by
    rw [eps_eq, induced_compose]
    rfl
  change epsTensorTopology (E ⊗[ℂ] F) G =
    TopologicalSpace.induced (TensorProduct.assoc ℂ E F G) (epsTensorTopology E (F ⊗[ℂ] G))
  rw [hL, hR]
  apply le_antisymm
  · apply induced_uniformOnFun_le
    rintro _ ⟨A, Q, hA, hQ, rfl⟩
    obtain ⟨B, D, hB, hD, δ, hδ, hQ'⟩ := exists_of_equicontinuous F G rfl Q hQ
    refine ⟨{c | ∃ a ∈ A, ∃ b ∈ B, c = tf E F rfl a b} ×ˢ D,
      ⟨_, D, equicontinuous_tf E F rfl A B hA hB, hD, rfl⟩, δ, hδ, ?_⟩
    intro w hw
    rintro ⟨a, κ⟩ ⟨ha, hκ⟩
    change ‖tensorFunctional E (F ⊗[ℂ] G) (a, κ) (TensorProduct.assoc ℂ E F G w)‖ < 1
    rw [tensorFunctional_left]
    apply hQ' _ _ κ hκ
    intro b hb d hd
    rw [slice_left_assoc a b d (tf E F rfl a b) (fun u => rfl)]
    exact hw (tf E F rfl a b, d) ⟨⟨a, ha, b, hb, rfl⟩, hd⟩
  · apply induced_uniformOnFun_le
    rintro _ ⟨C, D, hC, hD, rfl⟩
    obtain ⟨A, B, hA, hB, δ, hδ, hC'⟩ := exists_of_equicontinuous E F rfl C hC
    refine ⟨A ×ˢ {κ | ∃ b ∈ B, ∃ d ∈ D, κ = tf F G rfl b d},
      ⟨A, _, hA, equicontinuous_tf F G rfl B D hB hD, rfl⟩, δ, hδ, ?_⟩
    intro w hw
    rintro ⟨c, d⟩ ⟨hc, hd⟩
    change ‖tensorFunctional (E ⊗[ℂ] F) G (c, d) w‖ < 1
    rw [tensorFunctional_right]
    apply hC' _ _ c hc
    intro a ha b hb
    rw [slice_right_assoc a b d (tf F G rfl b d) (fun v => rfl)]
    exact hw (a, tf F G rfl b d) ⟨ha, b, hb, d, hd, rfl⟩
