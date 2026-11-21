-- Prove2me | solution 1 for MasulloGRH.abs_summing_of_l1_tensor_topologies_eq
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:25:23.184871+00:00
-- url     : https://prove2.me/submissions/6c36db5f-3509-4230-a02d-5c1637972b69

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open MasulloGRH TensorProduct Topology Filter

universe u

namespace AbsSummingAux

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


/-- A `0`-neighbourhood for the `ε`-topology contains a set cut out by a product of
equicontinuous sets. -/
theorem exists_of_eps_nhds (U : Set (X ⊗[ℂ] Y))
    (hU : U ∈ @nhds _ (epsTensorTopology X Y) (0 : X ⊗[ℂ] Y)) :
    ∃ (A : Set (StrongDual ℂ X)) (B : Set (StrongDual ℂ Y)),
      Equicontinuous (fun a : A => (a : X → ℂ)) ∧ Equicontinuous (fun b : B => (b : Y → ℂ)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ u : X ⊗[ℂ] Y,
        (∀ a ∈ A, ∀ b ∈ B, ‖tensorFunctional X Y (a, b) u‖ < δ) → u ∈ U := by
  have hn : @nhds _ (epsTensorTopology X Y) (0 : X ⊗[ℂ] Y) =
      Filter.comap (fun u => UniformOnFun.ofFun (eqSets X Y) (Ψ X Y u))
        (𝓝 (UniformOnFun.ofFun (eqSets X Y) (Ψ X Y 0))) := nhds_induced _ _
  rw [hn, Filter.mem_comap] at hU
  obtain ⟨V0, hV0, hsubU⟩ := hU
  obtain ⟨⟨S, V⟩, ⟨⟨A, B, hA, hB, hS⟩, hV⟩, hsub⟩ :=
    (UniformOnFun.hasBasis_nhds _ _ _ (UniformOnFun.ofFun (eqSets X Y) (Ψ X Y 0))
      (eqSets_nonempty X Y) (eqSets_directed X Y)).mem_iff.1 hV0
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_uniformity_dist.1 hV
  refine ⟨A, B, hA, hB, δ, hδ, fun u hu => hsubU (hsub ?_)⟩
  intro x hx
  apply hδV
  change dist (Ψ X Y u x) (Ψ X Y 0 x) < δ
  have hx' : x ∈ A ×ˢ B := hS ▸ hx
  rw [map_zero, Pi.zero_apply, dist_zero_right]
  exact hu x.1 hx'.1 x.2 hx'.2

end defs

/-- The seminorm `c • p` for a real `c ≥ 0`. -/
noncomputable def sc {X : Type*} [AddCommGroup X] [Module ℂ X] (c : ℝ) (hc : 0 ≤ c)
    (p : Seminorm ℂ X) : Seminorm ℂ X :=
  let c' : NNReal := ⟨c, hc⟩
  c' • p

theorem sc_apply {X : Type*} [AddCommGroup X] [Module ℂ X] (c : ℝ) (hc : 0 ≤ c)
    (p : Seminorm ℂ X) (x : X) : sc c hc p x = c * p x := rfl

/-- The space `ℓ¹`, lifted to the universe `u`. -/
abbrev L : Type u := ULift.{u} (lp (fun _ : ℕ => ℂ) 1)

/-- The `i`-th coordinate functional on `ℓ¹`. -/
noncomputable def coord (i : ℕ) : L.{u} →ₗ[ℂ] ℂ where
  toFun ξ := ξ.down i
  map_add' ξ η := rfl
  map_smul' c ξ := rfl

/-- The `k`-th unit vector of `ℓ¹`. -/
noncomputable def e (k : ℕ) : L.{u} := ULift.up (lp.single 1 k (1 : ℂ) : lp (fun _ : ℕ => ℂ) 1)

theorem norm_e (k : ℕ) : ‖(e k : L.{u})‖ = 1 := by
  rw [e, ULift.norm_up, lp.norm_single one_pos]
  simp

theorem coord_e (j k : ℕ) : coord j (e k : L.{u}) = if j = k then 1 else 0 := by
  change (lp.single 1 k (1 : ℂ) : lp (fun _ : ℕ => ℂ) 1) j = _
  rw [lp.single_apply, Pi.single_apply]

theorem sum_coord_le (ξ : L.{u}) (n : ℕ) : ∑ i ∈ Finset.range n, ‖coord i ξ‖ ≤ ‖ξ‖ := by
  have h := lp.sum_rpow_le_norm_rpow (p := 1) (by simp) ξ.down (Finset.range n)
  simp only [ENNReal.toReal_one, Real.rpow_one] at h
  exact h

end AbsSummingAux

open AbsSummingAux in
theorem solution (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (ht : projTensorTopology E (ULift.{u} (lp (fun _ : ℕ => ℂ) 1)) =
      epsTensorTopology E (ULift.{u} (lp (fun _ : ℕ => ℂ) 1))) :
    ∀ p : Seminorm ℂ E, Continuous p → ∃ q : Seminorm ℂ E, Continuous q ∧
      ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
        (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (x i)‖ ≤ c) →
        ∑ i, p (x i) ≤ c := by
  intro p hp
  have hEg : IsTopologicalAddGroup E := addGroup_of_lc _ hE.1
  -- the slice maps and the seminorm `N u = ∑ᵢ p (uᵢ)`
  let S : ℕ → E ⊗[ℂ] L.{u} →ₗ[ℂ] E := fun i =>
    (TensorProduct.rid ℂ E).toLinearMap ∘ₗ TensorProduct.map LinearMap.id (coord i)
  have hS : ∀ (i : ℕ) (x : E) (ξ : L.{u}), S i (x ⊗ₜ[ℂ] ξ) = coord i ξ • x := by
    intro i x ξ
    simp [S]
  let fam : ℕ → Seminorm ℂ (E ⊗[ℂ] L.{u}) := fun n => ∑ i ∈ Finset.range n, p.comp (S i)
  have hfam : ∀ (n : ℕ) (w : E ⊗[ℂ] L.{u}), fam n w = ∑ i ∈ Finset.range n, p (S i w) := by
    intro n w
    induction n with
    | zero => simp [fam]
    | succ n ih =>
      have h1 : fam (n + 1) = fam n + p.comp (S n) := Finset.sum_range_succ _ _
      rw [h1, Seminorm.add_apply, ih, Finset.sum_range_succ, Seminorm.comp_apply]
  have hfam_tmul : ∀ (n : ℕ) (x : E) (ξ : L.{u}), fam n (x ⊗ₜ[ℂ] ξ) ≤ p x * ‖ξ‖ := by
    intro n x ξ
    rw [hfam]
    have h1 : ∀ i ∈ Finset.range n, p (S i (x ⊗ₜ[ℂ] ξ)) = ‖coord i ξ‖ * p x := by
      intro i _
      rw [hS, map_smul_eq_mul]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (sum_coord_le ξ n) (apply_nonneg p x)
  have hbddpt : ∀ w : E ⊗[ℂ] L.{u}, ∃ K : ℝ, ∀ n : ℕ, fam n w ≤ K := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, fun n => by simp⟩
    | tmul x ξ => exact ⟨p x * ‖ξ‖, fun n => hfam_tmul n x ξ⟩
    | add v w hv hw =>
      obtain ⟨K1, h1⟩ := hv
      obtain ⟨K2, h2⟩ := hw
      exact ⟨K1 + K2, fun n => (map_add_le_add (fam n) _ _).trans (add_le_add (h1 n) (h2 n))⟩
  have hbdd : BddAbove (Set.range fam) := by
    rw [Seminorm.bddAbove_range_iff]
    intro w
    obtain ⟨K, hK⟩ := hbddpt w
    refine ⟨K, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hK n
  let N : Seminorm ℂ (E ⊗[ℂ] L.{u}) := ⨆ n, fam n
  have hNapp : ∀ w, N w = ⨆ n, fam n w := fun w => Seminorm.iSup_apply hbdd
  have hNge : ∀ (n : ℕ) (w : E ⊗[ℂ] L.{u}), fam n w ≤ N w := by
    intro n w
    rw [hNapp]
    exact le_ciSup (f := fun n : ℕ => fam n w) (Seminorm.bddAbove_range_iff.1 hbdd w) n
  have hNle : ∀ (x : E) (ξ : L.{u}), N (x ⊗ₜ[ℂ] ξ) ≤ p x * (normSeminorm ℂ L.{u}) ξ := by
    intro x ξ
    rw [hNapp]
    exact ciSup_le fun n => hfam_tmul n x ξ
  -- `N` is `π`-continuous, hence `ε`-continuous
  have hNπ : @Continuous _ _ (projTensorTopology E L.{u}) _ N :=
    continuous_seminorm_proj N p (normSeminorm ℂ L.{u}) hp continuous_norm hNle
  rw [ht] at hNπ
  have hU : {w : E ⊗[ℂ] L.{u} | N w < 1} ∈ @nhds _ (epsTensorTopology E L.{u}) 0 := by
    letI : TopologicalSpace (E ⊗[ℂ] L.{u}) := epsTensorTopology E L.{u}
    exact (isOpen_lt hNπ continuous_const).mem_nhds (by simp)
  obtain ⟨A, B, hA, hB, δ, hδ, hN1⟩ := exists_of_eps_nhds E L.{u} _ hU
  -- a continuous seminorm bounding `A`
  have hVA : {x : E | ∀ a : A, dist ((a : StrongDual ℂ E) 0) ((a : StrongDual ℂ E) x) < 1}
      ∈ 𝓝 (0 : E) := hA 0 {p : ℂ × ℂ | dist p.1 p.2 < 1} (Metric.dist_mem_uniformity one_pos)
  obtain ⟨q₀, hq₀c, hq₀⟩ := exists_seminorm_ball_subset hE.1 hVA
  have hq₀' : ∀ a ∈ A, ∀ x : E, ‖a x‖ ≤ q₀ x := by
    intro a ha x
    have h1 := homog_bound q₀ (fun x => ‖a x‖) (fun k x hk => by
      change ‖a ((k : ℂ) • x)‖ = k * ‖a x‖
      rw [map_smul, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk.le])
      1 zero_le_one (fun x hx => by
        have h2 := hq₀ x hx ⟨a, ha⟩
        rw [map_zero, dist_comm, dist_zero_right] at h2
        exact h2.le) x
    simpa using h1
  -- a norm bound for `B`
  have hVB : {ξ : L.{u} | ∀ b : B, dist ((b : StrongDual ℂ L.{u}) 0)
      ((b : StrongDual ℂ L.{u}) ξ) < 1} ∈ 𝓝 (0 : L.{u}) :=
    hB 0 {p : ℂ × ℂ | dist p.1 p.2 < 1} (Metric.dist_mem_uniformity one_pos)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hVB
  have hρi : 0 ≤ ρ⁻¹ := (inv_pos.2 hρ).le
  have hM : ∀ b ∈ B, ∀ ξ : L.{u}, ‖b ξ‖ ≤ ρ⁻¹ * ‖ξ‖ := by
    intro b hb ξ
    have h1 := homog_bound (sc ρ⁻¹ hρi (normSeminorm ℂ L.{u})) (fun ξ => ‖b ξ‖)
      (fun k ξ hk => by
        change ‖b ((k : ℂ) • ξ)‖ = k * ‖b ξ‖
        rw [map_smul, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk.le])
      1 zero_le_one (fun ξ hξ => by
        rw [sc_apply, coe_normSeminorm, inv_mul_lt_iff₀ hρ, mul_one] at hξ
        have h2 := hball (mem_ball_zero_iff.2 hξ) ⟨b, hb⟩
        rw [map_zero, dist_comm, dist_zero_right] at h2
        exact h2.le) ξ
    rw [sc_apply, coe_normSeminorm, one_mul] at h1
    exact h1
  -- the seminorm `q = (ρ⁻¹ / δ) q₀`
  have hK : 0 < ρ⁻¹ / δ := div_pos (inv_pos.2 hρ) hδ
  refine ⟨sc (ρ⁻¹ / δ) hK.le q₀, ?_, ?_⟩
  · have : (fun x => (sc (ρ⁻¹ / δ) hK.le q₀) x) = fun x => ρ⁻¹ / δ * q₀ x :=
      funext fun x => sc_apply _ _ _ _
    change Continuous (fun x => (sc (ρ⁻¹ / δ) hK.le q₀) x)
    rw [this]
    exact continuous_const.mul hq₀c
  intro n x c hyp
  have hc0 : 0 ≤ c := by
    have h1 := hyp 0 (fun y => by
      rw [ContinuousLinearMap.zero_apply, norm_zero]
      exact apply_nonneg _ y)
    simpa using h1
  let w : E ⊗[ℂ] L.{u} := ∑ i : Fin n, x i ⊗ₜ[ℂ] (e (i : ℕ) : L.{u})
  -- `∑ p (x i) ≤ N w`
  have hlow : ∑ i, p (x i) ≤ N w := by
    refine le_trans (le_of_eq ?_) (hNge n w)
    rw [hfam, Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    change x j = S (j : ℕ) (∑ i : Fin n, x i ⊗ₜ[ℂ] (e (i : ℕ) : L.{u}))
    rw [map_sum]
    simp only [hS, coord_e, Fin.val_inj]
    simp
  -- `(a ⊗ b)(w)` is small
  have hAsum : ∀ a ∈ A, (ρ⁻¹ / δ) * ∑ i, ‖a (x i)‖ ≤ c := by
    intro a ha
    have h1 := hyp (((ρ⁻¹ / δ : ℝ) : ℂ) • a) (fun y => by
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hK.le, sc_apply]
      exact mul_le_mul_of_nonneg_left (hq₀' a ha y) hK.le)
    rw [Finset.mul_sum]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) h1
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hK.le]
  have htf : ∀ a ∈ A, ∀ b ∈ B, ‖tensorFunctional E L.{u} (a, b) w‖ ≤ c * δ := by
    intro a ha b hb
    have h1 : tensorFunctional E L.{u} (a, b) w = ∑ i : Fin n, a (x i) * b (e (i : ℕ)) := by
      change Ψ E L.{u} w (a, b) = _
      simp only [w, map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Ψ]
    rw [h1]
    calc ‖∑ i : Fin n, a (x i) * b (e (i : ℕ))‖
        ≤ ∑ i : Fin n, ‖a (x i) * b (e (i : ℕ))‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ‖a (x i)‖ * ρ⁻¹ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have := hM b hb (e (i : ℕ))
          rwa [norm_e, mul_one] at this
      _ = δ * ((ρ⁻¹ / δ) * ∑ i, ‖a (x i)‖) := by
          rw [← Finset.sum_mul]; field_simp
      _ ≤ δ * c := mul_le_mul_of_nonneg_left (hAsum a ha) hδ.le
      _ = c * δ := mul_comm _ _
  have hNw : N w ≤ c := by
    refine le_of_forall_pos_lt_add fun η hη => ?_
    have ht : 0 < c + η := by linarith
    have h1 : N ((((c + η)⁻¹ : ℝ) : ℂ) • w) < 1 := by
      apply hN1
      intro a ha b hb
      change ‖Ψ E L.{u} ((((c + η)⁻¹ : ℝ) : ℂ) • w) (a, b)‖ < δ
      rw [map_smul, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.2 ht.le), inv_mul_lt_iff₀ ht]
      have h2 : ‖Ψ E L.{u} w (a, b)‖ ≤ c * δ := htf a ha b hb
      nlinarith
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 ht.le),
      inv_mul_lt_iff₀ ht, mul_one] at h1
    exact h1
  exact hlow.trans hNw
