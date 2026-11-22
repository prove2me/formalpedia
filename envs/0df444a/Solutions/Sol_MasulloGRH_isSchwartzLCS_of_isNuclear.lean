-- Prove2me | solution 1 for MasulloGRH.isSchwartzLCS_of_isNuclear
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:35:22.150831+00:00
-- url     : https://prove2.me/submissions/d15d273f-ea28-4739-b3c5-ba517ac669fb

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_LocallyConvex_SchwartzSpace

open Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_isSchwartzLCS_of_isNuclear

open MasulloGRH TensorProduct Filter Set

universe u

section seminormed

variable {E : Type u} [AddCommGroup E] [Module ℂ E]

/-- `E` with the seminorm `p` as its norm. -/
def WS (_p : Seminorm ℂ E) : Type u := E

variable (p : Seminorm ℂ E)

noncomputable instance : SeminormedAddCommGroup (WS p) :=
  (p.toAddGroupSeminorm.toSeminormedAddCommGroup : SeminormedAddCommGroup E)

instance : Module ℂ (WS p) := inferInstanceAs (Module ℂ E)

/-- The identity map `E → (E, p)`. -/
def toWS : E →ₗ[ℂ] WS p where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem norm_toWS (x : E) : ‖toWS p x‖ = p x := rfl

noncomputable instance : NormedSpace ℂ (WS p) :=
  ⟨fun c x => (map_smul_eq_mul p c x).le⟩

/-- The dual of the seminormed space `(E, p)` is a normed space. -/
noncomputable instance : NormedAddCommGroup (StrongDual ℂ (WS p)) :=
  NormedAddCommGroup.ofSeparation fun f hf => by
    ext x
    have h := f.le_opNorm x
    rw [hf, zero_mul] at h
    exact norm_le_zero_iff.mp h

end seminormed

/-- A normed space is a Hausdorff locally convex space. -/
theorem normed_isHLCS (F : Type u) [NormedAddCommGroup F] [NormedSpace ℂ F] : IsHLCS F := by
  refine ⟨⟨PUnit.{u+1}, ⟨PUnit.unit⟩, fun _ => normSeminorm ℂ F, ?_⟩, inferInstance⟩
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf, iInf_const, coe_normSeminorm,
    comap_norm_nhds_zero]

/-- A seminorm which is at most `1` on the ball `{q < ρ}` is dominated by `ρ⁻¹ q`. -/
theorem seminorm_le_of_ball {V : Type*} [AddCommGroup V] [Module ℂ V] (q r : Seminorm ℂ V)
    {ρ : ℝ} (hρ : 0 < ρ) (h : ∀ x, q x < ρ → r x ≤ 1) (x : V) : r x ≤ ρ⁻¹ * q x := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hq : 0 ≤ q x := apply_nonneg q x
  have hc : 0 < q x + ρ * ε := add_pos_of_nonneg_of_pos hq (mul_pos hρ hε)
  have hpos : 0 < ρ / (q x + ρ * ε) := div_pos hρ hc
  have h1 : q (((ρ / (q x + ρ * ε) : ℝ) : ℂ) • x) < ρ := by
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le, div_mul_eq_mul_div,
      div_lt_iff₀ hc]
    nlinarith [mul_pos hρ hε]
  have h2 := h _ h1
  rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le, div_mul_eq_mul_div,
    div_le_iff₀ hc] at h2
  have h3 : r x ≤ (q x + ρ * ε) / ρ := by
    rw [le_div_iff₀ hρ]
    linarith
  calc r x ≤ (q x + ρ * ε) / ρ := h3
    _ = ρ⁻¹ * q x + ε := by field_simp

section tensor

variable {E F : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- The functional `x' ⊗ y'` as a linear map on `E ⊗ F`. -/
noncomputable def tfLin (ab : StrongDual ℂ E × StrongDual ℂ F) : E ⊗[ℂ] F →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
    TensorProduct.map (ab.1 : E →ₗ[ℂ] ℂ) (ab.2 : F →ₗ[ℂ] ℂ)

theorem tfLin_apply (ab : StrongDual ℂ E × StrongDual ℂ F) (u : E ⊗[ℂ] F) :
    tfLin ab u = tensorFunctional E F ab u := rfl

theorem tfLin_tmul (ab : StrongDual ℂ E × StrongDual ℂ F) (x : E) (y : F) :
    tfLin ab (x ⊗ₜ[ℂ] y) = ab.1 x * ab.2 y := by
  simp [tfLin]

theorem equicontinuous_union (A₁ A₂ : Set (StrongDual ℂ E))
    (h₁ : Equicontinuous (fun a : A₁ => ((a : StrongDual ℂ E) : E → ℂ)))
    (h₂ : Equicontinuous (fun a : A₂ => ((a : StrongDual ℂ E) : E → ℂ))) :
    Equicontinuous (fun a : ↥(A₁ ∪ A₂) => ((a : StrongDual ℂ E) : E → ℂ)) := by
  intro x U hU
  filter_upwards [h₁ x U hU, h₂ x U hU] with y hy₁ hy₂ a
  rcases a.2 with ha | ha
  · exact hy₁ ⟨a, ha⟩
  · exact hy₂ ⟨a, ha⟩

variable (E F) in
/-- The family of sets on which the injective topology is the topology of uniform convergence. -/
def epsFamily : Set (Set (StrongDual ℂ E × StrongDual ℂ F)) :=
  {S : Set (StrongDual ℂ E × StrongDual ℂ F) |
    ∃ (A : Set (StrongDual ℂ E)) (B : Set (StrongDual ℂ F)),
      Equicontinuous (fun a : A => (a : E → ℂ)) ∧
      Equicontinuous (fun b : B => (b : F → ℂ)) ∧ S = A ×ˢ B}

theorem epsFamily_nonempty : (epsFamily E F).Nonempty := by
  refine ⟨(∅ : Set (StrongDual ℂ E)) ×ˢ (∅ : Set (StrongDual ℂ F)), ∅, ∅, ?_, ?_, rfl⟩
  · intro x U _
    exact Filter.Eventually.of_forall fun z a => a.2.elim
  · intro x U _
    exact Filter.Eventually.of_forall fun z a => a.2.elim

theorem epsFamily_directed : DirectedOn (· ⊆ ·) (epsFamily E F) := by
  rintro _ ⟨A₁, B₁, hA₁, hB₁, rfl⟩ _ ⟨A₂, B₂, hA₂, hB₂, rfl⟩
  exact ⟨(A₁ ∪ A₂) ×ˢ (B₁ ∪ B₂),
    ⟨_, _, equicontinuous_union A₁ A₂ hA₁ hA₂, equicontinuous_union B₁ B₂ hB₁ hB₂, rfl⟩,
    prod_mono subset_union_left subset_union_left,
    prod_mono subset_union_right subset_union_right⟩

/-- A neighbourhood of `0` for the injective topology contains a set
`{z | |(a ⊗ b)(z)| < δ for all a ∈ A, b ∈ B}` with `A`, `B` equicontinuous. -/
theorem exists_of_mem_nhds_eps (U : Set (E ⊗[ℂ] F))
    (hU : U ∈ @nhds _ (epsTensorTopology E F) 0) :
    ∃ (A : Set (StrongDual ℂ E)) (B : Set (StrongDual ℂ F)) (δ : ℝ),
      Equicontinuous (fun a : A => ((a : StrongDual ℂ E) : E → ℂ)) ∧
      Equicontinuous (fun b : B => ((b : StrongDual ℂ F) : F → ℂ)) ∧ 0 < δ ∧
      ∀ z : E ⊗[ℂ] F, (∀ a ∈ A, ∀ b ∈ B, ‖tfLin (a, b) z‖ < δ) → z ∈ U := by
  let Φ : E ⊗[ℂ] F → UniformOnFun (StrongDual ℂ E × StrongDual ℂ F) ℂ (epsFamily E F) :=
    fun u => UniformOnFun.ofFun (epsFamily E F) (fun ab => tensorFunctional E F ab u)
  have htop : epsTensorTopology E F = TopologicalSpace.induced Φ inferInstance := rfl
  rw [htop, nhds_induced, mem_comap] at hU
  obtain ⟨t, ht, htU⟩ := hU
  obtain ⟨⟨S, δ⟩, ⟨⟨A, B, hA, hB, hS⟩, hδ⟩, hsub⟩ :=
    (UniformOnFun.hasBasis_nhds_of_basis _ _ (epsFamily E F) (Φ 0) epsFamily_nonempty
      epsFamily_directed Metric.uniformity_basis_dist).mem_iff.mp ht
  refine ⟨A, B, δ, hA, hB, hδ, fun z hz => htU (hsub ?_)⟩
  simp only at hS hδ
  subst hS
  intro ab hab
  change dist (tensorFunctional E F ab z) (tensorFunctional E F ab 0) < δ
  rw [← tfLin_apply, ← tfLin_apply, map_zero, dist_zero_right]
  exact hz ab.1 hab.1 ab.2 hab.2

end tensor


section stage1

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- The dual Banach space of `(E, p)`. -/
abbrev DS (p : Seminorm ℂ E) : Type u := StrongDual ℂ (WS p)

/-- In a nuclear space, for every continuous seminorm `p` there are a continuous seminorm `q` and
a set `A` of linear functionals bounded by `q` such that `∑ p (x i) ≤ C * sup_{a ∈ A} ∑ |a (x i)|`
for all finite families: the canonical map `E_q → E_p` is absolutely summing. -/
theorem exists_absolutelySumming (hN : IsNuclear E) (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ (q : Seminorm ℂ E) (A : Set (StrongDual ℂ E)) (C : ℝ), Continuous q ∧ 0 < C ∧
      (∀ a ∈ A, ∀ x, ‖a x‖ ≤ q x) ∧
      ∀ (n : ℕ) (x : Fin n → E) (M : ℝ), 0 ≤ M → (∀ a ∈ A, ∑ i, ‖a (x i)‖ ≤ M) →
        ∑ i, p (x i) ≤ C * M := by
  obtain ⟨⟨⟨ι, _, P, hP⟩, _⟩, hπε⟩ := hN
  have : IsTopologicalAddGroup E := hP.topologicalAddGroup
  have : ContinuousSMul ℂ E := hP.continuousSMul
  have hEq : projTensorTopology E (DS p) = epsTensorTopology E (DS p) :=
    hπε (DS p) (normed_isHLCS (DS p))
  -- continuity of `E → (E, p)`
  have hcont : Continuous (toWS p) := by
    rw [continuous_iff_continuousAt]
    intro x₀
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have h1 : Continuous (fun x : E => p (x - x₀)) := hp.comp (continuous_id.sub continuous_const)
    have h2 := h1.tendsto x₀
    simp only [sub_self, map_zero] at h2
    exact h2
  -- the canonical pairing
  let B : E →ₗ[ℂ] DS p →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun x f => f (toWS p x))
    (by intros; simp) (by intros; simp) (by intros; rfl) (by intros; rfl)
  let r : Seminorm ℂ (E ⊗[ℂ] DS p) := (normSeminorm ℂ ℂ).comp (TensorProduct.lift B)
  have hr_tmul : ∀ (x : E) (f : DS p), TensorProduct.lift B (x ⊗ₜ[ℂ] f) = f (toWS p x) :=
    fun x f => by rw [TensorProduct.lift.tmul]; rfl
  -- the topology defined by `r`
  let Q : SeminormFamily ℂ (E ⊗[ℂ] DS p) PUnit.{u+1} := fun _ => r
  let t : TopologicalSpace (E ⊗[ℂ] DS p) := Q.moduleFilterBasis.topology
  have ht : @WithSeminorms ℂ (E ⊗[ℂ] DS p) PUnit.{u+1} _ _ _ Q t := ⟨rfl⟩
  have hev : Continuous (fun v : E × DS p => v.2 (toWS p v.1)) := by
    have h := (isBoundedBilinearMap_apply (𝕜 := ℂ) (E := WS p) (F := ℂ)).continuous
    exact h.comp (continuous_snd.prodMk (hcont.comp continuous_fst))
  have htens : @Continuous (E × DS p) (E ⊗[ℂ] DS p) _ t (fun v => v.1 ⊗ₜ[ℂ] v.2) := by
    rw [@continuous_iff_continuousAt _ _ _ t _]
    intro v₀
    refine (WithSeminorms.tendsto_nhds ht _ _).mpr fun _ ε hε => ?_
    have h1 := hev.tendsto v₀
    rw [Metric.tendsto_nhds] at h1
    filter_upwards [h1 ε hε] with v hv
    change ‖TensorProduct.lift B (v.1 ⊗ₜ[ℂ] v.2 - v₀.1 ⊗ₜ[ℂ] v₀.2)‖ < ε
    rw [map_sub, hr_tmul, hr_tmul, ← dist_eq_norm]
    exact hv
  have hle : projTensorTopology E (DS p) ≤ t :=
    sInf_le ⟨⟨PUnit.{u+1}, ⟨PUnit.unit⟩, Q, ht⟩, htens⟩
  have hr_t : @Continuous _ _ t _ r := WithSeminorms.continuous_seminorm ht PUnit.unit
  have hr_eps : @Continuous _ _ (epsTensorTopology E (DS p)) _ r := by
    rw [← hEq]
    exact @Continuous.comp _ _ _ (projTensorTopology E (DS p)) t _ id r hr_t
      (continuous_id_of_le hle)
  have hnhds : {z : E ⊗[ℂ] DS p | r z < 1} ∈ @nhds _ (epsTensorTopology E (DS p)) 0 := by
    have h := @Continuous.tendsto _ _ (epsTensorTopology E (DS p)) _ _ hr_eps 0
    rw [map_zero] at h
    exact h (Iio_mem_nhds one_pos)
  obtain ⟨A, B', δ, hA, hB', hδ, hsub⟩ := exists_of_mem_nhds_eps _ hnhds
  -- `A` is bounded by a continuous seminorm
  have hWA : {x : E | ∀ a : A, dist ((a : StrongDual ℂ E) 0) ((a : StrongDual ℂ E) x) < 1} ∈
      𝓝 (0 : E) := Metric.equicontinuousAt_iff_right.mp (hA 0) 1 one_pos
  obtain ⟨⟨s, ρ⟩, hρ, hsρ⟩ := hP.hasBasis_zero_ball.mem_iff.mp hWA
  simp only at hρ hsρ
  let q₀ : Seminorm ℂ E := s.sup P
  have hq₀ : Continuous q₀ :=
    Seminorm.continuous (r := ρ) (hP.hasBasis_zero_ball.mem_of_mem (i := (s, ρ)) hρ)
  have hAq : ∀ a ∈ A, ∀ x, ‖a x‖ ≤ ρ⁻¹ * q₀ x := by
    intro a ha x
    have h := seminorm_le_of_ball q₀ ((normSeminorm ℂ ℂ).comp (a : E →ₗ[ℂ] ℂ)) hρ
      (fun y hy => ?_) x
    · exact h
    · have hy' : y ∈ q₀.ball 0 ρ := by rw [Seminorm.mem_ball_zero]; exact hy
      have h3 := hsρ hy' ⟨a, ha⟩
      simp only [map_zero, dist_zero_left] at h3
      exact h3.le
  -- `B'` is bounded on the unit ball
  have hWB : {g : DS p | ∀ b : B', dist ((b : StrongDual ℂ (DS p)) 0)
      ((b : StrongDual ℂ (DS p)) g) < 1} ∈ 𝓝 (0 : DS p) :=
    Metric.equicontinuousAt_iff_right.mp (hB' 0) 1 one_pos
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp hWB
  have hBb : ∀ b ∈ B', ∀ g : DS p, ‖b g‖ ≤ η⁻¹ * ‖g‖ := by
    intro b hb g
    have h := seminorm_le_of_ball (normSeminorm ℂ (DS p))
      ((normSeminorm ℂ ℂ).comp (b : DS p →ₗ[ℂ] ℂ)) hη (fun y hy => ?_) g
    · exact h
    · have hy' : y ∈ Metric.ball (0 : DS p) η := by rw [mem_ball_zero_iff]; exact hy
      have h3 := hηsub hy' ⟨b, hb⟩
      simp only [map_zero, dist_zero_left] at h3
      exact h3.le
  let c : NNReal := ⟨ρ⁻¹, (inv_pos.mpr hρ).le⟩
  let q : Seminorm ℂ E := c • q₀
  have hq_apply : ∀ x, q x = ρ⁻¹ * q₀ x := fun x => rfl
  refine ⟨q, A, (δ * η)⁻¹, ?_, inv_pos.mpr (mul_pos hδ hη), ?_, ?_⟩
  · have h : (q : E → ℝ) = fun x => ρ⁻¹ * q₀ x := funext hq_apply
    rw [h]
    exact continuous_const.mul hq₀
  · intro a ha x
    rw [hq_apply]
    exact hAq a ha x
  · intro n x M hM hx
    choose g hg hgx using fun i : Fin n => exists_dual_vector'' ℂ (toWS p (x i))
    have hSnn : 0 ≤ ∑ i, p (x i) := Finset.sum_nonneg fun i _ => apply_nonneg p _
    have key : ∀ M' : ℝ, M < M' → ∑ i, p (x i) ≤ (δ * η)⁻¹ * M' := by
      intro M' hM'
      have hM'pos : 0 < M' := lt_of_le_of_lt hM hM'
      have hτ : 0 < δ * η / M' := div_pos (mul_pos hδ hη) hM'pos
      let z : E ⊗[ℂ] DS p := ∑ i, (((δ * η / M' : ℝ) : ℂ) • x i) ⊗ₜ[ℂ] g i
      have hz : r z < 1 := by
        refine hsub z fun a ha b hb => ?_
        have h1 : tfLin (a, b) z = ∑ i, ((δ * η / M' : ℝ) : ℂ) * (a (x i) * b (g i)) := by
          simp only [z, map_sum, tfLin_tmul, map_smul, smul_eq_mul, mul_assoc]
        rw [h1]
        calc ‖∑ i, ((δ * η / M' : ℝ) : ℂ) * (a (x i) * b (g i))‖
            ≤ ∑ i, ‖((δ * η / M' : ℝ) : ℂ) * (a (x i) * b (g i))‖ := norm_sum_le _ _
          _ ≤ ∑ i, δ * η / M' * (‖a (x i)‖ * η⁻¹) := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ.le]
              refine mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) hτ.le
              calc ‖b (g i)‖ ≤ η⁻¹ * ‖g i‖ := hBb b hb (g i)
                _ ≤ η⁻¹ * 1 := mul_le_mul_of_nonneg_left (hg i) (inv_pos.mpr hη).le
                _ = η⁻¹ := mul_one _
          _ = δ * η / M' * η⁻¹ * ∑ i, ‖a (x i)‖ := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
          _ ≤ δ * η / M' * η⁻¹ * M :=
              mul_le_mul_of_nonneg_left (hx a ha) (mul_nonneg hτ.le (inv_pos.mpr hη).le)
          _ = δ * (M / M') := by field_simp
          _ < δ := by
              have h2 : M / M' < 1 := (div_lt_one hM'pos).mpr hM'
              nlinarith
      have hrz : r z = δ * η / M' * ∑ i, p (x i) := by
        change ‖TensorProduct.lift B z‖ = _
        have h1 : TensorProduct.lift B z = ((δ * η / M' * ∑ i, p (x i) : ℝ) : ℂ) := by
          simp only [z, map_sum, map_smul, hr_tmul, smul_eq_mul, hgx, norm_toWS]
          push_cast
          rw [Finset.mul_sum]
          rfl
        rw [h1, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hτ.le hSnn)]
      rw [hrz, div_mul_eq_mul_div, div_lt_one hM'pos] at hz
      rw [inv_mul_eq_div, le_div_iff₀ (mul_pos hδ hη)]
      linarith [mul_comm (δ * η) (∑ i, p (x i))]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h := key (M + δ * η * ε) (by linarith [mul_pos (mul_pos hδ hη) hε])
    calc ∑ i, p (x i) ≤ (δ * η)⁻¹ * (M + δ * η * ε) := h
      _ = (δ * η)⁻¹ * M + ε := by
          have h0 : δ * η ≠ 0 := (mul_pos hδ hη).ne'
          field_simp

end stage1


section pietsch

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

theorem norm_apply_real_smul (a : E →ₗ[ℂ] ℂ) {c : ℝ} (hc : 0 ≤ c) (x : E) :
    ‖a ((c : ℂ) • x)‖ = c * ‖a x‖ := by
  rw [map_smul, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]

theorem seminorm_real_smul (q : Seminorm ℂ E) {c : ℝ} (hc : 0 ≤ c) (x : E) :
    q ((c : ℂ) • x) = c * q x := by
  rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg hc]

/-- An index type with the discrete topology. -/
def Disc (T : Type*) : Type _ := T

instance (T : Type*) : TopologicalSpace (Disc T) := ⊥

instance (T : Type*) : DiscreteTopology (Disc T) := ⟨rfl⟩

variable {T : Type*} (a : T → E →ₗ[ℂ] ℂ) (q : Seminorm ℂ E)

/-- The absolute summability estimate implies its quadratic version. -/
theorem sum_sq_le {C : ℝ} (hC : 0 ≤ C)
    (hAS : ∀ (n : ℕ) (x : Fin n → E) (M : ℝ), 0 ≤ M → (∀ t, ∑ i, ‖a t (x i)‖ ≤ M) →
      ∑ i, q (x i) ≤ C * M)
    {n : ℕ} (x : Fin n → E) {M : ℝ} (hM : 0 ≤ M) (h : ∀ t, ∑ i, ‖a t (x i)‖ ^ 2 ≤ M) :
    ∑ i, q (x i) ^ 2 ≤ C ^ 2 * M := by
  have hL : 0 ≤ ∑ i, q (x i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have bound := hAS n (fun i => ((q (x i) : ℝ) : ℂ) • x i) (√((∑ i, q (x i) ^ 2) * M))
    (Real.sqrt_nonneg _) (fun t => by
      calc ∑ i, ‖a t (((q (x i) : ℝ) : ℂ) • x i)‖ = ∑ i, q (x i) * ‖a t (x i)‖ :=
            Finset.sum_congr rfl fun i _ => norm_apply_real_smul _ (apply_nonneg q _) _
        _ ≤ √((∑ i, q (x i) ^ 2) * M) :=
            Real.le_sqrt_of_sq_le ((Finset.univ.sum_mul_sq_le_sq_mul_sq _ _).trans
              (mul_le_mul_of_nonneg_left (h t) hL)))
  have e1 : ∑ i, q (((q (x i) : ℝ) : ℂ) • x i) = ∑ i, q (x i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [seminorm_real_smul q (apply_nonneg q _), pow_two]
  have bound' : ∑ i, q (x i) ^ 2 ≤ C * √((∑ i, q (x i) ^ 2) * M) := e1 ▸ bound
  generalize (∑ i, q (x i) ^ 2) = L at hL bound' ⊢
  by_cases hz : L = 0
  · rw [hz]; positivity
  have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hz)
  have hsq := (sq_le_sq₀ hL (mul_nonneg hC (Real.sqrt_nonneg _))).mpr bound'
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hL hM)] at hsq
  refine le_of_mul_le_mul_left ?_ hLpos
  nlinarith [hsq]

/-- The pointwise quadratic error. -/
noncomputable def cost (C : ℝ) (x : E) (t : Disc T) : ℝ := C ^ 2 * ‖a t x‖ ^ 2 - q x ^ 2

theorem cost_real_smul (C : ℝ) {c : ℝ} (hc : 0 ≤ c) (x : E) (t : Disc T) :
    cost a q C (((√c : ℝ) : ℂ) • x) t = c * cost a q C x t := by
  unfold cost
  rw [norm_apply_real_smul _ (Real.sqrt_nonneg _), seminorm_real_smul q (Real.sqrt_nonneg _),
    mul_pow, mul_pow, Real.sq_sqrt hc]
  ring

/-- The cone of bounded functions dominating a finite sum of pointwise quadratic errors. -/
noncomputable def cone (C : ℝ) : PointedCone ℝ (BoundedContinuousFunction (Disc T) ℝ) where
  carrier := {f | ∃ (n : ℕ) (x : Fin n → E), ∀ t, ∑ i, cost a q C (x i) t ≤ f t}
  zero_mem' := ⟨0, Fin.elim0, fun t => by simp⟩
  add_mem' := by
    rintro f g ⟨n, x, hx⟩ ⟨m, y, hy⟩
    refine ⟨n + m, Fin.append x y, fun t => ?_⟩
    simpa [Fin.sum_univ_add] using add_le_add (hx t) (hy t)
  smul_mem' := by
    rintro ⟨c, hc⟩ f ⟨n, x, hx⟩
    refine ⟨n, fun i => ((√c : ℝ) : ℂ) • x i, fun t => ?_⟩
    simp only [cost_real_smul a q C hc, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hx t) hc

theorem mem_cone_of_nonneg (C : ℝ) (f : BoundedContinuousFunction (Disc T) ℝ)
    (hf : ∀ t, 0 ≤ f t) : f ∈ cone a q C :=
  ⟨0, Fin.elim0, fun t => by simpa using hf t⟩

theorem re_mul_re_add_im_mul_im_self (z : ℂ) : z.re * z.re + z.im * z.im = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]

theorem norm_re_mul_re_add_im_mul_im_le (z w : ℂ) :
    ‖z.re * w.re + z.im * w.im‖ ≤ ‖z‖ * ‖w‖ := by
  have h : z.re * w.re + z.im * w.im = (z * (starRingEnd ℂ) w).re := by
    simp [Complex.mul_re]
  rw [h, Real.norm_eq_abs]
  calc |(z * (starRingEnd ℂ) w).re| ≤ ‖z * (starRingEnd ℂ) w‖ := Complex.abs_re_le_norm _
    _ = ‖z‖ * ‖w‖ := by rw [norm_mul, RCLike.norm_conj]

/-- **Pietsch domination, Hilbertian form.**  If `∑ q₁ (x i) ≤ C * sup_t ∑ |a t (x i)|` for all
finite families and `|a t x| ≤ q₂ x`, then there is a positive semi-definite symmetric real
bilinear form `β` on `E` with `q₁ ^ 2 ≤ C ^ 2 * β` and `β ≤ q₂ ^ 2`. -/
theorem exists_hilbert_form [Nonempty T] (q₁ q₂ : Seminorm ℂ E) {C : ℝ} (hC : 0 < C)
    (hAS : ∀ (n : ℕ) (x : Fin n → E) (M : ℝ), 0 ≤ M → (∀ t, ∑ i, ‖a t (x i)‖ ≤ M) →
      ∑ i, q₁ (x i) ≤ C * M)
    (hb : ∀ t x, ‖a t x‖ ≤ q₂ x) :
    ∃ β : E → E → ℝ, (∀ x y, β x y = β y x) ∧ (∀ x x' y, β (x + x') y = β x y + β x' y) ∧
      (∀ (c : ℝ) x y, β ((c : ℂ) • x) y = c * β x y) ∧ (∀ x, 0 ≤ β x x) ∧
      (∀ x, β x x ≤ q₂ x ^ 2) ∧ (∀ x, q₁ x ^ 2 ≤ C ^ 2 * β x x) := by
  classical
  have hne : Nonempty (Disc T) := ‹Nonempty T›
  obtain ⟨pt⟩ := hne
  let o : BoundedContinuousFunction (Disc T) ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun _ => (1 : ℝ)) 1 (fun _ => by simp)
  have ho : ∀ t, o t = 1 := fun _ => rfl
  let ev : BoundedContinuousFunction (Disc T) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun f => f pt, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let P := ev.toPMap (Submodule.span ℝ {o})
  have hpos : ∀ f : P.domain, (f : BoundedContinuousFunction (Disc T) ℝ) ∈ cone a q₁ C →
      0 ≤ P f := by
    rintro ⟨f, hf⟩ ⟨n, x, hx⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hf
    have hval : ∀ t, (r • o) t = r := fun t => by
      change r • o t = r
      rw [ho, smul_eq_mul, mul_one]
    change 0 ≤ (r • o) pt
    rw [hval]
    by_contra hneg
    rw [not_le] at hneg
    have h1 : ∀ t : Disc T, ∑ i, ‖a t (x i)‖ ^ 2 ≤ (r + ∑ i, q₁ (x i) ^ 2) / C ^ 2 := by
      intro t
      have h := hx t
      simp only at h
      rw [hval] at h
      simp only [cost, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
      rw [le_div_iff₀ (pow_pos hC 2)]
      linarith
    have hM : 0 ≤ (r + ∑ i, q₁ (x i) ^ 2) / C ^ 2 :=
      le_trans (Finset.sum_nonneg fun _ _ => sq_nonneg _) (h1 pt)
    have h2 := sum_sq_le a q₁ hC.le hAS x hM h1
    rw [mul_div_cancel₀ _ (pow_pos hC 2).ne'] at h2
    linarith
  have hmajor : ∀ f : BoundedContinuousFunction (Disc T) ℝ,
      ∃ g : P.domain, (g : BoundedContinuousFunction (Disc T) ℝ) + f ∈ cone a q₁ C := by
    intro f
    refine ⟨⟨‖f‖ • o, Submodule.mem_span_singleton.mpr ⟨‖f‖, rfl⟩⟩,
      mem_cone_of_nonneg a q₁ C _ fun t => ?_⟩
    simp only [BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_smul, Pi.add_apply,
      ho, smul_eq_mul, mul_one]
    have h := f.norm_coe_le_norm t
    rw [Real.norm_eq_abs] at h
    linarith [neg_abs_le (f t)]
  obtain ⟨g, hg, hcone⟩ := riesz_extension (cone a q₁ C) P hpos hmajor
  have hone : g o = 1 := by
    have h := hg ⟨o, Submodule.mem_span_singleton_self _⟩
    exact h
  have hnonneg : ∀ f : BoundedContinuousFunction (Disc T) ℝ, (∀ t, 0 ≤ f t) → 0 ≤ g f :=
    fun f hf => hcone f (mem_cone_of_nonneg a q₁ C f hf)
  let F : E → E → BoundedContinuousFunction (Disc T) ℝ := fun x y =>
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
      (fun t : Disc T => (a t x).re * (a t y).re + (a t x).im * (a t y).im) (q₂ x * q₂ y)
      (fun t => (norm_re_mul_re_add_im_mul_im_le _ _).trans
        (mul_le_mul (hb t x) (hb t y) (norm_nonneg _) (apply_nonneg q₂ x)))
  have hF : ∀ x y t, F x y t = (a t x).re * (a t y).re + (a t x).im * (a t y).im :=
    fun _ _ _ => rfl
  refine ⟨fun x y => g (F x y), fun x y => ?_, fun x x' y => ?_, fun c x y => ?_, fun x => ?_,
    fun x => ?_, fun x => ?_⟩
  · refine congrArg g ?_
    ext t
    rw [hF, hF]
    ring
  · have h : F (x + x') y = F x y + F x' y := by
      ext t
      simp only [hF, BoundedContinuousFunction.coe_add, Pi.add_apply, map_add, Complex.add_re,
        Complex.add_im]
      ring
    change g (F (x + x') y) = g (F x y) + g (F x' y)
    rw [h, map_add]
  · have h : F ((c : ℂ) • x) y = c • F x y := by
      ext t
      simp only [hF, BoundedContinuousFunction.coe_smul, map_smul, smul_eq_mul,
        Complex.re_ofReal_mul, Complex.im_ofReal_mul]
      ring
    change g (F ((c : ℂ) • x) y) = c * g (F x y)
    rw [h, map_smul, smul_eq_mul]
  · refine hnonneg _ fun t => ?_
    rw [hF, re_mul_re_add_im_mul_im_self]
    positivity
  · have h := hnonneg (q₂ x ^ 2 • o - F x x) (fun t => by
      simp only [BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.coe_smul,
        Pi.sub_apply, ho, hF, smul_eq_mul, mul_one, re_mul_re_add_im_mul_im_self, sub_nonneg]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb t x) 2)
    rw [map_sub, map_smul, hone, smul_eq_mul, mul_one, sub_nonneg] at h
    exact h
  · have hmem : C ^ 2 • F x x - q₁ x ^ 2 • o ∈ cone a q₁ C :=
      ⟨1, fun _ => x, fun t => by
        rw [Fin.sum_univ_one]
        simp only [BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.coe_smul,
          Pi.sub_apply, ho, hF, smul_eq_mul, mul_one, re_mul_re_add_im_mul_im_self, cost]
        exact le_refl _⟩
    have h := hcone _ hmem
    rw [map_sub, map_smul, map_smul, hone, smul_eq_mul, smul_eq_mul, mul_one, sub_nonneg] at h
    exact h

end pietsch


section hilbert

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- A positive semi-definite symmetric real bilinear form on the complex vector space `E`. -/
structure IsForm (β : E → E → ℝ) : Prop where
  symm : ∀ x y, β x y = β y x
  add_left : ∀ x x' y, β (x + x') y = β x y + β x' y
  smul_left : ∀ (c : ℝ) x y, β ((c : ℂ) • x) y = c * β x y
  nonneg : ∀ x, 0 ≤ β x x

/-- Orthonormal finite families. -/
def ON (β : E → E → ℝ) {n : ℕ} (e : Fin n → E) : Prop :=
  ∀ i j, β (e i) (e j) = if i = j then 1 else 0

namespace IsForm

variable {β : E → E → ℝ} (hβ : IsForm β)
include hβ

theorem zero_left (y : E) : β 0 y = 0 := by
  have h := hβ.add_left 0 0 y
  rw [add_zero] at h
  linarith

theorem smul_right (c : ℝ) (x y : E) : β x ((c : ℂ) • y) = c * β x y := by
  rw [hβ.symm, hβ.smul_left, hβ.symm]

theorem neg_left (x y : E) : β (-x) y = -β x y := by
  have h := hβ.add_left x (-x) y
  rw [add_neg_cancel, hβ.zero_left] at h
  linarith

theorem sub_left (x x' y : E) : β (x - x') y = β x y - β x' y := by
  rw [sub_eq_add_neg, hβ.add_left, hβ.neg_left]
  ring

theorem sub_right (x y y' : E) : β x (y - y') = β x y - β x y' := by
  rw [hβ.symm, hβ.sub_left, hβ.symm y, hβ.symm y']

theorem sum_left {ι : Type*} (s : Finset ι) (f : ι → E) (y : E) :
    β (∑ i ∈ s, f i) y = ∑ i ∈ s, β (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hβ.zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hβ.add_left, ih]

theorem comb_left {n : ℕ} (e : Fin n → E) (c : Fin n → ℝ) (y : E) :
    β (∑ i, (c i : ℂ) • e i) y = ∑ i, c i * β (e i) y := by
  rw [hβ.sum_left]
  exact Finset.sum_congr rfl fun i _ => hβ.smul_left _ _ _

theorem comb_ortho {n : ℕ} {e : Fin n → E} (hON : ON β e) (c : Fin n → ℝ) (j : Fin n) :
    β (∑ i, (c i : ℂ) • e i) (e j) = c j := by
  rw [hβ.comb_left]
  simp only [hON _ j, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem comb_self {n : ℕ} {e : Fin n → E} (hON : ON β e) (c : Fin n → ℝ) :
    β (∑ i, (c i : ℂ) • e i) (∑ i, (c i : ℂ) • e i) = ∑ i, c i ^ 2 := by
  rw [hβ.comb_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hβ.symm, hβ.comb_ortho hON, pow_two]

/-- Bessel's inequality for a real functional dominated by the form. -/
theorem sum_sq_le_of_orthonormal {n : ℕ} {e : Fin n → E} (hON : ON β e) (ℓ : E → ℝ) (K : ℝ)
    (hℓ : ∀ c : Fin n → ℝ, ℓ (∑ i, (c i : ℂ) • e i) = ∑ i, c i * ℓ (e i))
    (hK : ∀ x, ℓ x ^ 2 ≤ K ^ 2 * β x x) : ∑ i, ℓ (e i) ^ 2 ≤ K ^ 2 := by
  have h1 := hK (∑ i, ((ℓ (e i) : ℝ) : ℂ) • e i)
  rw [hℓ, hβ.comb_self hON] at h1
  have e2 : ∑ i, ℓ (e i) * ℓ (e i) = ∑ i, ℓ (e i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => (pow_two _).symm
  rw [e2] at h1
  have hs : 0 ≤ ∑ i, ℓ (e i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  generalize (∑ i, ℓ (e i) ^ 2) = s at h1 hs ⊢
  by_cases hz : s = 0
  · rw [hz]; positivity
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    refine le_of_mul_le_mul_left ?_ hspos
    nlinarith [h1]

/-- Bessel's inequality for a complex functional dominated by the form. -/
theorem sum_norm_sq_le_of_orthonormal {n : ℕ} {e : Fin n → E} (hON : ON β e) (a : E →ₗ[ℂ] ℂ)
    (K : ℝ) (hK : ∀ x, ‖a x‖ ^ 2 ≤ K ^ 2 * β x x) : ∑ i, ‖a (e i)‖ ^ 2 ≤ 2 * K ^ 2 := by
  have hre := hβ.sum_sq_le_of_orthonormal hON (fun x => (a x).re) K
    (fun c => by
      simp only [map_sum, map_smul, smul_eq_mul, Complex.re_sum, Complex.re_ofReal_mul])
    (fun x => by
      refine le_trans ?_ (hK x)
      nlinarith [re_mul_re_add_im_mul_im_self (a x), mul_self_nonneg (a x).im])
  have him := hβ.sum_sq_le_of_orthonormal hON (fun x => (a x).im) K
    (fun c => by
      simp only [map_sum, map_smul, smul_eq_mul, Complex.im_sum, Complex.im_ofReal_mul])
    (fun x => by
      refine le_trans ?_ (hK x)
      nlinarith [re_mul_re_add_im_mul_im_self (a x), mul_self_nonneg (a x).re])
  have e1 : ∑ i, ‖a (e i)‖ ^ 2 = ∑ i, (a (e i)).re ^ 2 + ∑ i, (a (e i)).im ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← re_mul_re_add_im_mul_im_self]
    ring
  rw [e1]
  linarith

end IsForm

end hilbert


section compact

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {β : E → E → ℝ}

/-- If an orthonormal family `e` cannot be extended by a unit vector `y` with `p y > δ`, then the
unit ball of the form is covered by finitely many `p`-balls of radius `ε > δ`. -/
theorem exists_net (hβ : IsForm β) (p : Seminorm ℂ E) {D : ℝ} (hD : ∀ x, p x ^ 2 ≤ D * β x x)
    {n : ℕ} {e : Fin n → E} (hON : ON β e) {δ ε : ℝ} (hδ : 0 ≤ δ) (hδε : δ < ε)
    (hno : ∀ y, (∀ i, β y (e i) = 0) → β y y = 1 → p y ≤ δ) :
    ∃ S : Finset E, {x | β x x < 1} ⊆ ⋃ y ∈ S, {x | p (x - y) < ε} := by
  classical
  have hsmall : ∀ y, (∀ i, β y (e i) = 0) → β y y ≤ 1 → p y ≤ δ := by
    intro y hy0 hy1
    by_cases h0 : β y y = 0
    · have h := hD y
      rw [h0, mul_zero] at h
      have h' : p y = 0 := (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h (sq_nonneg _))
      rw [h']
      exact hδ
    · have hpos : 0 < β y y := lt_of_le_of_ne (hβ.nonneg y) (Ne.symm h0)
      obtain ⟨s, hspos, hss⟩ : ∃ s : ℝ, 0 < s ∧ s * s = β y y :=
        ⟨√(β y y), Real.sqrt_pos.mpr hpos, Real.mul_self_sqrt hpos.le⟩
      have hsne : s ≠ 0 := hspos.ne'
      have hs1 : s ≤ 1 := by
        by_contra h
        rw [not_le] at h
        nlinarith
      have h1 := hno (((s⁻¹ : ℝ) : ℂ) • y) (fun i => by rw [hβ.smul_left, hy0 i, mul_zero])
        (by rw [hβ.smul_left, hβ.smul_right, ← hss]; field_simp)
      rw [seminorm_real_smul p (inv_nonneg.mpr hspos.le), inv_mul_le_iff₀ hspos] at h1
      nlinarith
  have hSp : 0 ≤ ∑ i, p (e i) := Finset.sum_nonneg fun i _ => apply_nonneg p _
  obtain ⟨η, hη, hηmul⟩ : ∃ η : ℝ, 0 < η ∧ η * (∑ i, p (e i)) + η = ε - δ := by
    refine ⟨(ε - δ) / (∑ i, p (e i) + 1), div_pos (sub_pos.mpr hδε) (by linarith), ?_⟩
    have hne : (∑ i, p (e i) + 1) ≠ 0 := by linarith
    field_simp
  obtain ⟨t, -, htfin, hcover⟩ :=
    (isCompact_univ_pi fun _ : Fin n => isCompact_Icc (a := (-1 : ℝ)) (b := 1)).finite_cover_balls hη
  refine ⟨htfin.toFinset.image (fun c : Fin n → ℝ => ∑ i, (c i : ℂ) • e i), fun x hx => ?_⟩
  have hx1 : β x x < 1 := hx
  obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, ∀ i, c i = β x (e i) := ⟨fun i => β x (e i), fun _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : E, w = ∑ i, (c i : ℂ) • e i := ⟨_, rfl⟩
  have hy0 : ∀ j, β (x - w) (e j) = 0 := fun j => by
    rw [hβ.sub_left, hw, hβ.comb_ortho hON, hc j, sub_self]
  have hwy : β w (x - w) = 0 := by
    rw [hw, hβ.comb_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hβ.symm, ← hw, hy0 i, mul_zero]
  have hxw : β w x = ∑ i, c i ^ 2 := by
    rw [hw, hβ.comb_left]
    exact Finset.sum_congr rfl fun i _ => by rw [hβ.symm (e i) x, ← hc i, pow_two]
  have hyy : β (x - w) (x - w) = β x x - ∑ i, c i ^ 2 := by
    rw [hβ.sub_left x w (x - w), hwy, sub_zero, hβ.sub_right, hβ.symm x w, hxw]
  have hcnn : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (c i)
  have hcsq : ∑ i, c i ^ 2 < 1 := by linarith [hβ.nonneg (x - w)]
  have hpy : p (x - w) ≤ δ := hsmall _ hy0 (by rw [hyy]; linarith)
  have hcmem : c ∈ Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1) := by
    intro i _
    have hi : c i ^ 2 < 1 := lt_of_le_of_lt
      (Finset.single_le_sum (f := fun j => c j ^ 2) (fun j _ => sq_nonneg (c j))
        (Finset.mem_univ i)) hcsq
    have h := abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hi)
    exact ⟨h.1.le, h.2.le⟩
  obtain ⟨c', hc't, hcc'⟩ := Set.mem_iUnion₂.mp (hcover hcmem)
  have hdist : ∀ i, |c i - c' i| < η := fun i => by
    have h := (dist_pi_lt_iff hη).mp (Metric.mem_ball.mp hcc') i
    rwa [Real.dist_eq] at h
  refine Set.mem_iUnion₂.mpr ⟨∑ i, (c' i : ℂ) • e i,
    Finset.mem_image.mpr ⟨c', htfin.mem_toFinset.mpr hc't, rfl⟩, ?_⟩
  change p (x - ∑ i, (c' i : ℂ) • e i) < ε
  have hsplit : x - ∑ i, (c' i : ℂ) • e i = (x - w) + ∑ i, ((c i - c' i : ℝ) : ℂ) • e i := by
    rw [hw]
    simp only [Complex.ofReal_sub, sub_smul, Finset.sum_sub_distrib]
    abel
  rw [hsplit]
  calc p ((x - w) + ∑ i, ((c i - c' i : ℝ) : ℂ) • e i)
      ≤ p (x - w) + p (∑ i, ((c i - c' i : ℝ) : ℂ) • e i) := map_add_le_add p _ _
    _ ≤ δ + ∑ i, |c i - c' i| * p (e i) := by
        refine add_le_add hpy
          ((Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _).trans
          (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)))
        rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ δ + ∑ i, η * p (e i) :=
        add_le_add_right (Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hdist i).le (apply_nonneg p _)) _
    _ = δ + η * ∑ i, p (e i) := by rw [Finset.mul_sum]
    _ < ε := by linarith

/-- An absolutely summing map out of a (semi-)Hilbert space is precompact: the unit ball of the
form `β` is totally bounded for `p`. -/
theorem totallyBounded_of_form (hβ : IsForm β) {T : Type*} (a : T → E →ₗ[ℂ] ℂ)
    (p : Seminorm ℂ E) {C K : ℝ} (hC : 0 ≤ C)
    (hAS : ∀ (n : ℕ) (x : Fin n → E) (M : ℝ), 0 ≤ M → (∀ t, ∑ i, ‖a t (x i)‖ ≤ M) →
      ∑ i, p (x i) ≤ C * M)
    (hK : ∀ t x, ‖a t x‖ ^ 2 ≤ K ^ 2 * β x x) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset E, {x | β x x < 1} ⊆ ⋃ y ∈ S, {x | p (x - y) < ε} := by
  have hD : ∀ x, p x ^ 2 ≤ C ^ 2 * K ^ 2 * β x x := fun x => by
    have h := sum_sq_le a p hC hAS (fun _ : Fin 1 => x)
      (mul_nonneg (sq_nonneg K) (hβ.nonneg x)) (fun t => by rw [Fin.sum_univ_one]; exact hK t x)
    rw [Fin.sum_univ_one] at h
    linarith [h]
  have hδ : 0 < ε / 2 := half_pos hε
  have main : ∀ n : ℕ, (∃ e : Fin n → E, ON β e ∧ ∀ i, ε / 2 < p (e i)) ∨
      ∃ S : Finset E, {x | β x x < 1} ⊆ ⋃ y ∈ S, {x | p (x - y) < ε} := by
    intro n
    induction n with
    | zero => exact Or.inl ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ n ih =>
      rcases ih with ⟨e, hON, he⟩ | h
      · by_cases hex : ∃ y, (∀ i, β y (e i) = 0) ∧ β y y = 1 ∧ ε / 2 < p y
        · obtain ⟨y, hy0, hy1, hyp⟩ := hex
          refine Or.inl ⟨Fin.cons y e, ?_, ?_⟩
          · intro i j
            induction i using Fin.cases with
            | zero =>
              induction j using Fin.cases with
              | zero => simp [hy1]
              | succ j => simp [hy0 j, (Fin.succ_ne_zero j).symm]
            | succ i =>
              induction j using Fin.cases with
              | zero => simp [hβ.symm (e i) y, hy0 i, Fin.succ_ne_zero]
              | succ j => simp [hON i j]
          · intro i
            induction i using Fin.cases with
            | zero => simpa using hyp
            | succ i => simpa using he i
        · refine Or.inr (exists_net hβ p hD hON hδ.le (half_lt_self hε) fun y h0 h1 => ?_)
          by_contra hcon
          exact hex ⟨y, h0, h1, not_le.mp hcon⟩
      · exact Or.inr h
  obtain ⟨n, hn⟩ := exists_nat_gt (C ^ 2 * (2 * K ^ 2) / (ε / 2) ^ 2)
  rcases main n with ⟨e, hON, he⟩ | h
  · exfalso
    have h1 : ∑ i, p (e i) ^ 2 ≤ C ^ 2 * (2 * K ^ 2) :=
      sum_sq_le a p hC hAS e (by positivity)
        (fun t => hβ.sum_norm_sq_le_of_orthonormal hON (a t) K (hK t))
    have h2 : (n : ℝ) * (ε / 2) ^ 2 ≤ ∑ i, p (e i) ^ 2 := by
      calc (n : ℝ) * (ε / 2) ^ 2 = ∑ _i : Fin n, (ε / 2) ^ 2 := by simp
        _ ≤ ∑ i, p (e i) ^ 2 :=
            Finset.sum_le_sum fun i _ => pow_le_pow_left₀ hδ.le (he i).le 2
    rw [div_lt_iff₀ (pow_pos hδ 2)] at hn
    linarith
  · exact h

end compact

end Sol_MasulloGRH_isSchwartzLCS_of_isNuclear

open MasulloGRH Sol_MasulloGRH_isSchwartzLCS_of_isNuclear

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hN : IsNuclear E) : IsSchwartzLCS E := by
  refine ⟨hN.1.1, fun p hp => ?_⟩
  obtain ⟨q₁, A₁, C₁, hq₁, hC₁, hA₁, hAS₁⟩ := exists_absolutelySumming hN p hp
  obtain ⟨q₂, A₂, C₂, hq₂, hC₂, hA₂, hAS₂⟩ := exists_absolutelySumming hN q₁ hq₁
  refine ⟨q₂.ball 0 1, q₂.ball_mem_nhds hq₂ one_pos, fun ε hε => ?_⟩
  -- the second family of functionals, made nonempty by adjoining `0`
  let a₂ : ↥(insert (0 : StrongDual ℂ E) A₂) → E →ₗ[ℂ] ℂ :=
    fun t => ((t : StrongDual ℂ E) : E →ₗ[ℂ] ℂ)
  have hne : Nonempty ↥(insert (0 : StrongDual ℂ E) A₂) := ⟨⟨0, Set.mem_insert _ _⟩⟩
  have hb₂ : ∀ t x, ‖a₂ t x‖ ≤ q₂ x := by
    rintro ⟨t, ht⟩ x
    rcases ht with rfl | ht
    · change ‖(0 : StrongDual ℂ E) x‖ ≤ q₂ x
      rw [show (0 : StrongDual ℂ E) x = 0 from rfl, norm_zero]
      exact apply_nonneg q₂ x
    · exact hA₂ t ht x
  have hAS₂' : ∀ (n : ℕ) (x : Fin n → E) (M : ℝ), 0 ≤ M → (∀ t, ∑ i, ‖a₂ t (x i)‖ ≤ M) →
      ∑ i, q₁ (x i) ≤ C₂ * M :=
    fun n x M hM h => hAS₂ n x M hM fun a ha => h ⟨a, Set.mem_insert_of_mem _ ha⟩
  obtain ⟨β, hsymm, hadd, hsmul, hnn, hle, hdom⟩ :=
    exists_hilbert_form a₂ q₁ q₂ hC₂ hAS₂' hb₂
  have hβ : IsForm β := ⟨hsymm, hadd, hsmul, hnn⟩
  -- the first family of functionals
  let a₁ : ↥A₁ → E →ₗ[ℂ] ℂ := fun t => ((t : StrongDual ℂ E) : E →ₗ[ℂ] ℂ)
  have hK : ∀ t x, ‖a₁ t x‖ ^ 2 ≤ C₂ ^ 2 * β x x := fun t x =>
    (pow_le_pow_left₀ (norm_nonneg _) (hA₁ t t.2 x) 2).trans (hdom x)
  have hAS₁' : ∀ (n : ℕ) (x : Fin n → E) (M : ℝ), 0 ≤ M → (∀ t, ∑ i, ‖a₁ t (x i)‖ ≤ M) →
      ∑ i, p (x i) ≤ C₁ * M :=
    fun n x M hM h => hAS₁ n x M hM fun a ha => h ⟨a, ha⟩
  obtain ⟨S, hS⟩ := totallyBounded_of_form hβ a₁ p hC₁.le hAS₁' hK hε
  refine ⟨S, fun x hx => hS ?_⟩
  have hx' : q₂ x < 1 := by
    rw [Seminorm.mem_ball_zero] at hx
    exact hx
  change β x x < 1
  calc β x x ≤ q₂ x ^ 2 := hle x
    _ < 1 := by nlinarith [apply_nonneg q₂ x]
