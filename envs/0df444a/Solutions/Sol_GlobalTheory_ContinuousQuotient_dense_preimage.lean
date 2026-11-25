-- Prove2me | solution 1 for GlobalTheory.ContinuousQuotient.dense_preimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:30:55.177098+00:00
-- url     : https://prove2.me/submissions/d56e656e-fb61-4250-8ccd-fab5ee784a27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfForallAlgHomComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEqMulOfContinuousOnQuotient
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Topology
namespace GlobalTheory.ContinuousQuotient
private theorem valAt'_ne_zero_iff_top_le_preimage_basicOpen {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U : X.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valAt' x U f ≠ 0 ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen f := by
  have hv : valAt' x U f = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((x.appLE U ⊤ h).hom f) := by
    simp only [valAt', dif_pos h, valAt]
  have hb : x ⁻¹ᵁ X.basicOpen f = (Sp ℂ).basicOpen ((x.appLE U ⊤ h).hom f) := by
    rw [Scheme.preimage_basicOpen]
    have := (Sp ℂ).basicOpen_res (x.app U f) (homOfLE h).op
    rw [top_inf_eq] at this
    rw [← this]
    rfl
  rw [hv, hb]
  constructor
  · intro h0
    refine le_of_eq (Scheme.basicOpen_of_isUnit _ ?_).symm
    have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((x.appLE U ⊤ h).hom f)) :=
      isUnit_iff_ne_zero.2 h0
    simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  · intro h1 h0
    have hz : (x.appLE U ⊤ h).hom f = 0 := by
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom h0
      simpa using this
    rw [hz, Scheme.basicOpen_zero] at h1
    obtain ⟨pt⟩ : Nonempty (Sp ℂ) := inferInstance
    exact (h1 (show pt ∈ (⊤ : (Sp ℂ).Opens) from trivial)).elim
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
end GlobalTheory.ContinuousQuotient
namespace GlobalTheory
end GlobalTheory
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Topology
open GlobalTheory GlobalTheory.ContinuousQuotient
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.ContinuousQuotient
theorem _root_.solution (W : A.left.Opens) (hW : ∃ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ W) :
    Dense {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ W} := by
  classical
  set V : Set (Fin g → ℂ) := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ W} with hVdef
  obtain ⟨pt⟩ : Nonempty (Sp ℂ) := inferInstance
  have hpt : ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X) (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x.base pt ∈ U := by
    intro X x U
    constructor
    · intro h
      exact h (show pt ∈ (⊤ : (Sp ℂ).Opens) from trivial)
    · intro h q _
      rw [Subsingleton.elim q pt]
      exact h
  by_contra hnd
  set F := closure V with hF
  have hFne : F ≠ Set.univ := fun h => hnd (dense_iff_closure_eq.2 h)
  have hFn : F.Nonempty := by
    obtain ⟨z, hz⟩ := hW
    exact ⟨z, subset_closure hz⟩

  obtain ⟨zs, hzs⟩ : (frontier F).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h0
    rcases isClopen_iff.1 (isClopen_iff_frontier_eq_empty.2 h0) with h1 | h1
    · exact hFn.ne_empty h1
    · exact hFne h1
  rw [isClosed_closure.frontier_eq] at hzs
  obtain ⟨hzsF, hzsi⟩ := hzs

  obtain ⟨U0, hU0a, hxU0, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens A.left)
    (show (u.ex zs).left.base pt ∈ (⊤ : A.left.Opens) from trivial)
  have hU0 : IsAffineOpen U0 := hU0a
  have hV0o : IsOpen {z : Fin g → ℂ | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U0} := (u.8 U0 0).1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV0o zs ((hpt _ _ _).2 hxU0)
  obtain ⟨z1, hz1V, hz1d⟩ := Metric.mem_closure_iff.1 hzsF ε hε
  have hz1b : z1 ∈ Metric.ball zs ε := by rw [Metric.mem_ball, dist_comm]; exact hz1d
  obtain ⟨z0, hz0b, hz0F⟩ : ∃ z0 ∈ Metric.ball zs ε, z0 ∉ F := by
    by_contra hno
    push Not at hno
    exact hzsi (mem_interior.2 ⟨Metric.ball zs ε, hno, Metric.isOpen_ball, Metric.mem_ball_self hε⟩)
  obtain ⟨δ, hδ, hδb⟩ := Metric.isOpen_iff.1
    (isClosed_closure.isOpen_compl.inter Metric.isOpen_ball) z0 ⟨hz0F, hz0b⟩

  have hx1 : (u.ex z1).left.base pt ∈ W ⊓ U0 := ⟨(hpt _ _ _).1 hz1V, (hpt _ _ _).1 (hball hz1b)⟩
  obtain ⟨f, hfW, hf1⟩ := hU0.exists_basicOpen_le (V := W ⊓ U0) ⟨_, hx1⟩ hx1.2
  have hf1' : valAt' (u.ex z1).left U0 f ≠ 0 :=
    (valAt'_ne_zero_iff_top_le_preimage_basicOpen _ (hball hz1b) f).2 ((hpt _ _ _).2 hf1)
  have hf0 : ∀ z ∈ Metric.ball z0 δ, valAt' (u.ex z).left U0 f = 0 := by
    intro z hz
    obtain ⟨hzF, hzb⟩ := hδb hz
    by_contra hne
    have h1 := (valAt'_ne_zero_iff_top_le_preimage_basicOpen _ (hball hzb) f).1 hne
    exact hzF (subset_closure ((hpt _ _ _).2 (hfW ((hpt _ _ _).1 h1)).1))

  let ℓ : ℂ → (Fin g → ℂ) := fun t => z0 + t • (z1 - z0)
  have hℓd : Differentiable ℂ ℓ := by fun_prop
  let T : Set ℂ := ℓ ⁻¹' Metric.ball zs ε
  have hTo : IsOpen T := Metric.isOpen_ball.preimage hℓd.continuous
  have hTc : Convex ℝ T := by
    intro t₁ h₁ t₂ h₂ α β hα hβ hαβ
    have hc := convex_ball zs ε h₁ h₂ hα hβ hαβ
    have hαβ' : (α : ℂ) + (β : ℂ) = 1 := by exact_mod_cast hαβ
    change ℓ (α • t₁ + β • t₂) ∈ Metric.ball zs ε
    convert hc using 1
    ext i
    simp only [ℓ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.real_smul]
    linear_combination (-(z0 i)) * hαβ'
  have hℓ0 : ℓ 0 = z0 := by simp [ℓ]
  have hℓ1 : ℓ 1 = z1 := by simp [ℓ]
  have h0T : (0 : ℂ) ∈ T := by
    change ℓ 0 ∈ Metric.ball zs ε
    rw [hℓ0]; exact hz0b
  let h : ℂ → ℂ := fun t => valAt' (u.ex (ℓ t)).left U0 f
  have hd : DifferentiableOn ℂ h T :=
    (u.8 U0 f).2.comp hℓd.differentiableOn (fun t ht => hball ht)
  have hev : h =ᶠ[nhds 0] 0 := by
    have hmem : ℓ ⁻¹' Metric.ball z0 δ ∈ nhds (0 : ℂ) :=
      hℓd.continuous.continuousAt.preimage_mem_nhds (by rw [hℓ0]; exact Metric.ball_mem_nhds z0 hδ)
    filter_upwards [hmem] with t ht
    exact hf0 _ ht
  have hzero := (hd.analyticOnNhd hTo).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hTc.isPreconnected h0T hev
  have h1T : (1 : ℂ) ∈ T := by
    change ℓ 1 ∈ Metric.ball zs ε
    rw [hℓ1]; exact hz1b
  apply hf1'
  have := hzero h1T
  simp only [h, hℓ1, Pi.zero_apply] at this
  exact this
end GlobalTheory.ContinuousQuotient
