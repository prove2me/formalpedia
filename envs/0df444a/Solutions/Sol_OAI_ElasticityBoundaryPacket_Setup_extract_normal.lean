-- Prove2me | solution 1 for OAI.ElasticityBoundaryPacket.Setup.extract_normal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:09:17.599314+00:00
-- url     : https://prove2.me/submissions/c303930e-283a-440f-96ee-97ebc82fbc56

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El004
import Theorems.Thm_OAI_ElasticityBoundaryMixedScaling_mixedEnergy_limit
import Theorems.Thm_OAI_ElasticityBoundaryPacket_Setup_energy_chart
import Theorems.Thm_OAI_ElasticityBoundaryPacket_Setup_packet

section
-- module Solutions.OAIQ6_Elast.Elasticity_Extension
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter Metric
open scoped Topology Manifold
namespace ElasticityBoundary
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma compact_smooth_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K⊆U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ⊆U ∧
      (∀ᶠ x in 𝓝ˢ K, χ x=1) ∧ ∀ x, χ x∈Icc 0 1 := by
  obtain ⟨R,hR⟩ := hK.isBounded.subset_ball (0 : E)
  obtain ⟨V,hV,hKV,hVU⟩ := normal_exists_closure_subset hK.isClosed (hU.inter isOpen_ball)
    (show K⊆U∩ball (0 : E) R from fun x hx => ⟨hKU hx,hR hx⟩)
  obtain ⟨χ,hχ,hzero,hb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,E)) (n := (⊤ : ℕ∞)) hK.isClosed (by rwa [hV.interior_eq])
  have hs : tsupport (χ : E → ℝ)⊆closure V := by
    apply closure_mono
    intro x hx
    by_contra hn
    exact hx (hzero x hn)
  refine ⟨χ,χ.contMDiff.contDiff,?_,fun x hx => (hVU (hs hx)).1,hχ,hb⟩
  apply (isCompact_closedBall (0 : E) R).of_isClosed_subset (isClosed_tsupport χ)
  exact fun x hx => ball_subset_closedBall ((hVU (hs hx)).2)

end ElasticityBoundary

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryCharts
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! The boundary-coordinate differential operator is obtained from literal
physical elasticity by the chain rule and a fixed Euclidean rotation. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryChartOperator
open ElasticityBoundaryChainRule ElasticityBoundaryPullback ElasticityBoundaryRotation
  ElasticityBoundaryFrameOperator ElasticityBoundaryPhysicalStrong
  ElasticityBoundarySmoothOperator ElasticityBoundaryLayerOperator ElasticityBoundaryStrongLayer

lemma smooth_jac {ψ : X → Y} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (v : X) (α : I) :
    ContDiff ℝ (⊤ : ℕ∞) (jac ψ v α) := by
  exact contDiff_apply ℝ ℝ α |>.comp ((hψ.fderiv_right (by simp)).clm_apply contDiff_const)

lemma smooth_chartPrincipal (Q : X ≃ₗᵢ[ℝ] X) {Φ : Y → X} {ψ : X → Y}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (s α r β : I) : ContDiff ℝ (⊤ : ℕ∞) (chartPrincipal Q Φ ψ l m s α r β) := by
  apply ContDiff.comp _ hΦ
  apply ContDiff.sum; intro k _
  apply ContDiff.sum; intro v _
  apply ContDiff.mul
  · apply ContDiff.mul
    · apply ContDiff.sum; intro i _
      apply ContDiff.sum; intro j _
      apply ContDiff.mul _ contDiff_const
      apply ContDiff.mul contDiff_const
      unfold coeff elasticityTensor
      exact (hl.mul contDiff_const |>.mul contDiff_const).add (hm.mul contDiff_const)
    · exact Complex.ofRealCLM.contDiff.comp (smooth_jac hψ (basis k) α)
  · exact Complex.ofRealCLM.contDiff.comp (smooth_jac hψ (basis v) β)

end ElasticityBoundaryChartOperator

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryParametrix
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Cut off actual boundary fields. The complete product-rule residual is
retained; its derivatives are flat at the concentration point. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ElasticityBoundaryCutoffLayer
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundarySmoothOperator ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryScaling ElasticityBoundaryLayerOperator
  ElasticityBoundaryWeights ElasticityBoundaryStrongLayer ElasticityBoundaryOrderBound
  ElasticityBoundaryCutoffBound

lemma smooth_dpart {f : Y → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (dpart f j) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

end ElasticityBoundaryCutoffLayer

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Variational
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X} {lam mu : X → ℝ}

lemma jetEnergy_symm (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u v : JetH Ω) : jetEnergy hl hm u v=jetEnergy hl hm v u := by
  rw [jetEnergy_integral,jetEnergy_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    have hs : (∑ i, ∑ j, jetStrain Ω i j u x*jetStrain Ω i j v x)=
        ∑ i, ∑ j, jetStrain Ω i j v x*jetStrain Ω i j u x := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    dsimp only
    rw [hs]
    ring)

lemma energy_symm (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u v : H1 Ω) : energy Ω lam mu u v=energy Ω lam mu v u := by
  have h := jetEnergy_symm hl hm ((h1Equiv Ω).symm u).val ((h1Equiv Ω).symm v).val
  rwa [jetEnergy_eq_energy,jetEnergy_eq_energy,Equiv.apply_symm_apply,
    Equiv.apply_symm_apply] at h

lemma energy_eq_of_sameTrace (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    {u v w : H1 Ω} (hu : WeakSolution Ω lam mu u) (hvw : SameTrace Ω v w) :
    energy Ω lam mu u v=energy Ω lam mu u w := by
  let u' := (h1Equiv Ω).symm u
  let v' := (h1Equiv Ω).symm v
  let w' := (h1Equiv Ω).symm w
  have ht : v'.val-w'.val ∈ H10Hilbert Ω :=
    (sameTrace_h1Equiv v' w').mp (by simpa only [v',w',Equiv.apply_symm_apply] using hvw)
  have he := (weakSolution_h1Equiv hl hm u').mp (by
    simpa only [u',Equiv.apply_symm_apply] using hu) ⟨v'.val-w'.val,ht⟩
  change jetEnergy hl hm u'.val (v'.val-w'.val)=0 at he
  rw [map_sub] at he
  have hv' := jetEnergy_eq_energy hl hm u' v'
  have hw' := jetEnergy_eq_energy hl hm u' w'
  simp only [u',v',w',Equiv.apply_symm_apply] at hv' hw'
  rw [hv',hw'] at he
  exact sub_eq_zero.mp he

lemma DN_eq_energy (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (f : BoundaryData Ω) (v : H1 Ω) :
    DN Ω lam mu f (trace Ω v)=energy Ω lam mu (dirichletSolution Ω lam mu f) v := by
  apply energy_eq_of_sameTrace (ha.1.boundedCoefficient hO hB)
    (ha.2.1.boundedCoefficient hO hB) (dirichletSolution_spec ha hO hB f).2
  apply (trace_eq_iff _ _).mp
  exact Quot.out_eq (trace Ω v)

end Elasticity

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryPackets
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Literal first derivatives of the compact physical trial and their exact
rotated chart expression. No trace reconstruction is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryGradientTransfer
open ElasticityBoundaryPhysicalMass ElasticityBoundaryPhysicalTransfer ElasticityBoundaryForceSupport
  ElasticityBoundaryChartMass ElasticityBoundaryChartOperator ElasticityBoundaryFrameOperator
  ElasticityBoundaryRotation ElasticityBoundaryFrameInverse ElasticityBoundaryOperatorLocal
  ElasticityBoundaryChainRule ElasticityBoundaryStrongLayer ElasticityBoundaryCompactMatrix

lemma dpart_support_lifted {f : Y → ℂ} {K : Set X} (hK : IsClosed K)
    (hf : Function.support (fun z : X => f z.ofLp)⊆K) (α : I) :
    Function.support (fun z : X => dpart f α z.ofLp)⊆K := by
  have hcl : IsClosed {y : Y | WithLp.toLp 2 y∈K} :=
    hK.preimage (PiLp.continuous_toLp 2 (fun _ : I => ℝ))
  have hs : Function.support f⊆{y : Y | WithLp.toLp 2 y∈K} := by
    intro y hy
    exact hf hy
  intro x hx
  exact closure_minimal hs hcl (tsupport_fderiv_apply_subset ℝ (Pi.single α 1) (subset_tsupport _ hx))

end ElasticityBoundaryGradientTransfer

end
end
section
/-!
Exact physical-DN remainder identity needed for boundary high-frequency tests.
All objects below use the physical energy and full trace quotient.
There are no additional main hypotheses; the estimates hold for any trial field.
-/
noncomputable section
open Set MeasureTheory
namespace Elasticity
variable {Ω : Set X} {lam mu : X → ℝ}

lemma physicalProjection_weak (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (u : H1Hilbert Ω) :
    WeakSolution Ω lam mu (h1Equiv Ω (physicalProjection (lam := lam) (mu := mu) u)) := by
  simpa only [physicalProjection, Equiv.apply_symm_apply] using
    (dirichletSolution_spec ha hO hB (trace Ω (h1Equiv Ω u))).2

lemma error_residual (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (u : H1Hilbert Ω) (v : H10Hilbert Ω) :
    zeroTraceEnergy (ha.1.boundedCoefficient hO hB) (ha.2.1.boundedCoefficient hO hB)
      (physicalError ha hO hB u) v =
      physicalResidual (ha.1.boundedCoefficient hO hB) (ha.2.1.boundedCoefficient hO hB) u v := by
  let hl := ha.1.boundedCoefficient hO hB
  let hm := ha.2.1.boundedCoefficient hO hB
  have hw := (weakSolution_h1Equiv hl hm _).mp (physicalProjection_weak ha hO hB u) v
  change jetEnergy hl hm (u.val - (physicalProjection (lam := lam) (mu := mu) u).val)
    v.val = jetEnergy hl hm u.val v.val
  rw [map_sub, sub_apply, hw, sub_zero]

/-- Coercivity gives a uniform correction bound in the honest Hilbert norm. -/
theorem physicalError_bound (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : H1Hilbert Ω,
      ‖physicalError ha hO hB u‖ ≤
      ‖physicalResidual (ha.1.boundedCoefficient hO hB) (ha.2.1.boundedCoefficient hO hB) u‖ / c := by
  obtain ⟨c, hc, hco⟩ := physical_coercive ha hO hB
  refine ⟨c, hc, ?_⟩
  intro u
  let e := physicalError ha hO hB u
  let r := physicalResidual (ha.1.boundedCoefficient hO hB)
    (ha.2.1.boundedCoefficient hO hB) u
  have h1 : c * ‖e‖ * ‖e‖ ≤ r e := by
    simpa only [e, r, error_residual] using hco e
  have h2 : r e ≤ ‖r‖ * ‖e‖ := (le_abs_self _).trans (r.le_opNorm e)
  by_cases he : ‖e‖ = 0
  · change ‖e‖ ≤ ‖r‖ / c
    rw [he]
    positivity
  · have he' : 0 < ‖e‖ := lt_of_le_of_ne (norm_nonneg e) (Ne.symm he)
    have hh : c * ‖e‖ ≤ ‖r‖ := (mul_le_mul_iff_left₀ he').mp (h1.trans h2)
    exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hh)

/-- Exact error identity for the bilinear full physical DN pairing. -/
theorem DN_quasimode_identity (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (u v : H1Hilbert Ω) :
    energy Ω lam mu (h1Equiv Ω u) (h1Equiv Ω v) -
      DN Ω lam mu (trace Ω (h1Equiv Ω u)) (trace Ω (h1Equiv Ω v)) =
      zeroTraceEnergy (ha.1.boundedCoefficient hO hB) (ha.2.1.boundedCoefficient hO hB)
        (physicalError ha hO hB u) (physicalError ha hO hB v) := by
  let hl := ha.1.boundedCoefficient hO hB
  let hm := ha.2.1.boundedCoefficient hO hB
  let U := physicalProjection (lam := lam) (mu := mu) u
  let V := physicalProjection (lam := lam) (mu := mu) v
  have hw := (weakSolution_h1Equiv hl hm V).mp (physicalProjection_weak ha hO hB v)
    (physicalError ha hO hB u)
  have he : jetEnergy hl hm (u.val - U.val) V.val = 0 := by
    rw [jetEnergy_symm]
    exact hw
  rw [DN_eq_energy ha hO hB]
  have hU : dirichletSolution Ω lam mu (trace Ω (h1Equiv Ω u)) = h1Equiv Ω U :=
    (Equiv.apply_symm_apply _ _).symm
  rw [hU, ← jetEnergy_eq_energy hl hm u v, ← jetEnergy_eq_energy hl hm U v]
  change jetEnergy hl hm u.val v.val - jetEnergy hl hm U.val v.val =
    jetEnergy hl hm (u.val - U.val) (v.val - V.val)
  have hsub : jetEnergy hl hm (u.val - U.val) v.val =
      jetEnergy hl hm u.val v.val - jetEnergy hl hm U.val v.val := by
    exact congrArg (fun f : JetH Ω →L[ℝ] ℝ => f v.val)
      ((jetEnergy hl hm).map_sub u.val U.val)
  rw [map_sub (jetEnergy hl hm (u.val - U.val)) v.val V.val, he, sub_zero]
  exact hsub.symm

end Elasticity

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryData
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Elasticity

section
/-! Mixed physical quasimodes. Unlike a quadratic same-system remainder,
this controls the coefficient-difference energy of a trial for each system.
It is the precise physical-DN bridge for the normal-jet induction. -/
open Set MeasureTheory
variable {Ω : Set X} {lam mu : X → ℝ}

lemma DN_trace_symm (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (u v : H1Hilbert Ω) :
    DN Ω lam mu (trace Ω (h1Equiv Ω u)) (trace Ω (h1Equiv Ω v)) =
      DN Ω lam mu (trace Ω (h1Equiv Ω v)) (trace Ω (h1Equiv Ω u)) := by
  have huv := DN_quasimode_identity ha hO hB u v
  have hvu := DN_quasimode_identity ha hO hB v u
  have he := energy_symm (ha.1.boundedCoefficient hO hB)
    (ha.2.1.boundedCoefficient hO hB) (h1Equiv Ω u) (h1Equiv Ω v)
  have hz : zeroTraceEnergy (ha.1.boundedCoefficient hO hB)
      (ha.2.1.boundedCoefficient hO hB) (physicalError ha hO hB u)
        (physicalError ha hO hB v) =
      zeroTraceEnergy (ha.1.boundedCoefficient hO hB)
      (ha.2.1.boundedCoefficient hO hB) (physicalError ha hO hB v)
        (physicalError ha hO hB u) := jetEnergy_symm _ _ _ _
  linarith

lemma DN_one_sided_error (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (u v : H1Hilbert Ω) :
    energy Ω lam mu (h1Equiv Ω u) (h1Equiv Ω v) -
      DN Ω lam mu (trace Ω (h1Equiv Ω u)) (trace Ω (h1Equiv Ω v)) =
      jetEnergy (ha.1.boundedCoefficient hO hB) (ha.2.1.boundedCoefficient hO hB)
        (physicalError ha hO hB u).val v.val := by
  let U := physicalProjection (lam := lam) (mu := mu) u
  let hl := ha.1.boundedCoefficient hO hB
  let hm := ha.2.1.boundedCoefficient hO hB
  rw [DN_eq_energy ha hO hB]
  have hU : dirichletSolution Ω lam mu (trace Ω (h1Equiv Ω u)) = h1Equiv Ω U :=
    (Equiv.apply_symm_apply _ _).symm
  rw [hU, ← jetEnergy_eq_energy hl hm u v, ← jetEnergy_eq_energy hl hm U v]
  exact (congrArg (fun f : JetH Ω →L[ℝ] ℝ => f v.val)
    ((jetEnergy hl hm).map_sub u.val U.val)).symm

lemma mixed_error_identity {l₁ m₁ l₂ m₂ : X → ℝ}
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hDN : DN Ω l₁ m₁ = DN Ω l₂ m₂) (u v : H1Hilbert Ω) :
    energy Ω l₁ m₁ (h1Equiv Ω u) (h1Equiv Ω v) -
      energy Ω l₂ m₂ (h1Equiv Ω u) (h1Equiv Ω v) =
    jetEnergy (ha₁.1.boundedCoefficient hO hB) (ha₁.2.1.boundedCoefficient hO hB)
      (physicalError ha₁ hO hB u).val v.val -
    jetEnergy (ha₂.1.boundedCoefficient hO hB) (ha₂.2.1.boundedCoefficient hO hB)
      u.val (physicalError ha₂ hO hB v).val := by
  have h₁ := DN_one_sided_error ha₁ hO hB u v
  have h₂ := DN_one_sided_error ha₂ hO hB v u
  rw [energy_symm (ha₂.1.boundedCoefficient hO hB)
      (ha₂.2.1.boundedCoefficient hO hB), DN_trace_symm ha₂ hO hB v u,
      jetEnergy_symm] at h₂
  rw [hDN] at h₁
  linarith

/-- Equal physical DN maps control the *same mixed fields* in the two
coefficient energies, using only the residual in its own system. -/
theorem equal_DN_mixed_quasimode_bound {l₁ m₁ l₂ m₂ : X → ℝ}
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hDN : DN Ω l₁ m₁ = DN Ω l₂ m₂) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ u v : H1Hilbert Ω,
      |energy Ω l₁ m₁ (h1Equiv Ω u) (h1Equiv Ω v) -
        energy Ω l₂ m₂ (h1Equiv Ω u) (h1Equiv Ω v)| ≤
      C₁ * ‖physicalResidual (ha₁.1.boundedCoefficient hO hB)
        (ha₁.2.1.boundedCoefficient hO hB) u‖ * ‖v‖ +
      C₂ * ‖u‖ * ‖physicalResidual (ha₂.1.boundedCoefficient hO hB)
        (ha₂.2.1.boundedCoefficient hO hB) v‖ := by
  obtain ⟨c₁, hc₁, hb₁⟩ := physicalError_bound ha₁ hO hB
  obtain ⟨c₂, hc₂, hb₂⟩ := physicalError_bound ha₂ hO hB
  let E₁ := jetEnergy (ha₁.1.boundedCoefficient hO hB) (ha₁.2.1.boundedCoefficient hO hB)
  let E₂ := jetEnergy (ha₂.1.boundedCoefficient hO hB) (ha₂.2.1.boundedCoefficient hO hB)
  refine ⟨(‖E₁‖+1)/c₁, (‖E₂‖+1)/c₂, by positivity, by positivity, ?_⟩
  intro u v
  rw [mixed_error_identity ha₁ ha₂ hO hB hDN]
  let r₁ := physicalResidual (ha₁.1.boundedCoefficient hO hB)
    (ha₁.2.1.boundedCoefficient hO hB) u
  let r₂ := physicalResidual (ha₂.1.boundedCoefficient hO hB)
    (ha₂.2.1.boundedCoefficient hO hB) v
  have h₁ : |E₁ (physicalError ha₁ hO hB u).val v.val| ≤
      ((‖E₁‖+1)/c₁) * ‖r₁‖ * ‖v‖ := by
    calc
      _ ≤ ‖E₁‖ * ‖physicalError ha₁ hO hB u‖ * ‖v‖ := E₁.le_opNorm₂ _ _
      _ ≤ (‖E₁‖+1) * (‖r₁‖/c₁) * ‖v‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (by linarith) (hb₁ u) (by positivity) (by positivity))
          (norm_nonneg v)
      _ = _ := by ring
  have h₂ : |E₂ u.val (physicalError ha₂ hO hB v).val| ≤
      ((‖E₂‖+1)/c₂) * ‖u‖ * ‖r₂‖ := by
    calc
      _ ≤ ‖E₂‖ * ‖u‖ * ‖physicalError ha₂ hO hB v‖ := E₂.le_opNorm₂ _ _
      _ ≤ ((‖E₂‖+1) * ‖u‖) * (‖r₂‖/c₂) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg u))
          (hb₂ v) (by positivity) (by positivity)
      _ = _ := by ring
  exact (abs_sub _ _).trans (add_le_add h₁ h₂)

end
/-! Complex boundary tests use only the real physical DN map. The following
is derived from four real identities; no equality of an augmented or assumed
complex DN map is introduced. -/
open Set
variable {Ω : Set X}

lemma norm_complex_four (a b c d : ℝ) :
    ‖(a:ℂ)+b+Complex.I*((c:ℂ)-d)‖≤|a|+|b|+|c|+|d| := by
  calc
    _ ≤ ‖(a:ℂ)+b‖+‖Complex.I*((c:ℂ)-d)‖ := norm_add_le _ _
    _ ≤ (‖(a:ℂ)‖+‖(b:ℂ)‖)+(‖(c:ℂ)‖+‖(d:ℂ)‖) := by
      rw [norm_mul,Complex.norm_I,one_mul]
      exact add_le_add (norm_add_le _ _) (norm_sub_le _ _)
    _ = _ := by simp only [Complex.norm_real,Real.norm_eq_abs]; ring

/-- Genuine sesquilinear mixed energy from equality of the real physical DN
maps. Each of the four trial components may have its own arbitrary trace. -/
theorem equal_DN_complex_mixed_bound {l₁ m₁ l₂ m₂ : X → ℝ}
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂) :
    ∃ C₁ C₂ : ℝ, 0<C₁ ∧ 0<C₂ ∧ ∀ u v : ComplexTrial Ω,
      ‖complexTrialEnergy l₁ m₁ u v-complexTrialEnergy l₂ m₂ u v‖≤
      C₁*complexResidualSize (ha₁.1.boundedCoefficient hO hB)
        (ha₁.2.1.boundedCoefficient hO hB) u*complexTrialSize v+
      C₂*complexTrialSize u*complexResidualSize (ha₂.1.boundedCoefficient hO hB)
        (ha₂.2.1.boundedCoefficient hO hB) v := by
  obtain ⟨C₁,C₂,hC₁,hC₂,h⟩ := equal_DN_mixed_quasimode_bound ha₁ ha₂ hO hB hDN
  refine ⟨C₁,C₂,hC₁,hC₂,fun u v => ?_⟩
  let E (a b : H1Hilbert Ω) := energy Ω l₁ m₁ (h1Equiv Ω a) (h1Equiv Ω b)-
    energy Ω l₂ m₂ (h1Equiv Ω a) (h1Equiv Ω b)
  have he : complexTrialEnergy l₁ m₁ u v-complexTrialEnergy l₂ m₂ u v=
      (E u.1 v.1:ℂ)+E u.2 v.2+Complex.I*((E u.2 v.1:ℂ)-E u.1 v.2) := by
    unfold complexTrialEnergy E
    push_cast
    ring
  rw [he]
  refine (norm_complex_four _ _ _ _).trans ?_
  have hh := add_le_add
    (add_le_add (add_le_add (h u.1 v.1) (h u.2 v.2)) (h u.2 v.1)) (h u.1 v.2)
  change |E u.1 v.1|+|E u.2 v.2|+|E u.2 v.1|+|E u.1 v.2|≤_ at hh
  refine hh.trans_eq ?_
  unfold complexResidualSize complexTrialSize
  ring

end Elasticity
/-! Squared physical H10-dual residual estimates in terms of the genuine
strong-force mass. This is the bridge from chart quasimodes to the DN map. -/
/-! Exact H1 masses of the physical complex trial projections, and bounds by
literal scalar component derivatives. -/
namespace ElasticityBoundaryPacket

/-! Equal full real physical DN maps control two genuine, independently
corrected physical packets; the traces need not coincide. -/
open Set
open scoped BigOperators
open Elasticity ElasticityBoundaryMVNormal
variable {Ω : Set X} {x : X}

lemma Setup.paired_packets (s : Setup Ω x) {l₁ m₁ l₂ m₂ : X → ℝ}
    (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
    (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω) (hx : x∈closure Ω)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂)
    (p₀ q₀ : W) (hp₀ : normal (l₁ x) (m₁ x) p₀=0) (hq₀ : normal (l₂ x) (m₂ x) q₀=0)
    (N : ℕ) :
    ∃ p q : Polynomial W, p.coeff 0=p₀ ∧ q.coeff 0=q₀ ∧
      ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
      ‖complexTrialEnergy l₁ m₁ (s.trial p δ) (s.trial q δ)-
        complexTrialEnergy l₂ m₂ (s.trial p δ) (s.trial q δ)‖≤C*δ^N := by
  obtain ⟨p,hp,A₁,B₁,hA₁,hB₁,hpB⟩ := s.packet hl₁ hm₁ ha₁ hO hB hx p₀ hp₀ N
  obtain ⟨q,hq,A₂,B₂,hA₂,hB₂,hqB⟩ := s.packet hl₂ hm₂ ha₂ hO hB hx q₀ hq₀ N
  obtain ⟨C₁,C₂,hC₁,hC₂,hE⟩ := equal_DN_complex_mixed_bound ha₁ ha₂ hO hB hDN
  refine ⟨p,q,hp,hq,C₁*B₁*A₂+C₂*A₁*B₂,by positivity,fun δ hδ hδ1 => ?_⟩
  apply (hE _ _).trans
  obtain ⟨hpS,hpR⟩ := hpB δ hδ hδ1
  obtain ⟨hqS,hqR⟩ := hqB δ hδ hδ1
  have hRS₂ : 0 ≤ complexResidualSize (ha₂.1.boundedCoefficient hO hB)
      (ha₂.2.1.boundedCoefficient hO hB) (s.trial q δ) := add_nonneg (ContinuousLinearMap.opNorm_nonneg _) (ContinuousLinearMap.opNorm_nonneg _)
  have hS₂ : 0 ≤ complexTrialSize (s.trial q δ) := add_nonneg (norm_nonneg _) (norm_nonneg _)
  calc
    _ ≤ C₁*(B₁*δ^N)*A₂+C₂*A₁*(B₂*δ^N) := add_le_add
      (mul_le_mul (mul_le_mul_of_nonneg_left hpR hC₁.le) hqS hS₂
        (mul_nonneg hC₁.le (mul_nonneg hB₁ (pow_nonneg hδ.le _))))
      (mul_le_mul (mul_le_mul_of_nonneg_left hpS hC₂.le) hqR hRS₂
        (mul_nonneg hC₂.le hA₁))
    _ = _ := by ring

end ElasticityBoundaryPacket

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryEnergy
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityBoundaryPacket
/-! Smooth compact localization of the literal pulled physical energy tensor.
The true chart Jacobian is retained, including its nonzero value at the center. -/
open Set Filter
open scoped Topology BigOperators
open Elasticity ElasticityBoundary ElasticityBoundaryPhysicalMass
  ElasticityBoundaryChartOperator ElasticityBoundaryLayerOperator

variable {Ω : Set X} {x : X}

lemma Setup.jacobian_continuous (s : Setup Ω x) : Continuous s.jacobian :=
  ((ContinuousLinearMap.continuous_det.comp (s.Φ_smooth.continuous_fderiv (by simp))).abs).comp
    (PiLp.continuous_toLp 2 (fun _ : I => ℝ))

lemma Setup.rawCoeff_continuous (s : Setup Ω x) {l m : X → ℂ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m) (i α j β : I) :
    Continuous (s.rawCoeff l m i α j β) := by
  exact (Complex.continuous_ofReal.comp s.jacobian_continuous).mul
    (smooth_chartPrincipal s.Q (s.Φ_smooth.comp PiLp.contDiff_toLp)
      (PiLp.contDiff_ofLp.comp s.Ψ_smooth) hl hm i α j β).continuous

/-- All modifications of this coefficient are outside the support of the
actual trial gradients. Its leading coefficient is the actual isotropic tensor. -/
lemma Setup.compact_energy_coefficients (s : Setup Ω x) {l m : X → ℂ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m) :
    ∃ H : I → I → I → I → Y → ℂ,
      (∀ i α j β, Continuous (H i α j β)) ∧
      (∀ i α j β, HasCompactSupport (H i α j β)) ∧
      (∀ i α j β y, WithLp.toLp 2 y∈s.K → H i α j β y=s.rawCoeff l m i α j β y) := by
  obtain ⟨ρ,hρ,hρc,_,hρ1,_⟩ := compact_smooth_cutoff s.compact isOpen_univ (subset_univ s.K)
  let ρc : Y → ℂ := fun y => (ρ (WithLp.toLp 2 y):ℂ)
  have hρcc : HasCompactSupport ρc :=
    (hρc.comp_homeomorph (PiLp.homeomorph 2 (fun _ : I => ℝ)).symm).comp_left
      (g := Complex.ofReal) Complex.ofReal_zero
  refine ⟨fun i α j β y => ρc y*s.rawCoeff l m i α j β y,?_,?_,?_⟩
  · intro i α j β
    exact (Complex.continuous_ofReal.comp (hρ.continuous.comp
      (PiLp.continuous_toLp 2 (fun _ : I => ℝ)))).mul (s.rawCoeff_continuous hl hm i α j β)
  · intro i α j β
    exact hρcc.mul_right
  · intro i α j β y hy
    simp only [ρc,hρ1.self_of_nhdsSet _ hy,Complex.ofReal_one,one_mul]

end ElasticityBoundaryPacket
namespace ElasticityBoundaryLimit
/-! Genuine Gaussian boundary scaling limits for the finite corrected
amplitudes. Dominated convergence is proved from the uniform polynomial
majorants and the actual half-space weight. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryScaling ElasticityBoundaryWeights ElasticityBoundaryOrderBound
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryCutoffParametrix
  ElasticityBoundaryProfileBounds ElasticityBoundaryCutoffLayer

lemma eventually_small_positive : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0<δ ∧ δ≤1 := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with δ hδ h1
  exact ⟨hδ,h1.le⟩

end ElasticityBoundaryLimit
namespace ElasticityBoundaryPacket
/-! Exact physical variational packet energy, with its true compact chart
Jacobian, equals the finite mixed coordinate-energy integrals. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open Elasticity ElasticityBoundaryDensityPull ElasticityBoundaryPacketMass ElasticityBoundaryPhysicalMass ElasticityBoundaryCutoffLayer
  ElasticityBoundaryStrongLayer ElasticityBoundaryMixedScaling ElasticityBoundaryGradientTransfer
  ElasticityBoundaryChartOperator ElasticityBoundaryMVNormal ElasticityBoundaryPhysicalTransfer
  ElasticityBoundaryCutoffParametrix ElasticityBoundaryActualTower

variable {Ω : Set X} {x : X}

lemma Setup.energy_compact_tensor (s : Setup Ω x) (hΩ : MeasurableSet Ω) {l m : X → ℝ}
    (hl : BoundedCoefficient Ω l) (hm : BoundedCoefficient Ω m)
    (H : I → I → I → I → Y → ℂ)
    (hH : ∀ i α j β y, WithLp.toLp 2 y∈s.K → H i α j β y=
      s.rawCoeff (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) i α j β y)
    (p q : Polynomial W) (δ : ℝ) :
    complexTrialEnergy l m (s.trial p δ) (s.trial q δ)=
      ∫ y in ElasticityBoundaryProfileBounds.halfspace,
        tensorDensity (fun i α j β => H i α j β y)
          (fun i α => dpart (cutoffLayer s.cutoff p δ i) α y)
          (fun i α => dpart (cutoffLayer s.cutoff q δ i) α y) := by
  rw [s.energy_chart hΩ hl hm]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  by_cases hy : WithLp.toLp 2 y∈s.K
  · simp only [hH _ _ _ _ y hy]
  · have hdp (i α : I) : dpart (cutoffLayer s.cutoff p δ i) α y=0 :=
      Function.notMem_support.mp (fun h => hy
        (dpart_support_lifted s.compact.isClosed (s.cutoff_layer_support p δ i) α h))
    simp only [tensorDensity,hdp,mul_zero,zero_mul,Finset.sum_const_zero]

lemma Setup.energy_sum (s : Setup Ω x) (hΩ : MeasurableSet Ω) {l m : X → ℝ}
    (hl : BoundedCoefficient Ω l) (hm : BoundedCoefficient Ω m)
    (H : I → I → I → I → Y → ℂ)
    (hHc : ∀ i α j β, Continuous (H i α j β))
    (hHs : ∀ i α j β, HasCompactSupport (H i α j β))
    (hH : ∀ i α j β y, WithLp.toLp 2 y∈s.K → H i α j β y=
      s.rawCoeff (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) i α j β y)
    (p q : Polynomial W) (δ : ℝ) :
    complexTrialEnergy l m (s.trial p δ) (s.trial q δ)=
      ∑ i, ∑ α, ∑ j, ∑ β, mixedEnergy 0 (H i α j β) s.cutoff p q i α j β δ := by
  rw [s.energy_compact_tensor hΩ hl hm H hH]
  have hInt (i α j β : I) : Integrable (fun y => H i α j β y*
      dpart (cutoffLayer s.cutoff p δ i) α y*star (dpart (cutoffLayer s.cutoff q δ j) β y)) :=
    (((hHc i α j β).mul (smooth_dpart (smooth_cutoffLayer s.cutoff_smooth p δ i) α).continuous).mul
      (smooth_dpart (smooth_cutoffLayer s.cutoff_smooth q δ j) β).continuous.star).integrable_of_hasCompactSupport
        ((hHs i α j β).mul_right.mul_right)
  simp only [tensorDensity,mixedEnergy,pow_zero,one_mul]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun α _ =>
    integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun β _ => (hInt i α j β).integrableOn))))]
  apply Finset.sum_congr rfl; intro i _
  rw [integral_finsetSum _ (fun α _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun β _ => (hInt i α j β).integrableOn)))]
  apply Finset.sum_congr rfl; intro α _
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun β _ => (hInt i α j β).integrableOn))]
  apply Finset.sum_congr rfl; intro j _
  exact integral_finsetSum _ (fun β _ => (hInt i α j β).integrableOn)

end ElasticityBoundaryPacket
namespace ElasticityBoundaryPacket
/-! The actual variational energy difference extracts a true normal factor of
the coefficient difference. No equality in a boundary neighborhood is used. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open Elasticity ElasticityBoundaryMixedScaling ElasticityBoundaryMVNormal
  ElasticityBoundaryCutoffLayer ElasticityBoundaryStrongLayer ElasticityBoundaryDensityPull
  ElasticityBoundaryGradientTransfer ElasticityBoundaryProfileBounds
variable {Ω : Set X} {x : X}

lemma mixed_integrable (n : ℕ) {H χ : Y → ℂ} (hH : Continuous H) (hcH : HasCompactSupport H)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (p q : Polynomial W) (i α j β : I) (δ : ℝ) :
    Integrable (fun y => (y 2:ℂ)^n*H y*dpart (cutoffLayer χ p δ i) α y*
      star (dpart (cutoffLayer χ q δ j) β y)) :=
  ((((Complex.continuous_ofReal.comp (continuous_apply 2)).pow n |>.mul hH).mul
    (smooth_dpart (smooth_cutoffLayer hχ p δ i) α).continuous).mul
    (smooth_dpart (smooth_cutoffLayer hχ q δ j) β).continuous.star).integrable_of_hasCompactSupport
      (hcH.mul_left.mul_right.mul_right)

lemma Setup.energy_difference_normal (s : Setup Ω x) (hΩ : MeasurableSet Ω)
    {l₁ m₁ l₂ m₂ : X → ℝ}
    (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
    (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
    (hb₁ : BoundedCoefficient Ω l₁) (hc₁ : BoundedCoefficient Ω m₁)
    (hb₂ : BoundedCoefficient Ω l₂) (hc₂ : BoundedCoefficient Ω m₂)
    (n : ℕ) (H : I → I → I → I → Y → ℂ)
    (hH : ∀ i α j β y, WithLp.toLp 2 y∈s.K →
      s.rawCoeff (fun z => (l₁ z:ℂ)) (fun z => (m₁ z:ℂ)) i α j β y-
      s.rawCoeff (fun z => (l₂ z:ℂ)) (fun z => (m₂ z:ℂ)) i α j β y=(y 2:ℂ)^n*H i α j β y)
    (p q : Polynomial W) (δ : ℝ) :
    complexTrialEnergy l₁ m₁ (s.trial p δ) (s.trial q δ)-
      complexTrialEnergy l₂ m₂ (s.trial p δ) (s.trial q δ)=
      ∑ i, ∑ α, ∑ j, ∑ β, mixedEnergy n (H i α j β) s.cutoff p q i α j β δ := by
  obtain ⟨H₁,hH₁,hH₁c,hE₁⟩ := s.compact_energy_coefficients
    (Complex.ofRealCLM.contDiff.comp hl₁) (Complex.ofRealCLM.contDiff.comp hm₁)
  obtain ⟨H₂,hH₂,hH₂c,hE₂⟩ := s.compact_energy_coefficients
    (Complex.ofRealCLM.contDiff.comp hl₂) (Complex.ofRealCLM.contDiff.comp hm₂)
  rw [s.energy_sum hΩ hb₁ hc₁ H₁ hH₁ hH₁c hE₁,s.energy_sum hΩ hb₂ hc₂ H₂ hH₂ hH₂c hE₂]
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro α _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro β _
  unfold mixedEnergy
  rw [← integral_sub (mixed_integrable 0 (hH₁ i α j β) (hH₁c i α j β) s.cutoff_smooth p q i α j β δ).integrableOn
    (mixed_integrable 0 (hH₂ i α j β) (hH₂c i α j β) s.cutoff_smooth p q i α j β δ).integrableOn]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  simp only [pow_zero,one_mul,← sub_mul]
  by_cases hy : WithLp.toLp 2 y∈s.K
  · rw [hE₁ _ _ _ _ y hy,hE₂ _ _ _ _ y hy]
    exact congrArg (fun a : ℂ => a*dpart (cutoffLayer s.cutoff p δ i) α y*
      star (dpart (cutoffLayer s.cutoff q δ j) β y)) (hH i α j β y hy)
  · have hp : dpart (cutoffLayer s.cutoff p δ i) α y=0 :=
      Function.notMem_support.mp (fun h => hy
        (dpart_support_lifted s.compact.isClosed (s.cutoff_layer_support p δ i) α h))
    simp only [hp,mul_zero,zero_mul]

end ElasticityBoundaryPacket
namespace ElasticityBoundaryPacket
/-! Direct extraction of every factored normal coefficient by the real physical
DN map and the genuine physical localized asymptotic tests. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open Elasticity ElasticityBoundaryMVNormal ElasticityBoundaryMixedScaling
  ElasticityBoundaryLimit ElasticityBoundaryMVCalculus ElasticityBoundaryWeights
  ElasticityBoundaryTensorSeries ElasticityBoundaryParameter
variable {Ω : Set X} {x : X}

lemma normalized_tendsto_zero (n : ℕ) {f : ℝ → ℂ} {C : ℝ}
    (hf : ∀ δ : ℝ, 0<δ → δ≤1 → ‖f δ‖≤C*δ^(2*n+1)) :
    Tendsto (fun δ => ((δ^(2*n))⁻¹:ℝ) • f δ) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun δ => C*δ)
  · filter_upwards [eventually_small_positive] with δ hδ
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hδ.1.le _))]
    apply (mul_le_mul_of_nonneg_left (hf δ hδ.1 hδ.2)
      (inv_nonneg.mpr (pow_nonneg hδ.1.le _))).trans_eq
    rw [pow_succ]
    field_simp [hδ.1.ne']
  · simpa using (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds) :
      Tendsto (fun δ : ℝ => C*δ) (𝓝[>] 0) (𝓝 (C*0)))

/-- Any actual normal factor of the pulled tensor is detected. The hypothesis
is an exact factorization on the packet support, not a boundary agreement
assumption and not an abstract conclusion-carrying jet interface. -/
lemma Setup.extract_normal_oai (s : Setup Ω x) {l₁ m₁ l₂ m₂ : X → ℝ}
    (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
    (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω) (hx : x∈closure Ω)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂)
    (n : ℕ) (H : I → I → I → I → Y → ℂ)
    (hHc : ∀ i α j β, Continuous (H i α j β))
    (hHs : ∀ i α j β, HasCompactSupport (H i α j β))
    (hH : ∀ i α j β y, WithLp.toLp 2 y∈s.K →
      s.rawCoeff (fun z => (l₁ z:ℂ)) (fun z => (m₁ z:ℂ)) i α j β y-
      s.rawCoeff (fun z => (l₂ z:ℂ)) (fun z => (m₂ z:ℂ)) i α j β y=(y 2:ℂ)^n*H i α j β y)
    (p₀ q₀ : W) (hp₀ : normal (l₁ x) (m₁ x) p₀=0) (hq₀ : normal (l₂ x) (m₂ x) q₀=0) :
    frozenPair n (fun i α j β => H i α j β 0) p₀ q₀=0 := by
  obtain ⟨p,q,hp,hq,C,_hC,hEst⟩ := s.paired_packets hl₁ hm₁ hl₂ hm₂ ha₁ ha₂
    hO hB hx hDN p₀ q₀ hp₀ hq₀ (2*n+1)
  have he (δ : ℝ) := s.energy_difference_normal hO.measurableSet hl₁ hm₁ hl₂ hm₂
    (ha₁.1.boundedCoefficient hO hB) (ha₁.2.1.boundedCoefficient hO hB)
    (ha₂.1.boundedCoefficient hO hB) (ha₂.2.1.boundedCoefficient hO hB) n H hH p q δ
  have ht := normalized_tendsto_zero n hEst
  have hlim := tendsto_finsetSum Finset.univ (fun i _ => tendsto_finsetSum Finset.univ
    (fun α _ => tendsto_finsetSum Finset.univ (fun j _ => tendsto_finsetSum Finset.univ
      (fun β _ => mixedEnergy_limit n (hHc i α j β) (hHs i α j β) s.cutoff_smooth
        s.cutoff_compact s.cutoff_one.eq_of_nhds p q i α j β))))
  have ht' : Tendsto (fun δ => ∑ i, ∑ α, ∑ j, ∑ β,
      ((δ^(2*n))⁻¹:ℝ) • mixedEnergy n (H i α j β) s.cutoff p q i α j β δ)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [he,Finset.smul_sum] using ht
  have hEq := tendsto_nhds_unique hlim ht'
  simpa only [frozenPair,hp,hq] using hEq

end ElasticityBoundaryPacket

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryPacket.Setup.extract_normal_oai := @OAI.ElasticityBoundaryPacket.Setup.extract_normal_oai
