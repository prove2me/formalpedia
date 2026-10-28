-- Prove2me | solution 1 for OAI.Elasticity.physicalResidual_sq_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:46:32.155912+00:00
-- url     : https://prove2.me/submissions/30dc8378-908c-4340-af52-9f7990a325fc

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El000

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Elasticity
/-! Genuine strong-to-variational residual estimate for boundary trial fields.
All pairings are on the actual physical H10 space, extended by its defining
density, not a separately assumed boundary test class. -/
open MeasureTheory Set
open scoped BigOperators
variable {Ω : Set X} {lam mu : X → ℝ}

lemma jetStrain_symm (u : JetH Ω) (i j : Fin 3) :
    jetStrain Ω i j u = jetStrain Ω j i u := by
  simp only [jetStrain, add_comm]

lemma jetEnergy_stress (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u v : JetH Ω) :
    jetEnergy hl hm u v = ∑ i, ∑ j, inner ℝ (jetStress hl hm u i j) (jetEntry Ω i j v) := by
  have hv (i j : Fin 3) : jetStrain Ω i j v =
      (1/2 : ℝ) • (jetEntry Ω i j v + jetEntry Ω j i v) := rfl
  have hs : (∑ i, ∑ j, inner ℝ (hm.mulL (jetStrain Ω i j u)) (jetEntry Ω j i v)) =
      ∑ i, ∑ j, inner ℝ (hm.mulL (jetStrain Ω i j u)) (jetEntry Ω i j v) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [jetStrain_symm u j i]
  have hd (i j : Fin 3) :
      inner ℝ (if i = j then hl.mulL (jetDiv Ω u) else 0) (jetEntry Ω i j v) =
        if i = j then inner ℝ (hl.mulL (jetDiv Ω u)) (jetEntry Ω i j v) else 0 := by
    by_cases h : i = j <;> simp [h]
  rw [jetEnergy_apply]
  simp only [hv, inner_smul_right, inner_add_right, mul_add, Finset.sum_add_distrib,
    ← Finset.mul_sum, hs]
  simp only [jetStress, inner_add_left, real_inner_smul_left,
    Finset.sum_add_distrib, ← Finset.mul_sum, hd,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [jetDiv, sum_apply, inner_sum]
  ring

/-- Smooth scalar integration by parts with a compactly supported interior test. -/
lemma boundary_smooth_ibp {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
    (hs : tsupport (g : X → ℝ) ⊆ Ω) (j : Fin 3) :
    (∫ x, f x*ElasticityKorn.d (coordVector j) g x ∂(volume.restrict Ω)) =
    -(∫ x, fderiv ℝ f x (coordVector j)*g x ∂(volume.restrict Ω)) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (g : X → ℝ) := g.smooth _
  have hd : Continuous (fun x => fderiv ℝ f x (coordVector j)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgd : Continuous (fun x => fderiv ℝ (g : X → ℝ) x (coordVector j)) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    have hz := image_eq_zero_of_notMem_tsupport (f := (ElasticityKorn.d (coordVector j) g : X → ℝ))
      (fun ht => hx (hs ((tsupport_fderiv_apply_subset ℝ (coordVector j)) ht)))
    rw [hz,mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (f := (g : X → ℝ)) (fun ht => hx (hs ht)),mul_zero])]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hd.mul hg.continuous).integrable_of_hasCompactSupport (hc.mul_left))
    ((hf.continuous.mul hgd).integrable_of_hasCompactSupport ((hc.fderiv_apply ℝ _).mul_left))
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport (hc.mul_left))
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hg.differentiable (by simp) x)

lemma boundary_L2_schwartz_pair (f : ScalarL2 Ω) (g : SchwartzMap X ℝ) :
    inner ℝ f (schwartzR Ω g) = ∫ x, f x*g x ∂(volume.restrict Ω) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [g.coeFn_toLp 2 (volume.restrict Ω)] with x hx
  change inner ℝ (f x) (g.toLp 2 (volume.restrict Ω) x)=_
  rw [hx, real_inner_comm]
  rfl

lemma boundaryForcePair_apply (F : Fin 3 → ScalarL2 Ω) (v : JetH Ω) :
    boundaryForcePair F v = ∑ i, inner ℝ (F i) (jetScalar Ω none i v) := by
  simp [boundaryForcePair, sum_apply]

/-- Smooth stresses with their literal divergence give exactly the physical
variational residual. The same statement permits local coefficient extensions:
only equality to the actual stress on Ω is required. -/
theorem physicalResidual_of_smooth_stress
    (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (hB : Bornology.IsBounded Ω) (u : H1Hilbert Ω) (s : Fin 3 → Fin 3 → X → ℝ)
    (hs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (s i j))
    (hes : ∀ i j, jetStress hl hm u.val i j =ᵐ[volume.restrict Ω] s i j)
    (hd : ∀ i j, MemLp (fun x => fderiv ℝ (s i j) x (coordVector j)) 2 (volume.restrict Ω)) :
    physicalResidual hl hm u =
      -(boundaryForcePair (fun i => ∑ j, (hd i j).toLp _)).comp (H10Hilbert Ω).subtypeL := by
  apply ContinuousLinearMap.ext
  intro v
  change jetEnergy hl hm u.val v.val =
    -boundaryForcePair (fun i => ∑ j, (hd i j).toLp _) v.val
  apply h10_induction_closed (P := fun w => jetEnergy hl hm u.val w =
    -boundaryForcePair (fun i => ∑ j, (hd i j).toLp _) w)
  · exact isClosed_eq (jetEnergy hl hm u.val).continuous
      (boundaryForcePair (fun i => ∑ j, (hd i j).toLp _)).continuous.neg
  · intro w hw
    obtain ⟨G, hG, h0, h1⟩ := jet_test_representation w hw
    rw [jetEnergy_stress, boundaryForcePair_apply]
    simp only [h0, h1, sum_inner, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [boundary_L2_schwartz_pair, boundary_L2_schwartz_pair]
    have hab := boundary_smooth_ibp (hs i j) (G i)
      (Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_tsupport _, hB.subset (hG i)⟩) (hG i) j
    calc
      _ = ∫ x, s i j x * ElasticityKorn.d (coordVector j) (G i) x ∂(volume.restrict Ω) := by
        apply integral_congr_ae
        filter_upwards [hes i j] with x hx
        rw [hx]
        rfl
      _ = _ := hab
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [(hd i j).coeFn_toLp] with x hx
        rw [hx]

lemma jetScalar_value_norm_le (v : JetH Ω) (i : Fin 3) :
    ‖jetScalar Ω none i v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [jet_norm_sq]
  have h1 : ‖jetScalar Ω none i v‖ ^ 2 ≤ jetValueSq Ω v := by
    apply Finset.single_le_sum (f := fun j => ‖jetScalar Ω none j v‖ ^ 2)
    · intro j _; exact sq_nonneg _
    · exact Finset.mem_univ i
  have h2 : 0 ≤ jetGradSq Ω v :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  linarith

lemma boundaryForcePair_norm_le (F : Fin 3 → ScalarL2 Ω) :
    ‖boundaryForcePair F‖ ≤ ∑ i, ‖F i‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro v
  rw [boundaryForcePair_apply]
  calc
    ‖∑ i, inner ℝ (F i) (jetScalar Ω none i v)‖ ≤
        ∑ i, ‖inner ℝ (F i) (jetScalar Ω none i v)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖F i‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (jetScalar_value_norm_le v i) (norm_nonneg _))
    _ = _ := by rw [Finset.sum_mul]

/-- The actual dual residual obeys an L2 strong-residual bound; no boundary
regularity of the test space or unproved trace density is used. -/
theorem physicalResidual_norm_le_of_smooth_stress
    (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (hB : Bornology.IsBounded Ω) (u : H1Hilbert Ω) (s : Fin 3 → Fin 3 → X → ℝ)
    (hs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (s i j))
    (hes : ∀ i j, jetStress hl hm u.val i j =ᵐ[volume.restrict Ω] s i j)
    (hd : ∀ i j, MemLp (fun x => fderiv ℝ (s i j) x (coordVector j)) 2 (volume.restrict Ω)) :
    ‖physicalResidual hl hm u‖ ≤ ∑ i, ‖∑ j, (hd i j).toLp _‖ := by
  rw [physicalResidual_of_smooth_stress hl hm hB u s hs hes hd]
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro v
  change ‖-boundaryForcePair (fun i => ∑ j, (hd i j).toLp _) v.val‖ ≤ _
  rw [norm_neg]
  exact ((boundaryForcePair (fun i => ∑ j, (hd i j).toLp _)).le_opNorm v.val).trans
    (mul_le_mul_of_nonneg_right (boundaryForcePair_norm_le _) (norm_nonneg _))

end Elasticity
/-! Squared physical H10-dual residual estimates in terms of the genuine
strong-force mass. This is the bridge from chart quasimodes to the DN map. -/
section
open Set MeasureTheory
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X}

lemma L2_norm_sq_mass (v : ScalarL2 Ω) : ‖v‖^2=∫ x in Ω, ‖v x‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma sum_toLp_norm_sq (f : Fin 3 → X → ℝ) (hf : ∀ j, MemLp (f j) 2 (volume.restrict Ω)) :
    ‖∑ j, (hf j).toLp (f j)‖^2=∫ x in Ω, ‖∑ j, f j x‖^2 := by
  rw [L2_norm_sq_mass]
  apply integral_congr_ae
  have hall := Filter.eventually_all.mpr (fun j => (hf j).coeFn_toLp)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => (hf j).toLp (f j)),hall] with x hx hy
  simp only [hx,Finset.sum_apply,hy]

lemma sum_three_sq (v : Fin 3 → ℝ) : (∑ i, v i)^2≤3*∑ i, (v i)^2 := by
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (v 0-v 1),sq_nonneg (v 0-v 2),sq_nonneg (v 1-v 2)]

lemma physicalResidual_sq_mass_oai {l m : X → ℝ}
    (hl : BoundedCoefficient Ω l) (hm : BoundedCoefficient Ω m)
    (hB : Bornology.IsBounded Ω) (u : H1Hilbert Ω) (s : Fin 3 → Fin 3 → X → ℝ)
    (hs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (s i j))
    (hes : ∀ i j, jetStress hl hm u.val i j =ᵐ[volume.restrict Ω] s i j)
    (hd : ∀ i j, MemLp (fun x => fderiv ℝ (s i j) x (coordVector j)) 2 (volume.restrict Ω)) :
    ‖physicalResidual hl hm u‖^2≤3*∑ i,
      (∫ x in Ω, ‖∑ j, fderiv ℝ (s i j) x (coordVector j)‖^2) := by
  have h := physicalResidual_norm_le_of_smooth_stress hl hm hB u s hs hes hd
  have h0 : 0≤∑ i, ‖∑ j, (hd i j).toLp _‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  apply ((sq_le_sq₀ (norm_nonneg (physicalResidual hl hm u)) h0).mpr h).trans
  have hsq := sum_three_sq (fun i => ‖∑ j, (hd i j).toLp _‖)
  simpa only [sum_toLp_norm_sq] using hsq

end Elasticity

end
/-! Exact H1 masses of the physical complex trial projections, and bounds by
literal scalar component derivatives. -/

end

end OAI
end

theorem solution : type_of% @OAI.Elasticity.physicalResidual_sq_mass_oai := @OAI.Elasticity.physicalResidual_sq_mass_oai
