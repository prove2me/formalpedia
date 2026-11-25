-- Prove2me | solution 1 for GlobalTheory.ThetaInter.mean_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:51:24.046683+00:00
-- url     : https://prove2.me/submissions/dd60e963-7602-485a-881b-33f10f0d0c06

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Theorems.Thm_GlobalTheory_ThetaInter_chi_eq_one_iff
import Theorems.Thm_GlobalTheory_ThetaInter_alpha_sq
import Theorems.Thm_GlobalTheory_ThetaInter_alpha_conj
import Theorems.Thm_GlobalTheory_ThetaInter_inter_eq
import Theorems.Thm_GlobalTheory_ThetaInter_inter_mem_fixedBy
import Theorems.Thm_GlobalTheory_ThetaInter_rho_eq
import Theorems.Thm_GlobalTheory_ThetaInter_rho_opU
import Theorems.Thm_GlobalTheory_ThetaInter_rho_add_of_fixed
import Theorems.Thm_GlobalTheory_ThetaInter_exists_basis
import Theorems.Thm_GlobalTheory_ThetaInter_span_inf_eq_top
import Theorems.Thm_GlobalTheory_ThetaInter_differentiable_opU
import Theorems.Thm_GlobalTheory_ThetaInter_differentiable_inter
import Theorems.Thm_GlobalTheory_ThetaInter_continuous_dens
import Theorems.Thm_GlobalTheory_ThetaInter_continuous_rho
import Theorems.Thm_GlobalTheory_ThetaInter_mean_eq
import Theorems.Thm_GlobalTheory_ThetaInter_integral_dens_eq_zero
import Theorems.Thm_GlobalTheory_average_fundamentalDomain_eq_real
import Theorems.Thm_GlobalTheory_integrableOn_fundamentalDomain_of_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaInter
open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
variable {α : V → ℂ}
open MeasureTheory
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
  [FiniteDimensional ℝ W] {H : Sesq W} {α : W → ℂ}
variable [MeasurableSpace W] [BorelSpace W] (μ : Measure W) [μ.IsAddHaarMeasure]
namespace GlobalTheory.ThetaInter
theorem _root_.solution (hH : IsHerm H) {A₁ A₂ : AddSubgroup W} [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)]
    (hA₁ : DiscreteTopology A₁) (hsp₁ : Submodule.span ℝ (A₁ : Set W) = ⊤)
    (hA₂ : DiscreteTopology A₂) (hsp₂ : Submodule.span ℝ (A₂ : Set W) = ⊤)
    (hd₁ : IsSelfDual H A₁) (hs₁ : IsSemiChar H A₁ α) (hd₂ : IsSelfDual H A₂) (hs₂ : IsSemiChar H A₂ α)
    {F : W → ℂ} (hc : Differentiable ℂ F) (hF : F ∈ fixedBy H α A₁) :
    mean μ A₂ (rho H (inter H α A₁ A₂ F)) = mean μ A₁ (rho H F) := by
  classical
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  obtain ⟨n₁, b₁, hb₁⟩ := exists_basis hA₁ hsp₁
  obtain ⟨n₂, b₂, hb₂⟩ := exists_basis hA₂ hsp₂
  obtain ⟨n, b, hb⟩ := exists_basis (A := A₁ ⊓ A₂)
    (DiscreteTopology.of_subset (s := (A₂ : Set W)) hA₂ fun x hx => hx.2) (span_inf_eq_top hsp₂)
  have hm := inter_mem_fixedBy hH hs₁ hd₂ hs₂ hF
  have hle₁ : Submodule.span ℤ (Set.range b) ≤ Submodule.span ℤ (Set.range b₁) := fun x hx =>
    hb₁.ge (hb.le hx).1
  have hle₂ : Submodule.span ℤ (Set.range b) ≤ Submodule.span ℤ (Set.range b₂) := fun x hx =>
    hb₂.ge (hb.le hx).2
  have e1 := average_fundamentalDomain_eq_real μ b₂ b _
    (continuous_rho hH (differentiable_inter (H := H) (α := α) A₁ A₂ hc).continuous)
    (fun y hy z => rho_add_of_fixed hH hs₂ hm (hb₂.le hy) z) hle₂ 0
  have e2 := fun a => average_fundamentalDomain_eq_real μ b₁ b _ (continuous_rho hH hc.continuous)
    (fun y hy z => rho_add_of_fixed hH hs₁ hF (hb₁.le hy) z) hle₁ a
  simp only [add_zero] at e1
  rw [mean_eq μ b₂ hb₂ fun y hy z => rho_add_of_fixed hH hs₂ hm hy z,
    mean_eq μ b₁ hb₁ fun y hy z => rho_add_of_fixed hH hs₁ hF hy z, ← e1]
  set m : ℝ := (Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂) : ℝ) with hmdef
  have hpos : 0 < m := by rw [hmdef]; exact_mod_cast Fintype.card_pos
  set r : A₂ ⧸ A₁.addSubgroupOf A₂ → W := fun c => ((Quotient.out c : A₂) : W) with hr
  have hrm : ∀ c, r c ∈ A₂ := fun c => (Quotient.out c : A₂).2
  have e3 : ∫ v in ZSpan.fundamentalDomain b, rho H (inter H α A₁ A₂ F) v ∂μ =
      m⁻¹ * ∑ c, ∫ v in ZSpan.fundamentalDomain b, rho H F (v + r c) ∂μ := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    have hpt : ∀ v, ((rho H (inter H α A₁ A₂ F) v : ℝ) : ℂ) =
        (m⁻¹ : ℝ) * ∑ c, ∑ c', (α (r c) * α (r c')) * dens H (opU H (r c) F) (opU H (r c') F) v := by
      intro v
      have h2 : ((Real.sqrt m : ℝ) : ℂ)⁻¹ * ((Real.sqrt m : ℝ) : ℂ)⁻¹ = (m⁻¹ : ℝ) := by
        rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le, Complex.ofReal_inv]
      rw [rho_eq hH, inter_eq, ← h2]
      simp only [dens, map_mul, map_sum, map_inv₀, Complex.conj_ofReal]
      rw [mul_mul_mul_comm, Finset.sum_mul_sum, mul_assoc]
      congr 1
      simp only [Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
      rw [alpha_conj hs₂ (hrm c')]
      ring
    have hint : ∀ c c', IntegrableOn (fun v => (α (r c) * α (r c')) *
          dens H (opU H (r c) F) (opU H (r c') F) v) (ZSpan.fundamentalDomain b) μ := fun c c' =>
      integrableOn_fundamentalDomain_of_continuous μ b _
        (continuous_const.mul (continuous_dens hH (differentiable_opU hc _).continuous
          (differentiable_opU hc _).continuous))
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
      integral_finset_sum _ fun y _ => integrable_finset_sum _ fun y' _ => hint y y',
      Complex.ofReal_mul, Complex.ofReal_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_finset_sum _ fun y' _ => hint c y', Finset.sum_eq_single_of_mem c (Finset.mem_univ _)]
    · rw [alpha_sq hs₂ (hrm c), ← integral_complex_ofReal]
      simp only [one_mul, ← rho_eq hH, rho_opU hH]
    · intro c' _ hne
      rw [integral_const_mul, integral_dens_eq_zero μ hH hd₁ hs₁ hF b (fun x hx => (hb.le hx).1) _ _
        (fun x hx => (chi_eq_one_iff _ _).2 (hd₂.ge (hb.le hx).2 _ (A₂.sub_mem (hrm c) (hrm c'))))
        (fun h => hne ?_), mul_zero]
      rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c', QuotientAddGroup.eq,
        AddSubgroup.mem_addSubgroupOf]
      simpa [hr, neg_add_eq_sub] using h
  rw [setAverage_eq, e3, smul_eq_mul, mul_left_comm, Finset.mul_sum]
  simp only [← smul_eq_mul, ← setAverage_eq, e2]
  simp [← hmdef, hpos.ne']
end GlobalTheory.ThetaInter
