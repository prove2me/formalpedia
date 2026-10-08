-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_moving_zero_free
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:51:01.056975+00:00
-- url     : https://prove2.me/submissions/8ec308e8-2bf4-48f6-93cd-9597a038682a

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_disk_logderiv

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MertensClassical
namespace Erdos970


namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics



end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology




end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log













































attribute [fun_prop] measurable_from_top












section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg



@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]






end LogZetaInteg
end











section
open _root_.MeasureTheory _root_.Set








end












































end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Rectangle
namespace Erdos970

open _root_.Complex _root_.Set _root_.Topology

open scoped _root_.Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle




@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl





































end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.ResidueCalcOnRectangles
namespace Erdos970

open _root_.Complex _root_.BigOperators _root_.Nat _root_.Classical _root_.Real _root_.Topology _root_.Filter
open _root_.Set _root_.MeasureTheory _root_.intervalIntegral _root_.Asymptotics

open scoped _root_.Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}
















theorem existsDifferentiableOn_of_bddAbove [CompleteSpace E]
    {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c}))
    (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E),
      HolomorphicOn g s ∧ Set.EqOn f g (s \ {c}) :=
  ⟨Function.update f c (limUnder (𝓝[{c}ᶜ] c) f),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb,
    fun z hz ↦ if h : z = c then (hz.2 h).elim
      else by simp [h]⟩







































lemma IsBigO_to_BddAbove {f : ℂ → ℂ} {p : ℂ}
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by
  simp only [isBigO_iff, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at f_near_p
  obtain ⟨c, hc⟩ := f_near_p
  dsimp [Filter.Eventually, nhdsWithin] at hc
  rw [mem_inf_principal'] at hc
  obtain ⟨U, hU, ⟨U_is_open, p_in_U⟩⟩ := mem_nhds_iff.mp hc
  use U
  constructor
  · exact IsOpen.mem_nhds U_is_open p_in_U
  · refine bddAbove_def.mpr ?_
    use c
    intro y hy
    simp only [Function.comp_apply, mem_image, Set.mem_sdiff, mem_singleton_iff] at hy
    obtain ⟨x, ⟨x_in_U, x_not_p⟩, fxy⟩ := hy
    rw [← fxy]
    simpa [x_not_p] using hU x_in_U






























end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Sobolev
namespace Erdos970

open _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap _root_.BigOperators
open scoped _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun




section lemmas




end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun



















end CS

namespace trunc







end trunc

namespace W1











end W1

namespace W21













end W21


end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Fourier
namespace Erdos970

open _root_.FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap VectorFourier _root_.BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]


@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl



@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas


@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.ZetaBounds
namespace Erdos970


open _root_.Complex _root_.Topology _root_.Filter _root_.Interval _root_.Set _root_.Asymptotics






local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

theorem ResidueOfTendsTo {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (hU : U ∈ 𝓝 p)
    (hf : HolomorphicOn f (U \ {p}))
    {A : ℂ}
    (h_limit : Tendsto (fun s ↦ (s - p) * f s) (𝓝[≠] p) (𝓝 A)) :
    ∃ V ∈ 𝓝 p,
    BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (V \ {p})) := by
                                                                
  have h_event : ∀ᶠ s in 𝓝[≠] p, ‖(s - p) * f s - A‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_nhds :
      ∀ᶠ s in 𝓝 p, s ≠ p → ‖(s - p) * f s - A‖ < 1 := by
    exact (eventually_nhdsWithin_iff).1 h_event
  rcases (eventually_nhds_iff.1 h_event_nhds) with ⟨V₀, hV₀_mem, hV₀_prop⟩
  have h_bound :
      ∀ s, s ∈ V₀ \ {p} → ‖(s - p) * f s‖ ≤ ‖A‖ + 1 := by
    intro s hs
    rcases hs with ⟨hV₀, hsne⟩
    calc ‖(s - p) * f s‖ = ‖((s - p) * f s - A) + A‖ := by
          ring_nf
        _ ≤ ‖(s - p) * f s - A‖ + ‖A‖ := norm_add_le ((s - p) * f s - A) A
        _ ≤ 1 + ‖A‖ := add_le_add_left (le_of_lt (hV₀_mem s hV₀ hsne)) ‖A‖
        _ = ‖A‖ + 1 := add_comm 1 ‖A‖
  have h_bdd :
      BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (V₀ \ {p})) := by
    refine ⟨‖A‖ + 1, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact h_bound s hs
                                                                 
  set W : Set ℂ := V₀ ∩ U with hW_def
  have hW_mem : (W : Set ℂ) ∈ 𝓝 p := inter_mem (IsOpen.mem_nhds hV₀_prop.1 hV₀_prop.2) hU
  have h_subset_V₀ : (W \ {p}) ⊆ (V₀ \ {p}) := by
    intro z hz; exact ⟨hz.1.1, hz.2⟩
  have h_prod_holo : HolomorphicOn (fun z ↦ (z - p) * f z) (W \ {p}) := by
    have h_id : HolomorphicOn (fun z : ℂ ↦ z - p) (W \ {p}) :=
      Differentiable.differentiableOn (Differentiable.sub_const differentiable_fun_id p)
    have hfW : HolomorphicOn f (W \ {p}) := by
      apply hf.mono
      exact Set.sdiff_subset_sdiff_left inter_subset_right
    simpa using! h_id.mul hfW
  have h_bdd_W : BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (W \ {p})) :=
    h_bdd.mono (image_mono h_subset_V₀)
                                                                    
  obtain ⟨g, hg_holo, hg_eq⟩ :=
    existsDifferentiableOn_of_bddAbove hW_mem h_prod_holo h_bdd_W
  have h_event_eq :
      (fun z ↦ g z) =ᶠ[𝓝[≠] p] fun z ↦ (z - p) * f z := by
    have hW_diff_mem : (W \ {p} : Set ℂ) ∈ 𝓝[≠] p :=
      sdiff_mem_nhdsWithin_compl hW_mem {p}
    exact (hg_eq.eventuallyEq_of_mem hW_diff_mem).symm
  have h_tendsto_gA : Tendsto g (𝓝[≠] p) (𝓝 A) :=
      h_limit.congr' (id (EventuallyEq.symm h_event_eq))
  have hpW : p ∈ W := by
    exact mem_of_mem_nhds hW_mem
  have h_cont_g : ContinuousAt g p := by
    apply (hg_holo.continuousOn.continuousWithinAt hpW).continuousAt hW_mem
  have h_tendsto_gp : Tendsto g (𝓝[≠] p) (𝓝 (g p)) :=
    h_cont_g.tendsto.mono_left inf_le_left
  have g_p_eq : g p = A :=
    tendsto_nhds_unique' (NormedField.nhdsNE_neBot p) h_tendsto_gp h_tendsto_gA
  let q : ℂ → ℂ := fun z ↦ (g z - A) / (z - p)
  have h_deriv : HasDerivAt g (deriv g p) p := by
    exact DifferentiableOn.hasDerivAt hg_holo hW_mem
  have h_q_limit : Tendsto q (𝓝[≠] p) (𝓝 (deriv g p)) := by
    rw [hasDerivAt_iff_tendsto_slope] at h_deriv
    unfold slope at h_deriv
    simp only [vsub_eq_sub, smul_eq_mul, inv_mul_eq_div, g_p_eq] at h_deriv
    exact h_deriv
  have h_event_q : ∀ᶠ z in 𝓝[≠] p, ‖q z - deriv g p‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_q_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_q_nhds : ∀ᶠ z in 𝓝 p, z ≠ p → ‖q z - deriv g p‖ < 1 := by
    simpa using (eventually_nhdsWithin_iff).1 h_event_q
  rcases (eventually_nhds_iff.1 h_event_q_nhds) with
    ⟨V₁, hV₁_mem, hV₁_prop⟩
  have h_q_bound :
      ∀ z, z ∈ V₁ \ {p} → ‖q z‖ ≤ ‖deriv g p‖ + 1 := by
    intro z hz
    rcases hz with ⟨hV₁, hz_ne⟩
    calc ‖q z‖ = ‖(q z - deriv g p) + (deriv g p)‖ := by
          ring_nf
        _ ≤ ‖q z - deriv g p‖ + ‖deriv g p‖ := norm_add_le (q z - deriv g p) (deriv g p)
        _ ≤ 1 + ‖deriv g p‖  := add_le_add_left (le_of_lt (hV₁_mem z hV₁ hz_ne)) ‖deriv g p‖
        _ = ‖deriv g p‖ + 1 := add_comm 1 ‖deriv g p‖
                                                   
  have h_eq_diff :
      EqOn (fun z ↦ f z - A * (z - p)⁻¹) q (W \ {p}) := by
    intro z hz
    simp only
    have hz_ne : (z - p) ≠ 0 := sub_ne_zero.mpr hz.2
    have hgz : g z = (z - p) * f z := by
      exact id (EqOn.symm hg_eq) hz
    simp only [hgz, q]
    field_simp
  apply IsBigO_to_BddAbove
  rw [isBigO_iff]
  use ‖deriv g p‖ + 1
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [IsOpen.mem_nhds hV₁_prop.1 hV₁_prop.2, hW_mem] with z hV₁ hW z_ne_p
  specialize h_eq_diff ⟨ hW, z_ne_p⟩
  simp only [Pi.sub_apply, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary,
    mul_one] at h_eq_diff ⊢
  rw [h_eq_diff]
  exact h_q_bound _ ⟨hV₁, z_ne_p⟩



theorem riemannZetaResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (ζ - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  have zeta_holc : HolomorphicOn ζ (univ \ {1}) := by
    intro y hy
    exact DifferentiableAt.differentiableWithinAt <| differentiableAt_riemannZeta hy.2
  convert (preTransparency := .instances) ResidueOfTendsTo univ_mem zeta_holc riemannZeta_residue_one using 6
  simp

theorem deriv_eqOn_of_eqOn_punctured (f g : ℂ → ℂ) (U : Set ℂ) (p : ℂ)
    (hU_open : IsOpen U)
    (h_eq : EqOn f g (U \ {p})) :
    EqOn (deriv f) (deriv g) (U \ {p}) := by
  intro x hx
  apply EventuallyEq.deriv_eq
  filter_upwards [IsOpen.mem_nhds (hU_open.sdiff isClosed_singleton) hx] with t ht using h_eq ht

theorem analytic_deriv_bounded_near_point
    (f : ℂ → ℂ) {U : Set ℂ} {p : ℂ} (hU : IsOpen U) (hp : p ∈ U) (hf : HolomorphicOn f U) :
    (deriv f) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have U_in_filter : U ∈ 𝓝 p := by
    exact IsOpen.mem_nhds hU hp
  have T := (analyticOn_iff_differentiableOn hU).mpr hf
  have T2 : ContDiffOn ℂ 1 f U :=
      DifferentiableOn.contDiffOn hf hU
  have T3 : ContinuousOn (fun x ↦ ((deriv f) x)) U := by
    apply T2.continuousOn_deriv_of_isOpen hU (by simp)
  have T4 := T3.continuousAt U_in_filter
  have T5 : (deriv f) =O[𝓝 p] (1 : ℂ → ℂ) :=
    T4.norm.isBoundedUnder_le.isBigO_one ℂ
  exact Asymptotics.IsBigO.mono T5 inf_le_left

theorem derivative_const_plus_product {g : ℂ → ℂ} (A p x : ℂ) (hg : DifferentiableAt ℂ g x) :
    deriv ((fun _ ↦ A) + g * fun s ↦ s - p) x = deriv g x * (x - p) + g x := by
  rw [deriv_add (by fun_prop) (by fun_prop), deriv_const, deriv_mul hg (by fun_prop)]
  simp

lemma deriv_inv_sub {x p : ℂ} (hp : x ≠ p) :
  deriv (fun z => (z - p)⁻¹) x =  -((x - p) ^ 2)⁻¹ := by
  rw [deriv_fun_inv'' (by fun_prop) (by grind)]
  simp
  field

theorem deriv_f_minus_A_inv_sub_clean (f : ℂ → ℂ) (A x p : ℂ)
    (hf : DifferentiableAt ℂ f x) (hp : x ≠ p) :
    deriv (f  - (fun z ↦ A * (z - p)⁻¹)) x = deriv f x + A * ((x - p) ^ 2)⁻¹ := by
  have h1 : DifferentiableAt ℂ (fun z => (z - p)⁻¹) x := by
    fun_prop (disch := grind)
  rw [deriv_sub hf (h1.const_mul A), deriv_const_mul A h1, deriv_inv_sub hp]
  ring

theorem nonZeroOfBddAbove {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, IsOpen V ∧ ∀ s ∈ V \ {p}, f s ≠ 0 := by

  have h_decomp : ∀ s, f s = (f s - A * (s - p)⁻¹) + A * (s - p)⁻¹ := by
    intro s
    ring
                                      
  obtain ⟨M, hM⟩ := f_near_p

  have A_norm_pos : 0 < ‖A‖ := norm_pos_iff.mpr A_ne_zero
                                                                        
  let δ := ‖A‖ / (‖M‖ + 1)
  have δ_pos : 0 < δ := by
    refine div_pos A_norm_pos (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)
                                                                            
  obtain ⟨V, hV_open, hV_mem, hV_sub⟩ : ∃ V, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∩ Metric.ball p δ := by
                                     
    obtain ⟨W, hW_sub, hW_open, hW_mem⟩ := mem_nhds_iff.mp U_in_nhds
    let V := W ∩ Metric.ball p δ
    have VNp : V ∈ 𝓝 p := (𝓝 p).inter_mem (IsOpen.mem_nhds hW_open hW_mem)
      (Metric.ball_mem_nhds p δ_pos)
    exact ⟨V, IsOpen.inter hW_open Metric.isOpen_ball, mem_of_mem_nhds VNp,
      inter_subset_inter_left _ hW_sub⟩
  use V, mem_nhds_iff.mpr ⟨V, subset_refl V, hV_open, hV_mem⟩, hV_open
                    
  intro s hs
  have hs_in_U : s ∈ U := hV_sub hs.1 |>.1
  have hs_near_p : dist s p < δ := hV_sub hs.1 |>.2
  have hs_ne_p : s ≠ p := hs.2
                                                              
  rw [h_decomp s]
                                 
  have bound_first : ‖f s - A * (s - p)⁻¹‖ ≤ M := by
    apply hM
    exact ⟨s, ⟨hs_in_U, hs_ne_p⟩, rfl⟩
                                      
  have large_second : ‖M‖ + 1 < ‖A * (s - p)⁻¹‖ := by
    rw [norm_mul, norm_inv, ← div_eq_mul_inv]
    rw [lt_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs_ne_p))]
    rw [mul_comm, ← lt_div_iff₀ (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)]
    rw [dist_eq_norm_sub] at hs_near_p
    exact hs_near_p
                                                
  by_contra h_zero
                                                                  
  rw [add_eq_zero_iff_eq_neg] at h_zero
  rw [h_zero, norm_neg] at bound_first
                                    
  have : ‖M‖ + 1 < ‖M‖ := (lt_of_lt_of_le (lt_of_lt_of_le large_second bound_first)
    (Real.le_norm_self M))
  norm_num at this

theorem logDerivResidue' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_is_open : IsOpen U)
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by

  have simpleHolo : HolomorphicOn (fun s ↦ A / (s - p)) (U \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by rw [sub_ne_zero]; exact hx
    · rintro s ⟨_, hs⟩ ; exact hs

  have f_minus_pole_is_holomorphic : HolomorphicOn (f - (fun s ↦ A * (s - p)⁻¹)) (U \ {p}) := by
    exact (DifferentiableOn.sub_iff_right holc).mpr simpleHolo

  let ⟨g, ⟨g_is_holomorphic, g_is_f_minus_pole⟩⟩ := existsDifferentiableOn_of_bddAbove
    U_in_nhds f_minus_pole_is_holomorphic f_near_p

  let h := (fun _ ↦ A) + g * (fun (s : ℂ) ↦ (s - p))

  have linear_is_holomorphic : HolomorphicOn (fun (s : ℂ ) ↦ (s - p)) U := by
    exact DifferentiableOn.sub_const differentiableOn_id p

  have h_is_holomorphic : HolomorphicOn h U := by
    have T := DifferentiableOn.mul g_is_holomorphic linear_is_holomorphic
    exact DifferentiableOn.const_add A T

  have h_continuous : ContinuousOn h U :=
    by exact DifferentiableOn.continuousOn h_is_holomorphic

  have deriv_h_identity : ∀x ∈ (U \ {p}), (deriv h) x = f x + (deriv f x) * (x - p) := by
    intro x x_in_u_not_p
    have x_in_u : x ∈ U := by exact Set.mem_of_mem_sdiff x_in_u_not_p
    have x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp x_in_u_not_p).2

    have weird : U ∈ 𝓝 x := by
      exact IsOpen.mem_nhds (U_is_open) (x_in_u)

    rw [derivative_const_plus_product, ← g_is_f_minus_pole x_in_u_not_p,
      ← deriv_eqOn_of_eqOn_punctured _ _ U p U_is_open g_is_f_minus_pole x_in_u_not_p,
      deriv_f_minus_A_inv_sub_clean]
    · simp only [Pi.sub_apply]
      have := sub_ne_zero_of_ne x_not_p
      field_simp
      ring
    · apply holc.differentiableAt
      exact Filter.inter_mem weird <| compl_singleton_mem_nhds x_not_p
    · exact x_not_p
    · exact g_is_holomorphic.differentiableAt weird
  have h_identity : ∀x ∈ (U \ {p}), h x = (f x) * (x - p)  := by
    intro x x_in_u_not_p
    have hyp_x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp x_in_u_not_p).2
    simp only [h, Pi.add_apply, Pi.mul_apply]
    rw [← g_is_f_minus_pole x_in_u_not_p]
    simp only [Pi.sub_apply]
    field [sub_ne_zero.mpr hyp_x_not_p]
  have log_deriv_f_plus_pole_equal_log_deriv_h :
      EqOn (deriv f * f⁻¹ + fun s ↦ (s - p)⁻¹) ((deriv h) * h⁻¹) (U \ {p}) := by
    simp only [Set.mem_sdiff, mem_singleton_iff, ne_eq, and_imp, Function.comp_apply, Pi.sub_apply,
      DifferentiableOn.sub_iff_right, differentiableOn_const, DifferentiableOn.fun_sub_iff_left,
      holc] at *
    intro x hyp_x
    have x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp hyp_x).2
    have x_in_u : x ∈ U := by exact Set.mem_of_mem_sdiff hyp_x
    simp only [Pi.add_apply, Pi.mul_apply, Pi.inv_apply]
    rw [deriv_h_identity _ x_in_u x_not_p, h_identity _ x_in_u x_not_p]

    field [sub_ne_zero.mpr x_not_p, non_zero x (x_in_u) x_not_p]
  have h_inv_bounded :
      h⁻¹ =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    have : ContinuousAt h⁻¹ p := by
      apply ContinuousOn.continuousAt h_continuous U_in_nhds |>.inv₀
      simp [h, A_ne_zero]
    exact Asymptotics.IsBigO.mono (this.norm.isBoundedUnder_le.isBigO_one ℂ) inf_le_left

  have h_deriv_bounded :
        (deriv h) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
          analytic_deriv_bounded_near_point h U_is_open
            (by exact mem_of_mem_nhds U_in_nhds) h_is_holomorphic

  have h_log_deriv_bounded :
    ((deriv h) * h⁻¹) =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
      have T := Asymptotics.IsBigO.mul h_deriv_bounded h_inv_bounded
      exact IsBigO.of_const_mul_right T

  have u_not_p_in_filter : U \ {p} ∈ 𝓝[≠] p := by
    exact sdiff_mem_nhdsWithin_compl U_in_nhds {p}
  have T := Set.EqOn.eventuallyEq_of_mem log_deriv_f_plus_pole_equal_log_deriv_h u_not_p_in_filter
  exact EventuallyEq.trans_isBigO T h_log_deriv_bounded

theorem logDerivResidue {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    by
      let ⟨U', ⟨a,b,c⟩⟩ := mem_nhds_iff.mp U_in_nhds
      have W : (U' \ {p}) ⊆ U' := by
        exact Set.sdiff_subset

      have T : (U' \ {p}) ⊆ (U \ {p}) := by
        exact Set.sdiff_subset_sdiff a (subset_refl _)

      refine logDerivResidue' b ?_ ?_ (IsOpen.mem_nhds b c) A_ne_zero ?_
      · intro x hyp_x
        exact non_zero x <| T hyp_x
      · exact DifferentiableOn.mono holc T
      · exact (f_near_p.mono (image_mono (Set.sdiff_subset_sdiff a (subset_refl _))))

lemma BddAbove_to_IsBigO {f : ℂ → ℂ} {p : ℂ}
    {U : Set ℂ} (hU : U ∈ 𝓝 p) (bdd : BddAbove (norm ∘ f '' (U \ {p}))) :
    f =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
  dsimp [BddAbove, upperBounds] at bdd
  rcases bdd with ⟨C, hC⟩

  have h : ∀ x ∈ U \ {p}, ‖f x‖ ≤ C := by
    intro x hx
    have fx_is_norm : ‖f x‖ ∈ norm ∘ f ''(U \ {p}) := by
      exact ⟨x, hx, rfl⟩
    exact hC fx_is_norm

  rw [Asymptotics.isBigO_iff]
  use C
  rw [eventually_nhdsWithin_iff]
  simp only [Set.mem_sdiff, mem_singleton_iff, and_imp, mem_compl_iff, Pi.one_apply, one_mem,
    CStarRing.norm_of_mem_unitary, mul_one] at h ⊢
  filter_upwards [hU] using h

theorem logDerivResidue'' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, BddAbove (norm ∘ (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) '' (V \ {p})) := by
  apply IsBigO_to_BddAbove
  exact logDerivResidue non_zero holc U_in_nhds A_ne_zero f_near_p


theorem riemannZetaLogDerivResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (-(ζ' / ζ) - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  obtain ⟨U,U_in_nhds, hU⟩ := riemannZetaResidue
  have hU' : BddAbove (norm ∘ (ζ - fun s ↦ 1 * (s - 1)⁻¹) '' (U \ {1})) := by
    simp only [Function.comp_apply, Pi.sub_apply, one_mul] at hU ⊢
    exact hU
  obtain ⟨V,V_in_nhds, V_is_open, hV⟩ := nonZeroOfBddAbove U_in_nhds one_ne_zero hU'
  let W := V ∩ interior U
  have hW : ∀ s ∈ W \ {1}, ζ s ≠ 0 := by
    intro s hs
    have s_in_V_diff : s ∈ V \ {1} := ⟨hs.1.1, hs.2⟩
    exact hV s s_in_V_diff
  have ζ_holc: HolomorphicOn ζ (W \ {1}) := by
    intro y hy
    simp only [Set.mem_sdiff, mem_singleton_iff] at hy
    refine DifferentiableAt.differentiableWithinAt ?_
    apply differentiableAt_riemannZeta hy.2
  have W_in_nhds : W ∈ 𝓝 1 := by
    refine inter_mem V_in_nhds ?_
    exact interior_mem_nhds.mpr U_in_nhds
  have := logDerivResidue'' hW ζ_holc W_in_nhds one_ne_zero
  have HW : BddAbove (norm ∘ (ζ - fun s ↦ (s - 1)⁻¹) '' (W \ {1})) := by
    obtain ⟨c, hc⟩ := bddAbove_def.mp hU
    apply bddAbove_def.mpr
    use c
    rintro y ⟨x, x_in_W, fxy⟩
    apply hc
    exact ⟨x, ⟨interior_subset x_in_W.1.2, x_in_W.2⟩, fxy⟩
  simp only [one_mul] at this
  have aux: ∀ a, ‖-(deriv ζ a / ζ a) - (a - 1)⁻¹‖ = ‖(deriv ζ a / ζ a) + (a - 1)⁻¹‖ := by
    intro a
    calc ‖-(deriv ζ a / ζ a) - (a - 1)⁻¹‖
         = ‖-((deriv ζ a / ζ a) + (a - 1)⁻¹)‖ := by ring_nf
       _ = ‖(deriv ζ a / ζ a) + (a - 1)⁻¹‖ := by rw [norm_neg]
  simp only [Function.comp_apply, Pi.sub_apply] at hU
  simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, aux]
  apply this HW

theorem riemannZetaLogDerivResidueBigO :
    (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
  obtain ⟨U, hU, bdd⟩ := riemannZetaLogDerivResidue
  convert (preTransparency := .instances) BddAbove_to_IsBigO hU bdd using 2
  rw [neg_div]


local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

































































































































open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
                                                              



end Erdos970

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.PNT2_LogDerivative
namespace Erdos970




open _root_.Filter _root_.Metric _root_.Set _root_.Bornology _root_.Function


open _root_.Classical

lemma lem_frho_zero (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (_hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    f ρ = 0 := h_rho_in_KfR1.2

lemma lem_m_rho_is_nat (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hR_lt_1 : R < 1) :
    ∀ (ρ : ℂ) (_h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f),
    analyticOrderAt f ρ ≠ ⊤ := by
  intro ρ h_rho_in_KfR1
                                           
  have hρ_closed_R1 : ρ ∈ Metric.closedBall (0 : ℂ) R1 := h_rho_in_KfR1.1
                                    
  have hR1_le_R : R1 ≤ R := by linarith
  have hR1_lt_one : R1 < 1 := by linarith
                       
  have hρ_ball1 : ρ ∈ Metric.ball (0 : ℂ) 1 := by
    have hdist_le : dist ρ (0 : ℂ) ≤ R1 := (Metric.mem_closedBall.mp hρ_closed_R1)
    have hdist_lt : dist ρ (0 : ℂ) < 1 := by linarith
    simpa [Metric.mem_ball] using hdist_lt
                       
  have hf_at_ρ : AnalyticAt ℂ f ρ := by
                                      
    have hsubset : Metric.closedBall (0 : ℂ) R1 ⊆ Metric.closedBall (0 : ℂ) 1 :=
      Metric.closedBall_subset_closedBall (le_of_lt hR1_lt_one)
    have hρ_closed1 : ρ ∈ Metric.closedBall (0 : ℂ) 1 := hsubset hρ_closed_R1
    exact h_f_analytic ρ hρ_closed1
                                                    
  by_contra htop
                                                           
  have h_eventually_zero : ∀ᶠ z in nhds ρ, f z = 0 := by
    have h_equiv : (analyticOrderAt f ρ = ⊤ ↔ ∀ᶠ z in nhds ρ, f z = 0) := by
      simp [analyticOrderAt, hf_at_ρ]
    exact h_equiv.mp (by simpa using htop)
                                                     
  have hf_on_ball : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      (Metric.ball_subset_closedBall : Metric.ball (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1) hz
    exact h_f_analytic z hz'
                                  
  have h_preconn : IsPreconnected (Metric.ball (0 : ℂ) 1) :=
    (Metric.isConnected_ball (by exact (zero_lt_one : (0 : ℝ) < 1))).isPreconnected
                                                  
  have h_eqOn_zero : Set.EqOn f 0 (Metric.ball (0 : ℂ) 1) :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hf_on_ball h_preconn hρ_ball1
      h_eventually_zero
                                 
  have h0_in_ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simp [Metric.mem_ball]
  have : f 0 = 0 := by
    have h := h_eqOn_zero h0_in_ball
    simpa [Pi.zero_apply] using h
  exact h_f_nonzero_at_zero this

lemma analyticOrderAt_ge_one_of_zero (f : ℂ → ℂ) (z : ℂ) (hf : AnalyticAt ℂ f z) (hz : f z = 0) (hfinite : analyticOrderAt f z ≠ ⊤) : analyticOrderAt f z ≥ 1 := by
                                                                 
  have h_order_ne_zero : analyticOrderAt f z ≠ 0 := by
    intro h_order_zero
                                                              
    have h_f_ne_zero : f z ≠ 0 := by
      rw [← AnalyticAt.analyticOrderAt_eq_zero hf]
      exact h_order_zero
                                    
    exact h_f_ne_zero hz
                                                                      
  cases' h : analyticOrderAt f z with n
  ·                                 
                               
    rw [h] at hfinite
    exact False.elim (hfinite rfl)
  ·                                                 

    rw [h] at h_order_ne_zero
    have n_ne_zero : n ≠ 0 := by
      intro n_zero
      rw [n_zero, Nat.cast_zero] at h_order_ne_zero
      exact h_order_ne_zero rfl
                                 
    have n_ge_one : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr n_ne_zero
                            
    exact Nat.cast_le.mpr n_ge_one

lemma lem_m_rho_ge_1 (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hR_lt_1 : R < 1) :
    ∀ (ρ : ℂ) (_h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f),
    analyticOrderAt f ρ ≥ 1 := by
  intro ρ h_rho_in_KfR1
                                                     
  have h_f_rho_zero : f ρ = 0 := lem_frho_zero R R1 hR1_pos hR1_lt_R f h_f_analytic ρ h_rho_in_KfR1
                                                        
  have h_order_finite : analyticOrderAt f ρ ≠ ⊤ := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 ρ h_rho_in_KfR1
                       
  have h_f_analytic_at_rho : AnalyticAt ℂ f ρ := by
    apply h_f_analytic
                                            
    have h_R1_lt_1 : R1 < 1 := by linarith
    have h_rho_in_R1 : ρ ∈ Metric.closedBall 0 R1 := h_rho_in_KfR1.1
    exact Metric.closedBall_subset_closedBall (le_of_lt h_R1_lt_1) h_rho_in_R1
                                                                          
  exact analyticOrderAt_ge_one_of_zero f ρ h_f_analytic_at_rho h_f_rho_zero h_order_finite

































































































variable {R R1 r B : ℝ} {f : ℂ → ℂ} {h_σ : ℂ → (ℂ → ℂ)}
variable (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
variable (hR1_pos : 0 < R1)
variable (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
variable (h_f_zero : f 0 = 1)
variable (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
variable (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)


























































































end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterLogGrowth
namespace OAI

/-! One absolute constant in the nonprincipal disk bounds, with all
modulus and height dependence kept in log(q*(abs(t)+2)). -/

namespace TwoPointCorrelations







lemma mrtCharacterLogDerivativeConstant_pos : 0 < mrtCharacterLogDerivativeConstant := by
  have hl : 0 < Real.log ((15/16:ℝ)/(7/8)) := Real.log_pos (by norm_num)
  unfold mrtCharacterLogDerivativeConstant
  positivity



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterMovingCenter
namespace OAI

/-! Normalization of Dirichlet L-functions on a moving disk. The radius is
an explicit parameter; all characters, including the principal character,
are allowed when the disk stays away from the real axis. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Filter
open scoped _root_.BigOperators _root_.Classical _root_.Topology

variable {q : ℕ} [NeZero q]



lemma mrt_moving_point_ne_one {r t : ℝ} (hr : 0 < r) (ht : 3 * r < |t|)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : mrtMovingPoint r t z ≠ 1 := by
  intro he
  have him := congrArg Complex.im he
  have him' : t + 3 * r * z.im = 0 := by
    simpa [mrtMovingPoint, Complex.mul_im] using him
  have hzi := (Complex.abs_im_le_norm z).trans hz
  have heq : t = -(3 * r * z.im) := by linarith
  rw [heq, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < 3 * r)] at ht
  nlinarith

lemma mrt_moving_point_center_ne_zero (χ : DirichletCharacter ℂ q)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    DirichletCharacter.LFunction χ (mrtMovingPoint r t 0) ≠ 0 := by
  apply χ.LFunction_ne_zero_of_one_le_re
  · right
    intro h
    have hh := congrArg Complex.re h
    simp [mrtMovingPoint] at hh
    linarith
  · simp [mrtMovingPoint]
    linarith

lemma mrt_moving_LFunction_zero (χ : DirichletCharacter ℂ q)
    {r : ℝ} (hr : 0 < r) (t : ℝ) : mrtMovingLFunction χ r t 0 = 1 :=
  div_self (mrt_moving_point_center_ne_zero χ hr t)

lemma mrt_moving_LFunction_analytic (χ : DirichletCharacter ℂ q)
    {r t : ℝ} (hr : 0 < r) (ht : 3 * r < |t|) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ (mrtMovingLFunction χ r t) z := by
  intro z hz
  have hn := mrt_moving_point_ne_one hr ht (by simpa using hz)
  have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := by
    intro w hw
    exact (χ.differentiableAt_LFunction w (Or.inl hw)).differentiableWithinAt
  have ha := hd.analyticAt (isOpen_compl_singleton.mem_nhds hn)
  have hp : AnalyticAt ℂ (mrtMovingPoint r t) z := by
    apply Differentiable.analyticAt
    unfold mrtMovingPoint
    fun_prop
  exact (ha.comp hp).div_const


lemma mrt_moving_LFunction_deriv (χ : DirichletCharacter ℂ q)
    {r t : ℝ} (hr : 0 < r) (ht : 3 * r < |t|)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    deriv (mrtMovingLFunction χ r t) z =
      (deriv (DirichletCharacter.LFunction χ) (mrtMovingPoint r t z) *
        ((3 * r : ℝ) : ℂ)) /
        DirichletCharacter.LFunction χ (mrtMovingPoint r t 0) := by
  have hp : HasDerivAt (mrtMovingPoint r t) ((3 * r : ℝ) : ℂ) z := by
    exact (hasDerivAt_const_mul ((3 * r : ℝ) : ℂ)).const_add
      (((1 + 2 * r : ℝ) : ℂ) + Complex.I * (t : ℂ))
  have hn := mrt_moving_point_ne_one hr ht hz
  exact (((χ.differentiableAt_LFunction _ (Or.inl hn)).hasDerivAt.comp z hp).div_const
    (DirichletCharacter.LFunction χ (mrtMovingPoint r t 0))).deriv

lemma mrt_moving_logderiv_eq (χ : DirichletCharacter ℂ q)
    {r t : ℝ} (hr : 0 < r) (ht : 3 * r < |t|)
    {z : ℂ} (hz : ‖z‖ ≤ 1)
    (hn : DirichletCharacter.LFunction χ (mrtMovingPoint r t z) ≠ 0) :
    deriv (mrtMovingLFunction χ r t) z / mrtMovingLFunction χ r t z =
      ((3 * r : ℝ) : ℂ) *
        (deriv (DirichletCharacter.LFunction χ) (mrtMovingPoint r t z) /
          DirichletCharacter.LFunction χ (mrtMovingPoint r t z)) := by
  rw [mrt_moving_LFunction_deriv χ hr ht hz]
  unfold mrtMovingLFunction
  field_simp [hn, mrt_moving_point_center_ne_zero χ hr t]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingZeroTerms
namespace OAI

/-! The one-zero de la Vallée Poussin estimate on a shrinking disk.
All constants retain the physical radius and logarithmic growth budget. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.BigOperators _root_.Classical

variable {q : ℕ} [NeZero q]


lemma mrt_moving_real_point {r : ℝ} (hr : 0 < r) (t σ : ℝ) :
    mrtMovingPoint r t (mrtMovingRealPoint r σ) = (σ : ℂ) + Complex.I * (t : ℂ) := by
  unfold mrtMovingPoint mrtMovingRealPoint
  push_cast
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp [hrC]
  ring

lemma mrt_moving_real_point_norm {r σ : ℝ} (hr : 0 < r)
    (hσ : 1 - r / 4 ≤ σ) (hσ2 : σ ≤ 1 + r) :
    ‖mrtMovingRealPoint r σ‖ ≤ 3 / 4 := by
  rw [mrtMovingRealPoint, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 3 * r)).mpr
    nlinarith
  · apply (div_le_iff₀ (by positivity : 0 < 3 * r)).mpr
    nlinarith

lemma mrt_moving_zero_physical (χ : DirichletCharacter ℂ q)
    {r t : ℝ} (hr : 0 < r) {ρ : ℂ}
    (hρ : ρ ∈ mrtDiskZeros (mrtMovingLFunction χ r t)) :
    DirichletCharacter.LFunction χ (mrtMovingPoint r t ρ) = 0 := by
  exact (div_eq_zero_iff.mp hρ.2).resolve_right (mrt_moving_point_center_ne_zero χ hr t)

lemma mrt_moving_zero_re (χ : DirichletCharacter ℂ q)
    {r t : ℝ} (hr : 0 < r) (ht : 3 * r < |t|) {ρ : ℂ}
    (hρ : ρ ∈ mrtDiskZeros (mrtMovingLFunction χ r t)) : ρ.re < -(2 / 3 : ℝ) := by
  have hρn : ‖ρ‖ ≤ 7 / 8 := by simpa using hρ.1
  have hn := mrt_moving_point_ne_one hr ht (hρn.trans (by norm_num))
  have hzero := mrt_moving_zero_physical χ hr hρ
  by_contra! hh
  have hσ : 1 ≤ (mrtMovingPoint r t ρ).re := by
    simp only [mrtMovingPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    nlinarith
  exact χ.LFunction_ne_zero_of_one_le_re (Or.inr hn) hσ hzero

lemma mrt_moving_zero_term_nonneg (χ : DirichletCharacter ℂ q)
    {r t σ : ℝ} (hr : 0 < r) (ht : 3 * r < |t|) (hσ : 1 < σ)
    {ρ : ℂ} (hρ : ρ ∈ mrtDiskZeros (mrtMovingLFunction χ r t)) :
    0 ≤ (((analyticOrderAt (mrtMovingLFunction χ r t) ρ).toNat : ℂ) /
      (mrtMovingRealPoint r σ - ρ)).re := by
  have hh := mrt_moving_zero_re χ hr ht hρ
  have hd : 0 ≤ (mrtMovingRealPoint r σ - ρ).re := by
    simp only [Complex.sub_re, mrtMovingRealPoint, Complex.ofReal_re]
    have hfrac : -(2 / 3 : ℝ) ≤ (σ - 1 - 2 * r) / (3 * r) := by
      apply (le_div_iff₀ (by positivity : 0 < 3 * r)).mpr
      nlinarith
    linarith
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hd) (Complex.normSq_nonneg _)

/-- Dropping the nonnegative zero terms gives an upper bound for `-L'/L`. -/
theorem mrt_moving_neg_logderiv (χ : DirichletCharacter ℂ q)
    {r t B σ : ℝ} (hr : 0 < r) (ht : 3 * r < |t|) (hB : 0 < B)
    (hg : ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
      ‖mrtMovingLFunction χ r t z‖ ≤ Real.exp B)
    (hσ : 1 < σ) (hσ2 : σ ≤ 1 + r) :
    (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
      DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))).re ≤
        mrtCharacterLogDerivativeConstant * B / (3 * r) := by
  let f := mrtMovingLFunction χ r t
  have hf := mrt_moving_LFunction_analytic χ hr ht
  have h0 := mrt_moving_LFunction_zero χ hr t
  have hz := mrt_moving_real_point_norm hr (by linarith) hσ2
  have hn : DirichletCharacter.LFunction χ (mrtMovingPoint r t (mrtMovingRealPoint r σ)) ≠ 0 := by
    rw [mrt_moving_real_point hr]
    exact χ.LFunction_ne_zero_of_one_le_re (Or.inr (by
      intro he; have hre := congrArg Complex.re he; simp at hre; linarith)) (by simpa using hσ.le)
  have hfn : f (mrtMovingRealPoint r σ) ≠ 0 :=
    div_ne_zero hn (mrt_moving_point_center_ne_zero χ hr t)
  have he := mrt_disk_logderiv f hf h0 hB hg hz hfn
  have hlow := (abs_le.mp ((Complex.abs_re_le_norm _).trans he)).1
  have hs : 0 ≤ ∑ ρ ∈ (mrtDiskZeros_finite f hf h0).toFinset,
      (((analyticOrderAt f ρ).toNat : ℂ) / (mrtMovingRealPoint r σ - ρ)).re := by
    apply sum_nonneg
    intro ρ hρ
    exact mrt_moving_zero_term_nonneg χ hr ht hσ
      ((mrtDiskZeros_finite f hf h0).mem_toFinset.mp hρ)
  rw [Complex.sub_re, Complex.re_sum] at hlow
  rw [mrt_moving_logderiv_eq χ hr ht (hz.trans (by norm_num)) hn,
    mrt_moving_real_point hr] at hlow
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hlow
  simp only [neg_div, Complex.neg_re]
  apply (le_div_iff₀ (by positivity : 0 < 3 * r)).mpr
  nlinarith only [hlow, hs]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingSelectedZero
namespace OAI

/-! A selected zero supplies its entire reciprocal horizontal distance in
the shrinking-disk logarithmic derivative. This is the quantitative input
for the three-factor positivity contradiction. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.BigOperators _root_.Classical

lemma mrt_disk_zero_multiplicity (f : ℂ → ℂ)
    (hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h0 : f 0 = 1) {ρ : ℂ} (hρ : ρ ∈ mrtDiskZeros f) :
    1 ≤ (analyticOrderAt f ρ).toNat := by
  have hfinite := Erdos970.lem_m_rho_is_nat (15 / 16) (7 / 8)
    (by norm_num) (by norm_num) f hf (by rw [h0]; exact one_ne_zero)
    (by norm_num) ρ hρ
  have hpos := Erdos970.lem_m_rho_ge_1 (15 / 16) (7 / 8)
    (by norm_num) (by norm_num) f hf (by rw [h0]; exact one_ne_zero)
    (by norm_num) ρ hρ
  simpa using ENat.toNat_le_toNat hpos hfinite

variable {q : ℕ} [NeZero q]

lemma mrt_moving_real_zero_mem (χ : DirichletCharacter ℂ q)
    {r t β : ℝ} (hr : 0 < r) (hβ : 1 - r / 4 ≤ β) (hβ1 : β ≤ 1)
    (hz : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) = 0) :
    mrtMovingRealPoint r β ∈ mrtDiskZeros (mrtMovingLFunction χ r t) := by
  refine ⟨?_, ?_⟩
  · have hn := mrt_moving_real_point_norm hr hβ (show β ≤ 1 + r by linarith)
    simpa using hn.trans (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8)
  · change DirichletCharacter.LFunction χ
      (mrtMovingPoint r t (mrtMovingRealPoint r β)) / _ = 0
    rw [mrt_moving_real_point hr, hz, zero_div]

lemma mrt_moving_selected_zero_sum (χ : DirichletCharacter ℂ q)
    {r t σ β : ℝ} (hr : 0 < r) (ht : 3 * r < |t|) (hσ : 1 < σ)
    (hβ : 1 - r / 4 ≤ β) (hβ1 : β ≤ 1)
    (hz : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) = 0) :
    (3 * r) / (σ - β) ≤
      ∑ ρ ∈ (mrtDiskZeros_finite (mrtMovingLFunction χ r t)
        (mrt_moving_LFunction_analytic χ hr ht) (mrt_moving_LFunction_zero χ hr t)).toFinset,
        (((analyticOrderAt (mrtMovingLFunction χ r t) ρ).toNat : ℂ) /
          (mrtMovingRealPoint r σ - ρ)).re := by
  let f := mrtMovingLFunction χ r t
  have hf := mrt_moving_LFunction_analytic χ hr ht
  have h0 := mrt_moving_LFunction_zero χ hr t
  let w := mrtMovingRealPoint r β
  have hw : w ∈ mrtDiskZeros f := mrt_moving_real_zero_mem χ hr hβ hβ1 hz
  have hm := mrt_disk_zero_multiplicity f hf h0 hw
  have hd : 0 < σ - β := by linarith
  have h3 : 0 < 3 * r := by positivity
  have hdiff : mrtMovingRealPoint r σ - w = (((σ - β) / (3 * r) : ℝ) : ℂ) := by
    dsimp [w, mrtMovingRealPoint]
    push_cast
    ring
  have hterm : (3 * r) / (σ - β) ≤
      (((analyticOrderAt f w).toNat : ℂ) / (mrtMovingRealPoint r σ - w)).re := by
    rw [hdiff]
    change (3 * r) / (σ - β) ≤
      ((((analyticOrderAt f w).toNat : ℝ) : ℂ) / (((σ - β) / (3 * r) : ℝ) : ℂ)).re
    rw [← Complex.ofReal_div, Complex.ofReal_re]
    calc
      _ = 1 / ((σ - β) / (3 * r)) := by field_simp [hr.ne', hd.ne']
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hm) (div_pos hd h3).le
  exact hterm.trans (single_le_sum
    (fun ρ hρ => mrt_moving_zero_term_nonneg χ hr ht hσ
      ((mrtDiskZeros_finite f hf h0).mem_toFinset.mp hρ))
    ((mrtDiskZeros_finite f hf h0).mem_toFinset.mpr hw))

/-- The same bound with the full negative reciprocal of a selected zero. -/
theorem mrt_moving_neg_logderiv_of_zero (χ : DirichletCharacter ℂ q)
    {r t B σ β : ℝ} (hr : 0 < r) (ht : 3 * r < |t|) (hB : 0 < B)
    (hg : ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
      ‖mrtMovingLFunction χ r t z‖ ≤ Real.exp B)
    (hσ : 1 < σ) (hσ2 : σ ≤ 1 + r)
    (hβ : 1 - r / 4 ≤ β) (hβ1 : β ≤ 1)
    (hz : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) = 0) :
    (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
      DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))).re ≤
        mrtCharacterLogDerivativeConstant * B / (3 * r) - 1 / (σ - β) := by
  let f := mrtMovingLFunction χ r t
  have hf := mrt_moving_LFunction_analytic χ hr ht
  have h0 := mrt_moving_LFunction_zero χ hr t
  have hzn := mrt_moving_real_point_norm hr (by linarith) hσ2
  have hn : DirichletCharacter.LFunction χ (mrtMovingPoint r t (mrtMovingRealPoint r σ)) ≠ 0 := by
    rw [mrt_moving_real_point hr]
    exact χ.LFunction_ne_zero_of_one_le_re (Or.inr (by
      intro he; have hre := congrArg Complex.re he; simp at hre; linarith)) (by simpa using hσ.le)
  have hfn : f (mrtMovingRealPoint r σ) ≠ 0 :=
    div_ne_zero hn (mrt_moving_point_center_ne_zero χ hr t)
  have he := mrt_disk_logderiv f hf h0 hB hg hzn hfn
  have hlow := (abs_le.mp ((Complex.abs_re_le_norm _).trans he)).1
  have hs := mrt_moving_selected_zero_sum χ hr ht hσ hβ hβ1 hz
  rw [Complex.sub_re, Complex.re_sum] at hlow
  rw [mrt_moving_logderiv_eq χ hr ht (hzn.trans (by norm_num)) hn,
    mrt_moving_real_point hr] at hlow
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hlow
  simp only [neg_div, Complex.neg_re]
  have h3 : 0 < 3 * r := by positivity
  have hdist : σ - β ≠ 0 := ne_of_gt (by linarith)
  have heq : mrtCharacterLogDerivativeConstant * B / (3 * r) - 1 / (σ - β) =
      (mrtCharacterLogDerivativeConstant * B - (3 * r) / (σ - β)) / (3 * r) := by
    field_simp [hr.ne', hdist]
  rw [heq]
  apply (le_div_iff₀ h3).mpr
  nlinarith only [hlow, hs]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterPositivity
namespace OAI

/-! The de la Vallée Poussin positivity inequality for arbitrary positive modulus.
The proof is termwise and uses the actual Mangoldt Dirichlet series.
It does not assume a zero-free region or a prime-number estimate.
-/

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction
open scoped _root_.BigOperators _root_.Classical _root_.LSeries.notation

variable {q : ℕ}


lemma mrtCharacter_three_four_one_nonneg {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have hn : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have := sq_le_sq₀ (norm_nonneg z) zero_le_one |>.mpr hz
    simpa only [Complex.sq_norm, Complex.normSq_apply, ← sq, one_pow] using this
  have hs := sq_nonneg (z.re + 1)
  simp only [pow_two, Complex.mul_re]
  nlinarith

lemma mrtCharacter_phase_norm (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    ‖(n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp

lemma mrtCharacter_twisted_phase_norm (χ : DirichletCharacter ℂ q)
    (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    ‖χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ 1 := by
  rw [norm_mul, mrtCharacter_phase_norm n hn t, mul_one]
  exact χ.norm_le_one _

lemma mrtCharacter_real_mangoldt_term (σ : ℝ) (n : ℕ) (hn : n ≠ 0) :
    LSeries.term (fun m => (vonMangoldt m : ℂ)) (σ : ℂ) n =
      ((vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg,
    ← Complex.ofReal_neg, ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow n.cast_nonneg, Complex.ofReal_mul]

lemma mrtCharacter_twisted_mangoldt_term (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (n : ℕ) (hn : n ≠ 0) :
    LSeries.term (mrtCharacterMangoldtTwist χ) ((σ : ℂ) + Complex.I * (t : ℂ)) n =
      ((vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
        (χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, neg_add,
    Complex.cpow_add _ _ (by exact_mod_cast hn)]
  rw [← Complex.ofReal_neg, ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow n.cast_nonneg]
  simp only [mrtCharacterMangoldtTwist, Complex.ofReal_mul]
  ring

lemma mrtCharacter_double_phase (χ : DirichletCharacter ℂ q) (n : ℕ) (t : ℝ) :
    (χ ^ 2) (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * ((2 * t : ℝ) : ℂ))) =
      (χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) ^ 2 := by
  rw [χ.pow_apply' (by decide : 2 ≠ 0)]
  rw [show -(Complex.I * ((2 * t : ℝ) : ℂ)) =
      (2 : ℕ) * (-(Complex.I * (t : ℂ))) by push_cast; ring,
    Complex.cpow_nat_mul, mul_pow]

lemma mrtCharacter_mangoldt_term_positivity (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (LSeries.term (fun m => (vonMangoldt m : ℂ)) (σ : ℂ) n).re +
      4 * (LSeries.term (mrtCharacterMangoldtTwist χ)
        ((σ : ℂ) + Complex.I * (t : ℂ)) n).re +
      (LSeries.term (mrtCharacterMangoldtTwist (χ ^ 2))
        ((σ : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ)) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero, Complex.zero_re, mul_zero, add_zero, le_refl]
  rw [mrtCharacter_real_mangoldt_term σ n hn,
    mrtCharacter_twisted_mangoldt_term χ σ t n hn,
    mrtCharacter_twisted_mangoldt_term (χ ^ 2) σ (2 * t) n hn,
    mrtCharacter_double_phase]
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hpoly := mrtCharacter_three_four_one_nonneg (mrtCharacter_twisted_phase_norm χ n hn t)
  simp only [Complex.mul_re] at hpoly
  have ha : 0 ≤ vonMangoldt n * (n : ℝ) ^ (-σ) :=
    mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg n.cast_nonneg _)
  nlinarith [mul_nonneg ha hpoly]

/-- Positivity of the three actual, absolutely convergent Mangoldt series. -/
theorem mrtCharacter_mangoldt_series_positivity (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (LSeries (fun m => (vonMangoldt m : ℂ)) (σ : ℂ)).re +
      4 * (LSeries (mrtCharacterMangoldtTwist χ) ((σ : ℂ) + Complex.I * (t : ℂ))).re +
      (LSeries (mrtCharacterMangoldtTwist (χ ^ 2))
        ((σ : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ))).re := by
  have hs0 : 1 < (σ : ℂ).re := hσ
  have hs1 : 1 < ((σ : ℂ) + Complex.I * (t : ℂ)).re := by simpa using hσ
  have hs2 : 1 < ((σ : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ)).re := by simpa using hσ
  have h0 := Complex.hasSum_re (LSeriesSummable_vonMangoldt hs0).LSeriesHasSum
  have h1 := Complex.hasSum_re (χ.LSeriesSummable_twist_vonMangoldt hs1).LSeriesHasSum
  have h2 := Complex.hasSum_re ((χ ^ 2).LSeriesSummable_twist_vonMangoldt hs2).LSeriesHasSum
  exact (((h0.mul_left 3).add (h1.mul_left 4)).add h2).nonneg
    (mrtCharacter_mangoldt_term_positivity χ σ t)

lemma mrtCharacter_twisted_series_logderiv [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (mrtCharacterMangoldtTwist χ) s =
      -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact χ.LSeries_twist_vonMangoldt_eq hs

/-- The general-character logarithmic-derivative inequality needed by the
quantitative zero-free-region proof. -/
theorem mrtCharacter_logderiv_positivity [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re +
      4 * (-deriv (DirichletCharacter.LFunction χ)
        ((σ : ℂ) + Complex.I * (t : ℂ)) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))).re +
      (-deriv (DirichletCharacter.LFunction (χ ^ 2))
        ((σ : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ)) /
        DirichletCharacter.LFunction (χ ^ 2)
          ((σ : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ))).re := by
  have h := mrtCharacter_mangoldt_series_positivity χ hσ t
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hσ,
    mrtCharacter_twisted_series_logderiv χ (by simpa using hσ),
    mrtCharacter_twisted_series_logderiv (χ ^ 2) (by simpa using hσ)] at h
  exact h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.Z0
namespace Erdos970

open _root_.Complex _root_.Topology _root_.Filter _root_.Interval _root_.Set _root_.Asymptotics

local notation (name := riemannzeta1) "ζ" => riemannZeta
local notation (name := derivriemannzeta1) "ζ'" => deriv riemannZeta

lemma Z0bound_aux :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) (fun (delta : ℝ) => -(ζ' / ζ) ((1 : ℂ) + delta) - (1 / (delta : ℂ))) (fun _ => (1 : ℂ)) := by

  let F := fun s : ℂ => -(ζ' / ζ) s - (s - 1)⁻¹

  have h_F_bigO : F =O[𝓝[≠] 1] (1 : ℂ → ℂ) := by
    have h_fun_eq : F = (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) := by
      ext s
      simp only [F, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, neg_div]
    rw [h_fun_eq]
    exact riemannZetaLogDerivResidueBigO

  let u := fun (delta : ℝ) => (1 : ℂ) + delta
  have h_tendsto : Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (𝓝[≠] 1) := by

    apply tendsto_inf.mpr
    constructor
    ·                                     
      have h_cont : Continuous u := continuous_const.add continuous_ofReal
                                                             
      have h_tendsto_nhds : Tendsto u (𝓝 0) (𝓝 (u 0)) := h_cont.continuousAt.tendsto
                                                                     
      simp only [u, Complex.ofReal_zero, add_zero] at h_tendsto_nhds

      exact h_tendsto_nhds.mono_left nhdsWithin_le_nhds
    ·                                                  
                                                      
      simp
                                                  
      filter_upwards [self_mem_nhdsWithin] with delta h_delta_pos
      simp only [u]

      refine add_ne_left.mpr ?_
      rw [Complex.ofReal_ne_zero]
      exact ne_of_gt h_delta_pos

  have h_comp := h_F_bigO.comp_tendsto h_tendsto

  convert (preTransparency := .instances) h_comp using 1
  ext delta
                                                           
  simp only [F, u, Function.comp_apply, Pi.div_apply]
  rw [inv_eq_one_div]
  aesop
  all_goals rfl

lemma Z0bound :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) (fun (delta : ℝ) => -logDerivZeta ((1 : ℂ) + delta) - (1 / (delta : ℂ))) (fun _ => (1 : ℂ)) := Z0bound_aux

end Erdos970

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.PNT4_ZeroFreeRegion
namespace Erdos970

































































lemma Z0boundRe :
Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) (fun (delta : ℝ) => (- (logDerivZeta ((1 : ℂ) + delta))).re - (1 / delta)) (fun _ => (1 : ℝ)) := by
                                              
  have h := Z0bound

  have h_eq : (fun (delta : ℝ) => (- (logDerivZeta ((1 : ℂ) + delta))).re - (1 / delta)) =
              (fun (delta : ℝ) => (-logDerivZeta ((1 : ℂ) + delta) - (1 / (delta : ℂ))).re) := by
    ext delta
    rw [Complex.sub_re, Complex.neg_re]
                                                 
    have : (1 / (delta : ℂ)).re = 1 / delta := by
      rw [Complex.div_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im]
      simp [Complex.normSq_ofReal]
    rw [this]

  rw [h_eq]

  rw [Asymptotics.isBigO_iff] at h ⊢
  obtain ⟨c, hc⟩ := h
  use c
  filter_upwards [hc] with delta h_delta
  have : ‖(1 : ℂ)‖ = (1 : ℝ) := by simp
  rw [this] at h_delta
  have : ‖(1 : ℝ)‖ = (1 : ℝ) := by simp
  rw [this]
  exact le_trans (Complex.abs_re_le_norm _) h_delta


lemma uniform_bound_Z0 : ∃ δ0 > 0, ∃ C0 ≥ 0, ∀ δ : ℝ, 0 < δ → δ < δ0 → (- (logDerivZeta ((1 : ℂ) + δ))).re ≤ 1 / δ + C0 := by
                                                             
  let f : ℝ → ℝ := fun δ => (- (logDerivZeta ((1 : ℂ) + δ))).re - (1 / δ)
                                           
  have hO := Z0boundRe
                                                                 
  rcases (Asymptotics.isBigO_iff).1 hO with ⟨c, hc⟩
                                                                                       
  have h1norm : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ‖f δ‖ ≤ c := by
                       
    have : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ‖f δ‖ ≤ c * ‖(1 : ℝ)‖ := hc
    refine this.mono ?_
    intro δ hδ
    simpa using (by simpa using hδ)
                                                                                 
  rcases (Filter.eventually_iff_exists_mem).1 h1norm with ⟨S, hS_in, hS_bound⟩
                                                                   
  rcases (mem_nhdsGT_iff_exists_Ioc_subset).1 hS_in with ⟨δ0, hδ0pos, hIoc_sub_S⟩
                                                                       
  refine ⟨δ0, hδ0pos, max c 0, le_max_right _ _, ?_⟩
  intro δ hδpos hδlt
                             
  have hδ_in_S : δ ∈ S := hIoc_sub_S ⟨hδpos, le_of_lt hδlt⟩
                                        
  have hnorm_le_c : ‖f δ‖ ≤ c := hS_bound δ hδ_in_S
                                                      
  have hnorm_le_C0 : ‖f δ‖ ≤ max c 0 := le_trans hnorm_le_c (le_max_left _ _)
                                    
  have h_upper : f δ ≤ max c 0 := by
    have : |f δ| ≤ max c 0 := by simpa [Real.norm_eq_abs] using hnorm_le_C0
    exact (abs_le.mp this).2
                                        
  have := (sub_le_iff_le_add).1 h_upper
  simpa [f, add_comm] using this













































































































































































































open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterHighZeros
namespace OAI

/-! A classical logarithmic zero-free strip, uniform in the character modulus.
This is the high-height part only; it makes no Vinogradov--Korobov claim. -/

namespace TwoPointCorrelations

open _root_.Complex
open scoped _root_.Classical



lemma mrt_character_zero_free_arithmetic {D H delta eps : ℝ}
    (hD : 0 < D) (hH : 0 < H) (hd : delta = 1 / (10 * D * H))
    (he : 0 ≤ eps) (heu : eps ≤ delta / 4) :
    3 / delta + D * H - 4 / (delta + eps) < 0 := by
  have hdp : 0 < delta := by rw [hd]; positivity
  have hde : 0 < delta + eps := by linarith
  have hinv : 16 / (5 * delta) ≤ 4 / (delta + eps) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 5 * delta) hde).mpr
    nlinarith
  have heq : 3 / delta + D * H - 16 / (5 * delta) = -(D * H) := by
    rw [hd]
    field_simp [hD.ne', hH.ne']
    ring
  have hle : 3 / delta + D * H - 4 / (delta + eps) ≤
      3 / delta + D * H - 16 / (5 * delta) := by linarith
  rw [heq] at hle
  exact hle.trans_lt (neg_neg_of_pos (mul_pos hD hH))


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingStrip
namespace OAI

/-! A zero-free strip deduced from two local shrinking-disk growth bounds.
The analytic growth assumption remains explicit; the proof itself is the
exact three-factor positivity argument for the actual L-functions. -/

namespace TwoPointCorrelations

open _root_.Complex
open scoped _root_.Classical

/-- Two disks of radius `3r` with logarithmic growth budget `B` give a
zero-free horizontal distance proportional to `r/B`. -/
theorem mrt_moving_zero_free_oai : ∃ c r₀ : ℝ, 0 < c ∧ 0 < r₀ ∧
    ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q),
    ∀ (r t B β : ℝ), 0 < r → r ≤ r₀ → 3 * r < |t| → 1 ≤ B →
      (∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
        ‖mrtMovingLFunction χ r t z‖ ≤ Real.exp B) →
      (∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
        ‖mrtMovingLFunction (χ ^ 2) r (2 * t) z‖ ≤ Real.exp B) →
      1 - c * r / B ≤ β →
        DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
  obtain ⟨δ₀, hδ₀, Z, hZ, hzeta⟩ := Erdos970.uniform_bound_Z0
  let D := 3 * Z + (5 / 3 : ℝ) * mrtCharacterLogDerivativeConstant + 2
  have hC := mrtCharacterLogDerivativeConstant_pos
  have hD1 : 1 < D := by dsimp [D]; nlinarith
  have hD : 0 < D := zero_lt_one.trans hD1
  refine ⟨1 / (40 * D), min δ₀ 1, by positivity, lt_min hδ₀ zero_lt_one, ?_⟩
  intro q _ χ r t B β hr hrr ht hB hg hg2 hβ hz
  have hr1 : r ≤ 1 := hrr.trans (min_le_right _ _)
  have hrδ : r ≤ δ₀ := hrr.trans (min_le_left _ _)
  have hBp : 0 < B := zero_lt_one.trans_le hB
  let δ := r / (10 * D * B)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ ≤ r / 10 := by
    dsimp [δ]
    apply (div_le_div_iff₀ (by positivity : 0 < 10 * D * B) (by norm_num : (0 : ℝ) < 10)).mpr
    have hDB : 1 ≤ D * B := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hD1.le) (sub_nonneg.mpr hB)]
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hDB)]
  have hδsmall : δ < δ₀ := by linarith
  have hδ1 : δ < 1 := by linarith
  have ht2 : 3 * r < |2 * t| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg t]
  have hβ1 : β < 1 := by
    by_contra! h
    have hn : (β : ℂ) + Complex.I * (t : ℂ) ≠ 1 := by
      intro he
      have him := congrArg Complex.im he
      simp at him
      have htp : 0 < |t| := by linarith
      simp [him] at htp
    exact χ.LFunction_ne_zero_of_one_le_re (Or.inr hn) (by simpa using h) hz
  let ε := 1 - β
  have hε : 0 ≤ ε := by dsimp [ε]; linarith
  have heq : (1 / (40 * D)) * r / B = δ / 4 := by dsimp [δ]; field_simp; ring
  rw [heq] at hβ
  have hεu : ε ≤ δ / 4 := by dsimp [ε]; linarith
  have hβr : 1 - r / 4 ≤ β := by linarith
  have hc := mrt_moving_neg_logderiv_of_zero χ hr ht hBp hg
    (σ := 1 + δ) (by linarith) (by linarith) hβr hβ1.le hz
  have hs := mrt_moving_neg_logderiv (χ ^ 2) hr ht2 hBp hg2
    (σ := 1 + δ) (by linarith) (by linarith)
  have hz0 := hzeta δ hδ hδsmall
  have hp := mrtCharacter_logderiv_positivity χ (σ := 1 + δ) (by linarith) t
  have hpoint : ((1 + δ : ℝ) : ℂ) = (1 : ℂ) + (δ : ℂ) := by push_cast; rfl
  simp only [Erdos970.logDerivZeta, ← neg_div] at hz0
  rw [← hpoint] at hz0
  have hdist : 1 + δ - β = δ + ε := by dsimp [ε]; ring
  rw [hdist] at hc
  have hBr : 1 ≤ B / r := (le_div_iff₀ hr).mpr (by linarith)
  have hcost : 3 * Z + 5 * (mrtCharacterLogDerivativeConstant * B / (3 * r)) ≤
      D * (B / r) := by
    have hZbr := mul_le_mul_of_nonneg_left hBr (show 0 ≤ 3 * Z by positivity)
    have hid : 5 * (mrtCharacterLogDerivativeConstant * B / (3 * r)) =
        ((5 / 3 : ℝ) * mrtCharacterLogDerivativeConstant) * (B / r) := by ring
    rw [hid]
    dsimp [D]
    nlinarith [div_nonneg hBp.le hr.le]
  have hpos : 0 ≤ 3 / δ + D * (B / r) - 4 / (δ + ε) := by
    have hm := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hz0 (by norm_num : (0 : ℝ) ≤ 3))
        (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 4))) hs
    have he : 3 * (1 / δ + Z) +
        4 * (mrtCharacterLogDerivativeConstant * B / (3 * r) - 1 / (δ + ε)) +
        mrtCharacterLogDerivativeConstant * B / (3 * r) =
        3 / δ + (3 * Z + 5 * (mrtCharacterLogDerivativeConstant * B / (3 * r))) -
          4 / (δ + ε) := by ring
    rw [he] at hm
    linarith only [hp.trans hm, hcost]
  have hδeq : δ = 1 / (10 * D * (B / r)) := by dsimp [δ]; field_simp
  exact (not_lt_of_ge hpos)
    (mrt_character_zero_free_arithmetic hD (div_pos hBp hr) hδeq hε hεu)

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_moving_zero_free_oai := @OAI.TwoPointCorrelations.mrt_moving_zero_free_oai
