-- Prove2me | solution 1 for OAI.Elasticity.dn_weak_transport_column
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:27:19.008331+00:00
-- url     : https://prove2.me/submissions/42d7fb5f-fbdb-4a93-a974-fd9b728ab243

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El006
import Theorems.Thm_OAI_Elasticity_extended_dn_amplitude_transfer
import Theorems.Thm_OAI_ElasticityCGO_localized_actual_strong_bound
import Theorems.Thm_OAI_ElasticityCGO_localized_formal_L2_tendsto
import Theorems.Thm_OAI_ElasticityDistribution_actual_transferred_limit
import Theorems.Thm_OAI_ElasticityPhysicalEstimate_physical_compact_comparison

section
-- module Solutions.OAIQ6_Elast.Elasticity_Bessel
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Concrete Fourier Bessel potentials for the required negative-order
supported Carleman estimate. All functions and operators are actual Schwartz
maps; no Sobolev-shift estimate is being assumed. -/
open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
namespace ElasticityBessel

lemma weight_pos (h s : ℝ) (x : X) : 0 < weight h s x := by
  exact Real.rpow_pos_of_pos (by positivity) _

lemma temperate_weight (h s : ℝ) : (weight h s).HasTemperateGrowth := by
  exact (Function.hasTemperateGrowth_one_add_norm_sq_rpow X (s/2)).comp
    (((2*Real.pi*h) • ContinuousLinearMap.id ℝ X).hasTemperateGrowth)

lemma temperate_complex_weight (h s : ℝ) :
    (fun x => (weight h s x : ℂ)).HasTemperateGrowth := by
  exact Complex.ofRealCLM.hasTemperateGrowth.comp (temperate_weight h s)

@[simp] lemma M_apply (h s : ℝ) (f : S) (x : X) :
    M h s f x = (weight h s x : ℂ)*f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (temperate_complex_weight h s) f x

@[simp] lemma M_zero (h : ℝ) (f : S) : M h 0 f = f := by
  ext x
  simp only [M_apply, weight_zero, Complex.ofReal_one, one_mul]

@[simp] lemma J_zero (h : ℝ) (f : S) : J h 0 f = f := by
  simp only [J, M_zero, FourierTransform.fourierInv_fourier_eq]

lemma norm2_nonneg (f : S) : 0 ≤ norm2 f := norm_nonneg _

lemma norm2_bound (f g : S) (c : ℝ) (h : ∀ x : X, ‖f x‖ ≤ c*‖g x‖) :
    norm2 f ≤ c*norm2 g := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [f.coeFn_toLp 2 volume, g.coeFn_toLp 2 volume] with x hx hy
  change ‖f.toLp 2 volume x‖ ≤ c * ‖g.toLp 2 volume x‖
  rw [hx, hy]
  exact h x

lemma norm2_fourier (f : S) : norm2 (𝓕 f) = norm2 f :=
  SchwartzMap.norm_fourier_toL2_eq f

lemma norm2_fourierInv (f : S) : norm2 (𝓕⁻ f) = norm2 f := by
  have h := norm2_fourier (𝓕⁻ f)
  rw [FourierTransform.fourier_fourierInv_eq] at h
  exact h.symm

lemma norm2_J (h s : ℝ) (f : S) : norm2 (J h s f) = norm2 (M h s (𝓕 f)) :=
  norm2_fourierInv _

lemma real_weight_bound (h s t c : ℝ)
    (hw : ∀ x : X, weight h s x ≤ c*weight h t x) (f : S) :
    norm2 (J h s f) ≤ c*norm2 (J h t f) := by
  rw [norm2_J, norm2_J]
  apply norm2_bound
  intro x
  simp only [M_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (weight_pos _ _ _)]
  exact (mul_le_mul_of_nonneg_right (hw x) (norm_nonneg (𝓕 f x))).trans_eq (by ring)

lemma weight_mono (h : ℝ) {s t : ℝ} (hst : s ≤ t) (x : X) :
    weight h s x ≤ weight h t x := by
  exact Real.rpow_le_rpow_of_exponent_le
    (by nlinarith [sq_nonneg ‖(2*Real.pi*h) • x‖]) (by linarith)

lemma norm2_J_mono (h : ℝ) {s t : ℝ} (hst : s ≤ t) (f : S) :
    norm2 (J h s f) ≤ norm2 (J h t f) := by
  have he := real_weight_bound h s t 1 (fun x => by
    simpa only [one_mul] using weight_mono h hst x) f
  simpa only [one_mul] using he

end ElasticityBessel

/-! Positive commutator algebra on actual Schwartz functions, allowing
nonlocal Bessel shifts without silently retaining compact support. -/
open MeasureTheory Complex SchwartzMap LineDeriv
open scoped BigOperators LineDeriv SchwartzMap

namespace ElasticityNegativeOrder
open ElasticityBessel
open ElasticitySchwartzCarleman

section

lemma norm2_J_one_ge (h : ℝ) (f : S) : norm2 f ≤ norm2 (J h 1 f) := by
  have ht := norm2_J_mono h (show (0 : ℝ) ≤ 1 by norm_num) f
  simpa only [J_zero] using ht

end

lemma sobNorm_component_bound {n : ℕ} (h k s t C : ℝ) (hC : 0 ≤ C)
    (U V : Fin n → S) (hb : ∀ i, norm2 (J h s (U i)) ≤ C*norm2 (J k t (V i))) :
    sobNorm h s U ≤ C*sobNorm k t V := by
  have hs : ∑ i, (norm2 (J h s (U i)))^2 ≤ C^2 * ∑ i, (norm2 (J k t (V i)))^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [hb i, norm2_nonneg (J h s (U i)), norm2_nonneg (J k t (V i))]
  rw [sobNorm, sobNorm]
  have hp : 0 ≤ ∑ i, (norm2 (J h s (U i)))^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hq : 0 ≤ ∑ i, (norm2 (J k t (V i)))^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hp, Real.sq_sqrt hq]
  exact hs

end ElasticityNegativeOrder

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transfer
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators SchwartzMap
namespace ElasticityPhysicalEstimate
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder ElasticityPhysicalAlgebra
open ElasticityAugmented (coord coeffA coeffV)
open ElasticityCoeffBounds

lemma physicalAug_sub (z : Fin 3 → ℂ) (u v : Fin 3 → S) :
    physicalAug z (v-u)=physicalAug z v-physicalAug z u := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [physicalAug,Fin.cons_zero,Pi.sub_apply,divShift,map_sub,Finset.sum_sub_distrib]
  · rfl

end ElasticityPhysicalEstimate

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_PhysicalCGO
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityAugmented

open Set
open scoped BigOperators
lemma real_longitudinal_positive (lam m : X → ℝ) (hp : ∀ x,0 < m x ∧ 0<3*lam x+2*m x) (x : X) :
    0<lam x+m x+m x := by have hh := hp x; linarith

end ElasticityAugmented
namespace Elasticity
open Set MeasureTheory
open scoped BigOperators SchwartzMap
open ElasticityAugmented (Smooth smoothOfReal smooth_coe)
open ElasticityCoeffBounds
open ElasticityDistribution (Coeff eval)
open ElasticityPhysicalAlgebra (physical)
open ElasticityCGO (expCut)

open ElasticityPhysicalEstimate (physicalAug)
open ElasticityPhysicalAlgebra (phase)
open ElasticityNegativeOrder (sobNorm)

/-- The actual physical DN equality gives the uniform compact comparison bound.
The Cauchy-data transfer, normalized forcing, and coefficient bounds are all
proved dependencies. This theorem still starts at the common-exterior stage;
it does not replace the missing original-boundary jet determination. -/
theorem extended_dn_compact_comparison {Ω B B' : Set X}
    (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (hB : IsOpen B)
    (hBB : Bornology.IsBounded B) (hB' : IsOpen B') (hsub : B'⊆B) (hcl : closure Ω⊆B')
    (R : ℝ) (hR : 1≤R) (hKR : closure Ω⊆Metric.closedBall 0 R)
    (α β : X) (hα : α≠0)
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1))
    (χ g : Smooth) (hcχ : HasCompactSupport (χ : X → ℂ))
    (hc : HasCompactSupport (g : X → ℂ)) (hs : tsupport (g : X → ℂ)⊆B)
    (hχ : EqOn (χ : X → ℂ) 1 B) (hg : EqOn (g : X → ℂ) 1 B') :
    ∃ C h₀ : ℝ,0<C ∧ 0<h₀ ∧ ∀ h : ℝ,0<h → h≤h₀ →
      ∀ u : Fin 3 → SchwartzMap X ℂ,
      (∀ i,EqOn (physical (phase h α β) (fun x => (lam 0 x : ℂ))
        (fun x => (m 0 x : ℂ)) u i : X → ℂ) 0 B) →
      ∃ v : Fin 3 → SchwartzMap X ℂ,
        (∀ i,tsupport (v i-u i : SchwartzMap X ℂ)⊆closure Ω) ∧
        (∀ i,EqOn (physical (phase h α β) (fun x => (lam 1 x : ℂ))
          (fun x => (m 1 x : ℂ)) v i : X → ℂ) 0 B') ∧
        sobNorm h 1 (physicalAug (phase h α β) (v-u))≤
          C*sobNorm h 1 (physicalAug (phase h α β) u) := by
  let l := fun q => smoothOfReal (lam q) (hl q)
  let μ := fun q => smoothOfReal (m q) (hm q)
  have hn0 (q x) : (μ q : X → ℂ) x≠0 := Complex.ofReal_ne_zero.mpr (hp q x).1.ne'
  have ho0 (q x) : ((l q+μ q+μ q : Smooth) : X → ℂ) x≠0 := by
    change (lam q x : ℂ)+(m q x : ℂ)+(m q x : ℂ)≠0
    exact_mod_cast (ElasticityAugmented.real_longitudinal_positive (lam q) (m q) (hp q) x).ne'
  have hel : EqOn (l 0 : X → ℂ) (l 1) (closure Ω)ᶜ := by
    intro x hx
    exact congrArg Complex.ofReal (he x (fun hh => hx (subset_closure hh))).1
  have hem : EqOn (μ 0 : X → ℂ) (μ 1) (closure Ω)ᶜ := by
    intro x hx
    exact congrArg Complex.ofReal (he x (fun hh => hx (subset_closure hh))).2
  obtain ⟨C,h₀,hC,hh₀,hest⟩ := ElasticityPhysicalEstimate.physical_compact_comparison
    hB' isClosed_closure hcl R hR hKR α β hα l μ hcll hclm hn0 ho0 hel hem
  refine ⟨C,h₀,hC,hh₀,fun h hh hsmall u hu => ?_⟩
  obtain ⟨v,hv,hsol⟩ := extended_dn_amplitude_transfer hΩ hOB hB hBB hB' hsub hcl
    lam m hl hm hp hcll hclm he hDN χ g hcχ hc hs hχ hg (phase h α β) u hu
  exact ⟨v,hv,hsol,hest h hh hsmall u v hv (fun i => (hu i).mono hsub) hsol⟩
end Elasticity

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_WeakLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityCGO

section
open Set Filter MeasureTheory
open scoped SchwartzMap Topology BigOperators ENNReal
open ElasticityAugmented
open ElasticityBessel (L2 norm2 J)
open ElasticityNegativeOrder (mult sobNorm)
open ElasticityPhysicalAlgebra (divShift)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityDistribution (AugHilbert)

lemma augEmbed_apply (u : Fin 4 → S) (i : Fin 4) : augEmbed u i=L2 (u i) := rfl
lemma norm_augEmbed (h : ℝ) (u : Fin 4 → S) : ‖augEmbed u‖=sobNorm h 0 u := by
  rw [PiLp.norm_eq_of_L2]
  simp only [augEmbed_apply,sobNorm,ElasticityBessel.J_zero,norm2]
lemma norm_augEmbed_le (h : ℝ) (u : Fin 4 → S) : ‖augEmbed u‖≤ sobNorm h 1 u := by
  rw [norm_augEmbed h]
  simpa only [one_mul] using ElasticityNegativeOrder.sobNorm_component_bound h h 0 1 1
    (by norm_num) u u (fun i => by
      simpa only [ElasticityBessel.J_zero,one_mul] using ElasticityNegativeOrder.norm2_J_one_ge h (u i))

end
open Set MeasureTheory Filter
open scoped SchwartzMap Topology BigOperators
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityBessel (L2 norm2)
open ElasticityNegativeOrder (mult sobNorm)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityPhysicalEstimate (physicalAug)

end ElasticityCGO
namespace ElasticitySequences
open Filter
open scoped Topology
lemma small_sequence {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    ∃ h : ℕ → ℝ,Tendsto h atTop (𝓝 0) ∧ (∀ n,0<h n) ∧
      (∀ n,h n≤a) ∧ (∀ n,h n≤b) := by
  let c := min a b
  have hc : 0 < c := lt_min ha hb
  let h := fun n : ℕ => c*((n+1 : ℝ)⁻¹)
  have hh : Tendsto h atTop (𝓝 0) := by
    simpa only [h,one_div,mul_zero] using
      tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 0))
  have hpos (n) : 0<h n := mul_pos hc (inv_pos.mpr (by positivity))
  have hle (n) : h n ≤ c := by
    change c*((n+1 : ℝ)⁻¹) ≤ c
    apply mul_le_of_le_one_right hc.le
    exact inv_le_one_of_one_le₀ (by have hn : (0 : ℝ)≤(n : ℝ) := Nat.cast_nonneg n; linarith)
  exact ⟨h,hh,hpos,fun n => (hle n).trans (min_le_left a b),
    fun n => (hle n).trans (min_le_right a b)⟩
lemma tendsto_of_error {E : Type*} [NormedAddCommGroup E]
    {u f : ℕ → E} {a : E} {h : ℕ → ℝ} {C : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) (hh : Tendsto h atTop (𝓝 0))
    (he : ∀ n,‖u n-f n‖≤C*h n) : Tendsto u atTop (𝓝 a) := by
  have hn : Tendsto (fun n => ‖u n-f n‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) he (by simpa using tendsto_const_nhds.mul hh)
  have hz : Tendsto (fun n => u n-f n) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hn
  simpa only [sub_add_cancel,zero_add] using hz.add hf
end ElasticitySequences
namespace Elasticity
open Set MeasureTheory Filter TemperedDistribution
open scoped BigOperators SchwartzMap Topology
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityDistribution (Coeff Dist LocalEq AugHilbert leadingRd leadingSd normald)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityNegativeOrder (sobNorm)
open ElasticityCGO

/-- A genuine physical DN transfer yields a bounded weak leading transport
column with the actual exterior leading value. Every bound and equation is
derived from the physical CGO construction and the compact comparison. -/
theorem dn_weak_transport_column_oai {Ω B B' : Set X}
    (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (hB : IsOpen B)
    (hBB : Bornology.IsBounded B) (hB' : IsOpen B') (hsub : B'⊆B) (hcl : closure Ω⊆B')
    (R : ℝ) (hR : 1≤R) (hKR : closure Ω⊆Metric.closedBall 0 R)
    (hBR : B⊆Metric.ball 0 R) (α β : X) (hα : α≠0)
    (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1))
    (χ g η : Smooth) (hcχ : HasCompactSupport (χ : X → ℂ))
    (hc : HasCompactSupport (g : X → ℂ)) (hs : tsupport (g : X → ℂ)⊆B)
    (hχ : EqOn (χ : X → ℂ) 1 B) (hg : EqOn (g : X → ℂ) 1 B')
    (hcη : HasCompactSupport (η : X → ℂ)) (hsη : tsupport (η : X → ℂ)⊆Metric.ball 0 R)
    (hη : EqOn (η : X → ℂ) 1 B)
    (a : ℕ → Amplitude Smooth)
    (ha : PhysicalColumn R hR α β (smoothOfReal (lam 0) (hl 0)) (smoothOfReal (m 0) (hm 0)) a)
    (h₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
    (hrec : ∀ j<8,EqOn (fun x => ((normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ))
      (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(ElasticityAugmented.div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) (Metric.ball 0 R)) :
    let L : Coeff := ⟨smoothOfReal (lam 1) (hl 1),(hcll 1).growth⟩
    let M : Coeff := ⟨smoothOfReal (m 1) (hm 1),(hclm 1).growth⟩
    let θ := fun i => (α i : ℂ)+Complex.I*(β i : ℂ)
    ∃ W : AugHilbert,
      (∀ i,LocalEq B' (leadingRd θ L M (fun j => (W j.succ : Dist)) (W 0 : Dist) i) 0) ∧
      LocalEq B' (leadingSd θ L M (fun j => (W j.succ : Dist)) (W 0 : Dist)) 0 ∧
      LocalEq B' (normald θ (fun j => (W j.succ : Dist))) 0 ∧
      ∀ i,LocalEq (closure Ω)ᶜ (W i : Dist) (localizedLeading R hR a η i : Dist) := by
  intro L M θ
  obtain ⟨C,D,h₀',hC,hD,hh₀,hsource⟩ := localized_actual_strong_bound R hR α β
    (smoothOfReal (lam 0) (hl 0)) (smoothOfReal (m 0) (hm 0)) (hcll 0) (hclm 0)
    a ha h₀ hrec (smooth_coe η) hcη hsη hB hBR hη
  obtain ⟨A,h₁,hA,hh₁,htransfer⟩ := extended_dn_compact_comparison hΩ hOB hB hBB hB' hsub hcl
    R hR hKR α β hα lam m hl hm hp hcll hclm he hDN χ g hcχ hc hs hχ hg
  obtain ⟨h,hh,hpos,hle₀,hle₁⟩ := ElasticitySequences.small_sequence hh₀ hh₁
  choose u hu hub hue using fun n => hsource (h n) (hpos n) (hle₀ n)
  choose v hvs hv hvb using fun n => htransfer (h n) (hpos n) (hle₁ n) (u n) (hu n)
  have bound (n) : ‖augEmbed (physicalAug (phase (h n) α β) (v n))‖≤(A+1)*C := by
    have hd : augEmbed (physicalAug (phase (h n) α β) (v n-u n))=
        augEmbed (physicalAug (phase (h n) α β) (v n))-
          augEmbed (physicalAug (phase (h n) α β) (u n)) := by
      rw [ElasticityPhysicalEstimate.physicalAug_sub,map_sub]
    have hhU := (norm_augEmbed_le (h n) (physicalAug (phase (h n) α β) (u n))).trans (hub n)
    have hhV := (norm_augEmbed_le (h n) (physicalAug (phase (h n) α β) (v n-u n))).trans (hvb n)
    rw [hd] at hhV
    have hAC := mul_le_mul_of_nonneg_left (hub n) hA.le
    have hn := norm_sub_norm_le (augEmbed (physicalAug (phase (h n) α β) (v n)))
      (augEmbed (physicalAug (phase (h n) α β) (u n)))
    nlinarith only [hhU,hhV,hAC,hn]
  have strong (i : Fin 4) : Tendsto
      (fun n => ElasticityBessel.L2 (physicalAug (phase (h n) α β) (u n) i)) atTop
      (𝓝 (ElasticityBessel.L2 (localizedLeading R hR a η i))) := by
    apply ElasticitySequences.tendsto_of_error
      (localized_formal_L2_tendsto R hR α β a h₀ hrec (hcη.hasTemperateGrowth (smooth_coe η))
        hsη hh (fun n => (hpos n).ne') i) hh
    intro n
    simpa only [map_sub] using hue n i
  exact ElasticityDistribution.actual_transferred_limit B' (closure Ω) α β hθ L M h hh
    (fun n => (hpos n).ne') u v (localizedLeading R hR a η) hv hvs ((A+1)*C) bound strong
end Elasticity

end

end OAI
end

theorem solution : type_of% @OAI.Elasticity.dn_weak_transport_column_oai := @OAI.Elasticity.dn_weak_transport_column_oai
