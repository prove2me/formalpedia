-- Prove2me | solution 1 for OAI.Elasticity.dn_common_normal_frame
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:58:31.98808+00:00
-- url     : https://prove2.me/submissions/f580b66c-9456-48de-a5a4-3a6b2a3e00e4

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El003
import Definitions.Def_OAIQ6El004
import Theorems.Thm_OAI_Elasticity_dn_smooth_transport_column
import Theorems.Thm_OAI_ElasticityAugmented_exists_real_physical_series
import Theorems.Thm_OAI_ElasticityAugmented_leading_equations_at_iff
import Theorems.Thm_OAI_ElasticityCGO_physical_cgo_from_recursion

section
-- module Solutions.OAIQ6_Elast.Elasticity_TransportAlgebra
attribute [-instance] _root_.OAI.ElasticityDistribution.instIsCentralScalarSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexMulOppositeSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulCommClassComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityAugmented

lemma localCoord_restrict {U : Set X} (hU : IsOpen U) (i : Fin 3) (f : Smooth) :
    localCoord hU i (restrictSmooth U f)=restrictSmooth U (coord i f) := by
  exact Derivation.liftOfSurjective_apply (restrictSmooth_surjective U) (restrict_coord_zero hU i) f
lemma restrict_direction {U : Set X} (hU : IsOpen U) (θ : Fin 3 → ℂ) (f : Smooth) :
    restrictSmooth U (direction coord θ f)=direction (localCoord hU) θ (restrictSmooth U f) := by
  simp only [direction,map_sum,map_smul,localCoord_restrict]
lemma restrict_leadingR {U : Set X} (hU : IsOpen U) (θ : Fin 3 → ℂ)
    (lam mu : Smooth) (a : Fin 3 → Smooth) (b : Smooth) (i : Fin 3) :
    restrictSmooth U (leadingR coord θ lam mu a b i)=
      leadingR (localCoord hU) θ (restrictSmooth U lam) (restrictSmooth U mu)
        (fun i => restrictSmooth U (a i)) (restrictSmooth U b) i := by
  simp only [leadingR,map_add,map_mul,map_ofNat,map_sum,map_smul,localCoord_restrict,restrict_direction hU]
lemma restrict_leadingS {U : Set X} (hU : IsOpen U) (θ : Fin 3 → ℂ)
    (lam mu : Smooth) (a : Fin 3 → Smooth) (b : Smooth) :
    restrictSmooth U (leadingS coord θ lam mu a b)=
      leadingS (localCoord hU) θ (restrictSmooth U lam) (restrictSmooth U mu)
        (fun i => restrictSmooth U (a i)) (restrictSmooth U b) := by
  simp only [leadingS,map_add,map_mul,map_ofNat,map_sum,localCoord_restrict,restrict_direction hU]
end ElasticityAugmented

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transport
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityParameter
open scoped BigOperators InnerProductSpace

lemma real_complex_plane_injective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (ha : a≠0) (hb : b≠0) (hab : inner ℝ a b=0) :
    Function.Injective (Complex.reCLM.smulRight a+Complex.imCLM.smulRight b : ℂ →L[ℝ] E) := by
  let J : ℂ →L[ℝ] E := Complex.reCLM.smulRight a+Complex.imCLM.smulRight b
  suffices hn : ∀ z : ℂ, J z=0 → z=0 by
    intro z w h
    apply sub_eq_zero.mp
    apply hn
    rw [map_sub,h,sub_self]
  intro z hz
  have ha0 : inner ℝ a a≠0 := by
    intro h
    exact ha (inner_self_eq_zero.mp h)
  have hb0 : inner ℝ b b≠0 := by
    intro h
    exact hb (inner_self_eq_zero.mp h)
  have hba : inner ℝ b a=0 := by rwa [real_inner_comm]
  have hr := congrArg (fun v : E => inner ℝ a v) hz
  have hi := congrArg (fun v : E => inner ℝ b v) hz
  change inner ℝ a (z.re • a+z.im • b)=inner ℝ a 0 at hr
  change inner ℝ b (z.re • a+z.im • b)=inner ℝ b 0 at hi
  simp only [inner_add_right,inner_smul_right,hab,hba,mul_zero,zero_add,add_zero,inner_zero_right] at hr hi
  apply Complex.ext
  · exact (mul_eq_zero.mp hr).resolve_right ha0
  · exact (mul_eq_zero.mp hi).resolve_right hb0

lemma basis_sum_apply (v : Fin 3 → ℝ) (i : Fin 3) :
    (∑ r, v r • basis r : X) i=v i := by
  simp [basis,Pi.single_apply]

lemma null_re_im (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0) :
    (∑ i, (θ i).re*(θ i).re)=(∑ i, (θ i).im*(θ i).im) ∧
      (∑ i, (θ i).re*(θ i).im)=0 := by
  have hr := congrArg Complex.re hθ
  have hi := congrArg Complex.im hθ
  simp only [Complex.re_sum,Complex.mul_re,Complex.zero_re,Finset.sum_sub_distrib] at hr
  simp only [Complex.im_sum,Complex.mul_im,Complex.zero_im,Finset.sum_add_distrib] at hi
  have he : (∑ i, (θ i).im*(θ i).re)=(∑ i, (θ i).re*(θ i).im) :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [he] at hi
  constructor
  · exact sub_eq_zero.mp hr
  · linarith

lemma null_plane_injective (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0) (hne : θ≠0) :
    Function.Injective (characteristicPlane basis θ) := by
  obtain ⟨hre,him⟩ := null_re_im θ hθ
  let a : X := ∑ i, (θ i).re • basis i
  let b : X := ∑ i, (θ i).im • basis i
  have hai (i : Fin 3) : a i=(θ i).re := basis_sum_apply _ i
  have hbi (i : Fin 3) : b i=(θ i).im := basis_sum_apply _ i
  have haa : inner ℝ a a=∑ i, (θ i).re*(θ i).re := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hai]
  have hbb : inner ℝ b b=∑ i, (θ i).im*(θ i).im := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hbi]
  have hab : inner ℝ a b=0 := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hai,hbi]
    simpa only [mul_comm] using him
  have he : inner ℝ a a=inner ℝ b b := by rw [haa,hbb,hre]
  have hboth : ¬ (a=0 ∧ b=0) := by
    rintro ⟨ha,hb⟩
    apply hne
    funext i
    apply Complex.ext
    · simpa only [ha,PiLp.zero_apply,Pi.zero_apply,Complex.zero_re] using (hai i).symm
    · simpa only [hb,PiLp.zero_apply,Pi.zero_apply,Complex.zero_im] using (hbi i).symm
  have ha : a≠0 := by
    intro hz
    apply hboth
    refine ⟨hz,(@inner_self_eq_zero ℝ X _ _ _).mp ?_⟩
    rw [← he,hz,inner_zero_left]
  have hb : b≠0 := by
    intro hz
    apply ha
    apply (@inner_self_eq_zero ℝ X _ _ _).mp
    rw [he,hz,inner_zero_left]
  exact real_complex_plane_injective a b ha hb hab
end ElasticityParameter
namespace ElasticityAugmented
open scoped BigOperators

lemma smoothInv_apply (f : Smooth) (hf : ∀ x, (f : X → ℂ) x≠0) (x : X) :
    (smoothInv f hf : X → ℂ) x=((f : X → ℂ) x)⁻¹ := rfl
end ElasticityAugmented

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
lemma real_k_positive (lam m : X → ℝ) (hp : ∀ x,0 < m x ∧ 0<3*lam x+2*m x) (x : X) :
    0<lam x+m x := by have hh := hp x; linarith
lemma real_longitudinal_positive (lam m : X → ℝ) (hp : ∀ x,0 < m x ∧ 0<3*lam x+2*m x) (x : X) :
    0<lam x+m x+m x := by have hh := hp x; linarith

end ElasticityAugmented
namespace ElasticityCGO

open Set
open ElasticityAugmented
open ElasticityNegativeOrder (cutoff)

lemma fiveCutoff_support (R : ℝ) (hR : 1≤R) (i : Fin 5) :
    tsupport (fiveCutoff R hR i)⊆Metric.closedBall 0 (R+(i.val : ℝ)+2) := by
  let b := cutoff (R+(i.val : ℝ)) (by have h := Nat.cast_nonneg (α := ℝ) i.val; linarith)
  have hs : tsupport (fiveCutoff R hR i)⊆tsupport b := by
    apply closure_mono
    intro x hx
    exact fun hh => hx (by change (b x : ℂ)=0; rw [hh,Complex.ofReal_zero])
  simpa only [b,ContDiffBump.tsupport_eq,cutoff] using hs
lemma fiveCutoff_one (R : ℝ) (hR : 1≤R) (i : Fin 5) {x : X}
    (hx : x∈Metric.closedBall 0 (R+(i.val : ℝ)+1)) : fiveCutoff R hR i x=1 := by
  have hh := (cutoff (R+(i.val : ℝ)) (by have h := Nat.cast_nonneg (α := ℝ) i.val; linarith)).one_of_mem_closedBall hx
  unfold fiveCutoff
  rw [hh,Complex.ofReal_one]
lemma fiveCutoff_nested (R : ℝ) (hR : 1≤R) (i : Fin 4) :
    EqOn (fiveCutoff R hR i.succ) 1 (tsupport (fiveCutoff R hR i.castSucc)) := by
  intro x hx
  apply fiveCutoff_one
  have hh := fiveCutoff_support R hR i.castSucc hx
  simp only [Metric.mem_closedBall,Fin.val_castSucc,Fin.val_succ,Nat.cast_add,Nat.cast_one] at hh ⊢
  linarith
lemma fiveCutoff_inside (R : ℝ) (hR : 1≤R) (i : Fin 5) :
    tsupport (fiveCutoff R hR i)⊆Metric.ball 0 (R+7) := by
  intro x hx
  have hh := fiveCutoff_support R hR i hx
  have hi : (i.val : ℝ)<5 := by exact_mod_cast i.isLt
  simp only [Metric.mem_closedBall] at hh
  rw [Metric.mem_ball]
  linarith
lemma fiveCutoff_initial (R : ℝ) (hR : 1≤R) :
    EqOn (fiveCutoff R hR 0) 1 (Metric.ball 0 R) := by
  intro x hx
  apply fiveCutoff_one
  simp only [Fin.val_zero,Nat.cast_zero,add_zero,Metric.mem_closedBall]
  have hh := Metric.mem_ball.mp hx
  linarith
end ElasticityCGO
namespace ElasticityCGO
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityRegularity (sobolevInjection)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityDistribution (HV Dist divd)

theorem physical_column_of_recursion (R : ℝ) (hR : 1≤R) (α β : X) (hα : α≠0)
    (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hrl : ∀ x,star ((lam : X → ℂ) x)=(lam : X → ℂ) x)
    (hrm : ∀ x,star ((m : X → ℂ) x)=(m : X → ℂ) x)
    (hm0 : ∀ x,(m : X → ℂ) x≠0) (he0 : ∀ x,((lam+m+m : Smooth) : X → ℂ) x≠0)
    (a : ℕ → Amplitude Smooth)
    (hR₀ : leadingR (localCoord Metric.isOpen_ball) (fun i => (α i : ℂ)+Complex.I*(β i : ℂ))
      (restrictSmooth (Metric.ball 0 R) lam) (restrictSmooth (Metric.ball 0 R) m)
      (localAmp (Metric.ball 0 R) (a 0)).1 (localAmp (Metric.ball 0 R) (a 0)).2=0)
    (hn₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
    (hrec : ∀ j<8,RecursOn (U := Metric.ball 0 R) Metric.isOpen_ball
      (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) lam m (a j) (a (j+1))) :
    PhysicalColumn R hR α β lam m a := by
  exact physical_cgo_from_recursion (R+7) (by linarith) (Metric.ball 0 (R+7)) (Metric.ball 0 R)
    Metric.ball_subset_closedBall Metric.isOpen_ball (Metric.ball_subset_ball (by linarith))
    α β hα hθ lam m hl hm hrl hrm hm0 he0 (fiveCutoff R hR) (fiveCutoff_smooth R hR)
    (fiveCutoff_compact R hR) (fiveCutoff_nested R hR) (fiveCutoff_inside R hR)
    (fiveCutoff_initial R hR) a hR₀ hn₀ hrec

end ElasticityCGO

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_CommonFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators
namespace Elasticity
open ElasticityAugmented ElasticityCGO
open ElasticityCoeffBounds (ExteriorConstant)
/-- Three actual transferred physical leading columns, in the same constrained
fiber as the original globally independent frame. The new columns need not be
assumed independent. -/
theorem dn_common_leading_frame {Ω : Set X} (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω)
    (r₀ : ℝ) (hr₀ : 1 ≤ r₀) (hK : closure Ω⊆Metric.closedBall 0 r₀)
    (α β : X) (hα : α≠0)
    (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1)) :
    let θ := fun i => (α i : ℂ)+Complex.I*(β i : ℂ)
    let l := fun q => smoothOfReal (lam q) (hl q)
    let μ := fun q => smoothOfReal (m q) (hm q)
    let r := positiveRoot (m 0) (hm 0) (fun x => (hp 0 x).1)
    let hr := positiveRoot_nonzero (m 0) (hm 0) (fun x => (hp 0 x).1)
    ∃ a : Fin 2 → Fin 3 → Amplitude Smooth,
    ∃ B : X → Module.Basis (Fin 3) ℂ (ElasticityFrame.Fiber θ),
      (∀ q ν,normal θ (a q ν).1=0) ∧
      (∀ q ν i,EqOn ((leadingR coord θ (l q) (μ q) (a q ν).1 (a q ν).2 i : Smooth) : X → ℂ) 0 (Metric.ball 0 (r₀+3))) ∧
      (∀ q ν,EqOn ((leadingS coord θ (l q) (μ q) (a q ν).1 (a q ν).2 : Smooth) : X → ℂ) 0 (Metric.ball 0 (r₀+3))) ∧
      (∀ ν i,tsupport ((((Fin.cons (a 1 ν).2 (a 1 ν).1 : Fin 4 → Smooth) i-
        (Fin.cons (a 0 ν).2 (a 0 ν).1 : Fin 4 → Smooth) i : Smooth)) : X → ℂ)⊆closure Ω) ∧
      ∀ ν x,((B x ν : ElasticityFrame.Fiber θ) : ElasticityFrame.Amp)=
        ((fun i => (changeP r (a 0 ν).1 i : X → ℂ) x),
          (changeS (l 0+μ 0) r hr (a 0 ν).1 (a 0 ν).2 : X → ℂ) x) := by
  intro θ l μ r hr
  let R := r₀+7
  have hR : 1≤R := by dsimp [R]; linarith
  have hne : θ≠0 := by
    intro hz
    apply hα
    ext i
    change α i=0
    have hh := congrArg Complex.re (congrFun hz i)
    simpa [θ] using hh
  have hC : IsCompact (closure (Metric.ball (0 : X) R)) :=
    (isCompact_closedBall (0 : X) R).of_isClosed_subset isClosed_closure
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
  obtain ⟨a,B,hn,hL,hrec,hB⟩ := exists_real_physical_series Metric.isOpen_ball hC θ hθ hne
    (lam 0) (m 0) (hl 0) (hm 0) (hp 0)
  let χ : Fin 5 → Smooth := fun i => ⟨fiveCutoff r₀ hr₀ i,fiveCutoff_smooth r₀ hr₀ i⟩
  have hball {s t : ℝ} (hst : s<t) : Metric.closedBall (0 : X) s⊆Metric.ball 0 t :=
    Metric.closedBall_subset_ball hst
  have hcb : closure Ω⊆Metric.ball 0 (r₀+3) := hK.trans (hball (by linarith))
  have hpc (ν : Fin 3) : PhysicalColumn R hR α β (l 0) (μ 0) (a ν) := by
    apply physical_column_of_recursion R hR α β hα hθ (l 0) (μ 0) (hcll 0) (hclm 0)
      (fun x => Complex.conj_ofReal _) (fun x => Complex.conj_ofReal _)
      (fun x => Complex.ofReal_ne_zero.mpr (hp 0 x).1.ne') (fun x => ?_)
      (a ν) (hL ν).1 (hn ν) (fun j _ => hrec ν j)
    change (lam 0 x : ℂ)+(m 0 x : ℂ)+(m 0 x : ℂ)≠0
    exact_mod_cast (real_longitudinal_positive (lam 0) (m 0) (hp 0) x).ne'
  have hex (ν : Fin 3) := dn_smooth_transport_column hΩ hOB Metric.isOpen_ball Metric.isBounded_ball
    (B := Metric.ball 0 (r₀+5)) (B' := Metric.ball 0 (r₀+3)) Metric.isOpen_ball
    (Metric.ball_subset_ball (by linarith)) hcb R hR
    (hK.trans (Metric.closedBall_subset_closedBall (by dsimp [R]; linarith)))
    (Metric.ball_subset_ball (by dsimp [R]; linarith)) α β hα hθ lam m hl hm hp hcll hclm he hDN
    (χ 4) (χ 2) (χ 4) (fiveCutoff_compact r₀ hr₀ 4) (fiveCutoff_compact r₀ hr₀ 2)
    ((fiveCutoff_support r₀ hr₀ 2).trans (hball (by norm_num; linarith)))
    (fun x hx => fiveCutoff_one r₀ hr₀ 4 (by convert Metric.ball_subset_closedBall hx using 1; norm_num [add_assoc]))
    (fun x hx => fiveCutoff_one r₀ hr₀ 2 (by convert Metric.ball_subset_closedBall hx using 1; norm_num [add_assoc]))
    (fiveCutoff_compact r₀ hr₀ 4) ((fiveCutoff_support r₀ hr₀ 4).trans (hball (by norm_num; dsimp [R]; linarith)))
    (fun x hx => fiveCutoff_one r₀ hr₀ 4 (by convert Metric.ball_subset_closedBall hx using 1; norm_num [add_assoc]))
    (a ν) (hpc ν) (hn ν)
    (fun j _ x _ => congrArg (fun f : Smooth => (f : X → ℂ) x) (hrec ν j).2.2)
    (B₀ := Metric.ball 0 (r₀+1)) Metric.isOpen_ball (hK.trans (hball (by linarith)))
    (χ 0) (fiveCutoff_compact r₀ hr₀ 0)
    ((fiveCutoff_support r₀ hr₀ 0).trans (hball (by norm_num)))
    (fun x hx => fiveCutoff_one r₀ hr₀ 0 (by convert Metric.ball_subset_closedBall hx using 1; norm_num [add_assoc]))
  choose v hvs hvR hvS hvn using hex
  let A : Fin 2 → Fin 3 → Amplitude Smooth := ![(fun ν => a ν 0),fun ν => ((fun i => v ν i.succ),v ν 0)]
  have hR₀ (ν i) : EqOn ((leadingR coord θ (l 0) (μ 0) (a ν 0).1 (a ν 0).2 i : Smooth) : X → ℂ) 0
      (Metric.ball 0 (r₀+3)) := by
    have hh := congrFun (hL ν).1 i
    dsimp only [localAmp] at hh
    rw [← restrict_leadingR Metric.isOpen_ball] at hh
    intro x hx
    exact (restrictSmooth_zero_iff _ _).mp hh x (Metric.ball_subset_ball (by dsimp [R]; linarith) hx)
  have hS₀ (ν) : EqOn ((leadingS coord θ (l 0) (μ 0) (a ν 0).1 (a ν 0).2 : Smooth) : X → ℂ) 0
      (Metric.ball 0 (r₀+3)) := by
    have hh := (hL ν).2
    dsimp only [localAmp] at hh
    rw [← restrict_leadingS Metric.isOpen_ball] at hh
    intro x hx
    exact (restrictSmooth_zero_iff _ _).mp hh x (Metric.ball_subset_ball (by dsimp [R]; linarith) hx)
  refine ⟨A,B,?_,?_,?_,?_,hB⟩
  · intro q ν
    fin_cases q
    · exact hn ν
    · exact hvn ν
  · intro q ν i
    fin_cases q
    · exact hR₀ ν i
    · exact hvR ν i
  · intro q ν
    fin_cases q
    · exact hS₀ ν
    · exact hvS ν
  · intro ν i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hvs ν 0
    · exact hvs ν j.succ
end Elasticity

end
end
section
noncomputable section
open Set
open scoped BigOperators
namespace ElasticityAugmented
lemma smooth_sum_eval {ι : Type*} [Fintype ι] (f : ι → Smooth) (x : X) :
    ((∑ i,f i : Smooth) : X → ℂ) x=∑ i,(f i : X → ℂ) x := by
  exact map_sum ((Pi.evalRingHom (fun _ : X => ℂ) x).comp Smooth.val.toRingHom) f Finset.univ
lemma eqOn_coord {U : Set X} (hU : IsOpen U) (f g : Smooth)
    (he : EqOn (f : X → ℂ) g U) (i : Fin 3) :
    EqOn (coord i f : X → ℂ) (coord i g) U := by
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [← localCoord_restrict hU,← localCoord_restrict hU,(restrictSmooth_eq_iff U f g).mpr he]
lemma eqOn_logarithmicGrad {U : Set X} (hU : IsOpen U) (r₀ r₁ : Smooth)
    (hr₀ : ∀ x,(r₀ : X → ℂ) x≠0) (hr₁ : ∀ x,(r₁ : X → ℂ) x≠0)
    (he : EqOn (r₀ : X → ℂ) r₁ U) (i : Fin 3) :
    EqOn (logarithmicGrad r₀ hr₀ i : X → ℂ) (logarithmicGrad r₁ hr₁ i) U := by
  intro x hx
  change 2*((r₀ : X → ℂ) x)⁻¹*(coord i r₀ : X → ℂ) x=
    2*((r₁ : X → ℂ) x)⁻¹*(coord i r₁ : X → ℂ) x
  rw [he hx,eqOn_coord hU r₀ r₁ he i hx]
lemma eqOn_physical_change {U : Set X} (hU : IsOpen U) (k₀ k₁ r₀ r₁ : Smooth)
    (hr₀ : ∀ x,(r₀ : X → ℂ) x≠0) (hr₁ : ∀ x,(r₁ : X → ℂ) x≠0)
    (a₀ a₁ : Fin 3 → Smooth) (b₀ b₁ : Smooth)
    (hk : EqOn (k₀ : X → ℂ) k₁ U) (hr : EqOn (r₀ : X → ℂ) r₁ U)
    (ha : ∀ i,EqOn (a₀ i : X → ℂ) (a₁ i) U) (hb : EqOn (b₀ : X → ℂ) b₁ U) :
    (∀ i,EqOn (changeP r₀ a₀ i : X → ℂ) (changeP r₁ a₁ i) U) ∧
      EqOn (changeS k₀ r₀ hr₀ a₀ b₀ : X → ℂ) (changeS k₁ r₁ hr₁ a₁ b₁) U := by
  have hp (i) : EqOn (changeP r₀ a₀ i : X → ℂ) (changeP r₁ a₁ i) U := by
    intro x hx
    change (r₀ : X → ℂ) x*(a₀ i : X → ℂ) x=(r₁ : X → ℂ) x*(a₁ i : X → ℂ) x
    rw [hr hx,ha i hx]
  refine ⟨hp,fun x hx => ?_⟩
  simp only [changeS,Subalgebra.coe_smul,Subalgebra.coe_add,Subalgebra.coe_mul,
    smooth_sum_eval,Pi.smul_apply,Pi.add_apply,Pi.mul_apply,smoothInv_apply]
  rw [hk hx,hr hx,hb hx]
  rw [show (∑ i,(logarithmicGrad r₀ hr₀ i : X → ℂ) x*(changeP r₀ a₀ i : X → ℂ) x)=
      ∑ i,(logarithmicGrad r₁ hr₁ i : X → ℂ) x*(changeP r₁ a₁ i : X → ℂ) x from
    Finset.sum_congr rfl (fun i _ => by rw [eqOn_logarithmicGrad hU r₀ r₁ hr₀ hr₁ hr i hx,hp i hx])]
end ElasticityAugmented

end
end
section
noncomputable section
open Set
open scoped BigOperators
namespace Elasticity
open ElasticityAugmented ElasticityCGO
open ElasticityCoeffBounds (ExteriorConstant)
lemma null_real_imag (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0) :
    ∃ α β : X,α≠0 ∧ θ=fun i => (α i : ℂ)+Complex.I*(β i : ℂ) := by
  let J := ElasticityParameter.characteristicPlane ElasticityParameter.basis θ
  refine ⟨J 1,J Complex.I,?_,?_⟩
  · intro hh
    have hz : J 1=J 0 := by rw [hh,map_zero]
    exact one_ne_zero (ElasticityParameter.null_plane_injective θ hθ hne hz)
  · funext i
    have ha : J 1 i=(θ i).re := by
      simp only [J,ElasticityParameter.characteristicPlane,add_apply,
        ContinuousLinearMap.smulRight_apply,Complex.reCLM_apply,Complex.imCLM_apply,
        Complex.one_re,Complex.one_im,one_smul,zero_smul,add_zero]
      exact ElasticityParameter.basis_sum_apply _ i
    have hb : J Complex.I i=(θ i).im := by
      simp only [J,ElasticityParameter.characteristicPlane,add_apply,
        ContinuousLinearMap.smulRight_apply,Complex.reCLM_apply,Complex.imCLM_apply,
        Complex.I_re,Complex.I_im,one_smul,zero_smul,zero_add]
      exact ElasticityParameter.basis_sum_apply _ i
    rw [ha,hb,mul_comm]
    exact (Complex.re_add_im (θ i)).symm

/-- The DN-derived common physical frame in the exact normal variables.
All coefficients and the exterior identification are still the actual Lamé pair. -/
theorem dn_common_normal_frame_oai {Ω : Set X} (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω)
    (r₀ : ℝ) (hr₀ : 1 ≤ r₀) (hK : closure Ω⊆Metric.closedBall 0 r₀)
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1)) :
    let k := fun q => smoothOfReal (lam q) (hl q)+smoothOfReal (m q) (hm q)
    let r := fun q => positiveRoot (m q) (hm q) (fun x => (hp q x).1)
    let hr := fun q => positiveRoot_nonzero (m q) (hm q) (fun x => (hp q x).1)
    ∃ hk : ∀ q x,(k q : X → ℂ) x≠0,
    ∃ hL : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0,
    ∃ p : Fin 2 → Fin 3 → Fin 3 → Smooth,∃ s : Fin 2 → Fin 3 → Smooth,
    ∃ B : X → Module.Basis (Fin 3) ℂ (ElasticityFrame.Fiber θ),
      (∀ q ν,normal θ (p q ν)=0) ∧
      (∀ q ν x,x∈Metric.ball 0 (r₀+3) →
        (∀ i,(direction (A := Smooth) coord θ (p q ν i) : X → ℂ) x=θ i*(s q ν : X → ℂ) x) ∧
        (direction (A := Smooth) coord θ (s q ν) : X → ℂ) x=
          ((transportT θ (k q) (r q) (hk q) (hL q)*s q ν+
            ∑ i,transportQ θ (k q) (r q) (hr q) (hk q) (hL q) i*p q ν i : Smooth) : X → ℂ) x) ∧
      (∀ ν x,x∉closure Ω → (∀ i,(p 0 ν i : X → ℂ) x=(p 1 ν i : X → ℂ) x) ∧
        (s 0 ν : X → ℂ) x=(s 1 ν : X → ℂ) x) ∧
      ∀ ν x,((B x ν : ElasticityFrame.Fiber θ) : ElasticityFrame.Amp)=
        ((fun i => (p 0 ν i : X → ℂ) x),(s 0 ν : X → ℂ) x) := by
  intro k r hr
  obtain ⟨α,β,hα,hαβ⟩ := null_real_imag θ hθ hne
  have heq (i) := congrFun hαβ i
  have hθ' : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0 := by
    simpa only [← heq] using hθ
  have hh := dn_common_leading_frame hΩ hOB r₀ hr₀ hK α β hα hθ' lam m hl hm hp hcll hclm he hDN
  dsimp only at hh
  rw [← hαβ] at hh
  obtain ⟨a,B,hn,hR,hS,hs,hB⟩ := hh
  have hr2 (q) : r q*r q=smoothOfReal (m q) (hm q) := positiveRoot_square _ _ _
  have hk : ∀ q x,(k q : X → ℂ) x≠0 := by
    intro q x
    change (lam q x : ℂ)+(m q x : ℂ)≠0
    exact_mod_cast (real_k_positive (lam q) (m q) (hp q) x).ne'
  have hL : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0 := by
    intro q x
    rw [hr2]
    change (lam q x : ℂ)+(m q x : ℂ)+(m q x : ℂ)≠0
    exact_mod_cast (real_longitudinal_positive (lam q) (m q) (hp q) x).ne'
  let p := fun q ν => changeP (r q) (a q ν).1
  let s := fun q ν => changeS (k q) (r q) (hr q) (a q ν).1 (a q ν).2
  refine ⟨hk,hL,p,s,B,?_,?_,?_,hB⟩
  · intro q ν
    have heq : normal θ (p q ν)=r q*normal θ (a q ν).1 := by
      simp only [p,normal,changeP,Algebra.smul_def,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [heq,hn,mul_zero]
  · intro q ν x hx
    apply (leading_equations_at_iff θ (k q) (r q) (hr q) (hk q) (hL q) (a q ν).1 (a q ν).2 x).mp
    simpa only [hr2,k,add_sub_cancel_right] using ⟨fun i => hR q ν i hx,hS q ν hx⟩
  · intro ν x hx
    have hkE : EqOn (k 0 : X → ℂ) (k 1) (closure Ω)ᶜ := by
      intro y hy
      have hy' : y∉Ω := fun hyΩ => hy (subset_closure hyΩ)
      change (lam 0 y : ℂ)+(m 0 y : ℂ)=(lam 1 y : ℂ)+(m 1 y : ℂ)
      rw [(he y hy').1,(he y hy').2]
    have hrE : EqOn (r 0 : X → ℂ) (r 1) (closure Ω)ᶜ := by
      intro y hy
      change (Real.sqrt (m 0 y) : ℂ)=(Real.sqrt (m 1 y) : ℂ)
      rw [(he y (fun hyΩ => hy (subset_closure hyΩ))).2]
    have haE (i : Fin 4) : EqOn
        (((Fin.cons (a 0 ν).2 (a 0 ν).1 : Fin 4 → Smooth) i) : X → ℂ)
        ((Fin.cons (a 1 ν).2 (a 1 ν).1 : Fin 4 → Smooth) i) (closure Ω)ᶜ := by
      intro y hy
      have hz := image_eq_zero_of_notMem_tsupport (fun hh => hy (hs ν i hh))
      exact (sub_eq_zero.mp hz).symm
    have hc := eqOn_physical_change isClosed_closure.isOpen_compl (k 0) (k 1) (r 0) (r 1)
      (hr 0) (hr 1) (a 0 ν).1 (a 1 ν).1 (a 0 ν).2 (a 1 ν).2 hkE hrE
      (fun i => haE i.succ) (haE 0)
    exact ⟨fun i => hc.1 i hx,hc.2 hx⟩
end Elasticity

end
end

end OAI
end

theorem solution : type_of% @OAI.Elasticity.dn_common_normal_frame_oai := @OAI.Elasticity.dn_common_normal_frame_oai
