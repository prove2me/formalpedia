-- Prove2me | solution 1 for OAI.ElasticityDistribution.smooth_column_patch
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:37:07.513482+00:00
-- url     : https://prove2.me/submissions/212196ca-3dc5-421e-ba80-829679ec8dd8

import Mathlib
import Definitions.Def_OAIQ6El006

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

/-! Positive commutator algebra on actual Schwartz functions, allowing
nonlocal Bessel shifts without silently retaining compact support. -/
open MeasureTheory Complex SchwartzMap LineDeriv
open scoped BigOperators LineDeriv SchwartzMap

namespace ElasticityNegativeOrder
open ElasticityBessel
open ElasticitySchwartzCarleman

section

lemma mult_apply (a : X → ℂ) (ha : a.HasTemperateGrowth) (f : S) (x : X) :
    mult a f x = a x * f x :=
  SchwartzMap.smulLeftCLM_apply_apply ha f x

end

end ElasticityNegativeOrder

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Carleman
attribute [-instance] _root_.OAI.ElasticityDistribution.instIsCentralScalarSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexMulOppositeSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulCommClassComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

namespace ElasticityPhysicalAlgebra
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder

lemma toSmooth_mult (a : Smooth) (ha : (a : X → ℂ).HasTemperateGrowth) (f : S) :
    toSmooth (mult a f) = a*toSmooth f := by
  apply Subtype.ext
  funext x
  exact mult_apply a ha f x

end ElasticityPhysicalAlgebra

open scoped BigOperators

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
open Set MeasureTheory SchwartzMap
open scoped BigOperators SchwartzMap Topology

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Regularity
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Actual distributional elliptic regularity dependencies of the physical and
planar weak-limit constructions. No regularity assumption on an L2 unknown is
used in the gain of Sobolev order below. -/
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal

open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
namespace ElasticityDistribution

open ElasticityAugmented ElasticityRegularity TemperedDistribution
lemma dd_apply (i : Fin 3) (u : Dist) : dd i u = ∂_{e i} u := rfl

open ElasticityAugmented TrivSqZeroExt

end ElasticityDistribution

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators

open scoped SchwartzMap LineDeriv BigOperators
open scoped SchwartzMap LineDeriv Laplacian BigOperators

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_LocalRegularity
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal
namespace ElasticityRegularity


section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace LocalEqual
variable {Ω : Set E} {u v w u' v' : 𝓢'(E,ℂ)}
lemma cutoff (h : LocalEqual Ω u v) {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) :
    smulLeftCLM ℂ g u = smulLeftCLM ℂ g v := by
  ext φ
  change u (SchwartzMap.smulLeftCLM ℂ g φ) = v (SchwartzMap.smulLeftCLM ℂ g φ)
  apply h
  · simpa only [SchwartzMap.smulLeftCLM_apply (hc.hasTemperateGrowth hg),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (hc.mul_right : HasCompactSupport (g * (φ : E → ℂ)))
  · simpa only [SchwartzMap.smulLeftCLM_apply (hc.hasTemperateGrowth hg),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (tsupport_mul_subset_left (f := g) (g := (φ : E → ℂ))).trans hs
end LocalEqual
end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartz_dist_injective : Function.Injective (fun u : 𝓢(E,ℂ) => (u : 𝓢'(E,ℂ))) := by
  intro u v h
  apply SchwartzMap.injective_toLp 2 volume
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ))
  change ((u.toLp 2 volume : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E,ℂ)) =
    ((v.toLp 2 volume : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E,ℂ))
  simpa only [Lp.toTemperedDistribution_toLp_eq] using h

lemma distribution_schwartz_product {g : E → ℂ} (hg : g.HasTemperateGrowth) (u : 𝓢(E,ℂ)) :
    smulLeftCLM ℂ g (u : 𝓢'(E,ℂ)) = (SchwartzMap.smulLeftCLM ℂ g u : 𝓢'(E,ℂ)) := by
  ext φ
  simp only [smulLeftCLM_apply_apply,SchwartzMap.coe_apply,SchwartzMap.smulLeftCLM_apply_apply hg,
    smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

lemma LocalEqual.schwartz_eqOn {Ω : Set E} (hΩ : IsOpen Ω)
    {u v : 𝓢(E,ℂ)} (h : LocalEqual Ω (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ))) :
    Set.EqOn (u : E → ℂ) (v : E → ℂ) Ω := by
  intro x hx
  obtain ⟨g,hs,hc,hg,_,h1⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hΩ.mem_nhds hx)
  let f : E → ℂ := fun y => (g y : ℂ)
  have hfc : HasCompactSupport f :=
    show HasCompactSupport (Complex.ofReal ∘ g) from hc.comp_left Complex.ofReal_zero
  have hfg : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff : ContDiff ℝ (⊤ : ℕ∞) Complex.ofReal).comp hg
  have hfs : tsupport f ⊆ Ω := by
    change closure (Function.support f) ⊆ Ω
    apply Set.Subset.trans (closure_mono ?_) hs
    intro y hy
    change g y ≠ 0
    intro hy0
    apply hy
    change (g y : ℂ)=0
    rw [hy0,Complex.ofReal_zero]
  have he := h.cutoff hfg hfc hfs
  rw [distribution_schwartz_product (hfc.hasTemperateGrowth hfg),
    distribution_schwartz_product (hfc.hasTemperateGrowth hfg)] at he
  have he' := congrArg (fun w : 𝓢(E,ℂ) => w x) (schwartz_dist_injective he)
  simp only [SchwartzMap.smulLeftCLM_apply_apply (hfc.hasTemperateGrowth hfg),smul_eq_mul] at he'
  have hx1 : f x=1 := by simp only [f,h1,Complex.ofReal_one]
  simpa only [hx1,one_mul] using he'

end

end ElasticityRegularity

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators ENNReal
namespace ElasticityDistribution
open ElasticityAugmented ElasticityPhysicalAlgebra ElasticityNegativeOrder

lemma coe_schwartz_add (u v : S) : ((u+v : S) : Dist)=(u : Dist)+(v : Dist) := map_add _ _ _
lemma coe_schwartz_smul (c : ℂ) (u : S) : ((c • u : S) : Dist)=c • (u : Dist) := map_smul _ _ _
lemma coe_schwartz_sum {ι : Type*} (s : Finset ι) (u : ι → S) :
    ((∑ i ∈ s, u i : S) : Dist)=∑ i ∈ s, (u i : Dist) := map_sum _ _ _
lemma coeff_schwartz (a : Coeff) (u : S) : a • (u : Dist)=(mult (eval a) u : Dist) :=
  ElasticityRegularity.distribution_schwartz_product (growth a) u
end ElasticityDistribution

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Smoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityDistribution
open Set TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityAugmented ElasticityPhysicalAlgebra ElasticityNegativeOrder

lemma schwartzDirection_dist (θ : Fin 3 → ℂ) (u : Test) :
    (schwartzDirection θ u : Dist)=directiond θ (u : Dist) := by
  simp only [schwartzDirection,directiond,coe_schwartz_sum,coe_schwartz_smul,dd_apply,
    lineDerivOp_toTemperedDistributionCLM_eq]
lemma schwartzLeadingR_dist (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Test) (b : Test) (i : Fin 3) :
    (schwartzLeadingR θ lam m u b i : Dist)=leadingRd θ lam m (fun j => (u j : Dist)) (b : Dist) i := by
  simp only [schwartzLeadingR,leadingRd,coe_schwartz_add,coe_schwartz_smul,coe_schwartz_sum,
    ← coeff_schwartz,schwartzDirection_dist]
lemma schwartzLeadingS_dist (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Test) (b : Test) :
    (schwartzLeadingS θ lam m u b : Dist)=leadingSd θ lam m (fun j => (u j : Dist)) (b : Dist) := by
  simp only [schwartzLeadingS,leadingSd,coe_schwartz_add,coe_schwartz_sum,
    ← coeff_schwartz,schwartzDirection_dist]
lemma schwartzDirection_smooth (θ : Fin 3 → ℂ) (u : Test) :
    toSmooth (schwartzDirection θ u)=direction coord θ (toSmooth u) := by
  simp only [schwartzDirection,direction,map_sum,map_smul]
  congr 1
lemma direction_coeff_val (θ : Fin 3 → ℂ) (m : Coeff) :
    (direction dc θ m).val=direction coord θ m.val := by
  apply Subtype.ext
  rfl
lemma toSmooth_coeff_mult (a : Coeff) (u : Test) :
    toSmooth (mult (eval a) u)=a.val*toSmooth u :=
  toSmooth_mult a.val (growth a) u
lemma dc_coeff_val (i : Fin 3) (m : Coeff) : (dc i m).val=coord i m.val := rfl
lemma schwartzLeadingR_smooth (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Test) (b : Test) (i : Fin 3) :
    toSmooth (schwartzLeadingR θ lam m u b i)=leadingR coord θ lam.val m.val (fun j => toSmooth (u j)) (toSmooth b) i := by
  simp only [schwartzLeadingR,map_add,map_smul,map_sum,
    toSmooth_coeff_mult,schwartzDirection_smooth,leadingR,direction_coeff_val,dc_coeff_val]
  rfl
lemma schwartzLeadingS_smooth (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Test) (b : Test) :
    toSmooth (schwartzLeadingS θ lam m u b)=leadingS coord θ lam.val m.val (fun j => toSmooth (u j)) (toSmooth b) := by
  simp only [schwartzLeadingS,map_add,map_sum,
    toSmooth_coeff_mult,schwartzDirection_smooth,leadingS,direction_coeff_val,dc_coeff_val]
  simp only [Finset.mul_sum]
  rfl
lemma leading_classical {B : Set X} (hB : IsOpen B) (θ : Fin 3 → ℂ) (lam m : Coeff)
    (u : Fin 3 → Test) (b : Test)
    (hr : ∀ i,LocalEq B (leadingRd θ lam m (fun j => (u j : Dist)) (b : Dist) i) 0)
    (hs : LocalEq B (leadingSd θ lam m (fun j => (u j : Dist)) (b : Dist)) 0) :
    (∀ i,EqOn ((leadingR coord θ lam.val m.val (fun j => toSmooth (u j)) (toSmooth b) i).val) 0 B) ∧
      EqOn ((leadingS coord θ lam.val m.val (fun j => toSmooth (u j)) (toSmooth b)).val) 0 B := by
  have h0 : ((0 : Test) : Dist)=0 := map_zero _
  constructor
  · intro i
    have hh : ElasticityRegularity.LocalEqual B (schwartzLeadingR θ lam m u b i : Dist) ((0 : Test) : Dist) := by
      simpa only [schwartzLeadingR_dist,h0,LocalEq,ElasticityRegularity.LocalEqual] using hr i
    have hh' := hh.schwartz_eqOn hB
    intro x hx
    rw [← schwartzLeadingR_smooth]
    exact hh' hx
  · have hh : ElasticityRegularity.LocalEqual B (schwartzLeadingS θ lam m u b : Dist) ((0 : Test) : Dist) := by
      simpa only [schwartzLeadingS_dist,h0,LocalEq,ElasticityRegularity.LocalEqual] using hs
    intro x hx
    rw [← schwartzLeadingS_smooth]
    exact hh.schwartz_eqOn hB hx
end ElasticityDistribution
section
open Set Filter TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators Topology
namespace ElasticityDistribution
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth)
lemma normal_classical {B : Set X} (hB : IsOpen B) (θ : Fin 3 → ℂ) (u : Fin 3 → Test)
    (hn : LocalEq B (normald θ (fun j => (u j : Dist))) 0) :
    EqOn (normal θ (fun j => toSmooth (u j))).val 0 B := by
  let w : Test := ∑ i,θ i • u i
  have hw : (w : Dist)=normald θ (fun j => (u j : Dist)) := by
    simp only [w,normald,coe_schwartz_sum,coe_schwartz_smul]
  have hl : ElasticityRegularity.LocalEqual B (w : Dist) ((0 : Test) : Dist) := by
    simpa only [hw,map_zero,LocalEq,ElasticityRegularity.LocalEqual] using hn
  have he : toSmooth w=normal θ (fun j => toSmooth (u j)) := by
    simp only [w,normal,map_sum,map_smul]
  intro x hx
  rw [← he]
  exact hl.schwartz_eqOn hB hx
end ElasticityDistribution

end
open Set Filter TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators Topology
namespace ElasticityAugmented
lemma direction_eqOn {B : Set X} (hB : IsOpen B) (θ : Fin 3 → ℂ) {a b : Smooth}
    (h : EqOn (a : X → ℂ) (b : X → ℂ) B) :
    EqOn (direction (A := Smooth) coord θ a : X → ℂ) (direction (A := Smooth) coord θ b : X → ℂ) B := by
  intro x hx
  have he : (a : X → ℂ)=ᶠ[𝓝 x] (b : X → ℂ) := Filter.mem_of_superset (hB.mem_nhds hx) h
  change (∑ i,θ i*fderiv ℝ (a : X → ℂ) x (e i))=(∑ i,θ i*fderiv ℝ (b : X → ℂ) x (e i))
  rw [he.fderiv_eq]
lemma leadingR_eqOn {B : Set X} (hB : IsOpen B) (θ : Fin 3 → ℂ) (lam m : Smooth)
    {a a' : Fin 3 → Smooth} {b b' : Smooth}
    (ha : ∀ i,EqOn (a i : X → ℂ) (a' i : X → ℂ) B)
    (hb : EqOn (b : X → ℂ) (b' : X → ℂ) B) (i) :
    EqOn (leadingR (A := Smooth) coord θ lam m a b i : X → ℂ) (leadingR (A := Smooth) coord θ lam m a' b' i : X → ℂ) B := by
  intro x hx
  change ((2*m : Smooth) : X → ℂ) x*(direction (A := Smooth) coord θ (a i) : X → ℂ) x+
    (direction (A := Smooth) coord θ m : X → ℂ) x*(a i : X → ℂ) x+θ i*(((lam+m : Smooth) : X → ℂ) x*(b : X → ℂ) x+
      ∑ j,(coord j m : X → ℂ) x*(a j : X → ℂ) x)=_
  rw [direction_eqOn hB θ (ha i) hx,ha i hx,hb hx]
  have hs : (∑ j,(coord j m : X → ℂ) x*(a j : X → ℂ) x)=
      ∑ j,(coord j m : X → ℂ) x*(a' j : X → ℂ) x :=
    Finset.sum_congr rfl (fun j _ => congrArg ((coord j m : X → ℂ) x*·) (ha j hx))
  rw [hs]
  rfl
lemma leadingS_eqOn {B : Set X} (hB : IsOpen B) (θ : Fin 3 → ℂ) (lam m : Smooth)
    {a a' : Fin 3 → Smooth} {b b' : Smooth}
    (ha : ∀ i,EqOn (a i : X → ℂ) (a' i : X → ℂ) B)
    (hb : EqOn (b : X → ℂ) (b' : X → ℂ) B) :
    EqOn (leadingS (A := Smooth) coord θ lam m a b : X → ℂ) (leadingS (A := Smooth) coord θ lam m a' b' : X → ℂ) B := by
  intro x hx
  change ((2*(lam+m+m) : Smooth) : X → ℂ) x*(direction (A := Smooth) coord θ b : X → ℂ) x+
    ((2*direction (A := Smooth) coord θ (lam+m) : Smooth) : X → ℂ) x*(b : X → ℂ) x+
    4*(∑ i,(coord i m : X → ℂ) x*(direction (A := Smooth) coord θ (a i) : X → ℂ) x)+
    2*(∑ i,(direction (A := Smooth) coord θ (coord i m) : X → ℂ) x*(a i : X → ℂ) x)=_
  rw [direction_eqOn hB θ hb hx,hb hx]
  have hd := fun i => direction_eqOn hB θ (ha i) hx
  simp only [hd,fun i => ha i hx]
  rfl
end ElasticityAugmented
namespace ElasticityDistribution
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth)
/-- Patch the actual smooth representative to the original unlocalized
amplitude, without pretending the localization derivative vanishes globally. -/
theorem smooth_column_patch_oai {K B : Set X} (hB : IsOpen B) (hKB : K⊆B)
    (θ : Fin 3 → ℂ) (lam m : Coeff) (v φ : Fin 4 → Test) (a₀ : Fin 4 → Smooth)
    (hs : ∀ i,tsupport (v i-φ i : Test)⊆K)
    (hφ : ∀ i,EqOn (φ i : X → ℂ) (a₀ i : X → ℂ) B)
    (hr : ∀ i,LocalEq B (leadingRd θ lam m (fun j => (v j.succ : Dist)) (v 0 : Dist) i) 0)
    (he : LocalEq B (leadingSd θ lam m (fun j => (v j.succ : Dist)) (v 0 : Dist)) 0)
    (hn : LocalEq B (normald θ (fun j => (v j.succ : Dist))) 0)
    (hn₀ : normal θ (fun j => a₀ j.succ)=0) :
    ∃ a : Fin 4 → Smooth,
      (∀ i,tsupport ((a i-a₀ i : Smooth) : X → ℂ)⊆K) ∧
      (∀ i,EqOn (leadingR (A := Smooth) coord θ lam.val m.val (fun j => a j.succ) (a 0) i : X → ℂ) 0 B) ∧
      EqOn (leadingS (A := Smooth) coord θ lam.val m.val (fun j => a j.succ) (a 0) : X → ℂ) 0 B ∧
      normal θ (fun j => a j.succ)=0 := by
  let a := fun i => a₀ i+toSmooth (v i-φ i)
  have ha (i) : EqOn (a i : X → ℂ) (toSmooth (v i) : X → ℂ) B := by
    intro x hx
    change (a₀ i : X → ℂ) x+(v i x-φ i x)=v i x
    rw [hφ i hx]
    ring
  have hsp (i) : tsupport ((a i-a₀ i : Smooth) : X → ℂ)⊆K := by
    have hh : ((a i-a₀ i : Smooth) : X → ℂ)=(v i-φ i : Test) := by
      funext x
      change (a₀ i : X → ℂ) x+(v i x-φ i x)-(a₀ i : X → ℂ) x=v i x-φ i x
      ring
    rw [hh]
    exact hs i
  obtain ⟨hR,hS⟩ := leading_classical hB θ lam m (fun j => v j.succ) (v 0) hr he
  refine ⟨a,hsp,fun i => (leadingR_eqOn hB θ lam.val m.val (fun j => ha j.succ) (ha 0) i).trans (hR i),
    (leadingS_eqOn hB θ lam.val m.val (fun j => ha j.succ) (ha 0)).trans hS,?_⟩
  apply Subtype.ext
  funext x
  by_cases hx : x∈B
  · have hh := normal_classical hB θ (fun j => v j.succ) hn hx
    change (∑ j,θ j*(a j.succ : X → ℂ) x)=0
    change (∑ j,θ j*v j.succ x)=0 at hh
    rw [show (∑ j,θ j*(a j.succ : X → ℂ) x)=(∑ j,θ j*v j.succ x) from
      Finset.sum_congr rfl (fun j _ => congrArg (θ j*·) (ha j.succ hx))]
    exact hh
  · have hh (i) : (a i : X → ℂ) x=(a₀ i : X → ℂ) x := by
      have hz := image_eq_zero_of_notMem_tsupport (f := ((a i-a₀ i : Smooth) : X → ℂ))
        (fun hn => hx (hKB (hsp i hn)))
      exact sub_eq_zero.mp hz
    change (∑ j,θ j*(a j.succ : X → ℂ) x)=0
    simp only [hh]
    exact congrArg (fun f : Smooth => (f : X → ℂ) x) hn₀
end ElasticityDistribution

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityDistribution.smooth_column_patch_oai := @OAI.ElasticityDistribution.smooth_column_patch_oai
