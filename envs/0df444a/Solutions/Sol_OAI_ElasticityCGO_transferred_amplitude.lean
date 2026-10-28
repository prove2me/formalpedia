-- Prove2me | solution 1 for OAI.ElasticityCGO.transferred_amplitude
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:13:08.173021+00:00
-- url     : https://prove2.me/submissions/7f045635-0692-4acb-8965-1c30b44c8f91

import Mathlib
import Definitions.Def_OAIQ6El004

section
-- module Solutions.OAIQ6_Elast.Elasticity_Augmented
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact differential-algebra identities of the physical and normalized
augmented elasticity systems. Smooth derivatives are constructed below;
commutation and Leibniz are proved, not postulated for the physical operator. -/
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

section DifferentialAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A)

omit [Fintype ι] in
lemma partial_mul (i : ι) (a b : A) : D i (a*b) = D i a*b + a*D i b := by
  simpa only [smul_eq_mul, add_comm, mul_comm] using (D i).leibniz a b

end DifferentialAlgebra

section CovariantAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A) (T : ι → A →ₗ[ℂ] A)

variable (hD : ∀ i j f, D i (D j f) = D j (D i f))
variable (hT : ∀ i j f, T i (T j f) = T j (T i f))
variable (hTD : ∀ i a b, T i (a*b) = D i a*b+a*T i b)

omit [Fintype ι] in
lemma shifted_apply (z : ι → ℂ) (i : ι) (f : A) :
    shifted D z i f = D i f + z i • f := rfl

end CovariantAlgebra

end ElasticityAugmented

end

end OAI
end

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

lemma toSmooth_d (f : S) (i : Fin 3) :
    toSmooth (d (e i) f) = ElasticityAugmented.coord i (toSmooth f) := by
  apply Subtype.ext
  rfl

lemma toSmooth_mult (a : Smooth) (ha : (a : X → ℂ).HasTemperateGrowth) (f : S) :
    toSmooth (mult a f) = a*toSmooth f := by
  apply Subtype.ext
  funext x
  exact mult_apply a ha f x

lemma shiftD_apply (z : Fin 3 → ℂ) (i : Fin 3) (f : S) :
    shiftD z i f = d (e i) f + z i • f := rfl

lemma toSmooth_shiftD (z : Fin 3 → ℂ) (i : Fin 3) (f : S) :
    toSmooth (shiftD z i f) = ElasticityAugmented.shifted ElasticityAugmented.coord z i (toSmooth f) := by
  simp only [shiftD_apply, map_add, map_smul, toSmooth_d, ElasticityAugmented.shifted_apply]

lemma toSmooth_physical (z : Fin 3 → ℂ) (lam m : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (u : Fin 3 → S) (i : Fin 3) :
    toSmooth (physical z lam m u i) =
      ElasticityAugmented.LT (ElasticityAugmented.shifted ElasticityAugmented.coord z)
        lam m (fun j => toSmooth (u j)) i := by
  simp only [physical, ElasticityAugmented.LT, ElasticityAugmented.divT, map_add, map_sum,
    toSmooth_shiftD, toSmooth_mult lam hl, toSmooth_mult m hm,
    Finset.mul_sum, mul_add]

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
end ElasticityAugmented

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_CGO
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

lemma restrict_shifted {U : Set X} (hU : IsOpen U) (z : Fin 3 → ℂ) (i : Fin 3) (f : Smooth) :
    restrictSmooth U (shifted coord z i f)=shifted (localCoord hU) z i (restrictSmooth U f) := by
  simp only [shifted_apply,map_add,map_smul,localCoord_restrict]
lemma restrict_LT {U : Set X} (hU : IsOpen U) (z : Fin 3 → ℂ) (lam m : Smooth)
    (a : Fin 3 → Smooth) (i : Fin 3) :
    restrictSmooth U (LT (shifted coord z) lam m a i)=
      LT (shifted (localCoord hU) z) (restrictSmooth U lam) (restrictSmooth U m)
        (fun j => restrictSmooth U (a j)) i := by
  simp only [LT,divT,restrict_shifted hU,map_mul,map_sum,map_add]

end ElasticityAugmented

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
open Set MeasureTheory
open scoped BigOperators SchwartzMap
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth toSmooth_apply toSmooth_physical physical phase)
lemma cut_local {U : Set X} (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ))
    (hχ : EqOn (χ : X → ℂ) 1 U) (f : Smooth) :
    restrictSmooth U (toSmooth (cut χ hc f))=restrictSmooth U f := by
  apply (restrictSmooth_eq_iff U _ _).mpr
  intro x hx
  simp only [toSmooth_apply,cut_apply,hχ hx,Pi.one_apply,one_mul]
lemma physical_cut_local {U : Set X} (hU : IsOpen U)
    (z : Fin 3 → ℂ) (lam m χ : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    (u : Fin 3 → Smooth) (i : Fin 3) :
    EqOn (physical z lam m (fun j => cut χ hc (u j)) i : X → ℂ)
      ((LT (shifted coord z) lam m u i : Smooth) : X → ℂ) U := by
  change EqOn ((toSmooth (physical z lam m (fun j => cut χ hc (u j)) i) : Smooth) : X → ℂ) _ U
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [toSmooth_physical z lam m hl hm,restrict_LT hU,restrict_LT hU]
  congr 1
  funext j
  exact cut_local χ hc hχ (u j)

end ElasticityCGO

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators SchwartzMap
namespace ElasticityPhysicalAlgebra
open ElasticityAugmented

lemma physical_eqOn_of_eqOn {U : Set X} (hU : IsOpen U)
    (z : Fin 3 → ℂ) (lam m : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (f g : Fin 3 → SchwartzMap X ℂ) (hfg : ∀ j,EqOn (f j : X → ℂ) (g j) U) (i : Fin 3) :
    EqOn (physical z lam m f i : X → ℂ) (physical z lam m g i) U := by
  change EqOn ((toSmooth (physical z lam m f i) : Smooth) : X → ℂ)
    ((toSmooth (physical z lam m g i) : Smooth) : X → ℂ) U
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [toSmooth_physical z lam m hl hm,toSmooth_physical z lam m hl hm,
    restrict_LT hU,restrict_LT hU]
  congr 1
  funext j
  exact (restrictSmooth_eq_iff U _ _).mpr (hfg j)

end ElasticityPhysicalAlgebra

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented
section Algebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A) (z : ι → ℂ) (χ : A)
omit [Fintype ι] in
lemma deriv_phase_mul (hχ : ∀ i,D i χ=z i • χ) (i : ι) (f : A) :
    D i (χ*f)=χ*(shifted D z i f) := by
  rw [partial_mul,hχ,shifted_apply]
  simp only [Algebra.smul_def]
  ring

/-- The shifted operator is the literal exponential conjugation of the
physical stress-divergence, not a new PDE declared equivalent by hypothesis. -/
theorem physical_phase_conjugation (hχ : ∀ i,D i χ=z i • χ)
    (lam m : A) (u : ι → A) (i : ι) :
    LT (fun j => (D j).toLinearMap) lam m (fun j => χ*u j) i =
      χ*LT (shifted D z) lam m u i := by
  have hd (j) (f) := deriv_phase_mul D z χ hχ j f
  change D i (lam*(∑ j,D j (χ*u j)))+
    ∑ j,D j (m*(D j (χ*u i)+D i (χ*u j)))=_
  simp only [hd,← Finset.mul_sum,← mul_add]
  have hfirst : lam*(χ*(∑ j,shifted D z j (u j)))=χ*(lam*(∑ j,shifted D z j (u j))) := by ring
  have hsecond (j) : m*(χ*(shifted D z j (u i)+shifted D z i (u j)))=
      χ*(m*(shifted D z j (u i)+shifted D z i (u j))) := by ring
  rw [hfirst,hd]
  simp_rw [hsecond,hd]
  rw [← Finset.mul_sum,← mul_add]
  rfl
end Algebra

lemma coord_exponential (L : X →L[ℝ] ℂ) (i : Fin 3) :
    coord i (exponential L)=L (e i) • exponential L := by
  apply Subtype.ext
  funext x
  have hh := congrArg (fun K : X →L[ℝ] ℂ => K (e i)) (L.hasFDerivAt.cexp.fderiv (x := x))
  change fderiv ℝ (fun y => Complex.exp (L y)) x (e i)=L (e i)*Complex.exp (L x)
  simpa only [smul_apply,smul_eq_mul,mul_comm] using hh

theorem physical_exponential_conjugation (L : X →L[ℝ] ℂ) (lam m : Smooth)
    (u : Fin 3 → Smooth) (i : Fin 3) :
    LT (fun j => (coord j).toLinearMap) lam m (fun j => exponential L*u j) i=
      exponential L*LT (shifted coord (fun j => L (e j))) lam m u i :=
  physical_phase_conjugation coord (fun j => L (e j)) (exponential L) (coord_exponential L) lam m u i
end ElasticityAugmented

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators FourierTransform

namespace ElasticityCarleman

lemma phaseCLM_e (θ : Direction) (i : Fin 3) : phaseCLM θ (e i) = θ i := by
  simp [phaseCLM, e, EuclideanSpace.proj, apply_ite]

end ElasticityCarleman

end
end
section
noncomputable section
open Set
open scoped BigOperators SchwartzMap
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth toSmooth_apply toSmooth_physical physical)
open ElasticityCarleman (phaseCLM phaseCLM_e)

lemma shifted_zero : shifted coord (0 : Fin 3 → ℂ)=fun j => (coord j).toLinearMap := by
  funext j
  apply LinearMap.ext
  intro f
  change coord j f+(0 : ℂ) • f=coord j f
  rw [zero_smul,add_zero]
lemma phaseCLM_coords (z : Fin 3 → ℂ) : (fun j => phaseCLM z (e j))=z := by
  funext j
  exact phaseCLM_e z j

/-- The literal unshifted stress-divergence of a cut-off exponential field. -/
theorem expCut_physical {U : Set X} (hU : IsOpen U) (lam m χ : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    (z : Fin 3 → ℂ) (f : Fin 3 → S) (i : Fin 3) :
    EqOn (physical 0 lam m (fun j => expCut χ hc z (f j)) i : X → ℂ)
      (fun x => Complex.exp (phaseCLM z x)*physical z lam m f i x) U := by
  intro x hx
  change physical 0 lam m (fun j => cut χ hc (exponential (phaseCLM z)*toSmooth (f j))) i x=_
  rw [physical_cut_local hU 0 lam m χ hl hm hc hχ _ i hx,shifted_zero,
    physical_exponential_conjugation,phaseCLM_coords,← toSmooth_physical z lam m hl hm f i]
  rfl

end ElasticityCGO

end
end
section
noncomputable section
open Set
open scoped BigOperators SchwartzMap
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (physical physical_eqOn_of_eqOn shiftD shiftD_apply)
open ElasticityCarleman (phaseCLM)

lemma phaseCLM_neg (z : Fin 3 → ℂ) : phaseCLM (-z)=-phaseCLM z := by
  ext x
  simp only [ElasticityCarleman.phaseCLM,sum_apply,smul_apply,
    Pi.neg_apply,neg_apply,smul_eq_mul,neg_mul,Finset.sum_neg_distrib]

lemma expCut_support (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ))
    (z : Fin 3 → ℂ) (f : S) : tsupport (expCut χ hc z f : X → ℂ)⊆tsupport (f : X → ℂ) := by
  have he : (expCut χ hc z f : X → ℂ)=
      (fun x => (χ : X → ℂ) x*Complex.exp (phaseCLM z x))*(f : X → ℂ) := by
    funext x
    exact expCut_apply χ hc z f x
  rw [he]
  exact tsupport_mul_subset_right

/-- Factoring the transferred PHYSICAL solution gives a shifted physical
solution. The compact difference is multiplied by the inverse exponential only
on a compact support, never regarded as a global temperate multiplier. -/
theorem transferred_amplitude_oai {B K : Set X} (hB : IsOpen B)
    (lam m χ : Smooth) (hl : (lam : X → ℂ).HasTemperateGrowth)
    (hm : (m : X → ℂ).HasTemperateGrowth) (hc : HasCompactSupport (χ : X → ℂ))
    (hχ : EqOn (χ : X → ℂ) 1 B) (z : Fin 3 → ℂ) (u F H : Fin 3 → S)
    (hF : ∀ i x,x∈B → F i x=Complex.exp (phaseCLM z x)*u i x)
    (hH : ∀ i,tsupport (H i : X → ℂ)⊆K)
    (hsol : ∀ i,EqOn (physical 0 lam m (F+H) i : X → ℂ) 0 B) :
    ∃ v : Fin 3 → S,
      (∀ i,tsupport (v i-u i : S)⊆K) ∧
      (∀ i,EqOn (physical z lam m v i : X → ℂ) 0 B) ∧
      (∀ i x,x∈B → Complex.exp (phaseCLM z x)*v i x=F i x+H i x) := by
  let w : Fin 3 → S := fun i => expCut χ hc (-z) (H i)
  let v := u+w
  have he : ∀ i x,x∈B → Complex.exp (phaseCLM z x)*v i x=F i x+H i x := by
    intro i x hx
    change Complex.exp (phaseCLM z x)*(u i x+w i x)=F i x+H i x
    dsimp [w]
    rw [expCut_apply,hχ hx,Pi.one_apply,one_mul,phaseCLM_neg]
    change Complex.exp (phaseCLM z x)*(u i x+Complex.exp (-(phaseCLM z x))*H i x)=F i x+H i x
    rw [mul_add,← mul_assoc,← Complex.exp_add,add_neg_cancel,Complex.exp_zero,one_mul,hF i x hx]
  have hex : ∀ i,EqOn (expCut χ hc z (v i) : X → ℂ) ((F+H) i) B := by
    intro i x hx
    rw [expCut_apply,hχ hx,Pi.one_apply,one_mul]
    exact he i x hx
  refine ⟨v,fun i => ?_,fun i x hx => ?_,he⟩
  · have hv : v i-u i=w i := by dsimp [v]; simp only [add_sub_cancel_left]
    rw [hv]
    exact (expCut_support χ hc (-z) (H i)).trans (hH i)
  · have hp := physical_eqOn_of_eqOn hB 0 lam m hl hm
      (fun j => expCut χ hc z (v j)) (F+H) hex i hx
    rw [expCut_physical hB lam m χ hl hm hc hχ z v i hx] at hp
    have hz : Complex.exp (phaseCLM z x)*physical z lam m v i x=0 := hp.trans (hsol i hx)
    exact (mul_eq_zero.mp hz).resolve_left (Complex.exp_ne_zero _)

end ElasticityCGO

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityCGO.transferred_amplitude_oai := @OAI.ElasticityCGO.transferred_amplitude_oai
