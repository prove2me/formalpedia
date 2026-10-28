-- Prove2me | solution 1 for OAI.ElasticityAugmented.exists_physical_recursion_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:46:59.069295+00:00
-- url     : https://prove2.me/submissions/47199241-7f52-45cf-ba84-b66413dc627d

import Mathlib
import Definitions.Def_OAIQ6El004
import Theorems.Thm_OAI_ElasticityAugmented_exists_physical_forced_transport

section
-- module Solutions.OAIQ6_Elast.Elasticity_Augmented
attribute [-instance] _root_.OAI.ElasticityDistribution.instIsCentralScalarSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexMulOppositeSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulCommClassComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
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

lemma coord_coord (f : Smooth) (i j : Fin 3) (x : X) :
    (coord i (coord j f) : X → ℂ) x = fderiv ℝ (fderiv ℝ (f : X → ℂ)) x (e i) (e j) := by
  have hd : Differentiable ℝ (fderiv ℝ (f : X → ℂ)) :=
    ((smooth_coe f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ (f : X → ℂ) y (e j)) x (e i) = _
  rw [fderiv_clm_apply (hd x) (differentiableAt_const (e j))]
  simp

lemma coord_commute (i j : Fin 3) (f : Smooth) : coord i (coord j f) = coord j (coord i f) := by
  apply Subtype.ext
  funext x
  rw [coord_coord, coord_coord]
  exact (smooth_coe f).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) _ _

section DifferentialAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A)

omit [Fintype ι] in
lemma partial_mul (i : ι) (a b : A) : D i (a*b) = D i a*b + a*D i b := by
  simpa only [smul_eq_mul, add_comm, mul_comm] using (D i).leibniz a b

variable (hD : ∀ i j f, D i (D j f) = D j (D i f))
include hD

lemma div_lap (u : ι → A) : div D (fun i => lap D (u i)) = lap D (div D u) := by
  simp only [div, lap, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hD i j, hD i j]

lemma div_cm (m : A) (u : ι → A) :
    div D (cm D m u) =
    2*(∑ i, ∑ j, D i (D j m)*D i (u j)) +
      (∑ i, D i m*D i (div D u)) + (∑ i, D i m*lap D (u i)) := by
  have hH : (∑ i, ∑ j, D i (D j m)*D j (u i)) =
      ∑ i, ∑ j, D i (D j m)*D i (u j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hD j i]
  have hv : (∑ i, ∑ j, D j m * D i (D j (u i))) =
      ∑ j, D j m*D j (div D u) := by
    rw [Finset.sum_comm]
    simp only [div, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [hD i j]
  have hl : (∑ i, ∑ j, D j m * D i (D i (u j))) =
      ∑ j, D j m*lap D (u j) := by
    rw [Finset.sum_comm]
    simp only [lap, Finset.mul_sum]
  simp only [div, cm, map_sum, partial_mul, map_add, mul_add, Finset.sum_add_distrib]
  rw [hH, hv, hl]
  simp only [div, map_sum]
  ring

/-- The independent scalar compatibility identity, before imposing d=div u. -/
theorem augmented_identity (lam m : A) (u : ι → A) (d : A) :
    div D (R D lam m u d) - S D lam m u d = P D m (div D u-d) := by
  have hL := div_lap D hD u
  have hC := div_cm D hD m u
  simp only [div] at hL hC
  simp only [div, R, map_add, partial_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hL, hC]
  simp only [S, P, lap, map_sub, map_add, map_sum, mul_sub, add_mul, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  ring_nf
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

end DifferentialAlgebra

end ElasticityAugmented

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
open scoped BigOperators
namespace ElasticityAugmented
section CGO
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A)

lemma leading_normal (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0)
    (lam m : A) (u : Fin 3 → A) (b : A) :
    normal θ (leadingR D θ lam m u b)=leadingP D θ m (normal θ u) := by
  have hz : ∑ i, algebraMap ℂ A (θ i)*algebraMap ℂ A (θ i)=0 := by
    simpa only [map_sum,map_mul,map_zero] using congrArg (algebraMap ℂ A) hθ
  simp only [Fin.sum_univ_three] at hz
  simp only [normal,leadingR,leadingP,direction,Fin.sum_univ_three,map_add,Derivation.map_smul]
  simp only [Algebra.smul_def]
  linear_combination ((lam+m)*b+(D 0 m*u 0+D 1 m*u 1+D 2 m*u 2))*hz

/-- The exact first-order compatibility identity used by the physical recursion. -/
lemma transport_compatibility (θ : Fin 3 → ℂ) (lam m : A) (u : Fin 3 → A) (b : A)
    (hD : ∀ i j f, D i (D j f)=D j (D i f)) :
    div D (leadingR D θ lam m u b)+normal θ (R D lam m u b)-leadingS D θ lam m u b =
      P D m (normal θ u)+leadingP D θ m (div D u-b) := by
  have htwo (i : Fin 3) : D i (2 : A)=0 := (D i).map_natCast 2
  simp only [div,normal,leadingR,leadingS,leadingP,direction,R,P,cm,lap,
    Fin.sum_univ_three,map_add,map_sub,Derivation.map_smul,partial_mul,htwo,zero_mul,zero_add]
  simp only [hD 1 0,hD 2 0,hD 2 1,Algebra.smul_def]
  ring
end CGO
end ElasticityAugmented

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A)

lemma P_neg (m f : A) : P D m (-f)=-P D m f := by
  simp only [P,lap,map_neg,mul_neg,Finset.sum_neg_distrib,neg_add_rev,add_comm]

/-- Compatibility at every recursive stage follows from both augmented rows
and the preceding physical constraint. No extra compatibility is assumed. -/
theorem recursive_normal_compatibility (hD : ∀ i j f, D i (D j f)=D j (D i f))
    (θ : Fin 3 → ℂ) (lam m : A) (u v : Fin 3 → A) (b c : A)
    (hR : leadingR D θ lam m u b=-R D lam m v c)
    (hS : leadingS D θ lam m u b=-S D lam m v c)
    (hn : normal θ u=-(div D v-c)) :
    normal θ (R D lam m u b)=leadingP D θ m (div D u-b) := by
  have hc := transport_compatibility D θ lam m u b hD
  rw [hR,hS,hn,P_neg] at hc
  have hd : div D (-R D lam m v c)= -div D (R D lam m v c) := by
    simp only [div,Pi.neg_apply,map_neg,Finset.sum_neg_distrib]
  rw [hd] at hc
  have hp := augmented_identity D hD lam m v c
  linear_combination hc+hp

end ElasticityAugmented

end
end
section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityAugmented

lemma localCoord_restrict {U : Set X} (hU : IsOpen U) (i : Fin 3) (f : Smooth) :
    localCoord hU i (restrictSmooth U f)=restrictSmooth U (coord i f) := by
  exact Derivation.liftOfSurjective_apply (restrictSmooth_surjective U) (restrict_coord_zero hU i) f
lemma localCoord_commute {U : Set X} (hU : IsOpen U) (i j : Fin 3) (f : LocalSmooth U) :
    localCoord hU i (localCoord hU j f)=localCoord hU j (localCoord hU i f) := by
  obtain ⟨f,rfl⟩ := restrictSmooth_surjective U f
  simp only [localCoord_restrict,coord_commute i j]

lemma restrict_div {U : Set X} (hU : IsOpen U) (a : Fin 3 → Smooth) :
    restrictSmooth U (div coord a)=div (localCoord hU) (fun i => restrictSmooth U (a i)) := by
  simp only [div,map_sum,localCoord_restrict]
lemma restrict_normal (U : Set X) (θ : Fin 3 → ℂ) (a : Fin 3 → Smooth) :
    restrictSmooth U (normal θ a)=normal θ (fun i => restrictSmooth U (a i)) := by
  simp only [normal,map_sum,map_smul]
lemma restrict_direction {U : Set X} (hU : IsOpen U) (θ : Fin 3 → ℂ) (f : Smooth) :
    restrictSmooth U (direction coord θ f)=direction (localCoord hU) θ (restrictSmooth U f) := by
  simp only [direction,map_sum,map_smul,localCoord_restrict]
lemma restrict_R {U : Set X} (hU : IsOpen U) (lam mu : Smooth) (a : Fin 3 → Smooth) (b : Smooth) (i : Fin 3) :
    restrictSmooth U (R coord lam mu a b i)=
      R (localCoord hU) (restrictSmooth U lam) (restrictSmooth U mu)
        (fun i => restrictSmooth U (a i)) (restrictSmooth U b) i := by
  simp only [R,cm,lap,map_add,map_mul,map_sum,localCoord_restrict]
lemma restrict_S {U : Set X} (hU : IsOpen U) (lam mu : Smooth) (a : Fin 3 → Smooth) (b : Smooth) :
    restrictSmooth U (S coord lam mu a b)=
      S (localCoord hU) (restrictSmooth U lam) (restrictSmooth U mu)
        (fun i => restrictSmooth U (a i)) (restrictSmooth U b) := by
  simp only [S,lap,map_add,map_mul,map_ofNat,map_sum,localCoord_restrict]
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
-- module Solutions.OAIQ6_Elast.Elasticity_ForcedTransport
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A)
lemma leadingP_neg (θ : Fin 3 → ℂ) (m f : A) : leadingP D θ m (-f)=-leadingP D θ m f := by
  simp only [leadingP,direction,map_neg,smul_neg,Finset.sum_neg_distrib]
  ring
lemma normal_sub (θ : Fin 3 → ℂ) (u v : Fin 3 → A) : normal θ (u-v)=normal θ u-normal θ v := by
  simp only [normal,Pi.sub_apply,smul_sub,Finset.sum_sub_distrib]
lemma normal_neg (θ : Fin 3 → ℂ) (u : Fin 3 → A) : normal θ (-u)=-normal θ u := by
  simp only [normal,Pi.neg_apply,smul_neg,Finset.sum_neg_distrib]

lemma normal_particular (θ n : Fin 3 → ℂ) (hn : ∑ i,θ i*n i=1) (q : A) :
    normal θ (fun i => -(n i • q))=-q := by
  simp only [normal,smul_neg,smul_smul,Finset.sum_neg_distrib]
  rw [← Finset.sum_smul,hn,one_smul]
lemma exists_normalizing_vector (θ : Fin 3 → ℂ) (hθ : θ≠0) : ∃ n : Fin 3 → ℂ,∑ i,θ i*n i=1 := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hθ
  change θ i≠0 at hi
  refine ⟨Pi.single i (θ i)⁻¹,?_⟩
  simp [Pi.single_apply,hi]

lemma residual_source_tangent (θ n : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hn : ∑ i,θ i*n i=1)
    (lam m : A) (u : Fin 3 → A) (b : A)
    (hc : normal θ (R D lam m u b)=leadingP D θ m (div D u-b)) :
    normal θ (-R D lam m u b-leadingR D θ lam m (fun i => -(n i • (div D u-b))) 0)=0 := by
  rw [normal_sub,normal_neg,leading_normal D θ hθ,normal_particular θ n hn,leadingP_neg,hc]
  exact sub_self _
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
section Algebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A)
lemma leadingR_add (θ : Fin 3 → ℂ) (lam m : A) (u v : Fin 3 → A) (b c : A) :
    leadingR D θ lam m (u+v) (b+c)=leadingR D θ lam m u b+leadingR D θ lam m v c :=
  (leadingRpair D θ lam m).map_add (u,b) (v,c)
lemma leadingS_add (θ : Fin 3 → ℂ) (lam m : A) (u v : Fin 3 → A) (b c : A) :
    leadingS D θ lam m (u+v) (b+c)=leadingS D θ lam m u b+leadingS D θ lam m v c := by
  simp only [leadingS,direction,Pi.add_apply,map_add,smul_add,Finset.sum_add_distrib,mul_add]
  ring
lemma normal_add (θ : Fin 3 → ℂ) (u v : Fin 3 → A) : normal θ (u+v)=normal θ u+normal θ v :=
  (normalPair θ).map_add (u,0) (v,0)
end Algebra

lemma recurs_compatible {U : Set X} (hU : IsOpen U) (θ : Fin 3 → ℂ) (lam m : Smooth)
    (a b : Amplitude Smooth) (h : RecursOn hU θ lam m a b) : CompatibleOn hU θ lam m b := by
  obtain ⟨hR,hS,hn⟩ := h
  apply recursive_normal_compatibility (localCoord hU) (localCoord_commute hU) θ
    (restrictSmooth U lam) (restrictSmooth U m) (localAmp U b).1 (localAmp U a).1
    (localAmp U b).2 (localAmp U a).2 hR hS
  have hh := congrArg (restrictSmooth U) hn
  simpa only [restrict_normal,map_neg,map_sub,restrict_div hU,localAmp] using hh

/-- One actual smooth recursive step, solving all three physical equations.
The open-region restriction algebra certifies differentiated compatibility;
continuity extends the tangent source to its compact closure for transport. -/
theorem exists_physical_recursion_step_oai {U : Set X} (hU : IsOpen U) (hC : IsCompact (closure U))
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (k r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0)
    (a : Amplitude Smooth) (ha : CompatibleOn hU θ (k-r*r) (r*r) a) :
    ∃ b : Amplitude Smooth, RecursOn hU θ (k-r*r) (r*r) a b ∧
      CompatibleOn hU θ (k-r*r) (r*r) b := by
  obtain ⟨n,hn⟩ := exists_normalizing_vector θ hne
  let p : Fin 3 → Smooth := fun i => -(n i • (div coord a.1-a.2))
  let H : Fin 3 → Smooth := -R coord (k-r*r) (r*r) a.1 a.2-leadingR coord θ (k-r*r) (r*r) p 0
  let K : Smooth := -S coord (k-r*r) (r*r) a.1 a.2-leadingS coord θ (k-r*r) (r*r) p 0
  have hp (i) : restrictSmooth U (p i)=-(n i •
      (div (localCoord hU) (localAmp U a).1-(localAmp U a).2)) := by
    simp only [p,map_neg,map_smul,map_sub,restrict_div hU,localAmp]
  have ht : restrictSmooth U (normal θ H)=0 := by
    rw [restrict_normal]
    have hh := residual_source_tangent (localCoord hU) θ n hθ hn
      (restrictSmooth U (k-r*r)) (restrictSmooth U (r*r))
      (localAmp U a).1 (localAmp U a).2 ha
    simpa only [H,Pi.sub_apply,Pi.neg_apply,map_sub,map_neg,restrict_R hU,
      restrict_leadingR hU,map_zero,hp,localAmp,Pi.sub_def,Pi.neg_def] using hh
  have hH : ∀ x∈closure U,((normal θ H : Smooth) : X → ℂ) x=0 := by
    have he : EqOn ((normal θ H : Smooth) : X → ℂ) 0 U :=
      (restrictSmooth_zero_iff U _).mp ht
    exact he.closure (smooth_coe (normal θ H)).continuous continuous_const
  obtain ⟨u,b,hu,he⟩ := exists_physical_forced_transport θ hθ hne k r hr hk hl H K hC hH
  let c : Amplitude Smooth := (p+u,b)
  have hc : RecursOn hU θ (k-r*r) (r*r) a c := by
    refine ⟨?_,?_,?_⟩
    · funext i
      simp only [localAmp,Pi.neg_apply]
      rw [← restrict_leadingR hU,← restrict_R hU,← map_neg]
      apply (restrictSmooth_eq_iff U _ _).mpr
      intro x hx
      have hh := (he x (subset_closure hx)).1 i
      have hadd := congrArg (fun v : Fin 3 → Smooth => (v i : X → ℂ) x)
        (leadingR_add coord θ (k-r*r) (r*r) p u 0 b)
      simp only [zero_add] at hadd
      change ((leadingR coord θ (k-r*r) (r*r) (p+u) b i : Smooth) : X → ℂ) x=
        -((R coord (k-r*r) (r*r) a.1 a.2 i : Smooth) : X → ℂ) x
      change ((leadingR coord θ (k-r*r) (r*r) (p+u) b i : Smooth) : X → ℂ) x=
        ((leadingR coord θ (k-r*r) (r*r) p 0 i : Smooth) : X → ℂ) x+
          ((leadingR coord θ (k-r*r) (r*r) u b i : Smooth) : X → ℂ) x at hadd
      change ((leadingR coord θ (k-r*r) (r*r) u b i : Smooth) : X → ℂ) x=
        -((R coord (k-r*r) (r*r) a.1 a.2 i : Smooth) : X → ℂ) x-
          ((leadingR coord θ (k-r*r) (r*r) p 0 i : Smooth) : X → ℂ) x at hh
      linear_combination hadd+hh
    · simp only [localAmp]
      rw [← restrict_leadingS hU,← restrict_S hU,← map_neg]
      apply (restrictSmooth_eq_iff U _ _).mpr
      intro x hx
      have hh := (he x (subset_closure hx)).2
      have hadd := congrArg (fun v : Smooth => (v : X → ℂ) x)
        (leadingS_add coord θ (k-r*r) (r*r) p u 0 b)
      simp only [zero_add] at hadd
      change ((leadingS coord θ (k-r*r) (r*r) (p+u) b : Smooth) : X → ℂ) x=
        -((S coord (k-r*r) (r*r) a.1 a.2 : Smooth) : X → ℂ) x
      change ((leadingS coord θ (k-r*r) (r*r) (p+u) b : Smooth) : X → ℂ) x=
        ((leadingS coord θ (k-r*r) (r*r) p 0 : Smooth) : X → ℂ) x+
          ((leadingS coord θ (k-r*r) (r*r) u b : Smooth) : X → ℂ) x at hadd
      change ((leadingS coord θ (k-r*r) (r*r) u b : Smooth) : X → ℂ) x=
        -((S coord (k-r*r) (r*r) a.1 a.2 : Smooth) : X → ℂ) x-
          ((leadingS coord θ (k-r*r) (r*r) p 0 : Smooth) : X → ℂ) x at hh
      linear_combination hadd+hh
    · change normal θ (p+u)=_
      rw [normal_add,hu,add_zero]
      exact normal_particular θ n hn _
  exact ⟨c,hc,recurs_compatible hU θ (k-r*r) (r*r) a c hc⟩
end ElasticityAugmented

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityAugmented.exists_physical_recursion_step_oai := @OAI.ElasticityAugmented.exists_physical_recursion_step_oai
