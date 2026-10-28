-- Prove2me | solution 1 for OAI.ElasticityAugmented.exists_real_physical_series
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:03:07.422777+00:00
-- url     : https://prove2.me/submissions/affb6ebd-ad10-4d89-9d0e-1129403cf6a6

import Mathlib
import Definitions.Def_OAIQ6El004
import Theorems.Thm_OAI_ElasticityAugmented_exists_physical_leading_frame
import Theorems.Thm_OAI_ElasticityAugmented_exists_physical_recursion_step

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

lemma leading_stage_compatibility (hD : ∀ i j f, D i (D j f)=D j (D i f))
    (θ : Fin 3 → ℂ) (lam m : A) (u : Fin 3 → A) (b : A)
    (hR : leadingR D θ lam m u b=0) (hS : leadingS D θ lam m u b=0)
    (hn : normal θ u=0) :
    normal θ (R D lam m u b)=leadingP D θ m (div D u-b) := by
  have hc := transport_compatibility D θ lam m u b hD
  simpa only [hR,hS,hn,div,P,lap,Pi.zero_apply,map_zero,mul_zero,Finset.sum_const_zero,
    zero_add,add_zero,sub_zero] using hc
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

lemma restrict_normal (U : Set X) (θ : Fin 3 → ℂ) (a : Fin 3 → Smooth) :
    restrictSmooth U (normal θ a)=normal θ (fun i => restrictSmooth U (a i)) := by
  simp only [normal,map_sum,map_smul]
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
-- module Solutions.OAIQ6_Elast.Elasticity_CGO
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set
open scoped BigOperators
namespace ElasticityAugmented

/-- Every compatible smooth amplitude has an actual infinite recursive sequence;
only its finite truncations are used. There is no formal-solvability hypothesis. -/
theorem exists_recursive_series {U : Set X} (hU : IsOpen U) (hC : IsCompact (closure U))
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (k r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0)
    (a₀ : Amplitude Smooth) (ha₀ : CompatibleOn hU θ (k-r*r) (r*r) a₀) :
    ∃ a : ℕ → Amplitude Smooth, a 0=a₀ ∧
      (∀ j,RecursOn hU θ (k-r*r) (r*r) (a j) (a (j+1))) ∧
      ∀ j,CompatibleOn hU θ (k-r*r) (r*r) (a j) := by
  let E := {a : Amplitude Smooth // CompatibleOn hU θ (k-r*r) (r*r) a}
  have hex (a : E) := exists_physical_recursion_step hU hC θ hθ hne k r hr hk hl a.val a.property
  let step : E → E := fun a => ⟨Classical.choose (hex a),(Classical.choose_spec (hex a)).2⟩
  have hstep (a : E) : RecursOn hU θ (k-r*r) (r*r) a.val (step a).val :=
    (Classical.choose_spec (hex a)).1
  let seq : ℕ → E := Nat.rec ⟨a₀,ha₀⟩ (fun _ a => step a)
  refine ⟨fun j => (seq j).val,rfl,?_,fun j => (seq j).property⟩
  intro j
  exact hstep (seq j)

/-- The given genuine leading frame develops to physical compatible amplitudes,
with all three recursive equations on the same open region. -/
theorem exists_physical_formal_frame {U : Set X} (hU : IsOpen U) (hC : IsCompact (closure U))
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (k r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) :
    ∃ a : Fin 3 → ℕ → Amplitude Smooth,
    ∃ B : X → Module.Basis (Fin 3) ℂ (ElasticityFrame.Fiber θ),
      (∀ ν,normal θ (a ν 0).1=0) ∧
      (∀ ν,leadingR (localCoord hU) θ (restrictSmooth U (k-r*r)) (restrictSmooth U (r*r))
          (localAmp U (a ν 0)).1 (localAmp U (a ν 0)).2=0 ∧
        leadingS (localCoord hU) θ (restrictSmooth U (k-r*r)) (restrictSmooth U (r*r))
          (localAmp U (a ν 0)).1 (localAmp U (a ν 0)).2=0) ∧
      (∀ ν j,RecursOn hU θ (k-r*r) (r*r) (a ν j) (a ν (j+1))) ∧
      ∀ ν x, ((B x ν : ElasticityFrame.Fiber θ) : ElasticityFrame.Amp)=
        ((fun i => (changeP r (a ν 0).1 i : X → ℂ) x),
          (changeS k r hr (a ν 0).1 (a ν 0).2 : X → ℂ) x) := by
  obtain ⟨a₀,b₀,B,hn₀,he₀,hB⟩ := exists_physical_leading_frame θ hθ hne k r hr hk hl hC
  have hR₀ (ν) : leadingR (localCoord hU) θ (restrictSmooth U (k-r*r)) (restrictSmooth U (r*r))
      (localAmp U (a₀ ν,b₀ ν)).1 (localAmp U (a₀ ν,b₀ ν)).2=0 := by
    funext i
    simp only [localAmp,Pi.zero_apply]
    rw [← restrict_leadingR hU]
    exact (restrictSmooth_zero_iff U _).mpr (fun x hx => (he₀ ν x (subset_closure hx)).1 i)
  have hS₀ (ν) : leadingS (localCoord hU) θ (restrictSmooth U (k-r*r)) (restrictSmooth U (r*r))
      (localAmp U (a₀ ν,b₀ ν)).1 (localAmp U (a₀ ν,b₀ ν)).2=0 := by
    simp only [localAmp]
    rw [← restrict_leadingS hU]
    exact (restrictSmooth_zero_iff U _).mpr (fun x hx => (he₀ ν x (subset_closure hx)).2)
  have hc₀ (ν) : CompatibleOn hU θ (k-r*r) (r*r) (a₀ ν,b₀ ν) := by
    apply leading_stage_compatibility (localCoord hU) (localCoord_commute hU) θ _ _
      (localAmp U (a₀ ν,b₀ ν)).1 (localAmp U (a₀ ν,b₀ ν)).2 (hR₀ ν) (hS₀ ν)
    change normal θ (fun i => restrictSmooth U (a₀ ν i))=0
    rw [← restrict_normal,hn₀ ν,map_zero]
  choose a ha hrec hc using (fun ν => exists_recursive_series hU hC θ hθ hne k r hr hk hl (a₀ ν,b₀ ν) (hc₀ ν))
  refine ⟨a,B,?_,?_,hrec,?_⟩
  · intro ν
    rw [ha ν]
    exact hn₀ ν
  · intro ν
    rw [ha ν]
    exact ⟨hR₀ ν,hS₀ ν⟩
  · intro ν x
    rw [ha ν]
    exact hB ν x
end ElasticityAugmented

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
lemma real_k_positive (lam m : X → ℝ) (hp : ∀ x,0 < m x ∧ 0<3*lam x+2*m x) (x : X) :
    0<lam x+m x := by have hh := hp x; linarith
lemma real_longitudinal_positive (lam m : X → ℝ) (hp : ∀ x,0 < m x ∧ 0<3*lam x+2*m x) (x : X) :
    0<lam x+m x+m x := by have hh := hp x; linarith

/-- Actual real strongly convex Lamé pairs develop to a full independent
physical amplitude frame and all its compatible recursion orders. -/
theorem exists_real_physical_series_oai {U : Set X} (hU : IsOpen U) (hC : IsCompact (closure U))
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (lam m : X → ℝ) (hl : ContDiff ℝ (⊤ : ℕ∞) lam) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hp : ∀ x,0 < m x ∧ 0<3*lam x+2*m x) :
    let l := smoothOfReal lam hl
    let μ := smoothOfReal m hm
    let r := positiveRoot m hm (fun x => (hp x).1)
    let hr := positiveRoot_nonzero m hm (fun x => (hp x).1)
    ∃ a : Fin 3 → ℕ → Amplitude Smooth,
    ∃ B : X → Module.Basis (Fin 3) ℂ (ElasticityFrame.Fiber θ),
      (∀ ν,normal θ (a ν 0).1=0) ∧
      (∀ ν,leadingR (localCoord hU) θ (restrictSmooth U l) (restrictSmooth U μ)
          (localAmp U (a ν 0)).1 (localAmp U (a ν 0)).2=0 ∧
        leadingS (localCoord hU) θ (restrictSmooth U l) (restrictSmooth U μ)
          (localAmp U (a ν 0)).1 (localAmp U (a ν 0)).2=0) ∧
      (∀ ν j,RecursOn hU θ l μ (a ν j) (a ν (j+1))) ∧
      ∀ ν x,((B x ν : ElasticityFrame.Fiber θ) : ElasticityFrame.Amp)=
        ((fun i => (changeP r (a ν 0).1 i : X → ℂ) x),
          (changeS (l+μ) r hr (a ν 0).1 (a ν 0).2 : X → ℂ) x) := by
  intro l μ r hr
  have hr2 : r*r=μ := positiveRoot_square m hm (fun x => (hp x).1)
  have hk : ∀ x,((l+μ : Smooth) : X → ℂ) x≠0 := by
    intro x
    change (lam x : ℂ)+(m x : ℂ)≠0
    exact_mod_cast (real_k_positive lam m hp x).ne'
  have hsum : ∀ x,((l+μ+r*r : Smooth) : X → ℂ) x≠0 := by
    intro x
    rw [hr2]
    change (lam x : ℂ)+(m x : ℂ)+(m x : ℂ)≠0
    exact_mod_cast (real_longitudinal_positive lam m hp x).ne'
  obtain ⟨a,B,hn,he,hrec,hB⟩ := exists_physical_formal_frame hU hC θ hθ hne (l+μ) r hr hk hsum
  refine ⟨a,B,hn,?_,?_,hB⟩
  · simpa only [hr2,add_sub_cancel_right] using he
  · simpa only [hr2,add_sub_cancel_right] using hrec
end ElasticityAugmented

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityAugmented.exists_real_physical_series_oai := @OAI.ElasticityAugmented.exists_real_physical_series_oai
