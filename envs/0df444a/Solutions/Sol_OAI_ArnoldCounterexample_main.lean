-- Prove2me | solution 1 for OAI.ArnoldCounterexample.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:30:01.77087+00:00
-- url     : https://prove2.me/submissions/ae69bcc6-d829-4c02-b02d-31d60dc16e00

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Main.lean:L12-L19
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.ArnoldCounterexample.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_ArnoldCounterexample_main) verbatim and is proved by it.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Definitions.Def_OAI_Geometry_Arnold_Exterior
import Definitions.Def_OAI_Geometry_Arnold_Homotopy
import Definitions.Def_OAI_Geometry_Arnold_Volume
import Definitions.Def_OAI_Geometry_Arnold_Obstruction
import Definitions.Def_OAI_Geometry_Arnold_ThreePoints
import Definitions.Def_OAI_Geometry_Arnold_Factors
import Definitions.Def_OAI_Geometry_Arnold_Field
import Definitions.Def_OAI_Geometry_Arnold_CompactField
import Definitions.Def_OAI_Geometry_Arnold_Midpoint
import Definitions.Def_OAI_Geometry_Arnold_MidpointGeometry
import Definitions.Def_OAI_Geometry_Arnold_Parameter
import Definitions.Def_OAI_Geometry_Arnold_Quotient
import Definitions.Def_OAI_Geometry_Arnold_Hamiltonian
import Definitions.Def_OAI_Geometry_Arnold_CriticalLifts
import Definitions.Def_OAI_Geometry_Arnold_Kernel
import Definitions.Def_OAI_Geometry_Arnold_Degeneracy
import Theorems.Thm_OAI_ArnoldCounterexample_Construction_core_otherVector
import Theorems.Thm_OAI_ArnoldCounterexample_Construction_fixed_factor_critical
import Theorems.Thm_OAI_ArnoldCounterexample_Construction_fixed_zero_coordinate
import Theorems.Thm_OAI_ArnoldCounterexample_Construction_vertical_core_fixed
import Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_cover_map
import Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_no_unit_equivariant_map
import Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_normalize_cover_map
import Theorems.Thm_OAI_ArnoldCounterexample_ThreePoints_multiplierCritical_iff

-- ---- from OAI.Geometry.Arnold.Obstruction ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms ContinuousAlternatingMap

attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM_4
end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms ContinuousAlternatingMap

attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM_5
end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample
open CriticalBound

/-- The lower bound for every smooth function, including all
possible degenerate critical points. No Morse assumption is made. -/
theorem four_le_criticalSet (h : SmoothFunction) : 4 ≤ (criticalSet h).encard := by
  by_contra hn
  have hs : (criticalSet h).encard ≤ 3 := by
    exact Order.le_of_lt_add_one (lt_of_not_ge hn)
  obtain ⟨F₀, hF₀, hne, hphase₀⟩ := cover_map h hs
  obtain ⟨F, hF, hunit, hphase⟩ := normalize_cover_map hF₀ hne hphase₀
  exact no_unit_equivariant_map F hF hunit hphase

/-- The critical-number half of the exact main theorem. -/
theorem four_le_criticalNumber : 4 ≤ criticalNumber :=
  le_iInf four_le_criticalSet

end ArnoldCounterexample

end

end OAI

-- ---- from OAI.Geometry.Arnold.ThreePoints ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff

open scoped BigOperators ContDiff

namespace ArnoldCounterexample
namespace ThreePoints

lemma qzero_ne_qplus : qzero ≠ qplus := by
  intro h
  have := congrArg (fun q : Pair => q.2 0) h
  norm_num [qzero, pole, east, qplus] at this

lemma qzero_ne_qminus : qzero ≠ qminus := by
  intro h
  have := congrArg (fun q : Pair => q.2 0) h
  norm_num [qzero, pole, east, qminus] at this

lemma qplus_ne_qminus : qplus ≠ qminus := by
  intro h
  have he := congrArg (fun q : Pair => q.1 0) h
  have hp : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  norm_num [qplus, qminus] at he
  linarith

open scoped Matrix

end ThreePoints
end ArnoldCounterexample

end

end OAI

-- ---- from OAI.Geometry.Arnold.Factors ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Factors
open ArnoldCounterexample.Quadric ArnoldCounterexample.ThreePoints

lemma moment_skew (a b : Fin 5) (z : CV) : moment a b z = -moment b a z := by
  rw [moment_real, moment_real]
  ring

lemma sphere_norm_identity (z : CV) :
    sqNorm (leftSphere z) + (fourPolynomial z).re ^ 2 + (fourPolynomial z).im ^ 2 = fourNorm z ^ 2 ∧
    sqNorm (rightSphere z) + (fourPolynomial z).re ^ 2 + (fourPolynomial z).im ^ 2 = fourNorm z ^ 2 := by
  change (((moment 1 2 z + moment 3 4 z)^2 + (moment 1 3 z - moment 2 4 z)^2 +
    (moment 1 4 z + moment 2 3 z)^2) + _ + _ = _) ∧
    (((moment 1 2 z - moment 3 4 z)^2 + (moment 1 3 z + moment 2 4 z)^2 +
    (moment 1 4 z - moment 2 3 z)^2) + _ + _ = _)
  norm_num [ moment_real, fourPolynomial, fourNorm,
    Fin.sum_univ_succ, Fin.succ, Fin.reduceFinMk, pow_two, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  constructor <;> ring!

lemma sphereFactors_mem (z : UnitQuadric) (hz : (z : CV) 0 = 0) :
    sphereFactors z ∈ sphereProduct := by
  have hn : fourNorm z = 1 := by
    have h := z.property.1
    simpa only [normSquared, Fin.sum_univ_succ, hz, Complex.normSq_zero, zero_add, fourNorm] using h
  have hp : fourPolynomial z = 0 := by
    have h := z.property.2
    simpa only [quadricPolynomial, Fin.sum_univ_succ, hz, zero_pow (by decide : 2 ≠ 0), zero_add,
      fourPolynomial] using h
  have h := sphere_norm_identity z
  simpa only [sphereFactors, sphereProduct, Set.mem_ofPred_eq, hp, Complex.zero_re,
    Complex.zero_im, zero_pow (by decide : 2 ≠ 0), add_zero, hn, one_pow] using h

lemma planeMatrix_of_sphereFactors (z w : CV) (hz : z 0 = 0) (hw : w 0 = 0)
    (h : sphereFactors z = sphereFactors w) : planeMatrix z = planeMatrix w := by
  have hl := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  have hl0 := congrFun hl 0
  have hl1 := congrFun hl 1
  have hl2 := congrFun hl 2
  have hr0 := congrFun hr 0
  have hr1 := congrFun hr 1
  have hr2 := congrFun hr 2
  simp [sphereFactors, leftSphere, rightSphere] at hl0 hl1 hl2 hr0 hr1 hr2
  have h12 : moment 1 2 z = moment 1 2 w := by linarith
  have h34 : moment 3 4 z = moment 3 4 w := by linarith
  have h13 : moment 1 3 z = moment 1 3 w := by linarith
  have h24 : moment 2 4 z = moment 2 4 w := by linarith
  have h14 : moment 1 4 z = moment 1 4 w := by linarith
  have h23 : moment 2 3 z = moment 2 3 w := by linarith
  have hzero (i : Fin 5) (v : CV) : moment i i v = 0 := by rw [moment_real]; ring
  have h0z (i : Fin 5) : moment 0 i z = 0 := by simp [moment, hz]
  have h0w (i : Fin 5) : moment 0 i w = 0 := by simp [moment, hw]
  ext i j
  change moment i j z = moment i j w
  have h0zr (i : Fin 5) : moment i 0 z = 0 := by rw [moment_skew, h0z, neg_zero]
  have h0wr (i : Fin 5) : moment i 0 w = 0 := by rw [moment_skew, h0w, neg_zero]
  fin_cases i <;> fin_cases j <;>
    first | exact h12 | exact h34 | exact h13 | exact h24 | exact h14 | exact h23 |
      (change moment 0 _ z = moment 0 _ w; rw [h0z, h0w]) |
      (change moment _ 0 z = moment _ 0 w; rw [h0zr, h0wr]) |
      solve | simp only [hzero] |
      (rw [moment_skew _ _ z, moment_skew _ _ w]; congr 1)

end ArnoldCounterexample.Factors

namespace ArnoldCounterexample.Factors
open ArnoldCounterexample.Quadric

lemma hermitian_self (z : UnitQuadric) : hermitian z z = 1 := by
  have he : hermitian z z = (normSquared z : ℂ) := by
    simp only [hermitian, normSquared, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (Complex.normSq_eq_conj_mul_self).symm
  rw [he, z.property.1, Complex.ofReal_one]

lemma complexDot_self (z : UnitQuadric) : complexDot z z = 0 := by
  simpa only [complexDot, quadricPolynomial, pow_two] using z.property.2

lemma moment_complex (a b : Fin 5) (z : CV) :
    (moment a b z : ℂ) = Complex.I * (z a * star (z b) - star (z a) * z b) := by
  apply Complex.ext <;> simp [moment_real, Complex.mul_re, Complex.mul_im]
  ring

lemma matrix_apply (z w : CV) (a : Fin 5) :
    (∑ b, (moment a b z : ℂ) * w b) =
      Complex.I * (z a * hermitian z w - star (z a) * complexDot z w) := by
  simp only [hermitian, complexDot, Finset.mul_sum, moment_complex]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma planeMatrix_project_injective (z w : UnitQuadric) (h : planeMatrix z = planeMatrix w) :
    project z = project w := by
  have hw (a : Fin 5) : (w : CV) a = (z : CV) a * hermitian z w - star ((z : CV) a) * complexDot z w := by
    have hm : (∑ b, (moment a b z : ℂ) * (w : CV) b) = ∑ b, (moment a b w : ℂ) * (w : CV) b := by
      apply Finset.sum_congr rfl
      intro b _
      have hab := congrFun (congrFun h a) b
      change moment a b z = moment a b w at hab
      rw [hab]
    rw [matrix_apply, matrix_apply, hermitian_self, complexDot_self, mul_one, mul_zero, sub_zero] at hm
    exact (mul_left_cancel₀ Complex.I_ne_zero hm).symm
  have hb : complexDot z w = 0 := by
    have he : complexDot z w = complexDot z z * hermitian z w - hermitian z z * complexDot z w := by
      simp only [complexDot, hermitian, Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [hw a]
      dsimp [complexDot, hermitian]
      ring
    rw [complexDot_self, hermitian_self, zero_mul, one_mul, zero_sub] at he
    have he' := congrArg (fun c : ℂ ↦ c + complexDot z w) he
    simp only [neg_add_cancel] at he'
    exact (add_self_eq_zero.mp he')
  have he : (w : CV) = hermitian z w • (z : CV) := by
    ext a
    rw [hw a, hb, mul_zero, sub_zero]
    simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
  apply Subtype.ext
  change Projectivization.mk ℂ (z : CV) _ = Projectivization.mk ℂ (w : CV) _
  symm
  rw [Projectivization.mk_eq_mk_iff']
  exact ⟨hermitian z w, he.symm⟩

lemma sphereFactors_project_injective (z w : UnitQuadric)
    (hz : (z : CV) 0 = 0) (hw : (w : CV) 0 = 0) (h : sphereFactors z = sphereFactors w) :
    project z = project w :=
  planeMatrix_project_injective z w (planeMatrix_of_sphereFactors z w hz hw h)

end ArnoldCounterexample.Factors

end

end OAI

-- ---- from OAI.Geometry.Arnold.Field ----
namespace OAI

universe uι

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Field
open ArnoldCounterexample.Quadric ArnoldCounterexample.ThreePoints ArnoldCounterexample.Factors
open scoped ContDiff Topology
open Set Filter

end ArnoldCounterexample.Field

namespace ArnoldCounterexample.Field
open ArnoldCounterexample.Quadric ArnoldCounterexample.ThreePoints ArnoldCounterexample.Factors
open scoped ContDiff Topology
open Set Filter

lemma radial_eq (s : ℝ) (hs : s ∈ Icc (1/32 : ℝ) 32) : radial s = (Real.sqrt s)⁻¹ :=
  exists_radial.choose_spec.2 s hs

lemma radial_eventually {s : ℝ} (hs : s ∈ Ioo (1/32 : ℝ) 32) :
    radial =ᶠ[𝓝 s] fun x ↦ (Real.sqrt x)⁻¹ := by
  filter_upwards [isOpen_Ioo.mem_nhds hs] with x hx
  exact radial_eq x ⟨le_of_lt hx.1, le_of_lt hx.2⟩

lemma radial_squared (r : ℝ) (hr : r ∈ Ioo (1/2 : ℝ) 2) :
    radial (r^2) = r⁻¹ ∧ deriv radial (r^2) = -(2*r^3)⁻¹ := by
  have hr0 : 0 < r := lt_trans (by norm_num) hr.1
  have hs : r^2 ∈ Ioo (1/32 : ℝ) 32 := by constructor <;> nlinarith [hr.1, hr.2, sq_nonneg (r-2), sq_nonneg (r-1/2)]
  have hsqrt : Real.sqrt (r^2) = r := Real.sqrt_sq hr0.le
  have he : radial (r^2) = r⁻¹ := by rw [radial_eq _ ⟨hs.1.le,hs.2.le⟩, hsqrt]
  refine ⟨he, ?_⟩
  have hd := (((hasDerivAt_id (r^2)).sqrt (sq_pos_of_pos hr0).ne').inv ((Real.sqrt_pos.2 (sq_pos_of_pos hr0)).ne'))
  have hb := hd.congr_of_eventuallyEq (radial_eventually hs)
  rw [hb.deriv]
  simp only [id_eq, hsqrt]
  field_simp

lemma radial_at_one : radial 1 = 1 ∧ deriv radial 1 = -(1/2 : ℝ) := by
  simpa using radial_squared 1 (by norm_num)

end ArnoldCounterexample.Field

end

end OAI

-- ---- from OAI.Geometry.Arnold.FieldAlgebra ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Field
open ArnoldCounterexample.Quadric ArnoldCounterexample.ThreePoints ArnoldCounterexample.Factors
open scoped ContDiff Topology Matrix
open Set Filter

lemma casimir_unit (z : UnitQuadric) (hz : (z:CV) 0 = 0) : casimir z = 1 := by
  have h := (sphereFactors_mem z hz).1
  simpa [casimir, sphereFactors, sqNorm, Fin.sum_univ_succ, add_assoc] using h

lemma core_unit (z : UnitQuadric) (hz : (z:CV) 0 = 0) :
    core z = leftOperator 0 z - rightOperator 2 z + mixedField z - pairing z • selfField z := by
  simp only [core, casimir_unit z hz, radial_at_one.1, radial_at_one.2, one_smul]
  module

end ArnoldCounterexample.Field

end

end OAI

-- ---- from OAI.Geometry.Arnold.Hamiltonian ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Quadric
open ArnoldCounterexample.Field
open scoped ContDiff Topology

lemma pathLinear_apply (t : ℝ) (z : CV) : pathLinear t z = rotationPath (t,z) := rfl

end ArnoldCounterexample.Quadric

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field
open scoped ContDiff Topology

lemma main_isHamiltonian : IsHamiltonian mainEquiv := ⟨mainHamiltonianPath⟩

end ArnoldCounterexample.Construction

end

end OAI

-- ---- from OAI.Geometry.Arnold.CriticalLifts ----
namespace OAI

universe uα

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field ArnoldCounterexample.Factors
open ArnoldCounterexample.ThreePoints
open scoped ContDiff Topology Matrix
open Set Filter

lemma vec_five_two {α : Type uα} (a b c d e : α) : (![a,b,c,d,e] : Fin 5 → α) 2 = c := rfl
lemma vec_five_three {α : Type uα} (a b c d e : α) : (![a,b,c,d,e] : Fin 5 → α) 3 = d := rfl
lemma vec_five_four {α : Type uα} (a b c d e : α) : (![a,b,c,d,e] : Fin 5 → α) 4 = e := rfl

lemma zeroVector_factors : sphereFactors zeroVector = qzero := by
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    norm_num [vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two, Fin.ext_iff, sphereFactors, leftSphere, rightSphere, moment_real, zeroVector, qzero, pole, east]

lemma otherVector_factors (r : ℝ) (_hr : r^2 = 3) :
    sphereFactors (otherVector r) = (![r/2,0,-1/2], ![1/2,0,-r/2]) := by
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    norm_num [vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two, Fin.ext_iff, sphereFactors, leftSphere, rightSphere, moment_real, otherVector] <;> nlinarith

lemma plusLift_factors : sphereFactors plusLift = qplus :=
  otherVector_factors _ (Real.sq_sqrt (by norm_num))
lemma minusLift_factors : sphereFactors minusLift = qminus := by
  simpa [minusLift, qminus] using otherVector_factors (-Real.sqrt 3) (by rw [neg_sq]; exact Real.sq_sqrt (by norm_num))

lemma core_zeroVector : core zeroVector = 0 := by
  have he := core_unit zeroLift (by rfl)
  change core zeroVector = _ at he
  rw [he]
  have hL : leftSphere zeroVector = pole := congrArg Prod.fst zeroVector_factors
  have hR : rightSphere zeroVector = -east := congrArg Prod.snd zeroVector_factors
  change leftOperator 0 zeroVector - rightOperator 2 zeroVector + mixedField zeroVector - pairing zeroVector • selfField zeroVector = _
  simp only [mixedField, pairing, selfField, hL, hR]
  ext i
  fin_cases i <;> norm_num [vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two, Fin.ext_iff, pole, east,
    leftOperator, rightOperator, rotor_apply, zeroVector, Fin.sum_univ_succ, Pi.single_apply]

end ArnoldCounterexample.Construction

end

end OAI

-- ---- from OAI.Geometry.Arnold.FixedCount ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field ArnoldCounterexample.Factors
open ArnoldCounterexample.ThreePoints
open scoped ContDiff Topology Matrix
open Set Filter

lemma zeroLift_fixed : mainEquiv (project zeroLift) = project zeroLift := by
  apply vertical_core_fixed zeroLift (by rfl) 0 (by norm_num)
  simp only [zero_smul]
  change core zeroVector = 0
  exact core_zeroVector

lemma otherLift_fixed (r : ℝ) (hr : r^2 = 3) :
    mainEquiv (project ⟨otherVector r,otherVector_unit r hr⟩) =
      project ⟨otherVector r,otherVector_unit r hr⟩ := by
  apply vertical_core_fixed _ (by rfl) (-(3*r/2))
  · have hb : |r| ≤ 2 := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    rw [abs_neg, abs_div, abs_mul]
    norm_num
    linarith
  · exact core_otherVector r hr

lemma plusLift_fixed : mainEquiv (project plusLift) = project plusLift :=
  otherLift_fixed _ (Real.sq_sqrt (by norm_num))
lemma minusLift_fixed : mainEquiv (project minusLift) = project minusLift :=
  otherLift_fixed _ (by rw [neg_sq]; exact Real.sq_sqrt (by norm_num))

lemma factors_respects (z w : UnitQuadric) (h : project z = project w) :
    sphereFactors z = sphereFactors w := by
  obtain ⟨c,hc,he⟩ := (project_eq_iff_phase z w).mp h
  rw [← he]
  simp only [sphereFactors, left_scale, right_scale, hc, one_smul]

lemma zeroLift_ne_plusLift : project zeroLift ≠ project plusLift := by
  intro h
  have he := factors_respects _ _ h
  rw [plusLift_factors, show sphereFactors zeroLift = qzero from zeroVector_factors] at he
  exact qzero_ne_qplus he
lemma zeroLift_ne_minusLift : project zeroLift ≠ project minusLift := by
  intro h
  have he := factors_respects _ _ h
  rw [minusLift_factors, show sphereFactors zeroLift = qzero from zeroVector_factors] at he
  exact qzero_ne_qminus he
lemma plusLift_ne_minusLift : project plusLift ≠ project minusLift := by
  intro h
  have he := factors_respects _ _ h
  rw [plusLift_factors, minusLift_factors] at he
  exact qplus_ne_qminus he

lemma main_fixed_iff (q : Q3) : mainEquiv q = q ↔
    q = project zeroLift ∨ q = project plusLift ∨ q = project minusLift := by
  constructor
  · obtain ⟨z,rfl⟩ := project_surjective q
    intro hz
    have hz0 := fixed_zero_coordinate z hz
    have hc := multiplierCritical_iff (sphereFactors z) |>.mp (fixed_factor_critical z hz)
    rcases hc with hc | hc | hc
    · exact Or.inl (sphereFactors_project_injective z zeroLift hz0 (by rfl) (hc.trans zeroVector_factors.symm))
    · exact Or.inr (Or.inl (sphereFactors_project_injective z plusLift hz0 (by rfl) (hc.trans plusLift_factors.symm)))
    · exact Or.inr (Or.inr (sphereFactors_project_injective z minusLift hz0 (by rfl) (hc.trans minusLift_factors.symm)))
  · rintro (rfl | rfl | rfl)
    · exact zeroLift_fixed
    · exact plusLift_fixed
    · exact minusLift_fixed

lemma main_fixed_set : fixedSet mainEquiv = {project zeroLift, project plusLift, project minusLift} := by
  ext q
  simp only [fixedSet, mem_ofPred_eq, main_fixed_iff, mem_insert_iff, mem_singleton_iff]

lemma main_fixed_encard : (fixedSet mainEquiv).encard = 3 := by
  rw [main_fixed_set, Set.encard_insert_of_notMem]
  · rw [Set.encard_pair plusLift_ne_minusLift]
    norm_num
  · simp [zeroLift_ne_plusLift, zeroLift_ne_minusLift]

end ArnoldCounterexample.Construction

end

end OAI

-- ---- from OAI.Geometry.Arnold.MidpointDerivative ----
namespace OAI

universe uE

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Midpoint
open scoped ContDiff Topology NNReal
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma resolvent_equilibrium (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖*C < 1) (t : ℝ) (z : E) (hz : X z = 0) :
    resolvent X hX τ hτ (t,z) = z := by
  symm
  apply resolvent_unique
  simp [hz]

lemma step_equilibrium (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖*C < 1) (t : ℝ) (z : E) (hz : X z = 0) :
    step X hX τ hτ (t,z) = z := by
  rw [step_center, resolvent_equilibrium _ hX τ hτ t z hz, hz, smul_zero, add_zero]

lemma resolvent_right_inverse (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖*C < 1) (t : ℝ) (z : E) :
    resolvent X hX τ hτ (t, z - τ t • X z) = z := by
  symm
  apply resolvent_unique
  simp

lemma resolvent_kernel (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (hXs : ContDiff ℝ ∞ X) (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖*C < 1)
    (hτs : ContDiff ℝ ∞ τ) (t : ℝ) (z v : E) (hz : X z = 0)
    (hv : fderiv ℝ X z v = 0) :
    fderiv ℝ (fun w ↦ resolvent X hX τ hτ (t,w)) z v = v := by
  let R : E → E := fun w ↦ resolvent X hX τ hτ (t,w)
  have hR : ContDiff ℝ ∞ R := (resolvent_smooth _ hX hXs _ hτ hτs).comp (contDiff_const.prodMk contDiff_id)
  have hU := (hasFDerivAt_id (𝕜 := ℝ) z).sub ((hXs.differentiable (by simp) z).hasFDerivAt.const_smul (τ t))
  have he : (fun w ↦ R (w - τ t • X w)) = id := funext (resolvent_right_inverse _ hX τ hτ t)
  have hUZ : z - τ t • X z = z := by simp [hz]
  have hd := (hR.differentiable (by simp) (z - τ t • X z)).hasFDerivAt.comp z hU
  change HasFDerivAt (fun w ↦ R (w - τ t • X w)) _ z at hd
  rw [he,hUZ] at hd
  have h := congrArg (fun L : E →L[ℝ] E ↦ L v) (hd.unique (hasFDerivAt_id z))
  simpa only [ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply, smul_apply, hv, smul_zero, sub_zero] using h

lemma step_kernel (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (hXs : ContDiff ℝ ∞ X) (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖*C < 1)
    (hτs : ContDiff ℝ ∞ τ) (t : ℝ) (z v : E) (hz : X z = 0)
    (hv : fderiv ℝ X z v = 0) :
    fderiv ℝ (fun w ↦ step X hX τ hτ (t,w)) z v = v := by
  have hR : ContDiff ℝ ∞ (fun w ↦ resolvent X hX τ hτ (t,w)) :=
    (resolvent_smooth _ hX hXs _ hτ hτs).comp (contDiff_const.prodMk contDiff_id)
  have hd := ((hR.differentiable (by simp) z).hasFDerivAt.const_smul (2:ℝ)).sub (hasFDerivAt_id z)
  change HasFDerivAt (fun w ↦ step X hX τ hτ (t,w)) _ z at hd
  rw [hd.fderiv]
  change (2:ℝ) • fderiv ℝ (fun w ↦ resolvent X hX τ hτ (t,w)) z v - v = v
  rw [resolvent_kernel _ hX hXs τ hτ hτs t z v hz hv]
  module

end ArnoldCounterexample.Midpoint

end

end OAI

-- ---- from OAI.Geometry.Arnold.Kernel ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field ArnoldCounterexample.Factors
open ArnoldCounterexample.ThreePoints
open scoped ContDiff Topology Matrix
open Set Filter

lemma kernelVector_ne_zero : kernelVector ≠ 0 := by
  intro h
  have := congrFun h 1
  norm_num [kernelVector] at this

lemma kernelVector_horizontal : Horizontal zeroVector kernelVector := by
  constructor <;> apply Complex.ext <;>
    norm_num [Horizontal, zeroVector, kernelVector, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im, map_ofNat, vec_five_two, vec_five_three, vec_five_four]

lemma zero_left : leftSphere zeroVector = pole := congrArg Prod.fst zeroVector_factors
lemma zero_right : rightSphere zeroVector = -east := congrArg Prod.snd zeroVector_factors
lemma zero_casimir : casimir zeroVector = 1 := casimir_unit zeroLift (by rfl)
lemma zero_pairing : pairing zeroVector = 0 := by
  simp only [pairing, zero_left, zero_right]
  norm_num [pole,east,Fin.sum_univ_succ]

lemma zero_leftOperator (i : Fin 3) : leftOperator i zeroVector =
    (![![0,Complex.I/2,1/2,-Complex.I/2,1/2],
      ![0,-1/2,Complex.I/2,1/2,Complex.I/2],
      ![0,-Complex.I/2,-1/2,-Complex.I/2,1/2]] : Fin 3 → CV) i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [leftOperator, rotor_apply, Pi.single_apply, zeroVector,
      vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two, Fin.ext_iff] <;> ring

lemma zero_rightOperator (i : Fin 3) : rightOperator i zeroVector =
    (![![0,Complex.I/2,1/2,Complex.I/2,-1/2],
      ![0,-1/2,-Complex.I/2,1/2,-Complex.I/2],
      ![0,-Complex.I/2,1/2,Complex.I/2,1/2]] : Fin 3 → CV) i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [rightOperator, rotor_apply, Pi.single_apply, zeroVector,
      vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two, Fin.ext_iff] <;> ring

lemma left_kernel (i : Fin 3) : symplectic (leftOperator i zeroVector) kernelVector = east i := by
  rw [zero_leftOperator, symplectic_apply]
  fin_cases i <;> norm_num [omega, kernelVector, Fin.sum_univ_succ, Complex.mul_im, east,
    vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two, map_ofNat]

lemma right_kernel (i : Fin 3) : symplectic (rightOperator i zeroVector) kernelVector = 0 := by
  rw [zero_rightOperator, symplectic_apply]
  fin_cases i <;> norm_num [omega, kernelVector, Fin.sum_univ_succ, Complex.mul_im,
    vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two, map_ofNat]

lemma zero_operator_cancel : rightOperator 0 zeroVector + leftOperator 2 zeroVector = 0 := by
  rw [zero_leftOperator, zero_rightOperator]
  ext i
  fin_cases i <;> norm_num [vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two] <;> ring

lemma kernelCurve_zero : kernelCurve 0 = zeroVector := by simp [kernelCurve]
lemma kernelCurve_derivative : HasDerivAt kernelCurve kernelVector 0 := by
  convert! (hasDerivAt_const (0:ℝ) zeroVector).add ((hasDerivAt_id (0:ℝ)).smul_const kernelVector) using 1
  simp

lemma left_curve (i : Fin 3) : HasDerivAt (fun t ↦ leftSphere (kernelCurve t) i) (east i) 0 := by
  convert! (left_hasFDerivAt i (kernelCurve 0)).comp_hasDerivAt 0 kernelCurve_derivative using 1
  simp only [kernelCurve_zero, left_kernel]
lemma right_curve (i : Fin 3) : HasDerivAt (fun t ↦ rightSphere (kernelCurve t) i) 0 0 := by
  convert! (right_hasFDerivAt i (kernelCurve 0)).comp_hasDerivAt 0 kernelCurve_derivative using 1
  simp only [kernelCurve_zero, right_kernel]

lemma casimir_curve : HasDerivAt (fun t ↦ casimir (kernelCurve t)) 0 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i : Fin 3 ↦ fun _ ↦ (left_curve i).pow 2)
  convert! h using 1
  norm_num [kernelCurve_zero, zero_left, pole, east, Fin.sum_univ_succ]

lemma pairing_curve : HasDerivAt (fun t ↦ pairing (kernelCurve t)) (-1) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i : Fin 3 ↦ fun _ ↦ (left_curve i).mul (right_curve i))
  convert! h using 1
  norm_num [kernelCurve_zero, zero_left, zero_right, pole, east, Fin.sum_univ_succ]

lemma mixed_curve : HasDerivAt (fun t ↦ mixedField (kernelCurve t))
    (-leftOperator 0 kernelVector + rightOperator 2 kernelVector + rightOperator 0 zeroVector) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i : Fin 3 ↦ fun _ ↦
    ((right_curve i).smul ((leftOperator i).hasFDerivAt.comp_hasDerivAt 0 kernelCurve_derivative)).add
    ((left_curve i).smul ((rightOperator i).hasFDerivAt.comp_hasDerivAt 0 kernelCurve_derivative)))
  convert! h using 1
  simp [kernelCurve_zero, zero_left, zero_right, pole, east, Fin.sum_univ_succ]
  module

lemma core_curve : HasDerivAt (fun t ↦ core (kernelCurve t)) 0 0 := by
  have hb : HasDerivAt (fun t ↦ radial (casimir (kernelCurve t))) 0 0 := by
    convert! (radial_smooth.differentiable (by simp) (casimir (kernelCurve 0))).hasDerivAt.comp 0 casimir_curve using 1
    simp only [mul_zero]
  have hds : ContDiff ℝ ∞ (deriv radial) := (contDiff_infty_iff_deriv.mp radial_smooth).2
  have hdb : HasDerivAt (fun t ↦ deriv radial (casimir (kernelCurve t))) 0 0 := by
    convert! (hds.differentiable (by simp) (casimir (kernelCurve 0))).hasDerivAt.comp 0 casimir_curve using 1
    simp only [mul_zero]
  have hc : HasDerivAt (fun t ↦ 2 * deriv radial (casimir (kernelCurve t)) * pairing (kernelCurve t)) 1 0 := by
    convert! (hdb.const_mul 2).mul pairing_curve using 1
    simp [kernelCurve_zero, zero_casimir, zero_pairing, radial_at_one.2]
  have hs : HasDerivAt (fun t ↦ selfField (kernelCurve t))
      (fderiv ℝ selfField zeroVector kernelVector) 0 := by
    convert! (self_smooth.differentiable (by simp) (kernelCurve 0)).hasFDerivAt.comp_hasDerivAt 0 kernelCurve_derivative using 1
    simp only [kernelCurve_zero]
  have h := (((leftOperator 0).hasFDerivAt.comp_hasDerivAt 0 kernelCurve_derivative).sub
    ((rightOperator 2).hasFDerivAt.comp_hasDerivAt 0 kernelCurve_derivative)).add (hb.smul mixed_curve) |>.add (hc.smul hs)
  convert! h using 1
  simp [kernelCurve_zero, zero_casimir, zero_pairing, radial_at_one.1, selfField,
    zero_left, pole, Fin.sum_univ_succ]
  calc
    _ = rightOperator 0 zeroVector + leftOperator 2 zeroVector := zero_operator_cancel.symm
    _ = _ := by module

lemma core_kernel : fderiv ℝ core zeroVector kernelVector = 0 := by
  have h := (core_smooth.differentiable (by simp) (kernelCurve 0)).hasFDerivAt.comp_hasDerivAt 0 kernelCurve_derivative
  simpa only [kernelCurve_zero] using h.unique core_curve

lemma vectorField_zeroVector : vectorField zeroVector = 0 := by
  rw [vectorField, core_zeroVector, smul_zero]

lemma vectorField_kernel : fderiv ℝ vectorField zeroVector kernelVector = 0 := by
  have h := vectorField_local_core (by rw [zeroVector_unit.1]; norm_num : normSquared zeroVector < 4)
  rw [h.fderiv_eq]
  exact core_kernel

end ArnoldCounterexample.Construction

end

end OAI

-- ---- from OAI.Geometry.Arnold.Degeneracy ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field
open scoped ContDiff Topology

lemma rotation_finish_neg (z : CV) (hz : z 0 = 0) : rotationPath (1,z) = -z := by
  rw [rotationPath_finish]
  ext j
  by_cases hj : j = 0
  · subst j
    simp [hz]
  · simp [hj]

lemma forwardMid_zeroVector (t : ℝ) : forwardMid (t,zeroVector) = zeroVector :=
  Midpoint.step_equilibrium _ lipschitz parameter parameter_contract t zeroVector vectorField_zeroVector

lemma forwardMid_kernel (t : ℝ) :
    fderiv ℝ (fun w ↦ forwardMid (t,w)) zeroVector kernelVector = kernelVector :=
  Midpoint.step_kernel _ lipschitz vectorField_smooth parameter parameter_contract parameter_smooth
    t zeroVector kernelVector vectorField_zeroVector vectorField_kernel

lemma degenerateLift_smooth : ContDiff ℝ ∞ degenerateLift :=
  (forward_smooth.comp (contDiff_const.prodMk contDiff_id)).neg

lemma degenerateLift_zeroVector : degenerateLift zeroVector = zeroVector := by
  rw [degenerateLift, forward, forwardMid_zeroVector, rotation_finish_neg zeroVector (by rfl), neg_neg]

lemma degenerateLift_project (z : UnitQuadric) :
    project ⟨degenerateLift z,degenerateLift_preserves z⟩ = mainEquiv (project z) := by
  rw [mainEquiv_project]
  apply (project_eq_iff_phase _ _).mpr
  exact ⟨-1, by norm_num, by simp [degenerateLift]⟩

lemma degenerateLift_kernel :
    fderiv ℝ degenerateLift zeroVector kernelVector = kernelVector := by
  have hM : ContDiff ℝ ∞ (fun w ↦ forwardMid (1,w)) :=
    forwardMid_smooth.comp (contDiff_const.prodMk contDiff_id)
  have hD := ((pathLinear 1).hasFDerivAt.comp zeroVector
    ((hM.differentiable (by simp) zeroVector).hasFDerivAt)).neg
  change HasFDerivAt degenerateLift _ zeroVector at hD
  rw [hD.fderiv]
  change -(pathLinear 1 (fderiv ℝ (fun w ↦ forwardMid (1,w)) zeroVector kernelVector)) = kernelVector
  rw [forwardMid_kernel, pathLinear_apply, rotation_finish_neg kernelVector (by rfl), neg_neg]

lemma main_degenerate : HasDegenerateFixedPoint mainEquiv := by
  refine ⟨zeroLift,kernelVector,zeroLift_fixed,kernelVector_ne_zero,kernelVector_horizontal,
    Set.univ,degenerateLift,isOpen_univ,Set.mem_univ _,degenerateLift_smooth.contDiffOn,
    degenerateLift_zeroVector,?_,0,?_⟩
  · intro y _
    exact ⟨degenerateLift_preserves y,degenerateLift_project y⟩
  · change fderiv ℝ degenerateLift zeroVector kernelVector - kernelVector = (0:ℝ) • _
    rw [degenerateLift_kernel, sub_self, zero_smul]

end ArnoldCounterexample.Construction

end

end OAI

-- ---- from OAI.Geometry.Arnold.Main ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample

/-- The Hamiltonian counterexample, with the complete fixed set, the lower bound
for all smooth functions, and a genuine nonzero quotient-tangent eigenvector. -/
theorem main :
    ∃ φ : Q3 ≃ Q3, IsHamiltonian φ ∧ (fixedSet φ).encard = 3 ∧
      (3 : ℕ∞) < 4 ∧ 4 ≤ criticalNumber ∧ HasDegenerateFixedPoint φ := by
  exact ⟨Construction.mainEquiv, Construction.main_isHamiltonian,
    Construction.main_fixed_encard, by norm_num, four_le_criticalNumber,
    Construction.main_degenerate⟩

end ArnoldCounterexample

end

end OAI

-- ---- mission target ----
open OAI OAI.ArnoldCounterexample
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace OAI
namespace ArnoldCounterexample
theorem _root_.solution :
    ∃ φ : Q3 ≃ Q3, IsHamiltonian φ ∧ (fixedSet φ).encard = 3 ∧
      (3 : ℕ∞) < 4 ∧ 4 ≤ criticalNumber ∧ HasDegenerateFixedPoint φ := by
  first
    | exact OAI.ArnoldCounterexample.main
    | (apply OAI.ArnoldCounterexample.main <;> assumption)
    | (intros; apply OAI.ArnoldCounterexample.main <;> assumption)
end ArnoldCounterexample
end OAI
