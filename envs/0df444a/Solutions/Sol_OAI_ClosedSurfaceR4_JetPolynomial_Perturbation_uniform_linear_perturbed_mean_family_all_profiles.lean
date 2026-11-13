-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.uniform_linear_perturbed_mean_family_all_profiles
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:03:46.414137+00:00
-- url     : https://prove2.me/submissions/10fb1b7a-943b-4f09-a4eb-ab60b75489c6

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_OAIQ249SI011

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



lemma WeightedBound.mono_order {U : Set E} {s C : ℝ} {m r : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hr : r ≤ m) : WeightedBound U s r C f :=
  fun j hj => h j (hj.trans hr)

lemma WeightedBound.fderivWithin {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hs : 0 < s) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (C / s) (fderivWithin ℝ f U) := by
  intro j hj x hx
  rw [norm_iteratedFDerivWithin_fderivWithin hU hx]
  apply (le_div_iff₀ hs).2
  have hh := hb (j + 1) (Nat.add_le_add_right hj 1) x hx
  rw [pow_succ] at hh
  nlinarith


lemma WeightedBound.const_smul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ}
    {m : ℕ} {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℝ) :
    WeightedBound U s m (|a| * C) (fun x => a • f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul, Real.norm_eq_abs]
  calc
    _ = |a| * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (abs_nonneg _)

lemma WeightedBound.clm_apply_const {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {f : E → F →L[ℝ] G} (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s m C f) (v : F) :
    WeightedBound U s m (‖v‖ * C) (fun x => f x v) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (‖v‖ * ‖iteratedFDerivWithin ℝ j f U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_clm_apply_const (n := j) (N := ∞)
        (hf.contDiffWithinAt hx) hU hx (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ = ‖v‖ * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (norm_nonneg v)



lemma WeightedBound.comp {U : Set E} {V : Set F} (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V)
    {s C D : ℝ} {m : ℕ} {f : E → F} {g : F → G} (hs : 0 < s) (hC : 1 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g V) (hUV : MapsTo f U V)
    (hbf : WeightedBound U s m C f)
    (hbg : ∀ j ≤ m, ∀ x ∈ U, ‖iteratedFDerivWithin ℝ j g V (f x)‖ ≤ D) :
    WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (g ∘ f) := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  intro j hj x hx
  have hi (i : ℕ) (hi1 : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i f U x‖ ≤ (C / s) ^ i := by
    have hp : C ≤ C ^ i := by
      simpa only [pow_one] using pow_le_pow_right₀ hC hi1
    calc
      _ ≤ C / s ^ i := hbf.deriv_le hs (hij.trans hj) hx
      _ ≤ C ^ i / s ^ i := div_le_div_of_nonneg_right hp (pow_nonneg hs.le _)
      _ = _ := (div_pow C s i).symm
  have hn : (j : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)
  have hh := norm_iteratedFDerivWithin_comp_le hg hf hn hV hU hUV hx
    (fun i hij => hbg i (hij.trans hj) x hx) hi
  calc
    _ ≤ s ^ j * ((j.factorial : ℝ) * D * (C / s) ^ j) :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
    _ = (j.factorial : ℝ) * D * C ^ j := by
      rw [div_pow]
      field_simp
    _ ≤ _ := by
      gcongr




lemma smooth_compact_weighted_bound {U : Set E} {V K : Set F}
    (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V) (hK : IsCompact K) (hKV : K ⊆ V)
    {g : F → G} (hg : ContDiffOn ℝ ∞ g V) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (f : E → F) (s C : ℝ), 0 < s → 1 ≤ C →
      ContDiffOn ℝ ∞ f U → MapsTo f U K → WeightedBound U s m C f →
      WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (g ∘ f) := by
  obtain ⟨D, hD, hbD⟩ := compact_coefficient_bound hV hK hKV hg m
  refine ⟨D, hD, ?_⟩
  intro f s C hs hC hf hfk hbf
  exact hbf.comp hU hV hs hC (le_trans zero_le_one hD) hf hg
    (fun x hx => hKV (hfk hx)) (fun j hj x hx => hbD j hj (f x) (hfk hx))




lemma WeightedBound.congr {U : Set E} {s C : ℝ} {m : ℕ} {f g : E → F}
    (hf : WeightedBound U s m C f) (he : EqOn g f U) : WeightedBound U s m C g := by
  intro j hj x hx
  rw [iteratedFDerivWithin_congr he hx]
  exact hf j hj x hx

lemma WeightedBound.mul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f g : E → ℂ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2 ^ m * C * D) (fun x => f x * g x) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f U x‖ * ‖iteratedFDerivWithin ℝ (j - i) g U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_mul_le (n := j) (N := ∞) hf hg hU hx
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ ≤ 2 ^ j * C * D := weighted_binomial_bound hs hC hD j _ _
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun i hi => hbf i (hi.trans hj) x hx) (fun i hi => hbg i (hi.trans hj) x hx)
    _ ≤ _ := by gcongr; norm_num

lemma WeightedBound.const_mul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℂ) :
    WeightedBound U s m (‖a‖ * C) (fun x => a * f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul]
  calc
    _ = ‖a‖ * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (norm_nonneg a)

lemma WeightedBound.directional {U : Set E} (hU : IsOpen U) {s C : ℝ} {m : ℕ}
    {f : E → F} (hs : 0 < s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s (m + 1) C f) (v : E) :
    WeightedBound U s m (‖v‖ * (C / s)) (fun x => fderiv ℝ f x v) := by
  have hd := hb.fderivWithin hU.uniqueDiffOn hs
  have hdsm : ContDiffOn ℝ ∞ (_root_.fderivWithin ℝ f U) U :=
    hf.fderivWithin hU.uniqueDiffOn (by exact le_rfl)
  apply (hd.clm_apply_const hU.uniqueDiffOn hs.le hdsm v).congr
  intro x hx
  dsimp only
  rw [fderivWithin_of_isOpen hU hx]

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_RealBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma weighted_linearIsometry {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {U : Set E} (hU : UniqueDiffOn ℝ U) {f : E → X} (hf : ContDiffOn ℝ ∞ f U)
    {s C : ℝ} {m : ℕ} (hb : WeightedBound U s m C f) (A : X →ₗᵢ[ℝ] Y) :
    WeightedBound U s m C (A ∘ f) := by
  intro j hj p hp
  rw [A.norm_iteratedFDerivWithin_comp_left (hf p hp) hU hp
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))]
  exact hb j hj p hp

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MeanSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




lemma WeightedBound.extend_support {U : Set E} (hU : IsOpen U) {f : E → F}
    (hfs : tsupport f ⊆ U) {s C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C f) : WeightedBound univ s m C f := by
  intro j hj x hx
  rw [iteratedFDerivWithin_univ]
  by_cases hxU : x ∈ U
  · rw [← iteratedFDerivWithin_of_isOpen j hU hxU]
    exact hb j hj x hxU
  · have hz : f =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun hh => hxU (hfs hh))
    rw [(hz.iteratedFDeriv ℝ j).self_of_nhds]
    simpa using hC

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma WeightedBound.restrict_open {U : Set E} (hU : IsOpen U) {f : E → F}
    {s C : ℝ} {m : ℕ} (hb : WeightedBound univ s m C f) : WeightedBound U s m C f := by
  intro j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hU hx]
  simpa only [iteratedFDerivWithin_univ] using hb j hj x (mem_univ x)

lemma WeightedBound.indicator_of_support {U K : Set E} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) {f : E → F} {s C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C f) (hz : ∀ x ∈ U, x ∉ K → f x = 0) :
    WeightedBound univ s m C (U.indicator f) := by
  classical
  apply WeightedBound.extend_support hU ((tsupport_indicator_subset hK hz).trans hKU) hC
  apply hb.congr
  intro x hx
  exact indicator_of_mem hx f

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_CrossModes
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.QuadraticMean
open ClosedSurfaceR4.SmallModes (coordDeriv)
open ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.RealModes (contDiffOn_dot)

lemma weighted_real_complex {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → ℝ} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p : ℂ)) := by
  have hh := hb.linear hU hs hf Complex.ofRealCLM
  have hn : ‖Complex.ofRealCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    hh.mono_const (mul_le_of_le_one_left hC hn)




end ClosedSurfaceR4.QuadraticMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GoodDirections
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes
open Set Polynomial



lemma secondQuadratic_smul {n : ℕ} (B : Fin 3 → RVec n) (v : Base) (w : ℝ) :
    secondQuadratic B (w • v) = w ^ 2 • secondQuadratic B v := by
  ext i
  simp only [secondQuadratic, Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring



end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_JetBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates




namespace LowJet
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma contDiffAt_scalarCoefficients {J : TwoJet n}
    (hD : gramDet (J 0) (J 1) ≠ 0)
    (hb : normalPart (J 0) (J 1) (J 4) ⬝ᵥ normalPart (J 0) (J 1) (J 4) ≠ 0) :
    ContDiffAt ℝ ∞ scalarCoefficients J := by
  have h (i : Fin 5) : ContDiffAt ℝ ∞ (fun A : TwoJet n => A i) J := contDiffAt_apply ℝ (Ambient n) i J
  have hX (i : Fin 5) := contDiffAt_liftX (h 0) (h 1)
    (contDiffAt_dot (h 0) (h i)) (contDiffAt_dot (h 1) (h i)) hD
  have hY (i : Fin 5) := contDiffAt_liftY (h 0) (h 1)
    (contDiffAt_dot (h 0) (h i)) (contDiffAt_dot (h 1) (h i)) hD
  have hn (i : Fin 5) := contDiffAt_normalPart (h 0) (h 1) (h i) hD
  have hr (i : Fin 5) := contDiffAt_cdiv (contDiffAt_dot (hn i) (hn 4))
    (contDiffAt_dot (hn 4) (hn 4)) hb
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hX 2
  · exact hY 2
  · exact hX 3
  · exact hY 3
  · exact hX 4
  · exact hY 4
  · exact hr 2
  · exact hr 3

lemma contDiffAt_vectorCoefficients {J : TwoJet n}
    (hD : gramDet (J 0) (J 1) ≠ 0)
    (hb : normalPart (J 0) (J 1) (J 4) ⬝ᵥ normalPart (J 0) (J 1) (J 4) ≠ 0) :
    ContDiffAt ℝ ∞ vectorCoefficients J := by
  have h (i : Fin 5) : ContDiffAt ℝ ∞ (fun A : TwoJet n => A i) J := contDiffAt_apply ℝ (Ambient n) i J
  have hn (i : Fin 5) := contDiffAt_normalPart (h 0) (h 1) (h i) hD
  have ht (a b : ℂ) := contDiffAt_tangentLift (h 0) (h 1)
    (ux := fun _ => a) (uy := fun _ => b) contDiffAt_const contDiffAt_const hD
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hn 2
  · exact hn 3
  · exact ht 1 0
  · exact ht 0 1
  · exact ((contDiffAt_dot (hn 4) (hn 4)).fun_inv hb).smul (hn 4)

lemma Domain.smoothCoefficients {V : Set (TwoJet n)} (h : Domain V) :
    ContDiffOn ℝ ∞ coefficients V := by
  intro J hJ
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_pi.mpr
  intro i
  cases i with
  | inl i => exact contDiffAt_pi.mp (contDiffAt_scalarCoefficients (h.determinant J hJ) (h.good J hJ)) i
  | inr i =>
    exact contDiffAt_pi.mp
      (contDiffAt_pi.mp (contDiffAt_vectorCoefficients (h.determinant J hJ) (h.good J hJ)) i.1) i.2

end LowJet

lemma contDiffOn_twoJet {n : ℕ} {G : Field n} {U : Set Base} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) : ContDiffOn ℝ ∞ (twoJet G) U := by
  intro p hp
  have h := (hG p hp).contDiffAt (hU.mem_nhds hp)
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_coordDeriv h dx
  · exact contDiffAt_coordDeriv h dy
  · exact contDiffAt_coordDeriv (contDiffAt_coordDeriv h dx) dx
  · exact contDiffAt_coordDeriv (contDiffAt_coordDeriv h dy) dx
  · exact contDiffAt_coordDeriv (contDiffAt_coordDeriv h dy) dy




theorem compact_reconstructionCoefficientBound {n : ℕ} {U : Set Base}
    (hU : IsOpen U) {Ω K : Set (TwoJet n)} (hΩ : LowJet.Domain Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (G : Field n) (s C : ℝ), 0 < s → 1 ≤ C →
      ContDiffOn ℝ ∞ G U → MapsTo (twoJet G) U K →
      WeightedBound U s m C (twoJet G) →
      ReconstructionCoefficientBound G U s m ((m.factorial : ℝ) * D * C ^ m) := by
  obtain ⟨D, hD, hbD⟩ := smooth_compact_weighted_bound hU.uniqueDiffOn hΩ.isOpen.uniqueDiffOn
    hK hKΩ hΩ.smoothCoefficients m
  refine ⟨D, hD, ?_⟩
  intro G s C hs hC hG hGK hb
  have ht := contDiffOn_twoJet hU hG
  have hGΩ : MapsTo (twoJet G) U Ω := fun p hp => hKΩ (hGK hp)
  have hc := hbD (twoJet G) s C hs hC ht hGK hb
  have hsm : ContDiffOn ℝ ∞ (LowJet.coefficients ∘ twoJet G) U :=
    hΩ.smoothCoefficients.comp ht hGΩ
  have hn : 0 ≤ (m.factorial : ℝ) * D * C ^ m :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hD))
      (pow_nonneg (zero_le_one.trans hC) _)
  have hscalar (i : Fin 8) := hc.component hU.uniqueDiffOn hs.le hn hsm (Sum.inl i)
  have hvector (i : Fin 5) : WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m)
      (fun p => LowJet.vectorCoefficients (twoJet G p) i) := by
    apply WeightedBound.pi hU.uniqueDiffOn hs hn
    · intro a
      exact contDiffOn_pi.mp hsm (Sum.inr (i, a))
    · intro a
      exact hc.component hU.uniqueDiffOn hs.le hn hsm (Sum.inr (i, a))
  exact ⟨⟨⟨hscalar 0, hscalar 1, hscalar 2, hscalar 3, hscalar 4, hscalar 5,
    hscalar 6, hscalar 7⟩, hvector 0, hvector 1⟩, hvector 2, hvector 3, hvector 4⟩

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalJets
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma RealJetDomain.smoothNormal {Ω : Set RealTwoJet} (hΩ : RealJetDomain Ω) :
    ContDiffOn ℝ ∞ normalFromJet Ω := by
  intro J hJ
  have hslot (i : Fin 5) : ContDiffAt ℝ ∞ (fun K : RealTwoJet => K i) J :=
    (ContinuousLinearMap.proj i : RealTwoJet →L[ℝ] RVec 4).contDiff.contDiffAt
  have hb := contDiffAt_realNormalPart (hslot 0) (hslot 1) (hslot 4) (hΩ.determinant J hJ)
  have hn := realNormalPart_perp (J 0) (J 1) (J 4) (hΩ.determinant J hJ)
  exact (NormalFrame.contDiffAt_unitPerp (hslot 0) (hslot 1) hb
    (hΩ.determinant J hJ) (hΩ.good J hJ) hn.1 hn.2).contDiffWithinAt

lemma contDiff_realTwoJet {F : RField 4} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (realTwoJet F) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_real_coordDeriv hF dx
  · exact contDiff_real_coordDeriv hF dy
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dx) dx
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dx
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy




theorem compact_freeNormal_bound {U : Set Base} (hU : IsOpen U) {Ω K : Set RealTwoJet}
    (hΩ : RealJetDomain Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (F : RField 4) (s C : ℝ), 0 < s → 1 ≤ C →
      ContDiff ℝ ∞ F → MapsTo (realTwoJet F) U K → WeightedBound U s m C (realTwoJet F) →
      WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (freeNormal F) := by
  obtain ⟨D, hD, hbD⟩ := smooth_compact_weighted_bound hU.uniqueDiffOn hΩ.isOpen.uniqueDiffOn
    hK hKΩ hΩ.smoothNormal m
  refine ⟨D, hD, ?_⟩
  intro F s C hs hC hF hFK hb
  exact hbD (realTwoJet F) s C hs hC (contDiff_realTwoJet hF).contDiffOn hFK hb

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalProjection
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.NormalFrame

lemma gramDet_change_basis (X Y : RVec 4) (a b c d : ℝ) :
    NormalFrame.gramDet (a • X + b • Y) (c • X + d • Y) =
      (a*d-b*c)^2 * NormalFrame.gramDet X Y := by
  simp only [NormalFrame.gramDet, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, dotProduct_comm Y X]
  ring

lemma realNormalPart_linear (X Y : RVec 4) :
    IsLinearMap ℝ (realNormalPart X Y) := by
  constructor
  · intro W Z
    ext i
    simp [realNormalPart, dotProduct_add, Pi.add_apply]
    ring
  · intro s W
    ext i
    simp [realNormalPart, dotProduct_smul, Pi.smul_apply]
    ring

lemma realNormalPart_of_perp (X Y W : RVec 4) (hX : X ⬝ᵥ W = 0) (hY : Y ⬝ᵥ W = 0) :
    realNormalPart X Y W = W := by simp [realNormalPart, hX, hY]

lemma realNormalPart_self_left (X Y : RVec 4) (hD : NormalFrame.gramDet X Y ≠ 0) :
    realNormalPart X Y X = 0 := by
  have hxy : Y ⬝ᵥ X = X ⬝ᵥ Y := dotProduct_comm _ _
  have ha : ((Y ⬝ᵥ Y) * (X ⬝ᵥ X) - (X ⬝ᵥ Y) * (Y ⬝ᵥ X)) /
      NormalFrame.gramDet X Y = 1 := by
    rw [hxy]
    convert div_self hD using 1
    all_goals try with_reducible_and_instances rfl
    unfold NormalFrame.gramDet
    ring
  have hb : (X ⬝ᵥ X) * (Y ⬝ᵥ X) - (X ⬝ᵥ Y) * (X ⬝ᵥ X) = 0 := by rw [hxy]; ring
  simp [realNormalPart, ha, hb]

lemma realNormalPart_self_right (X Y : RVec 4) (hD : NormalFrame.gramDet X Y ≠ 0) :
    realNormalPart X Y Y = 0 := by
  have ha : (Y ⬝ᵥ Y) * (X ⬝ᵥ Y) - (X ⬝ᵥ Y) * (Y ⬝ᵥ Y) = 0 := by ring
  have hb : ((X ⬝ᵥ X) * (Y ⬝ᵥ Y) - (X ⬝ᵥ Y) * (X ⬝ᵥ Y)) /
      NormalFrame.gramDet X Y = 1 := by
    convert div_self hD using 1
    all_goals try with_reducible_and_instances rfl
    unfold NormalFrame.gramDet
    ring
  simp [realNormalPart, ha, hb]



lemma realNormalPart_change_basis (X Y W : RVec 4) (a b c d : ℝ)
    (hD : NormalFrame.gramDet X Y ≠ 0) (hdet : a*d-b*c ≠ 0) :
    realNormalPart (a • X + b • Y) (c • X + d • Y) W = realNormalPart X Y W := by
  let Z := realNormalPart (a • X + b • Y) (c • X + d • Y) W
  have hD' : NormalFrame.gramDet (a • X + b • Y) (c • X + d • Y) ≠ 0 := by
    rw [gramDet_change_basis]
    exact mul_ne_zero (pow_ne_zero 2 hdet) hD
  obtain ⟨hAZ, hBZ⟩ := realNormalPart_perp (a • X + b • Y) (c • X + d • Y) W hD'
  change (a • X + b • Y) ⬝ᵥ Z = 0 at hAZ
  change (c • X + d • Y) ⬝ᵥ Z = 0 at hBZ
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at hAZ hBZ
  have hXZ : X ⬝ᵥ Z = 0 := by
    apply (mul_eq_zero.mp (show (a*d-b*c) * (X ⬝ᵥ Z) = 0 by
      linear_combination d * hAZ - b * hBZ)).resolve_left hdet
  have hYZ : Y ⬝ᵥ Z = 0 := by
    apply (mul_eq_zero.mp (show (a*d-b*c) * (Y ⬝ᵥ Z) = 0 by
      linear_combination a * hBZ - c * hAZ)).resolve_left hdet
  have hlin := realNormalPart_linear X Y
  have hA : realNormalPart X Y (a • X + b • Y) = 0 := by
    rw [hlin.map_add, hlin.map_smul, hlin.map_smul, realNormalPart_self_left _ _ hD,
      realNormalPart_self_right _ _ hD, smul_zero, smul_zero, add_zero]
  have hB : realNormalPart X Y (c • X + d • Y) = 0 := by
    rw [hlin.map_add, hlin.map_smul, hlin.map_smul, realNormalPart_self_left _ _ hD,
      realNormalPart_self_right _ _ hD, smul_zero, smul_zero, add_zero]
  have he : realNormalPart X Y Z = realNormalPart X Y W := by
    dsimp [Z]
    conv_lhs => arg 3; unfold realNormalPart
    rw [hlin.map_sub, hlin.map_sub, hlin.map_smul, hlin.map_smul, hA, hB]
    simp
  exact (realNormalPart_of_perp X Y Z hXZ hYZ).symm.trans he

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SecondForms
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set

lemma real_second_coordDeriv {n : ℕ} {F : RField n} {p : Base}
    (hF : DifferentiableAt ℝ (fderiv ℝ F) p) (v w : Base) :
    coordDeriv v (coordDeriv w F) p = fderiv ℝ (fderiv ℝ F) p v w := by
  have h := (hF.hasFDerivAt.clm_apply (hasFDerivAt_const w p)).fderiv
  change (fderiv ℝ (fun q => (fderiv ℝ F q) w) p) v = _
  rw [h]
  simp

lemma real_second_coordDeriv_comm {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) : coordDeriv v (coordDeriv w F) p = coordDeriv w (coordDeriv v F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
  rw [real_second_coordDeriv hd, real_second_coordDeriv hd]
  exact second_derivative_symmetric
    (fun q => (hF.differentiable (by simp) q).hasFDerivAt) hd.hasFDerivAt v w

lemma base_eq_basis (v : Base) : v = v.1 • dx + v.2 • dy := by ext <;> simp [dx,dy]

lemma coordDeriv_eq_basis {n : ℕ} (F : RField n) (v p : Base) :
    coordDeriv v F p = v.1 • coordDeriv dx F p + v.2 • coordDeriv dy F p := by
  conv_lhs => arg 1; rw [base_eq_basis v]
  simp [coordDeriv]

lemma second_coordDeriv_quadratic {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (v p : Base) : coordDeriv v (coordDeriv v F) p =
      (v.1^2) • coordDeriv dx (coordDeriv dx F) p +
      (2*v.1*v.2) • coordDeriv dx (coordDeriv dy F) p +
      (v.2^2) • coordDeriv dy (coordDeriv dy F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  have hsym := real_second_coordDeriv_comm hF p dy dx
  simp only [real_second_coordDeriv hd] at hsym ⊢
  conv_lhs => arg 2; rw [base_eq_basis v]
  conv_lhs => arg 1; arg 2; rw [base_eq_basis v]
  simp only [map_add, map_smul, add_apply, smul_apply,
    hsym]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma coordDeriv_comp_linear {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (e : Base →L[ℝ] Base) (v p : Base) :
    coordDeriv v (F ∘ e) p = coordDeriv (e v) F (e p) := by
  simp only [coordDeriv, fderiv_comp p (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) e.differentiableAt,
    e.fderiv, ContinuousLinearMap.comp_apply]

lemma second_coordDeriv_comp_linear {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (e : Base →L[ℝ] Base) (v w p : Base) :
    coordDeriv v (coordDeriv w (F ∘ e)) p =
      coordDeriv (e v) (coordDeriv (e w) F) (e p) := by
  have he : coordDeriv w (F ∘ e) = (coordDeriv (e w) F) ∘ e := by
    funext q; exact coordDeriv_comp_linear hF e w q
  rw [he, coordDeriv_comp_linear (contDiff_real_coordDeriv hF (e w))]


lemma realSecondForm_quadratic {F : RField 4} (hF : ContDiff ℝ ∞ F) (v p : Base) :
    realSecondForm F v v p = secondQuadratic (realSecondTensor F p) v := by
  unfold realSecondForm
  rw [second_coordDeriv_quadratic hF]
  have hlin := realNormalPart_linear (coordDeriv dx F p) (coordDeriv dy F p)
  rw [hlin.map_add, hlin.map_add, hlin.map_smul, hlin.map_smul, hlin.map_smul]
  simp [secondQuadratic, realSecondTensor, realSecondForm]

lemma realSecondForm_comp_linear {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (e : Base →L[ℝ] Base) (v w p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (e p)) (coordDeriv dy F (e p)) ≠ 0)
    (hdet : (e dx).1 * (e dy).2 - (e dx).2 * (e dy).1 ≠ 0) :
    realSecondForm (F ∘ e) v w p = realSecondForm F (e v) (e w) (e p) := by
  unfold realSecondForm
  rw [coordDeriv_comp_linear hF, coordDeriv_comp_linear hF, second_coordDeriv_comp_linear hF,
    coordDeriv_eq_basis F (e dx), coordDeriv_eq_basis F (e dy), realNormalPart_change_basis]
  · exact hD
  · exact hdet

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ImmersionJets
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes



lemma gramDet_ne_zero_of_injective (A : Base →L[ℝ] RVec 4) (hA : Function.Injective A) :
    NormalFrame.gramDet (A dx) (A dy) ≠ 0 := by
  let X := A dx
  let Y := A dy
  have hX : X ≠ 0 := by
    intro hx
    have he : dx = 0 := hA (by simpa [X] using hx)
    exact one_ne_zero (congrArg Prod.fst he)
  have hXX : X ⬝ᵥ X ≠ 0 := (dotProduct_self_eq_zero).not.mpr hX
  intro hD
  let v : Base := -(X ⬝ᵥ Y) • dx + (X ⬝ᵥ X) • dy
  have hv : A v = -(X ⬝ᵥ Y) • X + (X ⬝ᵥ X) • Y := by simp [v,X,Y]
  have hsq : A v ⬝ᵥ A v = (X ⬝ᵥ X) * NormalFrame.gramDet X Y := by
    rw [hv]
    simp only [NormalFrame.gramDet, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, dotProduct_comm Y X]
    ring
  have hz : A v = 0 := dotProduct_self_eq_zero.mp (by rw [hsq]; change _ * NormalFrame.gramDet (A dx) (A dy) = 0; rw [hD,mul_zero])
  have hv0 : v = 0 := hA (by simpa using hz)
  have hy0 := congrArg Prod.snd hv0
  exact hXX (by simpa [v,dx,dy] using hy0)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PullbackBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes (Base coordDeriv)
open ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.RealModes (complexify)
open ClosedSurfaceR4.QuadraticMean (weighted_real_complex)

lemma weighted_base_fst {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → Base} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p).1) := by
  exact (hb.linear hU hs hf (ContinuousLinearMap.fst ℝ ℝ ℝ)).mono_const
    (mul_le_of_le_one_left hC (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ))

lemma weighted_base_snd {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → Base} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p).2) := by
  exact (hb.linear hU hs hf (ContinuousLinearMap.snd ℝ ℝ ℝ)).mono_const
    (mul_le_of_le_one_left hC (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ))

lemma weighted_complexEvaluate {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {A : Base → ComplexTensor} {v w : Base → Base} {s C D B : ℝ} {m : ℕ}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hA : ContDiffOn ℝ ∞ A U) (hv : ContDiffOn ℝ ∞ v U) (hw : ContDiffOn ℝ ∞ w U)
    (hbA : WeightedBound U s m C A) (hbv : WeightedBound U s m D v)
    (hbw : WeightedBound U s m B w) :
    WeightedBound U s m (4 * (2 ^ m * (2 ^ m * C * D) * B))
      (fun p => complexEvaluate (A p) (v p) (w p)) := by
  have hvc := Complex.ofRealCLM.contDiff.comp_contDiffOn hv.fst
  have hvd := Complex.ofRealCLM.contDiff.comp_contDiffOn hv.snd
  have hwc := Complex.ofRealCLM.contDiff.comp_contDiffOn hw.fst
  have hwd := Complex.ofRealCLM.contDiff.comp_contDiffOn hw.snd
  have hvcB := weighted_real_complex hU hs hD hv.fst (weighted_base_fst hU hs hD hv hbv)
  have hvdB := weighted_real_complex hU hs hD hv.snd (weighted_base_snd hU hs hD hv hbv)
  have hwcB := weighted_real_complex hU hs hB hw.fst (weighted_base_fst hU hs hB hw hbw)
  have hwdB := weighted_real_complex hU hs hB hw.snd (weighted_base_snd hU hs hB hw hbw)
  have h0s := ((contDiffOn_pi.mp hA 0).mul hvc).mul hwc
  have h1s := (contDiffOn_pi.mp hA 1).mul ((hvc.mul hwd).add (hvd.mul hwc))
  have h2s := ((contDiffOn_pi.mp hA 2).mul hvd).mul hwd
  have h0 := ((hbA.component hU hs hC hA 0).mul hU hs hC hD
    (contDiffOn_pi.mp hA 0) hvc hvcB).mul hU hs (by positivity) hB
    ((contDiffOn_pi.mp hA 0).mul hvc) hwc hwcB
  have h2 := ((hbA.component hU hs hC hA 2).mul hU hs hC hD
    (contDiffOn_pi.mp hA 2) hvd hvdB).mul hU hs (by positivity) hB
    ((contDiffOn_pi.mp hA 2).mul hvd) hwd hwdB
  have h11 := hvcB.mul hU hs hD hB hvc hwd hwdB
  have h12 := hvdB.mul hU hs hD hB hvd hwc hwcB
  have h1 := (hbA.component hU hs hC hA 1).mul hU hs hC (by positivity)
    (contDiffOn_pi.mp hA 1) ((hvc.mul hwd).add (hvd.mul hwc))
    (h11.add hU hs (hvc.mul hwd) (hvd.mul hwc) h12)
  have hh := (h0.add hU hs h0s h1s h1).add hU hs (h0s.add h1s) h2s h2
  convert hh using 1 <;> first | rfl | ring

lemma weighted_complexPullbackField_apply {U : Set Base} (hU : IsOpen U)
    {A : Base → ComplexTensor} {e : Base → Base} {s C D : ℝ} {m : ℕ}
    (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ContDiffOn ℝ ∞ A U) (he : ContDiffOn ℝ ∞ e U)
    (hbA : WeightedBound U s m C A)
    (hbe : ∀ v, ‖v‖ ≤ 1 → WeightedBound U s m D (coordDeriv v e)) :
    WeightedBound U s m (4 * (2 ^ m * (2 ^ m * C * D) * D))
      (fun p => complexPullbackField e p (A p)) := by
  apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
    (contDiffOn_pi.mp (contDiffOn_complexPullbackField_apply hU hA he))
  intro i
  exact weighted_complexEvaluate hU.uniqueDiffOn hs.le hC hD hD hA
    (ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU he (firstDirection i))
    (ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU he (secondDirection i)) hbA
    (hbe _ (firstDirection_norm i)) (hbe _ (secondDirection_norm i))

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_UniformMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.FiniteMean Set
open ClosedSurfaceR4.RootMean



lemma weighted_coordDeriv_of_jets {U : Set Base} (hU : IsOpen U)
    {f : Base → Base} (hf : ContDiffOn ℝ ∞ f U) {τ D : ℝ} {m : ℕ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ j, 1 ≤ j → j ≤ m + 1 → ∀ p ∈ U,
      ‖iteratedFDerivWithin ℝ j f U p‖ ≤ D) (v : Base) (hv : ‖v‖ ≤ 1) :
    WeightedBound U τ m D (coordDeriv v f) := by
  have hd : WeightedBound U τ m D (fderivWithin ℝ f U) := by
    intro j hj p hp
    rw [norm_iteratedFDerivWithin_fderivWithin hU.uniqueDiffOn hp]
    exact (mul_le_mul_of_nonneg_left (hb (j+1) (by omega) (by omega) p hp)
      (pow_nonneg hτ j)).trans (mul_le_of_le_one_left hD (pow_le_one₀ hτ hτ1))
  have hh := hd.clm_apply_const hU.uniqueDiffOn hτ
    (hf.fderivWithin hU.uniqueDiffOn le_rfl) v
  apply (hh.mono_const (mul_le_of_le_one_left hD hv)).congr
  intro p hp
  simp only [coordDeriv, fderivWithin_of_isOpen hU hp]



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseReparametrization
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A good covector supplies the actual free coordinate system for a mode. -/

noncomputable section

namespace ClosedSurfaceR4.RealModes

open SmallModes PhaseGeometry Set
open scoped ContDiff

lemma phaseInverse_det {ξ : Base} (hξ : ξ ≠ 0) :
    (((phaseEquiv ξ hξ).symm dx).1 * ((phaseEquiv ξ hξ).symm dy).2 -
      ((phaseEquiv ξ hξ).symm dx).2 * ((phaseEquiv ξ hξ).symm dy).1) ≠ 0 := by
  have hd : ξ.1 ^ 2 + ξ.2 ^ 2 ≠ 0 := (covector_length_sq_pos hξ).ne'
  have he :
      (((phaseEquiv ξ hξ).symm dx).1 * ((phaseEquiv ξ hξ).symm dy).2 -
        ((phaseEquiv ξ hξ).symm dx).2 * ((phaseEquiv ξ hξ).symm dy).1) =
        (ξ.1 ^ 2 + ξ.2 ^ 2)⁻¹ := by
    simp only [phaseEquiv_symm_apply, dx, dy]
    field_simp
    ring
  rw [he]
  exact inv_ne_zero hd

lemma phaseInverse_dy {ξ : Base} (hξ : ξ ≠ 0) :
    (phaseEquiv ξ hξ).symm dy = (ξ.1 ^ 2 + ξ.2 ^ 2)⁻¹ • (-ξ.2, ξ.1) := by
  ext <;> simp [dy, div_eq_mul_inv, mul_comm]

/-- The normal acceleration in the new y direction is a positive scalar
multiple of the old second fundamental form in the covector's kernel. -/
theorem realSecond_phase {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {ξ : Base} (hξ : ξ ≠ 0) (p : Base)
    (hImm : Function.Injective (fderiv ℝ F ((phaseEquiv ξ hξ).symm p))) :
    realSecond (F ∘ (phaseEquiv ξ hξ).symm) p =
      ((ξ.1 ^ 2 + ξ.2 ^ 2)⁻¹) ^ 2 •
        secondQuadratic (realSecondTensor F ((phaseEquiv ξ hξ).symm p)) (-ξ.2, ξ.1) := by
  change realSecondForm (F ∘ (phaseEquiv ξ hξ).symm) dy dy p = _
  have he := realSecondForm_comp_linear hF (phaseEquiv ξ hξ).symm.toContinuousLinearMap
    dy dy p (gramDet_ne_zero_of_injective _ hImm) (phaseInverse_det hξ)
  simp only [ContinuousLinearEquiv.coe_coe] at he
  rw [he]
  rw [phaseInverse_dy, realSecondForm_quadratic hF, secondQuadratic_smul]

/-- Immersion and the good-direction condition on an open set produce the
free-mode domain required by the finite oscillatory construction. -/
theorem realModeDomain_phase {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {O : Set Base} (hO : IsOpen O) {ξ : Base} (hξ : ξ ≠ 0)
    (hImm : ∀ p ∈ O, Function.Injective (fderiv ℝ F p))
    (hgood : ∀ p ∈ O, Good (realSecondTensor F p) ξ) :
    RealModeDomain (F ∘ (phaseEquiv ξ hξ).symm) ((phaseEquiv ξ hξ) '' O) := by
  refine ⟨(phaseEquiv ξ hξ).isOpenMap O hO, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    apply gramDet_ne_zero_of_injective
    rw [fderiv_comp _ (hF.differentiable (by simp) _)
      (phaseEquiv ξ hξ).symm.differentiableAt]
    simpa only [ContinuousLinearEquiv.fderiv, ContinuousLinearMap.coe_comp,
      ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using
      (hImm p hp).comp (phaseEquiv ξ hξ).symm.injective
  · rintro _ ⟨p, hp, rfl⟩
    have hi : Function.Injective (fderiv ℝ F
        ((phaseEquiv ξ hξ).symm ((phaseEquiv ξ hξ) p))) := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hImm p hp
    rw [realSecond_phase hF hξ _ hi, ContinuousLinearEquiv.symm_apply_apply]
    exact smul_ne_zero (pow_ne_zero 2 (inv_ne_zero (covector_length_sq_pos hξ).ne'))
      (hgood p hp).2

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LinearPhaseChart
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit restricted linear chart used for a nonzero phase covector. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma linearPhaseChart_phase (ξ : Base) (hξ : ξ ≠ 0) (U : Set Base) (hU : IsOpen U)
    (x : Base) : (linearPhaseChart ξ hξ U hU x).1 = phaseLinear ξ x := rfl

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GoodPhaseC2Stability
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The good-phase stability radius uses only the ordinary C2 difference. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry WeightedEstimates

lemma coordDeriv_sub_smooth {F G : RField 4} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (v : Base) :
    coordDeriv v (F-G) = coordDeriv v F - coordDeriv v G := by
  funext p
  simp only [coordDeriv, fderiv_sub (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)
    (hG.differentiable (by simp) p), sub_apply, Pi.sub_apply]

lemma realTwoJet_sub {F G : RField 4} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    realTwoJet (F-G) = realTwoJet F - realTwoJet G := by
  have hx := coordDeriv_sub_smooth hF hG dx
  have hy := coordDeriv_sub_smooth hF hG dy
  have hxx := coordDeriv_sub_smooth (contDiff_real_coordDeriv hF dx)
    (contDiff_real_coordDeriv hG dx) dx
  have hxy := coordDeriv_sub_smooth (contDiff_real_coordDeriv hF dy)
    (contDiff_real_coordDeriv hG dy) dx
  have hyy := coordDeriv_sub_smooth (contDiff_real_coordDeriv hF dy)
    (contDiff_real_coordDeriv hG dy) dy
  funext p i
  fin_cases i <;> simp [realTwoJet,hx,hy,hxx,hxy,hyy]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_DirectionalJetBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Higher directional jets of a controlled second jet lose one scale per
additional derivative. These are the factors in the finite jet polynomials. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.WeightedEstimates

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeightedBound.iteratedDirectional {U : Set A} (hU : IsOpen U) {f : A → E}
    {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hf : ContDiffOn ℝ ∞ f U)
    (vs : List A) (hv : ∀ v ∈ vs, ‖v‖ ≤ 1) (m : ℕ)
    (hb : WeightedBound U s (m + vs.length) C f) :
    WeightedBound U s m (C / s ^ vs.length) (iteratedDirectional vs f) := by
  induction vs generalizing m with
  | nil => simpa [ClosedSurfaceR4.WeightedEstimates.iteratedDirectional] using hb
  | cons v vs ih =>
    have he : m + (v :: vs).length = (m + 1) + vs.length := by simp; omega
    have ht := ih (fun w hw => hv w (List.mem_cons_of_mem v hw)) (m + 1) (he ▸ hb)
    have hd := ht.directional hU hs (contDiffOn_iteratedDirectional hU hf vs) v
    apply hd.mono_const
    have hn : ‖v‖ ≤ 1 := hv v (List.mem_cons_self ..)
    have hc : 0 ≤ C / s ^ vs.length / s := by positivity
    calc
      ‖v‖ * (C / s ^ vs.length / s) ≤ C / s ^ vs.length / s := mul_le_of_le_one_left hc hn
      _ = C / s ^ (v :: vs).length := by simp [pow_succ, div_div]

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JetWordDecomposition
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every ordered coordinate jet is a derivative of a component of the
actual second jet, with precisely the excess derivative count. -/
noncomputable section

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma exists_lowWord (w : List (Fin 2)) (hw : w.length ≤ 2) :
    ∃ i : Fin 7, lowWord i = w := by
  cases w with
  | nil => exact ⟨0, rfl⟩
  | cons a w =>
    cases w with
    | nil =>
      fin_cases a
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    | cons b w =>
      have he : w = [] := List.eq_nil_of_length_eq_zero (by
        simp only [List.length_cons] at hw
        omega)
      subst w
      fin_cases a <;> fin_cases b
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨6, rfl⟩

lemma split_lowWord (w : List (Fin 2)) :
    ∃ v : List (Fin 2), ∃ i : Fin 7, w = v ++ lowWord i ∧ v.length = w.length - 2 := by
  obtain ⟨i, hi⟩ := exists_lowWord (w.drop (w.length - 2)) (by
    rw [List.length_drop]
    omega)
  refine ⟨w.take (w.length - 2), i, ?_, ?_⟩
  · rw [hi, List.take_append_drop]
  · rw [List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]

lemma iteratedDirectional_append {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v w : List A) (f : A → E) :
    iteratedDirectional (v ++ w) f = iteratedDirectional v (iteratedDirectional w f) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    simp only [List.cons_append, iteratedDirectional, ih]

/-- The scale loss of an ordered jet factor is its derivative order minus two. -/
lemma jet_as_lowJet_derivative (w : List (Fin 2)) (a : Fin 4) :
    ∃ v : List (Fin 2), ∃ i : Fin 7, v.length = w.length - 2 ∧
      ∀ (G : Base → Space), jet G w a =
        iteratedDirectional (v.map coordinateVector) (fun p => lowJet G p (Sum.inr (i, a))) := by
  obtain ⟨v, i, hw, hv⟩ := split_lowWord w
  refine ⟨v, i, hv, ?_⟩
  intro G
  change iteratedDirectional (w.map coordinateVector) (fun p => G p a) = _
  rw [hw, List.map_append, iteratedDirectional_append]
  rfl

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedActualJets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual jets have precisely one scale loss per derivative beyond the
controlled second jet, with no loss for their first two derivatives. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma norm_coordinateVector_le (v : Fin 2) : ‖coordinateVector v‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro i
  by_cases h : i = v
  · subst i
    simp [coordinateVector]
  · simp [coordinateVector, h]

/-- A weighted bound on the second-jet map controls every actual higher jet. -/
theorem weighted_actual_jet {U : Set Base} (hU : IsOpen U) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) {s B : ℝ} (hs : 0 < s) (hB : 0 ≤ B)
    (m : ℕ) (w : List (Fin 2)) (a : Fin 4)
    (hb : WeightedBound U s (m + (w.length - 2)) B (lowJet G)) :
    WeightedBound U s m (B / s ^ (w.length - 2)) (jet G w a) := by
  obtain ⟨v, i, hv, he⟩ := jet_as_lowJet_derivative w a
  rw [he G]
  have hQ := (lowJet_smooth hG).contDiffOn (s := U)
  have hcomp := hb.component hU.uniqueDiffOn hs.le hB hQ (Sum.inr (i, a))
  have hf : ContDiffOn ℝ ∞ (fun p => lowJet G p (Sum.inr (i, a))) U :=
    (contDiff_pi.mp (lowJet_smooth hG) (Sum.inr (i, a))).contDiffOn
  have hvnorm : ∀ x ∈ v.map coordinateVector, ‖x‖ ≤ 1 := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact norm_coordinateVector_le j
  have hcomp' : WeightedBound U s (m + (v.map coordinateVector).length) B
      (fun p => lowJet G p (Sum.inr (i, a))) := by
    simpa only [List.length_map, hv] using hcomp
  have hd := hcomp'.iteratedDirectional hU hs hB hf (v.map coordinateVector) hvnorm m
  simpa only [List.length_map, hv] using hd

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedLowCoefficients
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform angular-slice estimates for smooth low-jet coefficients on a
compact admissible set. The angular parameter adds no scale loss. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma weighted_lowJet_pair {U : Set Base} (hU : IsOpen U) {Q : Base → LowJet}
    (hQ : ContDiffOn ℝ ∞ Q U) {s B : ℝ} (hs : 0 < s) (hB : 1 ≤ B) (m : ℕ)
    (hb : WeightedBound U s m B Q) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    WeightedBound U s m (2 * B) (fun p => (Q p, t)) := by
  have hleft : WeightedBound U s m B (fun p => (Q p, (0 : ℝ))) := by
    simpa only [ContinuousLinearMap.norm_inl, one_mul, Function.comp_def,
      ContinuousLinearMap.inl_apply] using
      hb.linear hU.uniqueDiffOn hs.le hQ (ContinuousLinearMap.inl ℝ LowJet ℝ)
  have hc : ‖((0 : LowJet), t)‖ ≤ 1 := by
    rw [Prod.norm_def, norm_zero, Real.norm_of_nonneg ht.1]
    exact max_le (by norm_num) ht.2
  have hright : WeightedBound U s m 1 (fun _ : Base => ((0 : LowJet), t)) :=
    (weightedBound_const U s m ((0 : LowJet), t)).mono_const hc
  have hsum := hleft.add hU.uniqueDiffOn hs.le (hQ.prodMk contDiffOn_const) contDiffOn_const hright
  have hp : WeightedBound U s m (B + 1) (fun p => (Q p, t)) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using hsum
  exact hp.mono_const (by linarith)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedCoefficientVariation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A low-jet coefficient variation is linear in the varied map and loses
only the two derivatives in its second jet. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem compact_low_coefficient_vector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {c : LowJet × ℝ → E} (hc : ContDiffOn ℝ ∞ c (O ×ˢ Set.univ))
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (Q : Base → LowJet) (s : ℝ), 0 < s →
      ContDiffOn ℝ ∞ Q U → Set.MapsTo Q U K → WeightedBound U s m B Q →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, WeightedBound U s m D (fun p => c (Q p, t)) := by
  have hsub : K ×ˢ Set.Icc (0 : ℝ) 1 ⊆ O ×ˢ Set.univ :=
    fun _ hz => ⟨hKO hz.1, Set.mem_univ _⟩
  obtain ⟨D, hD, hb⟩ := smooth_compact_weighted_bound hU.uniqueDiffOn
    (hO.prod isOpen_univ).uniqueDiffOn (hK.prod isCompact_Icc) hsub hc m
  refine ⟨(m.factorial : ℝ) * D * (2 * B) ^ m, by positivity, ?_⟩
  intro Q s hs hQ hQK hQB t ht
  exact hb (fun p => (Q p, t)) s (2 * B) hs (by linarith)
    (hQ.prodMk contDiffOn_const) (fun p hp => ⟨hQK hp, ht⟩)
    (weighted_lowJet_pair hU hQ hs hB m hQB ht)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_MixedJetPolynomial
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomials in the base-map jet and three independent variation jets.
Differentiating the base map increases the scale loss by at most two. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

namespace MixedExpression

lemma ofExpression_loss (e : Expression) : (ofExpression e).loss = e.loss := by
  induction e with
  | coeff => rfl
  | atom _ _ _ ih => simp only [ofExpression, loss, ↓reduceIte, Expression.loss, ih]
  | add _ _ ihe ihf => simp only [ofExpression, loss, Expression.loss, ihe, ihf]

lemma loss_sumList_le {ι : Type*} (l : List ι) (f : ι → MixedExpression) (N : ℕ)
    (h : ∀ i ∈ l, (f i).loss ≤ N) : (sumList l f).loss ≤ N := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons i l ih =>
    exact max_le (h i (List.mem_cons_self ..))
      (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

theorem loss_differentiate (j : Fin 3) (e : MixedExpression) :
    (e.differentiate j).loss ≤ e.loss + 2 := by
  induction e with
  | coeff c =>
    apply loss_sumList_le
    intro i _
    have hl : (lowWord i.1).length ≤ 2 := by
      obtain ⟨i, a⟩ := i
      fin_cases i <;> simp [lowWord]
    simpa only [loss, Fin.succ_ne_zero, ↓reduceIte, Nat.add_zero] using hl
  | atom i w a e ih =>
    by_cases hi : i = 0
    · subst i
      simp only [differentiate, loss, Fin.succ_ne_zero, ↓reduceIte]
      omega
    · simp only [differentiate, hi, ↓reduceIte, loss]
      omega
  | add e f ihe ihf =>
    simp only [differentiate, loss]
    omega

theorem loss_third_variation (e : Expression) :
    ((((ofExpression e).differentiate 0).differentiate 1).differentiate 2).loss ≤ e.loss + 6 := by
  have h₁ := loss_differentiate 0 (ofExpression e)
  have h₂ := loss_differentiate 1 ((ofExpression e).differentiate 0)
  have h₃ := loss_differentiate 2 (((ofExpression e).differentiate 0).differentiate 1)
  rw [ofExpression_loss] at h₁
  omega

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetRegularity
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial order and smoothness of mixed jet expressions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

lemma order_sumList_le {ι : Type*} (l : List ι) (f : ι → MixedExpression) (N : ℕ)
    (hN : 2 ≤ N) (h : ∀ i ∈ l, (f i).order ≤ N) : (sumList l f).order ≤ N := by
  induction l with
  | nil => exact hN
  | cons i l ih =>
    exact max_le (h i (List.mem_cons_self ..))
      (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

lemma order_differentiate (j : Fin 3) (e : MixedExpression) :
    (e.differentiate j).order ≤ e.order := by
  induction e with
  | coeff c =>
    apply order_sumList_le _ _ 2 (le_refl 2)
    intro i _
    have hl : (lowWord i.1).length ≤ 2 := by
      obtain ⟨i, a⟩ := i
      fin_cases i <;> simp [lowWord]
    exact max_le hl (le_refl 2)
  | atom i w a e ih =>
    by_cases hi : i = 0
    · simp only [differentiate, hi, ↓reduceIte, order]
      omega
    · simp only [differentiate, hi, ↓reduceIte, order]
      omega
  | add e f ihe ihf =>
    simp only [differentiate, order]
    omega

lemma order_ofExpression (e : Expression) : (ofExpression e).order = e.order := by
  induction e with
  | coeff => rfl
  | atom _ _ _ ih => simp only [ofExpression, order, Expression.order, ih]
  | add _ _ ihe ihf => simp only [ofExpression, order, Expression.order, ihe, ihf]

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetCalculus
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coefficient part of the mixed polynomial variation is the actual
low-jet chain rule, with the position coordinates held fixed. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial

lemma variationLowJet_expansion (H : Base → Space) (p : Base) :
    variationLowJet H p = ∑ i : Fin 7 × Fin 4,
      jet H (lowWord i.1) i.2 p • lowBasis (.inr i) := by
  funext k
  cases k with
  | inl k => simp [variationLowJet, lowBasis]
  | inr k => simp [variationLowJet, lowBasis, Pi.single_apply]

lemma coefficient_variation_sum (c : LowJet × ℝ → ℝ) (G H : Base → Space) (z : Base × ℝ) :
    fderiv ℝ c (lowJet G z.1, z.2) (variationLowJet H z.1, 0) =
      ∑ i : Fin 7 × Fin 4, jet H (lowWord i.1) i.2 z.1 *
        fderiv ℝ c (lowJet G z.1, z.2) (lowBasis (.inr i), 0) := by
  let L : LowJet →L[ℝ] ℝ :=
    (fderiv ℝ c (lowJet G z.1, z.2)).comp (ContinuousLinearMap.inl ℝ LowJet ℝ)
  change L (variationLowJet H z.1) = _
  rw [variationLowJet_expansion, map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialVariationBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first three actual polynomial variations have one fixed scale
exponent, the excess-jet loss plus six. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression

namespace Expression

lemma variations_order (e : Expression) (i : Fin 3) : (e.variations i).order ≤ e.order := by
  have h₁ := order_differentiate 0 (ofExpression e)
  have h₂ := order_differentiate 1 ((ofExpression e).differentiate 0)
  have h₃ := order_differentiate 2 (((ofExpression e).differentiate 0).differentiate 1)
  rw [order_ofExpression] at h₁
  fin_cases i
  · exact h₁
  · exact h₂.trans h₁
  · exact h₃.trans (h₂.trans h₁)

lemma variations_loss (e : Expression) (i : Fin 3) : (e.variations i).loss ≤ e.loss + 6 := by
  have h₁ := loss_differentiate 0 (ofExpression e)
  have h₂ := loss_differentiate 1 ((ofExpression e).differentiate 0)
  have h₃ := loss_differentiate 2 (((ofExpression e).differentiate 0).differentiate 1)
  rw [ofExpression_loss] at h₁
  fin_cases i
  · change ((ofExpression e).differentiate 0).loss ≤ e.loss + 6
    omega
  · change (((ofExpression e).differentiate 0).differentiate 1).loss ≤ e.loss + 6
    omega
  · exact loss_third_variation e

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedComplexMixedJets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-scale evaluation: the output is measured at the slow scale, while
only the explicit jet excess contributes short-scale loss. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression
open WeightedEstimates

theorem compact_complex_mixed_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : MixedExpression) (he : e.SmoothCoeffs O) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (J : JetData) (s τ : ℝ),
      0 < s → 0 < τ → τ ≤ 1 → ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) U K →
      WeightedBound U s m B (lowJet G) →
      (∀ i w a, ContDiffOn ℝ ∞ (J i w a) U) →
      (∀ i w a, w.length ≤ e.order →
        WeightedBound U s m (B / τ ^ slotLoss i w) (J i w a)) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (D / τ ^ e.loss) (fun p => e.evalComplex G J (p, t)) := by
  induction e with
  | coeff c =>
    have hc := Complex.ofRealCLM.contDiff.comp_contDiffOn he
    obtain ⟨D, hD, hd⟩ := compact_low_coefficient_vector hU hO hK hKO hc m B hB
    refine ⟨D, hD, ?_⟩
    intro G J s τ hs _ _ hG hGK hb _ _ t ht
    simpa only [loss, pow_zero, div_one, evalComplex, Function.comp_def,
      Complex.ofRealCLM_apply] using hd (lowJet G) s hs (lowJet_smooth hG).contDiffOn hGK hb t ht
  | atom i w a e ih =>
    obtain ⟨D, hD, hd⟩ := ih he
    refine ⟨2 ^ m * B * D, by positivity, ?_⟩
    intro G J s τ hs hτ hτ1 hG hGK hb hJ hJB t ht
    have hQ : Set.MapsTo (lowJet G) U O := fun _ hp => hKO (hGK hp)
    have htBound := hd G J s τ hs hτ hτ1 hG hGK hb hJ
      (fun j v b hv => hJB j v b (hv.trans (le_max_right _ _))) t ht
    have hjBound := hJB i w a (le_max_left _ _)
    have hp := hjBound.mul hU.uniqueDiffOn hs.le (by positivity) (by positivity)
      (hJ i w a) (evalComplex_parameter_smooth hG hQ hJ (e := e) he t) htBound
    convert hp using 1 <;> first | rfl | simp only [loss, slotLoss, pow_add]; ring
  | add e f ihe ihf =>
    obtain ⟨D, hD, hd⟩ := ihe he.1
    obtain ⟨C, hC, hc⟩ := ihf he.2
    refine ⟨D + C, add_nonneg hD hC, ?_⟩
    intro G J s τ hs hτ hτ1 hG hGK hb hJ hJB t ht
    have hQ : Set.MapsTo (lowJet G) U O := fun _ hp => hKO (hGK hp)
    have hd' := hd G J s τ hs hτ hτ1 hG hGK hb hJ
      (fun i w a hw => hJB i w a (hw.trans (le_max_left _ _))) t ht
    have hc' := hc G J s τ hs hτ hτ1 hG hGK hb hJ
      (fun i w a hw => hJB i w a (hw.trans (le_max_right _ _))) t ht
    have hd'' : WeightedBound U s m (D / τ ^ max e.loss f.loss)
        (fun p => e.evalComplex G J (p, t)) :=
      hd'.mono_const (div_le_div_of_nonneg_left hD (pow_pos hτ _)
        (pow_le_pow_of_le_one hτ.le hτ1 (le_max_left _ _)))
    have hc'' : WeightedBound U s m (C / τ ^ max e.loss f.loss)
        (fun p => f.evalComplex G J (p, t)) :=
      hc'.mono_const (div_le_div_of_nonneg_left hC (pow_pos hτ _)
        (pow_le_pow_of_le_one hτ.le hτ1 (le_max_right _ _)))
    simpa only [loss, add_div, evalComplex] using hd''.add hU.uniqueDiffOn hs.le
      (evalComplex_parameter_smooth hG hQ hJ (e := e) he.1 t)
      (evalComplex_parameter_smooth hG hQ hJ (e := f) he.2 t) hc''

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedModulatedJets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Slow-scale bounds on the amplitudes of fast oscillatory jets. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates

lemma weighted_complexify {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → ℝ} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p : ℂ)) := by
  have hh := hb.linear hU hs hf Complex.ofRealCLM
  have hn : ‖Complex.ofRealCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    hh.mono_const (mul_le_of_le_one_left hC hn)

lemma weighted_amplitudeDerivative {U : Set Base} (hU : IsOpen U)
    {φ : Base → ℝ} {Z : Base → ℂ} {τ s C P : ℝ} {m : ℕ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z)
    (hb : WeightedBound U s (m + 1) C Z) (v : Base) (hv : ‖v‖ ≤ 1)
    (hp : WeightedBound U s m P (fun p => fderiv ℝ φ p v)) :
    WeightedBound U s m ((1 + 2 ^ m * P) * C / τ) (amplitudeDerivative τ φ v Z) := by
  have hd := (hb.directional hU hs hZ.contDiffOn v).mono_const
    (mul_le_of_le_one_left (div_nonneg hC hs.le) hv)
  have hd' := hd.mono_const (div_le_div_of_nonneg_left hC hτ hτs)
  have hds : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v) :=
    (hφ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply (contDiff_const (c := v))
  have hc := weighted_complexify hU.uniqueDiffOn hs.le hP hds.contDiffOn hp
  have hcs := Complex.ofRealCLM.contDiff.comp hds
  have hc' := hc.const_mul hU.uniqueDiffOn hcs.contDiffOn (Complex.I / (τ : ℂ))
  have hn : ‖Complex.I / (τ : ℂ)‖ = 1 / τ := by
    simp [Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hτ.le]
  rw [hn] at hc'
  have hcm := (contDiff_const (c := Complex.I / (τ : ℂ))).mul hcs
  have hz := hc'.mul hU.uniqueDiffOn hs.le (by positivity) hC hcm.contDiffOn hZ.contDiffOn
    (hb.mono_order (Nat.le_succ m))
  have ha := hd'.add hU.uniqueDiffOn hs.le
    ((hZ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply (contDiff_const (c := v))).contDiffOn
    (hcm.mul hZ).contDiffOn hz
  convert ha using 1 <;> first | rfl | ring

lemma jetConstant_nonneg {P : ℝ} (hP : 0 ≤ P) (m r : ℕ) : 0 ≤ jetConstant P m r := by
  induction r generalizing m with
  | zero => exact zero_le_one
  | succ r ih => exact mul_nonneg (by positivity) (ih (m + 1))

/-- Output derivatives remain at the slow scale. Only the length of the jet
word contributes short-scale powers. -/
theorem weighted_amplitudeJet {U : Set Base} (hU : IsOpen U)
    {φ : Base → ℝ} {Z : Base → ℂ} {τ s C P : ℝ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z) (w : List Base)
    (hw : ∀ v ∈ w, ‖v‖ ≤ 1) (m : ℕ)
    (hb : WeightedBound U s (m + w.length) C Z)
    (hp : ∀ v ∈ w, WeightedBound U s (m + w.length) P (fun p => fderiv ℝ φ p v)) :
    WeightedBound U s m (jetConstant P m w.length * C / τ ^ w.length)
      (amplitudeJet τ φ w Z) := by
  induction w generalizing m with
  | nil => simpa only [amplitudeJet, List.length_nil, Nat.add_zero, jetConstant, one_mul, pow_zero, div_one] using hb
  | cons v w ih =>
    have hlen : m + (v :: w).length = (m + 1) + w.length := by simp; omega
    have hb' := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx)) (m + 1)
      (hlen ▸ hb) (fun x hx => hlen ▸ hp x (List.mem_cons_of_mem _ hx))
    have hd := weighted_amplitudeDerivative hU hτ hs hτs
      (div_nonneg (mul_nonneg (jetConstant_nonneg hP _ _) hC) (pow_nonneg hτ.le _)) hP
      hφ (amplitudeJet_smooth hφ hZ τ w) hb' v (hw v (List.mem_cons_self ..))
      ((hp v (List.mem_cons_self ..)).mono_order (by simp))
    convert hd using 1
    · simp only [List.length_cons, jetConstant, pow_succ]
      ring
    · rfl

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ModulatedJetDataBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform finite-order budget for all demodulated jet slots. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

lemma amplitudeBudget_ge_one {N m : ℕ} {B P : ℝ} (hB : 0 ≤ B) (hP : 0 ≤ P) :
    1 ≤ amplitudeBudget N m B P := by
  have hsum := Finset.sum_nonneg (s := Finset.range (N + 1))
    (fun r _ => jetConstant_nonneg hP m r)
  dsimp only [amplitudeBudget]
  linarith

lemma le_amplitudeBudget {N m : ℕ} {B P : ℝ} (hP : 0 ≤ P) :
    B ≤ amplitudeBudget N m B P := by
  have hsum := Finset.sum_nonneg (s := Finset.range (N + 1))
    (fun r _ => jetConstant_nonneg hP m r)
  dsimp only [amplitudeBudget]
  linarith

lemma jetConstant_le_amplitudeBudget {N m r : ℕ} {B P : ℝ}
    (hB : 0 ≤ B) (hP : 0 ≤ P) (hr : r ≤ N) :
    jetConstant P m r ≤ amplitudeBudget N m B P := by
  have h := Finset.single_le_sum (fun a _ => jetConstant_nonneg hP m a)
    (show r ∈ Finset.range (N + 1) from Finset.mem_range.mpr (by omega))
  dsimp only [amplitudeBudget]
  linarith

theorem weighted_amplitudeData {U : Set Base} (hU : IsOpen U)
    {G : Base → Space} {φ : Fin 3 → Base → ℝ} {H : DirectionFields}
    (hG : ContDiff ℝ ∞ G) (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) {τ s B P : ℝ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hB : 0 ≤ B) (hP : 0 ≤ P)
    (m N : ℕ) (hGb : WeightedBound U s (m + N) B (lowJet G))
    (hHb : ∀ j, WeightedBound U s (m + N) 1 (H j))
    (hφb : ∀ j v, WeightedBound U s (m + N) P (fun p => fderiv ℝ (φ j) p (coordinateVector v)))
    (i : Fin 4) (w : List (Fin 2)) (a : Fin 4) (hw : w.length ≤ N) :
    WeightedBound U s m (amplitudeBudget N m B P / τ ^ slotLoss i w)
      (amplitudeData G φ H τ i w a) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have hj := weighted_actual_jet hU hG hs hB m w a (hGb.mono_order (by omega))
    have hc := weighted_complexify hU.uniqueDiffOn hs.le (by positivity)
      (jet_smooth hG w a).contDiffOn hj
    apply hc.mono_const
    calc
      B / s ^ (w.length - 2) ≤ B / τ ^ (w.length - 2) :=
        div_le_div_of_nonneg_left hB (pow_pos hτ _) (pow_le_pow_left₀ hτ.le hτs _)
      _ ≤ _ := div_le_div_of_nonneg_right (le_amplitudeBudget hP) (pow_nonneg hτ.le _)
  · have hcomp := (hHb j).component hU.uniqueDiffOn hs.le zero_le_one (hH j).contDiffOn a
    have hc := weighted_amplitudeJet hU hτ hs hτs zero_le_one hP
      (hφ j) (contDiff_pi.mp (hH j) a) (w.map coordinateVector)
      (fun v hv => by
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
        exact norm_coordinateVector_le v) m
      (hcomp.mono_order (by simp only [List.length_map]; omega))
      (fun v hv => by
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
        exact (hφb j v).mono_order (by simp only [List.length_map]; omega))
    simp only [List.length_map, mul_one] at hc
    apply hc.mono_const
    exact div_le_div_of_nonneg_right (jetConstant_le_amplitudeBudget hB hP hw)
      (pow_nonneg hτ.le _)

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ConjugatedVariationBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sharp slow-scale estimates for the first three conjugated polynomial
variations. The power E+6 is independent of correction accuracy and order. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

/-- Unit amplitude bounds give the sharp exponent for every first, second,
and third variation after removing all participating phase factors. -/
theorem compact_conjugated_variation_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (m : ℕ) (B P : ℝ) (hB : 1 ≤ B) (hP : 0 ≤ P) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (φ : Fin 3 → Base → ℝ)
      (H : DirectionFields) (s τ : ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 →
      ContDiff ℝ ∞ G → (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, ContDiff ℝ ∞ (H j)) →
      Set.MapsTo (lowJet G) U K →
      WeightedBound U s (m + e.order) B (lowJet G) →
      (∀ j, WeightedBound U s (m + e.order) 1 (H j)) →
      (∀ j v, WeightedBound U s (m + e.order) P
        (fun p => fderiv ℝ (φ j) p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m (D / τ ^ (e.loss + 6))
          (fun p => conjugatedVariation e G φ H τ i (p, t)) := by
  classical
  let A := amplitudeBudget e.order m B P
  have hA : 1 ≤ A := amplitudeBudget_ge_one (zero_le_one.trans hB) hP
  have hex := fun i : Fin 3 => compact_complex_mixed_bound hU hO hK hKO (e.variations i)
    (e.variations_smoothCoeffs hO he i) m A hA
  choose D hD hb using hex
  refine ⟨∑ i, D i, Finset.sum_nonneg (fun i _ => hD i), ?_⟩
  intro G φ H s τ hτ hs hτs hs1 hG hφ hH hGK hGb hHb hφb t ht i
  have hdata := weighted_amplitudeData hU hG hφ hH hτ hs hτs (zero_le_one.trans hB) hP
    m e.order hGb hHb hφb
  have h := hb i G (amplitudeData G φ H τ) s τ hs hτ (hτs.trans hs1) hG hGK
    ((hGb.mono_order (by omega)).mono_const (le_amplitudeBudget hP))
    (fun j w a => (amplitudeData_smooth hG hφ hH τ j w a).contDiffOn)
    (fun j w a hw => hdata j w a (hw.trans (e.variations_order i))) t ht
  have hbound : D i / τ ^ (e.variations i).loss ≤ (∑ j, D j) / τ ^ (e.loss + 6) := by
    calc
      _ ≤ D i / τ ^ (e.loss + 6) := div_le_div_of_nonneg_left (hD i) (pow_pos hτ _)
        (pow_le_pow_of_le_one hτ.le (hτs.trans hs1) (e.variations_loss i))
      _ ≤ _ := div_le_div_of_nonneg_right
        (Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i)) (pow_nonneg hτ.le _)
  apply (h.mono_const hbound).congr
  intro p _
  exact conjugatedVariation_eq e G hφ hH τ i (p, t)

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ModulatedJetScaling
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scaling each oscillatory amplitude independently. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

lemma amplitudeDerivative_real_smul {Z : Base → ℂ} (hZ : ContDiff ℝ ∞ Z)
    (φ : Base → ℝ) (τ c : ℝ) (v : Base) :
    amplitudeDerivative τ φ v (fun p => c • Z p) =
      fun p => c • amplitudeDerivative τ φ v Z p := by
  funext p
  have hd := congrArg (fun L : Base →L[ℝ] ℂ => L v)
    (((hZ.differentiable (by simp) p).hasFDerivAt.const_smul c).fderiv)
  change fderiv ℝ (fun q => c • Z q) p v = c • fderiv ℝ Z p v at hd
  change fderiv ℝ (fun q => c • Z q) p v + _ = _
  rw [hd]
  simp only [amplitudeDerivative, Complex.real_smul]
  ring

lemma amplitudeJet_real_smul {φ : Base → ℝ} {Z : Base → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z) (τ c : ℝ) (w : List Base) :
    amplitudeJet τ φ w (fun p => c • Z p) = fun p => c • amplitudeJet τ φ w Z p := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    simp only [amplitudeJet, ih]
    exact amplitudeDerivative_real_smul (amplitudeJet_smooth hφ hZ τ w) φ τ c v

lemma scaleDirections_smooth {H : DirectionFields} (hH : ∀ j, ContDiff ℝ ∞ (H j))
    (c : Fin 3 → ℝ) : ∀ j, ContDiff ℝ ∞ (scaleDirections H c j) :=
  fun j => ContDiff.const_smul (c j) (hH j)

lemma amplitudeData_scale (G : Base → Space) {φ : Fin 3 → Base → ℝ}
    {H : DirectionFields} (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) (τ : ℝ) (c : Fin 3 → ℝ) :
    amplitudeData G φ (scaleDirections H c) τ =
      scaleJets (amplitudeData G φ H τ) (fun j _ => (c j : ℂ)) := by
  funext i w a p
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (scaleJets_base (amplitudeData G φ H τ) (fun j _ => (c j : ℂ)) w a p).symm
  · rw [scaleJets_succ]
    change amplitudeJet τ (φ j) (w.map coordinateVector) (fun q => c j • H j q a) p = _
    rw [amplitudeJet_real_smul (hφ j) (contDiff_pi.mp (hH j) a)]
    rfl

lemma conjugatedVariation_scale (e : Expression) (G : Base → Space)
    {φ : Fin 3 → Base → ℝ} {H : DirectionFields}
    (hφ : ∀ j, ContDiff ℝ ∞ (φ j)) (hH : ∀ j, ContDiff ℝ ∞ (H j))
    (τ : ℝ) (c : Fin 3 → ℝ) (i : Fin 3) (z : Base × ℝ) :
    conjugatedVariation e G φ (scaleDirections H c) τ i z =
      (c 0 * (if 1 ≤ i then c 1 else 1) * (if 2 ≤ i then c 2 else 1)) •
        conjugatedVariation e G φ H τ i z := by
  rw [conjugatedVariation_eq e G hφ (scaleDirections_smooth hH c),
    conjugatedVariation_eq e G hφ hH, amplitudeData_scale G hφ hH τ c]
  have h := evalComplex_scaleJets (fun j => e.variations_degree i j) G
    (amplitudeData G φ H τ) (fun j _ => (c j : ℂ)) z
  fin_cases i <;> simpa [Complex.real_smul] using h

lemma scaleDirections_inverse (H : DirectionFields) (C : Fin 3 → ℝ) (hC : ∀ j, C j ≠ 0) :
    scaleDirections (scaleDirections H (fun j => (C j)⁻¹)) C = H := by
  funext j p
  simp only [scaleDirections, smul_smul, mul_inv_cancel₀ (hC j), one_smul]

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ConjugatedMultilinearBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conjugated polynomial estimates retain the product of the input
amplitude bounds. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

/-- Product estimate corresponding to the fixed-power perturbation bound
in the small-modes argument. No output-order or accuracy dependence is
hidden in the short-scale exponent. -/
theorem compact_conjugated_multilinear_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (m : ℕ) (B P : ℝ) (hB : 1 ≤ B) (hP : 0 ≤ P) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (φ : Fin 3 → Base → ℝ)
      (H : DirectionFields) (s τ : ℝ) (C : Fin 3 → ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → (∀ j, 0 < C j) →
      ContDiff ℝ ∞ G → (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, ContDiff ℝ ∞ (H j)) →
      Set.MapsTo (lowJet G) U K →
      WeightedBound U s (m + e.order) B (lowJet G) →
      (∀ j, WeightedBound U s (m + e.order) (C j) (H j)) →
      (∀ j v, WeightedBound U s (m + e.order) P
        (fun p => fderiv ℝ (φ j) p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m
          (D * (C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)) /
            τ ^ (e.loss + 6)) (fun p => conjugatedVariation e G φ H τ i (p, t)) := by
  obtain ⟨D, hD, hb⟩ := compact_conjugated_variation_bound hU hO hK hKO e he m B P hB hP
  refine ⟨D, hD, ?_⟩
  intro G φ H s τ C hτ hs hτs hs1 hC hG hφ hH hGK hGb hHb hφb t ht i
  let V := scaleDirections H (fun j => (C j)⁻¹)
  have hV := scaleDirections_smooth hH (fun j => (C j)⁻¹)
  have hunit : ∀ j, WeightedBound U s (m + e.order) 1 (V j) := by
    intro j
    have h := (hHb j).const_smul hU.uniqueDiffOn (hH j).contDiffOn (C j)⁻¹
    change WeightedBound U s (m + e.order) 1 (fun p => (C j)⁻¹ • H j p)
    simpa only [abs_of_pos (inv_pos.mpr (hC j)),
      inv_mul_cancel₀ (ne_of_gt (hC j))] using h
  have hbound := hb G φ V s τ hτ hs hτs hs1 hG hφ hV hGK hGb hunit hφb t ht i
  let W : ℝ := C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)
  have hW : 0 < W := by
    have h₀ := hC 0
    have h₁ := hC 1
    have h₂ := hC 2
    dsimp only [W]
    split_ifs <;> positivity
  have heq : (fun p => conjugatedVariation e G φ H τ i (p, t)) =
      (fun p => W • conjugatedVariation e G φ V τ i (p, t)) := by
    funext p
    have h := conjugatedVariation_scale e G hφ hV τ C i (p, t)
    rw [scaleDirections_inverse H C (fun j => ne_of_gt (hC j))] at h
    exact h
  rw [heq]
  have hsmooth : ContDiffOn ℝ ∞ (fun p => conjugatedVariation e G φ V τ i (p, t)) U := by
    have h := evalComplex_parameter_smooth hG (fun p hp => hKO (hGK hp))
      (fun j w a => (amplitudeData_smooth hG hφ hV τ j w a).contDiffOn)
      (e := e.variations i) (e.variations_smoothCoeffs hO he i) t
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    exact conjugatedVariation_eq e G hφ hV τ i (p, t)
  have h := hbound.const_smul hU.uniqueDiffOn hsmooth W
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [abs_of_pos hW]
  ring

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPerturbationBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomial perturbations have one fixed short-scale exponent. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates MixedExpression ModulatedJets

variable {n : ℕ}

/-- The perturbation parameter enters linearly in the bound, and the single
short-scale loss works at every requested output order. -/
theorem compact_conjugated_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B Q : ℝ) (hB : 1 ≤ B) (hQ : 0 ≤ Q) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (φ : Fin 3 → Base → ℝ)
      (H : DirectionFields) (s τ ε : ℝ) (C : Fin 3 → ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → (∀ j, 0 < C j) →
      ContDiff ℝ ∞ G → (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, ContDiff ℝ ∞ (H j)) →
      Set.MapsTo (lowJet G) U K → WeightedBound U s (m + order P) B (lowJet G) →
      (∀ j, WeightedBound U s (m + order P) (C j) (H j)) →
      (∀ j v, WeightedBound U s (m + order P) Q
        (fun p => fderiv ℝ (φ j) p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m
          (D * ε * (C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)) /
            τ ^ loss P) (fun p => conjugated P ε G φ H τ i (p, t)) := by
  classical
  have hex := fun l => compact_conjugated_multilinear_bound hU hO hK hKO (P l) (hP l) m B Q hB hQ
  choose D hD hb using hex
  refine ⟨∑ l, D l, Finset.sum_nonneg (fun l _ => hD l), ?_⟩
  intro G φ H s τ ε C hτ hs hτs hs1 hε hε1 hC hG hφ hH hGK hGb hHb hφb t ht i
  let W := C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)
  have hW : 0 ≤ W := by
    have h₀ := (hC 0).le
    have h₁ := (hC 1).le
    have h₂ := (hC 2).le
    dsimp only [W]
    split_ifs <;> positivity
  have hval (l : Fin n) : WeightedBound U s m (D l * ε * W / τ ^ loss P)
      (fun p => ε ^ (l.val + 1) • conjugatedVariation (P l) G φ H τ i (p, t)) := by
    have hl : (P l).order ≤ order P := Finset.le_sup (f := fun k => (P k).order) (Finset.mem_univ l)
    have hh := hb l G φ H s τ C hτ hs hτs hs1 hC hG hφ hH hGK
      (hGb.mono_order (Nat.add_le_add_left hl m))
      (fun j => (hHb j).mono_order (Nat.add_le_add_left hl m))
      (fun j v => (hφb j v).mono_order (Nat.add_le_add_left hl m)) t ht i
    have hsmooth := conjugatedVariation_smooth (hP l) hG hφ hH hO
      (fun p hp => hKO (hGK hp)) τ i t
    have hh' : WeightedBound U s m (D l * W / τ ^ loss P)
        (fun p => conjugatedVariation (P l) G φ H τ i (p, t)) :=
      hh.mono_const (div_le_div_of_nonneg_left (mul_nonneg (hD l) hW) (pow_pos hτ _)
        (pow_le_pow_of_le_one hτ.le (hτs.trans hs1)
          (Finset.le_sup (f := fun k => (P k).loss + 6) (Finset.mem_univ l))))
    have hscaled := hh'.const_smul hU.uniqueDiffOn hsmooth (ε ^ (l.val + 1))
    apply hscaled.mono_const
    rw [abs_of_nonneg (pow_nonneg hε _)]
    have heps : ε ^ (l.val + 1) ≤ ε := by
      simpa only [pow_one] using pow_le_pow_of_le_one hε hε1 (show 1 ≤ l.val + 1 by omega)
    calc
      _ ≤ ε * (D l * W / τ ^ loss P) :=
        mul_le_mul_of_nonneg_right heps
          (div_nonneg (mul_nonneg (hD l) hW) (pow_nonneg hτ.le _))
      _ = _ := by ring
  have hsum := WeightedBound.finset_sum hU.uniqueDiffOn hs.le Finset.univ
    (fun l => D l * ε * W / τ ^ loss P)
    (fun l p => ε ^ (l.val + 1) • conjugatedVariation (P l) G φ H τ i (p, t))
    (fun l _ => (conjugatedVariation_smooth (hP l) hG hφ hH hO
      (fun p hp => hKO (hGK hp)) τ i t).const_smul _) (fun l _ => hval l)
  simpa only [conjugated, ← Finset.sum_div, ← Finset.sum_mul, W] using hsum

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedWeightedSeminorm
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPush_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted derivative bounds as actual seminorms on smooth fields
with fixed compact support, for finite derivative-loss parametrix iteration. -/
noncomputable section
open TopologicalSpace
open scoped Distributions NNReal

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma supportedWeightedSeminorm_component {K : Compacts A} (s : ℝ≥0) (m j : ℕ)
    (hj : j ≤ m) (f : SupportedField (F := F) K) :
    (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤
      supportedWeightedSeminorm K s m f := by
  let q : ℕ → Seminorm ℝ (SupportedField (F := F) K) :=
    fun j => s ^ j • ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j
  have h : q j f ≤ (Finset.range (m + 1)).sup q f :=
    Seminorm.le_finset_sup_apply (show j ∈ Finset.range (m + 1) by simpa using hj)
  simpa only [q, supportedWeightedSeminorm, smul_apply, NNReal.smul_def,
    NNReal.coe_pow, smul_eq_mul] using h

lemma weightedBound_of_supportedSeminorm {K : Compacts A} (s : ℝ≥0) (m : ℕ)
    (f : SupportedField (F := F) K) :
    WeightedBound Set.univ s m (supportedWeightedSeminorm K s m f) f := by
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  calc
    (s : ℝ) ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤
        (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f :=
      mul_le_mul_of_nonneg_left (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ)
        (pow_nonneg s.coe_nonneg _)
    _ ≤ _ := supportedWeightedSeminorm_component s m j hj f

lemma supportedSeminorm_le_of_weightedBound {K : Compacts A} {s : ℝ≥0} (hs : 0 < (s : ℝ))
    {m : ℕ} {C : ℝ} (hC : 0 ≤ C) (f : SupportedField (F := F) K)
    (hb : WeightedBound Set.univ s m C f) : supportedWeightedSeminorm K s m f ≤ C := by
  apply Seminorm.finset_sup_apply_le hC
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  change (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤ C
  have hn : ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤ C / (s : ℝ) ^ j := by
    apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (div_nonneg hC (pow_nonneg s.coe_nonneg _)) j f).2
    intro x _
    simpa only [iteratedFDerivWithin_univ] using hb.deriv_le hs hjm (Set.mem_univ x)
  calc
    _ ≤ (s : ℝ) ^ j * (C / (s : ℝ) ^ j) := mul_le_mul_of_nonneg_left hn (pow_nonneg s.coe_nonneg _)
    _ = C := by field_simp [ne_of_gt hs]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ComplexJetDecomposition
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real and imaginary parts commute with all actual ordered jets. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma complexJet_re {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H)
    (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    (complexJet H w a p).re = jet (realField H) w a p := by
  exact (congrFun (directional_clm Complex.reCLM (contDiff_pi.mp hH a)
    (w.map coordinateVector)) p).symm

lemma complexJet_im {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H)
    (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    (complexJet H w a p).im = jet (imagField H) w a p := by
  exact (congrFun (directional_clm Complex.imCLM (contDiff_pi.mp hH a)
    (w.map coordinateVector)) p).symm

lemma complexJet_decompose {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H)
    (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    complexJet H w a p = (jet (realField H) w a p : ℂ) +
      Complex.I * (jet (imagField H) w a p : ℂ) := by
  rw [← complexJet_re hH, ← complexJet_im hH]
  exact Complex.ext (by simp) (by simp)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ComplexFirstVariation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complex polynomial first variation is exactly the complexification
of the actual real differential. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

lemma evalComplex_sumList {ι : Type*} (l : List ι) (f : ι → MixedExpression)
    (G : Base → Space) (J : JetData) (z : Base × ℝ) :
    (sumList l f).evalComplex G J z = (l.map (fun i => (f i).evalComplex G J z)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [sumList, evalComplex, List.map_cons, List.sum_cons, ih]

lemma evalComplex_ofExpression (e : Expression) (G : Base → Space)
    (H : Base → Fin 4 → ℂ) (z : Base × ℝ) :
    (ofExpression e).evalComplex G (complexDirectionData G H) z = (e.eval G z : ℂ) := by
  induction e with
  | coeff c => rfl
  | atom w a e ih => simp only [ofExpression, evalComplex, complexDirectionData, Fin.cases_zero,
      ih, Expression.eval, Complex.ofReal_mul]
  | add e f ihe ihf => simp only [ofExpression, evalComplex, ihe, ihf, Expression.eval, Complex.ofReal_add]

lemma complex_coefficient_variation (c : LowJet × ℝ → ℝ) (G : Base → Space)
    (H : Base → Fin 4 → ℂ) (z : Base × ℝ) :
    ((coeff c).differentiate 0).evalComplex G (complexDirectionData G H) z =
      ∑ i : Fin 7 × Fin 4, complexJet H (lowWord i.1) i.2 z.1 *
        (coefficientDerivative c i (lowJet G z.1, z.2) : ℂ) := by
  simp only [differentiate, evalComplex_sumList, evalComplex, complexDirectionData,
    Fin.cases_succ, ↓reduceIte]
  exact Finset.sum_map_toList _ _

private lemma complex_sum_decompose {ι : Type*} [Fintype ι] (a b d : ι → ℝ) :
    (∑ i, ((a i : ℂ) + Complex.I * (b i : ℂ)) * (d i : ℂ)) =
      (∑ i, a i * d i : ℝ) + Complex.I * (∑ i, b i * d i : ℝ) := by
  simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum]

/-- This identity identifies the algebraic complex evaluation with the
actual real differential on the real and imaginary parts separately. -/
theorem complex_first_variation (e : Expression) (G : Base → Space)
    {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (z : Base × ℝ) :
    ((ofExpression e).differentiate 0).evalComplex G (complexDirectionData G H) z =
      (e.variation G (realField H) z : ℂ) +
        Complex.I * (e.variation G (imagField H) z : ℂ) := by
  induction e with
  | coeff c =>
    rw [ofExpression, complex_coefficient_variation]
    simp_rw [complexJet_decompose hH]
    rw [complex_sum_decompose]
    rw [Expression.variation, Expression.variation,
      coefficient_variation_sum, coefficient_variation_sum]
    rfl
  | atom w a e ih =>
    simp only [ofExpression, differentiate, ↓reduceIte, evalComplex,
      complexDirectionData, Fin.cases_zero, Fin.cases_succ, evalComplex_ofExpression, ih,
      Expression.variation]
    rw [complexJet_decompose hH]
    push_cast
    ring
  | add e f ihe ihf =>
    simp only [ofExpression, differentiate, evalComplex, ihe, ihf, Expression.variation,
      Complex.ofReal_add]
    ring

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ComplexifiedPolynomialOperator
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complexification of the actual supported polynomial linearization. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

namespace Expression

/-- The bundled operator is the same complex first variation whose
conjugated finite-jet estimates were proved above. -/
lemma complexVariationLM_apply {O : Set LowJet} {U : Set Base} {G : Base → Space} {e : Expression}
    (hO : IsOpen O) (hU : IsOpen U) (he : e.SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) (t : ℝ)
    (H : SupportedField (F := Fin 4 → ℂ) K) (p : Base) :
    complexVariationLM hO hU he hG hQ K hKU t H p =
      ((ofExpression e).differentiate 0).evalComplex G (complexDirectionData G H) (p, t) := by
  change (e.variation G (realField H) (p, t) : ℂ) +
    Complex.I * (e.variation G (imagField H) (p, t) : ℂ) = _
  exact (complex_first_variation e G H.contDiff (p, t)).symm

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ConjugatedPolynomialOperator
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The oscillatory estimates apply to the actual conjugated polynomial
linearization on supported smooth fields. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

lemma singlePhase_smooth {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ∀ i, ContDiff ℝ ∞ (singlePhase φ i) := by
  intro i
  fin_cases i
  · exact hφ
  · exact contDiff_const
  · exact contDiff_const

lemma singleDirection_smooth {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) :
    ∀ i, ContDiff ℝ ∞ (singleDirection H i) := by
  intro i
  fin_cases i
  · exact hH
  · exact contDiff_const
  · exact contDiff_const

lemma single_oscillatoryData (G : Base → Space) (φ : Base → ℝ) (H : Base → Fin 4 → ℂ) (τ : ℝ) :
    oscillatoryData G (singlePhase φ) (singleDirection H) τ =
      complexDirectionData G (fun p => phase τ φ p • H p) := by
  funext i w a p
  fin_cases i
  · rfl
  · rfl
  · change iteratedDirectional (w.map coordinateVector)
      (fun q => phase τ (fun _ => 0) q * (0 : ℂ)) p = 0
    simp only [mul_zero, iteratedDirectional_zero]
  · change iteratedDirectional (w.map coordinateVector)
      (fun q => phase τ (fun _ => 0) q * (0 : ℂ)) p = 0
    simp only [mul_zero, iteratedDirectional_zero]

namespace Expression

lemma conjugatedVariationLM_apply {O : Set LowJet} {U : Set Base} {G : Base → Space} {e : Expression}
    (hO : IsOpen O) (hU : IsOpen U) (he : e.SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {φ : Base → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (τ t : ℝ) (H : SupportedField (F := Fin 4 → ℂ) K) (p : Base) :
    conjugatedVariationLM hO hU he hG hQ K hKU hφ τ t H p =
      conjugatedVariation e G (singlePhase φ) (singleDirection H) τ 0 (p, t) := by
  change phase τ (fun q => -φ q) p *
    complexVariationLM hO hU he hG hQ K hKU t (phaseLM K hφ τ H) p = _
  rw [complexVariationLM_apply, phase_neg_inv]
  change (phase τ φ p)⁻¹ * ((ofExpression e).differentiate 0).evalComplex G
    (complexDirectionData G (fun q => phase τ φ q • H q)) (p, t) = _
  rw [← single_oscillatoryData]
  simp only [conjugatedVariation, phaseProduct, singlePhase, Matrix.cons_val_zero]
  simp only [show ¬ (1 : Fin 3) ≤ 0 by decide, show ¬ (2 : Fin 3) ≤ 0 by decide,
    ↓reduceIte, mul_one]
  rfl

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ConjugatedOperatorBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-loss conjugated estimate for the actual supported linear map. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

lemma supportedField_eq_zero_of_seminorm_eq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {K : Compacts Base} (s : ℝ≥0) (m : ℕ)
    {f : SupportedField (F := F) K} (hf : supportedWeightedSeminorm K s m f = 0) : f = 0 := by
  apply DFunLike.ext
  intro p
  have h := (weightedBound_of_supportedSeminorm s m f).norm_le (Set.mem_univ p)
  rw [hf] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SupportedTupleOperators
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite tuples of supported linear operators, with actual weighted
seminorm bounds. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A F E ι : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [AddCommGroup E] [Module ℝ E]
  [Fintype ι]

lemma supportedWeightedSeminorm_mono {K : Compacts A} (s : ℝ≥0) {m r : ℕ} (hmr : m ≤ r)
    (f : SupportedField (F := F) K) :
    supportedWeightedSeminorm K s m f ≤ supportedWeightedSeminorm K s r f := by
  apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact supportedWeightedSeminorm_component s r j (hjm.trans hmr) f

lemma tupleSupportedLM_bound (K : Compacts A) (L : ι → E →ₗ[ℝ] SupportedField (F := F) K)
    {s : ℝ≥0} (hs : 0 < (s : ℝ)) (m : ℕ) (z : E) :
    supportedWeightedSeminorm K s m (tupleSupportedLM K L z) ≤
      ∑ i, supportedWeightedSeminorm K s m (L i z) := by
  have hn : 0 ≤ ∑ i, supportedWeightedSeminorm K s m (L i z) :=
    Finset.sum_nonneg fun i _ => apply_nonneg _ _
  apply supportedSeminorm_le_of_weightedBound hs hn
  apply WeightedBound.pi uniqueDiffOn_univ hs hn
  · intro i
    exact (L i z).contDiff.contDiffOn
  · intro i
    exact (weightedBound_of_supportedSeminorm s m (L i z)).mono_const
      (Finset.single_le_sum (f := fun j => supportedWeightedSeminorm K s m (L j z))
        (fun j _ => apply_nonneg _ _) (Finset.mem_univ i))

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPerturbationOperator
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPush_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conjugated derivative of the actual finite polynomial perturbation,
with its fixed scale loss and linear dependence on epsilon. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates ModulatedJets

variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

lemma conjugatedLM_apply (hO : IsOpen O) (hU : IsOpen U) (P : Fin n → Expression)
    (hP : ∀ l, (P l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε t : ℝ)
    (H : SupportedField (F := Fin 4 → ℂ) K) (p : Base) :
    conjugatedLM hO hU P hP hG hQ K hKU hφ τ ε t H p =
      conjugated P ε G (singlePhase φ) (singleDirection H) τ 0 (p, t) := by
  simp only [conjugatedLM, LinearMap.sum_apply, LinearMap.smul_apply]
  have hsum := congrArg (fun f : Base → ℂ => f p)
    (map_sum (FunLike.coeAddMonoidHom (SupportedField (F := ℂ) K) Base ℂ)
      (fun l : Fin n => ε ^ (l.val + 1) •
        (P l).conjugatedVariationLM hO hU (hP l) hG hQ K hKU hφ τ t H) Finset.univ)
  simp only [FunLike.coeAddMonoidHom_apply, Finset.sum_apply] at hsum
  rw [hsum]
  simp only [smul_apply, Expression.conjugatedVariationLM_apply, conjugated]

theorem conjugatedLM_bound {Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQcompact : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (m : ℕ) (B R : ℝ) (hB : 1 ≤ B) (hR : 0 ≤ R) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ)
      (hGQ : Set.MapsTo (lowJet G) U Q) (s : ℝ≥0) (τ ε : ℝ),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      WeightedBound U s (m + order P) B (lowJet G) →
      (∀ v, WeightedBound U s (m + order P) R
        (fun p => fderiv ℝ φ p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ H : SupportedField (F := Fin 4 → ℂ) K,
        supportedWeightedSeminorm K s m
          (conjugatedLM hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ ε t H) ≤
        D * ε / τ ^ loss P * supportedWeightedSeminorm K s (m + order P) H := by
  obtain ⟨D, hD, hd⟩ := compact_conjugated_bound hU hO hQcompact hQO P hP m B R hB hR
  refine ⟨D, hD, ?_⟩
  intro G φ hG hφ hGQ s τ ε hτ hs hτs hs1 hε hε1 hGb hφb t ht H
  let C := supportedWeightedSeminorm K s (m + order P) H
  have hC : 0 ≤ C := apply_nonneg _ _
  by_cases hC0 : C = 0
  · have hH0 : H = 0 := supportedField_eq_zero_of_seminorm_eq_zero s (m + order P) hC0
    simp only [hH0, map_zero, mul_zero, le_refl]
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have hCs : ∀ j : Fin 3, 0 < (![C, 1, 1] j) := by
      intro j
      fin_cases j <;> simp [hCpos]
    have hHb : ∀ j, WeightedBound U s (m + order P) (![C, 1, 1] j) (singleDirection H j) := by
      intro j
      fin_cases j
      · exact (weightedBound_of_supportedSeminorm s (m + order P) H).restrict_open hU
      · exact (weightedBound_zero U s (m + order P)).mono_const zero_le_one
      · exact (weightedBound_zero U s (m + order P)).mono_const zero_le_one
    have hΦb : ∀ j v, WeightedBound U s (m + order P) R
        (fun p => fderiv ℝ (singlePhase φ j) p (coordinateVector v)) := by
      intro j v
      fin_cases j
      · exact hφb v
      · change WeightedBound U s (m + order P) R
          (fun p => fderiv ℝ (fun _ : Base => (0 : ℝ)) p (coordinateVector v))
        simpa only [fderiv_fun_const, Pi.zero_apply, zero_apply] using
          (weightedBound_zero U s (m + order P) (F := ℝ)).mono_const hR
      · change WeightedBound U s (m + order P) R
          (fun p => fderiv ℝ (fun _ : Base => (0 : ℝ)) p (coordinateVector v))
        simpa only [fderiv_fun_const, Pi.zero_apply, zero_apply] using
          (weightedBound_zero U s (m + order P) (F := ℝ)).mono_const hR
    have hv := hd G (singlePhase φ) (singleDirection H) s τ ε ![C, 1, 1]
      hτ hs hτs hs1 hε hε1 hCs hG (singlePhase_smooth hφ) (singleDirection_smooth H.contDiff)
      hGQ hGb hHb hΦb t ht 0
    have hl : WeightedBound U s m (D * ε * C / τ ^ loss P)
        (conjugatedLM hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ ε t H) := by
      apply (show WeightedBound U s m (D * ε * C / τ ^ loss P)
        (fun p => conjugated P ε G (singlePhase φ) (singleDirection H) τ 0 (p, t)) by
          simpa using hv).congr
      intro p _
      exact conjugatedLM_apply hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ ε t H p
    have hg := hl.extend_support hU
      ((conjugatedLM hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ ε t H).tsupport_subset.trans hKU)
      (by positivity)
    have hn := supportedSeminorm_le_of_weightedBound hs
      (show 0 ≤ D * ε * C / τ ^ loss P by positivity)
      (conjugatedLM hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ ε t H) hg
    convert hn using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [C]
    ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorPerturbationOperator
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor-valued polynomial perturbations inherit one fixed derivative
budget and one fixed short-scale exponent from their three components. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

theorem tensorConjugatedLM_bound {Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQcompact : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ i l, (P i l).SmoothCoeffs O) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (m : ℕ) (B R : ℝ) (hB : 1 ≤ B) (hR : 0 ≤ R) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ)
      (hGQ : Set.MapsTo (lowJet G) U Q) (s : ℝ≥0) (τ ε : ℝ),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      WeightedBound U s (m + tensorOrder P) B (lowJet G) →
      (∀ v, WeightedBound U s (m + tensorOrder P) R
        (fun p => fderiv ℝ φ p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ H : SupportedField (F := Fin 4 → ℂ) K,
        supportedWeightedSeminorm K s m
          (tensorConjugatedLM hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ ε t H) ≤
        D * ε / τ ^ tensorLoss P * supportedWeightedSeminorm K s (m + tensorOrder P) H := by
  classical
  have hex := fun i => conjugatedLM_bound hU hO hQcompact hQO (P i) (hP i) K hKU m B R hB hR
  choose D hD hd using hex
  refine ⟨∑ i, D i, Finset.sum_nonneg (fun i _ => hD i), ?_⟩
  intro G φ hG hφ hGQ s τ ε hτ hs hτs hs1 hε hε1 hGb hφb t ht H
  have hiOrder (i : Fin 3) : order (P i) ≤ tensorOrder P :=
    Finset.le_sup (f := fun j => order (P j)) (Finset.mem_univ i)
  have hiLoss (i : Fin 3) : loss (P i) ≤ tensorLoss P :=
    Finset.le_sup (f := fun j => loss (P j)) (Finset.mem_univ i)
  calc
    _ ≤ ∑ i, supportedWeightedSeminorm K s m
        (conjugatedLM hO hU (P i) (hP i) hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ ε t H) :=
      tupleSupportedLM_bound K _ hs m H
    _ ≤ ∑ i, D i * ε / τ ^ tensorLoss P * supportedWeightedSeminorm K s (m + tensorOrder P) H := by
      apply Finset.sum_le_sum
      intro i _
      have hv := hd i G φ hG hφ hGQ s τ ε hτ hs hτs hs1 hε hε1
        (hGb.mono_order (Nat.add_le_add_left (hiOrder i) m))
        (fun v => (hφb v).mono_order (Nat.add_le_add_left (hiOrder i) m)) t ht H
      apply hv.trans
      apply mul_le_mul
      · exact div_le_div_of_nonneg_left (mul_nonneg (hD i) hε) (pow_pos hτ _)
          (pow_le_pow_of_le_one hτ.le (hτs.trans hs1) (hiLoss i))
      · exact supportedWeightedSeminorm_mono s (Nat.add_le_add_left (hiOrder i) m) H
      · exact apply_nonneg _ _
      · exact div_nonneg (mul_nonneg (hD i) hε) (pow_nonneg hτ.le _)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_div, ← Finset.sum_mul]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedCoordinateChange
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isometric linear coordinate changes preserve the supported weighted
seminorms exactly. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A B F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma supportedCoordinateEquiv_norm (e : A ≃ₗᵢ[ℝ] B) (K : Compacts A)
    {s : ℝ≥0} (hs : 0 < (s : ℝ)) (m : ℕ) (f : SupportedField (F := F) K) :
    supportedWeightedSeminorm (K.map e e.continuous) s m (supportedCoordinateEquiv e K f) =
      supportedWeightedSeminorm K s m f := by
  apply le_antisymm
  · apply supportedSeminorm_le_of_weightedBound hs (apply_nonneg _ _)
    exact weightedBound_comp_isometry e.symm f.contDiff (weightedBound_of_supportedSeminorm s m f)
  · have hb := weightedBound_comp_isometry e (supportedCoordinateEquiv e K f).contDiff
      (weightedBound_of_supportedSeminorm s m (supportedCoordinateEquiv e K f))
    have hid : (supportedCoordinateEquiv e K f : B → F) ∘ e = (f : A → F) := by
      funext x
      change f (e.symm (e x)) = f x
      rw [e.symm_apply_apply]
    rw [hid] at hb
    exact supportedSeminorm_le_of_weightedBound hs (apply_nonneg _ _) f hb

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SupportedOperatorTransport
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of differential operators through a fixed isometric coordinate
change, including their finite derivative-loss estimates. -/
noncomputable section
open TopologicalSpace
open scoped NNReal

namespace ClosedSurfaceR4.JetPolynomial

variable {A B F G : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma transportSupportedLM_bound (e : A ≃ₗᵢ[ℝ] B) (K : Compacts A)
    (L : SupportedField (F := F) K →ₗ[ℝ] SupportedField (F := G) K)
    {s : ℝ≥0} (hs : 0 < (s : ℝ)) (m r : ℕ) (C : ℝ)
    (hL : ∀ f, supportedWeightedSeminorm K s m (L f) ≤ C * supportedWeightedSeminorm K s r f)
    (f : SupportedField (F := F) (K.map e e.continuous)) :
    supportedWeightedSeminorm (K.map e e.continuous) s m (transportSupportedLM e K L f) ≤
      C * supportedWeightedSeminorm (K.map e e.continuous) s r f := by
  change supportedWeightedSeminorm (K.map e e.continuous) s m
    (supportedCoordinateEquiv e K (L ((supportedCoordinateEquiv e K).symm f))) ≤ _
  rw [supportedCoordinateEquiv_norm e K hs]
  calc
    _ ≤ C * supportedWeightedSeminorm K s r ((supportedCoordinateEquiv e K).symm f) := hL _
    _ = _ := by
      have he := supportedCoordinateEquiv_norm e K hs r ((supportedCoordinateEquiv e K).symm f)
      rw [LinearEquiv.apply_symm_apply] at he
      rw [he]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedChartEquiv
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Invertible local-chart transport on supported fields and their linear
operators. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A B F : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma chartPull_bound (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e e.source) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) {s : ℝ≥0} {J : ℝ} {m : ℕ}
    (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1) (hJ : 1 ≤ J)
    (hderiv : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J)
    (f : SupportedField (F := F) (chartSupport e K hK)) :
    supportedWeightedSeminorm K s m (chartPull e he K hK f) ≤
      (m.factorial : ℝ) * supportedWeightedSeminorm (chartSupport e K hK) s m f * J ^ m := by
  have hf := (weightedBound_of_supportedSeminorm s m f).restrict_open e.open_target
  have hb := hf.comp_coordinates e.open_source.uniqueDiffOn e.open_target.uniqueDiffOn hs hs1 hJ
    (apply_nonneg _ _) he f.contDiff.contDiffOn (fun _ hx => e.map_source hx) hderiv
  apply supportedSeminorm_le_of_weightedBound hs (by positivity)
  exact hb.indicator_of_support e.open_source K.isCompact.isClosed hK (by positivity)
    (chartPull_zero e K hK f)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorChartBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted estimates for tensor transport through phase charts. The
change of chart changes constants but introduces no scale loss. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates PhaseMean

variable (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (K : Compacts SmallModes.Base) (hK : (K : Set SmallModes.Base) ⊆ e.source)

lemma tensorChartBudget_nonneg (m : ℕ) {J D : ℝ} (hJ : 0 ≤ J) (hD : 0 ≤ D) :
    0 ≤ tensorChartBudget m J D := by unfold tensorChartBudget; positivity

lemma tensorChartPush_bound (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {s : ℝ≥0} {J D : ℝ} {m : ℕ} (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1)
    (hJ : 1 ≤ J) (hD : 0 ≤ D)
    (hderiv : ∀ j, 1 ≤ j → j ≤ m → ∀ y ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target y‖ ≤ J)
    (hfield : ∀ v, ‖v‖ ≤ 1 → WeightedBound e.target s m D
      (SmallModes.coordDeriv v e.symm)) (f : SupportedField (F := ComplexTensor) K) :
    supportedWeightedSeminorm (chartSupport e K hK) s m (tensorChartPush e hi K hK f) ≤
      tensorChartBudget m J D * supportedWeightedSeminorm K s m f := by
  have hN : 0 ≤ supportedWeightedSeminorm K s m f := apply_nonneg _ _
  have hb := ((weightedBound_of_supportedSeminorm s m f).restrict_open e.open_source).comp_coordinates
    e.open_target.uniqueDiffOn e.open_source.uniqueDiffOn hs hs1 hJ hN hi
    f.contDiff.contDiffOn (fun _ hy => e.map_target hy) hderiv
  have ht := weighted_complexPullbackField_apply e.open_target hs (by positivity) hD
    (f.contDiff.comp_contDiffOn hi) hi hb hfield
  have hg := ht.indicator_of_support e.open_target (chartSupport e K hK).isCompact.isClosed
    (chartSupport_subset e K hK) (by positivity) (tensorChartPush_zero e K hK f)
  apply supportedSeminorm_le_of_weightedBound hs
    (mul_nonneg (tensorChartBudget_nonneg m (zero_le_one.trans hJ) hD) hN)
  convert hg using 1 <;> first | rfl | (unfold tensorChartBudget; ring)

lemma chartTensorTransportLM_bound (he : ContDiffOn ℝ ∞ e e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (R : SupportedField (F := Fin 4 → ℂ) K →ₗ[ℝ] SupportedField (F := ComplexTensor) K)
    {s : ℝ≥0} {J I D C : ℝ} {m r : ℕ} (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1)
    (hJ : 1 ≤ J) (hI : 1 ≤ I) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hebound : ∀ j, 1 ≤ j → j ≤ r → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J)
    (hibound : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target x‖ ≤ I)
    (hfield : ∀ v, ‖v‖ ≤ 1 → WeightedBound e.target s m D
      (SmallModes.coordDeriv v e.symm))
    (hR : ∀ f, supportedWeightedSeminorm K s m (R f) ≤ C * supportedWeightedSeminorm K s r f)
    (f : SupportedField (F := Fin 4 → ℂ) (chartSupport e K hK)) :
    supportedWeightedSeminorm (chartSupport e K hK) s m (chartTensorTransportLM e K hK he hi R f) ≤
      (tensorChartBudget m I D * C * ((r.factorial : ℝ) * J ^ r)) *
        supportedWeightedSeminorm (chartSupport e K hK) s r f := by
  have hbudget := tensorChartBudget_nonneg m (zero_le_one.trans hI) hD
  have hpush := tensorChartPush_bound e K hK hi hs hs1 hI hD hibound hfield (R (chartPull e he K hK f))
  have hpull := chartPull_bound e he K hK hs hs1 hJ hebound f
  change supportedWeightedSeminorm _ s m (tensorChartPush e hi K hK (R (chartPull e he K hK f))) ≤ _
  calc
    _ ≤ tensorChartBudget m I D * (C * supportedWeightedSeminorm K s r (chartPull e he K hK f)) :=
      hpush.trans (mul_le_mul_of_nonneg_left (hR _) hbudget)
    _ ≤ tensorChartBudget m I D * (C * ((r.factorial : ℝ) *
        supportedWeightedSeminorm (chartSupport e K hK) s r f * J ^ r)) := by gcongr
    _ = _ := by ring

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ArbitraryPhasePolynomial
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorOrder_emptyMetricPolynomial _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial conjugation estimate and its real realization for an
arbitrary smooth phase, before changing to a first-coordinate chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates ModulatedJets

variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

theorem phaseCoordinatePolynomialOperator_bounds {Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (B F : ℕ → ℝ) (hB : ∀ m, 1 ≤ B m) (hF : ∀ m, 0 ≤ F m) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ)
      (hGQ : Set.MapsTo (lowJet G) U Q) (s : ℝ≥0) (τ ε : ℝ),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      (∀ m, WeightedBound U s (m + tensorOrder P) (B m) (lowJet G)) →
      (∀ m v, WeightedBound U s (m + tensorOrder P) (F m)
        (fun p => fderiv ℝ φ p (coordinateVector v))) →
      ∀ m Z, supportedWeightedSeminorm (modeSupport K) s m
        (phaseCoordinatePolynomialOperator hO hU P hP hG (fun _ hp => hQO (hGQ hp))
          K hKU hφ τ ε Z) ≤
        ε / τ ^ tensorLoss P * D m * supportedWeightedSeminorm (modeSupport K) s (m + tensorOrder P) Z := by
  have hex (m : ℕ) := tensorConjugatedLM_bound hU hO hQ hQO P hP K hKU m (B m) (F m) (hB m) (hF m)
  choose D hD hd using hex
  refine ⟨D,hD,?_⟩
  intro G φ hG hφ hGQ s τ ε hτ hs hτs hs1 hε hε1 hGb hφb m Z
  have hl := hd m G φ hG hφ hGQ s τ ε hτ hs hτs hs1 hε hε1
    (hGb m) (hφb m) 0 (by simp)
  have ht := transportSupportedLM_bound planeCoordinateIsometry K
    (tensorConjugatedLM hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ ε 0)
    hs m (m + tensorOrder P) (D m * ε / τ ^ tensorLoss P) hl Z
  change supportedWeightedSeminorm _ s m (transportSupportedLM planeCoordinateIsometry K _ Z) ≤ _
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseChartBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local phase-coordinate polynomial operator keeps the original
fixed scale exponent and derivative loss. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

variable {n : ℕ} {U : Set Base} {O Q : Set LowJet}

theorem phaseChartPolynomialOperator_bounds
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source)
    (B F J I : ℕ → ℝ) (hB : ∀ m, 1 ≤ B m) (hF : ∀ m, 0 ≤ F m)
    (hJ : ∀ m, 1 ≤ J m) (hI : ∀ m, 1 ≤ I m)
    (hebound : ∀ m j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J m)
    (hibound : ∀ m j, 1 ≤ j → j ≤ m + 1 → ∀ x ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target x‖ ≤ I m) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ)
      (hGQ : Set.MapsTo (lowJet G) U Q) (s : ℝ≥0) (τ ε : ℝ),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      (∀ m, WeightedBound U s (m + tensorOrder P) (B m) (lowJet G)) →
      (∀ m v, WeightedBound U s (m + tensorOrder P) (F m)
        (fun p => fderiv ℝ φ p (coordinateVector v))) →
      ∀ m Z, supportedWeightedSeminorm (chartSupport e (modeSupport K) hKe) s m
        (phaseChartPolynomialOperator hO hU P hP hG (fun _ hp => hQO (hGQ hp))
          K hKU hφ τ ε e he hi hKe Z) ≤
        ε / τ ^ tensorLoss P * D m *
          supportedWeightedSeminorm (chartSupport e (modeSupport K) hKe) s (m + tensorOrder P) Z := by
  obtain ⟨D,hD,hd⟩ := phaseCoordinatePolynomialOperator_bounds hU hO hQ hQO P hP K hKU B F hB hF
  let E := fun m => tensorChartBudget m (I m) (I m) * D m *
    (((m + tensorOrder P).factorial : ℝ) * J (m + tensorOrder P) ^ (m + tensorOrder P))
  have hI0 (m : ℕ) : 0 ≤ I m := zero_le_one.trans (hI m)
  have hJ0 (m : ℕ) : 0 ≤ J m := zero_le_one.trans (hJ m)
  refine ⟨E,fun m => mul_nonneg (mul_nonneg (tensorChartBudget_nonneg m (hI0 m) (hI0 m)) (hD m))
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hJ0 _) _)),?_⟩
  intro G φ hG hφ hGQ s τ ε hτ hs hτs hs1 hε hε1 hGb hφb m Z
  have hDm := hD m
  have hR := hd G φ hG hφ hGQ s τ ε hτ hs hτs hs1 hε hε1 hGb hφb m
  have hfield := RealModes.weighted_coordDeriv_of_jets e.open_target hi s.coe_nonneg hs1
    (hI0 m) (hibound m)
  have hb := chartTensorTransportLM_bound e (modeSupport K) hKe he hi
    (phaseCoordinatePolynomialOperator hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ ε)
    hs hs1 (hJ (m + tensorOrder P)) (hI m) (hI0 m) (by positivity)
    (hebound (m + tensorOrder P))
    (fun j hj hjm => hibound m j hj (hjm.trans (Nat.le_succ m))) hfield hR Z
  change supportedWeightedSeminorm _ s m (chartTensorTransportLM e (modeSupport K) hKe he hi _ Z) ≤ _
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [E]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactLocalBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform slow-scale bounds on a relatively compact coordinate domain. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_local_weighted_bound {V Ω K : Set E}
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hVK : V ⊆ K) (hKΩ : K ⊆ Ω) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f Ω) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 → WeightedBound V s m C f := by
  obtain ⟨C,hC,hb⟩ := compact_coefficient_bound hΩ.uniqueDiffOn hK hKΩ hf m
  refine ⟨C,hC,?_⟩
  intro s hs hs1 j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hV hx]
  have hh := hb j hj x (hVK hx)
  rw [iteratedFDerivWithin_of_isOpen j hΩ (hKΩ (hVK hx))] at hh
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs hs1)).trans hh

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformRealModeCoefficients
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform reconstruction estimates on a fixed compact set of real two-jets. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SmallModes
open RealModes WeightedEstimates

lemma admissibleComplexJets_domain : LowJet.Domain admissibleComplexJets := by
  refine ⟨?_,fun _ h => h.1,fun _ h => h.2⟩
  apply isOpen_iff_mem_nhds.mpr
  intro J hJ
  have hs (i : Fin 5) : ContDiffAt ℝ ∞ (fun K : TwoJet 4 => K i) J :=
    (ContinuousLinearMap.proj i : TwoJet 4 →L[ℝ] Ambient 4).contDiff.contDiffAt
  have hd := LowJet.contDiffAt_gramDet (hs 0) (hs 1)
  have hn := LowJet.contDiffAt_normalPart (hs 0) (hs 1) (hs 4) hJ.1
  exact (hd.continuousAt.eventually_ne hJ.1).and
    ((LowJet.contDiffAt_dot hn hn).continuousAt.eventually_ne hJ.2)

lemma complexifyJet_mem {J : RealTwoJet}
    (hD : NormalFrame.gramDet (J 0) (J 1) ≠ 0)
    (hB : realNormalPart (J 0) (J 1) (J 4) ≠ 0) :
    complexifyJetCLM J ∈ admissibleComplexJets := by
  constructor
  · change gramDet (complexify (J 0)) (complexify (J 1)) ≠ 0
    rw [complexify_gram]
    exact Complex.ofReal_ne_zero.mpr hD
  · change normalPart (complexify (J 0)) (complexify (J 1)) (complexify (J 4)) ⬝ᵥ
      normalPart (complexify (J 0)) (complexify (J 1)) (complexify (J 4)) ≠ 0
    rw [← complexify_normalPart,complexify_dot]
    exact Complex.ofReal_ne_zero.mpr ((dotProduct_self_eq_zero).not.mpr hB)

lemma twoJet_complexify {F : RField 4} (hF : ContDiff ℝ ∞ F) :
    twoJet (fun p => complexify (F p)) = complexifyJetCLM ∘ realTwoJet F := by
  have hfirst (v : Base) : coordDeriv v (fun p => complexify (F p)) =
      fun p => complexify (coordDeriv v F p) := by
    funext p
    exact coordDeriv_complexify (hF.differentiable (by simp) p) v
  have hsecond (v w : Base) : coordDeriv v (fun p => complexify (coordDeriv w F p)) =
      fun p => complexify (coordDeriv v (coordDeriv w F) p) := by
    funext p
    exact coordDeriv_complexify ((contDiff_real_coordDeriv hF w).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p) v
  funext p i
  fin_cases i
  · change coordDeriv dx (fun p => complexify (F p)) p = complexify (coordDeriv dx F p)
    exact congrFun (hfirst dx) p
  · change coordDeriv dy (fun p => complexify (F p)) p = complexify (coordDeriv dy F p)
    exact congrFun (hfirst dy) p
  · change coordDeriv dx (coordDeriv dx (fun p => complexify (F p))) p =
      complexify (coordDeriv dx (coordDeriv dx F) p)
    rw [hfirst dx]
    exact congrFun (hsecond dx dx) p
  · change coordDeriv dx (coordDeriv dy (fun p => complexify (F p))) p =
      complexify (coordDeriv dx (coordDeriv dy F) p)
    rw [hfirst dy]
    exact congrFun (hsecond dx dy) p
  · change coordDeriv dy (coordDeriv dy (fun p => complexify (F p))) p =
      complexify (coordDeriv dy (coordDeriv dy F) p)
    rw [hfirst dy]
    exact congrFun (hsecond dy dy) p

/-- The constant precedes the map and scale. Its only geometric input is a
fixed compact set of admissible real two-jets; higher bounds enter polynomially. -/
theorem compact_real_reconstruction_bounds {U : Set Base} (hU : IsOpen U)
    {Ω K : Set RealTwoJet} (hΩ : RealJetDomain Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (F : RField 4) (s C : ℝ), 0 < s → 1 ≤ C →
      ContDiff ℝ ∞ F → MapsTo (realTwoJet F) U K →
      WeightedBound U s m C (realTwoJet F) →
      ReconstructionCoefficientBound (fun p => complexify (F p)) U s m
        ((m.factorial : ℝ) * D * C^m) := by
  have hKc : IsCompact (complexifyJetCLM '' K) := hK.image complexifyJetCLM.continuous
  have hKo : complexifyJetCLM '' K ⊆ admissibleComplexJets := by
    rintro _ ⟨J,hJ,rfl⟩
    exact complexifyJet_mem (hΩ.determinant J (hKΩ hJ)) (hΩ.good J (hKΩ hJ))
  obtain ⟨D,hD,hd⟩ := compact_reconstructionCoefficientBound hU
    admissibleComplexJets_domain hKc hKo m
  refine ⟨D,hD,?_⟩
  intro F s C hs hC hF hFK hb
  apply hd (fun p => complexify (F p)) s C hs hC (contDiff_complexify hF).contDiffOn
  · intro p hp
    rw [twoJet_complexify hF]
    exact mem_image_of_mem complexifyJetCLM (hFK hp)
  · rw [twoJet_complexify hF]
    exact weighted_linearIsometry hU.uniqueDiffOn (contDiff_realTwoJet hF).contDiffOn hb complexifyJetLI

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactRealJetNeighborhood
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed compact admissible jet neighborhoods for nearby immersed maps. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

lemma admissibleRealJets_domain : RealJetDomain admissibleRealJets := by
  refine ⟨?_,fun _ h => h.1,fun _ h => h.2⟩
  apply isOpen_iff_mem_nhds.mpr
  intro J hJ
  have hs (i : Fin 5) : ContDiffAt ℝ ∞ (fun K : RealTwoJet => K i) J :=
    (ContinuousLinearMap.proj i : RealTwoJet →L[ℝ] RVec 4).contDiff.contDiffAt
  have hd : Continuous (fun K : RealTwoJet => NormalFrame.gramDet (K 0) (K 1)) := by
    unfold NormalFrame.gramDet dotProduct
    fun_prop
  exact (hd.continuousAt.eventually_ne hJ.1).and
    ((contDiffAt_realNormalPart (hs 0) (hs 1) (hs 4) hJ.1).continuousAt.eventually_ne hJ.2)

theorem compact_real_jet_neighborhood {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (K : TopologicalSpace.Compacts Base)
    (hD : ∀ p ∈ (K : Set Base),
      NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hB : ∀ p ∈ (K : Set Base), realSecond F p ≠ 0) :
    ∃ (ε : ℝ) (Q : Set RealTwoJet), 0 < ε ∧ IsCompact Q ∧ Q ⊆ admissibleRealJets ∧
      ∀ G : RField 4, (∀ p ∈ (K : Set Base), ‖realTwoJet G p - realTwoJet F p‖ < ε) →
        MapsTo (realTwoJet G) K Q := by
  let J := realTwoJet F '' (K : Set Base)
  have hJ : IsCompact J := K.isCompact.image (contDiff_realTwoJet hF).continuous
  have hJa : J ⊆ admissibleRealJets := by
    rintro _ ⟨p,hp,rfl⟩
    exact ⟨hD p hp,hB p hp⟩
  obtain ⟨ε,hε,he⟩ := hJ.exists_cthickening_subset_open admissibleRealJets_domain.isOpen hJa
  refine ⟨ε,Metric.cthickening ε J,hε,hJ.cthickening,he,?_⟩
  intro G hGF p hp
  apply Metric.thickening_subset_cthickening
  apply Metric.mem_thickening_iff.mpr
  exact ⟨realTwoJet F p,mem_image_of_mem _ hp,by simpa only [dist_eq_norm] using hGF p hp⟩

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseChartStability
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed good phase chart remains admissible throughout a C2 neighborhood. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

lemma norm_realTwoJet_le_on {U : Set Base} (hU : IsOpen U) {F : RField 4}
    (hF : ContDiff ℝ ∞ F) {C : ℝ} (hC : 0 ≤ C)
    (hb : WeightedBound U 1 2 C F) {p : Base} (hp : p ∈ U) :
    ‖realTwoJet F p‖ ≤ C := by
  have h1 (v : Base) (hv : ‖v‖ = 1) : WeightedBound U 1 1 C (coordDeriv v F) := by
    change WeightedBound U 1 1 C (fun x => fderiv ℝ F x v)
    simpa only [hv,div_one,one_mul] using hb.directional hU zero_lt_one hF.contDiffOn v
  have h2 (v w : Base) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      ‖coordDeriv v (coordDeriv w F) p‖ ≤ C := by
    have hd := (h1 w hw).directional hU zero_lt_one (contDiff_real_coordDeriv hF w).contDiffOn v
    simpa only [coordDeriv,hv,div_one,one_mul] using hd.norm_le hp
  have hx : ‖dx‖ = 1 := by simp [dx]
  have hy : ‖dy‖ = 1 := by simp [dy]
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  fin_cases i
  · exact (h1 dx hx).norm_le hp
  · exact (h1 dy hy).norm_le hp
  · exact h2 dx dx hx hx
  · exact h2 dx dy hx hy
  · exact h2 dy dy hy hy

theorem compact_twoJet_comp_bound {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (K : Compacts Base) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (F : RField 4), ContDiff ℝ ∞ F → ∀ C : ℝ,
      0 ≤ C → WeightedBound univ 1 2 C F →
      ∀ p ∈ (K : Set Base), ‖realTwoJet (F ∘ T) p‖ ≤ D*C := by
  obtain ⟨r,hr⟩ := K.isCompact.isBounded.subset_ball (0 : Base)
  obtain ⟨B,hB,hb⟩ := compact_local_weighted_bound Metric.isOpen_ball isOpen_univ
    (isCompact_closedBall (0 : Base) r) Metric.ball_subset_closedBall (subset_univ _)
    hT.contDiffOn 2
  let D : ℝ := ((2 : ℕ).factorial : ℝ)*B^2
  have hD : 1 ≤ D := by dsimp [D] <;> nlinarith [sq_nonneg (B-1)]
  refine ⟨D,hD,?_⟩
  intro F hF C hC hFC p hp
  have hcoord (j : ℕ) (_ : 1 ≤ j) (hj : j ≤ 2) (x : Base)
      (hx : x ∈ Metric.ball (0 : Base) r) :
      ‖iteratedFDerivWithin ℝ j T (Metric.ball (0 : Base) r) x‖ ≤ B := by
    simpa only [one_pow,one_mul] using hb 1 zero_le_one le_rfl j hj x hx
  have hc := hFC.comp_coordinates Metric.isOpen_ball.uniqueDiffOn uniqueDiffOn_univ
    zero_lt_one le_rfl hB hC hT.contDiffOn hF.contDiffOn (mapsTo_univ _ _) hcoord
  have hn := norm_realTwoJet_le_on Metric.isOpen_ball (hF.comp hT) (by positivity) hc (hr hp)
  simpa only [D,mul_assoc,mul_left_comm,mul_comm] using hn

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes WeightedEstimates

/-- The compact jet neighborhood and radius are fixed before the perturbed
map, using the smooth inverse of the reference map. -/
theorem GoodPhaseChart.uniform_jet_neighborhood {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (c : GoodPhaseChart F φ) :
    ∃ (ρ : ℝ) (Q : Set RealTwoJet), 0 < ρ ∧ IsCompact Q ∧ Q ⊆ admissibleRealJets ∧
      ∀ (G : RField 4), ContDiff ℝ ∞ G → ∀ C : ℝ, 0 ≤ C → C < ρ →
      WeightedBound univ 1 2 C (G-F) →
      MapsTo (realTwoJet (G ∘ c.chart.symm)) c.chart.target Q ∧
        RealModeDomain (G ∘ c.chart.symm) c.chart.target := by
  obtain ⟨ε,Q,hε,hQ,hQa,hclose⟩ := compact_real_jet_neighborhood (hF.comp c.smoothInverse)
    c.targetCompact (fun p hp => c.good.determinant p (c.targetInside hp))
    (fun p hp => c.good.good p (c.targetInside hp))
  obtain ⟨D,hD,hd⟩ := compact_twoJet_comp_bound c.smoothInverse c.targetCompact
  have hDp : 0 < D := zero_lt_one.trans_le hD
  refine ⟨ε/D,Q,div_pos hε hDp,hQ,hQa,?_⟩
  intro G hG C hC hCρ hb
  have hDC : D*C < ε := by
    simpa only [mul_comm] using (lt_div_iff₀ hDp).mp hCρ
  have hsmall (p : Base) (hp : p ∈ (c.targetCompact : Set Base)) :
      ‖realTwoJet (G ∘ c.chart.symm) p - realTwoJet (F ∘ c.chart.symm) p‖ < ε := by
    have hj := hd (G-F) (hG.sub hF) C hC hb p hp
    have he : (G-F) ∘ c.chart.symm = (G ∘ c.chart.symm) - (F ∘ c.chart.symm) := rfl
    rw [he,realTwoJet_sub (hG.comp c.smoothInverse) (hF.comp c.smoothInverse)] at hj
    exact hj.trans_lt hDC
  have hmaps : MapsTo (realTwoJet (G ∘ c.chart.symm)) c.chart.target Q :=
    fun p hp => hclose (G ∘ c.chart.symm) hsmall (c.targetBound hp)
  refine ⟨hmaps,c.chart.open_target,?_,?_⟩
  · intro p hp
    exact (hQa (hmaps hp)).1
  · intro p hp
    exact (hQa (hmaps hp)).2

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_UniformPhaseChartBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform mode coefficients and normal fields on the fixed local phase chart. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes WeightedEstimates

/-- The radius and all constant profiles are fixed before the perturbed map.
Only its weighted two-jet size enters, with the explicit polynomial power. -/
theorem GoodPhaseChart.uniform_mode_bounds {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (c : GoodPhaseChart F φ) :
    ∃ (ρ : ℝ) (D E : ℕ → ℝ), 0 < ρ ∧ (∀ m, 1 ≤ D m) ∧ (∀ m, 1 ≤ E m) ∧
      ∀ (G : RField 4), ContDiff ℝ ∞ G → ∀ C₀ : ℝ, 0 ≤ C₀ → C₀ < ρ →
      WeightedBound univ 1 2 C₀ (G-F) →
      RealModeDomain (G ∘ c.chart.symm) c.chart.target ∧
      ∀ (m : ℕ) (s C : ℝ), 0 < s → 1 ≤ C →
        WeightedBound c.chart.target s m C (realTwoJet (G ∘ c.chart.symm)) →
        ReconstructionCoefficientBound (fun p => complexify ((G ∘ c.chart.symm) p))
          c.chart.target s m ((m.factorial : ℝ) * D m * C^m) ∧
        WeightedBound c.chart.target s m ((m.factorial : ℝ) * E m * C^m)
          (freeNormal (G ∘ c.chart.symm)) := by
  obtain ⟨ρ,Q,hρ,hQ,hQa,hnear⟩ := c.uniform_jet_neighborhood hF
  choose D hD hd using fun m => compact_real_reconstruction_bounds c.chart.open_target
    admissibleRealJets_domain hQ hQa m
  choose E hE he using fun m => compact_freeNormal_bound c.chart.open_target
    admissibleRealJets_domain hQ hQa m
  refine ⟨ρ,D,E,hρ,hD,hE,?_⟩
  intro G hG C₀ hC₀ hCρ hb
  obtain ⟨hmap,hdom⟩ := hnear G hG C₀ hC₀ hCρ hb
  refine ⟨hdom,?_⟩
  intro m s C hs hC hj
  exact ⟨hd m (G ∘ c.chart.symm) s C hs hC (hG.comp c.smoothInverse) hmap hj,
    he m (G ∘ c.chart.symm) s C hs hC (hG.comp c.smoothInverse) hmap hj⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_UniformLinearPhaseBudgets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed numerical mean budgets for nearby immersions in a linear phase chart.
The chart, cut-off, coefficient form, and weighted two-jet profile are fixed
before the nearby immersion and slow scale are supplied. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes PhaseMean WeightedEstimates

/-- All seven mean-budget profiles can be chosen before a nearby immersion
and its actual slow scale. The dependence on its two-jet is the displayed
fixed profile `H`, rather than an implicit map-dependent constant. -/
theorem uniform_linear_phase_budgets_all_profiles {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {Ω U K : Set Base} (hΩ : IsOpen Ω) (hU : IsOpen U) (hK : IsCompact K)
    (hUK : U ⊆ K) (hKΩ : K ⊆ Ω) {ξ : Base} (hξ : ξ ≠ 0)
    (hImm : ∀ x ∈ Ω, Function.Injective (fderiv ℝ F x))
    (hgood : ∀ x ∈ Ω, Good (realSecondTensor F x) ξ)
    {ψ : Base → ℝ} (hψ : ContDiff ℝ ∞ ψ) (Q : PhaseMean.Tensor →L[ℝ] ℝ)
    : ∃ ρ : ℝ, 0 < ρ ∧ ∀ (H : ℕ → ℝ), (∀ m, 1 ≤ H m) →
    ∃ b : BudgetProfiles,
      ∀ (G : RField 4), ContDiff ℝ ∞ G → ∀ C₀ : ℝ, 0 ≤ C₀ → C₀ < ρ →
      WeightedBound univ 1 2 C₀ (G-F) →
      ∀ s : ℝ, 0 < s → s ≤ 1 →
      (∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s m (H m)
        (realTwoJet (G ∘ (linearPhaseChart ξ hξ U hU).symm))) →
      RealModeDomain (G ∘ (linearPhaseChart ξ hξ U hU).symm)
        (linearPhaseChart ξ hξ U hU).target ∧
      ∃ d : Budgets U (linearPhaseChart ξ hξ U hU).target s
        (G ∘ (linearPhaseChart ξ hξ U hU).symm) ψ (fun _ => Q)
        (linearPhaseChart ξ hξ U hU) (linearPhaseChart ξ hξ U hU).symm,
        d.profiles = b := by
  let L := phaseEquiv ξ hξ
  let V := (linearPhaseChart ξ hξ U hU).target
  let KV := L '' K
  let ΩV := L '' Ω
  have hV : IsOpen V := (linearPhaseChart ξ hξ U hU).open_target
  have hKV : IsCompact KV := hK.image L.continuous
  have hVK : V ⊆ KV := image_mono hUK
  have hsm := linearPhaseChart_smooth ξ hξ U hU
  let c : GoodPhaseChart F (phaseLinear ξ) := {
    chart := linearPhaseChart ξ hξ U hU
    phase := linearPhaseChart_phase ξ hξ U hU
    smooth := hsm.1
    smoothInverse := hsm.2
    sourceCompact := ⟨K,hK⟩
    targetCompact := ⟨KV,hKV⟩
    domain := ΩV
    sourceBound := hUK
    targetBound := hVK
    targetInside := image_mono hKΩ
    good := realModeDomain_phase hF hΩ hξ hImm hgood
  }
  obtain ⟨ρ,D,E,hρ,hD,hE,hnear⟩ := c.uniform_mode_bounds hF
  have hpull : ContDiffOn ℝ ∞ (pullbackField (linearPhaseChart ξ hξ U hU)) univ := by
    have hh : pullbackField (linearPhaseChart ξ hξ U hU) =
        fun _ => pullback (phaseEquiv ξ hξ).toContinuousLinearMap :=
      funext (pullbackField_linearPhaseChart hξ hU)
    rw [hh]
    exact contDiffOn_const
  choose I hI hbI using fun m => compact_local_weighted_bound hV isOpen_univ hKV
    hVK (subset_univ KV) hsm.2.contDiffOn m
  choose J hJ hbJ using fun m => compact_local_weighted_bound hU isOpen_univ hK
    hUK (subset_univ K) hsm.1.contDiffOn m
  choose P hP hbP using fun m => compact_local_weighted_bound hV isOpen_univ hKV
    hVK (subset_univ KV) hψ.contDiffOn m
  choose Qb hQb hbQ using fun m => compact_local_weighted_bound hV isOpen_univ hKV
    hVK (subset_univ KV) (show ContDiffOn ℝ ∞ (fun _ : Base => Q) univ from
      contDiffOn_const) m
  choose T hT hbT using fun m => compact_local_weighted_bound hU isOpen_univ hK
    hUK (subset_univ K) hpull m
  refine ⟨ρ,hρ,?_⟩
  intro H hH
  have hfactor (A : ℕ → ℝ) (hA : ∀ m, 1 ≤ A m) (m : ℕ) :
      1 ≤ (m.factorial : ℝ) * A m * H m ^ m := by
    have hf : (1 : ℝ) ≤ (m.factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos m)
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hf (hA m)) (one_le_pow₀ (hH m))
  let b : BudgetProfiles := {
    inv := I
    chi := J
    psi := P
    forms := Qb
    pull := T
    normal := fun m => (m.factorial : ℝ) * E m * H m ^ m
    mode := fun m => (m.factorial : ℝ) * D m * H m ^ m
    inv_pos := hI
    chi_pos := hJ
    psi_pos := hP
    forms_pos := hQb
    pull_pos := hT
    normal_pos := hfactor E hE
    mode_pos := hfactor D hD
  }
  refine ⟨b,?_⟩
  intro G hG C₀ hC₀ hCρ hb s hs hs1 hjet
  obtain ⟨hdom,hmodes⟩ := hnear G hG C₀ hC₀ hCρ hb
  refine ⟨hdom, {
    inv := b.inv
    chi := b.chi
    psi := b.psi
    forms := b.forms
    pull := b.pull
    normal := b.normal
    mode := b.mode
    inv_pos := b.inv_pos
    chi_pos := b.chi_pos
    psi_pos := b.psi_pos
    forms_pos := b.forms_pos
    pull_pos := b.pull_pos
    normal_pos := b.normal_pos
    mode_pos := b.mode_pos
    inv_bound := ?_
    chi_bound := ?_
    psi_bound := fun m => hbP m s hs.le hs1
    forms_bound := fun m => hbQ m s hs.le hs1
    pull_bound := fun m => hbT m s hs.le hs1
    normal_bound := fun m => (hmodes m s (H m) hs (hH m) (hjet m)).2
    mode_bound := fun m => (hmodes m s (H m) hs (hH m) (hjet m)).1
  }, rfl⟩
  · intro m j _ hj x hx
    simpa only [one_pow,one_mul] using hbI m 1 zero_le_one le_rfl j hj x hx
  · intro m j _ hj x hx
    simpa only [one_pow,one_mul] using hbJ m 1 zero_le_one le_rfl j hj x hx

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PerturbedMeanTransfer
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer actual geometric mean data to a fixed polynomial perturbation.
The cutoff, form, local geometry and reconstruction budgets stay the same.
Only the polynomial profile and the required input-jet orders change. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates

theorem ChartedMeanProfile.Fits.withPolynomial {n : ℕ}
    {p₀ : ChartedMeanProfile emptyMetricPolynomial}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {τ : ℝ} {s : ℝ≥0}
    {c₀ : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    {d₀ : ChartedMeanData c₀ r ρ R reference} (hf : p₀.Fits d₀)
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) {O : Set LowJet}
    (hO : IsOpen O) (hP : ∀ k j, (P k j).SmoothCoeffs O)
    (hGO : Set.MapsTo (lowJet G) c₀.U O) (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
    (hpoly : ∀ m Z, supportedWeightedSeminorm
      (chartSupport c₀.e (modeSupport K) c₀.supportChart) s m
      (phaseChartPolynomialOperator hO c₀.openU P hP hG hGO K c₀.supportU
        c₀.smoothPhase τ ε c₀.e c₀.smoothForward c₀.smoothInverse c₀.supportChart Z) ≤
      ε / τ ^ tensorLoss P * D m * supportedWeightedSeminorm
        (chartSupport c₀.e (modeSupport K) c₀.supportChart) s (m + tensorOrder P) Z)
    (hQO : p₀.Q ⊆ O) :
    (p₀.withPolynomial P hO hP hQO D).Fits
      (d₀.withPolynomial P ε hO hP hGO D hD hpoly
        (fun _ hx => hQO (by simpa only [hf.range] using hx))) := by
  refine ⟨hf.domain,hf.coefficients,rfl,hf.coordinates,hf.target,
    hf.inverse,hf.forms,hf.cutoff,hf.normal,?_,?_,hf.range⟩
  · funext m
    exact congrFun hf.jets (m + tensorOrder P)
  · funext m
    exact congrFun hf.phase (m + tensorOrder P)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetPrefixBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual positional two-jet on a fixed bounded domain. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem directional_of_prefix {U : Set E} (hU : IsOpen U)
    {f : E → V} (hf : ContDiff ℝ ∞ f) {s C : ℝ} {m : ℕ}
    (hs : 0 < s) (hC : 0 ≤ C)
    (hb : ∀ j ≤ m+1, WeightedBound U 1 j (C/s^(j-1)) f)
    (v : E) (hv : ‖v‖ ≤ 1) :
    WeightedBound U s m C (fun x => fderiv ℝ f x v) := by
  intro j hj x hx
  have hh := ((hb (j+1) (by omega)).directional hU zero_lt_one hf.contDiffOn v)
    j le_rfl x hx
  simp only [one_pow,one_mul,div_one,Nat.add_sub_cancel] at hh
  calc
    _ ≤ s^j*(‖v‖*(C/s^j)) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
    _ = ‖v‖*C := by field_simp
    _ ≤ C := mul_le_of_le_one_left hC hv

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem jet_lowWord_bound {U : Set Base} (hU : IsOpen U)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) {s C : ℝ} {m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hb : ∀ j ≤ m+2, WeightedBound U 1 j (C/s^(j-2)) G)
    (w : Fin 7) (a : Fin 4) :
    WeightedBound U s m C (fun p => jet G (lowWord w) a p) := by
  let f : Base → ℝ := fun p => G p a
  have hf : ContDiff ℝ ∞ f := contDiff_pi.mp hG a
  have hp (j : ℕ) (hj : j ≤ m+2) : WeightedBound U 1 j (C/s^(j-2)) f :=
    (hb j hj).component hU.uniqueDiffOn zero_le_one
      (div_nonneg hC (pow_nonneg hs.le _)) hG.contDiffOn a
  have hzero : WeightedBound U s m C f := by
    intro j hj x hx
    have hh := hp j (by omega) j le_rfl x hx
    simp only [one_pow,one_mul] at hh
    calc
      _ ≤ s^j*(C/s^(j-2)) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
      _ ≤ s^j*(C/s^j) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hC (pow_pos hs _)
          (pow_le_pow_of_le_one hs.le hs1 (Nat.sub_le _ _))) (pow_nonneg hs.le _)
      _ = C := by field_simp
  have hunit (v : Fin 2) : ‖coordinateVector v‖ = 1 := by
    simp only [coordinateVector,Pi.norm_single,norm_one]
  have hfirst (v : Fin 2) (j : ℕ) (hj : j ≤ m+1) :
      WeightedBound U 1 j (C/s^(j-1)) (fun x => fderiv ℝ f x (coordinateVector v)) := by
    have hh := (hp (j+1) (by omega)).directional hU zero_lt_one hf.contDiffOn (coordinateVector v)
    have he : j+1-2 = j-1 := by omega
    simpa only [hunit,one_mul,div_one,he] using hh
  have hone (v : Fin 2) :
      WeightedBound U s m C (fun x => fderiv ℝ f x (coordinateVector v)) := by
    apply directional_of_prefix hU hf hs hC _ (coordinateVector v) (hunit v).le
    intro j hj
    apply (hp j (by omega)).mono_const
    exact div_le_div_of_nonneg_left hC (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1 (by omega))
  have htwo (v v' : Fin 2) : WeightedBound U s m C
      (fun x => fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector v')) x (coordinateVector v)) :=
    directional_of_prefix hU
      ((hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)
      hs hC (hfirst v') (coordinateVector v) (hunit v).le
  fin_cases w
  · exact hzero
  · exact hone 0
  · exact hone 1
  · exact htwo 0 0
  · exact htwo 0 1
  · exact htwo 1 0
  · exact htwo 1 1

theorem bounded_lowJet_prefix {U : Set Base} (hU : IsOpen U)
    (K : Compacts Base) (hUK : U ⊆ K) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (G : Base → Space), ContDiff ℝ ∞ G → ∀ s C : ℝ,
      0 < s → s ≤ 1 → 0 ≤ C →
      (∀ j ≤ m+2, WeightedBound U 1 j (C/s^(j-2)) G) →
      WeightedBound U s m (D+C) (lowJet G) := by
  obtain ⟨D,hD,hd⟩ := compact_local_weighted_bound hU isOpen_univ K.isCompact hUK
    (subset_univ _) (contDiff_id : ContDiff ℝ ∞ (id : Base → Base)).contDiffOn m
  refine ⟨D,hD,?_⟩
  intro G hG s C hs hs1 hC hb
  apply WeightedBound.pi hU.uniqueDiffOn hs (by linarith)
  · intro i
    exact (contDiff_pi.mp (lowJet_smooth hG) i).contDiffOn
  · intro i
    cases i with
    | inl i =>
      exact ((hd s hs.le hs1).component hU.uniqueDiffOn hs.le
        (zero_le_one.trans hD) contDiff_id.contDiffOn i).mono_const (by linarith)
    | inr i =>
      exact (jet_lowWord_bound hU hG hs hs1 hC hb i.1 i.2).mono_const (by linarith)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetCompactRange
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One compact positional-jet range for all maps in a bounded C2 family. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem bounded_lowJet_range {U : Set Base} (hU : IsOpen U)
    (K : Compacts Base) (hUK : U ⊆ K) {C : ℝ} (hC : 0 ≤ C) :
    ∃ Q : Set LowJet, IsCompact Q ∧ ∀ (G : Base → Space), ContDiff ℝ ∞ G →
      WeightedBound U 1 2 C G → MapsTo (lowJet G) U Q := by
  obtain ⟨D,_,hd⟩ := bounded_lowJet_prefix hU K hUK 0
  refine ⟨Metric.closedBall 0 (D+C),isCompact_closedBall _ _,?_⟩
  intro G hG hb p hp
  have hj := hd G hG 1 C zero_lt_one le_rfl hC (fun j hj => by
    simpa only [one_pow,div_one] using hb.mono_order (by omega : j ≤ 2))
  simpa only [Metric.mem_closedBall,dist_zero_right] using hj.norm_le hp

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformLinearChartedMeanData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual charted mean data with one profile for a nearby family. The
positional jet is read on a fixed bounded original-coordinate domain. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes PhaseMean PhaseGeometry

/-- A bounded original-coordinate domain and explicit weighted jet profiles
give one charted-mean profile before the nearby map and both scales. -/
theorem uniform_linear_charted_mean_data_all_profiles
    {F : Base → Space} (hF : ContDiff ℝ ∞ F)
    {Ω U K : Set SmallModes.Base} (hΩ : IsOpen Ω) (hU : IsOpen U) (hK : IsCompact K)
    (hUK : U ⊆ K) (hKΩ : K ⊆ Ω)
    {ξ : SmallModes.Base} (hξ : ξ ≠ 0)
    (hImm : ∀ x ∈ Ω, Function.Injective
      (fderiv ℝ (F ∘ planeCoordinateIsometry.symm) x))
    (hgood : ∀ x ∈ Ω, Good (realSecondTensor (F ∘ planeCoordinateIsometry.symm) x) ξ)
    (S : Compacts Base) (hS : (modeSupport S : Set SmallModes.Base) ⊆ U)
    {U₀ : Set Base} (hU₀ : IsOpen U₀) (K₀ : Compacts Base)
    (hU₀K : U₀ ⊆ K₀) (hSU₀ : (S : Set Base) ⊆ U₀)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hphase : coordinatePhase φ = phaseLinear ξ)
    (ψ : SupportedField (F := ℝ)
      (chartSupport (linearPhaseChart ξ hξ U hU) (modeSupport S) hS))
    (Q : Tensor →L[ℝ] ℝ) {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (hmargin : ∀ x ∈ U, ρ + ‖Q‖*r ≤ Q (reference x) ∧
      Q (reference x) ≤ R - ‖Q‖*r)
    : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (H Pjet : ℕ → ℝ),
      (∀ m, 1 ≤ H m) → (∀ m, 0 ≤ Pjet m) →
      ∃ p : ChartedMeanProfile emptyMetricPolynomial,
      p.U = U₀ ∧ p.O = univ ∧ (∀ m, p.D m = 0) ∧
      ∀ (G : Base → Space) (hG : ContDiff ℝ ∞ G) (C₀ : ℝ),
        0 ≤ C₀ → C₀ < ρ₀ →
        WeightedBound univ 1 2 C₀
          ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
        ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s m (H m)
          (realTwoJet ((G ∘ planeCoordinateIsometry.symm) ∘
            (linearPhaseChart ξ hξ U hU).symm))) →
        (∀ m j, j ≤ m+2 → WeightedBound U₀ 1 j
          (Pjet m / (s : ℝ)^(j-2)) G) →
        ∀ τ : ℝ, ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ S τ s,
          ∃ d : ChartedMeanData c r ρ R reference,
            p.Fits d ∧ c.e = linearPhaseChart ξ hξ U hU ∧
              (∀ x, d.cutoff x = ψ x) ∧ d.form = fun _ => Q := by
  classical
  have hFc : ContDiff ℝ ∞ (F ∘ planeCoordinateIsometry.symm) :=
    hF.comp planeCoordinateIsometry.symm.contDiff
  obtain ⟨ρ₀,hρ₀,hall⟩ := uniform_linear_phase_budgets_all_profiles hFc hΩ hU hK hUK hKΩ
    hξ hImm hgood ψ.contDiff Q
  refine ⟨ρ₀,hρ₀,?_⟩
  intro H Pjet hH hPjet
  obtain ⟨b,hb⟩ := hall H hH
  choose D hD hd using fun m => bounded_lowJet_prefix hU₀ K₀ hU₀K m
  obtain ⟨Qjet,hQjet,hQrange⟩ := bounded_lowJet_range hU₀ K₀ hU₀K (hPjet 0)
  have hφderiv (v : Fin 2) : ContDiff ℝ ∞ (fun x => fderiv ℝ φ x (coordinateVector v)) :=
    (hφ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  choose A hA ha using fun (m : ℕ) (v : Fin 2) => compact_local_weighted_bound
    hU₀ isOpen_univ K₀.isCompact hU₀K (subset_univ _) (hφderiv v).contDiffOn m
  let B : ℕ → ℝ := fun m => D m + Pjet m
  let Ph : ℕ → ℝ := fun m => ∑ v : Fin 2, A m v
  have hB (m : ℕ) : 1 ≤ B m := (hD m).trans (le_add_of_nonneg_right (hPjet m))
  have hPh (m : ℕ) : 0 ≤ Ph m :=
    Finset.sum_nonneg (fun v _ => zero_le_one.trans (hA m v))
  have hP : ∀ k l, (emptyMetricPolynomial k l).SmoothCoeffs univ :=
    fun _ l => Fin.elim0 l
  let e := linearPhaseChart ξ hξ U hU
  have he := linearPhaseChart_smooth ξ hξ U hU
  let p : ChartedMeanProfile emptyMetricPolynomial := {
    U := U₀
    O := univ
    Q := Qjet
    V := e.target
    openU := hU₀
    openO := isOpen_univ
    openV := e.open_target
    compact := hQjet
    subsetDomain := subset_univ _
    smoothP := hP
    C := fun m => b.mode (m+1)
    D := fun _ => 0
    J := b.chi
    inv := b.inv
    forms := b.forms
    psi := b.psi
    normal := b.normal
    B := B
    F := Ph
    nonnegC := fun m => zero_le_one.trans (b.mode_pos (m+1))
    oneLEJ := b.chi_pos
    oneLEInv := b.inv_pos
    oneLEForms := b.forms_pos
    oneLEPsi := b.psi_pos
    oneLENormal := b.normal_pos
    oneLEB := hB
    nonnegF := hPh
  }
  refine ⟨p,rfl,rfl,(fun _ => rfl),?_⟩
  intro G hG C₀ hC₀ hCρ hclose s hs hs1 hjet hpref τ
  have hGc : ContDiff ℝ ∞ (G ∘ planeCoordinateIsometry.symm) :=
    hG.comp planeCoordinateIsometry.symm.contDiff
  obtain ⟨hdom,d₀,hprofiles⟩ := hb (G ∘ planeCoordinateIsometry.symm) hGc C₀
    hC₀ hCρ hclose s hs hs1 hjet
  have hmode : d₀.mode = b.mode := congrArg BudgetProfiles.mode hprofiles
  have hchi : d₀.chi = b.chi := congrArg BudgetProfiles.chi hprofiles
  have hinv : d₀.inv = b.inv := congrArg BudgetProfiles.inv hprofiles
  have hforms : d₀.forms = b.forms := congrArg BudgetProfiles.forms hprofiles
  have hpsi : d₀.psi = b.psi := congrArg BudgetProfiles.psi hprofiles
  have hnormal : d₀.normal = b.normal := congrArg BudgetProfiles.normal hprofiles
  have hmap : ContDiff ℝ ∞ ((G ∘ planeCoordinateIsometry.symm) ∘ e.symm) :=
    hGc.comp he.2
  let c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ S τ s := {
    U := U₀
    O := univ
    openU := hU₀
    openO := isOpen_univ
    smoothP := hP
    mapsG := mapsTo_univ _ _
    supportU := hSU₀
    smoothPhase := hφ
    e := e
    smoothForward := he.1.contDiffOn
    smoothInverse := he.2.contDiffOn
    supportChart := hS
    phase := by
      intro x _
      rw [hphase]
      exact linearPhaseChart_phase ξ hξ U hU x
    smoothMap := hmap
    domain := hdom.complexDomain hmap
    C := fun m => b.mode (m+1)
    D := fun _ => 0
    J := b.chi
    nonnegC := fun m => zero_le_one.trans (b.mode_pos (m+1))
    nonnegD := fun _ => le_rfl
    oneLEJ := b.chi_pos
    coordinates := by
      intro m j hj hjm x hx
      have hxU : x ∈ U := by simpa only [e,linearPhaseChart_source] using hx
      simpa only [e,linearPhaseChart_source,hchi] using d₀.chi_bound m j hj hjm x hxU
    coefficients := by
      intro m
      simpa only [e,hmode,Function.comp_def] using d₀.mode_bound (m+1)
    polynomial := by
      intro m Z
      have hsS : (modeSupport S : Set SmallModes.Base) ⊆ e.source := hS
      have hz := phaseChartPolynomialOperator_zero isOpen_univ hU₀ emptyMetricPolynomial hP hG
        (mapsTo_univ _ _) S hSU₀ hφ τ e he.1.contDiffOn he.2.contDiffOn hsS
      rw [hz]
      simp
  }
  have hpull : ContDiffOn ℝ ∞ (pullbackField e) U := by
    have hh : pullbackField e = fun _ => pullback (phaseEquiv ξ hξ).toContinuousLinearMap :=
      funext (pullbackField_linearPhaseChart hξ hU)
    rw [hh]
    exact contDiffOn_const
  let loc : LocalBounds U e.target s r ρ R reference c.realMap ψ (fun _ => Q) e e.symm := {
    openU := hU
    smoothF := hmap
    domain := hdom
    smoothPsi := ψ.contDiff.contDiffOn
    smoothQ := contDiffOn_const
    smoothChi := he.1.contDiffOn
    smoothInv := he.2.contDiffOn
    chiInto := fun x hx => e.map_source hx
    invInto := fun x hx => e.map_target hx
    smoothPullback := hpull
    margin := fun x hx => hmargin _ (e.map_target hx)
  }
  have hjetRange : MapsTo (lowJet G) U₀ Qjet := by
    apply hQrange G hG
    simpa only [Nat.sub_self,pow_zero,div_one] using hpref 0 2 (by omega)
  let d : ChartedMeanData c r ρ R reference := {
    cutoff := ψ
    form := fun _ => Q
    localBounds := loc
    budgets := d₀
    compactJets := Qjet
    compact := hQjet
    subsetDomain := subset_univ _
    mapsJets := hjetRange
    B := B
    F := Ph
    oneLEB := hB
    nonnegF := hPh
    jetsBound := by
      intro m
      simpa only [tensorOrder_emptyMetricPolynomial,Nat.add_zero] using
        hd m G hG s (Pjet m) hs hs1 (hPjet m) (hpref m)
    phaseBound := by
      intro m v
      have hv : A m v ≤ Ph m := Finset.single_le_sum
        (fun w _ => zero_le_one.trans (hA m w)) (Finset.mem_univ v)
      simpa only [tensorOrder_emptyMetricPolynomial,Nat.add_zero] using
        (ha m v s s.coe_nonneg hs1).mono_const hv
  }
  refine ⟨c,d,?_,rfl,(fun _ => rfl),rfl⟩
  exact ⟨rfl,rfl,rfl,rfl,rfl,hinv,hforms,hpsi,hnormal,rfl,rfl,rfl⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformLinearChartedMeanFamily
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniformly profiled three-phase mean family for nearby immersions. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes PhaseMean PhaseGeometry

theorem ChartedMeanProfile.Fits.atRadius {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {ε τ : ℝ} {s : ℝ≥0} {G : Base → Space} {hG : ContDiff ℝ ∞ G}
    {φ : Base → ℝ} {S : Compacts Base}
    {c : PolynomialSolveData P ε G hG φ S τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    {p : ChartedMeanProfile P} {d : ChartedMeanData c r ρ R reference}
    (h : p.Fits d) (r' : ℝ) (hr : r' ≤ r) : p.Fits (d.atRadius r' hr) := by
  exact ⟨h.domain,h.coefficients,h.perturbation,h.coordinates,h.target,h.inverse,
    h.forms,h.cutoff,h.normal,h.jets,h.phase,h.range⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformLinearPerturbedMeanData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform perturbed mean data in a fixed linear phase chart.  Bounds for
transporting the polynomial may be chosen independently of the numerical
profiles retained by the geometric solver. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes PhaseMean PhaseGeometry

/-- Independent fixed chart bounds control polynomial transport without
changing the geometric solver or the profile fitted by its mean data. -/
theorem uniform_perturbed_mean_transfer_with_chart_profiles {n : ℕ}
    (p₀ : ChartedMeanProfile emptyMetricPolynomial)
    (P : Fin 3 → Fin n → Expression) {O : Set LowJet} (hO : IsOpen O)
    (hP : ∀ k j, (P k j).SmoothCoeffs O) (hQO : p₀.Q ⊆ O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ p₀.U)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source)
    (J I : ℕ → ℝ) (hJ : ∀ m, 1 ≤ J m) (hI : ∀ m, 1 ≤ I m)
    (hebound : ∀ m j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J m)
    (hibound : ∀ m j, 1 ≤ j → j ≤ m + 1 → ∀ x ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target x‖ ≤ I m) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ (G : Base → Space) (hG : ContDiff ℝ ∞ G) (φ : Base → ℝ)
        (τ ε : ℝ) (s : ℝ≥0),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      ∀ (c₀ : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s),
      c₀.e = e → ∀ {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
        (d₀ : ChartedMeanData c₀ r ρ R reference), p₀.Fits d₀ →
      ∃ c : PolynomialSolveData P ε G hG φ K τ s,
      ∃ d : ChartedMeanData c r ρ R reference,
        (p₀.withPolynomial P hO hP hQO D).Fits d ∧ c.e = e ∧
        (∀ x, d.cutoff x = d₀.cutoff x) ∧ d.form = d₀.form := by
  obtain ⟨D,hD,hd⟩ := phaseChartPolynomialOperator_bounds
    p₀.openU hO p₀.compact hQO P hP K hKU e he hi hKe
    (fun m => p₀.B (m + tensorOrder P)) (fun m => p₀.F (m + tensorOrder P))
    J I (fun m => p₀.oneLEB (m + tensorOrder P))
    (fun m => p₀.nonnegF (m + tensorOrder P)) hJ hI hebound hibound
  refine ⟨D,hD,?_⟩
  intro G hG φ τ ε s hτ hs hτs hs1 hε hε1 c₀ he₀ r ρ R reference d₀ hf
  subst e
  have hGQ : Set.MapsTo (lowJet G) p₀.U p₀.Q := by
    simpa only [hf.domain,hf.range] using d₀.mapsJets
  have hGb (m : ℕ) : WeightedBound p₀.U s (m + tensorOrder P)
      (p₀.B (m + tensorOrder P)) (lowJet G) := by
    simpa only [tensorOrder_emptyMetricPolynomial,Nat.add_zero,hf.domain,hf.jets] using
      d₀.jetsBound (m + tensorOrder P)
  have hφb (m : ℕ) (v : Fin 2) : WeightedBound p₀.U s (m + tensorOrder P)
      (p₀.F (m + tensorOrder P)) (fun x => fderiv ℝ φ x (coordinateVector v)) := by
    simpa only [tensorOrder_emptyMetricPolynomial,Nat.add_zero,hf.domain,hf.phase] using
      d₀.phaseBound (m + tensorOrder P) v
  have hGO : Set.MapsTo (lowJet G) c₀.U O := by
    intro x hx
    exact hQO (hGQ (by simpa only [hf.domain] using hx))
  have hpoly : ∀ m Z, supportedWeightedSeminorm
      (chartSupport c₀.e (modeSupport K) c₀.supportChart) s m
      (phaseChartPolynomialOperator hO c₀.openU P hP hG hGO K c₀.supportU
        c₀.smoothPhase τ ε c₀.e c₀.smoothForward c₀.smoothInverse c₀.supportChart Z) ≤
      ε / τ ^ tensorLoss P * D m * supportedWeightedSeminorm
        (chartSupport c₀.e (modeSupport K) c₀.supportChart) s (m + tensorOrder P) Z := by
    simpa only [← hf.domain] using
      hd G φ hG c₀.smoothPhase hGQ s τ ε hτ hs hτs hs1 hε hε1 hGb hφb
  let c := c₀.withPolynomial P ε hO hP hGO D hD hpoly
  let d := d₀.withPolynomial P ε hO hP hGO D hD hpoly
    (fun _ hx => hQO (by simpa only [hf.range] using hx))
  exact ⟨c,d,hf.withPolynomial P ε hO hP hGO D hD hpoly hQO,rfl,
    (fun _ => rfl),rfl⟩

/-- A fixed globally smooth polynomial and linear-phase geometry give one
perturbed mean profile before every nearby map and both scales. -/
theorem uniform_linear_perturbed_mean_data_all_profiles {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs univ)
    {F : Base → Space} (hF : ContDiff ℝ ∞ F)
    {Ω U K : Set SmallModes.Base} (hΩ : IsOpen Ω) (hU : IsOpen U) (hK : IsCompact K)
    (hUK : U ⊆ K) (hKΩ : K ⊆ Ω) {ξ : SmallModes.Base} (hξ : ξ ≠ 0)
    (hImm : ∀ x ∈ Ω, Function.Injective
      (fderiv ℝ (F ∘ planeCoordinateIsometry.symm) x))
    (hgood : ∀ x ∈ Ω, Good (realSecondTensor (F ∘ planeCoordinateIsometry.symm) x) ξ)
    (S : Compacts Base) (hS : (modeSupport S : Set SmallModes.Base) ⊆ U)
    {U₀ : Set Base} (hU₀ : IsOpen U₀) (K₀ : Compacts Base)
    (hU₀K : U₀ ⊆ K₀) (hSU₀ : (S : Set Base) ⊆ U₀)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hphase : coordinatePhase φ = phaseLinear ξ)
    (ψ : SupportedField (F := ℝ)
      (chartSupport (linearPhaseChart ξ hξ U hU) (modeSupport S) hS))
    (Q : Tensor →L[ℝ] ℝ) {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (hmargin : ∀ x ∈ U, ρ + ‖Q‖ * r ≤ Q (reference x) ∧
      Q (reference x) ≤ R - ‖Q‖ * r) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (H Pjet : ℕ → ℝ),
      (∀ m, 1 ≤ H m) → (∀ m, 0 ≤ Pjet m) →
      ∃ p : ChartedMeanProfile P,
      p.U = U₀ ∧ p.O = univ ∧ (∀ m, 0 ≤ p.D m) ∧
      ∀ (G : Base → Space) (hG : ContDiff ℝ ∞ G) (C₀ : ℝ),
        0 ≤ C₀ → C₀ < ρ₀ →
        WeightedBound univ 1 2 C₀
          ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
        ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s m (H m)
          (realTwoJet ((G ∘ planeCoordinateIsometry.symm) ∘
            (linearPhaseChart ξ hξ U hU).symm))) →
        (∀ m j, j ≤ m + 2 → WeightedBound U₀ 1 j
          (Pjet m / (s : ℝ) ^ (j - 2)) G) →
        ∀ τ ε : ℝ, 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
        ∃ c : PolynomialSolveData P ε G hG φ S τ s,
        ∃ d : ChartedMeanData c r ρ R reference,
          p.Fits d ∧ c.e = linearPhaseChart ξ hξ U hU ∧
          (∀ x, d.cutoff x = ψ x) ∧ d.form = fun _ => Q := by
  classical
  obtain ⟨ρ₀,hρ₀,hbase⟩ := uniform_linear_charted_mean_data_all_profiles
    hF hΩ hU hK hUK hKΩ hξ hImm hgood S hS hU₀ K₀ hU₀K hSU₀ hφ hphase ψ Q hmargin
  let e := linearPhaseChart ξ hξ U hU
  have hsm := linearPhaseChart_smooth ξ hξ U hU
  have hsource : e.source ⊆ K := hUK
  let KV := (phaseEquiv ξ hξ) '' K
  have hKV : IsCompact KV := hK.image (phaseEquiv ξ hξ).continuous
  have htarget : e.target ⊆ KV := image_mono hUK
  choose J hJ hj using fun m => compact_local_weighted_bound e.open_source isOpen_univ
    hK hsource (subset_univ K) hsm.1.contDiffOn m
  choose I hI hi using fun m => compact_local_weighted_bound e.open_target isOpen_univ
    hKV htarget (subset_univ KV) hsm.2.contDiffOn (m + 1)
  have hJb (m j : ℕ) (_ : 1 ≤ j) (hjm : j ≤ m)
      (x : SmallModes.Base) (hx : x ∈ e.source) :
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J m := by
    simpa only [one_pow,one_mul] using hj m 1 zero_le_one le_rfl j hjm x hx
  have hIb (m j : ℕ) (_ : 1 ≤ j) (hjm : j ≤ m + 1)
      (x : SmallModes.Base) (hx : x ∈ e.target) :
      ‖iteratedFDerivWithin ℝ j e.symm e.target x‖ ≤ I m := by
    simpa only [one_pow,one_mul] using hi m 1 zero_le_one le_rfl j hjm x hx
  refine ⟨ρ₀,hρ₀,?_⟩
  intro H Pjet hH hPjet
  obtain ⟨p₀,hpU,_hpO,_hpD,hdata⟩ := hbase H Pjet hH hPjet
  have hSp : (S : Set Base) ⊆ p₀.U := by simpa only [hpU] using hSU₀
  obtain ⟨D,hD,ht⟩ := uniform_perturbed_mean_transfer_with_chart_profiles
    p₀ P isOpen_univ hP (subset_univ _) S hSp e hsm.1.contDiffOn hsm.2.contDiffOn
    hS J I hJ hI hJb hIb
  let p := p₀.withPolynomial P isOpen_univ hP (subset_univ _) D
  refine ⟨p,hpU,rfl,hD,?_⟩
  intro G hG C₀ hC₀ hCρ hclose s hs hs1 hjet hpref τ ε hτ hτs hε hε1
  obtain ⟨c₀,d₀,hfit,hce,hcut,hform⟩ := hdata G hG C₀ hC₀ hCρ hclose s hs hs1 hjet hpref τ
  obtain ⟨c,d,hfit',hce',hcut',hform'⟩ :=
    ht G hG φ τ ε s hτ hs hτs hs1 hε hε1 c₀ hce d₀ hfit
  exact ⟨c,d,hfit',hce',(fun x => (hcut' x).trans (hcut x)),hform'.trans hform⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformLinearPerturbedMeanFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A three-phase perturbed mean family with a common geometric radius.
The radius precedes all derivative profiles, and the actual family retains
the fixed phase charts, cutoffs and coefficient forms. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes PhaseMean PhaseGeometry

theorem uniform_linear_perturbed_mean_family_all_profiles_oai {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs univ)
    {F : Base → Space} (hF : ContDiff ℝ ∞ F)
    (Ω U K : Fin 3 → Set SmallModes.Base)
    (hΩ : ∀ j, IsOpen (Ω j)) (hU : ∀ j, IsOpen (U j))
    (hK : ∀ j, IsCompact (K j)) (hUK : ∀ j, U j ⊆ K j) (hKΩ : ∀ j, K j ⊆ Ω j)
    (ξ : Fin 3 → SmallModes.Base) (hξ : ∀ j, ξ j ≠ 0)
    (hImm : ∀ j x, x ∈ Ω j → Function.Injective
      (fderiv ℝ (F ∘ planeCoordinateIsometry.symm) x))
    (hgood : ∀ j x, x ∈ Ω j →
      Good (realSecondTensor (F ∘ planeCoordinateIsometry.symm) x) (ξ j))
    (S : Fin 3 → Compacts Base)
    (hS : ∀ j, (modeSupport (S j) : Set SmallModes.Base) ⊆ U j)
    {U₀ : Set Base} (hU₀ : IsOpen U₀) (K₀ : Compacts Base)
    (hU₀K : U₀ ⊆ K₀) (hSU₀ : ∀ j, (S j : Set Base) ⊆ U₀)
    (φ : Fin 3 → Base → ℝ) (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hphase : ∀ j, coordinatePhase (φ j) = phaseLinear (ξ j))
    (ψ : ∀ j, SupportedField (F := ℝ)
      (chartSupport (linearPhaseChart (ξ j) (hξ j) (U j) (hU j))
        (modeSupport (S j)) (hS j)))
    (Q : Fin 3 → Tensor →L[ℝ] ℝ) {r ρ R : ℝ}
    {reference : SmallModes.Base → Tensor}
    (hmargin : ∀ j x, x ∈ U j → ρ + ‖Q j‖ * r ≤ Q j (reference x) ∧
      Q j (reference x) ≤ R - ‖Q j‖ * r) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (H : Fin 3 → ℕ → ℝ) (Pjet : ℕ → ℝ),
      (∀ j m, 1 ≤ H j m) → (∀ m, 0 ≤ Pjet m) →
      ∃ p : Fin 3 → ChartedMeanProfile P,
        (∀ j, (p j).U = U₀) ∧ (∀ j, (p j).O = univ) ∧
        (∀ j m, 0 ≤ (p j).D m) ∧
      ∀ (G : Base → Space) (_hG : ContDiff ℝ ∞ G) (C₀ : ℝ),
      0 ≤ C₀ → C₀ < ρ₀ →
      WeightedBound univ 1 2 C₀
        ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
      ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
      (∀ j m, WeightedBound (linearPhaseChart (ξ j) (hξ j) (U j) (hU j)).target
        s m (H j m) (realTwoJet ((G ∘ planeCoordinateIsometry.symm) ∘
          (linearPhaseChart (ξ j) (hξ j) (U j) (hU j)).symm))) →
      (∀ m j, j ≤ m + 2 → WeightedBound U₀ 1 j
        (Pjet m / (s : ℝ) ^ (j - 2)) G) →
      ∀ (τ ε r' : ℝ), r' ≤ r → 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
      ∃ d : ChartedMeanFamilyData P ε τ s r' ρ R reference,
        d.Fits p ∧ d.G = G ∧ d.phase = φ ∧ d.support = S ∧
        (∀ j, (d.solver j).e = linearPhaseChart (ξ j) (hξ j) (U j) (hU j)) ∧
        (∀ j x, (d.data j).cutoff x = ψ j x) ∧
        (∀ j, (d.data j).form = fun _ => Q j) := by
  classical
  choose a ha hall using fun j => uniform_linear_perturbed_mean_data_all_profiles
    P hP hF (hΩ j) (hU j) (hK j) (hUK j) (hKΩ j) (hξ j) (hImm j) (hgood j)
    (S j) (hS j) hU₀ K₀ hU₀K (hSU₀ j) (hφ j) (hphase j) (ψ j) (Q j) (hmargin j)
  let ρ₀ := min (a 0) (min (a 1) (a 2))
  have hρ₀ : 0 < ρ₀ := lt_min (ha 0) (lt_min (ha 1) (ha 2))
  have hρa (j : Fin 3) : ρ₀ ≤ a j := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ₀,hρ₀,?_⟩
  intro H Pjet hH hPjet
  choose p hpU hpO hpD hdata using fun j => hall j (H j) Pjet (hH j) hPjet
  refine ⟨p,hpU,hpO,hpD,?_⟩
  intro G hG C₀ hC₀ hCρ hclose s hs hs1 hjet hpref τ ε r' hr hτ hτs hε hε1
  choose c d hfit he hcut hform using fun j => hdata j G hG C₀ hC₀
    (hCρ.trans_le (hρa j)) hclose s hs hs1 (hjet j) hpref τ ε hτ hτs hε hε1
  refine ⟨{
    G := G
    smoothG := hG
    phase := φ
    support := S
    solver := c
    data := fun j => (d j).atRadius r' hr
  },?_,rfl,rfl,rfl,he,hcut,hform⟩
  exact fun j => (hfit j).atRadius r' hr

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.uniform_linear_perturbed_mean_family_all_profiles_oai := @OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.uniform_linear_perturbed_mean_family_all_profiles_oai
