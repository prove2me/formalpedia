-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.forall_localZeta31_fe_of_twist_modulus_cpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/fa193ddb-661c-5061-beb8-e33b5d279d2e

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_forall_localZeta31_fe_of_twist_modulus_cpow

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_forall_localZeta31_fe_of_twist_modulus_cpow.LanglandsTunnell.CubicInduction"

open scoped nonZeroDivisors

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.modulus TateLocal.modulus_ne_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "transposeInv3 iotaGL LocalGL3 diagUnitGL2 localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lowerUnipotent21 dualWhittakerFn3 weylPrime3"
namespace TwistShift
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem modulus_cast_ne_zero (a : (v.adicCompletion ℚ)ˣ) :
    ((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (TateLocal.modulus_ne_zero a.ne_zero))

theorem twist_factor (η χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (t : ℂ)
    (hχ : ∀ a : (v.adicCompletion ℚ)ˣ,
      ((χ a : ℂˣ) : ℂ) = ((η a : ℂˣ) : ℂ) * (((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (a : (v.adicCompletion ℚ)ˣ) (s : ℂ) :
    ((χ a : ℂˣ) : ℂ) * ((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) =
      ((η a : ℂˣ) : ℂ) * ((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + t - 1) := by
  rw [hχ a, mul_assoc, ← Complex.cpow_add _ _ (modulus_cast_ne_zero v a)]
  congr 2
  ring

theorem twist_factor_inv (η χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (t : ℂ)
    (hχ : ∀ a : (v.adicCompletion ℚ)ˣ,
      ((χ a : ℂˣ) : ℂ) = ((η a : ℂˣ) : ℂ) * (((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (a : (v.adicCompletion ℚ)ˣ) (s : ℂ) :
    ((χ⁻¹ a : ℂˣ) : ℂ) * ((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) =
      ((η⁻¹ a : ℂˣ) : ℂ) * ((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - t - 1) := by
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hχ a,
    mul_inv, ← Complex.cpow_neg, mul_assoc, ← Complex.cpow_add _ _ (modulus_cast_ne_zero v a)]
  congr 2
  ring

variable {mT : MeasurableSpace (v.adicCompletion ℚ)ˣ} {mA : MeasurableSpace (v.adicCompletion ℚ)}

theorem localZeta30_twist (μ : Measure (v.adicCompletion ℚ)ˣ) (W : LocalGL3 v → ℂ)
    (η χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (t : ℂ)
    (hχ : ∀ a : (v.adicCompletion ℚ)ˣ,
      ((χ a : ℂˣ) : ℂ) = ((η a : ℂˣ) : ℂ) * (((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (s : ℂ) (g : LocalGL3 v) :
    localZeta30 v μ W χ s g = localZeta30 v μ W η (s + t) g := by
  unfold localZeta30
  congr 1
  funext a
  rw [mul_assoc, twist_factor v η χ t hχ a s, ← mul_assoc]

theorem localZetaDual31_twist (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ))
    (W : LocalGL3 v → ℂ) (η χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (t : ℂ)
    (hχ : ∀ a : (v.adicCompletion ℚ)ˣ,
      ((χ a : ℂˣ) : ℂ) = ((η a : ℂˣ) : ℂ) * (((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (s : ℂ) (g : LocalGL3 v) :
    localZetaDual31 v μ ν W χ s g = localZetaDual31 v μ ν W η (s - t) g := by
  unfold localZetaDual31 localZeta31
  congr 1
  funext a
  rw [mul_assoc, twist_factor_inv v η χ t hχ a s, ← mul_assoc]

theorem isLocalZeta30ConvergentAbove_twist (μ : Measure (v.adicCompletion ℚ)ˣ) (W : LocalGL3 v → ℂ)
    (η χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (t : ℂ)
    (hχ : ∀ a : (v.adicCompletion ℚ)ˣ,
      ((χ a : ℂˣ) : ℂ) = ((η a : ℂˣ) : ℂ) * (((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (g : LocalGL3 v) (σ₀ : ℝ) (h : IsLocalZeta30ConvergentAbove v μ W η g σ₀) :
    IsLocalZeta30ConvergentAbove v μ W χ g (σ₀ - t.re) := by
  intro s hs
  have h' := h (s + t) (by rw [Complex.add_re]; linarith)
  have e : (fun a : (v.adicCompletion ℚ)ˣ => W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
        ((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) =
      (fun a : (v.adicCompletion ℚ)ˣ => W (iotaGL (diagUnitGL2 a) * g) * ((η a : ℂˣ) : ℂ) *
        ((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + t - 1)) :=
    funext fun a => by rw [mul_assoc, twist_factor v η χ t hχ a s, ← mul_assoc]
  rw [e]
  exact h'

theorem isLocalZeta31ConvergentAbove_twist_inv (μ : Measure (v.adicCompletion ℚ)ˣ)
    (ν : Measure (v.adicCompletion ℚ)) (W : LocalGL3 v → ℂ)
    (η χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (t : ℂ)
    (hχ : ∀ a : (v.adicCompletion ℚ)ˣ,
      ((χ a : ℂˣ) : ℂ) = ((η a : ℂˣ) : ℂ) * (((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (g : LocalGL3 v) (σ₁ : ℝ) (h : IsLocalZeta31ConvergentAbove v μ ν W η⁻¹ g σ₁) :
    IsLocalZeta31ConvergentAbove v μ ν W χ⁻¹ g (σ₁ + t.re) := by
  intro s hs
  have h' := h (s - t) (by rw [Complex.sub_re]; linarith)
  have e : (fun q : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
        W (iotaGL (diagUnitGL2 q.1) * lowerUnipotent21 q.2 * g) * ((χ⁻¹ q.1 : ℂˣ) : ℂ) *
          ((TateLocal.modulus (q.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) =
      (fun q : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
        W (iotaGL (diagUnitGL2 q.1) * lowerUnipotent21 q.2 * g) * ((η⁻¹ q.1 : ℂˣ) : ℂ) *
          ((TateLocal.modulus (q.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - t - 1)) :=
    funext fun q => by rw [mul_assoc, twist_factor_inv v η χ t hχ q.1 s, ← mul_assoc]
  rw [e]
  exact h'

theorem comp_C_mul_X_ne_zero (Q : Polynomial ℂ) (hQ : Q ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    Q.comp (Polynomial.C c * Polynomial.X) ≠ 0 := by
  intro h0
  have hdeg : (Polynomial.C c * Polynomial.X).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_C_mul_X _ hc]; exact one_ne_zero
  have hl := Polynomial.leadingCoeff_comp (p := Q) hdeg
  rw [h0, Polynomial.leadingCoeff_zero, Polynomial.leadingCoeff_C_mul_X] at hl
  exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hQ) (pow_ne_zero _ hc) hl.symm

end LanglandsTunnell.CubicInduction.TwistShift

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (W₃base : LocalGL3 p → ℂ)
    (η χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (t : ℂ)
    (hχ : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((χ a : ℂˣ) : ℂ) = ((η a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (C : ℂ) (k : ℤ)
    (h31 :
              ∀ g : LocalGL3 p,
                letI := localBorel ℚ p
                ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
                  IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
                    W₃base η g σ₀ ∧
                  (∀ s : ℂ, σ₀ < s.re →
                    localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base η s g *
                      Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                    Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
                  IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) (η)⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
                  (∀ s : ℂ, σ₁ < (1 - s).re →
                    localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
                      W₃base η (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                    Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
                      (C * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s)))) :
    ∀ g : LocalGL3 p,
                letI := localBorel ℚ p
                ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
                  IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
                    W₃base χ g σ₀ ∧
                  (∀ s : ℂ, σ₀ < s.re →
                    localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base χ s g *
                      Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                    Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
                  IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) (χ)⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
                  (∀ s : ℂ, σ₁ < (1 - s).re →
                    localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
                      W₃base χ (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                    Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
                      (C * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * t) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s))) := by
  intro g
  obtain ⟨Q₁, Q₂, n, σ₀, σ₁, hQ₂, hc0, hZ, hc1, hZd⟩ := h31 g
  have hN : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast fun h => p.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hc : (Ideal.absNorm p.asIdeal : ℂ) ^ (-t) ≠ 0 := fun h => hN ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have e1 : ∀ s : ℂ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-t) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-s) =
      (Ideal.absNorm p.asIdeal : ℂ) ^ (-(s + t)) := fun s => by
    rw [← Complex.cpow_add _ _ hN]; congr 1; ring
  have e2 : ∀ (m : ℤ) (s : ℂ), (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (s + t)) =
      (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * t) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) := fun m s => by
    rw [← Complex.cpow_add _ _ hN]; congr 1; ring
  refine ⟨Polynomial.C ((Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * t)) *
      Q₁.comp (Polynomial.C ((Ideal.absNorm p.asIdeal : ℂ) ^ (-t)) * Polynomial.X),
    Q₂.comp (Polynomial.C ((Ideal.absNorm p.asIdeal : ℂ) ^ (-t)) * Polynomial.X), n, σ₀ - t.re, σ₁ + t.re,
    LanglandsTunnell.CubicInduction.TwistShift.comp_C_mul_X_ne_zero Q₂ hQ₂ _ hc,
    LanglandsTunnell.CubicInduction.TwistShift.isLocalZeta30ConvergentAbove_twist p _ W₃base η χ t hχ g σ₀ hc0,
    ?_,
    LanglandsTunnell.CubicInduction.TwistShift.isLocalZeta31ConvergentAbove_twist_inv p _ _ _ η χ t hχ _ σ₁ hc1,
    ?_⟩
  · intro s hs
    have hS := hZ (s + t) (by rw [Complex.add_re]; linarith)
    rw [LanglandsTunnell.CubicInduction.TwistShift.localZeta30_twist p _ W₃base η χ t hχ s g]
    simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [e1 s, hS, e2 n s]
    ring
  · intro s hs
    have hS := hZd (s + t) (by rw [Complex.sub_re, Complex.add_re]; rw [Complex.sub_re] at hs; linarith)
    rw [LanglandsTunnell.CubicInduction.TwistShift.localZetaDual31_twist p _ _ W₃base η χ t hχ (1 - s) g,
      show (1 : ℂ) - s - t = 1 - (s + t) by ring]
    simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [e1 s, hS, e2 n s, e2 k s]
    ring

end S_LanglandsTunnell_CubicInduction_forall_localZeta31_fe_of_twist_modulus_cpow
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_forall_localZeta31_fe_of_twist_modulus_cpow (solution)
