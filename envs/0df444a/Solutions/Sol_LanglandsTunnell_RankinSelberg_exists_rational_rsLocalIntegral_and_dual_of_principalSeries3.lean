-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_and_dual_of_principalSeries3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/3e4eaa33-04c1-59c6-b8b9-7f2e51df6002

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
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

import Theorems.Thm_LanglandsTunnell_CubicInduction_coefficientFn_eq_sum_jacquetWhittaker3_of_isWhittakerFunctional3_inv
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_and_dual_of_jacquetWhittaker3_ed2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_and_dual_of_principalSeries3
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

namespace Ws31
namespace RSRAT

open Polynomial

def IsLaur (q : ℂ) (f : ℂ → ℂ) : Prop :=
  ∃ (m : ℤ) (P : Polynomial ℂ), ∀ s : ℂ, f s = q ^ ((m : ℂ) * s) * P.eval (q ^ (-s))

variable {q : ℂ}

theorem cpow_ne_zero' (hq : q ≠ 0) (a : ℂ) : q ^ a ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero hq]; exact Complex.exp_ne_zero _

theorem cpow_neg_nat_mul (n : ℕ) (s : ℂ) : q ^ (-((n : ℂ) * s)) = (q ^ (-s)) ^ n := by
  rw [show -((n : ℂ) * s) = (n : ℂ) * (-s) by ring, Complex.cpow_nat_mul]

theorem IsLaur.congr {f g : ℂ → ℂ} (h : ∀ s, f s = g s) (hg : IsLaur q g) : IsLaur q f := by
  obtain ⟨m, P, hP⟩ := hg; exact ⟨m, P, fun s => (h s).trans (hP s)⟩

theorem IsLaur.zero : IsLaur q (fun _ => 0) := ⟨0, 0, fun s => by simp⟩

theorem IsLaur.const (c : ℂ) : IsLaur q (fun _ => c) := ⟨0, Polynomial.C c, fun s => by simp⟩

theorem IsLaur.monomial (k : ℤ) : IsLaur q (fun s => q ^ ((k : ℂ) * s)) :=
  ⟨k, 1, fun s => by simp⟩

theorem IsLaur.smul {f : ℂ → ℂ} (c : ℂ) (hf : IsLaur q f) : IsLaur q (fun s => c * f s) := by
  obtain ⟨m, P, hP⟩ := hf
  refine ⟨m, Polynomial.C c * P, fun s => ?_⟩
  beta_reduce
  rw [hP s, Polynomial.eval_mul, Polynomial.eval_C]; ring

theorem IsLaur.mul (hq : q ≠ 0) {f g : ℂ → ℂ} (hf : IsLaur q f) (hg : IsLaur q g) :
    IsLaur q (fun s => f s * g s) := by
  obtain ⟨m, P, hP⟩ := hf
  obtain ⟨n, R, hR⟩ := hg
  refine ⟨m + n, P * R, fun s => ?_⟩
  beta_reduce
  rw [hP s, hR s, Polynomial.eval_mul, Int.cast_add, add_mul, Complex.cpow_add _ _ hq]; ring

theorem IsLaur.shift (hq : q ≠ 0) {f : ℂ → ℂ} (k : ℤ) (hf : IsLaur q f) :
    IsLaur q (fun s => q ^ ((k : ℂ) * s) * f s) :=
  IsLaur.mul hq (IsLaur.monomial k) hf

theorem laur_recentre (hq : q ≠ 0) (m' m : ℤ) (hle : m' ≤ m) (P : Polynomial ℂ) (s : ℂ) :
    q ^ ((m' : ℂ) * s) * P.eval (q ^ (-s)) =
      q ^ ((m : ℂ) * s) * (Polynomial.X ^ (m - m').toNat * P).eval (q ^ (-s)) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, m = m' + d := ⟨(m - m').toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
  subst hd
  rw [show ((m' + (d : ℤ) : ℤ) - m').toNat = d by simp, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, ← cpow_neg_nat_mul d s, Int.cast_add, Int.cast_natCast, add_mul,
    Complex.cpow_add _ _ hq, show q ^ (-((d : ℂ) * s)) = (q ^ ((d : ℂ) * s))⁻¹ from Complex.cpow_neg _ _]
  have hne : q ^ ((d : ℂ) * s) ≠ 0 := cpow_ne_zero' hq _
  rw [mul_assoc, ← mul_assoc (q ^ ((d : ℂ) * s)), mul_inv_cancel₀ hne, one_mul]

theorem IsLaur.add (hq : q ≠ 0) {f g : ℂ → ℂ} (hf : IsLaur q f) (hg : IsLaur q g) :
    IsLaur q (fun s => f s + g s) := by
  obtain ⟨m, P, hP⟩ := hf
  obtain ⟨n, R, hR⟩ := hg
  refine ⟨max m n, Polynomial.X ^ (max m n - m).toNat * P + Polynomial.X ^ (max m n - n).toNat * R, fun s => ?_⟩
  beta_reduce
  rw [hP s, hR s, laur_recentre hq m (max m n) (le_max_left _ _) P s,
    laur_recentre hq n (max m n) (le_max_right _ _) R s, Polynomial.eval_add]
  ring

theorem IsLaur.sum (hq : q ≠ 0) {ι : Type} (S : Finset ι) (f : ι → ℂ → ℂ) (hf : ∀ j ∈ S, IsLaur q (f j)) :
    IsLaur q (fun s => ∑ j ∈ S, f j s) := by
  induction S using Finset.induction_on with
  | empty => exact IsLaur.congr (fun s => by simp) IsLaur.zero
  | insert a S ha ih =>
    refine IsLaur.congr (fun s => Finset.sum_insert ha) ?_
    exact IsLaur.add hq (hf a (Finset.mem_insert_self a S)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem IsLaur.prod (hq : q ≠ 0) {ι : Type} (S : Finset ι) (f : ι → ℂ → ℂ) (hf : ∀ j ∈ S, IsLaur q (f j)) :
    IsLaur q (fun s => ∏ j ∈ S, f j s) := by
  induction S using Finset.induction_on with
  | empty => exact IsLaur.congr (fun s => by simp) (IsLaur.const 1)
  | insert a S ha ih =>
    refine IsLaur.congr (fun s => Finset.prod_insert ha) ?_
    exact IsLaur.mul hq (hf a (Finset.mem_insert_self a S)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem IsLaur.reflect (hq : q ≠ 0) {f : ℂ → ℂ} (hf : IsLaur q f) : IsLaur q (fun s => f (-s)) := by
  obtain ⟨m, P, hP⟩ := hf
  refine ⟨P.natDegree - m, P.reverse, fun s => ?_⟩
  beta_reduce
  rw [hP (-s), neg_neg]
  have hx : q ^ s ≠ 0 := cpow_ne_zero' hq _
  letI : Invertible (q ^ s) := invertibleOfNonzero hx
  have hrev : P.reverse.eval (q ^ (-s)) * (q ^ s) ^ P.natDegree = P.eval (q ^ s) := by
    have h1 := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) (q ^ s) P
    rw [invOf_eq_inv, ← Complex.cpow_neg] at h1
    exact h1
  rw [← hrev, ← Complex.cpow_nat_mul, Int.cast_sub, Int.cast_natCast, sub_mul, Complex.cpow_sub _ _ hq,
    show (m : ℂ) * -s = -((m : ℂ) * s) by ring, show q ^ (-((m : ℂ) * s)) = (q ^ ((m : ℂ) * s))⁻¹ from Complex.cpow_neg _ _]
  have h2 : q ^ ((m : ℂ) * s) ≠ 0 := cpow_ne_zero' hq _
  field_simp

theorem IsLaur.rational {f g : ℂ → ℂ} (σ : ℝ) (hfg : ∀ s : ℂ, σ < s.re → g s = f s) (hf : IsLaur q f) :
    ∃ (P Q : Polynomial ℂ) (m : ℤ), Q ≠ 0 ∧
      ∀ s : ℂ, σ < s.re → g s * Q.eval (q ^ (-s)) = q ^ ((m : ℂ) * s) * P.eval (q ^ (-s)) := by
  obtain ⟨m, P, hP⟩ := hf
  exact ⟨P, 1, m, one_ne_zero, fun s hs => by rw [hfg s hs, hP s, Polynomial.eval_one, mul_one]⟩

section PS

variable (p : HeightOneSpectrum (𝓞 ℚ)) (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))

theorem translate_mem (g : LocalGL3 p) (f : ↥(principalSeries3 p lam)) :
    (gl3AmbientRightTranslate (R := ℂ) g (f : LocalGL3 p → ℂ)) ∈ principalSeries3 p lam := by
  obtain ⟨hlc, hN, hT⟩ := f.2
  refine ⟨?_, fun x y z h => ?_, fun a h => ?_⟩
  · exact hlc.comp_continuous (continuous_mul_right g)
  · change (f : LocalGL3 p → ℂ) (upperUnipotent3 x y z * h * g) = (f : LocalGL3 p → ℂ) (h * g)
    rw [mul_assoc]; exact hN x y z (h * g)
  · change (f : LocalGL3 p → ℂ) (diagonal3 p a * h * g) = torusChar3 p lam a * halfModulus3 p a * (f : LocalGL3 p → ℂ) (h * g)
    rw [mul_assoc]; exact hT a (h * g)

theorem coefficientFn_apply (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 p lam)) (g : LocalGL3 p) :
    coefficientFn Λ f g = Λ ⟨gl3AmbientRightTranslate (R := ℂ) g (f : LocalGL3 p → ℂ), translate_mem p lam g f⟩ := rfl

theorem coefficientFn_mul (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 p lam)) (g : LocalGL3 p) :
    (fun h => coefficientFn Λ f (h * g)) =
      coefficientFn Λ ⟨gl3AmbientRightTranslate (R := ℂ) g (f : LocalGL3 p → ℂ), translate_mem p lam g f⟩ := by
  funext h
  rw [coefficientFn_apply, coefficientFn_apply]
  congr 1
  apply Subtype.ext
  funext x
  change (f : LocalGL3 p → ℂ) (x * (h * g)) = (f : LocalGL3 p → ℂ) (x * h * g)
  rw [mul_assoc]

theorem coefficientFn_add (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f f' : ↥(principalSeries3 p lam)) :
    coefficientFn Λ (f + f') = coefficientFn Λ f + coefficientFn Λ f' := by
  funext h
  rw [Pi.add_apply, coefficientFn_apply, coefficientFn_apply, coefficientFn_apply, ← map_add]
  congr 1

theorem coefficientFn_smul (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (c : ℂ) (f : ↥(principalSeries3 p lam)) :
    coefficientFn Λ (c • f) = c • coefficientFn Λ f := by
  funext h
  rw [Pi.smul_apply, coefficientFn_apply, coefficientFn_apply, ← map_smul]
  congr 1

theorem coefficientFn_zero (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) :
    coefficientFn Λ (0 : ↥(principalSeries3 p lam)) = 0 := by
  funext h
  rw [Pi.zero_apply, coefficientFn_apply, ← Λ.map_zero]
  congr 1

theorem exists_eq_coefficientFn_of_mem_gl3CyclicSubspace (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ)
    (f : ↥(principalSeries3 p lam)) (W : LocalGL3 p → ℂ) (hW : W ∈ gl3CyclicSubspace (coefficientFn Λ f)) :
    ∃ f' : ↥(principalSeries3 p lam), W = coefficientFn Λ f' := by
  induction hW using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact ⟨_, coefficientFn_mul p lam Λ f g⟩
  | zero => exact ⟨0, (coefficientFn_zero p lam Λ).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨fx, rfl⟩ := hx
    obtain ⟨fy, rfl⟩ := hy
    exact ⟨fx + fy, (coefficientFn_add p lam Λ fx fy).symm⟩
  | smul c x _ hx =>
    obtain ⟨fx, rfl⟩ := hx
    exact ⟨c • fx, (coefficientFn_smul p lam Λ c fx).symm⟩

end PS

theorem rational_sum (q : ℂ) (hq : q ≠ 0) {n : ℕ} (κ : Fin n → ℂ) (A : Fin n → ℂ → ℂ)
    (P Q : Fin n → Polynomial ℂ) (m : Fin n → ℤ) (σ : Fin n → ℝ) (hQ : ∀ j, Q j ≠ 0)
    (hA : ∀ j, ∀ s : ℂ, σ j < s.re → A j s * (Q j).eval (q ^ (-s)) = q ^ ((m j : ℂ) * s) * (P j).eval (q ^ (-s))) :
    ∃ (P' Q' : Polynomial ℂ) (m' : ℤ), Q' ≠ 0 ∧
      ∀ s : ℂ, (∀ j, σ j < s.re) →
        (∑ j, κ j * A j s) * Q'.eval (q ^ (-s)) = q ^ ((m' : ℂ) * s) * P'.eval (q ^ (-s)) := by
  classical

  have hL : IsLaur q (fun s => ∑ j, κ j * (q ^ ((m j : ℂ) * s) * (P j).eval (q ^ (-s))) *
      ∏ i ∈ Finset.univ.erase j, (Q i).eval (q ^ (-s))) := by
    refine IsLaur.sum hq Finset.univ _ fun j _ => ?_
    refine IsLaur.mul hq (IsLaur.smul (κ j) ⟨m j, P j, fun s => rfl⟩) ?_
    exact IsLaur.prod hq _ _ fun i _ => ⟨0, Q i, fun s => by simp⟩
  obtain ⟨m', P', hP'⟩ := hL
  refine ⟨P', ∏ i, Q i, m', Finset.prod_ne_zero_iff.2 fun i _ => hQ i, fun s hs => ?_⟩
  rw [← hP' s, Polynomial.eval_prod, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_prod_erase Finset.univ (fun i => (Q i).eval (q ^ (-s))) (Finset.mem_univ j), ← hA j s (hs j)]
  ring

end Ws31.RSRAT

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

open Ws31.RSRAT in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (ω₃ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hlamω : lam 0 * lam 1 * lam 2 = ω₃)
    (hlam : ∀ i : Fin 3, IsLocallyConstant (lam i))
    (hlamu : ∀ (i : Fin 3) (x : (p.adicCompletion ℚ)ˣ), ‖((lam i x : ℂˣ) : ℂ)‖ = 1)
    (W2 : LocalGL3 p → ℂ)
    (hmem : ∃ (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 p lam)),
      IsWhittakerFunctional3 (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ Λ ∧ W2 = coefficientFn Λ f)
    (hW2law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W2)
    (hW2sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W2 (g * k) = W2 g)
    (hω2 : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W2 (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * W2 h)

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    :
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ W₃ ∈ gl3CyclicSubspace W2,
          ∃ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧

            (∀ s : ℂ, σ₂ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => W₃ (iotaGL g)) w₂ * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
            (∀ s : ℂ, σ₃ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by
  intro μ₂ _ μN₂ _ w₂ hw₂ W₃ hW₃
  classical
  obtain ⟨Λ, f, hΛ, hW2⟩ := hmem

  rw [hW2] at hW₃
  obtain ⟨f₃, rfl⟩ := exists_eq_coefficientFn_of_mem_gl3CyclicSubspace p lam Λ f W₃ hW₃

  obtain ⟨n, κ, xs, ys, zs, Φs, hΦs, hsum⟩ :=
    LanglandsTunnell.CubicInduction.coefficientFn_eq_sum_jacquetWhittaker3_of_isWhittakerFunctional3_inv
      p lam hlam Λ hΛ f₃

  set Wj : Fin n → LocalGL3 p → ℂ := fun j h => jacquetWhittaker3 p lam (Φs j)
      (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 (xs j) (ys j) (zs j) * antidiagonal3 p)) with hWj
  have hsum' : coefficientFn Λ f₃ = fun h => ∑ j, κ j * Wj j h := by
    rw [hsum]

  have hj : ∀ j : Fin n, _ := fun j =>
    LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_and_dual_of_jacquetWhittaker3_ed2
      p lam hlam (Φs j) (hΦs j) (xs j) (ys j) (zs j) (Wj j) rfl θ₀ N hN w₂base hw₂law hw₂K hw₂ne
      hw₂irr hw₂adm hcentral w₀p hw₀p μ₂ μN₂ w₂ hw₂
  choose P Pd Q Qd m md σ σd hQ hQd hconv hconvd hrat hratd using hj

  set q : ℂ := (Ideal.absNorm p.asIdeal : ℂ) with hq
  have hq0 : q ≠ 0 := by
    have h0 : Ideal.absNorm p.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact p.ne_bot
    rw [hq]; exact_mod_cast h0

  set σ₂ : ℝ := ∑ j, |σ j| with hσ₂
  set σ₃ : ℝ := ∑ j, |σd j| with hσ₃
  have hσ₂le : ∀ j, σ j ≤ σ₂ := fun j =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |σ j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))
  have hσ₃le : ∀ j, σd j ≤ σ₃ := fun j =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |σd j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))

  set δ : GL (Fin 2) (p.adicCompletion ℚ) → ℝ := fun g =>
    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) with hδ
  set wd : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun g => ((δ g : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g) with hwd
  set μq := μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂) with hμq

  have hprim : ∀ s : ℂ, (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      (coefficientFn Λ f₃ (iotaGL g) * w₂ g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2)) =
      fun g => ∑ j, κ j * ((Wj j (iotaGL g) * w₂ g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2)) := by
    intro s; funext g
    rw [hsum', Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hdualfn : dualWhittakerFn3 (coefficientFn Λ f₃) = fun x => ∑ j, κ j * dualWhittakerFn3 (Wj j) x := by
    funext x
    simp only [dualWhittakerFn3_apply, hsum']
  have hdual : ∀ s : ℂ, (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      (dualWhittakerFn3 (coefficientFn Λ f₃) (iotaGL g) * wd g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2)) =
      fun g => ∑ j, κ j * ((dualWhittakerFn3 (Wj j) (iotaGL g) * wd g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2)) := by
    intro s; funext g
    rw [hdualfn, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

  obtain ⟨P', Q', m', hQ', hrat'⟩ := rational_sum q hq0 κ
    (fun j s => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂ δ s
      (fun g => Wj j (iotaGL g)) w₂) P Q m σ hQ hrat
  obtain ⟨Pd', Qd', md', hQd', hratd'⟩ := rational_sum q hq0 κ
    (fun j s => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂ δ s
      (fun g => dualWhittakerFn3 (Wj j) (iotaGL g)) wd) Pd Qd md σd hQd hratd
  refine ⟨P', Pd', Q', Qd', m', md', σ₂, σ₃, hQ', hQd', ?_, ?_, ?_, ?_⟩
  ·
    intro s hs
    rw [hprim s]
    exact integrable_finset_sum _ fun j _ => (hconv j s (lt_of_le_of_lt (hσ₂le j) hs)).const_mul (κ j)
  ·
    intro s hs
    rw [hdual s]
    exact integrable_finset_sum _ fun j _ => (hconvd j s (lt_of_le_of_lt (hσ₃le j) hs)).const_mul (κ j)
  ·
    intro s hs
    have hlin : RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂ δ s
        (fun g => coefficientFn Λ f₃ (iotaGL g)) w₂ =
        ∑ j, κ j * RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂ δ s
          (fun g => Wj j (iotaGL g)) w₂ := by
      unfold RSCarrier.rsLocalIntegral
      rw [show (fun g : GL (Fin 2) (p.adicCompletion ℚ) => coefficientFn Λ f₃ (iotaGL g) * w₂ g * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2)) =
        fun g => ∑ j, κ j * ((Wj j (iotaGL g) * w₂ g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2)) from hprim s,
        integral_finset_sum _ fun j _ => (hconv j s (lt_of_le_of_lt (hσ₂le j) hs)).const_mul (κ j)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
    rw [hlin]
    exact hrat' s fun j => lt_of_le_of_lt (hσ₂le j) hs
  ·
    intro s hs
    have hlin : RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂ δ s
        (fun g => dualWhittakerFn3 (coefficientFn Λ f₃) (iotaGL g)) wd =
        ∑ j, κ j * RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂ δ s
          (fun g => dualWhittakerFn3 (Wj j) (iotaGL g)) wd := by
      unfold RSCarrier.rsLocalIntegral
      rw [show (fun g : GL (Fin 2) (p.adicCompletion ℚ) => dualWhittakerFn3 (coefficientFn Λ f₃) (iotaGL g) * wd g * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2)) =
        fun g => ∑ j, κ j * ((dualWhittakerFn3 (Wj j) (iotaGL g) * wd g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2)) from hdual s,
        integral_finset_sum _ fun j _ => (hconvd j s (lt_of_le_of_lt (hσ₃le j) hs)).const_mul (κ j)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
    rw [hlin]
    exact hratd' s fun j => lt_of_le_of_lt (hσ₃le j) hs

end S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_and_dual_of_principalSeries3
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_and_dual_of_principalSeries3 (solution)
