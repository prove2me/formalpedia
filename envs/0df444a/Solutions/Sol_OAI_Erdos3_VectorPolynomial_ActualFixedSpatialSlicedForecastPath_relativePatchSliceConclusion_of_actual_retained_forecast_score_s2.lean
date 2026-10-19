-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.relativePatchSliceConclusion_of_actual_retained_forecast_score_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:02:57.779271+00:00
-- url     : https://prove2.me/submissions/58967b4e-4763-4247-ab56-2801def6d239

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B303
import Definitions.Def_OAIE3v2B262
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialForecastPath_reference_inactive_goodPrimeDeletion_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_targetAt_mean_mul_bufferedScalarScore_eq_fin_s2
import Theorems.Thm_OAI_Erdos3_exists_spatially_localized_patch_s2
import Theorems.Thm_OAI_Erdos3_fixedSpatialKernelDensity_probability_density_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteImageProducts
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteImageMass_pi {D : Type*} [Fintype D] [DecidableEq D]
    {X Z : D → Type*} [∀ d, Fintype (X d)] [∀ d, DecidableEq (Z d)]
    (p : ∀ d, FiniteProbabilityWeights (X d)) (Y : ∀ d, X d → Z d) (z : ∀ d, Z d) :
    finiteImageMass (FiniteProbabilityWeights.pi p) (fun x d => Y d (x d)) z =
      ∏ d, finiteImageMass (p d) (Y d) (z d) := by
  classical
  have h := FiniteProbabilityWeights.eventProbability_pi p (fun d x => Y d x = z d)
  have he : finiteImageMass (FiniteProbabilityWeights.pi p) (fun x d => Y d (x d)) z =
      (FiniteProbabilityWeights.pi p).eventProbability (fun x => ∀ d, Y d (x d) = z d) := by
    unfold finiteImageMass FiniteProbabilityWeights.eventProbability
    congr 1
    funext x
    by_cases hx : ∀ d, Y d (x d) = z d
    · simp [hx]
    · have hf : (fun d => Y d (x d)) ≠ z := fun e => hx (fun d => congrFun e d)
      simp only [hf, hx, ite_false]
  have hr : (∏ d, (p d).eventProbability (fun x => Y d x = z d)) =
      ∏ d, finiteImageMass (p d) (Y d) (z d) := by
    apply Finset.prod_congr rfl
    intro d _
    unfold FiniteProbabilityWeights.eventProbability finiteImageMass
    congr 1
    funext x
    by_cases hx : Y d x = z d <;> simp only [hx, ite_true, ite_false]
  exact he.trans (h.trans hr)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialPatch

variable {σ : Type*} {s d D E : ℕ}

theorem value_mem_Icc (A : PolynomialPatch σ s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end PolynomialPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceNormalizedCell
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open _root_.MvPolynomial

variable {ι : Type*} {N : ι → ℕ} {q s d : ℕ}

theorem reparamPatch_value (A : ResidueBoxSlice N q) (P : PolynomialPatch ι s d)
    (j : ∀ i, Fin (A.length i)) :
    (A.reparamPatch P).value (fun i => ((j i).val : ℝ)) =
      P.value (fun i => ((A.point j i).val : ℝ)) := by
  rw [reparamPatch, PolynomialPatch.reparam_value]
  congr 1
  funext i
  simp [parameters, point]

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedIntervalWindow
namespace OAI

section

namespace Erdos3

open MeasureTheory _root_.Set

theorem intervalWindow_mem_Icc (a b t : ℝ) : intervalWindow a b t ∈ Icc (0 : ℝ) 1 := by
  by_cases ht : t ∈ Ioc a b <;> simp [intervalWindow, ht]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

omit [∀ d, Fintype (I d)] in
theorem sigmaAxisWeight_nonneg (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d y, 0 ≤ w d y) (x : (Σ d, I d) → ℝ) : 0 ≤ sigmaAxisWeight w x :=
  tensorCutoffWeight_nonneg w hw _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialImage
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {L Tag V : Type*} [Fintype L]

theorem crtInput_integerPolynomial_eval (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (F : MvPolynomial V ℤ) (x : ∀ l : L, V → ZMod (q l)) (l : L) :
    ZMod.prodEquivPi q hq
      (MvPolynomial.eval₂ (Int.castRingHom (ZMod (∏ k, q k))) (crtInput q hq x) F) l =
        MvPolynomial.eval₂ (Int.castRingHom (ZMod (q l))) (x l) F := by
  let e := ZMod.prodEquivPi q hq
  let φ := (Pi.evalRingHom (fun k => ZMod (q k)) l).comp e.toRingHom
  change φ (MvPolynomial.eval₂ _ _ F) = _
  rw [MvPolynomial.hom_eval₂]
  have hc : φ.comp (Int.castRingHom (ZMod (∏ k, q k))) =
      Int.castRingHom (ZMod (q l)) := Subsingleton.elim _ _
  rw [hc]
  congr 1
  funext v
  exact congrFun (e.apply_symm_apply (fun k => x k v)) l

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularMultilinearAmbientSublevel
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Classical BigOperators

variable {I J R : Type*} [CommRing R]

theorem eval_conditionPolynomial (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) (y : J → R) :
    eval y (conditionPolynomial f hf v P) = eval (Function.extend f y v) P := by
  unfold conditionPolynomial
  induction P using MvPolynomial.induction_on with
  | C c => simp only [polynomialTranslate_C, killCompl_C, eval_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP, polynomialTranslate_X, map_add, killCompl_C, eval_C, eval_X]
    congr 1
    by_cases hi : i ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hi
      simp only [show f j ∈ Set.range f from ⟨j, rfl⟩, ite_true, add_zero,
        hf.extend_apply]
      rw [← rename_X f j, killCompl_rename_app, eval_X]
    · simp only [hi, ite_false, Function.extend_apply' y v i hi]
      have hz : killCompl hf (X i : MvPolynomial I R) = 0 := by
        simp only [killCompl, aeval_X, hi, dite_false]
      rw [hz, map_zero, zero_add]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPatchReparam
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace WeightedParameterPatch

variable {σ : Type*} {p : σ → ℕ} {s d : ℕ}

theorem value_mem_Icc (A : WeightedParameterPatch σ p s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end WeightedParameterPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BufferedIntegerLift
namespace OAI

section

namespace Erdos3

namespace PatchKernel

theorem buffered_sum_eq_nearest {m : ℕ} (Ψ : PatchKernel m) (x : Fin m → ℝ)
    (f : (Fin m → ℤ) → ℝ) :
    (∑' β, Ψ.value (fun i => x i - (β i : ℝ)) * f β) =
      Ψ.value (fun i => x i - (nearestIntegerLift x i : ℝ)) * f (nearestIntegerLift x) := by
  classical
  apply tsum_eq_single (nearestIntegerLift x)
  intro γ hγ
  have hzero : Ψ.value (fun i => x i - (γ i : ℝ)) = 0 := by
    by_contra hn
    exact hγ (Ψ.buffered_lift_unique x _ γ (nearestIntegerLift_close x) hn)
  rw [hzero, zero_mul]

end PatchKernel
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.BufferedScoreDiscount
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem positive_score_discount_pointwise {a b W w δ ε : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 ≤ w)
    (hlower : (1 - δ) * w ≤ W) (hupper : W ≤ (1 + δ) * w)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ) :
    (a - b) * W ≤ (1 + δ) * (a - (1 - ε) * b) * w := by
  have hpos := mul_le_mul_of_nonneg_left hupper ha
  have hneg := mul_le_mul_of_nonneg_left hlower hb
  have hbase := mul_le_mul_of_nonneg_right hdiscount (mul_nonneg hb hw)
  nlinarith

theorem positive_score_discount {Ω : Type*} [Fintype Ω]
    (a b W w : Ω → ℝ) {δ ε S : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) (hw : ∀ x, 0 ≤ w x)
    (hlower : ∀ x, (1 - δ) * w x ≤ W x) (hupper : ∀ x, W x ≤ (1 + δ) * w x)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hscore : S ≤ 𝔼 x, (a x - b x) * W x) :
    S / (1 + δ) ≤ 𝔼 x, (a x - (1 - ε) * b x) * w x := by
  apply (div_le_iff₀ (by linarith : 0 < 1 + δ)).mpr
  calc
    S ≤ 𝔼 x, (a x - b x) * W x := hscore
    _ ≤ 𝔼 x, (1 + δ) * ((a x - (1 - ε) * b x) * w x) := by
      apply Finset.expect_le_expect
      intro x _
      simpa only [mul_assoc] using positive_score_discount_pointwise
        (ha x) (hb x) (hw x) (hlower x) (hupper x) hdiscount
    _ = _ := by rw [← Finset.mul_expect, mul_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem buffered_score_discount {Ω : Type*} [Fintype Ω] {m : ℕ}
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ)
    (T W w : Ω → (Fin m → ℤ) → ℝ) (f : Ω → ℝ) {lam δ ε S : ℝ}
    (hδ : 0 ≤ δ) (hf : ∀ u, 0 ≤ f u) (hlam : 0 ≤ lam)
    (hT : ∀ u β, 0 ≤ T u β) (hw : ∀ u β, 0 ≤ w u β)
    (hlower : ∀ u β, (1 - δ) * w u β ≤ W u β)
    (hupper : ∀ u β, W u β ≤ (1 + δ) * w u β)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hscore : S ≤ 𝔼 u, (f u - lam) * ∑' β,
      χ.value (fun i => x u i - (β i : ℝ)) * W u β * T u β) :
    S / (1 + δ) ≤ 𝔼 u, (f u - (1 - ε) * lam) * ∑' β,
      χ.value (fun i => x u i - (β i : ℝ)) * w u β * T u β := by
  let β : Ω → Fin m → ℤ := fun u => nearestIntegerLift (x u)
  let cut : Ω → ℝ := fun u => χ.value (fun i => x u i - (β u i : ℝ)) * T u (β u)
  have hcut (u) : 0 ≤ cut u := mul_nonneg (χ.nonneg _) (hT u _)
  have hsum (U : Ω → (Fin m → ℤ) → ℝ) (u) :
      (∑' b, χ.value (fun i => x u i - (b i : ℝ)) * U u b * T u b) =
        χ.value (fun i => x u i - (β u i : ℝ)) * U u (β u) * T u (β u) := by
    simpa only [mul_assoc] using χ.buffered_sum_eq_nearest (x u) (fun b => U u b * T u b)
  have hsource : S ≤ 𝔼 u, (f u * cut u - lam * cut u) * W u (β u) := by
    apply hscore.trans_eq
    apply Finset.expect_congr rfl
    intro u _
    rw [hsum W]
    dsimp only [cut]
    ring
  have h := positive_score_discount (fun u => f u * cut u) (fun u => lam * cut u)
    (fun u => W u (β u)) (fun u => w u (β u)) hδ
    (fun u => mul_nonneg (hf u) (hcut u)) (fun u => mul_nonneg hlam (hcut u))
    (fun u => hw u _) (fun u => hlower u _) (fun u => hupper u _) hdiscount hsource
  apply h.trans_eq
  apply Finset.expect_congr rfl
  intro u _
  rw [hsum w]
  dsimp only [cut]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialInputAffineLaw
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

omit [Fintype V] in

theorem crtPrimePowerIntegerPolynomialOutput_reduce {s : ℕ} {J : Fin s → Type*}
    (p A e : L → ℕ) [NeZero (∏ l, p l ^ A l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (F : ∀ j, J j → MvPolynomial V ℤ) (r : ∀ l, V → ZMod (p l ^ A l))
    (x : ∀ l, V → ZMod (p l ^ A l)) (j : Sigma J) :
    (crtPrimePowerIntegerPolynomialOutput p A e hq F r x j : ZMod (∏ l, p l ^ A l)) =
      crtPrimePowerPolynomialMap p A e hq F r x j.1 j.2 := by
  unfold crtPrimePowerIntegerPolynomialOutput crtPrimePowerPolynomialMap
  change (Int.castRingHom (ZMod (∏ l, p l ^ A l))) (eval₂ (RingHom.id ℤ) _ _) = _
  rw [MvPolynomial.hom_eval₂, RingHom.comp_id]
  congr 1
  funext v
  simp only [Int.coe_castRingHom, Int.cast_natCast, ZMod.natCast_zmod_val]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem finiteImageMass_outputEquiv {X Z W : Type*} [Fintype X]
    [DecidableEq Z] [DecidableEq W] (law : FiniteProbabilityWeights X)
    (Y : X → Z) (e : Z ≃ W) (z : Z) :
    finiteImageMass law (fun x => e (Y x)) (e z) = finiteImageMass law Y z := by
  unfold finiteImageMass
  simp only [e.injective.eq_iff]

theorem crt_integer_polynomial_rational_density_product
    {L V : Type*} [Fintype L] [Fintype V] {s : ℕ}
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (F : ∀ j, J j → MvPolynomial V ℤ)
    (r : ∀ l, V → ZMod (p l ^ A l))
    (z : Sigma J → ZMod (∏ l, p l ^ A l)) :
    let : NeZero (∏ l, p l ^ A l) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
    rationalOutputDensity (crtPrimePowerPolynomialLaw (V := V) p A)
      (crtPrimePowerIntegerPolynomialOutput p A e hq F r) (∏ l, p l ^ A l) z =
      ∏ l, rationalOutputDensity (FiniteProbabilityWeights.uniform (V → ZMod (p l ^ A l)))
        (localPrimePowerIntegerPolynomialOutput (p l) (A l) (e l) F (r l)) (p l ^ A l)
        (fun j => ZMod.castHom (Finset.dvd_prod_of_mem (fun l => p l ^ A l)
          (Finset.mem_univ l)) (ZMod (p l ^ A l)) (z j)) := by
  let : NeZero (∏ l, p l ^ A l) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
  let outputEquiv : (Sigma J → ZMod (∏ l, p l ^ A l)) ≃
      (∀ l, Sigma J → ZMod (p l ^ A l)) :=
    (taggedPolynomialOutputCurry J _).toEquiv |>.trans
      ((taggedOutputCRTEquiv J (fun l => p l ^ A l) hq).toEquiv.trans
        (Equiv.piCongrRight (fun l => (taggedPolynomialOutputCurry J (p l ^ A l)).symm.toEquiv)))
  let localLaw := fun l => FiniteProbabilityWeights.uniform (V → ZMod (p l ^ A l))
  let Y := fun (l : L) (x : V → ZMod (p l ^ A l)) (j : Sigma J) =>
    (localPrimePowerIntegerPolynomialOutput (p l) (A l) (e l) F (r l) x j : ZMod (p l ^ A l))
  let globalY := fun (x : ∀ l, V → ZMod (p l ^ A l)) (j : Sigma J) =>
    (crtPrimePowerIntegerPolynomialOutput p A e hq F r x j : ZMod (∏ l, p l ^ A l))
  have heval (x : ∀ l, V → ZMod (p l ^ A l)) :
      outputEquiv (globalY x) = fun l => Y l (x l) := by
    funext l j
    change ZMod.prodEquivPi (fun l => p l ^ A l) hq (globalY x j) l = Y l (x l) j
    dsimp only [globalY, Y]
    rw [crtPrimePowerIntegerPolynomialOutput_reduce,
      localPrimePowerIntegerPolynomialOutput_reduce]
    exact crtInput_integerPolynomial_eval (fun l => p l ^ A l) hq (F j.1 j.2)
      (fun l v => r l v + (p l : ZMod (p l ^ A l)) ^ e l * x l v) l
  have hmass : finiteImageMass (FiniteProbabilityWeights.pi localLaw) globalY z =
      ∏ l, finiteImageMass (localLaw l) (Y l) (outputEquiv z l) := by
    rw [← finiteImageMass_outputEquiv _ globalY outputEquiv z]
    simp_rw [heval]
    exact finiteImageMass_pi localLaw Y (outputEquiv z)
  have hcard : Fintype.card (Sigma J → ZMod (∏ l, p l ^ A l)) =
      ∏ l, Fintype.card (Sigma J → ZMod (p l ^ A l)) :=
    (Fintype.card_congr outputEquiv).trans Fintype.card_pi
  change (Fintype.card (Sigma J → ZMod (∏ l, p l ^ A l)) : ℝ) *
      finiteImageMass (FiniteProbabilityWeights.pi localLaw) globalY z = _
  rw [hmass, hcard, Nat.cast_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l _
  unfold rationalOutputDensity
  congr 1
  apply congrArg (finiteImageMass (localLaw l) (Y l))
  funext j
  exact ZMod.prodEquivPi_apply (fun l => p l ^ A l) hq (z j) l

theorem crt_integer_polynomial_rational_inactive_density_product
    {L V I Z : Type*} [Fintype L] [Fintype V] [Fintype I] {s : ℕ}
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (inactive : FiniteProbabilityWeights I) (gridPoint : I → Z)
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (F : I → ∀ j, J j → MvPolynomial V ℤ)
    (r : I → ∀ l, V → ZMod (p l ^ A l))
    (gridVolume : ℝ) (z : Z) (β : Sigma J → ZMod (∏ l, p l ^ A l)) :
    let : NeZero (∏ l, p l ^ A l) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
    rationalInactiveForecast inactive (fun _ => crtPrimePowerPolynomialLaw (V := V) p A)
      gridPoint (fun i => crtPrimePowerIntegerPolynomialOutput p A e hq (F i) (r i))
      (∏ l, p l ^ A l) gridVolume z β =
      gridVolume * inactive.fiberMean gridPoint z (fun i =>
        ∏ l, rationalOutputDensity (FiniteProbabilityWeights.uniform (V → ZMod (p l ^ A l)))
          (localPrimePowerIntegerPolynomialOutput (p l) (A l) (e l) (F i) (r i l)) (p l ^ A l)
          (fun j => ZMod.castHom (Finset.dvd_prod_of_mem (fun l => p l ^ A l)
            (Finset.mem_univ l)) (ZMod (p l ^ A l)) (β j))) := by
  let : NeZero (∏ l, p l ^ A l) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
  unfold rationalInactiveForecast
  congr 1
  apply congrArg (inactive.fiberMean gridPoint z)
  funext i
  exact crt_integer_polynomial_rational_density_product p A e hq (F i) (r i) β

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem crt_integer_polynomial_retained_inactive_density_product
    {L V I Z : Type*} [Fintype L] [Fintype V] [Fintype I] {s : ℕ}
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (inactive : FiniteProbabilityWeights I) (gridPoint : I → Z)
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (F : I → ∀ j, J j → MvPolynomial V ℤ)
    (r : I → ∀ l, V → ZMod (p l ^ A l))
    (retained : Finset L) (gridVolume : ℝ) (z : Z)
    (β : Sigma J → ZMod (∏ l, p l ^ A l)) :
    letI : DecidableEq retained := Classical.decEq retained
    let p' : retained → ℕ := fun l => p l.val
    let A' : retained → ℕ := fun l => A l.val
    let e' : retained → ℕ := fun l => e l.val
    let hq' : Pairwise (fun l k : retained => (p' l ^ A' l).Coprime (p' k ^ A' k)) :=
      fun _l _k hne => hq (fun heq => hne (Subtype.ext heq))
    letI : NeZero (∏ l : retained, p' l ^ A' l) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l.val)))⟩
    rationalInactiveForecast inactive
      (fun _ => crtPrimePowerPolynomialLaw (V := V) p' A') gridPoint
      (fun i => crtPrimePowerIntegerPolynomialOutput p' A' e' hq' (F i) (fun l => r i l.val))
      (∏ l : retained, p' l ^ A' l) gridVolume z
      (fun j => ZMod.castHom (retainedPrimePowerModulus_dvd p A retained)
        (ZMod (∏ l : retained, p' l ^ A' l)) (β j)) =
      gridVolume * inactive.fiberMean gridPoint z (fun i =>
        ∏ l ∈ retained,
          rationalOutputDensity (FiniteProbabilityWeights.uniform (V → ZMod (p l ^ A l)))
            (localPrimePowerIntegerPolynomialOutput (p l) (A l) (e l) (F i) (r i l)) (p l ^ A l)
            (fun j => ZMod.castHom (Finset.dvd_prod_of_mem (fun l => p l ^ A l)
              (Finset.mem_univ l)) (ZMod (p l ^ A l)) (β j))) := by
  intro p' A' e' hq'
  let : NeZero (∏ l : retained, p' l ^ A' l) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l.val)))⟩
  rw [crt_integer_polynomial_rational_inactive_density_product]
  congr 1
  apply congrArg (inactive.fiberMean gridPoint z)
  funext i
  conv_rhs => rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro l _
  congr 1
  funext j
  exact congrArg (fun h : ZMod (∏ l, p l ^ A l) →+* ZMod (p l.val ^ A l.val) => h (β j))
    (ZMod.castHom_comp (Finset.dvd_prod_of_mem (fun k : retained => p' k ^ A' k)
      (Finset.mem_univ l)) (retainedPrimePowerModulus_dvd p A retained))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

theorem samplerLongEmbedding_dedicated_mem_range (inactive : D → Prop) (h : D → ℕ)
    (d : D) (b : B d) (v : Fin (h d)) :
    (Sum.inr ⟨d, b, v⟩ : SamplerTupleIndex G B h) ∈
      Set.range (samplerLongEmbedding inactive h) ↔ ¬ inactive d := by
  constructor
  · rintro ⟨k, hk⟩
    rcases k with g | ⟨a, c, w⟩
    · simp only [samplerLongEmbedding_common, Sum.inl_ne_inr] at hk
    · have he : a.val = d := congrArg Sigma.fst (Sum.inr.inj hk)
      exact he ▸ a.property
  · intro hd
    exact ⟨.inr ⟨⟨d, hd⟩, b, v⟩, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SamplerSeparatedVariables
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {D G : Type*} {B : D → Type*}

theorem samplerSeparatedValues_eq_extend {R : Type*} [Zero R]
    (inactive : D → Prop) (h : D → ℕ)
    (long : SamplerLongVariables inactive G B h → R)
    (raw : PrincipalTupleIndex B h × Option Empty → R) :
    Sum.elim long raw ∘ samplerSeparatedVariable inactive h =
      Function.extend (samplerLongEmbedding inactive h) long (samplerFrozenRaw h raw) := by
  funext k
  rcases k with g | ⟨d, b, v⟩
  · exact ((samplerLongEmbedding (B := B) inactive h).injective.extend_apply
      long (samplerFrozenRaw h raw) (.inl g)).symm
  · by_cases hd : inactive d
    · have hn : ¬ ∃ k, samplerLongEmbedding (G := G) inactive h k = .inr ⟨d, b, v⟩ := by
        intro hk
        exact ((samplerLongEmbedding_dedicated_mem_range inactive h d b v).mp hk) hd
      rw [Function.extend_apply' long (samplerFrozenRaw h raw) _ hn]
      simp only [Function.comp_apply, samplerSeparatedVariable_inactive inactive h d b v hd,
        Sum.elim_inr, samplerFrozenRaw]
    · simp only [Function.comp_apply, samplerSeparatedVariable_active inactive h d b v hd,
        Sum.elim_inl]
      exact ((samplerLongEmbedding (G := G) inactive h).injective.extend_apply
        long (samplerFrozenRaw h raw) (.inr ⟨⟨d, hd⟩, b, v⟩)).symm

theorem eval_rename_samplerSeparatedVariable {R : Type*} [CommRing R]
    (inactive : D → Prop) (h : D → ℕ)
    (P : MvPolynomial (SamplerTupleIndex G B h) R)
    (long : SamplerLongVariables inactive G B h → R)
    (raw : PrincipalTupleIndex B h × Option Empty → R) :
    eval (Sum.elim long raw) (rename (samplerSeparatedVariable inactive h) P) =
      eval long (conditionPolynomial (samplerLongEmbedding inactive h)
        (samplerLongEmbedding inactive h).injective (samplerFrozenRaw h raw) P) := by
  rw [eval_rename, samplerSeparatedValues_eq_extend, eval_conditionPolynomial]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedSeparatedCongruencePolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j)

theorem allocatedUnconditionedCongruenceIntegerPolynomial_condition
    (v : LayerSamplerVariables G I n B → ℤ) :
    conditionPolynomial (allocatedLongEmbedding inactive) (allocatedLongEmbedding inactive).injective v
      (allocatedUnconditionedCongruenceIntegerPolynomial inactive j base noise r projection o) =
      allocatedCongruenceIntegerPolynomial inactive j base noise r projection v o := by
  rcases o with x | i | a <;> rfl

theorem allocatedSeparatedCongruencePolynomial_eval
    (long : LayerSamplerLongVariables inactive G B → ℤ)
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ) :
    MvPolynomial.eval (Sum.elim long raw)
      (allocatedSeparatedCongruencePolynomial inactive j base noise r projection o) =
      MvPolynomial.eval long (allocatedCongruenceIntegerPolynomial inactive j base noise r projection
        (samplerFrozenRaw (layerSamplerDegree I n) raw) o) := by
  rw [allocatedSeparatedCongruencePolynomial, eval_rename_samplerSeparatedVariable]
  rw [← allocatedUnconditionedCongruenceIntegerPolynomial_condition]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialRetainedModulusBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem crtPolynomialInputLaw_integerLong_density_of_output
    {L V Inactive Out : Type*} [Fintype L] [Fintype V] [Fintype Out] [DecidableEq Out]
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    (poly : Out → MvPolynomial (V ⊕ Inactive) ℤ) (inactive : Inactive → ℤ)
    (Y : (∀ l, V → ZMod (p l ^ A l)) → Out → ℤ)
    (hY : ∀ x j, Y x j = MvPolynomial.eval
      (Sum.elim (fun v => ((prescribedCRTPolynomialInput p A e hq origin x v).val : ℤ))
        inactive) (poly j))
    (β : Out → ZMod (∏ l, p l ^ A l)) :
    letI : NeZero (∏ l, p l ^ A l) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
    rationalOutputDensity (crtPolynomialInputLaw p A e hq origin)
      (integerLongPolynomialOutput poly inactive (∏ l, p l ^ A l)) (∏ l, p l ^ A l) β =
    rationalOutputDensity (crtPrimePowerPolynomialLaw (V := V) p A) Y (∏ l, p l ^ A l) β := by
  let : NeZero (∏ l, p l ^ A l) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
  unfold rationalOutputDensity finiteImageMass crtPolynomialInputLaw
  rw [FiniteProbabilityWeights.fiberLaw_mean]
  congr 1
  apply congrArg (crtPrimePowerPolynomialLaw (V := V) p A).mean
  funext x
  have heq : (fun j => (integerLongPolynomialOutput poly inactive (∏ l, p l ^ A l)
      (prescribedCRTPolynomialInput p A e hq origin x) j : ZMod (∏ l, p l ^ A l))) =
      fun j => (Y x j : ZMod (∏ l, p l ^ A l)) := by
    funext j
    exact congrArg (fun a : ℤ => (a : ZMod (∏ l, p l ^ A l))) (hY x j).symm
  dsimp only
  simp only [heq]

namespace VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

attribute [local instance] retainedLabelDecidableEq

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.smallReferencePrimeNeZero
attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.smallReferenceModulusNeZero
omit [Fintype Tsp] in

theorem referenceRetainedCRT_density_eq (cutoff : ℕ)
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod (path.referenceRetainedCRTModulus cutoff)) :
    rationalOutputDensity (path.referenceRetainedCRTInputLaw cutoff)
      (integerLongPolynomialOutput path.referencePolynomial raw
        (path.referenceRetainedCRTModulus cutoff)) (path.referenceRetainedCRTModulus cutoff) β =
    rationalOutputDensity
      (crtPrimePowerPolynomialLaw
        (V := LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B)
        (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
        (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val))
      (crtPrimePowerIntegerPolynomialOutput
        (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
        (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)
        (fun p : path.referenceRetainedPrimes cutoff => path.prescribed p.val.val)
        (primePower_crt_coprime (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
          (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)
          (fun p => path.prime p.val.val p.val.property)
          (Subtype.val_injective.comp Subtype.val_injective))
        (path.localReferencePolynomial raw) (fun p => path.origin p.val))
      (path.referenceRetainedCRTModulus cutoff) β := by
  apply crtPolynomialInputLaw_integerLong_density_of_output
  intro x o
  simpa only [crtPrimePowerIntegerPolynomialOutput, prescribedCRTPolynomialInput,
    localReferencePolynomial, referencePolynomial, allocatedForecastPolynomial] using
    (allocatedSeparatedCongruencePolynomial_eval (allocatedShortAxis (I := I) U b S.value)
      o.1 path.base path.noise (allocatedReadDeck path.read)
      (fun a => allocatedReadProjection path.read ⟨o.1, a.val⟩) o.2 _ raw).symm

omit [Fintype Tsp] in
theorem retainedCRTIndependentForecast_eq {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (gridVolume : ℝ) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) :
    path.retainedCRTIndependentForecast inactive gridPoint raw cutoff gridVolume z β =
      path.retainedReferenceForecast inactive gridPoint raw cutoff gridVolume z β := by
  dsimp only [retainedCRTIndependentForecast, retainedReferenceForecast,
    referenceLocalDensity, referenceRetainedCRTModulus]
  have h := crt_integer_polynomial_retained_inactive_density_product inactive gridPoint
    (fun p : path.primes => p.val) (fun p : path.primes => path.exponent p.val)
    (fun p : path.primes => path.prescribed p.val)
    (primePower_crt_coprime (fun p : path.primes => p.val)
      (fun p : path.primes => path.exponent p.val)
      (fun p => path.prime p.val p.property) Subtype.val_injective)
    (fun i => path.localReferencePolynomial (raw i)) (fun _ => path.origin)
    (path.referenceRetainedPrimes cutoff) gridVolume z β
  dsimp only at h
  simp only [rationalInactiveForecast, rationalOutputDensity, ← Nat.card_eq_fintype_card] at h ⊢
  exact h

omit [Fintype Tsp] in
theorem retainedCRTReferenceForecast_eq_independent {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (gridVolume : ℝ) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) :
    path.retainedCRTReferenceForecast inactive gridPoint raw cutoff gridVolume z β =
      path.retainedCRTIndependentForecast inactive gridPoint raw cutoff gridVolume z β := by
  unfold retainedCRTReferenceForecast retainedCRTIndependentForecast rationalInactiveForecast
  congr 1
  apply congrArg (inactive.fiberMean gridPoint z)
  funext i
  exact path.referenceRetainedCRT_density_eq cutoff (raw i) _

omit [Fintype Tsp] in

theorem retainedCRTReferenceForecast_eq {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (gridVolume : ℝ) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) :
    path.retainedCRTReferenceForecast inactive gridPoint raw cutoff gridVolume z β =
      path.retainedReferenceForecast inactive gridPoint raw cutoff gridVolume z β :=
  (path.retainedCRTReferenceForecast_eq_independent inactive gridPoint raw cutoff gridVolume z β).trans
    (path.retainedCRTIndependentForecast_eq inactive gridPoint raw cutoff gridVolume z β)

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.retainedFullReferenceModulusNeZero
omit [Fintype Tsp] in

theorem reference_inactive_goodPrimeDeletion_retainedCRT {Ω Z : Type*} [Fintype Ω]
    (hm : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (haccuracy : 4 / (cutoff : ℝ) ≤ δ)
    (gridVolume : ℝ) (hvolume : 0 ≤ gridVolume) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) :
    let full := rationalInactiveForecast inactive (fun _ => path.referenceInputLaw) gridPoint
      (fun i => integerLongPolynomialOutput path.referencePolynomial (raw i) path.referenceModulus)
      path.referenceModulus gridVolume z β
    let truncated := path.retainedCRTReferenceForecast inactive gridPoint raw cutoff gridVolume z β
    (1 - δ) * truncated ≤ full ∧ full ≤ (1 + δ) * truncated := by
  dsimp only
  rw [path.retainedCRTReferenceForecast_eq]
  exact path.reference_inactive_goodPrimeDeletion_s2 hm hD inactive gridPoint raw
    cutoff hcutoff hsmall hδ haccuracy gridVolume hvolume z β

end ActualFixedSpatialForecastPath
end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ActualFixedSpatialSlicedNumericalDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem SlicedProductBlock.pairDensity_nonneg {ι : Type*} [Fintype ι]
    (A B : SlicedProductBlock ι) (x : ℝ) : 0 ≤ SlicedProductBlock.pairDensity A B x := by
  unfold pairDensity affinePairDensity randomIntervalDensity densityMixture
  apply integral_nonneg
  intro p
  unfold normalizedIntervalWindow affinePairWidth
  exact div_nonneg (intervalWindow_mem_Icc _ _ _).1
    (le_max_of_le_left (abs_nonneg _))

theorem SlicedProductBlock.fourDensity_nonneg {ι : Type*} [Fintype ι]
    (A B C D : SlicedProductBlock ι) (x : ℝ) :
    0 ≤ SlicedProductBlock.fourDensity A B C D x := by
  unfold fourDensity scalarDensityConvolution
  exact integral_nonneg (fun t =>
    mul_nonneg (pairDensity_nonneg A B _) (pairDensity_nonneg C D _))

theorem principalFourRemainderDensity_nonneg {J ι : Type*}
    [Fintype J] [Fintype ι] [DecidableEq J] [DecidableEq ι]
    (c : Fin 4 ⊕ J → ℝ) (lower width : (Fin 4 ⊕ J) × Option ι → ℝ) (x : ℝ) :
    0 ≤ principalFourRemainderDensity c lower width x := by
  unfold principalFourRemainderDensity independentShiftDensity densityMixture
  exact integral_nonneg (fun t => SlicedProductBlock.fourDensity_nonneg _ _ _ _ _)

theorem canonicalSlicedPrincipalDensity_nonneg {B F : Type*}
    [Fintype B] [Fintype F] [DecidableEq F]
    (hB : 4 ≤ Fintype.card B) (i : F) (c : B → ℝ)
    (lower width : B × F → ℝ) (x : ℝ) :
    0 ≤ canonicalSlicedPrincipalDensity hB i c lower width x :=
  principalFourRemainderDensity_nonneg _ _ _ _

theorem jointSlicedPrincipalDensity_nonneg {D : Type*} [Fintype D]
    {B F : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]
    (hB : ∀ d, 4 ≤ Fintype.card (B d)) (i : ∀ d, F d)
    (c : ∀ d, B d → ℝ) (lower width : ∀ d, B d × F d → ℝ)
    (shift : D → ℝ) (y : (Σ _d : D, Unit) → ℝ) :
    0 ≤ jointSlicedPrincipalDensity hB i c lower width shift y := by
  exact sigmaAxisWeight_nonneg _
    (fun d v => canonicalSlicedPrincipalDensity_nonneg (hB d) (i d)
      (c d) (lower d) (width d) _) y

end Erdos3

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

theorem density_nonneg
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (y : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) → ℝ))) :
    0 ≤ slice.density hBactive y := by
  cases Subsingleton.elim decX (Classical.decEq X)
  let := Classical.decEq X
  classical
  unfold density fixedSpatialKernelSliceOriginalForecastDensity
    fixedSpatialKernelOriginalForecastDensity binaryDensity allocatedFixedPathLiftDensity
  apply mul_nonneg
  · exact (fixedSpatialKernelDensity_probability_density_s2 _ _ _ _ _ _).1 _
  · exact jointSlicedPrincipalDensity_nonneg _ _ _ _ _ _ _

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualFixedSpatialSlicedRetainedKernelComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.fullReferenceNonzero
attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.retainedReferenceNonzero
omit [Fintype Tsp] in
theorem retainedForecastOutput_reduce (cutoff : ℕ)
    (r : X → ZMod slice.path.referenceModulus) (labels : ∀ j, Fin (n j) ⊕ Eout j → ℤ) :
    (fun out => ZMod.castHom (slice.path.referenceRetainedCRTModulus_dvd cutoff)
      (ZMod (slice.path.referenceRetainedCRTModulus cutoff))
      (forecastCongruenceOutput (allocatedShortAxis (I := I) U b S.value) r
        (fun j i => (labels j i : ZMod slice.path.referenceModulus)) out)) =
      forecastCongruenceOutput (allocatedShortAxis (I := I) U b S.value)
        (fun i => ZMod.castHom (slice.path.referenceRetainedCRTModulus_dvd cutoff)
          (ZMod (slice.path.referenceRetainedCRTModulus cutoff)) (r i))
        (fun j i => (labels j i : ZMod (slice.path.referenceRetainedCRTModulus cutoff))) := by
  funext out
  rcases out with ⟨j, x | i | a⟩ <;>
    simp only [forecastCongruenceOutput, map_intCast]

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

local notation "labels" => forecastRecoveredIntegerLabels U b hb bW
local notation "grid" => forecastInactiveFixedOutput B U b S selected
  (allocatedOriginalSampleInactiveCoefficients B selected slice.path.sample) slice.path.commonTuple
local notation "vol" => (∏ a, (basisAxisScale (b (Sigma.fst (selected a))) (Sigma.snd (selected a)) : ℝ))
local notation "raw" => (fun z : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U b S) =>
    fun k : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty => (z (Prod.fst k) (Prod.snd k) : ℤ))
local notation "out" r:max β:max => forecastCongruenceOutput (allocatedShortAxis (I := I) U b S.value) r
  (fun j i => (labels (fun a => β (e.symm a)) j i : ZMod slice.path.referenceModulus))
local notation "gridAt" β:max => (fun a (_ : (Finset.univ : Finset (Finset Empty))) =>
  labels (fun a => β (e.symm a)) (Sigma.fst (selected a)) (Sum.inl (Sigma.snd (selected a))))
local notation "reduced" cutoff:max r:max => (fun i => ZMod.castHom
  (slice.path.referenceRetainedCRTModulus_dvd cutoff)
  (ZMod (slice.path.referenceRetainedCRTModulus cutoff)) (r i))

local instance instNeZeroNatReferenceModulusPath_r9b2bc5_1 : NeZero slice.path.referenceModulus := ⟨slice.path.referenceModulus_pos.ne'⟩
local instance instNeZeroNatReferenceRetainedCRTModulusPath_r9b2bc5_1 (cutoff : ℕ) : NeZero (slice.path.referenceRetainedCRTModulus cutoff) :=
  ⟨(slice.path.referenceRetainedCRTModulus_pos cutoff).ne'⟩
omit [Fintype Tsp] in

theorem retainedRecoveredRationalFactor_eq_reference (cutoff : ℕ)
    (r : X → ZMod slice.path.referenceModulus) (β : Fin d → ℤ) :
    slice.retainedRecoveredRationalFactor selected bW hb e cutoff (reduced cutoff r) β =
      slice.path.retainedCRTReferenceForecast slice.principalLaw grid raw cutoff vol
        (gridAt β) (out r β) := by
  unfold retainedRecoveredRationalFactor forecastLawRecoveredRationalFactor
    ActualFixedSpatialForecastPath.retainedCRTReferenceForecast
  rw [slice.retainedForecastOutput_reduce cutoff r]
  simp only [rationalInactiveForecast, rationalOutputDensity, ← Nat.card_eq_fintype_card]

omit [Fintype Tsp] in

theorem recoveredRationalFactor_retained_comparison
    (hm : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (haccuracy : 4 / (cutoff : ℝ) ≤ δ)
    (r : X → ZMod slice.path.referenceModulus) (β : Fin d → ℤ) :
    (1 - δ) * slice.retainedRecoveredRationalFactor selected bW hb e cutoff (reduced cutoff r) β ≤
      slice.recoveredRationalFactor selected bW hb e r β ∧
    slice.recoveredRationalFactor selected bW hb e r β ≤
      (1 + δ) * slice.retainedRecoveredRationalFactor selected bW hb e cutoff (reduced cutoff r) β := by
  rw [slice.retainedRecoveredRationalFactor_eq_reference selected bW hb e cutoff r β]
  unfold recoveredRationalFactor forecastLawRecoveredRationalFactor
  have h := slice.path.reference_inactive_goodPrimeDeletion_retainedCRT hm hD slice.principalLaw
    grid raw cutoff hcutoff hsmall hδ haccuracy vol (by positivity) (gridAt β) (out r β)
  dsimp only at h
  simpa only [rationalInactiveForecast, rationalOutputDensity, ← Nat.card_eq_fintype_card] using h

private theorem mul_relative_bounds {w f g δ : ℝ} (hw : 0 ≤ w)
    (h : (1 - δ) * g ≤ f ∧ f ≤ (1 + δ) * g) :
    (1 - δ) * (w * g) ≤ w * f ∧ w * f ≤ (1 + δ) * (w * g) := by
  constructor
  · calc
      _ = w * ((1 - δ) * g) := by ring
      _ ≤ w * f := mul_le_mul_of_nonneg_left h.1 hw
  · calc
      _ ≤ w * ((1 + δ) * g) := mul_le_mul_of_nonneg_left h.2 hw
      _ = _ := by ring

theorem recoveredG_retained_comparison
    (hm : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (haccuracy : 4 / (cutoff : ℝ) ≤ δ)
    (v : X → ℝ) (r : X → ZMod slice.path.referenceModulus)
    (β : Fin d → ℤ) (y : Fin d → ℝ) :
    (1 - δ) * slice.retainedRecoveredG selected hB o bW hb e cutoff v (reduced cutoff r) β y ≤
      slice.recoveredG selected hB o bW hb e v r β y ∧
    slice.recoveredG selected hB o bW hb e v r β y ≤
      (1 + δ) * slice.retainedRecoveredG selected hB o bW hb e cutoff v (reduced cutoff r) β y := by
  exact mul_relative_bounds (slice.density_nonneg hB _)
    (slice.recoveredRationalFactor_retained_comparison selected bW hb e hm hD cutoff hcutoff
      hsmall hδ haccuracy r β)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialRetainedPatchEndpoint
namespace OAI

section

namespace Erdos3

private theorem extraction_exp_two {L : ℝ} (hL : 1 ≤ L) : 2 ≤ Real.exp L := by
  linarith only [hL, Real.add_one_le_exp L]

private theorem extraction_exp_four {L : ℝ} (hL : 1 ≤ L) : 4 ≤ Real.exp (2 * L) := by
  have h := extraction_exp_two hL
  have he : Real.exp (2 * L) = Real.exp L * Real.exp L := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  nlinarith

theorem spatialPatchExtraction_radius {L : ℝ} (hL : 1 ≤ L) :
    0 < Real.exp (-4 * L) ∧ Real.exp (-4 * L) ≤ 1 := by
  exact ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith)⟩

theorem spatialPatchExtraction_strict_budget {L Λ C S : ℝ}
    (hL : 1 ≤ L) (hΛ : Λ ≤ Real.exp L) (hC : C ≤ Real.exp L)
    (hS : Real.exp (-L) ≤ S) :
    Real.exp (-3 * L) + Λ * Real.exp (-4 * L) + C * Real.exp (-4 * L) < S := by
  have hprod : Real.exp L * Real.exp (-4 * L) = Real.exp (-3 * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hΛ' : Λ * Real.exp (-4 * L) ≤ Real.exp (-3 * L) := by
    rw [← hprod]
    exact mul_le_mul_of_nonneg_right hΛ (Real.exp_nonneg _)
  have hC' : C * Real.exp (-4 * L) ≤ Real.exp (-3 * L) := by
    rw [← hprod]
    exact mul_le_mul_of_nonneg_right hC (Real.exp_nonneg _)
  have he : Real.exp (2 * L) * Real.exp (-3 * L) = Real.exp (-L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hh := mul_le_mul_of_nonneg_right (extraction_exp_four hL) (Real.exp_nonneg (-3 * L))
  rw [he] at hh
  have hp := Real.exp_pos (-3 * L)
  linarith

theorem spatialPatchExtraction_side_lower {L : ℝ} (hL : 1 ≤ L)
    (q₀ n : ℕ) (hq₀ : 0 < q₀) (hq₀bound : (q₀ : ℝ) ≤ Real.exp L)
    (hn : (n : ℝ) ≤ L) :
    Real.exp (-spatialPatchExtractionCost L) ≤
      Real.exp (-4 * L) * Real.exp (-4 * L) / (4 * (q₀ : ℝ) * (n + 1)) := by
  have hdenpos : 0 < 4 * (q₀ : ℝ) * (n + 1) := by positivity
  have hnexp : (n : ℝ) + 1 ≤ Real.exp L := by
    linarith only [hn, Real.add_one_le_exp L]
  have hden : 4 * (q₀ : ℝ) * (n + 1) ≤ Real.exp (4 * L) := by
    calc
      _ ≤ Real.exp (2 * L) * Real.exp L * Real.exp L := by
        exact mul_le_mul (mul_le_mul (extraction_exp_four hL) hq₀bound
          (by positivity) (Real.exp_nonneg _)) hnexp (by positivity) (by positivity)
      _ = Real.exp (4 * L) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hcost : 12 * L ≤ spatialPatchExtractionCost L := by
    unfold spatialPatchExtractionCost
    nlinarith [sq_nonneg L]
  have hbase : Real.exp (-12 * L) ≤
      Real.exp (-4 * L) * Real.exp (-4 * L) / (4 * (q₀ : ℝ) * (n + 1)) := by
    apply (le_div_iff₀ hdenpos).mpr
    calc
      _ ≤ Real.exp (-12 * L) * Real.exp (4 * L) :=
        mul_le_mul_of_nonneg_left hden (Real.exp_nonneg _)
      _ = Real.exp (-4 * L) * Real.exp (-4 * L) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  exact (Real.exp_le_exp.mpr (by linarith : -spatialPatchExtractionCost L ≤ -12 * L)).trans hbase

theorem spatialPatchExtraction_large {L N : ℝ} (hL : 1 ≤ L)
    (q₀ : ℕ) (hq₀ : (q₀ : ℝ) ≤ Real.exp L)
    (hN : Real.exp (spatialPatchExtractionCost L) ≤ N) :
    2 * (q₀ : ℝ) ≤ Real.exp (-4 * L) * N := by
  have hcost : 6 * L ≤ spatialPatchExtractionCost L := by
    unfold spatialPatchExtractionCost
    nlinarith [sq_nonneg L]
  calc
    _ ≤ 2 * Real.exp L := mul_le_mul_of_nonneg_left hq₀ (by norm_num)
    _ ≤ Real.exp L * Real.exp L :=
      mul_le_mul_of_nonneg_right (extraction_exp_two hL) (Real.exp_nonneg L)
    _ = Real.exp (2 * L) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-4 * L + spatialPatchExtractionCost L) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-4 * L) * Real.exp (spatialPatchExtractionCost L) := Real.exp_add _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg _)

theorem spatialPatchExtraction_gain_lower {L C : ℝ} (hL : 1 ≤ L)
    (hCpos : 0 < C) (hC : C ≤ Real.exp L) (q d : ℕ) (hq : 0 < q)
    (hqd : (q : ℝ) ^ d ≤ Real.exp (6 * L ^ 2)) :
    Real.exp (-spatialPatchExtractionCost L) ≤
      Real.exp (-3 * L) / (C * (q : ℝ) ^ d) := by
  have hdenpos : 0 < C * (q : ℝ) ^ d := by positivity
  have hden : C * (q : ℝ) ^ d ≤ Real.exp (L + 6 * L ^ 2) := by
    calc
      _ ≤ Real.exp L * Real.exp (6 * L ^ 2) :=
        mul_le_mul hC hqd (by positivity) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  have hcost : 6 * L ^ 2 + 4 * L ≤ spatialPatchExtractionCost L := by
    unfold spatialPatchExtractionCost
    nlinarith [sq_nonneg L]
  have hbase : Real.exp (-(6 * L ^ 2 + 4 * L)) ≤
      Real.exp (-3 * L) / (C * (q : ℝ) ^ d) := by
    apply (le_div_iff₀ hdenpos).mpr
    calc
      _ ≤ Real.exp (-(6 * L ^ 2 + 4 * L)) * Real.exp (L + 6 * L ^ 2) :=
        mul_le_mul_of_nonneg_left hden (Real.exp_nonneg _)
      _ = Real.exp (-3 * L) := by
        rw [← Real.exp_add]
        congr 1
        ring
  exact (Real.exp_le_exp.mpr (by linarith :
    -spatialPatchExtractionCost L ≤ -(6 * L ^ 2 + 4 * L))).trans hbase

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem relativePatchSliceScore_reparamPatch {X : Type*} [Fintype X]
    {s d q : ℕ} {N : X → ℕ} (S : ResidueBoxSlice N q)
    (f : (X → ℤ) → ℝ) (target : ℝ) (A : PolynomialPatch X s d) :
    relativePatchSliceScore S f target (S.reparamPatch A) =
      (𝔼 j : (∀ i, Fin (S.length i)),
        (f (fun i => ((S.point j i).val : ℤ)) - target) *
          A.value (fun i => ((S.point j i).val : ℝ))) := by
  unfold relativePatchSliceScore
  apply Finset.expect_congr rfl
  intro j _
  rw [S.reparamPatch_value]

theorem relativePatchSliceConclusion_of_spatially_localized_patch
    {X : Type*} [Fintype X] {s d q rankBound : ℕ} {N : X → ℕ}
    (S : ResidueBoxSlice N q) (hq : 0 < q)
    (f : (X → ℤ) → ℝ) (target cost gain : ℝ)
    (A : PolynomialPatch X s d) (lip : ℝ≥0)
    (hrank : d ≤ rankBound)
    (hlength : ∀ i, Real.exp (-cost) * (N i : ℝ) ≤ S.length i)
    (hlip : A.kernel.lip ≤ lip)
    (hbudget : (d : ℝ) + Real.log (1 + (lip : ℝ)) ≤ cost)
    (hgain : Real.exp (-cost) ≤ gain)
    (hscore : gain ≤
      (𝔼 j : (∀ i, Fin (S.length i)),
        (f (fun i => ((S.point j i).val : ℤ)) - target) *
          A.value (fun i => ((S.point j i).val : ℝ)))) :
    RelativePatchSliceConclusion s N f target rankBound cost := by
  refine ⟨q, hq, S, d, S.reparamPatch A, hlength, hrank, ?_, ?_⟩
  · apply le_trans _ hbudget
    unfold relativePatchComplexity
    rw [S.reparamPatch_kernel]
    apply add_le_add le_rfl
    apply Real.log_le_log (by positivity)
    exact add_le_add le_rfl (show (A.kernel.lip : ℝ) ≤ lip from hlip)
  · rw [relativePatchSliceScore_reparamPatch]
    exact hgain.trans hscore

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators NNReal Classical

theorem relativePatchSliceConclusion_of_discounted_spatial_buffered_score
    {X : Type*} [Fintype X] [DecidableEq X] (N : X → ℕ) (hN : ∀ i, 0 < N i)
    (q₀ : ℕ) (hq₀ : 0 < q₀) {s d E m rankBound : ℕ}
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial X ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : X => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (X ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (G : (X → ℝ) → (X → ZMod q₀) → (Fin m → ℤ) → (Fin m → ℝ) → ℝ)
    (Λ L C : ℝ≥0) (hC : 1 ≤ C)
    (hGspace : ∀ r b y, LipschitzWith Λ (fun z => G z r b y))
    (hGlift : ∀ z r b, LipschitzWith L (G z r b))
    (hGcap : ∀ z r b y, G z r b y ∈ Set.Icc (0 : ℝ) C)
    (hinvariant : ∀ z r c k, G z r (recoveredIntegerLift M c k) = G z r c)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (full : (∀ i, Fin (N i)) → (Fin m → ℤ) → ℝ)
    {lam δ ε gain surplus meshWidth shortLoss cost : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : 0 ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hlower : ∀ u β, (1 - δ) *
      G (BoxProgressionPartition.normalizedPoint u) (fun i => ((u i).val : ZMod q₀)) β
        (fun i => realIntegerMatrix M (fun j => aeval (fun x => ((u x).val : ℝ)) (P j)) i -
          (β i : ℝ)) ≤ full u β)
    (hupper : ∀ u β, full u β ≤ (1 + δ) *
      G (BoxProgressionPartition.normalizedPoint u) (fun i => ((u i).val : ZMod q₀)) β
        (fun i => realIntegerMatrix M (fun j => aeval (fun x => ((u x).val : ℝ)) (P j)) i -
          (β i : ℝ)))
    (hscore : gain ≤ 𝔼 u : (∀ i, Fin (N i)),
      (f (fun i => ((u i).val : ℤ)) - lam) * ∑' β : Fin m → ℤ,
        χ.value (fun i => realIntegerMatrix M (fun j => aeval (fun x => ((u x).val : ℝ)) (P j)) i -
          (β i : ℝ)) * full u β *
        B.value (Sum.elim (fun i => ((u i).val : ℝ)) (fun i => (β i : ℝ))))
    (hsurplus : 0 ≤ surplus) (hmeshWidth : 0 < meshWidth) (hmeshWidth1 : meshWidth ≤ 1)
    (hshortLoss : 0 < shortLoss) (hlarge : ∀ i, 2 * (q₀ : ℝ) ≤ meshWidth * N i)
    (hfreeze : surplus + Λ * meshWidth + C * shortLoss < gain / (1 + δ))
    (hrank : d + E ≤ rankBound)
    (hlength : ∀ i, Real.exp (-cost) * (N i : ℝ) ≤
      shortLoss * meshWidth * N i / (4 * q₀ * (Fintype.card X + 1)))
    (hbudget : ((d + E : ℕ) : ℝ) + Real.log (1 +
      ((q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) +
        (χ.lip + L / C) * K + B.kernel.lip : ℝ≥0)) ≤ cost)
    (hgain : Real.exp (-cost) ≤ surplus / ((C : ℝ) * (q : ℝ) ^ d)) :
    RelativePatchSliceConclusion s N f ((1 - ε) * lam) rankBound cost := by
  let t : (∀ i, Fin (N i)) → X → ℝ := fun u i => ((u i).val : ℝ)
  let input : (∀ i, Fin (N i)) → ℝ := fun u => f (fun i => ((u i).val : ℤ))
  let x : (∀ i, Fin (N i)) → Fin m → ℝ :=
    fun u => realIntegerMatrix M (fun j => aeval (t u) (P j))
  let T := fun (u : ∀ i, Fin (N i)) (β : Fin m → ℤ) =>
    B.value (Sum.elim (t u) (fun i => (β i : ℝ)))
  let reduced := fun (u : ∀ i, Fin (N i)) (β : Fin m → ℤ) =>
    G (BoxProgressionPartition.normalizedPoint u) (fun i => ((u i).val : ZMod q₀)) β
      (fun i => x u i - (β i : ℝ))
  have hinput (u : ∀ i, Fin (N i)) : input u ∈ Set.Icc (0 : ℝ) 1 :=
    hf _ ((mem_integerBox N _).mpr (fun i =>
      ⟨by positivity, by exact_mod_cast (u i).isLt⟩))
  have htarget : (1 - ε) * lam ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg (sub_nonneg.mpr hε.2) hlam.1
    · exact (mul_le_of_le_one_left hlam.1 (by linarith only [hε.1])).trans hlam.2
  have hdiscounted := buffered_score_discount χ x T full reduced input hδ
    (fun u => (hinput u).1) hlam.1 (fun u β => (B.value_mem_Icc _).1)
    (fun u β => (hGcap _ _ _ _).1) hlower hupper hdiscount hscore
  obtain ⟨S, Q, hlen, _, hQl, hQs⟩ := exists_spatially_localized_patch_s2 N hN q₀ hq₀
    w hw hws hmono P hP p B χ M K hM hweight G Λ L C hC hGspace hGlift hGcap
    hinvariant q hq hmesh t (fun u => input u - (1 - ε) * lam)
    hsurplus hmeshWidth hmeshWidth1 hshortLoss
    (fun u => abs_le.mpr ⟨by linarith only [(hinput u).1, htarget.2],
      by linarith only [(hinput u).2, htarget.1]⟩)
    hlarge hdiscounted hfreeze
  apply relativePatchSliceConclusion_of_spatially_localized_patch S hq₀ f
    ((1 - ε) * lam) cost (surplus / ((C : ℝ) * (q : ℝ) ^ d)) Q _ hrank
    (fun i => (hlength i).trans (hlen i)) hQl hbudget hgain
  apply hQs.trans_eq
  apply Finset.expect_congr
  · ext j
    simp
  · intro j _
    rfl

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem spatialPatchExtractionMesh_exp_le (L : ℝ) :
    Real.exp (5 * L) ≤ (spatialPatchExtractionMesh L : ℝ) := Nat.le_ceil _

theorem spatialPatchExtractionMesh_le_exp {L : ℝ} (hL : 1 ≤ L) :
    (spatialPatchExtractionMesh L : ℝ) ≤ Real.exp (6 * L) := by
  have hfive : 0 ≤ 5 * L := by linarith
  exact (ceil_exp_le_exp_add_one hfive).trans (Real.exp_le_exp.mpr (by linarith))

theorem spatialPatchExtractionMesh_bounds {L : ℝ} (hL : 1 ≤ L)
    (K : ℝ≥0) (hK : (K : ℝ) ≤ Real.exp L) :
    8 ≤ spatialPatchExtractionMesh L ∧
      16 * (K : ℝ) ≤ (spatialPatchExtractionMesh L : ℝ) ∧
      (spatialPatchExtractionMesh L : ℝ) ≤ Real.exp (6 * L) := by
  have hexp : (2 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hfour : (16 : ℝ) ≤ Real.exp (4 * L) := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hexp 4
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, show (2 : ℝ)^4 = 16 by norm_num] using hp
  have hlarge : 16 * Real.exp L ≤ Real.exp (5 * L) := by
    calc
      _ ≤ Real.exp (4 * L) * Real.exp L :=
        mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hq := spatialPatchExtractionMesh_exp_le L
  have height : (8 : ℝ) ≤ (spatialPatchExtractionMesh L : ℝ) := by
    linarith
  refine ⟨by exact_mod_cast height, ?_, spatialPatchExtractionMesh_le_exp hL⟩
  exact (mul_le_mul_of_nonneg_left hK (by norm_num)).trans (hlarge.trans hq)

theorem spatialPatchExtractionMesh_pow_le {L : ℝ} (hL : 1 ≤ L)
    (d : ℕ) (hd : (d : ℝ) ≤ L) :
    (spatialPatchExtractionMesh L : ℝ)^d ≤ Real.exp (6 * L^2) := by
  have hp := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _)
    (spatialPatchExtractionMesh_le_exp hL) (by linarith : 0 ≤ 6 * L) d hd
  convert hp using 1
  congr 1
  ring

theorem spatialPatchExtraction_log_complexity_le_of_mesh {L E : ℝ}
    (hL : 1 ≤ L) (hE : E ≤ L) (d q : ℕ) (hd : (d : ℝ) ≤ L)
    (hq : (q : ℝ) ≤ Real.exp (6 * L))
    (hqd : (q : ℝ)^d ≤ Real.exp (6 * L^2))
    (K χlip Llift Blip C : ℝ≥0)
    (hK : (K : ℝ) ≤ Real.exp L) (hχ : (χlip : ℝ) ≤ Real.exp L)
    (hLift : (Llift : ℝ) ≤ Real.exp L) (hB : (Blip : ℝ) ≤ Real.exp L)
    (hC : 1 ≤ C) :
    ((d : ℝ) + E) + Real.log
      (1 + (q : ℝ) * (2 * (q : ℝ)^d + 1) +
        ((χlip : ℝ) + (Llift : ℝ) / C) * K + Blip) ≤ 20 * (L + 1)^2 := by
  let T : ℝ := 6 * L^2 + 6 * L
  have hL0 : 0 ≤ L := by linarith
  have hT0 : 0 ≤ T := by dsimp only [T]; positivity
  have hTtwo : 2 * L ≤ T := by dsimp only [T]; nlinarith [sq_nonneg L]
  have hTL : L ≤ T := by linarith
  have hbase : 1 ≤ Real.exp T := Real.one_le_exp hT0
  have hpbase : 1 ≤ Real.exp (6 * L^2) := Real.one_le_exp (by positivity)
  have hinner : 2 * (q : ℝ)^d + 1 ≤ 3 * Real.exp (6 * L^2) := by linarith
  have hmesh : (q : ℝ) * (2 * (q : ℝ)^d + 1) ≤ 3 * Real.exp T := by
    calc
      _ ≤ Real.exp (6 * L) * (3 * Real.exp (6 * L^2)) :=
        mul_le_mul hq hinner (by positivity) (Real.exp_nonneg _)
      _ = _ := by dsimp only [T]; rw [Real.exp_add]; ring
  have hCr : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hdiv : (Llift : ℝ) / C ≤ Llift := div_le_self Llift.coe_nonneg hCr
  have hsum : (χlip : ℝ) + (Llift : ℝ) / C ≤ 2 * Real.exp L := by linarith
  have hlift : ((χlip : ℝ) + (Llift : ℝ) / C) * K ≤ 2 * Real.exp T := by
    calc
      _ ≤ (2 * Real.exp L) * Real.exp L :=
        mul_le_mul hsum hK K.coe_nonneg (by positivity)
      _ = 2 * Real.exp (2 * L) := by rw [show 2 * L = L + L by ring, Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hTtwo) (by norm_num)
  have hBlip : (Blip : ℝ) ≤ Real.exp T := hB.trans (Real.exp_le_exp.mpr hTL)
  have htotal : 1 + (q : ℝ) * (2 * (q : ℝ)^d + 1) +
      ((χlip : ℝ) + (Llift : ℝ) / C) * K + Blip ≤ Real.exp (T + 7) := by
    calc
      _ ≤ 7 * Real.exp T := by linarith
      _ ≤ Real.exp 7 * Real.exp T := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (7 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hlog : Real.log (1 + (q : ℝ) * (2 * (q : ℝ)^d + 1) +
      ((χlip : ℝ) + (Llift : ℝ) / C) * K + Blip) ≤ T + 7 :=
    (Real.log_le_iff_le_exp (by positivity)).mpr htotal
  dsimp only [T] at hlog
  nlinarith [sq_nonneg L]

theorem spatialPatchExtraction_log_complexity_le {L E : ℝ}
    (hL : 1 ≤ L) (hE : E ≤ L) (d : ℕ) (hd : (d : ℝ) ≤ L)
    (K χlip Llift Blip C : ℝ≥0)
    (hK : (K : ℝ) ≤ Real.exp L) (hχ : (χlip : ℝ) ≤ Real.exp L)
    (hLift : (Llift : ℝ) ≤ Real.exp L) (hB : (Blip : ℝ) ≤ Real.exp L)
    (hC : 1 ≤ C) :
    ((d : ℝ) + E) + Real.log
      (1 + (spatialPatchExtractionMesh L : ℝ) *
        (2 * (spatialPatchExtractionMesh L : ℝ)^d + 1) +
        ((χlip : ℝ) + (Llift : ℝ) / C) * K + Blip) ≤ 20 * (L + 1)^2 :=
  spatialPatchExtraction_log_complexity_le_of_mesh hL hE d (spatialPatchExtractionMesh L) hd
    (spatialPatchExtractionMesh_le_exp hL) (spatialPatchExtractionMesh_pow_le hL d hd)
    K χlip Llift Blip C hK hχ hLift hB hC

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

theorem exists_spatialPatchExtraction_parameters {L S : ℝ} (hL : 1 ≤ L)
    (d E n : ℕ) (hd : (d : ℝ) ≤ L) (hE : (E : ℝ) ≤ L) (hn : (n : ℝ) ≤ L)
    (K Λ C Llift χlip Blip : ℝ≥0)
    (hK : (K : ℝ) ≤ Real.exp L) (hΛ : (Λ : ℝ) ≤ Real.exp L)
    (hC : (C : ℝ) ≤ Real.exp L) (hLift : (Llift : ℝ) ≤ Real.exp L)
    (hχ : (χlip : ℝ) ≤ Real.exp L) (hB : (Blip : ℝ) ≤ Real.exp L)
    (hC1 : 1 ≤ C) (q₀ : ℕ) (hq₀ : 0 < q₀) (hq₀bound : (q₀ : ℝ) ≤ Real.exp L)
    (hS : Real.exp (-L) ≤ S) :
    ∃ (q : ℕ) (ρ θ τ : ℝ),
      8 ≤ q ∧ 16 * (K : ℝ) ≤ q ∧ 0 < ρ ∧ ρ ≤ 1 ∧ 0 < θ ∧ 0 ≤ τ ∧
      τ + (Λ : ℝ) * ρ + (C : ℝ) * θ < S ∧
      Real.exp (-spatialPatchExtractionCost L) ≤ θ * ρ / (4 * (q₀ : ℝ) * (n + 1)) ∧
      Real.exp (-spatialPatchExtractionCost L) ≤ τ / ((C : ℝ) * (q : ℝ) ^ d) ∧
      (d + E : ℝ) + Real.log
        (1 + (q : ℝ) * (2 * (q : ℝ) ^ d + 1) +
          ((χlip : ℝ) + (Llift : ℝ) / (C : ℝ)) * (K : ℝ) + (Blip : ℝ)) ≤
        spatialPatchExtractionCost L ∧
      (∀ N : ℝ, Real.exp (spatialPatchExtractionCost L) ≤ N →
        2 * (q₀ : ℝ) ≤ ρ * N) := by
  let q := spatialPatchExtractionMesh L
  obtain ⟨hq8, hqK, hqupper⟩ := spatialPatchExtractionMesh_bounds hL K hK
  obtain ⟨hρ, hρ1⟩ := spatialPatchExtraction_radius hL
  have hCpos : 0 < (C : ℝ) := by
    have hc : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC1
    linarith
  refine ⟨q, Real.exp (-4 * L), Real.exp (-4 * L), Real.exp (-3 * L),
    hq8, hqK, hρ, hρ1, hρ, (Real.exp_pos _).le,
    spatialPatchExtraction_strict_budget hL hΛ hC hS,
    spatialPatchExtraction_side_lower hL q₀ n hq₀ hq₀bound hn,
    spatialPatchExtraction_gain_lower hL hCpos hC q d (by omega)
      (spatialPatchExtractionMesh_pow_le hL d hd), ?_,
    fun N hN => spatialPatchExtraction_large hL q₀ hq₀bound hN⟩
  exact spatialPatchExtraction_log_complexity_le hL hE d hd K χlip Llift Blip C
    hK hχ hLift hB hC1

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators NNReal Classical

theorem relativePatchSliceConclusion_of_budgeted_spatial_buffered_score
    {X : Type*} [Fintype X] [DecidableEq X] (N : X → ℕ) (hN : ∀ i, 0 < N i)
    (q₀ : ℕ) (hq₀ : 0 < q₀) {s d E m rankBound : ℕ}
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial X ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : X => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (X ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (G : (X → ℝ) → (X → ZMod q₀) → (Fin m → ℤ) → (Fin m → ℝ) → ℝ)
    (Λ Llift C : ℝ≥0) (hC : 1 ≤ C)
    (hGspace : ∀ r b y, LipschitzWith Λ (fun z => G z r b y))
    (hGlift : ∀ z r b, LipschitzWith Llift (G z r b))
    (hGcap : ∀ z r b y, G z r b y ∈ Set.Icc (0 : ℝ) C)
    (hinvariant : ∀ z r c k, G z r (recoveredIntegerLift M c k) = G z r c)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (full : (∀ i, Fin (N i)) → (Fin m → ℤ) → ℝ)
    {lam δ ε gain L : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : 0 ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hlower : ∀ u β, (1 - δ) *
      G (BoxProgressionPartition.normalizedPoint u) (fun i => ((u i).val : ZMod q₀)) β
        (fun i => realIntegerMatrix M (fun j => aeval (fun x => ((u x).val : ℝ)) (P j)) i -
          (β i : ℝ)) ≤ full u β)
    (hupper : ∀ u β, full u β ≤ (1 + δ) *
      G (BoxProgressionPartition.normalizedPoint u) (fun i => ((u i).val : ZMod q₀)) β
        (fun i => realIntegerMatrix M (fun j => aeval (fun x => ((u x).val : ℝ)) (P j)) i -
          (β i : ℝ)))
    (hscore : gain ≤ 𝔼 u : (∀ i, Fin (N i)),
      (f (fun i => ((u i).val : ℤ)) - lam) * ∑' β : Fin m → ℤ,
        χ.value (fun i => realIntegerMatrix M (fun j => aeval (fun x => ((u x).val : ℝ)) (P j)) i -
          (β i : ℝ)) * full u β *
        B.value (Sum.elim (fun i => ((u i).val : ℝ)) (fun i => (β i : ℝ))))
    (hL : 1 ≤ L) (hd : (d : ℝ) ≤ L) (hE : (E : ℝ) ≤ L)
    (hn : (Fintype.card X : ℝ) ≤ L)
    (hKbudget : (K : ℝ) ≤ Real.exp L) (hΛbudget : (Λ : ℝ) ≤ Real.exp L)
    (hCbudget : (C : ℝ) ≤ Real.exp L) (hLiftbudget : (Llift : ℝ) ≤ Real.exp L)
    (hχbudget : (χ.lip : ℝ) ≤ Real.exp L) (hBbudget : (B.kernel.lip : ℝ) ≤ Real.exp L)
    (hq₀budget : (q₀ : ℝ) ≤ Real.exp L)
    (hgainBudget : Real.exp (-L) ≤ gain / (1 + δ))
    (hlarge : ∀ i, Real.exp (spatialPatchExtractionCost L) ≤ (N i : ℝ))
    (hrank : d + E ≤ rankBound) :
    RelativePatchSliceConclusion s N f ((1 - ε) * lam) rankBound
      (spatialPatchExtractionCost L) := by
  obtain ⟨q, ρ, θ, surplus, hq, hmesh, hρ, hρ1, hθ, hsurplus, hfreeze,
    hside, hgain, hcomplex, hbig⟩ := exists_spatialPatchExtraction_parameters hL d E
      (Fintype.card X) hd hE hn K Λ C Llift χ.lip B.kernel.lip hKbudget hΛbudget
      hCbudget hLiftbudget hχbudget hBbudget hC q₀ hq₀ hq₀budget hgainBudget
  have hlength (i : X) : Real.exp (-spatialPatchExtractionCost L) * (N i : ℝ) ≤
      θ * ρ * N i / (4 * q₀ * (Fintype.card X + 1)) := by
    calc
      _ ≤ (θ * ρ / (4 * (q₀ : ℝ) * (Fintype.card X + 1))) * (N i : ℝ) :=
        mul_le_mul_of_nonneg_right hside (Nat.cast_nonneg _)
      _ = _ := by ring
  apply relativePatchSliceConclusion_of_discounted_spatial_buffered_score N hN q₀ hq₀
    w hw hws hmono P hP p B χ M K hM hweight G Λ Llift C hC hGspace hGlift hGcap
    hinvariant q hq hmesh f hf full hlam hδ hε hdiscount hlower hupper hscore
    hsurplus hρ hρ1 hθ (fun i => hbig (N i) (hlarge i)) hfreeze hrank
    hlength ?_ hgain
  simpa only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast,
    NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_one, Nat.cast_add, add_assoc] using hcomplex

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

theorem relativePatchSliceConclusion_of_actual_retained_forecast_score_s2_oai
    (hmpos : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j)
    (hN : ∀ i, 0 < physicalN i)
    {s r E rankBound : ℕ}
    (w : Fin r → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (Pscalar : Fin r → MvPolynomial X ℝ)
    (hP : ∀ j, Pscalar j ∈ weightedSupportLE (fun _ : X => 1) (w j))
    (p : Fin d → ℕ)
    (Bpatch : WeightedParameterPatch (X ⊕ Fin d) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel d) (M : Fin d → Fin r → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hcoords : ∀ x : X → ℤ,
      fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val) x =
        realIntegerMatrix M (fun j => MvPolynomial.aeval (fun i => (x i : ℝ)) (Pscalar j)))
    (Λ Llift C : ℝ≥0) (hC : 1 ≤ C)
    (hGspace : ∀ residue β y, LipschitzWith Λ
      (fun v => slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β y))
    (hGlift : ∀ v residue β, LipschitzWith Llift
      (slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β))
    (hGcap : ∀ v residue β y,
      slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β y ∈
        Set.Icc (0 : ℝ) C)
    (hinvariant : ∀ v residue β k,
      slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue
        (recoveredIntegerLift M β k) =
      slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox physicalN, f x ∈ Set.Icc (0 : ℝ) 1)
    {lam δ ε gain L : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : 0 ≤ δ)
    (haccuracy : 4 / (cutoff : ℝ) ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hscore : gain ≤ 𝔼 x : ↥(integerBox physicalN),
      (slice.targetAt selected hB o bW hb poly hm κ x.val).re *
        bufferedScalarScore χ
          (fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val))
          (fun u β => Bpatch.value (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ))))
          f lam x.val)
    (hL : 1 ≤ L) (hr : (r : ℝ) ≤ L) (hE : (E : ℝ) ≤ L)
    (hn : (Fintype.card X : ℝ) ≤ L)
    (hKbudget : (K : ℝ) ≤ Real.exp L) (hΛbudget : (Λ : ℝ) ≤ Real.exp L)
    (hCbudget : (C : ℝ) ≤ Real.exp L) (hLiftbudget : (Llift : ℝ) ≤ Real.exp L)
    (hχbudget : (χ.lip : ℝ) ≤ Real.exp L) (hBbudget : (Bpatch.kernel.lip : ℝ) ≤ Real.exp L)
    (hqbudget : (slice.path.referenceRetainedCRTModulus cutoff : ℝ) ≤ Real.exp L)
    (hgainBudget : Real.exp (-L) ≤ gain / (1 + δ))
    (hlarge : ∀ i, Real.exp (spatialPatchExtractionCost L) ≤ (physicalN i : ℝ))
    (hrank : r + E ≤ rankBound) :
    RelativePatchSliceConclusion s physicalN f ((1 - ε) * lam) rankBound
      (spatialPatchExtractionCost L) := by
  let full : (∀ i, Fin (physicalN i)) → (Fin d → ℤ) → ℝ := fun u β =>
    κ * slice.recoveredG selected hB o bW hb e
      (BoxProgressionPartition.normalizedPoint u)
      (fun i => ((u i).val : ZMod slice.path.referenceModulus)) β
      (fun i => realIntegerMatrix M
        (fun j => MvPolynomial.aeval (fun x => ((u x).val : ℝ)) (Pscalar j)) i - (β i : ℝ))
  have hscoreFin := hscore.trans_eq
    (slice.targetAt_mean_mul_bufferedScalarScore_eq_fin_s2 selected hB o bW hb e poly hm κ χ
      (fun u β => Bpatch.value (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ)))) f lam)
  apply relativePatchSliceConclusion_of_budgeted_spatial_buffered_score physicalN hN
    (slice.path.referenceRetainedCRTModulus cutoff)
    (slice.path.referenceRetainedCRTModulus_pos cutoff)
    w hw hws hmono Pscalar hP p Bpatch χ M K hM hweight
    (slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ)
    Λ Llift C hC hGspace hGlift hGcap hinvariant f hf full hlam hδ hε hdiscount
    ?_ ?_ ?_ hL hr hE hn hKbudget hΛbudget hCbudget hLiftbudget hχbudget hBbudget
    hqbudget hgainBudget hlarge hrank
  · intro u β
    have h := (slice.recoveredG_retained_comparison selected hB o bW hb e hmpos hD
      cutoff hcutoff hsmall hδ haccuracy (BoxProgressionPartition.normalizedPoint u)
      (fun i => ((u i).val : ZMod slice.path.referenceModulus)) β
      (fun i => realIntegerMatrix M
        (fun j => MvPolynomial.aeval (fun x => ((u x).val : ℝ)) (Pscalar j)) i -
          (β i : ℝ))).1
    have hs := mul_le_mul_of_nonneg_left h hκ
    simpa only [full, scaledRetainedRecoveredG, map_natCast, mul_left_comm κ (1 - δ)] using hs
  · intro u β
    have h := (slice.recoveredG_retained_comparison selected hB o bW hb e hmpos hD
      cutoff hcutoff hsmall hδ haccuracy (BoxProgressionPartition.normalizedPoint u)
      (fun i => ((u i).val : ZMod slice.path.referenceModulus)) β
      (fun i => realIntegerMatrix M
        (fun j => MvPolynomial.aeval (fun x => ((u x).val : ℝ)) (Pscalar j)) i -
          (β i : ℝ))).2
    have hs := mul_le_mul_of_nonneg_left h hκ
    simpa only [full, scaledRetainedRecoveredG, map_natCast, mul_left_comm κ (1 + δ)] using hs
  · apply hscoreFin.trans_eq
    apply Finset.expect_congr
    · ext u
      simp
    · intro u _
      simp only [full, hcoords, Int.cast_natCast]
      unfold BoxProgressionPartition.normalizedPoint
      rfl

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.relativePatchSliceConclusion_of_actual_retained_forecast_score_s2_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.relativePatchSliceConclusion_of_actual_retained_forecast_score_s2_oai
