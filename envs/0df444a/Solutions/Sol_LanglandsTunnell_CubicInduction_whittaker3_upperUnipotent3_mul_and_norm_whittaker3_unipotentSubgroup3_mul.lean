-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5d177824-1ead-5315-a4f6-acbe7f8aa716

import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory NumberField.StandardAddChar
open LanglandsTunnell.CubicInduction NumberField.AdelicHaar

namespace WhittakerUnipotentEquivariance

private theorem upperUnipotent3_mul {R : Type*} [CommRing R] (x y z x' y' z' : R) :
    upperUnipotent3 x y z * upperUnipotent3 x' y' z' = upperUnipotent3 (x + x') (y + y') (z + z' + x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem globalPointsGL_upperUnipotent3 (a b c : ℚ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (upperUnipotent3 a b c) =
      upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) b)
        (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPointsGL, Matrix.GeneralLinearGroup.map]

section Periodic

variable (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
  (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
  (g : AdelicGL 3 (𝓞 ℚ) ℚ)
include haut

private theorem shift_z (x y : AdeleRing (𝓞 ℚ) ℚ) (q : ℚ) (z : AdeleRing (𝓞 ℚ) ℚ) :
    f (upperUnipotent3 x y (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + z) * g) = f (upperUnipotent3 x y z * g) := by
  have h := haut (upperUnipotent3 0 0 q) (upperUnipotent3 x y z * g)
  rw [globalPointsGL_upperUnipotent3, map_zero, ← mul_assoc, upperUnipotent3_mul] at h
  simpa using h

private theorem shift_y (x : AdeleRing (𝓞 ℚ) ℚ) (q : ℚ) (y z : AdeleRing (𝓞 ℚ) ℚ) :
    f (upperUnipotent3 x (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + y) z * g) = f (upperUnipotent3 x y z * g) := by
  have h := haut (upperUnipotent3 0 q 0) (upperUnipotent3 x y z * g)
  rw [globalPointsGL_upperUnipotent3, map_zero, ← mul_assoc, upperUnipotent3_mul] at h
  simpa using h

private theorem shift_x (q : ℚ) (x y z : AdeleRing (𝓞 ℚ) ℚ) :
    f (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + x) y (z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q * y) * g) =
      f (upperUnipotent3 x y z * g) := by
  have h := haut (upperUnipotent3 q 0 0) (upperUnipotent3 x y z * g)
  rw [globalPointsGL_upperUnipotent3, map_zero, ← mul_assoc, upperUnipotent3_mul] at h
  simpa using h

end Periodic

private theorem psiQ_rat_add (q : ℚ) (w : AdeleRing (𝓞 ℚ) ℚ) :
    psiQ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + w) = psiQ w := by
  rw [AddChar.map_add_eq_mul, psiQ_algebraMap, one_mul]

private theorem neg_add_rat (q : ℚ) (x w : AdeleRing (𝓞 ℚ) ℚ) :
    -(x + (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + w)) = algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (-q) + -(x + w) := by
  rw [map_neg]; abel

private theorem neg_rat_add_add (q : ℚ) (x w : AdeleRing (𝓞 ℚ) ℚ) :
    -(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + x + w) = algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (-q) + -(x + w) := by
  rw [map_neg]; abel

private theorem norm_exp_neg (r : ℝ) : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by
  rw [show -(2 * Real.pi * Complex.I) * (r : ℂ) = ((-(2 * Real.pi * r) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem norm_exp_pos (r : ℝ) : ‖Complex.exp ((2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by
  rw [show (2 * Real.pi * Complex.I) * (r : ℂ) = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem norm_psiPadicFun {p : ℕ} [Fact p.Prime] (t : ℚ_[p]) : ‖psiPadicFun t‖ = 1 := by
  unfold psiPadicFun
  have h := norm_exp_neg
    (((exists_pPow_approx t).choose : ℝ) / (p : ℝ) ^ (exists_pPow_approx t).choose_spec.choose)
  push_cast at h
  simpa using h

private theorem norm_psiV (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (t : v.adicCompletion ℚ) :
    ‖psiV v t‖ = 1 := by
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  show ‖psiPadicFun _‖ = 1
  exact norm_psiPadicFun _

private theorem norm_psiArchPlace (v : InfinitePlace ℚ) (t : v.Completion) :
    ‖psiArchPlace v t‖ = 1 := by
  show ‖Complex.exp _‖ = 1
  exact norm_exp_pos _

private theorem norm_finprod_eq_one {ι : Type*} (a : ι → ℂ) (ha : ∀ i, ‖a i‖ = 1) :
    ‖∏ᶠ i, a i‖ = 1 := by
  by_cases hs : (Function.mulSupport a).Finite
  · rw [finprod_eq_prod_of_mulSupport_subset_of_finite a subset_rfl hs, norm_prod]
    exact Finset.prod_eq_one fun i _ => ha i
  · rw [finprod_of_infinite_mulSupport hs, norm_one]

private theorem norm_psiQ (t : AdeleRing (𝓞 ℚ) ℚ) : ‖psiQ t‖ = 1 := by
  rw [psiQ_apply, norm_mul,
    show psiArch t.1 = ∏ᶠ v, psiArchPlace v (t.1 v) from rfl,
    show psiFin t.2 = ∏ᶠ v, psiV v (t.2 v) from rfl,
    norm_finprod_eq_one (fun v => psiArchPlace v (t.1 v)) (fun v => norm_psiArchPlace v (t.1 v)),
    norm_finprod_eq_one (fun v => psiV v (t.2 v)) (fun v => norm_psiV v (t.2 v)), mul_one]

private noncomputable abbrev ν₀ := (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν

private theorem integral_add_right (h : AdeleRing (𝓞 ℚ) ℚ → ℂ)
    (hper : ∀ (q : ℚ) (t : AdeleRing (𝓞 ℚ) ℚ), h (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + t) = h t)
    (a : AdeleRing (𝓞 ℚ) ℚ) :
    ∫ t, h (t + a) ∂ν₀ = ∫ t, h t ∂ν₀ := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := adeleBorel (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI : (adelicAddHaar (𝓞 ℚ) ℚ).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ

  haveI : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) :=
    (show Function.Surjective
        (fun q : ℚ => (⟨algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q, ⟨q, rfl⟩⟩ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)) from
      fun ⟨_, q, rfl⟩ => ⟨q, rfl⟩).countable
  have hinv : ∀ (γ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (t : AdeleRing (𝓞 ℚ) ℚ), h (γ +ᵥ t) = h t := by
    rintro ⟨_, q, rfl⟩ t
    exact hper q t
  have hD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)
      (adelicAddHaar (𝓞 ℚ) ℚ) :=
    AdelicBox.isAddFundamentalDomain_adelicBox ℚ _
  have hD' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)
      ((fun t => -a + t) ⁻¹' AdelicBox.adelicBox ℚ) (adelicAddHaar (𝓞 ℚ) ℚ) :=
    hD.preimage_of_equiv (measurePreserving_add_left (adelicAddHaar (𝓞 ℚ) ℚ) (-a)).quasiMeasurePreserving
      Function.bijective_id fun γ t => by
        show -a + ((γ : AdeleRing (𝓞 ℚ) ℚ) + t) = (γ : AdeleRing (𝓞 ℚ) ℚ) + (-a + t)
        exact add_left_comm _ _ _
  have hbox : (fun t => a + t) ⁻¹' ((fun t => -a + t) ⁻¹' AdelicBox.adelicBox ℚ) =
      AdelicBox.adelicBox ℚ := by
    ext t
    simp
  show (∫ t, h (t + a) ∂@ProbabilityTheory.cond _ (adeleBorel (𝓞 ℚ) ℚ) (adelicAddHaar (𝓞 ℚ) ℚ)
      (AdelicBox.adelicBox ℚ)) =
    ∫ t, h t ∂@ProbabilityTheory.cond _ (adeleBorel (𝓞 ℚ) ℚ) (adelicAddHaar (𝓞 ℚ) ℚ)
      (AdelicBox.adelicBox ℚ)
  simp only [ProbabilityTheory.cond, integral_smul_measure]
  congr 1
  simp_rw [add_comm _ a]
  calc ∫ t in AdelicBox.adelicBox ℚ, h (a + t) ∂adelicAddHaar (𝓞 ℚ) ℚ
      = ∫ t in (fun t => a + t) ⁻¹' ((fun t => -a + t) ⁻¹' AdelicBox.adelicBox ℚ), h (a + t)
          ∂adelicAddHaar (𝓞 ℚ) ℚ := by rw [hbox]
    _ = ∫ t in (fun t => -a + t) ⁻¹' AdelicBox.adelicBox ℚ, h t ∂adelicAddHaar (𝓞 ℚ) ℚ :=
          (measurePreserving_add_left (adelicAddHaar (𝓞 ℚ) ℚ) a).setIntegral_preimage_emb
            (MeasurableEquiv.addLeft a).measurableEmbedding h _
    _ = ∫ t in AdelicBox.adelicBox ℚ, h t ∂adelicAddHaar (𝓞 ℚ) ℚ := hD'.setIntegral_eq hD hinv

private theorem integral_mul_const' (F : AdeleRing (𝓞 ℚ) ℚ → ℂ) (c : ℂ) :
    (∫ t, F t * c ∂ν₀) = (∫ t, F t ∂ν₀) * c :=
  integral_mul_const c F

private theorem integral_const_mul' (c : ℂ) (F : AdeleRing (𝓞 ℚ) ℚ → ℂ) :
    (∫ t, c * F t ∂ν₀) = c * ∫ t, F t ∂ν₀ :=
  integral_const_mul c F

private theorem equivariant (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (x₀ y₀ z₀ : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ f
        (upperUnipotent3 x₀ y₀ z₀ * g) =
      psiQ (x₀ + y₀) *
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ f g := by
  have hprod : ∀ x y z : AdeleRing (𝓞 ℚ) ℚ,
      upperUnipotent3 x y z * (upperUnipotent3 x₀ y₀ z₀ * g) =
        upperUnipotent3 (x + x₀) (y + y₀) (z + (z₀ + x * y₀)) * g := fun x y z => by
    rw [← mul_assoc, upperUnipotent3_mul, add_assoc]

  have hz : ∀ x y : AdeleRing (𝓞 ℚ) ℚ,
      (∫ z, f (upperUnipotent3 (x + x₀) (y + y₀) (z + (z₀ + x * y₀)) * g) * psiQ (-(x + y)) ∂ν₀) =
        ∫ z, f (upperUnipotent3 (x + x₀) (y + y₀) z * g) * psiQ (-(x + y)) ∂ν₀ := fun x y =>
    integral_add_right (fun z => f (upperUnipotent3 (x + x₀) (y + y₀) z * g) * psiQ (-(x + y)))
      (fun q z => by simp only [shift_z f haut g]) (z₀ + x * y₀)

  have hy : ∀ x : AdeleRing (𝓞 ℚ) ℚ,
      (∫ y, ∫ z, f (upperUnipotent3 (x + x₀) (y + y₀) z * g) * psiQ (-(x + y)) ∂ν₀ ∂ν₀) =
        psiQ y₀ * ∫ y, ∫ z, f (upperUnipotent3 (x + x₀) y z * g) * psiQ (-(x + y)) ∂ν₀ ∂ν₀ := fun x => by
    have hsplit : ∀ y : AdeleRing (𝓞 ℚ) ℚ, psiQ (-(x + y)) = psiQ (-(x + (y + y₀))) * psiQ y₀ := fun y => by
      rw [← AddChar.map_add_eq_mul]; congr 1; abel
    calc (∫ y, ∫ z, f (upperUnipotent3 (x + x₀) (y + y₀) z * g) * psiQ (-(x + y)) ∂ν₀ ∂ν₀)
        = ∫ y, ∫ z, f (upperUnipotent3 (x + x₀) (y + y₀) z * g) * psiQ (-(x + (y + y₀))) * psiQ y₀ ∂ν₀ ∂ν₀ := by
          congr 1
          funext y
          congr 1
          funext z
          rw [hsplit y, mul_assoc]
      _ = ∫ y, (∫ z, f (upperUnipotent3 (x + x₀) (y + y₀) z * g) * psiQ (-(x + (y + y₀))) ∂ν₀) * psiQ y₀ ∂ν₀ := by
          congr 1
          funext y
          exact integral_mul_const' _ _
      _ = (∫ y, ∫ z, f (upperUnipotent3 (x + x₀) (y + y₀) z * g) * psiQ (-(x + (y + y₀))) ∂ν₀ ∂ν₀) *
            psiQ y₀ :=
          integral_mul_const' _ _
      _ = (∫ y, ∫ z, f (upperUnipotent3 (x + x₀) y z * g) * psiQ (-(x + y)) ∂ν₀ ∂ν₀) * psiQ y₀ := by
          congr 1
          refine integral_add_right
            (fun y => ∫ z, f (upperUnipotent3 (x + x₀) y z * g) * psiQ (-(x + y)) ∂ν₀) (fun q y => ?_) y₀
          congr 1
          funext z
          rw [shift_y f haut g, neg_add_rat, psiQ_rat_add]
      _ = psiQ y₀ * ∫ y, ∫ z, f (upperUnipotent3 (x + x₀) y z * g) * psiQ (-(x + y)) ∂ν₀ ∂ν₀ :=
          mul_comm _ _

  have hsplit : ∀ x y : AdeleRing (𝓞 ℚ) ℚ, psiQ (-(x + y)) = psiQ (-(x + x₀ + y)) * psiQ x₀ := fun x y => by
    rw [← AddChar.map_add_eq_mul]; congr 1; abel
  have hper : ∀ (q : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ),
      (∫ y, ∫ z, f (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + x) y z * g) *
          psiQ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + x + y)) ∂ν₀ ∂ν₀) =
        ∫ y, ∫ z, f (upperUnipotent3 x y z * g) * psiQ (-(x + y)) ∂ν₀ ∂ν₀ := fun q x => by
    congr 1
    funext y
    rw [neg_rat_add_add, psiQ_rat_add,
      ← integral_add_right
        (fun z => f (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + x) y z * g) * psiQ (-(x + y)))
        (fun q' z => by simp only [shift_z f haut g]) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q * y)]
    simp only [shift_x f haut g]
  have hx : (∫ x, ∫ y, ∫ z, f (upperUnipotent3 (x + x₀) y z * g) * psiQ (-(x + y)) ∂ν₀ ∂ν₀ ∂ν₀) =
      psiQ x₀ * ∫ x, ∫ y, ∫ z, f (upperUnipotent3 x y z * g) * psiQ (-(x + y)) ∂ν₀ ∂ν₀ ∂ν₀ := by
    calc (∫ x, ∫ y, ∫ z, f (upperUnipotent3 (x + x₀) y z * g) * psiQ (-(x + y)) ∂ν₀ ∂ν₀ ∂ν₀)
        = ∫ x, ∫ y, ∫ z, f (upperUnipotent3 (x + x₀) y z * g) * psiQ (-(x + x₀ + y)) * psiQ x₀ ∂ν₀ ∂ν₀ ∂ν₀ := by
          congr 1
          funext x
          congr 1
          funext y
          congr 1
          funext z
          rw [hsplit x y, mul_assoc]
      _ = ∫ x, ∫ y, (∫ z, f (upperUnipotent3 (x + x₀) y z * g) * psiQ (-(x + x₀ + y)) ∂ν₀) * psiQ x₀ ∂ν₀ ∂ν₀ := by
          congr 1
          funext x
          congr 1
          funext y
          exact integral_mul_const' _ _
      _ = ∫ x, (∫ y, ∫ z, f (upperUnipotent3 (x + x₀) y z * g) * psiQ (-(x + x₀ + y)) ∂ν₀ ∂ν₀) * psiQ x₀ ∂ν₀ := by
          congr 1
          funext x
          exact integral_mul_const' _ _
      _ = (∫ x, ∫ y, ∫ z, f (upperUnipotent3 (x + x₀) y z * g) * psiQ (-(x + x₀ + y)) ∂ν₀ ∂ν₀ ∂ν₀) *
            psiQ x₀ :=
          integral_mul_const' _ _
      _ = (∫ x, ∫ y, ∫ z, f (upperUnipotent3 x y z * g) * psiQ (-(x + y)) ∂ν₀ ∂ν₀ ∂ν₀) * psiQ x₀ := by
          congr 1
          exact integral_add_right
            (fun x => ∫ y, ∫ z, f (upperUnipotent3 x y z * g) * psiQ (-(x + y)) ∂ν₀ ∂ν₀) hper x₀
      _ = psiQ x₀ * ∫ x, ∫ y, ∫ z, f (upperUnipotent3 x y z * g) * psiQ (-(x + y)) ∂ν₀ ∂ν₀ ∂ν₀ :=
          mul_comm _ _

  show (∫ x, ∫ y, ∫ z, f (upperUnipotent3 x y z * (upperUnipotent3 x₀ y₀ z₀ * g)) * psiQ (-(x + y)) ∂ν₀ ∂ν₀ ∂ν₀) =
    psiQ (x₀ + y₀) * ∫ x, ∫ y, ∫ z, f (upperUnipotent3 x y z * g) * psiQ (-(x + y)) ∂ν₀ ∂ν₀ ∂ν₀
  calc (∫ x, ∫ y, ∫ z, f (upperUnipotent3 x y z * (upperUnipotent3 x₀ y₀ z₀ * g)) * psiQ (-(x + y)) ∂ν₀ ∂ν₀ ∂ν₀)
      = ∫ x, ∫ y, ∫ z, f (upperUnipotent3 (x + x₀) (y + y₀) (z + (z₀ + x * y₀)) * g) * psiQ (-(x + y))
          ∂ν₀ ∂ν₀ ∂ν₀ := by
        congr 1
        funext x
        congr 1
        funext y
        congr 1
        funext z
        rw [hprod]
    _ = ∫ x, ∫ y, ∫ z, f (upperUnipotent3 (x + x₀) (y + y₀) z * g) * psiQ (-(x + y)) ∂ν₀ ∂ν₀ ∂ν₀ := by
        congr 1
        funext x
        congr 1
        funext y
        exact hz x y
    _ = ∫ x, psiQ y₀ * ∫ y, ∫ z, f (upperUnipotent3 (x + x₀) y z * g) * psiQ (-(x + y)) ∂ν₀ ∂ν₀ ∂ν₀ := by
        congr 1
        funext x
        exact hy x
    _ = psiQ y₀ * ∫ x, ∫ y, ∫ z, f (upperUnipotent3 (x + x₀) y z * g) * psiQ (-(x + y)) ∂ν₀ ∂ν₀ ∂ν₀ :=
        integral_const_mul' _ _
    _ = psiQ y₀ * (psiQ x₀ * ∫ x, ∫ y, ∫ z, f (upperUnipotent3 x y z * g) * psiQ (-(x + y)) ∂ν₀ ∂ν₀ ∂ν₀) := by
        rw [hx]
    _ = psiQ (x₀ + y₀) * ∫ x, ∫ y, ∫ z, f (upperUnipotent3 x y z * g) * psiQ (-(x + y)) ∂ν₀ ∂ν₀ ∂ν₀ := by
        rw [AddChar.map_add_eq_mul]
        ring

end WhittakerUnipotentEquivariance

open WhittakerUnipotentEquivariance

theorem solution
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (_haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g) :
    (∀ (x y z : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ f
            (upperUnipotent3 x y z * g) =
          psiQ (x + y) *
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ f g) ∧
      ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ f (n * g)‖ =
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ f g‖ := by
  refine ⟨fun x y z g => equivariant f _haut x y z g, fun n hn => ?_⟩
  have hn' : n ∈ Subgroup.closure (Set.range fun t : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      upperUnipotent3 t.1 t.2.1 t.2.2) := hn
  clear hn
  induction hn' using Subgroup.closure_induction with
  | mem m hm =>
    obtain ⟨t, rfl⟩ := hm
    intro g
    rw [equivariant f _haut, norm_mul, norm_psiQ, one_mul]
  | one => intro g; rw [one_mul]
  | mul m m' _ _ ihm ihm' => intro g; rw [mul_assoc, ihm, ihm']
  | inv m _ ihm => intro g; rw [← ihm (m⁻¹ * g), mul_inv_cancel_left]

end S_LanglandsTunnell_CubicInduction_whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul (solution)
