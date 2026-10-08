-- Prove2me | solution 1 for GrayStability.smooth_moser_lie_generator
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T19:22:55.80311+00:00
-- url     : https://prove2.me/submissions/26b05dfd-82d5-480a-b18e-7886ff0f8638

import Definitions.Def_GrayStability_Basic
import Theorems.Thm_ContactLinearAlgebra_augmented_moser_operator_bijective
import Theorems.Thm_SmoothLinearAlgebra_compact_supported_linear_solution
import Theorems.Thm_ContactCalculus_lie_derivative_eq_exterior_of_annihilation
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 800000
open GrayStability Set Function
open scoped ContDiff

theorem solution {n c : ℕ} (F : E n → E c) (hF : IsCompactRegularLevel F)
    (α : ℝ → OneForm n) (hα : IsContactFamilyOn F α) :
    ∃ X : ℝ → E n → E n, ∃ μ : ℝ → E n → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × E n => X p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E n => μ p.1 p.2) ∧
      (∃ K : Set (E n), IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ levelSet F,
        X t y ∈ contactPlane F (α t) y) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ levelSet F, ∀ v ∈ tangentSpace F y,
        formTimeDeriv α t y v + lieDerivOneForm (X t) (α t) y v =
          μ t y * α t y v := by
  let D : ℝ × E n → E n →L[ℝ] E c := fun p => fderiv ℝ F p.2
  let a : ℝ × E n → E n →L[ℝ] ℝ := fun p => α p.1 p.2
  let d : ℝ × E n → E n →L[ℝ] E n →L[ℝ] ℝ :=
    fun p => fderiv ℝ (α p.1) p.2
  let B : ℝ × E n → E n →L[ℝ] E n →L[ℝ] ℝ := fun p => d p - (d p).flip
  have hD : ContDiff ℝ ∞ D := (hF.1.fderiv_right (m := ∞) (by simp)).comp contDiff_snd
  have ha : ContDiff ℝ ∞ a := hα.1
  have hd : ContDiff ℝ ∞ d := by
    have hh : ContDiff ℝ ∞ (fun p : (ℝ × E n) × E n => α p.1.1 p.2) :=
      hα.1.comp (contDiff_fst.fst.prodMk contDiff_snd)
    exact hh.fderiv contDiff_snd (by simp)
  have hB : ContDiff ℝ ∞ B := by
    apply hd.sub
    apply contDiff_clm_apply_iff.mpr
    intro v
    apply contDiff_clm_apply_iff.mpr
    intro w
    exact (hd.clm_apply contDiff_const).clm_apply contDiff_const
  let A : ℝ × E n → (E n × (ℝ × (E c →L[ℝ] ℝ))) →L[ℝ]
      ((E n →L[ℝ] ℝ) × (ℝ × E c)) := fun p =>
    LinearMap.toContinuousLinearMap
      { toFun := fun r => (B p r.1 - r.2.1 • a p - r.2.2.comp (D p), (a p r.1, D p r.1))
        map_add' := by
          intro r s
          ext v <;> simp [add_smul] <;> ring
        map_smul' := by
          intro r s
          ext v <;> simp [smul_sub, smul_smul] <;> ring }
  have hA : ContDiff ℝ ∞ A := by
    apply contDiff_clm_apply_iff.mpr
    intro r
    change ContDiff ℝ ∞ (fun p =>
      (B p r.1 - r.2.1 • a p - r.2.2.comp (D p), (a p r.1, D p r.1)))
    exact (((hB.clm_apply contDiff_const).sub (ha.const_smul _)).sub
      (contDiff_const.clm_comp hD)).prodMk
        ((ha.clm_apply contDiff_const).prodMk (hD.clm_apply contDiff_const))
  let C : Set (ℝ × E n) := Icc (0 : ℝ) 1 ×ˢ levelSet F
  have hC : IsCompact C := isCompact_Icc.prod hF.2.1
  have hinv : ∀ p ∈ C, (A p).IsInvertible := by
    intro p hp
    obtain ⟨hpT, hpM⟩ := hp
    have hc := hα.2 p.1 hpT p.2 hpM
    let eV : Module.Dual ℝ (E n) ≃ₗ[ℝ] (E n →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
    let eW : Module.Dual ℝ (E c) ≃ₗ[ℝ] (E c →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
    let eIn := (LinearEquiv.refl ℝ (E n)).prodCongr
      ((LinearEquiv.refl ℝ ℝ).prodCongr eW.symm)
    let eOut := eV.prodCongr (LinearEquiv.refl ℝ (ℝ × E c))
    have hcore := ContactLinearAlgebra.augmented_moser_operator_bijective
      (D p).toLinearMap (a p).toLinearMap (eV.symm.toLinearMap.comp (B p).toLinearMap)
      (hF.2.2 p.2 hpM) hc.1 (by
        intro u hDu hau hz
        by_contra hne
        obtain ⟨v, hv, hnev⟩ := hc.2 u ⟨hDu, hau⟩ hne
        exact hnev (hz v hv.1 hv.2))
    have hj : Function.Bijective (A p) := by
      convert eOut.bijective.comp (hcore.comp eIn.bijective) using 1
      ext r v <;> rfl
    let e := (LinearEquiv.ofBijective (A p).toLinearMap hj).toContinuousLinearEquiv
    exact ⟨e, rfl⟩
  let β : ℝ × E n → E n →L[ℝ] ℝ :=
    fun p => fderiv ℝ a p (1, 0)
  have hβ : ContDiff ℝ ∞ β :=
    (ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hβv : ∀ t y v, β (t, y) v = formTimeDeriv α t y v := by
    intro t y v
    have h := ((ha.differentiable (by simp)) (t, y)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
    have hv := h.clm_apply (hasDerivAt_const t v)
    simpa [β, a, formTimeDeriv] using hv.deriv.symm
  obtain ⟨u, χ, hu, hχ, hsu, hχC, he⟩ :=
    SmoothLinearAlgebra.compact_supported_linear_solution A
      (fun p => (-β p, (0, 0))) hA ((hβ.neg).prodMk contDiff_const) C hC hinv
  let X : ℝ → E n → E n := fun t y => (u (t, y)).1
  let μ : ℝ → E n → ℝ := fun t y => (u (t, y)).2.1
  have hX : ContDiff ℝ ∞ (fun p : ℝ × E n => X p.1 p.2) := hu.fst
  have hμ : ContDiff ℝ ∞ (fun p : ℝ × E n => μ p.1 p.2) := hu.snd.fst
  have hhor : ∀ t y, α t y (X t y) = 0 := by
    intro t y
    have hh := congrArg (fun q => q.2.1) (he (t, y))
    simpa [A, a, X] using hh
  have htan : ∀ t y, fderiv ℝ F y (X t y) = 0 := by
    intro t y
    have hh := congrArg (fun q => q.2.2) (he (t, y))
    simpa [A, D, X] using hh
  refine ⟨X, μ, hX, hμ, ?_, ?_, ?_⟩
  · refine ⟨Prod.snd '' tsupport u, hsu.image continuous_snd, ?_⟩
    intro t y hy
    have hz : u (t, y) = 0 := by
      apply notMem_support.mp
      intro hs
      exact hy ⟨(t, y), subset_tsupport u hs, rfl⟩
    simp [X, hz]
  · intro t ht y hy
    exact ⟨htan t y, hhor t y⟩
  · intro t ht y hy v hv
    have hc : χ (t, y) = 1 := hχC (t, y) ⟨ht, hy⟩
    have hh := congrArg (fun q => q.1 v) (he (t, y))
    have hlie := ContactCalculus.lie_derivative_eq_exterior_of_annihilation
      (α t) (X t)
      ((ha.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp))
      ((hX.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp))
      (hhor t) y v
    change lieDerivOneForm (X t) (α t) y v = extDerivOneForm (α t) y (X t y) v at hlie
    rw [hlie]
    have hv0 : fderiv ℝ F y v = 0 := hv
    simp [A, B, d, a, D, hc, hv0, hβv] at hh
    simp only [extDerivOneForm, X, μ]
    linarith
