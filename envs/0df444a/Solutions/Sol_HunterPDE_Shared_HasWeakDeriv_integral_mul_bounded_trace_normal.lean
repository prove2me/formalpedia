-- Prove2me | solution 1 for HunterPDE.Shared.HasWeakDeriv.integral_mul_bounded_trace_normal
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T22:12:58.993779+00:00
-- url     : https://prove2.me/submissions/13ba9227-6d03-4e29-ad54-2f7e6831ef79

import Theorems.Thm_HunterPDE_Compactness_exists_global_testFunction_halfSpace_approx
import Theorems.Thm_HunterPDE_Compactness_weakDeriv_eLpNorm_le_sobolevNorm
import Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_sub
import Theorems.Thm_HunterPDE_Shared_integral_mul_smooth_normal
import Theorems.Thm_MeasureTheory_tendsto_integral_mul_of_eLpNorm
import Theorems.Thm_HunterPDE_Shared_hasWeakDeriv_partial_of_contDiffOn
import Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_ae_eq
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Tactic.Positivity
open MeasureTheory HunterPDE.Compactness HunterPDE.Shared Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem solution {m : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (C : ℝ≥0) (T : (EuclideanSpace ℝ (Fin (m + 1)) → ℝ) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hlinear : (∀ f g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
        MemW 1 p (upperHalfSpace m) f → MemW 1 p (upperHalfSpace m) g → ∀ a b : ℝ,
          T (a • f + b • g) =ᵐ[volume] a • T f + b • T g))
    (hbound : (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, MemW 1 p (upperHalfSpace m) f →
        MemLp (T f) p volume ∧
          eLpNorm (T f) p volume ≤ (C : ℝ≥0∞) * sobolevNorm 1 p (upperHalfSpace m) f))
    (hsmooth : (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, IsSmoothCompactClosedHalfSpace f →
        T f =ᵐ[volume] fun x' => f (boundaryPoint x')))
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) (hf : MemW 1 p (upperHalfSpace m) f)
    (g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hg : HunterPDE.Shared.HasWeakDeriv (upperHalfSpace m) (Pi.single (Fin.last m) 1) f g)
    (hgp : MemLp g p (volume.restrict (upperHalfSpace m)))
    (ψ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hψ : HunterPDE.Shared.IsTestFunction Set.univ ψ) :
    (∫ x in upperHalfSpace m, g x * ψ x) =
      -(∫ x in upperHalfSpace m,
        f x * HunterPDE.Shared.multiDeriv ψ (Pi.single (Fin.last m) 1) x) -
      ∫ x', T f x' * ψ (boundaryPoint x') := by
  classical
  let Ω := upperHalfSpace m
  let μ := volume.restrict Ω
  let α : Fin (m + 1) → ℕ := Pi.single (Fin.last m) 1
  have hΩ : IsOpen Ω :=
    isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last m)).continuous
  have hα : α ∈ multiIndicesLe (m + 1) 1 := by
    simp [multiIndicesLe, α, Fintype.mem_piFinset]
    intro a
    by_cases ha : a = Fin.last m <;> simp [ha]
  have hz : (0 : Fin (m + 1) → ℕ) ∈ multiIndicesLe (m + 1) 1 := by
    simp [multiIndicesLe]
  have self (a : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
      (ha : LocallyIntegrableOn a Ω) : HasWeakDeriv Ω 0 a a := by
    refine ⟨ha, ha, ?_⟩
    intro χ _
    have hl : multiIndexList (0 : Fin (m + 1) → ℕ) = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro i _
      simp
    simp [multiDeriv, hl, iteratedPartial]
  obtain ⟨u, hu, hup⟩ := hf 0 hz
  have hfp : MemLp f p μ := hup.ae_eq (hu.ae_eq hΩ (self f hg.1))
  let ε : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (1 / ((j : ℝ) + 1))
  have hεpos (j : ℕ) : 0 < ε j := ENNReal.ofReal_pos.mpr (by positivity)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose φ hφ hφW hdist using fun j =>
    exists_global_testFunction_halfSpace_approx m 1 p hp hp' f hf (ε j) (hεpos j)
  have hnorm : Tendsto (fun j => sobolevNorm 1 p Ω (f - φ j)) atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hεlim
      (fun _ => zero_le) (fun j => (hdist j).le)
  have hd (j : ℕ) : HasWeakDeriv Ω α (φ j) (partialDeriv (φ j) (Fin.last m)) :=
    hasWeakDeriv_partial_of_contDiffOn hΩ (φ j)
      ((hφ j).1.of_le (by simp)).contDiffOn (Fin.last m)
  have hdLp (j : ℕ) : MemLp (partialDeriv (φ j) (Fin.last m)) p μ := by
    obtain ⟨v, hv, hvp⟩ := hφW j α hα
    exact hvp.ae_eq (hv.ae_eq hΩ (hd j))
  have hφLp (j : ℕ) : MemLp (φ j) p μ := by
    obtain ⟨v, hv, hvp⟩ := hφW j 0 hz
    exact hvp.ae_eq (hv.ae_eq hΩ (self (φ j) (hd j).1))
  have hdiff (j : ℕ) : MemW 1 p Ω (f - φ j) := by
    intro β hβ
    obtain ⟨u, hu, hup⟩ := hf β hβ
    obtain ⟨v, hv, hvp⟩ := hφW j β hβ
    exact ⟨u - v, hu.sub hv, hup.sub hvp⟩
  have hvlim : Tendsto (fun j => eLpNorm (φ j - f) p μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hnorm
      (fun _ => zero_le)
    intro j
    change eLpNorm (φ j - f) p μ ≤ sobolevNorm 1 p Ω (f - φ j)
    rw [eLpNorm_sub_comm]
    exact weakDeriv_eLpNorm_le_sobolevNorm hp hp' Ω hΩ 0 hz _ _
      ((self f hg.1).sub (self (φ j) (hd j).1))
  have hdlim : Tendsto
      (fun j => eLpNorm ((partialDeriv (φ j) (Fin.last m)) - g) p μ)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hnorm
      (fun _ => zero_le)
    intro j
    change eLpNorm (partialDeriv (φ j) (Fin.last m) - g) p μ ≤
      sobolevNorm 1 p Ω (f - φ j)
    rw [eLpNorm_sub_comm]
    exact weakDeriv_eLpNorm_le_sobolevNorm hp hp' Ω hΩ α hα _ _ (hg.sub (hd j))
  have htrace (j : ℕ) : T (f - φ j) =ᵐ[volume] T f - T (φ j) := by
    simpa only [one_smul, neg_one_smul, sub_eq_add_neg] using
      hlinear f (φ j) hf (hφW j) 1 (-1)
  have htlim : Tendsto (fun j => eLpNorm (T (φ j) - T f) p volume)
      atTop (𝓝 0) := by
    have hmul : Tendsto (fun j => (C : ℝ≥0∞) * sobolevNorm 1 p Ω (f - φ j))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using
        ENNReal.Tendsto.const_mul hnorm (Or.inr ENNReal.coe_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
      (fun _ => zero_le)
    intro j
    change eLpNorm (T (φ j) - T f) p volume ≤
      (C : ℝ≥0∞) * sobolevNorm 1 p Ω (f - φ j)
    rw [eLpNorm_sub_comm, ← eLpNorm_congr_ae (htrace j)]
    exact (hbound _ (hdiff j)).2
  have hsmoothφ (j : ℕ) : IsSmoothCompactClosedHalfSpace (φ j) :=
    ⟨(hφ j).1.contDiffOn, tsupport (φ j), (hφ j).2.1,
      fun x _ hx => image_eq_zero_of_notMem_tsupport hx⟩
  have hb : Continuous (@boundaryPoint m) := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using (continuous_const :
        Continuous (fun _ : EuclideanSpace ℝ (Fin m) => (0 : ℝ)))
    · simpa only [Fin.snoc_castSucc] using
        (PiLp.continuous_apply (p := 2) (β := fun _ : Fin m => ℝ) j)
  let π : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin m) :=
    fun x => WithLp.toLp 2 (fun i => x i.castSucc)
  have hπ : Continuous π := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => (EuclideanSpace.proj i.castSucc).continuous)
  have hbc : HasCompactSupport (fun x' => ψ (boundaryPoint x')) := by
    have hs : Function.support (fun x' => ψ (boundaryPoint x')) ⊆ π '' tsupport ψ := by
      intro x hx
      refine ⟨boundaryPoint x, subset_tsupport ψ hx, ?_⟩
      ext i
      simp [π, boundaryPoint]
    exact ((hψ.2.1).image hπ).of_isClosed_subset isClosed_closure
      (closure_minimal hs ((hψ.2.1).image hπ).isClosed)
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (multiDeriv ψ α) := by
    have hs (l : List (Fin (m + 1))) :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iteratedPartial ψ l) := by
      induction l with
      | nil => exact hψ.1
      | cons i l ih =>
        exact (ih.contDiff_fderiv_apply (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).comp
          (contDiff_id.prodMk contDiff_const)
    exact hs _
  have hDc : HasCompactSupport (multiDeriv ψ α) := by
    have hs (l : List (Fin (m + 1))) : HasCompactSupport (iteratedPartial ψ l) := by
      induction l with
      | nil => exact hψ.2.1
      | cons i l ih => exact ih.fderiv_apply ℝ _
    exact hs _
  have hleft := MeasureTheory.tendsto_integral_mul_of_eLpNorm hp hp' μ
    (fun j => partialDeriv (φ j) (Fin.last m)) g hdLp hgp hdlim ψ hψ.1.continuous hψ.2.1
  have hright := MeasureTheory.tendsto_integral_mul_of_eLpNorm hp hp' μ
    φ f hφLp hfp hvlim (multiDeriv ψ α) hD.continuous hDc
  have hboundary := MeasureTheory.tendsto_integral_mul_of_eLpNorm hp hp' volume
    (fun j => T (φ j)) (T f) (fun j => (hbound _ (hφW j)).1)
    (hbound f hf).1 htlim (fun x' => ψ (boundaryPoint x')) (hψ.1.continuous.comp hb) hbc
  have heq (j : ℕ) :
      (∫ x in Ω, partialDeriv (φ j) (Fin.last m) x * ψ x) =
        -(∫ x in Ω, φ j x * multiDeriv ψ α x) -
          ∫ x', T (φ j) x' * ψ (boundaryPoint x') := by
    have hh := HunterPDE.Shared.integral_mul_smooth_normal (φ j) ψ (hφ j) hψ
    have hbnd : (∫ x', T (φ j) x' * ψ (boundaryPoint x')) =
        ∫ x', φ j (boundaryPoint x') * ψ (boundaryPoint x') :=
      integral_congr_ae ((hsmooth (φ j) (hsmoothφ j)).mul (Filter.Eventually.of_forall fun _ => rfl))
    rw [hbnd]
    exact hh
  exact tendsto_nhds_unique hleft
    ((hright.neg.sub hboundary).congr (fun j => (heq j).symm))
