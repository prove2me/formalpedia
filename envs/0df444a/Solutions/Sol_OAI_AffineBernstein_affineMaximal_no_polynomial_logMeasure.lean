-- Prove2me | solution 1 for OAI.AffineBernstein.affineMaximal_no_polynomial_logMeasure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:06:22.662092+00:00
-- url     : https://prove2.me/submissions/d238b889-1e10-4e8c-b4c3-c126d06295be

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_global_log_coordinate_identity
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_invariant_f_smooth
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_invariant_tube_positive
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_tube_angular_pair_nonneg
import Theorems.Thm_OAI_AffineBernstein_affineMaximal_tube_energy

section
-- module Solutions.OAIQ22_AB.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_WeightedDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section WeightedDivergence

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem contDiffAt_dirDeriv {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v : E) :
    ContDiffAt ℝ ∞ (dirDeriv v f) x :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

end WeightedDivergence

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DeterminantVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

/-- Expansion in the frozen Euclidean coordinate vectors. -/
theorem sum_coordinateVector {n : ℕ} (v : Space n) :
    (∑ i, (v i) • coordinateVector n i) = v := by
  ext j
  simp [coordinateVector, Pi.single_apply]

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CapCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

theorem hessian_eq_second {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i j : Fin n) :
    hessian u x i j =
      fderiv ℝ (fderiv ℝ u) x (coordinateVector n i) (coordinateVector n j) := by
  have hd := ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have he := hd.clm_apply (hasFDerivAt_const (coordinateVector n j) x)
  unfold hessian
  rw [he.fderiv]
  simp

theorem second_fderiv_eq_sum {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (v : Space n) :
    fderiv ℝ (fderiv ℝ u) x v v =
    ∑ i, ∑ j, v i * hessian u x i j * v j := by
  calc
    _ = fderiv ℝ (fderiv ℝ u) x (∑ i, v i • coordinateVector n i)
        (∑ j, v j • coordinateVector n j) := by rw [sum_coordinateVector]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hessian_eq_second hu,
        hu.isSymmSndFDerivAt (by simp)
          (coordinateVector n j) (coordinateVector n i)]
      ring

theorem second_fderiv_nonneg {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosSemidef) (v : Space n) :
    0 ≤ fderiv ℝ (fderiv ℝ u) x v v := by
  rw [second_fderiv_eq_sum hu]
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    using hp.dotProduct_mulVec_nonneg (fun i => v i)

theorem second_fderiv_pos {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) {v : Space n} (hv : v ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ u) x v v := by
  rw [second_fderiv_eq_sum hu]
  have hv' : (fun i => v i) ≠ 0 := fun he => hv (by ext i; exact congrFun he i)
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    using hp.dotProduct_mulVec_pos hv'

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GraphPatchArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/
theorem convexOn_of_hessian_posSemidef {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosSemidef) :
    ConvexOn ℝ Ω u := by
  refine ⟨hcv, ?_⟩
  intro x hx y hy a b ha hb hab
  let γ : ℝ → Space n := fun t => x + t • (y - x)
  let d : ℝ → ℝ := fun t => fderiv ℝ u (γ t) (y - x)
  let dd : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ u) (γ t) (y - x) (y - x)
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ Ω :=
    hcv.add_smul_mem hx (by simpa using hy) ht
  have hγ : ContDiff ℝ ∞ γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγd (t : ℝ) : HasDerivAt γ (y - x) t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hf : ContinuousOn (u ∘ γ) (Icc (0 : ℝ) 1) :=
    hu.continuousOn.comp hγ.continuous.continuousOn hseg
  have hdf (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt (u ∘ γ) (d t) (interior (Icc (0 : ℝ) 1)) t :=
    (((hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht)))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t (hγd t)).hasDerivWithinAt
  have hdd (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt d (dd t) (interior (Icc (0 : ℝ) 1)) t := by
    have hd := (((hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht)))).fderiv_right
      (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
    have he := hd.clm_apply (hasFDerivAt_const (y - x) (γ t))
    have hc := he.comp_hasDerivAt t (hγd t)
    simpa only [d, dd, Function.comp_def, ContinuousLinearMap.comp_zero,
      zero_add, ContinuousLinearMap.flip_apply] using
      hc.hasDerivWithinAt (s := interior (Icc (0 : ℝ) 1))
  have hc : ConvexOn ℝ (Icc (0 : ℝ) 1) (u ∘ γ) :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) hf hdf hdd
      (fun t ht => second_fderiv_nonneg
        (hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht))))
        (hp _ (hseg t (interior_subset ht))) (y - x))
  have he := hc.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) ha hb hab
  have heq : γ b = a • x + b • y := by
    dsimp [γ]
    rw [smul_sub]
    have ha' : a = 1 - b := by linarith
    rw [ha', sub_smul, one_smul]
    abel
  simpa [Function.comp_def, γ, heq, smul_eq_mul] using he

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SupportGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

section CompleteSphericalDependencies
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section SupportGeometry
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- The literal support value, not a freely chosen support coordinate. -/
theorem convex_first_order {W : Set E} {F : E → ℝ} (hF : ConvexOn ℝ W F)
    {x y : E} (hx : x ∈ W) (hy : y ∈ W) (hd : DifferentiableAt ℝ F x) :
    fderiv ℝ F x (y - x) ≤ F y - F x := by
  let γ : ℝ →ᵃ[ℝ] E :=
    { toFun := fun t => x + t • (y - x)
      linear := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (y - x)
      map_vadd' := by intro t s; simp [add_smul]; abel }
  have hc := hF.comp_affineMap γ
  have hdγ : HasDerivAt γ (y - x) 0 := by
    change HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hdx : HasFDerivAt F (fderiv ℝ F x) (γ 0) := by
    simpa [γ] using hd.hasFDerivAt
  have hs := hc.le_slope_of_hasDerivAt (x := 0) (y := 1)
    (by simpa [γ] using hx) (by simpa [γ] using hy) (by norm_num)
    (by simpa [γ] using hdx.comp_hasDerivAt 0 hdγ)
  simpa [slope_def_field, γ] using hs

/- A nonzero linear functional cannot attain its sublevel maximum below the level. -/
theorem sublevel_max_on_level {W : Set E} (hW : IsOpen W) {F : E → ℝ}
    {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) {z : E} (hz : z ∈ W)
    (hzF : F z ≤ 0) (hc : ContinuousAt F z)
    (hmax : IsMaxOn ℓ {y | y ∈ W ∧ F y ≤ 0} z) : F z = 0 := by
  by_contra hn
  have ht : F z < 0 := lt_of_le_of_ne hzF hn
  have hm : IsLocalMax ℓ z := by
    filter_upwards [hW.mem_nhds hz, hc.eventually (eventually_lt_nhds ht)] with y hy hyF
    exact hmax ⟨hy, hyF.le⟩
  exact hℓ (by simpa using hm.fderiv_eq_zero)

/- The support maximum of a compact smooth convex sublevel has a positive
Lagrange multiplier. This includes dimension one without a sphere convention. -/
theorem exists_support_multiplier [CompleteSpace E] {W : Set E} (hW : IsOpen W) {F : E → ℝ}
    (hcv : ConvexOn ℝ W F) (hF : ContDiffOn ℝ ∞ F W)
    {x₀ : E} (hx₀ : x₀ ∈ W) (hneg : F x₀ < 0)
    (hK : IsCompact {y | y ∈ W ∧ F y ≤ 0})
    {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    ∃ z ∈ W, F z = 0 ∧ ∃ lam : ℝ, 0 < lam ∧
      fderiv ℝ F z = lam • ℓ ∧
      (∀ y ∈ W, F y ≤ 0 → ℓ y ≤ ℓ z) ∧
      supportValue {y | y ∈ W ∧ F y ≤ 0} ℓ = ℓ z := by
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨x₀, hx₀, hneg.le⟩ ℓ.continuous.continuousOn
  have hd := hF.contDiffAt (hW.mem_nhds hz.1)
  have hzF := sublevel_max_on_level hW hℓ hz.1 hz.2 hd.continuousAt hmax
  have he : IsLocalExtrOn ℓ {y | F y = F z} z := by
    apply Or.inr
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hz.1)]
      with y hy hyW
    exact hmax ⟨hyW, by simp [hy, hzF]⟩
  obtain ⟨a, b, hab, heq⟩ := he.exists_multipliers_of_hasStrictFDerivAt_1d
    (hd.hasStrictFDerivAt (by simp)) ℓ.hasStrictFDerivAt
  have ha : a ≠ 0 := by
    intro ha
    have hb : b ≠ 0 := by simpa [ha] using hab
    simp only [ha, zero_smul, zero_add] at heq
    exact hℓ ((smul_eq_zero.mp heq).resolve_left hb)
  let lam := -b / a
  have hder : fderiv ℝ F z = lam • ℓ := by
    ext v
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) heq
    simp only [add_apply, smul_apply, zero_apply, smul_eq_mul] at hh ⊢
    dsimp [lam]
    field_simp
    nlinarith
  have hi := convex_first_order hcv hz.1 hx₀ (hd.differentiableAt (by simp))
  rw [hder, smul_apply, smul_eq_mul, hzF, sub_zero] at hi
  have hlin : ℓ (x₀ - z) ≤ 0 := by
    rw [map_sub, sub_nonpos]
    exact hmax ⟨hx₀, hneg.le⟩
  have hlam : 0 < lam := by
    by_contra ht
    have hh := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt ht) hlin
    linarith
  refine ⟨z, hz.1, hzF, lam, hlam, hder, ?_, ?_⟩
  · intro y hy hyF
    exact hmax ⟨hy, hyF⟩
  · unfold supportValue
    refine csSup_eq_of_forall_le_of_forall_lt_exists_gt (s := ℓ '' {y | y ∈ W ∧ F y ≤ 0}) ?_ ?_ ?_
    · exact ⟨ℓ z, z, hz, rfl⟩
    · rintro v ⟨y, hy, rfl⟩; exact hmax hy
    · intro b hb
      exact ⟨ℓ z, ⟨z, hz, rfl⟩, hb⟩

/- Linearization of the actual support equations `F(y)=0`, `DF(y)=lam*ell`. -/
theorem supportJacobian_injective {d : E →L[ℝ] ℝ}
    {H : E →L[ℝ] (E →L[ℝ] ℝ)} {ℓ : E →L[ℝ] ℝ} {lam : ℝ}
    (hℓ : ℓ ≠ 0) (hlam : lam ≠ 0) (hd : d = lam • ℓ)
    (hH : ∀ v : E, v ≠ 0 → 0 < H v v) :
    Function.Injective (supportJacobian d H ℓ) := by
  apply (injective_iff_map_eq_zero (supportJacobian d H ℓ)).mpr
  rintro ⟨v, a⟩ hv
  change (d v, H v - a • ℓ) = (0, 0) at hv
  have hv1 : d v = 0 := congrArg Prod.fst hv
  have hv2 : H v = a • ℓ := sub_eq_zero.mp (congrArg Prod.snd hv)
  have hlv : ℓ v = 0 := by
    simpa [hd, hlam] using hv1
  have hv0 : v = 0 := by
    by_contra hn
    have hh := hH v hn
    rw [hv2] at hh
    simp [hlv] at hh
  have ha0 : a = 0 := by
    rw [hv0, map_zero] at hv2
    exact (smul_eq_zero.mp hv2.symm).resolve_right hℓ
  simp [hv0, ha0]

theorem supportJacobian_isInvertible [FiniteDimensional ℝ E]
    {d : E →L[ℝ] ℝ} {H : E →L[ℝ] (E →L[ℝ] ℝ)}
    {ℓ : E →L[ℝ] ℝ} {lam : ℝ} (hℓ : ℓ ≠ 0) (hlam : lam ≠ 0)
    (hd : d = lam • ℓ) (hH : ∀ v : E, v ≠ 0 → 0 < H v v) :
    (supportJacobian d H ℓ).IsInvertible := by
  have hi := supportJacobian_injective hℓ hlam hd hH
  have hf : Module.finrank ℝ (E × ℝ) = Module.finrank ℝ (ℝ × (E →L[ℝ] ℝ)) := by
    rw [Module.finrank_prod, Module.finrank_prod,
      ← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq,
      Subspace.dual_finrank_eq]
    omega
  let e := (supportJacobian d H ℓ).toLinearMap.linearEquivOfInjective hi hf
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  rfl

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/- Fiber derivatives of the actual defining function. -/

theorem contDiffAt_fiberGradient {F : S × E → ℝ} {p : S × E}
    (hF : ContDiffAt ℝ ∞ F p) : ContDiffAt ℝ ∞ (fiberGradient F) p := by
  apply ContDiffAt.fderiv (n := ∞) (g := Prod.snd) _ contDiffAt_snd (by simp)
  exact hF.comp (p, p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)

theorem contDiffAt_supportEquations {F : S × E → ℝ} {s : S} {y : E}
    {ℓ : E →L[ℝ] ℝ} {lam : ℝ} (hF : ContDiffAt ℝ ∞ F (s, y)) :
    ContDiffAt ℝ ∞ (supportEquations F) ((s, ℓ), (y, lam)) := by
  have he : ContDiffAt ℝ ∞ (fun q : (S × (E →L[ℝ] ℝ)) × (E × ℝ) =>
      (q.1.1, q.2.1)) ((s, ℓ), (y, lam)) :=
    contDiffAt_fst.fst.prodMk contDiffAt_snd.fst
  have hc1 : ContDiffAt ℝ ∞ (fun q : (S × (E →L[ℝ] ℝ)) × (E × ℝ) =>
      F (q.1.1, q.2.1)) ((s, ℓ), (y, lam)) := hF.comp ((s, ℓ), (y, lam)) he
  have hc2 : ContDiffAt ℝ ∞ (fun q : (S × (E →L[ℝ] ℝ)) × (E × ℝ) =>
      fiberGradient F (q.1.1, q.2.1)) ((s, ℓ), (y, lam)) := by
    have hh := (contDiffAt_fiberGradient (F := F) (p := (s, y)) hF).comp ((s, ℓ), (y, lam)) he
    exact hh
  exact hc1.prodMk (hc2.sub (contDiffAt_snd.snd.smul contDiffAt_fst.snd))

theorem supportEquations_partial {F : S × E → ℝ} {s : S} {y : E}
    {ℓ : E →L[ℝ] ℝ} {lam : ℝ} (hF : ContDiffAt ℝ ∞ F (s, y)) :
    fderiv ℝ (supportEquations F) ((s, ℓ), (y, lam)) ∘L
      ContinuousLinearMap.inr ℝ (S × (E →L[ℝ] ℝ)) (E × ℝ) =
    supportJacobian (fderiv ℝ (fun z => F (s, z)) y)
      (fderiv ℝ (fderiv ℝ (fun z => F (s, z))) y) ℓ := by
  have hfu : ContDiffAt ℝ ∞ (fun z => F (s, z)) y :=
    hF.comp y (contDiffAt_const.prodMk contDiffAt_id)
  have hdu := hfu.differentiableAt (by simp)
  have h2u := (hfu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hp : HasFDerivAt (fun q : E × ℝ => supportEquations F ((s, ℓ), q))
      (supportJacobian (fderiv ℝ (fun z => F (s, z)) y)
        (fderiv ℝ (fderiv ℝ (fun z => F (s, z))) y) ℓ) (y, lam) := by
    exact (hdu.hasFDerivAt.comp (y, lam) (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt).prodMk
      ((h2u.hasFDerivAt.comp (y, lam) (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt).sub
        ((ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.smul_const ℓ))
  have hi : HasFDerivAt (fun q : E × ℝ => ((s, ℓ), q))
      (ContinuousLinearMap.inr ℝ (S × (E →L[ℝ] ℝ)) (E × ℝ)) (y, lam) := by
    convert (hasFDerivAt_const (s, ℓ) (y, lam)).prodMk (hasFDerivAt_id (y, lam)) using 1 <;>
      ext <;> simp
  exact (((contDiffAt_supportEquations (ℓ := ℓ) (lam := lam) hF).differentiableAt
    (by simp)).hasFDerivAt.comp (y, lam) hi).unique hp

/- A solution of the support equations with positive multiplier is a global,
not merely local, support point. -/
theorem supportValue_of_equations {W : Set E} {F : E → ℝ}
    (hcv : ConvexOn ℝ W F) {z : E} (hz : z ∈ W) (hzF : F z = 0)
    (hd : DifferentiableAt ℝ F z) {ℓ : E →L[ℝ] ℝ} {lam : ℝ}
    (hlam : 0 < lam) (he : fderiv ℝ F z = lam • ℓ) :
    supportValue {y | y ∈ W ∧ F y ≤ 0} ℓ = ℓ z := by
  unfold supportValue
  have hmax (y : E) (hy : y ∈ W ∧ F y ≤ 0) : ℓ y ≤ ℓ z := by
    have hh := convex_first_order hcv hz hy.1 hd
    simp only [he, smul_apply, smul_eq_mul, map_sub, hzF, sub_zero] at hh
    have hh' : lam * (ℓ y - ℓ z) ≤ 0 := by simpa [mul_sub] using hh.trans hy.2
    nlinarith
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt (s := ℓ '' {y | y ∈ W ∧ F y ≤ 0}) ?_ ?_ ?_
  · exact ⟨ℓ z, z, ⟨hz, hzF.le⟩, rfl⟩
  · rintro v ⟨y, hy, rfl⟩; exact hmax y hy
  · intro a ha; exact ⟨ℓ z, ⟨z, ⟨hz, hzF.le⟩, rfl⟩, ha⟩

/- Smooth dependence of the literal support value on base and conormal.
The IFT is applied to the actual defining function and its actual Hessian. -/
theorem contDiffAt_supportValue_fibers [FiniteDimensional ℝ E] [CompleteSpace S]
    {B : Set S} (hB : IsOpen B) {W : Set (S × E)} (hW : IsOpen W)
    {F : S × E → ℝ} (hF : ContDiffOn ℝ ∞ F W)
    (hcv : ∀ s ∈ B, ConvexOn ℝ {y | (s, y) ∈ W} (fun y => F (s, y)))
    {s : S} (hs : s ∈ B) {x₀ : E} (hx₀ : (s, x₀) ∈ W) (hneg : F (s, x₀) < 0)
    (hK : IsCompact {y | (s, y) ∈ W ∧ F (s, y) ≤ 0})
    (hH : ∀ y, (s, y) ∈ W → F (s, y) = 0 → ∀ v : E, v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun z => F (s, z))) y v v)
    {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : S × (E →L[ℝ] ℝ) =>
      supportValue {y | (q.1, y) ∈ W ∧ F (q.1, y) ≤ 0} q.2) (s, ℓ) := by
  have hWs : IsOpen {y | (s, y) ∈ W} := hW.preimage (by fun_prop)
  have hFs : ContDiffOn ℝ ∞ (fun y => F (s, y)) {y | (s, y) ∈ W} :=
    hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
  obtain ⟨z, hz, hzF, lam, hlam, hder, -, hsup⟩ :=
    exists_support_multiplier hWs (hcv s hs) hFs hx₀ hneg hK hℓ
  have hcF := hF.contDiffAt (hW.mem_nhds hz)
  have hg := contDiffAt_supportEquations (ℓ := ℓ) (lam := lam) hcF
  have hinv : (fderiv ℝ (supportEquations F) ((s, ℓ), (z, lam)) ∘L
      ContinuousLinearMap.inr ℝ (S × (E →L[ℝ] ℝ)) (E × ℝ)).IsInvertible := by
    rw [supportEquations_partial hcF]
    exact supportJacobian_isInvertible hℓ hlam.ne' hder (hH z hz hzF)
  let ψ := hg.implicitFunction (by simp) hinv
  have hψ : ContDiffAt ℝ ∞ ψ (s, ℓ) := hg.contDiffAt_implicitFunction (by simp) hinv
  have hψ₀ : ψ (s, ℓ) = (z, lam) := hg.implicitFunction_apply_self (by simp) hinv
  have hge : ∀ᶠ q in 𝓝 (s, ℓ), supportEquations F (q, ψ q) = 0 := by
    have hh := hg.eventually_apply_implicitFunction (by simp) hinv
    have hg0 : supportEquations F ((s, ℓ), (z, lam)) = 0 := by
      simp [supportEquations, fiberGradient, hzF, hder]
    simpa only [hg0, ψ] using hh
  have hnearW : ∀ᶠ q in 𝓝 (s, ℓ), (q.1, (ψ q).1) ∈ W := by
    apply (continuousAt_fst.prodMk hψ.continuousAt.fst).eventually
      (hW.mem_nhds (show ((s, ℓ).1, (ψ (s, ℓ)).1) ∈ W by simpa [hψ₀] using hz))
  have hnearL : ∀ᶠ q in 𝓝 (s, ℓ), 0 < (ψ q).2 := by
    exact hψ.continuousAt.snd.eventually (eventually_gt_nhds (by simpa [hψ₀] using hlam))
  have hnearB : ∀ᶠ q in 𝓝 (s, ℓ), q.1 ∈ B :=
    continuousAt_fst.eventually (hB.mem_nhds hs)
  have heq : (fun q : S × (E →L[ℝ] ℝ) =>
      supportValue {y | (q.1, y) ∈ W ∧ F (q.1, y) ≤ 0} q.2) =ᶠ[𝓝 (s, ℓ)]
      (fun q => q.2 ((ψ q).1)) := by
    filter_upwards [hge, hnearW, hnearL, hnearB] with q hq hqW hqL hqB
    have hzero : F (q.1, (ψ q).1) = 0 := congrArg Prod.fst hq
    have hgrad : fiberGradient F (q.1, (ψ q).1) = (ψ q).2 • q.2 :=
      sub_eq_zero.mp (congrArg Prod.snd hq)
    apply supportValue_of_equations (hcv q.1 hqB) hqW hzero _ hqL hgrad
    exact ((hF.contDiffAt (hW.mem_nhds hqW)).comp _
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  exact (contDiffAt_snd.clm_apply hψ.fst).congr_of_eventuallyEq heq

/- Finiteness of the literal support value on a compact fiber. -/
theorem le_supportValue {K : Set E} (hK : IsCompact K) {z : E} (hz : z ∈ K)
    (ℓ : E →L[ℝ] ℝ) : ℓ z ≤ supportValue K ℓ := by
  exact le_csSup (hK.image ℓ.continuous).bddAbove ⟨z, hz, rfl⟩

/- The envelope identity recovers the Gauss parametrization from the literal
support function; no choice of a surrogate support coordinate is involved. -/

theorem supportValue_pos [FiniteDimensional ℝ E] {K : Set E} (hK : IsCompact K)
    (hzero : (0 : E) ∈ interior K) {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    0 < supportValue K ℓ := by
  have hex : ∃ v : E, ℓ v ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hℓ
    ext v
    exact hn v
  obtain ⟨v, hv⟩ := hex
  let w := (ℓ v) • v
  have hw : 0 < ℓ w := by simp only [w, map_smul, smul_eq_mul]; exact mul_self_pos.mpr hv
  have hw0 : w ≠ 0 := by intro hh; simp [hh] at hw
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  let t := r / (2 * ‖w‖)
  have ht : 0 < t := div_pos hr (by positivity)
  have htw : t • w ∈ K := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    have hh : r / (2 * ‖w‖) * ‖w‖ = r / 2 := by field_simp
    rw [hh]
    linarith
  have hp : 0 < ℓ (t • w) := by simpa using mul_pos ht hw
  exact hp.trans_le (le_supportValue hK htw ℓ)

end SupportGeometry

/- Coordinate entries coincide with the actual second Fréchet differential. -/
/- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/

end CompleteSphericalDependencies

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- A genuine affine slice of the original epigraph, in arbitrary transverse
coordinates. -/
theorem affineEpigraphFiber_no_vertical {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {x : Space n} {z : ℝ} {A : E →L[ℝ] Space n}
    {b : E →L[ℝ] ℝ} (hK : IsCompact (affineEpigraphFiber Ω u x z A b))
    (hne : (affineEpigraphFiber Ω u x z A b).Nonempty)
    {v : E} (hv : A v = 0) : b v = 0 := by
  by_contra hb
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨M, hM⟩ := (hK.image b.continuous).bddAbove
  let r := max M (u (x + A y₀) - z) + 1
  let t := (r - b y₀) / b v
  have hbase : x + A (y₀ + t • v) = x + A y₀ := by simp [hv]
  have hheight : b (y₀ + t • v) = r := by
    simp only [map_add, map_smul, smul_eq_mul, t]
    field_simp
    ring
  have hy : y₀ + t • v ∈ affineEpigraphFiber Ω u x z A b := by
    refine ⟨by rw [hbase]; exact hy₀.1, ?_⟩
    rw [hbase, hheight]
    have hh := le_max_right M (u (x + A y₀) - z)
    dsimp [r]
    linarith
  have hh := hM (show b (y₀ + t • v) ∈ b '' affineEpigraphFiber Ω u x z A b from
    ⟨_, hy, rfl⟩)
  rw [hheight] at hh
  have hh' := le_max_left M (u (x + A y₀) - z)
  dsimp [r] at hh
  linarith

/- For an affine coordinate isomorphism compact fibers force injectivity of
its horizontal linear part. -/
theorem affineEpigraphFiber_injective {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {x : Space n} {z : ℝ} {A : E →L[ℝ] Space n}
    {b : E →L[ℝ] ℝ} (hK : IsCompact (affineEpigraphFiber Ω u x z A b))
    (hne : (affineEpigraphFiber Ω u x z A b).Nonempty)
    (hi : Function.Injective (fun y => (A y, b y))) : Function.Injective A := by
  intro v w hvw
  have hav : A (v - w) = 0 := by simpa [map_sub] using sub_eq_zero.mpr hvw
  have hb := affineEpigraphFiber_no_vertical hK hne hav
  have hbw : b v = b w := sub_eq_zero.mp (by simpa [map_sub] using hb)
  exact hi (Prod.ext hvw hbw)

/- Chain rule for the actual second differential of an affine epigraph slice. -/
theorem affineSlice_second {n : ℕ} {u : Space n → ℝ} {x : Space n} {z : ℝ}
    {A : E →L[ℝ] Space n} {b : E →L[ℝ] ℝ} {y : E}
    (hu : ContDiffAt ℝ ∞ u (x + A y)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun q => u (x + A q) - (z + b q))) y v w =
      fderiv ℝ (fderiv ℝ u) (x + A y) (A v) (A w) := by
  have he : fderiv ℝ (fun q => u (x + A q) - (z + b q)) =ᶠ[𝓝 y]
      (fun q => (fderiv ℝ u (x + A q)).comp A - b) := by
    have hne : ∀ᶠ q in 𝓝 y, DifferentiableAt ℝ u (x + A q) := by
      apply (continuous_const.add A.continuous).continuousAt.eventually
      have hh : ∀ᶠ p in 𝓝 (x + A y), ContDiffAt ℝ 1 u p :=
        (hu.of_le (by simp)).eventually (by simp)
      exact hh.mono (fun p hp => hp.differentiableAt (by simp))
    filter_upwards [hne] with q hq
    exact ((hq.hasFDerivAt.comp q (A.hasFDerivAt.const_add x)).sub
      (b.hasFDerivAt.const_add z)).fderiv
  rw [he.fderiv_eq]
  have hd := ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hc := (hd.comp y (A.hasFDerivAt.const_add x)).clm_comp (hasFDerivAt_const A y)
  have heq := (hc.sub_const b).fderiv
  simp only [Function.comp_def] at heq
  rw [heq]
  simp

/- An interior point of a convex sublevel is a strict sublevel point whenever
its actual Hessian is positive definite. -/
theorem sublevel_interior_strict [Nontrivial E] {W : Set E} {F : E → ℝ}
    (hcv : ConvexOn ℝ W F) {z : E}
    (hz : z ∈ interior {y | y ∈ W ∧ F y ≤ 0})
    (hd : DifferentiableAt ℝ F z)
    (hH : ∀ v : E, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ F) z v v) : F z < 0 := by
  have hzK := interior_subset hz
  by_contra hn
  have hz0 : F z = 0 := le_antisymm hzK.2 (le_of_not_gt hn)
  have hnK : {y | y ∈ W ∧ F y ≤ 0} ∈ 𝓝 z := mem_interior_iff_mem_nhds.mp hz
  have hm : IsLocalMax F z := by
    filter_upwards [hnK] with y hy
    simpa [hz0] using hy.2
  have hdz := hm.fderiv_eq_zero
  have he : F =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnK] with y hy
    have hh := convex_first_order hcv hzK.1 hy.1 hd
    simp only [hdz, zero_apply, hz0, sub_zero] at hh
    exact le_antisymm hy.2 hh
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hh := hH v hv
  rw [he.fderiv.fderiv_eq] at hh
  simp at hh

/- Convexity survives the actual affine slice and subtraction of its height. -/
theorem convexOn_affineSlice {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hcv : ConvexOn ℝ Ω u) (x : Space n) (z : ℝ)
    (A : E →L[ℝ] Space n) (b : E →L[ℝ] ℝ) :
    ConvexOn ℝ {y | x + A y ∈ Ω} (fun y => u (x + A y) - (z + b y)) := by
  let g : E →ᵃ[ℝ] Space n :=
    { toFun := fun y => x + A y
      linear := A.toLinearMap
      map_vadd' := by
        intro v p
        change x + A (p + v) = A p + (x + A v)
        rw [map_add]
        abel }
  have hc := hcv.comp_affineMap g
  have hb := (b.toLinearMap.concaveOn hc.1).add_const z
  have hh := hc.sub hb
  change ConvexOn ℝ {y | x + A y ∈ Ω} (fun y => u (x + A y) - (b y + z)) at hh
  simpa only [add_comm (b _) z] using hh

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/- The literal inverse image of the original epigraph under affine coordinates. -/

theorem affine_coordinates_split {n : ℕ} (a : Space n × ℝ)
    (L : (S × E) ≃L[ℝ] (Space n × ℝ)) (s : S) (y : E) :
    a + L (s, y) = ((a + L (s, 0)).1 + affineFiberHorizontal L y,
      (a + L (s, 0)).2 + affineFiberHeight L y) := by
  have hh : L (s, y) = L (s, 0) + L (0, y) := by rw [← map_add]; simp
  rw [hh]
  ext <;> simp [affineFiberHorizontal, affineFiberHeight, add_assoc]

theorem affineEpigraphPullback_fiber {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ)) (s : S) :
    {y | (s, y) ∈ affineEpigraphPullback Ω u a L} =
      affineEpigraphFiber Ω u (a + L (s, 0)).1 (a + L (s, 0)).2
        (affineFiberHorizontal L) (affineFiberHeight L) := by
  ext y
  change ((a + L (s, y)).1 ∈ Ω ∧ u (a + L (s, y)).1 ≤ (a + L (s, y)).2) ↔ _
  rw [affine_coordinates_split a L s y]
  rfl

theorem affineFiberHorizontal_injective {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {a : Space n × ℝ} {L : (S × E) ≃L[ℝ] (Space n × ℝ)} {s : S}
    (hK : IsCompact {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    (hne : {y | (s, y) ∈ affineEpigraphPullback Ω u a L}.Nonempty) :
    Function.Injective (affineFiberHorizontal L) := by
  rw [affineEpigraphPullback_fiber] at hK hne
  apply affineEpigraphFiber_injective hK hne
  intro v w hvw
  have hh : L (0, v) = L (0, w) := hvw
  exact congrArg Prod.snd (L.injective hh)

variable [CompleteSpace S]

/- The principal support-coordinate regularity assertion in tubes.tex:39–60,
for actual affine images of the standing epigraph, not abstract smooth bodies.
The transverse dimension is nonzero, as in the manuscript (m=n+1-k≥1). -/
theorem affineEpigraph_support_smooth [FiniteDimensional ℝ E] [Nontrivial E]
    {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : S × (E →L[ℝ] ℝ) =>
      supportValue {y | (q.1, y) ∈ affineEpigraphPullback Ω u a L} q.2) (s, ℓ) ∧
    0 < supportValue {y | (s, y) ∈ affineEpigraphPullback Ω u a L} ℓ := by
  let W : Set (S × E) := {p | (a + L p).1 ∈ Ω}
  let F : S × E → ℝ := fun p => u (a + L p).1 - (a + L p).2
  have hbase : ContDiff ℝ ∞ (fun p : S × E => (a + L p).1) :=
    (contDiff_const.add L.contDiff).fst
  have hheight : ContDiff ℝ ∞ (fun p : S × E => (a + L p).2) :=
    (contDiff_const.add L.contDiff).snd
  have hW : IsOpen W := hΩ.preimage hbase.continuous
  have hF : ContDiffOn ℝ ∞ F W :=
    (hu.comp hbase.contDiffOn (fun _ h => h)).sub hheight.contDiffOn
  have hFu : ConvexOn ℝ Ω u :=
    convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hFeq (r : S) : (fun q => F (r, q)) = (fun q =>
      u ((a + L (r, 0)).1 + affineFiberHorizontal L q) -
        ((a + L (r, 0)).2 + affineFiberHeight L q)) := by
    funext q
    change u (a + L (r, q)).1 - (a + L (r, q)).2 = _
    rw [affine_coordinates_split a L r q]
  have hWeq (r : S) : {y | (r, y) ∈ W} =
      {y | (a + L (r, 0)).1 + affineFiberHorizontal L y ∈ Ω} := by
    ext y
    change (a + L (r, y)).1 ∈ Ω ↔ _
    rw [affine_coordinates_split a L r y]
    rfl
  have hcvF (r : S) : ConvexOn ℝ {y | (r, y) ∈ W} (fun y => F (r, y)) := by
    rw [hFeq, hWeq]
    exact convexOn_affineSlice hFu (a + L (r, 0)).1 (a + L (r, 0)).2
      (affineFiberHorizontal L) (affineFiberHeight L)
  have hKeq (r : S) : {y | (r, y) ∈ W ∧ F (r, y) ≤ 0} =
      {y | (r, y) ∈ affineEpigraphPullback Ω u a L} := by
    ext y
    simp only [W, F, affineEpigraphPullback, mem_ofPred_eq, sub_nonpos]
  have hK' : IsCompact {y | (s, y) ∈ W ∧ F (s, y) ≤ 0} := by rw [hKeq]; exact hK s hs
  have hzero' : (0 : E) ∈ interior {y | (s, y) ∈ W ∧ F (s, y) ≤ 0} := by
    rw [hKeq]; exact hzero s hs
  have hA : Function.Injective (affineFiberHorizontal L) :=
    affineFiberHorizontal_injective (hK s hs) ⟨0, interior_subset (hzero s hs)⟩
  have hH (y : E) (hy : (s, y) ∈ W) (v : E) (hv : v ≠ 0) :
      0 < fderiv ℝ (fderiv ℝ (fun q => F (s, q))) y v v := by
    have huc := hu.contDiffAt (hΩ.mem_nhds hy)
    have hx : (a + L (s, y)).1 = (a + L (s, 0)).1 + affineFiberHorizontal L y :=
      congrArg Prod.fst (affine_coordinates_split a L s y)
    rw [hFeq, affineSlice_second (by rw [← hx]; exact huc)]
    exact second_fderiv_pos (by rw [← hx]; exact huc)
      (by rw [← hx]; exact hp _ hy)
      (fun hh => hv (hA (by simpa using hh)))
  have hzW : (s, (0 : E)) ∈ W := (interior_subset hzero').1
  have hzF : F (s, 0) < 0 := sublevel_interior_strict (hcvF s) hzero'
    (((hF.contDiffAt (hW.mem_nhds hzW)).comp 0
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)) (hH 0 hzW)
  have hh := contDiffAt_supportValue_fibers hB hW hF (fun r _ => hcvF r)
    hs hzW hzF hK' (fun y hy _ => hH y hy) hℓ
  refine ⟨?_, supportValue_pos (hK s hs) (hzero s hs) hℓ⟩
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext q
  rw [hKeq]

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GaussCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/- The one-homogeneous extension of the literal spherical support function. -/

theorem homogeneousSupport_le {K : Set E} (hK : IsCompact K)
    {z : E} (hz : z ∈ K) (e : E) : inner ℝ e z ≤ homogeneousSupport K e :=
  le_supportValue hK hz (InnerProductSpace.toDual ℝ E e)

theorem homogeneousSupport_eq_of_max {K : Set E} {e z : E}
    (hz : z ∈ K) (hm : IsMaxOn (fun y => inner ℝ e y) K z) :
    homogeneousSupport K e = inner ℝ e z := by
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · exact ⟨inner ℝ e z, z, hz, rfl⟩
  · rintro r ⟨y, hy, rfl⟩; exact hm hy
  · intro r hr; exact ⟨inner ℝ e z, ⟨z, hz, rfl⟩, hr⟩

theorem gaussPoint_eq_of_max {K : Set E} (hK : IsCompact K)
    {e z : E} (hz : z ∈ K) (hm : homogeneousSupport K e = inner ℝ e z)
    (hd : DifferentiableAt ℝ (homogeneousSupport K) e) : gaussPoint K e = z := by
  have hl : IsLocalMin (fun q => homogeneousSupport K q - inner ℝ z q) e := by
    apply Eventually.of_forall
    intro q
    have hh := homogeneousSupport_le hK hz q
    simpa [real_inner_comm z, hm] using sub_nonneg.mpr hh
  have hder := hd.hasFDerivAt.sub (InnerProductSpace.toDual ℝ E z).hasFDerivAt
  have hh : fderiv ℝ (homogeneousSupport K) e - InnerProductSpace.toDual ℝ E z = 0 := by
    rw [← hder.fderiv]
    exact hl.fderiv_eq_zero
  unfold gaussPoint gradient
  rw [sub_eq_zero.mp hh]
  simp

theorem gaussPoint_mem_support {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {e : E} (hd : DifferentiableAt ℝ (homogeneousSupport K) e) :
    gaussPoint K e ∈ K ∧
      homogeneousSupport K e = inner ℝ e (gaussPoint K e) := by
  obtain ⟨z, hz, hm⟩ := hK.exists_isMaxOn hne (InnerProductSpace.toDual ℝ E e).continuous.continuousOn
  have he := homogeneousSupport_eq_of_max hz hm
  rw [gaussPoint_eq_of_max hK hz he hd]
  exact ⟨hz, he⟩

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]

omit [CompleteSpace S] in
theorem contDiffAt_gaussPoint_fibers {K : S → Set E} {s : S} {e : E}
    (hh : ContDiffAt ℝ ∞ (fun p : S × E => homogeneousSupport (K p.1) p.2) (s,e)) :
    ContDiffAt ℝ ∞ (fun p : S × E => gaussPoint (K p.1) p.2) (s,e) := by
  exact ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt).comp
    (s,e) (contDiffAt_fiberGradient hh)

omit [CompleteSpace S] in
theorem contDiffAt_homogeneousSupport_fibers {K : S → Set E} {s : S} {e : E}
    (hh : ContDiffAt ℝ ∞ (fun q : S × (E →L[ℝ] ℝ) => supportValue (K q.1) q.2)
      (s, InnerProductSpace.toDual ℝ E e)) :
    ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) := by
  have hc : ContDiffAt ℝ ∞ (fun q : S × E =>
      (q.1, InnerProductSpace.toDual ℝ E q.2)) (s,e) :=
    contDiffAt_fst.prodMk
      ((InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.contDiff.contDiffAt.comp
        (s,e) contDiffAt_snd)
  have ht := hh.comp (s,e) hc
  exact ht

/- Actual smooth Gauss coordinates of each affine epigraph tube. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_JetCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem second_fderiv_comp {f : F → G} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f (g x)) (hg : ContDiffAt ℝ ∞ g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (f ∘ g)) x v w =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) +
        fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v w) := by
  have hdf := hf.differentiableAt (by simp)
  have hdg := hg.differentiableAt (by simp)
  have hddf := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hddg := (hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hdfg := (((hf.comp x hg).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
  have hleft := hdfg.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hright := (hddf.hasFDerivAt.comp x hdg.hasFDerivAt).clm_apply
    (hddg.hasFDerivAt.clm_apply (hasFDerivAt_const w x))
  have heq : (fun q => fderiv ℝ (f ∘ g) q w) =ᶠ[𝓝 x]
      (fun q => fderiv ℝ f (g q) (fderiv ℝ g q w)) := by
    have hfg : ∀ᶠ q in 𝓝 x, ContDiffAt ℝ 1 f (g q) := hg.continuousAt.eventually
      ((hf.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp))
    filter_upwards [hfg,
      (hg.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hqf hqg
    rw [fderiv_comp q (hqf.differentiableAt (by norm_num)) (hqg.differentiableAt (by norm_num))]
    rfl
  have he := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  have hh := congrArg (fun L : E →L[ℝ] G => L v) he
  simpa [add_comm] using hh

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualTubeSecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma homogeneousSupport_fibers_angular {K : S → Set E} {x : S × E}
    (hH : DifferentiableAt ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) x)
    (w : E) :
    fderiv ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) x (0,w) =
      inner ℝ (gaussPoint (K x.1) x.2) w := by
  have hd := hH.hasFDerivAt.comp (f := fun y : E => (x.1,y)) x.2
    ((hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2))
  have he : fderiv ℝ (homogeneousSupport (K x.1)) x.2 w =
      fderiv ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) x (0,w) := by
    change fderiv ℝ ((fun q : S × E => homogeneousSupport (K q.1) q.2) ∘
      (fun y : E => (x.1,y))) x.2 w = _
    rw [hd.fderiv]
    rfl
  rw [← he]
  simp [gaussPoint]

lemma homogeneousSupport_fibers_euler {K : S → Set E} {x : S × E}
    (hK : IsCompact (K x.1)) (hne : (K x.1).Nonempty)
    (hH : DifferentiableAt ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) x) :
    homogeneousSupport (K x.1) x.2 = inner ℝ x.2 (gaussPoint (K x.1) x.2) := by
  exact (gaussPoint_mem_support hK hne
    (hH.comp (f := fun y : E => (x.1,y)) x.2 (differentiableAt_const x.1 |>.prodMk differentiableAt_id))).2

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeDensityVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Matrix
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

lemma second_fderiv_affine_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : F → G} (L : S →L[ℝ] F) (a : F)
    {x : S} (hf : ContDiffAt ℝ ∞ f (a + L x)) (v w : S) :
    fderiv ℝ (fderiv ℝ (fun z => f (a + L z))) x v w =
      fderiv ℝ (fderiv ℝ f) (a + L x) (L v) (L w) := by
  have hd (z : S) : fderiv ℝ (fun z => a + L z) z = L := by
    exact ((L.hasFDerivAt).const_add a).fderiv
  have hdd : fderiv ℝ (fderiv ℝ (fun z => a + L z)) x = 0 := by
    rw [show fderiv ℝ (fun z => a + L z) = (fun _ => L) from funext hd]
    simp
  change fderiv ℝ (fderiv ℝ (f ∘ (fun z => a + L z))) x v w = _
  rw [second_fderiv_comp (g := fun z => a + L z) hf (contDiffAt_const.add L.contDiff.contDiffAt), hd, hdd]
  simp

lemma second_fderiv_prod_right {H : S × E → ℝ} {s : S} {e : E}
    (hH : ContDiffAt ℝ ∞ H (s,e)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => H (s,y))) e v w =
      fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,w) := by
  simpa using second_fderiv_affine_comp (ContinuousLinearMap.inr ℝ S E) (s,0) (by simpa using hH) v w

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualTubeArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma affineEpigraph_support_jets {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {e : E} (he : e ≠ 0) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    ContDiffAt ℝ ∞ H (s,e) ∧ ContDiffAt ℝ ∞ Y (s,e) ∧
      H =ᶠ[𝓝 (s,e)] (fun q => inner ℝ q.2 (Y q)) ∧
      ∀ᶠ q in 𝓝 (s,e), ∀ w : E, fderiv ℝ H q (0,w) = inner ℝ (Y q) w := by
  let K : S → Set E := fun r => {y | (r,y) ∈ affineEpigraphPullback Ω u a L}
  let H : S × E → ℝ := fun q => homogeneousSupport (K q.1) q.2
  let Y : S × E → E := fun q => gaussPoint (K q.1) q.2
  have hℓ : InnerProductSpace.toDual ℝ E e ≠ 0 := by
    intro hz; apply he
    exact (InnerProductSpace.toDual ℝ E).injective (hz.trans (map_zero _).symm)
  have hH : ContDiffAt ℝ ∞ H (s,e) := contDiffAt_homogeneousSupport_fibers
    (K := K) (affineEpigraph_support_smooth hΩ hcv hu hp a L hB hK hzero hs hℓ).1
  refine ⟨hH, contDiffAt_gaussPoint_fibers (K := K) hH, ?_, ?_⟩
  · filter_upwards [(continuous_fst.continuousAt.preimage_mem_nhds (hB.mem_nhds hs)),
      (hH.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hqs hq
    exact homogeneousSupport_fibers_euler (hK q.1 hqs) ⟨0, interior_subset (hzero q.1 hqs)⟩
      (hq.differentiableAt (by norm_num))
  · filter_upwards [(hH.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hq
    exact homogeneousSupport_fibers_angular (hq.differentiableAt (by norm_num))

/- Both matrices in the actual tube area formula are positive definite,
including an empty angular matrix. This is derived from the original graph,
not imposed as an additional curvature assumption. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatBlockCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma contDiffAt_adjugate_entries {A : E → Matrix ι ι ℝ} {x : E}
    (hA : ContDiffAt ℝ ∞ (fun y i j => A y i j) x) (i j : ι) :
    ContDiffAt ℝ ∞ (fun y => (A y).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  change ContDiffAt ℝ ∞ (fun y => continuousDetRows (fun l m => (A y).updateRow j (Pi.single i 1) l m)) x
  apply (continuousDetRows (ι := ι)).contDiff.contDiffAt.comp x
  apply contDiffAt_pi.mpr
  intro l
  by_cases hl : l = j
  · subst l
    simpa only [Matrix.updateRow_self] using (contDiffAt_const (c := (Pi.single i (1 : ℝ) : ι → ℝ)))
  · simp only [Matrix.updateRow_ne hl]
    exact (contDiffAt_pi.mp hA) l

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeInvariantSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
open scoped Matrix
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [CompleteSpace E] [DecidableEq ι] in
lemma contDiffAt_tubeFullRadiusMatrix {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    ContDiffAt ℝ ∞ (fun y i j => tubeFullRadiusMatrix H y b i j) q := by
  have hh := (hH.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
    (hh.clm_apply contDiffAt_const).clm_apply contDiffAt_const))

omit [CompleteSpace E] [DecidableEq ι] in
lemma contDiffAt_tubeBaseMatrix {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : Module.Basis ι ℝ S) :
    ContDiffAt ℝ ∞ (fun y i j => tubeBaseMatrix H y b i j) q := by
  have hh := (hH.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
    ((hh.clm_apply contDiffAt_const).clm_apply contDiffAt_const).neg))

omit [CompleteSpace E] in
lemma contDiffAt_tubeAngularDensity {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    ContDiffAt ℝ ∞ (fun y => tubeAngularDensity H y b) q := by
  change ContDiffAt ℝ ∞ (fun y => ∑ i, (tubeFullRadiusMatrix H y b).adjugate i i) q
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_adjugate_entries (contDiffAt_tubeFullRadiusMatrix hH b) i i

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeWeightAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/- Literal invariant tube measure coefficient with respect to `ds dω`. -/

lemma tubeMeasureCoefficient_pos {n : ℕ} {h B Q : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hQ : 0 < Q) :
    0 < tubeMeasureCoefficient n h B Q :=
  mul_pos (Real.rpow_pos_of_pos hh _) (Real.sqrt_pos.2 (mul_pos hB hQ))

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricVariationAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma contDiff_adjugate_entry (i j : ι) :
    ContDiff ℝ ∞ (fun A : ι → ι → ℝ => Matrix.adjugate (Matrix.of A) i j) := by
  simp only [Matrix.adjugate_apply]
  change ContDiff ℝ ∞ (continuousDetRows ∘ fun A : ι → ι → ℝ =>
    fun l m => Matrix.updateRow (Matrix.of A) j (Pi.single i 1) l m)
  apply (continuousDetRows (ι := ι)).contDiff.comp
  apply contDiff_pi.mpr
  intro l
  by_cases hl : l = j
  · subst l
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne hl, Matrix.of_apply]
    fun_prop

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NewtonTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- The penultimate Newton tensor, defined polynomially, not using an inverse. -/

theorem contDiff_newtonTensor_entry (i j : ι) :
    ContDiff ℝ ∞ (fun A : ι → ι → ℝ => newtonTensor (Matrix.of A) i j) := by
  exact ((contDiff_adjugate_entry i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_JointAngularCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Partial fiber gradient, represented through the derivative of the joint scalar. -/

lemma jointAngularGradient_eq_slice {g : S × E → ℝ} {q : S × E}
    (hg : DifferentiableAt ℝ g q) :
    jointAngularGradient g q = gradient (fun y => g (q.1,y)) q.2 := by
  have hc : HasFDerivAt (fun y : E => (q.1,y)) (ContinuousLinearMap.inr ℝ S E) q.2 := by
    convert (hasFDerivAt_const (𝕜 := ℝ) q.1 q.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) q.2) using 1 <;> ext y <;> rfl
  have hd : HasFDerivAt (fun y => g (q.1,y))
      ((fderiv ℝ g q).comp (ContinuousLinearMap.inr ℝ S E)) q.2 := hg.hasFDerivAt.comp q.2 hc
  change (InnerProductSpace.toDual ℝ E).symm _ = (InnerProductSpace.toDual ℝ E).symm _
  rw [hd.fderiv]

lemma contDiffAt_jointAngularGradient {g : S × E → ℝ} {q : S × E}
    (hg : ContDiffAt ℝ ∞ g q) : ContDiffAt ℝ ∞ (jointAngularGradient g) q := by
  apply (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp q
  exact (hg.fderiv_right (m := ∞) (by simp)).clm_comp contDiffAt_const

/- Partial angular derivative of the gradient, represented without slice-dependent differentiation. -/

lemma jointNewtonTensor_eq_slice {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    jointNewtonTensor H b q = supportNewtonTensor b (fun y => H (q.1,y)) q.2 := by
  unfold jointNewtonTensor supportNewtonTensor
  congr 2
  ext i j
  exact (second_fderiv_prod_right (s := q.1) (e := q.2) hH (b i) (b j)).symm

lemma contDiffAt_jointNewtonTensor {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    ContDiffAt ℝ ∞ (jointNewtonTensor H b) q := by
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    @NormedSpace.toIsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) _ _ _
  unfold jointNewtonTensor bilinearOfMatrix
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    ((contDiff_newtonTensor_entry i j).contDiffAt.comp q (contDiffAt_tubeFullRadiusMatrix hH b)).smul contDiffAt_const

lemma continuousOn_sliceAngularGradient {U : Set (S × E)} {g : S × E → ℝ}
    (hg : ∀ q ∈ U, ContDiffAt ℝ ∞ g q) :
    ContinuousOn (fun q : S × E => gradient (fun y => g (q.1,y)) q.2) U := by
  have hc : ContinuousOn (jointAngularGradient g) U :=
    fun q hq => (contDiffAt_jointAngularGradient (hg q hq)).continuousAt.continuousWithinAt
  apply hc.congr
  intro q hq
  exact (jointAngularGradient_eq_slice ((hg q hq).differentiableAt (by simp))).symm

lemma continuousOn_sliceNewtonTensor {U : Set (S × E)} {H : S × E → ℝ}
    (hH : ∀ q ∈ U, ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    ContinuousOn (fun q : S × E => supportNewtonTensor b (fun y => H (q.1,y)) q.2) U := by
  have hc : ContinuousOn (jointNewtonTensor H b) U :=
    fun q hq => (contDiffAt_jointNewtonTensor (hH q hq) b).continuousAt.continuousWithinAt
  apply hc.congr
  intro q hq
  exact (jointNewtonTensor_eq_slice (hH q hq) b).symm

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricSmoothness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma contDiffAt_inverse_matrix_entry_param {P ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype ι] [DecidableEq ι]
    {A : P → Matrix ι ι ℝ} {p : P}
    (hA : ContDiffAt ℝ ∞ (fun q i j => A q i j) p) (hd : (A p).det ≠ 0) (i j : ι) :
    ContDiffAt ℝ ∞ (fun q => (A q)⁻¹ i j) p := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact (((continuousDetRows (ι := ι)).contDiff.contDiffAt.comp p hA).inv hd).mul
    ((contDiff_adjugate_entry i j).contDiffAt.comp p hA)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_JointTubeMetrics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section JointTubeMetrics
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [CompleteSpace E] in
lemma contDiffAt_tubeBasePair {H f g : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (hf : ContDiffAt ℝ ∞ f q) (hg : ContDiffAt ℝ ∞ g q)
    (b : Module.Basis ι ℝ S) (hd : (tubeBaseMatrix H q b).det ≠ 0) :
    ContDiffAt ℝ ∞ (tubeBasePair H b f g) q := by
  apply hH.mul
  unfold flatInversePair
  exact ContDiffAt.sum fun j _ => ContDiffAt.sum fun i _ =>
    ((contDiffAt_inverse_matrix_entry_param (contDiffAt_tubeBaseMatrix hH b) hd i j).mul
      (contDiffAt_dirDeriv hf _)).mul (contDiffAt_dirDeriv hg _)

omit [CompleteSpace E] in
lemma continuousAt_tubeMeasureDensity {n : ℕ} {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hh : 0 < H q) : ContinuousAt (tubeMeasureDensity n H bS bE) q := by
  unfold tubeMeasureDensity tubeMeasureCoefficient
  apply (hH.continuousAt.rpow_const (Or.inl hh.ne')).mul
  exact (((continuousDetRows (ι := ι)).contDiff.contDiffAt.comp q
    (contDiffAt_tubeBaseMatrix hH bS)).continuousAt.mul
      (contDiffAt_tubeAngularDensity hH bE).continuousAt).sqrt

lemma continuousOn_tubeAngularPair {U : Set (S × E)} {H f g : S × E → ℝ}
    (hH : ∀ q ∈ U, ContDiffAt ℝ ∞ H q) (hf : ∀ q ∈ U, ContDiffAt ℝ ∞ f q)
    (hg : ∀ q ∈ U, ContDiffAt ℝ ∞ g q) (b : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hQ : ∀ q ∈ U, tubeAngularDensity H q b ≠ 0) :
    ContinuousOn (tubeAngularPair H b f g) U := by
  have ht (g : S × E → ℝ) (hg : ∀ q ∈ U, ContDiffAt ℝ ∞ g q) :
      ContinuousOn (fun q : S × E => tangentProjection q.2 (gradient (fun y => g (q.1,y)) q.2)) U := by
    have hd := continuousOn_sliceAngularGradient hg
    exact hd.sub ((((continuous_snd.continuousOn).inner hd)).smul continuous_snd.continuousOn)
  have hcH : ContinuousOn H U := fun q hq => (hH q hq).continuousAt.continuousWithinAt
  have hcQ : ContinuousOn (fun q => tubeAngularDensity H q b) U :=
    fun q hq => (contDiffAt_tubeAngularDensity (hH q hq) b).continuousAt.continuousWithinAt
  exact (hcH.div hcQ hQ).mul
    (((continuousOn_sliceNewtonTensor hH b).clm_apply (ht f hf)).clm_apply (ht g hg))

end JointTubeMetrics

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_MatrixMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma inverseMatrixPair_eq_dot (A : Matrix ι ι ℝ) (x y : ι → ℝ) :
    inverseMatrixPair A x y = y ⬝ᵥ A⁻¹.mulVec x := by
  simp only [inverseMatrixPair,dotProduct,Matrix.mulVec,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma inverseMatrixPair_self_nonneg {A : Matrix ι ι ℝ} (hA : A.PosDef) (x : ι → ℝ) :
    0 ≤ inverseMatrixPair A x x := by
  rw [inverseMatrixPair_eq_dot]
  simpa using hA.inv.posSemidef.dotProduct_mulVec_nonneg x

lemma inverseMatrixPair_symm {A : Matrix ι ι ℝ} (hA : A.IsSymm) (x y : ι → ℝ) :
    inverseMatrixPair A x y = inverseMatrixPair A y x := by
  have hi : A⁻¹.IsSymm := by rw [Matrix.IsSymm,Matrix.transpose_nonsing_inv,hA.eq]
  unfold inverseMatrixPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.transpose_apply A⁻¹ i j,hi.eq]
  ring

lemma inverseMatrixPair_add_left (A : Matrix ι ι ℝ) (x y z : ι → ℝ) :
    inverseMatrixPair A (fun i => x i+y i) z = inverseMatrixPair A x z+inverseMatrixPair A y z := by
  simp only [inverseMatrixPair,mul_add,add_mul,Finset.sum_add_distrib]

lemma inverseMatrixPair_add_right (A : Matrix ι ι ℝ) (x y z : ι → ℝ) :
    inverseMatrixPair A x (fun i => y i+z i) = inverseMatrixPair A x y+inverseMatrixPair A x z := by
  simp only [inverseMatrixPair,mul_add,Finset.sum_add_distrib]

lemma inverseMatrixPair_smul_left (A : Matrix ι ι ℝ) (t : ℝ) (x y : ι → ℝ) :
    inverseMatrixPair A (fun i => t*x i) y = t*inverseMatrixPair A x y := by
  simp only [inverseMatrixPair,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma inverseMatrixPair_smul_right (A : Matrix ι ι ℝ) (t : ℝ) (x y : ι → ℝ) :
    inverseMatrixPair A x (fun i => t*y i) = t*inverseMatrixPair A x y := by
  simp only [inverseMatrixPair,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/- Cauchy--Schwarz for a positive definite inverse matrix, including zero vectors. -/
lemma inverseMatrixPair_cauchy {A : Matrix ι ι ℝ} (hA : A.PosDef) (x y : ι → ℝ) :
    inverseMatrixPair A x y^2 ≤ inverseMatrixPair A x x*inverseMatrixPair A y y := by
  have hs : A.IsSymm := by simpa only [Matrix.isHermitian_iff_isSymm] using hA.isHermitian
  have hq (t : ℝ) : 0 ≤ inverseMatrixPair A y y*(t*t)+
      (2*inverseMatrixPair A x y)*t+inverseMatrixPair A x x := by
    have hh := inverseMatrixPair_self_nonneg hA (fun i => x i+t*y i)
    rw [inverseMatrixPair_add_left,inverseMatrixPair_add_right,inverseMatrixPair_add_right,
      inverseMatrixPair_smul_right,inverseMatrixPair_smul_left,inverseMatrixPair_smul_left,
      inverseMatrixPair_smul_right,inverseMatrixPair_symm hs y x] at hh
    nlinarith [hh]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeCompactIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section
variable {S T : Type*} [NormedAddCommGroup S]
  [MeasurableSpace S] [BorelSpace S]
  [TopologicalSpace T] [T2Space T] [CompactSpace T] [SecondCountableTopology T]
  [MeasurableSpace T] [BorelSpace T]
  {μ : Measure S} {ν : Measure T} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasure ν]
lemma integrable_joint_compact_mul {f : S × T → ℝ} {σ : S → ℝ}
    (hσ : Continuous σ) (hc : HasCompactSupport σ)
    (hf : ContinuousOn f (tsupport σ ×ˢ (Set.univ : Set T))) :
    Integrable (fun q : S × T => f q*σ q.1) (μ.prod ν) := by
  have hs : Function.support (fun q : S × T => f q*σ q.1) ⊆ tsupport σ ×ˢ (Set.univ : Set T) := by
    intro q hq
    refine ⟨?_,Set.mem_univ _⟩
    by_contra hn
    simp [image_eq_zero_of_notMem_tsupport hn] at hq
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  exact ContinuousOn.integrableOn_compact (hc.isCompact.prod isCompact_univ)
    (hf.mul (hσ.comp continuous_fst).continuousOn)
end
open Metric
variable {S E : Type*} [NormedAddCommGroup S]
  [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]

omit [MeasurableSpace S] [BorelSpace S]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
lemma continuous_tubeLift : Continuous (tubeLift (S := S) (E := E)) :=
  continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

omit [NormedAddCommGroup S]
  [MeasurableSpace S] [BorelSpace S] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tubeLift_mem {D : Set S} (q : S × sphere (0:E) 1) (h : q.1 ∈ D) :
    tubeLift q ∈ tubeOpenSet D := by
  refine ⟨h,?_⟩
  have hh : ‖(q.2:E)‖ = 1 := mem_sphere_zero_iff_norm.1 q.2.property
  intro hz
  change (q.2:E) = 0 at hz
  simp [hz] at hh

lemma integrable_tube_compact_mul {M g : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hσ : Continuous σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (hM : ContinuousOn M (tubeOpenSet D)) (hg : ContinuousOn g (tubeOpenSet D)) :
    Integrable (fun q : S × sphere (0:E) 1 => M (tubeLift q)*g (tubeLift q)*σ q.1)
      (μ.prod (volume.toSphere : Measure (sphere (0:E) 1))) := by
  apply integrable_joint_compact_mul hσ hc
  exact (hM.mul hg).comp continuous_tubeLift.continuousOn
    (fun q hq => tubeLift_mem q (hσD hq.1))

lemma integrable_tube_compact_sq {M g : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hσ : Continuous σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (hM : ContinuousOn M (tubeOpenSet D)) (hg : ContinuousOn g (tubeOpenSet D)) :
    Integrable (fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1^2*g (tubeLift q))
      (μ.prod (volume.toSphere : Measure (sphere (0:E) 1))) := by
  have hh := integrable_tube_compact_mul (μ := μ) hσ hc hσD hM
    (hg.mul (hσ.comp continuous_fst).continuousOn)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext q
  simp only [tubeLift,Pi.mul_apply,Function.comp_apply]
  ring

/- The unrestricted product integral of a cutoff times a tube coefficient. -/

lemma tubeIntegral_add {M f g : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hσ : Continuous σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (hM : ContinuousOn M (tubeOpenSet D)) (hf : ContinuousOn f (tubeOpenSet D))
    (hg : ContinuousOn g (tubeOpenSet D)) :
    tubeIntegral μ M σ (fun q => f q+g q) = tubeIntegral μ M σ f+tubeIntegral μ M σ g := by
  have hi (f) (hf : ContinuousOn f (tubeOpenSet D)) :
      Integrable (fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1*f (tubeLift q)) (μ.prod volume.toSphere) := by
    convert integrable_tube_compact_mul (μ := μ) hσ hc hσD hM hf using 1
    all_goals try with_reducible_and_instances rfl
    ext q; ring
  simp only [tubeIntegral,mul_add]
  exact integral_add (hi f hf) (hi g hg)

omit [MeasurableSpace S] [BorelSpace S] in
lemma tsupport_sq_subset {σ : S → ℝ} : tsupport (fun s => σ s^2) ⊆ tsupport σ := by
  simpa only [pow_two] using (tsupport_mul_subset_left (f := σ) (g := σ))

omit [MeasurableSpace S] [BorelSpace S] in
lemma compactSupport_sq {σ : S → ℝ} (hc : HasCompactSupport σ) :
    HasCompactSupport (fun s => σ s^2) :=
  hc.isCompact.of_isClosed_subset isClosed_closure tsupport_sq_subset

lemma integrable_tube_supported {f : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (hf : ContinuousOn f (tubeOpenSet D))
    (hz : ∀ s ∉ tsupport σ, ∀ e : E, f (s,e) = 0) :
    Integrable (fun q : S × sphere (0:E) 1 => f (tubeLift q)) (μ.prod volume.toSphere) := by
  have hs : Function.support (fun q : S × sphere (0:E) 1 => f (tubeLift q)) ⊆
      tsupport σ ×ˢ (Set.univ : Set (sphere (0:E) 1)) := by
    intro q hq
    refine ⟨?_,Set.mem_univ _⟩
    by_contra hn
    exact hq (hz q.1 hn q.2)
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  exact ContinuousOn.integrableOn_compact (hc.isCompact.prod isCompact_univ)
    (hf.comp continuous_tubeLift.continuousOn (fun q hq => tubeLift_mem q (hσD hq.1)))

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeMetricPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma tubeBasePair_nonneg {H : S × E → ℝ} {q : S × E} (b : Module.Basis ι ℝ S)
    (hh : 0 ≤ H q) (hB : (tubeBaseMatrix H q b).PosDef) (f : S × E → ℝ) :
    0 ≤ tubeBasePair H b f f q := mul_nonneg hh (inverseMatrixPair_self_nonneg hB _)

lemma tubeBasePair_cauchy {H : S × E → ℝ} {q : S × E} (b : Module.Basis ι ℝ S)
    (hB : (tubeBaseMatrix H q b).PosDef) (f g : S × E → ℝ) :
    tubeBasePair H b f g q^2 ≤ tubeBasePair H b f f q*tubeBasePair H b g g q := by
  have hc := mul_le_mul_of_nonneg_left (inverseMatrixPair_cauchy hB
    (fun i => dirDeriv (b i,(0:E)) f q) (fun i => dirDeriv (b i,(0:E)) g q)) (sq_nonneg (H q))
  change H q^2 * (flatInversePair _ _ f g q)^2 ≤ H q^2 *
    (flatInversePair _ _ f f q * flatInversePair _ _ g g q) at hc
  unfold tubeBasePair
  nlinarith [hc]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualGlobalCoercive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

theorem paired_cauchy_coercive {P D I a b c : ℝ}
    (hP : 0 ≤ P) (hD : 0 ≤ D) (hI : I ^ 2 ≤ P * D)
    (ha : 0 ≤ a) (hb : 0 < b) (hdet : c ^ 2 ≤ 4 * a * b) :
    0 ≤ a * P + c * I + b * D := by
  by_cases hP0 : P = 0
  · have hI0 : I = 0 := by nlinarith [sq_nonneg I]
    simp only [hI0, mul_zero, add_zero]
    exact add_nonneg (mul_nonneg ha hP) (mul_nonneg hb.le hD)
  have hPp : 0 < P := lt_of_le_of_ne hP (Ne.symm hP0)
  have h1 := mul_nonneg (show 0 ≤ 4 * a * b - c ^ 2 by linarith) (sq_nonneg P)
  have h2 := mul_nonneg (show 0 ≤ P * D - I ^ 2 by linarith) (show 0 ≤ 4 * b ^ 2 by positivity)
  have h3 := sq_nonneg (c * P + 2 * b * I)
  have htot : 0 ≤ 4 * b * P * (a * P + c * I + b * D) := by nlinarith
  exact nonneg_of_mul_nonneg_right htot (by positivity)

/- A fixed explicit lower coercivity constant for the exact source range.
In particular it is independent of the number of directions k >= 2. -/
theorem cauchy_young {P Q J a ε : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hJ : J ^ 2 ≤ P * Q) (hε : 0 < ε) :
    a * J ≤ ε * P + (a ^ 2 / (4 * ε)) * Q := by
  have hdet : (-a) ^ 2 ≤ 4 * (a ^ 2 / (4 * ε)) * ε := by
    field_simp
    nlinarith
  have h := paired_cauchy_coercive hQ hP (by nlinarith [hJ])
    (show 0 ≤ a ^ 2 / (4 * ε) by positivity) hε hdet
  nlinarith

/- The exact coefficients on the right of the source coercive identity. -/

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LinearLogTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

theorem tube_log_cutoff_absorption {n v PP DD EE AA Q PA DA RA : ℝ}
    (hn : 3 ≤ n) (hn9 : n ≤ 9) (hP : 0 ≤ PP) (hD : 0 ≤ DD) (hE : 0 ≤ EE)
    (hA : 0 ≤ AA) (hQ : 0 ≤ Q) (hPA : PA^2 ≤ AA*PP) (hDA : DA^2 ≤ AA*DD)
    (hRA : RA^2 ≤ AA*Q) :
    v^2*AA ≤ 4*v^2*(AA+n*PA+((n+2)/2)*DA)-8*v*RA+
      324*v^2*(1+PP+DD+EE)+16*Q := by
  have hpa := mul_le_mul_of_nonneg_left hPA (sq_nonneg v)
  have hda := mul_le_mul_of_nonneg_left hDA (sq_nonneg v)
  have hra := mul_le_mul_of_nonneg_left hRA (sq_nonneg v)
  have hp := cauchy_young (show 0 ≤ v^2*AA by positivity) hP
    (show (v*PA)^2 ≤ (v^2*AA)*PP by nlinarith [hpa]) (a := -n*v) (by norm_num : (0:ℝ) < 1/4)
  have hd := cauchy_young (show 0 ≤ v^2*AA by positivity) hD
    (show (v*DA)^2 ≤ (v^2*AA)*DD by nlinarith [hda]) (a := -((n+2)/2)*v) (by norm_num : (0:ℝ) < 1/4)
  have hr := cauchy_young (show 0 ≤ v^2*AA by positivity) hQ
    (show (v*RA)^2 ≤ (v^2*AA)*Q by nlinarith [hra]) (a := 2) (by norm_num : (0:ℝ) < 1/4)
  norm_num at hp hd hr
  have hnq : 0 ≤ 81-n^2 := by nlinarith [mul_nonneg (show 0 ≤ 9-n by linarith) (show 0 ≤ 9+n by linarith)]
  have hcq : 0 ≤ 81-((n+2)/2)^2 := by nlinarith [mul_nonneg (show 0 ≤ 18-(n+2) by linarith) (show 0 ≤ 18+(n+2) by linarith)]
  have hrem : 0 ≤ v^2*((81-n^2)*PP+(81-((n+2)/2)^2)*DD+81*(1+EE)) := by positivity
  nlinarith [hp,hd,hr,hrem]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_WeightedLogEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ S] [FiniteDimensional ℝ S] [Nontrivial E] in
theorem tube_compact_log_energy_of_identity {n : ℝ} (hn : 3 ≤ n) (hn9 : n ≤ 9)
    {D : Set S} {σ : S → ℝ} (hσ : Continuous σ) (hc : HasCompactSupport σ) (hsD : tsupport σ ⊆ D)
    {M PP DD EE AA PA DA Q RA : S × E → ℝ}
    (hM : ContinuousOn M (tubeOpenSet D)) (hPP : ContinuousOn PP (tubeOpenSet D))
    (hDD : ContinuousOn DD (tubeOpenSet D)) (hEE : ContinuousOn EE (tubeOpenSet D))
    (hAA : ContinuousOn AA (tubeOpenSet D)) (hPA : ContinuousOn PA (tubeOpenSet D))
    (hDA : ContinuousOn DA (tubeOpenSet D)) (hQ : ContinuousOn Q (tubeOpenSet D))
    (hRA : ContinuousOn RA (tubeOpenSet D))
    (hQzero : ∀ s ∉ tsupport σ, ∀ e : E, Q (s,e) = 0)
    (hpos : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ M (s,e) ∧ 0 ≤ PP (s,e) ∧ 0 ≤ DD (s,e) ∧
      0 ≤ EE (s,e) ∧ 0 ≤ AA (s,e) ∧ 0 ≤ Q (s,e) ∧ PA (s,e)^2 ≤ AA (s,e)*PP (s,e) ∧
      DA (s,e)^2 ≤ AA (s,e)*DD (s,e) ∧ RA (s,e)^2 ≤ AA (s,e)*Q (s,e))
    (hid : tubeIntegral μ M (fun s => σ s^2) (fun q => AA q+n*PA q+((n+2)/2)*DA q) =
      2*tubeIntegral μ M σ RA)
    (henergy : tubeIntegral μ M (fun s => σ s^2) (fun q => 1+PP q+DD q+EE q) ≤
      4194304*tubeIntegral μ M (fun _ => 1) Q) :
    tubeIntegral μ M (fun s => σ s^2) AA ≤ 1358954512*tubeIntegral μ M (fun _ => 1) Q := by
  let en := fun q => 1+PP q+DD q+EE q
  let hl := fun q => AA q+n*PA q+((n+2)/2)*DA q
  let iA := fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1^2*AA (tubeLift q)
  let iH := fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1^2*hl (tubeLift q)
  let iR := fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1*RA (tubeLift q)
  let iE := fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1^2*en (tubeLift q)
  let iQ := fun q : S × sphere (0:E) 1 => M (tubeLift q)*Q (tubeLift q)
  have hen : ContinuousOn en (tubeOpenSet D) := ((continuousOn_const.add hPP).add hDD).add hEE
  have hhl : ContinuousOn hl (tubeOpenSet D) := (hAA.add (continuousOn_const.mul hPA)).add
    (continuousOn_const.mul hDA)
  have hiA : Integrable iA (μ.prod volume.toSphere) := integrable_tube_compact_sq hσ hc hsD hM hAA
  have hiH : Integrable iH (μ.prod volume.toSphere) := integrable_tube_compact_sq hσ hc hsD hM hhl
  have hiR : Integrable iR (μ.prod volume.toSphere) := by
    convert integrable_tube_compact_mul (μ := μ) hσ hc hsD hM hRA using 1
    all_goals try with_reducible_and_instances rfl
    ext q; dsimp [iR]; ring
  have hiE : Integrable iE (μ.prod volume.toSphere) := integrable_tube_compact_sq hσ hc hsD hM hen
  have hiQ : Integrable iQ (μ.prod volume.toSphere) :=
    integrable_tube_supported hc hsD (hM.mul hQ) (fun s hs e => by simp [hQzero s hs e])
  have hup := integral_mono_ae hiA ((((hiH.const_mul 4).sub (hiR.const_mul 8)).add
    (hiE.const_mul 324)).add (hiQ.const_mul 16)) (Filter.Eventually.of_forall fun q => by
      dsimp only [Pi.add_apply,Pi.sub_apply]
      by_cases hs : q.1 ∈ tsupport σ
      · have hh := hpos q.1 (hsD hs) q.2 (mem_sphere_zero_iff_norm.1 q.2.property)
        have ha := tube_log_cutoff_absorption hn hn9 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1
          hh.2.2.2.2.2.1 hh.2.2.2.2.2.2.1 hh.2.2.2.2.2.2.2.1 hh.2.2.2.2.2.2.2.2 (v := σ q.1)
        have ham := mul_le_mul_of_nonneg_left ha hh.1
        dsimp only [iA,iH,iR,iE,iQ,hl,en,tubeLift]
        nlinarith [ham]
      · simp [iA,iH,iR,iE,iQ,tubeLift,image_eq_zero_of_notMem_tsupport hs,hQzero q.1 hs q.2])
  have hlin : (∫ q, (((fun q => 4*iH q)-(fun q => 8*iR q))+(fun q => 324*iE q)+
      (fun q => 16*iQ q)) q ∂μ.prod volume.toSphere) =
      4*(∫ q, iH q ∂μ.prod volume.toSphere)-8*(∫ q, iR q ∂μ.prod volume.toSphere)+
      324*(∫ q, iE q ∂μ.prod volume.toSphere)+16*(∫ q, iQ q ∂μ.prod volume.toSphere) := by
    have h₁ := integral_add (((hiH.const_mul 4).sub (hiR.const_mul 8)).add (hiE.const_mul 324)) (hiQ.const_mul 16)
    have h₂ := integral_add ((hiH.const_mul 4).sub (hiR.const_mul 8)) (hiE.const_mul 324)
    have h₃ := integral_sub (hiH.const_mul 4) (hiR.const_mul 8)
    simp only [Pi.add_apply,Pi.sub_apply] at h₁ h₂ h₃ ⊢
    rw [h₁,h₂,h₃,integral_const_mul,integral_const_mul,integral_const_mul,integral_const_mul]
  rw [hlin] at hup
  change tubeIntegral μ M (fun s => σ s^2) AA ≤
    4*tubeIntegral μ M (fun s => σ s^2) hl-8*tubeIntegral μ M σ RA+
    324*tubeIntegral μ M (fun s => σ s^2) en+16*(∫ q, iQ q ∂μ.prod volume.toSphere) at hup
  have hqI : (∫ q, iQ q ∂μ.prod volume.toSphere) = tubeIntegral μ M (fun _ => 1) Q := by
    simp [iQ,tubeIntegral]
  rw [hqI,hid] at hup
  change tubeIntegral μ M (fun s => σ s^2) en ≤ _ at henergy
  linarith

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualLogEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem affineMaximal_tube_log_coordinate_energy {n : ℕ} (hn : 3 ≤ n) (hn9 : n ≤ 9) {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hk : 2 ≤ Fintype.card ι)
    (ℓ : S →L[ℝ] ℝ) (hℓ : ∀ s ∈ D, 0 < ℓ s)
    {σ : S → ℝ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let M := tubeMeasureDensity n H bS bE
    tubeIntegral μ M (fun s => σ s^2)
      (tubeBasePair H bS (fun q => Real.log (ℓ q.1)) (fun q => Real.log (ℓ q.1))) ≤
      1358954512*tubeIntegral μ M (fun _ => 1) (tubeBasePair H bS (fun q => σ q.1) (fun q => σ q.1)) := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let P := fun q => Real.log (H q)
  let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
  let M := tubeMeasureDensity n H bS bE
  let V := fun q : S × E => σ q.1
  let A := fun q : S × E => Real.log (ℓ q.1)
  have hA (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ A q :=
    (ℓ.contDiff.contDiffAt.comp q contDiffAt_fst).log (hℓ q.1 hq.1).ne'
  have hH (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ H q :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hq.1 hq.2).1
  have hpos (q : S × E) (hq : q ∈ tubeOpenSet D) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 bS bE
  have hF (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ F q :=
    affineEpigraph_invariant_f_smooth hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 bS bE _
  have hP (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ P q :=
    (hH q hq).log (hpos q hq).2.2.ne'
  have hV (q : S × E) (_ : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ V q :=
    hσ.contDiffAt.comp q contDiffAt_fst
  have hM : ContinuousOn M (tubeOpenSet D) := fun q hq =>
    (continuousAt_tubeMeasureDensity (hH q hq) bS bE (hpos q hq).2.2).continuousWithinAt
  have hpair (f g : S × E → ℝ) (hf : ∀ q ∈ tubeOpenSet D, ContDiffAt ℝ ∞ f q)
      (hg : ∀ q ∈ tubeOpenSet D, ContDiffAt ℝ ∞ g q) : ContinuousOn (tubeBasePair H bS f g) (tubeOpenSet D) :=
    fun q hq => (contDiffAt_tubeBasePair (hH q hq) (hf q hq) (hg q hq) bS
       (hpos q hq).1.det_pos.ne').continuousAt.continuousWithinAt
  have hEE : ContinuousOn (tubeAngularPair H bE F F) (tubeOpenSet D) :=
    continuousOn_tubeAngularPair hH hF hF bE (fun q hq => (hpos q hq).2.1.ne')
  have hQzero (s : S) (hs : s ∉ tsupport σ) (e : E) : tubeBasePair H bS V V (s,e) = 0 := by
    have hd : fderiv ℝ V (s,e) = 0 := by
      dsimp only [V]
      rw [show (fun q : S × E => σ q.1) = σ ∘ Prod.fst by rfl,
        fderiv_comp (s,e) (hσ.differentiable (by simp) s) differentiableAt_fst,
        fderiv_of_notMem_tsupport ℝ hs]
      simp
    simp [tubeBasePair,flatInversePair,dirDeriv,hd]
  have hid := affineEpigraph_global_log_coordinate_identity (μ := μ)
    hΩ hcv hu hp a L hD hK hzero bS bE ℓ hℓ hσ hc hσD
  have he := affineMaximal_tube_energy (μ := μ) hn hn9 hΩ hcv hu hp hm a L hD hK hzero
    bS bE hk hσ hc hσD
  apply tube_compact_log_energy_of_identity (n := (n : ℝ))
    (by exact_mod_cast hn) (by exact_mod_cast hn9)
    hσ.continuous hc hσD hM (hpair P P hP hP) (hpair F F hF hF) hEE
    (hpair A A hA hA) (hpair P A hP hA) (hpair F A hF hA)
    (hpair V V hV hV) (hpair V A hV hA) hQzero _ hid he
  intro s hs e he
  have hen : e ≠ 0 := by intro hz; simp [hz] at he
  have hq : (s,e) ∈ tubeOpenSet D := ⟨hs,hen⟩
  have hz := hpos (s,e) hq
  refine ⟨(tubeMeasureCoefficient_pos hz.2.2 hz.1.det_pos hz.2.1).le,
    tubeBasePair_nonneg bS hz.2.2.le hz.1 P,
    tubeBasePair_nonneg bS hz.2.2.le hz.1 F,
    affineEpigraph_tube_angular_pair_nonneg hΩ hcv hu hp a L hD hK hzero hs he bS bE
      ((hF (s,e) hq).differentiableAt (by simp)),
    tubeBasePair_nonneg bS hz.2.2.le hz.1 A,
    tubeBasePair_nonneg bS hz.2.2.le hz.1 V, ?_, ?_, ?_⟩
  · simpa only [mul_comm] using tubeBasePair_cauchy bS hz.1 P A
  · simpa only [mul_comm] using tubeBasePair_cauchy bS hz.1 F A
  · simpa only [mul_comm] using tubeBasePair_cauchy bS hz.1 V A

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeSumIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {S E : Type*} [NormedAddCommGroup S]
  [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]

lemma tubeIntegral_sum {J : Type*} (t : Finset J) {M : S × E → ℝ} {f : J → S × E → ℝ}
    {σ : S → ℝ} {D : Set S} (hσ : Continuous σ) (hc : HasCompactSupport σ)
    (hsD : tsupport σ ⊆ D) (hM : ContinuousOn M (tubeOpenSet D))
    (hf : ∀ j ∈ t, ContinuousOn (f j) (tubeOpenSet D)) :
    tubeIntegral μ M σ (fun q => ∑ j ∈ t, f j q) = ∑ j ∈ t, tubeIntegral μ M σ (f j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [tubeIntegral]
  | @insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    rw [tubeIntegral_add hσ hc hsD hM (hf a (Finset.mem_insert_self _ _))
      (continuousOn_finsetSum _ fun j hj => hf j (Finset.mem_insert_of_mem hj))]
    rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

lemma tubeIntegral_mono_sq {M f g : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hσ : Continuous σ) (hc : HasCompactSupport σ) (hsD : tsupport σ ⊆ D)
    (hM : ContinuousOn M (tubeOpenSet D)) (hf : ContinuousOn f (tubeOpenSet D))
    (hg : ContinuousOn g (tubeOpenSet D))
    (hpos : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ M (s,e))
    (hfg : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → f (s,e) ≤ g (s,e)) :
    tubeIntegral μ M (fun s => σ s^2) f ≤ tubeIntegral μ M (fun s => σ s^2) g := by
  apply integral_mono_ae (integrable_tube_compact_sq hσ hc hsD hM hf)
    (integrable_tube_compact_sq hσ hc hsD hM hg)
  apply Filter.Eventually.of_forall
  intro q
  by_cases hs : q.1 ∈ tsupport σ
  · exact mul_le_mul_of_nonneg_left (hfg q.1 (hsD hs) q.2 (mem_sphere_zero_iff_norm.1 q.2.property))
      (mul_nonneg (hpos q.1 (hsD hs) q.2 (mem_sphere_zero_iff_norm.1 q.2.property)) (sq_nonneg _))
  · simp [image_eq_zero_of_notMem_tsupport hs]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualLogMeasureEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem affineMaximal_tube_log_measure_energy {n : ℕ} (hn : 3 ≤ n) (hn9 : n ≤ 9) {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hk : 2 ≤ Fintype.card ι)
    (ℓ : ι → S →L[ℝ] ℝ) (hℓ : ∀ i, ∀ s ∈ D, 0 < ℓ i s)
    {σ : S → ℝ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let M := tubeMeasureDensity n H bS bE
    tubeIntegral μ M (fun s => σ s^2)
      (fun q => 1+∑ i, tubeBasePair H bS (fun q => Real.log (ℓ i q.1))
        (fun q => Real.log (ℓ i q.1)) q) ≤
      (4194304+(Fintype.card ι : ℝ)*1358954512)*tubeIntegral μ M (fun _ => 1) (tubeBasePair H bS (fun q => σ q.1) (fun q => σ q.1)) := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let P := fun q => Real.log (H q)
  let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
  let M := tubeMeasureDensity n H bS bE
  let V := fun q : S × E => σ q.1
  let A := fun i (q : S × E) => Real.log (ℓ i q.1)
  have hA (i : ι) (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ (A i) q :=
    ((ℓ i).contDiff.contDiffAt.comp q contDiffAt_fst).log (hℓ i q.1 hq.1).ne'
  have hH (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ H q :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hq.1 hq.2).1
  have hpos (q : S × E) (hq : q ∈ tubeOpenSet D) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 bS bE
  have hF (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ F q :=
    affineEpigraph_invariant_f_smooth hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 bS bE _
  have hP (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ P q :=
    (hH q hq).log (hpos q hq).2.2.ne'
  have hV (q : S × E) (_ : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ V q :=
    hσ.contDiffAt.comp q contDiffAt_fst
  have hM : ContinuousOn M (tubeOpenSet D) := fun q hq =>
    (continuousAt_tubeMeasureDensity (hH q hq) bS bE (hpos q hq).2.2).continuousWithinAt
  have hpair (f g : S × E → ℝ) (hf : ∀ q ∈ tubeOpenSet D, ContDiffAt ℝ ∞ f q)
      (hg : ∀ q ∈ tubeOpenSet D, ContDiffAt ℝ ∞ g q) : ContinuousOn (tubeBasePair H bS f g) (tubeOpenSet D) :=
    fun q hq => (contDiffAt_tubeBasePair (hH q hq) (hf q hq) (hg q hq) bS
       (hpos q hq).1.det_pos.ne').continuousAt.continuousWithinAt
  have hEE : ContinuousOn (tubeAngularPair H bE F F) (tubeOpenSet D) :=
    continuousOn_tubeAngularPair hH hF hF bE (fun q hq => (hpos q hq).2.1.ne')
  have he := affineMaximal_tube_energy (μ := μ) hn hn9 hΩ hcv hu hp hm a L hD hK hzero
    bS bE hk hσ hc hσD
  have ha (i : ι) := affineMaximal_tube_log_coordinate_energy (μ := μ) hn hn9 hΩ hcv hu hp hm a L
    hD hK hzero bS bE hk (ℓ i) (hℓ i) hσ hc hσD
  let Q := tubeBasePair H bS V V
  have h1 : tubeIntegral μ M (fun s => σ s^2) (fun _ => 1) ≤
      4194304*tubeIntegral μ M (fun _ => 1) Q := by
    apply le_trans (tubeIntegral_mono_sq hσ.continuous hc hσD hM continuousOn_const
      (((continuousOn_const.add (hpair P P hP hP)).add (hpair F F hF hF)).add hEE) ?_ ?_) he
    · intro s hs e he
      have hen : e ≠ 0 := by intro hz; simp [hz] at he
      have hz := hpos (s,e) ⟨hs,hen⟩
      exact (tubeMeasureCoefficient_pos hz.2.2 hz.1.det_pos hz.2.1).le
    · intro s hs e he
      have hen : e ≠ 0 := by intro hz; simp [hz] at he
      have hz := hpos (s,e) ⟨hs,hen⟩
      have hp0 := tubeBasePair_nonneg bS hz.2.2.le hz.1 P
      have hf0 := tubeBasePair_nonneg bS hz.2.2.le hz.1 F
      have he0 := affineEpigraph_tube_angular_pair_nonneg hΩ hcv hu hp a L hD hK hzero hs he bS bE
        ((hF (s,e) ⟨hs,hen⟩).differentiableAt (by simp))
      change 0 ≤ tubeBasePair H bS P P (s,e) at hp0
      change 0 ≤ tubeBasePair H bS F F (s,e) at hf0
      change 0 ≤ tubeAngularPair H bE F F (s,e) at he0
      change 1 ≤ 1+tubeBasePair H bS P P (s,e)+tubeBasePair H bS F F (s,e)+tubeAngularPair H bE F F (s,e)
      linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => ha i)
  change (∑ i, tubeIntegral μ M (fun s => σ s^2) (tubeBasePair H bS (A i) (A i))) ≤
    ∑ i : ι, 1358954512*tubeIntegral μ M (fun _ => 1) Q at hsum
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  change tubeIntegral μ M (fun s => σ s^2) (fun q => 1+∑ i, tubeBasePair H bS (A i) (A i) q) ≤ _
  rw [tubeIntegral_add (σ := fun s => σ s^2) (hσ.continuous.pow 2) (compactSupport_sq hc) (tsupport_sq_subset.trans hσD)
    hM continuousOn_const (continuousOn_finsetSum _ fun i _ => hpair (A i) (A i) (hA i) (hA i))]
  rw [tubeIntegral_sum Finset.univ (σ := fun s => σ s^2) (hσ.continuous.pow 2) (compactSupport_sq hc)
    (tsupport_sq_subset.trans hσD) hM (fun i _ => hpair (A i) (A i) (hA i) (hA i))]
  change _ ≤ (4194304+(Fintype.card ι : ℝ)*1358954512)*tubeIntegral μ M (fun _ => 1) Q
  nlinarith

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_MatrixCombination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]

omit [Fintype J] in
lemma inverseMatrixPair_sum_left (A : Matrix ι ι ℝ) (t : Finset J)
    (v : J → ι → ℝ) (w : ι → ℝ) :
    inverseMatrixPair A (fun i => ∑ j ∈ t, v j i) w = ∑ j ∈ t, inverseMatrixPair A (v j) w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [inverseMatrixPair]
  | @insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    rw [inverseMatrixPair_add_left,ih]

/- Cauchy--Schwarz for an arbitrary finite linear combination in the literal inverse metric. -/
lemma inverseMatrixPair_combination {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (a : J → ℝ) (v : J → ι → ℝ) :
    inverseMatrixPair A (fun i => ∑ j, a j*v j i) (fun i => ∑ j, a j*v j i) ≤
      (∑ j, a j^2)*(∑ j, inverseMatrixPair A (v j) (v j)) := by
  let z := fun i => ∑ j, a j*v j i
  let B := inverseMatrixPair A z z
  have hB : 0 ≤ B := inverseMatrixPair_self_nonneg hA z
  have hs : B = ∑ j, a j*inverseMatrixPair A (v j) z := by
    dsimp only [B]
    change inverseMatrixPair A (fun i => ∑ j, a j*v j i) z = _
    rw [inverseMatrixPair_sum_left]
    simp only [inverseMatrixPair_smul_left]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) (f := a)
    (g := fun j => inverseMatrixPair A (v j) z)
  have hsum : (∑ j, inverseMatrixPair A (v j) z^2) ≤ (∑ j, inverseMatrixPair A (v j) (v j))*B := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => inverseMatrixPair_cauchy hA (v j) z
  have hn : 0 ≤ ∑ j, a j^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsum hn
  rw [← hs] at hc
  have hC : 0 ≤ (∑ j, a j^2)*(∑ j, inverseMatrixPair A (v j) (v j)) :=
    mul_nonneg hn (Finset.sum_nonneg fun j _ => inverseMatrixPair_self_nonneg hA (v j))
  change B ≤ _
  nlinarith

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeCombination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section TubeCombination
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]

lemma tubeBasePair_linearCombination {H : S × E → ℝ} (b : Module.Basis ι ℝ S)
    {q : S × E} (hp : 0 ≤ H q) (hB : (tubeBaseMatrix H q b).PosDef)
    (v : S × E → ℝ) (α : J → S × E → ℝ) (a : J → ℝ)
    (hd : ∀ i, dirDeriv (b i, (0 : E)) v q = ∑ j, a j*dirDeriv (b i, (0 : E)) (α j) q) :
    tubeBasePair H b v v q ≤ (∑ j, a j^2)*(∑ j, tubeBasePair H b (α j) (α j) q) := by
  have hv : (fun i => dirDeriv (b i,(0:E)) v q) =
      (fun i => ∑ j, a j*dirDeriv (b i,(0:E)) (α j) q) := funext hd
  have hc := inverseMatrixPair_combination hB a (fun j i => dirDeriv (b i,(0:E)) (α j) q)
  have hm := mul_le_mul_of_nonneg_left hc hp
  change H q * inverseMatrixPair (tubeBaseMatrix H q b) (fun i => dirDeriv (b i,(0:E)) v q)
    (fun i => dirDeriv (b i,(0:E)) v q) ≤ _
  rw [hv]
  have hr : (∑ j, a j^2)*(∑ j, tubeBasePair H b (α j) (α j) q) =
      H q*((∑ j, a j^2)*(∑ j, inverseMatrixPair (tubeBaseMatrix H q b)
        (fun i => dirDeriv (b i,(0:E)) (α j) q) (fun i => dirDeriv (b i,(0:E)) (α j) q))) := by
    change (∑ j, a j^2)*(∑ j, H q*inverseMatrixPair (tubeBaseMatrix H q b)
      (fun i => dirDeriv (b i,(0:E)) (α j) q) (fun i => dirDeriv (b i,(0:E)) (α j) q)) = _
    rw [← Finset.mul_sum]
    ring
  rw [hr]
  exact hm

end TubeCombination

/- The manuscript's positive base orthant. -/

lemma isOpen_positiveOrthant (k : ℕ) : IsOpen (positiveOrthant k) := by
  change IsOpen {s : Space k | ∀ i, 0 < s i}
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (EuclideanSpace.proj i).continuous

lemma expSpace_mem_positive {k : ℕ} (s : Space k) : expSpace s ∈ positiveOrthant k :=
  fun index => Real.exp_pos (s index)

lemma expSpace_logSpace {k : ℕ} {s : Space k} (hs : s ∈ positiveOrthant k) :
    expSpace (logSpace s) = s := by
  ext i
  exact Real.exp_log (hs i)

lemma contDiff_expSpace {k : ℕ} : ContDiff ℝ ∞ (expSpace : Space k → Space k) := by
  apply (EuclideanSpace.equiv (Fin k) ℝ).symm.contDiff.comp
  exact contDiff_pi.mpr fun i => (EuclideanSpace.proj i).contDiff.exp

lemma contDiffAt_logSpace {k : ℕ} {s : Space k} (hs : s ∈ positiveOrthant k) :
    ContDiffAt ℝ ∞ logSpace s := by
  apply (EuclideanSpace.equiv (Fin k) ℝ).symm.contDiff.contDiffAt.comp
  exact contDiffAt_pi.mpr fun i => (EuclideanSpace.proj i).contDiff.contDiffAt.log (hs i).ne'

/- Extension by zero of a compact test in logarithmic coordinates; a negative
coordinate must not be silently sent through Real.log. -/

lemma logPullback_of_positive {k : ℕ} (φ : Space k → ℝ) {s : Space k}
    (hs : s ∈ positiveOrthant k) : logPullback φ s = φ (logSpace s) := ite_eq_left hs

lemma logPullback_eventuallyEq {k : ℕ} (φ : Space k → ℝ) {s : Space k}
    (hs : s ∈ positiveOrthant k) : logPullback φ =ᶠ[nhds s] φ ∘ logSpace := by
  filter_upwards [(isOpen_positiveOrthant k).mem_nhds hs] with x hx
  exact logPullback_of_positive φ hx

lemma support_logPullback_subset {k : ℕ} (φ : Space k → ℝ) :
    Function.support (logPullback φ) ⊆ expSpace '' tsupport φ := by
  intro s hs
  have hp : s ∈ positiveOrthant k := by
    by_contra hn
    exact hs (ite_eq_right hn)
  refine ⟨logSpace s,subset_closure ?_,expSpace_logSpace hp⟩
  change φ (logSpace s) ≠ 0
  change logPullback φ s ≠ 0 at hs
  simpa only [logPullback_of_positive φ hp] using hs

lemma tsupport_logPullback_subset {k : ℕ} {φ : Space k → ℝ} (hc : HasCompactSupport φ) :
    tsupport (logPullback φ) ⊆ expSpace '' tsupport φ :=
  closure_minimal (support_logPullback_subset φ) (hc.isCompact.image contDiff_expSpace.continuous).isClosed

lemma hasCompactSupport_logPullback {k : ℕ} {φ : Space k → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (logPullback φ) :=
  (hc.isCompact.image contDiff_expSpace.continuous).of_isClosed_subset isClosed_closure
    (tsupport_logPullback_subset hc)

lemma contDiff_logPullback {k : ℕ} {φ : Space k → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) : ContDiff ℝ ∞ (logPullback φ) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s ∈ positiveOrthant k
  · exact (hφ.contDiffAt.comp s (contDiffAt_logSpace hs)).congr_of_eventuallyEq
      (logPullback_eventuallyEq φ hs)
  · have hn : s ∉ expSpace '' tsupport φ := by
      rintro ⟨x,_,rfl⟩
      exact hs (expSpace_mem_positive x)
    have he : logPullback φ =ᶠ[nhds s] (fun _ => 0) := by
      filter_upwards [(hc.isCompact.image contDiff_expSpace.continuous).isClosed.isOpen_compl.mem_nhds hn] with x hx
      by_contra hzero
      exact hx (support_logPullback_subset φ hzero)
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma tsupport_logPullback_subset_logDomain {k : ℕ} {φ : Space k → ℝ} {D : Set (Space k)}
    (hD : D ⊆ positiveOrthant k) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ logSpace '' D) :
    tsupport (logPullback φ) ⊆ D := by
  intro s hsp
  obtain ⟨x,hx,rfl⟩ := tsupport_logPullback_subset hc hsp
  obtain ⟨y,hy,rfl⟩ := hs hx
  simpa only [expSpace_logSpace (hD hy)] using hy

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_EuclideanChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section EuclideanChain

lemma continuousLinearMap_euclidean_sum {k : ℕ} (L : Space k →L[ℝ] ℝ) (y : Space k) :
    L y = ∑ i : Fin k, L ((EuclideanSpace.basisFun (Fin k) ℝ) i)*y i := by
  have hr : (∑ i : Fin k, y i • (EuclideanSpace.basisFun (Fin k) ℝ) i) = y := by
    simpa only [EuclideanSpace.basisFun_repr] using (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr y
  calc
    _ = L (∑ i : Fin k, y i • (EuclideanSpace.basisFun (Fin k) ℝ) i) := congrArg L hr.symm
    _ = _ := by simp [map_sum,map_smul,mul_comm]

lemma euclidean_chain_fderiv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {k : ℕ} {f : X → Space k} {φ : Space k → ℝ} {x : X}
    (hf : DifferentiableAt ℝ f x) (hφ : DifferentiableAt ℝ φ (f x)) (v : X) :
    fderiv ℝ (φ ∘ f) x v = ∑ i : Fin k,
      fderiv ℝ φ (f x) ((EuclideanSpace.basisFun (Fin k) ℝ) i)*
        fderiv ℝ (fun y => f y i) x v := by
  rw [fderiv_comp x hφ hf]
  change fderiv ℝ φ (f x) (fderiv ℝ f x v) = _
  rw [continuousLinearMap_euclidean_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hi := ((EuclideanSpace.proj i).hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  exact (congrArg (fun L : X →L[ℝ] ℝ => L v) hi).symm

end EuclideanChain

/- Euclidean norm squared of the gradient, written in the fixed orthonormal coordinate basis. -/

lemma euclideanGradientSquare_eq_norm {k : ℕ} (φ : Space k → ℝ) (s : Space k) :
    euclideanGradientSquare φ s = ‖fderiv ℝ φ s‖^2 := by
  have hh := (EuclideanSpace.basisFun (Fin k) ℝ).sum_sq_inner_left
    ((InnerProductSpace.toDual ℝ (Space k)).symm (fderiv ℝ φ s))
  simpa only [euclideanGradientSquare,InnerProductSpace.toDual_symm_apply,LinearIsometryEquiv.norm_map] using hh

lemma euclideanGradientSquare_zero {k : ℕ} {φ : Space k → ℝ} {s : Space k}
    (hs : s ∉ tsupport φ) : euclideanGradientSquare φ s = 0 := by
  simp [euclideanGradientSquare,fderiv_of_notMem_tsupport ℝ hs]

lemma tsupport_euclideanGradientSquare {k : ℕ} (φ : Space k → ℝ) :
    tsupport (euclideanGradientSquare φ) ⊆ tsupport φ := by
  apply closure_minimal _ isClosed_closure
  intro s hs
  by_contra hn
  exact hs (euclideanGradientSquare_zero hn)

lemma contDiff_euclideanGradientSquare {k : ℕ} {φ : Space k → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (euclideanGradientSquare φ) := by
  exact ContDiff.sum fun i _ => (((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).pow 2)

lemma compactSupport_euclideanGradientSquare {k : ℕ} {φ : Space k → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (euclideanGradientSquare φ) :=
  hc.isCompact.of_isClosed_subset isClosed_closure (tsupport_euclideanGradientSquare φ)

lemma logPullback_gradient_support {k : ℕ} {φ : Space k → ℝ} (hc : HasCompactSupport φ) :
    tsupport (logPullback (euclideanGradientSquare φ)) ⊆ expSpace '' tsupport φ := by
  apply (tsupport_logPullback_subset (compactSupport_euclideanGradientSquare hc)).trans
  exact Set.image_mono (tsupport_euclideanGradientSquare φ)

lemma logPullback_fderiv_chain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {φ : Space k → ℝ} (hφ : ContDiff ℝ ∞ φ) {q : Space k × E}
    (hq : q.1 ∈ positiveOrthant k) (v : Space k × E) :
    fderiv ℝ (fun z : Space k × E => logPullback φ z.1) q v =
      ∑ i : Fin k, fderiv ℝ φ (logSpace q.1) ((EuclideanSpace.basisFun (Fin k) ℝ) i)*
        fderiv ℝ (fun z : Space k × E => Real.log (z.1 i)) q v := by
  have he : (fun z : Space k × E => logPullback φ z.1) =ᶠ[nhds q]
      (φ ∘ fun z : Space k × E => logSpace z.1) :=
    (logPullback_eventuallyEq φ hq).comp_tendsto continuousAt_fst
  rw [he.fderiv_eq]
  exact euclidean_chain_fderiv
    (((contDiffAt_logSpace hq).comp q contDiffAt_fst).differentiableAt (by simp))
    (hφ.differentiable (by simp) _) v

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeSupportedIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {S E : Type*} [NormedAddCommGroup S]
  [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]

lemma integrable_tube_compactBase {K D : Set S} (hK : IsCompact K) (hKD : K ⊆ D)
    {f : S × E → ℝ} (hf : ContinuousOn f (tubeOpenSet D))
    (hz : ∀ s ∉ K, ∀ e : E, f (s,e) = 0) :
    Integrable (fun q : S × sphere (0:E) 1 => f (tubeLift q)) (μ.prod volume.toSphere) := by
  have hs : Function.support (fun q : S × sphere (0:E) 1 => f (tubeLift q)) ⊆
      K ×ˢ (Set.univ : Set (sphere (0:E) 1)) := by
    intro q hq
    refine ⟨?_,Set.mem_univ _⟩
    by_contra hn
    exact hq (hz q.1 hn q.2)
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  exact ContinuousOn.integrableOn_compact (hK.prod isCompact_univ)
    (hf.comp continuous_tubeLift.continuousOn (fun q hq => tubeLift_mem q (hKD hq.1)))

lemma tubeIntegral_supported_mono {K D : Set S} (hK : IsCompact K) (hKD : K ⊆ D)
    {M f g : S × E → ℝ} (hM : ContinuousOn M (tubeOpenSet D))
    (hf : ContinuousOn f (tubeOpenSet D)) (hg : ContinuousOn g (tubeOpenSet D))
    (hfz : ∀ s ∉ K, ∀ e : E, f (s,e) = 0) (hgz : ∀ s ∉ K, ∀ e : E, g (s,e) = 0)
    (hpos : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ M (s,e))
    (hfg : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → f (s,e) ≤ g (s,e)) :
    tubeIntegral μ M (fun _ => 1) f ≤ tubeIntegral μ M (fun _ => 1) g := by
  simp only [tubeIntegral,mul_one]
  apply integral_mono_ae
    (integrable_tube_compactBase hK hKD (hM.mul hf) (fun s hs e => by simp [hfz s hs e]))
    (integrable_tube_compactBase hK hKD (hM.mul hg) (fun s hs e => by simp [hgz s hs e]))
  apply Filter.Eventually.of_forall
  intro q
  by_cases hs : q.1 ∈ K
  · exact mul_le_mul_of_nonneg_left (hfg q.1 (hKD hs) q.2 (mem_sphere_zero_iff_norm.1 q.2.property))
      (hpos q.1 (hKD hs) q.2 (mem_sphere_zero_iff_norm.1 q.2.property))
  · simp [tubeLift,hfz q.1 hs q.2,hgz q.1 hs q.2]

omit [NormedAddCommGroup S] [BorelSpace S] [μ.IsAddHaarMeasure] in
lemma tubeIntegral_supported_nonneg {K D : Set S} (hKD : K ⊆ D)
    {M f : S × E → ℝ} (hfz : ∀ s ∉ K, ∀ e : E, f (s,e) = 0)
    (hpos : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ M (s,e) ∧ 0 ≤ f (s,e)) :
    0 ≤ tubeIntegral μ M (fun _ => 1) f := by
  apply integral_nonneg
  intro q
  by_cases hs : q.1 ∈ K
  · have hp := hpos q.1 (hKD hs) q.2 (mem_sphere_zero_iff_norm.1 q.2.property)
    simpa [tubeLift] using mul_nonneg hp.1 hp.2
  · simp [tubeLift,hfz q.1 hs q.2]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualLogInequality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/- Proposition log-inequality for the actual affine-epigraph tube. The positive-
orthant pullback is extended by zero, and both sides are literal product integrals
with the source logarithmic density. No tube-metric completeness is required. -/
theorem affineMaximal_logarithmic_inequality {n k : ℕ} (hn : 3 ≤ n) (hn9 : n ≤ 9)
    (hk : 2 ≤ k) (hkn : k ≤ n) {μ : Measure (Space k)} [μ.IsAddHaarMeasure]
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D) (hDpos : D ⊆ positiveOrthant k)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {φ : Space k → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ logSpace '' D) :
    let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    let M := tubeMeasureDensity n H b bE
    let T := fun q => 1+∑ i : Fin k,
      tubeBasePair H b (fun z => Real.log (z.1 i)) (fun z => Real.log (z.1 i)) q
    tubeIntegral μ M (fun s => logPullback φ s^2) T ≤
      (4194304+(n : ℝ)*1358954512)*tubeIntegral μ M (fun _ => 1)
        (fun q => logPullback (euclideanGradientSquare φ) q.1*T q) := by
  dsimp only
  let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let M := tubeMeasureDensity n H b bE
  let A := fun (i : Fin k) (q : Space k × E) => Real.log (q.1 i)
  let T := fun q => 1+∑ i : Fin k, tubeBasePair H b (A i) (A i) q
  let σ := logPullback φ
  let V := fun q : Space k × E => σ q.1
  let W := logPullback (euclideanGradientSquare φ)
  let Q := tubeBasePair H b V V
  let K := expSpace '' tsupport φ
  have hKc : IsCompact K := hc.isCompact.image contDiff_expSpace.continuous
  have hKD : K ⊆ D := by
    rintro s ⟨x,hx,rfl⟩
    obtain ⟨y,hy,rfl⟩ := hφD hx
    simpa only [expSpace_logSpace (hDpos hy)] using hy
  have hσ : ContDiff ℝ ∞ σ := contDiff_logPullback hφ hc
  have hcσ : HasCompactSupport σ := hasCompactSupport_logPullback hc
  have hσD : tsupport σ ⊆ D := tsupport_logPullback_subset_logDomain hDpos hc hφD
  have hW : Continuous W := (contDiff_logPullback (contDiff_euclideanGradientSquare hφ)
    (compactSupport_euclideanGradientSquare hc)).continuous
  have hH (q : Space k × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ H q :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hq.1 hq.2).1
  have hpos (q : Space k × E) (hq : q ∈ tubeOpenSet D) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 b bE
  have hA (i : Fin k) (q : Space k × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ (A i) q :=
    by
      have hpj : ContDiff ℝ ∞ (fun s : Space k => s i) := (EuclideanSpace.proj i : Space k →L[ℝ] ℝ).contDiff
      have hh : ContDiffAt ℝ ∞ (fun z : Space k × E => z.1 i) q :=
        (hpj.comp contDiff_fst).contDiffAt
      exact hh.log (hDpos hq.1 i).ne'
  have hV (q : Space k × E) (_ : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ V q :=
    hσ.contDiffAt.comp q contDiffAt_fst
  have hM : ContinuousOn M (tubeOpenSet D) := fun q hq =>
    (continuousAt_tubeMeasureDensity (hH q hq) b bE (hpos q hq).2.2).continuousWithinAt
  have hpair (f g : Space k × E → ℝ) (hf : ∀ q ∈ tubeOpenSet D, ContDiffAt ℝ ∞ f q)
      (hg : ∀ q ∈ tubeOpenSet D, ContDiffAt ℝ ∞ g q) : ContinuousOn (tubeBasePair H b f g) (tubeOpenSet D) :=
    fun q hq => (contDiffAt_tubeBasePair (hH q hq) (hf q hq) (hg q hq) b
       (hpos q hq).1.det_pos.ne').continuousAt.continuousWithinAt
  have hT : ContinuousOn T (tubeOpenSet D) := continuousOn_const.add
    (continuousOn_finsetSum _ fun i _ => hpair (A i) (A i) (hA i) (hA i))
  have hQ : ContinuousOn Q (tubeOpenSet D) := hpair V V hV hV
  have hQzero (s : Space k) (hs : s ∉ K) (e : E) : Q (s,e) = 0 := by
    have hsσ : s ∉ tsupport σ := fun h => hs (tsupport_logPullback_subset hc h)
    have hd : fderiv ℝ V (s,e) = 0 := by
      dsimp only [V]
      rw [show (fun q : Space k × E => σ q.1) = σ ∘ Prod.fst by rfl,
        fderiv_comp (s,e) (hσ.differentiable (by simp) s) differentiableAt_fst,
        fderiv_of_notMem_tsupport ℝ hsσ]
      simp
    simp [Q,tubeBasePair,flatInversePair,dirDeriv,hd]
  have hWzero (s : Space k) (hs : s ∉ K) : W s = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hs (logPullback_gradient_support hc h))
  have hMn (s : Space k) (hs : s ∈ D) (e : E) (he : ‖e‖ = 1) : 0 ≤ M (s,e) := by
    have hen : e ≠ 0 := by intro hz; simp [hz] at he
    have hz := hpos (s,e) ⟨hs,hen⟩
    exact (tubeMeasureCoefficient_pos hz.2.2 hz.1.det_pos hz.2.1).le
  have hQI : 0 ≤ tubeIntegral μ M (fun _ => 1) Q := by
    apply tubeIntegral_supported_nonneg hKD hQzero
    intro s hs e he
    have hen : e ≠ 0 := by intro hz; simp [hz] at he
    have hz := hpos (s,e) ⟨hs,hen⟩
    exact ⟨hMn s hs e he,tubeBasePair_nonneg b hz.2.2.le hz.1 V⟩
  have hcomp : tubeIntegral μ M (fun _ => 1) Q ≤
      tubeIntegral μ M (fun _ => 1) (fun q => W q.1*T q) := by
    apply tubeIntegral_supported_mono hKc hKD hM hQ ((hW.comp continuous_fst).continuousOn.mul hT)
      hQzero (fun s hs _ => by simp [hWzero s hs]) hMn
    intro s hs e he
    have hen : e ≠ 0 := by intro hz; simp [hz] at he
    have hz := hpos (s,e) ⟨hs,hen⟩
    let c := fun i : Fin k => fderiv ℝ φ (logSpace s) ((EuclideanSpace.basisFun (Fin k) ℝ) i)
    have hcb := tubeBasePair_linearCombination b hz.2.2.le hz.1 V A c
      (fun i => logPullback_fderiv_chain hφ (hDpos hs) (b i,(0:E)))
    change Q (s,e) ≤ (∑ i, c i^2)*(∑ i, tubeBasePair H b (A i) (A i) (s,e)) at hcb
    have hWeq : W s = ∑ i, c i^2 := logPullback_of_positive _ (hDpos hs)
    change Q (s,e) ≤ W s*(1+∑ i, tubeBasePair H b (A i) (A i) (s,e))
    rw [hWeq]
    nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (c i))]
  have he := affineMaximal_tube_log_measure_energy (μ := μ) hn hn9 hΩ hcv hu hp hm a L hD hK hzero
    b bE (by simpa using hk) (fun i => EuclideanSpace.proj i) (fun i s hs => hDpos hs i) hσ hcσ hσD
  change tubeIntegral μ M (fun s => σ s^2) T ≤
    (4194304+(Fintype.card (Fin k) : ℝ)*1358954512)*tubeIntegral μ M (fun _ => 1) Q at he
  have hco : 4194304+(Fintype.card (Fin k) : ℝ)*1358954512 ≤ 4194304+(n : ℝ)*1358954512 := by
    simp only [Fintype.card_fin]
    have hknr : (k : ℝ) ≤ n := by exact_mod_cast hkn
    linarith
  have hcn : 0 ≤ 4194304+(n : ℝ)*1358954512 := by positivity
  exact he.trans ((mul_le_mul_of_nonneg_right hco hQI).trans
    (mul_le_mul_of_nonneg_left hcomp hcn))

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LogTubeMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {k : ℕ} {μ : Measure (Space k)}

lemma measurable_logSpace : Measurable (logSpace : Space k → Space k) := by
  apply (EuclideanSpace.equiv (Fin k) ℝ).symm.continuous.measurable.comp
  exact Measurable.of_eval fun index =>
    Real.measurable_log.comp (EuclideanSpace.proj index).continuous.measurable

/- The actual logarithmic pushforward of a tube density, restricted to its
positive base domain. Only the nonnegative part outside that domain is discarded. -/

lemma logPullback_zero_outside_domain {D : Set (Space k)} {φ : Space k → ℝ}
    (hDpos : D ⊆ positiveOrthant k) (hsupp : tsupport φ ⊆ logSpace '' D)
    {s : Space k} (hs : s ∉ D) : logPullback φ s = 0 := by
  by_cases hp : s ∈ positiveOrthant k
  · rw [logPullback_of_positive φ hp]
    apply image_eq_zero_of_notMem_tsupport
    intro ht
    obtain ⟨y,hy,he⟩ := hsupp ht
    apply hs
    have heq : y = s := by
      have hh := congrArg expSpace he
      simpa only [expSpace_logSpace (hDpos hy),expSpace_logSpace hp] using hh
    simpa only [heq] using hy
  · exact ite_eq_right hp

lemma integral_logTubeMeasure {D : Set (Space k)} (hD : MeasurableSet D)
    (hDpos : D ⊆ positiveOrthant k) {F : Space k × E → ℝ}
    (hF : ContinuousOn F (tubeOpenSet D))
    (hFn : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ F (s,e))
    {φ : Space k → ℝ} (hφ : StronglyMeasurable φ)
    (hsupp : tsupport φ ⊆ logSpace '' D) :
    (∫ x, φ x ∂logTubeMeasure μ D F) =
      tubeIntegral μ F (logPullback φ) (fun _ => 1) := by
  have hP : MeasurableSet (D ×ˢ (Set.univ : Set (sphere (0:E) 1))) := hD.prod MeasurableSet.univ
  have hm : AEMeasurable (fun q : Space k × sphere (0:E) 1 => ENNReal.ofReal (F (tubeLift q)))
      ((μ.prod volume.toSphere).restrict (D ×ˢ Set.univ)) :=
    (hF.comp continuous_tubeLift.continuousOn (fun q hq => tubeLift_mem q hq.1)).aemeasurable hP |>.ennreal_ofReal
  have hmap : Measurable (fun q : Space k × sphere (0:E) 1 => logSpace q.1) :=
    measurable_logSpace.comp measurable_fst
  rw [logTubeMeasure,integral_map_of_stronglyMeasurable hmap hφ,
    integral_withDensity_eq_integral_toReal_smul₀ hm (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [← integral_indicator hP]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  by_cases hs : q.1 ∈ D
  · rw [Set.indicator_of_mem (show q ∈ D ×ˢ Set.univ from ⟨hs,Set.mem_univ _⟩)]
    simp only [tubeLift]
    rw [ENNReal.toReal_ofReal (hFn q.1 hs q.2 (mem_sphere_zero_iff_norm.1 q.2.property))]
    simp [logPullback_of_positive φ (hDpos hs)]
  · rw [Set.indicator_of_notMem (show q ∉ D ×ˢ Set.univ from fun h => hs h.1)]
    simp [logPullback_zero_outside_domain hDpos hsupp hs]

lemma integral_logTubeMeasure_mul {D : Set (Space k)} (hD : MeasurableSet D)
    (hDpos : D ⊆ positiveOrthant k) {M T : Space k × E → ℝ}
    (hM : ContinuousOn M (tubeOpenSet D)) (hT : ContinuousOn T (tubeOpenSet D))
    (hMn : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ M (s,e))
    (hTn : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ T (s,e))
    {φ : Space k → ℝ} (hφ : StronglyMeasurable φ)
    (hsupp : tsupport φ ⊆ logSpace '' D) :
    (∫ x, φ x ∂logTubeMeasure μ D (fun q => M q*T q)) =
      tubeIntegral μ M (logPullback φ) T := by
  rw [integral_logTubeMeasure (μ := μ) (F := fun q => M q*T q) hD hDpos (hM.mul hT)
    (fun s hs e he => mul_nonneg (hMn s hs e he) (hTn s hs e he)) hφ hsupp]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ => by ring

lemma logPullback_sq (φ : Space k → ℝ) : logPullback (fun x => φ x^2) = fun s => logPullback φ s^2 := by
  funext s
  unfold logPullback
  split_ifs <;> simp

lemma logTubeMeasure_compact_lt_top [μ.IsAddHaarMeasure]
    {D : Set (Space k)} (hDpos : D ⊆ positiveOrthant k) {F : Space k × E → ℝ}
    (hF : ContinuousOn F (tubeOpenSet D))
    {K : Set (Space k)} (hK : IsCompact K) (hKD : K ⊆ logSpace '' D) :
    logTubeMeasure μ D F K < ⊤ := by
  have hmap : Measurable (fun q : Space k × sphere (0:E) 1 => logSpace q.1) :=
    measurable_logSpace.comp measurable_fst
  have hEK : IsCompact (expSpace '' K) := hK.image contDiff_expSpace.continuous
  have hED : expSpace '' K ⊆ D := by
    rintro s ⟨t,ht,rfl⟩
    obtain ⟨y,hy,rfl⟩ := hKD ht
    simpa only [expSpace_logSpace (hDpos hy)] using hy
  have hset : (fun q : Space k × sphere (0:E) 1 => logSpace q.1) ⁻¹' K ∩ (D ×ˢ Set.univ) =
      (expSpace '' K) ×ˢ Set.univ := by
    ext q
    constructor
    · rintro ⟨hq,hDq,-⟩
      exact ⟨⟨logSpace q.1,hq,expSpace_logSpace (hDpos hDq)⟩,Set.mem_univ _⟩
    · rintro ⟨⟨s,hs,he⟩,-⟩
      have ht : q.1 ∈ expSpace '' K := ⟨s,hs,he⟩
      refine ⟨?_,hED ht,Set.mem_univ _⟩
      change logSpace q.1 ∈ K
      rw [← he,logSpace_expSpace]
      exact hs
  rw [logTubeMeasure,Measure.map_apply hmap hK.measurableSet,
    withDensity_apply _ (hK.measurableSet.preimage hmap),
    Measure.restrict_restrict (hK.measurableSet.preimage hmap),hset]
  have hi : IntegrableOn (fun q : Space k × sphere (0:E) 1 => F (tubeLift q))
      ((expSpace '' K) ×ˢ Set.univ) (μ.prod volume.toSphere) :=
    ContinuousOn.integrableOn_compact (hEK.prod isCompact_univ)
      (hF.comp continuous_tubeLift.continuousOn (fun q hq => tubeLift_mem q (hED hq.1)))
  exact (lintegral_ofReal_le_lintegral_enorm _).trans_lt hi.2

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualLogMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [MeasurableSpace E] [BorelSpace E] in
lemma affineEpigraph_logWeight_regular {n k : ℕ}
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D) (hDpos : D ⊆ positiveOrthant k)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let M := tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE
    let T := tubeLogMassWeight H
    ContinuousOn M (tubeOpenSet D) ∧ ContinuousOn T (tubeOpenSet D) ∧
      ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ M (s,e) ∧ 0 ≤ T (s,e) := by
  dsimp only
  let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let A := fun (i : Fin k) (q : Space k × E) => Real.log (q.1 i)
  have hH (q : Space k × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ H q :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hq.1 hq.2).1
  have hpos (q : Space k × E) (hq : q ∈ tubeOpenSet D) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 b bE
  have hA (i : Fin k) (q : Space k × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ (A i) q := by
    have hpj : ContDiff ℝ ∞ (fun s : Space k => s i) := (EuclideanSpace.proj i : Space k →L[ℝ] ℝ).contDiff
    have hh : ContDiffAt ℝ ∞ (fun z : Space k × E => z.1 i) q := (hpj.comp contDiff_fst).contDiffAt
    exact hh.log (hDpos hq.1 i).ne'
  refine ⟨?_,?_,?_⟩
  · intro q hq
    exact (continuousAt_tubeMeasureDensity (hH q hq) b bE (hpos q hq).2.2).continuousWithinAt
  · apply continuousOn_const.add
    apply continuousOn_finsetSum
    intro i _ q hq
    exact (contDiffAt_tubeBasePair (hH q hq) (hA i q hq) (hA i q hq) b
      (hpos q hq).1.det_pos.ne').continuousAt.continuousWithinAt
  · intro s hs e he
    have hen : e ≠ 0 := by intro hz; simp [hz] at he
    have hz := hpos (s,e) ⟨hs,hen⟩
    refine ⟨(tubeMeasureCoefficient_pos hz.2.2 hz.1.det_pos hz.2.1).le,?_⟩
    apply add_nonneg zero_le_one
    exact Finset.sum_nonneg fun i _ => tubeBasePair_nonneg b hz.2.2.le hz.1 (A i)

/- The paper's sigma measure, pushed to logarithmic coordinates. This definition
uses the actual affine epigraph support function, not an abstract model metric. -/
theorem affineMaximal_logMeasure_poincare {n k : ℕ} (hn : 3 ≤ n) (hn9 : n ≤ 9)
    (hk : 2 ≤ k) (hkn : k ≤ n) {μ : Measure (Space k)} [μ.IsAddHaarMeasure]
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D) (hDpos : D ⊆ positiveOrthant k)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {φ : Space k → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ logSpace '' D) :
    (∫ x, φ x^2 ∂affineEpigraphLogMeasure μ D Ω u a L bE) ≤
      (4194304+(n : ℝ)*1358954512) *
        ∫ x, ‖fderiv ℝ φ x‖^2 ∂affineEpigraphLogMeasure μ D Ω u a L bE := by
  let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let M := tubeMeasureDensity n H b bE
  let T := tubeLogMassWeight H
  obtain ⟨hM,hT,hpos⟩ := affineEpigraph_logWeight_regular hΩ hcv hu hp a L hD hDpos hK hzero bE
  have hi (ψ : Space k → ℝ) (hψ : StronglyMeasurable ψ) (hs : tsupport ψ ⊆ logSpace '' D) :
      (∫ x, ψ x ∂affineEpigraphLogMeasure μ D Ω u a L bE) = tubeIntegral μ M (logPullback ψ) T :=
    integral_logTubeMeasure_mul hD.measurableSet hDpos hM hT
      (fun s hs e he => (hpos s hs e he).1) (fun s hs e he => (hpos s hs e he).2) hψ hs
  have hgS : tsupport (euclideanGradientSquare φ) ⊆ logSpace '' D :=
    (tsupport_euclideanGradientSquare φ).trans hφD
  have hsqS : tsupport (fun x => φ x^2) ⊆ logSpace '' D := by
    apply (tsupport_comp_subset (g := fun x : ℝ => x^2) (by simp) φ).trans hφD
  rw [hi (fun x => φ x^2) (hφ.continuous.pow 2).stronglyMeasurable hsqS,logPullback_sq]
  simp_rw [← euclideanGradientSquare_eq_norm]
  rw [hi _ (contDiff_euclideanGradientSquare hφ).continuous.stronglyMeasurable hgS]
  have hh := affineMaximal_logarithmic_inequality hn hn9 hk hkn hΩ hcv hu hp hm a L
    hD hDpos hK hzero bE hφ hc hφD (μ := μ)
  apply hh.trans_eq
  apply congrArg ((4194304+(n : ℝ)*1358954512) * ·)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ => by
    dsimp only [M,T,H,b,tubeLogMassWeight,tubeLift]
    ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualLogMeasureFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Filter Metric
open scoped Topology

/- The quantifier order in bounds.tex: every finite box has its own eventual
index. No common threshold for infinitely many boxes is needed. -/
theorem no_eventual_polynomial_exponential_growth
    (M : ℕ → ℕ → ℝ) (k l₀ : ℕ) {c q C : ℝ}
    (hc : 0 < c) (hq : 1 < q)
    (hpos : ∀ᶠ j in atTop, c ≤ M j l₀)
    (hstep : ∀ l, l₀ ≤ l → ∀ᶠ j in atTop, q * M j l ≤ M j (l+1))
    (hupper : ∀ L, l₀ ≤ L → ∀ᶠ j in atTop, M j L ≤ C * (L+1:ℝ)^k) : False := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hlower : ∀ r : ℕ, ∀ᶠ j in atTop, c*q^r ≤ M j (l₀+r) := by
    intro r
    induction r with
    | zero => simpa using hpos
    | succ r ihr =>
      filter_upwards [ihr,hstep (l₀+r) (Nat.le_add_right _ _)] with j hj hs
      have hh := (mul_le_mul_of_nonneg_left hj hq0.le).trans hs
      simpa only [Nat.add_succ, pow_succ, mul_left_comm q c, mul_comm q (q^r)] using hh
  have ht : Tendsto (fun r : ℕ => C * ((l₀+r+1:ℕ):ℝ)^k / q^r) atTop (𝓝 0) := by
    have hh := ((tendsto_pow_const_div_const_pow_of_one_lt k hq).comp
      (tendsto_add_atTop_nat (l₀+1))).const_mul (C*q^(l₀+1))
    simpa only [mul_zero] using hh.congr (fun r => by
      dsimp only [Function.comp_def]
      have hn : r+(l₀+1) = l₀+r+1 := by omega
      rw [← hn, pow_add]
      field_simp [hq0.ne']
      ring)
  have hsmall : ∀ᶠ r in atTop, C * ((l₀+r+1:ℕ):ℝ)^k / q^r < c := ht.eventually (gt_mem_nhds hc)
  obtain ⟨r,hr⟩ := hsmall.exists
  have he := (hlower r).and (hupper (l₀+r) (Nat.le_add_right _ _))
  obtain ⟨j,hj,hju⟩ := he.exists
  have hle : c ≤ C * ((l₀+r+1:ℕ):ℝ)^k / q^r := by
    apply (le_div_iff₀ (pow_pos hq0 _)).mpr
    exact hj.trans (by simpa only [Nat.cast_add,Nat.cast_one] using hju)
  exact (not_lt_of_ge hle) hr

/- The source shell inequality has precisely the exponential recurrence
required above. Integrals may vary with the approximating index. -/
theorem no_eventual_polynomial_shell_growth
    (M : ℕ → ℕ → ℝ) (k l₀ : ℕ) {c A C : ℝ}
    (hc : 0 < c) (hA : 0 < A)
    (hpos : ∀ᶠ j in atTop, c ≤ M j l₀)
    (hshell : ∀ l, l₀ ≤ l → ∀ᶠ j in atTop,
      M j l ≤ A * (M j (l+1)-M j l))
    (hupper : ∀ L, l₀ ≤ L → ∀ᶠ j in atTop, M j L ≤ C * (L+1:ℝ)^k) : False := by
  apply no_eventual_polynomial_exponential_growth M k l₀ hc
    (show 1 < 1+A⁻¹ by linarith [inv_pos.mpr hA]) hpos _ hupper
  intro l hl
  filter_upwards [hshell l hl] with j hj
  apply (le_of_mul_le_mul_left (a := A) ?_ hA)
  field_simp
  nlinarith

/- A product of two unit-bounded Lipschitz functions has the sum of their
Lipschitz constants. Here the multiplication is the ring multiplication on ℝ. -/
theorem lipschitzWith_mul_unit {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {K L : NNReal} (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hfb : ∀ x, ‖f x‖ ≤ 1) (hgb : ∀ x, ‖g x‖ ≤ 1) :
    LipschitzWith (K+L) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hi : f x*g x-f y*g y = f x*(g x-g y)+(f x-f y)*g y := by ring
  rw [dist_eq_norm,hi]
  calc
    ‖f x*(g x-g y)+(f x-f y)*g y‖ ≤ ‖f x‖*‖g x-g y‖+‖f x-f y‖*‖g y‖ :=
      by simpa only [norm_mul] using (norm_add_le (f x*(g x-g y)) ((f x-f y)*g y))
    _ ≤ 1*((L:ℝ)*dist x y)+((K:ℝ)*dist x y)*1 := by
      gcongr
      · exact hfb x
      · simpa only [dist_eq_norm] using hg.dist_le_mul x y
      · simpa only [dist_eq_norm] using hf.dist_le_mul x y
      · exact hgb y
    _ = (↑(K+L):ℝ)*dist x y := by simp only [NNReal.coe_add]; ring

theorem lipschitzWith_prod_unit {X I : Type*} [PseudoMetricSpace X]
    (s : Finset I) (f : I → X → ℝ) (K : I → NNReal)
    (hl : ∀ i ∈ s, LipschitzWith (K i) (f i))
    (hb : ∀ i ∈ s, ∀ x, ‖f i x‖ ≤ 1) :
    LipschitzWith (∑ i ∈ s, K i) (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha,Finset.prod_insert ha]
    apply lipschitzWith_mul_unit (hl a (by simp))
      (ih (fun i hi => hl i (by simp [hi])) (fun i hi => hb i (by simp [hi])))
      (hb a (by simp))
    intro x
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i hi => hb i (by simp [hi]) x)

/- The fixed smooth transition has some finite global Lipschitz constant;
constancy off [0,1] makes the derivative bound compact. -/
theorem smoothTransition_exists_lipschitz : ∃ K : NNReal, LipschitzWith K Real.smoothTransition := by
  have hcd : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (-1:ℝ) 2)).exists_bound_of_continuousOn
    ((hcd.continuous_deriv (by simp)).continuousOn)
  refine ⟨⟨max B 0,le_max_right _ _⟩,lipschitzWith_of_nnnorm_deriv_le (hcd.differentiable (by simp)) ?_⟩
  intro x
  change ‖deriv Real.smoothTransition x‖ ≤ max B 0
  by_cases hx : x ∈ Icc (-1:ℝ) 2
  · exact (hB x hx).trans (le_max_left _ _)
  have hd : deriv Real.smoothTransition x = 0 := by
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
        filter_upwards [gt_mem_nhds (show x < 0 by linarith)] with y hy
        exact Real.smoothTransition.zero_of_nonpos hy.le
      exact ((hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq he).deriv
    · have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1:ℝ) := by
        filter_upwards [lt_mem_nhds (show 1 < x by linarith)] with y hy
        exact Real.smoothTransition.one_of_one_le hy.le
      exact ((hasDerivAt_const x (1:ℝ)).congr_of_eventuallyEq he).deriv
  simp only [hd,norm_zero]
  exact le_max_right _ _

/- Closed boxes in the literal logarithmic base coordinates. -/
/- A fixed-width smooth box cutoff; its derivatives have no dependence on L
apart from coordinate translations. -/

theorem logarithmicCutoff_mem_Icc (k : ℕ) (L : ℝ) (x : Space k) :
    logarithmicCutoff k L x ∈ Icc (0:ℝ) 1 := by
  have hb : ∀ t : ℝ, 0 ≤ 1-Real.smoothTransition t ∧ 1-Real.smoothTransition t ≤ 1 :=
    fun t => ⟨sub_nonneg.mpr (Real.smoothTransition.le_one t),by linarith [Real.smoothTransition.nonneg t]⟩
  exact ⟨Finset.prod_nonneg (fun i _ => mul_nonneg (hb _).1 (hb _).1),
    Finset.prod_le_one (fun i _ => mul_nonneg (hb _).1 (hb _).1)
      (fun i _ => (mul_le_of_le_one_left (hb _).1 (hb _).2).trans (hb _).2)⟩

theorem logarithmicCutoff_one {k : ℕ} {L : ℝ} {x : Space k}
    (hx : x ∈ logarithmicBox k L) : logarithmicCutoff k L x = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  have hh := abs_le.mp (hx i)
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : x i-L ≤ 0),
    Real.smoothTransition.zero_of_nonpos (by linarith : -x i-L ≤ 0)]
  norm_num

theorem logarithmicCutoff_zero {k : ℕ} {L : ℝ} {x : Space k}
    (hx : ∃ i, L+1 ≤ |x i|) : logarithmicCutoff k L x = 0 := by
  classical
  obtain ⟨i,hi⟩ := hx
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rcases le_abs.mp hi with hi | hi
  · rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x i-L)]
    simp
  · rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ -x i-L)]
    simp

theorem logarithmicCutoff_smooth (k : ℕ) (L : ℝ) : ContDiff ℝ ∞ (logarithmicCutoff k L) := by
  unfold logarithmicCutoff
  apply contDiff_prod
  intro i hi
  exact (contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((EuclideanSpace.proj i).contDiff.sub contDiff_const))).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((EuclideanSpace.proj i).contDiff.neg.sub contDiff_const)))

/- One constant controls every translated logarithmic cutoff. -/
theorem logarithmicCutoff_uniform_lipschitz (k : ℕ) :
    ∃ K : NNReal, 0 < K ∧ ∀ L : ℝ, LipschitzWith K (logarithmicCutoff k L) := by
  obtain ⟨K,hK⟩ := smoothTransition_exists_lipschitz
  refine ⟨(k:NNReal)*(K+K)+1,by positivity,?_⟩
  intro L
  have hproj : ∀ i : Fin k, LipschitzWith 1 (fun x : Space k => x i) := by
    intro i
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one,one_mul,dist_eq_norm,PiLp.sub_apply] using
      (PiLp.norm_apply_le (x-y) i)
  have hb : ∀ t : ℝ, ‖1-Real.smoothTransition t‖ ≤ 1 := by
    intro t
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (Real.smoothTransition.le_one t))]
    linarith [Real.smoothTransition.nonneg t]
  have hf : ∀ i : Fin k, LipschitzWith (K+K)
      (fun x : Space k => (1-Real.smoothTransition (x i-L))*(1-Real.smoothTransition (-x i-L))) := by
    intro i
    apply lipschitzWith_mul_unit
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      calc
        dist (1-Real.smoothTransition (x i-L)) (1-Real.smoothTransition (y i-L)) =
            dist (Real.smoothTransition (x i-L)) (Real.smoothTransition (y i-L)) := dist_sub_left _ _ _
        _ ≤ (K:ℝ)*dist (x i-L) (y i-L) := hK.dist_le_mul _ _
        _ ≤ (K:ℝ)*dist x y := by
          gcongr
          simpa only [dist_sub_right,NNReal.coe_one,one_mul] using (hproj i).dist_le_mul x y
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      calc
        dist (1-Real.smoothTransition (-x i-L)) (1-Real.smoothTransition (-y i-L)) =
            dist (Real.smoothTransition (-x i-L)) (Real.smoothTransition (-y i-L)) := dist_sub_left _ _ _
        _ ≤ (K:ℝ)*dist (-x i-L) (-y i-L) := hK.dist_le_mul _ _
        _ ≤ (K:ℝ)*dist x y := by
          gcongr
          simpa only [dist_sub_right,dist_neg_neg,NNReal.coe_one,one_mul] using (hproj i).dist_le_mul x y
    · exact fun x => hb _
    · exact fun x => hb _
  have hp := lipschitzWith_prod_unit Finset.univ _ (fun _ : Fin k => K+K)
    (fun i _ => hf i) (fun i _ x => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hb _)).trans (hb _))
  change LipschitzWith _ (logarithmicCutoff k L) at hp
  have he : (∑ i : Fin k, (K+K)) = (k:NNReal)*(K+K) := by simp [mul_add]
  rw [he] at hp
  exact hp.weaken (le_add_of_nonneg_right (by positivity))

theorem logarithmicBox_mono {k : ℕ} {a b : ℝ} (h : a ≤ b) :
    logarithmicBox k a ⊆ logarithmicBox k b := fun _ hx i => (hx i).trans h

theorem logarithmicBox_isClosed (k : ℕ) (L : ℝ) : IsClosed (logarithmicBox k L) := by
  convert isClosed_iInter (fun i : Fin k => isClosed_le ((EuclideanSpace.proj i).continuous.abs)
    (show Continuous (fun _ : Space k => L) from continuous_const)) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp [logarithmicBox]

theorem logarithmicBox_isCompact (k : ℕ) (L : ℝ) : IsCompact (logarithmicBox k L) := by
  have h : IsCompact (Set.pi univ (fun _ : Fin k => Icc (-L) L)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have he : logarithmicBox k L = (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)) ⁻¹'
      (Set.pi univ (fun _ : Fin k => Icc (-L) L)) := by
    ext x
    simp only [logarithmicBox,mem_ofPred_eq,mem_preimage,Set.mem_pi,mem_univ,true_implies,mem_Icc]
    exact forall_congr' (fun i => abs_le)
  rw [he]
  exact (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).isCompact_preimage.mpr h

theorem logarithmicCutoff_hasCompactSupport (k : ℕ) (L : ℝ) :
    HasCompactSupport (logarithmicCutoff k L) := by
  apply (logarithmicBox_isCompact k (L+1)).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (logarithmicBox_isClosed k (L+1))
  intro x hx i
  by_contra hi
  exact hx (logarithmicCutoff_zero ⟨i,(not_le.mp hi).le⟩)

/- The derivative vanishes on the inner closed box, including its faces. -/
theorem logarithmicCutoff_fderiv_eq_zero_of_mem {k : ℕ} {L : ℝ} {x : Space k}
    (hx : x ∈ logarithmicBox k L) : fderiv ℝ (logarithmicCutoff k L) x = 0 := by
  apply IsLocalMax.fderiv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  rw [logarithmicCutoff_one hx]
  exact (logarithmicCutoff_mem_Icc k L y).2

/- The same holds at and outside the outer faces; no zero-boundary-mass
assumption is needed in the ensuing shell estimate. -/
theorem logarithmicCutoff_fderiv_eq_zero_of_outside {k : ℕ} {L : ℝ} {x : Space k}
    (hx : ∃ i, L+1 ≤ |x i|) : fderiv ℝ (logarithmicCutoff k L) x = 0 := by
  apply IsLocalMin.fderiv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  rw [logarithmicCutoff_zero hx]
  exact (logarithmicCutoff_mem_Icc k L y).1

/- The logarithmic Poincaré inequality turns the genuine smooth cutoff into
mass growth in a fixed-width shell. Measures need only be finite on this box. -/
theorem logarithmic_shell_growth {k : ℕ} {L : ℝ} (μ : Measure (Space k))
    {K : NNReal} (hK : LipschitzWith K (logarithmicCutoff k L)) (hfin : μ (logarithmicBox k (L+1)) ≠ ⊤)
    {A : ℝ} (hA : 0 ≤ A)
    (hP : (∫ x, (logarithmicCutoff k L x)^2 ∂μ) ≤
      A * ∫ x, ‖fderiv ℝ (logarithmicCutoff k L) x‖^2 ∂μ) :
    μ.real (logarithmicBox k L) ≤ A*(K:ℝ)^2 *
      (μ.real (logarithmicBox k (L+1))-μ.real (logarithmicBox k L)) := by
  classical
  let B₀ := logarithmicBox k L
  let B₁ := logarithmicBox k (L+1)
  let S := B₁ \ B₀
  have hm₀ : MeasurableSet B₀ := (logarithmicBox_isClosed _ _).measurableSet
  have hm₁ : MeasurableSet B₁ := (logarithmicBox_isClosed _ _).measurableSet
  have hmS : MeasurableSet S := hm₁.diff hm₀
  have hsub : B₀ ⊆ B₁ := logarithmicBox_mono (by linarith)
  have hfin₀ : μ B₀ ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono hsub)
  have hfinS : μ S ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono sdiff_subset)
  have hi₀ : Integrable (B₀.indicator (fun _ => (1:ℝ))) μ :=
    (integrable_indicator_iff hm₀).mpr (integrableOn_const hfin₀)
  have hi₁ : Integrable (B₁.indicator (fun _ => (1:ℝ))) μ :=
    (integrable_indicator_iff hm₁).mpr (integrableOn_const hfin)
  have hiS : Integrable (S.indicator (fun _ => (K:ℝ)^2)) μ :=
    (integrable_indicator_iff hmS).mpr (integrableOn_const hfinS)
  have hsq : ∀ x, (logarithmicCutoff k L x)^2 ≤ B₁.indicator (fun _ => (1:ℝ)) x := by
    intro x
    by_cases hx : x ∈ B₁
    · rw [indicator_of_mem hx]
      have hh := logarithmicCutoff_mem_Icc k L x
      nlinarith [sq_nonneg (logarithmicCutoff k L x),mul_nonneg hh.1 (sub_nonneg.mpr hh.2)]
    · rw [indicator_of_notMem hx]
      have ho : ∃ i, L+1 ≤ |x i| := by
        change ¬∀ i, |x i| ≤ L+1 at hx
        push Not at hx
        obtain ⟨i,hi⟩ := hx
        exact ⟨i,hi.le⟩
      rw [logarithmicCutoff_zero ho]
      norm_num
  have hd : ∀ x, ‖fderiv ℝ (logarithmicCutoff k L) x‖^2 ≤
      S.indicator (fun _ => (K:ℝ)^2) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hK) 2
    · rw [indicator_of_notMem hx]
      have he : fderiv ℝ (logarithmicCutoff k L) x = 0 := by
        by_cases hx₀ : x ∈ B₀
        · exact logarithmicCutoff_fderiv_eq_zero_of_mem hx₀
        · have hx₁ : x ∉ B₁ := fun h => hx ⟨h,hx₀⟩
          change ¬∀ i, |x i| ≤ L+1 at hx₁
          push Not at hx₁
          obtain ⟨i,hi⟩ := hx₁
          exact logarithmicCutoff_fderiv_eq_zero_of_outside ⟨i,hi.le⟩
      simp [he]
  have hiv : Integrable (fun x => (logarithmicCutoff k L x)^2) μ :=
    hi₁.mono' ((logarithmicCutoff_smooth k L).continuous.pow 2).aestronglyMeasurable
      (ae_of_all _ (fun x => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hsq x))
  have hid : Integrable (fun x => ‖fderiv ℝ (logarithmicCutoff k L) x‖^2) μ :=
    hiS.mono' (((logarithmicCutoff_smooth k L).continuous_fderiv (by simp)).norm.pow 2).aestronglyMeasurable
      (ae_of_all _ (fun x => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hd x))
  have hlo : μ.real B₀ ≤ ∫ x, (logarithmicCutoff k L x)^2 ∂μ := by
    have hh := integral_mono hi₀ hiv (show B₀.indicator (fun _ => (1:ℝ)) ≤
        (fun x => (logarithmicCutoff k L x)^2) from by
      intro x
      by_cases hx : x ∈ B₀
      · simp only [indicator_of_mem hx,logarithmicCutoff_one hx,one_pow,le_refl]
      · simp only [indicator_of_notMem hx]
        exact sq_nonneg _)
    simpa only [integral_indicator_const _ hm₀,smul_eq_mul,mul_one] using hh
  have hhi : (∫ x, ‖fderiv ℝ (logarithmicCutoff k L) x‖^2 ∂μ) ≤
      (K:ℝ)^2 * (μ.real B₁-μ.real B₀) := by
    have hh := integral_mono hid hiS hd
    rw [integral_indicator_const _ hmS,smul_eq_mul,measureReal_sdiff hsub hm₀ hfin,mul_comm] at hh
    exact hh
  exact (hlo.trans hP).trans ((mul_le_mul_of_nonneg_left hhi hA).trans_eq (by ring))

/- The growth contradiction, for actual Borel measures and actual smooth
cutoffs, with only eventual availability on each finite logarithmic box. -/
theorem no_polynomial_logarithmic_poincare {k l₀ : ℕ} (μ : ℕ → Measure (Space k))
    {c A C : ℝ} (hc : 0 < c) (hA : 0 < A)
    (hpos : ∀ᶠ j in atTop, c ≤ (μ j).real (logarithmicBox k l₀))
    (hfin : ∀ L : ℕ, l₀ ≤ L → ∀ᶠ j in atTop, μ j (logarithmicBox k L) ≠ ⊤)
    (hupper : ∀ L : ℕ, l₀ ≤ L → ∀ᶠ j in atTop,
      (μ j).real (logarithmicBox k L) ≤ C*(L+1:ℝ)^k)
    (hP : ∀ L : ℕ, l₀ ≤ L → ∀ᶠ j in atTop,
      (∫ x, (logarithmicCutoff k L x)^2 ∂μ j) ≤
        A * ∫ x, ‖fderiv ℝ (logarithmicCutoff k L) x‖^2 ∂μ j) : False := by
  obtain ⟨K,hKpos,hK⟩ := logarithmicCutoff_uniform_lipschitz k
  apply no_eventual_polynomial_shell_growth (fun j L => (μ j).real (logarithmicBox k L))
    k l₀ hc (show 0 < A*(K:ℝ)^2 by exact mul_pos hA (sq_pos_of_pos (by exact_mod_cast hKpos))) hpos ?_ hupper
  intro L hL
  filter_upwards [hP L hL,hfin (L+1) (by omega)] with j hj hf
  have hf' : μ j (logarithmicBox k ((L:ℝ)+1)) ≠ ⊤ := by
    simpa only [Nat.cast_add,Nat.cast_one] using hf
  simpa only [Nat.cast_add,Nat.cast_one] using logarithmic_shell_growth (μ j) (hK L) hf' hA.le hj

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualLogGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter Metric
open scoped Topology

open Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

lemma tsupport_logarithmicCutoff_subset (k : ℕ) (L : ℝ) :
    tsupport (logarithmicCutoff k L) ⊆ logarithmicBox k (L+1) := by
  apply closure_minimal _ (logarithmicBox_isClosed k (L+1))
  intro x hx i
  by_contra hi
  exact hx (logarithmicCutoff_zero ⟨i,(not_le.mp hi).le⟩)

/- Finiteness on each available logarithmic box follows from the literal
support-function density, without any a priori integral bound. -/
lemma affineEpigraphLogMeasure_box_finite {n k : ℕ}
    {μ : Measure (Space k)} [μ.IsAddHaarMeasure]
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D) (hDpos : D ⊆ positiveOrthant k)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) {R : ℝ}
    (hR : logarithmicBox k R ⊆ logSpace '' D) :
    affineEpigraphLogMeasure μ D Ω u a L bE (logarithmicBox k R) ≠ ⊤ := by
  obtain ⟨hM,hT,-⟩ := affineEpigraph_logWeight_regular hΩ hcv hu hp a L hD hDpos hK hzero bE
  exact (logTubeMeasure_compact_lt_top hDpos (hM.mul hT)
    (logarithmicBox_isCompact k R) hR).ne

/- The growth contradiction is now specialized to genuine affine-maximal
approximate graphs. Only the two remaining quantitative model bounds are inputs:
positive mass on one fixed box and a uniform polynomial upper bound. Every
Poincare estimate and local finiteness assertion is derived here. -/
theorem affineMaximal_no_polynomial_logMeasure_oai {n k l₀ : ℕ}
    (hn : 3 ≤ n) (hn9 : n ≤ 9) (hk : 2 ≤ k) (hkn : k ≤ n)
    {μ : Measure (Space k)} [μ.IsAddHaarMeasure]
    (Ω : ℕ → Set (Space n)) (u : ℕ → Space n → ℝ)
    (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × E) ≃L[ℝ] (Space n × ℝ))
    (D : ℕ → Set (Space k)) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hΩ : ∀ j, IsOpen (Ω j)) (hcv : ∀ j, Convex ℝ (Ω j))
    (hu : ∀ j, ContDiffOn ℝ ∞ (u j) (Ω j))
    (hp : ∀ j x, x ∈ Ω j → (hessian (u j) x).PosDef)
    (hm : ∀ j, AffineMaximalOn (Ω j) (u j))
    (hD : ∀ j, IsOpen (D j)) (hDpos : ∀ j, D j ⊆ positiveOrthant k)
    (hK : ∀ j s, s ∈ D j → IsCompact {y | (s,y) ∈ affineEpigraphPullback (Ω j) (u j) (a j) (L j)})
    (hzero : ∀ j s, s ∈ D j →
      (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback (Ω j) (u j) (a j) (L j)})
    (havail : ∀ R : ℕ, l₀ ≤ R → ∀ᶠ j in atTop, logarithmicBox k R ⊆ logSpace '' (D j))
    {c C : ℝ} (hc : 0 < c)
    (hpos : ∀ᶠ j in atTop, c ≤
      (affineEpigraphLogMeasure μ (D j) (Ω j) (u j) (a j) (L j) bE).real (logarithmicBox k l₀))
    (hupper : ∀ R : ℕ, l₀ ≤ R → ∀ᶠ j in atTop,
      (affineEpigraphLogMeasure μ (D j) (Ω j) (u j) (a j) (L j) bE).real (logarithmicBox k R) ≤
        C*(R+1:ℝ)^k) : False := by
  apply no_polynomial_logarithmic_poincare
    (fun j => affineEpigraphLogMeasure μ (D j) (Ω j) (u j) (a j) (L j) bE)
    hc (A := 4194304+(n : ℝ)*1358954512)
    (by positivity) hpos ?_ hupper ?_
  · intro R hR
    filter_upwards [havail R hR] with j hj
    exact affineEpigraphLogMeasure_box_finite (hΩ j) (hcv j) (hu j) (hp j) (a j) (L j)
      (hD j) (hDpos j) (hK j) (hzero j) bE hj
  · intro R hR
    filter_upwards [havail (R+1) (by omega)] with j hj
    apply affineMaximal_logMeasure_poincare hn hn9 hk hkn (hΩ j) (hcv j) (hu j) (hp j)
      (hm j) (a j) (L j) (hD j) (hDpos j) (hK j) (hzero j) bE
      (logarithmicCutoff_smooth k R) (logarithmicCutoff_hasCompactSupport k R)
    apply (tsupport_logarithmicCutoff_subset k R).trans
    simpa only [Nat.cast_add,Nat.cast_one] using hj

end AffineBernstein

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.AffineBernstein.affineMaximal_no_polynomial_logMeasure_oai.{u_1, u_2} := @OAI.AffineBernstein.affineMaximal_no_polynomial_logMeasure_oai.{u_1, u_2}
