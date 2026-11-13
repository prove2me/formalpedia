-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.CollarVelocity.small_shift_collar_density
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:38:15.666852+00:00
-- url     : https://prove2.me/submissions/9370a78b-756b-4fe3-b602-2a9aa1086f81

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Definitions.Def_OAIQ249SI005

section
-- module Solutions.OAIQ249_SI.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- d13f23b's `ContinuousLinearMap.IsInvertible.eventually_nhds`: invertible operators form an open set
(SurfaceImmersion primitives, q249). -/
theorem _root_.ContinuousLinearMap.IsInvertible.eventually_nhds {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E →L[𝕜] F} (hf : f.IsInvertible) : ∀ᶠ g in nhds f, g.IsInvertible := by
  obtain ⟨e, rfl⟩ := hf
  exact Filter.mem_of_superset (ContinuousLinearEquiv.nhds e) (by rintro _ ⟨e', rfl⟩; exact ⟨e', rfl⟩)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LoopDensityLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three linear moment equations for a positive loop density. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.LoopDensity

lemma momentMap_apply (p : ℝ → Plane) (ψ : Fin 3 → ℝ → ℝ) (w : Moments) :
    momentMap p ψ w = ∑ i, w i • column p (ψ i) := by
  simp [momentMap, ContinuousLinearMap.smulRight_apply]

lemma augment_continuous : Continuous augment := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [augment] <;> fun_prop

lemma density_pos {ε : ℝ} (hε : 0 < ε) {ψ : Fin 3 → ℝ → ℝ} {w : Moments}
    (hψ : ∀ i t, 0 ≤ ψ i t) (hw : ∀ i, 0 ≤ w i) (t : ℝ) : 0 < density ε ψ w t := by
  apply add_pos_of_pos_of_nonneg hε
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hψ i t))

lemma density_periodic (ε : ℝ) (ψ : Fin 3 → ℝ → ℝ) (w : Moments)
    (hp : ∀ i, Function.Periodic (ψ i) 1) : Function.Periodic (density ε ψ w) 1 := by
  intro t
  simp only [density]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hp i t]

lemma density_moments {p : ℝ → Plane} (hp : Continuous p)
    {ψ : Fin 3 → ℝ → ℝ} (hψ : ∀ i, Continuous (ψ i)) (ε : ℝ) (w : Moments) :
    (∫ t in 0..1, density ε ψ w t • augment (p t)) =
      ε • background p + momentMap p ψ w := by
  have hc : Continuous (fun t => augment (p t)) := augment_continuous.comp hp
  have he : Continuous (fun t => ε • augment (p t)) := hc.const_smul ε
  have hs : Continuous (fun t => (∑ i, w i * ψ i t) • augment (p t)) :=
    (continuous_finsetSum _ (fun i _ => continuous_const.mul (hψ i))).smul hc
  simp_rw [density, add_smul]
  rw [intervalIntegral.integral_add
    (f := fun t => ε • augment (p t))
    (g := fun t => (∑ i, w i * ψ i t) • augment (p t))
    (he.intervalIntegrable _ _)
    (hs.intervalIntegrable _ _), intervalIntegral.integral_smul]
  congr 1
  simp_rw [Finset.sum_smul]
  rw [intervalIntegral.integral_finsetSum]
  · rw [momentMap_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_smul, intervalIntegral.integral_smul, column]
  · intro i _
    exact ((continuous_const.mul (hψ i)).smul hc).intervalIntegrable _ _

/-- Once the moment matrix is invertible, all three equations are solved exactly. -/
theorem solved_moments {p : ℝ → Plane} (hp : Continuous p)
    {ψ : Fin 3 → ℝ → ℝ} (hψ : ∀ i, Continuous (ψ i))
    (hM : (momentMap p ψ).IsInvertible) (ε : ℝ) (c : Plane) :
    (∫ t in 0..1, density ε ψ (weights p ψ ε c) t • augment (p t)) = augment c := by
  rw [density_moments hp hψ]
  unfold weights
  rw [hM.self_apply_inverse]
  abel

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LoopDensityParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth local positive solutions of the three density moment equations. -/
noncomputable section
open Filter Set
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.LoopDensity

lemma augment_smooth : ContDiff ℝ ∞ augment := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun _ : Plane => (1 : ℝ))
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun x : Plane => x 0)
    exact contDiff_apply ℝ ℝ 0
  · change ContDiff ℝ ∞ (fun x : Plane => x 1)
    exact contDiff_apply ℝ ℝ 1

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  {p : B → ℝ → Plane} {c : B → Plane} {ψ : Fin 3 → ℝ → ℝ}

lemma background_smooth (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2)) :
    ContDiff ℝ ∞ (fun b => background (p b)) :=
  SmoothParameterIntegral.contDiff_integral (augment_smooth.comp hp) 0 1

lemma column_smooth (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2))
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (i : Fin 3) :
    ContDiff ℝ ∞ (fun b => column (p b) (ψ i)) :=
  SmoothParameterIntegral.contDiff_integral
    (((hψ i).comp contDiff_snd).smul (augment_smooth.comp hp)) 0 1

lemma momentMap_smooth (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2))
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) :
    ContDiff ℝ ∞ (fun b => momentMap (p b) ψ) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.smulRight (column_smooth hp hψ i)

lemma weights_smoothAt (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2))
    (hc : ContDiff ℝ ∞ c) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    {b : B} (hM : (momentMap (p b) ψ).IsInvertible) (ε : ℝ) :
    ContDiffAt ℝ ∞ (fun x => weights (p x) ψ ε (c x)) b := by
  exact (hM.contDiffAt_map_inverse.comp b (momentMap_smooth hp hψ).contDiffAt).clm_apply
    (((augment_smooth.comp hc).sub ((background_smooth hp).const_smul ε)).contDiffAt)

lemma weights_smoothOn (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2))
    (hc : ContDiff ℝ ∞ c) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    {U : Set B} (hM : ∀ b ∈ U, (momentMap (p b) ψ).IsInvertible) (ε : ℝ) :
    ContDiffOn ℝ ∞ (fun x => weights (p x) ψ ε (c x)) U :=
  fun b hb => (weights_smoothAt hp hc hψ (hM b hb) ε).contDiffWithinAt

/-- Positive weights and an invertible three-moment matrix persist locally;
this constructs an actual smooth positive density with the exact required mean. -/
theorem exists_positive_density_near
    (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2)) (hc : ContDiff ℝ ∞ c)
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (hψnonneg : ∀ i t, 0 ≤ ψ i t)
    (hψper : ∀ i, Function.Periodic (ψ i) 1)
    {b₀ : B} {ε : ℝ} (hε : 0 < ε) (hM : (momentMap (p b₀) ψ).IsInvertible)
    (hw : ∀ i, 0 < weights (p b₀) ψ ε (c b₀) i) :
    ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧ ∃ ρ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ ρ (U ×ˢ Set.univ) ∧
      (∀ b ∈ U, ∀ t, 0 < ρ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
      ∀ b ∈ U, (∫ t in 0..1, ρ (b, t) • augment (p b t)) = augment (c b) := by
  have hmNear : ∀ᶠ b in 𝓝 b₀, (momentMap (p b) ψ).IsInvertible :=
    (momentMap_smooth hp hψ).continuous.continuousAt.eventually hM.eventually_nhds
  have hwAt := (weights_smoothAt hp hc hψ hM ε).continuousAt
  have hwNear : ∀ᶠ b in 𝓝 b₀, ∀ i, 0 < weights (p b) ψ ε (c b) i := by
    rw [Filter.eventually_all]
    intro i
    exact ((continuous_apply i).continuousAt.comp hwAt).eventually_const_lt (hw i)
  obtain ⟨U, hUsub, hU, hb₀⟩ := mem_nhds_iff.mp (hmNear.and hwNear)
  let ρ : B × ℝ → ℝ := fun z => density ε ψ (weights (p z.1) ψ ε (c z.1)) z.2
  have hweights := weights_smoothOn hp hc hψ (fun b hb => (hUsub hb).1) ε
  refine ⟨U, hU, hb₀, ρ, ?_, ?_, ?_, ?_⟩
  · apply contDiffOn_const.add
    apply ContDiffOn.sum
    intro i _
    have hwi : ContDiffOn ℝ ∞
        (fun z : B × ℝ => weights (p z.1) ψ ε (c z.1) i) (U ×ˢ Set.univ) :=
      ((contDiff_apply ℝ ℝ i).comp_contDiffOn hweights).comp contDiffOn_fst
        (fun _ hz => hz.1)
    exact hwi.mul ((hψ i).comp contDiff_snd).contDiffOn
  · intro b hb t
    exact density_pos hε hψnonneg (fun i => ((hUsub hb).2 i).le) t
  · intro b
    exact density_periodic ε ψ (weights (p b) ψ ε (c b)) hψper
  · intro b hb
    exact solved_moments
      (hp.continuous.comp (continuous_const.prodMk continuous_id))
      (fun i => (hψ i).continuous) (hUsub hb).1 ε (c b)

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LoopDensityPatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite smooth patching of local positive density solutions. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.LoopDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
  {ι : Type*} [Fintype ι]

/-- Nonnegative smooth weights preserve both positivity and the linear moments;
normalization gives mass one on the open region where some weight is positive. -/
theorem patch_densities
    {p : B → ℝ → Plane} {c : B → Plane}
    (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2))
    (U : ι → Set B) (hU : ∀ i, IsOpen (U i))
    (ρ : ι → B × ℝ → ℝ)
    (hρ : ∀ i, ContDiffOn ℝ ∞ (ρ i) (U i ×ˢ univ))
    (hpos : ∀ i b, b ∈ U i → ∀ t, 0 < ρ i (b, t))
    (hper : ∀ i b, Function.Periodic (fun t => ρ i (b, t)) 1)
    (hmom : ∀ i b, b ∈ U i →
      (∫ t in 0..1, ρ i (b, t) • augment (p b t)) = augment (c b))
    (ψ : ι → B → ℝ) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    (hn : ∀ i b, 0 ≤ ψ i b) (hsupp : ∀ i, tsupport (ψ i) ⊆ U i) :
    ∃ σ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ σ ({b | 0 < ∑ i, ψ i b} ×ˢ univ) ∧
      (∀ b, 0 < ∑ i, ψ i b → ∀ t, 0 < σ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => σ (b, t)) 1) ∧
      (∀ b, 0 < ∑ i, ψ i b →
        (∫ t in 0..1, σ (b, t) • augment (p b t)) = augment (c b)) ∧
      σ = (fun z => (∑ i, ψ i z.1 * ρ i z) / (∑ i, ψ i z.1)) := by
  let w : ι → B × ℝ → ℝ := fun i z => ψ i z.1 * ρ i z
  have hw (i : ι) : ContDiff ℝ ∞ (w i) := by
    apply LocalPeriodicExpansion.contDiff_of_zero_off_closed (hU i)
      (((hψ i).comp contDiff_fst).contDiffOn.mul (hρ i)) (isClosed_tsupport _) (hsupp i)
    intro b hb t
    have hz : ψ i b = 0 := image_eq_zero_of_notMem_tsupport hb
    change ψ i b * ρ i (b, t) = 0
    rw [hz, zero_mul]
  let S : B → ℝ := fun b => ∑ i, ψ i b
  let W : B × ℝ → ℝ := fun z => ∑ i, w i z
  let σ : B × ℝ → ℝ := fun z => W z / S z.1
  have hS : ContDiff ℝ ∞ S := ContDiff.sum (fun i _ => hψ i)
  have hW : ContDiff ℝ ∞ W := ContDiff.sum (fun i _ => hw i)
  have hUof (i : ι) (b : B) (hne : ψ i b ≠ 0) : b ∈ U i :=
    hsupp i (subset_tsupport _ (Function.mem_support.mpr hne))
  have hterm (i : ι) (b : B) (t : ℝ) : 0 ≤ w i (b, t) := by
    by_cases hz : ψ i b = 0
    · simp [w, hz]
    · exact mul_nonneg (hn i b) (hpos i b (hUof i b hz) t).le
  refine ⟨σ, ?_, ?_, ?_, ?_, rfl⟩
  · exact hW.contDiffOn.div (hS.comp contDiff_fst).contDiffOn (fun z hz => hz.1.ne')
  · intro b hb t
    obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => hn j b)).mp hb
    have hwi : 0 < w i (b, t) := mul_pos hi (hpos i b (hUof i b hi.ne') t)
    exact div_pos (lt_of_lt_of_le hwi (Finset.single_le_sum (fun j _ => hterm j b t)
      (Finset.mem_univ i))) hb
  · intro b t
    change (∑ i, ψ i b * ρ i (b, t + 1)) / S b = (∑ i, ψ i b * ρ i (b, t)) / S b
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun x : ℝ => ψ i b * x) (hper i b t)
  · intro b hb
    have hpc : Continuous (fun t => augment (p b t)) :=
      augment_continuous.comp (hp.continuous.comp (continuous_const.prodMk continuous_id))
    have hint (i : ι) : IntervalIntegrable (fun t => w i (b, t) • augment (p b t))
        MeasureTheory.volume 0 1 :=
      (((hw i).continuous.comp (continuous_const.prodMk continuous_id)).smul hpc).intervalIntegrable _ _
    have hmean : (∫ t in 0..1, W (b, t) • augment (p b t)) = S b • augment (c b) := by
      change (∫ t in 0..1, (∑ i, w i (b, t)) • augment (p b t)) = _
      simp_rw [Finset.sum_smul]
      rw [intervalIntegral.integral_finsetSum (fun i _ => hint i)]
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hz : ψ i b = 0
      · simp [w, hz]
      · change (∫ t in 0..1, (ψ i b * ρ i (b, t)) • augment (p b t)) = _
        simp_rw [mul_smul]
        rw [intervalIntegral.integral_smul, hmom i b (hUof i b hz)]
    change (∫ t in 0..1, (W (b, t) / S b) • augment (p b t)) = _
    simp_rw [div_eq_inv_mul, mul_smul]
    rw [intervalIntegral.integral_smul, hmean, smul_smul, inv_mul_cancel₀ hb.ne', one_smul]

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LoopDensityCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact patching, retaining every value on which the local densities agree. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LoopDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

theorem compact_patch_densities {ι : Type*} {p : B → ℝ → Plane} {c : B → Plane}
    (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2))
    (U : ι → Set B) (hU : ∀ i, IsOpen (U i))
    (ρ : ι → B × ℝ → ℝ)
    (hρ : ∀ i, ContDiffOn ℝ ∞ (ρ i) (U i ×ˢ univ))
    (hpos : ∀ i b, b ∈ U i → ∀ t, 0 < ρ i (b, t))
    (hper : ∀ i b, Function.Periodic (fun t => ρ i (b, t)) 1)
    (hmom : ∀ i b, b ∈ U i →
      (∫ t in 0..1, ρ i (b, t) • augment (p b t)) = augment (c b))
    {K : Set B} (hK : IsCompact K) (hcover : K ⊆ ⋃ i, U i) :
    ∃ V : Set B, IsOpen V ∧ K ⊆ V ∧ ∃ σ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ σ (V ×ˢ univ) ∧
      (∀ b ∈ V, ∀ t, 0 < σ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => σ (b, t)) 1) ∧
      (∀ b ∈ V, (∫ t in 0..1, σ (b, t) • augment (p b t)) = augment (c b)) ∧
      ∀ b ∈ V, ∀ t r, (∀ i, b ∈ U i → ρ i (b, t) = r) → σ (b, t) = r := by
  classical
  obtain ⟨J, hJ⟩ := hK.elim_finite_subcover U hU hcover
  have hcJ : K ⊆ ⋃ i : J, U i.val := by
    intro b hbk
    obtain ⟨i, hi, hbi⟩ := mem_iUnion₂.mp (hJ hbk)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hbi⟩
  obtain ⟨ψ, hψsub⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, B))
    hK.isClosed (fun i : J => U i.val) (fun i => hU i.val) hcJ
  have hψ (i : J) : ContDiff ℝ ∞ (ψ i) := (ψ i).contMDiff.contDiff
  let S : B → ℝ := fun b => ∑ i : J, ψ i b
  have hS : ContDiff ℝ ∞ S := ContDiff.sum (fun i _ => hψ i)
  let V : Set B := {b | 0 < S b}
  have hV : IsOpen V := isOpen_lt continuous_const hS.continuous
  have hKV : K ⊆ V := by
    intro b hbk
    have hone : S b = 1 := by
      simpa only [S, finsum_eq_sum_of_fintype] using ψ.sum_eq_one hbk
    change 0 < S b
    rw [hone]
    exact zero_lt_one
  obtain ⟨σ, hσ, hpσ, hperσ, hmσ, hformula⟩ := patch_densities hp
    (fun i : J => U i.val) (fun i : J => hU i.val) (fun i : J => ρ i.val)
    (fun i : J => hρ i.val) (fun i : J => hpos i.val) (fun i : J => hper i.val)
    (fun i : J => hmom i.val) (fun (i : J) b => ψ i b) hψ
    (fun (i : J) b => ψ.nonneg i b) hψsub
  refine ⟨V, hV, hKV, σ, hσ, hpσ, hperσ, hmσ, ?_⟩
  intro b hb t r hr
  rw [hformula]
  change (∑ i : J, ψ i b * ρ i.val (b, t)) / S b = r
  have hsum : (∑ i : J, ψ i b * ρ i.val (b, t)) = S b * r := by
    dsimp only [S]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hz : ψ i b = 0
    · rw [hz, zero_mul, zero_mul]
    · rw [hr i.val (hψsub i (subset_tsupport _ (Function.mem_support.mpr hz)))]
  rw [hsum]
  exact mul_div_cancel_left₀ r hb.ne'

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LoopDensityRelative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend prescribed positive densities while fixing a closed collar. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.LoopDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

theorem positive_density_compact_preserving
    {p : B → ℝ → Plane} {c : B → Plane}
    (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2))
    {U C K : Set B} (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hK : IsCompact K) (ρ₀ : B × ℝ → ℝ)
    (hρ₀ : ContDiffOn ℝ ∞ ρ₀ (U ×ˢ univ))
    (hpos₀ : ∀ b ∈ U, ∀ t, 0 < ρ₀ (b, t))
    (hper₀ : ∀ b, Function.Periodic (fun t => ρ₀ (b, t)) 1)
    (hmom₀ : ∀ b ∈ U, (∫ t in 0..1, ρ₀ (b, t) • augment (p b t)) = augment (c b))
    (hlocal : ∀ b ∈ K \ U, ∃ W : Set B, IsOpen W ∧ b ∈ W ∧ ∃ ρ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ ρ (W ×ˢ univ) ∧
      (∀ x ∈ W, ∀ t, 0 < ρ (x, t)) ∧
      (∀ x, Function.Periodic (fun t => ρ (x, t)) 1) ∧
      ∀ x ∈ W, (∫ t in 0..1, ρ (x, t) • augment (p x t)) = augment (c x)) :
    ∃ V : Set B, IsOpen V ∧ K ⊆ V ∧ ∃ σ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ σ (V ×ˢ univ) ∧
      (∀ b ∈ V, ∀ t, 0 < σ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => σ (b, t)) 1) ∧
      (∀ b ∈ V, (∫ t in 0..1, σ (b, t) • augment (p b t)) = augment (c b)) ∧
      ∀ b ∈ V ∩ C, ∀ t, σ (b, t) = ρ₀ (b, t) := by
  classical
  let I := {b : B // b ∈ K \ U}
  choose W hW hbW ρ hρ hpos hper hmom using fun b : I => hlocal b b.property
  let O : Option I → Set B := fun i =>
    match i with
    | none => U
    | some b => W b \ C
  let r : Option I → B × ℝ → ℝ := fun i =>
    match i with
    | none => ρ₀
    | some b => ρ b
  have hO (i : Option I) : IsOpen (O i) := by
    cases i with
    | none => exact hU
    | some b => exact (hW b).sdiff hC
  have hr (i : Option I) : ContDiffOn ℝ ∞ (r i) (O i ×ˢ univ) := by
    cases i with
    | none => exact hρ₀
    | some b => exact (hρ b).mono (fun _ hx => ⟨hx.1.1, hx.2⟩)
  have hrpos (i : Option I) (x : B) (hx : x ∈ O i) (t : ℝ) : 0 < r i (x, t) := by
    cases i with
    | none => exact hpos₀ x hx t
    | some b => exact hpos b x hx.1 t
  have hrper (i : Option I) (x : B) : Function.Periodic (fun t => r i (x, t)) 1 := by
    cases i with
    | none => exact hper₀ x
    | some b => exact hper b x
  have hrmom (i : Option I) (x : B) (hx : x ∈ O i) :
      (∫ t in 0..1, r i (x, t) • augment (p x t)) = augment (c x) := by
    cases i with
    | none => exact hmom₀ x hx
    | some b => exact hmom b x hx.1
  have hcover : K ⊆ ⋃ i, O i := by
    intro b hbK
    by_cases hbU : b ∈ U
    · exact mem_iUnion.mpr ⟨none, hbU⟩
    · have hbC : b ∉ C := fun h => hbU (hCU h)
      exact mem_iUnion.mpr ⟨some ⟨b, hbK, hbU⟩, hbW ⟨b, hbK, hbU⟩, hbC⟩
  obtain ⟨V, hV, hKV, σ, hσ, hσpos, hσper, hσmom, heq⟩ :=
    compact_patch_densities hp O hO r hr hrpos hrper hrmom hK hcover
  refine ⟨V, hV, hKV, σ, hσ, hσpos, hσper, hσmom, ?_⟩
  intro b hb t
  apply heq b hb.1 t (ρ₀ (b, t))
  intro i hi
  cases i with
  | none => rfl
  | some x => exact False.elim (hi.2 hb.2)

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarVelocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit small circular arc and positive averaging density. This gives
an alternative collar construction without solving a squared-amplitude equation. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

lemma density_mul_arcX (a t : ℝ) :
    density a t * arcX a t = (1 - (a * Real.cos t) ^ 2) / (1 + a ^ 2 / 2) := by
  unfold density arcX
  field_simp [(arcDen_pos a t).ne', (densityDen_pos a).ne']

lemma density_mul_arcY (a t : ℝ) :
    density a t * arcY a t = 2 * a * Real.cos t / (1 + a ^ 2 / 2) := by
  unfold density arcY
  field_simp [(arcDen_pos a t).ne', (densityDen_pos a).ne']

lemma density_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => density z.1 z.2) := by
  exact (contDiff_const.add ((contDiff_fst.mul contDiff_snd.cos).pow 2)).div
    (contDiff_const.add (contDiff_fst.pow 2 |>.div_const 2))
    (fun z => (densityDen_pos z.1).ne')

lemma density_periodic (a : ℝ) : Function.Periodic (density a) (2 * Real.pi) := by
  intro t
  simp only [density, Real.cos_add_two_pi]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarVelocityMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact mean constraints for the explicit collar velocity arc. -/
noncomputable section
open MeasureTheory

namespace ClosedSurfaceR4.CollarVelocity

lemma integral_cos_period : (∫ t in (0 : ℝ)..2 * Real.pi, Real.cos t) = 0 := by
  rw [integral_cos]
  simp

lemma integral_cos_sq_period : (∫ t in (0 : ℝ)..2 * Real.pi, Real.cos t ^ 2) = Real.pi := by
  rw [integral_cos_sq]
  simp

lemma integral_arc_den (a : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi, 1 + (a * Real.cos t) ^ 2) =
      2 * Real.pi * (1 + a ^ 2 / 2) := by
  simp only [mul_pow]
  rw [intervalIntegral.integral_add (f := fun _ : ℝ => (1 : ℝ))
    (g := fun t : ℝ => a ^ 2 * Real.cos t ^ 2) intervalIntegrable_const
    ((continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_cos_sq_period]
  simp only [sub_zero, smul_eq_mul, mul_one]
  ring

lemma integral_arc_num (a : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi, 1 - (a * Real.cos t) ^ 2) =
      2 * Real.pi * (1 - a ^ 2 / 2) := by
  simp only [mul_pow]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ))
    (g := fun t : ℝ => a ^ 2 * Real.cos t ^ 2) intervalIntegrable_const
    ((continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_cos_sq_period]
  simp only [sub_zero, smul_eq_mul, mul_one]
  ring

lemma mean_density (a : ℝ) : circleMean (density a) = 1 := by
  unfold circleMean density
  rw [intervalIntegral.integral_div, integral_arc_den]
  field_simp [(densityDen_pos a).ne', Real.pi_ne_zero]

lemma mean_density_arcX (a : ℝ) :
    circleMean (fun t => density a t * arcX a t) = (1 - a ^ 2 / 2) / (1 + a ^ 2 / 2) := by
  unfold circleMean
  simp_rw [density_mul_arcX]
  rw [intervalIntegral.integral_div, integral_arc_num]
  field_simp [(densityDen_pos a).ne', Real.pi_ne_zero]

lemma mean_density_arcY (a : ℝ) : circleMean (fun t => density a t * arcY a t) = 0 := by
  unfold circleMean
  simp_rw [density_mul_arcY]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_cos_period]
  simp

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarVelocityAngle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit collar arc has exactly two stationary angular positions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

lemma baseAngle_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => baseAngle z.1 z.2) :=
  contDiff_const.mul ((contDiff_fst.mul contDiff_snd.cos).arctan)

lemma cos_baseAngle (a t : ℝ) : Real.cos (baseAngle a t) = arcX a t := by
  rw [baseAngle, Real.cos_two_mul, Real.cos_sq_arctan]
  unfold arcX
  field_simp [(arcDen_pos a t).ne']
  ring

lemma sin_baseAngle (a t : ℝ) : Real.sin (baseAngle a t) = arcY a t := by
  rw [baseAngle, Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  unfold arcY
  have hs : Real.sqrt (1 + (a * Real.cos t) ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 (arcDen_pos a t)).ne'
  field_simp [hs]
  rw [Real.sq_sqrt (by positivity)]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityAngleInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interpolate the collar angle to a circle-covering interior angle without extra turns. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

lemma blendedAngle_zero (a A s h : ℝ) :
    blendedAngle a A s h 0 = h + ((1 - s) * (2 * Real.arctan a) + s * A) := by
  simp [blendedAngle, baseAngle]
  ring

lemma blendedAngle_pi (a A s h : ℝ) :
    blendedAngle a A s h Real.pi = h - ((1 - s) * (2 * Real.arctan a) + s * A) := by
  simp [blendedAngle, baseAngle, Real.arctan_neg]
  ring

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicLocalizedBump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth positive-mass bumps on the unit circle, localized inside one period. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.LoopDensity

lemma circleBump_smooth (φ : ContDiffBump (0 : ℝ)) (c : ℝ) :
    ContDiff ℝ ∞ (circleBump φ c) :=
  φ.contDiff.comp ((contDiff_const.mul (contDiff_id.sub contDiff_const)).sin)

lemma circleBump_periodic (φ : ContDiffBump (0 : ℝ)) (c : ℝ) :
    Function.Periodic (circleBump φ c) 1 := by
  intro t
  unfold circleBump
  rw [show Real.pi * (t + 1 - c) = Real.pi * (t - c) + Real.pi by ring]
  rw [Real.sin_add_pi, φ.neg]

lemma circleBump_at_center (φ : ContDiffBump (0 : ℝ)) (c : ℝ) : circleBump φ c c = 1 := by
  simp only [circleBump, sub_self, mul_zero, Real.sin_zero]
  exact φ.one_of_mem_closedBall (mem_closedBall_self φ.rIn_pos.le)

private lemma sine_nonzero {c t : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hne : t ≠ c) : Real.sin (Real.pi * (t - c)) ≠ 0 := by
  rw [ne_eq, Real.sin_eq_zero_iff_of_lt_of_lt]
  · exact mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr hne)
  · have h : -1 < t - c := by linarith [hc.2, ht.1]
    simpa using mul_lt_mul_of_pos_left h Real.pi_pos
  · have h : t - c < 1 := by linarith [hc.1, ht.2]
    simpa using mul_lt_mul_of_pos_left h Real.pi_pos

/-- An actual smooth periodic nonnegative density of mass one supported in any
prescribed neighborhood of an interior point of the fundamental interval. -/
theorem exists_localized_bump {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1)
    {V : Set ℝ} (hV : IsOpen V) (hcV : c ∈ V) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ Function.Periodic ψ 1 ∧
      (∀ t, 0 ≤ ψ t) ∧ (∫ t in 0..1, ψ t) = 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, t ∉ V → ψ t = 0 := by
  let K := Icc (0 : ℝ) 1 \ V
  have hK : IsCompact K := isCompact_Icc.diff hV
  have hf : Continuous (fun t : ℝ => |Real.sin (Real.pi * (t - c))|) := by fun_prop
  have hr : ∃ r : ℝ, 0 < r ∧ ∀ t ∈ K, r ≤ |Real.sin (Real.pi * (t - c))| := by
    by_cases hne : K.Nonempty
    · obtain ⟨t, ht, hmin⟩ := hK.exists_isMinOn hne hf.continuousOn
      refine ⟨|Real.sin (Real.pi * (t - c))|, abs_pos.mpr ?_, hmin⟩
      apply sine_nonzero hc ht.1
      intro heq
      exact ht.2 (heq ▸ hcV)
    · exact ⟨1, zero_lt_one, fun t ht => (hne ⟨t, ht⟩).elim⟩
  obtain ⟨r, hr, hbound⟩ := hr
  let φ : ContDiffBump (0 : ℝ) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let f := circleBump φ c
  have hfs : ContDiff ℝ ∞ f := circleBump_smooth φ c
  have hfn (t : ℝ) : 0 ≤ f t := φ.nonneg
  have hfc : f c = 1 := circleBump_at_center φ c
  have hfi : 0 < ∫ t in 0..1, f t :=
    intervalIntegral.integral_pos zero_lt_one hfs.continuous.continuousOn
      (fun t _ => hfn t) ⟨c, ⟨hc.1.le, hc.2.le⟩, by rw [hfc]; norm_num⟩
  let ψ : ℝ → ℝ := fun t => f t / ∫ s in 0..1, f s
  refine ⟨ψ, hfs.div_const _, ?_, ?_, ?_, ?_⟩
  · intro t
    change f (t + 1) / _ = f t / _
    exact congrArg (fun x : ℝ => x / ∫ s in 0..1, f s) (circleBump_periodic φ c t)
  · intro t
    exact div_nonneg (hfn t) hfi.le
  · change (∫ t in 0..1, f t / _) = 1
    rw [intervalIntegral.integral_div, div_self hfi.ne']
  · intro t ht htV
    have hz : f t = 0 := by
      apply φ.zero_of_le_dist
      change r / 2 ≤ dist (Real.sin (Real.pi * (t - c))) 0
      rw [Real.dist_eq, sub_zero]
      exact (by linarith : r / 2 ≤ r).trans (hbound t ⟨ht, htV⟩)
    change f t / _ = 0
    rw [hz, zero_div]

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicBumpAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Localized positive periodic densities approximate any chosen path value. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.LoopDensity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Point masses in the convex-hull argument can be replaced by actual smooth
nonnegative densities while changing their vector moments arbitrarily little. -/
theorem exists_bump_average_near {f : ℝ → E} (hf : Continuous f)
    {c ε : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ Function.Periodic ψ 1 ∧
      (∀ t, 0 ≤ ψ t) ∧ (∫ t in 0..1, ψ t) = 1 ∧
      ‖(∫ t in 0..1, ψ t • f t) - f c‖ < ε := by
  let V := f ⁻¹' ball (f c) (ε / 2)
  have hV : IsOpen V := isOpen_ball.preimage hf
  have hcV : c ∈ V := mem_ball_self (by positivity)
  obtain ⟨ψ, hψ, hper, hnonneg, hmass, hsupp⟩ := exists_localized_bump hc hV hcV
  refine ⟨ψ, hψ, hper, hnonneg, hmass, ?_⟩
  have hconst : Continuous (fun t => ψ t • f c) := hψ.continuous.smul continuous_const
  have hprod : Continuous (fun t => ψ t • f t) := hψ.continuous.smul hf
  have heq : (∫ t in 0..1, ψ t • f t) - f c =
      ∫ t in 0..1, ψ t • (f t - f c) := by
    simp_rw [smul_sub]
    rw [intervalIntegral.integral_sub (hprod.intervalIntegrable _ _)
      (hconst.intervalIntegrable _ _), intervalIntegral.integral_smul_const, hmass, one_smul]
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖ψ t • (f t - f c)‖ ≤ ψ t * (ε / 2) := by
    by_cases hz : ψ t = 0
    · simp [hz]
    · have htV : t ∈ V := by
        by_contra h
        exact hz (hsupp t ht h)
      have hd : ‖f t - f c‖ < ε / 2 := by
        simpa only [V, mem_preimage, mem_ball, dist_eq_norm] using htV
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnonneg t)]
      exact mul_le_mul_of_nonneg_left hd.le (hnonneg t)
  rw [heq]
  calc
    _ ≤ ∫ t in 0..1, ψ t * (ε / 2) := by
      exact intervalIntegral.norm_integral_le_of_norm_le zero_le_one
        (Filter.Eventually.of_forall (fun t ht => hb t ⟨ht.1.le, ht.2⟩))
        ((hψ.continuous.mul_const (ε / 2)).intervalIntegrable _ _)
    _ = ε / 2 := by rw [intervalIntegral.integral_mul_const, hmass, one_mul]
    _ < ε := by linarith

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LoopDensityBumpSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replace three nondegenerate point masses by smooth positive-density data. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.LoopDensity

lemma columnOperator_smooth : ContDiff ℝ ∞ columnOperator := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.smulRight (contDiff_apply ℝ Moments i)

/-- A strictly positive, nondegenerate three-point barycenter can be replaced
by smooth nonnegative periodic bumps and a strictly positive constant density. -/
theorem select_positive_moment_bumps {p : ℝ → Plane} (hp : Continuous p)
    {t : Fin 3 → ℝ} (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1)
    {c : Plane} {w : Moments}
    (hM : (columnOperator (fun i => augment (p (t i)))).IsInvertible)
    (hw : ∀ i, 0 < w i)
    (hbary : columnOperator (fun i => augment (p (t i))) w = augment c) :
    ∃ ψ : Fin 3 → ℝ → ℝ, (∀ i, ContDiff ℝ ∞ (ψ i)) ∧
      (∀ i, Function.Periodic (ψ i) 1) ∧ (∀ i x, 0 ≤ ψ i x) ∧
      (∀ i, (∫ x in 0..1, ψ i x) = 1) ∧
      ∃ ε : ℝ, 0 < ε ∧ (momentMap p ψ).IsInvertible ∧
        ∀ i, 0 < weights p ψ ε c i := by
  let C₀ : Columns := fun i => augment (p (t i))
  let W : Columns × ℝ → Moments := fun z =>
    (columnOperator z.1).inverse (augment c - z.2 • background p)
  have hsource : ContDiff ℝ ∞ (fun z : Columns × ℝ => augment c - z.2 • background p) :=
    contDiff_const.sub (contDiff_snd.smul contDiff_const)
  have hi : ContDiffAt ℝ ∞ (fun z : Columns × ℝ => (columnOperator z.1).inverse) (C₀, 0) :=
    hM.contDiffAt_map_inverse.comp (C₀, 0)
      (columnOperator_smooth.comp contDiff_fst).contDiffAt
  have hW : ContDiffAt ℝ ∞ W (C₀, 0) := hi.clm_apply hsource.contDiffAt
  have hW₀ : W (C₀, 0) = w := by
    change (columnOperator C₀).inverse (augment c - (0 : ℝ) • background p) = w
    rw [zero_smul, sub_zero, ← hbary, hM.inverse_apply_self]
  have hnearM : ∀ᶠ z : Columns × ℝ in 𝓝 (C₀, 0), (columnOperator z.1).IsInvertible :=
    (columnOperator_smooth.comp contDiff_fst).continuous.continuousAt.eventually hM.eventually_nhds
  have hnearW : ∀ᶠ z : Columns × ℝ in 𝓝 (C₀, 0), ∀ i, 0 < W z i := by
    rw [Filter.eventually_all]
    intro i
    exact ((continuous_apply i).continuousAt.comp hW.continuousAt).eventually_const_lt
      (by change 0 < W (C₀, 0) i; rw [hW₀]; exact hw i)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hnearM.and hnearW)
  have hchoose (i : Fin 3) := exists_bump_average_near (augment_continuous.comp hp) (ht i) hδ
  choose ψ hψ hper hn hm hclose using hchoose
  let C : Columns := fun i => column p (ψ i)
  have hC : ‖C - C₀‖ < δ := by
    apply (pi_norm_lt_iff hδ).mpr
    intro i
    exact hclose i
  have hz : (C, δ / 2) ∈ ball (C₀, 0) δ := by
    rw [mem_ball, Prod.dist_eq]
    apply max_lt
    · simpa only [dist_eq_norm] using hC
    · rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < δ / 2)]
      linarith
  have hgood := hball hz
  exact ⟨ψ, hψ, hper, hn, hm, δ / 2, by positivity, hgood.1, hgood.2⟩

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LoopDensityTriangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three circle directions strictly surrounding any radial target in the open disk. -/
noncomputable section
open scoped Matrix BigOperators

namespace ClosedSurfaceR4.LoopDensity

lemma triangleWeights_pos {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (i : Fin 3) :
    0 < triangleWeights r i := by
  fin_cases i <;> simp [triangleWeights] <;> linarith

lemma triangle_barycenter (e : Plane) (r : ℝ) :
    columnOperator (fun i => augment (triangle e i)) (triangleWeights r) = augment (r • e) := by
  ext i
  fin_cases i <;>
    simp [columnOperator, triangle, triangleWeights, augment, Fin.sum_univ_three] <;> ring

lemma triangle_determinant {e : Plane} (he : e 0 ^ 2 + e 1 ^ 2 = 1) :
    Matrix.det (Matrix.of (fun i j : Fin 3 => augment (triangle e j) i)) = 3 * Real.sqrt 3 / 2 := by
  calc
    _ = (3 * Real.sqrt 3 / 2) * (e 0 ^ 2 + e 1 ^ 2) := by
      rw [Matrix.det_fin_three (Matrix.of (fun i j : Fin 3 => augment (triangle e j) i))]
      norm_num [triangle, augment]
      ring
    _ = _ := by rw [he, mul_one]

lemma triangle_invertible {e : Plane} (he : e 0 ^ 2 + e 1 ^ 2 = 1) :
    (columnOperator (fun i => augment (triangle e i))).IsInvertible := by
  let M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (fun i j => augment (triangle e j) i)
  have hd : IsUnit M.det := by
    rw [triangle_determinant he]
    exact isUnit_iff_ne_zero.mpr (by positivity)
  have hm : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr hd
  have heval (x : Moments) : M.mulVec x = columnOperator (fun i => augment (triangle e i)) x := by
    ext i
    simp [M, Matrix.mulVec, dotProduct, columnOperator, mul_comm]
  have hi : Function.Injective (columnOperator (fun i => augment (triangle e i))) := by
    intro x y h
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hm)
    simpa only [heval] using h
  have hs := LinearMap.surjective_of_injective
    (f := (columnOperator (fun i => augment (triangle e i))).toLinearMap) hi
  exact ⟨(LinearEquiv.ofBijective _ ⟨hi, hs⟩).toContinuousLinearEquiv, rfl⟩

lemma triangle_unit {e : Plane} (he : e 0 ^ 2 + e 1 ^ 2 = 1) (i : Fin 3) :
    (triangle e i) 0 ^ 2 + (triangle e i) 1 ^ 2 = 1 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases i
  · exact he
  · change (-e 0 / 2 - Real.sqrt 3 / 2 * e 1) ^ 2 +
      (-e 1 / 2 + Real.sqrt 3 / 2 * e 0) ^ 2 = 1
    ring_nf
    rw [hs]
    nlinarith [he]
  · change (-e 0 / 2 + Real.sqrt 3 / 2 * e 1) ^ 2 +
      (-e 1 / 2 - Real.sqrt 3 / 2 * e 0) ^ 2 = 1
    ring_nf
    rw [hs]
    nlinarith [he]

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LoopDensityDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radial coordinates and angular representatives for the interior density construction. -/
noncomputable section
open Set

namespace ClosedSurfaceR4.LoopDensity

lemma radial_representation {c : Plane} (hc : c 0 ^ 2 + c 1 ^ 2 < 1) :
    ∃ (r : ℝ) (e : Plane), 0 ≤ r ∧ r < 1 ∧ e 0 ^ 2 + e 1 ^ 2 = 1 ∧ c = r • e := by
  let r := Real.sqrt (c 0 ^ 2 + c 1 ^ 2)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = c 0 ^ 2 + c 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hr1 : r < 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by positivity) hc
  by_cases hz : r = 0
  · have hc0 : c 0 = 0 := by nlinarith
    have hc1 : c 1 = 0 := by nlinarith
    refine ⟨0, ![1, 0], le_rfl, zero_lt_one, by norm_num, ?_⟩
    ext i
    fin_cases i <;> simp [hc0, hc1]
  · let e : Plane := fun i => c i / r
    refine ⟨r, e, hr, hr1, ?_, ?_⟩
    · change (c 0 / r) ^ 2 + (c 1 / r) ^ 2 = 1
      field_simp
      nlinarith [hr2]
    · ext i
      change c i = r * (c i / r)
      field_simp

lemma unit_direction_angle {e : Plane} (he : e 0 ^ 2 + e 1 ^ 2 = 1) :
    ∃ β ∈ Icc (-Real.pi) Real.pi, Real.cos β = e 0 ∧ Real.sin β = e 1 := by
  let z : ℂ := ⟨e 0, e 1⟩
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    change Real.sqrt (e 0 ^ 2 + e 1 ^ 2) = 1
    rw [he, Real.sqrt_one]
  have hz : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    norm_num at hn
  refine ⟨Complex.arg z, ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩, ?_, ?_⟩
  · rw [Complex.cos_arg hz, hn, div_one]
  · rw [Complex.sin_arg, hn, div_one]

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_InteriorVelocityPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The interior oscillatory path covers the whole velocity circle. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.LoopDensity

/-- All circle directions occur away from the endpoints and turning points. -/
theorem interiorPath_covers {A h : ℝ} (hA : Real.pi + |h| < A)
    {e : Plane} (he : e 0 ^ 2 + e 1 ^ 2 = 1) :
    ∃ t ∈ Ioo (0 : ℝ) 1, interiorPath A h t = e := by
  obtain ⟨β, hβ, hcos, hsin⟩ := unit_direction_angle he
  have hAp : 0 < A := lt_of_lt_of_le Real.pi_pos (by linarith [abs_nonneg h])
  have hlo : -1 < (β - h) / A := (lt_div_iff₀ hAp).mpr (by linarith [le_abs_self h, hβ.1])
  have hhi : (β - h) / A < 1 := (div_lt_iff₀ hAp).mpr (by linarith [neg_abs_le h, hβ.2])
  let x := Real.arccos ((β - h) / A)
  have hx0 : 0 < x := Real.arccos_pos.mpr hhi
  have hxπ : x < Real.pi := Real.arccos_lt_pi.mpr hlo
  have hp : 0 < 2 * Real.pi := by positivity
  refine ⟨x / (2 * Real.pi), ⟨div_pos hx0 hp, (div_lt_one hp).mpr (by linarith [Real.pi_pos])⟩, ?_⟩
  have hcancel : 2 * Real.pi * (x / (2 * Real.pi)) = x := by field_simp
  have hcx : Real.cos x = (β - h) / A := Real.cos_arccos hlo.le hhi.le
  have harg : h + A * ((β - h) / A) = β := by field_simp <;> ring
  ext i
  fin_cases i <;> simp [interiorPath, hcancel, hcx, harg, hcos, hsin]

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_InteriorDensityLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth local positive averaging densities for the interior velocity path. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.LoopDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

/-- Circle coverage and a target in the open disk suffice for the local density construction. -/
theorem positive_density_near_of_circle_coverage
    {p : B → ℝ → Plane} {c : B → Plane}
    (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2)) (hc : ContDiff ℝ ∞ c)
    {b₀ : B} (hc₀ : c b₀ 0 ^ 2 + c b₀ 1 ^ 2 < 1)
    (hcover : ∀ e : Plane, e 0 ^ 2 + e 1 ^ 2 = 1 → ∃ t ∈ Ioo (0 : ℝ) 1, p b₀ t = e) :
    ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧ ∃ ρ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ ρ (U ×ˢ univ) ∧
      (∀ b ∈ U, ∀ t, 0 < ρ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
      ∀ b ∈ U, (∫ t in 0..1, ρ (b, t) • augment (p b t)) = augment (c b) := by
  obtain ⟨r, e, hr, hr1, he, hce⟩ := radial_representation hc₀
  choose t ht hpt using fun i : Fin 3 => hcover (triangle e i) (triangle_unit he i)
  have hcols : (fun i => augment (p b₀ (t i))) = fun i => augment (triangle e i) := by
    funext i
    rw [hpt i]
  have hM : (columnOperator (fun i => augment (p b₀ (t i)))).IsInvertible := by
    rw [hcols]
    exact triangle_invertible he
  have hbary : columnOperator (fun i => augment (p b₀ (t i))) (triangleWeights r) = augment (c b₀) := by
    rw [hcols, triangle_barycenter, ← hce]
  have hp₀ : Continuous (p b₀) := hp.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨ψ, hψ, hper, hn, _hm, ε, hε, hMψ, hw⟩ :=
    select_positive_moment_bumps hp₀ ht hM (triangleWeights_pos hr hr1) hbary
  exact exists_positive_density_near hp hc hψ hn hper hε hMψ hw

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_LoopDensityArcTriangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nondegenerate three-point barycenter inside a symmetric circular arc. -/
noncomputable section
open scoped Matrix BigOperators

namespace ClosedSurfaceR4.LoopDensity

lemma arcWeights_pos {q m : ℝ} (hqm : q < m) (hm : m < 1) (i : Fin 3) :
    0 < arcWeights q m i := by
  have hq : 0 < 1 - q := by linarith
  have hnum : 0 < m - q := sub_pos.mpr hqm
  have hm' : 0 < 1 - m := sub_pos.mpr hm
  fin_cases i
  · exact div_pos hnum hq
  · exact div_pos hm' (mul_pos (by norm_num) hq)
  · exact div_pos hm' (mul_pos (by norm_num) hq)

lemma arcTriangle_barycenter {q m : ℝ} (hq : q ≠ 1) (s : ℝ) :
    columnOperator (fun i => augment (arcTriangle q s i)) (arcWeights q m) = augment ![m, 0] := by
  have hd : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  ext i
  fin_cases i <;> simp [columnOperator, arcTriangle, arcWeights, augment, Fin.sum_univ_three] <;>
    field_simp [hd] <;> ring

lemma arcTriangle_invertible {q s : ℝ} (hq : q ≠ 1) (hs : s ≠ 0) :
    (columnOperator (fun i => augment (arcTriangle q s i))).IsInvertible := by
  let M : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of (fun i j => augment (arcTriangle q s j) i)
  have hdet : M.det = 2 * s * (1 - q) := by
    rw [Matrix.det_fin_three M]
    norm_num [M, arcTriangle, augment]
    ring
  have hd : M.det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hs) (sub_ne_zero.mpr (Ne.symm hq))
  have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hd)
  have heval (x : Moments) : M.mulVec x = columnOperator (fun i => augment (arcTriangle q s i)) x := by
    ext i
    simp [M, Matrix.mulVec, dotProduct, columnOperator, mul_comm]
  have hi : Function.Injective (columnOperator (fun i => augment (arcTriangle q s i))) := by
    intro x y h
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hunit)
    simpa only [heval] using h
  have hsurj := LinearMap.surjective_of_injective
    (f := (columnOperator (fun i => augment (arcTriangle q s i))).toLinearMap) hi
  exact ⟨(LinearEquiv.ofBijective _ ⟨hi, hsurj⟩).toContinuousLinearEquiv, rfl⟩

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ArcDensityLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive averaging densities when a symmetric circular arc surrounds the target. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.LoopDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

theorem positive_density_near_of_arc_coverage
    {p : B → ℝ → Plane} {c : B → Plane}
    (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2)) (hc : ContDiff ℝ ∞ c)
    {b₀ : B} {m A : ℝ} (hc₀ : c b₀ = ![m, 0]) (hm : -1 < m) (hm1 : m < 1)
    (hA : Real.arccos m < A)
    (hcover : ∀ β ∈ Ioo (-A) A,
      ∃ t ∈ Ioo (0 : ℝ) 1, p b₀ t = ![Real.cos β, Real.sin β]) :
    ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧ ∃ ρ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ ρ (U ×ˢ univ) ∧
      (∀ b ∈ U, ∀ t, 0 < ρ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
      ∀ b ∈ U, (∫ t in 0..1, ρ (b, t) • augment (p b t)) = augment (c b) := by
  let β := (Real.arccos m + min A Real.pi) / 2
  have hmin : Real.arccos m < min A Real.pi :=
    lt_min hA (Real.arccos_lt_pi.mpr hm)
  have hβlo : Real.arccos m < β := by dsimp [β] <;> linarith
  have hβhi : β < min A Real.pi := by dsimp [β] <;> linarith
  have hβpos : 0 < β := lt_of_le_of_lt (Real.arccos_nonneg m) hβlo
  have hβA : β < A := lt_of_lt_of_le hβhi (min_le_left _ _)
  have hβπ : β < Real.pi := lt_of_lt_of_le hβhi (min_le_right _ _)
  have hcos : Real.cos β < m := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (Real.arccos_nonneg m) hβπ.le hβlo
    rwa [Real.cos_arccos hm.le hm1.le] at hh
  have hAp : 0 < A := lt_trans hβpos hβA
  obtain ⟨t₀, ht₀, hp₀⟩ := hcover 0 (by constructor <;> linarith)
  obtain ⟨t₁, ht₁, hp₁⟩ := hcover β ⟨by linarith, hβA⟩
  obtain ⟨t₂, ht₂, hp₂⟩ := hcover (-β) ⟨by linarith, by linarith⟩
  let t : Fin 3 → ℝ := ![t₀, t₁, t₂]
  have ht (i : Fin 3) : t i ∈ Ioo (0 : ℝ) 1 := by
    fin_cases i
    · exact ht₀
    · exact ht₁
    · exact ht₂
  have hpt (i : Fin 3) : p b₀ (t i) = arcTriangle (Real.cos β) (Real.sin β) i := by
    fin_cases i
    · simpa [t, arcTriangle] using hp₀
    · exact hp₁
    · simpa [t, arcTriangle, Real.cos_neg, Real.sin_neg] using hp₂
  have hcols : (fun i => augment (p b₀ (t i))) =
      fun i => augment (arcTriangle (Real.cos β) (Real.sin β) i) := by
    funext i
    rw [hpt]
  have hq : Real.cos β ≠ 1 := ne_of_lt (lt_trans hcos hm1)
  have hM : (columnOperator (fun i => augment (p b₀ (t i)))).IsInvertible := by
    rw [hcols]
    exact arcTriangle_invertible hq (Real.sin_pos_of_pos_of_lt_pi hβpos hβπ).ne'
  have hbary : columnOperator (fun i => augment (p b₀ (t i)))
      (arcWeights (Real.cos β) m) = augment (c b₀) := by
    rw [hcols, arcTriangle_barycenter hq, hc₀]
  have hpcont : Continuous (p b₀) := hp.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨ψ, hψ, hper, hn, _hmass, ε, hε, hMψ, hw⟩ :=
    select_positive_moment_bumps hpcont ht hM (arcWeights_pos hcos hm1) hbary
  exact exists_positive_density_near hp hc hψ hn hper hε hMψ hw

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BlendedVelocityPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth transition paths and their strict convex-hull margin. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]

lemma blendedPath_smooth {a A s h : B → ℝ}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun z : B × ℝ => blendedPath (a z.1) (A z.1) (s z.1) (h z.1) z.2) := by
  have hangle : ContDiff ℝ ∞ (fun z : B × ℝ =>
      blendedAngle (a z.1) (A z.1) (s z.1) (h z.1) (2 * Real.pi * z.2)) := by
    have hb : ContDiff ℝ ∞ (fun z : B × ℝ => baseAngle (a z.1) (2 * Real.pi * z.2)) :=
      baseAngle_smooth.comp ((ha.comp contDiff_fst).prodMk (contDiff_const.mul contDiff_snd))
    exact ((hh.comp contDiff_fst).add
      ((contDiff_const.sub (hs.comp contDiff_fst)).mul hb)).add
        ((hs.comp contDiff_fst).mul ((hA.comp contDiff_fst).mul
          (contDiff_const.mul contDiff_snd).cos))
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact hangle.cos
  · exact hangle.sin

lemma blendedPath_covers {a A s β : ℝ}
    (hβ : β ∈ Ioo (-((1 - s) * (2 * Real.arctan a) + s * A))
      ((1 - s) * (2 * Real.arctan a) + s * A)) :
    ∃ t ∈ Ioo (0 : ℝ) 1, blendedPath a A s 0 t = ![Real.cos β, Real.sin β] := by
  have hf : Continuous (blendedAngle a A s 0) := by
    unfold blendedAngle baseAngle
    fun_prop
  have hmem : β ∈ Icc (blendedAngle a A s 0 Real.pi) (blendedAngle a A s 0 0) := by
    rw [blendedAngle_pi, blendedAngle_zero]
    simpa only [zero_add, zero_sub] using ⟨hβ.1.le, hβ.2.le⟩
  obtain ⟨u, hu, heq⟩ := intermediate_value_Icc' Real.pi_pos.le hf.continuousOn hmem
  have hu0 : 0 < u := by
    by_contra hn
    have hz : u = 0 := le_antisymm (le_of_not_gt hn) hu.1
    rw [hz, blendedAngle_zero, zero_add] at heq
    linarith [hβ.2]
  have huπ : u < Real.pi := by
    by_contra hn
    have hz : u = Real.pi := le_antisymm hu.2 (le_of_not_gt hn)
    rw [hz, blendedAngle_pi, zero_sub] at heq
    linarith [hβ.1]
  refine ⟨u / (2 * Real.pi), ⟨div_pos hu0 (by positivity), ?_⟩, ?_⟩
  · apply (div_lt_one (by positivity : 0 < 2 * Real.pi)).mpr
    linarith [Real.pi_pos]
  · have hsimp : 2 * Real.pi * (u / (2 * Real.pi)) = u := by field_simp
    simp only [blendedPath, hsimp, heq]

lemma collar_mean_arc_margin {a : ℝ} (ha : 0 < a) :
    Real.arccos ((1 - a ^ 2 / 2) / (1 + a ^ 2 / 2)) < 2 * Real.arctan a := by
  have hd : 0 < 1 + a ^ 2 := by positivity
  have hd' : 0 < 1 + a ^ 2 / 2 := by positivity
  have hsq : 0 < a ^ 2 := sq_pos_of_pos ha
  have hcos : Real.cos (2 * Real.arctan a) = (1 - a ^ 2) / (1 + a ^ 2) := by
    simpa [baseAngle, arcX] using cos_baseAngle a 0
  have hlt : (1 - a ^ 2) / (1 + a ^ 2) < (1 - a ^ 2 / 2) / (1 + a ^ 2 / 2) := by
    apply (div_lt_div_iff₀ hd hd').mpr
    nlinarith
  have hangle0 : 0 ≤ 2 * Real.arctan a := by
    have := Real.arctan_pos.mpr ha
    positivity
  have hangleπ : 2 * Real.arctan a ≤ Real.pi := by
    have := Real.arctan_lt_pi_div_two a
    linarith
  have hm1 : (1 - a ^ 2 / 2) / (1 + a ^ 2 / 2) ≤ 1 := by
    apply (div_le_one hd').mpr
    linarith
  have hleft : -1 ≤ Real.cos (2 * Real.arctan a) := Real.neg_one_le_cos _
  have hh := Real.arccos_lt_arccos hleft (hcos ▸ hlt) hm1
  rwa [Real.arccos_cos hangle0 hangleπ] at hh

theorem blended_positive_density_near [FiniteDimensional ℝ B]
    {a A s h : B → ℝ} {c : B → LoopDensity.Plane}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hh : ContDiff ℝ ∞ h) (hc : ContDiff ℝ ∞ c)
    {b₀ : B} (ha₀ : 0 < a b₀) (hA₀ : 2 * Real.arctan (a b₀) ≤ A b₀)
    (hs₀ : s b₀ ∈ Icc (0 : ℝ) 1) (hh₀ : h b₀ = 0)
    (hc₀ : c b₀ = ![(1 - a b₀ ^ 2 / 2) / (1 + a b₀ ^ 2 / 2), 0]) :
    ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧ ∃ ρ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ ρ (U ×ˢ univ) ∧
      (∀ b ∈ U, ∀ t, 0 < ρ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
      ∀ b ∈ U, (∫ t in 0..1, ρ (b, t) •
        LoopDensity.augment (blendedPath (a b) (A b) (s b) (h b) t)) = LoopDensity.augment (c b) := by
  have hd : 0 < 1 + a b₀ ^ 2 / 2 := by positivity
  have hsq : 0 < a b₀ ^ 2 := sq_pos_of_pos ha₀
  have hml : -1 < (1 - a b₀ ^ 2 / 2) / (1 + a b₀ ^ 2 / 2) := by
    apply (lt_div_iff₀ hd).mpr
    linarith
  have hmu : (1 - a b₀ ^ 2 / 2) / (1 + a b₀ ^ 2 / 2) < 1 := by
    apply (div_lt_one hd).mpr
    linarith
  have hamplitude : 2 * Real.arctan (a b₀) ≤
      (1 - s b₀) * (2 * Real.arctan (a b₀)) + s b₀ * A b₀ := by
    nlinarith [mul_nonneg hs₀.1 (sub_nonneg.mpr hA₀)]
  apply LoopDensity.positive_density_near_of_arc_coverage (blendedPath_smooth ha hA hs hh)
    hc hc₀ hml hmu (lt_of_lt_of_le (collar_mean_arc_margin ha₀) hamplitude)
  intro β hβ
  rw [hh₀]
  exact blendedPath_covers hβ

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarVelocityPeriod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the explicit collar arc to the unit period used by the corrector. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity
open CovarianceCorrector SmoothPeriodicCalculus

lemma integral_rescale (f : ℝ → ℝ) :
    (∫ t in 0..1, f (2 * Real.pi * t)) = circleMean f := by
  rw [intervalIntegral.integral_comp_mul_left f (by positivity)]
  simp only [mul_zero, mul_one, smul_eq_mul, circleMean]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarDensityMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact unit-period moment equations for the prescribed collar density. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

lemma unitDensity_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => unitDensity z.1 z.2) :=
  density_smooth.comp (contDiff_fst.prodMk (contDiff_const.mul contDiff_snd))

lemma unitDensity_pos (a t : ℝ) : 0 < unitDensity a t := density_pos a _

lemma unitDensity_periodic (a : ℝ) : Function.Periodic (unitDensity a) 1 := by
  intro t
  unfold unitDensity
  rw [mul_add, mul_one]
  exact density_periodic a _

lemma blendedPath_collar (a A t : ℝ) :
    blendedPath a A 0 0 t = ![arcX a (2 * Real.pi * t), arcY a (2 * Real.pi * t)] := by
  simp [blendedPath, blendedAngle, cos_baseAngle, sin_baseAngle]

lemma collar_density_moments (a A : ℝ) :
    (∫ t in 0..1, unitDensity a t • LoopDensity.augment (blendedPath a A 0 0 t)) =
      LoopDensity.augment ![(1 - a ^ 2 / 2) / (1 + a ^ 2 / 2), 0] := by
  let f : ℝ → LoopDensity.Moments := fun t =>
    unitDensity a t • LoopDensity.augment (blendedPath a A 0 0 t)
  have hp : Continuous (blendedPath a A 0 0) := by
    have hang : Continuous (blendedAngle a A 0 0) := by
      unfold blendedAngle baseAngle
      fun_prop
    have hscaled : Continuous (fun t : ℝ => blendedAngle a A 0 0 (2 * Real.pi * t)) :=
      hang.comp (continuous_const.mul continuous_id)
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.continuous_cos.comp hscaled
    · exact Real.continuous_sin.comp hscaled
  have hρ : Continuous (unitDensity a) :=
    unitDensity_smooth.continuous.comp (continuous_const.prodMk continuous_id)
  have hf : Continuous f :=
    hρ.smul (LoopDensity.augment_continuous.comp hp)
  have heval (i : Fin 3) : (∫ t in 0..1, f t) i = ∫ t in 0..1, f t i :=
    ((ContinuousLinearMap.proj i : LoopDensity.Moments →L[ℝ] ℝ).intervalIntegral_comp_comm
      (hf.intervalIntegrable 0 1)).symm
  change (∫ t in 0..1, f t) = _
  ext i
  rw [heval]
  fin_cases i
  · change (∫ t in 0..1, unitDensity a t * 1) = 1
    simp only [mul_one, unitDensity]
    rw [integral_rescale, mean_density]
  · change (∫ t in 0..1, unitDensity a t * (blendedPath a A 0 0 t) 0) = _
    simp only [blendedPath_collar, Matrix.cons_val_zero, unitDensity]
    exact (integral_rescale (fun u => density a u * arcX a u)).trans (mean_density_arcX a)
  · change (∫ t in 0..1, unitDensity a t * (blendedPath a A 0 0 t) 1) = 0
    simp only [blendedPath_collar, Matrix.cons_val_one, Matrix.cons_val_zero, unitDensity]
    exact (integral_rescale (fun u => density a u * arcY a u)).trans (mean_density_arcY a)

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BlendedDensityCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive densities through the collar, transition, and circle-covering interior. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

theorem blended_density_near_interior
    {a A s h : B → ℝ} {c : B → LoopDensity.Plane}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hh : ContDiff ℝ ∞ h) (hc : ContDiff ℝ ∞ c)
    {b₀ : B} (hs₀ : s b₀ = 1) (hA₀ : Real.pi + |h b₀| < A b₀)
    (hc₀ : c b₀ 0 ^ 2 + c b₀ 1 ^ 2 < 1) :
    ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧ ∃ ρ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ ρ (U ×ˢ univ) ∧
      (∀ b ∈ U, ∀ t, 0 < ρ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
      ∀ b ∈ U, (∫ t in 0..1, ρ (b, t) •
        LoopDensity.augment (blendedPath (a b) (A b) (s b) (h b) t)) = LoopDensity.augment (c b) := by
  apply LoopDensity.positive_density_near_of_circle_coverage
    (blendedPath_smooth ha hA hs hh) hc hc₀
  intro e he
  obtain ⟨t, ht, hpt⟩ := LoopDensity.interiorPath_covers hA₀ he
  exact ⟨t, ht, by simpa [blendedPath, blendedAngle, hs₀, LoopDensity.interiorPath] using hpt⟩

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ShiftedDensityCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform positive densities for small translations of the blended angle.
The allowable translation size follows from compactness after constructing
smooth solutions near zero translation. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

theorem shifted_density_compact {a A s : B → ℝ} {c : B → LoopDensity.Plane}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hc : ContDiff ℝ ∞ c)
    {K : Set B} (hK : IsCompact K)
    (hshape : ∀ b ∈ K,
      (0 < a b ∧ 2 * Real.arctan (a b) ≤ A b ∧ s b ∈ Icc (0 : ℝ) 1 ∧
        c b = ![(1 - a b ^ 2 / 2) / (1 + a b ^ 2 / 2), 0]) ∨
      (s b = 1 ∧ Real.pi < A b ∧ c b 0 ^ 2 + c b 1 ^ 2 < 1)) :
    ∃ W : Set B, IsOpen W ∧ K ⊆ W ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ ρ : (B × ℝ) × ℝ → ℝ,
        ContDiffOn ℝ ∞ ρ ((W ×ˢ Metric.ball (0 : ℝ) ε) ×ˢ univ) ∧
        (∀ b ∈ W, ∀ h, |h| < ε → ∀ t, 0 < ρ ((b, h), t)) ∧
        (∀ b h, Function.Periodic (fun t => ρ ((b, h), t)) 1) ∧
        ∀ b ∈ W, ∀ h, |h| < ε →
          (∫ t in 0..1, ρ ((b, h), t) •
            LoopDensity.augment (blendedPath (a b) (A b) (s b) h t)) =
              LoopDensity.augment (c b) := by
  classical
  let a' : B × ℝ → ℝ := fun p => a p.1
  let A' : B × ℝ → ℝ := fun p => A p.1
  let s' : B × ℝ → ℝ := fun p => s p.1
  let c' : B × ℝ → LoopDensity.Plane := fun p => c p.1
  have ha' : ContDiff ℝ ∞ a' := ha.comp contDiff_fst
  have hA' : ContDiff ℝ ∞ A' := hA.comp contDiff_fst
  have hs' : ContDiff ℝ ∞ s' := hs.comp contDiff_fst
  have hc' : ContDiff ℝ ∞ c' := hc.comp contDiff_fst
  let J := {p : B × ℝ // p ∈ K ×ˢ ({0} : Set ℝ)}
  have hlocal (p : J) : ∃ V : Set (B × ℝ), IsOpen V ∧ p.val ∈ V ∧
      ∃ ρ : (B × ℝ) × ℝ → ℝ, ContDiffOn ℝ ∞ ρ (V ×ˢ univ) ∧
        (∀ b ∈ V, ∀ t, 0 < ρ (b, t)) ∧
        (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
        ∀ b ∈ V, (∫ t in 0..1, ρ (b, t) • LoopDensity.augment
          (blendedPath (a' b) (A' b) (s' b) b.2 t)) = LoopDensity.augment (c' b) := by
    have hp0 : p.val.2 = 0 := p.property.2
    rcases hshape p.val.1 p.property.1 with ht | hi
    · exact blended_positive_density_near ha' hA' hs' contDiff_snd hc'
        ht.1 ht.2.1 ht.2.2.1 hp0 ht.2.2.2
    · apply blended_density_near_interior ha' hA' hs' contDiff_snd hc' hi.1 _ hi.2.2
      simpa only [hp0, abs_zero, add_zero] using hi.2.1
  choose V hV hpV ρ hρ hpos hper hmom using hlocal
  have hcover : K ×ˢ ({0} : Set ℝ) ⊆ ⋃ p : J, V p := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hpV ⟨p, hp⟩⟩
  obtain ⟨U, hU, hKU, σ, hσ, hσpos, hσper, hσmom, _⟩ :=
    LoopDensity.compact_patch_densities
      (blendedPath_smooth ha' hA' hs' contDiff_snd) V hV ρ hρ hpos hper hmom
      (hK.prod isCompact_singleton) hcover
  obtain ⟨W, Z, hW, hZ, hKW, h0Z, hWZ⟩ :=
    generalized_tube_lemma hK isCompact_singleton hU hKU
  obtain ⟨ε, hε, hεZ⟩ := Metric.isOpen_iff.mp hZ 0 (h0Z (mem_singleton 0))
  have htube : W ×ˢ Metric.ball (0 : ℝ) ε ⊆ U :=
    (prod_mono Subset.rfl hεZ).trans hWZ
  refine ⟨W, hW, hKW, ε, hε, σ, hσ.mono (prod_mono htube Subset.rfl), ?_, ?_, ?_⟩
  · intro b hb h hh t
    exact hσpos (b, h) (htube ⟨hb, by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hh⟩) t
  · intro b h
    exact hσper (b, h)
  · intro b hb h hh
    exact hσmom (b, h) (htube ⟨hb, by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hh⟩)

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LoopDensityMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extract mass one and the vector mean from the three augmented moments. -/
noncomputable section

namespace ClosedSurfaceR4.LoopDensity

theorem mass_and_mean {ρ : ℝ → ℝ} {p : ℝ → Plane} {c : Plane}
    (hρ : Continuous ρ) (hp : Continuous p)
    (hm : (∫ t in 0..1, ρ t • augment (p t)) = augment c) :
    (∫ t in 0..1, ρ t) = 1 ∧ (∫ t in 0..1, ρ t • p t) = c := by
  have hi : IntervalIntegrable (fun t => ρ t • augment (p t)) MeasureTheory.volume 0 1 :=
    (hρ.smul (augment_continuous.comp hp)).intervalIntegrable 0 1
  have hpi : IntervalIntegrable (fun t => ρ t • p t) MeasureTheory.volume 0 1 :=
    (hρ.smul hp).intervalIntegrable 0 1
  have hcoord (i : Fin 3) :
      (∫ t in 0..1, (ρ t • augment (p t)) i) = (augment c) i := by
    have he := congrArg (fun x : Moments => x i) hm
    have hev : (∫ t in 0..1, ρ t • augment (p t)) i =
        ∫ t in 0..1, (ρ t • augment (p t)) i :=
      ((ContinuousLinearMap.proj i : Moments →L[ℝ] ℝ).intervalIntegral_comp_comm hi).symm
    rwa [hev] at he
  constructor
  · simpa [augment] using hcoord 0
  · ext i
    have hev : (∫ t in 0..1, ρ t • p t) i = ∫ t in 0..1, (ρ t • p t) i :=
      ((ContinuousLinearMap.proj i : Plane →L[ℝ] ℝ).intervalIntegral_comp_comm hpi).symm
    rw [hev]
    fin_cases i
    · simpa [augment] using hcoord 1
    · simpa [augment] using hcoord 2

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ShiftedDensityPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pull back the universal translation-dependent density along any small smooth
translation. Its derivatives may be arbitrarily large. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

theorem small_shift_density {a A s : B → ℝ} {c : B → LoopDensity.Plane}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hc : ContDiff ℝ ∞ c)
    {K : Set B} (hK : IsCompact K)
    (hshape : ∀ b ∈ K,
      (0 < a b ∧ 2 * Real.arctan (a b) ≤ A b ∧ s b ∈ Icc (0 : ℝ) 1 ∧
        c b = ![(1 - a b ^ 2 / 2) / (1 + a b ^ 2 / 2), 0]) ∨
      (s b = 1 ∧ Real.pi < A b ∧ c b 0 ^ 2 + c b 1 ^ 2 < 1)) :
    ∃ W : Set B, IsOpen W ∧ K ⊆ W ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ h : B → ℝ, ContDiff ℝ ∞ h → (∀ b, |h b| < ε) →
        ∃ σ : B × ℝ → ℝ, ContDiffOn ℝ ∞ σ (W ×ˢ univ) ∧
          (∀ b ∈ W, ∀ t, 0 < σ (b, t)) ∧
          (∀ b, Function.Periodic (fun t => σ (b, t)) 1) ∧
          (∀ b ∈ W, (∫ t in 0..1, σ (b, t)) = 1) ∧
          ∀ b ∈ W, (∫ t in 0..1, σ (b, t) •
            blendedPath (a b) (A b) (s b) (h b) t) = c b := by
  obtain ⟨W, hW, hKW, ε, hε, ρ, hρ, hpos, hper, hmom⟩ :=
    shifted_density_compact ha hA hs hc hK hshape
  refine ⟨W, hW, hKW, ε, hε, ?_⟩
  intro h hh hsmall
  let σ : B × ℝ → ℝ := fun z => ρ ((z.1, h z.1), z.2)
  have hσ : ContDiffOn ℝ ∞ σ (W ×ˢ univ) := by
    apply hρ.comp
      (((contDiff_fst.prodMk (hh.comp contDiff_fst)).prodMk contDiff_snd).contDiffOn)
    intro z hz
    exact ⟨⟨hz.1, by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, Function.comp_apply] using hsmall z.1⟩, hz.2⟩
  have hσpos (b : B) (hb : b ∈ W) (t : ℝ) : 0 < σ (b, t) :=
    hpos b hb (h b) (hsmall b) t
  have hσmom (b : B) (hb : b ∈ W) :
      (∫ t in 0..1, σ (b, t) •
        LoopDensity.augment (blendedPath (a b) (A b) (s b) (h b) t)) =
          LoopDensity.augment (c b) := hmom b hb (h b) (hsmall b)
  have hσboth (b : B) (hb : b ∈ W) := LoopDensity.mass_and_mean
    (LocalPeriodicCalculus.smooth_slice hW hσ hb).continuous
    ((blendedPath_smooth ha hA hs hh).continuous.comp
      (continuous_const.prodMk continuous_id)) (hσmom b hb)
  exact ⟨σ, hσ, hσpos, (fun b => hper b (h b)),
    (fun b hb => (hσboth b hb).1), (fun b hb => (hσboth b hb).2)⟩

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LoopDensityMomentConverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recombine mass and vector mean into the augmented linear moment equation. -/
noncomputable section

namespace ClosedSurfaceR4.LoopDensity

lemma augmented_moments {ρ : ℝ → ℝ} {p : ℝ → Plane} {c : Plane}
    (hρ : Continuous ρ) (hp : Continuous p)
    (hmass : (∫ t in 0..1, ρ t) = 1)
    (hmean : (∫ t in 0..1, ρ t • p t) = c) :
    (∫ t in 0..1, ρ t • augment (p t)) = augment c := by
  have hi : IntervalIntegrable (fun t => ρ t • augment (p t)) MeasureTheory.volume 0 1 :=
    (hρ.smul (augment_continuous.comp hp)).intervalIntegrable 0 1
  have hpi : IntervalIntegrable (fun t => ρ t • p t) MeasureTheory.volume 0 1 :=
    (hρ.smul hp).intervalIntegrable 0 1
  have hc (i : Fin 2) : (∫ t in 0..1, (ρ t • p t) i) = c i := by
    have he := congrArg (fun x : Plane => x i) hmean
    have hev : (∫ t in 0..1, ρ t • p t) i = ∫ t in 0..1, (ρ t • p t) i :=
      ((ContinuousLinearMap.proj i : Plane →L[ℝ] ℝ).intervalIntegral_comp_comm hpi).symm
    rwa [hev] at he
  ext i
  have hev : (∫ t in 0..1, ρ t • augment (p t)) i =
      ∫ t in 0..1, (ρ t • augment (p t)) i :=
    ((ContinuousLinearMap.proj i : Moments →L[ℝ] ℝ).intervalIntegral_comp_comm hi).symm
  rw [hev]
  fin_cases i
  · simpa [augment] using hmass
  · simpa [augment] using hc 0
  · simpa [augment] using hc 1

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ShiftedCollarDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the mean-adjusting density for the whole collar/interior family,
allowing any sufficiently small smooth translation supported off the collar. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

private lemma path_continuous (a A s h : ℝ) : Continuous (blendedPath a A s h) := by
  have hb : Continuous (fun t : ℝ => baseAngle a (2 * Real.pi * t)) := by
    unfold baseAngle
    fun_prop
  have hg : Continuous (fun t : ℝ => blendedAngle a A s h (2 * Real.pi * t)) := by
    unfold blendedAngle
    fun_prop
  apply continuous_pi
  intro i
  fin_cases i
  · exact Real.continuous_cos.comp hg
  · exact Real.continuous_sin.comp hg

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

theorem small_shift_collar_density_oai {a A s : B → ℝ} {c : B → LoopDensity.Plane}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hc : ContDiff ℝ ∞ c)
    {U C K : Set B} (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hcollar : ∀ b ∈ U, s b = 0 ∧ c b = ![(1 - a b ^ 2 / 2) / (1 + a b ^ 2 / 2), 0])
    (hrest : ∀ b ∈ K \ U,
      (0 < a b ∧ 2 * Real.arctan (a b) ≤ A b ∧ s b ∈ Icc (0 : ℝ) 1 ∧
        c b = ![(1 - a b ^ 2 / 2) / (1 + a b ^ 2 / 2), 0]) ∨
      (s b = 1 ∧ Real.pi < A b ∧ c b 0 ^ 2 + c b 1 ^ 2 < 1)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : B → ℝ, ContDiff ℝ ∞ h →
      (∀ b, |h b| < ε) → (∀ b ∈ U, h b = 0) →
      ∃ V : Set B, IsOpen V ∧ K ⊆ V ∧ ∃ ρ : B × ℝ → ℝ,
        ContDiffOn ℝ ∞ ρ (V ×ˢ univ) ∧
        (∀ b ∈ V, ∀ t, 0 < ρ (b, t)) ∧
        (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
        (∀ b ∈ V, (∫ t in 0..1, ρ (b, t) •
          LoopDensity.augment (blendedPath (a b) (A b) (s b) (h b) t)) =
            LoopDensity.augment (c b)) ∧
        ∀ b ∈ V ∩ C, ∀ t, ρ (b, t) = unitDensity (a b) t := by
  obtain ⟨W, hW, hKW, ε, hε, hsol⟩ := small_shift_density ha hA hs hc (hK.diff hU) hrest
  refine ⟨ε, hε, ?_⟩
  intro h hh hsmall hzero
  obtain ⟨σ, hσ, hσpos, hσper, hσmass, hσmean⟩ := hsol h hh hsmall
  apply LoopDensity.positive_density_compact_preserving
    (blendedPath_smooth ha hA hs hh) hU hC hCU hK (fun z => unitDensity (a z.1) z.2)
  · exact (unitDensity_smooth.comp ((ha.comp contDiff_fst).prodMk contDiff_snd)).contDiffOn
  · intro b _ t
    exact unitDensity_pos _ _
  · intro b
    exact unitDensity_periodic (a b)
  · intro b hb
    obtain ⟨hsb, hcb⟩ := hcollar b hb
    simp only [hsb, hzero b hb, hcb]
    exact collar_density_moments _ _
  · intro b hb
    refine ⟨W, hW, hKW hb, σ, hσ, hσpos, hσper, ?_⟩
    intro x hx
    exact LoopDensity.augmented_moments (ρ := fun t => σ (x, t))
      (p := fun t => blendedPath (a x) (A x) (s x) (h x) t) (c := c x)
      (LocalPeriodicCalculus.smooth_slice hW hσ hx).continuous (path_continuous (a x) (A x) (s x) (h x))
      (hσmass x hx) (hσmean x hx)

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.CollarVelocity.small_shift_collar_density_oai := @OAI.ClosedSurfaceR4.CollarVelocity.small_shift_collar_density_oai
