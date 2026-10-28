-- Prove2me | solution 1 for OAI.CoulombAtom.sharp_cell_local_potential
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:54:16.425244+00:00
-- url     : https://prove2.me/submissions/1bf00af4-ebcf-48d2-8618-b907543c595b

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_GlobalDensityBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal

namespace CoulombPauli

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]

lemma tensorLeft_adjoint_tensor (u u' : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    (tensorLeft u).adjoint (tensor u' v) = ⟪u,u'⟫_ℂ • v := by
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right, tensorLeft_apply, tensor_inner, inner_smul_right]

end CoulombPauli

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Basis
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
namespace CoulombPauli
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]

variable {ι κ : Type*}

lemma tensorBasis_apply (a : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (b : HilbertBasis κ ℂ (Lp ℂ 2 ν)) (p : ι × κ) :
    tensorBasis a b p = tensor (a p.1) (b p.2) := by
  simp [tensorBasis]

omit [SigmaFinite μ] [SigmaFinite ν] in
lemma basis_parseval {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ι ℂ H) (u : H) :
    HasSum (fun i => ‖inner ℂ (b i) u‖^2) (‖u‖^2) := by
  have hh := (b.hasSum_inner_mul_inner u u).mapL Complex.reCLM
  convert hh using 1
  · ext i
    simp only [Complex.reCLM_apply, ← inner_conj_symm u (b i),
      ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  · simp only [Complex.reCLM_apply, inner_self_eq_norm_sq_to_K,
      ← RCLike.ofReal_pow]
    rfl

lemma tensorRight_parseval (a : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (b : HilbertBasis κ ℂ (Lp ℂ 2 ν)) (ψ : Lp ℂ 2 (μ.prod ν)) :
    ∑' j, ENNReal.ofReal (‖(tensorRight (b j)).adjoint ψ‖^2) =
      ENNReal.ofReal (‖ψ‖^2) := by
  have hs (j : κ) := basis_parseval a ((tensorRight (b j)).adjoint ψ)
  have hsb := basis_parseval (tensorBasis a b) ψ
  calc
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner ℂ (tensor (a i) (b j)) ψ‖^2) := by
      congr 1; funext j
      rw [← (hs j).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hs j).summable]
      simp only [ContinuousLinearMap.adjoint_inner_right, tensorRight_apply]
    _ = ∑' p : ι × κ, ENNReal.ofReal (‖inner ℂ (tensor (a p.1) (b p.2)) ψ‖^2) := by
      rw [ENNReal.tsum_comm]
      exact ENNReal.tsum_prod.symm
    _ = _ := by
      simp_rw [← tensorBasis_apply]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsb.summable, hsb.tsum_eq]

omit [SigmaFinite μ] [SigmaFinite ν] in
lemma hilbertBasis_countable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [SeparableSpace H] (b : HilbertBasis ι ℂ H) : Countable ι := by
  classical
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (b i) (1/2 : ℝ)) (Metric.ball (b j) (1/2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have h := norm_inner_le_norm (𝕜 := ℂ) (b i) (b i - b j)
    have hi := b.orthonormal.norm_eq_one i
    have hii := orthonormal_iff_ite.mp b.orthonormal i i
    have hij' := orthonormal_iff_ite.mp b.orthonormal i j
    have h' : (1 : ℝ) ≤ ‖b i - b j‖ := by
      simpa [inner_sub_right, hii, hij', hi, hij] using h
    norm_num only [dist_eq_norm] at ⊢
    exact h'
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨b i, Metric.mem_ball_self (by norm_num)⟩)

end CoulombPauli

open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Pull
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
namespace CoulombPauli

section
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B}

lemma pull_ae (f : A → B) (hf : MeasurePreserving f μ ν) (ψ : Lp ℂ 2 ν) :
    pull f hf ψ =ᵐ[μ] (fun x => ψ (f x)) := Lp.coeFn_compMeasurePreserving ψ hf

lemma pull_norm (f : A → B) (hf : MeasurePreserving f μ ν) (ψ : Lp ℂ 2 ν) :
    ‖pull f hf ψ‖ = ‖ψ‖ := Lp.norm_compMeasurePreserving ψ hf

lemma pull_inner (f : A → B) (hf : MeasurePreserving f μ ν) (ψ φ : Lp ℂ 2 ν) :
    ⟪pull f hf ψ, pull f hf φ⟫_ℂ = ⟪ψ,φ⟫_ℂ :=
  (Lp.compMeasurePreservingₗᵢ ℂ f hf).inner_map_map ψ φ

end

section EquivPull
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B}
lemma pull_symm (e : A ≃ᵐ B) (he : MeasurePreserving e μ ν) (ψ : Lp ℂ 2 μ) :
    pull e he (pull e.symm he.symm ψ) = ψ := by
  apply Lp.ext
  filter_upwards [pull_ae e he (pull e.symm he.symm ψ),
    he.quasiMeasurePreserving.ae (pull_ae e.symm he.symm ψ)] with x hx hx'
  rw [hx,hx',e.symm_apply_apply]

end EquivPull
section

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]

lemma pureTensor_ae {N : ℕ} (u : Fin N → Lp ℂ 2 μ) :
    pureTensor u =ᵐ[configMeasure N μ] (fun x => ∏ i, u i (x i)) := MemLp.coeFn_toLp _

lemma pureTensor_split {N : ℕ} (u : Fin (N+1) → Lp ℂ 2 μ) (i : Fin (N+1)) :
    pull (splitAt i) (splitAt_preserving i)
      (tensor (u i) (pureTensor (fun j => u (i.succAbove j)))) = pureTensor u := by
  apply Lp.ext
  filter_upwards [pull_ae (splitAt i) (splitAt_preserving i)
      (tensor (u i) (pureTensor (fun j => u (i.succAbove j)))),
    (splitAt_preserving i).quasiMeasurePreserving.ae
      (tensor_ae (u i) (pureTensor (fun j => u (i.succAbove j)))),
    (splitAt_preserving i).quasiMeasurePreserving.ae
      (Measure.quasiMeasurePreserving_snd.ae (pureTensor_ae (fun j => u (i.succAbove j)))),
    pureTensor_ae u] with x h1 h2 h3 h4
  rw [h1,h2,h4]
  dsimp only [splitAt, MeasurableEquiv.piFinSuccAbove_apply] at h3 ⊢
  rw [h3]
  exact (Fin.prod_univ_succAbove (fun j => u j (x j)) i).symm

lemma pureTensor_zero_inner (ψ : sectorL2 0 μ)
    (hψ : ∀ u : Fin 0 → Lp ℂ 2 μ, ⟪pureTensor u,ψ⟫_ℂ = 0) : ψ = 0 := by
  let u : Fin 0 → Lp ℂ 2 μ := Fin.elim0
  have he : ⟪pureTensor u, ψ⟫_ℂ = ψ default := by
    rw [L2.inner_def]
    calc
      _ = ∫ x, ψ x ∂configMeasure 0 μ := by
        apply integral_congr_ae
        filter_upwards [pureTensor_ae u] with x hx
        simp only [hx, Finset.univ_eq_empty, Finset.prod_empty, inner, star_one, mul_one]
      _ = ψ default := by simp [integral_unique, Measure.real, configMeasure]
  apply Lp.ext
  have hv := he.symm.trans (hψ u)
  filter_upwards [Lp.coeFn_zero ℂ 2 (configMeasure 0 μ)] with x hx
  rw [hx]
  simpa only [Subsingleton.elim x default, Pi.zero_apply] using hv

lemma eq_zero_of_pureTensor_orthogonal (N : ℕ) (ψ : sectorL2 N μ)
    (hψ : ∀ u : Fin N → Lp ℂ 2 μ, ⟪pureTensor u,ψ⟫_ℂ = 0) : ψ = 0 := by
  induction N with
  | zero => exact pureTensor_zero_inner ψ hψ
  | succ N ih =>
    let Φ := pull (splitAt (A := A) (0 : Fin (N+1))).symm (splitAt_preserving (μ := μ) 0).symm ψ
    have hΦ : Φ = 0 := by
      apply eq_zero_of_tensor_orthogonal
      intro u v
      have hv : (tensorLeft u).adjoint Φ = 0 := by
        apply ih
        intro w
        rw [ContinuousLinearMap.adjoint_inner_right, tensorLeft_apply]
        have he := pull_inner (splitAt (A := A) (0 : Fin (N+1)))
          (splitAt_preserving (μ := μ) 0) (tensor u (pureTensor w)) Φ
        have ht : pull (splitAt (A := A) (0 : Fin (N+1))) (splitAt_preserving (μ := μ) 0)
            (tensor u (pureTensor w)) = pureTensor (Fin.cons u w) := by
          simpa using pureTensor_split (Fin.cons u w) 0
        rw [ht, show pull (splitAt (A := A) (0 : Fin (N+1))) (splitAt_preserving (μ := μ) 0) Φ = ψ from
          pull_symm _ _ ψ, hψ] at he
        exact he.symm
      rw [← tensorLeft_apply, ← ContinuousLinearMap.adjoint_inner_right, hv, inner_zero_right]
    have he := congrArg (pull (splitAt (A := A) (0 : Fin (N+1))) (splitAt_preserving (μ := μ) 0)) hΦ
    rw [show pull (splitAt (A := A) (0 : Fin (N+1))) (splitAt_preserving (μ := μ) 0) Φ = ψ from
      pull_symm _ _ ψ, map_zero] at he
    exact he

end

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]

lemma continuousLinearMap_ext_pure {N : ℕ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (F G : sectorL2 N μ →L[ℂ] H)
    (h : ∀ u : Fin N → Lp ℂ 2 μ, F (pureTensor u) = G (pureTensor u)) : F = G := by
  have hz (w : H) : (F-G).adjoint w = 0 := by
    apply eq_zero_of_pureTensor_orthogonal
    intro u
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp only [sub_apply, h u, sub_self, inner_zero_left]
  ext x
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  change ⟪(F-G) x, (F-G) x⟫_ℂ = 0
  rw [← ContinuousLinearMap.adjoint_inner_right, hz, inner_zero_right]

omit [SigmaFinite μ] in
lemma pull_adjoint_pull {B : Type*} [MeasurableSpace B] {ν : Measure B}
    (f : A → B) (hf : MeasurePreserving f μ ν) (ψ : Lp ℂ 2 ν) :
    (pull f hf).adjoint (pull f hf ψ) = ψ := by
  apply ext_inner_left ℂ
  intro φ
  rw [ContinuousLinearMap.adjoint_inner_right, pull_inner]

lemma insertOrbital_adjoint_pure {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 μ)
    (f : Fin (N+1) → Lp ℂ 2 μ) :
    (insertOrbital i u).adjoint (pureTensor f) = ⟪u,f i⟫_ℂ • pureTensor (fun j => f (i.succAbove j)) := by
  rw [← pureTensor_split f i]
  dsimp only [insertOrbital]
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    pull_adjoint_pull, tensorLeft_adjoint_tensor]

lemma insertOrbital_pure {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 μ)
    (f : Fin (N+1) → Lp ℂ 2 μ) :
    insertOrbital i u (pureTensor (fun j => f (i.succAbove j))) = pureTensor (Function.update f i u) := by
  simpa only [insertOrbital, ContinuousLinearMap.comp_apply, tensorLeft_apply, Function.update_self, Function.update_of_ne (Fin.succAbove_ne i _)] using
    pureTensor_split (Function.update f i u) i

lemma projectOrbital_pure {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 μ)
    (f : Fin (N+1) → Lp ℂ 2 μ) :
    projectOrbital i u (pureTensor f) = ⟪u,f i⟫_ℂ • pureTensor (Function.update f i u) := by
  dsimp only [projectOrbital, ContinuousLinearMap.comp_apply]
  rw [insertOrbital_adjoint_pure, map_smul, insertOrbital_pure]

lemma permCoords_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : Fin N → A) :
    permCoords π x = x ∘ π := by
  ext j
  simp [permCoords, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

lemma permute_pure {N : ℕ} (π : Equiv.Perm (Fin N)) (f : Fin N → Lp ℂ 2 μ) :
    permute π (pureTensor f) = pureTensor (f ∘ π.symm) := by
  apply Lp.ext
  filter_upwards [pull_ae (permCoords π) (permCoords_preserving π) (pureTensor f),
    (permCoords_preserving π).quasiMeasurePreserving.ae (pureTensor_ae f),
    pureTensor_ae (f ∘ π.symm)] with x h1 h2 h3
  change pull (permCoords π) (permCoords_preserving π) (pureTensor f) x = _
  rw [h1,h2,h3,permCoords_apply]
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp π (fun j => f (π.symm j) (x j))

end CoulombPauli

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Pauli
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
namespace CoulombPauli
variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]

lemma update_pair_swap {N : ℕ} {C : Type*} (f : Fin N → C) (i j : Fin N) (u : C) :
    Function.update (Function.update (f ∘ Equiv.swap i j) j u) i u =
      Function.update (Function.update f j u) i u := by
  classical
  ext k
  by_cases hki : k = i
  · subst k; simp
  by_cases hkj : k = j
  · rw [hkj] at hki ⊢
    simp only [Function.update_of_ne hki, Function.update_self]
  simp [Function.update_of_ne hki, Function.update_of_ne hkj,
    Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]

lemma project_pair_swap {N : ℕ} (i j : Fin (N+1)) (hij : i ≠ j) (u : Lp ℂ 2 μ) :
    ((projectOrbital i u).comp (projectOrbital j u)).comp (permute (Equiv.swap i j)) =
      (projectOrbital i u).comp (projectOrbital j u) := by
  classical
  apply continuousLinearMap_ext_pure
  intro f
  simp only [ContinuousLinearMap.comp_apply, permute_pure, Equiv.symm_swap,
    projectOrbital_pure, map_smul, Function.update_of_ne hij, smul_smul,
    Function.comp_apply, Equiv.swap_apply_right, Equiv.swap_apply_left, update_pair_swap,
    mul_comm]

lemma project_pair_eq_zero {N : ℕ} (i j : Fin (N+1)) (hij : i ≠ j)
    (u : Lp ℂ 2 μ) (ψ : sectorL2 (N+1) μ) (hψ : permute (Equiv.swap i j) ψ = -ψ) :
    projectOrbital i u (projectOrbital j u ψ) = 0 := by
  have he := congrArg (fun F : sectorL2 (N+1) μ →L[ℂ] sectorL2 (N+1) μ => F ψ)
    (project_pair_swap i j hij u)
  simp only [ContinuousLinearMap.comp_apply, hψ, map_neg] at he
  have hi := congrArg (fun w => ⟪projectOrbital i u (projectOrbital j u ψ), w⟫_ℂ) he
  rw [inner_neg_right] at hi
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  linear_combination (norm := ring_nf) -(1/2 : ℂ) * hi

lemma project_inner {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 μ) (ψ φ : sectorL2 (N+1) μ) :
    ⟪projectOrbital i u ψ, φ⟫_ℂ = ⟪ψ, projectOrbital i u φ⟫_ℂ := by
  simp only [projectOrbital, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_adjoint]

lemma project_pair_orthogonal {N : ℕ} (i j : Fin (N+1)) (hij : i ≠ j)
    (u : Lp ℂ 2 μ) (ψ : sectorL2 (N+1) μ) (hψ : permute (Equiv.swap i j) ψ = -ψ) :
    ⟪projectOrbital i u ψ, projectOrbital j u ψ⟫_ℂ = 0 := by
  rw [project_inner, project_pair_eq_zero i j hij u ψ hψ, inner_zero_right]

lemma insertOrbital_norm {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 μ) (ψ : sectorL2 N μ) :
    ‖insertOrbital i u ψ‖ = ‖u‖ * ‖ψ‖ := by
  rw [insertOrbital, ContinuousLinearMap.comp_apply, pull_norm, tensorLeft_apply, tensor_norm]

lemma project_inner_self {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 μ)
    (hu : ‖u‖ = 1) (ψ : sectorL2 (N+1) μ) :
    (⟪projectOrbital i u ψ, ψ⟫_ℂ).re = ‖projectOrbital i u ψ‖^2 := by
  change (⟪insertOrbital i u ((insertOrbital i u).adjoint ψ), ψ⟫_ℂ).re =
    ‖insertOrbital i u ((insertOrbital i u).adjoint ψ)‖^2
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change RCLike.re ⟪(insertOrbital i u).adjoint ψ, (insertOrbital i u).adjoint ψ⟫_ℂ = _
  rw [inner_self_eq_norm_sq (𝕜 := ℂ), insertOrbital_norm, hu, one_mul]

lemma sum_project_norm_sq_le {N : ℕ} (u : Lp ℂ 2 μ) (hu : ‖u‖ = 1)
    (ψ : sectorL2 (N+1) μ)
    (hψ : ∀ i j : Fin (N+1), i ≠ j → permute (Equiv.swap i j) ψ = -ψ) :
    (∑ i : Fin (N+1), ‖projectOrbital i u ψ‖^2) ≤ ‖ψ‖^2 := by
  classical
  let p : Fin (N+1) → sectorL2 (N+1) μ := fun i => projectOrbital i u ψ
  have horth (i j : Fin (N+1)) (hij : i ≠ j) : ⟪p i,p j⟫_ℂ = 0 :=
    project_pair_orthogonal i j hij u ψ (hψ i j hij)
  have hs : ‖∑ i, p i‖^2 = ∑ i, ‖p i‖^2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    have he : ⟪∑ i, p i, ∑ j, p j⟫_ℂ = ∑ i, ⟪p i,p i⟫_ℂ := by
      simp only [sum_inner, inner_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_eq_single i (fun j _ hji => horth j i hji) (by simp)
    rw [he, map_sum]
    simp only [inner_self_eq_norm_sq (𝕜 := ℂ)]
  have hp : (⟪∑ i, p i, ψ⟫_ℂ).re = ∑ i, ‖p i‖^2 := by
    rw [sum_inner, Complex.re_sum]
    exact Finset.sum_congr rfl (fun i _ => project_inner_self i u hu ψ)
  have hn := sq_nonneg ‖(∑ i, p i) - ψ‖
  rw [norm_sub_sq (𝕜 := ℂ), hs] at hn
  change 0 ≤ _ - 2 * (⟪∑ i, p i, ψ⟫_ℂ).re + _ at hn
  rw [hp] at hn
  dsimp only [p] at *
  linarith

end CoulombPauli

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_WeakDirectionalDerivative
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
namespace CoulombAtom
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma testScale_pos (n : ℕ) : 0 < testScale n := by unfold testScale; positivity
lemma testScale_le_one (n : ℕ) : testScale n ≤ 1 := by
  unfold testScale
  exact inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
lemma testScale_tendsto : Tendsto testScale atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_atTop_mono
    (fun n : ℕ => by linarith : ∀ n : ℕ, (n:ℝ) ≤ (n:ℝ)+1) tendsto_natCast_atTop_atTop)

omit [MeasurableSpace V] [BorelSpace V] in
lemma testCutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (testCutoff (V := V) n) :=
  (testBump (V := V)).contDiff.comp (contDiff_id.const_smul _)

omit [MeasurableSpace V] [BorelSpace V] in
lemma testCutoff_compact (n : ℕ) : HasCompactSupport (testCutoff (V := V) n) :=
  (testBump (V := V)).hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero (testScale n) (testScale_pos n).ne')

omit [MeasurableSpace V] [BorelSpace V] in
lemma testCutoff_norm_le (n : ℕ) (x : V) : ‖testCutoff n x‖ ≤ 1 := by
  change ‖(testBump (V := V)) (testScale n • x)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (testBump (V := V)).nonneg]
  exact (testBump (V := V)).le_one

omit [MeasurableSpace V] [BorelSpace V] in
lemma testCutoff_tendsto (x : V) : Tendsto (fun n => testCutoff n x) atTop (𝓝 1) := by
  have hh := (testBump (V := V)).continuous.continuousAt.tendsto.comp (testScale_tendsto.smul_const x)
  have hz : (testBump (V := V)) 0 = 1 :=
    (testBump (V := V)).one_of_mem_closedBall (by simp [testBump])
  simpa only [zero_smul, hz, testCutoff, Function.comp_def] using hh

omit [MeasurableSpace V] [BorelSpace V] in
lemma testCutoff_derivative (n : ℕ) (x v : V) :
    fderiv ℝ (testCutoff n) x v =
      testScale n * fderiv ℝ (testBump (V := V) : V → ℝ) (testScale n • x) v := by
  have hh := ((((testBump (V := V)).contDiff (n := ⊤)).differentiable (by simp) (testScale n • x)).hasFDerivAt).comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul (testScale n))
  have he := congrArg (fun L : V →L[ℝ] ℝ => L v) hh.fderiv
  refine he.trans ?_
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    map_smul, smul_eq_mul]

omit [MeasurableSpace V] [BorelSpace V] in
lemma testCutoff_derivative_control (v : V) : ∃ D : ℝ, 0 ≤ D ∧
    (∀ n x, ‖fderiv ℝ (testCutoff n) x v‖ ≤ D) ∧
    (∀ x, Tendsto (fun n => fderiv ℝ (testCutoff n) x v) atTop (𝓝 0)) := by
  obtain ⟨C, hC⟩ := (((testBump (V := V)).contDiff (n := ⊤)).continuous_fderiv (by simp)).bounded_above_of_compact_support
    ((testBump (V := V)).hasCompactSupport.fderiv ℝ)
  let D := max C 0 * ‖v‖
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb (n : ℕ) (x : V) : ‖fderiv ℝ (testCutoff n) x v‖ ≤ testScale n * D := by
    rw [testCutoff_derivative, norm_mul, Real.norm_eq_abs, abs_of_pos (testScale_pos n)]
    apply mul_le_mul_of_nonneg_left _ (testScale_pos n).le
    exact ((fderiv ℝ (testBump (V := V) : V → ℝ) (testScale n • x)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right ((hC _).trans (le_max_left _ _)) (norm_nonneg v))
  refine ⟨D, hD, fun n x => (hb n x).trans ?_, fun x => ?_⟩
  · exact (mul_le_mul_of_nonneg_right (testScale_le_one n) hD).trans_eq (one_mul D)
  · exact squeeze_zero_norm (fun n => hb n x) (by simpa using testScale_tendsto.mul_const D)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma fderiv_mul_real {φ χ : V → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hχ : ContDiff ℝ ∞ χ) (x v : V) :
    fderiv ℝ (fun y => χ y * φ y) x v = fderiv ℝ χ x v * φ x + χ x * fderiv ℝ φ x v := by
  have hd := ((hχ.differentiable (by simp) x).hasFDerivAt).mul
    ((hφ.differentiable (by simp) x).hasFDerivAt)
  have he := congrArg (fun L : V →L[ℝ] ℝ => L v) hd.fderiv
  refine he.trans ?_
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma weak_derivative_smooth_L2 {f g : V → ℂ} {v : V}
    (hf : MemLp f 2) (hg : MemLp g 2) (hw : HasWeakDirectionalDerivative f g v)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφL : MemLp φ 2)
    (hφD : MemLp (fun x => fderiv ℝ φ x v) 2) :
    (∫ x, f x * (fderiv ℝ φ x v : ℂ)) = -(∫ x, g x * (φ x : ℂ)) := by
  obtain ⟨D, hD, hbound, htendsto⟩ := testCutoff_derivative_control v
  let φn : ℕ → V → ℝ := fun n x => testCutoff n x * φ x
  have hs (n : ℕ) : ContDiff ℝ ∞ (φn n) := (testCutoff_smooth n).mul hφ
  have hcompact (n : ℕ) : HasCompactSupport (φn n) := (testCutoff_compact n).mul_right
  have hd (n : ℕ) (x : V) : fderiv ℝ (φn n) x v =
      fderiv ℝ (testCutoff n) x v * φ x + testCutoff n x * fderiv ℝ φ x v :=
    fderiv_mul_real hφ (testCutoff_smooth n) x v
  have hi1 := hf.norm.integrable_mul hφL.norm
  have hi2 := hf.norm.integrable_mul hφD.norm
  have ha : Tendsto (fun n => ∫ x, f x * (fderiv ℝ (φn n) x v : ℂ)) atTop
      (𝓝 (∫ x, f x * (fderiv ℝ φ x v : ℂ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x => D * (‖f x‖ * ‖φ x‖) + ‖f x‖ * ‖fderiv ℝ φ x v‖)
    · exact Eventually.of_forall (fun n => hf.aestronglyMeasurable.mul
        ((Complex.continuous_ofReal.comp (((hs n).continuous_fderiv (by simp)).clm_apply
          continuous_const)).aestronglyMeasurable))
    · refine Eventually.of_forall (fun n => Eventually.of_forall fun x => ?_)
      rw [norm_mul, Complex.norm_real, hd]
      calc
        _ ≤ ‖f x‖ * (‖fderiv ℝ (testCutoff n) x v‖ * ‖φ x‖ +
            ‖testCutoff n x‖ * ‖fderiv ℝ φ x v‖) := by
          gcongr; exact (norm_add_le _ _).trans_eq (by simp only [norm_mul])
        _ ≤ ‖f x‖ * (D * ‖φ x‖ + 1 * ‖fderiv ℝ φ x v‖) := by
          gcongr; exact hbound n x; exact testCutoff_norm_le n x
        _ = _ := by ring
    · exact (hi1.const_mul D).add hi2
    · refine Eventually.of_forall (fun x => ?_)
      simp_rw [hd]
      simpa only [zero_mul, one_mul, zero_add] using
        (((htendsto x).mul_const (φ x)).add
          ((testCutoff_tendsto x).mul_const (fderiv ℝ φ x v))).ofReal.const_mul (f x)
  have hb : Tendsto (fun n => ∫ x, g x * (φn n x : ℂ)) atTop
      (𝓝 (∫ x, g x * (φ x : ℂ))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖g x‖ * ‖φ x‖)
    · exact Eventually.of_forall (fun n => hg.aestronglyMeasurable.mul
        ((Complex.continuous_ofReal.comp (hs n).continuous).aestronglyMeasurable))
    · refine Eventually.of_forall (fun n => Eventually.of_forall fun x => ?_)
      simp only [norm_mul, Complex.norm_real, φn]
      calc
        _ ≤ ‖g x‖ * (1 * ‖φ x‖) := by gcongr; exact testCutoff_norm_le n x
        _ = _ := by ring
    · exact hg.norm.integrable_mul hφL.norm
    · refine Eventually.of_forall (fun x => ?_)
      simpa only [one_mul, φn] using
        ((testCutoff_tendsto x).mul_const (φ x)).ofReal.const_mul (g x)
  apply tendsto_nhds_unique ha
  convert hb.neg using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  have hh := hw (φn n) (hs n) (hcompact n)
  simpa only [((hs n).differentiable (by simp) _).lineDeriv_eq_fderiv] using hh

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma fderiv_schwartz_postcomp (φ : 𝓢(V, ℂ)) (L : ℂ →L[ℝ] ℝ) (x v : V) :
    fderiv ℝ (φ.postcompCLM L) x v = L (fderiv ℝ φ x v) := by
  have hh := L.hasFDerivAt.comp x (φ.differentiable x).hasFDerivAt
  exact congrArg (fun A : V →L[ℝ] ℝ => A v) hh.fderiv

lemma weak_derivative_schwartz {f g : V → ℂ} {v : V}
    (hf : MemLp f 2) (hg : MemLp g 2) (hw : HasWeakDirectionalDerivative f g v)
    (φ : 𝓢(V, ℂ)) :
    (∫ x, f x * fderiv ℝ φ x v) = -(∫ x, g x * φ x) := by
  let r : 𝓢(V, ℝ) := φ.postcompCLM Complex.reCLM
  let j : 𝓢(V, ℝ) := φ.postcompCLM Complex.imCLM
  let dr : 𝓢(V, ℝ) := SchwartzMap.evalCLM ℝ V ℝ v (SchwartzMap.fderivCLM ℝ V ℝ r)
  let dj : 𝓢(V, ℝ) := SchwartzMap.evalCLM ℝ V ℝ v (SchwartzMap.fderivCLM ℝ V ℝ j)
  have hdr : MemLp (fun x => fderiv ℝ (r : V → ℝ) x v) 2 volume := by
    convert dr.memLp 2 volume using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp [dr, SchwartzMap.evalCLM_apply_apply, SchwartzMap.fderivCLM_apply]
  have hdj : MemLp (fun x => fderiv ℝ (j : V → ℝ) x v) 2 volume := by
    convert dj.memLp 2 volume using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp [dj, SchwartzMap.evalCLM_apply_apply, SchwartzMap.fderivCLM_apply]
  have hr := weak_derivative_smooth_L2 hf hg hw (φ := (r : V → ℝ)) r.smooth' (r.memLp 2 volume) hdr
  have hj := weak_derivative_smooth_L2 hf hg hw (φ := (j : V → ℝ)) j.smooth' (j.memLp 2 volume) hdj
  have hcast (a : 𝓢(V, ℝ)) : MemLp (fun x => (a x : ℂ)) 2 volume := by
    convert (a.postcompCLM Complex.ofRealCLM).memLp 2 volume using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp
  have hdecomp (x : V) : fderiv ℝ φ x v = (dr x : ℂ) + (dj x : ℂ) * Complex.I := by
    change fderiv ℝ φ x v = (fderiv ℝ r x v : ℂ) + (fderiv ℝ j x v : ℂ) * Complex.I
    rw [fderiv_schwartz_postcomp, fderiv_schwartz_postcomp]
    exact (Complex.re_add_im _).symm
  have hdecomp' (x : V) : φ x = (r x : ℂ) + (j x : ℂ) * Complex.I :=
    (Complex.re_add_im _).symm
  have hir : Integrable (fun x => f x * (dr x : ℂ)) :=
    hf.integrable_mul (hcast dr)
  have hij : Integrable (fun x => f x * (dj x : ℂ)) :=
    hf.integrable_mul (hcast dj)
  have hgr : Integrable (fun x => g x * (r x : ℂ)) :=
    hg.integrable_mul (hcast r)
  have hgj : Integrable (fun x => g x * (j x : ℂ)) :=
    hg.integrable_mul (hcast j)
  calc
    _ = (∫ x, f x * (dr x : ℂ)) + (∫ x, f x * (dj x : ℂ)) * Complex.I := by
      simp_rw [hdecomp, mul_add, ← mul_assoc]
      rw [integral_add hir (hij.mul_const _), integral_mul_const]
    _ = -((∫ x, g x * (r x : ℂ)) + (∫ x, g x * (j x : ℂ)) * Complex.I) := by
      change (∫ x, f x * (fderiv ℝ r x v : ℂ)) +
        (∫ x, f x * (fderiv ℝ j x v : ℂ)) * Complex.I = _
      rw [hr, hj]
      ring
    _ = _ := by
      congr 1
      simp_rw [hdecomp', mul_add, ← mul_assoc]
      rw [integral_add hgr (hgj.mul_const _), integral_mul_const]

open LineDeriv in
lemma weak_derivative_tempered {f g : V → ℂ} {v : V}
    (hf : MemLp f 2) (hg : MemLp g 2) (hw : HasWeakDirectionalDerivative f g v) :
    ∂_{v} (Lp.toTemperedDistribution (hf.toLp f)) =
      Lp.toTemperedDistribution (hg.toLp g) := by
  ext φ
  rw [TemperedDistribution.lineDerivOp_apply_apply]
  simp only [Lp.toTemperedDistribution_apply, neg_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul, neg_mul, integral_neg]
  have h1 : (∫ x : V, fderiv ℝ φ x v * hf.toLp f x) =
      ∫ x : V, f x * fderiv ℝ φ x v := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx, mul_comm]
  have h2 : (∫ x : V, φ x * hg.toLp g x) = ∫ x : V, g x * φ x := by
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx, mul_comm]
  rw [h1, h2, weak_derivative_schwartz hf hg hw φ, neg_neg]

open LineDeriv in
lemma weak_fourier_derivative_ae {f g : V → ℂ} {v : V}
    (hf : MemLp f 2) (hg : MemLp g 2) (hw : HasWeakDirectionalDerivative f g v) :
    (fun ξ => (𝓕 (hg.toLp g) : Lp ℂ 2 volume) ξ) =ᵐ[volume]
      (fun ξ => (2 * Real.pi * Complex.I) * (inner ℝ ξ v : ℂ) *
        (𝓕 (hf.toLp f) : Lp ℂ 2 volume) ξ) := by
  let F : Lp ℂ 2 (volume : Measure V) := 𝓕 (hf.toLp f)
  let G : Lp ℂ 2 (volume : Measure V) := 𝓕 (hg.toLp g)
  have hd := congrArg (fun d : 𝓢'(V, ℂ) => 𝓕 d) (weak_derivative_tempered hf hg hw)
  rw [TemperedDistribution.fourier_lineDerivOp_eq,
    Lp.fourier_toTemperedDistribution_eq, Lp.fourier_toTemperedDistribution_eq] at hd
  have ht : (fun ξ : V => (inner ℝ ξ v : ℂ)).HasTemperateGrowth := by fun_prop
  have hc : Continuous (fun ξ : V => (2 * Real.pi * Complex.I) * (inner ℝ ξ v : ℂ)) := by
    fun_prop
  apply ae_eq_of_integral_contDiff_smul_eq
    (Lp.memLp G |>.locallyIntegrable (by norm_num))
    (LocallyIntegrable.continuous_mul hc (Lp.memLp F |>.locallyIntegrable (by norm_num)))
  intro φ hφ hcompact
  let ψ : 𝓢(V, ℂ) := (hcompact.comp_left rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hφ)
  have hh := congrArg (fun d : 𝓢'(V, ℂ) => d ψ) hd
  simp only [smul_apply, TemperedDistribution.smulLeftCLM_apply_apply,
    Lp.toTemperedDistribution_apply, SchwartzMap.smulLeftCLM_apply_apply ht,
    smul_eq_mul] at hh
  change (2 * Real.pi * Complex.I) *
      (∫ x, ((inner ℝ x v : ℂ) * ψ x) * F x) = ∫ x, ψ x * G x at hh
  simp only [Complex.real_smul]
  change (∫ x, ψ x * G x) = ∫ x, ψ x * ((2 * Real.pi * Complex.I) * (inner ℝ x v : ℂ) * F x)
  rw [← hh, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    ring

lemma l2_norm_sq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : Lp ℂ 2 μ) : ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def]
  simp only [inner_self_eq_norm_sq_to_K]
  change (∫ x, (‖u x‖ : ℂ)^2 ∂μ).re = _
  simp_rw [← Complex.ofReal_pow]
  rw [integral_complex_ofReal]
  rfl

lemma weak_fourier_moment {f g : V → ℂ} {v : V}
    (hf : MemLp f 2) (hg : MemLp g 2) (hw : HasWeakDirectionalDerivative f g v) :
    Integrable (fun ξ => (2 * Real.pi)^2 * (inner ℝ ξ v)^2 *
        ‖(𝓕 (hf.toLp f) : Lp ℂ 2 volume) ξ‖^2) ∧
    (∫ ξ, (2 * Real.pi)^2 * (inner ℝ ξ v)^2 *
        ‖(𝓕 (hf.toLp f) : Lp ℂ 2 volume) ξ‖^2) = ∫ x, ‖g x‖^2 := by
  let G : Lp ℂ 2 (volume : Measure V) := 𝓕 (hg.toLp g)
  have hae : (fun ξ => ‖G ξ‖^2) =ᵐ[volume]
      (fun ξ => (2 * Real.pi)^2 * (inner ℝ ξ v)^2 *
        ‖(𝓕 (hf.toLp f) : Lp ℂ 2 volume) ξ‖^2) := by
    filter_upwards [weak_fourier_derivative_ae hf hg hw] with ξ hξ
    change ‖(𝓕 (hg.toLp g) : Lp ℂ 2 volume) ξ‖^2 = _
    rw [hξ]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
      mul_one, mul_pow, Real.norm_eq_abs, sq_abs]
  have hi : Integrable (fun ξ => ‖G ξ‖^2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable G)).mp (Lp.memLp G)
  refine ⟨hi.congr hae, ?_⟩
  rw [← integral_congr_ae hae, ← l2_norm_sq_integral, Lp.norm_fourier_eq,
    l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]

lemma weak_fourier_kinetic {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {f : V → ℂ} {g : ι → V → ℂ} (hf : MemLp f 2) (hg : ∀ i, MemLp (g i) 2)
    (hw : ∀ i, HasWeakDirectionalDerivative f (g i) (b i)) :
    Integrable (fun ξ => (2 * Real.pi)^2 * ‖ξ‖^2 *
        ‖(𝓕 (hf.toLp f) : Lp ℂ 2 volume) ξ‖^2) ∧
    (∫ ξ, (2 * Real.pi)^2 * ‖ξ‖^2 *
        ‖(𝓕 (hf.toLp f) : Lp ℂ 2 volume) ξ‖^2) = ∑ i, ∫ x, ‖g i x‖^2 := by
  classical
  have he (ξ : V) : (2 * Real.pi)^2 * ‖ξ‖^2 *
      ‖(𝓕 (hf.toLp f) : Lp ℂ 2 volume) ξ‖^2 =
      ∑ i, (2 * Real.pi)^2 * (inner ℝ ξ (b i))^2 *
        ‖(𝓕 (hf.toLp f) : Lp ℂ 2 volume) ξ‖^2 := by
    rw [← b.sum_sq_inner_left ξ, Finset.mul_sum, Finset.sum_mul]
  simp_rw [he]
  have hi (i : ι) := (weak_fourier_moment hf (hg i) (hw i)).1
  refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hi i)]
  exact Finset.sum_congr rfl (fun i _ => (weak_fourier_moment hf (hg i) (hw i)).2)

lemma classical_fourier_continuous {f : V → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf

open scoped LineDeriv

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_L2
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace CoulombSobolev

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

namespace Test

omit [FiniteDimensional ℝ E] in
lemma coe_toL2 (φ : Test E) : (φ.toL2 : E → ℂ) =ᵐ[volume] fun x => (φ.fn x : ℂ) :=
  φ.memLp.coeFn_toLp

omit [FiniteDimensional ℝ E] in
lemma inner_toL2 (φ : Test E) (f : L2 E) :
    ⟪φ.toL2, f⟫_ℂ = ∫ x, f x * (φ.fn x : ℂ) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [φ.coe_toL2] with x hx
  rw [hx]
  simp [RCLike.inner_apply]

end Test

lemma test_total (f : L2 E) (hf : ∀ φ : Test E, ⟪φ.toL2, f⟫_ℂ = 0) : f = 0 := by
  apply Lp.ext
  have ht : ∀ (g : E → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • f x = 0 := by
    intro g hg hc
    have hid := hf ⟨g, hg, hc⟩
    rw [Test.inner_toL2] at hid
    simpa only [Complex.real_smul, mul_comm] using hid
  have hh : (f : E → ℂ) =ᵐ[volume] 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((Lp.memLp f).locallyIntegrable (by norm_num)) ht
  exact hh.trans (Lp.coeFn_zero _ _ _).symm

end

section
open CoulombPauli
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [(volume : Measure V).IsAddHaarMeasure]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasureSpace W] [BorelSpace W]
  [(volume : Measure W).IsAddHaarMeasure]

namespace Test

omit [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [(volume : Measure V).IsAddHaarMeasure]
  [FiniteDimensional ℝ W] [MeasureSpace W] [BorelSpace W]
  [(volume : Measure W).IsAddHaarMeasure] in
lemma tensor_deriv (φ : Test V) (η : Test W) (v : V) :
    (φ.tensor η).deriv (v,0) = (φ.deriv v).tensor η := by
  have hext {a b : Test (V × W)} (h : a.fn = b.fn) : a = b := by
    cases a; cases b; cases h; rfl
  apply hext
  funext z
  dsimp [tensor,deriv]
  change (fderiv ℝ ((φ.fn ∘ Prod.fst) * (η.fn ∘ Prod.snd)) z) (v,0) = _
  rw [fderiv_mul ((φ.smooth.comp contDiff_fst).differentiable (by simp) z)
      ((η.smooth.comp contDiff_snd).differentiable (by simp) z),
    add_apply]
  simp only [smul_apply, smul_eq_mul]
  rw [fderiv_comp z (φ.smooth.differentiable (by simp) _) (by fun_prop),
    fderiv_comp z (η.smooth.differentiable (by simp) _) (by fun_prop)]
  simp only [fderiv_fst, fderiv_snd, ContinuousLinearMap.comp_apply]
  change φ.fn z.1 * (fderiv ℝ η.fn z.2) 0 + η.fn z.2 * (fderiv ℝ φ.fn z.1) v = _
  rw [map_zero]
  ring
end Test

end

open CoulombPauli
end CoulombSobolev

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_L2
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
namespace CoulombAtom
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma l2_norm_sq (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def]
  simp_rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
  rw [integral_ofReal]
  rfl

end CoulombAtom

open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Spin
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombPauli
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
  [Fintype S] [MeasurableSingletonClass S] {μ : Measure A} [SigmaFinite μ]

lemma prod_spin_norm_sq (v : S → A → ℂ) (hv : ∀ s, MemLp (v s) 2 μ) :
    (∫ p : A × S, ‖v p.2 p.1‖^2 ∂μ.prod Measure.count) = ∑ s : S, ∫ x, ‖v s x‖^2 ∂μ := by
  have hi := (memLp_two_iff_integrable_sq_norm
    (memLp_spin v hv).aestronglyMeasurable).1 (memLp_spin v hv)
  rw [integral_prod_symm _ hi, integral_count]

end CoulombPauli

namespace CoulombAtom
namespace Pauli
open CoulombPauli

lemma splitSpin_apply {N : ℕ} (x : Fin N → OneParticle) :
    splitSpin N x = (fun i => (x i).1, fun i => (x i).2) := rfl

lemma toMany_ae {N : ℕ} (ψ : FormVector N) (hψ : ∀ s, MemLp (ψ.value s) 2) :
    toMany ψ hψ =ᵐ[configMeasure N oneMeasure] (fun x : Fin N → OneParticle =>
      ψ.value (fun i => (x i).2) (fun i => (x i).1)) := MemLp.coeFn_toLp _

lemma toMany_norm_sq {N : ℕ} (ψ : FormVector N) (hψ : ∀ s, MemLp (ψ.value s) 2) :
    ‖toMany ψ hψ‖^2 = ∑ s : Spins N, ∫ x, ‖ψ.value s x‖^2 := by
  rw [l2_norm_sq]
  calc
    _ = ∫ x : Fin N → OneParticle,
        ‖ψ.value (fun i => (x i).2) (fun i => (x i).1)‖^2 ∂configMeasure N oneMeasure :=
      integral_congr_ae ((toMany_ae ψ hψ).fun_comp (fun z : ℂ => ‖z‖^2))
    _ = ∫ p : Configuration N × Spins N, ‖ψ.value p.2 p.1‖^2 ∂volume.prod Measure.count :=
      (splitSpin_preserving N).integral_comp (splitSpin N).measurableEmbedding
        (fun p : Configuration N × Spins N => ‖ψ.value p.2 p.1‖^2)
    _ = _ := prod_spin_norm_sq ψ.value hψ

lemma toMany_permute {N : ℕ} (ψ : FormVector N) (hψ : ∀ s, MemLp (ψ.value s) 2)
    (π : Equiv.Perm (Fin N))
    (ha : ∀ s, ∀ᵐ x, ψ.value (s ∘ π) (x ∘ π) =
      (((Equiv.Perm.sign π : ℤ) : ℂ) * ψ.value s x)) :
    permute π (toMany ψ hψ) = (((Equiv.Perm.sign π : ℤ) : ℂ)) • toMany ψ hψ := by
  have hax : ∀ᵐ x, ∀ s, ψ.value (s ∘ π) (x ∘ π) =
      (((Equiv.Perm.sign π : ℤ) : ℂ) * ψ.value s x) := ae_all_iff.2 ha
  have hab : ∀ᵐ p : Configuration N × Spins N ∂volume.prod Measure.count,
      ψ.value (p.2 ∘ π) (p.1 ∘ π) = (((Equiv.Perm.sign π : ℤ) : ℂ) * ψ.value p.2 p.1) :=
    (Measure.quasiMeasurePreserving_fst.ae hax).mono (fun p hp => hp p.2)
  have hat := (splitSpin_preserving N).quasiMeasurePreserving.ae hab
  apply Lp.ext
  filter_upwards [pull_ae (permCoords π) (permCoords_preserving π) (toMany ψ hψ),
    (permCoords_preserving π).quasiMeasurePreserving.ae (toMany_ae ψ hψ),
    toMany_ae ψ hψ, Lp.coeFn_smul (((Equiv.Perm.sign π : ℤ) : ℂ)) (toMany ψ hψ), hat]
    with x h1 h2 h3 h4 h5
  change pull (permCoords π) (permCoords_preserving π) (toMany ψ hψ) x = _
  rw [h1,h2,h4]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h3]
  simpa only [splitSpin_apply, permCoords_apply, Function.comp_def, smul_eq_mul] using h5

end Pauli
end CoulombAtom

namespace CoulombPauli
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

attribute [local instance] OAI.CoulombPauli.instDecidableEq_solutions
omit [Fintype S] in
lemma countVector_inner (s : S) (u : Lp ℂ 2 (Measure.count : Measure S)) :
    inner ℂ (countVector s) u = u s := by
  rw [countVector, L2.inner_indicatorConstLp_one]
  simp

omit [Fintype S] in
lemma countVector_ae (s : S) :
    countVector s =ᵐ[Measure.count] (fun t : S => if t = s then (1 : ℂ) else 0) := by
  unfold countVector
  filter_upwards [(indicatorConstLp_coeFn (p := 2) (hs := measurableSet_singleton s)
    (hμs := by simp) (c := (1 : ℂ)))] with t ht
  rw [ht]
  by_cases h : t = s <;> simp [h]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
open CoulombSobolev

lemma spin_test_total (f : Lp ℂ 2 ((volume : Measure E).prod (Measure.count : Measure S)))
    (hf : ∀ (φ : Test E) (s : S), inner ℂ (tensor φ.toL2 (countVector s)) f = 0) : f = 0 := by
  have hx (φ : Test E) : (tensorLeft φ.toL2).adjoint f = 0 := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_zero ℂ 2 (Measure.count : Measure S)] with s hs
    rw [← countVector_inner, ContinuousLinearMap.adjoint_inner_right, tensorLeft_apply,
      hf, hs, Pi.zero_apply]
  apply eq_zero_of_tensor_orthogonal
  intro u v
  have hh : (tensorRight v).adjoint f = 0 := by
    apply test_total
    intro φ
    rw [← tensor_adjoint_exchange, hx, inner_zero_right]
  rw [← tensorRight_apply, ← ContinuousLinearMap.adjoint_inner_right, hh, inner_zero_right]

lemma spin_test_inner (v : S → E → ℂ) (hv : ∀ s, MemLp (v s) 2)
    (φ : Test E) (s : S) :
    inner ℂ (tensor φ.toL2 (countVector s)) ((memLp_spin v hv).toLp _) =
      ∫ x, v s x * (φ.fn x : ℂ) := by
  classical
  have he : (fun p : E × S => inner ℂ (tensor φ.toL2 (countVector s) p)
      ((memLp_spin v hv).toLp _ p)) =ᵐ[volume.prod Measure.count]
      (fun p : E × S => (v p.2 p.1 * (φ.fn p.1 : ℂ)) * (if p.2 = s then 1 else 0)) := by
    filter_upwards [tensor_ae φ.toL2 (countVector s),
      (memLp_spin v hv).coeFn_toLp,
      Measure.quasiMeasurePreserving_fst.ae φ.coe_toL2,
      Measure.quasiMeasurePreserving_snd.ae (countVector_ae s)] with p h1 h2 h3 h4
    rw [h1,h2,h3,h4]
    split_ifs <;> simp [RCLike.inner_apply, mul_comm]
  have hi : Integrable (fun p : E × S => (v p.2 p.1 * (φ.fn p.1 : ℂ)) *
      (if p.2 = s then 1 else 0)) (volume.prod Measure.count) :=
    (L2.integrable_inner (tensor φ.toL2 (countVector s)) ((memLp_spin v hv).toLp _)).congr he
  rw [MeasureTheory.L2.inner_def, integral_congr_ae he, integral_prod_symm _ hi, integral_count]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ ht; simp [ht]
  · simp
end CoulombPauli

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_ManyTest
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombAtom.Pauli
open CoulombPauli CoulombSobolev

lemma manyTest_ae {N : ℕ} (φ : Test (Configuration N)) (s : Spins N) :
    manyTest φ s =ᵐ[configMeasure N oneMeasure] (fun x : Fin N → OneParticle =>
      (φ.fn (fun i => (x i).1) : ℂ) * (if (fun i => (x i).2) = s then 1 else 0)) := by
  have hh : tensor φ.toL2 (countVector s) =ᵐ[volume.prod Measure.count]
      (fun p : Configuration N × Spins N => (φ.fn p.1 : ℂ) * (if p.2 = s then 1 else 0)) := by
    filter_upwards [tensor_ae φ.toL2 (countVector s),
      Measure.quasiMeasurePreserving_fst.ae φ.coe_toL2,
      Measure.quasiMeasurePreserving_snd.ae (countVector_ae s)] with p h1 h2 h3
    rw [h1,h2,h3]
    by_cases h : p.2 = s <;> simp [h]
  exact (pull_ae _ _ _).trans ((splitSpin_preserving N).quasiMeasurePreserving.ae hh)

lemma toMany_eq_pull {N : ℕ} (ψ : FormVector N) (hψ : ∀ s, MemLp (ψ.value s) 2) :
    toMany ψ hψ = pull (splitSpin N) (splitSpin_preserving N)
      ((memLp_spin ψ.value hψ).toLp _) := by
  apply Lp.ext
  exact (toMany_ae ψ hψ).trans ((pull_ae _ _ _).trans
    ((splitSpin_preserving N).quasiMeasurePreserving.ae (memLp_spin ψ.value hψ).coeFn_toLp)).symm

lemma manyTest_inner {N : ℕ} (ψ : FormVector N) (hψ : ∀ s, MemLp (ψ.value s) 2)
    (φ : Test (Configuration N)) (s : Spins N) :
    inner ℂ (manyTest φ s) (toMany ψ hψ) = ∫ x, ψ.value s x * (φ.fn x : ℂ) := by
  rw [manyTest, toMany_eq_pull, pull_inner]
  exact spin_test_inner ψ.value hψ φ s

lemma manyTest_total {N : ℕ} (ψ : Many N)
    (hψ : ∀ (φ : Test (Configuration N)) (s : Spins N), inner ℂ (manyTest φ s) ψ = 0) : ψ = 0 := by
  let e := splitSpin N
  let he := splitSpin_preserving N
  have hz : pull e.symm (he.symm e) ψ = 0 := by
    apply spin_test_total
    intro φ s
    have hh := hψ φ s
    unfold manyTest at hh
    rw [← pull_symm e he ψ] at hh
    rw [pull_inner] at hh
    exact hh
  have hh := congrArg (pull e he) hz
  simpa only [pull_symm, map_zero] using hh

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

lemma coordinateSplit_apply {N : ℕ} (i : Fin (N+1)) (x : Fin (N+1) → X) :
    coordinateSplit i x = (x i, fun j => x (i.succAbove j)) := rfl

end CoulombAtom.Pauli

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CompCL
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombSobolev.Test
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma ext_fn {φ η : Test E} (h : φ.fn = η.fn) : φ = η := by
  cases φ; cases η; cases h; rfl

lemma compCL_deriv (φ : Test F) (e : E ≃L[ℝ] F) (v : E) :
    (φ.compCL e).deriv v = (φ.deriv (e v)).compCL e := by
  apply ext_fn
  funext x
  change fderiv ℝ (φ.fn ∘ e) x v = _
  rw [fderiv_comp x (φ.smooth.differentiable (by simp) _) e.differentiableAt]
  simp only [ContinuousLinearEquiv.fderiv, ContinuousLinearMap.comp_apply]
  rfl
end CoulombSobolev.Test

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_InsertTest
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombAtom.Pauli
open CoulombPauli CoulombSobolev

lemma coordinateSplit_direction {N : ℕ} (i : Fin (N+1)) (a : Fin 3) :
    coordinateSplit i (direction i a) = (EuclideanSpace.single a 1, 0) := by
  rw [coordinateSplit_apply]
  apply Prod.ext
  · simp [direction]
  · funext j
    simp [direction, Fin.succAbove_ne]

lemma insertTest_deriv {N : ℕ} (i : Fin (N+1)) (a : Fin 3)
    (φ : Test Space) (η : Test (Configuration N)) :
    (insertTest i φ η).deriv (direction i a) =
      insertTest i (φ.deriv (EuclideanSpace.single a 1)) η := by
  rw [insertTest, Test.compCL_deriv, coordinateSplit_direction, Test.tensor_deriv]
  rfl

lemma insertTest_apply {N : ℕ} (i : Fin (N+1)) (φ : Test Space) (η : Test (Configuration N))
    (x : Configuration (N+1)) :
    (insertTest i φ η).fn x = φ.fn (x i) * η.fn (fun j => x (i.succAbove j)) := rfl

lemma insertOrbital_ae {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 oneMeasure) (ψ : Many N) :
    CoulombPauli.insertOrbital i u ψ =ᵐ[configMeasure (N+1) oneMeasure]
      (fun x : Fin (N+1) → OneParticle => u (x i) * ψ (fun j => x (i.succAbove j))) := by
  dsimp only [CoulombPauli.insertOrbital, ContinuousLinearMap.comp_apply, tensorLeft_apply]
  exact (pull_ae _ _ _).trans ((splitAt_preserving i).quasiMeasurePreserving.ae (tensor_ae u ψ))

lemma oneTest_ae (φ : Test Space) (s : Fin 2) :
    tensor φ.toL2 (countVector s) =ᵐ[oneMeasure]
      (fun x : OneParticle => (φ.fn x.1 : ℂ) * (if x.2 = s then 1 else 0)) := by
  filter_upwards [tensor_ae φ.toL2 (countVector s),
    Measure.quasiMeasurePreserving_fst.ae φ.coe_toL2,
    Measure.quasiMeasurePreserving_snd.ae (countVector_ae s)] with x h1 h2 h3
  rw [h1,h2,h3]
  by_cases h : x.2 = s <;> simp [h]

lemma insertOrbital_manyTest {N : ℕ} (i : Fin (N+1)) (φ : Test Space) (η : Test (Configuration N))
    (s : Fin 2) (τ : Spins N) :
    CoulombPauli.insertOrbital i (tensor φ.toL2 (countVector s)) (manyTest η τ) =
      manyTest (insertTest i φ η) (Fin.insertNth i s τ) := by
  apply Lp.ext
  have h1 := (splitAt_preserving i).quasiMeasurePreserving.ae
    (Measure.quasiMeasurePreserving_fst.ae (oneTest_ae φ s))
  have h2 := (splitAt_preserving i).quasiMeasurePreserving.ae
    (Measure.quasiMeasurePreserving_snd.ae (manyTest_ae η τ))
  filter_upwards [insertOrbital_ae i (tensor φ.toL2 (countVector s)) (manyTest η τ),
    manyTest_ae (insertTest i φ η) (Fin.insertNth i s τ), h1, h2] with x hx hy hφ hη
  rw [hx,hy]
  change (tensor φ.toL2 (countVector s)) (x i) =
    (φ.fn (x i).1 : ℂ) * (if (x i).2 = s then 1 else 0) at hφ
  change manyTest η τ (fun j => x (i.succAbove j)) =
    (η.fn (fun j => (x (i.succAbove j)).1) : ℂ) *
      (if (fun j => (x (i.succAbove j)).2) = τ then 1 else 0) at hη
  rw [hφ,hη,insertTest_apply, Complex.ofReal_mul]
  have he : ((fun j => (x j).2) = Fin.insertNth i s τ) ↔
      (x i).2 = s ∧ (fun j => (x (i.succAbove j)).2) = τ := Fin.eq_insertNth_iff
  by_cases hs : (x i).2 = s <;> by_cases ht : (fun j => (x (i.succAbove j)).2) = τ <;>
    simp [he, hs, ht]
end CoulombAtom.Pauli

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_PullAdjoint
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
namespace CoulombPauli
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B}
lemma pull_adjoint_symm (e : A ≃ᵐ B) (he : MeasurePreserving e μ ν) (ψ : Lp ℂ 2 μ) :
    (pull e he).adjoint ψ = pull e.symm (he.symm e) ψ := by
  apply ext_inner_left ℂ
  intro φ
  rw [ContinuousLinearMap.adjoint_inner_right]
  calc
    _ = inner ℂ (pull e he φ) (pull e he (pull e.symm (he.symm e) ψ)) := by
      rw [pull_symm e he]
    _ = _ := pull_inner e he _ _
end CoulombPauli

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_Trace
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
namespace CoulombPackets

open CoulombPauli

lemma spinBasis_apply (s : Fin 2) : spinBasis s = spinVector s := by
  simp [spinBasis]

end CoulombPackets

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_FermionL2
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
namespace CoulombPackets
open CoulombPauli
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma splitFermion_norm {N : ℕ} (i : Fin (N+1)) (ψ : fermionL2 (V := V) (N+1)) :
    ‖splitFermion i ψ‖ = ‖ψ‖ := pull_norm _ _ _

lemma insert_adjoint_split {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 (spinSpaceMeasure (V := V)))
    (ψ : fermionL2 (V := V) (N+1)) :
    (insertOrbital i u).adjoint ψ = (tensorLeft u).adjoint (splitFermion i ψ) := by
  rw [insertOrbital, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    pull_adjoint_symm]
  rfl

end CoulombPackets

open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketFourier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology

namespace CoulombPauli
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]
lemma tensorRight_hasSum_general {ι κ : Type*}
    (a : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (b : HilbertBasis κ ℂ (Lp ℂ 2 ν)) (ψ : Lp ℂ 2 (μ.prod ν)) :
    HasSum (fun j => ‖(tensorRight (b j)).adjoint ψ‖^2) (‖ψ‖^2) := by
  have he := tensorRight_parseval a b ψ
  have ht : (∑' j, ENNReal.ofReal (‖(tensorRight (b j)).adjoint ψ‖^2)) ≠ ⊤ := by
    rw [he]; exact ENNReal.ofReal_ne_top
  have hh := ENNReal.hasSum_toReal ht
  rw [← ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top), he] at hh
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hh
end CoulombPauli

namespace CoulombPackets
open CoulombPauli CoulombSobolev
open scoped LineDeriv
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {B : Type*} [MeasurableSpace B] {ν : Measure B} [SigmaFinite ν]

lemma spinMarginal_weak_derivative
    {ψ u : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν)} {v : V}
    (hw : HasWeakSpinPartialDerivative ψ u v) (s : Fin 2) (w : Lp ℂ 2 ν) :
    CoulombAtom.HasWeakDirectionalDerivative (spinMarginal ψ s w) (spinMarginal u s w) v := by
  intro φ hφ hcφ
  let Φ : CoulombSobolev.Test V := ⟨φ,hφ,hcφ⟩
  have h : inner ℂ (Φ.deriv v).toL2 (spinMarginal ψ s w) +
      inner ℂ Φ.toL2 (spinMarginal u s w) = 0 := by
    simp only [spinMarginal, ContinuousLinearMap.adjoint_inner_right, tensorRight_apply]
    have hh := congrArg (fun z => inner ℂ w z) (hw Φ s)
    simpa only [inner_add_right, ContinuousLinearMap.adjoint_inner_right, tensorLeft_apply,
      inner_zero_right] using hh
  rw [CoulombSobolev.Test.inner_toL2, CoulombSobolev.Test.inner_toL2] at h
  apply eq_neg_of_add_eq_zero_left
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ (· + ·) _ rfl
  apply integral_congr_ae
  filter_upwards [] with x
  congr 2
  exact (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv

lemma spinMarginal_sum_norm (ψ : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν))
    (w : Lp ℂ 2 ν) :
    (∑ s : Fin 2, ‖spinMarginal ψ s w‖^2) = ‖(tensorRight w).adjoint ψ‖^2 := by
  obtain ⟨κ,a,-⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 (volume : Measure V))
  have h := tensorRight_hasSum_general a spinBasis ((tensorRight w).adjoint ψ)
  simpa only [tsum_fintype, spinBasis_apply, spinMarginal] using h.tsum_eq

end CoulombPackets

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_GradientVector
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombAtom.Pauli
open CoulombPauli CoulombSobolev CoulombPackets

lemma weak_test_identity {N : ℕ} (ψ : FormVector N) (hψ : FormAdmissible ψ)
    (i : Fin N) (a : Fin 3) (φ : Test (Configuration N)) (s : Spins N) :
    inner ℂ (manyTest (φ.deriv (direction i a)) s) (toMany ψ hψ.1) +
      inner ℂ (manyTest φ s) (gradientMany ψ hψ i a) = 0 := by
  have h2 : inner ℂ (manyTest φ s) (gradientMany ψ hψ i a) =
      ∫ x, ψ.gradient s i a x * (φ.fn x : ℂ) :=
    manyTest_inner (gradientVector ψ i a) (fun s => hψ.2.1 s i a) φ s
  rw [manyTest_inner, h2]
  have hw := hψ.2.2.1 s i a φ.fn φ.smooth φ.compact
  have he : (∫ x, ψ.value s x * ((φ.deriv (direction i a)).fn x : ℂ)) =
      ∫ x, ψ.value s x * Complex.ofReal (lineDeriv ℝ φ.fn x (direction i a)) := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [(φ.smooth.differentiable (by simp) x).lineDeriv_eq_fderiv]
    rfl
  rw [he,hw]
  simp

lemma form_hasFermionGradient {N : ℕ} (ψ : FormVector (N+1)) (hψ : FormAdmissible ψ) :
    HasFermionGradient (EuclideanSpace.basisFun (Fin 3) ℝ) (toMany ψ hψ.1)
      (gradientMany ψ hψ) := by
  intro i a φ s
  apply manyTest_total
  intro η τ
  rw [inner_add_right]
  change inner ℂ (manyTest η τ)
      ((tensorLeft (tensor (φ.deriv ((EuclideanSpace.basisFun (Fin 3) ℝ) a)).toL2 (countVector s))).adjoint
        (splitFermion i (toMany ψ hψ.1))) +
    inner ℂ (manyTest η τ) ((tensorLeft (tensor φ.toL2 (countVector s))).adjoint
        (splitFermion i (gradientMany ψ hψ i a))) = 0
  rw [← insert_adjoint_split, ← insert_adjoint_split,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    insertOrbital_manyTest, insertOrbital_manyTest]
  rw [EuclideanSpace.basisFun_apply, ← insertTest_deriv]
  exact weak_test_identity ψ hψ i a (insertTest i φ η) (Fin.insertNth i s τ)

lemma gradientMany_norm_sq {N : ℕ} (ψ : FormVector N) (hψ : FormAdmissible ψ)
    (i : Fin N) (a : Fin 3) :
    ‖gradientMany ψ hψ i a‖^2 = ∑ s : Spins N, ∫ x, ‖ψ.gradient s i a x‖^2 := by
  exact toMany_norm_sq (gradientVector ψ i a) (fun s => hψ.2.1 s i a)

end CoulombAtom.Pauli

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_IntegralFourierInvMul
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace CoulombAtom
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma integral_fourierInv_mul {f g : V → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ ξ, (𝓕⁻ f) ξ * g ξ) = ∫ x, f x * (𝓕⁻ g) x := by
  have he := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := -(innerₗ V)) Real.continuous_fourierChar
    ((innerSL ℝ).continuous₂.neg) hf hg
  have hflip : (-(innerₗ V)).flip = -(innerₗ V) := by
    ext x y
    exact congrArg Neg.neg (real_inner_comm x y)
  change (∫ ξ, VectorFourier.fourierIntegral Real.fourierChar volume (-(innerₗ V)) f ξ * g ξ) =
    ∫ x, f x * VectorFourier.fourierIntegral Real.fourierChar volume (-(innerₗ V)) g x
  simpa only [smul_eq_mul, hflip] using he

lemma l2_fourierInv_ae_classical {f : V → ℂ} (hf : MemLp f 2) (hfi : Integrable f) :
    (fun ξ => (𝓕⁻ (hf.toLp f) : Lp ℂ 2 volume) ξ) =ᵐ[volume] (𝓕⁻ f) := by
  have hc : Continuous (𝓕⁻ f) := by
    have he : 𝓕⁻ f = fun x => (𝓕 f) (-x) := funext (Real.fourierInv_eq_fourier_neg f)
    rw [he]
    exact (classical_fourier_continuous hfi).comp continuous_neg
  apply ae_eq_of_integral_contDiff_smul_eq
    (Lp.memLp (𝓕⁻ (hf.toLp f)) |>.locallyIntegrable (by norm_num))
    hc.locallyIntegrable
  intro φ hφ hcompact
  let ψ : 𝓢(V, ℂ) := (hcompact.comp_left rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hφ)
  have hd := congrArg (fun d : 𝓢'(V, ℂ) => d ψ)
    (Lp.fourierInv_toTemperedDistribution_eq (hf.toLp f))
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] at hd
  simp only [Complex.real_smul]
  change (∫ ξ, ψ ξ * (𝓕⁻ (hf.toLp f) : Lp ℂ 2 volume) ξ) = ∫ ξ, ψ ξ * (𝓕⁻ f) ξ
  rw [← hd]
  calc
    _ = ∫ x, (𝓕⁻ (ψ : V → ℂ)) x * f x := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]
      simp only [SchwartzMap.fourierInv_coe]
    _ = _ := integral_fourierInv_mul ψ.integrable hfi
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_FreqCut
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace CoulombLT

section
open CoulombAtom Metric
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma l2_norm_sq_eq_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (f : Lp ℂ 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def]
  simp only [inner_self_eq_norm_sq_to_K]
  change (∫ x, (‖f x‖ : ℂ)^2 ∂μ).re = _
  simp_rw [← Complex.ofReal_pow]
  rw [integral_complex_ofReal]
  rfl

lemma l2_ball_integrable (f : Lp ℂ 2 (volume : Measure V)) (R : ℝ) :
    Integrable ((ball 0 R).indicator (fun ξ => f ξ)) := by
  have : IsFiniteMeasure ((volume : Measure V).restrict (ball 0 R)) :=
    ⟨by simpa using measure_ball_lt_top (x := (0:V)) (r := R)⟩
  apply IntegrableOn.integrable_indicator _ measurableSet_ball
  exact memLp_one_iff_integrable.mp (((Lp.memLp f).restrict (ball 0 R)).mono_exponent (by norm_num))

lemma freqCut_ae (R : ℝ) (f : Lp ℂ 2 (volume : Measure V)) :
    (fun ξ => freqCut R f ξ) =ᵐ[volume] (ball 0 R).indicator (fun ξ => f ξ) :=
  ((Lp.memLp f).indicator (measurableSet_ball (x := (0:V)) (ε := R))).coeFn_toLp

lemma lowPart_ae (R : ℝ) (f : Lp ℂ 2 (volume : Measure V)) :
    (fun x => (𝓕⁻ (freqCut R (𝓕 f)) : Lp ℂ 2 volume) x) =ᵐ[volume] lowPart R f :=
  l2_fourierInv_ae_classical ((Lp.memLp (𝓕 f)).indicator (measurableSet_ball (x := (0:V)) (ε := R)))
    (l2_ball_integrable (𝓕 f) R)

lemma highPart_norm_sq (R : ℝ) (f : Lp ℂ 2 (volume : Measure V)) :
    (∫ x, ‖f x - lowPart R f x‖^2) =
      ∫ ξ in (ball 0 R)ᶜ, ‖(𝓕 f : Lp ℂ 2 volume) ξ‖^2 := by
  have hi : (fun x => (f - 𝓕⁻ (freqCut R (𝓕 f)) : Lp ℂ 2 volume) x) =ᵐ[volume]
      (fun x => f x - lowPart R f x) := by
    filter_upwards [Lp.coeFn_sub f (𝓕⁻ (freqCut R (𝓕 f))), lowPart_ae R f] with x hx hy
    simpa only [Pi.sub_apply,hy] using hx
  calc
    _ = ‖f - 𝓕⁻ (freqCut R (𝓕 f))‖^2 := by
      rw [l2_norm_sq_eq_integral]
      exact integral_congr_ae (hi.symm.fun_comp (fun z => ‖z‖^2))
    _ = ‖(𝓕 f : Lp ℂ 2 volume) - freqCut R (𝓕 f)‖^2 := by
      rw [← Lp.norm_fourier_eq]
      change ‖(Lp.fourierTransformₗᵢ V ℂ) (f - 𝓕⁻ (freqCut R (𝓕 f)))‖^2 = _
      rw [map_sub]
      change ‖(𝓕 f : Lp ℂ 2 volume) - 𝓕 (𝓕⁻ (freqCut R (𝓕 f)))‖^2 = _
      rw [FourierInvPair.fourier_fourierInv_eq]
    _ = _ := by
      rw [l2_norm_sq_eq_integral, ← integral_indicator measurableSet_ball.compl]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (𝓕 f) (freqCut R (𝓕 f)),
        freqCut_ae R (𝓕 f)] with x hx hy
      simp only [Pi.sub_apply] at hx
      rw [hx]
      rw [hy]
      by_cases h : x ∈ ball (0:V) R <;> simp [h]
end

open CoulombAtom Metric ComplexConjugate
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma lowKernel_norm_sq (R : ℝ) (x : V) :
    ‖lowKernel R x‖^2 = (volume : Measure V).real (ball 0 R) := by
  rw [l2_norm_sq_eq_integral]
  have he : (fun ξ => ‖lowKernel R x ξ‖^2) =ᵐ[volume]
      (ball 0 R).indicator (fun _ => (1:ℝ)) := by
    filter_upwards [(kernelFunction_memLp R x).coeFn_toLp] with ξ hξ
    change ‖(kernelFunction_memLp R x).toLp _ ξ‖^2 = _
    rw [hξ]
    by_cases h : ξ ∈ ball (0:V) R <;> simp [kernelFunction,h,Circle.norm_coe]
  rw [integral_congr_ae he,integral_indicator measurableSet_ball,integral_const]
  simp [Measure.real]

lemma lowPart_eq_inner (R : ℝ) (f : Lp ℂ 2 (volume : Measure V)) (x : V) :
    lowPart R f x = inner ℂ (lowKernel R x) (𝓕 f) := by
  rw [lowPart,Real.fourierInv_eq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(kernelFunction_memLp R x).coeFn_toLp] with ξ hξ
  change _ = inner ℂ ((kernelFunction_memLp R x).toLp _ ξ) _
  rw [hξ,RCLike.inner_apply]
  by_cases h : ξ ∈ ball (0:V) R <;>
    simp [kernelFunction,h,Circle.smul_def,smul_eq_mul,mul_comm]

variable {ι : Type*} [Fintype ι]

lemma BesselFamily.fourier {f : ι → Lp ℂ 2 (volume : Measure V)}
    (hf : BesselFamily f) : BesselFamily (fun j => 𝓕 (f j)) := by
  intro u
  have h := hf (𝓕⁻ u)
  have hi (j) : inner ℂ u (𝓕 (f j)) = inner ℂ (𝓕⁻ u) (f j) := by
    simpa only [FourierInvPair.fourier_fourierInv_eq] using (Lp.inner_fourier_eq (𝓕⁻ u) (f j))
  have hn : ‖(𝓕⁻ u : Lp ℂ 2 volume)‖ = ‖u‖ := by
    simpa only [FourierInvPair.fourier_fourierInv_eq] using (Lp.norm_fourier_eq (𝓕⁻ u)).symm
  simpa only [hi,hn] using h

lemma BesselFamily.low_bound {f : ι → Lp ℂ 2 (volume : Measure V)}
    (hf : BesselFamily f) (R : ℝ) (x : V) :
    (∑ j, ‖lowPart R (f j) x‖^2) ≤ (volume : Measure V).real (ball 0 R) := by
  simpa only [lowPart_eq_inner,lowKernel_norm_sq] using hf.fourier (lowKernel R x)

lemma family_density_split (f : ι → Lp ℂ 2 (volume : Measure V)) (R : ℝ) (x : V) :
    (∑ j, ‖f j x‖^2) ≤ 2*(∑ j, ‖lowPart R (f j) x‖^2) +
      2*(∑ j, ‖f j x - lowPart R (f j) x‖^2) := by
  rw [Finset.mul_sum,Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have h : ‖f j x‖ ≤ ‖lowPart R (f j) x‖ + ‖f j x - lowPart R (f j) x‖ := by
    convert norm_add_le (lowPart R (f j) x) (f j x - lowPart R (f j) x) using 1; abel_nf
  have hs := pow_le_pow_left₀ (norm_nonneg (f j x)) h 2
  nlinarith [sq_nonneg (‖lowPart R (f j) x‖ - ‖f j x - lowPart R (f j) x‖)]
end CoulombLT

open MeasureTheory Filter
open scoped ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_DyadicPowerSq
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombLT
lemma dyadic_power_sq (n : ℕ) : ((2:ℝ)^n)^2 = (4:ℝ)^n := by
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
  norm_num
lemma dyadic_power_cube (n : ℕ) : ((2:ℝ)^n)^3 = (8:ℝ)^n := by
  rw [← pow_mul, Nat.mul_comm n 3, pow_mul]
  norm_num

lemma dyadic_sum_bound (r : ℝ) (_hr : 0 ≤ r) (M : ℕ) :
    (∑ n ∈ Finset.range M, if (2:ℝ)^n ≤ r then (4:ℝ)^n else 0) ≤ (4/3:ℝ)*r^2 := by
  have hgeom (M : ℕ) :
      (∑ n ∈ Finset.range M, if (2:ℝ)^n ≤ r then (4:ℝ)^n else 0) ≤
        ((4:ℝ)^M-1)/3 := by
    have h := Finset.sum_le_sum (s := Finset.range M)
      (f := fun n => if (2:ℝ)^n ≤ r then (4:ℝ)^n else 0)
      (g := fun n => (4:ℝ)^n) (fun n _ => by split_ifs; rfl; positivity)
    have he := geom_sum_mul (4:ℝ) M
    nlinarith
  induction M with
  | zero => simp; positivity
  | succ M ih =>
    rw [Finset.sum_range_succ]
    split_ifs with h
    · have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (2:ℝ)^M) h 2
      rw [dyadic_power_sq] at hp
      linarith [hgeom M]
    · simpa using ih

lemma dyadic_tsum_bound (r : ℝ) (hr : 0 ≤ r) :
    (∑' n : ℕ, ENNReal.ofReal (if (2:ℝ)^n ≤ r then (4:ℝ)^n else 0)) ≤
      ENNReal.ofReal ((4/3:ℝ)*r^2) := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro M
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => by split_ifs <;> positivity)]
  exact ENNReal.ofReal_le_ofReal (dyadic_sum_bound r hr M)

lemma rpow_two_thirds_cube {r : ℝ} (hr : 0 ≤ r) :
    (r^3) ^ (2/3:ℝ) = r^2 := by
  rw [← Real.rpow_natCast_mul hr]
  norm_num

lemma dyadic_density_bound {ρ : ℝ} (hρ : 0 ≤ ρ) (H : ℕ → ℝ)
    (_hH : ∀ n, 0 ≤ H n)
    (hsplit : ∀ n, ρ ≤ 16*((2:ℝ)^n)^3 + 2*H n) :
    ENNReal.ofReal (ρ^(5/3:ℝ)) ≤
      16*ENNReal.ofReal ρ + 256*(∑' n : ℕ, ENNReal.ofReal ((4:ℝ)^n*H n)) := by
  have hpow : ρ^(5/3:ℝ) = ρ * ρ^(2/3:ℝ) := by
    by_cases hzero : ρ = 0
    · simp [hzero]
    · rw [show (5/3:ℝ) = 1+2/3 by norm_num, Real.rpow_add (lt_of_le_of_ne hρ (Ne.symm hzero)), Real.rpow_one]
  by_cases hsmall : ρ ≤ 64
  · have hp : ρ^(2/3:ℝ) ≤ 16 := by
      calc
        _ ≤ ((4:ℝ)^3)^(2/3:ℝ) := Real.rpow_le_rpow hρ (by norm_num; exact hsmall) (by norm_num)
        _ = 16 := by rw [rpow_two_thirds_cube (by norm_num)]; norm_num
    have h := ENNReal.ofReal_le_ofReal (show ρ^(5/3:ℝ) ≤ 16*ρ by rw [hpow]; nlinarith)
    have he : ENNReal.ofReal (16*ρ) = 16*ENNReal.ofReal ρ := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
    rw [he] at h
    exact h.trans (le_add_right le_rfl)
  · have hbig : 1 ≤ ρ/64 := by linarith
    obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near hbig (by norm_num : (1:ℝ)<8)
    have hp : ρ^(2/3:ℝ) ≤ 64*(4:ℝ)^n := by
      have hx : ρ ≤ (8*(2:ℝ)^n)^3 := by
        rw [mul_pow,dyadic_power_cube]
        rw [pow_succ] at hn'
        norm_num only [show (8:ℝ)^3 = 512 by norm_num]
        linarith
      calc
        _ ≤ ((8*(2:ℝ)^n)^3)^(2/3:ℝ) := Real.rpow_le_rpow hρ hx (by norm_num)
        _ = 64*(4:ℝ)^n := by
          rw [rpow_two_thirds_cube (by positivity),mul_pow,dyadic_power_sq]
          norm_num
    have hlow : 64*((2:ℝ)^n)^3 ≤ ρ := by rw [dyadic_power_cube]; linarith
    have hhigh : ρ ≤ 4*H n := by nlinarith [hsplit n]
    have hbound : ρ^(5/3:ℝ) ≤ 256*((4:ℝ)^n*H n) := by
      rw [hpow]
      calc
        _ ≤ ρ*(64*(4:ℝ)^n) := mul_le_mul_of_nonneg_left hp hρ
        _ ≤ (4*H n)*(64*(4:ℝ)^n) := mul_le_mul_of_nonneg_right hhigh (by positivity)
        _ = _ := by ring
    have he : ENNReal.ofReal (256*((4:ℝ)^n*H n)) =
        256*ENNReal.ofReal ((4:ℝ)^n*H n) := by
      rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
    calc
      _ ≤ ENNReal.ofReal (256*((4:ℝ)^n*H n)) := ENNReal.ofReal_le_ofReal hbound
      _ = 256*ENNReal.ofReal ((4:ℝ)^n*H n) := he
      _ ≤ 256*(∑' n : ℕ, ENNReal.ofReal ((4:ℝ)^n*H n)) := by
        gcongr
        exact ENNReal.le_tsum (f := fun index : ℕ => ENNReal.ofReal ((4:ℝ)^index*H index)) n
      _ ≤ _ := le_add_left le_rfl

open CoulombAtom Metric

lemma ball_volume_le (R : ℝ) (hR : 0 ≤ R) :
    (volume : Measure Space).real (ball 0 R) ≤ 8*R^3 := by
  rw [Measure.real,EuclideanSpace.volume_ball_fin_three,ENNReal.toReal_mul,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal hR,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
  have h := Real.pi_lt_four
  nlinarith [pow_nonneg hR 3]

variable {ι : Type*} [Fintype ι]

lemma familyDensity_nonneg (f : ι → Lp ℂ 2 (volume : Measure Space)) (x : Space) :
    0 ≤ familyDensity f x := Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma highDensity_nonneg (f : ι → Lp ℂ 2 (volume : Measure Space)) (n : ℕ) (x : Space) :
    0 ≤ highDensity f n x := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma familyDensity_integrable (f : ι → Lp ℂ 2 (volume : Measure Space)) :
    Integrable (familyDensity f) := by
  apply integrable_finsetSum
  intro j _
  exact memLp_two_iff_integrable_sq_norm (Lp.memLp (f j)).aestronglyMeasurable |>.mp (Lp.memLp (f j))

lemma highPart_integrable (R : ℝ) (f : Lp ℂ 2 (volume : Measure Space)) :
    Integrable (fun x => ‖f x - lowPart R f x‖^2) := by
  have hi : (fun x => (f - 𝓕⁻ (freqCut R (𝓕 f)) : Lp ℂ 2 volume) x) =ᵐ[volume]
      (fun x => f x - lowPart R f x) := by
    filter_upwards [Lp.coeFn_sub f (𝓕⁻ (freqCut R (𝓕 f))), lowPart_ae R f] with x hx hy
    simpa only [Pi.sub_apply,hy] using hx
  have hm := MemLp.ae_eq hi (Lp.memLp (f - 𝓕⁻ (freqCut R (𝓕 f))))
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

lemma highDensity_integrable (f : ι → Lp ℂ 2 (volume : Measure Space)) (n : ℕ) :
    Integrable (highDensity f n) :=
  integrable_finsetSum Finset.univ (fun j _ => highPart_integrable _ (f j))

lemma familyDensity_pointwise {f : ι → Lp ℂ 2 (volume : Measure Space)}
    (hf : BesselFamily f) (x : Space) :
    ENNReal.ofReal (familyDensity f x ^(5/3:ℝ)) ≤
      16*ENNReal.ofReal (familyDensity f x) +
      256*(∑' n : ℕ, ENNReal.ofReal ((4:ℝ)^n*highDensity f n x)) := by
  apply dyadic_density_bound (familyDensity_nonneg f x) _ (fun n => highDensity_nonneg f n x)
  intro n
  have h := family_density_split f ((2:ℝ)^n) x
  have hb := (hf.low_bound ((2:ℝ)^n) x).trans (ball_volume_le _ (by positivity))
  change familyDensity f x ≤ 16*((2:ℝ)^n)^3 + 2*highDensity f n x
  dsimp [familyDensity,highDensity]
  linarith

lemma highPart_lintegral (R : ℝ) (f : Lp ℂ 2 (volume : Measure Space)) :
    (∫⁻ x, ENNReal.ofReal (‖f x-lowPart R f x‖^2)) =
      ∫⁻ ξ in (ball 0 R)ᶜ, ENNReal.ofReal (‖(𝓕 f : Lp ℂ 2 volume) ξ‖^2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (highPart_integrable R f)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _),highPart_norm_sq]
  apply ofReal_integral_eq_lintegral_ofReal
  · exact ((memLp_two_iff_integrable_sq_norm (Lp.memLp (𝓕 f)).aestronglyMeasurable).mp
      (Lp.memLp (𝓕 f))).restrict
  · exact Filter.Eventually.of_forall fun _ => sq_nonneg _

lemma highDensity_lintegral (f : ι → Lp ℂ 2 (volume : Measure Space)) (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (highDensity f n x)) =
      ∫⁻ ξ in (ball 0 ((2:ℝ)^n))ᶜ, ENNReal.ofReal (familyDensity (fun j => 𝓕 (f j)) ξ) := by
  calc
    _ = ∫⁻ x, ∑ j, ENNReal.ofReal (‖f j x - lowPart ((2:ℝ)^n) (f j) x‖^2) := by
      apply lintegral_congr
      intro x
      exact ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)
    _ = ∑ j, ∫⁻ x, ENNReal.ofReal (‖f j x - lowPart ((2:ℝ)^n) (f j) x‖^2) := by
      apply lintegral_finsetSum'
      intro j _
      exact (highPart_integrable _ (f j)).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    _ = ∑ j, ∫⁻ ξ in (ball 0 ((2:ℝ)^n))ᶜ,
        ENNReal.ofReal (‖(𝓕 (f j) : Lp ℂ 2 volume) ξ‖^2) := by
      apply Finset.sum_congr rfl
      intro j _
      exact highPart_lintegral _ (f j)
    _ = ∫⁻ ξ in (ball 0 ((2:ℝ)^n))ᶜ,
        ∑ j, ENNReal.ofReal (‖(𝓕 (f j) : Lp ℂ 2 volume) ξ‖^2) := by
      symm
      apply lintegral_finsetSum'
      intro j _
      exact (((Lp.memLp (𝓕 (f j))).aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal).restrict
    _ = _ := by
      apply lintegral_congr
      intro ξ
      exact (ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)).symm

lemma density_mass (f : ι → Lp ℂ 2 (volume : Measure Space)) :
    (∫⁻ x, ENNReal.ofReal (familyDensity f x)) =
      ENNReal.ofReal (∑ j, ‖f j‖^2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (familyDensity_integrable f)
    (Filter.Eventually.of_forall (familyDensity_nonneg f))]
  congr 1
  change (∫ x, ∑ j, ‖f j x‖^2) = _
  rw [integral_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm (Lp.memLp (f j)).aestronglyMeasurable).mp (Lp.memLp (f j)))]
  simp only [← l2_norm_sq_eq_integral]

lemma dyadic_kinetic_bound (f : ι → Lp ℂ 2 (volume : Measure Space)) :
    (∑' n : ℕ, ENNReal.ofReal ((4:ℝ)^n) * ∫⁻ x, ENNReal.ofReal (highDensity f n x)) ≤
      ENNReal.ofReal (4/3:ℝ) *
      ∫⁻ ξ, ENNReal.ofReal (‖ξ‖^2 * familyDensity (fun j => 𝓕 (f j)) ξ) := by
  let d := familyDensity (fun j => 𝓕 (f j))
  have hm : AEMeasurable (fun ξ => ENNReal.ofReal (d ξ)) volume :=
    (familyDensity_integrable _).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hpoint (ξ : Space) :
      (∑' n : ℕ, (ball 0 ((2:ℝ)^n))ᶜ.indicator
        (fun ξ => ENNReal.ofReal ((4:ℝ)^n) * ENNReal.ofReal (d ξ)) ξ) ≤
        ENNReal.ofReal (4/3:ℝ) * ENNReal.ofReal (‖ξ‖^2*d ξ) := by
    have he (n : ℕ) :
        (ball 0 ((2:ℝ)^n))ᶜ.indicator
          (fun ξ => ENNReal.ofReal ((4:ℝ)^n) * ENNReal.ofReal (d ξ)) ξ =
        ENNReal.ofReal (if (2:ℝ)^n ≤ ‖ξ‖ then (4:ℝ)^n else 0) * ENNReal.ofReal (d ξ) := by
      by_cases h : (2:ℝ)^n ≤ ‖ξ‖
      · simp [Set.indicator,Metric.mem_ball,dist_zero_right,not_lt.mpr h,h]
      · simp [Set.indicator,Metric.mem_ball,dist_zero_right,not_le.mp h,h]
    simp_rw [he]
    rw [ENNReal.tsum_mul_right]
    have hb := dyadic_tsum_bound ‖ξ‖ (norm_nonneg ξ)
    calc
      _ ≤ ENNReal.ofReal ((4/3:ℝ)*‖ξ‖^2) * ENNReal.ofReal (d ξ) := by gcongr
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (sq_nonneg _)]; ac_rfl
  calc
    _ = ∑' n : ℕ, ∫⁻ ξ, (ball 0 ((2:ℝ)^n))ᶜ.indicator
        (fun ξ => ENNReal.ofReal ((4:ℝ)^n)*ENNReal.ofReal (d ξ)) ξ := by
      apply tsum_congr
      intro n
      rw [highDensity_lintegral,lintegral_indicator measurableSet_ball.compl,
        lintegral_const_mul'' _ (hm.restrict)]
    _ = ∫⁻ ξ, ∑' n : ℕ, (ball 0 ((2:ℝ)^n))ᶜ.indicator
        (fun ξ => ENNReal.ofReal ((4:ℝ)^n)*ENNReal.ofReal (d ξ)) ξ := by
      symm
      apply lintegral_tsum
      intro n
      exact (hm.const_mul _).indicator measurableSet_ball.compl
    _ ≤ ∫⁻ ξ, ENNReal.ofReal (4/3:ℝ) * ENNReal.ofReal (‖ξ‖^2*d ξ) :=
      lintegral_mono hpoint
    _ = _ := by
      have hm' : AEMeasurable (fun ξ : Space => ENNReal.ofReal (‖ξ‖^2*d ξ)) volume :=
        ((continuous_norm.pow 2).aestronglyMeasurable.mul
          (familyDensity_integrable _).aestronglyMeasurable).aemeasurable.ennreal_ofReal
      exact lintegral_const_mul'' _ hm'

theorem finite_lieb_thirring_lintegral {f : ι → Lp ℂ 2 (volume : Measure Space)}
    (hf : BesselFamily f) :
    (∫⁻ x, ENNReal.ofReal (familyDensity f x ^(5/3:ℝ))) ≤
      16*ENNReal.ofReal (∑ j, ‖f j‖^2) + ENNReal.ofReal (1024/3:ℝ) *
        ∫⁻ ξ, ENNReal.ofReal (‖ξ‖^2 * familyDensity (fun j => 𝓕 (f j)) ξ) := by
  have hm : AEMeasurable (fun x => ENNReal.ofReal (familyDensity f x)) volume :=
    (familyDensity_integrable f).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hH (n : ℕ) : AEMeasurable
      (fun x => ENNReal.ofReal ((4:ℝ)^n* highDensity f n x)) volume :=
    ((highDensity_integrable f n).const_mul _).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hT : AEMeasurable (fun x => ∑' n : ℕ, ENNReal.ofReal ((4:ℝ)^n*highDensity f n x)) volume :=
    AEMeasurable.tsum hH
  calc
    _ ≤ ∫⁻ x, 16*ENNReal.ofReal (familyDensity f x) +
        256*(∑' n : ℕ, ENNReal.ofReal ((4:ℝ)^n*highDensity f n x)) :=
      lintegral_mono (familyDensity_pointwise hf)
    _ = 16*ENNReal.ofReal (∑ j, ‖f j‖^2) +
        256*(∑' n : ℕ, ENNReal.ofReal ((4:ℝ)^n)*∫⁻ x, ENNReal.ofReal (highDensity f n x)) := by
      rw [lintegral_add_left' (hm.const_mul _), lintegral_const_mul'' _ hm,
        density_mass, lintegral_const_mul'' _ hT, lintegral_tsum hH]
      congr 2
      apply tsum_congr
      intro n
      simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (4:ℝ)^n)]
      exact lintegral_const_mul'' _
        (highDensity_integrable f n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    _ ≤ 16*ENNReal.ofReal (∑ j, ‖f j‖^2) +
        256*(ENNReal.ofReal (4/3:ℝ)*∫⁻ ξ,
          ENNReal.ofReal (‖ξ‖^2*familyDensity (fun j => 𝓕 (f j)) ξ)) := by
      gcongr
      exact dyadic_kinetic_bound f
    _ = _ := by
      rw [← mul_assoc]
      congr 2
      calc
        _ = ENNReal.ofReal ((256:ℝ)*(4/3)) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          norm_num
        _ = _ := by norm_num
end CoulombLT

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_InfiniteDensity
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombLT
open CoulombAtom Metric
variable {ι : Type*}

lemma finite_fourierMoment [Fintype ι] (f : ι → Lp ℂ 2 (volume : Measure Space)) :
    (∫⁻ ξ, ENNReal.ofReal (‖ξ‖^2*familyDensity (fun j => 𝓕 (f j)) ξ)) =
    ∑ j, fourierMoment (f j) := by
  have he (ξ : Space) :
      ENNReal.ofReal (‖ξ‖^2*familyDensity (fun j => 𝓕 (f j)) ξ) =
      ∑ j, ENNReal.ofReal (‖ξ‖^2*‖(𝓕 (f j) : Lp ℂ 2 volume) ξ‖^2) := by
    rw [familyDensity, Finset.mul_sum]
    exact ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  simp_rw [he]
  apply lintegral_finsetSum'
  intro j _
  exact ((continuous_norm.pow 2).aestronglyMeasurable.mul
    ((Lp.memLp (𝓕 (f j))).aestronglyMeasurable.norm.pow 2)).aemeasurable.ennreal_ofReal

lemma infiniteDensity_rpow (f : ι → Lp ℂ 2 (volume : Measure Space)) (x : Space) :
    infiniteDensity f x ^ (5/3:ℝ) =
      ⨆ s : Finset ι, ENNReal.ofReal ((∑ j ∈ s, ‖f j x‖^2)^(5/3:ℝ)) := by
  rw [infiniteDensity, ENNReal.tsum_eq_iSup_sum]
  change (ENNReal.orderIsoRpow (5/3:ℝ) (by norm_num)) _ = _
  rw [OrderIso.map_iSup]
  congr 1
  funext s
  change (∑ j ∈ s, ENNReal.ofReal (‖f j x‖^2)) ^ (5/3:ℝ) = _
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
  exact ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg _)) (by norm_num)

theorem countable_lieb_thirring_lintegral [Countable ι]
    {f : ι → Lp ℂ 2 (volume : Measure Space)}
    (hf : ∀ s : Finset ι, BesselFamily (fun j : s => f j)) :
    (∫⁻ x, infiniteDensity f x ^ (5/3:ℝ)) ≤
      16*(∑' j, ENNReal.ofReal (‖f j‖^2)) +
        ENNReal.ofReal (1024/3:ℝ)*(∑' j, fourierMoment (f j)) := by
  classical
  have hm (s : Finset ι) : AEMeasurable
      (fun x => ENNReal.ofReal ((∑ j ∈ s, ‖f j x‖^2)^(5/3:ℝ))) volume := by
    have hi : Integrable (fun x => ∑ j ∈ s, ‖f j x‖^2) volume :=
      integrable_finsetSum s (fun j _ =>
        (memLp_two_iff_integrable_sq_norm (Lp.memLp (f j)).aestronglyMeasurable).mp (Lp.memLp (f j)))
    have h := hi.aestronglyMeasurable
    exact ((Real.continuous_rpow_const (by norm_num : (0:ℝ)≤5/3)).comp_aestronglyMeasurable h).aemeasurable.ennreal_ofReal
  have hmono (s t : Finset ι) (h : s ⊆ t) (x : Space) :
      ENNReal.ofReal ((∑ j ∈ s, ‖f j x‖^2)^(5/3:ℝ)) ≤
      ENNReal.ofReal ((∑ j ∈ t, ‖f j x‖^2)^(5/3:ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) _ (by norm_num)
    exact Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => sq_nonneg _)
  simp_rw [infiniteDensity_rpow]
  rw [lintegral_iSup_directed hm (fun s t =>
    ⟨s ∪ t, hmono s (s ∪ t) Finset.subset_union_left,
      hmono t (s ∪ t) Finset.subset_union_right⟩)]
  apply iSup_le
  intro s
  have hb := finite_lieb_thirring_lintegral (hf s)
  rw [finite_fourierMoment, ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)] at hb
  have he (x : Space) : familyDensity (fun j : s => f j) x = ∑ j ∈ s, ‖f j x‖^2 := by
    exact Finset.sum_coe_sort s (fun j => ‖f j x‖^2)
  simp_rw [he] at hb
  refine hb.trans ?_
  apply add_le_add
  · gcongr
    rw [Finset.sum_coe_sort s (fun j => ENNReal.ofReal (‖f j‖^2))]
    exact ENNReal.sum_le_tsum s
  · gcongr
    rw [Finset.sum_coe_sort s (fun j => fourierMoment (f j))]
    exact ENNReal.sum_le_tsum s
end CoulombLT

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FourierMomentGradient
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombLT

section
open CoulombAtom
lemma fourierMoment_le_gradient {f : Lp ℂ 2 (volume : Measure Space)}
    {g : Fin 3 → Lp ℂ 2 (volume : Measure Space)}
    (hw : ∀ a, HasWeakDirectionalDerivative f (g a) (EuclideanSpace.single a 1)) :
    fourierMoment f ≤ ENNReal.ofReal (∑ a, ‖g a‖^2) := by
  have he := weak_fourier_kinetic (EuclideanSpace.basisFun (Fin 3) ℝ)
    (Lp.memLp f) (fun a => Lp.memLp (g a)) (fun a => by simpa using hw a)
  simp only [Lp.toLp_coeFn] at he
  have hp : 1 ≤ (2*Real.pi)^2 := by nlinarith [Real.pi_gt_three]
  calc
    _ ≤ ∫⁻ ξ, ENNReal.ofReal ((2*Real.pi)^2*‖ξ‖^2*‖(𝓕 f : Lp ℂ 2 volume) ξ‖^2) := by
      apply lintegral_mono
      intro ξ
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_nonneg (sq_nonneg ‖ξ‖) (sq_nonneg ‖(𝓕 f : Lp ℂ 2 volume) ξ‖)]
    _ = ENNReal.ofReal (∑ a, ∫ x, ‖g a x‖^2) := by
      rw [← ofReal_integral_eq_lintegral_ofReal he.1
        (Filter.Eventually.of_forall (fun _ => by positivity)), he.2]
    _ = _ := by simp only [← l2_norm_sq_eq_integral]

variable {ι : Type*} [Countable ι]
theorem weak_family_lieb_thirring {f : ι → Lp ℂ 2 (volume : Measure Space)}
    {g : Fin 3 → ι → Lp ℂ 2 (volume : Measure Space)}
    (hf : ∀ s : Finset ι, BesselFamily (fun j : s => f j))
    (hw : ∀ a j, HasWeakDirectionalDerivative (f j) (g a j) (EuclideanSpace.single a 1)) :
    (∫⁻ x, infiniteDensity f x ^ (5/3:ℝ)) ≤
      16*(∑' j, ENNReal.ofReal (‖f j‖^2)) +
        ENNReal.ofReal (1024/3:ℝ)*(∑ a, ∑' j, ENNReal.ofReal (‖g a j‖^2)) := by
  apply (countable_lieb_thirring_lintegral hf).trans
  apply add_le_add_right
  gcongr
  calc
    _ ≤ ∑' j, ENNReal.ofReal (∑ a, ‖g a j‖^2) :=
      ENNReal.tsum_le_tsum (fun j => fourierMoment_le_gradient (fun a => hw a j))
    _ = _ := by
      simp_rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => sq_nonneg _)]
      simpa only [tsum_fintype] using (ENNReal.tsum_comm (f := fun j a => ENNReal.ofReal (‖g a j‖^2)))
end

open CoulombPauli CoulombPackets
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma besselFamily_of_unit {ι : Type*} [Fintype ι]
    {f : ι → Lp ℂ 2 (volume : Measure V)}
    (h : ∀ u : Lp ℂ 2 (volume : Measure V), ‖u‖ = 1 →
      (∑ j, ‖inner ℂ u (f j)‖^2) ≤ 1) : BesselFamily f := by
  intro u
  by_cases hu : u = 0
  · simp [hu]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  let v : Lp ℂ 2 (volume : Measure V) := ((‖u‖⁻¹ : ℝ) : ℂ) • u
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn]
  have hh := h v hv
  have hi (j : ι) : ‖inner ℂ v (f j)‖^2 = ‖u‖⁻¹^2 * ‖inner ℂ u (f j)‖^2 := by
    simp only [v, inner_smul_left, norm_mul, starRingEnd_apply, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg _), mul_pow]
  simp_rw [hi, ← Finset.mul_sum] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖u‖)
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hn, one_pow, one_mul, mul_one] at hh'
  exact hh'

lemma spinMarginal_coefficient {B : Type*} [MeasurableSpace B] {ν : Measure B}
    [SigmaFinite ν] (ψ : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν))
    (u : Lp ℂ 2 (volume : Measure V)) (s : Fin 2) (w : Lp ℂ 2 ν) :
    inner ℂ u (spinMarginal ψ s w) =
      inner ℂ w ((tensorLeft (tensor u (spinVector s))).adjoint ψ) := by
  simp only [spinMarginal, ContinuousLinearMap.adjoint_inner_right,
    tensorRight_apply, tensorLeft_apply]

lemma sum_insert_adjoint_sq_le {N : ℕ}
    (u : Lp ℂ 2 (spinSpaceMeasure (V := V))) (hu : ‖u‖ = 1)
    (ψ : fermionL2 (V := V) (N+1))
    (ha : ∀ i j : Fin (N+1), i ≠ j → permute (Equiv.swap i j) ψ = -ψ) :
    (∑ i : Fin (N+1), ‖(insertOrbital i u).adjoint ψ‖^2) ≤ ‖ψ‖^2 := by
  have h := sum_project_norm_sq_le u hu ψ ha
  simpa only [projectOrbital, ContinuousLinearMap.comp_apply, insertOrbital_norm,
    hu, one_mul] using h

variable {N : ℕ} {κ : Type*}

lemma fermionFamily_coefficient_sum
    (b : HilbertBasis κ ℂ (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := V)))))
    (ψ : fermionL2 (V := V) (N+1)) (u : Lp ℂ 2 (volume : Measure V)) :
    (∑' p, ENNReal.ofReal (‖inner ℂ u (fermionFamily b ψ p)‖^2)) =
      ENNReal.ofReal ((1/2:ℝ) * ∑ i : Fin (N+1), ∑ s : Fin 2,
        ‖(insertOrbital i (tensor u (spinVector s))).adjoint ψ‖^2) := by
  have hc : ((Real.sqrt 2)⁻¹)^2 = (1/2:ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hi (i : Fin (N+1)) (s : Fin 2) (j : κ) :
      ‖inner ℂ u (fermionFamily b ψ (i,s,j))‖^2 = (1/2:ℝ) *
        ‖inner ℂ (b j) ((insertOrbital i (tensor u (spinVector s))).adjoint ψ)‖^2 := by
    simp only [fermionFamily, inner_smul_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hc,
      spinMarginal_coefficient, insert_adjoint_split]
  rw [ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_prod', hi]
  have he (i : Fin (N+1)) (s : Fin 2) :
      (∑' j, ENNReal.ofReal ((1/2:ℝ) *
        ‖inner ℂ (b j) ((insertOrbital i (tensor u (spinVector s))).adjoint ψ)‖^2)) =
      ENNReal.ofReal ((1/2:ℝ) * ‖(insertOrbital i (tensor u (spinVector s))).adjoint ψ‖^2) := by
    have h := (basis_parseval b ((insertOrbital i (tensor u (spinVector s))).adjoint ψ)).mul_left (1/2:ℝ)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) h.summable, h.tsum_eq]
  simp_rw [he, tsum_fintype]
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]

lemma fermionFamily_bessel
    (b : HilbertBasis κ ℂ (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := V)))))
    (ψ : fermionL2 (V := V) (N+1)) (hn : ‖ψ‖^2 = 1)
    (ha : ∀ i j : Fin (N+1), i ≠ j → permute (Equiv.swap i j) ψ = -ψ)
    (F : Finset (Fin (N+1) × Fin 2 × κ)) :
    BesselFamily (fun p : F => fermionFamily b ψ p) := by
  classical
  apply besselFamily_of_unit
  intro u hu
  have hs (s : Fin 2) := sum_insert_adjoint_sq_le (tensor u (spinVector s))
    (by rw [tensor_norm, hu, spinVector_orthonormal.norm_eq_one, one_mul]) ψ ha
  have hb : (1/2:ℝ) * (∑ i : Fin (N+1), ∑ s : Fin 2,
        ‖(insertOrbital i (tensor u (spinVector s))).adjoint ψ‖^2) ≤ 1 := by
    rw [Finset.sum_comm]
    have hh := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Fin 2))) => hs s)
    simp only [hn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    norm_num only [Nat.cast_ofNat, mul_one] at hh
    linarith
  apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0:ℝ) ≤ 1)).mp
  calc
    _ = ∑ p ∈ F, ENNReal.ofReal (‖inner ℂ u (fermionFamily b ψ p)‖^2) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
      exact Finset.sum_coe_sort F (fun p => ENNReal.ofReal (‖inner ℂ u (fermionFamily b ψ p)‖^2))
    _ ≤ ∑' p, ENNReal.ofReal (‖inner ℂ u (fermionFamily b ψ p)‖^2) := ENNReal.sum_le_tsum F
    _ = _ := fermionFamily_coefficient_sum b ψ u
    _ ≤ _ := ENNReal.ofReal_le_ofReal hb
end CoulombLT

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_ContractFunction
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace CoulombPauli
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]

lemma contractL2_ae (b : Lp ℂ 2 ν) (ψ : Lp ℂ 2 (μ.prod ν)) :
    contractL2 b ψ =ᵐ[μ] contractFunction b ψ := MemLp.coeFn_toLp _

lemma tensorRight_adjoint_eq_contract (b : Lp ℂ 2 ν) (ψ : Lp ℂ 2 (μ.prod ν)) :
    (tensorRight b).adjoint ψ = contractL2 b ψ := by
  apply ext_inner_left ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right, tensorRight_apply, L2.inner_def, L2.inner_def]
  have hprod : Integrable (fun z : A × B => inner ℂ (u z.1 * b z.2) (ψ z)) (μ.prod ν) := by
    apply (L2.integrable_inner (tensor u b) ψ).congr
    filter_upwards [tensor_ae u b] with z hz
    rw [hz]
  calc
    _ = ∫ z : A × B, star (u z.1) * (star (b z.2) * ψ z) ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards [tensor_ae u b] with z hz
      simp only [hz, inner, star_mul]
      ring
    _ = ∫ x, ∫ y, star (u x) * (star (b y) * ψ (x,y)) ∂ν ∂μ := by
      apply integral_prod
      convert hprod using 1
      all_goals try with_reducible_and_instances rfl
      ext z
      simp only [inner, star_mul]
      ring
    _ = ∫ x, inner ℂ (u x) (contractL2 b ψ x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [contractL2_ae b ψ] with x hx
      rw [integral_const_mul]
      simp only [hx, contractFunction, inner]
      ring

lemma tensorRight_slice_parseval {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) (ψ : Lp ℂ 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, (∑' j, ENNReal.ofReal (‖((tensorRight (b j)).adjoint ψ) x‖^2)) =
      ∫⁻ y, ENNReal.ofReal (‖ψ (x,y)‖^2) ∂ν := by
  have hj (j : ι) : (fun x => ((tensorRight (b j)).adjoint ψ) x) =ᵐ[μ]
      contractFunction (b j) ψ := by
    rw [tensorRight_adjoint_eq_contract]
    exact contractL2_ae (b j) ψ
  filter_upwards [memLp_slice_ae ψ, ae_all_iff.mpr hj] with x hx hjs
  let u := hx.toLp (fun y => ψ (x,y))
  have hs := basis_parseval b u
  have hn : ‖u‖^2 = ∫ y, ‖ψ (x,y)‖^2 ∂ν := by
    rw [l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [hx.coeFn_toLp] with y hy
    rw [hy]
  calc
    _ = ∑' j, ENNReal.ofReal (‖inner ℂ (b j) u‖^2) := by
      apply tsum_congr
      intro j
      rw [hjs j, contractFunction_slice (b j) ψ x hx]
    _ = ENNReal.ofReal (‖u‖^2) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs.summable, hs.tsum_eq]
    _ = _ := by
      rw [hn]
      apply ofReal_integral_eq_lintegral_ofReal
      · exact (memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).mp hx
      · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
end CoulombPauli

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_TensorRightSpinVectorAe
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombPackets
open CoulombPauli
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma tensorRight_spinVector_ae
    (ψ : Lp ℂ 2 (spinSpaceMeasure (V := V))) (s : Fin 2) :
    (fun x => ((tensorRight (spinVector s)).adjoint ψ) x) =ᵐ[volume]
      (fun x => ψ (x,s)) := by
  rw [tensorRight_adjoint_eq_contract]
  filter_upwards [contractL2_ae (spinVector s) ψ, memLp_slice_ae ψ] with x hx hm
  rw [hx,contractFunction_slice (spinVector s) ψ x hm, spinVector_inner]
  exact (Measure.ae_count_iff.mp hm.coeFn_toLp) s

variable {B : Type*} [MeasurableSpace B] {ν : Measure B} [SigmaFinite ν]
lemma spinMarginal_slice_parseval {κ : Type*} [Countable κ]
    (b : HilbertBasis κ ℂ (Lp ℂ 2 ν))
    (ψ : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν)) :
    ∀ᵐ x ∂(volume : Measure V), ∀ s : Fin 2,
      (∑' j, ENNReal.ofReal (‖spinMarginal ψ s (b j) x‖^2)) =
        ∫⁻ y, ENNReal.ofReal (‖ψ ((x,s),y)‖^2) ∂ν := by
  have h1 (s : Fin 2) (j : κ) :
      (fun x => spinMarginal ψ s (b j) x) =ᵐ[volume]
        (fun x => ((tensorRight (b j)).adjoint ψ) (x,s)) :=
    tensorRight_spinVector_ae ((tensorRight (b j)).adjoint ψ) s
  have h2 := Measure.ae_ae_of_ae_prod (tensorRight_slice_parseval b ψ)
  filter_upwards [ae_all_iff.mpr (fun s => ae_all_iff.mpr (h1 s)), h2] with x hx hy
  intro s
  rw [← Measure.ae_count_iff.mp hy s]
  apply tsum_congr
  intro j
  rw [hx s j]

lemma spinMarginal_parseval_norm {κ : Type*}
    (b : HilbertBasis κ ℂ (Lp ℂ 2 ν))
    (ψ : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν)) :
    (∑' p : Fin 2 × κ, ENNReal.ofReal (‖spinMarginal ψ p.1 (b p.2)‖^2)) =
      ENNReal.ofReal (‖ψ‖^2) := by
  obtain ⟨ι,a,-⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 (spinSpaceMeasure (V := V)))
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  simp_rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
    spinMarginal_sum_norm]
  exact tensorRight_parseval a b ψ
end CoulombPackets

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_HalfScaleNormSq
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombLT
open CoulombPauli CoulombPackets
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {N : ℕ} {κ : Type*}

lemma half_scale_norm_sq {H : Type*} [SeminormedAddCommGroup H] [NormedSpace ℂ H]
    (u : H) : ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • u‖^2 = (1/2:ℝ)*‖u‖^2 := by
  have hc : ((Real.sqrt 2)⁻¹)^2 = (1/2:ℝ) := by
    rw [inv_pow,Real.sq_sqrt (by norm_num)]; norm_num
  simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,hc]

lemma marginal_family_trace
    (b : HilbertBasis κ ℂ (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := V)))))
    (ψ : Fin (N+1) → fermionL2 (V := V) (N+1)) :
    (∑' p : Fin (N+1) × Fin 2 × κ,
      ENNReal.ofReal (‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
        spinMarginal (splitFermion p.1 (ψ p.1)) p.2.1 (b p.2.2)‖^2)) =
      ENNReal.ofReal ((1/2:ℝ) * ∑ i, ‖ψ i‖^2) := by
  simp_rw [half_scale_norm_sq,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [ENNReal.tsum_mul_left,ENNReal.tsum_prod']
  simp_rw [spinMarginal_parseval_norm b,splitFermion_norm,tsum_fintype,
    ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]

lemma fermionFamily_trace
    (b : HilbertBasis κ ℂ (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := V)))))
    (ψ : fermionL2 (V := V) (N+1)) :
    (∑' p, ENNReal.ofReal (‖fermionFamily b ψ p‖^2)) =
      ENNReal.ofReal ((N+1:ℝ)/2 * ‖ψ‖^2) := by
  have h := marginal_family_trace b (fun _ => ψ)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_one] at h
  unfold fermionFamily
  rw [h]
  congr 1
  ring

end CoulombLT

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_WeakDerivativeSmulL2
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombAtom
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma weak_derivative_smul_L2 {f g : Lp ℂ 2 (volume : Measure V)} {v : V}
    (h : HasWeakDirectionalDerivative f g v) (c : ℂ) :
    HasWeakDirectionalDerivative (c • f : Lp ℂ 2 volume) (c • g : Lp ℂ 2 volume) v := by
  intro φ hφ hcφ
  have he (w : Lp ℂ 2 (volume : Measure V)) (a : V → ℝ) :
      (∫ x, (c • w : Lp ℂ 2 volume) x * (a x : ℂ)) =
        c * ∫ x, w x * (a x : ℂ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c w] with x hx
    simp only [hx,Pi.smul_apply,smul_eq_mul,mul_assoc]
  rw [he,he,h φ hφ hcφ,mul_neg]
end CoulombAtom

namespace CoulombLT

section
open CoulombPauli CoulombPackets
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma fermionDensity_eq_family {N : ℕ} {κ : Type*} [Countable κ]
    (b : HilbertBasis κ ℂ (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := Space)))))
    (ψ : fermionL2 (V := Space) (N+1)) :
    ∀ᵐ x ∂(volume : Measure Space),
      fermionDensity ψ x = 2 * infiniteDensity (fermionFamily b ψ) x := by
  have he (p : Fin (N+1) × Fin 2 × κ) :
      (fun x => fermionFamily b ψ p x) =ᵐ[volume]
        (fun x => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
          spinMarginal (splitFermion p.1 ψ) p.2.1 (b p.2.2) x) := by
    exact Lp.coeFn_smul _ _
  filter_upwards [ae_all_iff.mpr he,
    ae_all_iff.mpr (fun i : Fin (N+1) => spinMarginal_slice_parseval b (splitFermion i ψ))]
      with x hx hy
  have hs : infiniteDensity (fermionFamily b ψ) x =
      ENNReal.ofReal (1/2:ℝ) * fermionDensity ψ x := by
    unfold infiniteDensity
    simp_rw [hx,half_scale_norm_sq,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
    rw [ENNReal.tsum_mul_left,ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_prod',hy,tsum_fintype]
    rfl
  rw [hs,← mul_assoc]
  have hc : (2:ℝ≥0∞)*ENNReal.ofReal (1/2:ℝ) = 1 := by
    rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [hc,one_mul]
end

open CoulombPauli CoulombPackets CoulombAtom
local instance instFactNeENNRealOfNatTop_solutions : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

lemma fermion_lt_numeric {N : ℕ} (u : Fin (N+1) → Fin 3 → fermionL2 (V := Space) (N+1)) :
    (4:ℝ≥0∞)*(16*ENNReal.ofReal ((N+1:ℝ)/2) + ENNReal.ofReal (1024/3:ℝ)*
        (∑ a : Fin 3, ENNReal.ofReal ((1/2:ℝ)*∑ i, ‖u i a‖^2))) =
      ENNReal.ofReal (32*(N+1:ℝ) + (2048/3:ℝ) * ∑ i, ∑ a, ‖u i a‖^2) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), ← Finset.mul_sum,
    Finset.sum_comm]
  have h4 : (4:ℝ≥0∞) = ENNReal.ofReal (4:ℝ) := by norm_num
  have h16 : (16:ℝ≥0∞) = ENNReal.ofReal (16:ℝ) := by norm_num
  rw [h4,h16,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 16),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1024/3),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
  congr 1
  ring

theorem fermion_lieb_thirring {N : ℕ}
    (ψ : fermionL2 (V := Space) (N+1))
    (u : Fin (N+1) → Fin 3 → fermionL2 (V := Space) (N+1))
    (hw : ∀ i a, HasWeakSpinPartialDerivative (splitFermion i ψ)
      (splitFermion i (u i a)) (EuclideanSpace.single a 1))
    (hn : ‖ψ‖^2 = 1)
    (ha : ∀ i j : Fin (N+1), i ≠ j → permute (Equiv.swap i j) ψ = -ψ) :
    (∫⁻ x, fermionDensity ψ x ^ (5/3:ℝ)) ≤
      ENNReal.ofReal (32*(N+1:ℝ) + (2048/3:ℝ) * ∑ i, ∑ a, ‖u i a‖^2) := by
  let : MeasureTheory.IsSeparable (configMeasure N (spinSpaceMeasure (V := Space))) :=
    MeasureTheory.isSeparable_of_sigmaFinite _
  obtain ⟨κ,b,-⟩ := exists_hilbertBasis ℂ
    (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := Space))))
  let : Countable κ := hilbertBasis_countable b
  let f := fermionFamily b ψ
  let g (a : Fin 3) (p : Fin (N+1) × Fin 2 × κ) : Lp ℂ 2 (volume : Measure Space) :=
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • spinMarginal (splitFermion p.1 (u p.1 a)) p.2.1 (b p.2.2)
  have hg (a : Fin 3) (p : Fin (N+1) × Fin 2 × κ) :
      HasWeakDirectionalDerivative (f p) (g a p) (EuclideanSpace.single a 1) :=
    weak_derivative_smul_L2 (spinMarginal_weak_derivative (hw p.1 a) p.2.1 (b p.2.2)) _
  have hb := weak_family_lieb_thirring (fermionFamily_bessel b ψ hn ha) hg
  have hftrace : (∑' j, ENNReal.ofReal (‖f j‖^2)) = ENNReal.ofReal ((N+1:ℝ)/2) := by
    simpa only [hn,mul_one] using fermionFamily_trace b ψ
  have hgtrace (a : Fin 3) :
      (∑' j, ENNReal.ofReal (‖g a j‖^2)) = ENNReal.ofReal ((1/2:ℝ)*∑ i, ‖u i a‖^2) :=
    marginal_family_trace b (fun i => u i a)
  rw [hftrace] at hb
  simp_rw [hgtrace] at hb
  have hc : (2:ℝ≥0∞)^(5/3:ℝ) ≤ 4 := by
    calc
      _ ≤ (2:ℝ≥0∞)^(2:ℝ) := ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by norm_num
  calc
    _ = ∫⁻ x, (2*infiniteDensity f x)^(5/3:ℝ) :=
      by
      apply lintegral_congr_ae
      filter_upwards [fermionDensity_eq_family b ψ] with x hx
      exact congrArg (fun t : ℝ≥0∞ => t^(5/3:ℝ)) hx
    _ ≤ ∫⁻ x, 4*(infiniteDensity f x)^(5/3:ℝ) := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 5/3)]
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 4 * ∫⁻ x, infiniteDensity f x^(5/3:ℝ) := lintegral_const_mul' _ _ (by norm_num)
    _ ≤ 4*(16*ENNReal.ofReal ((N+1:ℝ)/2) + ENNReal.ofReal (1024/3:ℝ)*
        (∑ a : Fin 3, ENNReal.ofReal ((1/2:ℝ)*∑ i, ‖u i a‖^2))) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := fermion_lt_numeric u
end CoulombLT

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_ParticleDensity
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombAtom.Pauli
open CoulombPauli CoulombPackets CoulombLT

theorem form_lieb_thirring {N : ℕ} (ψ : FormVector (N+1))
    (hψ : FormAdmissible ψ) :
    (∫⁻ x, oneParticleDensity ψ hψ.1 x ^ (5/3:ℝ)) ≤
      ENNReal.ofReal (32*(N+1:ℝ) + (2048/3:ℝ)*
        (∑ s : Spins (N+1), ∑ i : Fin (N+1), ∑ a : Fin 3,
          ∫ x : Configuration (N+1), ‖ψ.gradient s i a x‖^2)) := by
  have hn : ‖toMany ψ hψ.1‖^2 = 1 :=
    (toMany_norm_sq ψ hψ.1).trans hψ.2.2.2.2.1
  have ha (i j : Fin (N+1)) (hij : i ≠ j) :
      permute (Equiv.swap i j) (toMany ψ hψ.1) = -toMany ψ hψ.1 := by
    rw [toMany_permute ψ hψ.1 (Equiv.swap i j) (hψ.2.2.2.1 _)]
    simp [Equiv.Perm.sign_swap hij]
  have hw (i : Fin (N+1)) (a : Fin 3) := form_hasFermionGradient ψ hψ i a
  simp only [EuclideanSpace.basisFun_apply] at hw
  have h := fermion_lieb_thirring (toMany ψ hψ.1) (gradientMany ψ hψ) hw hn ha
  simp only [gradientMany_norm_sq] at h
  have hs : (∑ s : Spins (N+1), ∑ i : Fin (N+1), ∑ a : Fin 3,
      ∫ x : Configuration (N+1), ‖ψ.gradient s i a x‖^2) =
      ∑ i : Fin (N+1), ∑ a : Fin 3, ∑ s : Spins (N+1),
        ∫ x : Configuration (N+1), ‖ψ.gradient s i a x‖^2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
  simpa only [oneParticleDensity,hs] using h
end CoulombAtom.Pauli

namespace CoulombLT
open CoulombPauli CoulombPackets
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma coordinateDensity_aemeasurable {N : ℕ}
    (ψ : fermionL2 (V := V) (N+1)) (i : Fin (N+1)) :
    AEMeasurable (fun x => ∑ s : Fin 2, ∫⁻ y,
      ENNReal.ofReal (‖splitFermion i ψ ((x,s),y)‖^2)
        ∂(configMeasure N (spinSpaceMeasure (V := V)))) volume := by
  have hm := ((Lp.memLp (splitFermion i ψ)).aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal
  have h1 := hm.lintegral_prod_right'
  have h2 := h1.lintegral_prod_right'
  simpa only [lintegral_fintype,Measure.count_singleton,mul_one,Pi.pow_apply] using h2

lemma fermionDensity_aemeasurable {N : ℕ} (ψ : fermionL2 (V := V) (N+1)) :
    AEMeasurable (fermionDensity ψ) volume := by
  exact Finset.aemeasurable_fun_sum Finset.univ (fun i _ => coordinateDensity_aemeasurable ψ i)

lemma coordinate_density_weighted {N : ℕ} (ψ : fermionL2 (V := V) (N+1))
    (i : Fin (N+1)) (w : V → ℝ) (hw : Measurable w) :
    (∫⁻ x, ENNReal.ofReal (w x) * (∑ s : Fin 2, ∫⁻ y,
      ENNReal.ofReal (‖splitFermion i ψ ((x,s),y)‖^2)
        ∂(configMeasure N (spinSpaceMeasure (V := V))))) =
    ∫⁻ q, ENNReal.ofReal (w (q i).1) * ENNReal.ofReal (‖ψ q‖^2)
      ∂(configMeasure (N+1) (spinSpaceMeasure (V := V))) := by
  let ν := configMeasure N (spinSpaceMeasure (V := V))
  have hm : AEMeasurable (fun p : (V × Fin 2) × (Fin N → V × Fin 2) =>
      ENNReal.ofReal (w p.1.1) * ENNReal.ofReal (‖splitFermion i ψ p‖^2))
      ((spinSpaceMeasure (V := V)).prod ν) :=
    ((hw.comp (measurable_fst.comp measurable_fst)).ennreal_ofReal.aemeasurable).mul
      ((Lp.memLp (splitFermion i ψ)).aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal
  have hp := splitAt_preserving (μ := spinSpaceMeasure (V := V)) i
  have ha := pull_ae (splitAt i).symm (hp.symm (splitAt i)) ψ
  calc
    _ = ∫⁻ x, ∫⁻ s : Fin 2, ∫⁻ y,
        ENNReal.ofReal (w x) * ENNReal.ofReal (‖splitFermion i ψ ((x,s),y)‖^2) ∂ν ∂Measure.count := by
      apply lintegral_congr
      intro x
      simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_fintype,Measure.count_singleton,mul_one,Finset.mul_sum]
      rfl
    _ = ∫⁻ p, ENNReal.ofReal (w p.1.1) * ENNReal.ofReal (‖splitFermion i ψ p‖^2)
        ∂((spinSpaceMeasure (V := V)).prod ν) := by
      rw [lintegral_prod _ hm,lintegral_prod _ hm.lintegral_prod_right']
    _ = ∫⁻ p, ENNReal.ofReal (w p.1.1) * ENNReal.ofReal (‖ψ ((splitAt i).symm p)‖^2)
        ∂((spinSpaceMeasure (V := V)).prod ν) := by
      apply lintegral_congr_ae
      filter_upwards [ha] with p hp
      rw [← hp]
      rfl
    _ = _ := by
      have he := (hp.symm (splitAt i)).lintegral_comp_emb
        (splitAt i).symm.measurableEmbedding
        (fun q => ENNReal.ofReal (w (q i).1) * ENNReal.ofReal (‖ψ q‖^2))
      have hs (p : (V × Fin 2) × (Fin N → V × Fin 2)) :
          (splitAt i).symm p i = p.1 := by
        exact congrArg Prod.fst ((splitAt i).apply_symm_apply p)
      simp_rw [hs] at he
      exact he

lemma density_weighted_lintegral {N : ℕ} (ψ : fermionL2 (V := V) (N+1))
    (w : V → ℝ) (hw : Measurable w) :
    (∫⁻ x, ENNReal.ofReal (w x) * fermionDensity ψ x) =
      ∑ i : Fin (N+1), ∫⁻ q, ENNReal.ofReal (w (q i).1) * ENNReal.ofReal (‖ψ q‖^2)
        ∂(configMeasure (N+1) (spinSpaceMeasure (V := V))) := by
  change (∫⁻ x, ENNReal.ofReal (w x) * ∑ i : Fin (N+1),
    ∑ s : Fin 2, ∫⁻ y, ENNReal.ofReal (‖splitFermion i ψ ((x,s),y)‖^2)
      ∂(configMeasure N (spinSpaceMeasure (V := V)))) = _
  conv_lhs => arg 2; ext x; rw [Finset.mul_sum]
  rw [lintegral_finsetSum' (f := fun i x => ENNReal.ofReal (w x) *
      (∑ s : Fin 2, ∫⁻ y, ENNReal.ofReal (‖splitFermion i ψ ((x,s),y)‖^2)
        ∂(configMeasure N (spinSpaceMeasure (V := V))))) Finset.univ (fun i _ =>
    hw.ennreal_ofReal.aemeasurable.mul (coordinateDensity_aemeasurable ψ i))]
  exact Finset.sum_congr rfl (fun i _ => coordinate_density_weighted ψ i w hw)
end CoulombLT

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Density
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombAtom.Pauli
open CoulombPauli CoulombPackets CoulombLT

lemma density_power_integrable {N : ℕ} (ψ : FormVector (N+1)) (hψ : FormAdmissible ψ) :
    Integrable (fun x => density ψ hψ.1 x^(5/3:ℝ)) := by
  have hm := (fermionDensity_aemeasurable (toMany ψ hψ.1)).pow_const (5/3:ℝ)
  have hb := form_lieb_thirring ψ hψ
  have hn : (∫⁻ x, oneParticleDensity ψ hψ.1 x^(5/3:ℝ)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hi := integrable_toReal_of_lintegral_ne_top hm hn
  change Integrable (fun x => (fermionDensity (toMany ψ hψ.1) x).toReal ^ (5/3:ℝ))
  simpa only [← ENNReal.toReal_rpow] using hi

lemma toMany_coordinate_lintegral {N : ℕ} (ψ : FormVector N)
    (hψ : ∀ s, MemLp (ψ.value s) 2) (i : Fin N) (w : Space → ℝ)
    (hw : Measurable w) :
    (∫⁻ q, ENNReal.ofReal (w (q i).1) * ENNReal.ofReal (‖toMany ψ hψ q‖^2)
      ∂configMeasure N oneMeasure) =
    ∑ s : Spins N, ∫⁻ x : Configuration N,
      ENNReal.ofReal (w (x i)) * ENNReal.ofReal (‖ψ.value s x‖^2) := by
  have hm : AEMeasurable (fun p : Configuration N × Spins N =>
      ENNReal.ofReal (w (p.1 i)) * ENNReal.ofReal (‖ψ.value p.2 p.1‖^2))
      ((volume : Measure (Configuration N)).prod Measure.count) :=
    ((hw.comp ((measurable_pi_apply i).comp measurable_fst)).ennreal_ofReal.aemeasurable).mul
      ((memLp_spin ψ.value hψ).aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal
  calc
    _ = ∫⁻ q, ENNReal.ofReal (w (q i).1) *
        ENNReal.ofReal (‖ψ.value (fun j => (q j).2) (fun j => (q j).1)‖^2)
          ∂configMeasure N oneMeasure := by
      apply lintegral_congr_ae
      filter_upwards [toMany_ae ψ hψ] with q hq
      rw [hq]
    _ = ∫⁻ p : Configuration N × Spins N,
        ENNReal.ofReal (w (p.1 i)) * ENNReal.ofReal (‖ψ.value p.2 p.1‖^2)
        ∂volume.prod Measure.count :=
      (splitSpin_preserving N).lintegral_comp_emb (splitSpin N).measurableEmbedding
        (fun p : Configuration N × Spins N => ENNReal.ofReal (w (p.1 i)) * ENNReal.ofReal (‖ψ.value p.2 p.1‖^2))
    _ = _ := by
      rw [lintegral_prod_symm _ hm]
      simp only [lintegral_fintype,Measure.count_singleton,mul_one]

end CoulombAtom.Pauli

open MeasureTheory Set Metric
open scoped ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoreSliceMassIntegrable
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

theorem CoreAntisymmetric.integrated_priced {N M : ℕ} {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (hψ : SobolevVector ψ) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam * formMass ψ ≤
      (∑ t : Spins M, ∫ y, formEnergy Z (coreSlice ψ t y)) + lam * N * formMass ψ := by
  rw [← hψ.integral_coreSlice_mass, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hψ.coreSlice_energy_integrable Z t)
      ((hψ.coreSlice_mass_integrable t).const_mul _)]
  exact integral_mono_ae ((hψ.coreSlice_mass_integrable t).const_mul _)
    ((hψ.coreSlice_energy_integrable Z t).add
      ((hψ.coreSlice_mass_integrable t).const_mul _))
    ((ha.ae_coreSlice hψ t).mono fun _ h => h.priced_lower_bound hZ hlam)

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CutCoreNumber
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

theorem cutCoreEnergy_priced {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    {ψ : FormVector L} (hψ : SobolevFermion ψ) (b : Fin L → Fin 2)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam * formMass (multiplyForm (spatialProduct (N := L) p hp b) ψ) ≤
      cutCoreEnergy p hp Z ψ b + lam * cutCoreNumber b *
        formMass (multiplyForm (spatialProduct (N := L) p hp b) ψ) := by
  have hh := (orderedCutForm_core_antisymmetric p hp hψ b).integrated_priced
    (orderedCutForm_sobolev p hp hψ.sobolevVector b) hZ hlam
  simpa only [orderedCutForm_mass, cutCoreEnergy] using hh

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CoulombBallIntegral
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis

lemma integral_coulomb_power_ball {R : ℝ} (hR : 0 < R) :
    (∫ x : TFSpace in ball 0 R, ‖x‖^(-5/2:ℝ)) = 8*Real.pi*R^(1/2:ℝ) := by
  have hh := integral_norm_rpow_ball hR (by norm_num : (-3:ℝ) < -5/2)
  norm_num at hh
  norm_num only [neg_div] at ⊢
  rw [hh]
  ring

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ShortRangePotential
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped ENNReal

namespace CoulombAnalysis

lemma coulomb_short_range_holder {R : ℝ} (hR : 0 < R)
    {f : TFSpace → ℝ} (hf : MemLp f (5/3) (ballMeasure R)) :
    (∫ x in ball 0 R, ‖f x‖/‖x‖) ≤
      (∫ x in ball 0 R, ‖f x‖^(5/3:ℝ))^(3/5:ℝ) *
      (8*Real.pi)^(2/5:ℝ) * R^(1/5:ℝ) := by
  have hf' : MemLp (fun x => ‖f x‖) (ENNReal.ofReal (5/3:ℝ)) (ballMeasure R) := by
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 3),ENNReal.ofReal_ofNat] using hf.norm
  have hk : MemLp (fun x : TFSpace => ‖x‖⁻¹) (ENNReal.ofReal (5/2:ℝ)) (ballMeasure R) := by
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2),ENNReal.ofReal_ofNat] using nuclear_memLp R
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (5/3:ℝ).HolderConjugate (5/2) from Real.holderConjugate_iff.mpr (by norm_num))
    (Filter.Eventually.of_forall fun x => norm_nonneg (f x))
    (Filter.Eventually.of_forall fun x : TFSpace => inv_nonneg.mpr (norm_nonneg x)) hf' hk
  have he : (∫ x, (‖x‖⁻¹)^(5/2:ℝ) ∂ballMeasure R) = 8*Real.pi*R^(1/2:ℝ) := by
    simpa only [ballMeasure,←Real.rpow_neg_eq_inv_rpow,neg_div] using integral_coulomb_power_ball hR
  rw [he] at hh
  norm_num only [one_div_div,mul_one] at hh
  have he' : (8*Real.pi*R^(1/2:ℝ))^(2/5:ℝ) =
      (8*Real.pi)^(2/5:ℝ)*R^(1/5:ℝ) := by
    rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_mul hR.le]
    norm_num
  rw [he'] at hh
  simpa only [ballMeasure,div_eq_mul_inv,mul_assoc] using hh

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CutCoreExcess
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
namespace CoulombAtom

lemma cutCoreExcess_nonneg {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (b : Fin L → Fin 2) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) : 0 ≤ cutCoreExcess p hp Z lam ψ b := by
  have hh := cutCoreEnergy_priced p hp hψ b hZ hlam
  unfold cutCoreExcess
  rw [orderedCutForm_mass]
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_FreshKineticBudgetBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombAtom

lemma cut_out_kinetic_le_field_work {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    (∑ c : Fin L → Fin 2, outKinetic (orderedCutForm p hp ψ c)) ≤
      corePriceExcess Z lam ψ+(1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p)+
        (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          conditionalFieldSum Z lam (orderedCutForm p hp ψ c) s u) := by
  have hid := fock_cut_excess_identity p hp hψ.sobolevVector Z lam
  simp_rw [cutExteriorPrice_eq_field_work p hp hψ.sobolevVector Z lam] at hid
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib] at hid
  have he : 0 ≤ ∑ c : Fin L → Fin 2, cutCoreExcess p hp Z lam ψ c :=
    Finset.sum_nonneg (fun c _ => cutCoreExcess_nonneg p hp hψ c hZ hlam)
  have hr : 0 ≤ ∑ c : Fin L → Fin 2, outRepulsion (orderedCutForm p hp ψ c) :=
    Finset.sum_nonneg (fun c _ => outRepulsion_nonneg _)
  linarith only [hid,he,hr]

 theorem radial_out_kinetic_coupling {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (y : Space) {t b R : ℝ} (ht : 0 ≤ t)
    (hb : 0 < b) (hy : t+2*b ≤ ‖y‖) (hR : t+b ≤ R) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    (∑ c : Fin L → Fin 2, outKinetic (orderedCutForm p hp ψ c)) ≤
      corePriceExcess Z lam ψ+(1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p)+
        Real.sqrt (freshOutMaximumSecondMoment p hp ψ Z lam)*
          Real.sqrt (rawCountMoment ψ y R) := by
  dsimp only
  refine (cut_out_kinetic_le_field_work _ _ hψ hZ hlam).trans (add_le_add le_rfl
    ((radial_full_field_work_budget hψ.sobolevVector y ht hb hy hZ hlam.le).trans ?_))
  rw [rawCountMoment_eq_integral hψ.sobolevVector]
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (radialCut_out_second_moment hψ.sobolevVector y ht hb hR))
    (Real.sqrt_nonneg _)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TranslatedShortRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped ContDiff

namespace CoulombAnalysis

lemma ball_translation_preserving (y : TFSpace) (R : ℝ) :
    MeasurePreserving (fun x : TFSpace => y+x) (ballMeasure R) (volume.restrict (ball y R)) := by
  have h := (measurePreserving_add_left (volume : Measure TFSpace) y).restrict_preimage
    (measurableSet_ball (x := y) (ε := R))
  have he : (fun x : TFSpace => y+x) ⁻¹' ball y R = ball 0 R := by
    ext x
    simp only [mem_preimage,mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero]
  simpa only [he,ballMeasure] using h

lemma setIntegral_translate_ball (y : TFSpace) (R : ℝ) (f : TFSpace → ℝ) :
    (∫ x in ball 0 R, f (y+x)) = ∫ x in ball y R, f x :=
  (ball_translation_preserving y R).integral_comp (MeasurableEquiv.addLeft y).measurableEmbedding f

lemma coulomb_short_range_holder_centered {R : ℝ} (hR : 0 < R) (y : TFSpace)
    {f : TFSpace → ℝ} (hf : MemLp f (5/3) (volume.restrict (ball y R))) :
    (∫ x in ball y R, ‖f x‖/‖y-x‖) ≤
      (∫ x in ball y R, ‖f x‖^(5/3:ℝ))^(3/5:ℝ) *
      (8*Real.pi)^(2/5:ℝ)*R^(1/5:ℝ) := by
  have hh := coulomb_short_range_holder hR (hf.comp_measurePreserving (ball_translation_preserving y R))
  have he := setIntegral_translate_ball y R (fun x => ‖f x‖/‖y-x‖)
  simp only [sub_add_cancel_left,norm_neg] at he
  have hp := setIntegral_translate_ball y R (fun x => ‖f x‖^(5/3:ℝ))
  simp only [Function.comp_apply] at hh
  rw [he,hp] at hh
  exact hh

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LocalFieldScalarBoundBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

lemma thinFieldBase_collar_bound {a b m D B C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m)
    (hDm : D*a ≤ m^2) (hbm : a ≤ b^2*m) (hB : 0 ≤ B)
    (hC : 1 ≤ C) (hBC : B ≤ C*m^2) :
    thinFieldBase a b D B ≤ (6+C+localizationIMSConstant*C)*(m/a)^2 := by
  have hfield := localFieldScale_linear_bound ha hm h3 hC hBC (D := D)
  have hr : Real.sqrt B ≤ C*m := by
    simpa using sqrt_count_scale hB hC (by norm_num : (0:ℝ) ≤ 1)
      (le_trans zero_le_one hm) (by simpa using hBC)
  have hD : D/a ≤ (m/a)^2 := by
    have hh := div_le_div_of_nonneg_right hDm (sq_nonneg a)
    calc _ = (D*a)/a^2 := by field_simp
         _ ≤ m^2/a^2 := hh
         _ = _ := by ring
  have hcollar : m/(b^2*a) ≤ (m/a)^2 := by
    have hh := mul_le_mul_of_nonneg_left hbm (show 0 ≤ m/(b^2*a^2) by positivity)
    calc _ = m/(b^2*a^2)*a := by field_simp
         _ ≤ m/(b^2*a^2)*(b^2*m) := hh
         _ = _ := by field_simp
  have hI := localizationIMSConstant_nonneg
  have hC0 := le_trans zero_le_one hC
  have hi : localizationIMSConstant*Real.sqrt B/(b^2*a) ≤
      localizationIMSConstant*C*(m/a)^2 := by
    calc _ ≤ localizationIMSConstant*(C*m)/(b^2*a) := by gcongr
         _ = localizationIMSConstant*C*(m/(b^2*a)) := by ring
         _ ≤ _ := by gcongr
  unfold thinFieldBase
  nlinarith only [hfield,hD,hi]

lemma sharpFreshFieldConstant_one_le : 1 ≤ sharpFreshFieldConstant := by
  have hC := actualCellMomentConstant_one_le
  have hI := localizationIMSConstant_nonneg
  have hT := thinFieldUniversalConstant_pos
  unfold sharpFreshFieldConstant
  have h : 0 ≤ thinFieldUniversalConstant*(6+actualCellMomentConstant+
      localizationIMSConstant*actualCellMomentConstant) := by positivity
  linarith only [h]

lemma sharpFreshField_square {a b D B m : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) (hDm : D*a ≤ m^2) (hbm : a ≤ b^2*m)
    (hB : 0 ≤ B) (hBC : B ≤ actualCellMomentConstant*m^2) :
    thinFieldUniversalConstant*thinFieldBase a b D B ≤ (sharpFreshFieldConstant*(m/a))^2 := by
  have hh := thinFieldBase_collar_bound ha hb hm h3 hDm hbm hB actualCellMomentConstant_one_le hBC
  let K := thinFieldUniversalConstant*(6+actualCellMomentConstant+
    localizationIMSConstant*actualCellMomentConstant)
  have hK : 0 ≤ K := by
    have := thinFieldUniversalConstant_pos
    have := actualCellMomentConstant_one_le
    have := localizationIMSConstant_nonneg
    dsimp [K]; positivity
  have hKK : K ≤ sharpFreshFieldConstant^2 := by change K ≤ (1+K)^2; nlinarith only [hK]
  calc _ ≤ K*(m/a)^2 := by
          have ht := mul_le_mul_of_nonneg_left hh thinFieldUniversalConstant_pos.le
          exact ht.trans_eq (by dsimp [K]; ring)
       _ ≤ sharpFreshFieldConstant^2*(m/a)^2 := mul_le_mul_of_nonneg_right hKK (sq_nonneg _)
       _ = _ := by ring

theorem sharp_cell_fresh_field_mass {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {y : Space} (hy : y ≠ 0)
    {b r Z lam : ℝ} (hb : 0 < b) (hba : b ≤ localCellRadius y)
    (hr : r ∈ Set.Icc (5*localCellRadius y) (6*localCellRadius y))
    (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hcollar : localCellRadius y ≤ b^2*localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) :
    ∃ hr0 : 0 ≤ r,
      freshOutMaximumSecondMoment (coreFirstRadialCut y hr0 hb)
        (coreFirstRadialCut_partition y hr0 hb) ψ Z lam ≤
          (sharpFreshFieldConstant*(localOffsetMass (max (corePriceExcess Z lam ψ) 0) y/localCellRadius y))^2 ∧
      freshPatchMass (coreFirstRadialCut y hr0 hb) (coreFirstRadialCut_partition y hr0 hb)
        ψ Z lam y (r-4*b) ≤
          768*sharpFreshFieldConstant*localOffsetMass (max (corePriceExcess Z lam ψ) 0) y := by
  let a := localCellRadius y
  let D := max (corePriceExcess Z lam ψ) 0
  let m := localOffsetMass D y
  let B := rawCountMoment ψ y (16*a)
  have ha : 0 < a := localCellRadius_pos hy
  have hr0 : 0 ≤ r := le_trans (by positivity : 0 ≤ 5*a) hr.1
  have hsep : 20*a ≤ ‖y‖ := by dsimp [a,localCellRadius]; nlinarith [norm_nonneg y]
  have hbcount : B ≤ actualCellMomentConstant*m^2 :=
    (rawCountMoment_le_of_radius hψ.sobolevVector y y (by simp only [sub_self,norm_zero,zero_add]; linarith : ‖y-y‖+16*a ≤ 32*a)).trans
      (priced_enlarged_cell_count hψ hm hZ hlam hy)
  have hsq := sharpFreshField_square ha hb (localOffsetMass_one_le D y)
    (localOffsetMass_cube_le D y) (localOffsetMass_offset (le_max_right _ _) hy) hcollar
    (rawCountMoment_nonneg ψ y (16*a)) hbcount
  refine ⟨hr0,(freshOutMaximum_thin_bound hψ hm y ha hr0 hr.2 hb hba hsep hZ hlam).trans hsq,?_⟩
  have hh := freshPatchMass_thin_bound hψ hm y ha hr0 hr.2 hb (by linarith [hr.1]) hba hsep hZ hlam
  have hQ : 0 ≤ sharpFreshFieldConstant*(m/a) := by
    have := sharpFreshFieldConstant_one_le
    have := localOffsetMass_one_le D y
    positivity
  have hroot := Real.sqrt_le_iff.mpr ⟨hQ,hsq⟩
  calc _ ≤ 768*a*Real.sqrt (thinFieldUniversalConstant*thinFieldBase a b D B) := hh
       _ ≤ 768*a*(sharpFreshFieldConstant*(m/a)) := mul_le_mul_of_nonneg_left hroot (by positivity)
       _ = _ := by dsimp [m,D]; field_simp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_OrdinaryDensity
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAtom

lemma rawOneParticleLaw_ac {N : ℕ} (ψ : FormVector N) :
    rawOneParticleLaw (formRawLaw ψ) ≪ volume := by
  apply Measure.absolutelyContinuous_sum_left
  intro i
  exact ((withDensity_absolutelyContinuous volume _).map (measurable_pi_apply i)).trans
    (Measure.quasiMeasurePreserving_eval (fun _ : Fin N => (volume : Measure Space)) i).absolutelyContinuous

lemma ordinaryDensity_nonneg {N : ℕ} (ψ : FormVector N) (z : Space) :
    0 ≤ ordinaryDensity ψ z := ENNReal.toReal_nonneg

lemma ordinaryDensity_measurable {N : ℕ} (ψ : FormVector N) :
    Measurable (ordinaryDensity ψ) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

lemma ordinaryDensity_pairing {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {f : Space → ℝ} (hf : Measurable f)
    (hi : ∀ i : Fin N, Integrable (fun x => f (x i)) (formRawLaw ψ)) :
    (∫ z, ordinaryDensity ψ z*f z) = ∫ x, ∑ i, f (x i) ∂formRawLaw ψ := by
  let : IsFiniteMeasure (formRawLaw ψ) := formRawLaw_finite hψ
  let : IsFiniteMeasure (rawOneParticleLaw (formRawLaw ψ)) := rawOneParticleLaw_finite _
  change (∫ z, ((rawOneParticleLaw (formRawLaw ψ)).rnDeriv volume z).toReal*f z) = _
  rw [integral_toReal_rnDeriv_mul (rawOneParticleLaw_ac ψ)]
  exact rawOneParticleLaw_pairing _ hf hi

lemma ordinaryDensity_raw_local_potential {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (y : Space) (q : ℝ) :
    (∫ x, rawLocalPotential y q x ∂formRawLaw ψ) =
      ∫ z in ball y q, ordinaryDensity ψ z/‖z-y‖ := by
  let f : Space → ℝ := fun z => if ‖z-y‖ < q then 1/‖z-y‖ else 0
  have hf : Measurable f := Measurable.ite
    (measurableSet_lt ((continuous_id.sub continuous_const).norm.measurable) measurable_const)
    (measurable_const.div ((continuous_id.sub continuous_const).norm.measurable)) measurable_const
  have hn (z : Space) : 0 ≤ f z := by dsimp [f]; split_ifs <;> positivity
  have hi (i : Fin N) : Integrable (fun x : Configuration N => f (x i)) (formRawLaw ψ) := by
    apply (rawPotential_form_integrable hψ y).mono'
      (hf.comp (measurable_pi_apply i)).aestronglyMeasurable
    apply ae_of_all
    intro x
    change ‖f (x i)‖ ≤ rawPotential y x
    rw [Real.norm_of_nonneg (hn _)]
    have hle : 1/‖x i-y‖ ≤ rawPotential y x := by
      unfold rawPotential
      exact Finset.single_le_sum (f := fun j : Fin N => (1:ℝ)/‖x j-y‖)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    dsimp [f]
    split_ifs
    · exact hle
    · exact rawPotential_nonneg y x
  have hp := ordinaryDensity_pairing hψ hf hi
  have he : (fun z => ordinaryDensity ψ z*f z) =
      (ball y q).indicator (fun z => ordinaryDensity ψ z/‖z-y‖) := by
    funext z
    by_cases hz : ‖z-y‖ < q
    · have hm : z ∈ ball y q := by simpa only [mem_ball,dist_eq_norm] using hz
      rw [Set.indicator_of_mem hm]
      simp [f,hz,div_eq_mul_inv]
    · have hm : z ∉ ball y q := by simpa only [mem_ball,dist_eq_norm] using hz
      rw [Set.indicator_of_notMem hm]
      simp [f,hz]
  rw [he,integral_indicator measurableSet_ball] at hp
  exact hp.symm

theorem ordinaryDensity_raw_local_holder {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (y : Space) {q : ℝ} (hq : 0 < q)
    (hp : MemLp (ordinaryDensity ψ) (5/3) (volume.restrict (ball y q))) :
    (∫ x, rawLocalPotential y q x ∂formRawLaw ψ) ≤
      (∫ z in ball y q, (ordinaryDensity ψ z)^(5/3:ℝ))^(3/5:ℝ)*
        (8*Real.pi)^(2/5:ℝ)*q^(1/5:ℝ) := by
  rw [ordinaryDensity_raw_local_potential hψ]
  have hh := CoulombAnalysis.coulomb_short_range_holder_centered hq y hp
  simpa only [Real.norm_of_nonneg (ordinaryDensity_nonneg ψ _),norm_sub_rev y] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_BarrierOrdinaryGlobalBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace CoulombAtom

lemma formRawLaw_lintegral_eq_spin_sum {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) {w : Configuration N → ℝ} (hw : Measurable w) :
    (∫⁻ x, ENNReal.ofReal (w x) ∂formRawLaw ψ) =
      ∑ s : Spins N, ∫⁻ x, ENNReal.ofReal (w x)*ENNReal.ofReal (‖ψ.value s x‖^2) := by
  have hm (s : Spins N) : AEMeasurable (fun x : Configuration N => ENNReal.ofReal (‖ψ.value s x‖^2)) volume :=
    ((hψ.1 s).norm.integrable_sq).aemeasurable.ennreal_ofReal
  rw [formRawLaw,lintegral_withDensity_eq_lintegral_mul₀
    (formRawDensity_integrable hψ).aemeasurable.ennreal_ofReal hw.ennreal_ofReal.aemeasurable]
  simp only [Pi.mul_apply,formRawDensity,ENNReal.ofReal_sum_of_nonneg (fun s _ => sq_nonneg _),Finset.sum_mul]
  rw [lintegral_finsetSum' (f := fun s x => ENNReal.ofReal (‖ψ.value s x‖^2)*ENNReal.ofReal (w x)) Finset.univ (fun s _ =>
    ((hm s).mul hw.ennreal_ofReal.aemeasurable))]
  exact Finset.sum_congr rfl (fun s _ => lintegral_congr (fun x => mul_comm _ _))

lemma rawOneParticleLaw_weighted_lintegral {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) {w : Space → ℝ} (hw : Measurable w) :
    (∫⁻ z, ENNReal.ofReal (w z) ∂rawOneParticleLaw (formRawLaw ψ)) =
      ∑ i : Fin N, ∑ s : Spins N, ∫⁻ x,
        ENNReal.ofReal (w (x i))*ENNReal.ofReal (‖ψ.value s x‖^2) := by
  rw [rawOneParticleLaw,Measure.sum_fintype,lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_map hw.ennreal_ofReal (measurable_pi_apply i)]
  exact formRawLaw_lintegral_eq_spin_sum hψ (hw.comp (measurable_pi_apply i))

namespace Pauli
open CoulombLT

theorem oneParticleDensity_measure {N : ℕ} {ψ : FormVector (N+1)}
    (hψ : SobolevVector ψ) :
    volume.withDensity (oneParticleDensity ψ hψ.1) =
      rawOneParticleLaw (formRawLaw ψ) := by
  apply Measure.ext
  intro A hA
  let w : Space → ℝ := A.indicator (fun _ => 1)
  have hw : Measurable w := measurable_const.indicator hA
  have he := density_weighted_lintegral (toMany ψ hψ.1) w hw
  have hr := rawOneParticleLaw_weighted_lintegral hψ hw
  have hs : (∑ i : Fin (N+1), ∫⁻ q,
      ENNReal.ofReal (w (q i).1)*ENNReal.ofReal (‖toMany ψ hψ.1 q‖^2)
        ∂CoulombPauli.configMeasure (N+1) oneMeasure) =
      ∑ i : Fin (N+1), ∑ s : Spins (N+1), ∫⁻ x,
        ENNReal.ofReal (w (x i))*ENNReal.ofReal (‖ψ.value s x‖^2) :=
    Finset.sum_congr rfl (fun i _ => toMany_coordinate_lintegral ψ hψ.1 i w hw)
  have hwl : (fun x => ENNReal.ofReal (w x)*oneParticleDensity ψ hψ.1 x) =
      A.indicator (oneParticleDensity ψ hψ.1) := by
    funext x
    by_cases hx : x ∈ A <;> simp [w,hx]
  have hwr : (fun x => ENNReal.ofReal (w x)) = A.indicator (fun _ => (1:ENNReal)) := by
    funext x
    by_cases hx : x ∈ A <;> simp [w,hx]
  change (∫⁻ x, ENNReal.ofReal (w x)*oneParticleDensity ψ hψ.1 x) = _ at he
  rw [hwl,lintegral_indicator hA] at he
  rw [hwr,lintegral_indicator hA,lintegral_const,one_mul,Measure.restrict_apply_univ] at hr
  rw [withDensity_apply _ hA]
  exact he.trans (hs.trans hr.symm)

theorem ordinaryDensity_eq_density {N : ℕ} {ψ : FormVector (N+1)}
    (hψ : SobolevVector ψ) : ordinaryDensity ψ =ᵐ[volume] density ψ hψ.1 := by
  have he := Measure.rnDeriv_withDensity₀ volume
    (fermionDensity_aemeasurable (toMany ψ hψ.1))
  rw [show volume.withDensity (fermionDensity (toMany ψ hψ.1)) =
    rawOneParticleLaw (formRawLaw ψ) from oneParticleDensity_measure hψ] at he
  exact he.mono (fun x hx => congrArg ENNReal.toReal hx)

theorem ordinaryDensity_eq_spatialDensity {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) : ordinaryDensity ψ =ᵐ[volume] spatialDensity ψ hψ.1 := by
  cases N with
  | zero =>
    filter_upwards [Measure.rnDeriv_zero (volume : Measure Space)] with x hx
    simpa [ordinaryDensity,rawOneParticleLaw,Measure.sum_fintype,spatialDensity] using congrArg ENNReal.toReal hx
  | succ N => exact ordinaryDensity_eq_density hψ

end Pauli

theorem ordinaryDensity_memLp {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ) :
    MemLp (ordinaryDensity ψ) (5/3) := by
  have hae := Pauli.ordinaryDensity_eq_spatialDensity hψ.sobolevFermion.sobolevVector
  have hi : Integrable (fun x => (ordinaryDensity ψ x)^(5/3:ℝ)) := by
    apply Integrable.congr (f := fun x => (Pauli.spatialDensity ψ hψ.1 x)^(5/3:ℝ))
    · cases N with
      | zero => simp [Pauli.spatialDensity,Real.zero_rpow (by norm_num : (5/3:ℝ) ≠ 0)]
      | succ N => exact Pauli.density_power_integrable ψ hψ
    · exact hae.symm.mono (fun x hx => congrArg (fun a : ℝ => a^(5/3:ℝ)) hx)
  apply (integrable_norm_rpow_iff (ordinaryDensity_measurable ψ).aestronglyMeasurable
    (by norm_num : (5/3:ENNReal) ≠ 0) (ENNReal.div_ne_top (by norm_num) (by norm_num) : (5/3:ENNReal) ≠ ⊤)).mp
  simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat,
    Real.norm_of_nonneg (ordinaryDensity_nonneg ψ _)] using hi

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FockKineticReindexBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators

lemma sum_out_reindex {L : ℕ} (b : Fin L → Fin 2) (f : Fin L → ℝ) :
    (∑ i : Fin (cutOutNumber b), f (cutOrder b (finSumFinEquiv (Sum.inr i)))) =
      ∑ i : Fin L, if b i = 1 then f i else 0 := by
  classical
  have hl (i : Fin (cutCoreNumber b)) : b (cutOrder b (finSumFinEquiv (Sum.inl i))) = 0 := by
    have h := congrFun (cutOrder_labels b) (finSumFinEquiv (Sum.inl i))
    simpa only [Function.comp_apply,coreCutLabels,joinLists_left] using h
  have hr (i : Fin (cutOutNumber b)) : b (cutOrder b (finSumFinEquiv (Sum.inr i))) = 1 := by
    have h := congrFun (cutOrder_labels b) (finSumFinEquiv (Sum.inr i))
    simpa only [Function.comp_apply,coreCutLabels,joinLists_right] using h
  rw [← Equiv.sum_comp (cutOrder b),← Equiv.sum_comp finSumFinEquiv,Fintype.sum_sum_type]
  simp only [hl,hr,zero_ne_one,ite_false,ite_true,Finset.sum_const_zero,zero_add]

lemma outKinetic_reindex {L : ℕ} (b : Fin L → Fin 2) (ψ : FormVector L) :
    outKinetic (reindexForm (cutOrder b) ψ) =
      (1/2:ℝ)*∑ s : Spins L, ∑ i : Fin L, if b i = 1 then
        (∑ a : Fin 3, ∫ x : Configuration L, ‖ψ.gradient s i a x‖^2) else 0 := by
  classical
  unfold outKinetic
  have he (s : Spins (cutCoreNumber b+cutOutNumber b))
      (i : Fin (cutOutNumber b)) (a : Fin 3) :
      (∫ z, ‖(reindexForm (cutOrder b) ψ).gradient s (finSumFinEquiv (Sum.inr i)) a z‖^2) =
        ∫ x, ‖ψ.gradient (s ∘ (cutOrder b).symm) (cutOrder b (finSumFinEquiv (Sum.inr i))) a x‖^2 :=
    integral_reindex (cutOrder b) (fun x =>
      ‖ψ.gradient (s ∘ (cutOrder b).symm) (cutOrder b (finSumFinEquiv (Sum.inr i))) a x‖^2)
  simp_rw [he]
  have hs (s : Spins (cutCoreNumber b+cutOutNumber b)) :=
    sum_out_reindex b (fun j => ∑ a : Fin 3, ∫ x : Configuration L,
      ‖ψ.gradient (s ∘ (cutOrder b).symm) j a x‖^2)
  simp_rw [hs]
  congr 1
  exact sum_spin_reindex (cutOrder b) (fun s => ∑ i : Fin L, if b i = 1 then
    (∑ a : Fin 3, ∫ x : Configuration L, ‖ψ.gradient s i a x‖^2) else 0)

lemma full_out_kinetic_eq {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L) :
    (∑ b : Fin L → Fin 2, outKinetic (orderedCutForm p hp ψ b)) =
      unorderedOutKinetic p hp ψ := by
  simp only [orderedCutForm,outKinetic_reindex,unorderedOutKinetic,Finset.mul_sum]

open MeasureTheory Filter
open scoped BigOperators

lemma core_branch_gradient_zero {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L)
    (b : Fin L → Fin 2) (s : Spins L) (i : Fin L) (a : Fin 3) (x : Configuration L)
    (hi : b i = 0) (h0 : (p 0).value (x i) = 0)
    (hd : lineDeriv ℝ (p 0).value (x i) (spaceDirections a) = 0) :
    (multiplyForm (spatialProduct p hp b) ψ).gradient s i a x = 0 := by
  classical
  have hv : (spatialProduct p hp b).value x = 0 := by
    change (∏ j, (p (b j)).value (x j)) = 0
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi,h0])
  have hder : lineDeriv ℝ (spatialProduct p hp b).value x (direction i a) = 0 := by
    change lineDeriv ℝ (spatialProductValue p b) x (direction i a) = 0
    rw [spatialProduct_derivative,hi,hd,mul_zero]
  change (↑((spatialProduct p hp b).value x):ℂ)*_+Complex.ofReal
    (lineDeriv ℝ (spatialProduct p hp b).value x (direction i a))*_ = 0
  rw [hv,hder,Complex.ofReal_zero,zero_mul,zero_mul,zero_add]

lemma weighted_gradient_le_out_branches {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L)
    (q : SmoothMultiplier spaceDirections) (hq : ∀ x, |q.value x| ≤ 1)
    (hcore : ∀ x, q.value x ≠ 0 → (p 0).value x = 0)
    (hder : ∀ x, q.value x ≠ 0 → ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    (s : Spins L) (i : Fin L) (a : Fin 3) (x : Configuration L) :
    q.value (x i)^2*‖ψ.gradient s i a x‖^2 ≤
      ∑ b : Fin L → Fin 2, if b i = 1 then
        ‖(multiplyForm (spatialProduct p hp b) ψ).gradient s i a x‖^2 else 0 := by
  classical
  by_cases hq0 : q.value (x i) = 0
  · rw [hq0,zero_pow (by decide : 2 ≠ 0),zero_mul]
    exact Finset.sum_nonneg (fun b _ => by split_ifs <;> positivity)
  have hfull := finite_partition_gradient (spatialProduct p hp) (spatial_square_partition p hp) ψ s i a x
  have hsum : (∑ b : Fin L → Fin 2, if b i = 1 then
        ‖(multiplyForm (spatialProduct p hp b) ψ).gradient s i a x‖^2 else 0) =
      ∑ b : Fin L → Fin 2, ‖(multiplyForm (spatialProduct p hp b) ψ).gradient s i a x‖^2 := by
    apply Finset.sum_congr rfl
    intro b _
    split_ifs with hb
    · rfl
    · have hb0 : b i = 0 := by omega
      rw [core_branch_gradient_zero p hp ψ b s i a x hb0 (hcore _ hq0) (hder _ hq0 a)]
      simp
  rw [hsum,hfull]
  have hq1 : q.value (x i)^2 ≤ 1 := by nlinarith [hq (x i),sq_abs (q.value (x i)),abs_nonneg (q.value (x i))]
  have hh := mul_le_mul_of_nonneg_right hq1 (sq_nonneg ‖ψ.gradient s i a x‖)
  have he : 0 ≤ (∑ j, lineDeriv ℝ (spatialProduct p hp j).value x (direction i a)^2)*‖ψ.value s x‖^2 := by positivity
  nlinarith only [hh,he]

lemma local_gradient_integrable {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (q : SmoothMultiplier spaceDirections) (s : Spins L) (i : Fin L) (a : Fin 3) :
    Integrable (fun x : Configuration L => q.value (x i)^2*‖ψ.gradient s i a x‖^2) := by
  have hc : Continuous (fun x : Configuration L => q.value (x i)) :=
    q.regular.continuous.comp (continuous_apply i)
  have hb : ∃ C, ∀ x : Configuration L, |q.value (x i)| ≤ C := by
    obtain ⟨C,hC⟩ := q.bound
    exact ⟨C,fun x => hC (x i)⟩
  have hh := (memLp_bounded_mul hc hb (hψ.2.1 s i a)).norm.integrable_sq
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,Function.comp_apply] using hh

lemma local_gradient_integral_le {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    (q : SmoothMultiplier spaceDirections) (hq : ∀ x, |q.value x| ≤ 1)
    (hcore : ∀ x, q.value x ≠ 0 → (p 0).value x = 0)
    (hder : ∀ x, q.value x ≠ 0 → ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    (s : Spins L) (i : Fin L) (a : Fin 3) :
    (∫ x, q.value (x i)^2*‖ψ.gradient s i a x‖^2) ≤
      ∑ b : Fin L → Fin 2, if b i = 1 then
        (∫ x, ‖(multiplyForm (spatialProduct p hp b) ψ).gradient s i a x‖^2) else 0 := by
  classical
  have hb (b : Fin L → Fin 2) : Integrable (fun x => if b i = 1 then
      ‖(multiplyForm (spatialProduct p hp b) ψ).gradient s i a x‖^2 else 0) := by
    split_ifs
    · exact ((hψ.multiply _).2.1 s i a).norm.integrable_sq
    · exact (integrable_zero _ _ _ : Integrable (fun _ : Configuration L => (0:ℝ)))
  have hh := integral_mono (local_gradient_integrable hψ q s i a)
    (integrable_finsetSum _ (fun b _ => hb b))
    (weighted_gradient_le_out_branches p hp ψ q hq hcore hder s i a)
  rw [integral_finsetSum _ (fun b _ => hb b)] at hh
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp

 theorem localGradientTrace_le_full_out {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    (q : SmoothMultiplier spaceDirections) (hq : ∀ x, |q.value x| ≤ 1)
    (hcore : ∀ x, q.value x ≠ 0 → (p 0).value x = 0)
    (hder : ∀ x, q.value x ≠ 0 → ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0) :
    localGradientTrace ψ q ≤ 2*∑ b : Fin L → Fin 2, outKinetic (orderedCutForm p hp ψ b) := by
  classical
  rw [full_out_kinetic_eq,unorderedOutKinetic]
  rw [←mul_assoc,show (2:ℝ)*(1/2)=1 by norm_num,one_mul]
  have hh := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Spins L))) =>
    Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin L))) =>
      Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) =>
        local_gradient_integral_le hψ p hp q hq hcore hder s i a)))
  apply hh.trans_eq
  conv_lhs => arg 2; ext s; arg 2; ext i; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext s; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro i _
  split_ifs <;> simp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpFreshPatchBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace

namespace CoulombAtom

lemma smoothMultiplyL2_ae (p : SmoothMultiplier spaceDirections)
    (f : Lp ℂ 2 (volume : Measure Space)) :
    (smoothMultiplyL2 p f : Space → ℂ) =ᵐ[volume] fun x => (p.value x : ℂ)*f x :=
  (memLp_bounded_mul p.regular.continuous p.bound (Lp.memLp f)).coeFn_toLp

lemma smoothMultiplyL2_norm_le (p : SmoothMultiplier spaceDirections)
    (hp : ∀ x, |p.value x| ≤ 1) (f : Lp ℂ 2 (volume : Measure Space)) :
    ‖smoothMultiplyL2 p f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [smoothMultiplyL2_ae p f] with x hx
  rw [hx,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  simpa using mul_le_mul_of_nonneg_right (hp x) (norm_nonneg (f x))

lemma smoothMultiplyL2_inner (p : SmoothMultiplier spaceDirections)
    (f g : Lp ℂ 2 (volume : Measure Space)) :
    inner ℂ f (smoothMultiplyL2 p g) = inner ℂ (smoothMultiplyL2 p f) g := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [smoothMultiplyL2_ae p f,smoothMultiplyL2_ae p g] with x hf hg
  rw [hf,hg]
  change (p.value x:ℂ)*g x*starRingEnd ℂ (f x) =
    g x*starRingEnd ℂ ((p.value x:ℂ)*f x)
  rw [map_mul,Complex.conj_ofReal]
  ring

lemma smoothDerivativeProductL2_ae (p : SmoothMultiplier spaceDirections)
    (a : Fin 3) (f g : Lp ℂ 2 (volume : Measure Space)) :
    (smoothDerivativeProductL2 p a f g : Space → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ)*g x + Complex.ofReal (lineDeriv ℝ p.value x (spaceDirections a))*f x :=
  ((memLp_bounded_mul p.regular.continuous p.bound (Lp.memLp g)).add
    (memLp_bounded_mul (p.derivative_continuous a) (p.gradient_bound a) (Lp.memLp f))).coeFn_toLp

lemma smoothMultiplyL2_weak (p : SmoothMultiplier spaceDirections)
    {a : Fin 3} {f g : Lp ℂ 2 (volume : Measure Space)}
    (hw : HasWeakDirectionalDerivative f g (spaceDirections a)) :
    HasWeakDirectionalDerivative (smoothMultiplyL2 p f)
      (smoothDerivativeProductL2 p a f g) (spaceDirections a) :=
  (IsWeakDerivative.mul_smooth hw (Lp.memLp f) (Lp.memLp g) p.regular).congr_ae
    (smoothMultiplyL2_ae p f).symm (smoothDerivativeProductL2_ae p a f g).symm

end CoulombAtom
namespace CoulombLT
open CoulombAtom

lemma BesselFamily.smoothMultiply {ι : Type*} [Fintype ι]
    {f : ι → Lp ℂ 2 (volume : Measure Space)} (hf : BesselFamily f)
    (p : SmoothMultiplier spaceDirections) (hp : ∀ x, |p.value x| ≤ 1) :
    BesselFamily (fun j => smoothMultiplyL2 p (f j)) := by
  intro u
  simp only [smoothMultiplyL2_inner]
  exact (hf (smoothMultiplyL2 p u)).trans
    (pow_le_pow_left₀ (norm_nonneg _) (smoothMultiplyL2_norm_le p hp u) 2)

lemma infiniteDensity_smoothMultiply {ι : Type*} [Countable ι]
    (f : ι → Lp ℂ 2 (volume : Measure Space)) (p : SmoothMultiplier spaceDirections) :
    ∀ᵐ x ∂volume, infiniteDensity (fun j => smoothMultiplyL2 p (f j)) x =
      ENNReal.ofReal (p.value x^2)*infiniteDensity f x := by
  filter_upwards [ae_all_iff.mpr (fun j => smoothMultiplyL2_ae p (f j))] with x hx
  unfold infiniteDensity
  simp only [hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,
    ENNReal.ofReal_mul (sq_nonneg _),ENNReal.tsum_mul_left]

theorem localized_family_lieb_thirring {ι : Type*} [Countable ι]
    {f : ι → Lp ℂ 2 (volume : Measure Space)}
    {g : Fin 3 → ι → Lp ℂ 2 (volume : Measure Space)}
    (hf : ∀ s : Finset ι, BesselFamily (fun j : s => f j))
    (hw : ∀ a j, HasWeakDirectionalDerivative (f j) (g a j) (spaceDirections a))
    (p : SmoothMultiplier spaceDirections) (hp : ∀ x, |p.value x| ≤ 1) :
    (∫⁻ x, (ENNReal.ofReal (p.value x^2)*infiniteDensity f x)^(5/3:ℝ)) ≤
      16*(∑' j, ENNReal.ofReal (‖smoothMultiplyL2 p (f j)‖^2))+
        ENNReal.ofReal (1024/3:ℝ)*(∑ a, ∑' j,
          ENNReal.ofReal (‖smoothDerivativeProductL2 p a (f j) (g a j)‖^2)) := by
  have hb (s : Finset ι) : BesselFamily (fun j : s => smoothMultiplyL2 p (f j)) :=
    (hf s).smoothMultiply p hp
  have hd (a : Fin 3) (j : ι) : HasWeakDirectionalDerivative (smoothMultiplyL2 p (f j))
      (smoothDerivativeProductL2 p a (f j) (g a j)) (EuclideanSpace.single a 1) :=
    smoothMultiplyL2_weak p (hw a j)
  have h := weak_family_lieb_thirring
    (f := fun j : ι => smoothMultiplyL2 p (f j))
    (g := fun a j => smoothDerivativeProductL2 p a (f j) (g a j)) hb hd
  calc
    _ = ∫⁻ x, infiniteDensity (fun j => smoothMultiplyL2 p (f j)) x^(5/3:ℝ) := by
      apply lintegral_congr_ae
      filter_upwards [infiniteDensity_smoothMultiply f p] with x hx
      rw [hx]
    _ ≤ _ := h

end CoulombLT

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_LocalDensityTraceBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombLT

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_LocalDensityTrace_barrier_scope

open MeasureTheory Filter
open scoped BigOperators ENNReal

open CoulombAtom

lemma infiniteDensity_aemeasurable {ι : Type*} [Countable ι]
    (f : ι → Lp ℂ 2 (volume : Measure Space)) :
    AEMeasurable (infiniteDensity f) volume :=
  AEMeasurable.tsum (fun j => ((Lp.memLp (f j)).aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal)

lemma family_trace_eq_lintegral {ι : Type*} [Countable ι]
    (f : ι → Lp ℂ 2 (volume : Measure Space)) :
    (∑' j, ENNReal.ofReal (‖f j‖^2)) = ∫⁻ x, infiniteDensity f x := by
  unfold infiniteDensity
  rw [lintegral_tsum (f := fun j x => ENNReal.ofReal (‖f j x‖^2))
    (fun j => ((Lp.memLp (f j)).aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal)]
  apply tsum_congr
  intro j
  rw [CoulombPauli.l2_norm_sq]
  exact ofReal_integral_eq_lintegral_ofReal (Lp.memLp (f j)).norm.integrable_sq
    (ae_of_all _ (fun _ => sq_nonneg _))

lemma smoothMultiply_trace {ι : Type*} [Countable ι]
    (f : ι → Lp ℂ 2 (volume : Measure Space)) (p : SmoothMultiplier spaceDirections) :
    (∑' j, ENNReal.ofReal (‖smoothMultiplyL2 p (f j)‖^2)) =
      ∫⁻ x, ENNReal.ofReal (p.value x^2)*infiniteDensity f x := by
  rw [family_trace_eq_lintegral]
  exact lintegral_congr_ae (infiniteDensity_smoothMultiply f p)

lemma complex_norm_add_sq_bound (u v : ℂ) : ‖u+v‖^2 ≤ 2*‖u‖^2+2*‖v‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (u+v)) (norm_add_le u v) 2
  nlinarith [sq_nonneg (‖u‖-‖v‖)]

lemma smoothDerivative_density_bound {ι : Type*} [Countable ι]
    (f g : ι → Lp ℂ 2 (volume : Measure Space)) (p : SmoothMultiplier spaceDirections)
    (a : Fin 3) :
    ∀ᵐ x ∂volume, infiniteDensity (fun j => smoothDerivativeProductL2 p a (f j) (g j)) x ≤
      2*ENNReal.ofReal (p.value x^2)*infiniteDensity g x+
        2*ENNReal.ofReal ((lineDeriv ℝ p.value x (spaceDirections a))^2)*infiniteDensity f x := by
  filter_upwards [ae_all_iff.mpr (fun j => smoothDerivativeProductL2_ae p a (f j) (g j))] with x hx
  have hh (j : ι) : ENNReal.ofReal (‖smoothDerivativeProductL2 p a (f j) (g j) x‖^2) ≤
      2*ENNReal.ofReal (p.value x^2)*ENNReal.ofReal (‖g j x‖^2)+
        2*ENNReal.ofReal ((lineDeriv ℝ p.value x (spaceDirections a))^2)*ENNReal.ofReal (‖f j x‖^2) := by
    rw [hx j]
    have hb := complex_norm_add_sq_bound ((p.value x:ℂ)*g j x)
      (Complex.ofReal (lineDeriv ℝ p.value x (spaceDirections a))*f j x)
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs] at hb
    have he : ENNReal.ofReal (2*(p.value x^2*‖g j x‖^2)+
        2*((lineDeriv ℝ p.value x (spaceDirections a))^2*‖f j x‖^2)) =
        2*ENNReal.ofReal (p.value x^2)*ENNReal.ofReal (‖g j x‖^2)+
        2*ENNReal.ofReal ((lineDeriv ℝ p.value x (spaceDirections a))^2)*ENNReal.ofReal (‖f j x‖^2) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      simp only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_mul (sq_nonneg _),
        ENNReal.ofReal_ofNat,mul_assoc]
    exact (ENNReal.ofReal_le_ofReal hb).trans_eq he
  change (∑' j, _) ≤ _
  calc
    _ ≤ ∑' j, (2*ENNReal.ofReal (p.value x^2)*ENNReal.ofReal (‖g j x‖^2)+
        2*ENNReal.ofReal ((lineDeriv ℝ p.value x (spaceDirections a))^2)*ENNReal.ofReal (‖f j x‖^2)) :=
      ENNReal.tsum_le_tsum hh
    _ = _ := by rw [ENNReal.tsum_add,ENNReal.tsum_mul_left,ENNReal.tsum_mul_left]; rfl

lemma smoothDerivative_trace_bound {ι : Type*} [Countable ι]
    (f g : ι → Lp ℂ 2 (volume : Measure Space)) (p : SmoothMultiplier spaceDirections)
    (a : Fin 3) :
    (∑' j, ENNReal.ofReal (‖smoothDerivativeProductL2 p a (f j) (g j)‖^2)) ≤
      2*(∫⁻ x, ENNReal.ofReal (p.value x^2)*infiniteDensity g x)+
      2*(∫⁻ x, ENNReal.ofReal ((lineDeriv ℝ p.value x (spaceDirections a))^2)*infiniteDensity f x) := by
  rw [family_trace_eq_lintegral]
  calc
    _ ≤ ∫⁻ x, (2*ENNReal.ofReal (p.value x^2)*infiniteDensity g x+
        2*ENNReal.ofReal ((lineDeriv ℝ p.value x (spaceDirections a))^2)*infiniteDensity f x) :=
      lintegral_mono_ae (smoothDerivative_density_bound f g p a)
    _ = _ := by
      have hm : AEMeasurable (fun x : Space =>
          2*(ENNReal.ofReal (p.value x^2)*infiniteDensity g x)) volume :=
        ((p.regular.continuous.pow 2).measurable.ennreal_ofReal.aemeasurable.mul
          (infiniteDensity_aemeasurable g)).const_mul (2:ℝ≥0∞)
      simp only [mul_assoc]
      rw [lintegral_add_left' hm,
        lintegral_const_mul' _ _ (by norm_num),lintegral_const_mul' _ _ (by norm_num)]

end Work_LocalDensityTrace_barrier_scope

open MeasureTheory Filter
open scoped BigOperators ENNReal

open CoulombPauli CoulombPackets CoulombAtom
variable {N : ℕ} {κ : Type*}

lemma indexed_density_eq [Countable κ]
    (b : HilbertBasis κ ℂ (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := Space)))))
    (ψ : Fin (N+1) → fermionL2 (V := Space) (N+1)) :
    ∀ᵐ x ∂(volume : Measure Space), infiniteDensity (indexedFermionFamily b ψ) x =
      ENNReal.ofReal (1/2:ℝ) * (∑ i : Fin (N+1), ∑ s : Fin 2, ∫⁻ y,
        ENNReal.ofReal (‖splitFermion i (ψ i) ((x,s),y)‖^2)
          ∂(configMeasure N (spinSpaceMeasure (V := Space)))) := by
  have he (p : Fin (N+1) × Fin 2 × κ) :
      (fun x => indexedFermionFamily b ψ p x) =ᵐ[volume]
        (fun x => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
          spinMarginal (splitFermion p.1 (ψ p.1)) p.2.1 (b p.2.2) x) :=
    Lp.coeFn_smul _ _
  filter_upwards [ae_all_iff.mpr he,
    ae_all_iff.mpr (fun i : Fin (N+1) => spinMarginal_slice_parseval b (splitFermion i (ψ i)))]
      with x hx hy
  unfold infiniteDensity
  simp_rw [hx,half_scale_norm_sq,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [ENNReal.tsum_mul_left,ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_prod',hy,tsum_fintype]

lemma indexed_density_weighted [Countable κ]
    (b : HilbertBasis κ ℂ (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := Space)))))
    (ψ : Fin (N+1) → fermionL2 (V := Space) (N+1))
    (w : Space → ℝ) (hw : Measurable w) :
    (∫⁻ x, ENNReal.ofReal (w x)*infiniteDensity (indexedFermionFamily b ψ) x) =
      ENNReal.ofReal (1/2:ℝ)*(∑ i : Fin (N+1), ∫⁻ q,
        ENNReal.ofReal (w (q i).1)*ENNReal.ofReal (‖ψ i q‖^2)
          ∂(configMeasure (N+1) (spinSpaceMeasure (V := Space)))) := by
  calc
    _ = ∫⁻ x, ENNReal.ofReal (1/2:ℝ)*(∑ i : Fin (N+1),
        ENNReal.ofReal (w x)*(∑ s : Fin 2, ∫⁻ y,
          ENNReal.ofReal (‖splitFermion i (ψ i) ((x,s),y)‖^2)
            ∂(configMeasure N (spinSpaceMeasure (V := Space))))) := by
      apply lintegral_congr_ae
      filter_upwards [indexed_density_eq b ψ] with x hx
      rw [hx,← Finset.mul_sum]
      ac_rfl
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finsetSum' (f := fun i x => ENNReal.ofReal (w x)*
          (∑ s : Fin 2, ∫⁻ y, ENNReal.ofReal (‖splitFermion i (ψ i) ((x,s),y)‖^2)
            ∂(configMeasure N (spinSpaceMeasure (V := Space))))) Finset.univ (fun i _ =>
          hw.ennreal_ofReal.aemeasurable.mul (coordinateDensity_aemeasurable (ψ i) i))]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => coordinate_density_weighted (ψ i) i w hw)

lemma fermionFamily_weighted [Countable κ]
    (b : HilbertBasis κ ℂ (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := Space)))))
    (ψ : fermionL2 (V := Space) (N+1)) (w : Space → ℝ) (hw : Measurable w) :
    (∫⁻ x, ENNReal.ofReal (w x)*infiniteDensity (fermionFamily b ψ) x) =
      ENNReal.ofReal (1/2:ℝ)* coordinateWeightedTrace (fun _ => ψ) w :=
  indexed_density_weighted b (fun _ => ψ) w hw

end CoulombLT

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_LocalFermionDensityBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace CoulombLT
open CoulombPauli CoulombPackets CoulombAtom
local instance instFactNeENNRealOfNatTop_solutions_1 : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

theorem fermion_local_density {N : ℕ}
    (ψ : fermionL2 (V := Space) (N+1))
    (u : Fin (N+1) → Fin 3 → fermionL2 (V := Space) (N+1))
    (hw : ∀ i a, HasWeakSpinPartialDerivative (splitFermion i ψ)
      (splitFermion i (u i a)) (EuclideanSpace.single a 1))
    (hn : ‖ψ‖^2 = 1)
    (ha : ∀ i j : Fin (N+1), i ≠ j → permute (Equiv.swap i j) ψ = -ψ)
    (p : SmoothMultiplier spaceDirections) (hp : ∀ x, |p.value x| ≤ 1) :
    (∫⁻ x, (ENNReal.ofReal (p.value x^2)*fermionDensity ψ x)^(5/3:ℝ)) ≤
      32*coordinateWeightedTrace (fun _ => ψ) (fun x => p.value x^2)+
      ENNReal.ofReal (4096/3:ℝ)*(∑ a : Fin 3,
        (coordinateWeightedTrace (fun i => u i a) (fun x => p.value x^2)+
         coordinateWeightedTrace (fun _ => ψ)
           (fun x => (lineDeriv ℝ p.value x (spaceDirections a))^2))) := by
  let : MeasureTheory.IsSeparable (configMeasure N (spinSpaceMeasure (V := Space))) :=
    MeasureTheory.isSeparable_of_sigmaFinite _
  obtain ⟨κ,b,-⟩ := exists_hilbertBasis ℂ
    (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := Space))))
  let : Countable κ := hilbertBasis_countable b
  let f := fermionFamily b ψ
  let g (a : Fin 3) := indexedFermionFamily b (fun i => u i a)
  have hg (a : Fin 3) (q : Fin (N+1) × Fin 2 × κ) :
      HasWeakDirectionalDerivative (f q) (g a q) (EuclideanSpace.single a 1) :=
    weak_derivative_smul_L2 (spinMarginal_weak_derivative (hw q.1 a) q.2.1 (b q.2.2)) _
  have hb := localized_family_lieb_thirring (fermionFamily_bessel b ψ hn ha) hg p hp
  have htrace : (∑' j, ENNReal.ofReal (‖smoothMultiplyL2 p (f j)‖^2)) =
      ENNReal.ofReal (1/2:ℝ)*coordinateWeightedTrace (fun _ => ψ) (fun x => p.value x^2) := by
    rw [smoothMultiply_trace]
    exact fermionFamily_weighted b ψ _ (p.regular.continuous.pow 2).measurable
  have hgrad (a : Fin 3) :
      (∑' j, ENNReal.ofReal (‖smoothDerivativeProductL2 p a (f j) (g a j)‖^2)) ≤
        coordinateWeightedTrace (fun i => u i a) (fun x => p.value x^2)+
        coordinateWeightedTrace (fun _ => ψ)
          (fun x => (lineDeriv ℝ p.value x (spaceDirections a))^2) := by
    have ht := smoothDerivative_trace_bound f (g a) p a
    rw [indexed_density_weighted b (fun i => u i a) (fun x => p.value x^2) (p.regular.continuous.pow 2).measurable,
      fermionFamily_weighted b ψ (fun x => (lineDeriv ℝ p.value x (spaceDirections a))^2)
        ((p.derivative_continuous a).pow 2).measurable] at ht
    have hc : (2:ℝ≥0∞)*ENNReal.ofReal (1/2:ℝ) = 1 := by
      rw [show (2:ℝ≥0∞)=ENNReal.ofReal (2:ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    simpa only [← mul_assoc,hc,one_mul,coordinateWeightedTrace] using ht
  rw [htrace] at hb
  have hgb := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) => hgrad a)
  have hc : (2:ℝ≥0∞)^(5/3:ℝ) ≤ 4 := by
    calc _ ≤ (2:ℝ≥0∞)^(2:ℝ) :=
           ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
         _ = _ := by norm_num
  calc
    _ = ∫⁻ x, (2*(ENNReal.ofReal (p.value x^2)*infiniteDensity f x))^(5/3:ℝ) := by
      apply lintegral_congr_ae
      filter_upwards [fermionDensity_eq_family b ψ] with x hx
      rw [hx]
      congr 1
      ac_rfl
    _ ≤ ∫⁻ x, 4*(ENNReal.ofReal (p.value x^2)*infiniteDensity f x)^(5/3:ℝ) := by
      apply lintegral_mono
      intro x
      simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 5/3)]
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 4*(∫⁻ x, (ENNReal.ofReal (p.value x^2)*infiniteDensity f x)^(5/3:ℝ)) :=
      lintegral_const_mul' _ _ (by norm_num)
    _ ≤ 4*(16*(ENNReal.ofReal (1/2:ℝ)*coordinateWeightedTrace (fun _ => ψ) (fun x => p.value x^2))+
        ENNReal.ofReal (1024/3:ℝ)*(∑ a, ∑' j,
          ENNReal.ofReal (‖smoothDerivativeProductL2 p a (f j) (g a j)‖^2))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ 4*(16*(ENNReal.ofReal (1/2:ℝ)*coordinateWeightedTrace (fun _ => ψ) (fun x => p.value x^2))+
        ENNReal.ofReal (1024/3:ℝ)*(∑ a : Fin 3,
          (coordinateWeightedTrace (fun i => u i a) (fun x => p.value x^2)+
           coordinateWeightedTrace (fun _ => ψ)
             (fun x => (lineDeriv ℝ p.value x (spaceDirections a))^2)))) := by
      gcongr
    _ = _ := by
      simp only [mul_add,← mul_assoc]
      congr 1
      · congr 1
        norm_num only [Nat.reduceMul]
        rw [show (64:ℝ≥0∞)=ENNReal.ofReal (64:ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 64)]
        norm_num
      · congr 1
        rw [show (4:ℝ≥0∞)=ENNReal.ofReal (4:ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
        norm_num

end CoulombLT

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace CoulombAtom.Pauli
open CoulombPauli CoulombPackets CoulombLT

lemma square_weight_integrable {L : ℕ} {v : Configuration L → ℂ}
    (hv : MemLp v 2) (r : Space → ℝ) (hr : Continuous r)
    (hb : ∃ C, ∀ x, |r x| ≤ C) (i : Fin L) :
    Integrable (fun x : Configuration L => r (x i)^2*‖v x‖^2) := by
  have hh := (memLp_bounded_mul (hr.comp (continuous_apply i))
    (by obtain ⟨C,hC⟩ := hb; exact ⟨C,fun x => hC (x i)⟩) hv).norm.integrable_sq
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,Function.comp_apply] using hh

lemma coordinateWeightedTrace_form {N : ℕ}
    (φ : Fin (N+1) → FormVector (N+1)) (hφ : ∀ i s, MemLp ((φ i).value s) 2)
    (w : Space → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hI : ∀ i s, Integrable (fun x : Configuration (N+1) => w (x i)*‖(φ i).value s x‖^2)) :
    coordinateWeightedTrace (fun i => toMany (φ i) (hφ i)) w =
      ENNReal.ofReal (∑ i : Fin (N+1), ∑ s : Spins (N+1),
        ∫ x : Configuration (N+1), w (x i)*‖(φ i).value s x‖^2) := by
  unfold coordinateWeightedTrace
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg
    (fun s _ => integral_nonneg (fun x => mul_nonneg (hw0 _) (sq_nonneg _))))]
  apply Finset.sum_congr rfl
  intro i _
  rw [toMany_coordinate_lintegral (φ i) (hφ i) i w hw,
    ENNReal.ofReal_sum_of_nonneg (fun s _ => integral_nonneg
      (fun x => mul_nonneg (hw0 _) (sq_nonneg _)))]
  apply Finset.sum_congr rfl
  intro s _
  rw [ofReal_integral_eq_lintegral_ofReal (hI i s)
    (ae_of_all _ (fun x => mul_nonneg (hw0 _) (sq_nonneg _)))]
  apply lintegral_congr
  intro x
  exact (ENNReal.ofReal_mul (hw0 _)).symm

lemma coordinateWeightedTrace_square_form {N : ℕ}
    (φ : Fin (N+1) → FormVector (N+1)) (hφ : ∀ i s, MemLp ((φ i).value s) 2)
    (r : Space → ℝ) (hr : Continuous r) (hb : ∃ C, ∀ x, |r x| ≤ C) :
    coordinateWeightedTrace (fun i => toMany (φ i) (hφ i)) (fun x => r x^2) =
      ENNReal.ofReal (∑ i : Fin (N+1), ∑ s : Spins (N+1),
        ∫ x : Configuration (N+1), r (x i)^2*‖(φ i).value s x‖^2) :=
  coordinateWeightedTrace_form φ hφ _ (hr.pow 2).measurable (fun _ => sq_nonneg _)
    (fun i s => square_weight_integrable (hφ i s) r hr hb i)

lemma coordinateWeightedTrace_square_mass {N : ℕ} {ψ : FormVector (N+1)}
    (hψ : ∀ s, MemLp (ψ.value s) 2)
    (r : Space → ℝ) (hr : Continuous r) (hb : ∃ C, ∀ x, |r x| ≤ C) :
    coordinateWeightedTrace (fun _ : Fin (N+1) => toMany ψ hψ) (fun x => r x^2) =
      ENNReal.ofReal (weightedParticleCount ψ (fun x => r x^2)) := by
  rw [coordinateWeightedTrace_square_form (fun _ => ψ) (fun _ => hψ) r hr hb]
  congr 1
  exact Finset.sum_comm

lemma coordinateWeightedTrace_square_gradient {N : ℕ} (ψ : FormVector (N+1))
    (hψ : FormAdmissible ψ) (a : Fin 3)
    (r : Space → ℝ) (hr : Continuous r) (hb : ∃ C, ∀ x, |r x| ≤ C) :
    coordinateWeightedTrace (fun i => gradientMany ψ hψ i a) (fun x => r x^2) =
      ENNReal.ofReal (∑ s : Spins (N+1), ∑ i : Fin (N+1),
        ∫ x, r (x i)^2*‖ψ.gradient s i a x‖^2) := by
  have he := coordinateWeightedTrace_square_form
    (fun i => gradientVector ψ i a) (fun i s => hψ.2.1 s i a) r hr hb
  exact he.trans (congrArg ENNReal.ofReal Finset.sum_comm)

end CoulombAtom.Pauli

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_LocalOrdinaryBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_LocalOrdinaryLT_barrier_scope

open MeasureTheory Filter
open scoped BigOperators ENNReal

open CoulombPauli CoulombPackets CoulombLT

lemma weightedParticleCount_sq_nonneg {N : ℕ} (ψ : FormVector N) (r : Space → ℝ) :
    0 ≤ weightedParticleCount ψ (fun x => r x^2) := by
  unfold weightedParticleCount
  exact Finset.sum_nonneg (fun s _ => Finset.sum_nonneg
    (fun i _ => integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))))

lemma localDensityBudget_nonneg {N : ℕ} (ψ : FormVector N)
    (p : SmoothMultiplier spaceDirections) : 0 ≤ localDensityBudget ψ p := by
  have he : 0 ≤ densityLocalizationError ψ p :=
    Finset.sum_nonneg (fun a _ => weightedParticleCount_sq_nonneg ψ _)
  have hg : 0 ≤ localGradientTrace ψ p := by
    unfold localGradientTrace
    exact Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun a _ => integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)))))
  have hm := weightedParticleCount_sq_nonneg ψ p.value
  unfold localDensityBudget
  positivity

namespace Pauli

 theorem form_local_density {N : ℕ} (ψ : FormVector (N+1))
    (hψ : FormAdmissible ψ) (p : SmoothMultiplier spaceDirections)
    (hp : ∀ x, |p.value x| ≤ 1) :
    (∫⁻ x, (ENNReal.ofReal (p.value x^2)*oneParticleDensity ψ hψ.1 x)^(5/3:ℝ)) ≤
      ENNReal.ofReal (localDensityBudget ψ p) := by
  have hn : ‖toMany ψ hψ.1‖^2 = 1 :=
    (toMany_norm_sq ψ hψ.1).trans hψ.2.2.2.2.1
  have ha (i j : Fin (N+1)) (hij : i ≠ j) :
      permute (Equiv.swap i j) (toMany ψ hψ.1) = -toMany ψ hψ.1 := by
    rw [toMany_permute ψ hψ.1 (Equiv.swap i j) (hψ.2.2.2.1 _)]
    simp [Equiv.Perm.sign_swap hij]
  have hw (i : Fin (N+1)) (a : Fin 3) := form_hasFermionGradient ψ hψ i a
  simp only [EuclideanSpace.basisFun_apply] at hw
  have hh := fermion_local_density (toMany ψ hψ.1) (gradientMany ψ hψ) hw hn ha p hp
  rw [coordinateWeightedTrace_square_mass hψ.1 p.value p.regular.continuous p.bound] at hh
  simp_rw [coordinateWeightedTrace_square_gradient ψ hψ _ p.value p.regular.continuous p.bound,
    coordinateWeightedTrace_square_mass hψ.1 _ (p.derivative_continuous _) (p.gradient_bound _)] at hh
  let G : Fin 3 → ℝ := fun a => ∑ s : Spins (N+1), ∑ i : Fin (N+1),
    ∫ x : Configuration (N+1), p.value (x i)^2*‖ψ.gradient s i a x‖^2
  let E : Fin 3 → ℝ := fun a => weightedParticleCount ψ
    (fun x => (lineDeriv ℝ p.value x (spaceDirections a))^2)
  have hG (a) : 0 ≤ G a := Finset.sum_nonneg (fun s _ => Finset.sum_nonneg
    (fun i _ => integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))))
  have hE (a) : 0 ≤ E a := weightedParticleCount_sq_nonneg ψ _
  have hs : (∑ a : Fin 3, (ENNReal.ofReal (G a)+ENNReal.ofReal (E a))) =
      ENNReal.ofReal (localGradientTrace ψ p+densityLocalizationError ψ p) := by
    have heq (a : Fin 3) : ENNReal.ofReal (G a)+ENNReal.ofReal (E a) =
        ENNReal.ofReal (G a+E a) := (ENNReal.ofReal_add (hG a) (hE a)).symm
    simp_rw [heq]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => add_nonneg (hG a) (hE a))]
    congr 1
    rw [Finset.sum_add_distrib]
    congr 1
    dsimp only [G,localGradientTrace]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    exact Finset.sum_comm
  change (∫⁻ x, (ENNReal.ofReal (p.value x^2)*oneParticleDensity ψ hψ.1 x)^(5/3:ℝ)) ≤
    32*ENNReal.ofReal (weightedParticleCount ψ (fun x => p.value x^2))+
      ENNReal.ofReal (4096/3:ℝ)*(∑ a : Fin 3, (ENNReal.ofReal (G a)+ENNReal.ofReal (E a))) at hh
  rw [hs] at hh
  have hn0 := weightedParticleCount_sq_nonneg ψ p.value
  have hge0 : 0 ≤ localGradientTrace ψ p+densityLocalizationError ψ p := by
    have hg : 0 ≤ localGradientTrace ψ p := by
      unfold localGradientTrace
      exact Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
        (fun a _ => integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)))))
    exact add_nonneg hg (Finset.sum_nonneg (fun a _ => hE a))
  simpa only [localDensityBudget,ENNReal.ofReal_add (mul_nonneg (by norm_num : (0:ℝ) ≤ 32) hn0)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 4096/3) hge0),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 32),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4096/3),ENNReal.ofReal_ofNat] using hh

 theorem form_local_density_real {N : ℕ} (ψ : FormVector (N+1))
    (hψ : FormAdmissible ψ) (p : SmoothMultiplier spaceDirections)
    (hp : ∀ x, |p.value x| ≤ 1) :
    (∫ x, (p.value x^2*density ψ hψ.1 x)^(5/3:ℝ)) ≤ localDensityBudget ψ p := by
  have hme := ((p.regular.continuous.pow 2).aemeasurable.ennreal_ofReal.mul
    (fermionDensity_aemeasurable (toMany ψ hψ.1))).pow_const (5/3:ℝ)
  have hb := form_local_density ψ hψ p hp
  have hn : (∫⁻ x, (ENNReal.ofReal (p.value x^2)*oneParticleDensity ψ hψ.1 x)^(5/3:ℝ)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have he := integral_toReal hme (ae_lt_top' hme hn)
  simp only [Pi.mul_apply,Pi.pow_apply,← ENNReal.toReal_rpow,ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg _)] at he
  change (∫ x, (p.value x^2*(fermionDensity (toMany ψ hψ.1) x).toReal)^(5/3:ℝ)) ≤ _
  rw [he]
  exact (ENNReal.toReal_le_toReal hn ENNReal.ofReal_ne_top).2 hb |>.trans_eq
    (ENNReal.toReal_ofReal (localDensityBudget_nonneg ψ p))

end Pauli

 theorem ordinaryDensity_local_lt {N : ℕ} (ψ : FormVector N)
    (hψ : FormAdmissible ψ) (p : SmoothMultiplier spaceDirections)
    (hp : ∀ x, |p.value x| ≤ 1) :
    (∫ x, (p.value x^2*ordinaryDensity ψ x)^(5/3:ℝ)) ≤ localDensityBudget ψ p := by
  cases N with
  | zero =>
    have hae := Pauli.ordinaryDensity_eq_spatialDensity hψ.sobolevFermion.sobolevVector
    have he : (fun x => (p.value x^2*ordinaryDensity ψ x)^(5/3:ℝ)) =ᵐ[volume] fun _ => (0:ℝ) := by
      filter_upwards [hae] with x hx
      simp only [hx,Pauli.spatialDensity,Pi.zero_apply,mul_zero,Real.zero_rpow (by norm_num : (5/3:ℝ) ≠ 0)]
    rw [integral_congr_ae he,integral_zero]
    exact localDensityBudget_nonneg ψ p
  | succ N =>
    have hae := Pauli.ordinaryDensity_eq_density hψ.sobolevFermion.sobolevVector
    have he := integral_congr_ae (hae.mono (fun x hx =>
      congrArg (fun t : ℝ => (p.value x^2*t)^(5/3:ℝ)) hx))
    rw [he]
    exact Pauli.form_local_density_real ψ hψ p hp

end Work_LocalOrdinaryLT_barrier_scope

open MeasureTheory Filter Set
open scoped BigOperators

 theorem sharp_cell_fresh_kinetic {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {y : Space} (hy : y ≠ 0)
    {b r Z lam : ℝ} (hb : 0 < b) (hba : b ≤ localCellRadius y)
    (hr : r ∈ Set.Icc (5*localCellRadius y) (6*localCellRadius y))
    (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hcollar : localCellRadius y ≤ b^2*localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) :
    ∃ hr0 : 0 ≤ r,
      (∑ c : Fin N → Fin 2, outKinetic (orderedCutForm (coreFirstRadialCut y hr0 hb)
        (coreFirstRadialCut_partition y hr0 hb) ψ c)) ≤
          sharpFreshKineticConstant*(localOffsetMass (max (corePriceExcess Z lam ψ) 0) y)^2/localCellRadius y := by
  let a := localCellRadius y
  let D := max (corePriceExcess Z lam ψ) 0
  let m := localOffsetMass D y
  let C := actualCellMomentConstant
  let F := sharpFreshFieldConstant
  have ha : 0 < a := localCellRadius_pos hy
  have hm1 : 1 ≤ m := localOffsetMass_one_le D y
  have hm0 : 0 ≤ m := le_trans zero_le_one hm1
  have hC : 1 ≤ C := actualCellMomentConstant_one_le
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hF0 : 0 ≤ F := le_trans zero_le_one sharpFreshFieldConstant_one_le
  have hsep : r+2*b ≤ ‖y‖ := by
    have hae : 100000*a = ‖y‖ := by dsimp [a,localCellRadius]; ring
    linarith [hr.2]
  obtain ⟨hr0,hfield,-⟩ := sharp_cell_fresh_field_mass hψ hm hy hb hba hr hZ hlam hcollar
  refine ⟨hr0,?_⟩
  have hB := priced_enlarged_cell_count hψ hm hZ hlam hy
  have hroot : Real.sqrt (rawCountMoment ψ y (32*a)) ≤ C*m := by
    simpa using sqrt_count_scale (rawCountMoment_nonneg ψ y (32*a)) hC
      (by norm_num : (0:ℝ) ≤ 1) hm0 (by simpa using hB)
  have hrootF : Real.sqrt (freshOutMaximumSecondMoment (coreFirstRadialCut y hr0 hb)
      (coreFirstRadialCut_partition y hr0 hb) ψ Z lam) ≤ F*(m/a) :=
    Real.sqrt_le_iff.mpr ⟨by positivity,hfield⟩
  have hcut := radial_out_kinetic_coupling hψ y hr0 hb hsep
    (show r+b ≤ 32*a by linarith [hr.2]) hZ hlam
  have hims := radial_ims_le_sqrt_count hψ.sobolevVector y hr0 hb
    (show r+b < 32*a by linarith [hr.2])
  rw [hm,Real.sqrt_one,mul_one] at hims
  have hI := localizationIMSConstant_nonneg
  have hK : (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2 = localizationIMSConstant/b^2 := by
    unfold localizationIMSConstant
    ring
  rw [hK] at hims
  have hma : m/b^2 ≤ m^2/a := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hb) ha).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hcollar hm0]
  have hims' : (1/2:ℝ)*weightedParticleCount ψ
      (spatialErrorWeight (coreFirstRadialCut y hr0 hb)) ≤
        localizationIMSConstant*C*(m^2/a) := by
    calc _ ≤ localizationIMSConstant/b^2*Real.sqrt (rawCountMoment ψ y (32*a)) := hims
         _ ≤ localizationIMSConstant/b^2*(C*m) := by gcongr
         _ = localizationIMSConstant*C*(m/b^2) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hma (mul_nonneg hI hC0)
  have hD : corePriceExcess Z lam ψ ≤ m^2/a :=
    (le_max_left _ _).trans ((le_div_iff₀ ha).mpr (localOffsetMass_offset (le_max_right _ _) hy))
  have hwork : Real.sqrt (freshOutMaximumSecondMoment (coreFirstRadialCut y hr0 hb)
      (coreFirstRadialCut_partition y hr0 hb) ψ Z lam)*Real.sqrt (rawCountMoment ψ y (32*a)) ≤
        F*C*(m^2/a) := by
    calc _ ≤ (F*(m/a))*(C*m) := mul_le_mul hrootF hroot (Real.sqrt_nonneg _) (by positivity)
         _ = _ := by ring
  calc _ ≤ corePriceExcess Z lam ψ+(1/2:ℝ)*weightedParticleCount ψ
        (spatialErrorWeight (coreFirstRadialCut y hr0 hb))+
        Real.sqrt (freshOutMaximumSecondMoment (coreFirstRadialCut y hr0 hb)
          (coreFirstRadialCut_partition y hr0 hb) ψ Z lam)*Real.sqrt (rawCountMoment ψ y (32*a)) := hcut
       _ ≤ m^2/a+localizationIMSConstant*C*(m^2/a)+F*C*(m^2/a) := add_le_add (add_le_add hD hims') hwork
       _ = _ := by dsimp [sharpFreshKineticConstant,C,F,m,D,a]; ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_LocalBallTraceBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

lemma ballIndicator_measurable (y : Space) (R : ℝ) :
    Measurable (fun z : Space => if ‖z-y‖ < R then (1:ℝ) else 0) :=
  measurable_const.ite ((isOpen_lt ((continuous_id.sub continuous_const).norm)
    continuous_const).measurableSet) measurable_const

lemma weightedParticleCount_ball {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) (R : ℝ) :
    weightedParticleCount ψ (fun z => if ‖z-y‖ < R then 1 else 0) =
      rawFormPair ψ (rawBallCount y R) := by
  have hB (z : Space) : ‖if ‖z-y‖ < R then (1:ℝ) else 0‖ ≤ 1 := by split_ifs <;> norm_num
  unfold weightedParticleCount rawFormPair rawBallCount
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [Finset.sum_mul]
  exact (integral_finsetSum _ (fun i _ =>
    weightedParticleCount_integrable hψ (ballIndicator_measurable y R) hB s i)).symm

lemma weightedParticleCount_le_ball {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    {w : Space → ℝ} (hw : Measurable w) {B : ℝ} (hB : ∀ z, ‖w z‖ ≤ B)
    (y : Space) (R : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hle : ∀ z, w z ≤ C*(if ‖z-y‖ < R then 1 else 0)) :
    weightedParticleCount ψ w ≤ C*Real.sqrt (rawCountMoment ψ y R)*Real.sqrt (formMass ψ) := by
  have hi (z : Space) : ‖C*(if ‖z-y‖ < R then (1:ℝ) else 0)‖ ≤ C := by
    split_ifs <;> simp [hC,Real.norm_of_nonneg hC]
  have hh := weightedParticleCount_mono
    (fun s i => weightedParticleCount_integrable hψ hw hB s i)
    (fun s i => weightedParticleCount_integrable hψ
      (measurable_const.mul (ballIndicator_measurable y R)) hi s i) hle
  change weightedParticleCount ψ w ≤ weightedParticleCount ψ (fun z => C * (if ‖z-y‖ < R then 1 else 0)) at hh
  rw [weightedParticleCount_const_mul,weightedParticleCount_ball hψ] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (rawBallFirst_le_sqrt_count hψ y R) hC).trans_eq (by ring))

lemma radialInside_sq_count {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b R : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hR : t+b ≤ R) :
    weightedParticleCount ψ (fun z => (radialInside y ht hb).value z^2) ≤
      Real.sqrt (rawCountMoment ψ y R)*Real.sqrt (formMass ψ) := by
  have hq (z : Space) : |(radialInside y ht hb).value z| ≤ 1 := Real.abs_cos_le_one _
  have hq2 (z : Space) : (radialInside y ht hb).value z^2 ≤ 1 := by
    nlinarith [hq z,abs_nonneg ((radialInside y ht hb).value z),sq_abs ((radialInside y ht hb).value z)]
  have hB (z : Space) : ‖(radialInside y ht hb).value z^2‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hq2 z
  have he (z : Space) : (radialInside y ht hb).value z^2 ≤ 1*(if ‖z-y‖ < R then 1 else 0) := by
    split_ifs with hz
    · simpa only [mul_one] using hq2 z
    · have hn : t+b ≤ ‖z-y‖ := hR.trans (le_of_not_gt hz)
      simp only [radialInside,radialPhase_pi_half ht hb hn,Real.cos_pi_div_two,zero_pow (by decide : 2 ≠ 0),mul_zero,le_refl]
  simpa only [one_mul, Pi.pow_apply] using weightedParticleCount_le_ball hψ
    (w := fun z => (radialInside y ht hb).value z^2)
    (by exact ((radialInside y ht hb).regular.continuous.pow 2).measurable) hB y R (by norm_num : (0:ℝ) ≤ 1) he

lemma radialInside_derivative_count {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b R : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hR : t+b < R) (a : Fin 3) :
    weightedParticleCount ψ (fun z => (lineDeriv ℝ (radialInside y ht hb).value z (spaceDirections a))^2) ≤
      (Real.pi*smoothTransitionBound/b)^2*Real.sqrt (rawCountMoment ψ y R)*Real.sqrt (formMass ψ) := by
  let q := radialInside y ht hb
  have hd (z : Space) : |lineDeriv ℝ q.value z (spaceDirections a)| ≤ Real.pi*smoothTransitionBound/b := by
    dsimp only [q,radialInside]
    rw [radial_cos_derivative,abs_mul,abs_neg]
    exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans
      (by simpa only [one_mul] using radialPhase_derivative_le y ht hb z a)
  have hC : 0 ≤ Real.pi*smoothTransitionBound/b := by have := smoothTransitionBound_pos; positivity
  have hd2 (z : Space) : (lineDeriv ℝ q.value z (spaceDirections a))^2 ≤ (Real.pi*smoothTransitionBound/b)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hd z) 2
  have hB (z : Space) : ‖(lineDeriv ℝ q.value z (spaceDirections a))^2‖ ≤ (Real.pi*smoothTransitionBound/b)^2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hd2 z
  apply weightedParticleCount_le_ball hψ ((q.derivative_continuous a).pow 2).measurable hB y R (sq_nonneg _)
  intro z
  simp only [Pi.pow_apply]
  split_ifs with hz
  · simpa only [mul_one] using hd2 z
  · have hoff : ¬ (t ≤ ‖z-y‖ ∧ ‖z-y‖ ≤ t+b) := fun hh => hz (lt_of_le_of_lt hh.2 hR)
    dsimp only [q,radialInside]
    rw [radial_cos_derivative,radialPhase_derivative_zero_off_collar ht hb hoff,mul_zero]
    norm_num

lemma radialInside_density_error {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b R : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hR : t+b < R) :
    densityLocalizationError ψ (radialInside y ht hb) ≤
      3*(Real.pi*smoothTransitionBound/b)^2*Real.sqrt (rawCountMoment ψ y R)*Real.sqrt (formMass ψ) := by
  have hh := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) =>
    radialInside_derivative_count hψ y ht hb hR a)
  simpa only [densityLocalizationError,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_assoc] using hh

open MeasureTheory Filter Set Metric
open scoped BigOperators

lemma radialInside_nonzero_lt {y z : Space} {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hz : (radialInside y ht hb).value z ≠ 0) : ‖z-y‖ < t+b := by
  by_contra hn
  apply hz
  change Real.cos (radialPhase y t b z) = 0
  rw [radialPhase_pi_half ht hb (le_of_not_gt hn),Real.cos_pi_div_two]

 theorem sharp_cell_ordinary_density {N : ℕ} {ψ : FormVector N}
    (hψ : FormAdmissible ψ) {y : Space} (hy : y ≠ 0)
    (ha1 : localCellRadius y ≤ 1) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    (∫ z in ball y (4*localCellRadius y), (ordinaryDensity ψ z)^(5/3:ℝ)) ≤
      sharpOrdinaryDensityConstant*(localOffsetMass (max (corePriceExcess Z lam ψ) 0) y)^2/localCellRadius y := by
  let a := localCellRadius y
  let m := localOffsetMass (max (corePriceExcess Z lam ψ) 0) y
  let C := actualCellMomentConstant
  have ha : 0 < a := localCellRadius_pos hy
  have hm1 : 1 ≤ m := localOffsetMass_one_le _ _
  have hm0 : 0 ≤ m := le_trans zero_le_one hm1
  have ham : 1 ≤ a*m := cell_mass_product ha hm1 (localOffsetMass_cube_le _ _)
  have hc : a ≤ a^2*m := by nlinarith [mul_le_mul_of_nonneg_left ham ha.le]
  have hm : formMass ψ = 1 := hψ.2.2.2.2.1
  have hsv := hψ.sobolevFermion.sobolevVector
  obtain ⟨hr,hT⟩ := sharp_cell_fresh_kinetic hψ.sobolevFermion hm hy ha le_rfl
    (show 5*a ∈ Icc (5*localCellRadius y) (6*localCellRadius y) by constructor <;> dsimp only [a] at * <;> linarith)
    hZ hlam hc
  let q := radialInside y (show 0 ≤ 4*a by positivity) ha
  have hq (z : Space) : |q.value z| ≤ 1 := Real.abs_cos_le_one _
  have hout (z : Space) (hz : q.value z ≠ 0) : z ∉ radialPatchCore y (5*a) := by
    have hh := radialInside_nonzero_lt (show 0 ≤ 4*a by positivity) ha hz
    change ¬ (5*a ≤ ‖z-y‖)
    linarith
  have hg := localGradientTrace_le_full_out hsv (coreFirstRadialCut y hr ha)
    (coreFirstRadialCut_partition y hr ha) q hq
    (fun z hz => coreFirstRadialCut_core_zero y hr ha z (hout z hz))
    (fun z hz i => coreFirstRadialCut_core_deriv_zero y hr ha z (hout z hz) i)
  have hg' : localGradientTrace ψ q ≤ 2*sharpFreshKineticConstant*(m^2/a) :=
    (hg.trans (mul_le_mul_of_nonneg_left hT (by norm_num))).trans_eq (by ring)
  have hcount := priced_enlarged_cell_count hψ.sobolevFermion hm hZ hlam hy
  have hroot : Real.sqrt (rawCountMoment ψ y (32*a)) ≤ C*m := by
    simpa using sqrt_count_scale (rawCountMoment_nonneg ψ y (32*a)) actualCellMomentConstant_one_le
      (by norm_num : (0:ℝ) ≤ 1) hm0 (by simpa using hcount)
  have hn := radialInside_sq_count hsv y (show 0 ≤ 4*a by positivity) ha
    (show 4*a+a ≤ 32*a by linarith)
  have he := radialInside_density_error hsv y (show 0 ≤ 4*a by positivity) ha
    (show 4*a+a < 32*a by linarith)
  rw [hm,Real.sqrt_one,mul_one] at hn he
  have hmle : m ≤ m^2/a := by
    apply (le_div_iff₀ ha).mpr
    nlinarith [mul_le_mul_of_nonneg_left ha1 hm0]
  have hma : m/a^2 ≤ m^2/a := by
    apply (div_le_div_iff₀ (sq_pos_of_pos ha) ha).mpr
    nlinarith [mul_le_mul_of_nonneg_left ham (mul_nonneg ha.le hm0)]
  have hC0 : 0 ≤ C := le_trans zero_le_one actualCellMomentConstant_one_le
  have hn' : weightedParticleCount ψ (fun z => q.value z^2) ≤ C*(m^2/a) :=
    hn.trans (hroot.trans (mul_le_mul_of_nonneg_left hmle hC0))
  have he' : densityLocalizationError ψ q ≤ 3*(Real.pi*smoothTransitionBound)^2*C*(m^2/a) := by
    calc _ ≤ 3*(Real.pi*smoothTransitionBound/a)^2*Real.sqrt (rawCountMoment ψ y (32*a)) := he
         _ ≤ 3*(Real.pi*smoothTransitionBound/a)^2*(C*m) := by gcongr
         _ = 3*(Real.pi*smoothTransitionBound)^2*C*(m/a^2) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hma (by positivity)
  have hb : localDensityBudget ψ q ≤ sharpOrdinaryDensityConstant*(m^2/a) := by
    unfold localDensityBudget
    have h1 := mul_le_mul_of_nonneg_left hn' (by norm_num : (0:ℝ) ≤ 32)
    have h2 := mul_le_mul_of_nonneg_left (add_le_add hg' he') (by norm_num : (0:ℝ) ≤ 4096/3)
    apply (add_le_add h1 h2).trans_eq
    dsimp only [sharpOrdinaryDensityConstant,C]
    ring
  have hloc := ordinaryDensity_local_lt ψ hψ q hq
  have hi0 : Integrable (fun z => (ordinaryDensity ψ z)^(5/3:ℝ)) := by
    have hh := (ordinaryDensity_memLp hψ).integrable_norm_rpow (by norm_num : (5/3:ENNReal) ≠ 0)
      (ENNReal.div_ne_top (by norm_num) (by norm_num) : (5/3:ENNReal) ≠ ⊤)
    simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat,Real.norm_of_nonneg (ordinaryDensity_nonneg ψ _)] using hh
  have hi : Integrable (fun z => (q.value z^2*ordinaryDensity ψ z)^(5/3:ℝ)) := by
    apply hi0.mono' ((((q.regular.continuous.pow 2).measurable.mul
      (ordinaryDensity_measurable ψ)).pow_const (5/3:ℝ)).aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      simp only [Pi.mul_apply,Pi.pow_apply]
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (mul_nonneg (sq_nonneg _) (ordinaryDensity_nonneg ψ z)) _)]
      apply Real.rpow_le_rpow (mul_nonneg (sq_nonneg _) (ordinaryDensity_nonneg ψ z)) _ (by norm_num)
      have hq2 : q.value z^2 ≤ 1 := by nlinarith [hq z,abs_nonneg (q.value z),sq_abs (q.value z)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hq2 (ordinaryDensity_nonneg ψ z))
  have heq : (∫ z in ball y (4*a), (ordinaryDensity ψ z)^(5/3:ℝ)) =
      ∫ z in ball y (4*a), (q.value z^2*ordinaryDensity ψ z)^(5/3:ℝ) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    have hz' : ‖z-y‖ ≤ 4*a := (by simpa only [mem_ball,dist_eq_norm] using hz : ‖z-y‖ < 4*a).le
    have hq1 : q.value z = 1 := by
      change Real.cos (radialPhase y (4*a) a z) = 1
      rw [radialPhase_zero (by positivity) ha hz',Real.cos_zero]
    dsimp only
    rw [hq1,one_pow,one_mul]
  rw [heq]
  apply (setIntegral_le_integral hi (ae_of_all _ (fun z => Real.rpow_nonneg
    (mul_nonneg (sq_nonneg _) (ordinaryDensity_nonneg ψ z)) _))).trans
  exact (hloc.trans hb).trans_eq (by ring)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpLocalPotentialBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SharpLocalPotential_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

lemma ordinaryDensity_power_integrable {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ) :
    Integrable (fun z => (ordinaryDensity ψ z)^(5/3:ℝ)) := by
  have hh := (ordinaryDensity_memLp hψ).integrable_norm_rpow (by norm_num : (5/3:ENNReal) ≠ 0)
    (ENNReal.div_ne_top (by norm_num) (by norm_num) : (5/3:ENNReal) ≠ ⊤)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat,Real.norm_of_nonneg (ordinaryDensity_nonneg ψ _)] using hh

lemma ordinaryDensity_power_ball_mono {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ)
    (y : Space) {q R : ℝ} (hqR : q ≤ R) :
    (∫ z in ball y q, (ordinaryDensity ψ z)^(5/3:ℝ)) ≤
      ∫ z in ball y R, (ordinaryDensity ψ z)^(5/3:ℝ) := by
  exact setIntegral_mono_set (ordinaryDensity_power_integrable hψ).integrableOn
    (ae_of_all _ (fun z => Real.rpow_nonneg (ordinaryDensity_nonneg ψ z) _))
    (ae_of_all _ (fun _ hz => ball_subset_ball hqR hz))

 theorem sharp_cell_local_potential_oai {N : ℕ} {ψ : FormVector N}
    (hψ : FormAdmissible ψ) {y : Space} (hy : y ≠ 0)
    (ha1 : localCellRadius y ≤ 1) {Z lam q : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hq : 0 < q) (hqR : q ≤ 4*localCellRadius y) :
    (∫ x, rawLocalPotential y q x ∂formRawLaw ψ) ≤
      (sharpOrdinaryDensityConstant*(localOffsetMass (max (corePriceExcess Z lam ψ) 0) y)^2/localCellRadius y)^(3/5:ℝ)*
        (8*Real.pi)^(2/5:ℝ)*q^(1/5:ℝ) := by
  apply (ordinaryDensity_raw_local_holder hψ.sobolevFermion.sobolevVector y hq
    ((ordinaryDensity_memLp hψ).restrict _)).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Real.rpow_le_rpow (setIntegral_nonneg measurableSet_ball
      (fun z _ => Real.rpow_nonneg (ordinaryDensity_nonneg ψ z) _))
    ((ordinaryDensity_power_ball_mono hψ y hqR).trans (sharp_cell_ordinary_density hψ hy ha1 hZ hlam))
    (by norm_num)

end Work_SharpLocalPotential_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators

open CoulombAnalysis CoulombNeumann

end CoulombAtom

end

end OAI
end

theorem solution : type_of% @OAI.CoulombAtom.sharp_cell_local_potential_oai := @OAI.CoulombAtom.sharp_cell_local_potential_oai
