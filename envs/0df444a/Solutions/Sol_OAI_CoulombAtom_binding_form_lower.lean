-- Prove2me | solution 1 for OAI.CoulombAtom.binding_form_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:40:33.744398+00:00
-- url     : https://prove2.me/submissions/81b0b9d1-b335-45ae-bcb9-ab06e86dfd47

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C008

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_WeakDerivative
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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
namespace CoulombAtom
section WeakDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]

variable [IsLocallyFiniteMeasure (volume : Measure E)]

lemma IsWeakDerivative.unique {v : E} {f g g' : E → ℂ}
    (h : IsWeakDerivative v f g) (h' : IsWeakDerivative v f g')
    (hg : MemLp g 2) (hg' : MemLp g' 2) : g =ᵐ[volume] g' := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (hg.locallyIntegrable (by norm_num)) (hg'.locallyIntegrable (by norm_num))
  intro φ hφ hcφ
  have hh := neg_injective ((h φ hφ hcφ).symm.trans (h' φ hφ hcφ))
  simpa only [Complex.real_smul, mul_comm] using hh

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma weakGraphValue_injective (v : ι → E) : Function.Injective (weakGraphValue v) := by
  intro F G hFG
  apply Subtype.ext
  apply PiLp.ext
  intro j
  cases j with
  | none => exact hFG
  | some i =>
    have hF := (mem_weakGraph v F).mp F.property i
    have hG := (mem_weakGraph v G).mp G.property i
    have hv : (F.val none : E → ℂ) =ᵐ[volume] (G.val none : E → ℂ) := by
      change F.val none = G.val none at hFG
      rw [hFG]
    have hF' := hF.congr_ae hv (EventuallyEq.refl _ _)
    exact Lp.ext (hF'.unique hG (Lp.memLp _) (Lp.memLp _))

end WeakDerivative

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_IteratedReduction
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
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
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution


open Filter
open scoped Topology InnerProductSpace

open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace

lemma complex_ims_identity (p d : ℝ) (a b : ℂ) :
    ‖(p : ℂ) * a + (d : ℂ) * b‖ ^ 2 -
      (⟪(p : ℂ) * ((p : ℂ) * a + (d : ℂ) * b) +
        (d : ℂ) * ((p : ℂ) * b), a⟫_ℂ).re = d ^ 2 * ‖b‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, RCLike.inner_apply,
    map_add, map_mul, Complex.conj_ofReal, Complex.conj_re, Complex.conj_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

end CoulombAtom

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

lemma l2_inner_re (f g : Lp ℂ 2 μ) :
    (⟪f, g⟫_ℂ).re = ∫ x, (⟪f x, g x⟫_ℂ).re ∂μ := by
  rw [L2.inner_def]
  exact (integral_re (L2.integrable_inner (𝕜 := ℂ) f g)).symm

lemma l2_ims_identity (p d : α → ℝ) (a b v w : Lp ℂ 2 μ)
    (hv : (v : α → ℂ) =ᵐ[μ] fun x => (p x : ℂ) * a x + (d x : ℂ) * b x)
    (hw : (w : α → ℂ) =ᵐ[μ] fun x => (p x : ℂ) * v x +
      (d x : ℂ) * ((p x : ℂ) * b x)) :
    ‖v‖ ^ 2 - (⟪w, a⟫_ℂ).re = ∫ x, (d x) ^ 2 * ‖b x‖ ^ 2 ∂μ := by
  rw [l2_norm_sq, l2_inner_re]
  have hi : Integrable (fun x => ‖v x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp v).aestronglyMeasurable).mp (Lp.memLp v)
  have hj : Integrable (fun x => (⟪w x, a x⟫_ℂ).re) μ :=
    (L2.integrable_inner (𝕜 := ℂ) w a).re
  rw [← integral_sub hi hj]
  apply integral_congr_ae
  filter_upwards [hv, hw] with x hx hy
  rw [hy, hx]
  exact complex_ims_identity (p x) (d x) (a x) (b x)

end CoulombAtom

open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Multiplier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom
section Multiplier
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma SmoothMultiplier.apply_gradient {v : ι → E} (p : SmoothMultiplier v)
    (F : weakGraph v) (i : ι) :
    ((p.apply F).val (some i) : E → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * F.val (some i) x +
        Complex.ofReal (lineDeriv ℝ p.value x (v i)) * F.val none x :=
  (p.gradient_memLp F i).coeFn_toLp

end Multiplier

lemma FermionMultiplier.apply_value {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) :
    (graphComponent s none (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphComponent s none F x :=
  p.toSmoothMultiplier.apply_value (F.val s)

lemma graphNuclear_ae {N : ℕ} (s : Spins N) (i : Fin N) (F : fermionGraph N) :
    (graphNuclear s i F : Configuration N → ℂ) =ᵐ[volume]
      fun x => graphComponent s none F x / (Real.sqrt ‖x i‖ : ℂ) := by
  exact (rootCoulombFn_memLp (sectorDirections N) (ContinuousLinearMap.proj i)
    (fun a => (i, a)) (by intro a; simp [sectorDirections, direction]) (F.val s)).coeFn_toLp

lemma graphPair_ae {N : ℕ} (s : Spins N) (i j : Fin N) (hij : i ≠ j)
    (F : fermionGraph N) :
    (graphPair s i j hij F : Configuration N → ℂ) =ᵐ[volume]
      fun x => graphComponent s none F x / (Real.sqrt ‖x i - x j‖ : ℂ) := by
  exact (rootCoulombFn_memLp (sectorDirections N) (electronProjection i - electronProjection j)
    (fun a => (i, a)) (by
      intro a
      change direction i a i - direction i a j = EuclideanSpace.single a 1
      simp [direction, Ne.symm hij]) (F.val s)).coeFn_toLp

attribute [local irreducible] graphNuclear graphPair graphComponent FermionMultiplier.apply

lemma FermionMultiplier.apply_nuclear {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) :
    (graphNuclear s i (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphNuclear s i F x := by
  filter_upwards [graphNuclear_ae s i (p.apply F), graphNuclear_ae s i F,
    p.apply_value F s] with x hx hy hz
  exact hx.trans ((congrArg (fun z : ℂ => z / _) hz).trans
    ((mul_div_assoc (p.value x : ℂ) _ _).trans (congrArg (fun z : ℂ => (p.value x : ℂ) * z) hy.symm)))

lemma FermionMultiplier.apply_pair {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i j : Fin N) (hij : i ≠ j) :
    (graphPair s i j hij (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphPair s i j hij F x := by
  filter_upwards [graphPair_ae s i j hij (p.apply F), graphPair_ae s i j hij F,
    p.apply_value F s] with x hx hy hz
  exact hx.trans ((congrArg (fun z : ℂ => z / _) hz).trans
    ((mul_div_assoc (p.value x : ℂ) _ _).trans (congrArg (fun z : ℂ => (p.value x : ℂ) * z) hy.symm)))

lemma coulombFormOperator_pairing (Z : ℝ) (N : ℕ) (F G : fermionGraph N) :
    (⟪G, coulombFormOperator Z N F⟫_ℂ).re =
      (1 / 2 : ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        (⟪graphComponent s (some (i, a)) G, graphComponent s (some (i, a)) F⟫_ℂ).re) -
      Z * (∑ s : Spins N, ∑ i : Fin N,
        (⟪graphNuclear s i G, graphNuclear s i F⟫_ℂ).re) +
      (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
        if hij : i < j then (⟪graphPair s i j (ne_of_lt hij) G,
          graphPair s i j (ne_of_lt hij) F⟫_ℂ).re else 0) := by
  have ht : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  unfold coulombFormOperator
  simp only [ht, add_apply, sub_apply, smul_apply, sum_apply, inner_add_right, inner_sub_right,
    inner_smul_right, inner_sum, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [ContinuousLinearMap.adjoint_inner_right]

attribute [local irreducible] fermionGraphValue coulombFormOperator

attribute [local irreducible] formEnergy graphFormVector

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_ActualMasterCenterComparison
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

lemma graphFormVector_sobolev {N : ℕ} (F : fermionGraph N) :
    SobolevFermion (graphFormVector F) := by
  refine ⟨fun s => Lp.memLp _, fun s i a => Lp.memLp _, ?_, ?_⟩
  · intro s i a
    exact (mem_weakGraph _ _).mp (F.val s).property (i,a)
  · intro π s
    exact (mem_fermionSpace_ae _).mp (fermionGraphValue N F).property π s

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BindingBase
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

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

lemma linear_hardy_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    (P : E →L[ℝ] Space) (v : Fin 3 → E)
    (hPv : ∀ a, P (v a) = EuclideanSpace.single a 1)
    {f : E → ℂ} {g : Fin 3 → E → ℂ} (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (v a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    Integrable (fun x => ‖f x‖ ^ 2 / (4 * ‖P x‖ ^ 2)) ∧
      (∫ x, ‖f x‖ ^ 2 / (4 * ‖P x‖ ^ 2)) ≤ ∑ a, ∫ x, ‖g a x‖ ^ 2 := by
  obtain ⟨hi,hb⟩ := linear_hardy_integrable_bound P v hPv hf hg hweak
  have he : (fun x => ‖f x‖^2/(4*‖P x‖^2)) =
      fun x => (1/4:ℝ)*(‖f x‖^2/‖P x‖^2) := by funext x; ring
  rw [he]
  refine ⟨hi.const_mul _,?_⟩
  rw [integral_const_mul]
  linarith

open MeasureTheory Filter
open scoped Topology BigOperators

section

lemma SobolevFermion.quantumEnergyDensity_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (Z : ℝ) (s : Spins N) :
    Integrable (quantumEnergyDensity Z ψ s) := by
  classical
  have hn (i : Fin N) := nuclear_integrable i (hψ.1 s) (hψ.2.1 s i) (hψ.2.2.1 s i)
  have hp (i j : Fin N) (hij : i ≠ j) := pair_integrable i j hij (hψ.1 s)
    (hψ.2.1 s i) (hψ.2.2.1 s i)
  apply Integrable.add
  · exact ((integrable_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun a _ => (hψ.2.1 s i a).norm.integrable_sq))).const_mul _).sub
      ((integrable_finsetSum _ (fun i _ => hn i)).const_mul _)
  · apply Integrable.const_mul
    apply integrable_finsetSum; intro i _
    apply integrable_finsetSum; intro j _
    split_ifs with hij
    · exact hp i j hij
    · exact integrable_zero _ _ _

lemma SobolevFermion.quantumCoreDensity_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (Z : ℝ) (i : Fin N) (s : Spins N) :
    Integrable (quantumCoreDensity Z ψ i s) := by
  classical
  have hk : Integrable (fun x => ∑ j, if j ≠ i then ∑ a, ‖ψ.gradient s j a x‖ ^ 2 else 0) := by
    apply integrable_finsetSum; intro j _
    split_ifs
    · exact integrable_finsetSum _ (fun a _ => (hψ.2.1 s j a).norm.integrable_sq)
    · exact integrable_zero _ _ _
  have hn : Integrable (fun x => ∑ j, if j ≠ i then ‖ψ.value s x‖ ^ 2 / ‖x j‖ else 0) := by
    apply integrable_finsetSum; intro j _
    split_ifs
    · exact nuclear_integrable j (hψ.1 s) (hψ.2.1 s j) (hψ.2.2.1 s j)
    · exact integrable_zero _ _ _
  have hp : Integrable (fun x => ∑ j, ∑ k,
      if j ≠ i ∧ k ≠ i ∧ j ≠ k then ‖ψ.value s x‖ ^ 2 / ‖x j-x k‖ else 0) := by
    apply integrable_finsetSum; intro j _
    apply integrable_finsetSum; intro k _
    split_ifs with hij
    · exact pair_integrable j k hij.2.2 (hψ.1 s) (hψ.2.1 s j) (hψ.2.2.1 s j)
    · exact integrable_zero _ _ _
  exact ((hk.const_mul _).sub (hn.const_mul _)).add (hp.const_mul _)

lemma graphFormVector_value_eq {N : ℕ} (F : fermionGraph N) (s : Spins N) (x : Configuration N) :
    (graphFormVector F).value s x = graphComponent s none F x := rfl

lemma graphFormVector_gradient_eq {N : ℕ} (F : fermionGraph N) (s : Spins N)
    (i : Fin N) (a : Fin 3) (x : Configuration N) :
    (graphFormVector F).gradient s i a x = graphComponent s (some (i,a)) F x := rfl

attribute [local irreducible] graphComponent graphFormVector

end

lemma sum_excluding_add {α : Type*} [Fintype α] [DecidableEq α] (i : α) (f : α → ℝ) :
    (∑ j, if j ≠ i then f j else 0) + f i = ∑ j, f j := by
  have hh (j : α) : (if j ≠ i then f j else 0) + (if j = i then f j else 0) = f j := by
    by_cases h : j = i <;> simp [h]
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
    Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => hh j)

lemma pairs_excluding_add {α : Type*} [Fintype α] [DecidableEq α] (i : α)
    (f : α → α → ℝ) (hs : ∀ j k, f j k = f k j) (hii : f i i = 0) :
    (∑ j, ∑ k, if j ≠ i ∧ k ≠ i then f j k else 0) + 2 * (∑ k, f i k) =
      ∑ j, ∑ k, f j k := by
  have hinner (j : α) : (∑ k, if k ≠ i then f j k else 0) + f j i = ∑ k, f j k :=
    sum_excluding_add i (f j)
  have houter := sum_excluding_add i (fun j => ∑ k, if k ≠ i then f j k else 0)
  have hr := sum_excluding_add i (f i)
  rw [hii, add_zero] at hr
  have hc : (∑ j, f j i) = ∑ j, f i j := Finset.sum_congr rfl (fun j _ => hs j i)
  have hd : (∑ j, if j ≠ i then ∑ k, if k ≠ i then f j k else 0 else 0) =
      ∑ j, ∑ k, if j ≠ i ∧ k ≠ i then f j k else 0 := by
    apply Finset.sum_congr rfl; intro j _
    by_cases h : j = i <;> simp [h]
  rw [hd, hr] at houter
  have he := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => hinner j)
  rw [Finset.sum_add_distrib, hc] at he
  linarith

lemma quantumEnergyDensity_delete {N : ℕ} (Z : ℝ) (ψ : FormVector N)
    (i : Fin N) (s : Spins N) (x : Configuration N) :
    quantumEnergyDensity Z ψ s x = quantumCoreDensity Z ψ i s x +
      (1/2:ℝ) * (∑ a, ‖ψ.gradient s i a x‖ ^ 2) - Z * (‖ψ.value s x‖ ^ 2 / ‖x i‖) +
      (∑ j, if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0) := by
  classical
  have hk := sum_excluding_add i (fun j => ∑ a, ‖ψ.gradient s j a x‖ ^ 2)
  have hn := sum_excluding_add i (fun j => ‖ψ.value s x‖ ^ 2 / ‖x j‖)
  let f := fun j k : Fin N => if j ≠ k then ‖ψ.value s x‖ ^ 2 / ‖x j-x k‖ else 0
  have hs (j k : Fin N) : f j k = f k j := by
    dsimp [f]
    by_cases h : j = k
    · simp [h]
    · simp [h, Ne.symm h, norm_sub_rev]
  have hp := pairs_excluding_add i f hs (by simp [f])
  have he (j k : Fin N) : (if j ≠ i ∧ k ≠ i then f j k else 0) =
      if j ≠ i ∧ k ≠ i ∧ j ≠ k then ‖ψ.value s x‖ ^ 2 / ‖x j-x k‖ else 0 := by
    simp only [f]; split_ifs <;> simp_all
  simp only [he] at hp
  unfold quantumEnergyDensity quantumCoreDensity
  change _ = _
  dsimp only [f] at hp
  rw [← hk, ← hn, ← hp]
  ring


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Weighted
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
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
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
open scoped Topology BigOperators InnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

lemma SmoothMultiplier.weighted_kinetic_nonneg (P : E →L[ℝ] Space) (v : Fin 3 → E)
    (hPv : ∀ a, P (v a) = EuclideanSpace.single a 1) (p : SmoothMultiplier v)
    (hp : ∀ x, (∑ a : Fin 3, (lineDeriv ℝ p.value x (v a)) ^ 2) ≤
      (p.value x) ^ 2 / (4 * ‖P x‖ ^ 2)) (F : weakGraph v) :
    0 ≤ ∑ a : Fin 3, (⟪(p.apply (p.apply F)).val (some a), F.val (some a)⟫_ℂ).re := by
  have hh := linear_hardy_bound P v hPv (Lp.memLp ((p.apply F).val none))
    (fun a => Lp.memLp ((p.apply F).val (some a)))
    ((mem_weakGraph v (p.apply F).val).mp (p.apply F).property)
  have hi (a : Fin 3) : Integrable (fun x =>
      (lineDeriv ℝ p.value x (v a)) ^ 2 * ‖F.val none x‖ ^ 2) := by
    obtain ⟨C,hC⟩ := p.gradient_bound a
    apply (Lp.memLp (F.val none)).norm.integrable_sq.bdd_mul (c := C ^ 2)
      ((p.derivative_continuous a).pow 2).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change ‖lineDeriv ℝ p.value x (v a) ^ 2‖ ≤ C ^ 2
      rw [norm_pow, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC x) 2
  have hims (a : Fin 3) : ‖(p.apply F).val (some a)‖ ^ 2 -
      (⟪(p.apply (p.apply F)).val (some a), F.val (some a)⟫_ℂ).re =
        ∫ x, (lineDeriv ℝ p.value x (v a)) ^ 2 * ‖F.val none x‖ ^ 2 := by
    apply l2_ims_identity p.value (fun x => lineDeriv ℝ p.value x (v a))
      (F.val (some a)) (F.val none) ((p.apply F).val (some a))
      ((p.apply (p.apply F)).val (some a)) (p.apply_gradient F a)
    filter_upwards [p.apply_gradient (p.apply F) a, p.apply_value F] with x hx hy
    rw [hx, hy]
  have hl : (∑ a : Fin 3, ∫ x, (lineDeriv ℝ p.value x (v a)) ^ 2 * ‖F.val none x‖ ^ 2) ≤
      ∫ x, ‖(p.apply F).val none x‖ ^ 2 / (4 * ‖P x‖ ^ 2) := by
    rw [← integral_finsetSum _ fun a _ => hi a]
    apply integral_mono_ae (integrable_finsetSum _ fun a _ => hi a) hh.1
    filter_upwards [p.apply_value F] with x hx
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      ← Finset.sum_mul]
    have h := mul_le_mul_of_nonneg_right (hp x) (sq_nonneg ‖F.val none x‖)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hsum := hl.trans hh.2
  simp_rw [← hims, ← l2_norm_sq] at hsum
  rw [Finset.sum_sub_distrib] at hsum
  linarith

end

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

lemma bindingRoot_hardy_control {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (x : Space) :
    (∑ a : Fin 3, (fderiv ℝ (bindingRoot R ε) x (EuclideanSpace.single a 1)) ^ 2) ≤
      bindingRoot R ε x ^ 2 / (4 * ‖x‖ ^ 2) := by
  simp only [bindingRoot_derivative hR hε, div_pow, mul_pow,
    ← Finset.sum_div, ← Finset.mul_sum, sum_coordinate_sq]
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let t := regularizedRadius ε x
  have ht : 0 < t := regularizedRadius_pos hε x
  have hnt : ‖x‖ ≤ t := norm_le_regularizedRadius ε x
  change bindingRoot R ε x ^ 2 * R^2 * ‖x‖^2 /
    (2^2 * (t^2)^2 * (R+t)^2) ≤ _
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hfour : ‖x‖^4 ≤ t^4 := pow_le_pow_left₀ (norm_nonneg _) hnt 4
  have hRs : R^2 ≤ (R+t)^2 := by nlinarith
  have hm := mul_le_mul hfour hRs (sq_nonneg R) (pow_nonneg ht.le 4)
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 4 * bindingRoot R ε x ^ 2 by positivity)
  nlinarith [sq_nonneg (bindingRoot R ε x)]


open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_Restriction
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
open scoped Topology BigOperators ContDiff
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
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
namespace CoulombAtom
section Restriction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] [Fintype κ] in
lemma SmoothMultiplier.restrict_apply {v : ι → E} (p : SmoothMultiplier v)
    (j : κ → ι) (F : weakGraph v) :
    (p.restrict j).apply (restrictWeakGraph v j F) = restrictWeakGraph v j (p.apply F) := by
  apply weakGraphValue_injective (v ∘ j)
  apply Lp.ext
  exact (p.restrict j).apply_value (restrictWeakGraph v j F) |>.trans (p.apply_value F).symm

omit [Fintype ι] in
lemma SmoothMultiplier.projected_kinetic_nonneg {v : ι → E}
    (P : E →L[ℝ] Space) (j : Fin 3 → ι)
    (hP : ∀ a, P (v (j a)) = EuclideanSpace.single a 1) (p : SmoothMultiplier v)
    (hp : ∀ x, (∑ a : Fin 3, (lineDeriv ℝ p.value x (v (j a))) ^ 2) ≤
      p.value x ^ 2 / (4 * ‖P x‖ ^ 2)) (F : weakGraph v) :
    0 ≤ ∑ a : Fin 3, (⟪(p.apply (p.apply F)).val (some (j a)), F.val (some (j a))⟫_ℂ).re := by
  have hh := (p.restrict j).weighted_kinetic_nonneg P (v ∘ j) hP hp
    (restrictWeakGraph v j F)
  rw [p.restrict_apply, p.restrict_apply] at hh
  exact hh

end Restriction

lemma bindingMultiplier_kinetic_nonneg {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (i : Fin N) (F : weakGraph (sectorDirections N)) :
    0 ≤ ∑ a : Fin 3, (⟪((bindingMultiplier hR hε i).apply
      ((bindingMultiplier hR hε i).apply F)).val (some (i,a)), F.val (some (i,a))⟫_ℂ).re := by
  apply (bindingMultiplier hR hε i).projected_kinetic_nonneg (electronProjection i)
    (fun a => (i,a))
  · intro a
    simp [sectorDirections, direction, electronProjection]
  · intro x
    simpa [bindingMultiplier, sectorDirections, lineDeriv_binding_coordinate hR hε,
      electronProjection] using bindingRoot_hardy_control hR hε (x i)

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Sum
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
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
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
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

lemma bindingTotalMultiplier_value {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (x : Configuration N) : (bindingTotalMultiplier hR hε).value x =
      ∑ i, bindingWeight R ε (x i) := by
  change (∑ i, bindingRoot R ε (x i) ^ 2) = _
  simp only [bindingRoot_sq hR hε]


open MeasureTheory Filter
open scoped Topology BigOperators

lemma l2_coe_finset_sum {X α : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Finset α) (f : α → Lp ℂ 2 μ) :
    ((∑ i ∈ s, f i : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    exact hx
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x hx hy
    simp only [Pi.add_apply] at hx
    rw [hx, hy]

section Sum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]
variable {ι α : Type*} [Fintype ι] [Fintype α] {v : ι → E}

omit [Fintype ι] in
lemma SmoothMultiplier.sumSquares_apply (p : α → SmoothMultiplier v) (F : weakGraph v) :
    (SmoothMultiplier.sumSquares p).apply F = ∑ i, (p i).apply ((p i).apply F) := by
  apply weakGraphValue_injective v
  rw [map_sum]
  apply Lp.ext
  have ha : ∀ᵐ x : E, ∀ i : α,
      ((p i).apply ((p i).apply F)).val none x =
        ((p i).value x : ℂ) * ((p i).value x : ℂ) * F.val none x := by
    apply ae_all_iff.mpr; intro i
    filter_upwards [(p i).apply_value ((p i).apply F), (p i).apply_value F] with x hx hy
    rw [hx, hy, mul_assoc]
  filter_upwards [(SmoothMultiplier.sumSquares p).apply_value F, ha,
    l2_coe_finset_sum volume Finset.univ
      (fun i => weakGraphValue v ((p i).apply ((p i).apply F)))] with x hx hy hz
  change ((SmoothMultiplier.sumSquares p).apply F).val none x = _
  rw [hx, hz]
  change (((∑ i, (p i).value x ^ 2 : ℝ) : ℂ) * F.val none x) = _
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  change ((p i).value x : ℂ) ^ 2 * F.val none x =
    ((p i).apply ((p i).apply F)).val none x
  rw [hy i, pow_two]

omit [Fintype ι] in
lemma weakGraph_sum_component (G : α → weakGraph v) (k : Option ι) :
    (∑ i, G i).val k = ∑ i, (G i).val k := by
  rw [Submodule.coe_sum, WithLp.ofLp_sum, Finset.sum_apply]

end Sum

lemma bindingTotalMultiplier_component {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : fermionGraph N) (s : Spins N) (k : Option (Fin N × Fin 3)) :
    graphComponent s k ((bindingTotalMultiplier hR hε).apply F) =
      ∑ i, ((bindingMultiplier hR hε i).apply ((bindingMultiplier hR hε i).apply (F.val s))).val k := by
  change ((SmoothMultiplier.sumSquares (bindingMultiplier hR hε)).apply (F.val s)).val k = _
  rw [SmoothMultiplier.sumSquares_apply, weakGraph_sum_component]


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ComplexRealWeightPairing
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
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
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
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
section

lemma complex_real_weight_pairing (w : ℝ) (a : ℂ) :
    (⟪(w : ℂ) * a, a⟫_ℂ).re = w * ‖a‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, RCLike.inner_apply,
    map_mul, Complex.conj_ofReal, Complex.conj_re, Complex.conj_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma l2_real_weight_pairing {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (w : X → ℝ) (f g : Lp ℂ 2 μ)
    (hg : (g : X → ℂ) =ᵐ[μ] fun x => (w x : ℂ) * f x) :
    (⟪g, f⟫_ℂ).re = ∫ x, w x * ‖f x‖ ^ 2 ∂μ := by
  rw [l2_inner_re]
  apply integral_congr_ae
  filter_upwards [hg] with x hx
  rw [hx, complex_real_weight_pairing]

lemma norm_div_sqrt_real_sq (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ‖a / (Real.sqrt r : ℂ)‖ ^ 2 = ‖a‖ ^ 2 / r := by
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hr]

attribute [local irreducible] graphNuclear graphPair graphComponent FermionMultiplier.apply

lemma FermionMultiplier.nuclear_weighted_pairing {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) :
    (⟪graphNuclear s i (p.apply F), graphNuclear s i F⟫_ℂ).re =
      ∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i‖) := by
  rw [l2_real_weight_pairing p.value _ _ (p.apply_nuclear F s i)]
  apply integral_congr_ae
  filter_upwards [graphNuclear_ae s i F] with x hx
  rw [hx, norm_div_sqrt_real_sq _ (norm_nonneg _)]

lemma FermionMultiplier.pair_weighted_pairing {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i j : Fin N) (hij : i ≠ j) :
    (⟪graphPair s i j hij (p.apply F), graphPair s i j hij F⟫_ℂ).re =
      ∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i-x j‖) := by
  rw [l2_real_weight_pairing p.value _ _ (p.apply_pair F s i j hij)]
  apply integral_congr_ae
  filter_upwards [graphPair_ae s i j hij F] with x hx
  rw [hx, norm_div_sqrt_real_sq _ (norm_nonneg _)]

lemma binding_pairing_off {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : weakGraph (sectorDirections N)) (i j : Fin N) (hij : i ≠ j) (a : Fin 3) :
    (⟪((bindingMultiplier hR hε i).apply ((bindingMultiplier hR hε i).apply F)).val
      (some (j,a)), F.val (some (j,a))⟫_ℂ).re =
      ∫ x, bindingWeight R ε (x i) * ‖F.val (some (j,a)) x‖ ^ 2 := by
  apply l2_real_weight_pairing
  have hd (x : Configuration N) : lineDeriv ℝ (bindingMultiplier hR hε i).value x
      (sectorDirections N (j,a)) = 0 := by
    simp only [bindingMultiplier, sectorDirections, lineDeriv_binding_coordinate hR hε,
      ite_eq_right (Ne.symm hij)]
  filter_upwards [(bindingMultiplier hR hε i).apply_gradient
    ((bindingMultiplier hR hε i).apply F) (j,a),
    (bindingMultiplier hR hε i).apply_gradient F (j,a)] with x hx hy
  rw [hd, Complex.ofReal_zero, zero_mul, add_zero] at hx hy
  rw [hx, hy]
  change (bindingRoot R ε (x i) : ℂ) * ((bindingRoot R ε (x i) : ℂ) * _) = _
  rw [← mul_assoc, ← pow_two, ← Complex.ofReal_pow, bindingRoot_sq hR hε]

end

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

lemma weighted_integrable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] {μ : Measure X} {f : X → ℝ} (hf : Integrable f μ)
    {w : X → ℝ} (hw : Continuous w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    Integrable (fun x => w x * f x) μ :=
  hf.bdd_mul hw.aestronglyMeasurable (Eventually.of_forall hC)

lemma integral_weighted_quantumDensity {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (Z : ℝ) (s : Spins N)
    (w : Configuration N → ℝ) (hw : Continuous w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    (∫ x, w x * quantumEnergyDensity Z ψ s x) =
      (1/2:ℝ) * (∑ i, ∑ a, ∫ x, w x * ‖ψ.gradient s i a x‖ ^ 2) -
      Z * (∑ i, ∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x i‖)) +
      (1/2:ℝ) * (∑ i, ∑ j, ∫ x, w x *
        (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) := by
  classical
  have hk (i : Fin N) (a : Fin 3) := weighted_integrable (hψ.2.1 s i a).norm.integrable_sq hw hC
  have hn (i : Fin N) := weighted_integrable
    (nuclear_integrable i (hψ.1 s) (hψ.2.1 s i) (hψ.2.2.1 s i)) hw hC
  have hp (i j : Fin N) : Integrable (fun x => w x *
      (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) := by
    split_ifs with hij
    · exact weighted_integrable (pair_integrable i j hij (hψ.1 s)
        (hψ.2.1 s i) (hψ.2.2.1 s i)) hw hC
    · simp only [mul_zero]; exact integrable_zero _ _ _
  have hks := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun a _ => hk i a))
  have hns := integrable_finsetSum Finset.univ (fun i _ => hn i)
  have hps := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hp i j))
  have hleft : (∫ x, w x * quantumEnergyDensity Z ψ s x) =
      ∫ x, (1/2:ℝ) * (∑ i, ∑ a, w x * ‖ψ.gradient s i a x‖ ^ 2) -
        Z * (∑ i, w x * (‖ψ.value s x‖ ^ 2 / ‖x i‖)) +
        (1/2:ℝ) * (∑ i, ∑ j, w x *
          (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [quantumEnergyDensity, mul_add, mul_sub, mul_left_comm (w x) (1/2:ℝ),
        mul_left_comm (w x) Z, Finset.mul_sum]
  have ha := integral_add ((hks.const_mul (1/2:ℝ)).sub (hns.const_mul Z))
    (hps.const_mul (1/2:ℝ))
  have hb := integral_sub (hks.const_mul (1/2:ℝ)) (hns.const_mul Z)
  simp only [Pi.sub_apply] at ha hb
  rw [hleft, ha, hb]
  simp only [integral_const_mul]
  simp_rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hk i a)),
    integral_finsetSum _ (fun a _ => hk _ a), integral_finsetSum _ (fun i _ => hn i),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hp i j)),
    integral_finsetSum _ (fun j _ => hp _ j)]


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BindingWeightContinuous
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
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
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
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

lemma bindingWeight_continuous {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    Continuous (bindingWeight R ε) := by
  have he : bindingWeight R ε = fun x => bindingRoot R ε x ^ 2 := by
    funext x; exact (bindingRoot_sq hR hε x).symm
  rw [he]
  exact (bindingRoot_smooth hR hε).continuous.pow 2

lemma bindingWeight_integrable {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (i : Fin N) {f : Configuration N → ℝ} (hf : Integrable f) :
    Integrable (fun x => bindingWeight R ε (x i) * f x) := by
  apply weighted_integrable hf ((bindingWeight_continuous hR hε).comp (continuous_apply i))
  intro x
  change ‖bindingWeight R ε (x i)‖ ≤ R
  rw [Real.norm_of_nonneg (bindingWeight_pos hR hε (x i)).le]
  exact bindingWeight_le hR hε (x i)

lemma bindingTotal_integral {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    {f : Configuration N → ℝ} (hf : Integrable f) :
    (∫ x, (bindingTotalMultiplier hR hε).value x * f x) =
      ∑ i, ∫ x, bindingWeight R ε (x i) * f x := by
  simp only [bindingTotalMultiplier_value hR hε, Finset.sum_mul]
  exact integral_finsetSum _ (fun i _ => bindingWeight_integrable hR hε i hf)

lemma bindingKinetic_lower {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : weakGraph (sectorDirections N)) (i : Fin N) :
    (∑ j, ∑ a, ∫ x, bindingWeight R ε (x i) * ‖F.val (some (j,a)) x‖ ^ 2) -
      (∑ a, ∫ x, bindingWeight R ε (x i) * ‖F.val (some (i,a)) x‖ ^ 2) ≤
    ∑ j, ∑ a, (⟪((bindingMultiplier hR hε i).apply
      ((bindingMultiplier hR hε i).apply F)).val (some (j,a)), F.val (some (j,a))⟫_ℂ).re := by
  classical
  let A (j : Fin N) := ∑ a, ∫ x,
    bindingWeight R ε (x i) * ‖F.val (some (j,a)) x‖ ^ 2
  let B (j : Fin N) := ∑ a, (⟪((bindingMultiplier hR hε i).apply
    ((bindingMultiplier hR hε i).apply F)).val (some (j,a)), F.val (some (j,a))⟫_ℂ).re
  have hoff (j : Fin N) (hji : j ≠ i) : B j = A j := by
    apply Finset.sum_congr rfl; intro a _
    exact binding_pairing_off hR hε F i j hji.symm a
  have he : (∑ j, if j ≠ i then B j else 0) = ∑ j, if j ≠ i then A j else 0 := by
    apply Finset.sum_congr rfl; intro j _
    split_ifs with hji
    · exact hoff j hji
    · rfl
  have ha := sum_excluding_add i A
  have hb := sum_excluding_add i B
  have hp : 0 ≤ B i := bindingMultiplier_kinetic_nonneg hR hε i F
  change (∑ j, A j) - A i ≤ ∑ j, B j
  rw [he] at hb
  linarith


open MeasureTheory Filter
open scoped Topology BigOperators


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace


open MeasureTheory Filter
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BindingPairApproxIntegral
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
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
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
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

section

lemma integral_weighted_deletedDensity {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (Z : ℝ) (s : Spins N) (i : Fin N)
    (w : Configuration N → ℝ) (hw : Continuous w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    (∫ x, w x * quantumEnergyDensity Z ψ s x) =
      (∫ x, w x * quantumCoreDensity Z ψ i s x) +
      (1/2:ℝ) * (∑ a : Fin 3, ∫ x, w x * ‖ψ.gradient s i a x‖ ^ 2) -
      Z * (∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x i‖)) +
      (∑ j : Fin N, ∫ x, w x * (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) := by
  classical
  have hc := weighted_integrable (hψ.quantumCoreDensity_integrable Z i s) hw hC
  have hk (a : Fin 3) := weighted_integrable (hψ.2.1 s i a).norm.integrable_sq hw hC
  have hn := weighted_integrable
    (nuclear_integrable i (hψ.1 s) (hψ.2.1 s i) (hψ.2.2.1 s i)) hw hC
  have hp (j : Fin N) : Integrable (fun x => w x *
      (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) := by
    split_ifs with hij
    · exact weighted_integrable (pair_integrable i j hij (hψ.1 s)
        (hψ.2.1 s i) (hψ.2.2.1 s i)) hw hC
    · simp only [mul_zero]; exact integrable_zero _ _ _
  have hks := integrable_finsetSum Finset.univ (fun a _ => hk a)
  have hps := integrable_finsetSum Finset.univ (fun j _ => hp j)
  have he : (∫ x, w x * quantumEnergyDensity Z ψ s x) =
      ∫ x, w x * quantumCoreDensity Z ψ i s x +
        (1/2:ℝ) * (∑ a : Fin 3, w x * ‖ψ.gradient s i a x‖ ^ 2) -
        Z * (w x * (‖ψ.value s x‖ ^ 2 / ‖x i‖)) +
        (∑ j : Fin N, w x * (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [quantumEnergyDensity_delete Z ψ i s x]
      simp only [mul_add, mul_sub, mul_left_comm (w x) (1/2:ℝ),
        mul_left_comm (w x) Z, Finset.mul_sum]
  have ha := integral_add ((hc.add (hks.const_mul (1/2:ℝ))).sub (hn.const_mul Z)) hps
  have hb := integral_sub (hc.add (hks.const_mul (1/2:ℝ))) (hn.const_mul Z)
  have hd := integral_add hc (hks.const_mul (1/2:ℝ))
  simp only [Pi.sub_apply, Pi.add_apply] at ha hb hd
  rw [he, ha, hb, hd]
  simp only [integral_const_mul]
  rw [integral_finsetSum _ (fun a _ => hk a), integral_finsetSum _ (fun j _ => hp j)]

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply

lemma binding_total_kinetic_lower {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : fermionGraph N) :
    (∑ s : Spins N, ∑ i : Fin N, ((∑ j : Fin N, ∑ a : Fin 3, ∫ x, bindingWeight R ε (x i) *
        ‖graphComponent s (some (j,a)) F x‖ ^ 2) -
      (∑ a : Fin 3, ∫ x, bindingWeight R ε (x i) * ‖graphComponent s (some (i,a)) F x‖ ^ 2))) ≤
      ∑ s : Spins N, ∑ j : Fin N, ∑ a : Fin 3, (⟪graphComponent s (some (j,a)) ((bindingTotalMultiplier hR hε).apply F),
        graphComponent s (some (j,a)) F⟫_ℂ).re := by
  classical
  have h (s : Spins N) := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => bindingKinetic_lower hR hε (F.val s) i)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun s _ => h s)
  simp only [← graphComponent_apply] at hs
  apply le_trans hs
  apply le_of_eq
  apply Finset.sum_congr rfl; intro s _
  simp only [bindingTotalMultiplier_component, sum_inner, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]

end
section

attribute [local irreducible] graphNuclear graphPair graphComponent graphFormVector FermionMultiplier.apply coulombFormOperator fermionGraph weakGraph fermionGraphValue

lemma integral_weighted_quantumDensity_ordered {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (Z : ℝ) (s : Spins N)
    (w : Configuration N → ℝ) (hw : Continuous w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    (∫ x, w x * quantumEnergyDensity Z ψ s x) =
      (1/2:ℝ) * (∑ i : Fin N, ∑ a : Fin 3, ∫ x, w x * ‖ψ.gradient s i a x‖ ^ 2) -
      Z * (∑ i : Fin N, ∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x i‖)) +
      (∑ i : Fin N, ∑ j : Fin N, if i < j then (∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x i-x j‖)) else 0) := by
  classical
  have hp (i j : Fin N) : (∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x i-x j‖)) =
      ∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x j-x i‖) := by simp only [norm_sub_rev]
  have hi (i j : Fin N) :
      (∫ x, w x * (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) =
      if i ≠ j then (∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x i-x j‖)) else 0 := by
    split_ifs <;> simp
  rw [integral_weighted_quantumDensity hψ Z s w hw hC]
  simp only [hi]
  rw [← sum_pairs_half _ hp]

lemma FermionMultiplier.density_weighted_identity {N : ℕ} (Z : ℝ) (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) :
    (∫ x, p.value x * quantumEnergyDensity Z (graphFormVector F) s x) =
      (1/2:ℝ) * (∑ i : Fin N, ∑ a : Fin 3, ∫ x, p.value x * ‖graphComponent s (some (i,a)) F x‖ ^ 2) -
      Z * (∑ i : Fin N, ∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i‖)) +
      (∑ i : Fin N, ∑ j : Fin N, if i < j then
        (∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i-x j‖)) else 0) := by
  let C : ℝ := Classical.choose p.toSmoothMultiplier.bound
  have hC : ∀ x, |p.value x| ≤ C := Classical.choose_spec p.toSmoothMultiplier.bound
  have hCp (x : Configuration N) : ‖p.value x‖ ≤ C := by
    simpa only [Real.norm_eq_abs] using hC x
  simpa only [graphFormVector_value_eq, graphFormVector_gradient_eq] using
    integral_weighted_quantumDensity_ordered (graphFormVector_sobolev F) Z s p.value p.regular.continuous hCp

lemma FermionMultiplier.operator_weighted_pairing {N : ℕ} (Z : ℝ) (p : FermionMultiplier N)
    (F : fermionGraph N) :
    (⟪p.apply F, coulombFormOperator Z N F⟫_ℂ).re =
      (1/2:ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        (⟪graphComponent s (some (i,a)) (p.apply F), graphComponent s (some (i,a)) F⟫_ℂ).re) -
      Z * (∑ s : Spins N, ∑ i : Fin N, ∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i‖)) +
      (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N, if i < j then
        (∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i-x j‖)) else 0) := by
  have hh := coulombFormOperator_pairing Z N F (p.apply F)
  simpa only [p.nuclear_weighted_pairing, p.pair_weighted_pairing, dite_eq_ite] using hh

lemma weighted_form_algebra (Z K G V W D A : ℝ)
    (hd : D = (1/2:ℝ)*K-Z*V+W) (ha : A = (1/2:ℝ)*G-Z*V+W) :
    A = D+(1/2:ℝ)*(G-K) := by rw [hd, ha]; ring

lemma FermionMultiplier.density_weighted_sum {N : ℕ} (Z : ℝ) (p : FermionMultiplier N)
    (F : fermionGraph N) :
    (∑ s : Spins N, ∫ x, p.value x * quantumEnergyDensity Z (graphFormVector F) s x) =
      (1/2:ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        ∫ x, p.value x * ‖graphComponent s (some (i,a)) F x‖ ^ 2) -
      Z * (∑ s : Spins N, ∑ i : Fin N,
        ∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i‖)) +
      (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N, if i < j then
        (∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i-x j‖)) else 0) := by
  classical
  have he := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun s _ => p.density_weighted_identity Z F s)
  simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] using he

lemma FermionMultiplier.form_weighted_identity {N : ℕ} (Z : ℝ) (p : FermionMultiplier N)
    (F : fermionGraph N) :
    (⟪p.apply F, coulombFormOperator Z N F⟫_ℂ).re =
      (∑ s : Spins N, ∫ x, p.value x * quantumEnergyDensity Z (graphFormVector F) s x) +
      (1/2:ℝ) * ((∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        (⟪graphComponent s (some (i,a)) (p.apply F), graphComponent s (some (i,a)) F⟫_ℂ).re) -
        (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ∫ x, p.value x * ‖graphComponent s (some (i,a)) F x‖ ^ 2)) := by
  exact weighted_form_algebra Z _ _ _ _ _ _ (p.density_weighted_sum Z F) (p.operator_weighted_pairing Z F)

end

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_WeightedMass
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
open scoped Topology BigOperators ContDiff
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
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace CoulombAtom

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply coulombFormOperator fermionGraph weakGraph fermionGraphValue

lemma weightedFullDensity_delete {N : ℕ} (Z : ℝ) (F : fermionGraph N) (i : Fin N)
    (w : Configuration N → ℝ) (hw : Continuous w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    weightedFullDensity Z F w = weightedCoreDensity Z F i w +
      (1/2:ℝ) * weightedGradient F w i - Z * weightedNuclear F i w + weightedPairs F i w := by
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun s _ => integral_weighted_deletedDensity (graphFormVector_sobolev F) Z s i w hw hC)
  simpa only [weightedFullDensity, weightedCoreDensity, weightedGradient, weightedNuclear, weightedPairs,
    graphFormVector_value_eq, graphFormVector_gradient_eq,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] using h

attribute [local irreducible] bindingTotalMultiplier graphNuclear graphPair
  weightedMass weightedGradient weightedFullDensity weightedCoreDensity weightedNuclear weightedPairs

lemma sum_rotate_three {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A → B → C → ℝ) : (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

attribute [local irreducible] weightedKinetic graphKineticPair

lemma weightedKinetic_expand {N : ℕ} (F : fermionGraph N) (w : Configuration N → ℝ) :
    weightedKinetic F w =
      ∑ s, ∑ i, ∑ a, ∫ x, w x * ‖graphComponent s (some (i,a)) F x‖ ^ 2 := by
  unfold weightedKinetic weightedGradient
  exact Finset.sum_comm

lemma bindingTotal_full {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (Z : ℝ) (F : fermionGraph N) :
    weightedFullDensity Z F (bindingTotalMultiplier hR hε).value =
      ∑ i, weightedFullDensity Z F (fun x => bindingWeight R ε (x i)) := by
  unfold weightedFullDensity
  simp only [bindingTotal_integral hR hε ((graphFormVector_sobolev F).quantumEnergyDensity_integrable Z _)]
  exact Finset.sum_comm

lemma bindingTotal_kinetic {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : fermionGraph N) :
    weightedKinetic F (bindingTotalMultiplier hR hε).value =
      ∑ s, ∑ j, ∑ i, ∑ a, ∫ x, bindingWeight R ε (x j) *
        ‖graphComponent s (some (i,a)) F x‖ ^ 2 := by
  rw [weightedKinetic_expand]
  simp only [bindingTotal_integral hR hε (Lp.memLp _).norm.integrable_sq]
  apply Finset.sum_congr rfl; intro s _
  exact sum_rotate_three (fun i a j => ∫ x, bindingWeight R ε (x j) *
    ‖graphComponent s (some (i,a)) F x‖ ^ 2)

lemma sum_sub_le_transport {α β : Type*} [Fintype α] [Fintype β]
    (a b : α → β → ℝ) (G W K : ℝ)
    (ha : (∑ s, ∑ i, a s i) = W) (hb : (∑ s, ∑ i, b s i) = K)
    (hc : (∑ s, ∑ i, (a s i-b s i)) ≤ G) : W-K ≤ G := by
  rw [← ha, ← hb]
  simpa only [Finset.sum_sub_distrib] using hc

lemma bindingTotal_kinetic_diagonal {N : ℕ} (F : fermionGraph N) (R ε : ℝ) :
    (∑ s, ∑ i, ∑ a, ∫ x, bindingWeight R ε (x i) *
      ‖graphComponent s (some (i,a)) F x‖ ^ 2) =
      ∑ i, weightedGradient F (fun x => bindingWeight R ε (x i)) i := by
  unfold weightedGradient
  exact Finset.sum_comm

lemma bindingTotal_kinetic_lower_packed {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : fermionGraph N) :
    weightedKinetic F (bindingTotalMultiplier hR hε).value -
      (∑ i, weightedGradient F (fun x => bindingWeight R ε (x i)) i) ≤
      graphKineticPair ((bindingTotalMultiplier hR hε).apply F) F := by
  exact sum_sub_le_transport
    (fun s i => ∑ j, ∑ a, ∫ x, bindingWeight R ε (x i) *
      ‖graphComponent s (some (j,a)) F x‖ ^ 2)
    (fun s i => ∑ a, ∫ x, bindingWeight R ε (x i) *
      ‖graphComponent s (some (i,a)) F x‖ ^ 2)
    _ _ _ (bindingTotal_kinetic hR hε F).symm
    (bindingTotal_kinetic_diagonal F R ε) (by
      unfold graphKineticPair
      exact binding_total_kinetic_lower hR hε F)

lemma FermionMultiplier.form_weighted_packed {N : ℕ} (Z : ℝ) (p : FermionMultiplier N)
    (F : fermionGraph N) :
    (⟪p.apply F, coulombFormOperator Z N F⟫_ℂ).re =
      weightedFullDensity Z F p.value + (1/2:ℝ)*
        (graphKineticPair (p.apply F) F-weightedKinetic F p.value) := by
  simpa only [weightedKinetic_expand, weightedFullDensity, graphKineticPair] using
    p.form_weighted_identity Z F

lemma binding_form_sum_arithmetic {ι : Type*} [Fintype ι]
    (D C K V P : ι → ℝ) (Z W G A Dt : ℝ)
    (hD : ∀ i, D i = C i + (1/2:ℝ)*K i - Z*V i + P i)
    (hG : W-(∑ i, K i) ≤ G) (hDt : Dt = ∑ i, D i)
    (hA : A = Dt+(1/2:ℝ)*(G-W)) :
    (∑ i, (C i-Z*V i+P i)) ≤ A := by
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => hD i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs ⊢
  linarith

lemma binding_form_lower_oai {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (Z : ℝ) (F : fermionGraph N) :
    (∑ i : Fin N, (weightedCoreDensity Z F i (fun x => bindingWeight R ε (x i)) -
      Z * weightedNuclear F i (fun x => bindingWeight R ε (x i)) +
      weightedPairs F i (fun x => bindingWeight R ε (x i)))) ≤
      (⟪(bindingTotalMultiplier hR hε).apply F, coulombFormOperator Z N F⟫_ℂ).re := by
  let w : Fin N → Configuration N → ℝ := fun i x => bindingWeight R ε (x i)
  have hc (i : Fin N) : Continuous (w i) :=
    (bindingWeight_continuous hR hε).comp (continuous_apply i)
  have hb (i : Fin N) (x : Configuration N) : ‖w i x‖ ≤ R := by
    change ‖bindingWeight R ε (x i)‖ ≤ R
    rw [Real.norm_of_nonneg (bindingWeight_pos hR hε (x i)).le]
    exact bindingWeight_le hR hε (x i)
  exact binding_form_sum_arithmetic _ _ _ _ _ Z _ _ _ _
    (fun i => weightedFullDensity_delete Z F i (w i) (hc i) (hb i))
    (bindingTotal_kinetic_lower_packed hR hε F) (bindingTotal_full hR hε Z F)
    ((bindingTotalMultiplier hR hε).form_weighted_packed Z F)

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end

end OAI
end

theorem solution : type_of% @OAI.CoulombAtom.binding_form_lower_oai := @OAI.CoulombAtom.binding_form_lower_oai
