-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.exists_minimal_represented_averages
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:01:24.25949+00:00
-- url     : https://prove2.me/submissions/fafb844d-e902-4a45-874c-7947c5450c17

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma rightAverage_product_normalized (m : I → M) (n : J → M)
    (hm : ∑ i, m i * star (m i) = 1) (hn : ∑ j, n j * star (n j) = 1) :
    ∑ p : I × J, (m p.1 * n p.2) * star (m p.1 * n p.2) = 1 := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ i, m i * (∑ j, n j * star (n j)) * star (m i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.mul_sum, Finset.sum_mul, star_mul, mul_assoc]
    _ = 1 := by simp only [hn, mul_one, hm]

lemma rightAverage_real_smul_normalized (m : I → M) (r : ℝ)
    (hm : ∑ i, m i * star (m i) = 1) :
    ∑ i, (r • m i) * star (r • m i) = (r * r) • (1 : M) := by
  simp only [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
    smul_smul, ← Finset.smul_sum, hm]

lemma rightAverage_convex_normalized (m : I → M) (n : J → M)
    (hm : ∑ i, m i * star (m i) = 1) (hn : ∑ j, n j * star (n j) = 1)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s = 1) :
    ∑ p : I ⊕ J,
      (Sum.elim (fun i => Real.sqrt r • m i) (fun j => Real.sqrt s • n j) p) *
        star (Sum.elim (fun i => Real.sqrt r • m i) (fun j => Real.sqrt s • n j) p) = 1 := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [rightAverage_real_smul_normalized m _ hm, rightAverage_real_smul_normalized n _ hn,
    Real.mul_self_sqrt hr, Real.mul_self_sqrt hs, ← add_smul, hrs, one_smul]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace Generator

namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_weak_vector_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (v : ι → H) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C) :
    ∃ z : H, ‖z‖ ≤ C ∧ ∀ y : H,
      Tendsto (fun i => inner ℂ y (v i)) (ω : Filter ι) (𝓝 (inner ℂ y z)) := by
  let f : ι → WeakDual ℂ H := fun i =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H (v i))
  obtain ⟨d, hd, ht⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ H) C).ultrafilter_le_nhds
    (ω.map f) (by
      apply le_principal_iff.mpr
      change ∀ᶠ i in (ω : Filter ι), f i ∈ _
      exact Eventually.of_forall fun i => by
        simpa [f, Metric.mem_closedBall, dist_zero_right] using hv i)
  let z := (InnerProductSpace.toDual ℂ H).symm (WeakDual.toStrongDual d)
  refine ⟨z, ?_, ?_⟩
  · have hd' : ‖WeakDual.toStrongDual d‖ ≤ C := by
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hd
    simpa only [z, LinearIsometryEquiv.norm_map] using hd'
  · intro y
    have he : Tendsto (fun i => inner ℂ (v i) y) (ω : Filter ι)
        (𝓝 (inner ℂ z y)) := by
      have h := (WeakBilin.eval_continuous _ y).continuousAt.tendsto.comp ht
      change Tendsto (fun i => inner ℂ (v i) y) (ω : Filter ι) (𝓝 (d y)) at h
      rw [show inner ℂ z y = d y from InnerProductSpace.toDual_symm_apply]
      exact h
    have hs := he.star
    change Tendsto (fun i => (starRingEnd ℂ) (inner ℂ (v i) y)) (ω : Filter ι)
      (𝓝 ((starRingEnd ℂ) (inner ℂ z y))) at hs
    simpa only [inner_conj_symm] using hs
end Tracial
end Generator
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem exists_rectangular_weak_ultralimit {I : Type*} (ω : Ultrafilter I)
    (a : I → H →L[ℂ] K) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    ∃ T : H →L[ℂ] K, ‖T‖ ≤ C ∧ ∀ x y,
      Tendsto (fun i => inner ℂ y (a i x)) (ω : Filter I) (𝓝 (inner ℂ y (T x))) := by
  have h (x : H) := Generator.Tracial.exists_weak_vector_ultralimit ω
    (fun i => a i x) (C * ‖x‖) (fun i => (a i).le_of_opNorm_le (ha i) x)
  choose v hv ht using h
  have hadd (x z : H) : v (x + z) = v x + v z := by
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (x + z) y)
    simpa only [map_add, inner_add_right] using (ht x y).add (ht z y)
  have hsmul (c : ℂ) (x : H) : v (c • x) = c • v x := by
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (c • x) y)
    simpa only [map_smul, inner_smul_right] using (ht x y).const_mul c
  let T : H →L[ℂ] K := LinearMap.mkContinuous
    { toFun := v, map_add' := hadd, map_smul' := hsmul } C hv
  exact ⟨T, T.opNorm_le_bound hC hv, ht⟩

def rectangularWeakBall (C : ℝ) : Set (H →WOT[ℂ] K) := {T | ‖T.toCLM‖ ≤ C}

theorem rectangularWeakBall_isCompact (C : ℝ) :
    IsCompact (rectangularWeakBall (H := H) (K := K) C) := by
  classical
  by_cases hC : 0 ≤ C
  · apply isCompact_iff_ultrafilter_le_nhds'.mpr
    intro ω hω
    let a : (H →WOT[ℂ] K) → H →L[ℂ] K := fun T =>
      if T ∈ rectangularWeakBall C then T.toCLM else 0
    have ha (T : H →WOT[ℂ] K) : ‖a T‖ ≤ C := by
      dsimp [a]
      split_ifs with h
      · exact h
      · simpa only [norm_zero] using hC
    obtain ⟨T, hT, ht⟩ := exists_rectangular_weak_ultralimit ω a hC ha
    refine ⟨ContinuousLinearMapWOT.ofCLM T, hT, ?_⟩
    have hl : Tendsto (fun U => ContinuousLinearMapWOT.ofCLM (a U))
        (ω : Filter (H →WOT[ℂ] K)) (𝓝 (ContinuousLinearMapWOT.ofCLM T)) :=
      ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr ht
    have he : (fun U => ContinuousLinearMapWOT.ofCLM (a U)) =ᶠ[ω] id := by
      filter_upwards [show ∀ᶠ U in (ω : Filter (H →WOT[ℂ] K)),
        U ∈ rectangularWeakBall C from hω] with U hU
      simp only [a, ite_eq_left hU, ContinuousLinearMapWOT.ofCLM_toCLM, id_eq]
    exact hl.congr' he
  · have he : rectangularWeakBall (H := H) (K := K) C = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro T hT
      exact hC ((norm_nonneg _).trans hT)
    rw [he]
    exact isCompact_empty

theorem rectangularWeakBall_isClosed (C : ℝ) :
    IsClosed (rectangularWeakBall (H := H) (K := K) C) :=
  (rectangularWeakBall_isCompact C).isClosed
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {I H K : Type*} [Fintype I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma sum_norm_adjoint_sq (a : I → (H →L[ℂ] H))
    (ha : ∑ i, a i * star (a i) = 1) (ξ : H) :
    ∑ i, ‖(a i).adjoint ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
  have he : (∑ i, inner ℂ ((a i).adjoint ξ) ((a i).adjoint ξ)) = inner ℂ ξ ξ := by
    calc
      _ = ∑ i, inner ℂ ξ ((a i) ((a i).adjoint ξ)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (ContinuousLinearMap.adjoint_inner_left (a i) ((a i).adjoint ξ) ξ)
      _ = inner ℂ ξ ((∑ i, a i * star (a i)) ξ) := by
        simp only [sum_apply, inner_sum, ContinuousLinearMap.star_eq_adjoint]
        rfl
      _ = inner ℂ ξ ξ := by rw [ha]; rfl
  have hr := congrArg Complex.re he
  change Complex.re (∑ i, inner ℂ ((a i).adjoint ξ) ((a i).adjoint ξ)) =
    RCLike.re (inner ℂ ξ ξ) at hr
  simp only [Complex.re_sum] at hr
  change (∑ i, RCLike.re (inner ℂ ((a i).adjoint ξ) ((a i).adjoint ξ))) =
    RCLike.re (inner ℂ ξ ξ) at hr
  simpa only [inner_self_eq_norm_sq] using hr

omit [CompleteSpace K] in
lemma norm_sum_inner_sq_le (x y : I → K) :
    ‖∑ i, inner ℂ (x i) (y i)‖ ^ 2 ≤
      (∑ i, ‖x i‖ ^ 2) * ∑ i, ‖y i‖ ^ 2 := by
  have h : ‖∑ i, inner ℂ (x i) (y i)‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_inner_le_norm (x i) (y i))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

theorem operatorRowAverage_norm_le (a : I → (K →L[ℂ] K))
    (b : I → (H →L[ℂ] H)) (ha : ∑ i, a i * star (a i) = 1)
    (hb : ∑ i, b i * star (b i) = 1) (W : H →L[ℂ] K) :
    ‖operatorRowAverage a b W‖ ≤ ‖W‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg W)
  intro ξ
  let ζ := operatorRowAverage a b W ξ
  have he : inner ℂ ζ ζ = ∑ i, inner ℂ ((a i).adjoint ζ) (W ((b i).adjoint ξ)) := by
    conv_lhs => rhs; rw [show ζ = operatorRowAverage a b W ξ from rfl,
      operatorRowAverage_apply]
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (ContinuousLinearMap.adjoint_inner_left (a i) (W ((b i).adjoint ξ)) ζ).symm
  have hs : ∑ i, ‖W ((b i).adjoint ξ)‖ ^ 2 ≤ ‖W‖ ^ 2 * ‖ξ‖ ^ 2 := by
    calc
      _ ≤ ∑ i, (‖W‖ * ‖(b i).adjoint ξ‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (norm_nonneg _) (W.le_opNorm _) 2
      _ = ‖W‖ ^ 2 * ∑ i, ‖(b i).adjoint ξ‖ ^ 2 := by
        simp only [mul_pow, Finset.mul_sum]
      _ = _ := by rw [sum_norm_adjoint_sq b hb ξ]
  have hi := norm_sum_inner_sq_le (fun i => (a i).adjoint ζ)
    (fun i => W ((b i).adjoint ξ))
  rw [← he, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg ζ), sum_norm_adjoint_sq a ha ζ] at hi
  have hf : (‖ζ‖ ^ 2) ^ 2 ≤ ‖ζ‖ ^ 2 * (‖W‖ ^ 2 * ‖ξ‖ ^ 2) :=
    hi.trans (mul_le_mul_of_nonneg_left hs (sq_nonneg _))
  have hsq : ‖ζ‖ ^ 2 ≤ (‖W‖ * ‖ξ‖) ^ 2 := by nlinarith [sq_nonneg (‖ζ‖ ^ 2 - ‖W‖ ^ 2 * ‖ξ‖ ^ 2)]
  exact (sq_le_sq₀ (norm_nonneg ζ) (mul_nonneg (norm_nonneg W) (norm_nonneg ξ))).mp hsq
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable {I H K : Type*} [Fintype I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [PartialOrder M] [StarOrderedRing M] in
theorem representedRightAverage_norm_le (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M)
    (hm : ∑ i, m i * star (m i) = 1) (W : H →L[ℂ] K) :
    ‖representedRightAverage π σ m W‖ ≤ ‖W‖ := by
  apply operatorRowAverage_norm_le
  · simpa only [map_sum, map_mul, map_star, map_one] using congrArg π hm
  · simpa only [map_sum, map_mul, map_star, map_one] using congrArg σ hm
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology
open scoped InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M I H K : Type*} [CStarAlgebra M] [Fintype I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma weakRepresentedRightAverage_continuous (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M) :
    Continuous (weakRepresentedRightAverage π σ m) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro ξ η
  have he : (fun W : H →WOT[ℂ] K => inner ℂ η (weakRepresentedRightAverage π σ m W ξ)) =
      fun W => ∑ i, inner ℂ ((π (m i)).adjoint η) (W ((σ (m i)).adjoint ξ)) := by
    funext W
    change inner ℂ η (representedRightAverage π σ m W.toCLM ξ) = _
    simp only [representedRightAverage, operatorRowAverage_apply, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (ContinuousLinearMap.adjoint_inner_left (π (m i))
      (W ((σ (m i)).adjoint ξ)) η).symm
  rw [he]
  apply continuous_finsetSum
  intro i _
  exact ContinuousLinearMapWOT.continuous_inner_apply continuous_id _ _
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M I J H K : Type*} [CStarAlgebra M] [Fintype I] [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma representedRightAverage_reindex (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (e : I ≃ J) (m : J → M) (W : H →L[ℂ] K) :
    representedRightAverage π σ (m ∘ e) W = representedRightAverage π σ m W := by
  apply ContinuousLinearMap.ext
  intro ξ
  simpa only [representedRightAverage, operatorRowAverage_apply, Function.comp_apply] using
    e.sum_comp (fun j => π (m j) (W ((σ (m j)).adjoint ξ)))

lemma representedRightAverage_comp (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M) (n : J → M) (W : H →L[ℂ] K) :
    representedRightAverage π σ m (representedRightAverage π σ n W) =
      representedRightAverage π σ (fun p : I × J => m p.1 * n p.2) W := by
  classical
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [representedRightAverage, operatorRowAverage_apply, Fintype.sum_prod_type,
    map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change π (m i) (π (n j) (W ((σ (n j)).adjoint ((σ (m i)).adjoint ξ)))) =
    (π (m i) * π (n j)) (W ((σ (m i) * σ (n j)).adjoint ξ))
  rw [show σ (m i) * σ (n j) = (σ (m i)).comp (σ (n j)) from rfl,
    ContinuousLinearMap.adjoint_comp]
  rfl

lemma representedRightAverage_one (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (W : H →L[ℂ] K) :
    representedRightAverage π σ (fun _ : Fin 1 => (1 : M)) W = W := by
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [representedRightAverage, operatorRowAverage_apply, Fin.sum_univ_one,
    map_one, ContinuousLinearMap.adjoint_one, one_apply_eq_self]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M H K : Type*} [CStarAlgebra M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma weakRepresentedRightAverage_mem_orbit (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) {I : Type*} [Fintype I] (m : I → M)
    (hm : ∑ i, m i * star (m i) = 1) (W : H →WOT[ℂ] K) :
    weakRepresentedRightAverage π σ m W ∈ representedAveragingOrbit π σ W := by
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, m ∘ e.symm, ?_, ?_⟩
  · exact (e.symm.sum_comp (fun i => m i * star (m i))).trans hm
  · exact congrArg ContinuousLinearMapWOT.ofCLM
      (representedRightAverage_reindex π σ e.symm m W.toCLM).symm

lemma representedAveragingOrbit_self (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (W : H →WOT[ℂ] K) :
    W ∈ representedAveragingOrbit π σ W := by
  have h := weakRepresentedRightAverage_mem_orbit π σ
    (fun _ : Fin 1 => (1 : M)) (by simp) W
  change ContinuousLinearMapWOT.ofCLM
    (representedRightAverage π σ (fun _ : Fin 1 => (1 : M)) W.toCLM) ∈ _ at h
  simpa only [representedRightAverage_one, ContinuousLinearMapWOT.ofCLM_toCLM] using h

lemma representedAveragingOrbit_invariant (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) {I : Type*} [Fintype I] (m : I → M)
    (hm : ∑ i, m i * star (m i) = 1) (W : H →WOT[ℂ] K) :
    Set.MapsTo (weakRepresentedRightAverage π σ m)
      (representedAveragingOrbit π σ W) (representedAveragingOrbit π σ W) := by
  rintro V ⟨n, v, hv, rfl⟩
  have he := congrArg ContinuousLinearMapWOT.ofCLM
    (representedRightAverage_comp π σ m v W.toCLM)
  change weakRepresentedRightAverage π σ m (weakRepresentedRightAverage π σ v W) =
    weakRepresentedRightAverage π σ (fun p : I × Fin n => m p.1 * v p.2) W at he
  rw [he]
  exact weakRepresentedRightAverage_mem_orbit π σ _
    (rightAverage_product_normalized m v hm hv) W

theorem closedRepresentedAveragingOrbit_invariant (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) {I : Type*} [Fintype I] (m : I → M)
    (hm : ∑ i, m i * star (m i) = 1) (W : H →WOT[ℂ] K) :
    Set.MapsTo (weakRepresentedRightAverage π σ m)
      (closedRepresentedAveragingOrbit π σ W) (closedRepresentedAveragingOrbit π σ W) :=
  (representedAveragingOrbit_invariant π σ m hm W).closure
    (weakRepresentedRightAverage_continuous π σ m)

theorem closedRepresentedAveragingOrbit_isCompact (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (W : H →WOT[ℂ] K) :
    IsCompact (closedRepresentedAveragingOrbit π σ W) := by
  apply (rectangularWeakBall_isCompact ‖W.toCLM‖).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (rectangularWeakBall_isClosed ‖W.toCLM‖)
  rintro V ⟨n, m, hm, rfl⟩
  exact representedRightAverage_norm_le π σ m hm W.toCLM
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M I J H K : Type*} [CStarAlgebra M] [Fintype I] [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma representedRightAverage_real_smul (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M) (r : ℝ) (W : H →L[ℂ] K) :
    representedRightAverage π σ (fun i => r • m i) W =
      (r * r) • representedRightAverage π σ m W := by
  have hπ (a : M) : π (r • a) = r • π a :=
    (π.toLinearMap.restrictScalars ℝ).map_smul r a
  have hσ (a : M) : σ (r • a) = r • σ a :=
    (σ.toLinearMap.restrictScalars ℝ).map_smul r a
  have hW (x : H) : W (r • x) = r • W x := (W.restrictScalars ℝ).map_smul r x
  have hA (a : M) (x : K) : π a (r • x) = r • π a x :=
    ((π a).restrictScalars ℝ).map_smul r x
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [representedRightAverage, operatorRowAverage_apply, hπ, hσ,
    ← ContinuousLinearMap.star_eq_adjoint, star_smul, star_trivial,
    smul_apply, hW, hA, smul_smul, Finset.smul_sum]

lemma representedRightAverage_sum (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M) (n : J → M) (W : H →L[ℂ] K) :
    representedRightAverage π σ (Sum.elim m n) W =
      representedRightAverage π σ m W + representedRightAverage π σ n W := by
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [representedRightAverage, operatorRowAverage_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, add_apply]

lemma representedRightAverage_convex (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M) (n : J → M)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (W : H →L[ℂ] K) :
    representedRightAverage π σ
      (Sum.elim (fun i => Real.sqrt r • m i) (fun j => Real.sqrt s • n j)) W =
      r • representedRightAverage π σ m W + s • representedRightAverage π σ n W := by
  rw [representedRightAverage_sum, representedRightAverage_real_smul,
    representedRightAverage_real_smul, Real.mul_self_sqrt hr, Real.mul_self_sqrt hs]

theorem representedAveragingOrbit_convex (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (W : H →WOT[ℂ] K) :
    Convex ℝ (representedAveragingOrbit π σ W) := by
  rintro U ⟨n, m, hm, rfl⟩ V ⟨k, v, hv, rfl⟩ r s hr hs hrs
  have he := congrArg ContinuousLinearMapWOT.ofCLM
    (representedRightAverage_convex π σ m v hr hs W.toCLM)
  change weakRepresentedRightAverage π σ
    (Sum.elim (fun i => Real.sqrt r • m i) (fun j => Real.sqrt s • v j)) W =
    r • weakRepresentedRightAverage π σ m W + s • weakRepresentedRightAverage π σ v W at he
  rw [← he]
  exact weakRepresentedRightAverage_mem_orbit π σ _
    (rightAverage_convex_normalized m v hm hv hr hs hrs) W

theorem closedRepresentedAveragingOrbit_convex (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (W : H →WOT[ℂ] K) :
    Convex ℝ (closedRepresentedAveragingOrbit π σ W) :=
  (representedAveragingOrbit_convex π σ W).closure
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M H K : Type*} [CStarAlgebra M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem exists_minimal_represented_averages (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (W : H →WOT[ℂ] K) :
    ∃ F : Set (H →WOT[ℂ] K), F ⊆ closedRepresentedAveragingOrbit π σ W ∧
      F.Nonempty ∧ IsClosed F ∧ Convex ℝ F ∧ RepresentedRightAverageInvariant π σ F ∧
      ∀ G : Set (H →WOT[ℂ] K), G ⊆ F → G.Nonempty → IsClosed G →
        Convex ℝ G → RepresentedRightAverageInvariant π σ G → F ⊆ G := by
  classical
  let B := closedRepresentedAveragingOrbit π σ W
  have hBc : IsCompact B := closedRepresentedAveragingOrbit_isCompact π σ W
  let S : Set (Set (H →WOT[ℂ] K)) := {F | F ⊆ B ∧ F.Nonempty ∧ IsClosed F ∧
    Convex ℝ F ∧ RepresentedRightAverageInvariant π σ F}
  have hBS : B ∈ S := ⟨Set.Subset.rfl,
    ⟨W, subset_closure (representedAveragingOrbit_self π σ W)⟩,
    isClosed_closure, closedRepresentedAveragingOrbit_convex π σ W,
    fun _ m hm => closedRepresentedAveragingOrbit_invariant π σ m hm W⟩
  obtain ⟨F, hFB, hF⟩ := zorn_superset_nonempty S (fun c hc hchain hcne => by
    have : Nonempty c := hcne.to_subtype
    have hn : (⋂₀ c).Nonempty :=
      IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        (fun A hA B hB => by
          rcases hchain.total hA hB with h | h
          · exact ⟨A, hA, Set.Subset.rfl, h⟩
          · exact ⟨B, hB, h, Set.Subset.rfl⟩)
        (fun A hA => (hc hA).2.1)
        (fun A hA => hBc.of_isClosed_subset (hc hA).2.2.1 (hc hA).1)
        (fun A hA => (hc hA).2.2.1)
    refine ⟨⋂₀ c, ⟨?_, hn, ?_, ?_, ?_⟩, fun A hA => Set.sInter_subset_of_mem hA⟩
    · obtain ⟨A, hA⟩ := hcne
      exact (Set.sInter_subset_of_mem hA).trans (hc hA).1
    · exact isClosed_sInter (fun A hA => (hc hA).2.2.1)
    · intro x hx y hy r s hr hs hrs
      apply Set.mem_sInter.mpr
      intro A hA
      exact (hc hA).2.2.2.1 (Set.mem_sInter.mp hx A hA)
        (Set.mem_sInter.mp hy A hA) hr hs hrs
    · intro n m hm x hx
      apply Set.mem_sInter.mpr
      intro A hA
      exact (hc hA).2.2.2.2 n m hm (Set.mem_sInter.mp hx A hA)) B hBS
  exact ⟨F, hFB, hF.1.2.1, hF.1.2.2.1, hF.1.2.2.2.1, hF.1.2.2.2.2,
    fun G hGF hGn hGc hGv hGi => hF.2 ⟨hGF.trans hFB, hGn, hGc, hGv, hGi⟩ hGF⟩
end BoundedHochschild.KadisonRingrose
end
end OAI
end

theorem solution.{u_1,u_2,u_3} : type_of% @OAI.BoundedHochschild.KadisonRingrose.exists_minimal_represented_averages.{u_1,u_2,u_3} := @OAI.BoundedHochschild.KadisonRingrose.exists_minimal_represented_averages.{u_1,u_2,u_3}
