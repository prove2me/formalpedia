-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.compressed_norm_eq_on_minimal_family
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:02:29.067149+00:00
-- url     : https://prove2.me/submissions/e397eae6-e5ed-4f5d-a7a5-fb59875f6a3b

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

set_option Elab.async false
set_option linter.all false

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

namespace BoundedHochschild.KadisonRingrose

variable {M H K : Type*} [CStarAlgebra M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
lemma weakCompression_continuous (P : K →L[ℂ] K) (Q : H →L[ℂ] H) :
    Continuous (weakCompression P Q) :=
  (ContinuousLinearMapWOT.continuous_postcomp _).comp
    (ContinuousLinearMapWOT.continuous_precomp _)

omit [CompleteSpace H] [CompleteSpace K] in
lemma weakCompression_sublevel_convex (P : K →L[ℂ] K) (Q : H →L[ℂ] H) (c : ℝ) :
    Convex ℝ {W : H →WOT[ℂ] K | ‖(weakCompression P Q W).toCLM‖ ≤ c} := by
  let f : (H →WOT[ℂ] K) →ₗ[ℝ] (H →L[ℂ] K) :=
    { toFun := fun W => (weakCompression P Q W).toCLM
      map_add' := by intros; ext; simp [weakCompression]
      map_smul' := by intros; ext; simp [weakCompression] }
  have hs : f ⁻¹' Metric.closedBall 0 c =
      {W : H →WOT[ℂ] K | ‖(weakCompression P Q W).toCLM‖ ≤ c} := by
    ext W
    change dist ((weakCompression P Q W).toCLM) 0 ≤ c ↔ _
    rw [dist_zero_right]
    rfl
  rw [← hs]
  exact (convex_closedBall (0 : H →L[ℂ] K) c).linear_preimage f

lemma representedRightAverage_compress (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (P : K →L[ℂ] K) (Q : H →L[ℂ] H)
    (hP : ∀ a, P.comp (π a) = (π a).comp P)
    (hQ : ∀ a, Q.comp (σ a) = (σ a).comp Q)
    {I : Type*} [Fintype I] (m : I → M) (W : H →L[ℂ] K) :
    P.comp ((representedRightAverage π σ m W).comp Q) =
      representedRightAverage π σ m (P.comp (W.comp Q)) := by
  have hp (a : M) (ξ : K) : P (π a ξ) = π a (P ξ) :=
    congrArg (fun A : K →L[ℂ] K => A ξ) (hP a)
  have hq (a : M) (ξ : H) : (σ a).adjoint (Q ξ) = Q ((σ a).adjoint ξ) := by
    have hh := congrArg (fun A : H →L[ℂ] H => A ξ) (hQ (star a)).symm
    simpa only [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.comp_apply] using hh
  ext ξ
  simp only [ContinuousLinearMap.comp_apply, representedRightAverage,
    operatorRowAverage_apply, map_sum, hp, hq]

theorem compressed_norm_eq_on_minimal_family (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (F : Set (H →WOT[ℂ] K))
    (hclosed : IsClosed F) (hconv : Convex ℝ F)
    (hinv : RepresentedRightAverageInvariant π σ F)
    (hmin : ∀ G : Set (H →WOT[ℂ] K), G ⊆ F → G.Nonempty → IsClosed G →
      Convex ℝ G → RepresentedRightAverageInvariant π σ G → F ⊆ G)
    (P : K →L[ℂ] K) (Q : H →L[ℂ] H)
    (hP : ∀ a, P.comp (π a) = (π a).comp P)
    (hQ : ∀ a, Q.comp (σ a) = (σ a).comp Q)
    {U V : H →WOT[ℂ] K} (hU : U ∈ F) (hV : V ∈ F) :
    ‖(weakCompression P Q U).toCLM‖ = ‖(weakCompression P Q V).toCLM‖ := by
  have hle (A B : H →WOT[ℂ] K) (hA : A ∈ F) (hB : B ∈ F) :
      ‖(weakCompression P Q A).toCLM‖ ≤ ‖(weakCompression P Q B).toCLM‖ := by
    let c := ‖(weakCompression P Q B).toCLM‖
    let G := F ∩ (weakCompression P Q ⁻¹' rectangularWeakBall c)
    have hGc : IsClosed G := hclosed.inter
      ((rectangularWeakBall_isClosed c).preimage (weakCompression_continuous P Q))
    have hGv : Convex ℝ G := hconv.inter (weakCompression_sublevel_convex P Q c)
    have hGi : RepresentedRightAverageInvariant π σ G := by
      intro n m hm W hW
      refine ⟨hinv n m hm hW.1, ?_⟩
      change ‖P.comp ((representedRightAverage π σ m W.toCLM).comp Q)‖ ≤ c
      rw [representedRightAverage_compress π σ P Q hP hQ]
      exact (representedRightAverage_norm_le π σ m hm _).trans hW.2
    exact (hmin G (fun _ h => h.1) ⟨B, hB, show ‖(weakCompression P Q B).toCLM‖ ≤ c from le_rfl⟩ hGc hGv hGi hA).2
  exact le_antisymm (hle U V hU hV) (hle V U hV hU)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

theorem solution.{u_1,u_2,u_3} : type_of% @OAI.BoundedHochschild.KadisonRingrose.compressed_norm_eq_on_minimal_family.{u_1,u_2,u_3} := @OAI.BoundedHochschild.KadisonRingrose.compressed_norm_eq_on_minimal_family.{u_1,u_2,u_3}
