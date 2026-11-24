-- Prove2me | solution 1 for GlobalTheory.exists_isometric_intertwiner_of_matrixCoeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:08:43.618588+00:00
-- url     : https://prove2.me/submissions/73ba318d-297d-4fc6-ac6c-a508aaf98dc2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometricIntertwinerOfMatrixCoeffEq
import Theorems.Thm_GlobalTheory_inner_translate_translate_of_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (G : Type) [Group G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : G →* (H →L[ℂ] H)) (Hp : Type) [NormedAddCommGroup Hp]
      [InnerProductSpace ℂ Hp] [CompleteSpace Hp] (π : G →* (Hp →L[ℂ] Hp)),
      (∀ g x, ‖σ g x‖ = ‖x‖) → (∀ g x, ‖π g x‖ = ‖x‖) → ∀ (w : H) (v : Hp),
      (∀ y : H, (∀ g, ⟪y, σ g w⟫_ℂ = 0) → y = 0) → (∀ g, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ) →
      ∃ io : H →ₗᵢ[ℂ] Hp, io w = v ∧ ∀ (g : G) (u : H), io (σ g u) = π g (io u) := by
  intro G _ H _ _ _ σ Hp _ _ _ π hσ hπ w v hcyc hvw

  obtain ⟨A, hA⟩ : ∃ A : (G →₀ ℂ) →ₗ[ℂ] H, A = Finsupp.linearCombination ℂ (fun g => σ g w) :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : (G →₀ ℂ) →ₗ[ℂ] Hp, B = Finsupp.linearCombination ℂ (fun g => π g v) :=
    ⟨_, rfl⟩

  have hkey : ∀ g h : G, ⟪π g v, π h v⟫_ℂ = ⟪σ g w, σ h w⟫_ℂ := by
    intro g h
    rw [inner_translate_translate_of_norm π hπ, inner_translate_translate_of_norm σ hσ, hvw]
  have hinner : ∀ c d, ⟪B c, B d⟫_ℂ = ⟪A c, A d⟫_ℂ := by
    intro c d
    rw [hA, hB]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hkey]
  have hnorm : ∀ c, ‖B c‖ = ‖A c‖ := by
    intro c
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) (A c), hinner]
  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← norm_eq_zero, hnorm, hc, norm_zero]

  obtain ⟨F, hF⟩ : ∃ F : LinearMap.range A →ₗ[ℂ] Hp,
      ∀ c, F ⟨A c, LinearMap.mem_range_self A c⟩ = B c :=
    ⟨(LinearMap.ker A).liftQ B hker ∘ₗ A.quotKerEquivRange.symm.toLinearMap, fun c => by simp⟩
  have hFn : ∀ y, ‖F y‖ = ‖y‖ := by
    rintro ⟨_, c, rfl⟩
    rw [hF, hnorm]
    rfl
  let F' : LinearMap.range A →ₗᵢ[ℂ] Hp := { toLinearMap := F, norm_map' := hFn }

  have hclos : (LinearMap.range A).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro y hy
    refine hcyc y fun g => inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp hy _ ?_)
    exact ⟨Finsupp.single g 1, by simp [hA]⟩
  have hdense : DenseRange (LinearMap.range A).subtypeL :=
    denseRange_subtype_val.mpr (Submodule.dense_iff_topologicalClosure_eq_top.mpr hclos)
  have huni : IsUniformInducing (LinearMap.range A).subtypeL :=
    (LinearMap.range A).subtypeₗᵢ.isometry.isUniformInducing

  obtain ⟨X, hXdef⟩ : ∃ X : H →L[ℂ] Hp, X = F'.toContinuousLinearMap.extend (LinearMap.range A).subtypeL :=
    ⟨_, rfl⟩
  have hX : ∀ c, X (A c) = B c := fun c => by
    rw [hXdef]
    exact (ContinuousLinearMap.extend_eq F'.toContinuousLinearMap hdense huni
      ⟨A c, LinearMap.mem_range_self A c⟩).trans (hF c)
  have hXn : ∀ u, ‖X u‖ = ‖u‖ := by
    intro u
    refine hdense.induction_on (p := fun u => ‖X u‖ = ‖u‖) u
      (isClosed_eq (continuous_norm.comp X.continuous) continuous_norm) ?_
    rintro ⟨_, c, rfl⟩
    show ‖X (A c)‖ = ‖A c‖
    rw [hX, hnorm]

  have hshA : ∀ g c, σ g (A c) = A (Finsupp.mapDomain (g * ·) c) := by
    intro g c
    rw [hA, Finsupp.linearCombination_mapDomain]
    change (σ g : H →ₗ[ℂ] H) _ = _
    rw [Finsupp.apply_linearCombination]
    refine congrArg (fun f => Finsupp.linearCombination ℂ f c) ?_
    funext h
    simp [map_mul]
  have hshB : ∀ g c, π g (B c) = B (Finsupp.mapDomain (g * ·) c) := by
    intro g c
    rw [hB, Finsupp.linearCombination_mapDomain]
    change (π g : Hp →ₗ[ℂ] Hp) _ = _
    rw [Finsupp.apply_linearCombination]
    refine congrArg (fun f => Finsupp.linearCombination ℂ f c) ?_
    funext h
    simp [map_mul]
  have hXi : ∀ g u, X (σ g u) = π g (X u) := by
    intro g u
    refine hdense.induction_on (p := fun u => X (σ g u) = π g (X u)) u
      (isClosed_eq (X.continuous.comp (σ g).continuous) ((π g).continuous.comp X.continuous)) ?_
    rintro ⟨_, c, rfl⟩
    show X (σ g (A c)) = π g (X (A c))
    rw [hshA, hX, hX, hshB]
  have hw : A (Finsupp.single 1 1) = w := by simp [hA]
  have hv : B (Finsupp.single 1 1) = v := by simp [hB]
  refine ⟨{ toLinearMap := (X : H →ₗ[ℂ] Hp), norm_map' := hXn }, ?_, fun g u => hXi g u⟩
  show X w = v
  rw [← hw, hX, hv]
end GlobalTheory
