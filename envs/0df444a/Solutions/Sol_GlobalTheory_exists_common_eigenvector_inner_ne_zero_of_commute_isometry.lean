-- Prove2me | solution 1 for GlobalTheory.exists_common_eigenvector_inner_ne_zero_of_commute_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T06:22:01.05923+00:00
-- url     : https://prove2.me/submissions/3ee76856-9fb4-4d12-ac19-050cea794220

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CommutingIsometriesCommonEigenvector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory
open Module.End
namespace GlobalTheory
theorem _root_.solution
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (U : Submodule ℂ V)
    (hfin : FiniteDimensional ℂ U) {ι : Type} (A : ι → V →L[ℂ] V) (x₀ : V)
    (hx₀ : x₀ ∈ U) (hne : x₀ ≠ 0) (hU : ∀ i, ∀ x ∈ U, A i x ∈ U)
    (hiso : ∀ i x, ‖A i x‖ = ‖x‖) (hcomm : ∀ i l x, A i (A l x) = A l (A i x)) :
    ∃ v ∈ U, ⟪v, x₀⟫_ℂ ≠ 0 ∧ ∀ i, ∃ c : ℂ, A i v = c • v := by
  classical
  let B : ι → Module.End ℂ U := fun i => (A i).toLinearMap.restrict (hU i)
  have hBapp : ∀ i (x : U), ((B i x : U) : V) = A i x := fun i x => rfl
  have hinner : ∀ i (x y : U), ⟪B i x, B i y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro i x y
    let L : U →ₗᵢ[ℂ] U := { toLinearMap := B i, norm_map' := fun x => hiso i x }
    exact L.inner_map_map x y
  let D : ι → Module.End ℂ U := fun i => LinearMap.adjoint (B i)
  have hDB : ∀ i, D i * B i = 1 := by
    intro i
    apply LinearMap.ext; intro x
    apply ext_inner_left ℂ; intro y
    rw [Module.End.mul_apply, LinearMap.adjoint_inner_right, hinner]
    rfl
  have hBD : ∀ i, B i * D i = 1 := fun i => mul_eq_one_comm.mp (hDB i)
  let u : ι → (Module.End ℂ U)ˣ := fun i => ⟨B i, D i, hBD i, hDB i⟩
  have hBB : ∀ i l, Commute (B i) (B l) := by
    intro i l
    apply LinearMap.ext; intro x
    apply Subtype.ext
    exact hcomm i l x
  have hDBc : ∀ i l, Commute (D i) (B l) := fun i l =>
    Commute.units_inv_left (u := u i) (hBB i l)
  have hDD : ∀ i l, Commute (D i) (D l) := fun i l =>
    Commute.units_inv_left (u := u i) (hDBc l i).symm
  let T : ι ⊕ ι → Module.End ℂ U :=
    Sum.elim (fun i => B i + D i) (fun i => Complex.I • (B i - D i))
  have hTB : ∀ a k, Commute (T a) (B k) := by
    rintro (i|i) k
    · exact (hBB i k).add_left (hDBc i k)
    · exact ((hBB i k).sub_left (hDBc i k)).smul_left _
  have hTD : ∀ a k, Commute (T a) (D k) := by
    rintro (i|i) k
    · exact (hDBc k i).symm.add_left (hDD i k)
    · exact ((hDBc k i).symm.sub_left (hDD i k)).smul_left _
  have hTT : ∀ a b, Commute (T a) (T b) := by
    intro a b
    rcases b with i|i
    · exact (hTB a i).add_right (hTD a i)
    · exact ((hTB a i).sub_right (hTD a i)).smul_right _
  have hTsym : ∀ a, (T a).IsSymmetric := by
    rintro (i|i) x y
    · simp only [T, D, Sum.elim_inl, LinearMap.add_apply, inner_add_left, inner_add_right,
        LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
      ring
    · simp only [T, D, Sum.elim_inr, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left,
        inner_smul_right, inner_sub_left, inner_sub_right,
        LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right, Complex.conj_I]
      ring
  have hsup := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hTsym (fun a b _ => hTT a b)
  have key : ∃ χ : ι ⊕ ι → ℂ, ∃ w ∈ ⨅ a, eigenspace (T a) (χ a), ⟪(w : V), x₀⟫_ℂ ≠ 0 := by
    by_contra h
    push_neg at h
    let x : U := ⟨x₀, hx₀⟩
    have hle : (⨆ χ : ι ⊕ ι → ℂ, ⨅ a, eigenspace (T a) (χ a)) ≤ LinearMap.ker (innerₛₗ ℂ x) := by
      refine iSup_le fun χ w hw => ?_
      rw [LinearMap.mem_ker, innerₛₗ_apply_apply, Submodule.coe_inner, ← inner_conj_symm, h χ w hw]
      simp
    rw [hsup] at hle
    have hx : x ∈ LinearMap.ker (innerₛₗ ℂ x) := hle Submodule.mem_top
    rw [LinearMap.mem_ker, innerₛₗ_apply_apply, inner_self_eq_zero] at hx
    exact hne (congrArg Subtype.val hx)
  obtain ⟨χ, w, hw, hwx⟩ := key
  refine ⟨w, w.2, hwx, fun i => ⟨(χ (Sum.inl i) - Complex.I * χ (Sum.inr i)) / 2, ?_⟩⟩
  rw [Submodule.mem_iInf] at hw
  have h1 : B i w + D i w = χ (Sum.inl i) • w := by
    have := hw (Sum.inl i)
    rw [mem_eigenspace_iff] at this
    simpa [T] using this
  have h2 : Complex.I • (B i w - D i w) = χ (Sum.inr i) • w := by
    have := hw (Sum.inr i)
    rw [mem_eigenspace_iff] at this
    simpa [T] using this
  have h3 : B i w = ((χ (Sum.inl i) - Complex.I * χ (Sum.inr i)) / 2) • w := by
    have h2' : (B i w - D i w) = (-Complex.I * χ (Sum.inr i)) • w := by
      have := congrArg (fun z : U => (-Complex.I) • z) h2
      simp only [smul_smul] at this
      rw [show -Complex.I * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul] at this
      exact this
    linear_combination (norm := module) (1/2 : ℂ) • h1 + (1/2 : ℂ) • h2'
  have := congrArg Subtype.val h3
  exact this
end GlobalTheory
