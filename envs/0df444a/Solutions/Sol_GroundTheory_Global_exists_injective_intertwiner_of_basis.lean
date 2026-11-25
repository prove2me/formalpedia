-- Prove2me | solution 1 for GroundTheory.Global.exists_injective_intertwiner_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:16:28.592262+00:00
-- url     : https://prove2.me/submissions/843bd836-1357-4d80-900f-9a33c94d76e1

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_RationalForm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_exists_rat_intertwiner
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
open scoped TensorProduct
variable {G M M' : Type*} [Group G] [AddCommGroup M] [AddCommGroup M']
namespace GroundTheory.Global
theorem _root_.solution {ι : Type*} [Fintype ι]
    (ρ : Representation ℤ G M) (ρ' : Representation ℤ G M') (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x))
    (b : Module.Basis ι ℤ M) (b' : Module.Basis ι ℤ M') :
    ∃ φ : M →ₗ[ℤ] M', Function.Injective φ ∧ (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ g x, φ (ρ g x) = ρ' g (φ x) := by
  classical

  let bR := Algebra.TensorProduct.basis ℝ b
  let bR' := Algebra.TensorProduct.basis ℝ b'
  let A : G → Matrix ι ι ℤ := fun g => LinearMap.toMatrix b b (ρ g)
  let A' : G → Matrix ι ι ℤ := fun g => LinearMap.toMatrix b' b' (ρ' g)
  let P : Matrix ι ι ℝ := LinearMap.toMatrix bR bR' e.toLinearMap
  have hP : P.det ≠ 0 := by
    have hid : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id :=
      LinearMap.ext fun x => by simp
    have h1 := congrArg (LinearMap.toMatrix bR bR) hid
    rw [LinearMap.toMatrix_comp bR bR' bR, LinearMap.toMatrix_id] at h1
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one] at h2
    exact right_ne_zero_of_mul_eq_one h2
  have hPA : ∀ g, P * (A g).map (Int.cast : ℤ → ℝ) = (A' g).map (Int.cast : ℤ → ℝ) * P := by
    intro g
    have hc : e.toLinearMap ∘ₗ (ρ g).baseChange ℝ = (ρ' g).baseChange ℝ ∘ₗ e.toLinearMap :=
      LinearMap.ext (he g)
    have h1 := congrArg (LinearMap.toMatrix bR bR') hc
    rw [LinearMap.toMatrix_comp bR bR bR', LinearMap.toMatrix_comp bR bR' bR',
      LinearMap.toMatrix_baseChange, LinearMap.toMatrix_baseChange, algebraMap_int_eq] at h1
    exact h1

  obtain ⟨Q, hQ, hQA⟩ := exists_rat_intertwiner (fun g => (A g).map (Int.cast : ℤ → ℚ))
    (fun g => (A' g).map (Int.cast : ℤ → ℚ)) P hP (fun g => by
      rw [Matrix.map_map, Matrix.map_map]
      convert hPA g using 3 <;> ext x <;> simp)

  obtain ⟨⟨d, hd⟩, hdQ⟩ := IsLocalization.exist_integer_multiples (R := ℤ)
    (M := nonZeroDivisors ℤ) (S := ℚ) Finset.univ (fun p : ι × ι => Q p.1 p.2)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  choose D hD using fun a b => RingHom.mem_rangeS.1 (hdQ (a, b) (Finset.mem_univ _))
  let Dm : Matrix ι ι ℤ := Matrix.of D
  have hDm : Dm.map (Int.cast : ℤ → ℚ) = (d : ℚ) • Q := by
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, Dm, Matrix.of_apply]
    rw [← eq_intCast (algebraMap ℤ ℚ), hD a b, zsmul_eq_mul, smul_eq_mul]
  have hdet : Dm.det ≠ 0 := by
    have h1 : (Dm.det : ℚ) = (d : ℚ) ^ Fintype.card ι * Q.det := by
      rw [Int.cast_det]
      change (Dm.map (Int.cast : ℤ → ℚ)).det = _
      rw [hDm, Matrix.det_smul]
    intro h0
    rw [h0, Int.cast_zero] at h1
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hd0)) hQ h1.symm
  have hmap : ∀ X Y : Matrix ι ι ℤ, (X * Y).map (Int.cast : ℤ → ℚ) =
      X.map (Int.cast : ℤ → ℚ) * Y.map (Int.cast : ℤ → ℚ) := fun X Y =>
    Matrix.map_mul (f := Int.castRingHom ℚ)
  have hDA : ∀ g, Dm * A g = A' g * Dm := by
    intro g
    apply Matrix.map_injective (f := (Int.cast : ℤ → ℚ)) Int.cast_injective
    show (Dm * A g).map (Int.cast : ℤ → ℚ) = (A' g * Dm).map (Int.cast : ℤ → ℚ)
    rw [hmap, hmap, hDm, Matrix.smul_mul, Matrix.mul_smul, hQA g]

  let φ : M →ₗ[ℤ] M' := Matrix.toLin b b' Dm
  refine ⟨φ, ?_, ⟨Dm.det, hdet, fun y => ?_⟩, fun g x => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := Matrix.repr_toLin (v₁ := b) (v₂ := b') Dm x
    rw [show Matrix.toLin b b' Dm x = 0 from hx, map_zero] at h1
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hdet h1.symm
    exact b.repr.map_eq_zero_iff.1 (Finsupp.ext fun i => congrFun h2 i)
  · refine ⟨Matrix.toLin b' b Dm.adjugate y, ?_⟩
    show (Matrix.toLin b b' Dm ∘ₗ Matrix.toLin b' b Dm.adjugate) y = _
    rw [← Matrix.toLin_mul, Matrix.mul_adjugate, map_smul, Matrix.toLin_one,
      LinearMap.smul_apply, LinearMap.id_apply]
  · have h1 : φ ∘ₗ ρ g = ρ' g ∘ₗ φ := by
      apply (LinearMap.toMatrix b b').injective
      rw [LinearMap.toMatrix_comp b b b', LinearMap.toMatrix_comp b b' b',
        LinearMap.toMatrix_toLin]
      exact hDA g
    exact LinearMap.congr_fun h1 x
end GroundTheory.Global
