-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.exists_univ_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:53:14.456407+00:00
-- url     : https://prove2.me/submissions/a9b79bb5-cde0-4e87-980a-942026542680

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_AgreementIffGuarded
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_GenericBlockMatrixIsBlockDiag
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_IsLowerUni_det_submatrix
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_IsLowerUni_eq_one
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_IsBlockDiag_exists_upper
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_generic_block_matrix_isBlockDiag
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_genLow_blockDiag
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_generic_block_matrix_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
variable {R : Type} [CommRing R] {N : ℕ} {Ψ : Type}
variable {j : ℕ} {S : Type} [CommRing S]
namespace GlobalTheory.CompanionTheory.Ar.PB
theorem _root_.solution (Ω : Type) [Field Ω] (Ψ : Type) (N j : ℕ) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra Ω T) (i : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] T)
      (ψ : T →ₐ[Ω] MvPolynomial (LowIdx Ψ N j) Ω) (B : Ψ → Matrix (Fin N) (Fin N) T), Function.Injective i ∧
      (∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (ev : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] Φ), Function.Injective ev →
        ∃ e : T →ₐ[Ω] Φ, Function.Injective e ∧ ∀ a, e (i a) = ev a) ∧
      ∀ τ, IsBlockDiag j (B τ) ∧ (B τ).BlockTriangular id ∧ IsLowerUni ((genericBlockMatrix Ω N j τ).map i.toRingHom * B τ) ∧
        ((genericBlockMatrix Ω N j τ).map i.toRingHom * B τ).map ψ.toRingHom = genLow Ω N j τ := by
  let A := MvPolynomial (inertBlockIndex Ψ N j) Ω
  let ψ₀ : A →ₐ[Ω] MvPolynomial (LowIdx Ψ N j) Ω := aeval fun q => genLow Ω N j q.1.1 q.1.2.1 q.1.2.2
  have h₀ : ∀ τ, (genericBlockMatrix Ω N j τ).map ψ₀.toRingHom = genLow Ω N j τ :=
    generic_block_matrix_map _ genLow_blockDiag fun q => aeval_X _ q
  let M : Submonoid A := (IsUnit.submonoid _).comap ψ₀
  have hM : ∀ m : M, (m : A) ≠ 0 := fun m e => by
    have : IsUnit (ψ₀ m) := m.2
    rw [e, map_zero] at this
    exact not_isUnit_zero this
  let T := Localization M
  let i : A →ₐ[Ω] T := IsScalarTower.toAlgHom Ω A T
  let ψ : T →ₐ[Ω] MvPolynomial (LowIdx Ψ N j) Ω := IsLocalization.liftAlgHom (M := M) (f := ψ₀) fun m => m.2
  have hψ : ∀ a, ψ (i a) = ψ₀ a := fun a => IsLocalization.lift_eq _ a
  have hi : Function.Injective i :=
    IsLocalization.injective T (M := M) fun m hm => mem_nonZeroDivisors_of_ne_zero (hM ⟨m, hm⟩)
  have hB : ∀ τ : Ψ, ∃ B, IsBlockDiag j B ∧ B.BlockTriangular id ∧
      IsLowerUni ((genericBlockMatrix Ω N j τ).map i.toRingHom * B) := fun τ => by
    refine ((generic_block_matrix_isBlockDiag τ).map _).exists_upper fun b => ?_
    rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    refine IsLocalization.map_units T (M := M) ⟨_, ?_⟩
    show IsUnit (ψ₀.toRingHom (Matrix.det _))
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, h₀, (genLow_lowerUni τ).det_submatrix]
    exact isUnit_one
  choose B hB using hB
  refine ⟨T, inferInstance, inferInstance, i, ψ, B, hi, fun Φ _ _ ev hev => ?_,
    fun τ => ⟨(hB τ).1, (hB τ).2.1, (hB τ).2.2, ?_⟩⟩
  · have hu : ∀ m : M, IsUnit (ev m) := fun m => ((map_ne_zero_iff ev hev).2 (hM m)).isUnit
    refine ⟨IsLocalization.liftAlgHom (M := M) (f := ev) hu, ?_, fun a => IsLocalization.lift_eq _ a⟩
    exact (IsLocalization.lift_injective_iff (g := ev.toRingHom) hu).2 fun x y =>
      ⟨fun h => congrArg ev (hi h), fun h => congrArg i (hev h)⟩
  · have e : ((genericBlockMatrix Ω N j τ).map i.toRingHom).map ψ.toRingHom = genLow Ω N j τ := by
      rw [← h₀]; ext1 a b; exact hψ _
    have h1 := (hB τ).2.2.map ψ.toRingHom
    rw [Matrix.map_mul, e] at h1 ⊢
    rw [(genLow_lowerUni τ).eq_one ((hB τ).2.1.map _) h1, mul_one]
end GlobalTheory.CompanionTheory.Ar.PB
