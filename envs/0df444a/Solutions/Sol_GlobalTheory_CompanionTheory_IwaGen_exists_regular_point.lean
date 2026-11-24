-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwaGen.exists_regular_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:39:22.852693+00:00
-- url     : https://prove2.me/submissions/4053608f-524f-43b2-8fc2-9b5a4a7cc66f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsRegularElementAbelian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwaGen
namespace GlobalTheory.CompanionTheory.IwaGen
theorem _root_.solution : ∀ {n : ℕ} (𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (U : Matrix (Fin n) (Fin n) ℂ), ∃ H ∈ 𝔞, ∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j →
      ∀ A ∈ 𝔞, (Uᴴ * A * U) i i = (Uᴴ * A * U) j j := by
  classical
  intro n 𝔞 U
  let L : Fin n × Fin n → (↥𝔞 →ₗ[ℝ] ℂ) := fun p =>
    { toFun := fun A => (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.1 p.1
        - (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.2 p.2
      map_add' := by
        intro A B
        simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
        ring
      map_smul' := by
        intro c A
        simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
          RingHom.id_apply, smul_sub] }
  have hL : ∀ (p : Fin n × Fin n) (A : ↥𝔞), L p A =
      (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.1 p.1
        - (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.2 p.2 := fun _ _ => rfl
  let s : Finset (Submodule ℝ ↥𝔞) :=
    (Finset.univ.image fun p => LinearMap.ker (L p)).erase ⊤
  have hs : (⊤ : Submodule ℝ ↥𝔞) ∉ s := Finset.notMem_erase _ _
  obtain ⟨H, hH⟩ := (Set.ne_univ_iff_exists_notMem _).1
    (Subspace.biUnion_ne_univ_of_top_notMem hs)
  refine ⟨H, H.2, fun i j hij A hA => ?_⟩
  have hker : H ∈ LinearMap.ker (L (i, j)) := by
    rw [LinearMap.mem_ker, hL]
    exact sub_eq_zero.2 hij
  have htop : LinearMap.ker (L (i, j)) = ⊤ := by
    by_contra hne
    apply hH
    refine Set.mem_biUnion (x := LinearMap.ker (L (i, j))) ?_ hker
    exact Finset.mem_coe.2 (Finset.mem_erase.2
      ⟨hne, Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩⟩)
  have hA' : (⟨A, hA⟩ : ↥𝔞) ∈ LinearMap.ker (L (i, j)) := by
    rw [htop]
    exact Submodule.mem_top
  rw [LinearMap.mem_ker, hL] at hA'
  exact sub_eq_zero.1 hA'
end GlobalTheory.CompanionTheory.IwaGen
